-- Prove2me | solution 1 for syracuse_descends_range_1682041_1684041
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:22:37.483691+00:00
-- url     : https://prove2.me/submissions/4782c8a3-48f9-4173-9270-5d20a7a8b22b

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


theorem B1892353 : Blo 1682041 1892353 := bbase (se 2 (by rfl) ⟨709632, by rfl⟩ : syracuseStep 1892353 = 1419265) (by norm_num)
theorem B2523149 : Blo 1682041 2523149 := bbase (se 3 (by rfl) ⟨473090, by rfl⟩ : syracuseStep 2523149 = 946181) (by norm_num)
theorem B4259861 : Blo 1682041 4259861 := bbase (se 6 (by rfl) ⟨99840, by rfl⟩ : syracuseStep 4259861 = 199681) (by norm_num)
theorem B3596309 : Blo 1682041 3596309 := bbase (se 6 (by rfl) ⟨84288, by rfl⟩ : syracuseStep 3596309 = 168577) (by norm_num)
theorem B3784733 : Blo 1682041 3784733 := bbase (se 3 (by rfl) ⟨709637, by rfl⟩ : syracuseStep 3784733 = 1419275) (by norm_num)
theorem B2523173 : Blo 1682041 2523173 := bbase (se 4 (by rfl) ⟨236547, by rfl⟩ : syracuseStep 2523173 = 473095) (by norm_num)
theorem B1892389 : Blo 1682041 1892389 := bbase (se 4 (by rfl) ⟨177411, by rfl⟩ : syracuseStep 1892389 = 354823) (by norm_num)
theorem B4612133 : Blo 1682041 4612133 := bbase (se 4 (by rfl) ⟨432387, by rfl⟩ : syracuseStep 4612133 = 864775) (by norm_num)
theorem B2523197 : Blo 1682041 2523197 := bbase (se 3 (by rfl) ⟨473099, by rfl⟩ : syracuseStep 2523197 = 946199) (by norm_num)
theorem B1892425 : Blo 1682041 1892425 := bbase (se 2 (by rfl) ⟨709659, by rfl⟩ : syracuseStep 1892425 = 1419319) (by norm_num)
theorem B3194957 : Blo 1682041 3194957 := bbase (se 3 (by rfl) ⟨599054, by rfl⟩ : syracuseStep 3194957 = 1198109) (by norm_num)
theorem B2523221 : Blo 1682041 2523221 := bbase (se 8 (by rfl) ⟨14784, by rfl⟩ : syracuseStep 2523221 = 29569) (by norm_num)
theorem B3784805 : Blo 1682041 3784805 := bbase (se 4 (by rfl) ⟨354825, by rfl⟩ : syracuseStep 3784805 = 709651) (by norm_num)
theorem B2523245 : Blo 1682041 2523245 := bbase (se 3 (by rfl) ⟨473108, by rfl⟩ : syracuseStep 2523245 = 946217) (by norm_num)
theorem B1892461 : Blo 1682041 1892461 := bbase (se 3 (by rfl) ⟨354836, by rfl⟩ : syracuseStep 1892461 = 709673) (by norm_num)
theorem B3031157 : Blo 1682041 3031157 := bbase (se 5 (by rfl) ⟨142085, by rfl⟩ : syracuseStep 3031157 = 284171) (by norm_num)
theorem B9101429 : Blo 1682041 9101429 := bbase (se 5 (by rfl) ⟨426629, by rfl⟩ : syracuseStep 9101429 = 853259) (by norm_num)
theorem B2523269 : Blo 1682041 2523269 := bbase (se 4 (by rfl) ⟨236556, by rfl⟩ : syracuseStep 2523269 = 473113) (by norm_num)
theorem B1892497 : Blo 1682041 1892497 := bbase (se 2 (by rfl) ⟨709686, by rfl⟩ : syracuseStep 1892497 = 1419373) (by norm_num)
theorem B2523293 : Blo 1682041 2523293 := bbase (se 3 (by rfl) ⟨473117, by rfl⟩ : syracuseStep 2523293 = 946235) (by norm_num)
theorem B2130077 : Blo 1682041 2130077 := bbase (se 3 (by rfl) ⟨399389, by rfl⟩ : syracuseStep 2130077 = 798779) (by norm_num)
theorem B3784877 : Blo 1682041 3784877 := bbase (se 3 (by rfl) ⟨709664, by rfl⟩ : syracuseStep 3784877 = 1419329) (by norm_num)
theorem B2523317 : Blo 1682041 2523317 := bbase (se 5 (by rfl) ⟨118280, by rfl⟩ : syracuseStep 2523317 = 236561) (by norm_num)
theorem B1892533 : Blo 1682041 1892533 := bbase (se 5 (by rfl) ⟨88712, by rfl⟩ : syracuseStep 1892533 = 177425) (by norm_num)
theorem B2523341 : Blo 1682041 2523341 := bbase (se 3 (by rfl) ⟨473126, by rfl⟩ : syracuseStep 2523341 = 946253) (by norm_num)
theorem B4260053 : Blo 1682041 4260053 := bbase (se 7 (by rfl) ⟨49922, by rfl⟩ : syracuseStep 4260053 = 99845) (by norm_num)
theorem B2130133 : Blo 1682041 2130133 := bbase (se 7 (by rfl) ⟨24962, by rfl⟩ : syracuseStep 2130133 = 49925) (by norm_num)
theorem B1892569 : Blo 1682041 1892569 := bbase (se 2 (by rfl) ⟨709713, by rfl⟩ : syracuseStep 1892569 = 1419427) (by norm_num)
theorem B3195101 : Blo 1682041 3195101 := bbase (se 3 (by rfl) ⟨599081, by rfl⟩ : syracuseStep 3195101 = 1198163) (by norm_num)
theorem B2523365 : Blo 1682041 2523365 := bbase (se 4 (by rfl) ⟨236565, by rfl⟩ : syracuseStep 2523365 = 473131) (by norm_num)
theorem B3784949 : Blo 1682041 3784949 := bbase (se 5 (by rfl) ⟨177419, by rfl⟩ : syracuseStep 3784949 = 354839) (by norm_num)
theorem B2523389 : Blo 1682041 2523389 := bbase (se 3 (by rfl) ⟨473135, by rfl⟩ : syracuseStep 2523389 = 946271) (by norm_num)
theorem B1892605 : Blo 1682041 1892605 := bbase (se 3 (by rfl) ⟨354863, by rfl⟩ : syracuseStep 1892605 = 709727) (by norm_num)
theorem B6062357 : Blo 1682041 6062357 := bbase (se 6 (by rfl) ⟨142086, by rfl⟩ : syracuseStep 6062357 = 284173) (by norm_num)
theorem B2523413 : Blo 1682041 2523413 := bbase (se 6 (by rfl) ⟨59142, by rfl⟩ : syracuseStep 2523413 = 118285) (by norm_num)
theorem B1892641 : Blo 1682041 1892641 := bbase (se 2 (by rfl) ⟨709740, by rfl⟩ : syracuseStep 1892641 = 1419481) (by norm_num)
theorem B2523437 : Blo 1682041 2523437 := bbase (se 3 (by rfl) ⟨473144, by rfl⟩ : syracuseStep 2523437 = 946289) (by norm_num)
theorem B2130229 : Blo 1682041 2130229 := bbase (se 5 (by rfl) ⟨99854, by rfl⟩ : syracuseStep 2130229 = 199709) (by norm_num)
theorem B3785021 : Blo 1682041 3785021 := bbase (se 3 (by rfl) ⟨709691, by rfl⟩ : syracuseStep 3785021 = 1419383) (by norm_num)
theorem B3694909 : Blo 1682041 3694909 := bbase (se 3 (by rfl) ⟨692795, by rfl⟩ : syracuseStep 3694909 = 1385591) (by norm_num)
theorem B2523461 : Blo 1682041 2523461 := bbase (se 4 (by rfl) ⟨236574, by rfl⟩ : syracuseStep 2523461 = 473149) (by norm_num)
theorem B1892677 : Blo 1682041 1892677 := bbase (se 4 (by rfl) ⟨177438, by rfl⟩ : syracuseStep 1892677 = 354877) (by norm_num)
theorem B5677397 : Blo 1682041 5677397 := bbase (se 10 (by rfl) ⟨8316, by rfl⟩ : syracuseStep 5677397 = 16633) (by norm_num)
theorem B2523485 : Blo 1682041 2523485 := bbase (se 3 (by rfl) ⟨473153, by rfl⟩ : syracuseStep 2523485 = 946307) (by norm_num)
theorem B1892713 : Blo 1682041 1892713 := bbase (se 2 (by rfl) ⟨709767, by rfl⟩ : syracuseStep 1892713 = 1419535) (by norm_num)
theorem B2523509 : Blo 1682041 2523509 := bbase (se 5 (by rfl) ⟨118289, by rfl⟩ : syracuseStep 2523509 = 236579) (by norm_num)
theorem B3785093 : Blo 1682041 3785093 := bbase (se 4 (by rfl) ⟨354852, by rfl⟩ : syracuseStep 3785093 = 709705) (by norm_num)
theorem B4792709 : Blo 1682041 4792709 := bbase (se 4 (by rfl) ⟨449316, by rfl⟩ : syracuseStep 4792709 = 898633) (by norm_num)
theorem B2523533 : Blo 1682041 2523533 := bbase (se 3 (by rfl) ⟨473162, by rfl⟩ : syracuseStep 2523533 = 946325) (by norm_num)
theorem B1892749 : Blo 1682041 1892749 := bbase (se 3 (by rfl) ⟨354890, by rfl⟩ : syracuseStep 1892749 = 709781) (by norm_num)
theorem B12788117 : Blo 1682041 12788117 := bbase (se 6 (by rfl) ⟨299721, by rfl⟩ : syracuseStep 12788117 = 599443) (by norm_num)
theorem B6062501 : Blo 1682041 6062501 := bbase (se 4 (by rfl) ⟨568359, by rfl⟩ : syracuseStep 6062501 = 1136719) (by norm_num)
theorem B2523557 : Blo 1682041 2523557 := bbase (se 4 (by rfl) ⟨236583, by rfl⟩ : syracuseStep 2523557 = 473167) (by norm_num)
theorem B1892785 : Blo 1682041 1892785 := bbase (se 2 (by rfl) ⟨709794, by rfl⟩ : syracuseStep 1892785 = 1419589) (by norm_num)
theorem B2523581 : Blo 1682041 2523581 := bbase (se 3 (by rfl) ⟨473171, by rfl⟩ : syracuseStep 2523581 = 946343) (by norm_num)
theorem B3785165 : Blo 1682041 3785165 := bbase (se 3 (by rfl) ⟨709718, by rfl⟩ : syracuseStep 3785165 = 1419437) (by norm_num)
theorem B2523605 : Blo 1682041 2523605 := bbase (se 7 (by rfl) ⟨29573, by rfl⟩ : syracuseStep 2523605 = 59147) (by norm_num)
theorem B1892821 : Blo 1682041 1892821 := bbase (se 7 (by rfl) ⟨22181, by rfl⟩ : syracuseStep 1892821 = 44363) (by norm_num)
theorem B2130401 : Blo 1682041 2130401 := bbase (se 2 (by rfl) ⟨798900, by rfl⟩ : syracuseStep 2130401 = 1597801) (by norm_num)
theorem B2523629 : Blo 1682041 2523629 := bbase (se 3 (by rfl) ⟨473180, by rfl⟩ : syracuseStep 2523629 = 946361) (by norm_num)
theorem B5390837 : Blo 1682041 5390837 := bbase (se 5 (by rfl) ⟨252695, by rfl⟩ : syracuseStep 5390837 = 505391) (by norm_num)
theorem B1892857 : Blo 1682041 1892857 := bbase (se 2 (by rfl) ⟨709821, by rfl⟩ : syracuseStep 1892857 = 1419643) (by norm_num)
theorem B3195389 : Blo 1682041 3195389 := bbase (se 3 (by rfl) ⟨599135, by rfl⟩ : syracuseStep 3195389 = 1198271) (by norm_num)
theorem B2523653 : Blo 1682041 2523653 := bbase (se 4 (by rfl) ⟨236592, by rfl⟩ : syracuseStep 2523653 = 473185) (by norm_num)
theorem B3785237 : Blo 1682041 3785237 := bbase (se 6 (by rfl) ⟨88716, by rfl⟩ : syracuseStep 3785237 = 177433) (by norm_num)
theorem B2130457 : Blo 1682041 2130457 := bbase (se 2 (by rfl) ⟨798921, by rfl⟩ : syracuseStep 2130457 = 1597843) (by norm_num)
theorem B2523677 : Blo 1682041 2523677 := bbase (se 3 (by rfl) ⟨473189, by rfl⟩ : syracuseStep 2523677 = 946379) (by norm_num)
theorem B1892893 : Blo 1682041 1892893 := bbase (se 3 (by rfl) ⟨354917, by rfl⟩ : syracuseStep 1892893 = 709835) (by norm_num)
theorem B4260397 : Blo 1682041 4260397 := bbase (se 3 (by rfl) ⟨798824, by rfl⟩ : syracuseStep 4260397 = 1597649) (by norm_num)
theorem B2523701 : Blo 1682041 2523701 := bbase (se 5 (by rfl) ⟨118298, by rfl⟩ : syracuseStep 2523701 = 236597) (by norm_num)
theorem B1892929 : Blo 1682041 1892929 := bbase (se 2 (by rfl) ⟨709848, by rfl⟩ : syracuseStep 1892929 = 1419697) (by norm_num)
theorem B2523725 : Blo 1682041 2523725 := bbase (se 3 (by rfl) ⟨473198, by rfl⟩ : syracuseStep 2523725 = 946397) (by norm_num)
theorem B3785309 : Blo 1682041 3785309 := bbase (se 3 (by rfl) ⟨709745, by rfl⟩ : syracuseStep 3785309 = 1419491) (by norm_num)
theorem B2523749 : Blo 1682041 2523749 := bbase (se 4 (by rfl) ⟨236601, by rfl⟩ : syracuseStep 2523749 = 473203) (by norm_num)
theorem B1892965 : Blo 1682041 1892965 := bbase (se 4 (by rfl) ⟨177465, by rfl⟩ : syracuseStep 1892965 = 354931) (by norm_num)
theorem B2130553 : Blo 1682041 2130553 := bbase (se 2 (by rfl) ⟨798957, by rfl⟩ : syracuseStep 2130553 = 1597915) (by norm_num)
theorem B2523773 : Blo 1682041 2523773 := bbase (se 3 (by rfl) ⟨473207, by rfl⟩ : syracuseStep 2523773 = 946415) (by norm_num)
theorem B1893001 : Blo 1682041 1893001 := bbase (se 2 (by rfl) ⟨709875, by rfl⟩ : syracuseStep 1893001 = 1419751) (by norm_num)
theorem B2523797 : Blo 1682041 2523797 := bbase (se 6 (by rfl) ⟨59151, by rfl⟩ : syracuseStep 2523797 = 118303) (by norm_num)
theorem B3195541 : Blo 1682041 3195541 := bbase (se 6 (by rfl) ⟨74895, by rfl⟩ : syracuseStep 3195541 = 149791) (by norm_num)
theorem B4260509 : Blo 1682041 4260509 := bbase (se 3 (by rfl) ⟨798845, by rfl⟩ : syracuseStep 4260509 = 1597691) (by norm_num)
theorem B3785381 : Blo 1682041 3785381 := bbase (se 4 (by rfl) ⟨354879, by rfl⟩ : syracuseStep 3785381 = 709759) (by norm_num)
theorem B2523821 : Blo 1682041 2523821 := bbase (se 3 (by rfl) ⟨473216, by rfl⟩ : syracuseStep 2523821 = 946433) (by norm_num)
theorem B1893037 : Blo 1682041 1893037 := bbase (se 3 (by rfl) ⟨354944, by rfl⟩ : syracuseStep 1893037 = 709889) (by norm_num)
theorem B6062789 : Blo 1682041 6062789 := bbase (se 4 (by rfl) ⟨568386, by rfl⟩ : syracuseStep 6062789 = 1136773) (by norm_num)
theorem B2523845 : Blo 1682041 2523845 := bbase (se 4 (by rfl) ⟨236610, by rfl⟩ : syracuseStep 2523845 = 473221) (by norm_num)
theorem B8520389 : Blo 1682041 8520389 := bbase (se 4 (by rfl) ⟨798786, by rfl⟩ : syracuseStep 8520389 = 1597573) (by norm_num)
theorem B1893073 : Blo 1682041 1893073 := bbase (se 2 (by rfl) ⟨709902, by rfl⟩ : syracuseStep 1893073 = 1419805) (by norm_num)
theorem B2523869 : Blo 1682041 2523869 := bbase (se 3 (by rfl) ⟨473225, by rfl⟩ : syracuseStep 2523869 = 946451) (by norm_num)
theorem B3785453 : Blo 1682041 3785453 := bbase (se 3 (by rfl) ⟨709772, by rfl⟩ : syracuseStep 3785453 = 1419545) (by norm_num)
theorem B2523893 : Blo 1682041 2523893 := bbase (se 5 (by rfl) ⟨118307, by rfl⟩ : syracuseStep 2523893 = 236615) (by norm_num)
theorem B1893109 : Blo 1682041 1893109 := bbase (se 5 (by rfl) ⟨88739, by rfl⟩ : syracuseStep 1893109 = 177479) (by norm_num)
theorem B5677829 : Blo 1682041 5677829 := bbase (se 4 (by rfl) ⟨532296, by rfl⟩ : syracuseStep 5677829 = 1064593) (by norm_num)
theorem B2523917 : Blo 1682041 2523917 := bbase (se 3 (by rfl) ⟨473234, by rfl⟩ : syracuseStep 2523917 = 946469) (by norm_num)
theorem B1893145 : Blo 1682041 1893145 := bbase (se 2 (by rfl) ⟨709929, by rfl⟩ : syracuseStep 1893145 = 1419859) (by norm_num)
theorem B2523941 : Blo 1682041 2523941 := bbase (se 4 (by rfl) ⟨236619, by rfl⟩ : syracuseStep 2523941 = 473239) (by norm_num)
theorem B2130725 : Blo 1682041 2130725 := bbase (se 4 (by rfl) ⟨199755, by rfl⟩ : syracuseStep 2130725 = 399511) (by norm_num)
theorem B3785525 : Blo 1682041 3785525 := bbase (se 5 (by rfl) ⟨177446, by rfl⟩ : syracuseStep 3785525 = 354893) (by norm_num)
theorem B12780341 : Blo 1682041 12780341 := bbase (se 5 (by rfl) ⟨599078, by rfl⟩ : syracuseStep 12780341 = 1198157) (by norm_num)
theorem B2523965 : Blo 1682041 2523965 := bbase (se 3 (by rfl) ⟨473243, by rfl⟩ : syracuseStep 2523965 = 946487) (by norm_num)
theorem B1893181 : Blo 1682041 1893181 := bbase (se 3 (by rfl) ⟨354971, by rfl⟩ : syracuseStep 1893181 = 709943) (by norm_num)
theorem B6824773 : Blo 1682041 6824773 := bbase (se 4 (by rfl) ⟨639822, by rfl⟩ : syracuseStep 6824773 = 1279645) (by norm_num)
theorem B34530133 : Blo 1682041 34530133 := bbase (se 9 (by rfl) ⟨101162, by rfl⟩ : syracuseStep 34530133 = 202325) (by norm_num)
theorem B2523989 : Blo 1682041 2523989 := bbase (se 9 (by rfl) ⟨7394, by rfl⟩ : syracuseStep 2523989 = 14789) (by norm_num)
theorem B2696021 : Blo 1682041 2696021 := bbase (se 9 (by rfl) ⟨7898, by rfl⟩ : syracuseStep 2696021 = 15797) (by norm_num)
theorem B4260701 : Blo 1682041 4260701 := bbase (se 3 (by rfl) ⟨798881, by rfl⟩ : syracuseStep 4260701 = 1597763) (by norm_num)
theorem B2130781 : Blo 1682041 2130781 := bbase (se 3 (by rfl) ⟨399521, by rfl⟩ : syracuseStep 2130781 = 799043) (by norm_num)
theorem B1893217 : Blo 1682041 1893217 := bbase (se 2 (by rfl) ⟨709956, by rfl⟩ : syracuseStep 1893217 = 1419913) (by norm_num)
theorem B2524013 : Blo 1682041 2524013 := bbase (se 3 (by rfl) ⟨473252, by rfl⟩ : syracuseStep 2524013 = 946505) (by norm_num)
theorem B3785597 : Blo 1682041 3785597 := bbase (se 3 (by rfl) ⟨709799, by rfl⟩ : syracuseStep 3785597 = 1419599) (by norm_num)
theorem B4547461 : Blo 1682041 4547461 := bbase (se 4 (by rfl) ⟨426324, by rfl⟩ : syracuseStep 4547461 = 852649) (by norm_num)
theorem B2524037 : Blo 1682041 2524037 := bbase (se 4 (by rfl) ⟨236628, by rfl⟩ : syracuseStep 2524037 = 473257) (by norm_num)
theorem B1893253 : Blo 1682041 1893253 := bbase (se 4 (by rfl) ⟨177492, by rfl⟩ : syracuseStep 1893253 = 354985) (by norm_num)
theorem B2524061 : Blo 1682041 2524061 := bbase (se 3 (by rfl) ⟨473261, by rfl⟩ : syracuseStep 2524061 = 946523) (by norm_num)
theorem B1893289 : Blo 1682041 1893289 := bbase (se 2 (by rfl) ⟨709983, by rfl⟩ : syracuseStep 1893289 = 1419967) (by norm_num)
theorem B2524085 : Blo 1682041 2524085 := bbase (se 5 (by rfl) ⟨118316, by rfl⟩ : syracuseStep 2524085 = 236633) (by norm_num)
theorem B2130877 : Blo 1682041 2130877 := bbase (se 3 (by rfl) ⟨399539, by rfl⟩ : syracuseStep 2130877 = 799079) (by norm_num)
theorem B3785669 : Blo 1682041 3785669 := bbase (se 4 (by rfl) ⟨354906, by rfl⟩ : syracuseStep 3785669 = 709813) (by norm_num)
theorem B3195845 : Blo 1682041 3195845 := bbase (se 4 (by rfl) ⟨299610, by rfl⟩ : syracuseStep 3195845 = 599221) (by norm_num)
theorem B2524109 : Blo 1682041 2524109 := bbase (se 3 (by rfl) ⟨473270, by rfl⟩ : syracuseStep 2524109 = 946541) (by norm_num)
theorem B1893325 : Blo 1682041 1893325 := bbase (se 3 (by rfl) ⟨354998, by rfl⟩ : syracuseStep 1893325 = 709997) (by norm_num)
theorem B2524133 : Blo 1682041 2524133 := bbase (se 4 (by rfl) ⟨236637, by rfl⟩ : syracuseStep 2524133 = 473275) (by norm_num)
theorem B2769893 : Blo 1682041 2769893 := bbase (se 4 (by rfl) ⟨259677, by rfl⟩ : syracuseStep 2769893 = 519355) (by norm_num)
theorem B1893361 : Blo 1682041 1893361 := bbase (se 2 (by rfl) ⟨710010, by rfl⟩ : syracuseStep 1893361 = 1420021) (by norm_num)
theorem B12125173 : Blo 1682041 12125173 := bbase (se 5 (by rfl) ⟨568367, by rfl⟩ : syracuseStep 12125173 = 1136735) (by norm_num)
theorem B2524157 : Blo 1682041 2524157 := bbase (se 3 (by rfl) ⟨473279, by rfl⟩ : syracuseStep 2524157 = 946559) (by norm_num)
theorem B3785741 : Blo 1682041 3785741 := bbase (se 3 (by rfl) ⟨709826, by rfl⟩ : syracuseStep 3785741 = 1419653) (by norm_num)
theorem B2524181 : Blo 1682041 2524181 := bbase (se 6 (by rfl) ⟨59160, by rfl⟩ : syracuseStep 2524181 = 118321) (by norm_num)
theorem B1893397 : Blo 1682041 1893397 := bbase (se 6 (by rfl) ⟨44376, by rfl⟩ : syracuseStep 1893397 = 88753) (by norm_num)
theorem B2696213 : Blo 1682041 2696213 := bbase (se 6 (by rfl) ⟨63192, by rfl⟩ : syracuseStep 2696213 = 126385) (by norm_num)
theorem B1704997 : Blo 1682041 1704997 := bbase (se 4 (by rfl) ⟨159843, by rfl⟩ : syracuseStep 1704997 = 319687) (by norm_num)
theorem B3032101 : Blo 1682041 3032101 := bbase (se 4 (by rfl) ⟨284259, by rfl⟩ : syracuseStep 3032101 = 568519) (by norm_num)
theorem B4793381 : Blo 1682041 4793381 := bbase (se 4 (by rfl) ⟨449379, by rfl⟩ : syracuseStep 4793381 = 898759) (by norm_num)
theorem B2524205 : Blo 1682041 2524205 := bbase (se 3 (by rfl) ⟨473288, by rfl⟩ : syracuseStep 2524205 = 946577) (by norm_num)
theorem B1893433 : Blo 1682041 1893433 := bbase (se 2 (by rfl) ⟨710037, by rfl⟩ : syracuseStep 1893433 = 1420075) (by norm_num)
theorem B2524229 : Blo 1682041 2524229 := bbase (se 4 (by rfl) ⟨236646, by rfl⟩ : syracuseStep 2524229 = 473293) (by norm_num)
theorem B3785813 : Blo 1682041 3785813 := bbase (se 8 (by rfl) ⟨22182, by rfl⟩ : syracuseStep 3785813 = 44365) (by norm_num)
theorem B2524253 : Blo 1682041 2524253 := bbase (se 3 (by rfl) ⟨473297, by rfl⟩ : syracuseStep 2524253 = 946595) (by norm_num)
theorem B1893469 : Blo 1682041 1893469 := bbase (se 3 (by rfl) ⟨355025, by rfl⟩ : syracuseStep 1893469 = 710051) (by norm_num)
theorem B2049121 : Blo 1682041 2049121 := bbase (se 2 (by rfl) ⟨768420, by rfl⟩ : syracuseStep 2049121 = 1536841) (by norm_num)
theorem B2131049 : Blo 1682041 2131049 := bbase (se 2 (by rfl) ⟨799143, by rfl⟩ : syracuseStep 2131049 = 1598287) (by norm_num)
theorem B2524277 : Blo 1682041 2524277 := bbase (se 5 (by rfl) ⟨118325, by rfl⟩ : syracuseStep 2524277 = 236651) (by norm_num)
theorem B1893505 : Blo 1682041 1893505 := bbase (se 2 (by rfl) ⟨710064, by rfl⟩ : syracuseStep 1893505 = 1420129) (by norm_num)
theorem B2524301 : Blo 1682041 2524301 := bbase (se 3 (by rfl) ⟨473306, by rfl⟩ : syracuseStep 2524301 = 946613) (by norm_num)
theorem B2696341 : Blo 1682041 2696341 := bbase (se 6 (by rfl) ⟨63195, by rfl⟩ : syracuseStep 2696341 = 126391) (by norm_num)
theorem B3785885 : Blo 1682041 3785885 := bbase (se 3 (by rfl) ⟨709853, by rfl⟩ : syracuseStep 3785885 = 1419707) (by norm_num)
theorem B2131105 : Blo 1682041 2131105 := bbase (se 2 (by rfl) ⟨799164, by rfl⟩ : syracuseStep 2131105 = 1598329) (by norm_num)
theorem B2524325 : Blo 1682041 2524325 := bbase (se 4 (by rfl) ⟨236655, by rfl⟩ : syracuseStep 2524325 = 473311) (by norm_num)
theorem B1893541 : Blo 1682041 1893541 := bbase (se 4 (by rfl) ⟨177519, by rfl⟩ : syracuseStep 1893541 = 355039) (by norm_num)
theorem B13640885 : Blo 1682041 13640885 := bbase (se 5 (by rfl) ⟨639416, by rfl⟩ : syracuseStep 13640885 = 1278833) (by norm_num)
theorem B5678261 : Blo 1682041 5678261 := bbase (se 5 (by rfl) ⟨266168, by rfl⟩ : syracuseStep 5678261 = 532337) (by norm_num)
theorem B4261045 : Blo 1682041 4261045 := bbase (se 5 (by rfl) ⟨199736, by rfl⟩ : syracuseStep 4261045 = 399473) (by norm_num)
theorem B2524349 : Blo 1682041 2524349 := bbase (se 3 (by rfl) ⟨473315, by rfl⟩ : syracuseStep 2524349 = 946631) (by norm_num)
theorem B1893577 : Blo 1682041 1893577 := bbase (se 2 (by rfl) ⟨710091, by rfl⟩ : syracuseStep 1893577 = 1420183) (by norm_num)
theorem B2524373 : Blo 1682041 2524373 := bbase (se 7 (by rfl) ⟨29582, by rfl⟩ : syracuseStep 2524373 = 59165) (by norm_num)
theorem B3785957 : Blo 1682041 3785957 := bbase (se 4 (by rfl) ⟨354933, by rfl⟩ : syracuseStep 3785957 = 709867) (by norm_num)
theorem B2524397 : Blo 1682041 2524397 := bbase (se 3 (by rfl) ⟨473324, by rfl⟩ : syracuseStep 2524397 = 946649) (by norm_num)
theorem B1893613 : Blo 1682041 1893613 := bbase (se 3 (by rfl) ⟨355052, by rfl⟩ : syracuseStep 1893613 = 710105) (by norm_num)
theorem B5391605 : Blo 1682041 5391605 := bbase (se 5 (by rfl) ⟨252731, by rfl⟩ : syracuseStep 5391605 = 505463) (by norm_num)
theorem B2131201 : Blo 1682041 2131201 := bbase (se 2 (by rfl) ⟨799200, by rfl⟩ : syracuseStep 2131201 = 1598401) (by norm_num)
theorem B2524421 : Blo 1682041 2524421 := bbase (se 4 (by rfl) ⟨236664, by rfl⟩ : syracuseStep 2524421 = 473329) (by norm_num)
theorem B1893649 : Blo 1682041 1893649 := bbase (se 2 (by rfl) ⟨710118, by rfl⟩ : syracuseStep 1893649 = 1420237) (by norm_num)
theorem B2524445 : Blo 1682041 2524445 := bbase (se 3 (by rfl) ⟨473333, by rfl⟩ : syracuseStep 2524445 = 946667) (by norm_num)
theorem B4261157 : Blo 1682041 4261157 := bbase (se 4 (by rfl) ⟨399483, by rfl⟩ : syracuseStep 4261157 = 798967) (by norm_num)
theorem B3786029 : Blo 1682041 3786029 := bbase (se 3 (by rfl) ⟨709880, by rfl⟩ : syracuseStep 3786029 = 1419761) (by norm_num)
theorem B2524469 : Blo 1682041 2524469 := bbase (se 5 (by rfl) ⟨118334, by rfl⟩ : syracuseStep 2524469 = 236669) (by norm_num)
theorem B1893685 : Blo 1682041 1893685 := bbase (se 5 (by rfl) ⟨88766, by rfl⟩ : syracuseStep 1893685 = 177533) (by norm_num)
theorem B2524493 : Blo 1682041 2524493 := bbase (se 3 (by rfl) ⟨473342, by rfl⟩ : syracuseStep 2524493 = 946685) (by norm_num)
theorem B1893721 : Blo 1682041 1893721 := bbase (se 2 (by rfl) ⟨710145, by rfl⟩ : syracuseStep 1893721 = 1420291) (by norm_num)
theorem B2524517 : Blo 1682041 2524517 := bbase (se 4 (by rfl) ⟨236673, by rfl⟩ : syracuseStep 2524517 = 473347) (by norm_num)
theorem B3786101 : Blo 1682041 3786101 := bbase (se 5 (by rfl) ⟨177473, by rfl⟩ : syracuseStep 3786101 = 354947) (by norm_num)
theorem B2524541 : Blo 1682041 2524541 := bbase (se 3 (by rfl) ⟨473351, by rfl⟩ : syracuseStep 2524541 = 946703) (by norm_num)
theorem B1893757 : Blo 1682041 1893757 := bbase (se 3 (by rfl) ⟨355079, by rfl⟩ : syracuseStep 1893757 = 710159) (by norm_num)
theorem B2524565 : Blo 1682041 2524565 := bbase (se 6 (by rfl) ⟨59169, by rfl⟩ : syracuseStep 2524565 = 118339) (by norm_num)
theorem B1893793 : Blo 1682041 1893793 := bbase (se 2 (by rfl) ⟨710172, by rfl⟩ : syracuseStep 1893793 = 1420345) (by norm_num)
theorem B2524589 : Blo 1682041 2524589 := bbase (se 3 (by rfl) ⟨473360, by rfl⟩ : syracuseStep 2524589 = 946721) (by norm_num)
theorem B3786173 : Blo 1682041 3786173 := bbase (se 3 (by rfl) ⟨709907, by rfl⟩ : syracuseStep 3786173 = 1419815) (by norm_num)
theorem B2524613 : Blo 1682041 2524613 := bbase (se 4 (by rfl) ⟨236682, by rfl⟩ : syracuseStep 2524613 = 473365) (by norm_num)
theorem B1893829 : Blo 1682041 1893829 := bbase (se 4 (by rfl) ⟨177546, by rfl⟩ : syracuseStep 1893829 = 355093) (by norm_num)
theorem B4793813 : Blo 1682041 4793813 := bbase (se 7 (by rfl) ⟨56177, by rfl⟩ : syracuseStep 4793813 = 112355) (by norm_num)
theorem B2524637 : Blo 1682041 2524637 := bbase (se 3 (by rfl) ⟨473369, by rfl⟩ : syracuseStep 2524637 = 946739) (by norm_num)
theorem B4261349 : Blo 1682041 4261349 := bbase (se 4 (by rfl) ⟨399501, by rfl⟩ : syracuseStep 4261349 = 799003) (by norm_num)
theorem B1893865 : Blo 1682041 1893865 := bbase (se 2 (by rfl) ⟨710199, by rfl⟩ : syracuseStep 1893865 = 1420399) (by norm_num)
theorem B2524661 : Blo 1682041 2524661 := bbase (se 5 (by rfl) ⟨118343, by rfl⟩ : syracuseStep 2524661 = 236687) (by norm_num)
theorem B3786245 : Blo 1682041 3786245 := bbase (se 4 (by rfl) ⟨354960, by rfl⟩ : syracuseStep 3786245 = 709921) (by norm_num)
theorem B4097549 : Blo 1682041 4097549 := bbase (se 3 (by rfl) ⟨768290, by rfl⟩ : syracuseStep 4097549 = 1536581) (by norm_num)
theorem B2524685 : Blo 1682041 2524685 := bbase (se 3 (by rfl) ⟨473378, by rfl⟩ : syracuseStep 2524685 = 946757) (by norm_num)
theorem B1893901 : Blo 1682041 1893901 := bbase (se 3 (by rfl) ⟨355106, by rfl⟩ : syracuseStep 1893901 = 710213) (by norm_num)
theorem B2524709 : Blo 1682041 2524709 := bbase (se 4 (by rfl) ⟨236691, by rfl⟩ : syracuseStep 2524709 = 473383) (by norm_num)
theorem B1893937 : Blo 1682041 1893937 := bbase (se 2 (by rfl) ⟨710226, by rfl⟩ : syracuseStep 1893937 = 1420453) (by norm_num)
theorem B2524733 : Blo 1682041 2524733 := bbase (se 3 (by rfl) ⟨473387, by rfl⟩ : syracuseStep 2524733 = 946775) (by norm_num)
theorem B3786317 : Blo 1682041 3786317 := bbase (se 3 (by rfl) ⟨709934, by rfl⟩ : syracuseStep 3786317 = 1419869) (by norm_num)
theorem B2524757 : Blo 1682041 2524757 := bbase (se 8 (by rfl) ⟨14793, by rfl⟩ : syracuseStep 2524757 = 29587) (by norm_num)
theorem B1893973 : Blo 1682041 1893973 := bbase (se 8 (by rfl) ⟨11097, by rfl⟩ : syracuseStep 1893973 = 22195) (by norm_num)
theorem B5678693 : Blo 1682041 5678693 := bbase (se 4 (by rfl) ⟨532377, by rfl⟩ : syracuseStep 5678693 = 1064755) (by norm_num)
theorem B2524781 : Blo 1682041 2524781 := bbase (se 3 (by rfl) ⟨473396, by rfl⟩ : syracuseStep 2524781 = 946793) (by norm_num)
theorem B1894009 : Blo 1682041 1894009 := bbase (se 2 (by rfl) ⟨710253, by rfl⟩ : syracuseStep 1894009 = 1420507) (by norm_num)
theorem B2524805 : Blo 1682041 2524805 := bbase (se 4 (by rfl) ⟨236700, by rfl⟩ : syracuseStep 2524805 = 473401) (by norm_num)
theorem B3786389 : Blo 1682041 3786389 := bbase (se 6 (by rfl) ⟨88743, by rfl⟩ : syracuseStep 3786389 = 177487) (by norm_num)
theorem B2524829 : Blo 1682041 2524829 := bbase (se 3 (by rfl) ⟨473405, by rfl⟩ : syracuseStep 2524829 = 946811) (by norm_num)
theorem B1894045 : Blo 1682041 1894045 := bbase (se 3 (by rfl) ⟨355133, by rfl⟩ : syracuseStep 1894045 = 710267) (by norm_num)
theorem B10782389 : Blo 1682041 10782389 := bbase (se 5 (by rfl) ⟨505424, by rfl⟩ : syracuseStep 10782389 = 1010849) (by norm_num)
theorem B2524853 : Blo 1682041 2524853 := bbase (se 5 (by rfl) ⟨118352, by rfl⟩ : syracuseStep 2524853 = 236705) (by norm_num)
theorem B3196597 : Blo 1682041 3196597 := bbase (se 5 (by rfl) ⟨149840, by rfl⟩ : syracuseStep 3196597 = 299681) (by norm_num)
theorem B1894081 : Blo 1682041 1894081 := bbase (se 2 (by rfl) ⟨710280, by rfl⟩ : syracuseStep 1894081 = 1420561) (by norm_num)
theorem B6391493 : Blo 1682041 6391493 := bbase (se 4 (by rfl) ⟨599202, by rfl⟩ : syracuseStep 6391493 = 1198405) (by norm_num)
theorem B2524877 : Blo 1682041 2524877 := bbase (se 3 (by rfl) ⟨473414, by rfl⟩ : syracuseStep 2524877 = 946829) (by norm_num)
theorem B3786461 : Blo 1682041 3786461 := bbase (se 3 (by rfl) ⟨709961, by rfl⟩ : syracuseStep 3786461 = 1419923) (by norm_num)
theorem B4548325 : Blo 1682041 4548325 := bbase (se 4 (by rfl) ⟨426405, by rfl⟩ : syracuseStep 4548325 = 852811) (by norm_num)
theorem B2524901 : Blo 1682041 2524901 := bbase (se 4 (by rfl) ⟨236709, by rfl⟩ : syracuseStep 2524901 = 473419) (by norm_num)
theorem B1894117 : Blo 1682041 1894117 := bbase (se 4 (by rfl) ⟨177573, by rfl⟩ : syracuseStep 1894117 = 355147) (by norm_num)
theorem B5392117 : Blo 1682041 5392117 := bbase (se 5 (by rfl) ⟨252755, by rfl⟩ : syracuseStep 5392117 = 505511) (by norm_num)
theorem B2524925 : Blo 1682041 2524925 := bbase (se 3 (by rfl) ⟨473423, by rfl⟩ : syracuseStep 2524925 = 946847) (by norm_num)
theorem B1894153 : Blo 1682041 1894153 := bbase (se 2 (by rfl) ⟨710307, by rfl⟩ : syracuseStep 1894153 = 1420615) (by norm_num)
theorem B2524949 : Blo 1682041 2524949 := bbase (se 6 (by rfl) ⟨59178, by rfl⟩ : syracuseStep 2524949 = 118357) (by norm_num)
theorem B2696981 : Blo 1682041 2696981 := bbase (se 6 (by rfl) ⟨63210, by rfl⟩ : syracuseStep 2696981 = 126421) (by norm_num)
theorem B3786533 : Blo 1682041 3786533 := bbase (se 4 (by rfl) ⟨354987, by rfl⟩ : syracuseStep 3786533 = 709975) (by norm_num)
theorem B2524973 : Blo 1682041 2524973 := bbase (se 3 (by rfl) ⟨473432, by rfl⟩ : syracuseStep 2524973 = 946865) (by norm_num)
theorem B1894189 : Blo 1682041 1894189 := bbase (se 3 (by rfl) ⟨355160, by rfl⟩ : syracuseStep 1894189 = 710321) (by norm_num)
theorem B16181045 : Blo 1682041 16181045 := bbase (se 5 (by rfl) ⟨758486, by rfl⟩ : syracuseStep 16181045 = 1516973) (by norm_num)
theorem B4261693 : Blo 1682041 4261693 := bbase (se 3 (by rfl) ⟨799067, by rfl⟩ : syracuseStep 4261693 = 1598135) (by norm_num)
theorem B2524997 : Blo 1682041 2524997 := bbase (se 4 (by rfl) ⟨236718, by rfl⟩ : syracuseStep 2524997 = 473437) (by norm_num)
theorem B3196741 : Blo 1682041 3196741 := bbase (se 4 (by rfl) ⟨299694, by rfl⟩ : syracuseStep 3196741 = 599389) (by norm_num)
theorem B1894225 : Blo 1682041 1894225 := bbase (se 2 (by rfl) ⟨710334, by rfl⟩ : syracuseStep 1894225 = 1420669) (by norm_num)
theorem B2525021 : Blo 1682041 2525021 := bbase (se 3 (by rfl) ⟨473441, by rfl⟩ : syracuseStep 2525021 = 946883) (by norm_num)
theorem B3786605 : Blo 1682041 3786605 := bbase (se 3 (by rfl) ⟨709988, by rfl⟩ : syracuseStep 3786605 = 1419977) (by norm_num)
theorem B3237749 : Blo 1682041 3237749 := bbase (se 5 (by rfl) ⟨151769, by rfl⟩ : syracuseStep 3237749 = 303539) (by norm_num)
theorem B2525045 : Blo 1682041 2525045 := bbase (se 5 (by rfl) ⟨118361, by rfl⟩ : syracuseStep 2525045 = 236723) (by norm_num)
theorem B1894261 : Blo 1682041 1894261 := bbase (se 5 (by rfl) ⟨88793, by rfl⟩ : syracuseStep 1894261 = 177587) (by norm_num)
theorem B2525069 : Blo 1682041 2525069 := bbase (se 3 (by rfl) ⟨473450, by rfl⟩ : syracuseStep 2525069 = 946901) (by norm_num)
theorem B15345557 : Blo 1682041 15345557 := bbase (se 6 (by rfl) ⟨359661, by rfl⟩ : syracuseStep 15345557 = 719323) (by norm_num)
theorem B1894297 : Blo 1682041 1894297 := bbase (se 2 (by rfl) ⟨710361, by rfl⟩ : syracuseStep 1894297 = 1420723) (by norm_num)
theorem B2525093 : Blo 1682041 2525093 := bbase (se 4 (by rfl) ⟨236727, by rfl⟩ : syracuseStep 2525093 = 473455) (by norm_num)
theorem B4261805 : Blo 1682041 4261805 := bbase (se 3 (by rfl) ⟨799088, by rfl⟩ : syracuseStep 4261805 = 1598177) (by norm_num)
theorem B3786677 : Blo 1682041 3786677 := bbase (se 5 (by rfl) ⟨177500, by rfl⟩ : syracuseStep 3786677 = 355001) (by norm_num)
theorem B2557885 : Blo 1682041 2557885 := bbase (se 3 (by rfl) ⟨479603, by rfl⟩ : syracuseStep 2557885 = 959207) (by norm_num)
theorem B2525117 : Blo 1682041 2525117 := bbase (se 3 (by rfl) ⟨473459, by rfl⟩ : syracuseStep 2525117 = 946919) (by norm_num)
theorem B1894333 : Blo 1682041 1894333 := bbase (se 3 (by rfl) ⟨355187, by rfl⟩ : syracuseStep 1894333 = 710375) (by norm_num)
theorem B8521685 : Blo 1682041 8521685 := bbase (se 7 (by rfl) ⟨99863, by rfl⟩ : syracuseStep 8521685 = 199727) (by norm_num)
theorem B2525141 : Blo 1682041 2525141 := bbase (se 7 (by rfl) ⟨29591, by rfl⟩ : syracuseStep 2525141 = 59183) (by norm_num)
theorem B1894369 : Blo 1682041 1894369 := bbase (se 2 (by rfl) ⟨710388, by rfl⟩ : syracuseStep 1894369 = 1420777) (by norm_num)
theorem B6391781 : Blo 1682041 6391781 := bbase (se 4 (by rfl) ⟨599229, by rfl⟩ : syracuseStep 6391781 = 1198459) (by norm_num)
theorem B3196901 : Blo 1682041 3196901 := bbase (se 4 (by rfl) ⟨299709, by rfl⟩ : syracuseStep 3196901 = 599419) (by norm_num)
theorem B2525165 : Blo 1682041 2525165 := bbase (se 3 (by rfl) ⟨473468, by rfl⟩ : syracuseStep 2525165 = 946937) (by norm_num)
theorem B3786749 : Blo 1682041 3786749 := bbase (se 3 (by rfl) ⟨710015, by rfl⟩ : syracuseStep 3786749 = 1420031) (by norm_num)
theorem B2525189 : Blo 1682041 2525189 := bbase (se 4 (by rfl) ⟨236736, by rfl⟩ : syracuseStep 2525189 = 473473) (by norm_num)
theorem B1894405 : Blo 1682041 1894405 := bbase (se 4 (by rfl) ⟨177600, by rfl⟩ : syracuseStep 1894405 = 355201) (by norm_num)
theorem B5679125 : Blo 1682041 5679125 := bbase (se 6 (by rfl) ⟨133104, by rfl⟩ : syracuseStep 5679125 = 266209) (by norm_num)
theorem B2525213 : Blo 1682041 2525213 := bbase (se 3 (by rfl) ⟨473477, by rfl⟩ : syracuseStep 2525213 = 946955) (by norm_num)
theorem B1894441 : Blo 1682041 1894441 := bbase (se 2 (by rfl) ⟨710415, by rfl⟩ : syracuseStep 1894441 = 1420831) (by norm_num)
theorem B2525237 : Blo 1682041 2525237 := bbase (se 5 (by rfl) ⟨118370, by rfl⟩ : syracuseStep 2525237 = 236741) (by norm_num)
theorem B3786821 : Blo 1682041 3786821 := bbase (se 4 (by rfl) ⟨355014, by rfl⟩ : syracuseStep 3786821 = 710029) (by norm_num)
theorem B2525261 : Blo 1682041 2525261 := bbase (se 3 (by rfl) ⟨473486, by rfl⟩ : syracuseStep 2525261 = 946973) (by norm_num)
theorem B1894477 : Blo 1682041 1894477 := bbase (se 3 (by rfl) ⟨355214, by rfl⟩ : syracuseStep 1894477 = 710429) (by norm_num)
theorem B4098133 : Blo 1682041 4098133 := bbase (se 8 (by rfl) ⟨24012, by rfl⟩ : syracuseStep 4098133 = 48025) (by norm_num)
theorem B2525285 : Blo 1682041 2525285 := bbase (se 4 (by rfl) ⟨236745, by rfl⟩ : syracuseStep 2525285 = 473491) (by norm_num)
theorem B4261997 : Blo 1682041 4261997 := bbase (se 3 (by rfl) ⟨799124, by rfl⟩ : syracuseStep 4261997 = 1598249) (by norm_num)
theorem B1894513 : Blo 1682041 1894513 := bbase (se 2 (by rfl) ⟨710442, by rfl⟩ : syracuseStep 1894513 = 1420885) (by norm_num)
theorem B3197045 : Blo 1682041 3197045 := bbase (se 5 (by rfl) ⟨149861, by rfl⟩ : syracuseStep 3197045 = 299723) (by norm_num)
theorem B2525309 : Blo 1682041 2525309 := bbase (se 3 (by rfl) ⟨473495, by rfl⟩ : syracuseStep 2525309 = 946991) (by norm_num)
theorem B3786893 : Blo 1682041 3786893 := bbase (se 3 (by rfl) ⟨710042, by rfl⟩ : syracuseStep 3786893 = 1420085) (by norm_num)
theorem B2525333 : Blo 1682041 2525333 := bbase (se 6 (by rfl) ⟨59187, by rfl⟩ : syracuseStep 2525333 = 118375) (by norm_num)
theorem B1706141 : Blo 1682041 1706141 := bbase (se 3 (by rfl) ⟨319901, by rfl⟩ : syracuseStep 1706141 = 639803) (by norm_num)
theorem B2525357 : Blo 1682041 2525357 := bbase (se 3 (by rfl) ⟨473504, by rfl⟩ : syracuseStep 2525357 = 947009) (by norm_num)
theorem B2525381 : Blo 1682041 2525381 := bbase (se 4 (by rfl) ⟨236754, by rfl⟩ : syracuseStep 2525381 = 473509) (by norm_num)
theorem B4794565 : Blo 1682041 4794565 := bbase (se 4 (by rfl) ⟨449490, by rfl⟩ : syracuseStep 4794565 = 898981) (by norm_num)
theorem B3786965 : Blo 1682041 3786965 := bbase (se 7 (by rfl) ⟨44378, by rfl⟩ : syracuseStep 3786965 = 88757) (by norm_num)
theorem B7678165 : Blo 1682041 7678165 := bbase (se 7 (by rfl) ⟨89978, by rfl⟩ : syracuseStep 7678165 = 179957) (by norm_num)
theorem B2525405 : Blo 1682041 2525405 := bbase (se 3 (by rfl) ⟨473513, by rfl⟩ : syracuseStep 2525405 = 947027) (by norm_num)
theorem B2697437 : Blo 1682041 2697437 := bbase (se 3 (by rfl) ⟨505769, by rfl⟩ : syracuseStep 2697437 = 1011539) (by norm_num)
theorem B2525429 : Blo 1682041 2525429 := bbase (se 5 (by rfl) ⟨118379, by rfl⟩ : syracuseStep 2525429 = 236759) (by norm_num)
theorem B2525453 : Blo 1682041 2525453 := bbase (se 3 (by rfl) ⟨473522, by rfl⟩ : syracuseStep 2525453 = 947045) (by norm_num)
theorem B3787037 : Blo 1682041 3787037 := bbase (se 3 (by rfl) ⟨710069, by rfl⟩ : syracuseStep 3787037 = 1420139) (by norm_num)
theorem B2525477 : Blo 1682041 2525477 := bbase (se 4 (by rfl) ⟨236763, by rfl⟩ : syracuseStep 2525477 = 473527) (by norm_num)
theorem B2525501 : Blo 1682041 2525501 := bbase (se 3 (by rfl) ⟨473531, by rfl⟩ : syracuseStep 2525501 = 947063) (by norm_num)
theorem B4319573 : Blo 1682041 4319573 := bbase (se 10 (by rfl) ⟨6327, by rfl⟩ : syracuseStep 4319573 = 12655) (by norm_num)
theorem B2525525 : Blo 1682041 2525525 := bbase (se 10 (by rfl) ⟨3699, by rfl⟩ : syracuseStep 2525525 = 7399) (by norm_num)
theorem B3787109 : Blo 1682041 3787109 := bbase (se 4 (by rfl) ⟨355041, by rfl⟩ : syracuseStep 3787109 = 710083) (by norm_num)
theorem B2525549 : Blo 1682041 2525549 := bbase (se 3 (by rfl) ⟨473540, by rfl⟩ : syracuseStep 2525549 = 947081) (by norm_num)
theorem B6064517 : Blo 1682041 6064517 := bbase (se 4 (by rfl) ⟨568548, by rfl⟩ : syracuseStep 6064517 = 1137097) (by norm_num)
theorem B2525573 : Blo 1682041 2525573 := bbase (se 4 (by rfl) ⟨236772, by rfl⟩ : syracuseStep 2525573 = 473545) (by norm_num)
theorem B1919381 : Blo 1682041 1919381 := bbase (se 6 (by rfl) ⟨44985, by rfl⟩ : syracuseStep 1919381 = 89971) (by norm_num)
theorem B3836317 : Blo 1682041 3836317 := bbase (se 3 (by rfl) ⟨719309, by rfl⟩ : syracuseStep 3836317 = 1438619) (by norm_num)
theorem B2525597 : Blo 1682041 2525597 := bbase (se 3 (by rfl) ⟨473549, by rfl⟩ : syracuseStep 2525597 = 947099) (by norm_num)
theorem B3787181 : Blo 1682041 3787181 := bbase (se 3 (by rfl) ⟨710096, by rfl⟩ : syracuseStep 3787181 = 1420193) (by norm_num)
theorem B2525621 : Blo 1682041 2525621 := bbase (se 5 (by rfl) ⟨118388, by rfl⟩ : syracuseStep 2525621 = 236777) (by norm_num)
theorem B5679557 : Blo 1682041 5679557 := bbase (se 4 (by rfl) ⟨532458, by rfl⟩ : syracuseStep 5679557 = 1064917) (by norm_num)
theorem B8088005 : Blo 1682041 8088005 := bbase (se 4 (by rfl) ⟨758250, by rfl⟩ : syracuseStep 8088005 = 1516501) (by norm_num)
theorem B4262341 : Blo 1682041 4262341 := bbase (se 4 (by rfl) ⟨399594, by rfl⟩ : syracuseStep 4262341 = 799189) (by norm_num)
theorem B2525645 : Blo 1682041 2525645 := bbase (se 3 (by rfl) ⟨473558, by rfl⟩ : syracuseStep 2525645 = 947117) (by norm_num)
theorem B19179989 : Blo 1682041 19179989 := bbase (se 7 (by rfl) ⟨224765, by rfl⟩ : syracuseStep 19179989 = 449531) (by norm_num)
theorem B2525669 : Blo 1682041 2525669 := bbase (se 4 (by rfl) ⟨236781, by rfl⟩ : syracuseStep 2525669 = 473563) (by norm_num)
theorem B3787253 : Blo 1682041 3787253 := bbase (se 5 (by rfl) ⟨177527, by rfl⟩ : syracuseStep 3787253 = 355055) (by norm_num)
theorem B2525693 : Blo 1682041 2525693 := bbase (se 3 (by rfl) ⟨473567, by rfl⟩ : syracuseStep 2525693 = 947135) (by norm_num)
theorem B1796617 : Blo 1682041 1796617 := bbase (se 2 (by rfl) ⟨673731, by rfl⟩ : syracuseStep 1796617 = 1347463) (by norm_num)
theorem B2525717 : Blo 1682041 2525717 := bbase (se 6 (by rfl) ⟨59196, by rfl⟩ : syracuseStep 2525717 = 118393) (by norm_num)
theorem B2525741 : Blo 1682041 2525741 := bbase (se 3 (by rfl) ⟨473576, by rfl⟩ : syracuseStep 2525741 = 947153) (by norm_num)
theorem B4319797 : Blo 1682041 4319797 := bbase (se 5 (by rfl) ⟨202490, by rfl⟩ : syracuseStep 4319797 = 404981) (by norm_num)
theorem B4262453 : Blo 1682041 4262453 := bbase (se 5 (by rfl) ⟨199802, by rfl⟩ : syracuseStep 4262453 = 399605) (by norm_num)
theorem B3787325 : Blo 1682041 3787325 := bbase (se 3 (by rfl) ⟨710123, by rfl⟩ : syracuseStep 3787325 = 1420247) (by norm_num)
theorem B2525765 : Blo 1682041 2525765 := bbase (se 4 (by rfl) ⟨236790, by rfl⟩ : syracuseStep 2525765 = 473581) (by norm_num)
theorem B1796689 : Blo 1682041 1796689 := bbase (se 2 (by rfl) ⟨673758, by rfl⟩ : syracuseStep 1796689 = 1347517) (by norm_num)
theorem B2525789 : Blo 1682041 2525789 := bbase (se 3 (by rfl) ⟨473585, by rfl⟩ : syracuseStep 2525789 = 947171) (by norm_num)
theorem B3033701 : Blo 1682041 3033701 := bbase (se 4 (by rfl) ⟨284409, by rfl⟩ : syracuseStep 3033701 = 568819) (by norm_num)
theorem B2525813 : Blo 1682041 2525813 := bbase (se 5 (by rfl) ⟨118397, by rfl⟩ : syracuseStep 2525813 = 236795) (by norm_num)
theorem B3787397 : Blo 1682041 3787397 := bbase (se 4 (by rfl) ⟨355068, by rfl⟩ : syracuseStep 3787397 = 710137) (by norm_num)
theorem B2525837 : Blo 1682041 2525837 := bbase (se 3 (by rfl) ⟨473594, by rfl⟩ : syracuseStep 2525837 = 947189) (by norm_num)
theorem B2525861 : Blo 1682041 2525861 := bbase (se 4 (by rfl) ⟨236799, by rfl⟩ : syracuseStep 2525861 = 473599) (by norm_num)
theorem B2525885 : Blo 1682041 2525885 := bbase (se 3 (by rfl) ⟨473603, by rfl⟩ : syracuseStep 2525885 = 947207) (by norm_num)
theorem B3787469 : Blo 1682041 3787469 := bbase (se 3 (by rfl) ⟨710150, by rfl⟩ : syracuseStep 3787469 = 1420301) (by norm_num)
theorem B2525909 : Blo 1682041 2525909 := bbase (se 7 (by rfl) ⟨29600, by rfl⟩ : syracuseStep 2525909 = 59201) (by norm_num)
theorem B2525933 : Blo 1682041 2525933 := bbase (se 3 (by rfl) ⟨473612, by rfl⟩ : syracuseStep 2525933 = 947225) (by norm_num)
theorem B4262645 : Blo 1682041 4262645 := bbase (se 5 (by rfl) ⟨199811, by rfl⟩ : syracuseStep 4262645 = 399623) (by norm_num)
theorem B2525957 : Blo 1682041 2525957 := bbase (se 4 (by rfl) ⟨236808, by rfl⟩ : syracuseStep 2525957 = 473617) (by norm_num)
theorem B3787541 : Blo 1682041 3787541 := bbase (se 6 (by rfl) ⟨88770, by rfl⟩ : syracuseStep 3787541 = 177541) (by norm_num)
theorem B2525981 : Blo 1682041 2525981 := bbase (se 3 (by rfl) ⟨473621, by rfl⟩ : syracuseStep 2525981 = 947243) (by norm_num)
theorem B3410741 : Blo 1682041 3410741 := bbase (se 5 (by rfl) ⟨159878, by rfl⟩ : syracuseStep 3410741 = 319757) (by norm_num)
theorem B2526005 : Blo 1682041 2526005 := bbase (se 5 (by rfl) ⟨118406, by rfl⟩ : syracuseStep 2526005 = 236813) (by norm_num)
theorem B2526029 : Blo 1682041 2526029 := bbase (se 3 (by rfl) ⟨473630, by rfl⟩ : syracuseStep 2526029 = 947261) (by norm_num)
theorem B3787613 : Blo 1682041 3787613 := bbase (se 3 (by rfl) ⟨710177, by rfl⟩ : syracuseStep 3787613 = 1420355) (by norm_num)
theorem B3074917 : Blo 1682041 3074917 := bbase (se 4 (by rfl) ⟨288273, by rfl⟩ : syracuseStep 3074917 = 576547) (by norm_num)
theorem B2526053 : Blo 1682041 2526053 := bbase (se 4 (by rfl) ⟨236817, by rfl⟩ : syracuseStep 2526053 = 473635) (by norm_num)
theorem B5679989 : Blo 1682041 5679989 := bbase (se 5 (by rfl) ⟨266249, by rfl⟩ : syracuseStep 5679989 = 532499) (by norm_num)
theorem B3787685 : Blo 1682041 3787685 := bbase (se 4 (by rfl) ⟨355095, by rfl⟩ : syracuseStep 3787685 = 710191) (by norm_num)
theorem B1797061 : Blo 1682041 1797061 := bbase (se 4 (by rfl) ⟨168474, by rfl⟩ : syracuseStep 1797061 = 336949) (by norm_num)
theorem B3787757 : Blo 1682041 3787757 := bbase (se 3 (by rfl) ⟨710204, by rfl⟩ : syracuseStep 3787757 = 1420409) (by norm_num)
theorem B4041781 : Blo 1682041 4041781 := bbase (se 5 (by rfl) ⟨189458, by rfl⟩ : syracuseStep 4041781 = 378917) (by norm_num)
theorem B3787829 : Blo 1682041 3787829 := bbase (se 5 (by rfl) ⟨177554, by rfl⟩ : syracuseStep 3787829 = 355109) (by norm_num)
theorem B2395261 : Blo 1682041 2395261 := bbase (se 3 (by rfl) ⟨449111, by rfl⟩ : syracuseStep 2395261 = 898223) (by norm_num)
theorem B3787901 : Blo 1682041 3787901 := bbase (se 3 (by rfl) ⟨710231, by rfl⟩ : syracuseStep 3787901 = 1420463) (by norm_num)
theorem B6392965 : Blo 1682041 6392965 := bbase (se 4 (by rfl) ⟨599340, by rfl⟩ : syracuseStep 6392965 = 1198681) (by norm_num)
theorem B3787973 : Blo 1682041 3787973 := bbase (se 4 (by rfl) ⟨355122, by rfl⟩ : syracuseStep 3787973 = 710245) (by norm_num)
theorem B8522981 : Blo 1682041 8522981 := bbase (se 4 (by rfl) ⟨799029, by rfl⟩ : syracuseStep 8522981 = 1598059) (by norm_num)
theorem B3788045 : Blo 1682041 3788045 := bbase (se 3 (by rfl) ⟨710258, by rfl⟩ : syracuseStep 3788045 = 1420517) (by norm_num)
theorem B5680421 : Blo 1682041 5680421 := bbase (se 4 (by rfl) ⟨532539, by rfl⟩ : syracuseStep 5680421 = 1065079) (by norm_num)
theorem B1797437 : Blo 1682041 1797437 := bbase (se 3 (by rfl) ⟨337019, by rfl⟩ : syracuseStep 1797437 = 674039) (by norm_num)
theorem B3788117 : Blo 1682041 3788117 := bbase (se 11 (by rfl) ⟨2774, by rfl⟩ : syracuseStep 3788117 = 5549) (by norm_num)
theorem B1797509 : Blo 1682041 1797509 := bbase (se 4 (by rfl) ⟨168516, by rfl⟩ : syracuseStep 1797509 = 337033) (by norm_num)
theorem B4320661 : Blo 1682041 4320661 := bbase (se 6 (by rfl) ⟨101265, by rfl⟩ : syracuseStep 4320661 = 202531) (by norm_num)
theorem B3788189 : Blo 1682041 3788189 := bbase (se 3 (by rfl) ⟨710285, by rfl⟩ : syracuseStep 3788189 = 1420571) (by norm_num)
theorem B6393269 : Blo 1682041 6393269 := bbase (se 5 (by rfl) ⟨299684, by rfl⟩ : syracuseStep 6393269 = 599369) (by norm_num)
theorem B5393861 : Blo 1682041 5393861 := bbase (se 4 (by rfl) ⟨505674, by rfl⟩ : syracuseStep 5393861 = 1011349) (by norm_num)
theorem B3034565 : Blo 1682041 3034565 := bbase (se 4 (by rfl) ⟨284490, by rfl⟩ : syracuseStep 3034565 = 568981) (by norm_num)
theorem B2395597 : Blo 1682041 2395597 := bbase (se 3 (by rfl) ⟨449174, by rfl⟩ : syracuseStep 2395597 = 898349) (by norm_num)
theorem B3788261 : Blo 1682041 3788261 := bbase (se 4 (by rfl) ⟨355149, by rfl⟩ : syracuseStep 3788261 = 710299) (by norm_num)
theorem B1822241 : Blo 1682041 1822241 := bbase (se 2 (by rfl) ⟨683340, by rfl⟩ : syracuseStep 1822241 = 1366681) (by norm_num)
theorem B3788333 : Blo 1682041 3788333 := bbase (se 3 (by rfl) ⟨710312, by rfl⟩ : syracuseStep 3788333 = 1420625) (by norm_num)
theorem B1797697 : Blo 1682041 1797697 := bbase (se 2 (by rfl) ⟨674136, by rfl⟩ : syracuseStep 1797697 = 1348273) (by norm_num)
theorem B3788405 : Blo 1682041 3788405 := bbase (se 5 (by rfl) ⟨177581, by rfl⟩ : syracuseStep 3788405 = 355163) (by norm_num)
theorem B5394053 : Blo 1682041 5394053 := bbase (se 4 (by rfl) ⟨505692, by rfl⟩ : syracuseStep 5394053 = 1011385) (by norm_num)
theorem B2395813 : Blo 1682041 2395813 := bbase (se 4 (by rfl) ⟨224607, by rfl⟩ : syracuseStep 2395813 = 449215) (by norm_num)
theorem B8089253 : Blo 1682041 8089253 := bbase (se 4 (by rfl) ⟨758367, by rfl⟩ : syracuseStep 8089253 = 1516735) (by norm_num)
theorem B3788477 : Blo 1682041 3788477 := bbase (se 3 (by rfl) ⟨710339, by rfl⟩ : syracuseStep 3788477 = 1420679) (by norm_num)
theorem B10235605 : Blo 1682041 10235605 := bbase (se 7 (by rfl) ⟨119948, by rfl⟩ : syracuseStep 10235605 = 239897) (by norm_num)
theorem B5680853 : Blo 1682041 5680853 := bbase (se 7 (by rfl) ⟨66572, by rfl⟩ : syracuseStep 5680853 = 133145) (by norm_num)
theorem B1847009 : Blo 1682041 1847009 := bbase (se 2 (by rfl) ⟨692628, by rfl⟩ : syracuseStep 1847009 = 1385257) (by norm_num)
theorem B1797881 : Blo 1682041 1797881 := bbase (se 2 (by rfl) ⟨674205, by rfl⟩ : syracuseStep 1797881 = 1348411) (by norm_num)
theorem B3788549 : Blo 1682041 3788549 := bbase (se 4 (by rfl) ⟨355176, by rfl⟩ : syracuseStep 3788549 = 710353) (by norm_num)
theorem B3788621 : Blo 1682041 3788621 := bbase (se 3 (by rfl) ⟨710366, by rfl⟩ : syracuseStep 3788621 = 1420733) (by norm_num)
theorem B2158417 : Blo 1682041 2158417 := bbase (se 2 (by rfl) ⟨809406, by rfl⟩ : syracuseStep 2158417 = 1618813) (by norm_num)
theorem B2158421 : Blo 1682041 2158421 := bbase (se 9 (by rfl) ⟨6323, by rfl⟩ : syracuseStep 2158421 = 12647) (by norm_num)
theorem B3788693 : Blo 1682041 3788693 := bbase (se 6 (by rfl) ⟨88797, by rfl⟩ : syracuseStep 3788693 = 177595) (by norm_num)
theorem B1945513 : Blo 1682041 1945513 := bbase (se 2 (by rfl) ⟨729567, by rfl⟩ : syracuseStep 1945513 = 1459135) (by norm_num)
theorem B2158513 : Blo 1682041 2158513 := bbase (se 2 (by rfl) ⟨809442, by rfl⟩ : syracuseStep 2158513 = 1618885) (by norm_num)
theorem B2838469 : Blo 1682041 2838469 := bbase (se 4 (by rfl) ⟨266106, by rfl⟩ : syracuseStep 2838469 = 532213) (by norm_num)
theorem B3788765 : Blo 1682041 3788765 := bbase (se 3 (by rfl) ⟨710393, by rfl⟩ : syracuseStep 3788765 = 1420787) (by norm_num)
theorem B7680005 : Blo 1682041 7680005 := bbase (se 4 (by rfl) ⟨720000, by rfl⟩ : syracuseStep 7680005 = 1440001) (by norm_num)
theorem B5754901 : Blo 1682041 5754901 := bbase (se 6 (by rfl) ⟨134880, by rfl⟩ : syracuseStep 5754901 = 269761) (by norm_num)
theorem B2838557 : Blo 1682041 2838557 := bbase (se 3 (by rfl) ⟨532229, by rfl⟩ : syracuseStep 2838557 = 1064459) (by norm_num)
theorem B2396189 : Blo 1682041 2396189 := bbase (se 3 (by rfl) ⟨449285, by rfl⟩ : syracuseStep 2396189 = 898571) (by norm_num)
theorem B3788837 : Blo 1682041 3788837 := bbase (se 4 (by rfl) ⟨355203, by rfl⟩ : syracuseStep 3788837 = 710407) (by norm_num)
theorem B7188533 : Blo 1682041 7188533 := bbase (se 5 (by rfl) ⟨336962, by rfl⟩ : syracuseStep 7188533 = 673925) (by norm_num)
theorem B3788909 : Blo 1682041 3788909 := bbase (se 3 (by rfl) ⟨710420, by rfl⟩ : syracuseStep 3788909 = 1420841) (by norm_num)
theorem B5681285 : Blo 1682041 5681285 := bbase (se 4 (by rfl) ⟨532620, by rfl⟩ : syracuseStep 5681285 = 1065241) (by norm_num)
theorem B2838685 : Blo 1682041 2838685 := bbase (se 3 (by rfl) ⟨532253, by rfl⟩ : syracuseStep 2838685 = 1064507) (by norm_num)
theorem B3788981 : Blo 1682041 3788981 := bbase (se 5 (by rfl) ⟨177608, by rfl⟩ : syracuseStep 3788981 = 355217) (by norm_num)
theorem B3838141 : Blo 1682041 3838141 := bbase (se 3 (by rfl) ⟨719651, by rfl⟩ : syracuseStep 3838141 = 1439303) (by norm_num)
theorem B2838773 : Blo 1682041 2838773 := bbase (se 5 (by rfl) ⟨133067, by rfl⟩ : syracuseStep 2838773 = 266135) (by norm_num)
theorem B2732285 : Blo 1682041 2732285 := bbase (se 3 (by rfl) ⟨512303, by rfl⟩ : syracuseStep 2732285 = 1024607) (by norm_num)
theorem B3789053 : Blo 1682041 3789053 := bbase (se 3 (by rfl) ⟨710447, by rfl⟩ : syracuseStep 3789053 = 1420895) (by norm_num)
theorem B2838901 : Blo 1682041 2838901 := bbase (se 5 (by rfl) ⟨133073, by rfl⟩ : syracuseStep 2838901 = 266147) (by norm_num)
theorem B4551029 : Blo 1682041 4551029 := bbase (se 5 (by rfl) ⟨213329, by rfl⟩ : syracuseStep 4551029 = 426659) (by norm_num)
theorem B2838989 : Blo 1682041 2838989 := bbase (se 3 (by rfl) ⟨532310, by rfl⟩ : syracuseStep 2838989 = 1064621) (by norm_num)
theorem B8524277 : Blo 1682041 8524277 := bbase (se 5 (by rfl) ⟨399575, by rfl⟩ : syracuseStep 8524277 = 799151) (by norm_num)
theorem B5681717 : Blo 1682041 5681717 := bbase (se 5 (by rfl) ⟨266330, by rfl⟩ : syracuseStep 5681717 = 532661) (by norm_num)
theorem B2839117 : Blo 1682041 2839117 := bbase (se 3 (by rfl) ⟨532334, by rfl⟩ : syracuseStep 2839117 = 1064669) (by norm_num)
theorem B2839205 : Blo 1682041 2839205 := bbase (se 4 (by rfl) ⟨266175, by rfl⟩ : syracuseStep 2839205 = 532351) (by norm_num)
theorem B5116645 : Blo 1682041 5116645 := bbase (se 4 (by rfl) ⟨479685, by rfl⟩ : syracuseStep 5116645 = 959371) (by norm_num)
theorem B2159345 : Blo 1682041 2159345 := bbase (se 2 (by rfl) ⟨809754, by rfl⟩ : syracuseStep 2159345 = 1619509) (by norm_num)
theorem B2159365 : Blo 1682041 2159365 := bbase (se 4 (by rfl) ⟨202440, by rfl⟩ : syracuseStep 2159365 = 404881) (by norm_num)
theorem B2839333 : Blo 1682041 2839333 := bbase (se 4 (by rfl) ⟨266187, by rfl⟩ : syracuseStep 2839333 = 532375) (by norm_num)
theorem B9581429 : Blo 1682041 9581429 := bbase (se 5 (by rfl) ⟨449129, by rfl⟩ : syracuseStep 9581429 = 898259) (by norm_num)
theorem B2839421 : Blo 1682041 2839421 := bbase (se 3 (by rfl) ⟨532391, by rfl⟩ : syracuseStep 2839421 = 1064783) (by norm_num)
theorem B8516501 : Blo 1682041 8516501 := bbase (se 6 (by rfl) ⟨199605, by rfl⟩ : syracuseStep 8516501 = 399211) (by norm_num)
theorem B4551589 : Blo 1682041 4551589 := bbase (se 4 (by rfl) ⟨426711, by rfl⟩ : syracuseStep 4551589 = 853423) (by norm_num)
theorem B3593173 : Blo 1682041 3593173 := bbase (se 7 (by rfl) ⟨42107, by rfl⟩ : syracuseStep 3593173 = 84215) (by norm_num)
theorem B5682149 : Blo 1682041 5682149 := bbase (se 4 (by rfl) ⟨532701, by rfl⟩ : syracuseStep 5682149 = 1065403) (by norm_num)
theorem B2839549 : Blo 1682041 2839549 := bbase (se 3 (by rfl) ⟨532415, by rfl⟩ : syracuseStep 2839549 = 1064831) (by norm_num)
theorem B2839637 : Blo 1682041 2839637 := bbase (se 8 (by rfl) ⟨16638, by rfl⟩ : syracuseStep 2839637 = 33277) (by norm_num)
theorem B2839765 : Blo 1682041 2839765 := bbase (se 7 (by rfl) ⟨33278, by rfl⟩ : syracuseStep 2839765 = 66557) (by norm_num)
theorem B3642605 : Blo 1682041 3642605 := bbase (se 3 (by rfl) ⟨682988, by rfl⟩ : syracuseStep 3642605 = 1365977) (by norm_num)
theorem B2839853 : Blo 1682041 2839853 := bbase (se 3 (by rfl) ⟨532472, by rfl⟩ : syracuseStep 2839853 = 1064945) (by norm_num)
theorem B2159941 : Blo 1682041 2159941 := bbase (se 4 (by rfl) ⟨202494, by rfl⟩ : syracuseStep 2159941 = 404989) (by norm_num)
theorem B5682581 : Blo 1682041 5682581 := bbase (se 6 (by rfl) ⟨133185, by rfl⟩ : syracuseStep 5682581 = 266371) (by norm_num)
theorem B2839981 : Blo 1682041 2839981 := bbase (se 3 (by rfl) ⟨532496, by rfl⟩ : syracuseStep 2839981 = 1064993) (by norm_num)
theorem B2397613 : Blo 1682041 2397613 := bbase (se 3 (by rfl) ⟨449552, by rfl⟩ : syracuseStep 2397613 = 899105) (by norm_num)
theorem B2840069 : Blo 1682041 2840069 := bbase (se 4 (by rfl) ⟨266256, by rfl⟩ : syracuseStep 2840069 = 532513) (by norm_num)
theorem B12949109 : Blo 1682041 12949109 := bbase (se 5 (by rfl) ⟨606989, by rfl⟩ : syracuseStep 12949109 = 1213979) (by norm_num)
theorem B5117573 : Blo 1682041 5117573 := bbase (se 4 (by rfl) ⟨479772, by rfl⟩ : syracuseStep 5117573 = 959545) (by norm_num)
theorem B2840197 : Blo 1682041 2840197 := bbase (se 4 (by rfl) ⟨266268, by rfl⟩ : syracuseStep 2840197 = 532537) (by norm_num)
theorem B14382805 : Blo 1682041 14382805 := bbase (se 7 (by rfl) ⟨168548, by rfl⟩ : syracuseStep 14382805 = 337097) (by norm_num)
theorem B2840285 : Blo 1682041 2840285 := bbase (se 3 (by rfl) ⟨532553, by rfl⟩ : syracuseStep 2840285 = 1065107) (by norm_num)
theorem B7190309 : Blo 1682041 7190309 := bbase (se 4 (by rfl) ⟨674091, by rfl⟩ : syracuseStep 7190309 = 1348183) (by norm_num)
theorem B5683013 : Blo 1682041 5683013 := bbase (se 4 (by rfl) ⟨532782, by rfl⟩ : syracuseStep 5683013 = 1065565) (by norm_num)
theorem B3594061 : Blo 1682041 3594061 := bbase (se 3 (by rfl) ⟨673886, by rfl⟩ : syracuseStep 3594061 = 1347773) (by norm_num)
theorem B2840413 : Blo 1682041 2840413 := bbase (se 3 (by rfl) ⟨532577, by rfl⟩ : syracuseStep 2840413 = 1065155) (by norm_num)
theorem B13645685 : Blo 1682041 13645685 := bbase (se 5 (by rfl) ⟨639641, by rfl⟩ : syracuseStep 13645685 = 1279283) (by norm_num)
theorem B6387605 : Blo 1682041 6387605 := bbase (se 6 (by rfl) ⟨149709, by rfl⟩ : syracuseStep 6387605 = 299419) (by norm_num)
theorem B2840501 : Blo 1682041 2840501 := bbase (se 5 (by rfl) ⟨133148, by rfl⟩ : syracuseStep 2840501 = 266297) (by norm_num)
theorem B59062229 : Blo 1682041 59062229 := bbase (se 7 (by rfl) ⟨692135, by rfl⟩ : syracuseStep 59062229 = 1384271) (by norm_num)
theorem B2021333 : Blo 1682041 2021333 := bbase (se 7 (by rfl) ⟨23687, by rfl⟩ : syracuseStep 2021333 = 47375) (by norm_num)
theorem B4257805 : Blo 1682041 4257805 := bbase (se 3 (by rfl) ⟨798338, by rfl⟩ : syracuseStep 4257805 = 1596677) (by norm_num)
theorem B2021429 : Blo 1682041 2021429 := bbase (se 5 (by rfl) ⟨94754, by rfl⟩ : syracuseStep 2021429 = 189509) (by norm_num)
theorem B2840629 : Blo 1682041 2840629 := bbase (se 5 (by rfl) ⟨133154, by rfl⟩ : syracuseStep 2840629 = 266309) (by norm_num)
theorem B8198213 : Blo 1682041 8198213 := bbase (se 4 (by rfl) ⟨768582, by rfl⟩ : syracuseStep 8198213 = 1537165) (by norm_num)
theorem B2021449 : Blo 1682041 2021449 := bbase (se 2 (by rfl) ⟨758043, by rfl⟩ : syracuseStep 2021449 = 1516087) (by norm_num)
theorem B2734157 : Blo 1682041 2734157 := bbase (se 3 (by rfl) ⟨512654, by rfl⟩ : syracuseStep 2734157 = 1025309) (by norm_num)
theorem B4257917 : Blo 1682041 4257917 := bbase (se 3 (by rfl) ⟨798359, by rfl⟩ : syracuseStep 4257917 = 1596719) (by norm_num)
theorem B4044925 : Blo 1682041 4044925 := bbase (se 3 (by rfl) ⟨758423, by rfl⟩ : syracuseStep 4044925 = 1516847) (by norm_num)
theorem B2840717 : Blo 1682041 2840717 := bbase (se 3 (by rfl) ⟨532634, by rfl⟩ : syracuseStep 2840717 = 1065269) (by norm_num)
theorem B8517797 : Blo 1682041 8517797 := bbase (se 4 (by rfl) ⟨798543, by rfl⟩ : syracuseStep 8517797 = 1597087) (by norm_num)
theorem B4044973 : Blo 1682041 4044973 := bbase (se 3 (by rfl) ⟨758432, by rfl⟩ : syracuseStep 4044973 = 1516865) (by norm_num)
theorem B6387893 : Blo 1682041 6387893 := bbase (se 5 (by rfl) ⟨299432, by rfl⟩ : syracuseStep 6387893 = 598865) (by norm_num)
theorem B3840205 : Blo 1682041 3840205 := bbase (se 3 (by rfl) ⟨720038, by rfl⟩ : syracuseStep 3840205 = 1440077) (by norm_num)
theorem B2021593 : Blo 1682041 2021593 := bbase (se 2 (by rfl) ⟨758097, by rfl⟩ : syracuseStep 2021593 = 1516195) (by norm_num)
theorem B5683445 : Blo 1682041 5683445 := bbase (se 5 (by rfl) ⟨266411, by rfl⟩ : syracuseStep 5683445 = 532823) (by norm_num)
theorem B2840845 : Blo 1682041 2840845 := bbase (se 3 (by rfl) ⟨532658, by rfl⟩ : syracuseStep 2840845 = 1065317) (by norm_num)
theorem B4258109 : Blo 1682041 4258109 := bbase (se 3 (by rfl) ⟨798395, by rfl⟩ : syracuseStep 4258109 = 1596791) (by norm_num)
theorem B3594557 : Blo 1682041 3594557 := bbase (se 3 (by rfl) ⟨673979, by rfl⟩ : syracuseStep 3594557 = 1347959) (by norm_num)
theorem B4438349 : Blo 1682041 4438349 := bbase (se 3 (by rfl) ⟨832190, by rfl⟩ : syracuseStep 4438349 = 1664381) (by norm_num)
theorem B2840933 : Blo 1682041 2840933 := bbase (se 4 (by rfl) ⟨266337, by rfl⟩ : syracuseStep 2840933 = 532675) (by norm_num)
theorem B8092021 : Blo 1682041 8092021 := bbase (se 5 (by rfl) ⟨379313, by rfl⟩ : syracuseStep 8092021 = 758627) (by norm_num)
theorem B2841061 : Blo 1682041 2841061 := bbase (se 4 (by rfl) ⟨266349, by rfl⟩ : syracuseStep 2841061 = 532699) (by norm_num)
theorem B1972765 : Blo 1682041 1972765 := bbase (se 3 (by rfl) ⟨369893, by rfl⟩ : syracuseStep 1972765 = 739787) (by norm_num)
theorem B2841149 : Blo 1682041 2841149 := bbase (se 3 (by rfl) ⟨532715, by rfl⟩ : syracuseStep 2841149 = 1065431) (by norm_num)
theorem B3193445 : Blo 1682041 3193445 := bbase (se 4 (by rfl) ⟨299385, by rfl⟩ : syracuseStep 3193445 = 598771) (by norm_num)
theorem B4258453 : Blo 1682041 4258453 := bbase (se 6 (by rfl) ⟨99807, by rfl⟩ : syracuseStep 4258453 = 199615) (by norm_num)
theorem B2841277 : Blo 1682041 2841277 := bbase (se 3 (by rfl) ⟨532739, by rfl⟩ : syracuseStep 2841277 = 1065479) (by norm_num)
theorem B3840733 : Blo 1682041 3840733 := bbase (se 3 (by rfl) ⟨720137, by rfl⟩ : syracuseStep 3840733 = 1440275) (by norm_num)
theorem B3193597 : Blo 1682041 3193597 := bbase (se 3 (by rfl) ⟨598799, by rfl⟩ : syracuseStep 3193597 = 1197599) (by norm_num)
theorem B4258565 : Blo 1682041 4258565 := bbase (se 4 (by rfl) ⟨399240, by rfl⟩ : syracuseStep 4258565 = 798481) (by norm_num)
theorem B6077189 : Blo 1682041 6077189 := bbase (se 4 (by rfl) ⟨569736, by rfl⟩ : syracuseStep 6077189 = 1139473) (by norm_num)
theorem B7191301 : Blo 1682041 7191301 := bbase (se 4 (by rfl) ⟨674184, by rfl⟩ : syracuseStep 7191301 = 1348369) (by norm_num)
theorem B4045589 : Blo 1682041 4045589 := bbase (se 6 (by rfl) ⟨94818, by rfl⟩ : syracuseStep 4045589 = 189637) (by norm_num)
theorem B2841365 : Blo 1682041 2841365 := bbase (se 6 (by rfl) ⟨66594, by rfl⟩ : syracuseStep 2841365 = 133189) (by norm_num)
theorem B4791125 : Blo 1682041 4791125 := bbase (se 9 (by rfl) ⟨14036, by rfl⟩ : syracuseStep 4791125 = 28073) (by norm_num)
theorem B2841493 : Blo 1682041 2841493 := bbase (se 6 (by rfl) ⟨66597, by rfl⟩ : syracuseStep 2841493 = 133195) (by norm_num)
theorem B2128837 : Blo 1682041 2128837 := bbase (se 4 (by rfl) ⟨199578, by rfl⟩ : syracuseStep 2128837 = 399157) (by norm_num)
theorem B4258757 : Blo 1682041 4258757 := bbase (se 4 (by rfl) ⟨399258, by rfl⟩ : syracuseStep 4258757 = 798517) (by norm_num)
theorem B2841581 : Blo 1682041 2841581 := bbase (se 3 (by rfl) ⟨532796, by rfl⟩ : syracuseStep 2841581 = 1065593) (by norm_num)
theorem B8084485 : Blo 1682041 8084485 := bbase (se 4 (by rfl) ⟨757920, by rfl⟩ : syracuseStep 8084485 = 1515841) (by norm_num)
theorem B21855253 : Blo 1682041 21855253 := bbase (se 6 (by rfl) ⟨512232, by rfl⟩ : syracuseStep 21855253 = 1024465) (by norm_num)
theorem B2128933 : Blo 1682041 2128933 := bbase (se 4 (by rfl) ⟨199587, by rfl⟩ : syracuseStep 2128933 = 399175) (by norm_num)
theorem B3193901 : Blo 1682041 3193901 := bbase (se 3 (by rfl) ⟨598856, by rfl⟩ : syracuseStep 3193901 = 1197713) (by norm_num)
theorem B4045933 : Blo 1682041 4045933 := bbase (se 3 (by rfl) ⟨758612, by rfl⟩ : syracuseStep 4045933 = 1517225) (by norm_num)
theorem B2841709 : Blo 1682041 2841709 := bbase (se 3 (by rfl) ⟨532820, by rfl⟩ : syracuseStep 2841709 = 1065641) (by norm_num)
theorem B3595421 : Blo 1682041 3595421 := bbase (se 3 (by rfl) ⟨674141, by rfl⟩ : syracuseStep 3595421 = 1348283) (by norm_num)
theorem B2841797 : Blo 1682041 2841797 := bbase (se 4 (by rfl) ⟨266418, by rfl⟩ : syracuseStep 2841797 = 532837) (by norm_num)
theorem B2129105 : Blo 1682041 2129105 := bbase (se 2 (by rfl) ⟨798414, by rfl⟩ : syracuseStep 2129105 = 1596829) (by norm_num)
theorem B2129161 : Blo 1682041 2129161 := bbase (se 2 (by rfl) ⟨798435, by rfl⟩ : syracuseStep 2129161 = 1596871) (by norm_num)
theorem B4259101 : Blo 1682041 4259101 := bbase (se 3 (by rfl) ⟨798581, by rfl⟩ : syracuseStep 4259101 = 1597163) (by norm_num)
theorem B3595565 : Blo 1682041 3595565 := bbase (se 3 (by rfl) ⟨674168, by rfl⟩ : syracuseStep 3595565 = 1348337) (by norm_num)
theorem B6389077 : Blo 1682041 6389077 := bbase (se 11 (by rfl) ⟨4679, by rfl⟩ : syracuseStep 6389077 = 9359) (by norm_num)
theorem B4046165 : Blo 1682041 4046165 := bbase (se 11 (by rfl) ⟨2963, by rfl⟩ : syracuseStep 4046165 = 5927) (by norm_num)
theorem B2129257 : Blo 1682041 2129257 := bbase (se 2 (by rfl) ⟨798471, by rfl⟩ : syracuseStep 2129257 = 1596943) (by norm_num)
theorem B4259213 : Blo 1682041 4259213 := bbase (se 3 (by rfl) ⟨798602, by rfl⟩ : syracuseStep 4259213 = 1597205) (by norm_num)
theorem B8519093 : Blo 1682041 8519093 := bbase (se 5 (by rfl) ⟨399332, by rfl⟩ : syracuseStep 8519093 = 798665) (by norm_num)
theorem B2694637 : Blo 1682041 2694637 := bbase (se 3 (by rfl) ⟨505244, by rfl⟩ : syracuseStep 2694637 = 1010489) (by norm_num)
theorem B2129429 : Blo 1682041 2129429 := bbase (se 6 (by rfl) ⟨49908, by rfl⟩ : syracuseStep 2129429 = 99817) (by norm_num)
theorem B2694701 : Blo 1682041 2694701 := bbase (se 3 (by rfl) ⟨505256, by rfl⟩ : syracuseStep 2694701 = 1010513) (by norm_num)
theorem B2129485 : Blo 1682041 2129485 := bbase (se 3 (by rfl) ⟨399278, by rfl⟩ : syracuseStep 2129485 = 798557) (by norm_num)
theorem B4259405 : Blo 1682041 4259405 := bbase (se 3 (by rfl) ⟨798638, by rfl⟩ : syracuseStep 4259405 = 1597277) (by norm_num)
theorem B6389381 : Blo 1682041 6389381 := bbase (se 4 (by rfl) ⟨599004, by rfl⟩ : syracuseStep 6389381 = 1198009) (by norm_num)
theorem B14384789 : Blo 1682041 14384789 := bbase (se 6 (by rfl) ⟨337143, by rfl⟩ : syracuseStep 14384789 = 674287) (by norm_num)
theorem B2129581 : Blo 1682041 2129581 := bbase (se 3 (by rfl) ⟨399296, by rfl⟩ : syracuseStep 2129581 = 798593) (by norm_num)
theorem B3890917 : Blo 1682041 3890917 := bbase (se 4 (by rfl) ⟨364773, by rfl⟩ : syracuseStep 3890917 = 729547) (by norm_num)
theorem B3194653 : Blo 1682041 3194653 := bbase (se 3 (by rfl) ⟨598997, by rfl⟩ : syracuseStep 3194653 = 1197995) (by norm_num)
theorem B92118869 : Blo 1682041 92118869 := bbase (se 9 (by rfl) ⟨269879, by rfl⟩ : syracuseStep 92118869 = 539759) (by norm_num)
theorem B2129753 : Blo 1682041 2129753 := bbase (se 2 (by rfl) ⟨798657, by rfl⟩ : syracuseStep 2129753 = 1597315) (by norm_num)
theorem B9715573 : Blo 1682041 9715573 := bbase (se 5 (by rfl) ⟨455417, by rfl⟩ : syracuseStep 9715573 = 910835) (by norm_num)
theorem B2129809 : Blo 1682041 2129809 := bbase (se 2 (by rfl) ⟨798678, by rfl⟩ : syracuseStep 2129809 = 1597357) (by norm_num)
theorem B5676965 : Blo 1682041 5676965 := bbase (se 4 (by rfl) ⟨532215, by rfl⟩ : syracuseStep 5676965 = 1064431) (by norm_num)
theorem B4259749 : Blo 1682041 4259749 := bbase (se 4 (by rfl) ⟨399351, by rfl⟩ : syracuseStep 4259749 = 798703) (by norm_num)
theorem B3194797 : Blo 1682041 3194797 := bbase (se 3 (by rfl) ⟨599024, by rfl⟩ : syracuseStep 3194797 = 1198049) (by norm_num)
theorem B2523077 : Blo 1682041 2523077 := bbase (se 4 (by rfl) ⟨236538, by rfl⟩ : syracuseStep 2523077 = 473077) (by norm_num)
theorem B3784661 : Blo 1682041 3784661 := bbase (se 7 (by rfl) ⟨44351, by rfl⟩ : syracuseStep 3784661 = 88703) (by norm_num)
theorem B1892317 : Blo 1682041 1892317 := bbase (se 3 (by rfl) ⟨354809, by rfl⟩ : syracuseStep 1892317 = 709619) (by norm_num)
theorem B2523101 : Blo 1682041 2523101 := bbase (se 3 (by rfl) ⟨473081, by rfl⟩ : syracuseStep 2523101 = 946163) (by norm_num)
theorem B2129905 : Blo 1682041 2129905 := bbase (se 2 (by rfl) ⟨798714, by rfl⟩ : syracuseStep 2129905 = 1597429) (by norm_num)
theorem B2523125 : Blo 1682041 2523125 := bbase (se 5 (by rfl) ⟨118271, by rfl⟩ : syracuseStep 2523125 = 236543) (by norm_num)
theorem B2523137 : Blo 1682041 2523137 := bstep (se 2 (by rfl) ⟨946176, by rfl⟩ : syracuseStep 2523137 = 1892353) B1892353
theorem B5120003 : Blo 1682041 5120003 := bstep (se 1 (by rfl) ⟨3840002, by rfl⟩ : syracuseStep 5120003 = 7680005) B7680005
theorem B5677073 : Blo 1682041 5677073 := bstep (se 2 (by rfl) ⟨2128902, by rfl⟩ : syracuseStep 5677073 = 4257805) B4257805
theorem B2523155 : Blo 1682041 2523155 := bstep (se 1 (by rfl) ⟨1892366, by rfl⟩ : syracuseStep 2523155 = 3784733) B3784733
theorem B1892371 : Blo 1682041 1892371 := bstep (se 1 (by rfl) ⟨1419278, by rfl⟩ : syracuseStep 1892371 = 2838557) B2838557
theorem B4792355 : Blo 1682041 4792355 := bstep (se 1 (by rfl) ⟨3594266, by rfl⟩ : syracuseStep 4792355 = 7188533) B7188533
theorem B2523185 : Blo 1682041 2523185 := bstep (se 2 (by rfl) ⟨946194, by rfl⟩ : syracuseStep 2523185 = 1892389) B1892389
theorem B2129971 : Blo 1682041 2129971 := bstep (se 1 (by rfl) ⟨1597478, by rfl⟩ : syracuseStep 2129971 = 3194957) B3194957
theorem B2523203 : Blo 1682041 2523203 := bstep (se 1 (by rfl) ⟨1892402, by rfl⟩ : syracuseStep 2523203 = 3784805) B3784805
theorem B6389837 : Blo 1682041 6389837 := bstep (se 3 (by rfl) ⟨1198094, by rfl⟩ : syracuseStep 6389837 = 2396189) B2396189
theorem B2523233 : Blo 1682041 2523233 := bstep (se 2 (by rfl) ⟨946212, by rfl⟩ : syracuseStep 2523233 = 1892425) B1892425
theorem B2695265 : Blo 1682041 2695265 := bstep (se 2 (by rfl) ⟨1010724, by rfl⟩ : syracuseStep 2695265 = 2021449) B2021449
theorem B2523251 : Blo 1682041 2523251 := bstep (se 1 (by rfl) ⟨1892438, by rfl⟩ : syracuseStep 2523251 = 3784877) B3784877
theorem B5390477 : Blo 1682041 5390477 := bstep (se 3 (by rfl) ⟨1010714, by rfl⟩ : syracuseStep 5390477 = 2021429) B2021429
theorem B2523281 : Blo 1682041 2523281 := bstep (se 2 (by rfl) ⟨946230, by rfl⟩ : syracuseStep 2523281 = 1892461) B1892461
theorem B2130067 : Blo 1682041 2130067 := bstep (se 1 (by rfl) ⟨1597550, by rfl⟩ : syracuseStep 2130067 = 3195101) B3195101
theorem B2523299 : Blo 1682041 2523299 := bstep (se 1 (by rfl) ⟨1892474, by rfl⟩ : syracuseStep 2523299 = 3784949) B3784949
theorem B1892515 : Blo 1682041 1892515 := bstep (se 1 (by rfl) ⟨1419386, by rfl⟩ : syracuseStep 1892515 = 2838773) B2838773
theorem B2523329 : Blo 1682041 2523329 := bstep (se 2 (by rfl) ⟨946248, by rfl⟩ : syracuseStep 2523329 = 1892497) B1892497
theorem B3784913 : Blo 1682041 3784913 := bstep (se 2 (by rfl) ⟨1419342, by rfl⟩ : syracuseStep 3784913 = 2838685) B2838685
theorem B2523347 : Blo 1682041 2523347 := bstep (se 1 (by rfl) ⟨1892510, by rfl⟩ : syracuseStep 2523347 = 3785021) B3785021
theorem B3784931 : Blo 1682041 3784931 := bstep (se 1 (by rfl) ⟨2838698, by rfl⟩ : syracuseStep 3784931 = 5677397) B5677397
theorem B2523377 : Blo 1682041 2523377 := bstep (se 2 (by rfl) ⟨946266, by rfl⟩ : syracuseStep 2523377 = 1892533) B1892533
theorem B2523395 : Blo 1682041 2523395 := bstep (se 1 (by rfl) ⟨1892546, by rfl⟩ : syracuseStep 2523395 = 3785093) B3785093
theorem B3195139 : Blo 1682041 3195139 := bstep (se 1 (by rfl) ⟨2396354, by rfl⟩ : syracuseStep 3195139 = 4792709) B4792709
theorem B5120273 : Blo 1682041 5120273 := bstep (se 2 (by rfl) ⟨1920102, by rfl⟩ : syracuseStep 5120273 = 3840205) B3840205
theorem B2523425 : Blo 1682041 2523425 := bstep (se 2 (by rfl) ⟨946284, by rfl⟩ : syracuseStep 2523425 = 1892569) B1892569
theorem B2695457 : Blo 1682041 2695457 := bstep (se 2 (by rfl) ⟨1010796, by rfl⟩ : syracuseStep 2695457 = 2021593) B2021593
theorem B2523443 : Blo 1682041 2523443 := bstep (se 1 (by rfl) ⟨1892582, by rfl⟩ : syracuseStep 2523443 = 3785165) B3785165
theorem B1892659 : Blo 1682041 1892659 := bstep (se 1 (by rfl) ⟨1419494, by rfl⟩ : syracuseStep 1892659 = 2838989) B2838989
theorem B2523473 : Blo 1682041 2523473 := bstep (se 2 (by rfl) ⟨946302, by rfl⟩ : syracuseStep 2523473 = 1892605) B1892605
theorem B2523491 : Blo 1682041 2523491 := bstep (se 1 (by rfl) ⟨1892618, by rfl⟩ : syracuseStep 2523491 = 3785237) B3785237
theorem B2523521 : Blo 1682041 2523521 := bstep (se 2 (by rfl) ⟨946320, by rfl⟩ : syracuseStep 2523521 = 1892641) B1892641
theorem B2523539 : Blo 1682041 2523539 := bstep (se 1 (by rfl) ⟨1892654, by rfl⟩ : syracuseStep 2523539 = 3785309) B3785309
theorem B2523569 : Blo 1682041 2523569 := bstep (se 2 (by rfl) ⟨946338, by rfl⟩ : syracuseStep 2523569 = 1892677) B1892677
theorem B2523587 : Blo 1682041 2523587 := bstep (se 1 (by rfl) ⟨1892690, by rfl⟩ : syracuseStep 2523587 = 3785381) B3785381
theorem B1892803 : Blo 1682041 1892803 := bstep (se 1 (by rfl) ⟨1419602, by rfl⟩ : syracuseStep 1892803 = 2839205) B2839205
theorem B21856709 : Blo 1682041 21856709 := bstep (se 4 (by rfl) ⟨2049066, by rfl⟩ : syracuseStep 21856709 = 4098133) B4098133
theorem B2523617 : Blo 1682041 2523617 := bstep (se 2 (by rfl) ⟨946356, by rfl⟩ : syracuseStep 2523617 = 1892713) B1892713
theorem B3785201 : Blo 1682041 3785201 := bstep (se 2 (by rfl) ⟨1419450, by rfl⟩ : syracuseStep 3785201 = 2838901) B2838901
theorem B10789361 : Blo 1682041 10789361 := bstep (se 2 (by rfl) ⟨4046010, by rfl⟩ : syracuseStep 10789361 = 8092021) B8092021
theorem B2523635 : Blo 1682041 2523635 := bstep (se 1 (by rfl) ⟨1892726, by rfl⟩ : syracuseStep 2523635 = 3785453) B3785453
theorem B3785219 : Blo 1682041 3785219 := bstep (se 1 (by rfl) ⟨2838914, by rfl⟩ : syracuseStep 3785219 = 5677829) B5677829
theorem B10928645 : Blo 1682041 10928645 := bstep (se 4 (by rfl) ⟨1024560, by rfl⟩ : syracuseStep 10928645 = 2049121) B2049121
theorem B2523665 : Blo 1682041 2523665 := bstep (se 2 (by rfl) ⟨946374, by rfl⟩ : syracuseStep 2523665 = 1892749) B1892749
theorem B2523683 : Blo 1682041 2523683 := bstep (se 1 (by rfl) ⟨1892762, by rfl⟩ : syracuseStep 2523683 = 3785525) B3785525
theorem B8520227 : Blo 1682041 8520227 := bstep (se 1 (by rfl) ⟨6390170, by rfl⟩ : syracuseStep 8520227 = 12780341) B12780341
theorem B5677613 : Blo 1682041 5677613 := bstep (se 3 (by rfl) ⟨1064552, by rfl⟩ : syracuseStep 5677613 = 2129105) B2129105
theorem B2523713 : Blo 1682041 2523713 := bstep (se 2 (by rfl) ⟨946392, by rfl⟩ : syracuseStep 2523713 = 1892785) B1892785
theorem B21578309 : Blo 1682041 21578309 := bstep (se 4 (by rfl) ⟨2022966, by rfl⟩ : syracuseStep 21578309 = 4045933) B4045933
theorem B2523731 : Blo 1682041 2523731 := bstep (se 1 (by rfl) ⟨1892798, by rfl⟩ : syracuseStep 2523731 = 3785597) B3785597
theorem B1892947 : Blo 1682041 1892947 := bstep (se 1 (by rfl) ⟨1419710, by rfl⟩ : syracuseStep 1892947 = 2839421) B2839421
theorem B5677667 : Blo 1682041 5677667 := bstep (se 1 (by rfl) ⟨4258250, by rfl⟩ : syracuseStep 5677667 = 8516501) B8516501
theorem B2523761 : Blo 1682041 2523761 := bstep (se 2 (by rfl) ⟨946410, by rfl⟩ : syracuseStep 2523761 = 1892821) B1892821
theorem B2523779 : Blo 1682041 2523779 := bstep (se 1 (by rfl) ⟨1892834, by rfl⟩ : syracuseStep 2523779 = 3785669) B3785669
theorem B2130563 : Blo 1682041 2130563 := bstep (se 1 (by rfl) ⟨1597922, by rfl⟩ : syracuseStep 2130563 = 3195845) B3195845
theorem B2523809 : Blo 1682041 2523809 := bstep (se 2 (by rfl) ⟨946428, by rfl⟩ : syracuseStep 2523809 = 1892857) B1892857
theorem B2523827 : Blo 1682041 2523827 := bstep (se 1 (by rfl) ⟨1892870, by rfl⟩ : syracuseStep 2523827 = 3785741) B3785741
theorem B3195587 : Blo 1682041 3195587 := bstep (se 1 (by rfl) ⟨2396690, by rfl⟩ : syracuseStep 3195587 = 4793381) B4793381
theorem B2523857 : Blo 1682041 2523857 := bstep (se 2 (by rfl) ⟨946446, by rfl⟩ : syracuseStep 2523857 = 1892893) B1892893
theorem B2523875 : Blo 1682041 2523875 := bstep (se 1 (by rfl) ⟨1892906, by rfl⟩ : syracuseStep 2523875 = 3785813) B3785813
theorem B1893091 : Blo 1682041 1893091 := bstep (se 1 (by rfl) ⟨1419818, by rfl⟩ : syracuseStep 1893091 = 2839637) B2839637
theorem B5759729 : Blo 1682041 5759729 := bstep (se 2 (by rfl) ⟨2159898, by rfl⟩ : syracuseStep 5759729 = 4319797) B4319797
theorem B2523905 : Blo 1682041 2523905 := bstep (se 2 (by rfl) ⟨946464, by rfl⟩ : syracuseStep 2523905 = 1892929) B1892929
theorem B3785489 : Blo 1682041 3785489 := bstep (se 2 (by rfl) ⟨1419558, by rfl⟩ : syracuseStep 3785489 = 2839117) B2839117
theorem B2523923 : Blo 1682041 2523923 := bstep (se 1 (by rfl) ⟨1892942, by rfl⟩ : syracuseStep 2523923 = 3785885) B3785885
theorem B9093923 : Blo 1682041 9093923 := bstep (se 1 (by rfl) ⟨6820442, by rfl⟩ : syracuseStep 9093923 = 13640885) B13640885
theorem B3785507 : Blo 1682041 3785507 := bstep (se 1 (by rfl) ⟨2839130, by rfl⟩ : syracuseStep 3785507 = 5678261) B5678261
theorem B2523953 : Blo 1682041 2523953 := bstep (se 2 (by rfl) ⟨946482, by rfl⟩ : syracuseStep 2523953 = 1892965) B1892965
theorem B2523971 : Blo 1682041 2523971 := bstep (se 1 (by rfl) ⟨1892978, by rfl⟩ : syracuseStep 2523971 = 3785957) B3785957
theorem B9585485 : Blo 1682041 9585485 := bstep (se 3 (by rfl) ⟨1797278, by rfl⟩ : syracuseStep 9585485 = 3594557) B3594557
theorem B4793165 : Blo 1682041 4793165 := bstep (se 3 (by rfl) ⟨898718, by rfl⟩ : syracuseStep 4793165 = 1797437) B1797437
theorem B2524001 : Blo 1682041 2524001 := bstep (se 2 (by rfl) ⟨946500, by rfl⟩ : syracuseStep 2524001 = 1893001) B1893001
theorem B5677937 : Blo 1682041 5677937 := bstep (se 2 (by rfl) ⟨2129226, by rfl⟩ : syracuseStep 5677937 = 4258453) B4258453
theorem B4260721 : Blo 1682041 4260721 := bstep (se 2 (by rfl) ⟨1597770, by rfl⟩ : syracuseStep 4260721 = 3195541) B3195541
theorem B2524019 : Blo 1682041 2524019 := bstep (se 1 (by rfl) ⟨1893014, by rfl⟩ : syracuseStep 2524019 = 3786029) B3786029
theorem B1893235 : Blo 1682041 1893235 := bstep (se 1 (by rfl) ⟨1419926, by rfl⟩ : syracuseStep 1893235 = 2839853) B2839853
theorem B11518861 : Blo 1682041 11518861 := bstep (se 3 (by rfl) ⟨2159786, by rfl⟩ : syracuseStep 11518861 = 4319573) B4319573
theorem B2524049 : Blo 1682041 2524049 := bstep (se 2 (by rfl) ⟨946518, by rfl⟩ : syracuseStep 2524049 = 1893037) B1893037
theorem B2524067 : Blo 1682041 2524067 := bstep (se 1 (by rfl) ⟨1893050, by rfl⟩ : syracuseStep 2524067 = 3786101) B3786101
theorem B2524097 : Blo 1682041 2524097 := bstep (se 2 (by rfl) ⟨946536, by rfl⟩ : syracuseStep 2524097 = 1893073) B1893073
theorem B5120977 : Blo 1682041 5120977 := bstep (se 2 (by rfl) ⟨1920366, by rfl⟩ : syracuseStep 5120977 = 3840733) B3840733
theorem B2524115 : Blo 1682041 2524115 := bstep (se 1 (by rfl) ⟨1893086, by rfl⟩ : syracuseStep 2524115 = 3786173) B3786173
theorem B3195875 : Blo 1682041 3195875 := bstep (se 1 (by rfl) ⟨2396906, by rfl⟩ : syracuseStep 3195875 = 4793813) B4793813
theorem B2524145 : Blo 1682041 2524145 := bstep (se 2 (by rfl) ⟨946554, by rfl⟩ : syracuseStep 2524145 = 1893109) B1893109
theorem B2524163 : Blo 1682041 2524163 := bstep (se 1 (by rfl) ⟨1893122, by rfl⟩ : syracuseStep 2524163 = 3786245) B3786245
theorem B1893379 : Blo 1682041 1893379 := bstep (se 1 (by rfl) ⟨1420034, by rfl⟩ : syracuseStep 1893379 = 2840069) B2840069
theorem B16172045 : Blo 1682041 16172045 := bstep (se 3 (by rfl) ⟨3032258, by rfl⟩ : syracuseStep 16172045 = 6064517) B6064517
theorem B4793357 : Blo 1682041 4793357 := bstep (se 3 (by rfl) ⟨898754, by rfl⟩ : syracuseStep 4793357 = 1797509) B1797509
theorem B46048277 : Blo 1682041 46048277 := bstep (se 6 (by rfl) ⟨1079256, by rfl⟩ : syracuseStep 46048277 = 2158513) B2158513
theorem B2524193 : Blo 1682041 2524193 := bstep (se 2 (by rfl) ⟨946572, by rfl⟩ : syracuseStep 2524193 = 1893145) B1893145
theorem B3785777 : Blo 1682041 3785777 := bstep (se 2 (by rfl) ⟨1419666, by rfl⟩ : syracuseStep 3785777 = 2839333) B2839333
theorem B2524211 : Blo 1682041 2524211 := bstep (se 1 (by rfl) ⟨1893158, by rfl⟩ : syracuseStep 2524211 = 3786317) B3786317
theorem B3785795 : Blo 1682041 3785795 := bstep (se 1 (by rfl) ⟨2839346, by rfl⟩ : syracuseStep 3785795 = 5678693) B5678693
theorem B2524241 : Blo 1682041 2524241 := bstep (se 2 (by rfl) ⟨946590, by rfl⟩ : syracuseStep 2524241 = 1893181) B1893181
theorem B2524259 : Blo 1682041 2524259 := bstep (se 1 (by rfl) ⟨1893194, by rfl⟩ : syracuseStep 2524259 = 3786389) B3786389
theorem B46040177 : Blo 1682041 46040177 := bstep (se 2 (by rfl) ⟨17265066, by rfl⟩ : syracuseStep 46040177 = 34530133) B34530133
theorem B2524289 : Blo 1682041 2524289 := bstep (se 2 (by rfl) ⟨946608, by rfl⟩ : syracuseStep 2524289 = 1893217) B1893217
theorem B4260995 : Blo 1682041 4260995 := bstep (se 1 (by rfl) ⟨3195746, by rfl⟩ : syracuseStep 4260995 = 6391493) B6391493
theorem B2524307 : Blo 1682041 2524307 := bstep (se 1 (by rfl) ⟨1893230, by rfl⟩ : syracuseStep 2524307 = 3786461) B3786461
theorem B1893523 : Blo 1682041 1893523 := bstep (se 1 (by rfl) ⟨1420142, by rfl⟩ : syracuseStep 1893523 = 2840285) B2840285
theorem B6063281 : Blo 1682041 6063281 := bstep (se 2 (by rfl) ⟨2273730, by rfl⟩ : syracuseStep 6063281 = 4547461) B4547461
theorem B2524337 : Blo 1682041 2524337 := bstep (se 2 (by rfl) ⟨946626, by rfl⟩ : syracuseStep 2524337 = 1893253) B1893253
theorem B2524355 : Blo 1682041 2524355 := bstep (se 1 (by rfl) ⟨1893266, by rfl⟩ : syracuseStep 2524355 = 3786533) B3786533
theorem B2524385 : Blo 1682041 2524385 := bstep (se 2 (by rfl) ⟨946644, by rfl⟩ : syracuseStep 2524385 = 1893289) B1893289
theorem B2524403 : Blo 1682041 2524403 := bstep (se 1 (by rfl) ⟨1893302, by rfl⟩ : syracuseStep 2524403 = 3786605) B3786605
theorem B2524433 : Blo 1682041 2524433 := bstep (se 2 (by rfl) ⟨946662, by rfl⟩ : syracuseStep 2524433 = 1893325) B1893325
theorem B2524451 : Blo 1682041 2524451 := bstep (se 1 (by rfl) ⟨1893338, by rfl⟩ : syracuseStep 2524451 = 3786677) B3786677
theorem B1893667 : Blo 1682041 1893667 := bstep (se 1 (by rfl) ⟨1420250, by rfl⟩ : syracuseStep 1893667 = 2840501) B2840501
theorem B2524481 : Blo 1682041 2524481 := bstep (se 2 (by rfl) ⟨946680, by rfl⟩ : syracuseStep 2524481 = 1893361) B1893361
theorem B4261187 : Blo 1682041 4261187 := bstep (se 1 (by rfl) ⟨3195890, by rfl⟩ : syracuseStep 4261187 = 6391781) B6391781
theorem B2131267 : Blo 1682041 2131267 := bstep (se 1 (by rfl) ⟨1598450, by rfl⟩ : syracuseStep 2131267 = 3196901) B3196901
theorem B8521037 : Blo 1682041 8521037 := bstep (se 3 (by rfl) ⟨1597694, by rfl⟩ : syracuseStep 8521037 = 3195389) B3195389
theorem B3786065 : Blo 1682041 3786065 := bstep (se 2 (by rfl) ⟨1419774, by rfl⟩ : syracuseStep 3786065 = 2839549) B2839549
theorem B2524499 : Blo 1682041 2524499 := bstep (se 1 (by rfl) ⟨1893374, by rfl⟩ : syracuseStep 2524499 = 3786749) B3786749
theorem B3786083 : Blo 1682041 3786083 := bstep (se 1 (by rfl) ⟨2839562, by rfl⟩ : syracuseStep 3786083 = 5679125) B5679125
theorem B29140337 : Blo 1682041 29140337 := bstep (se 2 (by rfl) ⟨10927626, by rfl⟩ : syracuseStep 29140337 = 21855253) B21855253
theorem B2524529 : Blo 1682041 2524529 := bstep (se 2 (by rfl) ⟨946698, by rfl⟩ : syracuseStep 2524529 = 1893397) B1893397
theorem B2524547 : Blo 1682041 2524547 := bstep (se 1 (by rfl) ⟨1893410, by rfl⟩ : syracuseStep 2524547 = 3786821) B3786821
theorem B5678477 : Blo 1682041 5678477 := bstep (se 3 (by rfl) ⟨1064714, by rfl⟩ : syracuseStep 5678477 = 2129429) B2129429
theorem B2524577 : Blo 1682041 2524577 := bstep (se 2 (by rfl) ⟨946716, by rfl⟩ : syracuseStep 2524577 = 1893433) B1893433
theorem B2131363 : Blo 1682041 2131363 := bstep (se 1 (by rfl) ⟨1598522, by rfl⟩ : syracuseStep 2131363 = 3197045) B3197045
theorem B4859309 : Blo 1682041 4859309 := bstep (se 3 (by rfl) ⟨911120, by rfl⟩ : syracuseStep 4859309 = 1822241) B1822241
theorem B2524595 : Blo 1682041 2524595 := bstep (se 1 (by rfl) ⟨1893446, by rfl⟩ : syracuseStep 2524595 = 3786893) B3786893
theorem B1893811 : Blo 1682041 1893811 := bstep (se 1 (by rfl) ⟨1420358, by rfl⟩ : syracuseStep 1893811 = 2840717) B2840717
theorem B5678531 : Blo 1682041 5678531 := bstep (se 1 (by rfl) ⟨4258898, by rfl⟩ : syracuseStep 5678531 = 8517797) B8517797
theorem B2524625 : Blo 1682041 2524625 := bstep (se 2 (by rfl) ⟨946734, by rfl⟩ : syracuseStep 2524625 = 1893469) B1893469
theorem B2524643 : Blo 1682041 2524643 := bstep (se 1 (by rfl) ⟨1893482, by rfl⟩ : syracuseStep 2524643 = 3786965) B3786965
theorem B2524673 : Blo 1682041 2524673 := bstep (se 2 (by rfl) ⟨946752, by rfl⟩ : syracuseStep 2524673 = 1893505) B1893505
theorem B2524691 : Blo 1682041 2524691 := bstep (se 1 (by rfl) ⟨1893518, by rfl⟩ : syracuseStep 2524691 = 3787037) B3787037
theorem B2524721 : Blo 1682041 2524721 := bstep (se 2 (by rfl) ⟨946770, by rfl⟩ : syracuseStep 2524721 = 1893541) B1893541
theorem B2958899 : Blo 1682041 2958899 := bstep (se 1 (by rfl) ⟨2219174, by rfl⟩ : syracuseStep 2958899 = 4438349) B4438349
theorem B20473397 : Blo 1682041 20473397 := bstep (se 5 (by rfl) ⟨959690, by rfl⟩ : syracuseStep 20473397 = 1919381) B1919381
theorem B2524739 : Blo 1682041 2524739 := bstep (se 1 (by rfl) ⟨1893554, by rfl⟩ : syracuseStep 2524739 = 3787109) B3787109
theorem B1893955 : Blo 1682041 1893955 := bstep (se 1 (by rfl) ⟨1420466, by rfl⟩ : syracuseStep 1893955 = 2840933) B2840933
theorem B2524769 : Blo 1682041 2524769 := bstep (se 2 (by rfl) ⟨946788, by rfl⟩ : syracuseStep 2524769 = 1893577) B1893577
theorem B3786353 : Blo 1682041 3786353 := bstep (se 2 (by rfl) ⟨1419882, by rfl⟩ : syracuseStep 3786353 = 2839765) B2839765
theorem B2524787 : Blo 1682041 2524787 := bstep (se 1 (by rfl) ⟨1893590, by rfl⟩ : syracuseStep 2524787 = 3787181) B3787181
theorem B3786371 : Blo 1682041 3786371 := bstep (se 1 (by rfl) ⟨2839778, by rfl⟩ : syracuseStep 3786371 = 5679557) B5679557
theorem B5392003 : Blo 1682041 5392003 := bstep (se 1 (by rfl) ⟨4044002, by rfl⟩ : syracuseStep 5392003 = 8088005) B8088005
theorem B2524817 : Blo 1682041 2524817 := bstep (se 2 (by rfl) ⟨946806, by rfl⟩ : syracuseStep 2524817 = 1893613) B1893613
theorem B2524835 : Blo 1682041 2524835 := bstep (se 1 (by rfl) ⟨1893626, by rfl⟩ : syracuseStep 2524835 = 3787253) B3787253
theorem B2524865 : Blo 1682041 2524865 := bstep (se 2 (by rfl) ⟨946824, by rfl⟩ : syracuseStep 2524865 = 1893649) B1893649
theorem B5678801 : Blo 1682041 5678801 := bstep (se 2 (by rfl) ⟨2129550, by rfl⟩ : syracuseStep 5678801 = 4259101) B4259101
theorem B2524883 : Blo 1682041 2524883 := bstep (se 1 (by rfl) ⟨1893662, by rfl⟩ : syracuseStep 2524883 = 3787325) B3787325
theorem B1894099 : Blo 1682041 1894099 := bstep (se 1 (by rfl) ⟨1420574, by rfl⟩ : syracuseStep 1894099 = 2841149) B2841149
theorem B2524913 : Blo 1682041 2524913 := bstep (se 2 (by rfl) ⟨946842, by rfl⟩ : syracuseStep 2524913 = 1893685) B1893685
theorem B2524931 : Blo 1682041 2524931 := bstep (se 1 (by rfl) ⟨1893698, by rfl⟩ : syracuseStep 2524931 = 3787397) B3787397
theorem B2524961 : Blo 1682041 2524961 := bstep (se 2 (by rfl) ⟨946860, by rfl⟩ : syracuseStep 2524961 = 1893721) B1893721
theorem B2524979 : Blo 1682041 2524979 := bstep (se 1 (by rfl) ⟨1893734, by rfl⟩ : syracuseStep 2524979 = 3787469) B3787469
theorem B2525009 : Blo 1682041 2525009 := bstep (se 2 (by rfl) ⟨946878, by rfl⟩ : syracuseStep 2525009 = 1893757) B1893757
theorem B2525027 : Blo 1682041 2525027 := bstep (se 1 (by rfl) ⟨1893770, by rfl⟩ : syracuseStep 2525027 = 3787541) B3787541
theorem B2697059 : Blo 1682041 2697059 := bstep (se 1 (by rfl) ⟨2022794, by rfl⟩ : syracuseStep 2697059 = 4045589) B4045589
theorem B1894243 : Blo 1682041 1894243 := bstep (se 1 (by rfl) ⟨1420682, by rfl⟩ : syracuseStep 1894243 = 2841365) B2841365
theorem B5760881 : Blo 1682041 5760881 := bstep (se 2 (by rfl) ⟨2160330, by rfl⟩ : syracuseStep 5760881 = 4320661) B4320661
theorem B2525057 : Blo 1682041 2525057 := bstep (se 2 (by rfl) ⟨946896, by rfl⟩ : syracuseStep 2525057 = 1893793) B1893793
theorem B3786641 : Blo 1682041 3786641 := bstep (se 2 (by rfl) ⟨1419990, by rfl⟩ : syracuseStep 3786641 = 2839981) B2839981
theorem B3196817 : Blo 1682041 3196817 := bstep (se 2 (by rfl) ⟨1198806, by rfl⟩ : syracuseStep 3196817 = 2397613) B2397613
theorem B2525075 : Blo 1682041 2525075 := bstep (se 1 (by rfl) ⟨1893806, by rfl⟩ : syracuseStep 2525075 = 3787613) B3787613
theorem B3786659 : Blo 1682041 3786659 := bstep (se 1 (by rfl) ⟨2839994, by rfl⟩ : syracuseStep 3786659 = 5679989) B5679989
theorem B4925357 : Blo 1682041 4925357 := bstep (se 3 (by rfl) ⟨923504, by rfl⟩ : syracuseStep 4925357 = 1847009) B1847009
theorem B2525105 : Blo 1682041 2525105 := bstep (se 2 (by rfl) ⟨946914, by rfl⟩ : syracuseStep 2525105 = 1893829) B1893829
theorem B2525123 : Blo 1682041 2525123 := bstep (se 1 (by rfl) ⟨1893842, by rfl⟩ : syracuseStep 2525123 = 3787685) B3787685
theorem B2525153 : Blo 1682041 2525153 := bstep (se 2 (by rfl) ⟨946932, by rfl⟩ : syracuseStep 2525153 = 1893865) B1893865
theorem B4794349 : Blo 1682041 4794349 := bstep (se 3 (by rfl) ⟨898940, by rfl⟩ : syracuseStep 4794349 = 1797881) B1797881
theorem B2525171 : Blo 1682041 2525171 := bstep (se 1 (by rfl) ⟨1893878, by rfl⟩ : syracuseStep 2525171 = 3787757) B3787757
theorem B1894387 : Blo 1682041 1894387 := bstep (se 1 (by rfl) ⟨1420790, by rfl⟩ : syracuseStep 1894387 = 2841581) B2841581
theorem B16205837 : Blo 1682041 16205837 := bstep (se 3 (by rfl) ⟨3038594, by rfl⟩ : syracuseStep 16205837 = 6077189) B6077189
theorem B2525201 : Blo 1682041 2525201 := bstep (se 2 (by rfl) ⟨946950, by rfl⟩ : syracuseStep 2525201 = 1893901) B1893901
theorem B2525219 : Blo 1682041 2525219 := bstep (se 1 (by rfl) ⟨1893914, by rfl⟩ : syracuseStep 2525219 = 3787829) B3787829
theorem B32368693 : Blo 1682041 32368693 := bstep (se 5 (by rfl) ⟨1517282, by rfl⟩ : syracuseStep 32368693 = 3034565) B3034565
theorem B2525249 : Blo 1682041 2525249 := bstep (se 2 (by rfl) ⟨946968, by rfl⟩ : syracuseStep 2525249 = 1893937) B1893937
theorem B2525267 : Blo 1682041 2525267 := bstep (se 1 (by rfl) ⟨1893950, by rfl⟩ : syracuseStep 2525267 = 3787901) B3787901
theorem B2525297 : Blo 1682041 2525297 := bstep (se 2 (by rfl) ⟨946986, by rfl⟩ : syracuseStep 2525297 = 1893973) B1893973
theorem B2525315 : Blo 1682041 2525315 := bstep (se 1 (by rfl) ⟨1893986, by rfl⟩ : syracuseStep 2525315 = 3787973) B3787973
theorem B1894531 : Blo 1682041 1894531 := bstep (se 1 (by rfl) ⟨1420898, by rfl⟩ : syracuseStep 1894531 = 2841797) B2841797
theorem B2525345 : Blo 1682041 2525345 := bstep (se 2 (by rfl) ⟨947004, by rfl⟩ : syracuseStep 2525345 = 1894009) B1894009
theorem B3786929 : Blo 1682041 3786929 := bstep (se 2 (by rfl) ⟨1420098, by rfl⟩ : syracuseStep 3786929 = 2840197) B2840197
theorem B2525363 : Blo 1682041 2525363 := bstep (se 1 (by rfl) ⟨1894022, by rfl⟩ : syracuseStep 2525363 = 3788045) B3788045
theorem B3786947 : Blo 1682041 3786947 := bstep (se 1 (by rfl) ⟨2840210, by rfl⟩ : syracuseStep 3786947 = 5680421) B5680421
theorem B2525393 : Blo 1682041 2525393 := bstep (se 2 (by rfl) ⟨947022, by rfl⟩ : syracuseStep 2525393 = 1894045) B1894045
theorem B2525411 : Blo 1682041 2525411 := bstep (se 1 (by rfl) ⟨1894058, by rfl⟩ : syracuseStep 2525411 = 3788117) B3788117
theorem B2697443 : Blo 1682041 2697443 := bstep (se 1 (by rfl) ⟨2023082, by rfl⟩ : syracuseStep 2697443 = 4046165) B4046165
theorem B5679341 : Blo 1682041 5679341 := bstep (se 3 (by rfl) ⟨1064876, by rfl⟩ : syracuseStep 5679341 = 2129753) B2129753
theorem B4262129 : Blo 1682041 4262129 := bstep (se 2 (by rfl) ⟨1598298, by rfl⟩ : syracuseStep 4262129 = 3196597) B3196597
theorem B2525441 : Blo 1682041 2525441 := bstep (se 2 (by rfl) ⟨947040, by rfl⟩ : syracuseStep 2525441 = 1894081) B1894081
theorem B2525459 : Blo 1682041 2525459 := bstep (se 1 (by rfl) ⟨1894094, by rfl⟩ : syracuseStep 2525459 = 3788189) B3788189
theorem B5679395 : Blo 1682041 5679395 := bstep (se 1 (by rfl) ⟨4259546, by rfl⟩ : syracuseStep 5679395 = 8519093) B8519093
theorem B4262179 : Blo 1682041 4262179 := bstep (se 1 (by rfl) ⟨3196634, by rfl⟩ : syracuseStep 4262179 = 6393269) B6393269
theorem B6064433 : Blo 1682041 6064433 := bstep (se 2 (by rfl) ⟨2274162, by rfl⟩ : syracuseStep 6064433 = 4548325) B4548325
theorem B5187889 : Blo 1682041 5187889 := bstep (se 2 (by rfl) ⟨1945458, by rfl⟩ : syracuseStep 5187889 = 3890917) B3890917
theorem B2525489 : Blo 1682041 2525489 := bstep (se 2 (by rfl) ⟨947058, by rfl⟩ : syracuseStep 2525489 = 1894117) B1894117
theorem B2525507 : Blo 1682041 2525507 := bstep (se 1 (by rfl) ⟨1894130, by rfl⟩ : syracuseStep 2525507 = 3788261) B3788261
theorem B2525537 : Blo 1682041 2525537 := bstep (se 2 (by rfl) ⟨947076, by rfl⟩ : syracuseStep 2525537 = 1894153) B1894153
theorem B1796467 : Blo 1682041 1796467 := bstep (se 1 (by rfl) ⟨1347350, by rfl⟩ : syracuseStep 1796467 = 2694701) B2694701
theorem B2525555 : Blo 1682041 2525555 := bstep (se 1 (by rfl) ⟨1894166, by rfl⟩ : syracuseStep 2525555 = 3788333) B3788333
theorem B2525585 : Blo 1682041 2525585 := bstep (se 2 (by rfl) ⟨947094, by rfl⟩ : syracuseStep 2525585 = 1894189) B1894189
theorem B2525603 : Blo 1682041 2525603 := bstep (se 1 (by rfl) ⟨1894202, by rfl⟩ : syracuseStep 2525603 = 3788405) B3788405
theorem B4262321 : Blo 1682041 4262321 := bstep (se 2 (by rfl) ⟨1598370, by rfl⟩ : syracuseStep 4262321 = 3196741) B3196741
theorem B2877889 : Blo 1682041 2877889 := bstep (se 2 (by rfl) ⟨1079208, by rfl⟩ : syracuseStep 2877889 = 2158417) B2158417
theorem B5392835 : Blo 1682041 5392835 := bstep (se 1 (by rfl) ⟨4044626, by rfl⟩ : syracuseStep 5392835 = 8089253) B8089253
theorem B2525633 : Blo 1682041 2525633 := bstep (se 2 (by rfl) ⟨947112, by rfl⟩ : syracuseStep 2525633 = 1894225) B1894225
theorem B3787217 : Blo 1682041 3787217 := bstep (se 2 (by rfl) ⟨1420206, by rfl⟩ : syracuseStep 3787217 = 2840413) B2840413
theorem B2525651 : Blo 1682041 2525651 := bstep (se 1 (by rfl) ⟨1894238, by rfl⟩ : syracuseStep 2525651 = 3788477) B3788477
theorem B3787235 : Blo 1682041 3787235 := bstep (se 1 (by rfl) ⟨2840426, by rfl⟩ : syracuseStep 3787235 = 5680853) B5680853
theorem B12954097 : Blo 1682041 12954097 := bstep (se 2 (by rfl) ⟨4857786, by rfl⟩ : syracuseStep 12954097 = 9715573) B9715573
theorem B2525681 : Blo 1682041 2525681 := bstep (se 2 (by rfl) ⟨947130, by rfl⟩ : syracuseStep 2525681 = 1894261) B1894261
theorem B2525699 : Blo 1682041 2525699 := bstep (se 1 (by rfl) ⟨1894274, by rfl⟩ : syracuseStep 2525699 = 3788549) B3788549
theorem B2525729 : Blo 1682041 2525729 := bstep (se 2 (by rfl) ⟨947148, by rfl⟩ : syracuseStep 2525729 = 1894297) B1894297
theorem B5679665 : Blo 1682041 5679665 := bstep (se 2 (by rfl) ⟨2129874, by rfl⟩ : syracuseStep 5679665 = 4259749) B4259749
theorem B2525747 : Blo 1682041 2525747 := bstep (se 1 (by rfl) ⟨1894310, by rfl⟩ : syracuseStep 2525747 = 3788621) B3788621
theorem B3410513 : Blo 1682041 3410513 := bstep (se 2 (by rfl) ⟨1278942, by rfl⟩ : syracuseStep 3410513 = 2557885) B2557885
theorem B2525777 : Blo 1682041 2525777 := bstep (se 2 (by rfl) ⟨947166, by rfl⟩ : syracuseStep 2525777 = 1894333) B1894333
theorem B2525795 : Blo 1682041 2525795 := bstep (se 1 (by rfl) ⟨1894346, by rfl⟩ : syracuseStep 2525795 = 3788693) B3788693
theorem B2525825 : Blo 1682041 2525825 := bstep (se 2 (by rfl) ⟨947184, by rfl⟩ : syracuseStep 2525825 = 1894369) B1894369
theorem B1682051 : Blo 1682041 1682051 := bstep (se 1 (by rfl) ⟨1261538, by rfl⟩ : syracuseStep 1682051 = 2523077) B2523077
theorem B1682067 : Blo 1682041 1682067 := bstep (se 1 (by rfl) ⟨1261550, by rfl⟩ : syracuseStep 1682067 = 2523101) B2523101
theorem B2525843 : Blo 1682041 2525843 := bstep (se 1 (by rfl) ⟨1894382, by rfl⟩ : syracuseStep 2525843 = 3788765) B3788765
theorem B1682083 : Blo 1682041 1682083 := bstep (se 1 (by rfl) ⟨1261562, by rfl⟩ : syracuseStep 1682083 = 2523125) B2523125
theorem B2525873 : Blo 1682041 2525873 := bstep (se 2 (by rfl) ⟨947202, by rfl⟩ : syracuseStep 2525873 = 1894405) B1894405
theorem B1682099 : Blo 1682041 1682099 := bstep (se 1 (by rfl) ⟨1261574, by rfl⟩ : syracuseStep 1682099 = 2523149) B2523149
theorem B1682115 : Blo 1682041 1682115 := bstep (se 1 (by rfl) ⟨1261586, by rfl⟩ : syracuseStep 1682115 = 2523173) B2523173
theorem B3074755 : Blo 1682041 3074755 := bstep (se 1 (by rfl) ⟨2306066, by rfl⟩ : syracuseStep 3074755 = 4612133) B4612133
theorem B2525891 : Blo 1682041 2525891 := bstep (se 1 (by rfl) ⟨1894418, by rfl⟩ : syracuseStep 2525891 = 3788837) B3788837
theorem B1682131 : Blo 1682041 1682131 := bstep (se 1 (by rfl) ⟨1261598, by rfl⟩ : syracuseStep 1682131 = 2523197) B2523197
theorem B2525921 : Blo 1682041 2525921 := bstep (se 2 (by rfl) ⟨947220, by rfl⟩ : syracuseStep 2525921 = 1894441) B1894441
theorem B1682147 : Blo 1682041 1682147 := bstep (se 1 (by rfl) ⟨1261610, by rfl⟩ : syracuseStep 1682147 = 2523221) B2523221
theorem B3787505 : Blo 1682041 3787505 := bstep (se 2 (by rfl) ⟨1420314, by rfl⟩ : syracuseStep 3787505 = 2840629) B2840629
theorem B1682163 : Blo 1682041 1682163 := bstep (se 1 (by rfl) ⟨1261622, by rfl⟩ : syracuseStep 1682163 = 2523245) B2523245
theorem B2525939 : Blo 1682041 2525939 := bstep (se 1 (by rfl) ⟨1894454, by rfl⟩ : syracuseStep 2525939 = 3788909) B3788909
theorem B1682179 : Blo 1682041 1682179 := bstep (se 1 (by rfl) ⟨1261634, by rfl⟩ : syracuseStep 1682179 = 2523269) B2523269
theorem B3787523 : Blo 1682041 3787523 := bstep (se 1 (by rfl) ⟨2840642, by rfl⟩ : syracuseStep 3787523 = 5681285) B5681285
theorem B2525969 : Blo 1682041 2525969 := bstep (se 2 (by rfl) ⟨947238, by rfl⟩ : syracuseStep 2525969 = 1894477) B1894477
theorem B1682195 : Blo 1682041 1682195 := bstep (se 1 (by rfl) ⟨1261646, by rfl⟩ : syracuseStep 1682195 = 2523293) B2523293
theorem B1682211 : Blo 1682041 1682211 := bstep (se 1 (by rfl) ⟨1261658, by rfl⟩ : syracuseStep 1682211 = 2523317) B2523317
theorem B2525987 : Blo 1682041 2525987 := bstep (se 1 (by rfl) ⟨1894490, by rfl⟩ : syracuseStep 2525987 = 3788981) B3788981
theorem B1682227 : Blo 1682041 1682227 := bstep (se 1 (by rfl) ⟨1261670, by rfl⟩ : syracuseStep 1682227 = 2523341) B2523341
theorem B2526017 : Blo 1682041 2526017 := bstep (se 2 (by rfl) ⟨947256, by rfl⟩ : syracuseStep 2526017 = 1894513) B1894513
theorem B1682243 : Blo 1682041 1682243 := bstep (se 1 (by rfl) ⟨1261682, by rfl⟩ : syracuseStep 1682243 = 2523365) B2523365
theorem B10521413 : Blo 1682041 10521413 := bstep (se 4 (by rfl) ⟨986382, by rfl⟩ : syracuseStep 10521413 = 1972765) B1972765
theorem B5393233 : Blo 1682041 5393233 := bstep (se 2 (by rfl) ⟨2022462, by rfl⟩ : syracuseStep 5393233 = 4044925) B4044925
theorem B1682259 : Blo 1682041 1682259 := bstep (se 1 (by rfl) ⟨1261694, by rfl⟩ : syracuseStep 1682259 = 2523389) B2523389
theorem B1821523 : Blo 1682041 1821523 := bstep (se 1 (by rfl) ⟨1366142, by rfl⟩ : syracuseStep 1821523 = 2732285) B2732285
theorem B2526035 : Blo 1682041 2526035 := bstep (se 1 (by rfl) ⟨1894526, by rfl⟩ : syracuseStep 2526035 = 3789053) B3789053
theorem B4041571 : Blo 1682041 4041571 := bstep (se 1 (by rfl) ⟨3031178, by rfl⟩ : syracuseStep 4041571 = 6062357) B6062357
theorem B1682275 : Blo 1682041 1682275 := bstep (se 1 (by rfl) ⟨1261706, by rfl⟩ : syracuseStep 1682275 = 2523413) B2523413
theorem B1682291 : Blo 1682041 1682291 := bstep (se 1 (by rfl) ⟨1261718, by rfl⟩ : syracuseStep 1682291 = 2523437) B2523437
theorem B1682307 : Blo 1682041 1682307 := bstep (se 1 (by rfl) ⟨1261730, by rfl⟩ : syracuseStep 1682307 = 2523461) B2523461
theorem B5393297 : Blo 1682041 5393297 := bstep (se 2 (by rfl) ⟨2022486, by rfl⟩ : syracuseStep 5393297 = 4044973) B4044973
theorem B1682323 : Blo 1682041 1682323 := bstep (se 1 (by rfl) ⟨1261742, by rfl⟩ : syracuseStep 1682323 = 2523485) B2523485
theorem B1682339 : Blo 1682041 1682339 := bstep (se 1 (by rfl) ⟨1261754, by rfl⟩ : syracuseStep 1682339 = 2523509) B2523509
theorem B3034019 : Blo 1682041 3034019 := bstep (se 1 (by rfl) ⟨2275514, by rfl⟩ : syracuseStep 3034019 = 4551029) B4551029
theorem B6392753 : Blo 1682041 6392753 := bstep (se 2 (by rfl) ⟨2397282, by rfl⟩ : syracuseStep 6392753 = 4794565) B4794565
theorem B1682355 : Blo 1682041 1682355 := bstep (se 1 (by rfl) ⟨1261766, by rfl⟩ : syracuseStep 1682355 = 2523533) B2523533
theorem B4041667 : Blo 1682041 4041667 := bstep (se 1 (by rfl) ⟨3031250, by rfl⟩ : syracuseStep 4041667 = 6062501) B6062501
theorem B1682371 : Blo 1682041 1682371 := bstep (se 1 (by rfl) ⟨1261778, by rfl⟩ : syracuseStep 1682371 = 2523557) B2523557
theorem B21556165 : Blo 1682041 21556165 := bstep (se 4 (by rfl) ⟨2020890, by rfl⟩ : syracuseStep 21556165 = 4041781) B4041781
theorem B1682387 : Blo 1682041 1682387 := bstep (se 1 (by rfl) ⟨1261790, by rfl⟩ : syracuseStep 1682387 = 2523581) B2523581
theorem B1682403 : Blo 1682041 1682403 := bstep (se 1 (by rfl) ⟨1261802, by rfl⟩ : syracuseStep 1682403 = 2523605) B2523605
theorem B1682419 : Blo 1682041 1682419 := bstep (se 1 (by rfl) ⟨1261814, by rfl⟩ : syracuseStep 1682419 = 2523629) B2523629
theorem B1682435 : Blo 1682041 1682435 := bstep (se 1 (by rfl) ⟨1261826, by rfl⟩ : syracuseStep 1682435 = 2523653) B2523653
theorem B9587717 : Blo 1682041 9587717 := bstep (se 4 (by rfl) ⟨898848, by rfl⟩ : syracuseStep 9587717 = 1797697) B1797697
theorem B3787793 : Blo 1682041 3787793 := bstep (se 2 (by rfl) ⟨1420422, by rfl⟩ : syracuseStep 3787793 = 2840845) B2840845
theorem B1682451 : Blo 1682041 1682451 := bstep (se 1 (by rfl) ⟨1261838, by rfl⟩ : syracuseStep 1682451 = 2523677) B2523677
theorem B1682467 : Blo 1682041 1682467 := bstep (se 1 (by rfl) ⟨1261850, by rfl⟩ : syracuseStep 1682467 = 2523701) B2523701
theorem B3787811 : Blo 1682041 3787811 := bstep (se 1 (by rfl) ⟨2840858, by rfl⟩ : syracuseStep 3787811 = 5681717) B5681717
theorem B1682483 : Blo 1682041 1682483 := bstep (se 1 (by rfl) ⟨1261862, by rfl⟩ : syracuseStep 1682483 = 2523725) B2523725
theorem B1682499 : Blo 1682041 1682499 := bstep (se 1 (by rfl) ⟨1261874, by rfl⟩ : syracuseStep 1682499 = 2523749) B2523749
theorem B5680205 : Blo 1682041 5680205 := bstep (se 3 (by rfl) ⟨1065038, by rfl⟩ : syracuseStep 5680205 = 2130077) B2130077
theorem B4549709 : Blo 1682041 4549709 := bstep (se 3 (by rfl) ⟨853070, by rfl⟩ : syracuseStep 4549709 = 1706141) B1706141
theorem B4926545 : Blo 1682041 4926545 := bstep (se 2 (by rfl) ⟨1847454, by rfl⟩ : syracuseStep 4926545 = 3694909) B3694909
theorem B1682515 : Blo 1682041 1682515 := bstep (se 1 (by rfl) ⟨1261886, by rfl⟩ : syracuseStep 1682515 = 2523773) B2523773
theorem B1682531 : Blo 1682041 1682531 := bstep (se 1 (by rfl) ⟨1261898, by rfl⟩ : syracuseStep 1682531 = 2523797) B2523797
theorem B1682547 : Blo 1682041 1682547 := bstep (se 1 (by rfl) ⟨1261910, by rfl⟩ : syracuseStep 1682547 = 2523821) B2523821
theorem B4041859 : Blo 1682041 4041859 := bstep (se 1 (by rfl) ⟨3031394, by rfl⟩ : syracuseStep 4041859 = 6062789) B6062789
theorem B1682563 : Blo 1682041 1682563 := bstep (se 1 (by rfl) ⟨1261922, by rfl⟩ : syracuseStep 1682563 = 2523845) B2523845
theorem B5680259 : Blo 1682041 5680259 := bstep (se 1 (by rfl) ⟨4260194, by rfl⟩ : syracuseStep 5680259 = 8520389) B8520389
theorem B1682579 : Blo 1682041 1682579 := bstep (se 1 (by rfl) ⟨1261934, by rfl⟩ : syracuseStep 1682579 = 2523869) B2523869
theorem B1682595 : Blo 1682041 1682595 := bstep (se 1 (by rfl) ⟨1261946, by rfl⟩ : syracuseStep 1682595 = 2523893) B2523893
theorem B1682611 : Blo 1682041 1682611 := bstep (se 1 (by rfl) ⟨1261958, by rfl⟩ : syracuseStep 1682611 = 2523917) B2523917
theorem B1682627 : Blo 1682041 1682627 := bstep (se 1 (by rfl) ⟨1261970, by rfl⟩ : syracuseStep 1682627 = 2523941) B2523941
theorem B5115089 : Blo 1682041 5115089 := bstep (se 2 (by rfl) ⟨1918158, by rfl⟩ : syracuseStep 5115089 = 3836317) B3836317
theorem B1682643 : Blo 1682041 1682643 := bstep (se 1 (by rfl) ⟨1261982, by rfl⟩ : syracuseStep 1682643 = 2523965) B2523965
theorem B1682659 : Blo 1682041 1682659 := bstep (se 1 (by rfl) ⟨1261994, by rfl⟩ : syracuseStep 1682659 = 2523989) B2523989
theorem B1797347 : Blo 1682041 1797347 := bstep (se 1 (by rfl) ⟨1348010, by rfl⟩ : syracuseStep 1797347 = 2696021) B2696021
theorem B1682675 : Blo 1682041 1682675 := bstep (se 1 (by rfl) ⟨1262006, by rfl⟩ : syracuseStep 1682675 = 2524013) B2524013
theorem B1682691 : Blo 1682041 1682691 := bstep (se 1 (by rfl) ⟨1262018, by rfl⟩ : syracuseStep 1682691 = 2524037) B2524037
theorem B1682707 : Blo 1682041 1682707 := bstep (se 1 (by rfl) ⟨1262030, by rfl⟩ : syracuseStep 1682707 = 2524061) B2524061
theorem B1682723 : Blo 1682041 1682723 := bstep (se 1 (by rfl) ⟨1262042, by rfl⟩ : syracuseStep 1682723 = 2524085) B2524085
theorem B3788081 : Blo 1682041 3788081 := bstep (se 2 (by rfl) ⟨1420530, by rfl⟩ : syracuseStep 3788081 = 2841061) B2841061
theorem B1682739 : Blo 1682041 1682739 := bstep (se 1 (by rfl) ⟨1262054, by rfl⟩ : syracuseStep 1682739 = 2524109) B2524109
theorem B1682755 : Blo 1682041 1682755 := bstep (se 1 (by rfl) ⟨1262066, by rfl⟩ : syracuseStep 1682755 = 2524133) B2524133
theorem B1846595 : Blo 1682041 1846595 := bstep (se 1 (by rfl) ⟨1384946, by rfl⟩ : syracuseStep 1846595 = 2769893) B2769893
theorem B3788099 : Blo 1682041 3788099 := bstep (se 1 (by rfl) ⟨2841074, by rfl⟩ : syracuseStep 3788099 = 5682149) B5682149
theorem B1682771 : Blo 1682041 1682771 := bstep (se 1 (by rfl) ⟨1262078, by rfl⟩ : syracuseStep 1682771 = 2524157) B2524157
theorem B2395489 : Blo 1682041 2395489 := bstep (se 2 (by rfl) ⟨898308, by rfl⟩ : syracuseStep 2395489 = 1796617) B1796617
theorem B1682787 : Blo 1682041 1682787 := bstep (se 1 (by rfl) ⟨1262090, by rfl⟩ : syracuseStep 1682787 = 2524181) B2524181
theorem B1797475 : Blo 1682041 1797475 := bstep (se 1 (by rfl) ⟨1348106, by rfl⟩ : syracuseStep 1797475 = 2696213) B2696213
theorem B1682803 : Blo 1682041 1682803 := bstep (se 1 (by rfl) ⟨1262102, by rfl⟩ : syracuseStep 1682803 = 2524205) B2524205
theorem B1682819 : Blo 1682041 1682819 := bstep (se 1 (by rfl) ⟨1262114, by rfl⟩ : syracuseStep 1682819 = 2524229) B2524229
theorem B5680529 : Blo 1682041 5680529 := bstep (se 2 (by rfl) ⟨2130198, by rfl⟩ : syracuseStep 5680529 = 4260397) B4260397
theorem B1682835 : Blo 1682041 1682835 := bstep (se 1 (by rfl) ⟨1262126, by rfl⟩ : syracuseStep 1682835 = 2524253) B2524253
theorem B1682851 : Blo 1682041 1682851 := bstep (se 1 (by rfl) ⟨1262138, by rfl⟩ : syracuseStep 1682851 = 2524277) B2524277
theorem B1682867 : Blo 1682041 1682867 := bstep (se 1 (by rfl) ⟨1262150, by rfl⟩ : syracuseStep 1682867 = 2524301) B2524301
theorem B2395585 : Blo 1682041 2395585 := bstep (se 2 (by rfl) ⟨898344, by rfl⟩ : syracuseStep 2395585 = 1796689) B1796689
theorem B1682883 : Blo 1682041 1682883 := bstep (se 1 (by rfl) ⟨1262162, by rfl⟩ : syracuseStep 1682883 = 2524325) B2524325
theorem B1682899 : Blo 1682041 1682899 := bstep (se 1 (by rfl) ⟨1262174, by rfl⟩ : syracuseStep 1682899 = 2524349) B2524349
theorem B1682915 : Blo 1682041 1682915 := bstep (se 1 (by rfl) ⟨1262186, by rfl⟩ : syracuseStep 1682915 = 2524373) B2524373
theorem B2428403 : Blo 1682041 2428403 := bstep (se 1 (by rfl) ⟨1821302, by rfl⟩ : syracuseStep 2428403 = 3642605) B3642605
theorem B1682931 : Blo 1682041 1682931 := bstep (se 1 (by rfl) ⟨1262198, by rfl⟩ : syracuseStep 1682931 = 2524397) B2524397
theorem B1682947 : Blo 1682041 1682947 := bstep (se 1 (by rfl) ⟨1262210, by rfl⟩ : syracuseStep 1682947 = 2524421) B2524421
theorem B1682963 : Blo 1682041 1682963 := bstep (se 1 (by rfl) ⟨1262222, by rfl⟩ : syracuseStep 1682963 = 2524445) B2524445
theorem B1682979 : Blo 1682041 1682979 := bstep (se 1 (by rfl) ⟨1262234, by rfl⟩ : syracuseStep 1682979 = 2524469) B2524469
theorem B1682995 : Blo 1682041 1682995 := bstep (se 1 (by rfl) ⟨1262246, by rfl⟩ : syracuseStep 1682995 = 2524493) B2524493
theorem B1683011 : Blo 1682041 1683011 := bstep (se 1 (by rfl) ⟨1262258, by rfl⟩ : syracuseStep 1683011 = 2524517) B2524517
theorem B3788369 : Blo 1682041 3788369 := bstep (se 2 (by rfl) ⟨1420638, by rfl⟩ : syracuseStep 3788369 = 2841277) B2841277
theorem B1683027 : Blo 1682041 1683027 := bstep (se 1 (by rfl) ⟨1262270, by rfl⟩ : syracuseStep 1683027 = 2524541) B2524541
theorem B1683043 : Blo 1682041 1683043 := bstep (se 1 (by rfl) ⟨1262282, by rfl⟩ : syracuseStep 1683043 = 2524565) B2524565
theorem B3788387 : Blo 1682041 3788387 := bstep (se 1 (by rfl) ⟨2841290, by rfl⟩ : syracuseStep 3788387 = 5682581) B5682581
theorem B1683059 : Blo 1682041 1683059 := bstep (se 1 (by rfl) ⟨1262294, by rfl⟩ : syracuseStep 1683059 = 2524589) B2524589
theorem B1683075 : Blo 1682041 1683075 := bstep (se 1 (by rfl) ⟨1262306, by rfl⟩ : syracuseStep 1683075 = 2524613) B2524613
theorem B1683091 : Blo 1682041 1683091 := bstep (se 1 (by rfl) ⟨1262318, by rfl⟩ : syracuseStep 1683091 = 2524637) B2524637
theorem B1683107 : Blo 1682041 1683107 := bstep (se 1 (by rfl) ⟨1262330, by rfl⟩ : syracuseStep 1683107 = 2524661) B2524661
theorem B2879153 : Blo 1682041 2879153 := bstep (se 2 (by rfl) ⟨1079682, by rfl⟩ : syracuseStep 2879153 = 2159365) B2159365
theorem B9588401 : Blo 1682041 9588401 := bstep (se 2 (by rfl) ⟨3595650, by rfl⟩ : syracuseStep 9588401 = 7191301) B7191301
theorem B2731699 : Blo 1682041 2731699 := bstep (se 1 (by rfl) ⟨2048774, by rfl⟩ : syracuseStep 2731699 = 4097549) B4097549
theorem B1683123 : Blo 1682041 1683123 := bstep (se 1 (by rfl) ⟨1262342, by rfl⟩ : syracuseStep 1683123 = 2524685) B2524685
theorem B1683139 : Blo 1682041 1683139 := bstep (se 1 (by rfl) ⟨1262354, by rfl⟩ : syracuseStep 1683139 = 2524709) B2524709
theorem B1683155 : Blo 1682041 1683155 := bstep (se 1 (by rfl) ⟨1262366, by rfl⟩ : syracuseStep 1683155 = 2524733) B2524733
theorem B1683171 : Blo 1682041 1683171 := bstep (se 1 (by rfl) ⟨1262378, by rfl⟩ : syracuseStep 1683171 = 2524757) B2524757
theorem B1683187 : Blo 1682041 1683187 := bstep (se 1 (by rfl) ⟨1262390, by rfl⟩ : syracuseStep 1683187 = 2524781) B2524781
theorem B3411715 : Blo 1682041 3411715 := bstep (se 1 (by rfl) ⟨2558786, by rfl⟩ : syracuseStep 3411715 = 5117573) B5117573
theorem B1683203 : Blo 1682041 1683203 := bstep (se 1 (by rfl) ⟨1262402, by rfl⟩ : syracuseStep 1683203 = 2524805) B2524805
theorem B1683219 : Blo 1682041 1683219 := bstep (se 1 (by rfl) ⟨1262414, by rfl⟩ : syracuseStep 1683219 = 2524829) B2524829
theorem B7188259 : Blo 1682041 7188259 := bstep (se 1 (by rfl) ⟨5391194, by rfl⟩ : syracuseStep 7188259 = 10782389) B10782389
theorem B1683235 : Blo 1682041 1683235 := bstep (se 1 (by rfl) ⟨1262426, by rfl⟩ : syracuseStep 1683235 = 2524853) B2524853
theorem B4099889 : Blo 1682041 4099889 := bstep (se 2 (by rfl) ⟨1537458, by rfl⟩ : syracuseStep 4099889 = 3074917) B3074917
theorem B1683251 : Blo 1682041 1683251 := bstep (se 1 (by rfl) ⟨1262438, by rfl⟩ : syracuseStep 1683251 = 2524877) B2524877
theorem B1683267 : Blo 1682041 1683267 := bstep (se 1 (by rfl) ⟨1262450, by rfl⟩ : syracuseStep 1683267 = 2524901) B2524901
theorem B1683283 : Blo 1682041 1683283 := bstep (se 1 (by rfl) ⟨1262462, by rfl⟩ : syracuseStep 1683283 = 2524925) B2524925
theorem B1683299 : Blo 1682041 1683299 := bstep (se 1 (by rfl) ⟨1262474, by rfl⟩ : syracuseStep 1683299 = 2524949) B2524949
theorem B3788657 : Blo 1682041 3788657 := bstep (se 2 (by rfl) ⟨1420746, by rfl⟩ : syracuseStep 3788657 = 2841493) B2841493
theorem B1683315 : Blo 1682041 1683315 := bstep (se 1 (by rfl) ⟨1262486, by rfl⟩ : syracuseStep 1683315 = 2524973) B2524973
theorem B1683331 : Blo 1682041 1683331 := bstep (se 1 (by rfl) ⟨1262498, by rfl⟩ : syracuseStep 1683331 = 2524997) B2524997
theorem B3788675 : Blo 1682041 3788675 := bstep (se 1 (by rfl) ⟨2841506, by rfl⟩ : syracuseStep 3788675 = 5683013) B5683013
theorem B1683347 : Blo 1682041 1683347 := bstep (se 1 (by rfl) ⟨1262510, by rfl⟩ : syracuseStep 1683347 = 2525021) B2525021
theorem B2158499 : Blo 1682041 2158499 := bstep (se 1 (by rfl) ⟨1618874, by rfl⟩ : syracuseStep 2158499 = 3237749) B3237749
theorem B9097123 : Blo 1682041 9097123 := bstep (se 1 (by rfl) ⟨6822842, by rfl⟩ : syracuseStep 9097123 = 13645685) B13645685
theorem B1683363 : Blo 1682041 1683363 := bstep (se 1 (by rfl) ⟨1262522, by rfl⟩ : syracuseStep 1683363 = 2525045) B2525045
theorem B5681069 : Blo 1682041 5681069 := bstep (se 3 (by rfl) ⟨1065200, by rfl⟩ : syracuseStep 5681069 = 2130401) B2130401
theorem B2838449 : Blo 1682041 2838449 := bstep (se 2 (by rfl) ⟨1064418, by rfl⟩ : syracuseStep 2838449 = 2128837) B2128837
theorem B2396081 : Blo 1682041 2396081 := bstep (se 2 (by rfl) ⟨898530, by rfl⟩ : syracuseStep 2396081 = 1797061) B1797061
theorem B1683379 : Blo 1682041 1683379 := bstep (se 1 (by rfl) ⟨1262534, by rfl⟩ : syracuseStep 1683379 = 2525069) B2525069
theorem B1683395 : Blo 1682041 1683395 := bstep (se 1 (by rfl) ⟨1262546, by rfl⟩ : syracuseStep 1683395 = 2525093) B2525093
theorem B1683411 : Blo 1682041 1683411 := bstep (se 1 (by rfl) ⟨1262558, by rfl⟩ : syracuseStep 1683411 = 2525117) B2525117
theorem B39374819 : Blo 1682041 39374819 := bstep (se 1 (by rfl) ⟨29531114, by rfl⟩ : syracuseStep 39374819 = 59062229) B59062229
theorem B5681123 : Blo 1682041 5681123 := bstep (se 1 (by rfl) ⟨4260842, by rfl⟩ : syracuseStep 5681123 = 8521685) B8521685
theorem B1683427 : Blo 1682041 1683427 := bstep (se 1 (by rfl) ⟨1262570, by rfl⟩ : syracuseStep 1683427 = 2525141) B2525141
theorem B16166897 : Blo 1682041 16166897 := bstep (se 2 (by rfl) ⟨6062586, by rfl⟩ : syracuseStep 16166897 = 12125173) B12125173
theorem B1683443 : Blo 1682041 1683443 := bstep (se 1 (by rfl) ⟨1262582, by rfl⟩ : syracuseStep 1683443 = 2525165) B2525165
theorem B1683459 : Blo 1682041 1683459 := bstep (se 1 (by rfl) ⟨1262594, by rfl⟩ : syracuseStep 1683459 = 2525189) B2525189
theorem B1683475 : Blo 1682041 1683475 := bstep (se 1 (by rfl) ⟨1262606, by rfl⟩ : syracuseStep 1683475 = 2525213) B2525213
theorem B1683491 : Blo 1682041 1683491 := bstep (se 1 (by rfl) ⟨1262618, by rfl⟩ : syracuseStep 1683491 = 2525237) B2525237
theorem B2273329 : Blo 1682041 2273329 := bstep (se 2 (by rfl) ⟨852498, by rfl⟩ : syracuseStep 2273329 = 1704997) B1704997
theorem B2838577 : Blo 1682041 2838577 := bstep (se 2 (by rfl) ⟨1064466, by rfl⟩ : syracuseStep 2838577 = 2128933) B2128933
theorem B4042801 : Blo 1682041 4042801 := bstep (se 2 (by rfl) ⟨1516050, by rfl⟩ : syracuseStep 4042801 = 3032101) B3032101
theorem B1683507 : Blo 1682041 1683507 := bstep (se 1 (by rfl) ⟨1262630, by rfl⟩ : syracuseStep 1683507 = 2525261) B2525261
theorem B1822771 : Blo 1682041 1822771 := bstep (se 1 (by rfl) ⟨1367078, by rfl⟩ : syracuseStep 1822771 = 2734157) B2734157
theorem B1683523 : Blo 1682041 1683523 := bstep (se 1 (by rfl) ⟨1262642, by rfl⟩ : syracuseStep 1683523 = 2525285) B2525285
theorem B2838611 : Blo 1682041 2838611 := bstep (se 1 (by rfl) ⟨2128958, by rfl⟩ : syracuseStep 2838611 = 4257917) B4257917
theorem B1683539 : Blo 1682041 1683539 := bstep (se 1 (by rfl) ⟨1262654, by rfl⟩ : syracuseStep 1683539 = 2525309) B2525309
theorem B1683555 : Blo 1682041 1683555 := bstep (se 1 (by rfl) ⟨1262666, by rfl⟩ : syracuseStep 1683555 = 2525333) B2525333
theorem B1683571 : Blo 1682041 1683571 := bstep (se 1 (by rfl) ⟨1262678, by rfl⟩ : syracuseStep 1683571 = 2525357) B2525357
theorem B1683587 : Blo 1682041 1683587 := bstep (se 1 (by rfl) ⟨1262690, by rfl⟩ : syracuseStep 1683587 = 2525381) B2525381
theorem B3788945 : Blo 1682041 3788945 := bstep (se 2 (by rfl) ⟨1420854, by rfl⟩ : syracuseStep 3788945 = 2841709) B2841709
theorem B1683603 : Blo 1682041 1683603 := bstep (se 1 (by rfl) ⟨1262702, by rfl⟩ : syracuseStep 1683603 = 2525405) B2525405
theorem B1798291 : Blo 1682041 1798291 := bstep (se 1 (by rfl) ⟨1348718, by rfl⟩ : syracuseStep 1798291 = 2697437) B2697437
theorem B1683619 : Blo 1682041 1683619 := bstep (se 1 (by rfl) ⟨1262714, by rfl⟩ : syracuseStep 1683619 = 2525429) B2525429
theorem B3788963 : Blo 1682041 3788963 := bstep (se 1 (by rfl) ⟨2841722, by rfl⟩ : syracuseStep 3788963 = 5683445) B5683445
theorem B8523953 : Blo 1682041 8523953 := bstep (se 2 (by rfl) ⟨3196482, by rfl⟩ : syracuseStep 8523953 = 6392965) B6392965
theorem B1683635 : Blo 1682041 1683635 := bstep (se 1 (by rfl) ⟨1262726, by rfl⟩ : syracuseStep 1683635 = 2525453) B2525453
theorem B1683651 : Blo 1682041 1683651 := bstep (se 1 (by rfl) ⟨1262738, by rfl⟩ : syracuseStep 1683651 = 2525477) B2525477
theorem B2838739 : Blo 1682041 2838739 := bstep (se 1 (by rfl) ⟨2129054, by rfl⟩ : syracuseStep 2838739 = 4258109) B4258109
theorem B1683667 : Blo 1682041 1683667 := bstep (se 1 (by rfl) ⟨1262750, by rfl⟩ : syracuseStep 1683667 = 2525501) B2525501
theorem B1683683 : Blo 1682041 1683683 := bstep (se 1 (by rfl) ⟨1262762, by rfl⟩ : syracuseStep 1683683 = 2525525) B2525525
theorem B5681393 : Blo 1682041 5681393 := bstep (se 2 (by rfl) ⟨2130522, by rfl⟩ : syracuseStep 5681393 = 4261045) B4261045
theorem B1683699 : Blo 1682041 1683699 := bstep (se 1 (by rfl) ⟨1262774, by rfl⟩ : syracuseStep 1683699 = 2525549) B2525549
theorem B1683715 : Blo 1682041 1683715 := bstep (se 1 (by rfl) ⟨1262786, by rfl⟩ : syracuseStep 1683715 = 2525573) B2525573
theorem B8515853 : Blo 1682041 8515853 := bstep (se 3 (by rfl) ⟨1596722, by rfl⟩ : syracuseStep 8515853 = 3193445) B3193445
theorem B1683731 : Blo 1682041 1683731 := bstep (se 1 (by rfl) ⟨1262798, by rfl⟩ : syracuseStep 1683731 = 2525597) B2525597
theorem B1683747 : Blo 1682041 1683747 := bstep (se 1 (by rfl) ⟨1262810, by rfl⟩ : syracuseStep 1683747 = 2525621) B2525621
theorem B1683763 : Blo 1682041 1683763 := bstep (se 1 (by rfl) ⟨1262822, by rfl⟩ : syracuseStep 1683763 = 2525645) B2525645
theorem B1683779 : Blo 1682041 1683779 := bstep (se 1 (by rfl) ⟨1262834, by rfl⟩ : syracuseStep 1683779 = 2525669) B2525669
theorem B1683795 : Blo 1682041 1683795 := bstep (se 1 (by rfl) ⟨1262846, by rfl⟩ : syracuseStep 1683795 = 2525693) B2525693
theorem B2838881 : Blo 1682041 2838881 := bstep (se 2 (by rfl) ⟨1064580, by rfl⟩ : syracuseStep 2838881 = 2129161) B2129161
theorem B1683811 : Blo 1682041 1683811 := bstep (se 1 (by rfl) ⟨1262858, by rfl⟩ : syracuseStep 1683811 = 2525717) B2525717
theorem B1683827 : Blo 1682041 1683827 := bstep (se 1 (by rfl) ⟨1262870, by rfl⟩ : syracuseStep 1683827 = 2525741) B2525741
theorem B1683843 : Blo 1682041 1683843 := bstep (se 1 (by rfl) ⟨1262882, by rfl⟩ : syracuseStep 1683843 = 2525765) B2525765
theorem B1683859 : Blo 1682041 1683859 := bstep (se 1 (by rfl) ⟨1262894, by rfl⟩ : syracuseStep 1683859 = 2525789) B2525789
theorem B1683875 : Blo 1682041 1683875 := bstep (se 1 (by rfl) ⟨1262906, by rfl⟩ : syracuseStep 1683875 = 2525813) B2525813
theorem B2879921 : Blo 1682041 2879921 := bstep (se 2 (by rfl) ⟨1079970, by rfl⟩ : syracuseStep 2879921 = 2159941) B2159941
theorem B1683891 : Blo 1682041 1683891 := bstep (se 1 (by rfl) ⟨1262918, by rfl⟩ : syracuseStep 1683891 = 2525837) B2525837
theorem B1683907 : Blo 1682041 1683907 := bstep (se 1 (by rfl) ⟨1262930, by rfl⟩ : syracuseStep 1683907 = 2525861) B2525861
theorem B1683923 : Blo 1682041 1683923 := bstep (se 1 (by rfl) ⟨1262942, by rfl⟩ : syracuseStep 1683923 = 2525885) B2525885
theorem B2839009 : Blo 1682041 2839009 := bstep (se 2 (by rfl) ⟨1064628, by rfl⟩ : syracuseStep 2839009 = 2129257) B2129257
theorem B1683939 : Blo 1682041 1683939 := bstep (se 1 (by rfl) ⟨1262954, by rfl⟩ : syracuseStep 1683939 = 2525909) B2525909
theorem B1683955 : Blo 1682041 1683955 := bstep (se 1 (by rfl) ⟨1262966, by rfl⟩ : syracuseStep 1683955 = 2525933) B2525933
theorem B2839043 : Blo 1682041 2839043 := bstep (se 1 (by rfl) ⟨2129282, by rfl⟩ : syracuseStep 2839043 = 4258565) B4258565
theorem B1683971 : Blo 1682041 1683971 := bstep (se 1 (by rfl) ⟨1262978, by rfl⟩ : syracuseStep 1683971 = 2525957) B2525957
theorem B1683987 : Blo 1682041 1683987 := bstep (se 1 (by rfl) ⟨1262990, by rfl⟩ : syracuseStep 1683987 = 2525981) B2525981
theorem B2273827 : Blo 1682041 2273827 := bstep (se 1 (by rfl) ⟨1705370, by rfl⟩ : syracuseStep 2273827 = 3410741) B3410741
theorem B1684003 : Blo 1682041 1684003 := bstep (se 1 (by rfl) ⟨1263002, by rfl⟩ : syracuseStep 1684003 = 2526005) B2526005
theorem B1684019 : Blo 1682041 1684019 := bstep (se 1 (by rfl) ⟨1263014, by rfl⟩ : syracuseStep 1684019 = 2526029) B2526029
theorem B1684035 : Blo 1682041 1684035 := bstep (se 1 (by rfl) ⟨1263026, by rfl⟩ : syracuseStep 1684035 = 2526053) B2526053
theorem B2839171 : Blo 1682041 2839171 := bstep (se 1 (by rfl) ⟨2129378, by rfl⟩ : syracuseStep 2839171 = 4258757) B4258757
theorem B3592849 : Blo 1682041 3592849 := bstep (se 2 (by rfl) ⟨1347318, by rfl⟩ : syracuseStep 3592849 = 2694637) B2694637
theorem B19174157 : Blo 1682041 19174157 := bstep (se 3 (by rfl) ⟨3595154, by rfl⟩ : syracuseStep 19174157 = 7190309) B7190309
theorem B5681933 : Blo 1682041 5681933 := bstep (se 3 (by rfl) ⟨1065362, by rfl⟩ : syracuseStep 5681933 = 2130725) B2130725
theorem B2839313 : Blo 1682041 2839313 := bstep (se 2 (by rfl) ⟨1064742, by rfl⟩ : syracuseStep 2839313 = 2129485) B2129485
theorem B2396947 : Blo 1682041 2396947 := bstep (se 1 (by rfl) ⟨1797710, by rfl⟩ : syracuseStep 2396947 = 3595421) B3595421
theorem B5681987 : Blo 1682041 5681987 := bstep (se 1 (by rfl) ⟨4261490, by rfl⟩ : syracuseStep 5681987 = 8522981) B8522981
theorem B2397043 : Blo 1682041 2397043 := bstep (se 1 (by rfl) ⟨1797782, by rfl⟩ : syracuseStep 2397043 = 3595565) B3595565
theorem B5755789 : Blo 1682041 5755789 := bstep (se 3 (by rfl) ⟨1079210, by rfl⟩ : syracuseStep 5755789 = 2158421) B2158421
theorem B2839441 : Blo 1682041 2839441 := bstep (se 2 (by rfl) ⟨1064790, by rfl⟩ : syracuseStep 2839441 = 2129581) B2129581
theorem B2839475 : Blo 1682041 2839475 := bstep (se 1 (by rfl) ⟨2129606, by rfl⟩ : syracuseStep 2839475 = 4259213) B4259213
theorem B7189489 : Blo 1682041 7189489 := bstep (se 2 (by rfl) ⟨2696058, by rfl⟩ : syracuseStep 7189489 = 5392117) B5392117
theorem B2839603 : Blo 1682041 2839603 := bstep (se 1 (by rfl) ⟨2129702, by rfl⟩ : syracuseStep 2839603 = 4259405) B4259405
theorem B5682257 : Blo 1682041 5682257 := bstep (se 2 (by rfl) ⟨2130846, by rfl⟩ : syracuseStep 5682257 = 4261693) B4261693
theorem B9589859 : Blo 1682041 9589859 := bstep (se 1 (by rfl) ⟨7192394, by rfl⟩ : syracuseStep 9589859 = 14384789) B14384789
theorem B2839745 : Blo 1682041 2839745 := bstep (se 2 (by rfl) ⟨1064904, by rfl⟩ : syracuseStep 2839745 = 2129809) B2129809
theorem B2594017 : Blo 1682041 2594017 := bstep (se 2 (by rfl) ⟨972756, by rfl⟩ : syracuseStep 2594017 = 1945513) B1945513
theorem B61412579 : Blo 1682041 61412579 := bstep (se 1 (by rfl) ⟨46059434, by rfl⟩ : syracuseStep 61412579 = 92118869) B92118869
theorem B2839873 : Blo 1682041 2839873 := bstep (se 2 (by rfl) ⟨1064952, by rfl⟩ : syracuseStep 2839873 = 2129905) B2129905
theorem B2839907 : Blo 1682041 2839907 := bstep (se 1 (by rfl) ⟨2129930, by rfl⟩ : syracuseStep 2839907 = 4259861) B4259861
theorem B2397539 : Blo 1682041 2397539 := bstep (se 1 (by rfl) ⟨1798154, by rfl⟩ : syracuseStep 2397539 = 3596309) B3596309
theorem B7673201 : Blo 1682041 7673201 := bstep (se 2 (by rfl) ⟨2877450, by rfl⟩ : syracuseStep 7673201 = 5754901) B5754901
theorem B2020771 : Blo 1682041 2020771 := bstep (se 1 (by rfl) ⟨1515578, by rfl⟩ : syracuseStep 2020771 = 3031157) B3031157
theorem B6067619 : Blo 1682041 6067619 := bstep (se 1 (by rfl) ⟨4550714, by rfl⟩ : syracuseStep 6067619 = 9101429) B9101429
theorem B2840035 : Blo 1682041 2840035 := bstep (se 1 (by rfl) ⟨2130026, by rfl⟩ : syracuseStep 2840035 = 4260053) B4260053
theorem B28767797 : Blo 1682041 28767797 := bstep (se 5 (by rfl) ⟨1348490, by rfl⟩ : syracuseStep 28767797 = 2696981) B2696981
theorem B5117521 : Blo 1682041 5117521 := bstep (se 2 (by rfl) ⟨1919070, by rfl⟩ : syracuseStep 5117521 = 3838141) B3838141
theorem B8525411 : Blo 1682041 8525411 := bstep (se 1 (by rfl) ⟨6394058, by rfl⟩ : syracuseStep 8525411 = 12788117) B12788117
theorem B5682797 : Blo 1682041 5682797 := bstep (se 3 (by rfl) ⟨1065524, by rfl⟩ : syracuseStep 5682797 = 2131049) B2131049
theorem B2840177 : Blo 1682041 2840177 := bstep (se 2 (by rfl) ⟨1065066, by rfl⟩ : syracuseStep 2840177 = 2130133) B2130133
theorem B10237553 : Blo 1682041 10237553 := bstep (se 2 (by rfl) ⟨3839082, by rfl⟩ : syracuseStep 10237553 = 7678165) B7678165
theorem B3593891 : Blo 1682041 3593891 := bstep (se 1 (by rfl) ⟨2695418, by rfl⟩ : syracuseStep 3593891 = 5390837) B5390837
theorem B5682851 : Blo 1682041 5682851 := bstep (se 1 (by rfl) ⟨4262138, by rfl⟩ : syracuseStep 5682851 = 8524277) B8524277
theorem B2840305 : Blo 1682041 2840305 := bstep (se 2 (by rfl) ⟨1065114, by rfl⟩ : syracuseStep 2840305 = 2130229) B2130229
theorem B2840339 : Blo 1682041 2840339 := bstep (se 1 (by rfl) ⟨2130254, by rfl⟩ : syracuseStep 2840339 = 4260509) B4260509
theorem B2840467 : Blo 1682041 2840467 := bstep (se 1 (by rfl) ⟨2130350, by rfl⟩ : syracuseStep 2840467 = 4260701) B4260701
theorem B6387619 : Blo 1682041 6387619 := bstep (se 1 (by rfl) ⟨4790714, by rfl⟩ : syracuseStep 6387619 = 9581429) B9581429
theorem B5683121 : Blo 1682041 5683121 := bstep (se 2 (by rfl) ⟨2131170, by rfl⟩ : syracuseStep 5683121 = 4262341) B4262341
theorem B2840609 : Blo 1682041 2840609 := bstep (se 2 (by rfl) ⟨1065228, by rfl⟩ : syracuseStep 2840609 = 2130457) B2130457
theorem B87447605 : Blo 1682041 87447605 := bstep (se 5 (by rfl) ⟨4099106, by rfl⟩ : syracuseStep 87447605 = 8198213) B8198213
theorem B2840737 : Blo 1682041 2840737 := bstep (se 2 (by rfl) ⟨1065276, by rfl⟩ : syracuseStep 2840737 = 2130553) B2130553
theorem B3594403 : Blo 1682041 3594403 := bstep (se 1 (by rfl) ⟨2695802, by rfl⟩ : syracuseStep 3594403 = 5391605) B5391605
theorem B2840771 : Blo 1682041 2840771 := bstep (se 1 (by rfl) ⟨2130578, by rfl⟩ : syracuseStep 2840771 = 4261157) B4261157
theorem B6822193 : Blo 1682041 6822193 := bstep (se 2 (by rfl) ⟨2558322, by rfl⟩ : syracuseStep 6822193 = 5116645) B5116645
theorem B2840899 : Blo 1682041 2840899 := bstep (se 1 (by rfl) ⟨2130674, by rfl⟩ : syracuseStep 2840899 = 4261349) B4261349
theorem B4258129 : Blo 1682041 4258129 := bstep (se 2 (by rfl) ⟨1596798, by rfl⟩ : syracuseStep 4258129 = 3193597) B3193597
theorem B8632739 : Blo 1682041 8632739 := bstep (se 1 (by rfl) ⟨6474554, by rfl⟩ : syracuseStep 8632739 = 12949109) B12949109
theorem B9099697 : Blo 1682041 9099697 := bstep (se 2 (by rfl) ⟨3412386, by rfl⟩ : syracuseStep 9099697 = 6824773) B6824773
theorem B2841041 : Blo 1682041 2841041 := bstep (se 2 (by rfl) ⟨1065390, by rfl⟩ : syracuseStep 2841041 = 2130781) B2130781
theorem B10787363 : Blo 1682041 10787363 := bstep (se 1 (by rfl) ⟨8090522, by rfl⟩ : syracuseStep 10787363 = 16181045) B16181045
theorem B6068785 : Blo 1682041 6068785 := bstep (se 2 (by rfl) ⟨2275794, by rfl⟩ : syracuseStep 6068785 = 4551589) B4551589
theorem B2841169 : Blo 1682041 2841169 := bstep (se 2 (by rfl) ⟨1065438, by rfl⟩ : syracuseStep 2841169 = 2130877) B2130877
theorem B10230371 : Blo 1682041 10230371 := bstep (se 1 (by rfl) ⟨7672778, by rfl⟩ : syracuseStep 10230371 = 15345557) B15345557
theorem B4258403 : Blo 1682041 4258403 := bstep (se 1 (by rfl) ⟨3193802, by rfl⟩ : syracuseStep 4258403 = 6387605) B6387605
theorem B4790897 : Blo 1682041 4790897 := bstep (se 2 (by rfl) ⟨1796586, by rfl⟩ : syracuseStep 4790897 = 3593173) B3593173
theorem B2841203 : Blo 1682041 2841203 := bstep (se 1 (by rfl) ⟨2130902, by rfl⟩ : syracuseStep 2841203 = 4261805) B4261805
theorem B10779313 : Blo 1682041 10779313 := bstep (se 2 (by rfl) ⟨4042242, by rfl⟩ : syracuseStep 10779313 = 8084485) B8084485
theorem B2841331 : Blo 1682041 2841331 := bstep (se 1 (by rfl) ⟨2130998, by rfl⟩ : syracuseStep 2841331 = 4261997) B4261997
theorem B4258595 : Blo 1682041 4258595 := bstep (se 1 (by rfl) ⟨3193946, by rfl⟩ : syracuseStep 4258595 = 6387893) B6387893
theorem B3193681 : Blo 1682041 3193681 := bstep (se 2 (by rfl) ⟨1197630, by rfl⟩ : syracuseStep 3193681 = 2395261) B2395261
theorem B3595121 : Blo 1682041 3595121 := bstep (se 2 (by rfl) ⟨1348170, by rfl⟩ : syracuseStep 3595121 = 2696341) B2696341
theorem B2841473 : Blo 1682041 2841473 := bstep (se 2 (by rfl) ⟨1065552, by rfl⟩ : syracuseStep 2841473 = 2131105) B2131105
theorem B12786659 : Blo 1682041 12786659 := bstep (se 1 (by rfl) ⟨9589994, by rfl⟩ : syracuseStep 12786659 = 19179989) B19179989
theorem B2841601 : Blo 1682041 2841601 := bstep (se 2 (by rfl) ⟨1065600, by rfl⟩ : syracuseStep 2841601 = 2131201) B2131201
theorem B14384141 : Blo 1682041 14384141 := bstep (se 3 (by rfl) ⟨2697026, by rfl⟩ : syracuseStep 14384141 = 5394053) B5394053
theorem B2841635 : Blo 1682041 2841635 := bstep (se 1 (by rfl) ⟨2131226, by rfl⟩ : syracuseStep 2841635 = 4262453) B4262453
theorem B2022467 : Blo 1682041 2022467 := bstep (se 1 (by rfl) ⟨1516850, by rfl⟩ : syracuseStep 2022467 = 3033701) B3033701
theorem B19168325 : Blo 1682041 19168325 := bstep (se 4 (by rfl) ⟨1797030, by rfl⟩ : syracuseStep 19168325 = 3594061) B3594061
theorem B8518769 : Blo 1682041 8518769 := bstep (se 2 (by rfl) ⟨3194538, by rfl⟩ : syracuseStep 8518769 = 6389077) B6389077
theorem B2841763 : Blo 1682041 2841763 := bstep (se 1 (by rfl) ⟨2131322, by rfl⟩ : syracuseStep 2841763 = 4262645) B4262645
theorem B3194083 : Blo 1682041 3194083 := bstep (se 1 (by rfl) ⟨2395562, by rfl⟩ : syracuseStep 3194083 = 4791125) B4791125
theorem B3194129 : Blo 1682041 3194129 := bstep (se 2 (by rfl) ⟨1197798, by rfl⟩ : syracuseStep 3194129 = 2395597) B2395597
theorem B5758253 : Blo 1682041 5758253 := bstep (se 3 (by rfl) ⟨1079672, by rfl⟩ : syracuseStep 5758253 = 2159345) B2159345
theorem B2129267 : Blo 1682041 2129267 := bstep (se 1 (by rfl) ⟨1596950, by rfl⟩ : syracuseStep 2129267 = 3193901) B3193901
theorem B3194417 : Blo 1682041 3194417 := bstep (se 2 (by rfl) ⟨1197906, by rfl⟩ : syracuseStep 3194417 = 2395813) B2395813
theorem B13647473 : Blo 1682041 13647473 := bstep (se 2 (by rfl) ⟨5117802, by rfl⟩ : syracuseStep 13647473 = 10235605) B10235605
theorem B19177073 : Blo 1682041 19177073 := bstep (se 2 (by rfl) ⟨7191402, by rfl⟩ : syracuseStep 19177073 = 14382805) B14382805
theorem B3595907 : Blo 1682041 3595907 := bstep (se 1 (by rfl) ⟨2696930, by rfl⟩ : syracuseStep 3595907 = 5393861) B5393861
theorem B4259537 : Blo 1682041 4259537 := bstep (se 2 (by rfl) ⟨1597326, by rfl⟩ : syracuseStep 4259537 = 3194653) B3194653
theorem B4259587 : Blo 1682041 4259587 := bstep (se 1 (by rfl) ⟨3194690, by rfl⟩ : syracuseStep 4259587 = 6389381) B6389381
theorem B5390221 : Blo 1682041 5390221 := bstep (se 3 (by rfl) ⟨1010666, by rfl⟩ : syracuseStep 5390221 = 2021333) B2021333
theorem B4259729 : Blo 1682041 4259729 := bstep (se 2 (by rfl) ⟨1597398, by rfl⟩ : syracuseStep 4259729 = 3194797) B3194797
theorem B3784625 : Blo 1682041 3784625 := bstep (se 2 (by rfl) ⟨1419234, by rfl⟩ : syracuseStep 3784625 = 2838469) B2838469
theorem B3784643 : Blo 1682041 3784643 := bstep (se 1 (by rfl) ⟨2838482, by rfl⟩ : syracuseStep 3784643 = 5676965) B5676965
theorem B2523089 : Blo 1682041 2523089 := bstep (se 2 (by rfl) ⟨946158, by rfl⟩ : syracuseStep 2523089 = 1892317) B1892317
theorem B2523107 : Blo 1682041 2523107 := bstep (se 1 (by rfl) ⟨1892330, by rfl⟩ : syracuseStep 2523107 = 3784661) B3784661
theorem B3784715 : Blo 1682041 3784715 := bstep (se 1 (by rfl) ⟨2838536, by rfl⟩ : syracuseStep 3784715 = 5677073) B5677073
theorem B3194903 : Blo 1682041 3194903 := bstep (se 1 (by rfl) ⟨2396177, by rfl⟩ : syracuseStep 3194903 = 4792355) B4792355
theorem B2523161 : Blo 1682041 2523161 := bstep (se 2 (by rfl) ⟨946185, by rfl⟩ : syracuseStep 2523161 = 1892371) B1892371
theorem B4259891 : Blo 1682041 4259891 := bstep (se 1 (by rfl) ⟨3194918, by rfl⟩ : syracuseStep 4259891 = 6389837) B6389837
theorem B1892407 : Blo 1682041 1892407 := bstep (se 1 (by rfl) ⟨1419305, by rfl⟩ : syracuseStep 1892407 = 2838611) B2838611
theorem B3784769 : Blo 1682041 3784769 := bstep (se 2 (by rfl) ⟨1419288, by rfl⟩ : syracuseStep 3784769 = 2838577) B2838577
theorem B5390401 : Blo 1682041 5390401 := bstep (se 2 (by rfl) ⟨2021400, by rfl⟩ : syracuseStep 5390401 = 4042801) B4042801
theorem B2523275 : Blo 1682041 2523275 := bstep (se 1 (by rfl) ⟨1892456, by rfl⟩ : syracuseStep 2523275 = 3784913) B3784913
theorem B2523287 : Blo 1682041 2523287 := bstep (se 1 (by rfl) ⟨1892465, by rfl⟩ : syracuseStep 2523287 = 3784931) B3784931
theorem B5677235 : Blo 1682041 5677235 := bstep (se 1 (by rfl) ⟨4257926, by rfl⟩ : syracuseStep 5677235 = 8515853) B8515853
theorem B2523353 : Blo 1682041 2523353 := bstep (se 2 (by rfl) ⟨946257, by rfl⟩ : syracuseStep 2523353 = 1892515) B1892515
theorem B4792537 : Blo 1682041 4792537 := bstep (se 2 (by rfl) ⟨1797201, by rfl⟩ : syracuseStep 4792537 = 3594403) B3594403
theorem B1892587 : Blo 1682041 1892587 := bstep (se 1 (by rfl) ⟨1419440, by rfl⟩ : syracuseStep 1892587 = 2838881) B2838881
theorem B12124421 : Blo 1682041 12124421 := bstep (se 4 (by rfl) ⟨1136664, by rfl⟩ : syracuseStep 12124421 = 2273329) B2273329
theorem B3784985 : Blo 1682041 3784985 := bstep (se 2 (by rfl) ⟨1419369, by rfl⟩ : syracuseStep 3784985 = 2838739) B2838739
theorem B2523467 : Blo 1682041 2523467 := bstep (se 1 (by rfl) ⟨1892600, by rfl⟩ : syracuseStep 2523467 = 3785201) B3785201
theorem B7192907 : Blo 1682041 7192907 := bstep (se 1 (by rfl) ⟨5394680, by rfl⟩ : syracuseStep 7192907 = 10789361) B10789361
theorem B2523479 : Blo 1682041 2523479 := bstep (se 1 (by rfl) ⟨1892609, by rfl⟩ : syracuseStep 2523479 = 3785219) B3785219
theorem B1892695 : Blo 1682041 1892695 := bstep (se 1 (by rfl) ⟨1419521, by rfl⟩ : syracuseStep 1892695 = 2839043) B2839043
theorem B4260185 : Blo 1682041 4260185 := bstep (se 2 (by rfl) ⟨1597569, by rfl⟩ : syracuseStep 4260185 = 3195139) B3195139
theorem B3785075 : Blo 1682041 3785075 := bstep (se 1 (by rfl) ⟨2838806, by rfl⟩ : syracuseStep 3785075 = 5677613) B5677613
theorem B14385539 : Blo 1682041 14385539 := bstep (se 1 (by rfl) ⟨10789154, by rfl⟩ : syracuseStep 14385539 = 21578309) B21578309
theorem B3785111 : Blo 1682041 3785111 := bstep (se 1 (by rfl) ⟨2838833, by rfl⟩ : syracuseStep 3785111 = 5677667) B5677667
theorem B2523545 : Blo 1682041 2523545 := bstep (se 2 (by rfl) ⟨946329, by rfl⟩ : syracuseStep 2523545 = 1892659) B1892659
theorem B5677505 : Blo 1682041 5677505 := bstep (se 2 (by rfl) ⟨2129064, by rfl⟩ : syracuseStep 5677505 = 4258129) B4258129
theorem B2130391 : Blo 1682041 2130391 := bstep (se 1 (by rfl) ⟨1597793, by rfl⟩ : syracuseStep 2130391 = 3195587) B3195587
theorem B2523659 : Blo 1682041 2523659 := bstep (se 1 (by rfl) ⟨1892744, by rfl⟩ : syracuseStep 2523659 = 3785489) B3785489
theorem B1892875 : Blo 1682041 1892875 := bstep (se 1 (by rfl) ⟨1419656, by rfl⟩ : syracuseStep 1892875 = 2839313) B2839313
theorem B6062615 : Blo 1682041 6062615 := bstep (se 1 (by rfl) ⟨4546961, by rfl⟩ : syracuseStep 6062615 = 9093923) B9093923
theorem B2523671 : Blo 1682041 2523671 := bstep (se 1 (by rfl) ⟨1892753, by rfl⟩ : syracuseStep 2523671 = 3785507) B3785507
theorem B13640237 : Blo 1682041 13640237 := bstep (se 3 (by rfl) ⟨2557544, by rfl⟩ : syracuseStep 13640237 = 5115089) B5115089
theorem B6390323 : Blo 1682041 6390323 := bstep (se 1 (by rfl) ⟨4792742, by rfl⟩ : syracuseStep 6390323 = 9585485) B9585485
theorem B3195443 : Blo 1682041 3195443 := bstep (se 1 (by rfl) ⟨2396582, by rfl⟩ : syracuseStep 3195443 = 4793165) B4793165
theorem B932774453 : Blo 1682041 932774453 := bstep (se 5 (by rfl) ⟨43723802, by rfl⟩ : syracuseStep 932774453 = 87447605) B87447605
theorem B12132929 : Blo 1682041 12132929 := bstep (se 2 (by rfl) ⟨4549848, by rfl⟩ : syracuseStep 12132929 = 9099697) B9099697
theorem B3785291 : Blo 1682041 3785291 := bstep (se 1 (by rfl) ⟨2838968, by rfl⟩ : syracuseStep 3785291 = 5677937) B5677937
theorem B2523737 : Blo 1682041 2523737 := bstep (se 2 (by rfl) ⟨946401, by rfl⟩ : syracuseStep 2523737 = 1892803) B1892803
theorem B4792925 : Blo 1682041 4792925 := bstep (se 3 (by rfl) ⟨898673, by rfl⟩ : syracuseStep 4792925 = 1797347) B1797347
theorem B1892983 : Blo 1682041 1892983 := bstep (se 1 (by rfl) ⟨1419737, by rfl⟩ : syracuseStep 1892983 = 2839475) B2839475
theorem B3785345 : Blo 1682041 3785345 := bstep (se 2 (by rfl) ⟨1419504, by rfl⟩ : syracuseStep 3785345 = 2839009) B2839009
theorem B10781363 : Blo 1682041 10781363 := bstep (se 1 (by rfl) ⟨8086022, by rfl⟩ : syracuseStep 10781363 = 16172045) B16172045
theorem B2523851 : Blo 1682041 2523851 := bstep (se 1 (by rfl) ⟨1892888, by rfl⟩ : syracuseStep 2523851 = 3785777) B3785777
theorem B2523863 : Blo 1682041 2523863 := bstep (se 1 (by rfl) ⟨1892897, by rfl⟩ : syracuseStep 2523863 = 3785795) B3785795
theorem B3031769 : Blo 1682041 3031769 := bstep (se 2 (by rfl) ⟨1136913, by rfl⟩ : syracuseStep 3031769 = 2273827) B2273827
theorem B2523929 : Blo 1682041 2523929 := bstep (se 2 (by rfl) ⟨946473, by rfl⟩ : syracuseStep 2523929 = 1892947) B1892947
theorem B1893163 : Blo 1682041 1893163 := bstep (se 1 (by rfl) ⟨1419872, by rfl⟩ : syracuseStep 1893163 = 2839745) B2839745
theorem B3785561 : Blo 1682041 3785561 := bstep (se 2 (by rfl) ⟨1419585, by rfl⟩ : syracuseStep 3785561 = 2839171) B2839171
theorem B4924253 : Blo 1682041 4924253 := bstep (se 3 (by rfl) ⟨923297, by rfl⟩ : syracuseStep 4924253 = 1846595) B1846595
theorem B2524043 : Blo 1682041 2524043 := bstep (se 1 (by rfl) ⟨1893032, by rfl⟩ : syracuseStep 2524043 = 3786065) B3786065
theorem B2524055 : Blo 1682041 2524055 := bstep (se 1 (by rfl) ⟨1893041, by rfl⟩ : syracuseStep 2524055 = 3786083) B3786083
theorem B1893271 : Blo 1682041 1893271 := bstep (se 1 (by rfl) ⟨1419953, by rfl⟩ : syracuseStep 1893271 = 2839907) B2839907
theorem B3785651 : Blo 1682041 3785651 := bstep (se 1 (by rfl) ⟨2839238, by rfl⟩ : syracuseStep 3785651 = 5678477) B5678477
theorem B3785687 : Blo 1682041 3785687 := bstep (se 1 (by rfl) ⟨2839265, by rfl⟩ : syracuseStep 3785687 = 5678531) B5678531
theorem B2524121 : Blo 1682041 2524121 := bstep (se 2 (by rfl) ⟨946545, by rfl⟩ : syracuseStep 2524121 = 1893091) B1893091
theorem B5678045 : Blo 1682041 5678045 := bstep (se 3 (by rfl) ⟨1064633, by rfl⟩ : syracuseStep 5678045 = 2129267) B2129267
theorem B3195929 : Blo 1682041 3195929 := bstep (se 2 (by rfl) ⟨1198473, by rfl⟩ : syracuseStep 3195929 = 2396947) B2396947
theorem B13648931 : Blo 1682041 13648931 := bstep (se 1 (by rfl) ⟨10236698, by rfl⟩ : syracuseStep 13648931 = 20473397) B20473397
theorem B19178531 : Blo 1682041 19178531 := bstep (se 1 (by rfl) ⟨14383898, by rfl⟩ : syracuseStep 19178531 = 28767797) B28767797
theorem B2524235 : Blo 1682041 2524235 := bstep (se 1 (by rfl) ⟨1893176, by rfl⟩ : syracuseStep 2524235 = 3786353) B3786353
theorem B1893451 : Blo 1682041 1893451 := bstep (se 1 (by rfl) ⟨1420088, by rfl⟩ : syracuseStep 1893451 = 2840177) B2840177
theorem B6825035 : Blo 1682041 6825035 := bstep (se 1 (by rfl) ⟨5118776, by rfl⟩ : syracuseStep 6825035 = 10237553) B10237553
theorem B2524247 : Blo 1682041 2524247 := bstep (se 1 (by rfl) ⟨1893185, by rfl⟩ : syracuseStep 2524247 = 3786371) B3786371
theorem B3785867 : Blo 1682041 3785867 := bstep (se 1 (by rfl) ⟨2839400, by rfl⟩ : syracuseStep 3785867 = 5678801) B5678801
theorem B2524313 : Blo 1682041 2524313 := bstep (se 2 (by rfl) ⟨946617, by rfl⟩ : syracuseStep 2524313 = 1893235) B1893235
theorem B1893559 : Blo 1682041 1893559 := bstep (se 1 (by rfl) ⟨1420169, by rfl⟩ : syracuseStep 1893559 = 2840339) B2840339
theorem B3785921 : Blo 1682041 3785921 := bstep (se 2 (by rfl) ⟨1419720, by rfl⟩ : syracuseStep 3785921 = 2839441) B2839441
theorem B2524427 : Blo 1682041 2524427 := bstep (se 1 (by rfl) ⟨1893320, by rfl⟩ : syracuseStep 2524427 = 3786641) B3786641
theorem B2131211 : Blo 1682041 2131211 := bstep (se 1 (by rfl) ⟨1598408, by rfl⟩ : syracuseStep 2131211 = 3196817) B3196817
theorem B2524439 : Blo 1682041 2524439 := bstep (se 1 (by rfl) ⟨1893329, by rfl⟩ : syracuseStep 2524439 = 3786659) B3786659
theorem B9585985 : Blo 1682041 9585985 := bstep (se 2 (by rfl) ⟨3594744, by rfl⟩ : syracuseStep 9585985 = 7189489) B7189489
theorem B2524505 : Blo 1682041 2524505 := bstep (se 2 (by rfl) ⟨946689, by rfl⟩ : syracuseStep 2524505 = 1893379) B1893379
theorem B1893739 : Blo 1682041 1893739 := bstep (se 1 (by rfl) ⟨1420304, by rfl⟩ : syracuseStep 1893739 = 2840609) B2840609
theorem B3786137 : Blo 1682041 3786137 := bstep (se 2 (by rfl) ⟨1419801, by rfl⟩ : syracuseStep 3786137 = 2839603) B2839603
theorem B2524619 : Blo 1682041 2524619 := bstep (se 1 (by rfl) ⟨1893464, by rfl⟩ : syracuseStep 2524619 = 3786929) B3786929
theorem B2524631 : Blo 1682041 2524631 := bstep (se 1 (by rfl) ⟨1893473, by rfl⟩ : syracuseStep 2524631 = 3786947) B3786947
theorem B1893847 : Blo 1682041 1893847 := bstep (se 1 (by rfl) ⟨1420385, by rfl⟩ : syracuseStep 1893847 = 2840771) B2840771
theorem B3786227 : Blo 1682041 3786227 := bstep (se 1 (by rfl) ⟨2839670, by rfl⟩ : syracuseStep 3786227 = 5679341) B5679341
theorem B3786263 : Blo 1682041 3786263 := bstep (se 1 (by rfl) ⟨2839697, by rfl⟩ : syracuseStep 3786263 = 5679395) B5679395
theorem B2524697 : Blo 1682041 2524697 := bstep (se 2 (by rfl) ⟨946761, by rfl⟩ : syracuseStep 2524697 = 1893523) B1893523
theorem B2524811 : Blo 1682041 2524811 := bstep (se 1 (by rfl) ⟨1893608, by rfl⟩ : syracuseStep 2524811 = 3787217) B3787217
theorem B1894027 : Blo 1682041 1894027 := bstep (se 1 (by rfl) ⟨1420520, by rfl⟩ : syracuseStep 1894027 = 2841041) B2841041
theorem B2524823 : Blo 1682041 2524823 := bstep (se 1 (by rfl) ⟨1893617, by rfl⟩ : syracuseStep 2524823 = 3787235) B3787235
theorem B3786443 : Blo 1682041 3786443 := bstep (se 1 (by rfl) ⟨2839832, by rfl⟩ : syracuseStep 3786443 = 5679665) B5679665
theorem B2524889 : Blo 1682041 2524889 := bstep (se 2 (by rfl) ⟨946833, by rfl⟩ : syracuseStep 2524889 = 1893667) B1893667
theorem B1894135 : Blo 1682041 1894135 := bstep (se 1 (by rfl) ⟨1420601, by rfl⟩ : syracuseStep 1894135 = 2841203) B2841203
theorem B3786497 : Blo 1682041 3786497 := bstep (se 2 (by rfl) ⟨1419936, by rfl⟩ : syracuseStep 3786497 = 2839873) B2839873
theorem B2525003 : Blo 1682041 2525003 := bstep (se 1 (by rfl) ⟨1893752, by rfl⟩ : syracuseStep 2525003 = 3787505) B3787505
theorem B2525015 : Blo 1682041 2525015 := bstep (se 1 (by rfl) ⟨1893761, by rfl⟩ : syracuseStep 2525015 = 3787523) B3787523
theorem B7014275 : Blo 1682041 7014275 := bstep (se 1 (by rfl) ⟨5260706, by rfl⟩ : syracuseStep 7014275 = 10521413) B10521413
theorem B2525081 : Blo 1682041 2525081 := bstep (se 2 (by rfl) ⟨946905, by rfl⟩ : syracuseStep 2525081 = 1893811) B1893811
theorem B1894315 : Blo 1682041 1894315 := bstep (se 1 (by rfl) ⟨1420736, by rfl⟩ : syracuseStep 1894315 = 2841473) B2841473
theorem B4261835 : Blo 1682041 4261835 := bstep (se 1 (by rfl) ⟨3196376, by rfl⟩ : syracuseStep 4261835 = 6392753) B6392753
theorem B3786713 : Blo 1682041 3786713 := bstep (se 2 (by rfl) ⟨1420017, by rfl⟩ : syracuseStep 3786713 = 2840035) B2840035
theorem B6391811 : Blo 1682041 6391811 := bstep (se 1 (by rfl) ⟨4793858, by rfl⟩ : syracuseStep 6391811 = 9587717) B9587717
theorem B2525195 : Blo 1682041 2525195 := bstep (se 1 (by rfl) ⟨1893896, by rfl⟩ : syracuseStep 2525195 = 3787793) B3787793
theorem B2525207 : Blo 1682041 2525207 := bstep (se 1 (by rfl) ⟨1893905, by rfl⟩ : syracuseStep 2525207 = 3787811) B3787811
theorem B1894423 : Blo 1682041 1894423 := bstep (se 1 (by rfl) ⟨1420817, by rfl⟩ : syracuseStep 1894423 = 2841635) B2841635
theorem B3786803 : Blo 1682041 3786803 := bstep (se 1 (by rfl) ⟨2840102, by rfl⟩ : syracuseStep 3786803 = 5680205) B5680205
theorem B3033139 : Blo 1682041 3033139 := bstep (se 1 (by rfl) ⟨2274854, by rfl⟩ : syracuseStep 3033139 = 4549709) B4549709
theorem B5679179 : Blo 1682041 5679179 := bstep (se 1 (by rfl) ⟨4259384, by rfl⟩ : syracuseStep 5679179 = 8518769) B8518769
theorem B3786839 : Blo 1682041 3786839 := bstep (se 1 (by rfl) ⟨2840129, by rfl⟩ : syracuseStep 3786839 = 5680259) B5680259
theorem B2525273 : Blo 1682041 2525273 := bstep (se 2 (by rfl) ⟨946977, by rfl⟩ : syracuseStep 2525273 = 1893955) B1893955
theorem B2525387 : Blo 1682041 2525387 := bstep (se 1 (by rfl) ⟨1894040, by rfl⟩ : syracuseStep 2525387 = 3788081) B3788081
theorem B2525399 : Blo 1682041 2525399 := bstep (se 1 (by rfl) ⟨1894049, by rfl⟩ : syracuseStep 2525399 = 3788099) B3788099
theorem B3787019 : Blo 1682041 3787019 := bstep (se 1 (by rfl) ⟨2840264, by rfl⟩ : syracuseStep 3787019 = 5680529) B5680529
theorem B2525465 : Blo 1682041 2525465 := bstep (se 2 (by rfl) ⟨947049, by rfl⟩ : syracuseStep 2525465 = 1894099) B1894099
theorem B3787073 : Blo 1682041 3787073 := bstep (se 2 (by rfl) ⟨1420152, by rfl⟩ : syracuseStep 3787073 = 2840305) B2840305
theorem B5679449 : Blo 1682041 5679449 := bstep (se 2 (by rfl) ⟨2129793, by rfl⟩ : syracuseStep 5679449 = 4259587) B4259587
theorem B4548953 : Blo 1682041 4548953 := bstep (se 2 (by rfl) ⟨1705857, by rfl⟩ : syracuseStep 4548953 = 3411715) B3411715
theorem B2525579 : Blo 1682041 2525579 := bstep (se 1 (by rfl) ⟨1894184, by rfl⟩ : syracuseStep 2525579 = 3788369) B3788369
theorem B2525591 : Blo 1682041 2525591 := bstep (se 1 (by rfl) ⟨1894193, by rfl⟩ : syracuseStep 2525591 = 3788387) B3788387
theorem B1919435 : Blo 1682041 1919435 := bstep (se 1 (by rfl) ⟨1439576, by rfl⟩ : syracuseStep 1919435 = 2879153) B2879153
theorem B6392267 : Blo 1682041 6392267 := bstep (se 1 (by rfl) ⟨4794200, by rfl⟩ : syracuseStep 6392267 = 9588401) B9588401
theorem B2525657 : Blo 1682041 2525657 := bstep (se 2 (by rfl) ⟨947121, by rfl⟩ : syracuseStep 2525657 = 1894243) B1894243
theorem B7186961 : Blo 1682041 7186961 := bstep (se 2 (by rfl) ⟨2695110, by rfl⟩ : syracuseStep 7186961 = 5390221) B5390221
theorem B3787289 : Blo 1682041 3787289 := bstep (se 2 (by rfl) ⟨1420233, by rfl⟩ : syracuseStep 3787289 = 2840467) B2840467
theorem B2525771 : Blo 1682041 2525771 := bstep (se 1 (by rfl) ⟨1894328, by rfl⟩ : syracuseStep 2525771 = 3788657) B3788657
theorem B2525783 : Blo 1682041 2525783 := bstep (se 1 (by rfl) ⟨1894337, by rfl⟩ : syracuseStep 2525783 = 3788675) B3788675
theorem B8522333 : Blo 1682041 8522333 := bstep (se 3 (by rfl) ⟨1597937, by rfl⟩ : syracuseStep 8522333 = 3195875) B3195875
theorem B3787379 : Blo 1682041 3787379 := bstep (se 1 (by rfl) ⟨2840534, by rfl⟩ : syracuseStep 3787379 = 5681069) B5681069
theorem B1682059 : Blo 1682041 1682059 := bstep (se 1 (by rfl) ⟨1261544, by rfl⟩ : syracuseStep 1682059 = 2523089) B2523089
theorem B6392465 : Blo 1682041 6392465 := bstep (se 2 (by rfl) ⟨2397174, by rfl⟩ : syracuseStep 6392465 = 4794349) B4794349
theorem B1682071 : Blo 1682041 1682071 := bstep (se 1 (by rfl) ⟨1261553, by rfl⟩ : syracuseStep 1682071 = 2523107) B2523107
theorem B26249879 : Blo 1682041 26249879 := bstep (se 1 (by rfl) ⟨19687409, by rfl⟩ : syracuseStep 26249879 = 39374819) B39374819
theorem B3787415 : Blo 1682041 3787415 := bstep (se 1 (by rfl) ⟨2840561, by rfl⟩ : syracuseStep 3787415 = 5681123) B5681123
theorem B2525849 : Blo 1682041 2525849 := bstep (se 2 (by rfl) ⟨947193, by rfl⟩ : syracuseStep 2525849 = 1894387) B1894387
theorem B1682091 : Blo 1682041 1682091 := bstep (se 1 (by rfl) ⟨1261568, by rfl⟩ : syracuseStep 1682091 = 2523137) B2523137
theorem B1682103 : Blo 1682041 1682103 := bstep (se 1 (by rfl) ⟨1261577, by rfl⟩ : syracuseStep 1682103 = 2523155) B2523155
theorem B1682123 : Blo 1682041 1682123 := bstep (se 1 (by rfl) ⟨1261592, by rfl⟩ : syracuseStep 1682123 = 2523185) B2523185
theorem B43215565 : Blo 1682041 43215565 := bstep (se 3 (by rfl) ⟨8102918, by rfl⟩ : syracuseStep 43215565 = 16205837) B16205837
theorem B12782285 : Blo 1682041 12782285 := bstep (se 3 (by rfl) ⟨2396678, by rfl⟩ : syracuseStep 12782285 = 4793357) B4793357
theorem B1682135 : Blo 1682041 1682135 := bstep (se 1 (by rfl) ⟨1261601, by rfl⟩ : syracuseStep 1682135 = 2523203) B2523203
theorem B1682155 : Blo 1682041 1682155 := bstep (se 1 (by rfl) ⟨1261616, by rfl⟩ : syracuseStep 1682155 = 2523233) B2523233
theorem B1796843 : Blo 1682041 1796843 := bstep (se 1 (by rfl) ⟨1347632, by rfl⟩ : syracuseStep 1796843 = 2695265) B2695265
theorem B43158257 : Blo 1682041 43158257 := bstep (se 2 (by rfl) ⟨16184346, by rfl⟩ : syracuseStep 43158257 = 32368693) B32368693
theorem B1682167 : Blo 1682041 1682167 := bstep (se 1 (by rfl) ⟨1261625, by rfl⟩ : syracuseStep 1682167 = 2523251) B2523251
theorem B1682187 : Blo 1682041 1682187 := bstep (se 1 (by rfl) ⟨1261640, by rfl⟩ : syracuseStep 1682187 = 2523281) B2523281
theorem B2525963 : Blo 1682041 2525963 := bstep (se 1 (by rfl) ⟨1894472, by rfl⟩ : syracuseStep 2525963 = 3788945) B3788945
theorem B1682199 : Blo 1682041 1682199 := bstep (se 1 (by rfl) ⟨1261649, by rfl⟩ : syracuseStep 1682199 = 2523299) B2523299
theorem B2525975 : Blo 1682041 2525975 := bstep (se 1 (by rfl) ⟨1894481, by rfl⟩ : syracuseStep 2525975 = 3788963) B3788963
theorem B1682219 : Blo 1682041 1682219 := bstep (se 1 (by rfl) ⟨1261664, by rfl⟩ : syracuseStep 1682219 = 2523329) B2523329
theorem B1682231 : Blo 1682041 1682231 := bstep (se 1 (by rfl) ⟨1261673, by rfl⟩ : syracuseStep 1682231 = 2523347) B2523347
theorem B1682251 : Blo 1682041 1682251 := bstep (se 1 (by rfl) ⟨1261688, by rfl⟩ : syracuseStep 1682251 = 2523377) B2523377
theorem B3787595 : Blo 1682041 3787595 := bstep (se 1 (by rfl) ⟨2840696, by rfl⟩ : syracuseStep 3787595 = 5681393) B5681393
theorem B1682263 : Blo 1682041 1682263 := bstep (se 1 (by rfl) ⟨1261697, by rfl⟩ : syracuseStep 1682263 = 2523395) B2523395
theorem B2526041 : Blo 1682041 2526041 := bstep (se 2 (by rfl) ⟨947265, by rfl⟩ : syracuseStep 2526041 = 1894531) B1894531
theorem B5393245 : Blo 1682041 5393245 := bstep (se 3 (by rfl) ⟨1011233, by rfl⟩ : syracuseStep 5393245 = 2022467) B2022467
theorem B1682283 : Blo 1682041 1682283 := bstep (se 1 (by rfl) ⟨1261712, by rfl⟩ : syracuseStep 1682283 = 2523425) B2523425
theorem B1682295 : Blo 1682041 1682295 := bstep (se 1 (by rfl) ⟨1261721, by rfl⟩ : syracuseStep 1682295 = 2523443) B2523443
theorem B3787649 : Blo 1682041 3787649 := bstep (se 2 (by rfl) ⟨1420368, by rfl⟩ : syracuseStep 3787649 = 2840737) B2840737
theorem B1682315 : Blo 1682041 1682315 := bstep (se 1 (by rfl) ⟨1261736, by rfl⟩ : syracuseStep 1682315 = 2523473) B2523473
theorem B1682327 : Blo 1682041 1682327 := bstep (se 1 (by rfl) ⟨1261745, by rfl⟩ : syracuseStep 1682327 = 2523491) B2523491
theorem B1682347 : Blo 1682041 1682347 := bstep (se 1 (by rfl) ⟨1261760, by rfl⟩ : syracuseStep 1682347 = 2523521) B2523521
theorem B1682359 : Blo 1682041 1682359 := bstep (se 1 (by rfl) ⟨1261769, by rfl⟩ : syracuseStep 1682359 = 2523539) B2523539
theorem B1682379 : Blo 1682041 1682379 := bstep (se 1 (by rfl) ⟨1261784, by rfl⟩ : syracuseStep 1682379 = 2523569) B2523569
theorem B1919947 : Blo 1682041 1919947 := bstep (se 1 (by rfl) ⟨1439960, by rfl⟩ : syracuseStep 1919947 = 2879921) B2879921
theorem B1682391 : Blo 1682041 1682391 := bstep (se 1 (by rfl) ⟨1261793, by rfl⟩ : syracuseStep 1682391 = 2523587) B2523587
theorem B1682411 : Blo 1682041 1682411 := bstep (se 1 (by rfl) ⟨1261808, by rfl⟩ : syracuseStep 1682411 = 2523617) B2523617
theorem B1682423 : Blo 1682041 1682423 := bstep (se 1 (by rfl) ⟨1261817, by rfl⟩ : syracuseStep 1682423 = 2523635) B2523635
theorem B7285763 : Blo 1682041 7285763 := bstep (se 1 (by rfl) ⟨5464322, by rfl⟩ : syracuseStep 7285763 = 10928645) B10928645
theorem B1682443 : Blo 1682041 1682443 := bstep (se 1 (by rfl) ⟨1261832, by rfl⟩ : syracuseStep 1682443 = 2523665) B2523665
theorem B1682455 : Blo 1682041 1682455 := bstep (se 1 (by rfl) ⟨1261841, by rfl⟩ : syracuseStep 1682455 = 2523683) B2523683
theorem B5680151 : Blo 1682041 5680151 := bstep (se 1 (by rfl) ⟨4260113, by rfl⟩ : syracuseStep 5680151 = 8520227) B8520227
theorem B1682475 : Blo 1682041 1682475 := bstep (se 1 (by rfl) ⟨1261856, by rfl⟩ : syracuseStep 1682475 = 2523713) B2523713
theorem B1682487 : Blo 1682041 1682487 := bstep (se 1 (by rfl) ⟨1261865, by rfl⟩ : syracuseStep 1682487 = 2523731) B2523731
theorem B9096257 : Blo 1682041 9096257 := bstep (se 2 (by rfl) ⟨3411096, by rfl⟩ : syracuseStep 9096257 = 6822193) B6822193
theorem B6917185 : Blo 1682041 6917185 := bstep (se 2 (by rfl) ⟨2593944, by rfl⟩ : syracuseStep 6917185 = 5187889) B5187889
theorem B1682507 : Blo 1682041 1682507 := bstep (se 1 (by rfl) ⟨1261880, by rfl⟩ : syracuseStep 1682507 = 2523761) B2523761
theorem B1682519 : Blo 1682041 1682519 := bstep (se 1 (by rfl) ⟨1261889, by rfl⟩ : syracuseStep 1682519 = 2523779) B2523779
theorem B3787865 : Blo 1682041 3787865 := bstep (se 2 (by rfl) ⟨1420449, by rfl⟩ : syracuseStep 3787865 = 2840899) B2840899
theorem B1682539 : Blo 1682041 1682539 := bstep (se 1 (by rfl) ⟨1261904, by rfl⟩ : syracuseStep 1682539 = 2523809) B2523809
theorem B1682551 : Blo 1682041 1682551 := bstep (se 1 (by rfl) ⟨1261913, by rfl⟩ : syracuseStep 1682551 = 2523827) B2523827
theorem B1682571 : Blo 1682041 1682571 := bstep (se 1 (by rfl) ⟨1261928, by rfl⟩ : syracuseStep 1682571 = 2523857) B2523857
theorem B1682583 : Blo 1682041 1682583 := bstep (se 1 (by rfl) ⟨1261937, by rfl⟩ : syracuseStep 1682583 = 2523875) B2523875
theorem B2395289 : Blo 1682041 2395289 := bstep (se 2 (by rfl) ⟨898233, by rfl⟩ : syracuseStep 2395289 = 1796467) B1796467
theorem B1682603 : Blo 1682041 1682603 := bstep (se 1 (by rfl) ⟨1261952, by rfl⟩ : syracuseStep 1682603 = 2523905) B2523905
theorem B12782771 : Blo 1682041 12782771 := bstep (se 1 (by rfl) ⟨9587078, by rfl⟩ : syracuseStep 12782771 = 19174157) B19174157
theorem B3787955 : Blo 1682041 3787955 := bstep (se 1 (by rfl) ⟨2840966, by rfl⟩ : syracuseStep 3787955 = 5681933) B5681933
theorem B1682615 : Blo 1682041 1682615 := bstep (se 1 (by rfl) ⟨1261961, by rfl⟩ : syracuseStep 1682615 = 2523923) B2523923
theorem B1682635 : Blo 1682041 1682635 := bstep (se 1 (by rfl) ⟨1261976, by rfl⟩ : syracuseStep 1682635 = 2523953) B2523953
theorem B1682647 : Blo 1682041 1682647 := bstep (se 1 (by rfl) ⟨1261985, by rfl⟩ : syracuseStep 1682647 = 2523971) B2523971
theorem B3787991 : Blo 1682041 3787991 := bstep (se 1 (by rfl) ⟨2840993, by rfl⟩ : syracuseStep 3787991 = 5681987) B5681987
theorem B1682667 : Blo 1682041 1682667 := bstep (se 1 (by rfl) ⟨1262000, by rfl⟩ : syracuseStep 1682667 = 2524001) B2524001
theorem B1682679 : Blo 1682041 1682679 := bstep (se 1 (by rfl) ⟨1262009, by rfl⟩ : syracuseStep 1682679 = 2524019) B2524019
theorem B3837185 : Blo 1682041 3837185 := bstep (se 2 (by rfl) ⟨1438944, by rfl⟩ : syracuseStep 3837185 = 2877889) B2877889
theorem B1682699 : Blo 1682041 1682699 := bstep (se 1 (by rfl) ⟨1262024, by rfl⟩ : syracuseStep 1682699 = 2524049) B2524049
theorem B1682711 : Blo 1682041 1682711 := bstep (se 1 (by rfl) ⟨1262033, by rfl⟩ : syracuseStep 1682711 = 2524067) B2524067
theorem B1682731 : Blo 1682041 1682731 := bstep (se 1 (by rfl) ⟨1262048, by rfl⟩ : syracuseStep 1682731 = 2524097) B2524097
theorem B1682743 : Blo 1682041 1682743 := bstep (se 1 (by rfl) ⟨1262057, by rfl⟩ : syracuseStep 1682743 = 2524115) B2524115
theorem B17272129 : Blo 1682041 17272129 := bstep (se 2 (by rfl) ⟨6477048, by rfl⟩ : syracuseStep 17272129 = 12954097) B12954097
theorem B1682763 : Blo 1682041 1682763 := bstep (se 1 (by rfl) ⟨1262072, by rfl⟩ : syracuseStep 1682763 = 2524145) B2524145
theorem B1682775 : Blo 1682041 1682775 := bstep (se 1 (by rfl) ⟨1262081, by rfl⟩ : syracuseStep 1682775 = 2524163) B2524163
theorem B30698851 : Blo 1682041 30698851 := bstep (se 1 (by rfl) ⟨23024138, by rfl⟩ : syracuseStep 30698851 = 46048277) B46048277
theorem B1682795 : Blo 1682041 1682795 := bstep (se 1 (by rfl) ⟨1262096, by rfl⟩ : syracuseStep 1682795 = 2524193) B2524193
theorem B1682807 : Blo 1682041 1682807 := bstep (se 1 (by rfl) ⟨1262105, by rfl⟩ : syracuseStep 1682807 = 2524211) B2524211
theorem B1682827 : Blo 1682041 1682827 := bstep (se 1 (by rfl) ⟨1262120, by rfl⟩ : syracuseStep 1682827 = 2524241) B2524241
theorem B3788171 : Blo 1682041 3788171 := bstep (se 1 (by rfl) ⟨2841128, by rfl⟩ : syracuseStep 3788171 = 5682257) B5682257
theorem B1682839 : Blo 1682041 1682839 := bstep (se 1 (by rfl) ⟨1262129, by rfl⟩ : syracuseStep 1682839 = 2524259) B2524259
theorem B6393239 : Blo 1682041 6393239 := bstep (se 1 (by rfl) ⟨4794929, by rfl⟩ : syracuseStep 6393239 = 9589859) B9589859
theorem B1682859 : Blo 1682041 1682859 := bstep (se 1 (by rfl) ⟨1262144, by rfl⟩ : syracuseStep 1682859 = 2524289) B2524289
theorem B7187885 : Blo 1682041 7187885 := bstep (se 3 (by rfl) ⟨1347728, by rfl⟩ : syracuseStep 7187885 = 2695457) B2695457
theorem B1682871 : Blo 1682041 1682871 := bstep (se 1 (by rfl) ⟨1262153, by rfl⟩ : syracuseStep 1682871 = 2524307) B2524307
theorem B3788225 : Blo 1682041 3788225 := bstep (se 2 (by rfl) ⟨1420584, by rfl⟩ : syracuseStep 3788225 = 2841169) B2841169
theorem B4042187 : Blo 1682041 4042187 := bstep (se 1 (by rfl) ⟨3031640, by rfl⟩ : syracuseStep 4042187 = 6063281) B6063281
theorem B1682891 : Blo 1682041 1682891 := bstep (se 1 (by rfl) ⟨1262168, by rfl⟩ : syracuseStep 1682891 = 2524337) B2524337
theorem B1682903 : Blo 1682041 1682903 := bstep (se 1 (by rfl) ⟨1262177, by rfl⟩ : syracuseStep 1682903 = 2524355) B2524355
theorem B1682923 : Blo 1682041 1682923 := bstep (se 1 (by rfl) ⟨1262192, by rfl⟩ : syracuseStep 1682923 = 2524385) B2524385
theorem B1682935 : Blo 1682041 1682935 := bstep (se 1 (by rfl) ⟨1262201, by rfl⟩ : syracuseStep 1682935 = 2524403) B2524403
theorem B1682955 : Blo 1682041 1682955 := bstep (se 1 (by rfl) ⟨1262216, by rfl⟩ : syracuseStep 1682955 = 2524433) B2524433
theorem B1682967 : Blo 1682041 1682967 := bstep (se 1 (by rfl) ⟨1262225, by rfl⟩ : syracuseStep 1682967 = 2524451) B2524451
theorem B1682987 : Blo 1682041 1682987 := bstep (se 1 (by rfl) ⟨1262240, by rfl⟩ : syracuseStep 1682987 = 2524481) B2524481
theorem B5680691 : Blo 1682041 5680691 := bstep (se 1 (by rfl) ⟨4260518, by rfl⟩ : syracuseStep 5680691 = 8521037) B8521037
theorem B1682999 : Blo 1682041 1682999 := bstep (se 1 (by rfl) ⟨1262249, by rfl⟩ : syracuseStep 1682999 = 2524499) B2524499
theorem B14372417 : Blo 1682041 14372417 := bstep (se 2 (by rfl) ⟨5389656, by rfl⟩ : syracuseStep 14372417 = 10779313) B10779313
theorem B5115467 : Blo 1682041 5115467 := bstep (se 1 (by rfl) ⟨3836600, by rfl⟩ : syracuseStep 5115467 = 7673201) B7673201
theorem B19426891 : Blo 1682041 19426891 := bstep (se 1 (by rfl) ⟨14570168, by rfl⟩ : syracuseStep 19426891 = 29140337) B29140337
theorem B1683019 : Blo 1682041 1683019 := bstep (se 1 (by rfl) ⟨1262264, by rfl⟩ : syracuseStep 1683019 = 2524529) B2524529
theorem B1683031 : Blo 1682041 1683031 := bstep (se 1 (by rfl) ⟨1262273, by rfl⟩ : syracuseStep 1683031 = 2524547) B2524547
theorem B4099673 : Blo 1682041 4099673 := bstep (se 2 (by rfl) ⟨1537377, by rfl⟩ : syracuseStep 4099673 = 3074755) B3074755
theorem B6393437 : Blo 1682041 6393437 := bstep (se 3 (by rfl) ⟨1198769, by rfl⟩ : syracuseStep 6393437 = 2397539) B2397539
theorem B1683051 : Blo 1682041 1683051 := bstep (se 1 (by rfl) ⟨1262288, by rfl⟩ : syracuseStep 1683051 = 2524577) B2524577
theorem B1683063 : Blo 1682041 1683063 := bstep (se 1 (by rfl) ⟨1262297, by rfl⟩ : syracuseStep 1683063 = 2524595) B2524595
theorem B1683083 : Blo 1682041 1683083 := bstep (se 1 (by rfl) ⟨1262312, by rfl⟩ : syracuseStep 1683083 = 2524625) B2524625
theorem B1683095 : Blo 1682041 1683095 := bstep (se 1 (by rfl) ⟨1262321, by rfl⟩ : syracuseStep 1683095 = 2524643) B2524643
theorem B3788441 : Blo 1682041 3788441 := bstep (se 2 (by rfl) ⟨1420665, by rfl⟩ : syracuseStep 3788441 = 2841331) B2841331
theorem B1683115 : Blo 1682041 1683115 := bstep (se 1 (by rfl) ⟨1262336, by rfl⟩ : syracuseStep 1683115 = 2524673) B2524673
theorem B1683127 : Blo 1682041 1683127 := bstep (se 1 (by rfl) ⟨1262345, by rfl⟩ : syracuseStep 1683127 = 2524691) B2524691
theorem B1683147 : Blo 1682041 1683147 := bstep (se 1 (by rfl) ⟨1262360, by rfl⟩ : syracuseStep 1683147 = 2524721) B2524721
theorem B1683159 : Blo 1682041 1683159 := bstep (se 1 (by rfl) ⟨1262369, by rfl⟩ : syracuseStep 1683159 = 2524739) B2524739
theorem B1683179 : Blo 1682041 1683179 := bstep (se 1 (by rfl) ⟨1262384, by rfl⟩ : syracuseStep 1683179 = 2524769) B2524769
theorem B3788531 : Blo 1682041 3788531 := bstep (se 1 (by rfl) ⟨2841398, by rfl⟩ : syracuseStep 3788531 = 5682797) B5682797
theorem B1683191 : Blo 1682041 1683191 := bstep (se 1 (by rfl) ⟨1262393, by rfl⟩ : syracuseStep 1683191 = 2524787) B2524787
theorem B1683211 : Blo 1682041 1683211 := bstep (se 1 (by rfl) ⟨1262408, by rfl⟩ : syracuseStep 1683211 = 2524817) B2524817
theorem B2395927 : Blo 1682041 2395927 := bstep (se 1 (by rfl) ⟨1796945, by rfl⟩ : syracuseStep 2395927 = 3593891) B3593891
theorem B1683223 : Blo 1682041 1683223 := bstep (se 1 (by rfl) ⟨1262417, by rfl⟩ : syracuseStep 1683223 = 2524835) B2524835
theorem B2428697 : Blo 1682041 2428697 := bstep (se 2 (by rfl) ⟨910761, by rfl⟩ : syracuseStep 2428697 = 1821523) B1821523
theorem B3788567 : Blo 1682041 3788567 := bstep (se 1 (by rfl) ⟨2841425, by rfl⟩ : syracuseStep 3788567 = 5682851) B5682851
theorem B1683243 : Blo 1682041 1683243 := bstep (se 1 (by rfl) ⟨1262432, by rfl⟩ : syracuseStep 1683243 = 2524865) B2524865
theorem B1683255 : Blo 1682041 1683255 := bstep (se 1 (by rfl) ⟨1262441, by rfl⟩ : syracuseStep 1683255 = 2524883) B2524883
theorem B5680961 : Blo 1682041 5680961 := bstep (se 2 (by rfl) ⟨2130360, by rfl⟩ : syracuseStep 5680961 = 4260721) B4260721
theorem B1683275 : Blo 1682041 1683275 := bstep (se 1 (by rfl) ⟨1262456, by rfl⟩ : syracuseStep 1683275 = 2524913) B2524913
theorem B1683287 : Blo 1682041 1683287 := bstep (se 1 (by rfl) ⟨1262465, by rfl⟩ : syracuseStep 1683287 = 2524931) B2524931
theorem B1683307 : Blo 1682041 1683307 := bstep (se 1 (by rfl) ⟨1262480, by rfl⟩ : syracuseStep 1683307 = 2524961) B2524961
theorem B1683319 : Blo 1682041 1683319 := bstep (se 1 (by rfl) ⟨1262489, by rfl⟩ : syracuseStep 1683319 = 2524979) B2524979
theorem B1683339 : Blo 1682041 1683339 := bstep (se 1 (by rfl) ⟨1262504, by rfl⟩ : syracuseStep 1683339 = 2525009) B2525009
theorem B1683351 : Blo 1682041 1683351 := bstep (se 1 (by rfl) ⟨1262513, by rfl⟩ : syracuseStep 1683351 = 2525027) B2525027
theorem B1798039 : Blo 1682041 1798039 := bstep (se 1 (by rfl) ⟨1348529, by rfl⟩ : syracuseStep 1798039 = 2697059) B2697059
theorem B1683371 : Blo 1682041 1683371 := bstep (se 1 (by rfl) ⟨1262528, by rfl⟩ : syracuseStep 1683371 = 2525057) B2525057
theorem B28741553 : Blo 1682041 28741553 := bstep (se 2 (by rfl) ⟨10778082, by rfl⟩ : syracuseStep 28741553 = 21556165) B21556165
theorem B1683383 : Blo 1682041 1683383 := bstep (se 1 (by rfl) ⟨1262537, by rfl⟩ : syracuseStep 1683383 = 2525075) B2525075
theorem B6827969 : Blo 1682041 6827969 := bstep (se 2 (by rfl) ⟨2560488, by rfl⟩ : syracuseStep 6827969 = 5120977) B5120977
theorem B1683403 : Blo 1682041 1683403 := bstep (se 1 (by rfl) ⟨1262552, by rfl⟩ : syracuseStep 1683403 = 2525105) B2525105
theorem B3788747 : Blo 1682041 3788747 := bstep (se 1 (by rfl) ⟨2841560, by rfl⟩ : syracuseStep 3788747 = 5683121) B5683121
theorem B1683415 : Blo 1682041 1683415 := bstep (se 1 (by rfl) ⟨1262561, by rfl⟩ : syracuseStep 1683415 = 2525123) B2525123
theorem B1683435 : Blo 1682041 1683435 := bstep (se 1 (by rfl) ⟨1262576, by rfl⟩ : syracuseStep 1683435 = 2525153) B2525153
theorem B1683447 : Blo 1682041 1683447 := bstep (se 1 (by rfl) ⟨1262585, by rfl⟩ : syracuseStep 1683447 = 2525171) B2525171
theorem B3788801 : Blo 1682041 3788801 := bstep (se 2 (by rfl) ⟨1420800, by rfl⟩ : syracuseStep 3788801 = 2841601) B2841601
theorem B1683467 : Blo 1682041 1683467 := bstep (se 1 (by rfl) ⟨1262600, by rfl⟩ : syracuseStep 1683467 = 2525201) B2525201
theorem B1683479 : Blo 1682041 1683479 := bstep (se 1 (by rfl) ⟨1262609, by rfl⟩ : syracuseStep 1683479 = 2525219) B2525219
theorem B1683499 : Blo 1682041 1683499 := bstep (se 1 (by rfl) ⟨1262624, by rfl⟩ : syracuseStep 1683499 = 2525249) B2525249
theorem B1683511 : Blo 1682041 1683511 := bstep (se 1 (by rfl) ⟨1262633, by rfl⟩ : syracuseStep 1683511 = 2525267) B2525267
theorem B1683531 : Blo 1682041 1683531 := bstep (se 1 (by rfl) ⟨1262648, by rfl⟩ : syracuseStep 1683531 = 2525297) B2525297
theorem B1683543 : Blo 1682041 1683543 := bstep (se 1 (by rfl) ⟨1262657, by rfl⟩ : syracuseStep 1683543 = 2525315) B2525315
theorem B1683563 : Blo 1682041 1683563 := bstep (se 1 (by rfl) ⟨1262672, by rfl⟩ : syracuseStep 1683563 = 2525345) B2525345
theorem B1683575 : Blo 1682041 1683575 := bstep (se 1 (by rfl) ⟨1262681, by rfl⟩ : syracuseStep 1683575 = 2525363) B2525363
theorem B1683595 : Blo 1682041 1683595 := bstep (se 1 (by rfl) ⟨1262696, by rfl⟩ : syracuseStep 1683595 = 2525393) B2525393
theorem B1683607 : Blo 1682041 1683607 := bstep (se 1 (by rfl) ⟨1262705, by rfl⟩ : syracuseStep 1683607 = 2525411) B2525411
theorem B1798295 : Blo 1682041 1798295 := bstep (se 1 (by rfl) ⟨1348721, by rfl⟩ : syracuseStep 1798295 = 2697443) B2697443
theorem B1683627 : Blo 1682041 1683627 := bstep (se 1 (by rfl) ⟨1262720, by rfl⟩ : syracuseStep 1683627 = 2525441) B2525441
theorem B1683639 : Blo 1682041 1683639 := bstep (se 1 (by rfl) ⟨1262729, by rfl⟩ : syracuseStep 1683639 = 2525459) B2525459
theorem B4042955 : Blo 1682041 4042955 := bstep (se 1 (by rfl) ⟨3032216, by rfl⟩ : syracuseStep 4042955 = 6064433) B6064433
theorem B1683659 : Blo 1682041 1683659 := bstep (se 1 (by rfl) ⟨1262744, by rfl⟩ : syracuseStep 1683659 = 2525489) B2525489
theorem B1683671 : Blo 1682041 1683671 := bstep (se 1 (by rfl) ⟨1262753, by rfl⟩ : syracuseStep 1683671 = 2525507) B2525507
theorem B3789017 : Blo 1682041 3789017 := bstep (se 2 (by rfl) ⟨1420881, by rfl⟩ : syracuseStep 3789017 = 2841763) B2841763
theorem B1683691 : Blo 1682041 1683691 := bstep (se 1 (by rfl) ⟨1262768, by rfl⟩ : syracuseStep 1683691 = 2525537) B2525537
theorem B1683703 : Blo 1682041 1683703 := bstep (se 1 (by rfl) ⟨1262777, by rfl⟩ : syracuseStep 1683703 = 2525555) B2525555
theorem B1683723 : Blo 1682041 1683723 := bstep (se 1 (by rfl) ⟨1262792, by rfl⟩ : syracuseStep 1683723 = 2525585) B2525585
theorem B5755159 : Blo 1682041 5755159 := bstep (se 1 (by rfl) ⟨4316369, by rfl⟩ : syracuseStep 5755159 = 8632739) B8632739
theorem B1683735 : Blo 1682041 1683735 := bstep (se 1 (by rfl) ⟨1262801, by rfl⟩ : syracuseStep 1683735 = 2525603) B2525603
theorem B1683755 : Blo 1682041 1683755 := bstep (se 1 (by rfl) ⟨1262816, by rfl⟩ : syracuseStep 1683755 = 2525633) B2525633
theorem B1683767 : Blo 1682041 1683767 := bstep (se 1 (by rfl) ⟨1262825, by rfl⟩ : syracuseStep 1683767 = 2525651) B2525651
theorem B1683787 : Blo 1682041 1683787 := bstep (se 1 (by rfl) ⟨1262840, by rfl⟩ : syracuseStep 1683787 = 2525681) B2525681
theorem B1683799 : Blo 1682041 1683799 := bstep (se 1 (by rfl) ⟨1262849, by rfl⟩ : syracuseStep 1683799 = 2525699) B2525699
theorem B5681501 : Blo 1682041 5681501 := bstep (se 3 (by rfl) ⟨1065281, by rfl⟩ : syracuseStep 5681501 = 2130563) B2130563
theorem B1683819 : Blo 1682041 1683819 := bstep (se 1 (by rfl) ⟨1262864, by rfl⟩ : syracuseStep 1683819 = 2525729) B2525729
theorem B1683831 : Blo 1682041 1683831 := bstep (se 1 (by rfl) ⟨1262873, by rfl⟩ : syracuseStep 1683831 = 2525747) B2525747
theorem B2273675 : Blo 1682041 2273675 := bstep (se 1 (by rfl) ⟨1705256, by rfl⟩ : syracuseStep 2273675 = 3410513) B3410513
theorem B1683851 : Blo 1682041 1683851 := bstep (se 1 (by rfl) ⟨1262888, by rfl⟩ : syracuseStep 1683851 = 2525777) B2525777
theorem B6820247 : Blo 1682041 6820247 := bstep (se 1 (by rfl) ⟨5115185, by rfl⟩ : syracuseStep 6820247 = 10230371) B10230371
theorem B2838935 : Blo 1682041 2838935 := bstep (se 1 (by rfl) ⟨2129201, by rfl⟩ : syracuseStep 2838935 = 4258403) B4258403
theorem B1683863 : Blo 1682041 1683863 := bstep (se 1 (by rfl) ⟨1262897, by rfl⟩ : syracuseStep 1683863 = 2525795) B2525795
theorem B1683883 : Blo 1682041 1683883 := bstep (se 1 (by rfl) ⟨1262912, by rfl⟩ : syracuseStep 1683883 = 2525825) B2525825
theorem B1683895 : Blo 1682041 1683895 := bstep (se 1 (by rfl) ⟨1262921, by rfl⟩ : syracuseStep 1683895 = 2525843) B2525843
theorem B1683915 : Blo 1682041 1683915 := bstep (se 1 (by rfl) ⟨1262936, by rfl⟩ : syracuseStep 1683915 = 2525873) B2525873
theorem B1683927 : Blo 1682041 1683927 := bstep (se 1 (by rfl) ⟨1262945, by rfl⟩ : syracuseStep 1683927 = 2525891) B2525891
theorem B2396633 : Blo 1682041 2396633 := bstep (se 2 (by rfl) ⟨898737, by rfl⟩ : syracuseStep 2396633 = 1797475) B1797475
theorem B1683947 : Blo 1682041 1683947 := bstep (se 1 (by rfl) ⟨1262960, by rfl⟩ : syracuseStep 1683947 = 2525921) B2525921
theorem B1683959 : Blo 1682041 1683959 := bstep (se 1 (by rfl) ⟨1262969, by rfl⟩ : syracuseStep 1683959 = 2525939) B2525939
theorem B1683979 : Blo 1682041 1683979 := bstep (se 1 (by rfl) ⟨1262984, by rfl⟩ : syracuseStep 1683979 = 2525969) B2525969
theorem B2839063 : Blo 1682041 2839063 := bstep (se 1 (by rfl) ⟨2129297, by rfl⟩ : syracuseStep 2839063 = 4258595) B4258595
theorem B1683991 : Blo 1682041 1683991 := bstep (se 1 (by rfl) ⟨1262993, by rfl⟩ : syracuseStep 1683991 = 2525987) B2525987
theorem B1684011 : Blo 1682041 1684011 := bstep (se 1 (by rfl) ⟨1263008, by rfl⟩ : syracuseStep 1684011 = 2526017) B2526017
theorem B1684023 : Blo 1682041 1684023 := bstep (se 1 (by rfl) ⟨1263017, by rfl⟩ : syracuseStep 1684023 = 2526035) B2526035
theorem B2396747 : Blo 1682041 2396747 := bstep (se 1 (by rfl) ⟨1797560, by rfl⟩ : syracuseStep 2396747 = 3595121) B3595121
theorem B12784229 : Blo 1682041 12784229 := bstep (se 4 (by rfl) ⟨1198521, by rfl⟩ : syracuseStep 12784229 = 2397043) B2397043
theorem B8524439 : Blo 1682041 8524439 := bstep (se 1 (by rfl) ⟨6393329, by rfl⟩ : syracuseStep 8524439 = 12786659) B12786659
theorem B9589427 : Blo 1682041 9589427 := bstep (se 1 (by rfl) ⟨7192070, by rfl⟩ : syracuseStep 9589427 = 14384141) B14384141
theorem B7189337 : Blo 1682041 7189337 := bstep (se 2 (by rfl) ⟨2696001, by rfl⟩ : syracuseStep 7189337 = 5392003) B5392003
theorem B10777445 : Blo 1682041 10777445 := bstep (se 4 (by rfl) ⟨1010385, by rfl⟩ : syracuseStep 10777445 = 2020771) B2020771
theorem B3838835 : Blo 1682041 3838835 := bstep (se 1 (by rfl) ⟨2879126, by rfl⟩ : syracuseStep 3838835 = 5758253) B5758253
theorem B3642265 : Blo 1682041 3642265 := bstep (se 2 (by rfl) ⟨1365849, by rfl⟩ : syracuseStep 3642265 = 2731699) B2731699
theorem B12776453 : Blo 1682041 12776453 := bstep (se 4 (by rfl) ⟨1197792, by rfl⟩ : syracuseStep 12776453 = 2395585) B2395585
theorem B9098315 : Blo 1682041 9098315 := bstep (se 1 (by rfl) ⟨6823736, by rfl⟩ : syracuseStep 9098315 = 13647473) B13647473
theorem B12784715 : Blo 1682041 12784715 := bstep (se 1 (by rfl) ⟨9588536, by rfl⟩ : syracuseStep 12784715 = 19177073) B19177073
theorem B2397271 : Blo 1682041 2397271 := bstep (se 1 (by rfl) ⟨1797953, by rfl⟩ : syracuseStep 2397271 = 3595907) B3595907
theorem B5755997 : Blo 1682041 5755997 := bstep (se 3 (by rfl) ⟨1079249, by rfl⟩ : syracuseStep 5755997 = 2158499) B2158499
theorem B2839691 : Blo 1682041 2839691 := bstep (se 1 (by rfl) ⟨2129768, by rfl⟩ : syracuseStep 2839691 = 4259537) B4259537
theorem B2733259 : Blo 1682041 2733259 := bstep (se 1 (by rfl) ⟨2049944, by rfl⟩ : syracuseStep 2733259 = 4099889) B4099889
theorem B8516825 : Blo 1682041 8516825 := bstep (se 2 (by rfl) ⟨3193809, by rfl⟩ : syracuseStep 8516825 = 6387619) B6387619
theorem B12129497 : Blo 1682041 12129497 := bstep (se 2 (by rfl) ⟨4548561, by rfl⟩ : syracuseStep 12129497 = 9097123) B9097123
theorem B2839819 : Blo 1682041 2839819 := bstep (se 1 (by rfl) ⟨2129864, by rfl⟩ : syracuseStep 2839819 = 4259729) B4259729
theorem B10777931 : Blo 1682041 10777931 := bstep (se 1 (by rfl) ⟨8083448, by rfl⟩ : syracuseStep 10777931 = 16166897) B16166897
theorem B3413335 : Blo 1682041 3413335 := bstep (se 1 (by rfl) ⟨2560001, by rfl⟩ : syracuseStep 3413335 = 5120003) B5120003
theorem B2839961 : Blo 1682041 2839961 := bstep (se 2 (by rfl) ⟨1064985, by rfl⟩ : syracuseStep 2839961 = 2129971) B2129971
theorem B2430361 : Blo 1682041 2430361 := bstep (se 2 (by rfl) ⟨911385, by rfl⟩ : syracuseStep 2430361 = 1822771) B1822771
theorem B3593651 : Blo 1682041 3593651 := bstep (se 1 (by rfl) ⟨2695238, by rfl⟩ : syracuseStep 3593651 = 5390477) B5390477
theorem B5682635 : Blo 1682041 5682635 := bstep (se 1 (by rfl) ⟨4261976, by rfl⟩ : syracuseStep 5682635 = 8523953) B8523953
theorem B3413515 : Blo 1682041 3413515 := bstep (se 1 (by rfl) ⟨2560136, by rfl⟩ : syracuseStep 3413515 = 5120273) B5120273
theorem B2840089 : Blo 1682041 2840089 := bstep (se 2 (by rfl) ⟨1065033, by rfl⟩ : syracuseStep 2840089 = 2130067) B2130067
theorem B14571139 : Blo 1682041 14571139 := bstep (se 1 (by rfl) ⟨10928354, by rfl⟩ : syracuseStep 14571139 = 21856709) B21856709
theorem B5682905 : Blo 1682041 5682905 := bstep (se 2 (by rfl) ⟨2131089, by rfl⟩ : syracuseStep 5682905 = 4262179) B4262179
theorem B3839819 : Blo 1682041 3839819 := bstep (se 1 (by rfl) ⟨2879864, by rfl⟩ : syracuseStep 3839819 = 5759729) B5759729
theorem B31561589 : Blo 1682041 31561589 := bstep (se 5 (by rfl) ⟨1479449, by rfl⟩ : syracuseStep 31561589 = 2958899) B2958899
theorem B8091713 : Blo 1682041 8091713 := bstep (se 2 (by rfl) ⟨3034392, by rfl⟩ : syracuseStep 8091713 = 6068785) B6068785
theorem B30693451 : Blo 1682041 30693451 := bstep (se 1 (by rfl) ⟨23020088, by rfl⟩ : syracuseStep 30693451 = 46040177) B46040177
theorem B2840663 : Blo 1682041 2840663 := bstep (se 1 (by rfl) ⟨2130497, by rfl⟩ : syracuseStep 2840663 = 4260995) B4260995
theorem B9590885 : Blo 1682041 9590885 := bstep (se 4 (by rfl) ⟨899145, by rfl⟩ : syracuseStep 9590885 = 1798291) B1798291
theorem B40941719 : Blo 1682041 40941719 := bstep (se 1 (by rfl) ⟨30706289, by rfl⟩ : syracuseStep 40941719 = 61412579) B61412579
theorem B4790465 : Blo 1682041 4790465 := bstep (se 2 (by rfl) ⟨1796424, by rfl⟩ : syracuseStep 4790465 = 3592849) B3592849
theorem B2840791 : Blo 1682041 2840791 := bstep (se 1 (by rfl) ⟨2130593, by rfl⟩ : syracuseStep 2840791 = 4261187) B4261187
theorem B4045079 : Blo 1682041 4045079 := bstep (se 1 (by rfl) ⟨3033809, by rfl⟩ : syracuseStep 4045079 = 6067619) B6067619
theorem B5683607 : Blo 1682041 5683607 := bstep (se 1 (by rfl) ⟨4262705, by rfl⟩ : syracuseStep 5683607 = 8525411) B8525411
theorem B4258241 : Blo 1682041 4258241 := bstep (se 2 (by rfl) ⟨1596840, by rfl⟩ : syracuseStep 4258241 = 3193681) B3193681
theorem B7190977 : Blo 1682041 7190977 := bstep (se 2 (by rfl) ⟨2696616, by rfl⟩ : syracuseStep 7190977 = 5393233) B5393233
theorem B12958157 : Blo 1682041 12958157 := bstep (se 3 (by rfl) ⟨2429654, by rfl⟩ : syracuseStep 12958157 = 4859309) B4859309
theorem B5388761 : Blo 1682041 5388761 := bstep (se 2 (by rfl) ⟨2020785, by rfl⟩ : syracuseStep 5388761 = 4041571) B4041571
theorem B13834757 : Blo 1682041 13834757 := bstep (se 4 (by rfl) ⟨1297008, by rfl⟩ : syracuseStep 13834757 = 2594017) B2594017
theorem B7674385 : Blo 1682041 7674385 := bstep (se 2 (by rfl) ⟨2877894, by rfl⟩ : syracuseStep 7674385 = 5755789) B5755789
theorem B15358481 : Blo 1682041 15358481 := bstep (se 2 (by rfl) ⟨5759430, by rfl⟩ : syracuseStep 15358481 = 11518861) B11518861
theorem B3840587 : Blo 1682041 3840587 := bstep (se 1 (by rfl) ⟨2880440, by rfl⟩ : syracuseStep 3840587 = 5760881) B5760881
theorem B5388889 : Blo 1682041 5388889 := bstep (se 2 (by rfl) ⟨2020833, by rfl⟩ : syracuseStep 5388889 = 4041667) B4041667
theorem B3283571 : Blo 1682041 3283571 := bstep (se 1 (by rfl) ⟨2462678, by rfl⟩ : syracuseStep 3283571 = 4925357) B4925357
theorem B8518445 : Blo 1682041 8518445 := bstep (se 3 (by rfl) ⟨1597208, by rfl⟩ : syracuseStep 8518445 = 3194417) B3194417
theorem B2841419 : Blo 1682041 2841419 := bstep (se 1 (by rfl) ⟨2131064, by rfl⟩ : syracuseStep 2841419 = 4262129) B4262129
theorem B5389145 : Blo 1682041 5389145 := bstep (se 2 (by rfl) ⟨2020929, by rfl⟩ : syracuseStep 5389145 = 4041859) B4041859
theorem B2841547 : Blo 1682041 2841547 := bstep (se 1 (by rfl) ⟨2131160, by rfl⟩ : syracuseStep 2841547 = 4262321) B4262321
theorem B3595223 : Blo 1682041 3595223 := bstep (se 1 (by rfl) ⟨2696417, by rfl⟩ : syracuseStep 3595223 = 5392835) B5392835
theorem B4258777 : Blo 1682041 4258777 := bstep (se 2 (by rfl) ⟨1597041, by rfl⟩ : syracuseStep 4258777 = 3194083) B3194083
theorem B7191575 : Blo 1682041 7191575 := bstep (se 1 (by rfl) ⟨5393681, by rfl⟩ : syracuseStep 7191575 = 10787363) B10787363
theorem B3193931 : Blo 1682041 3193931 := bstep (se 1 (by rfl) ⟨2395448, by rfl⟩ : syracuseStep 3193931 = 4790897) B4790897
theorem B2841689 : Blo 1682041 2841689 := bstep (se 2 (by rfl) ⟨1065633, by rfl⟩ : syracuseStep 2841689 = 2131267) B2131267
theorem B3193985 : Blo 1682041 3193985 := bstep (se 2 (by rfl) ⟨1197744, by rfl⟩ : syracuseStep 3193985 = 2395489) B2395489
theorem B2841817 : Blo 1682041 2841817 := bstep (se 2 (by rfl) ⟨1065681, by rfl⟩ : syracuseStep 2841817 = 2131363) B2131363
theorem B3595531 : Blo 1682041 3595531 := bstep (se 1 (by rfl) ⟨2696648, by rfl⟩ : syracuseStep 3595531 = 5393297) B5393297
theorem B2022679 : Blo 1682041 2022679 := bstep (se 1 (by rfl) ⟨1517009, by rfl⟩ : syracuseStep 2022679 = 3034019) B3034019
theorem B12778883 : Blo 1682041 12778883 := bstep (se 1 (by rfl) ⟨9584162, by rfl⟩ : syracuseStep 12778883 = 19168325) B19168325
theorem B3284363 : Blo 1682041 3284363 := bstep (se 1 (by rfl) ⟨2463272, by rfl⟩ : syracuseStep 3284363 = 4926545) B4926545
theorem B6823361 : Blo 1682041 6823361 := bstep (se 2 (by rfl) ⟨2558760, by rfl⟩ : syracuseStep 6823361 = 5117521) B5117521
theorem B2129419 : Blo 1682041 2129419 := bstep (se 1 (by rfl) ⟨1597064, by rfl⟩ : syracuseStep 2129419 = 3194129) B3194129
theorem B9584345 : Blo 1682041 9584345 := bstep (se 2 (by rfl) ⟨3594129, by rfl⟩ : syracuseStep 9584345 = 7188259) B7188259
theorem B6389549 : Blo 1682041 6389549 := bstep (se 3 (by rfl) ⟨1198040, by rfl⟩ : syracuseStep 6389549 = 2396081) B2396081
theorem B25902965 : Blo 1682041 25902965 := bstep (se 5 (by rfl) ⟨1214201, by rfl⟩ : syracuseStep 25902965 = 2428403) B2428403
theorem B1892299 : Blo 1682041 1892299 := bstep (se 1 (by rfl) ⟨1419224, by rfl⟩ : syracuseStep 1892299 = 2838449) B2838449
theorem B2523083 : Blo 1682041 2523083 := bstep (se 1 (by rfl) ⟨1892312, by rfl⟩ : syracuseStep 2523083 = 3784625) B3784625
theorem B2523095 : Blo 1682041 2523095 := bstep (se 1 (by rfl) ⟨1892321, by rfl⟩ : syracuseStep 2523095 = 3784643) B3784643
theorem B2523143 : Blo 1682041 2523143 := bstep (se 1 (by rfl) ⟨1892357, by rfl⟩ : syracuseStep 2523143 = 3784715) B3784715
theorem B2523179 : Blo 1682041 2523179 := bstep (se 1 (by rfl) ⟨1892384, by rfl⟩ : syracuseStep 2523179 = 3784769) B3784769
theorem B8519741 : Blo 1682041 8519741 := bstep (se 3 (by rfl) ⟨1597451, by rfl⟩ : syracuseStep 8519741 = 3194903) B3194903
theorem B2523209 : Blo 1682041 2523209 := bstep (se 2 (by rfl) ⟨946203, by rfl⟩ : syracuseStep 2523209 = 1892407) B1892407
theorem B3784823 : Blo 1682041 3784823 := bstep (se 1 (by rfl) ⟨2838617, by rfl⟩ : syracuseStep 3784823 = 5677235) B5677235
theorem B2695303 : Blo 1682041 2695303 := bstep (se 1 (by rfl) ⟨2021477, by rfl⟩ : syracuseStep 2695303 = 4042955) B4042955
theorem B24256685 : Blo 1682041 24256685 := bstep (se 3 (by rfl) ⟨4548128, by rfl⟩ : syracuseStep 24256685 = 9096257) B9096257
theorem B2523323 : Blo 1682041 2523323 := bstep (se 1 (by rfl) ⟨1892492, by rfl⟩ : syracuseStep 2523323 = 3784985) B3784985
theorem B2523383 : Blo 1682041 2523383 := bstep (se 1 (by rfl) ⟨1892537, by rfl⟩ : syracuseStep 2523383 = 3785075) B3785075
theorem B2523407 : Blo 1682041 2523407 := bstep (se 1 (by rfl) ⟨1892555, by rfl⟩ : syracuseStep 2523407 = 3785111) B3785111
theorem B1892623 : Blo 1682041 1892623 := bstep (se 1 (by rfl) ⟨1419467, by rfl⟩ : syracuseStep 1892623 = 2838935) B2838935
theorem B6390049 : Blo 1682041 6390049 := bstep (se 2 (by rfl) ⟨2396268, by rfl⟩ : syracuseStep 6390049 = 4792537) B4792537
theorem B3785003 : Blo 1682041 3785003 := bstep (se 1 (by rfl) ⟨2838752, by rfl⟩ : syracuseStep 3785003 = 5677505) B5677505
theorem B2523449 : Blo 1682041 2523449 := bstep (se 2 (by rfl) ⟨946293, by rfl⟩ : syracuseStep 2523449 = 1892587) B1892587
theorem B9093491 : Blo 1682041 9093491 := bstep (se 1 (by rfl) ⟨6820118, by rfl⟩ : syracuseStep 9093491 = 13640237) B13640237
theorem B4260215 : Blo 1682041 4260215 := bstep (se 1 (by rfl) ⟨3195161, by rfl⟩ : syracuseStep 4260215 = 6390323) B6390323
theorem B2130295 : Blo 1682041 2130295 := bstep (se 1 (by rfl) ⟨1597721, by rfl⟩ : syracuseStep 2130295 = 3195443) B3195443
theorem B2523527 : Blo 1682041 2523527 := bstep (se 1 (by rfl) ⟨1892645, by rfl⟩ : syracuseStep 2523527 = 3785291) B3785291
theorem B3195283 : Blo 1682041 3195283 := bstep (se 1 (by rfl) ⟨2396462, by rfl⟩ : syracuseStep 3195283 = 4792925) B4792925
theorem B2523563 : Blo 1682041 2523563 := bstep (se 1 (by rfl) ⟨1892672, by rfl⟩ : syracuseStep 2523563 = 3785345) B3785345
theorem B2523593 : Blo 1682041 2523593 := bstep (se 2 (by rfl) ⟨946347, by rfl⟩ : syracuseStep 2523593 = 1892695) B1892695
theorem B2523707 : Blo 1682041 2523707 := bstep (se 1 (by rfl) ⟨1892780, by rfl⟩ : syracuseStep 2523707 = 3785561) B3785561
theorem B4792891 : Blo 1682041 4792891 := bstep (se 1 (by rfl) ⟨3594668, by rfl⟩ : syracuseStep 4792891 = 7189337) B7189337
theorem B7184963 : Blo 1682041 7184963 := bstep (se 1 (by rfl) ⟨5388722, by rfl⟩ : syracuseStep 7184963 = 10777445) B10777445
theorem B2523767 : Blo 1682041 2523767 := bstep (se 1 (by rfl) ⟨1892825, by rfl⟩ : syracuseStep 2523767 = 3785651) B3785651
theorem B2523791 : Blo 1682041 2523791 := bstep (se 1 (by rfl) ⟨1892843, by rfl⟩ : syracuseStep 2523791 = 3785687) B3785687
theorem B3785363 : Blo 1682041 3785363 := bstep (se 1 (by rfl) ⟨2839022, by rfl⟩ : syracuseStep 3785363 = 5678045) B5678045
theorem B2523833 : Blo 1682041 2523833 := bstep (se 2 (by rfl) ⟨946437, by rfl⟩ : syracuseStep 2523833 = 1892875) B1892875
theorem B2130619 : Blo 1682041 2130619 := bstep (se 1 (by rfl) ⟨1597964, by rfl⟩ : syracuseStep 2130619 = 3195929) B3195929
theorem B10232513 : Blo 1682041 10232513 := bstep (se 2 (by rfl) ⟨3837192, by rfl⟩ : syracuseStep 10232513 = 7674385) B7674385
theorem B3785417 : Blo 1682041 3785417 := bstep (se 2 (by rfl) ⟨1419531, by rfl⟩ : syracuseStep 3785417 = 2839063) B2839063
theorem B2523911 : Blo 1682041 2523911 := bstep (se 1 (by rfl) ⟨1892933, by rfl⟩ : syracuseStep 2523911 = 3785867) B3785867
theorem B1893127 : Blo 1682041 1893127 := bstep (se 1 (by rfl) ⟨1419845, by rfl⟩ : syracuseStep 1893127 = 2839691) B2839691
theorem B7185185 : Blo 1682041 7185185 := bstep (se 2 (by rfl) ⟨2694444, by rfl⟩ : syracuseStep 7185185 = 5388889) B5388889
theorem B2523947 : Blo 1682041 2523947 := bstep (se 1 (by rfl) ⟨1892960, by rfl⟩ : syracuseStep 2523947 = 3785921) B3785921
theorem B5677883 : Blo 1682041 5677883 := bstep (se 1 (by rfl) ⟨4258412, by rfl⟩ : syracuseStep 5677883 = 8516825) B8516825
theorem B8086331 : Blo 1682041 8086331 := bstep (se 1 (by rfl) ⟨6064748, by rfl⟩ : syracuseStep 8086331 = 12129497) B12129497
theorem B2523977 : Blo 1682041 2523977 := bstep (se 2 (by rfl) ⟨946491, by rfl⟩ : syracuseStep 2523977 = 1892983) B1892983
theorem B7185287 : Blo 1682041 7185287 := bstep (se 1 (by rfl) ⟨5388965, by rfl⟩ : syracuseStep 7185287 = 10777931) B10777931
theorem B2524091 : Blo 1682041 2524091 := bstep (se 1 (by rfl) ⟨1893068, by rfl⟩ : syracuseStep 2524091 = 3786137) B3786137
theorem B1893307 : Blo 1682041 1893307 := bstep (se 1 (by rfl) ⟨1419980, by rfl⟩ : syracuseStep 1893307 = 2839961) B2839961
theorem B2524151 : Blo 1682041 2524151 := bstep (se 1 (by rfl) ⟨1893113, by rfl⟩ : syracuseStep 2524151 = 3786227) B3786227
theorem B2524175 : Blo 1682041 2524175 := bstep (se 1 (by rfl) ⟨1893131, by rfl⟩ : syracuseStep 2524175 = 3786263) B3786263
theorem B2524217 : Blo 1682041 2524217 := bstep (se 2 (by rfl) ⟨946581, by rfl⟩ : syracuseStep 2524217 = 1893163) B1893163
theorem B18187325 : Blo 1682041 18187325 := bstep (se 3 (by rfl) ⟨3410123, by rfl⟩ : syracuseStep 18187325 = 6820247) B6820247
theorem B2524295 : Blo 1682041 2524295 := bstep (se 1 (by rfl) ⟨1893221, by rfl⟩ : syracuseStep 2524295 = 3786443) B3786443
theorem B2524331 : Blo 1682041 2524331 := bstep (se 1 (by rfl) ⟨1893248, by rfl⟩ : syracuseStep 2524331 = 3786497) B3786497
theorem B2524361 : Blo 1682041 2524361 := bstep (se 2 (by rfl) ⟨946635, by rfl⟩ : syracuseStep 2524361 = 1893271) B1893271
theorem B34555085 : Blo 1682041 34555085 := bstep (se 3 (by rfl) ⟨6479078, by rfl⟩ : syracuseStep 34555085 = 12958157) B12958157
theorem B6391021 : Blo 1682041 6391021 := bstep (se 3 (by rfl) ⟨1198316, by rfl⟩ : syracuseStep 6391021 = 2396633) B2396633
theorem B5678369 : Blo 1682041 5678369 := bstep (se 2 (by rfl) ⟨2129388, by rfl⟩ : syracuseStep 5678369 = 4258777) B4258777
theorem B2524475 : Blo 1682041 2524475 := bstep (se 1 (by rfl) ⟨1893356, by rfl⟩ : syracuseStep 2524475 = 3786713) B3786713
theorem B4261207 : Blo 1682041 4261207 := bstep (se 1 (by rfl) ⟨3195905, by rfl⟩ : syracuseStep 4261207 = 6391811) B6391811
theorem B2524535 : Blo 1682041 2524535 := bstep (se 1 (by rfl) ⟨1893401, by rfl⟩ : syracuseStep 2524535 = 3786803) B3786803
theorem B3786119 : Blo 1682041 3786119 := bstep (se 1 (by rfl) ⟨2839589, by rfl⟩ : syracuseStep 3786119 = 5679179) B5679179
theorem B2524559 : Blo 1682041 2524559 := bstep (se 1 (by rfl) ⟨1893419, by rfl⟩ : syracuseStep 2524559 = 3786839) B3786839
theorem B1893775 : Blo 1682041 1893775 := bstep (se 1 (by rfl) ⟨1420331, by rfl⟩ : syracuseStep 1893775 = 2840663) B2840663
theorem B2524601 : Blo 1682041 2524601 := bstep (se 2 (by rfl) ⟨946725, by rfl⟩ : syracuseStep 2524601 = 1893451) B1893451
theorem B3196361 : Blo 1682041 3196361 := bstep (se 2 (by rfl) ⟨1198635, by rfl⟩ : syracuseStep 3196361 = 2397271) B2397271
theorem B2524679 : Blo 1682041 2524679 := bstep (se 1 (by rfl) ⟨1893509, by rfl⟩ : syracuseStep 2524679 = 3787019) B3787019
theorem B6391325 : Blo 1682041 6391325 := bstep (se 3 (by rfl) ⟨1198373, by rfl⟩ : syracuseStep 6391325 = 2396747) B2396747
theorem B2524715 : Blo 1682041 2524715 := bstep (se 1 (by rfl) ⟨1893536, by rfl⟩ : syracuseStep 2524715 = 3787073) B3787073
theorem B3786299 : Blo 1682041 3786299 := bstep (se 1 (by rfl) ⟨2839724, by rfl⟩ : syracuseStep 3786299 = 5679449) B5679449
theorem B3032635 : Blo 1682041 3032635 := bstep (se 1 (by rfl) ⟨2274476, by rfl⟩ : syracuseStep 3032635 = 4548953) B4548953
theorem B2524745 : Blo 1682041 2524745 := bstep (se 2 (by rfl) ⟨946779, by rfl⟩ : syracuseStep 2524745 = 1893559) B1893559
theorem B4261511 : Blo 1682041 4261511 := bstep (se 1 (by rfl) ⟨3196133, by rfl⟩ : syracuseStep 4261511 = 6392267) B6392267
theorem B3786425 : Blo 1682041 3786425 := bstep (se 2 (by rfl) ⟨1419909, by rfl⟩ : syracuseStep 3786425 = 2839819) B2839819
theorem B4794041 : Blo 1682041 4794041 := bstep (se 2 (by rfl) ⟨1797765, by rfl⟩ : syracuseStep 4794041 = 3595531) B3595531
theorem B2524859 : Blo 1682041 2524859 := bstep (se 1 (by rfl) ⟨1893644, by rfl⟩ : syracuseStep 2524859 = 3787289) B3787289
theorem B2696905 : Blo 1682041 2696905 := bstep (se 2 (by rfl) ⟨1011339, by rfl⟩ : syracuseStep 2696905 = 2022679) B2022679
theorem B2524919 : Blo 1682041 2524919 := bstep (se 1 (by rfl) ⟨1893689, by rfl⟩ : syracuseStep 2524919 = 3787379) B3787379
theorem B2189047 : Blo 1682041 2189047 := bstep (se 1 (by rfl) ⟨1641785, by rfl⟩ : syracuseStep 2189047 = 3283571) B3283571
theorem B23029505 : Blo 1682041 23029505 := bstep (se 2 (by rfl) ⟨8636064, by rfl⟩ : syracuseStep 23029505 = 17272129) B17272129
theorem B12781313 : Blo 1682041 12781313 := bstep (se 2 (by rfl) ⟨4792992, by rfl⟩ : syracuseStep 12781313 = 9585985) B9585985
theorem B4261643 : Blo 1682041 4261643 := bstep (se 1 (by rfl) ⟨3196232, by rfl⟩ : syracuseStep 4261643 = 6392465) B6392465
theorem B17499919 : Blo 1682041 17499919 := bstep (se 1 (by rfl) ⟨13124939, by rfl⟩ : syracuseStep 17499919 = 26249879) B26249879
theorem B2524943 : Blo 1682041 2524943 := bstep (se 1 (by rfl) ⟨1893707, by rfl⟩ : syracuseStep 2524943 = 3787415) B3787415
theorem B8521523 : Blo 1682041 8521523 := bstep (se 1 (by rfl) ⟨6391142, by rfl⟩ : syracuseStep 8521523 = 12782285) B12782285
theorem B2524985 : Blo 1682041 2524985 := bstep (se 2 (by rfl) ⟨946869, by rfl⟩ : syracuseStep 2524985 = 1893739) B1893739
theorem B28772171 : Blo 1682041 28772171 := bstep (se 1 (by rfl) ⟨21579128, by rfl⟩ : syracuseStep 28772171 = 43158257) B43158257
theorem B5678963 : Blo 1682041 5678963 := bstep (se 1 (by rfl) ⟨4259222, by rfl⟩ : syracuseStep 5678963 = 8518445) B8518445
theorem B2525063 : Blo 1682041 2525063 := bstep (se 1 (by rfl) ⟨1893797, by rfl⟩ : syracuseStep 2525063 = 3787595) B3787595
theorem B1894279 : Blo 1682041 1894279 := bstep (se 1 (by rfl) ⟨1420709, by rfl⟩ : syracuseStep 1894279 = 2841419) B2841419
theorem B2525099 : Blo 1682041 2525099 := bstep (se 1 (by rfl) ⟨1893824, by rfl⟩ : syracuseStep 2525099 = 3787649) B3787649
theorem B2525129 : Blo 1682041 2525129 := bstep (se 2 (by rfl) ⟨946923, by rfl⟩ : syracuseStep 2525129 = 1893847) B1893847
theorem B3786767 : Blo 1682041 3786767 := bstep (se 1 (by rfl) ⟨2840075, by rfl⟩ : syracuseStep 3786767 = 5680151) B5680151
theorem B4794383 : Blo 1682041 4794383 := bstep (se 1 (by rfl) ⟨3595787, by rfl⟩ : syracuseStep 4794383 = 7191575) B7191575
theorem B3786785 : Blo 1682041 3786785 := bstep (se 2 (by rfl) ⟨1420044, by rfl⟩ : syracuseStep 3786785 = 2840089) B2840089
theorem B2525243 : Blo 1682041 2525243 := bstep (se 1 (by rfl) ⟨1893932, by rfl⟩ : syracuseStep 2525243 = 3787865) B3787865
theorem B1894459 : Blo 1682041 1894459 := bstep (se 1 (by rfl) ⟨1420844, by rfl⟩ : syracuseStep 1894459 = 2841689) B2841689
theorem B20473973 : Blo 1682041 20473973 := bstep (se 5 (by rfl) ⟨959717, by rfl⟩ : syracuseStep 20473973 = 1919435) B1919435
theorem B8521847 : Blo 1682041 8521847 := bstep (se 1 (by rfl) ⟨6391385, by rfl⟩ : syracuseStep 8521847 = 12782771) B12782771
theorem B2525303 : Blo 1682041 2525303 := bstep (se 1 (by rfl) ⟨1893977, by rfl⟩ : syracuseStep 2525303 = 3787955) B3787955
theorem B19425413 : Blo 1682041 19425413 := bstep (se 4 (by rfl) ⟨1821132, by rfl⟩ : syracuseStep 19425413 = 3642265) B3642265
theorem B2525327 : Blo 1682041 2525327 := bstep (se 1 (by rfl) ⟨1893995, by rfl⟩ : syracuseStep 2525327 = 3787991) B3787991
theorem B2558123 : Blo 1682041 2558123 := bstep (se 1 (by rfl) ⟨1918592, by rfl⟩ : syracuseStep 2558123 = 3837185) B3837185
theorem B2525369 : Blo 1682041 2525369 := bstep (se 2 (by rfl) ⟨947013, by rfl⟩ : syracuseStep 2525369 = 1894027) B1894027
theorem B2525447 : Blo 1682041 2525447 := bstep (se 1 (by rfl) ⟨1894085, by rfl⟩ : syracuseStep 2525447 = 3788171) B3788171
theorem B2189575 : Blo 1682041 2189575 := bstep (se 1 (by rfl) ⟨1642181, by rfl⟩ : syracuseStep 2189575 = 3284363) B3284363
theorem B4262159 : Blo 1682041 4262159 := bstep (se 1 (by rfl) ⟨3196619, by rfl⟩ : syracuseStep 4262159 = 6393239) B6393239
theorem B4548907 : Blo 1682041 4548907 := bstep (se 1 (by rfl) ⟨3411680, by rfl⟩ : syracuseStep 4548907 = 6823361) B6823361
theorem B2525483 : Blo 1682041 2525483 := bstep (se 1 (by rfl) ⟨1894112, by rfl⟩ : syracuseStep 2525483 = 3788225) B3788225
theorem B2525513 : Blo 1682041 2525513 := bstep (se 2 (by rfl) ⟨947067, by rfl⟩ : syracuseStep 2525513 = 1894135) B1894135
theorem B3787127 : Blo 1682041 3787127 := bstep (se 1 (by rfl) ⟨2840345, by rfl⟩ : syracuseStep 3787127 = 5680691) B5680691
theorem B3410311 : Blo 1682041 3410311 := bstep (se 1 (by rfl) ⟨2557733, by rfl⟩ : syracuseStep 3410311 = 5115467) B5115467
theorem B4262291 : Blo 1682041 4262291 := bstep (se 1 (by rfl) ⟨3196718, by rfl⟩ : syracuseStep 4262291 = 6393437) B6393437
theorem B2525627 : Blo 1682041 2525627 := bstep (se 1 (by rfl) ⟨1894220, by rfl⟩ : syracuseStep 2525627 = 3788441) B3788441
theorem B2525687 : Blo 1682041 2525687 := bstep (se 1 (by rfl) ⟨1894265, by rfl⟩ : syracuseStep 2525687 = 3788531) B3788531
theorem B2525711 : Blo 1682041 2525711 := bstep (se 1 (by rfl) ⟨1894283, by rfl⟩ : syracuseStep 2525711 = 3788567) B3788567
theorem B3787307 : Blo 1682041 3787307 := bstep (se 1 (by rfl) ⟨2840480, by rfl⟩ : syracuseStep 3787307 = 5680961) B5680961
theorem B2525753 : Blo 1682041 2525753 := bstep (se 2 (by rfl) ⟨947157, by rfl⟩ : syracuseStep 2525753 = 1894315) B1894315
theorem B9587261 : Blo 1682041 9587261 := bstep (se 3 (by rfl) ⟨1797611, by rfl⟩ : syracuseStep 9587261 = 3595223) B3595223
theorem B1682055 : Blo 1682041 1682055 := bstep (se 1 (by rfl) ⟨1261541, by rfl⟩ : syracuseStep 1682055 = 2523083) B2523083
theorem B2525831 : Blo 1682041 2525831 := bstep (se 1 (by rfl) ⟨1894373, by rfl⟩ : syracuseStep 2525831 = 3788747) B3788747
theorem B1682063 : Blo 1682041 1682063 := bstep (se 1 (by rfl) ⟨1261547, by rfl⟩ : syracuseStep 1682063 = 2523095) B2523095
theorem B2525867 : Blo 1682041 2525867 := bstep (se 1 (by rfl) ⟨1894400, by rfl⟩ : syracuseStep 2525867 = 3788801) B3788801
theorem B1682107 : Blo 1682041 1682107 := bstep (se 1 (by rfl) ⟨1261580, by rfl⟩ : syracuseStep 1682107 = 2523161) B2523161
theorem B2525897 : Blo 1682041 2525897 := bstep (se 2 (by rfl) ⟨947211, by rfl⟩ : syracuseStep 2525897 = 1894423) B1894423
theorem B7187201 : Blo 1682041 7187201 := bstep (se 2 (by rfl) ⟨2695200, by rfl⟩ : syracuseStep 7187201 = 5390401) B5390401
theorem B1682183 : Blo 1682041 1682183 := bstep (se 1 (by rfl) ⟨1261637, by rfl⟩ : syracuseStep 1682183 = 2523275) B2523275
theorem B1682191 : Blo 1682041 1682191 := bstep (se 1 (by rfl) ⟨1261643, by rfl⟩ : syracuseStep 1682191 = 2523287) B2523287
theorem B1682235 : Blo 1682041 1682235 := bstep (se 1 (by rfl) ⟨1261676, by rfl⟩ : syracuseStep 1682235 = 2523353) B2523353
theorem B2526011 : Blo 1682041 2526011 := bstep (se 1 (by rfl) ⟨1894508, by rfl⟩ : syracuseStep 2526011 = 3789017) B3789017
theorem B1682311 : Blo 1682041 1682311 := bstep (se 1 (by rfl) ⟨1261733, by rfl⟩ : syracuseStep 1682311 = 2523467) B2523467
theorem B4795271 : Blo 1682041 4795271 := bstep (se 1 (by rfl) ⟨3596453, by rfl⟩ : syracuseStep 4795271 = 7192907) B7192907
theorem B1682319 : Blo 1682041 1682319 := bstep (se 1 (by rfl) ⟨1261739, by rfl⟩ : syracuseStep 1682319 = 2523479) B2523479
theorem B3787667 : Blo 1682041 3787667 := bstep (se 1 (by rfl) ⟨2840750, by rfl⟩ : syracuseStep 3787667 = 5681501) B5681501
theorem B1682363 : Blo 1682041 1682363 := bstep (se 1 (by rfl) ⟨1261772, by rfl⟩ : syracuseStep 1682363 = 2523545) B2523545
theorem B3787721 : Blo 1682041 3787721 := bstep (se 2 (by rfl) ⟨1420395, by rfl⟩ : syracuseStep 3787721 = 2840791) B2840791
theorem B1682439 : Blo 1682041 1682439 := bstep (se 1 (by rfl) ⟨1261829, by rfl⟩ : syracuseStep 1682439 = 2523659) B2523659
theorem B4041743 : Blo 1682041 4041743 := bstep (se 1 (by rfl) ⟨3031307, by rfl⟩ : syracuseStep 4041743 = 6062615) B6062615
theorem B1682447 : Blo 1682041 1682447 := bstep (se 1 (by rfl) ⟨1261835, by rfl⟩ : syracuseStep 1682447 = 2523671) B2523671
theorem B621849635 : Blo 1682041 621849635 := bstep (se 1 (by rfl) ⟨466387226, by rfl⟩ : syracuseStep 621849635 = 932774453) B932774453
theorem B1682491 : Blo 1682041 1682491 := bstep (se 1 (by rfl) ⟨1261868, by rfl⟩ : syracuseStep 1682491 = 2523737) B2523737
theorem B4795453 : Blo 1682041 4795453 := bstep (se 3 (by rfl) ⟨899147, by rfl⟩ : syracuseStep 4795453 = 1798295) B1798295
theorem B8522819 : Blo 1682041 8522819 := bstep (se 1 (by rfl) ⟨6392114, by rfl⟩ : syracuseStep 8522819 = 12784229) B12784229
theorem B6392951 : Blo 1682041 6392951 := bstep (se 1 (by rfl) ⟨4794713, by rfl⟩ : syracuseStep 6392951 = 9589427) B9589427
theorem B1682567 : Blo 1682041 1682567 := bstep (se 1 (by rfl) ⟨1261925, by rfl⟩ : syracuseStep 1682567 = 2523851) B2523851
theorem B1682575 : Blo 1682041 1682575 := bstep (se 1 (by rfl) ⟨1261931, by rfl⟩ : syracuseStep 1682575 = 2523863) B2523863
theorem B1682619 : Blo 1682041 1682619 := bstep (se 1 (by rfl) ⟨1261964, by rfl⟩ : syracuseStep 1682619 = 2523929) B2523929
theorem B2559223 : Blo 1682041 2559223 := bstep (se 1 (by rfl) ⟨1919417, by rfl⟩ : syracuseStep 2559223 = 3838835) B3838835
theorem B9587969 : Blo 1682041 9587969 := bstep (se 2 (by rfl) ⟨3595488, by rfl⟩ : syracuseStep 9587969 = 7190977) B7190977
theorem B1682695 : Blo 1682041 1682695 := bstep (se 1 (by rfl) ⟨1262021, by rfl⟩ : syracuseStep 1682695 = 2524043) B2524043
theorem B1682703 : Blo 1682041 1682703 := bstep (se 1 (by rfl) ⟨1262027, by rfl⟩ : syracuseStep 1682703 = 2524055) B2524055
theorem B1682747 : Blo 1682041 1682747 := bstep (se 1 (by rfl) ⟨1262060, by rfl⟩ : syracuseStep 1682747 = 2524121) B2524121
theorem B1682823 : Blo 1682041 1682823 := bstep (se 1 (by rfl) ⟨1262117, by rfl⟩ : syracuseStep 1682823 = 2524235) B2524235
theorem B6065543 : Blo 1682041 6065543 := bstep (se 1 (by rfl) ⟨4549157, by rfl⟩ : syracuseStep 6065543 = 9098315) B9098315
theorem B4550023 : Blo 1682041 4550023 := bstep (se 1 (by rfl) ⟨3412517, by rfl⟩ : syracuseStep 4550023 = 6825035) B6825035
theorem B8523143 : Blo 1682041 8523143 := bstep (se 1 (by rfl) ⟨6392357, by rfl⟩ : syracuseStep 8523143 = 12784715) B12784715
theorem B1682831 : Blo 1682041 1682831 := bstep (se 1 (by rfl) ⟨1262123, by rfl⟩ : syracuseStep 1682831 = 2524247) B2524247
theorem B3837331 : Blo 1682041 3837331 := bstep (se 1 (by rfl) ⟨2877998, by rfl⟩ : syracuseStep 3837331 = 5755997) B5755997
theorem B1682875 : Blo 1682041 1682875 := bstep (se 1 (by rfl) ⟨1262156, by rfl⟩ : syracuseStep 1682875 = 2524313) B2524313
theorem B1682951 : Blo 1682041 1682951 := bstep (se 1 (by rfl) ⟨1262213, by rfl⟩ : syracuseStep 1682951 = 2524427) B2524427
theorem B1682959 : Blo 1682041 1682959 := bstep (se 1 (by rfl) ⟨1262219, by rfl⟩ : syracuseStep 1682959 = 2524439) B2524439
theorem B1683003 : Blo 1682041 1683003 := bstep (se 1 (by rfl) ⟨1262252, by rfl⟩ : syracuseStep 1683003 = 2524505) B2524505
theorem B1683079 : Blo 1682041 1683079 := bstep (se 1 (by rfl) ⟨1262309, by rfl⟩ : syracuseStep 1683079 = 2524619) B2524619
theorem B3788423 : Blo 1682041 3788423 := bstep (se 1 (by rfl) ⟨2841317, by rfl⟩ : syracuseStep 3788423 = 5682635) B5682635
theorem B1683087 : Blo 1682041 1683087 := bstep (se 1 (by rfl) ⟨1262315, by rfl⟩ : syracuseStep 1683087 = 2524631) B2524631
theorem B1683131 : Blo 1682041 1683131 := bstep (se 1 (by rfl) ⟨1262348, by rfl⟩ : syracuseStep 1683131 = 2524697) B2524697
theorem B1683207 : Blo 1682041 1683207 := bstep (se 1 (by rfl) ⟨1262405, by rfl⟩ : syracuseStep 1683207 = 2524811) B2524811
theorem B1683215 : Blo 1682041 1683215 := bstep (se 1 (by rfl) ⟨1262411, by rfl⟩ : syracuseStep 1683215 = 2524823) B2524823
theorem B1683259 : Blo 1682041 1683259 := bstep (se 1 (by rfl) ⟨1262444, by rfl⟩ : syracuseStep 1683259 = 2524889) B2524889
theorem B3788603 : Blo 1682041 3788603 := bstep (se 1 (by rfl) ⟨2841452, by rfl⟩ : syracuseStep 3788603 = 5682905) B5682905
theorem B1683335 : Blo 1682041 1683335 := bstep (se 1 (by rfl) ⟨1262501, by rfl⟩ : syracuseStep 1683335 = 2525003) B2525003
theorem B1683343 : Blo 1682041 1683343 := bstep (se 1 (by rfl) ⟨1262507, by rfl⟩ : syracuseStep 1683343 = 2525015) B2525015
theorem B21041059 : Blo 1682041 21041059 := bstep (se 1 (by rfl) ⟨15780794, by rfl⟩ : syracuseStep 21041059 = 31561589) B31561589
theorem B2559929 : Blo 1682041 2559929 := bstep (se 2 (by rfl) ⟨959973, by rfl⟩ : syracuseStep 2559929 = 1919947) B1919947
theorem B3788729 : Blo 1682041 3788729 := bstep (se 2 (by rfl) ⟨1420773, by rfl⟩ : syracuseStep 3788729 = 2841547) B2841547
theorem B1683387 : Blo 1682041 1683387 := bstep (se 1 (by rfl) ⟨1262540, by rfl⟩ : syracuseStep 1683387 = 2525081) B2525081
theorem B1683463 : Blo 1682041 1683463 := bstep (se 1 (by rfl) ⟨1262597, by rfl⟩ : syracuseStep 1683463 = 2525195) B2525195
theorem B36892685 : Blo 1682041 36892685 := bstep (se 3 (by rfl) ⟨6917378, by rfl⟩ : syracuseStep 36892685 = 13834757) B13834757
theorem B1683471 : Blo 1682041 1683471 := bstep (se 1 (by rfl) ⟨1262603, by rfl⟩ : syracuseStep 1683471 = 2525207) B2525207
theorem B5394475 : Blo 1682041 5394475 := bstep (se 1 (by rfl) ⟨4045856, by rfl⟩ : syracuseStep 5394475 = 8091713) B8091713
theorem B1683515 : Blo 1682041 1683515 := bstep (se 1 (by rfl) ⟨1262636, by rfl⟩ : syracuseStep 1683515 = 2525273) B2525273
theorem B6393923 : Blo 1682041 6393923 := bstep (se 1 (by rfl) ⟨4795442, by rfl⟩ : syracuseStep 6393923 = 9590885) B9590885
theorem B24252533 : Blo 1682041 24252533 := bstep (se 5 (by rfl) ⟨1136837, by rfl⟩ : syracuseStep 24252533 = 2273675) B2273675
theorem B1683591 : Blo 1682041 1683591 := bstep (se 1 (by rfl) ⟨1262693, by rfl⟩ : syracuseStep 1683591 = 2525387) B2525387
theorem B1683599 : Blo 1682041 1683599 := bstep (se 1 (by rfl) ⟨1262699, by rfl⟩ : syracuseStep 1683599 = 2525399) B2525399
theorem B32354477 : Blo 1682041 32354477 := bstep (se 3 (by rfl) ⟨6066464, by rfl⟩ : syracuseStep 32354477 = 12132929) B12132929
theorem B1683643 : Blo 1682041 1683643 := bstep (se 1 (by rfl) ⟨1262732, by rfl⟩ : syracuseStep 1683643 = 2525465) B2525465
theorem B10932461 : Blo 1682041 10932461 := bstep (se 3 (by rfl) ⟨2049836, by rfl⟩ : syracuseStep 10932461 = 4099673) B4099673
theorem B1683719 : Blo 1682041 1683719 := bstep (se 1 (by rfl) ⟨1262789, by rfl⟩ : syracuseStep 1683719 = 2525579) B2525579
theorem B1683727 : Blo 1682041 1683727 := bstep (se 1 (by rfl) ⟨1262795, by rfl⟩ : syracuseStep 1683727 = 2525591) B2525591
theorem B3789071 : Blo 1682041 3789071 := bstep (se 1 (by rfl) ⟨2841803, by rfl⟩ : syracuseStep 3789071 = 5683607) B5683607
theorem B3789089 : Blo 1682041 3789089 := bstep (se 2 (by rfl) ⟨1420908, by rfl⟩ : syracuseStep 3789089 = 2841817) B2841817
theorem B2838827 : Blo 1682041 2838827 := bstep (se 1 (by rfl) ⟨2129120, by rfl⟩ : syracuseStep 2838827 = 4258241) B4258241
theorem B3592507 : Blo 1682041 3592507 := bstep (se 1 (by rfl) ⟨2694380, by rfl⟩ : syracuseStep 3592507 = 5388761) B5388761
theorem B1683771 : Blo 1682041 1683771 := bstep (se 1 (by rfl) ⟨1262828, by rfl⟩ : syracuseStep 1683771 = 2525657) B2525657
theorem B1683847 : Blo 1682041 1683847 := bstep (se 1 (by rfl) ⟨1262885, by rfl⟩ : syracuseStep 1683847 = 2525771) B2525771
theorem B2560391 : Blo 1682041 2560391 := bstep (se 1 (by rfl) ⟨1920293, by rfl⟩ : syracuseStep 2560391 = 3840587) B3840587
theorem B1683855 : Blo 1682041 1683855 := bstep (se 1 (by rfl) ⟨1262891, by rfl⟩ : syracuseStep 1683855 = 2525783) B2525783
theorem B5681555 : Blo 1682041 5681555 := bstep (se 1 (by rfl) ⟨4261166, by rfl⟩ : syracuseStep 5681555 = 8522333) B8522333
theorem B1683899 : Blo 1682041 1683899 := bstep (se 1 (by rfl) ⟨1262924, by rfl⟩ : syracuseStep 1683899 = 2525849) B2525849
theorem B4551113 : Blo 1682041 4551113 := bstep (se 2 (by rfl) ⟨1706667, by rfl⟩ : syracuseStep 4551113 = 3413335) B3413335
theorem B40931801 : Blo 1682041 40931801 := bstep (se 2 (by rfl) ⟨15349425, by rfl⟩ : syracuseStep 40931801 = 30698851) B30698851
theorem B28750301 : Blo 1682041 28750301 := bstep (se 3 (by rfl) ⟨5390681, by rfl⟩ : syracuseStep 28750301 = 10781363) B10781363
theorem B1683975 : Blo 1682041 1683975 := bstep (se 1 (by rfl) ⟨1262981, by rfl⟩ : syracuseStep 1683975 = 2525963) B2525963
theorem B1683983 : Blo 1682041 1683983 := bstep (se 1 (by rfl) ⟨1262987, by rfl⟩ : syracuseStep 1683983 = 2525975) B2525975
theorem B3240481 : Blo 1682041 3240481 := bstep (se 2 (by rfl) ⟨1215180, by rfl⟩ : syracuseStep 3240481 = 2430361) B2430361
theorem B3592763 : Blo 1682041 3592763 := bstep (se 1 (by rfl) ⟨2694572, by rfl⟩ : syracuseStep 3592763 = 5389145) B5389145
theorem B1684027 : Blo 1682041 1684027 := bstep (se 1 (by rfl) ⟨1263020, by rfl⟩ : syracuseStep 1684027 = 2526041) B2526041
theorem B2839225 : Blo 1682041 2839225 := bstep (se 2 (by rfl) ⟨1064709, by rfl⟩ : syracuseStep 2839225 = 2129419) B2129419
theorem B4551353 : Blo 1682041 4551353 := bstep (se 2 (by rfl) ⟨1706757, by rfl⟩ : syracuseStep 4551353 = 3413515) B3413515
theorem B6476525 : Blo 1682041 6476525 := bstep (se 3 (by rfl) ⟨1214348, by rfl⟩ : syracuseStep 6476525 = 2428697) B2428697
theorem B19428185 : Blo 1682041 19428185 := bstep (se 2 (by rfl) ⟨7285569, by rfl⟩ : syracuseStep 19428185 = 14571139) B14571139
theorem B9581611 : Blo 1682041 9581611 := bstep (se 1 (by rfl) ⟨7186208, by rfl⟩ : syracuseStep 9581611 = 14372417) B14372417
theorem B2397385 : Blo 1682041 2397385 := bstep (se 2 (by rfl) ⟨899019, by rfl⟩ : syracuseStep 2397385 = 1798039) B1798039
theorem B4551979 : Blo 1682041 4551979 := bstep (se 1 (by rfl) ⟨3413984, by rfl⟩ : syracuseStep 4551979 = 6827969) B6827969
theorem B2839927 : Blo 1682041 2839927 := bstep (se 1 (by rfl) ⟨2129945, by rfl⟩ : syracuseStep 2839927 = 4259891) B4259891
theorem B4044185 : Blo 1682041 4044185 := bstep (se 2 (by rfl) ⟨1516569, by rfl⟩ : syracuseStep 4044185 = 3033139) B3033139
theorem B40924601 : Blo 1682041 40924601 := bstep (se 2 (by rfl) ⟨15346725, by rfl⟩ : syracuseStep 40924601 = 30693451) B30693451
theorem B8082947 : Blo 1682041 8082947 := bstep (se 1 (by rfl) ⟨6062210, by rfl⟩ : syracuseStep 8082947 = 12124421) B12124421
theorem B8517149 : Blo 1682041 8517149 := bstep (se 3 (by rfl) ⟨1596965, by rfl⟩ : syracuseStep 8517149 = 3193931) B3193931
theorem B2840123 : Blo 1682041 2840123 := bstep (se 1 (by rfl) ⟨2130092, by rfl⟩ : syracuseStep 2840123 = 4260185) B4260185
theorem B9590359 : Blo 1682041 9590359 := bstep (se 1 (by rfl) ⟨7192769, by rfl⟩ : syracuseStep 9590359 = 14385539) B14385539
theorem B7673545 : Blo 1682041 7673545 := bstep (se 2 (by rfl) ⟨2877579, by rfl⟩ : syracuseStep 7673545 = 5755159) B5755159
theorem B6387437 : Blo 1682041 6387437 := bstep (se 3 (by rfl) ⟨1197644, by rfl⟩ : syracuseStep 6387437 = 2395289) B2395289
theorem B5682959 : Blo 1682041 5682959 := bstep (se 1 (by rfl) ⟨4262219, by rfl⟩ : syracuseStep 5682959 = 8524439) B8524439
theorem B2840521 : Blo 1682041 2840521 := bstep (se 2 (by rfl) ⟨1065195, by rfl⟩ : syracuseStep 2840521 = 2130391) B2130391
theorem B8517635 : Blo 1682041 8517635 := bstep (se 1 (by rfl) ⟨6388226, by rfl⟩ : syracuseStep 8517635 = 12776453) B12776453
theorem B9099287 : Blo 1682041 9099287 := bstep (se 1 (by rfl) ⟨6824465, by rfl⟩ : syracuseStep 9099287 = 13648931) B13648931
theorem B12785687 : Blo 1682041 12785687 := bstep (se 1 (by rfl) ⟨9589265, by rfl⟩ : syracuseStep 12785687 = 19178531) B19178531
theorem B5683229 : Blo 1682041 5683229 := bstep (se 3 (by rfl) ⟨1065605, by rfl⟩ : syracuseStep 5683229 = 2131211) B2131211
theorem B10786877 : Blo 1682041 10786877 := bstep (se 3 (by rfl) ⟨2022539, by rfl⟩ : syracuseStep 10786877 = 4045079) B4045079
theorem B57620753 : Blo 1682041 57620753 := bstep (se 2 (by rfl) ⟨21607782, by rfl⟩ : syracuseStep 57620753 = 43215565) B43215565
theorem B7190993 : Blo 1682041 7190993 := bstep (se 2 (by rfl) ⟨2696622, by rfl⟩ : syracuseStep 7190993 = 5393245) B5393245
theorem B9583069 : Blo 1682041 9583069 := bstep (se 3 (by rfl) ⟨1796825, by rfl⟩ : syracuseStep 9583069 = 3593651) B3593651
theorem B4676183 : Blo 1682041 4676183 := bstep (se 1 (by rfl) ⟨3507137, by rfl⟩ : syracuseStep 4676183 = 7014275) B7014275
theorem B2841223 : Blo 1682041 2841223 := bstep (se 1 (by rfl) ⟨2130917, by rfl⟩ : syracuseStep 2841223 = 4261835) B4261835
theorem B9222913 : Blo 1682041 9222913 := bstep (se 2 (by rfl) ⟨3458592, by rfl⟩ : syracuseStep 9222913 = 6917185) B6917185
theorem B27294479 : Blo 1682041 27294479 := bstep (se 1 (by rfl) ⟨20470859, by rfl⟩ : syracuseStep 27294479 = 40941719) B40941719
theorem B3193643 : Blo 1682041 3193643 := bstep (se 1 (by rfl) ⟨2395232, by rfl⟩ : syracuseStep 3193643 = 4790465) B4790465
theorem B3644345 : Blo 1682041 3644345 := bstep (se 2 (by rfl) ⟨1366629, by rfl⟩ : syracuseStep 3644345 = 2733259) B2733259
theorem B4791307 : Blo 1682041 4791307 := bstep (se 1 (by rfl) ⟨3593480, by rfl⟩ : syracuseStep 4791307 = 7186961) B7186961
theorem B10238987 : Blo 1682041 10238987 := bstep (se 1 (by rfl) ⟨7679240, by rfl⟩ : syracuseStep 10238987 = 15358481) B15358481
theorem B8084717 : Blo 1682041 8084717 := bstep (se 3 (by rfl) ⟨1515884, by rfl⟩ : syracuseStep 8084717 = 3031769) B3031769
theorem B4791581 : Blo 1682041 4791581 := bstep (se 3 (by rfl) ⟨898421, by rfl⟩ : syracuseStep 4791581 = 1796843) B1796843
theorem B4857175 : Blo 1682041 4857175 := bstep (se 1 (by rfl) ⟨3642881, by rfl⟩ : syracuseStep 4857175 = 7285763) B7285763
theorem B2129323 : Blo 1682041 2129323 := bstep (se 1 (by rfl) ⟨1596992, by rfl⟩ : syracuseStep 2129323 = 3193985) B3193985
theorem B25902521 : Blo 1682041 25902521 := bstep (se 2 (by rfl) ⟨9713445, by rfl⟩ : syracuseStep 25902521 = 19426891) B19426891
theorem B10239517 : Blo 1682041 10239517 := bstep (se 3 (by rfl) ⟨1919909, by rfl⟩ : syracuseStep 10239517 = 3839819) B3839819
theorem B13131341 : Blo 1682041 13131341 := bstep (se 3 (by rfl) ⟨2462126, by rfl⟩ : syracuseStep 13131341 = 4924253) B4924253
theorem B8519255 : Blo 1682041 8519255 := bstep (se 1 (by rfl) ⟨6389441, by rfl⟩ : syracuseStep 8519255 = 12778883) B12778883
theorem B4791923 : Blo 1682041 4791923 := bstep (se 1 (by rfl) ⟨3593942, by rfl⟩ : syracuseStep 4791923 = 7187885) B7187885
theorem B2694791 : Blo 1682041 2694791 := bstep (se 1 (by rfl) ⟨2021093, by rfl⟩ : syracuseStep 2694791 = 4042187) B4042187
theorem B3194569 : Blo 1682041 3194569 := bstep (se 2 (by rfl) ⟨1197963, by rfl⟩ : syracuseStep 3194569 = 2395927) B2395927
theorem B6389563 : Blo 1682041 6389563 := bstep (se 1 (by rfl) ⟨4792172, by rfl⟩ : syracuseStep 6389563 = 9584345) B9584345
theorem B4259699 : Blo 1682041 4259699 := bstep (se 1 (by rfl) ⟨3194774, by rfl⟩ : syracuseStep 4259699 = 6389549) B6389549
theorem B17268643 : Blo 1682041 17268643 := bstep (se 1 (by rfl) ⟨12951482, by rfl⟩ : syracuseStep 17268643 = 25902965) B25902965
theorem B2523065 : Blo 1682041 2523065 := bstep (se 2 (by rfl) ⟨946149, by rfl⟩ : syracuseStep 2523065 = 1892299) B1892299
theorem B19161035 : Blo 1682041 19161035 := bstep (se 1 (by rfl) ⟨14370776, by rfl⟩ : syracuseStep 19161035 = 28741553) B28741553
theorem B27303965 : Blo 1682041 27303965 := bstep (se 3 (by rfl) ⟨5119493, by rfl⟩ : syracuseStep 27303965 = 10238987) B10238987
theorem B7192633 : Blo 1682041 7192633 := bstep (se 2 (by rfl) ⟨2697237, by rfl⟩ : syracuseStep 7192633 = 5394475) B5394475
theorem B2523215 : Blo 1682041 2523215 := bstep (se 1 (by rfl) ⟨1892411, by rfl⟩ : syracuseStep 2523215 = 3784823) B3784823
theorem B16171123 : Blo 1682041 16171123 := bstep (se 1 (by rfl) ⟨12128342, by rfl⟩ : syracuseStep 16171123 = 24256685) B24256685
theorem B21569651 : Blo 1682041 21569651 := bstep (se 1 (by rfl) ⟨16177238, by rfl⟩ : syracuseStep 21569651 = 32354477) B32354477
theorem B2523335 : Blo 1682041 2523335 := bstep (se 1 (by rfl) ⟨1892501, by rfl⟩ : syracuseStep 2523335 = 3785003) B3785003
theorem B1892551 : Blo 1682041 1892551 := bstep (se 1 (by rfl) ⟨1419413, by rfl⟩ : syracuseStep 1892551 = 2838827) B2838827
theorem B6062327 : Blo 1682041 6062327 := bstep (se 1 (by rfl) ⟨4546745, by rfl⟩ : syracuseStep 6062327 = 9093491) B9093491
theorem B27287867 : Blo 1682041 27287867 := bstep (se 1 (by rfl) ⟨20465900, by rfl⟩ : syracuseStep 27287867 = 40931801) B40931801
theorem B2523497 : Blo 1682041 2523497 := bstep (se 2 (by rfl) ⟨946311, by rfl⟩ : syracuseStep 2523497 = 1892623) B1892623
theorem B8520065 : Blo 1682041 8520065 := bstep (se 2 (by rfl) ⟨3195024, by rfl⟩ : syracuseStep 8520065 = 6390049) B6390049
theorem B2523575 : Blo 1682041 2523575 := bstep (se 1 (by rfl) ⟨1892681, by rfl⟩ : syracuseStep 2523575 = 3785363) B3785363
theorem B2523611 : Blo 1682041 2523611 := bstep (se 1 (by rfl) ⟨1892708, by rfl⟩ : syracuseStep 2523611 = 3785417) B3785417
theorem B4317683 : Blo 1682041 4317683 := bstep (se 1 (by rfl) ⟨3238262, by rfl⟩ : syracuseStep 4317683 = 6476525) B6476525
theorem B4547081 : Blo 1682041 4547081 := bstep (se 2 (by rfl) ⟨1705155, by rfl⟩ : syracuseStep 4547081 = 3410311) B3410311
theorem B4260377 : Blo 1682041 4260377 := bstep (se 2 (by rfl) ⟨1597641, by rfl⟩ : syracuseStep 4260377 = 3195283) B3195283
theorem B3785255 : Blo 1682041 3785255 := bstep (se 1 (by rfl) ⟨2838941, by rfl⟩ : syracuseStep 3785255 = 5677883) B5677883
theorem B5390887 : Blo 1682041 5390887 := bstep (se 1 (by rfl) ⟨4043165, by rfl⟩ : syracuseStep 5390887 = 8086331) B8086331
theorem B12124883 : Blo 1682041 12124883 := bstep (se 1 (by rfl) ⟨9093662, by rfl⟩ : syracuseStep 12124883 = 18187325) B18187325
theorem B6390521 : Blo 1682041 6390521 := bstep (se 2 (by rfl) ⟨2396445, by rfl⟩ : syracuseStep 6390521 = 4792891) B4792891
theorem B23036723 : Blo 1682041 23036723 := bstep (se 1 (by rfl) ⟨17277542, by rfl⟩ : syracuseStep 23036723 = 34555085) B34555085
theorem B3785579 : Blo 1682041 3785579 := bstep (se 1 (by rfl) ⟨2839184, by rfl⟩ : syracuseStep 3785579 = 5678369) B5678369
theorem B3785633 : Blo 1682041 3785633 := bstep (se 2 (by rfl) ⟨1419612, by rfl⟩ : syracuseStep 3785633 = 2839225) B2839225
theorem B2524079 : Blo 1682041 2524079 := bstep (se 1 (by rfl) ⟨1893059, by rfl⟩ : syracuseStep 2524079 = 3786119) B3786119
theorem B2696123 : Blo 1682041 2696123 := bstep (se 1 (by rfl) ⟨2022092, by rfl⟩ : syracuseStep 2696123 = 4044185) B4044185
theorem B12297217 : Blo 1682041 12297217 := bstep (se 2 (by rfl) ⟨4611456, by rfl⟩ : syracuseStep 12297217 = 9222913) B9222913
theorem B2524169 : Blo 1682041 2524169 := bstep (se 2 (by rfl) ⟨946563, by rfl⟩ : syracuseStep 2524169 = 1893127) B1893127
theorem B5678099 : Blo 1682041 5678099 := bstep (se 1 (by rfl) ⟨4258574, by rfl⟩ : syracuseStep 5678099 = 8517149) B8517149
theorem B4260883 : Blo 1682041 4260883 := bstep (se 1 (by rfl) ⟨3195662, by rfl⟩ : syracuseStep 4260883 = 6391325) B6391325
theorem B2524199 : Blo 1682041 2524199 := bstep (se 1 (by rfl) ⟨1893149, by rfl⟩ : syracuseStep 2524199 = 3786299) B3786299
theorem B1893415 : Blo 1682041 1893415 := bstep (se 1 (by rfl) ⟨1420061, by rfl⟩ : syracuseStep 1893415 = 2840123) B2840123
theorem B2524283 : Blo 1682041 2524283 := bstep (se 1 (by rfl) ⟨1893212, by rfl⟩ : syracuseStep 2524283 = 3786425) B3786425
theorem B3196027 : Blo 1682041 3196027 := bstep (se 1 (by rfl) ⟨2397020, by rfl⟩ : syracuseStep 3196027 = 4794041) B4794041
theorem B15353003 : Blo 1682041 15353003 := bstep (se 1 (by rfl) ⟨11514752, by rfl⟩ : syracuseStep 15353003 = 23029505) B23029505
theorem B8520875 : Blo 1682041 8520875 := bstep (se 1 (by rfl) ⟨6390656, by rfl⟩ : syracuseStep 8520875 = 12781313) B12781313
theorem B3785975 : Blo 1682041 3785975 := bstep (se 1 (by rfl) ⟨2839481, by rfl⟩ : syracuseStep 3785975 = 5678963) B5678963
theorem B2524409 : Blo 1682041 2524409 := bstep (se 2 (by rfl) ⟨946653, by rfl⟩ : syracuseStep 2524409 = 1893307) B1893307
theorem B5678423 : Blo 1682041 5678423 := bstep (se 1 (by rfl) ⟨4258817, by rfl⟩ : syracuseStep 5678423 = 8517635) B8517635
theorem B21554525 : Blo 1682041 21554525 := bstep (se 3 (by rfl) ⟨4041473, by rfl⟩ : syracuseStep 21554525 = 8082947) B8082947
theorem B2524511 : Blo 1682041 2524511 := bstep (se 1 (by rfl) ⟨1893383, by rfl⟩ : syracuseStep 2524511 = 3786767) B3786767
theorem B3196255 : Blo 1682041 3196255 := bstep (se 1 (by rfl) ⟨2397191, by rfl⟩ : syracuseStep 3196255 = 4794383) B4794383
theorem B2524523 : Blo 1682041 2524523 := bstep (se 1 (by rfl) ⟨1893392, by rfl⟩ : syracuseStep 2524523 = 3786785) B3786785
theorem B13649315 : Blo 1682041 13649315 := bstep (se 1 (by rfl) ⟨10236986, by rfl⟩ : syracuseStep 13649315 = 20473973) B20473973
theorem B1705415 : Blo 1682041 1705415 := bstep (se 1 (by rfl) ⟨1279061, by rfl⟩ : syracuseStep 1705415 = 2558123) B2558123
theorem B38413835 : Blo 1682041 38413835 := bstep (se 1 (by rfl) ⟨28810376, by rfl⟩ : syracuseStep 38413835 = 57620753) B57620753
theorem B2524751 : Blo 1682041 2524751 := bstep (se 1 (by rfl) ⟨1893563, by rfl⟩ : syracuseStep 2524751 = 3787127) B3787127
theorem B3196513 : Blo 1682041 3196513 := bstep (se 2 (by rfl) ⟨1198692, by rfl⟩ : syracuseStep 3196513 = 2397385) B2397385
theorem B4793995 : Blo 1682041 4793995 := bstep (se 1 (by rfl) ⟨3595496, by rfl⟩ : syracuseStep 4793995 = 7190993) B7190993
theorem B8521361 : Blo 1682041 8521361 := bstep (se 2 (by rfl) ⟨3195510, by rfl⟩ : syracuseStep 8521361 = 6391021) B6391021
theorem B2524871 : Blo 1682041 2524871 := bstep (se 1 (by rfl) ⟨1893653, by rfl⟩ : syracuseStep 2524871 = 3787307) B3787307
theorem B6391507 : Blo 1682041 6391507 := bstep (se 1 (by rfl) ⟨4793630, by rfl⟩ : syracuseStep 6391507 = 9587261) B9587261
theorem B25904933 : Blo 1682041 25904933 := bstep (se 4 (by rfl) ⟨2428587, by rfl⟩ : syracuseStep 25904933 = 4857175) B4857175
theorem B3786569 : Blo 1682041 3786569 := bstep (se 2 (by rfl) ⟨1419963, by rfl⟩ : syracuseStep 3786569 = 2839927) B2839927
theorem B18196319 : Blo 1682041 18196319 := bstep (se 1 (by rfl) ⟨13647239, by rfl⟩ : syracuseStep 18196319 = 27294479) B27294479
theorem B2525033 : Blo 1682041 2525033 := bstep (se 2 (by rfl) ⟨946887, by rfl⟩ : syracuseStep 2525033 = 1893775) B1893775
theorem B3196847 : Blo 1682041 3196847 := bstep (se 1 (by rfl) ⟨2397635, by rfl⟩ : syracuseStep 3196847 = 4795271) B4795271
theorem B2525111 : Blo 1682041 2525111 := bstep (se 1 (by rfl) ⟨1893833, by rfl⟩ : syracuseStep 2525111 = 3787667) B3787667
theorem B2525147 : Blo 1682041 2525147 := bstep (se 1 (by rfl) ⟨1893860, by rfl⟩ : syracuseStep 2525147 = 3787721) B3787721
theorem B414566423 : Blo 1682041 414566423 := bstep (se 1 (by rfl) ⟨310924817, by rfl⟩ : syracuseStep 414566423 = 621849635) B621849635
theorem B4261967 : Blo 1682041 4261967 := bstep (se 1 (by rfl) ⟨3196475, by rfl⟩ : syracuseStep 4261967 = 6392951) B6392951
theorem B6391979 : Blo 1682041 6391979 := bstep (se 1 (by rfl) ⟨4793984, by rfl⟩ : syracuseStep 6391979 = 9587969) B9587969
theorem B51808493 : Blo 1682041 51808493 := bstep (se 3 (by rfl) ⟨9714092, by rfl⟩ : syracuseStep 51808493 = 19428185) B19428185
theorem B2918729 : Blo 1682041 2918729 := bstep (se 2 (by rfl) ⟨1094523, by rfl⟩ : syracuseStep 2918729 = 2189047) B2189047
theorem B23333225 : Blo 1682041 23333225 := bstep (se 2 (by rfl) ⟨8749959, by rfl⟩ : syracuseStep 23333225 = 17499919) B17499919
theorem B5679503 : Blo 1682041 5679503 := bstep (se 1 (by rfl) ⟨4259627, by rfl⟩ : syracuseStep 5679503 = 8519255) B8519255
theorem B1796527 : Blo 1682041 1796527 := bstep (se 1 (by rfl) ⟨1347395, by rfl⟩ : syracuseStep 1796527 = 2694791) B2694791
theorem B2525615 : Blo 1682041 2525615 := bstep (se 1 (by rfl) ⟨1894211, by rfl⟩ : syracuseStep 2525615 = 3788423) B3788423
theorem B6826477 : Blo 1682041 6826477 := bstep (se 3 (by rfl) ⟨1279964, by rfl⟩ : syracuseStep 6826477 = 2559929) B2559929
theorem B2525705 : Blo 1682041 2525705 := bstep (se 2 (by rfl) ⟨947139, by rfl⟩ : syracuseStep 2525705 = 1894279) B1894279
theorem B2525735 : Blo 1682041 2525735 := bstep (se 1 (by rfl) ⟨1894301, by rfl⟩ : syracuseStep 2525735 = 3788603) B3788603
theorem B3787361 : Blo 1682041 3787361 := bstep (se 2 (by rfl) ⟨1420260, by rfl⟩ : syracuseStep 3787361 = 2840521) B2840521
theorem B1682043 : Blo 1682041 1682043 := bstep (se 1 (by rfl) ⟨1261532, by rfl⟩ : syracuseStep 1682043 = 2523065) B2523065
theorem B2525819 : Blo 1682041 2525819 := bstep (se 1 (by rfl) ⟨1894364, by rfl⟩ : syracuseStep 2525819 = 3788729) B3788729
theorem B12774023 : Blo 1682041 12774023 := bstep (se 1 (by rfl) ⟨9580517, by rfl⟩ : syracuseStep 12774023 = 19161035) B19161035
theorem B1682095 : Blo 1682041 1682095 := bstep (se 1 (by rfl) ⟨1261571, by rfl⟩ : syracuseStep 1682095 = 2523143) B2523143
theorem B24595123 : Blo 1682041 24595123 := bstep (se 1 (by rfl) ⟨18446342, by rfl⟩ : syracuseStep 24595123 = 36892685) B36892685
theorem B1682119 : Blo 1682041 1682119 := bstep (se 1 (by rfl) ⟨1261589, by rfl⟩ : syracuseStep 1682119 = 2523179) B2523179
theorem B5679827 : Blo 1682041 5679827 := bstep (se 1 (by rfl) ⟨4259870, by rfl⟩ : syracuseStep 5679827 = 8519741) B8519741
theorem B4262615 : Blo 1682041 4262615 := bstep (se 1 (by rfl) ⟨3196961, by rfl⟩ : syracuseStep 4262615 = 6393923) B6393923
theorem B1682139 : Blo 1682041 1682139 := bstep (se 1 (by rfl) ⟨1261604, by rfl⟩ : syracuseStep 1682139 = 2523209) B2523209
theorem B2525945 : Blo 1682041 2525945 := bstep (se 2 (by rfl) ⟨947229, by rfl⟩ : syracuseStep 2525945 = 1894459) B1894459
theorem B1682215 : Blo 1682041 1682215 := bstep (se 1 (by rfl) ⟨1261661, by rfl⟩ : syracuseStep 1682215 = 2523323) B2523323
theorem B54610757 : Blo 1682041 54610757 := bstep (se 4 (by rfl) ⟨5119758, by rfl⟩ : syracuseStep 54610757 = 10239517) B10239517
theorem B1682255 : Blo 1682041 1682255 := bstep (se 1 (by rfl) ⟨1261691, by rfl⟩ : syracuseStep 1682255 = 2523383) B2523383
theorem B1682271 : Blo 1682041 1682271 := bstep (se 1 (by rfl) ⟨1261703, by rfl⟩ : syracuseStep 1682271 = 2523407) B2523407
theorem B2526047 : Blo 1682041 2526047 := bstep (se 1 (by rfl) ⟨1894535, by rfl⟩ : syracuseStep 2526047 = 3789071) B3789071
theorem B2526059 : Blo 1682041 2526059 := bstep (se 1 (by rfl) ⟨1894544, by rfl⟩ : syracuseStep 2526059 = 3789089) B3789089
theorem B1682299 : Blo 1682041 1682299 := bstep (se 1 (by rfl) ⟨1261724, by rfl⟩ : syracuseStep 1682299 = 2523449) B2523449
theorem B1682351 : Blo 1682041 1682351 := bstep (se 1 (by rfl) ⟨1261763, by rfl⟩ : syracuseStep 1682351 = 2523527) B2523527
theorem B1706927 : Blo 1682041 1706927 := bstep (se 1 (by rfl) ⟨1280195, by rfl⟩ : syracuseStep 1706927 = 2560391) B2560391
theorem B3787703 : Blo 1682041 3787703 := bstep (se 1 (by rfl) ⟨2840777, by rfl⟩ : syracuseStep 3787703 = 5681555) B5681555
theorem B1682375 : Blo 1682041 1682375 := bstep (se 1 (by rfl) ⟨1261781, by rfl⟩ : syracuseStep 1682375 = 2523563) B2523563
theorem B1682395 : Blo 1682041 1682395 := bstep (se 1 (by rfl) ⟨1261796, by rfl⟩ : syracuseStep 1682395 = 2523593) B2523593
theorem B2395175 : Blo 1682041 2395175 := bstep (se 1 (by rfl) ⟨1796381, by rfl⟩ : syracuseStep 2395175 = 3592763) B3592763
theorem B1682471 : Blo 1682041 1682471 := bstep (se 1 (by rfl) ⟨1261853, by rfl⟩ : syracuseStep 1682471 = 2523707) B2523707
theorem B6065209 : Blo 1682041 6065209 := bstep (se 2 (by rfl) ⟨2274453, by rfl⟩ : syracuseStep 6065209 = 4548907) B4548907
theorem B1682511 : Blo 1682041 1682511 := bstep (se 1 (by rfl) ⟨1261883, by rfl⟩ : syracuseStep 1682511 = 2523767) B2523767
theorem B1682527 : Blo 1682041 1682527 := bstep (se 1 (by rfl) ⟨1261895, by rfl⟩ : syracuseStep 1682527 = 2523791) B2523791
theorem B1682555 : Blo 1682041 1682555 := bstep (se 1 (by rfl) ⟨1261916, by rfl⟩ : syracuseStep 1682555 = 2523833) B2523833
theorem B3034235 : Blo 1682041 3034235 := bstep (se 1 (by rfl) ⟨2275676, by rfl⟩ : syracuseStep 3034235 = 4551353) B4551353
theorem B1682607 : Blo 1682041 1682607 := bstep (se 1 (by rfl) ⟨1261955, by rfl⟩ : syracuseStep 1682607 = 2523911) B2523911
theorem B1682631 : Blo 1682041 1682631 := bstep (se 1 (by rfl) ⟨1261973, by rfl⟩ : syracuseStep 1682631 = 2523947) B2523947
theorem B1682651 : Blo 1682041 1682651 := bstep (se 1 (by rfl) ⟨1261988, by rfl⟩ : syracuseStep 1682651 = 2523977) B2523977
theorem B1682727 : Blo 1682041 1682727 := bstep (se 1 (by rfl) ⟨1262045, by rfl⟩ : syracuseStep 1682727 = 2524091) B2524091
theorem B1682767 : Blo 1682041 1682767 := bstep (se 1 (by rfl) ⟨1262075, by rfl⟩ : syracuseStep 1682767 = 2524151) B2524151
theorem B1682783 : Blo 1682041 1682783 := bstep (se 1 (by rfl) ⟨1262087, by rfl⟩ : syracuseStep 1682783 = 2524175) B2524175
theorem B1682811 : Blo 1682041 1682811 := bstep (se 1 (by rfl) ⟨1262108, by rfl⟩ : syracuseStep 1682811 = 2524217) B2524217
theorem B4320641 : Blo 1682041 4320641 := bstep (se 2 (by rfl) ⟨1620240, by rfl⟩ : syracuseStep 4320641 = 3240481) B3240481
theorem B1682863 : Blo 1682041 1682863 := bstep (se 1 (by rfl) ⟨1262147, by rfl⟩ : syracuseStep 1682863 = 2524295) B2524295
theorem B1682887 : Blo 1682041 1682887 := bstep (se 1 (by rfl) ⟨1262165, by rfl⟩ : syracuseStep 1682887 = 2524331) B2524331
theorem B1682907 : Blo 1682041 1682907 := bstep (se 1 (by rfl) ⟨1262180, by rfl⟩ : syracuseStep 1682907 = 2524361) B2524361
theorem B3788297 : Blo 1682041 3788297 := bstep (se 2 (by rfl) ⟨1420611, by rfl⟩ : syracuseStep 3788297 = 2841223) B2841223
theorem B1682983 : Blo 1682041 1682983 := bstep (se 1 (by rfl) ⟨1262237, by rfl⟩ : syracuseStep 1682983 = 2524475) B2524475
theorem B1683023 : Blo 1682041 1683023 := bstep (se 1 (by rfl) ⟨1262267, by rfl⟩ : syracuseStep 1683023 = 2524535) B2524535
theorem B1683039 : Blo 1682041 1683039 := bstep (se 1 (by rfl) ⟨1262279, by rfl⟩ : syracuseStep 1683039 = 2524559) B2524559
theorem B27283067 : Blo 1682041 27283067 := bstep (se 1 (by rfl) ⟨20462300, by rfl⟩ : syracuseStep 27283067 = 40924601) B40924601
theorem B1683067 : Blo 1682041 1683067 := bstep (se 1 (by rfl) ⟨1262300, by rfl⟩ : syracuseStep 1683067 = 2524601) B2524601
theorem B1683119 : Blo 1682041 1683119 := bstep (se 1 (by rfl) ⟨1262339, by rfl⟩ : syracuseStep 1683119 = 2524679) B2524679
theorem B1683143 : Blo 1682041 1683143 := bstep (se 1 (by rfl) ⟨1262357, by rfl⟩ : syracuseStep 1683143 = 2524715) B2524715
theorem B1683163 : Blo 1682041 1683163 := bstep (se 1 (by rfl) ⟨1262372, by rfl⟩ : syracuseStep 1683163 = 2524745) B2524745
theorem B1683239 : Blo 1682041 1683239 := bstep (se 1 (by rfl) ⟨1262429, by rfl⟩ : syracuseStep 1683239 = 2524859) B2524859
theorem B1683279 : Blo 1682041 1683279 := bstep (se 1 (by rfl) ⟨1262459, by rfl⟩ : syracuseStep 1683279 = 2524919) B2524919
theorem B1683295 : Blo 1682041 1683295 := bstep (se 1 (by rfl) ⟨1262471, by rfl⟩ : syracuseStep 1683295 = 2524943) B2524943
theorem B3788639 : Blo 1682041 3788639 := bstep (se 1 (by rfl) ⟨2841479, by rfl⟩ : syracuseStep 3788639 = 5682959) B5682959
theorem B8523629 : Blo 1682041 8523629 := bstep (se 3 (by rfl) ⟨1598180, by rfl⟩ : syracuseStep 8523629 = 3196361) B3196361
theorem B12136301 : Blo 1682041 12136301 := bstep (se 3 (by rfl) ⟨2275556, by rfl⟩ : syracuseStep 12136301 = 4551113) B4551113
theorem B5681015 : Blo 1682041 5681015 := bstep (se 1 (by rfl) ⟨4260761, by rfl⟩ : syracuseStep 5681015 = 8521523) B8521523
theorem B1683323 : Blo 1682041 1683323 := bstep (se 1 (by rfl) ⟨1262492, by rfl⟩ : syracuseStep 1683323 = 2524985) B2524985
theorem B19181447 : Blo 1682041 19181447 := bstep (se 1 (by rfl) ⟨14386085, by rfl⟩ : syracuseStep 19181447 = 28772171) B28772171
theorem B1683375 : Blo 1682041 1683375 := bstep (se 1 (by rfl) ⟨1262531, by rfl⟩ : syracuseStep 1683375 = 2525063) B2525063
theorem B1683399 : Blo 1682041 1683399 := bstep (se 1 (by rfl) ⟨1262549, by rfl⟩ : syracuseStep 1683399 = 2525099) B2525099
theorem B1683419 : Blo 1682041 1683419 := bstep (se 1 (by rfl) ⟨1262564, by rfl⟩ : syracuseStep 1683419 = 2525129) B2525129
theorem B6066191 : Blo 1682041 6066191 := bstep (se 1 (by rfl) ⟨4549643, by rfl⟩ : syracuseStep 6066191 = 9099287) B9099287
theorem B8523791 : Blo 1682041 8523791 := bstep (se 1 (by rfl) ⟨6392843, by rfl⟩ : syracuseStep 8523791 = 12785687) B12785687
theorem B3788819 : Blo 1682041 3788819 := bstep (se 1 (by rfl) ⟨2841614, by rfl⟩ : syracuseStep 3788819 = 5683229) B5683229
theorem B11677733 : Blo 1682041 11677733 := bstep (se 4 (by rfl) ⟨1094787, by rfl⟩ : syracuseStep 11677733 = 2189575) B2189575
theorem B1683495 : Blo 1682041 1683495 := bstep (se 1 (by rfl) ⟨1262621, by rfl⟩ : syracuseStep 1683495 = 2525243) B2525243
theorem B12775481 : Blo 1682041 12775481 := bstep (se 2 (by rfl) ⟨4790805, by rfl⟩ : syracuseStep 12775481 = 9581611) B9581611
theorem B5681231 : Blo 1682041 5681231 := bstep (se 1 (by rfl) ⟨4260923, by rfl⟩ : syracuseStep 5681231 = 8521847) B8521847
theorem B1683535 : Blo 1682041 1683535 := bstep (se 1 (by rfl) ⟨1262651, by rfl⟩ : syracuseStep 1683535 = 2525303) B2525303
theorem B6393937 : Blo 1682041 6393937 := bstep (se 2 (by rfl) ⟨2397726, by rfl⟩ : syracuseStep 6393937 = 4795453) B4795453
theorem B1683551 : Blo 1682041 1683551 := bstep (se 1 (by rfl) ⟨1262663, by rfl⟩ : syracuseStep 1683551 = 2525327) B2525327
theorem B1683579 : Blo 1682041 1683579 := bstep (se 1 (by rfl) ⟨1262684, by rfl⟩ : syracuseStep 1683579 = 2525369) B2525369
theorem B1683631 : Blo 1682041 1683631 := bstep (se 1 (by rfl) ⟨1262723, by rfl⟩ : syracuseStep 1683631 = 2525447) B2525447
theorem B1683655 : Blo 1682041 1683655 := bstep (se 1 (by rfl) ⟨1262741, by rfl⟩ : syracuseStep 1683655 = 2525483) B2525483
theorem B1683675 : Blo 1682041 1683675 := bstep (se 1 (by rfl) ⟨1262756, by rfl⟩ : syracuseStep 1683675 = 2525513) B2525513
theorem B1683751 : Blo 1682041 1683751 := bstep (se 1 (by rfl) ⟨1262813, by rfl⟩ : syracuseStep 1683751 = 2525627) B2525627
theorem B3412297 : Blo 1682041 3412297 := bstep (se 2 (by rfl) ⟨1279611, by rfl⟩ : syracuseStep 3412297 = 2559223) B2559223
theorem B1683791 : Blo 1682041 1683791 := bstep (se 1 (by rfl) ⟨1262843, by rfl⟩ : syracuseStep 1683791 = 2525687) B2525687
theorem B1683807 : Blo 1682041 1683807 := bstep (se 1 (by rfl) ⟨1262855, by rfl⟩ : syracuseStep 1683807 = 2525711) B2525711
theorem B1683835 : Blo 1682041 1683835 := bstep (se 1 (by rfl) ⟨1262876, by rfl⟩ : syracuseStep 1683835 = 2525753) B2525753
theorem B3117455 : Blo 1682041 3117455 := bstep (se 1 (by rfl) ⟨2338091, by rfl⟩ : syracuseStep 3117455 = 4676183) B4676183
theorem B1683887 : Blo 1682041 1683887 := bstep (se 1 (by rfl) ⟨1262915, by rfl⟩ : syracuseStep 1683887 = 2525831) B2525831
theorem B1683911 : Blo 1682041 1683911 := bstep (se 1 (by rfl) ⟨1262933, by rfl⟩ : syracuseStep 1683911 = 2525867) B2525867
theorem B5681609 : Blo 1682041 5681609 := bstep (se 2 (by rfl) ⟨2130603, by rfl⟩ : syracuseStep 5681609 = 4261207) B4261207
theorem B1683931 : Blo 1682041 1683931 := bstep (se 1 (by rfl) ⟨1262948, by rfl⟩ : syracuseStep 1683931 = 2525897) B2525897
theorem B6066697 : Blo 1682041 6066697 := bstep (se 2 (by rfl) ⟨2275011, by rfl⟩ : syracuseStep 6066697 = 4550023) B4550023
theorem B5116441 : Blo 1682041 5116441 := bstep (se 2 (by rfl) ⟨1918665, by rfl⟩ : syracuseStep 5116441 = 3837331) B3837331
theorem B1684007 : Blo 1682041 1684007 := bstep (se 1 (by rfl) ⟨1263005, by rfl⟩ : syracuseStep 1684007 = 2526011) B2526011
theorem B2839097 : Blo 1682041 2839097 := bstep (se 2 (by rfl) ⟨1064661, by rfl⟩ : syracuseStep 2839097 = 2129323) B2129323
theorem B2429563 : Blo 1682041 2429563 := bstep (se 1 (by rfl) ⟨1822172, by rfl⟩ : syracuseStep 2429563 = 3644345) B3644345
theorem B5681879 : Blo 1682041 5681879 := bstep (se 1 (by rfl) ⟨4261409, by rfl⟩ : syracuseStep 5681879 = 8522819) B8522819
theorem B4043513 : Blo 1682041 4043513 := bstep (se 2 (by rfl) ⟨1516317, by rfl⟩ : syracuseStep 4043513 = 3032635) B3032635
theorem B4043695 : Blo 1682041 4043695 := bstep (se 1 (by rfl) ⟨3032771, by rfl⟩ : syracuseStep 4043695 = 6065543) B6065543
theorem B5682095 : Blo 1682041 5682095 := bstep (se 1 (by rfl) ⟨4261571, by rfl⟩ : syracuseStep 5682095 = 8523143) B8523143
theorem B8754227 : Blo 1682041 8754227 := bstep (se 1 (by rfl) ⟨6565670, by rfl⟩ : syracuseStep 8754227 = 13131341) B13131341
theorem B23024857 : Blo 1682041 23024857 := bstep (se 2 (by rfl) ⟨8634321, by rfl⟩ : syracuseStep 23024857 = 17268643) B17268643
theorem B28054745 : Blo 1682041 28054745 := bstep (se 2 (by rfl) ⟨10520529, by rfl⟩ : syracuseStep 28054745 = 21041059) B21041059
theorem B2839799 : Blo 1682041 2839799 := bstep (se 1 (by rfl) ⟨2129849, by rfl⟩ : syracuseStep 2839799 = 4259699) B4259699
theorem B10777981 : Blo 1682041 10777981 := bstep (se 3 (by rfl) ⟨2020871, by rfl⟩ : syracuseStep 10777981 = 4041743) B4041743
theorem B16168355 : Blo 1682041 16168355 := bstep (se 1 (by rfl) ⟨12126266, by rfl⟩ : syracuseStep 16168355 = 24252533) B24252533
theorem B7288307 : Blo 1682041 7288307 := bstep (se 1 (by rfl) ⟨5466230, by rfl⟩ : syracuseStep 7288307 = 10932461) B10932461
theorem B3593737 : Blo 1682041 3593737 := bstep (se 2 (by rfl) ⟨1347651, by rfl⟩ : syracuseStep 3593737 = 2695303) B2695303
theorem B2840143 : Blo 1682041 2840143 := bstep (se 1 (by rfl) ⟨2130107, by rfl⟩ : syracuseStep 2840143 = 4260215) B4260215
theorem B19166867 : Blo 1682041 19166867 := bstep (se 1 (by rfl) ⟨14375150, by rfl⟩ : syracuseStep 19166867 = 28750301) B28750301
theorem B4789975 : Blo 1682041 4789975 := bstep (se 1 (by rfl) ⟨3592481, by rfl⟩ : syracuseStep 4789975 = 7184963) B7184963
theorem B4790009 : Blo 1682041 4790009 := bstep (se 2 (by rfl) ⟨1796253, by rfl⟩ : syracuseStep 4790009 = 3592507) B3592507
theorem B6821675 : Blo 1682041 6821675 := bstep (se 1 (by rfl) ⟨5116256, by rfl⟩ : syracuseStep 6821675 = 10232513) B10232513
theorem B2840393 : Blo 1682041 2840393 := bstep (se 2 (by rfl) ⟨1065147, by rfl⟩ : syracuseStep 2840393 = 2130295) B2130295
theorem B4790123 : Blo 1682041 4790123 := bstep (se 1 (by rfl) ⟨3592592, by rfl⟩ : syracuseStep 4790123 = 7185185) B7185185
theorem B4790191 : Blo 1682041 4790191 := bstep (se 1 (by rfl) ⟨3592643, by rfl⟩ : syracuseStep 4790191 = 7185287) B7185287
theorem B12777425 : Blo 1682041 12777425 := bstep (se 2 (by rfl) ⟨4791534, by rfl⟩ : syracuseStep 12777425 = 9583069) B9583069
theorem B2840825 : Blo 1682041 2840825 := bstep (se 2 (by rfl) ⟨1065309, by rfl⟩ : syracuseStep 2840825 = 2130619) B2130619
theorem B40925573 : Blo 1682041 40925573 := bstep (se 4 (by rfl) ⟨3836772, by rfl⟩ : syracuseStep 40925573 = 7673545) B7673545
theorem B2841007 : Blo 1682041 2841007 := bstep (se 1 (by rfl) ⟨2130755, by rfl⟩ : syracuseStep 2841007 = 4261511) B4261511
theorem B4258291 : Blo 1682041 4258291 := bstep (se 1 (by rfl) ⟨3193718, by rfl⟩ : syracuseStep 4258291 = 6387437) B6387437
theorem B2841095 : Blo 1682041 2841095 := bstep (se 1 (by rfl) ⟨2130821, by rfl⟩ : syracuseStep 2841095 = 4261643) B4261643
theorem B6388409 : Blo 1682041 6388409 := bstep (se 2 (by rfl) ⟨2395653, by rfl⟩ : syracuseStep 6388409 = 4791307) B4791307
theorem B7191251 : Blo 1682041 7191251 := bstep (se 1 (by rfl) ⟨5393438, by rfl⟩ : syracuseStep 7191251 = 10786877) B10786877
theorem B12950275 : Blo 1682041 12950275 := bstep (se 1 (by rfl) ⟨9712706, by rfl⟩ : syracuseStep 12950275 = 19425413) B19425413
theorem B2841439 : Blo 1682041 2841439 := bstep (se 1 (by rfl) ⟨2131079, by rfl⟩ : syracuseStep 2841439 = 4262159) B4262159
theorem B2841527 : Blo 1682041 2841527 := bstep (se 1 (by rfl) ⟨2131145, by rfl⟩ : syracuseStep 2841527 = 4262291) B4262291
theorem B6069305 : Blo 1682041 6069305 := bstep (se 2 (by rfl) ⟨2275989, by rfl⟩ : syracuseStep 6069305 = 4551979) B4551979
theorem B4791467 : Blo 1682041 4791467 := bstep (se 1 (by rfl) ⟨3593600, by rfl⟩ : syracuseStep 4791467 = 7187201) B7187201
theorem B2129095 : Blo 1682041 2129095 := bstep (se 1 (by rfl) ⟨1596821, by rfl⟩ : syracuseStep 2129095 = 3193643) B3193643
theorem B12787145 : Blo 1682041 12787145 := bstep (se 2 (by rfl) ⟨4795179, by rfl⟩ : syracuseStep 12787145 = 9590359) B9590359
theorem B5389811 : Blo 1682041 5389811 := bstep (se 1 (by rfl) ⟨4042358, by rfl⟩ : syracuseStep 5389811 = 8084717) B8084717
theorem B3194387 : Blo 1682041 3194387 := bstep (se 1 (by rfl) ⟨2395790, by rfl⟩ : syracuseStep 3194387 = 4791581) B4791581
theorem B4259425 : Blo 1682041 4259425 := bstep (se 2 (by rfl) ⟨1597284, by rfl⟩ : syracuseStep 4259425 = 3194569) B3194569
theorem B3595873 : Blo 1682041 3595873 := bstep (se 2 (by rfl) ⟨1348452, by rfl⟩ : syracuseStep 3595873 = 2696905) B2696905
theorem B17268347 : Blo 1682041 17268347 := bstep (se 1 (by rfl) ⟨12951260, by rfl⟩ : syracuseStep 17268347 = 25902521) B25902521
theorem B3194615 : Blo 1682041 3194615 := bstep (se 1 (by rfl) ⟨2395961, by rfl⟩ : syracuseStep 3194615 = 4791923) B4791923
theorem B8519417 : Blo 1682041 8519417 := bstep (se 2 (by rfl) ⟨3194781, by rfl⟩ : syracuseStep 8519417 = 6389563) B6389563
theorem B18202643 : Blo 1682041 18202643 := bstep (se 1 (by rfl) ⟨13651982, by rfl⟩ : syracuseStep 18202643 = 27303965) B27303965
theorem B21561497 : Blo 1682041 21561497 := bstep (se 2 (by rfl) ⟨8085561, by rfl⟩ : syracuseStep 21561497 = 16171123) B16171123
theorem B2523401 : Blo 1682041 2523401 := bstep (se 2 (by rfl) ⟨946275, by rfl⟩ : syracuseStep 2523401 = 1892551) B1892551
theorem B3031387 : Blo 1682041 3031387 := bstep (se 1 (by rfl) ⟨2273540, by rfl⟩ : syracuseStep 3031387 = 4547081) B4547081
theorem B2523503 : Blo 1682041 2523503 := bstep (se 1 (by rfl) ⟨1892627, by rfl⟩ : syracuseStep 2523503 = 3785255) B3785255
theorem B1892731 : Blo 1682041 1892731 := bstep (se 1 (by rfl) ⟨1419548, by rfl⟩ : syracuseStep 1892731 = 2839097) B2839097
theorem B2695675 : Blo 1682041 2695675 := bstep (se 1 (by rfl) ⟨2021756, by rfl⟩ : syracuseStep 2695675 = 4043513) B4043513
theorem B4260347 : Blo 1682041 4260347 := bstep (se 1 (by rfl) ⟨3195260, by rfl⟩ : syracuseStep 4260347 = 6390521) B6390521
theorem B2523719 : Blo 1682041 2523719 := bstep (se 1 (by rfl) ⟨1892789, by rfl⟩ : syracuseStep 2523719 = 3785579) B3785579
theorem B2523755 : Blo 1682041 2523755 := bstep (se 1 (by rfl) ⟨1892816, by rfl⟩ : syracuseStep 2523755 = 3785633) B3785633
theorem B9101969 : Blo 1682041 9101969 := bstep (se 2 (by rfl) ⟨3413238, by rfl⟩ : syracuseStep 9101969 = 6826477) B6826477
theorem B5677721 : Blo 1682041 5677721 := bstep (se 2 (by rfl) ⟨2129145, by rfl⟩ : syracuseStep 5677721 = 4258291) B4258291
theorem B3785399 : Blo 1682041 3785399 := bstep (se 1 (by rfl) ⟨2839049, by rfl⟩ : syracuseStep 3785399 = 5678099) B5678099
theorem B18703163 : Blo 1682041 18703163 := bstep (se 1 (by rfl) ⟨14027372, by rfl⟩ : syracuseStep 18703163 = 28054745) B28054745
theorem B2523983 : Blo 1682041 2523983 := bstep (se 1 (by rfl) ⟨1892987, by rfl⟩ : syracuseStep 2523983 = 3785975) B3785975
theorem B1893199 : Blo 1682041 1893199 := bstep (se 1 (by rfl) ⟨1419899, by rfl⟩ : syracuseStep 1893199 = 2839799) B2839799
theorem B3785615 : Blo 1682041 3785615 := bstep (se 1 (by rfl) ⟨2839211, by rfl⟩ : syracuseStep 3785615 = 5678423) B5678423
theorem B14369683 : Blo 1682041 14369683 := bstep (se 1 (by rfl) ⟨10777262, by rfl⟩ : syracuseStep 14369683 = 21554525) B21554525
theorem B32793497 : Blo 1682041 32793497 := bstep (se 2 (by rfl) ⟨12297561, by rfl⟩ : syracuseStep 32793497 = 24595123) B24595123
theorem B4858871 : Blo 1682041 4858871 := bstep (se 1 (by rfl) ⟨3644153, by rfl⟩ : syracuseStep 4858871 = 7288307) B7288307
theorem B25609223 : Blo 1682041 25609223 := bstep (se 1 (by rfl) ⟨19206917, by rfl⟩ : syracuseStep 25609223 = 38413835) B38413835
theorem B36398173 : Blo 1682041 36398173 := bstep (se 3 (by rfl) ⟨6824657, by rfl⟩ : syracuseStep 36398173 = 13649315) B13649315
theorem B4547773 : Blo 1682041 4547773 := bstep (se 3 (by rfl) ⟨852707, by rfl⟩ : syracuseStep 4547773 = 1705415) B1705415
theorem B17269955 : Blo 1682041 17269955 := bstep (se 1 (by rfl) ⟨12952466, by rfl⟩ : syracuseStep 17269955 = 25904933) B25904933
theorem B4547783 : Blo 1682041 4547783 := bstep (se 1 (by rfl) ⟨3410837, by rfl⟩ : syracuseStep 4547783 = 6821675) B6821675
theorem B2524379 : Blo 1682041 2524379 := bstep (se 1 (by rfl) ⟨1893284, by rfl⟩ : syracuseStep 2524379 = 3786569) B3786569
theorem B1893595 : Blo 1682041 1893595 := bstep (se 1 (by rfl) ⟨1420196, by rfl⟩ : syracuseStep 1893595 = 2840393) B2840393
theorem B5391593 : Blo 1682041 5391593 := bstep (se 2 (by rfl) ⟨2021847, by rfl⟩ : syracuseStep 5391593 = 4043695) B4043695
theorem B2524553 : Blo 1682041 2524553 := bstep (se 2 (by rfl) ⟨946707, by rfl⟩ : syracuseStep 2524553 = 1893415) B1893415
theorem B4261319 : Blo 1682041 4261319 := bstep (se 1 (by rfl) ⟨3195989, by rfl⟩ : syracuseStep 4261319 = 6391979) B6391979
theorem B34538995 : Blo 1682041 34538995 := bstep (se 1 (by rfl) ⟨25904246, by rfl⟩ : syracuseStep 34538995 = 51808493) B51808493
theorem B4261369 : Blo 1682041 4261369 := bstep (se 2 (by rfl) ⟨1598013, by rfl⟩ : syracuseStep 4261369 = 3196027) B3196027
theorem B1893883 : Blo 1682041 1893883 := bstep (se 1 (by rfl) ⟨1420412, by rfl⟩ : syracuseStep 1893883 = 2840825) B2840825
theorem B3786335 : Blo 1682041 3786335 := bstep (se 1 (by rfl) ⟨2839751, by rfl⟩ : syracuseStep 3786335 = 5679503) B5679503
theorem B46048925 : Blo 1682041 46048925 := bstep (se 3 (by rfl) ⟨8634173, by rfl⟩ : syracuseStep 46048925 = 17268347) B17268347
theorem B1894063 : Blo 1682041 1894063 := bstep (se 1 (by rfl) ⟨1420547, by rfl⟩ : syracuseStep 1894063 = 2841095) B2841095
theorem B2524907 : Blo 1682041 2524907 := bstep (se 1 (by rfl) ⟨1893680, by rfl⟩ : syracuseStep 2524907 = 3787361) B3787361
theorem B4261673 : Blo 1682041 4261673 := bstep (se 2 (by rfl) ⟨1598127, by rfl⟩ : syracuseStep 4261673 = 3196255) B3196255
theorem B3786551 : Blo 1682041 3786551 := bstep (se 1 (by rfl) ⟨2839913, by rfl⟩ : syracuseStep 3786551 = 5679827) B5679827
theorem B4794167 : Blo 1682041 4794167 := bstep (se 1 (by rfl) ⟨3595625, by rfl⟩ : syracuseStep 4794167 = 7191251) B7191251
theorem B14370641 : Blo 1682041 14370641 := bstep (se 2 (by rfl) ⟨5388990, by rfl⟩ : syracuseStep 14370641 = 10777981) B10777981
theorem B36407171 : Blo 1682041 36407171 := bstep (se 1 (by rfl) ⟨27305378, by rfl⟩ : syracuseStep 36407171 = 54610757) B54610757
theorem B2525135 : Blo 1682041 2525135 := bstep (se 1 (by rfl) ⟨1893851, by rfl⟩ : syracuseStep 2525135 = 3787703) B3787703
theorem B1894351 : Blo 1682041 1894351 := bstep (se 1 (by rfl) ⟨1420763, by rfl⟩ : syracuseStep 1894351 = 2841527) B2841527
theorem B3786857 : Blo 1682041 3786857 := bstep (se 2 (by rfl) ⟨1420071, by rfl⟩ : syracuseStep 3786857 = 2840143) B2840143
theorem B5679233 : Blo 1682041 5679233 := bstep (se 2 (by rfl) ⟨2129712, by rfl⟩ : syracuseStep 5679233 = 4259425) B4259425
theorem B4794497 : Blo 1682041 4794497 := bstep (se 2 (by rfl) ⟨1797936, by rfl⟩ : syracuseStep 4794497 = 3595873) B3595873
theorem B4262017 : Blo 1682041 4262017 := bstep (se 2 (by rfl) ⟨1598256, by rfl⟩ : syracuseStep 4262017 = 3196513) B3196513
theorem B6391993 : Blo 1682041 6391993 := bstep (se 2 (by rfl) ⟨2396997, by rfl⟩ : syracuseStep 6391993 = 4793995) B4793995
theorem B8522009 : Blo 1682041 8522009 := bstep (se 2 (by rfl) ⟨3195753, by rfl⟩ : syracuseStep 8522009 = 6391507) B6391507
theorem B2525531 : Blo 1682041 2525531 := bstep (se 1 (by rfl) ⟨1894148, by rfl⟩ : syracuseStep 2525531 = 3788297) B3788297
theorem B18188711 : Blo 1682041 18188711 := bstep (se 1 (by rfl) ⟨13641533, by rfl⟩ : syracuseStep 18188711 = 27283067) B27283067
theorem B5679611 : Blo 1682041 5679611 := bstep (se 1 (by rfl) ⟨4259708, by rfl⟩ : syracuseStep 5679611 = 8519417) B8519417
theorem B2525759 : Blo 1682041 2525759 := bstep (se 1 (by rfl) ⟨1894319, by rfl⟩ : syracuseStep 2525759 = 3788639) B3788639
theorem B3787343 : Blo 1682041 3787343 := bstep (se 1 (by rfl) ⟨2840507, by rfl⟩ : syracuseStep 3787343 = 5681015) B5681015
theorem B2525879 : Blo 1682041 2525879 := bstep (se 1 (by rfl) ⟨1894409, by rfl⟩ : syracuseStep 2525879 = 3788819) B3788819
theorem B7785155 : Blo 1682041 7785155 := bstep (se 1 (by rfl) ⟨5838866, by rfl⟩ : syracuseStep 7785155 = 11677733) B11677733
theorem B1682143 : Blo 1682041 1682143 := bstep (se 1 (by rfl) ⟨1261607, by rfl⟩ : syracuseStep 1682143 = 2523215) B2523215
theorem B3787487 : Blo 1682041 3787487 := bstep (se 1 (by rfl) ⟨2840615, by rfl⟩ : syracuseStep 3787487 = 5681231) B5681231
theorem B14379767 : Blo 1682041 14379767 := bstep (se 1 (by rfl) ⟨10784825, by rfl⟩ : syracuseStep 14379767 = 21569651) B21569651
theorem B1682223 : Blo 1682041 1682223 := bstep (se 1 (by rfl) ⟨1261667, by rfl⟩ : syracuseStep 1682223 = 2523335) B2523335
theorem B4041551 : Blo 1682041 4041551 := bstep (se 1 (by rfl) ⟨3031163, by rfl⟩ : syracuseStep 4041551 = 6062327) B6062327
theorem B1682331 : Blo 1682041 1682331 := bstep (se 1 (by rfl) ⟨1261748, by rfl⟩ : syracuseStep 1682331 = 2523497) B2523497
theorem B5680043 : Blo 1682041 5680043 := bstep (se 1 (by rfl) ⟨4260032, by rfl⟩ : syracuseStep 5680043 = 8520065) B8520065
theorem B1682383 : Blo 1682041 1682383 := bstep (se 1 (by rfl) ⟨1261787, by rfl⟩ : syracuseStep 1682383 = 2523575) B2523575
theorem B3787739 : Blo 1682041 3787739 := bstep (se 1 (by rfl) ⟨2840804, by rfl⟩ : syracuseStep 3787739 = 5681609) B5681609
theorem B1682407 : Blo 1682041 1682407 := bstep (se 1 (by rfl) ⟨1261805, by rfl⟩ : syracuseStep 1682407 = 2523611) B2523611
theorem B3787919 : Blo 1682041 3787919 := bstep (se 1 (by rfl) ⟨2840939, by rfl⟩ : syracuseStep 3787919 = 5681879) B5681879
theorem B2395369 : Blo 1682041 2395369 := bstep (se 2 (by rfl) ⟨898263, by rfl⟩ : syracuseStep 2395369 = 1796527) B1796527
theorem B3788009 : Blo 1682041 3788009 := bstep (se 2 (by rfl) ⟨1420503, by rfl⟩ : syracuseStep 3788009 = 2841007) B2841007
theorem B1682719 : Blo 1682041 1682719 := bstep (se 1 (by rfl) ⟨1262039, by rfl⟩ : syracuseStep 1682719 = 2524079) B2524079
theorem B3788063 : Blo 1682041 3788063 := bstep (se 1 (by rfl) ⟨2841047, by rfl⟩ : syracuseStep 3788063 = 5682095) B5682095
theorem B1682779 : Blo 1682041 1682779 := bstep (se 1 (by rfl) ⟨1262084, by rfl⟩ : syracuseStep 1682779 = 2524169) B2524169
theorem B8088929 : Blo 1682041 8088929 := bstep (se 2 (by rfl) ⟨3033348, by rfl⟩ : syracuseStep 8088929 = 6066697) B6066697
theorem B1682799 : Blo 1682041 1682799 := bstep (se 1 (by rfl) ⟨1262099, by rfl⟩ : syracuseStep 1682799 = 2524199) B2524199
theorem B5836151 : Blo 1682041 5836151 := bstep (se 1 (by rfl) ⟨4377113, by rfl⟩ : syracuseStep 5836151 = 8754227) B8754227
theorem B7187849 : Blo 1682041 7187849 := bstep (se 2 (by rfl) ⟨2695443, by rfl⟩ : syracuseStep 7187849 = 5390887) B5390887
theorem B1682855 : Blo 1682041 1682855 := bstep (se 1 (by rfl) ⟨1262141, by rfl⟩ : syracuseStep 1682855 = 2524283) B2524283
theorem B10235335 : Blo 1682041 10235335 := bstep (se 1 (by rfl) ⟨7676501, by rfl⟩ : syracuseStep 10235335 = 15353003) B15353003
theorem B5680583 : Blo 1682041 5680583 := bstep (se 1 (by rfl) ⟨4260437, by rfl⟩ : syracuseStep 5680583 = 8520875) B8520875
theorem B3239417 : Blo 1682041 3239417 := bstep (se 2 (by rfl) ⟨1214781, by rfl⟩ : syracuseStep 3239417 = 2429563) B2429563
theorem B1682939 : Blo 1682041 1682939 := bstep (se 1 (by rfl) ⟨1262204, by rfl⟩ : syracuseStep 1682939 = 2524409) B2524409
theorem B1683007 : Blo 1682041 1683007 := bstep (se 1 (by rfl) ⟨1262255, by rfl⟩ : syracuseStep 1683007 = 2524511) B2524511
theorem B1683015 : Blo 1682041 1683015 := bstep (se 1 (by rfl) ⟨1262261, by rfl⟩ : syracuseStep 1683015 = 2524523) B2524523
theorem B62221933 : Blo 1682041 62221933 := bstep (se 3 (by rfl) ⟨11666612, by rfl⟩ : syracuseStep 62221933 = 23333225) B23333225
theorem B11521709 : Blo 1682041 11521709 := bstep (se 3 (by rfl) ⟨2160320, by rfl⟩ : syracuseStep 11521709 = 4320641) B4320641
theorem B1683167 : Blo 1682041 1683167 := bstep (se 1 (by rfl) ⟨1262375, by rfl⟩ : syracuseStep 1683167 = 2524751) B2524751
theorem B5680907 : Blo 1682041 5680907 := bstep (se 1 (by rfl) ⟨4260680, by rfl⟩ : syracuseStep 5680907 = 8521361) B8521361
theorem B3788585 : Blo 1682041 3788585 := bstep (se 2 (by rfl) ⟨1420719, by rfl⟩ : syracuseStep 3788585 = 2841439) B2841439
theorem B1683247 : Blo 1682041 1683247 := bstep (se 1 (by rfl) ⟨1262435, by rfl⟩ : syracuseStep 1683247 = 2524871) B2524871
theorem B1683355 : Blo 1682041 1683355 := bstep (se 1 (by rfl) ⟨1262516, by rfl⟩ : syracuseStep 1683355 = 2525033) B2525033
theorem B1683407 : Blo 1682041 1683407 := bstep (se 1 (by rfl) ⟨1262555, by rfl⟩ : syracuseStep 1683407 = 2525111) B2525111
theorem B11513821 : Blo 1682041 11513821 := bstep (se 3 (by rfl) ⟨2158841, by rfl⟩ : syracuseStep 11513821 = 4317683) B4317683
theorem B1683431 : Blo 1682041 1683431 := bstep (se 1 (by rfl) ⟨1262573, by rfl⟩ : syracuseStep 1683431 = 2525147) B2525147
theorem B16396289 : Blo 1682041 16396289 := bstep (se 2 (by rfl) ⟨6148608, by rfl⟩ : syracuseStep 16396289 = 12297217) B12297217
theorem B276377615 : Blo 1682041 276377615 := bstep (se 1 (by rfl) ⟨207283211, by rfl⟩ : syracuseStep 276377615 = 414566423) B414566423
theorem B5681177 : Blo 1682041 5681177 := bstep (se 2 (by rfl) ⟨2130441, by rfl⟩ : syracuseStep 5681177 = 4260883) B4260883
theorem B1945819 : Blo 1682041 1945819 := bstep (se 1 (by rfl) ⟨1459364, by rfl⟩ : syracuseStep 1945819 = 2918729) B2918729
theorem B27283715 : Blo 1682041 27283715 := bstep (se 1 (by rfl) ⟨20462786, by rfl⟩ : syracuseStep 27283715 = 40925573) B40925573
theorem B2838793 : Blo 1682041 2838793 := bstep (se 2 (by rfl) ⟨1064547, by rfl⟩ : syracuseStep 2838793 = 2129095) B2129095
theorem B1683743 : Blo 1682041 1683743 := bstep (se 1 (by rfl) ⟨1262807, by rfl⟩ : syracuseStep 1683743 = 2525615) B2525615
theorem B30699809 : Blo 1682041 30699809 := bstep (se 2 (by rfl) ⟨11512428, by rfl⟩ : syracuseStep 30699809 = 23024857) B23024857
theorem B1683803 : Blo 1682041 1683803 := bstep (se 1 (by rfl) ⟨1262852, by rfl⟩ : syracuseStep 1683803 = 2525705) B2525705
theorem B1683823 : Blo 1682041 1683823 := bstep (se 1 (by rfl) ⟨1262867, by rfl⟩ : syracuseStep 1683823 = 2525735) B2525735
theorem B18198917 : Blo 1682041 18198917 := bstep (se 4 (by rfl) ⟨1706148, by rfl⟩ : syracuseStep 18198917 = 3412297) B3412297
theorem B1683879 : Blo 1682041 1683879 := bstep (se 1 (by rfl) ⟨1262909, by rfl⟩ : syracuseStep 1683879 = 2525819) B2525819
theorem B8516015 : Blo 1682041 8516015 := bstep (se 1 (by rfl) ⟨6387011, by rfl⟩ : syracuseStep 8516015 = 12774023) B12774023
theorem B1683963 : Blo 1682041 1683963 := bstep (se 1 (by rfl) ⟨1262972, by rfl⟩ : syracuseStep 1683963 = 2525945) B2525945
theorem B1684031 : Blo 1682041 1684031 := bstep (se 1 (by rfl) ⟨1263023, by rfl⟩ : syracuseStep 1684031 = 2526047) B2526047
theorem B1684039 : Blo 1682041 1684039 := bstep (se 1 (by rfl) ⟨1263029, by rfl⟩ : syracuseStep 1684039 = 2526059) B2526059
theorem B6386633 : Blo 1682041 6386633 := bstep (se 2 (by rfl) ⟨2394987, by rfl⟩ : syracuseStep 6386633 = 4789975) B4789975
theorem B8524763 : Blo 1682041 8524763 := bstep (se 1 (by rfl) ⟨6393572, by rfl⟩ : syracuseStep 8524763 = 12787145) B12787145
theorem B3593207 : Blo 1682041 3593207 := bstep (se 1 (by rfl) ⟨2694905, by rfl⟩ : syracuseStep 3593207 = 5389811) B5389811
theorem B8524925 : Blo 1682041 8524925 := bstep (se 3 (by rfl) ⟨1598423, by rfl⟩ : syracuseStep 8524925 = 3196847) B3196847
theorem B4551805 : Blo 1682041 4551805 := bstep (se 3 (by rfl) ⟨853463, by rfl⟩ : syracuseStep 4551805 = 1706927) B1706927
theorem B7189661 : Blo 1682041 7189661 := bstep (se 3 (by rfl) ⟨1348061, by rfl⟩ : syracuseStep 7189661 = 2696123) B2696123
theorem B6386921 : Blo 1682041 6386921 := bstep (se 2 (by rfl) ⟨2395095, by rfl⟩ : syracuseStep 6386921 = 4790191) B4790191
theorem B5682419 : Blo 1682041 5682419 := bstep (se 1 (by rfl) ⟨4261814, by rfl⟩ : syracuseStep 5682419 = 8523629) B8523629
theorem B8090867 : Blo 1682041 8090867 := bstep (se 1 (by rfl) ⟨6068150, by rfl⟩ : syracuseStep 8090867 = 12136301) B12136301
theorem B5682527 : Blo 1682041 5682527 := bstep (se 1 (by rfl) ⟨4261895, by rfl⟩ : syracuseStep 5682527 = 8523791) B8523791
theorem B8516987 : Blo 1682041 8516987 := bstep (se 1 (by rfl) ⟨6387740, by rfl⟩ : syracuseStep 8516987 = 12775481) B12775481
theorem B16176509 : Blo 1682041 16176509 := bstep (se 3 (by rfl) ⟨3033095, by rfl⟩ : syracuseStep 16176509 = 6066191) B6066191
theorem B9590177 : Blo 1682041 9590177 := bstep (se 2 (by rfl) ⟨3596316, by rfl⟩ : syracuseStep 9590177 = 7192633) B7192633
theorem B6387133 : Blo 1682041 6387133 := bstep (se 3 (by rfl) ⟨1197587, by rfl⟩ : syracuseStep 6387133 = 2395175) B2395175
theorem B8525249 : Blo 1682041 8525249 := bstep (se 2 (by rfl) ⟨3196968, by rfl⟩ : syracuseStep 8525249 = 6393937) B6393937
theorem B18191911 : Blo 1682041 18191911 := bstep (se 1 (by rfl) ⟨13643933, by rfl⟩ : syracuseStep 18191911 = 27287867) B27287867
theorem B2078303 : Blo 1682041 2078303 := bstep (se 1 (by rfl) ⟨1558727, by rfl⟩ : syracuseStep 2078303 = 3117455) B3117455
theorem B32347781 : Blo 1682041 32347781 := bstep (se 4 (by rfl) ⟨3032604, by rfl⟩ : syracuseStep 32347781 = 6065209) B6065209
theorem B2840251 : Blo 1682041 2840251 := bstep (se 1 (by rfl) ⟨2130188, by rfl⟩ : syracuseStep 2840251 = 4260377) B4260377
theorem B8083255 : Blo 1682041 8083255 := bstep (se 1 (by rfl) ⟨6062441, by rfl⟩ : syracuseStep 8083255 = 12124883) B12124883
theorem B15357815 : Blo 1682041 15357815 := bstep (se 1 (by rfl) ⟨11518361, by rfl⟩ : syracuseStep 15357815 = 23036723) B23036723
theorem B6821921 : Blo 1682041 6821921 := bstep (se 2 (by rfl) ⟨2558220, by rfl⟩ : syracuseStep 6821921 = 5116441) B5116441
theorem B10778903 : Blo 1682041 10778903 := bstep (se 1 (by rfl) ⟨8084177, by rfl⟩ : syracuseStep 10778903 = 16168355) B16168355
theorem B17267033 : Blo 1682041 17267033 := bstep (se 2 (by rfl) ⟨6475137, by rfl⟩ : syracuseStep 17267033 = 12950275) B12950275
theorem B12777911 : Blo 1682041 12777911 := bstep (se 1 (by rfl) ⟨9583433, by rfl⟩ : syracuseStep 12777911 = 19166867) B19166867
theorem B3193339 : Blo 1682041 3193339 := bstep (se 1 (by rfl) ⟨2395004, by rfl⟩ : syracuseStep 3193339 = 4790009) B4790009
theorem B12130879 : Blo 1682041 12130879 := bstep (se 1 (by rfl) ⟨9098159, by rfl⟩ : syracuseStep 12130879 = 18196319) B18196319
theorem B3193415 : Blo 1682041 3193415 := bstep (se 1 (by rfl) ⟨2395061, by rfl⟩ : syracuseStep 3193415 = 4790123) B4790123
theorem B8518283 : Blo 1682041 8518283 := bstep (se 1 (by rfl) ⟨6388712, by rfl⟩ : syracuseStep 8518283 = 12777425) B12777425
theorem B2841311 : Blo 1682041 2841311 := bstep (se 1 (by rfl) ⟨2130983, by rfl⟩ : syracuseStep 2841311 = 4261967) B4261967
theorem B4258939 : Blo 1682041 4258939 := bstep (se 1 (by rfl) ⟨3194204, by rfl⟩ : syracuseStep 4258939 = 6388409) B6388409
theorem B2841743 : Blo 1682041 2841743 := bstep (se 1 (by rfl) ⟨2131307, by rfl⟩ : syracuseStep 2841743 = 4262615) B4262615
theorem B4791649 : Blo 1682041 4791649 := bstep (se 2 (by rfl) ⟨1796868, by rfl⟩ : syracuseStep 4791649 = 3593737) B3593737
theorem B4046203 : Blo 1682041 4046203 := bstep (se 1 (by rfl) ⟨3034652, by rfl⟩ : syracuseStep 4046203 = 6069305) B6069305
theorem B2022823 : Blo 1682041 2022823 := bstep (se 1 (by rfl) ⟨1517117, by rfl⟩ : syracuseStep 2022823 = 3034235) B3034235
theorem B3194311 : Blo 1682041 3194311 := bstep (se 1 (by rfl) ⟨2395733, by rfl⟩ : syracuseStep 3194311 = 4791467) B4791467
theorem B2129591 : Blo 1682041 2129591 := bstep (se 1 (by rfl) ⟨1597193, by rfl⟩ : syracuseStep 2129591 = 3194387) B3194387
theorem B2129743 : Blo 1682041 2129743 := bstep (se 1 (by rfl) ⟨1597307, by rfl⟩ : syracuseStep 2129743 = 3194615) B3194615
theorem B12787631 : Blo 1682041 12787631 := bstep (se 1 (by rfl) ⟨9590723, by rfl⟩ : syracuseStep 12787631 = 19181447) B19181447
theorem B12132611 : Blo 1682041 12132611 := bstep (se 1 (by rfl) ⟨9099458, by rfl⟩ : syracuseStep 12132611 = 18198917) B18198917
theorem B5677343 : Blo 1682041 5677343 := bstep (se 1 (by rfl) ⟨4258007, by rfl⟩ : syracuseStep 5677343 = 8516015) B8516015
theorem B3785057 : Blo 1682041 3785057 := bstep (se 2 (by rfl) ⟨1419396, by rfl⟩ : syracuseStep 3785057 = 2838793) B2838793
theorem B3785147 : Blo 1682041 3785147 := bstep (se 1 (by rfl) ⟨2838860, by rfl⟩ : syracuseStep 3785147 = 5677721) B5677721
theorem B2523599 : Blo 1682041 2523599 := bstep (se 1 (by rfl) ⟨1892699, by rfl⟩ : syracuseStep 2523599 = 3785399) B3785399
theorem B2523641 : Blo 1682041 2523641 := bstep (se 2 (by rfl) ⟨946365, by rfl⟩ : syracuseStep 2523641 = 1892731) B1892731
theorem B2523743 : Blo 1682041 2523743 := bstep (se 1 (by rfl) ⟨1892807, by rfl⟩ : syracuseStep 2523743 = 3785615) B3785615
theorem B17072815 : Blo 1682041 17072815 := bstep (se 1 (by rfl) ⟨12804611, by rfl⟩ : syracuseStep 17072815 = 25609223) B25609223
theorem B4793107 : Blo 1682041 4793107 := bstep (se 1 (by rfl) ⟨3594830, by rfl⟩ : syracuseStep 4793107 = 7189661) B7189661
theorem B5677991 : Blo 1682041 5677991 := bstep (se 1 (by rfl) ⟨4258493, by rfl⟩ : syracuseStep 5677991 = 8516987) B8516987
theorem B2524223 : Blo 1682041 2524223 := bstep (se 1 (by rfl) ⟨1893167, by rfl⟩ : syracuseStep 2524223 = 3786335) B3786335
theorem B2524265 : Blo 1682041 2524265 := bstep (se 2 (by rfl) ⟨946599, by rfl⟩ : syracuseStep 2524265 = 1893199) B1893199
theorem B2524367 : Blo 1682041 2524367 := bstep (se 1 (by rfl) ⟨1893275, by rfl⟩ : syracuseStep 2524367 = 3786551) B3786551
theorem B3196111 : Blo 1682041 3196111 := bstep (se 1 (by rfl) ⟨2397083, by rfl⟩ : syracuseStep 3196111 = 4794167) B4794167
theorem B4547947 : Blo 1682041 4547947 := bstep (se 1 (by rfl) ⟨3410960, by rfl⟩ : syracuseStep 4547947 = 6821921) B6821921
theorem B2524571 : Blo 1682041 2524571 := bstep (se 1 (by rfl) ⟨1893428, by rfl⟩ : syracuseStep 2524571 = 3786857) B3786857
theorem B3786155 : Blo 1682041 3786155 := bstep (se 1 (by rfl) ⟨2839616, by rfl⟩ : syracuseStep 3786155 = 5679233) B5679233
theorem B3196331 : Blo 1682041 3196331 := bstep (se 1 (by rfl) ⟨2397248, by rfl⟩ : syracuseStep 3196331 = 4794497) B4794497
theorem B48530897 : Blo 1682041 48530897 := bstep (se 2 (by rfl) ⟨18199086, by rfl⟩ : syracuseStep 48530897 = 36398173) B36398173
theorem B5678585 : Blo 1682041 5678585 := bstep (se 2 (by rfl) ⟨2129469, by rfl⟩ : syracuseStep 5678585 = 4258939) B4258939
theorem B7185935 : Blo 1682041 7185935 := bstep (se 1 (by rfl) ⟨5389451, by rfl⟩ : syracuseStep 7185935 = 10778903) B10778903
theorem B6063697 : Blo 1682041 6063697 := bstep (se 2 (by rfl) ⟨2273886, by rfl⟩ : syracuseStep 6063697 = 4547773) B4547773
theorem B12125807 : Blo 1682041 12125807 := bstep (se 1 (by rfl) ⟨9094355, by rfl⟩ : syracuseStep 12125807 = 18188711) B18188711
theorem B2524793 : Blo 1682041 2524793 := bstep (se 2 (by rfl) ⟨946797, by rfl⟩ : syracuseStep 2524793 = 1893595) B1893595
theorem B3786407 : Blo 1682041 3786407 := bstep (se 1 (by rfl) ⟨2839805, by rfl⟩ : syracuseStep 3786407 = 5679611) B5679611
theorem B2524895 : Blo 1682041 2524895 := bstep (se 1 (by rfl) ⟨1893671, by rfl⟩ : syracuseStep 2524895 = 3787343) B3787343
theorem B5678855 : Blo 1682041 5678855 := bstep (se 1 (by rfl) ⟨4259141, by rfl⟩ : syracuseStep 5678855 = 8518283) B8518283
theorem B5678909 : Blo 1682041 5678909 := bstep (se 3 (by rfl) ⟨1064795, by rfl⟩ : syracuseStep 5678909 = 2129591) B2129591
theorem B2524991 : Blo 1682041 2524991 := bstep (se 1 (by rfl) ⟨1893743, by rfl⟩ : syracuseStep 2524991 = 3787487) B3787487
theorem B1894207 : Blo 1682041 1894207 := bstep (se 1 (by rfl) ⟨1420655, by rfl⟩ : syracuseStep 1894207 = 2841311) B2841311
theorem B9586511 : Blo 1682041 9586511 := bstep (se 1 (by rfl) ⟨7189883, by rfl⟩ : syracuseStep 9586511 = 14379767) B14379767
theorem B3786695 : Blo 1682041 3786695 := bstep (se 1 (by rfl) ⟨2840021, by rfl⟩ : syracuseStep 3786695 = 5680043) B5680043
theorem B2525159 : Blo 1682041 2525159 := bstep (se 1 (by rfl) ⟨1893869, by rfl⟩ : syracuseStep 2525159 = 3787739) B3787739
theorem B2525177 : Blo 1682041 2525177 := bstep (se 2 (by rfl) ⟨946941, by rfl⟩ : syracuseStep 2525177 = 1893883) B1893883
theorem B2525279 : Blo 1682041 2525279 := bstep (se 1 (by rfl) ⟨1893959, by rfl⟩ : syracuseStep 2525279 = 3787919) B3787919
theorem B1894495 : Blo 1682041 1894495 := bstep (se 1 (by rfl) ⟨1420871, by rfl⟩ : syracuseStep 1894495 = 2841743) B2841743
theorem B82962577 : Blo 1682041 82962577 := bstep (se 2 (by rfl) ⟨31110966, by rfl⟩ : syracuseStep 82962577 = 62221933) B62221933
theorem B2525339 : Blo 1682041 2525339 := bstep (se 1 (by rfl) ⟨1894004, by rfl⟩ : syracuseStep 2525339 = 3788009) B3788009
theorem B49875101 : Blo 1682041 49875101 := bstep (se 3 (by rfl) ⟨9351581, by rfl⟩ : syracuseStep 49875101 = 18703163) B18703163
theorem B2525375 : Blo 1682041 2525375 := bstep (se 1 (by rfl) ⟨1894031, by rfl⟩ : syracuseStep 2525375 = 3788063) B3788063
theorem B2525417 : Blo 1682041 2525417 := bstep (se 2 (by rfl) ⟨947031, by rfl⟩ : syracuseStep 2525417 = 1894063) B1894063
theorem B5392619 : Blo 1682041 5392619 := bstep (se 1 (by rfl) ⟨4044464, by rfl⟩ : syracuseStep 5392619 = 8088929) B8088929
theorem B3787001 : Blo 1682041 3787001 := bstep (se 2 (by rfl) ⟨1420125, by rfl⟩ : syracuseStep 3787001 = 2840251) B2840251
theorem B3787055 : Blo 1682041 3787055 := bstep (se 1 (by rfl) ⟨2840291, by rfl⟩ : syracuseStep 3787055 = 5680583) B5680583
theorem B3787271 : Blo 1682041 3787271 := bstep (se 1 (by rfl) ⟨2840453, by rfl⟩ : syracuseStep 3787271 = 5680907) B5680907
theorem B2525723 : Blo 1682041 2525723 := bstep (se 1 (by rfl) ⟨1894292, by rfl⟩ : syracuseStep 2525723 = 3788585) B3788585
theorem B2525801 : Blo 1682041 2525801 := bstep (se 2 (by rfl) ⟨947175, by rfl⟩ : syracuseStep 2525801 = 1894351) B1894351
theorem B10930859 : Blo 1682041 10930859 := bstep (se 1 (by rfl) ⟨8198144, by rfl⟩ : syracuseStep 10930859 = 16396289) B16396289
theorem B12135095 : Blo 1682041 12135095 := bstep (se 1 (by rfl) ⟨9101321, by rfl⟩ : syracuseStep 12135095 = 18202643) B18202643
theorem B3787451 : Blo 1682041 3787451 := bstep (se 1 (by rfl) ⟨2840588, by rfl⟩ : syracuseStep 3787451 = 5681177) B5681177
theorem B18189143 : Blo 1682041 18189143 := bstep (se 1 (by rfl) ⟨13641857, by rfl⟩ : syracuseStep 18189143 = 27283715) B27283715
theorem B1682267 : Blo 1682041 1682267 := bstep (se 1 (by rfl) ⟨1261700, by rfl⟩ : syracuseStep 1682267 = 2523401) B2523401
theorem B20466539 : Blo 1682041 20466539 := bstep (se 1 (by rfl) ⟨15349904, by rfl⟩ : syracuseStep 20466539 = 30699809) B30699809
theorem B1682335 : Blo 1682041 1682335 := bstep (se 1 (by rfl) ⟨1261751, by rfl⟩ : syracuseStep 1682335 = 2523503) B2523503
theorem B8522657 : Blo 1682041 8522657 := bstep (se 2 (by rfl) ⟨3195996, by rfl⟩ : syracuseStep 8522657 = 6391993) B6391993
theorem B1682479 : Blo 1682041 1682479 := bstep (se 1 (by rfl) ⟨1261859, by rfl⟩ : syracuseStep 1682479 = 2523719) B2523719
theorem B1682503 : Blo 1682041 1682503 := bstep (se 1 (by rfl) ⟨1261877, by rfl⟩ : syracuseStep 1682503 = 2523755) B2523755
theorem B12127421 : Blo 1682041 12127421 := bstep (se 3 (by rfl) ⟨2273891, by rfl⟩ : syracuseStep 12127421 = 4547783) B4547783
theorem B1682655 : Blo 1682041 1682655 := bstep (se 1 (by rfl) ⟨1261991, by rfl⟩ : syracuseStep 1682655 = 2523983) B2523983
theorem B24276293 : Blo 1682041 24276293 := bstep (se 4 (by rfl) ⟨2275902, by rfl⟩ : syracuseStep 24276293 = 4551805) B4551805
theorem B16174505 : Blo 1682041 16174505 := bstep (se 2 (by rfl) ⟨6065439, by rfl⟩ : syracuseStep 16174505 = 12130879) B12130879
theorem B11513303 : Blo 1682041 11513303 := bstep (se 1 (by rfl) ⟨8634977, by rfl⟩ : syracuseStep 11513303 = 17269955) B17269955
theorem B1682919 : Blo 1682041 1682919 := bstep (se 1 (by rfl) ⟨1262189, by rfl⟩ : syracuseStep 1682919 = 2524379) B2524379
theorem B3788279 : Blo 1682041 3788279 := bstep (se 1 (by rfl) ⟨2841209, by rfl⟩ : syracuseStep 3788279 = 5682419) B5682419
theorem B3788351 : Blo 1682041 3788351 := bstep (se 1 (by rfl) ⟨2841263, by rfl⟩ : syracuseStep 3788351 = 5682527) B5682527
theorem B10784339 : Blo 1682041 10784339 := bstep (se 1 (by rfl) ⟨8088254, by rfl⟩ : syracuseStep 10784339 = 16176509) B16176509
theorem B1683035 : Blo 1682041 1683035 := bstep (se 1 (by rfl) ⟨1262276, by rfl⟩ : syracuseStep 1683035 = 2524553) B2524553
theorem B6393451 : Blo 1682041 6393451 := bstep (se 1 (by rfl) ⟨4795088, by rfl⟩ : syracuseStep 6393451 = 9590177) B9590177
theorem B21565187 : Blo 1682041 21565187 := bstep (se 1 (by rfl) ⟨16173890, by rfl⟩ : syracuseStep 21565187 = 32347781) B32347781
theorem B1683271 : Blo 1682041 1683271 := bstep (se 1 (by rfl) ⟨1262453, by rfl⟩ : syracuseStep 1683271 = 2524907) B2524907
theorem B9580427 : Blo 1682041 9580427 := bstep (se 1 (by rfl) ⟨7185320, by rfl⟩ : syracuseStep 9580427 = 14370641) B14370641
theorem B1683423 : Blo 1682041 1683423 := bstep (se 1 (by rfl) ⟨1262567, by rfl⟩ : syracuseStep 1683423 = 2525135) B2525135
theorem B8638445 : Blo 1682041 8638445 := bstep (se 3 (by rfl) ⟨1619708, by rfl⟩ : syracuseStep 8638445 = 3239417) B3239417
theorem B5681339 : Blo 1682041 5681339 := bstep (se 1 (by rfl) ⟨4261004, by rfl⟩ : syracuseStep 5681339 = 8522009) B8522009
theorem B1683687 : Blo 1682041 1683687 := bstep (se 1 (by rfl) ⟨1262765, by rfl⟩ : syracuseStep 1683687 = 2525531) B2525531
theorem B5542141 : Blo 1682041 5542141 := bstep (se 3 (by rfl) ⟨1039151, by rfl⟩ : syracuseStep 5542141 = 2078303) B2078303
theorem B1683839 : Blo 1682041 1683839 := bstep (se 1 (by rfl) ⟨1262879, by rfl⟩ : syracuseStep 1683839 = 2525759) B2525759
theorem B1683919 : Blo 1682041 1683919 := bstep (se 1 (by rfl) ⟨1262939, by rfl⟩ : syracuseStep 1683919 = 2525879) B2525879
theorem B5190103 : Blo 1682041 5190103 := bstep (se 1 (by rfl) ⟨3892577, by rfl⟩ : syracuseStep 5190103 = 7785155) B7785155
theorem B16167397 : Blo 1682041 16167397 := bstep (se 4 (by rfl) ⟨1515693, by rfl⟩ : syracuseStep 16167397 = 3031387) B3031387
theorem B5394937 : Blo 1682041 5394937 := bstep (se 2 (by rfl) ⟨2023101, by rfl⟩ : syracuseStep 5394937 = 4046203) B4046203
theorem B8516177 : Blo 1682041 8516177 := bstep (se 2 (by rfl) ⟨3193566, by rfl⟩ : syracuseStep 8516177 = 6387133) B6387133
theorem B46051993 : Blo 1682041 46051993 := bstep (se 2 (by rfl) ⟨17269497, by rfl⟩ : syracuseStep 46051993 = 34538995) B34538995
theorem B5681825 : Blo 1682041 5681825 := bstep (se 2 (by rfl) ⟨2130684, by rfl⟩ : syracuseStep 5681825 = 4261369) B4261369
theorem B10777673 : Blo 1682041 10777673 := bstep (se 2 (by rfl) ⟨4041627, by rfl⟩ : syracuseStep 10777673 = 8083255) B8083255
theorem B2839657 : Blo 1682041 2839657 := bstep (se 2 (by rfl) ⟨1064871, by rfl⟩ : syracuseStep 2839657 = 2129743) B2129743
theorem B7681139 : Blo 1682041 7681139 := bstep (se 1 (by rfl) ⟨5760854, by rfl⟩ : syracuseStep 7681139 = 11521709) B11521709
theorem B8525087 : Blo 1682041 8525087 := bstep (se 1 (by rfl) ⟨6393815, by rfl⟩ : syracuseStep 8525087 = 12787631) B12787631
theorem B9581885 : Blo 1682041 9581885 := bstep (se 3 (by rfl) ⟨1796603, by rfl⟩ : syracuseStep 9581885 = 3593207) B3593207
theorem B12956989 : Blo 1682041 12956989 := bstep (se 3 (by rfl) ⟨2429435, by rfl⟩ : syracuseStep 12956989 = 4858871) B4858871
theorem B184251743 : Blo 1682041 184251743 := bstep (se 1 (by rfl) ⟨138188807, by rfl⟩ : syracuseStep 184251743 = 276377615) B276377615
theorem B14374331 : Blo 1682041 14374331 := bstep (se 1 (by rfl) ⟨10780748, by rfl⟩ : syracuseStep 14374331 = 21561497) B21561497
theorem B5682689 : Blo 1682041 5682689 := bstep (se 2 (by rfl) ⟨2131008, by rfl⟩ : syracuseStep 5682689 = 4262017) B4262017
theorem B2594425 : Blo 1682041 2594425 := bstep (se 2 (by rfl) ⟨972909, by rfl⟩ : syracuseStep 2594425 = 1945819) B1945819
theorem B2840231 : Blo 1682041 2840231 := bstep (se 1 (by rfl) ⟨2130173, by rfl⟩ : syracuseStep 2840231 = 4260347) B4260347
theorem B6067979 : Blo 1682041 6067979 := bstep (se 1 (by rfl) ⟨4550984, by rfl⟩ : syracuseStep 6067979 = 9101969) B9101969
theorem B21862331 : Blo 1682041 21862331 := bstep (se 1 (by rfl) ⟨16396748, by rfl⟩ : syracuseStep 21862331 = 32793497) B32793497
theorem B4257755 : Blo 1682041 4257755 := bstep (se 1 (by rfl) ⟨3193316, by rfl⟩ : syracuseStep 4257755 = 6386633) B6386633
theorem B21575645 : Blo 1682041 21575645 := bstep (se 3 (by rfl) ⟨4045433, by rfl⟩ : syracuseStep 21575645 = 8090867) B8090867
theorem B5683175 : Blo 1682041 5683175 := bstep (se 1 (by rfl) ⟨4262381, by rfl⟩ : syracuseStep 5683175 = 8524763) B8524763
theorem B4257785 : Blo 1682041 4257785 := bstep (se 2 (by rfl) ⟨1596669, by rfl⟩ : syracuseStep 4257785 = 3193339) B3193339
theorem B3594233 : Blo 1682041 3594233 := bstep (se 2 (by rfl) ⟨1347837, by rfl⟩ : syracuseStep 3594233 = 2695675) B2695675
theorem B5683283 : Blo 1682041 5683283 := bstep (se 1 (by rfl) ⟨4262462, by rfl⟩ : syracuseStep 5683283 = 8524925) B8524925
theorem B4257947 : Blo 1682041 4257947 := bstep (se 1 (by rfl) ⟨3193460, by rfl⟩ : syracuseStep 4257947 = 6386921) B6386921
theorem B3594395 : Blo 1682041 3594395 := bstep (se 1 (by rfl) ⟨2695796, by rfl⟩ : syracuseStep 3594395 = 5391593) B5391593
theorem B46045421 : Blo 1682041 46045421 := bstep (se 3 (by rfl) ⟨8633516, by rfl⟩ : syracuseStep 46045421 = 17267033) B17267033
theorem B5683499 : Blo 1682041 5683499 := bstep (se 1 (by rfl) ⟨4262624, by rfl⟩ : syracuseStep 5683499 = 8525249) B8525249
theorem B2840879 : Blo 1682041 2840879 := bstep (se 1 (by rfl) ⟨2130659, by rfl⟩ : syracuseStep 2840879 = 4261319) B4261319
theorem B15563069 : Blo 1682041 15563069 := bstep (se 3 (by rfl) ⟨2918075, by rfl⟩ : syracuseStep 15563069 = 5836151) B5836151
theorem B19159577 : Blo 1682041 19159577 := bstep (se 2 (by rfl) ⟨7184841, by rfl⟩ : syracuseStep 19159577 = 14369683) B14369683
theorem B2841115 : Blo 1682041 2841115 := bstep (se 1 (by rfl) ⟨2130836, by rfl⟩ : syracuseStep 2841115 = 4261673) B4261673
theorem B10238543 : Blo 1682041 10238543 := bstep (se 1 (by rfl) ⟨7678907, by rfl⟩ : syracuseStep 10238543 = 15357815) B15357815
theorem B24271447 : Blo 1682041 24271447 := bstep (se 1 (by rfl) ⟨18203585, by rfl⟩ : syracuseStep 24271447 = 36407171) B36407171
theorem B8518607 : Blo 1682041 8518607 := bstep (se 1 (by rfl) ⟨6388955, by rfl⟩ : syracuseStep 8518607 = 12777911) B12777911
theorem B3193825 : Blo 1682041 3193825 := bstep (se 2 (by rfl) ⟨1197684, by rfl⟩ : syracuseStep 3193825 = 2395369) B2395369
theorem B2128943 : Blo 1682041 2128943 := bstep (se 1 (by rfl) ⟨1596707, by rfl⟩ : syracuseStep 2128943 = 3193415) B3193415
theorem B122797133 : Blo 1682041 122797133 := bstep (se 3 (by rfl) ⟨23024462, by rfl⟩ : syracuseStep 122797133 = 46048925) B46048925
theorem B6388865 : Blo 1682041 6388865 := bstep (se 2 (by rfl) ⟨2395824, by rfl⟩ : syracuseStep 6388865 = 4791649) B4791649
theorem B2694367 : Blo 1682041 2694367 := bstep (se 1 (by rfl) ⟨2020775, by rfl⟩ : syracuseStep 2694367 = 4041551) B4041551
theorem B4259081 : Blo 1682041 4259081 := bstep (se 2 (by rfl) ⟨1597155, by rfl⟩ : syracuseStep 4259081 = 3194311) B3194311
theorem B13647113 : Blo 1682041 13647113 := bstep (se 2 (by rfl) ⟨5117667, by rfl⟩ : syracuseStep 13647113 = 10235335) B10235335
theorem B24255881 : Blo 1682041 24255881 := bstep (se 2 (by rfl) ⟨9095955, by rfl⟩ : syracuseStep 24255881 = 18191911) B18191911
theorem B10788389 : Blo 1682041 10788389 := bstep (se 4 (by rfl) ⟨1011411, by rfl⟩ : syracuseStep 10788389 = 2022823) B2022823
theorem B4791899 : Blo 1682041 4791899 := bstep (se 1 (by rfl) ⟨3593924, by rfl⟩ : syracuseStep 4791899 = 7187849) B7187849
theorem B15351761 : Blo 1682041 15351761 := bstep (se 2 (by rfl) ⟨5756910, by rfl⟩ : syracuseStep 15351761 = 11513821) B11513821
theorem B5677181 : Blo 1682041 5677181 := bstep (se 3 (by rfl) ⟨1064471, by rfl⟩ : syracuseStep 5677181 = 2128943) B2128943
theorem B3784895 : Blo 1682041 3784895 := bstep (se 1 (by rfl) ⟨2838671, by rfl⟩ : syracuseStep 3784895 = 5677343) B5677343
theorem B110616769 : Blo 1682041 110616769 := bstep (se 2 (by rfl) ⟨41481288, by rfl⟩ : syracuseStep 110616769 = 82962577) B82962577
theorem B2523371 : Blo 1682041 2523371 := bstep (se 1 (by rfl) ⟨1892528, by rfl⟩ : syracuseStep 2523371 = 3785057) B3785057
theorem B2523431 : Blo 1682041 2523431 := bstep (se 1 (by rfl) ⟨1892573, by rfl⟩ : syracuseStep 2523431 = 3785147) B3785147
theorem B7389521 : Blo 1682041 7389521 := bstep (se 2 (by rfl) ⟨2771070, by rfl⟩ : syracuseStep 7389521 = 5542141) B5542141
theorem B5677451 : Blo 1682041 5677451 := bstep (se 1 (by rfl) ⟨4258088, by rfl⟩ : syracuseStep 5677451 = 8516177) B8516177
theorem B9585053 : Blo 1682041 9585053 := bstep (se 3 (by rfl) ⟨1797197, by rfl⟩ : syracuseStep 9585053 = 3594395) B3594395
theorem B3785327 : Blo 1682041 3785327 := bstep (se 1 (by rfl) ⟨2838995, by rfl⟩ : syracuseStep 3785327 = 5677991) B5677991
theorem B7193249 : Blo 1682041 7193249 := bstep (se 2 (by rfl) ⟨2697468, by rfl⟩ : syracuseStep 7193249 = 5394937) B5394937
theorem B7185115 : Blo 1682041 7185115 := bstep (se 1 (by rfl) ⟨5388836, by rfl⟩ : syracuseStep 7185115 = 10777673) B10777673
theorem B5120759 : Blo 1682041 5120759 := bstep (se 1 (by rfl) ⟨3840569, by rfl⟩ : syracuseStep 5120759 = 7681139) B7681139
theorem B2524103 : Blo 1682041 2524103 := bstep (se 1 (by rfl) ⟨1893077, by rfl⟩ : syracuseStep 2524103 = 3786155) B3786155
theorem B2130887 : Blo 1682041 2130887 := bstep (se 1 (by rfl) ⟨1598165, by rfl⟩ : syracuseStep 2130887 = 3196331) B3196331
theorem B3785723 : Blo 1682041 3785723 := bstep (se 1 (by rfl) ⟨2839292, by rfl⟩ : syracuseStep 3785723 = 5678585) B5678585
theorem B6390809 : Blo 1682041 6390809 := bstep (se 2 (by rfl) ⟨2396553, by rfl⟩ : syracuseStep 6390809 = 4793107) B4793107
theorem B43132013 : Blo 1682041 43132013 := bstep (se 3 (by rfl) ⟨8087252, by rfl⟩ : syracuseStep 43132013 = 16174505) B16174505
theorem B2524271 : Blo 1682041 2524271 := bstep (se 1 (by rfl) ⟨1893203, by rfl⟩ : syracuseStep 2524271 = 3786407) B3786407
theorem B1893487 : Blo 1682041 1893487 := bstep (se 1 (by rfl) ⟨1420115, by rfl⟩ : syracuseStep 1893487 = 2840231) B2840231
theorem B14369957 : Blo 1682041 14369957 := bstep (se 4 (by rfl) ⟨1347183, by rfl⟩ : syracuseStep 14369957 = 2694367) B2694367
theorem B3785903 : Blo 1682041 3785903 := bstep (se 1 (by rfl) ⟨2839427, by rfl⟩ : syracuseStep 3785903 = 5678855) B5678855
theorem B3785939 : Blo 1682041 3785939 := bstep (se 1 (by rfl) ⟨2839454, by rfl⟩ : syracuseStep 3785939 = 5678909) B5678909
theorem B6391007 : Blo 1682041 6391007 := bstep (se 1 (by rfl) ⟨4793255, by rfl⟩ : syracuseStep 6391007 = 9586511) B9586511
theorem B14574887 : Blo 1682041 14574887 := bstep (se 1 (by rfl) ⟨10931165, by rfl⟩ : syracuseStep 14574887 = 21862331) B21862331
theorem B2524463 : Blo 1682041 2524463 := bstep (se 1 (by rfl) ⟨1893347, by rfl⟩ : syracuseStep 2524463 = 3786695) B3786695
theorem B19162493 : Blo 1682041 19162493 := bstep (se 3 (by rfl) ⟨3592967, by rfl⟩ : syracuseStep 19162493 = 7185935) B7185935
theorem B3786209 : Blo 1682041 3786209 := bstep (se 2 (by rfl) ⟨1419828, by rfl⟩ : syracuseStep 3786209 = 2839657) B2839657
theorem B30696947 : Blo 1682041 30696947 := bstep (se 1 (by rfl) ⟨23022710, by rfl⟩ : syracuseStep 30696947 = 46045421) B46045421
theorem B2524667 : Blo 1682041 2524667 := bstep (se 1 (by rfl) ⟨1893500, by rfl⟩ : syracuseStep 2524667 = 3787001) B3787001
theorem B2524703 : Blo 1682041 2524703 := bstep (se 1 (by rfl) ⟨1893527, by rfl⟩ : syracuseStep 2524703 = 3787055) B3787055
theorem B1893919 : Blo 1682041 1893919 := bstep (se 1 (by rfl) ⟨1420439, by rfl⟩ : syracuseStep 1893919 = 2840879) B2840879
theorem B4261481 : Blo 1682041 4261481 := bstep (se 2 (by rfl) ⟨1598055, by rfl⟩ : syracuseStep 4261481 = 3196111) B3196111
theorem B2524847 : Blo 1682041 2524847 := bstep (se 1 (by rfl) ⟨1893635, by rfl⟩ : syracuseStep 2524847 = 3787271) B3787271
theorem B12773051 : Blo 1682041 12773051 := bstep (se 1 (by rfl) ⟨9579788, by rfl⟩ : syracuseStep 12773051 = 19159577) B19159577
theorem B2524967 : Blo 1682041 2524967 := bstep (se 1 (by rfl) ⟨1893725, by rfl⟩ : syracuseStep 2524967 = 3787451) B3787451
theorem B6063929 : Blo 1682041 6063929 := bstep (se 2 (by rfl) ⟨2273973, by rfl⟩ : syracuseStep 6063929 = 4547947) B4547947
theorem B12126095 : Blo 1682041 12126095 := bstep (se 1 (by rfl) ⟨9094571, by rfl⟩ : syracuseStep 12126095 = 18189143) B18189143
theorem B5679071 : Blo 1682041 5679071 := bstep (se 1 (by rfl) ⟨4259303, by rfl⟩ : syracuseStep 5679071 = 8518607) B8518607
theorem B81864755 : Blo 1682041 81864755 := bstep (se 1 (by rfl) ⟨61398566, by rfl⟩ : syracuseStep 81864755 = 122797133) B122797133
theorem B3459233 : Blo 1682041 3459233 := bstep (se 2 (by rfl) ⟨1297212, by rfl⟩ : syracuseStep 3459233 = 2594425) B2594425
theorem B2525519 : Blo 1682041 2525519 := bstep (se 1 (by rfl) ⟨1894139, by rfl⟩ : syracuseStep 2525519 = 3788279) B3788279
theorem B2525567 : Blo 1682041 2525567 := bstep (se 1 (by rfl) ⟨1894175, by rfl⟩ : syracuseStep 2525567 = 3788351) B3788351
theorem B2525609 : Blo 1682041 2525609 := bstep (se 2 (by rfl) ⟨947103, by rfl⟩ : syracuseStep 2525609 = 1894207) B1894207
theorem B10234507 : Blo 1682041 10234507 := bstep (se 1 (by rfl) ⟨7675880, by rfl⟩ : syracuseStep 10234507 = 15351761) B15351761
theorem B3787559 : Blo 1682041 3787559 := bstep (se 1 (by rfl) ⟨2840669, by rfl⟩ : syracuseStep 3787559 = 5681339) B5681339
theorem B2525993 : Blo 1682041 2525993 := bstep (se 2 (by rfl) ⟨947247, by rfl⟩ : syracuseStep 2525993 = 1894495) B1894495
theorem B8088407 : Blo 1682041 8088407 := bstep (se 1 (by rfl) ⟨6066305, by rfl⟩ : syracuseStep 8088407 = 12132611) B12132611
theorem B1682399 : Blo 1682041 1682399 := bstep (se 1 (by rfl) ⟨1261799, by rfl⟩ : syracuseStep 1682399 = 2523599) B2523599
theorem B1682427 : Blo 1682041 1682427 := bstep (se 1 (by rfl) ⟨1261820, by rfl⟩ : syracuseStep 1682427 = 2523641) B2523641
theorem B1682495 : Blo 1682041 1682495 := bstep (se 1 (by rfl) ⟨1261871, by rfl⟩ : syracuseStep 1682495 = 2523743) B2523743
theorem B3787883 : Blo 1682041 3787883 := bstep (se 1 (by rfl) ⟨2840912, by rfl⟩ : syracuseStep 3787883 = 5681825) B5681825
theorem B21556529 : Blo 1682041 21556529 := bstep (se 2 (by rfl) ⟨8083698, by rfl⟩ : syracuseStep 21556529 = 16167397) B16167397
theorem B3788153 : Blo 1682041 3788153 := bstep (se 2 (by rfl) ⟨1420557, by rfl⟩ : syracuseStep 3788153 = 2841115) B2841115
theorem B1682815 : Blo 1682041 1682815 := bstep (se 1 (by rfl) ⟨1262111, by rfl⟩ : syracuseStep 1682815 = 2524223) B2524223
theorem B1682843 : Blo 1682041 1682843 := bstep (se 1 (by rfl) ⟨1262132, by rfl⟩ : syracuseStep 1682843 = 2524265) B2524265
theorem B32361929 : Blo 1682041 32361929 := bstep (se 2 (by rfl) ⟨12135723, by rfl⟩ : syracuseStep 32361929 = 24271447) B24271447
theorem B1682911 : Blo 1682041 1682911 := bstep (se 1 (by rfl) ⟨1262183, by rfl⟩ : syracuseStep 1682911 = 2524367) B2524367
theorem B109211125 : Blo 1682041 109211125 := bstep (se 5 (by rfl) ⟨5119271, by rfl⟩ : syracuseStep 109211125 = 10238543) B10238543
theorem B61402657 : Blo 1682041 61402657 := bstep (se 2 (by rfl) ⟨23025996, by rfl⟩ : syracuseStep 61402657 = 46051993) B46051993
theorem B122834495 : Blo 1682041 122834495 := bstep (se 1 (by rfl) ⟨92125871, by rfl⟩ : syracuseStep 122834495 = 184251743) B184251743
theorem B1683047 : Blo 1682041 1683047 := bstep (se 1 (by rfl) ⟨1262285, by rfl⟩ : syracuseStep 1683047 = 2524571) B2524571
theorem B32353931 : Blo 1682041 32353931 := bstep (se 1 (by rfl) ⟨24265448, by rfl⟩ : syracuseStep 32353931 = 48530897) B48530897
theorem B3788459 : Blo 1682041 3788459 := bstep (se 1 (by rfl) ⟨2841344, by rfl⟩ : syracuseStep 3788459 = 5682689) B5682689
theorem B1683195 : Blo 1682041 1683195 := bstep (se 1 (by rfl) ⟨1262396, by rfl⟩ : syracuseStep 1683195 = 2524793) B2524793
theorem B1683263 : Blo 1682041 1683263 := bstep (se 1 (by rfl) ⟨1262447, by rfl⟩ : syracuseStep 1683263 = 2524895) B2524895
theorem B1683327 : Blo 1682041 1683327 := bstep (se 1 (by rfl) ⟨1262495, by rfl⟩ : syracuseStep 1683327 = 2524991) B2524991
theorem B2838503 : Blo 1682041 2838503 := bstep (se 1 (by rfl) ⟨2128877, by rfl⟩ : syracuseStep 2838503 = 4257755) B4257755
theorem B1683439 : Blo 1682041 1683439 := bstep (se 1 (by rfl) ⟨1262579, by rfl⟩ : syracuseStep 1683439 = 2525159) B2525159
theorem B3788783 : Blo 1682041 3788783 := bstep (se 1 (by rfl) ⟨2841587, by rfl⟩ : syracuseStep 3788783 = 5683175) B5683175
theorem B2838523 : Blo 1682041 2838523 := bstep (se 1 (by rfl) ⟨2128892, by rfl⟩ : syracuseStep 2838523 = 4257785) B4257785
theorem B2396155 : Blo 1682041 2396155 := bstep (se 1 (by rfl) ⟨1797116, by rfl⟩ : syracuseStep 2396155 = 3594233) B3594233
theorem B1683451 : Blo 1682041 1683451 := bstep (se 1 (by rfl) ⟨1262588, by rfl⟩ : syracuseStep 1683451 = 2525177) B2525177
theorem B3788855 : Blo 1682041 3788855 := bstep (se 1 (by rfl) ⟨2841641, by rfl⟩ : syracuseStep 3788855 = 5683283) B5683283
theorem B1683519 : Blo 1682041 1683519 := bstep (se 1 (by rfl) ⟨1262639, by rfl⟩ : syracuseStep 1683519 = 2525279) B2525279
theorem B2838631 : Blo 1682041 2838631 := bstep (se 1 (by rfl) ⟨2128973, by rfl⟩ : syracuseStep 2838631 = 4257947) B4257947
theorem B1683559 : Blo 1682041 1683559 := bstep (se 1 (by rfl) ⟨1262669, by rfl⟩ : syracuseStep 1683559 = 2525339) B2525339
theorem B1683583 : Blo 1682041 1683583 := bstep (se 1 (by rfl) ⟨1262687, by rfl⟩ : syracuseStep 1683583 = 2525375) B2525375
theorem B1683611 : Blo 1682041 1683611 := bstep (se 1 (by rfl) ⟨1262708, by rfl⟩ : syracuseStep 1683611 = 2525417) B2525417
theorem B3788999 : Blo 1682041 3788999 := bstep (se 1 (by rfl) ⟨2841749, by rfl⟩ : syracuseStep 3788999 = 5683499) B5683499
theorem B10375379 : Blo 1682041 10375379 := bstep (se 1 (by rfl) ⟨7781534, by rfl⟩ : syracuseStep 10375379 = 15563069) B15563069
theorem B1683815 : Blo 1682041 1683815 := bstep (se 1 (by rfl) ⟨1262861, by rfl⟩ : syracuseStep 1683815 = 2525723) B2525723
theorem B1683867 : Blo 1682041 1683867 := bstep (se 1 (by rfl) ⟨1262900, by rfl⟩ : syracuseStep 1683867 = 2525801) B2525801
theorem B7287239 : Blo 1682041 7287239 := bstep (se 1 (by rfl) ⟨5465429, by rfl⟩ : syracuseStep 7287239 = 10930859) B10930859
theorem B8090063 : Blo 1682041 8090063 := bstep (se 1 (by rfl) ⟨6067547, by rfl⟩ : syracuseStep 8090063 = 12135095) B12135095
theorem B13644359 : Blo 1682041 13644359 := bstep (se 1 (by rfl) ⟨10233269, by rfl⟩ : syracuseStep 13644359 = 20466539) B20466539
theorem B5681771 : Blo 1682041 5681771 := bstep (se 1 (by rfl) ⟨4261328, by rfl⟩ : syracuseStep 5681771 = 8522657) B8522657
theorem B8524601 : Blo 1682041 8524601 := bstep (se 2 (by rfl) ⟨3196725, by rfl⟩ : syracuseStep 8524601 = 6393451) B6393451
theorem B2839387 : Blo 1682041 2839387 := bstep (se 1 (by rfl) ⟨2129540, by rfl⟩ : syracuseStep 2839387 = 4259081) B4259081
theorem B9098075 : Blo 1682041 9098075 := bstep (se 1 (by rfl) ⟨6823556, by rfl⟩ : syracuseStep 9098075 = 13647113) B13647113
theorem B16184195 : Blo 1682041 16184195 := bstep (se 1 (by rfl) ⟨12138146, by rfl⟩ : syracuseStep 16184195 = 24276293) B24276293
theorem B7189559 : Blo 1682041 7189559 := bstep (se 1 (by rfl) ⟨5392169, by rfl⟩ : syracuseStep 7189559 = 10784339) B10784339
theorem B6386951 : Blo 1682041 6386951 := bstep (se 1 (by rfl) ⟨4790213, by rfl⟩ : syracuseStep 6386951 = 9580427) B9580427
theorem B6920137 : Blo 1682041 6920137 := bstep (se 2 (by rfl) ⟨2595051, by rfl⟩ : syracuseStep 6920137 = 5190103) B5190103
theorem B5683391 : Blo 1682041 5683391 := bstep (se 1 (by rfl) ⟨4262543, by rfl⟩ : syracuseStep 5683391 = 8525087) B8525087
theorem B6387923 : Blo 1682041 6387923 := bstep (se 1 (by rfl) ⟨4790942, by rfl⟩ : syracuseStep 6387923 = 9581885) B9581885
theorem B22763753 : Blo 1682041 22763753 := bstep (se 2 (by rfl) ⟨8536407, by rfl⟩ : syracuseStep 22763753 = 17072815) B17072815
theorem B9582887 : Blo 1682041 9582887 := bstep (se 1 (by rfl) ⟨7187165, by rfl⟩ : syracuseStep 9582887 = 14374331) B14374331
theorem B8083871 : Blo 1682041 8083871 := bstep (se 1 (by rfl) ⟨6062903, by rfl⟩ : syracuseStep 8083871 = 12125807) B12125807
theorem B4045319 : Blo 1682041 4045319 := bstep (se 1 (by rfl) ⟨3033989, by rfl⟩ : syracuseStep 4045319 = 6067979) B6067979
theorem B4258433 : Blo 1682041 4258433 := bstep (se 2 (by rfl) ⟨1596912, by rfl⟩ : syracuseStep 4258433 = 3193825) B3193825
theorem B14383763 : Blo 1682041 14383763 := bstep (se 1 (by rfl) ⟨10787822, by rfl⟩ : syracuseStep 14383763 = 21575645) B21575645
theorem B33250067 : Blo 1682041 33250067 := bstep (se 1 (by rfl) ⟨24937550, by rfl⟩ : syracuseStep 33250067 = 49875101) B49875101
theorem B3595079 : Blo 1682041 3595079 := bstep (se 1 (by rfl) ⟨2696309, by rfl⟩ : syracuseStep 3595079 = 5392619) B5392619
theorem B12778397 : Blo 1682041 12778397 := bstep (se 3 (by rfl) ⟨2395949, by rfl⟩ : syracuseStep 12778397 = 4791899) B4791899
theorem B17275985 : Blo 1682041 17275985 := bstep (se 2 (by rfl) ⟨6478494, by rfl⟩ : syracuseStep 17275985 = 12956989) B12956989
theorem B4259243 : Blo 1682041 4259243 := bstep (se 1 (by rfl) ⟨3194432, by rfl⟩ : syracuseStep 4259243 = 6388865) B6388865
theorem B8084929 : Blo 1682041 8084929 := bstep (se 2 (by rfl) ⟨3031848, by rfl⟩ : syracuseStep 8084929 = 6063697) B6063697
theorem B8084947 : Blo 1682041 8084947 := bstep (se 1 (by rfl) ⟨6063710, by rfl⟩ : syracuseStep 8084947 = 12127421) B12127421
theorem B16170587 : Blo 1682041 16170587 := bstep (se 1 (by rfl) ⟨12127940, by rfl⟩ : syracuseStep 16170587 = 24255881) B24255881
theorem B7675535 : Blo 1682041 7675535 := bstep (se 1 (by rfl) ⟨5756651, by rfl⟩ : syracuseStep 7675535 = 11513303) B11513303
theorem B7192259 : Blo 1682041 7192259 := bstep (se 1 (by rfl) ⟨5394194, by rfl⟩ : syracuseStep 7192259 = 10788389) B10788389
theorem B14376791 : Blo 1682041 14376791 := bstep (se 1 (by rfl) ⟨10782593, by rfl⟩ : syracuseStep 14376791 = 21565187) B21565187
theorem B23035853 : Blo 1682041 23035853 := bstep (se 3 (by rfl) ⟨4319222, by rfl⟩ : syracuseStep 23035853 = 8638445) B8638445
theorem B3784787 : Blo 1682041 3784787 := bstep (se 1 (by rfl) ⟨2838590, by rfl⟩ : syracuseStep 3784787 = 5677181) B5677181
theorem B2523263 : Blo 1682041 2523263 := bstep (se 1 (by rfl) ⟨1892447, by rfl⟩ : syracuseStep 2523263 = 3784895) B3784895
theorem B3784841 : Blo 1682041 3784841 := bstep (se 2 (by rfl) ⟨1419315, by rfl⟩ : syracuseStep 3784841 = 2838631) B2838631
theorem B147489025 : Blo 1682041 147489025 := bstep (se 2 (by rfl) ⟨55308384, by rfl⟩ : syracuseStep 147489025 = 110616769) B110616769
theorem B3784967 : Blo 1682041 3784967 := bstep (se 1 (by rfl) ⟨2838725, by rfl⟩ : syracuseStep 3784967 = 5677451) B5677451
theorem B6390035 : Blo 1682041 6390035 := bstep (se 1 (by rfl) ⟨4792526, by rfl⟩ : syracuseStep 6390035 = 9585053) B9585053
theorem B4858159 : Blo 1682041 4858159 := bstep (se 1 (by rfl) ⟨3643619, by rfl⟩ : syracuseStep 4858159 = 7287239) B7287239
theorem B2523551 : Blo 1682041 2523551 := bstep (se 1 (by rfl) ⟨1892663, by rfl⟩ : syracuseStep 2523551 = 3785327) B3785327
theorem B10789463 : Blo 1682041 10789463 := bstep (se 1 (by rfl) ⟨8092097, by rfl⟩ : syracuseStep 10789463 = 16184195) B16184195
theorem B2523815 : Blo 1682041 2523815 := bstep (se 1 (by rfl) ⟨1892861, by rfl⟩ : syracuseStep 2523815 = 3785723) B3785723
theorem B4260539 : Blo 1682041 4260539 := bstep (se 1 (by rfl) ⟨3195404, by rfl⟩ : syracuseStep 4260539 = 6390809) B6390809
theorem B4793039 : Blo 1682041 4793039 := bstep (se 1 (by rfl) ⟨3594779, by rfl⟩ : syracuseStep 4793039 = 7189559) B7189559
theorem B28754675 : Blo 1682041 28754675 := bstep (se 1 (by rfl) ⟨21566006, by rfl⟩ : syracuseStep 28754675 = 43132013) B43132013
theorem B2523935 : Blo 1682041 2523935 := bstep (se 1 (by rfl) ⟨1892951, by rfl⟩ : syracuseStep 2523935 = 3785903) B3785903
theorem B2523959 : Blo 1682041 2523959 := bstep (se 1 (by rfl) ⟨1892969, by rfl⟩ : syracuseStep 2523959 = 3785939) B3785939
theorem B4260671 : Blo 1682041 4260671 := bstep (se 1 (by rfl) ⟨3195503, by rfl⟩ : syracuseStep 4260671 = 6391007) B6391007
theorem B9716591 : Blo 1682041 9716591 := bstep (se 1 (by rfl) ⟨7287443, by rfl⟩ : syracuseStep 9716591 = 14574887) B14574887
theorem B2524139 : Blo 1682041 2524139 := bstep (se 1 (by rfl) ⟨1893104, by rfl⟩ : syracuseStep 2524139 = 3786209) B3786209
theorem B20464631 : Blo 1682041 20464631 := bstep (se 1 (by rfl) ⟨15348473, by rfl⟩ : syracuseStep 20464631 = 30696947) B30696947
theorem B3785849 : Blo 1682041 3785849 := bstep (se 2 (by rfl) ⟨1419693, by rfl⟩ : syracuseStep 3785849 = 2839387) B2839387
theorem B3786047 : Blo 1682041 3786047 := bstep (se 1 (by rfl) ⟨2839535, by rfl⟩ : syracuseStep 3786047 = 5679071) B5679071
theorem B54576503 : Blo 1682041 54576503 := bstep (se 1 (by rfl) ⟨40932377, by rfl⟩ : syracuseStep 54576503 = 81864755) B81864755
theorem B3194873 : Blo 1682041 3194873 := bstep (se 2 (by rfl) ⟨1198077, by rfl⟩ : syracuseStep 3194873 = 2396155) B2396155
theorem B2524649 : Blo 1682041 2524649 := bstep (se 2 (by rfl) ⟨946743, by rfl⟩ : syracuseStep 2524649 = 1893487) B1893487
theorem B2696879 : Blo 1682041 2696879 := bstep (se 1 (by rfl) ⟨2022659, by rfl⟩ : syracuseStep 2696879 = 4045319) B4045319
theorem B2525039 : Blo 1682041 2525039 := bstep (se 1 (by rfl) ⟨1893779, by rfl⟩ : syracuseStep 2525039 = 3787559) B3787559
theorem B5392271 : Blo 1682041 5392271 := bstep (se 1 (by rfl) ⟨4044203, by rfl⟩ : syracuseStep 5392271 = 8088407) B8088407
theorem B145614833 : Blo 1682041 145614833 := bstep (se 2 (by rfl) ⟨54605562, by rfl⟩ : syracuseStep 145614833 = 109211125) B109211125
theorem B2525225 : Blo 1682041 2525225 := bstep (se 2 (by rfl) ⟨946959, by rfl⟩ : syracuseStep 2525225 = 1893919) B1893919
theorem B2525255 : Blo 1682041 2525255 := bstep (se 1 (by rfl) ⟨1893941, by rfl⟩ : syracuseStep 2525255 = 3787883) B3787883
theorem B14371019 : Blo 1682041 14371019 := bstep (se 1 (by rfl) ⟨10778264, by rfl⟩ : syracuseStep 14371019 = 21556529) B21556529
theorem B2525435 : Blo 1682041 2525435 := bstep (se 1 (by rfl) ⟨1894076, by rfl⟩ : syracuseStep 2525435 = 3788153) B3788153
theorem B81889663 : Blo 1682041 81889663 := bstep (se 1 (by rfl) ⟨61417247, by rfl⟩ : syracuseStep 81889663 = 122834495) B122834495
theorem B36907397 : Blo 1682041 36907397 := bstep (se 4 (by rfl) ⟨3460068, by rfl⟩ : syracuseStep 36907397 = 6920137) B6920137
theorem B2525639 : Blo 1682041 2525639 := bstep (se 1 (by rfl) ⟨1894229, by rfl⟩ : syracuseStep 2525639 = 3788459) B3788459
theorem B4794839 : Blo 1682041 4794839 := bstep (se 1 (by rfl) ⟨3596129, by rfl⟩ : syracuseStep 4794839 = 7192259) B7192259
theorem B2525855 : Blo 1682041 2525855 := bstep (se 1 (by rfl) ⟨1894391, by rfl⟩ : syracuseStep 2525855 = 3788783) B3788783
theorem B2525903 : Blo 1682041 2525903 := bstep (se 1 (by rfl) ⟨1894427, by rfl⟩ : syracuseStep 2525903 = 3788855) B3788855
theorem B2525999 : Blo 1682041 2525999 := bstep (se 1 (by rfl) ⟨1894499, by rfl⟩ : syracuseStep 2525999 = 3788999) B3788999
theorem B6916919 : Blo 1682041 6916919 := bstep (se 1 (by rfl) ⟨5187689, by rfl⟩ : syracuseStep 6916919 = 10375379) B10375379
theorem B1682247 : Blo 1682041 1682247 := bstep (se 1 (by rfl) ⟨1261685, by rfl⟩ : syracuseStep 1682247 = 2523371) B2523371
theorem B1682287 : Blo 1682041 1682287 := bstep (se 1 (by rfl) ⟨1261715, by rfl⟩ : syracuseStep 1682287 = 2523431) B2523431
theorem B4926347 : Blo 1682041 4926347 := bstep (se 1 (by rfl) ⟨3694760, by rfl⟩ : syracuseStep 4926347 = 7389521) B7389521
theorem B5393375 : Blo 1682041 5393375 := bstep (se 1 (by rfl) ⟨4045031, by rfl⟩ : syracuseStep 5393375 = 8090063) B8090063
theorem B9096239 : Blo 1682041 9096239 := bstep (se 1 (by rfl) ⟨6822179, by rfl⟩ : syracuseStep 9096239 = 13644359) B13644359
theorem B3787847 : Blo 1682041 3787847 := bstep (se 1 (by rfl) ⟨2840885, by rfl⟩ : syracuseStep 3787847 = 5681771) B5681771
theorem B4795499 : Blo 1682041 4795499 := bstep (se 1 (by rfl) ⟨3596624, by rfl⟩ : syracuseStep 4795499 = 7193249) B7193249
theorem B6065383 : Blo 1682041 6065383 := bstep (se 1 (by rfl) ⟨4549037, by rfl⟩ : syracuseStep 6065383 = 9098075) B9098075
theorem B1682735 : Blo 1682041 1682735 := bstep (se 1 (by rfl) ⟨1262051, by rfl⟩ : syracuseStep 1682735 = 2524103) B2524103
theorem B1682847 : Blo 1682041 1682847 := bstep (se 1 (by rfl) ⟨1262135, by rfl⟩ : syracuseStep 1682847 = 2524271) B2524271
theorem B9579971 : Blo 1682041 9579971 := bstep (se 1 (by rfl) ⟨7184978, by rfl⟩ : syracuseStep 9579971 = 14369957) B14369957
theorem B1682975 : Blo 1682041 1682975 := bstep (se 1 (by rfl) ⟨1262231, by rfl⟩ : syracuseStep 1682975 = 2524463) B2524463
theorem B12774995 : Blo 1682041 12774995 := bstep (se 1 (by rfl) ⟨9581246, by rfl⟩ : syracuseStep 12774995 = 19162493) B19162493
theorem B9580153 : Blo 1682041 9580153 := bstep (se 2 (by rfl) ⟨3592557, by rfl⟩ : syracuseStep 9580153 = 7185115) B7185115
theorem B1683111 : Blo 1682041 1683111 := bstep (se 1 (by rfl) ⟨1262333, by rfl⟩ : syracuseStep 1683111 = 2524667) B2524667
theorem B1683135 : Blo 1682041 1683135 := bstep (se 1 (by rfl) ⟨1262351, by rfl⟩ : syracuseStep 1683135 = 2524703) B2524703
theorem B1683231 : Blo 1682041 1683231 := bstep (se 1 (by rfl) ⟨1262423, by rfl⟩ : syracuseStep 1683231 = 2524847) B2524847
theorem B8515367 : Blo 1682041 8515367 := bstep (se 1 (by rfl) ⟨6386525, by rfl⟩ : syracuseStep 8515367 = 12773051) B12773051
theorem B1683311 : Blo 1682041 1683311 := bstep (se 1 (by rfl) ⟨1262483, by rfl⟩ : syracuseStep 1683311 = 2524967) B2524967
theorem B4042619 : Blo 1682041 4042619 := bstep (se 1 (by rfl) ⟨3031964, by rfl⟩ : syracuseStep 4042619 = 6063929) B6063929
theorem B2306155 : Blo 1682041 2306155 := bstep (se 1 (by rfl) ⟨1729616, by rfl⟩ : syracuseStep 2306155 = 3459233) B3459233
theorem B3788927 : Blo 1682041 3788927 := bstep (se 1 (by rfl) ⟨2841695, by rfl⟩ : syracuseStep 3788927 = 5683391) B5683391
theorem B15175835 : Blo 1682041 15175835 := bstep (se 1 (by rfl) ⟨11381876, by rfl⟩ : syracuseStep 15175835 = 22763753) B22763753
theorem B1683679 : Blo 1682041 1683679 := bstep (se 1 (by rfl) ⟨1262759, by rfl⟩ : syracuseStep 1683679 = 2525519) B2525519
theorem B1683711 : Blo 1682041 1683711 := bstep (se 1 (by rfl) ⟨1262783, by rfl⟩ : syracuseStep 1683711 = 2525567) B2525567
theorem B1683739 : Blo 1682041 1683739 := bstep (se 1 (by rfl) ⟨1262804, by rfl⟩ : syracuseStep 1683739 = 2525609) B2525609
theorem B2838955 : Blo 1682041 2838955 := bstep (se 1 (by rfl) ⟨2129216, by rfl⟩ : syracuseStep 2838955 = 4258433) B4258433
theorem B9589175 : Blo 1682041 9589175 := bstep (se 1 (by rfl) ⟨7191881, by rfl⟩ : syracuseStep 9589175 = 14383763) B14383763
theorem B1683995 : Blo 1682041 1683995 := bstep (se 1 (by rfl) ⟨1262996, by rfl⟩ : syracuseStep 1683995 = 2525993) B2525993
theorem B2396719 : Blo 1682041 2396719 := bstep (se 1 (by rfl) ⟨1797539, by rfl⟩ : syracuseStep 2396719 = 3595079) B3595079
theorem B2839495 : Blo 1682041 2839495 := bstep (se 1 (by rfl) ⟨2129621, by rfl⟩ : syracuseStep 2839495 = 4259243) B4259243
theorem B21574619 : Blo 1682041 21574619 := bstep (se 1 (by rfl) ⟨16180964, by rfl⟩ : syracuseStep 21574619 = 32361929) B32361929
theorem B5117023 : Blo 1682041 5117023 := bstep (se 1 (by rfl) ⟨3837767, by rfl⟩ : syracuseStep 5117023 = 7675535) B7675535
theorem B5682365 : Blo 1682041 5682365 := bstep (se 3 (by rfl) ⟨1065443, by rfl⟩ : syracuseStep 5682365 = 2130887) B2130887
theorem B15357235 : Blo 1682041 15357235 := bstep (se 1 (by rfl) ⟨11517926, by rfl⟩ : syracuseStep 15357235 = 23035853) B23035853
theorem B3413839 : Blo 1682041 3413839 := bstep (se 1 (by rfl) ⟨2560379, by rfl⟩ : syracuseStep 3413839 = 5120759) B5120759
theorem B5683067 : Blo 1682041 5683067 := bstep (se 1 (by rfl) ⟨4262300, by rfl⟩ : syracuseStep 5683067 = 8524601) B8524601
theorem B4257967 : Blo 1682041 4257967 := bstep (se 1 (by rfl) ⟨3193475, by rfl⟩ : syracuseStep 4257967 = 6386951) B6386951
theorem B13646009 : Blo 1682041 13646009 := bstep (se 2 (by rfl) ⟨5117253, by rfl⟩ : syracuseStep 13646009 = 10234507) B10234507
theorem B2840987 : Blo 1682041 2840987 := bstep (se 1 (by rfl) ⟨2130740, by rfl⟩ : syracuseStep 2840987 = 4261481) B4261481
theorem B8084063 : Blo 1682041 8084063 := bstep (se 1 (by rfl) ⟨6063047, by rfl⟩ : syracuseStep 8084063 = 12126095) B12126095
theorem B4258615 : Blo 1682041 4258615 := bstep (se 1 (by rfl) ⟨3193961, by rfl⟩ : syracuseStep 4258615 = 6387923) B6387923
theorem B6388591 : Blo 1682041 6388591 := bstep (se 1 (by rfl) ⟨4791443, by rfl⟩ : syracuseStep 6388591 = 9582887) B9582887
theorem B5389247 : Blo 1682041 5389247 := bstep (se 1 (by rfl) ⟨4041935, by rfl⟩ : syracuseStep 5389247 = 8083871) B8083871
theorem B22166711 : Blo 1682041 22166711 := bstep (se 1 (by rfl) ⟨16625033, by rfl⟩ : syracuseStep 22166711 = 33250067) B33250067
theorem B10779905 : Blo 1682041 10779905 := bstep (se 2 (by rfl) ⟨4042464, by rfl⟩ : syracuseStep 10779905 = 8084929) B8084929
theorem B8518931 : Blo 1682041 8518931 := bstep (se 1 (by rfl) ⟨6389198, by rfl⟩ : syracuseStep 8518931 = 12778397) B12778397
theorem B10779929 : Blo 1682041 10779929 := bstep (se 2 (by rfl) ⟨4042473, by rfl⟩ : syracuseStep 10779929 = 8084947) B8084947
theorem B81870209 : Blo 1682041 81870209 := bstep (se 2 (by rfl) ⟨30701328, by rfl⟩ : syracuseStep 81870209 = 61402657) B61402657
theorem B11517323 : Blo 1682041 11517323 := bstep (se 1 (by rfl) ⟨8637992, by rfl⟩ : syracuseStep 11517323 = 17275985) B17275985
theorem B10780391 : Blo 1682041 10780391 := bstep (se 1 (by rfl) ⟨8085293, by rfl⟩ : syracuseStep 10780391 = 16170587) B16170587
theorem B21569287 : Blo 1682041 21569287 := bstep (se 1 (by rfl) ⟨16176965, by rfl⟩ : syracuseStep 21569287 = 32353931) B32353931
theorem B9584527 : Blo 1682041 9584527 := bstep (se 1 (by rfl) ⟨7188395, by rfl⟩ : syracuseStep 9584527 = 14376791) B14376791
theorem B1892335 : Blo 1682041 1892335 := bstep (se 1 (by rfl) ⟨1419251, by rfl⟩ : syracuseStep 1892335 = 2838503) B2838503
theorem B3784697 : Blo 1682041 3784697 := bstep (se 2 (by rfl) ⟨1419261, by rfl⟩ : syracuseStep 3784697 = 2838523) B2838523
theorem B2523191 : Blo 1682041 2523191 := bstep (se 1 (by rfl) ⟨1892393, by rfl⟩ : syracuseStep 2523191 = 3784787) B3784787
theorem B2523227 : Blo 1682041 2523227 := bstep (se 1 (by rfl) ⟨1892420, by rfl⟩ : syracuseStep 2523227 = 3784841) B3784841
theorem B10117223 : Blo 1682041 10117223 := bstep (se 1 (by rfl) ⟨7587917, by rfl⟩ : syracuseStep 10117223 = 15175835) B15175835
theorem B2523311 : Blo 1682041 2523311 := bstep (se 1 (by rfl) ⟨1892483, by rfl⟩ : syracuseStep 2523311 = 3784967) B3784967
theorem B4260023 : Blo 1682041 4260023 := bstep (se 1 (by rfl) ⟨3195017, by rfl⟩ : syracuseStep 4260023 = 6390035) B6390035
theorem B5677289 : Blo 1682041 5677289 := bstep (se 2 (by rfl) ⟨2128983, by rfl⟩ : syracuseStep 5677289 = 4257967) B4257967
theorem B7192975 : Blo 1682041 7192975 := bstep (se 1 (by rfl) ⟨5394731, by rfl⟩ : syracuseStep 7192975 = 10789463) B10789463
theorem B3195359 : Blo 1682041 3195359 := bstep (se 1 (by rfl) ⟨2396519, by rfl⟩ : syracuseStep 3195359 = 4793039) B4793039
theorem B36389357 : Blo 1682041 36389357 := bstep (se 3 (by rfl) ⟨6823004, by rfl⟩ : syracuseStep 36389357 = 13646009) B13646009
theorem B19169783 : Blo 1682041 19169783 := bstep (se 1 (by rfl) ⟨14377337, by rfl⟩ : syracuseStep 19169783 = 28754675) B28754675
theorem B3785273 : Blo 1682041 3785273 := bstep (se 2 (by rfl) ⟨1419477, by rfl⟩ : syracuseStep 3785273 = 2838955) B2838955
theorem B3195625 : Blo 1682041 3195625 := bstep (se 2 (by rfl) ⟨1198359, by rfl⟩ : syracuseStep 3195625 = 2396719) B2396719
theorem B2523899 : Blo 1682041 2523899 := bstep (se 1 (by rfl) ⟨1892924, by rfl⟩ : syracuseStep 2523899 = 3785849) B3785849
theorem B2524031 : Blo 1682041 2524031 := bstep (se 1 (by rfl) ⟨1893023, by rfl⟩ : syracuseStep 2524031 = 3786047) B3786047
theorem B2129915 : Blo 1682041 2129915 := bstep (se 1 (by rfl) ⟨1597436, by rfl⟩ : syracuseStep 2129915 = 3194873) B3194873
theorem B30712861 : Blo 1682041 30712861 := bstep (se 3 (by rfl) ⟨5758661, by rfl⟩ : syracuseStep 30712861 = 11517323) B11517323
theorem B5678153 : Blo 1682041 5678153 := bstep (se 2 (by rfl) ⟨2129307, by rfl⟩ : syracuseStep 5678153 = 4258615) B4258615
theorem B3785993 : Blo 1682041 3785993 := bstep (se 2 (by rfl) ⟨1419747, by rfl⟩ : syracuseStep 3785993 = 2839495) B2839495
theorem B97076555 : Blo 1682041 97076555 := bstep (se 1 (by rfl) ⟨72807416, by rfl⟩ : syracuseStep 97076555 = 145614833) B145614833
theorem B1893991 : Blo 1682041 1893991 := bstep (se 1 (by rfl) ⟨1420493, by rfl⟩ : syracuseStep 1893991 = 2840987) B2840987
theorem B8087177 : Blo 1682041 8087177 := bstep (se 2 (by rfl) ⟨3032691, by rfl⟩ : syracuseStep 8087177 = 6065383) B6065383
theorem B3196559 : Blo 1682041 3196559 := bstep (se 1 (by rfl) ⟨2397419, by rfl⟩ : syracuseStep 3196559 = 4794839) B4794839
theorem B6064159 : Blo 1682041 6064159 := bstep (se 1 (by rfl) ⟨4548119, by rfl⟩ : syracuseStep 6064159 = 9096239) B9096239
theorem B2525231 : Blo 1682041 2525231 := bstep (se 1 (by rfl) ⟨1893923, by rfl⟩ : syracuseStep 2525231 = 3787847) B3787847
theorem B3196999 : Blo 1682041 3196999 := bstep (se 1 (by rfl) ⟨2397749, by rfl⟩ : syracuseStep 3196999 = 4795499) B4795499
theorem B12773537 : Blo 1682041 12773537 := bstep (se 2 (by rfl) ⟨4790076, by rfl⟩ : syracuseStep 12773537 = 9580153) B9580153
theorem B7186603 : Blo 1682041 7186603 := bstep (se 1 (by rfl) ⟨5389952, by rfl⟩ : syracuseStep 7186603 = 10779905) B10779905
theorem B5679287 : Blo 1682041 5679287 := bstep (se 1 (by rfl) ⟨4259465, by rfl⟩ : syracuseStep 5679287 = 8518931) B8518931
theorem B7186619 : Blo 1682041 7186619 := bstep (se 1 (by rfl) ⟨5389964, by rfl⟩ : syracuseStep 7186619 = 10779929) B10779929
theorem B14379389 : Blo 1682041 14379389 := bstep (se 3 (by rfl) ⟨2696135, by rfl⟩ : syracuseStep 14379389 = 5392271) B5392271
theorem B7186927 : Blo 1682041 7186927 := bstep (se 1 (by rfl) ⟨5390195, by rfl⟩ : syracuseStep 7186927 = 10780391) B10780391
theorem B1682175 : Blo 1682041 1682175 := bstep (se 1 (by rfl) ⟨1261631, by rfl⟩ : syracuseStep 1682175 = 2523263) B2523263
theorem B2525951 : Blo 1682041 2525951 := bstep (se 1 (by rfl) ⟨1894463, by rfl⟩ : syracuseStep 2525951 = 3788927) B3788927
theorem B3074873 : Blo 1682041 3074873 := bstep (se 2 (by rfl) ⟨1153077, by rfl⟩ : syracuseStep 3074873 = 2306155) B2306155
theorem B1682367 : Blo 1682041 1682367 := bstep (se 1 (by rfl) ⟨1261775, by rfl⟩ : syracuseStep 1682367 = 2523551) B2523551
theorem B6392783 : Blo 1682041 6392783 := bstep (se 1 (by rfl) ⟨4794587, by rfl⟩ : syracuseStep 6392783 = 9589175) B9589175
theorem B196652033 : Blo 1682041 196652033 := bstep (se 2 (by rfl) ⟨73744512, by rfl⟩ : syracuseStep 196652033 = 147489025) B147489025
theorem B1682543 : Blo 1682041 1682543 := bstep (se 1 (by rfl) ⟨1261907, by rfl⟩ : syracuseStep 1682543 = 2523815) B2523815
theorem B27290789 : Blo 1682041 27290789 := bstep (se 4 (by rfl) ⟨2558511, by rfl⟩ : syracuseStep 27290789 = 5117023) B5117023
theorem B109186217 : Blo 1682041 109186217 := bstep (se 2 (by rfl) ⟨40944831, by rfl⟩ : syracuseStep 109186217 = 81889663) B81889663
theorem B1682623 : Blo 1682041 1682623 := bstep (se 1 (by rfl) ⟨1261967, by rfl⟩ : syracuseStep 1682623 = 2523935) B2523935
theorem B1682639 : Blo 1682041 1682639 := bstep (se 1 (by rfl) ⟨1261979, by rfl⟩ : syracuseStep 1682639 = 2523959) B2523959
theorem B1682759 : Blo 1682041 1682759 := bstep (se 1 (by rfl) ⟨1262069, by rfl⟩ : syracuseStep 1682759 = 2524139) B2524139
theorem B13643087 : Blo 1682041 13643087 := bstep (se 1 (by rfl) ⟨10232315, by rfl⟩ : syracuseStep 13643087 = 20464631) B20464631
theorem B3788243 : Blo 1682041 3788243 := bstep (se 1 (by rfl) ⟨2841182, by rfl⟩ : syracuseStep 3788243 = 5682365) B5682365
theorem B36384335 : Blo 1682041 36384335 := bstep (se 1 (by rfl) ⟨27288251, by rfl⟩ : syracuseStep 36384335 = 54576503) B54576503
theorem B1683099 : Blo 1682041 1683099 := bstep (se 1 (by rfl) ⟨1262324, by rfl⟩ : syracuseStep 1683099 = 2524649) B2524649
theorem B1797919 : Blo 1682041 1797919 := bstep (se 1 (by rfl) ⟨1348439, by rfl⟩ : syracuseStep 1797919 = 2696879) B2696879
theorem B1683359 : Blo 1682041 1683359 := bstep (se 1 (by rfl) ⟨1262519, by rfl⟩ : syracuseStep 1683359 = 2525039) B2525039
theorem B3788711 : Blo 1682041 3788711 := bstep (se 1 (by rfl) ⟨2841533, by rfl⟩ : syracuseStep 3788711 = 5683067) B5683067
theorem B1683483 : Blo 1682041 1683483 := bstep (se 1 (by rfl) ⟨1262612, by rfl⟩ : syracuseStep 1683483 = 2525225) B2525225
theorem B1683503 : Blo 1682041 1683503 := bstep (se 1 (by rfl) ⟨1262627, by rfl⟩ : syracuseStep 1683503 = 2525255) B2525255
theorem B9580679 : Blo 1682041 9580679 := bstep (se 1 (by rfl) ⟨7185509, by rfl⟩ : syracuseStep 9580679 = 14371019) B14371019
theorem B1683623 : Blo 1682041 1683623 := bstep (se 1 (by rfl) ⟨1262717, by rfl⟩ : syracuseStep 1683623 = 2525435) B2525435
theorem B21557501 : Blo 1682041 21557501 := bstep (se 3 (by rfl) ⟨4042031, by rfl⟩ : syracuseStep 21557501 = 8084063) B8084063
theorem B24604931 : Blo 1682041 24604931 := bstep (se 1 (by rfl) ⟨18453698, by rfl⟩ : syracuseStep 24604931 = 36907397) B36907397
theorem B1683759 : Blo 1682041 1683759 := bstep (se 1 (by rfl) ⟨1262819, by rfl⟩ : syracuseStep 1683759 = 2525639) B2525639
theorem B20476313 : Blo 1682041 20476313 := bstep (se 2 (by rfl) ⟨7678617, by rfl⟩ : syracuseStep 20476313 = 15357235) B15357235
theorem B1683903 : Blo 1682041 1683903 := bstep (se 1 (by rfl) ⟨1262927, by rfl⟩ : syracuseStep 1683903 = 2525855) B2525855
theorem B1683935 : Blo 1682041 1683935 := bstep (se 1 (by rfl) ⟨1262951, by rfl⟩ : syracuseStep 1683935 = 2525903) B2525903
theorem B1683999 : Blo 1682041 1683999 := bstep (se 1 (by rfl) ⟨1262999, by rfl⟩ : syracuseStep 1683999 = 2525999) B2525999
theorem B3592831 : Blo 1682041 3592831 := bstep (se 1 (by rfl) ⟨2694623, by rfl⟩ : syracuseStep 3592831 = 5389247) B5389247
theorem B18445117 : Blo 1682041 18445117 := bstep (se 3 (by rfl) ⟨3458459, by rfl⟩ : syracuseStep 18445117 = 6916919) B6916919
theorem B54580139 : Blo 1682041 54580139 := bstep (se 1 (by rfl) ⟨40935104, by rfl⟩ : syracuseStep 54580139 = 81870209) B81870209
theorem B6386647 : Blo 1682041 6386647 := bstep (se 1 (by rfl) ⟨4789985, by rfl⟩ : syracuseStep 6386647 = 9579971) B9579971
theorem B28759049 : Blo 1682041 28759049 := bstep (se 2 (by rfl) ⟨10784643, by rfl⟩ : syracuseStep 28759049 = 21569287) B21569287
theorem B8516663 : Blo 1682041 8516663 := bstep (se 1 (by rfl) ⟨6387497, by rfl⟩ : syracuseStep 8516663 = 12774995) B12774995
theorem B4551785 : Blo 1682041 4551785 := bstep (se 2 (by rfl) ⟨1706919, by rfl⟩ : syracuseStep 4551785 = 3413839) B3413839
theorem B6477545 : Blo 1682041 6477545 := bstep (se 2 (by rfl) ⟨2429079, by rfl⟩ : syracuseStep 6477545 = 4858159) B4858159
theorem B2840359 : Blo 1682041 2840359 := bstep (se 1 (by rfl) ⟨2130269, by rfl⟩ : syracuseStep 2840359 = 4260539) B4260539
theorem B2840447 : Blo 1682041 2840447 := bstep (se 1 (by rfl) ⟨2130335, by rfl⟩ : syracuseStep 2840447 = 4260671) B4260671
theorem B6477727 : Blo 1682041 6477727 := bstep (se 1 (by rfl) ⟨4858295, by rfl⟩ : syracuseStep 6477727 = 9716591) B9716591
theorem B14383079 : Blo 1682041 14383079 := bstep (se 1 (by rfl) ⟨10787309, by rfl⟩ : syracuseStep 14383079 = 21574619) B21574619
theorem B8518121 : Blo 1682041 8518121 := bstep (se 2 (by rfl) ⟨3194295, by rfl⟩ : syracuseStep 8518121 = 6388591) B6388591
theorem B3284231 : Blo 1682041 3284231 := bstep (se 1 (by rfl) ⟨2463173, by rfl⟩ : syracuseStep 3284231 = 4926347) B4926347
theorem B3595583 : Blo 1682041 3595583 := bstep (se 1 (by rfl) ⟨2696687, by rfl⟩ : syracuseStep 3595583 = 5393375) B5393375
theorem B14777807 : Blo 1682041 14777807 := bstep (se 1 (by rfl) ⟨11083355, by rfl⟩ : syracuseStep 14777807 = 22166711) B22166711
theorem B12779369 : Blo 1682041 12779369 := bstep (se 2 (by rfl) ⟨4792263, by rfl⟩ : syracuseStep 12779369 = 9584527) B9584527
theorem B5676911 : Blo 1682041 5676911 := bstep (se 1 (by rfl) ⟨4257683, by rfl⟩ : syracuseStep 5676911 = 8515367) B8515367
theorem B2695079 : Blo 1682041 2695079 := bstep (se 1 (by rfl) ⟨2021309, by rfl⟩ : syracuseStep 2695079 = 4042619) B4042619
theorem B2523113 : Blo 1682041 2523113 := bstep (se 2 (by rfl) ⟨946167, by rfl⟩ : syracuseStep 2523113 = 1892335) B1892335
theorem B2523131 : Blo 1682041 2523131 := bstep (se 1 (by rfl) ⟨1892348, by rfl⟩ : syracuseStep 2523131 = 3784697) B3784697
theorem B8085545 : Blo 1682041 8085545 := bstep (se 2 (by rfl) ⟨3032079, by rfl⟩ : syracuseStep 8085545 = 6064159) B6064159
theorem B3784859 : Blo 1682041 3784859 := bstep (se 1 (by rfl) ⟨2838644, by rfl⟩ : syracuseStep 3784859 = 5677289) B5677289
theorem B2130239 : Blo 1682041 2130239 := bstep (se 1 (by rfl) ⟨1597679, by rfl⟩ : syracuseStep 2130239 = 3195359) B3195359
theorem B12779855 : Blo 1682041 12779855 := bstep (se 1 (by rfl) ⟨9584891, by rfl⟩ : syracuseStep 12779855 = 19169783) B19169783
theorem B2523515 : Blo 1682041 2523515 := bstep (se 1 (by rfl) ⟨1892636, by rfl⟩ : syracuseStep 2523515 = 3785273) B3785273
theorem B8757949 : Blo 1682041 8757949 := bstep (se 3 (by rfl) ⟨1642115, by rfl⟩ : syracuseStep 8757949 = 3284231) B3284231
theorem B5677775 : Blo 1682041 5677775 := bstep (se 1 (by rfl) ⟨4258331, by rfl⟩ : syracuseStep 5677775 = 8516663) B8516663
theorem B3785435 : Blo 1682041 3785435 := bstep (se 1 (by rfl) ⟨2839076, by rfl⟩ : syracuseStep 3785435 = 5678153) B5678153
theorem B2523995 : Blo 1682041 2523995 := bstep (se 1 (by rfl) ⟨1892996, by rfl⟩ : syracuseStep 2523995 = 3785993) B3785993
theorem B36381565 : Blo 1682041 36381565 := bstep (se 3 (by rfl) ⟨6821543, by rfl⟩ : syracuseStep 36381565 = 13643087) B13643087
theorem B64717703 : Blo 1682041 64717703 := bstep (se 1 (by rfl) ⟨48538277, by rfl⟩ : syracuseStep 64717703 = 97076555) B97076555
theorem B4260833 : Blo 1682041 4260833 := bstep (se 2 (by rfl) ⟨1597812, by rfl⟩ : syracuseStep 4260833 = 3195625) B3195625
theorem B24593489 : Blo 1682041 24593489 := bstep (se 2 (by rfl) ⟨9222558, by rfl⟩ : syracuseStep 24593489 = 18445117) B18445117
theorem B5391451 : Blo 1682041 5391451 := bstep (se 1 (by rfl) ⟨4043588, by rfl⟩ : syracuseStep 5391451 = 8087177) B8087177
theorem B2131039 : Blo 1682041 2131039 := bstep (se 1 (by rfl) ⟨1598279, by rfl⟩ : syracuseStep 2131039 = 3196559) B3196559
theorem B4318363 : Blo 1682041 4318363 := bstep (se 1 (by rfl) ⟨3238772, by rfl⟩ : syracuseStep 4318363 = 6477545) B6477545
theorem B1893631 : Blo 1682041 1893631 := bstep (se 1 (by rfl) ⟨1420223, by rfl⟩ : syracuseStep 1893631 = 2840447) B2840447
theorem B3786191 : Blo 1682041 3786191 := bstep (se 1 (by rfl) ⟨2839643, by rfl⟩ : syracuseStep 3786191 = 5679287) B5679287
theorem B9586259 : Blo 1682041 9586259 := bstep (se 1 (by rfl) ⟨7189694, by rfl⟩ : syracuseStep 9586259 = 14379389) B14379389
theorem B5678747 : Blo 1682041 5678747 := bstep (se 1 (by rfl) ⟨4259060, by rfl⟩ : syracuseStep 5678747 = 8518121) B8518121
theorem B4261855 : Blo 1682041 4261855 := bstep (se 1 (by rfl) ⟨3196391, by rfl⟩ : syracuseStep 4261855 = 6392783) B6392783
theorem B2525321 : Blo 1682041 2525321 := bstep (se 2 (by rfl) ⟨946995, by rfl⟩ : syracuseStep 2525321 = 1893991) B1893991
theorem B2525495 : Blo 1682041 2525495 := bstep (se 1 (by rfl) ⟨1894121, by rfl⟩ : syracuseStep 2525495 = 3788243) B3788243
theorem B3787145 : Blo 1682041 3787145 := bstep (se 2 (by rfl) ⟨1420179, by rfl⟩ : syracuseStep 3787145 = 2840359) B2840359
theorem B7186877 : Blo 1682041 7186877 := bstep (se 3 (by rfl) ⟨1347539, by rfl⟩ : syracuseStep 7186877 = 2695079) B2695079
theorem B8636969 : Blo 1682041 8636969 := bstep (se 2 (by rfl) ⟨3238863, by rfl⟩ : syracuseStep 8636969 = 6477727) B6477727
theorem B2525807 : Blo 1682041 2525807 := bstep (se 1 (by rfl) ⟨1894355, by rfl⟩ : syracuseStep 2525807 = 3788711) B3788711
theorem B1682075 : Blo 1682041 1682075 := bstep (se 1 (by rfl) ⟨1261556, by rfl⟩ : syracuseStep 1682075 = 2523113) B2523113
theorem B5679773 : Blo 1682041 5679773 := bstep (se 3 (by rfl) ⟨1064957, by rfl⟩ : syracuseStep 5679773 = 2129915) B2129915
theorem B1682087 : Blo 1682041 1682087 := bstep (se 1 (by rfl) ⟨1261565, by rfl⟩ : syracuseStep 1682087 = 2523131) B2523131
theorem B1682127 : Blo 1682041 1682127 := bstep (se 1 (by rfl) ⟨1261595, by rfl⟩ : syracuseStep 1682127 = 2523191) B2523191
theorem B1682151 : Blo 1682041 1682151 := bstep (se 1 (by rfl) ⟨1261613, by rfl⟩ : syracuseStep 1682151 = 2523227) B2523227
theorem B6744815 : Blo 1682041 6744815 := bstep (se 1 (by rfl) ⟨5058611, by rfl⟩ : syracuseStep 6744815 = 10117223) B10117223
theorem B4262665 : Blo 1682041 4262665 := bstep (se 2 (by rfl) ⟨1598499, by rfl⟩ : syracuseStep 4262665 = 3196999) B3196999
theorem B1682207 : Blo 1682041 1682207 := bstep (se 1 (by rfl) ⟨1261655, by rfl⟩ : syracuseStep 1682207 = 2523311) B2523311
theorem B163801925 : Blo 1682041 163801925 := bstep (se 4 (by rfl) ⟨15356430, by rfl⟩ : syracuseStep 163801925 = 30712861) B30712861
theorem B14371667 : Blo 1682041 14371667 := bstep (se 1 (by rfl) ⟨10778750, by rfl⟩ : syracuseStep 14371667 = 21557501) B21557501
theorem B13650875 : Blo 1682041 13650875 := bstep (se 1 (by rfl) ⟨10238156, by rfl⟩ : syracuseStep 13650875 = 20476313) B20476313
theorem B24259571 : Blo 1682041 24259571 := bstep (se 1 (by rfl) ⟨18194678, by rfl⟩ : syracuseStep 24259571 = 36389357) B36389357
theorem B1682599 : Blo 1682041 1682599 := bstep (se 1 (by rfl) ⟨1261949, by rfl⟩ : syracuseStep 1682599 = 2523899) B2523899
theorem B1682687 : Blo 1682041 1682687 := bstep (se 1 (by rfl) ⟨1262015, by rfl⟩ : syracuseStep 1682687 = 2524031) B2524031
theorem B19172699 : Blo 1682041 19172699 := bstep (se 1 (by rfl) ⟨14379524, by rfl⟩ : syracuseStep 19172699 = 28759049) B28759049
theorem B65613149 : Blo 1682041 65613149 := bstep (se 3 (by rfl) ⟨12302465, by rfl⟩ : syracuseStep 65613149 = 24604931) B24604931
theorem B3034523 : Blo 1682041 3034523 := bstep (se 1 (by rfl) ⟨2275892, by rfl⟩ : syracuseStep 3034523 = 4551785) B4551785
theorem B39407485 : Blo 1682041 39407485 := bstep (se 3 (by rfl) ⟨7388903, by rfl⟩ : syracuseStep 39407485 = 14777807) B14777807
theorem B8515529 : Blo 1682041 8515529 := bstep (se 2 (by rfl) ⟨3193323, by rfl⟩ : syracuseStep 8515529 = 6386647) B6386647
theorem B9588719 : Blo 1682041 9588719 := bstep (se 1 (by rfl) ⟨7191539, by rfl⟩ : syracuseStep 9588719 = 14383079) B14383079
theorem B1683487 : Blo 1682041 1683487 := bstep (se 1 (by rfl) ⟨1262615, by rfl⟩ : syracuseStep 1683487 = 2525231) B2525231
theorem B8515691 : Blo 1682041 8515691 := bstep (se 1 (by rfl) ⟨6386768, by rfl⟩ : syracuseStep 8515691 = 12773537) B12773537
theorem B9588901 : Blo 1682041 9588901 := bstep (se 4 (by rfl) ⟨898959, by rfl⟩ : syracuseStep 9588901 = 1797919) B1797919
theorem B1683967 : Blo 1682041 1683967 := bstep (se 1 (by rfl) ⟨1262975, by rfl⟩ : syracuseStep 1683967 = 2525951) B2525951
theorem B131101355 : Blo 1682041 131101355 := bstep (se 1 (by rfl) ⟨98326016, by rfl⟩ : syracuseStep 131101355 = 196652033) B196652033
theorem B72790811 : Blo 1682041 72790811 := bstep (se 1 (by rfl) ⟨54593108, by rfl⟩ : syracuseStep 72790811 = 109186217) B109186217
theorem B2397055 : Blo 1682041 2397055 := bstep (se 1 (by rfl) ⟨1797791, by rfl⟩ : syracuseStep 2397055 = 3595583) B3595583
theorem B6387119 : Blo 1682041 6387119 := bstep (se 1 (by rfl) ⟨4790339, by rfl⟩ : syracuseStep 6387119 = 9580679) B9580679
theorem B2840015 : Blo 1682041 2840015 := bstep (se 1 (by rfl) ⟨2130011, by rfl⟩ : syracuseStep 2840015 = 4260023) B4260023
theorem B9582137 : Blo 1682041 9582137 := bstep (se 2 (by rfl) ⟨3593301, by rfl⟩ : syracuseStep 9582137 = 7186603) B7186603
theorem B9590633 : Blo 1682041 9590633 := bstep (se 2 (by rfl) ⟨3596487, by rfl⟩ : syracuseStep 9590633 = 7192975) B7192975
theorem B32798645 : Blo 1682041 32798645 := bstep (se 5 (by rfl) ⟨1537436, by rfl⟩ : syracuseStep 32798645 = 3074873) B3074873
theorem B36386759 : Blo 1682041 36386759 := bstep (se 1 (by rfl) ⟨27290069, by rfl⟩ : syracuseStep 36386759 = 54580139) B54580139
theorem B9582569 : Blo 1682041 9582569 := bstep (se 2 (by rfl) ⟨3593463, by rfl⟩ : syracuseStep 9582569 = 7186927) B7186927
theorem B4790441 : Blo 1682041 4790441 := bstep (se 2 (by rfl) ⟨1796415, by rfl⟩ : syracuseStep 4790441 = 3592831) B3592831
theorem B4791079 : Blo 1682041 4791079 := bstep (se 1 (by rfl) ⟨3593309, by rfl⟩ : syracuseStep 4791079 = 7186619) B7186619
theorem B18193859 : Blo 1682041 18193859 := bstep (se 1 (by rfl) ⟨13645394, by rfl⟩ : syracuseStep 18193859 = 27290789) B27290789
theorem B24256223 : Blo 1682041 24256223 := bstep (se 1 (by rfl) ⟨18192167, by rfl⟩ : syracuseStep 24256223 = 36384335) B36384335
theorem B8519579 : Blo 1682041 8519579 := bstep (se 1 (by rfl) ⟨6389684, by rfl⟩ : syracuseStep 8519579 = 12779369) B12779369
theorem B3784607 : Blo 1682041 3784607 := bstep (se 1 (by rfl) ⟨2838455, by rfl⟩ : syracuseStep 3784607 = 5676911) B5676911
theorem B5390363 : Blo 1682041 5390363 := bstep (se 1 (by rfl) ⟨4042772, by rfl⟩ : syracuseStep 5390363 = 8085545) B8085545
theorem B5677127 : Blo 1682041 5677127 := bstep (se 1 (by rfl) ⟨4257845, by rfl⟩ : syracuseStep 5677127 = 8515691) B8515691
theorem B2523239 : Blo 1682041 2523239 := bstep (se 1 (by rfl) ⟨1892429, by rfl⟩ : syracuseStep 2523239 = 3784859) B3784859
theorem B8519903 : Blo 1682041 8519903 := bstep (se 1 (by rfl) ⟨6389927, by rfl⟩ : syracuseStep 8519903 = 12779855) B12779855
theorem B87400903 : Blo 1682041 87400903 := bstep (se 1 (by rfl) ⟨65550677, by rfl⟩ : syracuseStep 87400903 = 131101355) B131101355
theorem B3785183 : Blo 1682041 3785183 := bstep (se 1 (by rfl) ⟨2838887, by rfl⟩ : syracuseStep 3785183 = 5677775) B5677775
theorem B2523623 : Blo 1682041 2523623 := bstep (se 1 (by rfl) ⟨1892717, by rfl⟩ : syracuseStep 2523623 = 3785435) B3785435
theorem B2524127 : Blo 1682041 2524127 := bstep (se 1 (by rfl) ⟨1893095, by rfl⟩ : syracuseStep 2524127 = 3786191) B3786191
theorem B1893343 : Blo 1682041 1893343 := bstep (se 1 (by rfl) ⟨1420007, by rfl⟩ : syracuseStep 1893343 = 2840015) B2840015
theorem B6390839 : Blo 1682041 6390839 := bstep (se 1 (by rfl) ⟨4793129, by rfl⟩ : syracuseStep 6390839 = 9586259) B9586259
theorem B3785831 : Blo 1682041 3785831 := bstep (se 1 (by rfl) ⟨2839373, by rfl⟩ : syracuseStep 3785831 = 5678747) B5678747
theorem B3196073 : Blo 1682041 3196073 := bstep (se 2 (by rfl) ⟨1198527, by rfl⟩ : syracuseStep 3196073 = 2397055) B2397055
theorem B21865763 : Blo 1682041 21865763 := bstep (se 1 (by rfl) ⟨16399322, by rfl⟩ : syracuseStep 21865763 = 32798645) B32798645
theorem B24257839 : Blo 1682041 24257839 := bstep (se 1 (by rfl) ⟨18193379, by rfl⟩ : syracuseStep 24257839 = 36386759) B36386759
theorem B2524763 : Blo 1682041 2524763 := bstep (se 1 (by rfl) ⟨1893572, by rfl⟩ : syracuseStep 2524763 = 3787145) B3787145
theorem B2524841 : Blo 1682041 2524841 := bstep (se 2 (by rfl) ⟨946815, by rfl⟩ : syracuseStep 2524841 = 1893631) B1893631
theorem B3786515 : Blo 1682041 3786515 := bstep (se 1 (by rfl) ⟨2839886, by rfl⟩ : syracuseStep 3786515 = 5679773) B5679773
theorem B109201283 : Blo 1682041 109201283 := bstep (se 1 (by rfl) ⟨81900962, by rfl⟩ : syracuseStep 109201283 = 163801925) B163801925
theorem B16173047 : Blo 1682041 16173047 := bstep (se 1 (by rfl) ⟨12129785, by rfl⟩ : syracuseStep 16173047 = 24259571) B24259571
theorem B12781799 : Blo 1682041 12781799 := bstep (se 1 (by rfl) ⟨9586349, by rfl⟩ : syracuseStep 12781799 = 19172699) B19172699
theorem B5679719 : Blo 1682041 5679719 := bstep (se 1 (by rfl) ⟨4259789, by rfl⟩ : syracuseStep 5679719 = 8519579) B8519579
theorem B6392479 : Blo 1682041 6392479 := bstep (se 1 (by rfl) ⟨4794359, by rfl⟩ : syracuseStep 6392479 = 9588719) B9588719
theorem B1682343 : Blo 1682041 1682343 := bstep (se 1 (by rfl) ⟨1261757, by rfl⟩ : syracuseStep 1682343 = 2523515) B2523515
theorem B12774509 : Blo 1682041 12774509 := bstep (se 3 (by rfl) ⟨2395220, by rfl⟩ : syracuseStep 12774509 = 4790441) B4790441
theorem B1682663 : Blo 1682041 1682663 := bstep (se 1 (by rfl) ⟨1261997, by rfl⟩ : syracuseStep 1682663 = 2523995) B2523995
theorem B16395659 : Blo 1682041 16395659 := bstep (se 1 (by rfl) ⟨12296744, by rfl⟩ : syracuseStep 16395659 = 24593489) B24593489
theorem B5680637 : Blo 1682041 5680637 := bstep (se 3 (by rfl) ⟨1065119, by rfl⟩ : syracuseStep 5680637 = 2130239) B2130239
theorem B11677265 : Blo 1682041 11677265 := bstep (se 2 (by rfl) ⟨4378974, by rfl⟩ : syracuseStep 11677265 = 8757949) B8757949
theorem B48508753 : Blo 1682041 48508753 := bstep (se 2 (by rfl) ⟨18190782, by rfl⟩ : syracuseStep 48508753 = 36381565) B36381565
theorem B6393755 : Blo 1682041 6393755 := bstep (se 1 (by rfl) ⟨4795316, by rfl⟩ : syracuseStep 6393755 = 9590633) B9590633
theorem B1683547 : Blo 1682041 1683547 := bstep (se 1 (by rfl) ⟨1262660, by rfl⟩ : syracuseStep 1683547 = 2525321) B2525321
theorem B7188601 : Blo 1682041 7188601 := bstep (se 2 (by rfl) ⟨2695725, by rfl⟩ : syracuseStep 7188601 = 5391451) B5391451
theorem B1683663 : Blo 1682041 1683663 := bstep (se 1 (by rfl) ⟨1262747, by rfl⟩ : syracuseStep 1683663 = 2525495) B2525495
theorem B1683871 : Blo 1682041 1683871 := bstep (se 1 (by rfl) ⟨1262903, by rfl⟩ : syracuseStep 1683871 = 2525807) B2525807
theorem B9581111 : Blo 1682041 9581111 := bstep (se 1 (by rfl) ⟨7185833, by rfl⟩ : syracuseStep 9581111 = 14371667) B14371667
theorem B43742099 : Blo 1682041 43742099 := bstep (se 1 (by rfl) ⟨32806574, by rfl⟩ : syracuseStep 43742099 = 65613149) B65613149
theorem B12129239 : Blo 1682041 12129239 := bstep (se 1 (by rfl) ⟨9096929, by rfl⟩ : syracuseStep 12129239 = 18193859) B18193859
theorem B5682473 : Blo 1682041 5682473 := bstep (se 2 (by rfl) ⟨2130927, by rfl⟩ : syracuseStep 5682473 = 4261855) B4261855
theorem B12785201 : Blo 1682041 12785201 := bstep (se 2 (by rfl) ⟨4794450, by rfl⟩ : syracuseStep 12785201 = 9588901) B9588901
theorem B48527207 : Blo 1682041 48527207 := bstep (se 1 (by rfl) ⟨36395405, by rfl⟩ : syracuseStep 48527207 = 72790811) B72790811
theorem B43145135 : Blo 1682041 43145135 := bstep (se 1 (by rfl) ⟨32358851, by rfl⟩ : syracuseStep 43145135 = 64717703) B64717703
theorem B2840555 : Blo 1682041 2840555 := bstep (se 1 (by rfl) ⟨2130416, by rfl⟩ : syracuseStep 2840555 = 4260833) B4260833
theorem B4258079 : Blo 1682041 4258079 := bstep (se 1 (by rfl) ⟨3193559, by rfl⟩ : syracuseStep 4258079 = 6387119) B6387119
theorem B5683553 : Blo 1682041 5683553 := bstep (se 2 (by rfl) ⟨2131332, by rfl⟩ : syracuseStep 5683553 = 4262665) B4262665
theorem B6388091 : Blo 1682041 6388091 := bstep (se 1 (by rfl) ⟨4791068, by rfl⟩ : syracuseStep 6388091 = 9582137) B9582137
theorem B6388105 : Blo 1682041 6388105 := bstep (se 2 (by rfl) ⟨2395539, by rfl⟩ : syracuseStep 6388105 = 4791079) B4791079
theorem B8092061 : Blo 1682041 8092061 := bstep (se 3 (by rfl) ⟨1517261, by rfl⟩ : syracuseStep 8092061 = 3034523) B3034523
theorem B6388379 : Blo 1682041 6388379 := bstep (se 1 (by rfl) ⟨4791284, by rfl⟩ : syracuseStep 6388379 = 9582569) B9582569
theorem B2841385 : Blo 1682041 2841385 := bstep (se 2 (by rfl) ⟨1065519, by rfl⟩ : syracuseStep 2841385 = 2131039) B2131039
theorem B5757817 : Blo 1682041 5757817 := bstep (se 2 (by rfl) ⟨2159181, by rfl⟩ : syracuseStep 5757817 = 4318363) B4318363
theorem B4791251 : Blo 1682041 4791251 := bstep (se 1 (by rfl) ⟨3593438, by rfl⟩ : syracuseStep 4791251 = 7186877) B7186877
theorem B5757979 : Blo 1682041 5757979 := bstep (se 1 (by rfl) ⟨4318484, by rfl⟩ : syracuseStep 5757979 = 8636969) B8636969
theorem B4496543 : Blo 1682041 4496543 := bstep (se 1 (by rfl) ⟨3372407, by rfl⟩ : syracuseStep 4496543 = 6744815) B6744815
theorem B9100583 : Blo 1682041 9100583 := bstep (se 1 (by rfl) ⟨6825437, by rfl⟩ : syracuseStep 9100583 = 13650875) B13650875
theorem B16170815 : Blo 1682041 16170815 := bstep (se 1 (by rfl) ⟨12128111, by rfl⟩ : syracuseStep 16170815 = 24256223) B24256223
theorem B52543313 : Blo 1682041 52543313 := bstep (se 2 (by rfl) ⟨19703742, by rfl⟩ : syracuseStep 52543313 = 39407485) B39407485
theorem B2523071 : Blo 1682041 2523071 := bstep (se 1 (by rfl) ⟨1892303, by rfl⟩ : syracuseStep 2523071 = 3784607) B3784607
theorem B5677019 : Blo 1682041 5677019 := bstep (se 1 (by rfl) ⟨4257764, by rfl⟩ : syracuseStep 5677019 = 8515529) B8515529
theorem B3784751 : Blo 1682041 3784751 := bstep (se 1 (by rfl) ⟨2838563, by rfl⟩ : syracuseStep 3784751 = 5677127) B5677127
theorem B9584801 : Blo 1682041 9584801 := bstep (se 2 (by rfl) ⟨3594300, by rfl⟩ : syracuseStep 9584801 = 7188601) B7188601
theorem B2523455 : Blo 1682041 2523455 := bstep (se 1 (by rfl) ⟨1892591, by rfl⟩ : syracuseStep 2523455 = 3785183) B3785183
theorem B8086159 : Blo 1682041 8086159 := bstep (se 1 (by rfl) ⟨6064619, by rfl⟩ : syracuseStep 8086159 = 12129239) B12129239
theorem B4260559 : Blo 1682041 4260559 := bstep (se 1 (by rfl) ⟨3195419, by rfl⟩ : syracuseStep 4260559 = 6390839) B6390839
theorem B2523887 : Blo 1682041 2523887 := bstep (se 1 (by rfl) ⟨1892915, by rfl⟩ : syracuseStep 2523887 = 3785831) B3785831
theorem B2130715 : Blo 1682041 2130715 := bstep (se 1 (by rfl) ⟨1598036, by rfl⟩ : syracuseStep 2130715 = 3196073) B3196073
theorem B7677089 : Blo 1682041 7677089 := bstep (se 2 (by rfl) ⟨2878908, by rfl⟩ : syracuseStep 7677089 = 5757817) B5757817
theorem B2524343 : Blo 1682041 2524343 := bstep (se 1 (by rfl) ⟨1893257, by rfl⟩ : syracuseStep 2524343 = 3786515) B3786515
theorem B32351471 : Blo 1682041 32351471 := bstep (se 1 (by rfl) ⟨24263603, by rfl⟩ : syracuseStep 32351471 = 48527207) B48527207
theorem B28763423 : Blo 1682041 28763423 := bstep (se 1 (by rfl) ⟨21572567, by rfl⟩ : syracuseStep 28763423 = 43145135) B43145135
theorem B2524457 : Blo 1682041 2524457 := bstep (se 2 (by rfl) ⟨946671, by rfl⟩ : syracuseStep 2524457 = 1893343) B1893343
theorem B1893703 : Blo 1682041 1893703 := bstep (se 1 (by rfl) ⟨1420277, by rfl⟩ : syracuseStep 1893703 = 2840555) B2840555
theorem B10782031 : Blo 1682041 10782031 := bstep (se 1 (by rfl) ⟨8086523, by rfl⟩ : syracuseStep 10782031 = 16173047) B16173047
theorem B7677305 : Blo 1682041 7677305 := bstep (se 2 (by rfl) ⟨2878989, by rfl⟩ : syracuseStep 7677305 = 5757979) B5757979
theorem B8521199 : Blo 1682041 8521199 := bstep (se 1 (by rfl) ⟨6390899, by rfl⟩ : syracuseStep 8521199 = 12781799) B12781799
theorem B32343785 : Blo 1682041 32343785 := bstep (se 2 (by rfl) ⟨12128919, by rfl⟩ : syracuseStep 32343785 = 24257839) B24257839
theorem B3786479 : Blo 1682041 3786479 := bstep (se 1 (by rfl) ⟨2839859, by rfl⟩ : syracuseStep 3786479 = 5679719) B5679719
theorem B10930439 : Blo 1682041 10930439 := bstep (se 1 (by rfl) ⟨8197829, by rfl⟩ : syracuseStep 10930439 = 16395659) B16395659
theorem B3787091 : Blo 1682041 3787091 := bstep (se 1 (by rfl) ⟨2840318, by rfl⟩ : syracuseStep 3787091 = 5680637) B5680637
theorem B7784843 : Blo 1682041 7784843 := bstep (se 1 (by rfl) ⟨5838632, by rfl⟩ : syracuseStep 7784843 = 11677265) B11677265
theorem B64678337 : Blo 1682041 64678337 := bstep (se 2 (by rfl) ⟨24254376, by rfl⟩ : syracuseStep 64678337 = 48508753) B48508753
theorem B4262503 : Blo 1682041 4262503 := bstep (se 1 (by rfl) ⟨3196877, by rfl⟩ : syracuseStep 4262503 = 6393755) B6393755
theorem B1682047 : Blo 1682041 1682047 := bstep (se 1 (by rfl) ⟨1261535, by rfl⟩ : syracuseStep 1682047 = 2523071) B2523071
theorem B1682159 : Blo 1682041 1682159 := bstep (se 1 (by rfl) ⟨1261619, by rfl⟩ : syracuseStep 1682159 = 2523239) B2523239
theorem B5679935 : Blo 1682041 5679935 := bstep (se 1 (by rfl) ⟨4259951, by rfl⟩ : syracuseStep 5679935 = 8519903) B8519903
theorem B1682415 : Blo 1682041 1682415 := bstep (se 1 (by rfl) ⟨1261811, by rfl⟩ : syracuseStep 1682415 = 2523623) B2523623
theorem B116534537 : Blo 1682041 116534537 := bstep (se 2 (by rfl) ⟨43700451, by rfl⟩ : syracuseStep 116534537 = 87400903) B87400903
theorem B1682751 : Blo 1682041 1682751 := bstep (se 1 (by rfl) ⟨1262063, by rfl⟩ : syracuseStep 1682751 = 2524127) B2524127
theorem B14577175 : Blo 1682041 14577175 := bstep (se 1 (by rfl) ⟨10932881, by rfl⟩ : syracuseStep 14577175 = 21865763) B21865763
theorem B3788315 : Blo 1682041 3788315 := bstep (se 1 (by rfl) ⟨2841236, by rfl⟩ : syracuseStep 3788315 = 5682473) B5682473
theorem B8523305 : Blo 1682041 8523305 := bstep (se 2 (by rfl) ⟨3196239, by rfl⟩ : syracuseStep 8523305 = 6392479) B6392479
theorem B8523467 : Blo 1682041 8523467 := bstep (se 1 (by rfl) ⟨6392600, by rfl⟩ : syracuseStep 8523467 = 12785201) B12785201
theorem B3788513 : Blo 1682041 3788513 := bstep (se 2 (by rfl) ⟨1420692, by rfl⟩ : syracuseStep 3788513 = 2841385) B2841385
theorem B1683175 : Blo 1682041 1683175 := bstep (se 1 (by rfl) ⟨1262381, by rfl⟩ : syracuseStep 1683175 = 2524763) B2524763
theorem B1683227 : Blo 1682041 1683227 := bstep (se 1 (by rfl) ⟨1262420, by rfl⟩ : syracuseStep 1683227 = 2524841) B2524841
theorem B2838719 : Blo 1682041 2838719 := bstep (se 1 (by rfl) ⟨2129039, by rfl⟩ : syracuseStep 2838719 = 4258079) B4258079
theorem B3789035 : Blo 1682041 3789035 := bstep (se 1 (by rfl) ⟨2841776, by rfl⟩ : syracuseStep 3789035 = 5683553) B5683553
theorem B5394707 : Blo 1682041 5394707 := bstep (se 1 (by rfl) ⟨4046030, by rfl⟩ : syracuseStep 5394707 = 8092061) B8092061
theorem B8516339 : Blo 1682041 8516339 := bstep (se 1 (by rfl) ⟨6387254, by rfl⟩ : syracuseStep 8516339 = 12774509) B12774509
theorem B6067055 : Blo 1682041 6067055 := bstep (se 1 (by rfl) ⟨4550291, by rfl⟩ : syracuseStep 6067055 = 9100583) B9100583
theorem B3593575 : Blo 1682041 3593575 := bstep (se 1 (by rfl) ⟨2695181, by rfl⟩ : syracuseStep 3593575 = 5390363) B5390363
theorem B6387407 : Blo 1682041 6387407 := bstep (se 1 (by rfl) ⟨4790555, by rfl⟩ : syracuseStep 6387407 = 9581111) B9581111
theorem B8517473 : Blo 1682041 8517473 := bstep (se 2 (by rfl) ⟨3194052, by rfl⟩ : syracuseStep 8517473 = 6388105) B6388105
theorem B29161399 : Blo 1682041 29161399 := bstep (se 1 (by rfl) ⟨21871049, by rfl⟩ : syracuseStep 29161399 = 43742099) B43742099
theorem B72800855 : Blo 1682041 72800855 := bstep (se 1 (by rfl) ⟨54600641, by rfl⟩ : syracuseStep 72800855 = 109201283) B109201283
theorem B4258727 : Blo 1682041 4258727 := bstep (se 1 (by rfl) ⟨3194045, by rfl⟩ : syracuseStep 4258727 = 6388091) B6388091
theorem B4258919 : Blo 1682041 4258919 := bstep (se 1 (by rfl) ⟨3194189, by rfl⟩ : syracuseStep 4258919 = 6388379) B6388379
theorem B3194167 : Blo 1682041 3194167 := bstep (se 1 (by rfl) ⟨2395625, by rfl⟩ : syracuseStep 3194167 = 4791251) B4791251
theorem B2997695 : Blo 1682041 2997695 := bstep (se 1 (by rfl) ⟨2248271, by rfl⟩ : syracuseStep 2997695 = 4496543) B4496543
theorem B10780543 : Blo 1682041 10780543 := bstep (se 1 (by rfl) ⟨8085407, by rfl⟩ : syracuseStep 10780543 = 16170815) B16170815
theorem B35028875 : Blo 1682041 35028875 := bstep (se 1 (by rfl) ⟨26271656, by rfl⟩ : syracuseStep 35028875 = 52543313) B52543313
theorem B3784679 : Blo 1682041 3784679 := bstep (se 1 (by rfl) ⟨2838509, by rfl⟩ : syracuseStep 3784679 = 5677019) B5677019
theorem B2523167 : Blo 1682041 2523167 := bstep (se 1 (by rfl) ⟨1892375, by rfl⟩ : syracuseStep 2523167 = 3784751) B3784751
theorem B6389867 : Blo 1682041 6389867 := bstep (se 1 (by rfl) ⟨4792400, by rfl⟩ : syracuseStep 6389867 = 9584801) B9584801
theorem B1892479 : Blo 1682041 1892479 := bstep (se 1 (by rfl) ⟨1419359, by rfl⟩ : syracuseStep 1892479 = 2838719) B2838719
theorem B3596471 : Blo 1682041 3596471 := bstep (se 1 (by rfl) ⟨2697353, by rfl⟩ : syracuseStep 3596471 = 5394707) B5394707
theorem B5677559 : Blo 1682041 5677559 := bstep (se 1 (by rfl) ⟨4258169, by rfl⟩ : syracuseStep 5677559 = 8516339) B8516339
theorem B10781545 : Blo 1682041 10781545 := bstep (se 2 (by rfl) ⟨4043079, by rfl⟩ : syracuseStep 10781545 = 8086159) B8086159
theorem B20759581 : Blo 1682041 20759581 := bstep (se 3 (by rfl) ⟨3892421, by rfl⟩ : syracuseStep 20759581 = 7784843) B7784843
theorem B21562523 : Blo 1682041 21562523 := bstep (se 1 (by rfl) ⟨16171892, by rfl⟩ : syracuseStep 21562523 = 32343785) B32343785
theorem B2524319 : Blo 1682041 2524319 := bstep (se 1 (by rfl) ⟨1893239, by rfl⟩ : syracuseStep 2524319 = 3786479) B3786479
theorem B5678315 : Blo 1682041 5678315 := bstep (se 1 (by rfl) ⟨4258736, by rfl⟩ : syracuseStep 5678315 = 8517473) B8517473
theorem B2524727 : Blo 1682041 2524727 := bstep (se 1 (by rfl) ⟨1893545, by rfl⟩ : syracuseStep 2524727 = 3787091) B3787091
theorem B2524937 : Blo 1682041 2524937 := bstep (se 2 (by rfl) ⟨946851, by rfl⟩ : syracuseStep 2524937 = 1893703) B1893703
theorem B3786623 : Blo 1682041 3786623 := bstep (se 1 (by rfl) ⟨2839967, by rfl⟩ : syracuseStep 3786623 = 5679935) B5679935
theorem B2525543 : Blo 1682041 2525543 := bstep (se 1 (by rfl) ⟨1894157, by rfl⟩ : syracuseStep 2525543 = 3788315) B3788315
theorem B2525675 : Blo 1682041 2525675 := bstep (se 1 (by rfl) ⟨1894256, by rfl⟩ : syracuseStep 2525675 = 3788513) B3788513
theorem B38881865 : Blo 1682041 38881865 := bstep (se 2 (by rfl) ⟨14580699, by rfl⟩ : syracuseStep 38881865 = 29161399) B29161399
theorem B77744933 : Blo 1682041 77744933 := bstep (se 4 (by rfl) ⟨7288587, by rfl⟩ : syracuseStep 77744933 = 14577175) B14577175
theorem B2526023 : Blo 1682041 2526023 := bstep (se 1 (by rfl) ⟨1894517, by rfl⟩ : syracuseStep 2526023 = 3789035) B3789035
theorem B1682303 : Blo 1682041 1682303 := bstep (se 1 (by rfl) ⟨1261727, by rfl⟩ : syracuseStep 1682303 = 2523455) B2523455
theorem B1682591 : Blo 1682041 1682591 := bstep (se 1 (by rfl) ⟨1261943, by rfl⟩ : syracuseStep 1682591 = 2523887) B2523887
theorem B1682895 : Blo 1682041 1682895 := bstep (se 1 (by rfl) ⟨1262171, by rfl⟩ : syracuseStep 1682895 = 2524343) B2524343
theorem B1682971 : Blo 1682041 1682971 := bstep (se 1 (by rfl) ⟨1262228, by rfl⟩ : syracuseStep 1682971 = 2524457) B2524457
theorem B5680745 : Blo 1682041 5680745 := bstep (se 2 (by rfl) ⟨2130279, by rfl⟩ : syracuseStep 5680745 = 4260559) B4260559
theorem B5680799 : Blo 1682041 5680799 := bstep (se 1 (by rfl) ⟨4260599, by rfl⟩ : syracuseStep 5680799 = 8521199) B8521199
theorem B7286959 : Blo 1682041 7286959 := bstep (se 1 (by rfl) ⟨5465219, by rfl⟩ : syracuseStep 7286959 = 10930439) B10930439
theorem B43118891 : Blo 1682041 43118891 := bstep (se 1 (by rfl) ⟨32339168, by rfl⟩ : syracuseStep 43118891 = 64678337) B64678337
theorem B48533903 : Blo 1682041 48533903 := bstep (se 1 (by rfl) ⟨36400427, by rfl⟩ : syracuseStep 48533903 = 72800855) B72800855
theorem B2839151 : Blo 1682041 2839151 := bstep (se 1 (by rfl) ⟨2129363, by rfl⟩ : syracuseStep 2839151 = 4258727) B4258727
theorem B2839279 : Blo 1682041 2839279 := bstep (se 1 (by rfl) ⟨2129459, by rfl⟩ : syracuseStep 2839279 = 4258919) B4258919
theorem B77689691 : Blo 1682041 77689691 := bstep (se 1 (by rfl) ⟨58267268, by rfl⟩ : syracuseStep 77689691 = 116534537) B116534537
theorem B5682203 : Blo 1682041 5682203 := bstep (se 1 (by rfl) ⟨4261652, by rfl⟩ : syracuseStep 5682203 = 8523305) B8523305
theorem B93410333 : Blo 1682041 93410333 := bstep (se 3 (by rfl) ⟨17514437, by rfl⟩ : syracuseStep 93410333 = 35028875) B35028875
theorem B5682311 : Blo 1682041 5682311 := bstep (se 1 (by rfl) ⟨4261733, by rfl⟩ : syracuseStep 5682311 = 8523467) B8523467
theorem B14374057 : Blo 1682041 14374057 := bstep (se 2 (by rfl) ⟨5390271, by rfl⟩ : syracuseStep 14374057 = 10780543) B10780543
theorem B4044703 : Blo 1682041 4044703 := bstep (se 1 (by rfl) ⟨3033527, by rfl⟩ : syracuseStep 4044703 = 6067055) B6067055
theorem B5118059 : Blo 1682041 5118059 := bstep (se 1 (by rfl) ⟨3838544, by rfl⟩ : syracuseStep 5118059 = 7677089) B7677089
theorem B5683337 : Blo 1682041 5683337 := bstep (se 2 (by rfl) ⟨2131251, by rfl⟩ : syracuseStep 5683337 = 4262503) B4262503
theorem B21567647 : Blo 1682041 21567647 := bstep (se 1 (by rfl) ⟨16175735, by rfl⟩ : syracuseStep 21567647 = 32351471) B32351471
theorem B19175615 : Blo 1682041 19175615 := bstep (se 1 (by rfl) ⟨14381711, by rfl⟩ : syracuseStep 19175615 = 28763423) B28763423
theorem B5118203 : Blo 1682041 5118203 := bstep (se 1 (by rfl) ⟨3838652, by rfl⟩ : syracuseStep 5118203 = 7677305) B7677305
theorem B2840953 : Blo 1682041 2840953 := bstep (se 2 (by rfl) ⟨1065357, by rfl⟩ : syracuseStep 2840953 = 2130715) B2130715
theorem B4258271 : Blo 1682041 4258271 := bstep (se 1 (by rfl) ⟨3193703, by rfl⟩ : syracuseStep 4258271 = 6387407) B6387407
theorem B7993853 : Blo 1682041 7993853 := bstep (se 3 (by rfl) ⟨1498847, by rfl⟩ : syracuseStep 7993853 = 2997695) B2997695
theorem B4258889 : Blo 1682041 4258889 := bstep (se 2 (by rfl) ⟨1597083, by rfl⟩ : syracuseStep 4258889 = 3194167) B3194167
theorem B14376041 : Blo 1682041 14376041 := bstep (se 2 (by rfl) ⟨5391015, by rfl⟩ : syracuseStep 14376041 = 10782031) B10782031
theorem B4791433 : Blo 1682041 4791433 := bstep (se 2 (by rfl) ⟨1796787, by rfl⟩ : syracuseStep 4791433 = 3593575) B3593575
theorem B2523119 : Blo 1682041 2523119 := bstep (se 1 (by rfl) ⟨1892339, by rfl⟩ : syracuseStep 2523119 = 3784679) B3784679
theorem B4259911 : Blo 1682041 4259911 := bstep (se 1 (by rfl) ⟨3194933, by rfl⟩ : syracuseStep 4259911 = 6389867) B6389867
theorem B2523305 : Blo 1682041 2523305 := bstep (se 2 (by rfl) ⟨946239, by rfl⟩ : syracuseStep 2523305 = 1892479) B1892479
theorem B28745927 : Blo 1682041 28745927 := bstep (se 1 (by rfl) ⟨21559445, by rfl⟩ : syracuseStep 28745927 = 43118891) B43118891
theorem B9715945 : Blo 1682041 9715945 := bstep (se 2 (by rfl) ⟨3643479, by rfl⟩ : syracuseStep 9715945 = 7286959) B7286959
theorem B3785039 : Blo 1682041 3785039 := bstep (se 1 (by rfl) ⟨2838779, by rfl⟩ : syracuseStep 3785039 = 5677559) B5677559
theorem B1892767 : Blo 1682041 1892767 := bstep (se 1 (by rfl) ⟨1419575, by rfl⟩ : syracuseStep 1892767 = 2839151) B2839151
theorem B3785543 : Blo 1682041 3785543 := bstep (se 1 (by rfl) ⟨2839157, by rfl⟩ : syracuseStep 3785543 = 5678315) B5678315
theorem B3785705 : Blo 1682041 3785705 := bstep (se 2 (by rfl) ⟨1419639, by rfl⟩ : syracuseStep 3785705 = 2839279) B2839279
theorem B2524415 : Blo 1682041 2524415 := bstep (se 1 (by rfl) ⟨1893311, by rfl⟩ : syracuseStep 2524415 = 3786623) B3786623
theorem B14378431 : Blo 1682041 14378431 := bstep (se 1 (by rfl) ⟨10783823, by rfl⟩ : syracuseStep 14378431 = 21567647) B21567647
theorem B25921243 : Blo 1682041 25921243 := bstep (se 1 (by rfl) ⟨19440932, by rfl⟩ : syracuseStep 25921243 = 38881865) B38881865
theorem B3787163 : Blo 1682041 3787163 := bstep (se 1 (by rfl) ⟨2840372, by rfl⟩ : syracuseStep 3787163 = 5680745) B5680745
theorem B3787199 : Blo 1682041 3787199 := bstep (se 1 (by rfl) ⟨2840399, by rfl⟩ : syracuseStep 3787199 = 5680799) B5680799
theorem B5392937 : Blo 1682041 5392937 := bstep (se 2 (by rfl) ⟨2022351, by rfl⟩ : syracuseStep 5392937 = 4044703) B4044703
theorem B1682079 : Blo 1682041 1682079 := bstep (se 1 (by rfl) ⟨1261559, by rfl⟩ : syracuseStep 1682079 = 2523119) B2523119
theorem B1682111 : Blo 1682041 1682111 := bstep (se 1 (by rfl) ⟨1261583, by rfl⟩ : syracuseStep 1682111 = 2523167) B2523167
theorem B110717765 : Blo 1682041 110717765 := bstep (se 4 (by rfl) ⟨10379790, by rfl⟩ : syracuseStep 110717765 = 20759581) B20759581
theorem B3787937 : Blo 1682041 3787937 := bstep (se 2 (by rfl) ⟨1420476, by rfl⟩ : syracuseStep 3787937 = 2840953) B2840953
theorem B51793127 : Blo 1682041 51793127 := bstep (se 1 (by rfl) ⟨38844845, by rfl⟩ : syracuseStep 51793127 = 77689691) B77689691
theorem B3788135 : Blo 1682041 3788135 := bstep (se 1 (by rfl) ⟨2841101, by rfl⟩ : syracuseStep 3788135 = 5682203) B5682203
theorem B3788207 : Blo 1682041 3788207 := bstep (se 1 (by rfl) ⟨2841155, by rfl⟩ : syracuseStep 3788207 = 5682311) B5682311
theorem B1682879 : Blo 1682041 1682879 := bstep (se 1 (by rfl) ⟨1262159, by rfl⟩ : syracuseStep 1682879 = 2524319) B2524319
theorem B1683151 : Blo 1682041 1683151 := bstep (se 1 (by rfl) ⟨1262363, by rfl⟩ : syracuseStep 1683151 = 2524727) B2524727
theorem B1683291 : Blo 1682041 1683291 := bstep (se 1 (by rfl) ⟨1262468, by rfl⟩ : syracuseStep 1683291 = 2524937) B2524937
theorem B3412039 : Blo 1682041 3412039 := bstep (se 1 (by rfl) ⟨2559029, by rfl⟩ : syracuseStep 3412039 = 5118059) B5118059
theorem B3788891 : Blo 1682041 3788891 := bstep (se 1 (by rfl) ⟨2841668, by rfl⟩ : syracuseStep 3788891 = 5683337) B5683337
theorem B12783743 : Blo 1682041 12783743 := bstep (se 1 (by rfl) ⟨9587807, by rfl⟩ : syracuseStep 12783743 = 19175615) B19175615
theorem B3412135 : Blo 1682041 3412135 := bstep (se 1 (by rfl) ⟨2559101, by rfl⟩ : syracuseStep 3412135 = 5118203) B5118203
theorem B19165409 : Blo 1682041 19165409 := bstep (se 2 (by rfl) ⟨7187028, by rfl⟩ : syracuseStep 19165409 = 14374057) B14374057
theorem B1683695 : Blo 1682041 1683695 := bstep (se 1 (by rfl) ⟨1262771, by rfl⟩ : syracuseStep 1683695 = 2525543) B2525543
theorem B2838847 : Blo 1682041 2838847 := bstep (se 1 (by rfl) ⟨2129135, by rfl⟩ : syracuseStep 2838847 = 4258271) B4258271
theorem B1683783 : Blo 1682041 1683783 := bstep (se 1 (by rfl) ⟨1262837, by rfl⟩ : syracuseStep 1683783 = 2525675) B2525675
theorem B5329235 : Blo 1682041 5329235 := bstep (se 1 (by rfl) ⟨3996926, by rfl⟩ : syracuseStep 5329235 = 7993853) B7993853
theorem B1684015 : Blo 1682041 1684015 := bstep (se 1 (by rfl) ⟨1263011, by rfl⟩ : syracuseStep 1684015 = 2526023) B2526023
theorem B2839259 : Blo 1682041 2839259 := bstep (se 1 (by rfl) ⟨2129444, by rfl⟩ : syracuseStep 2839259 = 4258889) B4258889
theorem B2397647 : Blo 1682041 2397647 := bstep (se 1 (by rfl) ⟨1798235, by rfl⟩ : syracuseStep 2397647 = 3596471) B3596471
theorem B32355935 : Blo 1682041 32355935 := bstep (se 1 (by rfl) ⟨24266951, by rfl⟩ : syracuseStep 32355935 = 48533903) B48533903
theorem B62273555 : Blo 1682041 62273555 := bstep (se 1 (by rfl) ⟨46705166, by rfl⟩ : syracuseStep 62273555 = 93410333) B93410333
theorem B14375015 : Blo 1682041 14375015 := bstep (se 1 (by rfl) ⟨10781261, by rfl⟩ : syracuseStep 14375015 = 21562523) B21562523
theorem B14375393 : Blo 1682041 14375393 := bstep (se 2 (by rfl) ⟨5390772, by rfl⟩ : syracuseStep 14375393 = 10781545) B10781545
theorem B6388577 : Blo 1682041 6388577 := bstep (se 2 (by rfl) ⟨2395716, by rfl⟩ : syracuseStep 6388577 = 4791433) B4791433
theorem B51829955 : Blo 1682041 51829955 := bstep (se 1 (by rfl) ⟨38872466, by rfl⟩ : syracuseStep 51829955 = 77744933) B77744933
theorem B9584027 : Blo 1682041 9584027 := bstep (se 1 (by rfl) ⟨7188020, by rfl⟩ : syracuseStep 9584027 = 14376041) B14376041
theorem B2523359 : Blo 1682041 2523359 := bstep (se 1 (by rfl) ⟨1892519, by rfl⟩ : syracuseStep 2523359 = 3785039) B3785039
theorem B3785129 : Blo 1682041 3785129 := bstep (se 2 (by rfl) ⟨1419423, by rfl⟩ : syracuseStep 3785129 = 2838847) B2838847
theorem B1892839 : Blo 1682041 1892839 := bstep (se 1 (by rfl) ⟨1419629, by rfl⟩ : syracuseStep 1892839 = 2839259) B2839259
theorem B2523689 : Blo 1682041 2523689 := bstep (se 2 (by rfl) ⟨946383, by rfl⟩ : syracuseStep 2523689 = 1892767) B1892767
theorem B2523695 : Blo 1682041 2523695 := bstep (se 1 (by rfl) ⟨1892771, by rfl⟩ : syracuseStep 2523695 = 3785543) B3785543
theorem B2523803 : Blo 1682041 2523803 := bstep (se 1 (by rfl) ⟨1892852, by rfl⟩ : syracuseStep 2523803 = 3785705) B3785705
theorem B21570623 : Blo 1682041 21570623 := bstep (se 1 (by rfl) ⟨16177967, by rfl⟩ : syracuseStep 21570623 = 32355935) B32355935
theorem B2524775 : Blo 1682041 2524775 := bstep (se 1 (by rfl) ⟨1893581, by rfl⟩ : syracuseStep 2524775 = 3787163) B3787163
theorem B2524799 : Blo 1682041 2524799 := bstep (se 1 (by rfl) ⟨1893599, by rfl⟩ : syracuseStep 2524799 = 3787199) B3787199
theorem B73811843 : Blo 1682041 73811843 := bstep (se 1 (by rfl) ⟨55358882, by rfl⟩ : syracuseStep 73811843 = 110717765) B110717765
theorem B19171241 : Blo 1682041 19171241 := bstep (se 2 (by rfl) ⟨7189215, by rfl⟩ : syracuseStep 19171241 = 14378431) B14378431
theorem B2525291 : Blo 1682041 2525291 := bstep (se 1 (by rfl) ⟨1893968, by rfl⟩ : syracuseStep 2525291 = 3787937) B3787937
theorem B2525423 : Blo 1682041 2525423 := bstep (se 1 (by rfl) ⟨1894067, by rfl⟩ : syracuseStep 2525423 = 3788135) B3788135
theorem B2525471 : Blo 1682041 2525471 := bstep (se 1 (by rfl) ⟨1894103, by rfl⟩ : syracuseStep 2525471 = 3788207) B3788207
theorem B2525927 : Blo 1682041 2525927 := bstep (se 1 (by rfl) ⟨1894445, by rfl⟩ : syracuseStep 2525927 = 3788891) B3788891
theorem B8522495 : Blo 1682041 8522495 := bstep (se 1 (by rfl) ⟨6391871, by rfl⟩ : syracuseStep 8522495 = 12783743) B12783743
theorem B5679881 : Blo 1682041 5679881 := bstep (se 2 (by rfl) ⟨2129955, by rfl⟩ : syracuseStep 5679881 = 4259911) B4259911
theorem B4549385 : Blo 1682041 4549385 := bstep (se 2 (by rfl) ⟨1706019, by rfl⟩ : syracuseStep 4549385 = 3412039) B3412039
theorem B1682203 : Blo 1682041 1682203 := bstep (se 1 (by rfl) ⟨1261652, by rfl⟩ : syracuseStep 1682203 = 2523305) B2523305
theorem B19163951 : Blo 1682041 19163951 := bstep (se 1 (by rfl) ⟨14372963, by rfl⟩ : syracuseStep 19163951 = 28745927) B28745927
theorem B4549513 : Blo 1682041 4549513 := bstep (se 2 (by rfl) ⟨1706067, by rfl⟩ : syracuseStep 4549513 = 3412135) B3412135
theorem B12954593 : Blo 1682041 12954593 := bstep (se 2 (by rfl) ⟨4857972, by rfl⟩ : syracuseStep 12954593 = 9715945) B9715945
theorem B1682943 : Blo 1682041 1682943 := bstep (se 1 (by rfl) ⟨1262207, by rfl⟩ : syracuseStep 1682943 = 2524415) B2524415
theorem B6393725 : Blo 1682041 6393725 := bstep (se 3 (by rfl) ⟨1198823, by rfl⟩ : syracuseStep 6393725 = 2397647) B2397647
theorem B14381165 : Blo 1682041 14381165 := bstep (se 3 (by rfl) ⟨2696468, by rfl⟩ : syracuseStep 14381165 = 5392937) B5392937
theorem B12776939 : Blo 1682041 12776939 := bstep (se 1 (by rfl) ⟨9582704, by rfl⟩ : syracuseStep 12776939 = 19165409) B19165409
theorem B14211293 : Blo 1682041 14211293 := bstep (se 3 (by rfl) ⟨2664617, by rfl⟩ : syracuseStep 14211293 = 5329235) B5329235
theorem B41515703 : Blo 1682041 41515703 := bstep (se 1 (by rfl) ⟨31136777, by rfl⟩ : syracuseStep 41515703 = 62273555) B62273555
theorem B9583343 : Blo 1682041 9583343 := bstep (se 1 (by rfl) ⟨7187507, by rfl⟩ : syracuseStep 9583343 = 14375015) B14375015
theorem B9583595 : Blo 1682041 9583595 := bstep (se 1 (by rfl) ⟨7187696, by rfl⟩ : syracuseStep 9583595 = 14375393) B14375393
theorem B4259051 : Blo 1682041 4259051 := bstep (se 1 (by rfl) ⟨3194288, by rfl⟩ : syracuseStep 4259051 = 6388577) B6388577
theorem B34553303 : Blo 1682041 34553303 := bstep (se 1 (by rfl) ⟨25914977, by rfl⟩ : syracuseStep 34553303 = 51829955) B51829955
theorem B34528751 : Blo 1682041 34528751 := bstep (se 1 (by rfl) ⟨25896563, by rfl⟩ : syracuseStep 34528751 = 51793127) B51793127
theorem B6389351 : Blo 1682041 6389351 := bstep (se 1 (by rfl) ⟨4792013, by rfl⟩ : syracuseStep 6389351 = 9584027) B9584027
theorem B34561657 : Blo 1682041 34561657 := bstep (se 2 (by rfl) ⟨12960621, by rfl⟩ : syracuseStep 34561657 = 25921243) B25921243
theorem B2523419 : Blo 1682041 2523419 := bstep (se 1 (by rfl) ⟨1892564, by rfl⟩ : syracuseStep 2523419 = 3785129) B3785129
theorem B37896781 : Blo 1682041 37896781 := bstep (se 3 (by rfl) ⟨7105646, by rfl⟩ : syracuseStep 37896781 = 14211293) B14211293
theorem B2523785 : Blo 1682041 2523785 := bstep (se 2 (by rfl) ⟨946419, by rfl⟩ : syracuseStep 2523785 = 1892839) B1892839
theorem B12780827 : Blo 1682041 12780827 := bstep (se 1 (by rfl) ⟨9585620, by rfl⟩ : syracuseStep 12780827 = 19171241) B19171241
theorem B3786587 : Blo 1682041 3786587 := bstep (se 1 (by rfl) ⟨2839940, by rfl⟩ : syracuseStep 3786587 = 5679881) B5679881
theorem B3032923 : Blo 1682041 3032923 := bstep (se 1 (by rfl) ⟨2274692, by rfl⟩ : syracuseStep 3032923 = 4549385) B4549385
theorem B8636395 : Blo 1682041 8636395 := bstep (se 1 (by rfl) ⟨6477296, by rfl⟩ : syracuseStep 8636395 = 12954593) B12954593
theorem B46082209 : Blo 1682041 46082209 := bstep (se 2 (by rfl) ⟨17280828, by rfl⟩ : syracuseStep 46082209 = 34561657) B34561657
theorem B4262483 : Blo 1682041 4262483 := bstep (se 1 (by rfl) ⟨3196862, by rfl⟩ : syracuseStep 4262483 = 6393725) B6393725
theorem B9587443 : Blo 1682041 9587443 := bstep (se 1 (by rfl) ⟨7190582, by rfl⟩ : syracuseStep 9587443 = 14381165) B14381165
theorem B1682239 : Blo 1682041 1682239 := bstep (se 1 (by rfl) ⟨1261679, by rfl⟩ : syracuseStep 1682239 = 2523359) B2523359
theorem B1682459 : Blo 1682041 1682459 := bstep (se 1 (by rfl) ⟨1261844, by rfl⟩ : syracuseStep 1682459 = 2523689) B2523689
theorem B1682463 : Blo 1682041 1682463 := bstep (se 1 (by rfl) ⟨1261847, by rfl⟩ : syracuseStep 1682463 = 2523695) B2523695
theorem B1682535 : Blo 1682041 1682535 := bstep (se 1 (by rfl) ⟨1261901, by rfl⟩ : syracuseStep 1682535 = 2523803) B2523803
theorem B14380415 : Blo 1682041 14380415 := bstep (se 1 (by rfl) ⟨10785311, by rfl⟩ : syracuseStep 14380415 = 21570623) B21570623
theorem B1683183 : Blo 1682041 1683183 := bstep (se 1 (by rfl) ⟨1262387, by rfl⟩ : syracuseStep 1683183 = 2524775) B2524775
theorem B1683199 : Blo 1682041 1683199 := bstep (se 1 (by rfl) ⟨1262399, by rfl⟩ : syracuseStep 1683199 = 2524799) B2524799
theorem B6066017 : Blo 1682041 6066017 := bstep (se 2 (by rfl) ⟨2274756, by rfl⟩ : syracuseStep 6066017 = 4549513) B4549513
theorem B1683527 : Blo 1682041 1683527 := bstep (se 1 (by rfl) ⟨1262645, by rfl⟩ : syracuseStep 1683527 = 2525291) B2525291
theorem B1683615 : Blo 1682041 1683615 := bstep (se 1 (by rfl) ⟨1262711, by rfl⟩ : syracuseStep 1683615 = 2525423) B2525423
theorem B1683647 : Blo 1682041 1683647 := bstep (se 1 (by rfl) ⟨1262735, by rfl⟩ : syracuseStep 1683647 = 2525471) B2525471
theorem B27677135 : Blo 1682041 27677135 := bstep (se 1 (by rfl) ⟨20757851, by rfl⟩ : syracuseStep 27677135 = 41515703) B41515703
theorem B1683951 : Blo 1682041 1683951 := bstep (se 1 (by rfl) ⟨1262963, by rfl⟩ : syracuseStep 1683951 = 2525927) B2525927
theorem B5681663 : Blo 1682041 5681663 := bstep (se 1 (by rfl) ⟨4261247, by rfl⟩ : syracuseStep 5681663 = 8522495) B8522495
theorem B12775967 : Blo 1682041 12775967 := bstep (se 1 (by rfl) ⟨9581975, by rfl⟩ : syracuseStep 12775967 = 19163951) B19163951
theorem B2839367 : Blo 1682041 2839367 := bstep (se 1 (by rfl) ⟨2129525, by rfl⟩ : syracuseStep 2839367 = 4259051) B4259051
theorem B8517959 : Blo 1682041 8517959 := bstep (se 1 (by rfl) ⟨6388469, by rfl⟩ : syracuseStep 8517959 = 12776939) B12776939
theorem B49207895 : Blo 1682041 49207895 := bstep (se 1 (by rfl) ⟨36905921, by rfl⟩ : syracuseStep 49207895 = 73811843) B73811843
theorem B6388895 : Blo 1682041 6388895 := bstep (se 1 (by rfl) ⟨4791671, by rfl⟩ : syracuseStep 6388895 = 9583343) B9583343
theorem B6389063 : Blo 1682041 6389063 := bstep (se 1 (by rfl) ⟨4791797, by rfl⟩ : syracuseStep 6389063 = 9583595) B9583595
theorem B23035535 : Blo 1682041 23035535 := bstep (se 1 (by rfl) ⟨17276651, by rfl⟩ : syracuseStep 23035535 = 34553303) B34553303
theorem B23019167 : Blo 1682041 23019167 := bstep (se 1 (by rfl) ⟨17264375, by rfl⟩ : syracuseStep 23019167 = 34528751) B34528751
theorem B4259567 : Blo 1682041 4259567 := bstep (se 1 (by rfl) ⟨3194675, by rfl⟩ : syracuseStep 4259567 = 6389351) B6389351
theorem B1892911 : Blo 1682041 1892911 := bstep (se 1 (by rfl) ⟨1419683, by rfl⟩ : syracuseStep 1892911 = 2839367) B2839367
theorem B50529041 : Blo 1682041 50529041 := bstep (se 2 (by rfl) ⟨18948390, by rfl⟩ : syracuseStep 50529041 = 37896781) B37896781
theorem B8520551 : Blo 1682041 8520551 := bstep (se 1 (by rfl) ⟨6390413, by rfl⟩ : syracuseStep 8520551 = 12780827) B12780827
theorem B2524391 : Blo 1682041 2524391 := bstep (se 1 (by rfl) ⟨1893293, by rfl⟩ : syracuseStep 2524391 = 3786587) B3786587
theorem B5678639 : Blo 1682041 5678639 := bstep (se 1 (by rfl) ⟨4258979, by rfl⟩ : syracuseStep 5678639 = 8517959) B8517959
theorem B9586943 : Blo 1682041 9586943 := bstep (se 1 (by rfl) ⟨7190207, by rfl⟩ : syracuseStep 9586943 = 14380415) B14380415
theorem B15346111 : Blo 1682041 15346111 := bstep (se 1 (by rfl) ⟨11509583, by rfl⟩ : syracuseStep 15346111 = 23019167) B23019167
theorem B1682279 : Blo 1682041 1682279 := bstep (se 1 (by rfl) ⟨1261709, by rfl⟩ : syracuseStep 1682279 = 2523419) B2523419
theorem B61442945 : Blo 1682041 61442945 := bstep (se 2 (by rfl) ⟨23041104, by rfl⟩ : syracuseStep 61442945 = 46082209) B46082209
theorem B18451423 : Blo 1682041 18451423 := bstep (se 1 (by rfl) ⟨13838567, by rfl⟩ : syracuseStep 18451423 = 27677135) B27677135
theorem B3787775 : Blo 1682041 3787775 := bstep (se 1 (by rfl) ⟨2840831, by rfl⟩ : syracuseStep 3787775 = 5681663) B5681663
theorem B1682523 : Blo 1682041 1682523 := bstep (se 1 (by rfl) ⟨1261892, by rfl⟩ : syracuseStep 1682523 = 2523785) B2523785
theorem B12783257 : Blo 1682041 12783257 := bstep (se 2 (by rfl) ⟨4793721, by rfl⟩ : syracuseStep 12783257 = 9587443) B9587443
theorem B32805263 : Blo 1682041 32805263 := bstep (se 1 (by rfl) ⟨24603947, by rfl⟩ : syracuseStep 32805263 = 49207895) B49207895
theorem B15357023 : Blo 1682041 15357023 := bstep (se 1 (by rfl) ⟨11517767, by rfl⟩ : syracuseStep 15357023 = 23035535) B23035535
theorem B4043897 : Blo 1682041 4043897 := bstep (se 2 (by rfl) ⟨1516461, by rfl⟩ : syracuseStep 4043897 = 3032923) B3032923
theorem B2839711 : Blo 1682041 2839711 := bstep (se 1 (by rfl) ⟨2129783, by rfl⟩ : syracuseStep 2839711 = 4259567) B4259567
theorem B4044011 : Blo 1682041 4044011 := bstep (se 1 (by rfl) ⟨3033008, by rfl⟩ : syracuseStep 4044011 = 6066017) B6066017
theorem B11515193 : Blo 1682041 11515193 := bstep (se 2 (by rfl) ⟨4318197, by rfl⟩ : syracuseStep 11515193 = 8636395) B8636395
theorem B8517311 : Blo 1682041 8517311 := bstep (se 1 (by rfl) ⟨6387983, by rfl⟩ : syracuseStep 8517311 = 12775967) B12775967
theorem B2841655 : Blo 1682041 2841655 := bstep (se 1 (by rfl) ⟨2131241, by rfl⟩ : syracuseStep 2841655 = 4262483) B4262483
theorem B4259263 : Blo 1682041 4259263 := bstep (se 1 (by rfl) ⟨3194447, by rfl⟩ : syracuseStep 4259263 = 6388895) B6388895
theorem B4259375 : Blo 1682041 4259375 := bstep (se 1 (by rfl) ⟨3194531, by rfl⟩ : syracuseStep 4259375 = 6389063) B6389063
theorem B33686027 : Blo 1682041 33686027 := bstep (se 1 (by rfl) ⟨25264520, by rfl⟩ : syracuseStep 33686027 = 50529041) B50529041
theorem B2523881 : Blo 1682041 2523881 := bstep (se 2 (by rfl) ⟨946455, by rfl⟩ : syracuseStep 2523881 = 1892911) B1892911
theorem B2695931 : Blo 1682041 2695931 := bstep (se 1 (by rfl) ⟨2021948, by rfl⟩ : syracuseStep 2695931 = 4043897) B4043897
theorem B7676795 : Blo 1682041 7676795 := bstep (se 1 (by rfl) ⟨5757596, by rfl⟩ : syracuseStep 7676795 = 11515193) B11515193
theorem B3785759 : Blo 1682041 3785759 := bstep (se 1 (by rfl) ⟨2839319, by rfl⟩ : syracuseStep 3785759 = 5678639) B5678639
theorem B5678207 : Blo 1682041 5678207 := bstep (se 1 (by rfl) ⟨4258655, by rfl⟩ : syracuseStep 5678207 = 8517311) B8517311
theorem B24601897 : Blo 1682041 24601897 := bstep (se 2 (by rfl) ⟨9225711, by rfl⟩ : syracuseStep 24601897 = 18451423) B18451423
theorem B6391295 : Blo 1682041 6391295 := bstep (se 1 (by rfl) ⟨4793471, by rfl⟩ : syracuseStep 6391295 = 9586943) B9586943
theorem B3786281 : Blo 1682041 3786281 := bstep (se 2 (by rfl) ⟨1419855, by rfl⟩ : syracuseStep 3786281 = 2839711) B2839711
theorem B5679017 : Blo 1682041 5679017 := bstep (se 2 (by rfl) ⟨2129631, by rfl⟩ : syracuseStep 5679017 = 4259263) B4259263
theorem B40961963 : Blo 1682041 40961963 := bstep (se 1 (by rfl) ⟨30721472, by rfl⟩ : syracuseStep 40961963 = 61442945) B61442945
theorem B2525183 : Blo 1682041 2525183 := bstep (se 1 (by rfl) ⟨1893887, by rfl⟩ : syracuseStep 2525183 = 3787775) B3787775
theorem B8522171 : Blo 1682041 8522171 := bstep (se 1 (by rfl) ⟨6391628, by rfl⟩ : syracuseStep 8522171 = 12783257) B12783257
theorem B5680367 : Blo 1682041 5680367 := bstep (se 1 (by rfl) ⟨4260275, by rfl⟩ : syracuseStep 5680367 = 8520551) B8520551
theorem B10784029 : Blo 1682041 10784029 := bstep (se 3 (by rfl) ⟨2022005, by rfl⟩ : syracuseStep 10784029 = 4044011) B4044011
theorem B1682927 : Blo 1682041 1682927 := bstep (se 1 (by rfl) ⟨1262195, by rfl⟩ : syracuseStep 1682927 = 2524391) B2524391
theorem B3788873 : Blo 1682041 3788873 := bstep (se 2 (by rfl) ⟨1420827, by rfl⟩ : syracuseStep 3788873 = 2841655) B2841655
theorem B2839583 : Blo 1682041 2839583 := bstep (se 1 (by rfl) ⟨2129687, by rfl⟩ : syracuseStep 2839583 = 4259375) B4259375
theorem B21870175 : Blo 1682041 21870175 := bstep (se 1 (by rfl) ⟨16402631, by rfl⟩ : syracuseStep 21870175 = 32805263) B32805263
theorem B20461481 : Blo 1682041 20461481 := bstep (se 2 (by rfl) ⟨7673055, by rfl⟩ : syracuseStep 20461481 = 15346111) B15346111
theorem B10238015 : Blo 1682041 10238015 := bstep (se 1 (by rfl) ⟨7678511, by rfl⟩ : syracuseStep 10238015 = 15357023) B15357023
theorem B2523839 : Blo 1682041 2523839 := bstep (se 1 (by rfl) ⟨1892879, by rfl⟩ : syracuseStep 2523839 = 3785759) B3785759
theorem B1893055 : Blo 1682041 1893055 := bstep (se 1 (by rfl) ⟨1419791, by rfl⟩ : syracuseStep 1893055 = 2839583) B2839583
theorem B3785471 : Blo 1682041 3785471 := bstep (se 1 (by rfl) ⟨2839103, by rfl⟩ : syracuseStep 3785471 = 5678207) B5678207
theorem B4260863 : Blo 1682041 4260863 := bstep (se 1 (by rfl) ⟨3195647, by rfl⟩ : syracuseStep 4260863 = 6391295) B6391295
theorem B2524187 : Blo 1682041 2524187 := bstep (se 1 (by rfl) ⟨1893140, by rfl⟩ : syracuseStep 2524187 = 3786281) B3786281
theorem B13640987 : Blo 1682041 13640987 := bstep (se 1 (by rfl) ⟨10230740, by rfl⟩ : syracuseStep 13640987 = 20461481) B20461481
theorem B3786011 : Blo 1682041 3786011 := bstep (se 1 (by rfl) ⟨2839508, by rfl⟩ : syracuseStep 3786011 = 5679017) B5679017
theorem B6825343 : Blo 1682041 6825343 := bstep (se 1 (by rfl) ⟨5119007, by rfl⟩ : syracuseStep 6825343 = 10238015) B10238015
theorem B14378705 : Blo 1682041 14378705 := bstep (se 2 (by rfl) ⟨5392014, by rfl⟩ : syracuseStep 14378705 = 10784029) B10784029
theorem B32802529 : Blo 1682041 32802529 := bstep (se 2 (by rfl) ⟨12300948, by rfl⟩ : syracuseStep 32802529 = 24601897) B24601897
theorem B3786911 : Blo 1682041 3786911 := bstep (se 1 (by rfl) ⟨2840183, by rfl⟩ : syracuseStep 3786911 = 5680367) B5680367
theorem B2525915 : Blo 1682041 2525915 := bstep (se 1 (by rfl) ⟨1894436, by rfl⟩ : syracuseStep 2525915 = 3788873) B3788873
theorem B22457351 : Blo 1682041 22457351 := bstep (se 1 (by rfl) ⟨16843013, by rfl⟩ : syracuseStep 22457351 = 33686027) B33686027
theorem B1682587 : Blo 1682041 1682587 := bstep (se 1 (by rfl) ⟨1261940, by rfl⟩ : syracuseStep 1682587 = 2523881) B2523881
theorem B1797287 : Blo 1682041 1797287 := bstep (se 1 (by rfl) ⟨1347965, by rfl⟩ : syracuseStep 1797287 = 2695931) B2695931
theorem B27307975 : Blo 1682041 27307975 := bstep (se 1 (by rfl) ⟨20480981, by rfl⟩ : syracuseStep 27307975 = 40961963) B40961963
theorem B1683455 : Blo 1682041 1683455 := bstep (se 1 (by rfl) ⟨1262591, by rfl⟩ : syracuseStep 1683455 = 2525183) B2525183
theorem B5681447 : Blo 1682041 5681447 := bstep (se 1 (by rfl) ⟨4261085, by rfl⟩ : syracuseStep 5681447 = 8522171) B8522171
theorem B29160233 : Blo 1682041 29160233 := bstep (se 2 (by rfl) ⟨10935087, by rfl⟩ : syracuseStep 29160233 = 21870175) B21870175
theorem B5117863 : Blo 1682041 5117863 := bstep (se 1 (by rfl) ⟨3838397, by rfl⟩ : syracuseStep 5117863 = 7676795) B7676795
theorem B4792765 : Blo 1682041 4792765 := bstep (se 3 (by rfl) ⟨898643, by rfl⟩ : syracuseStep 4792765 = 1797287) B1797287
theorem B2523647 : Blo 1682041 2523647 := bstep (se 1 (by rfl) ⟨1892735, by rfl⟩ : syracuseStep 2523647 = 3785471) B3785471
theorem B19440155 : Blo 1682041 19440155 := bstep (se 1 (by rfl) ⟨14580116, by rfl⟩ : syracuseStep 19440155 = 29160233) B29160233
theorem B9093991 : Blo 1682041 9093991 := bstep (se 1 (by rfl) ⟨6820493, by rfl⟩ : syracuseStep 9093991 = 13640987) B13640987
theorem B2524007 : Blo 1682041 2524007 := bstep (se 1 (by rfl) ⟨1893005, by rfl⟩ : syracuseStep 2524007 = 3786011) B3786011
theorem B2524073 : Blo 1682041 2524073 := bstep (se 2 (by rfl) ⟨946527, by rfl⟩ : syracuseStep 2524073 = 1893055) B1893055
theorem B9585803 : Blo 1682041 9585803 := bstep (se 1 (by rfl) ⟨7189352, by rfl⟩ : syracuseStep 9585803 = 14378705) B14378705
theorem B2524607 : Blo 1682041 2524607 := bstep (se 1 (by rfl) ⟨1893455, by rfl⟩ : syracuseStep 2524607 = 3786911) B3786911
theorem B3787631 : Blo 1682041 3787631 := bstep (se 1 (by rfl) ⟨2840723, by rfl⟩ : syracuseStep 3787631 = 5681447) B5681447
theorem B1682559 : Blo 1682041 1682559 := bstep (se 1 (by rfl) ⟨1261919, by rfl⟩ : syracuseStep 1682559 = 2523839) B2523839
theorem B1682791 : Blo 1682041 1682791 := bstep (se 1 (by rfl) ⟨1262093, by rfl⟩ : syracuseStep 1682791 = 2524187) B2524187
theorem B1683943 : Blo 1682041 1683943 := bstep (se 1 (by rfl) ⟨1262957, by rfl⟩ : syracuseStep 1683943 = 2525915) B2525915
theorem B14971567 : Blo 1682041 14971567 := bstep (se 1 (by rfl) ⟨11228675, by rfl⟩ : syracuseStep 14971567 = 22457351) B22457351
theorem B36410633 : Blo 1682041 36410633 := bstep (se 2 (by rfl) ⟨13653987, by rfl⟩ : syracuseStep 36410633 = 27307975) B27307975
theorem B2840575 : Blo 1682041 2840575 := bstep (se 1 (by rfl) ⟨2130431, by rfl⟩ : syracuseStep 2840575 = 4260863) B4260863
theorem B9100457 : Blo 1682041 9100457 := bstep (se 2 (by rfl) ⟨3412671, by rfl⟩ : syracuseStep 9100457 = 6825343) B6825343
theorem B43736705 : Blo 1682041 43736705 := bstep (se 2 (by rfl) ⟨16401264, by rfl⟩ : syracuseStep 43736705 = 32802529) B32802529
theorem B6823817 : Blo 1682041 6823817 := bstep (se 2 (by rfl) ⟨2558931, by rfl⟩ : syracuseStep 6823817 = 5117863) B5117863
theorem B12960103 : Blo 1682041 12960103 := bstep (se 1 (by rfl) ⟨9720077, by rfl⟩ : syracuseStep 12960103 = 19440155) B19440155
theorem B6390353 : Blo 1682041 6390353 := bstep (se 2 (by rfl) ⟨2396382, by rfl⟩ : syracuseStep 6390353 = 4792765) B4792765
theorem B6390535 : Blo 1682041 6390535 := bstep (se 1 (by rfl) ⟨4792901, by rfl⟩ : syracuseStep 6390535 = 9585803) B9585803
theorem B24273755 : Blo 1682041 24273755 := bstep (se 1 (by rfl) ⟨18205316, by rfl⟩ : syracuseStep 24273755 = 36410633) B36410633
theorem B12125321 : Blo 1682041 12125321 := bstep (se 2 (by rfl) ⟨4546995, by rfl⟩ : syracuseStep 12125321 = 9093991) B9093991
theorem B2525087 : Blo 1682041 2525087 := bstep (se 1 (by rfl) ⟨1893815, by rfl⟩ : syracuseStep 2525087 = 3787631) B3787631
theorem B29157803 : Blo 1682041 29157803 := bstep (se 1 (by rfl) ⟨21868352, by rfl⟩ : syracuseStep 29157803 = 43736705) B43736705
theorem B4549211 : Blo 1682041 4549211 := bstep (se 1 (by rfl) ⟨3411908, by rfl⟩ : syracuseStep 4549211 = 6823817) B6823817
theorem B3787433 : Blo 1682041 3787433 := bstep (se 2 (by rfl) ⟨1420287, by rfl⟩ : syracuseStep 3787433 = 2840575) B2840575
theorem B1682431 : Blo 1682041 1682431 := bstep (se 1 (by rfl) ⟨1261823, by rfl⟩ : syracuseStep 1682431 = 2523647) B2523647
theorem B1682671 : Blo 1682041 1682671 := bstep (se 1 (by rfl) ⟨1262003, by rfl⟩ : syracuseStep 1682671 = 2524007) B2524007
theorem B1682715 : Blo 1682041 1682715 := bstep (se 1 (by rfl) ⟨1262036, by rfl⟩ : syracuseStep 1682715 = 2524073) B2524073
theorem B1683071 : Blo 1682041 1683071 := bstep (se 1 (by rfl) ⟨1262303, by rfl⟩ : syracuseStep 1683071 = 2524607) B2524607
theorem B6066971 : Blo 1682041 6066971 := bstep (se 1 (by rfl) ⟨4550228, by rfl⟩ : syracuseStep 6066971 = 9100457) B9100457
theorem B19962089 : Blo 1682041 19962089 := bstep (se 2 (by rfl) ⟨7485783, by rfl⟩ : syracuseStep 19962089 = 14971567) B14971567
theorem B4260235 : Blo 1682041 4260235 := bstep (se 1 (by rfl) ⟨3195176, by rfl⟩ : syracuseStep 4260235 = 6390353) B6390353
theorem B8520713 : Blo 1682041 8520713 := bstep (se 2 (by rfl) ⟨3195267, by rfl⟩ : syracuseStep 8520713 = 6390535) B6390535
theorem B3032807 : Blo 1682041 3032807 := bstep (se 1 (by rfl) ⟨2274605, by rfl⟩ : syracuseStep 3032807 = 4549211) B4549211
theorem B2524955 : Blo 1682041 2524955 := bstep (se 1 (by rfl) ⟨1893716, by rfl⟩ : syracuseStep 2524955 = 3787433) B3787433
theorem B17280137 : Blo 1682041 17280137 := bstep (se 2 (by rfl) ⟨6480051, by rfl⟩ : syracuseStep 17280137 = 12960103) B12960103
theorem B16182503 : Blo 1682041 16182503 := bstep (se 1 (by rfl) ⟨12136877, by rfl⟩ : syracuseStep 16182503 = 24273755) B24273755
theorem B1683391 : Blo 1682041 1683391 := bstep (se 1 (by rfl) ⟨1262543, by rfl⟩ : syracuseStep 1683391 = 2525087) B2525087
theorem B13308059 : Blo 1682041 13308059 := bstep (se 1 (by rfl) ⟨9981044, by rfl⟩ : syracuseStep 13308059 = 19962089) B19962089
theorem B4044647 : Blo 1682041 4044647 := bstep (se 1 (by rfl) ⟨3033485, by rfl⟩ : syracuseStep 4044647 = 6066971) B6066971
theorem B8083547 : Blo 1682041 8083547 := bstep (se 1 (by rfl) ⟨6062660, by rfl⟩ : syracuseStep 8083547 = 12125321) B12125321
theorem B19438535 : Blo 1682041 19438535 := bstep (se 1 (by rfl) ⟨14578901, by rfl⟩ : syracuseStep 19438535 = 29157803) B29157803
theorem B8872039 : Blo 1682041 8872039 := bstep (se 1 (by rfl) ⟨6654029, by rfl⟩ : syracuseStep 8872039 = 13308059) B13308059
theorem B2696431 : Blo 1682041 2696431 := bstep (se 1 (by rfl) ⟨2022323, by rfl⟩ : syracuseStep 2696431 = 4044647) B4044647
theorem B8087485 : Blo 1682041 8087485 := bstep (se 3 (by rfl) ⟨1516403, by rfl⟩ : syracuseStep 8087485 = 3032807) B3032807
theorem B11520091 : Blo 1682041 11520091 := bstep (se 1 (by rfl) ⟨8640068, by rfl⟩ : syracuseStep 11520091 = 17280137) B17280137
theorem B5680313 : Blo 1682041 5680313 := bstep (se 2 (by rfl) ⟨2130117, by rfl⟩ : syracuseStep 5680313 = 4260235) B4260235
theorem B5680475 : Blo 1682041 5680475 := bstep (se 1 (by rfl) ⟨4260356, by rfl⟩ : syracuseStep 5680475 = 8520713) B8520713
theorem B1683303 : Blo 1682041 1683303 := bstep (se 1 (by rfl) ⟨1262477, by rfl⟩ : syracuseStep 1683303 = 2524955) B2524955
theorem B5389031 : Blo 1682041 5389031 := bstep (se 1 (by rfl) ⟨4041773, by rfl⟩ : syracuseStep 5389031 = 8083547) B8083547
theorem B12959023 : Blo 1682041 12959023 := bstep (se 1 (by rfl) ⟨9719267, by rfl⟩ : syracuseStep 12959023 = 19438535) B19438535
theorem B10788335 : Blo 1682041 10788335 := bstep (se 1 (by rfl) ⟨8091251, by rfl⟩ : syracuseStep 10788335 = 16182503) B16182503
theorem B15360121 : Blo 1682041 15360121 := bstep (se 2 (by rfl) ⟨5760045, by rfl⟩ : syracuseStep 15360121 = 11520091) B11520091
theorem B11829385 : Blo 1682041 11829385 := bstep (se 2 (by rfl) ⟨4436019, by rfl⟩ : syracuseStep 11829385 = 8872039) B8872039
theorem B17278697 : Blo 1682041 17278697 := bstep (se 2 (by rfl) ⟨6479511, by rfl⟩ : syracuseStep 17278697 = 12959023) B12959023
theorem B3786875 : Blo 1682041 3786875 := bstep (se 1 (by rfl) ⟨2840156, by rfl⟩ : syracuseStep 3786875 = 5680313) B5680313
theorem B3786983 : Blo 1682041 3786983 := bstep (se 1 (by rfl) ⟨2840237, by rfl⟩ : syracuseStep 3786983 = 5680475) B5680475
theorem B10783313 : Blo 1682041 10783313 := bstep (se 2 (by rfl) ⟨4043742, by rfl⟩ : syracuseStep 10783313 = 8087485) B8087485
theorem B3592687 : Blo 1682041 3592687 := bstep (se 1 (by rfl) ⟨2694515, by rfl⟩ : syracuseStep 3592687 = 5389031) B5389031
theorem B3595241 : Blo 1682041 3595241 := bstep (se 2 (by rfl) ⟨1348215, by rfl⟩ : syracuseStep 3595241 = 2696431) B2696431
theorem B7192223 : Blo 1682041 7192223 := bstep (se 1 (by rfl) ⟨5394167, by rfl⟩ : syracuseStep 7192223 = 10788335) B10788335
theorem B81920645 : Blo 1682041 81920645 := bstep (se 4 (by rfl) ⟨7680060, by rfl⟩ : syracuseStep 81920645 = 15360121) B15360121
theorem B11519131 : Blo 1682041 11519131 := bstep (se 1 (by rfl) ⟨8639348, by rfl⟩ : syracuseStep 11519131 = 17278697) B17278697
theorem B2524583 : Blo 1682041 2524583 := bstep (se 1 (by rfl) ⟨1893437, by rfl⟩ : syracuseStep 2524583 = 3786875) B3786875
theorem B2524655 : Blo 1682041 2524655 := bstep (se 1 (by rfl) ⟨1893491, by rfl⟩ : syracuseStep 2524655 = 3786983) B3786983
theorem B4794815 : Blo 1682041 4794815 := bstep (se 1 (by rfl) ⟨3596111, by rfl⟩ : syracuseStep 4794815 = 7192223) B7192223
theorem B63090053 : Blo 1682041 63090053 := bstep (se 4 (by rfl) ⟨5914692, by rfl⟩ : syracuseStep 63090053 = 11829385) B11829385
theorem B7188875 : Blo 1682041 7188875 := bstep (se 1 (by rfl) ⟨5391656, by rfl⟩ : syracuseStep 7188875 = 10783313) B10783313
theorem B2396827 : Blo 1682041 2396827 := bstep (se 1 (by rfl) ⟨1797620, by rfl⟩ : syracuseStep 2396827 = 3595241) B3595241
theorem B4790249 : Blo 1682041 4790249 := bstep (se 2 (by rfl) ⟨1796343, by rfl⟩ : syracuseStep 4790249 = 3592687) B3592687
theorem B4792583 : Blo 1682041 4792583 := bstep (se 1 (by rfl) ⟨3594437, by rfl⟩ : syracuseStep 4792583 = 7188875) B7188875
theorem B3195769 : Blo 1682041 3195769 := bstep (se 2 (by rfl) ⟨1198413, by rfl⟩ : syracuseStep 3195769 = 2396827) B2396827
theorem B42060035 : Blo 1682041 42060035 := bstep (se 1 (by rfl) ⟨31545026, by rfl⟩ : syracuseStep 42060035 = 63090053) B63090053
theorem B1683055 : Blo 1682041 1683055 := bstep (se 1 (by rfl) ⟨1262291, by rfl⟩ : syracuseStep 1683055 = 2524583) B2524583
theorem B1683103 : Blo 1682041 1683103 := bstep (se 1 (by rfl) ⟨1262327, by rfl⟩ : syracuseStep 1683103 = 2524655) B2524655
theorem B54613763 : Blo 1682041 54613763 := bstep (se 1 (by rfl) ⟨40960322, by rfl⟩ : syracuseStep 54613763 = 81920645) B81920645
theorem B12786173 : Blo 1682041 12786173 := bstep (se 3 (by rfl) ⟨2397407, by rfl⟩ : syracuseStep 12786173 = 4794815) B4794815
theorem B3193499 : Blo 1682041 3193499 := bstep (se 1 (by rfl) ⟨2395124, by rfl⟩ : syracuseStep 3193499 = 4790249) B4790249
theorem B15358841 : Blo 1682041 15358841 := bstep (se 2 (by rfl) ⟨5759565, by rfl⟩ : syracuseStep 15358841 = 11519131) B11519131
theorem B3195055 : Blo 1682041 3195055 := bstep (se 1 (by rfl) ⟨2396291, by rfl⟩ : syracuseStep 3195055 = 4792583) B4792583
theorem B4261025 : Blo 1682041 4261025 := bstep (se 2 (by rfl) ⟨1597884, by rfl⟩ : syracuseStep 4261025 = 3195769) B3195769
theorem B36409175 : Blo 1682041 36409175 := bstep (se 1 (by rfl) ⟨27306881, by rfl⟩ : syracuseStep 36409175 = 54613763) B54613763
theorem B8524115 : Blo 1682041 8524115 := bstep (se 1 (by rfl) ⟨6393086, by rfl⟩ : syracuseStep 8524115 = 12786173) B12786173
theorem B28040023 : Blo 1682041 28040023 := bstep (se 1 (by rfl) ⟨21030017, by rfl⟩ : syracuseStep 28040023 = 42060035) B42060035
theorem B2128999 : Blo 1682041 2128999 := bstep (se 1 (by rfl) ⟨1596749, by rfl⟩ : syracuseStep 2128999 = 3193499) B3193499
theorem B10239227 : Blo 1682041 10239227 := bstep (se 1 (by rfl) ⟨7679420, by rfl⟩ : syracuseStep 10239227 = 15358841) B15358841
theorem B4260073 : Blo 1682041 4260073 := bstep (se 2 (by rfl) ⟨1597527, by rfl⟩ : syracuseStep 4260073 = 3195055) B3195055
theorem B6826151 : Blo 1682041 6826151 := bstep (se 1 (by rfl) ⟨5119613, by rfl⟩ : syracuseStep 6826151 = 10239227) B10239227
theorem B2838665 : Blo 1682041 2838665 := bstep (se 2 (by rfl) ⟨1064499, by rfl⟩ : syracuseStep 2838665 = 2128999) B2128999
theorem B5682743 : Blo 1682041 5682743 := bstep (se 1 (by rfl) ⟨4262057, by rfl⟩ : syracuseStep 5682743 = 8524115) B8524115
theorem B2840683 : Blo 1682041 2840683 := bstep (se 1 (by rfl) ⟨2130512, by rfl⟩ : syracuseStep 2840683 = 4261025) B4261025
theorem B37386697 : Blo 1682041 37386697 := bstep (se 2 (by rfl) ⟨14020011, by rfl⟩ : syracuseStep 37386697 = 28040023) B28040023
theorem B24272783 : Blo 1682041 24272783 := bstep (se 1 (by rfl) ⟨18204587, by rfl⟩ : syracuseStep 24272783 = 36409175) B36409175
theorem B1892443 : Blo 1682041 1892443 := bstep (se 1 (by rfl) ⟨1419332, by rfl⟩ : syracuseStep 1892443 = 2838665) B2838665
theorem B18203069 : Blo 1682041 18203069 := bstep (se 3 (by rfl) ⟨3413075, by rfl⟩ : syracuseStep 18203069 = 6826151) B6826151
theorem B49848929 : Blo 1682041 49848929 := bstep (se 2 (by rfl) ⟨18693348, by rfl⟩ : syracuseStep 49848929 = 37386697) B37386697
theorem B16181855 : Blo 1682041 16181855 := bstep (se 1 (by rfl) ⟨12136391, by rfl⟩ : syracuseStep 16181855 = 24272783) B24272783
theorem B3787577 : Blo 1682041 3787577 := bstep (se 2 (by rfl) ⟨1420341, by rfl⟩ : syracuseStep 3787577 = 2840683) B2840683
theorem B5680097 : Blo 1682041 5680097 := bstep (se 2 (by rfl) ⟨2130036, by rfl⟩ : syracuseStep 5680097 = 4260073) B4260073
theorem B3788495 : Blo 1682041 3788495 := bstep (se 1 (by rfl) ⟨2841371, by rfl⟩ : syracuseStep 3788495 = 5682743) B5682743
theorem B2523257 : Blo 1682041 2523257 := bstep (se 2 (by rfl) ⟨946221, by rfl⟩ : syracuseStep 2523257 = 1892443) B1892443
theorem B2525051 : Blo 1682041 2525051 := bstep (se 1 (by rfl) ⟨1893788, by rfl⟩ : syracuseStep 2525051 = 3787577) B3787577
theorem B3786731 : Blo 1682041 3786731 := bstep (se 1 (by rfl) ⟨2840048, by rfl⟩ : syracuseStep 3786731 = 5680097) B5680097
theorem B2525663 : Blo 1682041 2525663 := bstep (se 1 (by rfl) ⟨1894247, by rfl⟩ : syracuseStep 2525663 = 3788495) B3788495
theorem B12135379 : Blo 1682041 12135379 := bstep (se 1 (by rfl) ⟨9101534, by rfl⟩ : syracuseStep 12135379 = 18203069) B18203069
theorem B33232619 : Blo 1682041 33232619 := bstep (se 1 (by rfl) ⟨24924464, by rfl⟩ : syracuseStep 33232619 = 49848929) B49848929
theorem B10787903 : Blo 1682041 10787903 := bstep (se 1 (by rfl) ⟨8090927, by rfl⟩ : syracuseStep 10787903 = 16181855) B16181855
theorem B16180505 : Blo 1682041 16180505 := bstep (se 2 (by rfl) ⟨6067689, by rfl⟩ : syracuseStep 16180505 = 12135379) B12135379
theorem B2524487 : Blo 1682041 2524487 := bstep (se 1 (by rfl) ⟨1893365, by rfl⟩ : syracuseStep 2524487 = 3786731) B3786731
theorem B1682171 : Blo 1682041 1682171 := bstep (se 1 (by rfl) ⟨1261628, by rfl⟩ : syracuseStep 1682171 = 2523257) B2523257
theorem B1683367 : Blo 1682041 1683367 := bstep (se 1 (by rfl) ⟨1262525, by rfl⟩ : syracuseStep 1683367 = 2525051) B2525051
theorem B1683775 : Blo 1682041 1683775 := bstep (se 1 (by rfl) ⟨1262831, by rfl⟩ : syracuseStep 1683775 = 2525663) B2525663
theorem B88620317 : Blo 1682041 88620317 := bstep (se 3 (by rfl) ⟨16616309, by rfl⟩ : syracuseStep 88620317 = 33232619) B33232619
theorem B7191935 : Blo 1682041 7191935 := bstep (se 1 (by rfl) ⟨5393951, by rfl⟩ : syracuseStep 7191935 = 10787903) B10787903
theorem B4794623 : Blo 1682041 4794623 := bstep (se 1 (by rfl) ⟨3595967, by rfl⟩ : syracuseStep 4794623 = 7191935) B7191935
theorem B1682991 : Blo 1682041 1682991 := bstep (se 1 (by rfl) ⟨1262243, by rfl⟩ : syracuseStep 1682991 = 2524487) B2524487
theorem B10787003 : Blo 1682041 10787003 := bstep (se 1 (by rfl) ⟨8090252, by rfl⟩ : syracuseStep 10787003 = 16180505) B16180505
theorem B59080211 : Blo 1682041 59080211 := bstep (se 1 (by rfl) ⟨44310158, by rfl⟩ : syracuseStep 59080211 = 88620317) B88620317
theorem B3196415 : Blo 1682041 3196415 := bstep (se 1 (by rfl) ⟨2397311, by rfl⟩ : syracuseStep 3196415 = 4794623) B4794623
theorem B7191335 : Blo 1682041 7191335 := bstep (se 1 (by rfl) ⟨5393501, by rfl⟩ : syracuseStep 7191335 = 10787003) B10787003
theorem B39386807 : Blo 1682041 39386807 := bstep (se 1 (by rfl) ⟨29540105, by rfl⟩ : syracuseStep 39386807 = 59080211) B59080211
theorem B2130943 : Blo 1682041 2130943 := bstep (se 1 (by rfl) ⟨1598207, by rfl⟩ : syracuseStep 2130943 = 3196415) B3196415
theorem B4794223 : Blo 1682041 4794223 := bstep (se 1 (by rfl) ⟨3595667, by rfl⟩ : syracuseStep 4794223 = 7191335) B7191335
theorem B26257871 : Blo 1682041 26257871 := bstep (se 1 (by rfl) ⟨19693403, by rfl⟩ : syracuseStep 26257871 = 39386807) B39386807
theorem B6392297 : Blo 1682041 6392297 := bstep (se 2 (by rfl) ⟨2397111, by rfl⟩ : syracuseStep 6392297 = 4794223) B4794223
theorem B2841257 : Blo 1682041 2841257 := bstep (se 2 (by rfl) ⟨1065471, by rfl⟩ : syracuseStep 2841257 = 2130943) B2130943
theorem B17505247 : Blo 1682041 17505247 := bstep (se 1 (by rfl) ⟨13128935, by rfl⟩ : syracuseStep 17505247 = 26257871) B26257871
theorem B23340329 : Blo 1682041 23340329 := bstep (se 2 (by rfl) ⟨8752623, by rfl⟩ : syracuseStep 23340329 = 17505247) B17505247
theorem B4261531 : Blo 1682041 4261531 := bstep (se 1 (by rfl) ⟨3196148, by rfl⟩ : syracuseStep 4261531 = 6392297) B6392297
theorem B1894171 : Blo 1682041 1894171 := bstep (se 1 (by rfl) ⟨1420628, by rfl⟩ : syracuseStep 1894171 = 2841257) B2841257
theorem B2525561 : Blo 1682041 2525561 := bstep (se 2 (by rfl) ⟨947085, by rfl⟩ : syracuseStep 2525561 = 1894171) B1894171
theorem B15560219 : Blo 1682041 15560219 := bstep (se 1 (by rfl) ⟨11670164, by rfl⟩ : syracuseStep 15560219 = 23340329) B23340329
theorem B5682041 : Blo 1682041 5682041 := bstep (se 2 (by rfl) ⟨2130765, by rfl⟩ : syracuseStep 5682041 = 4261531) B4261531
theorem B41493917 : Blo 1682041 41493917 := bstep (se 3 (by rfl) ⟨7780109, by rfl⟩ : syracuseStep 41493917 = 15560219) B15560219
theorem B3788027 : Blo 1682041 3788027 := bstep (se 1 (by rfl) ⟨2841020, by rfl⟩ : syracuseStep 3788027 = 5682041) B5682041
theorem B1683707 : Blo 1682041 1683707 := bstep (se 1 (by rfl) ⟨1262780, by rfl⟩ : syracuseStep 1683707 = 2525561) B2525561
theorem B110650445 : Blo 1682041 110650445 := bstep (se 3 (by rfl) ⟨20746958, by rfl⟩ : syracuseStep 110650445 = 41493917) B41493917
theorem B2525351 : Blo 1682041 2525351 := bstep (se 1 (by rfl) ⟨1894013, by rfl⟩ : syracuseStep 2525351 = 3788027) B3788027
theorem B1683567 : Blo 1682041 1683567 := bstep (se 1 (by rfl) ⟨1262675, by rfl⟩ : syracuseStep 1683567 = 2525351) B2525351
theorem B73766963 : Blo 1682041 73766963 := bstep (se 1 (by rfl) ⟨55325222, by rfl⟩ : syracuseStep 73766963 = 110650445) B110650445
theorem B196711901 : Blo 1682041 196711901 := bstep (se 3 (by rfl) ⟨36883481, by rfl⟩ : syracuseStep 196711901 = 73766963) B73766963
theorem B131141267 : Blo 1682041 131141267 := bstep (se 1 (by rfl) ⟨98355950, by rfl⟩ : syracuseStep 131141267 = 196711901) B196711901
theorem B87427511 : Blo 1682041 87427511 := bstep (se 1 (by rfl) ⟨65570633, by rfl⟩ : syracuseStep 87427511 = 131141267) B131141267
theorem B58285007 : Blo 1682041 58285007 := bstep (se 1 (by rfl) ⟨43713755, by rfl⟩ : syracuseStep 58285007 = 87427511) B87427511
theorem B38856671 : Blo 1682041 38856671 := bstep (se 1 (by rfl) ⟨29142503, by rfl⟩ : syracuseStep 38856671 = 58285007) B58285007
theorem B25904447 : Blo 1682041 25904447 := bstep (se 1 (by rfl) ⟨19428335, by rfl⟩ : syracuseStep 25904447 = 38856671) B38856671
theorem B17269631 : Blo 1682041 17269631 := bstep (se 1 (by rfl) ⟨12952223, by rfl⟩ : syracuseStep 17269631 = 25904447) B25904447
theorem B11513087 : Blo 1682041 11513087 := bstep (se 1 (by rfl) ⟨8634815, by rfl⟩ : syracuseStep 11513087 = 17269631) B17269631
theorem B7675391 : Blo 1682041 7675391 := bstep (se 1 (by rfl) ⟨5756543, by rfl⟩ : syracuseStep 7675391 = 11513087) B11513087
theorem B5116927 : Blo 1682041 5116927 := bstep (se 1 (by rfl) ⟨3837695, by rfl⟩ : syracuseStep 5116927 = 7675391) B7675391
theorem B6822569 : Blo 1682041 6822569 := bstep (se 2 (by rfl) ⟨2558463, by rfl⟩ : syracuseStep 6822569 = 5116927) B5116927
theorem B18193517 : Blo 1682041 18193517 := bstep (se 3 (by rfl) ⟨3411284, by rfl⟩ : syracuseStep 18193517 = 6822569) B6822569
theorem B12129011 : Blo 1682041 12129011 := bstep (se 1 (by rfl) ⟨9096758, by rfl⟩ : syracuseStep 12129011 = 18193517) B18193517
theorem B8086007 : Blo 1682041 8086007 := bstep (se 1 (by rfl) ⟨6064505, by rfl⟩ : syracuseStep 8086007 = 12129011) B12129011
theorem B5390671 : Blo 1682041 5390671 := bstep (se 1 (by rfl) ⟨4043003, by rfl⟩ : syracuseStep 5390671 = 8086007) B8086007
theorem B7187561 : Blo 1682041 7187561 := bstep (se 2 (by rfl) ⟨2695335, by rfl⟩ : syracuseStep 7187561 = 5390671) B5390671
theorem B4791707 : Blo 1682041 4791707 := bstep (se 1 (by rfl) ⟨3593780, by rfl⟩ : syracuseStep 4791707 = 7187561) B7187561
theorem B3194471 : Blo 1682041 3194471 := bstep (se 1 (by rfl) ⟨2395853, by rfl⟩ : syracuseStep 3194471 = 4791707) B4791707
theorem B2129647 : Blo 1682041 2129647 := bstep (se 1 (by rfl) ⟨1597235, by rfl⟩ : syracuseStep 2129647 = 3194471) B3194471
theorem B2839529 : Blo 1682041 2839529 := bstep (se 2 (by rfl) ⟨1064823, by rfl⟩ : syracuseStep 2839529 = 2129647) B2129647
theorem B1893019 : Blo 1682041 1893019 := bstep (se 1 (by rfl) ⟨1419764, by rfl⟩ : syracuseStep 1893019 = 2839529) B2839529
theorem B2524025 : Blo 1682041 2524025 := bstep (se 2 (by rfl) ⟨946509, by rfl⟩ : syracuseStep 2524025 = 1893019) B1893019
theorem B1682683 : Blo 1682041 1682683 := bstep (se 1 (by rfl) ⟨1262012, by rfl⟩ : syracuseStep 1682683 = 2524025) B2524025

theorem C0 (j : ℕ) (h1 : 420510 ≤ j) (h2 : j ≤ 421009) : Blo 1682041 (4 * j + 3) := by
  interval_cases j
  · exact B1682043
  · exact B1682047
  · exact B1682051
  · exact B1682055
  · exact B1682059
  · exact B1682063
  · exact B1682067
  · exact B1682071
  · exact B1682075
  · exact B1682079
  · exact B1682083
  · exact B1682087
  · exact B1682091
  · exact B1682095
  · exact B1682099
  · exact B1682103
  · exact B1682107
  · exact B1682111
  · exact B1682115
  · exact B1682119
  · exact B1682123
  · exact B1682127
  · exact B1682131
  · exact B1682135
  · exact B1682139
  · exact B1682143
  · exact B1682147
  · exact B1682151
  · exact B1682155
  · exact B1682159
  · exact B1682163
  · exact B1682167
  · exact B1682171
  · exact B1682175
  · exact B1682179
  · exact B1682183
  · exact B1682187
  · exact B1682191
  · exact B1682195
  · exact B1682199
  · exact B1682203
  · exact B1682207
  · exact B1682211
  · exact B1682215
  · exact B1682219
  · exact B1682223
  · exact B1682227
  · exact B1682231
  · exact B1682235
  · exact B1682239
  · exact B1682243
  · exact B1682247
  · exact B1682251
  · exact B1682255
  · exact B1682259
  · exact B1682263
  · exact B1682267
  · exact B1682271
  · exact B1682275
  · exact B1682279
  · exact B1682283
  · exact B1682287
  · exact B1682291
  · exact B1682295
  · exact B1682299
  · exact B1682303
  · exact B1682307
  · exact B1682311
  · exact B1682315
  · exact B1682319
  · exact B1682323
  · exact B1682327
  · exact B1682331
  · exact B1682335
  · exact B1682339
  · exact B1682343
  · exact B1682347
  · exact B1682351
  · exact B1682355
  · exact B1682359
  · exact B1682363
  · exact B1682367
  · exact B1682371
  · exact B1682375
  · exact B1682379
  · exact B1682383
  · exact B1682387
  · exact B1682391
  · exact B1682395
  · exact B1682399
  · exact B1682403
  · exact B1682407
  · exact B1682411
  · exact B1682415
  · exact B1682419
  · exact B1682423
  · exact B1682427
  · exact B1682431
  · exact B1682435
  · exact B1682439
  · exact B1682443
  · exact B1682447
  · exact B1682451
  · exact B1682455
  · exact B1682459
  · exact B1682463
  · exact B1682467
  · exact B1682471
  · exact B1682475
  · exact B1682479
  · exact B1682483
  · exact B1682487
  · exact B1682491
  · exact B1682495
  · exact B1682499
  · exact B1682503
  · exact B1682507
  · exact B1682511
  · exact B1682515
  · exact B1682519
  · exact B1682523
  · exact B1682527
  · exact B1682531
  · exact B1682535
  · exact B1682539
  · exact B1682543
  · exact B1682547
  · exact B1682551
  · exact B1682555
  · exact B1682559
  · exact B1682563
  · exact B1682567
  · exact B1682571
  · exact B1682575
  · exact B1682579
  · exact B1682583
  · exact B1682587
  · exact B1682591
  · exact B1682595
  · exact B1682599
  · exact B1682603
  · exact B1682607
  · exact B1682611
  · exact B1682615
  · exact B1682619
  · exact B1682623
  · exact B1682627
  · exact B1682631
  · exact B1682635
  · exact B1682639
  · exact B1682643
  · exact B1682647
  · exact B1682651
  · exact B1682655
  · exact B1682659
  · exact B1682663
  · exact B1682667
  · exact B1682671
  · exact B1682675
  · exact B1682679
  · exact B1682683
  · exact B1682687
  · exact B1682691
  · exact B1682695
  · exact B1682699
  · exact B1682703
  · exact B1682707
  · exact B1682711
  · exact B1682715
  · exact B1682719
  · exact B1682723
  · exact B1682727
  · exact B1682731
  · exact B1682735
  · exact B1682739
  · exact B1682743
  · exact B1682747
  · exact B1682751
  · exact B1682755
  · exact B1682759
  · exact B1682763
  · exact B1682767
  · exact B1682771
  · exact B1682775
  · exact B1682779
  · exact B1682783
  · exact B1682787
  · exact B1682791
  · exact B1682795
  · exact B1682799
  · exact B1682803
  · exact B1682807
  · exact B1682811
  · exact B1682815
  · exact B1682819
  · exact B1682823
  · exact B1682827
  · exact B1682831
  · exact B1682835
  · exact B1682839
  · exact B1682843
  · exact B1682847
  · exact B1682851
  · exact B1682855
  · exact B1682859
  · exact B1682863
  · exact B1682867
  · exact B1682871
  · exact B1682875
  · exact B1682879
  · exact B1682883
  · exact B1682887
  · exact B1682891
  · exact B1682895
  · exact B1682899
  · exact B1682903
  · exact B1682907
  · exact B1682911
  · exact B1682915
  · exact B1682919
  · exact B1682923
  · exact B1682927
  · exact B1682931
  · exact B1682935
  · exact B1682939
  · exact B1682943
  · exact B1682947
  · exact B1682951
  · exact B1682955
  · exact B1682959
  · exact B1682963
  · exact B1682967
  · exact B1682971
  · exact B1682975
  · exact B1682979
  · exact B1682983
  · exact B1682987
  · exact B1682991
  · exact B1682995
  · exact B1682999
  · exact B1683003
  · exact B1683007
  · exact B1683011
  · exact B1683015
  · exact B1683019
  · exact B1683023
  · exact B1683027
  · exact B1683031
  · exact B1683035
  · exact B1683039
  · exact B1683043
  · exact B1683047
  · exact B1683051
  · exact B1683055
  · exact B1683059
  · exact B1683063
  · exact B1683067
  · exact B1683071
  · exact B1683075
  · exact B1683079
  · exact B1683083
  · exact B1683087
  · exact B1683091
  · exact B1683095
  · exact B1683099
  · exact B1683103
  · exact B1683107
  · exact B1683111
  · exact B1683115
  · exact B1683119
  · exact B1683123
  · exact B1683127
  · exact B1683131
  · exact B1683135
  · exact B1683139
  · exact B1683143
  · exact B1683147
  · exact B1683151
  · exact B1683155
  · exact B1683159
  · exact B1683163
  · exact B1683167
  · exact B1683171
  · exact B1683175
  · exact B1683179
  · exact B1683183
  · exact B1683187
  · exact B1683191
  · exact B1683195
  · exact B1683199
  · exact B1683203
  · exact B1683207
  · exact B1683211
  · exact B1683215
  · exact B1683219
  · exact B1683223
  · exact B1683227
  · exact B1683231
  · exact B1683235
  · exact B1683239
  · exact B1683243
  · exact B1683247
  · exact B1683251
  · exact B1683255
  · exact B1683259
  · exact B1683263
  · exact B1683267
  · exact B1683271
  · exact B1683275
  · exact B1683279
  · exact B1683283
  · exact B1683287
  · exact B1683291
  · exact B1683295
  · exact B1683299
  · exact B1683303
  · exact B1683307
  · exact B1683311
  · exact B1683315
  · exact B1683319
  · exact B1683323
  · exact B1683327
  · exact B1683331
  · exact B1683335
  · exact B1683339
  · exact B1683343
  · exact B1683347
  · exact B1683351
  · exact B1683355
  · exact B1683359
  · exact B1683363
  · exact B1683367
  · exact B1683371
  · exact B1683375
  · exact B1683379
  · exact B1683383
  · exact B1683387
  · exact B1683391
  · exact B1683395
  · exact B1683399
  · exact B1683403
  · exact B1683407
  · exact B1683411
  · exact B1683415
  · exact B1683419
  · exact B1683423
  · exact B1683427
  · exact B1683431
  · exact B1683435
  · exact B1683439
  · exact B1683443
  · exact B1683447
  · exact B1683451
  · exact B1683455
  · exact B1683459
  · exact B1683463
  · exact B1683467
  · exact B1683471
  · exact B1683475
  · exact B1683479
  · exact B1683483
  · exact B1683487
  · exact B1683491
  · exact B1683495
  · exact B1683499
  · exact B1683503
  · exact B1683507
  · exact B1683511
  · exact B1683515
  · exact B1683519
  · exact B1683523
  · exact B1683527
  · exact B1683531
  · exact B1683535
  · exact B1683539
  · exact B1683543
  · exact B1683547
  · exact B1683551
  · exact B1683555
  · exact B1683559
  · exact B1683563
  · exact B1683567
  · exact B1683571
  · exact B1683575
  · exact B1683579
  · exact B1683583
  · exact B1683587
  · exact B1683591
  · exact B1683595
  · exact B1683599
  · exact B1683603
  · exact B1683607
  · exact B1683611
  · exact B1683615
  · exact B1683619
  · exact B1683623
  · exact B1683627
  · exact B1683631
  · exact B1683635
  · exact B1683639
  · exact B1683643
  · exact B1683647
  · exact B1683651
  · exact B1683655
  · exact B1683659
  · exact B1683663
  · exact B1683667
  · exact B1683671
  · exact B1683675
  · exact B1683679
  · exact B1683683
  · exact B1683687
  · exact B1683691
  · exact B1683695
  · exact B1683699
  · exact B1683703
  · exact B1683707
  · exact B1683711
  · exact B1683715
  · exact B1683719
  · exact B1683723
  · exact B1683727
  · exact B1683731
  · exact B1683735
  · exact B1683739
  · exact B1683743
  · exact B1683747
  · exact B1683751
  · exact B1683755
  · exact B1683759
  · exact B1683763
  · exact B1683767
  · exact B1683771
  · exact B1683775
  · exact B1683779
  · exact B1683783
  · exact B1683787
  · exact B1683791
  · exact B1683795
  · exact B1683799
  · exact B1683803
  · exact B1683807
  · exact B1683811
  · exact B1683815
  · exact B1683819
  · exact B1683823
  · exact B1683827
  · exact B1683831
  · exact B1683835
  · exact B1683839
  · exact B1683843
  · exact B1683847
  · exact B1683851
  · exact B1683855
  · exact B1683859
  · exact B1683863
  · exact B1683867
  · exact B1683871
  · exact B1683875
  · exact B1683879
  · exact B1683883
  · exact B1683887
  · exact B1683891
  · exact B1683895
  · exact B1683899
  · exact B1683903
  · exact B1683907
  · exact B1683911
  · exact B1683915
  · exact B1683919
  · exact B1683923
  · exact B1683927
  · exact B1683931
  · exact B1683935
  · exact B1683939
  · exact B1683943
  · exact B1683947
  · exact B1683951
  · exact B1683955
  · exact B1683959
  · exact B1683963
  · exact B1683967
  · exact B1683971
  · exact B1683975
  · exact B1683979
  · exact B1683983
  · exact B1683987
  · exact B1683991
  · exact B1683995
  · exact B1683999
  · exact B1684003
  · exact B1684007
  · exact B1684011
  · exact B1684015
  · exact B1684019
  · exact B1684023
  · exact B1684027
  · exact B1684031
  · exact B1684035
  · exact B1684039

theorem solution (m : ℕ) (hlo : 1682041 ≤ m) (hhi : m ≤ 1684041) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 420510 ≤ j := by omega
    have hj2 : j ≤ 421009 := by omega
    have hb : Blo 1682041 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
