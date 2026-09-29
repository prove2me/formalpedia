-- Prove2me | solution 1 for syracuse_descends_range_1859631_1861631
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T01:10:00.392025+00:00
-- url     : https://prove2.me/submissions/42ab30cc-917b-4c7a-a443-2d5eaea9a13f

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


theorem B3579917 : Blo 1859631 3579917 := bbase (se 3 (by rfl) ⟨671234, by rfl⟩ : syracuseStep 3579917 = 1342469) (by norm_num)
theorem B4710413 : Blo 1859631 4710413 := bbase (se 3 (by rfl) ⟨883202, by rfl⟩ : syracuseStep 4710413 = 1766405) (by norm_num)
theorem B7946261 : Blo 1859631 7946261 := bbase (se 6 (by rfl) ⟨186240, by rfl⟩ : syracuseStep 7946261 = 372481) (by norm_num)
theorem B4186133 : Blo 1859631 4186133 := bbase (se 6 (by rfl) ⟨98112, by rfl⟩ : syracuseStep 4186133 = 196225) (by norm_num)
theorem B5300309 : Blo 1859631 5300309 := bbase (se 8 (by rfl) ⟨31056, by rfl⟩ : syracuseStep 5300309 = 62113) (by norm_num)
theorem B4186205 : Blo 1859631 4186205 := bbase (se 3 (by rfl) ⟨784913, by rfl⟩ : syracuseStep 4186205 = 1569827) (by norm_num)
theorem B2121889 : Blo 1859631 2121889 := bbase (se 2 (by rfl) ⟨795708, by rfl⟩ : syracuseStep 2121889 = 1591417) (by norm_num)
theorem B4186277 : Blo 1859631 4186277 := bbase (se 4 (by rfl) ⟨392463, by rfl⟩ : syracuseStep 4186277 = 784927) (by norm_num)
theorem B3973301 : Blo 1859631 3973301 := bbase (se 5 (by rfl) ⟨186248, by rfl⟩ : syracuseStep 3973301 = 372497) (by norm_num)
theorem B7061701 : Blo 1859631 7061701 := bbase (se 4 (by rfl) ⟨662034, by rfl⟩ : syracuseStep 7061701 = 1324069) (by norm_num)
theorem B3530965 : Blo 1859631 3530965 := bbase (se 7 (by rfl) ⟨41378, by rfl⟩ : syracuseStep 3530965 = 82757) (by norm_num)
theorem B26820821 : Blo 1859631 26820821 := bbase (se 7 (by rfl) ⟨314306, by rfl⟩ : syracuseStep 26820821 = 628613) (by norm_num)
theorem B4186349 : Blo 1859631 4186349 := bbase (se 3 (by rfl) ⟨784940, by rfl⟩ : syracuseStep 4186349 = 1569881) (by norm_num)
theorem B8945909 : Blo 1859631 8945909 := bbase (se 5 (by rfl) ⟨419339, by rfl⟩ : syracuseStep 8945909 = 838679) (by norm_num)
theorem B4776221 : Blo 1859631 4776221 := bbase (se 3 (by rfl) ⟨895541, by rfl⟩ : syracuseStep 4776221 = 1791083) (by norm_num)
theorem B7545125 : Blo 1859631 7545125 := bbase (se 4 (by rfl) ⟨707355, by rfl⟩ : syracuseStep 7545125 = 1414711) (by norm_num)
theorem B4186421 : Blo 1859631 4186421 := bbase (se 5 (by rfl) ⟨196238, by rfl⟩ : syracuseStep 4186421 = 392477) (by norm_num)
theorem B9421109 : Blo 1859631 9421109 := bbase (se 5 (by rfl) ⟨441614, by rfl⟩ : syracuseStep 9421109 = 883229) (by norm_num)
theorem B5300549 : Blo 1859631 5300549 := bbase (se 4 (by rfl) ⟨496926, by rfl⟩ : syracuseStep 5300549 = 993853) (by norm_num)
theorem B31777109 : Blo 1859631 31777109 := bbase (se 10 (by rfl) ⟨46548, by rfl⟩ : syracuseStep 31777109 = 93097) (by norm_num)
theorem B3531109 : Blo 1859631 3531109 := bbase (se 4 (by rfl) ⟨331041, by rfl⟩ : syracuseStep 3531109 = 662083) (by norm_num)
theorem B4710757 : Blo 1859631 4710757 := bbase (se 4 (by rfl) ⟨441633, by rfl⟩ : syracuseStep 4710757 = 883267) (by norm_num)
theorem B4186493 : Blo 1859631 4186493 := bbase (se 3 (by rfl) ⟨784967, by rfl⟩ : syracuseStep 4186493 = 1569935) (by norm_num)
theorem B4186565 : Blo 1859631 4186565 := bbase (se 4 (by rfl) ⟨392490, by rfl⟩ : syracuseStep 4186565 = 784981) (by norm_num)
theorem B4710869 : Blo 1859631 4710869 := bbase (se 7 (by rfl) ⟨55205, by rfl⟩ : syracuseStep 4710869 = 110411) (by norm_num)
theorem B7062005 : Blo 1859631 7062005 := bbase (se 5 (by rfl) ⟨331031, by rfl⟩ : syracuseStep 7062005 = 662063) (by norm_num)
theorem B3531269 : Blo 1859631 3531269 := bbase (se 4 (by rfl) ⟨331056, by rfl⟩ : syracuseStep 3531269 = 662113) (by norm_num)
theorem B5300741 : Blo 1859631 5300741 := bbase (se 4 (by rfl) ⟨496944, by rfl⟩ : syracuseStep 5300741 = 993889) (by norm_num)
theorem B4186637 : Blo 1859631 4186637 := bbase (se 3 (by rfl) ⟨784994, by rfl⟩ : syracuseStep 4186637 = 1569989) (by norm_num)
theorem B6365765 : Blo 1859631 6365765 := bbase (se 4 (by rfl) ⟨596790, by rfl⟩ : syracuseStep 6365765 = 1193581) (by norm_num)
theorem B2122309 : Blo 1859631 2122309 := bbase (se 4 (by rfl) ⟨198966, by rfl⟩ : syracuseStep 2122309 = 397933) (by norm_num)
theorem B4186709 : Blo 1859631 4186709 := bbase (se 8 (by rfl) ⟨24531, by rfl⟩ : syracuseStep 4186709 = 49063) (by norm_num)
theorem B3138149 : Blo 1859631 3138149 := bbase (se 4 (by rfl) ⟨294201, by rfl⟩ : syracuseStep 3138149 = 588403) (by norm_num)
theorem B4244069 : Blo 1859631 4244069 := bbase (se 4 (by rfl) ⟨397881, by rfl⟩ : syracuseStep 4244069 = 795763) (by norm_num)
theorem B3531413 : Blo 1859631 3531413 := bbase (se 6 (by rfl) ⟨82767, by rfl⟩ : syracuseStep 3531413 = 165535) (by norm_num)
theorem B4711061 : Blo 1859631 4711061 := bbase (se 6 (by rfl) ⟨110415, by rfl⟩ : syracuseStep 4711061 = 220831) (by norm_num)
theorem B4186781 : Blo 1859631 4186781 := bbase (se 3 (by rfl) ⟨785021, by rfl⟩ : syracuseStep 4186781 = 1570043) (by norm_num)
theorem B3138277 : Blo 1859631 3138277 := bbase (se 4 (by rfl) ⟨294213, by rfl⟩ : syracuseStep 3138277 = 588427) (by norm_num)
theorem B4186853 : Blo 1859631 4186853 := bbase (se 4 (by rfl) ⟨392517, by rfl⟩ : syracuseStep 4186853 = 785035) (by norm_num)
theorem B4186925 : Blo 1859631 4186925 := bbase (se 3 (by rfl) ⟨785048, by rfl⟩ : syracuseStep 4186925 = 1570097) (by norm_num)
theorem B3138365 : Blo 1859631 3138365 := bbase (se 3 (by rfl) ⟨588443, by rfl⟩ : syracuseStep 3138365 = 1176887) (by norm_num)
theorem B2040665 : Blo 1859631 2040665 := bbase (se 2 (by rfl) ⟨765249, by rfl⟩ : syracuseStep 2040665 = 1530499) (by norm_num)
theorem B4186997 : Blo 1859631 4186997 := bbase (se 5 (by rfl) ⟨196265, by rfl⟩ : syracuseStep 4186997 = 392531) (by norm_num)
theorem B3531701 : Blo 1859631 3531701 := bbase (se 5 (by rfl) ⟨165548, by rfl⟩ : syracuseStep 3531701 = 331097) (by norm_num)
theorem B3138493 : Blo 1859631 3138493 := bbase (se 3 (by rfl) ⟨588467, by rfl⟩ : syracuseStep 3138493 = 1176935) (by norm_num)
theorem B4187069 : Blo 1859631 4187069 := bbase (se 3 (by rfl) ⟨785075, by rfl⟩ : syracuseStep 4187069 = 1570151) (by norm_num)
theorem B4711405 : Blo 1859631 4711405 := bbase (se 3 (by rfl) ⟨883388, by rfl⟩ : syracuseStep 4711405 = 1766777) (by norm_num)
theorem B4187141 : Blo 1859631 4187141 := bbase (se 4 (by rfl) ⟨392544, by rfl⟩ : syracuseStep 4187141 = 785089) (by norm_num)
theorem B3138581 : Blo 1859631 3138581 := bbase (se 6 (by rfl) ⟨73560, by rfl⟩ : syracuseStep 3138581 = 147121) (by norm_num)
theorem B3974189 : Blo 1859631 3974189 := bbase (se 3 (by rfl) ⟨745160, by rfl⟩ : syracuseStep 3974189 = 1490321) (by norm_num)
theorem B5030981 : Blo 1859631 5030981 := bbase (se 4 (by rfl) ⟨471654, by rfl⟩ : syracuseStep 5030981 = 943309) (by norm_num)
theorem B3531853 : Blo 1859631 3531853 := bbase (se 3 (by rfl) ⟨662222, by rfl⟩ : syracuseStep 3531853 = 1324445) (by norm_num)
theorem B4187213 : Blo 1859631 4187213 := bbase (se 3 (by rfl) ⟨785102, by rfl⟩ : syracuseStep 4187213 = 1570205) (by norm_num)
theorem B4711517 : Blo 1859631 4711517 := bbase (se 3 (by rfl) ⟨883409, by rfl⟩ : syracuseStep 4711517 = 1766819) (by norm_num)
theorem B3138709 : Blo 1859631 3138709 := bbase (se 6 (by rfl) ⟨73563, by rfl⟩ : syracuseStep 3138709 = 147127) (by norm_num)
theorem B4187285 : Blo 1859631 4187285 := bbase (se 6 (by rfl) ⟨98139, by rfl⟩ : syracuseStep 4187285 = 196279) (by norm_num)
theorem B4187357 : Blo 1859631 4187357 := bbase (se 3 (by rfl) ⟨785129, by rfl⟩ : syracuseStep 4187357 = 1570259) (by norm_num)
theorem B3351781 : Blo 1859631 3351781 := bbase (se 4 (by rfl) ⟨314229, by rfl⟩ : syracuseStep 3351781 = 628459) (by norm_num)
theorem B3138797 : Blo 1859631 3138797 := bbase (se 3 (by rfl) ⟨588524, by rfl⟩ : syracuseStep 3138797 = 1177049) (by norm_num)
theorem B16966901 : Blo 1859631 16966901 := bbase (se 5 (by rfl) ⟨795323, by rfl⟩ : syracuseStep 16966901 = 1590647) (by norm_num)
theorem B3974429 : Blo 1859631 3974429 := bbase (se 3 (by rfl) ⟨745205, by rfl⟩ : syracuseStep 3974429 = 1490411) (by norm_num)
theorem B4711709 : Blo 1859631 4711709 := bbase (se 3 (by rfl) ⟨883445, by rfl⟩ : syracuseStep 4711709 = 1766891) (by norm_num)
theorem B4187429 : Blo 1859631 4187429 := bbase (se 4 (by rfl) ⟨392571, by rfl⟩ : syracuseStep 4187429 = 785143) (by norm_num)
theorem B3138925 : Blo 1859631 3138925 := bbase (se 3 (by rfl) ⟨588548, by rfl⟩ : syracuseStep 3138925 = 1177097) (by norm_num)
theorem B4187501 : Blo 1859631 4187501 := bbase (se 3 (by rfl) ⟨785156, by rfl⟩ : syracuseStep 4187501 = 1570313) (by norm_num)
theorem B3351925 : Blo 1859631 3351925 := bbase (se 5 (by rfl) ⟨157121, by rfl⟩ : syracuseStep 3351925 = 314243) (by norm_num)
theorem B3532157 : Blo 1859631 3532157 := bbase (se 3 (by rfl) ⟨662279, by rfl⟩ : syracuseStep 3532157 = 1324559) (by norm_num)
theorem B4187573 : Blo 1859631 4187573 := bbase (se 5 (by rfl) ⟨196292, by rfl⟩ : syracuseStep 4187573 = 392585) (by norm_num)
theorem B3139013 : Blo 1859631 3139013 := bbase (se 4 (by rfl) ⟨294282, by rfl⟩ : syracuseStep 3139013 = 588565) (by norm_num)
theorem B6276581 : Blo 1859631 6276581 := bbase (se 4 (by rfl) ⟨588429, by rfl⟩ : syracuseStep 6276581 = 1176859) (by norm_num)
theorem B4187645 : Blo 1859631 4187645 := bbase (se 3 (by rfl) ⟨785183, by rfl⟩ : syracuseStep 4187645 = 1570367) (by norm_num)
theorem B8488469 : Blo 1859631 8488469 := bbase (se 6 (by rfl) ⟨198948, by rfl⟩ : syracuseStep 8488469 = 397897) (by norm_num)
theorem B3139141 : Blo 1859631 3139141 := bbase (se 4 (by rfl) ⟨294294, by rfl⟩ : syracuseStep 3139141 = 588589) (by norm_num)
theorem B4187717 : Blo 1859631 4187717 := bbase (se 4 (by rfl) ⟨392598, by rfl⟩ : syracuseStep 4187717 = 785197) (by norm_num)
theorem B9422405 : Blo 1859631 9422405 := bbase (se 4 (by rfl) ⟨883350, by rfl⟩ : syracuseStep 9422405 = 1766701) (by norm_num)
theorem B4712053 : Blo 1859631 4712053 := bbase (se 5 (by rfl) ⟨220877, by rfl⟩ : syracuseStep 4712053 = 441755) (by norm_num)
theorem B4187789 : Blo 1859631 4187789 := bbase (se 3 (by rfl) ⟨785210, by rfl⟩ : syracuseStep 4187789 = 1570421) (by norm_num)
theorem B21186197 : Blo 1859631 21186197 := bbase (se 6 (by rfl) ⟨496551, by rfl⟩ : syracuseStep 21186197 = 993103) (by norm_num)
theorem B3139229 : Blo 1859631 3139229 := bbase (se 3 (by rfl) ⟨588605, by rfl⟩ : syracuseStep 3139229 = 1177211) (by norm_num)
theorem B8488613 : Blo 1859631 8488613 := bbase (se 4 (by rfl) ⟨795807, by rfl⟩ : syracuseStep 8488613 = 1591615) (by norm_num)
theorem B2827981 : Blo 1859631 2827981 := bbase (se 3 (by rfl) ⟨530246, by rfl⟩ : syracuseStep 2827981 = 1060493) (by norm_num)
theorem B4187861 : Blo 1859631 4187861 := bbase (se 7 (by rfl) ⟨49076, by rfl⟩ : syracuseStep 4187861 = 98153) (by norm_num)
theorem B4712165 : Blo 1859631 4712165 := bbase (se 4 (by rfl) ⟨441765, by rfl⟩ : syracuseStep 4712165 = 883531) (by norm_num)
theorem B7948037 : Blo 1859631 7948037 := bbase (se 4 (by rfl) ⟨745128, by rfl⟩ : syracuseStep 7948037 = 1490257) (by norm_num)
theorem B1885961 : Blo 1859631 1885961 := bbase (se 2 (by rfl) ⟨707235, by rfl⟩ : syracuseStep 1885961 = 1414471) (by norm_num)
theorem B3974933 : Blo 1859631 3974933 := bbase (se 6 (by rfl) ⟨93162, by rfl⟩ : syracuseStep 3974933 = 186325) (by norm_num)
theorem B3139357 : Blo 1859631 3139357 := bbase (se 3 (by rfl) ⟨588629, by rfl⟩ : syracuseStep 3139357 = 1177259) (by norm_num)
theorem B3974941 : Blo 1859631 3974941 := bbase (se 3 (by rfl) ⟨745301, by rfl⟩ : syracuseStep 3974941 = 1490603) (by norm_num)
theorem B4187933 : Blo 1859631 4187933 := bbase (se 3 (by rfl) ⟨785237, by rfl⟩ : syracuseStep 4187933 = 1570475) (by norm_num)
theorem B4188005 : Blo 1859631 4188005 := bbase (se 4 (by rfl) ⟨392625, by rfl⟩ : syracuseStep 4188005 = 785251) (by norm_num)
theorem B3139445 : Blo 1859631 3139445 := bbase (se 5 (by rfl) ⟨147161, by rfl⟩ : syracuseStep 3139445 = 294323) (by norm_num)
theorem B6277013 : Blo 1859631 6277013 := bbase (se 6 (by rfl) ⟨147117, by rfl⟩ : syracuseStep 6277013 = 294235) (by norm_num)
theorem B4188077 : Blo 1859631 4188077 := bbase (se 3 (by rfl) ⟨785264, by rfl⟩ : syracuseStep 4188077 = 1570529) (by norm_num)
theorem B9414629 : Blo 1859631 9414629 := bbase (se 4 (by rfl) ⟨882621, by rfl⟩ : syracuseStep 9414629 = 1765243) (by norm_num)
theorem B5957621 : Blo 1859631 5957621 := bbase (se 5 (by rfl) ⟨279263, by rfl⟩ : syracuseStep 5957621 = 558527) (by norm_num)
theorem B3139573 : Blo 1859631 3139573 := bbase (se 5 (by rfl) ⟨147167, by rfl⟩ : syracuseStep 3139573 = 294335) (by norm_num)
theorem B7948277 : Blo 1859631 7948277 := bbase (se 5 (by rfl) ⟨372575, by rfl⟩ : syracuseStep 7948277 = 745151) (by norm_num)
theorem B4188149 : Blo 1859631 4188149 := bbase (se 5 (by rfl) ⟨196319, by rfl⟩ : syracuseStep 4188149 = 392639) (by norm_num)
theorem B10602485 : Blo 1859631 10602485 := bbase (se 5 (by rfl) ⟨496991, by rfl⟩ : syracuseStep 10602485 = 993983) (by norm_num)
theorem B2828285 : Blo 1859631 2828285 := bbase (se 3 (by rfl) ⟨530303, by rfl⟩ : syracuseStep 2828285 = 1060607) (by norm_num)
theorem B5367845 : Blo 1859631 5367845 := bbase (se 4 (by rfl) ⟨503235, by rfl⟩ : syracuseStep 5367845 = 1006471) (by norm_num)
theorem B4188221 : Blo 1859631 4188221 := bbase (se 3 (by rfl) ⟨785291, by rfl⟩ : syracuseStep 4188221 = 1570583) (by norm_num)
theorem B3139661 : Blo 1859631 3139661 := bbase (se 3 (by rfl) ⟨588686, by rfl⟩ : syracuseStep 3139661 = 1177373) (by norm_num)
theorem B3532909 : Blo 1859631 3532909 := bbase (se 3 (by rfl) ⟨662420, by rfl⟩ : syracuseStep 3532909 = 1324841) (by norm_num)
theorem B10594421 : Blo 1859631 10594421 := bbase (se 5 (by rfl) ⟨496613, by rfl⟩ : syracuseStep 10594421 = 993227) (by norm_num)
theorem B14133365 : Blo 1859631 14133365 := bbase (se 5 (by rfl) ⟨662501, by rfl⟩ : syracuseStep 14133365 = 1325003) (by norm_num)
theorem B4188293 : Blo 1859631 4188293 := bbase (se 4 (by rfl) ⟨392652, by rfl⟩ : syracuseStep 4188293 = 785305) (by norm_num)
theorem B3139789 : Blo 1859631 3139789 := bbase (se 3 (by rfl) ⟨588710, by rfl⟩ : syracuseStep 3139789 = 1177421) (by norm_num)
theorem B4188365 : Blo 1859631 4188365 := bbase (se 3 (by rfl) ⟨785318, by rfl⟩ : syracuseStep 4188365 = 1570637) (by norm_num)
theorem B3533053 : Blo 1859631 3533053 := bbase (se 3 (by rfl) ⟨662447, by rfl⟩ : syracuseStep 3533053 = 1324895) (by norm_num)
theorem B4188437 : Blo 1859631 4188437 := bbase (se 6 (by rfl) ⟨98166, by rfl⟩ : syracuseStep 4188437 = 196333) (by norm_num)
theorem B3139877 : Blo 1859631 3139877 := bbase (se 4 (by rfl) ⟨294363, by rfl⟩ : syracuseStep 3139877 = 588727) (by norm_num)
theorem B6277445 : Blo 1859631 6277445 := bbase (se 4 (by rfl) ⟨588510, by rfl⟩ : syracuseStep 6277445 = 1177021) (by norm_num)
theorem B2648389 : Blo 1859631 2648389 := bbase (se 4 (by rfl) ⟨248286, by rfl⟩ : syracuseStep 2648389 = 496573) (by norm_num)
theorem B4188509 : Blo 1859631 4188509 := bbase (se 3 (by rfl) ⟨785345, by rfl⟩ : syracuseStep 4188509 = 1570691) (by norm_num)
theorem B8939909 : Blo 1859631 8939909 := bbase (se 4 (by rfl) ⟨838116, by rfl⟩ : syracuseStep 8939909 = 1676233) (by norm_num)
theorem B3533213 : Blo 1859631 3533213 := bbase (se 3 (by rfl) ⟨662477, by rfl⟩ : syracuseStep 3533213 = 1324955) (by norm_num)
theorem B3140005 : Blo 1859631 3140005 := bbase (se 4 (by rfl) ⟨294375, by rfl⟩ : syracuseStep 3140005 = 588751) (by norm_num)
theorem B4188581 : Blo 1859631 4188581 := bbase (se 4 (by rfl) ⟨392679, by rfl⟩ : syracuseStep 4188581 = 785359) (by norm_num)
theorem B2353637 : Blo 1859631 2353637 := bbase (se 4 (by rfl) ⟨220653, by rfl⟩ : syracuseStep 2353637 = 441307) (by norm_num)
theorem B4188653 : Blo 1859631 4188653 := bbase (se 3 (by rfl) ⟨785372, by rfl⟩ : syracuseStep 4188653 = 1570745) (by norm_num)
theorem B3140093 : Blo 1859631 3140093 := bbase (se 3 (by rfl) ⟨588767, by rfl⟩ : syracuseStep 3140093 = 1177535) (by norm_num)
theorem B14125589 : Blo 1859631 14125589 := bbase (se 6 (by rfl) ⟨331068, by rfl⟩ : syracuseStep 14125589 = 662137) (by norm_num)
theorem B2353693 : Blo 1859631 2353693 := bbase (se 3 (by rfl) ⟨441317, by rfl⟩ : syracuseStep 2353693 = 882635) (by norm_num)
theorem B3533357 : Blo 1859631 3533357 := bbase (se 3 (by rfl) ⟨662504, by rfl⟩ : syracuseStep 3533357 = 1325009) (by norm_num)
theorem B7064117 : Blo 1859631 7064117 := bbase (se 5 (by rfl) ⟨331130, by rfl⟩ : syracuseStep 7064117 = 662261) (by norm_num)
theorem B3353165 : Blo 1859631 3353165 := bbase (se 3 (by rfl) ⟨628718, by rfl⟩ : syracuseStep 3353165 = 1257437) (by norm_num)
theorem B11922005 : Blo 1859631 11922005 := bbase (se 8 (by rfl) ⟨69855, by rfl⟩ : syracuseStep 11922005 = 139711) (by norm_num)
theorem B15903317 : Blo 1859631 15903317 := bbase (se 8 (by rfl) ⟨93183, by rfl⟩ : syracuseStep 15903317 = 186367) (by norm_num)
theorem B2353789 : Blo 1859631 2353789 := bbase (se 3 (by rfl) ⟨441335, by rfl⟩ : syracuseStep 2353789 = 882671) (by norm_num)
theorem B3140221 : Blo 1859631 3140221 := bbase (se 3 (by rfl) ⟨588791, by rfl⟩ : syracuseStep 3140221 = 1177583) (by norm_num)
theorem B3140309 : Blo 1859631 3140309 := bbase (se 7 (by rfl) ⟨36800, by rfl⟩ : syracuseStep 3140309 = 73601) (by norm_num)
theorem B6277877 : Blo 1859631 6277877 := bbase (se 5 (by rfl) ⟨294275, by rfl⟩ : syracuseStep 6277877 = 588551) (by norm_num)
theorem B2353961 : Blo 1859631 2353961 := bbase (se 2 (by rfl) ⟨882735, by rfl⟩ : syracuseStep 2353961 = 1765471) (by norm_num)
theorem B17886005 : Blo 1859631 17886005 := bbase (se 5 (by rfl) ⟨838406, by rfl⟩ : syracuseStep 17886005 = 1676813) (by norm_num)
theorem B4533053 : Blo 1859631 4533053 := bbase (se 3 (by rfl) ⟨849947, by rfl⟩ : syracuseStep 4533053 = 1699895) (by norm_num)
theorem B3533645 : Blo 1859631 3533645 := bbase (se 3 (by rfl) ⟨662558, by rfl⟩ : syracuseStep 3533645 = 1325117) (by norm_num)
theorem B7064405 : Blo 1859631 7064405 := bbase (se 9 (by rfl) ⟨20696, by rfl⟩ : syracuseStep 7064405 = 41393) (by norm_num)
theorem B3140437 : Blo 1859631 3140437 := bbase (se 9 (by rfl) ⟨9200, by rfl⟩ : syracuseStep 3140437 = 18401) (by norm_num)
theorem B9423701 : Blo 1859631 9423701 := bbase (se 9 (by rfl) ⟨27608, by rfl⟩ : syracuseStep 9423701 = 55217) (by norm_num)
theorem B2354017 : Blo 1859631 2354017 := bbase (se 2 (by rfl) ⟨882756, by rfl⟩ : syracuseStep 2354017 = 1765513) (by norm_num)
theorem B2648981 : Blo 1859631 2648981 := bbase (se 6 (by rfl) ⟨62085, by rfl⟩ : syracuseStep 2648981 = 124171) (by norm_num)
theorem B3140525 : Blo 1859631 3140525 := bbase (se 3 (by rfl) ⟨588848, by rfl⟩ : syracuseStep 3140525 = 1177697) (by norm_num)
theorem B2354113 : Blo 1859631 2354113 := bbase (se 2 (by rfl) ⟨882792, by rfl⟩ : syracuseStep 2354113 = 1765585) (by norm_num)
theorem B2649061 : Blo 1859631 2649061 := bbase (se 4 (by rfl) ⟨248349, by rfl⟩ : syracuseStep 2649061 = 496699) (by norm_num)
theorem B3533797 : Blo 1859631 3533797 := bbase (se 4 (by rfl) ⟨331293, by rfl⟩ : syracuseStep 3533797 = 662587) (by norm_num)
theorem B3140653 : Blo 1859631 3140653 := bbase (se 3 (by rfl) ⟨588872, by rfl⟩ : syracuseStep 3140653 = 1177745) (by norm_num)
theorem B3771461 : Blo 1859631 3771461 := bbase (se 4 (by rfl) ⟨353574, by rfl⟩ : syracuseStep 3771461 = 707149) (by norm_num)
theorem B2092117 : Blo 1859631 2092117 := bbase (se 8 (by rfl) ⟨12258, by rfl⟩ : syracuseStep 2092117 = 24517) (by norm_num)
theorem B2649181 : Blo 1859631 2649181 := bbase (se 3 (by rfl) ⟨496721, by rfl⟩ : syracuseStep 2649181 = 993443) (by norm_num)
theorem B2354285 : Blo 1859631 2354285 := bbase (se 3 (by rfl) ⟨441428, by rfl⟩ : syracuseStep 2354285 = 882857) (by norm_num)
theorem B2092153 : Blo 1859631 2092153 := bbase (se 2 (by rfl) ⟨784557, by rfl⟩ : syracuseStep 2092153 = 1569115) (by norm_num)
theorem B3140741 : Blo 1859631 3140741 := bbase (se 4 (by rfl) ⟨294444, by rfl⟩ : syracuseStep 3140741 = 588889) (by norm_num)
theorem B2092189 : Blo 1859631 2092189 := bbase (se 3 (by rfl) ⟨392285, by rfl⟩ : syracuseStep 2092189 = 784571) (by norm_num)
theorem B2354341 : Blo 1859631 2354341 := bbase (se 4 (by rfl) ⟨220719, by rfl⟩ : syracuseStep 2354341 = 441439) (by norm_num)
theorem B6278309 : Blo 1859631 6278309 := bbase (se 4 (by rfl) ⟨588591, by rfl⟩ : syracuseStep 6278309 = 1177183) (by norm_num)
theorem B2649277 : Blo 1859631 2649277 := bbase (se 3 (by rfl) ⟨496739, by rfl⟩ : syracuseStep 2649277 = 993479) (by norm_num)
theorem B2092225 : Blo 1859631 2092225 := bbase (se 2 (by rfl) ⟨784584, by rfl⟩ : syracuseStep 2092225 = 1569169) (by norm_num)
theorem B2092261 : Blo 1859631 2092261 := bbase (se 4 (by rfl) ⟨196149, by rfl⟩ : syracuseStep 2092261 = 392299) (by norm_num)
theorem B9415925 : Blo 1859631 9415925 := bbase (se 5 (by rfl) ⟨441371, by rfl⟩ : syracuseStep 9415925 = 882743) (by norm_num)
theorem B2354437 : Blo 1859631 2354437 := bbase (se 4 (by rfl) ⟨220728, by rfl⟩ : syracuseStep 2354437 = 441457) (by norm_num)
theorem B3140869 : Blo 1859631 3140869 := bbase (se 4 (by rfl) ⟨294456, by rfl⟩ : syracuseStep 3140869 = 588913) (by norm_num)
theorem B2092297 : Blo 1859631 2092297 := bbase (se 2 (by rfl) ⟨784611, by rfl⟩ : syracuseStep 2092297 = 1569223) (by norm_num)
theorem B3534101 : Blo 1859631 3534101 := bbase (se 6 (by rfl) ⟨82830, by rfl⟩ : syracuseStep 3534101 = 165661) (by norm_num)
theorem B2092333 : Blo 1859631 2092333 := bbase (se 3 (by rfl) ⟨392312, by rfl⟩ : syracuseStep 2092333 = 784625) (by norm_num)
theorem B2092369 : Blo 1859631 2092369 := bbase (se 2 (by rfl) ⟨784638, by rfl⟩ : syracuseStep 2092369 = 1569277) (by norm_num)
theorem B3140957 : Blo 1859631 3140957 := bbase (se 3 (by rfl) ⟨588929, by rfl⟩ : syracuseStep 3140957 = 1177859) (by norm_num)
theorem B2092405 : Blo 1859631 2092405 := bbase (se 5 (by rfl) ⟨98081, by rfl⟩ : syracuseStep 2092405 = 196163) (by norm_num)
theorem B5737861 : Blo 1859631 5737861 := bbase (se 4 (by rfl) ⟨537924, by rfl⟩ : syracuseStep 5737861 = 1075849) (by norm_num)
theorem B2092441 : Blo 1859631 2092441 := bbase (se 2 (by rfl) ⟨784665, by rfl⟩ : syracuseStep 2092441 = 1569331) (by norm_num)
theorem B2354609 : Blo 1859631 2354609 := bbase (se 2 (by rfl) ⟨882978, by rfl⟩ : syracuseStep 2354609 = 1765957) (by norm_num)
theorem B2092477 : Blo 1859631 2092477 := bbase (se 3 (by rfl) ⟨392339, by rfl⟩ : syracuseStep 2092477 = 784679) (by norm_num)
theorem B1986001 : Blo 1859631 1986001 := bbase (se 2 (by rfl) ⟨744750, by rfl⟩ : syracuseStep 1986001 = 1489501) (by norm_num)
theorem B3141085 : Blo 1859631 3141085 := bbase (se 3 (by rfl) ⟨588953, by rfl⟩ : syracuseStep 3141085 = 1177907) (by norm_num)
theorem B2092513 : Blo 1859631 2092513 := bbase (se 2 (by rfl) ⟨784692, by rfl⟩ : syracuseStep 2092513 = 1569385) (by norm_num)
theorem B2354665 : Blo 1859631 2354665 := bbase (se 2 (by rfl) ⟨882999, by rfl⟩ : syracuseStep 2354665 = 1765999) (by norm_num)
theorem B2092549 : Blo 1859631 2092549 := bbase (se 4 (by rfl) ⟨196176, by rfl⟩ : syracuseStep 2092549 = 392353) (by norm_num)
theorem B2092585 : Blo 1859631 2092585 := bbase (se 2 (by rfl) ⟨784719, by rfl⟩ : syracuseStep 2092585 = 1569439) (by norm_num)
theorem B3141173 : Blo 1859631 3141173 := bbase (se 5 (by rfl) ⟨147242, by rfl⟩ : syracuseStep 3141173 = 294485) (by norm_num)
theorem B1986121 : Blo 1859631 1986121 := bbase (se 2 (by rfl) ⟨744795, by rfl⟩ : syracuseStep 1986121 = 1489591) (by norm_num)
theorem B2354761 : Blo 1859631 2354761 := bbase (se 2 (by rfl) ⟨883035, by rfl⟩ : syracuseStep 2354761 = 1766071) (by norm_num)
theorem B2092621 : Blo 1859631 2092621 := bbase (se 3 (by rfl) ⟨392366, by rfl⟩ : syracuseStep 2092621 = 784733) (by norm_num)
theorem B6278741 : Blo 1859631 6278741 := bbase (se 8 (by rfl) ⟨36789, by rfl⟩ : syracuseStep 6278741 = 73579) (by norm_num)
theorem B71528021 : Blo 1859631 71528021 := bbase (se 8 (by rfl) ⟨419109, by rfl⟩ : syracuseStep 71528021 = 838219) (by norm_num)
theorem B2092657 : Blo 1859631 2092657 := bbase (se 2 (by rfl) ⟨784746, by rfl⟩ : syracuseStep 2092657 = 1569493) (by norm_num)
theorem B4468349 : Blo 1859631 4468349 := bbase (se 3 (by rfl) ⟨837815, by rfl⟩ : syracuseStep 4468349 = 1675631) (by norm_num)
theorem B2092693 : Blo 1859631 2092693 := bbase (se 6 (by rfl) ⟨49047, by rfl⟩ : syracuseStep 2092693 = 98095) (by norm_num)
theorem B2649773 : Blo 1859631 2649773 := bbase (se 3 (by rfl) ⟨496832, by rfl⟩ : syracuseStep 2649773 = 993665) (by norm_num)
theorem B3141301 : Blo 1859631 3141301 := bbase (se 5 (by rfl) ⟨147248, by rfl⟩ : syracuseStep 3141301 = 294497) (by norm_num)
theorem B2092729 : Blo 1859631 2092729 := bbase (se 2 (by rfl) ⟨784773, by rfl⟩ : syracuseStep 2092729 = 1569547) (by norm_num)
theorem B2092765 : Blo 1859631 2092765 := bbase (se 3 (by rfl) ⟨392393, by rfl⟩ : syracuseStep 2092765 = 784787) (by norm_num)
theorem B7540469 : Blo 1859631 7540469 := bbase (se 5 (by rfl) ⟨353459, by rfl⟩ : syracuseStep 7540469 = 706919) (by norm_num)
theorem B2354933 : Blo 1859631 2354933 := bbase (se 5 (by rfl) ⟨110387, by rfl⟩ : syracuseStep 2354933 = 220775) (by norm_num)
theorem B2092801 : Blo 1859631 2092801 := bbase (se 2 (by rfl) ⟨784800, by rfl⟩ : syracuseStep 2092801 = 1569601) (by norm_num)
theorem B3141389 : Blo 1859631 3141389 := bbase (se 3 (by rfl) ⟨589010, by rfl⟩ : syracuseStep 3141389 = 1178021) (by norm_num)
theorem B2092837 : Blo 1859631 2092837 := bbase (se 4 (by rfl) ⟨196203, by rfl⟩ : syracuseStep 2092837 = 392407) (by norm_num)
theorem B2354989 : Blo 1859631 2354989 := bbase (se 3 (by rfl) ⟨441560, by rfl⟩ : syracuseStep 2354989 = 883121) (by norm_num)
theorem B1986373 : Blo 1859631 1986373 := bbase (se 4 (by rfl) ⟨186222, by rfl⟩ : syracuseStep 1986373 = 372445) (by norm_num)
theorem B1986377 : Blo 1859631 1986377 := bbase (se 2 (by rfl) ⟨744891, by rfl⟩ : syracuseStep 1986377 = 1489783) (by norm_num)
theorem B2092873 : Blo 1859631 2092873 := bbase (se 2 (by rfl) ⟨784827, by rfl⟩ : syracuseStep 2092873 = 1569655) (by norm_num)
theorem B2092909 : Blo 1859631 2092909 := bbase (se 3 (by rfl) ⟨392420, by rfl⟩ : syracuseStep 2092909 = 784841) (by norm_num)
theorem B5959541 : Blo 1859631 5959541 := bbase (se 5 (by rfl) ⟨279353, by rfl⟩ : syracuseStep 5959541 = 558707) (by norm_num)
theorem B2355085 : Blo 1859631 2355085 := bbase (se 3 (by rfl) ⟨441578, by rfl⟩ : syracuseStep 2355085 = 883157) (by norm_num)
theorem B2092945 : Blo 1859631 2092945 := bbase (se 2 (by rfl) ⟨784854, by rfl⟩ : syracuseStep 2092945 = 1569709) (by norm_num)
theorem B2387885 : Blo 1859631 2387885 := bbase (se 3 (by rfl) ⟨447728, by rfl⟩ : syracuseStep 2387885 = 895457) (by norm_num)
theorem B2092981 : Blo 1859631 2092981 := bbase (se 5 (by rfl) ⟨98108, by rfl⟩ : syracuseStep 2092981 = 196217) (by norm_num)
theorem B2093017 : Blo 1859631 2093017 := bbase (se 2 (by rfl) ⟨784881, by rfl⟩ : syracuseStep 2093017 = 1569763) (by norm_num)
theorem B5296117 : Blo 1859631 5296117 := bbase (se 5 (by rfl) ⟨248255, by rfl⟩ : syracuseStep 5296117 = 496511) (by norm_num)
theorem B6123509 : Blo 1859631 6123509 := bbase (se 5 (by rfl) ⟨287039, by rfl⟩ : syracuseStep 6123509 = 574079) (by norm_num)
theorem B7065589 : Blo 1859631 7065589 := bbase (se 5 (by rfl) ⟨331199, by rfl⟩ : syracuseStep 7065589 = 662399) (by norm_num)
theorem B2093053 : Blo 1859631 2093053 := bbase (se 3 (by rfl) ⟨392447, by rfl⟩ : syracuseStep 2093053 = 784895) (by norm_num)
theorem B6279173 : Blo 1859631 6279173 := bbase (se 4 (by rfl) ⟨588672, by rfl⟩ : syracuseStep 6279173 = 1177345) (by norm_num)
theorem B2797589 : Blo 1859631 2797589 := bbase (se 6 (by rfl) ⟨65568, by rfl⟩ : syracuseStep 2797589 = 131137) (by norm_num)
theorem B2093089 : Blo 1859631 2093089 := bbase (se 2 (by rfl) ⟨784908, by rfl⟩ : syracuseStep 2093089 = 1569817) (by norm_num)
theorem B2355257 : Blo 1859631 2355257 := bbase (se 2 (by rfl) ⟨883221, by rfl⟩ : syracuseStep 2355257 = 1766443) (by norm_num)
theorem B2093125 : Blo 1859631 2093125 := bbase (se 4 (by rfl) ⟨196230, by rfl⟩ : syracuseStep 2093125 = 392461) (by norm_num)
theorem B2789453 : Blo 1859631 2789453 := bbase (se 3 (by rfl) ⟨523022, by rfl⟩ : syracuseStep 2789453 = 1046045) (by norm_num)
theorem B3182669 : Blo 1859631 3182669 := bbase (se 3 (by rfl) ⟨596750, by rfl⟩ : syracuseStep 3182669 = 1193501) (by norm_num)
theorem B2789477 : Blo 1859631 2789477 := bbase (se 4 (by rfl) ⟨261513, by rfl⟩ : syracuseStep 2789477 = 523027) (by norm_num)
theorem B2093161 : Blo 1859631 2093161 := bbase (se 2 (by rfl) ⟨784935, by rfl⟩ : syracuseStep 2093161 = 1569871) (by norm_num)
theorem B2355313 : Blo 1859631 2355313 := bbase (se 2 (by rfl) ⟨883242, by rfl⟩ : syracuseStep 2355313 = 1766485) (by norm_num)
theorem B2789501 : Blo 1859631 2789501 := bbase (se 3 (by rfl) ⟨523031, by rfl⟩ : syracuseStep 2789501 = 1046063) (by norm_num)
theorem B2093197 : Blo 1859631 2093197 := bbase (se 3 (by rfl) ⟨392474, by rfl⟩ : syracuseStep 2093197 = 784949) (by norm_num)
theorem B2789525 : Blo 1859631 2789525 := bbase (se 6 (by rfl) ⟨65379, by rfl⟩ : syracuseStep 2789525 = 130759) (by norm_num)
theorem B2789549 : Blo 1859631 2789549 := bbase (se 3 (by rfl) ⟨523040, by rfl⟩ : syracuseStep 2789549 = 1046081) (by norm_num)
theorem B2093233 : Blo 1859631 2093233 := bbase (se 2 (by rfl) ⟨784962, by rfl⟩ : syracuseStep 2093233 = 1569925) (by norm_num)
theorem B2789573 : Blo 1859631 2789573 := bbase (se 4 (by rfl) ⟨261522, by rfl⟩ : syracuseStep 2789573 = 523045) (by norm_num)
theorem B2355409 : Blo 1859631 2355409 := bbase (se 2 (by rfl) ⟨883278, by rfl⟩ : syracuseStep 2355409 = 1766557) (by norm_num)
theorem B2093269 : Blo 1859631 2093269 := bbase (se 7 (by rfl) ⟨24530, by rfl⟩ : syracuseStep 2093269 = 49061) (by norm_num)
theorem B35778773 : Blo 1859631 35778773 := bbase (se 7 (by rfl) ⟨419282, by rfl⟩ : syracuseStep 35778773 = 838565) (by norm_num)
theorem B2650325 : Blo 1859631 2650325 := bbase (se 7 (by rfl) ⟨31058, by rfl⟩ : syracuseStep 2650325 = 62117) (by norm_num)
theorem B2150617 : Blo 1859631 2150617 := bbase (se 2 (by rfl) ⟨806481, by rfl⟩ : syracuseStep 2150617 = 1612963) (by norm_num)
theorem B2789597 : Blo 1859631 2789597 := bbase (se 3 (by rfl) ⟨523049, by rfl⟩ : syracuseStep 2789597 = 1046099) (by norm_num)
theorem B7950565 : Blo 1859631 7950565 := bbase (se 4 (by rfl) ⟨745365, by rfl⟩ : syracuseStep 7950565 = 1490731) (by norm_num)
theorem B2789621 : Blo 1859631 2789621 := bbase (se 5 (by rfl) ⟨130763, by rfl⟩ : syracuseStep 2789621 = 261527) (by norm_num)
theorem B2093305 : Blo 1859631 2093305 := bbase (se 2 (by rfl) ⟨784989, by rfl⟩ : syracuseStep 2093305 = 1569979) (by norm_num)
theorem B2789645 : Blo 1859631 2789645 := bbase (se 3 (by rfl) ⟨523058, by rfl⟩ : syracuseStep 2789645 = 1046117) (by norm_num)
theorem B2093341 : Blo 1859631 2093341 := bbase (se 3 (by rfl) ⟨392501, by rfl⟩ : syracuseStep 2093341 = 785003) (by norm_num)
theorem B2789669 : Blo 1859631 2789669 := bbase (se 4 (by rfl) ⟨261531, by rfl⟩ : syracuseStep 2789669 = 523063) (by norm_num)
theorem B7065893 : Blo 1859631 7065893 := bbase (se 4 (by rfl) ⟨662427, by rfl⟩ : syracuseStep 7065893 = 1324855) (by norm_num)
theorem B2789693 : Blo 1859631 2789693 := bbase (se 3 (by rfl) ⟨523067, by rfl⟩ : syracuseStep 2789693 = 1046135) (by norm_num)
theorem B2093377 : Blo 1859631 2093377 := bbase (se 2 (by rfl) ⟨785016, by rfl⟩ : syracuseStep 2093377 = 1570033) (by norm_num)
theorem B2789717 : Blo 1859631 2789717 := bbase (se 10 (by rfl) ⟨4086, by rfl⟩ : syracuseStep 2789717 = 8173) (by norm_num)
theorem B3772765 : Blo 1859631 3772765 := bbase (se 3 (by rfl) ⟨707393, by rfl⟩ : syracuseStep 3772765 = 1414787) (by norm_num)
theorem B2093413 : Blo 1859631 2093413 := bbase (se 4 (by rfl) ⟨196257, by rfl⟩ : syracuseStep 2093413 = 392515) (by norm_num)
theorem B2789741 : Blo 1859631 2789741 := bbase (se 3 (by rfl) ⟨523076, by rfl⟩ : syracuseStep 2789741 = 1046153) (by norm_num)
theorem B1986941 : Blo 1859631 1986941 := bbase (se 3 (by rfl) ⟨372551, by rfl⟩ : syracuseStep 1986941 = 745103) (by norm_num)
theorem B2355581 : Blo 1859631 2355581 := bbase (se 3 (by rfl) ⟨441671, by rfl⟩ : syracuseStep 2355581 = 883343) (by norm_num)
theorem B2789765 : Blo 1859631 2789765 := bbase (se 4 (by rfl) ⟨261540, by rfl⟩ : syracuseStep 2789765 = 523081) (by norm_num)
theorem B2093449 : Blo 1859631 2093449 := bbase (se 2 (by rfl) ⟨785043, by rfl⟩ : syracuseStep 2093449 = 1570087) (by norm_num)
theorem B2789789 : Blo 1859631 2789789 := bbase (se 3 (by rfl) ⟨523085, by rfl⟩ : syracuseStep 2789789 = 1046171) (by norm_num)
theorem B2093485 : Blo 1859631 2093485 := bbase (se 3 (by rfl) ⟨392528, by rfl⟩ : syracuseStep 2093485 = 785057) (by norm_num)
theorem B2789813 : Blo 1859631 2789813 := bbase (se 5 (by rfl) ⟨130772, by rfl⟩ : syracuseStep 2789813 = 261545) (by norm_num)
theorem B6279605 : Blo 1859631 6279605 := bbase (se 5 (by rfl) ⟨294356, by rfl⟩ : syracuseStep 6279605 = 588713) (by norm_num)
theorem B2355637 : Blo 1859631 2355637 := bbase (se 5 (by rfl) ⟨110420, by rfl⟩ : syracuseStep 2355637 = 220841) (by norm_num)
theorem B2789837 : Blo 1859631 2789837 := bbase (se 3 (by rfl) ⟨523094, by rfl⟩ : syracuseStep 2789837 = 1046189) (by norm_num)
theorem B2093521 : Blo 1859631 2093521 := bbase (se 2 (by rfl) ⟨785070, by rfl⟩ : syracuseStep 2093521 = 1570141) (by norm_num)
theorem B48320981 : Blo 1859631 48320981 := bbase (se 7 (by rfl) ⟨566261, by rfl⟩ : syracuseStep 48320981 = 1132523) (by norm_num)
theorem B2789861 : Blo 1859631 2789861 := bbase (se 4 (by rfl) ⟨261549, by rfl⟩ : syracuseStep 2789861 = 523099) (by norm_num)
theorem B2093557 : Blo 1859631 2093557 := bbase (se 5 (by rfl) ⟨98135, by rfl⟩ : syracuseStep 2093557 = 196271) (by norm_num)
theorem B2789885 : Blo 1859631 2789885 := bbase (se 3 (by rfl) ⟨523103, by rfl⟩ : syracuseStep 2789885 = 1046207) (by norm_num)
theorem B9417221 : Blo 1859631 9417221 := bbase (se 4 (by rfl) ⟨882864, by rfl⟩ : syracuseStep 9417221 = 1765729) (by norm_num)
theorem B2789909 : Blo 1859631 2789909 := bbase (se 6 (by rfl) ⟨65388, by rfl⟩ : syracuseStep 2789909 = 130777) (by norm_num)
theorem B2355733 : Blo 1859631 2355733 := bbase (se 6 (by rfl) ⟨55212, by rfl⟩ : syracuseStep 2355733 = 110425) (by norm_num)
theorem B2093593 : Blo 1859631 2093593 := bbase (se 2 (by rfl) ⟨785097, by rfl⟩ : syracuseStep 2093593 = 1570195) (by norm_num)
theorem B2789933 : Blo 1859631 2789933 := bbase (se 3 (by rfl) ⟨523112, by rfl⟩ : syracuseStep 2789933 = 1046225) (by norm_num)
theorem B1987129 : Blo 1859631 1987129 := bbase (se 2 (by rfl) ⟨745173, by rfl⟩ : syracuseStep 1987129 = 1490347) (by norm_num)
theorem B2093629 : Blo 1859631 2093629 := bbase (se 3 (by rfl) ⟨392555, by rfl⟩ : syracuseStep 2093629 = 785111) (by norm_num)
theorem B2789957 : Blo 1859631 2789957 := bbase (se 4 (by rfl) ⟨261558, by rfl⟩ : syracuseStep 2789957 = 523117) (by norm_num)
theorem B2789981 : Blo 1859631 2789981 := bbase (se 3 (by rfl) ⟨523121, by rfl⟩ : syracuseStep 2789981 = 1046243) (by norm_num)
theorem B2093665 : Blo 1859631 2093665 := bbase (se 2 (by rfl) ⟨785124, by rfl⟩ : syracuseStep 2093665 = 1570249) (by norm_num)
theorem B2790005 : Blo 1859631 2790005 := bbase (se 5 (by rfl) ⟨130781, by rfl⟩ : syracuseStep 2790005 = 261563) (by norm_num)
theorem B2093701 : Blo 1859631 2093701 := bbase (se 4 (by rfl) ⟨196284, by rfl⟩ : syracuseStep 2093701 = 392569) (by norm_num)
theorem B2790029 : Blo 1859631 2790029 := bbase (se 3 (by rfl) ⟨523130, by rfl⟩ : syracuseStep 2790029 = 1046261) (by norm_num)
theorem B2790053 : Blo 1859631 2790053 := bbase (se 4 (by rfl) ⟨261567, by rfl⟩ : syracuseStep 2790053 = 523135) (by norm_num)
theorem B2093737 : Blo 1859631 2093737 := bbase (se 2 (by rfl) ⟨785151, by rfl⟩ : syracuseStep 2093737 = 1570303) (by norm_num)
theorem B2790077 : Blo 1859631 2790077 := bbase (se 3 (by rfl) ⟨523139, by rfl⟩ : syracuseStep 2790077 = 1046279) (by norm_num)
theorem B2355905 : Blo 1859631 2355905 := bbase (se 2 (by rfl) ⟨883464, by rfl⟩ : syracuseStep 2355905 = 1766929) (by norm_num)
theorem B2093773 : Blo 1859631 2093773 := bbase (se 3 (by rfl) ⟨392582, by rfl⟩ : syracuseStep 2093773 = 785165) (by norm_num)
theorem B2790101 : Blo 1859631 2790101 := bbase (se 7 (by rfl) ⟨32696, by rfl⟩ : syracuseStep 2790101 = 65393) (by norm_num)
theorem B2790125 : Blo 1859631 2790125 := bbase (se 3 (by rfl) ⟨523148, by rfl⟩ : syracuseStep 2790125 = 1046297) (by norm_num)
theorem B2093809 : Blo 1859631 2093809 := bbase (se 2 (by rfl) ⟨785178, by rfl⟩ : syracuseStep 2093809 = 1570357) (by norm_num)
theorem B2355961 : Blo 1859631 2355961 := bbase (se 2 (by rfl) ⟨883485, by rfl⟩ : syracuseStep 2355961 = 1766971) (by norm_num)
theorem B2790149 : Blo 1859631 2790149 := bbase (se 4 (by rfl) ⟨261576, by rfl⟩ : syracuseStep 2790149 = 523153) (by norm_num)
theorem B2093845 : Blo 1859631 2093845 := bbase (se 6 (by rfl) ⟨49074, by rfl⟩ : syracuseStep 2093845 = 98149) (by norm_num)
theorem B2790173 : Blo 1859631 2790173 := bbase (se 3 (by rfl) ⟨523157, by rfl⟩ : syracuseStep 2790173 = 1046315) (by norm_num)
theorem B3773213 : Blo 1859631 3773213 := bbase (se 3 (by rfl) ⟨707477, by rfl⟩ : syracuseStep 3773213 = 1414955) (by norm_num)
theorem B2790197 : Blo 1859631 2790197 := bbase (se 5 (by rfl) ⟨130790, by rfl⟩ : syracuseStep 2790197 = 261581) (by norm_num)
theorem B2093881 : Blo 1859631 2093881 := bbase (se 2 (by rfl) ⟨785205, by rfl⟩ : syracuseStep 2093881 = 1570411) (by norm_num)
theorem B2790221 : Blo 1859631 2790221 := bbase (se 3 (by rfl) ⟨523166, by rfl⟩ : syracuseStep 2790221 = 1046333) (by norm_num)
theorem B2356057 : Blo 1859631 2356057 := bbase (se 2 (by rfl) ⟨883521, by rfl⟩ : syracuseStep 2356057 = 1767043) (by norm_num)
theorem B2093917 : Blo 1859631 2093917 := bbase (se 3 (by rfl) ⟨392609, by rfl⟩ : syracuseStep 2093917 = 785219) (by norm_num)
theorem B2790245 : Blo 1859631 2790245 := bbase (se 4 (by rfl) ⟨261585, by rfl⟩ : syracuseStep 2790245 = 523171) (by norm_num)
theorem B6280037 : Blo 1859631 6280037 := bbase (se 4 (by rfl) ⟨588753, by rfl⟩ : syracuseStep 6280037 = 1177507) (by norm_num)
theorem B2790269 : Blo 1859631 2790269 := bbase (se 3 (by rfl) ⟨523175, by rfl⟩ : syracuseStep 2790269 = 1046351) (by norm_num)
theorem B2093953 : Blo 1859631 2093953 := bbase (se 2 (by rfl) ⟨785232, by rfl⟩ : syracuseStep 2093953 = 1570465) (by norm_num)
theorem B2790293 : Blo 1859631 2790293 := bbase (se 6 (by rfl) ⟨65397, by rfl⟩ : syracuseStep 2790293 = 130795) (by norm_num)
theorem B2093989 : Blo 1859631 2093989 := bbase (se 4 (by rfl) ⟨196311, by rfl⟩ : syracuseStep 2093989 = 392623) (by norm_num)
theorem B2790317 : Blo 1859631 2790317 := bbase (se 3 (by rfl) ⟨523184, by rfl⟩ : syracuseStep 2790317 = 1046369) (by norm_num)
theorem B2790341 : Blo 1859631 2790341 := bbase (se 4 (by rfl) ⟨261594, by rfl⟩ : syracuseStep 2790341 = 523189) (by norm_num)
theorem B2094025 : Blo 1859631 2094025 := bbase (se 2 (by rfl) ⟨785259, by rfl⟩ : syracuseStep 2094025 = 1570519) (by norm_num)
theorem B2790365 : Blo 1859631 2790365 := bbase (se 3 (by rfl) ⟨523193, by rfl⟩ : syracuseStep 2790365 = 1046387) (by norm_num)
theorem B2978797 : Blo 1859631 2978797 := bbase (se 3 (by rfl) ⟨558524, by rfl⟩ : syracuseStep 2978797 = 1117049) (by norm_num)
theorem B2094061 : Blo 1859631 2094061 := bbase (se 3 (by rfl) ⟨392636, by rfl⟩ : syracuseStep 2094061 = 785273) (by norm_num)
theorem B2790389 : Blo 1859631 2790389 := bbase (se 5 (by rfl) ⟨130799, by rfl⟩ : syracuseStep 2790389 = 261599) (by norm_num)
theorem B2790413 : Blo 1859631 2790413 := bbase (se 3 (by rfl) ⟨523202, by rfl⟩ : syracuseStep 2790413 = 1046405) (by norm_num)
theorem B2094097 : Blo 1859631 2094097 := bbase (se 2 (by rfl) ⟨785286, by rfl⟩ : syracuseStep 2094097 = 1570573) (by norm_num)
theorem B2790437 : Blo 1859631 2790437 := bbase (se 4 (by rfl) ⟨261603, by rfl⟩ : syracuseStep 2790437 = 523207) (by norm_num)
theorem B2978861 : Blo 1859631 2978861 := bbase (se 3 (by rfl) ⟨558536, by rfl⟩ : syracuseStep 2978861 = 1117073) (by norm_num)
theorem B2094133 : Blo 1859631 2094133 := bbase (se 5 (by rfl) ⟨98162, by rfl⟩ : syracuseStep 2094133 = 196325) (by norm_num)
theorem B2790461 : Blo 1859631 2790461 := bbase (se 3 (by rfl) ⟨523211, by rfl⟩ : syracuseStep 2790461 = 1046423) (by norm_num)
theorem B3822661 : Blo 1859631 3822661 := bbase (se 4 (by rfl) ⟨358374, by rfl⟩ : syracuseStep 3822661 = 716749) (by norm_num)
theorem B2790485 : Blo 1859631 2790485 := bbase (se 8 (by rfl) ⟨16350, by rfl⟩ : syracuseStep 2790485 = 32701) (by norm_num)
theorem B2094169 : Blo 1859631 2094169 := bbase (se 2 (by rfl) ⟨785313, by rfl⟩ : syracuseStep 2094169 = 1570627) (by norm_num)
theorem B2790509 : Blo 1859631 2790509 := bbase (se 3 (by rfl) ⟨523220, by rfl⟩ : syracuseStep 2790509 = 1046441) (by norm_num)
theorem B2094205 : Blo 1859631 2094205 := bbase (se 3 (by rfl) ⟨392663, by rfl⟩ : syracuseStep 2094205 = 785327) (by norm_num)
theorem B2790533 : Blo 1859631 2790533 := bbase (se 4 (by rfl) ⟨261612, by rfl⟩ : syracuseStep 2790533 = 523225) (by norm_num)
theorem B2790557 : Blo 1859631 2790557 := bbase (se 3 (by rfl) ⟨523229, by rfl⟩ : syracuseStep 2790557 = 1046459) (by norm_num)
theorem B2094241 : Blo 1859631 2094241 := bbase (se 2 (by rfl) ⟨785340, by rfl⟩ : syracuseStep 2094241 = 1570681) (by norm_num)
theorem B2790581 : Blo 1859631 2790581 := bbase (se 5 (by rfl) ⟨130808, by rfl⟩ : syracuseStep 2790581 = 261617) (by norm_num)
theorem B4707517 : Blo 1859631 4707517 := bbase (se 3 (by rfl) ⟨882659, by rfl⟩ : syracuseStep 4707517 = 1765319) (by norm_num)
theorem B2094277 : Blo 1859631 2094277 := bbase (se 4 (by rfl) ⟨196338, by rfl⟩ : syracuseStep 2094277 = 392677) (by norm_num)
theorem B2790605 : Blo 1859631 2790605 := bbase (se 3 (by rfl) ⟨523238, by rfl⟩ : syracuseStep 2790605 = 1046477) (by norm_num)
theorem B1938637 : Blo 1859631 1938637 := bbase (se 3 (by rfl) ⟨363494, by rfl⟩ : syracuseStep 1938637 = 726989) (by norm_num)
theorem B11310293 : Blo 1859631 11310293 := bbase (se 7 (by rfl) ⟨132542, by rfl⟩ : syracuseStep 11310293 = 265085) (by norm_num)
theorem B2790629 : Blo 1859631 2790629 := bbase (se 4 (by rfl) ⟨261621, by rfl⟩ : syracuseStep 2790629 = 523243) (by norm_num)
theorem B2094313 : Blo 1859631 2094313 := bbase (se 2 (by rfl) ⟨785367, by rfl⟩ : syracuseStep 2094313 = 1570735) (by norm_num)
theorem B2790653 : Blo 1859631 2790653 := bbase (se 3 (by rfl) ⟨523247, by rfl⟩ : syracuseStep 2790653 = 1046495) (by norm_num)
theorem B5960965 : Blo 1859631 5960965 := bbase (se 4 (by rfl) ⟨558840, by rfl⟩ : syracuseStep 5960965 = 1117681) (by norm_num)
theorem B2790677 : Blo 1859631 2790677 := bbase (se 6 (by rfl) ⟨65406, by rfl⟩ : syracuseStep 2790677 = 130813) (by norm_num)
theorem B6280469 : Blo 1859631 6280469 := bbase (se 6 (by rfl) ⟨147198, by rfl⟩ : syracuseStep 6280469 = 294397) (by norm_num)
theorem B4707629 : Blo 1859631 4707629 := bbase (se 3 (by rfl) ⟨882680, by rfl⟩ : syracuseStep 4707629 = 1765361) (by norm_num)
theorem B4470061 : Blo 1859631 4470061 := bbase (se 3 (by rfl) ⟨838136, by rfl⟩ : syracuseStep 4470061 = 1676273) (by norm_num)
theorem B2790701 : Blo 1859631 2790701 := bbase (se 3 (by rfl) ⟨523256, by rfl⟩ : syracuseStep 2790701 = 1046513) (by norm_num)
theorem B2790725 : Blo 1859631 2790725 := bbase (se 4 (by rfl) ⟨261630, by rfl⟩ : syracuseStep 2790725 = 523261) (by norm_num)
theorem B2790749 : Blo 1859631 2790749 := bbase (se 3 (by rfl) ⟨523265, by rfl⟩ : syracuseStep 2790749 = 1046531) (by norm_num)
theorem B1987949 : Blo 1859631 1987949 := bbase (se 3 (by rfl) ⟨372740, by rfl⟩ : syracuseStep 1987949 = 745481) (by norm_num)
theorem B2790773 : Blo 1859631 2790773 := bbase (se 5 (by rfl) ⟨130817, by rfl⟩ : syracuseStep 2790773 = 261635) (by norm_num)
theorem B2790797 : Blo 1859631 2790797 := bbase (se 3 (by rfl) ⟨523274, by rfl⟩ : syracuseStep 2790797 = 1046549) (by norm_num)
theorem B2790821 : Blo 1859631 2790821 := bbase (se 4 (by rfl) ⟨261639, by rfl⟩ : syracuseStep 2790821 = 523279) (by norm_num)
theorem B2790845 : Blo 1859631 2790845 := bbase (se 3 (by rfl) ⟨523283, by rfl⟩ : syracuseStep 2790845 = 1046567) (by norm_num)
theorem B2790869 : Blo 1859631 2790869 := bbase (se 7 (by rfl) ⟨32705, by rfl⟩ : syracuseStep 2790869 = 65411) (by norm_num)
theorem B4707821 : Blo 1859631 4707821 := bbase (se 3 (by rfl) ⟨882716, by rfl⟩ : syracuseStep 4707821 = 1765433) (by norm_num)
theorem B2790893 : Blo 1859631 2790893 := bbase (se 3 (by rfl) ⟨523292, by rfl⟩ : syracuseStep 2790893 = 1046585) (by norm_num)
theorem B2790917 : Blo 1859631 2790917 := bbase (se 4 (by rfl) ⟨261648, by rfl⟩ : syracuseStep 2790917 = 523297) (by norm_num)
theorem B2790941 : Blo 1859631 2790941 := bbase (se 3 (by rfl) ⟨523301, by rfl⟩ : syracuseStep 2790941 = 1046603) (by norm_num)
theorem B2790965 : Blo 1859631 2790965 := bbase (se 5 (by rfl) ⟨130826, by rfl⟩ : syracuseStep 2790965 = 261653) (by norm_num)
theorem B2790989 : Blo 1859631 2790989 := bbase (se 3 (by rfl) ⟨523310, by rfl⟩ : syracuseStep 2790989 = 1046621) (by norm_num)
theorem B2791013 : Blo 1859631 2791013 := bbase (se 4 (by rfl) ⟨261657, by rfl⟩ : syracuseStep 2791013 = 523315) (by norm_num)
theorem B3061373 : Blo 1859631 3061373 := bbase (se 3 (by rfl) ⟨574007, by rfl⟩ : syracuseStep 3061373 = 1148015) (by norm_num)
theorem B2791037 : Blo 1859631 2791037 := bbase (se 3 (by rfl) ⟨523319, by rfl⟩ : syracuseStep 2791037 = 1046639) (by norm_num)
theorem B2791061 : Blo 1859631 2791061 := bbase (se 6 (by rfl) ⟨65415, by rfl⟩ : syracuseStep 2791061 = 130831) (by norm_num)
theorem B2791085 : Blo 1859631 2791085 := bbase (se 3 (by rfl) ⟨523328, by rfl⟩ : syracuseStep 2791085 = 1046657) (by norm_num)
theorem B2791109 : Blo 1859631 2791109 := bbase (se 4 (by rfl) ⟨261666, by rfl⟩ : syracuseStep 2791109 = 523333) (by norm_num)
theorem B5961413 : Blo 1859631 5961413 := bbase (se 4 (by rfl) ⟨558882, by rfl⟩ : syracuseStep 5961413 = 1117765) (by norm_num)
theorem B6280901 : Blo 1859631 6280901 := bbase (se 4 (by rfl) ⟨588834, by rfl⟩ : syracuseStep 6280901 = 1177669) (by norm_num)
theorem B2791133 : Blo 1859631 2791133 := bbase (se 3 (by rfl) ⟨523337, by rfl⟩ : syracuseStep 2791133 = 1046675) (by norm_num)
theorem B4593389 : Blo 1859631 4593389 := bbase (se 3 (by rfl) ⟨861260, by rfl⟩ : syracuseStep 4593389 = 1722521) (by norm_num)
theorem B2791157 : Blo 1859631 2791157 := bbase (se 5 (by rfl) ⟨130835, by rfl⟩ : syracuseStep 2791157 = 261671) (by norm_num)
theorem B2791181 : Blo 1859631 2791181 := bbase (se 3 (by rfl) ⟨523346, by rfl⟩ : syracuseStep 2791181 = 1046693) (by norm_num)
theorem B9418517 : Blo 1859631 9418517 := bbase (se 6 (by rfl) ⟨220746, by rfl⟩ : syracuseStep 9418517 = 441493) (by norm_num)
theorem B3020581 : Blo 1859631 3020581 := bbase (se 4 (by rfl) ⟨283179, by rfl⟩ : syracuseStep 3020581 = 566359) (by norm_num)
theorem B2791205 : Blo 1859631 2791205 := bbase (se 4 (by rfl) ⟨261675, by rfl⟩ : syracuseStep 2791205 = 523351) (by norm_num)
theorem B14718773 : Blo 1859631 14718773 := bbase (se 5 (by rfl) ⟨689942, by rfl⟩ : syracuseStep 14718773 = 1379885) (by norm_num)
theorem B2791229 : Blo 1859631 2791229 := bbase (se 3 (by rfl) ⟨523355, by rfl⟩ : syracuseStep 2791229 = 1046711) (by norm_num)
theorem B4708165 : Blo 1859631 4708165 := bbase (se 4 (by rfl) ⟨441390, by rfl⟩ : syracuseStep 4708165 = 882781) (by norm_num)
theorem B2791253 : Blo 1859631 2791253 := bbase (se 9 (by rfl) ⟨8177, by rfl⟩ : syracuseStep 2791253 = 16355) (by norm_num)
theorem B2234209 : Blo 1859631 2234209 := bbase (se 2 (by rfl) ⟨837828, by rfl⟩ : syracuseStep 2234209 = 1675657) (by norm_num)
theorem B2791277 : Blo 1859631 2791277 := bbase (se 3 (by rfl) ⟨523364, by rfl⟩ : syracuseStep 2791277 = 1046729) (by norm_num)
theorem B2791301 : Blo 1859631 2791301 := bbase (se 4 (by rfl) ⟨261684, by rfl⟩ : syracuseStep 2791301 = 523369) (by norm_num)
theorem B4470677 : Blo 1859631 4470677 := bbase (se 6 (by rfl) ⟨104781, by rfl⟩ : syracuseStep 4470677 = 209563) (by norm_num)
theorem B2791325 : Blo 1859631 2791325 := bbase (se 3 (by rfl) ⟨523373, by rfl⟩ : syracuseStep 2791325 = 1046747) (by norm_num)
theorem B4708277 : Blo 1859631 4708277 := bbase (se 5 (by rfl) ⟨220700, by rfl⟩ : syracuseStep 4708277 = 441401) (by norm_num)
theorem B2791349 : Blo 1859631 2791349 := bbase (se 5 (by rfl) ⟨130844, by rfl⟩ : syracuseStep 2791349 = 261689) (by norm_num)
theorem B2234309 : Blo 1859631 2234309 := bbase (se 4 (by rfl) ⟨209466, by rfl⟩ : syracuseStep 2234309 = 418933) (by norm_num)
theorem B2791373 : Blo 1859631 2791373 := bbase (se 3 (by rfl) ⟨523382, by rfl⟩ : syracuseStep 2791373 = 1046765) (by norm_num)
theorem B2791397 : Blo 1859631 2791397 := bbase (se 4 (by rfl) ⟨261693, by rfl⟩ : syracuseStep 2791397 = 523387) (by norm_num)
theorem B2791421 : Blo 1859631 2791421 := bbase (se 3 (by rfl) ⟨523391, by rfl⟩ : syracuseStep 2791421 = 1046783) (by norm_num)
theorem B5027845 : Blo 1859631 5027845 := bbase (se 4 (by rfl) ⟨471360, by rfl⟩ : syracuseStep 5027845 = 942721) (by norm_num)
theorem B2791445 : Blo 1859631 2791445 := bbase (se 6 (by rfl) ⟨65424, by rfl⟩ : syracuseStep 2791445 = 130849) (by norm_num)
theorem B2791469 : Blo 1859631 2791469 := bbase (se 3 (by rfl) ⟨523400, by rfl⟩ : syracuseStep 2791469 = 1046801) (by norm_num)
theorem B2791493 : Blo 1859631 2791493 := bbase (se 4 (by rfl) ⟨261702, by rfl⟩ : syracuseStep 2791493 = 523405) (by norm_num)
theorem B5658709 : Blo 1859631 5658709 := bbase (se 8 (by rfl) ⟨33156, by rfl⟩ : syracuseStep 5658709 = 66313) (by norm_num)
theorem B2791517 : Blo 1859631 2791517 := bbase (se 3 (by rfl) ⟨523409, by rfl⟩ : syracuseStep 2791517 = 1046819) (by norm_num)
theorem B3446885 : Blo 1859631 3446885 := bbase (se 4 (by rfl) ⟨323145, by rfl⟩ : syracuseStep 3446885 = 646291) (by norm_num)
theorem B4708469 : Blo 1859631 4708469 := bbase (se 5 (by rfl) ⟨220709, by rfl⟩ : syracuseStep 4708469 = 441419) (by norm_num)
theorem B2791541 : Blo 1859631 2791541 := bbase (se 5 (by rfl) ⟨130853, by rfl⟩ : syracuseStep 2791541 = 261707) (by norm_num)
theorem B6281333 : Blo 1859631 6281333 := bbase (se 5 (by rfl) ⟨294437, by rfl⟩ : syracuseStep 6281333 = 588875) (by norm_num)
theorem B4184189 : Blo 1859631 4184189 := bbase (se 3 (by rfl) ⟨784535, by rfl⟩ : syracuseStep 4184189 = 1569071) (by norm_num)
theorem B4241533 : Blo 1859631 4241533 := bbase (se 3 (by rfl) ⟨795287, by rfl⟩ : syracuseStep 4241533 = 1590575) (by norm_num)
theorem B3061901 : Blo 1859631 3061901 := bbase (se 3 (by rfl) ⟨574106, by rfl⟩ : syracuseStep 3061901 = 1148213) (by norm_num)
theorem B2791565 : Blo 1859631 2791565 := bbase (se 3 (by rfl) ⟨523418, by rfl⟩ : syracuseStep 2791565 = 1046837) (by norm_num)
theorem B2013337 : Blo 1859631 2013337 := bbase (se 2 (by rfl) ⟨755001, by rfl⟩ : syracuseStep 2013337 = 1510003) (by norm_num)
theorem B2791589 : Blo 1859631 2791589 := bbase (se 4 (by rfl) ⟨261711, by rfl⟩ : syracuseStep 2791589 = 523423) (by norm_num)
theorem B2791613 : Blo 1859631 2791613 := bbase (se 3 (by rfl) ⟨523427, by rfl⟩ : syracuseStep 2791613 = 1046855) (by norm_num)
theorem B4184261 : Blo 1859631 4184261 := bbase (se 4 (by rfl) ⟨392274, by rfl⟩ : syracuseStep 4184261 = 784549) (by norm_num)
theorem B2791637 : Blo 1859631 2791637 := bbase (se 7 (by rfl) ⟨32714, by rfl⟩ : syracuseStep 2791637 = 65429) (by norm_num)
theorem B2791661 : Blo 1859631 2791661 := bbase (se 3 (by rfl) ⟨523436, by rfl⟩ : syracuseStep 2791661 = 1046873) (by norm_num)
theorem B9058549 : Blo 1859631 9058549 := bbase (se 5 (by rfl) ⟨424619, by rfl⟩ : syracuseStep 9058549 = 849239) (by norm_num)
theorem B2791685 : Blo 1859631 2791685 := bbase (se 4 (by rfl) ⟨261720, by rfl⟩ : syracuseStep 2791685 = 523441) (by norm_num)
theorem B4184333 : Blo 1859631 4184333 := bbase (se 3 (by rfl) ⟨784562, by rfl⟩ : syracuseStep 4184333 = 1569125) (by norm_num)
theorem B2791709 : Blo 1859631 2791709 := bbase (se 3 (by rfl) ⟨523445, by rfl⟩ : syracuseStep 2791709 = 1046891) (by norm_num)
theorem B2791733 : Blo 1859631 2791733 := bbase (se 5 (by rfl) ⟨130862, by rfl⟩ : syracuseStep 2791733 = 261725) (by norm_num)
theorem B4471109 : Blo 1859631 4471109 := bbase (se 4 (by rfl) ⟨419166, by rfl⟩ : syracuseStep 4471109 = 838333) (by norm_num)
theorem B2791757 : Blo 1859631 2791757 := bbase (se 3 (by rfl) ⟨523454, by rfl⟩ : syracuseStep 2791757 = 1046909) (by norm_num)
theorem B4184405 : Blo 1859631 4184405 := bbase (se 10 (by rfl) ⟨6129, by rfl⟩ : syracuseStep 4184405 = 12259) (by norm_num)
theorem B2980181 : Blo 1859631 2980181 := bbase (se 10 (by rfl) ⟨4365, by rfl⟩ : syracuseStep 2980181 = 8731) (by norm_num)
theorem B2791781 : Blo 1859631 2791781 := bbase (se 4 (by rfl) ⟨261729, by rfl⟩ : syracuseStep 2791781 = 523459) (by norm_num)
theorem B7068005 : Blo 1859631 7068005 := bbase (se 4 (by rfl) ⟨662625, by rfl⟩ : syracuseStep 7068005 = 1325251) (by norm_num)
theorem B2791805 : Blo 1859631 2791805 := bbase (se 3 (by rfl) ⟨523463, by rfl⟩ : syracuseStep 2791805 = 1046927) (by norm_num)
theorem B2791829 : Blo 1859631 2791829 := bbase (se 6 (by rfl) ⟨65433, by rfl⟩ : syracuseStep 2791829 = 130867) (by norm_num)
theorem B4184477 : Blo 1859631 4184477 := bbase (se 3 (by rfl) ⟨784589, by rfl⟩ : syracuseStep 4184477 = 1569179) (by norm_num)
theorem B2791853 : Blo 1859631 2791853 := bbase (se 3 (by rfl) ⟨523472, by rfl⟩ : syracuseStep 2791853 = 1046945) (by norm_num)
theorem B2791877 : Blo 1859631 2791877 := bbase (se 4 (by rfl) ⟨261738, by rfl⟩ : syracuseStep 2791877 = 523477) (by norm_num)
theorem B4708813 : Blo 1859631 4708813 := bbase (se 3 (by rfl) ⟨882902, by rfl⟩ : syracuseStep 4708813 = 1765805) (by norm_num)
theorem B2980309 : Blo 1859631 2980309 := bbase (se 7 (by rfl) ⟨34925, by rfl⟩ : syracuseStep 2980309 = 69851) (by norm_num)
theorem B2791901 : Blo 1859631 2791901 := bbase (se 3 (by rfl) ⟨523481, by rfl⟩ : syracuseStep 2791901 = 1046963) (by norm_num)
theorem B4184549 : Blo 1859631 4184549 := bbase (se 4 (by rfl) ⟨392301, by rfl⟩ : syracuseStep 4184549 = 784603) (by norm_num)
theorem B2791925 : Blo 1859631 2791925 := bbase (se 5 (by rfl) ⟨130871, by rfl⟩ : syracuseStep 2791925 = 261743) (by norm_num)
theorem B2791949 : Blo 1859631 2791949 := bbase (se 3 (by rfl) ⟨523490, by rfl⟩ : syracuseStep 2791949 = 1046981) (by norm_num)
theorem B6281765 : Blo 1859631 6281765 := bbase (se 4 (by rfl) ⟨588915, by rfl⟩ : syracuseStep 6281765 = 1177831) (by norm_num)
theorem B2791973 : Blo 1859631 2791973 := bbase (se 4 (by rfl) ⟨261747, by rfl⟩ : syracuseStep 2791973 = 523495) (by norm_num)
theorem B4184621 : Blo 1859631 4184621 := bbase (se 3 (by rfl) ⟨784616, by rfl⟩ : syracuseStep 4184621 = 1569233) (by norm_num)
theorem B4708925 : Blo 1859631 4708925 := bbase (se 3 (by rfl) ⟨882923, by rfl⟩ : syracuseStep 4708925 = 1765847) (by norm_num)
theorem B2791997 : Blo 1859631 2791997 := bbase (se 3 (by rfl) ⟨523499, by rfl⟩ : syracuseStep 2791997 = 1046999) (by norm_num)
theorem B2792021 : Blo 1859631 2792021 := bbase (se 8 (by rfl) ⟨16359, by rfl⟩ : syracuseStep 2792021 = 32719) (by norm_num)
theorem B2792045 : Blo 1859631 2792045 := bbase (se 3 (by rfl) ⟨523508, by rfl⟩ : syracuseStep 2792045 = 1047017) (by norm_num)
theorem B4184693 : Blo 1859631 4184693 := bbase (se 5 (by rfl) ⟨196157, by rfl⟩ : syracuseStep 4184693 = 392315) (by norm_num)
theorem B2792069 : Blo 1859631 2792069 := bbase (se 4 (by rfl) ⟨261756, by rfl⟩ : syracuseStep 2792069 = 523513) (by norm_num)
theorem B7068293 : Blo 1859631 7068293 := bbase (se 4 (by rfl) ⟨662652, by rfl⟩ : syracuseStep 7068293 = 1325305) (by norm_num)
theorem B2792093 : Blo 1859631 2792093 := bbase (se 3 (by rfl) ⟨523517, by rfl⟩ : syracuseStep 2792093 = 1047035) (by norm_num)
theorem B2792117 : Blo 1859631 2792117 := bbase (se 5 (by rfl) ⟨130880, by rfl⟩ : syracuseStep 2792117 = 261761) (by norm_num)
theorem B4184765 : Blo 1859631 4184765 := bbase (se 3 (by rfl) ⟨784643, by rfl⟩ : syracuseStep 4184765 = 1569287) (by norm_num)
theorem B2792141 : Blo 1859631 2792141 := bbase (se 3 (by rfl) ⟨523526, by rfl⟩ : syracuseStep 2792141 = 1047053) (by norm_num)
theorem B2235097 : Blo 1859631 2235097 := bbase (se 2 (by rfl) ⟨838161, by rfl⟩ : syracuseStep 2235097 = 1676323) (by norm_num)
theorem B2792165 : Blo 1859631 2792165 := bbase (se 4 (by rfl) ⟨261765, by rfl⟩ : syracuseStep 2792165 = 523531) (by norm_num)
theorem B4709117 : Blo 1859631 4709117 := bbase (se 3 (by rfl) ⟨882959, by rfl⟩ : syracuseStep 4709117 = 1765919) (by norm_num)
theorem B2792189 : Blo 1859631 2792189 := bbase (se 3 (by rfl) ⟨523535, by rfl⟩ : syracuseStep 2792189 = 1047071) (by norm_num)
theorem B4184837 : Blo 1859631 4184837 := bbase (se 4 (by rfl) ⟨392328, by rfl⟩ : syracuseStep 4184837 = 784657) (by norm_num)
theorem B5298965 : Blo 1859631 5298965 := bbase (se 6 (by rfl) ⟨124194, by rfl⟩ : syracuseStep 5298965 = 248389) (by norm_num)
theorem B2792213 : Blo 1859631 2792213 := bbase (se 6 (by rfl) ⟨65442, by rfl⟩ : syracuseStep 2792213 = 130885) (by norm_num)
theorem B2792237 : Blo 1859631 2792237 := bbase (se 3 (by rfl) ⟨523544, by rfl⟩ : syracuseStep 2792237 = 1047089) (by norm_num)
theorem B3824437 : Blo 1859631 3824437 := bbase (se 5 (by rfl) ⟨179270, by rfl⟩ : syracuseStep 3824437 = 358541) (by norm_num)
theorem B2792261 : Blo 1859631 2792261 := bbase (se 4 (by rfl) ⟨261774, by rfl⟩ : syracuseStep 2792261 = 523549) (by norm_num)
theorem B4184909 : Blo 1859631 4184909 := bbase (se 3 (by rfl) ⟨784670, by rfl⟩ : syracuseStep 4184909 = 1569341) (by norm_num)
theorem B2792285 : Blo 1859631 2792285 := bbase (se 3 (by rfl) ⟨523553, by rfl⟩ : syracuseStep 2792285 = 1047107) (by norm_num)
theorem B3824501 : Blo 1859631 3824501 := bbase (se 5 (by rfl) ⟨179273, by rfl⟩ : syracuseStep 3824501 = 358547) (by norm_num)
theorem B2792309 : Blo 1859631 2792309 := bbase (se 5 (by rfl) ⟨130889, by rfl⟩ : syracuseStep 2792309 = 261779) (by norm_num)
theorem B3627917 : Blo 1859631 3627917 := bbase (se 3 (by rfl) ⟨680234, by rfl⟩ : syracuseStep 3627917 = 1360469) (by norm_num)
theorem B2792333 : Blo 1859631 2792333 := bbase (se 3 (by rfl) ⟨523562, by rfl⟩ : syracuseStep 2792333 = 1047125) (by norm_num)
theorem B4184981 : Blo 1859631 4184981 := bbase (se 6 (by rfl) ⟨98085, by rfl⟩ : syracuseStep 4184981 = 196171) (by norm_num)
theorem B2792357 : Blo 1859631 2792357 := bbase (se 4 (by rfl) ⟨261783, by rfl⟩ : syracuseStep 2792357 = 523567) (by norm_num)
theorem B2792381 : Blo 1859631 2792381 := bbase (se 3 (by rfl) ⟨523571, by rfl⟩ : syracuseStep 2792381 = 1047143) (by norm_num)
theorem B3972037 : Blo 1859631 3972037 := bbase (se 4 (by rfl) ⟨372378, by rfl⟩ : syracuseStep 3972037 = 744757) (by norm_num)
theorem B6282197 : Blo 1859631 6282197 := bbase (se 7 (by rfl) ⟨73619, by rfl⟩ : syracuseStep 6282197 = 147239) (by norm_num)
theorem B2792405 : Blo 1859631 2792405 := bbase (se 7 (by rfl) ⟨32723, by rfl⟩ : syracuseStep 2792405 = 65447) (by norm_num)
theorem B4185053 : Blo 1859631 4185053 := bbase (se 3 (by rfl) ⟨784697, by rfl⟩ : syracuseStep 4185053 = 1569395) (by norm_num)
theorem B6364133 : Blo 1859631 6364133 := bbase (se 4 (by rfl) ⟨596637, by rfl⟩ : syracuseStep 6364133 = 1193275) (by norm_num)
theorem B2792429 : Blo 1859631 2792429 := bbase (se 3 (by rfl) ⟨523580, by rfl⟩ : syracuseStep 2792429 = 1047161) (by norm_num)
theorem B4185125 : Blo 1859631 4185125 := bbase (se 4 (by rfl) ⟨392355, by rfl⟩ : syracuseStep 4185125 = 784711) (by norm_num)
theorem B9419813 : Blo 1859631 9419813 := bbase (se 4 (by rfl) ⟨883107, by rfl⟩ : syracuseStep 9419813 = 1766215) (by norm_num)
theorem B4709461 : Blo 1859631 4709461 := bbase (se 8 (by rfl) ⟨27594, by rfl⟩ : syracuseStep 4709461 = 55189) (by norm_num)
theorem B4185197 : Blo 1859631 4185197 := bbase (se 3 (by rfl) ⟨784724, by rfl⟩ : syracuseStep 4185197 = 1569449) (by norm_num)
theorem B2014345 : Blo 1859631 2014345 := bbase (se 2 (by rfl) ⟨755379, by rfl⟩ : syracuseStep 2014345 = 1510759) (by norm_num)
theorem B4185269 : Blo 1859631 4185269 := bbase (se 5 (by rfl) ⟨196184, by rfl⟩ : syracuseStep 4185269 = 392369) (by norm_num)
theorem B4709573 : Blo 1859631 4709573 := bbase (se 4 (by rfl) ⟨441522, by rfl⟩ : syracuseStep 4709573 = 883045) (by norm_num)
theorem B4185341 : Blo 1859631 4185341 := bbase (se 3 (by rfl) ⟨784751, by rfl⟩ : syracuseStep 4185341 = 1569503) (by norm_num)
theorem B2981117 : Blo 1859631 2981117 := bbase (se 3 (by rfl) ⟨558959, by rfl⟩ : syracuseStep 2981117 = 1117919) (by norm_num)
theorem B4185413 : Blo 1859631 4185413 := bbase (se 4 (by rfl) ⟨392382, by rfl⟩ : syracuseStep 4185413 = 784765) (by norm_num)
theorem B2866517 : Blo 1859631 2866517 := bbase (se 11 (by rfl) ⟨2099, by rfl⟩ : syracuseStep 2866517 = 4199) (by norm_num)
theorem B4709765 : Blo 1859631 4709765 := bbase (se 4 (by rfl) ⟨441540, by rfl⟩ : syracuseStep 4709765 = 883081) (by norm_num)
theorem B6282629 : Blo 1859631 6282629 := bbase (se 4 (by rfl) ⟨588996, by rfl⟩ : syracuseStep 6282629 = 1177993) (by norm_num)
theorem B4185485 : Blo 1859631 4185485 := bbase (se 3 (by rfl) ⟨784778, by rfl⟩ : syracuseStep 4185485 = 1569557) (by norm_num)
theorem B2235809 : Blo 1859631 2235809 := bbase (se 2 (by rfl) ⟨838428, by rfl⟩ : syracuseStep 2235809 = 1676857) (by norm_num)
theorem B4185557 : Blo 1859631 4185557 := bbase (se 7 (by rfl) ⟨49049, by rfl⟩ : syracuseStep 4185557 = 98099) (by norm_num)
theorem B4472309 : Blo 1859631 4472309 := bbase (se 5 (by rfl) ⟨209639, by rfl⟩ : syracuseStep 4472309 = 419279) (by norm_num)
theorem B5307925 : Blo 1859631 5307925 := bbase (se 6 (by rfl) ⟨124404, by rfl⟩ : syracuseStep 5307925 = 248809) (by norm_num)
theorem B4185629 : Blo 1859631 4185629 := bbase (se 3 (by rfl) ⟨784805, by rfl⟩ : syracuseStep 4185629 = 1569611) (by norm_num)
theorem B2981405 : Blo 1859631 2981405 := bbase (se 3 (by rfl) ⟨559013, by rfl⟩ : syracuseStep 2981405 = 1118027) (by norm_num)
theorem B2121265 : Blo 1859631 2121265 := bbase (se 2 (by rfl) ⟨795474, by rfl⟩ : syracuseStep 2121265 = 1590949) (by norm_num)
theorem B4185701 : Blo 1859631 4185701 := bbase (se 4 (by rfl) ⟨392409, by rfl⟩ : syracuseStep 4185701 = 784819) (by norm_num)
theorem B2121337 : Blo 1859631 2121337 := bbase (se 2 (by rfl) ⟨795501, by rfl⟩ : syracuseStep 2121337 = 1591003) (by norm_num)
theorem B4185773 : Blo 1859631 4185773 := bbase (se 3 (by rfl) ⟨784832, by rfl⟩ : syracuseStep 4185773 = 1569665) (by norm_num)
theorem B4710109 : Blo 1859631 4710109 := bbase (se 3 (by rfl) ⟨883145, by rfl⟩ : syracuseStep 4710109 = 1766291) (by norm_num)
theorem B4775645 : Blo 1859631 4775645 := bbase (se 3 (by rfl) ⟨895433, by rfl⟩ : syracuseStep 4775645 = 1790867) (by norm_num)
theorem B2236145 : Blo 1859631 2236145 := bbase (se 2 (by rfl) ⟨838554, by rfl⟩ : syracuseStep 2236145 = 1677109) (by norm_num)
theorem B4185845 : Blo 1859631 4185845 := bbase (se 5 (by rfl) ⟨196211, by rfl⟩ : syracuseStep 4185845 = 392423) (by norm_num)
theorem B3972925 : Blo 1859631 3972925 := bbase (se 3 (by rfl) ⟨744923, by rfl⟩ : syracuseStep 3972925 = 1489847) (by norm_num)
theorem B4185917 : Blo 1859631 4185917 := bbase (se 3 (by rfl) ⟨784859, by rfl⟩ : syracuseStep 4185917 = 1569719) (by norm_num)
theorem B4710221 : Blo 1859631 4710221 := bbase (se 3 (by rfl) ⟨883166, by rfl⟩ : syracuseStep 4710221 = 1766333) (by norm_num)
theorem B2121557 : Blo 1859631 2121557 := bbase (se 9 (by rfl) ⟨6215, by rfl⟩ : syracuseStep 2121557 = 12431) (by norm_num)
theorem B2236261 : Blo 1859631 2236261 := bbase (se 4 (by rfl) ⟨209649, by rfl⟩ : syracuseStep 2236261 = 419299) (by norm_num)
theorem B2236285 : Blo 1859631 2236285 := bbase (se 3 (by rfl) ⟨419303, by rfl⟩ : syracuseStep 2236285 = 838607) (by norm_num)
theorem B4185989 : Blo 1859631 4185989 := bbase (se 4 (by rfl) ⟨392436, by rfl⟩ : syracuseStep 4185989 = 784873) (by norm_num)
theorem B5963669 : Blo 1859631 5963669 := bbase (se 6 (by rfl) ⟨139773, by rfl⟩ : syracuseStep 5963669 = 279547) (by norm_num)
theorem B3973045 : Blo 1859631 3973045 := bbase (se 5 (by rfl) ⟨186236, by rfl⟩ : syracuseStep 3973045 = 372473) (by norm_num)
theorem B5300149 : Blo 1859631 5300149 := bbase (se 5 (by rfl) ⟨248444, by rfl⟩ : syracuseStep 5300149 = 496889) (by norm_num)
theorem B2981821 : Blo 1859631 2981821 := bbase (se 3 (by rfl) ⟨559091, by rfl⟩ : syracuseStep 2981821 = 1118183) (by norm_num)
theorem B4186061 : Blo 1859631 4186061 := bbase (se 3 (by rfl) ⟨784886, by rfl⟩ : syracuseStep 4186061 = 1569773) (by norm_num)
theorem B16981973 : Blo 1859631 16981973 := bbase (se 7 (by rfl) ⟨199007, by rfl⟩ : syracuseStep 16981973 = 398015) (by norm_num)
theorem B15081461 : Blo 1859631 15081461 := bbase (se 5 (by rfl) ⟨706943, by rfl⟩ : syracuseStep 15081461 = 1413887) (by norm_num)
theorem B4186115 : Blo 1859631 4186115 := bstep (se 1 (by rfl) ⟨3139586, by rfl⟩ : syracuseStep 4186115 = 6279173) B6279173
theorem B1859635 : Blo 1859631 1859635 := bstep (se 1 (by rfl) ⟨1394726, by rfl⟩ : syracuseStep 1859635 = 2789453) B2789453
theorem B2121779 : Blo 1859631 2121779 := bstep (se 1 (by rfl) ⟨1591334, by rfl⟩ : syracuseStep 2121779 = 3182669) B3182669
theorem B1859651 : Blo 1859631 1859651 := bstep (se 1 (by rfl) ⟨1394738, by rfl⟩ : syracuseStep 1859651 = 2789477) B2789477
theorem B1859667 : Blo 1859631 1859667 := bstep (se 1 (by rfl) ⟨1394750, by rfl⟩ : syracuseStep 1859667 = 2789501) B2789501
theorem B1859683 : Blo 1859631 1859683 := bstep (se 1 (by rfl) ⟨1394762, by rfl⟩ : syracuseStep 1859683 = 2789525) B2789525
theorem B7544945 : Blo 1859631 7544945 := bstep (se 2 (by rfl) ⟨2829354, by rfl⟩ : syracuseStep 7544945 = 5658709) B5658709
theorem B1859699 : Blo 1859631 1859699 := bstep (se 1 (by rfl) ⟨1394774, by rfl⟩ : syracuseStep 1859699 = 2789549) B2789549
theorem B1859715 : Blo 1859631 1859715 := bstep (se 1 (by rfl) ⟨1394786, by rfl⟩ : syracuseStep 1859715 = 2789573) B2789573
theorem B4710545 : Blo 1859631 4710545 := bstep (se 2 (by rfl) ⟨1766454, by rfl⟩ : syracuseStep 4710545 = 3532909) B3532909
theorem B1859731 : Blo 1859631 1859731 := bstep (se 1 (by rfl) ⟨1394798, by rfl⟩ : syracuseStep 1859731 = 2789597) B2789597
theorem B1859747 : Blo 1859631 1859747 := bstep (se 1 (by rfl) ⟨1394810, by rfl⟩ : syracuseStep 1859747 = 2789621) B2789621
theorem B5963939 : Blo 1859631 5963939 := bstep (se 1 (by rfl) ⟨4472954, by rfl⟩ : syracuseStep 5963939 = 8945909) B8945909
theorem B1859763 : Blo 1859631 1859763 := bstep (se 1 (by rfl) ⟨1394822, by rfl⟩ : syracuseStep 1859763 = 2789645) B2789645
theorem B1859779 : Blo 1859631 1859779 := bstep (se 1 (by rfl) ⟨1394834, by rfl⟩ : syracuseStep 1859779 = 2789669) B2789669
theorem B5030083 : Blo 1859631 5030083 := bstep (se 1 (by rfl) ⟨3772562, by rfl⟩ : syracuseStep 5030083 = 7545125) B7545125
theorem B4710595 : Blo 1859631 4710595 := bstep (se 1 (by rfl) ⟨3532946, by rfl⟩ : syracuseStep 4710595 = 7065893) B7065893
theorem B1859795 : Blo 1859631 1859795 := bstep (se 1 (by rfl) ⟨1394846, by rfl⟩ : syracuseStep 1859795 = 2789693) B2789693
theorem B1859811 : Blo 1859631 1859811 := bstep (se 1 (by rfl) ⟨1394858, by rfl⟩ : syracuseStep 1859811 = 2789717) B2789717
theorem B21184739 : Blo 1859631 21184739 := bstep (se 1 (by rfl) ⟨15888554, by rfl⟩ : syracuseStep 21184739 = 31777109) B31777109
theorem B1859827 : Blo 1859631 1859827 := bstep (se 1 (by rfl) ⟨1394870, by rfl⟩ : syracuseStep 1859827 = 2789741) B2789741
theorem B1859843 : Blo 1859631 1859843 := bstep (se 1 (by rfl) ⟨1394882, by rfl⟩ : syracuseStep 1859843 = 2789765) B2789765
theorem B9191693 : Blo 1859631 9191693 := bstep (se 3 (by rfl) ⟨1723442, by rfl⟩ : syracuseStep 9191693 = 3446885) B3446885
theorem B4186385 : Blo 1859631 4186385 := bstep (se 2 (by rfl) ⟨1569894, by rfl⟩ : syracuseStep 4186385 = 3139789) B3139789
theorem B1859859 : Blo 1859631 1859859 := bstep (se 1 (by rfl) ⟨1394894, by rfl⟩ : syracuseStep 1859859 = 2789789) B2789789
theorem B2867489 : Blo 1859631 2867489 := bstep (se 2 (by rfl) ⟨1075308, by rfl⟩ : syracuseStep 2867489 = 2150617) B2150617
theorem B1859875 : Blo 1859631 1859875 := bstep (se 1 (by rfl) ⟨1394906, by rfl⟩ : syracuseStep 1859875 = 2789813) B2789813
theorem B4186403 : Blo 1859631 4186403 := bstep (se 1 (by rfl) ⟨3139802, by rfl⟩ : syracuseStep 4186403 = 6279605) B6279605
theorem B10600753 : Blo 1859631 10600753 := bstep (se 2 (by rfl) ⟨3975282, by rfl⟩ : syracuseStep 10600753 = 7950565) B7950565
theorem B1859891 : Blo 1859631 1859891 := bstep (se 1 (by rfl) ⟨1394918, by rfl⟩ : syracuseStep 1859891 = 2789837) B2789837
theorem B1859907 : Blo 1859631 1859907 := bstep (se 1 (by rfl) ⟨1394930, by rfl⟩ : syracuseStep 1859907 = 2789861) B2789861
theorem B4710737 : Blo 1859631 4710737 := bstep (se 2 (by rfl) ⟨1766526, by rfl⟩ : syracuseStep 4710737 = 3533053) B3533053
theorem B1859923 : Blo 1859631 1859923 := bstep (se 1 (by rfl) ⟨1394942, by rfl⟩ : syracuseStep 1859923 = 2789885) B2789885
theorem B1859939 : Blo 1859631 1859939 := bstep (se 1 (by rfl) ⟨1394954, by rfl⟩ : syracuseStep 1859939 = 2789909) B2789909
theorem B1859955 : Blo 1859631 1859955 := bstep (se 1 (by rfl) ⟨1394966, by rfl⟩ : syracuseStep 1859955 = 2789933) B2789933
theorem B1859971 : Blo 1859631 1859971 := bstep (se 1 (by rfl) ⟨1394978, by rfl⟩ : syracuseStep 1859971 = 2789957) B2789957
theorem B4243843 : Blo 1859631 4243843 := bstep (se 1 (by rfl) ⟨3182882, by rfl⟩ : syracuseStep 4243843 = 6365765) B6365765
theorem B1859987 : Blo 1859631 1859987 := bstep (se 1 (by rfl) ⟨1394990, by rfl⟩ : syracuseStep 1859987 = 2789981) B2789981
theorem B1860003 : Blo 1859631 1860003 := bstep (se 1 (by rfl) ⟨1395002, by rfl⟩ : syracuseStep 1860003 = 2790005) B2790005
theorem B3531185 : Blo 1859631 3531185 := bstep (se 2 (by rfl) ⟨1324194, by rfl⟩ : syracuseStep 3531185 = 2648389) B2648389
theorem B1860019 : Blo 1859631 1860019 := bstep (se 1 (by rfl) ⟨1395014, by rfl⟩ : syracuseStep 1860019 = 2790029) B2790029
theorem B1860035 : Blo 1859631 1860035 := bstep (se 1 (by rfl) ⟨1395026, by rfl⟩ : syracuseStep 1860035 = 2790053) B2790053
theorem B5030353 : Blo 1859631 5030353 := bstep (se 2 (by rfl) ⟨1886382, by rfl⟩ : syracuseStep 5030353 = 3772765) B3772765
theorem B1860051 : Blo 1859631 1860051 := bstep (se 1 (by rfl) ⟨1395038, by rfl⟩ : syracuseStep 1860051 = 2790077) B2790077
theorem B1860067 : Blo 1859631 1860067 := bstep (se 1 (by rfl) ⟨1395050, by rfl⟩ : syracuseStep 1860067 = 2790101) B2790101
theorem B1860083 : Blo 1859631 1860083 := bstep (se 1 (by rfl) ⟨1395062, by rfl⟩ : syracuseStep 1860083 = 2790125) B2790125
theorem B1860099 : Blo 1859631 1860099 := bstep (se 1 (by rfl) ⟨1395074, by rfl⟩ : syracuseStep 1860099 = 2790149) B2790149
theorem B1860115 : Blo 1859631 1860115 := bstep (se 1 (by rfl) ⟨1395086, by rfl⟩ : syracuseStep 1860115 = 2790173) B2790173
theorem B2515475 : Blo 1859631 2515475 := bstep (se 1 (by rfl) ⟨1886606, by rfl⟩ : syracuseStep 2515475 = 3773213) B3773213
theorem B1860131 : Blo 1859631 1860131 := bstep (se 1 (by rfl) ⟨1395098, by rfl⟩ : syracuseStep 1860131 = 2790197) B2790197
theorem B4186673 : Blo 1859631 4186673 := bstep (se 2 (by rfl) ⟨1570002, by rfl⟩ : syracuseStep 4186673 = 3140005) B3140005
theorem B1860147 : Blo 1859631 1860147 := bstep (se 1 (by rfl) ⟨1395110, by rfl⟩ : syracuseStep 1860147 = 2790221) B2790221
theorem B1860163 : Blo 1859631 1860163 := bstep (se 1 (by rfl) ⟨1395122, by rfl⟩ : syracuseStep 1860163 = 2790245) B2790245
theorem B4186691 : Blo 1859631 4186691 := bstep (se 1 (by rfl) ⟨3140018, by rfl⟩ : syracuseStep 4186691 = 6280037) B6280037
theorem B1860179 : Blo 1859631 1860179 := bstep (se 1 (by rfl) ⟨1395134, by rfl⟩ : syracuseStep 1860179 = 2790269) B2790269
theorem B1860195 : Blo 1859631 1860195 := bstep (se 1 (by rfl) ⟨1395146, by rfl⟩ : syracuseStep 1860195 = 2790293) B2790293
theorem B3973745 : Blo 1859631 3973745 := bstep (se 2 (by rfl) ⟨1490154, by rfl⟩ : syracuseStep 3973745 = 2980309) B2980309
theorem B1860211 : Blo 1859631 1860211 := bstep (se 1 (by rfl) ⟨1395158, by rfl⟩ : syracuseStep 1860211 = 2790317) B2790317
theorem B1860227 : Blo 1859631 1860227 := bstep (se 1 (by rfl) ⟨1395170, by rfl⟩ : syracuseStep 1860227 = 2790341) B2790341
theorem B1860243 : Blo 1859631 1860243 := bstep (se 1 (by rfl) ⟨1395182, by rfl⟩ : syracuseStep 1860243 = 2790365) B2790365
theorem B1860259 : Blo 1859631 1860259 := bstep (se 1 (by rfl) ⟨1395194, by rfl⟩ : syracuseStep 1860259 = 2790389) B2790389
theorem B1860275 : Blo 1859631 1860275 := bstep (se 1 (by rfl) ⟨1395206, by rfl⟩ : syracuseStep 1860275 = 2790413) B2790413
theorem B1860291 : Blo 1859631 1860291 := bstep (se 1 (by rfl) ⟨1395218, by rfl⟩ : syracuseStep 1860291 = 2790437) B2790437
theorem B3138257 : Blo 1859631 3138257 := bstep (se 2 (by rfl) ⟨1176846, by rfl⟩ : syracuseStep 3138257 = 2353693) B2353693
theorem B1860307 : Blo 1859631 1860307 := bstep (se 1 (by rfl) ⟨1395230, by rfl⟩ : syracuseStep 1860307 = 2790461) B2790461
theorem B1860323 : Blo 1859631 1860323 := bstep (se 1 (by rfl) ⟨1395242, by rfl⟩ : syracuseStep 1860323 = 2790485) B2790485
theorem B1860339 : Blo 1859631 1860339 := bstep (se 1 (by rfl) ⟨1395254, by rfl⟩ : syracuseStep 1860339 = 2790509) B2790509
theorem B1860355 : Blo 1859631 1860355 := bstep (se 1 (by rfl) ⟨1395266, by rfl⟩ : syracuseStep 1860355 = 2790533) B2790533
theorem B1860371 : Blo 1859631 1860371 := bstep (se 1 (by rfl) ⟨1395278, by rfl⟩ : syracuseStep 1860371 = 2790557) B2790557
theorem B1860387 : Blo 1859631 1860387 := bstep (se 1 (by rfl) ⟨1395290, by rfl⟩ : syracuseStep 1860387 = 2790581) B2790581
theorem B1860403 : Blo 1859631 1860403 := bstep (se 1 (by rfl) ⟨1395302, by rfl⟩ : syracuseStep 1860403 = 2790605) B2790605
theorem B1860419 : Blo 1859631 1860419 := bstep (se 1 (by rfl) ⟨1395314, by rfl⟩ : syracuseStep 1860419 = 2790629) B2790629
theorem B3138385 : Blo 1859631 3138385 := bstep (se 2 (by rfl) ⟨1176894, by rfl⟩ : syracuseStep 3138385 = 2353789) B2353789
theorem B4186961 : Blo 1859631 4186961 := bstep (se 2 (by rfl) ⟨1570110, by rfl⟩ : syracuseStep 4186961 = 3140221) B3140221
theorem B1860435 : Blo 1859631 1860435 := bstep (se 1 (by rfl) ⟨1395326, by rfl⟩ : syracuseStep 1860435 = 2790653) B2790653
theorem B1860451 : Blo 1859631 1860451 := bstep (se 1 (by rfl) ⟨1395338, by rfl⟩ : syracuseStep 1860451 = 2790677) B2790677
theorem B4186979 : Blo 1859631 4186979 := bstep (se 1 (by rfl) ⟨3140234, by rfl⟩ : syracuseStep 4186979 = 6280469) B6280469
theorem B3138419 : Blo 1859631 3138419 := bstep (se 1 (by rfl) ⟨2353814, by rfl⟩ : syracuseStep 3138419 = 4707629) B4707629
theorem B1860467 : Blo 1859631 1860467 := bstep (se 1 (by rfl) ⟨1395350, by rfl⟩ : syracuseStep 1860467 = 2790701) B2790701
theorem B1860483 : Blo 1859631 1860483 := bstep (se 1 (by rfl) ⟨1395362, by rfl⟩ : syracuseStep 1860483 = 2790725) B2790725
theorem B1860499 : Blo 1859631 1860499 := bstep (se 1 (by rfl) ⟨1395374, by rfl⟩ : syracuseStep 1860499 = 2790749) B2790749
theorem B1860515 : Blo 1859631 1860515 := bstep (se 1 (by rfl) ⟨1395386, by rfl⟩ : syracuseStep 1860515 = 2790773) B2790773
theorem B1860531 : Blo 1859631 1860531 := bstep (se 1 (by rfl) ⟨1395398, by rfl⟩ : syracuseStep 1860531 = 2790797) B2790797
theorem B21767093 : Blo 1859631 21767093 := bstep (se 5 (by rfl) ⟨1020332, by rfl⟩ : syracuseStep 21767093 = 2040665) B2040665
theorem B1860547 : Blo 1859631 1860547 := bstep (se 1 (by rfl) ⟨1395410, by rfl⟩ : syracuseStep 1860547 = 2790821) B2790821
theorem B5301197 : Blo 1859631 5301197 := bstep (se 3 (by rfl) ⟨993974, by rfl⟩ : syracuseStep 5301197 = 1987949) B1987949
theorem B1860563 : Blo 1859631 1860563 := bstep (se 1 (by rfl) ⟨1395422, by rfl⟩ : syracuseStep 1860563 = 2790845) B2790845
theorem B1860579 : Blo 1859631 1860579 := bstep (se 1 (by rfl) ⟨1395434, by rfl⟩ : syracuseStep 1860579 = 2790869) B2790869
theorem B3138547 : Blo 1859631 3138547 := bstep (se 1 (by rfl) ⟨2353910, by rfl⟩ : syracuseStep 3138547 = 4707821) B4707821
theorem B1860595 : Blo 1859631 1860595 := bstep (se 1 (by rfl) ⟨1395446, by rfl⟩ : syracuseStep 1860595 = 2790893) B2790893
theorem B1860611 : Blo 1859631 1860611 := bstep (se 1 (by rfl) ⟨1395458, by rfl⟩ : syracuseStep 1860611 = 2790917) B2790917
theorem B23839757 : Blo 1859631 23839757 := bstep (se 3 (by rfl) ⟨4469954, by rfl⟩ : syracuseStep 23839757 = 8939909) B8939909
theorem B1860627 : Blo 1859631 1860627 := bstep (se 1 (by rfl) ⟨1395470, by rfl⟩ : syracuseStep 1860627 = 2790941) B2790941
theorem B1860643 : Blo 1859631 1860643 := bstep (se 1 (by rfl) ⟨1395482, by rfl⟩ : syracuseStep 1860643 = 2790965) B2790965
theorem B1860659 : Blo 1859631 1860659 := bstep (se 1 (by rfl) ⟨1395494, by rfl⟩ : syracuseStep 1860659 = 2790989) B2790989
theorem B1860675 : Blo 1859631 1860675 := bstep (se 1 (by rfl) ⟨1395506, by rfl⟩ : syracuseStep 1860675 = 2791013) B2791013
theorem B10339397 : Blo 1859631 10339397 := bstep (se 4 (by rfl) ⟨969318, by rfl⟩ : syracuseStep 10339397 = 1938637) B1938637
theorem B1860691 : Blo 1859631 1860691 := bstep (se 1 (by rfl) ⟨1395518, by rfl⟩ : syracuseStep 1860691 = 2791037) B2791037
theorem B14124131 : Blo 1859631 14124131 := bstep (se 1 (by rfl) ⟨10593098, by rfl⟩ : syracuseStep 14124131 = 21186197) B21186197
theorem B1860707 : Blo 1859631 1860707 := bstep (se 1 (by rfl) ⟨1395530, by rfl⟩ : syracuseStep 1860707 = 2791061) B2791061
theorem B4187249 : Blo 1859631 4187249 := bstep (se 2 (by rfl) ⟨1570218, by rfl⟩ : syracuseStep 4187249 = 3140437) B3140437
theorem B1860723 : Blo 1859631 1860723 := bstep (se 1 (by rfl) ⟨1395542, by rfl⟩ : syracuseStep 1860723 = 2791085) B2791085
theorem B3138689 : Blo 1859631 3138689 := bstep (se 2 (by rfl) ⟨1177008, by rfl⟩ : syracuseStep 3138689 = 2354017) B2354017
theorem B1860739 : Blo 1859631 1860739 := bstep (se 1 (by rfl) ⟨1395554, by rfl⟩ : syracuseStep 1860739 = 2791109) B2791109
theorem B11920517 : Blo 1859631 11920517 := bstep (se 4 (by rfl) ⟨1117548, by rfl⟩ : syracuseStep 11920517 = 2235097) B2235097
theorem B3974275 : Blo 1859631 3974275 := bstep (se 1 (by rfl) ⟨2980706, by rfl⟩ : syracuseStep 3974275 = 5961413) B5961413
theorem B4187267 : Blo 1859631 4187267 := bstep (se 1 (by rfl) ⟨3140450, by rfl⟩ : syracuseStep 4187267 = 6280901) B6280901
theorem B1860755 : Blo 1859631 1860755 := bstep (se 1 (by rfl) ⟨1395566, by rfl⟩ : syracuseStep 1860755 = 2791133) B2791133
theorem B1860771 : Blo 1859631 1860771 := bstep (se 1 (by rfl) ⟨1395578, by rfl⟩ : syracuseStep 1860771 = 2791157) B2791157
theorem B1860787 : Blo 1859631 1860787 := bstep (se 1 (by rfl) ⟨1395590, by rfl⟩ : syracuseStep 1860787 = 2791181) B2791181
theorem B1860803 : Blo 1859631 1860803 := bstep (se 1 (by rfl) ⟨1395602, by rfl⟩ : syracuseStep 1860803 = 2791205) B2791205
theorem B1860819 : Blo 1859631 1860819 := bstep (se 1 (by rfl) ⟨1395614, by rfl⟩ : syracuseStep 1860819 = 2791229) B2791229
theorem B1860835 : Blo 1859631 1860835 := bstep (se 1 (by rfl) ⟨1395626, by rfl⟩ : syracuseStep 1860835 = 2791253) B2791253
theorem B1860851 : Blo 1859631 1860851 := bstep (se 1 (by rfl) ⟨1395638, by rfl⟩ : syracuseStep 1860851 = 2791277) B2791277
theorem B3138817 : Blo 1859631 3138817 := bstep (se 2 (by rfl) ⟨1177056, by rfl⟩ : syracuseStep 3138817 = 2354113) B2354113
theorem B1860867 : Blo 1859631 1860867 := bstep (se 1 (by rfl) ⟨1395650, by rfl⟩ : syracuseStep 1860867 = 2791301) B2791301
theorem B6276365 : Blo 1859631 6276365 := bstep (se 3 (by rfl) ⟨1176818, by rfl⟩ : syracuseStep 6276365 = 2353637) B2353637
theorem B1860883 : Blo 1859631 1860883 := bstep (se 1 (by rfl) ⟨1395662, by rfl⟩ : syracuseStep 1860883 = 2791325) B2791325
theorem B3138851 : Blo 1859631 3138851 := bstep (se 1 (by rfl) ⟨2354138, by rfl⟩ : syracuseStep 3138851 = 4708277) B4708277
theorem B1860899 : Blo 1859631 1860899 := bstep (se 1 (by rfl) ⟨1395674, by rfl⟩ : syracuseStep 1860899 = 2791349) B2791349
theorem B3532081 : Blo 1859631 3532081 := bstep (se 2 (by rfl) ⟨1324530, by rfl⟩ : syracuseStep 3532081 = 2649061) B2649061
theorem B4711729 : Blo 1859631 4711729 := bstep (se 2 (by rfl) ⟨1766898, by rfl⟩ : syracuseStep 4711729 = 3533797) B3533797
theorem B1860915 : Blo 1859631 1860915 := bstep (se 1 (by rfl) ⟨1395686, by rfl⟩ : syracuseStep 1860915 = 2791373) B2791373
theorem B6276419 : Blo 1859631 6276419 := bstep (se 1 (by rfl) ⟨4707314, by rfl⟩ : syracuseStep 6276419 = 9414629) B9414629
theorem B1860931 : Blo 1859631 1860931 := bstep (se 1 (by rfl) ⟨1395698, by rfl⟩ : syracuseStep 1860931 = 2791397) B2791397
theorem B1885523 : Blo 1859631 1885523 := bstep (se 1 (by rfl) ⟨1414142, by rfl⟩ : syracuseStep 1885523 = 2828285) B2828285
theorem B1860947 : Blo 1859631 1860947 := bstep (se 1 (by rfl) ⟨1395710, by rfl⟩ : syracuseStep 1860947 = 2791421) B2791421
theorem B1860963 : Blo 1859631 1860963 := bstep (se 1 (by rfl) ⟨1395722, by rfl⟩ : syracuseStep 1860963 = 2791445) B2791445
theorem B1860979 : Blo 1859631 1860979 := bstep (se 1 (by rfl) ⟨1395734, by rfl⟩ : syracuseStep 1860979 = 2791469) B2791469
theorem B1860995 : Blo 1859631 1860995 := bstep (se 1 (by rfl) ⟨1395746, by rfl⟩ : syracuseStep 1860995 = 2791493) B2791493
theorem B4187537 : Blo 1859631 4187537 := bstep (se 2 (by rfl) ⟨1570326, by rfl⟩ : syracuseStep 4187537 = 3140653) B3140653
theorem B1861011 : Blo 1859631 1861011 := bstep (se 1 (by rfl) ⟨1395758, by rfl⟩ : syracuseStep 1861011 = 2791517) B2791517
theorem B3138979 : Blo 1859631 3138979 := bstep (se 1 (by rfl) ⟨2354234, by rfl⟩ : syracuseStep 3138979 = 4708469) B4708469
theorem B7062947 : Blo 1859631 7062947 := bstep (se 1 (by rfl) ⟨5297210, by rfl⟩ : syracuseStep 7062947 = 10594421) B10594421
theorem B1861027 : Blo 1859631 1861027 := bstep (se 1 (by rfl) ⟨1395770, by rfl⟩ : syracuseStep 1861027 = 2791541) B2791541
theorem B4187555 : Blo 1859631 4187555 := bstep (se 1 (by rfl) ⟨3140666, by rfl⟩ : syracuseStep 4187555 = 6281333) B6281333
theorem B9422243 : Blo 1859631 9422243 := bstep (se 1 (by rfl) ⟨7066682, by rfl⟩ : syracuseStep 9422243 = 14133365) B14133365
theorem B5096881 : Blo 1859631 5096881 := bstep (se 2 (by rfl) ⟨1911330, by rfl⟩ : syracuseStep 5096881 = 3822661) B3822661
theorem B1861043 : Blo 1859631 1861043 := bstep (se 1 (by rfl) ⟨1395782, by rfl⟩ : syracuseStep 1861043 = 2791565) B2791565
theorem B1861059 : Blo 1859631 1861059 := bstep (se 1 (by rfl) ⟨1395794, by rfl⟩ : syracuseStep 1861059 = 2791589) B2791589
theorem B3532241 : Blo 1859631 3532241 := bstep (se 2 (by rfl) ⟨1324590, by rfl⟩ : syracuseStep 3532241 = 2649181) B2649181
theorem B1861075 : Blo 1859631 1861075 := bstep (se 1 (by rfl) ⟨1395806, by rfl⟩ : syracuseStep 1861075 = 2791613) B2791613
theorem B1861091 : Blo 1859631 1861091 := bstep (se 1 (by rfl) ⟨1395818, by rfl⟩ : syracuseStep 1861091 = 2791637) B2791637
theorem B1861107 : Blo 1859631 1861107 := bstep (se 1 (by rfl) ⟨1395830, by rfl⟩ : syracuseStep 1861107 = 2791661) B2791661
theorem B1861123 : Blo 1859631 1861123 := bstep (se 1 (by rfl) ⟨1395842, by rfl⟩ : syracuseStep 1861123 = 2791685) B2791685
theorem B1861139 : Blo 1859631 1861139 := bstep (se 1 (by rfl) ⟨1395854, by rfl⟩ : syracuseStep 1861139 = 2791709) B2791709
theorem B1861155 : Blo 1859631 1861155 := bstep (se 1 (by rfl) ⟨1395866, by rfl⟩ : syracuseStep 1861155 = 2791733) B2791733
theorem B3139121 : Blo 1859631 3139121 := bstep (se 2 (by rfl) ⟨1177170, by rfl⟩ : syracuseStep 3139121 = 2354341) B2354341
theorem B1861171 : Blo 1859631 1861171 := bstep (se 1 (by rfl) ⟨1395878, by rfl⟩ : syracuseStep 1861171 = 2791757) B2791757
theorem B1861187 : Blo 1859631 1861187 := bstep (se 1 (by rfl) ⟨1395890, by rfl⟩ : syracuseStep 1861187 = 2791781) B2791781
theorem B4712003 : Blo 1859631 4712003 := bstep (se 1 (by rfl) ⟨3534002, by rfl⟩ : syracuseStep 4712003 = 7068005) B7068005
theorem B6276689 : Blo 1859631 6276689 := bstep (se 2 (by rfl) ⟨2353758, by rfl⟩ : syracuseStep 6276689 = 4707517) B4707517
theorem B1861203 : Blo 1859631 1861203 := bstep (se 1 (by rfl) ⟨1395902, by rfl⟩ : syracuseStep 1861203 = 2791805) B2791805
theorem B1861219 : Blo 1859631 1861219 := bstep (se 1 (by rfl) ⟨1395914, by rfl⟩ : syracuseStep 1861219 = 2791829) B2791829
theorem B1861235 : Blo 1859631 1861235 := bstep (se 1 (by rfl) ⟨1395926, by rfl⟩ : syracuseStep 1861235 = 2791853) B2791853
theorem B1861251 : Blo 1859631 1861251 := bstep (se 1 (by rfl) ⟨1395938, by rfl⟩ : syracuseStep 1861251 = 2791877) B2791877
theorem B1861267 : Blo 1859631 1861267 := bstep (se 1 (by rfl) ⟨1395950, by rfl⟩ : syracuseStep 1861267 = 2791901) B2791901
theorem B1861283 : Blo 1859631 1861283 := bstep (se 1 (by rfl) ⟨1395962, by rfl⟩ : syracuseStep 1861283 = 2791925) B2791925
theorem B3139249 : Blo 1859631 3139249 := bstep (se 2 (by rfl) ⟨1177218, by rfl⟩ : syracuseStep 3139249 = 2354437) B2354437
theorem B7947953 : Blo 1859631 7947953 := bstep (se 2 (by rfl) ⟨2980482, by rfl⟩ : syracuseStep 7947953 = 5960965) B5960965
theorem B4187825 : Blo 1859631 4187825 := bstep (se 2 (by rfl) ⟨1570434, by rfl⟩ : syracuseStep 4187825 = 3140869) B3140869
theorem B1861299 : Blo 1859631 1861299 := bstep (se 1 (by rfl) ⟨1395974, by rfl⟩ : syracuseStep 1861299 = 2791949) B2791949
theorem B4187843 : Blo 1859631 4187843 := bstep (se 1 (by rfl) ⟨3140882, by rfl⟩ : syracuseStep 4187843 = 6281765) B6281765
theorem B1861315 : Blo 1859631 1861315 := bstep (se 1 (by rfl) ⟨1395986, by rfl⟩ : syracuseStep 1861315 = 2791973) B2791973
theorem B10593989 : Blo 1859631 10593989 := bstep (se 4 (by rfl) ⟨993186, by rfl⟩ : syracuseStep 10593989 = 1986373) B1986373
theorem B3139283 : Blo 1859631 3139283 := bstep (se 1 (by rfl) ⟨2354462, by rfl⟩ : syracuseStep 3139283 = 4708925) B4708925
theorem B1861331 : Blo 1859631 1861331 := bstep (se 1 (by rfl) ⟨1395998, by rfl⟩ : syracuseStep 1861331 = 2791997) B2791997
theorem B7948003 : Blo 1859631 7948003 := bstep (se 1 (by rfl) ⟨5961002, by rfl⟩ : syracuseStep 7948003 = 11922005) B11922005
theorem B1861347 : Blo 1859631 1861347 := bstep (se 1 (by rfl) ⟨1396010, by rfl⟩ : syracuseStep 1861347 = 2792021) B2792021
theorem B10602211 : Blo 1859631 10602211 := bstep (se 1 (by rfl) ⟨7951658, by rfl⟩ : syracuseStep 10602211 = 15903317) B15903317
theorem B1861363 : Blo 1859631 1861363 := bstep (se 1 (by rfl) ⟨1396022, by rfl⟩ : syracuseStep 1861363 = 2792045) B2792045
theorem B1861379 : Blo 1859631 1861379 := bstep (se 1 (by rfl) ⟨1396034, by rfl⟩ : syracuseStep 1861379 = 2792069) B2792069
theorem B4712195 : Blo 1859631 4712195 := bstep (se 1 (by rfl) ⟨3534146, by rfl⟩ : syracuseStep 4712195 = 7068293) B7068293
theorem B1861395 : Blo 1859631 1861395 := bstep (se 1 (by rfl) ⟨1396046, by rfl⟩ : syracuseStep 1861395 = 2792093) B2792093
theorem B1861411 : Blo 1859631 1861411 := bstep (se 1 (by rfl) ⟨1396058, by rfl⟩ : syracuseStep 1861411 = 2792117) B2792117
theorem B1861427 : Blo 1859631 1861427 := bstep (se 1 (by rfl) ⟨1396070, by rfl⟩ : syracuseStep 1861427 = 2792141) B2792141
theorem B1861443 : Blo 1859631 1861443 := bstep (se 1 (by rfl) ⟨1396082, by rfl⟩ : syracuseStep 1861443 = 2792165) B2792165
theorem B3139411 : Blo 1859631 3139411 := bstep (se 1 (by rfl) ⟨2354558, by rfl⟩ : syracuseStep 3139411 = 4709117) B4709117
theorem B1861459 : Blo 1859631 1861459 := bstep (se 1 (by rfl) ⟨1396094, by rfl⟩ : syracuseStep 1861459 = 2792189) B2792189
theorem B3532643 : Blo 1859631 3532643 := bstep (se 1 (by rfl) ⟨2649482, by rfl⟩ : syracuseStep 3532643 = 5298965) B5298965
theorem B1861475 : Blo 1859631 1861475 := bstep (se 1 (by rfl) ⟨1396106, by rfl⟩ : syracuseStep 1861475 = 2792213) B2792213
theorem B1861491 : Blo 1859631 1861491 := bstep (se 1 (by rfl) ⟨1396118, by rfl⟩ : syracuseStep 1861491 = 2792237) B2792237
theorem B1861507 : Blo 1859631 1861507 := bstep (se 1 (by rfl) ⟨1396130, by rfl⟩ : syracuseStep 1861507 = 2792261) B2792261
theorem B1861523 : Blo 1859631 1861523 := bstep (se 1 (by rfl) ⟨1396142, by rfl⟩ : syracuseStep 1861523 = 2792285) B2792285
theorem B1861539 : Blo 1859631 1861539 := bstep (se 1 (by rfl) ⟨1396154, by rfl⟩ : syracuseStep 1861539 = 2792309) B2792309
theorem B2418611 : Blo 1859631 2418611 := bstep (se 1 (by rfl) ⟨1813958, by rfl⟩ : syracuseStep 2418611 = 3627917) B3627917
theorem B1861555 : Blo 1859631 1861555 := bstep (se 1 (by rfl) ⟨1396166, by rfl⟩ : syracuseStep 1861555 = 2792333) B2792333
theorem B1861571 : Blo 1859631 1861571 := bstep (se 1 (by rfl) ⟨1396178, by rfl⟩ : syracuseStep 1861571 = 2792357) B2792357
theorem B17876933 : Blo 1859631 17876933 := bstep (se 4 (by rfl) ⟨1675962, by rfl⟩ : syracuseStep 17876933 = 3351925) B3351925
theorem B12249037 : Blo 1859631 12249037 := bstep (se 3 (by rfl) ⟨2296694, by rfl⟩ : syracuseStep 12249037 = 4593389) B4593389
theorem B4188113 : Blo 1859631 4188113 := bstep (se 2 (by rfl) ⟨1570542, by rfl⟩ : syracuseStep 4188113 = 3141085) B3141085
theorem B1861587 : Blo 1859631 1861587 := bstep (se 1 (by rfl) ⟨1396190, by rfl⟩ : syracuseStep 1861587 = 2792381) B2792381
theorem B3139553 : Blo 1859631 3139553 := bstep (se 2 (by rfl) ⟨1177332, by rfl⟩ : syracuseStep 3139553 = 2354665) B2354665
theorem B4188131 : Blo 1859631 4188131 := bstep (se 1 (by rfl) ⟨3141098, by rfl⟩ : syracuseStep 4188131 = 6282197) B6282197
theorem B1861603 : Blo 1859631 1861603 := bstep (se 1 (by rfl) ⟨1396202, by rfl⟩ : syracuseStep 1861603 = 2792405) B2792405
theorem B1861619 : Blo 1859631 1861619 := bstep (se 1 (by rfl) ⟨1396214, by rfl⟩ : syracuseStep 1861619 = 2792429) B2792429
theorem B23832629 : Blo 1859631 23832629 := bstep (se 5 (by rfl) ⟨1117154, by rfl⟩ : syracuseStep 23832629 = 2234309) B2234309
theorem B2828353 : Blo 1859631 2828353 := bstep (se 2 (by rfl) ⟨1060632, by rfl⟩ : syracuseStep 2828353 = 2121265) B2121265
theorem B2648161 : Blo 1859631 2648161 := bstep (se 2 (by rfl) ⟨993060, by rfl⟩ : syracuseStep 2648161 = 1986121) B1986121
theorem B3139681 : Blo 1859631 3139681 := bstep (se 2 (by rfl) ⟨1177380, by rfl⟩ : syracuseStep 3139681 = 2354761) B2354761
theorem B6277229 : Blo 1859631 6277229 := bstep (se 3 (by rfl) ⟨1176980, by rfl⟩ : syracuseStep 6277229 = 2353961) B2353961
theorem B3139715 : Blo 1859631 3139715 := bstep (se 1 (by rfl) ⟨2354786, by rfl⟩ : syracuseStep 3139715 = 4709573) B4709573
theorem B2828449 : Blo 1859631 2828449 := bstep (se 2 (by rfl) ⟨1060668, by rfl⟩ : syracuseStep 2828449 = 2121337) B2121337
theorem B6277283 : Blo 1859631 6277283 := bstep (se 1 (by rfl) ⟨4707962, by rfl⟩ : syracuseStep 6277283 = 9415925) B9415925
theorem B9423053 : Blo 1859631 9423053 := bstep (se 3 (by rfl) ⟨1766822, by rfl⟩ : syracuseStep 9423053 = 3533645) B3533645
theorem B1911011 : Blo 1859631 1911011 := bstep (se 1 (by rfl) ⟨1433258, by rfl⟩ : syracuseStep 1911011 = 2866517) B2866517
theorem B4188401 : Blo 1859631 4188401 := bstep (se 2 (by rfl) ⟨1570650, by rfl⟩ : syracuseStep 4188401 = 3141301) B3141301
theorem B3139843 : Blo 1859631 3139843 := bstep (se 1 (by rfl) ⟨2354882, by rfl⟩ : syracuseStep 3139843 = 4709765) B4709765
theorem B4188419 : Blo 1859631 4188419 := bstep (se 1 (by rfl) ⟨3141314, by rfl⟩ : syracuseStep 4188419 = 6282629) B6282629
theorem B3770641 : Blo 1859631 3770641 := bstep (se 2 (by rfl) ⟨1413990, by rfl⟩ : syracuseStep 3770641 = 2827981) B2827981
theorem B7063949 : Blo 1859631 7063949 := bstep (se 3 (by rfl) ⟨1324490, by rfl⟩ : syracuseStep 7063949 = 2648981) B2648981
theorem B3139985 : Blo 1859631 3139985 := bstep (se 2 (by rfl) ⟨1177494, by rfl⟩ : syracuseStep 3139985 = 2354989) B2354989
theorem B6277553 : Blo 1859631 6277553 := bstep (se 2 (by rfl) ⟨2354082, by rfl⟩ : syracuseStep 6277553 = 4708165) B4708165
theorem B6367693 : Blo 1859631 6367693 := bstep (se 3 (by rfl) ⟨1193942, by rfl⟩ : syracuseStep 6367693 = 2387885) B2387885
theorem B3140113 : Blo 1859631 3140113 := bstep (se 2 (by rfl) ⟨1177542, by rfl⟩ : syracuseStep 3140113 = 2355085) B2355085
theorem B3140147 : Blo 1859631 3140147 := bstep (se 1 (by rfl) ⟨2355110, by rfl⟩ : syracuseStep 3140147 = 4710221) B4710221
theorem B3975761 : Blo 1859631 3975761 := bstep (se 2 (by rfl) ⟨1490910, by rfl⟩ : syracuseStep 3975761 = 2981821) B2981821
theorem B3975779 : Blo 1859631 3975779 := bstep (se 1 (by rfl) ⟨2981834, by rfl⟩ : syracuseStep 3975779 = 5963669) B5963669
theorem B10054307 : Blo 1859631 10054307 := bstep (se 1 (by rfl) ⟨7540730, by rfl⟩ : syracuseStep 10054307 = 15081461) B15081461
theorem B4082339 : Blo 1859631 4082339 := bstep (se 1 (by rfl) ⟨3061754, by rfl⟩ : syracuseStep 4082339 = 6123509) B6123509
theorem B6703793 : Blo 1859631 6703793 := bstep (se 2 (by rfl) ⟨2513922, by rfl⟩ : syracuseStep 6703793 = 5027845) B5027845
theorem B3140275 : Blo 1859631 3140275 := bstep (se 1 (by rfl) ⟨2355206, by rfl⟩ : syracuseStep 3140275 = 4710413) B4710413
theorem B9546445 : Blo 1859631 9546445 := bstep (se 3 (by rfl) ⟨1789958, by rfl⟩ : syracuseStep 9546445 = 3579917) B3579917
theorem B3533539 : Blo 1859631 3533539 := bstep (se 1 (by rfl) ⟨2650154, by rfl⟩ : syracuseStep 3533539 = 5300309) B5300309
theorem B2648867 : Blo 1859631 2648867 := bstep (se 1 (by rfl) ⟨1986650, by rfl⟩ : syracuseStep 2648867 = 3973301) B3973301
theorem B3140417 : Blo 1859631 3140417 := bstep (se 2 (by rfl) ⟨1177656, by rfl⟩ : syracuseStep 3140417 = 2355313) B2355313
theorem B5655377 : Blo 1859631 5655377 := bstep (se 2 (by rfl) ⟨2120766, by rfl⟩ : syracuseStep 5655377 = 4241533) B4241533
theorem B2829185 : Blo 1859631 2829185 := bstep (se 2 (by rfl) ⟨1060944, by rfl⟩ : syracuseStep 2829185 = 2121889) B2121889
theorem B3533699 : Blo 1859631 3533699 := bstep (se 1 (by rfl) ⟨2650274, by rfl⟩ : syracuseStep 3533699 = 5300549) B5300549
theorem B9415601 : Blo 1859631 9415601 := bstep (se 2 (by rfl) ⟨3530850, by rfl⟩ : syracuseStep 9415601 = 7061701) B7061701
theorem B3140545 : Blo 1859631 3140545 := bstep (se 2 (by rfl) ⟨1177704, by rfl⟩ : syracuseStep 3140545 = 2355409) B2355409
theorem B6278093 : Blo 1859631 6278093 := bstep (se 3 (by rfl) ⟨1177142, by rfl⟩ : syracuseStep 6278093 = 2354285) B2354285
theorem B32213987 : Blo 1859631 32213987 := bstep (se 1 (by rfl) ⟨24160490, by rfl⟩ : syracuseStep 32213987 = 48320981) B48320981
theorem B3140579 : Blo 1859631 3140579 := bstep (se 1 (by rfl) ⟨2355434, by rfl⟩ : syracuseStep 3140579 = 4710869) B4710869
theorem B12078065 : Blo 1859631 12078065 := bstep (se 2 (by rfl) ⟨4529274, by rfl⟩ : syracuseStep 12078065 = 9058549) B9058549
theorem B2354179 : Blo 1859631 2354179 := bstep (se 1 (by rfl) ⟨1765634, by rfl⟩ : syracuseStep 2354179 = 3531269) B3531269
theorem B6278147 : Blo 1859631 6278147 := bstep (se 1 (by rfl) ⟨4708610, by rfl⟩ : syracuseStep 6278147 = 9417221) B9417221
theorem B2092099 : Blo 1859631 2092099 := bstep (se 1 (by rfl) ⟨1569074, by rfl⟩ : syracuseStep 2092099 = 3138149) B3138149
theorem B2829379 : Blo 1859631 2829379 := bstep (se 1 (by rfl) ⟨2122034, by rfl⟩ : syracuseStep 2829379 = 4244069) B4244069
theorem B2354275 : Blo 1859631 2354275 := bstep (se 1 (by rfl) ⟨1765706, by rfl⟩ : syracuseStep 2354275 = 3531413) B3531413
theorem B3140707 : Blo 1859631 3140707 := bstep (se 1 (by rfl) ⟨2355530, by rfl⟩ : syracuseStep 3140707 = 4711061) B4711061
theorem B2092243 : Blo 1859631 2092243 := bstep (se 1 (by rfl) ⟨1569182, by rfl⟩ : syracuseStep 2092243 = 3138365) B3138365
theorem B3140849 : Blo 1859631 3140849 := bstep (se 2 (by rfl) ⟨1177818, by rfl⟩ : syracuseStep 3140849 = 2355637) B2355637
theorem B6278417 : Blo 1859631 6278417 := bstep (se 2 (by rfl) ⟨2354406, by rfl⟩ : syracuseStep 6278417 = 4708813) B4708813
theorem B48352565 : Blo 1859631 48352565 := bstep (se 5 (by rfl) ⟨2266526, by rfl⟩ : syracuseStep 48352565 = 4533053) B4533053
theorem B2092387 : Blo 1859631 2092387 := bstep (se 1 (by rfl) ⟨1569290, by rfl⟩ : syracuseStep 2092387 = 3138581) B3138581
theorem B3140977 : Blo 1859631 3140977 := bstep (se 2 (by rfl) ⟨1177866, by rfl⟩ : syracuseStep 3140977 = 2355733) B2355733
theorem B3353987 : Blo 1859631 3353987 := bstep (se 1 (by rfl) ⟨2515490, by rfl⟩ : syracuseStep 3353987 = 5030981) B5030981
theorem B3141011 : Blo 1859631 3141011 := bstep (se 1 (by rfl) ⟨2355758, by rfl⟩ : syracuseStep 3141011 = 4711517) B4711517
theorem B2649505 : Blo 1859631 2649505 := bstep (se 2 (by rfl) ⟨993564, by rfl⟩ : syracuseStep 2649505 = 1987129) B1987129
theorem B2829745 : Blo 1859631 2829745 := bstep (se 2 (by rfl) ⟨1061154, by rfl⟩ : syracuseStep 2829745 = 2122309) B2122309
theorem B2092531 : Blo 1859631 2092531 := bstep (se 1 (by rfl) ⟨1569398, by rfl⟩ : syracuseStep 2092531 = 3138797) B3138797
theorem B2649619 : Blo 1859631 2649619 := bstep (se 1 (by rfl) ⟨1987214, by rfl⟩ : syracuseStep 2649619 = 3974429) B3974429
theorem B3141139 : Blo 1859631 3141139 := bstep (se 1 (by rfl) ⟨2355854, by rfl⟩ : syracuseStep 3141139 = 4711709) B4711709
theorem B2354771 : Blo 1859631 2354771 := bstep (se 1 (by rfl) ⟨1766078, by rfl⟩ : syracuseStep 2354771 = 3532157) B3532157
theorem B2092675 : Blo 1859631 2092675 := bstep (se 1 (by rfl) ⟨1569506, by rfl⟩ : syracuseStep 2092675 = 3139013) B3139013
theorem B3141281 : Blo 1859631 3141281 := bstep (se 2 (by rfl) ⟨1177980, by rfl⟩ : syracuseStep 3141281 = 2355961) B2355961
theorem B5099249 : Blo 1859631 5099249 := bstep (se 2 (by rfl) ⟨1912218, by rfl⟩ : syracuseStep 5099249 = 3824437) B3824437
theorem B2092819 : Blo 1859631 2092819 := bstep (se 1 (by rfl) ⟨1569614, by rfl⟩ : syracuseStep 2092819 = 3139229) B3139229
theorem B3141409 : Blo 1859631 3141409 := bstep (se 2 (by rfl) ⟨1178028, by rfl⟩ : syracuseStep 3141409 = 2356057) B2356057
theorem B6278957 : Blo 1859631 6278957 := bstep (se 3 (by rfl) ⟨1177304, by rfl⟩ : syracuseStep 6278957 = 2354609) B2354609
theorem B3141443 : Blo 1859631 3141443 := bstep (se 1 (by rfl) ⟨2356082, by rfl⟩ : syracuseStep 3141443 = 4712165) B4712165
theorem B6279011 : Blo 1859631 6279011 := bstep (se 1 (by rfl) ⟨4709258, by rfl⟩ : syracuseStep 6279011 = 9418517) B9418517
theorem B2092963 : Blo 1859631 2092963 := bstep (se 1 (by rfl) ⟨1569722, by rfl⟩ : syracuseStep 2092963 = 3139445) B3139445
theorem B5296049 : Blo 1859631 5296049 := bstep (se 2 (by rfl) ⟨1986018, by rfl⟩ : syracuseStep 5296049 = 3972037) B3972037
theorem B14135309 : Blo 1859631 14135309 := bstep (se 3 (by rfl) ⟨2650370, by rfl⟩ : syracuseStep 14135309 = 5300741) B5300741
theorem B2093107 : Blo 1859631 2093107 := bstep (se 1 (by rfl) ⟨1569830, by rfl⟩ : syracuseStep 2093107 = 3139661) B3139661
theorem B7950413 : Blo 1859631 7950413 := bstep (se 3 (by rfl) ⟨1490702, by rfl⟩ : syracuseStep 7950413 = 2981405) B2981405
theorem B2789459 : Blo 1859631 2789459 := bstep (se 1 (by rfl) ⟨2092094, by rfl⟩ : syracuseStep 2789459 = 4184189) B4184189
theorem B2789489 : Blo 1859631 2789489 := bstep (se 2 (by rfl) ⟨1046058, by rfl⟩ : syracuseStep 2789489 = 2092117) B2092117
theorem B6279281 : Blo 1859631 6279281 := bstep (se 2 (by rfl) ⟨2354730, by rfl⟩ : syracuseStep 6279281 = 4709461) B4709461
theorem B2789507 : Blo 1859631 2789507 := bstep (se 1 (by rfl) ⟨2092130, by rfl⟩ : syracuseStep 2789507 = 4184261) B4184261
theorem B2789537 : Blo 1859631 2789537 := bstep (se 2 (by rfl) ⟨1046076, by rfl⟩ : syracuseStep 2789537 = 2092153) B2092153
theorem B2789555 : Blo 1859631 2789555 := bstep (se 1 (by rfl) ⟨2092166, by rfl⟩ : syracuseStep 2789555 = 4184333) B4184333
theorem B2093251 : Blo 1859631 2093251 := bstep (se 1 (by rfl) ⟨1569938, by rfl⟩ : syracuseStep 2093251 = 3139877) B3139877
theorem B16109765 : Blo 1859631 16109765 := bstep (se 4 (by rfl) ⟨1510290, by rfl⟩ : syracuseStep 16109765 = 3020581) B3020581
theorem B2789585 : Blo 1859631 2789585 := bstep (se 2 (by rfl) ⟨1046094, by rfl⟩ : syracuseStep 2789585 = 2092189) B2092189
theorem B2789603 : Blo 1859631 2789603 := bstep (se 1 (by rfl) ⟨2092202, by rfl⟩ : syracuseStep 2789603 = 4184405) B4184405
theorem B1986787 : Blo 1859631 1986787 := bstep (se 1 (by rfl) ⟨1490090, by rfl⟩ : syracuseStep 1986787 = 2980181) B2980181
theorem B2789633 : Blo 1859631 2789633 := bstep (se 2 (by rfl) ⟨1046112, by rfl⟩ : syracuseStep 2789633 = 2092225) B2092225
theorem B2789651 : Blo 1859631 2789651 := bstep (se 1 (by rfl) ⟨2092238, by rfl⟩ : syracuseStep 2789651 = 4184477) B4184477
theorem B2355475 : Blo 1859631 2355475 := bstep (se 1 (by rfl) ⟨1766606, by rfl⟩ : syracuseStep 2355475 = 3533213) B3533213
theorem B2789681 : Blo 1859631 2789681 := bstep (se 2 (by rfl) ⟨1046130, by rfl⟩ : syracuseStep 2789681 = 2092261) B2092261
theorem B4469041 : Blo 1859631 4469041 := bstep (se 2 (by rfl) ⟨1675890, by rfl⟩ : syracuseStep 4469041 = 3351781) B3351781
theorem B2789699 : Blo 1859631 2789699 := bstep (se 1 (by rfl) ⟨2092274, by rfl⟩ : syracuseStep 2789699 = 4184549) B4184549
theorem B8163661 : Blo 1859631 8163661 := bstep (se 3 (by rfl) ⟨1530686, by rfl⟩ : syracuseStep 8163661 = 3061373) B3061373
theorem B2093395 : Blo 1859631 2093395 := bstep (se 1 (by rfl) ⟨1570046, by rfl⟩ : syracuseStep 2093395 = 3140093) B3140093
theorem B2789729 : Blo 1859631 2789729 := bstep (se 2 (by rfl) ⟨1046148, by rfl⟩ : syracuseStep 2789729 = 2092297) B2092297
theorem B9417059 : Blo 1859631 9417059 := bstep (se 1 (by rfl) ⟨7062794, by rfl⟩ : syracuseStep 9417059 = 14125589) B14125589
theorem B2789747 : Blo 1859631 2789747 := bstep (se 1 (by rfl) ⟨2092310, by rfl⟩ : syracuseStep 2789747 = 4184621) B4184621
theorem B2355571 : Blo 1859631 2355571 := bstep (se 1 (by rfl) ⟨1766678, by rfl⟩ : syracuseStep 2355571 = 3533357) B3533357
theorem B2789777 : Blo 1859631 2789777 := bstep (se 2 (by rfl) ⟨1046166, by rfl⟩ : syracuseStep 2789777 = 2092333) B2092333
theorem B5960081 : Blo 1859631 5960081 := bstep (se 2 (by rfl) ⟨2235030, by rfl⟩ : syracuseStep 5960081 = 4470061) B4470061
theorem B2789795 : Blo 1859631 2789795 := bstep (se 1 (by rfl) ⟨2092346, by rfl⟩ : syracuseStep 2789795 = 4184693) B4184693
theorem B2789825 : Blo 1859631 2789825 := bstep (se 2 (by rfl) ⟨1046184, by rfl⟩ : syracuseStep 2789825 = 2092369) B2092369
theorem B7066061 : Blo 1859631 7066061 := bstep (se 3 (by rfl) ⟨1324886, by rfl⟩ : syracuseStep 7066061 = 2649773) B2649773
theorem B2789843 : Blo 1859631 2789843 := bstep (se 1 (by rfl) ⟨2092382, by rfl⟩ : syracuseStep 2789843 = 4184765) B4184765
theorem B2093539 : Blo 1859631 2093539 := bstep (se 1 (by rfl) ⟨1570154, by rfl⟩ : syracuseStep 2093539 = 3140309) B3140309
theorem B2789873 : Blo 1859631 2789873 := bstep (se 2 (by rfl) ⟨1046202, by rfl⟩ : syracuseStep 2789873 = 2092405) B2092405
theorem B2789891 : Blo 1859631 2789891 := bstep (se 1 (by rfl) ⟨2092418, by rfl⟩ : syracuseStep 2789891 = 4184837) B4184837
theorem B2789921 : Blo 1859631 2789921 := bstep (se 2 (by rfl) ⟨1046220, by rfl⟩ : syracuseStep 2789921 = 2092441) B2092441
theorem B11924003 : Blo 1859631 11924003 := bstep (se 1 (by rfl) ⟨8943002, by rfl⟩ : syracuseStep 11924003 = 17886005) B17886005
theorem B2789939 : Blo 1859631 2789939 := bstep (se 1 (by rfl) ⟨2092454, by rfl⟩ : syracuseStep 2789939 = 4184909) B4184909
theorem B12735053 : Blo 1859631 12735053 := bstep (se 3 (by rfl) ⟨2387822, by rfl⟩ : syracuseStep 12735053 = 4775645) B4775645
theorem B2789969 : Blo 1859631 2789969 := bstep (se 2 (by rfl) ⟨1046238, by rfl⟩ : syracuseStep 2789969 = 2092477) B2092477
theorem B2789987 : Blo 1859631 2789987 := bstep (se 1 (by rfl) ⟨2092490, by rfl⟩ : syracuseStep 2789987 = 4184981) B4184981
theorem B2093683 : Blo 1859631 2093683 := bstep (se 1 (by rfl) ⟨1570262, by rfl⟩ : syracuseStep 2093683 = 3140525) B3140525
theorem B2790017 : Blo 1859631 2790017 := bstep (se 2 (by rfl) ⟨1046256, by rfl⟩ : syracuseStep 2790017 = 2092513) B2092513
theorem B6279821 : Blo 1859631 6279821 := bstep (se 3 (by rfl) ⟨1177466, by rfl⟩ : syracuseStep 6279821 = 2354933) B2354933
theorem B2790035 : Blo 1859631 2790035 := bstep (se 1 (by rfl) ⟨2092526, by rfl⟩ : syracuseStep 2790035 = 4185053) B4185053
theorem B2790065 : Blo 1859631 2790065 := bstep (se 2 (by rfl) ⟨1046274, by rfl⟩ : syracuseStep 2790065 = 2092549) B2092549
theorem B2790083 : Blo 1859631 2790083 := bstep (se 1 (by rfl) ⟨2092562, by rfl⟩ : syracuseStep 2790083 = 4185125) B4185125
theorem B6279875 : Blo 1859631 6279875 := bstep (se 1 (by rfl) ⟨4709906, by rfl⟩ : syracuseStep 6279875 = 9419813) B9419813
theorem B30601925 : Blo 1859631 30601925 := bstep (se 4 (by rfl) ⟨2868930, by rfl⟩ : syracuseStep 30601925 = 5737861) B5737861
theorem B2790113 : Blo 1859631 2790113 := bstep (se 2 (by rfl) ⟨1046292, by rfl⟩ : syracuseStep 2790113 = 2092585) B2092585
theorem B2790131 : Blo 1859631 2790131 := bstep (se 1 (by rfl) ⟨2092598, by rfl⟩ : syracuseStep 2790131 = 4185197) B4185197
theorem B2093827 : Blo 1859631 2093827 := bstep (se 1 (by rfl) ⟨1570370, by rfl⟩ : syracuseStep 2093827 = 3140741) B3140741
theorem B2790161 : Blo 1859631 2790161 := bstep (se 2 (by rfl) ⟨1046310, by rfl⟩ : syracuseStep 2790161 = 2092621) B2092621
theorem B2790179 : Blo 1859631 2790179 := bstep (se 1 (by rfl) ⟨2092634, by rfl⟩ : syracuseStep 2790179 = 4185269) B4185269
theorem B2790209 : Blo 1859631 2790209 := bstep (se 2 (by rfl) ⟨1046328, by rfl⟩ : syracuseStep 2790209 = 2092657) B2092657
theorem B2790227 : Blo 1859631 2790227 := bstep (se 1 (by rfl) ⟨2092670, by rfl⟩ : syracuseStep 2790227 = 4185341) B4185341
theorem B1987411 : Blo 1859631 1987411 := bstep (se 1 (by rfl) ⟨1490558, by rfl⟩ : syracuseStep 1987411 = 2981117) B2981117
theorem B2356067 : Blo 1859631 2356067 := bstep (se 1 (by rfl) ⟨1767050, by rfl⟩ : syracuseStep 2356067 = 3534101) B3534101
theorem B5297005 : Blo 1859631 5297005 := bstep (se 3 (by rfl) ⟨993188, by rfl⟩ : syracuseStep 5297005 = 1986377) B1986377
theorem B2790257 : Blo 1859631 2790257 := bstep (se 2 (by rfl) ⟨1046346, by rfl⟩ : syracuseStep 2790257 = 2092693) B2092693
theorem B2790275 : Blo 1859631 2790275 := bstep (se 1 (by rfl) ⟨2092706, by rfl⟩ : syracuseStep 2790275 = 4185413) B4185413
theorem B5657485 : Blo 1859631 5657485 := bstep (se 3 (by rfl) ⟨1060778, by rfl⟩ : syracuseStep 5657485 = 2121557) B2121557
theorem B2093971 : Blo 1859631 2093971 := bstep (se 1 (by rfl) ⟨1570478, by rfl⟩ : syracuseStep 2093971 = 3140957) B3140957
theorem B2790305 : Blo 1859631 2790305 := bstep (se 2 (by rfl) ⟨1046364, by rfl⟩ : syracuseStep 2790305 = 2092729) B2092729
theorem B2790323 : Blo 1859631 2790323 := bstep (se 1 (by rfl) ⟨2092742, by rfl⟩ : syracuseStep 2790323 = 4185485) B4185485
theorem B2790353 : Blo 1859631 2790353 := bstep (se 2 (by rfl) ⟨1046382, by rfl⟩ : syracuseStep 2790353 = 2092765) B2092765
theorem B6280145 : Blo 1859631 6280145 := bstep (se 2 (by rfl) ⟨2355054, by rfl⟩ : syracuseStep 6280145 = 4710109) B4710109
theorem B2790371 : Blo 1859631 2790371 := bstep (se 1 (by rfl) ⟨2092778, by rfl⟩ : syracuseStep 2790371 = 4185557) B4185557
theorem B2790401 : Blo 1859631 2790401 := bstep (se 2 (by rfl) ⟨1046400, by rfl⟩ : syracuseStep 2790401 = 2092801) B2092801
theorem B2790419 : Blo 1859631 2790419 := bstep (se 1 (by rfl) ⟨2092814, by rfl⟩ : syracuseStep 2790419 = 4185629) B4185629
theorem B2094115 : Blo 1859631 2094115 := bstep (se 1 (by rfl) ⟨1570586, by rfl⟩ : syracuseStep 2094115 = 3141173) B3141173
theorem B2790449 : Blo 1859631 2790449 := bstep (se 2 (by rfl) ⟨1046418, by rfl⟩ : syracuseStep 2790449 = 2092837) B2092837
theorem B2790467 : Blo 1859631 2790467 := bstep (se 1 (by rfl) ⟨2092850, by rfl⟩ : syracuseStep 2790467 = 4185701) B4185701
theorem B5297233 : Blo 1859631 5297233 := bstep (se 2 (by rfl) ⟨1986462, by rfl⟩ : syracuseStep 5297233 = 3972925) B3972925
theorem B2978899 : Blo 1859631 2978899 := bstep (se 1 (by rfl) ⟨2234174, by rfl⟩ : syracuseStep 2978899 = 4468349) B4468349
theorem B2790497 : Blo 1859631 2790497 := bstep (se 2 (by rfl) ⟨1046436, by rfl⟩ : syracuseStep 2790497 = 2092873) B2092873
theorem B2790515 : Blo 1859631 2790515 := bstep (se 1 (by rfl) ⟨2092886, by rfl⟩ : syracuseStep 2790515 = 4185773) B4185773
theorem B2978945 : Blo 1859631 2978945 := bstep (se 2 (by rfl) ⟨1117104, by rfl⟩ : syracuseStep 2978945 = 2234209) B2234209
theorem B9417869 : Blo 1859631 9417869 := bstep (se 3 (by rfl) ⟨1765850, by rfl⟩ : syracuseStep 9417869 = 3531701) B3531701
theorem B2790545 : Blo 1859631 2790545 := bstep (se 2 (by rfl) ⟨1046454, by rfl⟩ : syracuseStep 2790545 = 2092909) B2092909
theorem B5026979 : Blo 1859631 5026979 := bstep (se 1 (by rfl) ⟨3770234, by rfl⟩ : syracuseStep 5026979 = 7540469) B7540469
theorem B2790563 : Blo 1859631 2790563 := bstep (se 1 (by rfl) ⟨2092922, by rfl⟩ : syracuseStep 2790563 = 4185845) B4185845
theorem B2094259 : Blo 1859631 2094259 := bstep (se 1 (by rfl) ⟨1570694, by rfl⟩ : syracuseStep 2094259 = 3141389) B3141389
theorem B2790593 : Blo 1859631 2790593 := bstep (se 2 (by rfl) ⟨1046472, by rfl⟩ : syracuseStep 2790593 = 2092945) B2092945
theorem B2790611 : Blo 1859631 2790611 := bstep (se 1 (by rfl) ⟨2092958, by rfl⟩ : syracuseStep 2790611 = 4185917) B4185917
theorem B5297393 : Blo 1859631 5297393 := bstep (se 2 (by rfl) ⟨1986522, by rfl⟩ : syracuseStep 5297393 = 3973045) B3973045
theorem B2790641 : Blo 1859631 2790641 := bstep (se 2 (by rfl) ⟨1046490, by rfl⟩ : syracuseStep 2790641 = 2092981) B2092981
theorem B7066865 : Blo 1859631 7066865 := bstep (se 2 (by rfl) ⟨2650074, by rfl⟩ : syracuseStep 7066865 = 5300149) B5300149
theorem B2790659 : Blo 1859631 2790659 := bstep (se 1 (by rfl) ⟨2092994, by rfl⟩ : syracuseStep 2790659 = 4185989) B4185989
theorem B2790689 : Blo 1859631 2790689 := bstep (se 2 (by rfl) ⟨1046508, by rfl⟩ : syracuseStep 2790689 = 2093017) B2093017
theorem B2790707 : Blo 1859631 2790707 := bstep (se 1 (by rfl) ⟨2093030, by rfl⟩ : syracuseStep 2790707 = 4186061) B4186061
theorem B2790737 : Blo 1859631 2790737 := bstep (se 2 (by rfl) ⟨1046526, by rfl⟩ : syracuseStep 2790737 = 2093053) B2093053
theorem B5297507 : Blo 1859631 5297507 := bstep (se 1 (by rfl) ⟨3973130, by rfl⟩ : syracuseStep 5297507 = 7946261) B7946261
theorem B2790755 : Blo 1859631 2790755 := bstep (se 1 (by rfl) ⟨2093066, by rfl⟩ : syracuseStep 2790755 = 4186133) B4186133
theorem B2790785 : Blo 1859631 2790785 := bstep (se 2 (by rfl) ⟨1046544, by rfl⟩ : syracuseStep 2790785 = 2093089) B2093089
theorem B7460237 : Blo 1859631 7460237 := bstep (se 3 (by rfl) ⟨1398794, by rfl⟩ : syracuseStep 7460237 = 2797589) B2797589
theorem B2790803 : Blo 1859631 2790803 := bstep (se 1 (by rfl) ⟨2093102, by rfl⟩ : syracuseStep 2790803 = 4186205) B4186205
theorem B2790833 : Blo 1859631 2790833 := bstep (se 2 (by rfl) ⟨1046562, by rfl⟩ : syracuseStep 2790833 = 2093125) B2093125
theorem B2790851 : Blo 1859631 2790851 := bstep (se 1 (by rfl) ⟨2093138, by rfl⟩ : syracuseStep 2790851 = 4186277) B4186277
theorem B7943629 : Blo 1859631 7943629 := bstep (se 3 (by rfl) ⟨1489430, by rfl⟩ : syracuseStep 7943629 = 2978861) B2978861
theorem B10597837 : Blo 1859631 10597837 := bstep (se 3 (by rfl) ⟨1987094, by rfl⟩ : syracuseStep 10597837 = 3974189) B3974189
theorem B2790881 : Blo 1859631 2790881 := bstep (se 2 (by rfl) ⟨1046580, by rfl⟩ : syracuseStep 2790881 = 2093161) B2093161
theorem B17880547 : Blo 1859631 17880547 := bstep (se 1 (by rfl) ⟨13410410, by rfl⟩ : syracuseStep 17880547 = 26820821) B26820821
theorem B23852515 : Blo 1859631 23852515 := bstep (se 1 (by rfl) ⟨17889386, by rfl⟩ : syracuseStep 23852515 = 35778773) B35778773
theorem B6280685 : Blo 1859631 6280685 := bstep (se 3 (by rfl) ⟨1177628, by rfl⟩ : syracuseStep 6280685 = 2355257) B2355257
theorem B2790899 : Blo 1859631 2790899 := bstep (se 1 (by rfl) ⟨2093174, by rfl⟩ : syracuseStep 2790899 = 4186349) B4186349
theorem B10057229 : Blo 1859631 10057229 := bstep (se 3 (by rfl) ⟨1885730, by rfl⟩ : syracuseStep 10057229 = 3771461) B3771461
theorem B2790929 : Blo 1859631 2790929 := bstep (se 2 (by rfl) ⟨1046598, by rfl⟩ : syracuseStep 2790929 = 2093197) B2093197
theorem B3184147 : Blo 1859631 3184147 := bstep (se 1 (by rfl) ⟨2388110, by rfl⟩ : syracuseStep 3184147 = 4776221) B4776221
theorem B2684449 : Blo 1859631 2684449 := bstep (se 2 (by rfl) ⟨1006668, by rfl⟩ : syracuseStep 2684449 = 2013337) B2013337
theorem B2790947 : Blo 1859631 2790947 := bstep (se 1 (by rfl) ⟨2093210, by rfl⟩ : syracuseStep 2790947 = 4186421) B4186421
theorem B6280739 : Blo 1859631 6280739 := bstep (se 1 (by rfl) ⟨4710554, by rfl⟩ : syracuseStep 6280739 = 9421109) B9421109
theorem B2790977 : Blo 1859631 2790977 := bstep (se 2 (by rfl) ⟨1046616, by rfl⟩ : syracuseStep 2790977 = 2093233) B2093233
theorem B2790995 : Blo 1859631 2790995 := bstep (se 1 (by rfl) ⟨2093246, by rfl⟩ : syracuseStep 2790995 = 4186493) B4186493
theorem B4707953 : Blo 1859631 4707953 := bstep (se 2 (by rfl) ⟨1765482, by rfl⟩ : syracuseStep 4707953 = 3530965) B3530965
theorem B2791025 : Blo 1859631 2791025 := bstep (se 2 (by rfl) ⟨1046634, by rfl⟩ : syracuseStep 2791025 = 2093269) B2093269
theorem B2791043 : Blo 1859631 2791043 := bstep (se 1 (by rfl) ⟨2093282, by rfl⟩ : syracuseStep 2791043 = 4186565) B4186565
theorem B2791073 : Blo 1859631 2791073 := bstep (se 2 (by rfl) ⟨1046652, by rfl⟩ : syracuseStep 2791073 = 2093305) B2093305
theorem B4708003 : Blo 1859631 4708003 := bstep (se 1 (by rfl) ⟨3531002, by rfl⟩ : syracuseStep 4708003 = 7062005) B7062005
theorem B2791091 : Blo 1859631 2791091 := bstep (se 1 (by rfl) ⟨2093318, by rfl⟩ : syracuseStep 2791091 = 4186637) B4186637
theorem B8165069 : Blo 1859631 8165069 := bstep (se 3 (by rfl) ⟨1530950, by rfl⟩ : syracuseStep 8165069 = 3061901) B3061901
theorem B2791121 : Blo 1859631 2791121 := bstep (se 2 (by rfl) ⟨1046670, by rfl⟩ : syracuseStep 2791121 = 2093341) B2093341
theorem B2791139 : Blo 1859631 2791139 := bstep (se 1 (by rfl) ⟨2093354, by rfl⟩ : syracuseStep 2791139 = 4186709) B4186709
theorem B2791169 : Blo 1859631 2791169 := bstep (se 2 (by rfl) ⟨1046688, by rfl⟩ : syracuseStep 2791169 = 2093377) B2093377
theorem B2791187 : Blo 1859631 2791187 := bstep (se 1 (by rfl) ⟨2093390, by rfl⟩ : syracuseStep 2791187 = 4186781) B4186781
theorem B4708145 : Blo 1859631 4708145 := bstep (se 2 (by rfl) ⟨1765554, by rfl⟩ : syracuseStep 4708145 = 3531109) B3531109
theorem B2791217 : Blo 1859631 2791217 := bstep (se 2 (by rfl) ⟨1046706, by rfl⟩ : syracuseStep 2791217 = 2093413) B2093413
theorem B6281009 : Blo 1859631 6281009 := bstep (se 2 (by rfl) ⟨2355378, by rfl⟩ : syracuseStep 6281009 = 4710757) B4710757
theorem B2791235 : Blo 1859631 2791235 := bstep (se 1 (by rfl) ⟨2093426, by rfl⟩ : syracuseStep 2791235 = 4186853) B4186853
theorem B2791265 : Blo 1859631 2791265 := bstep (se 2 (by rfl) ⟨1046724, by rfl⟩ : syracuseStep 2791265 = 2093449) B2093449
theorem B2791283 : Blo 1859631 2791283 := bstep (se 1 (by rfl) ⟨2093462, by rfl⟩ : syracuseStep 2791283 = 4186925) B4186925
theorem B30160781 : Blo 1859631 30160781 := bstep (se 3 (by rfl) ⟨5655146, by rfl⟩ : syracuseStep 30160781 = 11310293) B11310293
theorem B7067533 : Blo 1859631 7067533 := bstep (se 3 (by rfl) ⟨1325162, by rfl⟩ : syracuseStep 7067533 = 2650325) B2650325
theorem B2791313 : Blo 1859631 2791313 := bstep (se 2 (by rfl) ⟨1046742, by rfl⟩ : syracuseStep 2791313 = 2093485) B2093485
theorem B2791331 : Blo 1859631 2791331 := bstep (se 1 (by rfl) ⟨2093498, by rfl⟩ : syracuseStep 2791331 = 4186997) B4186997
theorem B2791361 : Blo 1859631 2791361 := bstep (se 2 (by rfl) ⟨1046760, by rfl⟩ : syracuseStep 2791361 = 2093521) B2093521
theorem B2791379 : Blo 1859631 2791379 := bstep (se 1 (by rfl) ⟨2093534, by rfl⟩ : syracuseStep 2791379 = 4187069) B4187069
theorem B2791409 : Blo 1859631 2791409 := bstep (se 2 (by rfl) ⟨1046778, by rfl⟩ : syracuseStep 2791409 = 2093557) B2093557
theorem B2791427 : Blo 1859631 2791427 := bstep (se 1 (by rfl) ⟨2093570, by rfl⟩ : syracuseStep 2791427 = 4187141) B4187141
theorem B2791457 : Blo 1859631 2791457 := bstep (se 2 (by rfl) ⟨1046796, by rfl⟩ : syracuseStep 2791457 = 2093593) B2093593
theorem B2791475 : Blo 1859631 2791475 := bstep (se 1 (by rfl) ⟨2093606, by rfl⟩ : syracuseStep 2791475 = 4187213) B4187213
theorem B2791505 : Blo 1859631 2791505 := bstep (se 2 (by rfl) ⟨1046814, by rfl⟩ : syracuseStep 2791505 = 2093629) B2093629
theorem B2791523 : Blo 1859631 2791523 := bstep (se 1 (by rfl) ⟨2093642, by rfl⟩ : syracuseStep 2791523 = 4187285) B4187285
theorem B2791553 : Blo 1859631 2791553 := bstep (se 2 (by rfl) ⟨1046832, by rfl⟩ : syracuseStep 2791553 = 2093665) B2093665
theorem B2791571 : Blo 1859631 2791571 := bstep (se 1 (by rfl) ⟨2093678, by rfl⟩ : syracuseStep 2791571 = 4187357) B4187357
theorem B11311267 : Blo 1859631 11311267 := bstep (se 1 (by rfl) ⟨8483450, by rfl⟩ : syracuseStep 11311267 = 16966901) B16966901
theorem B2791601 : Blo 1859631 2791601 := bstep (se 2 (by rfl) ⟨1046850, by rfl⟩ : syracuseStep 2791601 = 2093701) B2093701
theorem B2791619 : Blo 1859631 2791619 := bstep (se 1 (by rfl) ⟨2093714, by rfl⟩ : syracuseStep 2791619 = 4187429) B4187429
theorem B2791649 : Blo 1859631 2791649 := bstep (se 2 (by rfl) ⟨1046868, by rfl⟩ : syracuseStep 2791649 = 2093737) B2093737
theorem B2791667 : Blo 1859631 2791667 := bstep (se 1 (by rfl) ⟨2093750, by rfl⟩ : syracuseStep 2791667 = 4187501) B4187501
theorem B2791697 : Blo 1859631 2791697 := bstep (se 2 (by rfl) ⟨1046886, by rfl⟩ : syracuseStep 2791697 = 2093773) B2093773
theorem B2791715 : Blo 1859631 2791715 := bstep (se 1 (by rfl) ⟨2093786, by rfl⟩ : syracuseStep 2791715 = 4187573) B4187573
theorem B4184369 : Blo 1859631 4184369 := bstep (se 2 (by rfl) ⟨1569138, by rfl⟩ : syracuseStep 4184369 = 3138277) B3138277
theorem B2791745 : Blo 1859631 2791745 := bstep (se 2 (by rfl) ⟨1046904, by rfl⟩ : syracuseStep 2791745 = 2093809) B2093809
theorem B4184387 : Blo 1859631 4184387 := bstep (se 1 (by rfl) ⟨3138290, by rfl⟩ : syracuseStep 4184387 = 6276581) B6276581
theorem B14129477 : Blo 1859631 14129477 := bstep (se 4 (by rfl) ⟨1324638, by rfl⟩ : syracuseStep 14129477 = 2649277) B2649277
theorem B5298509 : Blo 1859631 5298509 := bstep (se 3 (by rfl) ⟨993470, by rfl⟩ : syracuseStep 5298509 = 1986941) B1986941
theorem B6281549 : Blo 1859631 6281549 := bstep (se 3 (by rfl) ⟨1177790, by rfl⟩ : syracuseStep 6281549 = 2355581) B2355581
theorem B2791763 : Blo 1859631 2791763 := bstep (se 1 (by rfl) ⟨2093822, by rfl⟩ : syracuseStep 2791763 = 4187645) B4187645
theorem B5658979 : Blo 1859631 5658979 := bstep (se 1 (by rfl) ⟨4244234, by rfl⟩ : syracuseStep 5658979 = 8488469) B8488469
theorem B2791793 : Blo 1859631 2791793 := bstep (se 2 (by rfl) ⟨1046922, by rfl⟩ : syracuseStep 2791793 = 2093845) B2093845
theorem B2791811 : Blo 1859631 2791811 := bstep (se 1 (by rfl) ⟨2093858, by rfl⟩ : syracuseStep 2791811 = 4187717) B4187717
theorem B6281603 : Blo 1859631 6281603 := bstep (se 1 (by rfl) ⟨4711202, by rfl⟩ : syracuseStep 6281603 = 9422405) B9422405
theorem B2791841 : Blo 1859631 2791841 := bstep (se 2 (by rfl) ⟨1046940, by rfl⟩ : syracuseStep 2791841 = 2093881) B2093881
theorem B5962157 : Blo 1859631 5962157 := bstep (se 3 (by rfl) ⟨1117904, by rfl⟩ : syracuseStep 5962157 = 2235809) B2235809
theorem B2791859 : Blo 1859631 2791859 := bstep (se 1 (by rfl) ⟨2093894, by rfl⟩ : syracuseStep 2791859 = 4187789) B4187789
theorem B5659075 : Blo 1859631 5659075 := bstep (se 1 (by rfl) ⟨4244306, by rfl⟩ : syracuseStep 5659075 = 8488613) B8488613
theorem B2791889 : Blo 1859631 2791889 := bstep (se 2 (by rfl) ⟨1046958, by rfl⟩ : syracuseStep 2791889 = 2093917) B2093917
theorem B2791907 : Blo 1859631 2791907 := bstep (se 1 (by rfl) ⟨2093930, by rfl⟩ : syracuseStep 2791907 = 4187861) B4187861
theorem B2791937 : Blo 1859631 2791937 := bstep (se 2 (by rfl) ⟨1046976, by rfl⟩ : syracuseStep 2791937 = 2093953) B2093953
theorem B5298691 : Blo 1859631 5298691 := bstep (se 1 (by rfl) ⟨3974018, by rfl⟩ : syracuseStep 5298691 = 7948037) B7948037
theorem B2791955 : Blo 1859631 2791955 := bstep (se 1 (by rfl) ⟨2093966, by rfl⟩ : syracuseStep 2791955 = 4187933) B4187933
theorem B9812515 : Blo 1859631 9812515 := bstep (se 1 (by rfl) ⟨7359386, by rfl⟩ : syracuseStep 9812515 = 14718773) B14718773
theorem B2791985 : Blo 1859631 2791985 := bstep (se 2 (by rfl) ⟨1046994, by rfl⟩ : syracuseStep 2791985 = 2093989) B2093989
theorem B2792003 : Blo 1859631 2792003 := bstep (se 1 (by rfl) ⟨2094002, by rfl⟩ : syracuseStep 2792003 = 4188005) B4188005
theorem B4184657 : Blo 1859631 4184657 := bstep (se 2 (by rfl) ⟨1569246, by rfl⟩ : syracuseStep 4184657 = 3138493) B3138493
theorem B2792033 : Blo 1859631 2792033 := bstep (se 2 (by rfl) ⟨1047012, by rfl⟩ : syracuseStep 2792033 = 2094025) B2094025
theorem B4184675 : Blo 1859631 4184675 := bstep (se 1 (by rfl) ⟨3138506, by rfl⟩ : syracuseStep 4184675 = 6277013) B6277013
theorem B2980451 : Blo 1859631 2980451 := bstep (se 1 (by rfl) ⟨2235338, by rfl⟩ : syracuseStep 2980451 = 4470677) B4470677
theorem B2792051 : Blo 1859631 2792051 := bstep (se 1 (by rfl) ⟨2094038, by rfl⟩ : syracuseStep 2792051 = 4188077) B4188077
theorem B3971729 : Blo 1859631 3971729 := bstep (se 2 (by rfl) ⟨1489398, by rfl⟩ : syracuseStep 3971729 = 2978797) B2978797
theorem B6281873 : Blo 1859631 6281873 := bstep (se 2 (by rfl) ⟨2355702, by rfl⟩ : syracuseStep 6281873 = 4711405) B4711405
theorem B2792081 : Blo 1859631 2792081 := bstep (se 2 (by rfl) ⟨1047030, by rfl⟩ : syracuseStep 2792081 = 2094061) B2094061
theorem B3971747 : Blo 1859631 3971747 := bstep (se 1 (by rfl) ⟨2978810, by rfl⟩ : syracuseStep 3971747 = 5957621) B5957621
theorem B5298851 : Blo 1859631 5298851 := bstep (se 1 (by rfl) ⟨3974138, by rfl⟩ : syracuseStep 5298851 = 7948277) B7948277
theorem B2792099 : Blo 1859631 2792099 := bstep (se 1 (by rfl) ⟨2094074, by rfl⟩ : syracuseStep 2792099 = 4188149) B4188149
theorem B7068323 : Blo 1859631 7068323 := bstep (se 1 (by rfl) ⟨5301242, by rfl⟩ : syracuseStep 7068323 = 10602485) B10602485
theorem B2792129 : Blo 1859631 2792129 := bstep (se 2 (by rfl) ⟨1047048, by rfl⟩ : syracuseStep 2792129 = 2094097) B2094097
theorem B3578563 : Blo 1859631 3578563 := bstep (se 1 (by rfl) ⟨2683922, by rfl⟩ : syracuseStep 3578563 = 5367845) B5367845
theorem B2792147 : Blo 1859631 2792147 := bstep (se 1 (by rfl) ⟨2094110, by rfl⟩ : syracuseStep 2792147 = 4188221) B4188221
theorem B2792177 : Blo 1859631 2792177 := bstep (se 2 (by rfl) ⟨1047066, by rfl⟩ : syracuseStep 2792177 = 2094133) B2094133
theorem B2792195 : Blo 1859631 2792195 := bstep (se 1 (by rfl) ⟨2094146, by rfl⟩ : syracuseStep 2792195 = 4188293) B4188293
theorem B4709137 : Blo 1859631 4709137 := bstep (se 2 (by rfl) ⟨1765926, by rfl⟩ : syracuseStep 4709137 = 3531853) B3531853
theorem B2792225 : Blo 1859631 2792225 := bstep (se 2 (by rfl) ⟨1047084, by rfl⟩ : syracuseStep 2792225 = 2094169) B2094169
theorem B2792243 : Blo 1859631 2792243 := bstep (se 1 (by rfl) ⟨2094182, by rfl⟩ : syracuseStep 2792243 = 4188365) B4188365
theorem B2792273 : Blo 1859631 2792273 := bstep (se 2 (by rfl) ⟨1047102, by rfl⟩ : syracuseStep 2792273 = 2094205) B2094205
theorem B2685793 : Blo 1859631 2685793 := bstep (se 2 (by rfl) ⟨1007172, by rfl⟩ : syracuseStep 2685793 = 2014345) B2014345
theorem B2792291 : Blo 1859631 2792291 := bstep (se 1 (by rfl) ⟨2094218, by rfl⟩ : syracuseStep 2792291 = 4188437) B4188437
theorem B4184945 : Blo 1859631 4184945 := bstep (se 2 (by rfl) ⟨1569354, by rfl⟩ : syracuseStep 4184945 = 3138709) B3138709
theorem B2792321 : Blo 1859631 2792321 := bstep (se 2 (by rfl) ⟨1047120, by rfl⟩ : syracuseStep 2792321 = 2094241) B2094241
theorem B4184963 : Blo 1859631 4184963 := bstep (se 1 (by rfl) ⟨3138722, by rfl⟩ : syracuseStep 4184963 = 6277445) B6277445
theorem B2980739 : Blo 1859631 2980739 := bstep (se 1 (by rfl) ⟨2235554, by rfl⟩ : syracuseStep 2980739 = 4471109) B4471109
theorem B2792339 : Blo 1859631 2792339 := bstep (se 1 (by rfl) ⟨2094254, by rfl⟩ : syracuseStep 2792339 = 4188509) B4188509
theorem B2792369 : Blo 1859631 2792369 := bstep (se 2 (by rfl) ⟨1047138, by rfl⟩ : syracuseStep 2792369 = 2094277) B2094277
theorem B2792387 : Blo 1859631 2792387 := bstep (se 1 (by rfl) ⟨2094290, by rfl⟩ : syracuseStep 2792387 = 4188581) B4188581
theorem B2792417 : Blo 1859631 2792417 := bstep (se 2 (by rfl) ⟨1047156, by rfl⟩ : syracuseStep 2792417 = 2094313) B2094313
theorem B2792435 : Blo 1859631 2792435 := bstep (se 1 (by rfl) ⟨2094326, by rfl⟩ : syracuseStep 2792435 = 4188653) B4188653
theorem B4709411 : Blo 1859631 4709411 := bstep (se 1 (by rfl) ⟨3532058, by rfl⟩ : syracuseStep 4709411 = 7064117) B7064117
theorem B2235443 : Blo 1859631 2235443 := bstep (se 1 (by rfl) ⟨1676582, by rfl⟩ : syracuseStep 2235443 = 3353165) B3353165
theorem B4185233 : Blo 1859631 4185233 := bstep (se 2 (by rfl) ⟨1569462, by rfl⟩ : syracuseStep 4185233 = 3138925) B3138925
theorem B4185251 : Blo 1859631 4185251 := bstep (se 1 (by rfl) ⟨3138938, by rfl⟩ : syracuseStep 4185251 = 6277877) B6277877
theorem B6282413 : Blo 1859631 6282413 := bstep (se 3 (by rfl) ⟨1177952, by rfl⟩ : syracuseStep 6282413 = 2355905) B2355905
theorem B4709603 : Blo 1859631 4709603 := bstep (se 1 (by rfl) ⟨3532202, by rfl⟩ : syracuseStep 4709603 = 7064405) B7064405
theorem B6282467 : Blo 1859631 6282467 := bstep (se 1 (by rfl) ⟨4711850, by rfl⟩ : syracuseStep 6282467 = 9423701) B9423701
theorem B5963053 : Blo 1859631 5963053 := bstep (se 3 (by rfl) ⟨1118072, by rfl⟩ : syracuseStep 5963053 = 2236145) B2236145
theorem B4242755 : Blo 1859631 4242755 := bstep (se 1 (by rfl) ⟨3182066, by rfl⟩ : syracuseStep 4242755 = 6364133) B6364133
theorem B5029229 : Blo 1859631 5029229 := bstep (se 3 (by rfl) ⟨942980, by rfl⟩ : syracuseStep 5029229 = 1885961) B1885961
theorem B7077233 : Blo 1859631 7077233 := bstep (se 2 (by rfl) ⟨2653962, by rfl⟩ : syracuseStep 7077233 = 5307925) B5307925
theorem B10599821 : Blo 1859631 10599821 := bstep (se 3 (by rfl) ⟨1987466, by rfl⟩ : syracuseStep 10599821 = 3974933) B3974933
theorem B4185521 : Blo 1859631 4185521 := bstep (se 2 (by rfl) ⟨1569570, by rfl⟩ : syracuseStep 4185521 = 3139141) B3139141
theorem B4185539 : Blo 1859631 4185539 := bstep (se 1 (by rfl) ⟨3139154, by rfl⟩ : syracuseStep 4185539 = 6278309) B6278309
theorem B6282737 : Blo 1859631 6282737 := bstep (se 2 (by rfl) ⟨2356026, by rfl⟩ : syracuseStep 6282737 = 4712053) B4712053
theorem B15892109 : Blo 1859631 15892109 := bstep (se 3 (by rfl) ⟨2979770, by rfl⟩ : syracuseStep 15892109 = 5959541) B5959541
theorem B10198669 : Blo 1859631 10198669 := bstep (se 3 (by rfl) ⟨1912250, by rfl⟩ : syracuseStep 10198669 = 3824501) B3824501
theorem B2981539 : Blo 1859631 2981539 := bstep (se 1 (by rfl) ⟨2236154, by rfl⟩ : syracuseStep 2981539 = 4472309) B4472309
theorem B4185809 : Blo 1859631 4185809 := bstep (se 2 (by rfl) ⟨1569678, by rfl⟩ : syracuseStep 4185809 = 3139357) B3139357
theorem B5299921 : Blo 1859631 5299921 := bstep (se 2 (by rfl) ⟨1987470, by rfl⟩ : syracuseStep 5299921 = 3974941) B3974941
theorem B4185827 : Blo 1859631 4185827 := bstep (se 1 (by rfl) ⟨3139370, by rfl⟩ : syracuseStep 4185827 = 6278741) B6278741
theorem B47685347 : Blo 1859631 47685347 := bstep (se 1 (by rfl) ⟨35764010, by rfl⟩ : syracuseStep 47685347 = 71528021) B71528021
theorem B10592005 : Blo 1859631 10592005 := bstep (se 4 (by rfl) ⟨993000, by rfl⟩ : syracuseStep 10592005 = 1986001) B1986001
theorem B2981681 : Blo 1859631 2981681 := bstep (se 2 (by rfl) ⟨1118130, by rfl⟩ : syracuseStep 2981681 = 2236261) B2236261
theorem B2981713 : Blo 1859631 2981713 := bstep (se 2 (by rfl) ⟨1118142, by rfl⟩ : syracuseStep 2981713 = 2236285) B2236285
theorem B11321315 : Blo 1859631 11321315 := bstep (se 1 (by rfl) ⟨8490986, by rfl⟩ : syracuseStep 11321315 = 16981973) B16981973
theorem B7061489 : Blo 1859631 7061489 := bstep (se 2 (by rfl) ⟨2648058, by rfl⟩ : syracuseStep 7061489 = 5296117) B5296117
theorem B4186097 : Blo 1859631 4186097 := bstep (se 2 (by rfl) ⟨1569786, by rfl⟩ : syracuseStep 4186097 = 3139573) B3139573
theorem B9420785 : Blo 1859631 9420785 := bstep (se 2 (by rfl) ⟨3532794, by rfl⟩ : syracuseStep 9420785 = 7065589) B7065589
theorem B5300275 : Blo 1859631 5300275 := bstep (se 1 (by rfl) ⟨3975206, by rfl⟩ : syracuseStep 5300275 = 7950413) B7950413
theorem B1859639 : Blo 1859631 1859639 := bstep (se 1 (by rfl) ⟨1394729, by rfl⟩ : syracuseStep 1859639 = 2789459) B2789459
theorem B1859659 : Blo 1859631 1859659 := bstep (se 1 (by rfl) ⟨1394744, by rfl⟩ : syracuseStep 1859659 = 2789489) B2789489
theorem B4186187 : Blo 1859631 4186187 := bstep (se 1 (by rfl) ⟨3139640, by rfl⟩ : syracuseStep 4186187 = 6279281) B6279281
theorem B1859671 : Blo 1859631 1859671 := bstep (se 1 (by rfl) ⟨1394753, by rfl⟩ : syracuseStep 1859671 = 2789507) B2789507
theorem B1859691 : Blo 1859631 1859691 := bstep (se 1 (by rfl) ⟨1394768, by rfl⟩ : syracuseStep 1859691 = 2789537) B2789537
theorem B1859703 : Blo 1859631 1859703 := bstep (se 1 (by rfl) ⟨1394777, by rfl⟩ : syracuseStep 1859703 = 2789555) B2789555
theorem B3530881 : Blo 1859631 3530881 := bstep (se 2 (by rfl) ⟨1324080, by rfl⟩ : syracuseStep 3530881 = 2648161) B2648161
theorem B4186241 : Blo 1859631 4186241 := bstep (se 2 (by rfl) ⟨1569840, by rfl⟩ : syracuseStep 4186241 = 3139681) B3139681
theorem B10739843 : Blo 1859631 10739843 := bstep (se 1 (by rfl) ⟨8054882, by rfl⟩ : syracuseStep 10739843 = 16109765) B16109765
theorem B1859723 : Blo 1859631 1859723 := bstep (se 1 (by rfl) ⟨1394792, by rfl⟩ : syracuseStep 1859723 = 2789585) B2789585
theorem B1859735 : Blo 1859631 1859735 := bstep (se 1 (by rfl) ⟨1394801, by rfl⟩ : syracuseStep 1859735 = 2789603) B2789603
theorem B14123159 : Blo 1859631 14123159 := bstep (se 1 (by rfl) ⟨10592369, by rfl⟩ : syracuseStep 14123159 = 21184739) B21184739
theorem B1859755 : Blo 1859631 1859755 := bstep (se 1 (by rfl) ⟨1394816, by rfl⟩ : syracuseStep 1859755 = 2789633) B2789633
theorem B6127795 : Blo 1859631 6127795 := bstep (se 1 (by rfl) ⟨4595846, by rfl⟩ : syracuseStep 6127795 = 9191693) B9191693
theorem B1859767 : Blo 1859631 1859767 := bstep (se 1 (by rfl) ⟨1394825, by rfl⟩ : syracuseStep 1859767 = 2789651) B2789651
theorem B1859787 : Blo 1859631 1859787 := bstep (se 1 (by rfl) ⟨1394840, by rfl⟩ : syracuseStep 1859787 = 2789681) B2789681
theorem B1859799 : Blo 1859631 1859799 := bstep (se 1 (by rfl) ⟨1394849, by rfl⟩ : syracuseStep 1859799 = 2789699) B2789699
theorem B15081689 : Blo 1859631 15081689 := bstep (se 2 (by rfl) ⟨5655633, by rfl⟩ : syracuseStep 15081689 = 11311267) B11311267
theorem B1859819 : Blo 1859631 1859819 := bstep (se 1 (by rfl) ⟨1394864, by rfl⟩ : syracuseStep 1859819 = 2789729) B2789729
theorem B1859831 : Blo 1859631 1859831 := bstep (se 1 (by rfl) ⟨1394873, by rfl⟩ : syracuseStep 1859831 = 2789747) B2789747
theorem B1859851 : Blo 1859631 1859851 := bstep (se 1 (by rfl) ⟨1394888, by rfl⟩ : syracuseStep 1859851 = 2789777) B2789777
theorem B3973387 : Blo 1859631 3973387 := bstep (se 1 (by rfl) ⟨2980040, by rfl⟩ : syracuseStep 3973387 = 5960081) B5960081
theorem B1859863 : Blo 1859631 1859863 := bstep (se 1 (by rfl) ⟨1394897, by rfl⟩ : syracuseStep 1859863 = 2789795) B2789795
theorem B1859883 : Blo 1859631 1859883 := bstep (se 1 (by rfl) ⟨1394912, by rfl⟩ : syracuseStep 1859883 = 2789825) B2789825
theorem B20119853 : Blo 1859631 20119853 := bstep (se 3 (by rfl) ⟨3772472, by rfl⟩ : syracuseStep 20119853 = 7544945) B7544945
theorem B4710707 : Blo 1859631 4710707 := bstep (se 1 (by rfl) ⟨3533030, by rfl⟩ : syracuseStep 4710707 = 7066061) B7066061
theorem B1859895 : Blo 1859631 1859895 := bstep (se 1 (by rfl) ⟨1394921, by rfl⟩ : syracuseStep 1859895 = 2789843) B2789843
theorem B1859915 : Blo 1859631 1859915 := bstep (se 1 (by rfl) ⟨1394936, by rfl⟩ : syracuseStep 1859915 = 2789873) B2789873
theorem B1859927 : Blo 1859631 1859927 := bstep (se 1 (by rfl) ⟨1394945, by rfl⟩ : syracuseStep 1859927 = 2789891) B2789891
theorem B4186457 : Blo 1859631 4186457 := bstep (se 2 (by rfl) ⟨1569921, by rfl⟩ : syracuseStep 4186457 = 3139843) B3139843
theorem B1859947 : Blo 1859631 1859947 := bstep (se 1 (by rfl) ⟨1394960, by rfl⟩ : syracuseStep 1859947 = 2789921) B2789921
theorem B1859959 : Blo 1859631 1859959 := bstep (se 1 (by rfl) ⟨1394969, by rfl⟩ : syracuseStep 1859959 = 2789939) B2789939
theorem B1859979 : Blo 1859631 1859979 := bstep (se 1 (by rfl) ⟨1394984, by rfl⟩ : syracuseStep 1859979 = 2789969) B2789969
theorem B1859991 : Blo 1859631 1859991 := bstep (se 1 (by rfl) ⟨1394993, by rfl⟩ : syracuseStep 1859991 = 2789987) B2789987
theorem B1860011 : Blo 1859631 1860011 := bstep (se 1 (by rfl) ⟨1395008, by rfl⟩ : syracuseStep 1860011 = 2790017) B2790017
theorem B4186547 : Blo 1859631 4186547 := bstep (se 1 (by rfl) ⟨3139910, by rfl⟩ : syracuseStep 4186547 = 6279821) B6279821
theorem B1860023 : Blo 1859631 1860023 := bstep (se 1 (by rfl) ⟨1395017, by rfl⟩ : syracuseStep 1860023 = 2790035) B2790035
theorem B1860043 : Blo 1859631 1860043 := bstep (se 1 (by rfl) ⟨1395032, by rfl⟩ : syracuseStep 1860043 = 2790065) B2790065
theorem B1860055 : Blo 1859631 1860055 := bstep (se 1 (by rfl) ⟨1395041, by rfl⟩ : syracuseStep 1860055 = 2790083) B2790083
theorem B4186583 : Blo 1859631 4186583 := bstep (se 1 (by rfl) ⟨3139937, by rfl⟩ : syracuseStep 4186583 = 6279875) B6279875
theorem B7545305 : Blo 1859631 7545305 := bstep (se 2 (by rfl) ⟨2829489, by rfl⟩ : syracuseStep 7545305 = 5658979) B5658979
theorem B1860075 : Blo 1859631 1860075 := bstep (se 1 (by rfl) ⟨1395056, by rfl⟩ : syracuseStep 1860075 = 2790113) B2790113
theorem B1860087 : Blo 1859631 1860087 := bstep (se 1 (by rfl) ⟨1395065, by rfl⟩ : syracuseStep 1860087 = 2790131) B2790131
theorem B1860107 : Blo 1859631 1860107 := bstep (se 1 (by rfl) ⟨1395080, by rfl⟩ : syracuseStep 1860107 = 2790161) B2790161
theorem B1860119 : Blo 1859631 1860119 := bstep (se 1 (by rfl) ⟨1395089, by rfl⟩ : syracuseStep 1860119 = 2790179) B2790179
theorem B1860139 : Blo 1859631 1860139 := bstep (se 1 (by rfl) ⟨1395104, by rfl⟩ : syracuseStep 1860139 = 2790209) B2790209
theorem B1860151 : Blo 1859631 1860151 := bstep (se 1 (by rfl) ⟨1395113, by rfl⟩ : syracuseStep 1860151 = 2790227) B2790227
theorem B1860171 : Blo 1859631 1860171 := bstep (se 1 (by rfl) ⟨1395128, by rfl⟩ : syracuseStep 1860171 = 2790257) B2790257
theorem B1860183 : Blo 1859631 1860183 := bstep (se 1 (by rfl) ⟨1395137, by rfl⟩ : syracuseStep 1860183 = 2790275) B2790275
theorem B7545433 : Blo 1859631 7545433 := bstep (se 2 (by rfl) ⟨2829537, by rfl⟩ : syracuseStep 7545433 = 5659075) B5659075
theorem B5096029 : Blo 1859631 5096029 := bstep (se 3 (by rfl) ⟨955505, by rfl⟩ : syracuseStep 5096029 = 1911011) B1911011
theorem B1860203 : Blo 1859631 1860203 := bstep (se 1 (by rfl) ⟨1395152, by rfl⟩ : syracuseStep 1860203 = 2790305) B2790305
theorem B1860215 : Blo 1859631 1860215 := bstep (se 1 (by rfl) ⟨1395161, by rfl⟩ : syracuseStep 1860215 = 2790323) B2790323
theorem B1860235 : Blo 1859631 1860235 := bstep (se 1 (by rfl) ⟨1395176, by rfl⟩ : syracuseStep 1860235 = 2790353) B2790353
theorem B4186763 : Blo 1859631 4186763 := bstep (se 1 (by rfl) ⟨3140072, by rfl⟩ : syracuseStep 4186763 = 6280145) B6280145
theorem B1860247 : Blo 1859631 1860247 := bstep (se 1 (by rfl) ⟨1395185, by rfl⟩ : syracuseStep 1860247 = 2790371) B2790371
theorem B1860267 : Blo 1859631 1860267 := bstep (se 1 (by rfl) ⟨1395200, by rfl⟩ : syracuseStep 1860267 = 2790401) B2790401
theorem B15893171 : Blo 1859631 15893171 := bstep (se 1 (by rfl) ⟨11919878, by rfl⟩ : syracuseStep 15893171 = 23839757) B23839757
theorem B1860279 : Blo 1859631 1860279 := bstep (se 1 (by rfl) ⟨1395209, by rfl⟩ : syracuseStep 1860279 = 2790419) B2790419
theorem B4186817 : Blo 1859631 4186817 := bstep (se 2 (by rfl) ⟨1570056, by rfl⟩ : syracuseStep 4186817 = 3140113) B3140113
theorem B1860299 : Blo 1859631 1860299 := bstep (se 1 (by rfl) ⟨1395224, by rfl⟩ : syracuseStep 1860299 = 2790449) B2790449
theorem B1860311 : Blo 1859631 1860311 := bstep (se 1 (by rfl) ⟨1395233, by rfl⟩ : syracuseStep 1860311 = 2790467) B2790467
theorem B13083353 : Blo 1859631 13083353 := bstep (se 2 (by rfl) ⟨4906257, by rfl⟩ : syracuseStep 13083353 = 9812515) B9812515
theorem B1860331 : Blo 1859631 1860331 := bstep (se 1 (by rfl) ⟨1395248, by rfl⟩ : syracuseStep 1860331 = 2790497) B2790497
theorem B1860343 : Blo 1859631 1860343 := bstep (se 1 (by rfl) ⟨1395257, by rfl⟩ : syracuseStep 1860343 = 2790515) B2790515
theorem B7947011 : Blo 1859631 7947011 := bstep (se 1 (by rfl) ⟨5960258, by rfl⟩ : syracuseStep 7947011 = 11920517) B11920517
theorem B1860363 : Blo 1859631 1860363 := bstep (se 1 (by rfl) ⟨1395272, by rfl⟩ : syracuseStep 1860363 = 2790545) B2790545
theorem B1860375 : Blo 1859631 1860375 := bstep (se 1 (by rfl) ⟨1395281, by rfl⟩ : syracuseStep 1860375 = 2790563) B2790563
theorem B1860395 : Blo 1859631 1860395 := bstep (se 1 (by rfl) ⟨1395296, by rfl⟩ : syracuseStep 1860395 = 2790593) B2790593
theorem B1860407 : Blo 1859631 1860407 := bstep (se 1 (by rfl) ⟨1395305, by rfl⟩ : syracuseStep 1860407 = 2790611) B2790611
theorem B3531595 : Blo 1859631 3531595 := bstep (se 1 (by rfl) ⟨2648696, by rfl⟩ : syracuseStep 3531595 = 5297393) B5297393
theorem B1860427 : Blo 1859631 1860427 := bstep (se 1 (by rfl) ⟨1395320, by rfl⟩ : syracuseStep 1860427 = 2790641) B2790641
theorem B4711243 : Blo 1859631 4711243 := bstep (se 1 (by rfl) ⟨3533432, by rfl⟩ : syracuseStep 4711243 = 7066865) B7066865
theorem B1860439 : Blo 1859631 1860439 := bstep (se 1 (by rfl) ⟨1395329, by rfl⟩ : syracuseStep 1860439 = 2790659) B2790659
theorem B15901541 : Blo 1859631 15901541 := bstep (se 4 (by rfl) ⟨1490769, by rfl⟩ : syracuseStep 15901541 = 2981539) B2981539
theorem B1860459 : Blo 1859631 1860459 := bstep (se 1 (by rfl) ⟨1395344, by rfl⟩ : syracuseStep 1860459 = 2790689) B2790689
theorem B20112245 : Blo 1859631 20112245 := bstep (se 5 (by rfl) ⟨942761, by rfl⟩ : syracuseStep 20112245 = 1885523) B1885523
theorem B1860471 : Blo 1859631 1860471 := bstep (se 1 (by rfl) ⟨1395353, by rfl⟩ : syracuseStep 1860471 = 2790707) B2790707
theorem B1860491 : Blo 1859631 1860491 := bstep (se 1 (by rfl) ⟨1395368, by rfl⟩ : syracuseStep 1860491 = 2790737) B2790737
theorem B3531671 : Blo 1859631 3531671 := bstep (se 1 (by rfl) ⟨2648753, by rfl⟩ : syracuseStep 3531671 = 5297507) B5297507
theorem B1860503 : Blo 1859631 1860503 := bstep (se 1 (by rfl) ⟨1395377, by rfl⟩ : syracuseStep 1860503 = 2790755) B2790755
theorem B4187033 : Blo 1859631 4187033 := bstep (se 2 (by rfl) ⟨1570137, by rfl⟩ : syracuseStep 4187033 = 3140275) B3140275
theorem B1860523 : Blo 1859631 1860523 := bstep (se 1 (by rfl) ⟨1395392, by rfl⟩ : syracuseStep 1860523 = 2790785) B2790785
theorem B4973491 : Blo 1859631 4973491 := bstep (se 1 (by rfl) ⟨3730118, by rfl⟩ : syracuseStep 4973491 = 7460237) B7460237
theorem B1860535 : Blo 1859631 1860535 := bstep (se 1 (by rfl) ⟨1395401, by rfl⟩ : syracuseStep 1860535 = 2790803) B2790803
theorem B1860555 : Blo 1859631 1860555 := bstep (se 1 (by rfl) ⟨1395416, by rfl⟩ : syracuseStep 1860555 = 2790833) B2790833
theorem B13411277 : Blo 1859631 13411277 := bstep (se 3 (by rfl) ⟨2514614, by rfl⟩ : syracuseStep 13411277 = 5029229) B5029229
theorem B1860567 : Blo 1859631 1860567 := bstep (se 1 (by rfl) ⟨1395425, by rfl⟩ : syracuseStep 1860567 = 2790851) B2790851
theorem B4711385 : Blo 1859631 4711385 := bstep (se 2 (by rfl) ⟨1766769, by rfl⟩ : syracuseStep 4711385 = 3533539) B3533539
theorem B1860587 : Blo 1859631 1860587 := bstep (se 1 (by rfl) ⟨1395440, by rfl⟩ : syracuseStep 1860587 = 2790881) B2790881
theorem B4187123 : Blo 1859631 4187123 := bstep (se 1 (by rfl) ⟨3140342, by rfl⟩ : syracuseStep 4187123 = 6280685) B6280685
theorem B1860599 : Blo 1859631 1860599 := bstep (se 1 (by rfl) ⟨1395449, by rfl⟩ : syracuseStep 1860599 = 2790899) B2790899
theorem B1860619 : Blo 1859631 1860619 := bstep (se 1 (by rfl) ⟨1395464, by rfl⟩ : syracuseStep 1860619 = 2790929) B2790929
theorem B1860631 : Blo 1859631 1860631 := bstep (se 1 (by rfl) ⟨1395473, by rfl⟩ : syracuseStep 1860631 = 2790947) B2790947
theorem B4187159 : Blo 1859631 4187159 := bstep (se 1 (by rfl) ⟨3140369, by rfl⟩ : syracuseStep 4187159 = 6280739) B6280739
theorem B1860651 : Blo 1859631 1860651 := bstep (se 1 (by rfl) ⟨1395488, by rfl⟩ : syracuseStep 1860651 = 2790977) B2790977
theorem B1860663 : Blo 1859631 1860663 := bstep (se 1 (by rfl) ⟨1395497, by rfl⟩ : syracuseStep 1860663 = 2790995) B2790995
theorem B3138635 : Blo 1859631 3138635 := bstep (se 1 (by rfl) ⟨2353976, by rfl⟩ : syracuseStep 3138635 = 4707953) B4707953
theorem B1860683 : Blo 1859631 1860683 := bstep (se 1 (by rfl) ⟨1395512, by rfl⟩ : syracuseStep 1860683 = 2791025) B2791025
theorem B1860695 : Blo 1859631 1860695 := bstep (se 1 (by rfl) ⟨1395521, by rfl⟩ : syracuseStep 1860695 = 2791043) B2791043
theorem B1860715 : Blo 1859631 1860715 := bstep (se 1 (by rfl) ⟨1395536, by rfl⟩ : syracuseStep 1860715 = 2791073) B2791073
theorem B1860727 : Blo 1859631 1860727 := bstep (se 1 (by rfl) ⟨1395545, by rfl⟩ : syracuseStep 1860727 = 2791091) B2791091
theorem B3581057 : Blo 1859631 3581057 := bstep (se 2 (by rfl) ⟨1342896, by rfl⟩ : syracuseStep 3581057 = 2685793) B2685793
theorem B7062659 : Blo 1859631 7062659 := bstep (se 1 (by rfl) ⟨5296994, by rfl⟩ : syracuseStep 7062659 = 10593989) B10593989
theorem B1860747 : Blo 1859631 1860747 := bstep (se 1 (by rfl) ⟨1395560, by rfl⟩ : syracuseStep 1860747 = 2791121) B2791121
theorem B7062673 : Blo 1859631 7062673 := bstep (se 2 (by rfl) ⟨2648502, by rfl⟩ : syracuseStep 7062673 = 5297005) B5297005
theorem B1860759 : Blo 1859631 1860759 := bstep (se 1 (by rfl) ⟨1395569, by rfl⟩ : syracuseStep 1860759 = 2791139) B2791139
theorem B1860779 : Blo 1859631 1860779 := bstep (se 1 (by rfl) ⟨1395584, by rfl⟩ : syracuseStep 1860779 = 2791169) B2791169
theorem B1860791 : Blo 1859631 1860791 := bstep (se 1 (by rfl) ⟨1395593, by rfl⟩ : syracuseStep 1860791 = 2791187) B2791187
theorem B3138763 : Blo 1859631 3138763 := bstep (se 1 (by rfl) ⟨2354072, by rfl⟩ : syracuseStep 3138763 = 4708145) B4708145
theorem B1860811 : Blo 1859631 1860811 := bstep (se 1 (by rfl) ⟨1395608, by rfl⟩ : syracuseStep 1860811 = 2791217) B2791217
theorem B4187339 : Blo 1859631 4187339 := bstep (se 1 (by rfl) ⟨3140504, by rfl⟩ : syracuseStep 4187339 = 6281009) B6281009
theorem B1860823 : Blo 1859631 1860823 := bstep (se 1 (by rfl) ⟨1395617, by rfl⟩ : syracuseStep 1860823 = 2791235) B2791235
theorem B1860843 : Blo 1859631 1860843 := bstep (se 1 (by rfl) ⟨1395632, by rfl⟩ : syracuseStep 1860843 = 2791265) B2791265
theorem B1860855 : Blo 1859631 1860855 := bstep (se 1 (by rfl) ⟨1395641, by rfl⟩ : syracuseStep 1860855 = 2791283) B2791283
theorem B4187393 : Blo 1859631 4187393 := bstep (se 2 (by rfl) ⟨1570272, by rfl⟩ : syracuseStep 4187393 = 3140545) B3140545
theorem B1860875 : Blo 1859631 1860875 := bstep (se 1 (by rfl) ⟨1395656, by rfl⟩ : syracuseStep 1860875 = 2791313) B2791313
theorem B1860887 : Blo 1859631 1860887 := bstep (se 1 (by rfl) ⟨1395665, by rfl⟩ : syracuseStep 1860887 = 2791331) B2791331
theorem B1860907 : Blo 1859631 1860907 := bstep (se 1 (by rfl) ⟨1395680, by rfl⟩ : syracuseStep 1860907 = 2791361) B2791361
theorem B1860919 : Blo 1859631 1860919 := bstep (se 1 (by rfl) ⟨1395689, by rfl⟩ : syracuseStep 1860919 = 2791379) B2791379
theorem B1860939 : Blo 1859631 1860939 := bstep (se 1 (by rfl) ⟨1395704, by rfl⟩ : syracuseStep 1860939 = 2791409) B2791409
theorem B1860951 : Blo 1859631 1860951 := bstep (se 1 (by rfl) ⟨1395713, by rfl⟩ : syracuseStep 1860951 = 2791427) B2791427
theorem B3138905 : Blo 1859631 3138905 := bstep (se 2 (by rfl) ⟨1177089, by rfl⟩ : syracuseStep 3138905 = 2354179) B2354179
theorem B1860971 : Blo 1859631 1860971 := bstep (se 1 (by rfl) ⟨1395728, by rfl⟩ : syracuseStep 1860971 = 2791457) B2791457
theorem B1860983 : Blo 1859631 1860983 := bstep (se 1 (by rfl) ⟨1395737, by rfl⟩ : syracuseStep 1860983 = 2791475) B2791475
theorem B1861003 : Blo 1859631 1861003 := bstep (se 1 (by rfl) ⟨1395752, by rfl⟩ : syracuseStep 1861003 = 2791505) B2791505
theorem B1861015 : Blo 1859631 1861015 := bstep (se 1 (by rfl) ⟨1395761, by rfl⟩ : syracuseStep 1861015 = 2791523) B2791523
theorem B1861035 : Blo 1859631 1861035 := bstep (se 1 (by rfl) ⟨1395776, by rfl⟩ : syracuseStep 1861035 = 2791553) B2791553
theorem B1861047 : Blo 1859631 1861047 := bstep (se 1 (by rfl) ⟨1395785, by rfl⟩ : syracuseStep 1861047 = 2791571) B2791571
theorem B7062977 : Blo 1859631 7062977 := bstep (se 2 (by rfl) ⟨2648616, by rfl⟩ : syracuseStep 7062977 = 5297233) B5297233
theorem B1861067 : Blo 1859631 1861067 := bstep (se 1 (by rfl) ⟨1395800, by rfl⟩ : syracuseStep 1861067 = 2791601) B2791601
theorem B1861079 : Blo 1859631 1861079 := bstep (se 1 (by rfl) ⟨1395809, by rfl⟩ : syracuseStep 1861079 = 2791619) B2791619
theorem B3139033 : Blo 1859631 3139033 := bstep (se 2 (by rfl) ⟨1177137, by rfl⟩ : syracuseStep 3139033 = 2354275) B2354275
theorem B4187609 : Blo 1859631 4187609 := bstep (se 2 (by rfl) ⟨1570353, by rfl⟩ : syracuseStep 4187609 = 3140707) B3140707
theorem B1861099 : Blo 1859631 1861099 := bstep (se 1 (by rfl) ⟨1395824, by rfl⟩ : syracuseStep 1861099 = 2791649) B2791649
theorem B1861111 : Blo 1859631 1861111 := bstep (se 1 (by rfl) ⟨1395833, by rfl⟩ : syracuseStep 1861111 = 2791667) B2791667
theorem B1861131 : Blo 1859631 1861131 := bstep (se 1 (by rfl) ⟨1395848, by rfl⟩ : syracuseStep 1861131 = 2791697) B2791697
theorem B1861143 : Blo 1859631 1861143 := bstep (se 1 (by rfl) ⟨1395857, by rfl⟩ : syracuseStep 1861143 = 2791715) B2791715
theorem B1861163 : Blo 1859631 1861163 := bstep (se 1 (by rfl) ⟨1395872, by rfl⟩ : syracuseStep 1861163 = 2791745) B2791745
theorem B10602029 : Blo 1859631 10602029 := bstep (se 3 (by rfl) ⟨1987880, by rfl⟩ : syracuseStep 10602029 = 3975761) B3975761
theorem B3532339 : Blo 1859631 3532339 := bstep (se 1 (by rfl) ⟨2649254, by rfl⟩ : syracuseStep 3532339 = 5298509) B5298509
theorem B4187699 : Blo 1859631 4187699 := bstep (se 1 (by rfl) ⟨3140774, by rfl⟩ : syracuseStep 4187699 = 6281549) B6281549
theorem B1861175 : Blo 1859631 1861175 := bstep (se 1 (by rfl) ⟨1395881, by rfl⟩ : syracuseStep 1861175 = 2791763) B2791763
theorem B1861195 : Blo 1859631 1861195 := bstep (se 1 (by rfl) ⟨1395896, by rfl⟩ : syracuseStep 1861195 = 2791793) B2791793
theorem B1861207 : Blo 1859631 1861207 := bstep (se 1 (by rfl) ⟨1395905, by rfl⟩ : syracuseStep 1861207 = 2791811) B2791811
theorem B4187735 : Blo 1859631 4187735 := bstep (se 1 (by rfl) ⟨3140801, by rfl⟩ : syracuseStep 4187735 = 6281603) B6281603
theorem B1861227 : Blo 1859631 1861227 := bstep (se 1 (by rfl) ⟨1395920, by rfl⟩ : syracuseStep 1861227 = 2791841) B2791841
theorem B3974771 : Blo 1859631 3974771 := bstep (se 1 (by rfl) ⟨2981078, by rfl⟩ : syracuseStep 3974771 = 5962157) B5962157
theorem B1861239 : Blo 1859631 1861239 := bstep (se 1 (by rfl) ⟨1395929, by rfl⟩ : syracuseStep 1861239 = 2791859) B2791859
theorem B1861259 : Blo 1859631 1861259 := bstep (se 1 (by rfl) ⟨1395944, by rfl⟩ : syracuseStep 1861259 = 2791889) B2791889
theorem B1861271 : Blo 1859631 1861271 := bstep (se 1 (by rfl) ⟨1395953, by rfl⟩ : syracuseStep 1861271 = 2791907) B2791907
theorem B1861291 : Blo 1859631 1861291 := bstep (se 1 (by rfl) ⟨1395968, by rfl⟩ : syracuseStep 1861291 = 2791937) B2791937
theorem B1861303 : Blo 1859631 1861303 := bstep (se 1 (by rfl) ⟨1395977, by rfl⟩ : syracuseStep 1861303 = 2791955) B2791955
theorem B1861323 : Blo 1859631 1861323 := bstep (se 1 (by rfl) ⟨1395992, by rfl⟩ : syracuseStep 1861323 = 2791985) B2791985
theorem B1861335 : Blo 1859631 1861335 := bstep (se 1 (by rfl) ⟨1396001, by rfl⟩ : syracuseStep 1861335 = 2792003) B2792003
theorem B1861355 : Blo 1859631 1861355 := bstep (se 1 (by rfl) ⟨1396016, by rfl⟩ : syracuseStep 1861355 = 2792033) B2792033
theorem B1861367 : Blo 1859631 1861367 := bstep (se 1 (by rfl) ⟨1396025, by rfl⟩ : syracuseStep 1861367 = 2792051) B2792051
theorem B2647819 : Blo 1859631 2647819 := bstep (se 1 (by rfl) ⟨1985864, by rfl⟩ : syracuseStep 2647819 = 3971729) B3971729
theorem B4187915 : Blo 1859631 4187915 := bstep (se 1 (by rfl) ⟨3140936, by rfl⟩ : syracuseStep 4187915 = 6281873) B6281873
theorem B1861387 : Blo 1859631 1861387 := bstep (se 1 (by rfl) ⟨1396040, by rfl⟩ : syracuseStep 1861387 = 2792081) B2792081
theorem B2647831 : Blo 1859631 2647831 := bstep (se 1 (by rfl) ⟨1985873, by rfl⟩ : syracuseStep 2647831 = 3971747) B3971747
theorem B6702871 : Blo 1859631 6702871 := bstep (se 1 (by rfl) ⟨5027153, by rfl⟩ : syracuseStep 6702871 = 10054307) B10054307
theorem B3532567 : Blo 1859631 3532567 := bstep (se 1 (by rfl) ⟨2649425, by rfl⟩ : syracuseStep 3532567 = 5298851) B5298851
theorem B1861399 : Blo 1859631 1861399 := bstep (se 1 (by rfl) ⟨1396049, by rfl⟩ : syracuseStep 1861399 = 2792099) B2792099
theorem B4712215 : Blo 1859631 4712215 := bstep (se 1 (by rfl) ⟨3534161, by rfl⟩ : syracuseStep 4712215 = 7068323) B7068323
theorem B1861419 : Blo 1859631 1861419 := bstep (se 1 (by rfl) ⟨1396064, by rfl⟩ : syracuseStep 1861419 = 2792129) B2792129
theorem B1861431 : Blo 1859631 1861431 := bstep (se 1 (by rfl) ⟨1396073, by rfl⟩ : syracuseStep 1861431 = 2792147) B2792147
theorem B4187969 : Blo 1859631 4187969 := bstep (se 2 (by rfl) ⟨1570488, by rfl⟩ : syracuseStep 4187969 = 3140977) B3140977
theorem B1861451 : Blo 1859631 1861451 := bstep (se 1 (by rfl) ⟨1396088, by rfl⟩ : syracuseStep 1861451 = 2792177) B2792177
theorem B1861463 : Blo 1859631 1861463 := bstep (se 1 (by rfl) ⟨1396097, by rfl⟩ : syracuseStep 1861463 = 2792195) B2792195
theorem B1861483 : Blo 1859631 1861483 := bstep (se 1 (by rfl) ⟨1396112, by rfl⟩ : syracuseStep 1861483 = 2792225) B2792225
theorem B1861495 : Blo 1859631 1861495 := bstep (se 1 (by rfl) ⟨1396121, by rfl⟩ : syracuseStep 1861495 = 2792243) B2792243
theorem B3532673 : Blo 1859631 3532673 := bstep (se 2 (by rfl) ⟨1324752, by rfl⟩ : syracuseStep 3532673 = 2649505) B2649505
theorem B1861515 : Blo 1859631 1861515 := bstep (se 1 (by rfl) ⟨1396136, by rfl⟩ : syracuseStep 1861515 = 2792273) B2792273
theorem B1861527 : Blo 1859631 1861527 := bstep (se 1 (by rfl) ⟨1396145, by rfl⟩ : syracuseStep 1861527 = 2792291) B2792291
theorem B1886123 : Blo 1859631 1886123 := bstep (se 1 (by rfl) ⟨1414592, by rfl⟩ : syracuseStep 1886123 = 2829185) B2829185
theorem B1861547 : Blo 1859631 1861547 := bstep (se 1 (by rfl) ⟨1396160, by rfl⟩ : syracuseStep 1861547 = 2792321) B2792321
theorem B1861559 : Blo 1859631 1861559 := bstep (se 1 (by rfl) ⟨1396169, by rfl⟩ : syracuseStep 1861559 = 2792339) B2792339
theorem B6277067 : Blo 1859631 6277067 := bstep (se 1 (by rfl) ⟨4707800, by rfl⟩ : syracuseStep 6277067 = 9415601) B9415601
theorem B1861579 : Blo 1859631 1861579 := bstep (se 1 (by rfl) ⟨1396184, by rfl⟩ : syracuseStep 1861579 = 2792369) B2792369
theorem B1861591 : Blo 1859631 1861591 := bstep (se 1 (by rfl) ⟨1396193, by rfl⟩ : syracuseStep 1861591 = 2792387) B2792387
theorem B23840729 : Blo 1859631 23840729 := bstep (se 2 (by rfl) ⟨8940273, by rfl⟩ : syracuseStep 23840729 = 17880547) B17880547
theorem B31803353 : Blo 1859631 31803353 := bstep (se 2 (by rfl) ⟨11926257, by rfl⟩ : syracuseStep 31803353 = 23852515) B23852515
theorem B1861611 : Blo 1859631 1861611 := bstep (se 1 (by rfl) ⟨1396208, by rfl⟩ : syracuseStep 1861611 = 2792417) B2792417
theorem B1861623 : Blo 1859631 1861623 := bstep (se 1 (by rfl) ⟨1396217, by rfl⟩ : syracuseStep 1861623 = 2792435) B2792435
theorem B3139607 : Blo 1859631 3139607 := bstep (se 1 (by rfl) ⟨2354705, by rfl⟩ : syracuseStep 3139607 = 4709411) B4709411
theorem B3532825 : Blo 1859631 3532825 := bstep (se 2 (by rfl) ⟨1324809, by rfl⟩ : syracuseStep 3532825 = 2649619) B2649619
theorem B4188185 : Blo 1859631 4188185 := bstep (se 2 (by rfl) ⟨1570569, by rfl⟩ : syracuseStep 4188185 = 3141139) B3141139
theorem B4245529 : Blo 1859631 4245529 := bstep (se 2 (by rfl) ⟨1592073, by rfl⟩ : syracuseStep 4245529 = 3184147) B3184147
theorem B7063645 : Blo 1859631 7063645 := bstep (se 3 (by rfl) ⟨1324433, by rfl⟩ : syracuseStep 7063645 = 2648867) B2648867
theorem B4188275 : Blo 1859631 4188275 := bstep (se 1 (by rfl) ⟨3141206, by rfl⟩ : syracuseStep 4188275 = 6282413) B6282413
theorem B3139735 : Blo 1859631 3139735 := bstep (se 1 (by rfl) ⟨2354801, by rfl⟩ : syracuseStep 3139735 = 4709603) B4709603
theorem B4188311 : Blo 1859631 4188311 := bstep (se 1 (by rfl) ⟨3141233, by rfl⟩ : syracuseStep 4188311 = 6282467) B6282467
theorem B2828503 : Blo 1859631 2828503 := bstep (se 1 (by rfl) ⟨2121377, by rfl⟩ : syracuseStep 2828503 = 4242755) B4242755
theorem B6277337 : Blo 1859631 6277337 := bstep (se 2 (by rfl) ⟨2354001, by rfl⟩ : syracuseStep 6277337 = 4708003) B4708003
theorem B4188491 : Blo 1859631 4188491 := bstep (se 1 (by rfl) ⟨3141368, by rfl⟩ : syracuseStep 4188491 = 6282737) B6282737
theorem B7948637 : Blo 1859631 7948637 := bstep (se 3 (by rfl) ⟨1490369, by rfl⟩ : syracuseStep 7948637 = 2980739) B2980739
theorem B4188545 : Blo 1859631 4188545 := bstep (se 2 (by rfl) ⟨1570704, by rfl⟩ : syracuseStep 4188545 = 3141409) B3141409
theorem B10594739 : Blo 1859631 10594739 := bstep (se 1 (by rfl) ⟨7946054, by rfl⟩ : syracuseStep 10594739 = 15892109) B15892109
theorem B3975617 : Blo 1859631 3975617 := bstep (se 2 (by rfl) ⟨1490856, by rfl⟩ : syracuseStep 3975617 = 2981713) B2981713
theorem B6449629 : Blo 1859631 6449629 := bstep (se 3 (by rfl) ⟨1209305, by rfl⟩ : syracuseStep 6449629 = 2418611) B2418611
theorem B9423377 : Blo 1859631 9423377 := bstep (se 2 (by rfl) ⟨3533766, by rfl⟩ : syracuseStep 9423377 = 7067533) B7067533
theorem B7547543 : Blo 1859631 7547543 := bstep (se 1 (by rfl) ⟨5660657, by rfl⟩ : syracuseStep 7547543 = 11321315) B11321315
theorem B9423539 : Blo 1859631 9423539 := bstep (se 1 (by rfl) ⟨7067654, by rfl⟩ : syracuseStep 9423539 = 14135309) B14135309
theorem B3771137 : Blo 1859631 3771137 := bstep (se 2 (by rfl) ⟨1414176, by rfl⟩ : syracuseStep 3771137 = 2828353) B2828353
theorem B3140363 : Blo 1859631 3140363 := bstep (se 1 (by rfl) ⟨2355272, by rfl⟩ : syracuseStep 3140363 = 4710545) B4710545
theorem B3975959 : Blo 1859631 3975959 := bstep (se 1 (by rfl) ⟨2981969, by rfl⟩ : syracuseStep 3975959 = 5963939) B5963939
theorem B1911659 : Blo 1859631 1911659 := bstep (se 1 (by rfl) ⟨1433744, by rfl⟩ : syracuseStep 1911659 = 2867489) B2867489
theorem B3140491 : Blo 1859631 3140491 := bstep (se 1 (by rfl) ⟨2355368, by rfl⟩ : syracuseStep 3140491 = 4710737) B4710737
theorem B6278039 : Blo 1859631 6278039 := bstep (se 1 (by rfl) ⟨4708529, by rfl⟩ : syracuseStep 6278039 = 9417059) B9417059
theorem B2354123 : Blo 1859631 2354123 := bstep (se 1 (by rfl) ⟨1765592, by rfl⟩ : syracuseStep 2354123 = 3531185) B3531185
theorem B7949335 : Blo 1859631 7949335 := bstep (se 1 (by rfl) ⟨5962001, by rfl⟩ : syracuseStep 7949335 = 11924003) B11924003
theorem B3140633 : Blo 1859631 3140633 := bstep (se 2 (by rfl) ⟨1177737, by rfl⟩ : syracuseStep 3140633 = 2355475) B2355475
theorem B8490035 : Blo 1859631 8490035 := bstep (se 1 (by rfl) ⟨6367526, by rfl⟩ : syracuseStep 8490035 = 12735053) B12735053
theorem B5958721 : Blo 1859631 5958721 := bstep (se 2 (by rfl) ⟨2234520, by rfl⟩ : syracuseStep 5958721 = 4469041) B4469041
theorem B14134337 : Blo 1859631 14134337 := bstep (se 2 (by rfl) ⟨5300376, by rfl⟩ : syracuseStep 14134337 = 10600753) B10600753
theorem B13405277 : Blo 1859631 13405277 := bstep (se 3 (by rfl) ⟨2513489, by rfl⟩ : syracuseStep 13405277 = 5026979) B5026979
theorem B15887461 : Blo 1859631 15887461 := bstep (se 4 (by rfl) ⟨1489449, by rfl⟩ : syracuseStep 15887461 = 2978899) B2978899
theorem B20401283 : Blo 1859631 20401283 := bstep (se 1 (by rfl) ⟨15300962, by rfl⟩ : syracuseStep 20401283 = 30601925) B30601925
theorem B2092171 : Blo 1859631 2092171 := bstep (se 1 (by rfl) ⟨1569128, by rfl⟩ : syracuseStep 2092171 = 3138257) B3138257
theorem B3140761 : Blo 1859631 3140761 := bstep (se 2 (by rfl) ⟨1177785, by rfl⟩ : syracuseStep 3140761 = 2355571) B2355571
theorem B2092279 : Blo 1859631 2092279 := bstep (se 1 (by rfl) ⟨1569209, by rfl⟩ : syracuseStep 2092279 = 3138419) B3138419
theorem B8490257 : Blo 1859631 8490257 := bstep (se 2 (by rfl) ⟨3183846, by rfl⟩ : syracuseStep 8490257 = 6367693) B6367693
theorem B14511395 : Blo 1859631 14511395 := bstep (se 1 (by rfl) ⟨10883546, by rfl⟩ : syracuseStep 14511395 = 21767093) B21767093
theorem B3534131 : Blo 1859631 3534131 := bstep (se 1 (by rfl) ⟨2650598, by rfl⟩ : syracuseStep 3534131 = 5301197) B5301197
theorem B7064921 : Blo 1859631 7064921 := bstep (se 2 (by rfl) ⟨2649345, by rfl⟩ : syracuseStep 7064921 = 5298691) B5298691
theorem B6892931 : Blo 1859631 6892931 := bstep (se 1 (by rfl) ⟨5169698, by rfl⟩ : syracuseStep 6892931 = 10339397) B10339397
theorem B9416087 : Blo 1859631 9416087 := bstep (se 1 (by rfl) ⟨7062065, by rfl⟩ : syracuseStep 9416087 = 14124131) B14124131
theorem B1985963 : Blo 1859631 1985963 := bstep (se 1 (by rfl) ⟨1489472, by rfl⟩ : syracuseStep 1985963 = 2978945) B2978945
theorem B2092459 : Blo 1859631 2092459 := bstep (se 1 (by rfl) ⟨1569344, by rfl⟩ : syracuseStep 2092459 = 3138689) B3138689
theorem B6278579 : Blo 1859631 6278579 := bstep (se 1 (by rfl) ⟨4708934, by rfl⟩ : syracuseStep 6278579 = 9417869) B9417869
theorem B15085061 : Blo 1859631 15085061 := bstep (se 4 (by rfl) ⟨1414224, by rfl⟩ : syracuseStep 15085061 = 2828449) B2828449
theorem B2092567 : Blo 1859631 2092567 := bstep (se 1 (by rfl) ⟨1569425, by rfl⟩ : syracuseStep 2092567 = 3138851) B3138851
theorem B2354827 : Blo 1859631 2354827 := bstep (se 1 (by rfl) ⟨1766120, by rfl⟩ : syracuseStep 2354827 = 3532241) B3532241
theorem B6704819 : Blo 1859631 6704819 := bstep (se 1 (by rfl) ⟨5028614, by rfl⟩ : syracuseStep 6704819 = 10057229) B10057229
theorem B6278849 : Blo 1859631 6278849 := bstep (se 2 (by rfl) ⟨2354568, by rfl⟩ : syracuseStep 6278849 = 4709137) B4709137
theorem B2092747 : Blo 1859631 2092747 := bstep (se 1 (by rfl) ⟨1569560, by rfl⟩ : syracuseStep 2092747 = 3139121) B3139121
theorem B3141335 : Blo 1859631 3141335 := bstep (se 1 (by rfl) ⟨2356001, by rfl⟩ : syracuseStep 3141335 = 4712003) B4712003
theorem B2649881 : Blo 1859631 2649881 := bstep (se 2 (by rfl) ⟨993705, by rfl⟩ : syracuseStep 2649881 = 1987411) B1987411
theorem B5443379 : Blo 1859631 5443379 := bstep (se 1 (by rfl) ⟨4082534, by rfl⟩ : syracuseStep 5443379 = 8165069) B8165069
theorem B2092855 : Blo 1859631 2092855 := bstep (se 1 (by rfl) ⟨1569641, by rfl⟩ : syracuseStep 2092855 = 3139283) B3139283
theorem B3141463 : Blo 1859631 3141463 := bstep (se 1 (by rfl) ⟨2356097, by rfl⟩ : syracuseStep 3141463 = 4712195) B4712195
theorem B10596197 : Blo 1859631 10596197 := bstep (se 4 (by rfl) ⟨993393, by rfl⟩ : syracuseStep 10596197 = 1986787) B1986787
theorem B2355095 : Blo 1859631 2355095 := bstep (se 1 (by rfl) ⟨1766321, by rfl⟩ : syracuseStep 2355095 = 3532643) B3532643
theorem B20107187 : Blo 1859631 20107187 := bstep (se 1 (by rfl) ⟨15080390, by rfl⟩ : syracuseStep 20107187 = 30160781) B30160781
theorem B2093035 : Blo 1859631 2093035 := bstep (se 1 (by rfl) ⟨1569776, by rfl⟩ : syracuseStep 2093035 = 3139553) B3139553
theorem B15888419 : Blo 1859631 15888419 := bstep (se 1 (by rfl) ⟨11916314, by rfl⟩ : syracuseStep 15888419 = 23832629) B23832629
theorem B2093143 : Blo 1859631 2093143 := bstep (se 1 (by rfl) ⟨1569857, by rfl⟩ : syracuseStep 2093143 = 3139715) B3139715
theorem B2789465 : Blo 1859631 2789465 := bstep (se 2 (by rfl) ⟨1046049, by rfl⟩ : syracuseStep 2789465 = 2092099) B2092099
theorem B3772505 : Blo 1859631 3772505 := bstep (se 2 (by rfl) ⟨1414689, by rfl⟩ : syracuseStep 3772505 = 2829379) B2829379
theorem B2789579 : Blo 1859631 2789579 := bstep (se 1 (by rfl) ⟨2092184, by rfl⟩ : syracuseStep 2789579 = 4184369) B4184369
theorem B2789591 : Blo 1859631 2789591 := bstep (se 1 (by rfl) ⟨2092193, by rfl⟩ : syracuseStep 2789591 = 4184387) B4184387
theorem B6279389 : Blo 1859631 6279389 := bstep (se 3 (by rfl) ⟨1177385, by rfl⟩ : syracuseStep 6279389 = 2354771) B2354771
theorem B2093323 : Blo 1859631 2093323 := bstep (se 1 (by rfl) ⟨1569992, by rfl⟩ : syracuseStep 2093323 = 3139985) B3139985
theorem B2789657 : Blo 1859631 2789657 := bstep (se 2 (by rfl) ⟨1046121, by rfl⟩ : syracuseStep 2789657 = 2092243) B2092243
theorem B10596653 : Blo 1859631 10596653 := bstep (se 3 (by rfl) ⟨1986872, by rfl⟩ : syracuseStep 10596653 = 3973745) B3973745
theorem B2093431 : Blo 1859631 2093431 := bstep (se 1 (by rfl) ⟨1570073, by rfl⟩ : syracuseStep 2093431 = 3140147) B3140147
theorem B2789771 : Blo 1859631 2789771 := bstep (se 1 (by rfl) ⟨2092328, by rfl⟩ : syracuseStep 2789771 = 4184657) B4184657
theorem B7950737 : Blo 1859631 7950737 := bstep (se 2 (by rfl) ⟨2981526, by rfl⟩ : syracuseStep 7950737 = 5963053) B5963053
theorem B2789783 : Blo 1859631 2789783 := bstep (se 1 (by rfl) ⟨2092337, by rfl⟩ : syracuseStep 2789783 = 4184675) B4184675
theorem B1986967 : Blo 1859631 1986967 := bstep (se 1 (by rfl) ⟨1490225, by rfl⟩ : syracuseStep 1986967 = 2980451) B2980451
theorem B2650519 : Blo 1859631 2650519 := bstep (se 1 (by rfl) ⟨1987889, by rfl⟩ : syracuseStep 2650519 = 3975779) B3975779
theorem B4469195 : Blo 1859631 4469195 := bstep (se 1 (by rfl) ⟨3351896, by rfl⟩ : syracuseStep 4469195 = 6703793) B6703793
theorem B2789849 : Blo 1859631 2789849 := bstep (se 2 (by rfl) ⟨1046193, by rfl⟩ : syracuseStep 2789849 = 2092387) B2092387
theorem B2093611 : Blo 1859631 2093611 := bstep (se 1 (by rfl) ⟨1570208, by rfl⟩ : syracuseStep 2093611 = 3140417) B3140417
theorem B6795841 : Blo 1859631 6795841 := bstep (se 2 (by rfl) ⟨2548440, by rfl⟩ : syracuseStep 6795841 = 5096881) B5096881
theorem B3772993 : Blo 1859631 3772993 := bstep (se 2 (by rfl) ⟨1414872, by rfl⟩ : syracuseStep 3772993 = 2829745) B2829745
theorem B2789963 : Blo 1859631 2789963 := bstep (se 1 (by rfl) ⟨2092472, by rfl⟩ : syracuseStep 2789963 = 4184945) B4184945
theorem B2789975 : Blo 1859631 2789975 := bstep (se 1 (by rfl) ⟨2092481, by rfl⟩ : syracuseStep 2789975 = 4184963) B4184963
theorem B2355799 : Blo 1859631 2355799 := bstep (se 1 (by rfl) ⟨1766849, by rfl⟩ : syracuseStep 2355799 = 3533699) B3533699
theorem B21475991 : Blo 1859631 21475991 := bstep (se 1 (by rfl) ⟨16106993, by rfl⟩ : syracuseStep 21475991 = 32213987) B32213987
theorem B2093719 : Blo 1859631 2093719 := bstep (se 1 (by rfl) ⟨1570289, by rfl⟩ : syracuseStep 2093719 = 3140579) B3140579
theorem B2790041 : Blo 1859631 2790041 := bstep (se 2 (by rfl) ⟨1046265, by rfl⟩ : syracuseStep 2790041 = 2092531) B2092531
theorem B2790155 : Blo 1859631 2790155 := bstep (se 1 (by rfl) ⟨2092616, by rfl⟩ : syracuseStep 2790155 = 4185233) B4185233
theorem B2790167 : Blo 1859631 2790167 := bstep (se 1 (by rfl) ⟨2092625, by rfl⟩ : syracuseStep 2790167 = 4185251) B4185251
theorem B2093899 : Blo 1859631 2093899 := bstep (se 1 (by rfl) ⟨1570424, by rfl⟩ : syracuseStep 2093899 = 3140849) B3140849
theorem B2790233 : Blo 1859631 2790233 := bstep (se 2 (by rfl) ⟨1046337, by rfl⟩ : syracuseStep 2790233 = 2092675) B2092675
theorem B7066547 : Blo 1859631 7066547 := bstep (se 1 (by rfl) ⟨5299910, by rfl⟩ : syracuseStep 7066547 = 10599821) B10599821
theorem B2094007 : Blo 1859631 2094007 := bstep (se 1 (by rfl) ⟨1570505, by rfl⟩ : syracuseStep 2094007 = 3141011) B3141011
theorem B7066561 : Blo 1859631 7066561 := bstep (se 2 (by rfl) ⟨2649960, by rfl⟩ : syracuseStep 7066561 = 5299921) B5299921
theorem B2790347 : Blo 1859631 2790347 := bstep (se 1 (by rfl) ⟨2092760, by rfl⟩ : syracuseStep 2790347 = 4185521) B4185521
theorem B2790359 : Blo 1859631 2790359 := bstep (se 1 (by rfl) ⟨2092769, by rfl⟩ : syracuseStep 2790359 = 4185539) B4185539
theorem B10597337 : Blo 1859631 10597337 := bstep (se 2 (by rfl) ⟨3974001, by rfl⟩ : syracuseStep 10597337 = 7948003) B7948003
theorem B14136281 : Blo 1859631 14136281 := bstep (se 2 (by rfl) ⟨5301105, by rfl⟩ : syracuseStep 14136281 = 10602211) B10602211
theorem B2790425 : Blo 1859631 2790425 := bstep (se 2 (by rfl) ⟨1046409, by rfl⟩ : syracuseStep 2790425 = 2092819) B2092819
theorem B2094187 : Blo 1859631 2094187 := bstep (se 1 (by rfl) ⟨1570640, by rfl⟩ : syracuseStep 2094187 = 3141281) B3141281
theorem B2790539 : Blo 1859631 2790539 := bstep (se 1 (by rfl) ⟨2092904, by rfl⟩ : syracuseStep 2790539 = 4185809) B4185809
theorem B2790551 : Blo 1859631 2790551 := bstep (se 1 (by rfl) ⟨2092913, by rfl⟩ : syracuseStep 2790551 = 4185827) B4185827
theorem B31790231 : Blo 1859631 31790231 := bstep (se 1 (by rfl) ⟨23842673, by rfl⟩ : syracuseStep 31790231 = 47685347) B47685347
theorem B1987787 : Blo 1859631 1987787 := bstep (se 1 (by rfl) ⟨1490840, by rfl⟩ : syracuseStep 1987787 = 2981681) B2981681
theorem B2094295 : Blo 1859631 2094295 := bstep (se 1 (by rfl) ⟨1570721, by rfl⟩ : syracuseStep 2094295 = 3141443) B3141443
theorem B2790617 : Blo 1859631 2790617 := bstep (se 2 (by rfl) ⟨1046481, by rfl⟩ : syracuseStep 2790617 = 2092963) B2092963
theorem B16332049 : Blo 1859631 16332049 := bstep (se 2 (by rfl) ⟨6124518, by rfl⟩ : syracuseStep 16332049 = 12249037) B12249037
theorem B4707659 : Blo 1859631 4707659 := bstep (se 1 (by rfl) ⟨3530744, by rfl⟩ : syracuseStep 4707659 = 7061489) B7061489
theorem B2790731 : Blo 1859631 2790731 := bstep (se 1 (by rfl) ⟨2093048, by rfl⟩ : syracuseStep 2790731 = 4186097) B4186097
theorem B6280523 : Blo 1859631 6280523 := bstep (se 1 (by rfl) ⟨4710392, by rfl⟩ : syracuseStep 6280523 = 9420785) B9420785
theorem B2790743 : Blo 1859631 2790743 := bstep (se 1 (by rfl) ⟨2093057, by rfl⟩ : syracuseStep 2790743 = 4186115) B4186115
theorem B2790809 : Blo 1859631 2790809 := bstep (se 2 (by rfl) ⟨1046553, by rfl⟩ : syracuseStep 2790809 = 2093107) B2093107
theorem B5658077 : Blo 1859631 5658077 := bstep (se 3 (by rfl) ⟨1060889, by rfl⟩ : syracuseStep 5658077 = 2121779) B2121779
theorem B2790923 : Blo 1859631 2790923 := bstep (se 1 (by rfl) ⟨2093192, by rfl⟩ : syracuseStep 2790923 = 4186385) B4186385
theorem B2790935 : Blo 1859631 2790935 := bstep (se 1 (by rfl) ⟨2093201, by rfl⟩ : syracuseStep 2790935 = 4186403) B4186403
theorem B2791001 : Blo 1859631 2791001 := bstep (se 2 (by rfl) ⟨1046625, by rfl⟩ : syracuseStep 2791001 = 2093251) B2093251
theorem B6280793 : Blo 1859631 6280793 := bstep (se 2 (by rfl) ⟨2355297, by rfl⟩ : syracuseStep 6280793 = 4710595) B4710595
theorem B5027521 : Blo 1859631 5027521 := bstep (se 2 (by rfl) ⟨1885320, by rfl⟩ : syracuseStep 5027521 = 3770641) B3770641
theorem B2791115 : Blo 1859631 2791115 := bstep (se 1 (by rfl) ⟨2093336, by rfl⟩ : syracuseStep 2791115 = 4186673) B4186673
theorem B2791127 : Blo 1859631 2791127 := bstep (se 1 (by rfl) ⟨2093345, by rfl⟩ : syracuseStep 2791127 = 4186691) B4186691
theorem B10884881 : Blo 1859631 10884881 := bstep (se 2 (by rfl) ⟨4081830, by rfl⟩ : syracuseStep 10884881 = 8163661) B8163661
theorem B2791193 : Blo 1859631 2791193 := bstep (se 2 (by rfl) ⟨1046697, by rfl⟩ : syracuseStep 2791193 = 2093395) B2093395
theorem B5658457 : Blo 1859631 5658457 := bstep (se 2 (by rfl) ⟨2121921, by rfl⟩ : syracuseStep 5658457 = 4243843) B4243843
theorem B23844725 : Blo 1859631 23844725 := bstep (se 5 (by rfl) ⟨1117721, by rfl⟩ : syracuseStep 23844725 = 2235443) B2235443
theorem B2791307 : Blo 1859631 2791307 := bstep (se 1 (by rfl) ⟨2093480, by rfl⟩ : syracuseStep 2791307 = 4186961) B4186961
theorem B2791319 : Blo 1859631 2791319 := bstep (se 1 (by rfl) ⟨2093489, by rfl⟩ : syracuseStep 2791319 = 4186979) B4186979
theorem B6707137 : Blo 1859631 6707137 := bstep (se 2 (by rfl) ⟨2515176, by rfl⟩ : syracuseStep 6707137 = 5030353) B5030353
theorem B2791385 : Blo 1859631 2791385 := bstep (se 2 (by rfl) ⟨1046769, by rfl⟩ : syracuseStep 2791385 = 2093539) B2093539
theorem B2791499 : Blo 1859631 2791499 := bstep (se 1 (by rfl) ⟨2093624, by rfl⟩ : syracuseStep 2791499 = 4187249) B4187249
theorem B2791511 : Blo 1859631 2791511 := bstep (se 1 (by rfl) ⟨2093633, by rfl⟩ : syracuseStep 2791511 = 4187267) B4187267
theorem B2791577 : Blo 1859631 2791577 := bstep (se 2 (by rfl) ⟨1046841, by rfl⟩ : syracuseStep 2791577 = 2093683) B2093683
theorem B4184243 : Blo 1859631 4184243 := bstep (se 1 (by rfl) ⟨3138182, by rfl⟩ : syracuseStep 4184243 = 6276365) B6276365
theorem B4184279 : Blo 1859631 4184279 := bstep (se 1 (by rfl) ⟨3138209, by rfl⟩ : syracuseStep 4184279 = 6276419) B6276419
theorem B2791691 : Blo 1859631 2791691 := bstep (se 1 (by rfl) ⟨2093768, by rfl⟩ : syracuseStep 2791691 = 4187537) B4187537
theorem B12728593 : Blo 1859631 12728593 := bstep (se 2 (by rfl) ⟨4773222, by rfl⟩ : syracuseStep 12728593 = 9546445) B9546445
theorem B4708631 : Blo 1859631 4708631 := bstep (se 1 (by rfl) ⟨3531473, by rfl⟩ : syracuseStep 4708631 = 7062947) B7062947
theorem B2791703 : Blo 1859631 2791703 := bstep (se 1 (by rfl) ⟨2093777, by rfl⟩ : syracuseStep 2791703 = 4187555) B4187555
theorem B6281495 : Blo 1859631 6281495 := bstep (se 1 (by rfl) ⟨4711121, by rfl⟩ : syracuseStep 6281495 = 9422243) B9422243
theorem B18872621 : Blo 1859631 18872621 := bstep (se 3 (by rfl) ⟨3538616, by rfl⟩ : syracuseStep 18872621 = 7077233) B7077233
theorem B2791769 : Blo 1859631 2791769 := bstep (se 2 (by rfl) ⟨1046913, by rfl⟩ : syracuseStep 2791769 = 2093827) B2093827
theorem B8943965 : Blo 1859631 8943965 := bstep (se 3 (by rfl) ⟨1676993, by rfl⟩ : syracuseStep 8943965 = 3353987) B3353987
theorem B19085669 : Blo 1859631 19085669 := bstep (se 4 (by rfl) ⟨1789281, by rfl⟩ : syracuseStep 19085669 = 3578563) B3578563
theorem B26827109 : Blo 1859631 26827109 := bstep (se 4 (by rfl) ⟨2515041, by rfl⟩ : syracuseStep 26827109 = 5030083) B5030083
theorem B4184459 : Blo 1859631 4184459 := bstep (se 1 (by rfl) ⟨3138344, by rfl⟩ : syracuseStep 4184459 = 6276689) B6276689
theorem B4184513 : Blo 1859631 4184513 := bstep (se 2 (by rfl) ⟨1569192, by rfl⟩ : syracuseStep 4184513 = 3138385) B3138385
theorem B5298635 : Blo 1859631 5298635 := bstep (se 1 (by rfl) ⟨3973976, by rfl⟩ : syracuseStep 5298635 = 7947953) B7947953
theorem B2791883 : Blo 1859631 2791883 := bstep (se 1 (by rfl) ⟨2093912, by rfl⟩ : syracuseStep 2791883 = 4187825) B4187825
theorem B2791895 : Blo 1859631 2791895 := bstep (se 1 (by rfl) ⟨2093921, by rfl⟩ : syracuseStep 2791895 = 4187843) B4187843
theorem B7543313 : Blo 1859631 7543313 := bstep (se 2 (by rfl) ⟨2828742, by rfl⟩ : syracuseStep 7543313 = 5657485) B5657485
theorem B2791961 : Blo 1859631 2791961 := bstep (se 2 (by rfl) ⟨1046985, by rfl⟩ : syracuseStep 2791961 = 2093971) B2093971
theorem B11917955 : Blo 1859631 11917955 := bstep (se 1 (by rfl) ⟨8938466, by rfl⟩ : syracuseStep 11917955 = 17876933) B17876933
theorem B2792075 : Blo 1859631 2792075 := bstep (se 1 (by rfl) ⟨2094056, by rfl⟩ : syracuseStep 2792075 = 4188113) B4188113
theorem B2792087 : Blo 1859631 2792087 := bstep (se 1 (by rfl) ⟨2094065, by rfl⟩ : syracuseStep 2792087 = 4188131) B4188131
theorem B4184729 : Blo 1859631 4184729 := bstep (se 2 (by rfl) ⟨1569273, by rfl⟩ : syracuseStep 4184729 = 3138547) B3138547
theorem B2792153 : Blo 1859631 2792153 := bstep (se 2 (by rfl) ⟨1047057, by rfl⟩ : syracuseStep 2792153 = 2094115) B2094115
theorem B6707933 : Blo 1859631 6707933 := bstep (se 3 (by rfl) ⟨1257737, by rfl⟩ : syracuseStep 6707933 = 2515475) B2515475
theorem B4184819 : Blo 1859631 4184819 := bstep (se 1 (by rfl) ⟨3138614, by rfl⟩ : syracuseStep 4184819 = 6277229) B6277229
theorem B4184855 : Blo 1859631 4184855 := bstep (se 1 (by rfl) ⟨3138641, by rfl⟩ : syracuseStep 4184855 = 6277283) B6277283
theorem B6282035 : Blo 1859631 6282035 := bstep (se 1 (by rfl) ⟨4711526, by rfl⟩ : syracuseStep 6282035 = 9423053) B9423053
theorem B2792267 : Blo 1859631 2792267 := bstep (se 1 (by rfl) ⟨2094200, by rfl⟩ : syracuseStep 2792267 = 4188401) B4188401
theorem B2792279 : Blo 1859631 2792279 := bstep (se 1 (by rfl) ⟨2094209, by rfl⟩ : syracuseStep 2792279 = 4188419) B4188419
theorem B5299033 : Blo 1859631 5299033 := bstep (se 2 (by rfl) ⟨1987137, by rfl⟩ : syracuseStep 5299033 = 3974275) B3974275
theorem B9419651 : Blo 1859631 9419651 := bstep (se 1 (by rfl) ⟨7064738, by rfl⟩ : syracuseStep 9419651 = 14129477) B14129477
theorem B2792345 : Blo 1859631 2792345 := bstep (se 2 (by rfl) ⟨1047129, by rfl⟩ : syracuseStep 2792345 = 2094259) B2094259
theorem B4709299 : Blo 1859631 4709299 := bstep (se 1 (by rfl) ⟨3531974, by rfl⟩ : syracuseStep 4709299 = 7063949) B7063949
theorem B4185035 : Blo 1859631 4185035 := bstep (se 1 (by rfl) ⟨3138776, by rfl⟩ : syracuseStep 4185035 = 6277553) B6277553
theorem B4185089 : Blo 1859631 4185089 := bstep (se 2 (by rfl) ⟨1569408, by rfl⟩ : syracuseStep 4185089 = 3138817) B3138817
theorem B4709441 : Blo 1859631 4709441 := bstep (se 2 (by rfl) ⟨1766040, by rfl⟩ : syracuseStep 4709441 = 3532081) B3532081
theorem B6282305 : Blo 1859631 6282305 := bstep (se 2 (by rfl) ⟨2355864, by rfl⟩ : syracuseStep 6282305 = 4711729) B4711729
theorem B10886237 : Blo 1859631 10886237 := bstep (se 3 (by rfl) ⟨2041169, by rfl⟩ : syracuseStep 10886237 = 4082339) B4082339
theorem B4185305 : Blo 1859631 4185305 := bstep (se 2 (by rfl) ⟨1569489, by rfl⟩ : syracuseStep 4185305 = 3138979) B3138979
theorem B10591505 : Blo 1859631 10591505 := bstep (se 2 (by rfl) ⟨3971814, by rfl⟩ : syracuseStep 10591505 = 7943629) B7943629
theorem B14130449 : Blo 1859631 14130449 := bstep (se 2 (by rfl) ⟨5298918, by rfl⟩ : syracuseStep 14130449 = 10597837) B10597837
theorem B4185395 : Blo 1859631 4185395 := bstep (se 1 (by rfl) ⟨3139046, by rfl⟩ : syracuseStep 4185395 = 6278093) B6278093
theorem B8052043 : Blo 1859631 8052043 := bstep (se 1 (by rfl) ⟨6039032, by rfl⟩ : syracuseStep 8052043 = 12078065) B12078065
theorem B4185431 : Blo 1859631 4185431 := bstep (se 1 (by rfl) ⟨3139073, by rfl⟩ : syracuseStep 4185431 = 6278147) B6278147
theorem B3579265 : Blo 1859631 3579265 := bstep (se 2 (by rfl) ⟨1342224, by rfl⟩ : syracuseStep 3579265 = 2684449) B2684449
theorem B4185611 : Blo 1859631 4185611 := bstep (se 1 (by rfl) ⟨3139208, by rfl⟩ : syracuseStep 4185611 = 6278417) B6278417
theorem B13598225 : Blo 1859631 13598225 := bstep (se 2 (by rfl) ⟨5099334, by rfl⟩ : syracuseStep 13598225 = 10198669) B10198669
theorem B32235043 : Blo 1859631 32235043 := bstep (se 1 (by rfl) ⟨24176282, by rfl⟩ : syracuseStep 32235043 = 48352565) B48352565
theorem B15081005 : Blo 1859631 15081005 := bstep (se 3 (by rfl) ⟨2827688, by rfl⟩ : syracuseStep 15081005 = 5655377) B5655377
theorem B4185665 : Blo 1859631 4185665 := bstep (se 2 (by rfl) ⟨1569624, by rfl⟩ : syracuseStep 4185665 = 3139249) B3139249
theorem B6282845 : Blo 1859631 6282845 := bstep (se 3 (by rfl) ⟨1178033, by rfl⟩ : syracuseStep 6282845 = 2356067) B2356067
theorem B14122673 : Blo 1859631 14122673 := bstep (se 2 (by rfl) ⟨5296002, by rfl⟩ : syracuseStep 14122673 = 10592005) B10592005
theorem B4185881 : Blo 1859631 4185881 := bstep (se 2 (by rfl) ⟨1569705, by rfl⟩ : syracuseStep 4185881 = 3139411) B3139411
theorem B3399499 : Blo 1859631 3399499 := bstep (se 1 (by rfl) ⟨2549624, by rfl⟩ : syracuseStep 3399499 = 5099249) B5099249
theorem B4185971 : Blo 1859631 4185971 := bstep (se 1 (by rfl) ⟨3139478, by rfl⟩ : syracuseStep 4185971 = 6278957) B6278957
theorem B4186007 : Blo 1859631 4186007 := bstep (se 1 (by rfl) ⟨3139505, by rfl⟩ : syracuseStep 4186007 = 6279011) B6279011
theorem B3530699 : Blo 1859631 3530699 := bstep (se 1 (by rfl) ⟨2648024, by rfl⟩ : syracuseStep 3530699 = 5296049) B5296049
theorem B10592279 : Blo 1859631 10592279 := bstep (se 1 (by rfl) ⟨7944209, by rfl⟩ : syracuseStep 10592279 = 15888419) B15888419
theorem B4710433 : Blo 1859631 4710433 := bstep (se 2 (by rfl) ⟨1766412, by rfl⟩ : syracuseStep 4710433 = 3532825) B3532825
theorem B5660705 : Blo 1859631 5660705 := bstep (se 2 (by rfl) ⟨2122764, by rfl⟩ : syracuseStep 5660705 = 4245529) B4245529
theorem B1859643 : Blo 1859631 1859643 := bstep (se 1 (by rfl) ⟨1394732, by rfl⟩ : syracuseStep 1859643 = 2789465) B2789465
theorem B7159895 : Blo 1859631 7159895 := bstep (se 1 (by rfl) ⟨5369921, by rfl⟩ : syracuseStep 7159895 = 10739843) B10739843
theorem B1859719 : Blo 1859631 1859719 := bstep (se 1 (by rfl) ⟨1394789, by rfl⟩ : syracuseStep 1859719 = 2789579) B2789579
theorem B1859727 : Blo 1859631 1859727 := bstep (se 1 (by rfl) ⟨1394795, by rfl⟩ : syracuseStep 1859727 = 2789591) B2789591
theorem B4186259 : Blo 1859631 4186259 := bstep (se 1 (by rfl) ⟨3139694, by rfl⟩ : syracuseStep 4186259 = 6279389) B6279389
theorem B1859771 : Blo 1859631 1859771 := bstep (se 1 (by rfl) ⟨1394828, by rfl⟩ : syracuseStep 1859771 = 2789657) B2789657
theorem B4186313 : Blo 1859631 4186313 := bstep (se 2 (by rfl) ⟨1569867, by rfl⟩ : syracuseStep 4186313 = 3139735) B3139735
theorem B10060013 : Blo 1859631 10060013 := bstep (se 3 (by rfl) ⟨1886252, by rfl⟩ : syracuseStep 10060013 = 3772505) B3772505
theorem B1859847 : Blo 1859631 1859847 := bstep (se 1 (by rfl) ⟨1394885, by rfl⟩ : syracuseStep 1859847 = 2789771) B2789771
theorem B5300491 : Blo 1859631 5300491 := bstep (se 1 (by rfl) ⟨3975368, by rfl⟩ : syracuseStep 5300491 = 7950737) B7950737
theorem B1859855 : Blo 1859631 1859855 := bstep (se 1 (by rfl) ⟨1394891, by rfl⟩ : syracuseStep 1859855 = 2789783) B2789783
theorem B1859899 : Blo 1859631 1859899 := bstep (se 1 (by rfl) ⟨1394924, by rfl⟩ : syracuseStep 1859899 = 2789849) B2789849
theorem B5030203 : Blo 1859631 5030203 := bstep (se 1 (by rfl) ⟨3772652, by rfl⟩ : syracuseStep 5030203 = 7545305) B7545305
theorem B1859975 : Blo 1859631 1859975 := bstep (se 1 (by rfl) ⟨1394981, by rfl⟩ : syracuseStep 1859975 = 2789963) B2789963
theorem B1859983 : Blo 1859631 1859983 := bstep (se 1 (by rfl) ⟨1394987, by rfl⟩ : syracuseStep 1859983 = 2789975) B2789975
theorem B1860027 : Blo 1859631 1860027 := bstep (se 1 (by rfl) ⟨1395020, by rfl⟩ : syracuseStep 1860027 = 2790041) B2790041
theorem B1860103 : Blo 1859631 1860103 := bstep (se 1 (by rfl) ⟨1395077, by rfl⟩ : syracuseStep 1860103 = 2790155) B2790155
theorem B1860111 : Blo 1859631 1860111 := bstep (se 1 (by rfl) ⟨1395083, by rfl⟩ : syracuseStep 1860111 = 2790167) B2790167
theorem B5300765 : Blo 1859631 5300765 := bstep (se 3 (by rfl) ⟨993893, by rfl⟩ : syracuseStep 5300765 = 1987787) B1987787
theorem B1860155 : Blo 1859631 1860155 := bstep (se 1 (by rfl) ⟨1395116, by rfl⟩ : syracuseStep 1860155 = 2790233) B2790233
theorem B10601027 : Blo 1859631 10601027 := bstep (se 1 (by rfl) ⟨7950770, by rfl⟩ : syracuseStep 10601027 = 15901541) B15901541
theorem B4711031 : Blo 1859631 4711031 := bstep (se 1 (by rfl) ⟨3533273, by rfl⟩ : syracuseStep 4711031 = 7066547) B7066547
theorem B1860231 : Blo 1859631 1860231 := bstep (se 1 (by rfl) ⟨1395173, by rfl⟩ : syracuseStep 1860231 = 2790347) B2790347
theorem B1860239 : Blo 1859631 1860239 := bstep (se 1 (by rfl) ⟨1395179, by rfl⟩ : syracuseStep 1860239 = 2790359) B2790359
theorem B1860283 : Blo 1859631 1860283 := bstep (se 1 (by rfl) ⟨1395212, by rfl⟩ : syracuseStep 1860283 = 2790425) B2790425
theorem B9061121 : Blo 1859631 9061121 := bstep (se 2 (by rfl) ⟨3397920, by rfl⟩ : syracuseStep 9061121 = 6795841) B6795841
theorem B5030657 : Blo 1859631 5030657 := bstep (se 2 (by rfl) ⟨1886496, by rfl⟩ : syracuseStep 5030657 = 3772993) B3772993
theorem B1860359 : Blo 1859631 1860359 := bstep (se 1 (by rfl) ⟨1395269, by rfl⟩ : syracuseStep 1860359 = 2790539) B2790539
theorem B1860367 : Blo 1859631 1860367 := bstep (se 1 (by rfl) ⟨1395275, by rfl⟩ : syracuseStep 1860367 = 2790551) B2790551
theorem B21193487 : Blo 1859631 21193487 := bstep (se 1 (by rfl) ⟨15895115, by rfl⟩ : syracuseStep 21193487 = 31790231) B31790231
theorem B10060577 : Blo 1859631 10060577 := bstep (se 2 (by rfl) ⟨3772716, by rfl⟩ : syracuseStep 10060577 = 7545433) B7545433
theorem B1860411 : Blo 1859631 1860411 := bstep (se 1 (by rfl) ⟨1395308, by rfl⟩ : syracuseStep 1860411 = 2790617) B2790617
theorem B3138439 : Blo 1859631 3138439 := bstep (se 1 (by rfl) ⟨2353829, by rfl⟩ : syracuseStep 3138439 = 4707659) B4707659
theorem B1860487 : Blo 1859631 1860487 := bstep (se 1 (by rfl) ⟨1395365, by rfl⟩ : syracuseStep 1860487 = 2790731) B2790731
theorem B4187015 : Blo 1859631 4187015 := bstep (se 1 (by rfl) ⟨3140261, by rfl⟩ : syracuseStep 4187015 = 6280523) B6280523
theorem B1860495 : Blo 1859631 1860495 := bstep (se 1 (by rfl) ⟨1395371, by rfl⟩ : syracuseStep 1860495 = 2790743) B2790743
theorem B1860539 : Blo 1859631 1860539 := bstep (se 1 (by rfl) ⟨1395404, by rfl⟩ : syracuseStep 1860539 = 2790809) B2790809
theorem B1860615 : Blo 1859631 1860615 := bstep (se 1 (by rfl) ⟨1395461, by rfl⟩ : syracuseStep 1860615 = 2790923) B2790923
theorem B1860623 : Blo 1859631 1860623 := bstep (se 1 (by rfl) ⟨1395467, by rfl⟩ : syracuseStep 1860623 = 2790935) B2790935
theorem B1860667 : Blo 1859631 1860667 := bstep (se 1 (by rfl) ⟨1395500, by rfl⟩ : syracuseStep 1860667 = 2791001) B2791001
theorem B4187195 : Blo 1859631 4187195 := bstep (se 1 (by rfl) ⟨3140396, by rfl⟩ : syracuseStep 4187195 = 6280793) B6280793
theorem B1860743 : Blo 1859631 1860743 := bstep (se 1 (by rfl) ⟨1395557, by rfl⟩ : syracuseStep 1860743 = 2791115) B2791115
theorem B1860751 : Blo 1859631 1860751 := bstep (se 1 (by rfl) ⟨1395563, by rfl⟩ : syracuseStep 1860751 = 2791127) B2791127
theorem B4187321 : Blo 1859631 4187321 := bstep (se 2 (by rfl) ⟨1570245, by rfl⟩ : syracuseStep 4187321 = 3140491) B3140491
theorem B1860795 : Blo 1859631 1860795 := bstep (se 1 (by rfl) ⟨1395596, by rfl⟩ : syracuseStep 1860795 = 2791193) B2791193
theorem B9422081 : Blo 1859631 9422081 := bstep (se 2 (by rfl) ⟨3533280, by rfl⟩ : syracuseStep 9422081 = 7066561) B7066561
theorem B1860871 : Blo 1859631 1860871 := bstep (se 1 (by rfl) ⟨1395653, by rfl⟩ : syracuseStep 1860871 = 2791307) B2791307
theorem B1860879 : Blo 1859631 1860879 := bstep (se 1 (by rfl) ⟨1395659, by rfl⟩ : syracuseStep 1860879 = 2791319) B2791319
theorem B15893819 : Blo 1859631 15893819 := bstep (se 1 (by rfl) ⟨11920364, by rfl⟩ : syracuseStep 15893819 = 23840729) B23840729
theorem B1860923 : Blo 1859631 1860923 := bstep (se 1 (by rfl) ⟨1395692, by rfl⟩ : syracuseStep 1860923 = 2791385) B2791385
theorem B21202235 : Blo 1859631 21202235 := bstep (se 1 (by rfl) ⟨15901676, by rfl⟩ : syracuseStep 21202235 = 31803353) B31803353
theorem B1860999 : Blo 1859631 1860999 := bstep (se 1 (by rfl) ⟨1395749, by rfl⟩ : syracuseStep 1860999 = 2791499) B2791499
theorem B1861007 : Blo 1859631 1861007 := bstep (se 1 (by rfl) ⟨1395755, by rfl⟩ : syracuseStep 1861007 = 2791511) B2791511
theorem B1861051 : Blo 1859631 1861051 := bstep (se 1 (by rfl) ⟨1395788, by rfl⟩ : syracuseStep 1861051 = 2791577) B2791577
theorem B40216013 : Blo 1859631 40216013 := bstep (se 3 (by rfl) ⟨7540502, by rfl⟩ : syracuseStep 40216013 = 15081005) B15081005
theorem B1861127 : Blo 1859631 1861127 := bstep (se 1 (by rfl) ⟨1395845, by rfl⟩ : syracuseStep 1861127 = 2791691) B2791691
theorem B3139087 : Blo 1859631 3139087 := bstep (se 1 (by rfl) ⟨2354315, by rfl⟩ : syracuseStep 3139087 = 4708631) B4708631
theorem B1861135 : Blo 1859631 1861135 := bstep (se 1 (by rfl) ⟨1395851, by rfl⟩ : syracuseStep 1861135 = 2791703) B2791703
theorem B4187663 : Blo 1859631 4187663 := bstep (se 1 (by rfl) ⟨3140747, by rfl⟩ : syracuseStep 4187663 = 6281495) B6281495
theorem B4187681 : Blo 1859631 4187681 := bstep (se 2 (by rfl) ⟨1570380, by rfl⟩ : syracuseStep 4187681 = 3140761) B3140761
theorem B1861179 : Blo 1859631 1861179 := bstep (se 1 (by rfl) ⟨1395884, by rfl⟩ : syracuseStep 1861179 = 2791769) B2791769
theorem B12723779 : Blo 1859631 12723779 := bstep (se 1 (by rfl) ⟨9542834, by rfl⟩ : syracuseStep 12723779 = 19085669) B19085669
theorem B17884739 : Blo 1859631 17884739 := bstep (se 1 (by rfl) ⟨13413554, by rfl⟩ : syracuseStep 17884739 = 26827109) B26827109
theorem B7063159 : Blo 1859631 7063159 := bstep (se 1 (by rfl) ⟨5297369, by rfl⟩ : syracuseStep 7063159 = 10594739) B10594739
theorem B3532423 : Blo 1859631 3532423 := bstep (se 1 (by rfl) ⟨2649317, by rfl⟩ : syracuseStep 3532423 = 5298635) B5298635
theorem B1861255 : Blo 1859631 1861255 := bstep (se 1 (by rfl) ⟨1395941, by rfl⟩ : syracuseStep 1861255 = 2791883) B2791883
theorem B1861263 : Blo 1859631 1861263 := bstep (se 1 (by rfl) ⟨1395947, by rfl⟩ : syracuseStep 1861263 = 2791895) B2791895
theorem B1861307 : Blo 1859631 1861307 := bstep (se 1 (by rfl) ⟨1395980, by rfl⟩ : syracuseStep 1861307 = 2791961) B2791961
theorem B1861383 : Blo 1859631 1861383 := bstep (se 1 (by rfl) ⟨1396037, by rfl⟩ : syracuseStep 1861383 = 2792075) B2792075
theorem B1861391 : Blo 1859631 1861391 := bstep (se 1 (by rfl) ⟨1396043, by rfl⟩ : syracuseStep 1861391 = 2792087) B2792087
theorem B5031695 : Blo 1859631 5031695 := bstep (se 1 (by rfl) ⟨3773771, by rfl⟩ : syracuseStep 5031695 = 7547543) B7547543
theorem B1861435 : Blo 1859631 1861435 := bstep (se 1 (by rfl) ⟨1396076, by rfl⟩ : syracuseStep 1861435 = 2792153) B2792153
theorem B4188023 : Blo 1859631 4188023 := bstep (se 1 (by rfl) ⟨3141017, by rfl⟩ : syracuseStep 4188023 = 6282035) B6282035
theorem B1861511 : Blo 1859631 1861511 := bstep (se 1 (by rfl) ⟨1396133, by rfl⟩ : syracuseStep 1861511 = 2792267) B2792267
theorem B1861519 : Blo 1859631 1861519 := bstep (se 1 (by rfl) ⟨1396139, by rfl⟩ : syracuseStep 1861519 = 2792279) B2792279
theorem B1861563 : Blo 1859631 1861563 := bstep (se 1 (by rfl) ⟨1396172, by rfl⟩ : syracuseStep 1861563 = 2792345) B2792345
theorem B3139627 : Blo 1859631 3139627 := bstep (se 1 (by rfl) ⟨2354720, by rfl⟩ : syracuseStep 3139627 = 4709441) B4709441
theorem B9422891 : Blo 1859631 9422891 := bstep (se 1 (by rfl) ⟨7067168, by rfl⟩ : syracuseStep 9422891 = 14134337) B14134337
theorem B4188203 : Blo 1859631 4188203 := bstep (se 1 (by rfl) ⟨3141152, by rfl⟩ : syracuseStep 4188203 = 6282305) B6282305
theorem B13600855 : Blo 1859631 13600855 := bstep (se 1 (by rfl) ⟨10200641, by rfl⟩ : syracuseStep 13600855 = 20401283) B20401283
theorem B3139769 : Blo 1859631 3139769 := bstep (se 2 (by rfl) ⟨1177413, by rfl⟩ : syracuseStep 3139769 = 2354827) B2354827
theorem B6703361 : Blo 1859631 6703361 := bstep (se 2 (by rfl) ⟨2513760, by rfl⟩ : syracuseStep 6703361 = 5027521) B5027521
theorem B6277391 : Blo 1859631 6277391 := bstep (se 1 (by rfl) ⟨4708043, by rfl⟩ : syracuseStep 6277391 = 9416087) B9416087
theorem B5097757 : Blo 1859631 5097757 := bstep (se 3 (by rfl) ⟨955829, by rfl⟩ : syracuseStep 5097757 = 1911659) B1911659
theorem B4188563 : Blo 1859631 4188563 := bstep (se 1 (by rfl) ⟨3141422, by rfl⟩ : syracuseStep 4188563 = 6282845) B6282845
theorem B4532665 : Blo 1859631 4532665 := bstep (se 2 (by rfl) ⟨1699749, by rfl⟩ : syracuseStep 4532665 = 3399499) B3399499
theorem B4188617 : Blo 1859631 4188617 := bstep (se 2 (by rfl) ⟨1570731, by rfl⟩ : syracuseStep 4188617 = 3141463) B3141463
theorem B9415115 : Blo 1859631 9415115 := bstep (se 1 (by rfl) ⟨7061336, by rfl⟩ : syracuseStep 9415115 = 14122673) B14122673
theorem B6277661 : Blo 1859631 6277661 := bstep (se 3 (by rfl) ⟨1177061, by rfl⟩ : syracuseStep 6277661 = 2354123) B2354123
theorem B7064131 : Blo 1859631 7064131 := bstep (se 1 (by rfl) ⟨5298098, by rfl⟩ : syracuseStep 7064131 = 10596197) B10596197
theorem B13404791 : Blo 1859631 13404791 := bstep (se 1 (by rfl) ⟨10053593, by rfl⟩ : syracuseStep 13404791 = 20107187) B20107187
theorem B2353799 : Blo 1859631 2353799 := bstep (se 1 (by rfl) ⟨1765349, by rfl⟩ : syracuseStep 2353799 = 3530699) B3530699
theorem B9415439 : Blo 1859631 9415439 := bstep (se 1 (by rfl) ⟨7061579, by rfl⟩ : syracuseStep 9415439 = 14123159) B14123159
theorem B10054459 : Blo 1859631 10054459 := bstep (se 1 (by rfl) ⟨7540844, by rfl⟩ : syracuseStep 10054459 = 15081689) B15081689
theorem B7064435 : Blo 1859631 7064435 := bstep (se 1 (by rfl) ⟨5298326, by rfl⟩ : syracuseStep 7064435 = 10596653) B10596653
theorem B3140471 : Blo 1859631 3140471 := bstep (se 1 (by rfl) ⟨2355353, by rfl⟩ : syracuseStep 3140471 = 4710707) B4710707
theorem B10595447 : Blo 1859631 10595447 := bstep (se 1 (by rfl) ⟨7946585, by rfl⟩ : syracuseStep 10595447 = 15893171) B15893171
theorem B2649289 : Blo 1859631 2649289 := bstep (se 2 (by rfl) ⟨993483, by rfl⟩ : syracuseStep 2649289 = 1986967) B1986967
theorem B3534025 : Blo 1859631 3534025 := bstep (se 2 (by rfl) ⟨1325259, by rfl⟩ : syracuseStep 3534025 = 2650519) B2650519
theorem B2354447 : Blo 1859631 2354447 := bstep (se 1 (by rfl) ⟨1765835, by rfl⟩ : syracuseStep 2354447 = 3531671) B3531671
theorem B8940851 : Blo 1859631 8940851 := bstep (se 1 (by rfl) ⟨6705638, by rfl⟩ : syracuseStep 8940851 = 13411277) B13411277
theorem B7064891 : Blo 1859631 7064891 := bstep (se 1 (by rfl) ⟨5298668, by rfl⟩ : syracuseStep 7064891 = 10597337) B10597337
theorem B3140923 : Blo 1859631 3140923 := bstep (se 1 (by rfl) ⟨2355692, by rfl⟩ : syracuseStep 3140923 = 4711385) B4711385
theorem B9424187 : Blo 1859631 9424187 := bstep (se 1 (by rfl) ⟨7068140, by rfl⟩ : syracuseStep 9424187 = 14136281) B14136281
theorem B2092423 : Blo 1859631 2092423 := bstep (se 1 (by rfl) ⟨1569317, by rfl⟩ : syracuseStep 2092423 = 3138635) B3138635
theorem B3141065 : Blo 1859631 3141065 := bstep (se 2 (by rfl) ⟨1177899, by rfl⟩ : syracuseStep 3141065 = 2355799) B2355799
theorem B53652941 : Blo 1859631 53652941 := bstep (se 3 (by rfl) ⟨10059926, by rfl⟩ : syracuseStep 53652941 = 20119853) B20119853
theorem B6794705 : Blo 1859631 6794705 := bstep (se 2 (by rfl) ⟨2548014, by rfl⟩ : syracuseStep 6794705 = 5096029) B5096029
theorem B9424349 : Blo 1859631 9424349 := bstep (se 3 (by rfl) ⟨1767065, by rfl⟩ : syracuseStep 9424349 = 3534131) B3534131
theorem B2092603 : Blo 1859631 2092603 := bstep (se 1 (by rfl) ⟨1569452, by rfl⟩ : syracuseStep 2092603 = 3138905) B3138905
theorem B32681573 : Blo 1859631 32681573 := bstep (se 4 (by rfl) ⟨3063897, by rfl⟩ : syracuseStep 32681573 = 6127795) B6127795
theorem B3772051 : Blo 1859631 3772051 := bstep (se 1 (by rfl) ⟨2829038, by rfl⟩ : syracuseStep 3772051 = 5658077) B5658077
theorem B2649847 : Blo 1859631 2649847 := bstep (se 1 (by rfl) ⟨1987385, by rfl⟩ : syracuseStep 2649847 = 3974771) B3974771
theorem B5295901 : Blo 1859631 5295901 := bstep (se 3 (by rfl) ⟨992981, by rfl⟩ : syracuseStep 5295901 = 1985963) B1985963
theorem B7065377 : Blo 1859631 7065377 := bstep (se 2 (by rfl) ⟨2649516, by rfl⟩ : syracuseStep 7065377 = 5299033) B5299033
theorem B15085349 : Blo 1859631 15085349 := bstep (se 4 (by rfl) ⟨1414251, by rfl⟩ : syracuseStep 15085349 = 2828503) B2828503
theorem B6279065 : Blo 1859631 6279065 := bstep (se 2 (by rfl) ⟨2354649, by rfl⟩ : syracuseStep 6279065 = 4709299) B4709299
theorem B15896483 : Blo 1859631 15896483 := bstep (se 1 (by rfl) ⟨11922362, by rfl⟩ : syracuseStep 15896483 = 23844725) B23844725
theorem B2093071 : Blo 1859631 2093071 := bstep (se 1 (by rfl) ⟨1569803, by rfl⟩ : syracuseStep 2093071 = 3139607) B3139607
theorem B2789495 : Blo 1859631 2789495 := bstep (se 1 (by rfl) ⟨2092121, by rfl⟩ : syracuseStep 2789495 = 4184243) B4184243
theorem B2789519 : Blo 1859631 2789519 := bstep (se 1 (by rfl) ⟨2092139, by rfl⟩ : syracuseStep 2789519 = 4184279) B4184279
theorem B2789561 : Blo 1859631 2789561 := bstep (se 2 (by rfl) ⟨1046085, by rfl⟩ : syracuseStep 2789561 = 2092171) B2092171
theorem B9416897 : Blo 1859631 9416897 := bstep (se 2 (by rfl) ⟨3531336, by rfl⟩ : syracuseStep 9416897 = 7062673) B7062673
theorem B2789639 : Blo 1859631 2789639 := bstep (se 1 (by rfl) ⟨2092229, by rfl⟩ : syracuseStep 2789639 = 4184459) B4184459
theorem B2789675 : Blo 1859631 2789675 := bstep (se 1 (by rfl) ⟨2092256, by rfl⟩ : syracuseStep 2789675 = 4184513) B4184513
theorem B2650411 : Blo 1859631 2650411 := bstep (se 1 (by rfl) ⟨1987808, by rfl⟩ : syracuseStep 2650411 = 3975617) B3975617
theorem B2789705 : Blo 1859631 2789705 := bstep (se 2 (by rfl) ⟨1046139, by rfl⟩ : syracuseStep 2789705 = 2092279) B2092279
theorem B10736057 : Blo 1859631 10736057 := bstep (se 2 (by rfl) ⟨4026021, by rfl⟩ : syracuseStep 10736057 = 8052043) B8052043
theorem B2789819 : Blo 1859631 2789819 := bstep (se 1 (by rfl) ⟨2092364, by rfl⟩ : syracuseStep 2789819 = 4184729) B4184729
theorem B2789879 : Blo 1859631 2789879 := bstep (se 1 (by rfl) ⟨2092409, by rfl⟩ : syracuseStep 2789879 = 4184819) B4184819
theorem B4772353 : Blo 1859631 4772353 := bstep (se 2 (by rfl) ⟨1789632, by rfl⟩ : syracuseStep 4772353 = 3579265) B3579265
theorem B2093575 : Blo 1859631 2093575 := bstep (se 1 (by rfl) ⟨1570181, by rfl⟩ : syracuseStep 2093575 = 3140363) B3140363
theorem B2789903 : Blo 1859631 2789903 := bstep (se 1 (by rfl) ⟨2092427, by rfl⟩ : syracuseStep 2789903 = 4184855) B4184855
theorem B2650639 : Blo 1859631 2650639 := bstep (se 1 (by rfl) ⟨1987979, by rfl⟩ : syracuseStep 2650639 = 3975959) B3975959
theorem B2789945 : Blo 1859631 2789945 := bstep (se 2 (by rfl) ⟨1046229, by rfl⟩ : syracuseStep 2789945 = 2092459) B2092459
theorem B6279767 : Blo 1859631 6279767 := bstep (se 1 (by rfl) ⟨4709825, by rfl⟩ : syracuseStep 6279767 = 9419651) B9419651
theorem B2790023 : Blo 1859631 2790023 := bstep (se 1 (by rfl) ⟨2092517, by rfl⟩ : syracuseStep 2790023 = 4185035) B4185035
theorem B2790059 : Blo 1859631 2790059 := bstep (se 1 (by rfl) ⟨2092544, by rfl⟩ : syracuseStep 2790059 = 4185089) B4185089
theorem B2093755 : Blo 1859631 2093755 := bstep (se 1 (by rfl) ⟨1570316, by rfl⟩ : syracuseStep 2093755 = 3140633) B3140633
theorem B2790089 : Blo 1859631 2790089 := bstep (se 2 (by rfl) ⟨1046283, by rfl⟩ : syracuseStep 2790089 = 2092567) B2092567
theorem B42980057 : Blo 1859631 42980057 := bstep (se 2 (by rfl) ⟨16117521, by rfl⟩ : syracuseStep 42980057 = 32235043) B32235043
theorem B7066349 : Blo 1859631 7066349 := bstep (se 3 (by rfl) ⟨1324940, by rfl⟩ : syracuseStep 7066349 = 2649881) B2649881
theorem B2790203 : Blo 1859631 2790203 := bstep (se 1 (by rfl) ⟨2092652, by rfl⟩ : syracuseStep 2790203 = 4185305) B4185305
theorem B2790263 : Blo 1859631 2790263 := bstep (se 1 (by rfl) ⟨2092697, by rfl⟩ : syracuseStep 2790263 = 4185395) B4185395
theorem B2790287 : Blo 1859631 2790287 := bstep (se 1 (by rfl) ⟨2092715, by rfl⟩ : syracuseStep 2790287 = 4185431) B4185431
theorem B2790329 : Blo 1859631 2790329 := bstep (se 2 (by rfl) ⟨1046373, by rfl⟩ : syracuseStep 2790329 = 2092747) B2092747
theorem B10056707 : Blo 1859631 10056707 := bstep (se 1 (by rfl) ⟨7542530, by rfl⟩ : syracuseStep 10056707 = 15085061) B15085061
theorem B2790407 : Blo 1859631 2790407 := bstep (se 1 (by rfl) ⟨2092805, by rfl⟩ : syracuseStep 2790407 = 4185611) B4185611
theorem B9065483 : Blo 1859631 9065483 := bstep (se 1 (by rfl) ⟨6799112, by rfl⟩ : syracuseStep 9065483 = 13598225) B13598225
theorem B2790443 : Blo 1859631 2790443 := bstep (se 1 (by rfl) ⟨2092832, by rfl⟩ : syracuseStep 2790443 = 4185665) B4185665
theorem B6280253 : Blo 1859631 6280253 := bstep (se 3 (by rfl) ⟨1177547, by rfl⟩ : syracuseStep 6280253 = 2355095) B2355095
theorem B2790473 : Blo 1859631 2790473 := bstep (se 2 (by rfl) ⟨1046427, by rfl⟩ : syracuseStep 2790473 = 2092855) B2092855
theorem B4469879 : Blo 1859631 4469879 := bstep (se 1 (by rfl) ⟨3352409, by rfl⟩ : syracuseStep 4469879 = 6704819) B6704819
theorem B2094223 : Blo 1859631 2094223 := bstep (se 1 (by rfl) ⟨1570667, by rfl⟩ : syracuseStep 2094223 = 3141335) B3141335
theorem B2790587 : Blo 1859631 2790587 := bstep (se 1 (by rfl) ⟨2092940, by rfl⟩ : syracuseStep 2790587 = 4185881) B4185881
theorem B2790647 : Blo 1859631 2790647 := bstep (se 1 (by rfl) ⟨2092985, by rfl⟩ : syracuseStep 2790647 = 4185971) B4185971
theorem B8942849 : Blo 1859631 8942849 := bstep (se 2 (by rfl) ⟨3353568, by rfl⟩ : syracuseStep 8942849 = 6707137) B6707137
theorem B2790671 : Blo 1859631 2790671 := bstep (se 1 (by rfl) ⟨2093003, by rfl⟩ : syracuseStep 2790671 = 4186007) B4186007
theorem B2790713 : Blo 1859631 2790713 := bstep (se 2 (by rfl) ⟨1046517, by rfl⟩ : syracuseStep 2790713 = 2093035) B2093035
theorem B2790791 : Blo 1859631 2790791 := bstep (se 1 (by rfl) ⟨2093093, by rfl⟩ : syracuseStep 2790791 = 4186187) B4186187
theorem B7067033 : Blo 1859631 7067033 := bstep (se 2 (by rfl) ⟨2650137, by rfl⟩ : syracuseStep 7067033 = 5300275) B5300275
theorem B2790827 : Blo 1859631 2790827 := bstep (se 1 (by rfl) ⟨2093120, by rfl⟩ : syracuseStep 2790827 = 4186241) B4186241
theorem B2790857 : Blo 1859631 2790857 := bstep (se 2 (by rfl) ⟨1046571, by rfl⟩ : syracuseStep 2790857 = 2093143) B2093143
theorem B9418193 : Blo 1859631 9418193 := bstep (se 2 (by rfl) ⟨3531822, by rfl⟩ : syracuseStep 9418193 = 7063645) B7063645
theorem B4707841 : Blo 1859631 4707841 := bstep (se 2 (by rfl) ⟨1765440, by rfl⟩ : syracuseStep 4707841 = 3530881) B3530881
theorem B2790971 : Blo 1859631 2790971 := bstep (se 1 (by rfl) ⟨2093228, by rfl⟩ : syracuseStep 2790971 = 4186457) B4186457
theorem B35747405 : Blo 1859631 35747405 := bstep (se 3 (by rfl) ⟨6702638, by rfl⟩ : syracuseStep 35747405 = 13405277) B13405277
theorem B2791031 : Blo 1859631 2791031 := bstep (se 1 (by rfl) ⟨2093273, by rfl⟩ : syracuseStep 2791031 = 4186547) B4186547
theorem B2791055 : Blo 1859631 2791055 := bstep (se 1 (by rfl) ⟨2093291, by rfl⟩ : syracuseStep 2791055 = 4186583) B4186583
theorem B9549485 : Blo 1859631 9549485 := bstep (se 3 (by rfl) ⟨1790528, by rfl⟩ : syracuseStep 9549485 = 3581057) B3581057
theorem B5297849 : Blo 1859631 5297849 := bstep (se 2 (by rfl) ⟨1986693, by rfl⟩ : syracuseStep 5297849 = 3973387) B3973387
theorem B2791097 : Blo 1859631 2791097 := bstep (se 2 (by rfl) ⟨1046661, by rfl⟩ : syracuseStep 2791097 = 2093323) B2093323
theorem B16971457 : Blo 1859631 16971457 := bstep (se 2 (by rfl) ⟨6364296, by rfl⟩ : syracuseStep 16971457 = 12728593) B12728593
theorem B2791175 : Blo 1859631 2791175 := bstep (se 1 (by rfl) ⟨2093381, by rfl⟩ : syracuseStep 2791175 = 4186763) B4186763
theorem B14317327 : Blo 1859631 14317327 := bstep (se 1 (by rfl) ⟨10737995, by rfl⟩ : syracuseStep 14317327 = 21475991) B21475991
theorem B2791211 : Blo 1859631 2791211 := bstep (se 1 (by rfl) ⟨2093408, by rfl⟩ : syracuseStep 2791211 = 4186817) B4186817
theorem B8722235 : Blo 1859631 8722235 := bstep (se 1 (by rfl) ⟨6541676, by rfl⟩ : syracuseStep 8722235 = 13083353) B13083353
theorem B2791241 : Blo 1859631 2791241 := bstep (se 2 (by rfl) ⟨1046715, by rfl⟩ : syracuseStep 2791241 = 2093431) B2093431
theorem B13408163 : Blo 1859631 13408163 := bstep (se 1 (by rfl) ⟨10056122, by rfl⟩ : syracuseStep 13408163 = 20112245) B20112245
theorem B2791355 : Blo 1859631 2791355 := bstep (se 1 (by rfl) ⟨2093516, by rfl⟩ : syracuseStep 2791355 = 4187033) B4187033
theorem B8599505 : Blo 1859631 8599505 := bstep (se 2 (by rfl) ⟨3224814, by rfl⟩ : syracuseStep 8599505 = 6449629) B6449629
theorem B2791415 : Blo 1859631 2791415 := bstep (se 1 (by rfl) ⟨2093561, by rfl⟩ : syracuseStep 2791415 = 4187123) B4187123
theorem B2791439 : Blo 1859631 2791439 := bstep (se 1 (by rfl) ⟨2093579, by rfl⟩ : syracuseStep 2791439 = 4187159) B4187159
theorem B2791481 : Blo 1859631 2791481 := bstep (se 2 (by rfl) ⟨1046805, by rfl⟩ : syracuseStep 2791481 = 2093611) B2093611
theorem B4708439 : Blo 1859631 4708439 := bstep (se 1 (by rfl) ⟨3531329, by rfl⟩ : syracuseStep 4708439 = 7062659) B7062659
theorem B2791559 : Blo 1859631 2791559 := bstep (se 1 (by rfl) ⟨2093669, by rfl⟩ : syracuseStep 2791559 = 4187339) B4187339
theorem B2791595 : Blo 1859631 2791595 := bstep (se 1 (by rfl) ⟨2093696, by rfl⟩ : syracuseStep 2791595 = 4187393) B4187393
theorem B2791625 : Blo 1859631 2791625 := bstep (se 2 (by rfl) ⟨1046859, by rfl⟩ : syracuseStep 2791625 = 2093719) B2093719
theorem B4708651 : Blo 1859631 4708651 := bstep (se 1 (by rfl) ⟨3531488, by rfl⟩ : syracuseStep 4708651 = 7062977) B7062977
theorem B2791739 : Blo 1859631 2791739 := bstep (se 1 (by rfl) ⟨2093804, by rfl⟩ : syracuseStep 2791739 = 4187609) B4187609
theorem B7068019 : Blo 1859631 7068019 := bstep (se 1 (by rfl) ⟨5301014, by rfl⟩ : syracuseStep 7068019 = 10602029) B10602029
theorem B2791799 : Blo 1859631 2791799 := bstep (se 1 (by rfl) ⟨2093849, by rfl⟩ : syracuseStep 2791799 = 4187699) B4187699
theorem B2791823 : Blo 1859631 2791823 := bstep (se 1 (by rfl) ⟨2093867, by rfl⟩ : syracuseStep 2791823 = 4187735) B4187735
theorem B4708793 : Blo 1859631 4708793 := bstep (se 2 (by rfl) ⟨1765797, by rfl⟩ : syracuseStep 4708793 = 3531595) B3531595
theorem B6281657 : Blo 1859631 6281657 := bstep (se 2 (by rfl) ⟨2355621, by rfl⟩ : syracuseStep 6281657 = 4711243) B4711243
theorem B2791865 : Blo 1859631 2791865 := bstep (se 2 (by rfl) ⟨1046949, by rfl⟩ : syracuseStep 2791865 = 2093899) B2093899
theorem B2791943 : Blo 1859631 2791943 := bstep (se 1 (by rfl) ⟨2093957, by rfl⟩ : syracuseStep 2791943 = 4187915) B4187915
theorem B7256587 : Blo 1859631 7256587 := bstep (se 1 (by rfl) ⟨5442440, by rfl⟩ : syracuseStep 7256587 = 10884881) B10884881
theorem B11917853 : Blo 1859631 11917853 := bstep (se 3 (by rfl) ⟨2234597, by rfl⟩ : syracuseStep 11917853 = 4469195) B4469195
theorem B2791979 : Blo 1859631 2791979 := bstep (se 1 (by rfl) ⟨2093984, by rfl⟩ : syracuseStep 2791979 = 4187969) B4187969
theorem B2792009 : Blo 1859631 2792009 := bstep (se 2 (by rfl) ⟨1047003, by rfl⟩ : syracuseStep 2792009 = 2094007) B2094007
theorem B4184711 : Blo 1859631 4184711 := bstep (se 1 (by rfl) ⟨3138533, by rfl⟩ : syracuseStep 4184711 = 6277067) B6277067
theorem B2792123 : Blo 1859631 2792123 := bstep (se 1 (by rfl) ⟨2094092, by rfl⟩ : syracuseStep 2792123 = 4188185) B4188185
theorem B10599113 : Blo 1859631 10599113 := bstep (se 2 (by rfl) ⟨3974667, by rfl⟩ : syracuseStep 10599113 = 7949335) B7949335
theorem B14121701 : Blo 1859631 14121701 := bstep (se 4 (by rfl) ⟨1323909, by rfl⟩ : syracuseStep 14121701 = 2647819) B2647819
theorem B2792183 : Blo 1859631 2792183 := bstep (se 1 (by rfl) ⟨2094137, by rfl⟩ : syracuseStep 2792183 = 4188275) B4188275
theorem B7944961 : Blo 1859631 7944961 := bstep (se 2 (by rfl) ⟨2979360, by rfl⟩ : syracuseStep 7944961 = 5958721) B5958721
theorem B87104261 : Blo 1859631 87104261 := bstep (se 4 (by rfl) ⟨8166024, by rfl⟩ : syracuseStep 87104261 = 16332049) B16332049
theorem B2792207 : Blo 1859631 2792207 := bstep (se 1 (by rfl) ⟨2094155, by rfl⟩ : syracuseStep 2792207 = 4188311) B4188311
theorem B21183281 : Blo 1859631 21183281 := bstep (se 2 (by rfl) ⟨7943730, by rfl⟩ : syracuseStep 21183281 = 15887461) B15887461
theorem B2792249 : Blo 1859631 2792249 := bstep (se 2 (by rfl) ⟨1047093, by rfl⟩ : syracuseStep 2792249 = 2094187) B2094187
theorem B4184891 : Blo 1859631 4184891 := bstep (se 1 (by rfl) ⟨3138668, by rfl⟩ : syracuseStep 4184891 = 6277337) B6277337
theorem B12581747 : Blo 1859631 12581747 := bstep (se 1 (by rfl) ⟨9436310, by rfl⟩ : syracuseStep 12581747 = 18872621) B18872621
theorem B2792327 : Blo 1859631 2792327 := bstep (se 1 (by rfl) ⟨2094245, by rfl⟩ : syracuseStep 2792327 = 4188491) B4188491
theorem B5299091 : Blo 1859631 5299091 := bstep (se 1 (by rfl) ⟨3974318, by rfl⟩ : syracuseStep 5299091 = 7948637) B7948637
theorem B5962643 : Blo 1859631 5962643 := bstep (se 1 (by rfl) ⟨4471982, by rfl⟩ : syracuseStep 5962643 = 8943965) B8943965
theorem B2792363 : Blo 1859631 2792363 := bstep (se 1 (by rfl) ⟨2094272, by rfl⟩ : syracuseStep 2792363 = 4188545) B4188545
theorem B4185017 : Blo 1859631 4185017 := bstep (se 2 (by rfl) ⟨1569381, by rfl⟩ : syracuseStep 4185017 = 3138763) B3138763
theorem B2792393 : Blo 1859631 2792393 := bstep (se 2 (by rfl) ⟨1047147, by rfl⟩ : syracuseStep 2792393 = 2094295) B2094295
theorem B5028875 : Blo 1859631 5028875 := bstep (se 1 (by rfl) ⟨3771656, by rfl⟩ : syracuseStep 5028875 = 7543313) B7543313
theorem B6282251 : Blo 1859631 6282251 := bstep (se 1 (by rfl) ⟨4711688, by rfl⟩ : syracuseStep 6282251 = 9423377) B9423377
theorem B7945303 : Blo 1859631 7945303 := bstep (se 1 (by rfl) ⟨5958977, by rfl⟩ : syracuseStep 7945303 = 11917955) B11917955
theorem B6282359 : Blo 1859631 6282359 := bstep (se 1 (by rfl) ⟨4711769, by rfl⟩ : syracuseStep 6282359 = 9423539) B9423539
theorem B4471955 : Blo 1859631 4471955 := bstep (se 1 (by rfl) ⟨3353966, by rfl⟩ : syracuseStep 4471955 = 6707933) B6707933
theorem B2514091 : Blo 1859631 2514091 := bstep (se 1 (by rfl) ⟨1885568, by rfl⟩ : syracuseStep 2514091 = 3771137) B3771137
theorem B4185359 : Blo 1859631 4185359 := bstep (se 1 (by rfl) ⟨3139019, by rfl⟩ : syracuseStep 4185359 = 6278039) B6278039
theorem B4185377 : Blo 1859631 4185377 := bstep (se 2 (by rfl) ⟨1569516, by rfl⟩ : syracuseStep 4185377 = 3139033) B3139033
theorem B21192029 : Blo 1859631 21192029 := bstep (se 3 (by rfl) ⟨3973505, by rfl⟩ : syracuseStep 21192029 = 7947011) B7947011
theorem B5660023 : Blo 1859631 5660023 := bstep (se 1 (by rfl) ⟨4245017, by rfl⟩ : syracuseStep 5660023 = 8490035) B8490035
theorem B7257491 : Blo 1859631 7257491 := bstep (se 1 (by rfl) ⟨5443118, by rfl⟩ : syracuseStep 7257491 = 10886237) B10886237
theorem B4709785 : Blo 1859631 4709785 := bstep (se 2 (by rfl) ⟨1766169, by rfl⟩ : syracuseStep 4709785 = 3532339) B3532339
theorem B7061003 : Blo 1859631 7061003 := bstep (se 1 (by rfl) ⟨5295752, by rfl⟩ : syracuseStep 7061003 = 10591505) B10591505
theorem B9420299 : Blo 1859631 9420299 := bstep (se 1 (by rfl) ⟨7065224, by rfl⟩ : syracuseStep 9420299 = 14130449) B14130449
theorem B5660171 : Blo 1859631 5660171 := bstep (se 1 (by rfl) ⟨4245128, by rfl⟩ : syracuseStep 5660171 = 8490257) B8490257
theorem B9674263 : Blo 1859631 9674263 := bstep (se 1 (by rfl) ⟨7255697, by rfl⟩ : syracuseStep 9674263 = 14511395) B14511395
theorem B4709947 : Blo 1859631 4709947 := bstep (se 1 (by rfl) ⟨3532460, by rfl⟩ : syracuseStep 4709947 = 7064921) B7064921
theorem B4595287 : Blo 1859631 4595287 := bstep (se 1 (by rfl) ⟨3446465, by rfl⟩ : syracuseStep 4595287 = 6892931) B6892931
theorem B26525285 : Blo 1859631 26525285 := bstep (se 4 (by rfl) ⟨2486745, by rfl⟩ : syracuseStep 26525285 = 4973491) B4973491
theorem B4185719 : Blo 1859631 4185719 := bstep (se 1 (by rfl) ⟨3139289, by rfl⟩ : syracuseStep 4185719 = 6278579) B6278579
theorem B9420461 : Blo 1859631 9420461 := bstep (se 3 (by rfl) ⟨1766336, by rfl⟩ : syracuseStep 9420461 = 3532673) B3532673
theorem B3530441 : Blo 1859631 3530441 := bstep (se 2 (by rfl) ⟨1323915, by rfl⟩ : syracuseStep 3530441 = 2647831) B2647831
theorem B8937161 : Blo 1859631 8937161 := bstep (se 2 (by rfl) ⟨3351435, by rfl⟩ : syracuseStep 8937161 = 6702871) B6702871
theorem B4710089 : Blo 1859631 4710089 := bstep (se 2 (by rfl) ⟨1766283, by rfl⟩ : syracuseStep 4710089 = 3532567) B3532567
theorem B6282953 : Blo 1859631 6282953 := bstep (se 2 (by rfl) ⟨2356107, by rfl⟩ : syracuseStep 6282953 = 4712215) B4712215
theorem B5029661 : Blo 1859631 5029661 := bstep (se 3 (by rfl) ⟨943061, by rfl⟩ : syracuseStep 5029661 = 1886123) B1886123
theorem B7544609 : Blo 1859631 7544609 := bstep (se 2 (by rfl) ⟨2829228, by rfl⟩ : syracuseStep 7544609 = 5658457) B5658457
theorem B4185899 : Blo 1859631 4185899 := bstep (se 1 (by rfl) ⟨3139424, by rfl⟩ : syracuseStep 4185899 = 6278849) B6278849
theorem B3628919 : Blo 1859631 3628919 := bstep (se 1 (by rfl) ⟨2721689, by rfl⟩ : syracuseStep 3628919 = 5443379) B5443379
theorem B7061519 : Blo 1859631 7061519 := bstep (se 1 (by rfl) ⟨5296139, by rfl⟩ : syracuseStep 7061519 = 10592279) B10592279
theorem B4186169 : Blo 1859631 4186169 := bstep (se 2 (by rfl) ⟨1569813, by rfl⟩ : syracuseStep 4186169 = 3139627) B3139627
theorem B1859663 : Blo 1859631 1859663 := bstep (se 1 (by rfl) ⟨1394747, by rfl⟩ : syracuseStep 1859663 = 2789495) B2789495
theorem B1859679 : Blo 1859631 1859679 := bstep (se 1 (by rfl) ⟨1394759, by rfl⟩ : syracuseStep 1859679 = 2789519) B2789519
theorem B1859707 : Blo 1859631 1859707 := bstep (se 1 (by rfl) ⟨1394780, by rfl⟩ : syracuseStep 1859707 = 2789561) B2789561
theorem B1859759 : Blo 1859631 1859759 := bstep (se 1 (by rfl) ⟨1394819, by rfl⟩ : syracuseStep 1859759 = 2789639) B2789639
theorem B1859783 : Blo 1859631 1859783 := bstep (se 1 (by rfl) ⟨1394837, by rfl⟩ : syracuseStep 1859783 = 2789675) B2789675
theorem B1859803 : Blo 1859631 1859803 := bstep (se 1 (by rfl) ⟨1394852, by rfl⟩ : syracuseStep 1859803 = 2789705) B2789705
theorem B1859879 : Blo 1859631 1859879 := bstep (se 1 (by rfl) ⟨1394909, by rfl⟩ : syracuseStep 1859879 = 2789819) B2789819
theorem B1859919 : Blo 1859631 1859919 := bstep (se 1 (by rfl) ⟨1394939, by rfl⟩ : syracuseStep 1859919 = 2789879) B2789879
theorem B1859935 : Blo 1859631 1859935 := bstep (se 1 (by rfl) ⟨1394951, by rfl⟩ : syracuseStep 1859935 = 2789903) B2789903
theorem B1859963 : Blo 1859631 1859963 := bstep (se 1 (by rfl) ⟨1394972, by rfl⟩ : syracuseStep 1859963 = 2789945) B2789945
theorem B4186511 : Blo 1859631 4186511 := bstep (se 1 (by rfl) ⟨3139883, by rfl⟩ : syracuseStep 4186511 = 6279767) B6279767
theorem B1860015 : Blo 1859631 1860015 := bstep (se 1 (by rfl) ⟨1395011, by rfl⟩ : syracuseStep 1860015 = 2790023) B2790023
theorem B1860039 : Blo 1859631 1860039 := bstep (se 1 (by rfl) ⟨1395029, by rfl⟩ : syracuseStep 1860039 = 2790059) B2790059
theorem B1860059 : Blo 1859631 1860059 := bstep (se 1 (by rfl) ⟨1395044, by rfl⟩ : syracuseStep 1860059 = 2790089) B2790089
theorem B4710899 : Blo 1859631 4710899 := bstep (se 1 (by rfl) ⟨3533174, by rfl⟩ : syracuseStep 4710899 = 7066349) B7066349
theorem B1860135 : Blo 1859631 1860135 := bstep (se 1 (by rfl) ⟨1395101, by rfl⟩ : syracuseStep 1860135 = 2790203) B2790203
theorem B1860175 : Blo 1859631 1860175 := bstep (se 1 (by rfl) ⟨1395131, by rfl⟩ : syracuseStep 1860175 = 2790263) B2790263
theorem B1860191 : Blo 1859631 1860191 := bstep (se 1 (by rfl) ⟨1395143, by rfl⟩ : syracuseStep 1860191 = 2790287) B2790287
theorem B1860219 : Blo 1859631 1860219 := bstep (se 1 (by rfl) ⟨1395164, by rfl⟩ : syracuseStep 1860219 = 2790329) B2790329
theorem B1860271 : Blo 1859631 1860271 := bstep (se 1 (by rfl) ⟨1395203, by rfl⟩ : syracuseStep 1860271 = 2790407) B2790407
theorem B9675449 : Blo 1859631 9675449 := bstep (se 2 (by rfl) ⟨3628293, by rfl⟩ : syracuseStep 9675449 = 7256587) B7256587
theorem B1860295 : Blo 1859631 1860295 := bstep (se 1 (by rfl) ⟨1395221, by rfl⟩ : syracuseStep 1860295 = 2790443) B2790443
theorem B4186835 : Blo 1859631 4186835 := bstep (se 1 (by rfl) ⟨3140126, by rfl⟩ : syracuseStep 4186835 = 6280253) B6280253
theorem B1860315 : Blo 1859631 1860315 := bstep (se 1 (by rfl) ⟨1395236, by rfl⟩ : syracuseStep 1860315 = 2790473) B2790473
theorem B1860391 : Blo 1859631 1860391 := bstep (se 1 (by rfl) ⟨1395293, by rfl⟩ : syracuseStep 1860391 = 2790587) B2790587
theorem B1860431 : Blo 1859631 1860431 := bstep (se 1 (by rfl) ⟨1395323, by rfl⟩ : syracuseStep 1860431 = 2790647) B2790647
theorem B1860447 : Blo 1859631 1860447 := bstep (se 1 (by rfl) ⟨1395335, by rfl⟩ : syracuseStep 1860447 = 2790671) B2790671
theorem B1860475 : Blo 1859631 1860475 := bstep (se 1 (by rfl) ⟨1395356, by rfl⟩ : syracuseStep 1860475 = 2790713) B2790713
theorem B1860527 : Blo 1859631 1860527 := bstep (se 1 (by rfl) ⟨1395395, by rfl⟩ : syracuseStep 1860527 = 2790791) B2790791
theorem B4711355 : Blo 1859631 4711355 := bstep (se 1 (by rfl) ⟨3533516, by rfl⟩ : syracuseStep 4711355 = 7067033) B7067033
theorem B1860551 : Blo 1859631 1860551 := bstep (se 1 (by rfl) ⟨1395413, by rfl⟩ : syracuseStep 1860551 = 2790827) B2790827
theorem B1860571 : Blo 1859631 1860571 := bstep (se 1 (by rfl) ⟨1395428, by rfl⟩ : syracuseStep 1860571 = 2790857) B2790857
theorem B10593281 : Blo 1859631 10593281 := bstep (se 2 (by rfl) ⟨3972480, by rfl⟩ : syracuseStep 10593281 = 7944961) B7944961
theorem B1860647 : Blo 1859631 1860647 := bstep (se 1 (by rfl) ⟨1395485, by rfl⟩ : syracuseStep 1860647 = 2790971) B2790971
theorem B23831603 : Blo 1859631 23831603 := bstep (se 1 (by rfl) ⟨17873702, by rfl⟩ : syracuseStep 23831603 = 35747405) B35747405
theorem B1860687 : Blo 1859631 1860687 := bstep (se 1 (by rfl) ⟨1395515, by rfl⟩ : syracuseStep 1860687 = 2791031) B2791031
theorem B1860703 : Blo 1859631 1860703 := bstep (se 1 (by rfl) ⟨1395527, by rfl⟩ : syracuseStep 1860703 = 2791055) B2791055
theorem B6366323 : Blo 1859631 6366323 := bstep (se 1 (by rfl) ⟨4774742, by rfl⟩ : syracuseStep 6366323 = 9549485) B9549485
theorem B3531899 : Blo 1859631 3531899 := bstep (se 1 (by rfl) ⟨2648924, by rfl⟩ : syracuseStep 3531899 = 5297849) B5297849
theorem B1860731 : Blo 1859631 1860731 := bstep (se 1 (by rfl) ⟨1395548, by rfl⟩ : syracuseStep 1860731 = 2791097) B2791097
theorem B1860783 : Blo 1859631 1860783 := bstep (se 1 (by rfl) ⟨1395587, by rfl⟩ : syracuseStep 1860783 = 2791175) B2791175
theorem B1860807 : Blo 1859631 1860807 := bstep (se 1 (by rfl) ⟨1395605, by rfl⟩ : syracuseStep 1860807 = 2791211) B2791211
theorem B1860827 : Blo 1859631 1860827 := bstep (se 1 (by rfl) ⟨1395620, by rfl⟩ : syracuseStep 1860827 = 2791241) B2791241
theorem B8938775 : Blo 1859631 8938775 := bstep (se 1 (by rfl) ⟨6704081, by rfl⟩ : syracuseStep 8938775 = 13408163) B13408163
theorem B1860903 : Blo 1859631 1860903 := bstep (se 1 (by rfl) ⟨1395677, by rfl⟩ : syracuseStep 1860903 = 2791355) B2791355
theorem B1860943 : Blo 1859631 1860943 := bstep (se 1 (by rfl) ⟨1395707, by rfl⟩ : syracuseStep 1860943 = 2791415) B2791415
theorem B1860959 : Blo 1859631 1860959 := bstep (se 1 (by rfl) ⟨1395719, by rfl⟩ : syracuseStep 1860959 = 2791439) B2791439
theorem B1860987 : Blo 1859631 1860987 := bstep (se 1 (by rfl) ⟨1395740, by rfl⟩ : syracuseStep 1860987 = 2791481) B2791481
theorem B3138959 : Blo 1859631 3138959 := bstep (se 1 (by rfl) ⟨2354219, by rfl⟩ : syracuseStep 3138959 = 4708439) B4708439
theorem B1861039 : Blo 1859631 1861039 := bstep (se 1 (by rfl) ⟨1395779, by rfl⟩ : syracuseStep 1861039 = 2791559) B2791559
theorem B10593737 : Blo 1859631 10593737 := bstep (se 2 (by rfl) ⟨3972651, by rfl⟩ : syracuseStep 10593737 = 7945303) B7945303
theorem B1861063 : Blo 1859631 1861063 := bstep (se 1 (by rfl) ⟨1395797, by rfl⟩ : syracuseStep 1861063 = 2791595) B2791595
theorem B1861083 : Blo 1859631 1861083 := bstep (se 1 (by rfl) ⟨1395812, by rfl⟩ : syracuseStep 1861083 = 2791625) B2791625
theorem B1861159 : Blo 1859631 1861159 := bstep (se 1 (by rfl) ⟨1395869, by rfl⟩ : syracuseStep 1861159 = 2791739) B2791739
theorem B3352121 : Blo 1859631 3352121 := bstep (se 2 (by rfl) ⟨1257045, by rfl⟩ : syracuseStep 3352121 = 2514091) B2514091
theorem B1861199 : Blo 1859631 1861199 := bstep (se 1 (by rfl) ⟨1395899, by rfl⟩ : syracuseStep 1861199 = 2791799) B2791799
theorem B1861215 : Blo 1859631 1861215 := bstep (se 1 (by rfl) ⟨1395911, by rfl⟩ : syracuseStep 1861215 = 2791823) B2791823
theorem B3532385 : Blo 1859631 3532385 := bstep (se 2 (by rfl) ⟨1324644, by rfl⟩ : syracuseStep 3532385 = 2649289) B2649289
theorem B4712033 : Blo 1859631 4712033 := bstep (se 2 (by rfl) ⟨1767012, by rfl⟩ : syracuseStep 4712033 = 3534025) B3534025
theorem B3139195 : Blo 1859631 3139195 := bstep (se 1 (by rfl) ⟨2354396, by rfl⟩ : syracuseStep 3139195 = 4708793) B4708793
theorem B4187771 : Blo 1859631 4187771 := bstep (se 1 (by rfl) ⟨3140828, by rfl⟩ : syracuseStep 4187771 = 6281657) B6281657
theorem B1861243 : Blo 1859631 1861243 := bstep (se 1 (by rfl) ⟨1395932, by rfl⟩ : syracuseStep 1861243 = 2791865) B2791865
theorem B6276743 : Blo 1859631 6276743 := bstep (se 1 (by rfl) ⟨4707557, by rfl⟩ : syracuseStep 6276743 = 9415115) B9415115
theorem B1861295 : Blo 1859631 1861295 := bstep (se 1 (by rfl) ⟨1395971, by rfl⟩ : syracuseStep 1861295 = 2791943) B2791943
theorem B6276797 : Blo 1859631 6276797 := bstep (se 3 (by rfl) ⟨1176899, by rfl⟩ : syracuseStep 6276797 = 2353799) B2353799
theorem B1861319 : Blo 1859631 1861319 := bstep (se 1 (by rfl) ⟨1395989, by rfl⟩ : syracuseStep 1861319 = 2791979) B2791979
theorem B1861339 : Blo 1859631 1861339 := bstep (se 1 (by rfl) ⟨1396004, by rfl⟩ : syracuseStep 1861339 = 2792009) B2792009
theorem B4187897 : Blo 1859631 4187897 := bstep (se 2 (by rfl) ⟨1570461, by rfl⟩ : syracuseStep 4187897 = 3140923) B3140923
theorem B1861415 : Blo 1859631 1861415 := bstep (se 1 (by rfl) ⟨1396061, by rfl⟩ : syracuseStep 1861415 = 2792123) B2792123
theorem B9414467 : Blo 1859631 9414467 := bstep (se 1 (by rfl) ⟨7060850, by rfl⟩ : syracuseStep 9414467 = 14121701) B14121701
theorem B7546697 : Blo 1859631 7546697 := bstep (se 2 (by rfl) ⟨2830011, by rfl⟩ : syracuseStep 7546697 = 5660023) B5660023
theorem B1861455 : Blo 1859631 1861455 := bstep (se 1 (by rfl) ⟨1396091, by rfl⟩ : syracuseStep 1861455 = 2792183) B2792183
theorem B6276959 : Blo 1859631 6276959 := bstep (se 1 (by rfl) ⟨4707719, by rfl⟩ : syracuseStep 6276959 = 9415439) B9415439
theorem B1861471 : Blo 1859631 1861471 := bstep (se 1 (by rfl) ⟨1396103, by rfl⟩ : syracuseStep 1861471 = 2792207) B2792207
theorem B1861499 : Blo 1859631 1861499 := bstep (se 1 (by rfl) ⟨1396124, by rfl⟩ : syracuseStep 1861499 = 2792249) B2792249
theorem B1861551 : Blo 1859631 1861551 := bstep (se 1 (by rfl) ⟨1396163, by rfl⟩ : syracuseStep 1861551 = 2792327) B2792327
theorem B3532727 : Blo 1859631 3532727 := bstep (se 1 (by rfl) ⟨2649545, by rfl⟩ : syracuseStep 3532727 = 5299091) B5299091
theorem B3975095 : Blo 1859631 3975095 := bstep (se 1 (by rfl) ⟨2981321, by rfl⟩ : syracuseStep 3975095 = 5962643) B5962643
theorem B1861575 : Blo 1859631 1861575 := bstep (se 1 (by rfl) ⟨1396181, by rfl⟩ : syracuseStep 1861575 = 2792363) B2792363
theorem B1861595 : Blo 1859631 1861595 := bstep (se 1 (by rfl) ⟨1396196, by rfl⟩ : syracuseStep 1861595 = 2792393) B2792393
theorem B6277121 : Blo 1859631 6277121 := bstep (se 2 (by rfl) ⟨2353920, by rfl⟩ : syracuseStep 6277121 = 4707841) B4707841
theorem B3352583 : Blo 1859631 3352583 := bstep (se 1 (by rfl) ⟨2514437, by rfl⟩ : syracuseStep 3352583 = 5028875) B5028875
theorem B4188167 : Blo 1859631 4188167 := bstep (se 1 (by rfl) ⟨3141125, by rfl⟩ : syracuseStep 4188167 = 6282251) B6282251
theorem B232278029 : Blo 1859631 232278029 := bstep (se 3 (by rfl) ⟨43552130, by rfl⟩ : syracuseStep 232278029 = 87104261) B87104261
theorem B7063631 : Blo 1859631 7063631 := bstep (se 1 (by rfl) ⟨5297723, by rfl⟩ : syracuseStep 7063631 = 10595447) B10595447
theorem B4188239 : Blo 1859631 4188239 := bstep (se 1 (by rfl) ⟨3141179, by rfl⟩ : syracuseStep 4188239 = 6282359) B6282359
theorem B22628609 : Blo 1859631 22628609 := bstep (se 2 (by rfl) ⟨8485728, by rfl⟩ : syracuseStep 22628609 = 16971457) B16971457
theorem B35768627 : Blo 1859631 35768627 := bstep (se 1 (by rfl) ⟨26826470, by rfl⟩ : syracuseStep 35768627 = 53652941) B53652941
theorem B9677117 : Blo 1859631 9677117 := bstep (se 3 (by rfl) ⟨1814459, by rfl⟩ : syracuseStep 9677117 = 3628919) B3628919
theorem B3533129 : Blo 1859631 3533129 := bstep (se 2 (by rfl) ⟨1324923, by rfl⟩ : syracuseStep 3533129 = 2649847) B2649847
theorem B19089769 : Blo 1859631 19089769 := bstep (se 2 (by rfl) ⟨7158663, by rfl⟩ : syracuseStep 19089769 = 14317327) B14317327
theorem B2353627 : Blo 1859631 2353627 := bstep (se 1 (by rfl) ⟨1765220, by rfl⟩ : syracuseStep 2353627 = 3530441) B3530441
theorem B5958107 : Blo 1859631 5958107 := bstep (se 1 (by rfl) ⟨4468580, by rfl⟩ : syracuseStep 5958107 = 8937161) B8937161
theorem B3140059 : Blo 1859631 3140059 := bstep (se 1 (by rfl) ⟨2355044, by rfl⟩ : syracuseStep 3140059 = 4710089) B4710089
theorem B4188635 : Blo 1859631 4188635 := bstep (se 1 (by rfl) ⟨3141476, by rfl⟩ : syracuseStep 4188635 = 6282953) B6282953
theorem B3353107 : Blo 1859631 3353107 := bstep (se 1 (by rfl) ⟨2514830, by rfl⟩ : syracuseStep 3353107 = 5029661) B5029661
theorem B22932013 : Blo 1859631 22932013 := bstep (se 3 (by rfl) ⟨4299752, by rfl⟩ : syracuseStep 22932013 = 8599505) B8599505
theorem B6277931 : Blo 1859631 6277931 := bstep (se 1 (by rfl) ⟨4708448, by rfl⟩ : syracuseStep 6277931 = 9416897) B9416897
theorem B3533843 : Blo 1859631 3533843 := bstep (se 1 (by rfl) ⟨2650382, by rfl⟩ : syracuseStep 3533843 = 5300765) B5300765
theorem B6278201 : Blo 1859631 6278201 := bstep (se 2 (by rfl) ⟨2354325, by rfl⟩ : syracuseStep 6278201 = 4708651) B4708651
theorem B3533881 : Blo 1859631 3533881 := bstep (se 2 (by rfl) ⟨1325205, by rfl⟩ : syracuseStep 3533881 = 2650411) B2650411
theorem B3140687 : Blo 1859631 3140687 := bstep (se 1 (by rfl) ⟨2355515, by rfl⟩ : syracuseStep 3140687 = 4711031) B4711031
theorem B9424025 : Blo 1859631 9424025 := bstep (se 2 (by rfl) ⟨3534009, by rfl⟩ : syracuseStep 9424025 = 7068019) B7068019
theorem B6040747 : Blo 1859631 6040747 := bstep (se 1 (by rfl) ⟨4530560, by rfl⟩ : syracuseStep 6040747 = 9061121) B9061121
theorem B3353771 : Blo 1859631 3353771 := bstep (se 1 (by rfl) ⟨2515328, by rfl⟩ : syracuseStep 3353771 = 5030657) B5030657
theorem B6704471 : Blo 1859631 6704471 := bstep (se 1 (by rfl) ⟨5028353, by rfl⟩ : syracuseStep 6704471 = 10056707) B10056707
theorem B3534185 : Blo 1859631 3534185 := bstep (se 2 (by rfl) ⟨1325319, by rfl⟩ : syracuseStep 3534185 = 2650639) B2650639
theorem B6278525 : Blo 1859631 6278525 := bstep (se 3 (by rfl) ⟨1177223, by rfl⟩ : syracuseStep 6278525 = 2354447) B2354447
theorem B10595879 : Blo 1859631 10595879 := bstep (se 1 (by rfl) ⟨7946909, by rfl⟩ : syracuseStep 10595879 = 15893819) B15893819
theorem B14134823 : Blo 1859631 14134823 := bstep (se 1 (by rfl) ⟨10601117, by rfl⟩ : syracuseStep 14134823 = 21202235) B21202235
theorem B6278795 : Blo 1859631 6278795 := bstep (se 1 (by rfl) ⟨4709096, by rfl⟩ : syracuseStep 6278795 = 9418193) B9418193
theorem B8482519 : Blo 1859631 8482519 := bstep (se 1 (by rfl) ⟨6361889, by rfl⟩ : syracuseStep 8482519 = 12723779) B12723779
theorem B11923159 : Blo 1859631 11923159 := bstep (se 1 (by rfl) ⟨8942369, by rfl⟩ : syracuseStep 11923159 = 17884739) B17884739
theorem B13405945 : Blo 1859631 13405945 := bstep (se 2 (by rfl) ⟨5027229, by rfl⟩ : syracuseStep 13405945 = 10054459) B10054459
theorem B3354463 : Blo 1859631 3354463 := bstep (se 1 (by rfl) ⟨2515847, by rfl⟩ : syracuseStep 3354463 = 5031695) B5031695
theorem B2093179 : Blo 1859631 2093179 := bstep (se 1 (by rfl) ⟨1569884, by rfl⟩ : syracuseStep 2093179 = 3139769) B3139769
theorem B4468907 : Blo 1859631 4468907 := bstep (se 1 (by rfl) ⟨3351680, by rfl⟩ : syracuseStep 4468907 = 6703361) B6703361
theorem B2789807 : Blo 1859631 2789807 := bstep (se 1 (by rfl) ⟨2092355, by rfl⟩ : syracuseStep 2789807 = 4184711) B4184711
theorem B7066075 : Blo 1859631 7066075 := bstep (se 1 (by rfl) ⟨5299556, by rfl⟩ : syracuseStep 7066075 = 10599113) B10599113
theorem B2789897 : Blo 1859631 2789897 := bstep (se 2 (by rfl) ⟨1046211, by rfl⟩ : syracuseStep 2789897 = 2092423) B2092423
theorem B6279713 : Blo 1859631 6279713 := bstep (se 2 (by rfl) ⟨2354892, by rfl⟩ : syracuseStep 6279713 = 4709785) B4709785
theorem B2789927 : Blo 1859631 2789927 := bstep (se 1 (by rfl) ⟨2092445, by rfl⟩ : syracuseStep 2789927 = 4184891) B4184891
theorem B2093647 : Blo 1859631 2093647 := bstep (se 1 (by rfl) ⟨1570235, by rfl⟩ : syracuseStep 2093647 = 3140471) B3140471
theorem B2790011 : Blo 1859631 2790011 := bstep (se 1 (by rfl) ⟨2092508, by rfl⟩ : syracuseStep 2790011 = 4185017) B4185017
theorem B12899017 : Blo 1859631 12899017 := bstep (se 2 (by rfl) ⟨4837131, by rfl⟩ : syracuseStep 12899017 = 9674263) B9674263
theorem B2790137 : Blo 1859631 2790137 := bstep (se 2 (by rfl) ⟨1046301, by rfl⟩ : syracuseStep 2790137 = 2092603) B2092603
theorem B6279929 : Blo 1859631 6279929 := bstep (se 2 (by rfl) ⟨2354973, by rfl⟩ : syracuseStep 6279929 = 4709947) B4709947
theorem B9417545 : Blo 1859631 9417545 := bstep (se 2 (by rfl) ⟨3531579, by rfl⟩ : syracuseStep 9417545 = 7063159) B7063159
theorem B2790239 : Blo 1859631 2790239 := bstep (se 1 (by rfl) ⟨2092679, by rfl⟩ : syracuseStep 2790239 = 4185359) B4185359
theorem B2790251 : Blo 1859631 2790251 := bstep (se 1 (by rfl) ⟨2092688, by rfl⟩ : syracuseStep 2790251 = 4185377) B4185377
theorem B5960567 : Blo 1859631 5960567 := bstep (se 1 (by rfl) ⟨4470425, by rfl⟩ : syracuseStep 5960567 = 8940851) B8940851
theorem B14128019 : Blo 1859631 14128019 := bstep (se 1 (by rfl) ⟨10596014, by rfl⟩ : syracuseStep 14128019 = 21192029) B21192029
theorem B4838327 : Blo 1859631 4838327 := bstep (se 1 (by rfl) ⟨3628745, by rfl⟩ : syracuseStep 4838327 = 7257491) B7257491
theorem B2094043 : Blo 1859631 2094043 := bstep (se 1 (by rfl) ⟨1570532, by rfl⟩ : syracuseStep 2094043 = 3141065) B3141065
theorem B4707335 : Blo 1859631 4707335 := bstep (se 1 (by rfl) ⟨3530501, by rfl⟩ : syracuseStep 4707335 = 7061003) B7061003
theorem B6280199 : Blo 1859631 6280199 := bstep (se 1 (by rfl) ⟨4710149, by rfl⟩ : syracuseStep 6280199 = 9420299) B9420299
theorem B3773447 : Blo 1859631 3773447 := bstep (se 1 (by rfl) ⟨2830085, by rfl⟩ : syracuseStep 3773447 = 5660171) B5660171
theorem B17683523 : Blo 1859631 17683523 := bstep (se 1 (by rfl) ⟨13262642, by rfl⟩ : syracuseStep 17683523 = 26525285) B26525285
theorem B21787715 : Blo 1859631 21787715 := bstep (se 1 (by rfl) ⟨16340786, by rfl⟩ : syracuseStep 21787715 = 32681573) B32681573
theorem B2790479 : Blo 1859631 2790479 := bstep (se 1 (by rfl) ⟨2092859, by rfl⟩ : syracuseStep 2790479 = 4185719) B4185719
theorem B6280307 : Blo 1859631 6280307 := bstep (se 1 (by rfl) ⟨4710230, by rfl⟩ : syracuseStep 6280307 = 9420461) B9420461
theorem B10056899 : Blo 1859631 10056899 := bstep (se 1 (by rfl) ⟨7542674, by rfl⟩ : syracuseStep 10056899 = 15085349) B15085349
theorem B2790599 : Blo 1859631 2790599 := bstep (se 1 (by rfl) ⟨2092949, by rfl⟩ : syracuseStep 2790599 = 4185899) B4185899
theorem B10597655 : Blo 1859631 10597655 := bstep (se 1 (by rfl) ⟨7948241, by rfl⟩ : syracuseStep 10597655 = 15896483) B15896483
theorem B2790761 : Blo 1859631 2790761 := bstep (se 2 (by rfl) ⟨1046535, by rfl⟩ : syracuseStep 2790761 = 2093071) B2093071
theorem B3773803 : Blo 1859631 3773803 := bstep (se 1 (by rfl) ⟨2830352, by rfl⟩ : syracuseStep 3773803 = 5660705) B5660705
theorem B6280577 : Blo 1859631 6280577 := bstep (se 2 (by rfl) ⟨2355216, by rfl⟩ : syracuseStep 6280577 = 4710433) B4710433
theorem B4773263 : Blo 1859631 4773263 := bstep (se 1 (by rfl) ⟨3579947, by rfl⟩ : syracuseStep 4773263 = 7159895) B7159895
theorem B2790839 : Blo 1859631 2790839 := bstep (se 1 (by rfl) ⟨2093129, by rfl⟩ : syracuseStep 2790839 = 4186259) B4186259
theorem B18134473 : Blo 1859631 18134473 := bstep (se 2 (by rfl) ⟨6800427, by rfl⟩ : syracuseStep 18134473 = 13600855) B13600855
theorem B2790875 : Blo 1859631 2790875 := bstep (se 1 (by rfl) ⟨2093156, by rfl⟩ : syracuseStep 2790875 = 4186313) B4186313
theorem B6706675 : Blo 1859631 6706675 := bstep (se 1 (by rfl) ⟨5030006, by rfl⟩ : syracuseStep 6706675 = 10060013) B10060013
theorem B7157371 : Blo 1859631 7157371 := bstep (se 1 (by rfl) ⟨5368028, by rfl⟩ : syracuseStep 7157371 = 10736057) B10736057
theorem B7067321 : Blo 1859631 7067321 := bstep (se 2 (by rfl) ⟨2650245, by rfl⟩ : syracuseStep 7067321 = 5300491) B5300491
theorem B6797009 : Blo 1859631 6797009 := bstep (se 2 (by rfl) ⟨2548878, by rfl⟩ : syracuseStep 6797009 = 5097757) B5097757
theorem B7067351 : Blo 1859631 7067351 := bstep (se 1 (by rfl) ⟨5300513, by rfl⟩ : syracuseStep 7067351 = 10601027) B10601027
theorem B6706937 : Blo 1859631 6706937 := bstep (se 2 (by rfl) ⟨2515101, by rfl⟩ : syracuseStep 6706937 = 5030203) B5030203
theorem B28653371 : Blo 1859631 28653371 := bstep (se 1 (by rfl) ⟨21490028, by rfl⟩ : syracuseStep 28653371 = 42980057) B42980057
theorem B14128991 : Blo 1859631 14128991 := bstep (se 1 (by rfl) ⟨10596743, by rfl⟩ : syracuseStep 14128991 = 21193487) B21193487
theorem B6707051 : Blo 1859631 6707051 := bstep (se 1 (by rfl) ⟨5030288, by rfl⟩ : syracuseStep 6707051 = 10060577) B10060577
theorem B6043553 : Blo 1859631 6043553 := bstep (se 2 (by rfl) ⟨2266332, by rfl⟩ : syracuseStep 6043553 = 4532665) B4532665
theorem B2791343 : Blo 1859631 2791343 := bstep (se 1 (by rfl) ⟨2093507, by rfl⟩ : syracuseStep 2791343 = 4187015) B4187015
theorem B6363137 : Blo 1859631 6363137 := bstep (se 2 (by rfl) ⟨2386176, by rfl⟩ : syracuseStep 6363137 = 4772353) B4772353
theorem B6043655 : Blo 1859631 6043655 := bstep (se 1 (by rfl) ⟨4532741, by rfl⟩ : syracuseStep 6043655 = 9065483) B9065483
theorem B2791433 : Blo 1859631 2791433 := bstep (se 2 (by rfl) ⟨1046787, by rfl⟩ : syracuseStep 2791433 = 2093575) B2093575
theorem B2791463 : Blo 1859631 2791463 := bstep (se 1 (by rfl) ⟨2093597, by rfl⟩ : syracuseStep 2791463 = 4187195) B4187195
theorem B2979919 : Blo 1859631 2979919 := bstep (se 1 (by rfl) ⟨2234939, by rfl⟩ : syracuseStep 2979919 = 4469879) B4469879
theorem B9418841 : Blo 1859631 9418841 := bstep (se 2 (by rfl) ⟨3532065, by rfl⟩ : syracuseStep 9418841 = 7064131) B7064131
theorem B20117605 : Blo 1859631 20117605 := bstep (se 4 (by rfl) ⟨1886025, by rfl⟩ : syracuseStep 20117605 = 3772051) B3772051
theorem B2791547 : Blo 1859631 2791547 := bstep (se 1 (by rfl) ⟨2093660, by rfl⟩ : syracuseStep 2791547 = 4187321) B4187321
theorem B5961899 : Blo 1859631 5961899 := bstep (se 1 (by rfl) ⟨4471424, by rfl⟩ : syracuseStep 5961899 = 8942849) B8942849
theorem B6281387 : Blo 1859631 6281387 := bstep (se 1 (by rfl) ⟨4711040, by rfl⟩ : syracuseStep 6281387 = 9422081) B9422081
theorem B2791673 : Blo 1859631 2791673 := bstep (se 2 (by rfl) ⟨1046877, by rfl⟩ : syracuseStep 2791673 = 2093755) B2093755
theorem B26810675 : Blo 1859631 26810675 := bstep (se 1 (by rfl) ⟨20108006, by rfl⟩ : syracuseStep 26810675 = 40216013) B40216013
theorem B2791775 : Blo 1859631 2791775 := bstep (se 1 (by rfl) ⟨2093831, by rfl⟩ : syracuseStep 2791775 = 4187663) B4187663
theorem B2791787 : Blo 1859631 2791787 := bstep (se 1 (by rfl) ⟨2093840, by rfl⟩ : syracuseStep 2791787 = 4187681) B4187681
theorem B4184585 : Blo 1859631 4184585 := bstep (se 2 (by rfl) ⟨1569219, by rfl⟩ : syracuseStep 4184585 = 3138439) B3138439
theorem B5814823 : Blo 1859631 5814823 := bstep (se 1 (by rfl) ⟨4361117, by rfl⟩ : syracuseStep 5814823 = 8722235) B8722235
theorem B18119213 : Blo 1859631 18119213 := bstep (se 3 (by rfl) ⟨3397352, by rfl⟩ : syracuseStep 18119213 = 6794705) B6794705
theorem B2792015 : Blo 1859631 2792015 := bstep (se 1 (by rfl) ⟨2094011, by rfl⟩ : syracuseStep 2792015 = 4188023) B4188023
theorem B6281927 : Blo 1859631 6281927 := bstep (se 1 (by rfl) ⟨4711445, by rfl⟩ : syracuseStep 6281927 = 9422891) B9422891
theorem B2792135 : Blo 1859631 2792135 := bstep (se 1 (by rfl) ⟨2094101, by rfl⟩ : syracuseStep 2792135 = 4188203) B4188203
theorem B4184927 : Blo 1859631 4184927 := bstep (se 1 (by rfl) ⟨3138695, by rfl⟩ : syracuseStep 4184927 = 6277391) B6277391
theorem B2792297 : Blo 1859631 2792297 := bstep (se 2 (by rfl) ⟨1047111, by rfl⟩ : syracuseStep 2792297 = 2094223) B2094223
theorem B2792375 : Blo 1859631 2792375 := bstep (se 1 (by rfl) ⟨2094281, by rfl⟩ : syracuseStep 2792375 = 4188563) B4188563
theorem B2792411 : Blo 1859631 2792411 := bstep (se 1 (by rfl) ⟨2094308, by rfl⟩ : syracuseStep 2792411 = 4188617) B4188617
theorem B4185107 : Blo 1859631 4185107 := bstep (se 1 (by rfl) ⟨3138830, by rfl⟩ : syracuseStep 4185107 = 6277661) B6277661
theorem B7945235 : Blo 1859631 7945235 := bstep (se 1 (by rfl) ⟨5958926, by rfl⟩ : syracuseStep 7945235 = 11917853) B11917853
theorem B8936527 : Blo 1859631 8936527 := bstep (se 1 (by rfl) ⟨6702395, by rfl⟩ : syracuseStep 8936527 = 13404791) B13404791
theorem B14122187 : Blo 1859631 14122187 := bstep (se 1 (by rfl) ⟨10591640, by rfl⟩ : syracuseStep 14122187 = 21183281) B21183281
theorem B8387831 : Blo 1859631 8387831 := bstep (se 1 (by rfl) ⟨6290873, by rfl⟩ : syracuseStep 8387831 = 12581747) B12581747
theorem B4709623 : Blo 1859631 4709623 := bstep (se 1 (by rfl) ⟨3532217, by rfl⟩ : syracuseStep 4709623 = 7064435) B7064435
theorem B4185449 : Blo 1859631 4185449 := bstep (se 2 (by rfl) ⟨1569543, by rfl⟩ : syracuseStep 4185449 = 3139087) B3139087
theorem B2981303 : Blo 1859631 2981303 := bstep (se 1 (by rfl) ⟨2235977, by rfl⟩ : syracuseStep 2981303 = 4471955) B4471955
theorem B6127049 : Blo 1859631 6127049 := bstep (se 2 (by rfl) ⟨2297643, by rfl⟩ : syracuseStep 6127049 = 4595287) B4595287
theorem B4709897 : Blo 1859631 4709897 := bstep (se 2 (by rfl) ⟨1766211, by rfl⟩ : syracuseStep 4709897 = 3532423) B3532423
theorem B4709927 : Blo 1859631 4709927 := bstep (se 1 (by rfl) ⟨3532445, by rfl⟩ : syracuseStep 4709927 = 7064891) B7064891
theorem B6282791 : Blo 1859631 6282791 := bstep (se 1 (by rfl) ⟨4712093, by rfl⟩ : syracuseStep 6282791 = 9424187) B9424187
theorem B6282899 : Blo 1859631 6282899 := bstep (se 1 (by rfl) ⟨4712174, by rfl⟩ : syracuseStep 6282899 = 9424349) B9424349
theorem B7061201 : Blo 1859631 7061201 := bstep (se 2 (by rfl) ⟨2647950, by rfl⟩ : syracuseStep 7061201 = 5295901) B5295901
theorem B5029739 : Blo 1859631 5029739 := bstep (se 1 (by rfl) ⟨3772304, by rfl⟩ : syracuseStep 5029739 = 7544609) B7544609
theorem B4710251 : Blo 1859631 4710251 := bstep (se 1 (by rfl) ⟨3532688, by rfl⟩ : syracuseStep 4710251 = 7065377) B7065377
theorem B4186043 : Blo 1859631 4186043 := bstep (se 1 (by rfl) ⟨3139532, by rfl⟩ : syracuseStep 4186043 = 6279065) B6279065
theorem B3973225 : Blo 1859631 3973225 := bstep (se 2 (by rfl) ⟨1489959, by rfl⟩ : syracuseStep 3973225 = 2979919) B2979919
theorem B1859871 : Blo 1859631 1859871 := bstep (se 1 (by rfl) ⟨1394903, by rfl⟩ : syracuseStep 1859871 = 2789807) B2789807
theorem B1859931 : Blo 1859631 1859931 := bstep (se 1 (by rfl) ⟨1394948, by rfl⟩ : syracuseStep 1859931 = 2789897) B2789897
theorem B4186475 : Blo 1859631 4186475 := bstep (se 1 (by rfl) ⟨3139856, by rfl⟩ : syracuseStep 4186475 = 6279713) B6279713
theorem B1859951 : Blo 1859631 1859951 := bstep (se 1 (by rfl) ⟨1394963, by rfl⟩ : syracuseStep 1859951 = 2789927) B2789927
theorem B1860007 : Blo 1859631 1860007 := bstep (se 1 (by rfl) ⟨1395005, by rfl⟩ : syracuseStep 1860007 = 2790011) B2790011
theorem B25453025 : Blo 1859631 25453025 := bstep (se 2 (by rfl) ⟨9544884, by rfl⟩ : syracuseStep 25453025 = 19089769) B19089769
theorem B1860091 : Blo 1859631 1860091 := bstep (se 1 (by rfl) ⟨1395068, by rfl⟩ : syracuseStep 1860091 = 2790137) B2790137
theorem B4186619 : Blo 1859631 4186619 := bstep (se 1 (by rfl) ⟨3139964, by rfl⟩ : syracuseStep 4186619 = 6279929) B6279929
theorem B1860159 : Blo 1859631 1860159 := bstep (se 1 (by rfl) ⟨1395119, by rfl⟩ : syracuseStep 1860159 = 2790239) B2790239
theorem B1860167 : Blo 1859631 1860167 := bstep (se 1 (by rfl) ⟨1395125, by rfl⟩ : syracuseStep 1860167 = 2790251) B2790251
theorem B3973711 : Blo 1859631 3973711 := bstep (se 1 (by rfl) ⟨2980283, by rfl⟩ : syracuseStep 3973711 = 5960567) B5960567
theorem B3138169 : Blo 1859631 3138169 := bstep (se 2 (by rfl) ⟨1176813, by rfl⟩ : syracuseStep 3138169 = 2353627) B2353627
theorem B4186745 : Blo 1859631 4186745 := bstep (se 2 (by rfl) ⟨1570029, by rfl⟩ : syracuseStep 4186745 = 3140059) B3140059
theorem B9421433 : Blo 1859631 9421433 := bstep (se 2 (by rfl) ⟨3533037, by rfl⟩ : syracuseStep 9421433 = 7066075) B7066075
theorem B7062187 : Blo 1859631 7062187 := bstep (se 1 (by rfl) ⟨5296640, by rfl⟩ : syracuseStep 7062187 = 10593281) B10593281
theorem B3138223 : Blo 1859631 3138223 := bstep (se 1 (by rfl) ⟨2353667, by rfl⟩ : syracuseStep 3138223 = 4707335) B4707335
theorem B4186799 : Blo 1859631 4186799 := bstep (se 1 (by rfl) ⟨3140099, by rfl⟩ : syracuseStep 4186799 = 6280199) B6280199
theorem B2515631 : Blo 1859631 2515631 := bstep (se 1 (by rfl) ⟨1886723, by rfl⟩ : syracuseStep 2515631 = 3773447) B3773447
theorem B11789015 : Blo 1859631 11789015 := bstep (se 1 (by rfl) ⟨8841761, by rfl⟩ : syracuseStep 11789015 = 17683523) B17683523
theorem B1860319 : Blo 1859631 1860319 := bstep (se 1 (by rfl) ⟨1395239, by rfl⟩ : syracuseStep 1860319 = 2790479) B2790479
theorem B4186871 : Blo 1859631 4186871 := bstep (se 1 (by rfl) ⟨3140153, by rfl⟩ : syracuseStep 4186871 = 6280307) B6280307
theorem B1860399 : Blo 1859631 1860399 := bstep (se 1 (by rfl) ⟨1395299, by rfl⟩ : syracuseStep 1860399 = 2790599) B2790599
theorem B1860507 : Blo 1859631 1860507 := bstep (se 1 (by rfl) ⟨1395380, by rfl⟩ : syracuseStep 1860507 = 2790761) B2790761
theorem B4187051 : Blo 1859631 4187051 := bstep (se 1 (by rfl) ⟨3140288, by rfl⟩ : syracuseStep 4187051 = 6280577) B6280577
theorem B1860559 : Blo 1859631 1860559 := bstep (se 1 (by rfl) ⟨1395419, by rfl⟩ : syracuseStep 1860559 = 2790839) B2790839
theorem B7062491 : Blo 1859631 7062491 := bstep (se 1 (by rfl) ⟨5296868, by rfl⟩ : syracuseStep 7062491 = 10593737) B10593737
theorem B1860583 : Blo 1859631 1860583 := bstep (se 1 (by rfl) ⟨1395437, by rfl⟩ : syracuseStep 1860583 = 2790875) B2790875
theorem B4711547 : Blo 1859631 4711547 := bstep (se 1 (by rfl) ⟨3533660, by rfl⟩ : syracuseStep 4711547 = 7067321) B7067321
theorem B4531339 : Blo 1859631 4531339 := bstep (se 1 (by rfl) ⟨3398504, by rfl⟩ : syracuseStep 4531339 = 6797009) B6797009
theorem B4711567 : Blo 1859631 4711567 := bstep (se 1 (by rfl) ⟨3533675, by rfl⟩ : syracuseStep 4711567 = 7067351) B7067351
theorem B6276311 : Blo 1859631 6276311 := bstep (se 1 (by rfl) ⟨4707233, by rfl⟩ : syracuseStep 6276311 = 9414467) B9414467
theorem B5031131 : Blo 1859631 5031131 := bstep (se 1 (by rfl) ⟨3773348, by rfl⟩ : syracuseStep 5031131 = 7546697) B7546697
theorem B1860895 : Blo 1859631 1860895 := bstep (se 1 (by rfl) ⟨1395671, by rfl⟩ : syracuseStep 1860895 = 2791343) B2791343
theorem B1860955 : Blo 1859631 1860955 := bstep (se 1 (by rfl) ⟨1395716, by rfl⟩ : syracuseStep 1860955 = 2791433) B2791433
theorem B1860975 : Blo 1859631 1860975 := bstep (se 1 (by rfl) ⟨1395731, by rfl⟩ : syracuseStep 1860975 = 2791463) B2791463
theorem B4711841 : Blo 1859631 4711841 := bstep (se 2 (by rfl) ⟨1766940, by rfl⟩ : syracuseStep 4711841 = 3533881) B3533881
theorem B1861031 : Blo 1859631 1861031 := bstep (se 1 (by rfl) ⟨1395773, by rfl⟩ : syracuseStep 1861031 = 2791547) B2791547
theorem B3974599 : Blo 1859631 3974599 := bstep (se 1 (by rfl) ⟨2980949, by rfl⟩ : syracuseStep 3974599 = 5961899) B5961899
theorem B4187591 : Blo 1859631 4187591 := bstep (se 1 (by rfl) ⟨3140693, by rfl⟩ : syracuseStep 4187591 = 6281387) B6281387
theorem B1861115 : Blo 1859631 1861115 := bstep (se 1 (by rfl) ⟨1395836, by rfl⟩ : syracuseStep 1861115 = 2791673) B2791673
theorem B8054329 : Blo 1859631 8054329 := bstep (se 2 (by rfl) ⟨3020373, by rfl⟩ : syracuseStep 8054329 = 6040747) B6040747
theorem B1861183 : Blo 1859631 1861183 := bstep (se 1 (by rfl) ⟨1395887, by rfl⟩ : syracuseStep 1861183 = 2791775) B2791775
theorem B1861191 : Blo 1859631 1861191 := bstep (se 1 (by rfl) ⟨1395893, by rfl⟩ : syracuseStep 1861191 = 2791787) B2791787
theorem B1861343 : Blo 1859631 1861343 := bstep (se 1 (by rfl) ⟨1396007, by rfl⟩ : syracuseStep 1861343 = 2792015) B2792015
theorem B4187951 : Blo 1859631 4187951 := bstep (se 1 (by rfl) ⟨3140963, by rfl⟩ : syracuseStep 4187951 = 6281927) B6281927
theorem B1861423 : Blo 1859631 1861423 := bstep (se 1 (by rfl) ⟨1396067, by rfl⟩ : syracuseStep 1861423 = 2792135) B2792135
theorem B5031737 : Blo 1859631 5031737 := bstep (se 2 (by rfl) ⟨1886901, by rfl⟩ : syracuseStep 5031737 = 3773803) B3773803
theorem B1861531 : Blo 1859631 1861531 := bstep (se 1 (by rfl) ⟨1396148, by rfl⟩ : syracuseStep 1861531 = 2792297) B2792297
theorem B1861583 : Blo 1859631 1861583 := bstep (se 1 (by rfl) ⟨1396187, by rfl⟩ : syracuseStep 1861583 = 2792375) B2792375
theorem B1861607 : Blo 1859631 1861607 := bstep (se 1 (by rfl) ⟨1396205, by rfl⟩ : syracuseStep 1861607 = 2792411) B2792411
theorem B9414791 : Blo 1859631 9414791 := bstep (se 1 (by rfl) ⟨7061093, by rfl⟩ : syracuseStep 9414791 = 14122187) B14122187
theorem B3139931 : Blo 1859631 3139931 := bstep (se 1 (by rfl) ⟨2354948, by rfl⟩ : syracuseStep 3139931 = 4709897) B4709897
theorem B7063919 : Blo 1859631 7063919 := bstep (se 1 (by rfl) ⟨5297939, by rfl⟩ : syracuseStep 7063919 = 10595879) B10595879
theorem B3139951 : Blo 1859631 3139951 := bstep (se 1 (by rfl) ⟨2354963, by rfl⟩ : syracuseStep 3139951 = 4709927) B4709927
theorem B9423215 : Blo 1859631 9423215 := bstep (se 1 (by rfl) ⟨7067411, by rfl⟩ : syracuseStep 9423215 = 14134823) B14134823
theorem B4188527 : Blo 1859631 4188527 := bstep (se 1 (by rfl) ⟨3141395, by rfl⟩ : syracuseStep 4188527 = 6282791) B6282791
theorem B4188599 : Blo 1859631 4188599 := bstep (se 1 (by rfl) ⟨3141449, by rfl⟩ : syracuseStep 4188599 = 6282899) B6282899
theorem B3353159 : Blo 1859631 3353159 := bstep (se 1 (by rfl) ⟨2514869, by rfl⟩ : syracuseStep 3353159 = 5029739) B5029739
theorem B3140167 : Blo 1859631 3140167 := bstep (se 1 (by rfl) ⟨2355125, by rfl⟩ : syracuseStep 3140167 = 4710251) B4710251
theorem B16968365 : Blo 1859631 16968365 := bstep (se 3 (by rfl) ⟨3181568, by rfl⟩ : syracuseStep 16968365 = 6363137) B6363137
theorem B16116413 : Blo 1859631 16116413 := bstep (se 3 (by rfl) ⟨3021827, by rfl⟩ : syracuseStep 16116413 = 6043655) B6043655
theorem B26823473 : Blo 1859631 26823473 := bstep (se 2 (by rfl) ⟨10058802, by rfl⟩ : syracuseStep 26823473 = 20117605) B20117605
theorem B58100573 : Blo 1859631 58100573 := bstep (se 3 (by rfl) ⟨10893857, by rfl⟩ : syracuseStep 58100573 = 21787715) B21787715
theorem B16976861 : Blo 1859631 16976861 := bstep (se 3 (by rfl) ⟨3183161, by rfl⟩ : syracuseStep 16976861 = 6366323) B6366323
theorem B3140599 : Blo 1859631 3140599 := bstep (se 1 (by rfl) ⟨2355449, by rfl⟩ : syracuseStep 3140599 = 4710899) B4710899
theorem B6450299 : Blo 1859631 6450299 := bstep (se 1 (by rfl) ⟨4837724, by rfl⟩ : syracuseStep 6450299 = 9675449) B9675449
theorem B6278363 : Blo 1859631 6278363 := bstep (se 1 (by rfl) ⟨4708772, by rfl⟩ : syracuseStep 6278363 = 9417545) B9417545
theorem B3140903 : Blo 1859631 3140903 := bstep (se 1 (by rfl) ⟨2355677, by rfl⟩ : syracuseStep 3140903 = 4711355) B4711355
theorem B22367549 : Blo 1859631 22367549 := bstep (se 3 (by rfl) ⟨4193915, by rfl⟩ : syracuseStep 22367549 = 8387831) B8387831
theorem B15887735 : Blo 1859631 15887735 := bstep (se 1 (by rfl) ⟨11915801, by rfl⟩ : syracuseStep 15887735 = 23831603) B23831603
theorem B7753097 : Blo 1859631 7753097 := bstep (se 2 (by rfl) ⟨2907411, by rfl⟩ : syracuseStep 7753097 = 5814823) B5814823
theorem B30576017 : Blo 1859631 30576017 := bstep (se 2 (by rfl) ⟨11466006, by rfl⟩ : syracuseStep 30576017 = 22932013) B22932013
theorem B2354599 : Blo 1859631 2354599 := bstep (se 1 (by rfl) ⟨1765949, by rfl⟩ : syracuseStep 2354599 = 3531899) B3531899
theorem B5959183 : Blo 1859631 5959183 := bstep (se 1 (by rfl) ⟨4469387, by rfl⟩ : syracuseStep 5959183 = 8938775) B8938775
theorem B7065103 : Blo 1859631 7065103 := bstep (se 1 (by rfl) ⟨5298827, by rfl⟩ : syracuseStep 7065103 = 10597655) B10597655
theorem B17878589 : Blo 1859631 17878589 := bstep (se 3 (by rfl) ⟨3352235, by rfl⟩ : syracuseStep 17878589 = 6704471) B6704471
theorem B2092639 : Blo 1859631 2092639 := bstep (se 1 (by rfl) ⟨1569479, by rfl⟩ : syracuseStep 2092639 = 3138959) B3138959
theorem B17198689 : Blo 1859631 17198689 := bstep (se 2 (by rfl) ⟨6449508, by rfl⟩ : syracuseStep 17198689 = 12899017) B12899017
theorem B2354923 : Blo 1859631 2354923 := bstep (se 1 (by rfl) ⟨1766192, by rfl⟩ : syracuseStep 2354923 = 3532385) B3532385
theorem B3141355 : Blo 1859631 3141355 := bstep (se 1 (by rfl) ⟨2356016, by rfl⟩ : syracuseStep 3141355 = 4712033) B4712033
theorem B16338797 : Blo 1859631 16338797 := bstep (se 3 (by rfl) ⟨3063524, by rfl⟩ : syracuseStep 16338797 = 6127049) B6127049
theorem B2355151 : Blo 1859631 2355151 := bstep (se 1 (by rfl) ⟨1766363, by rfl⟩ : syracuseStep 2355151 = 3532727) B3532727
theorem B6279227 : Blo 1859631 6279227 := bstep (se 1 (by rfl) ⟨4709420, by rfl⟩ : syracuseStep 6279227 = 9418841) B9418841
theorem B11915369 : Blo 1859631 11915369 := bstep (se 2 (by rfl) ⟨4468263, by rfl⟩ : syracuseStep 11915369 = 8936527) B8936527
theorem B15085739 : Blo 1859631 15085739 := bstep (se 1 (by rfl) ⟨11314304, by rfl⟩ : syracuseStep 15085739 = 22628609) B22628609
theorem B6451411 : Blo 1859631 6451411 := bstep (se 1 (by rfl) ⟨4838558, by rfl⟩ : syracuseStep 6451411 = 9677117) B9677117
theorem B2355419 : Blo 1859631 2355419 := bstep (se 1 (by rfl) ⟨1766564, by rfl⟩ : syracuseStep 2355419 = 3533129) B3533129
theorem B6279497 : Blo 1859631 6279497 := bstep (se 2 (by rfl) ⟨2354811, by rfl⟩ : syracuseStep 6279497 = 4709623) B4709623
theorem B2789723 : Blo 1859631 2789723 := bstep (se 1 (by rfl) ⟨2092292, by rfl⟩ : syracuseStep 2789723 = 4184585) B4184585
theorem B12079475 : Blo 1859631 12079475 := bstep (se 1 (by rfl) ⟨9059606, by rfl⟩ : syracuseStep 12079475 = 18119213) B18119213
theorem B2789951 : Blo 1859631 2789951 := bstep (se 1 (by rfl) ⟨2092463, by rfl⟩ : syracuseStep 2789951 = 4184927) B4184927
theorem B24179297 : Blo 1859631 24179297 := bstep (se 2 (by rfl) ⟨9067236, by rfl⟩ : syracuseStep 24179297 = 18134473) B18134473
theorem B8942233 : Blo 1859631 8942233 := bstep (se 2 (by rfl) ⟨3353337, by rfl⟩ : syracuseStep 8942233 = 6706675) B6706675
theorem B2790071 : Blo 1859631 2790071 := bstep (se 1 (by rfl) ⟨2092553, by rfl⟩ : syracuseStep 2790071 = 4185107) B4185107
theorem B5296823 : Blo 1859631 5296823 := bstep (se 1 (by rfl) ⟨3972617, by rfl⟩ : syracuseStep 5296823 = 7945235) B7945235
theorem B2355895 : Blo 1859631 2355895 := bstep (se 1 (by rfl) ⟨1766921, by rfl⟩ : syracuseStep 2355895 = 3533843) B3533843
theorem B2093791 : Blo 1859631 2093791 := bstep (se 1 (by rfl) ⟨1570343, by rfl⟩ : syracuseStep 2093791 = 3140687) B3140687
theorem B2790299 : Blo 1859631 2790299 := bstep (se 1 (by rfl) ⟨2092724, by rfl⟩ : syracuseStep 2790299 = 4185449) B4185449
theorem B2356123 : Blo 1859631 2356123 := bstep (se 1 (by rfl) ⟨1767092, by rfl⟩ : syracuseStep 2356123 = 3534185) B3534185
theorem B11310025 : Blo 1859631 11310025 := bstep (se 2 (by rfl) ⟨4241259, by rfl⟩ : syracuseStep 11310025 = 8482519) B8482519
theorem B15897545 : Blo 1859631 15897545 := bstep (se 2 (by rfl) ⟨5961579, by rfl⟩ : syracuseStep 15897545 = 11923159) B11923159
theorem B1987535 : Blo 1859631 1987535 := bstep (se 1 (by rfl) ⟨1490651, by rfl⟩ : syracuseStep 1987535 = 2981303) B2981303
theorem B4707467 : Blo 1859631 4707467 := bstep (se 1 (by rfl) ⟨3530600, by rfl⟩ : syracuseStep 4707467 = 7061201) B7061201
theorem B2790695 : Blo 1859631 2790695 := bstep (se 1 (by rfl) ⟨2093021, by rfl⟩ : syracuseStep 2790695 = 4186043) B4186043
theorem B4707679 : Blo 1859631 4707679 := bstep (se 1 (by rfl) ⟨3530759, by rfl⟩ : syracuseStep 4707679 = 7061519) B7061519
theorem B2790779 : Blo 1859631 2790779 := bstep (se 1 (by rfl) ⟨2093084, by rfl⟩ : syracuseStep 2790779 = 4186169) B4186169
theorem B2979271 : Blo 1859631 2979271 := bstep (se 1 (by rfl) ⟨2234453, by rfl⟩ : syracuseStep 2979271 = 4468907) B4468907
theorem B2790905 : Blo 1859631 2790905 := bstep (se 2 (by rfl) ⟨1046589, by rfl⟩ : syracuseStep 2790905 = 2093179) B2093179
theorem B2791007 : Blo 1859631 2791007 := bstep (se 1 (by rfl) ⟨2093255, by rfl⟩ : syracuseStep 2791007 = 4186511) B4186511
theorem B2791223 : Blo 1859631 2791223 := bstep (se 1 (by rfl) ⟨2093417, by rfl⟩ : syracuseStep 2791223 = 4186835) B4186835
theorem B26818397 : Blo 1859631 26818397 := bstep (se 3 (by rfl) ⟨5028449, by rfl⟩ : syracuseStep 26818397 = 10056899) B10056899
theorem B9418679 : Blo 1859631 9418679 := bstep (se 1 (by rfl) ⟨7064009, by rfl⟩ : syracuseStep 9418679 = 14128019) B14128019
theorem B3225551 : Blo 1859631 3225551 := bstep (se 1 (by rfl) ⟨2419163, by rfl⟩ : syracuseStep 3225551 = 4838327) B4838327
theorem B4470809 : Blo 1859631 4470809 := bstep (se 2 (by rfl) ⟨1676553, by rfl⟩ : syracuseStep 4470809 = 3353107) B3353107
theorem B2791529 : Blo 1859631 2791529 := bstep (se 2 (by rfl) ⟨1046823, by rfl⟩ : syracuseStep 2791529 = 2093647) B2093647
theorem B2234747 : Blo 1859631 2234747 := bstep (se 1 (by rfl) ⟨1676060, by rfl⟩ : syracuseStep 2234747 = 3352121) B3352121
theorem B12728701 : Blo 1859631 12728701 := bstep (se 3 (by rfl) ⟨2386631, by rfl⟩ : syracuseStep 12728701 = 4773263) B4773263
theorem B2791847 : Blo 1859631 2791847 := bstep (se 1 (by rfl) ⟨2093885, by rfl⟩ : syracuseStep 2791847 = 4187771) B4187771
theorem B4184495 : Blo 1859631 4184495 := bstep (se 1 (by rfl) ⟨3138371, by rfl⟩ : syracuseStep 4184495 = 6276743) B6276743
theorem B4184531 : Blo 1859631 4184531 := bstep (se 1 (by rfl) ⟨3138398, by rfl⟩ : syracuseStep 4184531 = 6276797) B6276797
theorem B4471291 : Blo 1859631 4471291 := bstep (se 1 (by rfl) ⟨3353468, by rfl⟩ : syracuseStep 4471291 = 6706937) B6706937
theorem B2791931 : Blo 1859631 2791931 := bstep (se 1 (by rfl) ⟨2093948, by rfl⟩ : syracuseStep 2791931 = 4187897) B4187897
theorem B19102247 : Blo 1859631 19102247 := bstep (se 1 (by rfl) ⟨14326685, by rfl⟩ : syracuseStep 19102247 = 28653371) B28653371
theorem B4184639 : Blo 1859631 4184639 := bstep (se 1 (by rfl) ⟨3138479, by rfl⟩ : syracuseStep 4184639 = 6276959) B6276959
theorem B9419327 : Blo 1859631 9419327 := bstep (se 1 (by rfl) ⟨7064495, by rfl⟩ : syracuseStep 9419327 = 14128991) B14128991
theorem B4471367 : Blo 1859631 4471367 := bstep (se 1 (by rfl) ⟨3353525, by rfl⟩ : syracuseStep 4471367 = 6707051) B6707051
theorem B4029035 : Blo 1859631 4029035 := bstep (se 1 (by rfl) ⟨3021776, by rfl⟩ : syracuseStep 4029035 = 6043553) B6043553
theorem B2792057 : Blo 1859631 2792057 := bstep (se 2 (by rfl) ⟨1047021, by rfl⟩ : syracuseStep 2792057 = 2094043) B2094043
theorem B4184747 : Blo 1859631 4184747 := bstep (se 1 (by rfl) ⟨3138560, by rfl⟩ : syracuseStep 4184747 = 6277121) B6277121
theorem B2235055 : Blo 1859631 2235055 := bstep (se 1 (by rfl) ⟨1676291, by rfl⟩ : syracuseStep 2235055 = 3352583) B3352583
theorem B2792111 : Blo 1859631 2792111 := bstep (se 1 (by rfl) ⟨2094083, by rfl⟩ : syracuseStep 2792111 = 4188167) B4188167
theorem B154852019 : Blo 1859631 154852019 := bstep (se 1 (by rfl) ⟨116139014, by rfl⟩ : syracuseStep 154852019 = 232278029) B232278029
theorem B4709087 : Blo 1859631 4709087 := bstep (se 1 (by rfl) ⟨3531815, by rfl⟩ : syracuseStep 4709087 = 7063631) B7063631
theorem B2792159 : Blo 1859631 2792159 := bstep (se 1 (by rfl) ⟨2094119, by rfl⟩ : syracuseStep 2792159 = 4188239) B4188239
theorem B17873783 : Blo 1859631 17873783 := bstep (se 1 (by rfl) ⟨13405337, by rfl⟩ : syracuseStep 17873783 = 26810675) B26810675
theorem B23845751 : Blo 1859631 23845751 := bstep (se 1 (by rfl) ⟨17884313, by rfl⟩ : syracuseStep 23845751 = 35768627) B35768627
theorem B3972071 : Blo 1859631 3972071 := bstep (se 1 (by rfl) ⟨2979053, by rfl⟩ : syracuseStep 3972071 = 5958107) B5958107
theorem B2792423 : Blo 1859631 2792423 := bstep (se 1 (by rfl) ⟨2094317, by rfl⟩ : syracuseStep 2792423 = 4188635) B4188635
theorem B4185287 : Blo 1859631 4185287 := bstep (se 1 (by rfl) ⟨3138965, by rfl⟩ : syracuseStep 4185287 = 6277931) B6277931
theorem B4185467 : Blo 1859631 4185467 := bstep (se 1 (by rfl) ⟨3139100, by rfl⟩ : syracuseStep 4185467 = 6278201) B6278201
theorem B6282683 : Blo 1859631 6282683 := bstep (se 1 (by rfl) ⟨4712012, by rfl⟩ : syracuseStep 6282683 = 9424025) B9424025
theorem B2235847 : Blo 1859631 2235847 := bstep (se 1 (by rfl) ⟨1676885, by rfl⟩ : syracuseStep 2235847 = 3353771) B3353771
theorem B9543161 : Blo 1859631 9543161 := bstep (se 2 (by rfl) ⟨3578685, by rfl⟩ : syracuseStep 9543161 = 7157371) B7157371
theorem B4185593 : Blo 1859631 4185593 := bstep (se 2 (by rfl) ⟨1569597, by rfl⟩ : syracuseStep 4185593 = 3139195) B3139195
theorem B4185683 : Blo 1859631 4185683 := bstep (se 1 (by rfl) ⟨3139262, by rfl⟩ : syracuseStep 4185683 = 6278525) B6278525
theorem B17874593 : Blo 1859631 17874593 := bstep (se 2 (by rfl) ⟨6702972, by rfl⟩ : syracuseStep 17874593 = 13405945) B13405945
theorem B4185863 : Blo 1859631 4185863 := bstep (se 1 (by rfl) ⟨3139397, by rfl⟩ : syracuseStep 4185863 = 6278795) B6278795
theorem B4472617 : Blo 1859631 4472617 := bstep (se 2 (by rfl) ⟨1677231, by rfl⟩ : syracuseStep 4472617 = 3354463) B3354463
theorem B10600253 : Blo 1859631 10600253 := bstep (se 3 (by rfl) ⟨1987547, by rfl⟩ : syracuseStep 10600253 = 3975095) B3975095
theorem B4186151 : Blo 1859631 4186151 := bstep (se 1 (by rfl) ⟨3139613, by rfl⟩ : syracuseStep 4186151 = 6279227) B6279227
theorem B4186331 : Blo 1859631 4186331 := bstep (se 1 (by rfl) ⟨3139748, by rfl⟩ : syracuseStep 4186331 = 6279497) B6279497
theorem B1859815 : Blo 1859631 1859815 := bstep (se 1 (by rfl) ⟨1394861, by rfl⟩ : syracuseStep 1859815 = 2789723) B2789723
theorem B8052983 : Blo 1859631 8052983 := bstep (se 1 (by rfl) ⟨6039737, by rfl⟩ : syracuseStep 8052983 = 12079475) B12079475
theorem B8601881 : Blo 1859631 8601881 := bstep (se 2 (by rfl) ⟨3225705, by rfl⟩ : syracuseStep 8601881 = 6451411) B6451411
theorem B1859967 : Blo 1859631 1859967 := bstep (se 1 (by rfl) ⟨1394975, by rfl⟩ : syracuseStep 1859967 = 2789951) B2789951
theorem B1860047 : Blo 1859631 1860047 := bstep (se 1 (by rfl) ⟨1395035, by rfl⟩ : syracuseStep 1860047 = 2790071) B2790071
theorem B3531215 : Blo 1859631 3531215 := bstep (se 1 (by rfl) ⟨2648411, by rfl⟩ : syracuseStep 3531215 = 5296823) B5296823
theorem B4186601 : Blo 1859631 4186601 := bstep (se 2 (by rfl) ⟨1569975, by rfl⟩ : syracuseStep 4186601 = 3139951) B3139951
theorem B1860199 : Blo 1859631 1860199 := bstep (se 1 (by rfl) ⟨1395149, by rfl⟩ : syracuseStep 1860199 = 2790299) B2790299
theorem B3138311 : Blo 1859631 3138311 := bstep (se 1 (by rfl) ⟨2353733, by rfl⟩ : syracuseStep 3138311 = 4707467) B4707467
theorem B4186889 : Blo 1859631 4186889 := bstep (se 2 (by rfl) ⟨1570083, by rfl⟩ : syracuseStep 4186889 = 3140167) B3140167
theorem B1860463 : Blo 1859631 1860463 := bstep (se 1 (by rfl) ⟨1395347, by rfl⟩ : syracuseStep 1860463 = 2790695) B2790695
theorem B1860519 : Blo 1859631 1860519 := bstep (se 1 (by rfl) ⟨1395389, by rfl⟩ : syracuseStep 1860519 = 2790779) B2790779
theorem B1860603 : Blo 1859631 1860603 := bstep (se 1 (by rfl) ⟨1395452, by rfl⟩ : syracuseStep 1860603 = 2790905) B2790905
theorem B1860671 : Blo 1859631 1860671 := bstep (se 1 (by rfl) ⟨1395503, by rfl⟩ : syracuseStep 1860671 = 2791007) B2791007
theorem B1860815 : Blo 1859631 1860815 := bstep (se 1 (by rfl) ⟨1395611, by rfl⟩ : syracuseStep 1860815 = 2791223) B2791223
theorem B4187465 : Blo 1859631 4187465 := bstep (se 2 (by rfl) ⟨1570299, by rfl⟩ : syracuseStep 4187465 = 3140599) B3140599
theorem B1861019 : Blo 1859631 1861019 := bstep (se 1 (by rfl) ⟨1395764, by rfl⟩ : syracuseStep 1861019 = 2791529) B2791529
theorem B6276527 : Blo 1859631 6276527 := bstep (se 1 (by rfl) ⟨4707395, by rfl⟩ : syracuseStep 6276527 = 9414791) B9414791
theorem B1861231 : Blo 1859631 1861231 := bstep (se 1 (by rfl) ⟨1395923, by rfl⟩ : syracuseStep 1861231 = 2791847) B2791847
theorem B1861287 : Blo 1859631 1861287 := bstep (se 1 (by rfl) ⟨1395965, by rfl⟩ : syracuseStep 1861287 = 2791931) B2791931
theorem B1861371 : Blo 1859631 1861371 := bstep (se 1 (by rfl) ⟨1396028, by rfl⟩ : syracuseStep 1861371 = 2792057) B2792057
theorem B1861407 : Blo 1859631 1861407 := bstep (se 1 (by rfl) ⟨1396055, by rfl⟩ : syracuseStep 1861407 = 2792111) B2792111
theorem B6276905 : Blo 1859631 6276905 := bstep (se 2 (by rfl) ⟨2353839, by rfl⟩ : syracuseStep 6276905 = 4707679) B4707679
theorem B3139391 : Blo 1859631 3139391 := bstep (se 1 (by rfl) ⟨2354543, by rfl⟩ : syracuseStep 3139391 = 4709087) B4709087
theorem B1861439 : Blo 1859631 1861439 := bstep (se 1 (by rfl) ⟨1396079, by rfl⟩ : syracuseStep 1861439 = 2792159) B2792159
theorem B3139465 : Blo 1859631 3139465 := bstep (se 2 (by rfl) ⟨1177299, by rfl⟩ : syracuseStep 3139465 = 2354599) B2354599
theorem B38733715 : Blo 1859631 38733715 := bstep (se 1 (by rfl) ⟨29050286, by rfl⟩ : syracuseStep 38733715 = 58100573) B58100573
theorem B2648047 : Blo 1859631 2648047 := bstep (se 1 (by rfl) ⟨1986035, by rfl⟩ : syracuseStep 2648047 = 3972071) B3972071
theorem B1861615 : Blo 1859631 1861615 := bstep (se 1 (by rfl) ⟨1396211, by rfl⟩ : syracuseStep 1861615 = 2792423) B2792423
theorem B22931585 : Blo 1859631 22931585 := bstep (se 2 (by rfl) ⟨8599344, by rfl⟩ : syracuseStep 22931585 = 17198689) B17198689
theorem B14911699 : Blo 1859631 14911699 := bstep (se 1 (by rfl) ⟨11183774, by rfl⟩ : syracuseStep 14911699 = 22367549) B22367549
theorem B125749493 : Blo 1859631 125749493 := bstep (se 5 (by rfl) ⟨5894507, by rfl⟩ : syracuseStep 125749493 = 11789015) B11789015
theorem B20384011 : Blo 1859631 20384011 := bstep (se 1 (by rfl) ⟨15288008, by rfl⟩ : syracuseStep 20384011 = 30576017) B30576017
theorem B4188455 : Blo 1859631 4188455 := bstep (se 1 (by rfl) ⟨3141341, by rfl⟩ : syracuseStep 4188455 = 6282683) B6282683
theorem B3139897 : Blo 1859631 3139897 := bstep (se 2 (by rfl) ⟨1177461, by rfl⟩ : syracuseStep 3139897 = 2354923) B2354923
theorem B4188473 : Blo 1859631 4188473 := bstep (se 2 (by rfl) ⟨1570677, by rfl⟩ : syracuseStep 4188473 = 3141355) B3141355
theorem B3140201 : Blo 1859631 3140201 := bstep (se 2 (by rfl) ⟨1177575, by rfl⟩ : syracuseStep 3140201 = 2355151) B2355151
theorem B11922157 : Blo 1859631 11922157 := bstep (se 3 (by rfl) ⟨2235404, by rfl⟩ : syracuseStep 11922157 = 4470809) B4470809
theorem B16968683 : Blo 1859631 16968683 := bstep (se 1 (by rfl) ⟨12726512, by rfl⟩ : syracuseStep 16968683 = 25453025) B25453025
theorem B3141031 : Blo 1859631 3141031 := bstep (se 1 (by rfl) ⟨2355773, by rfl⟩ : syracuseStep 3141031 = 4711547) B4711547
theorem B11922977 : Blo 1859631 11922977 := bstep (se 2 (by rfl) ⟨4471116, by rfl⟩ : syracuseStep 11922977 = 8942233) B8942233
theorem B9416249 : Blo 1859631 9416249 := bstep (se 2 (by rfl) ⟨3531093, by rfl⟩ : syracuseStep 9416249 = 7062187) B7062187
theorem B3141193 : Blo 1859631 3141193 := bstep (se 2 (by rfl) ⟨1177947, by rfl⟩ : syracuseStep 3141193 = 2355895) B2355895
theorem B3141227 : Blo 1859631 3141227 := bstep (se 1 (by rfl) ⟨2355920, by rfl⟩ : syracuseStep 3141227 = 4711841) B4711841
theorem B5959325 : Blo 1859631 5959325 := bstep (se 3 (by rfl) ⟨1117373, by rfl⟩ : syracuseStep 5959325 = 2234747) B2234747
theorem B3141497 : Blo 1859631 3141497 := bstep (se 2 (by rfl) ⟨1178061, by rfl⟩ : syracuseStep 3141497 = 2356123) B2356123
theorem B3354491 : Blo 1859631 3354491 := bstep (se 1 (by rfl) ⟨2515868, by rfl⟩ : syracuseStep 3354491 = 5031737) B5031737
theorem B17878931 : Blo 1859631 17878931 := bstep (se 1 (by rfl) ⟨13409198, by rfl⟩ : syracuseStep 17878931 = 26818397) B26818397
theorem B6279119 : Blo 1859631 6279119 := bstep (se 1 (by rfl) ⟨4709339, by rfl⟩ : syracuseStep 6279119 = 9418679) B9418679
theorem B6041785 : Blo 1859631 6041785 := bstep (se 2 (by rfl) ⟨2265669, by rfl⟩ : syracuseStep 6041785 = 4531339) B4531339
theorem B11923645 : Blo 1859631 11923645 := bstep (se 3 (by rfl) ⟨2235683, by rfl⟩ : syracuseStep 11923645 = 4471367) B4471367
theorem B2093287 : Blo 1859631 2093287 := bstep (se 1 (by rfl) ⟨1569965, by rfl⟩ : syracuseStep 2093287 = 3139931) B3139931
theorem B10744093 : Blo 1859631 10744093 := bstep (se 3 (by rfl) ⟨2014517, by rfl⟩ : syracuseStep 10744093 = 4029035) B4029035
theorem B2789663 : Blo 1859631 2789663 := bstep (se 1 (by rfl) ⟨2092247, by rfl⟩ : syracuseStep 2789663 = 4184495) B4184495
theorem B2789687 : Blo 1859631 2789687 := bstep (se 1 (by rfl) ⟨2092265, by rfl⟩ : syracuseStep 2789687 = 4184531) B4184531
theorem B12734831 : Blo 1859631 12734831 := bstep (se 1 (by rfl) ⟨9551123, by rfl⟩ : syracuseStep 12734831 = 19102247) B19102247
theorem B2789759 : Blo 1859631 2789759 := bstep (se 1 (by rfl) ⟨2092319, by rfl⟩ : syracuseStep 2789759 = 4184639) B4184639
theorem B6279551 : Blo 1859631 6279551 := bstep (se 1 (by rfl) ⟨4709663, by rfl⟩ : syracuseStep 6279551 = 9419327) B9419327
theorem B2789831 : Blo 1859631 2789831 := bstep (se 1 (by rfl) ⟨2092373, by rfl⟩ : syracuseStep 2789831 = 4184747) B4184747
theorem B11915855 : Blo 1859631 11915855 := bstep (se 1 (by rfl) ⟨8936891, by rfl⟩ : syracuseStep 11915855 = 17873783) B17873783
theorem B15897167 : Blo 1859631 15897167 := bstep (se 1 (by rfl) ⟨11922875, by rfl⟩ : syracuseStep 15897167 = 23845751) B23845751
theorem B11317907 : Blo 1859631 11317907 := bstep (se 1 (by rfl) ⟨8488430, by rfl⟩ : syracuseStep 11317907 = 16976861) B16976861
theorem B2790185 : Blo 1859631 2790185 := bstep (se 2 (by rfl) ⟨1046319, by rfl⟩ : syracuseStep 2790185 = 2092639) B2092639
theorem B2790191 : Blo 1859631 2790191 := bstep (se 1 (by rfl) ⟨2092643, by rfl⟩ : syracuseStep 2790191 = 4185287) B4185287
theorem B2093935 : Blo 1859631 2093935 := bstep (se 1 (by rfl) ⟨1570451, by rfl⟩ : syracuseStep 2093935 = 3140903) B3140903
theorem B2790311 : Blo 1859631 2790311 := bstep (se 1 (by rfl) ⟨2092733, by rfl⟩ : syracuseStep 2790311 = 4185467) B4185467
theorem B6362107 : Blo 1859631 6362107 := bstep (se 1 (by rfl) ⟨4771580, by rfl⟩ : syracuseStep 6362107 = 9543161) B9543161
theorem B2790395 : Blo 1859631 2790395 := bstep (se 1 (by rfl) ⟨2092796, by rfl⟩ : syracuseStep 2790395 = 4185593) B4185593
theorem B15889445 : Blo 1859631 15889445 := bstep (se 4 (by rfl) ⟨1489635, by rfl⟩ : syracuseStep 15889445 = 2979271) B2979271
theorem B21197861 : Blo 1859631 21197861 := bstep (se 4 (by rfl) ⟨1987299, by rfl⟩ : syracuseStep 21197861 = 3974599) B3974599
theorem B2790455 : Blo 1859631 2790455 := bstep (se 1 (by rfl) ⟨2092841, by rfl⟩ : syracuseStep 2790455 = 4185683) B4185683
theorem B11916395 : Blo 1859631 11916395 := bstep (se 1 (by rfl) ⟨8937296, by rfl⟩ : syracuseStep 11916395 = 17874593) B17874593
theorem B2790575 : Blo 1859631 2790575 := bstep (se 1 (by rfl) ⟨2092931, by rfl⟩ : syracuseStep 2790575 = 4185863) B4185863
theorem B7066835 : Blo 1859631 7066835 := bstep (se 1 (by rfl) ⟨5300126, by rfl⟩ : syracuseStep 7066835 = 10600253) B10600253
theorem B10892531 : Blo 1859631 10892531 := bstep (se 1 (by rfl) ⟨8169398, by rfl⟩ : syracuseStep 10892531 = 16338797) B16338797
theorem B7943579 : Blo 1859631 7943579 := bstep (se 1 (by rfl) ⟨5957684, by rfl⟩ : syracuseStep 7943579 = 11915369) B11915369
theorem B10057159 : Blo 1859631 10057159 := bstep (se 1 (by rfl) ⟨7542869, by rfl⟩ : syracuseStep 10057159 = 15085739) B15085739
theorem B5297633 : Blo 1859631 5297633 := bstep (se 2 (by rfl) ⟨1986612, by rfl⟩ : syracuseStep 5297633 = 3973225) B3973225
theorem B2790983 : Blo 1859631 2790983 := bstep (se 1 (by rfl) ⟨2093237, by rfl⟩ : syracuseStep 2790983 = 4186475) B4186475
theorem B2791079 : Blo 1859631 2791079 := bstep (se 1 (by rfl) ⟨2093309, by rfl⟩ : syracuseStep 2791079 = 4186619) B4186619
theorem B2791163 : Blo 1859631 2791163 := bstep (se 1 (by rfl) ⟨2093372, by rfl⟩ : syracuseStep 2791163 = 4186745) B4186745
theorem B6280955 : Blo 1859631 6280955 := bstep (se 1 (by rfl) ⟨4710716, by rfl⟩ : syracuseStep 6280955 = 9421433) B9421433
theorem B2791199 : Blo 1859631 2791199 := bstep (se 1 (by rfl) ⟨2093399, by rfl⟩ : syracuseStep 2791199 = 4186799) B4186799
theorem B2791247 : Blo 1859631 2791247 := bstep (se 1 (by rfl) ⟨2093435, by rfl⟩ : syracuseStep 2791247 = 4186871) B4186871
theorem B16971601 : Blo 1859631 16971601 := bstep (se 2 (by rfl) ⟨6364350, by rfl⟩ : syracuseStep 16971601 = 12728701) B12728701
theorem B6281117 : Blo 1859631 6281117 := bstep (se 3 (by rfl) ⟨1177709, by rfl⟩ : syracuseStep 6281117 = 2355419) B2355419
theorem B13416349 : Blo 1859631 13416349 := bstep (se 3 (by rfl) ⟨2515565, by rfl⟩ : syracuseStep 13416349 = 5031131) B5031131
theorem B2791367 : Blo 1859631 2791367 := bstep (se 1 (by rfl) ⟨2093525, by rfl⟩ : syracuseStep 2791367 = 4187051) B4187051
theorem B10598363 : Blo 1859631 10598363 := bstep (se 1 (by rfl) ⟨7948772, by rfl⟩ : syracuseStep 10598363 = 15897545) B15897545
theorem B4708327 : Blo 1859631 4708327 := bstep (se 1 (by rfl) ⟨3531245, by rfl⟩ : syracuseStep 4708327 = 7062491) B7062491
theorem B5961721 : Blo 1859631 5961721 := bstep (se 2 (by rfl) ⟨2235645, by rfl⟩ : syracuseStep 5961721 = 4471291) B4471291
theorem B5298281 : Blo 1859631 5298281 := bstep (se 2 (by rfl) ⟨1986855, by rfl⟩ : syracuseStep 5298281 = 3973711) B3973711
theorem B4184207 : Blo 1859631 4184207 := bstep (se 1 (by rfl) ⟨3138155, by rfl⟩ : syracuseStep 4184207 = 6276311) B6276311
theorem B4184225 : Blo 1859631 4184225 := bstep (se 2 (by rfl) ⟨1569084, by rfl⟩ : syracuseStep 4184225 = 3138169) B3138169
theorem B4184297 : Blo 1859631 4184297 := bstep (se 2 (by rfl) ⟨1569111, by rfl⟩ : syracuseStep 4184297 = 3138223) B3138223
theorem B2980073 : Blo 1859631 2980073 := bstep (se 2 (by rfl) ⟨1117527, by rfl⟩ : syracuseStep 2980073 = 2235055) B2235055
theorem B2791721 : Blo 1859631 2791721 := bstep (se 2 (by rfl) ⟨1046895, by rfl⟩ : syracuseStep 2791721 = 2093791) B2093791
theorem B2791727 : Blo 1859631 2791727 := bstep (se 1 (by rfl) ⟨2093795, by rfl⟩ : syracuseStep 2791727 = 4187591) B4187591
theorem B2791967 : Blo 1859631 2791967 := bstep (se 1 (by rfl) ⟨2093975, by rfl⟩ : syracuseStep 2791967 = 4187951) B4187951
theorem B15080033 : Blo 1859631 15080033 := bstep (se 2 (by rfl) ⟨5655012, by rfl⟩ : syracuseStep 15080033 = 11310025) B11310025
theorem B6282089 : Blo 1859631 6282089 := bstep (se 2 (by rfl) ⟨2355783, by rfl⟩ : syracuseStep 6282089 = 4711567) B4711567
theorem B4709279 : Blo 1859631 4709279 := bstep (se 1 (by rfl) ⟨3531959, by rfl⟩ : syracuseStep 4709279 = 7063919) B7063919
theorem B6282143 : Blo 1859631 6282143 := bstep (se 1 (by rfl) ⟨4711607, by rfl⟩ : syracuseStep 6282143 = 9423215) B9423215
theorem B2792351 : Blo 1859631 2792351 := bstep (se 1 (by rfl) ⟨2094263, by rfl⟩ : syracuseStep 2792351 = 4188527) B4188527
theorem B64478125 : Blo 1859631 64478125 := bstep (se 3 (by rfl) ⟨12089648, by rfl⟩ : syracuseStep 64478125 = 24179297) B24179297
theorem B2792399 : Blo 1859631 2792399 := bstep (se 1 (by rfl) ⟨2094299, by rfl⟩ : syracuseStep 2792399 = 4188599) B4188599
theorem B2235439 : Blo 1859631 2235439 := bstep (se 1 (by rfl) ⟨1676579, by rfl⟩ : syracuseStep 2235439 = 3353159) B3353159
theorem B11312243 : Blo 1859631 11312243 := bstep (se 1 (by rfl) ⟨8484182, by rfl⟩ : syracuseStep 11312243 = 16968365) B16968365
theorem B103234679 : Blo 1859631 103234679 := bstep (se 1 (by rfl) ⟨77426009, by rfl⟩ : syracuseStep 103234679 = 154852019) B154852019
theorem B6708349 : Blo 1859631 6708349 := bstep (se 3 (by rfl) ⟨1257815, by rfl⟩ : syracuseStep 6708349 = 2515631) B2515631
theorem B17882315 : Blo 1859631 17882315 := bstep (se 1 (by rfl) ⟨13411736, by rfl⟩ : syracuseStep 17882315 = 26823473) B26823473
theorem B2981129 : Blo 1859631 2981129 := bstep (se 2 (by rfl) ⟨1117923, by rfl⟩ : syracuseStep 2981129 = 2235847) B2235847
theorem B171908405 : Blo 1859631 171908405 := bstep (se 5 (by rfl) ⟨8058206, by rfl⟩ : syracuseStep 171908405 = 16116413) B16116413
theorem B7945577 : Blo 1859631 7945577 := bstep (se 2 (by rfl) ⟨2979591, by rfl⟩ : syracuseStep 7945577 = 5959183) B5959183
theorem B9420137 : Blo 1859631 9420137 := bstep (se 2 (by rfl) ⟨3532551, by rfl⟩ : syracuseStep 9420137 = 7065103) B7065103
theorem B10739105 : Blo 1859631 10739105 := bstep (se 2 (by rfl) ⟨4027164, by rfl⟩ : syracuseStep 10739105 = 8054329) B8054329
theorem B4300199 : Blo 1859631 4300199 := bstep (se 1 (by rfl) ⟨3225149, by rfl⟩ : syracuseStep 4300199 = 6450299) B6450299
theorem B4185575 : Blo 1859631 4185575 := bstep (se 1 (by rfl) ⟨3139181, by rfl⟩ : syracuseStep 4185575 = 6278363) B6278363
theorem B34405877 : Blo 1859631 34405877 := bstep (se 5 (by rfl) ⟨1612775, by rfl⟩ : syracuseStep 34405877 = 3225551) B3225551
theorem B10591823 : Blo 1859631 10591823 := bstep (se 1 (by rfl) ⟨7943867, by rfl⟩ : syracuseStep 10591823 = 15887735) B15887735
theorem B5168731 : Blo 1859631 5168731 := bstep (se 1 (by rfl) ⟨3876548, by rfl⟩ : syracuseStep 5168731 = 7753097) B7753097
theorem B11919059 : Blo 1859631 11919059 := bstep (se 1 (by rfl) ⟨8939294, by rfl⟩ : syracuseStep 11919059 = 17878589) B17878589
theorem B5963489 : Blo 1859631 5963489 := bstep (se 2 (by rfl) ⟨2236308, by rfl⟩ : syracuseStep 5963489 = 4472617) B4472617
theorem B5300093 : Blo 1859631 5300093 := bstep (se 3 (by rfl) ⟨993767, by rfl⟩ : syracuseStep 5300093 = 1987535) B1987535
theorem B1859775 : Blo 1859631 1859775 := bstep (se 1 (by rfl) ⟨1394831, by rfl⟩ : syracuseStep 1859775 = 2789663) B2789663
theorem B1859791 : Blo 1859631 1859791 := bstep (se 1 (by rfl) ⟨1394843, by rfl⟩ : syracuseStep 1859791 = 2789687) B2789687
theorem B1859839 : Blo 1859631 1859839 := bstep (se 1 (by rfl) ⟨1394879, by rfl⟩ : syracuseStep 1859839 = 2789759) B2789759
theorem B4186367 : Blo 1859631 4186367 := bstep (se 1 (by rfl) ⟨3139775, by rfl⟩ : syracuseStep 4186367 = 6279551) B6279551
theorem B19882265 : Blo 1859631 19882265 := bstep (se 2 (by rfl) ⟨7455849, by rfl⟩ : syracuseStep 19882265 = 14911699) B14911699
theorem B1859887 : Blo 1859631 1859887 := bstep (se 1 (by rfl) ⟨1394915, by rfl⟩ : syracuseStep 1859887 = 2789831) B2789831
theorem B4186529 : Blo 1859631 4186529 := bstep (se 2 (by rfl) ⟨1569948, by rfl⟩ : syracuseStep 4186529 = 3139897) B3139897
theorem B7545271 : Blo 1859631 7545271 := bstep (se 1 (by rfl) ⟨5658953, by rfl⟩ : syracuseStep 7545271 = 11317907) B11317907
theorem B1860123 : Blo 1859631 1860123 := bstep (se 1 (by rfl) ⟨1395092, by rfl⟩ : syracuseStep 1860123 = 2790185) B2790185
theorem B1860127 : Blo 1859631 1860127 := bstep (se 1 (by rfl) ⟨1395095, by rfl⟩ : syracuseStep 1860127 = 2790191) B2790191
theorem B1860207 : Blo 1859631 1860207 := bstep (se 1 (by rfl) ⟨1395155, by rfl⟩ : syracuseStep 1860207 = 2790311) B2790311
theorem B1860263 : Blo 1859631 1860263 := bstep (se 1 (by rfl) ⟨1395197, by rfl⟩ : syracuseStep 1860263 = 2790395) B2790395
theorem B10592963 : Blo 1859631 10592963 := bstep (se 1 (by rfl) ⟨7944722, by rfl⟩ : syracuseStep 10592963 = 15889445) B15889445
theorem B14131907 : Blo 1859631 14131907 := bstep (se 1 (by rfl) ⟨10598930, by rfl⟩ : syracuseStep 14131907 = 21197861) B21197861
theorem B1860303 : Blo 1859631 1860303 := bstep (se 1 (by rfl) ⟨1395227, by rfl⟩ : syracuseStep 1860303 = 2790455) B2790455
theorem B22938349 : Blo 1859631 22938349 := bstep (se 3 (by rfl) ⟨4300940, by rfl⟩ : syracuseStep 22938349 = 8601881) B8601881
theorem B1860383 : Blo 1859631 1860383 := bstep (se 1 (by rfl) ⟨1395287, by rfl⟩ : syracuseStep 1860383 = 2790575) B2790575
theorem B4711223 : Blo 1859631 4711223 := bstep (se 1 (by rfl) ⟨3533417, by rfl⟩ : syracuseStep 4711223 = 7066835) B7066835
theorem B3531755 : Blo 1859631 3531755 := bstep (se 1 (by rfl) ⟨2648816, by rfl⟩ : syracuseStep 3531755 = 5297633) B5297633
theorem B1860655 : Blo 1859631 1860655 := bstep (se 1 (by rfl) ⟨1395491, by rfl⟩ : syracuseStep 1860655 = 2790983) B2790983
theorem B1860719 : Blo 1859631 1860719 := bstep (se 1 (by rfl) ⟨1395539, by rfl⟩ : syracuseStep 1860719 = 2791079) B2791079
theorem B1860775 : Blo 1859631 1860775 := bstep (se 1 (by rfl) ⟨1395581, by rfl⟩ : syracuseStep 1860775 = 2791163) B2791163
theorem B4187303 : Blo 1859631 4187303 := bstep (se 1 (by rfl) ⟨3140477, by rfl⟩ : syracuseStep 4187303 = 6280955) B6280955
theorem B1860799 : Blo 1859631 1860799 := bstep (se 1 (by rfl) ⟨1395599, by rfl⟩ : syracuseStep 1860799 = 2791199) B2791199
theorem B1860831 : Blo 1859631 1860831 := bstep (se 1 (by rfl) ⟨1395623, by rfl⟩ : syracuseStep 1860831 = 2791247) B2791247
theorem B4187411 : Blo 1859631 4187411 := bstep (se 1 (by rfl) ⟨3140558, by rfl⟩ : syracuseStep 4187411 = 6281117) B6281117
theorem B1860911 : Blo 1859631 1860911 := bstep (se 1 (by rfl) ⟨1395683, by rfl⟩ : syracuseStep 1860911 = 2791367) B2791367
theorem B3532187 : Blo 1859631 3532187 := bstep (se 1 (by rfl) ⟨2649140, by rfl⟩ : syracuseStep 3532187 = 5298281) B5298281
theorem B15287723 : Blo 1859631 15287723 := bstep (se 1 (by rfl) ⟨11465792, by rfl⟩ : syracuseStep 15287723 = 22931585) B22931585
theorem B31794605 : Blo 1859631 31794605 := bstep (se 3 (by rfl) ⟨5961488, by rfl⟩ : syracuseStep 31794605 = 11922977) B11922977
theorem B1861147 : Blo 1859631 1861147 := bstep (se 1 (by rfl) ⟨1395860, by rfl⟩ : syracuseStep 1861147 = 2791721) B2791721
theorem B1861151 : Blo 1859631 1861151 := bstep (se 1 (by rfl) ⟨1395863, by rfl⟩ : syracuseStep 1861151 = 2791727) B2791727
theorem B1861311 : Blo 1859631 1861311 := bstep (se 1 (by rfl) ⟨1395983, by rfl⟩ : syracuseStep 1861311 = 2791967) B2791967
theorem B10053355 : Blo 1859631 10053355 := bstep (se 1 (by rfl) ⟨7540016, by rfl⟩ : syracuseStep 10053355 = 15080033) B15080033
theorem B4188041 : Blo 1859631 4188041 := bstep (se 2 (by rfl) ⟨1570515, by rfl⟩ : syracuseStep 4188041 = 3141031) B3141031
theorem B4188059 : Blo 1859631 4188059 := bstep (se 1 (by rfl) ⟨3141044, by rfl⟩ : syracuseStep 4188059 = 6282089) B6282089
theorem B3139519 : Blo 1859631 3139519 := bstep (se 1 (by rfl) ⟨2354639, by rfl⟩ : syracuseStep 3139519 = 4709279) B4709279
theorem B4188095 : Blo 1859631 4188095 := bstep (se 1 (by rfl) ⟨3141071, by rfl⟩ : syracuseStep 4188095 = 6282143) B6282143
theorem B1861567 : Blo 1859631 1861567 := bstep (se 1 (by rfl) ⟨1396175, by rfl⟩ : syracuseStep 1861567 = 2792351) B2792351
theorem B1861599 : Blo 1859631 1861599 := bstep (se 1 (by rfl) ⟨1396199, by rfl⟩ : syracuseStep 1861599 = 2792399) B2792399
theorem B68823119 : Blo 1859631 68823119 := bstep (se 1 (by rfl) ⟨51617339, by rfl⟩ : syracuseStep 68823119 = 103234679) B103234679
theorem B4188257 : Blo 1859631 4188257 := bstep (se 2 (by rfl) ⟨1570596, by rfl⟩ : syracuseStep 4188257 = 3141193) B3141193
theorem B206579813 : Blo 1859631 206579813 := bstep (se 4 (by rfl) ⟨19366857, by rfl⟩ : syracuseStep 206579813 = 38733715) B38733715
theorem B6891641 : Blo 1859631 6891641 := bstep (se 2 (by rfl) ⟨2584365, by rfl⟩ : syracuseStep 6891641 = 5168731) B5168731
theorem B11921543 : Blo 1859631 11921543 := bstep (se 1 (by rfl) ⟨8941157, by rfl⟩ : syracuseStep 11921543 = 17882315) B17882315
theorem B6277499 : Blo 1859631 6277499 := bstep (se 1 (by rfl) ⟨4708124, by rfl⟩ : syracuseStep 6277499 = 9416249) B9416249
theorem B22628801 : Blo 1859631 22628801 := bstep (se 2 (by rfl) ⟨8485800, by rfl⟩ : syracuseStep 22628801 = 16971601) B16971601
theorem B3975659 : Blo 1859631 3975659 := bstep (se 1 (by rfl) ⟨2981744, by rfl⟩ : syracuseStep 3975659 = 5963489) B5963489
theorem B3533395 : Blo 1859631 3533395 := bstep (se 1 (by rfl) ⟨2650046, by rfl⟩ : syracuseStep 3533395 = 5300093) B5300093
theorem B6277769 : Blo 1859631 6277769 := bstep (se 2 (by rfl) ⟨2354163, by rfl⟩ : syracuseStep 6277769 = 4708327) B4708327
theorem B7948961 : Blo 1859631 7948961 := bstep (se 2 (by rfl) ⟨2980860, by rfl⟩ : syracuseStep 7948961 = 5961721) B5961721
theorem B5368655 : Blo 1859631 5368655 := bstep (se 1 (by rfl) ⟨4026491, by rfl⟩ : syracuseStep 5368655 = 8052983) B8052983
theorem B8055713 : Blo 1859631 8055713 := bstep (se 2 (by rfl) ⟨3020892, by rfl⟩ : syracuseStep 8055713 = 6041785) B6041785
theorem B2092207 : Blo 1859631 2092207 := bstep (se 1 (by rfl) ⟨1569155, by rfl⟩ : syracuseStep 2092207 = 3138311) B3138311
theorem B7949677 : Blo 1859631 7949677 := bstep (se 3 (by rfl) ⟨1490564, by rfl⟩ : syracuseStep 7949677 = 2981129) B2981129
theorem B7261687 : Blo 1859631 7261687 := bstep (se 1 (by rfl) ⟨5446265, by rfl⟩ : syracuseStep 7261687 = 10892531) B10892531
theorem B5295719 : Blo 1859631 5295719 := bstep (se 1 (by rfl) ⟨3971789, by rfl⟩ : syracuseStep 5295719 = 7943579) B7943579
theorem B33959549 : Blo 1859631 33959549 := bstep (se 3 (by rfl) ⟨6367415, by rfl⟩ : syracuseStep 33959549 = 12734831) B12734831
theorem B15896209 : Blo 1859631 15896209 := bstep (se 2 (by rfl) ⟨5961078, by rfl⟩ : syracuseStep 15896209 = 11922157) B11922157
theorem B9416573 : Blo 1859631 9416573 := bstep (se 3 (by rfl) ⟨1765607, by rfl⟩ : syracuseStep 9416573 = 3531215) B3531215
theorem B2092927 : Blo 1859631 2092927 := bstep (se 1 (by rfl) ⟨1569695, by rfl⟩ : syracuseStep 2092927 = 3139391) B3139391
theorem B7065575 : Blo 1859631 7065575 := bstep (se 1 (by rfl) ⟨5299181, by rfl⟩ : syracuseStep 7065575 = 10598363) B10598363
theorem B2789471 : Blo 1859631 2789471 := bstep (se 1 (by rfl) ⟨2092103, by rfl⟩ : syracuseStep 2789471 = 4184207) B4184207
theorem B2789483 : Blo 1859631 2789483 := bstep (se 1 (by rfl) ⟨2092112, by rfl⟩ : syracuseStep 2789483 = 4184225) B4184225
theorem B2789531 : Blo 1859631 2789531 := bstep (se 1 (by rfl) ⟨2092148, by rfl⟩ : syracuseStep 2789531 = 4184297) B4184297
theorem B1986715 : Blo 1859631 1986715 := bstep (se 1 (by rfl) ⟨1490036, by rfl⟩ : syracuseStep 1986715 = 2980073) B2980073
theorem B83832995 : Blo 1859631 83832995 := bstep (se 1 (by rfl) ⟨62874746, by rfl⟩ : syracuseStep 83832995 = 125749493) B125749493
theorem B2093467 : Blo 1859631 2093467 := bstep (se 1 (by rfl) ⟨1570100, by rfl⟩ : syracuseStep 2093467 = 3140201) B3140201
theorem B7541495 : Blo 1859631 7541495 := bstep (se 1 (by rfl) ⟨5656121, by rfl⟩ : syracuseStep 7541495 = 11312243) B11312243
theorem B5297051 : Blo 1859631 5297051 := bstep (se 1 (by rfl) ⟨3972788, by rfl⟩ : syracuseStep 5297051 = 7945577) B7945577
theorem B6280091 : Blo 1859631 6280091 := bstep (se 1 (by rfl) ⟨4710068, by rfl⟩ : syracuseStep 6280091 = 9420137) B9420137
theorem B2790383 : Blo 1859631 2790383 := bstep (se 1 (by rfl) ⟨2092787, by rfl⟩ : syracuseStep 2790383 = 4185575) B4185575
theorem B2094151 : Blo 1859631 2094151 := bstep (se 1 (by rfl) ⟨1570613, by rfl⟩ : syracuseStep 2094151 = 3141227) B3141227
theorem B17888465 : Blo 1859631 17888465 := bstep (se 2 (by rfl) ⟨6708174, by rfl⟩ : syracuseStep 17888465 = 13416349) B13416349
theorem B2094331 : Blo 1859631 2094331 := bstep (se 1 (by rfl) ⟨1570748, by rfl⟩ : syracuseStep 2094331 = 3141497) B3141497
theorem B2790767 : Blo 1859631 2790767 := bstep (se 1 (by rfl) ⟨2093075, by rfl⟩ : syracuseStep 2790767 = 4186151) B4186151
theorem B2790887 : Blo 1859631 2790887 := bstep (se 1 (by rfl) ⟨2093165, by rfl⟩ : syracuseStep 2790887 = 4186331) B4186331
theorem B15898193 : Blo 1859631 15898193 := bstep (se 2 (by rfl) ⟨5961822, by rfl⟩ : syracuseStep 15898193 = 11923645) B11923645
theorem B2791049 : Blo 1859631 2791049 := bstep (se 2 (by rfl) ⟨1046643, by rfl⟩ : syracuseStep 2791049 = 2093287) B2093287
theorem B2791067 : Blo 1859631 2791067 := bstep (se 1 (by rfl) ⟨2093300, by rfl⟩ : syracuseStep 2791067 = 4186601) B4186601
theorem B27178681 : Blo 1859631 27178681 := bstep (se 2 (by rfl) ⟨10192005, by rfl⟩ : syracuseStep 27178681 = 20384011) B20384011
theorem B7943903 : Blo 1859631 7943903 := bstep (se 1 (by rfl) ⟨5957927, by rfl⟩ : syracuseStep 7943903 = 11915855) B11915855
theorem B10598111 : Blo 1859631 10598111 := bstep (se 1 (by rfl) ⟨7948583, by rfl⟩ : syracuseStep 10598111 = 15897167) B15897167
theorem B2791259 : Blo 1859631 2791259 := bstep (se 1 (by rfl) ⟨2093444, by rfl⟩ : syracuseStep 2791259 = 4186889) B4186889
theorem B7944263 : Blo 1859631 7944263 := bstep (se 1 (by rfl) ⟨5958197, by rfl⟩ : syracuseStep 7944263 = 11916395) B11916395
theorem B2791643 : Blo 1859631 2791643 := bstep (se 1 (by rfl) ⟨2093732, by rfl⟩ : syracuseStep 2791643 = 4187465) B4187465
theorem B4184351 : Blo 1859631 4184351 := bstep (se 1 (by rfl) ⟨3138263, by rfl⟩ : syracuseStep 4184351 = 6276527) B6276527
theorem B2791913 : Blo 1859631 2791913 := bstep (se 2 (by rfl) ⟨1046967, by rfl⟩ : syracuseStep 2791913 = 2093935) B2093935
theorem B4184603 : Blo 1859631 4184603 := bstep (se 1 (by rfl) ⟨3138452, by rfl⟩ : syracuseStep 4184603 = 6276905) B6276905
theorem B2980585 : Blo 1859631 2980585 := bstep (se 2 (by rfl) ⟨1117719, by rfl⟩ : syracuseStep 2980585 = 2235439) B2235439
theorem B57301829 : Blo 1859631 57301829 := bstep (se 4 (by rfl) ⟨5372046, by rfl⟩ : syracuseStep 57301829 = 10744093) B10744093
theorem B8944465 : Blo 1859631 8944465 := bstep (se 2 (by rfl) ⟨3354174, by rfl⟩ : syracuseStep 8944465 = 6708349) B6708349
theorem B2792303 : Blo 1859631 2792303 := bstep (se 1 (by rfl) ⟨2094227, by rfl⟩ : syracuseStep 2792303 = 4188455) B4188455
theorem B2792315 : Blo 1859631 2792315 := bstep (se 1 (by rfl) ⟨2094236, by rfl⟩ : syracuseStep 2792315 = 4188473) B4188473
theorem B13409545 : Blo 1859631 13409545 := bstep (se 2 (by rfl) ⟨5028579, by rfl⟩ : syracuseStep 13409545 = 10057159) B10057159
theorem B11312455 : Blo 1859631 11312455 := bstep (se 1 (by rfl) ⟨8484341, by rfl⟩ : syracuseStep 11312455 = 16968683) B16968683
theorem B114605603 : Blo 1859631 114605603 := bstep (se 1 (by rfl) ⟨85954202, by rfl⟩ : syracuseStep 114605603 = 171908405) B171908405
theorem B343883333 : Blo 1859631 343883333 := bstep (se 4 (by rfl) ⟨32239062, by rfl⟩ : syracuseStep 343883333 = 64478125) B64478125
theorem B7159403 : Blo 1859631 7159403 := bstep (se 1 (by rfl) ⟨5369552, by rfl⟩ : syracuseStep 7159403 = 10739105) B10739105
theorem B2866799 : Blo 1859631 2866799 := bstep (se 1 (by rfl) ⟨2150099, by rfl⟩ : syracuseStep 2866799 = 4300199) B4300199
theorem B8945309 : Blo 1859631 8945309 := bstep (se 3 (by rfl) ⟨1677245, by rfl⟩ : syracuseStep 8945309 = 3354491) B3354491
theorem B22937251 : Blo 1859631 22937251 := bstep (se 1 (by rfl) ⟨17202938, by rfl⟩ : syracuseStep 22937251 = 34405877) B34405877
theorem B7061215 : Blo 1859631 7061215 := bstep (se 1 (by rfl) ⟨5295911, by rfl⟩ : syracuseStep 7061215 = 10591823) B10591823
theorem B3972883 : Blo 1859631 3972883 := bstep (se 1 (by rfl) ⟨2979662, by rfl⟩ : syracuseStep 3972883 = 5959325) B5959325
theorem B7946039 : Blo 1859631 7946039 := bstep (se 1 (by rfl) ⟨5959529, by rfl⟩ : syracuseStep 7946039 = 11919059) B11919059
theorem B4185953 : Blo 1859631 4185953 := bstep (se 2 (by rfl) ⟨1569732, by rfl⟩ : syracuseStep 4185953 = 3139465) B3139465
theorem B11919287 : Blo 1859631 11919287 := bstep (se 1 (by rfl) ⟨8939465, by rfl⟩ : syracuseStep 11919287 = 17878931) B17878931
theorem B4186079 : Blo 1859631 4186079 := bstep (se 1 (by rfl) ⟨3139559, by rfl⟩ : syracuseStep 4186079 = 6279119) B6279119
theorem B33931237 : Blo 1859631 33931237 := bstep (se 4 (by rfl) ⟨3181053, by rfl⟩ : syracuseStep 33931237 = 6362107) B6362107
theorem B3530729 : Blo 1859631 3530729 := bstep (se 2 (by rfl) ⟨1324023, by rfl⟩ : syracuseStep 3530729 = 2648047) B2648047
theorem B1859647 : Blo 1859631 1859647 := bstep (se 1 (by rfl) ⟨1394735, by rfl⟩ : syracuseStep 1859647 = 2789471) B2789471
theorem B1859655 : Blo 1859631 1859655 := bstep (se 1 (by rfl) ⟨1394741, by rfl⟩ : syracuseStep 1859655 = 2789483) B2789483
theorem B1859687 : Blo 1859631 1859687 := bstep (se 1 (by rfl) ⟨1394765, by rfl⟩ : syracuseStep 1859687 = 2789531) B2789531
theorem B550879501 : Blo 1859631 550879501 := bstep (se 3 (by rfl) ⟨103289906, by rfl⟩ : syracuseStep 550879501 = 206579813) B206579813
theorem B7061975 : Blo 1859631 7061975 := bstep (se 1 (by rfl) ⟨5296481, by rfl⟩ : syracuseStep 7061975 = 10592963) B10592963
theorem B9421271 : Blo 1859631 9421271 := bstep (se 1 (by rfl) ⟨7065953, by rfl⟩ : syracuseStep 9421271 = 14131907) B14131907
theorem B10060361 : Blo 1859631 10060361 := bstep (se 2 (by rfl) ⟨3772635, by rfl⟩ : syracuseStep 10060361 = 7545271) B7545271
theorem B3531367 : Blo 1859631 3531367 := bstep (se 1 (by rfl) ⟨2648525, by rfl⟩ : syracuseStep 3531367 = 5297051) B5297051
theorem B4186727 : Blo 1859631 4186727 := bstep (se 1 (by rfl) ⟨3140045, by rfl⟩ : syracuseStep 4186727 = 6280091) B6280091
theorem B1860255 : Blo 1859631 1860255 := bstep (se 1 (by rfl) ⟨1395191, by rfl⟩ : syracuseStep 1860255 = 2790383) B2790383
theorem B53019373 : Blo 1859631 53019373 := bstep (se 3 (by rfl) ⟨9941132, by rfl⟩ : syracuseStep 53019373 = 19882265) B19882265
theorem B4711193 : Blo 1859631 4711193 := bstep (se 2 (by rfl) ⟨1766697, by rfl⟩ : syracuseStep 4711193 = 3533395) B3533395
theorem B1860511 : Blo 1859631 1860511 := bstep (se 1 (by rfl) ⟨1395383, by rfl⟩ : syracuseStep 1860511 = 2790767) B2790767
theorem B10191815 : Blo 1859631 10191815 := bstep (se 1 (by rfl) ⟨7643861, by rfl⟩ : syracuseStep 10191815 = 15287723) B15287723
theorem B3974113 : Blo 1859631 3974113 := bstep (se 2 (by rfl) ⟨1490292, by rfl⟩ : syracuseStep 3974113 = 2980585) B2980585
theorem B1860591 : Blo 1859631 1860591 := bstep (se 1 (by rfl) ⟨1395443, by rfl⟩ : syracuseStep 1860591 = 2790887) B2790887
theorem B1860699 : Blo 1859631 1860699 := bstep (se 1 (by rfl) ⟨1395524, by rfl⟩ : syracuseStep 1860699 = 2791049) B2791049
theorem B1860711 : Blo 1859631 1860711 := bstep (se 1 (by rfl) ⟨1395533, by rfl⟩ : syracuseStep 1860711 = 2791067) B2791067
theorem B1860839 : Blo 1859631 1860839 := bstep (se 1 (by rfl) ⟨1395629, by rfl⟩ : syracuseStep 1860839 = 2791259) B2791259
theorem B7947695 : Blo 1859631 7947695 := bstep (se 1 (by rfl) ⟨5960771, by rfl⟩ : syracuseStep 7947695 = 11921543) B11921543
theorem B1861095 : Blo 1859631 1861095 := bstep (se 1 (by rfl) ⟨1395821, by rfl⟩ : syracuseStep 1861095 = 2791643) B2791643
theorem B1861275 : Blo 1859631 1861275 := bstep (se 1 (by rfl) ⟨1395956, by rfl⟩ : syracuseStep 1861275 = 2791913) B2791913
theorem B15083273 : Blo 1859631 15083273 := bstep (se 2 (by rfl) ⟨5656227, by rfl⟩ : syracuseStep 15083273 = 11312455) B11312455
theorem B38201219 : Blo 1859631 38201219 := bstep (se 1 (by rfl) ⟨28650914, by rfl⟩ : syracuseStep 38201219 = 57301829) B57301829
theorem B1861535 : Blo 1859631 1861535 := bstep (se 1 (by rfl) ⟨1396151, by rfl⟩ : syracuseStep 1861535 = 2792303) B2792303
theorem B1861543 : Blo 1859631 1861543 := bstep (se 1 (by rfl) ⟨1396157, by rfl⟩ : syracuseStep 1861543 = 2792315) B2792315
theorem B21194945 : Blo 1859631 21194945 := bstep (se 2 (by rfl) ⟨7948104, by rfl⟩ : syracuseStep 21194945 = 15896209) B15896209
theorem B30583001 : Blo 1859631 30583001 := bstep (se 2 (by rfl) ⟨11468625, by rfl⟩ : syracuseStep 30583001 = 22937251) B22937251
theorem B9414953 : Blo 1859631 9414953 := bstep (se 2 (by rfl) ⟨3530607, by rfl⟩ : syracuseStep 9414953 = 7061215) B7061215
theorem B13404473 : Blo 1859631 13404473 := bstep (se 2 (by rfl) ⟨5026677, by rfl⟩ : syracuseStep 13404473 = 10053355) B10053355
theorem B229255555 : Blo 1859631 229255555 := bstep (se 1 (by rfl) ⟨171941666, by rfl⟩ : syracuseStep 229255555 = 343883333) B343883333
theorem B1911199 : Blo 1859631 1911199 := bstep (se 1 (by rfl) ⟨1433399, by rfl⟩ : syracuseStep 1911199 = 2866799) B2866799
theorem B21481901 : Blo 1859631 21481901 := bstep (se 3 (by rfl) ⟨4027856, by rfl⟩ : syracuseStep 21481901 = 8055713) B8055713
theorem B6277715 : Blo 1859631 6277715 := bstep (se 1 (by rfl) ⟨4708286, by rfl⟩ : syracuseStep 6277715 = 9416573) B9416573
theorem B9415277 : Blo 1859631 9415277 := bstep (se 3 (by rfl) ⟨1765364, by rfl⟩ : syracuseStep 9415277 = 3530729) B3530729
theorem B55888663 : Blo 1859631 55888663 := bstep (se 1 (by rfl) ⟨41916497, by rfl⟩ : syracuseStep 55888663 = 83832995) B83832995
theorem B2648953 : Blo 1859631 2648953 := bstep (se 2 (by rfl) ⟨993357, by rfl⟩ : syracuseStep 2648953 = 1986715) B1986715
theorem B183528317 : Blo 1859631 183528317 := bstep (se 3 (by rfl) ⟨34411559, by rfl⟩ : syracuseStep 183528317 = 68823119) B68823119
theorem B3140815 : Blo 1859631 3140815 := bstep (se 1 (by rfl) ⟨2355611, by rfl⟩ : syracuseStep 3140815 = 4711223) B4711223
theorem B2354503 : Blo 1859631 2354503 := bstep (se 1 (by rfl) ⟨1765877, by rfl⟩ : syracuseStep 2354503 = 3531755) B3531755
theorem B21196403 : Blo 1859631 21196403 := bstep (se 1 (by rfl) ⟨15897302, by rfl⟩ : syracuseStep 21196403 = 31794605) B31794605
theorem B30584465 : Blo 1859631 30584465 := bstep (se 2 (by rfl) ⟨11469174, by rfl⟩ : syracuseStep 30584465 = 22938349) B22938349
theorem B5295935 : Blo 1859631 5295935 := bstep (se 1 (by rfl) ⟨3971951, by rfl⟩ : syracuseStep 5295935 = 7943903) B7943903
theorem B7065407 : Blo 1859631 7065407 := bstep (se 1 (by rfl) ⟨5299055, by rfl⟩ : syracuseStep 7065407 = 10598111) B10598111
theorem B5296175 : Blo 1859631 5296175 := bstep (se 1 (by rfl) ⟨3972131, by rfl⟩ : syracuseStep 5296175 = 7944263) B7944263
theorem B2789567 : Blo 1859631 2789567 := bstep (se 1 (by rfl) ⟨2092175, by rfl⟩ : syracuseStep 2789567 = 4184351) B4184351
theorem B2789609 : Blo 1859631 2789609 := bstep (se 2 (by rfl) ⟨1046103, by rfl⟩ : syracuseStep 2789609 = 2092207) B2092207
theorem B15085867 : Blo 1859631 15085867 := bstep (se 1 (by rfl) ⟨11314400, by rfl⟩ : syracuseStep 15085867 = 22628801) B22628801
theorem B2650439 : Blo 1859631 2650439 := bstep (se 1 (by rfl) ⟨1987829, by rfl⟩ : syracuseStep 2650439 = 3975659) B3975659
theorem B17879393 : Blo 1859631 17879393 := bstep (se 2 (by rfl) ⟨6704772, by rfl⟩ : syracuseStep 17879393 = 13409545) B13409545
theorem B2789735 : Blo 1859631 2789735 := bstep (se 1 (by rfl) ⟨2092301, by rfl⟩ : syracuseStep 2789735 = 4184603) B4184603
theorem B36238241 : Blo 1859631 36238241 := bstep (se 2 (by rfl) ⟨13589340, by rfl⟩ : syracuseStep 36238241 = 27178681) B27178681
theorem B76403735 : Blo 1859631 76403735 := bstep (se 1 (by rfl) ⟨57302801, by rfl⟩ : syracuseStep 76403735 = 114605603) B114605603
theorem B5297177 : Blo 1859631 5297177 := bstep (se 2 (by rfl) ⟨1986441, by rfl⟩ : syracuseStep 5297177 = 3972883) B3972883
theorem B4772935 : Blo 1859631 4772935 := bstep (se 1 (by rfl) ⟨3579701, by rfl⟩ : syracuseStep 4772935 = 7159403) B7159403
theorem B22639699 : Blo 1859631 22639699 := bstep (se 1 (by rfl) ⟨16979774, by rfl⟩ : syracuseStep 22639699 = 33959549) B33959549
theorem B2790569 : Blo 1859631 2790569 := bstep (se 2 (by rfl) ⟨1046463, by rfl⟩ : syracuseStep 2790569 = 2092927) B2092927
theorem B5297359 : Blo 1859631 5297359 := bstep (se 1 (by rfl) ⟨3973019, by rfl⟩ : syracuseStep 5297359 = 7946039) B7946039
theorem B2790635 : Blo 1859631 2790635 := bstep (se 1 (by rfl) ⟨2092976, by rfl⟩ : syracuseStep 2790635 = 4185953) B4185953
theorem B45241649 : Blo 1859631 45241649 := bstep (se 2 (by rfl) ⟨16965618, by rfl⟩ : syracuseStep 45241649 = 33931237) B33931237
theorem B2790719 : Blo 1859631 2790719 := bstep (se 1 (by rfl) ⟨2093039, by rfl⟩ : syracuseStep 2790719 = 4186079) B4186079
theorem B2790911 : Blo 1859631 2790911 := bstep (se 1 (by rfl) ⟨2093183, by rfl⟩ : syracuseStep 2790911 = 4186367) B4186367
theorem B2791019 : Blo 1859631 2791019 := bstep (se 1 (by rfl) ⟨2093264, by rfl⟩ : syracuseStep 2791019 = 4186529) B4186529
theorem B5027663 : Blo 1859631 5027663 := bstep (se 1 (by rfl) ⟨3770747, by rfl⟩ : syracuseStep 5027663 = 7541495) B7541495
theorem B2791289 : Blo 1859631 2791289 := bstep (se 2 (by rfl) ⟨1046733, by rfl⟩ : syracuseStep 2791289 = 2093467) B2093467
theorem B2791535 : Blo 1859631 2791535 := bstep (se 1 (by rfl) ⟨2093651, by rfl⟩ : syracuseStep 2791535 = 4187303) B4187303
theorem B11925643 : Blo 1859631 11925643 := bstep (se 1 (by rfl) ⟨8944232, by rfl⟩ : syracuseStep 11925643 = 17888465) B17888465
theorem B2791607 : Blo 1859631 2791607 := bstep (se 1 (by rfl) ⟨2093705, by rfl⟩ : syracuseStep 2791607 = 4187411) B4187411
theorem B10598795 : Blo 1859631 10598795 := bstep (se 1 (by rfl) ⟨7949096, by rfl⟩ : syracuseStep 10598795 = 15898193) B15898193
theorem B9419165 : Blo 1859631 9419165 := bstep (se 3 (by rfl) ⟨1766093, by rfl⟩ : syracuseStep 9419165 = 3532187) B3532187
theorem B11925953 : Blo 1859631 11925953 := bstep (se 2 (by rfl) ⟨4472232, by rfl⟩ : syracuseStep 11925953 = 8944465) B8944465
theorem B2792027 : Blo 1859631 2792027 := bstep (se 1 (by rfl) ⟨2094020, by rfl⟩ : syracuseStep 2792027 = 4188041) B4188041
theorem B2792039 : Blo 1859631 2792039 := bstep (se 1 (by rfl) ⟨2094029, by rfl⟩ : syracuseStep 2792039 = 4188059) B4188059
theorem B2792063 : Blo 1859631 2792063 := bstep (se 1 (by rfl) ⟨2094047, by rfl⟩ : syracuseStep 2792063 = 4188095) B4188095
theorem B2792171 : Blo 1859631 2792171 := bstep (se 1 (by rfl) ⟨2094128, by rfl⟩ : syracuseStep 2792171 = 4188257) B4188257
theorem B4594427 : Blo 1859631 4594427 := bstep (se 1 (by rfl) ⟨3445820, by rfl⟩ : syracuseStep 4594427 = 6891641) B6891641
theorem B2792201 : Blo 1859631 2792201 := bstep (se 2 (by rfl) ⟨1047075, by rfl⟩ : syracuseStep 2792201 = 2094151) B2094151
theorem B4184999 : Blo 1859631 4184999 := bstep (se 1 (by rfl) ⟨3138749, by rfl⟩ : syracuseStep 4184999 = 6277499) B6277499
theorem B2792441 : Blo 1859631 2792441 := bstep (se 2 (by rfl) ⟨1047165, by rfl⟩ : syracuseStep 2792441 = 2094331) B2094331
theorem B4185179 : Blo 1859631 4185179 := bstep (se 1 (by rfl) ⟨3138884, by rfl⟩ : syracuseStep 4185179 = 6277769) B6277769
theorem B5299307 : Blo 1859631 5299307 := bstep (se 1 (by rfl) ⟨3974480, by rfl⟩ : syracuseStep 5299307 = 7948961) B7948961
theorem B10599569 : Blo 1859631 10599569 := bstep (se 2 (by rfl) ⟨3974838, by rfl⟩ : syracuseStep 10599569 = 7949677) B7949677
theorem B3579103 : Blo 1859631 3579103 := bstep (se 1 (by rfl) ⟨2684327, by rfl⟩ : syracuseStep 3579103 = 5368655) B5368655
theorem B9682249 : Blo 1859631 9682249 := bstep (se 2 (by rfl) ⟨3630843, by rfl⟩ : syracuseStep 9682249 = 7261687) B7261687
theorem B3530479 : Blo 1859631 3530479 := bstep (se 1 (by rfl) ⟨2647859, by rfl⟩ : syracuseStep 3530479 = 5295719) B5295719
theorem B5963539 : Blo 1859631 5963539 := bstep (se 1 (by rfl) ⟨4472654, by rfl⟩ : syracuseStep 5963539 = 8945309) B8945309
theorem B4186025 : Blo 1859631 4186025 := bstep (se 2 (by rfl) ⟨1569759, by rfl⟩ : syracuseStep 4186025 = 3139519) B3139519
theorem B7946191 : Blo 1859631 7946191 := bstep (se 1 (by rfl) ⟨5959643, by rfl⟩ : syracuseStep 7946191 = 11919287) B11919287
theorem B4710383 : Blo 1859631 4710383 := bstep (se 1 (by rfl) ⟨3532787, by rfl⟩ : syracuseStep 4710383 = 7065575) B7065575
theorem B3530783 : Blo 1859631 3530783 := bstep (se 1 (by rfl) ⟨2648087, by rfl⟩ : syracuseStep 3530783 = 5296175) B5296175
theorem B1859711 : Blo 1859631 1859711 := bstep (se 1 (by rfl) ⟨1394783, by rfl⟩ : syracuseStep 1859711 = 2789567) B2789567
theorem B1859739 : Blo 1859631 1859739 := bstep (se 1 (by rfl) ⟨1394804, by rfl⟩ : syracuseStep 1859739 = 2789609) B2789609
theorem B15900857 : Blo 1859631 15900857 := bstep (se 2 (by rfl) ⟨5962821, by rfl⟩ : syracuseStep 15900857 = 11925643) B11925643
theorem B11919595 : Blo 1859631 11919595 := bstep (se 1 (by rfl) ⟨8939696, by rfl⟩ : syracuseStep 11919595 = 17879393) B17879393
theorem B1859823 : Blo 1859631 1859823 := bstep (se 1 (by rfl) ⟨1394867, by rfl⟩ : syracuseStep 1859823 = 2789735) B2789735
theorem B2548265 : Blo 1859631 2548265 := bstep (se 2 (by rfl) ⟨955599, by rfl⟩ : syracuseStep 2548265 = 1911199) B1911199
theorem B24158827 : Blo 1859631 24158827 := bstep (se 1 (by rfl) ⟨18119120, by rfl⟩ : syracuseStep 24158827 = 36238241) B36238241
theorem B3531451 : Blo 1859631 3531451 := bstep (se 1 (by rfl) ⟨2648588, by rfl⟩ : syracuseStep 3531451 = 5297177) B5297177
theorem B1860379 : Blo 1859631 1860379 := bstep (se 1 (by rfl) ⟨1395284, by rfl⟩ : syracuseStep 1860379 = 2790569) B2790569
theorem B1860423 : Blo 1859631 1860423 := bstep (se 1 (by rfl) ⟨1395317, by rfl⟩ : syracuseStep 1860423 = 2790635) B2790635
theorem B1860479 : Blo 1859631 1860479 := bstep (se 1 (by rfl) ⟨1395359, by rfl⟩ : syracuseStep 1860479 = 2790719) B2790719
theorem B1860607 : Blo 1859631 1860607 := bstep (se 1 (by rfl) ⟨1395455, by rfl⟩ : syracuseStep 1860607 = 2790911) B2790911
theorem B1860679 : Blo 1859631 1860679 := bstep (se 1 (by rfl) ⟨1395509, by rfl⟩ : syracuseStep 1860679 = 2791019) B2791019
theorem B3531937 : Blo 1859631 3531937 := bstep (se 2 (by rfl) ⟨1324476, by rfl⟩ : syracuseStep 3531937 = 2648953) B2648953
theorem B3351775 : Blo 1859631 3351775 := bstep (se 1 (by rfl) ⟨2513831, by rfl⟩ : syracuseStep 3351775 = 5027663) B5027663
theorem B1860859 : Blo 1859631 1860859 := bstep (se 1 (by rfl) ⟨1395644, by rfl⟩ : syracuseStep 1860859 = 2791289) B2791289
theorem B1861023 : Blo 1859631 1861023 := bstep (se 1 (by rfl) ⟨1395767, by rfl⟩ : syracuseStep 1861023 = 2791535) B2791535
theorem B1861071 : Blo 1859631 1861071 := bstep (se 1 (by rfl) ⟨1395803, by rfl⟩ : syracuseStep 1861071 = 2791607) B2791607
theorem B6276635 : Blo 1859631 6276635 := bstep (se 1 (by rfl) ⟨4707476, by rfl⟩ : syracuseStep 6276635 = 9414953) B9414953
theorem B7063145 : Blo 1859631 7063145 := bstep (se 2 (by rfl) ⟨2648679, by rfl⟩ : syracuseStep 7063145 = 5297359) B5297359
theorem B4187753 : Blo 1859631 4187753 := bstep (se 2 (by rfl) ⟨1570407, by rfl⟩ : syracuseStep 4187753 = 3140815) B3140815
theorem B14321267 : Blo 1859631 14321267 := bstep (se 1 (by rfl) ⟨10740950, by rfl⟩ : syracuseStep 14321267 = 21481901) B21481901
theorem B1861351 : Blo 1859631 1861351 := bstep (se 1 (by rfl) ⟨1396013, by rfl⟩ : syracuseStep 1861351 = 2792027) B2792027
theorem B1861359 : Blo 1859631 1861359 := bstep (se 1 (by rfl) ⟨1396019, by rfl⟩ : syracuseStep 1861359 = 2792039) B2792039
theorem B6276851 : Blo 1859631 6276851 := bstep (se 1 (by rfl) ⟨4707638, by rfl⟩ : syracuseStep 6276851 = 9415277) B9415277
theorem B1861375 : Blo 1859631 1861375 := bstep (se 1 (by rfl) ⟨1396031, by rfl⟩ : syracuseStep 1861375 = 2792063) B2792063
theorem B3139337 : Blo 1859631 3139337 := bstep (se 2 (by rfl) ⟨1177251, by rfl⟩ : syracuseStep 3139337 = 2354503) B2354503
theorem B1861447 : Blo 1859631 1861447 := bstep (se 1 (by rfl) ⟨1396085, by rfl⟩ : syracuseStep 1861447 = 2792171) B2792171
theorem B1861467 : Blo 1859631 1861467 := bstep (se 1 (by rfl) ⟨1396100, by rfl⟩ : syracuseStep 1861467 = 2792201) B2792201
theorem B1861627 : Blo 1859631 1861627 := bstep (se 1 (by rfl) ⟨1396220, by rfl⟩ : syracuseStep 1861627 = 2792441) B2792441
theorem B3532871 : Blo 1859631 3532871 := bstep (se 1 (by rfl) ⟨2649653, by rfl⟩ : syracuseStep 3532871 = 5299307) B5299307
theorem B10594921 : Blo 1859631 10594921 := bstep (se 2 (by rfl) ⟨3973095, by rfl⟩ : syracuseStep 10594921 = 7946191) B7946191
theorem B3140255 : Blo 1859631 3140255 := bstep (se 1 (by rfl) ⟨2355191, by rfl⟩ : syracuseStep 3140255 = 4710383) B4710383
theorem B734506001 : Blo 1859631 734506001 := bstep (se 2 (by rfl) ⟨275439750, by rfl⟩ : syracuseStep 734506001 = 550879501) B550879501
theorem B20114489 : Blo 1859631 20114489 := bstep (se 2 (by rfl) ⟨7542933, by rfl⟩ : syracuseStep 20114489 = 15085867) B15085867
theorem B3140795 : Blo 1859631 3140795 := bstep (se 1 (by rfl) ⟨2355596, by rfl⟩ : syracuseStep 3140795 = 4711193) B4711193
theorem B6794543 : Blo 1859631 6794543 := bstep (se 1 (by rfl) ⟨5095907, by rfl⟩ : syracuseStep 6794543 = 10191815) B10191815
theorem B70692497 : Blo 1859631 70692497 := bstep (se 2 (by rfl) ⟨26509686, by rfl⟩ : syracuseStep 70692497 = 53019373) B53019373
theorem B74518217 : Blo 1859631 74518217 := bstep (se 2 (by rfl) ⟨27944331, by rfl⟩ : syracuseStep 74518217 = 55888663) B55888663
theorem B10055515 : Blo 1859631 10055515 := bstep (se 1 (by rfl) ⟨7541636, by rfl⟩ : syracuseStep 10055515 = 15083273) B15083273
theorem B7065863 : Blo 1859631 7065863 := bstep (se 1 (by rfl) ⟨5299397, by rfl⟩ : syracuseStep 7065863 = 10598795) B10598795
theorem B6279443 : Blo 1859631 6279443 := bstep (se 1 (by rfl) ⟨4709582, by rfl⟩ : syracuseStep 6279443 = 9419165) B9419165
theorem B4772137 : Blo 1859631 4772137 := bstep (se 2 (by rfl) ⟨1789551, by rfl⟩ : syracuseStep 4772137 = 3579103) B3579103
theorem B7950635 : Blo 1859631 7950635 := bstep (se 1 (by rfl) ⟨5962976, by rfl⟩ : syracuseStep 7950635 = 11925953) B11925953
theorem B122352211 : Blo 1859631 122352211 := bstep (se 1 (by rfl) ⟨91764158, by rfl⟩ : syracuseStep 122352211 = 183528317) B183528317
theorem B2789999 : Blo 1859631 2789999 := bstep (se 1 (by rfl) ⟨2092499, by rfl⟩ : syracuseStep 2789999 = 4184999) B4184999
theorem B2790119 : Blo 1859631 2790119 := bstep (se 1 (by rfl) ⟨2092589, by rfl⟩ : syracuseStep 2790119 = 4185179) B4185179
theorem B7066379 : Blo 1859631 7066379 := bstep (se 1 (by rfl) ⟨5299784, by rfl⟩ : syracuseStep 7066379 = 10599569) B10599569
theorem B4707305 : Blo 1859631 4707305 := bstep (se 2 (by rfl) ⟨1765239, by rfl⟩ : syracuseStep 4707305 = 3530479) B3530479
theorem B7951385 : Blo 1859631 7951385 := bstep (se 2 (by rfl) ⟨2981769, by rfl⟩ : syracuseStep 7951385 = 5963539) B5963539
theorem B2790683 : Blo 1859631 2790683 := bstep (se 1 (by rfl) ⟨2093012, by rfl⟩ : syracuseStep 2790683 = 4186025) B4186025
theorem B4707983 : Blo 1859631 4707983 := bstep (se 1 (by rfl) ⟨3530987, by rfl⟩ : syracuseStep 4707983 = 7061975) B7061975
theorem B6280847 : Blo 1859631 6280847 := bstep (se 1 (by rfl) ⟨4710635, by rfl⟩ : syracuseStep 6280847 = 9421271) B9421271
theorem B6706907 : Blo 1859631 6706907 := bstep (se 1 (by rfl) ⟨5030180, by rfl⟩ : syracuseStep 6706907 = 10060361) B10060361
theorem B2791151 : Blo 1859631 2791151 := bstep (se 1 (by rfl) ⟨2093363, by rfl⟩ : syracuseStep 2791151 = 4186727) B4186727
theorem B305674073 : Blo 1859631 305674073 := bstep (se 2 (by rfl) ⟨114627777, by rfl⟩ : syracuseStep 305674073 = 229255555) B229255555
theorem B50935823 : Blo 1859631 50935823 := bstep (se 1 (by rfl) ⟨38201867, by rfl⟩ : syracuseStep 50935823 = 76403735) B76403735
theorem B4708489 : Blo 1859631 4708489 := bstep (se 2 (by rfl) ⟨1765683, by rfl⟩ : syracuseStep 4708489 = 3531367) B3531367
theorem B7067837 : Blo 1859631 7067837 := bstep (se 3 (by rfl) ⟨1325219, by rfl⟩ : syracuseStep 7067837 = 2650439) B2650439
theorem B30161099 : Blo 1859631 30161099 := bstep (se 1 (by rfl) ⟨22620824, by rfl⟩ : syracuseStep 30161099 = 45241649) B45241649
theorem B5298463 : Blo 1859631 5298463 := bstep (se 1 (by rfl) ⟨3973847, by rfl⟩ : syracuseStep 5298463 = 7947695) B7947695
theorem B25467479 : Blo 1859631 25467479 := bstep (se 1 (by rfl) ⟨19100609, by rfl⟩ : syracuseStep 25467479 = 38201219) B38201219
theorem B5298817 : Blo 1859631 5298817 := bstep (se 2 (by rfl) ⟨1987056, by rfl⟩ : syracuseStep 5298817 = 3974113) B3974113
theorem B6363913 : Blo 1859631 6363913 := bstep (se 2 (by rfl) ⟨2386467, by rfl⟩ : syracuseStep 6363913 = 4772935) B4772935
theorem B30186265 : Blo 1859631 30186265 := bstep (se 2 (by rfl) ⟨11319849, by rfl⟩ : syracuseStep 30186265 = 22639699) B22639699
theorem B14129963 : Blo 1859631 14129963 := bstep (se 1 (by rfl) ⟨10597472, by rfl⟩ : syracuseStep 14129963 = 21194945) B21194945
theorem B20388667 : Blo 1859631 20388667 := bstep (se 1 (by rfl) ⟨15291500, by rfl⟩ : syracuseStep 20388667 = 30583001) B30583001
theorem B8936315 : Blo 1859631 8936315 := bstep (se 1 (by rfl) ⟨6702236, by rfl⟩ : syracuseStep 8936315 = 13404473) B13404473
theorem B4185143 : Blo 1859631 4185143 := bstep (se 1 (by rfl) ⟨3138857, by rfl⟩ : syracuseStep 4185143 = 6277715) B6277715
theorem B12909665 : Blo 1859631 12909665 := bstep (se 2 (by rfl) ⟨4841124, by rfl⟩ : syracuseStep 12909665 = 9682249) B9682249
theorem B3062951 : Blo 1859631 3062951 := bstep (se 1 (by rfl) ⟨2297213, by rfl⟩ : syracuseStep 3062951 = 4594427) B4594427
theorem B14130935 : Blo 1859631 14130935 := bstep (se 1 (by rfl) ⟨10598201, by rfl⟩ : syracuseStep 14130935 = 21196403) B21196403
theorem B20389643 : Blo 1859631 20389643 := bstep (se 1 (by rfl) ⟨15292232, by rfl⟩ : syracuseStep 20389643 = 30584465) B30584465
theorem B3530623 : Blo 1859631 3530623 := bstep (se 1 (by rfl) ⟨2647967, by rfl⟩ : syracuseStep 3530623 = 5295935) B5295935
theorem B4710271 : Blo 1859631 4710271 := bstep (se 1 (by rfl) ⟨3532703, by rfl⟩ : syracuseStep 4710271 = 7065407) B7065407
theorem B10600571 : Blo 1859631 10600571 := bstep (se 1 (by rfl) ⟨7950428, by rfl⟩ : syracuseStep 10600571 = 15900857) B15900857
theorem B4710575 : Blo 1859631 4710575 := bstep (se 1 (by rfl) ⟨3532931, by rfl⟩ : syracuseStep 4710575 = 7065863) B7065863
theorem B4186295 : Blo 1859631 4186295 := bstep (se 1 (by rfl) ⟨3139721, by rfl⟩ : syracuseStep 4186295 = 6279443) B6279443
theorem B5300423 : Blo 1859631 5300423 := bstep (se 1 (by rfl) ⟨3975317, by rfl⟩ : syracuseStep 5300423 = 7950635) B7950635
theorem B15892793 : Blo 1859631 15892793 := bstep (se 2 (by rfl) ⟨5959797, by rfl⟩ : syracuseStep 15892793 = 11919595) B11919595
theorem B1859999 : Blo 1859631 1859999 := bstep (se 1 (by rfl) ⟨1394999, by rfl⟩ : syracuseStep 1859999 = 2789999) B2789999
theorem B27181493 : Blo 1859631 27181493 := bstep (se 5 (by rfl) ⟨1274132, by rfl⟩ : syracuseStep 27181493 = 2548265) B2548265
theorem B1860079 : Blo 1859631 1860079 := bstep (se 1 (by rfl) ⟨1395059, by rfl⟩ : syracuseStep 1860079 = 2790119) B2790119
theorem B4710919 : Blo 1859631 4710919 := bstep (se 1 (by rfl) ⟨3533189, by rfl⟩ : syracuseStep 4710919 = 7066379) B7066379
theorem B3138203 : Blo 1859631 3138203 := bstep (se 1 (by rfl) ⟨2353652, by rfl⟩ : syracuseStep 3138203 = 4707305) B4707305
theorem B163136281 : Blo 1859631 163136281 := bstep (se 2 (by rfl) ⟨61176105, by rfl⟩ : syracuseStep 163136281 = 122352211) B122352211
theorem B32211769 : Blo 1859631 32211769 := bstep (se 2 (by rfl) ⟨12079413, by rfl⟩ : syracuseStep 32211769 = 24158827) B24158827
theorem B1860455 : Blo 1859631 1860455 := bstep (se 1 (by rfl) ⟨1395341, by rfl⟩ : syracuseStep 1860455 = 2790683) B2790683
theorem B40248353 : Blo 1859631 40248353 := bstep (se 2 (by rfl) ⟨15093132, by rfl⟩ : syracuseStep 40248353 = 30186265) B30186265
theorem B3138655 : Blo 1859631 3138655 := bstep (se 1 (by rfl) ⟨2353991, by rfl⟩ : syracuseStep 3138655 = 4707983) B4707983
theorem B4187231 : Blo 1859631 4187231 := bstep (se 1 (by rfl) ⟨3140423, by rfl⟩ : syracuseStep 4187231 = 6280847) B6280847
theorem B1860767 : Blo 1859631 1860767 := bstep (se 1 (by rfl) ⟨1395575, by rfl⟩ : syracuseStep 1860767 = 2791151) B2791151
theorem B33957215 : Blo 1859631 33957215 := bstep (se 1 (by rfl) ⟨25467911, by rfl⟩ : syracuseStep 33957215 = 50935823) B50935823
theorem B4711891 : Blo 1859631 4711891 := bstep (se 1 (by rfl) ⟨3533918, by rfl⟩ : syracuseStep 4711891 = 7067837) B7067837
theorem B5957543 : Blo 1859631 5957543 := bstep (se 1 (by rfl) ⟨4468157, by rfl⟩ : syracuseStep 5957543 = 8936315) B8936315
theorem B489670667 : Blo 1859631 489670667 := bstep (se 1 (by rfl) ⟨367253000, by rfl⟩ : syracuseStep 489670667 = 734506001) B734506001
theorem B2041967 : Blo 1859631 2041967 := bstep (se 1 (by rfl) ⟨1531475, by rfl⟩ : syracuseStep 2041967 = 3062951) B3062951
theorem B49678811 : Blo 1859631 49678811 := bstep (se 1 (by rfl) ⟨37259108, by rfl⟩ : syracuseStep 49678811 = 74518217) B74518217
theorem B13593095 : Blo 1859631 13593095 := bstep (se 1 (by rfl) ⟨10194821, by rfl⟩ : syracuseStep 13593095 = 20389643) B20389643
theorem B2353855 : Blo 1859631 2353855 := bstep (se 1 (by rfl) ⟨1765391, by rfl⟩ : syracuseStep 2353855 = 3530783) B3530783
theorem B21203693 : Blo 1859631 21203693 := bstep (se 3 (by rfl) ⟨3975692, by rfl⟩ : syracuseStep 21203693 = 7951385) B7951385
theorem B6277985 : Blo 1859631 6277985 := bstep (se 2 (by rfl) ⟨2354244, by rfl⟩ : syracuseStep 6277985 = 4708489) B4708489
theorem B34425773 : Blo 1859631 34425773 := bstep (se 3 (by rfl) ⟨6454832, by rfl⟩ : syracuseStep 34425773 = 12909665) B12909665
theorem B7064617 : Blo 1859631 7064617 := bstep (se 2 (by rfl) ⟨2649231, by rfl⟩ : syracuseStep 7064617 = 5298463) B5298463
theorem B14126561 : Blo 1859631 14126561 := bstep (se 2 (by rfl) ⟨5297460, by rfl⟩ : syracuseStep 14126561 = 10594921) B10594921
theorem B7065089 : Blo 1859631 7065089 := bstep (se 2 (by rfl) ⟨2649408, by rfl⟩ : syracuseStep 7065089 = 5298817) B5298817
theorem B9547511 : Blo 1859631 9547511 := bstep (se 1 (by rfl) ⟨7160633, by rfl⟩ : syracuseStep 9547511 = 14321267) B14321267
theorem B27184889 : Blo 1859631 27184889 := bstep (se 2 (by rfl) ⟨10194333, by rfl⟩ : syracuseStep 27184889 = 20388667) B20388667
theorem B2092891 : Blo 1859631 2092891 := bstep (se 1 (by rfl) ⟨1569668, by rfl⟩ : syracuseStep 2092891 = 3139337) B3139337
theorem B2355247 : Blo 1859631 2355247 := bstep (se 1 (by rfl) ⟨1766435, by rfl⟩ : syracuseStep 2355247 = 3532871) B3532871
theorem B20107399 : Blo 1859631 20107399 := bstep (se 1 (by rfl) ⟨15080549, by rfl⟩ : syracuseStep 20107399 = 30161099) B30161099
theorem B4469033 : Blo 1859631 4469033 := bstep (se 2 (by rfl) ⟨1675887, by rfl⟩ : syracuseStep 4469033 = 3351775) B3351775
theorem B16978319 : Blo 1859631 16978319 := bstep (se 1 (by rfl) ⟨12733739, by rfl⟩ : syracuseStep 16978319 = 25467479) B25467479
theorem B2093503 : Blo 1859631 2093503 := bstep (se 1 (by rfl) ⟨1570127, by rfl⟩ : syracuseStep 2093503 = 3140255) B3140255
theorem B2790095 : Blo 1859631 2790095 := bstep (se 1 (by rfl) ⟨2092571, by rfl⟩ : syracuseStep 2790095 = 4185143) B4185143
theorem B2093863 : Blo 1859631 2093863 := bstep (se 1 (by rfl) ⟨1570397, by rfl⟩ : syracuseStep 2093863 = 3140795) B3140795
theorem B13407353 : Blo 1859631 13407353 := bstep (se 2 (by rfl) ⟨5027757, by rfl⟩ : syracuseStep 13407353 = 10055515) B10055515
theorem B4707497 : Blo 1859631 4707497 := bstep (se 2 (by rfl) ⟨1765311, by rfl⟩ : syracuseStep 4707497 = 3530623) B3530623
theorem B6280361 : Blo 1859631 6280361 := bstep (se 2 (by rfl) ⟨2355135, by rfl⟩ : syracuseStep 6280361 = 4710271) B4710271
theorem B6362849 : Blo 1859631 6362849 := bstep (se 2 (by rfl) ⟨2386068, by rfl⟩ : syracuseStep 6362849 = 4772137) B4772137
theorem B4708601 : Blo 1859631 4708601 := bstep (se 2 (by rfl) ⟨1765725, by rfl⟩ : syracuseStep 4708601 = 3531451) B3531451
theorem B8485217 : Blo 1859631 8485217 := bstep (se 2 (by rfl) ⟨3181956, by rfl⟩ : syracuseStep 8485217 = 6363913) B6363913
theorem B4184423 : Blo 1859631 4184423 := bstep (se 1 (by rfl) ⟨3138317, by rfl⟩ : syracuseStep 4184423 = 6276635) B6276635
theorem B4708763 : Blo 1859631 4708763 := bstep (se 1 (by rfl) ⟨3531572, by rfl⟩ : syracuseStep 4708763 = 7063145) B7063145
theorem B2791835 : Blo 1859631 2791835 := bstep (se 1 (by rfl) ⟨2093876, by rfl⟩ : syracuseStep 2791835 = 4187753) B4187753
theorem B4471271 : Blo 1859631 4471271 := bstep (se 1 (by rfl) ⟨3353453, by rfl⟩ : syracuseStep 4471271 = 6706907) B6706907
theorem B4184567 : Blo 1859631 4184567 := bstep (se 1 (by rfl) ⟨3138425, by rfl⟩ : syracuseStep 4184567 = 6276851) B6276851
theorem B203782715 : Blo 1859631 203782715 := bstep (se 1 (by rfl) ⟨152837036, by rfl⟩ : syracuseStep 203782715 = 305674073) B305674073
theorem B4709249 : Blo 1859631 4709249 := bstep (se 2 (by rfl) ⟨1765968, by rfl⟩ : syracuseStep 4709249 = 3531937) B3531937
theorem B9419975 : Blo 1859631 9419975 := bstep (se 1 (by rfl) ⟨7064981, by rfl⟩ : syracuseStep 9419975 = 14129963) B14129963
theorem B13409659 : Blo 1859631 13409659 := bstep (se 1 (by rfl) ⟨10057244, by rfl⟩ : syracuseStep 13409659 = 20114489) B20114489
theorem B4529695 : Blo 1859631 4529695 := bstep (se 1 (by rfl) ⟨3397271, by rfl⟩ : syracuseStep 4529695 = 6794543) B6794543
theorem B47128331 : Blo 1859631 47128331 := bstep (se 1 (by rfl) ⟨35346248, by rfl⟩ : syracuseStep 47128331 = 70692497) B70692497
theorem B9420623 : Blo 1859631 9420623 := bstep (se 1 (by rfl) ⟨7065467, by rfl⟩ : syracuseStep 9420623 = 14130935) B14130935
theorem B18120995 : Blo 1859631 18120995 := bstep (se 1 (by rfl) ⟨13590746, by rfl⟩ : syracuseStep 18120995 = 27181493) B27181493
theorem B1860063 : Blo 1859631 1860063 := bstep (se 1 (by rfl) ⟨1395047, by rfl⟩ : syracuseStep 1860063 = 2790095) B2790095
theorem B8938235 : Blo 1859631 8938235 := bstep (se 1 (by rfl) ⟨6703676, by rfl⟩ : syracuseStep 8938235 = 13407353) B13407353
theorem B3138331 : Blo 1859631 3138331 := bstep (se 1 (by rfl) ⟨2353748, by rfl⟩ : syracuseStep 3138331 = 4707497) B4707497
theorem B4186907 : Blo 1859631 4186907 := bstep (se 1 (by rfl) ⟨3140180, by rfl⟩ : syracuseStep 4186907 = 6280361) B6280361
theorem B3138473 : Blo 1859631 3138473 := bstep (se 2 (by rfl) ⟨1176927, by rfl⟩ : syracuseStep 3138473 = 2353855) B2353855
theorem B217515041 : Blo 1859631 217515041 := bstep (se 2 (by rfl) ⟨81568140, by rfl⟩ : syracuseStep 217515041 = 163136281) B163136281
theorem B3139067 : Blo 1859631 3139067 := bstep (se 1 (by rfl) ⟨2354300, by rfl⟩ : syracuseStep 3139067 = 4708601) B4708601
theorem B3139175 : Blo 1859631 3139175 := bstep (se 1 (by rfl) ⟨2354381, by rfl⟩ : syracuseStep 3139175 = 4708763) B4708763
theorem B1861223 : Blo 1859631 1861223 := bstep (se 1 (by rfl) ⟨1395917, by rfl⟩ : syracuseStep 1861223 = 2791835) B2791835
theorem B9062063 : Blo 1859631 9062063 := bstep (se 1 (by rfl) ⟨6796547, by rfl⟩ : syracuseStep 9062063 = 13593095) B13593095
theorem B3139499 : Blo 1859631 3139499 := bstep (se 1 (by rfl) ⟨2354624, by rfl⟩ : syracuseStep 3139499 = 4709249) B4709249
theorem B6039593 : Blo 1859631 6039593 := bstep (se 2 (by rfl) ⟨2264847, by rfl⟩ : syracuseStep 6039593 = 4529695) B4529695
theorem B18123259 : Blo 1859631 18123259 := bstep (se 1 (by rfl) ⟨13592444, by rfl⟩ : syracuseStep 18123259 = 27184889) B27184889
theorem B31418887 : Blo 1859631 31418887 := bstep (se 1 (by rfl) ⟨23564165, by rfl⟩ : syracuseStep 31418887 = 47128331) B47128331
theorem B3140329 : Blo 1859631 3140329 := bstep (se 2 (by rfl) ⟨1177623, by rfl⟩ : syracuseStep 3140329 = 2355247) B2355247
theorem B3140383 : Blo 1859631 3140383 := bstep (se 1 (by rfl) ⟨2355287, by rfl⟩ : syracuseStep 3140383 = 4710575) B4710575
theorem B3533615 : Blo 1859631 3533615 := bstep (se 1 (by rfl) ⟨2650211, by rfl⟩ : syracuseStep 3533615 = 5300423) B5300423
theorem B10595195 : Blo 1859631 10595195 := bstep (se 1 (by rfl) ⟨7946396, by rfl⟩ : syracuseStep 10595195 = 15892793) B15892793
theorem B2092135 : Blo 1859631 2092135 := bstep (se 1 (by rfl) ⟨1569101, by rfl⟩ : syracuseStep 2092135 = 3138203) B3138203
theorem B26832235 : Blo 1859631 26832235 := bstep (se 1 (by rfl) ⟨20124176, by rfl⟩ : syracuseStep 26832235 = 40248353) B40248353
theorem B22638143 : Blo 1859631 22638143 := bstep (se 1 (by rfl) ⟨16978607, by rfl⟩ : syracuseStep 22638143 = 33957215) B33957215
theorem B326447111 : Blo 1859631 326447111 := bstep (se 1 (by rfl) ⟨244835333, by rfl⟩ : syracuseStep 326447111 = 489670667) B489670667
theorem B5656811 : Blo 1859631 5656811 := bstep (se 1 (by rfl) ⟨4242608, by rfl⟩ : syracuseStep 5656811 = 8485217) B8485217
theorem B2789615 : Blo 1859631 2789615 := bstep (se 1 (by rfl) ⟨2092211, by rfl⟩ : syracuseStep 2789615 = 4184423) B4184423
theorem B2789711 : Blo 1859631 2789711 := bstep (se 1 (by rfl) ⟨2092283, by rfl⟩ : syracuseStep 2789711 = 4184567) B4184567
theorem B14135795 : Blo 1859631 14135795 := bstep (se 1 (by rfl) ⟨10601846, by rfl⟩ : syracuseStep 14135795 = 21203693) B21203693
theorem B17879545 : Blo 1859631 17879545 := bstep (se 2 (by rfl) ⟨6704829, by rfl⟩ : syracuseStep 17879545 = 13409659) B13409659
theorem B22950515 : Blo 1859631 22950515 := bstep (se 1 (by rfl) ⟨17212886, by rfl⟩ : syracuseStep 22950515 = 34425773) B34425773
theorem B6279983 : Blo 1859631 6279983 := bstep (se 1 (by rfl) ⟨4709987, by rfl⟩ : syracuseStep 6279983 = 9419975) B9419975
theorem B9417707 : Blo 1859631 9417707 := bstep (se 1 (by rfl) ⟨7063280, by rfl⟩ : syracuseStep 9417707 = 14126561) B14126561
theorem B2790521 : Blo 1859631 2790521 := bstep (se 2 (by rfl) ⟨1046445, by rfl⟩ : syracuseStep 2790521 = 2092891) B2092891
theorem B6280415 : Blo 1859631 6280415 := bstep (se 1 (by rfl) ⟨4710311, by rfl⟩ : syracuseStep 6280415 = 9420623) B9420623
theorem B7067047 : Blo 1859631 7067047 := bstep (se 1 (by rfl) ⟨5300285, by rfl⟩ : syracuseStep 7067047 = 10600571) B10600571
theorem B2790863 : Blo 1859631 2790863 := bstep (se 1 (by rfl) ⟨2093147, by rfl⟩ : syracuseStep 2790863 = 4186295) B4186295
theorem B26809865 : Blo 1859631 26809865 := bstep (se 2 (by rfl) ⟨10053699, by rfl⟩ : syracuseStep 26809865 = 20107399) B20107399
theorem B2979355 : Blo 1859631 2979355 := bstep (se 1 (by rfl) ⟨2234516, by rfl⟩ : syracuseStep 2979355 = 4469033) B4469033
theorem B11318879 : Blo 1859631 11318879 := bstep (se 1 (by rfl) ⟨8489159, by rfl⟩ : syracuseStep 11318879 = 16978319) B16978319
theorem B5445245 : Blo 1859631 5445245 := bstep (se 3 (by rfl) ⟨1020983, by rfl⟩ : syracuseStep 5445245 = 2041967) B2041967
theorem B2791337 : Blo 1859631 2791337 := bstep (se 2 (by rfl) ⟨1046751, by rfl⟩ : syracuseStep 2791337 = 2093503) B2093503
theorem B6281225 : Blo 1859631 6281225 := bstep (se 2 (by rfl) ⟨2355459, by rfl⟩ : syracuseStep 6281225 = 4710919) B4710919
theorem B2791487 : Blo 1859631 2791487 := bstep (se 1 (by rfl) ⟨2093615, by rfl⟩ : syracuseStep 2791487 = 4187231) B4187231
theorem B2791817 : Blo 1859631 2791817 := bstep (se 2 (by rfl) ⟨1046931, by rfl⟩ : syracuseStep 2791817 = 2093863) B2093863
theorem B42949025 : Blo 1859631 42949025 := bstep (se 2 (by rfl) ⟨16105884, by rfl⟩ : syracuseStep 42949025 = 32211769) B32211769
theorem B4241899 : Blo 1859631 4241899 := bstep (se 1 (by rfl) ⟨3181424, by rfl⟩ : syracuseStep 4241899 = 6362849) B6362849
theorem B3971695 : Blo 1859631 3971695 := bstep (se 1 (by rfl) ⟨2978771, by rfl⟩ : syracuseStep 3971695 = 5957543) B5957543
theorem B9419489 : Blo 1859631 9419489 := bstep (se 2 (by rfl) ⟨3532308, by rfl⟩ : syracuseStep 9419489 = 7064617) B7064617
theorem B4184873 : Blo 1859631 4184873 := bstep (se 2 (by rfl) ⟨1569327, by rfl⟩ : syracuseStep 4184873 = 3138655) B3138655
theorem B33119207 : Blo 1859631 33119207 := bstep (se 1 (by rfl) ⟨24839405, by rfl⟩ : syracuseStep 33119207 = 49678811) B49678811
theorem B2980847 : Blo 1859631 2980847 := bstep (se 1 (by rfl) ⟨2235635, by rfl⟩ : syracuseStep 2980847 = 4471271) B4471271
theorem B135855143 : Blo 1859631 135855143 := bstep (se 1 (by rfl) ⟨101891357, by rfl⟩ : syracuseStep 135855143 = 203782715) B203782715
theorem B4185323 : Blo 1859631 4185323 := bstep (se 1 (by rfl) ⟨3138992, by rfl⟩ : syracuseStep 4185323 = 6277985) B6277985
theorem B6282521 : Blo 1859631 6282521 := bstep (se 2 (by rfl) ⟨2355945, by rfl⟩ : syracuseStep 6282521 = 4711891) B4711891
theorem B25460029 : Blo 1859631 25460029 := bstep (se 3 (by rfl) ⟨4773755, by rfl⟩ : syracuseStep 25460029 = 9547511) B9547511
theorem B4710059 : Blo 1859631 4710059 := bstep (se 1 (by rfl) ⟨3532544, by rfl⟩ : syracuseStep 4710059 = 7065089) B7065089
theorem B1859743 : Blo 1859631 1859743 := bstep (se 1 (by rfl) ⟨1394807, by rfl⟩ : syracuseStep 1859743 = 2789615) B2789615
theorem B1859807 : Blo 1859631 1859807 := bstep (se 1 (by rfl) ⟨1394855, by rfl⟩ : syracuseStep 1859807 = 2789711) B2789711
theorem B4186655 : Blo 1859631 4186655 := bstep (se 1 (by rfl) ⟨3139991, by rfl⟩ : syracuseStep 4186655 = 6279983) B6279983
theorem B23839393 : Blo 1859631 23839393 := bstep (se 2 (by rfl) ⟨8939772, by rfl⟩ : syracuseStep 23839393 = 17879545) B17879545
theorem B1860347 : Blo 1859631 1860347 := bstep (se 1 (by rfl) ⟨1395260, by rfl⟩ : syracuseStep 1860347 = 2790521) B2790521
theorem B4186943 : Blo 1859631 4186943 := bstep (se 1 (by rfl) ⟨3140207, by rfl⟩ : syracuseStep 4186943 = 6280415) B6280415
theorem B1860575 : Blo 1859631 1860575 := bstep (se 1 (by rfl) ⟨1395431, by rfl⟩ : syracuseStep 1860575 = 2790863) B2790863
theorem B4187105 : Blo 1859631 4187105 := bstep (se 2 (by rfl) ⟨1570164, by rfl⟩ : syracuseStep 4187105 = 3140329) B3140329
theorem B4187177 : Blo 1859631 4187177 := bstep (se 2 (by rfl) ⟨1570191, by rfl⟩ : syracuseStep 4187177 = 3140383) B3140383
theorem B1860891 : Blo 1859631 1860891 := bstep (se 1 (by rfl) ⟨1395668, by rfl⟩ : syracuseStep 1860891 = 2791337) B2791337
theorem B4187483 : Blo 1859631 4187483 := bstep (se 1 (by rfl) ⟨3140612, by rfl⟩ : syracuseStep 4187483 = 6281225) B6281225
theorem B1860991 : Blo 1859631 1860991 := bstep (se 1 (by rfl) ⟨1395743, by rfl⟩ : syracuseStep 1860991 = 2791487) B2791487
theorem B1861211 : Blo 1859631 1861211 := bstep (se 1 (by rfl) ⟨1395908, by rfl⟩ : syracuseStep 1861211 = 2791817) B2791817
theorem B28632683 : Blo 1859631 28632683 := bstep (se 1 (by rfl) ⟨21474512, by rfl⟩ : syracuseStep 28632683 = 42949025) B42949025
theorem B35776313 : Blo 1859631 35776313 := bstep (se 2 (by rfl) ⟨13416117, by rfl⟩ : syracuseStep 35776313 = 26832235) B26832235
theorem B9422729 : Blo 1859631 9422729 := bstep (se 2 (by rfl) ⟨3533523, by rfl⟩ : syracuseStep 9422729 = 7067047) B7067047
theorem B7063463 : Blo 1859631 7063463 := bstep (se 1 (by rfl) ⟨5297597, by rfl⟩ : syracuseStep 7063463 = 10595195) B10595195
theorem B22079471 : Blo 1859631 22079471 := bstep (se 1 (by rfl) ⟨16559603, by rfl⟩ : syracuseStep 22079471 = 33119207) B33119207
theorem B4188347 : Blo 1859631 4188347 := bstep (se 1 (by rfl) ⟨3141260, by rfl⟩ : syracuseStep 4188347 = 6282521) B6282521
theorem B15092095 : Blo 1859631 15092095 := bstep (se 1 (by rfl) ⟨11319071, by rfl⟩ : syracuseStep 15092095 = 22638143) B22638143
theorem B3140039 : Blo 1859631 3140039 := bstep (se 1 (by rfl) ⟨2355029, by rfl⟩ : syracuseStep 3140039 = 4710059) B4710059
theorem B7948925 : Blo 1859631 7948925 := bstep (se 3 (by rfl) ⟨1490423, by rfl⟩ : syracuseStep 7948925 = 2980847) B2980847
theorem B217631407 : Blo 1859631 217631407 := bstep (se 1 (by rfl) ⟨163223555, by rfl⟩ : syracuseStep 217631407 = 326447111) B326447111
theorem B9423863 : Blo 1859631 9423863 := bstep (se 1 (by rfl) ⟨7067897, by rfl⟩ : syracuseStep 9423863 = 14135795) B14135795
theorem B2092315 : Blo 1859631 2092315 := bstep (se 1 (by rfl) ⟨1569236, by rfl⟩ : syracuseStep 2092315 = 3138473) B3138473
theorem B15084829 : Blo 1859631 15084829 := bstep (se 3 (by rfl) ⟨2828405, by rfl⟩ : syracuseStep 15084829 = 5656811) B5656811
theorem B5655865 : Blo 1859631 5655865 := bstep (se 2 (by rfl) ⟨2120949, by rfl⟩ : syracuseStep 5655865 = 4241899) B4241899
theorem B6278471 : Blo 1859631 6278471 := bstep (se 1 (by rfl) ⟨4708853, by rfl⟩ : syracuseStep 6278471 = 9417707) B9417707
theorem B145010027 : Blo 1859631 145010027 := bstep (se 1 (by rfl) ⟨108757520, by rfl⟩ : syracuseStep 145010027 = 217515041) B217515041
theorem B5295593 : Blo 1859631 5295593 := bstep (se 2 (by rfl) ⟨1985847, by rfl⟩ : syracuseStep 5295593 = 3971695) B3971695
theorem B2092711 : Blo 1859631 2092711 := bstep (se 1 (by rfl) ⟨1569533, by rfl⟩ : syracuseStep 2092711 = 3139067) B3139067
theorem B2092783 : Blo 1859631 2092783 := bstep (se 1 (by rfl) ⟨1569587, by rfl⟩ : syracuseStep 2092783 = 3139175) B3139175
theorem B6041375 : Blo 1859631 6041375 := bstep (se 1 (by rfl) ⟨4531031, by rfl⟩ : syracuseStep 6041375 = 9062063) B9062063
theorem B2092999 : Blo 1859631 2092999 := bstep (se 1 (by rfl) ⟨1569749, by rfl⟩ : syracuseStep 2092999 = 3139499) B3139499
theorem B4026395 : Blo 1859631 4026395 := bstep (se 1 (by rfl) ⟨3019796, by rfl⟩ : syracuseStep 4026395 = 6039593) B6039593
theorem B2789513 : Blo 1859631 2789513 := bstep (se 2 (by rfl) ⟨1046067, by rfl⟩ : syracuseStep 2789513 = 2092135) B2092135
theorem B30183677 : Blo 1859631 30183677 := bstep (se 3 (by rfl) ⟨5659439, by rfl⟩ : syracuseStep 30183677 = 11318879) B11318879
theorem B14520653 : Blo 1859631 14520653 := bstep (se 3 (by rfl) ⟨2722622, by rfl⟩ : syracuseStep 14520653 = 5445245) B5445245
theorem B6279659 : Blo 1859631 6279659 := bstep (se 1 (by rfl) ⟨4709744, by rfl⟩ : syracuseStep 6279659 = 9419489) B9419489
theorem B2789915 : Blo 1859631 2789915 := bstep (se 1 (by rfl) ⟨2092436, by rfl⟩ : syracuseStep 2789915 = 4184873) B4184873
theorem B2355743 : Blo 1859631 2355743 := bstep (se 1 (by rfl) ⟨1766807, by rfl⟩ : syracuseStep 2355743 = 3533615) B3533615
theorem B23835293 : Blo 1859631 23835293 := bstep (se 3 (by rfl) ⟨4469117, by rfl⟩ : syracuseStep 23835293 = 8938235) B8938235
theorem B2790215 : Blo 1859631 2790215 := bstep (se 1 (by rfl) ⟨2092661, by rfl⟩ : syracuseStep 2790215 = 4185323) B4185323
theorem B12080663 : Blo 1859631 12080663 := bstep (se 1 (by rfl) ⟨9060497, by rfl⟩ : syracuseStep 12080663 = 18120995) B18120995
theorem B15300343 : Blo 1859631 15300343 := bstep (se 1 (by rfl) ⟨11475257, by rfl⟩ : syracuseStep 15300343 = 22950515) B22950515
theorem B2791271 : Blo 1859631 2791271 := bstep (se 1 (by rfl) ⟨2093453, by rfl⟩ : syracuseStep 2791271 = 4186907) B4186907
theorem B24164345 : Blo 1859631 24164345 := bstep (se 2 (by rfl) ⟨9061629, by rfl⟩ : syracuseStep 24164345 = 18123259) B18123259
theorem B41891849 : Blo 1859631 41891849 := bstep (se 2 (by rfl) ⟨15709443, by rfl⟩ : syracuseStep 41891849 = 31418887) B31418887
theorem B17873243 : Blo 1859631 17873243 := bstep (se 1 (by rfl) ⟨13404932, by rfl⟩ : syracuseStep 17873243 = 26809865) B26809865
theorem B4184441 : Blo 1859631 4184441 := bstep (se 2 (by rfl) ⟨1569165, by rfl⟩ : syracuseStep 4184441 = 3138331) B3138331
theorem B33946705 : Blo 1859631 33946705 := bstep (se 2 (by rfl) ⟨12730014, by rfl⟩ : syracuseStep 33946705 = 25460029) B25460029
theorem B90570095 : Blo 1859631 90570095 := bstep (se 1 (by rfl) ⟨67927571, by rfl⟩ : syracuseStep 90570095 = 135855143) B135855143
theorem B3972473 : Blo 1859631 3972473 := bstep (se 2 (by rfl) ⟨1489677, by rfl⟩ : syracuseStep 3972473 = 2979355) B2979355
theorem B1859675 : Blo 1859631 1859675 := bstep (se 1 (by rfl) ⟨1394756, by rfl⟩ : syracuseStep 1859675 = 2789513) B2789513
theorem B4186439 : Blo 1859631 4186439 := bstep (se 1 (by rfl) ⟨3139829, by rfl⟩ : syracuseStep 4186439 = 6279659) B6279659
theorem B1859943 : Blo 1859631 1859943 := bstep (se 1 (by rfl) ⟨1394957, by rfl⟩ : syracuseStep 1859943 = 2789915) B2789915
theorem B1860143 : Blo 1859631 1860143 := bstep (se 1 (by rfl) ⟨1395107, by rfl⟩ : syracuseStep 1860143 = 2790215) B2790215
theorem B31785857 : Blo 1859631 31785857 := bstep (se 2 (by rfl) ⟨11919696, by rfl⟩ : syracuseStep 31785857 = 23839393) B23839393
theorem B8053775 : Blo 1859631 8053775 := bstep (se 1 (by rfl) ⟨6040331, by rfl⟩ : syracuseStep 8053775 = 12080663) B12080663
theorem B19088455 : Blo 1859631 19088455 := bstep (se 1 (by rfl) ⟨14316341, by rfl⟩ : syracuseStep 19088455 = 28632683) B28632683
theorem B1860847 : Blo 1859631 1860847 := bstep (se 1 (by rfl) ⟨1395635, by rfl⟩ : syracuseStep 1860847 = 2791271) B2791271
theorem B27927899 : Blo 1859631 27927899 := bstep (se 1 (by rfl) ⟨20945924, by rfl⟩ : syracuseStep 27927899 = 41891849) B41891849
theorem B45262273 : Blo 1859631 45262273 := bstep (se 2 (by rfl) ⟨16973352, by rfl⟩ : syracuseStep 45262273 = 33946705) B33946705
theorem B20113105 : Blo 1859631 20113105 := bstep (se 2 (by rfl) ⟨7542414, by rfl⟩ : syracuseStep 20113105 = 15084829) B15084829
theorem B2648315 : Blo 1859631 2648315 := bstep (se 1 (by rfl) ⟨1986236, by rfl⟩ : syracuseStep 2648315 = 3972473) B3972473
theorem B20400457 : Blo 1859631 20400457 := bstep (se 2 (by rfl) ⟨7650171, by rfl⟩ : syracuseStep 20400457 = 15300343) B15300343
theorem B235514357 : Blo 1859631 235514357 := bstep (se 5 (by rfl) ⟨11039735, by rfl⟩ : syracuseStep 235514357 = 22079471) B22079471
theorem B20122451 : Blo 1859631 20122451 := bstep (se 1 (by rfl) ⟨15091838, by rfl⟩ : syracuseStep 20122451 = 30183677) B30183677
theorem B20122793 : Blo 1859631 20122793 := bstep (se 2 (by rfl) ⟨7546047, by rfl⟩ : syracuseStep 20122793 = 15092095) B15092095
theorem B23850875 : Blo 1859631 23850875 := bstep (se 1 (by rfl) ⟨17888156, by rfl⟩ : syracuseStep 23850875 = 35776313) B35776313
theorem B16109563 : Blo 1859631 16109563 := bstep (se 1 (by rfl) ⟨12082172, by rfl⟩ : syracuseStep 16109563 = 24164345) B24164345
theorem B11915495 : Blo 1859631 11915495 := bstep (se 1 (by rfl) ⟨8936621, by rfl⟩ : syracuseStep 11915495 = 17873243) B17873243
theorem B2789627 : Blo 1859631 2789627 := bstep (se 1 (by rfl) ⟨2092220, by rfl⟩ : syracuseStep 2789627 = 4184441) B4184441
theorem B2093359 : Blo 1859631 2093359 := bstep (se 1 (by rfl) ⟨1570019, by rfl⟩ : syracuseStep 2093359 = 3140039) B3140039
theorem B2789753 : Blo 1859631 2789753 := bstep (se 2 (by rfl) ⟨1046157, by rfl⟩ : syracuseStep 2789753 = 2092315) B2092315
theorem B7541153 : Blo 1859631 7541153 := bstep (se 2 (by rfl) ⟨2827932, by rfl⟩ : syracuseStep 7541153 = 5655865) B5655865
theorem B2790281 : Blo 1859631 2790281 := bstep (se 2 (by rfl) ⟨1046355, by rfl⟩ : syracuseStep 2790281 = 2092711) B2092711
theorem B60380063 : Blo 1859631 60380063 := bstep (se 1 (by rfl) ⟨45285047, by rfl⟩ : syracuseStep 60380063 = 90570095) B90570095
theorem B2790377 : Blo 1859631 2790377 := bstep (se 2 (by rfl) ⟨1046391, by rfl⟩ : syracuseStep 2790377 = 2092783) B2092783
theorem B4027583 : Blo 1859631 4027583 := bstep (se 1 (by rfl) ⟨3020687, by rfl⟩ : syracuseStep 4027583 = 6041375) B6041375
theorem B2790665 : Blo 1859631 2790665 := bstep (se 2 (by rfl) ⟨1046499, by rfl⟩ : syracuseStep 2790665 = 2092999) B2092999
theorem B2684263 : Blo 1859631 2684263 := bstep (se 1 (by rfl) ⟨2013197, by rfl⟩ : syracuseStep 2684263 = 4026395) B4026395
theorem B9680435 : Blo 1859631 9680435 := bstep (se 1 (by rfl) ⟨7260326, by rfl⟩ : syracuseStep 9680435 = 14520653) B14520653
theorem B2791103 : Blo 1859631 2791103 := bstep (se 1 (by rfl) ⟨2093327, by rfl⟩ : syracuseStep 2791103 = 4186655) B4186655
theorem B15890195 : Blo 1859631 15890195 := bstep (se 1 (by rfl) ⟨11917646, by rfl⟩ : syracuseStep 15890195 = 23835293) B23835293
theorem B2791295 : Blo 1859631 2791295 := bstep (se 1 (by rfl) ⟨2093471, by rfl⟩ : syracuseStep 2791295 = 4186943) B4186943
theorem B2791403 : Blo 1859631 2791403 := bstep (se 1 (by rfl) ⟨2093552, by rfl⟩ : syracuseStep 2791403 = 4187105) B4187105
theorem B2791451 : Blo 1859631 2791451 := bstep (se 1 (by rfl) ⟨2093588, by rfl⟩ : syracuseStep 2791451 = 4187177) B4187177
theorem B2791655 : Blo 1859631 2791655 := bstep (se 1 (by rfl) ⟨2093741, by rfl⟩ : syracuseStep 2791655 = 4187483) B4187483
theorem B290175209 : Blo 1859631 290175209 := bstep (se 2 (by rfl) ⟨108815703, by rfl⟩ : syracuseStep 290175209 = 217631407) B217631407
theorem B6281819 : Blo 1859631 6281819 := bstep (se 1 (by rfl) ⟨4711364, by rfl⟩ : syracuseStep 6281819 = 9422729) B9422729
theorem B4708975 : Blo 1859631 4708975 := bstep (se 1 (by rfl) ⟨3531731, by rfl⟩ : syracuseStep 4708975 = 7063463) B7063463
theorem B6281981 : Blo 1859631 6281981 := bstep (se 3 (by rfl) ⟨1177871, by rfl⟩ : syracuseStep 6281981 = 2355743) B2355743
theorem B2792231 : Blo 1859631 2792231 := bstep (se 1 (by rfl) ⟨2094173, by rfl⟩ : syracuseStep 2792231 = 4188347) B4188347
theorem B5299283 : Blo 1859631 5299283 := bstep (se 1 (by rfl) ⟨3974462, by rfl⟩ : syracuseStep 5299283 = 7948925) B7948925
theorem B6282575 : Blo 1859631 6282575 := bstep (se 1 (by rfl) ⟨4711931, by rfl⟩ : syracuseStep 6282575 = 9423863) B9423863
theorem B4185647 : Blo 1859631 4185647 := bstep (se 1 (by rfl) ⟨3139235, by rfl⟩ : syracuseStep 4185647 = 6278471) B6278471
theorem B96673351 : Blo 1859631 96673351 := bstep (se 1 (by rfl) ⟨72505013, by rfl⟩ : syracuseStep 96673351 = 145010027) B145010027
theorem B3530395 : Blo 1859631 3530395 := bstep (se 1 (by rfl) ⟨2647796, by rfl⟩ : syracuseStep 3530395 = 5295593) B5295593
theorem B1859751 : Blo 1859631 1859751 := bstep (se 1 (by rfl) ⟨1394813, by rfl⟩ : syracuseStep 1859751 = 2789627) B2789627
theorem B14131421 : Blo 1859631 14131421 := bstep (se 3 (by rfl) ⟨2649641, by rfl⟩ : syracuseStep 14131421 = 5299283) B5299283
theorem B1859835 : Blo 1859631 1859835 := bstep (se 1 (by rfl) ⟨1394876, by rfl⟩ : syracuseStep 1859835 = 2789753) B2789753
theorem B10740221 : Blo 1859631 10740221 := bstep (se 3 (by rfl) ⟨2013791, by rfl⟩ : syracuseStep 10740221 = 4027583) B4027583
theorem B1860187 : Blo 1859631 1860187 := bstep (se 1 (by rfl) ⟨1395140, by rfl⟩ : syracuseStep 1860187 = 2790281) B2790281
theorem B1860251 : Blo 1859631 1860251 := bstep (se 1 (by rfl) ⟨1395188, by rfl⟩ : syracuseStep 1860251 = 2790377) B2790377
theorem B7062173 : Blo 1859631 7062173 := bstep (se 3 (by rfl) ⟨1324157, by rfl⟩ : syracuseStep 7062173 = 2648315) B2648315
theorem B1860443 : Blo 1859631 1860443 := bstep (se 1 (by rfl) ⟨1395332, by rfl⟩ : syracuseStep 1860443 = 2790665) B2790665
theorem B1860735 : Blo 1859631 1860735 := bstep (se 1 (by rfl) ⟨1395551, by rfl⟩ : syracuseStep 1860735 = 2791103) B2791103
theorem B10593463 : Blo 1859631 10593463 := bstep (se 1 (by rfl) ⟨7945097, by rfl⟩ : syracuseStep 10593463 = 15890195) B15890195
theorem B1860863 : Blo 1859631 1860863 := bstep (se 1 (by rfl) ⟨1395647, by rfl⟩ : syracuseStep 1860863 = 2791295) B2791295
theorem B1860935 : Blo 1859631 1860935 := bstep (se 1 (by rfl) ⟨1395701, by rfl⟩ : syracuseStep 1860935 = 2791403) B2791403
theorem B1860967 : Blo 1859631 1860967 := bstep (se 1 (by rfl) ⟨1395725, by rfl⟩ : syracuseStep 1860967 = 2791451) B2791451
theorem B1861103 : Blo 1859631 1861103 := bstep (se 1 (by rfl) ⟨1395827, by rfl⟩ : syracuseStep 1861103 = 2791655) B2791655
theorem B157009571 : Blo 1859631 157009571 := bstep (se 1 (by rfl) ⟨117757178, by rfl⟩ : syracuseStep 157009571 = 235514357) B235514357
theorem B4187879 : Blo 1859631 4187879 := bstep (se 1 (by rfl) ⟨3140909, by rfl⟩ : syracuseStep 4187879 = 6281819) B6281819
theorem B4187987 : Blo 1859631 4187987 := bstep (se 1 (by rfl) ⟨3140990, by rfl⟩ : syracuseStep 4187987 = 6281981) B6281981
theorem B1861487 : Blo 1859631 1861487 := bstep (se 1 (by rfl) ⟨1396115, by rfl⟩ : syracuseStep 1861487 = 2792231) B2792231
theorem B4188383 : Blo 1859631 4188383 := bstep (se 1 (by rfl) ⟨3141287, by rfl⟩ : syracuseStep 4188383 = 6282575) B6282575
theorem B27200609 : Blo 1859631 27200609 := bstep (se 2 (by rfl) ⟨10200228, by rfl⟩ : syracuseStep 27200609 = 20400457) B20400457
theorem B5369183 : Blo 1859631 5369183 := bstep (se 1 (by rfl) ⟨4026887, by rfl⟩ : syracuseStep 5369183 = 8053775) B8053775
theorem B6278633 : Blo 1859631 6278633 := bstep (se 2 (by rfl) ⟨2354487, by rfl⟩ : syracuseStep 6278633 = 4708975) B4708975
theorem B193450139 : Blo 1859631 193450139 := bstep (se 1 (by rfl) ⟨145087604, by rfl⟩ : syracuseStep 193450139 = 290175209) B290175209
theorem B13414967 : Blo 1859631 13414967 := bstep (se 1 (by rfl) ⟨10061225, by rfl⟩ : syracuseStep 13414967 = 20122451) B20122451
theorem B128897801 : Blo 1859631 128897801 := bstep (se 2 (by rfl) ⟨48336675, by rfl⟩ : syracuseStep 128897801 = 96673351) B96673351
theorem B13415195 : Blo 1859631 13415195 := bstep (se 1 (by rfl) ⟨10061396, by rfl⟩ : syracuseStep 13415195 = 20122793) B20122793
theorem B4707193 : Blo 1859631 4707193 := bstep (se 2 (by rfl) ⟨1765197, by rfl⟩ : syracuseStep 4707193 = 3530395) B3530395
theorem B26817473 : Blo 1859631 26817473 := bstep (se 2 (by rfl) ⟨10056552, by rfl⟩ : syracuseStep 26817473 = 20113105) B20113105
theorem B2790431 : Blo 1859631 2790431 := bstep (se 1 (by rfl) ⟨2092823, by rfl⟩ : syracuseStep 2790431 = 4185647) B4185647
theorem B7943663 : Blo 1859631 7943663 := bstep (se 1 (by rfl) ⟨5957747, by rfl⟩ : syracuseStep 7943663 = 11915495) B11915495
theorem B2790959 : Blo 1859631 2790959 := bstep (se 1 (by rfl) ⟨2093219, by rfl⟩ : syracuseStep 2790959 = 4186439) B4186439
theorem B5027435 : Blo 1859631 5027435 := bstep (se 1 (by rfl) ⟨3770576, by rfl⟩ : syracuseStep 5027435 = 7541153) B7541153
theorem B2791145 : Blo 1859631 2791145 := bstep (se 2 (by rfl) ⟨1046679, by rfl⟩ : syracuseStep 2791145 = 2093359) B2093359
theorem B21190571 : Blo 1859631 21190571 := bstep (se 1 (by rfl) ⟨15892928, by rfl⟩ : syracuseStep 21190571 = 31785857) B31785857
theorem B40253375 : Blo 1859631 40253375 := bstep (se 1 (by rfl) ⟨30190031, by rfl⟩ : syracuseStep 40253375 = 60380063) B60380063
theorem B18618599 : Blo 1859631 18618599 := bstep (se 1 (by rfl) ⟨13963949, by rfl⟩ : syracuseStep 18618599 = 27927899) B27927899
theorem B6453623 : Blo 1859631 6453623 := bstep (se 1 (by rfl) ⟨4840217, by rfl⟩ : syracuseStep 6453623 = 9680435) B9680435
theorem B25451273 : Blo 1859631 25451273 := bstep (se 2 (by rfl) ⟨9544227, by rfl⟩ : syracuseStep 25451273 = 19088455) B19088455
theorem B3579017 : Blo 1859631 3579017 := bstep (se 2 (by rfl) ⟨1342131, by rfl⟩ : syracuseStep 3579017 = 2684263) B2684263
theorem B60349697 : Blo 1859631 60349697 := bstep (se 2 (by rfl) ⟨22631136, by rfl⟩ : syracuseStep 60349697 = 45262273) B45262273
theorem B15900583 : Blo 1859631 15900583 := bstep (se 1 (by rfl) ⟨11925437, by rfl⟩ : syracuseStep 15900583 = 23850875) B23850875
theorem B21479417 : Blo 1859631 21479417 := bstep (se 2 (by rfl) ⟨8054781, by rfl⟩ : syracuseStep 21479417 = 16109563) B16109563
theorem B128966759 : Blo 1859631 128966759 := bstep (se 1 (by rfl) ⟨96725069, by rfl⟩ : syracuseStep 128966759 = 193450139) B193450139
theorem B9420947 : Blo 1859631 9420947 := bstep (se 1 (by rfl) ⟨7065710, by rfl⟩ : syracuseStep 9420947 = 14131421) B14131421
theorem B7160147 : Blo 1859631 7160147 := bstep (se 1 (by rfl) ⟨5370110, by rfl⟩ : syracuseStep 7160147 = 10740221) B10740221
theorem B1860287 : Blo 1859631 1860287 := bstep (se 1 (by rfl) ⟨1395215, by rfl⟩ : syracuseStep 1860287 = 2790431) B2790431
theorem B1860639 : Blo 1859631 1860639 := bstep (se 1 (by rfl) ⟨1395479, by rfl⟩ : syracuseStep 1860639 = 2790959) B2790959
theorem B3351623 : Blo 1859631 3351623 := bstep (se 1 (by rfl) ⟨2513717, by rfl⟩ : syracuseStep 3351623 = 5027435) B5027435
theorem B1860763 : Blo 1859631 1860763 := bstep (se 1 (by rfl) ⟨1395572, by rfl⟩ : syracuseStep 1860763 = 2791145) B2791145
theorem B6276257 : Blo 1859631 6276257 := bstep (se 2 (by rfl) ⟨2353596, by rfl⟩ : syracuseStep 6276257 = 4707193) B4707193
theorem B38176181 : Blo 1859631 38176181 := bstep (se 5 (by rfl) ⟨1789508, by rfl⟩ : syracuseStep 38176181 = 3579017) B3579017
theorem B12412399 : Blo 1859631 12412399 := bstep (se 1 (by rfl) ⟨9309299, by rfl⟩ : syracuseStep 12412399 = 18618599) B18618599
theorem B14124617 : Blo 1859631 14124617 := bstep (se 2 (by rfl) ⟨5296731, by rfl⟩ : syracuseStep 14124617 = 10593463) B10593463
theorem B4302415 : Blo 1859631 4302415 := bstep (se 1 (by rfl) ⟨3226811, by rfl⟩ : syracuseStep 4302415 = 6453623) B6453623
theorem B40233131 : Blo 1859631 40233131 := bstep (se 1 (by rfl) ⟨30174848, by rfl⟩ : syracuseStep 40233131 = 60349697) B60349697
theorem B17878315 : Blo 1859631 17878315 := bstep (se 1 (by rfl) ⟨13408736, by rfl⟩ : syracuseStep 17878315 = 26817473) B26817473
theorem B5295775 : Blo 1859631 5295775 := bstep (se 1 (by rfl) ⟨3971831, by rfl⟩ : syracuseStep 5295775 = 7943663) B7943663
theorem B14127047 : Blo 1859631 14127047 := bstep (se 1 (by rfl) ⟨10595285, by rfl⟩ : syracuseStep 14127047 = 21190571) B21190571
theorem B1674768757 : Blo 1859631 1674768757 := bstep (se 5 (by rfl) ⟨78504785, by rfl⟩ : syracuseStep 1674768757 = 157009571) B157009571
theorem B18133739 : Blo 1859631 18133739 := bstep (se 1 (by rfl) ⟨13600304, by rfl⟩ : syracuseStep 18133739 = 27200609) B27200609
theorem B8943311 : Blo 1859631 8943311 := bstep (se 1 (by rfl) ⟨6707483, by rfl⟩ : syracuseStep 8943311 = 13414967) B13414967
theorem B4708115 : Blo 1859631 4708115 := bstep (se 1 (by rfl) ⟨3531086, by rfl⟩ : syracuseStep 4708115 = 7062173) B7062173
theorem B85931867 : Blo 1859631 85931867 := bstep (se 1 (by rfl) ⟨64448900, by rfl⟩ : syracuseStep 85931867 = 128897801) B128897801
theorem B8943463 : Blo 1859631 8943463 := bstep (se 1 (by rfl) ⟨6707597, by rfl⟩ : syracuseStep 8943463 = 13415195) B13415195
theorem B2791919 : Blo 1859631 2791919 := bstep (se 1 (by rfl) ⟨2093939, by rfl⟩ : syracuseStep 2791919 = 4187879) B4187879
theorem B2791991 : Blo 1859631 2791991 := bstep (se 1 (by rfl) ⟨2093993, by rfl⟩ : syracuseStep 2791991 = 4187987) B4187987
theorem B26835583 : Blo 1859631 26835583 := bstep (se 1 (by rfl) ⟨20126687, by rfl⟩ : syracuseStep 26835583 = 40253375) B40253375
theorem B2792255 : Blo 1859631 2792255 := bstep (se 1 (by rfl) ⟨2094191, by rfl⟩ : syracuseStep 2792255 = 4188383) B4188383
theorem B67870061 : Blo 1859631 67870061 := bstep (se 3 (by rfl) ⟨12725636, by rfl⟩ : syracuseStep 67870061 = 25451273) B25451273
theorem B3579455 : Blo 1859631 3579455 := bstep (se 1 (by rfl) ⟨2684591, by rfl⟩ : syracuseStep 3579455 = 5369183) B5369183
theorem B4185755 : Blo 1859631 4185755 := bstep (se 1 (by rfl) ⟨3139316, by rfl⟩ : syracuseStep 4185755 = 6278633) B6278633
theorem B21200777 : Blo 1859631 21200777 := bstep (se 2 (by rfl) ⟨7950291, by rfl⟩ : syracuseStep 21200777 = 15900583) B15900583
theorem B14319611 : Blo 1859631 14319611 := bstep (se 1 (by rfl) ⟨10739708, by rfl⟩ : syracuseStep 14319611 = 21479417) B21479417
theorem B8937661 : Blo 1859631 8937661 := bstep (se 3 (by rfl) ⟨1675811, by rfl⟩ : syracuseStep 8937661 = 3351623) B3351623
theorem B2233025009 : Blo 1859631 2233025009 := bstep (se 2 (by rfl) ⟨837384378, by rfl⟩ : syracuseStep 2233025009 = 1674768757) B1674768757
theorem B3138743 : Blo 1859631 3138743 := bstep (se 1 (by rfl) ⟨2354057, by rfl⟩ : syracuseStep 3138743 = 4708115) B4708115
theorem B57287911 : Blo 1859631 57287911 := bstep (se 1 (by rfl) ⟨42965933, by rfl⟩ : syracuseStep 57287911 = 85931867) B85931867
theorem B26822087 : Blo 1859631 26822087 := bstep (se 1 (by rfl) ⟨20116565, by rfl⟩ : syracuseStep 26822087 = 40233131) B40233131
theorem B1861279 : Blo 1859631 1861279 := bstep (se 1 (by rfl) ⟨1395959, by rfl⟩ : syracuseStep 1861279 = 2791919) B2791919
theorem B1861327 : Blo 1859631 1861327 := bstep (se 1 (by rfl) ⟨1395995, by rfl⟩ : syracuseStep 1861327 = 2791991) B2791991
theorem B1861503 : Blo 1859631 1861503 := bstep (se 1 (by rfl) ⟨1396127, by rfl⟩ : syracuseStep 1861503 = 2792255) B2792255
theorem B16549865 : Blo 1859631 16549865 := bstep (se 2 (by rfl) ⟨6206199, by rfl⟩ : syracuseStep 16549865 = 12412399) B12412399
theorem B5736553 : Blo 1859631 5736553 := bstep (se 2 (by rfl) ⟨2151207, by rfl⟩ : syracuseStep 5736553 = 4302415) B4302415
theorem B45246707 : Blo 1859631 45246707 := bstep (se 1 (by rfl) ⟨33935030, by rfl⟩ : syracuseStep 45246707 = 67870061) B67870061
theorem B2386303 : Blo 1859631 2386303 := bstep (se 1 (by rfl) ⟨1789727, by rfl⟩ : syracuseStep 2386303 = 3579455) B3579455
theorem B14133851 : Blo 1859631 14133851 := bstep (se 1 (by rfl) ⟨10600388, by rfl⟩ : syracuseStep 14133851 = 21200777) B21200777
theorem B9546407 : Blo 1859631 9546407 := bstep (se 1 (by rfl) ⟨7159805, by rfl⟩ : syracuseStep 9546407 = 14319611) B14319611
theorem B85977839 : Blo 1859631 85977839 := bstep (se 1 (by rfl) ⟨64483379, by rfl⟩ : syracuseStep 85977839 = 128966759) B128966759
theorem B9416411 : Blo 1859631 9416411 := bstep (se 1 (by rfl) ⟨7062308, by rfl⟩ : syracuseStep 9416411 = 14124617) B14124617
theorem B47698469 : Blo 1859631 47698469 := bstep (se 4 (by rfl) ⟨4471731, by rfl⟩ : syracuseStep 47698469 = 8943463) B8943463
theorem B2790503 : Blo 1859631 2790503 := bstep (se 1 (by rfl) ⟨2092877, by rfl⟩ : syracuseStep 2790503 = 4185755) B4185755
theorem B9418031 : Blo 1859631 9418031 := bstep (se 1 (by rfl) ⟨7063523, by rfl⟩ : syracuseStep 9418031 = 14127047) B14127047
theorem B6280631 : Blo 1859631 6280631 := bstep (se 1 (by rfl) ⟨4710473, by rfl⟩ : syracuseStep 6280631 = 9420947) B9420947
theorem B4773431 : Blo 1859631 4773431 := bstep (se 1 (by rfl) ⟨3580073, by rfl⟩ : syracuseStep 4773431 = 7160147) B7160147
theorem B12089159 : Blo 1859631 12089159 := bstep (se 1 (by rfl) ⟨9066869, by rfl⟩ : syracuseStep 12089159 = 18133739) B18133739
theorem B4184171 : Blo 1859631 4184171 := bstep (se 1 (by rfl) ⟨3138128, by rfl⟩ : syracuseStep 4184171 = 6276257) B6276257
theorem B35780777 : Blo 1859631 35780777 := bstep (se 2 (by rfl) ⟨13417791, by rfl⟩ : syracuseStep 35780777 = 26835583) B26835583
theorem B25450787 : Blo 1859631 25450787 := bstep (se 1 (by rfl) ⟨19088090, by rfl⟩ : syracuseStep 25450787 = 38176181) B38176181
theorem B5962207 : Blo 1859631 5962207 := bstep (se 1 (by rfl) ⟨4471655, by rfl⟩ : syracuseStep 5962207 = 8943311) B8943311
theorem B23837753 : Blo 1859631 23837753 := bstep (se 2 (by rfl) ⟨8939157, by rfl⟩ : syracuseStep 23837753 = 17878315) B17878315
theorem B7061033 : Blo 1859631 7061033 := bstep (se 2 (by rfl) ⟨2647887, by rfl⟩ : syracuseStep 7061033 = 5295775) B5295775
theorem B1488683339 : Blo 1859631 1488683339 := bstep (se 1 (by rfl) ⟨1116512504, by rfl⟩ : syracuseStep 1488683339 = 2233025009) B2233025009
theorem B1860335 : Blo 1859631 1860335 := bstep (se 1 (by rfl) ⟨1395251, by rfl⟩ : syracuseStep 1860335 = 2790503) B2790503
theorem B4187087 : Blo 1859631 4187087 := bstep (se 1 (by rfl) ⟨3140315, by rfl⟩ : syracuseStep 4187087 = 6280631) B6280631
theorem B30164471 : Blo 1859631 30164471 := bstep (se 1 (by rfl) ⟨22623353, by rfl⟩ : syracuseStep 30164471 = 45246707) B45246707
theorem B16967191 : Blo 1859631 16967191 := bstep (se 1 (by rfl) ⟨12725393, by rfl⟩ : syracuseStep 16967191 = 25450787) B25450787
theorem B76383881 : Blo 1859631 76383881 := bstep (se 2 (by rfl) ⟨28643955, by rfl⟩ : syracuseStep 76383881 = 57287911) B57287911
theorem B9422567 : Blo 1859631 9422567 := bstep (se 1 (by rfl) ⟨7066925, by rfl⟩ : syracuseStep 9422567 = 14133851) B14133851
theorem B6277607 : Blo 1859631 6277607 := bstep (se 1 (by rfl) ⟨4708205, by rfl⟩ : syracuseStep 6277607 = 9416411) B9416411
theorem B7949609 : Blo 1859631 7949609 := bstep (se 2 (by rfl) ⟨2981103, by rfl⟩ : syracuseStep 7949609 = 5962207) B5962207
theorem B2092495 : Blo 1859631 2092495 := bstep (se 1 (by rfl) ⟨1569371, by rfl⟩ : syracuseStep 2092495 = 3138743) B3138743
theorem B6278687 : Blo 1859631 6278687 := bstep (se 1 (by rfl) ⟨4709015, by rfl⟩ : syracuseStep 6278687 = 9418031) B9418031
theorem B3182287 : Blo 1859631 3182287 := bstep (se 1 (by rfl) ⟨2386715, by rfl⟩ : syracuseStep 3182287 = 4773431) B4773431
theorem B2789447 : Blo 1859631 2789447 := bstep (se 1 (by rfl) ⟨2092085, by rfl⟩ : syracuseStep 2789447 = 4184171) B4184171
theorem B12726949 : Blo 1859631 12726949 := bstep (se 4 (by rfl) ⟨1193151, by rfl⟩ : syracuseStep 12726949 = 2386303) B2386303
theorem B4707355 : Blo 1859631 4707355 := bstep (se 1 (by rfl) ⟨3530516, by rfl⟩ : syracuseStep 4707355 = 7061033) B7061033
theorem B11916881 : Blo 1859631 11916881 := bstep (se 2 (by rfl) ⟨4468830, by rfl⟩ : syracuseStep 11916881 = 8937661) B8937661
theorem B31798979 : Blo 1859631 31798979 := bstep (se 1 (by rfl) ⟨23849234, by rfl⟩ : syracuseStep 31798979 = 47698469) B47698469
theorem B17881391 : Blo 1859631 17881391 := bstep (se 1 (by rfl) ⟨13411043, by rfl⟩ : syracuseStep 17881391 = 26822087) B26822087
theorem B8059439 : Blo 1859631 8059439 := bstep (se 1 (by rfl) ⟨6044579, by rfl⟩ : syracuseStep 8059439 = 12089159) B12089159
theorem B11033243 : Blo 1859631 11033243 := bstep (se 1 (by rfl) ⟨8274932, by rfl⟩ : syracuseStep 11033243 = 16549865) B16549865
theorem B23853851 : Blo 1859631 23853851 := bstep (se 1 (by rfl) ⟨17890388, by rfl⟩ : syracuseStep 23853851 = 35780777) B35780777
theorem B6364271 : Blo 1859631 6364271 := bstep (se 1 (by rfl) ⟨4773203, by rfl⟩ : syracuseStep 6364271 = 9546407) B9546407
theorem B57318559 : Blo 1859631 57318559 := bstep (se 1 (by rfl) ⟨42988919, by rfl⟩ : syracuseStep 57318559 = 85977839) B85977839
theorem B15891835 : Blo 1859631 15891835 := bstep (se 1 (by rfl) ⟨11918876, by rfl⟩ : syracuseStep 15891835 = 23837753) B23837753
theorem B122379797 : Blo 1859631 122379797 := bstep (se 6 (by rfl) ⟨2868276, by rfl⟩ : syracuseStep 122379797 = 5736553) B5736553
theorem B1859631 : Blo 1859631 1859631 := bstep (se 1 (by rfl) ⟨1394723, by rfl⟩ : syracuseStep 1859631 = 2789447) B2789447
theorem B50922587 : Blo 1859631 50922587 := bstep (se 1 (by rfl) ⟨38191940, by rfl⟩ : syracuseStep 50922587 = 76383881) B76383881
theorem B6276473 : Blo 1859631 6276473 := bstep (se 2 (by rfl) ⟨2353677, by rfl⟩ : syracuseStep 6276473 = 4707355) B4707355
theorem B11920927 : Blo 1859631 11920927 := bstep (se 1 (by rfl) ⟨8940695, by rfl⟩ : syracuseStep 11920927 = 17881391) B17881391
theorem B15902567 : Blo 1859631 15902567 := bstep (se 1 (by rfl) ⟨11926925, by rfl⟩ : syracuseStep 15902567 = 23853851) B23853851
theorem B81586531 : Blo 1859631 81586531 := bstep (se 1 (by rfl) ⟨61189898, by rfl⟩ : syracuseStep 81586531 = 122379797) B122379797
theorem B992455559 : Blo 1859631 992455559 := bstep (se 1 (by rfl) ⟨744341669, by rfl⟩ : syracuseStep 992455559 = 1488683339) B1488683339
theorem B16969265 : Blo 1859631 16969265 := bstep (se 2 (by rfl) ⟨6363474, by rfl⟩ : syracuseStep 16969265 = 12726949) B12726949
theorem B21189113 : Blo 1859631 21189113 := bstep (se 2 (by rfl) ⟨7945917, by rfl⟩ : syracuseStep 21189113 = 15891835) B15891835
theorem B2789993 : Blo 1859631 2789993 := bstep (se 2 (by rfl) ⟨1046247, by rfl⟩ : syracuseStep 2789993 = 2092495) B2092495
theorem B22622921 : Blo 1859631 22622921 := bstep (se 2 (by rfl) ⟨8483595, by rfl⟩ : syracuseStep 22622921 = 16967191) B16967191
theorem B2791391 : Blo 1859631 2791391 := bstep (se 1 (by rfl) ⟨2093543, by rfl⟩ : syracuseStep 2791391 = 4187087) B4187087
theorem B305698981 : Blo 1859631 305698981 := bstep (se 4 (by rfl) ⟨28659279, by rfl⟩ : syracuseStep 305698981 = 57318559) B57318559
theorem B20109647 : Blo 1859631 20109647 := bstep (se 1 (by rfl) ⟨15082235, by rfl⟩ : syracuseStep 20109647 = 30164471) B30164471
theorem B7944587 : Blo 1859631 7944587 := bstep (se 1 (by rfl) ⟨5958440, by rfl⟩ : syracuseStep 7944587 = 11916881) B11916881
theorem B21199319 : Blo 1859631 21199319 := bstep (se 1 (by rfl) ⟨15899489, by rfl⟩ : syracuseStep 21199319 = 31798979) B31798979
theorem B6281711 : Blo 1859631 6281711 := bstep (se 1 (by rfl) ⟨4711283, by rfl⟩ : syracuseStep 6281711 = 9422567) B9422567
theorem B4185071 : Blo 1859631 4185071 := bstep (se 1 (by rfl) ⟨3138803, by rfl⟩ : syracuseStep 4185071 = 6277607) B6277607
theorem B5372959 : Blo 1859631 5372959 := bstep (se 1 (by rfl) ⟨4029719, by rfl⟩ : syracuseStep 5372959 = 8059439) B8059439
theorem B7355495 : Blo 1859631 7355495 := bstep (se 1 (by rfl) ⟨5516621, by rfl⟩ : syracuseStep 7355495 = 11033243) B11033243
theorem B4242847 : Blo 1859631 4242847 := bstep (se 1 (by rfl) ⟨3182135, by rfl⟩ : syracuseStep 4242847 = 6364271) B6364271
theorem B5299739 : Blo 1859631 5299739 := bstep (se 1 (by rfl) ⟨3974804, by rfl⟩ : syracuseStep 5299739 = 7949609) B7949609
theorem B4243049 : Blo 1859631 4243049 := bstep (se 2 (by rfl) ⟨1591143, by rfl⟩ : syracuseStep 4243049 = 3182287) B3182287
theorem B4185791 : Blo 1859631 4185791 := bstep (se 1 (by rfl) ⟨3139343, by rfl⟩ : syracuseStep 4185791 = 6278687) B6278687
theorem B1859995 : Blo 1859631 1859995 := bstep (se 1 (by rfl) ⟨1394996, by rfl⟩ : syracuseStep 1859995 = 2789993) B2789993
theorem B15081947 : Blo 1859631 15081947 := bstep (se 1 (by rfl) ⟨11311460, by rfl⟩ : syracuseStep 15081947 = 22622921) B22622921
theorem B108782041 : Blo 1859631 108782041 := bstep (se 2 (by rfl) ⟨40793265, by rfl⟩ : syracuseStep 108782041 = 81586531) B81586531
theorem B33948391 : Blo 1859631 33948391 := bstep (se 1 (by rfl) ⟨25461293, by rfl⟩ : syracuseStep 33948391 = 50922587) B50922587
theorem B10601711 : Blo 1859631 10601711 := bstep (se 1 (by rfl) ⟨7951283, by rfl⟩ : syracuseStep 10601711 = 15902567) B15902567
theorem B1860927 : Blo 1859631 1860927 := bstep (se 1 (by rfl) ⟨1395695, by rfl⟩ : syracuseStep 1860927 = 2791391) B2791391
theorem B14132879 : Blo 1859631 14132879 := bstep (se 1 (by rfl) ⟨10599659, by rfl⟩ : syracuseStep 14132879 = 21199319) B21199319
theorem B4187807 : Blo 1859631 4187807 := bstep (se 1 (by rfl) ⟨3140855, by rfl⟩ : syracuseStep 4187807 = 6281711) B6281711
theorem B661637039 : Blo 1859631 661637039 := bstep (se 1 (by rfl) ⟨496227779, by rfl⟩ : syracuseStep 661637039 = 992455559) B992455559
theorem B15894569 : Blo 1859631 15894569 := bstep (se 2 (by rfl) ⟨5960463, by rfl⟩ : syracuseStep 15894569 = 11920927) B11920927
theorem B3533159 : Blo 1859631 3533159 := bstep (se 1 (by rfl) ⟨2649869, by rfl⟩ : syracuseStep 3533159 = 5299739) B5299739
theorem B2828699 : Blo 1859631 2828699 := bstep (se 1 (by rfl) ⟨2121524, by rfl⟩ : syracuseStep 2828699 = 4243049) B4243049
theorem B19614653 : Blo 1859631 19614653 := bstep (se 3 (by rfl) ⟨3677747, by rfl⟩ : syracuseStep 19614653 = 7355495) B7355495
theorem B14126075 : Blo 1859631 14126075 := bstep (se 1 (by rfl) ⟨10594556, by rfl⟩ : syracuseStep 14126075 = 21189113) B21189113
theorem B7163945 : Blo 1859631 7163945 := bstep (se 2 (by rfl) ⟨2686479, by rfl⟩ : syracuseStep 7163945 = 5372959) B5372959
theorem B13406431 : Blo 1859631 13406431 := bstep (se 1 (by rfl) ⟨10054823, by rfl⟩ : syracuseStep 13406431 = 20109647) B20109647
theorem B5296391 : Blo 1859631 5296391 := bstep (se 1 (by rfl) ⟨3972293, by rfl⟩ : syracuseStep 5296391 = 7944587) B7944587
theorem B5657129 : Blo 1859631 5657129 := bstep (se 2 (by rfl) ⟨2121423, by rfl⟩ : syracuseStep 5657129 = 4242847) B4242847
theorem B2790047 : Blo 1859631 2790047 := bstep (se 1 (by rfl) ⟨2092535, by rfl⟩ : syracuseStep 2790047 = 4185071) B4185071
theorem B2790527 : Blo 1859631 2790527 := bstep (se 1 (by rfl) ⟨2092895, by rfl⟩ : syracuseStep 2790527 = 4185791) B4185791
theorem B407598641 : Blo 1859631 407598641 := bstep (se 2 (by rfl) ⟨152849490, by rfl⟩ : syracuseStep 407598641 = 305698981) B305698981
theorem B4184315 : Blo 1859631 4184315 := bstep (se 1 (by rfl) ⟨3138236, by rfl⟩ : syracuseStep 4184315 = 6276473) B6276473
theorem B11312843 : Blo 1859631 11312843 := bstep (se 1 (by rfl) ⟨8484632, by rfl⟩ : syracuseStep 11312843 = 16969265) B16969265
theorem B4775963 : Blo 1859631 4775963 := bstep (se 1 (by rfl) ⟨3581972, by rfl⟩ : syracuseStep 4775963 = 7163945) B7163945
theorem B3530927 : Blo 1859631 3530927 := bstep (se 1 (by rfl) ⟨2648195, by rfl⟩ : syracuseStep 3530927 = 5296391) B5296391
theorem B17875241 : Blo 1859631 17875241 := bstep (se 2 (by rfl) ⟨6703215, by rfl⟩ : syracuseStep 17875241 = 13406431) B13406431
theorem B1860031 : Blo 1859631 1860031 := bstep (se 1 (by rfl) ⟨1395023, by rfl⟩ : syracuseStep 1860031 = 2790047) B2790047
theorem B1860351 : Blo 1859631 1860351 := bstep (se 1 (by rfl) ⟨1395263, by rfl⟩ : syracuseStep 1860351 = 2790527) B2790527
theorem B9421757 : Blo 1859631 9421757 := bstep (se 3 (by rfl) ⟨1766579, by rfl⟩ : syracuseStep 9421757 = 3533159) B3533159
theorem B9421919 : Blo 1859631 9421919 := bstep (se 1 (by rfl) ⟨7066439, by rfl⟩ : syracuseStep 9421919 = 14132879) B14132879
theorem B1885799 : Blo 1859631 1885799 := bstep (se 1 (by rfl) ⟨1414349, by rfl⟩ : syracuseStep 1885799 = 2828699) B2828699
theorem B13076435 : Blo 1859631 13076435 := bstep (se 1 (by rfl) ⟨9807326, by rfl⟩ : syracuseStep 13076435 = 19614653) B19614653
theorem B10054631 : Blo 1859631 10054631 := bstep (se 1 (by rfl) ⟨7540973, by rfl⟩ : syracuseStep 10054631 = 15081947) B15081947
theorem B3771419 : Blo 1859631 3771419 := bstep (se 1 (by rfl) ⟨2828564, by rfl⟩ : syracuseStep 3771419 = 5657129) B5657129
theorem B145042721 : Blo 1859631 145042721 := bstep (se 2 (by rfl) ⟨54391020, by rfl⟩ : syracuseStep 145042721 = 108782041) B108782041
theorem B45264521 : Blo 1859631 45264521 := bstep (se 2 (by rfl) ⟨16974195, by rfl⟩ : syracuseStep 45264521 = 33948391) B33948391
theorem B271732427 : Blo 1859631 271732427 := bstep (se 1 (by rfl) ⟨203799320, by rfl⟩ : syracuseStep 271732427 = 407598641) B407598641
theorem B10596379 : Blo 1859631 10596379 := bstep (se 1 (by rfl) ⟨7947284, by rfl⟩ : syracuseStep 10596379 = 15894569) B15894569
theorem B2789543 : Blo 1859631 2789543 := bstep (se 1 (by rfl) ⟨2092157, by rfl⟩ : syracuseStep 2789543 = 4184315) B4184315
theorem B30167581 : Blo 1859631 30167581 := bstep (se 3 (by rfl) ⟨5656421, by rfl⟩ : syracuseStep 30167581 = 11312843) B11312843
theorem B9417383 : Blo 1859631 9417383 := bstep (se 1 (by rfl) ⟨7063037, by rfl⟩ : syracuseStep 9417383 = 14126075) B14126075
theorem B1764365437 : Blo 1859631 1764365437 := bstep (se 3 (by rfl) ⟨330818519, by rfl⟩ : syracuseStep 1764365437 = 661637039) B661637039
theorem B7067807 : Blo 1859631 7067807 := bstep (se 1 (by rfl) ⟨5300855, by rfl⟩ : syracuseStep 7067807 = 10601711) B10601711
theorem B2791871 : Blo 1859631 2791871 := bstep (se 1 (by rfl) ⟨2093903, by rfl⟩ : syracuseStep 2791871 = 4187807) B4187807
theorem B1859695 : Blo 1859631 1859695 := bstep (se 1 (by rfl) ⟨1394771, by rfl⟩ : syracuseStep 1859695 = 2789543) B2789543
theorem B40223441 : Blo 1859631 40223441 := bstep (se 2 (by rfl) ⟨15083790, by rfl⟩ : syracuseStep 40223441 = 30167581) B30167581
theorem B4711871 : Blo 1859631 4711871 := bstep (se 1 (by rfl) ⟨3533903, by rfl⟩ : syracuseStep 4711871 = 7067807) B7067807
theorem B1861247 : Blo 1859631 1861247 := bstep (se 1 (by rfl) ⟨1395935, by rfl⟩ : syracuseStep 1861247 = 2791871) B2791871
theorem B6703087 : Blo 1859631 6703087 := bstep (se 1 (by rfl) ⟨5027315, by rfl⟩ : syracuseStep 6703087 = 10054631) B10054631
theorem B2353951 : Blo 1859631 2353951 := bstep (se 1 (by rfl) ⟨1765463, by rfl⟩ : syracuseStep 2353951 = 3530927) B3530927
theorem B6278255 : Blo 1859631 6278255 := bstep (se 1 (by rfl) ⟨4708691, by rfl⟩ : syracuseStep 6278255 = 9417383) B9417383
theorem B96695147 : Blo 1859631 96695147 := bstep (se 1 (by rfl) ⟨72521360, by rfl⟩ : syracuseStep 96695147 = 145042721) B145042721
theorem B30176347 : Blo 1859631 30176347 := bstep (se 1 (by rfl) ⟨22632260, by rfl⟩ : syracuseStep 30176347 = 45264521) B45264521
theorem B181154951 : Blo 1859631 181154951 := bstep (se 1 (by rfl) ⟨135866213, by rfl⟩ : syracuseStep 181154951 = 271732427) B271732427
theorem B34870493 : Blo 1859631 34870493 := bstep (se 3 (by rfl) ⟨6538217, by rfl⟩ : syracuseStep 34870493 = 13076435) B13076435
theorem B14128505 : Blo 1859631 14128505 := bstep (se 2 (by rfl) ⟨5298189, by rfl⟩ : syracuseStep 14128505 = 10596379) B10596379
theorem B10057117 : Blo 1859631 10057117 := bstep (se 3 (by rfl) ⟨1885709, by rfl⟩ : syracuseStep 10057117 = 3771419) B3771419
theorem B12735901 : Blo 1859631 12735901 := bstep (se 3 (by rfl) ⟨2387981, by rfl⟩ : syracuseStep 12735901 = 4775963) B4775963
theorem B11916827 : Blo 1859631 11916827 := bstep (se 1 (by rfl) ⟨8937620, by rfl⟩ : syracuseStep 11916827 = 17875241) B17875241
theorem B6281171 : Blo 1859631 6281171 := bstep (se 1 (by rfl) ⟨4710878, by rfl⟩ : syracuseStep 6281171 = 9421757) B9421757
theorem B6281279 : Blo 1859631 6281279 := bstep (se 1 (by rfl) ⟨4710959, by rfl⟩ : syracuseStep 6281279 = 9421919) B9421919
theorem B2352487249 : Blo 1859631 2352487249 := bstep (se 2 (by rfl) ⟨882182718, by rfl⟩ : syracuseStep 2352487249 = 1764365437) B1764365437
theorem B5028797 : Blo 1859631 5028797 := bstep (se 3 (by rfl) ⟨942899, by rfl⟩ : syracuseStep 5028797 = 1885799) B1885799
theorem B3138601 : Blo 1859631 3138601 := bstep (se 2 (by rfl) ⟨1176975, by rfl⟩ : syracuseStep 3138601 = 2353951) B2353951
theorem B4187447 : Blo 1859631 4187447 := bstep (se 1 (by rfl) ⟨3140585, by rfl⟩ : syracuseStep 4187447 = 6281171) B6281171
theorem B4187519 : Blo 1859631 4187519 := bstep (se 1 (by rfl) ⟨3140639, by rfl⟩ : syracuseStep 4187519 = 6281279) B6281279
theorem B3352531 : Blo 1859631 3352531 := bstep (se 1 (by rfl) ⟨2514398, by rfl⟩ : syracuseStep 3352531 = 5028797) B5028797
theorem B257853725 : Blo 1859631 257853725 := bstep (se 3 (by rfl) ⟨48347573, by rfl⟩ : syracuseStep 257853725 = 96695147) B96695147
theorem B26815627 : Blo 1859631 26815627 := bstep (se 1 (by rfl) ⟨20111720, by rfl⟩ : syracuseStep 26815627 = 40223441) B40223441
theorem B120769967 : Blo 1859631 120769967 := bstep (se 1 (by rfl) ⟨90577475, by rfl⟩ : syracuseStep 120769967 = 181154951) B181154951
theorem B3141247 : Blo 1859631 3141247 := bstep (se 1 (by rfl) ⟨2355935, by rfl⟩ : syracuseStep 3141247 = 4711871) B4711871
theorem B40235129 : Blo 1859631 40235129 := bstep (se 2 (by rfl) ⟨15088173, by rfl⟩ : syracuseStep 40235129 = 30176347) B30176347
theorem B23246995 : Blo 1859631 23246995 := bstep (se 1 (by rfl) ⟨17435246, by rfl⟩ : syracuseStep 23246995 = 34870493) B34870493
theorem B9419003 : Blo 1859631 9419003 := bstep (se 1 (by rfl) ⟨7064252, by rfl⟩ : syracuseStep 9419003 = 14128505) B14128505
theorem B7944551 : Blo 1859631 7944551 := bstep (se 1 (by rfl) ⟨5958413, by rfl⟩ : syracuseStep 7944551 = 11916827) B11916827
theorem B3136649665 : Blo 1859631 3136649665 := bstep (se 2 (by rfl) ⟨1176243624, by rfl⟩ : syracuseStep 3136649665 = 2352487249) B2352487249
theorem B13409489 : Blo 1859631 13409489 := bstep (se 2 (by rfl) ⟨5028558, by rfl⟩ : syracuseStep 13409489 = 10057117) B10057117
theorem B16981201 : Blo 1859631 16981201 := bstep (se 2 (by rfl) ⟨6367950, by rfl⟩ : syracuseStep 16981201 = 12735901) B12735901
theorem B4185503 : Blo 1859631 4185503 := bstep (se 1 (by rfl) ⟨3139127, by rfl⟩ : syracuseStep 4185503 = 6278255) B6278255
theorem B8937449 : Blo 1859631 8937449 := bstep (se 2 (by rfl) ⟨3351543, by rfl⟩ : syracuseStep 8937449 = 6703087) B6703087
theorem B171902483 : Blo 1859631 171902483 := bstep (se 1 (by rfl) ⟨128926862, by rfl⟩ : syracuseStep 171902483 = 257853725) B257853725
theorem B8939659 : Blo 1859631 8939659 := bstep (se 1 (by rfl) ⟨6704744, by rfl⟩ : syracuseStep 8939659 = 13409489) B13409489
theorem B4188329 : Blo 1859631 4188329 := bstep (se 2 (by rfl) ⟨1570623, by rfl⟩ : syracuseStep 4188329 = 3141247) B3141247
theorem B80513311 : Blo 1859631 80513311 := bstep (se 1 (by rfl) ⟨60384983, by rfl⟩ : syracuseStep 80513311 = 120769967) B120769967
theorem B5958299 : Blo 1859631 5958299 := bstep (se 1 (by rfl) ⟨4468724, by rfl⟩ : syracuseStep 5958299 = 8937449) B8937449
theorem B26823419 : Blo 1859631 26823419 := bstep (se 1 (by rfl) ⟨20117564, by rfl⟩ : syracuseStep 26823419 = 40235129) B40235129
theorem B4182199553 : Blo 1859631 4182199553 := bstep (se 2 (by rfl) ⟨1568324832, by rfl⟩ : syracuseStep 4182199553 = 3136649665) B3136649665
theorem B6279335 : Blo 1859631 6279335 := bstep (se 1 (by rfl) ⟨4709501, by rfl⟩ : syracuseStep 6279335 = 9419003) B9419003
theorem B35754169 : Blo 1859631 35754169 := bstep (se 2 (by rfl) ⟨13407813, by rfl⟩ : syracuseStep 35754169 = 26815627) B26815627
theorem B5296367 : Blo 1859631 5296367 := bstep (se 1 (by rfl) ⟨3972275, by rfl⟩ : syracuseStep 5296367 = 7944551) B7944551
theorem B2790335 : Blo 1859631 2790335 := bstep (se 1 (by rfl) ⟨2092751, by rfl⟩ : syracuseStep 2790335 = 4185503) B4185503
theorem B4470041 : Blo 1859631 4470041 := bstep (se 2 (by rfl) ⟨1676265, by rfl⟩ : syracuseStep 4470041 = 3352531) B3352531
theorem B30995993 : Blo 1859631 30995993 := bstep (se 2 (by rfl) ⟨11623497, by rfl⟩ : syracuseStep 30995993 = 23246995) B23246995
theorem B2791631 : Blo 1859631 2791631 := bstep (se 1 (by rfl) ⟨2093723, by rfl⟩ : syracuseStep 2791631 = 4187447) B4187447
theorem B2791679 : Blo 1859631 2791679 := bstep (se 1 (by rfl) ⟨2093759, by rfl⟩ : syracuseStep 2791679 = 4187519) B4187519
theorem B4184801 : Blo 1859631 4184801 := bstep (se 2 (by rfl) ⟨1569300, by rfl⟩ : syracuseStep 4184801 = 3138601) B3138601
theorem B22641601 : Blo 1859631 22641601 := bstep (se 2 (by rfl) ⟨8490600, by rfl⟩ : syracuseStep 22641601 = 16981201) B16981201
theorem B4186223 : Blo 1859631 4186223 := bstep (se 1 (by rfl) ⟨3139667, by rfl⟩ : syracuseStep 4186223 = 6279335) B6279335
theorem B11919545 : Blo 1859631 11919545 := bstep (se 2 (by rfl) ⟨4469829, by rfl⟩ : syracuseStep 11919545 = 8939659) B8939659
theorem B14123645 : Blo 1859631 14123645 := bstep (se 3 (by rfl) ⟨2648183, by rfl⟩ : syracuseStep 14123645 = 5296367) B5296367
theorem B1860223 : Blo 1859631 1860223 := bstep (se 1 (by rfl) ⟨1395167, by rfl⟩ : syracuseStep 1860223 = 2790335) B2790335
theorem B30188801 : Blo 1859631 30188801 := bstep (se 2 (by rfl) ⟨11320800, by rfl⟩ : syracuseStep 30188801 = 22641601) B22641601
theorem B1861087 : Blo 1859631 1861087 := bstep (se 1 (by rfl) ⟨1395815, by rfl⟩ : syracuseStep 1861087 = 2791631) B2791631
theorem B1861119 : Blo 1859631 1861119 := bstep (se 1 (by rfl) ⟨1395839, by rfl⟩ : syracuseStep 1861119 = 2791679) B2791679
theorem B2788133035 : Blo 1859631 2788133035 := bstep (se 1 (by rfl) ⟨2091099776, by rfl⟩ : syracuseStep 2788133035 = 4182199553) B4182199553
theorem B47672225 : Blo 1859631 47672225 := bstep (se 2 (by rfl) ⟨17877084, by rfl⟩ : syracuseStep 47672225 = 35754169) B35754169
theorem B107351081 : Blo 1859631 107351081 := bstep (se 2 (by rfl) ⟨40256655, by rfl⟩ : syracuseStep 107351081 = 80513311) B80513311
theorem B114601655 : Blo 1859631 114601655 := bstep (se 1 (by rfl) ⟨85951241, by rfl⟩ : syracuseStep 114601655 = 171902483) B171902483
theorem B20663995 : Blo 1859631 20663995 := bstep (se 1 (by rfl) ⟨15497996, by rfl⟩ : syracuseStep 20663995 = 30995993) B30995993
theorem B15888797 : Blo 1859631 15888797 := bstep (se 3 (by rfl) ⟨2979149, by rfl⟩ : syracuseStep 15888797 = 5958299) B5958299
theorem B2789867 : Blo 1859631 2789867 := bstep (se 1 (by rfl) ⟨2092400, by rfl⟩ : syracuseStep 2789867 = 4184801) B4184801
theorem B2980027 : Blo 1859631 2980027 := bstep (se 1 (by rfl) ⟨2235020, by rfl⟩ : syracuseStep 2980027 = 4470041) B4470041
theorem B2792219 : Blo 1859631 2792219 := bstep (se 1 (by rfl) ⟨2094164, by rfl⟩ : syracuseStep 2792219 = 4188329) B4188329
theorem B17882279 : Blo 1859631 17882279 := bstep (se 1 (by rfl) ⟨13411709, by rfl⟩ : syracuseStep 17882279 = 26823419) B26823419
theorem B7946363 : Blo 1859631 7946363 := bstep (se 1 (by rfl) ⟨5959772, by rfl⟩ : syracuseStep 7946363 = 11919545) B11919545
theorem B3973369 : Blo 1859631 3973369 := bstep (se 2 (by rfl) ⟨1490013, by rfl⟩ : syracuseStep 3973369 = 2980027) B2980027
theorem B10592531 : Blo 1859631 10592531 := bstep (se 1 (by rfl) ⟨7944398, by rfl⟩ : syracuseStep 10592531 = 15888797) B15888797
theorem B1859911 : Blo 1859631 1859911 := bstep (se 1 (by rfl) ⟨1394933, by rfl⟩ : syracuseStep 1859911 = 2789867) B2789867
theorem B80503469 : Blo 1859631 80503469 := bstep (se 3 (by rfl) ⟨15094400, by rfl⟩ : syracuseStep 80503469 = 30188801) B30188801
theorem B1861479 : Blo 1859631 1861479 := bstep (se 1 (by rfl) ⟨1396109, by rfl⟩ : syracuseStep 1861479 = 2792219) B2792219
theorem B71567387 : Blo 1859631 71567387 := bstep (se 1 (by rfl) ⟨53675540, by rfl⟩ : syracuseStep 71567387 = 107351081) B107351081
theorem B11921519 : Blo 1859631 11921519 := bstep (se 1 (by rfl) ⟨8941139, by rfl⟩ : syracuseStep 11921519 = 17882279) B17882279
theorem B27551993 : Blo 1859631 27551993 := bstep (se 2 (by rfl) ⟨10331997, by rfl⟩ : syracuseStep 27551993 = 20663995) B20663995
theorem B76401103 : Blo 1859631 76401103 := bstep (se 1 (by rfl) ⟨57300827, by rfl⟩ : syracuseStep 76401103 = 114601655) B114601655
theorem B9415763 : Blo 1859631 9415763 := bstep (se 1 (by rfl) ⟨7061822, by rfl⟩ : syracuseStep 9415763 = 14123645) B14123645
theorem B31781483 : Blo 1859631 31781483 := bstep (se 1 (by rfl) ⟨23836112, by rfl⟩ : syracuseStep 31781483 = 47672225) B47672225
theorem B2790815 : Blo 1859631 2790815 := bstep (se 1 (by rfl) ⟨2093111, by rfl⟩ : syracuseStep 2790815 = 4186223) B4186223
theorem B3717510713 : Blo 1859631 3717510713 := bstep (se 2 (by rfl) ⟨1394066517, by rfl⟩ : syracuseStep 3717510713 = 2788133035) B2788133035
theorem B7061687 : Blo 1859631 7061687 := bstep (se 1 (by rfl) ⟨5296265, by rfl⟩ : syracuseStep 7061687 = 10592531) B10592531
theorem B101868137 : Blo 1859631 101868137 := bstep (se 2 (by rfl) ⟨38200551, by rfl⟩ : syracuseStep 101868137 = 76401103) B76401103
theorem B1860543 : Blo 1859631 1860543 := bstep (se 1 (by rfl) ⟨1395407, by rfl⟩ : syracuseStep 1860543 = 2790815) B2790815
theorem B47711591 : Blo 1859631 47711591 := bstep (se 1 (by rfl) ⟨35783693, by rfl⟩ : syracuseStep 47711591 = 71567387) B71567387
theorem B7947679 : Blo 1859631 7947679 := bstep (se 1 (by rfl) ⟨5960759, by rfl⟩ : syracuseStep 7947679 = 11921519) B11921519
theorem B6277175 : Blo 1859631 6277175 := bstep (se 1 (by rfl) ⟨4707881, by rfl⟩ : syracuseStep 6277175 = 9415763) B9415763
theorem B21187655 : Blo 1859631 21187655 := bstep (se 1 (by rfl) ⟨15890741, by rfl⟩ : syracuseStep 21187655 = 31781483) B31781483
theorem B53668979 : Blo 1859631 53668979 := bstep (se 1 (by rfl) ⟨40251734, by rfl⟩ : syracuseStep 53668979 = 80503469) B80503469
theorem B5297575 : Blo 1859631 5297575 := bstep (se 1 (by rfl) ⟨3973181, by rfl⟩ : syracuseStep 5297575 = 7946363) B7946363
theorem B5297825 : Blo 1859631 5297825 := bstep (se 2 (by rfl) ⟨1986684, by rfl⟩ : syracuseStep 5297825 = 3973369) B3973369
theorem B73471981 : Blo 1859631 73471981 := bstep (se 3 (by rfl) ⟨13775996, by rfl⟩ : syracuseStep 73471981 = 27551993) B27551993
theorem B2478340475 : Blo 1859631 2478340475 := bstep (se 1 (by rfl) ⟨1858755356, by rfl⟩ : syracuseStep 2478340475 = 3717510713) B3717510713
theorem B67912091 : Blo 1859631 67912091 := bstep (se 1 (by rfl) ⟨50934068, by rfl⟩ : syracuseStep 67912091 = 101868137) B101868137
theorem B7063433 : Blo 1859631 7063433 := bstep (se 2 (by rfl) ⟨2648787, by rfl⟩ : syracuseStep 7063433 = 5297575) B5297575
theorem B14125103 : Blo 1859631 14125103 := bstep (se 1 (by rfl) ⟨10593827, by rfl⟩ : syracuseStep 14125103 = 21187655) B21187655
theorem B97962641 : Blo 1859631 97962641 := bstep (se 2 (by rfl) ⟨36735990, by rfl⟩ : syracuseStep 97962641 = 73471981) B73471981
theorem B14127533 : Blo 1859631 14127533 := bstep (se 3 (by rfl) ⟨2648912, by rfl⟩ : syracuseStep 14127533 = 5297825) B5297825
theorem B10596905 : Blo 1859631 10596905 := bstep (se 2 (by rfl) ⟨3973839, by rfl⟩ : syracuseStep 10596905 = 7947679) B7947679
theorem B35779319 : Blo 1859631 35779319 := bstep (se 1 (by rfl) ⟨26834489, by rfl⟩ : syracuseStep 35779319 = 53668979) B53668979
theorem B4707791 : Blo 1859631 4707791 := bstep (se 1 (by rfl) ⟨3530843, by rfl⟩ : syracuseStep 4707791 = 7061687) B7061687
theorem B31807727 : Blo 1859631 31807727 := bstep (se 1 (by rfl) ⟨23855795, by rfl⟩ : syracuseStep 31807727 = 47711591) B47711591
theorem B4184783 : Blo 1859631 4184783 := bstep (se 1 (by rfl) ⟨3138587, by rfl⟩ : syracuseStep 4184783 = 6277175) B6277175
theorem B1652226983 : Blo 1859631 1652226983 := bstep (se 1 (by rfl) ⟨1239170237, by rfl⟩ : syracuseStep 1652226983 = 2478340475) B2478340475
theorem B3138527 : Blo 1859631 3138527 := bstep (se 1 (by rfl) ⟨2353895, by rfl⟩ : syracuseStep 3138527 = 4707791) B4707791
theorem B65308427 : Blo 1859631 65308427 := bstep (se 1 (by rfl) ⟨48981320, by rfl⟩ : syracuseStep 65308427 = 97962641) B97962641
theorem B7064603 : Blo 1859631 7064603 := bstep (se 1 (by rfl) ⟨5298452, by rfl⟩ : syracuseStep 7064603 = 10596905) B10596905
theorem B9416735 : Blo 1859631 9416735 := bstep (se 1 (by rfl) ⟨7062551, by rfl⟩ : syracuseStep 9416735 = 14125103) B14125103
theorem B21205151 : Blo 1859631 21205151 := bstep (se 1 (by rfl) ⟨15903863, by rfl⟩ : syracuseStep 21205151 = 31807727) B31807727
theorem B2789855 : Blo 1859631 2789855 := bstep (se 1 (by rfl) ⟨2092391, by rfl⟩ : syracuseStep 2789855 = 4184783) B4184783
theorem B1101484655 : Blo 1859631 1101484655 := bstep (se 1 (by rfl) ⟨826113491, by rfl⟩ : syracuseStep 1101484655 = 1652226983) B1652226983
theorem B45274727 : Blo 1859631 45274727 := bstep (se 1 (by rfl) ⟨33956045, by rfl⟩ : syracuseStep 45274727 = 67912091) B67912091
theorem B9418355 : Blo 1859631 9418355 := bstep (se 1 (by rfl) ⟨7063766, by rfl⟩ : syracuseStep 9418355 = 14127533) B14127533
theorem B23852879 : Blo 1859631 23852879 := bstep (se 1 (by rfl) ⟨17889659, by rfl⟩ : syracuseStep 23852879 = 35779319) B35779319
theorem B4708955 : Blo 1859631 4708955 := bstep (se 1 (by rfl) ⟨3531716, by rfl⟩ : syracuseStep 4708955 = 7063433) B7063433
theorem B1859903 : Blo 1859631 1859903 := bstep (se 1 (by rfl) ⟨1394927, by rfl⟩ : syracuseStep 1859903 = 2789855) B2789855
theorem B734323103 : Blo 1859631 734323103 := bstep (se 1 (by rfl) ⟨550742327, by rfl⟩ : syracuseStep 734323103 = 1101484655) B1101484655
theorem B15901919 : Blo 1859631 15901919 := bstep (se 1 (by rfl) ⟨11926439, by rfl⟩ : syracuseStep 15901919 = 23852879) B23852879
theorem B3139303 : Blo 1859631 3139303 := bstep (se 1 (by rfl) ⟨2354477, by rfl⟩ : syracuseStep 3139303 = 4708955) B4708955
theorem B6277823 : Blo 1859631 6277823 := bstep (se 1 (by rfl) ⟨4708367, by rfl⟩ : syracuseStep 6277823 = 9416735) B9416735
theorem B2092351 : Blo 1859631 2092351 := bstep (se 1 (by rfl) ⟨1569263, by rfl⟩ : syracuseStep 2092351 = 3138527) B3138527
theorem B6278903 : Blo 1859631 6278903 := bstep (se 1 (by rfl) ⟨4709177, by rfl⟩ : syracuseStep 6278903 = 9418355) B9418355
theorem B14136767 : Blo 1859631 14136767 := bstep (se 1 (by rfl) ⟨10602575, by rfl⟩ : syracuseStep 14136767 = 21205151) B21205151
theorem B43538951 : Blo 1859631 43538951 := bstep (se 1 (by rfl) ⟨32654213, by rfl⟩ : syracuseStep 43538951 = 65308427) B65308427
theorem B120732605 : Blo 1859631 120732605 := bstep (se 3 (by rfl) ⟨22637363, by rfl⟩ : syracuseStep 120732605 = 45274727) B45274727
theorem B4709735 : Blo 1859631 4709735 := bstep (se 1 (by rfl) ⟨3532301, by rfl⟩ : syracuseStep 4709735 = 7064603) B7064603
theorem B10601279 : Blo 1859631 10601279 := bstep (se 1 (by rfl) ⟨7950959, by rfl⟩ : syracuseStep 10601279 = 15901919) B15901919
theorem B29025967 : Blo 1859631 29025967 := bstep (se 1 (by rfl) ⟨21769475, by rfl⟩ : syracuseStep 29025967 = 43538951) B43538951
theorem B80488403 : Blo 1859631 80488403 := bstep (se 1 (by rfl) ⟨60366302, by rfl⟩ : syracuseStep 80488403 = 120732605) B120732605
theorem B3139823 : Blo 1859631 3139823 := bstep (se 1 (by rfl) ⟨2354867, by rfl⟩ : syracuseStep 3139823 = 4709735) B4709735
theorem B489548735 : Blo 1859631 489548735 := bstep (se 1 (by rfl) ⟨367161551, by rfl⟩ : syracuseStep 489548735 = 734323103) B734323103
theorem B9424511 : Blo 1859631 9424511 := bstep (se 1 (by rfl) ⟨7068383, by rfl⟩ : syracuseStep 9424511 = 14136767) B14136767
theorem B2789801 : Blo 1859631 2789801 := bstep (se 2 (by rfl) ⟨1046175, by rfl⟩ : syracuseStep 2789801 = 2092351) B2092351
theorem B4185215 : Blo 1859631 4185215 := bstep (se 1 (by rfl) ⟨3138911, by rfl⟩ : syracuseStep 4185215 = 6277823) B6277823
theorem B4185737 : Blo 1859631 4185737 := bstep (se 2 (by rfl) ⟨1569651, by rfl⟩ : syracuseStep 4185737 = 3139303) B3139303
theorem B4185935 : Blo 1859631 4185935 := bstep (se 1 (by rfl) ⟨3139451, by rfl⟩ : syracuseStep 4185935 = 6278903) B6278903
theorem B1859867 : Blo 1859631 1859867 := bstep (se 1 (by rfl) ⟨1394900, by rfl⟩ : syracuseStep 1859867 = 2789801) B2789801
theorem B53658935 : Blo 1859631 53658935 := bstep (se 1 (by rfl) ⟨40244201, by rfl⟩ : syracuseStep 53658935 = 80488403) B80488403
theorem B38701289 : Blo 1859631 38701289 := bstep (se 2 (by rfl) ⟨14512983, by rfl⟩ : syracuseStep 38701289 = 29025967) B29025967
theorem B2093215 : Blo 1859631 2093215 := bstep (se 1 (by rfl) ⟨1569911, by rfl⟩ : syracuseStep 2093215 = 3139823) B3139823
theorem B326365823 : Blo 1859631 326365823 := bstep (se 1 (by rfl) ⟨244774367, by rfl⟩ : syracuseStep 326365823 = 489548735) B489548735
theorem B2790143 : Blo 1859631 2790143 := bstep (se 1 (by rfl) ⟨2092607, by rfl⟩ : syracuseStep 2790143 = 4185215) B4185215
theorem B2790491 : Blo 1859631 2790491 := bstep (se 1 (by rfl) ⟨2092868, by rfl⟩ : syracuseStep 2790491 = 4185737) B4185737
theorem B2790623 : Blo 1859631 2790623 := bstep (se 1 (by rfl) ⟨2092967, by rfl⟩ : syracuseStep 2790623 = 4185935) B4185935
theorem B7067519 : Blo 1859631 7067519 := bstep (se 1 (by rfl) ⟨5300639, by rfl⟩ : syracuseStep 7067519 = 10601279) B10601279
theorem B6283007 : Blo 1859631 6283007 := bstep (se 1 (by rfl) ⟨4712255, by rfl⟩ : syracuseStep 6283007 = 9424511) B9424511
theorem B1860095 : Blo 1859631 1860095 := bstep (se 1 (by rfl) ⟨1395071, by rfl⟩ : syracuseStep 1860095 = 2790143) B2790143
theorem B1860327 : Blo 1859631 1860327 := bstep (se 1 (by rfl) ⟨1395245, by rfl⟩ : syracuseStep 1860327 = 2790491) B2790491
theorem B1860415 : Blo 1859631 1860415 := bstep (se 1 (by rfl) ⟨1395311, by rfl⟩ : syracuseStep 1860415 = 2790623) B2790623
theorem B4711679 : Blo 1859631 4711679 := bstep (se 1 (by rfl) ⟨3533759, by rfl⟩ : syracuseStep 4711679 = 7067519) B7067519
theorem B4188671 : Blo 1859631 4188671 := bstep (se 1 (by rfl) ⟨3141503, by rfl⟩ : syracuseStep 4188671 = 6283007) B6283007
theorem B25800859 : Blo 1859631 25800859 := bstep (se 1 (by rfl) ⟨19350644, by rfl⟩ : syracuseStep 25800859 = 38701289) B38701289
theorem B2790953 : Blo 1859631 2790953 := bstep (se 2 (by rfl) ⟨1046607, by rfl⟩ : syracuseStep 2790953 = 2093215) B2093215
theorem B217577215 : Blo 1859631 217577215 := bstep (se 1 (by rfl) ⟨163182911, by rfl⟩ : syracuseStep 217577215 = 326365823) B326365823
theorem B35772623 : Blo 1859631 35772623 := bstep (se 1 (by rfl) ⟨26829467, by rfl⟩ : syracuseStep 35772623 = 53658935) B53658935
theorem B1860635 : Blo 1859631 1860635 := bstep (se 1 (by rfl) ⟨1395476, by rfl⟩ : syracuseStep 1860635 = 2790953) B2790953
theorem B23848415 : Blo 1859631 23848415 := bstep (se 1 (by rfl) ⟨17886311, by rfl⟩ : syracuseStep 23848415 = 35772623) B35772623
theorem B34401145 : Blo 1859631 34401145 := bstep (se 2 (by rfl) ⟨12900429, by rfl⟩ : syracuseStep 34401145 = 25800859) B25800859
theorem B3141119 : Blo 1859631 3141119 := bstep (se 1 (by rfl) ⟨2355839, by rfl⟩ : syracuseStep 3141119 = 4711679) B4711679
theorem B2792447 : Blo 1859631 2792447 := bstep (se 1 (by rfl) ⟨2094335, by rfl⟩ : syracuseStep 2792447 = 4188671) B4188671
theorem B290102953 : Blo 1859631 290102953 := bstep (se 2 (by rfl) ⟨108788607, by rfl⟩ : syracuseStep 290102953 = 217577215) B217577215
theorem B45868193 : Blo 1859631 45868193 := bstep (se 2 (by rfl) ⟨17200572, by rfl⟩ : syracuseStep 45868193 = 34401145) B34401145
theorem B1861631 : Blo 1859631 1861631 := bstep (se 1 (by rfl) ⟨1396223, by rfl⟩ : syracuseStep 1861631 = 2792447) B2792447
theorem B386803937 : Blo 1859631 386803937 := bstep (se 2 (by rfl) ⟨145051476, by rfl⟩ : syracuseStep 386803937 = 290102953) B290102953
theorem B2094079 : Blo 1859631 2094079 := bstep (se 1 (by rfl) ⟨1570559, by rfl⟩ : syracuseStep 2094079 = 3141119) B3141119
theorem B15898943 : Blo 1859631 15898943 := bstep (se 1 (by rfl) ⟨11924207, by rfl⟩ : syracuseStep 15898943 = 23848415) B23848415
theorem B257869291 : Blo 1859631 257869291 := bstep (se 1 (by rfl) ⟨193401968, by rfl⟩ : syracuseStep 257869291 = 386803937) B386803937
theorem B30578795 : Blo 1859631 30578795 := bstep (se 1 (by rfl) ⟨22934096, by rfl⟩ : syracuseStep 30578795 = 45868193) B45868193
theorem B2792105 : Blo 1859631 2792105 := bstep (se 2 (by rfl) ⟨1047039, by rfl⟩ : syracuseStep 2792105 = 2094079) B2094079
theorem B10599295 : Blo 1859631 10599295 := bstep (se 1 (by rfl) ⟨7949471, by rfl⟩ : syracuseStep 10599295 = 15898943) B15898943
theorem B14132393 : Blo 1859631 14132393 := bstep (se 2 (by rfl) ⟨5299647, by rfl⟩ : syracuseStep 14132393 = 10599295) B10599295
theorem B1861403 : Blo 1859631 1861403 := bstep (se 1 (by rfl) ⟨1396052, by rfl⟩ : syracuseStep 1861403 = 2792105) B2792105
theorem B20385863 : Blo 1859631 20385863 := bstep (se 1 (by rfl) ⟨15289397, by rfl⟩ : syracuseStep 20385863 = 30578795) B30578795
theorem B343825721 : Blo 1859631 343825721 := bstep (se 2 (by rfl) ⟨128934645, by rfl⟩ : syracuseStep 343825721 = 257869291) B257869291
theorem B13590575 : Blo 1859631 13590575 := bstep (se 1 (by rfl) ⟨10192931, by rfl⟩ : syracuseStep 13590575 = 20385863) B20385863
theorem B9421595 : Blo 1859631 9421595 := bstep (se 1 (by rfl) ⟨7066196, by rfl⟩ : syracuseStep 9421595 = 14132393) B14132393
theorem B229217147 : Blo 1859631 229217147 := bstep (se 1 (by rfl) ⟨171912860, by rfl⟩ : syracuseStep 229217147 = 343825721) B343825721
theorem B9060383 : Blo 1859631 9060383 := bstep (se 1 (by rfl) ⟨6795287, by rfl⟩ : syracuseStep 9060383 = 13590575) B13590575
theorem B6281063 : Blo 1859631 6281063 := bstep (se 1 (by rfl) ⟨4710797, by rfl⟩ : syracuseStep 6281063 = 9421595) B9421595
theorem B152811431 : Blo 1859631 152811431 := bstep (se 1 (by rfl) ⟨114608573, by rfl⟩ : syracuseStep 152811431 = 229217147) B229217147
theorem B4187375 : Blo 1859631 4187375 := bstep (se 1 (by rfl) ⟨3140531, by rfl⟩ : syracuseStep 4187375 = 6281063) B6281063
theorem B6040255 : Blo 1859631 6040255 := bstep (se 1 (by rfl) ⟨4530191, by rfl⟩ : syracuseStep 6040255 = 9060383) B9060383
theorem B101874287 : Blo 1859631 101874287 := bstep (se 1 (by rfl) ⟨76405715, by rfl⟩ : syracuseStep 101874287 = 152811431) B152811431
theorem B8053673 : Blo 1859631 8053673 := bstep (se 2 (by rfl) ⟨3020127, by rfl⟩ : syracuseStep 8053673 = 6040255) B6040255
theorem B67916191 : Blo 1859631 67916191 := bstep (se 1 (by rfl) ⟨50937143, by rfl⟩ : syracuseStep 67916191 = 101874287) B101874287
theorem B2791583 : Blo 1859631 2791583 := bstep (se 1 (by rfl) ⟨2093687, by rfl⟩ : syracuseStep 2791583 = 4187375) B4187375
theorem B90554921 : Blo 1859631 90554921 := bstep (se 2 (by rfl) ⟨33958095, by rfl⟩ : syracuseStep 90554921 = 67916191) B67916191
theorem B1861055 : Blo 1859631 1861055 := bstep (se 1 (by rfl) ⟨1395791, by rfl⟩ : syracuseStep 1861055 = 2791583) B2791583
theorem B21476461 : Blo 1859631 21476461 := bstep (se 3 (by rfl) ⟨4026836, by rfl⟩ : syracuseStep 21476461 = 8053673) B8053673
theorem B60369947 : Blo 1859631 60369947 := bstep (se 1 (by rfl) ⟨45277460, by rfl⟩ : syracuseStep 60369947 = 90554921) B90554921
theorem B28635281 : Blo 1859631 28635281 := bstep (se 2 (by rfl) ⟨10738230, by rfl⟩ : syracuseStep 28635281 = 21476461) B21476461
theorem B19090187 : Blo 1859631 19090187 := bstep (se 1 (by rfl) ⟨14317640, by rfl⟩ : syracuseStep 19090187 = 28635281) B28635281
theorem B40246631 : Blo 1859631 40246631 := bstep (se 1 (by rfl) ⟨30184973, by rfl⟩ : syracuseStep 40246631 = 60369947) B60369947
theorem B26831087 : Blo 1859631 26831087 := bstep (se 1 (by rfl) ⟨20123315, by rfl⟩ : syracuseStep 26831087 = 40246631) B40246631
theorem B12726791 : Blo 1859631 12726791 := bstep (se 1 (by rfl) ⟨9545093, by rfl⟩ : syracuseStep 12726791 = 19090187) B19090187
theorem B17887391 : Blo 1859631 17887391 := bstep (se 1 (by rfl) ⟨13415543, by rfl⟩ : syracuseStep 17887391 = 26831087) B26831087
theorem B8484527 : Blo 1859631 8484527 := bstep (se 1 (by rfl) ⟨6363395, by rfl⟩ : syracuseStep 8484527 = 12726791) B12726791
theorem B11924927 : Blo 1859631 11924927 := bstep (se 1 (by rfl) ⟨8943695, by rfl⟩ : syracuseStep 11924927 = 17887391) B17887391
theorem B22625405 : Blo 1859631 22625405 := bstep (se 3 (by rfl) ⟨4242263, by rfl⟩ : syracuseStep 22625405 = 8484527) B8484527
theorem B15083603 : Blo 1859631 15083603 := bstep (se 1 (by rfl) ⟨11312702, by rfl⟩ : syracuseStep 15083603 = 22625405) B22625405
theorem B7949951 : Blo 1859631 7949951 := bstep (se 1 (by rfl) ⟨5962463, by rfl⟩ : syracuseStep 7949951 = 11924927) B11924927
theorem B10055735 : Blo 1859631 10055735 := bstep (se 1 (by rfl) ⟨7541801, by rfl⟩ : syracuseStep 10055735 = 15083603) B15083603
theorem B5299967 : Blo 1859631 5299967 := bstep (se 1 (by rfl) ⟨3974975, by rfl⟩ : syracuseStep 5299967 = 7949951) B7949951
theorem B3533311 : Blo 1859631 3533311 := bstep (se 1 (by rfl) ⟨2649983, by rfl⟩ : syracuseStep 3533311 = 5299967) B5299967
theorem B6703823 : Blo 1859631 6703823 := bstep (se 1 (by rfl) ⟨5027867, by rfl⟩ : syracuseStep 6703823 = 10055735) B10055735
theorem B4711081 : Blo 1859631 4711081 := bstep (se 2 (by rfl) ⟨1766655, by rfl⟩ : syracuseStep 4711081 = 3533311) B3533311
theorem B4469215 : Blo 1859631 4469215 := bstep (se 1 (by rfl) ⟨3351911, by rfl⟩ : syracuseStep 4469215 = 6703823) B6703823
theorem B5958953 : Blo 1859631 5958953 := bstep (se 2 (by rfl) ⟨2234607, by rfl⟩ : syracuseStep 5958953 = 4469215) B4469215
theorem B6281441 : Blo 1859631 6281441 := bstep (se 2 (by rfl) ⟨2355540, by rfl⟩ : syracuseStep 6281441 = 4711081) B4711081
theorem B4187627 : Blo 1859631 4187627 := bstep (se 1 (by rfl) ⟨3140720, by rfl⟩ : syracuseStep 4187627 = 6281441) B6281441
theorem B3972635 : Blo 1859631 3972635 := bstep (se 1 (by rfl) ⟨2979476, by rfl⟩ : syracuseStep 3972635 = 5958953) B5958953
theorem B2648423 : Blo 1859631 2648423 := bstep (se 1 (by rfl) ⟨1986317, by rfl⟩ : syracuseStep 2648423 = 3972635) B3972635
theorem B2791751 : Blo 1859631 2791751 := bstep (se 1 (by rfl) ⟨2093813, by rfl⟩ : syracuseStep 2791751 = 4187627) B4187627
theorem B7062461 : Blo 1859631 7062461 := bstep (se 3 (by rfl) ⟨1324211, by rfl⟩ : syracuseStep 7062461 = 2648423) B2648423
theorem B1861167 : Blo 1859631 1861167 := bstep (se 1 (by rfl) ⟨1395875, by rfl⟩ : syracuseStep 1861167 = 2791751) B2791751
theorem B4708307 : Blo 1859631 4708307 := bstep (se 1 (by rfl) ⟨3531230, by rfl⟩ : syracuseStep 4708307 = 7062461) B7062461
theorem B3138871 : Blo 1859631 3138871 := bstep (se 1 (by rfl) ⟨2354153, by rfl⟩ : syracuseStep 3138871 = 4708307) B4708307
theorem B4185161 : Blo 1859631 4185161 := bstep (se 2 (by rfl) ⟨1569435, by rfl⟩ : syracuseStep 4185161 = 3138871) B3138871
theorem B2790107 : Blo 1859631 2790107 := bstep (se 1 (by rfl) ⟨2092580, by rfl⟩ : syracuseStep 2790107 = 4185161) B4185161
theorem B1860071 : Blo 1859631 1860071 := bstep (se 1 (by rfl) ⟨1395053, by rfl⟩ : syracuseStep 1860071 = 2790107) B2790107

theorem C0 (j : ℕ) (h1 : 464907 ≤ j) (h2 : j ≤ 465407) : Blo 1859631 (4 * j + 3) := by
  interval_cases j
  · exact B1859631
  · exact B1859635
  · exact B1859639
  · exact B1859643
  · exact B1859647
  · exact B1859651
  · exact B1859655
  · exact B1859659
  · exact B1859663
  · exact B1859667
  · exact B1859671
  · exact B1859675
  · exact B1859679
  · exact B1859683
  · exact B1859687
  · exact B1859691
  · exact B1859695
  · exact B1859699
  · exact B1859703
  · exact B1859707
  · exact B1859711
  · exact B1859715
  · exact B1859719
  · exact B1859723
  · exact B1859727
  · exact B1859731
  · exact B1859735
  · exact B1859739
  · exact B1859743
  · exact B1859747
  · exact B1859751
  · exact B1859755
  · exact B1859759
  · exact B1859763
  · exact B1859767
  · exact B1859771
  · exact B1859775
  · exact B1859779
  · exact B1859783
  · exact B1859787
  · exact B1859791
  · exact B1859795
  · exact B1859799
  · exact B1859803
  · exact B1859807
  · exact B1859811
  · exact B1859815
  · exact B1859819
  · exact B1859823
  · exact B1859827
  · exact B1859831
  · exact B1859835
  · exact B1859839
  · exact B1859843
  · exact B1859847
  · exact B1859851
  · exact B1859855
  · exact B1859859
  · exact B1859863
  · exact B1859867
  · exact B1859871
  · exact B1859875
  · exact B1859879
  · exact B1859883
  · exact B1859887
  · exact B1859891
  · exact B1859895
  · exact B1859899
  · exact B1859903
  · exact B1859907
  · exact B1859911
  · exact B1859915
  · exact B1859919
  · exact B1859923
  · exact B1859927
  · exact B1859931
  · exact B1859935
  · exact B1859939
  · exact B1859943
  · exact B1859947
  · exact B1859951
  · exact B1859955
  · exact B1859959
  · exact B1859963
  · exact B1859967
  · exact B1859971
  · exact B1859975
  · exact B1859979
  · exact B1859983
  · exact B1859987
  · exact B1859991
  · exact B1859995
  · exact B1859999
  · exact B1860003
  · exact B1860007
  · exact B1860011
  · exact B1860015
  · exact B1860019
  · exact B1860023
  · exact B1860027
  · exact B1860031
  · exact B1860035
  · exact B1860039
  · exact B1860043
  · exact B1860047
  · exact B1860051
  · exact B1860055
  · exact B1860059
  · exact B1860063
  · exact B1860067
  · exact B1860071
  · exact B1860075
  · exact B1860079
  · exact B1860083
  · exact B1860087
  · exact B1860091
  · exact B1860095
  · exact B1860099
  · exact B1860103
  · exact B1860107
  · exact B1860111
  · exact B1860115
  · exact B1860119
  · exact B1860123
  · exact B1860127
  · exact B1860131
  · exact B1860135
  · exact B1860139
  · exact B1860143
  · exact B1860147
  · exact B1860151
  · exact B1860155
  · exact B1860159
  · exact B1860163
  · exact B1860167
  · exact B1860171
  · exact B1860175
  · exact B1860179
  · exact B1860183
  · exact B1860187
  · exact B1860191
  · exact B1860195
  · exact B1860199
  · exact B1860203
  · exact B1860207
  · exact B1860211
  · exact B1860215
  · exact B1860219
  · exact B1860223
  · exact B1860227
  · exact B1860231
  · exact B1860235
  · exact B1860239
  · exact B1860243
  · exact B1860247
  · exact B1860251
  · exact B1860255
  · exact B1860259
  · exact B1860263
  · exact B1860267
  · exact B1860271
  · exact B1860275
  · exact B1860279
  · exact B1860283
  · exact B1860287
  · exact B1860291
  · exact B1860295
  · exact B1860299
  · exact B1860303
  · exact B1860307
  · exact B1860311
  · exact B1860315
  · exact B1860319
  · exact B1860323
  · exact B1860327
  · exact B1860331
  · exact B1860335
  · exact B1860339
  · exact B1860343
  · exact B1860347
  · exact B1860351
  · exact B1860355
  · exact B1860359
  · exact B1860363
  · exact B1860367
  · exact B1860371
  · exact B1860375
  · exact B1860379
  · exact B1860383
  · exact B1860387
  · exact B1860391
  · exact B1860395
  · exact B1860399
  · exact B1860403
  · exact B1860407
  · exact B1860411
  · exact B1860415
  · exact B1860419
  · exact B1860423
  · exact B1860427
  · exact B1860431
  · exact B1860435
  · exact B1860439
  · exact B1860443
  · exact B1860447
  · exact B1860451
  · exact B1860455
  · exact B1860459
  · exact B1860463
  · exact B1860467
  · exact B1860471
  · exact B1860475
  · exact B1860479
  · exact B1860483
  · exact B1860487
  · exact B1860491
  · exact B1860495
  · exact B1860499
  · exact B1860503
  · exact B1860507
  · exact B1860511
  · exact B1860515
  · exact B1860519
  · exact B1860523
  · exact B1860527
  · exact B1860531
  · exact B1860535
  · exact B1860539
  · exact B1860543
  · exact B1860547
  · exact B1860551
  · exact B1860555
  · exact B1860559
  · exact B1860563
  · exact B1860567
  · exact B1860571
  · exact B1860575
  · exact B1860579
  · exact B1860583
  · exact B1860587
  · exact B1860591
  · exact B1860595
  · exact B1860599
  · exact B1860603
  · exact B1860607
  · exact B1860611
  · exact B1860615
  · exact B1860619
  · exact B1860623
  · exact B1860627
  · exact B1860631
  · exact B1860635
  · exact B1860639
  · exact B1860643
  · exact B1860647
  · exact B1860651
  · exact B1860655
  · exact B1860659
  · exact B1860663
  · exact B1860667
  · exact B1860671
  · exact B1860675
  · exact B1860679
  · exact B1860683
  · exact B1860687
  · exact B1860691
  · exact B1860695
  · exact B1860699
  · exact B1860703
  · exact B1860707
  · exact B1860711
  · exact B1860715
  · exact B1860719
  · exact B1860723
  · exact B1860727
  · exact B1860731
  · exact B1860735
  · exact B1860739
  · exact B1860743
  · exact B1860747
  · exact B1860751
  · exact B1860755
  · exact B1860759
  · exact B1860763
  · exact B1860767
  · exact B1860771
  · exact B1860775
  · exact B1860779
  · exact B1860783
  · exact B1860787
  · exact B1860791
  · exact B1860795
  · exact B1860799
  · exact B1860803
  · exact B1860807
  · exact B1860811
  · exact B1860815
  · exact B1860819
  · exact B1860823
  · exact B1860827
  · exact B1860831
  · exact B1860835
  · exact B1860839
  · exact B1860843
  · exact B1860847
  · exact B1860851
  · exact B1860855
  · exact B1860859
  · exact B1860863
  · exact B1860867
  · exact B1860871
  · exact B1860875
  · exact B1860879
  · exact B1860883
  · exact B1860887
  · exact B1860891
  · exact B1860895
  · exact B1860899
  · exact B1860903
  · exact B1860907
  · exact B1860911
  · exact B1860915
  · exact B1860919
  · exact B1860923
  · exact B1860927
  · exact B1860931
  · exact B1860935
  · exact B1860939
  · exact B1860943
  · exact B1860947
  · exact B1860951
  · exact B1860955
  · exact B1860959
  · exact B1860963
  · exact B1860967
  · exact B1860971
  · exact B1860975
  · exact B1860979
  · exact B1860983
  · exact B1860987
  · exact B1860991
  · exact B1860995
  · exact B1860999
  · exact B1861003
  · exact B1861007
  · exact B1861011
  · exact B1861015
  · exact B1861019
  · exact B1861023
  · exact B1861027
  · exact B1861031
  · exact B1861035
  · exact B1861039
  · exact B1861043
  · exact B1861047
  · exact B1861051
  · exact B1861055
  · exact B1861059
  · exact B1861063
  · exact B1861067
  · exact B1861071
  · exact B1861075
  · exact B1861079
  · exact B1861083
  · exact B1861087
  · exact B1861091
  · exact B1861095
  · exact B1861099
  · exact B1861103
  · exact B1861107
  · exact B1861111
  · exact B1861115
  · exact B1861119
  · exact B1861123
  · exact B1861127
  · exact B1861131
  · exact B1861135
  · exact B1861139
  · exact B1861143
  · exact B1861147
  · exact B1861151
  · exact B1861155
  · exact B1861159
  · exact B1861163
  · exact B1861167
  · exact B1861171
  · exact B1861175
  · exact B1861179
  · exact B1861183
  · exact B1861187
  · exact B1861191
  · exact B1861195
  · exact B1861199
  · exact B1861203
  · exact B1861207
  · exact B1861211
  · exact B1861215
  · exact B1861219
  · exact B1861223
  · exact B1861227
  · exact B1861231
  · exact B1861235
  · exact B1861239
  · exact B1861243
  · exact B1861247
  · exact B1861251
  · exact B1861255
  · exact B1861259
  · exact B1861263
  · exact B1861267
  · exact B1861271
  · exact B1861275
  · exact B1861279
  · exact B1861283
  · exact B1861287
  · exact B1861291
  · exact B1861295
  · exact B1861299
  · exact B1861303
  · exact B1861307
  · exact B1861311
  · exact B1861315
  · exact B1861319
  · exact B1861323
  · exact B1861327
  · exact B1861331
  · exact B1861335
  · exact B1861339
  · exact B1861343
  · exact B1861347
  · exact B1861351
  · exact B1861355
  · exact B1861359
  · exact B1861363
  · exact B1861367
  · exact B1861371
  · exact B1861375
  · exact B1861379
  · exact B1861383
  · exact B1861387
  · exact B1861391
  · exact B1861395
  · exact B1861399
  · exact B1861403
  · exact B1861407
  · exact B1861411
  · exact B1861415
  · exact B1861419
  · exact B1861423
  · exact B1861427
  · exact B1861431
  · exact B1861435
  · exact B1861439
  · exact B1861443
  · exact B1861447
  · exact B1861451
  · exact B1861455
  · exact B1861459
  · exact B1861463
  · exact B1861467
  · exact B1861471
  · exact B1861475
  · exact B1861479
  · exact B1861483
  · exact B1861487
  · exact B1861491
  · exact B1861495
  · exact B1861499
  · exact B1861503
  · exact B1861507
  · exact B1861511
  · exact B1861515
  · exact B1861519
  · exact B1861523
  · exact B1861527
  · exact B1861531
  · exact B1861535
  · exact B1861539
  · exact B1861543
  · exact B1861547
  · exact B1861551
  · exact B1861555
  · exact B1861559
  · exact B1861563
  · exact B1861567
  · exact B1861571
  · exact B1861575
  · exact B1861579
  · exact B1861583
  · exact B1861587
  · exact B1861591
  · exact B1861595
  · exact B1861599
  · exact B1861603
  · exact B1861607
  · exact B1861611
  · exact B1861615
  · exact B1861619
  · exact B1861623
  · exact B1861627
  · exact B1861631

theorem solution (m : ℕ) (hlo : 1859631 ≤ m) (hhi : m ≤ 1861631) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 464907 ≤ j := by omega
    have hj2 : j ≤ 465407 := by omega
    have hb : Blo 1859631 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
