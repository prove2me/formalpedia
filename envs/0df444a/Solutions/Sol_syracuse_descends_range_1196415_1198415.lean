-- Prove2me | solution 1 for syracuse_descends_range_1196415_1198415
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:10:42.960696+00:00
-- url     : https://prove2.me/submissions/4050e766-9a87-48c3-b0ac-f5ad7bd840e8

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


theorem B2695229 : Blo 1196415 2695229 := bbase (se 3 (by rfl) ⟨505355, by rfl⟩ : syracuseStep 2695229 = 1010711) (by norm_num)
theorem B3457093 : Blo 1196415 3457093 := bbase (se 4 (by rfl) ⟨324102, by rfl⟩ : syracuseStep 3457093 = 648205) (by norm_num)
theorem B1515601 : Blo 1196415 1515601 := bbase (se 2 (by rfl) ⟨568350, by rfl⟩ : syracuseStep 1515601 = 1136701) (by norm_num)
theorem B5111909 : Blo 1196415 5111909 := bbase (se 4 (by rfl) ⟨479241, by rfl⟩ : syracuseStep 5111909 = 958483) (by norm_num)
theorem B3031141 : Blo 1196415 3031141 := bbase (se 4 (by rfl) ⟨284169, by rfl⟩ : syracuseStep 3031141 = 568339) (by norm_num)
theorem B1917037 : Blo 1196415 1917037 := bbase (se 3 (by rfl) ⟨359444, by rfl⟩ : syracuseStep 1917037 = 718889) (by norm_num)
theorem B2695301 : Blo 1196415 2695301 := bbase (se 4 (by rfl) ⟨252684, by rfl⟩ : syracuseStep 2695301 = 505369) (by norm_num)
theorem B4038821 : Blo 1196415 4038821 := bbase (se 4 (by rfl) ⟨378639, by rfl⟩ : syracuseStep 4038821 = 757279) (by norm_num)
theorem B2695373 : Blo 1196415 2695373 := bbase (se 3 (by rfl) ⟨505382, by rfl⟩ : syracuseStep 2695373 = 1010765) (by norm_num)
theorem B3031253 : Blo 1196415 3031253 := bbase (se 7 (by rfl) ⟨35522, by rfl⟩ : syracuseStep 3031253 = 71045) (by norm_num)
theorem B2556125 : Blo 1196415 2556125 := bbase (se 3 (by rfl) ⟨479273, by rfl⟩ : syracuseStep 2556125 = 958547) (by norm_num)
theorem B5751013 : Blo 1196415 5751013 := bbase (se 4 (by rfl) ⟨539157, by rfl⟩ : syracuseStep 5751013 = 1078315) (by norm_num)
theorem B1515773 : Blo 1196415 1515773 := bbase (se 3 (by rfl) ⟨284207, by rfl⟩ : syracuseStep 1515773 = 568415) (by norm_num)
theorem B1704197 : Blo 1196415 1704197 := bbase (se 4 (by rfl) ⟨159768, by rfl⟩ : syracuseStep 1704197 = 319537) (by norm_num)
theorem B2695445 : Blo 1196415 2695445 := bbase (se 6 (by rfl) ⟨63174, by rfl⟩ : syracuseStep 2695445 = 126349) (by norm_num)
theorem B1515829 : Blo 1196415 1515829 := bbase (se 5 (by rfl) ⟨71054, by rfl⟩ : syracuseStep 1515829 = 142109) (by norm_num)
theorem B1704277 : Blo 1196415 1704277 := bbase (se 10 (by rfl) ⟨2496, by rfl⟩ : syracuseStep 1704277 = 4993) (by norm_num)
theorem B2695517 : Blo 1196415 2695517 := bbase (se 3 (by rfl) ⟨505409, by rfl⟩ : syracuseStep 2695517 = 1010819) (by norm_num)
theorem B1212769 : Blo 1196415 1212769 := bbase (se 2 (by rfl) ⟨454788, by rfl⟩ : syracuseStep 1212769 = 909577) (by norm_num)
theorem B1278353 : Blo 1196415 1278353 := bbase (se 2 (by rfl) ⟨479382, by rfl⟩ : syracuseStep 1278353 = 958765) (by norm_num)
theorem B3031445 : Blo 1196415 3031445 := bbase (se 6 (by rfl) ⟨71049, by rfl⟩ : syracuseStep 3031445 = 142099) (by norm_num)
theorem B1515925 : Blo 1196415 1515925 := bbase (se 6 (by rfl) ⟨35529, by rfl⟩ : syracuseStep 1515925 = 71059) (by norm_num)
theorem B1458589 : Blo 1196415 1458589 := bbase (se 3 (by rfl) ⟨273485, by rfl⟩ : syracuseStep 1458589 = 546971) (by norm_num)
theorem B2695589 : Blo 1196415 2695589 := bbase (se 4 (by rfl) ⟨252711, by rfl⟩ : syracuseStep 2695589 = 505423) (by norm_num)
theorem B1704397 : Blo 1196415 1704397 := bbase (se 3 (by rfl) ⟨319574, by rfl⟩ : syracuseStep 1704397 = 639149) (by norm_num)
theorem B2769365 : Blo 1196415 2769365 := bbase (se 7 (by rfl) ⟨32453, by rfl⟩ : syracuseStep 2769365 = 64907) (by norm_num)
theorem B2695661 : Blo 1196415 2695661 := bbase (se 3 (by rfl) ⟨505436, by rfl⟩ : syracuseStep 2695661 = 1010873) (by norm_num)
theorem B11502101 : Blo 1196415 11502101 := bbase (se 6 (by rfl) ⟨269580, by rfl⟩ : syracuseStep 11502101 = 539161) (by norm_num)
theorem B2875949 : Blo 1196415 2875949 := bbase (se 3 (by rfl) ⟨539240, by rfl⟩ : syracuseStep 2875949 = 1078481) (by norm_num)
theorem B1704493 : Blo 1196415 1704493 := bbase (se 3 (by rfl) ⟨319592, by rfl⟩ : syracuseStep 1704493 = 639185) (by norm_num)
theorem B2695733 : Blo 1196415 2695733 := bbase (se 5 (by rfl) ⟨126362, by rfl⟩ : syracuseStep 2695733 = 252725) (by norm_num)
theorem B1516097 : Blo 1196415 1516097 := bbase (se 2 (by rfl) ⟨568536, by rfl⟩ : syracuseStep 1516097 = 1137073) (by norm_num)
theorem B1794629 : Blo 1196415 1794629 := bbase (se 4 (by rfl) ⟨168246, by rfl⟩ : syracuseStep 1794629 = 336493) (by norm_num)
theorem B1278541 : Blo 1196415 1278541 := bbase (se 3 (by rfl) ⟨239726, by rfl⟩ : syracuseStep 1278541 = 479453) (by norm_num)
theorem B4039253 : Blo 1196415 4039253 := bbase (se 8 (by rfl) ⟨23667, by rfl⟩ : syracuseStep 4039253 = 47335) (by norm_num)
theorem B6824533 : Blo 1196415 6824533 := bbase (se 8 (by rfl) ⟨39987, by rfl⟩ : syracuseStep 6824533 = 79975) (by norm_num)
theorem B1229401 : Blo 1196415 1229401 := bbase (se 2 (by rfl) ⟨461025, by rfl⟩ : syracuseStep 1229401 = 922051) (by norm_num)
theorem B1794653 : Blo 1196415 1794653 := bbase (se 3 (by rfl) ⟨336497, by rfl⟩ : syracuseStep 1794653 = 672995) (by norm_num)
theorem B1794677 : Blo 1196415 1794677 := bbase (se 5 (by rfl) ⟨84125, by rfl⟩ : syracuseStep 1794677 = 168251) (by norm_num)
theorem B1516153 : Blo 1196415 1516153 := bbase (se 2 (by rfl) ⟨568557, by rfl⟩ : syracuseStep 1516153 = 1137115) (by norm_num)
theorem B2695805 : Blo 1196415 2695805 := bbase (se 3 (by rfl) ⟨505463, by rfl⟩ : syracuseStep 2695805 = 1010927) (by norm_num)
theorem B1794701 : Blo 1196415 1794701 := bbase (se 3 (by rfl) ⟨336506, by rfl⟩ : syracuseStep 1794701 = 673013) (by norm_num)
theorem B1794725 : Blo 1196415 1794725 := bbase (se 4 (by rfl) ⟨168255, by rfl⟩ : syracuseStep 1794725 = 336511) (by norm_num)
theorem B1794749 : Blo 1196415 1794749 := bbase (se 3 (by rfl) ⟨336515, by rfl⟩ : syracuseStep 1794749 = 673031) (by norm_num)
theorem B2695877 : Blo 1196415 2695877 := bbase (se 4 (by rfl) ⟨252738, by rfl⟩ : syracuseStep 2695877 = 505477) (by norm_num)
theorem B1794773 : Blo 1196415 1794773 := bbase (se 7 (by rfl) ⟨21032, by rfl⟩ : syracuseStep 1794773 = 42065) (by norm_num)
theorem B1516249 : Blo 1196415 1516249 := bbase (se 2 (by rfl) ⟨568593, by rfl⟩ : syracuseStep 1516249 = 1137187) (by norm_num)
theorem B1794797 : Blo 1196415 1794797 := bbase (se 3 (by rfl) ⟨336524, by rfl⟩ : syracuseStep 1794797 = 673049) (by norm_num)
theorem B2876141 : Blo 1196415 2876141 := bbase (se 3 (by rfl) ⟨539276, by rfl⟩ : syracuseStep 2876141 = 1078553) (by norm_num)
theorem B3031789 : Blo 1196415 3031789 := bbase (se 3 (by rfl) ⟨568460, by rfl⟩ : syracuseStep 3031789 = 1136921) (by norm_num)
theorem B1794821 : Blo 1196415 1794821 := bbase (se 4 (by rfl) ⟨168264, by rfl⟩ : syracuseStep 1794821 = 336529) (by norm_num)
theorem B2695949 : Blo 1196415 2695949 := bbase (se 3 (by rfl) ⟨505490, by rfl⟩ : syracuseStep 2695949 = 1010981) (by norm_num)
theorem B14754581 : Blo 1196415 14754581 := bbase (se 6 (by rfl) ⟨345810, by rfl⟩ : syracuseStep 14754581 = 691621) (by norm_num)
theorem B1794845 : Blo 1196415 1794845 := bbase (se 3 (by rfl) ⟨336533, by rfl⟩ : syracuseStep 1794845 = 673067) (by norm_num)
theorem B1794869 : Blo 1196415 1794869 := bbase (se 5 (by rfl) ⟨84134, by rfl⟩ : syracuseStep 1794869 = 168269) (by norm_num)
theorem B1794893 : Blo 1196415 1794893 := bbase (se 3 (by rfl) ⟨336542, by rfl⟩ : syracuseStep 1794893 = 673085) (by norm_num)
theorem B2696021 : Blo 1196415 2696021 := bbase (se 9 (by rfl) ⟨7898, by rfl⟩ : syracuseStep 2696021 = 15797) (by norm_num)
theorem B3031901 : Blo 1196415 3031901 := bbase (se 3 (by rfl) ⟨568481, by rfl⟩ : syracuseStep 3031901 = 1136963) (by norm_num)
theorem B1794917 : Blo 1196415 1794917 := bbase (se 4 (by rfl) ⟨168273, by rfl⟩ : syracuseStep 1794917 = 336547) (by norm_num)
theorem B1794941 : Blo 1196415 1794941 := bbase (se 3 (by rfl) ⟨336551, by rfl⟩ : syracuseStep 1794941 = 673103) (by norm_num)
theorem B1516421 : Blo 1196415 1516421 := bbase (se 4 (by rfl) ⟨142164, by rfl⟩ : syracuseStep 1516421 = 284329) (by norm_num)
theorem B1794965 : Blo 1196415 1794965 := bbase (se 6 (by rfl) ⟨42069, by rfl⟩ : syracuseStep 1794965 = 84139) (by norm_num)
theorem B2696093 : Blo 1196415 2696093 := bbase (se 3 (by rfl) ⟨505517, by rfl⟩ : syracuseStep 2696093 = 1011035) (by norm_num)
theorem B1794989 : Blo 1196415 1794989 := bbase (se 3 (by rfl) ⟨336560, by rfl⟩ : syracuseStep 1794989 = 673121) (by norm_num)
theorem B1516477 : Blo 1196415 1516477 := bbase (se 3 (by rfl) ⟨284339, by rfl⟩ : syracuseStep 1516477 = 568679) (by norm_num)
theorem B1795013 : Blo 1196415 1795013 := bbase (se 4 (by rfl) ⟨168282, by rfl⟩ : syracuseStep 1795013 = 336565) (by norm_num)
theorem B1795037 : Blo 1196415 1795037 := bbase (se 3 (by rfl) ⟨336569, by rfl⟩ : syracuseStep 1795037 = 673139) (by norm_num)
theorem B2696165 : Blo 1196415 2696165 := bbase (se 4 (by rfl) ⟨252765, by rfl⟩ : syracuseStep 2696165 = 505531) (by norm_num)
theorem B1795061 : Blo 1196415 1795061 := bbase (se 5 (by rfl) ⟨84143, by rfl⟩ : syracuseStep 1795061 = 168287) (by norm_num)
theorem B4039685 : Blo 1196415 4039685 := bbase (se 4 (by rfl) ⟨378720, by rfl⟩ : syracuseStep 4039685 = 757441) (by norm_num)
theorem B1795085 : Blo 1196415 1795085 := bbase (se 3 (by rfl) ⟨336578, by rfl⟩ : syracuseStep 1795085 = 673157) (by norm_num)
theorem B2876429 : Blo 1196415 2876429 := bbase (se 3 (by rfl) ⟨539330, by rfl⟩ : syracuseStep 2876429 = 1078661) (by norm_num)
theorem B1917965 : Blo 1196415 1917965 := bbase (se 3 (by rfl) ⟨359618, by rfl⟩ : syracuseStep 1917965 = 719237) (by norm_num)
theorem B1704989 : Blo 1196415 1704989 := bbase (se 3 (by rfl) ⟨319685, by rfl⟩ : syracuseStep 1704989 = 639371) (by norm_num)
theorem B3032093 : Blo 1196415 3032093 := bbase (se 3 (by rfl) ⟨568517, by rfl⟩ : syracuseStep 3032093 = 1137035) (by norm_num)
theorem B1516573 : Blo 1196415 1516573 := bbase (se 3 (by rfl) ⟨284357, by rfl⟩ : syracuseStep 1516573 = 568715) (by norm_num)
theorem B1795109 : Blo 1196415 1795109 := bbase (se 4 (by rfl) ⟨168291, by rfl⟩ : syracuseStep 1795109 = 336583) (by norm_num)
theorem B1819693 : Blo 1196415 1819693 := bbase (se 3 (by rfl) ⟨341192, by rfl⟩ : syracuseStep 1819693 = 682385) (by norm_num)
theorem B2696237 : Blo 1196415 2696237 := bbase (se 3 (by rfl) ⟨505544, by rfl⟩ : syracuseStep 2696237 = 1011089) (by norm_num)
theorem B1795133 : Blo 1196415 1795133 := bbase (se 3 (by rfl) ⟨336587, by rfl⟩ : syracuseStep 1795133 = 673175) (by norm_num)
theorem B6063173 : Blo 1196415 6063173 := bbase (se 4 (by rfl) ⟨568422, by rfl⟩ : syracuseStep 6063173 = 1136845) (by norm_num)
theorem B1795157 : Blo 1196415 1795157 := bbase (se 8 (by rfl) ⟨10518, by rfl⟩ : syracuseStep 1795157 = 21037) (by norm_num)
theorem B2557013 : Blo 1196415 2557013 := bbase (se 8 (by rfl) ⟨14982, by rfl⟩ : syracuseStep 2557013 = 29965) (by norm_num)
theorem B1795181 : Blo 1196415 1795181 := bbase (se 3 (by rfl) ⟨336596, by rfl⟩ : syracuseStep 1795181 = 673193) (by norm_num)
theorem B2696309 : Blo 1196415 2696309 := bbase (se 5 (by rfl) ⟨126389, by rfl⟩ : syracuseStep 2696309 = 252779) (by norm_num)
theorem B1795205 : Blo 1196415 1795205 := bbase (se 4 (by rfl) ⟨168300, by rfl⟩ : syracuseStep 1795205 = 336601) (by norm_num)
theorem B6915221 : Blo 1196415 6915221 := bbase (se 6 (by rfl) ⟨162075, by rfl⟩ : syracuseStep 6915221 = 324151) (by norm_num)
theorem B1795229 : Blo 1196415 1795229 := bbase (se 3 (by rfl) ⟨336605, by rfl⟩ : syracuseStep 1795229 = 673211) (by norm_num)
theorem B1795253 : Blo 1196415 1795253 := bbase (se 5 (by rfl) ⟨84152, by rfl⟩ : syracuseStep 1795253 = 168305) (by norm_num)
theorem B2335925 : Blo 1196415 2335925 := bbase (se 5 (by rfl) ⟨109496, by rfl⟩ : syracuseStep 2335925 = 218993) (by norm_num)
theorem B2696381 : Blo 1196415 2696381 := bbase (se 3 (by rfl) ⟨505571, by rfl⟩ : syracuseStep 2696381 = 1011143) (by norm_num)
theorem B1516745 : Blo 1196415 1516745 := bbase (se 2 (by rfl) ⟨568779, by rfl⟩ : syracuseStep 1516745 = 1137559) (by norm_num)
theorem B1795277 : Blo 1196415 1795277 := bbase (se 3 (by rfl) ⟨336614, by rfl⟩ : syracuseStep 1795277 = 673229) (by norm_num)
theorem B1795301 : Blo 1196415 1795301 := bbase (se 4 (by rfl) ⟨168309, by rfl⟩ : syracuseStep 1795301 = 336619) (by norm_num)
theorem B5833957 : Blo 1196415 5833957 := bbase (se 4 (by rfl) ⟨546933, by rfl⟩ : syracuseStep 5833957 = 1093867) (by norm_num)
theorem B1795325 : Blo 1196415 1795325 := bbase (se 3 (by rfl) ⟨336623, by rfl⟩ : syracuseStep 1795325 = 673247) (by norm_num)
theorem B1795349 : Blo 1196415 1795349 := bbase (se 6 (by rfl) ⟨42078, by rfl⟩ : syracuseStep 1795349 = 84157) (by norm_num)
theorem B1795373 : Blo 1196415 1795373 := bbase (se 3 (by rfl) ⟨336632, by rfl⟩ : syracuseStep 1795373 = 673265) (by norm_num)
theorem B1795397 : Blo 1196415 1795397 := bbase (se 4 (by rfl) ⟨168318, by rfl⟩ : syracuseStep 1795397 = 336637) (by norm_num)
theorem B2557253 : Blo 1196415 2557253 := bbase (se 4 (by rfl) ⟨239742, by rfl⟩ : syracuseStep 2557253 = 479485) (by norm_num)
theorem B1795421 : Blo 1196415 1795421 := bbase (se 3 (by rfl) ⟨336641, by rfl⟩ : syracuseStep 1795421 = 673283) (by norm_num)
theorem B1795445 : Blo 1196415 1795445 := bbase (se 5 (by rfl) ⟨84161, by rfl⟩ : syracuseStep 1795445 = 168323) (by norm_num)
theorem B9094517 : Blo 1196415 9094517 := bbase (se 5 (by rfl) ⟨426305, by rfl⟩ : syracuseStep 9094517 = 852611) (by norm_num)
theorem B3032437 : Blo 1196415 3032437 := bbase (se 5 (by rfl) ⟨142145, by rfl⟩ : syracuseStep 3032437 = 284291) (by norm_num)
theorem B1279361 : Blo 1196415 1279361 := bbase (se 2 (by rfl) ⟨479760, by rfl⟩ : syracuseStep 1279361 = 959521) (by norm_num)
theorem B1795469 : Blo 1196415 1795469 := bbase (se 3 (by rfl) ⟨336650, by rfl⟩ : syracuseStep 1795469 = 673301) (by norm_num)
theorem B1295777 : Blo 1196415 1295777 := bbase (se 2 (by rfl) ⟨485916, by rfl⟩ : syracuseStep 1295777 = 971833) (by norm_num)
theorem B1795493 : Blo 1196415 1795493 := bbase (se 4 (by rfl) ⟨168327, by rfl⟩ : syracuseStep 1795493 = 336655) (by norm_num)
theorem B4040117 : Blo 1196415 4040117 := bbase (se 5 (by rfl) ⟨189380, by rfl⟩ : syracuseStep 4040117 = 378761) (by norm_num)
theorem B1795517 : Blo 1196415 1795517 := bbase (se 3 (by rfl) ⟨336659, by rfl⟩ : syracuseStep 1795517 = 673319) (by norm_num)
theorem B1795541 : Blo 1196415 1795541 := bbase (se 7 (by rfl) ⟨21041, by rfl⟩ : syracuseStep 1795541 = 42083) (by norm_num)
theorem B1918421 : Blo 1196415 1918421 := bbase (se 7 (by rfl) ⟨22481, by rfl⟩ : syracuseStep 1918421 = 44963) (by norm_num)
theorem B3032549 : Blo 1196415 3032549 := bbase (se 4 (by rfl) ⟨284301, by rfl⟩ : syracuseStep 3032549 = 568603) (by norm_num)
theorem B1795565 : Blo 1196415 1795565 := bbase (se 3 (by rfl) ⟨336668, by rfl⟩ : syracuseStep 1795565 = 673337) (by norm_num)
theorem B3409397 : Blo 1196415 3409397 := bbase (se 5 (by rfl) ⟨159815, by rfl⟩ : syracuseStep 3409397 = 319631) (by norm_num)
theorem B1795589 : Blo 1196415 1795589 := bbase (se 4 (by rfl) ⟨168336, by rfl⟩ : syracuseStep 1795589 = 336673) (by norm_num)
theorem B1795613 : Blo 1196415 1795613 := bbase (se 3 (by rfl) ⟨336677, by rfl⟩ : syracuseStep 1795613 = 673355) (by norm_num)
theorem B1795637 : Blo 1196415 1795637 := bbase (se 5 (by rfl) ⟨84170, by rfl⟩ : syracuseStep 1795637 = 168341) (by norm_num)
theorem B1705541 : Blo 1196415 1705541 := bbase (se 4 (by rfl) ⟨159894, by rfl⟩ : syracuseStep 1705541 = 319789) (by norm_num)
theorem B1795661 : Blo 1196415 1795661 := bbase (se 3 (by rfl) ⟨336686, by rfl⟩ : syracuseStep 1795661 = 673373) (by norm_num)
theorem B1795685 : Blo 1196415 1795685 := bbase (se 4 (by rfl) ⟨168345, by rfl⟩ : syracuseStep 1795685 = 336691) (by norm_num)
theorem B1795709 : Blo 1196415 1795709 := bbase (se 3 (by rfl) ⟨336695, by rfl⟩ : syracuseStep 1795709 = 673391) (by norm_num)
theorem B3237509 : Blo 1196415 3237509 := bbase (se 4 (by rfl) ⟨303516, by rfl⟩ : syracuseStep 3237509 = 607033) (by norm_num)
theorem B1795733 : Blo 1196415 1795733 := bbase (se 6 (by rfl) ⟨42087, by rfl⟩ : syracuseStep 1795733 = 84175) (by norm_num)
theorem B21849749 : Blo 1196415 21849749 := bbase (se 6 (by rfl) ⟨512103, by rfl⟩ : syracuseStep 21849749 = 1024207) (by norm_num)
theorem B3032741 : Blo 1196415 3032741 := bbase (se 4 (by rfl) ⟨284319, by rfl⟩ : syracuseStep 3032741 = 568639) (by norm_num)
theorem B1795757 : Blo 1196415 1795757 := bbase (se 3 (by rfl) ⟨336704, by rfl⟩ : syracuseStep 1795757 = 673409) (by norm_num)
theorem B1795781 : Blo 1196415 1795781 := bbase (se 4 (by rfl) ⟨168354, by rfl⟩ : syracuseStep 1795781 = 336709) (by norm_num)
theorem B1795805 : Blo 1196415 1795805 := bbase (se 3 (by rfl) ⟨336713, by rfl⟩ : syracuseStep 1795805 = 673427) (by norm_num)
theorem B1795829 : Blo 1196415 1795829 := bbase (se 5 (by rfl) ⟨84179, by rfl⟩ : syracuseStep 1795829 = 168359) (by norm_num)
theorem B1795853 : Blo 1196415 1795853 := bbase (se 3 (by rfl) ⟨336722, by rfl⟩ : syracuseStep 1795853 = 673445) (by norm_num)
theorem B9086741 : Blo 1196415 9086741 := bbase (se 6 (by rfl) ⟨212970, by rfl⟩ : syracuseStep 9086741 = 425941) (by norm_num)
theorem B1795877 : Blo 1196415 1795877 := bbase (se 4 (by rfl) ⟨168363, by rfl⟩ : syracuseStep 1795877 = 336727) (by norm_num)
theorem B1795901 : Blo 1196415 1795901 := bbase (se 3 (by rfl) ⟨336731, by rfl⟩ : syracuseStep 1795901 = 673463) (by norm_num)
theorem B2557757 : Blo 1196415 2557757 := bbase (se 3 (by rfl) ⟨479579, by rfl⟩ : syracuseStep 2557757 = 959159) (by norm_num)
theorem B2557765 : Blo 1196415 2557765 := bbase (se 4 (by rfl) ⟨239790, by rfl⟩ : syracuseStep 2557765 = 479581) (by norm_num)
theorem B1214281 : Blo 1196415 1214281 := bbase (se 2 (by rfl) ⟨455355, by rfl⟩ : syracuseStep 1214281 = 910711) (by norm_num)
theorem B5113685 : Blo 1196415 5113685 := bbase (se 9 (by rfl) ⟨14981, by rfl⟩ : syracuseStep 5113685 = 29963) (by norm_num)
theorem B1795925 : Blo 1196415 1795925 := bbase (se 9 (by rfl) ⟨5261, by rfl⟩ : syracuseStep 1795925 = 10523) (by norm_num)
theorem B4040549 : Blo 1196415 4040549 := bbase (se 4 (by rfl) ⟨378801, by rfl⟩ : syracuseStep 4040549 = 757603) (by norm_num)
theorem B1795949 : Blo 1196415 1795949 := bbase (se 3 (by rfl) ⟨336740, by rfl⟩ : syracuseStep 1795949 = 673481) (by norm_num)
theorem B1795973 : Blo 1196415 1795973 := bbase (se 4 (by rfl) ⟨168372, by rfl⟩ : syracuseStep 1795973 = 336745) (by norm_num)
theorem B1795997 : Blo 1196415 1795997 := bbase (se 3 (by rfl) ⟨336749, by rfl⟩ : syracuseStep 1795997 = 673499) (by norm_num)
theorem B1796021 : Blo 1196415 1796021 := bbase (se 5 (by rfl) ⟨84188, by rfl⟩ : syracuseStep 1796021 = 168377) (by norm_num)
theorem B1796045 : Blo 1196415 1796045 := bbase (se 3 (by rfl) ⟨336758, by rfl⟩ : syracuseStep 1796045 = 673517) (by norm_num)
theorem B1796069 : Blo 1196415 1796069 := bbase (se 4 (by rfl) ⟨168381, by rfl⟩ : syracuseStep 1796069 = 336763) (by norm_num)
theorem B4548581 : Blo 1196415 4548581 := bbase (se 4 (by rfl) ⟨426429, by rfl⟩ : syracuseStep 4548581 = 852859) (by norm_num)
theorem B1796093 : Blo 1196415 1796093 := bbase (se 3 (by rfl) ⟨336767, by rfl⟩ : syracuseStep 1796093 = 673535) (by norm_num)
theorem B3033085 : Blo 1196415 3033085 := bbase (se 3 (by rfl) ⟨568703, by rfl⟩ : syracuseStep 3033085 = 1137407) (by norm_num)
theorem B1796117 : Blo 1196415 1796117 := bbase (se 6 (by rfl) ⟨42096, by rfl⟩ : syracuseStep 1796117 = 84193) (by norm_num)
theorem B1796141 : Blo 1196415 1796141 := bbase (se 3 (by rfl) ⟨336776, by rfl⟩ : syracuseStep 1796141 = 673553) (by norm_num)
theorem B3835957 : Blo 1196415 3835957 := bbase (se 5 (by rfl) ⟨179810, by rfl⟩ : syracuseStep 3835957 = 359621) (by norm_num)
theorem B5113925 : Blo 1196415 5113925 := bbase (se 4 (by rfl) ⟨479430, by rfl⟩ : syracuseStep 5113925 = 958861) (by norm_num)
theorem B1796165 : Blo 1196415 1796165 := bbase (se 4 (by rfl) ⟨168390, by rfl⟩ : syracuseStep 1796165 = 336781) (by norm_num)
theorem B1796189 : Blo 1196415 1796189 := bbase (se 3 (by rfl) ⟨336785, by rfl⟩ : syracuseStep 1796189 = 673571) (by norm_num)
theorem B5187685 : Blo 1196415 5187685 := bbase (se 4 (by rfl) ⟨486345, by rfl⟩ : syracuseStep 5187685 = 972691) (by norm_num)
theorem B3033197 : Blo 1196415 3033197 := bbase (se 3 (by rfl) ⟨568724, by rfl⟩ : syracuseStep 3033197 = 1137449) (by norm_num)
theorem B1796213 : Blo 1196415 1796213 := bbase (se 5 (by rfl) ⟨84197, by rfl⟩ : syracuseStep 1796213 = 168395) (by norm_num)
theorem B1796237 : Blo 1196415 1796237 := bbase (se 3 (by rfl) ⟨336794, by rfl⟩ : syracuseStep 1796237 = 673589) (by norm_num)
theorem B2271397 : Blo 1196415 2271397 := bbase (se 4 (by rfl) ⟨212943, by rfl⟩ : syracuseStep 2271397 = 425887) (by norm_num)
theorem B1796261 : Blo 1196415 1796261 := bbase (se 4 (by rfl) ⟨168399, by rfl⟩ : syracuseStep 1796261 = 336799) (by norm_num)
theorem B1820837 : Blo 1196415 1820837 := bbase (se 4 (by rfl) ⟨170703, by rfl⟩ : syracuseStep 1820837 = 341407) (by norm_num)
theorem B1796285 : Blo 1196415 1796285 := bbase (se 3 (by rfl) ⟨336803, by rfl⟩ : syracuseStep 1796285 = 673607) (by norm_num)
theorem B1820861 : Blo 1196415 1820861 := bbase (se 3 (by rfl) ⟨341411, by rfl⟩ : syracuseStep 1820861 = 682823) (by norm_num)
theorem B1796309 : Blo 1196415 1796309 := bbase (se 7 (by rfl) ⟨21050, by rfl⟩ : syracuseStep 1796309 = 42101) (by norm_num)
theorem B2427101 : Blo 1196415 2427101 := bbase (se 3 (by rfl) ⟨455081, by rfl⟩ : syracuseStep 2427101 = 910163) (by norm_num)
theorem B1796333 : Blo 1196415 1796333 := bbase (se 3 (by rfl) ⟨336812, by rfl⟩ : syracuseStep 1796333 = 673625) (by norm_num)
theorem B2156789 : Blo 1196415 2156789 := bbase (se 5 (by rfl) ⟨101099, by rfl⟩ : syracuseStep 2156789 = 202199) (by norm_num)
theorem B1796357 : Blo 1196415 1796357 := bbase (se 4 (by rfl) ⟨168408, by rfl⟩ : syracuseStep 1796357 = 336817) (by norm_num)
theorem B4548869 : Blo 1196415 4548869 := bbase (se 4 (by rfl) ⟨426456, by rfl⟩ : syracuseStep 4548869 = 852913) (by norm_num)
theorem B4040981 : Blo 1196415 4040981 := bbase (se 6 (by rfl) ⟨94710, by rfl⟩ : syracuseStep 4040981 = 189421) (by norm_num)
theorem B1796381 : Blo 1196415 1796381 := bbase (se 3 (by rfl) ⟨336821, by rfl⟩ : syracuseStep 1796381 = 673643) (by norm_num)
theorem B3033389 : Blo 1196415 3033389 := bbase (se 3 (by rfl) ⟨568760, by rfl⟩ : syracuseStep 3033389 = 1137521) (by norm_num)
theorem B1796405 : Blo 1196415 1796405 := bbase (se 5 (by rfl) ⟨84206, by rfl⟩ : syracuseStep 1796405 = 168413) (by norm_num)
theorem B1706293 : Blo 1196415 1706293 := bbase (se 5 (by rfl) ⟨79982, by rfl⟩ : syracuseStep 1706293 = 159965) (by norm_num)
theorem B2271557 : Blo 1196415 2271557 := bbase (se 4 (by rfl) ⟨212958, by rfl⟩ : syracuseStep 2271557 = 425917) (by norm_num)
theorem B1796429 : Blo 1196415 1796429 := bbase (se 3 (by rfl) ⟨336830, by rfl⟩ : syracuseStep 1796429 = 673661) (by norm_num)
theorem B6064469 : Blo 1196415 6064469 := bbase (se 10 (by rfl) ⟨8883, by rfl⟩ : syracuseStep 6064469 = 17767) (by norm_num)
theorem B1845605 : Blo 1196415 1845605 := bbase (se 4 (by rfl) ⟨173025, by rfl⟩ : syracuseStep 1845605 = 346051) (by norm_num)
theorem B1796453 : Blo 1196415 1796453 := bbase (se 4 (by rfl) ⟨168417, by rfl⟩ : syracuseStep 1796453 = 336835) (by norm_num)
theorem B1796477 : Blo 1196415 1796477 := bbase (se 3 (by rfl) ⟨336839, by rfl⟩ : syracuseStep 1796477 = 673679) (by norm_num)
theorem B1796501 : Blo 1196415 1796501 := bbase (se 6 (by rfl) ⟨42105, by rfl⟩ : syracuseStep 1796501 = 84211) (by norm_num)
theorem B1796525 : Blo 1196415 1796525 := bbase (se 3 (by rfl) ⟨336848, by rfl⟩ : syracuseStep 1796525 = 673697) (by norm_num)
theorem B1345981 : Blo 1196415 1345981 := bbase (se 3 (by rfl) ⟨252371, by rfl⟩ : syracuseStep 1345981 = 504743) (by norm_num)
theorem B1796549 : Blo 1196415 1796549 := bbase (se 4 (by rfl) ⟨168426, by rfl⟩ : syracuseStep 1796549 = 336853) (by norm_num)
theorem B2271701 : Blo 1196415 2271701 := bbase (se 7 (by rfl) ⟨26621, by rfl⟩ : syracuseStep 2271701 = 53243) (by norm_num)
theorem B7678421 : Blo 1196415 7678421 := bbase (se 7 (by rfl) ⟨89981, by rfl⟩ : syracuseStep 7678421 = 179963) (by norm_num)
theorem B1796573 : Blo 1196415 1796573 := bbase (se 3 (by rfl) ⟨336857, by rfl⟩ : syracuseStep 1796573 = 673715) (by norm_num)
theorem B1346017 : Blo 1196415 1346017 := bbase (se 2 (by rfl) ⟨504756, by rfl⟩ : syracuseStep 1346017 = 1009513) (by norm_num)
theorem B1796597 : Blo 1196415 1796597 := bbase (se 5 (by rfl) ⟨84215, by rfl⟩ : syracuseStep 1796597 = 168431) (by norm_num)
theorem B1346053 : Blo 1196415 1346053 := bbase (se 4 (by rfl) ⟨126192, by rfl⟩ : syracuseStep 1346053 = 252385) (by norm_num)
theorem B1796621 : Blo 1196415 1796621 := bbase (se 3 (by rfl) ⟨336866, by rfl⟩ : syracuseStep 1796621 = 673733) (by norm_num)
theorem B2157077 : Blo 1196415 2157077 := bbase (se 6 (by rfl) ⟨50556, by rfl⟩ : syracuseStep 2157077 = 101113) (by norm_num)
theorem B1796645 : Blo 1196415 1796645 := bbase (se 4 (by rfl) ⟨168435, by rfl⟩ : syracuseStep 1796645 = 336871) (by norm_num)
theorem B1346089 : Blo 1196415 1346089 := bbase (se 2 (by rfl) ⟨504783, by rfl⟩ : syracuseStep 1346089 = 1009567) (by norm_num)
theorem B1796669 : Blo 1196415 1796669 := bbase (se 3 (by rfl) ⟨336875, by rfl⟩ : syracuseStep 1796669 = 673751) (by norm_num)
theorem B1346125 : Blo 1196415 1346125 := bbase (se 3 (by rfl) ⟨252398, by rfl⟩ : syracuseStep 1346125 = 504797) (by norm_num)
theorem B1796693 : Blo 1196415 1796693 := bbase (se 8 (by rfl) ⟨10527, by rfl⟩ : syracuseStep 1796693 = 21055) (by norm_num)
theorem B1796717 : Blo 1196415 1796717 := bbase (se 3 (by rfl) ⟨336884, by rfl⟩ : syracuseStep 1796717 = 673769) (by norm_num)
theorem B1346161 : Blo 1196415 1346161 := bbase (se 2 (by rfl) ⟨504810, by rfl⟩ : syracuseStep 1346161 = 1009621) (by norm_num)
theorem B1796741 : Blo 1196415 1796741 := bbase (se 4 (by rfl) ⟨168444, by rfl⟩ : syracuseStep 1796741 = 336889) (by norm_num)
theorem B1346197 : Blo 1196415 1346197 := bbase (se 6 (by rfl) ⟨31551, by rfl⟩ : syracuseStep 1346197 = 63103) (by norm_num)
theorem B3410581 : Blo 1196415 3410581 := bbase (se 6 (by rfl) ⟨79935, by rfl⟩ : syracuseStep 3410581 = 159871) (by norm_num)
theorem B1796765 : Blo 1196415 1796765 := bbase (se 3 (by rfl) ⟨336893, by rfl⟩ : syracuseStep 1796765 = 673787) (by norm_num)
theorem B1796789 : Blo 1196415 1796789 := bbase (se 5 (by rfl) ⟨84224, by rfl⟩ : syracuseStep 1796789 = 168449) (by norm_num)
theorem B1346233 : Blo 1196415 1346233 := bbase (se 2 (by rfl) ⟨504837, by rfl⟩ : syracuseStep 1346233 = 1009675) (by norm_num)
theorem B4041413 : Blo 1196415 4041413 := bbase (se 4 (by rfl) ⟨378882, by rfl⟩ : syracuseStep 4041413 = 757765) (by norm_num)
theorem B1796813 : Blo 1196415 1796813 := bbase (se 3 (by rfl) ⟨336902, by rfl⟩ : syracuseStep 1796813 = 673805) (by norm_num)
theorem B1346269 : Blo 1196415 1346269 := bbase (se 3 (by rfl) ⟨252425, by rfl⟩ : syracuseStep 1346269 = 504851) (by norm_num)
theorem B1796837 : Blo 1196415 1796837 := bbase (se 4 (by rfl) ⟨168453, by rfl⟩ : syracuseStep 1796837 = 336907) (by norm_num)
theorem B2271989 : Blo 1196415 2271989 := bbase (se 5 (by rfl) ⟨106499, by rfl⟩ : syracuseStep 2271989 = 212999) (by norm_num)
theorem B2157301 : Blo 1196415 2157301 := bbase (se 5 (by rfl) ⟨101123, by rfl⟩ : syracuseStep 2157301 = 202247) (by norm_num)
theorem B10234613 : Blo 1196415 10234613 := bbase (se 5 (by rfl) ⟨479747, by rfl⟩ : syracuseStep 10234613 = 959495) (by norm_num)
theorem B2460413 : Blo 1196415 2460413 := bbase (se 3 (by rfl) ⟨461327, by rfl⟩ : syracuseStep 2460413 = 922655) (by norm_num)
theorem B1796861 : Blo 1196415 1796861 := bbase (se 3 (by rfl) ⟨336911, by rfl⟩ : syracuseStep 1796861 = 673823) (by norm_num)
theorem B1346305 : Blo 1196415 1346305 := bbase (se 2 (by rfl) ⟨504864, by rfl⟩ : syracuseStep 1346305 = 1009729) (by norm_num)
theorem B1796885 : Blo 1196415 1796885 := bbase (se 6 (by rfl) ⟨42114, by rfl⟩ : syracuseStep 1796885 = 84229) (by norm_num)
theorem B1346341 : Blo 1196415 1346341 := bbase (se 4 (by rfl) ⟨126219, by rfl⟩ : syracuseStep 1346341 = 252439) (by norm_num)
theorem B1796909 : Blo 1196415 1796909 := bbase (se 3 (by rfl) ⟨336920, by rfl⟩ : syracuseStep 1796909 = 673841) (by norm_num)
theorem B3074861 : Blo 1196415 3074861 := bbase (se 3 (by rfl) ⟨576536, by rfl⟩ : syracuseStep 3074861 = 1153073) (by norm_num)
theorem B2157365 : Blo 1196415 2157365 := bbase (se 5 (by rfl) ⟨101126, by rfl⟩ : syracuseStep 2157365 = 202253) (by norm_num)
theorem B3410741 : Blo 1196415 3410741 := bbase (se 5 (by rfl) ⟨159878, by rfl⟩ : syracuseStep 3410741 = 319757) (by norm_num)
theorem B1477441 : Blo 1196415 1477441 := bbase (se 2 (by rfl) ⟨554040, by rfl⟩ : syracuseStep 1477441 = 1108081) (by norm_num)
theorem B1796933 : Blo 1196415 1796933 := bbase (se 4 (by rfl) ⟨168462, by rfl⟩ : syracuseStep 1796933 = 336925) (by norm_num)
theorem B1346377 : Blo 1196415 1346377 := bbase (se 2 (by rfl) ⟨504891, by rfl⟩ : syracuseStep 1346377 = 1009783) (by norm_num)
theorem B1796957 : Blo 1196415 1796957 := bbase (se 3 (by rfl) ⟨336929, by rfl⟩ : syracuseStep 1796957 = 673859) (by norm_num)
theorem B1346413 : Blo 1196415 1346413 := bbase (se 3 (by rfl) ⟨252452, by rfl⟩ : syracuseStep 1346413 = 504905) (by norm_num)
theorem B2804597 : Blo 1196415 2804597 := bbase (se 5 (by rfl) ⟨131465, by rfl⟩ : syracuseStep 2804597 = 262931) (by norm_num)
theorem B1796981 : Blo 1196415 1796981 := bbase (se 5 (by rfl) ⟨84233, by rfl⟩ : syracuseStep 1796981 = 168467) (by norm_num)
theorem B2272141 : Blo 1196415 2272141 := bbase (se 3 (by rfl) ⟨426026, by rfl⟩ : syracuseStep 2272141 = 852053) (by norm_num)
theorem B1797005 : Blo 1196415 1797005 := bbase (se 3 (by rfl) ⟨336938, by rfl⟩ : syracuseStep 1797005 = 673877) (by norm_num)
theorem B1346449 : Blo 1196415 1346449 := bbase (se 2 (by rfl) ⟨504918, by rfl⟩ : syracuseStep 1346449 = 1009837) (by norm_num)
theorem B1797029 : Blo 1196415 1797029 := bbase (se 4 (by rfl) ⟨168471, by rfl⟩ : syracuseStep 1797029 = 336943) (by norm_num)
theorem B2558893 : Blo 1196415 2558893 := bbase (se 3 (by rfl) ⟨479792, by rfl⟩ : syracuseStep 2558893 = 959585) (by norm_num)
theorem B1346485 : Blo 1196415 1346485 := bbase (se 5 (by rfl) ⟨63116, by rfl⟩ : syracuseStep 1346485 = 126233) (by norm_num)
theorem B1797053 : Blo 1196415 1797053 := bbase (se 3 (by rfl) ⟨336947, by rfl⟩ : syracuseStep 1797053 = 673895) (by norm_num)
theorem B1797077 : Blo 1196415 1797077 := bbase (se 7 (by rfl) ⟨21059, by rfl⟩ : syracuseStep 1797077 = 42119) (by norm_num)
theorem B1346521 : Blo 1196415 1346521 := bbase (se 2 (by rfl) ⟨504945, by rfl⟩ : syracuseStep 1346521 = 1009891) (by norm_num)
theorem B2878429 : Blo 1196415 2878429 := bbase (se 3 (by rfl) ⟨539705, by rfl⟩ : syracuseStep 2878429 = 1079411) (by norm_num)
theorem B1797101 : Blo 1196415 1797101 := bbase (se 3 (by rfl) ⟨336956, by rfl⟩ : syracuseStep 1797101 = 673913) (by norm_num)
theorem B1346557 : Blo 1196415 1346557 := bbase (se 3 (by rfl) ⟨252479, by rfl⟩ : syracuseStep 1346557 = 504959) (by norm_num)
theorem B1797125 : Blo 1196415 1797125 := bbase (se 4 (by rfl) ⟨168480, by rfl⟩ : syracuseStep 1797125 = 336961) (by norm_num)
theorem B1797149 : Blo 1196415 1797149 := bbase (se 3 (by rfl) ⟨336965, by rfl⟩ : syracuseStep 1797149 = 673931) (by norm_num)
theorem B1346593 : Blo 1196415 1346593 := bbase (se 2 (by rfl) ⟨504972, by rfl⟩ : syracuseStep 1346593 = 1009945) (by norm_num)
theorem B3410981 : Blo 1196415 3410981 := bbase (se 4 (by rfl) ⟨319779, by rfl⟩ : syracuseStep 3410981 = 639559) (by norm_num)
theorem B1797173 : Blo 1196415 1797173 := bbase (se 5 (by rfl) ⟨84242, by rfl⟩ : syracuseStep 1797173 = 168485) (by norm_num)
theorem B1346629 : Blo 1196415 1346629 := bbase (se 4 (by rfl) ⟨126246, by rfl⟩ : syracuseStep 1346629 = 252493) (by norm_num)
theorem B1797197 : Blo 1196415 1797197 := bbase (se 3 (by rfl) ⟨336974, by rfl⟩ : syracuseStep 1797197 = 673949) (by norm_num)
theorem B1797221 : Blo 1196415 1797221 := bbase (se 4 (by rfl) ⟨168489, by rfl⟩ : syracuseStep 1797221 = 336979) (by norm_num)
theorem B1346665 : Blo 1196415 1346665 := bbase (se 2 (by rfl) ⟨504999, by rfl⟩ : syracuseStep 1346665 = 1009999) (by norm_num)
theorem B4041845 : Blo 1196415 4041845 := bbase (se 5 (by rfl) ⟨189461, by rfl⟩ : syracuseStep 4041845 = 378923) (by norm_num)
theorem B1797245 : Blo 1196415 1797245 := bbase (se 3 (by rfl) ⟨336983, by rfl⟩ : syracuseStep 1797245 = 673967) (by norm_num)
theorem B1346701 : Blo 1196415 1346701 := bbase (se 3 (by rfl) ⟨252506, by rfl⟩ : syracuseStep 1346701 = 505013) (by norm_num)
theorem B1797269 : Blo 1196415 1797269 := bbase (se 6 (by rfl) ⟨42123, by rfl⟩ : syracuseStep 1797269 = 84247) (by norm_num)
theorem B1797293 : Blo 1196415 1797293 := bbase (se 3 (by rfl) ⟨336992, by rfl⟩ : syracuseStep 1797293 = 673985) (by norm_num)
theorem B1346737 : Blo 1196415 1346737 := bbase (se 2 (by rfl) ⟨505026, by rfl⟩ : syracuseStep 1346737 = 1010053) (by norm_num)
theorem B2272445 : Blo 1196415 2272445 := bbase (se 3 (by rfl) ⟨426083, by rfl⟩ : syracuseStep 2272445 = 852167) (by norm_num)
theorem B1797317 : Blo 1196415 1797317 := bbase (se 4 (by rfl) ⟨168498, by rfl⟩ : syracuseStep 1797317 = 336997) (by norm_num)
theorem B1346773 : Blo 1196415 1346773 := bbase (se 7 (by rfl) ⟨15782, by rfl⟩ : syracuseStep 1346773 = 31565) (by norm_num)
theorem B1846493 : Blo 1196415 1846493 := bbase (se 3 (by rfl) ⟨346217, by rfl⟩ : syracuseStep 1846493 = 692435) (by norm_num)
theorem B1797341 : Blo 1196415 1797341 := bbase (se 3 (by rfl) ⟨337001, by rfl⟩ : syracuseStep 1797341 = 674003) (by norm_num)
theorem B3411173 : Blo 1196415 3411173 := bbase (se 4 (by rfl) ⟨319797, by rfl⟩ : syracuseStep 3411173 = 639595) (by norm_num)
theorem B1797365 : Blo 1196415 1797365 := bbase (se 5 (by rfl) ⟨84251, by rfl⟩ : syracuseStep 1797365 = 168503) (by norm_num)
theorem B1346809 : Blo 1196415 1346809 := bbase (se 2 (by rfl) ⟨505053, by rfl⟩ : syracuseStep 1346809 = 1010107) (by norm_num)
theorem B1797389 : Blo 1196415 1797389 := bbase (se 3 (by rfl) ⟨337010, by rfl⟩ : syracuseStep 1797389 = 674021) (by norm_num)
theorem B1346845 : Blo 1196415 1346845 := bbase (se 3 (by rfl) ⟨252533, by rfl⟩ : syracuseStep 1346845 = 505067) (by norm_num)
theorem B1797413 : Blo 1196415 1797413 := bbase (se 4 (by rfl) ⟨168507, by rfl⟩ : syracuseStep 1797413 = 337015) (by norm_num)
theorem B2559269 : Blo 1196415 2559269 := bbase (se 4 (by rfl) ⟨239931, by rfl⟩ : syracuseStep 2559269 = 479863) (by norm_num)
theorem B1797437 : Blo 1196415 1797437 := bbase (se 3 (by rfl) ⟨337019, by rfl⟩ : syracuseStep 1797437 = 674039) (by norm_num)
theorem B1346881 : Blo 1196415 1346881 := bbase (se 2 (by rfl) ⟨505080, by rfl⟩ : syracuseStep 1346881 = 1010161) (by norm_num)
theorem B1797461 : Blo 1196415 1797461 := bbase (se 11 (by rfl) ⟨1316, by rfl⟩ : syracuseStep 1797461 = 2633) (by norm_num)
theorem B1346917 : Blo 1196415 1346917 := bbase (se 4 (by rfl) ⟨126273, by rfl⟩ : syracuseStep 1346917 = 252547) (by norm_num)
theorem B2461037 : Blo 1196415 2461037 := bbase (se 3 (by rfl) ⟨461444, by rfl⟩ : syracuseStep 2461037 = 922889) (by norm_num)
theorem B1797485 : Blo 1196415 1797485 := bbase (se 3 (by rfl) ⟨337028, by rfl⟩ : syracuseStep 1797485 = 674057) (by norm_num)
theorem B1797509 : Blo 1196415 1797509 := bbase (se 4 (by rfl) ⟨168516, by rfl⟩ : syracuseStep 1797509 = 337033) (by norm_num)
theorem B1346953 : Blo 1196415 1346953 := bbase (se 2 (by rfl) ⟨505107, by rfl⟩ : syracuseStep 1346953 = 1010215) (by norm_num)
theorem B1797533 : Blo 1196415 1797533 := bbase (se 3 (by rfl) ⟨337037, by rfl⟩ : syracuseStep 1797533 = 674075) (by norm_num)
theorem B4550053 : Blo 1196415 4550053 := bbase (se 4 (by rfl) ⟨426567, by rfl⟩ : syracuseStep 4550053 = 853135) (by norm_num)
theorem B1346989 : Blo 1196415 1346989 := bbase (se 3 (by rfl) ⟨252560, by rfl⟩ : syracuseStep 1346989 = 505121) (by norm_num)
theorem B1797557 : Blo 1196415 1797557 := bbase (se 5 (by rfl) ⟨84260, by rfl⟩ : syracuseStep 1797557 = 168521) (by norm_num)
theorem B1797581 : Blo 1196415 1797581 := bbase (se 3 (by rfl) ⟨337046, by rfl⟩ : syracuseStep 1797581 = 674093) (by norm_num)
theorem B1347025 : Blo 1196415 1347025 := bbase (se 2 (by rfl) ⟨505134, by rfl⟩ : syracuseStep 1347025 = 1010269) (by norm_num)
theorem B1797605 : Blo 1196415 1797605 := bbase (se 4 (by rfl) ⟨168525, by rfl⟩ : syracuseStep 1797605 = 337051) (by norm_num)
theorem B1347061 : Blo 1196415 1347061 := bbase (se 5 (by rfl) ⟨63143, by rfl⟩ : syracuseStep 1347061 = 126287) (by norm_num)
theorem B4312597 : Blo 1196415 4312597 := bbase (se 6 (by rfl) ⟨101076, by rfl⟩ : syracuseStep 4312597 = 202153) (by norm_num)
theorem B1347097 : Blo 1196415 1347097 := bbase (se 2 (by rfl) ⟨505161, by rfl⟩ : syracuseStep 1347097 = 1010323) (by norm_num)
theorem B4042277 : Blo 1196415 4042277 := bbase (se 4 (by rfl) ⟨378963, by rfl⟩ : syracuseStep 4042277 = 757927) (by norm_num)
theorem B2592317 : Blo 1196415 2592317 := bbase (se 3 (by rfl) ⟨486059, by rfl⟩ : syracuseStep 2592317 = 972119) (by norm_num)
theorem B1347133 : Blo 1196415 1347133 := bbase (se 3 (by rfl) ⟨252587, by rfl⟩ : syracuseStep 1347133 = 505175) (by norm_num)
theorem B1347169 : Blo 1196415 1347169 := bbase (se 2 (by rfl) ⟨505188, by rfl⟩ : syracuseStep 1347169 = 1010377) (by norm_num)
theorem B6065765 : Blo 1196415 6065765 := bbase (se 4 (by rfl) ⟨568665, by rfl⟩ : syracuseStep 6065765 = 1137331) (by norm_num)
theorem B1347205 : Blo 1196415 1347205 := bbase (se 4 (by rfl) ⟨126300, by rfl⟩ : syracuseStep 1347205 = 252601) (by norm_num)
theorem B2018965 : Blo 1196415 2018965 := bbase (se 6 (by rfl) ⟨47319, by rfl⟩ : syracuseStep 2018965 = 94639) (by norm_num)
theorem B1347241 : Blo 1196415 1347241 := bbase (se 2 (by rfl) ⟨505215, by rfl⟩ : syracuseStep 1347241 = 1010431) (by norm_num)
theorem B4312757 : Blo 1196415 4312757 := bbase (se 5 (by rfl) ⟨202160, by rfl⟩ : syracuseStep 4312757 = 404321) (by norm_num)
theorem B1347277 : Blo 1196415 1347277 := bbase (se 3 (by rfl) ⟨252614, by rfl⟩ : syracuseStep 1347277 = 505229) (by norm_num)
theorem B25882325 : Blo 1196415 25882325 := bbase (se 7 (by rfl) ⟨303308, by rfl⟩ : syracuseStep 25882325 = 606617) (by norm_num)
theorem B17256149 : Blo 1196415 17256149 := bbase (se 7 (by rfl) ⟨202220, by rfl⟩ : syracuseStep 17256149 = 404441) (by norm_num)
theorem B2019053 : Blo 1196415 2019053 := bbase (se 3 (by rfl) ⟨378572, by rfl⟩ : syracuseStep 2019053 = 757145) (by norm_num)
theorem B1347313 : Blo 1196415 1347313 := bbase (se 2 (by rfl) ⟨505242, by rfl⟩ : syracuseStep 1347313 = 1010485) (by norm_num)
theorem B1347349 : Blo 1196415 1347349 := bbase (se 6 (by rfl) ⟨31578, by rfl⟩ : syracuseStep 1347349 = 63157) (by norm_num)
theorem B2305837 : Blo 1196415 2305837 := bbase (se 3 (by rfl) ⟨432344, by rfl⟩ : syracuseStep 2305837 = 864689) (by norm_num)
theorem B1347385 : Blo 1196415 1347385 := bbase (se 2 (by rfl) ⟨505269, by rfl⟩ : syracuseStep 1347385 = 1010539) (by norm_num)
theorem B1347421 : Blo 1196415 1347421 := bbase (se 3 (by rfl) ⟨252641, by rfl⟩ : syracuseStep 1347421 = 505283) (by norm_num)
theorem B2019181 : Blo 1196415 2019181 := bbase (se 3 (by rfl) ⟨378596, by rfl⟩ : syracuseStep 2019181 = 757193) (by norm_num)
theorem B1347457 : Blo 1196415 1347457 := bbase (se 2 (by rfl) ⟨505296, by rfl⟩ : syracuseStep 1347457 = 1010593) (by norm_num)
theorem B16396181 : Blo 1196415 16396181 := bbase (se 6 (by rfl) ⟨384285, by rfl⟩ : syracuseStep 16396181 = 768571) (by norm_num)
theorem B1347493 : Blo 1196415 1347493 := bbase (se 4 (by rfl) ⟨126327, by rfl⟩ : syracuseStep 1347493 = 252655) (by norm_num)
theorem B2273197 : Blo 1196415 2273197 := bbase (se 3 (by rfl) ⟨426224, by rfl⟩ : syracuseStep 2273197 = 852449) (by norm_num)
theorem B2019269 : Blo 1196415 2019269 := bbase (se 4 (by rfl) ⟨189306, by rfl⟩ : syracuseStep 2019269 = 378613) (by norm_num)
theorem B1347529 : Blo 1196415 1347529 := bbase (se 2 (by rfl) ⟨505323, by rfl⟩ : syracuseStep 1347529 = 1010647) (by norm_num)
theorem B4042709 : Blo 1196415 4042709 := bbase (se 7 (by rfl) ⟨47375, by rfl⟩ : syracuseStep 4042709 = 94751) (by norm_num)
theorem B1347565 : Blo 1196415 1347565 := bbase (se 3 (by rfl) ⟨252668, by rfl⟩ : syracuseStep 1347565 = 505337) (by norm_num)
theorem B6057989 : Blo 1196415 6057989 := bbase (se 4 (by rfl) ⟨567936, by rfl⟩ : syracuseStep 6057989 = 1135873) (by norm_num)
theorem B1347601 : Blo 1196415 1347601 := bbase (se 2 (by rfl) ⟨505350, by rfl⟩ : syracuseStep 1347601 = 1010701) (by norm_num)
theorem B1347637 : Blo 1196415 1347637 := bbase (se 5 (by rfl) ⟨63170, by rfl⟩ : syracuseStep 1347637 = 126341) (by norm_num)
theorem B2273341 : Blo 1196415 2273341 := bbase (se 3 (by rfl) ⟨426251, by rfl⟩ : syracuseStep 2273341 = 852503) (by norm_num)
theorem B2019397 : Blo 1196415 2019397 := bbase (se 4 (by rfl) ⟨189318, by rfl⟩ : syracuseStep 2019397 = 378637) (by norm_num)
theorem B1347673 : Blo 1196415 1347673 := bbase (se 2 (by rfl) ⟨505377, by rfl⟩ : syracuseStep 1347673 = 1010755) (by norm_num)
theorem B1347709 : Blo 1196415 1347709 := bbase (se 3 (by rfl) ⟨252695, by rfl⟩ : syracuseStep 1347709 = 505391) (by norm_num)
theorem B2019485 : Blo 1196415 2019485 := bbase (se 3 (by rfl) ⟨378653, by rfl⟩ : syracuseStep 2019485 = 757307) (by norm_num)
theorem B1347745 : Blo 1196415 1347745 := bbase (se 2 (by rfl) ⟨505404, by rfl⟩ : syracuseStep 1347745 = 1010809) (by norm_num)
theorem B1437869 : Blo 1196415 1437869 := bbase (se 3 (by rfl) ⟨269600, by rfl⟩ : syracuseStep 1437869 = 539201) (by norm_num)
theorem B1347781 : Blo 1196415 1347781 := bbase (se 4 (by rfl) ⟨126354, by rfl⟩ : syracuseStep 1347781 = 252709) (by norm_num)
theorem B3412165 : Blo 1196415 3412165 := bbase (se 4 (by rfl) ⟨319890, by rfl⟩ : syracuseStep 3412165 = 639781) (by norm_num)
theorem B5836997 : Blo 1196415 5836997 := bbase (se 4 (by rfl) ⟨547218, by rfl⟩ : syracuseStep 5836997 = 1094437) (by norm_num)
theorem B2273501 : Blo 1196415 2273501 := bbase (se 3 (by rfl) ⟨426281, by rfl⟩ : syracuseStep 2273501 = 852563) (by norm_num)
theorem B1347817 : Blo 1196415 1347817 := bbase (se 2 (by rfl) ⟨505431, by rfl⟩ : syracuseStep 1347817 = 1010863) (by norm_num)
theorem B1618165 : Blo 1196415 1618165 := bbase (se 5 (by rfl) ⟨75851, by rfl⟩ : syracuseStep 1618165 = 151703) (by norm_num)
theorem B1347853 : Blo 1196415 1347853 := bbase (se 3 (by rfl) ⟨252722, by rfl⟩ : syracuseStep 1347853 = 505445) (by norm_num)
theorem B2019613 : Blo 1196415 2019613 := bbase (se 3 (by rfl) ⟨378677, by rfl⟩ : syracuseStep 2019613 = 757355) (by norm_num)
theorem B1347889 : Blo 1196415 1347889 := bbase (se 2 (by rfl) ⟨505458, by rfl⟩ : syracuseStep 1347889 = 1010917) (by norm_num)
theorem B7672117 : Blo 1196415 7672117 := bbase (se 5 (by rfl) ⟨359630, by rfl⟩ : syracuseStep 7672117 = 719261) (by norm_num)
theorem B5116213 : Blo 1196415 5116213 := bbase (se 5 (by rfl) ⟨239822, by rfl⟩ : syracuseStep 5116213 = 479645) (by norm_num)
theorem B6476117 : Blo 1196415 6476117 := bbase (se 10 (by rfl) ⟨9486, by rfl⟩ : syracuseStep 6476117 = 18973) (by norm_num)
theorem B1347925 : Blo 1196415 1347925 := bbase (se 10 (by rfl) ⟨1974, by rfl⟩ : syracuseStep 1347925 = 3949) (by norm_num)
theorem B2273645 : Blo 1196415 2273645 := bbase (se 3 (by rfl) ⟨426308, by rfl⟩ : syracuseStep 2273645 = 852617) (by norm_num)
theorem B2019701 : Blo 1196415 2019701 := bbase (se 5 (by rfl) ⟨94673, by rfl⟩ : syracuseStep 2019701 = 189347) (by norm_num)
theorem B1732981 : Blo 1196415 1732981 := bbase (se 5 (by rfl) ⟨81233, by rfl⟩ : syracuseStep 1732981 = 162467) (by norm_num)
theorem B1347961 : Blo 1196415 1347961 := bbase (se 2 (by rfl) ⟨505485, by rfl⟩ : syracuseStep 1347961 = 1010971) (by norm_num)
theorem B4043141 : Blo 1196415 4043141 := bbase (se 4 (by rfl) ⟨379044, by rfl⟩ : syracuseStep 4043141 = 758089) (by norm_num)
theorem B1364369 : Blo 1196415 1364369 := bbase (se 2 (by rfl) ⟨511638, by rfl⟩ : syracuseStep 1364369 = 1023277) (by norm_num)
theorem B1347997 : Blo 1196415 1347997 := bbase (se 3 (by rfl) ⟨252749, by rfl⟩ : syracuseStep 1347997 = 505499) (by norm_num)
theorem B2429365 : Blo 1196415 2429365 := bbase (se 5 (by rfl) ⟨113876, by rfl⟩ : syracuseStep 2429365 = 227753) (by norm_num)
theorem B1348033 : Blo 1196415 1348033 := bbase (se 2 (by rfl) ⟨505512, by rfl⟩ : syracuseStep 1348033 = 1011025) (by norm_num)
theorem B1438177 : Blo 1196415 1438177 := bbase (se 2 (by rfl) ⟨539316, by rfl⟩ : syracuseStep 1438177 = 1078633) (by norm_num)
theorem B1348069 : Blo 1196415 1348069 := bbase (se 4 (by rfl) ⟨126381, by rfl⟩ : syracuseStep 1348069 = 252763) (by norm_num)
theorem B2019829 : Blo 1196415 2019829 := bbase (se 5 (by rfl) ⟨94679, by rfl⟩ : syracuseStep 2019829 = 189359) (by norm_num)
theorem B1348105 : Blo 1196415 1348105 := bbase (se 2 (by rfl) ⟨505539, by rfl⟩ : syracuseStep 1348105 = 1011079) (by norm_num)
theorem B13627925 : Blo 1196415 13627925 := bbase (se 6 (by rfl) ⟨319404, by rfl⟩ : syracuseStep 13627925 = 638809) (by norm_num)
theorem B13824533 : Blo 1196415 13824533 := bbase (se 6 (by rfl) ⟨324012, by rfl⟩ : syracuseStep 13824533 = 648025) (by norm_num)
theorem B1348141 : Blo 1196415 1348141 := bbase (se 3 (by rfl) ⟨252776, by rfl⟩ : syracuseStep 1348141 = 505553) (by norm_num)
theorem B2019917 : Blo 1196415 2019917 := bbase (se 3 (by rfl) ⟨378734, by rfl⟩ : syracuseStep 2019917 = 757469) (by norm_num)
theorem B1348177 : Blo 1196415 1348177 := bbase (se 2 (by rfl) ⟨505566, by rfl⟩ : syracuseStep 1348177 = 1011133) (by norm_num)
theorem B2626141 : Blo 1196415 2626141 := bbase (se 3 (by rfl) ⟨492401, by rfl⟩ : syracuseStep 2626141 = 984803) (by norm_num)
theorem B1348213 : Blo 1196415 1348213 := bbase (se 5 (by rfl) ⟨63197, by rfl⟩ : syracuseStep 1348213 = 126395) (by norm_num)
theorem B2273933 : Blo 1196415 2273933 := bbase (se 3 (by rfl) ⟨426362, by rfl⟩ : syracuseStep 2273933 = 852725) (by norm_num)
theorem B1438393 : Blo 1196415 1438393 := bbase (se 2 (by rfl) ⟨539397, by rfl⟩ : syracuseStep 1438393 = 1078795) (by norm_num)
theorem B2020045 : Blo 1196415 2020045 := bbase (se 3 (by rfl) ⟨378758, by rfl⟩ : syracuseStep 2020045 = 757517) (by norm_num)
theorem B2020133 : Blo 1196415 2020133 := bbase (se 4 (by rfl) ⟨189387, by rfl⟩ : syracuseStep 2020133 = 378775) (by norm_num)
theorem B2274085 : Blo 1196415 2274085 := bbase (se 4 (by rfl) ⟨213195, by rfl⟩ : syracuseStep 2274085 = 426391) (by norm_num)
theorem B4043573 : Blo 1196415 4043573 := bbase (se 5 (by rfl) ⟨189542, by rfl⟩ : syracuseStep 4043573 = 379085) (by norm_num)
theorem B3838853 : Blo 1196415 3838853 := bbase (se 4 (by rfl) ⟨359892, by rfl⟩ : syracuseStep 3838853 = 719785) (by norm_num)
theorem B2691989 : Blo 1196415 2691989 := bbase (se 6 (by rfl) ⟨63093, by rfl⟩ : syracuseStep 2691989 = 126187) (by norm_num)
theorem B2020261 : Blo 1196415 2020261 := bbase (se 4 (by rfl) ⟨189399, by rfl⟩ : syracuseStep 2020261 = 378799) (by norm_num)
theorem B2692061 : Blo 1196415 2692061 := bbase (se 3 (by rfl) ⟨504761, by rfl⟩ : syracuseStep 2692061 = 1009523) (by norm_num)
theorem B2020349 : Blo 1196415 2020349 := bbase (se 3 (by rfl) ⟨378815, by rfl⟩ : syracuseStep 2020349 = 757631) (by norm_num)
theorem B2692133 : Blo 1196415 2692133 := bbase (se 4 (by rfl) ⟨252387, by rfl⟩ : syracuseStep 2692133 = 504775) (by norm_num)
theorem B9335893 : Blo 1196415 9335893 := bbase (se 8 (by rfl) ⟨54702, by rfl⟩ : syracuseStep 9335893 = 109405) (by norm_num)
theorem B2274389 : Blo 1196415 2274389 := bbase (se 8 (by rfl) ⟨13326, by rfl⟩ : syracuseStep 2274389 = 26653) (by norm_num)
theorem B2692205 : Blo 1196415 2692205 := bbase (se 3 (by rfl) ⟨504788, by rfl⟩ : syracuseStep 2692205 = 1009577) (by norm_num)
theorem B2020477 : Blo 1196415 2020477 := bbase (se 3 (by rfl) ⟨378839, by rfl⟩ : syracuseStep 2020477 = 757679) (by norm_num)
theorem B2692277 : Blo 1196415 2692277 := bbase (se 5 (by rfl) ⟨126200, by rfl⟩ : syracuseStep 2692277 = 252401) (by norm_num)
theorem B2020565 : Blo 1196415 2020565 := bbase (se 7 (by rfl) ⟨23678, by rfl⟩ : syracuseStep 2020565 = 47357) (by norm_num)
theorem B4044005 : Blo 1196415 4044005 := bbase (se 4 (by rfl) ⟨379125, by rfl⟩ : syracuseStep 4044005 = 758251) (by norm_num)
theorem B1365241 : Blo 1196415 1365241 := bbase (se 2 (by rfl) ⟨511965, by rfl⟩ : syracuseStep 1365241 = 1023931) (by norm_num)
theorem B2692349 : Blo 1196415 2692349 := bbase (se 3 (by rfl) ⟨504815, by rfl⟩ : syracuseStep 2692349 = 1009631) (by norm_num)
theorem B1438993 : Blo 1196415 1438993 := bbase (se 2 (by rfl) ⟨539622, by rfl⟩ : syracuseStep 1438993 = 1079245) (by norm_num)
theorem B6059285 : Blo 1196415 6059285 := bbase (se 6 (by rfl) ⟨142014, by rfl⟩ : syracuseStep 6059285 = 284029) (by norm_num)
theorem B2692421 : Blo 1196415 2692421 := bbase (se 4 (by rfl) ⟨252414, by rfl⟩ : syracuseStep 2692421 = 504829) (by norm_num)
theorem B2020693 : Blo 1196415 2020693 := bbase (se 15 (by rfl) ⟨92, by rfl⟩ : syracuseStep 2020693 = 185) (by norm_num)
theorem B2692493 : Blo 1196415 2692493 := bbase (se 3 (by rfl) ⟨504842, by rfl⟩ : syracuseStep 2692493 = 1009685) (by norm_num)
theorem B2020781 : Blo 1196415 2020781 := bbase (se 3 (by rfl) ⟨378896, by rfl⟩ : syracuseStep 2020781 = 757793) (by norm_num)
theorem B1578433 : Blo 1196415 1578433 := bbase (se 2 (by rfl) ⟨591912, by rfl⟩ : syracuseStep 1578433 = 1183825) (by norm_num)
theorem B2692565 : Blo 1196415 2692565 := bbase (se 7 (by rfl) ⟨31553, by rfl⟩ : syracuseStep 2692565 = 63107) (by norm_num)
theorem B9713141 : Blo 1196415 9713141 := bbase (se 5 (by rfl) ⟨455303, by rfl⟩ : syracuseStep 9713141 = 910607) (by norm_num)
theorem B2692637 : Blo 1196415 2692637 := bbase (se 3 (by rfl) ⟨504869, by rfl⟩ : syracuseStep 2692637 = 1009739) (by norm_num)
theorem B2020909 : Blo 1196415 2020909 := bbase (se 3 (by rfl) ⟨378920, by rfl⟩ : syracuseStep 2020909 = 757841) (by norm_num)
theorem B11515445 : Blo 1196415 11515445 := bbase (se 5 (by rfl) ⟨539786, by rfl⟩ : syracuseStep 11515445 = 1079573) (by norm_num)
theorem B3028549 : Blo 1196415 3028549 := bbase (se 4 (by rfl) ⟨283926, by rfl⟩ : syracuseStep 3028549 = 567853) (by norm_num)
theorem B2692709 : Blo 1196415 2692709 := bbase (se 4 (by rfl) ⟨252441, by rfl⟩ : syracuseStep 2692709 = 504883) (by norm_num)
theorem B1619581 : Blo 1196415 1619581 := bbase (se 3 (by rfl) ⟨303671, by rfl⟩ : syracuseStep 1619581 = 607343) (by norm_num)
theorem B2020997 : Blo 1196415 2020997 := bbase (se 4 (by rfl) ⟨189468, by rfl⟩ : syracuseStep 2020997 = 378937) (by norm_num)
theorem B5060245 : Blo 1196415 5060245 := bbase (se 6 (by rfl) ⟨118599, by rfl⟩ : syracuseStep 5060245 = 237199) (by norm_num)
theorem B4044437 : Blo 1196415 4044437 := bbase (se 6 (by rfl) ⟨94791, by rfl⟩ : syracuseStep 4044437 = 189583) (by norm_num)
theorem B10237589 : Blo 1196415 10237589 := bbase (se 6 (by rfl) ⟨239943, by rfl⟩ : syracuseStep 10237589 = 479887) (by norm_num)
theorem B2692781 : Blo 1196415 2692781 := bbase (se 3 (by rfl) ⟨504896, by rfl⟩ : syracuseStep 2692781 = 1009793) (by norm_num)
theorem B3028661 : Blo 1196415 3028661 := bbase (se 5 (by rfl) ⟨141968, by rfl⟩ : syracuseStep 3028661 = 283937) (by norm_num)
theorem B2692853 : Blo 1196415 2692853 := bbase (se 5 (by rfl) ⟨126227, by rfl⟩ : syracuseStep 2692853 = 252455) (by norm_num)
theorem B2021125 : Blo 1196415 2021125 := bbase (se 4 (by rfl) ⟨189480, by rfl⟩ : syracuseStep 2021125 = 378961) (by norm_num)
theorem B5117701 : Blo 1196415 5117701 := bbase (se 4 (by rfl) ⟨479784, by rfl⟩ : syracuseStep 5117701 = 959569) (by norm_num)
theorem B5117717 : Blo 1196415 5117717 := bbase (se 6 (by rfl) ⟨119946, by rfl⟩ : syracuseStep 5117717 = 239893) (by norm_num)
theorem B2692925 : Blo 1196415 2692925 := bbase (se 3 (by rfl) ⟨504923, by rfl⟩ : syracuseStep 2692925 = 1009847) (by norm_num)
theorem B2021213 : Blo 1196415 2021213 := bbase (se 3 (by rfl) ⟨378977, by rfl⟩ : syracuseStep 2021213 = 757955) (by norm_num)
theorem B3028853 : Blo 1196415 3028853 := bbase (se 5 (by rfl) ⟨141977, by rfl⟩ : syracuseStep 3028853 = 283955) (by norm_num)
theorem B2692997 : Blo 1196415 2692997 := bbase (se 4 (by rfl) ⟨252468, by rfl⟩ : syracuseStep 2692997 = 504937) (by norm_num)
theorem B12285845 : Blo 1196415 12285845 := bbase (se 6 (by rfl) ⟨287949, by rfl⟩ : syracuseStep 12285845 = 575899) (by norm_num)
theorem B2693069 : Blo 1196415 2693069 := bbase (se 3 (by rfl) ⟨504950, by rfl⟩ : syracuseStep 2693069 = 1009901) (by norm_num)
theorem B2021341 : Blo 1196415 2021341 := bbase (se 3 (by rfl) ⟨379001, by rfl⟩ : syracuseStep 2021341 = 758003) (by norm_num)
theorem B9975797 : Blo 1196415 9975797 := bbase (se 5 (by rfl) ⟨467615, by rfl⟩ : syracuseStep 9975797 = 935231) (by norm_num)
theorem B1366021 : Blo 1196415 1366021 := bbase (se 4 (by rfl) ⟨128064, by rfl⟩ : syracuseStep 1366021 = 256129) (by norm_num)
theorem B2693141 : Blo 1196415 2693141 := bbase (se 6 (by rfl) ⟨63120, by rfl⟩ : syracuseStep 2693141 = 126241) (by norm_num)
theorem B2021429 : Blo 1196415 2021429 := bbase (se 5 (by rfl) ⟨94754, by rfl⟩ : syracuseStep 2021429 = 189509) (by norm_num)
theorem B2693213 : Blo 1196415 2693213 := bbase (se 3 (by rfl) ⟨504977, by rfl⟩ : syracuseStep 2693213 = 1009955) (by norm_num)
theorem B2693285 : Blo 1196415 2693285 := bbase (se 4 (by rfl) ⟨252495, by rfl⟩ : syracuseStep 2693285 = 504991) (by norm_num)
theorem B4544693 : Blo 1196415 4544693 := bbase (se 5 (by rfl) ⟨213032, by rfl⟩ : syracuseStep 4544693 = 426065) (by norm_num)
theorem B2021557 : Blo 1196415 2021557 := bbase (se 5 (by rfl) ⟨94760, by rfl⟩ : syracuseStep 2021557 = 189521) (by norm_num)
theorem B3029197 : Blo 1196415 3029197 := bbase (se 3 (by rfl) ⟨567974, by rfl⟩ : syracuseStep 3029197 = 1135949) (by norm_num)
theorem B9214165 : Blo 1196415 9214165 := bbase (se 7 (by rfl) ⟨107978, by rfl⟩ : syracuseStep 9214165 = 215957) (by norm_num)
theorem B2693357 : Blo 1196415 2693357 := bbase (se 3 (by rfl) ⟨505004, by rfl⟩ : syracuseStep 2693357 = 1010009) (by norm_num)
theorem B2021645 : Blo 1196415 2021645 := bbase (se 3 (by rfl) ⟨379058, by rfl⟩ : syracuseStep 2021645 = 758117) (by norm_num)
theorem B1366313 : Blo 1196415 1366313 := bbase (se 2 (by rfl) ⟨512367, by rfl⟩ : syracuseStep 1366313 = 1024735) (by norm_num)
theorem B2693429 : Blo 1196415 2693429 := bbase (se 5 (by rfl) ⟨126254, by rfl⟩ : syracuseStep 2693429 = 252509) (by norm_num)
theorem B3029309 : Blo 1196415 3029309 := bbase (se 3 (by rfl) ⟨567995, by rfl⟩ : syracuseStep 3029309 = 1135991) (by norm_num)
theorem B4921685 : Blo 1196415 4921685 := bbase (se 10 (by rfl) ⟨7209, by rfl⟩ : syracuseStep 4921685 = 14419) (by norm_num)
theorem B9845077 : Blo 1196415 9845077 := bbase (se 10 (by rfl) ⟨14421, by rfl⟩ : syracuseStep 9845077 = 28843) (by norm_num)
theorem B2693501 : Blo 1196415 2693501 := bbase (se 3 (by rfl) ⟨505031, by rfl⟩ : syracuseStep 2693501 = 1010063) (by norm_num)
theorem B2021773 : Blo 1196415 2021773 := bbase (se 3 (by rfl) ⟨379082, by rfl⟩ : syracuseStep 2021773 = 758165) (by norm_num)
theorem B2693573 : Blo 1196415 2693573 := bbase (se 4 (by rfl) ⟨252522, by rfl⟩ : syracuseStep 2693573 = 505045) (by norm_num)
theorem B4544981 : Blo 1196415 4544981 := bbase (se 7 (by rfl) ⟨53261, by rfl⟩ : syracuseStep 4544981 = 106523) (by norm_num)
theorem B4610533 : Blo 1196415 4610533 := bbase (se 4 (by rfl) ⟨432237, by rfl⟩ : syracuseStep 4610533 = 864475) (by norm_num)
theorem B2021861 : Blo 1196415 2021861 := bbase (se 4 (by rfl) ⟨189549, by rfl⟩ : syracuseStep 2021861 = 379099) (by norm_num)
theorem B3029501 : Blo 1196415 3029501 := bbase (se 3 (by rfl) ⟨568031, by rfl⟩ : syracuseStep 3029501 = 1136063) (by norm_num)
theorem B2693645 : Blo 1196415 2693645 := bbase (se 3 (by rfl) ⟨505058, by rfl⟩ : syracuseStep 2693645 = 1010117) (by norm_num)
theorem B6060581 : Blo 1196415 6060581 := bbase (se 4 (by rfl) ⟨568179, by rfl⟩ : syracuseStep 6060581 = 1136359) (by norm_num)
theorem B2693717 : Blo 1196415 2693717 := bbase (se 8 (by rfl) ⟨15783, by rfl⟩ : syracuseStep 2693717 = 31567) (by norm_num)
theorem B2021989 : Blo 1196415 2021989 := bbase (se 4 (by rfl) ⟨189561, by rfl⟩ : syracuseStep 2021989 = 379123) (by norm_num)
theorem B7666325 : Blo 1196415 7666325 := bbase (se 6 (by rfl) ⟨179679, by rfl⟩ : syracuseStep 7666325 = 359359) (by norm_num)
theorem B2693789 : Blo 1196415 2693789 := bbase (se 3 (by rfl) ⟨505085, by rfl⟩ : syracuseStep 2693789 = 1010171) (by norm_num)
theorem B2022077 : Blo 1196415 2022077 := bbase (se 3 (by rfl) ⟨379139, by rfl⟩ : syracuseStep 2022077 = 758279) (by norm_num)
theorem B2693861 : Blo 1196415 2693861 := bbase (se 4 (by rfl) ⟨252549, by rfl⟩ : syracuseStep 2693861 = 505099) (by norm_num)
theorem B2693933 : Blo 1196415 2693933 := bbase (se 3 (by rfl) ⟨505112, by rfl⟩ : syracuseStep 2693933 = 1010225) (by norm_num)
theorem B2022205 : Blo 1196415 2022205 := bbase (se 3 (by rfl) ⟨379163, by rfl⟩ : syracuseStep 2022205 = 758327) (by norm_num)
theorem B1514305 : Blo 1196415 1514305 := bbase (se 2 (by rfl) ⟨567864, by rfl⟩ : syracuseStep 1514305 = 1135729) (by norm_num)
theorem B5749589 : Blo 1196415 5749589 := bbase (se 9 (by rfl) ⟨16844, by rfl⟩ : syracuseStep 5749589 = 33689) (by norm_num)
theorem B3029845 : Blo 1196415 3029845 := bbase (se 9 (by rfl) ⟨8876, by rfl⟩ : syracuseStep 3029845 = 17753) (by norm_num)
theorem B13130581 : Blo 1196415 13130581 := bbase (se 9 (by rfl) ⟨38468, by rfl⟩ : syracuseStep 13130581 = 76937) (by norm_num)
theorem B2694005 : Blo 1196415 2694005 := bbase (se 5 (by rfl) ⟨126281, by rfl⟩ : syracuseStep 2694005 = 252563) (by norm_num)
theorem B2022293 : Blo 1196415 2022293 := bbase (se 6 (by rfl) ⟨47397, by rfl⟩ : syracuseStep 2022293 = 94795) (by norm_num)
theorem B2694077 : Blo 1196415 2694077 := bbase (se 3 (by rfl) ⟨505139, by rfl⟩ : syracuseStep 2694077 = 1010279) (by norm_num)
theorem B3029957 : Blo 1196415 3029957 := bbase (se 4 (by rfl) ⟨284058, by rfl⟩ : syracuseStep 3029957 = 568117) (by norm_num)
theorem B5757893 : Blo 1196415 5757893 := bbase (se 4 (by rfl) ⟨539802, by rfl⟩ : syracuseStep 5757893 = 1079605) (by norm_num)
theorem B1514477 : Blo 1196415 1514477 := bbase (se 3 (by rfl) ⟨283964, by rfl⟩ : syracuseStep 1514477 = 567929) (by norm_num)
theorem B3070973 : Blo 1196415 3070973 := bbase (se 3 (by rfl) ⟨575807, by rfl⟩ : syracuseStep 3070973 = 1151615) (by norm_num)
theorem B2694149 : Blo 1196415 2694149 := bbase (se 4 (by rfl) ⟨252576, by rfl⟩ : syracuseStep 2694149 = 505153) (by norm_num)
theorem B1514533 : Blo 1196415 1514533 := bbase (se 4 (by rfl) ⟨141987, by rfl⟩ : syracuseStep 1514533 = 283975) (by norm_num)
theorem B2694221 : Blo 1196415 2694221 := bbase (se 3 (by rfl) ⟨505166, by rfl⟩ : syracuseStep 2694221 = 1010333) (by norm_num)
theorem B1514629 : Blo 1196415 1514629 := bbase (se 4 (by rfl) ⟨141996, by rfl⟩ : syracuseStep 1514629 = 283993) (by norm_num)
theorem B3030149 : Blo 1196415 3030149 := bbase (se 4 (by rfl) ⟨284076, by rfl⟩ : syracuseStep 3030149 = 568153) (by norm_num)
theorem B2694293 : Blo 1196415 2694293 := bbase (se 6 (by rfl) ⟨63147, by rfl⟩ : syracuseStep 2694293 = 126295) (by norm_num)
theorem B2694365 : Blo 1196415 2694365 := bbase (se 3 (by rfl) ⟨505193, by rfl⟩ : syracuseStep 2694365 = 1010387) (by norm_num)
theorem B2694437 : Blo 1196415 2694437 := bbase (se 4 (by rfl) ⟨252603, by rfl⟩ : syracuseStep 2694437 = 505207) (by norm_num)
theorem B1514801 : Blo 1196415 1514801 := bbase (se 2 (by rfl) ⟨568050, by rfl⟩ : syracuseStep 1514801 = 1136101) (by norm_num)
theorem B4037957 : Blo 1196415 4037957 := bbase (se 4 (by rfl) ⟨378558, by rfl⟩ : syracuseStep 4037957 = 757117) (by norm_num)
theorem B3833189 : Blo 1196415 3833189 := bbase (se 4 (by rfl) ⟨359361, by rfl⟩ : syracuseStep 3833189 = 718723) (by norm_num)
theorem B1514857 : Blo 1196415 1514857 := bbase (se 2 (by rfl) ⟨568071, by rfl⟩ : syracuseStep 1514857 = 1136143) (by norm_num)
theorem B2694509 : Blo 1196415 2694509 := bbase (se 3 (by rfl) ⟨505220, by rfl⟩ : syracuseStep 2694509 = 1010441) (by norm_num)
theorem B2694581 : Blo 1196415 2694581 := bbase (se 5 (by rfl) ⟨126308, by rfl⟩ : syracuseStep 2694581 = 252617) (by norm_num)
theorem B6823349 : Blo 1196415 6823349 := bbase (se 5 (by rfl) ⟨319844, by rfl⟩ : syracuseStep 6823349 = 639689) (by norm_num)
theorem B1514953 : Blo 1196415 1514953 := bbase (se 2 (by rfl) ⟨568107, by rfl⟩ : syracuseStep 1514953 = 1136215) (by norm_num)
theorem B3030493 : Blo 1196415 3030493 := bbase (se 3 (by rfl) ⟨568217, by rfl⟩ : syracuseStep 3030493 = 1136435) (by norm_num)
theorem B4857317 : Blo 1196415 4857317 := bbase (se 4 (by rfl) ⟨455373, by rfl⟩ : syracuseStep 4857317 = 910747) (by norm_num)
theorem B2694653 : Blo 1196415 2694653 := bbase (se 3 (by rfl) ⟨505247, by rfl⟩ : syracuseStep 2694653 = 1010495) (by norm_num)
theorem B6815285 : Blo 1196415 6815285 := bbase (se 5 (by rfl) ⟨319466, by rfl⟩ : syracuseStep 6815285 = 638933) (by norm_num)
theorem B2694725 : Blo 1196415 2694725 := bbase (se 4 (by rfl) ⟨252630, by rfl⟩ : syracuseStep 2694725 = 505261) (by norm_num)
theorem B3030605 : Blo 1196415 3030605 := bbase (se 3 (by rfl) ⟨568238, by rfl⟩ : syracuseStep 3030605 = 1136477) (by norm_num)
theorem B1515125 : Blo 1196415 1515125 := bbase (se 5 (by rfl) ⟨71021, by rfl⟩ : syracuseStep 1515125 = 142043) (by norm_num)
theorem B4546165 : Blo 1196415 4546165 := bbase (se 5 (by rfl) ⟨213101, by rfl⟩ : syracuseStep 4546165 = 426203) (by norm_num)
theorem B2694797 : Blo 1196415 2694797 := bbase (se 3 (by rfl) ⟨505274, by rfl⟩ : syracuseStep 2694797 = 1010549) (by norm_num)
theorem B1515181 : Blo 1196415 1515181 := bbase (se 3 (by rfl) ⟨284096, by rfl⟩ : syracuseStep 1515181 = 568193) (by norm_num)
theorem B1703605 : Blo 1196415 1703605 := bbase (se 5 (by rfl) ⟨79856, by rfl⟩ : syracuseStep 1703605 = 159713) (by norm_num)
theorem B5463749 : Blo 1196415 5463749 := bbase (se 4 (by rfl) ⟨512226, by rfl⟩ : syracuseStep 5463749 = 1024453) (by norm_num)
theorem B2694869 : Blo 1196415 2694869 := bbase (se 7 (by rfl) ⟨31580, by rfl⟩ : syracuseStep 2694869 = 63161) (by norm_num)
theorem B3890917 : Blo 1196415 3890917 := bbase (se 4 (by rfl) ⟨364773, by rfl⟩ : syracuseStep 3890917 = 729547) (by norm_num)
theorem B4038389 : Blo 1196415 4038389 := bbase (se 5 (by rfl) ⟨189299, by rfl⟩ : syracuseStep 4038389 = 378599) (by norm_num)
theorem B1515277 : Blo 1196415 1515277 := bbase (se 3 (by rfl) ⟨284114, by rfl⟩ : syracuseStep 1515277 = 568229) (by norm_num)
theorem B3030797 : Blo 1196415 3030797 := bbase (se 3 (by rfl) ⟨568274, by rfl⟩ : syracuseStep 3030797 = 1136549) (by norm_num)
theorem B2694941 : Blo 1196415 2694941 := bbase (se 3 (by rfl) ⟨505301, by rfl⟩ : syracuseStep 2694941 = 1010603) (by norm_num)
theorem B8625973 : Blo 1196415 8625973 := bbase (se 5 (by rfl) ⟨404342, by rfl⟩ : syracuseStep 8625973 = 808685) (by norm_num)
theorem B6061877 : Blo 1196415 6061877 := bbase (se 5 (by rfl) ⟨284150, by rfl⟩ : syracuseStep 6061877 = 568301) (by norm_num)
theorem B1277785 : Blo 1196415 1277785 := bbase (se 2 (by rfl) ⟨479169, by rfl⟩ : syracuseStep 1277785 = 958339) (by norm_num)
theorem B1277789 : Blo 1196415 1277789 := bbase (se 3 (by rfl) ⟨239585, by rfl⟩ : syracuseStep 1277789 = 479171) (by norm_num)
theorem B2555749 : Blo 1196415 2555749 := bbase (se 4 (by rfl) ⟨239601, by rfl⟩ : syracuseStep 2555749 = 479203) (by norm_num)
theorem B2695013 : Blo 1196415 2695013 := bbase (se 4 (by rfl) ⟨252657, by rfl⟩ : syracuseStep 2695013 = 505315) (by norm_num)
theorem B4546469 : Blo 1196415 4546469 := bbase (se 4 (by rfl) ⟨426231, by rfl⟩ : syracuseStep 4546469 = 852463) (by norm_num)
theorem B2695085 : Blo 1196415 2695085 := bbase (se 3 (by rfl) ⟨505328, by rfl⟩ : syracuseStep 2695085 = 1010657) (by norm_num)
theorem B1515449 : Blo 1196415 1515449 := bbase (se 2 (by rfl) ⟨568293, by rfl⟩ : syracuseStep 1515449 = 1136587) (by norm_num)
theorem B2875333 : Blo 1196415 2875333 := bbase (se 4 (by rfl) ⟨269562, by rfl⟩ : syracuseStep 2875333 = 539125) (by norm_num)
theorem B2555869 : Blo 1196415 2555869 := bbase (se 3 (by rfl) ⟨479225, by rfl⟩ : syracuseStep 2555869 = 958451) (by norm_num)
theorem B1515505 : Blo 1196415 1515505 := bbase (se 2 (by rfl) ⟨568314, by rfl⟩ : syracuseStep 1515505 = 1136629) (by norm_num)
theorem B2695157 : Blo 1196415 2695157 := bbase (se 5 (by rfl) ⟨126335, by rfl⟩ : syracuseStep 2695157 = 252671) (by norm_num)
theorem B4038659 : Blo 1196415 4038659 := bstep (se 1 (by rfl) ⟨3028994, by rfl⟩ : syracuseStep 4038659 = 6057989) B6057989
theorem B3407939 : Blo 1196415 3407939 := bstep (se 1 (by rfl) ⟨2555954, by rfl⟩ : syracuseStep 3407939 = 5111909) B5111909
theorem B4546637 : Blo 1196415 4546637 := bstep (se 3 (by rfl) ⟨852494, by rfl⟩ : syracuseStep 4546637 = 1704989) B1704989
theorem B3031121 : Blo 1196415 3031121 := bstep (se 2 (by rfl) ⟨1136670, by rfl⟩ : syracuseStep 3031121 = 2273341) B2273341
theorem B3891331 : Blo 1196415 3891331 := bstep (se 1 (by rfl) ⟨2918498, by rfl⟩ : syracuseStep 3891331 = 5836997) B5836997
theorem B2556049 : Blo 1196415 2556049 := bstep (se 2 (by rfl) ⟨958518, by rfl⟩ : syracuseStep 2556049 = 1917037) B1917037
theorem B1704083 : Blo 1196415 1704083 := bstep (se 1 (by rfl) ⟨1278062, by rfl⟩ : syracuseStep 1704083 = 2556125) B2556125
theorem B1515667 : Blo 1196415 1515667 := bstep (se 1 (by rfl) ⟨1136750, by rfl⟩ : syracuseStep 1515667 = 2273501) B2273501
theorem B2695409 : Blo 1196415 2695409 := bstep (se 2 (by rfl) ⟨1010778, by rfl⟩ : syracuseStep 2695409 = 2021557) B2021557
theorem B1515763 : Blo 1196415 1515763 := bstep (se 1 (by rfl) ⟨1136822, by rfl⟩ : syracuseStep 1515763 = 2273645) B2273645
theorem B2695427 : Blo 1196415 2695427 := bstep (se 1 (by rfl) ⟨2021570, by rfl⟩ : syracuseStep 2695427 = 4043141) B4043141
theorem B4038929 : Blo 1196415 4038929 := bstep (se 2 (by rfl) ⟨1514598, by rfl⟩ : syracuseStep 4038929 = 3029197) B3029197
theorem B7668017 : Blo 1196415 7668017 := bstep (se 2 (by rfl) ⟨2875506, by rfl⟩ : syracuseStep 7668017 = 5751013) B5751013
theorem B9085283 : Blo 1196415 9085283 := bstep (se 1 (by rfl) ⟨6813962, by rfl⟩ : syracuseStep 9085283 = 13627925) B13627925
theorem B7668067 : Blo 1196415 7668067 := bstep (se 1 (by rfl) ⟨5751050, by rfl⟩ : syracuseStep 7668067 = 11502101) B11502101
theorem B9216355 : Blo 1196415 9216355 := bstep (se 1 (by rfl) ⟨6912266, by rfl⟩ : syracuseStep 9216355 = 13824533) B13824533
theorem B1917299 : Blo 1196415 1917299 := bstep (se 1 (by rfl) ⟨1437974, by rfl⟩ : syracuseStep 1917299 = 2875949) B2875949
theorem B1196419 : Blo 1196415 1196419 := bstep (se 1 (by rfl) ⟨897314, by rfl⟩ : syracuseStep 1196419 = 1794629) B1794629
theorem B1196435 : Blo 1196415 1196435 := bstep (se 1 (by rfl) ⟨897326, by rfl⟩ : syracuseStep 1196435 = 1794653) B1794653
theorem B1196451 : Blo 1196415 1196451 := bstep (se 1 (by rfl) ⟨897338, by rfl⟩ : syracuseStep 1196451 = 1794677) B1794677
theorem B1196467 : Blo 1196415 1196467 := bstep (se 1 (by rfl) ⟨897350, by rfl⟩ : syracuseStep 1196467 = 1794701) B1794701
theorem B1196483 : Blo 1196415 1196483 := bstep (se 1 (by rfl) ⟨897362, by rfl⟩ : syracuseStep 1196483 = 1794725) B1794725
theorem B3834317 : Blo 1196415 3834317 := bstep (se 3 (by rfl) ⟨718934, by rfl⟩ : syracuseStep 3834317 = 1437869) B1437869
theorem B1196499 : Blo 1196415 1196499 := bstep (se 1 (by rfl) ⟨897374, by rfl⟩ : syracuseStep 1196499 = 1794749) B1794749
theorem B1196515 : Blo 1196415 1196515 := bstep (se 1 (by rfl) ⟨897386, by rfl⟩ : syracuseStep 1196515 = 1794773) B1794773
theorem B1196531 : Blo 1196415 1196531 := bstep (se 1 (by rfl) ⟨897398, by rfl⟩ : syracuseStep 1196531 = 1794797) B1794797
theorem B1917427 : Blo 1196415 1917427 := bstep (se 1 (by rfl) ⟨1438070, by rfl⟩ : syracuseStep 1917427 = 2876141) B2876141
theorem B1196547 : Blo 1196415 1196547 := bstep (se 1 (by rfl) ⟨897410, by rfl⟩ : syracuseStep 1196547 = 1794821) B1794821
theorem B2695697 : Blo 1196415 2695697 := bstep (se 2 (by rfl) ⟨1010886, by rfl⟩ : syracuseStep 2695697 = 2021773) B2021773
theorem B1196563 : Blo 1196415 1196563 := bstep (se 1 (by rfl) ⟨897422, by rfl⟩ : syracuseStep 1196563 = 1794845) B1794845
theorem B1196579 : Blo 1196415 1196579 := bstep (se 1 (by rfl) ⟨897434, by rfl⟩ : syracuseStep 1196579 = 1794869) B1794869
theorem B2695715 : Blo 1196415 2695715 := bstep (se 1 (by rfl) ⟨2021786, by rfl⟩ : syracuseStep 2695715 = 4043573) B4043573
theorem B1196595 : Blo 1196415 1196595 := bstep (se 1 (by rfl) ⟨897446, by rfl⟩ : syracuseStep 1196595 = 1794893) B1794893
theorem B1196611 : Blo 1196415 1196611 := bstep (se 1 (by rfl) ⟨897458, by rfl⟩ : syracuseStep 1196611 = 1794917) B1794917
theorem B1794641 : Blo 1196415 1794641 := bstep (se 2 (by rfl) ⟨672990, by rfl⟩ : syracuseStep 1794641 = 1345981) B1345981
theorem B1196627 : Blo 1196415 1196627 := bstep (se 1 (by rfl) ⟨897470, by rfl⟩ : syracuseStep 1196627 = 1794941) B1794941
theorem B1794659 : Blo 1196415 1794659 := bstep (se 1 (by rfl) ⟨1345994, by rfl⟩ : syracuseStep 1794659 = 2691989) B2691989
theorem B1196643 : Blo 1196415 1196643 := bstep (se 1 (by rfl) ⟨897482, by rfl⟩ : syracuseStep 1196643 = 1794965) B1794965
theorem B1196659 : Blo 1196415 1196659 := bstep (se 1 (by rfl) ⟨897494, by rfl⟩ : syracuseStep 1196659 = 1794989) B1794989
theorem B1794689 : Blo 1196415 1794689 := bstep (se 2 (by rfl) ⟨673008, by rfl⟩ : syracuseStep 1794689 = 1346017) B1346017
theorem B1917569 : Blo 1196415 1917569 := bstep (se 2 (by rfl) ⟨719088, by rfl⟩ : syracuseStep 1917569 = 1438177) B1438177
theorem B1196675 : Blo 1196415 1196675 := bstep (se 1 (by rfl) ⟨897506, by rfl⟩ : syracuseStep 1196675 = 1795013) B1795013
theorem B1794707 : Blo 1196415 1794707 := bstep (se 1 (by rfl) ⟨1346030, by rfl⟩ : syracuseStep 1794707 = 2692061) B2692061
theorem B1196691 : Blo 1196415 1196691 := bstep (se 1 (by rfl) ⟨897518, by rfl⟩ : syracuseStep 1196691 = 1795037) B1795037
theorem B1196707 : Blo 1196415 1196707 := bstep (se 1 (by rfl) ⟨897530, by rfl⟩ : syracuseStep 1196707 = 1795061) B1795061
theorem B1794737 : Blo 1196415 1794737 := bstep (se 2 (by rfl) ⟨673026, by rfl⟩ : syracuseStep 1794737 = 1346053) B1346053
theorem B1196723 : Blo 1196415 1196723 := bstep (se 1 (by rfl) ⟨897542, by rfl⟩ : syracuseStep 1196723 = 1795085) B1795085
theorem B1794755 : Blo 1196415 1794755 := bstep (se 1 (by rfl) ⟨1346066, by rfl⟩ : syracuseStep 1794755 = 2692133) B2692133
theorem B1196739 : Blo 1196415 1196739 := bstep (se 1 (by rfl) ⟨897554, by rfl⟩ : syracuseStep 1196739 = 1795109) B1795109
theorem B1196755 : Blo 1196415 1196755 := bstep (se 1 (by rfl) ⟨897566, by rfl⟩ : syracuseStep 1196755 = 1795133) B1795133
theorem B1794785 : Blo 1196415 1794785 := bstep (se 2 (by rfl) ⟨673044, by rfl⟩ : syracuseStep 1794785 = 1346089) B1346089
theorem B1196771 : Blo 1196415 1196771 := bstep (se 1 (by rfl) ⟨897578, by rfl⟩ : syracuseStep 1196771 = 1795157) B1795157
theorem B1516259 : Blo 1196415 1516259 := bstep (se 1 (by rfl) ⟨1137194, by rfl⟩ : syracuseStep 1516259 = 2274389) B2274389
theorem B1794803 : Blo 1196415 1794803 := bstep (se 1 (by rfl) ⟨1346102, by rfl⟩ : syracuseStep 1794803 = 2692205) B2692205
theorem B1196787 : Blo 1196415 1196787 := bstep (se 1 (by rfl) ⟨897590, by rfl⟩ : syracuseStep 1196787 = 1795181) B1795181
theorem B1196803 : Blo 1196415 1196803 := bstep (se 1 (by rfl) ⟨897602, by rfl⟩ : syracuseStep 1196803 = 1795205) B1795205
theorem B1794833 : Blo 1196415 1794833 := bstep (se 2 (by rfl) ⟨673062, by rfl⟩ : syracuseStep 1794833 = 1346125) B1346125
theorem B1704721 : Blo 1196415 1704721 := bstep (se 2 (by rfl) ⟨639270, by rfl⟩ : syracuseStep 1704721 = 1278541) B1278541
theorem B1196819 : Blo 1196415 1196819 := bstep (se 1 (by rfl) ⟨897614, by rfl⟩ : syracuseStep 1196819 = 1795229) B1795229
theorem B1639201 : Blo 1196415 1639201 := bstep (se 2 (by rfl) ⟨614700, by rfl⟩ : syracuseStep 1639201 = 1229401) B1229401
theorem B1794851 : Blo 1196415 1794851 := bstep (se 1 (by rfl) ⟨1346138, by rfl⟩ : syracuseStep 1794851 = 2692277) B2692277
theorem B1196835 : Blo 1196415 1196835 := bstep (se 1 (by rfl) ⟨897626, by rfl⟩ : syracuseStep 1196835 = 1795253) B1795253
theorem B4039469 : Blo 1196415 4039469 := bstep (se 3 (by rfl) ⟨757400, by rfl⟩ : syracuseStep 4039469 = 1514801) B1514801
theorem B2695985 : Blo 1196415 2695985 := bstep (se 2 (by rfl) ⟨1010994, by rfl⟩ : syracuseStep 2695985 = 2021989) B2021989
theorem B1196851 : Blo 1196415 1196851 := bstep (se 1 (by rfl) ⟨897638, by rfl⟩ : syracuseStep 1196851 = 1795277) B1795277
theorem B1794881 : Blo 1196415 1794881 := bstep (se 2 (by rfl) ⟨673080, by rfl⟩ : syracuseStep 1794881 = 1346161) B1346161
theorem B1196867 : Blo 1196415 1196867 := bstep (se 1 (by rfl) ⟨897650, by rfl⟩ : syracuseStep 1196867 = 1795301) B1795301
theorem B2696003 : Blo 1196415 2696003 := bstep (se 1 (by rfl) ⟨2022002, by rfl⟩ : syracuseStep 2696003 = 4044005) B4044005
theorem B1794899 : Blo 1196415 1794899 := bstep (se 1 (by rfl) ⟨1346174, by rfl⟩ : syracuseStep 1794899 = 2692349) B2692349
theorem B1196883 : Blo 1196415 1196883 := bstep (se 1 (by rfl) ⟨897662, by rfl⟩ : syracuseStep 1196883 = 1795325) B1795325
theorem B4039523 : Blo 1196415 4039523 := bstep (se 1 (by rfl) ⟨3029642, by rfl⟩ : syracuseStep 4039523 = 6059285) B6059285
theorem B1196899 : Blo 1196415 1196899 := bstep (se 1 (by rfl) ⟨897674, by rfl⟩ : syracuseStep 1196899 = 1795349) B1795349
theorem B1794929 : Blo 1196415 1794929 := bstep (se 2 (by rfl) ⟨673098, by rfl⟩ : syracuseStep 1794929 = 1346197) B1346197
theorem B4547441 : Blo 1196415 4547441 := bstep (se 2 (by rfl) ⟨1705290, by rfl⟩ : syracuseStep 4547441 = 3410581) B3410581
theorem B1196915 : Blo 1196415 1196915 := bstep (se 1 (by rfl) ⟨897686, by rfl⟩ : syracuseStep 1196915 = 1795373) B1795373
theorem B1794947 : Blo 1196415 1794947 := bstep (se 1 (by rfl) ⟨1346210, by rfl⟩ : syracuseStep 1794947 = 2692421) B2692421
theorem B1196931 : Blo 1196415 1196931 := bstep (se 1 (by rfl) ⟨897698, by rfl⟩ : syracuseStep 1196931 = 1795397) B1795397
theorem B1704835 : Blo 1196415 1704835 := bstep (se 1 (by rfl) ⟨1278626, by rfl⟩ : syracuseStep 1704835 = 2557253) B2557253
theorem B17269645 : Blo 1196415 17269645 := bstep (se 3 (by rfl) ⟨3238058, by rfl⟩ : syracuseStep 17269645 = 6476117) B6476117
theorem B1196947 : Blo 1196415 1196947 := bstep (se 1 (by rfl) ⟨897710, by rfl⟩ : syracuseStep 1196947 = 1795421) B1795421
theorem B1794977 : Blo 1196415 1794977 := bstep (se 2 (by rfl) ⟨673116, by rfl⟩ : syracuseStep 1794977 = 1346233) B1346233
theorem B1917857 : Blo 1196415 1917857 := bstep (se 2 (by rfl) ⟨719196, by rfl⟩ : syracuseStep 1917857 = 1438393) B1438393
theorem B1196963 : Blo 1196415 1196963 := bstep (se 1 (by rfl) ⟨897722, by rfl⟩ : syracuseStep 1196963 = 1795445) B1795445
theorem B6063011 : Blo 1196415 6063011 := bstep (se 1 (by rfl) ⟨4547258, by rfl⟩ : syracuseStep 6063011 = 9094517) B9094517
theorem B1794995 : Blo 1196415 1794995 := bstep (se 1 (by rfl) ⟨1346246, by rfl⟩ : syracuseStep 1794995 = 2692493) B2692493
theorem B1196979 : Blo 1196415 1196979 := bstep (se 1 (by rfl) ⟨897734, by rfl⟩ : syracuseStep 1196979 = 1795469) B1795469
theorem B1196995 : Blo 1196415 1196995 := bstep (se 1 (by rfl) ⟨897746, by rfl⟩ : syracuseStep 1196995 = 1795493) B1795493
theorem B6562765 : Blo 1196415 6562765 := bstep (se 3 (by rfl) ⟨1230518, by rfl⟩ : syracuseStep 6562765 = 2461037) B2461037
theorem B1795025 : Blo 1196415 1795025 := bstep (se 2 (by rfl) ⟨673134, by rfl⟩ : syracuseStep 1795025 = 1346269) B1346269
theorem B1197011 : Blo 1196415 1197011 := bstep (se 1 (by rfl) ⟨897758, by rfl⟩ : syracuseStep 1197011 = 1795517) B1795517
theorem B1795043 : Blo 1196415 1795043 := bstep (se 1 (by rfl) ⟨1346282, by rfl⟩ : syracuseStep 1795043 = 2692565) B2692565
theorem B1197027 : Blo 1196415 1197027 := bstep (se 1 (by rfl) ⟨897770, by rfl⟩ : syracuseStep 1197027 = 1795541) B1795541
theorem B1278947 : Blo 1196415 1278947 := bstep (se 1 (by rfl) ⟨959210, by rfl⟩ : syracuseStep 1278947 = 1918421) B1918421
theorem B2876401 : Blo 1196415 2876401 := bstep (se 2 (by rfl) ⟨1078650, by rfl⟩ : syracuseStep 2876401 = 2157301) B2157301
theorem B1197043 : Blo 1196415 1197043 := bstep (se 1 (by rfl) ⟨897782, by rfl⟩ : syracuseStep 1197043 = 1795565) B1795565
theorem B1795073 : Blo 1196415 1795073 := bstep (se 2 (by rfl) ⟨673152, by rfl⟩ : syracuseStep 1795073 = 1346305) B1346305
theorem B1197059 : Blo 1196415 1197059 := bstep (se 1 (by rfl) ⟨897794, by rfl⟩ : syracuseStep 1197059 = 1795589) B1795589
theorem B1795091 : Blo 1196415 1795091 := bstep (se 1 (by rfl) ⟨1346318, by rfl⟩ : syracuseStep 1795091 = 2692637) B2692637
theorem B1197075 : Blo 1196415 1197075 := bstep (se 1 (by rfl) ⟨897806, by rfl⟩ : syracuseStep 1197075 = 1795613) B1795613
theorem B1197091 : Blo 1196415 1197091 := bstep (se 1 (by rfl) ⟨897818, by rfl⟩ : syracuseStep 1197091 = 1795637) B1795637
theorem B7676963 : Blo 1196415 7676963 := bstep (se 1 (by rfl) ⟨5757722, by rfl⟩ : syracuseStep 7676963 = 11515445) B11515445
theorem B3638317 : Blo 1196415 3638317 := bstep (se 3 (by rfl) ⟨682184, by rfl⟩ : syracuseStep 3638317 = 1364369) B1364369
theorem B3408941 : Blo 1196415 3408941 := bstep (se 3 (by rfl) ⟨639176, by rfl⟩ : syracuseStep 3408941 = 1278353) B1278353
theorem B1795121 : Blo 1196415 1795121 := bstep (se 2 (by rfl) ⟨673170, by rfl⟩ : syracuseStep 1795121 = 1346341) B1346341
theorem B3032113 : Blo 1196415 3032113 := bstep (se 2 (by rfl) ⟨1137042, by rfl⟩ : syracuseStep 3032113 = 2274085) B2274085
theorem B1197107 : Blo 1196415 1197107 := bstep (se 1 (by rfl) ⟨897830, by rfl⟩ : syracuseStep 1197107 = 1795661) B1795661
theorem B1795139 : Blo 1196415 1795139 := bstep (se 1 (by rfl) ⟨1346354, by rfl⟩ : syracuseStep 1795139 = 2692709) B2692709
theorem B1197123 : Blo 1196415 1197123 := bstep (se 1 (by rfl) ⟨897842, by rfl⟩ : syracuseStep 1197123 = 1795685) B1795685
theorem B2696273 : Blo 1196415 2696273 := bstep (se 2 (by rfl) ⟨1011102, by rfl⟩ : syracuseStep 2696273 = 2022205) B2022205
theorem B1197139 : Blo 1196415 1197139 := bstep (se 1 (by rfl) ⟨897854, by rfl⟩ : syracuseStep 1197139 = 1795709) B1795709
theorem B1795169 : Blo 1196415 1795169 := bstep (se 2 (by rfl) ⟨673188, by rfl⟩ : syracuseStep 1795169 = 1346377) B1346377
theorem B1197155 : Blo 1196415 1197155 := bstep (se 1 (by rfl) ⟨897866, by rfl⟩ : syracuseStep 1197155 = 1795733) B1795733
theorem B14566499 : Blo 1196415 14566499 := bstep (se 1 (by rfl) ⟨10924874, by rfl⟩ : syracuseStep 14566499 = 21849749) B21849749
theorem B2696291 : Blo 1196415 2696291 := bstep (se 1 (by rfl) ⟨2022218, by rfl⟩ : syracuseStep 2696291 = 4044437) B4044437
theorem B6825059 : Blo 1196415 6825059 := bstep (se 1 (by rfl) ⟨5118794, by rfl⟩ : syracuseStep 6825059 = 10237589) B10237589
theorem B4039793 : Blo 1196415 4039793 := bstep (se 2 (by rfl) ⟨1514922, by rfl⟩ : syracuseStep 4039793 = 3029845) B3029845
theorem B17507441 : Blo 1196415 17507441 := bstep (se 2 (by rfl) ⟨6565290, by rfl⟩ : syracuseStep 17507441 = 13130581) B13130581
theorem B1795187 : Blo 1196415 1795187 := bstep (se 1 (by rfl) ⟨1346390, by rfl⟩ : syracuseStep 1795187 = 2692781) B2692781
theorem B1197171 : Blo 1196415 1197171 := bstep (se 1 (by rfl) ⟨897878, by rfl⟩ : syracuseStep 1197171 = 1795757) B1795757
theorem B1197187 : Blo 1196415 1197187 := bstep (se 1 (by rfl) ⟨897890, by rfl⟩ : syracuseStep 1197187 = 1795781) B1795781
theorem B1795217 : Blo 1196415 1795217 := bstep (se 2 (by rfl) ⟨673206, by rfl⟩ : syracuseStep 1795217 = 1346413) B1346413
theorem B1197203 : Blo 1196415 1197203 := bstep (se 1 (by rfl) ⟨897902, by rfl⟩ : syracuseStep 1197203 = 1795805) B1795805
theorem B1795235 : Blo 1196415 1795235 := bstep (se 1 (by rfl) ⟨1346426, by rfl⟩ : syracuseStep 1795235 = 2692853) B2692853
theorem B1197219 : Blo 1196415 1197219 := bstep (se 1 (by rfl) ⟨897914, by rfl⟩ : syracuseStep 1197219 = 1795829) B1795829
theorem B1197235 : Blo 1196415 1197235 := bstep (se 1 (by rfl) ⟨897926, by rfl⟩ : syracuseStep 1197235 = 1795853) B1795853
theorem B1795265 : Blo 1196415 1795265 := bstep (se 2 (by rfl) ⟨673224, by rfl⟩ : syracuseStep 1795265 = 1346449) B1346449
theorem B1197251 : Blo 1196415 1197251 := bstep (se 1 (by rfl) ⟨897938, by rfl⟩ : syracuseStep 1197251 = 1795877) B1795877
theorem B1795283 : Blo 1196415 1795283 := bstep (se 1 (by rfl) ⟨1346462, by rfl⟩ : syracuseStep 1795283 = 2692925) B2692925
theorem B1197267 : Blo 1196415 1197267 := bstep (se 1 (by rfl) ⟨897950, by rfl⟩ : syracuseStep 1197267 = 1795901) B1795901
theorem B3409123 : Blo 1196415 3409123 := bstep (se 1 (by rfl) ⟨2556842, by rfl⟩ : syracuseStep 3409123 = 5113685) B5113685
theorem B1197283 : Blo 1196415 1197283 := bstep (se 1 (by rfl) ⟨897962, by rfl⟩ : syracuseStep 1197283 = 1795925) B1795925
theorem B1795313 : Blo 1196415 1795313 := bstep (se 2 (by rfl) ⟨673242, by rfl⟩ : syracuseStep 1795313 = 1346485) B1346485
theorem B1197299 : Blo 1196415 1197299 := bstep (se 1 (by rfl) ⟨897974, by rfl⟩ : syracuseStep 1197299 = 1795949) B1795949
theorem B1795331 : Blo 1196415 1795331 := bstep (se 1 (by rfl) ⟨1346498, by rfl⟩ : syracuseStep 1795331 = 2692997) B2692997
theorem B1197315 : Blo 1196415 1197315 := bstep (se 1 (by rfl) ⟨897986, by rfl⟩ : syracuseStep 1197315 = 1795973) B1795973
theorem B1197331 : Blo 1196415 1197331 := bstep (se 1 (by rfl) ⟨897998, by rfl⟩ : syracuseStep 1197331 = 1795997) B1795997
theorem B1795361 : Blo 1196415 1795361 := bstep (se 2 (by rfl) ⟨673260, by rfl⟩ : syracuseStep 1795361 = 1346521) B1346521
theorem B1197347 : Blo 1196415 1197347 := bstep (se 1 (by rfl) ⟨898010, by rfl⟩ : syracuseStep 1197347 = 1796021) B1796021
theorem B1795379 : Blo 1196415 1795379 := bstep (se 1 (by rfl) ⟨1346534, by rfl⟩ : syracuseStep 1795379 = 2693069) B2693069
theorem B1197363 : Blo 1196415 1197363 := bstep (se 1 (by rfl) ⟨898022, by rfl⟩ : syracuseStep 1197363 = 1796045) B1796045
theorem B1197379 : Blo 1196415 1197379 := bstep (se 1 (by rfl) ⟨898034, by rfl⟩ : syracuseStep 1197379 = 1796069) B1796069
theorem B3032387 : Blo 1196415 3032387 := bstep (se 1 (by rfl) ⟨2274290, by rfl⟩ : syracuseStep 3032387 = 4548581) B4548581
theorem B1795409 : Blo 1196415 1795409 := bstep (se 2 (by rfl) ⟨673278, by rfl⟩ : syracuseStep 1795409 = 1346557) B1346557
theorem B1197395 : Blo 1196415 1197395 := bstep (se 1 (by rfl) ⟨898046, by rfl⟩ : syracuseStep 1197395 = 1796093) B1796093
theorem B1795427 : Blo 1196415 1795427 := bstep (se 1 (by rfl) ⟨1346570, by rfl⟩ : syracuseStep 1795427 = 2693141) B2693141
theorem B1197411 : Blo 1196415 1197411 := bstep (se 1 (by rfl) ⟨898058, by rfl⟩ : syracuseStep 1197411 = 1796117) B1796117
theorem B1197427 : Blo 1196415 1197427 := bstep (se 1 (by rfl) ⟨898070, by rfl⟩ : syracuseStep 1197427 = 1796141) B1796141
theorem B1795457 : Blo 1196415 1795457 := bstep (se 2 (by rfl) ⟨673296, by rfl⟩ : syracuseStep 1795457 = 1346593) B1346593
theorem B3409283 : Blo 1196415 3409283 := bstep (se 1 (by rfl) ⟨2556962, by rfl⟩ : syracuseStep 3409283 = 5113925) B5113925
theorem B1197443 : Blo 1196415 1197443 := bstep (se 1 (by rfl) ⟨898082, by rfl⟩ : syracuseStep 1197443 = 1796165) B1796165
theorem B5752205 : Blo 1196415 5752205 := bstep (se 3 (by rfl) ⟨1078538, by rfl⟩ : syracuseStep 5752205 = 2157077) B2157077
theorem B2426257 : Blo 1196415 2426257 := bstep (se 2 (by rfl) ⟨909846, by rfl⟩ : syracuseStep 2426257 = 1819693) B1819693
theorem B1795475 : Blo 1196415 1795475 := bstep (se 1 (by rfl) ⟨1346606, by rfl⟩ : syracuseStep 1795475 = 2693213) B2693213
theorem B1197459 : Blo 1196415 1197459 := bstep (se 1 (by rfl) ⟨898094, by rfl⟩ : syracuseStep 1197459 = 1796189) B1796189
theorem B1197475 : Blo 1196415 1197475 := bstep (se 1 (by rfl) ⟨898106, by rfl⟩ : syracuseStep 1197475 = 1796213) B1796213
theorem B1795505 : Blo 1196415 1795505 := bstep (se 2 (by rfl) ⟨673314, by rfl⟩ : syracuseStep 1795505 = 1346629) B1346629
theorem B1197491 : Blo 1196415 1197491 := bstep (se 1 (by rfl) ⟨898118, by rfl⟩ : syracuseStep 1197491 = 1796237) B1796237
theorem B1795523 : Blo 1196415 1795523 := bstep (se 1 (by rfl) ⟨1346642, by rfl⟩ : syracuseStep 1795523 = 2693285) B2693285
theorem B1197507 : Blo 1196415 1197507 := bstep (se 1 (by rfl) ⟨898130, by rfl⟩ : syracuseStep 1197507 = 1796261) B1796261
theorem B1197523 : Blo 1196415 1197523 := bstep (se 1 (by rfl) ⟨898142, by rfl⟩ : syracuseStep 1197523 = 1796285) B1796285
theorem B1213907 : Blo 1196415 1213907 := bstep (se 1 (by rfl) ⟨910430, by rfl⟩ : syracuseStep 1213907 = 1820861) B1820861
theorem B1795553 : Blo 1196415 1795553 := bstep (se 2 (by rfl) ⟨673332, by rfl⟩ : syracuseStep 1795553 = 1346665) B1346665
theorem B1197539 : Blo 1196415 1197539 := bstep (se 1 (by rfl) ⟨898154, by rfl⟩ : syracuseStep 1197539 = 1796309) B1796309
theorem B1795571 : Blo 1196415 1795571 := bstep (se 1 (by rfl) ⟨1346678, by rfl⟩ : syracuseStep 1795571 = 2693357) B2693357
theorem B1197555 : Blo 1196415 1197555 := bstep (se 1 (by rfl) ⟨898166, by rfl⟩ : syracuseStep 1197555 = 1796333) B1796333
theorem B1197571 : Blo 1196415 1197571 := bstep (se 1 (by rfl) ⟨898178, by rfl⟩ : syracuseStep 1197571 = 1796357) B1796357
theorem B3032579 : Blo 1196415 3032579 := bstep (se 1 (by rfl) ⟨2274434, by rfl⟩ : syracuseStep 3032579 = 4548869) B4548869
theorem B4548109 : Blo 1196415 4548109 := bstep (se 3 (by rfl) ⟨852770, by rfl⟩ : syracuseStep 4548109 = 1705541) B1705541
theorem B1795601 : Blo 1196415 1795601 := bstep (se 2 (by rfl) ⟨673350, by rfl⟩ : syracuseStep 1795601 = 1346701) B1346701
theorem B1197587 : Blo 1196415 1197587 := bstep (se 1 (by rfl) ⟨898190, by rfl⟩ : syracuseStep 1197587 = 1796381) B1796381
theorem B1795619 : Blo 1196415 1795619 := bstep (se 1 (by rfl) ⟨1346714, by rfl⟩ : syracuseStep 1795619 = 2693429) B2693429
theorem B1197603 : Blo 1196415 1197603 := bstep (se 1 (by rfl) ⟨898202, by rfl⟩ : syracuseStep 1197603 = 1796405) B1796405
theorem B1197619 : Blo 1196415 1197619 := bstep (se 1 (by rfl) ⟨898214, by rfl⟩ : syracuseStep 1197619 = 1796429) B1796429
theorem B1795649 : Blo 1196415 1795649 := bstep (se 2 (by rfl) ⟨673368, by rfl⟩ : syracuseStep 1795649 = 1346737) B1346737
theorem B1197635 : Blo 1196415 1197635 := bstep (se 1 (by rfl) ⟨898226, by rfl⟩ : syracuseStep 1197635 = 1796453) B1796453
theorem B1795667 : Blo 1196415 1795667 := bstep (se 1 (by rfl) ⟨1346750, by rfl⟩ : syracuseStep 1795667 = 2693501) B2693501
theorem B1197651 : Blo 1196415 1197651 := bstep (se 1 (by rfl) ⟨898238, by rfl⟩ : syracuseStep 1197651 = 1796477) B1796477
theorem B1197667 : Blo 1196415 1197667 := bstep (se 1 (by rfl) ⟨898250, by rfl⟩ : syracuseStep 1197667 = 1796501) B1796501
theorem B1795697 : Blo 1196415 1795697 := bstep (se 2 (by rfl) ⟨673386, by rfl⟩ : syracuseStep 1795697 = 1346773) B1346773
theorem B1197683 : Blo 1196415 1197683 := bstep (se 1 (by rfl) ⟨898262, by rfl⟩ : syracuseStep 1197683 = 1796525) B1796525
theorem B1795715 : Blo 1196415 1795715 := bstep (se 1 (by rfl) ⟨1346786, by rfl⟩ : syracuseStep 1795715 = 2693573) B2693573
theorem B1197699 : Blo 1196415 1197699 := bstep (se 1 (by rfl) ⟨898274, by rfl⟩ : syracuseStep 1197699 = 1796549) B1796549
theorem B4040333 : Blo 1196415 4040333 := bstep (se 3 (by rfl) ⟨757562, by rfl⟩ : syracuseStep 4040333 = 1515125) B1515125
theorem B1197715 : Blo 1196415 1197715 := bstep (se 1 (by rfl) ⟨898286, by rfl⟩ : syracuseStep 1197715 = 1796573) B1796573
theorem B1795745 : Blo 1196415 1795745 := bstep (se 2 (by rfl) ⟨673404, by rfl⟩ : syracuseStep 1795745 = 1346809) B1346809
theorem B1820321 : Blo 1196415 1820321 := bstep (se 2 (by rfl) ⟨682620, by rfl⟩ : syracuseStep 1820321 = 1365241) B1365241
theorem B1197731 : Blo 1196415 1197731 := bstep (se 1 (by rfl) ⟨898298, by rfl⟩ : syracuseStep 1197731 = 1796597) B1796597
theorem B1795763 : Blo 1196415 1795763 := bstep (se 1 (by rfl) ⟨1346822, by rfl⟩ : syracuseStep 1795763 = 2693645) B2693645
theorem B1197747 : Blo 1196415 1197747 := bstep (se 1 (by rfl) ⟨898310, by rfl⟩ : syracuseStep 1197747 = 1796621) B1796621
theorem B1918657 : Blo 1196415 1918657 := bstep (se 2 (by rfl) ⟨719496, by rfl⟩ : syracuseStep 1918657 = 1438993) B1438993
theorem B4040387 : Blo 1196415 4040387 := bstep (se 1 (by rfl) ⟨3030290, by rfl⟩ : syracuseStep 4040387 = 6060581) B6060581
theorem B1197763 : Blo 1196415 1197763 := bstep (se 1 (by rfl) ⟨898322, by rfl⟩ : syracuseStep 1197763 = 1796645) B1796645
theorem B6063821 : Blo 1196415 6063821 := bstep (se 3 (by rfl) ⟨1136966, by rfl⟩ : syracuseStep 6063821 = 2273933) B2273933
theorem B1795793 : Blo 1196415 1795793 := bstep (se 2 (by rfl) ⟨673422, by rfl⟩ : syracuseStep 1795793 = 1346845) B1346845
theorem B1197779 : Blo 1196415 1197779 := bstep (se 1 (by rfl) ⟨898334, by rfl⟩ : syracuseStep 1197779 = 1796669) B1796669
theorem B1795811 : Blo 1196415 1795811 := bstep (se 1 (by rfl) ⟨1346858, by rfl⟩ : syracuseStep 1795811 = 2693717) B2693717
theorem B1197795 : Blo 1196415 1197795 := bstep (se 1 (by rfl) ⟨898346, by rfl⟩ : syracuseStep 1197795 = 1796693) B1796693
theorem B1197811 : Blo 1196415 1197811 := bstep (se 1 (by rfl) ⟨898358, by rfl⟩ : syracuseStep 1197811 = 1796717) B1796717
theorem B1795841 : Blo 1196415 1795841 := bstep (se 2 (by rfl) ⟨673440, by rfl⟩ : syracuseStep 1795841 = 1346881) B1346881
theorem B1197827 : Blo 1196415 1197827 := bstep (se 1 (by rfl) ⟨898370, by rfl⟩ : syracuseStep 1197827 = 1796741) B1796741
theorem B1795859 : Blo 1196415 1795859 := bstep (se 1 (by rfl) ⟨1346894, by rfl⟩ : syracuseStep 1795859 = 2693789) B2693789
theorem B1197843 : Blo 1196415 1197843 := bstep (se 1 (by rfl) ⟨898382, by rfl⟩ : syracuseStep 1197843 = 1796765) B1796765
theorem B1197859 : Blo 1196415 1197859 := bstep (se 1 (by rfl) ⟨898394, by rfl⟩ : syracuseStep 1197859 = 1796789) B1796789
theorem B1795889 : Blo 1196415 1795889 := bstep (se 2 (by rfl) ⟨673458, by rfl⟩ : syracuseStep 1795889 = 1346917) B1346917
theorem B1197875 : Blo 1196415 1197875 := bstep (se 1 (by rfl) ⟨898406, by rfl⟩ : syracuseStep 1197875 = 1796813) B1796813
theorem B1795907 : Blo 1196415 1795907 := bstep (se 1 (by rfl) ⟨1346930, by rfl⟩ : syracuseStep 1795907 = 2693861) B2693861
theorem B1197891 : Blo 1196415 1197891 := bstep (se 1 (by rfl) ⟨898418, by rfl⟩ : syracuseStep 1197891 = 1796837) B1796837
theorem B1197907 : Blo 1196415 1197907 := bstep (se 1 (by rfl) ⟨898430, by rfl⟩ : syracuseStep 1197907 = 1796861) B1796861
theorem B1795937 : Blo 1196415 1795937 := bstep (se 2 (by rfl) ⟨673476, by rfl⟩ : syracuseStep 1795937 = 1346953) B1346953
theorem B1197923 : Blo 1196415 1197923 := bstep (se 1 (by rfl) ⟨898442, by rfl⟩ : syracuseStep 1197923 = 1796885) B1796885
theorem B1795955 : Blo 1196415 1795955 := bstep (se 1 (by rfl) ⟨1346966, by rfl⟩ : syracuseStep 1795955 = 2693933) B2693933
theorem B1197939 : Blo 1196415 1197939 := bstep (se 1 (by rfl) ⟨898454, by rfl⟩ : syracuseStep 1197939 = 1796909) B1796909
theorem B2049907 : Blo 1196415 2049907 := bstep (se 1 (by rfl) ⟨1537430, by rfl⟩ : syracuseStep 2049907 = 3074861) B3074861
theorem B1197955 : Blo 1196415 1197955 := bstep (se 1 (by rfl) ⟨898466, by rfl⟩ : syracuseStep 1197955 = 1796933) B1796933
theorem B1795985 : Blo 1196415 1795985 := bstep (se 2 (by rfl) ⟨673494, by rfl⟩ : syracuseStep 1795985 = 1346989) B1346989
theorem B1197971 : Blo 1196415 1197971 := bstep (se 1 (by rfl) ⟨898478, by rfl⟩ : syracuseStep 1197971 = 1796957) B1796957
theorem B1869731 : Blo 1196415 1869731 := bstep (se 1 (by rfl) ⟨1402298, by rfl⟩ : syracuseStep 1869731 = 2804597) B2804597
theorem B1796003 : Blo 1196415 1796003 := bstep (se 1 (by rfl) ⟨1347002, by rfl⟩ : syracuseStep 1796003 = 2694005) B2694005
theorem B1197987 : Blo 1196415 1197987 := bstep (se 1 (by rfl) ⟨898490, by rfl⟩ : syracuseStep 1197987 = 1796981) B1796981
theorem B1198003 : Blo 1196415 1198003 := bstep (se 1 (by rfl) ⟨898502, by rfl⟩ : syracuseStep 1198003 = 1797005) B1797005
theorem B1796033 : Blo 1196415 1796033 := bstep (se 2 (by rfl) ⟨673512, by rfl⟩ : syracuseStep 1796033 = 1347025) B1347025
theorem B1198019 : Blo 1196415 1198019 := bstep (se 1 (by rfl) ⟨898514, by rfl⟩ : syracuseStep 1198019 = 1797029) B1797029
theorem B4040657 : Blo 1196415 4040657 := bstep (se 2 (by rfl) ⟨1515246, by rfl⟩ : syracuseStep 4040657 = 3030493) B3030493
theorem B1796051 : Blo 1196415 1796051 := bstep (se 1 (by rfl) ⟨1347038, by rfl⟩ : syracuseStep 1796051 = 2694077) B2694077
theorem B1198035 : Blo 1196415 1198035 := bstep (se 1 (by rfl) ⟨898526, by rfl⟩ : syracuseStep 1198035 = 1797053) B1797053
theorem B1198051 : Blo 1196415 1198051 := bstep (se 1 (by rfl) ⟨898538, by rfl⟩ : syracuseStep 1198051 = 1797077) B1797077
theorem B1796081 : Blo 1196415 1796081 := bstep (se 2 (by rfl) ⟨673530, by rfl⟩ : syracuseStep 1796081 = 1347061) B1347061
theorem B1198067 : Blo 1196415 1198067 := bstep (se 1 (by rfl) ⟨898550, by rfl⟩ : syracuseStep 1198067 = 1797101) B1797101
theorem B1796099 : Blo 1196415 1796099 := bstep (se 1 (by rfl) ⟨1347074, by rfl⟩ : syracuseStep 1796099 = 2694149) B2694149
theorem B1198083 : Blo 1196415 1198083 := bstep (se 1 (by rfl) ⟨898562, by rfl⟩ : syracuseStep 1198083 = 1797125) B1797125
theorem B1198099 : Blo 1196415 1198099 := bstep (se 1 (by rfl) ⟨898574, by rfl⟩ : syracuseStep 1198099 = 1797149) B1797149
theorem B1796129 : Blo 1196415 1796129 := bstep (se 2 (by rfl) ⟨673548, by rfl⟩ : syracuseStep 1796129 = 1347097) B1347097
theorem B1198115 : Blo 1196415 1198115 := bstep (se 1 (by rfl) ⟨898586, by rfl⟩ : syracuseStep 1198115 = 1797173) B1797173
theorem B1796147 : Blo 1196415 1796147 := bstep (se 1 (by rfl) ⟨1347110, by rfl⟩ : syracuseStep 1796147 = 2694221) B2694221
theorem B1198131 : Blo 1196415 1198131 := bstep (se 1 (by rfl) ⟨898598, by rfl⟩ : syracuseStep 1198131 = 1797197) B1797197
theorem B1198147 : Blo 1196415 1198147 := bstep (se 1 (by rfl) ⟨898610, by rfl⟩ : syracuseStep 1198147 = 1797221) B1797221
theorem B1796177 : Blo 1196415 1796177 := bstep (se 2 (by rfl) ⟨673566, by rfl⟩ : syracuseStep 1796177 = 1347133) B1347133
theorem B1198163 : Blo 1196415 1198163 := bstep (se 1 (by rfl) ⟨898622, by rfl⟩ : syracuseStep 1198163 = 1797245) B1797245
theorem B1796195 : Blo 1196415 1796195 := bstep (se 1 (by rfl) ⟨1347146, by rfl⟩ : syracuseStep 1796195 = 2694293) B2694293
theorem B1198179 : Blo 1196415 1198179 := bstep (se 1 (by rfl) ⟨898634, by rfl⟩ : syracuseStep 1198179 = 1797269) B1797269
theorem B1198195 : Blo 1196415 1198195 := bstep (se 1 (by rfl) ⟨898646, by rfl⟩ : syracuseStep 1198195 = 1797293) B1797293
theorem B1796225 : Blo 1196415 1796225 := bstep (se 2 (by rfl) ⟨673584, by rfl⟩ : syracuseStep 1796225 = 1347169) B1347169
theorem B1198211 : Blo 1196415 1198211 := bstep (se 1 (by rfl) ⟨898658, by rfl⟩ : syracuseStep 1198211 = 1797317) B1797317
theorem B1796243 : Blo 1196415 1796243 := bstep (se 1 (by rfl) ⟨1347182, by rfl⟩ : syracuseStep 1796243 = 2694365) B2694365
theorem B1230995 : Blo 1196415 1230995 := bstep (se 1 (by rfl) ⟨923246, by rfl⟩ : syracuseStep 1230995 = 1846493) B1846493
theorem B1198227 : Blo 1196415 1198227 := bstep (se 1 (by rfl) ⟨898670, by rfl⟩ : syracuseStep 1198227 = 1797341) B1797341
theorem B1198243 : Blo 1196415 1198243 := bstep (se 1 (by rfl) ⟨898682, by rfl⟩ : syracuseStep 1198243 = 1797365) B1797365
theorem B1796273 : Blo 1196415 1796273 := bstep (se 2 (by rfl) ⟨673602, by rfl⟩ : syracuseStep 1796273 = 1347205) B1347205
theorem B1198259 : Blo 1196415 1198259 := bstep (se 1 (by rfl) ⟨898694, by rfl⟩ : syracuseStep 1198259 = 1797389) B1797389
theorem B1796291 : Blo 1196415 1796291 := bstep (se 1 (by rfl) ⟨1347218, by rfl⟩ : syracuseStep 1796291 = 2694437) B2694437
theorem B1198275 : Blo 1196415 1198275 := bstep (se 1 (by rfl) ⟨898706, by rfl⟩ : syracuseStep 1198275 = 1797413) B1797413
theorem B1706179 : Blo 1196415 1706179 := bstep (se 1 (by rfl) ⟨1279634, by rfl⟩ : syracuseStep 1706179 = 2559269) B2559269
theorem B1198291 : Blo 1196415 1198291 := bstep (se 1 (by rfl) ⟨898718, by rfl⟩ : syracuseStep 1198291 = 1797437) B1797437
theorem B1796321 : Blo 1196415 1796321 := bstep (se 2 (by rfl) ⟨673620, by rfl⟩ : syracuseStep 1796321 = 1347241) B1347241
theorem B1198307 : Blo 1196415 1198307 := bstep (se 1 (by rfl) ⟨898730, by rfl⟩ : syracuseStep 1198307 = 1797461) B1797461
theorem B2271473 : Blo 1196415 2271473 := bstep (se 2 (by rfl) ⟨851802, by rfl⟩ : syracuseStep 2271473 = 1703605) B1703605
theorem B1796339 : Blo 1196415 1796339 := bstep (se 1 (by rfl) ⟨1347254, by rfl⟩ : syracuseStep 1796339 = 2694509) B2694509
theorem B1198323 : Blo 1196415 1198323 := bstep (se 1 (by rfl) ⟨898742, by rfl⟩ : syracuseStep 1198323 = 1797485) B1797485
theorem B1198339 : Blo 1196415 1198339 := bstep (se 1 (by rfl) ⟨898754, by rfl⟩ : syracuseStep 1198339 = 1797509) B1797509
theorem B1796369 : Blo 1196415 1796369 := bstep (se 2 (by rfl) ⟨673638, by rfl⟩ : syracuseStep 1796369 = 1347277) B1347277
theorem B1198355 : Blo 1196415 1198355 := bstep (se 1 (by rfl) ⟨898766, by rfl⟩ : syracuseStep 1198355 = 1797533) B1797533
theorem B1796387 : Blo 1196415 1796387 := bstep (se 1 (by rfl) ⟨1347290, by rfl⟩ : syracuseStep 1796387 = 2694581) B2694581
theorem B4548899 : Blo 1196415 4548899 := bstep (se 1 (by rfl) ⟨3411674, by rfl⟩ : syracuseStep 4548899 = 6823349) B6823349
theorem B1198371 : Blo 1196415 1198371 := bstep (se 1 (by rfl) ⟨898778, by rfl⟩ : syracuseStep 1198371 = 1797557) B1797557
theorem B5187889 : Blo 1196415 5187889 := bstep (se 2 (by rfl) ⟨1945458, by rfl⟩ : syracuseStep 5187889 = 3890917) B3890917
theorem B1198387 : Blo 1196415 1198387 := bstep (se 1 (by rfl) ⟨898790, by rfl⟩ : syracuseStep 1198387 = 1797581) B1797581
theorem B1796417 : Blo 1196415 1796417 := bstep (se 2 (by rfl) ⟨673656, by rfl⟩ : syracuseStep 1796417 = 1347313) B1347313
theorem B3238211 : Blo 1196415 3238211 := bstep (se 1 (by rfl) ⟨2428658, by rfl⟩ : syracuseStep 3238211 = 4857317) B4857317
theorem B1198403 : Blo 1196415 1198403 := bstep (se 1 (by rfl) ⟨898802, by rfl⟩ : syracuseStep 1198403 = 1797605) B1797605
theorem B1796435 : Blo 1196415 1796435 := bstep (se 1 (by rfl) ⟨1347326, by rfl⟩ : syracuseStep 1796435 = 2694653) B2694653
theorem B1796465 : Blo 1196415 1796465 := bstep (se 2 (by rfl) ⟨673674, by rfl⟩ : syracuseStep 1796465 = 1347349) B1347349
theorem B1796483 : Blo 1196415 1796483 := bstep (se 1 (by rfl) ⟨1347362, by rfl⟩ : syracuseStep 1796483 = 2694725) B2694725
theorem B3074449 : Blo 1196415 3074449 := bstep (se 2 (by rfl) ⟨1152918, by rfl⟩ : syracuseStep 3074449 = 2305837) B2305837
theorem B1796513 : Blo 1196415 1796513 := bstep (se 2 (by rfl) ⟨673692, by rfl⟩ : syracuseStep 1796513 = 1347385) B1347385
theorem B3410353 : Blo 1196415 3410353 := bstep (se 2 (by rfl) ⟨1278882, by rfl⟩ : syracuseStep 3410353 = 2557765) B2557765
theorem B1796531 : Blo 1196415 1796531 := bstep (se 1 (by rfl) ⟨1347398, by rfl⟩ : syracuseStep 1796531 = 2694797) B2694797
theorem B1796561 : Blo 1196415 1796561 := bstep (se 2 (by rfl) ⟨673710, by rfl⟩ : syracuseStep 1796561 = 1347421) B1347421
theorem B17254883 : Blo 1196415 17254883 := bstep (se 1 (by rfl) ⟨12941162, by rfl⟩ : syracuseStep 17254883 = 25882325) B25882325
theorem B11504099 : Blo 1196415 11504099 := bstep (se 1 (by rfl) ⟨8628074, by rfl⟩ : syracuseStep 11504099 = 17256149) B17256149
theorem B1796579 : Blo 1196415 1796579 := bstep (se 1 (by rfl) ⟨1347434, by rfl⟩ : syracuseStep 1796579 = 2694869) B2694869
theorem B4041197 : Blo 1196415 4041197 := bstep (se 3 (by rfl) ⟨757724, by rfl⟩ : syracuseStep 4041197 = 1515449) B1515449
theorem B1346035 : Blo 1196415 1346035 := bstep (se 1 (by rfl) ⟨1009526, by rfl⟩ : syracuseStep 1346035 = 2019053) B2019053
theorem B1796609 : Blo 1196415 1796609 := bstep (se 2 (by rfl) ⟨673728, by rfl⟩ : syracuseStep 1796609 = 1347457) B1347457
theorem B1796627 : Blo 1196415 1796627 := bstep (se 1 (by rfl) ⟨1347470, by rfl⟩ : syracuseStep 1796627 = 2694941) B2694941
theorem B4041251 : Blo 1196415 4041251 := bstep (se 1 (by rfl) ⟨3030938, by rfl⟩ : syracuseStep 4041251 = 6061877) B6061877
theorem B1796657 : Blo 1196415 1796657 := bstep (se 2 (by rfl) ⟨673746, by rfl⟩ : syracuseStep 1796657 = 1347493) B1347493
theorem B1796675 : Blo 1196415 1796675 := bstep (se 1 (by rfl) ⟨1347506, by rfl⟩ : syracuseStep 1796675 = 2695013) B2695013
theorem B1796705 : Blo 1196415 1796705 := bstep (se 2 (by rfl) ⟨673764, by rfl⟩ : syracuseStep 1796705 = 1347529) B1347529
theorem B10930787 : Blo 1196415 10930787 := bstep (se 1 (by rfl) ⟨8198090, by rfl⟩ : syracuseStep 10930787 = 16396181) B16396181
theorem B1796723 : Blo 1196415 1796723 := bstep (se 1 (by rfl) ⟨1347542, by rfl⟩ : syracuseStep 1796723 = 2695085) B2695085
theorem B1346179 : Blo 1196415 1346179 := bstep (se 1 (by rfl) ⟨1009634, by rfl⟩ : syracuseStep 1346179 = 2019269) B2019269
theorem B1796753 : Blo 1196415 1796753 := bstep (se 2 (by rfl) ⟨673782, by rfl⟩ : syracuseStep 1796753 = 1347565) B1347565
theorem B1796771 : Blo 1196415 1796771 := bstep (se 1 (by rfl) ⟨1347578, by rfl⟩ : syracuseStep 1796771 = 2695157) B2695157
theorem B1821361 : Blo 1196415 1821361 := bstep (se 2 (by rfl) ⟨683010, by rfl⟩ : syracuseStep 1821361 = 1366021) B1366021
theorem B1796801 : Blo 1196415 1796801 := bstep (se 2 (by rfl) ⟨673800, by rfl⟩ : syracuseStep 1796801 = 1347601) B1347601
theorem B7670477 : Blo 1196415 7670477 := bstep (se 3 (by rfl) ⟨1438214, by rfl⟩ : syracuseStep 7670477 = 2876429) B2876429
theorem B5114573 : Blo 1196415 5114573 := bstep (se 3 (by rfl) ⟨958982, by rfl⟩ : syracuseStep 5114573 = 1917965) B1917965
theorem B1796819 : Blo 1196415 1796819 := bstep (se 1 (by rfl) ⟨1347614, by rfl⟩ : syracuseStep 1796819 = 2695229) B2695229
theorem B5114609 : Blo 1196415 5114609 := bstep (se 2 (by rfl) ⟨1917978, by rfl⟩ : syracuseStep 5114609 = 3835957) B3835957
theorem B1796849 : Blo 1196415 1796849 := bstep (se 2 (by rfl) ⟨673818, by rfl⟩ : syracuseStep 1796849 = 1347637) B1347637
theorem B1796867 : Blo 1196415 1796867 := bstep (se 1 (by rfl) ⟨1347650, by rfl⟩ : syracuseStep 1796867 = 2695301) B2695301
theorem B1346323 : Blo 1196415 1346323 := bstep (se 1 (by rfl) ⟨1009742, by rfl⟩ : syracuseStep 1346323 = 2019485) B2019485
theorem B1796897 : Blo 1196415 1796897 := bstep (se 2 (by rfl) ⟨673836, by rfl⟩ : syracuseStep 1796897 = 1347673) B1347673
theorem B4041521 : Blo 1196415 4041521 := bstep (se 2 (by rfl) ⟨1515570, by rfl⟩ : syracuseStep 4041521 = 3031141) B3031141
theorem B6916913 : Blo 1196415 6916913 := bstep (se 2 (by rfl) ⟨2593842, by rfl⟩ : syracuseStep 6916913 = 5187685) B5187685
theorem B1796915 : Blo 1196415 1796915 := bstep (se 1 (by rfl) ⟨1347686, by rfl⟩ : syracuseStep 1796915 = 2695373) B2695373
theorem B1796945 : Blo 1196415 1796945 := bstep (se 2 (by rfl) ⟨673854, by rfl⟩ : syracuseStep 1796945 = 1347709) B1347709
theorem B1796963 : Blo 1196415 1796963 := bstep (se 1 (by rfl) ⟨1347722, by rfl⟩ : syracuseStep 1796963 = 2695445) B2695445
theorem B1796993 : Blo 1196415 1796993 := bstep (se 2 (by rfl) ⟨673872, by rfl⟩ : syracuseStep 1796993 = 1347745) B1347745
theorem B6818701 : Blo 1196415 6818701 := bstep (se 3 (by rfl) ⟨1278506, by rfl⟩ : syracuseStep 6818701 = 2557013) B2557013
theorem B1797011 : Blo 1196415 1797011 := bstep (se 1 (by rfl) ⟨1347758, by rfl⟩ : syracuseStep 1797011 = 2695517) B2695517
theorem B1346467 : Blo 1196415 1346467 := bstep (se 1 (by rfl) ⟨1009850, by rfl⟩ : syracuseStep 1346467 = 2019701) B2019701
theorem B1797041 : Blo 1196415 1797041 := bstep (se 2 (by rfl) ⟨673890, by rfl⟩ : syracuseStep 1797041 = 1347781) B1347781
theorem B4549553 : Blo 1196415 4549553 := bstep (se 2 (by rfl) ⟨1706082, by rfl⟩ : syracuseStep 4549553 = 3412165) B3412165
theorem B1797059 : Blo 1196415 1797059 := bstep (se 1 (by rfl) ⟨1347794, by rfl⟩ : syracuseStep 1797059 = 2695589) B2695589
theorem B1797089 : Blo 1196415 1797089 := bstep (se 2 (by rfl) ⟨673908, by rfl⟩ : syracuseStep 1797089 = 1347817) B1347817
theorem B1846243 : Blo 1196415 1846243 := bstep (se 1 (by rfl) ⟨1384682, by rfl⟩ : syracuseStep 1846243 = 2769365) B2769365
theorem B2157553 : Blo 1196415 2157553 := bstep (se 2 (by rfl) ⟨809082, by rfl⟩ : syracuseStep 2157553 = 1618165) B1618165
theorem B1797107 : Blo 1196415 1797107 := bstep (se 1 (by rfl) ⟨1347830, by rfl⟩ : syracuseStep 1797107 = 2695661) B2695661
theorem B1797137 : Blo 1196415 1797137 := bstep (se 2 (by rfl) ⟨673926, by rfl⟩ : syracuseStep 1797137 = 1347853) B1347853
theorem B1797155 : Blo 1196415 1797155 := bstep (se 1 (by rfl) ⟨1347866, by rfl⟩ : syracuseStep 1797155 = 2695733) B2695733
theorem B1346611 : Blo 1196415 1346611 := bstep (se 1 (by rfl) ⟨1009958, by rfl⟩ : syracuseStep 1346611 = 2019917) B2019917
theorem B1797185 : Blo 1196415 1797185 := bstep (se 2 (by rfl) ⟨673944, by rfl⟩ : syracuseStep 1797185 = 1347889) B1347889
theorem B1797203 : Blo 1196415 1797203 := bstep (se 1 (by rfl) ⟨1347902, by rfl⟩ : syracuseStep 1797203 = 2695805) B2695805
theorem B2272369 : Blo 1196415 2272369 := bstep (se 2 (by rfl) ⟨852138, by rfl⟩ : syracuseStep 2272369 = 1704277) B1704277
theorem B13126769 : Blo 1196415 13126769 := bstep (se 2 (by rfl) ⟨4922538, by rfl⟩ : syracuseStep 13126769 = 9845077) B9845077
theorem B1797233 : Blo 1196415 1797233 := bstep (se 2 (by rfl) ⟨673962, by rfl⟩ : syracuseStep 1797233 = 1347925) B1347925
theorem B1617025 : Blo 1196415 1617025 := bstep (se 2 (by rfl) ⟨606384, by rfl⟩ : syracuseStep 1617025 = 1212769) B1212769
theorem B1797251 : Blo 1196415 1797251 := bstep (se 1 (by rfl) ⟨1347938, by rfl⟩ : syracuseStep 1797251 = 2695877) B2695877
theorem B6229133 : Blo 1196415 6229133 := bstep (se 3 (by rfl) ⟨1167962, by rfl⟩ : syracuseStep 6229133 = 2335925) B2335925
theorem B1797281 : Blo 1196415 1797281 := bstep (se 2 (by rfl) ⟨673980, by rfl⟩ : syracuseStep 1797281 = 1347961) B1347961
theorem B1797299 : Blo 1196415 1797299 := bstep (se 1 (by rfl) ⟨1347974, by rfl⟩ : syracuseStep 1797299 = 2695949) B2695949
theorem B1346755 : Blo 1196415 1346755 := bstep (se 1 (by rfl) ⟨1010066, by rfl⟩ : syracuseStep 1346755 = 2020133) B2020133
theorem B1944785 : Blo 1196415 1944785 := bstep (se 2 (by rfl) ⟨729294, by rfl⟩ : syracuseStep 1944785 = 1458589) B1458589
theorem B1797329 : Blo 1196415 1797329 := bstep (se 2 (by rfl) ⟨673998, by rfl⟩ : syracuseStep 1797329 = 1347997) B1347997
theorem B1797347 : Blo 1196415 1797347 := bstep (se 1 (by rfl) ⟨1348010, by rfl⟩ : syracuseStep 1797347 = 2696021) B2696021
theorem B3239153 : Blo 1196415 3239153 := bstep (se 2 (by rfl) ⟨1214682, by rfl⟩ : syracuseStep 3239153 = 2429365) B2429365
theorem B1797377 : Blo 1196415 1797377 := bstep (se 2 (by rfl) ⟨674016, by rfl⟩ : syracuseStep 1797377 = 1348033) B1348033
theorem B2559235 : Blo 1196415 2559235 := bstep (se 1 (by rfl) ⟨1919426, by rfl⟩ : syracuseStep 2559235 = 3838853) B3838853
theorem B9096461 : Blo 1196415 9096461 := bstep (se 3 (by rfl) ⟨1705586, by rfl⟩ : syracuseStep 9096461 = 3411173) B3411173
theorem B2272529 : Blo 1196415 2272529 := bstep (se 2 (by rfl) ⟨852198, by rfl⟩ : syracuseStep 2272529 = 1704397) B1704397
theorem B1797395 : Blo 1196415 1797395 := bstep (se 1 (by rfl) ⟨1348046, by rfl⟩ : syracuseStep 1797395 = 2696093) B2696093
theorem B6147377 : Blo 1196415 6147377 := bstep (se 2 (by rfl) ⟨2305266, by rfl⟩ : syracuseStep 6147377 = 4610533) B4610533
theorem B1797425 : Blo 1196415 1797425 := bstep (se 2 (by rfl) ⟨674034, by rfl⟩ : syracuseStep 1797425 = 1348069) B1348069
theorem B1797443 : Blo 1196415 1797443 := bstep (se 1 (by rfl) ⟨1348082, by rfl⟩ : syracuseStep 1797443 = 2696165) B2696165
theorem B4042061 : Blo 1196415 4042061 := bstep (se 3 (by rfl) ⟨757886, by rfl⟩ : syracuseStep 4042061 = 1515773) B1515773
theorem B1346899 : Blo 1196415 1346899 := bstep (se 1 (by rfl) ⟨1010174, by rfl⟩ : syracuseStep 1346899 = 2020349) B2020349
theorem B1797473 : Blo 1196415 1797473 := bstep (se 2 (by rfl) ⟨674052, by rfl⟩ : syracuseStep 1797473 = 1348105) B1348105
theorem B1797491 : Blo 1196415 1797491 := bstep (se 1 (by rfl) ⟨1348118, by rfl⟩ : syracuseStep 1797491 = 2696237) B2696237
theorem B4042115 : Blo 1196415 4042115 := bstep (se 1 (by rfl) ⟨3031586, by rfl⟩ : syracuseStep 4042115 = 6063173) B6063173
theorem B1797521 : Blo 1196415 1797521 := bstep (se 2 (by rfl) ⟨674070, by rfl⟩ : syracuseStep 1797521 = 1348141) B1348141
theorem B1797539 : Blo 1196415 1797539 := bstep (se 1 (by rfl) ⟨1348154, by rfl⟩ : syracuseStep 1797539 = 2696309) B2696309
theorem B1797569 : Blo 1196415 1797569 := bstep (se 2 (by rfl) ⟨674088, by rfl⟩ : syracuseStep 1797569 = 1348177) B1348177
theorem B3501521 : Blo 1196415 3501521 := bstep (se 2 (by rfl) ⟨1313070, by rfl⟩ : syracuseStep 3501521 = 2626141) B2626141
theorem B1797587 : Blo 1196415 1797587 := bstep (se 1 (by rfl) ⟨1348190, by rfl⟩ : syracuseStep 1797587 = 2696381) B2696381
theorem B1347043 : Blo 1196415 1347043 := bstep (se 1 (by rfl) ⟨1010282, by rfl⟩ : syracuseStep 1347043 = 2020565) B2020565
theorem B1797617 : Blo 1196415 1797617 := bstep (se 2 (by rfl) ⟨674106, by rfl⟩ : syracuseStep 1797617 = 1348213) B1348213
theorem B1347187 : Blo 1196415 1347187 := bstep (se 1 (by rfl) ⟨1010390, by rfl⟩ : syracuseStep 1347187 = 2020781) B2020781
theorem B4042385 : Blo 1196415 4042385 := bstep (se 2 (by rfl) ⟨1515894, by rfl⟩ : syracuseStep 4042385 = 3031789) B3031789
theorem B2272931 : Blo 1196415 2272931 := bstep (se 1 (by rfl) ⟨1704698, by rfl⟩ : syracuseStep 2272931 = 3409397) B3409397
theorem B6475427 : Blo 1196415 6475427 := bstep (se 1 (by rfl) ⟨4856570, by rfl⟩ : syracuseStep 6475427 = 9713141) B9713141
theorem B3411629 : Blo 1196415 3411629 := bstep (se 3 (by rfl) ⟨639680, by rfl⟩ : syracuseStep 3411629 = 1279361) B1279361
theorem B2019073 : Blo 1196415 2019073 := bstep (se 2 (by rfl) ⟨757152, by rfl⟩ : syracuseStep 2019073 = 1514305) B1514305
theorem B1969921 : Blo 1196415 1969921 := bstep (se 2 (by rfl) ⟨738720, by rfl⟩ : syracuseStep 1969921 = 1477441) B1477441
theorem B1347331 : Blo 1196415 1347331 := bstep (se 1 (by rfl) ⟨1010498, by rfl⟩ : syracuseStep 1347331 = 2020997) B2020997
theorem B2158339 : Blo 1196415 2158339 := bstep (se 1 (by rfl) ⟨1618754, by rfl⟩ : syracuseStep 2158339 = 3237509) B3237509
theorem B2019107 : Blo 1196415 2019107 := bstep (se 1 (by rfl) ⟨1514330, by rfl⟩ : syracuseStep 2019107 = 3028661) B3028661
theorem B6057827 : Blo 1196415 6057827 := bstep (se 1 (by rfl) ⟨4543370, by rfl⟩ : syracuseStep 6057827 = 9086741) B9086741
theorem B3411811 : Blo 1196415 3411811 := bstep (se 1 (by rfl) ⟨2558858, by rfl⟩ : syracuseStep 3411811 = 5117717) B5117717
theorem B3411857 : Blo 1196415 3411857 := bstep (se 2 (by rfl) ⟨1279446, by rfl⟩ : syracuseStep 3411857 = 2558893) B2558893
theorem B1347475 : Blo 1196415 1347475 := bstep (se 1 (by rfl) ⟨1010606, by rfl⟩ : syracuseStep 1347475 = 2021213) B2021213
theorem B2019235 : Blo 1196415 2019235 := bstep (se 1 (by rfl) ⟨1514426, by rfl⟩ : syracuseStep 2019235 = 3028853) B3028853
theorem B3837905 : Blo 1196415 3837905 := bstep (se 2 (by rfl) ⟨1439214, by rfl⟩ : syracuseStep 3837905 = 2878429) B2878429
theorem B1347619 : Blo 1196415 1347619 := bstep (se 1 (by rfl) ⟨1010714, by rfl⟩ : syracuseStep 1347619 = 2021429) B2021429
theorem B2019377 : Blo 1196415 2019377 := bstep (se 2 (by rfl) ⟨757266, by rfl⟩ : syracuseStep 2019377 = 1514533) B1514533
theorem B12447857 : Blo 1196415 12447857 := bstep (se 2 (by rfl) ⟨4667946, by rfl⟩ : syracuseStep 12447857 = 9335893) B9335893
theorem B1618067 : Blo 1196415 1618067 := bstep (se 1 (by rfl) ⟨1213550, by rfl⟩ : syracuseStep 1618067 = 2427101) B2427101
theorem B1437859 : Blo 1196415 1437859 := bstep (se 1 (by rfl) ⟨1078394, by rfl⟩ : syracuseStep 1437859 = 2156789) B2156789
theorem B4042925 : Blo 1196415 4042925 := bstep (se 3 (by rfl) ⟨758048, by rfl⟩ : syracuseStep 4042925 = 1516097) B1516097
theorem B2019505 : Blo 1196415 2019505 := bstep (se 2 (by rfl) ⟨757314, by rfl⟩ : syracuseStep 2019505 = 1514629) B1514629
theorem B1347763 : Blo 1196415 1347763 := bstep (se 1 (by rfl) ⟨1010822, by rfl⟩ : syracuseStep 1347763 = 2021645) B2021645
theorem B2019539 : Blo 1196415 2019539 := bstep (se 1 (by rfl) ⟨1514654, by rfl⟩ : syracuseStep 2019539 = 3029309) B3029309
theorem B3281123 : Blo 1196415 3281123 := bstep (se 1 (by rfl) ⟨2460842, by rfl⟩ : syracuseStep 3281123 = 4921685) B4921685
theorem B4042979 : Blo 1196415 4042979 := bstep (se 1 (by rfl) ⟨3032234, by rfl⟩ : syracuseStep 4042979 = 6064469) B6064469
theorem B7778609 : Blo 1196415 7778609 := bstep (se 2 (by rfl) ⟨2916978, by rfl⟩ : syracuseStep 7778609 = 5833957) B5833957
theorem B1347907 : Blo 1196415 1347907 := bstep (se 1 (by rfl) ⟨1010930, by rfl⟩ : syracuseStep 1347907 = 2021861) B2021861
theorem B2019667 : Blo 1196415 2019667 := bstep (se 1 (by rfl) ⟨1514750, by rfl⟩ : syracuseStep 2019667 = 3029501) B3029501
theorem B1348051 : Blo 1196415 1348051 := bstep (se 1 (by rfl) ⟨1011038, by rfl⟩ : syracuseStep 1348051 = 2022077) B2022077
theorem B2019809 : Blo 1196415 2019809 := bstep (se 2 (by rfl) ⟨757428, by rfl⟩ : syracuseStep 2019809 = 1514857) B1514857
theorem B4043249 : Blo 1196415 4043249 := bstep (se 2 (by rfl) ⟨1516218, by rfl⟩ : syracuseStep 4043249 = 3032437) B3032437
theorem B1438243 : Blo 1196415 1438243 := bstep (se 1 (by rfl) ⟨1078682, by rfl⟩ : syracuseStep 1438243 = 2157365) B2157365
theorem B2273827 : Blo 1196415 2273827 := bstep (se 1 (by rfl) ⟨1705370, by rfl⟩ : syracuseStep 2273827 = 3410741) B3410741
theorem B6066737 : Blo 1196415 6066737 := bstep (se 2 (by rfl) ⟨2275026, by rfl⟩ : syracuseStep 6066737 = 4550053) B4550053
theorem B2019937 : Blo 1196415 2019937 := bstep (se 2 (by rfl) ⟨757476, by rfl⟩ : syracuseStep 2019937 = 1514953) B1514953
theorem B1348195 : Blo 1196415 1348195 := bstep (se 1 (by rfl) ⟨1011146, by rfl⟩ : syracuseStep 1348195 = 2022293) B2022293
theorem B2019971 : Blo 1196415 2019971 := bstep (se 1 (by rfl) ⟨1514978, by rfl⟩ : syracuseStep 2019971 = 3029957) B3029957
theorem B3838595 : Blo 1196415 3838595 := bstep (se 1 (by rfl) ⟨2878946, by rfl⟩ : syracuseStep 3838595 = 5757893) B5757893
theorem B6058637 : Blo 1196415 6058637 := bstep (se 3 (by rfl) ⟨1135994, by rfl⟩ : syracuseStep 6058637 = 2271989) B2271989
theorem B2273987 : Blo 1196415 2273987 := bstep (se 1 (by rfl) ⟨1705490, by rfl⟩ : syracuseStep 2273987 = 3410981) B3410981
theorem B2020099 : Blo 1196415 2020099 := bstep (se 1 (by rfl) ⟨1515074, by rfl⟩ : syracuseStep 2020099 = 3030149) B3030149
theorem B6820685 : Blo 1196415 6820685 := bstep (se 3 (by rfl) ⟨1278878, by rfl⟩ : syracuseStep 6820685 = 2557757) B2557757
theorem B2159441 : Blo 1196415 2159441 := bstep (se 2 (by rfl) ⟨809790, by rfl⟩ : syracuseStep 2159441 = 1619581) B1619581
theorem B2691953 : Blo 1196415 2691953 := bstep (se 2 (by rfl) ⟨1009482, by rfl⟩ : syracuseStep 2691953 = 2018965) B2018965
theorem B6746993 : Blo 1196415 6746993 := bstep (se 2 (by rfl) ⟨2530122, by rfl⟩ : syracuseStep 6746993 = 5060245) B5060245
theorem B2691971 : Blo 1196415 2691971 := bstep (se 1 (by rfl) ⟨2018978, by rfl⟩ : syracuseStep 2691971 = 4037957) B4037957
theorem B15332237 : Blo 1196415 15332237 := bstep (se 3 (by rfl) ⟨2874794, by rfl⟩ : syracuseStep 15332237 = 5749589) B5749589
theorem B2020241 : Blo 1196415 2020241 := bstep (se 2 (by rfl) ⟨757590, by rfl⟩ : syracuseStep 2020241 = 1515181) B1515181
theorem B4043789 : Blo 1196415 4043789 := bstep (se 3 (by rfl) ⟨758210, by rfl⟩ : syracuseStep 4043789 = 1516421) B1516421
theorem B2020369 : Blo 1196415 2020369 := bstep (se 2 (by rfl) ⟨757638, by rfl⟩ : syracuseStep 2020369 = 1515277) B1515277
theorem B4543523 : Blo 1196415 4543523 := bstep (se 1 (by rfl) ⟨3407642, by rfl⟩ : syracuseStep 4543523 = 6815285) B6815285
theorem B2020403 : Blo 1196415 2020403 := bstep (se 1 (by rfl) ⟨1515302, by rfl⟩ : syracuseStep 2020403 = 3030605) B3030605
theorem B4043843 : Blo 1196415 4043843 := bstep (se 1 (by rfl) ⟨3032882, by rfl⟩ : syracuseStep 4043843 = 6065765) B6065765
theorem B1619041 : Blo 1196415 1619041 := bstep (se 2 (by rfl) ⟨607140, by rfl⟩ : syracuseStep 1619041 = 1214281) B1214281
theorem B3642499 : Blo 1196415 3642499 := bstep (se 1 (by rfl) ⟨2731874, by rfl⟩ : syracuseStep 3642499 = 5463749) B5463749
theorem B2692241 : Blo 1196415 2692241 := bstep (se 2 (by rfl) ⟨1009590, by rfl⟩ : syracuseStep 2692241 = 2019181) B2019181
theorem B2692259 : Blo 1196415 2692259 := bstep (se 1 (by rfl) ⟨2019194, by rfl⟩ : syracuseStep 2692259 = 4038389) B4038389
theorem B2020531 : Blo 1196415 2020531 := bstep (se 1 (by rfl) ⟨1515398, by rfl⟩ : syracuseStep 2020531 = 3030797) B3030797
theorem B2020673 : Blo 1196415 2020673 := bstep (se 2 (by rfl) ⟨757752, by rfl⟩ : syracuseStep 2020673 = 1515505) B1515505
theorem B4044113 : Blo 1196415 4044113 := bstep (se 2 (by rfl) ⟨1516542, by rfl⟩ : syracuseStep 4044113 = 3033085) B3033085
theorem B2692529 : Blo 1196415 2692529 := bstep (se 2 (by rfl) ⟨1009698, by rfl⟩ : syracuseStep 2692529 = 2019397) B2019397
theorem B4609457 : Blo 1196415 4609457 := bstep (se 2 (by rfl) ⟨1728546, by rfl⟩ : syracuseStep 4609457 = 3457093) B3457093
theorem B2020801 : Blo 1196415 2020801 := bstep (se 2 (by rfl) ⟨757800, by rfl⟩ : syracuseStep 2020801 = 1515601) B1515601
theorem B2692547 : Blo 1196415 2692547 := bstep (se 1 (by rfl) ⟨2019410, by rfl⟩ : syracuseStep 2692547 = 4038821) B4038821
theorem B2020835 : Blo 1196415 2020835 := bstep (se 1 (by rfl) ⟨1515626, by rfl⟩ : syracuseStep 2020835 = 3031253) B3031253
theorem B3028529 : Blo 1196415 3028529 := bstep (se 2 (by rfl) ⟨1135698, by rfl⟩ : syracuseStep 3028529 = 2271397) B2271397
theorem B9090629 : Blo 1196415 9090629 := bstep (se 4 (by rfl) ⟨852246, by rfl⟩ : syracuseStep 9090629 = 1704493) B1704493
theorem B2020963 : Blo 1196415 2020963 := bstep (se 1 (by rfl) ⟨1515722, by rfl⟩ : syracuseStep 2020963 = 3031445) B3031445
theorem B12285553 : Blo 1196415 12285553 := bstep (se 2 (by rfl) ⟨4607082, by rfl⟩ : syracuseStep 12285553 = 9214165) B9214165
theorem B2692817 : Blo 1196415 2692817 := bstep (se 2 (by rfl) ⟨1009806, by rfl⟩ : syracuseStep 2692817 = 2019613) B2019613
theorem B2692835 : Blo 1196415 2692835 := bstep (se 1 (by rfl) ⟨2019626, by rfl⟩ : syracuseStep 2692835 = 4039253) B4039253
theorem B10229489 : Blo 1196415 10229489 := bstep (se 2 (by rfl) ⟨3836058, by rfl⟩ : syracuseStep 10229489 = 7672117) B7672117
theorem B2021105 : Blo 1196415 2021105 := bstep (se 2 (by rfl) ⟨757914, by rfl⟩ : syracuseStep 2021105 = 1515829) B1515829
theorem B6821617 : Blo 1196415 6821617 := bstep (se 2 (by rfl) ⟨2558106, by rfl⟩ : syracuseStep 6821617 = 5116213) B5116213
theorem B2275057 : Blo 1196415 2275057 := bstep (se 2 (by rfl) ⟨853146, by rfl⟩ : syracuseStep 2275057 = 1706293) B1706293
theorem B4855565 : Blo 1196415 4855565 := bstep (se 3 (by rfl) ⟨910418, by rfl⟩ : syracuseStep 4855565 = 1820837) B1820837
theorem B9836387 : Blo 1196415 9836387 := bstep (se 1 (by rfl) ⟨7377290, by rfl⟩ : syracuseStep 9836387 = 14754581) B14754581
theorem B4044653 : Blo 1196415 4044653 := bstep (se 3 (by rfl) ⟨758372, by rfl⟩ : syracuseStep 4044653 = 1516745) B1516745
theorem B2021233 : Blo 1196415 2021233 := bstep (se 2 (by rfl) ⟨757962, by rfl⟩ : syracuseStep 2021233 = 1515925) B1515925
theorem B2021267 : Blo 1196415 2021267 := bstep (se 1 (by rfl) ⟨1515950, by rfl⟩ : syracuseStep 2021267 = 3031901) B3031901
theorem B2693105 : Blo 1196415 2693105 := bstep (se 2 (by rfl) ⟨1009914, by rfl⟩ : syracuseStep 2693105 = 2019829) B2019829
theorem B2693123 : Blo 1196415 2693123 := bstep (se 1 (by rfl) ⟨2019842, by rfl⟩ : syracuseStep 2693123 = 4039685) B4039685
theorem B4544525 : Blo 1196415 4544525 := bstep (se 3 (by rfl) ⟨852098, by rfl⟩ : syracuseStep 4544525 = 1704197) B1704197
theorem B2021395 : Blo 1196415 2021395 := bstep (se 1 (by rfl) ⟨1516046, by rfl⟩ : syracuseStep 2021395 = 3032093) B3032093
theorem B4610147 : Blo 1196415 4610147 := bstep (se 1 (by rfl) ⟨3457610, by rfl⟩ : syracuseStep 4610147 = 6915221) B6915221
theorem B3643501 : Blo 1196415 3643501 := bstep (se 3 (by rfl) ⟨683156, by rfl⟩ : syracuseStep 3643501 = 1366313) B1366313
theorem B9099377 : Blo 1196415 9099377 := bstep (se 2 (by rfl) ⟨3412266, by rfl⟩ : syracuseStep 9099377 = 6824533) B6824533
theorem B2021537 : Blo 1196415 2021537 := bstep (se 2 (by rfl) ⟨758076, by rfl⟩ : syracuseStep 2021537 = 1516153) B1516153
theorem B4921613 : Blo 1196415 4921613 := bstep (se 3 (by rfl) ⟨922802, by rfl⟩ : syracuseStep 4921613 = 1845605) B1845605
theorem B2693393 : Blo 1196415 2693393 := bstep (se 2 (by rfl) ⟨1010022, by rfl⟩ : syracuseStep 2693393 = 2020045) B2020045
theorem B2021665 : Blo 1196415 2021665 := bstep (se 2 (by rfl) ⟨758124, by rfl⟩ : syracuseStep 2021665 = 1516249) B1516249
theorem B2693411 : Blo 1196415 2693411 := bstep (se 1 (by rfl) ⟨2020058, by rfl⟩ : syracuseStep 2693411 = 4040117) B4040117
theorem B2021699 : Blo 1196415 2021699 := bstep (se 1 (by rfl) ⟨1516274, by rfl⟩ : syracuseStep 2021699 = 3032549) B3032549
theorem B3455405 : Blo 1196415 3455405 := bstep (se 3 (by rfl) ⟨647888, by rfl⟩ : syracuseStep 3455405 = 1295777) B1295777
theorem B2021827 : Blo 1196415 2021827 := bstep (se 1 (by rfl) ⟨1516370, by rfl⟩ : syracuseStep 2021827 = 3032741) B3032741
theorem B3029521 : Blo 1196415 3029521 := bstep (se 2 (by rfl) ⟨1136070, by rfl⟩ : syracuseStep 3029521 = 2272141) B2272141
theorem B2693681 : Blo 1196415 2693681 := bstep (se 2 (by rfl) ⟨1010130, by rfl⟩ : syracuseStep 2693681 = 2020261) B2020261
theorem B2693699 : Blo 1196415 2693699 := bstep (se 1 (by rfl) ⟨2020274, by rfl⟩ : syracuseStep 2693699 = 4040549) B4040549
theorem B2021969 : Blo 1196415 2021969 := bstep (se 2 (by rfl) ⟨758238, by rfl⟩ : syracuseStep 2021969 = 1516477) B1516477
theorem B8190563 : Blo 1196415 8190563 := bstep (se 1 (by rfl) ⟨6142922, by rfl⟩ : syracuseStep 8190563 = 12285845) B12285845
theorem B6650531 : Blo 1196415 6650531 := bstep (se 1 (by rfl) ⟨4987898, by rfl⟩ : syracuseStep 6650531 = 9975797) B9975797
theorem B2022097 : Blo 1196415 2022097 := bstep (se 2 (by rfl) ⟨758286, by rfl⟩ : syracuseStep 2022097 = 1516573) B1516573
theorem B2022131 : Blo 1196415 2022131 := bstep (se 1 (by rfl) ⟨1516598, by rfl⟩ : syracuseStep 2022131 = 3033197) B3033197
theorem B3029795 : Blo 1196415 3029795 := bstep (se 1 (by rfl) ⟨2272346, by rfl⟩ : syracuseStep 3029795 = 4544693) B4544693
theorem B2693969 : Blo 1196415 2693969 := bstep (se 2 (by rfl) ⟨1010238, by rfl⟩ : syracuseStep 2693969 = 2020477) B2020477
theorem B2693987 : Blo 1196415 2693987 := bstep (se 1 (by rfl) ⟨2020490, by rfl⟩ : syracuseStep 2693987 = 4040981) B4040981
theorem B2022259 : Blo 1196415 2022259 := bstep (se 1 (by rfl) ⟨1516694, by rfl⟩ : syracuseStep 2022259 = 3033389) B3033389
theorem B1514371 : Blo 1196415 1514371 := bstep (se 1 (by rfl) ⟨1135778, by rfl⟩ : syracuseStep 1514371 = 2271557) B2271557
theorem B1514467 : Blo 1196415 1514467 := bstep (se 1 (by rfl) ⟨1135850, by rfl⟩ : syracuseStep 1514467 = 2271701) B2271701
theorem B3029987 : Blo 1196415 3029987 := bstep (se 1 (by rfl) ⟨2272490, by rfl⟩ : syracuseStep 3029987 = 4544981) B4544981
theorem B5118947 : Blo 1196415 5118947 := bstep (se 1 (by rfl) ⟨3839210, by rfl⟩ : syracuseStep 5118947 = 7678421) B7678421
theorem B147881045 : Blo 1196415 147881045 := bstep (se 8 (by rfl) ⟨866490, by rfl⟩ : syracuseStep 147881045 = 1732981) B1732981
theorem B5110883 : Blo 1196415 5110883 := bstep (se 1 (by rfl) ⟨3833162, by rfl⟩ : syracuseStep 5110883 = 7666325) B7666325
theorem B2694257 : Blo 1196415 2694257 := bstep (se 2 (by rfl) ⟨1010346, by rfl⟩ : syracuseStep 2694257 = 2020693) B2020693
theorem B2694275 : Blo 1196415 2694275 := bstep (se 1 (by rfl) ⟨2020706, by rfl⟩ : syracuseStep 2694275 = 4041413) B4041413
theorem B6814853 : Blo 1196415 6814853 := bstep (se 4 (by rfl) ⟨638892, by rfl⟩ : syracuseStep 6814853 = 1277785) B1277785
theorem B6823075 : Blo 1196415 6823075 := bstep (se 1 (by rfl) ⟨5117306, by rfl⟩ : syracuseStep 6823075 = 10234613) B10234613
theorem B2104577 : Blo 1196415 2104577 := bstep (se 2 (by rfl) ⟨789216, by rfl⟩ : syracuseStep 2104577 = 1578433) B1578433
theorem B6561101 : Blo 1196415 6561101 := bstep (se 3 (by rfl) ⟨1230206, by rfl⟩ : syracuseStep 6561101 = 2460413) B2460413
theorem B2047315 : Blo 1196415 2047315 := bstep (se 1 (by rfl) ⟨1535486, by rfl⟩ : syracuseStep 2047315 = 3070973) B3070973
theorem B5750129 : Blo 1196415 5750129 := bstep (se 2 (by rfl) ⟨2156298, by rfl⟩ : syracuseStep 5750129 = 4312597) B4312597
theorem B2694545 : Blo 1196415 2694545 := bstep (se 2 (by rfl) ⟨1010454, by rfl⟩ : syracuseStep 2694545 = 2020909) B2020909
theorem B2694563 : Blo 1196415 2694563 := bstep (se 1 (by rfl) ⟨2020922, by rfl⟩ : syracuseStep 2694563 = 4041845) B4041845
theorem B4038065 : Blo 1196415 4038065 := bstep (se 2 (by rfl) ⟨1514274, by rfl⟩ : syracuseStep 4038065 = 3028549) B3028549
theorem B1514963 : Blo 1196415 1514963 := bstep (se 1 (by rfl) ⟨1136222, by rfl⟩ : syracuseStep 1514963 = 2272445) B2272445
theorem B6061553 : Blo 1196415 6061553 := bstep (se 2 (by rfl) ⟨2273082, by rfl⟩ : syracuseStep 6061553 = 4546165) B4546165
theorem B2555459 : Blo 1196415 2555459 := bstep (se 1 (by rfl) ⟨1916594, by rfl⟩ : syracuseStep 2555459 = 3833189) B3833189
theorem B3407437 : Blo 1196415 3407437 := bstep (se 3 (by rfl) ⟨638894, by rfl⟩ : syracuseStep 3407437 = 1277789) B1277789
theorem B2694833 : Blo 1196415 2694833 := bstep (se 2 (by rfl) ⟨1010562, by rfl⟩ : syracuseStep 2694833 = 2021125) B2021125
theorem B6823601 : Blo 1196415 6823601 := bstep (se 2 (by rfl) ⟨2558850, by rfl⟩ : syracuseStep 6823601 = 5117701) B5117701
theorem B2694851 : Blo 1196415 2694851 := bstep (se 1 (by rfl) ⟨2021138, by rfl⟩ : syracuseStep 2694851 = 4042277) B4042277
theorem B1728211 : Blo 1196415 1728211 := bstep (se 1 (by rfl) ⟨1296158, by rfl⟩ : syracuseStep 1728211 = 2592317) B2592317
theorem B11501297 : Blo 1196415 11501297 := bstep (se 2 (by rfl) ⟨4312986, by rfl⟩ : syracuseStep 11501297 = 8625973) B8625973
theorem B2875171 : Blo 1196415 2875171 := bstep (se 1 (by rfl) ⟨2156378, by rfl⟩ : syracuseStep 2875171 = 4312757) B4312757
theorem B3407665 : Blo 1196415 3407665 := bstep (se 2 (by rfl) ⟨1277874, by rfl⟩ : syracuseStep 3407665 = 2555749) B2555749
theorem B3030929 : Blo 1196415 3030929 := bstep (se 2 (by rfl) ⟨1136598, by rfl⟩ : syracuseStep 3030929 = 2273197) B2273197
theorem B3833777 : Blo 1196415 3833777 := bstep (se 2 (by rfl) ⟨1437666, by rfl⟩ : syracuseStep 3833777 = 2875333) B2875333
theorem B3030979 : Blo 1196415 3030979 := bstep (se 1 (by rfl) ⟨2273234, by rfl⟩ : syracuseStep 3030979 = 4546469) B4546469
theorem B4038605 : Blo 1196415 4038605 := bstep (se 3 (by rfl) ⟨757238, by rfl⟩ : syracuseStep 4038605 = 1514477) B1514477
theorem B3407825 : Blo 1196415 3407825 := bstep (se 2 (by rfl) ⟨1277934, by rfl⟩ : syracuseStep 3407825 = 2555869) B2555869
theorem B2695121 : Blo 1196415 2695121 := bstep (se 2 (by rfl) ⟨1010670, by rfl⟩ : syracuseStep 2695121 = 2021341) B2021341
theorem B2695139 : Blo 1196415 2695139 := bstep (se 1 (by rfl) ⟨2021354, by rfl⟩ : syracuseStep 2695139 = 4042709) B4042709
theorem B2695193 : Blo 1196415 2695193 := bstep (se 2 (by rfl) ⟨1010697, by rfl⟩ : syracuseStep 2695193 = 2021395) B2021395
theorem B3031091 : Blo 1196415 3031091 := bstep (se 1 (by rfl) ⟨2273318, by rfl⟩ : syracuseStep 3031091 = 4546637) B4546637
theorem B8298571 : Blo 1196415 8298571 := bstep (se 1 (by rfl) ⟨6223928, by rfl⟩ : syracuseStep 8298571 = 12447857) B12447857
theorem B2695283 : Blo 1196415 2695283 := bstep (se 1 (by rfl) ⟨2021462, by rfl⟩ : syracuseStep 2695283 = 4042925) B4042925
theorem B4858001 : Blo 1196415 4858001 := bstep (se 2 (by rfl) ⟨1821750, by rfl⟩ : syracuseStep 4858001 = 3643501) B3643501
theorem B2187415 : Blo 1196415 2187415 := bstep (se 1 (by rfl) ⟨1640561, by rfl⟩ : syracuseStep 2187415 = 3281123) B3281123
theorem B2695319 : Blo 1196415 2695319 := bstep (se 1 (by rfl) ⟨2021489, by rfl⟩ : syracuseStep 2695319 = 4042979) B4042979
theorem B3408065 : Blo 1196415 3408065 := bstep (se 2 (by rfl) ⟨1278024, by rfl⟩ : syracuseStep 3408065 = 2556049) B2556049
theorem B5112011 : Blo 1196415 5112011 := bstep (se 1 (by rfl) ⟨3834008, by rfl⟩ : syracuseStep 5112011 = 7668017) B7668017
theorem B5185739 : Blo 1196415 5185739 := bstep (se 1 (by rfl) ⟨3889304, by rfl⟩ : syracuseStep 5185739 = 7778609) B7778609
theorem B1917145 : Blo 1196415 1917145 := bstep (se 2 (by rfl) ⟨718929, by rfl⟩ : syracuseStep 1917145 = 1437859) B1437859
theorem B1278199 : Blo 1196415 1278199 := bstep (se 1 (by rfl) ⟨958649, by rfl⟩ : syracuseStep 1278199 = 1917299) B1917299
theorem B2556211 : Blo 1196415 2556211 := bstep (se 1 (by rfl) ⟨1917158, by rfl⟩ : syracuseStep 2556211 = 3834317) B3834317
theorem B2695499 : Blo 1196415 2695499 := bstep (se 1 (by rfl) ⟨2021624, by rfl⟩ : syracuseStep 2695499 = 4043249) B4043249
theorem B2695553 : Blo 1196415 2695553 := bstep (se 2 (by rfl) ⟨1010832, by rfl⟩ : syracuseStep 2695553 = 2021665) B2021665
theorem B1196427 : Blo 1196415 1196427 := bstep (se 1 (by rfl) ⟨897320, by rfl⟩ : syracuseStep 1196427 = 1794641) B1794641
theorem B1196439 : Blo 1196415 1196439 := bstep (se 1 (by rfl) ⟨897329, by rfl⟩ : syracuseStep 1196439 = 1794659) B1794659
theorem B1196459 : Blo 1196415 1196459 := bstep (se 1 (by rfl) ⟨897344, by rfl⟩ : syracuseStep 1196459 = 1794689) B1794689
theorem B1278379 : Blo 1196415 1278379 := bstep (se 1 (by rfl) ⟨958784, by rfl⟩ : syracuseStep 1278379 = 1917569) B1917569
theorem B4039091 : Blo 1196415 4039091 := bstep (se 1 (by rfl) ⟨3029318, by rfl⟩ : syracuseStep 4039091 = 6058637) B6058637
theorem B1196471 : Blo 1196415 1196471 := bstep (se 1 (by rfl) ⟨897353, by rfl⟩ : syracuseStep 1196471 = 1794707) B1794707
theorem B1196491 : Blo 1196415 1196491 := bstep (se 1 (by rfl) ⟨897368, by rfl⟩ : syracuseStep 1196491 = 1794737) B1794737
theorem B1196503 : Blo 1196415 1196503 := bstep (se 1 (by rfl) ⟨897377, by rfl⟩ : syracuseStep 1196503 = 1794755) B1794755
theorem B1515991 : Blo 1196415 1515991 := bstep (se 1 (by rfl) ⟨1136993, by rfl⟩ : syracuseStep 1515991 = 2273987) B2273987
theorem B10224089 : Blo 1196415 10224089 := bstep (se 2 (by rfl) ⟨3834033, by rfl⟩ : syracuseStep 10224089 = 7668067) B7668067
theorem B12288473 : Blo 1196415 12288473 := bstep (se 2 (by rfl) ⟨4608177, by rfl⟩ : syracuseStep 12288473 = 9216355) B9216355
theorem B1196523 : Blo 1196415 1196523 := bstep (se 1 (by rfl) ⟨897392, by rfl⟩ : syracuseStep 1196523 = 1794785) B1794785
theorem B1196535 : Blo 1196415 1196535 := bstep (se 1 (by rfl) ⟨897401, by rfl⟩ : syracuseStep 1196535 = 1794803) B1794803
theorem B1196555 : Blo 1196415 1196555 := bstep (se 1 (by rfl) ⟨897416, by rfl⟩ : syracuseStep 1196555 = 1794833) B1794833
theorem B1196567 : Blo 1196415 1196567 := bstep (se 1 (by rfl) ⟨897425, by rfl⟩ : syracuseStep 1196567 = 1794851) B1794851
theorem B1196587 : Blo 1196415 1196587 := bstep (se 1 (by rfl) ⟨897440, by rfl⟩ : syracuseStep 1196587 = 1794881) B1794881
theorem B4547123 : Blo 1196415 4547123 := bstep (se 1 (by rfl) ⟨3410342, by rfl⟩ : syracuseStep 4547123 = 6820685) B6820685
theorem B1196599 : Blo 1196415 1196599 := bstep (se 1 (by rfl) ⟨897449, by rfl⟩ : syracuseStep 1196599 = 1794899) B1794899
theorem B4547137 : Blo 1196415 4547137 := bstep (se 2 (by rfl) ⟨1705176, by rfl⟩ : syracuseStep 4547137 = 3410353) B3410353
theorem B1794635 : Blo 1196415 1794635 := bstep (se 1 (by rfl) ⟨1345976, by rfl⟩ : syracuseStep 1794635 = 2691953) B2691953
theorem B1196619 : Blo 1196415 1196619 := bstep (se 1 (by rfl) ⟨897464, by rfl⟩ : syracuseStep 1196619 = 1794929) B1794929
theorem B3031627 : Blo 1196415 3031627 := bstep (se 1 (by rfl) ⟨2273720, by rfl⟩ : syracuseStep 3031627 = 4547441) B4547441
theorem B4497995 : Blo 1196415 4497995 := bstep (se 1 (by rfl) ⟨3373496, by rfl⟩ : syracuseStep 4497995 = 6746993) B6746993
theorem B1794647 : Blo 1196415 1794647 := bstep (se 1 (by rfl) ⟨1345985, by rfl⟩ : syracuseStep 1794647 = 2691971) B2691971
theorem B1196631 : Blo 1196415 1196631 := bstep (se 1 (by rfl) ⟨897473, by rfl⟩ : syracuseStep 1196631 = 1794947) B1794947
theorem B2695769 : Blo 1196415 2695769 := bstep (se 2 (by rfl) ⟨1010913, by rfl⟩ : syracuseStep 2695769 = 2021827) B2021827
theorem B1196651 : Blo 1196415 1196651 := bstep (se 1 (by rfl) ⟨897488, by rfl⟩ : syracuseStep 1196651 = 1794977) B1794977
theorem B1196663 : Blo 1196415 1196663 := bstep (se 1 (by rfl) ⟨897497, by rfl⟩ : syracuseStep 1196663 = 1794995) B1794995
theorem B1196683 : Blo 1196415 1196683 := bstep (se 1 (by rfl) ⟨897512, by rfl⟩ : syracuseStep 1196683 = 1795025) B1795025
theorem B1196695 : Blo 1196415 1196695 := bstep (se 1 (by rfl) ⟨897521, by rfl⟩ : syracuseStep 1196695 = 1795043) B1795043
theorem B1794713 : Blo 1196415 1794713 := bstep (se 2 (by rfl) ⟨673017, by rfl⟩ : syracuseStep 1794713 = 1346035) B1346035
theorem B2556569 : Blo 1196415 2556569 := bstep (se 2 (by rfl) ⟨958713, by rfl⟩ : syracuseStep 2556569 = 1917427) B1917427
theorem B1196715 : Blo 1196415 1196715 := bstep (se 1 (by rfl) ⟨897536, by rfl⟩ : syracuseStep 1196715 = 1795073) B1795073
theorem B2695859 : Blo 1196415 2695859 := bstep (se 1 (by rfl) ⟨2021894, by rfl⟩ : syracuseStep 2695859 = 4043789) B4043789
theorem B1196727 : Blo 1196415 1196727 := bstep (se 1 (by rfl) ⟨897545, by rfl⟩ : syracuseStep 1196727 = 1795091) B1795091
theorem B4039361 : Blo 1196415 4039361 := bstep (se 2 (by rfl) ⟨1514760, by rfl⟩ : syracuseStep 4039361 = 3029521) B3029521
theorem B1196747 : Blo 1196415 1196747 := bstep (se 1 (by rfl) ⟨897560, by rfl⟩ : syracuseStep 1196747 = 1795121) B1795121
theorem B1196759 : Blo 1196415 1196759 := bstep (se 1 (by rfl) ⟨897569, by rfl⟩ : syracuseStep 1196759 = 1795139) B1795139
theorem B2695895 : Blo 1196415 2695895 := bstep (se 1 (by rfl) ⟨2021921, by rfl⟩ : syracuseStep 2695895 = 4043843) B4043843
theorem B3031769 : Blo 1196415 3031769 := bstep (se 2 (by rfl) ⟨1136913, by rfl⟩ : syracuseStep 3031769 = 2273827) B2273827
theorem B1196779 : Blo 1196415 1196779 := bstep (se 1 (by rfl) ⟨897584, by rfl⟩ : syracuseStep 1196779 = 1795169) B1795169
theorem B1196791 : Blo 1196415 1196791 := bstep (se 1 (by rfl) ⟨897593, by rfl⟩ : syracuseStep 1196791 = 1795187) B1795187
theorem B1794827 : Blo 1196415 1794827 := bstep (se 1 (by rfl) ⟨1346120, by rfl⟩ : syracuseStep 1794827 = 2692241) B2692241
theorem B1196811 : Blo 1196415 1196811 := bstep (se 1 (by rfl) ⟨897608, by rfl⟩ : syracuseStep 1196811 = 1795217) B1795217
theorem B1794839 : Blo 1196415 1794839 := bstep (se 1 (by rfl) ⟨1346129, by rfl⟩ : syracuseStep 1794839 = 2692259) B2692259
theorem B1196823 : Blo 1196415 1196823 := bstep (se 1 (by rfl) ⟨897617, by rfl⟩ : syracuseStep 1196823 = 1795235) B1795235
theorem B1196843 : Blo 1196415 1196843 := bstep (se 1 (by rfl) ⟨897632, by rfl⟩ : syracuseStep 1196843 = 1795265) B1795265
theorem B1196855 : Blo 1196415 1196855 := bstep (se 1 (by rfl) ⟨897641, by rfl⟩ : syracuseStep 1196855 = 1795283) B1795283
theorem B1196875 : Blo 1196415 1196875 := bstep (se 1 (by rfl) ⟨897656, by rfl⟩ : syracuseStep 1196875 = 1795313) B1795313
theorem B1196887 : Blo 1196415 1196887 := bstep (se 1 (by rfl) ⟨897665, by rfl⟩ : syracuseStep 1196887 = 1795331) B1795331
theorem B1794905 : Blo 1196415 1794905 := bstep (se 2 (by rfl) ⟨673089, by rfl⟩ : syracuseStep 1794905 = 1346179) B1346179
theorem B1196907 : Blo 1196415 1196907 := bstep (se 1 (by rfl) ⟨897680, by rfl⟩ : syracuseStep 1196907 = 1795361) B1795361
theorem B1196919 : Blo 1196415 1196919 := bstep (se 1 (by rfl) ⟨897689, by rfl⟩ : syracuseStep 1196919 = 1795379) B1795379
theorem B1196939 : Blo 1196415 1196939 := bstep (se 1 (by rfl) ⟨897704, by rfl⟩ : syracuseStep 1196939 = 1795409) B1795409
theorem B2696075 : Blo 1196415 2696075 := bstep (se 1 (by rfl) ⟨2022056, by rfl⟩ : syracuseStep 2696075 = 4044113) B4044113
theorem B1196951 : Blo 1196415 1196951 := bstep (se 1 (by rfl) ⟨897713, by rfl⟩ : syracuseStep 1196951 = 1795427) B1795427
theorem B1196971 : Blo 1196415 1196971 := bstep (se 1 (by rfl) ⟨897728, by rfl⟩ : syracuseStep 1196971 = 1795457) B1795457
theorem B3834803 : Blo 1196415 3834803 := bstep (se 1 (by rfl) ⟨2876102, by rfl⟩ : syracuseStep 3834803 = 5752205) B5752205
theorem B1196983 : Blo 1196415 1196983 := bstep (se 1 (by rfl) ⟨897737, by rfl⟩ : syracuseStep 1196983 = 1795475) B1795475
theorem B2696129 : Blo 1196415 2696129 := bstep (se 2 (by rfl) ⟨1011048, by rfl⟩ : syracuseStep 2696129 = 2022097) B2022097
theorem B1795019 : Blo 1196415 1795019 := bstep (se 1 (by rfl) ⟨1346264, by rfl⟩ : syracuseStep 1795019 = 2692529) B2692529
theorem B1197003 : Blo 1196415 1197003 := bstep (se 1 (by rfl) ⟨897752, by rfl⟩ : syracuseStep 1197003 = 1795505) B1795505
theorem B3072971 : Blo 1196415 3072971 := bstep (se 1 (by rfl) ⟨2304728, by rfl⟩ : syracuseStep 3072971 = 4609457) B4609457
theorem B1795031 : Blo 1196415 1795031 := bstep (se 1 (by rfl) ⟨1346273, by rfl⟩ : syracuseStep 1795031 = 2692547) B2692547
theorem B1197015 : Blo 1196415 1197015 := bstep (se 1 (by rfl) ⟨897761, by rfl⟩ : syracuseStep 1197015 = 1795523) B1795523
theorem B1197035 : Blo 1196415 1197035 := bstep (se 1 (by rfl) ⟨897776, by rfl⟩ : syracuseStep 1197035 = 1795553) B1795553
theorem B1197047 : Blo 1196415 1197047 := bstep (se 1 (by rfl) ⟨897785, by rfl⟩ : syracuseStep 1197047 = 1795571) B1795571
theorem B10232837 : Blo 1196415 10232837 := bstep (se 4 (by rfl) ⟨959328, by rfl⟩ : syracuseStep 10232837 = 1918657) B1918657
theorem B1197067 : Blo 1196415 1197067 := bstep (se 1 (by rfl) ⟨897800, by rfl⟩ : syracuseStep 1197067 = 1795601) B1795601
theorem B1197079 : Blo 1196415 1197079 := bstep (se 1 (by rfl) ⟨897809, by rfl⟩ : syracuseStep 1197079 = 1795619) B1795619
theorem B1795097 : Blo 1196415 1795097 := bstep (se 2 (by rfl) ⟨673161, by rfl⟩ : syracuseStep 1795097 = 1346323) B1346323
theorem B1197099 : Blo 1196415 1197099 := bstep (se 1 (by rfl) ⟨897824, by rfl⟩ : syracuseStep 1197099 = 1795649) B1795649
theorem B1197111 : Blo 1196415 1197111 := bstep (se 1 (by rfl) ⟨897833, by rfl⟩ : syracuseStep 1197111 = 1795667) B1795667
theorem B1197131 : Blo 1196415 1197131 := bstep (se 1 (by rfl) ⟨897848, by rfl⟩ : syracuseStep 1197131 = 1795697) B1795697
theorem B1197143 : Blo 1196415 1197143 := bstep (se 1 (by rfl) ⟨897857, by rfl⟩ : syracuseStep 1197143 = 1795715) B1795715
theorem B1197163 : Blo 1196415 1197163 := bstep (se 1 (by rfl) ⟨897872, by rfl⟩ : syracuseStep 1197163 = 1795745) B1795745
theorem B1213547 : Blo 1196415 1213547 := bstep (se 1 (by rfl) ⟨910160, by rfl⟩ : syracuseStep 1213547 = 1820321) B1820321
theorem B1197175 : Blo 1196415 1197175 := bstep (se 1 (by rfl) ⟨897881, by rfl⟩ : syracuseStep 1197175 = 1795763) B1795763
theorem B1795211 : Blo 1196415 1795211 := bstep (se 1 (by rfl) ⟨1346408, by rfl⟩ : syracuseStep 1795211 = 2692817) B2692817
theorem B1197195 : Blo 1196415 1197195 := bstep (se 1 (by rfl) ⟨897896, by rfl⟩ : syracuseStep 1197195 = 1795793) B1795793
theorem B1795223 : Blo 1196415 1795223 := bstep (se 1 (by rfl) ⟨1346417, by rfl⟩ : syracuseStep 1795223 = 2692835) B2692835
theorem B1197207 : Blo 1196415 1197207 := bstep (se 1 (by rfl) ⟨897905, by rfl⟩ : syracuseStep 1197207 = 1795811) B1795811
theorem B2696345 : Blo 1196415 2696345 := bstep (se 2 (by rfl) ⟨1011129, by rfl⟩ : syracuseStep 2696345 = 2022259) B2022259
theorem B1197227 : Blo 1196415 1197227 := bstep (se 1 (by rfl) ⟨897920, by rfl⟩ : syracuseStep 1197227 = 1795841) B1795841
theorem B3237043 : Blo 1196415 3237043 := bstep (se 1 (by rfl) ⟨2427782, by rfl⟩ : syracuseStep 3237043 = 4855565) B4855565
theorem B1197239 : Blo 1196415 1197239 := bstep (se 1 (by rfl) ⟨897929, by rfl⟩ : syracuseStep 1197239 = 1795859) B1795859
theorem B1197259 : Blo 1196415 1197259 := bstep (se 1 (by rfl) ⟨897944, by rfl⟩ : syracuseStep 1197259 = 1795889) B1795889
theorem B1197271 : Blo 1196415 1197271 := bstep (se 1 (by rfl) ⟨897953, by rfl⟩ : syracuseStep 1197271 = 1795907) B1795907
theorem B1795289 : Blo 1196415 1795289 := bstep (se 2 (by rfl) ⟨673233, by rfl⟩ : syracuseStep 1795289 = 1346467) B1346467
theorem B4039901 : Blo 1196415 4039901 := bstep (se 3 (by rfl) ⟨757481, by rfl⟩ : syracuseStep 4039901 = 1514963) B1514963
theorem B3237085 : Blo 1196415 3237085 := bstep (se 3 (by rfl) ⟨606953, by rfl⟩ : syracuseStep 3237085 = 1213907) B1213907
theorem B1197291 : Blo 1196415 1197291 := bstep (se 1 (by rfl) ⟨897968, by rfl⟩ : syracuseStep 1197291 = 1795937) B1795937
theorem B2696435 : Blo 1196415 2696435 := bstep (se 1 (by rfl) ⟨2022326, by rfl⟩ : syracuseStep 2696435 = 4044653) B4044653
theorem B1197303 : Blo 1196415 1197303 := bstep (se 1 (by rfl) ⟨897977, by rfl⟩ : syracuseStep 1197303 = 1795955) B1795955
theorem B1197323 : Blo 1196415 1197323 := bstep (se 1 (by rfl) ⟨897992, by rfl⟩ : syracuseStep 1197323 = 1795985) B1795985
theorem B8750353 : Blo 1196415 8750353 := bstep (se 2 (by rfl) ⟨3281382, by rfl⟩ : syracuseStep 8750353 = 6562765) B6562765
theorem B1246487 : Blo 1196415 1246487 := bstep (se 1 (by rfl) ⟨934865, by rfl⟩ : syracuseStep 1246487 = 1869731) B1869731
theorem B1197335 : Blo 1196415 1197335 := bstep (se 1 (by rfl) ⟨898001, by rfl⟩ : syracuseStep 1197335 = 1796003) B1796003
theorem B1197355 : Blo 1196415 1197355 := bstep (se 1 (by rfl) ⟨898016, by rfl⟩ : syracuseStep 1197355 = 1796033) B1796033
theorem B1197367 : Blo 1196415 1197367 := bstep (se 1 (by rfl) ⟨898025, by rfl⟩ : syracuseStep 1197367 = 1796051) B1796051
theorem B3835201 : Blo 1196415 3835201 := bstep (se 2 (by rfl) ⟨1438200, by rfl⟩ : syracuseStep 3835201 = 2876401) B2876401
theorem B2876737 : Blo 1196415 2876737 := bstep (se 2 (by rfl) ⟨1078776, by rfl⟩ : syracuseStep 2876737 = 2157553) B2157553
theorem B1795403 : Blo 1196415 1795403 := bstep (se 1 (by rfl) ⟨1346552, by rfl⟩ : syracuseStep 1795403 = 2693105) B2693105
theorem B1197387 : Blo 1196415 1197387 := bstep (se 1 (by rfl) ⟨898040, by rfl⟩ : syracuseStep 1197387 = 1796081) B1796081
theorem B1795415 : Blo 1196415 1795415 := bstep (se 1 (by rfl) ⟨1346561, by rfl⟩ : syracuseStep 1795415 = 2693123) B2693123
theorem B1197399 : Blo 1196415 1197399 := bstep (se 1 (by rfl) ⟨898049, by rfl⟩ : syracuseStep 1197399 = 1796099) B1796099
theorem B1197419 : Blo 1196415 1197419 := bstep (se 1 (by rfl) ⟨898064, by rfl⟩ : syracuseStep 1197419 = 1796129) B1796129
theorem B1197431 : Blo 1196415 1197431 := bstep (se 1 (by rfl) ⟨898073, by rfl⟩ : syracuseStep 1197431 = 1796147) B1796147
theorem B1197451 : Blo 1196415 1197451 := bstep (se 1 (by rfl) ⟨898088, by rfl⟩ : syracuseStep 1197451 = 1796177) B1796177
theorem B4851089 : Blo 1196415 4851089 := bstep (se 2 (by rfl) ⟨1819158, by rfl⟩ : syracuseStep 4851089 = 3638317) B3638317
theorem B1197463 : Blo 1196415 1197463 := bstep (se 1 (by rfl) ⟨898097, by rfl⟩ : syracuseStep 1197463 = 1796195) B1796195
theorem B1795481 : Blo 1196415 1795481 := bstep (se 2 (by rfl) ⟨673305, by rfl⟩ : syracuseStep 1795481 = 1346611) B1346611
theorem B1197483 : Blo 1196415 1197483 := bstep (se 1 (by rfl) ⟨898112, by rfl⟩ : syracuseStep 1197483 = 1796225) B1796225
theorem B1197495 : Blo 1196415 1197495 := bstep (se 1 (by rfl) ⟨898121, by rfl⟩ : syracuseStep 1197495 = 1796243) B1796243
theorem B1197515 : Blo 1196415 1197515 := bstep (se 1 (by rfl) ⟨898136, by rfl⟩ : syracuseStep 1197515 = 1796273) B1796273
theorem B1197527 : Blo 1196415 1197527 := bstep (se 1 (by rfl) ⟨898145, by rfl⟩ : syracuseStep 1197527 = 1796291) B1796291
theorem B1197547 : Blo 1196415 1197547 := bstep (se 1 (by rfl) ⟨898160, by rfl⟩ : syracuseStep 1197547 = 1796321) B1796321
theorem B1197559 : Blo 1196415 1197559 := bstep (se 1 (by rfl) ⟨898169, by rfl⟩ : syracuseStep 1197559 = 1796339) B1796339
theorem B2156033 : Blo 1196415 2156033 := bstep (se 2 (by rfl) ⟨808512, by rfl⟩ : syracuseStep 2156033 = 1617025) B1617025
theorem B1795595 : Blo 1196415 1795595 := bstep (se 1 (by rfl) ⟨1346696, by rfl⟩ : syracuseStep 1795595 = 2693393) B2693393
theorem B1197579 : Blo 1196415 1197579 := bstep (se 1 (by rfl) ⟨898184, by rfl⟩ : syracuseStep 1197579 = 1796369) B1796369
theorem B1795607 : Blo 1196415 1795607 := bstep (se 1 (by rfl) ⟨1346705, by rfl⟩ : syracuseStep 1795607 = 2693411) B2693411
theorem B1197591 : Blo 1196415 1197591 := bstep (se 1 (by rfl) ⟨898193, by rfl⟩ : syracuseStep 1197591 = 1796387) B1796387
theorem B3032599 : Blo 1196415 3032599 := bstep (se 1 (by rfl) ⟨2274449, by rfl⟩ : syracuseStep 3032599 = 4548899) B4548899
theorem B1197611 : Blo 1196415 1197611 := bstep (se 1 (by rfl) ⟨898208, by rfl⟩ : syracuseStep 1197611 = 1796417) B1796417
theorem B1197623 : Blo 1196415 1197623 := bstep (se 1 (by rfl) ⟨898217, by rfl⟩ : syracuseStep 1197623 = 1796435) B1796435
theorem B1197643 : Blo 1196415 1197643 := bstep (se 1 (by rfl) ⟨898232, by rfl⟩ : syracuseStep 1197643 = 1796465) B1796465
theorem B1795673 : Blo 1196415 1795673 := bstep (se 2 (by rfl) ⟨673377, by rfl⟩ : syracuseStep 1795673 = 1346755) B1346755
theorem B1197655 : Blo 1196415 1197655 := bstep (se 1 (by rfl) ⟨898241, by rfl⟩ : syracuseStep 1197655 = 1796483) B1796483
theorem B21841501 : Blo 1196415 21841501 := bstep (se 3 (by rfl) ⟨4095281, by rfl⟩ : syracuseStep 21841501 = 8190563) B8190563
theorem B1197675 : Blo 1196415 1197675 := bstep (se 1 (by rfl) ⟨898256, by rfl⟩ : syracuseStep 1197675 = 1796513) B1796513
theorem B2303603 : Blo 1196415 2303603 := bstep (se 1 (by rfl) ⟨1727702, by rfl⟩ : syracuseStep 2303603 = 3455405) B3455405
theorem B1197687 : Blo 1196415 1197687 := bstep (se 1 (by rfl) ⟨898265, by rfl⟩ : syracuseStep 1197687 = 1796531) B1796531
theorem B1197707 : Blo 1196415 1197707 := bstep (se 1 (by rfl) ⟨898280, by rfl⟩ : syracuseStep 1197707 = 1796561) B1796561
theorem B11503255 : Blo 1196415 11503255 := bstep (se 1 (by rfl) ⟨8627441, by rfl⟩ : syracuseStep 11503255 = 17254883) B17254883
theorem B7669399 : Blo 1196415 7669399 := bstep (se 1 (by rfl) ⟨5752049, by rfl⟩ : syracuseStep 7669399 = 11504099) B11504099
theorem B1197719 : Blo 1196415 1197719 := bstep (se 1 (by rfl) ⟨898289, by rfl⟩ : syracuseStep 1197719 = 1796579) B1796579
theorem B1197739 : Blo 1196415 1197739 := bstep (se 1 (by rfl) ⟨898304, by rfl⟩ : syracuseStep 1197739 = 1796609) B1796609
theorem B1197751 : Blo 1196415 1197751 := bstep (se 1 (by rfl) ⟨898313, by rfl⟩ : syracuseStep 1197751 = 1796627) B1796627
theorem B1795787 : Blo 1196415 1795787 := bstep (se 1 (by rfl) ⟨1346840, by rfl⟩ : syracuseStep 1795787 = 2693681) B2693681
theorem B1197771 : Blo 1196415 1197771 := bstep (se 1 (by rfl) ⟨898328, by rfl⟩ : syracuseStep 1197771 = 1796657) B1796657
theorem B1795799 : Blo 1196415 1795799 := bstep (se 1 (by rfl) ⟨1346849, by rfl⟩ : syracuseStep 1795799 = 2693699) B2693699
theorem B1197783 : Blo 1196415 1197783 := bstep (se 1 (by rfl) ⟨898337, by rfl⟩ : syracuseStep 1197783 = 1796675) B1796675
theorem B1197803 : Blo 1196415 1197803 := bstep (se 1 (by rfl) ⟨898352, by rfl⟩ : syracuseStep 1197803 = 1796705) B1796705
theorem B1197815 : Blo 1196415 1197815 := bstep (se 1 (by rfl) ⟨898361, by rfl⟩ : syracuseStep 1197815 = 1796723) B1796723
theorem B1197835 : Blo 1196415 1197835 := bstep (se 1 (by rfl) ⟨898376, by rfl⟩ : syracuseStep 1197835 = 1796753) B1796753
theorem B4433687 : Blo 1196415 4433687 := bstep (se 1 (by rfl) ⟨3325265, by rfl⟩ : syracuseStep 4433687 = 6650531) B6650531
theorem B2729753 : Blo 1196415 2729753 := bstep (se 2 (by rfl) ⟨1023657, by rfl⟩ : syracuseStep 2729753 = 2047315) B2047315
theorem B1795865 : Blo 1196415 1795865 := bstep (se 2 (by rfl) ⟨673449, by rfl⟩ : syracuseStep 1795865 = 1346899) B1346899
theorem B1197847 : Blo 1196415 1197847 := bstep (se 1 (by rfl) ⟨898385, by rfl⟩ : syracuseStep 1197847 = 1796771) B1796771
theorem B1197867 : Blo 1196415 1197867 := bstep (se 1 (by rfl) ⟨898400, by rfl⟩ : syracuseStep 1197867 = 1796801) B1796801
theorem B5113651 : Blo 1196415 5113651 := bstep (se 1 (by rfl) ⟨3835238, by rfl⟩ : syracuseStep 5113651 = 7670477) B7670477
theorem B3409715 : Blo 1196415 3409715 := bstep (se 1 (by rfl) ⟨2557286, by rfl⟩ : syracuseStep 3409715 = 5114573) B5114573
theorem B1197879 : Blo 1196415 1197879 := bstep (se 1 (by rfl) ⟨898409, by rfl⟩ : syracuseStep 1197879 = 1796819) B1796819
theorem B3409739 : Blo 1196415 3409739 := bstep (se 1 (by rfl) ⟨2557304, by rfl⟩ : syracuseStep 3409739 = 5114609) B5114609
theorem B1197899 : Blo 1196415 1197899 := bstep (se 1 (by rfl) ⟨898424, by rfl⟩ : syracuseStep 1197899 = 1796849) B1796849
theorem B1197911 : Blo 1196415 1197911 := bstep (se 1 (by rfl) ⟨898433, by rfl⟩ : syracuseStep 1197911 = 1796867) B1796867
theorem B1197931 : Blo 1196415 1197931 := bstep (se 1 (by rfl) ⟨898448, by rfl⟩ : syracuseStep 1197931 = 1796897) B1796897
theorem B1197943 : Blo 1196415 1197943 := bstep (se 1 (by rfl) ⟨898457, by rfl⟩ : syracuseStep 1197943 = 1796915) B1796915
theorem B1795979 : Blo 1196415 1795979 := bstep (se 1 (by rfl) ⟨1346984, by rfl⟩ : syracuseStep 1795979 = 2693969) B2693969
theorem B1197963 : Blo 1196415 1197963 := bstep (se 1 (by rfl) ⟨898472, by rfl⟩ : syracuseStep 1197963 = 1796945) B1796945
theorem B1795991 : Blo 1196415 1795991 := bstep (se 1 (by rfl) ⟨1346993, by rfl⟩ : syracuseStep 1795991 = 2693987) B2693987
theorem B1197975 : Blo 1196415 1197975 := bstep (se 1 (by rfl) ⟨898481, by rfl⟩ : syracuseStep 1197975 = 1796963) B1796963
theorem B1197995 : Blo 1196415 1197995 := bstep (se 1 (by rfl) ⟨898496, by rfl⟩ : syracuseStep 1197995 = 1796993) B1796993
theorem B1198007 : Blo 1196415 1198007 := bstep (se 1 (by rfl) ⟨898505, by rfl⟩ : syracuseStep 1198007 = 1797011) B1797011
theorem B1198027 : Blo 1196415 1198027 := bstep (se 1 (by rfl) ⟨898520, by rfl⟩ : syracuseStep 1198027 = 1797041) B1797041
theorem B3033035 : Blo 1196415 3033035 := bstep (se 1 (by rfl) ⟨2274776, by rfl⟩ : syracuseStep 3033035 = 4549553) B4549553
theorem B1198039 : Blo 1196415 1198039 := bstep (se 1 (by rfl) ⟨898529, by rfl⟩ : syracuseStep 1198039 = 1797059) B1797059
theorem B1796057 : Blo 1196415 1796057 := bstep (se 2 (by rfl) ⟨673521, by rfl⟩ : syracuseStep 1796057 = 1347043) B1347043
theorem B1198059 : Blo 1196415 1198059 := bstep (se 1 (by rfl) ⟨898544, by rfl⟩ : syracuseStep 1198059 = 1797089) B1797089
theorem B1198071 : Blo 1196415 1198071 := bstep (se 1 (by rfl) ⟨898553, by rfl⟩ : syracuseStep 1198071 = 1797107) B1797107
theorem B1198091 : Blo 1196415 1198091 := bstep (se 1 (by rfl) ⟨898568, by rfl⟩ : syracuseStep 1198091 = 1797137) B1797137
theorem B6064145 : Blo 1196415 6064145 := bstep (se 2 (by rfl) ⟨2274054, by rfl⟩ : syracuseStep 6064145 = 4548109) B4548109
theorem B1198103 : Blo 1196415 1198103 := bstep (se 1 (by rfl) ⟨898577, by rfl⟩ : syracuseStep 1198103 = 1797155) B1797155
theorem B1198123 : Blo 1196415 1198123 := bstep (se 1 (by rfl) ⟨898592, by rfl⟩ : syracuseStep 1198123 = 1797185) B1797185
theorem B1198135 : Blo 1196415 1198135 := bstep (se 1 (by rfl) ⟨898601, by rfl⟩ : syracuseStep 1198135 = 1797203) B1797203
theorem B1796171 : Blo 1196415 1796171 := bstep (se 1 (by rfl) ⟨1347128, by rfl⟩ : syracuseStep 1796171 = 2694257) B2694257
theorem B8751179 : Blo 1196415 8751179 := bstep (se 1 (by rfl) ⟨6563384, by rfl⟩ : syracuseStep 8751179 = 13126769) B13126769
theorem B1198155 : Blo 1196415 1198155 := bstep (se 1 (by rfl) ⟨898616, by rfl⟩ : syracuseStep 1198155 = 1797233) B1797233
theorem B1796183 : Blo 1196415 1796183 := bstep (se 1 (by rfl) ⟨1347137, by rfl⟩ : syracuseStep 1796183 = 2694275) B2694275
theorem B1198167 : Blo 1196415 1198167 := bstep (se 1 (by rfl) ⟨898625, by rfl⟩ : syracuseStep 1198167 = 1797251) B1797251
theorem B1198187 : Blo 1196415 1198187 := bstep (se 1 (by rfl) ⟨898640, by rfl⟩ : syracuseStep 1198187 = 1797281) B1797281
theorem B1198199 : Blo 1196415 1198199 := bstep (se 1 (by rfl) ⟨898649, by rfl⟩ : syracuseStep 1198199 = 1797299) B1797299
theorem B1296523 : Blo 1196415 1296523 := bstep (se 1 (by rfl) ⟨972392, by rfl⟩ : syracuseStep 1296523 = 1944785) B1944785
theorem B1198219 : Blo 1196415 1198219 := bstep (se 1 (by rfl) ⟨898664, by rfl⟩ : syracuseStep 1198219 = 1797329) B1797329
theorem B1198231 : Blo 1196415 1198231 := bstep (se 1 (by rfl) ⟨898673, by rfl⟩ : syracuseStep 1198231 = 1797347) B1797347
theorem B1796249 : Blo 1196415 1796249 := bstep (se 2 (by rfl) ⟨673593, by rfl⟩ : syracuseStep 1796249 = 1347187) B1347187
theorem B1403051 : Blo 1196415 1403051 := bstep (se 1 (by rfl) ⟨1052288, by rfl⟩ : syracuseStep 1403051 = 2104577) B2104577
theorem B1198251 : Blo 1196415 1198251 := bstep (se 1 (by rfl) ⟨898688, by rfl⟩ : syracuseStep 1198251 = 1797377) B1797377
theorem B6064307 : Blo 1196415 6064307 := bstep (se 1 (by rfl) ⟨4548230, by rfl⟩ : syracuseStep 6064307 = 9096461) B9096461
theorem B1198263 : Blo 1196415 1198263 := bstep (se 1 (by rfl) ⟨898697, by rfl⟩ : syracuseStep 1198263 = 1797395) B1797395
theorem B4098251 : Blo 1196415 4098251 := bstep (se 1 (by rfl) ⟨3073688, by rfl⟩ : syracuseStep 4098251 = 6147377) B6147377
theorem B1198283 : Blo 1196415 1198283 := bstep (se 1 (by rfl) ⟨898712, by rfl⟩ : syracuseStep 1198283 = 1797425) B1797425
theorem B1198295 : Blo 1196415 1198295 := bstep (se 1 (by rfl) ⟨898721, by rfl⟩ : syracuseStep 1198295 = 1797443) B1797443
theorem B1198315 : Blo 1196415 1198315 := bstep (se 1 (by rfl) ⟨898736, by rfl⟩ : syracuseStep 1198315 = 1797473) B1797473
theorem B1198327 : Blo 1196415 1198327 := bstep (se 1 (by rfl) ⟨898745, by rfl⟩ : syracuseStep 1198327 = 1797491) B1797491
theorem B1796363 : Blo 1196415 1796363 := bstep (se 1 (by rfl) ⟨1347272, by rfl⟩ : syracuseStep 1796363 = 2694545) B2694545
theorem B1198347 : Blo 1196415 1198347 := bstep (se 1 (by rfl) ⟨898760, by rfl⟩ : syracuseStep 1198347 = 1797521) B1797521
theorem B1796375 : Blo 1196415 1796375 := bstep (se 1 (by rfl) ⟨1347281, by rfl⟩ : syracuseStep 1796375 = 2694563) B2694563
theorem B1198359 : Blo 1196415 1198359 := bstep (se 1 (by rfl) ⟨898769, by rfl⟩ : syracuseStep 1198359 = 1797539) B1797539
theorem B2304281 : Blo 1196415 2304281 := bstep (se 2 (by rfl) ⟨864105, by rfl⟩ : syracuseStep 2304281 = 1728211) B1728211
theorem B1198379 : Blo 1196415 1198379 := bstep (se 1 (by rfl) ⟨898784, by rfl⟩ : syracuseStep 1198379 = 1797569) B1797569
theorem B1198391 : Blo 1196415 1198391 := bstep (se 1 (by rfl) ⟨898793, by rfl⟩ : syracuseStep 1198391 = 1797587) B1797587
theorem B9095489 : Blo 1196415 9095489 := bstep (se 2 (by rfl) ⟨3410808, by rfl⟩ : syracuseStep 9095489 = 6821617) B6821617
theorem B3033409 : Blo 1196415 3033409 := bstep (se 2 (by rfl) ⟨1137528, by rfl⟩ : syracuseStep 3033409 = 2275057) B2275057
theorem B4041035 : Blo 1196415 4041035 := bstep (se 1 (by rfl) ⟨3030776, by rfl⟩ : syracuseStep 4041035 = 6061553) B6061553
theorem B1198411 : Blo 1196415 1198411 := bstep (se 1 (by rfl) ⟨898808, by rfl⟩ : syracuseStep 1198411 = 1797617) B1797617
theorem B1796441 : Blo 1196415 1796441 := bstep (se 2 (by rfl) ⟨673665, by rfl⟩ : syracuseStep 1796441 = 1347331) B1347331
theorem B2877785 : Blo 1196415 2877785 := bstep (se 2 (by rfl) ⟨1079169, by rfl⟩ : syracuseStep 2877785 = 2158339) B2158339
theorem B5114285 : Blo 1196415 5114285 := bstep (se 3 (by rfl) ⟨958928, by rfl⟩ : syracuseStep 5114285 = 1917857) B1917857
theorem B1796555 : Blo 1196415 1796555 := bstep (se 1 (by rfl) ⟨1347416, by rfl⟩ : syracuseStep 1796555 = 2694833) B2694833
theorem B4549067 : Blo 1196415 4549067 := bstep (se 1 (by rfl) ⟨3411800, by rfl⟩ : syracuseStep 4549067 = 6823601) B6823601
theorem B1796567 : Blo 1196415 1796567 := bstep (se 1 (by rfl) ⟨1347425, by rfl⟩ : syracuseStep 1796567 = 2694851) B2694851
theorem B4549081 : Blo 1196415 4549081 := bstep (se 2 (by rfl) ⟨1705905, by rfl⟩ : syracuseStep 4549081 = 3411811) B3411811
theorem B1346071 : Blo 1196415 1346071 := bstep (se 1 (by rfl) ⟨1009553, by rfl⟩ : syracuseStep 1346071 = 2019107) B2019107
theorem B1796633 : Blo 1196415 1796633 := bstep (se 2 (by rfl) ⟨673737, by rfl⟩ : syracuseStep 1796633 = 1347475) B1347475
theorem B4041305 : Blo 1196415 4041305 := bstep (se 2 (by rfl) ⟨1515489, by rfl⟩ : syracuseStep 4041305 = 3030979) B3030979
theorem B3410525 : Blo 1196415 3410525 := bstep (se 3 (by rfl) ⟨639473, by rfl⟩ : syracuseStep 3410525 = 1278947) B1278947
theorem B2271883 : Blo 1196415 2271883 := bstep (se 1 (by rfl) ⟨1703912, by rfl⟩ : syracuseStep 2271883 = 3407825) B3407825
theorem B1796747 : Blo 1196415 1796747 := bstep (se 1 (by rfl) ⟨1347560, by rfl⟩ : syracuseStep 1796747 = 2695121) B2695121
theorem B2558603 : Blo 1196415 2558603 := bstep (se 1 (by rfl) ⟨1918952, by rfl⟩ : syracuseStep 2558603 = 3837905) B3837905
theorem B1796759 : Blo 1196415 1796759 := bstep (se 1 (by rfl) ⟨1347569, by rfl⟩ : syracuseStep 1796759 = 2695139) B2695139
theorem B1346251 : Blo 1196415 1346251 := bstep (se 1 (by rfl) ⟨1009688, by rfl⟩ : syracuseStep 1346251 = 2019377) B2019377
theorem B2271959 : Blo 1196415 2271959 := bstep (se 1 (by rfl) ⟨1703969, by rfl⟩ : syracuseStep 2271959 = 3407939) B3407939
theorem B1796825 : Blo 1196415 1796825 := bstep (se 2 (by rfl) ⟨673809, by rfl⟩ : syracuseStep 1796825 = 1347619) B1347619
theorem B1346359 : Blo 1196415 1346359 := bstep (se 1 (by rfl) ⟨1009769, by rfl⟩ : syracuseStep 1346359 = 2019539) B2019539
theorem B1796939 : Blo 1196415 1796939 := bstep (se 1 (by rfl) ⟨1347704, by rfl⟩ : syracuseStep 1796939 = 2695409) B2695409
theorem B1796951 : Blo 1196415 1796951 := bstep (se 1 (by rfl) ⟨1347713, by rfl⟩ : syracuseStep 1796951 = 2695427) B2695427
theorem B5188441 : Blo 1196415 5188441 := bstep (se 2 (by rfl) ⟨1945665, by rfl⟩ : syracuseStep 5188441 = 3891331) B3891331
theorem B7670629 : Blo 1196415 7670629 := bstep (se 4 (by rfl) ⟨719121, by rfl⟩ : syracuseStep 7670629 = 1438243) B1438243
theorem B6056855 : Blo 1196415 6056855 := bstep (se 1 (by rfl) ⟨4542641, by rfl⟩ : syracuseStep 6056855 = 9085283) B9085283
theorem B1797017 : Blo 1196415 1797017 := bstep (se 2 (by rfl) ⟨673881, by rfl⟩ : syracuseStep 1797017 = 1347763) B1347763
theorem B1346539 : Blo 1196415 1346539 := bstep (se 1 (by rfl) ⟨1009904, by rfl⟩ : syracuseStep 1346539 = 2019809) B2019809
theorem B1797131 : Blo 1196415 1797131 := bstep (se 1 (by rfl) ⟨1347848, by rfl⟩ : syracuseStep 1797131 = 2695697) B2695697
theorem B1797143 : Blo 1196415 1797143 := bstep (se 1 (by rfl) ⟨1347857, by rfl⟩ : syracuseStep 1797143 = 2695715) B2695715
theorem B6917185 : Blo 1196415 6917185 := bstep (se 2 (by rfl) ⟨2593944, by rfl⟩ : syracuseStep 6917185 = 5187889) B5187889
theorem B1346647 : Blo 1196415 1346647 := bstep (se 1 (by rfl) ⟨1009985, by rfl⟩ : syracuseStep 1346647 = 2019971) B2019971
theorem B1797209 : Blo 1196415 1797209 := bstep (se 2 (by rfl) ⟨673953, by rfl⟩ : syracuseStep 1797209 = 1347907) B1347907
theorem B4099265 : Blo 1196415 4099265 := bstep (se 2 (by rfl) ⟨1537224, by rfl⟩ : syracuseStep 4099265 = 3074449) B3074449
theorem B1797323 : Blo 1196415 1797323 := bstep (se 1 (by rfl) ⟨1347992, by rfl⟩ : syracuseStep 1797323 = 2695985) B2695985
theorem B1797335 : Blo 1196415 1797335 := bstep (se 1 (by rfl) ⟨1348001, by rfl⟩ : syracuseStep 1797335 = 2696003) B2696003
theorem B1346827 : Blo 1196415 1346827 := bstep (se 1 (by rfl) ⟨1010120, by rfl⟩ : syracuseStep 1346827 = 2020241) B2020241
theorem B4042007 : Blo 1196415 4042007 := bstep (se 1 (by rfl) ⟨3031505, by rfl⟩ : syracuseStep 4042007 = 6063011) B6063011
theorem B1797401 : Blo 1196415 1797401 := bstep (se 2 (by rfl) ⟨674025, by rfl⟩ : syracuseStep 1797401 = 1348051) B1348051
theorem B19426661 : Blo 1196415 19426661 := bstep (se 4 (by rfl) ⟨1821249, by rfl⟩ : syracuseStep 19426661 = 3642499) B3642499
theorem B2272627 : Blo 1196415 2272627 := bstep (se 1 (by rfl) ⟨1704470, by rfl⟩ : syracuseStep 2272627 = 3408941) B3408941
theorem B1346935 : Blo 1196415 1346935 := bstep (se 1 (by rfl) ⟨1010201, by rfl⟩ : syracuseStep 1346935 = 2020403) B2020403
theorem B1797515 : Blo 1196415 1797515 := bstep (se 1 (by rfl) ⟨1348136, by rfl⟩ : syracuseStep 1797515 = 2696273) B2696273
theorem B9710999 : Blo 1196415 9710999 := bstep (se 1 (by rfl) ⟨7283249, by rfl⟩ : syracuseStep 9710999 = 14566499) B14566499
theorem B1797527 : Blo 1196415 1797527 := bstep (se 1 (by rfl) ⟨1348145, by rfl⟩ : syracuseStep 1797527 = 2696291) B2696291
theorem B4550039 : Blo 1196415 4550039 := bstep (se 1 (by rfl) ⟨3412529, by rfl⟩ : syracuseStep 4550039 = 6825059) B6825059
theorem B1797593 : Blo 1196415 1797593 := bstep (se 2 (by rfl) ⟨674097, by rfl⟩ : syracuseStep 1797593 = 1348195) B1348195
theorem B1347115 : Blo 1196415 1347115 := bstep (se 1 (by rfl) ⟨1010336, by rfl⟩ : syracuseStep 1347115 = 2020673) B2020673
theorem B2428481 : Blo 1196415 2428481 := bstep (se 2 (by rfl) ⟨910680, by rfl⟩ : syracuseStep 2428481 = 1821361) B1821361
theorem B2272855 : Blo 1196415 2272855 := bstep (se 1 (by rfl) ⟨1704641, by rfl⟩ : syracuseStep 2272855 = 3409283) B3409283
theorem B1347223 : Blo 1196415 1347223 := bstep (se 1 (by rfl) ⟨1010417, by rfl⟩ : syracuseStep 1347223 = 2020835) B2020835
theorem B2272961 : Blo 1196415 2272961 := bstep (se 2 (by rfl) ⟨852360, by rfl⟩ : syracuseStep 2272961 = 1704721) B1704721
theorem B2019019 : Blo 1196415 2019019 := bstep (se 1 (by rfl) ⟨1514264, by rfl⟩ : syracuseStep 2019019 = 3028529) B3028529
theorem B4042547 : Blo 1196415 4042547 := bstep (se 1 (by rfl) ⟨3031910, by rfl⟩ : syracuseStep 4042547 = 6063821) B6063821
theorem B6819659 : Blo 1196415 6819659 := bstep (se 1 (by rfl) ⟨5114744, by rfl⟩ : syracuseStep 6819659 = 10229489) B10229489
theorem B1347403 : Blo 1196415 1347403 := bstep (se 1 (by rfl) ⟨1010552, by rfl⟩ : syracuseStep 1347403 = 2021105) B2021105
theorem B2019161 : Blo 1196415 2019161 := bstep (se 2 (by rfl) ⟨757185, by rfl⟩ : syracuseStep 2019161 = 1514371) B1514371
theorem B2273113 : Blo 1196415 2273113 := bstep (se 2 (by rfl) ⟨852417, by rfl⟩ : syracuseStep 2273113 = 1704835) B1704835
theorem B6557591 : Blo 1196415 6557591 := bstep (se 1 (by rfl) ⟨4918193, by rfl⟩ : syracuseStep 6557591 = 9836387) B9836387
theorem B1347511 : Blo 1196415 1347511 := bstep (se 1 (by rfl) ⟨1010633, by rfl⟩ : syracuseStep 1347511 = 2021267) B2021267
theorem B2019289 : Blo 1196415 2019289 := bstep (se 2 (by rfl) ⟨757233, by rfl⟩ : syracuseStep 2019289 = 1514467) B1514467
theorem B2461657 : Blo 1196415 2461657 := bstep (se 2 (by rfl) ⟨923121, by rfl⟩ : syracuseStep 2461657 = 1846243) B1846243
theorem B4042817 : Blo 1196415 4042817 := bstep (se 2 (by rfl) ⟨1516056, by rfl⟩ : syracuseStep 4042817 = 3032113) B3032113
theorem B6066251 : Blo 1196415 6066251 := bstep (se 1 (by rfl) ⟨4549688, by rfl⟩ : syracuseStep 6066251 = 9099377) B9099377
theorem B1347691 : Blo 1196415 1347691 := bstep (se 1 (by rfl) ⟨1010768, by rfl⟩ : syracuseStep 1347691 = 2021537) B2021537
theorem B2158721 : Blo 1196415 2158721 := bstep (se 2 (by rfl) ⟨809520, by rfl⟩ : syracuseStep 2158721 = 1619041) B1619041
theorem B3281075 : Blo 1196415 3281075 := bstep (se 1 (by rfl) ⟨2460806, by rfl⟩ : syracuseStep 3281075 = 4921613) B4921613
theorem B2158807 : Blo 1196415 2158807 := bstep (se 1 (by rfl) ⟨1619105, by rfl⟩ : syracuseStep 2158807 = 3238211) B3238211
theorem B1347799 : Blo 1196415 1347799 := bstep (se 1 (by rfl) ⟨1010849, by rfl⟩ : syracuseStep 1347799 = 2021699) B2021699
theorem B9097433 : Blo 1196415 9097433 := bstep (se 2 (by rfl) ⟨3411537, by rfl⟩ : syracuseStep 9097433 = 6823075) B6823075
theorem B3412313 : Blo 1196415 3412313 := bstep (se 2 (by rfl) ⟨1279617, by rfl⟩ : syracuseStep 3412313 = 2559235) B2559235
theorem B10236253 : Blo 1196415 10236253 := bstep (se 3 (by rfl) ⟨1919297, by rfl⟩ : syracuseStep 10236253 = 3838595) B3838595
theorem B1347979 : Blo 1196415 1347979 := bstep (se 1 (by rfl) ⟨1010984, by rfl⟩ : syracuseStep 1347979 = 2021969) B2021969
theorem B7287191 : Blo 1196415 7287191 := bstep (se 1 (by rfl) ⟨5465393, by rfl⟩ : syracuseStep 7287191 = 10930787) B10930787
theorem B1348087 : Blo 1196415 1348087 := bstep (se 1 (by rfl) ⟨1011065, by rfl⟩ : syracuseStep 1348087 = 2022131) B2022131
theorem B2019863 : Blo 1196415 2019863 := bstep (se 1 (by rfl) ⟨1514897, by rfl⟩ : syracuseStep 2019863 = 3029795) B3029795
theorem B4043357 : Blo 1196415 4043357 := bstep (se 3 (by rfl) ⟨758129, by rfl⟩ : syracuseStep 4043357 = 1516259) B1516259
theorem B2019991 : Blo 1196415 2019991 := bstep (se 1 (by rfl) ⟨1514993, by rfl⟩ : syracuseStep 2019991 = 3029987) B3029987
theorem B3412631 : Blo 1196415 3412631 := bstep (se 1 (by rfl) ⟨2559473, by rfl⟩ : syracuseStep 3412631 = 5118947) B5118947
theorem B98587363 : Blo 1196415 98587363 := bstep (se 1 (by rfl) ⟨73940522, by rfl⟩ : syracuseStep 98587363 = 147881045) B147881045
theorem B4543235 : Blo 1196415 4543235 := bstep (se 1 (by rfl) ⟨3407426, by rfl⟩ : syracuseStep 4543235 = 6814853) B6814853
theorem B4543249 : Blo 1196415 4543249 := bstep (se 2 (by rfl) ⟨1703718, by rfl⟩ : syracuseStep 4543249 = 3407437) B3407437
theorem B16380737 : Blo 1196415 16380737 := bstep (se 2 (by rfl) ⟨6142776, by rfl⟩ : syracuseStep 16380737 = 12285553) B12285553
theorem B2159435 : Blo 1196415 2159435 := bstep (se 1 (by rfl) ⟨1619576, by rfl⟩ : syracuseStep 2159435 = 3239153) B3239153
theorem B2692043 : Blo 1196415 2692043 := bstep (se 1 (by rfl) ⟨2019032, by rfl⟩ : syracuseStep 2692043 = 4038065) B4038065
theorem B2692097 : Blo 1196415 2692097 := bstep (se 2 (by rfl) ⟨1009536, by rfl⟩ : syracuseStep 2692097 = 2019073) B2019073
theorem B2626561 : Blo 1196415 2626561 := bstep (se 2 (by rfl) ⟨984960, by rfl⟩ : syracuseStep 2626561 = 1969921) B1969921
theorem B4543553 : Blo 1196415 4543553 := bstep (se 2 (by rfl) ⟨1703832, by rfl⟩ : syracuseStep 4543553 = 3407665) B3407665
theorem B2274419 : Blo 1196415 2274419 := bstep (se 1 (by rfl) ⟨1705814, by rfl⟩ : syracuseStep 2274419 = 3411629) B3411629
theorem B2733209 : Blo 1196415 2733209 := bstep (se 2 (by rfl) ⟨1024953, by rfl⟩ : syracuseStep 2733209 = 2049907) B2049907
theorem B2692313 : Blo 1196415 2692313 := bstep (se 2 (by rfl) ⟨1009617, by rfl⟩ : syracuseStep 2692313 = 2019235) B2019235
theorem B2020619 : Blo 1196415 2020619 := bstep (se 1 (by rfl) ⟨1515464, by rfl⟩ : syracuseStep 2020619 = 3030929) B3030929
theorem B2274571 : Blo 1196415 2274571 := bstep (se 1 (by rfl) ⟨1705928, by rfl⟩ : syracuseStep 2274571 = 3411857) B3411857
theorem B2692403 : Blo 1196415 2692403 := bstep (se 1 (by rfl) ⟨2019302, by rfl⟩ : syracuseStep 2692403 = 4038605) B4038605
theorem B2692439 : Blo 1196415 2692439 := bstep (se 1 (by rfl) ⟨2019329, by rfl⟩ : syracuseStep 2692439 = 4038659) B4038659
theorem B2020747 : Blo 1196415 2020747 := bstep (se 1 (by rfl) ⟨1515560, by rfl⟩ : syracuseStep 2020747 = 3031121) B3031121
theorem B2692619 : Blo 1196415 2692619 := bstep (se 1 (by rfl) ⟨2019464, by rfl⟩ : syracuseStep 2692619 = 4038929) B4038929
theorem B2020889 : Blo 1196415 2020889 := bstep (se 2 (by rfl) ⟨757833, by rfl⟩ : syracuseStep 2020889 = 1515667) B1515667
theorem B2692673 : Blo 1196415 2692673 := bstep (se 2 (by rfl) ⟨1009752, by rfl⟩ : syracuseStep 2692673 = 2019505) B2019505
theorem B2274905 : Blo 1196415 2274905 := bstep (se 2 (by rfl) ⟨853089, by rfl⟩ : syracuseStep 2274905 = 1706179) B1706179
theorem B2021017 : Blo 1196415 2021017 := bstep (se 2 (by rfl) ⟨757881, by rfl⟩ : syracuseStep 2021017 = 1515763) B1515763
theorem B4044491 : Blo 1196415 4044491 := bstep (se 1 (by rfl) ⟨3033368, by rfl⟩ : syracuseStep 4044491 = 6066737) B6066737
theorem B4544221 : Blo 1196415 4544221 := bstep (se 3 (by rfl) ⟨852041, by rfl⟩ : syracuseStep 4544221 = 1704083) B1704083
theorem B4314845 : Blo 1196415 4314845 := bstep (se 3 (by rfl) ⟨809033, by rfl⟩ : syracuseStep 4314845 = 1618067) B1618067
theorem B3282653 : Blo 1196415 3282653 := bstep (se 3 (by rfl) ⟨615497, by rfl⟩ : syracuseStep 3282653 = 1230995) B1230995
theorem B2692889 : Blo 1196415 2692889 := bstep (se 2 (by rfl) ⟨1009833, by rfl⟩ : syracuseStep 2692889 = 2019667) B2019667
theorem B2692979 : Blo 1196415 2692979 := bstep (se 1 (by rfl) ⟨2019734, by rfl⟩ : syracuseStep 2692979 = 4039469) B4039469
theorem B1439627 : Blo 1196415 1439627 := bstep (se 1 (by rfl) ⟨1079720, by rfl⟩ : syracuseStep 1439627 = 2159441) B2159441
theorem B2693015 : Blo 1196415 2693015 := bstep (se 1 (by rfl) ⟨2019761, by rfl⟩ : syracuseStep 2693015 = 4039523) B4039523
theorem B10221491 : Blo 1196415 10221491 := bstep (se 1 (by rfl) ⟨7666118, by rfl⟩ : syracuseStep 10221491 = 15332237) B15332237
theorem B3029015 : Blo 1196415 3029015 := bstep (se 1 (by rfl) ⟨2271761, by rfl⟩ : syracuseStep 3029015 = 4543523) B4543523
theorem B5117975 : Blo 1196415 5117975 := bstep (se 1 (by rfl) ⟨3838481, by rfl⟩ : syracuseStep 5117975 = 7676963) B7676963
theorem B2693195 : Blo 1196415 2693195 := bstep (se 1 (by rfl) ⟨2019896, by rfl⟩ : syracuseStep 2693195 = 4039793) B4039793
theorem B11671627 : Blo 1196415 11671627 := bstep (se 1 (by rfl) ⟨8753720, by rfl⟩ : syracuseStep 11671627 = 17507441) B17507441
theorem B2693249 : Blo 1196415 2693249 := bstep (se 2 (by rfl) ⟨1009968, by rfl⟩ : syracuseStep 2693249 = 2019937) B2019937
theorem B2021591 : Blo 1196415 2021591 := bstep (se 1 (by rfl) ⟨1516193, by rfl⟩ : syracuseStep 2021591 = 3032387) B3032387
theorem B2021719 : Blo 1196415 2021719 := bstep (se 1 (by rfl) ⟨1516289, by rfl⟩ : syracuseStep 2021719 = 3032579) B3032579
theorem B2693465 : Blo 1196415 2693465 := bstep (se 2 (by rfl) ⟨1010049, by rfl⟩ : syracuseStep 2693465 = 2020099) B2020099
theorem B49174901 : Blo 1196415 49174901 := bstep (se 5 (by rfl) ⟨2305073, by rfl⟩ : syracuseStep 49174901 = 4610147) B4610147
theorem B2185601 : Blo 1196415 2185601 := bstep (se 2 (by rfl) ⟨819600, by rfl⟩ : syracuseStep 2185601 = 1639201) B1639201
theorem B6060419 : Blo 1196415 6060419 := bstep (se 1 (by rfl) ⟨4545314, by rfl⟩ : syracuseStep 6060419 = 9090629) B9090629
theorem B2693555 : Blo 1196415 2693555 := bstep (se 1 (by rfl) ⟨2020166, by rfl⟩ : syracuseStep 2693555 = 4040333) B4040333
theorem B2693591 : Blo 1196415 2693591 := bstep (se 1 (by rfl) ⟨2020193, by rfl⟩ : syracuseStep 2693591 = 4040387) B4040387
theorem B9091601 : Blo 1196415 9091601 := bstep (se 2 (by rfl) ⟨3409350, by rfl⟩ : syracuseStep 9091601 = 6818701) B6818701
theorem B23026193 : Blo 1196415 23026193 := bstep (se 2 (by rfl) ⟨8634822, by rfl⟩ : syracuseStep 23026193 = 17269645) B17269645
theorem B2693771 : Blo 1196415 2693771 := bstep (se 1 (by rfl) ⟨2020328, by rfl⟩ : syracuseStep 2693771 = 4040657) B4040657
theorem B3029683 : Blo 1196415 3029683 := bstep (se 1 (by rfl) ⟨2272262, by rfl⟩ : syracuseStep 3029683 = 4544525) B4544525
theorem B2693825 : Blo 1196415 2693825 := bstep (se 2 (by rfl) ⟨1010184, by rfl⟩ : syracuseStep 2693825 = 2020369) B2020369
theorem B3029825 : Blo 1196415 3029825 := bstep (se 2 (by rfl) ⟨1136184, by rfl⟩ : syracuseStep 3029825 = 2272369) B2272369
theorem B1514315 : Blo 1196415 1514315 := bstep (se 1 (by rfl) ⟨1135736, by rfl⟩ : syracuseStep 1514315 = 2271473) B2271473
theorem B2694041 : Blo 1196415 2694041 := bstep (se 2 (by rfl) ⟨1010265, by rfl⟩ : syracuseStep 2694041 = 2020531) B2020531
theorem B4545497 : Blo 1196415 4545497 := bstep (se 2 (by rfl) ⟨1704561, by rfl⟩ : syracuseStep 4545497 = 3409123) B3409123
theorem B2694131 : Blo 1196415 2694131 := bstep (se 1 (by rfl) ⟨2020598, by rfl⟩ : syracuseStep 2694131 = 4041197) B4041197
theorem B2694167 : Blo 1196415 2694167 := bstep (se 1 (by rfl) ⟨2020625, by rfl⟩ : syracuseStep 2694167 = 4041251) B4041251
theorem B3235009 : Blo 1196415 3235009 := bstep (se 2 (by rfl) ⟨1213128, by rfl⟩ : syracuseStep 3235009 = 2426257) B2426257
theorem B2694347 : Blo 1196415 2694347 := bstep (se 1 (by rfl) ⟨2020760, by rfl⟩ : syracuseStep 2694347 = 4041521) B4041521
theorem B4611275 : Blo 1196415 4611275 := bstep (se 1 (by rfl) ⟨3458456, by rfl⟩ : syracuseStep 4611275 = 6916913) B6916913
theorem B2694401 : Blo 1196415 2694401 := bstep (se 2 (by rfl) ⟨1010400, by rfl⟩ : syracuseStep 2694401 = 2020801) B2020801
theorem B3407255 : Blo 1196415 3407255 := bstep (se 1 (by rfl) ⟨2555441, by rfl⟩ : syracuseStep 3407255 = 5110883) B5110883
theorem B4152755 : Blo 1196415 4152755 := bstep (se 1 (by rfl) ⟨3114566, by rfl⟩ : syracuseStep 4152755 = 6229133) B6229133
theorem B2694617 : Blo 1196415 2694617 := bstep (se 2 (by rfl) ⟨1010481, by rfl⟩ : syracuseStep 2694617 = 2020963) B2020963
theorem B1515019 : Blo 1196415 1515019 := bstep (se 1 (by rfl) ⟨1136264, by rfl⟩ : syracuseStep 1515019 = 2272529) B2272529
theorem B4374067 : Blo 1196415 4374067 := bstep (se 1 (by rfl) ⟨3280550, by rfl⟩ : syracuseStep 4374067 = 6561101) B6561101
theorem B2694707 : Blo 1196415 2694707 := bstep (se 1 (by rfl) ⟨2021030, by rfl⟩ : syracuseStep 2694707 = 4042061) B4042061
theorem B3833419 : Blo 1196415 3833419 := bstep (se 1 (by rfl) ⟨2875064, by rfl⟩ : syracuseStep 3833419 = 5750129) B5750129
theorem B2694743 : Blo 1196415 2694743 := bstep (se 1 (by rfl) ⟨2021057, by rfl⟩ : syracuseStep 2694743 = 4042115) B4042115
theorem B2334347 : Blo 1196415 2334347 := bstep (se 1 (by rfl) ⟨1750760, by rfl⟩ : syracuseStep 2334347 = 3501521) B3501521
theorem B1703639 : Blo 1196415 1703639 := bstep (se 1 (by rfl) ⟨1277729, by rfl⟩ : syracuseStep 1703639 = 2555459) B2555459
theorem B3833561 : Blo 1196415 3833561 := bstep (se 2 (by rfl) ⟨1437585, by rfl⟩ : syracuseStep 3833561 = 2875171) B2875171
theorem B2694923 : Blo 1196415 2694923 := bstep (se 1 (by rfl) ⟨2021192, by rfl⟩ : syracuseStep 2694923 = 4042385) B4042385
theorem B1515287 : Blo 1196415 1515287 := bstep (se 1 (by rfl) ⟨1136465, by rfl⟩ : syracuseStep 1515287 = 2272931) B2272931
theorem B4316951 : Blo 1196415 4316951 := bstep (se 1 (by rfl) ⟨3237713, by rfl⟩ : syracuseStep 4316951 = 6475427) B6475427
theorem B10223405 : Blo 1196415 10223405 := bstep (se 3 (by rfl) ⟨1916888, by rfl⟩ : syracuseStep 10223405 = 3833777) B3833777
theorem B2694977 : Blo 1196415 2694977 := bstep (se 2 (by rfl) ⟨1010616, by rfl⟩ : syracuseStep 2694977 = 2021233) B2021233
theorem B7667531 : Blo 1196415 7667531 := bstep (se 1 (by rfl) ⟨5750648, by rfl⟩ : syracuseStep 7667531 = 11501297) B11501297
theorem B4038551 : Blo 1196415 4038551 := bstep (se 1 (by rfl) ⟨3028913, by rfl⟩ : syracuseStep 4038551 = 6057827) B6057827
theorem B2695211 : Blo 1196415 2695211 := bstep (se 1 (by rfl) ⟨2021408, by rfl⟩ : syracuseStep 2695211 = 4042817) B4042817
theorem B2187383 : Blo 1196415 2187383 := bstep (se 1 (by rfl) ⟨1640537, by rfl⟩ : syracuseStep 2187383 = 3281075) B3281075
theorem B3408007 : Blo 1196415 3408007 := bstep (se 1 (by rfl) ⟨2556005, by rfl⟩ : syracuseStep 3408007 = 5112011) B5112011
theorem B1728697 : Blo 1196415 1728697 := bstep (se 2 (by rfl) ⟨648261, by rfl⟩ : syracuseStep 1728697 = 1296523) B1296523
theorem B2916553 : Blo 1196415 2916553 := bstep (se 2 (by rfl) ⟨1093707, by rfl⟩ : syracuseStep 2916553 = 2187415) B2187415
theorem B4858127 : Blo 1196415 4858127 := bstep (se 1 (by rfl) ⟨3643595, by rfl⟩ : syracuseStep 4858127 = 7287191) B7287191
theorem B3236125 : Blo 1196415 3236125 := bstep (se 3 (by rfl) ⟨606773, by rfl⟩ : syracuseStep 3236125 = 1213547) B1213547
theorem B2556193 : Blo 1196415 2556193 := bstep (se 2 (by rfl) ⟨958572, by rfl⟩ : syracuseStep 2556193 = 1917145) B1917145
theorem B6816059 : Blo 1196415 6816059 := bstep (se 1 (by rfl) ⟨5112044, by rfl⟩ : syracuseStep 6816059 = 10224089) B10224089
theorem B8192315 : Blo 1196415 8192315 := bstep (se 1 (by rfl) ⟨6144236, by rfl⟩ : syracuseStep 8192315 = 12288473) B12288473
theorem B3031415 : Blo 1196415 3031415 := bstep (se 1 (by rfl) ⟨2273561, by rfl⟩ : syracuseStep 3031415 = 4547123) B4547123
theorem B1196423 : Blo 1196415 1196423 := bstep (se 1 (by rfl) ⟨897317, by rfl⟩ : syracuseStep 1196423 = 1794635) B1794635
theorem B2998663 : Blo 1196415 2998663 := bstep (se 1 (by rfl) ⟨2248997, by rfl⟩ : syracuseStep 2998663 = 4497995) B4497995
theorem B1196431 : Blo 1196415 1196431 := bstep (se 1 (by rfl) ⟨897323, by rfl⟩ : syracuseStep 1196431 = 1794647) B1794647
theorem B2695571 : Blo 1196415 2695571 := bstep (se 1 (by rfl) ⟨2021678, by rfl⟩ : syracuseStep 2695571 = 4043357) B4043357
theorem B3408281 : Blo 1196415 3408281 := bstep (se 2 (by rfl) ⟨1278105, by rfl⟩ : syracuseStep 3408281 = 2556211) B2556211
theorem B1196475 : Blo 1196415 1196475 := bstep (se 1 (by rfl) ⟨897356, by rfl⟩ : syracuseStep 1196475 = 1794713) B1794713
theorem B2695625 : Blo 1196415 2695625 := bstep (se 2 (by rfl) ⟨1010859, by rfl⟩ : syracuseStep 2695625 = 2021719) B2021719
theorem B13648337 : Blo 1196415 13648337 := bstep (se 2 (by rfl) ⟨5118126, by rfl⟩ : syracuseStep 13648337 = 10236253) B10236253
theorem B1196551 : Blo 1196415 1196551 := bstep (se 1 (by rfl) ⟨897413, by rfl⟩ : syracuseStep 1196551 = 1794827) B1794827
theorem B1196559 : Blo 1196415 1196559 := bstep (se 1 (by rfl) ⟨897419, by rfl⟩ : syracuseStep 1196559 = 1794839) B1794839
theorem B13828637 : Blo 1196415 13828637 := bstep (se 3 (by rfl) ⟨2592869, by rfl⟩ : syracuseStep 13828637 = 5185739) B5185739
theorem B10920491 : Blo 1196415 10920491 := bstep (se 1 (by rfl) ⟨8190368, by rfl⟩ : syracuseStep 10920491 = 16380737) B16380737
theorem B1704505 : Blo 1196415 1704505 := bstep (se 2 (by rfl) ⟨639189, by rfl⟩ : syracuseStep 1704505 = 1278379) B1278379
theorem B1196603 : Blo 1196415 1196603 := bstep (se 1 (by rfl) ⟨897452, by rfl⟩ : syracuseStep 1196603 = 1794905) B1794905
theorem B2556535 : Blo 1196415 2556535 := bstep (se 1 (by rfl) ⟨1917401, by rfl⟩ : syracuseStep 2556535 = 3834803) B3834803
theorem B1794695 : Blo 1196415 1794695 := bstep (se 1 (by rfl) ⟨1346021, by rfl⟩ : syracuseStep 1794695 = 2692043) B2692043
theorem B1196679 : Blo 1196415 1196679 := bstep (se 1 (by rfl) ⟨897509, by rfl⟩ : syracuseStep 1196679 = 1795019) B1795019
theorem B2048647 : Blo 1196415 2048647 := bstep (se 1 (by rfl) ⟨1536485, by rfl⟩ : syracuseStep 2048647 = 3072971) B3072971
theorem B1196687 : Blo 1196415 1196687 := bstep (se 1 (by rfl) ⟨897515, by rfl⟩ : syracuseStep 1196687 = 1795031) B1795031
theorem B1794731 : Blo 1196415 1794731 := bstep (se 1 (by rfl) ⟨1346048, by rfl⟩ : syracuseStep 1794731 = 2692097) B2692097
theorem B1196731 : Blo 1196415 1196731 := bstep (se 1 (by rfl) ⟨897548, by rfl⟩ : syracuseStep 1196731 = 1795097) B1795097
theorem B1794761 : Blo 1196415 1794761 := bstep (se 2 (by rfl) ⟨673035, by rfl⟩ : syracuseStep 1794761 = 1346071) B1346071
theorem B6144749 : Blo 1196415 6144749 := bstep (se 3 (by rfl) ⟨1152140, by rfl⟩ : syracuseStep 6144749 = 2304281) B2304281
theorem B6062849 : Blo 1196415 6062849 := bstep (se 2 (by rfl) ⟨2273568, by rfl⟩ : syracuseStep 6062849 = 4547137) B4547137
theorem B1196807 : Blo 1196415 1196807 := bstep (se 1 (by rfl) ⟨897605, by rfl⟩ : syracuseStep 1196807 = 1795211) B1795211
theorem B1196815 : Blo 1196415 1196815 := bstep (se 1 (by rfl) ⟨897611, by rfl⟩ : syracuseStep 1196815 = 1795223) B1795223
theorem B1794875 : Blo 1196415 1794875 := bstep (se 1 (by rfl) ⟨1346156, by rfl⟩ : syracuseStep 1794875 = 2692313) B2692313
theorem B1196859 : Blo 1196415 1196859 := bstep (se 1 (by rfl) ⟨897644, by rfl⟩ : syracuseStep 1196859 = 1795289) B1795289
theorem B1794935 : Blo 1196415 1794935 := bstep (se 1 (by rfl) ⟨1346201, by rfl⟩ : syracuseStep 1794935 = 2692403) B2692403
theorem B1196935 : Blo 1196415 1196935 := bstep (se 1 (by rfl) ⟨897701, by rfl⟩ : syracuseStep 1196935 = 1795403) B1795403
theorem B1794959 : Blo 1196415 1794959 := bstep (se 1 (by rfl) ⟨1346219, by rfl⟩ : syracuseStep 1794959 = 2692439) B2692439
theorem B1196943 : Blo 1196415 1196943 := bstep (se 1 (by rfl) ⟨897707, by rfl⟩ : syracuseStep 1196943 = 1795415) B1795415
theorem B4039577 : Blo 1196415 4039577 := bstep (se 2 (by rfl) ⟨1514841, by rfl⟩ : syracuseStep 4039577 = 3029683) B3029683
theorem B1795001 : Blo 1196415 1795001 := bstep (se 2 (by rfl) ⟨673125, by rfl⟩ : syracuseStep 1795001 = 1346251) B1346251
theorem B1196987 : Blo 1196415 1196987 := bstep (se 1 (by rfl) ⟨897740, by rfl⟩ : syracuseStep 1196987 = 1795481) B1795481
theorem B131449817 : Blo 1196415 131449817 := bstep (se 2 (by rfl) ⟨49293681, by rfl⟩ : syracuseStep 131449817 = 98587363) B98587363
theorem B1795079 : Blo 1196415 1795079 := bstep (se 1 (by rfl) ⟨1346309, by rfl⟩ : syracuseStep 1795079 = 2692619) B2692619
theorem B1197063 : Blo 1196415 1197063 := bstep (se 1 (by rfl) ⟨897797, by rfl⟩ : syracuseStep 1197063 = 1795595) B1795595
theorem B1197071 : Blo 1196415 1197071 := bstep (se 1 (by rfl) ⟨897803, by rfl⟩ : syracuseStep 1197071 = 1795607) B1795607
theorem B1795115 : Blo 1196415 1795115 := bstep (se 1 (by rfl) ⟨1346336, by rfl⟩ : syracuseStep 1795115 = 2692673) B2692673
theorem B1197115 : Blo 1196415 1197115 := bstep (se 1 (by rfl) ⟨897836, by rfl⟩ : syracuseStep 1197115 = 1795673) B1795673
theorem B1795145 : Blo 1196415 1795145 := bstep (se 2 (by rfl) ⟨673179, by rfl⟩ : syracuseStep 1795145 = 1346359) B1346359
theorem B1197191 : Blo 1196415 1197191 := bstep (se 1 (by rfl) ⟨897893, by rfl⟩ : syracuseStep 1197191 = 1795787) B1795787
theorem B2696327 : Blo 1196415 2696327 := bstep (se 1 (by rfl) ⟨2022245, by rfl⟩ : syracuseStep 2696327 = 4044491) B4044491
theorem B1197199 : Blo 1196415 1197199 := bstep (se 1 (by rfl) ⟨897899, by rfl⟩ : syracuseStep 1197199 = 1795799) B1795799
theorem B2876563 : Blo 1196415 2876563 := bstep (se 1 (by rfl) ⟨2157422, by rfl⟩ : syracuseStep 2876563 = 4314845) B4314845
theorem B2188435 : Blo 1196415 2188435 := bstep (se 1 (by rfl) ⟨1641326, by rfl⟩ : syracuseStep 2188435 = 3282653) B3282653
theorem B1795259 : Blo 1196415 1795259 := bstep (se 1 (by rfl) ⟨1346444, by rfl⟩ : syracuseStep 1795259 = 2692889) B2692889
theorem B1819835 : Blo 1196415 1819835 := bstep (se 1 (by rfl) ⟨1364876, by rfl⟩ : syracuseStep 1819835 = 2729753) B2729753
theorem B1197243 : Blo 1196415 1197243 := bstep (se 1 (by rfl) ⟨897932, by rfl⟩ : syracuseStep 1197243 = 1795865) B1795865
theorem B1795319 : Blo 1196415 1795319 := bstep (se 1 (by rfl) ⟨1346489, by rfl⟩ : syracuseStep 1795319 = 2692979) B2692979
theorem B1197319 : Blo 1196415 1197319 := bstep (se 1 (by rfl) ⟨897989, by rfl⟩ : syracuseStep 1197319 = 1795979) B1795979
theorem B1795343 : Blo 1196415 1795343 := bstep (se 1 (by rfl) ⟨1346507, by rfl⟩ : syracuseStep 1795343 = 2693015) B2693015
theorem B1197327 : Blo 1196415 1197327 := bstep (se 1 (by rfl) ⟨897995, by rfl⟩ : syracuseStep 1197327 = 1795991) B1795991
theorem B6817061 : Blo 1196415 6817061 := bstep (se 4 (by rfl) ⟨639099, by rfl⟩ : syracuseStep 6817061 = 1278199) B1278199
theorem B1795385 : Blo 1196415 1795385 := bstep (se 2 (by rfl) ⟨673269, by rfl⟩ : syracuseStep 1795385 = 1346539) B1346539
theorem B1197371 : Blo 1196415 1197371 := bstep (se 1 (by rfl) ⟨898028, by rfl⟩ : syracuseStep 1197371 = 1796057) B1796057
theorem B1795463 : Blo 1196415 1795463 := bstep (se 1 (by rfl) ⟨1346597, by rfl⟩ : syracuseStep 1795463 = 2693195) B2693195
theorem B1197447 : Blo 1196415 1197447 := bstep (se 1 (by rfl) ⟨898085, by rfl⟩ : syracuseStep 1197447 = 1796171) B1796171
theorem B5834119 : Blo 1196415 5834119 := bstep (se 1 (by rfl) ⟨4375589, by rfl⟩ : syracuseStep 5834119 = 8751179) B8751179
theorem B1197455 : Blo 1196415 1197455 := bstep (se 1 (by rfl) ⟨898091, by rfl⟩ : syracuseStep 1197455 = 1796183) B1796183
theorem B1795499 : Blo 1196415 1795499 := bstep (se 1 (by rfl) ⟨1346624, by rfl⟩ : syracuseStep 1795499 = 2693249) B2693249
theorem B1197499 : Blo 1196415 1197499 := bstep (se 1 (by rfl) ⟨898124, by rfl⟩ : syracuseStep 1197499 = 1796249) B1796249
theorem B1795529 : Blo 1196415 1795529 := bstep (se 2 (by rfl) ⟨673323, by rfl⟩ : syracuseStep 1795529 = 1346647) B1346647
theorem B1197575 : Blo 1196415 1197575 := bstep (se 1 (by rfl) ⟨898181, by rfl⟩ : syracuseStep 1197575 = 1796363) B1796363
theorem B1197583 : Blo 1196415 1197583 := bstep (se 1 (by rfl) ⟨898187, by rfl⟩ : syracuseStep 1197583 = 1796375) B1796375
theorem B6063659 : Blo 1196415 6063659 := bstep (se 1 (by rfl) ⟨4547744, by rfl⟩ : syracuseStep 6063659 = 9095489) B9095489
theorem B1795643 : Blo 1196415 1795643 := bstep (se 1 (by rfl) ⟨1346732, by rfl⟩ : syracuseStep 1795643 = 2693465) B2693465
theorem B1197627 : Blo 1196415 1197627 := bstep (se 1 (by rfl) ⟨898220, by rfl⟩ : syracuseStep 1197627 = 1796441) B1796441
theorem B1918523 : Blo 1196415 1918523 := bstep (se 1 (by rfl) ⟨1438892, by rfl⟩ : syracuseStep 1918523 = 2877785) B2877785
theorem B4040279 : Blo 1196415 4040279 := bstep (se 1 (by rfl) ⟨3030209, by rfl⟩ : syracuseStep 4040279 = 6060419) B6060419
theorem B3409523 : Blo 1196415 3409523 := bstep (se 1 (by rfl) ⟨2557142, by rfl⟩ : syracuseStep 3409523 = 5114285) B5114285
theorem B1795703 : Blo 1196415 1795703 := bstep (se 1 (by rfl) ⟨1346777, by rfl⟩ : syracuseStep 1795703 = 2693555) B2693555
theorem B1197703 : Blo 1196415 1197703 := bstep (se 1 (by rfl) ⟨898277, by rfl⟩ : syracuseStep 1197703 = 1796555) B1796555
theorem B3032711 : Blo 1196415 3032711 := bstep (se 1 (by rfl) ⟨2274533, by rfl⟩ : syracuseStep 3032711 = 4549067) B4549067
theorem B1795727 : Blo 1196415 1795727 := bstep (se 1 (by rfl) ⟨1346795, by rfl⟩ : syracuseStep 1795727 = 2693591) B2693591
theorem B1197711 : Blo 1196415 1197711 := bstep (se 1 (by rfl) ⟨898283, by rfl⟩ : syracuseStep 1197711 = 1796567) B1796567
theorem B1795769 : Blo 1196415 1795769 := bstep (se 2 (by rfl) ⟨673413, by rfl⟩ : syracuseStep 1795769 = 1346827) B1346827
theorem B1197755 : Blo 1196415 1197755 := bstep (se 1 (by rfl) ⟨898316, by rfl⟩ : syracuseStep 1197755 = 1796633) B1796633
theorem B3032761 : Blo 1196415 3032761 := bstep (se 2 (by rfl) ⟨1137285, by rfl⟩ : syracuseStep 3032761 = 2274571) B2274571
theorem B11667137 : Blo 1196415 11667137 := bstep (se 2 (by rfl) ⟨4375176, by rfl⟩ : syracuseStep 11667137 = 8750353) B8750353
theorem B6817517 : Blo 1196415 6817517 := bstep (se 3 (by rfl) ⟨1278284, by rfl⟩ : syracuseStep 6817517 = 2556569) B2556569
theorem B5113601 : Blo 1196415 5113601 := bstep (se 2 (by rfl) ⟨1917600, by rfl⟩ : syracuseStep 5113601 = 3835201) B3835201
theorem B3835649 : Blo 1196415 3835649 := bstep (se 2 (by rfl) ⟨1438368, by rfl⟩ : syracuseStep 3835649 = 2876737) B2876737
theorem B1795847 : Blo 1196415 1795847 := bstep (se 1 (by rfl) ⟨1346885, by rfl⟩ : syracuseStep 1795847 = 2693771) B2693771
theorem B1197831 : Blo 1196415 1197831 := bstep (se 1 (by rfl) ⟨898373, by rfl⟩ : syracuseStep 1197831 = 1796747) B1796747
theorem B1705735 : Blo 1196415 1705735 := bstep (se 1 (by rfl) ⟨1279301, by rfl⟩ : syracuseStep 1705735 = 2558603) B2558603
theorem B1197839 : Blo 1196415 1197839 := bstep (se 1 (by rfl) ⟨898379, by rfl⟩ : syracuseStep 1197839 = 1796759) B1796759
theorem B1795883 : Blo 1196415 1795883 := bstep (se 1 (by rfl) ⟨1346912, by rfl⟩ : syracuseStep 1795883 = 2693825) B2693825
theorem B1197883 : Blo 1196415 1197883 := bstep (se 1 (by rfl) ⟨898412, by rfl⟩ : syracuseStep 1197883 = 1796825) B1796825
theorem B1795913 : Blo 1196415 1795913 := bstep (se 2 (by rfl) ⟨673467, by rfl⟩ : syracuseStep 1795913 = 1346935) B1346935
theorem B1197959 : Blo 1196415 1197959 := bstep (se 1 (by rfl) ⟨898469, by rfl⟩ : syracuseStep 1197959 = 1796939) B1796939
theorem B1197967 : Blo 1196415 1197967 := bstep (se 1 (by rfl) ⟨898475, by rfl⟩ : syracuseStep 1197967 = 1796951) B1796951
theorem B1796027 : Blo 1196415 1796027 := bstep (se 1 (by rfl) ⟨1347020, by rfl⟩ : syracuseStep 1796027 = 2694041) B2694041
theorem B1198011 : Blo 1196415 1198011 := bstep (se 1 (by rfl) ⟨898508, by rfl⟩ : syracuseStep 1198011 = 1797017) B1797017
theorem B1796087 : Blo 1196415 1796087 := bstep (se 1 (by rfl) ⟨1347065, by rfl⟩ : syracuseStep 1796087 = 2694131) B2694131
theorem B1198087 : Blo 1196415 1198087 := bstep (se 1 (by rfl) ⟨898565, by rfl⟩ : syracuseStep 1198087 = 1797131) B1797131
theorem B1796111 : Blo 1196415 1796111 := bstep (se 1 (by rfl) ⟨1347083, by rfl⟩ : syracuseStep 1796111 = 2694167) B2694167
theorem B1198095 : Blo 1196415 1198095 := bstep (se 1 (by rfl) ⟨898571, by rfl⟩ : syracuseStep 1198095 = 1797143) B1797143
theorem B1796153 : Blo 1196415 1796153 := bstep (se 2 (by rfl) ⟨673557, by rfl⟩ : syracuseStep 1796153 = 1347115) B1347115
theorem B1198139 : Blo 1196415 1198139 := bstep (se 1 (by rfl) ⟨898604, by rfl⟩ : syracuseStep 1198139 = 1797209) B1797209
theorem B4040765 : Blo 1196415 4040765 := bstep (se 3 (by rfl) ⟨757643, by rfl⟩ : syracuseStep 4040765 = 1515287) B1515287
theorem B1796231 : Blo 1196415 1796231 := bstep (se 1 (by rfl) ⟨1347173, by rfl⟩ : syracuseStep 1796231 = 2694347) B2694347
theorem B3074183 : Blo 1196415 3074183 := bstep (se 1 (by rfl) ⟨2305637, by rfl⟩ : syracuseStep 3074183 = 4611275) B4611275
theorem B1198215 : Blo 1196415 1198215 := bstep (se 1 (by rfl) ⟨898661, by rfl⟩ : syracuseStep 1198215 = 1797323) B1797323
theorem B1198223 : Blo 1196415 1198223 := bstep (se 1 (by rfl) ⟨898667, by rfl⟩ : syracuseStep 1198223 = 1797335) B1797335
theorem B1796267 : Blo 1196415 1796267 := bstep (se 1 (by rfl) ⟨1347200, by rfl⟩ : syracuseStep 1796267 = 2694401) B2694401
theorem B1198267 : Blo 1196415 1198267 := bstep (se 1 (by rfl) ⟨898700, by rfl⟩ : syracuseStep 1198267 = 1797401) B1797401
theorem B15337673 : Blo 1196415 15337673 := bstep (se 2 (by rfl) ⟨5751627, by rfl⟩ : syracuseStep 15337673 = 11503255) B11503255
theorem B10225865 : Blo 1196415 10225865 := bstep (se 2 (by rfl) ⟨3834699, by rfl⟩ : syracuseStep 10225865 = 7669399) B7669399
theorem B1796297 : Blo 1196415 1796297 := bstep (se 2 (by rfl) ⟨673611, by rfl⟩ : syracuseStep 1796297 = 1347223) B1347223
theorem B1198343 : Blo 1196415 1198343 := bstep (se 1 (by rfl) ⟨898757, by rfl⟩ : syracuseStep 1198343 = 1797515) B1797515
theorem B2271503 : Blo 1196415 2271503 := bstep (se 1 (by rfl) ⟨1703627, by rfl⟩ : syracuseStep 2271503 = 3407255) B3407255
theorem B6473999 : Blo 1196415 6473999 := bstep (se 1 (by rfl) ⟨4855499, by rfl⟩ : syracuseStep 6473999 = 9710999) B9710999
theorem B1198351 : Blo 1196415 1198351 := bstep (se 1 (by rfl) ⟨898763, by rfl⟩ : syracuseStep 1198351 = 1797527) B1797527
theorem B3033359 : Blo 1196415 3033359 := bstep (se 1 (by rfl) ⟨2275019, by rfl⟩ : syracuseStep 3033359 = 4550039) B4550039
theorem B1796411 : Blo 1196415 1796411 := bstep (se 1 (by rfl) ⟨1347308, by rfl⟩ : syracuseStep 1796411 = 2694617) B2694617
theorem B1198395 : Blo 1196415 1198395 := bstep (se 1 (by rfl) ⟨898796, by rfl⟩ : syracuseStep 1198395 = 1797593) B1797593
theorem B1796471 : Blo 1196415 1796471 := bstep (se 1 (by rfl) ⟨1347353, by rfl⟩ : syracuseStep 1796471 = 2694707) B2694707
theorem B1796495 : Blo 1196415 1796495 := bstep (se 1 (by rfl) ⟨1347371, by rfl⟩ : syracuseStep 1796495 = 2694743) B2694743
theorem B6818201 : Blo 1196415 6818201 := bstep (se 2 (by rfl) ⟨2556825, by rfl⟩ : syracuseStep 6818201 = 5113651) B5113651
theorem B1796537 : Blo 1196415 1796537 := bstep (se 2 (by rfl) ⟨673701, by rfl⟩ : syracuseStep 1796537 = 1347403) B1347403
theorem B1796615 : Blo 1196415 1796615 := bstep (se 1 (by rfl) ⟨1347461, by rfl⟩ : syracuseStep 1796615 = 2694923) B2694923
theorem B2877967 : Blo 1196415 2877967 := bstep (se 1 (by rfl) ⟨2158475, by rfl⟩ : syracuseStep 2877967 = 4316951) B4316951
theorem B1796651 : Blo 1196415 1796651 := bstep (se 1 (by rfl) ⟨1347488, by rfl⟩ : syracuseStep 1796651 = 2694977) B2694977
theorem B1346107 : Blo 1196415 1346107 := bstep (se 1 (by rfl) ⟨1009580, by rfl⟩ : syracuseStep 1346107 = 2019161) B2019161
theorem B1796681 : Blo 1196415 1796681 := bstep (se 2 (by rfl) ⟨673755, by rfl⟩ : syracuseStep 1796681 = 1347511) B1347511
theorem B1796795 : Blo 1196415 1796795 := bstep (se 1 (by rfl) ⟨1347596, by rfl⟩ : syracuseStep 1796795 = 2695193) B2695193
theorem B1796855 : Blo 1196415 1796855 := bstep (se 1 (by rfl) ⟨1347641, by rfl⟩ : syracuseStep 1796855 = 2695283) B2695283
theorem B3238667 : Blo 1196415 3238667 := bstep (se 1 (by rfl) ⟨2429000, by rfl⟩ : syracuseStep 3238667 = 4858001) B4858001
theorem B1796879 : Blo 1196415 1796879 := bstep (se 1 (by rfl) ⟨1347659, by rfl⟩ : syracuseStep 1796879 = 2695319) B2695319
theorem B2272043 : Blo 1196415 2272043 := bstep (se 1 (by rfl) ⟨1704032, by rfl⟩ : syracuseStep 2272043 = 3408065) B3408065
theorem B1796921 : Blo 1196415 1796921 := bstep (se 2 (by rfl) ⟨673845, by rfl⟩ : syracuseStep 1796921 = 1347691) B1347691
theorem B6064955 : Blo 1196415 6064955 := bstep (se 1 (by rfl) ⟨4548716, by rfl⟩ : syracuseStep 6064955 = 9097433) B9097433
theorem B1796999 : Blo 1196415 1796999 := bstep (se 1 (by rfl) ⟨1347749, by rfl⟩ : syracuseStep 1796999 = 2695499) B2695499
theorem B1797035 : Blo 1196415 1797035 := bstep (se 1 (by rfl) ⟨1347776, by rfl⟩ : syracuseStep 1797035 = 2695553) B2695553
theorem B2878409 : Blo 1196415 2878409 := bstep (se 2 (by rfl) ⟨1079403, by rfl⟩ : syracuseStep 2878409 = 2158807) B2158807
theorem B1797065 : Blo 1196415 1797065 := bstep (se 2 (by rfl) ⟨673899, by rfl⟩ : syracuseStep 1797065 = 1347799) B1347799
theorem B6065117 : Blo 1196415 6065117 := bstep (se 3 (by rfl) ⟨1137209, by rfl⟩ : syracuseStep 6065117 = 2274419) B2274419
theorem B1346575 : Blo 1196415 1346575 := bstep (se 1 (by rfl) ⟨1009931, by rfl⟩ : syracuseStep 1346575 = 2019863) B2019863
theorem B1797179 : Blo 1196415 1797179 := bstep (se 1 (by rfl) ⟨1347884, by rfl⟩ : syracuseStep 1797179 = 2695769) B2695769
theorem B1797239 : Blo 1196415 1797239 := bstep (se 1 (by rfl) ⟨1347929, by rfl⟩ : syracuseStep 1797239 = 2695859) B2695859
theorem B1797263 : Blo 1196415 1797263 := bstep (se 1 (by rfl) ⟨1347947, by rfl⟩ : syracuseStep 1797263 = 2695895) B2695895
theorem B1797305 : Blo 1196415 1797305 := bstep (se 2 (by rfl) ⟨673989, by rfl⟩ : syracuseStep 1797305 = 1347979) B1347979
theorem B1797383 : Blo 1196415 1797383 := bstep (se 1 (by rfl) ⟨1348037, by rfl⟩ : syracuseStep 1797383 = 2696075) B2696075
theorem B6065441 : Blo 1196415 6065441 := bstep (se 2 (by rfl) ⟨2274540, by rfl⟩ : syracuseStep 6065441 = 4549081) B4549081
theorem B1797419 : Blo 1196415 1797419 := bstep (se 1 (by rfl) ⟨1348064, by rfl⟩ : syracuseStep 1797419 = 2696129) B2696129
theorem B1797449 : Blo 1196415 1797449 := bstep (se 2 (by rfl) ⟨674043, by rfl⟩ : syracuseStep 1797449 = 1348087) B1348087
theorem B4042169 : Blo 1196415 4042169 := bstep (se 2 (by rfl) ⟨1515813, by rfl⟩ : syracuseStep 4042169 = 3031627) B3031627
theorem B1797563 : Blo 1196415 1797563 := bstep (se 1 (by rfl) ⟨1348172, by rfl⟩ : syracuseStep 1797563 = 2696345) B2696345
theorem B1822139 : Blo 1196415 1822139 := bstep (se 1 (by rfl) ⟨1366604, by rfl⟩ : syracuseStep 1822139 = 2733209) B2733209
theorem B1797623 : Blo 1196415 1797623 := bstep (se 1 (by rfl) ⟨1348217, by rfl⟩ : syracuseStep 1797623 = 2696435) B2696435
theorem B1347079 : Blo 1196415 1347079 := bstep (se 1 (by rfl) ⟨1010309, by rfl⟩ : syracuseStep 1347079 = 2020619) B2020619
theorem B1437355 : Blo 1196415 1437355 := bstep (se 1 (by rfl) ⟨1078016, by rfl⟩ : syracuseStep 1437355 = 2156033) B2156033
theorem B5828269 : Blo 1196415 5828269 := bstep (se 3 (by rfl) ⟨1092800, by rfl⟩ : syracuseStep 5828269 = 2185601) B2185601
theorem B1347259 : Blo 1196415 1347259 := bstep (se 1 (by rfl) ⟨1010444, by rfl⟩ : syracuseStep 1347259 = 2020889) B2020889
theorem B6057665 : Blo 1196415 6057665 := bstep (se 2 (by rfl) ⟨2271624, by rfl⟩ : syracuseStep 6057665 = 4543249) B4543249
theorem B6917921 : Blo 1196415 6917921 := bstep (se 2 (by rfl) ⟨2594220, by rfl⟩ : syracuseStep 6917921 = 5188441) B5188441
theorem B10227505 : Blo 1196415 10227505 := bstep (se 2 (by rfl) ⟨3835314, by rfl⟩ : syracuseStep 10227505 = 7670629) B7670629
theorem B24571765 : Blo 1196415 24571765 := bstep (se 5 (by rfl) ⟨1151801, by rfl⟩ : syracuseStep 24571765 = 2303603) B2303603
theorem B2273159 : Blo 1196415 2273159 := bstep (se 1 (by rfl) ⟨1704869, by rfl⟩ : syracuseStep 2273159 = 3409739) B3409739
theorem B3502081 : Blo 1196415 3502081 := bstep (se 2 (by rfl) ⟨1313280, by rfl⟩ : syracuseStep 3502081 = 2626561) B2626561
theorem B4042763 : Blo 1196415 4042763 := bstep (se 1 (by rfl) ⟨3032072, by rfl⟩ : syracuseStep 4042763 = 6064145) B6064145
theorem B2019343 : Blo 1196415 2019343 := bstep (se 1 (by rfl) ⟨1514507, by rfl⟩ : syracuseStep 2019343 = 3029015) B3029015
theorem B3411983 : Blo 1196415 3411983 := bstep (se 1 (by rfl) ⟨2558987, by rfl⟩ : syracuseStep 3411983 = 5117975) B5117975
theorem B4042871 : Blo 1196415 4042871 := bstep (se 1 (by rfl) ⟨3032153, by rfl⟩ : syracuseStep 4042871 = 6064307) B6064307
theorem B2732167 : Blo 1196415 2732167 := bstep (se 1 (by rfl) ⟨2049125, by rfl⟩ : syracuseStep 2732167 = 4098251) B4098251
theorem B1347727 : Blo 1196415 1347727 := bstep (se 1 (by rfl) ⟨1010795, by rfl⟩ : syracuseStep 1347727 = 2021591) B2021591
theorem B6475949 : Blo 1196415 6475949 := bstep (se 3 (by rfl) ⟨1214240, by rfl⟩ : syracuseStep 6475949 = 2428481) B2428481
theorem B6066413 : Blo 1196415 6066413 := bstep (se 3 (by rfl) ⟨1137452, by rfl⟩ : syracuseStep 6066413 = 2274905) B2274905
theorem B4313345 : Blo 1196415 4313345 := bstep (se 2 (by rfl) ⟨1617504, by rfl⟩ : syracuseStep 4313345 = 3235009) B3235009
theorem B2273683 : Blo 1196415 2273683 := bstep (se 1 (by rfl) ⟨1705262, by rfl⟩ : syracuseStep 2273683 = 3410525) B3410525
theorem B2019883 : Blo 1196415 2019883 := bstep (se 1 (by rfl) ⟨1514912, by rfl⟩ : syracuseStep 2019883 = 3029825) B3029825
theorem B4543037 : Blo 1196415 4543037 := bstep (se 3 (by rfl) ⟨851819, by rfl⟩ : syracuseStep 4543037 = 1703639) B1703639
theorem B2020025 : Blo 1196415 2020025 := bstep (se 2 (by rfl) ⟨757509, by rfl⟩ : syracuseStep 2020025 = 1515019) B1515019
theorem B4043465 : Blo 1196415 4043465 := bstep (se 2 (by rfl) ⟨1516299, by rfl⟩ : syracuseStep 4043465 = 3032599) B3032599
theorem B2732843 : Blo 1196415 2732843 := bstep (se 1 (by rfl) ⟨2049632, by rfl⟩ : syracuseStep 2732843 = 4099265) B4099265
theorem B2692025 : Blo 1196415 2692025 := bstep (se 2 (by rfl) ⟨1009509, by rfl⟩ : syracuseStep 2692025 = 2019019) B2019019
theorem B6058961 : Blo 1196415 6058961 := bstep (se 2 (by rfl) ⟨2272110, by rfl⟩ : syracuseStep 6058961 = 4544221) B4544221
theorem B3839005 : Blo 1196415 3839005 := bstep (se 3 (by rfl) ⟨719813, by rfl⟩ : syracuseStep 3839005 = 1439627) B1439627
theorem B2692367 : Blo 1196415 2692367 := bstep (se 1 (by rfl) ⟨2019275, by rfl⟩ : syracuseStep 2692367 = 4038551) B4038551
theorem B4371727 : Blo 1196415 4371727 := bstep (se 1 (by rfl) ⟨3278795, by rfl⟩ : syracuseStep 4371727 = 6557591) B6557591
theorem B2692385 : Blo 1196415 2692385 := bstep (se 2 (by rfl) ⟨1009644, by rfl⟩ : syracuseStep 2692385 = 2019289) B2019289
theorem B3282209 : Blo 1196415 3282209 := bstep (se 2 (by rfl) ⟨1230828, by rfl⟩ : syracuseStep 3282209 = 2461657) B2461657
theorem B2020727 : Blo 1196415 2020727 := bstep (se 1 (by rfl) ⟨1515545, by rfl⟩ : syracuseStep 2020727 = 3031091) B3031091
theorem B4044167 : Blo 1196415 4044167 := bstep (se 1 (by rfl) ⟨3033125, by rfl⟩ : syracuseStep 4044167 = 6066251) B6066251
theorem B1439147 : Blo 1196415 1439147 := bstep (se 1 (by rfl) ⟨1079360, by rfl⟩ : syracuseStep 1439147 = 2158721) B2158721
theorem B11064761 : Blo 1196415 11064761 := bstep (se 2 (by rfl) ⟨4149285, by rfl⟩ : syracuseStep 11064761 = 8298571) B8298571
theorem B15562169 : Blo 1196415 15562169 := bstep (se 2 (by rfl) ⟨5835813, by rfl⟩ : syracuseStep 15562169 = 11671627) B11671627
theorem B2274875 : Blo 1196415 2274875 := bstep (se 1 (by rfl) ⟨1706156, by rfl⟩ : syracuseStep 2274875 = 3412313) B3412313
theorem B2692727 : Blo 1196415 2692727 := bstep (se 1 (by rfl) ⟨2019545, by rfl⟩ : syracuseStep 2692727 = 4039091) B4039091
theorem B4044545 : Blo 1196415 4044545 := bstep (se 2 (by rfl) ⟨1516704, by rfl⟩ : syracuseStep 4044545 = 3033409) B3033409
theorem B2692907 : Blo 1196415 2692907 := bstep (se 1 (by rfl) ⟨2019680, by rfl⟩ : syracuseStep 2692907 = 4039361) B4039361
theorem B2021179 : Blo 1196415 2021179 := bstep (se 1 (by rfl) ⟨1515884, by rfl⟩ : syracuseStep 2021179 = 3031769) B3031769
theorem B3028823 : Blo 1196415 3028823 := bstep (se 1 (by rfl) ⟨2271617, by rfl⟩ : syracuseStep 3028823 = 4543235) B4543235
theorem B1439623 : Blo 1196415 1439623 := bstep (se 1 (by rfl) ⟨1079717, by rfl⟩ : syracuseStep 1439623 = 2159435) B2159435
theorem B2021321 : Blo 1196415 2021321 := bstep (se 2 (by rfl) ⟨757995, by rfl⟩ : syracuseStep 2021321 = 1515991) B1515991
theorem B6821891 : Blo 1196415 6821891 := bstep (se 1 (by rfl) ⟨5116418, by rfl⟩ : syracuseStep 6821891 = 10232837) B10232837
theorem B3029035 : Blo 1196415 3029035 := bstep (se 1 (by rfl) ⟨2271776, by rfl⟩ : syracuseStep 3029035 = 4543553) B4543553
theorem B3323965 : Blo 1196415 3323965 := bstep (se 3 (by rfl) ⟨623243, by rfl⟩ : syracuseStep 3323965 = 1246487) B1246487
theorem B2693267 : Blo 1196415 2693267 := bstep (se 1 (by rfl) ⟨2019950, by rfl⟩ : syracuseStep 2693267 = 4039901) B4039901
theorem B3029177 : Blo 1196415 3029177 := bstep (se 2 (by rfl) ⟨1135941, by rfl⟩ : syracuseStep 3029177 = 2271883) B2271883
theorem B2693321 : Blo 1196415 2693321 := bstep (se 2 (by rfl) ⟨1009995, by rfl⟩ : syracuseStep 2693321 = 2019991) B2019991
theorem B3234059 : Blo 1196415 3234059 := bstep (se 1 (by rfl) ⟨2425544, by rfl⟩ : syracuseStep 3234059 = 4851089) B4851089
theorem B2955791 : Blo 1196415 2955791 := bstep (se 1 (by rfl) ⟨2216843, by rfl⟩ : syracuseStep 2955791 = 4433687) B4433687
theorem B6814327 : Blo 1196415 6814327 := bstep (se 1 (by rfl) ⟨5110745, by rfl⟩ : syracuseStep 6814327 = 10221491) B10221491
theorem B2022023 : Blo 1196415 2022023 := bstep (se 1 (by rfl) ⟨1516517, by rfl⟩ : syracuseStep 2022023 = 3033035) B3033035
theorem B9222913 : Blo 1196415 9222913 := bstep (se 2 (by rfl) ⟨3458592, by rfl⟩ : syracuseStep 9222913 = 6917185) B6917185
theorem B2694023 : Blo 1196415 2694023 := bstep (se 1 (by rfl) ⟨2020517, by rfl⟩ : syracuseStep 2694023 = 4041035) B4041035
theorem B4316057 : Blo 1196415 4316057 := bstep (se 2 (by rfl) ⟨1618521, by rfl⟩ : syracuseStep 4316057 = 3237043) B3237043
theorem B32783267 : Blo 1196415 32783267 := bstep (se 1 (by rfl) ⟨24587450, by rfl⟩ : syracuseStep 32783267 = 49174901) B49174901
theorem B4316113 : Blo 1196415 4316113 := bstep (se 2 (by rfl) ⟨1618542, by rfl⟩ : syracuseStep 4316113 = 3237085) B3237085
theorem B6061067 : Blo 1196415 6061067 := bstep (se 1 (by rfl) ⟨4545800, by rfl⟩ : syracuseStep 6061067 = 9091601) B9091601
theorem B15350795 : Blo 1196415 15350795 := bstep (se 1 (by rfl) ⟨11513096, by rfl⟩ : syracuseStep 15350795 = 23026193) B23026193
theorem B2694203 : Blo 1196415 2694203 := bstep (se 1 (by rfl) ⟨2020652, by rfl⟩ : syracuseStep 2694203 = 4041305) B4041305
theorem B9100349 : Blo 1196415 9100349 := bstep (se 3 (by rfl) ⟨1706315, by rfl⟩ : syracuseStep 9100349 = 3412631) B3412631
theorem B14965877 : Blo 1196415 14965877 := bstep (se 5 (by rfl) ⟨701525, by rfl⟩ : syracuseStep 14965877 = 1403051) B1403051
theorem B1514639 : Blo 1196415 1514639 := bstep (se 1 (by rfl) ⟨1135979, by rfl⟩ : syracuseStep 1514639 = 2271959) B2271959
theorem B3030169 : Blo 1196415 3030169 := bstep (se 2 (by rfl) ⟨1136313, by rfl⟩ : syracuseStep 3030169 = 2272627) B2272627
theorem B6061229 : Blo 1196415 6061229 := bstep (se 3 (by rfl) ⟨1136480, by rfl⟩ : syracuseStep 6061229 = 2272961) B2272961
theorem B2694329 : Blo 1196415 2694329 := bstep (se 2 (by rfl) ⟨1010373, by rfl⟩ : syracuseStep 2694329 = 2020747) B2020747
theorem B4037903 : Blo 1196415 4037903 := bstep (se 1 (by rfl) ⟨3028427, by rfl⟩ : syracuseStep 4037903 = 6056855) B6056855
theorem B3030331 : Blo 1196415 3030331 := bstep (se 1 (by rfl) ⟨2272748, by rfl⟩ : syracuseStep 3030331 = 4545497) B4545497
theorem B5832089 : Blo 1196415 5832089 := bstep (se 2 (by rfl) ⟨2187033, by rfl⟩ : syracuseStep 5832089 = 4374067) B4374067
theorem B5111225 : Blo 1196415 5111225 := bstep (se 2 (by rfl) ⟨1916709, by rfl⟩ : syracuseStep 5111225 = 3833419) B3833419
theorem B3030473 : Blo 1196415 3030473 := bstep (se 2 (by rfl) ⟨1136427, by rfl⟩ : syracuseStep 3030473 = 2272855) B2272855
theorem B29122001 : Blo 1196415 29122001 := bstep (se 2 (by rfl) ⟨10920750, by rfl⟩ : syracuseStep 29122001 = 21841501) B21841501
theorem B9092573 : Blo 1196415 9092573 := bstep (se 3 (by rfl) ⟨1704857, by rfl⟩ : syracuseStep 9092573 = 3409715) B3409715
theorem B2694671 : Blo 1196415 2694671 := bstep (se 1 (by rfl) ⟨2021003, by rfl⟩ : syracuseStep 2694671 = 4042007) B4042007
theorem B4038173 : Blo 1196415 4038173 := bstep (se 3 (by rfl) ⟨757157, by rfl⟩ : syracuseStep 4038173 = 1514315) B1514315
theorem B2694689 : Blo 1196415 2694689 := bstep (se 2 (by rfl) ⟨1010508, by rfl⟩ : syracuseStep 2694689 = 2021017) B2021017
theorem B12951107 : Blo 1196415 12951107 := bstep (se 1 (by rfl) ⟨9713330, by rfl⟩ : syracuseStep 12951107 = 19426661) B19426661
theorem B2768503 : Blo 1196415 2768503 := bstep (se 1 (by rfl) ⟨2076377, by rfl⟩ : syracuseStep 2768503 = 4152755) B4152755
theorem B1556231 : Blo 1196415 1556231 := bstep (se 1 (by rfl) ⟨1167173, by rfl⟩ : syracuseStep 1556231 = 2334347) B2334347
theorem B3030817 : Blo 1196415 3030817 := bstep (se 2 (by rfl) ⟨1136556, by rfl⟩ : syracuseStep 3030817 = 2273113) B2273113
theorem B2555707 : Blo 1196415 2555707 := bstep (se 1 (by rfl) ⟨1916780, by rfl⟩ : syracuseStep 2555707 = 3833561) B3833561
theorem B6815603 : Blo 1196415 6815603 := bstep (se 1 (by rfl) ⟨5111702, by rfl⟩ : syracuseStep 6815603 = 10223405) B10223405
theorem B2695031 : Blo 1196415 2695031 := bstep (se 1 (by rfl) ⟨2021273, by rfl⟩ : syracuseStep 2695031 = 4042547) B4042547
theorem B5111687 : Blo 1196415 5111687 := bstep (se 1 (by rfl) ⟨3833765, by rfl⟩ : syracuseStep 5111687 = 7667531) B7667531
theorem B4546439 : Blo 1196415 4546439 := bstep (se 1 (by rfl) ⟨3409829, by rfl⟩ : syracuseStep 4546439 = 6819659) B6819659
theorem B18677765 : Blo 1196415 18677765 := bstep (se 4 (by rfl) ⟨1751040, by rfl⟩ : syracuseStep 18677765 = 3502081) B3502081
theorem B2695175 : Blo 1196415 2695175 := bstep (se 1 (by rfl) ⟨2021381, by rfl⟩ : syracuseStep 2695175 = 4042763) B4042763
theorem B4038713 : Blo 1196415 4038713 := bstep (se 2 (by rfl) ⟨1514517, by rfl⟩ : syracuseStep 4038713 = 3029035) B3029035
theorem B2695247 : Blo 1196415 2695247 := bstep (se 1 (by rfl) ⟨2021435, by rfl⟩ : syracuseStep 2695247 = 4042871) B4042871
theorem B4431953 : Blo 1196415 4431953 := bstep (se 2 (by rfl) ⟨1661982, by rfl⟩ : syracuseStep 4431953 = 3323965) B3323965
theorem B4317299 : Blo 1196415 4317299 := bstep (se 1 (by rfl) ⟨3237974, by rfl⟩ : syracuseStep 4317299 = 6475949) B6475949
theorem B63971477 : Blo 1196415 63971477 := bstep (se 6 (by rfl) ⟨1499331, by rfl⟩ : syracuseStep 63971477 = 2998663) B2998663
theorem B5833021 : Blo 1196415 5833021 := bstep (se 3 (by rfl) ⟨1093691, by rfl⟩ : syracuseStep 5833021 = 2187383) B2187383
theorem B4039037 : Blo 1196415 4039037 := bstep (se 3 (by rfl) ⟨757319, by rfl⟩ : syracuseStep 4039037 = 1514639) B1514639
theorem B3408257 : Blo 1196415 3408257 := bstep (se 2 (by rfl) ⟨1278096, by rfl⟩ : syracuseStep 3408257 = 2556193) B2556193
theorem B1196463 : Blo 1196415 1196463 := bstep (se 1 (by rfl) ⟨897347, by rfl⟩ : syracuseStep 1196463 = 1794695) B1794695
theorem B1196487 : Blo 1196415 1196487 := bstep (se 1 (by rfl) ⟨897365, by rfl⟩ : syracuseStep 1196487 = 1794731) B1794731
theorem B1196507 : Blo 1196415 1196507 := bstep (se 1 (by rfl) ⟨897380, by rfl⟩ : syracuseStep 1196507 = 1794761) B1794761
theorem B2695643 : Blo 1196415 2695643 := bstep (se 1 (by rfl) ⟨2021732, by rfl⟩ : syracuseStep 2695643 = 4043465) B4043465
theorem B4096499 : Blo 1196415 4096499 := bstep (se 1 (by rfl) ⟨3072374, by rfl⟩ : syracuseStep 4096499 = 6144749) B6144749
theorem B3031577 : Blo 1196415 3031577 := bstep (se 2 (by rfl) ⟨1136841, by rfl⟩ : syracuseStep 3031577 = 2273683) B2273683
theorem B1196583 : Blo 1196415 1196583 := bstep (se 1 (by rfl) ⟨897437, by rfl⟩ : syracuseStep 1196583 = 1794875) B1794875
theorem B1196623 : Blo 1196415 1196623 := bstep (se 1 (by rfl) ⟨897467, by rfl⟩ : syracuseStep 1196623 = 1794935) B1794935
theorem B1196639 : Blo 1196415 1196639 := bstep (se 1 (by rfl) ⟨897479, by rfl⟩ : syracuseStep 1196639 = 1794959) B1794959
theorem B1794683 : Blo 1196415 1794683 := bstep (se 1 (by rfl) ⟨1346012, by rfl⟩ : syracuseStep 1794683 = 2692025) B2692025
theorem B1196667 : Blo 1196415 1196667 := bstep (se 1 (by rfl) ⟨897500, by rfl⟩ : syracuseStep 1196667 = 1795001) B1795001
theorem B4039307 : Blo 1196415 4039307 := bstep (se 1 (by rfl) ⟨3029480, by rfl⟩ : syracuseStep 4039307 = 6058961) B6058961
theorem B11502253 : Blo 1196415 11502253 := bstep (se 3 (by rfl) ⟨2156672, by rfl⟩ : syracuseStep 11502253 = 4313345) B4313345
theorem B1196719 : Blo 1196415 1196719 := bstep (se 1 (by rfl) ⟨897539, by rfl⟩ : syracuseStep 1196719 = 1795079) B1795079
theorem B1196743 : Blo 1196415 1196743 := bstep (se 1 (by rfl) ⟨897557, by rfl⟩ : syracuseStep 1196743 = 1795115) B1795115
theorem B1196763 : Blo 1196415 1196763 := bstep (se 1 (by rfl) ⟨897572, by rfl⟩ : syracuseStep 1196763 = 1795145) B1795145
theorem B1794809 : Blo 1196415 1794809 := bstep (se 2 (by rfl) ⟨673053, by rfl⟩ : syracuseStep 1794809 = 1346107) B1346107
theorem B1196839 : Blo 1196415 1196839 := bstep (se 1 (by rfl) ⟨897629, by rfl⟩ : syracuseStep 1196839 = 1795259) B1795259
theorem B1213223 : Blo 1196415 1213223 := bstep (se 1 (by rfl) ⟨909917, by rfl⟩ : syracuseStep 1213223 = 1819835) B1819835
theorem B9085769 : Blo 1196415 9085769 := bstep (se 2 (by rfl) ⟨3407163, by rfl⟩ : syracuseStep 9085769 = 6814327) B6814327
theorem B3408713 : Blo 1196415 3408713 := bstep (se 2 (by rfl) ⟨1278267, by rfl⟩ : syracuseStep 3408713 = 2556535) B2556535
theorem B1196879 : Blo 1196415 1196879 := bstep (se 1 (by rfl) ⟨897659, by rfl⟩ : syracuseStep 1196879 = 1795319) B1795319
theorem B1794911 : Blo 1196415 1794911 := bstep (se 1 (by rfl) ⟨1346183, by rfl⟩ : syracuseStep 1794911 = 2692367) B2692367
theorem B1196895 : Blo 1196415 1196895 := bstep (se 1 (by rfl) ⟨897671, by rfl⟩ : syracuseStep 1196895 = 1795343) B1795343
theorem B1794923 : Blo 1196415 1794923 := bstep (se 1 (by rfl) ⟨1346192, by rfl⟩ : syracuseStep 1794923 = 2692385) B2692385
theorem B2188139 : Blo 1196415 2188139 := bstep (se 1 (by rfl) ⟨1641104, by rfl⟩ : syracuseStep 2188139 = 3282209) B3282209
theorem B1196923 : Blo 1196415 1196923 := bstep (se 1 (by rfl) ⟨897692, by rfl⟩ : syracuseStep 1196923 = 1795385) B1795385
theorem B1196975 : Blo 1196415 1196975 := bstep (se 1 (by rfl) ⟨897731, by rfl⟩ : syracuseStep 1196975 = 1795463) B1795463
theorem B2696111 : Blo 1196415 2696111 := bstep (se 1 (by rfl) ⟨2022083, by rfl⟩ : syracuseStep 2696111 = 4044167) B4044167
theorem B1196999 : Blo 1196415 1196999 := bstep (se 1 (by rfl) ⟨897749, by rfl⟩ : syracuseStep 1196999 = 1795499) B1795499
theorem B1197019 : Blo 1196415 1197019 := bstep (se 1 (by rfl) ⟨897764, by rfl⟩ : syracuseStep 1197019 = 1795529) B1795529
theorem B12297217 : Blo 1196415 12297217 := bstep (se 2 (by rfl) ⟨4611456, by rfl⟩ : syracuseStep 12297217 = 9222913) B9222913
theorem B1197095 : Blo 1196415 1197095 := bstep (se 1 (by rfl) ⟨897821, by rfl⟩ : syracuseStep 1197095 = 1795643) B1795643
theorem B1516583 : Blo 1196415 1516583 := bstep (se 1 (by rfl) ⟨1137437, by rfl⟩ : syracuseStep 1516583 = 2274875) B2274875
theorem B1795151 : Blo 1196415 1795151 := bstep (se 1 (by rfl) ⟨1346363, by rfl⟩ : syracuseStep 1795151 = 2692727) B2692727
theorem B1197135 : Blo 1196415 1197135 := bstep (se 1 (by rfl) ⟨897851, by rfl⟩ : syracuseStep 1197135 = 1795703) B1795703
theorem B1197151 : Blo 1196415 1197151 := bstep (se 1 (by rfl) ⟨897863, by rfl⟩ : syracuseStep 1197151 = 1795727) B1795727
theorem B1197179 : Blo 1196415 1197179 := bstep (se 1 (by rfl) ⟨897884, by rfl⟩ : syracuseStep 1197179 = 1795769) B1795769
theorem B3409067 : Blo 1196415 3409067 := bstep (se 1 (by rfl) ⟨2556800, by rfl⟩ : syracuseStep 3409067 = 5113601) B5113601
theorem B2557099 : Blo 1196415 2557099 := bstep (se 1 (by rfl) ⟨1917824, by rfl⟩ : syracuseStep 2557099 = 3835649) B3835649
theorem B2696363 : Blo 1196415 2696363 := bstep (se 1 (by rfl) ⟨2022272, by rfl⟩ : syracuseStep 2696363 = 4044545) B4044545
theorem B1197231 : Blo 1196415 1197231 := bstep (se 1 (by rfl) ⟨897923, by rfl⟩ : syracuseStep 1197231 = 1795847) B1795847
theorem B1795271 : Blo 1196415 1795271 := bstep (se 1 (by rfl) ⟨1346453, by rfl⟩ : syracuseStep 1795271 = 2692907) B2692907
theorem B1197255 : Blo 1196415 1197255 := bstep (se 1 (by rfl) ⟨897941, by rfl⟩ : syracuseStep 1197255 = 1795883) B1795883
theorem B1197275 : Blo 1196415 1197275 := bstep (se 1 (by rfl) ⟨897956, by rfl⟩ : syracuseStep 1197275 = 1795913) B1795913
theorem B1197351 : Blo 1196415 1197351 := bstep (se 1 (by rfl) ⟨898013, by rfl⟩ : syracuseStep 1197351 = 1796027) B1796027
theorem B1197391 : Blo 1196415 1197391 := bstep (se 1 (by rfl) ⟨898043, by rfl⟩ : syracuseStep 1197391 = 1796087) B1796087
theorem B4547927 : Blo 1196415 4547927 := bstep (se 1 (by rfl) ⟨3410945, by rfl⟩ : syracuseStep 4547927 = 6821891) B6821891
theorem B1197407 : Blo 1196415 1197407 := bstep (se 1 (by rfl) ⟨898055, by rfl⟩ : syracuseStep 1197407 = 1796111) B1796111
theorem B1795433 : Blo 1196415 1795433 := bstep (se 2 (by rfl) ⟨673287, by rfl⟩ : syracuseStep 1795433 = 1346575) B1346575
theorem B1197435 : Blo 1196415 1197435 := bstep (se 1 (by rfl) ⟨898076, by rfl⟩ : syracuseStep 1197435 = 1796153) B1796153
theorem B7882109 : Blo 1196415 7882109 := bstep (se 3 (by rfl) ⟨1477895, by rfl⟩ : syracuseStep 7882109 = 2955791) B2955791
theorem B1197487 : Blo 1196415 1197487 := bstep (se 1 (by rfl) ⟨898115, by rfl⟩ : syracuseStep 1197487 = 1796231) B1796231
theorem B2049455 : Blo 1196415 2049455 := bstep (se 1 (by rfl) ⟨1537091, by rfl⟩ : syracuseStep 2049455 = 3074183) B3074183
theorem B1795511 : Blo 1196415 1795511 := bstep (se 1 (by rfl) ⟨1346633, by rfl⟩ : syracuseStep 1795511 = 2693267) B2693267
theorem B1197511 : Blo 1196415 1197511 := bstep (se 1 (by rfl) ⟨898133, by rfl⟩ : syracuseStep 1197511 = 1796267) B1796267
theorem B10225115 : Blo 1196415 10225115 := bstep (se 1 (by rfl) ⟨7668836, by rfl⟩ : syracuseStep 10225115 = 15337673) B15337673
theorem B6817243 : Blo 1196415 6817243 := bstep (se 1 (by rfl) ⟨5112932, by rfl⟩ : syracuseStep 6817243 = 10225865) B10225865
theorem B1795547 : Blo 1196415 1795547 := bstep (se 1 (by rfl) ⟨1346660, by rfl⟩ : syracuseStep 1795547 = 2693321) B2693321
theorem B1197531 : Blo 1196415 1197531 := bstep (se 1 (by rfl) ⟨898148, by rfl⟩ : syracuseStep 1197531 = 1796297) B1796297
theorem B2156039 : Blo 1196415 2156039 := bstep (se 1 (by rfl) ⟨1617029, by rfl⟩ : syracuseStep 2156039 = 3234059) B3234059
theorem B2917913 : Blo 1196415 2917913 := bstep (se 2 (by rfl) ⟨1094217, by rfl⟩ : syracuseStep 2917913 = 2188435) B2188435
theorem B4040225 : Blo 1196415 4040225 := bstep (se 2 (by rfl) ⟨1515084, by rfl⟩ : syracuseStep 4040225 = 3030169) B3030169
theorem B1197607 : Blo 1196415 1197607 := bstep (se 1 (by rfl) ⟨898205, by rfl⟩ : syracuseStep 1197607 = 1796411) B1796411
theorem B1197647 : Blo 1196415 1197647 := bstep (se 1 (by rfl) ⟨898235, by rfl⟩ : syracuseStep 1197647 = 1796471) B1796471
theorem B1197663 : Blo 1196415 1197663 := bstep (se 1 (by rfl) ⟨898247, by rfl⟩ : syracuseStep 1197663 = 1796495) B1796495
theorem B1197691 : Blo 1196415 1197691 := bstep (se 1 (by rfl) ⟨898268, by rfl⟩ : syracuseStep 1197691 = 1796537) B1796537
theorem B1197743 : Blo 1196415 1197743 := bstep (se 1 (by rfl) ⟨898307, by rfl⟩ : syracuseStep 1197743 = 1796615) B1796615
theorem B1197767 : Blo 1196415 1197767 := bstep (se 1 (by rfl) ⟨898325, by rfl⟩ : syracuseStep 1197767 = 1796651) B1796651
theorem B1197787 : Blo 1196415 1197787 := bstep (se 1 (by rfl) ⟨898340, by rfl⟩ : syracuseStep 1197787 = 1796681) B1796681
theorem B4040441 : Blo 1196415 4040441 := bstep (se 2 (by rfl) ⟨1515165, by rfl⟩ : syracuseStep 4040441 = 3030331) B3030331
theorem B1197863 : Blo 1196415 1197863 := bstep (se 1 (by rfl) ⟨898397, by rfl⟩ : syracuseStep 1197863 = 1796795) B1796795
theorem B1197903 : Blo 1196415 1197903 := bstep (se 1 (by rfl) ⟨898427, by rfl⟩ : syracuseStep 1197903 = 1796855) B1796855
theorem B1197919 : Blo 1196415 1197919 := bstep (se 1 (by rfl) ⟨898439, by rfl⟩ : syracuseStep 1197919 = 1796879) B1796879
theorem B1197947 : Blo 1196415 1197947 := bstep (se 1 (by rfl) ⟨898460, by rfl⟩ : syracuseStep 1197947 = 1796921) B1796921
theorem B1796015 : Blo 1196415 1796015 := bstep (se 1 (by rfl) ⟨1347011, by rfl⟩ : syracuseStep 1796015 = 2694023) B2694023
theorem B1197999 : Blo 1196415 1197999 := bstep (se 1 (by rfl) ⟨898499, by rfl⟩ : syracuseStep 1197999 = 1796999) B1796999
theorem B2877371 : Blo 1196415 2877371 := bstep (se 1 (by rfl) ⟨2158028, by rfl⟩ : syracuseStep 2877371 = 4316057) B4316057
theorem B131049413 : Blo 1196415 131049413 := bstep (se 4 (by rfl) ⟨12285882, by rfl⟩ : syracuseStep 131049413 = 24571765) B24571765
theorem B1198023 : Blo 1196415 1198023 := bstep (se 1 (by rfl) ⟨898517, by rfl⟩ : syracuseStep 1198023 = 1797035) B1797035
theorem B1918939 : Blo 1196415 1918939 := bstep (se 1 (by rfl) ⟨1439204, by rfl⟩ : syracuseStep 1918939 = 2878409) B2878409
theorem B1198043 : Blo 1196415 1198043 := bstep (se 1 (by rfl) ⟨898532, by rfl⟩ : syracuseStep 1198043 = 1797065) B1797065
theorem B4040711 : Blo 1196415 4040711 := bstep (se 1 (by rfl) ⟨3030533, by rfl⟩ : syracuseStep 4040711 = 6061067) B6061067
theorem B10233863 : Blo 1196415 10233863 := bstep (se 1 (by rfl) ⟨7675397, by rfl⟩ : syracuseStep 10233863 = 15350795) B15350795
theorem B1796105 : Blo 1196415 1796105 := bstep (se 2 (by rfl) ⟨673539, by rfl⟩ : syracuseStep 1796105 = 1347079) B1347079
theorem B7677989 : Blo 1196415 7677989 := bstep (se 4 (by rfl) ⟨719811, by rfl⟩ : syracuseStep 7677989 = 1439623) B1439623
theorem B1796135 : Blo 1196415 1796135 := bstep (se 1 (by rfl) ⟨1347101, by rfl⟩ : syracuseStep 1796135 = 2694203) B2694203
theorem B1198119 : Blo 1196415 1198119 := bstep (se 1 (by rfl) ⟨898589, by rfl⟩ : syracuseStep 1198119 = 1797179) B1797179
theorem B1198159 : Blo 1196415 1198159 := bstep (se 1 (by rfl) ⟨898619, by rfl⟩ : syracuseStep 1198159 = 1797239) B1797239
theorem B1198175 : Blo 1196415 1198175 := bstep (se 1 (by rfl) ⟨898631, by rfl⟩ : syracuseStep 1198175 = 1797263) B1797263
theorem B4040819 : Blo 1196415 4040819 := bstep (se 1 (by rfl) ⟨3030614, by rfl⟩ : syracuseStep 4040819 = 6061229) B6061229
theorem B1796219 : Blo 1196415 1796219 := bstep (se 1 (by rfl) ⟨1347164, by rfl⟩ : syracuseStep 1796219 = 2694329) B2694329
theorem B1198203 : Blo 1196415 1198203 := bstep (se 1 (by rfl) ⟨898652, by rfl⟩ : syracuseStep 1198203 = 1797305) B1797305
theorem B1198255 : Blo 1196415 1198255 := bstep (se 1 (by rfl) ⟨898691, by rfl⟩ : syracuseStep 1198255 = 1797383) B1797383
theorem B1198279 : Blo 1196415 1198279 := bstep (se 1 (by rfl) ⟨898709, by rfl⟩ : syracuseStep 1198279 = 1797419) B1797419
theorem B1198299 : Blo 1196415 1198299 := bstep (se 1 (by rfl) ⟨898724, by rfl⟩ : syracuseStep 1198299 = 1797449) B1797449
theorem B1796345 : Blo 1196415 1796345 := bstep (se 2 (by rfl) ⟨673629, by rfl⟩ : syracuseStep 1796345 = 1347259) B1347259
theorem B1198375 : Blo 1196415 1198375 := bstep (se 1 (by rfl) ⟨898781, by rfl⟩ : syracuseStep 1198375 = 1797563) B1797563
theorem B1214759 : Blo 1196415 1214759 := bstep (se 1 (by rfl) ⟨911069, by rfl⟩ : syracuseStep 1214759 = 1822139) B1822139
theorem B1198415 : Blo 1196415 1198415 := bstep (se 1 (by rfl) ⟨898811, by rfl⟩ : syracuseStep 1198415 = 1797623) B1797623
theorem B1796447 : Blo 1196415 1796447 := bstep (se 1 (by rfl) ⟨1347335, by rfl⟩ : syracuseStep 1796447 = 2694671) B2694671
theorem B1796459 : Blo 1196415 1796459 := bstep (se 1 (by rfl) ⟨1347344, by rfl⟩ : syracuseStep 1796459 = 2694689) B2694689
theorem B4041089 : Blo 1196415 4041089 := bstep (se 2 (by rfl) ⟨1515408, by rfl⟩ : syracuseStep 4041089 = 3030817) B3030817
theorem B1796687 : Blo 1196415 1796687 := bstep (se 1 (by rfl) ⟨1347515, by rfl⟩ : syracuseStep 1796687 = 2695031) B2695031
theorem B1796807 : Blo 1196415 1796807 := bstep (se 1 (by rfl) ⟨1347605, by rfl⟩ : syracuseStep 1796807 = 2695211) B2695211
theorem B20474693 : Blo 1196415 20474693 := bstep (se 4 (by rfl) ⟨1919502, by rfl⟩ : syracuseStep 20474693 = 3839005) B3839005
theorem B3238751 : Blo 1196415 3238751 := bstep (se 1 (by rfl) ⟨2429063, by rfl⟩ : syracuseStep 3238751 = 4858127) B4858127
theorem B1796969 : Blo 1196415 1796969 := bstep (se 2 (by rfl) ⟨673863, by rfl⟩ : syracuseStep 1796969 = 1347727) B1347727
theorem B2304929 : Blo 1196415 2304929 := bstep (se 2 (by rfl) ⟨864348, by rfl⟩ : syracuseStep 2304929 = 1728697) B1728697
theorem B1797047 : Blo 1196415 1797047 := bstep (se 1 (by rfl) ⟨1347785, by rfl⟩ : syracuseStep 1797047 = 2695571) B2695571
theorem B2272187 : Blo 1196415 2272187 := bstep (se 1 (by rfl) ⟨1704140, by rfl⟩ : syracuseStep 2272187 = 3408281) B3408281
theorem B1797083 : Blo 1196415 1797083 := bstep (se 1 (by rfl) ⟨1347812, by rfl⟩ : syracuseStep 1797083 = 2695625) B2695625
theorem B9219091 : Blo 1196415 9219091 := bstep (se 1 (by rfl) ⟨6914318, by rfl⟩ : syracuseStep 9219091 = 13828637) B13828637
theorem B1346683 : Blo 1196415 1346683 := bstep (se 1 (by rfl) ⟨1010012, by rfl⟩ : syracuseStep 1346683 = 2020025) B2020025
theorem B4041899 : Blo 1196415 4041899 := bstep (se 1 (by rfl) ⟨3031424, by rfl⟩ : syracuseStep 4041899 = 6062849) B6062849
theorem B1821895 : Blo 1196415 1821895 := bstep (se 1 (by rfl) ⟨1366421, by rfl⟩ : syracuseStep 1821895 = 2732843) B2732843
theorem B87633211 : Blo 1196415 87633211 := bstep (se 1 (by rfl) ⟨65724908, by rfl⟩ : syracuseStep 87633211 = 131449817) B131449817
theorem B3837289 : Blo 1196415 3837289 := bstep (se 2 (by rfl) ⟨1438983, by rfl⟩ : syracuseStep 3837289 = 2877967) B2877967
theorem B6057341 : Blo 1196415 6057341 := bstep (se 3 (by rfl) ⟨1135751, by rfl⟩ : syracuseStep 6057341 = 2271503) B2271503
theorem B2272673 : Blo 1196415 2272673 := bstep (se 2 (by rfl) ⟨852252, by rfl⟩ : syracuseStep 2272673 = 1704505) B1704505
theorem B1797551 : Blo 1196415 1797551 := bstep (se 1 (by rfl) ⟨1348163, by rfl⟩ : syracuseStep 1797551 = 2696327) B2696327
theorem B2731529 : Blo 1196415 2731529 := bstep (se 2 (by rfl) ⟨1024323, by rfl⟩ : syracuseStep 2731529 = 2048647) B2048647
theorem B1347151 : Blo 1196415 1347151 := bstep (se 1 (by rfl) ⟨1010363, by rfl⟩ : syracuseStep 1347151 = 2020727) B2020727
theorem B7376507 : Blo 1196415 7376507 := bstep (se 1 (by rfl) ⟨5532380, by rfl⟩ : syracuseStep 7376507 = 11064761) B11064761
theorem B10374779 : Blo 1196415 10374779 := bstep (se 1 (by rfl) ⟨7781084, by rfl⟩ : syracuseStep 10374779 = 15562169) B15562169
theorem B4042439 : Blo 1196415 4042439 := bstep (se 1 (by rfl) ⟨3031829, by rfl⟩ : syracuseStep 4042439 = 6063659) B6063659
theorem B2273015 : Blo 1196415 2273015 := bstep (se 1 (by rfl) ⟨1704761, by rfl⟩ : syracuseStep 2273015 = 3409523) B3409523
theorem B3837725 : Blo 1196415 3837725 := bstep (se 3 (by rfl) ⟨719573, by rfl⟩ : syracuseStep 3837725 = 1439147) B1439147
theorem B2019215 : Blo 1196415 2019215 := bstep (se 1 (by rfl) ⟨1514411, by rfl⟩ : syracuseStep 2019215 = 3028823) B3028823
theorem B5754817 : Blo 1196415 5754817 := bstep (se 2 (by rfl) ⟨2158056, by rfl⟩ : syracuseStep 5754817 = 4316113) B4316113
theorem B1347547 : Blo 1196415 1347547 := bstep (se 1 (by rfl) ⟨1010660, by rfl⟩ : syracuseStep 1347547 = 2021321) B2021321
theorem B2019451 : Blo 1196415 2019451 := bstep (se 1 (by rfl) ⟨1514588, by rfl⟩ : syracuseStep 2019451 = 3029177) B3029177
theorem B5116061 : Blo 1196415 5116061 := bstep (se 3 (by rfl) ⟨959261, by rfl⟩ : syracuseStep 5116061 = 1918523) B1918523
theorem B5828969 : Blo 1196415 5828969 := bstep (se 2 (by rfl) ⟨2185863, by rfl⟩ : syracuseStep 5828969 = 4371727) B4371727
theorem B1348015 : Blo 1196415 1348015 := bstep (se 1 (by rfl) ⟨1011011, by rfl⟩ : syracuseStep 1348015 = 2022023) B2022023
theorem B2159111 : Blo 1196415 2159111 := bstep (se 1 (by rfl) ⟨1619333, by rfl⟩ : syracuseStep 2159111 = 3238667) B3238667
theorem B7778825 : Blo 1196415 7778825 := bstep (se 2 (by rfl) ⟨2917059, by rfl⟩ : syracuseStep 7778825 = 5834119) B5834119
theorem B4043303 : Blo 1196415 4043303 := bstep (se 1 (by rfl) ⟨3032477, by rfl⟩ : syracuseStep 4043303 = 6064955) B6064955
theorem B4043411 : Blo 1196415 4043411 := bstep (se 1 (by rfl) ⟨3032558, by rfl⟩ : syracuseStep 4043411 = 6065117) B6065117
theorem B4149949 : Blo 1196415 4149949 := bstep (se 3 (by rfl) ⟨778115, by rfl⟩ : syracuseStep 4149949 = 1556231) B1556231
theorem B6066899 : Blo 1196415 6066899 := bstep (se 1 (by rfl) ⟨4550174, by rfl⟩ : syracuseStep 6066899 = 9100349) B9100349
theorem B3691337 : Blo 1196415 3691337 := bstep (se 2 (by rfl) ⟨1384251, by rfl⟩ : syracuseStep 3691337 = 2768503) B2768503
theorem B2691935 : Blo 1196415 2691935 := bstep (se 1 (by rfl) ⟨2018951, by rfl⟩ : syracuseStep 2691935 = 4037903) B4037903
theorem B4043627 : Blo 1196415 4043627 := bstep (se 1 (by rfl) ⟨3032720, by rfl⟩ : syracuseStep 4043627 = 6065441) B6065441
theorem B7771025 : Blo 1196415 7771025 := bstep (se 2 (by rfl) ⟨2914134, by rfl⟩ : syracuseStep 7771025 = 5828269) B5828269
theorem B4043681 : Blo 1196415 4043681 := bstep (se 2 (by rfl) ⟨1516380, by rfl⟩ : syracuseStep 4043681 = 3032761) B3032761
theorem B3888059 : Blo 1196415 3888059 := bstep (se 1 (by rfl) ⟨2916044, by rfl⟩ : syracuseStep 3888059 = 5832089) B5832089
theorem B2020315 : Blo 1196415 2020315 := bstep (se 1 (by rfl) ⟨1515236, by rfl⟩ : syracuseStep 2020315 = 3030473) B3030473
theorem B2274313 : Blo 1196415 2274313 := bstep (se 2 (by rfl) ⟨852867, by rfl⟩ : syracuseStep 2274313 = 1705735) B1705735
theorem B2692115 : Blo 1196415 2692115 := bstep (se 1 (by rfl) ⟨2019086, by rfl⟩ : syracuseStep 2692115 = 4038173) B4038173
theorem B13636673 : Blo 1196415 13636673 := bstep (se 2 (by rfl) ⟨5113752, by rfl⟩ : syracuseStep 13636673 = 10227505) B10227505
theorem B4543735 : Blo 1196415 4543735 := bstep (se 1 (by rfl) ⟨3407801, by rfl⟩ : syracuseStep 4543735 = 6815603) B6815603
theorem B2274655 : Blo 1196415 2274655 := bstep (se 1 (by rfl) ⟨1705991, by rfl⟩ : syracuseStep 2274655 = 3411983) B3411983
theorem B2692457 : Blo 1196415 2692457 := bstep (se 2 (by rfl) ⟨1009671, by rfl⟩ : syracuseStep 2692457 = 2019343) B2019343
theorem B4044275 : Blo 1196415 4044275 := bstep (se 1 (by rfl) ⟨3033206, by rfl⟩ : syracuseStep 4044275 = 6066413) B6066413
theorem B4544009 : Blo 1196415 4544009 := bstep (se 2 (by rfl) ⟨1704003, by rfl⟩ : syracuseStep 4544009 = 3408007) B3408007
theorem B3642889 : Blo 1196415 3642889 := bstep (se 2 (by rfl) ⟨1366083, by rfl⟩ : syracuseStep 3642889 = 2732167) B2732167
theorem B4544039 : Blo 1196415 4544039 := bstep (se 1 (by rfl) ⟨3408029, by rfl⟩ : syracuseStep 4544039 = 6816059) B6816059
theorem B5461543 : Blo 1196415 5461543 := bstep (se 1 (by rfl) ⟨4096157, by rfl⟩ : syracuseStep 5461543 = 8192315) B8192315
theorem B2020943 : Blo 1196415 2020943 := bstep (se 1 (by rfl) ⟨1515707, by rfl⟩ : syracuseStep 2020943 = 3031415) B3031415
theorem B3888737 : Blo 1196415 3888737 := bstep (se 2 (by rfl) ⟨1458276, by rfl⟩ : syracuseStep 3888737 = 2916553) B2916553
theorem B9098891 : Blo 1196415 9098891 := bstep (se 1 (by rfl) ⟨6824168, by rfl⟩ : syracuseStep 9098891 = 13648337) B13648337
theorem B39909005 : Blo 1196415 39909005 := bstep (se 3 (by rfl) ⟨7482938, by rfl⟩ : syracuseStep 39909005 = 14965877) B14965877
theorem B73791157 : Blo 1196415 73791157 := bstep (se 5 (by rfl) ⟨3458960, by rfl⟩ : syracuseStep 73791157 = 6917921) B6917921
theorem B7280327 : Blo 1196415 7280327 := bstep (se 1 (by rfl) ⟨5460245, by rfl⟩ : syracuseStep 7280327 = 10920491) B10920491
theorem B4314833 : Blo 1196415 4314833 := bstep (se 2 (by rfl) ⟨1618062, by rfl⟩ : syracuseStep 4314833 = 3236125) B3236125
theorem B3028691 : Blo 1196415 3028691 := bstep (se 1 (by rfl) ⟨2271518, by rfl⟩ : syracuseStep 3028691 = 4543037) B4543037
theorem B2693051 : Blo 1196415 2693051 := bstep (se 1 (by rfl) ⟨2019788, by rfl⟩ : syracuseStep 2693051 = 4039577) B4039577
theorem B2693177 : Blo 1196415 2693177 := bstep (se 2 (by rfl) ⟨1009941, by rfl⟩ : syracuseStep 2693177 = 2019883) B2019883
theorem B15341669 : Blo 1196415 15341669 := bstep (se 4 (by rfl) ⟨1438281, by rfl⟩ : syracuseStep 15341669 = 2876563) B2876563
theorem B4544707 : Blo 1196415 4544707 := bstep (se 1 (by rfl) ⟨3408530, by rfl⟩ : syracuseStep 4544707 = 6817061) B6817061
theorem B2693519 : Blo 1196415 2693519 := bstep (se 1 (by rfl) ⟨2020139, by rfl⟩ : syracuseStep 2693519 = 4040279) B4040279
theorem B2021807 : Blo 1196415 2021807 := bstep (se 1 (by rfl) ⟨1516355, by rfl⟩ : syracuseStep 2021807 = 3032711) B3032711
theorem B4545011 : Blo 1196415 4545011 := bstep (se 1 (by rfl) ⟨3408758, by rfl⟩ : syracuseStep 4545011 = 6817517) B6817517
theorem B2693843 : Blo 1196415 2693843 := bstep (se 1 (by rfl) ⟨2020382, by rfl⟩ : syracuseStep 2693843 = 4040765) B4040765
theorem B4315999 : Blo 1196415 4315999 := bstep (se 1 (by rfl) ⟨3236999, by rfl⟩ : syracuseStep 4315999 = 6473999) B6473999
theorem B2022239 : Blo 1196415 2022239 := bstep (se 1 (by rfl) ⟨1516679, by rfl⟩ : syracuseStep 2022239 = 3033359) B3033359
theorem B4545467 : Blo 1196415 4545467 := bstep (se 1 (by rfl) ⟨3409100, by rfl⟩ : syracuseStep 4545467 = 6818201) B6818201
theorem B31112365 : Blo 1196415 31112365 := bstep (se 3 (by rfl) ⟨5833568, by rfl⟩ : syracuseStep 31112365 = 11667137) B11667137
theorem B1514695 : Blo 1196415 1514695 := bstep (se 1 (by rfl) ⟨1136021, by rfl⟩ : syracuseStep 1514695 = 2272043) B2272043
theorem B21855511 : Blo 1196415 21855511 := bstep (se 1 (by rfl) ⟨16391633, by rfl⟩ : syracuseStep 21855511 = 32783267) B32783267
theorem B1916473 : Blo 1196415 1916473 := bstep (se 2 (by rfl) ⟨718677, by rfl⟩ : syracuseStep 1916473 = 1437355) B1437355
theorem B3407483 : Blo 1196415 3407483 := bstep (se 1 (by rfl) ⟨2555612, by rfl⟩ : syracuseStep 3407483 = 5111225) B5111225
theorem B2694779 : Blo 1196415 2694779 := bstep (se 1 (by rfl) ⟨2021084, by rfl⟩ : syracuseStep 2694779 = 4042169) B4042169
theorem B19414667 : Blo 1196415 19414667 := bstep (se 1 (by rfl) ⟨14561000, by rfl⟩ : syracuseStep 19414667 = 29122001) B29122001
theorem B6061715 : Blo 1196415 6061715 := bstep (se 1 (by rfl) ⟨4546286, by rfl⟩ : syracuseStep 6061715 = 9092573) B9092573
theorem B8634071 : Blo 1196415 8634071 := bstep (se 1 (by rfl) ⟨6475553, by rfl⟩ : syracuseStep 8634071 = 12951107) B12951107
theorem B3407609 : Blo 1196415 3407609 := bstep (se 2 (by rfl) ⟨1277853, by rfl⟩ : syracuseStep 3407609 = 2555707) B2555707
theorem B2694905 : Blo 1196415 2694905 := bstep (se 2 (by rfl) ⟨1010589, by rfl⟩ : syracuseStep 2694905 = 2021179) B2021179
theorem B4038443 : Blo 1196415 4038443 := bstep (se 1 (by rfl) ⟨3028832, by rfl⟩ : syracuseStep 4038443 = 6057665) B6057665
theorem B3407791 : Blo 1196415 3407791 := bstep (se 1 (by rfl) ⟨2555843, by rfl⟩ : syracuseStep 3407791 = 5111687) B5111687
theorem B1515439 : Blo 1196415 1515439 := bstep (se 1 (by rfl) ⟨1136579, by rfl⟩ : syracuseStep 1515439 = 2273159) B2273159
theorem B3030959 : Blo 1196415 3030959 := bstep (se 1 (by rfl) ⟨2273219, by rfl⟩ : syracuseStep 3030959 = 4546439) B4546439
theorem B12451843 : Blo 1196415 12451843 := bstep (se 1 (by rfl) ⟨9338882, by rfl⟩ : syracuseStep 12451843 = 18677765) B18677765
theorem B42647651 : Blo 1196415 42647651 := bstep (se 1 (by rfl) ⟨31985738, by rfl⟩ : syracuseStep 42647651 = 63971477) B63971477
theorem B5185883 : Blo 1196415 5185883 := bstep (se 1 (by rfl) ⟨3889412, by rfl⟩ : syracuseStep 5185883 = 7778825) B7778825
theorem B2695535 : Blo 1196415 2695535 := bstep (se 1 (by rfl) ⟨2021651, by rfl⟩ : syracuseStep 2695535 = 4043303) B4043303
theorem B1196455 : Blo 1196415 1196455 := bstep (se 1 (by rfl) ⟨897341, by rfl⟩ : syracuseStep 1196455 = 1794683) B1794683
theorem B2695607 : Blo 1196415 2695607 := bstep (se 1 (by rfl) ⟨2021705, by rfl⟩ : syracuseStep 2695607 = 4043411) B4043411
theorem B1196539 : Blo 1196415 1196539 := bstep (se 1 (by rfl) ⟨897404, by rfl⟩ : syracuseStep 1196539 = 1794809) B1794809
theorem B1794623 : Blo 1196415 1794623 := bstep (se 1 (by rfl) ⟨1345967, by rfl⟩ : syracuseStep 1794623 = 2691935) B2691935
theorem B1196607 : Blo 1196415 1196607 := bstep (se 1 (by rfl) ⟨897455, by rfl⟩ : syracuseStep 1196607 = 1794911) B1794911
theorem B1196615 : Blo 1196415 1196615 := bstep (se 1 (by rfl) ⟨897461, by rfl⟩ : syracuseStep 1196615 = 1794923) B1794923
theorem B2695751 : Blo 1196415 2695751 := bstep (se 1 (by rfl) ⟨2021813, by rfl⟩ : syracuseStep 2695751 = 4043627) B4043627
theorem B2695787 : Blo 1196415 2695787 := bstep (se 1 (by rfl) ⟨2021840, by rfl⟩ : syracuseStep 2695787 = 4043681) B4043681
theorem B1794743 : Blo 1196415 1794743 := bstep (se 1 (by rfl) ⟨1346057, by rfl⟩ : syracuseStep 1794743 = 2692115) B2692115
theorem B1196767 : Blo 1196415 1196767 := bstep (se 1 (by rfl) ⟨897575, by rfl⟩ : syracuseStep 1196767 = 1795151) B1795151
theorem B1196847 : Blo 1196415 1196847 := bstep (se 1 (by rfl) ⟨897635, by rfl⟩ : syracuseStep 1196847 = 1795271) B1795271
theorem B15336337 : Blo 1196415 15336337 := bstep (se 2 (by rfl) ⟨5751126, by rfl⟩ : syracuseStep 15336337 = 11502253) B11502253
theorem B3031951 : Blo 1196415 3031951 := bstep (se 1 (by rfl) ⟨2273963, by rfl⟩ : syracuseStep 3031951 = 4547927) B4547927
theorem B1794971 : Blo 1196415 1794971 := bstep (se 1 (by rfl) ⟨1346228, by rfl⟩ : syracuseStep 1794971 = 2692457) B2692457
theorem B1196955 : Blo 1196415 1196955 := bstep (se 1 (by rfl) ⟨897716, by rfl⟩ : syracuseStep 1196955 = 1795433) B1795433
theorem B1197007 : Blo 1196415 1197007 := bstep (se 1 (by rfl) ⟨897755, by rfl⟩ : syracuseStep 1197007 = 1795511) B1795511
theorem B6816743 : Blo 1196415 6816743 := bstep (se 1 (by rfl) ⟨5112557, by rfl⟩ : syracuseStep 6816743 = 10225115) B10225115
theorem B1197031 : Blo 1196415 1197031 := bstep (se 1 (by rfl) ⟨897773, by rfl⟩ : syracuseStep 1197031 = 1795547) B1795547
theorem B2696183 : Blo 1196415 2696183 := bstep (se 1 (by rfl) ⟨2022137, by rfl⟩ : syracuseStep 2696183 = 4044275) B4044275
theorem B9716773 : Blo 1196415 9716773 := bstep (se 4 (by rfl) ⟨910947, by rfl⟩ : syracuseStep 9716773 = 1821895) B1821895
theorem B2876555 : Blo 1196415 2876555 := bstep (se 1 (by rfl) ⟨2157416, by rfl⟩ : syracuseStep 2876555 = 4314833) B4314833
theorem B1197343 : Blo 1196415 1197343 := bstep (se 1 (by rfl) ⟨898007, by rfl⟩ : syracuseStep 1197343 = 1796015) B1796015
theorem B1795367 : Blo 1196415 1795367 := bstep (se 1 (by rfl) ⟨1346525, by rfl⟩ : syracuseStep 1795367 = 2693051) B2693051
theorem B1918247 : Blo 1196415 1918247 := bstep (se 1 (by rfl) ⟨1438685, by rfl⟩ : syracuseStep 1918247 = 2877371) B2877371
theorem B1197403 : Blo 1196415 1197403 := bstep (se 1 (by rfl) ⟨898052, by rfl⟩ : syracuseStep 1197403 = 1796105) B1796105
theorem B3032417 : Blo 1196415 3032417 := bstep (se 2 (by rfl) ⟨1137156, by rfl⟩ : syracuseStep 3032417 = 2274313) B2274313
theorem B7284077 : Blo 1196415 7284077 := bstep (se 3 (by rfl) ⟨1365764, by rfl⟩ : syracuseStep 7284077 = 2731529) B2731529
theorem B1197423 : Blo 1196415 1197423 := bstep (se 1 (by rfl) ⟨898067, by rfl⟩ : syracuseStep 1197423 = 1796135) B1796135
theorem B1795451 : Blo 1196415 1795451 := bstep (se 1 (by rfl) ⟨1346588, by rfl⟩ : syracuseStep 1795451 = 2693177) B2693177
theorem B1197479 : Blo 1196415 1197479 := bstep (se 1 (by rfl) ⟨898109, by rfl⟩ : syracuseStep 1197479 = 1796219) B1796219
theorem B1795577 : Blo 1196415 1795577 := bstep (se 2 (by rfl) ⟨673341, by rfl⟩ : syracuseStep 1795577 = 1346683) B1346683
theorem B1197563 : Blo 1196415 1197563 := bstep (se 1 (by rfl) ⟨898172, by rfl⟩ : syracuseStep 1197563 = 1796345) B1796345
theorem B3409465 : Blo 1196415 3409465 := bstep (se 2 (by rfl) ⟨1278549, by rfl⟩ : syracuseStep 3409465 = 2557099) B2557099
theorem B1197631 : Blo 1196415 1197631 := bstep (se 1 (by rfl) ⟨898223, by rfl⟩ : syracuseStep 1197631 = 1796447) B1796447
theorem B1197639 : Blo 1196415 1197639 := bstep (se 1 (by rfl) ⟨898229, by rfl⟩ : syracuseStep 1197639 = 1796459) B1796459
theorem B1795679 : Blo 1196415 1795679 := bstep (se 1 (by rfl) ⟨1346759, by rfl⟩ : syracuseStep 1795679 = 2693519) B2693519
theorem B1197791 : Blo 1196415 1197791 := bstep (se 1 (by rfl) ⟨898343, by rfl⟩ : syracuseStep 1197791 = 1796687) B1796687
theorem B116844281 : Blo 1196415 116844281 := bstep (se 2 (by rfl) ⟨43816605, by rfl⟩ : syracuseStep 116844281 = 87633211) B87633211
theorem B3032873 : Blo 1196415 3032873 := bstep (se 2 (by rfl) ⟨1137327, by rfl⟩ : syracuseStep 3032873 = 2274655) B2274655
theorem B1197871 : Blo 1196415 1197871 := bstep (se 1 (by rfl) ⟨898403, by rfl⟩ : syracuseStep 1197871 = 1796807) B1796807
theorem B1795895 : Blo 1196415 1795895 := bstep (se 1 (by rfl) ⟨1346921, by rfl⟩ : syracuseStep 1795895 = 2693843) B2693843
theorem B13649795 : Blo 1196415 13649795 := bstep (se 1 (by rfl) ⟨10237346, by rfl⟩ : syracuseStep 13649795 = 20474693) B20474693
theorem B1197979 : Blo 1196415 1197979 := bstep (se 1 (by rfl) ⟨898484, by rfl⟩ : syracuseStep 1197979 = 1796969) B1796969
theorem B1198031 : Blo 1196415 1198031 := bstep (se 1 (by rfl) ⟨898523, by rfl⟩ : syracuseStep 1198031 = 1797047) B1797047
theorem B1198055 : Blo 1196415 1198055 := bstep (se 1 (by rfl) ⟨898541, by rfl⟩ : syracuseStep 1198055 = 1797083) B1797083
theorem B1796201 : Blo 1196415 1796201 := bstep (se 2 (by rfl) ⟨673575, by rfl⟩ : syracuseStep 1796201 = 1347151) B1347151
theorem B98388209 : Blo 1196415 98388209 := bstep (se 2 (by rfl) ⟨36895578, by rfl⟩ : syracuseStep 98388209 = 73791157) B73791157
theorem B8636669 : Blo 1196415 8636669 := bstep (se 3 (by rfl) ⟨1619375, by rfl⟩ : syracuseStep 8636669 = 3238751) B3238751
theorem B5835037 : Blo 1196415 5835037 := bstep (se 3 (by rfl) ⟨1094069, by rfl⟩ : syracuseStep 5835037 = 2188139) B2188139
theorem B1198367 : Blo 1196415 1198367 := bstep (se 1 (by rfl) ⟨898775, by rfl⟩ : syracuseStep 1198367 = 1797551) B1797551
theorem B4917671 : Blo 1196415 4917671 := bstep (se 1 (by rfl) ⟨3688253, by rfl⟩ : syracuseStep 4917671 = 7376507) B7376507
theorem B2271655 : Blo 1196415 2271655 := bstep (se 1 (by rfl) ⟨1703741, by rfl⟩ : syracuseStep 2271655 = 3407483) B3407483
theorem B1796519 : Blo 1196415 1796519 := bstep (se 1 (by rfl) ⟨1347389, by rfl⟩ : syracuseStep 1796519 = 2694779) B2694779
theorem B6916519 : Blo 1196415 6916519 := bstep (se 1 (by rfl) ⟨5187389, by rfl⟩ : syracuseStep 6916519 = 10374779) B10374779
theorem B4041143 : Blo 1196415 4041143 := bstep (se 1 (by rfl) ⟨3030857, by rfl⟩ : syracuseStep 4041143 = 6061715) B6061715
theorem B2271739 : Blo 1196415 2271739 := bstep (se 1 (by rfl) ⟨1703804, by rfl⟩ : syracuseStep 2271739 = 3407609) B3407609
theorem B1796603 : Blo 1196415 1796603 := bstep (se 1 (by rfl) ⟨1347452, by rfl⟩ : syracuseStep 1796603 = 2694905) B2694905
theorem B2558483 : Blo 1196415 2558483 := bstep (se 1 (by rfl) ⟨1918862, by rfl⟩ : syracuseStep 2558483 = 3837725) B3837725
theorem B1346143 : Blo 1196415 1346143 := bstep (se 1 (by rfl) ⟨1009607, by rfl⟩ : syracuseStep 1346143 = 2019215) B2019215
theorem B1796729 : Blo 1196415 1796729 := bstep (se 2 (by rfl) ⟨673773, by rfl⟩ : syracuseStep 1796729 = 1347547) B1347547
theorem B2558585 : Blo 1196415 2558585 := bstep (se 2 (by rfl) ⟨959469, by rfl⟩ : syracuseStep 2558585 = 1918939) B1918939
theorem B1796783 : Blo 1196415 1796783 := bstep (se 1 (by rfl) ⟨1347587, by rfl⟩ : syracuseStep 1796783 = 2695175) B2695175
theorem B1796831 : Blo 1196415 1796831 := bstep (se 1 (by rfl) ⟨1347623, by rfl⟩ : syracuseStep 1796831 = 2695247) B2695247
theorem B2878199 : Blo 1196415 2878199 := bstep (se 1 (by rfl) ⟨2158649, by rfl⟩ : syracuseStep 2878199 = 4317299) B4317299
theorem B3410707 : Blo 1196415 3410707 := bstep (se 1 (by rfl) ⟨2558030, by rfl⟩ : syracuseStep 3410707 = 5116061) B5116061
theorem B3885979 : Blo 1196415 3885979 := bstep (se 1 (by rfl) ⟨2914484, by rfl⟩ : syracuseStep 3885979 = 5828969) B5828969
theorem B31124405 : Blo 1196415 31124405 := bstep (se 5 (by rfl) ⟨1458956, by rfl⟩ : syracuseStep 31124405 = 2917913) B2917913
theorem B1797095 : Blo 1196415 1797095 := bstep (se 1 (by rfl) ⟨1347821, by rfl⟩ : syracuseStep 1797095 = 2695643) B2695643
theorem B7777361 : Blo 1196415 7777361 := bstep (se 2 (by rfl) ⟨2916510, by rfl⟩ : syracuseStep 7777361 = 5833021) B5833021
theorem B6057179 : Blo 1196415 6057179 := bstep (se 1 (by rfl) ⟨4542884, by rfl⟩ : syracuseStep 6057179 = 9085769) B9085769
theorem B2272475 : Blo 1196415 2272475 := bstep (se 1 (by rfl) ⟨1704356, by rfl⟩ : syracuseStep 2272475 = 3408713) B3408713
theorem B1797353 : Blo 1196415 1797353 := bstep (se 2 (by rfl) ⟨674007, by rfl⟩ : syracuseStep 1797353 = 1348015) B1348015
theorem B5180683 : Blo 1196415 5180683 := bstep (se 1 (by rfl) ⟨3885512, by rfl⟩ : syracuseStep 5180683 = 7771025) B7771025
theorem B1797407 : Blo 1196415 1797407 := bstep (se 1 (by rfl) ⟨1348055, by rfl⟩ : syracuseStep 1797407 = 2696111) B2696111
theorem B3239357 : Blo 1196415 3239357 := bstep (se 3 (by rfl) ⟨607379, by rfl⟩ : syracuseStep 3239357 = 1214759) B1214759
theorem B2272711 : Blo 1196415 2272711 := bstep (se 1 (by rfl) ⟨1704533, by rfl⟩ : syracuseStep 2272711 = 3409067) B3409067
theorem B1797575 : Blo 1196415 1797575 := bstep (se 1 (by rfl) ⟨1348181, by rfl⟩ : syracuseStep 1797575 = 2696363) B2696363
theorem B5533265 : Blo 1196415 5533265 := bstep (se 2 (by rfl) ⟨2074974, by rfl⟩ : syracuseStep 5533265 = 4149949) B4149949
theorem B5254739 : Blo 1196415 5254739 := bstep (se 1 (by rfl) ⟨3941054, by rfl⟩ : syracuseStep 5254739 = 7882109) B7882109
theorem B9088685 : Blo 1196415 9088685 := bstep (se 3 (by rfl) ⟨1704128, by rfl⟩ : syracuseStep 9088685 = 3408257) B3408257
theorem B1437359 : Blo 1196415 1437359 := bstep (se 1 (by rfl) ⟨1078019, by rfl⟩ : syracuseStep 1437359 = 2156039) B2156039
theorem B1347295 : Blo 1196415 1347295 := bstep (se 1 (by rfl) ⟨1010471, by rfl⟩ : syracuseStep 1347295 = 2020943) B2020943
theorem B2592491 : Blo 1196415 2592491 := bstep (se 1 (by rfl) ⟨1944368, by rfl⟩ : syracuseStep 2592491 = 3888737) B3888737
theorem B6065927 : Blo 1196415 6065927 := bstep (se 1 (by rfl) ⟨4549445, by rfl⟩ : syracuseStep 6065927 = 9098891) B9098891
theorem B5754665 : Blo 1196415 5754665 := bstep (se 2 (by rfl) ⟨2157999, by rfl⟩ : syracuseStep 5754665 = 4315999) B4315999
theorem B2019127 : Blo 1196415 2019127 := bstep (se 1 (by rfl) ⟨1514345, by rfl⟩ : syracuseStep 2019127 = 3028691) B3028691
theorem B10923997 : Blo 1196415 10923997 := bstep (se 3 (by rfl) ⟨2048249, by rfl⟩ : syracuseStep 10923997 = 4096499) B4096499
theorem B16396289 : Blo 1196415 16396289 := bstep (se 2 (by rfl) ⟨6148608, by rfl⟩ : syracuseStep 16396289 = 12297217) B12297217
theorem B12292121 : Blo 1196415 12292121 := bstep (se 2 (by rfl) ⟨4609545, by rfl⟩ : syracuseStep 12292121 = 9219091) B9219091
theorem B10227779 : Blo 1196415 10227779 := bstep (se 1 (by rfl) ⟨7670834, by rfl⟩ : syracuseStep 10227779 = 15341669) B15341669
theorem B2019593 : Blo 1196415 2019593 := bstep (se 2 (by rfl) ⟨757347, by rfl⟩ : syracuseStep 2019593 = 1514695) B1514695
theorem B1347871 : Blo 1196415 1347871 := bstep (se 1 (by rfl) ⟨1010903, by rfl⟩ : syracuseStep 1347871 = 2021807) B2021807
theorem B6058313 : Blo 1196415 6058313 := bstep (se 2 (by rfl) ⟨2271867, by rfl⟩ : syracuseStep 6058313 = 4543735) B4543735
theorem B5116385 : Blo 1196415 5116385 := bstep (se 2 (by rfl) ⟨1918644, by rfl⟩ : syracuseStep 5116385 = 3837289) B3837289
theorem B23024189 : Blo 1196415 23024189 := bstep (se 3 (by rfl) ⟨4317035, by rfl⟩ : syracuseStep 23024189 = 8634071) B8634071
theorem B1348159 : Blo 1196415 1348159 := bstep (se 1 (by rfl) ⟨1011119, by rfl⟩ : syracuseStep 1348159 = 2022239) B2022239
theorem B1536619 : Blo 1196415 1536619 := bstep (se 1 (by rfl) ⟨1152464, by rfl⟩ : syracuseStep 1536619 = 2304929) B2304929
theorem B9089657 : Blo 1196415 9089657 := bstep (se 2 (by rfl) ⟨3408621, by rfl⟩ : syracuseStep 9089657 = 6817243) B6817243
theorem B9843565 : Blo 1196415 9843565 := bstep (se 3 (by rfl) ⟨1845668, by rfl⟩ : syracuseStep 9843565 = 3691337) B3691337
theorem B30692357 : Blo 1196415 30692357 := bstep (se 4 (by rfl) ⟨2877408, by rfl⟩ : syracuseStep 30692357 = 5754817) B5754817
theorem B10368157 : Blo 1196415 10368157 := bstep (se 3 (by rfl) ⟨1944029, by rfl⟩ : syracuseStep 10368157 = 3888059) B3888059
theorem B2692295 : Blo 1196415 2692295 := bstep (se 1 (by rfl) ⟨2019221, by rfl⟩ : syracuseStep 2692295 = 4038443) B4038443
theorem B4543721 : Blo 1196415 4543721 := bstep (se 2 (by rfl) ⟨1703895, by rfl⟩ : syracuseStep 4543721 = 3407791) B3407791
theorem B2020585 : Blo 1196415 2020585 := bstep (se 2 (by rfl) ⟨757719, by rfl⟩ : syracuseStep 2020585 = 1515439) B1515439
theorem B2020639 : Blo 1196415 2020639 := bstep (se 1 (by rfl) ⟨1515479, by rfl⟩ : syracuseStep 2020639 = 3030959) B3030959
theorem B2692475 : Blo 1196415 2692475 := bstep (se 1 (by rfl) ⟨2019356, by rfl⟩ : syracuseStep 2692475 = 4038713) B4038713
theorem B4044221 : Blo 1196415 4044221 := bstep (se 3 (by rfl) ⟨758291, by rfl⟩ : syracuseStep 4044221 = 1516583) B1516583
theorem B2692601 : Blo 1196415 2692601 := bstep (se 2 (by rfl) ⟨1009725, by rfl⟩ : syracuseStep 2692601 = 2019451) B2019451
theorem B11818541 : Blo 1196415 11818541 := bstep (se 3 (by rfl) ⟨2215976, by rfl⟩ : syracuseStep 11818541 = 4431953) B4431953
theorem B2692691 : Blo 1196415 2692691 := bstep (se 1 (by rfl) ⟨2019518, by rfl⟩ : syracuseStep 2692691 = 4039037) B4039037
theorem B6059609 : Blo 1196415 6059609 := bstep (se 2 (by rfl) ⟨2272353, by rfl⟩ : syracuseStep 6059609 = 4544707) B4544707
theorem B1439407 : Blo 1196415 1439407 := bstep (se 1 (by rfl) ⟨1079555, by rfl⟩ : syracuseStep 1439407 = 2159111) B2159111
theorem B2021051 : Blo 1196415 2021051 := bstep (se 1 (by rfl) ⟨1515788, by rfl⟩ : syracuseStep 2021051 = 3031577) B3031577
theorem B2692871 : Blo 1196415 2692871 := bstep (se 1 (by rfl) ⟨2019653, by rfl⟩ : syracuseStep 2692871 = 4039307) B4039307
theorem B4044599 : Blo 1196415 4044599 := bstep (se 1 (by rfl) ⟨3033449, by rfl⟩ : syracuseStep 4044599 = 6066899) B6066899
theorem B9091115 : Blo 1196415 9091115 := bstep (se 1 (by rfl) ⟨6818336, by rfl⟩ : syracuseStep 9091115 = 13636673) B13636673
theorem B1366303 : Blo 1196415 1366303 := bstep (se 1 (by rfl) ⟨1024727, by rfl⟩ : syracuseStep 1366303 = 2049455) B2049455
theorem B3029339 : Blo 1196415 3029339 := bstep (se 1 (by rfl) ⟨2272004, by rfl⟩ : syracuseStep 3029339 = 4544009) B4544009
theorem B2693483 : Blo 1196415 2693483 := bstep (se 1 (by rfl) ⟨2020112, by rfl⟩ : syracuseStep 2693483 = 4040225) B4040225
theorem B3029359 : Blo 1196415 3029359 := bstep (se 1 (by rfl) ⟨2272019, by rfl⟩ : syracuseStep 3029359 = 4544039) B4544039
theorem B26606003 : Blo 1196415 26606003 := bstep (se 1 (by rfl) ⟨19954502, by rfl⟩ : syracuseStep 26606003 = 39909005) B39909005
theorem B2693627 : Blo 1196415 2693627 := bstep (se 1 (by rfl) ⟨2020220, by rfl⟩ : syracuseStep 2693627 = 4040441) B4040441
theorem B2693753 : Blo 1196415 2693753 := bstep (se 2 (by rfl) ⟨1010157, by rfl⟩ : syracuseStep 2693753 = 2020315) B2020315
theorem B87366275 : Blo 1196415 87366275 := bstep (se 1 (by rfl) ⟨65524706, by rfl⟩ : syracuseStep 87366275 = 131049413) B131049413
theorem B2693807 : Blo 1196415 2693807 := bstep (se 1 (by rfl) ⟨2020355, by rfl⟩ : syracuseStep 2693807 = 4040711) B4040711
theorem B6822575 : Blo 1196415 6822575 := bstep (se 1 (by rfl) ⟨5116931, by rfl⟩ : syracuseStep 6822575 = 10233863) B10233863
theorem B5118659 : Blo 1196415 5118659 := bstep (se 1 (by rfl) ⟨3838994, by rfl⟩ : syracuseStep 5118659 = 7677989) B7677989
theorem B2693879 : Blo 1196415 2693879 := bstep (se 1 (by rfl) ⟨2020409, by rfl⟩ : syracuseStep 2693879 = 4040819) B4040819
theorem B116562725 : Blo 1196415 116562725 := bstep (se 4 (by rfl) ⟨10927755, by rfl⟩ : syracuseStep 116562725 = 21855511) B21855511
theorem B41483153 : Blo 1196415 41483153 := bstep (se 2 (by rfl) ⟨15556182, by rfl⟩ : syracuseStep 41483153 = 31112365) B31112365
theorem B2694059 : Blo 1196415 2694059 := bstep (se 1 (by rfl) ⟨2020544, by rfl⟩ : syracuseStep 2694059 = 4041089) B4041089
theorem B3030007 : Blo 1196415 3030007 := bstep (se 1 (by rfl) ⟨2272505, by rfl⟩ : syracuseStep 3030007 = 4545011) B4545011
theorem B19414205 : Blo 1196415 19414205 := bstep (se 3 (by rfl) ⟨3640163, by rfl⟩ : syracuseStep 19414205 = 7280327) B7280327
theorem B1514791 : Blo 1196415 1514791 := bstep (se 1 (by rfl) ⟨1136093, by rfl⟩ : syracuseStep 1514791 = 2272187) B2272187
theorem B3030311 : Blo 1196415 3030311 := bstep (se 1 (by rfl) ⟨2272733, by rfl⟩ : syracuseStep 3030311 = 4545467) B4545467
theorem B4857185 : Blo 1196415 4857185 := bstep (se 2 (by rfl) ⟨1821444, by rfl⟩ : syracuseStep 4857185 = 3642889) B3642889
theorem B7282057 : Blo 1196415 7282057 := bstep (se 2 (by rfl) ⟨2730771, by rfl⟩ : syracuseStep 7282057 = 5461543) B5461543
theorem B2555297 : Blo 1196415 2555297 := bstep (se 2 (by rfl) ⟨958236, by rfl⟩ : syracuseStep 2555297 = 1916473) B1916473
theorem B3235261 : Blo 1196415 3235261 := bstep (se 3 (by rfl) ⟨606611, by rfl⟩ : syracuseStep 3235261 = 1213223) B1213223
theorem B2694599 : Blo 1196415 2694599 := bstep (se 1 (by rfl) ⟨2020949, by rfl⟩ : syracuseStep 2694599 = 4041899) B4041899
theorem B4038227 : Blo 1196415 4038227 := bstep (se 1 (by rfl) ⟨3028670, by rfl⟩ : syracuseStep 4038227 = 6057341) B6057341
theorem B1515115 : Blo 1196415 1515115 := bstep (se 1 (by rfl) ⟨1136336, by rfl⟩ : syracuseStep 1515115 = 2272673) B2272673
theorem B12943111 : Blo 1196415 12943111 := bstep (se 1 (by rfl) ⟨9707333, by rfl⟩ : syracuseStep 12943111 = 19414667) B19414667
theorem B2694959 : Blo 1196415 2694959 := bstep (se 1 (by rfl) ⟨2021219, by rfl⟩ : syracuseStep 2694959 = 4042439) B4042439
theorem B1515343 : Blo 1196415 1515343 := bstep (se 1 (by rfl) ⟨1136507, by rfl⟩ : syracuseStep 1515343 = 2273015) B2273015
theorem B4038875 : Blo 1196415 4038875 := bstep (se 1 (by rfl) ⟨3029156, by rfl⟩ : syracuseStep 4038875 = 6058313) B6058313
theorem B3457255 : Blo 1196415 3457255 := bstep (se 1 (by rfl) ⟨2592941, by rfl⟩ : syracuseStep 3457255 = 5185883) B5185883
theorem B1196415 : Blo 1196415 1196415 := bstep (se 1 (by rfl) ⟨897311, by rfl⟩ : syracuseStep 1196415 = 1794623) B1794623
theorem B1196495 : Blo 1196415 1196495 := bstep (se 1 (by rfl) ⟨897371, by rfl⟩ : syracuseStep 1196495 = 1794743) B1794743
theorem B4039145 : Blo 1196415 4039145 := bstep (se 2 (by rfl) ⟨1514679, by rfl⟩ : syracuseStep 4039145 = 3029359) B3029359
theorem B1196647 : Blo 1196415 1196647 := bstep (se 1 (by rfl) ⟨897485, by rfl⟩ : syracuseStep 1196647 = 1794971) B1794971
theorem B1917703 : Blo 1196415 1917703 := bstep (se 1 (by rfl) ⟨1438277, by rfl⟩ : syracuseStep 1917703 = 2876555) B2876555
theorem B1794857 : Blo 1196415 1794857 := bstep (se 2 (by rfl) ⟨673071, by rfl⟩ : syracuseStep 1794857 = 1346143) B1346143
theorem B1794863 : Blo 1196415 1794863 := bstep (se 1 (by rfl) ⟨1346147, by rfl⟩ : syracuseStep 1794863 = 2692295) B2692295
theorem B2048825 : Blo 1196415 2048825 := bstep (se 2 (by rfl) ⟨768309, by rfl⟩ : syracuseStep 2048825 = 1536619) B1536619
theorem B1196911 : Blo 1196415 1196911 := bstep (se 1 (by rfl) ⟨897683, by rfl⟩ : syracuseStep 1196911 = 1795367) B1795367
theorem B1794983 : Blo 1196415 1794983 := bstep (se 1 (by rfl) ⟨1346237, by rfl⟩ : syracuseStep 1794983 = 2692475) B2692475
theorem B1196967 : Blo 1196415 1196967 := bstep (se 1 (by rfl) ⟨897725, by rfl⟩ : syracuseStep 1196967 = 1795451) B1795451
theorem B12952493 : Blo 1196415 12952493 := bstep (se 3 (by rfl) ⟨2428592, by rfl⟩ : syracuseStep 12952493 = 4857185) B4857185
theorem B2696147 : Blo 1196415 2696147 := bstep (se 1 (by rfl) ⟨2022110, by rfl⟩ : syracuseStep 2696147 = 4044221) B4044221
theorem B1795067 : Blo 1196415 1795067 := bstep (se 1 (by rfl) ⟨1346300, by rfl⟩ : syracuseStep 1795067 = 2692601) B2692601
theorem B1197051 : Blo 1196415 1197051 := bstep (se 1 (by rfl) ⟨897788, by rfl⟩ : syracuseStep 1197051 = 1795577) B1795577
theorem B4547609 : Blo 1196415 4547609 := bstep (se 2 (by rfl) ⟨1705353, by rfl⟩ : syracuseStep 4547609 = 3410707) B3410707
theorem B1795127 : Blo 1196415 1795127 := bstep (se 1 (by rfl) ⟨1346345, by rfl⟩ : syracuseStep 1795127 = 2692691) B2692691
theorem B4039739 : Blo 1196415 4039739 := bstep (se 1 (by rfl) ⟨3029804, by rfl⟩ : syracuseStep 4039739 = 6059609) B6059609
theorem B1197119 : Blo 1196415 1197119 := bstep (se 1 (by rfl) ⟨897839, by rfl⟩ : syracuseStep 1197119 = 1795679) B1795679
theorem B13124753 : Blo 1196415 13124753 := bstep (se 2 (by rfl) ⟨4921782, by rfl⟩ : syracuseStep 13124753 = 9843565) B9843565
theorem B1795247 : Blo 1196415 1795247 := bstep (se 1 (by rfl) ⟨1346435, by rfl⟩ : syracuseStep 1795247 = 2692871) B2692871
theorem B20448449 : Blo 1196415 20448449 := bstep (se 2 (by rfl) ⟨7668168, by rfl⟩ : syracuseStep 20448449 = 15336337) B15336337
theorem B1197263 : Blo 1196415 1197263 := bstep (se 1 (by rfl) ⟨897947, by rfl⟩ : syracuseStep 1197263 = 1795895) B1795895
theorem B2696399 : Blo 1196415 2696399 := bstep (se 1 (by rfl) ⟨2022299, by rfl⟩ : syracuseStep 2696399 = 4044599) B4044599
theorem B4040009 : Blo 1196415 4040009 := bstep (se 2 (by rfl) ⟨1515003, by rfl⟩ : syracuseStep 4040009 = 3030007) B3030007
theorem B1197467 : Blo 1196415 1197467 := bstep (se 1 (by rfl) ⟨898100, by rfl⟩ : syracuseStep 1197467 = 1796201) B1796201
theorem B1795655 : Blo 1196415 1795655 := bstep (se 1 (by rfl) ⟨1346741, by rfl⟩ : syracuseStep 1795655 = 2693483) B2693483
theorem B3278447 : Blo 1196415 3278447 := bstep (se 1 (by rfl) ⟨2458835, by rfl⟩ : syracuseStep 3278447 = 4917671) B4917671
theorem B1197679 : Blo 1196415 1197679 := bstep (se 1 (by rfl) ⟨898259, by rfl⟩ : syracuseStep 1197679 = 1796519) B1796519
theorem B1795751 : Blo 1196415 1795751 := bstep (se 1 (by rfl) ⟨1346813, by rfl⟩ : syracuseStep 1795751 = 2693627) B2693627
theorem B1197735 : Blo 1196415 1197735 := bstep (se 1 (by rfl) ⟨898301, by rfl⟩ : syracuseStep 1197735 = 1796603) B1796603
theorem B1705655 : Blo 1196415 1705655 := bstep (se 1 (by rfl) ⟨1279241, by rfl⟩ : syracuseStep 1705655 = 2558483) B2558483
theorem B6907577 : Blo 1196415 6907577 := bstep (se 2 (by rfl) ⟨2590341, by rfl⟩ : syracuseStep 6907577 = 5180683) B5180683
theorem B1795835 : Blo 1196415 1795835 := bstep (se 1 (by rfl) ⟨1346876, by rfl⟩ : syracuseStep 1795835 = 2693753) B2693753
theorem B1197819 : Blo 1196415 1197819 := bstep (se 1 (by rfl) ⟨898364, by rfl⟩ : syracuseStep 1197819 = 1796729) B1796729
theorem B1795871 : Blo 1196415 1795871 := bstep (se 1 (by rfl) ⟨1346903, by rfl⟩ : syracuseStep 1795871 = 2693807) B2693807
theorem B1197855 : Blo 1196415 1197855 := bstep (se 1 (by rfl) ⟨898391, by rfl⟩ : syracuseStep 1197855 = 1796783) B1796783
theorem B4548383 : Blo 1196415 4548383 := bstep (se 1 (by rfl) ⟨3411287, by rfl⟩ : syracuseStep 4548383 = 6822575) B6822575
theorem B1197887 : Blo 1196415 1197887 := bstep (se 1 (by rfl) ⟨898415, by rfl⟩ : syracuseStep 1197887 = 1796831) B1796831
theorem B1795919 : Blo 1196415 1795919 := bstep (se 1 (by rfl) ⟨1346939, by rfl⟩ : syracuseStep 1795919 = 2693879) B2693879
theorem B1918799 : Blo 1196415 1918799 := bstep (se 1 (by rfl) ⟨1439099, by rfl⟩ : syracuseStep 1918799 = 2878199) B2878199
theorem B9709409 : Blo 1196415 9709409 := bstep (se 2 (by rfl) ⟨3641028, by rfl⟩ : syracuseStep 9709409 = 7282057) B7282057
theorem B1796039 : Blo 1196415 1796039 := bstep (se 1 (by rfl) ⟨1347029, by rfl⟩ : syracuseStep 1796039 = 2694059) B2694059
theorem B1198063 : Blo 1196415 1198063 := bstep (se 1 (by rfl) ⟨898547, by rfl⟩ : syracuseStep 1198063 = 1797095) B1797095
theorem B1198235 : Blo 1196415 1198235 := bstep (se 1 (by rfl) ⟨898676, by rfl⟩ : syracuseStep 1198235 = 1797353) B1797353
theorem B1198271 : Blo 1196415 1198271 := bstep (se 1 (by rfl) ⟨898703, by rfl⟩ : syracuseStep 1198271 = 1797407) B1797407
theorem B1919209 : Blo 1196415 1919209 := bstep (se 2 (by rfl) ⟨719703, by rfl⟩ : syracuseStep 1919209 = 1439407) B1439407
theorem B1796393 : Blo 1196415 1796393 := bstep (se 2 (by rfl) ⟨673647, by rfl⟩ : syracuseStep 1796393 = 1347295) B1347295
theorem B1796399 : Blo 1196415 1796399 := bstep (se 1 (by rfl) ⟨1347299, by rfl⟩ : syracuseStep 1796399 = 2694599) B2694599
theorem B1198383 : Blo 1196415 1198383 := bstep (se 1 (by rfl) ⟨898787, by rfl⟩ : syracuseStep 1198383 = 1797575) B1797575
theorem B3688843 : Blo 1196415 3688843 := bstep (se 1 (by rfl) ⟨2766632, by rfl⟩ : syracuseStep 3688843 = 5533265) B5533265
theorem B3836443 : Blo 1196415 3836443 := bstep (se 1 (by rfl) ⟨2877332, by rfl⟩ : syracuseStep 3836443 = 5754665) B5754665
theorem B1796639 : Blo 1196415 1796639 := bstep (se 1 (by rfl) ⟨1347479, by rfl⟩ : syracuseStep 1796639 = 2694959) B2694959
theorem B10930859 : Blo 1196415 10930859 := bstep (se 1 (by rfl) ⟨8198144, by rfl⟩ : syracuseStep 10930859 = 16396289) B16396289
theorem B6818519 : Blo 1196415 6818519 := bstep (se 1 (by rfl) ⟨5113889, by rfl⟩ : syracuseStep 6818519 = 10227779) B10227779
theorem B32778989 : Blo 1196415 32778989 := bstep (se 3 (by rfl) ⟨6146060, by rfl⟩ : syracuseStep 32778989 = 12292121) B12292121
theorem B1346395 : Blo 1196415 1346395 := bstep (se 1 (by rfl) ⟨1009796, by rfl⟩ : syracuseStep 1346395 = 2019593) B2019593
theorem B1797023 : Blo 1196415 1797023 := bstep (se 1 (by rfl) ⟨1347767, by rfl⟩ : syracuseStep 1797023 = 2695535) B2695535
theorem B1797071 : Blo 1196415 1797071 := bstep (se 1 (by rfl) ⟨1347803, by rfl⟩ : syracuseStep 1797071 = 2695607) B2695607
theorem B3410923 : Blo 1196415 3410923 := bstep (se 1 (by rfl) ⟨2558192, by rfl⟩ : syracuseStep 3410923 = 5116385) B5116385
theorem B1797161 : Blo 1196415 1797161 := bstep (se 2 (by rfl) ⟨673935, by rfl⟩ : syracuseStep 1797161 = 1347871) B1347871
theorem B1821737 : Blo 1196415 1821737 := bstep (se 2 (by rfl) ⟨683151, by rfl⟩ : syracuseStep 1821737 = 1366303) B1366303
theorem B1797167 : Blo 1196415 1797167 := bstep (se 1 (by rfl) ⟨1347875, by rfl⟩ : syracuseStep 1797167 = 2695751) B2695751
theorem B1797191 : Blo 1196415 1797191 := bstep (se 1 (by rfl) ⟨1347893, by rfl⟩ : syracuseStep 1797191 = 2695787) B2695787
theorem B1797455 : Blo 1196415 1797455 := bstep (se 1 (by rfl) ⟨1348091, by rfl⟩ : syracuseStep 1797455 = 2696183) B2696183
theorem B1797545 : Blo 1196415 1797545 := bstep (se 2 (by rfl) ⟨674079, by rfl⟩ : syracuseStep 1797545 = 1348159) B1348159
theorem B5115325 : Blo 1196415 5115325 := bstep (se 3 (by rfl) ⟨959123, by rfl⟩ : syracuseStep 5115325 = 1918247) B1918247
theorem B1347367 : Blo 1196415 1347367 := bstep (se 1 (by rfl) ⟨1010525, by rfl⟩ : syracuseStep 1347367 = 2021051) B2021051
theorem B8638285 : Blo 1196415 8638285 := bstep (se 3 (by rfl) ⟨1619678, by rfl⟩ : syracuseStep 8638285 = 3239357) B3239357
theorem B4042601 : Blo 1196415 4042601 := bstep (se 2 (by rfl) ⟨1515975, by rfl⟩ : syracuseStep 4042601 = 3031951) B3031951
theorem B5181305 : Blo 1196415 5181305 := bstep (se 2 (by rfl) ⟨1942989, by rfl⟩ : syracuseStep 5181305 = 3885979) B3885979
theorem B12955697 : Blo 1196415 12955697 := bstep (se 2 (by rfl) ⟨4858386, by rfl⟩ : syracuseStep 12955697 = 9716773) B9716773
theorem B13824209 : Blo 1196415 13824209 := bstep (se 2 (by rfl) ⟨5184078, by rfl⟩ : syracuseStep 13824209 = 10368157) B10368157
theorem B2019559 : Blo 1196415 2019559 := bstep (se 1 (by rfl) ⟨1514669, by rfl⟩ : syracuseStep 2019559 = 3029339) B3029339
theorem B2019721 : Blo 1196415 2019721 := bstep (se 2 (by rfl) ⟨757395, by rfl⟩ : syracuseStep 2019721 = 1514791) B1514791
theorem B3412439 : Blo 1196415 3412439 := bstep (se 1 (by rfl) ⟨2559329, by rfl⟩ : syracuseStep 3412439 = 5118659) B5118659
theorem B4313681 : Blo 1196415 4313681 := bstep (se 2 (by rfl) ⟨1617630, by rfl⟩ : syracuseStep 4313681 = 3235261) B3235261
theorem B2020153 : Blo 1196415 2020153 := bstep (se 2 (by rfl) ⟨757557, by rfl⟩ : syracuseStep 2020153 = 1515115) B1515115
theorem B2020207 : Blo 1196415 2020207 := bstep (se 1 (by rfl) ⟨1515155, by rfl⟩ : syracuseStep 2020207 = 3030311) B3030311
theorem B17257481 : Blo 1196415 17257481 := bstep (se 2 (by rfl) ⟨6471555, by rfl⟩ : syracuseStep 17257481 = 12943111) B12943111
theorem B2692151 : Blo 1196415 2692151 := bstep (se 1 (by rfl) ⟨2019113, by rfl⟩ : syracuseStep 2692151 = 4038227) B4038227
theorem B3503159 : Blo 1196415 3503159 := bstep (se 1 (by rfl) ⟨2627369, by rfl⟩ : syracuseStep 3503159 = 5254739) B5254739
theorem B2692169 : Blo 1196415 2692169 := bstep (se 2 (by rfl) ⟨1009563, by rfl⟩ : syracuseStep 2692169 = 2019127) B2019127
theorem B2020457 : Blo 1196415 2020457 := bstep (se 2 (by rfl) ⟨757671, by rfl⟩ : syracuseStep 2020457 = 1515343) B1515343
theorem B6059123 : Blo 1196415 6059123 := bstep (se 1 (by rfl) ⟨4544342, by rfl⟩ : syracuseStep 6059123 = 9088685) B9088685
theorem B4043951 : Blo 1196415 4043951 := bstep (se 1 (by rfl) ⟨3032963, by rfl⟩ : syracuseStep 4043951 = 6065927) B6065927
theorem B16602457 : Blo 1196415 16602457 := bstep (se 2 (by rfl) ⟨6225921, by rfl⟩ : syracuseStep 16602457 = 12451843) B12451843
theorem B28431767 : Blo 1196415 28431767 := bstep (se 1 (by rfl) ⟨21323825, by rfl⟩ : syracuseStep 28431767 = 42647651) B42647651
theorem B20739629 : Blo 1196415 20739629 := bstep (se 3 (by rfl) ⟨3888680, by rfl⟩ : syracuseStep 20739629 = 7777361) B7777361
theorem B15349459 : Blo 1196415 15349459 := bstep (se 1 (by rfl) ⟨11512094, by rfl⟩ : syracuseStep 15349459 = 23024189) B23024189
theorem B7780049 : Blo 1196415 7780049 := bstep (se 2 (by rfl) ⟨2917518, by rfl⟩ : syracuseStep 7780049 = 5835037) B5835037
theorem B6059771 : Blo 1196415 6059771 := bstep (se 1 (by rfl) ⟨4544828, by rfl⟩ : syracuseStep 6059771 = 9089657) B9089657
theorem B3028873 : Blo 1196415 3028873 := bstep (se 2 (by rfl) ⟨1135827, by rfl⟩ : syracuseStep 3028873 = 2271655) B2271655
theorem B9222025 : Blo 1196415 9222025 := bstep (se 2 (by rfl) ⟨3458259, by rfl⟩ : syracuseStep 9222025 = 6916519) B6916519
theorem B6059933 : Blo 1196415 6059933 := bstep (se 3 (by rfl) ⟨1136237, by rfl⟩ : syracuseStep 6059933 = 2272475) B2272475
theorem B4544495 : Blo 1196415 4544495 := bstep (se 1 (by rfl) ⟨3408371, by rfl⟩ : syracuseStep 4544495 = 6816743) B6816743
theorem B3028985 : Blo 1196415 3028985 := bstep (se 2 (by rfl) ⟨1135869, by rfl⟩ : syracuseStep 3028985 = 2271739) B2271739
theorem B20461571 : Blo 1196415 20461571 := bstep (se 1 (by rfl) ⟨15346178, by rfl⟩ : syracuseStep 20461571 = 30692357) B30692357
theorem B3029147 : Blo 1196415 3029147 := bstep (se 1 (by rfl) ⟨2271860, by rfl⟩ : syracuseStep 3029147 = 4543721) B4543721
theorem B2021611 : Blo 1196415 2021611 := bstep (se 1 (by rfl) ⟨1516208, by rfl⟩ : syracuseStep 2021611 = 3032417) B3032417
theorem B4856051 : Blo 1196415 4856051 := bstep (se 1 (by rfl) ⟨3642038, by rfl⟩ : syracuseStep 4856051 = 7284077) B7284077
theorem B7879027 : Blo 1196415 7879027 := bstep (se 1 (by rfl) ⟨5909270, by rfl⟩ : syracuseStep 7879027 = 11818541) B11818541
theorem B70949341 : Blo 1196415 70949341 := bstep (se 3 (by rfl) ⟨13303001, by rfl⟩ : syracuseStep 70949341 = 26606003) B26606003
theorem B77896187 : Blo 1196415 77896187 := bstep (se 1 (by rfl) ⟨58422140, by rfl⟩ : syracuseStep 77896187 = 116844281) B116844281
theorem B2021915 : Blo 1196415 2021915 := bstep (se 1 (by rfl) ⟨1516436, by rfl⟩ : syracuseStep 2021915 = 3032873) B3032873
theorem B9099863 : Blo 1196415 9099863 := bstep (se 1 (by rfl) ⟨6824897, by rfl⟩ : syracuseStep 9099863 = 13649795) B13649795
theorem B6060743 : Blo 1196415 6060743 := bstep (se 1 (by rfl) ⟨4545557, by rfl⟩ : syracuseStep 6060743 = 9091115) B9091115
theorem B65592139 : Blo 1196415 65592139 := bstep (se 1 (by rfl) ⟨49194104, by rfl⟩ : syracuseStep 65592139 = 98388209) B98388209
theorem B5757779 : Blo 1196415 5757779 := bstep (se 1 (by rfl) ⟨4318334, by rfl⟩ : syracuseStep 5757779 = 8636669) B8636669
theorem B2694095 : Blo 1196415 2694095 := bstep (se 1 (by rfl) ⟨2020571, by rfl⟩ : syracuseStep 2694095 = 4041143) B4041143
theorem B2694113 : Blo 1196415 2694113 := bstep (se 2 (by rfl) ⟨1010292, by rfl⟩ : syracuseStep 2694113 = 2020585) B2020585
theorem B6822893 : Blo 1196415 6822893 := bstep (se 3 (by rfl) ⟨1279292, by rfl⟩ : syracuseStep 6822893 = 2558585) B2558585
theorem B2694185 : Blo 1196415 2694185 := bstep (se 2 (by rfl) ⟨1010319, by rfl⟩ : syracuseStep 2694185 = 2020639) B2020639
theorem B58244183 : Blo 1196415 58244183 := bstep (se 1 (by rfl) ⟨43683137, by rfl⟩ : syracuseStep 58244183 = 87366275) B87366275
theorem B3832957 : Blo 1196415 3832957 := bstep (se 3 (by rfl) ⟨718679, by rfl⟩ : syracuseStep 3832957 = 1437359) B1437359
theorem B77708483 : Blo 1196415 77708483 := bstep (se 1 (by rfl) ⟨58281362, by rfl⟩ : syracuseStep 77708483 = 116562725) B116562725
theorem B3030281 : Blo 1196415 3030281 := bstep (se 2 (by rfl) ⟨1136355, by rfl⟩ : syracuseStep 3030281 = 2272711) B2272711
theorem B27655435 : Blo 1196415 27655435 := bstep (se 1 (by rfl) ⟨20741576, by rfl⟩ : syracuseStep 27655435 = 41483153) B41483153
theorem B6913309 : Blo 1196415 6913309 := bstep (se 3 (by rfl) ⟨1296245, by rfl⟩ : syracuseStep 6913309 = 2592491) B2592491
theorem B20749603 : Blo 1196415 20749603 := bstep (se 1 (by rfl) ⟨15562202, by rfl⟩ : syracuseStep 20749603 = 31124405) B31124405
theorem B4545953 : Blo 1196415 4545953 := bstep (se 2 (by rfl) ⟨1704732, by rfl⟩ : syracuseStep 4545953 = 3409465) B3409465
theorem B12942803 : Blo 1196415 12942803 := bstep (se 1 (by rfl) ⟨9707102, by rfl⟩ : syracuseStep 12942803 = 19414205) B19414205
theorem B4038119 : Blo 1196415 4038119 := bstep (se 1 (by rfl) ⟨3028589, by rfl⟩ : syracuseStep 4038119 = 6057179) B6057179
theorem B1703531 : Blo 1196415 1703531 := bstep (se 1 (by rfl) ⟨1277648, by rfl⟩ : syracuseStep 1703531 = 2555297) B2555297
theorem B14565329 : Blo 1196415 14565329 := bstep (se 2 (by rfl) ⟨5461998, by rfl⟩ : syracuseStep 14565329 = 10923997) B10923997
theorem B4857965 : Blo 1196415 4857965 := bstep (se 3 (by rfl) ⟨910868, by rfl⟩ : syracuseStep 4857965 = 1821737) B1821737
theorem B9216139 : Blo 1196415 9216139 := bstep (se 1 (by rfl) ⟨6912104, by rfl⟩ : syracuseStep 9216139 = 13824209) B13824209
theorem B2695481 : Blo 1196415 2695481 := bstep (se 2 (by rfl) ⟨1010805, by rfl⟩ : syracuseStep 2695481 = 2021611) B2021611
theorem B2875787 : Blo 1196415 2875787 := bstep (se 1 (by rfl) ⟨2156840, by rfl⟩ : syracuseStep 2875787 = 4313681) B4313681
theorem B1196571 : Blo 1196415 1196571 := bstep (se 1 (by rfl) ⟨897428, by rfl⟩ : syracuseStep 1196571 = 1794857) B1794857
theorem B1196575 : Blo 1196415 1196575 := bstep (se 1 (by rfl) ⟨897431, by rfl⟩ : syracuseStep 1196575 = 1794863) B1794863
theorem B1196655 : Blo 1196415 1196655 := bstep (se 1 (by rfl) ⟨897491, by rfl⟩ : syracuseStep 1196655 = 1794983) B1794983
theorem B8634995 : Blo 1196415 8634995 := bstep (se 1 (by rfl) ⟨6476246, by rfl⟩ : syracuseStep 8634995 = 12952493) B12952493
theorem B1196711 : Blo 1196415 1196711 := bstep (se 1 (by rfl) ⟨897533, by rfl⟩ : syracuseStep 1196711 = 1795067) B1795067
theorem B3031739 : Blo 1196415 3031739 := bstep (se 1 (by rfl) ⟨2273804, by rfl⟩ : syracuseStep 3031739 = 4547609) B4547609
theorem B1794767 : Blo 1196415 1794767 := bstep (se 1 (by rfl) ⟨1346075, by rfl⟩ : syracuseStep 1794767 = 2692151) B2692151
theorem B1196751 : Blo 1196415 1196751 := bstep (se 1 (by rfl) ⟨897563, by rfl⟩ : syracuseStep 1196751 = 1795127) B1795127
theorem B2335439 : Blo 1196415 2335439 := bstep (se 1 (by rfl) ⟨1751579, by rfl⟩ : syracuseStep 2335439 = 3503159) B3503159
theorem B1794779 : Blo 1196415 1794779 := bstep (se 1 (by rfl) ⟨1346084, by rfl⟩ : syracuseStep 1794779 = 2692169) B2692169
theorem B4039415 : Blo 1196415 4039415 := bstep (se 1 (by rfl) ⟨3029561, by rfl⟩ : syracuseStep 4039415 = 6059123) B6059123
theorem B8749835 : Blo 1196415 8749835 := bstep (se 1 (by rfl) ⟨6562376, by rfl⟩ : syracuseStep 8749835 = 13124753) B13124753
theorem B1196831 : Blo 1196415 1196831 := bstep (se 1 (by rfl) ⟨897623, by rfl⟩ : syracuseStep 1196831 = 1795247) B1795247
theorem B2695967 : Blo 1196415 2695967 := bstep (se 1 (by rfl) ⟨2021975, by rfl⟩ : syracuseStep 2695967 = 4043951) B4043951
theorem B13632299 : Blo 1196415 13632299 := bstep (se 1 (by rfl) ⟨10224224, by rfl⟩ : syracuseStep 13632299 = 20448449) B20448449
theorem B2556937 : Blo 1196415 2556937 := bstep (se 2 (by rfl) ⟨958851, by rfl⟩ : syracuseStep 2556937 = 1917703) B1917703
theorem B1197103 : Blo 1196415 1197103 := bstep (se 1 (by rfl) ⟨897827, by rfl⟩ : syracuseStep 1197103 = 1795655) B1795655
theorem B75818045 : Blo 1196415 75818045 := bstep (se 3 (by rfl) ⟨14215883, by rfl⟩ : syracuseStep 75818045 = 28431767) B28431767
theorem B1197167 : Blo 1196415 1197167 := bstep (se 1 (by rfl) ⟨897875, by rfl⟩ : syracuseStep 1197167 = 1795751) B1795751
theorem B1795193 : Blo 1196415 1795193 := bstep (se 2 (by rfl) ⟨673197, by rfl⟩ : syracuseStep 1795193 = 1346395) B1346395
theorem B5186699 : Blo 1196415 5186699 := bstep (se 1 (by rfl) ⟨3890024, by rfl⟩ : syracuseStep 5186699 = 7780049) B7780049
theorem B4039847 : Blo 1196415 4039847 := bstep (se 1 (by rfl) ⟨3029885, by rfl⟩ : syracuseStep 4039847 = 6059771) B6059771
theorem B1197223 : Blo 1196415 1197223 := bstep (se 1 (by rfl) ⟨897917, by rfl⟩ : syracuseStep 1197223 = 1795835) B1795835
theorem B1197247 : Blo 1196415 1197247 := bstep (se 1 (by rfl) ⟨897935, by rfl⟩ : syracuseStep 1197247 = 1795871) B1795871
theorem B3032255 : Blo 1196415 3032255 := bstep (se 1 (by rfl) ⟨2274191, by rfl⟩ : syracuseStep 3032255 = 4548383) B4548383
theorem B1197279 : Blo 1196415 1197279 := bstep (se 1 (by rfl) ⟨897959, by rfl⟩ : syracuseStep 1197279 = 1795919) B1795919
theorem B1279199 : Blo 1196415 1279199 := bstep (se 1 (by rfl) ⟨959399, by rfl⟩ : syracuseStep 1279199 = 1918799) B1918799
theorem B4039955 : Blo 1196415 4039955 := bstep (se 1 (by rfl) ⟨3029966, by rfl⟩ : syracuseStep 4039955 = 6059933) B6059933
theorem B1197359 : Blo 1196415 1197359 := bstep (se 1 (by rfl) ⟨898019, by rfl⟩ : syracuseStep 1197359 = 1796039) B1796039
theorem B4547897 : Blo 1196415 4547897 := bstep (se 2 (by rfl) ⟨1705461, by rfl⟩ : syracuseStep 4547897 = 3410923) B3410923
theorem B13641047 : Blo 1196415 13641047 := bstep (se 1 (by rfl) ⟨10230785, by rfl⟩ : syracuseStep 13641047 = 20461571) B20461571
theorem B1197595 : Blo 1196415 1197595 := bstep (se 1 (by rfl) ⟨898196, by rfl⟩ : syracuseStep 1197595 = 1796393) B1796393
theorem B1197599 : Blo 1196415 1197599 := bstep (se 1 (by rfl) ⟨898199, by rfl⟩ : syracuseStep 1197599 = 1796399) B1796399
theorem B51930791 : Blo 1196415 51930791 := bstep (se 1 (by rfl) ⟨38948093, by rfl⟩ : syracuseStep 51930791 = 77896187) B77896187
theorem B36873913 : Blo 1196415 36873913 := bstep (se 2 (by rfl) ⟨13827717, by rfl⟩ : syracuseStep 36873913 = 27655435) B27655435
theorem B1197759 : Blo 1196415 1197759 := bstep (se 1 (by rfl) ⟨898319, by rfl⟩ : syracuseStep 1197759 = 1796639) B1796639
theorem B9217745 : Blo 1196415 9217745 := bstep (se 2 (by rfl) ⟨3456654, by rfl⟩ : syracuseStep 9217745 = 6913309) B6913309
theorem B27666137 : Blo 1196415 27666137 := bstep (se 2 (by rfl) ⟨10374801, by rfl⟩ : syracuseStep 27666137 = 20749603) B20749603
theorem B22136609 : Blo 1196415 22136609 := bstep (se 2 (by rfl) ⟨8301228, by rfl⟩ : syracuseStep 22136609 = 16602457) B16602457
theorem B4040495 : Blo 1196415 4040495 := bstep (se 1 (by rfl) ⟨3030371, by rfl⟩ : syracuseStep 4040495 = 6060743) B6060743
theorem B4548413 : Blo 1196415 4548413 := bstep (se 3 (by rfl) ⟨852827, by rfl⟩ : syracuseStep 4548413 = 1705655) B1705655
theorem B1198015 : Blo 1196415 1198015 := bstep (se 1 (by rfl) ⟨898511, by rfl⟩ : syracuseStep 1198015 = 1797023) B1797023
theorem B1796063 : Blo 1196415 1796063 := bstep (se 1 (by rfl) ⟨1347047, by rfl⟩ : syracuseStep 1796063 = 2694095) B2694095
theorem B1198047 : Blo 1196415 1198047 := bstep (se 1 (by rfl) ⟨898535, by rfl⟩ : syracuseStep 1198047 = 1797071) B1797071
theorem B1796075 : Blo 1196415 1796075 := bstep (se 1 (by rfl) ⟨1347056, by rfl⟩ : syracuseStep 1796075 = 2694113) B2694113
theorem B4548595 : Blo 1196415 4548595 := bstep (se 1 (by rfl) ⟨3411446, by rfl⟩ : syracuseStep 4548595 = 6822893) B6822893
theorem B1796123 : Blo 1196415 1796123 := bstep (se 1 (by rfl) ⟨1347092, by rfl⟩ : syracuseStep 1796123 = 2694185) B2694185
theorem B1198107 : Blo 1196415 1198107 := bstep (se 1 (by rfl) ⟨898580, by rfl⟩ : syracuseStep 1198107 = 1797161) B1797161
theorem B1198111 : Blo 1196415 1198111 := bstep (se 1 (by rfl) ⟨898583, by rfl⟩ : syracuseStep 1198111 = 1797167) B1797167
theorem B1198127 : Blo 1196415 1198127 := bstep (se 1 (by rfl) ⟨898595, by rfl⟩ : syracuseStep 1198127 = 1797191) B1797191
theorem B1198303 : Blo 1196415 1198303 := bstep (se 1 (by rfl) ⟨898727, by rfl⟩ : syracuseStep 1198303 = 1797455) B1797455
theorem B20465945 : Blo 1196415 20465945 := bstep (se 2 (by rfl) ⟨7674729, by rfl⟩ : syracuseStep 20465945 = 15349459) B15349459
theorem B1198363 : Blo 1196415 1198363 := bstep (se 1 (by rfl) ⟨898772, by rfl⟩ : syracuseStep 1198363 = 1797545) B1797545
theorem B8628535 : Blo 1196415 8628535 := bstep (se 1 (by rfl) ⟨6471401, by rfl⟩ : syracuseStep 8628535 = 12942803) B12942803
theorem B1796489 : Blo 1196415 1796489 := bstep (se 2 (by rfl) ⟨673683, by rfl⟩ : syracuseStep 1796489 = 1347367) B1347367
theorem B9710219 : Blo 1196415 9710219 := bstep (se 1 (by rfl) ⟨7282664, by rfl⟩ : syracuseStep 9710219 = 14565329) B14565329
theorem B8637131 : Blo 1196415 8637131 := bstep (se 1 (by rfl) ⟨6477848, by rfl⟩ : syracuseStep 8637131 = 12955697) B12955697
theorem B2558945 : Blo 1196415 2558945 := bstep (se 2 (by rfl) ⟨959604, by rfl⟩ : syracuseStep 2558945 = 1919209) B1919209
theorem B10505369 : Blo 1196415 10505369 := bstep (se 2 (by rfl) ⟨3939513, by rfl⟩ : syracuseStep 10505369 = 7879027) B7879027
theorem B4918457 : Blo 1196415 4918457 := bstep (se 2 (by rfl) ⟨1844421, by rfl⟩ : syracuseStep 4918457 = 3688843) B3688843
theorem B1797431 : Blo 1196415 1797431 := bstep (se 1 (by rfl) ⟨1348073, by rfl⟩ : syracuseStep 1797431 = 2696147) B2696147
theorem B11504987 : Blo 1196415 11504987 := bstep (se 1 (by rfl) ⟨8628740, by rfl⟩ : syracuseStep 11504987 = 17257481) B17257481
theorem B5115257 : Blo 1196415 5115257 := bstep (se 2 (by rfl) ⟨1918221, by rfl⟩ : syracuseStep 5115257 = 3836443) B3836443
theorem B1346971 : Blo 1196415 1346971 := bstep (se 1 (by rfl) ⟨1010228, by rfl⟩ : syracuseStep 1346971 = 2020457) B2020457
theorem B1797599 : Blo 1196415 1797599 := bstep (se 1 (by rfl) ⟨1348199, by rfl⟩ : syracuseStep 1797599 = 2696399) B2696399
theorem B2019323 : Blo 1196415 2019323 := bstep (se 1 (by rfl) ⟨1514492, by rfl⟩ : syracuseStep 2019323 = 3028985) B3028985
theorem B2019431 : Blo 1196415 2019431 := bstep (se 1 (by rfl) ⟨1514573, by rfl⟩ : syracuseStep 2019431 = 3029147) B3029147
theorem B4542749 : Blo 1196415 4542749 := bstep (se 3 (by rfl) ⟨851765, by rfl⟩ : syracuseStep 4542749 = 1703531) B1703531
theorem B1347943 : Blo 1196415 1347943 := bstep (se 1 (by rfl) ⟨1010957, by rfl⟩ : syracuseStep 1347943 = 2021915) B2021915
theorem B6066575 : Blo 1196415 6066575 := bstep (se 1 (by rfl) ⟨4549931, by rfl⟩ : syracuseStep 6066575 = 9099863) B9099863
theorem B7287239 : Blo 1196415 7287239 := bstep (se 1 (by rfl) ⟨5465429, by rfl⟩ : syracuseStep 7287239 = 10930859) B10930859
theorem B18420205 : Blo 1196415 18420205 := bstep (se 3 (by rfl) ⟨3453788, by rfl⟩ : syracuseStep 18420205 = 6907577) B6907577
theorem B21852659 : Blo 1196415 21852659 := bstep (se 1 (by rfl) ⟨16389494, by rfl⟩ : syracuseStep 21852659 = 32778989) B32778989
theorem B3838519 : Blo 1196415 3838519 := bstep (se 1 (by rfl) ⟨2878889, by rfl⟩ : syracuseStep 3838519 = 5757779) B5757779
theorem B6820433 : Blo 1196415 6820433 := bstep (se 2 (by rfl) ⟨2557662, by rfl⟩ : syracuseStep 6820433 = 5115325) B5115325
theorem B2020187 : Blo 1196415 2020187 := bstep (se 1 (by rfl) ⟨1515140, by rfl⟩ : syracuseStep 2020187 = 3030281) B3030281
theorem B25891757 : Blo 1196415 25891757 := bstep (se 3 (by rfl) ⟨4854704, by rfl⟩ : syracuseStep 25891757 = 9709409) B9709409
theorem B13816813 : Blo 1196415 13816813 := bstep (se 3 (by rfl) ⟨2590652, by rfl⟩ : syracuseStep 13816813 = 5181305) B5181305
theorem B2692079 : Blo 1196415 2692079 := bstep (se 1 (by rfl) ⟨2019059, by rfl⟩ : syracuseStep 2692079 = 4038119) B4038119
theorem B2692583 : Blo 1196415 2692583 := bstep (se 1 (by rfl) ⟨2019437, by rfl⟩ : syracuseStep 2692583 = 4038875) B4038875
theorem B2692745 : Blo 1196415 2692745 := bstep (se 2 (by rfl) ⟨1009779, by rfl⟩ : syracuseStep 2692745 = 2019559) B2019559
theorem B4609673 : Blo 1196415 4609673 := bstep (se 2 (by rfl) ⟨1728627, by rfl⟩ : syracuseStep 4609673 = 3457255) B3457255
theorem B2274959 : Blo 1196415 2274959 := bstep (se 1 (by rfl) ⟨1706219, by rfl⟩ : syracuseStep 2274959 = 3412439) B3412439
theorem B2692763 : Blo 1196415 2692763 := bstep (se 1 (by rfl) ⟨2019572, by rfl⟩ : syracuseStep 2692763 = 4039145) B4039145
theorem B2692961 : Blo 1196415 2692961 := bstep (se 2 (by rfl) ⟨1009860, by rfl⟩ : syracuseStep 2692961 = 2019721) B2019721
theorem B94599121 : Blo 1196415 94599121 := bstep (se 2 (by rfl) ⟨35474670, by rfl⟩ : syracuseStep 94599121 = 70949341) B70949341
theorem B12949469 : Blo 1196415 12949469 := bstep (se 3 (by rfl) ⟨2428025, by rfl⟩ : syracuseStep 12949469 = 4856051) B4856051
theorem B2693159 : Blo 1196415 2693159 := bstep (se 1 (by rfl) ⟨2019869, by rfl⟩ : syracuseStep 2693159 = 4039739) B4039739
theorem B2693339 : Blo 1196415 2693339 := bstep (se 1 (by rfl) ⟨2020004, by rfl⟩ : syracuseStep 2693339 = 4040009) B4040009
theorem B13826419 : Blo 1196415 13826419 := bstep (se 1 (by rfl) ⟨10369814, by rfl⟩ : syracuseStep 13826419 = 20739629) B20739629
theorem B2185631 : Blo 1196415 2185631 := bstep (se 1 (by rfl) ⟨1639223, by rfl⟩ : syracuseStep 2185631 = 3278447) B3278447
theorem B2693537 : Blo 1196415 2693537 := bstep (se 2 (by rfl) ⟨1010076, by rfl⟩ : syracuseStep 2693537 = 2020153) B2020153
theorem B87456185 : Blo 1196415 87456185 := bstep (se 2 (by rfl) ⟨32796069, by rfl⟩ : syracuseStep 87456185 = 65592139) B65592139
theorem B2693609 : Blo 1196415 2693609 := bstep (se 2 (by rfl) ⟨1010103, by rfl⟩ : syracuseStep 2693609 = 2020207) B2020207
theorem B3029663 : Blo 1196415 3029663 := bstep (se 1 (by rfl) ⟨2272247, by rfl⟩ : syracuseStep 3029663 = 4544495) B4544495
theorem B5110609 : Blo 1196415 5110609 := bstep (se 2 (by rfl) ⟨1916478, by rfl⟩ : syracuseStep 5110609 = 3832957) B3832957
theorem B4545679 : Blo 1196415 4545679 := bstep (se 1 (by rfl) ⟨3409259, by rfl⟩ : syracuseStep 4545679 = 6818519) B6818519
theorem B38829455 : Blo 1196415 38829455 := bstep (se 1 (by rfl) ⟨29122091, by rfl⟩ : syracuseStep 38829455 = 58244183) B58244183
theorem B51805655 : Blo 1196415 51805655 := bstep (se 1 (by rfl) ⟨38854241, by rfl⟩ : syracuseStep 51805655 = 77708483) B77708483
theorem B5463533 : Blo 1196415 5463533 := bstep (se 3 (by rfl) ⟨1024412, by rfl⟩ : syracuseStep 5463533 = 2048825) B2048825
theorem B3030635 : Blo 1196415 3030635 := bstep (se 1 (by rfl) ⟨2272976, by rfl⟩ : syracuseStep 3030635 = 4545953) B4545953
theorem B11517713 : Blo 1196415 11517713 := bstep (se 2 (by rfl) ⟨4319142, by rfl⟩ : syracuseStep 11517713 = 8638285) B8638285
theorem B4038497 : Blo 1196415 4038497 := bstep (se 2 (by rfl) ⟨1514436, by rfl⟩ : syracuseStep 4038497 = 3028873) B3028873
theorem B12296033 : Blo 1196415 12296033 := bstep (se 2 (by rfl) ⟨4611012, by rfl⟩ : syracuseStep 12296033 = 9222025) B9222025
theorem B2695067 : Blo 1196415 2695067 := bstep (se 1 (by rfl) ⟨2021300, by rfl⟩ : syracuseStep 2695067 = 4042601) B4042601
theorem B12288185 : Blo 1196415 12288185 := bstep (se 2 (by rfl) ⟨4608069, by rfl⟩ : syracuseStep 12288185 = 9216139) B9216139
theorem B1917191 : Blo 1196415 1917191 := bstep (se 1 (by rfl) ⟨1437893, by rfl⟩ : syracuseStep 1917191 = 2875787) B2875787
theorem B4858159 : Blo 1196415 4858159 := bstep (se 1 (by rfl) ⟨3643619, by rfl⟩ : syracuseStep 4858159 = 7287239) B7287239
theorem B4546955 : Blo 1196415 4546955 := bstep (se 1 (by rfl) ⟨3410216, by rfl⟩ : syracuseStep 4546955 = 6820433) B6820433
theorem B1196511 : Blo 1196415 1196511 := bstep (se 1 (by rfl) ⟨897383, by rfl⟩ : syracuseStep 1196511 = 1794767) B1794767
theorem B1196519 : Blo 1196415 1196519 := bstep (se 1 (by rfl) ⟨897389, by rfl⟩ : syracuseStep 1196519 = 1794779) B1794779
theorem B5833223 : Blo 1196415 5833223 := bstep (se 1 (by rfl) ⟨4374917, by rfl⟩ : syracuseStep 5833223 = 8749835) B8749835
theorem B17261171 : Blo 1196415 17261171 := bstep (se 1 (by rfl) ⟨12945878, by rfl⟩ : syracuseStep 17261171 = 25891757) B25891757
theorem B24560273 : Blo 1196415 24560273 := bstep (se 2 (by rfl) ⟨9210102, by rfl⟩ : syracuseStep 24560273 = 18420205) B18420205
theorem B1794719 : Blo 1196415 1794719 := bstep (se 1 (by rfl) ⟨1346039, by rfl⟩ : syracuseStep 1794719 = 2692079) B2692079
theorem B1196795 : Blo 1196415 1196795 := bstep (se 1 (by rfl) ⟨897596, by rfl⟩ : syracuseStep 1196795 = 1795193) B1795193
theorem B3457799 : Blo 1196415 3457799 := bstep (se 1 (by rfl) ⟨2593349, by rfl⟩ : syracuseStep 3457799 = 5186699) B5186699
theorem B3031931 : Blo 1196415 3031931 := bstep (se 1 (by rfl) ⟨2273948, by rfl⟩ : syracuseStep 3031931 = 4547897) B4547897
theorem B9094031 : Blo 1196415 9094031 := bstep (se 1 (by rfl) ⟨6820523, by rfl⟩ : syracuseStep 9094031 = 13641047) B13641047
theorem B1795055 : Blo 1196415 1795055 := bstep (se 1 (by rfl) ⟨1346291, by rfl⟩ : syracuseStep 1795055 = 2692583) B2692583
theorem B1795163 : Blo 1196415 1795163 := bstep (se 1 (by rfl) ⟨1346372, by rfl⟩ : syracuseStep 1795163 = 2692745) B2692745
theorem B3073115 : Blo 1196415 3073115 := bstep (se 1 (by rfl) ⟨2304836, by rfl⟩ : syracuseStep 3073115 = 4609673) B4609673
theorem B1516639 : Blo 1196415 1516639 := bstep (se 1 (by rfl) ⟨1137479, by rfl⟩ : syracuseStep 1516639 = 2274959) B2274959
theorem B1795175 : Blo 1196415 1795175 := bstep (se 1 (by rfl) ⟨1346381, by rfl⟩ : syracuseStep 1795175 = 2692763) B2692763
theorem B34620527 : Blo 1196415 34620527 := bstep (se 1 (by rfl) ⟨25965395, by rfl⟩ : syracuseStep 34620527 = 51930791) B51930791
theorem B6145163 : Blo 1196415 6145163 := bstep (se 1 (by rfl) ⟨4608872, by rfl⟩ : syracuseStep 6145163 = 9217745) B9217745
theorem B3032275 : Blo 1196415 3032275 := bstep (se 1 (by rfl) ⟨2274206, by rfl⟩ : syracuseStep 3032275 = 4548413) B4548413
theorem B1795307 : Blo 1196415 1795307 := bstep (se 1 (by rfl) ⟨1346480, by rfl⟩ : syracuseStep 1795307 = 2692961) B2692961
theorem B1197375 : Blo 1196415 1197375 := bstep (se 1 (by rfl) ⟨898031, by rfl⟩ : syracuseStep 1197375 = 1796063) B1796063
theorem B1197383 : Blo 1196415 1197383 := bstep (se 1 (by rfl) ⟨898037, by rfl⟩ : syracuseStep 1197383 = 1796075) B1796075
theorem B3409249 : Blo 1196415 3409249 := bstep (se 2 (by rfl) ⟨1278468, by rfl⟩ : syracuseStep 3409249 = 2556937) B2556937
theorem B1197415 : Blo 1196415 1197415 := bstep (se 1 (by rfl) ⟨898061, by rfl⟩ : syracuseStep 1197415 = 1796123) B1796123
theorem B1795439 : Blo 1196415 1795439 := bstep (se 1 (by rfl) ⟨1346579, by rfl⟩ : syracuseStep 1795439 = 2693159) B2693159
theorem B1795559 : Blo 1196415 1795559 := bstep (se 1 (by rfl) ⟨1346669, by rfl⟩ : syracuseStep 1795559 = 2693339) B2693339
theorem B1197659 : Blo 1196415 1197659 := bstep (se 1 (by rfl) ⟨898244, by rfl⟩ : syracuseStep 1197659 = 1796489) B1796489
theorem B1795691 : Blo 1196415 1795691 := bstep (se 1 (by rfl) ⟨1346768, by rfl⟩ : syracuseStep 1795691 = 2693537) B2693537
theorem B58304123 : Blo 1196415 58304123 := bstep (se 1 (by rfl) ⟨43728092, by rfl⟩ : syracuseStep 58304123 = 87456185) B87456185
theorem B1795739 : Blo 1196415 1795739 := bstep (se 1 (by rfl) ⟨1346804, by rfl⟩ : syracuseStep 1795739 = 2693609) B2693609
theorem B6473479 : Blo 1196415 6473479 := bstep (se 1 (by rfl) ⟨4855109, by rfl⟩ : syracuseStep 6473479 = 9710219) B9710219
theorem B1795961 : Blo 1196415 1795961 := bstep (se 2 (by rfl) ⟨673485, by rfl⟩ : syracuseStep 1795961 = 1346971) B1346971
theorem B6227837 : Blo 1196415 6227837 := bstep (se 3 (by rfl) ⟨1167719, by rfl⟩ : syracuseStep 6227837 = 2335439) B2335439
theorem B1705963 : Blo 1196415 1705963 := bstep (se 1 (by rfl) ⟨1279472, by rfl⟩ : syracuseStep 1705963 = 2558945) B2558945
theorem B3278971 : Blo 1196415 3278971 := bstep (se 1 (by rfl) ⟨2459228, by rfl⟩ : syracuseStep 3278971 = 4918457) B4918457
theorem B1198287 : Blo 1196415 1198287 := bstep (se 1 (by rfl) ⟨898715, by rfl⟩ : syracuseStep 1198287 = 1797431) B1797431
theorem B7669991 : Blo 1196415 7669991 := bstep (se 1 (by rfl) ⟨5752493, by rfl⟩ : syracuseStep 7669991 = 11504987) B11504987
theorem B3410171 : Blo 1196415 3410171 := bstep (se 1 (by rfl) ⟨2557628, by rfl⟩ : syracuseStep 3410171 = 5115257) B5115257
theorem B1198399 : Blo 1196415 1198399 := bstep (se 1 (by rfl) ⟨898799, by rfl⟩ : syracuseStep 1198399 = 1797599) B1797599
theorem B7678475 : Blo 1196415 7678475 := bstep (se 1 (by rfl) ⟨5758856, by rfl⟩ : syracuseStep 7678475 = 11517713) B11517713
theorem B1796711 : Blo 1196415 1796711 := bstep (se 1 (by rfl) ⟨1347533, by rfl⟩ : syracuseStep 1796711 = 2695067) B2695067
theorem B6064793 : Blo 1196415 6064793 := bstep (se 2 (by rfl) ⟨2274297, by rfl⟩ : syracuseStep 6064793 = 4548595) B4548595
theorem B1346215 : Blo 1196415 1346215 := bstep (se 1 (by rfl) ⟨1009661, by rfl⟩ : syracuseStep 1346215 = 2019323) B2019323
theorem B1346287 : Blo 1196415 1346287 := bstep (se 1 (by rfl) ⟨1009715, by rfl⟩ : syracuseStep 1346287 = 2019431) B2019431
theorem B3238643 : Blo 1196415 3238643 := bstep (se 1 (by rfl) ⟨2428982, by rfl⟩ : syracuseStep 3238643 = 4857965) B4857965
theorem B202181453 : Blo 1196415 202181453 := bstep (se 3 (by rfl) ⟨37909022, by rfl⟩ : syracuseStep 202181453 = 75818045) B75818045
theorem B1796987 : Blo 1196415 1796987 := bstep (se 1 (by rfl) ⟨1347740, by rfl⟩ : syracuseStep 1796987 = 2695481) B2695481
theorem B14568439 : Blo 1196415 14568439 := bstep (se 1 (by rfl) ⟨10926329, by rfl⟩ : syracuseStep 14568439 = 21852659) B21852659
theorem B1797257 : Blo 1196415 1797257 := bstep (se 2 (by rfl) ⟨673971, by rfl⟩ : syracuseStep 1797257 = 1347943) B1347943
theorem B1797311 : Blo 1196415 1797311 := bstep (se 1 (by rfl) ⟨1347983, by rfl⟩ : syracuseStep 1797311 = 2695967) B2695967
theorem B9088199 : Blo 1196415 9088199 := bstep (se 1 (by rfl) ⟨6816149, by rfl⟩ : syracuseStep 9088199 = 13632299) B13632299
theorem B1346791 : Blo 1196415 1346791 := bstep (se 1 (by rfl) ⟨1010093, by rfl⟩ : syracuseStep 1346791 = 2020187) B2020187
theorem B3411197 : Blo 1196415 3411197 := bstep (se 3 (by rfl) ⟨639599, by rfl⟩ : syracuseStep 3411197 = 1279199) B1279199
theorem B13643963 : Blo 1196415 13643963 := bstep (se 1 (by rfl) ⟨10232972, by rfl⟩ : syracuseStep 13643963 = 20465945) B20465945
theorem B46018853 : Blo 1196415 46018853 := bstep (se 4 (by rfl) ⟨4314267, by rfl⟩ : syracuseStep 46018853 = 8628535) B8628535
theorem B2019775 : Blo 1196415 2019775 := bstep (se 1 (by rfl) ⟨1514831, by rfl⟩ : syracuseStep 2019775 = 3029663) B3029663
theorem B73740901 : Blo 1196415 73740901 := bstep (se 4 (by rfl) ⟨6913209, by rfl⟩ : syracuseStep 73740901 = 13826419) B13826419
theorem B49165217 : Blo 1196415 49165217 := bstep (se 2 (by rfl) ⟨18436956, by rfl⟩ : syracuseStep 49165217 = 36873913) B36873913
theorem B3642355 : Blo 1196415 3642355 := bstep (se 1 (by rfl) ⟨2731766, by rfl⟩ : syracuseStep 3642355 = 5463533) B5463533
theorem B2020423 : Blo 1196415 2020423 := bstep (se 1 (by rfl) ⟨1515317, by rfl⟩ : syracuseStep 2020423 = 3030635) B3030635
theorem B2692331 : Blo 1196415 2692331 := bstep (se 1 (by rfl) ⟨2019248, by rfl⟩ : syracuseStep 2692331 = 4038497) B4038497
theorem B8197355 : Blo 1196415 8197355 := bstep (se 1 (by rfl) ⟨6148016, by rfl⟩ : syracuseStep 8197355 = 12296033) B12296033
theorem B3028499 : Blo 1196415 3028499 := bstep (se 1 (by rfl) ⟨2271374, by rfl⟩ : syracuseStep 3028499 = 4542749) B4542749
theorem B4044383 : Blo 1196415 4044383 := bstep (se 1 (by rfl) ⟨3033287, by rfl⟩ : syracuseStep 4044383 = 6066575) B6066575
theorem B5756663 : Blo 1196415 5756663 := bstep (se 1 (by rfl) ⟨4317497, by rfl⟩ : syracuseStep 5756663 = 8634995) B8634995
theorem B2021159 : Blo 1196415 2021159 := bstep (se 1 (by rfl) ⟨1515869, by rfl⟩ : syracuseStep 2021159 = 3031739) B3031739
theorem B2692943 : Blo 1196415 2692943 := bstep (se 1 (by rfl) ⟨2019707, by rfl⟩ : syracuseStep 2692943 = 4039415) B4039415
theorem B5118025 : Blo 1196415 5118025 := bstep (se 2 (by rfl) ⟨1919259, by rfl⟩ : syracuseStep 5118025 = 3838519) B3838519
theorem B2693231 : Blo 1196415 2693231 := bstep (se 1 (by rfl) ⟨2019923, by rfl⟩ : syracuseStep 2693231 = 4039847) B4039847
theorem B2021503 : Blo 1196415 2021503 := bstep (se 1 (by rfl) ⟨1516127, by rfl⟩ : syracuseStep 2021503 = 3032255) B3032255
theorem B2693303 : Blo 1196415 2693303 := bstep (se 1 (by rfl) ⟨2019977, by rfl⟩ : syracuseStep 2693303 = 4039955) B4039955
theorem B6814145 : Blo 1196415 6814145 := bstep (se 2 (by rfl) ⟨2555304, by rfl⟩ : syracuseStep 6814145 = 5110609) B5110609
theorem B2693663 : Blo 1196415 2693663 := bstep (se 1 (by rfl) ⟨2020247, by rfl⟩ : syracuseStep 2693663 = 4040495) B4040495
theorem B18422417 : Blo 1196415 18422417 := bstep (se 2 (by rfl) ⟨6908406, by rfl⟩ : syracuseStep 18422417 = 13816813) B13816813
theorem B8632979 : Blo 1196415 8632979 := bstep (se 1 (by rfl) ⟨6474734, by rfl⟩ : syracuseStep 8632979 = 12949469) B12949469
theorem B6060905 : Blo 1196415 6060905 := bstep (se 2 (by rfl) ⟨2272839, by rfl⟩ : syracuseStep 6060905 = 4545679) B4545679
theorem B1457087 : Blo 1196415 1457087 := bstep (se 1 (by rfl) ⟨1092815, by rfl⟩ : syracuseStep 1457087 = 2185631) B2185631
theorem B5758087 : Blo 1196415 5758087 := bstep (se 1 (by rfl) ⟨4318565, by rfl⟩ : syracuseStep 5758087 = 8637131) B8637131
theorem B73776365 : Blo 1196415 73776365 := bstep (se 3 (by rfl) ⟨13833068, by rfl⟩ : syracuseStep 73776365 = 27666137) B27666137
theorem B59030957 : Blo 1196415 59030957 := bstep (se 3 (by rfl) ⟨11068304, by rfl⟩ : syracuseStep 59030957 = 22136609) B22136609
theorem B7003579 : Blo 1196415 7003579 := bstep (se 1 (by rfl) ⟨5252684, by rfl⟩ : syracuseStep 7003579 = 10505369) B10505369
theorem B25886303 : Blo 1196415 25886303 := bstep (se 1 (by rfl) ⟨19414727, by rfl⟩ : syracuseStep 25886303 = 38829455) B38829455
theorem B34537103 : Blo 1196415 34537103 := bstep (se 1 (by rfl) ⟨25902827, by rfl⟩ : syracuseStep 34537103 = 51805655) B51805655
theorem B126132161 : Blo 1196415 126132161 := bstep (se 2 (by rfl) ⟨47299560, by rfl⟩ : syracuseStep 126132161 = 94599121) B94599121
theorem B6824033 : Blo 1196415 6824033 := bstep (se 2 (by rfl) ⟨2559012, by rfl⟩ : syracuseStep 6824033 = 5118025) B5118025
theorem B8192123 : Blo 1196415 8192123 := bstep (se 1 (by rfl) ⟨6144092, by rfl⟩ : syracuseStep 8192123 = 12288185) B12288185
theorem B2695337 : Blo 1196415 2695337 := bstep (se 2 (by rfl) ⟨1010751, by rfl⟩ : syracuseStep 2695337 = 2021503) B2021503
theorem B1278127 : Blo 1196415 1278127 := bstep (se 1 (by rfl) ⟨958595, by rfl⟩ : syracuseStep 1278127 = 1917191) B1917191
theorem B30679235 : Blo 1196415 30679235 := bstep (se 1 (by rfl) ⟨23009426, by rfl⟩ : syracuseStep 30679235 = 46018853) B46018853
theorem B3031303 : Blo 1196415 3031303 := bstep (se 1 (by rfl) ⟨2273477, by rfl⟩ : syracuseStep 3031303 = 4546955) B4546955
theorem B1196479 : Blo 1196415 1196479 := bstep (se 1 (by rfl) ⟨897359, by rfl⟩ : syracuseStep 1196479 = 1794719) B1794719
theorem B6062687 : Blo 1196415 6062687 := bstep (se 1 (by rfl) ⟨4547015, by rfl⟩ : syracuseStep 6062687 = 9094031) B9094031
theorem B32776811 : Blo 1196415 32776811 := bstep (se 1 (by rfl) ⟨24582608, by rfl⟩ : syracuseStep 32776811 = 49165217) B49165217
theorem B1196703 : Blo 1196415 1196703 := bstep (se 1 (by rfl) ⟨897527, by rfl⟩ : syracuseStep 1196703 = 1795055) B1795055
theorem B1196775 : Blo 1196415 1196775 := bstep (se 1 (by rfl) ⟨897581, by rfl⟩ : syracuseStep 1196775 = 1795163) B1795163
theorem B2048743 : Blo 1196415 2048743 := bstep (se 1 (by rfl) ⟨1536557, by rfl⟩ : syracuseStep 2048743 = 3073115) B3073115
theorem B1196783 : Blo 1196415 1196783 := bstep (se 1 (by rfl) ⟨897587, by rfl⟩ : syracuseStep 1196783 = 1795175) B1795175
theorem B4096775 : Blo 1196415 4096775 := bstep (se 1 (by rfl) ⟨3072581, by rfl⟩ : syracuseStep 4096775 = 6145163) B6145163
theorem B98321201 : Blo 1196415 98321201 := bstep (se 2 (by rfl) ⟨36870450, by rfl⟩ : syracuseStep 98321201 = 73740901) B73740901
theorem B1794887 : Blo 1196415 1794887 := bstep (se 1 (by rfl) ⟨1346165, by rfl⟩ : syracuseStep 1794887 = 2692331) B2692331
theorem B1196871 : Blo 1196415 1196871 := bstep (se 1 (by rfl) ⟨897653, by rfl⟩ : syracuseStep 1196871 = 1795307) B1795307
theorem B5464903 : Blo 1196415 5464903 := bstep (se 1 (by rfl) ⟨4098677, by rfl⟩ : syracuseStep 5464903 = 8197355) B8197355
theorem B1794953 : Blo 1196415 1794953 := bstep (se 2 (by rfl) ⟨673107, by rfl⟩ : syracuseStep 1794953 = 1346215) B1346215
theorem B1196959 : Blo 1196415 1196959 := bstep (se 1 (by rfl) ⟨897719, by rfl⟩ : syracuseStep 1196959 = 1795439) B1795439
theorem B1795049 : Blo 1196415 1795049 := bstep (se 2 (by rfl) ⟨673143, by rfl⟩ : syracuseStep 1795049 = 1346287) B1346287
theorem B1197039 : Blo 1196415 1197039 := bstep (se 1 (by rfl) ⟨897779, by rfl⟩ : syracuseStep 1197039 = 1795559) B1795559
theorem B2696255 : Blo 1196415 2696255 := bstep (se 1 (by rfl) ⟨2022191, by rfl⟩ : syracuseStep 2696255 = 4044383) B4044383
theorem B1197127 : Blo 1196415 1197127 := bstep (se 1 (by rfl) ⟨897845, by rfl⟩ : syracuseStep 1197127 = 1795691) B1795691
theorem B1197159 : Blo 1196415 1197159 := bstep (se 1 (by rfl) ⟨897869, by rfl⟩ : syracuseStep 1197159 = 1795739) B1795739
theorem B1795295 : Blo 1196415 1795295 := bstep (se 1 (by rfl) ⟨1346471, by rfl⟩ : syracuseStep 1795295 = 2692943) B2692943
theorem B1197307 : Blo 1196415 1197307 := bstep (se 1 (by rfl) ⟨897980, by rfl⟩ : syracuseStep 1197307 = 1795961) B1795961
theorem B19424585 : Blo 1196415 19424585 := bstep (se 2 (by rfl) ⟨7284219, by rfl⟩ : syracuseStep 19424585 = 14568439) B14568439
theorem B1795487 : Blo 1196415 1795487 := bstep (se 1 (by rfl) ⟨1346615, by rfl⟩ : syracuseStep 1795487 = 2693231) B2693231
theorem B1795535 : Blo 1196415 1795535 := bstep (se 1 (by rfl) ⟨1346651, by rfl⟩ : syracuseStep 1795535 = 2693303) B2693303
theorem B5113327 : Blo 1196415 5113327 := bstep (se 1 (by rfl) ⟨3834995, by rfl⟩ : syracuseStep 5113327 = 7669991) B7669991
theorem B7677449 : Blo 1196415 7677449 := bstep (se 2 (by rfl) ⟨2879043, by rfl⟩ : syracuseStep 7677449 = 5758087) B5758087
theorem B1795721 : Blo 1196415 1795721 := bstep (se 2 (by rfl) ⟨673395, by rfl⟩ : syracuseStep 1795721 = 1346791) B1346791
theorem B1795775 : Blo 1196415 1795775 := bstep (se 1 (by rfl) ⟨1346831, by rfl⟩ : syracuseStep 1795775 = 2693663) B2693663
theorem B1197807 : Blo 1196415 1197807 := bstep (se 1 (by rfl) ⟨898355, by rfl⟩ : syracuseStep 1197807 = 1796711) B1796711
theorem B4040603 : Blo 1196415 4040603 := bstep (se 1 (by rfl) ⟨3030452, by rfl⟩ : syracuseStep 4040603 = 6060905) B6060905
theorem B1197991 : Blo 1196415 1197991 := bstep (se 1 (by rfl) ⟨898493, by rfl⟩ : syracuseStep 1197991 = 1796987) B1796987
theorem B8636381 : Blo 1196415 8636381 := bstep (se 3 (by rfl) ⟨1619321, by rfl⟩ : syracuseStep 8636381 = 3238643) B3238643
theorem B1198171 : Blo 1196415 1198171 := bstep (se 1 (by rfl) ⟨898628, by rfl⟩ : syracuseStep 1198171 = 1797257) B1797257
theorem B1198207 : Blo 1196415 1198207 := bstep (se 1 (by rfl) ⟨898655, by rfl⟩ : syracuseStep 1198207 = 1797311) B1797311
theorem B3885565 : Blo 1196415 3885565 := bstep (se 3 (by rfl) ⟨728543, by rfl⟩ : syracuseStep 3885565 = 1457087) B1457087
theorem B9095975 : Blo 1196415 9095975 := bstep (se 1 (by rfl) ⟨6821981, by rfl⟩ : syracuseStep 9095975 = 13643963) B13643963
theorem B2305199 : Blo 1196415 2305199 := bstep (se 1 (by rfl) ⟨1728899, by rfl⟩ : syracuseStep 2305199 = 3457799) B3457799
theorem B23080351 : Blo 1196415 23080351 := bstep (se 1 (by rfl) ⟨17310263, by rfl⟩ : syracuseStep 23080351 = 34620527) B34620527
theorem B2018999 : Blo 1196415 2018999 := bstep (se 1 (by rfl) ⟨1514249, by rfl⟩ : syracuseStep 2018999 = 3028499) B3028499
theorem B3837775 : Blo 1196415 3837775 := bstep (se 1 (by rfl) ⟨2878331, by rfl⟩ : syracuseStep 3837775 = 5756663) B5756663
theorem B1347439 : Blo 1196415 1347439 := bstep (se 1 (by rfl) ⟨1010579, by rfl⟩ : syracuseStep 1347439 = 2021159) B2021159
theorem B2273447 : Blo 1196415 2273447 := bstep (se 1 (by rfl) ⟨1705085, by rfl⟩ : syracuseStep 2273447 = 3410171) B3410171
theorem B4043033 : Blo 1196415 4043033 := bstep (se 2 (by rfl) ⟨1516137, by rfl⟩ : syracuseStep 4043033 = 3032275) B3032275
theorem B4542763 : Blo 1196415 4542763 := bstep (se 1 (by rfl) ⟨3407072, by rfl⟩ : syracuseStep 4542763 = 6814145) B6814145
theorem B5755319 : Blo 1196415 5755319 := bstep (se 1 (by rfl) ⟨4316489, by rfl⟩ : syracuseStep 5755319 = 8632979) B8632979
theorem B4043195 : Blo 1196415 4043195 := bstep (se 1 (by rfl) ⟨3032396, by rfl⟩ : syracuseStep 4043195 = 6064793) B6064793
theorem B134787635 : Blo 1196415 134787635 := bstep (se 1 (by rfl) ⟨101090726, by rfl⟩ : syracuseStep 134787635 = 202181453) B202181453
theorem B6058799 : Blo 1196415 6058799 := bstep (se 1 (by rfl) ⟨4544099, by rfl⟩ : syracuseStep 6058799 = 9088199) B9088199
theorem B2274131 : Blo 1196415 2274131 := bstep (se 1 (by rfl) ⟨1705598, by rfl⟩ : syracuseStep 2274131 = 3411197) B3411197
theorem B8631305 : Blo 1196415 8631305 := bstep (se 2 (by rfl) ⟨3236739, by rfl⟩ : syracuseStep 8631305 = 6473479) B6473479
theorem B17257535 : Blo 1196415 17257535 := bstep (se 1 (by rfl) ⟨12943151, by rfl⟩ : syracuseStep 17257535 = 25886303) B25886303
theorem B23024735 : Blo 1196415 23024735 := bstep (se 1 (by rfl) ⟨17268551, by rfl⟩ : syracuseStep 23024735 = 34537103) B34537103
theorem B336352429 : Blo 1196415 336352429 := bstep (se 3 (by rfl) ⟨63066080, by rfl⟩ : syracuseStep 336352429 = 126132161) B126132161
theorem B2274617 : Blo 1196415 2274617 := bstep (se 2 (by rfl) ⟨852981, by rfl⟩ : syracuseStep 2274617 = 1705963) B1705963
theorem B4371961 : Blo 1196415 4371961 := bstep (se 2 (by rfl) ⟨1639485, by rfl⟩ : syracuseStep 4371961 = 3278971) B3278971
theorem B3888815 : Blo 1196415 3888815 := bstep (se 1 (by rfl) ⟨2916611, by rfl⟩ : syracuseStep 3888815 = 5833223) B5833223
theorem B6477545 : Blo 1196415 6477545 := bstep (se 2 (by rfl) ⟨2429079, by rfl⟩ : syracuseStep 6477545 = 4858159) B4858159
theorem B11507447 : Blo 1196415 11507447 := bstep (se 1 (by rfl) ⟨8630585, by rfl⟩ : syracuseStep 11507447 = 17261171) B17261171
theorem B16373515 : Blo 1196415 16373515 := bstep (se 1 (by rfl) ⟨12280136, by rfl⟩ : syracuseStep 16373515 = 24560273) B24560273
theorem B2021287 : Blo 1196415 2021287 := bstep (se 1 (by rfl) ⟨1515965, by rfl⟩ : syracuseStep 2021287 = 3031931) B3031931
theorem B2693033 : Blo 1196415 2693033 := bstep (se 2 (by rfl) ⟨1009887, by rfl⟩ : syracuseStep 2693033 = 2019775) B2019775
theorem B38869415 : Blo 1196415 38869415 := bstep (se 1 (by rfl) ⟨29152061, by rfl⟩ : syracuseStep 38869415 = 58304123) B58304123
theorem B4151891 : Blo 1196415 4151891 := bstep (se 1 (by rfl) ⟨3113918, by rfl⟩ : syracuseStep 4151891 = 6227837) B6227837
theorem B4856473 : Blo 1196415 4856473 := bstep (se 2 (by rfl) ⟨1821177, by rfl⟩ : syracuseStep 4856473 = 3642355) B3642355
theorem B2693897 : Blo 1196415 2693897 := bstep (se 2 (by rfl) ⟨1010211, by rfl⟩ : syracuseStep 2693897 = 2020423) B2020423
theorem B2022185 : Blo 1196415 2022185 := bstep (se 2 (by rfl) ⟨758319, by rfl⟩ : syracuseStep 2022185 = 1516639) B1516639
theorem B5118983 : Blo 1196415 5118983 := bstep (se 1 (by rfl) ⟨3839237, by rfl⟩ : syracuseStep 5118983 = 7678475) B7678475
theorem B49126445 : Blo 1196415 49126445 := bstep (se 3 (by rfl) ⟨9211208, by rfl⟩ : syracuseStep 49126445 = 18422417) B18422417
theorem B4545665 : Blo 1196415 4545665 := bstep (se 2 (by rfl) ⟨1704624, by rfl⟩ : syracuseStep 4545665 = 3409249) B3409249
theorem B9338105 : Blo 1196415 9338105 := bstep (se 2 (by rfl) ⟨3501789, by rfl⟩ : syracuseStep 9338105 = 7003579) B7003579
theorem B49184243 : Blo 1196415 49184243 := bstep (se 1 (by rfl) ⟨36888182, by rfl⟩ : syracuseStep 49184243 = 73776365) B73776365
theorem B39353971 : Blo 1196415 39353971 := bstep (se 1 (by rfl) ⟨29515478, by rfl⟩ : syracuseStep 39353971 = 59030957) B59030957
theorem B2695355 : Blo 1196415 2695355 := bstep (se 1 (by rfl) ⟨2021516, by rfl⟩ : syracuseStep 2695355 = 4043033) B4043033
theorem B1704169 : Blo 1196415 1704169 := bstep (se 2 (by rfl) ⟨639063, by rfl⟩ : syracuseStep 1704169 = 1278127) B1278127
theorem B2695463 : Blo 1196415 2695463 := bstep (se 1 (by rfl) ⟨2021597, by rfl⟩ : syracuseStep 2695463 = 4043195) B4043195
theorem B89858423 : Blo 1196415 89858423 := bstep (se 1 (by rfl) ⟨67393817, by rfl⟩ : syracuseStep 89858423 = 134787635) B134787635
theorem B6062525 : Blo 1196415 6062525 := bstep (se 3 (by rfl) ⟨1136723, by rfl⟩ : syracuseStep 6062525 = 2273447) B2273447
theorem B4039199 : Blo 1196415 4039199 := bstep (se 1 (by rfl) ⟨3029399, by rfl⟩ : syracuseStep 4039199 = 6058799) B6058799
theorem B1196591 : Blo 1196415 1196591 := bstep (se 1 (by rfl) ⟨897443, by rfl⟩ : syracuseStep 1196591 = 1794887) B1794887
theorem B1516087 : Blo 1196415 1516087 := bstep (se 1 (by rfl) ⟨1137065, by rfl⟩ : syracuseStep 1516087 = 2274131) B2274131
theorem B1196635 : Blo 1196415 1196635 := bstep (se 1 (by rfl) ⟨897476, by rfl⟩ : syracuseStep 1196635 = 1794953) B1794953
theorem B1196699 : Blo 1196415 1196699 := bstep (se 1 (by rfl) ⟨897524, by rfl⟩ : syracuseStep 1196699 = 1795049) B1795049
theorem B1196863 : Blo 1196415 1196863 := bstep (se 1 (by rfl) ⟨897647, by rfl⟩ : syracuseStep 1196863 = 1795295) B1795295
theorem B1516411 : Blo 1196415 1516411 := bstep (se 1 (by rfl) ⟨1137308, by rfl⟩ : syracuseStep 1516411 = 2274617) B2274617
theorem B1196991 : Blo 1196415 1196991 := bstep (se 1 (by rfl) ⟨897743, by rfl⟩ : syracuseStep 1196991 = 1795487) B1795487
theorem B1197023 : Blo 1196415 1197023 := bstep (se 1 (by rfl) ⟨897767, by rfl⟩ : syracuseStep 1197023 = 1795535) B1795535
theorem B1197147 : Blo 1196415 1197147 := bstep (se 1 (by rfl) ⟨897860, by rfl⟩ : syracuseStep 1197147 = 1795721) B1795721
theorem B1197183 : Blo 1196415 1197183 := bstep (se 1 (by rfl) ⟨897887, by rfl⟩ : syracuseStep 1197183 = 1795775) B1795775
theorem B4318363 : Blo 1196415 4318363 := bstep (se 1 (by rfl) ⟨3238772, by rfl⟩ : syracuseStep 4318363 = 6477545) B6477545
theorem B1795355 : Blo 1196415 1795355 := bstep (se 1 (by rfl) ⟨1346516, by rfl⟩ : syracuseStep 1795355 = 2693033) B2693033
theorem B25912943 : Blo 1196415 25912943 := bstep (se 1 (by rfl) ⟨19434707, by rfl⟩ : syracuseStep 25912943 = 38869415) B38869415
theorem B1795931 : Blo 1196415 1795931 := bstep (se 1 (by rfl) ⟨1346948, by rfl⟩ : syracuseStep 1795931 = 2693897) B2693897
theorem B6063983 : Blo 1196415 6063983 := bstep (se 1 (by rfl) ⟨4547987, by rfl⟩ : syracuseStep 6063983 = 9095975) B9095975
theorem B6817769 : Blo 1196415 6817769 := bstep (se 2 (by rfl) ⟨2556663, by rfl⟩ : syracuseStep 6817769 = 5113327) B5113327
theorem B52471961 : Blo 1196415 52471961 := bstep (se 2 (by rfl) ⟨19676985, by rfl⟩ : syracuseStep 52471961 = 39353971) B39353971
theorem B1345999 : Blo 1196415 1345999 := bstep (se 1 (by rfl) ⟨1009499, by rfl⟩ : syracuseStep 1345999 = 2018999) B2018999
theorem B1796585 : Blo 1196415 1796585 := bstep (se 2 (by rfl) ⟨673719, by rfl⟩ : syracuseStep 1796585 = 1347439) B1347439
theorem B4549355 : Blo 1196415 4549355 := bstep (se 1 (by rfl) ⟨3412016, by rfl⟩ : syracuseStep 4549355 = 6824033) B6824033
theorem B1796891 : Blo 1196415 1796891 := bstep (se 1 (by rfl) ⟨1347668, by rfl⟩ : syracuseStep 1796891 = 2695337) B2695337
theorem B3836879 : Blo 1196415 3836879 := bstep (se 1 (by rfl) ⟨2877659, by rfl⟩ : syracuseStep 3836879 = 5755319) B5755319
theorem B4041737 : Blo 1196415 4041737 := bstep (se 2 (by rfl) ⟨1515651, by rfl⟩ : syracuseStep 4041737 = 3031303) B3031303
theorem B6057017 : Blo 1196415 6057017 := bstep (se 2 (by rfl) ⟨2271381, by rfl⟩ : syracuseStep 6057017 = 4542763) B4542763
theorem B4041791 : Blo 1196415 4041791 := bstep (se 1 (by rfl) ⟨3031343, by rfl⟩ : syracuseStep 4041791 = 6062687) B6062687
theorem B21851207 : Blo 1196415 21851207 := bstep (se 1 (by rfl) ⟨16388405, by rfl⟩ : syracuseStep 21851207 = 32776811) B32776811
theorem B6147197 : Blo 1196415 6147197 := bstep (se 3 (by rfl) ⟨1152599, by rfl⟩ : syracuseStep 6147197 = 2305199) B2305199
theorem B65547467 : Blo 1196415 65547467 := bstep (se 1 (by rfl) ⟨49160600, by rfl⟩ : syracuseStep 65547467 = 98321201) B98321201
theorem B5180753 : Blo 1196415 5180753 := bstep (se 2 (by rfl) ⟨1942782, by rfl⟩ : syracuseStep 5180753 = 3885565) B3885565
theorem B5754203 : Blo 1196415 5754203 := bstep (se 1 (by rfl) ⟨4315652, by rfl⟩ : syracuseStep 5754203 = 8631305) B8631305
theorem B11505023 : Blo 1196415 11505023 := bstep (se 1 (by rfl) ⟨8628767, by rfl⟩ : syracuseStep 11505023 = 17257535) B17257535
theorem B1797503 : Blo 1196415 1797503 := bstep (se 1 (by rfl) ⟨1348127, by rfl⟩ : syracuseStep 1797503 = 2696255) B2696255
theorem B6475297 : Blo 1196415 6475297 := bstep (se 2 (by rfl) ⟨2428236, by rfl⟩ : syracuseStep 6475297 = 4856473) B4856473
theorem B1793879621 : Blo 1196415 1793879621 := bstep (se 4 (by rfl) ⟨168176214, by rfl⟩ : syracuseStep 1793879621 = 336352429) B336352429
theorem B2731657 : Blo 1196415 2731657 := bstep (se 2 (by rfl) ⟨1024371, by rfl⟩ : syracuseStep 2731657 = 2048743) B2048743
theorem B7286537 : Blo 1196415 7286537 := bstep (se 2 (by rfl) ⟨2732451, by rfl⟩ : syracuseStep 7286537 = 5464903) B5464903
theorem B7671631 : Blo 1196415 7671631 := bstep (se 1 (by rfl) ⟨5753723, by rfl⟩ : syracuseStep 7671631 = 11507447) B11507447
theorem B41480693 : Blo 1196415 41480693 := bstep (se 5 (by rfl) ⟨1944407, by rfl⟩ : syracuseStep 41480693 = 3888815) B3888815
theorem B1348123 : Blo 1196415 1348123 := bstep (se 1 (by rfl) ⟨1011092, by rfl⟩ : syracuseStep 1348123 = 2022185) B2022185
theorem B30773801 : Blo 1196415 30773801 := bstep (se 2 (by rfl) ⟨11540175, by rfl⟩ : syracuseStep 30773801 = 23080351) B23080351
theorem B5829281 : Blo 1196415 5829281 := bstep (se 2 (by rfl) ⟨2185980, by rfl⟩ : syracuseStep 5829281 = 4371961) B4371961
theorem B3412655 : Blo 1196415 3412655 := bstep (se 1 (by rfl) ⟨2559491, by rfl⟩ : syracuseStep 3412655 = 5118983) B5118983
theorem B10924733 : Blo 1196415 10924733 := bstep (se 3 (by rfl) ⟨2048387, by rfl⟩ : syracuseStep 10924733 = 4096775) B4096775
theorem B32789495 : Blo 1196415 32789495 := bstep (se 1 (by rfl) ⟨24592121, by rfl⟩ : syracuseStep 32789495 = 49184243) B49184243
theorem B5117033 : Blo 1196415 5117033 := bstep (se 2 (by rfl) ⟨1918887, by rfl⟩ : syracuseStep 5117033 = 3837775) B3837775
theorem B5461415 : Blo 1196415 5461415 := bstep (se 1 (by rfl) ⟨4096061, by rfl⟩ : syracuseStep 5461415 = 8192123) B8192123
theorem B20452823 : Blo 1196415 20452823 := bstep (se 1 (by rfl) ⟨15339617, by rfl⟩ : syracuseStep 20452823 = 30679235) B30679235
theorem B15349823 : Blo 1196415 15349823 := bstep (se 1 (by rfl) ⟨11512367, by rfl⟩ : syracuseStep 15349823 = 23024735) B23024735
theorem B12949723 : Blo 1196415 12949723 := bstep (se 1 (by rfl) ⟨9712292, by rfl⟩ : syracuseStep 12949723 = 19424585) B19424585
theorem B5118299 : Blo 1196415 5118299 := bstep (se 1 (by rfl) ⟨3838724, by rfl⟩ : syracuseStep 5118299 = 7677449) B7677449
theorem B2693735 : Blo 1196415 2693735 := bstep (se 1 (by rfl) ⟨2020301, by rfl⟩ : syracuseStep 2693735 = 4040603) B4040603
theorem B5757587 : Blo 1196415 5757587 := bstep (se 1 (by rfl) ⟨4318190, by rfl⟩ : syracuseStep 5757587 = 8636381) B8636381
theorem B2767927 : Blo 1196415 2767927 := bstep (se 1 (by rfl) ⟨2075945, by rfl⟩ : syracuseStep 2767927 = 4151891) B4151891
theorem B32750963 : Blo 1196415 32750963 := bstep (se 1 (by rfl) ⟨24563222, by rfl⟩ : syracuseStep 32750963 = 49126445) B49126445
theorem B3030443 : Blo 1196415 3030443 := bstep (se 1 (by rfl) ⟨2272832, by rfl⟩ : syracuseStep 3030443 = 4545665) B4545665
theorem B6225403 : Blo 1196415 6225403 := bstep (se 1 (by rfl) ⟨4669052, by rfl⟩ : syracuseStep 6225403 = 9338105) B9338105
theorem B21831353 : Blo 1196415 21831353 := bstep (se 2 (by rfl) ⟨8186757, by rfl⟩ : syracuseStep 21831353 = 16373515) B16373515
theorem B2695049 : Blo 1196415 2695049 := bstep (se 2 (by rfl) ⟨1010643, by rfl⟩ : syracuseStep 2695049 = 2021287) B2021287
theorem B7283155 : Blo 1196415 7283155 := bstep (se 1 (by rfl) ⟨5462366, by rfl⟩ : syracuseStep 7283155 = 10924733) B10924733
theorem B1794665 : Blo 1196415 1794665 := bstep (se 2 (by rfl) ⟨672999, by rfl⟩ : syracuseStep 1794665 = 1345999) B1345999
theorem B1196903 : Blo 1196415 1196903 := bstep (se 1 (by rfl) ⟨897677, by rfl⟩ : syracuseStep 1196903 = 1795355) B1795355
theorem B1197287 : Blo 1196415 1197287 := bstep (se 1 (by rfl) ⟨897965, by rfl⟩ : syracuseStep 1197287 = 1795931) B1795931
theorem B10233215 : Blo 1196415 10233215 := bstep (se 1 (by rfl) ⟨7674911, by rfl⟩ : syracuseStep 10233215 = 15349823) B15349823
theorem B34981307 : Blo 1196415 34981307 := bstep (se 1 (by rfl) ⟨26235980, by rfl⟩ : syracuseStep 34981307 = 52471961) B52471961
theorem B1197723 : Blo 1196415 1197723 := bstep (se 1 (by rfl) ⟨898292, by rfl⟩ : syracuseStep 1197723 = 1796585) B1796585
theorem B1795823 : Blo 1196415 1795823 := bstep (se 1 (by rfl) ⟨1346867, by rfl⟩ : syracuseStep 1795823 = 2693735) B2693735
theorem B3032903 : Blo 1196415 3032903 := bstep (se 1 (by rfl) ⟨2274677, by rfl⟩ : syracuseStep 3032903 = 4549355) B4549355
theorem B1197927 : Blo 1196415 1197927 := bstep (se 1 (by rfl) ⟨898445, by rfl⟩ : syracuseStep 1197927 = 1796891) B1796891
theorem B2557919 : Blo 1196415 2557919 := bstep (se 1 (by rfl) ⟨1918439, by rfl⟩ : syracuseStep 2557919 = 3836879) B3836879
theorem B8300537 : Blo 1196415 8300537 := bstep (se 2 (by rfl) ⟨3112701, by rfl⟩ : syracuseStep 8300537 = 6225403) B6225403
theorem B14567471 : Blo 1196415 14567471 := bstep (se 1 (by rfl) ⟨10925603, by rfl⟩ : syracuseStep 14567471 = 21851207) B21851207
theorem B4098131 : Blo 1196415 4098131 := bstep (se 1 (by rfl) ⟨3073598, by rfl⟩ : syracuseStep 4098131 = 6147197) B6147197
theorem B43698311 : Blo 1196415 43698311 := bstep (se 1 (by rfl) ⟨32773733, by rfl⟩ : syracuseStep 43698311 = 65547467) B65547467
theorem B3836135 : Blo 1196415 3836135 := bstep (se 1 (by rfl) ⟨2877101, by rfl⟩ : syracuseStep 3836135 = 5754203) B5754203
theorem B21833975 : Blo 1196415 21833975 := bstep (se 1 (by rfl) ⟨16375481, by rfl⟩ : syracuseStep 21833975 = 32750963) B32750963
theorem B7670015 : Blo 1196415 7670015 := bstep (se 1 (by rfl) ⟨5752511, by rfl⟩ : syracuseStep 7670015 = 11505023) B11505023
theorem B1198335 : Blo 1196415 1198335 := bstep (se 1 (by rfl) ⟨898751, by rfl⟩ : syracuseStep 1198335 = 1797503) B1797503
theorem B1195919747 : Blo 1196415 1195919747 := bstep (se 1 (by rfl) ⟨896939810, by rfl⟩ : syracuseStep 1195919747 = 1793879621) B1793879621
theorem B1796699 : Blo 1196415 1796699 := bstep (se 1 (by rfl) ⟨1347524, by rfl⟩ : syracuseStep 1796699 = 2695049) B2695049
theorem B1796903 : Blo 1196415 1796903 := bstep (se 1 (by rfl) ⟨1347677, by rfl⟩ : syracuseStep 1796903 = 2695355) B2695355
theorem B1796975 : Blo 1196415 1796975 := bstep (se 1 (by rfl) ⟨1347731, by rfl⟩ : syracuseStep 1796975 = 2695463) B2695463
theorem B4041683 : Blo 1196415 4041683 := bstep (se 1 (by rfl) ⟨3031262, by rfl⟩ : syracuseStep 4041683 = 6062525) B6062525
theorem B2272225 : Blo 1196415 2272225 := bstep (se 2 (by rfl) ⟨852084, by rfl⟩ : syracuseStep 2272225 = 1704169) B1704169
theorem B3886187 : Blo 1196415 3886187 := bstep (se 1 (by rfl) ⟨2914640, by rfl⟩ : syracuseStep 3886187 = 5829281) B5829281
theorem B1797497 : Blo 1196415 1797497 := bstep (se 2 (by rfl) ⟨674061, by rfl⟩ : syracuseStep 1797497 = 1348123) B1348123
theorem B3640943 : Blo 1196415 3640943 := bstep (se 1 (by rfl) ⟨2730707, by rfl⟩ : syracuseStep 3640943 = 5461415) B5461415
theorem B13635215 : Blo 1196415 13635215 := bstep (se 1 (by rfl) ⟨10226411, by rfl⟩ : syracuseStep 13635215 = 20452823) B20452823
theorem B4042655 : Blo 1196415 4042655 := bstep (se 1 (by rfl) ⟨3031991, by rfl⟩ : syracuseStep 4042655 = 6063983) B6063983
theorem B3690569 : Blo 1196415 3690569 := bstep (se 2 (by rfl) ⟨1383963, by rfl⟩ : syracuseStep 3690569 = 2767927) B2767927
theorem B82063469 : Blo 1196415 82063469 := bstep (se 3 (by rfl) ⟨15386900, by rfl⟩ : syracuseStep 82063469 = 30773801) B30773801
theorem B3412199 : Blo 1196415 3412199 := bstep (se 1 (by rfl) ⟨2559149, by rfl⟩ : syracuseStep 3412199 = 5118299) B5118299
theorem B3838391 : Blo 1196415 3838391 := bstep (se 1 (by rfl) ⟨2878793, by rfl⟩ : syracuseStep 3838391 = 5757587) B5757587
theorem B3642209 : Blo 1196415 3642209 := bstep (se 2 (by rfl) ⟨1365828, by rfl⟩ : syracuseStep 3642209 = 2731657) B2731657
theorem B3453835 : Blo 1196415 3453835 := bstep (se 1 (by rfl) ⟨2590376, by rfl⟩ : syracuseStep 3453835 = 5180753) B5180753
theorem B2020295 : Blo 1196415 2020295 := bstep (se 1 (by rfl) ⟨1515221, by rfl⟩ : syracuseStep 2020295 = 3030443) B3030443
theorem B10228841 : Blo 1196415 10228841 := bstep (se 2 (by rfl) ⟨3835815, by rfl⟩ : syracuseStep 10228841 = 7671631) B7671631
theorem B14554235 : Blo 1196415 14554235 := bstep (se 1 (by rfl) ⟨10915676, by rfl⟩ : syracuseStep 14554235 = 21831353) B21831353
theorem B87438653 : Blo 1196415 87438653 := bstep (se 3 (by rfl) ⟨16394747, by rfl⟩ : syracuseStep 87438653 = 32789495) B32789495
theorem B13645421 : Blo 1196415 13645421 := bstep (se 3 (by rfl) ⟨2558516, by rfl⟩ : syracuseStep 13645421 = 5117033) B5117033
theorem B17266297 : Blo 1196415 17266297 := bstep (se 2 (by rfl) ⟨6474861, by rfl⟩ : syracuseStep 17266297 = 12949723) B12949723
theorem B27653795 : Blo 1196415 27653795 := bstep (se 1 (by rfl) ⟨20740346, by rfl⟩ : syracuseStep 27653795 = 41480693) B41480693
theorem B2692799 : Blo 1196415 2692799 := bstep (se 1 (by rfl) ⟨2019599, by rfl⟩ : syracuseStep 2692799 = 4039199) B4039199
theorem B2275103 : Blo 1196415 2275103 := bstep (se 1 (by rfl) ⟨1706327, by rfl⟩ : syracuseStep 2275103 = 3412655) B3412655
theorem B2021449 : Blo 1196415 2021449 := bstep (se 2 (by rfl) ⟨758043, by rfl⟩ : syracuseStep 2021449 = 1516087) B1516087
theorem B239622461 : Blo 1196415 239622461 := bstep (se 3 (by rfl) ⟨44929211, by rfl⟩ : syracuseStep 239622461 = 89858423) B89858423
theorem B17275295 : Blo 1196415 17275295 := bstep (se 1 (by rfl) ⟨12956471, by rfl⟩ : syracuseStep 17275295 = 25912943) B25912943
theorem B2021881 : Blo 1196415 2021881 := bstep (se 2 (by rfl) ⟨758205, by rfl⟩ : syracuseStep 2021881 = 1516411) B1516411
theorem B4545179 : Blo 1196415 4545179 := bstep (se 1 (by rfl) ⟨3408884, by rfl⟩ : syracuseStep 4545179 = 6817769) B6817769
theorem B5757817 : Blo 1196415 5757817 := bstep (se 2 (by rfl) ⟨2159181, by rfl⟩ : syracuseStep 5757817 = 4318363) B4318363
theorem B2694491 : Blo 1196415 2694491 := bstep (se 1 (by rfl) ⟨2020868, by rfl⟩ : syracuseStep 2694491 = 4041737) B4041737
theorem B19430765 : Blo 1196415 19430765 := bstep (se 3 (by rfl) ⟨3643268, by rfl⟩ : syracuseStep 19430765 = 7286537) B7286537
theorem B4038011 : Blo 1196415 4038011 := bstep (se 1 (by rfl) ⟨3028508, by rfl⟩ : syracuseStep 4038011 = 6057017) B6057017
theorem B2694527 : Blo 1196415 2694527 := bstep (se 1 (by rfl) ⟨2020895, by rfl⟩ : syracuseStep 2694527 = 4041791) B4041791
theorem B8633729 : Blo 1196415 8633729 := bstep (se 2 (by rfl) ⟨3237648, by rfl⟩ : syracuseStep 8633729 = 6475297) B6475297
theorem B2695265 : Blo 1196415 2695265 := bstep (se 2 (by rfl) ⟨1010724, by rfl⟩ : syracuseStep 2695265 = 2021449) B2021449
theorem B1196443 : Blo 1196415 1196443 := bstep (se 1 (by rfl) ⟨897332, by rfl⟩ : syracuseStep 1196443 = 1794665) B1794665
theorem B2695841 : Blo 1196415 2695841 := bstep (se 2 (by rfl) ⟨1010940, by rfl⟩ : syracuseStep 2695841 = 2021881) B2021881
theorem B41452661 : Blo 1196415 41452661 := bstep (se 5 (by rfl) ⟨1943093, by rfl⟩ : syracuseStep 41452661 = 3886187) B3886187
theorem B1795199 : Blo 1196415 1795199 := bstep (se 1 (by rfl) ⟨1346399, by rfl⟩ : syracuseStep 1795199 = 2692799) B2692799
theorem B1197215 : Blo 1196415 1197215 := bstep (se 1 (by rfl) ⟨897911, by rfl⟩ : syracuseStep 1197215 = 1795823) B1795823
theorem B7677089 : Blo 1196415 7677089 := bstep (se 2 (by rfl) ⟨2878908, by rfl⟩ : syracuseStep 7677089 = 5757817) B5757817
theorem B4605113 : Blo 1196415 4605113 := bstep (se 2 (by rfl) ⟨1726917, by rfl⟩ : syracuseStep 4605113 = 3453835) B3453835
theorem B1516735 : Blo 1196415 1516735 := bstep (se 1 (by rfl) ⟨1137551, by rfl⟩ : syracuseStep 1516735 = 2275103) B2275103
theorem B29132207 : Blo 1196415 29132207 := bstep (se 1 (by rfl) ⟨21849155, by rfl⟩ : syracuseStep 29132207 = 43698311) B43698311
theorem B2557423 : Blo 1196415 2557423 := bstep (se 1 (by rfl) ⟨1918067, by rfl⟩ : syracuseStep 2557423 = 3836135) B3836135
theorem B5113343 : Blo 1196415 5113343 := bstep (se 1 (by rfl) ⟨3835007, by rfl⟩ : syracuseStep 5113343 = 7670015) B7670015
theorem B797279831 : Blo 1196415 797279831 := bstep (se 1 (by rfl) ⟨597959873, by rfl⟩ : syracuseStep 797279831 = 1195919747) B1195919747
theorem B1197799 : Blo 1196415 1197799 := bstep (se 1 (by rfl) ⟨898349, by rfl⟩ : syracuseStep 1197799 = 1796699) B1796699
theorem B1197935 : Blo 1196415 1197935 := bstep (se 1 (by rfl) ⟨898451, by rfl⟩ : syracuseStep 1197935 = 1796903) B1796903
theorem B1197983 : Blo 1196415 1197983 := bstep (se 1 (by rfl) ⟨898487, by rfl⟩ : syracuseStep 1197983 = 1796975) B1796975
theorem B23021729 : Blo 1196415 23021729 := bstep (se 2 (by rfl) ⟨8633148, by rfl⟩ : syracuseStep 23021729 = 17266297) B17266297
theorem B1796327 : Blo 1196415 1796327 := bstep (se 1 (by rfl) ⟨1347245, by rfl⟩ : syracuseStep 1796327 = 2694491) B2694491
theorem B12953843 : Blo 1196415 12953843 := bstep (se 1 (by rfl) ⟨9715382, by rfl⟩ : syracuseStep 12953843 = 19430765) B19430765
theorem B1796351 : Blo 1196415 1796351 := bstep (se 1 (by rfl) ⟨1347263, by rfl⟩ : syracuseStep 1796351 = 2694527) B2694527
theorem B1198331 : Blo 1196415 1198331 := bstep (se 1 (by rfl) ⟨898748, by rfl⟩ : syracuseStep 1198331 = 1797497) B1797497
theorem B2427295 : Blo 1196415 2427295 := bstep (se 1 (by rfl) ⟨1820471, by rfl⟩ : syracuseStep 2427295 = 3640943) B3640943
theorem B2460379 : Blo 1196415 2460379 := bstep (se 1 (by rfl) ⟨1845284, by rfl⟩ : syracuseStep 2460379 = 3690569) B3690569
theorem B54708979 : Blo 1196415 54708979 := bstep (se 1 (by rfl) ⟨41031734, by rfl⟩ : syracuseStep 54708979 = 82063469) B82063469
theorem B2558927 : Blo 1196415 2558927 := bstep (se 1 (by rfl) ⟨1919195, by rfl⟩ : syracuseStep 2558927 = 3838391) B3838391
theorem B2428139 : Blo 1196415 2428139 := bstep (se 1 (by rfl) ⟨1821104, by rfl⟩ : syracuseStep 2428139 = 3642209) B3642209
theorem B9710873 : Blo 1196415 9710873 := bstep (se 2 (by rfl) ⟨3641577, by rfl⟩ : syracuseStep 9710873 = 7283155) B7283155
theorem B1346863 : Blo 1196415 1346863 := bstep (se 1 (by rfl) ⟨1010147, by rfl⟩ : syracuseStep 1346863 = 2020295) B2020295
theorem B58223933 : Blo 1196415 58223933 := bstep (se 3 (by rfl) ⟨10916987, by rfl⟩ : syracuseStep 58223933 = 21833975) B21833975
theorem B6819227 : Blo 1196415 6819227 := bstep (se 1 (by rfl) ⟨5114420, by rfl⟩ : syracuseStep 6819227 = 10228841) B10228841
theorem B9702823 : Blo 1196415 9702823 := bstep (se 1 (by rfl) ⟨7277117, by rfl⟩ : syracuseStep 9702823 = 14554235) B14554235
theorem B9096947 : Blo 1196415 9096947 := bstep (se 1 (by rfl) ⟨6822710, by rfl⟩ : syracuseStep 9096947 = 13645421) B13645421
theorem B18435863 : Blo 1196415 18435863 := bstep (se 1 (by rfl) ⟨13826897, by rfl⟩ : syracuseStep 18435863 = 27653795) B27653795
theorem B5533691 : Blo 1196415 5533691 := bstep (se 1 (by rfl) ⟨4150268, by rfl⟩ : syracuseStep 5533691 = 8300537) B8300537
theorem B9711647 : Blo 1196415 9711647 := bstep (se 1 (by rfl) ⟨7283735, by rfl⟩ : syracuseStep 9711647 = 14567471) B14567471
theorem B2732087 : Blo 1196415 2732087 := bstep (se 1 (by rfl) ⟨2049065, by rfl⟩ : syracuseStep 2732087 = 4098131) B4098131
theorem B159748307 : Blo 1196415 159748307 := bstep (se 1 (by rfl) ⟨119811230, by rfl⟩ : syracuseStep 159748307 = 239622461) B239622461
theorem B2692007 : Blo 1196415 2692007 := bstep (se 1 (by rfl) ⟨2019005, by rfl⟩ : syracuseStep 2692007 = 4038011) B4038011
theorem B5755819 : Blo 1196415 5755819 := bstep (se 1 (by rfl) ⟨4316864, by rfl⟩ : syracuseStep 5755819 = 8633729) B8633729
theorem B9090143 : Blo 1196415 9090143 := bstep (se 1 (by rfl) ⟨6817607, by rfl⟩ : syracuseStep 9090143 = 13635215) B13635215
theorem B6821117 : Blo 1196415 6821117 := bstep (se 3 (by rfl) ⟨1278959, by rfl⟩ : syracuseStep 6821117 = 2557919) B2557919
theorem B2274799 : Blo 1196415 2274799 := bstep (se 1 (by rfl) ⟨1706099, by rfl⟩ : syracuseStep 2274799 = 3412199) B3412199
theorem B58292435 : Blo 1196415 58292435 := bstep (se 1 (by rfl) ⟨43719326, by rfl⟩ : syracuseStep 58292435 = 87438653) B87438653
theorem B6822143 : Blo 1196415 6822143 := bstep (se 1 (by rfl) ⟨5116607, by rfl⟩ : syracuseStep 6822143 = 10233215) B10233215
theorem B23320871 : Blo 1196415 23320871 := bstep (se 1 (by rfl) ⟨17490653, by rfl⟩ : syracuseStep 23320871 = 34981307) B34981307
theorem B2021935 : Blo 1196415 2021935 := bstep (se 1 (by rfl) ⟨1516451, by rfl⟩ : syracuseStep 2021935 = 3032903) B3032903
theorem B3029633 : Blo 1196415 3029633 := bstep (se 2 (by rfl) ⟨1136112, by rfl⟩ : syracuseStep 3029633 = 2272225) B2272225
theorem B11516863 : Blo 1196415 11516863 := bstep (se 1 (by rfl) ⟨8637647, by rfl⟩ : syracuseStep 11516863 = 17275295) B17275295
theorem B3030119 : Blo 1196415 3030119 := bstep (se 1 (by rfl) ⟨2272589, by rfl⟩ : syracuseStep 3030119 = 4545179) B4545179
theorem B2694455 : Blo 1196415 2694455 := bstep (se 1 (by rfl) ⟨2020841, by rfl⟩ : syracuseStep 2694455 = 4041683) B4041683
theorem B2695103 : Blo 1196415 2695103 := bstep (se 1 (by rfl) ⟨2021327, by rfl⟩ : syracuseStep 2695103 = 4042655) B4042655
theorem B3236393 : Blo 1196415 3236393 := bstep (se 2 (by rfl) ⟨1213647, by rfl⟩ : syracuseStep 3236393 = 2427295) B2427295
theorem B1794671 : Blo 1196415 1794671 := bstep (se 1 (by rfl) ⟨1346003, by rfl⟩ : syracuseStep 1794671 = 2692007) B2692007
theorem B2695913 : Blo 1196415 2695913 := bstep (se 2 (by rfl) ⟨1010967, by rfl⟩ : syracuseStep 2695913 = 2021935) B2021935
theorem B1196799 : Blo 1196415 1196799 := bstep (se 1 (by rfl) ⟨897599, by rfl⟩ : syracuseStep 1196799 = 1795199) B1795199
theorem B4547411 : Blo 1196415 4547411 := bstep (se 1 (by rfl) ⟨3410558, by rfl⟩ : syracuseStep 4547411 = 6821117) B6821117
theorem B3408895 : Blo 1196415 3408895 := bstep (se 1 (by rfl) ⟨2556671, by rfl⟩ : syracuseStep 3408895 = 5113343) B5113343
theorem B1197551 : Blo 1196415 1197551 := bstep (se 1 (by rfl) ⟨898163, by rfl⟩ : syracuseStep 1197551 = 1796327) B1796327
theorem B8635895 : Blo 1196415 8635895 := bstep (se 1 (by rfl) ⟨6476921, by rfl⟩ : syracuseStep 8635895 = 12953843) B12953843
theorem B1197567 : Blo 1196415 1197567 := bstep (se 1 (by rfl) ⟨898175, by rfl⟩ : syracuseStep 1197567 = 1796351) B1796351
theorem B4548095 : Blo 1196415 4548095 := bstep (se 1 (by rfl) ⟨3411071, by rfl⟩ : syracuseStep 4548095 = 6822143) B6822143
theorem B1795817 : Blo 1196415 1795817 := bstep (se 2 (by rfl) ⟨673431, by rfl⟩ : syracuseStep 1795817 = 1346863) B1346863
theorem B12937097 : Blo 1196415 12937097 := bstep (se 2 (by rfl) ⟨4851411, by rfl⟩ : syracuseStep 12937097 = 9702823) B9702823
theorem B1705951 : Blo 1196415 1705951 := bstep (se 1 (by rfl) ⟨1279463, by rfl⟩ : syracuseStep 1705951 = 2558927) B2558927
theorem B3033065 : Blo 1196415 3033065 := bstep (se 2 (by rfl) ⟨1137399, by rfl⟩ : syracuseStep 3033065 = 2274799) B2274799
theorem B6473915 : Blo 1196415 6473915 := bstep (se 1 (by rfl) ⟨4855436, by rfl⟩ : syracuseStep 6473915 = 9710873) B9710873
theorem B1796303 : Blo 1196415 1796303 := bstep (se 1 (by rfl) ⟨1347227, by rfl⟩ : syracuseStep 1796303 = 2694455) B2694455
theorem B38815955 : Blo 1196415 38815955 := bstep (se 1 (by rfl) ⟨29111966, by rfl⟩ : syracuseStep 38815955 = 58223933) B58223933
theorem B6064631 : Blo 1196415 6064631 := bstep (se 1 (by rfl) ⟨4548473, by rfl⟩ : syracuseStep 6064631 = 9096947) B9096947
theorem B12290575 : Blo 1196415 12290575 := bstep (se 1 (by rfl) ⟨9217931, by rfl⟩ : syracuseStep 12290575 = 18435863) B18435863
theorem B1796735 : Blo 1196415 1796735 := bstep (se 1 (by rfl) ⟨1347551, by rfl⟩ : syracuseStep 1796735 = 2695103) B2695103
theorem B14756509 : Blo 1196415 14756509 := bstep (se 3 (by rfl) ⟨2766845, by rfl⟩ : syracuseStep 14756509 = 5533691) B5533691
theorem B6474431 : Blo 1196415 6474431 := bstep (se 1 (by rfl) ⟨4855823, by rfl⟩ : syracuseStep 6474431 = 9711647) B9711647
theorem B1796843 : Blo 1196415 1796843 := bstep (se 1 (by rfl) ⟨1347632, by rfl⟩ : syracuseStep 1796843 = 2695265) B2695265
theorem B106498871 : Blo 1196415 106498871 := bstep (se 1 (by rfl) ⟨79874153, by rfl⟩ : syracuseStep 106498871 = 159748307) B159748307
theorem B7285565 : Blo 1196415 7285565 := bstep (se 3 (by rfl) ⟨1366043, by rfl⟩ : syracuseStep 7285565 = 2732087) B2732087
theorem B1797227 : Blo 1196415 1797227 := bstep (se 1 (by rfl) ⟨1347920, by rfl⟩ : syracuseStep 1797227 = 2695841) B2695841
theorem B27635107 : Blo 1196415 27635107 := bstep (se 1 (by rfl) ⟨20726330, by rfl⟩ : syracuseStep 27635107 = 41452661) B41452661
theorem B3280505 : Blo 1196415 3280505 := bstep (se 2 (by rfl) ⟨1230189, by rfl⟩ : syracuseStep 3280505 = 2460379) B2460379
theorem B72945305 : Blo 1196415 72945305 := bstep (se 2 (by rfl) ⟨27354489, by rfl⟩ : syracuseStep 72945305 = 54708979) B54708979
theorem B15355817 : Blo 1196415 15355817 := bstep (se 2 (by rfl) ⟨5758431, by rfl⟩ : syracuseStep 15355817 = 11516863) B11516863
theorem B15347819 : Blo 1196415 15347819 := bstep (se 1 (by rfl) ⟨11510864, by rfl⟩ : syracuseStep 15347819 = 23021729) B23021729
theorem B2019755 : Blo 1196415 2019755 := bstep (se 1 (by rfl) ⟨1514816, by rfl⟩ : syracuseStep 2019755 = 3029633) B3029633
theorem B2020079 : Blo 1196415 2020079 := bstep (se 1 (by rfl) ⟨1515059, by rfl⟩ : syracuseStep 2020079 = 3030119) B3030119
theorem B1618759 : Blo 1196415 1618759 := bstep (se 1 (by rfl) ⟨1214069, by rfl⟩ : syracuseStep 1618759 = 2428139) B2428139
theorem B6060095 : Blo 1196415 6060095 := bstep (se 1 (by rfl) ⟨4545071, by rfl⟩ : syracuseStep 6060095 = 9090143) B9090143
theorem B5118059 : Blo 1196415 5118059 := bstep (se 1 (by rfl) ⟨3838544, by rfl⟩ : syracuseStep 5118059 = 7677089) B7677089
theorem B3070075 : Blo 1196415 3070075 := bstep (se 1 (by rfl) ⟨2302556, by rfl⟩ : syracuseStep 3070075 = 4605113) B4605113
theorem B19421471 : Blo 1196415 19421471 := bstep (se 1 (by rfl) ⟨14566103, by rfl⟩ : syracuseStep 19421471 = 29132207) B29132207
theorem B531519887 : Blo 1196415 531519887 := bstep (se 1 (by rfl) ⟨398639915, by rfl⟩ : syracuseStep 531519887 = 797279831) B797279831
theorem B7674425 : Blo 1196415 7674425 := bstep (se 2 (by rfl) ⟨2877909, by rfl⟩ : syracuseStep 7674425 = 5755819) B5755819
theorem B38861623 : Blo 1196415 38861623 := bstep (se 1 (by rfl) ⟨29146217, by rfl⟩ : syracuseStep 38861623 = 58292435) B58292435
theorem B15547247 : Blo 1196415 15547247 := bstep (se 1 (by rfl) ⟨11660435, by rfl⟩ : syracuseStep 15547247 = 23320871) B23320871
theorem B2022313 : Blo 1196415 2022313 := bstep (se 2 (by rfl) ⟨758367, by rfl⟩ : syracuseStep 2022313 = 1516735) B1516735
theorem B4546151 : Blo 1196415 4546151 := bstep (se 1 (by rfl) ⟨3409613, by rfl⟩ : syracuseStep 4546151 = 6819227) B6819227
theorem B13639589 : Blo 1196415 13639589 := bstep (se 4 (by rfl) ⟨1278711, by rfl⟩ : syracuseStep 13639589 = 2557423) B2557423
theorem B10231879 : Blo 1196415 10231879 := bstep (se 1 (by rfl) ⟨7673909, by rfl⟩ : syracuseStep 10231879 = 15347819) B15347819
theorem B1196447 : Blo 1196415 1196447 := bstep (se 1 (by rfl) ⟨897335, by rfl⟩ : syracuseStep 1196447 = 1794671) B1794671
theorem B3031607 : Blo 1196415 3031607 := bstep (se 1 (by rfl) ⟨2273705, by rfl⟩ : syracuseStep 3031607 = 4547411) B4547411
theorem B51790589 : Blo 1196415 51790589 := bstep (se 3 (by rfl) ⟨9710735, by rfl⟩ : syracuseStep 51790589 = 19421471) B19421471
theorem B3032063 : Blo 1196415 3032063 := bstep (se 1 (by rfl) ⟨2274047, by rfl⟩ : syracuseStep 3032063 = 4548095) B4548095
theorem B51815497 : Blo 1196415 51815497 := bstep (se 2 (by rfl) ⟨19430811, by rfl⟩ : syracuseStep 51815497 = 38861623) B38861623
theorem B1197211 : Blo 1196415 1197211 := bstep (se 1 (by rfl) ⟨897908, by rfl⟩ : syracuseStep 1197211 = 1795817) B1795817
theorem B2696417 : Blo 1196415 2696417 := bstep (se 2 (by rfl) ⟨1011156, by rfl⟩ : syracuseStep 2696417 = 2022313) B2022313
theorem B4040063 : Blo 1196415 4040063 := bstep (se 1 (by rfl) ⟨3030047, by rfl⟩ : syracuseStep 4040063 = 6060095) B6060095
theorem B1197535 : Blo 1196415 1197535 := bstep (se 1 (by rfl) ⟨898151, by rfl⟩ : syracuseStep 1197535 = 1796303) B1796303
theorem B354346591 : Blo 1196415 354346591 := bstep (se 1 (by rfl) ⟨265759943, by rfl⟩ : syracuseStep 354346591 = 531519887) B531519887
theorem B1197823 : Blo 1196415 1197823 := bstep (se 1 (by rfl) ⟨898367, by rfl⟩ : syracuseStep 1197823 = 1796735) B1796735
theorem B1197895 : Blo 1196415 1197895 := bstep (se 1 (by rfl) ⟨898421, by rfl⟩ : syracuseStep 1197895 = 1796843) B1796843
theorem B10364831 : Blo 1196415 10364831 := bstep (se 1 (by rfl) ⟨7773623, by rfl⟩ : syracuseStep 10364831 = 15547247) B15547247
theorem B1198151 : Blo 1196415 1198151 := bstep (se 1 (by rfl) ⟨898613, by rfl⟩ : syracuseStep 1198151 = 1797227) B1797227
theorem B48630203 : Blo 1196415 48630203 := bstep (se 1 (by rfl) ⟨36472652, by rfl⟩ : syracuseStep 48630203 = 72945305) B72945305
theorem B1346503 : Blo 1196415 1346503 := bstep (se 1 (by rfl) ⟨1009877, by rfl⟩ : syracuseStep 1346503 = 2019755) B2019755
theorem B1797275 : Blo 1196415 1797275 := bstep (se 1 (by rfl) ⟨1347956, by rfl⟩ : syracuseStep 1797275 = 2695913) B2695913
theorem B1346719 : Blo 1196415 1346719 := bstep (se 1 (by rfl) ⟨1010039, by rfl⟩ : syracuseStep 1346719 = 2020079) B2020079
theorem B16387433 : Blo 1196415 16387433 := bstep (se 2 (by rfl) ⟨6145287, by rfl⟩ : syracuseStep 16387433 = 12290575) B12290575
theorem B2158345 : Blo 1196415 2158345 := bstep (se 2 (by rfl) ⟨809379, by rfl⟩ : syracuseStep 2158345 = 1618759) B1618759
theorem B3412039 : Blo 1196415 3412039 := bstep (se 1 (by rfl) ⟨2559029, by rfl⟩ : syracuseStep 3412039 = 5118059) B5118059
theorem B8630381 : Blo 1196415 8630381 := bstep (se 3 (by rfl) ⟨1618196, by rfl⟩ : syracuseStep 8630381 = 3236393) B3236393
theorem B4043087 : Blo 1196415 4043087 := bstep (se 1 (by rfl) ⟨3032315, by rfl⟩ : syracuseStep 4043087 = 6064631) B6064631
theorem B5116283 : Blo 1196415 5116283 := bstep (se 1 (by rfl) ⟨3837212, by rfl⟩ : syracuseStep 5116283 = 7674425) B7674425
theorem B17265149 : Blo 1196415 17265149 := bstep (se 3 (by rfl) ⟨3237215, by rfl⟩ : syracuseStep 17265149 = 6474431) B6474431
theorem B9098405 : Blo 1196415 9098405 := bstep (se 4 (by rfl) ⟨852975, by rfl⟩ : syracuseStep 9098405 = 1705951) B1705951
theorem B10237211 : Blo 1196415 10237211 := bstep (se 1 (by rfl) ⟨7677908, by rfl⟩ : syracuseStep 10237211 = 15355817) B15355817
theorem B4093433 : Blo 1196415 4093433 := bstep (se 2 (by rfl) ⟨1535037, by rfl⟩ : syracuseStep 4093433 = 3070075) B3070075
theorem B19675345 : Blo 1196415 19675345 := bstep (se 2 (by rfl) ⟨7378254, by rfl⟩ : syracuseStep 19675345 = 14756509) B14756509
theorem B5757263 : Blo 1196415 5757263 := bstep (se 1 (by rfl) ⟨4317947, by rfl⟩ : syracuseStep 5757263 = 8635895) B8635895
theorem B8624731 : Blo 1196415 8624731 := bstep (se 1 (by rfl) ⟨6468548, by rfl⟩ : syracuseStep 8624731 = 12937097) B12937097
theorem B2022043 : Blo 1196415 2022043 := bstep (se 1 (by rfl) ⟨1516532, by rfl⟩ : syracuseStep 2022043 = 3033065) B3033065
theorem B4545193 : Blo 1196415 4545193 := bstep (se 2 (by rfl) ⟨1704447, by rfl⟩ : syracuseStep 4545193 = 3408895) B3408895
theorem B4315943 : Blo 1196415 4315943 := bstep (se 1 (by rfl) ⟨3236957, by rfl⟩ : syracuseStep 4315943 = 6473915) B6473915
theorem B25877303 : Blo 1196415 25877303 := bstep (se 1 (by rfl) ⟨19407977, by rfl⟩ : syracuseStep 25877303 = 38815955) B38815955
theorem B8748013 : Blo 1196415 8748013 := bstep (se 3 (by rfl) ⟨1640252, by rfl⟩ : syracuseStep 8748013 = 3280505) B3280505
theorem B70999247 : Blo 1196415 70999247 := bstep (se 1 (by rfl) ⟨53249435, by rfl⟩ : syracuseStep 70999247 = 106498871) B106498871
theorem B4857043 : Blo 1196415 4857043 := bstep (se 1 (by rfl) ⟨3642782, by rfl⟩ : syracuseStep 4857043 = 7285565) B7285565
theorem B36846809 : Blo 1196415 36846809 := bstep (se 2 (by rfl) ⟨13817553, by rfl⟩ : syracuseStep 36846809 = 27635107) B27635107
theorem B3030767 : Blo 1196415 3030767 := bstep (se 1 (by rfl) ⟨2273075, by rfl⟩ : syracuseStep 3030767 = 4546151) B4546151
theorem B9093059 : Blo 1196415 9093059 := bstep (se 1 (by rfl) ⟨6819794, by rfl⟩ : syracuseStep 9093059 = 13639589) B13639589
theorem B2695391 : Blo 1196415 2695391 := bstep (se 1 (by rfl) ⟨2021543, by rfl⟩ : syracuseStep 2695391 = 4043087) B4043087
theorem B11510099 : Blo 1196415 11510099 := bstep (se 1 (by rfl) ⟨8632574, by rfl⟩ : syracuseStep 11510099 = 17265149) B17265149
theorem B6824807 : Blo 1196415 6824807 := bstep (se 1 (by rfl) ⟨5118605, by rfl⟩ : syracuseStep 6824807 = 10237211) B10237211
theorem B2696057 : Blo 1196415 2696057 := bstep (se 2 (by rfl) ⟨1011021, by rfl⟩ : syracuseStep 2696057 = 2022043) B2022043
theorem B2728955 : Blo 1196415 2728955 := bstep (se 1 (by rfl) ⟨2046716, by rfl⟩ : syracuseStep 2728955 = 4093433) B4093433
theorem B1795337 : Blo 1196415 1795337 := bstep (se 2 (by rfl) ⟨673251, by rfl⟩ : syracuseStep 1795337 = 1346503) B1346503
theorem B11511173 : Blo 1196415 11511173 := bstep (se 4 (by rfl) ⟨1079172, by rfl⟩ : syracuseStep 11511173 = 2158345) B2158345
theorem B1795625 : Blo 1196415 1795625 := bstep (se 2 (by rfl) ⟨673359, by rfl⟩ : syracuseStep 1795625 = 1346719) B1346719
theorem B2877295 : Blo 1196415 2877295 := bstep (se 1 (by rfl) ⟨2157971, by rfl⟩ : syracuseStep 2877295 = 4315943) B4315943
theorem B1198183 : Blo 1196415 1198183 := bstep (se 1 (by rfl) ⟨898637, by rfl⟩ : syracuseStep 1198183 = 1797275) B1797275
theorem B5753587 : Blo 1196415 5753587 := bstep (se 1 (by rfl) ⟨4315190, by rfl⟩ : syracuseStep 5753587 = 8630381) B8630381
theorem B13642505 : Blo 1196415 13642505 := bstep (se 2 (by rfl) ⟨5115939, by rfl⟩ : syracuseStep 13642505 = 10231879) B10231879
theorem B4549385 : Blo 1196415 4549385 := bstep (se 2 (by rfl) ⟨1706019, by rfl⟩ : syracuseStep 4549385 = 3412039) B3412039
theorem B3410855 : Blo 1196415 3410855 := bstep (se 1 (by rfl) ⟨2558141, by rfl⟩ : syracuseStep 3410855 = 5116283) B5116283
theorem B26233793 : Blo 1196415 26233793 := bstep (se 2 (by rfl) ⟨9837672, by rfl⟩ : syracuseStep 26233793 = 19675345) B19675345
theorem B6065603 : Blo 1196415 6065603 := bstep (se 1 (by rfl) ⟨4549202, by rfl⟩ : syracuseStep 6065603 = 9098405) B9098405
theorem B1797611 : Blo 1196415 1797611 := bstep (se 1 (by rfl) ⟨1348208, by rfl⟩ : syracuseStep 1797611 = 2696417) B2696417
theorem B6909887 : Blo 1196415 6909887 := bstep (se 1 (by rfl) ⟨5182415, by rfl⟩ : syracuseStep 6909887 = 10364831) B10364831
theorem B69087329 : Blo 1196415 69087329 := bstep (se 2 (by rfl) ⟨25907748, by rfl⟩ : syracuseStep 69087329 = 51815497) B51815497
theorem B3838175 : Blo 1196415 3838175 := bstep (se 1 (by rfl) ⟨2878631, by rfl⟩ : syracuseStep 3838175 = 5757263) B5757263
theorem B6476057 : Blo 1196415 6476057 := bstep (se 2 (by rfl) ⟨2428521, by rfl⟩ : syracuseStep 6476057 = 4857043) B4857043
theorem B32420135 : Blo 1196415 32420135 := bstep (se 1 (by rfl) ⟨24315101, by rfl⟩ : syracuseStep 32420135 = 48630203) B48630203
theorem B472462121 : Blo 1196415 472462121 := bstep (se 2 (by rfl) ⟨177173295, by rfl⟩ : syracuseStep 472462121 = 354346591) B354346591
theorem B24564539 : Blo 1196415 24564539 := bstep (se 1 (by rfl) ⟨18423404, by rfl⟩ : syracuseStep 24564539 = 36846809) B36846809
theorem B10924955 : Blo 1196415 10924955 := bstep (se 1 (by rfl) ⟨8193716, by rfl⟩ : syracuseStep 10924955 = 16387433) B16387433
theorem B2020511 : Blo 1196415 2020511 := bstep (se 1 (by rfl) ⟨1515383, by rfl⟩ : syracuseStep 2020511 = 3030767) B3030767
theorem B2021071 : Blo 1196415 2021071 := bstep (se 1 (by rfl) ⟨1515803, by rfl⟩ : syracuseStep 2021071 = 3031607) B3031607
theorem B34527059 : Blo 1196415 34527059 := bstep (se 1 (by rfl) ⟨25895294, by rfl⟩ : syracuseStep 34527059 = 51790589) B51790589
theorem B2021375 : Blo 1196415 2021375 := bstep (se 1 (by rfl) ⟨1516031, by rfl⟩ : syracuseStep 2021375 = 3032063) B3032063
theorem B11499641 : Blo 1196415 11499641 := bstep (se 2 (by rfl) ⟨4312365, by rfl⟩ : syracuseStep 11499641 = 8624731) B8624731
theorem B6060257 : Blo 1196415 6060257 := bstep (se 2 (by rfl) ⟨2272596, by rfl⟩ : syracuseStep 6060257 = 4545193) B4545193
theorem B2693375 : Blo 1196415 2693375 := bstep (se 1 (by rfl) ⟨2020031, by rfl⟩ : syracuseStep 2693375 = 4040063) B4040063
theorem B11664017 : Blo 1196415 11664017 := bstep (se 2 (by rfl) ⟨4374006, by rfl⟩ : syracuseStep 11664017 = 8748013) B8748013
theorem B17251535 : Blo 1196415 17251535 := bstep (se 1 (by rfl) ⟨12938651, by rfl⟩ : syracuseStep 17251535 = 25877303) B25877303
theorem B47332831 : Blo 1196415 47332831 := bstep (se 1 (by rfl) ⟨35499623, by rfl⟩ : syracuseStep 47332831 = 70999247) B70999247
theorem B6062039 : Blo 1196415 6062039 := bstep (se 1 (by rfl) ⟨4546529, by rfl⟩ : syracuseStep 6062039 = 9093059) B9093059
theorem B4317371 : Blo 1196415 4317371 := bstep (se 1 (by rfl) ⟨3238028, by rfl⟩ : syracuseStep 4317371 = 6476057) B6476057
theorem B314974747 : Blo 1196415 314974747 := bstep (se 1 (by rfl) ⟨236231060, by rfl⟩ : syracuseStep 314974747 = 472462121) B472462121
theorem B16376359 : Blo 1196415 16376359 := bstep (se 1 (by rfl) ⟨12282269, by rfl⟩ : syracuseStep 16376359 = 24564539) B24564539
theorem B7283303 : Blo 1196415 7283303 := bstep (se 1 (by rfl) ⟨5462477, by rfl⟩ : syracuseStep 7283303 = 10924955) B10924955
theorem B1196891 : Blo 1196415 1196891 := bstep (se 1 (by rfl) ⟨897668, by rfl⟩ : syracuseStep 1196891 = 1795337) B1795337
theorem B1197083 : Blo 1196415 1197083 := bstep (se 1 (by rfl) ⟨897812, by rfl⟩ : syracuseStep 1197083 = 1795625) B1795625
theorem B4040171 : Blo 1196415 4040171 := bstep (se 1 (by rfl) ⟨3030128, by rfl⟩ : syracuseStep 4040171 = 6060257) B6060257
theorem B1795583 : Blo 1196415 1795583 := bstep (se 1 (by rfl) ⟨1346687, by rfl⟩ : syracuseStep 1795583 = 2693375) B2693375
theorem B7776011 : Blo 1196415 7776011 := bstep (se 1 (by rfl) ⟨5832008, by rfl⟩ : syracuseStep 7776011 = 11664017) B11664017
theorem B9095003 : Blo 1196415 9095003 := bstep (se 1 (by rfl) ⟨6821252, by rfl⟩ : syracuseStep 9095003 = 13642505) B13642505
theorem B3032923 : Blo 1196415 3032923 := bstep (se 1 (by rfl) ⟨2274692, by rfl⟩ : syracuseStep 3032923 = 4549385) B4549385
theorem B1198407 : Blo 1196415 1198407 := bstep (se 1 (by rfl) ⟨898805, by rfl⟩ : syracuseStep 1198407 = 1797611) B1797611
theorem B3836393 : Blo 1196415 3836393 := bstep (se 2 (by rfl) ⟨1438647, by rfl⟩ : syracuseStep 3836393 = 2877295) B2877295
theorem B18426365 : Blo 1196415 18426365 := bstep (se 3 (by rfl) ⟨3454943, by rfl⟩ : syracuseStep 18426365 = 6909887) B6909887
theorem B4041359 : Blo 1196415 4041359 := bstep (se 1 (by rfl) ⟨3031019, by rfl⟩ : syracuseStep 4041359 = 6062039) B6062039
theorem B7277213 : Blo 1196415 7277213 := bstep (se 3 (by rfl) ⟨1364477, by rfl⟩ : syracuseStep 7277213 = 2728955) B2728955
theorem B46058219 : Blo 1196415 46058219 := bstep (se 1 (by rfl) ⟨34543664, by rfl⟩ : syracuseStep 46058219 = 69087329) B69087329
theorem B1796927 : Blo 1196415 1796927 := bstep (se 1 (by rfl) ⟨1347695, by rfl⟩ : syracuseStep 1796927 = 2695391) B2695391
theorem B2558783 : Blo 1196415 2558783 := bstep (se 1 (by rfl) ⟨1919087, by rfl⟩ : syracuseStep 2558783 = 3838175) B3838175
theorem B21613423 : Blo 1196415 21613423 := bstep (se 1 (by rfl) ⟨16210067, by rfl⟩ : syracuseStep 21613423 = 32420135) B32420135
theorem B4549871 : Blo 1196415 4549871 := bstep (se 1 (by rfl) ⟨3412403, by rfl⟩ : syracuseStep 4549871 = 6824807) B6824807
theorem B1797371 : Blo 1196415 1797371 := bstep (se 1 (by rfl) ⟨1348028, by rfl⟩ : syracuseStep 1797371 = 2696057) B2696057
theorem B1347007 : Blo 1196415 1347007 := bstep (se 1 (by rfl) ⟨1010255, by rfl⟩ : syracuseStep 1347007 = 2020511) B2020511
theorem B7671449 : Blo 1196415 7671449 := bstep (se 2 (by rfl) ⟨2876793, by rfl⟩ : syracuseStep 7671449 = 5753587) B5753587
theorem B1347583 : Blo 1196415 1347583 := bstep (se 1 (by rfl) ⟨1010687, by rfl⟩ : syracuseStep 1347583 = 2021375) B2021375
theorem B2273903 : Blo 1196415 2273903 := bstep (se 1 (by rfl) ⟨1705427, by rfl⟩ : syracuseStep 2273903 = 3410855) B3410855
theorem B4043735 : Blo 1196415 4043735 := bstep (se 1 (by rfl) ⟨3032801, by rfl⟩ : syracuseStep 4043735 = 6065603) B6065603
theorem B7673399 : Blo 1196415 7673399 := bstep (se 1 (by rfl) ⟨5755049, by rfl⟩ : syracuseStep 7673399 = 11510099) B11510099
theorem B7674115 : Blo 1196415 7674115 := bstep (se 1 (by rfl) ⟨5755586, by rfl⟩ : syracuseStep 7674115 = 11511173) B11511173
theorem B23018039 : Blo 1196415 23018039 := bstep (se 1 (by rfl) ⟨17263529, by rfl⟩ : syracuseStep 23018039 = 34527059) B34527059
theorem B7666427 : Blo 1196415 7666427 := bstep (se 1 (by rfl) ⟨5749820, by rfl⟩ : syracuseStep 7666427 = 11499641) B11499641
theorem B63110441 : Blo 1196415 63110441 := bstep (se 2 (by rfl) ⟨23666415, by rfl⟩ : syracuseStep 63110441 = 47332831) B47332831
theorem B17489195 : Blo 1196415 17489195 := bstep (se 1 (by rfl) ⟨13116896, by rfl⟩ : syracuseStep 17489195 = 26233793) B26233793
theorem B11501023 : Blo 1196415 11501023 := bstep (se 1 (by rfl) ⟨8625767, by rfl⟩ : syracuseStep 11501023 = 17251535) B17251535
theorem B2694761 : Blo 1196415 2694761 := bstep (se 2 (by rfl) ⟨1010535, by rfl⟩ : syracuseStep 2694761 = 2021071) B2021071
theorem B10232153 : Blo 1196415 10232153 := bstep (se 2 (by rfl) ⟨3837057, by rfl⟩ : syracuseStep 10232153 = 7674115) B7674115
theorem B1515935 : Blo 1196415 1515935 := bstep (se 1 (by rfl) ⟨1136951, by rfl⟩ : syracuseStep 1515935 = 2273903) B2273903
theorem B2695823 : Blo 1196415 2695823 := bstep (se 1 (by rfl) ⟨2021867, by rfl⟩ : syracuseStep 2695823 = 4043735) B4043735
theorem B1197055 : Blo 1196415 1197055 := bstep (se 1 (by rfl) ⟨897791, by rfl⟩ : syracuseStep 1197055 = 1795583) B1795583
theorem B6063335 : Blo 1196415 6063335 := bstep (se 1 (by rfl) ⟨4547501, by rfl⟩ : syracuseStep 6063335 = 9095003) B9095003
theorem B2557595 : Blo 1196415 2557595 := bstep (se 1 (by rfl) ⟨1918196, by rfl⟩ : syracuseStep 2557595 = 3836393) B3836393
theorem B15345359 : Blo 1196415 15345359 := bstep (se 1 (by rfl) ⟨11509019, by rfl⟩ : syracuseStep 15345359 = 23018039) B23018039
theorem B20457197 : Blo 1196415 20457197 := bstep (se 3 (by rfl) ⟨3835724, by rfl⟩ : syracuseStep 20457197 = 7671449) B7671449
theorem B30705479 : Blo 1196415 30705479 := bstep (se 1 (by rfl) ⟨23029109, by rfl⟩ : syracuseStep 30705479 = 46058219) B46058219
theorem B1197951 : Blo 1196415 1197951 := bstep (se 1 (by rfl) ⟨898463, by rfl⟩ : syracuseStep 1197951 = 1796927) B1796927
theorem B1705855 : Blo 1196415 1705855 := bstep (se 1 (by rfl) ⟨1279391, by rfl⟩ : syracuseStep 1705855 = 2558783) B2558783
theorem B1796009 : Blo 1196415 1796009 := bstep (se 2 (by rfl) ⟨673503, by rfl⟩ : syracuseStep 1796009 = 1347007) B1347007
theorem B3033247 : Blo 1196415 3033247 := bstep (se 1 (by rfl) ⟨2274935, by rfl⟩ : syracuseStep 3033247 = 4549871) B4549871
theorem B1198247 : Blo 1196415 1198247 := bstep (se 1 (by rfl) ⟨898685, by rfl⟩ : syracuseStep 1198247 = 1797371) B1797371
theorem B11659463 : Blo 1196415 11659463 := bstep (se 1 (by rfl) ⟨8744597, by rfl⟩ : syracuseStep 11659463 = 17489195) B17489195
theorem B1796507 : Blo 1196415 1796507 := bstep (se 1 (by rfl) ⟨1347380, by rfl⟩ : syracuseStep 1796507 = 2694761) B2694761
theorem B1796777 : Blo 1196415 1796777 := bstep (se 2 (by rfl) ⟨673791, by rfl⟩ : syracuseStep 1796777 = 1347583) B1347583
theorem B2878247 : Blo 1196415 2878247 := bstep (se 1 (by rfl) ⟨2158685, by rfl⟩ : syracuseStep 2878247 = 4317371) B4317371
theorem B419966329 : Blo 1196415 419966329 := bstep (se 2 (by rfl) ⟨157487373, by rfl⟩ : syracuseStep 419966329 = 314974747) B314974747
theorem B21835145 : Blo 1196415 21835145 := bstep (se 2 (by rfl) ⟨8188179, by rfl⟩ : syracuseStep 21835145 = 16376359) B16376359
theorem B5115599 : Blo 1196415 5115599 := bstep (se 1 (by rfl) ⟨3836699, by rfl⟩ : syracuseStep 5115599 = 7673399) B7673399
theorem B12284243 : Blo 1196415 12284243 := bstep (se 1 (by rfl) ⟨9213182, by rfl⟩ : syracuseStep 12284243 = 18426365) B18426365
theorem B4043897 : Blo 1196415 4043897 := bstep (se 2 (by rfl) ⟨1516461, by rfl⟩ : syracuseStep 4043897 = 3032923) B3032923
theorem B4855535 : Blo 1196415 4855535 := bstep (se 1 (by rfl) ⟨3641651, by rfl⟩ : syracuseStep 4855535 = 7283303) B7283303
theorem B2693447 : Blo 1196415 2693447 := bstep (se 1 (by rfl) ⟨2020085, by rfl⟩ : syracuseStep 2693447 = 4040171) B4040171
theorem B28817897 : Blo 1196415 28817897 := bstep (se 2 (by rfl) ⟨10806711, by rfl⟩ : syracuseStep 28817897 = 21613423) B21613423
theorem B5184007 : Blo 1196415 5184007 := bstep (se 1 (by rfl) ⟨3888005, by rfl⟩ : syracuseStep 5184007 = 7776011) B7776011
theorem B19405901 : Blo 1196415 19405901 := bstep (se 3 (by rfl) ⟨3638606, by rfl⟩ : syracuseStep 19405901 = 7277213) B7277213
theorem B2694239 : Blo 1196415 2694239 := bstep (se 1 (by rfl) ⟨2020679, by rfl⟩ : syracuseStep 2694239 = 4041359) B4041359
theorem B5110951 : Blo 1196415 5110951 := bstep (se 1 (by rfl) ⟨3833213, by rfl⟩ : syracuseStep 5110951 = 7666427) B7666427
theorem B15334697 : Blo 1196415 15334697 := bstep (se 2 (by rfl) ⟨5750511, by rfl⟩ : syracuseStep 15334697 = 11501023) B11501023
theorem B42073627 : Blo 1196415 42073627 := bstep (se 1 (by rfl) ⟨31555220, by rfl⟩ : syracuseStep 42073627 = 63110441) B63110441
theorem B27648037 : Blo 1196415 27648037 := bstep (se 4 (by rfl) ⟨2592003, by rfl⟩ : syracuseStep 27648037 = 5184007) B5184007
theorem B2695931 : Blo 1196415 2695931 := bstep (se 1 (by rfl) ⟨2021948, by rfl⟩ : syracuseStep 2695931 = 4043897) B4043897
theorem B1705063 : Blo 1196415 1705063 := bstep (se 1 (by rfl) ⟨1278797, by rfl⟩ : syracuseStep 1705063 = 2557595) B2557595
theorem B3237023 : Blo 1196415 3237023 := bstep (se 1 (by rfl) ⟨2427767, by rfl⟩ : syracuseStep 3237023 = 4855535) B4855535
theorem B1197339 : Blo 1196415 1197339 := bstep (se 1 (by rfl) ⟨898004, by rfl⟩ : syracuseStep 1197339 = 1796009) B1796009
theorem B1795631 : Blo 1196415 1795631 := bstep (se 1 (by rfl) ⟨1346723, by rfl⟩ : syracuseStep 1795631 = 2693447) B2693447
theorem B1197671 : Blo 1196415 1197671 := bstep (se 1 (by rfl) ⟨898253, by rfl⟩ : syracuseStep 1197671 = 1796507) B1796507
theorem B1197851 : Blo 1196415 1197851 := bstep (se 1 (by rfl) ⟨898388, by rfl⟩ : syracuseStep 1197851 = 1796777) B1796777
theorem B1918831 : Blo 1196415 1918831 := bstep (se 1 (by rfl) ⟨1439123, by rfl⟩ : syracuseStep 1918831 = 2878247) B2878247
theorem B12937267 : Blo 1196415 12937267 := bstep (se 1 (by rfl) ⟨9702950, by rfl⟩ : syracuseStep 12937267 = 19405901) B19405901
theorem B1796159 : Blo 1196415 1796159 := bstep (se 1 (by rfl) ⟨1347119, by rfl⟩ : syracuseStep 1796159 = 2694239) B2694239
theorem B3410399 : Blo 1196415 3410399 := bstep (se 1 (by rfl) ⟨2557799, by rfl⟩ : syracuseStep 3410399 = 5115599) B5115599
theorem B1797215 : Blo 1196415 1797215 := bstep (se 1 (by rfl) ⟨1347911, by rfl⟩ : syracuseStep 1797215 = 2695823) B2695823
theorem B4042223 : Blo 1196415 4042223 := bstep (se 1 (by rfl) ⟨3031667, by rfl⟩ : syracuseStep 4042223 = 6063335) B6063335
theorem B4042493 : Blo 1196415 4042493 := bstep (se 3 (by rfl) ⟨757967, by rfl⟩ : syracuseStep 4042493 = 1515935) B1515935
theorem B2274473 : Blo 1196415 2274473 := bstep (se 2 (by rfl) ⟨852927, by rfl⟩ : syracuseStep 2274473 = 1705855) B1705855
theorem B4044329 : Blo 1196415 4044329 := bstep (se 2 (by rfl) ⟨1516623, by rfl⟩ : syracuseStep 4044329 = 3033247) B3033247
theorem B8189495 : Blo 1196415 8189495 := bstep (se 1 (by rfl) ⟨6142121, by rfl⟩ : syracuseStep 8189495 = 12284243) B12284243
theorem B6821435 : Blo 1196415 6821435 := bstep (se 1 (by rfl) ⟨5116076, by rfl⟩ : syracuseStep 6821435 = 10232153) B10232153
theorem B10230239 : Blo 1196415 10230239 := bstep (se 1 (by rfl) ⟨7672679, by rfl⟩ : syracuseStep 10230239 = 15345359) B15345359
theorem B13638131 : Blo 1196415 13638131 := bstep (se 1 (by rfl) ⟨10228598, by rfl⟩ : syracuseStep 13638131 = 20457197) B20457197
theorem B20470319 : Blo 1196415 20470319 := bstep (se 1 (by rfl) ⟨15352739, by rfl⟩ : syracuseStep 20470319 = 30705479) B30705479
theorem B76847725 : Blo 1196415 76847725 := bstep (se 3 (by rfl) ⟨14408948, by rfl⟩ : syracuseStep 76847725 = 28817897) B28817897
theorem B7772975 : Blo 1196415 7772975 := bstep (se 1 (by rfl) ⟨5829731, by rfl⟩ : syracuseStep 7772975 = 11659463) B11659463
theorem B6814601 : Blo 1196415 6814601 := bstep (se 2 (by rfl) ⟨2555475, by rfl⟩ : syracuseStep 6814601 = 5110951) B5110951
theorem B559955105 : Blo 1196415 559955105 := bstep (se 2 (by rfl) ⟨209983164, by rfl⟩ : syracuseStep 559955105 = 419966329) B419966329
theorem B56098169 : Blo 1196415 56098169 := bstep (se 2 (by rfl) ⟨21036813, by rfl⟩ : syracuseStep 56098169 = 42073627) B42073627
theorem B10223131 : Blo 1196415 10223131 := bstep (se 1 (by rfl) ⟨7667348, by rfl⟩ : syracuseStep 10223131 = 15334697) B15334697
theorem B14556763 : Blo 1196415 14556763 := bstep (se 1 (by rfl) ⟨10917572, by rfl⟩ : syracuseStep 14556763 = 21835145) B21835145
theorem B147456197 : Blo 1196415 147456197 := bstep (se 4 (by rfl) ⟨13824018, by rfl⟩ : syracuseStep 147456197 = 27648037) B27648037
theorem B1516315 : Blo 1196415 1516315 := bstep (se 1 (by rfl) ⟨1137236, by rfl⟩ : syracuseStep 1516315 = 2274473) B2274473
theorem B2696219 : Blo 1196415 2696219 := bstep (se 1 (by rfl) ⟨2022164, by rfl⟩ : syracuseStep 2696219 = 4044329) B4044329
theorem B1197087 : Blo 1196415 1197087 := bstep (se 1 (by rfl) ⟨897815, by rfl⟩ : syracuseStep 1197087 = 1795631) B1795631
theorem B4547623 : Blo 1196415 4547623 := bstep (se 1 (by rfl) ⟨3410717, by rfl⟩ : syracuseStep 4547623 = 6821435) B6821435
theorem B1197439 : Blo 1196415 1197439 := bstep (se 1 (by rfl) ⟨898079, by rfl⟩ : syracuseStep 1197439 = 1796159) B1796159
theorem B1198143 : Blo 1196415 1198143 := bstep (se 1 (by rfl) ⟨898607, by rfl⟩ : syracuseStep 1198143 = 1797215) B1797215
theorem B373303403 : Blo 1196415 373303403 := bstep (se 1 (by rfl) ⟨279977552, by rfl⟩ : syracuseStep 373303403 = 559955105) B559955105
theorem B19409017 : Blo 1196415 19409017 := bstep (se 2 (by rfl) ⟨7278381, by rfl⟩ : syracuseStep 19409017 = 14556763) B14556763
theorem B37398779 : Blo 1196415 37398779 := bstep (se 1 (by rfl) ⟨28049084, by rfl⟩ : syracuseStep 37398779 = 56098169) B56098169
theorem B2558441 : Blo 1196415 2558441 := bstep (se 2 (by rfl) ⟨959415, by rfl⟩ : syracuseStep 2558441 = 1918831) B1918831
theorem B1797287 : Blo 1196415 1797287 := bstep (se 1 (by rfl) ⟨1347965, by rfl⟩ : syracuseStep 1797287 = 2695931) B2695931
theorem B2158015 : Blo 1196415 2158015 := bstep (se 1 (by rfl) ⟨1618511, by rfl⟩ : syracuseStep 2158015 = 3237023) B3237023
theorem B5459663 : Blo 1196415 5459663 := bstep (se 1 (by rfl) ⟨4094747, by rfl⟩ : syracuseStep 5459663 = 8189495) B8189495
theorem B2273417 : Blo 1196415 2273417 := bstep (se 2 (by rfl) ⟨852531, by rfl⟩ : syracuseStep 2273417 = 1705063) B1705063
theorem B6820159 : Blo 1196415 6820159 := bstep (se 1 (by rfl) ⟨5115119, by rfl⟩ : syracuseStep 6820159 = 10230239) B10230239
theorem B2273599 : Blo 1196415 2273599 := bstep (se 1 (by rfl) ⟨1705199, by rfl⟩ : syracuseStep 2273599 = 3410399) B3410399
theorem B5181983 : Blo 1196415 5181983 := bstep (se 1 (by rfl) ⟨3886487, by rfl⟩ : syracuseStep 5181983 = 7772975) B7772975
theorem B4543067 : Blo 1196415 4543067 := bstep (se 1 (by rfl) ⟨3407300, by rfl⟩ : syracuseStep 4543067 = 6814601) B6814601
theorem B17249689 : Blo 1196415 17249689 := bstep (se 2 (by rfl) ⟨6468633, by rfl⟩ : syracuseStep 17249689 = 12937267) B12937267
theorem B102463633 : Blo 1196415 102463633 := bstep (se 2 (by rfl) ⟨38423862, by rfl⟩ : syracuseStep 102463633 = 76847725) B76847725
theorem B9092087 : Blo 1196415 9092087 := bstep (se 1 (by rfl) ⟨6819065, by rfl⟩ : syracuseStep 9092087 = 13638131) B13638131
theorem B13646879 : Blo 1196415 13646879 := bstep (se 1 (by rfl) ⟨10235159, by rfl⟩ : syracuseStep 13646879 = 20470319) B20470319
theorem B13630841 : Blo 1196415 13630841 := bstep (se 2 (by rfl) ⟨5111565, by rfl⟩ : syracuseStep 13630841 = 10223131) B10223131
theorem B2694815 : Blo 1196415 2694815 := bstep (se 1 (by rfl) ⟨2021111, by rfl⟩ : syracuseStep 2694815 = 4042223) B4042223
theorem B2694995 : Blo 1196415 2694995 := bstep (se 1 (by rfl) ⟨2021246, by rfl⟩ : syracuseStep 2694995 = 4042493) B4042493
theorem B1515611 : Blo 1196415 1515611 := bstep (se 1 (by rfl) ⟨1136708, by rfl⟩ : syracuseStep 1515611 = 2273417) B2273417
theorem B98304131 : Blo 1196415 98304131 := bstep (se 1 (by rfl) ⟨73728098, by rfl⟩ : syracuseStep 98304131 = 147456197) B147456197
theorem B25878689 : Blo 1196415 25878689 := bstep (se 2 (by rfl) ⟨9704508, by rfl⟩ : syracuseStep 25878689 = 19409017) B19409017
theorem B136618177 : Blo 1196415 136618177 := bstep (se 2 (by rfl) ⟨51231816, by rfl⟩ : syracuseStep 136618177 = 102463633) B102463633
theorem B9093545 : Blo 1196415 9093545 := bstep (se 2 (by rfl) ⟨3410079, by rfl⟩ : syracuseStep 9093545 = 6820159) B6820159
theorem B3031465 : Blo 1196415 3031465 := bstep (se 2 (by rfl) ⟨1136799, by rfl⟩ : syracuseStep 3031465 = 2273599) B2273599
theorem B6063497 : Blo 1196415 6063497 := bstep (se 2 (by rfl) ⟨2273811, by rfl⟩ : syracuseStep 6063497 = 4547623) B4547623
theorem B1705627 : Blo 1196415 1705627 := bstep (se 1 (by rfl) ⟨1279220, by rfl⟩ : syracuseStep 1705627 = 2558441) B2558441
theorem B14559101 : Blo 1196415 14559101 := bstep (se 3 (by rfl) ⟨2729831, by rfl⟩ : syracuseStep 14559101 = 5459663) B5459663
theorem B2877353 : Blo 1196415 2877353 := bstep (se 2 (by rfl) ⟨1079007, by rfl⟩ : syracuseStep 2877353 = 2158015) B2158015
theorem B1198191 : Blo 1196415 1198191 := bstep (se 1 (by rfl) ⟨898643, by rfl⟩ : syracuseStep 1198191 = 1797287) B1797287
theorem B9087227 : Blo 1196415 9087227 := bstep (se 1 (by rfl) ⟨6815420, by rfl⟩ : syracuseStep 9087227 = 13630841) B13630841
theorem B1796543 : Blo 1196415 1796543 := bstep (se 1 (by rfl) ⟨1347407, by rfl⟩ : syracuseStep 1796543 = 2694815) B2694815
theorem B1796663 : Blo 1196415 1796663 := bstep (se 1 (by rfl) ⟨1347497, by rfl⟩ : syracuseStep 1796663 = 2694995) B2694995
theorem B1797479 : Blo 1196415 1797479 := bstep (se 1 (by rfl) ⟨1348109, by rfl⟩ : syracuseStep 1797479 = 2696219) B2696219
theorem B248868935 : Blo 1196415 248868935 := bstep (se 1 (by rfl) ⟨186651701, by rfl⟩ : syracuseStep 248868935 = 373303403) B373303403
theorem B24932519 : Blo 1196415 24932519 := bstep (se 1 (by rfl) ⟨18699389, by rfl⟩ : syracuseStep 24932519 = 37398779) B37398779
theorem B22999585 : Blo 1196415 22999585 := bstep (se 2 (by rfl) ⟨8624844, by rfl⟩ : syracuseStep 22999585 = 17249689) B17249689
theorem B9097919 : Blo 1196415 9097919 := bstep (se 1 (by rfl) ⟨6823439, by rfl⟩ : syracuseStep 9097919 = 13646879) B13646879
theorem B3454655 : Blo 1196415 3454655 := bstep (se 1 (by rfl) ⟨2590991, by rfl⟩ : syracuseStep 3454655 = 5181983) B5181983
theorem B3028711 : Blo 1196415 3028711 := bstep (se 1 (by rfl) ⟨2271533, by rfl⟩ : syracuseStep 3028711 = 4543067) B4543067
theorem B2021753 : Blo 1196415 2021753 := bstep (se 2 (by rfl) ⟨758157, by rfl⟩ : syracuseStep 2021753 = 1516315) B1516315
theorem B6061391 : Blo 1196415 6061391 := bstep (se 1 (by rfl) ⟨4546043, by rfl⟩ : syracuseStep 6061391 = 9092087) B9092087
theorem B165912623 : Blo 1196415 165912623 := bstep (se 1 (by rfl) ⟨124434467, by rfl⟩ : syracuseStep 165912623 = 248868935) B248868935
theorem B65536087 : Blo 1196415 65536087 := bstep (se 1 (by rfl) ⟨49152065, by rfl⟩ : syracuseStep 65536087 = 98304131) B98304131
theorem B17252459 : Blo 1196415 17252459 := bstep (se 1 (by rfl) ⟨12939344, by rfl⟩ : syracuseStep 17252459 = 25878689) B25878689
theorem B16621679 : Blo 1196415 16621679 := bstep (se 1 (by rfl) ⟨12466259, by rfl⟩ : syracuseStep 16621679 = 24932519) B24932519
theorem B182157569 : Blo 1196415 182157569 := bstep (se 2 (by rfl) ⟨68309088, by rfl⟩ : syracuseStep 182157569 = 136618177) B136618177
theorem B6062363 : Blo 1196415 6062363 := bstep (se 1 (by rfl) ⟨4546772, by rfl⟩ : syracuseStep 6062363 = 9093545) B9093545
theorem B1918235 : Blo 1196415 1918235 := bstep (se 1 (by rfl) ⟨1438676, by rfl⟩ : syracuseStep 1918235 = 2877353) B2877353
theorem B1197695 : Blo 1196415 1197695 := bstep (se 1 (by rfl) ⟨898271, by rfl⟩ : syracuseStep 1197695 = 1796543) B1796543
theorem B1197775 : Blo 1196415 1197775 := bstep (se 1 (by rfl) ⟨898331, by rfl⟩ : syracuseStep 1197775 = 1796663) B1796663
theorem B36849653 : Blo 1196415 36849653 := bstep (se 5 (by rfl) ⟨1727327, by rfl⟩ : syracuseStep 36849653 = 3454655) B3454655
theorem B4040927 : Blo 1196415 4040927 := bstep (se 1 (by rfl) ⟨3030695, by rfl⟩ : syracuseStep 4040927 = 6061391) B6061391
theorem B1198319 : Blo 1196415 1198319 := bstep (se 1 (by rfl) ⟨898739, by rfl⟩ : syracuseStep 1198319 = 1797479) B1797479
theorem B4041629 : Blo 1196415 4041629 := bstep (se 3 (by rfl) ⟨757805, by rfl⟩ : syracuseStep 4041629 = 1515611) B1515611
theorem B6065279 : Blo 1196415 6065279 := bstep (se 1 (by rfl) ⟨4548959, by rfl⟩ : syracuseStep 6065279 = 9097919) B9097919
theorem B4041953 : Blo 1196415 4041953 := bstep (se 2 (by rfl) ⟨1515732, by rfl⟩ : syracuseStep 4041953 = 3031465) B3031465
theorem B30666113 : Blo 1196415 30666113 := bstep (se 2 (by rfl) ⟨11499792, by rfl⟩ : syracuseStep 30666113 = 22999585) B22999585
theorem B4042331 : Blo 1196415 4042331 := bstep (se 1 (by rfl) ⟨3031748, by rfl⟩ : syracuseStep 4042331 = 6063497) B6063497
theorem B6058151 : Blo 1196415 6058151 := bstep (se 1 (by rfl) ⟨4543613, by rfl⟩ : syracuseStep 6058151 = 9087227) B9087227
theorem B1347835 : Blo 1196415 1347835 := bstep (se 1 (by rfl) ⟨1010876, by rfl⟩ : syracuseStep 1347835 = 2021753) B2021753
theorem B2274169 : Blo 1196415 2274169 := bstep (se 2 (by rfl) ⟨852813, by rfl⟩ : syracuseStep 2274169 = 1705627) B1705627
theorem B9706067 : Blo 1196415 9706067 := bstep (se 1 (by rfl) ⟨7279550, by rfl⟩ : syracuseStep 9706067 = 14559101) B14559101
theorem B4038281 : Blo 1196415 4038281 := bstep (se 2 (by rfl) ⟨1514355, by rfl⟩ : syracuseStep 4038281 = 3028711) B3028711
theorem B110608415 : Blo 1196415 110608415 := bstep (se 1 (by rfl) ⟨82956311, by rfl⟩ : syracuseStep 110608415 = 165912623) B165912623
theorem B11501639 : Blo 1196415 11501639 := bstep (se 1 (by rfl) ⟨8626229, by rfl⟩ : syracuseStep 11501639 = 17252459) B17252459
theorem B4038767 : Blo 1196415 4038767 := bstep (se 1 (by rfl) ⟨3029075, by rfl⟩ : syracuseStep 4038767 = 6058151) B6058151
theorem B121438379 : Blo 1196415 121438379 := bstep (se 1 (by rfl) ⟨91078784, by rfl⟩ : syracuseStep 121438379 = 182157569) B182157569
theorem B1278823 : Blo 1196415 1278823 := bstep (se 1 (by rfl) ⟨959117, by rfl⟩ : syracuseStep 1278823 = 1918235) B1918235
theorem B3032225 : Blo 1196415 3032225 := bstep (se 2 (by rfl) ⟨1137084, by rfl⟩ : syracuseStep 3032225 = 2274169) B2274169
theorem B4041575 : Blo 1196415 4041575 := bstep (se 1 (by rfl) ⟨3031181, by rfl⟩ : syracuseStep 4041575 = 6062363) B6062363
theorem B1797113 : Blo 1196415 1797113 := bstep (se 2 (by rfl) ⟨673917, by rfl⟩ : syracuseStep 1797113 = 1347835) B1347835
theorem B4043519 : Blo 1196415 4043519 := bstep (se 1 (by rfl) ⟨3032639, by rfl⟩ : syracuseStep 4043519 = 6065279) B6065279
theorem B20444075 : Blo 1196415 20444075 := bstep (se 1 (by rfl) ⟨15333056, by rfl⟩ : syracuseStep 20444075 = 30666113) B30666113
theorem B2692187 : Blo 1196415 2692187 := bstep (se 1 (by rfl) ⟨2019140, by rfl⟩ : syracuseStep 2692187 = 4038281) B4038281
theorem B11081119 : Blo 1196415 11081119 := bstep (se 1 (by rfl) ⟨8310839, by rfl⟩ : syracuseStep 11081119 = 16621679) B16621679
theorem B87381449 : Blo 1196415 87381449 := bstep (se 2 (by rfl) ⟨32768043, by rfl⟩ : syracuseStep 87381449 = 65536087) B65536087
theorem B24566435 : Blo 1196415 24566435 := bstep (se 1 (by rfl) ⟨18424826, by rfl⟩ : syracuseStep 24566435 = 36849653) B36849653
theorem B2693951 : Blo 1196415 2693951 := bstep (se 1 (by rfl) ⟨2020463, by rfl⟩ : syracuseStep 2693951 = 4040927) B4040927
theorem B6470711 : Blo 1196415 6470711 := bstep (se 1 (by rfl) ⟨4853033, by rfl⟩ : syracuseStep 6470711 = 9706067) B9706067
theorem B2694419 : Blo 1196415 2694419 := bstep (se 1 (by rfl) ⟨2020814, by rfl⟩ : syracuseStep 2694419 = 4041629) B4041629
theorem B2694635 : Blo 1196415 2694635 := bstep (se 1 (by rfl) ⟨2020976, by rfl⟩ : syracuseStep 2694635 = 4041953) B4041953
theorem B2694887 : Blo 1196415 2694887 := bstep (se 1 (by rfl) ⟨2021165, by rfl⟩ : syracuseStep 2694887 = 4042331) B4042331
theorem B7667759 : Blo 1196415 7667759 := bstep (se 1 (by rfl) ⟨5750819, by rfl⟩ : syracuseStep 7667759 = 11501639) B11501639
theorem B2695679 : Blo 1196415 2695679 := bstep (se 1 (by rfl) ⟨2021759, by rfl⟩ : syracuseStep 2695679 = 4043519) B4043519
theorem B1794791 : Blo 1196415 1794791 := bstep (se 1 (by rfl) ⟨1346093, by rfl⟩ : syracuseStep 1794791 = 2692187) B2692187
theorem B58254299 : Blo 1196415 58254299 := bstep (se 1 (by rfl) ⟨43690724, by rfl⟩ : syracuseStep 58254299 = 87381449) B87381449
theorem B1705097 : Blo 1196415 1705097 := bstep (se 2 (by rfl) ⟨639411, by rfl⟩ : syracuseStep 1705097 = 1278823) B1278823
theorem B16377623 : Blo 1196415 16377623 := bstep (se 1 (by rfl) ⟨12283217, by rfl⟩ : syracuseStep 16377623 = 24566435) B24566435
theorem B1795967 : Blo 1196415 1795967 := bstep (se 1 (by rfl) ⟨1346975, by rfl⟩ : syracuseStep 1795967 = 2693951) B2693951
theorem B1198075 : Blo 1196415 1198075 := bstep (se 1 (by rfl) ⟨898556, by rfl⟩ : syracuseStep 1198075 = 1797113) B1797113
theorem B1796279 : Blo 1196415 1796279 := bstep (se 1 (by rfl) ⟨1347209, by rfl⟩ : syracuseStep 1796279 = 2694419) B2694419
theorem B1796423 : Blo 1196415 1796423 := bstep (se 1 (by rfl) ⟨1347317, by rfl⟩ : syracuseStep 1796423 = 2694635) B2694635
theorem B1796591 : Blo 1196415 1796591 := bstep (se 1 (by rfl) ⟨1347443, by rfl⟩ : syracuseStep 1796591 = 2694887) B2694887
theorem B73738943 : Blo 1196415 73738943 := bstep (se 1 (by rfl) ⟨55304207, by rfl⟩ : syracuseStep 73738943 = 110608415) B110608415
theorem B14774825 : Blo 1196415 14774825 := bstep (se 2 (by rfl) ⟨5540559, by rfl⟩ : syracuseStep 14774825 = 11081119) B11081119
theorem B4313807 : Blo 1196415 4313807 := bstep (se 1 (by rfl) ⟨3235355, by rfl⟩ : syracuseStep 4313807 = 6470711) B6470711
theorem B2692511 : Blo 1196415 2692511 := bstep (se 1 (by rfl) ⟨2019383, by rfl⟩ : syracuseStep 2692511 = 4038767) B4038767
theorem B80958919 : Blo 1196415 80958919 := bstep (se 1 (by rfl) ⟨60719189, by rfl⟩ : syracuseStep 80958919 = 121438379) B121438379
theorem B13629383 : Blo 1196415 13629383 := bstep (se 1 (by rfl) ⟨10222037, by rfl⟩ : syracuseStep 13629383 = 20444075) B20444075
theorem B2021483 : Blo 1196415 2021483 := bstep (se 1 (by rfl) ⟨1516112, by rfl⟩ : syracuseStep 2021483 = 3032225) B3032225
theorem B2694383 : Blo 1196415 2694383 := bstep (se 1 (by rfl) ⟨2020787, by rfl⟩ : syracuseStep 2694383 = 4041575) B4041575
theorem B5111839 : Blo 1196415 5111839 := bstep (se 1 (by rfl) ⟨3833879, by rfl⟩ : syracuseStep 5111839 = 7667759) B7667759
theorem B4546925 : Blo 1196415 4546925 := bstep (se 3 (by rfl) ⟨852548, by rfl⟩ : syracuseStep 4546925 = 1705097) B1705097
theorem B2875871 : Blo 1196415 2875871 := bstep (se 1 (by rfl) ⟨2156903, by rfl⟩ : syracuseStep 2875871 = 4313807) B4313807
theorem B1196527 : Blo 1196415 1196527 := bstep (se 1 (by rfl) ⟨897395, by rfl⟩ : syracuseStep 1196527 = 1794791) B1794791
theorem B1795007 : Blo 1196415 1795007 := bstep (se 1 (by rfl) ⟨1346255, by rfl⟩ : syracuseStep 1795007 = 2692511) B2692511
theorem B1197311 : Blo 1196415 1197311 := bstep (se 1 (by rfl) ⟨897983, by rfl⟩ : syracuseStep 1197311 = 1795967) B1795967
theorem B9086255 : Blo 1196415 9086255 := bstep (se 1 (by rfl) ⟨6814691, by rfl⟩ : syracuseStep 9086255 = 13629383) B13629383
theorem B1197519 : Blo 1196415 1197519 := bstep (se 1 (by rfl) ⟨898139, by rfl⟩ : syracuseStep 1197519 = 1796279) B1796279
theorem B1197615 : Blo 1196415 1197615 := bstep (se 1 (by rfl) ⟨898211, by rfl⟩ : syracuseStep 1197615 = 1796423) B1796423
theorem B1197727 : Blo 1196415 1197727 := bstep (se 1 (by rfl) ⟨898295, by rfl⟩ : syracuseStep 1197727 = 1796591) B1796591
theorem B1796255 : Blo 1196415 1796255 := bstep (se 1 (by rfl) ⟨1347191, by rfl⟩ : syracuseStep 1796255 = 2694383) B2694383
theorem B1797119 : Blo 1196415 1797119 := bstep (se 1 (by rfl) ⟨1347839, by rfl⟩ : syracuseStep 1797119 = 2695679) B2695679
theorem B9849883 : Blo 1196415 9849883 := bstep (se 1 (by rfl) ⟨7387412, by rfl⟩ : syracuseStep 9849883 = 14774825) B14774825
theorem B1347655 : Blo 1196415 1347655 := bstep (se 1 (by rfl) ⟨1010741, by rfl⟩ : syracuseStep 1347655 = 2021483) B2021483
theorem B38836199 : Blo 1196415 38836199 := bstep (se 1 (by rfl) ⟨29127149, by rfl⟩ : syracuseStep 38836199 = 58254299) B58254299
theorem B10918415 : Blo 1196415 10918415 := bstep (se 1 (by rfl) ⟨8188811, by rfl⟩ : syracuseStep 10918415 = 16377623) B16377623
theorem B49159295 : Blo 1196415 49159295 := bstep (se 1 (by rfl) ⟨36869471, by rfl⟩ : syracuseStep 49159295 = 73738943) B73738943
theorem B107945225 : Blo 1196415 107945225 := bstep (se 2 (by rfl) ⟨40479459, by rfl⟩ : syracuseStep 107945225 = 80958919) B80958919
theorem B6815785 : Blo 1196415 6815785 := bstep (se 2 (by rfl) ⟨2555919, by rfl⟩ : syracuseStep 6815785 = 5111839) B5111839
theorem B3031283 : Blo 1196415 3031283 := bstep (se 1 (by rfl) ⟨2273462, by rfl⟩ : syracuseStep 3031283 = 4546925) B4546925
theorem B1196671 : Blo 1196415 1196671 := bstep (se 1 (by rfl) ⟨897503, by rfl⟩ : syracuseStep 1196671 = 1795007) B1795007
theorem B7668989 : Blo 1196415 7668989 := bstep (se 3 (by rfl) ⟨1437935, by rfl⟩ : syracuseStep 7668989 = 2875871) B2875871
theorem B13133177 : Blo 1196415 13133177 := bstep (se 2 (by rfl) ⟨4924941, by rfl⟩ : syracuseStep 13133177 = 9849883) B9849883
theorem B29115773 : Blo 1196415 29115773 := bstep (se 3 (by rfl) ⟨5459207, by rfl⟩ : syracuseStep 29115773 = 10918415) B10918415
theorem B1197503 : Blo 1196415 1197503 := bstep (se 1 (by rfl) ⟨898127, by rfl⟩ : syracuseStep 1197503 = 1796255) B1796255
theorem B1198079 : Blo 1196415 1198079 := bstep (se 1 (by rfl) ⟨898559, by rfl⟩ : syracuseStep 1198079 = 1797119) B1797119
theorem B1796873 : Blo 1196415 1796873 := bstep (se 2 (by rfl) ⟨673827, by rfl⟩ : syracuseStep 1796873 = 1347655) B1347655
theorem B6057503 : Blo 1196415 6057503 := bstep (se 1 (by rfl) ⟨4543127, by rfl⟩ : syracuseStep 6057503 = 9086255) B9086255
theorem B25890799 : Blo 1196415 25890799 := bstep (se 1 (by rfl) ⟨19418099, by rfl⟩ : syracuseStep 25890799 = 38836199) B38836199
theorem B32772863 : Blo 1196415 32772863 := bstep (se 1 (by rfl) ⟨24579647, by rfl⟩ : syracuseStep 32772863 = 49159295) B49159295
theorem B71963483 : Blo 1196415 71963483 := bstep (se 1 (by rfl) ⟨53972612, by rfl⟩ : syracuseStep 71963483 = 107945225) B107945225
theorem B21848575 : Blo 1196415 21848575 := bstep (se 1 (by rfl) ⟨16386431, by rfl⟩ : syracuseStep 21848575 = 32772863) B32772863
theorem B5112659 : Blo 1196415 5112659 := bstep (se 1 (by rfl) ⟨3834494, by rfl⟩ : syracuseStep 5112659 = 7668989) B7668989
theorem B1197915 : Blo 1196415 1197915 := bstep (se 1 (by rfl) ⟨898436, by rfl⟩ : syracuseStep 1197915 = 1796873) B1796873
theorem B9087713 : Blo 1196415 9087713 := bstep (se 2 (by rfl) ⟨3407892, by rfl⟩ : syracuseStep 9087713 = 6815785) B6815785
theorem B19410515 : Blo 1196415 19410515 := bstep (se 1 (by rfl) ⟨14557886, by rfl⟩ : syracuseStep 19410515 = 29115773) B29115773
theorem B191902621 : Blo 1196415 191902621 := bstep (se 3 (by rfl) ⟨35981741, by rfl⟩ : syracuseStep 191902621 = 71963483) B71963483
theorem B2020855 : Blo 1196415 2020855 := bstep (se 1 (by rfl) ⟨1515641, by rfl⟩ : syracuseStep 2020855 = 3031283) B3031283
theorem B8755451 : Blo 1196415 8755451 := bstep (se 1 (by rfl) ⟨6566588, by rfl⟩ : syracuseStep 8755451 = 13133177) B13133177
theorem B4038335 : Blo 1196415 4038335 := bstep (se 1 (by rfl) ⟨3028751, by rfl⟩ : syracuseStep 4038335 = 6057503) B6057503
theorem B34521065 : Blo 1196415 34521065 := bstep (se 2 (by rfl) ⟨12945399, by rfl⟩ : syracuseStep 34521065 = 25890799) B25890799
theorem B29131433 : Blo 1196415 29131433 := bstep (se 2 (by rfl) ⟨10924287, by rfl⟩ : syracuseStep 29131433 = 21848575) B21848575
theorem B255870161 : Blo 1196415 255870161 := bstep (se 2 (by rfl) ⟨95951310, by rfl⟩ : syracuseStep 255870161 = 191902621) B191902621
theorem B13633757 : Blo 1196415 13633757 := bstep (se 3 (by rfl) ⟨2556329, by rfl⟩ : syracuseStep 13633757 = 5112659) B5112659
theorem B23014043 : Blo 1196415 23014043 := bstep (se 1 (by rfl) ⟨17260532, by rfl⟩ : syracuseStep 23014043 = 34521065) B34521065
theorem B5836967 : Blo 1196415 5836967 := bstep (se 1 (by rfl) ⟨4377725, by rfl⟩ : syracuseStep 5836967 = 8755451) B8755451
theorem B6058475 : Blo 1196415 6058475 := bstep (se 1 (by rfl) ⟨4543856, by rfl⟩ : syracuseStep 6058475 = 9087713) B9087713
theorem B12940343 : Blo 1196415 12940343 := bstep (se 1 (by rfl) ⟨9705257, by rfl⟩ : syracuseStep 12940343 = 19410515) B19410515
theorem B2692223 : Blo 1196415 2692223 := bstep (se 1 (by rfl) ⟨2019167, by rfl⟩ : syracuseStep 2692223 = 4038335) B4038335
theorem B2694473 : Blo 1196415 2694473 := bstep (se 2 (by rfl) ⟨1010427, by rfl⟩ : syracuseStep 2694473 = 2020855) B2020855
theorem B3891311 : Blo 1196415 3891311 := bstep (se 1 (by rfl) ⟨2918483, by rfl⟩ : syracuseStep 3891311 = 5836967) B5836967
theorem B4038983 : Blo 1196415 4038983 := bstep (se 1 (by rfl) ⟨3029237, by rfl⟩ : syracuseStep 4038983 = 6058475) B6058475
theorem B8626895 : Blo 1196415 8626895 := bstep (se 1 (by rfl) ⟨6470171, by rfl⟩ : syracuseStep 8626895 = 12940343) B12940343
theorem B1794815 : Blo 1196415 1794815 := bstep (se 1 (by rfl) ⟨1346111, by rfl⟩ : syracuseStep 1794815 = 2692223) B2692223
theorem B1796315 : Blo 1196415 1796315 := bstep (se 1 (by rfl) ⟨1347236, by rfl⟩ : syracuseStep 1796315 = 2694473) B2694473
theorem B9089171 : Blo 1196415 9089171 := bstep (se 1 (by rfl) ⟨6816878, by rfl⟩ : syracuseStep 9089171 = 13633757) B13633757
theorem B19420955 : Blo 1196415 19420955 := bstep (se 1 (by rfl) ⟨14565716, by rfl⟩ : syracuseStep 19420955 = 29131433) B29131433
theorem B170580107 : Blo 1196415 170580107 := bstep (se 1 (by rfl) ⟨127935080, by rfl⟩ : syracuseStep 170580107 = 255870161) B255870161
theorem B15342695 : Blo 1196415 15342695 := bstep (se 1 (by rfl) ⟨11507021, by rfl⟩ : syracuseStep 15342695 = 23014043) B23014043
theorem B5751263 : Blo 1196415 5751263 := bstep (se 1 (by rfl) ⟨4313447, by rfl⟩ : syracuseStep 5751263 = 8626895) B8626895
theorem B1196543 : Blo 1196415 1196543 := bstep (se 1 (by rfl) ⟨897407, by rfl⟩ : syracuseStep 1196543 = 1794815) B1794815
theorem B1197543 : Blo 1196415 1197543 := bstep (se 1 (by rfl) ⟨898157, by rfl⟩ : syracuseStep 1197543 = 1796315) B1796315
theorem B12947303 : Blo 1196415 12947303 := bstep (se 1 (by rfl) ⟨9710477, by rfl⟩ : syracuseStep 12947303 = 19420955) B19420955
theorem B10228463 : Blo 1196415 10228463 := bstep (se 1 (by rfl) ⟨7671347, by rfl⟩ : syracuseStep 10228463 = 15342695) B15342695
theorem B2594207 : Blo 1196415 2594207 := bstep (se 1 (by rfl) ⟨1945655, by rfl⟩ : syracuseStep 2594207 = 3891311) B3891311
theorem B6059447 : Blo 1196415 6059447 := bstep (se 1 (by rfl) ⟨4544585, by rfl⟩ : syracuseStep 6059447 = 9089171) B9089171
theorem B2692655 : Blo 1196415 2692655 := bstep (se 1 (by rfl) ⟨2019491, by rfl⟩ : syracuseStep 2692655 = 4038983) B4038983
theorem B113720071 : Blo 1196415 113720071 := bstep (se 1 (by rfl) ⟨85290053, by rfl⟩ : syracuseStep 113720071 = 170580107) B170580107
theorem B4039631 : Blo 1196415 4039631 := bstep (se 1 (by rfl) ⟨3029723, by rfl⟩ : syracuseStep 4039631 = 6059447) B6059447
theorem B151626761 : Blo 1196415 151626761 := bstep (se 2 (by rfl) ⟨56860035, by rfl⟩ : syracuseStep 151626761 = 113720071) B113720071
theorem B1795103 : Blo 1196415 1795103 := bstep (se 1 (by rfl) ⟨1346327, by rfl⟩ : syracuseStep 1795103 = 2692655) B2692655
theorem B15336701 : Blo 1196415 15336701 := bstep (se 3 (by rfl) ⟨2875631, by rfl⟩ : syracuseStep 15336701 = 5751263) B5751263
theorem B6818975 : Blo 1196415 6818975 := bstep (se 1 (by rfl) ⟨5114231, by rfl⟩ : syracuseStep 6818975 = 10228463) B10228463
theorem B6917885 : Blo 1196415 6917885 := bstep (se 3 (by rfl) ⟨1297103, by rfl⟩ : syracuseStep 6917885 = 2594207) B2594207
theorem B8631535 : Blo 1196415 8631535 := bstep (se 1 (by rfl) ⟨6473651, by rfl⟩ : syracuseStep 8631535 = 12947303) B12947303
theorem B1196735 : Blo 1196415 1196735 := bstep (se 1 (by rfl) ⟨897551, by rfl⟩ : syracuseStep 1196735 = 1795103) B1795103
theorem B10224467 : Blo 1196415 10224467 := bstep (se 1 (by rfl) ⟨7668350, by rfl⟩ : syracuseStep 10224467 = 15336701) B15336701
theorem B101084507 : Blo 1196415 101084507 := bstep (se 1 (by rfl) ⟨75813380, by rfl⟩ : syracuseStep 101084507 = 151626761) B151626761
theorem B2693087 : Blo 1196415 2693087 := bstep (se 1 (by rfl) ⟨2019815, by rfl⟩ : syracuseStep 2693087 = 4039631) B4039631
theorem B11508713 : Blo 1196415 11508713 := bstep (se 2 (by rfl) ⟨4315767, by rfl⟩ : syracuseStep 11508713 = 8631535) B8631535
theorem B4545983 : Blo 1196415 4545983 := bstep (se 1 (by rfl) ⟨3409487, by rfl⟩ : syracuseStep 4545983 = 6818975) B6818975
theorem B4611923 : Blo 1196415 4611923 := bstep (se 1 (by rfl) ⟨3458942, by rfl⟩ : syracuseStep 4611923 = 6917885) B6917885
theorem B6816311 : Blo 1196415 6816311 := bstep (se 1 (by rfl) ⟨5112233, by rfl⟩ : syracuseStep 6816311 = 10224467) B10224467
theorem B1795391 : Blo 1196415 1795391 := bstep (se 1 (by rfl) ⟨1346543, by rfl⟩ : syracuseStep 1795391 = 2693087) B2693087
theorem B67389671 : Blo 1196415 67389671 := bstep (se 1 (by rfl) ⟨50542253, by rfl⟩ : syracuseStep 67389671 = 101084507) B101084507
theorem B3074615 : Blo 1196415 3074615 := bstep (se 1 (by rfl) ⟨2305961, by rfl⟩ : syracuseStep 3074615 = 4611923) B4611923
theorem B7672475 : Blo 1196415 7672475 := bstep (se 1 (by rfl) ⟨5754356, by rfl⟩ : syracuseStep 7672475 = 11508713) B11508713
theorem B3030655 : Blo 1196415 3030655 := bstep (se 1 (by rfl) ⟨2272991, by rfl⟩ : syracuseStep 3030655 = 4545983) B4545983
theorem B1196927 : Blo 1196415 1196927 := bstep (se 1 (by rfl) ⟨897695, by rfl⟩ : syracuseStep 1196927 = 1795391) B1795391
theorem B2049743 : Blo 1196415 2049743 := bstep (se 1 (by rfl) ⟨1537307, by rfl⟩ : syracuseStep 2049743 = 3074615) B3074615
theorem B4040873 : Blo 1196415 4040873 := bstep (se 2 (by rfl) ⟨1515327, by rfl⟩ : syracuseStep 4040873 = 3030655) B3030655
theorem B5114983 : Blo 1196415 5114983 := bstep (se 1 (by rfl) ⟨3836237, by rfl⟩ : syracuseStep 5114983 = 7672475) B7672475
theorem B4544207 : Blo 1196415 4544207 := bstep (se 1 (by rfl) ⟨3408155, by rfl⟩ : syracuseStep 4544207 = 6816311) B6816311
theorem B179705789 : Blo 1196415 179705789 := bstep (se 3 (by rfl) ⟨33694835, by rfl⟩ : syracuseStep 179705789 = 67389671) B67389671
theorem B5465981 : Blo 1196415 5465981 := bstep (se 3 (by rfl) ⟨1024871, by rfl⟩ : syracuseStep 5465981 = 2049743) B2049743
theorem B119803859 : Blo 1196415 119803859 := bstep (se 1 (by rfl) ⟨89852894, by rfl⟩ : syracuseStep 119803859 = 179705789) B179705789
theorem B6819977 : Blo 1196415 6819977 := bstep (se 2 (by rfl) ⟨2557491, by rfl⟩ : syracuseStep 6819977 = 5114983) B5114983
theorem B3029471 : Blo 1196415 3029471 := bstep (se 1 (by rfl) ⟨2272103, by rfl⟩ : syracuseStep 3029471 = 4544207) B4544207
theorem B2693915 : Blo 1196415 2693915 := bstep (se 1 (by rfl) ⟨2020436, by rfl⟩ : syracuseStep 2693915 = 4040873) B4040873
theorem B4546651 : Blo 1196415 4546651 := bstep (se 1 (by rfl) ⟨3409988, by rfl⟩ : syracuseStep 4546651 = 6819977) B6819977
theorem B1795943 : Blo 1196415 1795943 := bstep (se 1 (by rfl) ⟨1346957, by rfl⟩ : syracuseStep 1795943 = 2693915) B2693915
theorem B2019647 : Blo 1196415 2019647 := bstep (se 1 (by rfl) ⟨1514735, by rfl⟩ : syracuseStep 2019647 = 3029471) B3029471
theorem B79869239 : Blo 1196415 79869239 := bstep (se 1 (by rfl) ⟨59901929, by rfl⟩ : syracuseStep 79869239 = 119803859) B119803859
theorem B3643987 : Blo 1196415 3643987 := bstep (se 1 (by rfl) ⟨2732990, by rfl⟩ : syracuseStep 3643987 = 5465981) B5465981
theorem B6062201 : Blo 1196415 6062201 := bstep (se 2 (by rfl) ⟨2273325, by rfl⟩ : syracuseStep 6062201 = 4546651) B4546651
theorem B4858649 : Blo 1196415 4858649 := bstep (se 2 (by rfl) ⟨1821993, by rfl⟩ : syracuseStep 4858649 = 3643987) B3643987
theorem B1197295 : Blo 1196415 1197295 := bstep (se 1 (by rfl) ⟨897971, by rfl⟩ : syracuseStep 1197295 = 1795943) B1795943
theorem B1346431 : Blo 1196415 1346431 := bstep (se 1 (by rfl) ⟨1009823, by rfl⟩ : syracuseStep 1346431 = 2019647) B2019647
theorem B53246159 : Blo 1196415 53246159 := bstep (se 1 (by rfl) ⟨39934619, by rfl⟩ : syracuseStep 53246159 = 79869239) B79869239
theorem B1795241 : Blo 1196415 1795241 := bstep (se 2 (by rfl) ⟨673215, by rfl⟩ : syracuseStep 1795241 = 1346431) B1346431
theorem B35497439 : Blo 1196415 35497439 := bstep (se 1 (by rfl) ⟨26623079, by rfl⟩ : syracuseStep 35497439 = 53246159) B53246159
theorem B4041467 : Blo 1196415 4041467 := bstep (se 1 (by rfl) ⟨3031100, by rfl⟩ : syracuseStep 4041467 = 6062201) B6062201
theorem B3239099 : Blo 1196415 3239099 := bstep (se 1 (by rfl) ⟨2429324, by rfl⟩ : syracuseStep 3239099 = 4858649) B4858649
theorem B1196827 : Blo 1196415 1196827 := bstep (se 1 (by rfl) ⟨897620, by rfl⟩ : syracuseStep 1196827 = 1795241) B1795241
theorem B2159399 : Blo 1196415 2159399 := bstep (se 1 (by rfl) ⟨1619549, by rfl⟩ : syracuseStep 2159399 = 3239099) B3239099
theorem B23664959 : Blo 1196415 23664959 := bstep (se 1 (by rfl) ⟨17748719, by rfl⟩ : syracuseStep 23664959 = 35497439) B35497439
theorem B2694311 : Blo 1196415 2694311 := bstep (se 1 (by rfl) ⟨2020733, by rfl⟩ : syracuseStep 2694311 = 4041467) B4041467
theorem B1796207 : Blo 1196415 1796207 := bstep (se 1 (by rfl) ⟨1347155, by rfl⟩ : syracuseStep 1796207 = 2694311) B2694311
theorem B1439599 : Blo 1196415 1439599 := bstep (se 1 (by rfl) ⟨1079699, by rfl⟩ : syracuseStep 1439599 = 2159399) B2159399
theorem B15776639 : Blo 1196415 15776639 := bstep (se 1 (by rfl) ⟨11832479, by rfl⟩ : syracuseStep 15776639 = 23664959) B23664959
theorem B1197471 : Blo 1196415 1197471 := bstep (se 1 (by rfl) ⟨898103, by rfl⟩ : syracuseStep 1197471 = 1796207) B1796207
theorem B1919465 : Blo 1196415 1919465 := bstep (se 2 (by rfl) ⟨719799, by rfl⟩ : syracuseStep 1919465 = 1439599) B1439599
theorem B10517759 : Blo 1196415 10517759 := bstep (se 1 (by rfl) ⟨7888319, by rfl⟩ : syracuseStep 10517759 = 15776639) B15776639
theorem B1279643 : Blo 1196415 1279643 := bstep (se 1 (by rfl) ⟨959732, by rfl⟩ : syracuseStep 1279643 = 1919465) B1919465
theorem B7011839 : Blo 1196415 7011839 := bstep (se 1 (by rfl) ⟨5258879, by rfl⟩ : syracuseStep 7011839 = 10517759) B10517759
theorem B3412381 : Blo 1196415 3412381 := bstep (se 3 (by rfl) ⟨639821, by rfl⟩ : syracuseStep 3412381 = 1279643) B1279643
theorem B4674559 : Blo 1196415 4674559 := bstep (se 1 (by rfl) ⟨3505919, by rfl⟩ : syracuseStep 4674559 = 7011839) B7011839
theorem B4549841 : Blo 1196415 4549841 := bstep (se 2 (by rfl) ⟨1706190, by rfl⟩ : syracuseStep 4549841 = 3412381) B3412381
theorem B6232745 : Blo 1196415 6232745 := bstep (se 2 (by rfl) ⟨2337279, by rfl⟩ : syracuseStep 6232745 = 4674559) B4674559
theorem B3033227 : Blo 1196415 3033227 := bstep (se 1 (by rfl) ⟨2274920, by rfl⟩ : syracuseStep 3033227 = 4549841) B4549841
theorem B16620653 : Blo 1196415 16620653 := bstep (se 3 (by rfl) ⟨3116372, by rfl⟩ : syracuseStep 16620653 = 6232745) B6232745
theorem B44321741 : Blo 1196415 44321741 := bstep (se 3 (by rfl) ⟨8310326, by rfl⟩ : syracuseStep 44321741 = 16620653) B16620653
theorem B2022151 : Blo 1196415 2022151 := bstep (se 1 (by rfl) ⟨1516613, by rfl⟩ : syracuseStep 2022151 = 3033227) B3033227
theorem B2696201 : Blo 1196415 2696201 := bstep (se 2 (by rfl) ⟨1011075, by rfl⟩ : syracuseStep 2696201 = 2022151) B2022151
theorem B29547827 : Blo 1196415 29547827 := bstep (se 1 (by rfl) ⟨22160870, by rfl⟩ : syracuseStep 29547827 = 44321741) B44321741
theorem B1797467 : Blo 1196415 1797467 := bstep (se 1 (by rfl) ⟨1348100, by rfl⟩ : syracuseStep 1797467 = 2696201) B2696201
theorem B19698551 : Blo 1196415 19698551 := bstep (se 1 (by rfl) ⟨14773913, by rfl⟩ : syracuseStep 19698551 = 29547827) B29547827
theorem B13132367 : Blo 1196415 13132367 := bstep (se 1 (by rfl) ⟨9849275, by rfl⟩ : syracuseStep 13132367 = 19698551) B19698551
theorem B1198311 : Blo 1196415 1198311 := bstep (se 1 (by rfl) ⟨898733, by rfl⟩ : syracuseStep 1198311 = 1797467) B1797467
theorem B8754911 : Blo 1196415 8754911 := bstep (se 1 (by rfl) ⟨6566183, by rfl⟩ : syracuseStep 8754911 = 13132367) B13132367
theorem B5836607 : Blo 1196415 5836607 := bstep (se 1 (by rfl) ⟨4377455, by rfl⟩ : syracuseStep 5836607 = 8754911) B8754911
theorem B3891071 : Blo 1196415 3891071 := bstep (se 1 (by rfl) ⟨2918303, by rfl⟩ : syracuseStep 3891071 = 5836607) B5836607
theorem B10376189 : Blo 1196415 10376189 := bstep (se 3 (by rfl) ⟨1945535, by rfl⟩ : syracuseStep 10376189 = 3891071) B3891071
theorem B6917459 : Blo 1196415 6917459 := bstep (se 1 (by rfl) ⟨5188094, by rfl⟩ : syracuseStep 6917459 = 10376189) B10376189
theorem B18446557 : Blo 1196415 18446557 := bstep (se 3 (by rfl) ⟨3458729, by rfl⟩ : syracuseStep 18446557 = 6917459) B6917459
theorem B24595409 : Blo 1196415 24595409 := bstep (se 2 (by rfl) ⟨9223278, by rfl⟩ : syracuseStep 24595409 = 18446557) B18446557
theorem B16396939 : Blo 1196415 16396939 := bstep (se 1 (by rfl) ⟨12297704, by rfl⟩ : syracuseStep 16396939 = 24595409) B24595409
theorem B21862585 : Blo 1196415 21862585 := bstep (se 2 (by rfl) ⟨8198469, by rfl⟩ : syracuseStep 21862585 = 16396939) B16396939
theorem B29150113 : Blo 1196415 29150113 := bstep (se 2 (by rfl) ⟨10931292, by rfl⟩ : syracuseStep 29150113 = 21862585) B21862585
theorem B38866817 : Blo 1196415 38866817 := bstep (se 2 (by rfl) ⟨14575056, by rfl⟩ : syracuseStep 38866817 = 29150113) B29150113
theorem B25911211 : Blo 1196415 25911211 := bstep (se 1 (by rfl) ⟨19433408, by rfl⟩ : syracuseStep 25911211 = 38866817) B38866817
theorem B34548281 : Blo 1196415 34548281 := bstep (se 2 (by rfl) ⟨12955605, by rfl⟩ : syracuseStep 34548281 = 25911211) B25911211
theorem B23032187 : Blo 1196415 23032187 := bstep (se 1 (by rfl) ⟨17274140, by rfl⟩ : syracuseStep 23032187 = 34548281) B34548281
theorem B15354791 : Blo 1196415 15354791 := bstep (se 1 (by rfl) ⟨11516093, by rfl⟩ : syracuseStep 15354791 = 23032187) B23032187
theorem B10236527 : Blo 1196415 10236527 := bstep (se 1 (by rfl) ⟨7677395, by rfl⟩ : syracuseStep 10236527 = 15354791) B15354791
theorem B6824351 : Blo 1196415 6824351 := bstep (se 1 (by rfl) ⟨5118263, by rfl⟩ : syracuseStep 6824351 = 10236527) B10236527
theorem B4549567 : Blo 1196415 4549567 := bstep (se 1 (by rfl) ⟨3412175, by rfl⟩ : syracuseStep 4549567 = 6824351) B6824351
theorem B6066089 : Blo 1196415 6066089 := bstep (se 2 (by rfl) ⟨2274783, by rfl⟩ : syracuseStep 6066089 = 4549567) B4549567
theorem B4044059 : Blo 1196415 4044059 := bstep (se 1 (by rfl) ⟨3033044, by rfl⟩ : syracuseStep 4044059 = 6066089) B6066089
theorem B2696039 : Blo 1196415 2696039 := bstep (se 1 (by rfl) ⟨2022029, by rfl⟩ : syracuseStep 2696039 = 4044059) B4044059
theorem B1797359 : Blo 1196415 1797359 := bstep (se 1 (by rfl) ⟨1348019, by rfl⟩ : syracuseStep 1797359 = 2696039) B2696039
theorem B1198239 : Blo 1196415 1198239 := bstep (se 1 (by rfl) ⟨898679, by rfl⟩ : syracuseStep 1198239 = 1797359) B1797359

theorem C0 (j : ℕ) (h1 : 299103 ≤ j) (h2 : j ≤ 299603) : Blo 1196415 (4 * j + 3) := by
  interval_cases j
  · exact B1196415
  · exact B1196419
  · exact B1196423
  · exact B1196427
  · exact B1196431
  · exact B1196435
  · exact B1196439
  · exact B1196443
  · exact B1196447
  · exact B1196451
  · exact B1196455
  · exact B1196459
  · exact B1196463
  · exact B1196467
  · exact B1196471
  · exact B1196475
  · exact B1196479
  · exact B1196483
  · exact B1196487
  · exact B1196491
  · exact B1196495
  · exact B1196499
  · exact B1196503
  · exact B1196507
  · exact B1196511
  · exact B1196515
  · exact B1196519
  · exact B1196523
  · exact B1196527
  · exact B1196531
  · exact B1196535
  · exact B1196539
  · exact B1196543
  · exact B1196547
  · exact B1196551
  · exact B1196555
  · exact B1196559
  · exact B1196563
  · exact B1196567
  · exact B1196571
  · exact B1196575
  · exact B1196579
  · exact B1196583
  · exact B1196587
  · exact B1196591
  · exact B1196595
  · exact B1196599
  · exact B1196603
  · exact B1196607
  · exact B1196611
  · exact B1196615
  · exact B1196619
  · exact B1196623
  · exact B1196627
  · exact B1196631
  · exact B1196635
  · exact B1196639
  · exact B1196643
  · exact B1196647
  · exact B1196651
  · exact B1196655
  · exact B1196659
  · exact B1196663
  · exact B1196667
  · exact B1196671
  · exact B1196675
  · exact B1196679
  · exact B1196683
  · exact B1196687
  · exact B1196691
  · exact B1196695
  · exact B1196699
  · exact B1196703
  · exact B1196707
  · exact B1196711
  · exact B1196715
  · exact B1196719
  · exact B1196723
  · exact B1196727
  · exact B1196731
  · exact B1196735
  · exact B1196739
  · exact B1196743
  · exact B1196747
  · exact B1196751
  · exact B1196755
  · exact B1196759
  · exact B1196763
  · exact B1196767
  · exact B1196771
  · exact B1196775
  · exact B1196779
  · exact B1196783
  · exact B1196787
  · exact B1196791
  · exact B1196795
  · exact B1196799
  · exact B1196803
  · exact B1196807
  · exact B1196811
  · exact B1196815
  · exact B1196819
  · exact B1196823
  · exact B1196827
  · exact B1196831
  · exact B1196835
  · exact B1196839
  · exact B1196843
  · exact B1196847
  · exact B1196851
  · exact B1196855
  · exact B1196859
  · exact B1196863
  · exact B1196867
  · exact B1196871
  · exact B1196875
  · exact B1196879
  · exact B1196883
  · exact B1196887
  · exact B1196891
  · exact B1196895
  · exact B1196899
  · exact B1196903
  · exact B1196907
  · exact B1196911
  · exact B1196915
  · exact B1196919
  · exact B1196923
  · exact B1196927
  · exact B1196931
  · exact B1196935
  · exact B1196939
  · exact B1196943
  · exact B1196947
  · exact B1196951
  · exact B1196955
  · exact B1196959
  · exact B1196963
  · exact B1196967
  · exact B1196971
  · exact B1196975
  · exact B1196979
  · exact B1196983
  · exact B1196987
  · exact B1196991
  · exact B1196995
  · exact B1196999
  · exact B1197003
  · exact B1197007
  · exact B1197011
  · exact B1197015
  · exact B1197019
  · exact B1197023
  · exact B1197027
  · exact B1197031
  · exact B1197035
  · exact B1197039
  · exact B1197043
  · exact B1197047
  · exact B1197051
  · exact B1197055
  · exact B1197059
  · exact B1197063
  · exact B1197067
  · exact B1197071
  · exact B1197075
  · exact B1197079
  · exact B1197083
  · exact B1197087
  · exact B1197091
  · exact B1197095
  · exact B1197099
  · exact B1197103
  · exact B1197107
  · exact B1197111
  · exact B1197115
  · exact B1197119
  · exact B1197123
  · exact B1197127
  · exact B1197131
  · exact B1197135
  · exact B1197139
  · exact B1197143
  · exact B1197147
  · exact B1197151
  · exact B1197155
  · exact B1197159
  · exact B1197163
  · exact B1197167
  · exact B1197171
  · exact B1197175
  · exact B1197179
  · exact B1197183
  · exact B1197187
  · exact B1197191
  · exact B1197195
  · exact B1197199
  · exact B1197203
  · exact B1197207
  · exact B1197211
  · exact B1197215
  · exact B1197219
  · exact B1197223
  · exact B1197227
  · exact B1197231
  · exact B1197235
  · exact B1197239
  · exact B1197243
  · exact B1197247
  · exact B1197251
  · exact B1197255
  · exact B1197259
  · exact B1197263
  · exact B1197267
  · exact B1197271
  · exact B1197275
  · exact B1197279
  · exact B1197283
  · exact B1197287
  · exact B1197291
  · exact B1197295
  · exact B1197299
  · exact B1197303
  · exact B1197307
  · exact B1197311
  · exact B1197315
  · exact B1197319
  · exact B1197323
  · exact B1197327
  · exact B1197331
  · exact B1197335
  · exact B1197339
  · exact B1197343
  · exact B1197347
  · exact B1197351
  · exact B1197355
  · exact B1197359
  · exact B1197363
  · exact B1197367
  · exact B1197371
  · exact B1197375
  · exact B1197379
  · exact B1197383
  · exact B1197387
  · exact B1197391
  · exact B1197395
  · exact B1197399
  · exact B1197403
  · exact B1197407
  · exact B1197411
  · exact B1197415
  · exact B1197419
  · exact B1197423
  · exact B1197427
  · exact B1197431
  · exact B1197435
  · exact B1197439
  · exact B1197443
  · exact B1197447
  · exact B1197451
  · exact B1197455
  · exact B1197459
  · exact B1197463
  · exact B1197467
  · exact B1197471
  · exact B1197475
  · exact B1197479
  · exact B1197483
  · exact B1197487
  · exact B1197491
  · exact B1197495
  · exact B1197499
  · exact B1197503
  · exact B1197507
  · exact B1197511
  · exact B1197515
  · exact B1197519
  · exact B1197523
  · exact B1197527
  · exact B1197531
  · exact B1197535
  · exact B1197539
  · exact B1197543
  · exact B1197547
  · exact B1197551
  · exact B1197555
  · exact B1197559
  · exact B1197563
  · exact B1197567
  · exact B1197571
  · exact B1197575
  · exact B1197579
  · exact B1197583
  · exact B1197587
  · exact B1197591
  · exact B1197595
  · exact B1197599
  · exact B1197603
  · exact B1197607
  · exact B1197611
  · exact B1197615
  · exact B1197619
  · exact B1197623
  · exact B1197627
  · exact B1197631
  · exact B1197635
  · exact B1197639
  · exact B1197643
  · exact B1197647
  · exact B1197651
  · exact B1197655
  · exact B1197659
  · exact B1197663
  · exact B1197667
  · exact B1197671
  · exact B1197675
  · exact B1197679
  · exact B1197683
  · exact B1197687
  · exact B1197691
  · exact B1197695
  · exact B1197699
  · exact B1197703
  · exact B1197707
  · exact B1197711
  · exact B1197715
  · exact B1197719
  · exact B1197723
  · exact B1197727
  · exact B1197731
  · exact B1197735
  · exact B1197739
  · exact B1197743
  · exact B1197747
  · exact B1197751
  · exact B1197755
  · exact B1197759
  · exact B1197763
  · exact B1197767
  · exact B1197771
  · exact B1197775
  · exact B1197779
  · exact B1197783
  · exact B1197787
  · exact B1197791
  · exact B1197795
  · exact B1197799
  · exact B1197803
  · exact B1197807
  · exact B1197811
  · exact B1197815
  · exact B1197819
  · exact B1197823
  · exact B1197827
  · exact B1197831
  · exact B1197835
  · exact B1197839
  · exact B1197843
  · exact B1197847
  · exact B1197851
  · exact B1197855
  · exact B1197859
  · exact B1197863
  · exact B1197867
  · exact B1197871
  · exact B1197875
  · exact B1197879
  · exact B1197883
  · exact B1197887
  · exact B1197891
  · exact B1197895
  · exact B1197899
  · exact B1197903
  · exact B1197907
  · exact B1197911
  · exact B1197915
  · exact B1197919
  · exact B1197923
  · exact B1197927
  · exact B1197931
  · exact B1197935
  · exact B1197939
  · exact B1197943
  · exact B1197947
  · exact B1197951
  · exact B1197955
  · exact B1197959
  · exact B1197963
  · exact B1197967
  · exact B1197971
  · exact B1197975
  · exact B1197979
  · exact B1197983
  · exact B1197987
  · exact B1197991
  · exact B1197995
  · exact B1197999
  · exact B1198003
  · exact B1198007
  · exact B1198011
  · exact B1198015
  · exact B1198019
  · exact B1198023
  · exact B1198027
  · exact B1198031
  · exact B1198035
  · exact B1198039
  · exact B1198043
  · exact B1198047
  · exact B1198051
  · exact B1198055
  · exact B1198059
  · exact B1198063
  · exact B1198067
  · exact B1198071
  · exact B1198075
  · exact B1198079
  · exact B1198083
  · exact B1198087
  · exact B1198091
  · exact B1198095
  · exact B1198099
  · exact B1198103
  · exact B1198107
  · exact B1198111
  · exact B1198115
  · exact B1198119
  · exact B1198123
  · exact B1198127
  · exact B1198131
  · exact B1198135
  · exact B1198139
  · exact B1198143
  · exact B1198147
  · exact B1198151
  · exact B1198155
  · exact B1198159
  · exact B1198163
  · exact B1198167
  · exact B1198171
  · exact B1198175
  · exact B1198179
  · exact B1198183
  · exact B1198187
  · exact B1198191
  · exact B1198195
  · exact B1198199
  · exact B1198203
  · exact B1198207
  · exact B1198211
  · exact B1198215
  · exact B1198219
  · exact B1198223
  · exact B1198227
  · exact B1198231
  · exact B1198235
  · exact B1198239
  · exact B1198243
  · exact B1198247
  · exact B1198251
  · exact B1198255
  · exact B1198259
  · exact B1198263
  · exact B1198267
  · exact B1198271
  · exact B1198275
  · exact B1198279
  · exact B1198283
  · exact B1198287
  · exact B1198291
  · exact B1198295
  · exact B1198299
  · exact B1198303
  · exact B1198307
  · exact B1198311
  · exact B1198315
  · exact B1198319
  · exact B1198323
  · exact B1198327
  · exact B1198331
  · exact B1198335
  · exact B1198339
  · exact B1198343
  · exact B1198347
  · exact B1198351
  · exact B1198355
  · exact B1198359
  · exact B1198363
  · exact B1198367
  · exact B1198371
  · exact B1198375
  · exact B1198379
  · exact B1198383
  · exact B1198387
  · exact B1198391
  · exact B1198395
  · exact B1198399
  · exact B1198403
  · exact B1198407
  · exact B1198411
  · exact B1198415

theorem solution (m : ℕ) (hlo : 1196415 ≤ m) (hhi : m ≤ 1198415) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 299103 ≤ j := by omega
    have hj2 : j ≤ 299603 := by omega
    have hb : Blo 1196415 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
