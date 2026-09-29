-- Prove2me | solution 1 for syracuse_descends_range_794341_798341
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:05:34.915318+00:00
-- url     : https://prove2.me/submissions/6bfd5769-304f-48a7-b492-2d13adc353f2

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


theorem B1343533 : Blo 794341 1343533 := bbase (se 3 (by rfl) ⟨251912, by rfl⟩ : syracuseStep 1343533 = 503825) (by norm_num)
theorem B2687093 : Blo 794341 2687093 := bbase (se 5 (by rfl) ⟨125957, by rfl⟩ : syracuseStep 2687093 = 251915) (by norm_num)
theorem B1343621 : Blo 794341 1343621 := bbase (se 4 (by rfl) ⟨125964, by rfl⟩ : syracuseStep 1343621 = 251929) (by norm_num)
theorem B1343749 : Blo 794341 1343749 := bbase (se 4 (by rfl) ⟨125976, by rfl⟩ : syracuseStep 1343749 = 251953) (by norm_num)
theorem B852277 : Blo 794341 852277 := bbase (se 5 (by rfl) ⟨39950, by rfl⟩ : syracuseStep 852277 = 79901) (by norm_num)
theorem B1343837 : Blo 794341 1343837 := bbase (se 3 (by rfl) ⟨251969, by rfl⟩ : syracuseStep 1343837 = 503939) (by norm_num)
theorem B4358549 : Blo 794341 4358549 := bbase (se 6 (by rfl) ⟨102153, by rfl⟩ : syracuseStep 4358549 = 204307) (by norm_num)
theorem B1343965 : Blo 794341 1343965 := bbase (se 3 (by rfl) ⟨251993, by rfl⟩ : syracuseStep 1343965 = 503987) (by norm_num)
theorem B2425349 : Blo 794341 2425349 := bbase (se 4 (by rfl) ⟨227376, by rfl⟩ : syracuseStep 2425349 = 454753) (by norm_num)
theorem B11502101 : Blo 794341 11502101 := bbase (se 6 (by rfl) ⟨269580, by rfl⟩ : syracuseStep 11502101 = 539161) (by norm_num)
theorem B2687525 : Blo 794341 2687525 := bbase (se 4 (by rfl) ⟨251955, by rfl⟩ : syracuseStep 2687525 = 503911) (by norm_num)
theorem B1704493 : Blo 794341 1704493 := bbase (se 3 (by rfl) ⟨319592, by rfl⟩ : syracuseStep 1704493 = 639185) (by norm_num)
theorem B1344053 : Blo 794341 1344053 := bbase (se 5 (by rfl) ⟨63002, by rfl⟩ : syracuseStep 1344053 = 126005) (by norm_num)
theorem B4031045 : Blo 794341 4031045 := bbase (se 4 (by rfl) ⟨377910, by rfl⟩ : syracuseStep 4031045 = 755821) (by norm_num)
theorem B2556485 : Blo 794341 2556485 := bbase (se 4 (by rfl) ⟨239670, by rfl⟩ : syracuseStep 2556485 = 479341) (by norm_num)
theorem B1344181 : Blo 794341 1344181 := bbase (se 5 (by rfl) ⟨63008, by rfl⟩ : syracuseStep 1344181 = 126017) (by norm_num)
theorem B1344269 : Blo 794341 1344269 := bbase (se 3 (by rfl) ⟨252050, by rfl⟩ : syracuseStep 1344269 = 504101) (by norm_num)
theorem B1508149 : Blo 794341 1508149 := bbase (se 5 (by rfl) ⟨70694, by rfl⟩ : syracuseStep 1508149 = 141389) (by norm_num)
theorem B1344397 : Blo 794341 1344397 := bbase (se 3 (by rfl) ⟨252074, by rfl⟩ : syracuseStep 1344397 = 504149) (by norm_num)
theorem B1147861 : Blo 794341 1147861 := bbase (se 7 (by rfl) ⟨13451, by rfl⟩ : syracuseStep 1147861 = 26903) (by norm_num)
theorem B2687957 : Blo 794341 2687957 := bbase (se 7 (by rfl) ⟨31499, by rfl⟩ : syracuseStep 2687957 = 62999) (by norm_num)
theorem B1344485 : Blo 794341 1344485 := bbase (se 4 (by rfl) ⟨126045, by rfl⟩ : syracuseStep 1344485 = 252091) (by norm_num)
theorem B1704989 : Blo 794341 1704989 := bbase (se 3 (by rfl) ⟨319685, by rfl⟩ : syracuseStep 1704989 = 639371) (by norm_num)
theorem B1508453 : Blo 794341 1508453 := bbase (se 4 (by rfl) ⟨141417, by rfl⟩ : syracuseStep 1508453 = 282835) (by norm_num)
theorem B1344613 : Blo 794341 1344613 := bbase (se 4 (by rfl) ⟨126057, by rfl⟩ : syracuseStep 1344613 = 252115) (by norm_num)
theorem B2426021 : Blo 794341 2426021 := bbase (se 4 (by rfl) ⟨227439, by rfl⟩ : syracuseStep 2426021 = 454879) (by norm_num)
theorem B1344701 : Blo 794341 1344701 := bbase (se 3 (by rfl) ⟨252131, by rfl⟩ : syracuseStep 1344701 = 504263) (by norm_num)
theorem B2262293 : Blo 794341 2262293 := bbase (se 6 (by rfl) ⟨53022, by rfl⟩ : syracuseStep 2262293 = 106045) (by norm_num)
theorem B1344829 : Blo 794341 1344829 := bbase (se 3 (by rfl) ⟨252155, by rfl⟩ : syracuseStep 1344829 = 504311) (by norm_num)
theorem B2557253 : Blo 794341 2557253 := bbase (se 4 (by rfl) ⟨239742, by rfl⟩ : syracuseStep 2557253 = 479485) (by norm_num)
theorem B2295125 : Blo 794341 2295125 := bbase (se 12 (by rfl) ⟨840, by rfl⟩ : syracuseStep 2295125 = 1681) (by norm_num)
theorem B2688389 : Blo 794341 2688389 := bbase (se 4 (by rfl) ⟨252036, by rfl⟩ : syracuseStep 2688389 = 504073) (by norm_num)
theorem B1344917 : Blo 794341 1344917 := bbase (se 6 (by rfl) ⟨31521, by rfl⟩ : syracuseStep 1344917 = 63043) (by norm_num)
theorem B1934837 : Blo 794341 1934837 := bbase (se 5 (by rfl) ⟨90695, by rfl⟩ : syracuseStep 1934837 = 181391) (by norm_num)
theorem B3409397 : Blo 794341 3409397 := bbase (se 5 (by rfl) ⟨159815, by rfl⟩ : syracuseStep 3409397 = 319631) (by norm_num)
theorem B1345045 : Blo 794341 1345045 := bbase (se 6 (by rfl) ⟨31524, by rfl⟩ : syracuseStep 1345045 = 63049) (by norm_num)
theorem B1148509 : Blo 794341 1148509 := bbase (se 3 (by rfl) ⟨215345, by rfl⟩ : syracuseStep 1148509 = 430691) (by norm_num)
theorem B1345133 : Blo 794341 1345133 := bbase (se 3 (by rfl) ⟨252212, by rfl⟩ : syracuseStep 1345133 = 504425) (by norm_num)
theorem B2262725 : Blo 794341 2262725 := bbase (se 4 (by rfl) ⟨212130, by rfl⟩ : syracuseStep 2262725 = 424261) (by norm_num)
theorem B1345261 : Blo 794341 1345261 := bbase (se 3 (by rfl) ⟨252236, by rfl⟩ : syracuseStep 1345261 = 504473) (by norm_num)
theorem B2688821 : Blo 794341 2688821 := bbase (se 5 (by rfl) ⟨126038, by rfl⟩ : syracuseStep 2688821 = 252077) (by norm_num)
theorem B1345349 : Blo 794341 1345349 := bbase (se 4 (by rfl) ⟨126126, by rfl⟩ : syracuseStep 1345349 = 252253) (by norm_num)
theorem B1509205 : Blo 794341 1509205 := bbase (se 9 (by rfl) ⟨4421, by rfl⟩ : syracuseStep 1509205 = 8843) (by norm_num)
theorem B4032341 : Blo 794341 4032341 := bbase (se 9 (by rfl) ⟨11813, by rfl⟩ : syracuseStep 4032341 = 23627) (by norm_num)
theorem B5113685 : Blo 794341 5113685 := bbase (se 9 (by rfl) ⟨14981, by rfl⟩ : syracuseStep 5113685 = 29963) (by norm_num)
theorem B1345477 : Blo 794341 1345477 := bbase (se 4 (by rfl) ⟨126138, by rfl⟩ : syracuseStep 1345477 = 252277) (by norm_num)
theorem B1509349 : Blo 794341 1509349 := bbase (se 4 (by rfl) ⟨141501, by rfl⟩ : syracuseStep 1509349 = 283003) (by norm_num)
theorem B3016709 : Blo 794341 3016709 := bbase (se 4 (by rfl) ⟨282816, by rfl⟩ : syracuseStep 3016709 = 565633) (by norm_num)
theorem B13273109 : Blo 794341 13273109 := bbase (se 6 (by rfl) ⟨311088, by rfl⟩ : syracuseStep 13273109 = 622177) (by norm_num)
theorem B1345565 : Blo 794341 1345565 := bbase (se 3 (by rfl) ⟨252293, by rfl⟩ : syracuseStep 1345565 = 504587) (by norm_num)
theorem B3835957 : Blo 794341 3835957 := bbase (se 5 (by rfl) ⟨179810, by rfl⟩ : syracuseStep 3835957 = 359621) (by norm_num)
theorem B1935461 : Blo 794341 1935461 := bbase (se 4 (by rfl) ⟨181449, by rfl⟩ : syracuseStep 1935461 = 362899) (by norm_num)
theorem B1509509 : Blo 794341 1509509 := bbase (se 4 (by rfl) ⟨141516, by rfl⟩ : syracuseStep 1509509 = 283033) (by norm_num)
theorem B1345693 : Blo 794341 1345693 := bbase (se 3 (by rfl) ⟨252317, by rfl⟩ : syracuseStep 1345693 = 504635) (by norm_num)
theorem B919729 : Blo 794341 919729 := bbase (se 2 (by rfl) ⟨344898, by rfl⟩ : syracuseStep 919729 = 689797) (by norm_num)
theorem B2689253 : Blo 794341 2689253 := bbase (se 4 (by rfl) ⟨252117, by rfl⟩ : syracuseStep 2689253 = 504235) (by norm_num)
theorem B1345781 : Blo 794341 1345781 := bbase (se 5 (by rfl) ⟨63083, by rfl⟩ : syracuseStep 1345781 = 126167) (by norm_num)
theorem B1509653 : Blo 794341 1509653 := bbase (se 6 (by rfl) ⟨35382, by rfl⟩ : syracuseStep 1509653 = 70765) (by norm_num)
theorem B3016997 : Blo 794341 3016997 := bbase (se 4 (by rfl) ⟨282843, by rfl⟩ : syracuseStep 3016997 = 565687) (by norm_num)
theorem B2296117 : Blo 794341 2296117 := bbase (se 5 (by rfl) ⟨107630, by rfl⟩ : syracuseStep 2296117 = 215261) (by norm_num)
theorem B1837397 : Blo 794341 1837397 := bbase (se 10 (by rfl) ⟨2691, by rfl⟩ : syracuseStep 1837397 = 5383) (by norm_num)
theorem B1345909 : Blo 794341 1345909 := bbase (se 5 (by rfl) ⟨63089, by rfl⟩ : syracuseStep 1345909 = 126179) (by norm_num)
theorem B2263477 : Blo 794341 2263477 := bbase (se 5 (by rfl) ⟨106100, by rfl⟩ : syracuseStep 2263477 = 212201) (by norm_num)
theorem B1345997 : Blo 794341 1345997 := bbase (se 3 (by rfl) ⟨252374, by rfl⟩ : syracuseStep 1345997 = 504749) (by norm_num)
theorem B1935917 : Blo 794341 1935917 := bbase (se 3 (by rfl) ⟨362984, by rfl⟩ : syracuseStep 1935917 = 725969) (by norm_num)
theorem B1509941 : Blo 794341 1509941 := bbase (se 5 (by rfl) ⟨70778, by rfl⟩ : syracuseStep 1509941 = 141557) (by norm_num)
theorem B1346125 : Blo 794341 1346125 := bbase (se 3 (by rfl) ⟨252398, by rfl⟩ : syracuseStep 1346125 = 504797) (by norm_num)
theorem B1477205 : Blo 794341 1477205 := bbase (se 8 (by rfl) ⟨8655, by rfl⟩ : syracuseStep 1477205 = 17311) (by norm_num)
theorem B2689685 : Blo 794341 2689685 := bbase (se 6 (by rfl) ⟨63039, by rfl⟩ : syracuseStep 2689685 = 126079) (by norm_num)
theorem B1346213 : Blo 794341 1346213 := bbase (se 4 (by rfl) ⟨126207, by rfl⟩ : syracuseStep 1346213 = 252415) (by norm_num)
theorem B1510093 : Blo 794341 1510093 := bbase (se 3 (by rfl) ⟨283142, by rfl⟩ : syracuseStep 1510093 = 566285) (by norm_num)
theorem B1346341 : Blo 794341 1346341 := bbase (se 4 (by rfl) ⟨126219, by rfl⟩ : syracuseStep 1346341 = 252439) (by norm_num)
theorem B1346429 : Blo 794341 1346429 := bbase (se 3 (by rfl) ⟨252455, by rfl⟩ : syracuseStep 1346429 = 504911) (by norm_num)
theorem B1510397 : Blo 794341 1510397 := bbase (se 3 (by rfl) ⟨283199, by rfl⟩ : syracuseStep 1510397 = 566399) (by norm_num)
theorem B1346557 : Blo 794341 1346557 := bbase (se 3 (by rfl) ⟨252479, by rfl⟩ : syracuseStep 1346557 = 504959) (by norm_num)
theorem B2690117 : Blo 794341 2690117 := bbase (se 4 (by rfl) ⟨252198, by rfl⟩ : syracuseStep 2690117 = 504397) (by norm_num)
theorem B1346645 : Blo 794341 1346645 := bbase (se 8 (by rfl) ⟨7890, by rfl⟩ : syracuseStep 1346645 = 15781) (by norm_num)
theorem B4033637 : Blo 794341 4033637 := bbase (se 4 (by rfl) ⟨378153, by rfl⟩ : syracuseStep 4033637 = 756307) (by norm_num)
theorem B1346773 : Blo 794341 1346773 := bbase (se 7 (by rfl) ⟨15782, by rfl⟩ : syracuseStep 1346773 = 31565) (by norm_num)
theorem B3673349 : Blo 794341 3673349 := bbase (se 4 (by rfl) ⟨344376, by rfl⟩ : syracuseStep 3673349 = 688753) (by norm_num)
theorem B1346861 : Blo 794341 1346861 := bbase (se 3 (by rfl) ⟨252536, by rfl⟩ : syracuseStep 1346861 = 505073) (by norm_num)
theorem B1019209 : Blo 794341 1019209 := bbase (se 2 (by rfl) ⟨382203, by rfl⟩ : syracuseStep 1019209 = 764407) (by norm_num)
theorem B920965 : Blo 794341 920965 := bbase (se 4 (by rfl) ⟨86340, by rfl⟩ : syracuseStep 920965 = 172681) (by norm_num)
theorem B1346989 : Blo 794341 1346989 := bbase (se 3 (by rfl) ⟨252560, by rfl⟩ : syracuseStep 1346989 = 505121) (by norm_num)
theorem B3018181 : Blo 794341 3018181 := bbase (se 4 (by rfl) ⟨282954, by rfl⟩ : syracuseStep 3018181 = 565909) (by norm_num)
theorem B2690549 : Blo 794341 2690549 := bbase (se 5 (by rfl) ⟨126119, by rfl⟩ : syracuseStep 2690549 = 252239) (by norm_num)
theorem B1347077 : Blo 794341 1347077 := bbase (se 4 (by rfl) ⟨126288, by rfl⟩ : syracuseStep 1347077 = 252577) (by norm_num)
theorem B1511149 : Blo 794341 1511149 := bbase (se 3 (by rfl) ⟨283340, by rfl⟩ : syracuseStep 1511149 = 566681) (by norm_num)
theorem B3018485 : Blo 794341 3018485 := bbase (se 5 (by rfl) ⟨141491, by rfl⟩ : syracuseStep 3018485 = 282983) (by norm_num)
theorem B2723701 : Blo 794341 2723701 := bbase (se 5 (by rfl) ⟨127673, by rfl⟩ : syracuseStep 2723701 = 255347) (by norm_num)
theorem B1511293 : Blo 794341 1511293 := bbase (se 3 (by rfl) ⟨283367, by rfl⟩ : syracuseStep 1511293 = 566735) (by norm_num)
theorem B2690981 : Blo 794341 2690981 := bbase (se 4 (by rfl) ⟨252279, by rfl⟩ : syracuseStep 2690981 = 504559) (by norm_num)
theorem B1511453 : Blo 794341 1511453 := bbase (se 3 (by rfl) ⟨283397, by rfl⟩ : syracuseStep 1511453 = 566795) (by norm_num)
theorem B1511597 : Blo 794341 1511597 := bbase (se 3 (by rfl) ⟨283424, by rfl⟩ : syracuseStep 1511597 = 566849) (by norm_num)
theorem B22974677 : Blo 794341 22974677 := bbase (se 7 (by rfl) ⟨269234, by rfl⟩ : syracuseStep 22974677 = 538469) (by norm_num)
theorem B2691413 : Blo 794341 2691413 := bbase (se 10 (by rfl) ⟨3942, by rfl⟩ : syracuseStep 2691413 = 7885) (by norm_num)
theorem B954713 : Blo 794341 954713 := bbase (se 2 (by rfl) ⟨358017, by rfl⟩ : syracuseStep 954713 = 716035) (by norm_num)
theorem B4034933 : Blo 794341 4034933 := bbase (se 5 (by rfl) ⟨189137, by rfl⟩ : syracuseStep 4034933 = 378275) (by norm_num)
theorem B1511885 : Blo 794341 1511885 := bbase (se 3 (by rfl) ⟨283478, by rfl⟩ : syracuseStep 1511885 = 566957) (by norm_num)
theorem B922097 : Blo 794341 922097 := bbase (se 2 (by rfl) ⟨345786, by rfl⟩ : syracuseStep 922097 = 691573) (by norm_num)
theorem B1151581 : Blo 794341 1151581 := bbase (se 3 (by rfl) ⟨215921, by rfl⟩ : syracuseStep 1151581 = 431843) (by norm_num)
theorem B1512037 : Blo 794341 1512037 := bbase (se 4 (by rfl) ⟨141753, by rfl⟩ : syracuseStep 1512037 = 283507) (by norm_num)
theorem B1610381 : Blo 794341 1610381 := bbase (se 3 (by rfl) ⟨301946, by rfl⟩ : syracuseStep 1610381 = 603893) (by norm_num)
theorem B2691845 : Blo 794341 2691845 := bbase (se 4 (by rfl) ⟨252360, by rfl⟩ : syracuseStep 2691845 = 504721) (by norm_num)
theorem B1512341 : Blo 794341 1512341 := bbase (se 6 (by rfl) ⟨35445, by rfl⟩ : syracuseStep 1512341 = 70891) (by norm_num)
theorem B2102213 : Blo 794341 2102213 := bbase (se 4 (by rfl) ⟨197082, by rfl⟩ : syracuseStep 2102213 = 394165) (by norm_num)
theorem B955433 : Blo 794341 955433 := bbase (se 2 (by rfl) ⟨358287, by rfl⟩ : syracuseStep 955433 = 716575) (by norm_num)
theorem B2692277 : Blo 794341 2692277 := bbase (se 5 (by rfl) ⟨126200, by rfl⟩ : syracuseStep 2692277 = 252401) (by norm_num)
theorem B2266325 : Blo 794341 2266325 := bbase (se 7 (by rfl) ⟨26558, by rfl⟩ : syracuseStep 2266325 = 53117) (by norm_num)
theorem B955741 : Blo 794341 955741 := bbase (se 3 (by rfl) ⟨179201, by rfl⟩ : syracuseStep 955741 = 358403) (by norm_num)
theorem B955837 : Blo 794341 955837 := bbase (se 3 (by rfl) ⟨179219, by rfl⟩ : syracuseStep 955837 = 358439) (by norm_num)
theorem B955981 : Blo 794341 955981 := bbase (se 3 (by rfl) ⟨179246, by rfl⟩ : syracuseStep 955981 = 358493) (by norm_num)
theorem B2692709 : Blo 794341 2692709 := bbase (se 4 (by rfl) ⟨252441, by rfl⟩ : syracuseStep 2692709 = 504883) (by norm_num)
theorem B1513093 : Blo 794341 1513093 := bbase (se 4 (by rfl) ⟨141852, by rfl⟩ : syracuseStep 1513093 = 283705) (by norm_num)
theorem B4036229 : Blo 794341 4036229 := bbase (se 4 (by rfl) ⟨378396, by rfl⟩ : syracuseStep 4036229 = 756793) (by norm_num)
theorem B1513237 : Blo 794341 1513237 := bbase (se 6 (by rfl) ⟨35466, by rfl⟩ : syracuseStep 1513237 = 70933) (by norm_num)
theorem B3020597 : Blo 794341 3020597 := bbase (se 5 (by rfl) ⟨141590, by rfl⟩ : syracuseStep 3020597 = 283181) (by norm_num)
theorem B1513397 : Blo 794341 1513397 := bbase (se 5 (by rfl) ⟨70940, by rfl⟩ : syracuseStep 1513397 = 141881) (by norm_num)
theorem B2693141 : Blo 794341 2693141 := bbase (se 6 (by rfl) ⟨63120, by rfl⟩ : syracuseStep 2693141 = 126241) (by norm_num)
theorem B1513541 : Blo 794341 1513541 := bbase (se 4 (by rfl) ⟨141894, by rfl⟩ : syracuseStep 1513541 = 283789) (by norm_num)
theorem B3020885 : Blo 794341 3020885 := bbase (se 8 (by rfl) ⟨17700, by rfl⟩ : syracuseStep 3020885 = 35401) (by norm_num)
theorem B1022041 : Blo 794341 1022041 := bbase (se 2 (by rfl) ⟨383265, by rfl⟩ : syracuseStep 1022041 = 766531) (by norm_num)
theorem B5445845 : Blo 794341 5445845 := bbase (se 7 (by rfl) ⟨63818, by rfl⟩ : syracuseStep 5445845 = 127637) (by norm_num)
theorem B1022209 : Blo 794341 1022209 := bbase (se 2 (by rfl) ⟨383328, by rfl⟩ : syracuseStep 1022209 = 766657) (by norm_num)
theorem B1513829 : Blo 794341 1513829 := bbase (se 4 (by rfl) ⟨141921, by rfl⟩ : syracuseStep 1513829 = 283843) (by norm_num)
theorem B2267509 : Blo 794341 2267509 := bbase (se 5 (by rfl) ⟨106289, by rfl⟩ : syracuseStep 2267509 = 212579) (by norm_num)
theorem B2693573 : Blo 794341 2693573 := bbase (se 4 (by rfl) ⟨252522, by rfl⟩ : syracuseStep 2693573 = 505045) (by norm_num)
theorem B1513981 : Blo 794341 1513981 := bbase (se 3 (by rfl) ⟨283871, by rfl⟩ : syracuseStep 1513981 = 567743) (by norm_num)
theorem B2267669 : Blo 794341 2267669 := bbase (se 6 (by rfl) ⟨53148, by rfl⟩ : syracuseStep 2267669 = 106297) (by norm_num)
theorem B956981 : Blo 794341 956981 := bbase (se 5 (by rfl) ⟨44858, by rfl⟩ : syracuseStep 956981 = 89717) (by norm_num)
theorem B2267909 : Blo 794341 2267909 := bbase (se 4 (by rfl) ⟨212616, by rfl⟩ : syracuseStep 2267909 = 425233) (by norm_num)
theorem B1514285 : Blo 794341 1514285 := bbase (se 3 (by rfl) ⟨283928, by rfl⟩ : syracuseStep 1514285 = 567857) (by norm_num)
theorem B10197845 : Blo 794341 10197845 := bbase (se 9 (by rfl) ⟨29876, by rfl⟩ : syracuseStep 10197845 = 59753) (by norm_num)
theorem B2694005 : Blo 794341 2694005 := bbase (se 5 (by rfl) ⟨126281, by rfl⟩ : syracuseStep 2694005 = 252563) (by norm_num)
theorem B4037525 : Blo 794341 4037525 := bbase (se 6 (by rfl) ⟨94629, by rfl⟩ : syracuseStep 4037525 = 189259) (by norm_num)
theorem B2268101 : Blo 794341 2268101 := bbase (se 4 (by rfl) ⟨212634, by rfl⟩ : syracuseStep 2268101 = 425269) (by norm_num)
theorem B2104301 : Blo 794341 2104301 := bbase (se 3 (by rfl) ⟨394556, by rfl⟩ : syracuseStep 2104301 = 789113) (by norm_num)
theorem B4529141 : Blo 794341 4529141 := bbase (se 5 (by rfl) ⟨212303, by rfl⟩ : syracuseStep 4529141 = 424607) (by norm_num)
theorem B1612877 : Blo 794341 1612877 := bbase (se 3 (by rfl) ⟨302414, by rfl⟩ : syracuseStep 1612877 = 604829) (by norm_num)
theorem B1940701 : Blo 794341 1940701 := bbase (se 3 (by rfl) ⟨363881, by rfl⟩ : syracuseStep 1940701 = 727763) (by norm_num)
theorem B957673 : Blo 794341 957673 := bbase (se 2 (by rfl) ⟨359127, by rfl⟩ : syracuseStep 957673 = 718255) (by norm_num)
theorem B3022069 : Blo 794341 3022069 := bbase (se 5 (by rfl) ⟨141659, by rfl⟩ : syracuseStep 3022069 = 283319) (by norm_num)
theorem B1023277 : Blo 794341 1023277 := bbase (se 3 (by rfl) ⟨191864, by rfl⟩ : syracuseStep 1023277 = 383729) (by norm_num)
theorem B2039165 : Blo 794341 2039165 := bbase (se 3 (by rfl) ⟨382343, by rfl⟩ : syracuseStep 2039165 = 764687) (by norm_num)
theorem B957889 : Blo 794341 957889 := bbase (se 2 (by rfl) ⟨359208, by rfl⟩ : syracuseStep 957889 = 718417) (by norm_num)
theorem B1515037 : Blo 794341 1515037 := bbase (se 3 (by rfl) ⟨284069, by rfl⟩ : syracuseStep 1515037 = 568139) (by norm_num)
theorem B3022373 : Blo 794341 3022373 := bbase (se 4 (by rfl) ⟨283347, by rfl⟩ : syracuseStep 3022373 = 566695) (by norm_num)
theorem B1515181 : Blo 794341 1515181 := bbase (se 3 (by rfl) ⟨284096, by rfl⟩ : syracuseStep 1515181 = 568193) (by norm_num)
theorem B6463253 : Blo 794341 6463253 := bbase (se 6 (by rfl) ⟨151482, by rfl⟩ : syracuseStep 6463253 = 302965) (by norm_num)
theorem B1515341 : Blo 794341 1515341 := bbase (se 3 (by rfl) ⟨284126, by rfl⟩ : syracuseStep 1515341 = 568253) (by norm_num)
theorem B1908629 : Blo 794341 1908629 := bbase (se 6 (by rfl) ⟨44733, by rfl⟩ : syracuseStep 1908629 = 89467) (by norm_num)
theorem B2269093 : Blo 794341 2269093 := bbase (se 4 (by rfl) ⟨212727, by rfl⟩ : syracuseStep 2269093 = 425455) (by norm_num)
theorem B1515485 : Blo 794341 1515485 := bbase (se 3 (by rfl) ⟨284153, by rfl⟩ : syracuseStep 1515485 = 568307) (by norm_num)
theorem B1613981 : Blo 794341 1613981 := bbase (se 3 (by rfl) ⟨302621, by rfl⟩ : syracuseStep 1613981 = 605243) (by norm_num)
theorem B4038821 : Blo 794341 4038821 := bbase (se 4 (by rfl) ⟨378639, by rfl⟩ : syracuseStep 4038821 = 757279) (by norm_num)
theorem B1909021 : Blo 794341 1909021 := bbase (se 3 (by rfl) ⟨357941, by rfl⟩ : syracuseStep 1909021 = 715883) (by norm_num)
theorem B893641 : Blo 794341 893641 := bbase (se 2 (by rfl) ⟨335115, by rfl⟩ : syracuseStep 893641 = 670231) (by norm_num)
theorem B4301525 : Blo 794341 4301525 := bbase (se 7 (by rfl) ⟨50408, by rfl⟩ : syracuseStep 4301525 = 100817) (by norm_num)
theorem B893677 : Blo 794341 893677 := bbase (se 3 (by rfl) ⟨167564, by rfl⟩ : syracuseStep 893677 = 335129) (by norm_num)
theorem B893713 : Blo 794341 893713 := bbase (se 2 (by rfl) ⟨335142, by rfl⟩ : syracuseStep 893713 = 670285) (by norm_num)
theorem B893749 : Blo 794341 893749 := bbase (se 5 (by rfl) ⟨41894, by rfl⟩ : syracuseStep 893749 = 83789) (by norm_num)
theorem B893785 : Blo 794341 893785 := bbase (se 2 (by rfl) ⟨335169, by rfl⟩ : syracuseStep 893785 = 670339) (by norm_num)
theorem B893821 : Blo 794341 893821 := bbase (se 3 (by rfl) ⟨167591, by rfl⟩ : syracuseStep 893821 = 335183) (by norm_num)
theorem B893857 : Blo 794341 893857 := bbase (se 2 (by rfl) ⟨335196, by rfl⟩ : syracuseStep 893857 = 670393) (by norm_num)
theorem B893893 : Blo 794341 893893 := bbase (se 4 (by rfl) ⟨83802, by rfl⟩ : syracuseStep 893893 = 167605) (by norm_num)
theorem B893929 : Blo 794341 893929 := bbase (se 2 (by rfl) ⟨335223, by rfl⟩ : syracuseStep 893929 = 670447) (by norm_num)
theorem B2270197 : Blo 794341 2270197 := bbase (se 5 (by rfl) ⟨106415, by rfl⟩ : syracuseStep 2270197 = 212831) (by norm_num)
theorem B893965 : Blo 794341 893965 := bbase (se 3 (by rfl) ⟨167618, by rfl⟩ : syracuseStep 893965 = 335237) (by norm_num)
theorem B6038549 : Blo 794341 6038549 := bbase (se 6 (by rfl) ⟨141528, by rfl⟩ : syracuseStep 6038549 = 283057) (by norm_num)
theorem B894001 : Blo 794341 894001 := bbase (se 2 (by rfl) ⟨335250, by rfl⟩ : syracuseStep 894001 = 670501) (by norm_num)
theorem B894037 : Blo 794341 894037 := bbase (se 8 (by rfl) ⟨5238, by rfl⟩ : syracuseStep 894037 = 10477) (by norm_num)
theorem B894073 : Blo 794341 894073 := bbase (se 2 (by rfl) ⟨335277, by rfl⟩ : syracuseStep 894073 = 670555) (by norm_num)
theorem B894109 : Blo 794341 894109 := bbase (se 3 (by rfl) ⟨167645, by rfl⟩ : syracuseStep 894109 = 335291) (by norm_num)
theorem B894145 : Blo 794341 894145 := bbase (se 2 (by rfl) ⟨335304, by rfl⟩ : syracuseStep 894145 = 670609) (by norm_num)
theorem B894181 : Blo 794341 894181 := bbase (se 4 (by rfl) ⟨83829, by rfl⟩ : syracuseStep 894181 = 167659) (by norm_num)
theorem B2073853 : Blo 794341 2073853 := bbase (se 3 (by rfl) ⟨388847, by rfl⟩ : syracuseStep 2073853 = 777695) (by norm_num)
theorem B894217 : Blo 794341 894217 := bbase (se 2 (by rfl) ⟨335331, by rfl⟩ : syracuseStep 894217 = 670663) (by norm_num)
theorem B894253 : Blo 794341 894253 := bbase (se 3 (by rfl) ⟨167672, by rfl⟩ : syracuseStep 894253 = 335345) (by norm_num)
theorem B894289 : Blo 794341 894289 := bbase (se 2 (by rfl) ⟨335358, by rfl⟩ : syracuseStep 894289 = 670717) (by norm_num)
theorem B1910117 : Blo 794341 1910117 := bbase (se 4 (by rfl) ⟨179073, by rfl⟩ : syracuseStep 1910117 = 358147) (by norm_num)
theorem B894325 : Blo 794341 894325 := bbase (se 5 (by rfl) ⟨41921, by rfl⟩ : syracuseStep 894325 = 83843) (by norm_num)
theorem B894361 : Blo 794341 894361 := bbase (se 2 (by rfl) ⟨335385, by rfl⟩ : syracuseStep 894361 = 670771) (by norm_num)
theorem B4040117 : Blo 794341 4040117 := bbase (se 5 (by rfl) ⟨189380, by rfl⟩ : syracuseStep 4040117 = 378761) (by norm_num)
theorem B894397 : Blo 794341 894397 := bbase (se 3 (by rfl) ⟨167699, by rfl⟩ : syracuseStep 894397 = 335399) (by norm_num)
theorem B894433 : Blo 794341 894433 := bbase (se 2 (by rfl) ⟨335412, by rfl⟩ : syracuseStep 894433 = 670825) (by norm_num)
theorem B894469 : Blo 794341 894469 := bbase (se 4 (by rfl) ⟨83856, by rfl⟩ : syracuseStep 894469 = 167713) (by norm_num)
theorem B2041381 : Blo 794341 2041381 := bbase (se 4 (by rfl) ⟨191379, by rfl⟩ : syracuseStep 2041381 = 382759) (by norm_num)
theorem B894505 : Blo 794341 894505 := bbase (se 2 (by rfl) ⟨335439, by rfl⟩ : syracuseStep 894505 = 670879) (by norm_num)
theorem B894541 : Blo 794341 894541 := bbase (se 3 (by rfl) ⟨167726, by rfl⟩ : syracuseStep 894541 = 335453) (by norm_num)
theorem B3024485 : Blo 794341 3024485 := bbase (se 4 (by rfl) ⟨283545, by rfl⟩ : syracuseStep 3024485 = 567091) (by norm_num)
theorem B894577 : Blo 794341 894577 := bbase (se 2 (by rfl) ⟨335466, by rfl⟩ : syracuseStep 894577 = 670933) (by norm_num)
theorem B1910405 : Blo 794341 1910405 := bbase (se 4 (by rfl) ⟨179100, by rfl⟩ : syracuseStep 1910405 = 358201) (by norm_num)
theorem B894613 : Blo 794341 894613 := bbase (se 6 (by rfl) ⟨20967, by rfl⟩ : syracuseStep 894613 = 41935) (by norm_num)
theorem B894649 : Blo 794341 894649 := bbase (se 2 (by rfl) ⟨335493, by rfl⟩ : syracuseStep 894649 = 670987) (by norm_num)
theorem B894685 : Blo 794341 894685 := bbase (se 3 (by rfl) ⟨167753, by rfl⟩ : syracuseStep 894685 = 335507) (by norm_num)
theorem B894721 : Blo 794341 894721 := bbase (se 2 (by rfl) ⟨335520, by rfl⟩ : syracuseStep 894721 = 671041) (by norm_num)
theorem B894757 : Blo 794341 894757 := bbase (se 4 (by rfl) ⟨83883, by rfl⟩ : syracuseStep 894757 = 167767) (by norm_num)
theorem B894793 : Blo 794341 894793 := bbase (se 2 (by rfl) ⟨335547, by rfl⟩ : syracuseStep 894793 = 671095) (by norm_num)
theorem B894829 : Blo 794341 894829 := bbase (se 3 (by rfl) ⟨167780, by rfl⟩ : syracuseStep 894829 = 335561) (by norm_num)
theorem B3024773 : Blo 794341 3024773 := bbase (se 4 (by rfl) ⟨283572, by rfl⟩ : syracuseStep 3024773 = 567145) (by norm_num)
theorem B894865 : Blo 794341 894865 := bbase (se 2 (by rfl) ⟨335574, by rfl⟩ : syracuseStep 894865 = 671149) (by norm_num)
theorem B894901 : Blo 794341 894901 := bbase (se 5 (by rfl) ⟨41948, by rfl⟩ : syracuseStep 894901 = 83897) (by norm_num)
theorem B1943477 : Blo 794341 1943477 := bbase (se 5 (by rfl) ⟨91100, by rfl⟩ : syracuseStep 1943477 = 182201) (by norm_num)
theorem B894937 : Blo 794341 894937 := bbase (se 2 (by rfl) ⟨335601, by rfl⟩ : syracuseStep 894937 = 671203) (by norm_num)
theorem B894973 : Blo 794341 894973 := bbase (se 3 (by rfl) ⟨167807, by rfl⟩ : syracuseStep 894973 = 335615) (by norm_num)
theorem B895009 : Blo 794341 895009 := bbase (se 2 (by rfl) ⟨335628, by rfl⟩ : syracuseStep 895009 = 671257) (by norm_num)
theorem B895045 : Blo 794341 895045 := bbase (se 4 (by rfl) ⟨83910, by rfl⟩ : syracuseStep 895045 = 167821) (by norm_num)
theorem B895081 : Blo 794341 895081 := bbase (se 2 (by rfl) ⟨335655, by rfl⟩ : syracuseStep 895081 = 671311) (by norm_num)
theorem B895117 : Blo 794341 895117 := bbase (se 3 (by rfl) ⟨167834, by rfl⟩ : syracuseStep 895117 = 335669) (by norm_num)
theorem B895153 : Blo 794341 895153 := bbase (se 2 (by rfl) ⟨335682, by rfl⟩ : syracuseStep 895153 = 671365) (by norm_num)
theorem B895189 : Blo 794341 895189 := bbase (se 7 (by rfl) ⟨10490, by rfl⟩ : syracuseStep 895189 = 20981) (by norm_num)
theorem B895225 : Blo 794341 895225 := bbase (se 2 (by rfl) ⟨335709, by rfl⟩ : syracuseStep 895225 = 671419) (by norm_num)
theorem B895261 : Blo 794341 895261 := bbase (se 3 (by rfl) ⟨167861, by rfl⟩ : syracuseStep 895261 = 335723) (by norm_num)
theorem B3451189 : Blo 794341 3451189 := bbase (se 5 (by rfl) ⟨161774, by rfl⟩ : syracuseStep 3451189 = 323549) (by norm_num)
theorem B895297 : Blo 794341 895297 := bbase (se 2 (by rfl) ⟨335736, by rfl⟩ : syracuseStep 895297 = 671473) (by norm_num)
theorem B895333 : Blo 794341 895333 := bbase (se 4 (by rfl) ⟨83937, by rfl⟩ : syracuseStep 895333 = 167875) (by norm_num)
theorem B1845605 : Blo 794341 1845605 := bbase (se 4 (by rfl) ⟨173025, by rfl⟩ : syracuseStep 1845605 = 346051) (by norm_num)
theorem B895369 : Blo 794341 895369 := bbase (se 2 (by rfl) ⟨335763, by rfl⟩ : syracuseStep 895369 = 671527) (by norm_num)
theorem B895405 : Blo 794341 895405 := bbase (se 3 (by rfl) ⟨167888, by rfl⟩ : syracuseStep 895405 = 335777) (by norm_num)
theorem B895441 : Blo 794341 895441 := bbase (se 2 (by rfl) ⟨335790, by rfl⟩ : syracuseStep 895441 = 671581) (by norm_num)
theorem B2271701 : Blo 794341 2271701 := bbase (se 7 (by rfl) ⟨26621, by rfl⟩ : syracuseStep 2271701 = 53243) (by norm_num)
theorem B895477 : Blo 794341 895477 := bbase (se 5 (by rfl) ⟨41975, by rfl⟩ : syracuseStep 895477 = 83951) (by norm_num)
theorem B895513 : Blo 794341 895513 := bbase (se 2 (by rfl) ⟨335817, by rfl⟩ : syracuseStep 895513 = 671635) (by norm_num)
theorem B1944101 : Blo 794341 1944101 := bbase (se 4 (by rfl) ⟨182259, by rfl⟩ : syracuseStep 1944101 = 364519) (by norm_num)
theorem B895549 : Blo 794341 895549 := bbase (se 3 (by rfl) ⟨167915, by rfl⟩ : syracuseStep 895549 = 335831) (by norm_num)
theorem B895585 : Blo 794341 895585 := bbase (se 2 (by rfl) ⟨335844, by rfl⟩ : syracuseStep 895585 = 671689) (by norm_num)
theorem B895621 : Blo 794341 895621 := bbase (se 4 (by rfl) ⟨83964, by rfl⟩ : syracuseStep 895621 = 167929) (by norm_num)
theorem B895657 : Blo 794341 895657 := bbase (se 2 (by rfl) ⟨335871, by rfl⟩ : syracuseStep 895657 = 671743) (by norm_num)
theorem B4041413 : Blo 794341 4041413 := bbase (se 4 (by rfl) ⟨378882, by rfl⟩ : syracuseStep 4041413 = 757765) (by norm_num)
theorem B895693 : Blo 794341 895693 := bbase (se 3 (by rfl) ⟨167942, by rfl⟩ : syracuseStep 895693 = 335885) (by norm_num)
theorem B895729 : Blo 794341 895729 := bbase (se 2 (by rfl) ⟨335898, by rfl⟩ : syracuseStep 895729 = 671797) (by norm_num)
theorem B895765 : Blo 794341 895765 := bbase (se 6 (by rfl) ⟨20994, by rfl⟩ : syracuseStep 895765 = 41989) (by norm_num)
theorem B895801 : Blo 794341 895801 := bbase (se 2 (by rfl) ⟨335925, by rfl⟩ : syracuseStep 895801 = 671851) (by norm_num)
theorem B895837 : Blo 794341 895837 := bbase (se 3 (by rfl) ⟨167969, by rfl⟩ : syracuseStep 895837 = 335939) (by norm_num)
theorem B895873 : Blo 794341 895873 := bbase (se 2 (by rfl) ⟨335952, by rfl⟩ : syracuseStep 895873 = 671905) (by norm_num)
theorem B1682317 : Blo 794341 1682317 := bbase (se 3 (by rfl) ⟨315434, by rfl⟩ : syracuseStep 1682317 = 630869) (by norm_num)
theorem B1092509 : Blo 794341 1092509 := bbase (se 3 (by rfl) ⟨204845, by rfl⟩ : syracuseStep 1092509 = 409691) (by norm_num)
theorem B895909 : Blo 794341 895909 := bbase (se 4 (by rfl) ⟨83991, by rfl⟩ : syracuseStep 895909 = 167983) (by norm_num)
theorem B895945 : Blo 794341 895945 := bbase (se 2 (by rfl) ⟨335979, by rfl⟩ : syracuseStep 895945 = 671959) (by norm_num)
theorem B895981 : Blo 794341 895981 := bbase (se 3 (by rfl) ⟨167996, by rfl⟩ : syracuseStep 895981 = 335993) (by norm_num)
theorem B896017 : Blo 794341 896017 := bbase (se 2 (by rfl) ⟨336006, by rfl⟩ : syracuseStep 896017 = 672013) (by norm_num)
theorem B3025957 : Blo 794341 3025957 := bbase (se 4 (by rfl) ⟨283683, by rfl⟩ : syracuseStep 3025957 = 567367) (by norm_num)
theorem B896053 : Blo 794341 896053 := bbase (se 5 (by rfl) ⟨42002, by rfl⟩ : syracuseStep 896053 = 84005) (by norm_num)
theorem B896089 : Blo 794341 896089 := bbase (se 2 (by rfl) ⟨336033, by rfl⟩ : syracuseStep 896089 = 672067) (by norm_num)
theorem B896125 : Blo 794341 896125 := bbase (se 3 (by rfl) ⟨168023, by rfl⟩ : syracuseStep 896125 = 336047) (by norm_num)
theorem B896161 : Blo 794341 896161 := bbase (se 2 (by rfl) ⟨336060, by rfl⟩ : syracuseStep 896161 = 672121) (by norm_num)
theorem B896197 : Blo 794341 896197 := bbase (se 4 (by rfl) ⟨84018, by rfl⟩ : syracuseStep 896197 = 168037) (by norm_num)
theorem B3058901 : Blo 794341 3058901 := bbase (se 7 (by rfl) ⟨35846, by rfl⟩ : syracuseStep 3058901 = 71693) (by norm_num)
theorem B896233 : Blo 794341 896233 := bbase (se 2 (by rfl) ⟨336087, by rfl⟩ : syracuseStep 896233 = 672175) (by norm_num)
theorem B3222773 : Blo 794341 3222773 := bbase (se 5 (by rfl) ⟨151067, by rfl⟩ : syracuseStep 3222773 = 302135) (by norm_num)
theorem B1813757 : Blo 794341 1813757 := bbase (se 3 (by rfl) ⟨340079, by rfl⟩ : syracuseStep 1813757 = 680159) (by norm_num)
theorem B896269 : Blo 794341 896269 := bbase (se 3 (by rfl) ⟨168050, by rfl⟩ : syracuseStep 896269 = 336101) (by norm_num)
theorem B896305 : Blo 794341 896305 := bbase (se 2 (by rfl) ⟨336114, by rfl⟩ : syracuseStep 896305 = 672229) (by norm_num)
theorem B896341 : Blo 794341 896341 := bbase (se 11 (by rfl) ⟨656, by rfl⟩ : syracuseStep 896341 = 1313) (by norm_num)
theorem B3026261 : Blo 794341 3026261 := bbase (se 11 (by rfl) ⟨2216, by rfl⟩ : syracuseStep 3026261 = 4433) (by norm_num)
theorem B896377 : Blo 794341 896377 := bbase (se 2 (by rfl) ⟨336141, by rfl⟩ : syracuseStep 896377 = 672283) (by norm_num)
theorem B9055637 : Blo 794341 9055637 := bbase (se 6 (by rfl) ⟨212241, by rfl⟩ : syracuseStep 9055637 = 424483) (by norm_num)
theorem B896413 : Blo 794341 896413 := bbase (se 3 (by rfl) ⟨168077, by rfl⟩ : syracuseStep 896413 = 336155) (by norm_num)
theorem B896449 : Blo 794341 896449 := bbase (se 2 (by rfl) ⟨336168, by rfl⟩ : syracuseStep 896449 = 672337) (by norm_num)
theorem B896485 : Blo 794341 896485 := bbase (se 4 (by rfl) ⟨84045, by rfl⟩ : syracuseStep 896485 = 168091) (by norm_num)
theorem B896521 : Blo 794341 896521 := bbase (se 2 (by rfl) ⟨336195, by rfl⟩ : syracuseStep 896521 = 672391) (by norm_num)
theorem B3452453 : Blo 794341 3452453 := bbase (se 4 (by rfl) ⟨323667, by rfl⟩ : syracuseStep 3452453 = 647335) (by norm_num)
theorem B896557 : Blo 794341 896557 := bbase (se 3 (by rfl) ⟨168104, by rfl⟩ : syracuseStep 896557 = 336209) (by norm_num)
theorem B896593 : Blo 794341 896593 := bbase (se 2 (by rfl) ⟨336222, by rfl⟩ : syracuseStep 896593 = 672445) (by norm_num)
theorem B831061 : Blo 794341 831061 := bbase (se 8 (by rfl) ⟨4869, by rfl⟩ : syracuseStep 831061 = 9739) (by norm_num)
theorem B1191533 : Blo 794341 1191533 := bbase (se 3 (by rfl) ⟨223412, by rfl⟩ : syracuseStep 1191533 = 446825) (by norm_num)
theorem B896629 : Blo 794341 896629 := bbase (se 5 (by rfl) ⟨42029, by rfl⟩ : syracuseStep 896629 = 84059) (by norm_num)
theorem B1191557 : Blo 794341 1191557 := bbase (se 4 (by rfl) ⟨111708, by rfl⟩ : syracuseStep 1191557 = 223417) (by norm_num)
theorem B896665 : Blo 794341 896665 := bbase (se 2 (by rfl) ⟨336249, by rfl⟩ : syracuseStep 896665 = 672499) (by norm_num)
theorem B1191581 : Blo 794341 1191581 := bbase (se 3 (by rfl) ⟨223421, by rfl⟩ : syracuseStep 1191581 = 446843) (by norm_num)
theorem B1191605 : Blo 794341 1191605 := bbase (se 5 (by rfl) ⟨55856, by rfl⟩ : syracuseStep 1191605 = 111713) (by norm_num)
theorem B1814197 : Blo 794341 1814197 := bbase (se 5 (by rfl) ⟨85040, by rfl⟩ : syracuseStep 1814197 = 170081) (by norm_num)
theorem B1912501 : Blo 794341 1912501 := bbase (se 5 (by rfl) ⟨89648, by rfl⟩ : syracuseStep 1912501 = 179297) (by norm_num)
theorem B896701 : Blo 794341 896701 := bbase (se 3 (by rfl) ⟨168131, by rfl⟩ : syracuseStep 896701 = 336263) (by norm_num)
theorem B1191629 : Blo 794341 1191629 := bbase (se 3 (by rfl) ⟨223430, by rfl⟩ : syracuseStep 1191629 = 446861) (by norm_num)
theorem B2010845 : Blo 794341 2010845 := bbase (se 3 (by rfl) ⟨377033, by rfl⟩ : syracuseStep 2010845 = 754067) (by norm_num)
theorem B896737 : Blo 794341 896737 := bbase (se 2 (by rfl) ⟨336276, by rfl⟩ : syracuseStep 896737 = 672553) (by norm_num)
theorem B1191653 : Blo 794341 1191653 := bbase (se 4 (by rfl) ⟨111717, by rfl⟩ : syracuseStep 1191653 = 223435) (by norm_num)
theorem B1191677 : Blo 794341 1191677 := bbase (se 3 (by rfl) ⟨223439, by rfl⟩ : syracuseStep 1191677 = 446879) (by norm_num)
theorem B896773 : Blo 794341 896773 := bbase (se 4 (by rfl) ⟨84072, by rfl⟩ : syracuseStep 896773 = 168145) (by norm_num)
theorem B1191701 : Blo 794341 1191701 := bbase (se 6 (by rfl) ⟨27930, by rfl⟩ : syracuseStep 1191701 = 55861) (by norm_num)
theorem B896809 : Blo 794341 896809 := bbase (se 2 (by rfl) ⟨336303, by rfl⟩ : syracuseStep 896809 = 672607) (by norm_num)
theorem B1191725 : Blo 794341 1191725 := bbase (se 3 (by rfl) ⟨223448, by rfl⟩ : syracuseStep 1191725 = 446897) (by norm_num)
theorem B1191749 : Blo 794341 1191749 := bbase (se 4 (by rfl) ⟨111726, by rfl⟩ : syracuseStep 1191749 = 223453) (by norm_num)
theorem B896845 : Blo 794341 896845 := bbase (se 3 (by rfl) ⟨168158, by rfl⟩ : syracuseStep 896845 = 336317) (by norm_num)
theorem B1191773 : Blo 794341 1191773 := bbase (se 3 (by rfl) ⟨223457, by rfl⟩ : syracuseStep 1191773 = 446915) (by norm_num)
theorem B896881 : Blo 794341 896881 := bbase (se 2 (by rfl) ⟨336330, by rfl⟩ : syracuseStep 896881 = 672661) (by norm_num)
theorem B1191797 : Blo 794341 1191797 := bbase (se 5 (by rfl) ⟨55865, by rfl⟩ : syracuseStep 1191797 = 111731) (by norm_num)
theorem B1191821 : Blo 794341 1191821 := bbase (se 3 (by rfl) ⟨223466, by rfl⟩ : syracuseStep 1191821 = 446933) (by norm_num)
theorem B896917 : Blo 794341 896917 := bbase (se 6 (by rfl) ⟨21021, by rfl⟩ : syracuseStep 896917 = 42043) (by norm_num)
theorem B1191845 : Blo 794341 1191845 := bbase (se 4 (by rfl) ⟨111735, by rfl⟩ : syracuseStep 1191845 = 223471) (by norm_num)
theorem B896953 : Blo 794341 896953 := bbase (se 2 (by rfl) ⟨336357, by rfl⟩ : syracuseStep 896953 = 672715) (by norm_num)
theorem B1191869 : Blo 794341 1191869 := bbase (se 3 (by rfl) ⟨223475, by rfl⟩ : syracuseStep 1191869 = 446951) (by norm_num)
theorem B1191893 : Blo 794341 1191893 := bbase (se 7 (by rfl) ⟨13967, by rfl⟩ : syracuseStep 1191893 = 27935) (by norm_num)
theorem B1224661 : Blo 794341 1224661 := bbase (se 7 (by rfl) ⟨14351, by rfl⟩ : syracuseStep 1224661 = 28703) (by norm_num)
theorem B896989 : Blo 794341 896989 := bbase (se 3 (by rfl) ⟨168185, by rfl⟩ : syracuseStep 896989 = 336371) (by norm_num)
theorem B1191917 : Blo 794341 1191917 := bbase (se 3 (by rfl) ⟨223484, by rfl⟩ : syracuseStep 1191917 = 446969) (by norm_num)
theorem B897025 : Blo 794341 897025 := bbase (se 2 (by rfl) ⟨336384, by rfl⟩ : syracuseStep 897025 = 672769) (by norm_num)
theorem B1191941 : Blo 794341 1191941 := bbase (se 4 (by rfl) ⟨111744, by rfl⟩ : syracuseStep 1191941 = 223489) (by norm_num)
theorem B2273285 : Blo 794341 2273285 := bbase (se 4 (by rfl) ⟨213120, by rfl⟩ : syracuseStep 2273285 = 426241) (by norm_num)
theorem B1191965 : Blo 794341 1191965 := bbase (se 3 (by rfl) ⟨223493, by rfl⟩ : syracuseStep 1191965 = 446987) (by norm_num)
theorem B897061 : Blo 794341 897061 := bbase (se 4 (by rfl) ⟨84099, by rfl⟩ : syracuseStep 897061 = 168199) (by norm_num)
theorem B2011189 : Blo 794341 2011189 := bbase (se 5 (by rfl) ⟨94274, by rfl⟩ : syracuseStep 2011189 = 188549) (by norm_num)
theorem B1191989 : Blo 794341 1191989 := bbase (se 5 (by rfl) ⟨55874, by rfl⟩ : syracuseStep 1191989 = 111749) (by norm_num)
theorem B897097 : Blo 794341 897097 := bbase (se 2 (by rfl) ⟨336411, by rfl⟩ : syracuseStep 897097 = 672823) (by norm_num)
theorem B1192013 : Blo 794341 1192013 := bbase (se 3 (by rfl) ⟨223502, by rfl⟩ : syracuseStep 1192013 = 447005) (by norm_num)
theorem B1192037 : Blo 794341 1192037 := bbase (se 4 (by rfl) ⟨111753, by rfl⟩ : syracuseStep 1192037 = 223507) (by norm_num)
theorem B897133 : Blo 794341 897133 := bbase (se 3 (by rfl) ⟨168212, by rfl⟩ : syracuseStep 897133 = 336425) (by norm_num)
theorem B1192061 : Blo 794341 1192061 := bbase (se 3 (by rfl) ⟨223511, by rfl⟩ : syracuseStep 1192061 = 447023) (by norm_num)
theorem B897169 : Blo 794341 897169 := bbase (se 2 (by rfl) ⟨336438, by rfl⟩ : syracuseStep 897169 = 672877) (by norm_num)
theorem B1192085 : Blo 794341 1192085 := bbase (se 6 (by rfl) ⟨27939, by rfl⟩ : syracuseStep 1192085 = 55879) (by norm_num)
theorem B2011301 : Blo 794341 2011301 := bbase (se 4 (by rfl) ⟨188559, by rfl⟩ : syracuseStep 2011301 = 377119) (by norm_num)
theorem B1192109 : Blo 794341 1192109 := bbase (se 3 (by rfl) ⟨223520, by rfl⟩ : syracuseStep 1192109 = 447041) (by norm_num)
theorem B897205 : Blo 794341 897205 := bbase (se 5 (by rfl) ⟨42056, by rfl⟩ : syracuseStep 897205 = 84113) (by norm_num)
theorem B1192133 : Blo 794341 1192133 := bbase (se 4 (by rfl) ⟨111762, by rfl⟩ : syracuseStep 1192133 = 223525) (by norm_num)
theorem B897241 : Blo 794341 897241 := bbase (se 2 (by rfl) ⟨336465, by rfl⟩ : syracuseStep 897241 = 672931) (by norm_num)
theorem B1192157 : Blo 794341 1192157 := bbase (se 3 (by rfl) ⟨223529, by rfl⟩ : syracuseStep 1192157 = 447059) (by norm_num)
theorem B1192181 : Blo 794341 1192181 := bbase (se 5 (by rfl) ⟨55883, by rfl⟩ : syracuseStep 1192181 = 111767) (by norm_num)
theorem B1618165 : Blo 794341 1618165 := bbase (se 5 (by rfl) ⟨75851, by rfl⟩ : syracuseStep 1618165 = 151703) (by norm_num)
theorem B897277 : Blo 794341 897277 := bbase (se 3 (by rfl) ⟨168239, by rfl⟩ : syracuseStep 897277 = 336479) (by norm_num)
theorem B1192205 : Blo 794341 1192205 := bbase (se 3 (by rfl) ⟨223538, by rfl⟩ : syracuseStep 1192205 = 447077) (by norm_num)
theorem B897313 : Blo 794341 897313 := bbase (se 2 (by rfl) ⟨336492, by rfl⟩ : syracuseStep 897313 = 672985) (by norm_num)
theorem B1192229 : Blo 794341 1192229 := bbase (se 4 (by rfl) ⟨111771, by rfl⟩ : syracuseStep 1192229 = 223543) (by norm_num)
theorem B1192253 : Blo 794341 1192253 := bbase (se 3 (by rfl) ⟨223547, by rfl⟩ : syracuseStep 1192253 = 447095) (by norm_num)
theorem B897349 : Blo 794341 897349 := bbase (se 4 (by rfl) ⟨84126, by rfl⟩ : syracuseStep 897349 = 168253) (by norm_num)
theorem B1913165 : Blo 794341 1913165 := bbase (se 3 (by rfl) ⟨358718, by rfl⟩ : syracuseStep 1913165 = 717437) (by norm_num)
theorem B1192277 : Blo 794341 1192277 := bbase (se 10 (by rfl) ⟨1746, by rfl⟩ : syracuseStep 1192277 = 3493) (by norm_num)
theorem B2011493 : Blo 794341 2011493 := bbase (se 4 (by rfl) ⟨188577, by rfl⟩ : syracuseStep 2011493 = 377155) (by norm_num)
theorem B897385 : Blo 794341 897385 := bbase (se 2 (by rfl) ⟨336519, by rfl⟩ : syracuseStep 897385 = 673039) (by norm_num)
theorem B1192301 : Blo 794341 1192301 := bbase (se 3 (by rfl) ⟨223556, by rfl⟩ : syracuseStep 1192301 = 447113) (by norm_num)
theorem B1192325 : Blo 794341 1192325 := bbase (se 4 (by rfl) ⟨111780, by rfl⟩ : syracuseStep 1192325 = 223561) (by norm_num)
theorem B897421 : Blo 794341 897421 := bbase (se 3 (by rfl) ⟨168266, by rfl⟩ : syracuseStep 897421 = 336533) (by norm_num)
theorem B1192349 : Blo 794341 1192349 := bbase (se 3 (by rfl) ⟨223565, by rfl⟩ : syracuseStep 1192349 = 447131) (by norm_num)
theorem B897457 : Blo 794341 897457 := bbase (se 2 (by rfl) ⟨336546, by rfl⟩ : syracuseStep 897457 = 673093) (by norm_num)
theorem B1192373 : Blo 794341 1192373 := bbase (se 5 (by rfl) ⟨55892, by rfl⟩ : syracuseStep 1192373 = 111785) (by norm_num)
theorem B1192397 : Blo 794341 1192397 := bbase (se 3 (by rfl) ⟨223574, by rfl⟩ : syracuseStep 1192397 = 447149) (by norm_num)
theorem B897493 : Blo 794341 897493 := bbase (se 7 (by rfl) ⟨10517, by rfl⟩ : syracuseStep 897493 = 21035) (by norm_num)
theorem B1192421 : Blo 794341 1192421 := bbase (se 4 (by rfl) ⟨111789, by rfl⟩ : syracuseStep 1192421 = 223579) (by norm_num)
theorem B897529 : Blo 794341 897529 := bbase (se 2 (by rfl) ⟨336573, by rfl⟩ : syracuseStep 897529 = 673147) (by norm_num)
theorem B1192445 : Blo 794341 1192445 := bbase (se 3 (by rfl) ⟨223583, by rfl⟩ : syracuseStep 1192445 = 447167) (by norm_num)
theorem B1192469 : Blo 794341 1192469 := bbase (se 6 (by rfl) ⟨27948, by rfl⟩ : syracuseStep 1192469 = 55897) (by norm_num)
theorem B897565 : Blo 794341 897565 := bbase (se 3 (by rfl) ⟨168293, by rfl⟩ : syracuseStep 897565 = 336587) (by norm_num)
theorem B1192493 : Blo 794341 1192493 := bbase (se 3 (by rfl) ⟨223592, by rfl⟩ : syracuseStep 1192493 = 447185) (by norm_num)
theorem B897601 : Blo 794341 897601 := bbase (se 2 (by rfl) ⟨336600, by rfl⟩ : syracuseStep 897601 = 673201) (by norm_num)
theorem B1192517 : Blo 794341 1192517 := bbase (se 4 (by rfl) ⟨111798, by rfl⟩ : syracuseStep 1192517 = 223597) (by norm_num)
theorem B1192541 : Blo 794341 1192541 := bbase (se 3 (by rfl) ⟨223601, by rfl⟩ : syracuseStep 1192541 = 447203) (by norm_num)
theorem B897637 : Blo 794341 897637 := bbase (se 4 (by rfl) ⟨84153, by rfl⟩ : syracuseStep 897637 = 168307) (by norm_num)
theorem B1225325 : Blo 794341 1225325 := bbase (se 3 (by rfl) ⟨229748, by rfl⟩ : syracuseStep 1225325 = 459497) (by norm_num)
theorem B1192565 : Blo 794341 1192565 := bbase (se 5 (by rfl) ⟨55901, by rfl⟩ : syracuseStep 1192565 = 111803) (by norm_num)
theorem B897673 : Blo 794341 897673 := bbase (se 2 (by rfl) ⟨336627, by rfl⟩ : syracuseStep 897673 = 673255) (by norm_num)
theorem B1192589 : Blo 794341 1192589 := bbase (se 3 (by rfl) ⟨223610, by rfl⟩ : syracuseStep 1192589 = 447221) (by norm_num)
theorem B1225373 : Blo 794341 1225373 := bbase (se 3 (by rfl) ⟨229757, by rfl⟩ : syracuseStep 1225373 = 459515) (by norm_num)
theorem B1192613 : Blo 794341 1192613 := bbase (se 4 (by rfl) ⟨111807, by rfl⟩ : syracuseStep 1192613 = 223615) (by norm_num)
theorem B897709 : Blo 794341 897709 := bbase (se 3 (by rfl) ⟨168320, by rfl⟩ : syracuseStep 897709 = 336641) (by norm_num)
theorem B2011837 : Blo 794341 2011837 := bbase (se 3 (by rfl) ⟨377219, by rfl⟩ : syracuseStep 2011837 = 754439) (by norm_num)
theorem B1192637 : Blo 794341 1192637 := bbase (se 3 (by rfl) ⟨223619, by rfl⟩ : syracuseStep 1192637 = 447239) (by norm_num)
theorem B897745 : Blo 794341 897745 := bbase (se 2 (by rfl) ⟨336654, by rfl⟩ : syracuseStep 897745 = 673309) (by norm_num)
theorem B1192661 : Blo 794341 1192661 := bbase (se 7 (by rfl) ⟨13976, by rfl⟩ : syracuseStep 1192661 = 27953) (by norm_num)
theorem B1192685 : Blo 794341 1192685 := bbase (se 3 (by rfl) ⟨223628, by rfl⟩ : syracuseStep 1192685 = 447257) (by norm_num)
theorem B996077 : Blo 794341 996077 := bbase (se 3 (by rfl) ⟨186764, by rfl⟩ : syracuseStep 996077 = 373529) (by norm_num)
theorem B897781 : Blo 794341 897781 := bbase (se 5 (by rfl) ⟨42083, by rfl⟩ : syracuseStep 897781 = 84167) (by norm_num)
theorem B1192709 : Blo 794341 1192709 := bbase (se 4 (by rfl) ⟨111816, by rfl⟩ : syracuseStep 1192709 = 223633) (by norm_num)
theorem B897817 : Blo 794341 897817 := bbase (se 2 (by rfl) ⟨336681, by rfl⟩ : syracuseStep 897817 = 673363) (by norm_num)
theorem B1192733 : Blo 794341 1192733 := bbase (se 3 (by rfl) ⟨223637, by rfl⟩ : syracuseStep 1192733 = 447275) (by norm_num)
theorem B2011949 : Blo 794341 2011949 := bbase (se 3 (by rfl) ⟨377240, by rfl⟩ : syracuseStep 2011949 = 754481) (by norm_num)
theorem B1192757 : Blo 794341 1192757 := bbase (se 5 (by rfl) ⟨55910, by rfl⟩ : syracuseStep 1192757 = 111821) (by norm_num)
theorem B897853 : Blo 794341 897853 := bbase (se 3 (by rfl) ⟨168347, by rfl⟩ : syracuseStep 897853 = 336695) (by norm_num)
theorem B1815365 : Blo 794341 1815365 := bbase (se 4 (by rfl) ⟨170190, by rfl⟩ : syracuseStep 1815365 = 340381) (by norm_num)
theorem B1192781 : Blo 794341 1192781 := bbase (se 3 (by rfl) ⟨223646, by rfl⟩ : syracuseStep 1192781 = 447293) (by norm_num)
theorem B897889 : Blo 794341 897889 := bbase (se 2 (by rfl) ⟨336708, by rfl⟩ : syracuseStep 897889 = 673417) (by norm_num)
theorem B1192805 : Blo 794341 1192805 := bbase (se 4 (by rfl) ⟨111825, by rfl⟩ : syracuseStep 1192805 = 223651) (by norm_num)
theorem B1192829 : Blo 794341 1192829 := bbase (se 3 (by rfl) ⟨223655, by rfl⟩ : syracuseStep 1192829 = 447311) (by norm_num)
theorem B897925 : Blo 794341 897925 := bbase (se 4 (by rfl) ⟨84180, by rfl⟩ : syracuseStep 897925 = 168361) (by norm_num)
theorem B1192853 : Blo 794341 1192853 := bbase (se 6 (by rfl) ⟨27957, by rfl⟩ : syracuseStep 1192853 = 55915) (by norm_num)
theorem B897961 : Blo 794341 897961 := bbase (se 2 (by rfl) ⟨336735, by rfl⟩ : syracuseStep 897961 = 673471) (by norm_num)
theorem B1192877 : Blo 794341 1192877 := bbase (se 3 (by rfl) ⟨223664, by rfl⟩ : syracuseStep 1192877 = 447329) (by norm_num)
theorem B1192901 : Blo 794341 1192901 := bbase (se 4 (by rfl) ⟨111834, by rfl⟩ : syracuseStep 1192901 = 223669) (by norm_num)
theorem B897997 : Blo 794341 897997 := bbase (se 3 (by rfl) ⟨168374, by rfl⟩ : syracuseStep 897997 = 336749) (by norm_num)
theorem B1192925 : Blo 794341 1192925 := bbase (se 3 (by rfl) ⟨223673, by rfl⟩ : syracuseStep 1192925 = 447347) (by norm_num)
theorem B2012141 : Blo 794341 2012141 := bbase (se 3 (by rfl) ⟨377276, by rfl⟩ : syracuseStep 2012141 = 754553) (by norm_num)
theorem B898033 : Blo 794341 898033 := bbase (se 2 (by rfl) ⟨336762, by rfl⟩ : syracuseStep 898033 = 673525) (by norm_num)
theorem B1192949 : Blo 794341 1192949 := bbase (se 5 (by rfl) ⟨55919, by rfl⟩ : syracuseStep 1192949 = 111839) (by norm_num)
theorem B1192973 : Blo 794341 1192973 := bbase (se 3 (by rfl) ⟨223682, by rfl⟩ : syracuseStep 1192973 = 447365) (by norm_num)
theorem B898069 : Blo 794341 898069 := bbase (se 6 (by rfl) ⟨21048, by rfl⟩ : syracuseStep 898069 = 42097) (by norm_num)
theorem B1192997 : Blo 794341 1192997 := bbase (se 4 (by rfl) ⟨111843, by rfl⟩ : syracuseStep 1192997 = 223687) (by norm_num)
theorem B898105 : Blo 794341 898105 := bbase (se 2 (by rfl) ⟨336789, by rfl⟩ : syracuseStep 898105 = 673579) (by norm_num)
theorem B1193021 : Blo 794341 1193021 := bbase (se 3 (by rfl) ⟨223691, by rfl⟩ : syracuseStep 1193021 = 447383) (by norm_num)
theorem B1193045 : Blo 794341 1193045 := bbase (se 8 (by rfl) ⟨6990, by rfl⟩ : syracuseStep 1193045 = 13981) (by norm_num)
theorem B1193069 : Blo 794341 1193069 := bbase (se 3 (by rfl) ⟨223700, by rfl⟩ : syracuseStep 1193069 = 447401) (by norm_num)
theorem B1193093 : Blo 794341 1193093 := bbase (se 4 (by rfl) ⟨111852, by rfl⟩ : syracuseStep 1193093 = 223705) (by norm_num)
theorem B1193117 : Blo 794341 1193117 := bbase (se 3 (by rfl) ⟨223709, by rfl⟩ : syracuseStep 1193117 = 447419) (by norm_num)
theorem B1193141 : Blo 794341 1193141 := bbase (se 5 (by rfl) ⟨55928, by rfl⟩ : syracuseStep 1193141 = 111857) (by norm_num)
theorem B1193165 : Blo 794341 1193165 := bbase (se 3 (by rfl) ⟨223718, by rfl⟩ : syracuseStep 1193165 = 447437) (by norm_num)
theorem B1193189 : Blo 794341 1193189 := bbase (se 4 (by rfl) ⟨111861, by rfl⟩ : syracuseStep 1193189 = 223723) (by norm_num)
theorem B1193213 : Blo 794341 1193213 := bbase (se 3 (by rfl) ⟨223727, by rfl⟩ : syracuseStep 1193213 = 447455) (by norm_num)
theorem B1193237 : Blo 794341 1193237 := bbase (se 6 (by rfl) ⟨27966, by rfl⟩ : syracuseStep 1193237 = 55933) (by norm_num)
theorem B1193261 : Blo 794341 1193261 := bbase (se 3 (by rfl) ⟨223736, by rfl⟩ : syracuseStep 1193261 = 447473) (by norm_num)
theorem B2012485 : Blo 794341 2012485 := bbase (se 4 (by rfl) ⟨188670, by rfl⟩ : syracuseStep 2012485 = 377341) (by norm_num)
theorem B1193285 : Blo 794341 1193285 := bbase (se 4 (by rfl) ⟨111870, by rfl⟩ : syracuseStep 1193285 = 223741) (by norm_num)
theorem B1193309 : Blo 794341 1193309 := bbase (se 3 (by rfl) ⟨223745, by rfl⟩ : syracuseStep 1193309 = 447491) (by norm_num)
theorem B1193333 : Blo 794341 1193333 := bbase (se 5 (by rfl) ⟨55937, by rfl⟩ : syracuseStep 1193333 = 111875) (by norm_num)
theorem B1193357 : Blo 794341 1193357 := bbase (se 3 (by rfl) ⟨223754, by rfl⟩ : syracuseStep 1193357 = 447509) (by norm_num)
theorem B3028373 : Blo 794341 3028373 := bbase (se 6 (by rfl) ⟨70977, by rfl⟩ : syracuseStep 3028373 = 141955) (by norm_num)
theorem B1193381 : Blo 794341 1193381 := bbase (se 4 (by rfl) ⟨111879, by rfl⟩ : syracuseStep 1193381 = 223759) (by norm_num)
theorem B2012597 : Blo 794341 2012597 := bbase (se 5 (by rfl) ⟨94340, by rfl⟩ : syracuseStep 2012597 = 188681) (by norm_num)
theorem B1193405 : Blo 794341 1193405 := bbase (se 3 (by rfl) ⟨223763, by rfl⟩ : syracuseStep 1193405 = 447527) (by norm_num)
theorem B1193429 : Blo 794341 1193429 := bbase (se 7 (by rfl) ⟨13985, by rfl⟩ : syracuseStep 1193429 = 27971) (by norm_num)
theorem B1193453 : Blo 794341 1193453 := bbase (se 3 (by rfl) ⟨223772, by rfl⟩ : syracuseStep 1193453 = 447545) (by norm_num)
theorem B1193477 : Blo 794341 1193477 := bbase (se 4 (by rfl) ⟨111888, by rfl⟩ : syracuseStep 1193477 = 223777) (by norm_num)
theorem B1193501 : Blo 794341 1193501 := bbase (se 3 (by rfl) ⟨223781, by rfl⟩ : syracuseStep 1193501 = 447563) (by norm_num)
theorem B1193525 : Blo 794341 1193525 := bbase (se 5 (by rfl) ⟨55946, by rfl⟩ : syracuseStep 1193525 = 111893) (by norm_num)
theorem B1193549 : Blo 794341 1193549 := bbase (se 3 (by rfl) ⟨223790, by rfl⟩ : syracuseStep 1193549 = 447581) (by norm_num)
theorem B1193573 : Blo 794341 1193573 := bbase (se 4 (by rfl) ⟨111897, by rfl⟩ : syracuseStep 1193573 = 223795) (by norm_num)
theorem B2012789 : Blo 794341 2012789 := bbase (se 5 (by rfl) ⟨94349, by rfl⟩ : syracuseStep 2012789 = 188699) (by norm_num)
theorem B1193597 : Blo 794341 1193597 := bbase (se 3 (by rfl) ⟨223799, by rfl⟩ : syracuseStep 1193597 = 447599) (by norm_num)
theorem B1193621 : Blo 794341 1193621 := bbase (se 6 (by rfl) ⟨27975, by rfl⟩ : syracuseStep 1193621 = 55951) (by norm_num)
theorem B1193645 : Blo 794341 1193645 := bbase (se 3 (by rfl) ⟨223808, by rfl⟩ : syracuseStep 1193645 = 447617) (by norm_num)
theorem B3028661 : Blo 794341 3028661 := bbase (se 5 (by rfl) ⟨141968, by rfl⟩ : syracuseStep 3028661 = 283937) (by norm_num)
theorem B1193669 : Blo 794341 1193669 := bbase (se 4 (by rfl) ⟨111906, by rfl⟩ : syracuseStep 1193669 = 223813) (by norm_num)
theorem B1193693 : Blo 794341 1193693 := bbase (se 3 (by rfl) ⟨223817, by rfl⟩ : syracuseStep 1193693 = 447635) (by norm_num)
theorem B1193717 : Blo 794341 1193717 := bbase (se 5 (by rfl) ⟨55955, by rfl⟩ : syracuseStep 1193717 = 111911) (by norm_num)
theorem B1193741 : Blo 794341 1193741 := bbase (se 3 (by rfl) ⟨223826, by rfl⟩ : syracuseStep 1193741 = 447653) (by norm_num)
theorem B1816349 : Blo 794341 1816349 := bbase (se 3 (by rfl) ⟨340565, by rfl⟩ : syracuseStep 1816349 = 681131) (by norm_num)
theorem B1193765 : Blo 794341 1193765 := bbase (se 4 (by rfl) ⟨111915, by rfl⟩ : syracuseStep 1193765 = 223831) (by norm_num)
theorem B1193789 : Blo 794341 1193789 := bbase (se 3 (by rfl) ⟨223835, by rfl⟩ : syracuseStep 1193789 = 447671) (by norm_num)
theorem B1193813 : Blo 794341 1193813 := bbase (se 9 (by rfl) ⟨3497, by rfl⟩ : syracuseStep 1193813 = 6995) (by norm_num)
theorem B1193837 : Blo 794341 1193837 := bbase (se 3 (by rfl) ⟨223844, by rfl⟩ : syracuseStep 1193837 = 447689) (by norm_num)
theorem B1193861 : Blo 794341 1193861 := bbase (se 4 (by rfl) ⟨111924, by rfl⟩ : syracuseStep 1193861 = 223849) (by norm_num)
theorem B1193885 : Blo 794341 1193885 := bbase (se 3 (by rfl) ⟨223853, by rfl⟩ : syracuseStep 1193885 = 447707) (by norm_num)
theorem B2865061 : Blo 794341 2865061 := bbase (se 4 (by rfl) ⟨268599, by rfl⟩ : syracuseStep 2865061 = 537199) (by norm_num)
theorem B1193909 : Blo 794341 1193909 := bbase (se 5 (by rfl) ⟨55964, by rfl⟩ : syracuseStep 1193909 = 111929) (by norm_num)
theorem B2013133 : Blo 794341 2013133 := bbase (se 3 (by rfl) ⟨377462, by rfl⟩ : syracuseStep 2013133 = 754925) (by norm_num)
theorem B1193933 : Blo 794341 1193933 := bbase (se 3 (by rfl) ⟨223862, by rfl⟩ : syracuseStep 1193933 = 447725) (by norm_num)
theorem B1193957 : Blo 794341 1193957 := bbase (se 4 (by rfl) ⟨111933, by rfl⟩ : syracuseStep 1193957 = 223867) (by norm_num)
theorem B1193981 : Blo 794341 1193981 := bbase (se 3 (by rfl) ⟨223871, by rfl⟩ : syracuseStep 1193981 = 447743) (by norm_num)
theorem B1194005 : Blo 794341 1194005 := bbase (se 6 (by rfl) ⟨27984, by rfl⟩ : syracuseStep 1194005 = 55969) (by norm_num)
theorem B1194029 : Blo 794341 1194029 := bbase (se 3 (by rfl) ⟨223880, by rfl⟩ : syracuseStep 1194029 = 447761) (by norm_num)
theorem B1914941 : Blo 794341 1914941 := bbase (se 3 (by rfl) ⟨359051, by rfl⟩ : syracuseStep 1914941 = 718103) (by norm_num)
theorem B2013245 : Blo 794341 2013245 := bbase (se 3 (by rfl) ⟨377483, by rfl⟩ : syracuseStep 2013245 = 754967) (by norm_num)
theorem B1194053 : Blo 794341 1194053 := bbase (se 4 (by rfl) ⟨111942, by rfl⟩ : syracuseStep 1194053 = 223885) (by norm_num)
theorem B3881029 : Blo 794341 3881029 := bbase (se 4 (by rfl) ⟨363846, by rfl⟩ : syracuseStep 3881029 = 727693) (by norm_num)
theorem B1194077 : Blo 794341 1194077 := bbase (se 3 (by rfl) ⟨223889, by rfl⟩ : syracuseStep 1194077 = 447779) (by norm_num)
theorem B2046053 : Blo 794341 2046053 := bbase (se 4 (by rfl) ⟨191817, by rfl⟩ : syracuseStep 2046053 = 383635) (by norm_num)
theorem B1194101 : Blo 794341 1194101 := bbase (se 5 (by rfl) ⟨55973, by rfl⟩ : syracuseStep 1194101 = 111947) (by norm_num)
theorem B1194125 : Blo 794341 1194125 := bbase (se 3 (by rfl) ⟨223898, by rfl⟩ : syracuseStep 1194125 = 447797) (by norm_num)
theorem B1194149 : Blo 794341 1194149 := bbase (se 4 (by rfl) ⟨111951, by rfl⟩ : syracuseStep 1194149 = 223903) (by norm_num)
theorem B1194173 : Blo 794341 1194173 := bbase (se 3 (by rfl) ⟨223907, by rfl⟩ : syracuseStep 1194173 = 447815) (by norm_num)
theorem B2865365 : Blo 794341 2865365 := bbase (se 7 (by rfl) ⟨33578, by rfl⟩ : syracuseStep 2865365 = 67157) (by norm_num)
theorem B1194197 : Blo 794341 1194197 := bbase (se 7 (by rfl) ⟨13994, by rfl⟩ : syracuseStep 1194197 = 27989) (by norm_num)
theorem B1194221 : Blo 794341 1194221 := bbase (se 3 (by rfl) ⟨223916, by rfl⟩ : syracuseStep 1194221 = 447833) (by norm_num)
theorem B2013437 : Blo 794341 2013437 := bbase (se 3 (by rfl) ⟨377519, by rfl⟩ : syracuseStep 2013437 = 755039) (by norm_num)
theorem B1194245 : Blo 794341 1194245 := bbase (se 4 (by rfl) ⟨111960, by rfl⟩ : syracuseStep 1194245 = 223921) (by norm_num)
theorem B1194269 : Blo 794341 1194269 := bbase (se 3 (by rfl) ⟨223925, by rfl⟩ : syracuseStep 1194269 = 447851) (by norm_num)
theorem B1194293 : Blo 794341 1194293 := bbase (se 5 (by rfl) ⟨55982, by rfl⟩ : syracuseStep 1194293 = 111965) (by norm_num)
theorem B1194317 : Blo 794341 1194317 := bbase (se 3 (by rfl) ⟨223934, by rfl⟩ : syracuseStep 1194317 = 447869) (by norm_num)
theorem B1194341 : Blo 794341 1194341 := bbase (se 4 (by rfl) ⟨111969, by rfl⟩ : syracuseStep 1194341 = 223939) (by norm_num)
theorem B1227125 : Blo 794341 1227125 := bbase (se 5 (by rfl) ⟨57521, by rfl⟩ : syracuseStep 1227125 = 115043) (by norm_num)
theorem B1194365 : Blo 794341 1194365 := bbase (se 3 (by rfl) ⟨223943, by rfl⟩ : syracuseStep 1194365 = 447887) (by norm_num)
theorem B1194389 : Blo 794341 1194389 := bbase (se 6 (by rfl) ⟨27993, by rfl⟩ : syracuseStep 1194389 = 55987) (by norm_num)
theorem B1194413 : Blo 794341 1194413 := bbase (se 3 (by rfl) ⟨223952, by rfl⟩ : syracuseStep 1194413 = 447905) (by norm_num)
theorem B1194437 : Blo 794341 1194437 := bbase (se 4 (by rfl) ⟨111978, by rfl⟩ : syracuseStep 1194437 = 223957) (by norm_num)
theorem B1194461 : Blo 794341 1194461 := bbase (se 3 (by rfl) ⟨223961, by rfl⟩ : syracuseStep 1194461 = 447923) (by norm_num)
theorem B1194485 : Blo 794341 1194485 := bbase (se 5 (by rfl) ⟨55991, by rfl⟩ : syracuseStep 1194485 = 111983) (by norm_num)
theorem B1194509 : Blo 794341 1194509 := bbase (se 3 (by rfl) ⟨223970, by rfl⟩ : syracuseStep 1194509 = 447941) (by norm_num)
theorem B1817117 : Blo 794341 1817117 := bbase (se 3 (by rfl) ⟨340709, by rfl⟩ : syracuseStep 1817117 = 681419) (by norm_num)
theorem B1194533 : Blo 794341 1194533 := bbase (se 4 (by rfl) ⟨111987, by rfl⟩ : syracuseStep 1194533 = 223975) (by norm_num)
theorem B1194557 : Blo 794341 1194557 := bbase (se 3 (by rfl) ⟨223979, by rfl⟩ : syracuseStep 1194557 = 447959) (by norm_num)
theorem B2013781 : Blo 794341 2013781 := bbase (se 8 (by rfl) ⟨11799, by rfl⟩ : syracuseStep 2013781 = 23599) (by norm_num)
theorem B1194581 : Blo 794341 1194581 := bbase (se 8 (by rfl) ⟨6999, by rfl⟩ : syracuseStep 1194581 = 13999) (by norm_num)
theorem B1194605 : Blo 794341 1194605 := bbase (se 3 (by rfl) ⟨223988, by rfl⟩ : syracuseStep 1194605 = 447977) (by norm_num)
theorem B1194629 : Blo 794341 1194629 := bbase (se 4 (by rfl) ⟨111996, by rfl⟩ : syracuseStep 1194629 = 223993) (by norm_num)
theorem B1194653 : Blo 794341 1194653 := bbase (se 3 (by rfl) ⟨223997, by rfl⟩ : syracuseStep 1194653 = 447995) (by norm_num)
theorem B1194677 : Blo 794341 1194677 := bbase (se 5 (by rfl) ⟨56000, by rfl⟩ : syracuseStep 1194677 = 112001) (by norm_num)
theorem B2013893 : Blo 794341 2013893 := bbase (se 4 (by rfl) ⟨188802, by rfl⟩ : syracuseStep 2013893 = 377605) (by norm_num)
theorem B1194701 : Blo 794341 1194701 := bbase (se 3 (by rfl) ⟨224006, by rfl⟩ : syracuseStep 1194701 = 448013) (by norm_num)
theorem B1194725 : Blo 794341 1194725 := bbase (se 4 (by rfl) ⟨112005, by rfl⟩ : syracuseStep 1194725 = 224011) (by norm_num)
theorem B1194749 : Blo 794341 1194749 := bbase (se 3 (by rfl) ⟨224015, by rfl⟩ : syracuseStep 1194749 = 448031) (by norm_num)
theorem B1194773 : Blo 794341 1194773 := bbase (se 6 (by rfl) ⟨28002, by rfl⟩ : syracuseStep 1194773 = 56005) (by norm_num)
theorem B1194797 : Blo 794341 1194797 := bbase (se 3 (by rfl) ⟨224024, by rfl⟩ : syracuseStep 1194797 = 448049) (by norm_num)
theorem B1194821 : Blo 794341 1194821 := bbase (se 4 (by rfl) ⟨112014, by rfl⟩ : syracuseStep 1194821 = 224029) (by norm_num)
theorem B3029845 : Blo 794341 3029845 := bbase (se 9 (by rfl) ⟨8876, by rfl⟩ : syracuseStep 3029845 = 17753) (by norm_num)
theorem B1194845 : Blo 794341 1194845 := bbase (se 3 (by rfl) ⟨224033, by rfl⟩ : syracuseStep 1194845 = 448067) (by norm_num)
theorem B1194869 : Blo 794341 1194869 := bbase (se 5 (by rfl) ⟨56009, by rfl⟩ : syracuseStep 1194869 = 112019) (by norm_num)
theorem B4537205 : Blo 794341 4537205 := bbase (se 5 (by rfl) ⟨212681, by rfl⟩ : syracuseStep 4537205 = 425363) (by norm_num)
theorem B2014085 : Blo 794341 2014085 := bbase (se 4 (by rfl) ⟨188820, by rfl⟩ : syracuseStep 2014085 = 377641) (by norm_num)
theorem B1194893 : Blo 794341 1194893 := bbase (se 3 (by rfl) ⟨224042, by rfl⟩ : syracuseStep 1194893 = 448085) (by norm_num)
theorem B1194917 : Blo 794341 1194917 := bbase (se 4 (by rfl) ⟨112023, by rfl⟩ : syracuseStep 1194917 = 224047) (by norm_num)
theorem B1194941 : Blo 794341 1194941 := bbase (se 3 (by rfl) ⟨224051, by rfl⟩ : syracuseStep 1194941 = 448103) (by norm_num)
theorem B13581269 : Blo 794341 13581269 := bbase (se 7 (by rfl) ⟨159155, by rfl⟩ : syracuseStep 13581269 = 318311) (by norm_num)
theorem B1194965 : Blo 794341 1194965 := bbase (se 7 (by rfl) ⟨14003, by rfl⟩ : syracuseStep 1194965 = 28007) (by norm_num)
theorem B1194989 : Blo 794341 1194989 := bbase (se 3 (by rfl) ⟨224060, by rfl⟩ : syracuseStep 1194989 = 448121) (by norm_num)
theorem B1195013 : Blo 794341 1195013 := bbase (se 4 (by rfl) ⟨112032, by rfl⟩ : syracuseStep 1195013 = 224065) (by norm_num)
theorem B1195037 : Blo 794341 1195037 := bbase (se 3 (by rfl) ⟨224069, by rfl⟩ : syracuseStep 1195037 = 448139) (by norm_num)
theorem B1195061 : Blo 794341 1195061 := bbase (se 5 (by rfl) ⟨56018, by rfl⟩ : syracuseStep 1195061 = 112037) (by norm_num)
theorem B1195085 : Blo 794341 1195085 := bbase (se 3 (by rfl) ⟨224078, by rfl⟩ : syracuseStep 1195085 = 448157) (by norm_num)
theorem B1195109 : Blo 794341 1195109 := bbase (se 4 (by rfl) ⟨112041, by rfl⟩ : syracuseStep 1195109 = 224083) (by norm_num)
theorem B1195133 : Blo 794341 1195133 := bbase (se 3 (by rfl) ⟨224087, by rfl⟩ : syracuseStep 1195133 = 448175) (by norm_num)
theorem B3030149 : Blo 794341 3030149 := bbase (se 4 (by rfl) ⟨284076, by rfl⟩ : syracuseStep 3030149 = 568153) (by norm_num)
theorem B4832405 : Blo 794341 4832405 := bbase (se 6 (by rfl) ⟨113259, by rfl⟩ : syracuseStep 4832405 = 226519) (by norm_num)
theorem B1195157 : Blo 794341 1195157 := bbase (se 6 (by rfl) ⟨28011, by rfl⟩ : syracuseStep 1195157 = 56023) (by norm_num)
theorem B1195181 : Blo 794341 1195181 := bbase (se 3 (by rfl) ⟨224096, by rfl⟩ : syracuseStep 1195181 = 448193) (by norm_num)
theorem B1195205 : Blo 794341 1195205 := bbase (se 4 (by rfl) ⟨112050, by rfl⟩ : syracuseStep 1195205 = 224101) (by norm_num)
theorem B2014429 : Blo 794341 2014429 := bbase (se 3 (by rfl) ⟨377705, by rfl⟩ : syracuseStep 2014429 = 755411) (by norm_num)
theorem B1195229 : Blo 794341 1195229 := bbase (se 3 (by rfl) ⟨224105, by rfl⟩ : syracuseStep 1195229 = 448211) (by norm_num)
theorem B1195253 : Blo 794341 1195253 := bbase (se 5 (by rfl) ⟨56027, by rfl⟩ : syracuseStep 1195253 = 112055) (by norm_num)
theorem B1195277 : Blo 794341 1195277 := bbase (se 3 (by rfl) ⟨224114, by rfl⟩ : syracuseStep 1195277 = 448229) (by norm_num)
theorem B1195301 : Blo 794341 1195301 := bbase (se 4 (by rfl) ⟨112059, by rfl⟩ : syracuseStep 1195301 = 224119) (by norm_num)
theorem B1195325 : Blo 794341 1195325 := bbase (se 3 (by rfl) ⟨224123, by rfl⟩ : syracuseStep 1195325 = 448247) (by norm_num)
theorem B2014541 : Blo 794341 2014541 := bbase (se 3 (by rfl) ⟨377726, by rfl⟩ : syracuseStep 2014541 = 755453) (by norm_num)
theorem B1195349 : Blo 794341 1195349 := bbase (se 11 (by rfl) ⟨875, by rfl⟩ : syracuseStep 1195349 = 1751) (by norm_num)
theorem B1195373 : Blo 794341 1195373 := bbase (se 3 (by rfl) ⟨224132, by rfl⟩ : syracuseStep 1195373 = 448265) (by norm_num)
theorem B1195397 : Blo 794341 1195397 := bbase (se 4 (by rfl) ⟨112068, by rfl⟩ : syracuseStep 1195397 = 224137) (by norm_num)
theorem B1195421 : Blo 794341 1195421 := bbase (se 3 (by rfl) ⟨224141, by rfl⟩ : syracuseStep 1195421 = 448283) (by norm_num)
theorem B1195445 : Blo 794341 1195445 := bbase (se 5 (by rfl) ⟨56036, by rfl⟩ : syracuseStep 1195445 = 112073) (by norm_num)
theorem B1195469 : Blo 794341 1195469 := bbase (se 3 (by rfl) ⟨224150, by rfl⟩ : syracuseStep 1195469 = 448301) (by norm_num)
theorem B1195493 : Blo 794341 1195493 := bbase (se 4 (by rfl) ⟨112077, by rfl⟩ : syracuseStep 1195493 = 224155) (by norm_num)
theorem B1195517 : Blo 794341 1195517 := bbase (se 3 (by rfl) ⟨224159, by rfl⟩ : syracuseStep 1195517 = 448319) (by norm_num)
theorem B2014733 : Blo 794341 2014733 := bbase (se 3 (by rfl) ⟨377762, by rfl⟩ : syracuseStep 2014733 = 755525) (by norm_num)
theorem B1195541 : Blo 794341 1195541 := bbase (se 6 (by rfl) ⟨28020, by rfl⟩ : syracuseStep 1195541 = 56041) (by norm_num)
theorem B1195565 : Blo 794341 1195565 := bbase (se 3 (by rfl) ⟨224168, by rfl⟩ : syracuseStep 1195565 = 448337) (by norm_num)
theorem B1195589 : Blo 794341 1195589 := bbase (se 4 (by rfl) ⟨112086, by rfl⟩ : syracuseStep 1195589 = 224173) (by norm_num)
theorem B1195613 : Blo 794341 1195613 := bbase (se 3 (by rfl) ⟨224177, by rfl⟩ : syracuseStep 1195613 = 448355) (by norm_num)
theorem B1195637 : Blo 794341 1195637 := bbase (se 5 (by rfl) ⟨56045, by rfl⟩ : syracuseStep 1195637 = 112091) (by norm_num)
theorem B1195661 : Blo 794341 1195661 := bbase (se 3 (by rfl) ⟨224186, by rfl⟩ : syracuseStep 1195661 = 448373) (by norm_num)
theorem B1195685 : Blo 794341 1195685 := bbase (se 4 (by rfl) ⟨112095, by rfl⟩ : syracuseStep 1195685 = 224191) (by norm_num)
theorem B1195709 : Blo 794341 1195709 := bbase (se 3 (by rfl) ⟨224195, by rfl⟩ : syracuseStep 1195709 = 448391) (by norm_num)
theorem B1195733 : Blo 794341 1195733 := bbase (se 7 (by rfl) ⟨14012, by rfl⟩ : syracuseStep 1195733 = 28025) (by norm_num)
theorem B1195757 : Blo 794341 1195757 := bbase (se 3 (by rfl) ⟨224204, by rfl⟩ : syracuseStep 1195757 = 448409) (by norm_num)
theorem B1195781 : Blo 794341 1195781 := bbase (se 4 (by rfl) ⟨112104, by rfl⟩ : syracuseStep 1195781 = 224209) (by norm_num)
theorem B1195805 : Blo 794341 1195805 := bbase (se 3 (by rfl) ⟨224213, by rfl⟩ : syracuseStep 1195805 = 448427) (by norm_num)
theorem B1195829 : Blo 794341 1195829 := bbase (se 5 (by rfl) ⟨56054, by rfl⟩ : syracuseStep 1195829 = 112109) (by norm_num)
theorem B1195853 : Blo 794341 1195853 := bbase (se 3 (by rfl) ⟨224222, by rfl⟩ : syracuseStep 1195853 = 448445) (by norm_num)
theorem B2015077 : Blo 794341 2015077 := bbase (se 4 (by rfl) ⟨188913, by rfl⟩ : syracuseStep 2015077 = 377827) (by norm_num)
theorem B1195877 : Blo 794341 1195877 := bbase (se 4 (by rfl) ⟨112113, by rfl⟩ : syracuseStep 1195877 = 224227) (by norm_num)
theorem B1195901 : Blo 794341 1195901 := bbase (se 3 (by rfl) ⟨224231, by rfl⟩ : syracuseStep 1195901 = 448463) (by norm_num)
theorem B1195925 : Blo 794341 1195925 := bbase (se 6 (by rfl) ⟨28029, by rfl⟩ : syracuseStep 1195925 = 56059) (by norm_num)
theorem B1195949 : Blo 794341 1195949 := bbase (se 3 (by rfl) ⟨224240, by rfl⟩ : syracuseStep 1195949 = 448481) (by norm_num)
theorem B1195973 : Blo 794341 1195973 := bbase (se 4 (by rfl) ⟨112122, by rfl⟩ : syracuseStep 1195973 = 224245) (by norm_num)
theorem B2015189 : Blo 794341 2015189 := bbase (se 7 (by rfl) ⟨23615, by rfl⟩ : syracuseStep 2015189 = 47231) (by norm_num)
theorem B1195997 : Blo 794341 1195997 := bbase (se 3 (by rfl) ⟨224249, by rfl⟩ : syracuseStep 1195997 = 448499) (by norm_num)
theorem B1196021 : Blo 794341 1196021 := bbase (se 5 (by rfl) ⟨56063, by rfl⟩ : syracuseStep 1196021 = 112127) (by norm_num)
theorem B1196045 : Blo 794341 1196045 := bbase (se 3 (by rfl) ⟨224258, by rfl⟩ : syracuseStep 1196045 = 448517) (by norm_num)
theorem B4538389 : Blo 794341 4538389 := bbase (se 6 (by rfl) ⟨106368, by rfl⟩ : syracuseStep 4538389 = 212737) (by norm_num)
theorem B1196069 : Blo 794341 1196069 := bbase (se 4 (by rfl) ⟨112131, by rfl⟩ : syracuseStep 1196069 = 224263) (by norm_num)
theorem B5161013 : Blo 794341 5161013 := bbase (se 5 (by rfl) ⟨241922, by rfl⟩ : syracuseStep 5161013 = 483845) (by norm_num)
theorem B3227701 : Blo 794341 3227701 := bbase (se 5 (by rfl) ⟨151298, by rfl⟩ : syracuseStep 3227701 = 302597) (by norm_num)
theorem B1196093 : Blo 794341 1196093 := bbase (se 3 (by rfl) ⟨224267, by rfl⟩ : syracuseStep 1196093 = 448535) (by norm_num)
theorem B1196117 : Blo 794341 1196117 := bbase (se 8 (by rfl) ⟨7008, by rfl⟩ : syracuseStep 1196117 = 14017) (by norm_num)
theorem B1196141 : Blo 794341 1196141 := bbase (se 3 (by rfl) ⟨224276, by rfl⟩ : syracuseStep 1196141 = 448553) (by norm_num)
theorem B1917037 : Blo 794341 1917037 := bbase (se 3 (by rfl) ⟨359444, by rfl⟩ : syracuseStep 1917037 = 718889) (by norm_num)
theorem B1196165 : Blo 794341 1196165 := bbase (se 4 (by rfl) ⟨112140, by rfl⟩ : syracuseStep 1196165 = 224281) (by norm_num)
theorem B1720469 : Blo 794341 1720469 := bbase (se 6 (by rfl) ⟨40323, by rfl⟩ : syracuseStep 1720469 = 80647) (by norm_num)
theorem B2015381 : Blo 794341 2015381 := bbase (se 6 (by rfl) ⟨47235, by rfl⟩ : syracuseStep 2015381 = 94471) (by norm_num)
theorem B1196189 : Blo 794341 1196189 := bbase (se 3 (by rfl) ⟨224285, by rfl⟩ : syracuseStep 1196189 = 448571) (by norm_num)
theorem B1196213 : Blo 794341 1196213 := bbase (se 5 (by rfl) ⟨56072, by rfl⟩ : syracuseStep 1196213 = 112145) (by norm_num)
theorem B1196237 : Blo 794341 1196237 := bbase (se 3 (by rfl) ⟨224294, by rfl⟩ : syracuseStep 1196237 = 448589) (by norm_num)
theorem B1196261 : Blo 794341 1196261 := bbase (se 4 (by rfl) ⟨112149, by rfl⟩ : syracuseStep 1196261 = 224299) (by norm_num)
theorem B1196285 : Blo 794341 1196285 := bbase (se 3 (by rfl) ⟨224303, by rfl⟩ : syracuseStep 1196285 = 448607) (by norm_num)
theorem B1196309 : Blo 794341 1196309 := bbase (se 6 (by rfl) ⟨28038, by rfl⟩ : syracuseStep 1196309 = 56077) (by norm_num)
theorem B1196333 : Blo 794341 1196333 := bbase (se 3 (by rfl) ⟨224312, by rfl⟩ : syracuseStep 1196333 = 448625) (by norm_num)
theorem B1196357 : Blo 794341 1196357 := bbase (se 4 (by rfl) ⟨112158, by rfl⟩ : syracuseStep 1196357 = 224317) (by norm_num)
theorem B1196381 : Blo 794341 1196381 := bbase (se 3 (by rfl) ⟨224321, by rfl⟩ : syracuseStep 1196381 = 448643) (by norm_num)
theorem B1196405 : Blo 794341 1196405 := bbase (se 5 (by rfl) ⟨56081, by rfl⟩ : syracuseStep 1196405 = 112163) (by norm_num)
theorem B1196429 : Blo 794341 1196429 := bbase (se 3 (by rfl) ⟨224330, by rfl⟩ : syracuseStep 1196429 = 448661) (by norm_num)
theorem B1196453 : Blo 794341 1196453 := bbase (se 4 (by rfl) ⟨112167, by rfl⟩ : syracuseStep 1196453 = 224335) (by norm_num)
theorem B1196477 : Blo 794341 1196477 := bbase (se 3 (by rfl) ⟨224339, by rfl⟩ : syracuseStep 1196477 = 448679) (by norm_num)
theorem B1196501 : Blo 794341 1196501 := bbase (se 7 (by rfl) ⟨14021, by rfl⟩ : syracuseStep 1196501 = 28043) (by norm_num)
theorem B2015725 : Blo 794341 2015725 := bbase (se 3 (by rfl) ⟨377948, by rfl⟩ : syracuseStep 2015725 = 755897) (by norm_num)
theorem B1196525 : Blo 794341 1196525 := bbase (se 3 (by rfl) ⟨224348, by rfl⟩ : syracuseStep 1196525 = 448697) (by norm_num)
theorem B1196549 : Blo 794341 1196549 := bbase (se 4 (by rfl) ⟨112176, by rfl⟩ : syracuseStep 1196549 = 224353) (by norm_num)
theorem B3195413 : Blo 794341 3195413 := bbase (se 6 (by rfl) ⟨74892, by rfl⟩ : syracuseStep 3195413 = 149785) (by norm_num)
theorem B1196573 : Blo 794341 1196573 := bbase (se 3 (by rfl) ⟨224357, by rfl⟩ : syracuseStep 1196573 = 448715) (by norm_num)
theorem B1196597 : Blo 794341 1196597 := bbase (se 5 (by rfl) ⟨56090, by rfl⟩ : syracuseStep 1196597 = 112181) (by norm_num)
theorem B1196621 : Blo 794341 1196621 := bbase (se 3 (by rfl) ⟨224366, by rfl⟩ : syracuseStep 1196621 = 448733) (by norm_num)
theorem B2015837 : Blo 794341 2015837 := bbase (se 3 (by rfl) ⟨377969, by rfl⟩ : syracuseStep 2015837 = 755939) (by norm_num)
theorem B1196645 : Blo 794341 1196645 := bbase (se 4 (by rfl) ⟨112185, by rfl⟩ : syracuseStep 1196645 = 224371) (by norm_num)
theorem B6046325 : Blo 794341 6046325 := bbase (se 5 (by rfl) ⟨283421, by rfl⟩ : syracuseStep 6046325 = 566843) (by norm_num)
theorem B1196669 : Blo 794341 1196669 := bbase (se 3 (by rfl) ⟨224375, by rfl⟩ : syracuseStep 1196669 = 448751) (by norm_num)
theorem B1196693 : Blo 794341 1196693 := bbase (se 6 (by rfl) ⟨28047, by rfl⟩ : syracuseStep 1196693 = 56095) (by norm_num)
theorem B1196717 : Blo 794341 1196717 := bbase (se 3 (by rfl) ⟨224384, by rfl⟩ : syracuseStep 1196717 = 448769) (by norm_num)
theorem B1196741 : Blo 794341 1196741 := bbase (se 4 (by rfl) ⟨112194, by rfl⟩ : syracuseStep 1196741 = 224389) (by norm_num)
theorem B1196765 : Blo 794341 1196765 := bbase (se 3 (by rfl) ⟨224393, by rfl⟩ : syracuseStep 1196765 = 448787) (by norm_num)
theorem B1196789 : Blo 794341 1196789 := bbase (se 5 (by rfl) ⟨56099, by rfl⟩ : syracuseStep 1196789 = 112199) (by norm_num)
theorem B1196813 : Blo 794341 1196813 := bbase (se 3 (by rfl) ⟨224402, by rfl⟩ : syracuseStep 1196813 = 448805) (by norm_num)
theorem B2016029 : Blo 794341 2016029 := bbase (se 3 (by rfl) ⟨378005, by rfl⟩ : syracuseStep 2016029 = 756011) (by norm_num)
theorem B1196837 : Blo 794341 1196837 := bbase (se 4 (by rfl) ⟨112203, by rfl⟩ : syracuseStep 1196837 = 224407) (by norm_num)
theorem B1917749 : Blo 794341 1917749 := bbase (se 5 (by rfl) ⟨89894, by rfl⟩ : syracuseStep 1917749 = 179789) (by norm_num)
theorem B1196861 : Blo 794341 1196861 := bbase (se 3 (by rfl) ⟨224411, by rfl⟩ : syracuseStep 1196861 = 448823) (by norm_num)
theorem B1196885 : Blo 794341 1196885 := bbase (se 9 (by rfl) ⟨3506, by rfl⟩ : syracuseStep 1196885 = 7013) (by norm_num)
theorem B1196909 : Blo 794341 1196909 := bbase (se 3 (by rfl) ⟨224420, by rfl⟩ : syracuseStep 1196909 = 448841) (by norm_num)
theorem B1196933 : Blo 794341 1196933 := bbase (se 4 (by rfl) ⟨112212, by rfl⟩ : syracuseStep 1196933 = 224425) (by norm_num)
theorem B1196957 : Blo 794341 1196957 := bbase (se 3 (by rfl) ⟨224429, by rfl⟩ : syracuseStep 1196957 = 448859) (by norm_num)
theorem B1196981 : Blo 794341 1196981 := bbase (se 5 (by rfl) ⟨56108, by rfl⟩ : syracuseStep 1196981 = 112217) (by norm_num)
theorem B1197005 : Blo 794341 1197005 := bbase (se 3 (by rfl) ⟨224438, by rfl⟩ : syracuseStep 1197005 = 448877) (by norm_num)
theorem B1197029 : Blo 794341 1197029 := bbase (se 4 (by rfl) ⟨112221, by rfl⟩ : syracuseStep 1197029 = 224443) (by norm_num)
theorem B1197053 : Blo 794341 1197053 := bbase (se 3 (by rfl) ⟨224447, by rfl⟩ : syracuseStep 1197053 = 448895) (by norm_num)
theorem B1197077 : Blo 794341 1197077 := bbase (se 6 (by rfl) ⟨28056, by rfl⟩ : syracuseStep 1197077 = 56113) (by norm_num)
theorem B1197101 : Blo 794341 1197101 := bbase (se 3 (by rfl) ⟨224456, by rfl⟩ : syracuseStep 1197101 = 448913) (by norm_num)
theorem B1197125 : Blo 794341 1197125 := bbase (se 4 (by rfl) ⟨112230, by rfl⟩ : syracuseStep 1197125 = 224461) (by norm_num)
theorem B1197149 : Blo 794341 1197149 := bbase (se 3 (by rfl) ⟨224465, by rfl⟩ : syracuseStep 1197149 = 448931) (by norm_num)
theorem B2016373 : Blo 794341 2016373 := bbase (se 5 (by rfl) ⟨94517, by rfl⟩ : syracuseStep 2016373 = 189035) (by norm_num)
theorem B1197173 : Blo 794341 1197173 := bbase (se 5 (by rfl) ⟨56117, by rfl⟩ : syracuseStep 1197173 = 112235) (by norm_num)
theorem B1197197 : Blo 794341 1197197 := bbase (se 3 (by rfl) ⟨224474, by rfl⟩ : syracuseStep 1197197 = 448949) (by norm_num)
theorem B1197221 : Blo 794341 1197221 := bbase (se 4 (by rfl) ⟨112239, by rfl⟩ : syracuseStep 1197221 = 224479) (by norm_num)
theorem B1918133 : Blo 794341 1918133 := bbase (se 5 (by rfl) ⟨89912, by rfl⟩ : syracuseStep 1918133 = 179825) (by norm_num)
theorem B1197245 : Blo 794341 1197245 := bbase (se 3 (by rfl) ⟨224483, by rfl⟩ : syracuseStep 1197245 = 448967) (by norm_num)
theorem B1197269 : Blo 794341 1197269 := bbase (se 7 (by rfl) ⟨14030, by rfl⟩ : syracuseStep 1197269 = 28061) (by norm_num)
theorem B2016485 : Blo 794341 2016485 := bbase (se 4 (by rfl) ⟨189045, by rfl⟩ : syracuseStep 2016485 = 378091) (by norm_num)
theorem B1197293 : Blo 794341 1197293 := bbase (se 3 (by rfl) ⟨224492, by rfl⟩ : syracuseStep 1197293 = 448985) (by norm_num)
theorem B7259381 : Blo 794341 7259381 := bbase (se 5 (by rfl) ⟨340283, by rfl⟩ : syracuseStep 7259381 = 680567) (by norm_num)
theorem B1197317 : Blo 794341 1197317 := bbase (se 4 (by rfl) ⟨112248, by rfl⟩ : syracuseStep 1197317 = 224497) (by norm_num)
theorem B1197341 : Blo 794341 1197341 := bbase (se 3 (by rfl) ⟨224501, by rfl⟩ : syracuseStep 1197341 = 449003) (by norm_num)
theorem B1197365 : Blo 794341 1197365 := bbase (se 5 (by rfl) ⟨56126, by rfl⟩ : syracuseStep 1197365 = 112253) (by norm_num)
theorem B1197389 : Blo 794341 1197389 := bbase (se 3 (by rfl) ⟨224510, by rfl⟩ : syracuseStep 1197389 = 449021) (by norm_num)
theorem B1197413 : Blo 794341 1197413 := bbase (se 4 (by rfl) ⟨112257, by rfl⟩ : syracuseStep 1197413 = 224515) (by norm_num)
theorem B1197437 : Blo 794341 1197437 := bbase (se 3 (by rfl) ⟨224519, by rfl⟩ : syracuseStep 1197437 = 449039) (by norm_num)
theorem B1197461 : Blo 794341 1197461 := bbase (se 6 (by rfl) ⟨28065, by rfl⟩ : syracuseStep 1197461 = 56131) (by norm_num)
theorem B2016677 : Blo 794341 2016677 := bbase (se 4 (by rfl) ⟨189063, by rfl⟩ : syracuseStep 2016677 = 378127) (by norm_num)
theorem B1787309 : Blo 794341 1787309 := bbase (se 3 (by rfl) ⟨335120, by rfl⟩ : syracuseStep 1787309 = 670241) (by norm_num)
theorem B1197485 : Blo 794341 1197485 := bbase (se 3 (by rfl) ⟨224528, by rfl⟩ : syracuseStep 1197485 = 449057) (by norm_num)
theorem B1197509 : Blo 794341 1197509 := bbase (se 4 (by rfl) ⟨112266, by rfl⟩ : syracuseStep 1197509 = 224533) (by norm_num)
theorem B1787381 : Blo 794341 1787381 := bbase (se 5 (by rfl) ⟨83783, by rfl⟩ : syracuseStep 1787381 = 167567) (by norm_num)
theorem B3393029 : Blo 794341 3393029 := bbase (se 4 (by rfl) ⟨318096, by rfl⟩ : syracuseStep 3393029 = 636193) (by norm_num)
theorem B1132069 : Blo 794341 1132069 := bbase (se 4 (by rfl) ⟨106131, by rfl⟩ : syracuseStep 1132069 = 212263) (by norm_num)
theorem B1787453 : Blo 794341 1787453 := bbase (se 3 (by rfl) ⟨335147, by rfl⟩ : syracuseStep 1787453 = 670295) (by norm_num)
theorem B19613269 : Blo 794341 19613269 := bbase (se 8 (by rfl) ⟨114921, by rfl⟩ : syracuseStep 19613269 = 229843) (by norm_num)
theorem B5097077 : Blo 794341 5097077 := bbase (se 5 (by rfl) ⟨238925, by rfl⟩ : syracuseStep 5097077 = 477851) (by norm_num)
theorem B1787525 : Blo 794341 1787525 := bbase (se 4 (by rfl) ⟨167580, by rfl⟩ : syracuseStep 1787525 = 335161) (by norm_num)
theorem B1787597 : Blo 794341 1787597 := bbase (se 3 (by rfl) ⟨335174, by rfl⟩ : syracuseStep 1787597 = 670349) (by norm_num)
theorem B2017021 : Blo 794341 2017021 := bbase (se 3 (by rfl) ⟨378191, by rfl⟩ : syracuseStep 2017021 = 756383) (by norm_num)
theorem B1787669 : Blo 794341 1787669 := bbase (se 6 (by rfl) ⟨41898, by rfl⟩ : syracuseStep 1787669 = 83797) (by norm_num)
theorem B1787741 : Blo 794341 1787741 := bbase (se 3 (by rfl) ⟨335201, by rfl⟩ : syracuseStep 1787741 = 670403) (by norm_num)
theorem B2017133 : Blo 794341 2017133 := bbase (se 3 (by rfl) ⟨378212, by rfl⟩ : syracuseStep 2017133 = 756425) (by norm_num)
theorem B1787813 : Blo 794341 1787813 := bbase (se 4 (by rfl) ⟨167607, by rfl⟩ : syracuseStep 1787813 = 335215) (by norm_num)
theorem B4540373 : Blo 794341 4540373 := bbase (se 7 (by rfl) ⟨53207, by rfl⟩ : syracuseStep 4540373 = 106415) (by norm_num)
theorem B1787885 : Blo 794341 1787885 := bbase (se 3 (by rfl) ⟨335228, by rfl⟩ : syracuseStep 1787885 = 670457) (by norm_num)
theorem B2017325 : Blo 794341 2017325 := bbase (se 3 (by rfl) ⟨378248, by rfl⟩ : syracuseStep 2017325 = 756497) (by norm_num)
theorem B1787957 : Blo 794341 1787957 := bbase (se 5 (by rfl) ⟨83810, by rfl⟩ : syracuseStep 1787957 = 167621) (by norm_num)
theorem B1132661 : Blo 794341 1132661 := bbase (se 5 (by rfl) ⟨53093, by rfl⟩ : syracuseStep 1132661 = 106187) (by norm_num)
theorem B1722485 : Blo 794341 1722485 := bbase (se 5 (by rfl) ⟨80741, by rfl⟩ : syracuseStep 1722485 = 161483) (by norm_num)
theorem B1788029 : Blo 794341 1788029 := bbase (se 3 (by rfl) ⟨335255, by rfl⟩ : syracuseStep 1788029 = 670511) (by norm_num)
theorem B12601493 : Blo 794341 12601493 := bbase (se 6 (by rfl) ⟨295347, by rfl⟩ : syracuseStep 12601493 = 590695) (by norm_num)
theorem B1788101 : Blo 794341 1788101 := bbase (se 4 (by rfl) ⟨167634, by rfl⟩ : syracuseStep 1788101 = 335269) (by norm_num)
theorem B1132741 : Blo 794341 1132741 := bbase (se 4 (by rfl) ⟨106194, by rfl⟩ : syracuseStep 1132741 = 212389) (by norm_num)
theorem B1362125 : Blo 794341 1362125 := bbase (se 3 (by rfl) ⟨255398, by rfl⟩ : syracuseStep 1362125 = 510797) (by norm_num)
theorem B1788173 : Blo 794341 1788173 := bbase (se 3 (by rfl) ⟨335282, by rfl⟩ : syracuseStep 1788173 = 670565) (by norm_num)
theorem B1132861 : Blo 794341 1132861 := bbase (se 3 (by rfl) ⟨212411, by rfl⟩ : syracuseStep 1132861 = 424823) (by norm_num)
theorem B2148677 : Blo 794341 2148677 := bbase (se 4 (by rfl) ⟨201438, by rfl⟩ : syracuseStep 2148677 = 402877) (by norm_num)
theorem B1788245 : Blo 794341 1788245 := bbase (se 10 (by rfl) ⟨2619, by rfl⟩ : syracuseStep 1788245 = 5239) (by norm_num)
theorem B2017669 : Blo 794341 2017669 := bbase (se 4 (by rfl) ⟨189156, by rfl⟩ : syracuseStep 2017669 = 378313) (by norm_num)
theorem B1788317 : Blo 794341 1788317 := bbase (se 3 (by rfl) ⟨335309, by rfl⟩ : syracuseStep 1788317 = 670619) (by norm_num)
theorem B1132957 : Blo 794341 1132957 := bbase (se 3 (by rfl) ⟨212429, by rfl⟩ : syracuseStep 1132957 = 424859) (by norm_num)
theorem B2148773 : Blo 794341 2148773 := bbase (se 4 (by rfl) ⟨201447, by rfl⟩ : syracuseStep 2148773 = 402895) (by norm_num)
theorem B1788389 : Blo 794341 1788389 := bbase (se 4 (by rfl) ⟨167661, by rfl⟩ : syracuseStep 1788389 = 335323) (by norm_num)
theorem B2017781 : Blo 794341 2017781 := bbase (se 5 (by rfl) ⟨94583, by rfl⟩ : syracuseStep 2017781 = 189167) (by norm_num)
theorem B1788461 : Blo 794341 1788461 := bbase (se 3 (by rfl) ⟨335336, by rfl⟩ : syracuseStep 1788461 = 670673) (by norm_num)
theorem B1722989 : Blo 794341 1722989 := bbase (se 3 (by rfl) ⟨323060, by rfl⟩ : syracuseStep 1722989 = 646121) (by norm_num)
theorem B1788533 : Blo 794341 1788533 := bbase (se 5 (by rfl) ⟨83837, by rfl⟩ : syracuseStep 1788533 = 167675) (by norm_num)
theorem B2017973 : Blo 794341 2017973 := bbase (se 5 (by rfl) ⟨94592, by rfl⟩ : syracuseStep 2017973 = 189185) (by norm_num)
theorem B1788605 : Blo 794341 1788605 := bbase (se 3 (by rfl) ⟨335363, by rfl⟩ : syracuseStep 1788605 = 670727) (by norm_num)
theorem B1788677 : Blo 794341 1788677 := bbase (se 4 (by rfl) ⟨167688, by rfl⟩ : syracuseStep 1788677 = 335377) (by norm_num)
theorem B1788749 : Blo 794341 1788749 := bbase (se 3 (by rfl) ⟨335390, by rfl⟩ : syracuseStep 1788749 = 670781) (by norm_num)
theorem B1133453 : Blo 794341 1133453 := bbase (se 3 (by rfl) ⟨212522, by rfl⟩ : syracuseStep 1133453 = 425045) (by norm_num)
theorem B6441877 : Blo 794341 6441877 := bbase (se 6 (by rfl) ⟨150981, by rfl⟩ : syracuseStep 6441877 = 301963) (by norm_num)
theorem B1788821 : Blo 794341 1788821 := bbase (se 6 (by rfl) ⟨41925, by rfl⟩ : syracuseStep 1788821 = 83851) (by norm_num)
theorem B1788893 : Blo 794341 1788893 := bbase (se 3 (by rfl) ⟨335417, by rfl⟩ : syracuseStep 1788893 = 670835) (by norm_num)
theorem B2018317 : Blo 794341 2018317 := bbase (se 3 (by rfl) ⟨378434, by rfl⟩ : syracuseStep 2018317 = 756869) (by norm_num)
theorem B1788965 : Blo 794341 1788965 := bbase (se 4 (by rfl) ⟨167715, by rfl⟩ : syracuseStep 1788965 = 335431) (by norm_num)
theorem B805961 : Blo 794341 805961 := bbase (se 2 (by rfl) ⟨302235, by rfl⟩ : syracuseStep 805961 = 604471) (by norm_num)
theorem B969833 : Blo 794341 969833 := bbase (se 2 (by rfl) ⟨363687, by rfl⟩ : syracuseStep 969833 = 727375) (by norm_num)
theorem B1789037 : Blo 794341 1789037 := bbase (se 3 (by rfl) ⟨335444, by rfl⟩ : syracuseStep 1789037 = 670889) (by norm_num)
theorem B2018429 : Blo 794341 2018429 := bbase (se 3 (by rfl) ⟨378455, by rfl⟩ : syracuseStep 2018429 = 756911) (by norm_num)
theorem B1789109 : Blo 794341 1789109 := bbase (se 5 (by rfl) ⟨83864, by rfl⟩ : syracuseStep 1789109 = 167729) (by norm_num)
theorem B3067109 : Blo 794341 3067109 := bbase (se 4 (by rfl) ⟨287541, by rfl⟩ : syracuseStep 3067109 = 575083) (by norm_num)
theorem B1789181 : Blo 794341 1789181 := bbase (se 3 (by rfl) ⟨335471, by rfl⟩ : syracuseStep 1789181 = 670943) (by norm_num)
theorem B2018621 : Blo 794341 2018621 := bbase (se 3 (by rfl) ⟨378491, by rfl⟩ : syracuseStep 2018621 = 756983) (by norm_num)
theorem B1789253 : Blo 794341 1789253 := bbase (se 4 (by rfl) ⟨167742, by rfl⟩ : syracuseStep 1789253 = 335485) (by norm_num)
theorem B1789325 : Blo 794341 1789325 := bbase (se 3 (by rfl) ⟨335498, by rfl⟩ : syracuseStep 1789325 = 670997) (by norm_num)
theorem B1134005 : Blo 794341 1134005 := bbase (se 5 (by rfl) ⟨53156, by rfl⟩ : syracuseStep 1134005 = 106313) (by norm_num)
theorem B1789397 : Blo 794341 1789397 := bbase (se 7 (by rfl) ⟨20969, by rfl⟩ : syracuseStep 1789397 = 41939) (by norm_num)
theorem B2870741 : Blo 794341 2870741 := bbase (se 7 (by rfl) ⟨33641, by rfl⟩ : syracuseStep 2870741 = 67283) (by norm_num)
theorem B4312597 : Blo 794341 4312597 := bbase (se 6 (by rfl) ⟨101076, by rfl⟩ : syracuseStep 4312597 = 202153) (by norm_num)
theorem B1789469 : Blo 794341 1789469 := bbase (se 3 (by rfl) ⟨335525, by rfl⟩ : syracuseStep 1789469 = 671051) (by norm_num)
theorem B1363493 : Blo 794341 1363493 := bbase (se 4 (by rfl) ⟨127827, by rfl⟩ : syracuseStep 1363493 = 255655) (by norm_num)
theorem B1789541 : Blo 794341 1789541 := bbase (se 4 (by rfl) ⟨167769, by rfl⟩ : syracuseStep 1789541 = 335539) (by norm_num)
theorem B2018965 : Blo 794341 2018965 := bbase (se 6 (by rfl) ⟨47319, by rfl⟩ : syracuseStep 2018965 = 94639) (by norm_num)
theorem B1789613 : Blo 794341 1789613 := bbase (se 3 (by rfl) ⟨335552, by rfl⟩ : syracuseStep 1789613 = 671105) (by norm_num)
theorem B1789685 : Blo 794341 1789685 := bbase (se 5 (by rfl) ⟨83891, by rfl⟩ : syracuseStep 1789685 = 167783) (by norm_num)
theorem B2019077 : Blo 794341 2019077 := bbase (se 4 (by rfl) ⟨189288, by rfl⟩ : syracuseStep 2019077 = 378577) (by norm_num)
theorem B3624725 : Blo 794341 3624725 := bbase (se 6 (by rfl) ⟨84954, by rfl⟩ : syracuseStep 3624725 = 169909) (by norm_num)
theorem B1789757 : Blo 794341 1789757 := bbase (se 3 (by rfl) ⟨335579, by rfl⟩ : syracuseStep 1789757 = 671159) (by norm_num)
theorem B1396565 : Blo 794341 1396565 := bbase (se 9 (by rfl) ⟨4091, by rfl⟩ : syracuseStep 1396565 = 8183) (by norm_num)
theorem B1789829 : Blo 794341 1789829 := bbase (se 4 (by rfl) ⟨167796, by rfl⟩ : syracuseStep 1789829 = 335593) (by norm_num)
theorem B2019269 : Blo 794341 2019269 := bbase (se 4 (by rfl) ⟨189306, by rfl⟩ : syracuseStep 2019269 = 378613) (by norm_num)
theorem B1789901 : Blo 794341 1789901 := bbase (se 3 (by rfl) ⟨335606, by rfl⟩ : syracuseStep 1789901 = 671213) (by norm_num)
theorem B806869 : Blo 794341 806869 := bbase (se 7 (by rfl) ⟨9455, by rfl⟩ : syracuseStep 806869 = 18911) (by norm_num)
theorem B970729 : Blo 794341 970729 := bbase (se 2 (by rfl) ⟨364023, by rfl⟩ : syracuseStep 970729 = 728047) (by norm_num)
theorem B1789973 : Blo 794341 1789973 := bbase (se 6 (by rfl) ⟨41952, by rfl⟩ : syracuseStep 1789973 = 83905) (by norm_num)
theorem B1790045 : Blo 794341 1790045 := bbase (se 3 (by rfl) ⟨335633, by rfl⟩ : syracuseStep 1790045 = 671267) (by norm_num)
theorem B4542581 : Blo 794341 4542581 := bbase (se 5 (by rfl) ⟨212933, by rfl⟩ : syracuseStep 4542581 = 425867) (by norm_num)
theorem B1790117 : Blo 794341 1790117 := bbase (se 4 (by rfl) ⟨167823, by rfl⟩ : syracuseStep 1790117 = 335647) (by norm_num)
theorem B1134757 : Blo 794341 1134757 := bbase (se 4 (by rfl) ⟨106383, by rfl⟩ : syracuseStep 1134757 = 212767) (by norm_num)
theorem B1790189 : Blo 794341 1790189 := bbase (se 3 (by rfl) ⟨335660, by rfl⟩ : syracuseStep 1790189 = 671321) (by norm_num)
theorem B2019613 : Blo 794341 2019613 := bbase (se 3 (by rfl) ⟨378677, by rfl⟩ : syracuseStep 2019613 = 757355) (by norm_num)
theorem B1790261 : Blo 794341 1790261 := bbase (se 5 (by rfl) ⟨83918, by rfl⟩ : syracuseStep 1790261 = 167837) (by norm_num)
theorem B1790333 : Blo 794341 1790333 := bbase (se 3 (by rfl) ⟨335687, by rfl⟩ : syracuseStep 1790333 = 671375) (by norm_num)
theorem B2019725 : Blo 794341 2019725 := bbase (se 3 (by rfl) ⟨378698, by rfl⟩ : syracuseStep 2019725 = 757397) (by norm_num)
theorem B1790405 : Blo 794341 1790405 := bbase (se 4 (by rfl) ⟨167850, by rfl⟩ : syracuseStep 1790405 = 335701) (by norm_num)
theorem B1790477 : Blo 794341 1790477 := bbase (se 3 (by rfl) ⟨335714, by rfl⟩ : syracuseStep 1790477 = 671429) (by norm_num)
theorem B807445 : Blo 794341 807445 := bbase (se 6 (by rfl) ⟨18924, by rfl⟩ : syracuseStep 807445 = 37849) (by norm_num)
theorem B2019917 : Blo 794341 2019917 := bbase (se 3 (by rfl) ⟨378734, by rfl⟩ : syracuseStep 2019917 = 757469) (by norm_num)
theorem B1790549 : Blo 794341 1790549 := bbase (se 8 (by rfl) ⟨10491, by rfl⟩ : syracuseStep 1790549 = 20983) (by norm_num)
theorem B1790621 : Blo 794341 1790621 := bbase (se 3 (by rfl) ⟨335741, by rfl⟩ : syracuseStep 1790621 = 671483) (by norm_num)
theorem B1790693 : Blo 794341 1790693 := bbase (se 4 (by rfl) ⟨167877, by rfl⟩ : syracuseStep 1790693 = 335755) (by norm_num)
theorem B1790765 : Blo 794341 1790765 := bbase (se 3 (by rfl) ⟨335768, by rfl⟩ : syracuseStep 1790765 = 671537) (by norm_num)
theorem B3068725 : Blo 794341 3068725 := bbase (se 5 (by rfl) ⟨143846, by rfl⟩ : syracuseStep 3068725 = 287693) (by norm_num)
theorem B1037125 : Blo 794341 1037125 := bbase (se 4 (by rfl) ⟨97230, by rfl⟩ : syracuseStep 1037125 = 194461) (by norm_num)
theorem B1790837 : Blo 794341 1790837 := bbase (se 5 (by rfl) ⟨83945, by rfl⟩ : syracuseStep 1790837 = 167891) (by norm_num)
theorem B2872181 : Blo 794341 2872181 := bbase (se 5 (by rfl) ⟨134633, by rfl⟩ : syracuseStep 2872181 = 269267) (by norm_num)
theorem B2020261 : Blo 794341 2020261 := bbase (se 4 (by rfl) ⟨189399, by rfl⟩ : syracuseStep 2020261 = 378799) (by norm_num)
theorem B1790909 : Blo 794341 1790909 := bbase (se 3 (by rfl) ⟨335795, by rfl⟩ : syracuseStep 1790909 = 671591) (by norm_num)
theorem B1135549 : Blo 794341 1135549 := bbase (se 3 (by rfl) ⟨212915, by rfl⟩ : syracuseStep 1135549 = 425831) (by norm_num)
theorem B1790981 : Blo 794341 1790981 := bbase (se 4 (by rfl) ⟨167904, by rfl⟩ : syracuseStep 1790981 = 335809) (by norm_num)
theorem B2020373 : Blo 794341 2020373 := bbase (se 6 (by rfl) ⟨47352, by rfl⟩ : syracuseStep 2020373 = 94705) (by norm_num)
theorem B906277 : Blo 794341 906277 := bbase (se 4 (by rfl) ⟨84963, by rfl⟩ : syracuseStep 906277 = 169927) (by norm_num)
theorem B1791053 : Blo 794341 1791053 := bbase (se 3 (by rfl) ⟨335822, by rfl⟩ : syracuseStep 1791053 = 671645) (by norm_num)
theorem B808013 : Blo 794341 808013 := bbase (se 3 (by rfl) ⟨151502, by rfl⟩ : syracuseStep 808013 = 303005) (by norm_num)
theorem B1791125 : Blo 794341 1791125 := bbase (se 6 (by rfl) ⟨41979, by rfl⟩ : syracuseStep 1791125 = 83959) (by norm_num)
theorem B2020565 : Blo 794341 2020565 := bbase (se 7 (by rfl) ⟨23678, by rfl⟩ : syracuseStep 2020565 = 47357) (by norm_num)
theorem B1791197 : Blo 794341 1791197 := bbase (se 3 (by rfl) ⟨335849, by rfl⟩ : syracuseStep 1791197 = 671699) (by norm_num)
theorem B1365245 : Blo 794341 1365245 := bbase (se 3 (by rfl) ⟨255983, by rfl⟩ : syracuseStep 1365245 = 511967) (by norm_num)
theorem B1135885 : Blo 794341 1135885 := bbase (se 3 (by rfl) ⟨212978, by rfl⟩ : syracuseStep 1135885 = 425957) (by norm_num)
theorem B1791269 : Blo 794341 1791269 := bbase (se 4 (by rfl) ⟨167931, by rfl⟩ : syracuseStep 1791269 = 335863) (by norm_num)
theorem B1791341 : Blo 794341 1791341 := bbase (se 3 (by rfl) ⟨335876, by rfl⟩ : syracuseStep 1791341 = 671753) (by norm_num)
theorem B7853429 : Blo 794341 7853429 := bbase (se 5 (by rfl) ⟨368129, by rfl⟩ : syracuseStep 7853429 = 736259) (by norm_num)
theorem B1791413 : Blo 794341 1791413 := bbase (se 5 (by rfl) ⟨83972, by rfl⟩ : syracuseStep 1791413 = 167945) (by norm_num)
theorem B808385 : Blo 794341 808385 := bbase (se 2 (by rfl) ⟨303144, by rfl⟩ : syracuseStep 808385 = 606289) (by norm_num)
theorem B1136101 : Blo 794341 1136101 := bbase (se 4 (by rfl) ⟨106509, by rfl⟩ : syracuseStep 1136101 = 213019) (by norm_num)
theorem B1791485 : Blo 794341 1791485 := bbase (se 3 (by rfl) ⟨335903, by rfl⟩ : syracuseStep 1791485 = 671807) (by norm_num)
theorem B1791557 : Blo 794341 1791557 := bbase (se 4 (by rfl) ⟨167958, by rfl⟩ : syracuseStep 1791557 = 335917) (by norm_num)
theorem B1791629 : Blo 794341 1791629 := bbase (se 3 (by rfl) ⟨335930, by rfl⟩ : syracuseStep 1791629 = 671861) (by norm_num)
theorem B3397301 : Blo 794341 3397301 := bbase (se 5 (by rfl) ⟨159248, by rfl⟩ : syracuseStep 3397301 = 318497) (by norm_num)
theorem B1791701 : Blo 794341 1791701 := bbase (se 7 (by rfl) ⟨20996, by rfl⟩ : syracuseStep 1791701 = 41993) (by norm_num)
theorem B808685 : Blo 794341 808685 := bbase (se 3 (by rfl) ⟨151628, by rfl⟩ : syracuseStep 808685 = 303257) (by norm_num)
theorem B1791773 : Blo 794341 1791773 := bbase (se 3 (by rfl) ⟨335957, by rfl⟩ : syracuseStep 1791773 = 671915) (by norm_num)
theorem B907057 : Blo 794341 907057 := bbase (se 2 (by rfl) ⟨340146, by rfl⟩ : syracuseStep 907057 = 680293) (by norm_num)
theorem B1136477 : Blo 794341 1136477 := bbase (se 3 (by rfl) ⟨213089, by rfl⟩ : syracuseStep 1136477 = 426179) (by norm_num)
theorem B1791845 : Blo 794341 1791845 := bbase (se 4 (by rfl) ⟨167985, by rfl⟩ : syracuseStep 1791845 = 335971) (by norm_num)
theorem B6805397 : Blo 794341 6805397 := bbase (se 6 (by rfl) ⟨159501, by rfl⟩ : syracuseStep 6805397 = 319003) (by norm_num)
theorem B1005473 : Blo 794341 1005473 := bbase (se 2 (by rfl) ⟨377052, by rfl⟩ : syracuseStep 1005473 = 754105) (by norm_num)
theorem B1791917 : Blo 794341 1791917 := bbase (se 3 (by rfl) ⟨335984, by rfl⟩ : syracuseStep 1791917 = 671969) (by norm_num)
theorem B808913 : Blo 794341 808913 := bbase (se 2 (by rfl) ⟨303342, by rfl⟩ : syracuseStep 808913 = 606685) (by norm_num)
theorem B1005529 : Blo 794341 1005529 := bbase (se 2 (by rfl) ⟨377073, by rfl⟩ : syracuseStep 1005529 = 754147) (by norm_num)
theorem B1791989 : Blo 794341 1791989 := bbase (se 5 (by rfl) ⟨83999, by rfl⟩ : syracuseStep 1791989 = 167999) (by norm_num)
theorem B1005625 : Blo 794341 1005625 := bbase (se 2 (by rfl) ⟨377109, by rfl⟩ : syracuseStep 1005625 = 754219) (by norm_num)
theorem B1792061 : Blo 794341 1792061 := bbase (se 3 (by rfl) ⟨336011, by rfl⟩ : syracuseStep 1792061 = 672023) (by norm_num)
theorem B1792133 : Blo 794341 1792133 := bbase (se 4 (by rfl) ⟨168012, by rfl⟩ : syracuseStep 1792133 = 336025) (by norm_num)
theorem B1792205 : Blo 794341 1792205 := bbase (se 3 (by rfl) ⟨336038, by rfl⟩ : syracuseStep 1792205 = 672077) (by norm_num)
theorem B1005797 : Blo 794341 1005797 := bbase (se 4 (by rfl) ⟨94293, by rfl⟩ : syracuseStep 1005797 = 188587) (by norm_num)
theorem B1792277 : Blo 794341 1792277 := bbase (se 6 (by rfl) ⟨42006, by rfl⟩ : syracuseStep 1792277 = 84013) (by norm_num)
theorem B1005853 : Blo 794341 1005853 := bbase (se 3 (by rfl) ⟨188597, by rfl⟩ : syracuseStep 1005853 = 377195) (by norm_num)
theorem B1792349 : Blo 794341 1792349 := bbase (se 3 (by rfl) ⟨336065, by rfl⟩ : syracuseStep 1792349 = 672131) (by norm_num)
theorem B1005949 : Blo 794341 1005949 := bbase (se 3 (by rfl) ⟨188615, by rfl⟩ : syracuseStep 1005949 = 377231) (by norm_num)
theorem B1792421 : Blo 794341 1792421 := bbase (se 4 (by rfl) ⟨168039, by rfl⟩ : syracuseStep 1792421 = 336079) (by norm_num)
theorem B1792493 : Blo 794341 1792493 := bbase (se 3 (by rfl) ⟨336092, by rfl⟩ : syracuseStep 1792493 = 672185) (by norm_num)
theorem B1006121 : Blo 794341 1006121 := bbase (se 2 (by rfl) ⟨377295, by rfl⟩ : syracuseStep 1006121 = 754591) (by norm_num)
theorem B1792565 : Blo 794341 1792565 := bbase (se 5 (by rfl) ⟨84026, by rfl⟩ : syracuseStep 1792565 = 168053) (by norm_num)
theorem B1006177 : Blo 794341 1006177 := bbase (se 2 (by rfl) ⟨377316, by rfl⟩ : syracuseStep 1006177 = 754633) (by norm_num)
theorem B1792637 : Blo 794341 1792637 := bbase (se 3 (by rfl) ⟨336119, by rfl⟩ : syracuseStep 1792637 = 672239) (by norm_num)
theorem B1006273 : Blo 794341 1006273 := bbase (se 2 (by rfl) ⟨377352, by rfl⟩ : syracuseStep 1006273 = 754705) (by norm_num)
theorem B1792709 : Blo 794341 1792709 := bbase (se 4 (by rfl) ⟨168066, by rfl⟩ : syracuseStep 1792709 = 336133) (by norm_num)
theorem B1792781 : Blo 794341 1792781 := bbase (se 3 (by rfl) ⟨336146, by rfl⟩ : syracuseStep 1792781 = 672293) (by norm_num)
theorem B1792853 : Blo 794341 1792853 := bbase (se 9 (by rfl) ⟨5252, by rfl⟩ : syracuseStep 1792853 = 10505) (by norm_num)
theorem B1006445 : Blo 794341 1006445 := bbase (se 3 (by rfl) ⟨188708, by rfl⟩ : syracuseStep 1006445 = 377417) (by norm_num)
theorem B1792925 : Blo 794341 1792925 := bbase (se 3 (by rfl) ⟨336173, by rfl⟩ : syracuseStep 1792925 = 672347) (by norm_num)
theorem B1006501 : Blo 794341 1006501 := bbase (se 4 (by rfl) ⟨94359, by rfl⟩ : syracuseStep 1006501 = 188719) (by norm_num)
theorem B1792997 : Blo 794341 1792997 := bbase (se 4 (by rfl) ⟨168093, by rfl⟩ : syracuseStep 1792997 = 336187) (by norm_num)
theorem B1006597 : Blo 794341 1006597 := bbase (se 4 (by rfl) ⟨94368, by rfl⟩ : syracuseStep 1006597 = 188737) (by norm_num)
theorem B1793069 : Blo 794341 1793069 := bbase (se 3 (by rfl) ⟨336200, by rfl⟩ : syracuseStep 1793069 = 672401) (by norm_num)
theorem B1793141 : Blo 794341 1793141 := bbase (se 5 (by rfl) ⟨84053, by rfl⟩ : syracuseStep 1793141 = 168107) (by norm_num)
theorem B1006769 : Blo 794341 1006769 := bbase (se 2 (by rfl) ⟨377538, by rfl⟩ : syracuseStep 1006769 = 755077) (by norm_num)
theorem B1793213 : Blo 794341 1793213 := bbase (se 3 (by rfl) ⟨336227, by rfl⟩ : syracuseStep 1793213 = 672455) (by norm_num)
theorem B1006825 : Blo 794341 1006825 := bbase (se 2 (by rfl) ⟨377559, by rfl⟩ : syracuseStep 1006825 = 755119) (by norm_num)
theorem B1793285 : Blo 794341 1793285 := bbase (se 4 (by rfl) ⟨168120, by rfl⟩ : syracuseStep 1793285 = 336241) (by norm_num)
theorem B1006921 : Blo 794341 1006921 := bbase (se 2 (by rfl) ⟨377595, by rfl⟩ : syracuseStep 1006921 = 755191) (by norm_num)
theorem B1793357 : Blo 794341 1793357 := bbase (se 3 (by rfl) ⟨336254, by rfl⟩ : syracuseStep 1793357 = 672509) (by norm_num)
theorem B1793429 : Blo 794341 1793429 := bbase (se 6 (by rfl) ⟨42033, by rfl⟩ : syracuseStep 1793429 = 84067) (by norm_num)
theorem B3399077 : Blo 794341 3399077 := bbase (se 4 (by rfl) ⟨318663, by rfl⟩ : syracuseStep 3399077 = 637327) (by norm_num)
theorem B1793501 : Blo 794341 1793501 := bbase (se 3 (by rfl) ⟨336281, by rfl⟩ : syracuseStep 1793501 = 672563) (by norm_num)
theorem B1007093 : Blo 794341 1007093 := bbase (se 5 (by rfl) ⟨47207, by rfl⟩ : syracuseStep 1007093 = 94415) (by norm_num)
theorem B1793573 : Blo 794341 1793573 := bbase (se 4 (by rfl) ⟨168147, by rfl⟩ : syracuseStep 1793573 = 336295) (by norm_num)
theorem B1007149 : Blo 794341 1007149 := bbase (se 3 (by rfl) ⟨188840, by rfl⟩ : syracuseStep 1007149 = 377681) (by norm_num)
theorem B1793645 : Blo 794341 1793645 := bbase (se 3 (by rfl) ⟨336308, by rfl⟩ : syracuseStep 1793645 = 672617) (by norm_num)
theorem B3825269 : Blo 794341 3825269 := bbase (se 5 (by rfl) ⟨179309, by rfl⟩ : syracuseStep 3825269 = 358619) (by norm_num)
theorem B1007245 : Blo 794341 1007245 := bbase (se 3 (by rfl) ⟨188858, by rfl⟩ : syracuseStep 1007245 = 377717) (by norm_num)
theorem B3399317 : Blo 794341 3399317 := bbase (se 6 (by rfl) ⟨79671, by rfl⟩ : syracuseStep 3399317 = 159343) (by norm_num)
theorem B1793717 : Blo 794341 1793717 := bbase (se 5 (by rfl) ⟨84080, by rfl⟩ : syracuseStep 1793717 = 168161) (by norm_num)
theorem B4021973 : Blo 794341 4021973 := bbase (se 7 (by rfl) ⟨47132, by rfl⟩ : syracuseStep 4021973 = 94265) (by norm_num)
theorem B1433317 : Blo 794341 1433317 := bbase (se 4 (by rfl) ⟨134373, by rfl⟩ : syracuseStep 1433317 = 268747) (by norm_num)
theorem B1793789 : Blo 794341 1793789 := bbase (se 3 (by rfl) ⟨336335, by rfl⟩ : syracuseStep 1793789 = 672671) (by norm_num)
theorem B1007417 : Blo 794341 1007417 := bbase (se 2 (by rfl) ⟨377781, by rfl⟩ : syracuseStep 1007417 = 755563) (by norm_num)
theorem B1793861 : Blo 794341 1793861 := bbase (se 4 (by rfl) ⟨168174, by rfl⟩ : syracuseStep 1793861 = 336349) (by norm_num)
theorem B1007473 : Blo 794341 1007473 := bbase (se 2 (by rfl) ⟨377802, by rfl⟩ : syracuseStep 1007473 = 755605) (by norm_num)
theorem B1793933 : Blo 794341 1793933 := bbase (se 3 (by rfl) ⟨336362, by rfl⟩ : syracuseStep 1793933 = 672725) (by norm_num)
theorem B2547605 : Blo 794341 2547605 := bbase (se 6 (by rfl) ⟨59709, by rfl⟩ : syracuseStep 2547605 = 119419) (by norm_num)
theorem B1007569 : Blo 794341 1007569 := bbase (se 2 (by rfl) ⟨377838, by rfl⟩ : syracuseStep 1007569 = 755677) (by norm_num)
theorem B1794005 : Blo 794341 1794005 := bbase (se 7 (by rfl) ⟨21023, by rfl⟩ : syracuseStep 1794005 = 42047) (by norm_num)
theorem B1794077 : Blo 794341 1794077 := bbase (se 3 (by rfl) ⟨336389, by rfl⟩ : syracuseStep 1794077 = 672779) (by norm_num)
theorem B1794149 : Blo 794341 1794149 := bbase (se 4 (by rfl) ⟨168201, by rfl⟩ : syracuseStep 1794149 = 336403) (by norm_num)
theorem B1007741 : Blo 794341 1007741 := bbase (se 3 (by rfl) ⟨188951, by rfl⟩ : syracuseStep 1007741 = 377903) (by norm_num)
theorem B1794221 : Blo 794341 1794221 := bbase (se 3 (by rfl) ⟨336416, by rfl⟩ : syracuseStep 1794221 = 672833) (by norm_num)
theorem B1007797 : Blo 794341 1007797 := bbase (se 5 (by rfl) ⟨47240, by rfl⟩ : syracuseStep 1007797 = 94481) (by norm_num)
theorem B6054101 : Blo 794341 6054101 := bbase (se 7 (by rfl) ⟨70946, by rfl⟩ : syracuseStep 6054101 = 141893) (by norm_num)
theorem B909553 : Blo 794341 909553 := bbase (se 2 (by rfl) ⟨341082, by rfl⟩ : syracuseStep 909553 = 682165) (by norm_num)
theorem B1794293 : Blo 794341 1794293 := bbase (se 5 (by rfl) ⟨84107, by rfl⟩ : syracuseStep 1794293 = 168215) (by norm_num)
theorem B1007893 : Blo 794341 1007893 := bbase (se 6 (by rfl) ⟨23622, by rfl⟩ : syracuseStep 1007893 = 47245) (by norm_num)
theorem B1794365 : Blo 794341 1794365 := bbase (se 3 (by rfl) ⟨336443, by rfl⟩ : syracuseStep 1794365 = 672887) (by norm_num)
theorem B1794437 : Blo 794341 1794437 := bbase (se 4 (by rfl) ⟨168228, by rfl⟩ : syracuseStep 1794437 = 336457) (by norm_num)
theorem B1008065 : Blo 794341 1008065 := bbase (se 2 (by rfl) ⟨378024, by rfl⟩ : syracuseStep 1008065 = 756049) (by norm_num)
theorem B1794509 : Blo 794341 1794509 := bbase (se 3 (by rfl) ⟨336470, by rfl⟩ : syracuseStep 1794509 = 672941) (by norm_num)
theorem B1008121 : Blo 794341 1008121 := bbase (se 2 (by rfl) ⟨378045, by rfl⟩ : syracuseStep 1008121 = 756091) (by norm_num)
theorem B1794581 : Blo 794341 1794581 := bbase (se 6 (by rfl) ⟨42060, by rfl⟩ : syracuseStep 1794581 = 84121) (by norm_num)
theorem B1008217 : Blo 794341 1008217 := bbase (se 2 (by rfl) ⟨378081, by rfl⟩ : syracuseStep 1008217 = 756163) (by norm_num)
theorem B1794653 : Blo 794341 1794653 := bbase (se 3 (by rfl) ⟨336497, by rfl⟩ : syracuseStep 1794653 = 672995) (by norm_num)
theorem B1434245 : Blo 794341 1434245 := bbase (se 4 (by rfl) ⟨134460, by rfl⟩ : syracuseStep 1434245 = 268921) (by norm_num)
theorem B1794725 : Blo 794341 1794725 := bbase (se 4 (by rfl) ⟨168255, by rfl⟩ : syracuseStep 1794725 = 336511) (by norm_num)
theorem B1532629 : Blo 794341 1532629 := bbase (se 7 (by rfl) ⟨17960, by rfl⟩ : syracuseStep 1532629 = 35921) (by norm_num)
theorem B1794797 : Blo 794341 1794797 := bbase (se 3 (by rfl) ⟨336524, by rfl⟩ : syracuseStep 1794797 = 673049) (by norm_num)
theorem B1008389 : Blo 794341 1008389 := bbase (se 4 (by rfl) ⟨94536, by rfl⟩ : syracuseStep 1008389 = 189073) (by norm_num)
theorem B6808373 : Blo 794341 6808373 := bbase (se 5 (by rfl) ⟨319142, by rfl⟩ : syracuseStep 6808373 = 638285) (by norm_num)
theorem B1794869 : Blo 794341 1794869 := bbase (se 5 (by rfl) ⟨84134, by rfl⟩ : syracuseStep 1794869 = 168269) (by norm_num)
theorem B1008445 : Blo 794341 1008445 := bbase (se 3 (by rfl) ⟨189083, by rfl⟩ : syracuseStep 1008445 = 378167) (by norm_num)
theorem B1794941 : Blo 794341 1794941 := bbase (se 3 (by rfl) ⟨336551, by rfl⟩ : syracuseStep 1794941 = 673103) (by norm_num)
theorem B1008541 : Blo 794341 1008541 := bbase (se 3 (by rfl) ⟨189101, by rfl⟩ : syracuseStep 1008541 = 378203) (by norm_num)
theorem B1795013 : Blo 794341 1795013 := bbase (se 4 (by rfl) ⟨168282, by rfl⟩ : syracuseStep 1795013 = 336565) (by norm_num)
theorem B2155477 : Blo 794341 2155477 := bbase (se 7 (by rfl) ⟨25259, by rfl⟩ : syracuseStep 2155477 = 50519) (by norm_num)
theorem B4023269 : Blo 794341 4023269 := bbase (se 4 (by rfl) ⟨377181, by rfl⟩ : syracuseStep 4023269 = 754363) (by norm_num)
theorem B1795085 : Blo 794341 1795085 := bbase (se 3 (by rfl) ⟨336578, by rfl⟩ : syracuseStep 1795085 = 673157) (by norm_num)
theorem B1696805 : Blo 794341 1696805 := bbase (se 4 (by rfl) ⟨159075, by rfl⟩ : syracuseStep 1696805 = 318151) (by norm_num)
theorem B1008713 : Blo 794341 1008713 := bbase (se 2 (by rfl) ⟨378267, by rfl⟩ : syracuseStep 1008713 = 756535) (by norm_num)
theorem B1795157 : Blo 794341 1795157 := bbase (se 8 (by rfl) ⟨10518, by rfl⟩ : syracuseStep 1795157 = 21037) (by norm_num)
theorem B1008769 : Blo 794341 1008769 := bbase (se 2 (by rfl) ⟨378288, by rfl⟩ : syracuseStep 1008769 = 756577) (by norm_num)
theorem B1696925 : Blo 794341 1696925 := bbase (se 3 (by rfl) ⟨318173, by rfl⟩ : syracuseStep 1696925 = 636347) (by norm_num)
theorem B1795229 : Blo 794341 1795229 := bbase (se 3 (by rfl) ⟨336605, by rfl⟩ : syracuseStep 1795229 = 673211) (by norm_num)
theorem B3826885 : Blo 794341 3826885 := bbase (se 4 (by rfl) ⟨358770, by rfl⟩ : syracuseStep 3826885 = 717541) (by norm_num)
theorem B1008865 : Blo 794341 1008865 := bbase (se 2 (by rfl) ⟨378324, by rfl⟩ : syracuseStep 1008865 = 756649) (by norm_num)
theorem B1795301 : Blo 794341 1795301 := bbase (se 4 (by rfl) ⟨168309, by rfl⟩ : syracuseStep 1795301 = 336619) (by norm_num)
theorem B1795373 : Blo 794341 1795373 := bbase (se 3 (by rfl) ⟨336632, by rfl⟩ : syracuseStep 1795373 = 673265) (by norm_num)
theorem B1434989 : Blo 794341 1434989 := bbase (se 3 (by rfl) ⟨269060, by rfl⟩ : syracuseStep 1434989 = 538121) (by norm_num)
theorem B1795445 : Blo 794341 1795445 := bbase (se 5 (by rfl) ⟨84161, by rfl⟩ : syracuseStep 1795445 = 168323) (by norm_num)
theorem B1009037 : Blo 794341 1009037 := bbase (se 3 (by rfl) ⟨189194, by rfl⟩ : syracuseStep 1009037 = 378389) (by norm_num)
theorem B2418101 : Blo 794341 2418101 := bbase (se 5 (by rfl) ⟨113348, by rfl⟩ : syracuseStep 2418101 = 226697) (by norm_num)
theorem B1795517 : Blo 794341 1795517 := bbase (se 3 (by rfl) ⟨336659, by rfl⟩ : syracuseStep 1795517 = 673319) (by norm_num)
theorem B1009093 : Blo 794341 1009093 := bbase (se 4 (by rfl) ⟨94602, by rfl⟩ : syracuseStep 1009093 = 189205) (by norm_num)
theorem B1795589 : Blo 794341 1795589 := bbase (se 4 (by rfl) ⟨168336, by rfl⟩ : syracuseStep 1795589 = 336673) (by norm_num)
theorem B1009189 : Blo 794341 1009189 := bbase (se 4 (by rfl) ⟨94611, by rfl⟩ : syracuseStep 1009189 = 189223) (by norm_num)
theorem B1795661 : Blo 794341 1795661 := bbase (se 3 (by rfl) ⟨336686, by rfl⟩ : syracuseStep 1795661 = 673373) (by norm_num)
theorem B1795733 : Blo 794341 1795733 := bbase (se 6 (by rfl) ⟨42087, by rfl⟩ : syracuseStep 1795733 = 84175) (by norm_num)
theorem B1009361 : Blo 794341 1009361 := bbase (se 2 (by rfl) ⟨378510, by rfl⟩ : syracuseStep 1009361 = 757021) (by norm_num)
theorem B1795805 : Blo 794341 1795805 := bbase (se 3 (by rfl) ⟨336713, by rfl⟩ : syracuseStep 1795805 = 673427) (by norm_num)
theorem B1009417 : Blo 794341 1009417 := bbase (se 2 (by rfl) ⟨378531, by rfl⟩ : syracuseStep 1009417 = 757063) (by norm_num)
theorem B1697557 : Blo 794341 1697557 := bbase (se 6 (by rfl) ⟨39786, by rfl⟩ : syracuseStep 1697557 = 79573) (by norm_num)
theorem B1795877 : Blo 794341 1795877 := bbase (se 4 (by rfl) ⟨168363, by rfl⟩ : syracuseStep 1795877 = 336727) (by norm_num)
theorem B1009513 : Blo 794341 1009513 := bbase (se 2 (by rfl) ⟨378567, by rfl⟩ : syracuseStep 1009513 = 757135) (by norm_num)
theorem B1795949 : Blo 794341 1795949 := bbase (se 3 (by rfl) ⟨336740, by rfl⟩ : syracuseStep 1795949 = 673481) (by norm_num)
theorem B3401605 : Blo 794341 3401605 := bbase (se 4 (by rfl) ⟨318900, by rfl⟩ : syracuseStep 3401605 = 637801) (by norm_num)
theorem B1796021 : Blo 794341 1796021 := bbase (se 5 (by rfl) ⟨84188, by rfl⟩ : syracuseStep 1796021 = 168377) (by norm_num)
theorem B1796093 : Blo 794341 1796093 := bbase (se 3 (by rfl) ⟨336767, by rfl⟩ : syracuseStep 1796093 = 673535) (by norm_num)
theorem B1009685 : Blo 794341 1009685 := bbase (se 6 (by rfl) ⟨23664, by rfl⟩ : syracuseStep 1009685 = 47329) (by norm_num)
theorem B1796165 : Blo 794341 1796165 := bbase (se 4 (by rfl) ⟨168390, by rfl⟩ : syracuseStep 1796165 = 336781) (by norm_num)
theorem B1009741 : Blo 794341 1009741 := bbase (se 3 (by rfl) ⟨189326, by rfl⟩ : syracuseStep 1009741 = 378653) (by norm_num)
theorem B1796237 : Blo 794341 1796237 := bbase (se 3 (by rfl) ⟨336794, by rfl⟩ : syracuseStep 1796237 = 673589) (by norm_num)
theorem B1009837 : Blo 794341 1009837 := bbase (se 3 (by rfl) ⟨189344, by rfl⟩ : syracuseStep 1009837 = 378689) (by norm_num)
theorem B2681045 : Blo 794341 2681045 := bbase (se 7 (by rfl) ⟨31418, by rfl⟩ : syracuseStep 2681045 = 62837) (by norm_num)
theorem B4024565 : Blo 794341 4024565 := bbase (se 5 (by rfl) ⟨188651, by rfl⟩ : syracuseStep 4024565 = 377303) (by norm_num)
theorem B1010009 : Blo 794341 1010009 := bbase (se 2 (by rfl) ⟨378753, by rfl⟩ : syracuseStep 1010009 = 757507) (by norm_num)
theorem B1436005 : Blo 794341 1436005 := bbase (se 4 (by rfl) ⟨134625, by rfl⟩ : syracuseStep 1436005 = 269251) (by norm_num)
theorem B1010065 : Blo 794341 1010065 := bbase (se 2 (by rfl) ⟨378774, by rfl⟩ : syracuseStep 1010065 = 757549) (by norm_num)
theorem B2615765 : Blo 794341 2615765 := bbase (se 7 (by rfl) ⟨30653, by rfl⟩ : syracuseStep 2615765 = 61307) (by norm_num)
theorem B1010161 : Blo 794341 1010161 := bbase (se 2 (by rfl) ⟨378810, by rfl⟩ : syracuseStep 1010161 = 757621) (by norm_num)
theorem B2157077 : Blo 794341 2157077 := bbase (se 6 (by rfl) ⟨50556, by rfl⟩ : syracuseStep 2157077 = 101113) (by norm_num)
theorem B1436221 : Blo 794341 1436221 := bbase (se 3 (by rfl) ⟨269291, by rfl⟩ : syracuseStep 1436221 = 538583) (by norm_num)
theorem B2681477 : Blo 794341 2681477 := bbase (se 4 (by rfl) ⟨251388, by rfl⟩ : syracuseStep 2681477 = 502777) (by norm_num)
theorem B1698445 : Blo 794341 1698445 := bbase (se 3 (by rfl) ⟨318458, by rfl⟩ : syracuseStep 1698445 = 636917) (by norm_num)
theorem B1010333 : Blo 794341 1010333 := bbase (se 3 (by rfl) ⟨189437, by rfl⟩ : syracuseStep 1010333 = 378875) (by norm_num)
theorem B2550437 : Blo 794341 2550437 := bbase (se 4 (by rfl) ⟨239103, by rfl⟩ : syracuseStep 2550437 = 478207) (by norm_num)
theorem B1010389 : Blo 794341 1010389 := bbase (se 7 (by rfl) ⟨11840, by rfl⟩ : syracuseStep 1010389 = 23681) (by norm_num)
theorem B1698565 : Blo 794341 1698565 := bbase (se 4 (by rfl) ⟨159240, by rfl⟩ : syracuseStep 1698565 = 318481) (by norm_num)
theorem B1272629 : Blo 794341 1272629 := bbase (se 5 (by rfl) ⟨59654, by rfl⟩ : syracuseStep 1272629 = 119309) (by norm_num)
theorem B1272829 : Blo 794341 1272829 := bbase (se 3 (by rfl) ⟨238655, by rfl⟩ : syracuseStep 1272829 = 477311) (by norm_num)
theorem B1698821 : Blo 794341 1698821 := bbase (se 4 (by rfl) ⟨159264, by rfl⟩ : syracuseStep 1698821 = 318529) (by norm_num)
theorem B10185749 : Blo 794341 10185749 := bbase (se 6 (by rfl) ⟨238728, by rfl⟩ : syracuseStep 10185749 = 477457) (by norm_num)
theorem B2419733 : Blo 794341 2419733 := bbase (se 6 (by rfl) ⟨56712, by rfl⟩ : syracuseStep 2419733 = 113425) (by norm_num)
theorem B2681909 : Blo 794341 2681909 := bbase (se 5 (by rfl) ⟨125714, by rfl⟩ : syracuseStep 2681909 = 251429) (by norm_num)
theorem B945265 : Blo 794341 945265 := bbase (se 2 (by rfl) ⟨354474, by rfl⟩ : syracuseStep 945265 = 708949) (by norm_num)
theorem B1273085 : Blo 794341 1273085 := bbase (se 3 (by rfl) ⟨238703, by rfl⟩ : syracuseStep 1273085 = 477407) (by norm_num)
theorem B1076549 : Blo 794341 1076549 := bbase (se 4 (by rfl) ⟨100926, by rfl⟩ : syracuseStep 1076549 = 201853) (by norm_num)
theorem B3403093 : Blo 794341 3403093 := bbase (se 11 (by rfl) ⟨2492, by rfl⟩ : syracuseStep 3403093 = 4985) (by norm_num)
theorem B1437013 : Blo 794341 1437013 := bbase (se 11 (by rfl) ⟨1052, by rfl⟩ : syracuseStep 1437013 = 2105) (by norm_num)
theorem B3403109 : Blo 794341 3403109 := bbase (se 4 (by rfl) ⟨319041, by rfl⟩ : syracuseStep 3403109 = 638083) (by norm_num)
theorem B4091285 : Blo 794341 4091285 := bbase (se 6 (by rfl) ⟨95889, by rfl⟩ : syracuseStep 4091285 = 191779) (by norm_num)
theorem B2682341 : Blo 794341 2682341 := bbase (se 4 (by rfl) ⟨251469, by rfl⟩ : syracuseStep 2682341 = 502939) (by norm_num)
theorem B4025861 : Blo 794341 4025861 := bbase (se 4 (by rfl) ⟨377424, by rfl⟩ : syracuseStep 4025861 = 754849) (by norm_num)
theorem B2551333 : Blo 794341 2551333 := bbase (se 4 (by rfl) ⟨239187, by rfl⟩ : syracuseStep 2551333 = 478375) (by norm_num)
theorem B6123221 : Blo 794341 6123221 := bbase (se 7 (by rfl) ⟨71756, by rfl⟩ : syracuseStep 6123221 = 143513) (by norm_num)
theorem B25882325 : Blo 794341 25882325 := bbase (se 7 (by rfl) ⟨303308, by rfl⟩ : syracuseStep 25882325 = 606617) (by norm_num)
theorem B6647669 : Blo 794341 6647669 := bbase (se 5 (by rfl) ⟨311609, by rfl⟩ : syracuseStep 6647669 = 623219) (by norm_num)
theorem B1699709 : Blo 794341 1699709 := bbase (se 3 (by rfl) ⟨318695, by rfl⟩ : syracuseStep 1699709 = 637391) (by norm_num)
theorem B2682773 : Blo 794341 2682773 := bbase (se 6 (by rfl) ⟨62877, by rfl⟩ : syracuseStep 2682773 = 125755) (by norm_num)
theorem B5107637 : Blo 794341 5107637 := bbase (se 5 (by rfl) ⟨239420, by rfl⟩ : syracuseStep 5107637 = 478841) (by norm_num)
theorem B1437677 : Blo 794341 1437677 := bbase (se 3 (by rfl) ⟨269564, by rfl⟩ : syracuseStep 1437677 = 539129) (by norm_num)
theorem B1699949 : Blo 794341 1699949 := bbase (se 3 (by rfl) ⟨318740, by rfl⟩ : syracuseStep 1699949 = 637481) (by norm_num)
theorem B1437821 : Blo 794341 1437821 := bbase (se 3 (by rfl) ⟨269591, by rfl⟩ : syracuseStep 1437821 = 539183) (by norm_num)
theorem B2683205 : Blo 794341 2683205 := bbase (se 4 (by rfl) ⟨251550, by rfl⟩ : syracuseStep 2683205 = 503101) (by norm_num)
theorem B10875221 : Blo 794341 10875221 := bbase (se 10 (by rfl) ⟨15930, by rfl⟩ : syracuseStep 10875221 = 31861) (by norm_num)
theorem B1274213 : Blo 794341 1274213 := bbase (se 4 (by rfl) ⟨119457, by rfl⟩ : syracuseStep 1274213 = 238915) (by norm_num)
theorem B848317 : Blo 794341 848317 := bbase (se 3 (by rfl) ⟨159059, by rfl⟩ : syracuseStep 848317 = 318119) (by norm_num)
theorem B1700453 : Blo 794341 1700453 := bbase (se 4 (by rfl) ⟨159417, by rfl⟩ : syracuseStep 1700453 = 318835) (by norm_num)
theorem B1700461 : Blo 794341 1700461 := bbase (se 3 (by rfl) ⟨318836, by rfl⟩ : syracuseStep 1700461 = 637673) (by norm_num)
theorem B7664341 : Blo 794341 7664341 := bbase (se 7 (by rfl) ⟨89816, by rfl⟩ : syracuseStep 7664341 = 179633) (by norm_num)
theorem B2585317 : Blo 794341 2585317 := bbase (se 4 (by rfl) ⟨242373, by rfl⟩ : syracuseStep 2585317 = 484747) (by norm_num)
theorem B2683637 : Blo 794341 2683637 := bbase (se 5 (by rfl) ⟨125795, by rfl⟩ : syracuseStep 2683637 = 251591) (by norm_num)
theorem B4027157 : Blo 794341 4027157 := bbase (se 6 (by rfl) ⟨94386, by rfl⟩ : syracuseStep 4027157 = 188773) (by norm_num)
theorem B1274725 : Blo 794341 1274725 := bbase (se 4 (by rfl) ⟨119505, by rfl⟩ : syracuseStep 1274725 = 239011) (by norm_num)
theorem B848761 : Blo 794341 848761 := bbase (se 2 (by rfl) ⟨318285, by rfl⟩ : syracuseStep 848761 = 636571) (by norm_num)
theorem B848881 : Blo 794341 848881 := bbase (se 2 (by rfl) ⟨318330, by rfl⟩ : syracuseStep 848881 = 636661) (by norm_num)
theorem B816193 : Blo 794341 816193 := bbase (se 2 (by rfl) ⟨306072, by rfl⟩ : syracuseStep 816193 = 612145) (by norm_num)
theorem B9335893 : Blo 794341 9335893 := bbase (se 8 (by rfl) ⟨54702, by rfl⟩ : syracuseStep 9335893 = 109405) (by norm_num)
theorem B1340509 : Blo 794341 1340509 := bbase (se 3 (by rfl) ⟨251345, by rfl⟩ : syracuseStep 1340509 = 502691) (by norm_num)
theorem B4846709 : Blo 794341 4846709 := bbase (se 5 (by rfl) ⟨227189, by rfl⟩ : syracuseStep 4846709 = 454379) (by norm_num)
theorem B2684069 : Blo 794341 2684069 := bbase (se 4 (by rfl) ⟨251631, by rfl⟩ : syracuseStep 2684069 = 503263) (by norm_num)
theorem B1340597 : Blo 794341 1340597 := bbase (se 5 (by rfl) ⟨62840, by rfl⟩ : syracuseStep 1340597 = 125681) (by norm_num)
theorem B1635509 : Blo 794341 1635509 := bbase (se 5 (by rfl) ⟨76664, by rfl⟩ : syracuseStep 1635509 = 153329) (by norm_num)
theorem B849133 : Blo 794341 849133 := bbase (se 3 (by rfl) ⟨159212, by rfl⟩ : syracuseStep 849133 = 318425) (by norm_num)
theorem B849137 : Blo 794341 849137 := bbase (se 2 (by rfl) ⟨318426, by rfl⟩ : syracuseStep 849137 = 636853) (by norm_num)
theorem B1340725 : Blo 794341 1340725 := bbase (se 5 (by rfl) ⟨62846, by rfl⟩ : syracuseStep 1340725 = 125693) (by norm_num)
theorem B1275269 : Blo 794341 1275269 := bbase (se 4 (by rfl) ⟨119556, by rfl⟩ : syracuseStep 1275269 = 239113) (by norm_num)
theorem B1340813 : Blo 794341 1340813 := bbase (se 3 (by rfl) ⟨251402, by rfl⟩ : syracuseStep 1340813 = 502805) (by norm_num)
theorem B1340941 : Blo 794341 1340941 := bbase (se 3 (by rfl) ⟨251426, by rfl⟩ : syracuseStep 1340941 = 502853) (by norm_num)
theorem B8189461 : Blo 794341 8189461 := bbase (se 6 (by rfl) ⟨191940, by rfl⟩ : syracuseStep 8189461 = 383881) (by norm_num)
theorem B5174837 : Blo 794341 5174837 := bbase (se 5 (by rfl) ⟨242570, by rfl⟩ : syracuseStep 5174837 = 485141) (by norm_num)
theorem B3405365 : Blo 794341 3405365 := bbase (se 5 (by rfl) ⟨159626, by rfl⟩ : syracuseStep 3405365 = 319253) (by norm_num)
theorem B2684501 : Blo 794341 2684501 := bbase (se 8 (by rfl) ⟨15729, by rfl⟩ : syracuseStep 2684501 = 31459) (by norm_num)
theorem B1341029 : Blo 794341 1341029 := bbase (se 4 (by rfl) ⟨125721, by rfl⟩ : syracuseStep 1341029 = 251443) (by norm_num)
theorem B1701589 : Blo 794341 1701589 := bbase (se 7 (by rfl) ⟨19940, by rfl⟩ : syracuseStep 1701589 = 39881) (by norm_num)
theorem B1341157 : Blo 794341 1341157 := bbase (se 4 (by rfl) ⟨125733, by rfl⟩ : syracuseStep 1341157 = 251467) (by norm_num)
theorem B849701 : Blo 794341 849701 := bbase (se 4 (by rfl) ⟨79659, by rfl⟩ : syracuseStep 849701 = 159319) (by norm_num)
theorem B1341245 : Blo 794341 1341245 := bbase (se 3 (by rfl) ⟨251483, by rfl⟩ : syracuseStep 1341245 = 502967) (by norm_num)
theorem B12285845 : Blo 794341 12285845 := bbase (se 6 (by rfl) ⟨287949, by rfl⟩ : syracuseStep 12285845 = 575899) (by norm_num)
theorem B1275821 : Blo 794341 1275821 := bbase (se 3 (by rfl) ⟨239216, by rfl⟩ : syracuseStep 1275821 = 478433) (by norm_num)
theorem B1341373 : Blo 794341 1341373 := bbase (se 3 (by rfl) ⟨251507, by rfl⟩ : syracuseStep 1341373 = 503015) (by norm_num)
theorem B1275853 : Blo 794341 1275853 := bbase (se 3 (by rfl) ⟨239222, by rfl⟩ : syracuseStep 1275853 = 478445) (by norm_num)
theorem B849889 : Blo 794341 849889 := bbase (se 2 (by rfl) ⟨318708, by rfl⟩ : syracuseStep 849889 = 637417) (by norm_num)
theorem B2684933 : Blo 794341 2684933 := bbase (se 4 (by rfl) ⟨251712, by rfl⟩ : syracuseStep 2684933 = 503425) (by norm_num)
theorem B1341461 : Blo 794341 1341461 := bbase (se 6 (by rfl) ⟨31440, by rfl⟩ : syracuseStep 1341461 = 62881) (by norm_num)
theorem B4028453 : Blo 794341 4028453 := bbase (se 4 (by rfl) ⟨377667, by rfl⟩ : syracuseStep 4028453 = 755335) (by norm_num)
theorem B1701965 : Blo 794341 1701965 := bbase (se 3 (by rfl) ⟨319118, by rfl⟩ : syracuseStep 1701965 = 638237) (by norm_num)
theorem B1341589 : Blo 794341 1341589 := bbase (se 6 (by rfl) ⟨31443, by rfl⟩ : syracuseStep 1341589 = 62887) (by norm_num)
theorem B15497365 : Blo 794341 15497365 := bbase (se 6 (by rfl) ⟨363219, by rfl⟩ : syracuseStep 15497365 = 726439) (by norm_num)
theorem B1341677 : Blo 794341 1341677 := bbase (se 3 (by rfl) ⟨251564, by rfl⟩ : syracuseStep 1341677 = 503129) (by norm_num)
theorem B1210693 : Blo 794341 1210693 := bbase (se 4 (by rfl) ⟨113502, by rfl⟩ : syracuseStep 1210693 = 227005) (by norm_num)
theorem B1341805 : Blo 794341 1341805 := bbase (se 3 (by rfl) ⟨251588, by rfl⟩ : syracuseStep 1341805 = 503177) (by norm_num)
theorem B2554229 : Blo 794341 2554229 := bbase (se 5 (by rfl) ⟨119729, by rfl⟩ : syracuseStep 2554229 = 239459) (by norm_num)
theorem B2685365 : Blo 794341 2685365 := bbase (se 5 (by rfl) ⟨125876, by rfl⟩ : syracuseStep 2685365 = 251753) (by norm_num)
theorem B1341893 : Blo 794341 1341893 := bbase (se 4 (by rfl) ⟨125802, by rfl⟩ : syracuseStep 1341893 = 251605) (by norm_num)
theorem B2423333 : Blo 794341 2423333 := bbase (se 4 (by rfl) ⟨227187, by rfl⟩ : syracuseStep 2423333 = 454375) (by norm_num)
theorem B1342021 : Blo 794341 1342021 := bbase (se 4 (by rfl) ⟨125814, by rfl⟩ : syracuseStep 1342021 = 251629) (by norm_num)
theorem B1342109 : Blo 794341 1342109 := bbase (se 3 (by rfl) ⟨251645, by rfl⟩ : syracuseStep 1342109 = 503291) (by norm_num)
theorem B850709 : Blo 794341 850709 := bbase (se 6 (by rfl) ⟨19938, by rfl⟩ : syracuseStep 850709 = 39877) (by norm_num)
theorem B1342237 : Blo 794341 1342237 := bbase (se 3 (by rfl) ⟨251669, by rfl⟩ : syracuseStep 1342237 = 503339) (by norm_num)
theorem B2685797 : Blo 794341 2685797 := bbase (se 4 (by rfl) ⟨251793, by rfl⟩ : syracuseStep 2685797 = 503587) (by norm_num)
theorem B1276781 : Blo 794341 1276781 := bbase (se 3 (by rfl) ⟨239396, by rfl⟩ : syracuseStep 1276781 = 478793) (by norm_num)
theorem B1342325 : Blo 794341 1342325 := bbase (se 5 (by rfl) ⟨62921, by rfl⟩ : syracuseStep 1342325 = 125843) (by norm_num)
theorem B1342453 : Blo 794341 1342453 := bbase (se 5 (by rfl) ⟨62927, by rfl⟩ : syracuseStep 1342453 = 125855) (by norm_num)
theorem B1342541 : Blo 794341 1342541 := bbase (se 3 (by rfl) ⟨251726, by rfl⟩ : syracuseStep 1342541 = 503453) (by norm_num)
theorem B1342669 : Blo 794341 1342669 := bbase (se 3 (by rfl) ⟨251750, by rfl⟩ : syracuseStep 1342669 = 503501) (by norm_num)
theorem B851153 : Blo 794341 851153 := bbase (se 2 (by rfl) ⟨319182, by rfl⟩ : syracuseStep 851153 = 638365) (by norm_num)
theorem B2686229 : Blo 794341 2686229 := bbase (se 6 (by rfl) ⟨62958, by rfl⟩ : syracuseStep 2686229 = 125917) (by norm_num)
theorem B1342757 : Blo 794341 1342757 := bbase (se 4 (by rfl) ⟨125883, by rfl⟩ : syracuseStep 1342757 = 251767) (by norm_num)
theorem B4029749 : Blo 794341 4029749 := bbase (se 5 (by rfl) ⟨188894, by rfl⟩ : syracuseStep 4029749 = 377789) (by norm_num)
theorem B5242165 : Blo 794341 5242165 := bbase (se 5 (by rfl) ⟨245726, by rfl⟩ : syracuseStep 5242165 = 491453) (by norm_num)
theorem B3833189 : Blo 794341 3833189 := bbase (se 4 (by rfl) ⟨359361, by rfl⟩ : syracuseStep 3833189 = 718723) (by norm_num)
theorem B10911125 : Blo 794341 10911125 := bbase (se 6 (by rfl) ⟨255729, by rfl⟩ : syracuseStep 10911125 = 511459) (by norm_num)
theorem B1342885 : Blo 794341 1342885 := bbase (se 4 (by rfl) ⟨125895, by rfl⟩ : syracuseStep 1342885 = 251791) (by norm_num)
theorem B851401 : Blo 794341 851401 := bbase (se 2 (by rfl) ⟨319275, by rfl⟩ : syracuseStep 851401 = 638551) (by norm_num)
theorem B4849141 : Blo 794341 4849141 := bbase (se 5 (by rfl) ⟨227303, by rfl⟩ : syracuseStep 4849141 = 454607) (by norm_num)
theorem B1342973 : Blo 794341 1342973 := bbase (se 3 (by rfl) ⟨251807, by rfl⟩ : syracuseStep 1342973 = 503615) (by norm_num)
theorem B1277461 : Blo 794341 1277461 := bbase (se 6 (by rfl) ⟨29940, by rfl⟩ : syracuseStep 1277461 = 59881) (by norm_num)
theorem B1277525 : Blo 794341 1277525 := bbase (se 8 (by rfl) ⟨7485, by rfl⟩ : syracuseStep 1277525 = 14971) (by norm_num)
theorem B1343101 : Blo 794341 1343101 := bbase (se 3 (by rfl) ⟨251831, by rfl⟩ : syracuseStep 1343101 = 503663) (by norm_num)
theorem B1703605 : Blo 794341 1703605 := bbase (se 5 (by rfl) ⟨79856, by rfl⟩ : syracuseStep 1703605 = 159713) (by norm_num)
theorem B2686661 : Blo 794341 2686661 := bbase (se 4 (by rfl) ⟨251874, by rfl⟩ : syracuseStep 2686661 = 503749) (by norm_num)
theorem B1343189 : Blo 794341 1343189 := bbase (se 7 (by rfl) ⟨15740, by rfl⟩ : syracuseStep 1343189 = 31481) (by norm_num)
theorem B6061877 : Blo 794341 6061877 := bbase (se 5 (by rfl) ⟨284150, by rfl⟩ : syracuseStep 6061877 = 568301) (by norm_num)
theorem B1343317 : Blo 794341 1343317 := bbase (se 9 (by rfl) ⟨3935, by rfl⟩ : syracuseStep 1343317 = 7871) (by norm_num)
theorem B6225749 : Blo 794341 6225749 := bbase (se 9 (by rfl) ⟨18239, by rfl⟩ : syracuseStep 6225749 = 36479) (by norm_num)
theorem B851833 : Blo 794341 851833 := bbase (se 2 (by rfl) ⟨319437, by rfl⟩ : syracuseStep 851833 = 638875) (by norm_num)
theorem B1343405 : Blo 794341 1343405 := bbase (se 3 (by rfl) ⟨251888, by rfl⟩ : syracuseStep 1343405 = 503777) (by norm_num)
theorem B851905 : Blo 794341 851905 := bbase (se 2 (by rfl) ⟨319464, by rfl⟩ : syracuseStep 851905 = 638929) (by norm_num)
theorem B3440675 : Blo 794341 3440675 := bstep (se 1 (by rfl) ⟨2580506, by rfl⟩ : syracuseStep 3440675 = 5161013) B5161013
theorem B1146979 : Blo 794341 1146979 := bstep (se 1 (by rfl) ⟨860234, by rfl⟩ : syracuseStep 1146979 = 1720469) B1720469
theorem B1343587 : Blo 794341 1343587 := bstep (se 1 (by rfl) ⟨1007690, by rfl⟩ : syracuseStep 1343587 = 2015381) B2015381
theorem B2556049 : Blo 794341 2556049 := bstep (se 2 (by rfl) ⟨958518, by rfl⟩ : syracuseStep 2556049 = 1917037) B1917037
theorem B1343729 : Blo 794341 1343729 := bstep (se 2 (by rfl) ⟨503898, by rfl⟩ : syracuseStep 1343729 = 1007797) B1007797
theorem B1212737 : Blo 794341 1212737 := bstep (se 2 (by rfl) ⟨454776, by rfl⟩ : syracuseStep 1212737 = 909553) B909553
theorem B2687309 : Blo 794341 2687309 := bstep (se 3 (by rfl) ⟨503870, by rfl⟩ : syracuseStep 2687309 = 1007741) B1007741
theorem B2130275 : Blo 794341 2130275 := bstep (se 1 (by rfl) ⟨1597706, by rfl⟩ : syracuseStep 2130275 = 3195413) B3195413
theorem B7668067 : Blo 794341 7668067 := bstep (se 1 (by rfl) ⟨5751050, by rfl⟩ : syracuseStep 7668067 = 11502101) B11502101
theorem B1343857 : Blo 794341 1343857 := bstep (se 2 (by rfl) ⟨503946, by rfl⟩ : syracuseStep 1343857 = 1007893) B1007893
theorem B2687363 : Blo 794341 2687363 := bstep (se 1 (by rfl) ⟨2015522, by rfl⟩ : syracuseStep 2687363 = 4031045) B4031045
theorem B1704323 : Blo 794341 1704323 := bstep (se 1 (by rfl) ⟨1278242, by rfl⟩ : syracuseStep 1704323 = 2556485) B2556485
theorem B1343891 : Blo 794341 1343891 := bstep (se 1 (by rfl) ⟨1007918, by rfl⟩ : syracuseStep 1343891 = 2015837) B2015837
theorem B4030883 : Blo 794341 4030883 := bstep (se 1 (by rfl) ⟨3023162, by rfl⟩ : syracuseStep 4030883 = 6046325) B6046325
theorem B1344019 : Blo 794341 1344019 := bstep (se 1 (by rfl) ⟨1008014, by rfl⟩ : syracuseStep 1344019 = 2016029) B2016029
theorem B1278499 : Blo 794341 1278499 := bstep (se 1 (by rfl) ⟨958874, by rfl⟩ : syracuseStep 1278499 = 1917749) B1917749
theorem B2687633 : Blo 794341 2687633 := bstep (se 2 (by rfl) ⟨1007862, by rfl⟩ : syracuseStep 2687633 = 2015725) B2015725
theorem B1344161 : Blo 794341 1344161 := bstep (se 2 (by rfl) ⟨504060, by rfl⟩ : syracuseStep 1344161 = 1008121) B1008121
theorem B1344289 : Blo 794341 1344289 := bstep (se 2 (by rfl) ⟨504108, by rfl⟩ : syracuseStep 1344289 = 1008217) B1008217
theorem B1278755 : Blo 794341 1278755 := bstep (se 1 (by rfl) ⟨959066, by rfl⟩ : syracuseStep 1278755 = 1918133) B1918133
theorem B17204021 : Blo 794341 17204021 := bstep (se 5 (by rfl) ⟨806438, by rfl⟩ : syracuseStep 17204021 = 1612877) B1612877
theorem B1344323 : Blo 794341 1344323 := bstep (se 1 (by rfl) ⟨1008242, by rfl⟩ : syracuseStep 1344323 = 2016485) B2016485
theorem B1508195 : Blo 794341 1508195 := bstep (se 1 (by rfl) ⟨1131146, by rfl⟩ : syracuseStep 1508195 = 2262293) B2262293
theorem B1704835 : Blo 794341 1704835 := bstep (se 1 (by rfl) ⟨1278626, by rfl⟩ : syracuseStep 1704835 = 2557253) B2557253
theorem B1344451 : Blo 794341 1344451 := bstep (se 1 (by rfl) ⟨1008338, by rfl⟩ : syracuseStep 1344451 = 2016677) B2016677
theorem B2262019 : Blo 794341 2262019 := bstep (se 1 (by rfl) ⟨1696514, by rfl⟩ : syracuseStep 2262019 = 3393029) B3393029
theorem B1344593 : Blo 794341 1344593 := bstep (se 2 (by rfl) ⟨504222, by rfl⟩ : syracuseStep 1344593 = 1008445) B1008445
theorem B1508483 : Blo 794341 1508483 := bstep (se 1 (by rfl) ⟨1131362, by rfl⟩ : syracuseStep 1508483 = 2262725) B2262725
theorem B2688173 : Blo 794341 2688173 := bstep (se 3 (by rfl) ⟨504032, by rfl⟩ : syracuseStep 2688173 = 1008065) B1008065
theorem B4031693 : Blo 794341 4031693 := bstep (se 3 (by rfl) ⟨755942, by rfl⟩ : syracuseStep 4031693 = 1511885) B1511885
theorem B1344721 : Blo 794341 1344721 := bstep (se 2 (by rfl) ⟨504270, by rfl⟩ : syracuseStep 1344721 = 1008541) B1008541
theorem B2688227 : Blo 794341 2688227 := bstep (se 1 (by rfl) ⟨2016170, by rfl⟩ : syracuseStep 2688227 = 4032341) B4032341
theorem B3409123 : Blo 794341 3409123 := bstep (se 1 (by rfl) ⟨2556842, by rfl⟩ : syracuseStep 3409123 = 5113685) B5113685
theorem B1344755 : Blo 794341 1344755 := bstep (se 1 (by rfl) ⟨1008566, by rfl⟩ : syracuseStep 1344755 = 2017133) B2017133
theorem B2458925 : Blo 794341 2458925 := bstep (se 3 (by rfl) ⟨461048, by rfl⟩ : syracuseStep 2458925 = 922097) B922097
theorem B8848739 : Blo 794341 8848739 := bstep (se 1 (by rfl) ⟨6636554, by rfl⟩ : syracuseStep 8848739 = 13273109) B13273109
theorem B1344883 : Blo 794341 1344883 := bstep (se 1 (by rfl) ⟨1008662, by rfl⟩ : syracuseStep 1344883 = 2017325) B2017325
theorem B1148323 : Blo 794341 1148323 := bstep (se 1 (by rfl) ⟨861242, by rfl⟩ : syracuseStep 1148323 = 1722485) B1722485
theorem B2688497 : Blo 794341 2688497 := bstep (se 2 (by rfl) ⟨1008186, by rfl⟩ : syracuseStep 2688497 = 2016373) B2016373
theorem B1345025 : Blo 794341 1345025 := bstep (se 2 (by rfl) ⟨504384, by rfl⟩ : syracuseStep 1345025 = 1008769) B1008769
theorem B1345153 : Blo 794341 1345153 := bstep (se 2 (by rfl) ⟨504432, by rfl⟩ : syracuseStep 1345153 = 1008865) B1008865
theorem B1345187 : Blo 794341 1345187 := bstep (se 1 (by rfl) ⟨1008890, by rfl⟩ : syracuseStep 1345187 = 2017781) B2017781
theorem B984803 : Blo 794341 984803 := bstep (se 1 (by rfl) ⟨738602, by rfl⟩ : syracuseStep 984803 = 1477205) B1477205
theorem B1345315 : Blo 794341 1345315 := bstep (se 1 (by rfl) ⟨1008986, by rfl⟩ : syracuseStep 1345315 = 2017973) B2017973
theorem B11470733 : Blo 794341 11470733 := bstep (se 3 (by rfl) ⟨2150762, by rfl⟩ : syracuseStep 11470733 = 4301525) B4301525
theorem B1345457 : Blo 794341 1345457 := bstep (se 2 (by rfl) ⟨504546, by rfl⟩ : syracuseStep 1345457 = 1009093) B1009093
theorem B2656205 : Blo 794341 2656205 := bstep (se 3 (by rfl) ⟨498038, by rfl⟩ : syracuseStep 2656205 = 996077) B996077
theorem B2689037 : Blo 794341 2689037 := bstep (se 3 (by rfl) ⟨504194, by rfl⟩ : syracuseStep 2689037 = 1008389) B1008389
theorem B1509425 : Blo 794341 1509425 := bstep (se 2 (by rfl) ⟨566034, by rfl⟩ : syracuseStep 1509425 = 1132069) B1132069
theorem B1345585 : Blo 794341 1345585 := bstep (se 2 (by rfl) ⟨504594, by rfl⟩ : syracuseStep 1345585 = 1009189) B1009189
theorem B2689091 : Blo 794341 2689091 := bstep (se 1 (by rfl) ⟨2016818, by rfl⟩ : syracuseStep 2689091 = 4033637) B4033637
theorem B1345619 : Blo 794341 1345619 := bstep (se 1 (by rfl) ⟨1009214, by rfl⟩ : syracuseStep 1345619 = 2018429) B2018429
theorem B26151025 : Blo 794341 26151025 := bstep (se 2 (by rfl) ⟨9806634, by rfl⟩ : syracuseStep 26151025 = 19613269) B19613269
theorem B9078965 : Blo 794341 9078965 := bstep (se 5 (by rfl) ⟨425576, by rfl⟩ : syracuseStep 9078965 = 851153) B851153
theorem B1345747 : Blo 794341 1345747 := bstep (se 1 (by rfl) ⟨1009310, by rfl⟩ : syracuseStep 1345747 = 2018621) B2018621
theorem B2689361 : Blo 794341 2689361 := bstep (se 2 (by rfl) ⟨1008510, by rfl⟩ : syracuseStep 2689361 = 2017021) B2017021
theorem B1345889 : Blo 794341 1345889 := bstep (se 2 (by rfl) ⟨504708, by rfl⟩ : syracuseStep 1345889 = 1009417) B1009417
theorem B2263409 : Blo 794341 2263409 := bstep (se 2 (by rfl) ⟨848778, by rfl⟩ : syracuseStep 2263409 = 1697557) B1697557
theorem B1346017 : Blo 794341 1346017 := bstep (se 2 (by rfl) ⟨504756, by rfl⟩ : syracuseStep 1346017 = 1009513) B1009513
theorem B1346051 : Blo 794341 1346051 := bstep (se 1 (by rfl) ⟨1009538, by rfl⟩ : syracuseStep 1346051 = 2019077) B2019077
theorem B1346179 : Blo 794341 1346179 := bstep (se 1 (by rfl) ⟨1009634, by rfl⟩ : syracuseStep 1346179 = 2019269) B2019269
theorem B5114609 : Blo 794341 5114609 := bstep (se 2 (by rfl) ⟨1917978, by rfl⟩ : syracuseStep 5114609 = 3835957) B3835957
theorem B1346321 : Blo 794341 1346321 := bstep (se 2 (by rfl) ⟨504870, by rfl⟩ : syracuseStep 1346321 = 1009741) B1009741
theorem B2689901 : Blo 794341 2689901 := bstep (se 3 (by rfl) ⟨504356, by rfl⟩ : syracuseStep 2689901 = 1008713) B1008713
theorem B1346449 : Blo 794341 1346449 := bstep (se 2 (by rfl) ⟨504918, by rfl⟩ : syracuseStep 1346449 = 1009837) B1009837
theorem B2689955 : Blo 794341 2689955 := bstep (se 1 (by rfl) ⟨2017466, by rfl⟩ : syracuseStep 2689955 = 4034933) B4034933
theorem B1510321 : Blo 794341 1510321 := bstep (se 2 (by rfl) ⟨566370, by rfl⟩ : syracuseStep 1510321 = 1132741) B1132741
theorem B1346483 : Blo 794341 1346483 := bstep (se 1 (by rfl) ⟨1009862, by rfl⟩ : syracuseStep 1346483 = 2019725) B2019725
theorem B1346611 : Blo 794341 1346611 := bstep (se 1 (by rfl) ⟨1009958, by rfl⟩ : syracuseStep 1346611 = 2019917) B2019917
theorem B1510481 : Blo 794341 1510481 := bstep (se 2 (by rfl) ⟨566430, by rfl⟩ : syracuseStep 1510481 = 1132861) B1132861
theorem B4361357 : Blo 794341 4361357 := bstep (se 3 (by rfl) ⟨817754, by rfl⟩ : syracuseStep 4361357 = 1635509) B1635509
theorem B2690225 : Blo 794341 2690225 := bstep (se 2 (by rfl) ⟨1008834, by rfl⟩ : syracuseStep 2690225 = 2017669) B2017669
theorem B1346753 : Blo 794341 1346753 := bstep (se 2 (by rfl) ⟨505032, by rfl⟩ : syracuseStep 1346753 = 1010065) B1010065
theorem B3017969 : Blo 794341 3017969 := bstep (se 2 (by rfl) ⟨1131738, by rfl⟩ : syracuseStep 3017969 = 2263477) B2263477
theorem B2264365 : Blo 794341 2264365 := bstep (se 3 (by rfl) ⟨424568, by rfl⟩ : syracuseStep 2264365 = 849137) B849137
theorem B1346881 : Blo 794341 1346881 := bstep (se 2 (by rfl) ⟨505080, by rfl⟩ : syracuseStep 1346881 = 1010161) B1010161
theorem B1346915 : Blo 794341 1346915 := bstep (se 1 (by rfl) ⟨1010186, by rfl⟩ : syracuseStep 1346915 = 2020373) B2020373
theorem B1510883 : Blo 794341 1510883 := bstep (se 1 (by rfl) ⟨1133162, by rfl⟩ : syracuseStep 1510883 = 2266325) B2266325
theorem B1347043 : Blo 794341 1347043 := bstep (se 1 (by rfl) ⟨1010282, by rfl⟩ : syracuseStep 1347043 = 2020565) B2020565
theorem B2264593 : Blo 794341 2264593 := bstep (se 2 (by rfl) ⟨849222, by rfl⟩ : syracuseStep 2264593 = 1698445) B1698445
theorem B1347185 : Blo 794341 1347185 := bstep (se 2 (by rfl) ⟨505194, by rfl⟩ : syracuseStep 1347185 = 1010389) B1010389
theorem B2264753 : Blo 794341 2264753 := bstep (se 2 (by rfl) ⟨849282, by rfl⟩ : syracuseStep 2264753 = 1698565) B1698565
theorem B2690765 : Blo 794341 2690765 := bstep (se 3 (by rfl) ⟨504518, by rfl⟩ : syracuseStep 2690765 = 1009037) B1009037
theorem B2690819 : Blo 794341 2690819 := bstep (se 1 (by rfl) ⟨2018114, by rfl⟩ : syracuseStep 2690819 = 4036229) B4036229
theorem B2264867 : Blo 794341 2264867 := bstep (se 1 (by rfl) ⟨1698650, by rfl⟩ : syracuseStep 2264867 = 3397301) B3397301
theorem B8589169 : Blo 794341 8589169 := bstep (se 2 (by rfl) ⟨3220938, by rfl⟩ : syracuseStep 8589169 = 6441877) B6441877
theorem B2691089 : Blo 794341 2691089 := bstep (se 2 (by rfl) ⟨1009158, by rfl⟩ : syracuseStep 2691089 = 2018317) B2018317
theorem B4034609 : Blo 794341 4034609 := bstep (se 2 (by rfl) ⟨1512978, by rfl⟩ : syracuseStep 4034609 = 3025957) B3025957
theorem B1511779 : Blo 794341 1511779 := bstep (se 1 (by rfl) ⟨1133834, by rfl⟩ : syracuseStep 1511779 = 2267669) B2267669
theorem B1511939 : Blo 794341 1511939 := bstep (se 1 (by rfl) ⟨1133954, by rfl⟩ : syracuseStep 1511939 = 2267909) B2267909
theorem B2691629 : Blo 794341 2691629 := bstep (se 3 (by rfl) ⟨504680, by rfl⟩ : syracuseStep 2691629 = 1009361) B1009361
theorem B2691683 : Blo 794341 2691683 := bstep (se 1 (by rfl) ⟨2018762, by rfl⟩ : syracuseStep 2691683 = 4037525) B4037525
theorem B4526725 : Blo 794341 4526725 := bstep (se 4 (by rfl) ⟨424380, by rfl⟩ : syracuseStep 4526725 = 848761) B848761
theorem B3019427 : Blo 794341 3019427 := bstep (se 1 (by rfl) ⟨2264570, by rfl⟩ : syracuseStep 3019427 = 4529141) B4529141
theorem B8622773 : Blo 794341 8622773 := bstep (se 5 (by rfl) ⟨404192, by rfl⟩ : syracuseStep 8622773 = 808385) B808385
theorem B2265869 : Blo 794341 2265869 := bstep (se 3 (by rfl) ⟨424850, by rfl⟩ : syracuseStep 2265869 = 849701) B849701
theorem B2691953 : Blo 794341 2691953 := bstep (se 2 (by rfl) ⟨1009482, by rfl⟩ : syracuseStep 2691953 = 2018965) B2018965
theorem B2266051 : Blo 794341 2266051 := bstep (se 1 (by rfl) ⟨1699538, by rfl⟩ : syracuseStep 2266051 = 3399077) B3399077
theorem B2266211 : Blo 794341 2266211 := bstep (se 1 (by rfl) ⟨1699658, by rfl⟩ : syracuseStep 2266211 = 3399317) B3399317
theorem B2692493 : Blo 794341 2692493 := bstep (se 3 (by rfl) ⟨504842, by rfl⟩ : syracuseStep 2692493 = 1009685) B1009685
theorem B2692547 : Blo 794341 2692547 := bstep (se 1 (by rfl) ⟨2019410, by rfl⟩ : syracuseStep 2692547 = 4038821) B4038821
theorem B4036067 : Blo 794341 4036067 := bstep (se 1 (by rfl) ⟨3027050, by rfl⟩ : syracuseStep 4036067 = 6054101) B6054101
theorem B1513009 : Blo 794341 1513009 := bstep (se 2 (by rfl) ⟨567378, by rfl⟩ : syracuseStep 1513009 = 1134757) B1134757
theorem B3020429 : Blo 794341 3020429 := bstep (se 3 (by rfl) ⟨566330, by rfl⟩ : syracuseStep 3020429 = 1132661) B1132661
theorem B2692817 : Blo 794341 2692817 := bstep (se 2 (by rfl) ⟨1009806, by rfl⟩ : syracuseStep 2692817 = 2019613) B2019613
theorem B2267281 : Blo 794341 2267281 := bstep (se 2 (by rfl) ⟨850230, by rfl⟩ : syracuseStep 2267281 = 1700461) B1700461
theorem B2693357 : Blo 794341 2693357 := bstep (se 3 (by rfl) ⟨505004, by rfl⟩ : syracuseStep 2693357 = 1010009) B1010009
theorem B956659 : Blo 794341 956659 := bstep (se 1 (by rfl) ⟨717494, by rfl⟩ : syracuseStep 956659 = 1434989) B1434989
theorem B4036877 : Blo 794341 4036877 := bstep (se 3 (by rfl) ⟨756914, by rfl⟩ : syracuseStep 4036877 = 1513829) B1513829
theorem B4921613 : Blo 794341 4921613 := bstep (se 3 (by rfl) ⟨922802, by rfl⟩ : syracuseStep 4921613 = 1845605) B1845605
theorem B1612067 : Blo 794341 1612067 := bstep (se 1 (by rfl) ⟨1209050, by rfl⟩ : syracuseStep 1612067 = 2418101) B2418101
theorem B2693411 : Blo 794341 2693411 := bstep (se 1 (by rfl) ⟨2020058, by rfl⟩ : syracuseStep 2693411 = 4040117) B4040117
theorem B3447089 : Blo 794341 3447089 := bstep (se 2 (by rfl) ⟨1292658, by rfl⟩ : syracuseStep 3447089 = 2585317) B2585317
theorem B2693681 : Blo 794341 2693681 := bstep (se 2 (by rfl) ⟨1010130, by rfl⟩ : syracuseStep 2693681 = 2020261) B2020261
theorem B4528709 : Blo 794341 4528709 := bstep (se 4 (by rfl) ⟨424566, by rfl⟩ : syracuseStep 4528709 = 849133) B849133
theorem B1514065 : Blo 794341 1514065 := bstep (se 2 (by rfl) ⟨567774, by rfl⟩ : syracuseStep 1514065 = 1135549) B1135549
theorem B1088257 : Blo 794341 1088257 := bstep (se 2 (by rfl) ⟨408096, by rfl⟩ : syracuseStep 1088257 = 816193) B816193
theorem B5184269 : Blo 794341 5184269 := bstep (se 3 (by rfl) ⟨972050, by rfl⟩ : syracuseStep 5184269 = 1944101) B1944101
theorem B27958213 : Blo 794341 27958213 := bstep (se 4 (by rfl) ⟨2621082, by rfl⟩ : syracuseStep 27958213 = 5242165) B5242165
theorem B4594637 : Blo 794341 4594637 := bstep (se 3 (by rfl) ⟨861494, by rfl⟩ : syracuseStep 4594637 = 1722989) B1722989
theorem B1514467 : Blo 794341 1514467 := bstep (se 1 (by rfl) ⟨1135850, by rfl⟩ : syracuseStep 1514467 = 2271701) B2271701
theorem B1514513 : Blo 794341 1514513 := bstep (se 2 (by rfl) ⟨567942, by rfl⟩ : syracuseStep 1514513 = 1135885) B1135885
theorem B2694221 : Blo 794341 2694221 := bstep (se 3 (by rfl) ⟨505166, by rfl⟩ : syracuseStep 2694221 = 1010333) B1010333
theorem B2694275 : Blo 794341 2694275 := bstep (se 1 (by rfl) ⟨2020706, by rfl⟩ : syracuseStep 2694275 = 4041413) B4041413
theorem B1514801 : Blo 794341 1514801 := bstep (se 2 (by rfl) ⟨568050, by rfl⟩ : syracuseStep 1514801 = 1136101) B1136101
theorem B6790499 : Blo 794341 6790499 := bstep (se 1 (by rfl) ⟨5092874, by rfl⟩ : syracuseStep 6790499 = 10185749) B10185749
theorem B10919281 : Blo 794341 10919281 := bstep (se 2 (by rfl) ⟨4094730, by rfl⟩ : syracuseStep 10919281 = 8189461) B8189461
theorem B2268557 : Blo 794341 2268557 := bstep (se 3 (by rfl) ⟨425354, by rfl⟩ : syracuseStep 2268557 = 850709) B850709
theorem B2039267 : Blo 794341 2039267 := bstep (se 1 (by rfl) ⟨1529450, by rfl⟩ : syracuseStep 2039267 = 3058901) B3058901
theorem B2268739 : Blo 794341 2268739 := bstep (se 1 (by rfl) ⟨1701554, by rfl⟩ : syracuseStep 2268739 = 3403109) B3403109
theorem B6037091 : Blo 794341 6037091 := bstep (se 1 (by rfl) ⟨4527818, by rfl⟩ : syracuseStep 6037091 = 9055637) B9055637
theorem B2727523 : Blo 794341 2727523 := bstep (se 1 (by rfl) ⟨2045642, by rfl⟩ : syracuseStep 2727523 = 4091285) B4091285
theorem B2268785 : Blo 794341 2268785 := bstep (se 2 (by rfl) ⟨850794, by rfl⟩ : syracuseStep 2268785 = 1701589) B1701589
theorem B2301635 : Blo 794341 2301635 := bstep (se 1 (by rfl) ⟨1726226, by rfl⟩ : syracuseStep 2301635 = 3452453) B3452453
theorem B3022541 : Blo 794341 3022541 := bstep (se 3 (by rfl) ⟨566726, by rfl⟩ : syracuseStep 3022541 = 1133453) B1133453
theorem B794355 : Blo 794341 794355 := bstep (se 1 (by rfl) ⟨595766, by rfl⟩ : syracuseStep 794355 = 1191533) B1191533
theorem B794371 : Blo 794341 794371 := bstep (se 1 (by rfl) ⟨595778, by rfl⟩ : syracuseStep 794371 = 1191557) B1191557
theorem B794387 : Blo 794341 794387 := bstep (se 1 (by rfl) ⟨595790, by rfl⟩ : syracuseStep 794387 = 1191581) B1191581
theorem B794403 : Blo 794341 794403 := bstep (se 1 (by rfl) ⟨595802, by rfl⟩ : syracuseStep 794403 = 1191605) B1191605
theorem B794419 : Blo 794341 794419 := bstep (se 1 (by rfl) ⟨595814, by rfl⟩ : syracuseStep 794419 = 1191629) B1191629
theorem B8625973 : Blo 794341 8625973 := bstep (se 5 (by rfl) ⟨404342, by rfl⟩ : syracuseStep 8625973 = 808685) B808685
theorem B794435 : Blo 794341 794435 := bstep (se 1 (by rfl) ⟨595826, by rfl⟩ : syracuseStep 794435 = 1191653) B1191653
theorem B794451 : Blo 794341 794451 := bstep (se 1 (by rfl) ⟨595838, by rfl⟩ : syracuseStep 794451 = 1191677) B1191677
theorem B794467 : Blo 794341 794467 := bstep (se 1 (by rfl) ⟨595850, by rfl⟩ : syracuseStep 794467 = 1191701) B1191701
theorem B794483 : Blo 794341 794483 := bstep (se 1 (by rfl) ⟨595862, by rfl⟩ : syracuseStep 794483 = 1191725) B1191725
theorem B794499 : Blo 794341 794499 := bstep (se 1 (by rfl) ⟨595874, by rfl⟩ : syracuseStep 794499 = 1191749) B1191749
theorem B794515 : Blo 794341 794515 := bstep (se 1 (by rfl) ⟨595886, by rfl⟩ : syracuseStep 794515 = 1191773) B1191773
theorem B794531 : Blo 794341 794531 := bstep (se 1 (by rfl) ⟨595898, by rfl⟩ : syracuseStep 794531 = 1191797) B1191797
theorem B4431779 : Blo 794341 4431779 := bstep (se 1 (by rfl) ⟨3323834, by rfl⟩ : syracuseStep 4431779 = 6647669) B6647669
theorem B794547 : Blo 794341 794547 := bstep (se 1 (by rfl) ⟨595910, by rfl⟩ : syracuseStep 794547 = 1191821) B1191821
theorem B794563 : Blo 794341 794563 := bstep (se 1 (by rfl) ⟨595922, by rfl⟩ : syracuseStep 794563 = 1191845) B1191845
theorem B794579 : Blo 794341 794579 := bstep (se 1 (by rfl) ⟨595934, by rfl⟩ : syracuseStep 794579 = 1191869) B1191869
theorem B794595 : Blo 794341 794595 := bstep (se 1 (by rfl) ⟨595946, by rfl⟩ : syracuseStep 794595 = 1191893) B1191893
theorem B794611 : Blo 794341 794611 := bstep (se 1 (by rfl) ⟨595958, by rfl⟩ : syracuseStep 794611 = 1191917) B1191917
theorem B958451 : Blo 794341 958451 := bstep (se 1 (by rfl) ⟨718838, by rfl⟩ : syracuseStep 958451 = 1437677) B1437677
theorem B794627 : Blo 794341 794627 := bstep (se 1 (by rfl) ⟨595970, by rfl⟩ : syracuseStep 794627 = 1191941) B1191941
theorem B1515523 : Blo 794341 1515523 := bstep (se 1 (by rfl) ⟨1136642, by rfl⟩ : syracuseStep 1515523 = 2273285) B2273285
theorem B794643 : Blo 794341 794643 := bstep (se 1 (by rfl) ⟨595982, by rfl⟩ : syracuseStep 794643 = 1191965) B1191965
theorem B794659 : Blo 794341 794659 := bstep (se 1 (by rfl) ⟨595994, by rfl⟩ : syracuseStep 794659 = 1191989) B1191989
theorem B794675 : Blo 794341 794675 := bstep (se 1 (by rfl) ⟨596006, by rfl⟩ : syracuseStep 794675 = 1192013) B1192013
theorem B794691 : Blo 794341 794691 := bstep (se 1 (by rfl) ⟨596018, by rfl⟩ : syracuseStep 794691 = 1192037) B1192037
theorem B794707 : Blo 794341 794707 := bstep (se 1 (by rfl) ⟨596030, by rfl⟩ : syracuseStep 794707 = 1192061) B1192061
theorem B958547 : Blo 794341 958547 := bstep (se 1 (by rfl) ⟨718910, by rfl⟩ : syracuseStep 958547 = 1437821) B1437821
theorem B794723 : Blo 794341 794723 := bstep (se 1 (by rfl) ⟨596042, by rfl⟩ : syracuseStep 794723 = 1192085) B1192085
theorem B794739 : Blo 794341 794739 := bstep (se 1 (by rfl) ⟨596054, by rfl⟩ : syracuseStep 794739 = 1192109) B1192109
theorem B794755 : Blo 794341 794755 := bstep (se 1 (by rfl) ⟨596066, by rfl⟩ : syracuseStep 794755 = 1192133) B1192133
theorem B794771 : Blo 794341 794771 := bstep (se 1 (by rfl) ⟨596078, by rfl⟩ : syracuseStep 794771 = 1192157) B1192157
theorem B794787 : Blo 794341 794787 := bstep (se 1 (by rfl) ⟨596090, by rfl⟩ : syracuseStep 794787 = 1192181) B1192181
theorem B794803 : Blo 794341 794803 := bstep (se 1 (by rfl) ⟨596102, by rfl⟩ : syracuseStep 794803 = 1192205) B1192205
theorem B794819 : Blo 794341 794819 := bstep (se 1 (by rfl) ⟨596114, by rfl⟩ : syracuseStep 794819 = 1192229) B1192229
theorem B10887365 : Blo 794341 10887365 := bstep (se 4 (by rfl) ⟨1020690, by rfl⟩ : syracuseStep 10887365 = 2041381) B2041381
theorem B794835 : Blo 794341 794835 := bstep (se 1 (by rfl) ⟨596126, by rfl⟩ : syracuseStep 794835 = 1192253) B1192253
theorem B7250147 : Blo 794341 7250147 := bstep (se 1 (by rfl) ⟨5437610, by rfl⟩ : syracuseStep 7250147 = 10875221) B10875221
theorem B794851 : Blo 794341 794851 := bstep (se 1 (by rfl) ⟨596138, by rfl⟩ : syracuseStep 794851 = 1192277) B1192277
theorem B794867 : Blo 794341 794867 := bstep (se 1 (by rfl) ⟨596150, by rfl⟩ : syracuseStep 794867 = 1192301) B1192301
theorem B794883 : Blo 794341 794883 := bstep (se 1 (by rfl) ⟨596162, by rfl⟩ : syracuseStep 794883 = 1192325) B1192325
theorem B794899 : Blo 794341 794899 := bstep (se 1 (by rfl) ⟨596174, by rfl⟩ : syracuseStep 794899 = 1192349) B1192349
theorem B794915 : Blo 794341 794915 := bstep (se 1 (by rfl) ⟨596186, by rfl⟩ : syracuseStep 794915 = 1192373) B1192373
theorem B794931 : Blo 794341 794931 := bstep (se 1 (by rfl) ⟨596198, by rfl⟩ : syracuseStep 794931 = 1192397) B1192397
theorem B794947 : Blo 794341 794947 := bstep (se 1 (by rfl) ⟨596210, by rfl⟩ : syracuseStep 794947 = 1192421) B1192421
theorem B794963 : Blo 794341 794963 := bstep (se 1 (by rfl) ⟨596222, by rfl⟩ : syracuseStep 794963 = 1192445) B1192445
theorem B794979 : Blo 794341 794979 := bstep (se 1 (by rfl) ⟨596234, by rfl⟩ : syracuseStep 794979 = 1192469) B1192469
theorem B794995 : Blo 794341 794995 := bstep (se 1 (by rfl) ⟨596246, by rfl⟩ : syracuseStep 794995 = 1192493) B1192493
theorem B795011 : Blo 794341 795011 := bstep (se 1 (by rfl) ⟨596258, by rfl⟩ : syracuseStep 795011 = 1192517) B1192517
theorem B795027 : Blo 794341 795027 := bstep (se 1 (by rfl) ⟨596270, by rfl⟩ : syracuseStep 795027 = 1192541) B1192541
theorem B795043 : Blo 794341 795043 := bstep (se 1 (by rfl) ⟨596282, by rfl⟩ : syracuseStep 795043 = 1192565) B1192565
theorem B1614257 : Blo 794341 1614257 := bstep (se 2 (by rfl) ⟨605346, by rfl⟩ : syracuseStep 1614257 = 1210693) B1210693
theorem B795059 : Blo 794341 795059 := bstep (se 1 (by rfl) ⟨596294, by rfl⟩ : syracuseStep 795059 = 1192589) B1192589
theorem B795075 : Blo 794341 795075 := bstep (se 1 (by rfl) ⟨596306, by rfl⟩ : syracuseStep 795075 = 1192613) B1192613
theorem B795091 : Blo 794341 795091 := bstep (se 1 (by rfl) ⟨596318, by rfl⟩ : syracuseStep 795091 = 1192637) B1192637
theorem B795107 : Blo 794341 795107 := bstep (se 1 (by rfl) ⟨596330, by rfl⟩ : syracuseStep 795107 = 1192661) B1192661
theorem B3023345 : Blo 794341 3023345 := bstep (se 2 (by rfl) ⟨1133754, by rfl⟩ : syracuseStep 3023345 = 2267509) B2267509
theorem B795123 : Blo 794341 795123 := bstep (se 1 (by rfl) ⟨596342, by rfl⟩ : syracuseStep 795123 = 1192685) B1192685
theorem B795139 : Blo 794341 795139 := bstep (se 1 (by rfl) ⟨596354, by rfl⟩ : syracuseStep 795139 = 1192709) B1192709
theorem B795155 : Blo 794341 795155 := bstep (se 1 (by rfl) ⟨596366, by rfl⟩ : syracuseStep 795155 = 1192733) B1192733
theorem B795171 : Blo 794341 795171 := bstep (se 1 (by rfl) ⟨596378, by rfl⟩ : syracuseStep 795171 = 1192757) B1192757
theorem B795187 : Blo 794341 795187 := bstep (se 1 (by rfl) ⟨596390, by rfl⟩ : syracuseStep 795187 = 1192781) B1192781
theorem B795203 : Blo 794341 795203 := bstep (se 1 (by rfl) ⟨596402, by rfl⟩ : syracuseStep 795203 = 1192805) B1192805
theorem B795219 : Blo 794341 795219 := bstep (se 1 (by rfl) ⟨596414, by rfl⟩ : syracuseStep 795219 = 1192829) B1192829
theorem B795235 : Blo 794341 795235 := bstep (se 1 (by rfl) ⟨596426, by rfl⟩ : syracuseStep 795235 = 1192853) B1192853
theorem B795251 : Blo 794341 795251 := bstep (se 1 (by rfl) ⟨596438, by rfl⟩ : syracuseStep 795251 = 1192877) B1192877
theorem B795267 : Blo 794341 795267 := bstep (se 1 (by rfl) ⟨596450, by rfl⟩ : syracuseStep 795267 = 1192901) B1192901
theorem B795283 : Blo 794341 795283 := bstep (se 1 (by rfl) ⟨596462, by rfl⟩ : syracuseStep 795283 = 1192925) B1192925
theorem B795299 : Blo 794341 795299 := bstep (se 1 (by rfl) ⟨596474, by rfl⟩ : syracuseStep 795299 = 1192949) B1192949
theorem B795315 : Blo 794341 795315 := bstep (se 1 (by rfl) ⟨596486, by rfl⟩ : syracuseStep 795315 = 1192973) B1192973
theorem B795331 : Blo 794341 795331 := bstep (se 1 (by rfl) ⟨596498, by rfl⟩ : syracuseStep 795331 = 1192997) B1192997
theorem B795347 : Blo 794341 795347 := bstep (se 1 (by rfl) ⟨596510, by rfl⟩ : syracuseStep 795347 = 1193021) B1193021
theorem B795363 : Blo 794341 795363 := bstep (se 1 (by rfl) ⟨596522, by rfl⟩ : syracuseStep 795363 = 1193045) B1193045
theorem B795379 : Blo 794341 795379 := bstep (se 1 (by rfl) ⟨596534, by rfl⟩ : syracuseStep 795379 = 1193069) B1193069
theorem B795395 : Blo 794341 795395 := bstep (se 1 (by rfl) ⟨596546, by rfl⟩ : syracuseStep 795395 = 1193093) B1193093
theorem B795411 : Blo 794341 795411 := bstep (se 1 (by rfl) ⟨596558, by rfl⟩ : syracuseStep 795411 = 1193117) B1193117
theorem B893731 : Blo 794341 893731 := bstep (se 1 (by rfl) ⟨670298, by rfl⟩ : syracuseStep 893731 = 1340597) B1340597
theorem B795427 : Blo 794341 795427 := bstep (se 1 (by rfl) ⟨596570, by rfl⟩ : syracuseStep 795427 = 1193141) B1193141
theorem B795443 : Blo 794341 795443 := bstep (se 1 (by rfl) ⟨596582, by rfl⟩ : syracuseStep 795443 = 1193165) B1193165
theorem B795459 : Blo 794341 795459 := bstep (se 1 (by rfl) ⟨596594, by rfl⟩ : syracuseStep 795459 = 1193189) B1193189
theorem B795475 : Blo 794341 795475 := bstep (se 1 (by rfl) ⟨596606, by rfl⟩ : syracuseStep 795475 = 1193213) B1193213
theorem B795491 : Blo 794341 795491 := bstep (se 1 (by rfl) ⟨596618, by rfl⟩ : syracuseStep 795491 = 1193237) B1193237
theorem B795507 : Blo 794341 795507 := bstep (se 1 (by rfl) ⟨596630, by rfl⟩ : syracuseStep 795507 = 1193261) B1193261
theorem B795523 : Blo 794341 795523 := bstep (se 1 (by rfl) ⟨596642, by rfl⟩ : syracuseStep 795523 = 1193285) B1193285
theorem B795539 : Blo 794341 795539 := bstep (se 1 (by rfl) ⟨596654, by rfl⟩ : syracuseStep 795539 = 1193309) B1193309
theorem B795555 : Blo 794341 795555 := bstep (se 1 (by rfl) ⟨596666, by rfl⟩ : syracuseStep 795555 = 1193333) B1193333
theorem B893875 : Blo 794341 893875 := bstep (se 1 (by rfl) ⟨670406, by rfl⟩ : syracuseStep 893875 = 1340813) B1340813
theorem B795571 : Blo 794341 795571 := bstep (se 1 (by rfl) ⟨596678, by rfl⟩ : syracuseStep 795571 = 1193357) B1193357
theorem B795587 : Blo 794341 795587 := bstep (se 1 (by rfl) ⟨596690, by rfl⟩ : syracuseStep 795587 = 1193381) B1193381
theorem B795603 : Blo 794341 795603 := bstep (se 1 (by rfl) ⟨596702, by rfl⟩ : syracuseStep 795603 = 1193405) B1193405
theorem B795619 : Blo 794341 795619 := bstep (se 1 (by rfl) ⟨596714, by rfl⟩ : syracuseStep 795619 = 1193429) B1193429
theorem B795635 : Blo 794341 795635 := bstep (se 1 (by rfl) ⟨596726, by rfl⟩ : syracuseStep 795635 = 1193453) B1193453
theorem B795651 : Blo 794341 795651 := bstep (se 1 (by rfl) ⟨596738, by rfl⟩ : syracuseStep 795651 = 1193477) B1193477
theorem B795667 : Blo 794341 795667 := bstep (se 1 (by rfl) ⟨596750, by rfl⟩ : syracuseStep 795667 = 1193501) B1193501
theorem B795683 : Blo 794341 795683 := bstep (se 1 (by rfl) ⟨596762, by rfl⟩ : syracuseStep 795683 = 1193525) B1193525
theorem B3449891 : Blo 794341 3449891 := bstep (se 1 (by rfl) ⟨2587418, by rfl⟩ : syracuseStep 3449891 = 5174837) B5174837
theorem B2270243 : Blo 794341 2270243 := bstep (se 1 (by rfl) ⟨1702682, by rfl⟩ : syracuseStep 2270243 = 3405365) B3405365
theorem B795699 : Blo 794341 795699 := bstep (se 1 (by rfl) ⟨596774, by rfl⟩ : syracuseStep 795699 = 1193549) B1193549
theorem B894019 : Blo 794341 894019 := bstep (se 1 (by rfl) ⟨670514, by rfl⟩ : syracuseStep 894019 = 1341029) B1341029
theorem B795715 : Blo 794341 795715 := bstep (se 1 (by rfl) ⟨596786, by rfl⟩ : syracuseStep 795715 = 1193573) B1193573
theorem B795731 : Blo 794341 795731 := bstep (se 1 (by rfl) ⟨596798, by rfl⟩ : syracuseStep 795731 = 1193597) B1193597
theorem B795747 : Blo 794341 795747 := bstep (se 1 (by rfl) ⟨596810, by rfl⟩ : syracuseStep 795747 = 1193621) B1193621
theorem B4039793 : Blo 794341 4039793 := bstep (se 2 (by rfl) ⟨1514922, by rfl⟩ : syracuseStep 4039793 = 3029845) B3029845
theorem B795763 : Blo 794341 795763 := bstep (se 1 (by rfl) ⟨596822, by rfl⟩ : syracuseStep 795763 = 1193645) B1193645
theorem B795779 : Blo 794341 795779 := bstep (se 1 (by rfl) ⟨596834, by rfl⟩ : syracuseStep 795779 = 1193669) B1193669
theorem B3024013 : Blo 794341 3024013 := bstep (se 3 (by rfl) ⟨567002, by rfl⟩ : syracuseStep 3024013 = 1134005) B1134005
theorem B795795 : Blo 794341 795795 := bstep (se 1 (by rfl) ⟨596846, by rfl⟩ : syracuseStep 795795 = 1193693) B1193693
theorem B795811 : Blo 794341 795811 := bstep (se 1 (by rfl) ⟨596858, by rfl⟩ : syracuseStep 795811 = 1193717) B1193717
theorem B795827 : Blo 794341 795827 := bstep (se 1 (by rfl) ⟨596870, by rfl⟩ : syracuseStep 795827 = 1193741) B1193741
theorem B795843 : Blo 794341 795843 := bstep (se 1 (by rfl) ⟨596882, by rfl⟩ : syracuseStep 795843 = 1193765) B1193765
theorem B894163 : Blo 794341 894163 := bstep (se 1 (by rfl) ⟨670622, by rfl⟩ : syracuseStep 894163 = 1341245) B1341245
theorem B795859 : Blo 794341 795859 := bstep (se 1 (by rfl) ⟨596894, by rfl⟩ : syracuseStep 795859 = 1193789) B1193789
theorem B795875 : Blo 794341 795875 := bstep (se 1 (by rfl) ⟨596906, by rfl⟩ : syracuseStep 795875 = 1193813) B1193813
theorem B795891 : Blo 794341 795891 := bstep (se 1 (by rfl) ⟨596918, by rfl⟩ : syracuseStep 795891 = 1193837) B1193837
theorem B795907 : Blo 794341 795907 := bstep (se 1 (by rfl) ⟨596930, by rfl⟩ : syracuseStep 795907 = 1193861) B1193861
theorem B795923 : Blo 794341 795923 := bstep (se 1 (by rfl) ⟨596942, by rfl⟩ : syracuseStep 795923 = 1193885) B1193885
theorem B795939 : Blo 794341 795939 := bstep (se 1 (by rfl) ⟨596954, by rfl⟩ : syracuseStep 795939 = 1193909) B1193909
theorem B795955 : Blo 794341 795955 := bstep (se 1 (by rfl) ⟨596966, by rfl⟩ : syracuseStep 795955 = 1193933) B1193933
theorem B795971 : Blo 794341 795971 := bstep (se 1 (by rfl) ⟨596978, by rfl⟩ : syracuseStep 795971 = 1193957) B1193957
theorem B795987 : Blo 794341 795987 := bstep (se 1 (by rfl) ⟨596990, by rfl⟩ : syracuseStep 795987 = 1193981) B1193981
theorem B894307 : Blo 794341 894307 := bstep (se 1 (by rfl) ⟨670730, by rfl⟩ : syracuseStep 894307 = 1341461) B1341461
theorem B796003 : Blo 794341 796003 := bstep (se 1 (by rfl) ⟨597002, by rfl⟩ : syracuseStep 796003 = 1194005) B1194005
theorem B796019 : Blo 794341 796019 := bstep (se 1 (by rfl) ⟨597014, by rfl⟩ : syracuseStep 796019 = 1194029) B1194029
theorem B796035 : Blo 794341 796035 := bstep (se 1 (by rfl) ⟨597026, by rfl⟩ : syracuseStep 796035 = 1194053) B1194053
theorem B796051 : Blo 794341 796051 := bstep (se 1 (by rfl) ⟨597038, by rfl⟩ : syracuseStep 796051 = 1194077) B1194077
theorem B796067 : Blo 794341 796067 := bstep (se 1 (by rfl) ⟨597050, by rfl⟩ : syracuseStep 796067 = 1194101) B1194101
theorem B796083 : Blo 794341 796083 := bstep (se 1 (by rfl) ⟨597062, by rfl⟩ : syracuseStep 796083 = 1194125) B1194125
theorem B796099 : Blo 794341 796099 := bstep (se 1 (by rfl) ⟨597074, by rfl⟩ : syracuseStep 796099 = 1194149) B1194149
theorem B796115 : Blo 794341 796115 := bstep (se 1 (by rfl) ⟨597086, by rfl⟩ : syracuseStep 796115 = 1194173) B1194173
theorem B1910243 : Blo 794341 1910243 := bstep (se 1 (by rfl) ⟨1432682, by rfl⟩ : syracuseStep 1910243 = 2865365) B2865365
theorem B796131 : Blo 794341 796131 := bstep (se 1 (by rfl) ⟨597098, by rfl⟩ : syracuseStep 796131 = 1194197) B1194197
theorem B894451 : Blo 794341 894451 := bstep (se 1 (by rfl) ⟨670838, by rfl⟩ : syracuseStep 894451 = 1341677) B1341677
theorem B796147 : Blo 794341 796147 := bstep (se 1 (by rfl) ⟨597110, by rfl⟩ : syracuseStep 796147 = 1194221) B1194221
theorem B796163 : Blo 794341 796163 := bstep (se 1 (by rfl) ⟨597122, by rfl⟩ : syracuseStep 796163 = 1194245) B1194245
theorem B796179 : Blo 794341 796179 := bstep (se 1 (by rfl) ⟨597134, by rfl⟩ : syracuseStep 796179 = 1194269) B1194269
theorem B796195 : Blo 794341 796195 := bstep (se 1 (by rfl) ⟨597146, by rfl⟩ : syracuseStep 796195 = 1194293) B1194293
theorem B796211 : Blo 794341 796211 := bstep (se 1 (by rfl) ⟨597158, by rfl⟩ : syracuseStep 796211 = 1194317) B1194317
theorem B796227 : Blo 794341 796227 := bstep (se 1 (by rfl) ⟨597170, by rfl⟩ : syracuseStep 796227 = 1194341) B1194341
theorem B796243 : Blo 794341 796243 := bstep (se 1 (by rfl) ⟨597182, by rfl⟩ : syracuseStep 796243 = 1194365) B1194365
theorem B796259 : Blo 794341 796259 := bstep (se 1 (by rfl) ⟨597194, by rfl⟩ : syracuseStep 796259 = 1194389) B1194389
theorem B796275 : Blo 794341 796275 := bstep (se 1 (by rfl) ⟨597206, by rfl⟩ : syracuseStep 796275 = 1194413) B1194413
theorem B894595 : Blo 794341 894595 := bstep (se 1 (by rfl) ⟨670946, by rfl⟩ : syracuseStep 894595 = 1341893) B1341893
theorem B796291 : Blo 794341 796291 := bstep (se 1 (by rfl) ⟨597218, by rfl⟩ : syracuseStep 796291 = 1194437) B1194437
theorem B796307 : Blo 794341 796307 := bstep (se 1 (by rfl) ⟨597230, by rfl⟩ : syracuseStep 796307 = 1194461) B1194461
theorem B796323 : Blo 794341 796323 := bstep (se 1 (by rfl) ⟨597242, by rfl⟩ : syracuseStep 796323 = 1194485) B1194485
theorem B796339 : Blo 794341 796339 := bstep (se 1 (by rfl) ⟨597254, by rfl⟩ : syracuseStep 796339 = 1194509) B1194509
theorem B796355 : Blo 794341 796355 := bstep (se 1 (by rfl) ⟨597266, by rfl⟩ : syracuseStep 796355 = 1194533) B1194533
theorem B1615555 : Blo 794341 1615555 := bstep (se 1 (by rfl) ⟨1211666, by rfl⟩ : syracuseStep 1615555 = 2423333) B2423333
theorem B796371 : Blo 794341 796371 := bstep (se 1 (by rfl) ⟨597278, by rfl⟩ : syracuseStep 796371 = 1194557) B1194557
theorem B796387 : Blo 794341 796387 := bstep (se 1 (by rfl) ⟨597290, by rfl⟩ : syracuseStep 796387 = 1194581) B1194581
theorem B796403 : Blo 794341 796403 := bstep (se 1 (by rfl) ⟨597302, by rfl⟩ : syracuseStep 796403 = 1194605) B1194605
theorem B796419 : Blo 794341 796419 := bstep (se 1 (by rfl) ⟨597314, by rfl⟩ : syracuseStep 796419 = 1194629) B1194629
theorem B894739 : Blo 794341 894739 := bstep (se 1 (by rfl) ⟨671054, by rfl⟩ : syracuseStep 894739 = 1342109) B1342109
theorem B796435 : Blo 794341 796435 := bstep (se 1 (by rfl) ⟨597326, by rfl⟩ : syracuseStep 796435 = 1194653) B1194653
theorem B796451 : Blo 794341 796451 := bstep (se 1 (by rfl) ⟨597338, by rfl⟩ : syracuseStep 796451 = 1194677) B1194677
theorem B796467 : Blo 794341 796467 := bstep (se 1 (by rfl) ⟨597350, by rfl⟩ : syracuseStep 796467 = 1194701) B1194701
theorem B796483 : Blo 794341 796483 := bstep (se 1 (by rfl) ⟨597362, by rfl⟩ : syracuseStep 796483 = 1194725) B1194725
theorem B796499 : Blo 794341 796499 := bstep (se 1 (by rfl) ⟨597374, by rfl⟩ : syracuseStep 796499 = 1194749) B1194749
theorem B796515 : Blo 794341 796515 := bstep (se 1 (by rfl) ⟨597386, by rfl⟩ : syracuseStep 796515 = 1194773) B1194773
theorem B796531 : Blo 794341 796531 := bstep (se 1 (by rfl) ⟨597398, by rfl⟩ : syracuseStep 796531 = 1194797) B1194797
theorem B796547 : Blo 794341 796547 := bstep (se 1 (by rfl) ⟨597410, by rfl⟩ : syracuseStep 796547 = 1194821) B1194821
theorem B796563 : Blo 794341 796563 := bstep (se 1 (by rfl) ⟨597422, by rfl⟩ : syracuseStep 796563 = 1194845) B1194845
theorem B894883 : Blo 794341 894883 := bstep (se 1 (by rfl) ⟨671162, by rfl⟩ : syracuseStep 894883 = 1342325) B1342325
theorem B796579 : Blo 794341 796579 := bstep (se 1 (by rfl) ⟨597434, by rfl⟩ : syracuseStep 796579 = 1194869) B1194869
theorem B3024803 : Blo 794341 3024803 := bstep (se 1 (by rfl) ⟨2268602, by rfl⟩ : syracuseStep 3024803 = 4537205) B4537205
theorem B796595 : Blo 794341 796595 := bstep (se 1 (by rfl) ⟨597446, by rfl⟩ : syracuseStep 796595 = 1194893) B1194893
theorem B796611 : Blo 794341 796611 := bstep (se 1 (by rfl) ⟨597458, by rfl⟩ : syracuseStep 796611 = 1194917) B1194917
theorem B796627 : Blo 794341 796627 := bstep (se 1 (by rfl) ⟨597470, by rfl⟩ : syracuseStep 796627 = 1194941) B1194941
theorem B9054179 : Blo 794341 9054179 := bstep (se 1 (by rfl) ⟨6790634, by rfl⟩ : syracuseStep 9054179 = 13581269) B13581269
theorem B796643 : Blo 794341 796643 := bstep (se 1 (by rfl) ⟨597482, by rfl⟩ : syracuseStep 796643 = 1194965) B1194965
theorem B6465521 : Blo 794341 6465521 := bstep (se 2 (by rfl) ⟨2424570, by rfl⟩ : syracuseStep 6465521 = 4849141) B4849141
theorem B796659 : Blo 794341 796659 := bstep (se 1 (by rfl) ⟨597494, by rfl⟩ : syracuseStep 796659 = 1194989) B1194989
theorem B796675 : Blo 794341 796675 := bstep (se 1 (by rfl) ⟨597506, by rfl⟩ : syracuseStep 796675 = 1195013) B1195013
theorem B796691 : Blo 794341 796691 := bstep (se 1 (by rfl) ⟨597518, by rfl⟩ : syracuseStep 796691 = 1195037) B1195037
theorem B796707 : Blo 794341 796707 := bstep (se 1 (by rfl) ⟨597530, by rfl⟩ : syracuseStep 796707 = 1195061) B1195061
theorem B895027 : Blo 794341 895027 := bstep (se 1 (by rfl) ⟨671270, by rfl⟩ : syracuseStep 895027 = 1342541) B1342541
theorem B796723 : Blo 794341 796723 := bstep (se 1 (by rfl) ⟨597542, by rfl⟩ : syracuseStep 796723 = 1195085) B1195085
theorem B796739 : Blo 794341 796739 := bstep (se 1 (by rfl) ⟨597554, by rfl⟩ : syracuseStep 796739 = 1195109) B1195109
theorem B796755 : Blo 794341 796755 := bstep (se 1 (by rfl) ⟨597566, by rfl⟩ : syracuseStep 796755 = 1195133) B1195133
theorem B3221603 : Blo 794341 3221603 := bstep (se 1 (by rfl) ⟨2416202, by rfl⟩ : syracuseStep 3221603 = 4832405) B4832405
theorem B796771 : Blo 794341 796771 := bstep (se 1 (by rfl) ⟨597578, by rfl⟩ : syracuseStep 796771 = 1195157) B1195157
theorem B796787 : Blo 794341 796787 := bstep (se 1 (by rfl) ⟨597590, by rfl⟩ : syracuseStep 796787 = 1195181) B1195181
theorem B796803 : Blo 794341 796803 := bstep (se 1 (by rfl) ⟨597602, by rfl⟩ : syracuseStep 796803 = 1195205) B1195205
theorem B796819 : Blo 794341 796819 := bstep (se 1 (by rfl) ⟨597614, by rfl⟩ : syracuseStep 796819 = 1195229) B1195229
theorem B796835 : Blo 794341 796835 := bstep (se 1 (by rfl) ⟨597626, by rfl⟩ : syracuseStep 796835 = 1195253) B1195253
theorem B796851 : Blo 794341 796851 := bstep (se 1 (by rfl) ⟨597638, by rfl⟩ : syracuseStep 796851 = 1195277) B1195277
theorem B895171 : Blo 794341 895171 := bstep (se 1 (by rfl) ⟨671378, by rfl⟩ : syracuseStep 895171 = 1342757) B1342757
theorem B796867 : Blo 794341 796867 := bstep (se 1 (by rfl) ⟨597650, by rfl⟩ : syracuseStep 796867 = 1195301) B1195301
theorem B796883 : Blo 794341 796883 := bstep (se 1 (by rfl) ⟨597662, by rfl⟩ : syracuseStep 796883 = 1195325) B1195325
theorem B796899 : Blo 794341 796899 := bstep (se 1 (by rfl) ⟨597674, by rfl⟩ : syracuseStep 796899 = 1195349) B1195349
theorem B2271473 : Blo 794341 2271473 := bstep (se 2 (by rfl) ⟨851802, by rfl⟩ : syracuseStep 2271473 = 1703605) B1703605
theorem B796915 : Blo 794341 796915 := bstep (se 1 (by rfl) ⟨597686, by rfl⟩ : syracuseStep 796915 = 1195373) B1195373
theorem B796931 : Blo 794341 796931 := bstep (se 1 (by rfl) ⟨597698, by rfl⟩ : syracuseStep 796931 = 1195397) B1195397
theorem B796947 : Blo 794341 796947 := bstep (se 1 (by rfl) ⟨597710, by rfl⟩ : syracuseStep 796947 = 1195421) B1195421
theorem B796963 : Blo 794341 796963 := bstep (se 1 (by rfl) ⟨597722, by rfl⟩ : syracuseStep 796963 = 1195445) B1195445
theorem B1911089 : Blo 794341 1911089 := bstep (se 2 (by rfl) ⟨716658, by rfl⟩ : syracuseStep 1911089 = 1433317) B1433317
theorem B796979 : Blo 794341 796979 := bstep (se 1 (by rfl) ⟨597734, by rfl⟩ : syracuseStep 796979 = 1195469) B1195469
theorem B796995 : Blo 794341 796995 := bstep (se 1 (by rfl) ⟨597746, by rfl⟩ : syracuseStep 796995 = 1195493) B1195493
theorem B4532557 : Blo 794341 4532557 := bstep (se 3 (by rfl) ⟨849854, by rfl⟩ : syracuseStep 4532557 = 1699709) B1699709
theorem B895315 : Blo 794341 895315 := bstep (se 1 (by rfl) ⟨671486, by rfl⟩ : syracuseStep 895315 = 1342973) B1342973
theorem B797011 : Blo 794341 797011 := bstep (se 1 (by rfl) ⟨597758, by rfl⟩ : syracuseStep 797011 = 1195517) B1195517
theorem B797027 : Blo 794341 797027 := bstep (se 1 (by rfl) ⟨597770, by rfl⟩ : syracuseStep 797027 = 1195541) B1195541
theorem B797043 : Blo 794341 797043 := bstep (se 1 (by rfl) ⟨597782, by rfl⟩ : syracuseStep 797043 = 1195565) B1195565
theorem B797059 : Blo 794341 797059 := bstep (se 1 (by rfl) ⟨597794, by rfl⟩ : syracuseStep 797059 = 1195589) B1195589
theorem B797075 : Blo 794341 797075 := bstep (se 1 (by rfl) ⟨597806, by rfl⟩ : syracuseStep 797075 = 1195613) B1195613
theorem B797091 : Blo 794341 797091 := bstep (se 1 (by rfl) ⟨597818, by rfl⟩ : syracuseStep 797091 = 1195637) B1195637
theorem B797107 : Blo 794341 797107 := bstep (se 1 (by rfl) ⟨597830, by rfl⟩ : syracuseStep 797107 = 1195661) B1195661
theorem B797123 : Blo 794341 797123 := bstep (se 1 (by rfl) ⟨597842, by rfl⟩ : syracuseStep 797123 = 1195685) B1195685
theorem B797139 : Blo 794341 797139 := bstep (se 1 (by rfl) ⟨597854, by rfl⟩ : syracuseStep 797139 = 1195709) B1195709
theorem B895459 : Blo 794341 895459 := bstep (se 1 (by rfl) ⟨671594, by rfl⟩ : syracuseStep 895459 = 1343189) B1343189
theorem B797155 : Blo 794341 797155 := bstep (se 1 (by rfl) ⟨597866, by rfl⟩ : syracuseStep 797155 = 1195733) B1195733
theorem B797171 : Blo 794341 797171 := bstep (se 1 (by rfl) ⟨597878, by rfl⟩ : syracuseStep 797171 = 1195757) B1195757
theorem B797187 : Blo 794341 797187 := bstep (se 1 (by rfl) ⟨597890, by rfl⟩ : syracuseStep 797187 = 1195781) B1195781
theorem B797203 : Blo 794341 797203 := bstep (se 1 (by rfl) ⟨597902, by rfl⟩ : syracuseStep 797203 = 1195805) B1195805
theorem B797219 : Blo 794341 797219 := bstep (se 1 (by rfl) ⟨597914, by rfl⟩ : syracuseStep 797219 = 1195829) B1195829
theorem B4041251 : Blo 794341 4041251 := bstep (se 1 (by rfl) ⟨3030938, by rfl⟩ : syracuseStep 4041251 = 6061877) B6061877
theorem B3025457 : Blo 794341 3025457 := bstep (se 2 (by rfl) ⟨1134546, by rfl⟩ : syracuseStep 3025457 = 2269093) B2269093
theorem B797235 : Blo 794341 797235 := bstep (se 1 (by rfl) ⟨597926, by rfl⟩ : syracuseStep 797235 = 1195853) B1195853
theorem B797251 : Blo 794341 797251 := bstep (se 1 (by rfl) ⟨597938, by rfl⟩ : syracuseStep 797251 = 1195877) B1195877
theorem B797267 : Blo 794341 797267 := bstep (se 1 (by rfl) ⟨597950, by rfl⟩ : syracuseStep 797267 = 1195901) B1195901
theorem B797283 : Blo 794341 797283 := bstep (se 1 (by rfl) ⟨597962, by rfl⟩ : syracuseStep 797283 = 1195925) B1195925
theorem B895603 : Blo 794341 895603 := bstep (se 1 (by rfl) ⟨671702, by rfl⟩ : syracuseStep 895603 = 1343405) B1343405
theorem B797299 : Blo 794341 797299 := bstep (se 1 (by rfl) ⟨597974, by rfl⟩ : syracuseStep 797299 = 1195949) B1195949
theorem B797315 : Blo 794341 797315 := bstep (se 1 (by rfl) ⟨597986, by rfl⟩ : syracuseStep 797315 = 1195973) B1195973
theorem B797331 : Blo 794341 797331 := bstep (se 1 (by rfl) ⟨597998, by rfl⟩ : syracuseStep 797331 = 1195997) B1195997
theorem B797347 : Blo 794341 797347 := bstep (se 1 (by rfl) ⟨598010, by rfl⟩ : syracuseStep 797347 = 1196021) B1196021
theorem B797363 : Blo 794341 797363 := bstep (se 1 (by rfl) ⟨598022, by rfl⟩ : syracuseStep 797363 = 1196045) B1196045
theorem B797379 : Blo 794341 797379 := bstep (se 1 (by rfl) ⟨598034, by rfl⟩ : syracuseStep 797379 = 1196069) B1196069
theorem B797395 : Blo 794341 797395 := bstep (se 1 (by rfl) ⟨598046, by rfl⟩ : syracuseStep 797395 = 1196093) B1196093
theorem B797411 : Blo 794341 797411 := bstep (se 1 (by rfl) ⟨598058, by rfl⟩ : syracuseStep 797411 = 1196117) B1196117
theorem B4303601 : Blo 794341 4303601 := bstep (se 2 (by rfl) ⟨1613850, by rfl⟩ : syracuseStep 4303601 = 3227701) B3227701
theorem B797427 : Blo 794341 797427 := bstep (se 1 (by rfl) ⟨598070, by rfl⟩ : syracuseStep 797427 = 1196141) B1196141
theorem B895747 : Blo 794341 895747 := bstep (se 1 (by rfl) ⟨671810, by rfl⟩ : syracuseStep 895747 = 1343621) B1343621
theorem B797443 : Blo 794341 797443 := bstep (se 1 (by rfl) ⟨598082, by rfl⟩ : syracuseStep 797443 = 1196165) B1196165
theorem B797459 : Blo 794341 797459 := bstep (se 1 (by rfl) ⟨598094, by rfl⟩ : syracuseStep 797459 = 1196189) B1196189
theorem B797475 : Blo 794341 797475 := bstep (se 1 (by rfl) ⟨598106, by rfl⟩ : syracuseStep 797475 = 1196213) B1196213
theorem B797491 : Blo 794341 797491 := bstep (se 1 (by rfl) ⟨598118, by rfl⟩ : syracuseStep 797491 = 1196237) B1196237
theorem B797507 : Blo 794341 797507 := bstep (se 1 (by rfl) ⟨598130, by rfl⟩ : syracuseStep 797507 = 1196261) B1196261
theorem B797523 : Blo 794341 797523 := bstep (se 1 (by rfl) ⟨598142, by rfl⟩ : syracuseStep 797523 = 1196285) B1196285
theorem B797539 : Blo 794341 797539 := bstep (se 1 (by rfl) ⟨598154, by rfl⟩ : syracuseStep 797539 = 1196309) B1196309
theorem B797555 : Blo 794341 797555 := bstep (se 1 (by rfl) ⟨598166, by rfl⟩ : syracuseStep 797555 = 1196333) B1196333
theorem B797571 : Blo 794341 797571 := bstep (se 1 (by rfl) ⟨598178, by rfl⟩ : syracuseStep 797571 = 1196357) B1196357
theorem B895891 : Blo 794341 895891 := bstep (se 1 (by rfl) ⟨671918, by rfl⟩ : syracuseStep 895891 = 1343837) B1343837
theorem B797587 : Blo 794341 797587 := bstep (se 1 (by rfl) ⟨598190, by rfl⟩ : syracuseStep 797587 = 1196381) B1196381
theorem B797603 : Blo 794341 797603 := bstep (se 1 (by rfl) ⟨598202, by rfl⟩ : syracuseStep 797603 = 1196405) B1196405
theorem B797619 : Blo 794341 797619 := bstep (se 1 (by rfl) ⟨598214, by rfl⟩ : syracuseStep 797619 = 1196429) B1196429
theorem B797635 : Blo 794341 797635 := bstep (se 1 (by rfl) ⟨598226, by rfl⟩ : syracuseStep 797635 = 1196453) B1196453
theorem B797651 : Blo 794341 797651 := bstep (se 1 (by rfl) ⟨598238, by rfl⟩ : syracuseStep 797651 = 1196477) B1196477
theorem B797667 : Blo 794341 797667 := bstep (se 1 (by rfl) ⟨598250, by rfl⟩ : syracuseStep 797667 = 1196501) B1196501
theorem B797683 : Blo 794341 797683 := bstep (se 1 (by rfl) ⟨598262, by rfl⟩ : syracuseStep 797683 = 1196525) B1196525
theorem B797699 : Blo 794341 797699 := bstep (se 1 (by rfl) ⟨598274, by rfl⟩ : syracuseStep 797699 = 1196549) B1196549
theorem B797715 : Blo 794341 797715 := bstep (se 1 (by rfl) ⟨598286, by rfl⟩ : syracuseStep 797715 = 1196573) B1196573
theorem B896035 : Blo 794341 896035 := bstep (se 1 (by rfl) ⟨672026, by rfl⟩ : syracuseStep 896035 = 1344053) B1344053
theorem B797731 : Blo 794341 797731 := bstep (se 1 (by rfl) ⟨598298, by rfl⟩ : syracuseStep 797731 = 1196597) B1196597
theorem B797747 : Blo 794341 797747 := bstep (se 1 (by rfl) ⟨598310, by rfl⟩ : syracuseStep 797747 = 1196621) B1196621
theorem B797763 : Blo 794341 797763 := bstep (se 1 (by rfl) ⟨598322, by rfl⟩ : syracuseStep 797763 = 1196645) B1196645
theorem B797779 : Blo 794341 797779 := bstep (se 1 (by rfl) ⟨598334, by rfl⟩ : syracuseStep 797779 = 1196669) B1196669
theorem B797795 : Blo 794341 797795 := bstep (se 1 (by rfl) ⟨598346, by rfl⟩ : syracuseStep 797795 = 1196693) B1196693
theorem B797811 : Blo 794341 797811 := bstep (se 1 (by rfl) ⟨598358, by rfl⟩ : syracuseStep 797811 = 1196717) B1196717
theorem B797827 : Blo 794341 797827 := bstep (se 1 (by rfl) ⟨598370, by rfl⟩ : syracuseStep 797827 = 1196741) B1196741
theorem B5450885 : Blo 794341 5450885 := bstep (se 4 (by rfl) ⟨511020, by rfl⟩ : syracuseStep 5450885 = 1022041) B1022041
theorem B797843 : Blo 794341 797843 := bstep (se 1 (by rfl) ⟨598382, by rfl⟩ : syracuseStep 797843 = 1196765) B1196765
theorem B797859 : Blo 794341 797859 := bstep (se 1 (by rfl) ⟨598394, by rfl⟩ : syracuseStep 797859 = 1196789) B1196789
theorem B896179 : Blo 794341 896179 := bstep (se 1 (by rfl) ⟨672134, by rfl⟩ : syracuseStep 896179 = 1344269) B1344269
theorem B797875 : Blo 794341 797875 := bstep (se 1 (by rfl) ⟨598406, by rfl⟩ : syracuseStep 797875 = 1196813) B1196813
theorem B797891 : Blo 794341 797891 := bstep (se 1 (by rfl) ⟨598418, by rfl⟩ : syracuseStep 797891 = 1196837) B1196837
theorem B797907 : Blo 794341 797907 := bstep (se 1 (by rfl) ⟨598430, by rfl⟩ : syracuseStep 797907 = 1196861) B1196861
theorem B797923 : Blo 794341 797923 := bstep (se 1 (by rfl) ⟨598442, by rfl⟩ : syracuseStep 797923 = 1196885) B1196885
theorem B797939 : Blo 794341 797939 := bstep (se 1 (by rfl) ⟨598454, by rfl⟩ : syracuseStep 797939 = 1196909) B1196909
theorem B797955 : Blo 794341 797955 := bstep (se 1 (by rfl) ⟨598466, by rfl⟩ : syracuseStep 797955 = 1196933) B1196933
theorem B797971 : Blo 794341 797971 := bstep (se 1 (by rfl) ⟨598478, by rfl⟩ : syracuseStep 797971 = 1196957) B1196957
theorem B797987 : Blo 794341 797987 := bstep (se 1 (by rfl) ⟨598490, by rfl⟩ : syracuseStep 797987 = 1196981) B1196981
theorem B798003 : Blo 794341 798003 := bstep (se 1 (by rfl) ⟨598502, by rfl⟩ : syracuseStep 798003 = 1197005) B1197005
theorem B896323 : Blo 794341 896323 := bstep (se 1 (by rfl) ⟨672242, by rfl⟩ : syracuseStep 896323 = 1344485) B1344485
theorem B798019 : Blo 794341 798019 := bstep (se 1 (by rfl) ⟨598514, by rfl⟩ : syracuseStep 798019 = 1197029) B1197029
theorem B798035 : Blo 794341 798035 := bstep (se 1 (by rfl) ⟨598526, by rfl⟩ : syracuseStep 798035 = 1197053) B1197053
theorem B798051 : Blo 794341 798051 := bstep (se 1 (by rfl) ⟨598538, by rfl⟩ : syracuseStep 798051 = 1197077) B1197077
theorem B798067 : Blo 794341 798067 := bstep (se 1 (by rfl) ⟨598550, by rfl⟩ : syracuseStep 798067 = 1197101) B1197101
theorem B798083 : Blo 794341 798083 := bstep (se 1 (by rfl) ⟨598562, by rfl⟩ : syracuseStep 798083 = 1197125) B1197125
theorem B798099 : Blo 794341 798099 := bstep (se 1 (by rfl) ⟨598574, by rfl⟩ : syracuseStep 798099 = 1197149) B1197149
theorem B798115 : Blo 794341 798115 := bstep (se 1 (by rfl) ⟨598586, by rfl⟩ : syracuseStep 798115 = 1197173) B1197173
theorem B798131 : Blo 794341 798131 := bstep (se 1 (by rfl) ⟨598598, by rfl⟩ : syracuseStep 798131 = 1197197) B1197197
theorem B1617347 : Blo 794341 1617347 := bstep (se 1 (by rfl) ⟨1213010, by rfl⟩ : syracuseStep 1617347 = 2426021) B2426021
theorem B798147 : Blo 794341 798147 := bstep (se 1 (by rfl) ⟨598610, by rfl⟩ : syracuseStep 798147 = 1197221) B1197221
theorem B896467 : Blo 794341 896467 := bstep (se 1 (by rfl) ⟨672350, by rfl⟩ : syracuseStep 896467 = 1344701) B1344701
theorem B798163 : Blo 794341 798163 := bstep (se 1 (by rfl) ⟨598622, by rfl⟩ : syracuseStep 798163 = 1197245) B1197245
theorem B798179 : Blo 794341 798179 := bstep (se 1 (by rfl) ⟨598634, by rfl⟩ : syracuseStep 798179 = 1197269) B1197269
theorem B798195 : Blo 794341 798195 := bstep (se 1 (by rfl) ⟨598646, by rfl⟩ : syracuseStep 798195 = 1197293) B1197293
theorem B798211 : Blo 794341 798211 := bstep (se 1 (by rfl) ⟨598658, by rfl⟩ : syracuseStep 798211 = 1197317) B1197317
theorem B798227 : Blo 794341 798227 := bstep (se 1 (by rfl) ⟨598670, by rfl⟩ : syracuseStep 798227 = 1197341) B1197341
theorem B798243 : Blo 794341 798243 := bstep (se 1 (by rfl) ⟨598682, by rfl⟩ : syracuseStep 798243 = 1197365) B1197365
theorem B798259 : Blo 794341 798259 := bstep (se 1 (by rfl) ⟨598694, by rfl⟩ : syracuseStep 798259 = 1197389) B1197389
theorem B798275 : Blo 794341 798275 := bstep (se 1 (by rfl) ⟨598706, by rfl⟩ : syracuseStep 798275 = 1197413) B1197413
theorem B798291 : Blo 794341 798291 := bstep (se 1 (by rfl) ⟨598718, by rfl⟩ : syracuseStep 798291 = 1197437) B1197437
theorem B1191521 : Blo 794341 1191521 := bstep (se 2 (by rfl) ⟨446820, by rfl⟩ : syracuseStep 1191521 = 893641) B893641
theorem B896611 : Blo 794341 896611 := bstep (se 1 (by rfl) ⟨672458, by rfl⟩ : syracuseStep 896611 = 1344917) B1344917
theorem B798307 : Blo 794341 798307 := bstep (se 1 (by rfl) ⟨598730, by rfl⟩ : syracuseStep 798307 = 1197461) B1197461
theorem B2043505 : Blo 794341 2043505 := bstep (se 2 (by rfl) ⟨766314, by rfl⟩ : syracuseStep 2043505 = 1532629) B1532629
theorem B1191539 : Blo 794341 1191539 := bstep (se 1 (by rfl) ⟨893654, by rfl⟩ : syracuseStep 1191539 = 1787309) B1787309
theorem B798323 : Blo 794341 798323 := bstep (se 1 (by rfl) ⟨598742, by rfl⟩ : syracuseStep 798323 = 1197485) B1197485
theorem B798339 : Blo 794341 798339 := bstep (se 1 (by rfl) ⟨598754, by rfl⟩ : syracuseStep 798339 = 1197509) B1197509
theorem B1191569 : Blo 794341 1191569 := bstep (se 2 (by rfl) ⟨446838, by rfl⟩ : syracuseStep 1191569 = 893677) B893677
theorem B1191587 : Blo 794341 1191587 := bstep (se 1 (by rfl) ⟨893690, by rfl⟩ : syracuseStep 1191587 = 1787381) B1787381
theorem B1289891 : Blo 794341 1289891 := bstep (se 1 (by rfl) ⟨967418, by rfl⟩ : syracuseStep 1289891 = 1934837) B1934837
theorem B2272931 : Blo 794341 2272931 := bstep (se 1 (by rfl) ⟨1704698, by rfl⟩ : syracuseStep 2272931 = 3409397) B3409397
theorem B1191617 : Blo 794341 1191617 := bstep (se 2 (by rfl) ⟨446856, by rfl⟩ : syracuseStep 1191617 = 893713) B893713
theorem B1191635 : Blo 794341 1191635 := bstep (se 1 (by rfl) ⟨893726, by rfl⟩ : syracuseStep 1191635 = 1787453) B1787453
theorem B2010865 : Blo 794341 2010865 := bstep (se 2 (by rfl) ⟨754074, by rfl⟩ : syracuseStep 2010865 = 1508149) B1508149
theorem B1191665 : Blo 794341 1191665 := bstep (se 2 (by rfl) ⟨446874, by rfl⟩ : syracuseStep 1191665 = 893749) B893749
theorem B896755 : Blo 794341 896755 := bstep (se 1 (by rfl) ⟨672566, by rfl⟩ : syracuseStep 896755 = 1345133) B1345133
theorem B1191683 : Blo 794341 1191683 := bstep (se 1 (by rfl) ⟨893762, by rfl⟩ : syracuseStep 1191683 = 1787525) B1787525
theorem B1191713 : Blo 794341 1191713 := bstep (se 2 (by rfl) ⟨446892, by rfl⟩ : syracuseStep 1191713 = 893785) B893785
theorem B1191731 : Blo 794341 1191731 := bstep (se 1 (by rfl) ⟨893798, by rfl⟩ : syracuseStep 1191731 = 1787597) B1787597
theorem B1191761 : Blo 794341 1191761 := bstep (se 2 (by rfl) ⟨446910, by rfl⟩ : syracuseStep 1191761 = 893821) B893821
theorem B1191779 : Blo 794341 1191779 := bstep (se 1 (by rfl) ⟨893834, by rfl⟩ : syracuseStep 1191779 = 1787669) B1787669
theorem B1191809 : Blo 794341 1191809 := bstep (se 2 (by rfl) ⟨446928, by rfl⟩ : syracuseStep 1191809 = 893857) B893857
theorem B896899 : Blo 794341 896899 := bstep (se 1 (by rfl) ⟨672674, by rfl⟩ : syracuseStep 896899 = 1345349) B1345349
theorem B1191827 : Blo 794341 1191827 := bstep (se 1 (by rfl) ⟨893870, by rfl⟩ : syracuseStep 1191827 = 1787741) B1787741
theorem B1191857 : Blo 794341 1191857 := bstep (se 2 (by rfl) ⟨446946, by rfl⟩ : syracuseStep 1191857 = 893893) B893893
theorem B1191875 : Blo 794341 1191875 := bstep (se 1 (by rfl) ⟨893906, by rfl⟩ : syracuseStep 1191875 = 1787813) B1787813
theorem B1191905 : Blo 794341 1191905 := bstep (se 2 (by rfl) ⟨446964, by rfl⟩ : syracuseStep 1191905 = 893929) B893929
theorem B3026915 : Blo 794341 3026915 := bstep (se 1 (by rfl) ⟨2270186, by rfl⟩ : syracuseStep 3026915 = 4540373) B4540373
theorem B3026929 : Blo 794341 3026929 := bstep (se 2 (by rfl) ⟨1135098, by rfl⟩ : syracuseStep 3026929 = 2270197) B2270197
theorem B1191923 : Blo 794341 1191923 := bstep (se 1 (by rfl) ⟨893942, by rfl⟩ : syracuseStep 1191923 = 1787885) B1787885
theorem B2011139 : Blo 794341 2011139 := bstep (se 1 (by rfl) ⟨1508354, by rfl⟩ : syracuseStep 2011139 = 3016709) B3016709
theorem B5451781 : Blo 794341 5451781 := bstep (se 4 (by rfl) ⟨511104, by rfl⟩ : syracuseStep 5451781 = 1022209) B1022209
theorem B6467597 : Blo 794341 6467597 := bstep (se 3 (by rfl) ⟨1212674, by rfl⟩ : syracuseStep 6467597 = 2425349) B2425349
theorem B1191953 : Blo 794341 1191953 := bstep (se 2 (by rfl) ⟨446982, by rfl⟩ : syracuseStep 1191953 = 893965) B893965
theorem B897043 : Blo 794341 897043 := bstep (se 1 (by rfl) ⟨672782, by rfl⟩ : syracuseStep 897043 = 1345565) B1345565
theorem B1191971 : Blo 794341 1191971 := bstep (se 1 (by rfl) ⟨893978, by rfl⟩ : syracuseStep 1191971 = 1787957) B1787957
theorem B1192001 : Blo 794341 1192001 := bstep (se 2 (by rfl) ⟨447000, by rfl⟩ : syracuseStep 1192001 = 894001) B894001
theorem B1192019 : Blo 794341 1192019 := bstep (se 1 (by rfl) ⟨894014, by rfl⟩ : syracuseStep 1192019 = 1788029) B1788029
theorem B8400995 : Blo 794341 8400995 := bstep (se 1 (by rfl) ⟨6300746, by rfl⟩ : syracuseStep 8400995 = 12601493) B12601493
theorem B1192049 : Blo 794341 1192049 := bstep (se 2 (by rfl) ⟨447018, by rfl⟩ : syracuseStep 1192049 = 894037) B894037
theorem B1192067 : Blo 794341 1192067 := bstep (se 1 (by rfl) ⟨894050, by rfl⟩ : syracuseStep 1192067 = 1788101) B1788101
theorem B1192097 : Blo 794341 1192097 := bstep (se 2 (by rfl) ⟨447036, by rfl⟩ : syracuseStep 1192097 = 894073) B894073
theorem B897187 : Blo 794341 897187 := bstep (se 1 (by rfl) ⟨672890, by rfl⟩ : syracuseStep 897187 = 1345781) B1345781
theorem B1192115 : Blo 794341 1192115 := bstep (se 1 (by rfl) ⟨894086, by rfl⟩ : syracuseStep 1192115 = 1788173) B1788173
theorem B2011331 : Blo 794341 2011331 := bstep (se 1 (by rfl) ⟨1508498, by rfl⟩ : syracuseStep 2011331 = 3016997) B3016997
theorem B1192145 : Blo 794341 1192145 := bstep (se 2 (by rfl) ⟨447054, by rfl⟩ : syracuseStep 1192145 = 894109) B894109
theorem B1192163 : Blo 794341 1192163 := bstep (se 1 (by rfl) ⟨894122, by rfl⟩ : syracuseStep 1192163 = 1788245) B1788245
theorem B1224931 : Blo 794341 1224931 := bstep (se 1 (by rfl) ⟨918698, by rfl⟩ : syracuseStep 1224931 = 1837397) B1837397
theorem B1192193 : Blo 794341 1192193 := bstep (se 2 (by rfl) ⟨447072, by rfl⟩ : syracuseStep 1192193 = 894145) B894145
theorem B4534541 : Blo 794341 4534541 := bstep (se 3 (by rfl) ⟨850226, by rfl⟩ : syracuseStep 4534541 = 1700453) B1700453
theorem B1192211 : Blo 794341 1192211 := bstep (se 1 (by rfl) ⟨894158, by rfl⟩ : syracuseStep 1192211 = 1788317) B1788317
theorem B1192241 : Blo 794341 1192241 := bstep (se 2 (by rfl) ⟨447090, by rfl⟩ : syracuseStep 1192241 = 894181) B894181
theorem B897331 : Blo 794341 897331 := bstep (se 1 (by rfl) ⟨672998, by rfl⟩ : syracuseStep 897331 = 1345997) B1345997
theorem B1192259 : Blo 794341 1192259 := bstep (se 1 (by rfl) ⟨894194, by rfl⟩ : syracuseStep 1192259 = 1788389) B1788389
theorem B2765137 : Blo 794341 2765137 := bstep (se 2 (by rfl) ⟨1036926, by rfl⟩ : syracuseStep 2765137 = 2073853) B2073853
theorem B1192289 : Blo 794341 1192289 := bstep (se 2 (by rfl) ⟨447108, by rfl⟩ : syracuseStep 1192289 = 894217) B894217
theorem B1192307 : Blo 794341 1192307 := bstep (se 1 (by rfl) ⟨894230, by rfl⟩ : syracuseStep 1192307 = 1788461) B1788461
theorem B1290611 : Blo 794341 1290611 := bstep (se 1 (by rfl) ⟨967958, by rfl⟩ : syracuseStep 1290611 = 1935917) B1935917
theorem B1192337 : Blo 794341 1192337 := bstep (se 2 (by rfl) ⟨447126, by rfl⟩ : syracuseStep 1192337 = 894253) B894253
theorem B1192355 : Blo 794341 1192355 := bstep (se 1 (by rfl) ⟨894266, by rfl⟩ : syracuseStep 1192355 = 1788533) B1788533
theorem B1192385 : Blo 794341 1192385 := bstep (se 2 (by rfl) ⟨447144, by rfl⟩ : syracuseStep 1192385 = 894289) B894289
theorem B897475 : Blo 794341 897475 := bstep (se 1 (by rfl) ⟨673106, by rfl⟩ : syracuseStep 897475 = 1346213) B1346213
theorem B1192403 : Blo 794341 1192403 := bstep (se 1 (by rfl) ⟨894302, by rfl⟩ : syracuseStep 1192403 = 1788605) B1788605
theorem B1192433 : Blo 794341 1192433 := bstep (se 2 (by rfl) ⟨447162, by rfl⟩ : syracuseStep 1192433 = 894325) B894325
theorem B1192451 : Blo 794341 1192451 := bstep (se 1 (by rfl) ⟨894338, by rfl⟩ : syracuseStep 1192451 = 1788677) B1788677
theorem B1192481 : Blo 794341 1192481 := bstep (se 2 (by rfl) ⟨447180, by rfl⟩ : syracuseStep 1192481 = 894361) B894361
theorem B1192499 : Blo 794341 1192499 := bstep (se 1 (by rfl) ⟨894374, by rfl⟩ : syracuseStep 1192499 = 1788749) B1788749
theorem B1192529 : Blo 794341 1192529 := bstep (se 2 (by rfl) ⟨447198, by rfl⟩ : syracuseStep 1192529 = 894397) B894397
theorem B897619 : Blo 794341 897619 := bstep (se 1 (by rfl) ⟨673214, by rfl⟩ : syracuseStep 897619 = 1346429) B1346429
theorem B1192547 : Blo 794341 1192547 := bstep (se 1 (by rfl) ⟨894410, by rfl⟩ : syracuseStep 1192547 = 1788821) B1788821
theorem B1192577 : Blo 794341 1192577 := bstep (se 2 (by rfl) ⟨447216, by rfl⟩ : syracuseStep 1192577 = 894433) B894433
theorem B1192595 : Blo 794341 1192595 := bstep (se 1 (by rfl) ⟨894446, by rfl⟩ : syracuseStep 1192595 = 1788893) B1788893
theorem B1192625 : Blo 794341 1192625 := bstep (se 2 (by rfl) ⟨447234, by rfl⟩ : syracuseStep 1192625 = 894469) B894469
theorem B1192643 : Blo 794341 1192643 := bstep (se 1 (by rfl) ⟨894482, by rfl⟩ : syracuseStep 1192643 = 1788965) B1788965
theorem B1192673 : Blo 794341 1192673 := bstep (se 2 (by rfl) ⟨447252, by rfl⟩ : syracuseStep 1192673 = 894505) B894505
theorem B897763 : Blo 794341 897763 := bstep (se 1 (by rfl) ⟨673322, by rfl⟩ : syracuseStep 897763 = 1346645) B1346645
theorem B1192691 : Blo 794341 1192691 := bstep (se 1 (by rfl) ⟨894518, by rfl⟩ : syracuseStep 1192691 = 1789037) B1789037
theorem B1192721 : Blo 794341 1192721 := bstep (se 2 (by rfl) ⟨447270, by rfl⟩ : syracuseStep 1192721 = 894541) B894541
theorem B1192739 : Blo 794341 1192739 := bstep (se 1 (by rfl) ⟨894554, by rfl⟩ : syracuseStep 1192739 = 1789109) B1789109
theorem B1192769 : Blo 794341 1192769 := bstep (se 2 (by rfl) ⟨447288, by rfl⟩ : syracuseStep 1192769 = 894577) B894577
theorem B2044739 : Blo 794341 2044739 := bstep (se 1 (by rfl) ⟨1533554, by rfl⟩ : syracuseStep 2044739 = 3067109) B3067109
theorem B6042437 : Blo 794341 6042437 := bstep (se 4 (by rfl) ⟨566478, by rfl⟩ : syracuseStep 6042437 = 1132957) B1132957
theorem B1192787 : Blo 794341 1192787 := bstep (se 1 (by rfl) ⟨894590, by rfl⟩ : syracuseStep 1192787 = 1789181) B1789181
theorem B1192817 : Blo 794341 1192817 := bstep (se 2 (by rfl) ⟨447306, by rfl⟩ : syracuseStep 1192817 = 894613) B894613
theorem B897907 : Blo 794341 897907 := bstep (se 1 (by rfl) ⟨673430, by rfl⟩ : syracuseStep 897907 = 1346861) B1346861
theorem B1192835 : Blo 794341 1192835 := bstep (se 1 (by rfl) ⟨894626, by rfl⟩ : syracuseStep 1192835 = 1789253) B1789253
theorem B1192865 : Blo 794341 1192865 := bstep (se 2 (by rfl) ⟨447324, by rfl⟩ : syracuseStep 1192865 = 894649) B894649
theorem B1192883 : Blo 794341 1192883 := bstep (se 1 (by rfl) ⟨894662, by rfl⟩ : syracuseStep 1192883 = 1789325) B1789325
theorem B1192913 : Blo 794341 1192913 := bstep (se 2 (by rfl) ⟨447342, by rfl⟩ : syracuseStep 1192913 = 894685) B894685
theorem B1192931 : Blo 794341 1192931 := bstep (se 1 (by rfl) ⟨894698, by rfl⟩ : syracuseStep 1192931 = 1789397) B1789397
theorem B1913827 : Blo 794341 1913827 := bstep (se 1 (by rfl) ⟨1435370, by rfl⟩ : syracuseStep 1913827 = 2870741) B2870741
theorem B1192961 : Blo 794341 1192961 := bstep (se 2 (by rfl) ⟨447360, by rfl⟩ : syracuseStep 1192961 = 894721) B894721
theorem B898051 : Blo 794341 898051 := bstep (se 1 (by rfl) ⟨673538, by rfl⟩ : syracuseStep 898051 = 1347077) B1347077
theorem B1192979 : Blo 794341 1192979 := bstep (se 1 (by rfl) ⟨894734, by rfl⟩ : syracuseStep 1192979 = 1789469) B1789469
theorem B1193009 : Blo 794341 1193009 := bstep (se 2 (by rfl) ⟨447378, by rfl⟩ : syracuseStep 1193009 = 894757) B894757
theorem B1193027 : Blo 794341 1193027 := bstep (se 1 (by rfl) ⟨894770, by rfl⟩ : syracuseStep 1193027 = 1789541) B1789541
theorem B1193057 : Blo 794341 1193057 := bstep (se 2 (by rfl) ⟨447396, by rfl⟩ : syracuseStep 1193057 = 894793) B894793
theorem B2012273 : Blo 794341 2012273 := bstep (se 2 (by rfl) ⟨754602, by rfl⟩ : syracuseStep 2012273 = 1509205) B1509205
theorem B1193075 : Blo 794341 1193075 := bstep (se 1 (by rfl) ⟨894806, by rfl⟩ : syracuseStep 1193075 = 1789613) B1789613
theorem B1193105 : Blo 794341 1193105 := bstep (se 2 (by rfl) ⟨447414, by rfl⟩ : syracuseStep 1193105 = 894829) B894829
theorem B2012323 : Blo 794341 2012323 := bstep (se 1 (by rfl) ⟨1509242, by rfl⟩ : syracuseStep 2012323 = 3018485) B3018485
theorem B1193123 : Blo 794341 1193123 := bstep (se 1 (by rfl) ⟨894842, by rfl⟩ : syracuseStep 1193123 = 1789685) B1789685
theorem B4535473 : Blo 794341 4535473 := bstep (se 2 (by rfl) ⟨1700802, by rfl⟩ : syracuseStep 4535473 = 3401605) B3401605
theorem B1193153 : Blo 794341 1193153 := bstep (se 2 (by rfl) ⟨447432, by rfl⟩ : syracuseStep 1193153 = 894865) B894865
theorem B1193171 : Blo 794341 1193171 := bstep (se 1 (by rfl) ⟨894878, by rfl⟩ : syracuseStep 1193171 = 1789757) B1789757
theorem B931043 : Blo 794341 931043 := bstep (se 1 (by rfl) ⟨698282, by rfl⟩ : syracuseStep 931043 = 1396565) B1396565
theorem B1193201 : Blo 794341 1193201 := bstep (se 2 (by rfl) ⟨447450, by rfl⟩ : syracuseStep 1193201 = 894901) B894901
theorem B1193219 : Blo 794341 1193219 := bstep (se 1 (by rfl) ⟨894914, by rfl⟩ : syracuseStep 1193219 = 1789829) B1789829
theorem B1193249 : Blo 794341 1193249 := bstep (se 2 (by rfl) ⟨447468, by rfl⟩ : syracuseStep 1193249 = 894937) B894937
theorem B2012465 : Blo 794341 2012465 := bstep (se 2 (by rfl) ⟨754674, by rfl⟩ : syracuseStep 2012465 = 1509349) B1509349
theorem B1193267 : Blo 794341 1193267 := bstep (se 1 (by rfl) ⟨894950, by rfl⟩ : syracuseStep 1193267 = 1789901) B1789901
theorem B1193297 : Blo 794341 1193297 := bstep (se 2 (by rfl) ⟨447486, by rfl⟩ : syracuseStep 1193297 = 894973) B894973
theorem B1193315 : Blo 794341 1193315 := bstep (se 1 (by rfl) ⟨894986, by rfl⟩ : syracuseStep 1193315 = 1789973) B1789973
theorem B1193345 : Blo 794341 1193345 := bstep (se 2 (by rfl) ⟨447504, by rfl⟩ : syracuseStep 1193345 = 895009) B895009
theorem B1193363 : Blo 794341 1193363 := bstep (se 1 (by rfl) ⟨895022, by rfl⟩ : syracuseStep 1193363 = 1790045) B1790045
theorem B3028387 : Blo 794341 3028387 := bstep (se 1 (by rfl) ⟨2271290, by rfl⟩ : syracuseStep 3028387 = 4542581) B4542581
theorem B1193393 : Blo 794341 1193393 := bstep (se 2 (by rfl) ⟨447522, by rfl⟩ : syracuseStep 1193393 = 895045) B895045
theorem B1193411 : Blo 794341 1193411 := bstep (se 1 (by rfl) ⟨895058, by rfl⟩ : syracuseStep 1193411 = 1790117) B1790117
theorem B1193441 : Blo 794341 1193441 := bstep (se 2 (by rfl) ⟨447540, by rfl⟩ : syracuseStep 1193441 = 895081) B895081
theorem B15316451 : Blo 794341 15316451 := bstep (se 1 (by rfl) ⟨11487338, by rfl⟩ : syracuseStep 15316451 = 22974677) B22974677
theorem B1193459 : Blo 794341 1193459 := bstep (se 1 (by rfl) ⟨895094, by rfl⟩ : syracuseStep 1193459 = 1790189) B1790189
theorem B1193489 : Blo 794341 1193489 := bstep (se 2 (by rfl) ⟨447558, by rfl⟩ : syracuseStep 1193489 = 895117) B895117
theorem B1193507 : Blo 794341 1193507 := bstep (se 1 (by rfl) ⟨895130, by rfl⟩ : syracuseStep 1193507 = 1790261) B1790261
theorem B1226305 : Blo 794341 1226305 := bstep (se 2 (by rfl) ⟨459864, by rfl⟩ : syracuseStep 1226305 = 919729) B919729
theorem B1193537 : Blo 794341 1193537 := bstep (se 2 (by rfl) ⟨447576, by rfl⟩ : syracuseStep 1193537 = 895153) B895153
theorem B9090629 : Blo 794341 9090629 := bstep (se 4 (by rfl) ⟨852246, by rfl⟩ : syracuseStep 9090629 = 1704493) B1704493
theorem B1193555 : Blo 794341 1193555 := bstep (se 1 (by rfl) ⟨895166, by rfl⟩ : syracuseStep 1193555 = 1790333) B1790333
theorem B1193585 : Blo 794341 1193585 := bstep (se 2 (by rfl) ⟨447594, by rfl⟩ : syracuseStep 1193585 = 895189) B895189
theorem B1193603 : Blo 794341 1193603 := bstep (se 1 (by rfl) ⟨895202, by rfl⟩ : syracuseStep 1193603 = 1790405) B1790405
theorem B1193633 : Blo 794341 1193633 := bstep (se 2 (by rfl) ⟨447612, by rfl⟩ : syracuseStep 1193633 = 895225) B895225
theorem B1193651 : Blo 794341 1193651 := bstep (se 1 (by rfl) ⟨895238, by rfl⟩ : syracuseStep 1193651 = 1790477) B1790477
theorem B1193681 : Blo 794341 1193681 := bstep (se 2 (by rfl) ⟨447630, by rfl⟩ : syracuseStep 1193681 = 895261) B895261
theorem B1193699 : Blo 794341 1193699 := bstep (se 1 (by rfl) ⟨895274, by rfl⟩ : syracuseStep 1193699 = 1790549) B1790549
theorem B3061489 : Blo 794341 3061489 := bstep (se 2 (by rfl) ⟨1148058, by rfl⟩ : syracuseStep 3061489 = 2296117) B2296117
theorem B4601585 : Blo 794341 4601585 := bstep (se 2 (by rfl) ⟨1725594, by rfl⟩ : syracuseStep 4601585 = 3451189) B3451189
theorem B1193729 : Blo 794341 1193729 := bstep (se 2 (by rfl) ⟨447648, by rfl⟩ : syracuseStep 1193729 = 895297) B895297
theorem B1193747 : Blo 794341 1193747 := bstep (se 1 (by rfl) ⟨895310, by rfl⟩ : syracuseStep 1193747 = 1790621) B1790621
theorem B1193777 : Blo 794341 1193777 := bstep (se 2 (by rfl) ⟨447666, by rfl⟩ : syracuseStep 1193777 = 895333) B895333
theorem B1914673 : Blo 794341 1914673 := bstep (se 2 (by rfl) ⟨718002, by rfl⟩ : syracuseStep 1914673 = 1436005) B1436005
theorem B1193795 : Blo 794341 1193795 := bstep (se 1 (by rfl) ⟨895346, by rfl⟩ : syracuseStep 1193795 = 1790693) B1790693
theorem B1193825 : Blo 794341 1193825 := bstep (se 2 (by rfl) ⟨447684, by rfl⟩ : syracuseStep 1193825 = 895369) B895369
theorem B1193843 : Blo 794341 1193843 := bstep (se 1 (by rfl) ⟨895382, by rfl⟩ : syracuseStep 1193843 = 1790765) B1790765
theorem B1193873 : Blo 794341 1193873 := bstep (se 2 (by rfl) ⟨447702, by rfl⟩ : syracuseStep 1193873 = 895405) B895405
theorem B1193891 : Blo 794341 1193891 := bstep (se 1 (by rfl) ⟨895418, by rfl⟩ : syracuseStep 1193891 = 1790837) B1790837
theorem B1914787 : Blo 794341 1914787 := bstep (se 1 (by rfl) ⟨1436090, by rfl⟩ : syracuseStep 1914787 = 2872181) B2872181
theorem B1193921 : Blo 794341 1193921 := bstep (se 2 (by rfl) ⟨447720, by rfl⟩ : syracuseStep 1193921 = 895441) B895441
theorem B1193939 : Blo 794341 1193939 := bstep (se 1 (by rfl) ⟨895454, by rfl⟩ : syracuseStep 1193939 = 1790909) B1790909
theorem B1193969 : Blo 794341 1193969 := bstep (se 2 (by rfl) ⟨447738, by rfl⟩ : syracuseStep 1193969 = 895477) B895477
theorem B1193987 : Blo 794341 1193987 := bstep (se 1 (by rfl) ⟨895490, by rfl⟩ : syracuseStep 1193987 = 1790981) B1790981
theorem B1194017 : Blo 794341 1194017 := bstep (se 2 (by rfl) ⟨447756, by rfl⟩ : syracuseStep 1194017 = 895513) B895513
theorem B1194035 : Blo 794341 1194035 := bstep (se 1 (by rfl) ⟨895526, by rfl⟩ : syracuseStep 1194035 = 1791053) B1791053
theorem B1194065 : Blo 794341 1194065 := bstep (se 2 (by rfl) ⟨447774, by rfl⟩ : syracuseStep 1194065 = 895549) B895549
theorem B1194083 : Blo 794341 1194083 := bstep (se 1 (by rfl) ⟨895562, by rfl⟩ : syracuseStep 1194083 = 1791125) B1791125
theorem B1194113 : Blo 794341 1194113 := bstep (se 2 (by rfl) ⟨447792, by rfl⟩ : syracuseStep 1194113 = 895585) B895585
theorem B1194131 : Blo 794341 1194131 := bstep (se 1 (by rfl) ⟨895598, by rfl⟩ : syracuseStep 1194131 = 1791197) B1791197
theorem B1194161 : Blo 794341 1194161 := bstep (se 2 (by rfl) ⟨447810, by rfl⟩ : syracuseStep 1194161 = 895621) B895621
theorem B1194179 : Blo 794341 1194179 := bstep (se 1 (by rfl) ⟨895634, by rfl⟩ : syracuseStep 1194179 = 1791269) B1791269
theorem B1194209 : Blo 794341 1194209 := bstep (se 2 (by rfl) ⟨447828, by rfl⟩ : syracuseStep 1194209 = 895657) B895657
theorem B1194227 : Blo 794341 1194227 := bstep (se 1 (by rfl) ⟨895670, by rfl⟩ : syracuseStep 1194227 = 1791341) B1791341
theorem B2013457 : Blo 794341 2013457 := bstep (se 2 (by rfl) ⟨755046, by rfl⟩ : syracuseStep 2013457 = 1510093) B1510093
theorem B1194257 : Blo 794341 1194257 := bstep (se 2 (by rfl) ⟨447846, by rfl⟩ : syracuseStep 1194257 = 895693) B895693
theorem B1194275 : Blo 794341 1194275 := bstep (se 1 (by rfl) ⟨895706, by rfl⟩ : syracuseStep 1194275 = 1791413) B1791413
theorem B1194305 : Blo 794341 1194305 := bstep (se 2 (by rfl) ⟨447864, by rfl⟩ : syracuseStep 1194305 = 895729) B895729
theorem B1194323 : Blo 794341 1194323 := bstep (se 1 (by rfl) ⟨895742, by rfl⟩ : syracuseStep 1194323 = 1791485) B1791485
theorem B1194353 : Blo 794341 1194353 := bstep (se 2 (by rfl) ⟨447882, by rfl⟩ : syracuseStep 1194353 = 895765) B895765
theorem B1194371 : Blo 794341 1194371 := bstep (se 1 (by rfl) ⟨895778, by rfl⟩ : syracuseStep 1194371 = 1791557) B1791557
theorem B1194401 : Blo 794341 1194401 := bstep (se 2 (by rfl) ⟨447900, by rfl⟩ : syracuseStep 1194401 = 895801) B895801
theorem B1194419 : Blo 794341 1194419 := bstep (se 1 (by rfl) ⟨895814, by rfl⟩ : syracuseStep 1194419 = 1791629) B1791629
theorem B1194449 : Blo 794341 1194449 := bstep (se 2 (by rfl) ⟨447918, by rfl⟩ : syracuseStep 1194449 = 895837) B895837
theorem B1194467 : Blo 794341 1194467 := bstep (se 1 (by rfl) ⟨895850, by rfl⟩ : syracuseStep 1194467 = 1791701) B1791701
theorem B1194497 : Blo 794341 1194497 := bstep (se 2 (by rfl) ⟨447936, by rfl⟩ : syracuseStep 1194497 = 895873) B895873
theorem B2243089 : Blo 794341 2243089 := bstep (se 2 (by rfl) ⟨841158, by rfl⟩ : syracuseStep 2243089 = 1682317) B1682317
theorem B1194515 : Blo 794341 1194515 := bstep (se 1 (by rfl) ⟨895886, by rfl⟩ : syracuseStep 1194515 = 1791773) B1791773
theorem B2013731 : Blo 794341 2013731 := bstep (se 1 (by rfl) ⟨1510298, by rfl⟩ : syracuseStep 2013731 = 3020597) B3020597
theorem B1194545 : Blo 794341 1194545 := bstep (se 2 (by rfl) ⟨447954, by rfl⟩ : syracuseStep 1194545 = 895909) B895909
theorem B1194563 : Blo 794341 1194563 := bstep (se 1 (by rfl) ⟨895922, by rfl⟩ : syracuseStep 1194563 = 1791845) B1791845
theorem B1194593 : Blo 794341 1194593 := bstep (se 2 (by rfl) ⟨447972, by rfl⟩ : syracuseStep 1194593 = 895945) B895945
theorem B4536931 : Blo 794341 4536931 := bstep (se 1 (by rfl) ⟨3402698, by rfl⟩ : syracuseStep 4536931 = 6805397) B6805397
theorem B1194611 : Blo 794341 1194611 := bstep (se 1 (by rfl) ⟨895958, by rfl⟩ : syracuseStep 1194611 = 1791917) B1791917
theorem B1194641 : Blo 794341 1194641 := bstep (se 2 (by rfl) ⟨447990, by rfl⟩ : syracuseStep 1194641 = 895981) B895981
theorem B1194659 : Blo 794341 1194659 := bstep (se 1 (by rfl) ⟨895994, by rfl⟩ : syracuseStep 1194659 = 1791989) B1791989
theorem B1194689 : Blo 794341 1194689 := bstep (se 2 (by rfl) ⟨448008, by rfl⟩ : syracuseStep 1194689 = 896017) B896017
theorem B1194707 : Blo 794341 1194707 := bstep (se 1 (by rfl) ⟨896030, by rfl⟩ : syracuseStep 1194707 = 1792061) B1792061
theorem B2013923 : Blo 794341 2013923 := bstep (se 1 (by rfl) ⟨1510442, by rfl⟩ : syracuseStep 2013923 = 3020885) B3020885
theorem B1194737 : Blo 794341 1194737 := bstep (se 2 (by rfl) ⟨448026, by rfl⟩ : syracuseStep 1194737 = 896053) B896053
theorem B1194755 : Blo 794341 1194755 := bstep (se 1 (by rfl) ⟨896066, by rfl⟩ : syracuseStep 1194755 = 1792133) B1792133
theorem B1194785 : Blo 794341 1194785 := bstep (se 2 (by rfl) ⟨448044, by rfl⟩ : syracuseStep 1194785 = 896089) B896089
theorem B1194803 : Blo 794341 1194803 := bstep (se 1 (by rfl) ⟨896102, by rfl⟩ : syracuseStep 1194803 = 1792205) B1792205
theorem B1260353 : Blo 794341 1260353 := bstep (se 2 (by rfl) ⟨472632, by rfl⟩ : syracuseStep 1260353 = 945265) B945265
theorem B1194833 : Blo 794341 1194833 := bstep (se 2 (by rfl) ⟨448062, by rfl⟩ : syracuseStep 1194833 = 896125) B896125
theorem B1194851 : Blo 794341 1194851 := bstep (se 1 (by rfl) ⟨896138, by rfl⟩ : syracuseStep 1194851 = 1792277) B1792277
theorem B1194881 : Blo 794341 1194881 := bstep (se 2 (by rfl) ⟨448080, by rfl⟩ : syracuseStep 1194881 = 896161) B896161
theorem B1194899 : Blo 794341 1194899 := bstep (se 1 (by rfl) ⟨896174, by rfl⟩ : syracuseStep 1194899 = 1792349) B1792349
theorem B1194929 : Blo 794341 1194929 := bstep (se 2 (by rfl) ⟨448098, by rfl⟩ : syracuseStep 1194929 = 896197) B896197
theorem B1194947 : Blo 794341 1194947 := bstep (se 1 (by rfl) ⟨896210, by rfl⟩ : syracuseStep 1194947 = 1792421) B1792421
theorem B1194977 : Blo 794341 1194977 := bstep (se 2 (by rfl) ⟨448116, by rfl⟩ : syracuseStep 1194977 = 896233) B896233
theorem B1194995 : Blo 794341 1194995 := bstep (se 1 (by rfl) ⟨896246, by rfl⟩ : syracuseStep 1194995 = 1792493) B1792493
theorem B5094413 : Blo 794341 5094413 := bstep (se 3 (by rfl) ⟨955202, by rfl⟩ : syracuseStep 5094413 = 1910405) B1910405
theorem B1195025 : Blo 794341 1195025 := bstep (se 2 (by rfl) ⟨448134, by rfl⟩ : syracuseStep 1195025 = 896269) B896269
theorem B1195043 : Blo 794341 1195043 := bstep (se 1 (by rfl) ⟨896282, by rfl⟩ : syracuseStep 1195043 = 1792565) B1792565
theorem B1195073 : Blo 794341 1195073 := bstep (se 2 (by rfl) ⟨448152, by rfl⟩ : syracuseStep 1195073 = 896305) B896305
theorem B1195091 : Blo 794341 1195091 := bstep (se 1 (by rfl) ⟨896318, by rfl⟩ : syracuseStep 1195091 = 1792637) B1792637
theorem B1358945 : Blo 794341 1358945 := bstep (se 2 (by rfl) ⟨509604, by rfl⟩ : syracuseStep 1358945 = 1019209) B1019209
theorem B4537457 : Blo 794341 4537457 := bstep (se 2 (by rfl) ⟨1701546, by rfl⟩ : syracuseStep 4537457 = 3403093) B3403093
theorem B1195121 : Blo 794341 1195121 := bstep (se 2 (by rfl) ⟨448170, by rfl⟩ : syracuseStep 1195121 = 896341) B896341
theorem B1916017 : Blo 794341 1916017 := bstep (se 2 (by rfl) ⟨718506, by rfl⟩ : syracuseStep 1916017 = 1437013) B1437013
theorem B1195139 : Blo 794341 1195139 := bstep (se 1 (by rfl) ⟨896354, by rfl⟩ : syracuseStep 1195139 = 1792709) B1792709
theorem B1195169 : Blo 794341 1195169 := bstep (se 2 (by rfl) ⟨448188, by rfl⟩ : syracuseStep 1195169 = 896377) B896377
theorem B1227953 : Blo 794341 1227953 := bstep (se 2 (by rfl) ⟨460482, by rfl⟩ : syracuseStep 1227953 = 920965) B920965
theorem B1195187 : Blo 794341 1195187 := bstep (se 1 (by rfl) ⟨896390, by rfl⟩ : syracuseStep 1195187 = 1792781) B1792781
theorem B1195217 : Blo 794341 1195217 := bstep (se 2 (by rfl) ⟨448206, by rfl⟩ : syracuseStep 1195217 = 896413) B896413
theorem B6798563 : Blo 794341 6798563 := bstep (se 1 (by rfl) ⟨5098922, by rfl⟩ : syracuseStep 6798563 = 10197845) B10197845
theorem B1195235 : Blo 794341 1195235 := bstep (se 1 (by rfl) ⟨896426, by rfl⟩ : syracuseStep 1195235 = 1792853) B1792853
theorem B1195265 : Blo 794341 1195265 := bstep (se 2 (by rfl) ⟨448224, by rfl⟩ : syracuseStep 1195265 = 896449) B896449
theorem B1195283 : Blo 794341 1195283 := bstep (se 1 (by rfl) ⟨896462, by rfl⟩ : syracuseStep 1195283 = 1792925) B1792925
theorem B1195313 : Blo 794341 1195313 := bstep (se 2 (by rfl) ⟨448242, by rfl⟩ : syracuseStep 1195313 = 896485) B896485
theorem B1195331 : Blo 794341 1195331 := bstep (se 1 (by rfl) ⟨896498, by rfl⟩ : syracuseStep 1195331 = 1792997) B1792997
theorem B1195361 : Blo 794341 1195361 := bstep (se 2 (by rfl) ⟨448260, by rfl⟩ : syracuseStep 1195361 = 896521) B896521
theorem B5750129 : Blo 794341 5750129 := bstep (se 2 (by rfl) ⟨2156298, by rfl⟩ : syracuseStep 5750129 = 4312597) B4312597
theorem B1195379 : Blo 794341 1195379 := bstep (se 1 (by rfl) ⟨896534, by rfl⟩ : syracuseStep 1195379 = 1793069) B1793069
theorem B1195409 : Blo 794341 1195409 := bstep (se 2 (by rfl) ⟨448278, by rfl⟩ : syracuseStep 1195409 = 896557) B896557
theorem B1195427 : Blo 794341 1195427 := bstep (se 1 (by rfl) ⟨896570, by rfl⟩ : syracuseStep 1195427 = 1793141) B1793141
theorem B1195457 : Blo 794341 1195457 := bstep (se 2 (by rfl) ⟨448296, by rfl⟩ : syracuseStep 1195457 = 896593) B896593
theorem B1195475 : Blo 794341 1195475 := bstep (se 1 (by rfl) ⟨896606, by rfl⟩ : syracuseStep 1195475 = 1793213) B1793213
theorem B1195505 : Blo 794341 1195505 := bstep (se 2 (by rfl) ⟨448314, by rfl⟩ : syracuseStep 1195505 = 896629) B896629
theorem B1195523 : Blo 794341 1195523 := bstep (se 1 (by rfl) ⟨896642, by rfl⟩ : syracuseStep 1195523 = 1793285) B1793285
theorem B1195553 : Blo 794341 1195553 := bstep (se 2 (by rfl) ⟨448332, by rfl⟩ : syracuseStep 1195553 = 896665) B896665
theorem B1195571 : Blo 794341 1195571 := bstep (se 1 (by rfl) ⟨896678, by rfl⟩ : syracuseStep 1195571 = 1793357) B1793357
theorem B27901493 : Blo 794341 27901493 := bstep (se 5 (by rfl) ⟨1307882, by rfl⟩ : syracuseStep 27901493 = 2615765) B2615765
theorem B3030605 : Blo 794341 3030605 := bstep (se 3 (by rfl) ⟨568238, by rfl⟩ : syracuseStep 3030605 = 1136477) B1136477
theorem B1195601 : Blo 794341 1195601 := bstep (se 2 (by rfl) ⟨448350, by rfl⟩ : syracuseStep 1195601 = 896701) B896701
theorem B1359443 : Blo 794341 1359443 := bstep (se 1 (by rfl) ⟨1019582, by rfl⟩ : syracuseStep 1359443 = 2039165) B2039165
theorem B1195619 : Blo 794341 1195619 := bstep (se 1 (by rfl) ⟨896714, by rfl⟩ : syracuseStep 1195619 = 1793429) B1793429
theorem B1195649 : Blo 794341 1195649 := bstep (se 2 (by rfl) ⟨448368, by rfl⟩ : syracuseStep 1195649 = 896737) B896737
theorem B2014865 : Blo 794341 2014865 := bstep (se 2 (by rfl) ⟨755574, by rfl⟩ : syracuseStep 2014865 = 1511149) B1511149
theorem B1195667 : Blo 794341 1195667 := bstep (se 1 (by rfl) ⟨896750, by rfl⟩ : syracuseStep 1195667 = 1793501) B1793501
theorem B1195697 : Blo 794341 1195697 := bstep (se 2 (by rfl) ⟨448386, by rfl⟩ : syracuseStep 1195697 = 896773) B896773
theorem B2014915 : Blo 794341 2014915 := bstep (se 1 (by rfl) ⟨1511186, by rfl⟩ : syracuseStep 2014915 = 3022373) B3022373
theorem B1195715 : Blo 794341 1195715 := bstep (se 1 (by rfl) ⟨896786, by rfl⟩ : syracuseStep 1195715 = 1793573) B1793573
theorem B1195745 : Blo 794341 1195745 := bstep (se 2 (by rfl) ⟨448404, by rfl⟩ : syracuseStep 1195745 = 896809) B896809
theorem B1195763 : Blo 794341 1195763 := bstep (se 1 (by rfl) ⟨896822, by rfl⟩ : syracuseStep 1195763 = 1793645) B1793645
theorem B1195793 : Blo 794341 1195793 := bstep (se 2 (by rfl) ⟨448422, by rfl⟩ : syracuseStep 1195793 = 896845) B896845
theorem B1195811 : Blo 794341 1195811 := bstep (se 1 (by rfl) ⟨896858, by rfl⟩ : syracuseStep 1195811 = 1793717) B1793717
theorem B1195841 : Blo 794341 1195841 := bstep (se 2 (by rfl) ⟨448440, by rfl⟩ : syracuseStep 1195841 = 896881) B896881
theorem B2015057 : Blo 794341 2015057 := bstep (se 2 (by rfl) ⟨755646, by rfl⟩ : syracuseStep 2015057 = 1511293) B1511293
theorem B1195859 : Blo 794341 1195859 := bstep (se 1 (by rfl) ⟨896894, by rfl⟩ : syracuseStep 1195859 = 1793789) B1793789
theorem B4308835 : Blo 794341 4308835 := bstep (se 1 (by rfl) ⟨3231626, by rfl⟩ : syracuseStep 4308835 = 6463253) B6463253
theorem B1195889 : Blo 794341 1195889 := bstep (se 2 (by rfl) ⟨448458, by rfl⟩ : syracuseStep 1195889 = 896917) B896917
theorem B1195907 : Blo 794341 1195907 := bstep (se 1 (by rfl) ⟨896930, by rfl⟩ : syracuseStep 1195907 = 1793861) B1793861
theorem B1195937 : Blo 794341 1195937 := bstep (se 2 (by rfl) ⟨448476, by rfl⟩ : syracuseStep 1195937 = 896953) B896953
theorem B1195955 : Blo 794341 1195955 := bstep (se 1 (by rfl) ⟨896966, by rfl⟩ : syracuseStep 1195955 = 1793933) B1793933
theorem B1195985 : Blo 794341 1195985 := bstep (se 2 (by rfl) ⟨448494, by rfl⟩ : syracuseStep 1195985 = 896989) B896989
theorem B1196003 : Blo 794341 1196003 := bstep (se 1 (by rfl) ⟨897002, by rfl⟩ : syracuseStep 1196003 = 1794005) B1794005
theorem B1196033 : Blo 794341 1196033 := bstep (se 2 (by rfl) ⟨448512, by rfl⟩ : syracuseStep 1196033 = 897025) B897025
theorem B1196051 : Blo 794341 1196051 := bstep (se 1 (by rfl) ⟨897038, by rfl⟩ : syracuseStep 1196051 = 1794077) B1794077
theorem B1196081 : Blo 794341 1196081 := bstep (se 2 (by rfl) ⟨448530, by rfl⟩ : syracuseStep 1196081 = 897061) B897061
theorem B1196099 : Blo 794341 1196099 := bstep (se 1 (by rfl) ⟨897074, by rfl⟩ : syracuseStep 1196099 = 1794149) B1794149
theorem B1196129 : Blo 794341 1196129 := bstep (se 2 (by rfl) ⟨448548, by rfl⟩ : syracuseStep 1196129 = 897097) B897097
theorem B1196147 : Blo 794341 1196147 := bstep (se 1 (by rfl) ⟨897110, by rfl⟩ : syracuseStep 1196147 = 1794221) B1794221
theorem B1196177 : Blo 794341 1196177 := bstep (se 2 (by rfl) ⟨448566, by rfl⟩ : syracuseStep 1196177 = 897133) B897133
theorem B1196195 : Blo 794341 1196195 := bstep (se 1 (by rfl) ⟨897146, by rfl⟩ : syracuseStep 1196195 = 1794293) B1794293
theorem B1196225 : Blo 794341 1196225 := bstep (se 2 (by rfl) ⟨448584, by rfl⟩ : syracuseStep 1196225 = 897169) B897169
theorem B1196243 : Blo 794341 1196243 := bstep (se 1 (by rfl) ⟨897182, by rfl⟩ : syracuseStep 1196243 = 1794365) B1794365
theorem B1196273 : Blo 794341 1196273 := bstep (se 2 (by rfl) ⟨448602, by rfl⟩ : syracuseStep 1196273 = 897205) B897205
theorem B1196291 : Blo 794341 1196291 := bstep (se 1 (by rfl) ⟨897218, by rfl⟩ : syracuseStep 1196291 = 1794437) B1794437
theorem B5161229 : Blo 794341 5161229 := bstep (se 3 (by rfl) ⟨967730, by rfl⟩ : syracuseStep 5161229 = 1935461) B1935461
theorem B1196321 : Blo 794341 1196321 := bstep (se 2 (by rfl) ⟨448620, by rfl⟩ : syracuseStep 1196321 = 897241) B897241
theorem B1196339 : Blo 794341 1196339 := bstep (se 1 (by rfl) ⟨897254, by rfl⟩ : syracuseStep 1196339 = 1794509) B1794509
theorem B1196369 : Blo 794341 1196369 := bstep (se 2 (by rfl) ⟨448638, by rfl⟩ : syracuseStep 1196369 = 897277) B897277
theorem B1196387 : Blo 794341 1196387 := bstep (se 1 (by rfl) ⟨897290, by rfl⟩ : syracuseStep 1196387 = 1794581) B1794581
theorem B1196417 : Blo 794341 1196417 := bstep (se 2 (by rfl) ⟨448656, by rfl⟩ : syracuseStep 1196417 = 897313) B897313
theorem B1196435 : Blo 794341 1196435 := bstep (se 1 (by rfl) ⟨897326, by rfl⟩ : syracuseStep 1196435 = 1794653) B1794653
theorem B1196465 : Blo 794341 1196465 := bstep (se 2 (by rfl) ⟨448674, by rfl⟩ : syracuseStep 1196465 = 897349) B897349
theorem B1196483 : Blo 794341 1196483 := bstep (se 1 (by rfl) ⟨897362, by rfl⟩ : syracuseStep 1196483 = 1794725) B1794725
theorem B1196513 : Blo 794341 1196513 := bstep (se 2 (by rfl) ⟨448692, by rfl⟩ : syracuseStep 1196513 = 897385) B897385
theorem B1196531 : Blo 794341 1196531 := bstep (se 1 (by rfl) ⟨897398, by rfl⟩ : syracuseStep 1196531 = 1794797) B1794797
theorem B1196561 : Blo 794341 1196561 := bstep (se 2 (by rfl) ⟨448710, by rfl⟩ : syracuseStep 1196561 = 897421) B897421
theorem B4538915 : Blo 794341 4538915 := bstep (se 1 (by rfl) ⟨3404186, by rfl⟩ : syracuseStep 4538915 = 6808373) B6808373
theorem B1196579 : Blo 794341 1196579 := bstep (se 1 (by rfl) ⟨897434, by rfl⟩ : syracuseStep 1196579 = 1794869) B1794869
theorem B1196609 : Blo 794341 1196609 := bstep (se 2 (by rfl) ⟨448728, by rfl⟩ : syracuseStep 1196609 = 897457) B897457
theorem B1131089 : Blo 794341 1131089 := bstep (se 2 (by rfl) ⟨424158, by rfl⟩ : syracuseStep 1131089 = 848317) B848317
theorem B1196627 : Blo 794341 1196627 := bstep (se 1 (by rfl) ⟨897470, by rfl⟩ : syracuseStep 1196627 = 1794941) B1794941
theorem B1196657 : Blo 794341 1196657 := bstep (se 2 (by rfl) ⟨448746, by rfl⟩ : syracuseStep 1196657 = 897493) B897493
theorem B1196675 : Blo 794341 1196675 := bstep (se 1 (by rfl) ⟨897506, by rfl⟩ : syracuseStep 1196675 = 1795013) B1795013
theorem B1196705 : Blo 794341 1196705 := bstep (se 2 (by rfl) ⟨448764, by rfl⟩ : syracuseStep 1196705 = 897529) B897529
theorem B1196723 : Blo 794341 1196723 := bstep (se 1 (by rfl) ⟨897542, by rfl⟩ : syracuseStep 1196723 = 1795085) B1795085
theorem B1131203 : Blo 794341 1131203 := bstep (se 1 (by rfl) ⟨848402, by rfl⟩ : syracuseStep 1131203 = 1696805) B1696805
theorem B1196753 : Blo 794341 1196753 := bstep (se 2 (by rfl) ⟨448782, by rfl⟩ : syracuseStep 1196753 = 897565) B897565
theorem B1196771 : Blo 794341 1196771 := bstep (se 1 (by rfl) ⟨897578, by rfl⟩ : syracuseStep 1196771 = 1795157) B1795157
theorem B1196801 : Blo 794341 1196801 := bstep (se 2 (by rfl) ⟨448800, by rfl⟩ : syracuseStep 1196801 = 897601) B897601
theorem B1131283 : Blo 794341 1131283 := bstep (se 1 (by rfl) ⟨848462, by rfl⟩ : syracuseStep 1131283 = 1696925) B1696925
theorem B1196819 : Blo 794341 1196819 := bstep (se 1 (by rfl) ⟨897614, by rfl⟩ : syracuseStep 1196819 = 1795229) B1795229
theorem B2016049 : Blo 794341 2016049 := bstep (se 2 (by rfl) ⟨756018, by rfl⟩ : syracuseStep 2016049 = 1512037) B1512037
theorem B1196849 : Blo 794341 1196849 := bstep (se 2 (by rfl) ⟨448818, by rfl⟩ : syracuseStep 1196849 = 897637) B897637
theorem B1196867 : Blo 794341 1196867 := bstep (se 1 (by rfl) ⟨897650, by rfl⟩ : syracuseStep 1196867 = 1795301) B1795301
theorem B1196897 : Blo 794341 1196897 := bstep (se 2 (by rfl) ⟨448836, by rfl⟩ : syracuseStep 1196897 = 897673) B897673
theorem B1196915 : Blo 794341 1196915 := bstep (se 1 (by rfl) ⟨897686, by rfl⟩ : syracuseStep 1196915 = 1795373) B1795373
theorem B1196945 : Blo 794341 1196945 := bstep (se 2 (by rfl) ⟨448854, by rfl⟩ : syracuseStep 1196945 = 897709) B897709
theorem B1196963 : Blo 794341 1196963 := bstep (se 1 (by rfl) ⟨897722, by rfl⟩ : syracuseStep 1196963 = 1795445) B1795445
theorem B1196993 : Blo 794341 1196993 := bstep (se 2 (by rfl) ⟨448872, by rfl⟩ : syracuseStep 1196993 = 897745) B897745
theorem B1197011 : Blo 794341 1197011 := bstep (se 1 (by rfl) ⟨897758, by rfl⟩ : syracuseStep 1197011 = 1795517) B1795517
theorem B1197041 : Blo 794341 1197041 := bstep (se 2 (by rfl) ⟨448890, by rfl⟩ : syracuseStep 1197041 = 897781) B897781
theorem B1197059 : Blo 794341 1197059 := bstep (se 1 (by rfl) ⟨897794, by rfl⟩ : syracuseStep 1197059 = 1795589) B1795589
theorem B1197089 : Blo 794341 1197089 := bstep (se 2 (by rfl) ⟨448908, by rfl⟩ : syracuseStep 1197089 = 897817) B897817
theorem B1197107 : Blo 794341 1197107 := bstep (se 1 (by rfl) ⟨897830, by rfl⟩ : syracuseStep 1197107 = 1795661) B1795661
theorem B2016323 : Blo 794341 2016323 := bstep (se 1 (by rfl) ⟨1512242, by rfl⟩ : syracuseStep 2016323 = 3024485) B3024485
theorem B1197137 : Blo 794341 1197137 := bstep (se 2 (by rfl) ⟨448926, by rfl⟩ : syracuseStep 1197137 = 897853) B897853
theorem B1197155 : Blo 794341 1197155 := bstep (se 1 (by rfl) ⟨897866, by rfl⟩ : syracuseStep 1197155 = 1795733) B1795733
theorem B1197185 : Blo 794341 1197185 := bstep (se 2 (by rfl) ⟨448944, by rfl⟩ : syracuseStep 1197185 = 897889) B897889
theorem B1197203 : Blo 794341 1197203 := bstep (se 1 (by rfl) ⟨897902, by rfl⟩ : syracuseStep 1197203 = 1795805) B1795805
theorem B1197233 : Blo 794341 1197233 := bstep (se 2 (by rfl) ⟨448962, by rfl⟩ : syracuseStep 1197233 = 897925) B897925
theorem B1197251 : Blo 794341 1197251 := bstep (se 1 (by rfl) ⟨897938, by rfl⟩ : syracuseStep 1197251 = 1795877) B1795877
theorem B46613717 : Blo 794341 46613717 := bstep (se 7 (by rfl) ⟨546254, by rfl⟩ : syracuseStep 46613717 = 1092509) B1092509
theorem B1197281 : Blo 794341 1197281 := bstep (se 2 (by rfl) ⟨448980, by rfl⟩ : syracuseStep 1197281 = 897961) B897961
theorem B1197299 : Blo 794341 1197299 := bstep (se 1 (by rfl) ⟨897974, by rfl⟩ : syracuseStep 1197299 = 1795949) B1795949
theorem B2016515 : Blo 794341 2016515 := bstep (se 1 (by rfl) ⟨1512386, by rfl⟩ : syracuseStep 2016515 = 3024773) B3024773
theorem B1197329 : Blo 794341 1197329 := bstep (se 2 (by rfl) ⟨448998, by rfl⟩ : syracuseStep 1197329 = 897997) B897997
theorem B1295651 : Blo 794341 1295651 := bstep (se 1 (by rfl) ⟨971738, by rfl⟩ : syracuseStep 1295651 = 1943477) B1943477
theorem B1197347 : Blo 794341 1197347 := bstep (se 1 (by rfl) ⟨898010, by rfl⟩ : syracuseStep 1197347 = 1796021) B1796021
theorem B1131841 : Blo 794341 1131841 := bstep (se 2 (by rfl) ⟨424440, by rfl⟩ : syracuseStep 1131841 = 848881) B848881
theorem B1197377 : Blo 794341 1197377 := bstep (se 2 (by rfl) ⟨449016, by rfl⟩ : syracuseStep 1197377 = 898033) B898033
theorem B1197395 : Blo 794341 1197395 := bstep (se 1 (by rfl) ⟨898046, by rfl⟩ : syracuseStep 1197395 = 1796093) B1796093
theorem B1197425 : Blo 794341 1197425 := bstep (se 2 (by rfl) ⟨449034, by rfl⟩ : syracuseStep 1197425 = 898069) B898069
theorem B1197443 : Blo 794341 1197443 := bstep (se 1 (by rfl) ⟨898082, by rfl⟩ : syracuseStep 1197443 = 1796165) B1796165
theorem B5752205 : Blo 794341 5752205 := bstep (se 3 (by rfl) ⟨1078538, by rfl⟩ : syracuseStep 5752205 = 2157077) B2157077
theorem B1197473 : Blo 794341 1197473 := bstep (se 2 (by rfl) ⟨449052, by rfl⟩ : syracuseStep 1197473 = 898105) B898105
theorem B1197491 : Blo 794341 1197491 := bstep (se 1 (by rfl) ⟨898118, by rfl⟩ : syracuseStep 1197491 = 1796237) B1796237
theorem B1787345 : Blo 794341 1787345 := bstep (se 2 (by rfl) ⟨670254, by rfl⟩ : syracuseStep 1787345 = 1340509) B1340509
theorem B1787363 : Blo 794341 1787363 := bstep (se 1 (by rfl) ⟨1340522, by rfl⟩ : syracuseStep 1787363 = 2681045) B2681045
theorem B1787633 : Blo 794341 1787633 := bstep (se 2 (by rfl) ⟨670362, by rfl⟩ : syracuseStep 1787633 = 1340725) B1340725
theorem B1787651 : Blo 794341 1787651 := bstep (se 1 (by rfl) ⟨1340738, by rfl⟩ : syracuseStep 1787651 = 2681477) B2681477
theorem B1132547 : Blo 794341 1132547 := bstep (se 1 (by rfl) ⟨849410, by rfl⟩ : syracuseStep 1132547 = 1698821) B1698821
theorem B1787921 : Blo 794341 1787921 := bstep (se 2 (by rfl) ⟨670470, by rfl⟩ : syracuseStep 1787921 = 1340941) B1340941
theorem B1787939 : Blo 794341 1787939 := bstep (se 1 (by rfl) ⟨1340954, by rfl⟩ : syracuseStep 1787939 = 2681909) B2681909
theorem B3393677 : Blo 794341 3393677 := bstep (se 3 (by rfl) ⟨636314, by rfl⟩ : syracuseStep 3393677 = 1272629) B1272629
theorem B2148515 : Blo 794341 2148515 := bstep (se 1 (by rfl) ⟨1611386, by rfl⟩ : syracuseStep 2148515 = 3222773) B3222773
theorem B2017457 : Blo 794341 2017457 := bstep (se 2 (by rfl) ⟨756546, by rfl⟩ : syracuseStep 2017457 = 1513093) B1513093
theorem B2017507 : Blo 794341 2017507 := bstep (se 1 (by rfl) ⟨1513130, by rfl⟩ : syracuseStep 2017507 = 3026261) B3026261
theorem B1788209 : Blo 794341 1788209 := bstep (se 2 (by rfl) ⟨670578, by rfl⟩ : syracuseStep 1788209 = 1341157) B1341157
theorem B1788227 : Blo 794341 1788227 := bstep (se 1 (by rfl) ⟨1341170, by rfl⟩ : syracuseStep 1788227 = 2682341) B2682341
theorem B2017649 : Blo 794341 2017649 := bstep (se 2 (by rfl) ⟨756618, by rfl⟩ : syracuseStep 2017649 = 1513237) B1513237
theorem B4540805 : Blo 794341 4540805 := bstep (se 4 (by rfl) ⟨425700, by rfl⟩ : syracuseStep 4540805 = 851401) B851401
theorem B4082147 : Blo 794341 4082147 := bstep (se 1 (by rfl) ⟨3061610, by rfl⟩ : syracuseStep 4082147 = 6123221) B6123221
theorem B17254883 : Blo 794341 17254883 := bstep (se 1 (by rfl) ⟨12941162, by rfl⟩ : syracuseStep 17254883 = 25882325) B25882325
theorem B6048269 : Blo 794341 6048269 := bstep (se 3 (by rfl) ⟨1134050, by rfl⟩ : syracuseStep 6048269 = 2268101) B2268101
theorem B3820081 : Blo 794341 3820081 := bstep (se 2 (by rfl) ⟨1432530, by rfl⟩ : syracuseStep 3820081 = 2865061) B2865061
theorem B1788497 : Blo 794341 1788497 := bstep (se 2 (by rfl) ⟨670686, by rfl⟩ : syracuseStep 1788497 = 1341373) B1341373
theorem B1788515 : Blo 794341 1788515 := bstep (se 1 (by rfl) ⟨1341386, by rfl⟩ : syracuseStep 1788515 = 2682773) B2682773
theorem B1133185 : Blo 794341 1133185 := bstep (se 2 (by rfl) ⟨424944, by rfl⟩ : syracuseStep 1133185 = 849889) B849889
theorem B1133299 : Blo 794341 1133299 := bstep (se 1 (by rfl) ⟨849974, by rfl⟩ : syracuseStep 1133299 = 1699949) B1699949
theorem B2149229 : Blo 794341 2149229 := bstep (se 3 (by rfl) ⟨402980, by rfl⟩ : syracuseStep 2149229 = 805961) B805961
theorem B1788785 : Blo 794341 1788785 := bstep (se 2 (by rfl) ⟨670794, by rfl⟩ : syracuseStep 1788785 = 1341589) B1341589
theorem B20663153 : Blo 794341 20663153 := bstep (se 2 (by rfl) ⟨7748682, by rfl⟩ : syracuseStep 20663153 = 15497365) B15497365
theorem B1788803 : Blo 794341 1788803 := bstep (se 1 (by rfl) ⟨1341602, by rfl⟩ : syracuseStep 1788803 = 2683205) B2683205
theorem B5098565 : Blo 794341 5098565 := bstep (se 4 (by rfl) ⟨477990, by rfl⟩ : syracuseStep 5098565 = 955981) B955981
theorem B1789073 : Blo 794341 1789073 := bstep (se 2 (by rfl) ⟨670902, by rfl⟩ : syracuseStep 1789073 = 1341805) B1341805
theorem B1789091 : Blo 794341 1789091 := bstep (se 1 (by rfl) ⟨1341818, by rfl⟩ : syracuseStep 1789091 = 2683637) B2683637
theorem B4836685 : Blo 794341 4836685 := bstep (se 3 (by rfl) ⟨906878, by rfl⟩ : syracuseStep 4836685 = 1813757) B1813757
theorem B2018641 : Blo 794341 2018641 := bstep (se 2 (by rfl) ⟨756990, by rfl⟩ : syracuseStep 2018641 = 1513981) B1513981
theorem B3231139 : Blo 794341 3231139 := bstep (se 1 (by rfl) ⟨2423354, by rfl⟩ : syracuseStep 3231139 = 4846709) B4846709
theorem B1789361 : Blo 794341 1789361 := bstep (se 2 (by rfl) ⟨671010, by rfl⟩ : syracuseStep 1789361 = 1342021) B1342021
theorem B1789379 : Blo 794341 1789379 := bstep (se 1 (by rfl) ⟨1342034, by rfl⟩ : syracuseStep 1789379 = 2684069) B2684069
theorem B2870797 : Blo 794341 2870797 := bstep (se 3 (by rfl) ⟨538274, by rfl⟩ : syracuseStep 2870797 = 1076549) B1076549
theorem B2018915 : Blo 794341 2018915 := bstep (se 1 (by rfl) ⟨1514186, by rfl⟩ : syracuseStep 2018915 = 3028373) B3028373
theorem B1789649 : Blo 794341 1789649 := bstep (se 2 (by rfl) ⟨671118, by rfl⟩ : syracuseStep 1789649 = 1342237) B1342237
theorem B1789667 : Blo 794341 1789667 := bstep (se 1 (by rfl) ⟨1342250, by rfl⟩ : syracuseStep 1789667 = 2684501) B2684501
theorem B2019107 : Blo 794341 2019107 := bstep (se 1 (by rfl) ⟨1514330, by rfl⟩ : syracuseStep 2019107 = 3028661) B3028661
theorem B1789937 : Blo 794341 1789937 := bstep (se 2 (by rfl) ⟨671226, by rfl⟩ : syracuseStep 1789937 = 1342453) B1342453
theorem B1789955 : Blo 794341 1789955 := bstep (se 1 (by rfl) ⟨1342466, by rfl⟩ : syracuseStep 1789955 = 2684933) B2684933
theorem B1134643 : Blo 794341 1134643 := bstep (se 1 (by rfl) ⟨850982, by rfl⟩ : syracuseStep 1134643 = 1701965) B1701965
theorem B1364035 : Blo 794341 1364035 := bstep (se 1 (by rfl) ⟨1023026, by rfl⟩ : syracuseStep 1364035 = 2046053) B2046053
theorem B4837637 : Blo 794341 4837637 := bstep (se 4 (by rfl) ⟨453528, by rfl⟩ : syracuseStep 4837637 = 907057) B907057
theorem B1790225 : Blo 794341 1790225 := bstep (se 2 (by rfl) ⟨671334, by rfl⟩ : syracuseStep 1790225 = 1342669) B1342669
theorem B1790243 : Blo 794341 1790243 := bstep (se 1 (by rfl) ⟨1342682, by rfl⟩ : syracuseStep 1790243 = 2685365) B2685365
theorem B1364369 : Blo 794341 1364369 := bstep (se 2 (by rfl) ⟨511638, by rfl⟩ : syracuseStep 1364369 = 1023277) B1023277
theorem B1790513 : Blo 794341 1790513 := bstep (se 2 (by rfl) ⟨671442, by rfl⟩ : syracuseStep 1790513 = 1342885) B1342885
theorem B1790531 : Blo 794341 1790531 := bstep (se 1 (by rfl) ⟨1342898, by rfl⟩ : syracuseStep 1790531 = 2685797) B2685797
theorem B2020049 : Blo 794341 2020049 := bstep (se 2 (by rfl) ⟨757518, by rfl⟩ : syracuseStep 2020049 = 1515037) B1515037
theorem B2020099 : Blo 794341 2020099 := bstep (se 1 (by rfl) ⟨1515074, by rfl⟩ : syracuseStep 2020099 = 3030149) B3030149
theorem B1790801 : Blo 794341 1790801 := bstep (se 2 (by rfl) ⟨671550, by rfl⟩ : syracuseStep 1790801 = 1343101) B1343101
theorem B1790819 : Blo 794341 1790819 := bstep (se 1 (by rfl) ⟨1343114, by rfl⟩ : syracuseStep 1790819 = 2686229) B2686229
theorem B2020241 : Blo 794341 2020241 := bstep (se 2 (by rfl) ⟨757590, by rfl⟩ : syracuseStep 2020241 = 1515181) B1515181
theorem B1791089 : Blo 794341 1791089 := bstep (se 2 (by rfl) ⟨671658, by rfl⟩ : syracuseStep 1791089 = 1343317) B1343317
theorem B1791107 : Blo 794341 1791107 := bstep (se 1 (by rfl) ⟨1343330, by rfl⟩ : syracuseStep 1791107 = 2686661) B2686661
theorem B1135777 : Blo 794341 1135777 := bstep (se 2 (by rfl) ⟨425916, by rfl⟩ : syracuseStep 1135777 = 851833) B851833
theorem B4150499 : Blo 794341 4150499 := bstep (se 1 (by rfl) ⟨3112874, by rfl⟩ : syracuseStep 4150499 = 6225749) B6225749
theorem B1135873 : Blo 794341 1135873 := bstep (se 2 (by rfl) ⟨425952, by rfl⟩ : syracuseStep 1135873 = 851905) B851905
theorem B6051185 : Blo 794341 6051185 := bstep (se 2 (by rfl) ⟨2269194, by rfl⟩ : syracuseStep 6051185 = 4538389) B4538389
theorem B1791377 : Blo 794341 1791377 := bstep (se 2 (by rfl) ⟨671766, by rfl⟩ : syracuseStep 1791377 = 1343533) B1343533
theorem B1791395 : Blo 794341 1791395 := bstep (se 1 (by rfl) ⟨1343546, by rfl⟩ : syracuseStep 1791395 = 2687093) B2687093
theorem B1791665 : Blo 794341 1791665 := bstep (se 2 (by rfl) ⟨671874, by rfl⟩ : syracuseStep 1791665 = 1343749) B1343749
theorem B1791683 : Blo 794341 1791683 := bstep (se 1 (by rfl) ⟨1343762, by rfl⟩ : syracuseStep 1791683 = 2687525) B2687525
theorem B2545361 : Blo 794341 2545361 := bstep (se 2 (by rfl) ⟨954510, by rfl⟩ : syracuseStep 2545361 = 1909021) B1909021
theorem B1136369 : Blo 794341 1136369 := bstep (se 2 (by rfl) ⟨426138, by rfl⟩ : syracuseStep 1136369 = 852277) B852277
theorem B1791953 : Blo 794341 1791953 := bstep (se 2 (by rfl) ⟨671982, by rfl⟩ : syracuseStep 1791953 = 1343965) B1343965
theorem B1791971 : Blo 794341 1791971 := bstep (se 1 (by rfl) ⟨1343978, by rfl⟩ : syracuseStep 1791971 = 2687957) B2687957
theorem B1005635 : Blo 794341 1005635 := bstep (se 1 (by rfl) ⟨754226, by rfl⟩ : syracuseStep 1005635 = 1508453) B1508453
theorem B4839587 : Blo 794341 4839587 := bstep (se 1 (by rfl) ⟨3629690, by rfl⟩ : syracuseStep 4839587 = 7259381) B7259381
theorem B1530083 : Blo 794341 1530083 := bstep (se 1 (by rfl) ⟨1147562, by rfl⟩ : syracuseStep 1530083 = 2295125) B2295125
theorem B2545901 : Blo 794341 2545901 := bstep (se 3 (by rfl) ⟨477356, by rfl⟩ : syracuseStep 2545901 = 954713) B954713
theorem B1792241 : Blo 794341 1792241 := bstep (se 2 (by rfl) ⟨672090, by rfl⟩ : syracuseStep 1792241 = 1344181) B1344181
theorem B1792259 : Blo 794341 1792259 := bstep (se 1 (by rfl) ⟨1344194, by rfl⟩ : syracuseStep 1792259 = 2688389) B2688389
theorem B11622797 : Blo 794341 11622797 := bstep (se 3 (by rfl) ⟨2179274, by rfl⟩ : syracuseStep 11622797 = 4358549) B4358549
theorem B3398051 : Blo 794341 3398051 := bstep (se 1 (by rfl) ⟨2548538, by rfl⟩ : syracuseStep 3398051 = 5097077) B5097077
theorem B1792529 : Blo 794341 1792529 := bstep (se 2 (by rfl) ⟨672198, by rfl⟩ : syracuseStep 1792529 = 1344397) B1344397
theorem B1792547 : Blo 794341 1792547 := bstep (se 1 (by rfl) ⟨1344410, by rfl⟩ : syracuseStep 1792547 = 2688821) B2688821
theorem B2873969 : Blo 794341 2873969 := bstep (se 2 (by rfl) ⟨1077738, by rfl⟩ : syracuseStep 2873969 = 2155477) B2155477
theorem B1006339 : Blo 794341 1006339 := bstep (se 1 (by rfl) ⟨754754, by rfl⟩ : syracuseStep 1006339 = 1509509) B1509509
theorem B1792817 : Blo 794341 1792817 := bstep (se 2 (by rfl) ⟨672306, by rfl⟩ : syracuseStep 1792817 = 1344613) B1344613
theorem B908083 : Blo 794341 908083 := bstep (se 1 (by rfl) ⟨681062, by rfl⟩ : syracuseStep 908083 = 1362125) B1362125
theorem B1792835 : Blo 794341 1792835 := bstep (se 1 (by rfl) ⟨1344626, by rfl⟩ : syracuseStep 1792835 = 2689253) B2689253
theorem B1006435 : Blo 794341 1006435 := bstep (se 1 (by rfl) ⟨754826, by rfl⟩ : syracuseStep 1006435 = 1509653) B1509653
theorem B1432451 : Blo 794341 1432451 := bstep (se 1 (by rfl) ⟨1074338, by rfl⟩ : syracuseStep 1432451 = 2148677) B2148677
theorem B5102513 : Blo 794341 5102513 := bstep (se 2 (by rfl) ⟨1913442, by rfl⟩ : syracuseStep 5102513 = 3826885) B3826885
theorem B3824653 : Blo 794341 3824653 := bstep (se 3 (by rfl) ⟨717122, by rfl⟩ : syracuseStep 3824653 = 1434245) B1434245
theorem B1793105 : Blo 794341 1793105 := bstep (se 2 (by rfl) ⟨672414, by rfl⟩ : syracuseStep 1793105 = 1344829) B1344829
theorem B1793123 : Blo 794341 1793123 := bstep (se 1 (by rfl) ⟨1344842, by rfl⟩ : syracuseStep 1793123 = 2689685) B2689685
theorem B1006931 : Blo 794341 1006931 := bstep (se 1 (by rfl) ⟨755198, by rfl⟩ : syracuseStep 1006931 = 1510397) B1510397
theorem B1793393 : Blo 794341 1793393 := bstep (se 2 (by rfl) ⟨672522, by rfl⟩ : syracuseStep 1793393 = 1345045) B1345045
theorem B1793411 : Blo 794341 1793411 := bstep (se 1 (by rfl) ⟨1345058, by rfl⟩ : syracuseStep 1793411 = 2690117) B2690117
theorem B1531345 : Blo 794341 1531345 := bstep (se 2 (by rfl) ⟨574254, by rfl⟩ : syracuseStep 1531345 = 1148509) B1148509
theorem B2448899 : Blo 794341 2448899 := bstep (se 1 (by rfl) ⟨1836674, by rfl⟩ : syracuseStep 2448899 = 3673349) B3673349
theorem B1793681 : Blo 794341 1793681 := bstep (se 2 (by rfl) ⟨672630, by rfl⟩ : syracuseStep 1793681 = 1345261) B1345261
theorem B1793699 : Blo 794341 1793699 := bstep (se 1 (by rfl) ⟨1345274, by rfl⟩ : syracuseStep 1793699 = 2690549) B2690549
theorem B2416483 : Blo 794341 2416483 := bstep (se 1 (by rfl) ⟨1812362, by rfl⟩ : syracuseStep 2416483 = 3624725) B3624725
theorem B1793969 : Blo 794341 1793969 := bstep (se 2 (by rfl) ⟨672738, by rfl⟩ : syracuseStep 1793969 = 1345477) B1345477
theorem B1793987 : Blo 794341 1793987 := bstep (se 1 (by rfl) ⟨1345490, by rfl⟩ : syracuseStep 1793987 = 2690981) B2690981
theorem B1007635 : Blo 794341 1007635 := bstep (se 1 (by rfl) ⟨755726, by rfl⟩ : syracuseStep 1007635 = 1511453) B1511453
theorem B4546637 : Blo 794341 4546637 := bstep (se 3 (by rfl) ⟨852494, by rfl⟩ : syracuseStep 4546637 = 1704989) B1704989
theorem B2547821 : Blo 794341 2547821 := bstep (se 3 (by rfl) ⟨477716, by rfl⟩ : syracuseStep 2547821 = 955433) B955433
theorem B1007731 : Blo 794341 1007731 := bstep (se 1 (by rfl) ⟨755798, by rfl⟩ : syracuseStep 1007731 = 1511597) B1511597
theorem B2154701 : Blo 794341 2154701 := bstep (se 3 (by rfl) ⟨404006, by rfl⟩ : syracuseStep 2154701 = 808013) B808013
theorem B1794257 : Blo 794341 1794257 := bstep (se 2 (by rfl) ⟨672846, by rfl⟩ : syracuseStep 1794257 = 1345693) B1345693
theorem B1794275 : Blo 794341 1794275 := bstep (se 1 (by rfl) ⟨1345706, by rfl⟩ : syracuseStep 1794275 = 2691413) B2691413
theorem B7659845 : Blo 794341 7659845 := bstep (se 4 (by rfl) ⟨718110, by rfl⟩ : syracuseStep 7659845 = 1436221) B1436221
theorem B1073587 : Blo 794341 1073587 := bstep (se 1 (by rfl) ⟨805190, by rfl⟩ : syracuseStep 1073587 = 1610381) B1610381
theorem B1794545 : Blo 794341 1794545 := bstep (se 2 (by rfl) ⟨672954, by rfl⟩ : syracuseStep 1794545 = 1345909) B1345909
theorem B1794563 : Blo 794341 1794563 := bstep (se 1 (by rfl) ⟨1345922, by rfl⟩ : syracuseStep 1794563 = 2691845) B2691845
theorem B1008227 : Blo 794341 1008227 := bstep (se 1 (by rfl) ⟨756170, by rfl⟩ : syracuseStep 1008227 = 1512341) B1512341
theorem B1401475 : Blo 794341 1401475 := bstep (se 1 (by rfl) ⟨1051106, by rfl⟩ : syracuseStep 1401475 = 2102213) B2102213
theorem B1794833 : Blo 794341 1794833 := bstep (se 2 (by rfl) ⟨673062, by rfl⟩ : syracuseStep 1794833 = 1346125) B1346125
theorem B1794851 : Blo 794341 1794851 := bstep (se 1 (by rfl) ⟨1346138, by rfl⟩ : syracuseStep 1794851 = 2692277) B2692277
theorem B910163 : Blo 794341 910163 := bstep (se 1 (by rfl) ⟨682622, by rfl⟩ : syracuseStep 910163 = 1365245) B1365245
theorem B5235619 : Blo 794341 5235619 := bstep (se 1 (by rfl) ⟨3926714, by rfl⟩ : syracuseStep 5235619 = 7853429) B7853429
theorem B3400717 : Blo 794341 3400717 := bstep (se 3 (by rfl) ⟨637634, by rfl⟩ : syracuseStep 3400717 = 1275269) B1275269
theorem B1795121 : Blo 794341 1795121 := bstep (se 2 (by rfl) ⟨673170, by rfl⟩ : syracuseStep 1795121 = 1346341) B1346341
theorem B1795139 : Blo 794341 1795139 := bstep (se 1 (by rfl) ⟨1346354, by rfl⟩ : syracuseStep 1795139 = 2692709) B2692709
theorem B1008931 : Blo 794341 1008931 := bstep (se 1 (by rfl) ⟨756698, by rfl⟩ : syracuseStep 1008931 = 1513397) B1513397
theorem B1697105 : Blo 794341 1697105 := bstep (se 2 (by rfl) ⟨636414, by rfl⟩ : syracuseStep 1697105 = 1272829) B1272829
theorem B1795409 : Blo 794341 1795409 := bstep (se 2 (by rfl) ⟨673278, by rfl⟩ : syracuseStep 1795409 = 1346557) B1346557
theorem B1795427 : Blo 794341 1795427 := bstep (se 1 (by rfl) ⟨1346570, by rfl⟩ : syracuseStep 1795427 = 2693141) B2693141
theorem B1009027 : Blo 794341 1009027 := bstep (se 1 (by rfl) ⟨756770, by rfl⟩ : syracuseStep 1009027 = 1513541) B1513541
theorem B3630563 : Blo 794341 3630563 := bstep (se 1 (by rfl) ⟨2722922, by rfl⟩ : syracuseStep 3630563 = 5445845) B5445845
theorem B1795697 : Blo 794341 1795697 := bstep (se 2 (by rfl) ⟨673386, by rfl⟩ : syracuseStep 1795697 = 1346773) B1346773
theorem B1795715 : Blo 794341 1795715 := bstep (se 1 (by rfl) ⟨1346786, by rfl⟩ : syracuseStep 1795715 = 2693573) B2693573
theorem B5531333 : Blo 794341 5531333 := bstep (se 4 (by rfl) ⟨518562, by rfl⟩ : syracuseStep 5531333 = 1037125) B1037125
theorem B1009523 : Blo 794341 1009523 := bstep (se 1 (by rfl) ⟨757142, by rfl⟩ : syracuseStep 1009523 = 1514285) B1514285
theorem B1795985 : Blo 794341 1795985 := bstep (se 2 (by rfl) ⟨673494, by rfl⟩ : syracuseStep 1795985 = 1346989) B1346989
theorem B1796003 : Blo 794341 1796003 := bstep (se 1 (by rfl) ⟨1347002, by rfl⟩ : syracuseStep 1796003 = 2694005) B2694005
theorem B4024241 : Blo 794341 4024241 := bstep (se 2 (by rfl) ⟨1509090, by rfl⟩ : syracuseStep 4024241 = 3018181) B3018181
theorem B1402867 : Blo 794341 1402867 := bstep (se 1 (by rfl) ⟨1052150, by rfl⟩ : syracuseStep 1402867 = 2104301) B2104301
theorem B3401777 : Blo 794341 3401777 := bstep (se 2 (by rfl) ⟨1275666, by rfl⟩ : syracuseStep 3401777 = 2551333) B2551333
theorem B4843597 : Blo 794341 4843597 := bstep (se 3 (by rfl) ⟨908174, by rfl⟩ : syracuseStep 4843597 = 1816349) B1816349
theorem B1108081 : Blo 794341 1108081 := bstep (se 2 (by rfl) ⟨415530, by rfl⟩ : syracuseStep 1108081 = 831061) B831061
theorem B2418929 : Blo 794341 2418929 := bstep (se 2 (by rfl) ⟨907098, by rfl⟩ : syracuseStep 2418929 = 1814197) B1814197
theorem B2550001 : Blo 794341 2550001 := bstep (se 2 (by rfl) ⟨956250, by rfl⟩ : syracuseStep 2550001 = 1912501) B1912501
theorem B2550179 : Blo 794341 2550179 := bstep (se 1 (by rfl) ⟨1912634, by rfl⟩ : syracuseStep 2550179 = 3825269) B3825269
theorem B2681261 : Blo 794341 2681261 := bstep (se 3 (by rfl) ⟨502736, by rfl⟩ : syracuseStep 2681261 = 1005473) B1005473
theorem B6121925 : Blo 794341 6121925 := bstep (se 4 (by rfl) ⟨573930, by rfl⟩ : syracuseStep 6121925 = 1147861) B1147861
theorem B2681315 : Blo 794341 2681315 := bstep (se 1 (by rfl) ⟨2010986, by rfl⟩ : syracuseStep 2681315 = 4021973) B4021973
theorem B3631601 : Blo 794341 3631601 := bstep (se 2 (by rfl) ⟨1361850, by rfl⟩ : syracuseStep 3631601 = 2723701) B2723701
theorem B2157101 : Blo 794341 2157101 := bstep (se 3 (by rfl) ⟨404456, by rfl⟩ : syracuseStep 2157101 = 808913) B808913
theorem B1010227 : Blo 794341 1010227 := bstep (se 1 (by rfl) ⟨757670, by rfl⟩ : syracuseStep 1010227 = 1515341) B1515341
theorem B1272419 : Blo 794341 1272419 := bstep (se 1 (by rfl) ⟨954314, by rfl⟩ : syracuseStep 1272419 = 1908629) B1908629
theorem B1698403 : Blo 794341 1698403 := bstep (se 1 (by rfl) ⟨1273802, by rfl⟩ : syracuseStep 1698403 = 2547605) B2547605
theorem B1632881 : Blo 794341 1632881 := bstep (se 2 (by rfl) ⟨612330, by rfl⟩ : syracuseStep 1632881 = 1224661) B1224661
theorem B1075825 : Blo 794341 1075825 := bstep (se 2 (by rfl) ⟨403434, by rfl⟩ : syracuseStep 1075825 = 806869) B806869
theorem B1010323 : Blo 794341 1010323 := bstep (se 1 (by rfl) ⟨757742, by rfl⟩ : syracuseStep 1010323 = 1515485) B1515485
theorem B2681585 : Blo 794341 2681585 := bstep (se 2 (by rfl) ⟨1005594, by rfl⟩ : syracuseStep 2681585 = 2011189) B2011189
theorem B1075987 : Blo 794341 1075987 := bstep (se 1 (by rfl) ⟨806990, by rfl⟩ : syracuseStep 1075987 = 1613981) B1613981
theorem B5106509 : Blo 794341 5106509 := bstep (se 3 (by rfl) ⟨957470, by rfl⟩ : syracuseStep 5106509 = 1914941) B1914941
theorem B2157553 : Blo 794341 2157553 := bstep (se 2 (by rfl) ⟨809082, by rfl⟩ : syracuseStep 2157553 = 1618165) B1618165
theorem B2682125 : Blo 794341 2682125 := bstep (se 3 (by rfl) ⟨502898, by rfl⟩ : syracuseStep 2682125 = 1005797) B1005797
theorem B2682179 : Blo 794341 2682179 := bstep (se 1 (by rfl) ⟨2011634, by rfl⟩ : syracuseStep 2682179 = 4023269) B4023269
theorem B4025699 : Blo 794341 4025699 := bstep (se 1 (by rfl) ⟨3019274, by rfl⟩ : syracuseStep 4025699 = 6038549) B6038549
theorem B1076593 : Blo 794341 1076593 := bstep (se 2 (by rfl) ⟨403722, by rfl⟩ : syracuseStep 1076593 = 807445) B807445
theorem B1535441 : Blo 794341 1535441 := bstep (se 2 (by rfl) ⟨575790, by rfl⟩ : syracuseStep 1535441 = 1151581) B1151581
theorem B1273411 : Blo 794341 1273411 := bstep (se 1 (by rfl) ⟨955058, by rfl⟩ : syracuseStep 1273411 = 1910117) B1910117
theorem B2682449 : Blo 794341 2682449 := bstep (se 2 (by rfl) ⟨1005918, by rfl⟩ : syracuseStep 2682449 = 2011837) B2011837
theorem B10219121 : Blo 794341 10219121 := bstep (se 2 (by rfl) ⟨3832170, by rfl⟩ : syracuseStep 10219121 = 7664341) B7664341
theorem B3272333 : Blo 794341 3272333 := bstep (se 3 (by rfl) ⟨613562, by rfl⟩ : syracuseStep 3272333 = 1227125) B1227125
theorem B4091633 : Blo 794341 4091633 := bstep (se 2 (by rfl) ⟨1534362, by rfl⟩ : syracuseStep 4091633 = 3068725) B3068725
theorem B5730061 : Blo 794341 5730061 := bstep (se 3 (by rfl) ⟨1074386, by rfl⟩ : syracuseStep 5730061 = 2148773) B2148773
theorem B1699633 : Blo 794341 1699633 := bstep (se 2 (by rfl) ⟨637362, by rfl⟩ : syracuseStep 1699633 = 1274725) B1274725
theorem B1208369 : Blo 794341 1208369 := bstep (se 2 (by rfl) ⟨453138, by rfl⟩ : syracuseStep 1208369 = 906277) B906277
theorem B2682989 : Blo 794341 2682989 := bstep (se 3 (by rfl) ⟨503060, by rfl⟩ : syracuseStep 2682989 = 1006121) B1006121
theorem B12447857 : Blo 794341 12447857 := bstep (se 2 (by rfl) ⟨4667946, by rfl⟩ : syracuseStep 12447857 = 9335893) B9335893
theorem B4026509 : Blo 794341 4026509 := bstep (se 3 (by rfl) ⟨754970, by rfl⟩ : syracuseStep 4026509 = 1509941) B1509941
theorem B2551949 : Blo 794341 2551949 := bstep (se 3 (by rfl) ⟨478490, by rfl⟩ : syracuseStep 2551949 = 956981) B956981
theorem B2683043 : Blo 794341 2683043 := bstep (se 1 (by rfl) ⟨2012282, by rfl⟩ : syracuseStep 2683043 = 4024565) B4024565
theorem B13070645 : Blo 794341 13070645 := bstep (se 5 (by rfl) ⟨612686, by rfl⟩ : syracuseStep 13070645 = 1225373) B1225373
theorem B2683313 : Blo 794341 2683313 := bstep (se 2 (by rfl) ⟨1006242, by rfl⟩ : syracuseStep 2683313 = 2012485) B2012485
theorem B1700291 : Blo 794341 1700291 := bstep (se 1 (by rfl) ⟨1275218, by rfl⟩ : syracuseStep 1700291 = 2550437) B2550437
theorem B1274321 : Blo 794341 1274321 := bstep (se 2 (by rfl) ⟨477870, by rfl⟩ : syracuseStep 1274321 = 955741) B955741
theorem B1274449 : Blo 794341 1274449 := bstep (se 2 (by rfl) ⟨477918, by rfl⟩ : syracuseStep 1274449 = 955837) B955837
theorem B848723 : Blo 794341 848723 := bstep (se 1 (by rfl) ⟨636542, by rfl⟩ : syracuseStep 848723 = 1273085) B1273085
theorem B2683853 : Blo 794341 2683853 := bstep (se 3 (by rfl) ⟨503222, by rfl⟩ : syracuseStep 2683853 = 1006445) B1006445
theorem B3404749 : Blo 794341 3404749 := bstep (se 3 (by rfl) ⟨638390, by rfl⟩ : syracuseStep 3404749 = 1276781) B1276781
theorem B2683907 : Blo 794341 2683907 := bstep (se 1 (by rfl) ⟨2012930, by rfl⟩ : syracuseStep 2683907 = 4025861) B4025861
theorem B5108741 : Blo 794341 5108741 := bstep (se 4 (by rfl) ⟨478944, by rfl⟩ : syracuseStep 5108741 = 957889) B957889
theorem B1340563 : Blo 794341 1340563 := bstep (se 1 (by rfl) ⟨1005422, by rfl⟩ : syracuseStep 1340563 = 2010845) B2010845
theorem B2684177 : Blo 794341 2684177 := bstep (se 2 (by rfl) ⟨1006566, by rfl⟩ : syracuseStep 2684177 = 2013133) B2013133
theorem B1701137 : Blo 794341 1701137 := bstep (se 2 (by rfl) ⟨637926, by rfl⟩ : syracuseStep 1701137 = 1275853) B1275853
theorem B1340705 : Blo 794341 1340705 := bstep (se 2 (by rfl) ⟨502764, by rfl⟩ : syracuseStep 1340705 = 1005529) B1005529
theorem B3405091 : Blo 794341 3405091 := bstep (se 1 (by rfl) ⟨2553818, by rfl⟩ : syracuseStep 3405091 = 5107637) B5107637
theorem B6452621 : Blo 794341 6452621 := bstep (se 3 (by rfl) ⟨1209866, by rfl⟩ : syracuseStep 6452621 = 2419733) B2419733
theorem B1340833 : Blo 794341 1340833 := bstep (se 2 (by rfl) ⟨502812, by rfl⟩ : syracuseStep 1340833 = 1005625) B1005625
theorem B5174705 : Blo 794341 5174705 := bstep (se 2 (by rfl) ⟨1940514, by rfl⟩ : syracuseStep 5174705 = 3881029) B3881029
theorem B1340867 : Blo 794341 1340867 := bstep (se 1 (by rfl) ⟨1005650, by rfl⟩ : syracuseStep 1340867 = 2011301) B2011301
theorem B1275443 : Blo 794341 1275443 := bstep (se 1 (by rfl) ⟨956582, by rfl⟩ : syracuseStep 1275443 = 1913165) B1913165
theorem B1340995 : Blo 794341 1340995 := bstep (se 1 (by rfl) ⟨1005746, by rfl⟩ : syracuseStep 1340995 = 2011493) B2011493
theorem B849475 : Blo 794341 849475 := bstep (se 1 (by rfl) ⟨637106, by rfl⟩ : syracuseStep 849475 = 1274213) B1274213
theorem B2586221 : Blo 794341 2586221 := bstep (se 3 (by rfl) ⟨484916, by rfl⟩ : syracuseStep 2586221 = 969833) B969833
theorem B1341137 : Blo 794341 1341137 := bstep (se 2 (by rfl) ⟨502926, by rfl⟩ : syracuseStep 1341137 = 1005853) B1005853
theorem B816883 : Blo 794341 816883 := bstep (se 1 (by rfl) ⟨612662, by rfl⟩ : syracuseStep 816883 = 1225325) B1225325
theorem B2684717 : Blo 794341 2684717 := bstep (se 3 (by rfl) ⟨503384, by rfl⟩ : syracuseStep 2684717 = 1006769) B1006769
theorem B1341265 : Blo 794341 1341265 := bstep (se 2 (by rfl) ⟨502974, by rfl⟩ : syracuseStep 1341265 = 1005949) B1005949
theorem B2684771 : Blo 794341 2684771 := bstep (se 1 (by rfl) ⟨2013578, by rfl⟩ : syracuseStep 2684771 = 4027157) B4027157
theorem B1341299 : Blo 794341 1341299 := bstep (se 1 (by rfl) ⟨1005974, by rfl⟩ : syracuseStep 1341299 = 2011949) B2011949
theorem B1210243 : Blo 794341 1210243 := bstep (se 1 (by rfl) ⟨907682, by rfl⟩ : syracuseStep 1210243 = 1815365) B1815365
theorem B1341427 : Blo 794341 1341427 := bstep (se 1 (by rfl) ⟨1006070, by rfl⟩ : syracuseStep 1341427 = 2012141) B2012141
theorem B2685041 : Blo 794341 2685041 := bstep (se 2 (by rfl) ⟨1006890, by rfl⟩ : syracuseStep 2685041 = 2013781) B2013781
theorem B1341569 : Blo 794341 1341569 := bstep (se 2 (by rfl) ⟨503088, by rfl⟩ : syracuseStep 1341569 = 1006177) B1006177
theorem B1341697 : Blo 794341 1341697 := bstep (se 2 (by rfl) ⟨503136, by rfl⟩ : syracuseStep 1341697 = 1006273) B1006273
theorem B1341731 : Blo 794341 1341731 := bstep (se 1 (by rfl) ⟨1006298, by rfl⟩ : syracuseStep 1341731 = 2012597) B2012597
theorem B1341859 : Blo 794341 1341859 := bstep (se 1 (by rfl) ⟨1006394, by rfl⟩ : syracuseStep 1341859 = 2012789) B2012789
theorem B1342001 : Blo 794341 1342001 := bstep (se 2 (by rfl) ⟨503250, by rfl⟩ : syracuseStep 1342001 = 1006501) B1006501
theorem B8190563 : Blo 794341 8190563 := bstep (se 1 (by rfl) ⟨6142922, by rfl⟩ : syracuseStep 8190563 = 12285845) B12285845
theorem B850547 : Blo 794341 850547 := bstep (se 1 (by rfl) ⟨637910, by rfl⟩ : syracuseStep 850547 = 1275821) B1275821
theorem B2685581 : Blo 794341 2685581 := bstep (se 3 (by rfl) ⟨503546, by rfl⟩ : syracuseStep 2685581 = 1007093) B1007093
theorem B1342129 : Blo 794341 1342129 := bstep (se 2 (by rfl) ⟨503298, by rfl⟩ : syracuseStep 1342129 = 1006597) B1006597
theorem B2685635 : Blo 794341 2685635 := bstep (se 1 (by rfl) ⟨2014226, by rfl⟩ : syracuseStep 2685635 = 4028453) B4028453
theorem B1342163 : Blo 794341 1342163 := bstep (se 1 (by rfl) ⟨1006622, by rfl⟩ : syracuseStep 1342163 = 2013245) B2013245
theorem B3635981 : Blo 794341 3635981 := bstep (se 3 (by rfl) ⟨681746, by rfl⟩ : syracuseStep 3635981 = 1363493) B1363493
theorem B1342291 : Blo 794341 1342291 := bstep (se 1 (by rfl) ⟨1006718, by rfl⟩ : syracuseStep 1342291 = 2013437) B2013437
theorem B1702819 : Blo 794341 1702819 := bstep (se 1 (by rfl) ⟨1277114, by rfl⟩ : syracuseStep 1702819 = 2554229) B2554229
theorem B2685905 : Blo 794341 2685905 := bstep (se 2 (by rfl) ⟨1007214, by rfl⟩ : syracuseStep 2685905 = 2014429) B2014429
theorem B2587601 : Blo 794341 2587601 := bstep (se 2 (by rfl) ⟨970350, by rfl⟩ : syracuseStep 2587601 = 1940701) B1940701
theorem B1342433 : Blo 794341 1342433 := bstep (se 2 (by rfl) ⟨503412, by rfl⟩ : syracuseStep 1342433 = 1006825) B1006825
theorem B1276897 : Blo 794341 1276897 := bstep (se 2 (by rfl) ⟨478836, by rfl⟩ : syracuseStep 1276897 = 957673) B957673
theorem B4029425 : Blo 794341 4029425 := bstep (se 2 (by rfl) ⟨1511034, by rfl⟩ : syracuseStep 4029425 = 3022069) B3022069
theorem B1211411 : Blo 794341 1211411 := bstep (se 1 (by rfl) ⟨908558, by rfl⟩ : syracuseStep 1211411 = 1817117) B1817117
theorem B1342561 : Blo 794341 1342561 := bstep (se 2 (by rfl) ⟨503460, by rfl⟩ : syracuseStep 1342561 = 1006921) B1006921
theorem B1342595 : Blo 794341 1342595 := bstep (se 1 (by rfl) ⟨1006946, by rfl⟩ : syracuseStep 1342595 = 2013893) B2013893
theorem B1342723 : Blo 794341 1342723 := bstep (se 1 (by rfl) ⟨1007042, by rfl⟩ : syracuseStep 1342723 = 2014085) B2014085
theorem B1703281 : Blo 794341 1703281 := bstep (se 2 (by rfl) ⟨638730, by rfl⟩ : syracuseStep 1703281 = 1277461) B1277461
theorem B1342865 : Blo 794341 1342865 := bstep (se 2 (by rfl) ⟨503574, by rfl⟩ : syracuseStep 1342865 = 1007149) B1007149
theorem B2686445 : Blo 794341 2686445 := bstep (se 3 (by rfl) ⟨503708, by rfl⟩ : syracuseStep 2686445 = 1007417) B1007417
theorem B1342993 : Blo 794341 1342993 := bstep (se 2 (by rfl) ⟨503622, by rfl⟩ : syracuseStep 1342993 = 1007245) B1007245
theorem B20708885 : Blo 794341 20708885 := bstep (se 6 (by rfl) ⟨485364, by rfl⟩ : syracuseStep 20708885 = 970729) B970729
theorem B2686499 : Blo 794341 2686499 := bstep (se 1 (by rfl) ⟨2014874, by rfl⟩ : syracuseStep 2686499 = 4029749) B4029749
theorem B1343027 : Blo 794341 1343027 := bstep (se 1 (by rfl) ⟨1007270, by rfl⟩ : syracuseStep 1343027 = 2014541) B2014541
theorem B2555459 : Blo 794341 2555459 := bstep (se 1 (by rfl) ⟨1916594, by rfl⟩ : syracuseStep 2555459 = 3833189) B3833189
theorem B7274083 : Blo 794341 7274083 := bstep (se 1 (by rfl) ⟨5455562, by rfl⟩ : syracuseStep 7274083 = 10911125) B10911125
theorem B1343155 : Blo 794341 1343155 := bstep (se 1 (by rfl) ⟨1007366, by rfl⟩ : syracuseStep 1343155 = 2014733) B2014733
theorem B851683 : Blo 794341 851683 := bstep (se 1 (by rfl) ⟨638762, by rfl⟩ : syracuseStep 851683 = 1277525) B1277525
theorem B2686769 : Blo 794341 2686769 := bstep (se 2 (by rfl) ⟨1007538, by rfl⟩ : syracuseStep 2686769 = 2015077) B2015077
theorem B1343297 : Blo 794341 1343297 := bstep (se 2 (by rfl) ⟨503736, by rfl⟩ : syracuseStep 1343297 = 1007473) B1007473
theorem B1343425 : Blo 794341 1343425 := bstep (se 2 (by rfl) ⟨503784, by rfl⟩ : syracuseStep 1343425 = 1007569) B1007569
theorem B1343459 : Blo 794341 1343459 := bstep (se 1 (by rfl) ⟨1007594, by rfl⟩ : syracuseStep 1343459 = 2015189) B2015189
theorem B1343513 : Blo 794341 1343513 := bstep (se 2 (by rfl) ⟨503817, by rfl⟩ : syracuseStep 1343513 = 1007635) B1007635
theorem B9175133 : Blo 794341 9175133 := bstep (se 3 (by rfl) ⟨1720337, by rfl⟩ : syracuseStep 9175133 = 3440675) B3440675
theorem B1343641 : Blo 794341 1343641 := bstep (se 2 (by rfl) ⟨503865, by rfl⟩ : syracuseStep 1343641 = 1007731) B1007731
theorem B3440819 : Blo 794341 3440819 := bstep (se 1 (by rfl) ⟨2580614, by rfl⟩ : syracuseStep 3440819 = 5161229) B5161229
theorem B3408065 : Blo 794341 3408065 := bstep (se 2 (by rfl) ⟨1278024, by rfl⟩ : syracuseStep 3408065 = 2556049) B2556049
theorem B2556125 : Blo 794341 2556125 := bstep (se 3 (by rfl) ⟨479273, by rfl⟩ : syracuseStep 2556125 = 958547) B958547
theorem B2687255 : Blo 794341 2687255 := bstep (se 1 (by rfl) ⟨2015441, by rfl⟩ : syracuseStep 2687255 = 4030883) B4030883
theorem B10224089 : Blo 794341 10224089 := bstep (se 2 (by rfl) ⟨3834033, by rfl⟩ : syracuseStep 10224089 = 7668067) B7668067
theorem B852503 : Blo 794341 852503 := bstep (se 1 (by rfl) ⟨639377, by rfl⟩ : syracuseStep 852503 = 1278755) B1278755
theorem B11469347 : Blo 794341 11469347 := bstep (se 1 (by rfl) ⟨8602010, by rfl⟩ : syracuseStep 11469347 = 17204021) B17204021
theorem B1344215 : Blo 794341 1344215 := bstep (se 1 (by rfl) ⟨1008161, by rfl⟩ : syracuseStep 1344215 = 2016323) B2016323
theorem B1704665 : Blo 794341 1704665 := bstep (se 2 (by rfl) ⟨639249, by rfl⟩ : syracuseStep 1704665 = 1278499) B1278499
theorem B2687795 : Blo 794341 2687795 := bstep (se 1 (by rfl) ⟨2015846, by rfl⟩ : syracuseStep 2687795 = 4031693) B4031693
theorem B1344343 : Blo 794341 1344343 := bstep (se 1 (by rfl) ⟨1008257, by rfl⟩ : syracuseStep 1344343 = 2016515) B2016515
theorem B1868633 : Blo 794341 1868633 := bstep (se 2 (by rfl) ⟨700737, by rfl⟩ : syracuseStep 1868633 = 1401475) B1401475
theorem B1639283 : Blo 794341 1639283 := bstep (se 1 (by rfl) ⟨1229462, by rfl⟩ : syracuseStep 1639283 = 2458925) B2458925
theorem B5899159 : Blo 794341 5899159 := bstep (se 1 (by rfl) ⟨4424369, by rfl⟩ : syracuseStep 5899159 = 8848739) B8848739
theorem B3834803 : Blo 794341 3834803 := bstep (se 1 (by rfl) ⟨2876102, by rfl⟩ : syracuseStep 3834803 = 5752205) B5752205
theorem B3441629 : Blo 794341 3441629 := bstep (se 3 (by rfl) ⟨645305, by rfl⟩ : syracuseStep 3441629 = 1290611) B1290611
theorem B1508377 : Blo 794341 1508377 := bstep (se 2 (by rfl) ⟨565641, by rfl⟩ : syracuseStep 1508377 = 1131283) B1131283
theorem B3638317 : Blo 794341 3638317 := bstep (se 3 (by rfl) ⟨682184, by rfl⟩ : syracuseStep 3638317 = 1364369) B1364369
theorem B2688065 : Blo 794341 2688065 := bstep (se 2 (by rfl) ⟨1008024, by rfl⟩ : syracuseStep 2688065 = 2016049) B2016049
theorem B6980825 : Blo 794341 6980825 := bstep (se 2 (by rfl) ⟨2617809, by rfl⟩ : syracuseStep 6980825 = 5235619) B5235619
theorem B1770803 : Blo 794341 1770803 := bstep (se 1 (by rfl) ⟨1328102, by rfl⟩ : syracuseStep 1770803 = 2656205) B2656205
theorem B3016025 : Blo 794341 3016025 := bstep (se 2 (by rfl) ⟨1131009, by rfl⟩ : syracuseStep 3016025 = 2262019) B2262019
theorem B1344971 : Blo 794341 1344971 := bstep (se 1 (by rfl) ⟨1008728, by rfl⟩ : syracuseStep 1344971 = 2017457) B2017457
theorem B4032017 : Blo 794341 4032017 := bstep (se 2 (by rfl) ⟨1512006, by rfl⟩ : syracuseStep 4032017 = 3024013) B3024013
theorem B3016237 : Blo 794341 3016237 := bstep (se 3 (by rfl) ⟨565544, by rfl⟩ : syracuseStep 3016237 = 1131089) B1131089
theorem B1508939 : Blo 794341 1508939 := bstep (se 1 (by rfl) ⟨1131704, by rfl⟩ : syracuseStep 1508939 = 2263409) B2263409
theorem B1345099 : Blo 794341 1345099 := bstep (se 1 (by rfl) ⟨1008824, by rfl⟩ : syracuseStep 1345099 = 2017649) B2017649
theorem B2688605 : Blo 794341 2688605 := bstep (se 3 (by rfl) ⟨504113, by rfl⟩ : syracuseStep 2688605 = 1008227) B1008227
theorem B2721431 : Blo 794341 2721431 := bstep (se 1 (by rfl) ⟨2041073, by rfl⟩ : syracuseStep 2721431 = 4082147) B4082147
theorem B11503255 : Blo 794341 11503255 := bstep (se 1 (by rfl) ⟨8627441, by rfl⟩ : syracuseStep 11503255 = 17254883) B17254883
theorem B4032179 : Blo 794341 4032179 := bstep (se 1 (by rfl) ⟨3024134, by rfl⟩ : syracuseStep 4032179 = 6048269) B6048269
theorem B1345241 : Blo 794341 1345241 := bstep (se 2 (by rfl) ⟨504465, by rfl⟩ : syracuseStep 1345241 = 1008931) B1008931
theorem B1509121 : Blo 794341 1509121 := bstep (se 2 (by rfl) ⟨565920, by rfl⟩ : syracuseStep 1509121 = 1131841) B1131841
theorem B3409739 : Blo 794341 3409739 := bstep (se 1 (by rfl) ⟨2557304, by rfl⟩ : syracuseStep 3409739 = 5114609) B5114609
theorem B1345369 : Blo 794341 1345369 := bstep (se 2 (by rfl) ⟨504513, by rfl⟩ : syracuseStep 1345369 = 1009027) B1009027
theorem B3016541 : Blo 794341 3016541 := bstep (se 3 (by rfl) ⟨565601, by rfl⟩ : syracuseStep 3016541 = 1131203) B1131203
theorem B2263261 : Blo 794341 2263261 := bstep (se 3 (by rfl) ⟨424361, by rfl⟩ : syracuseStep 2263261 = 848723) B848723
theorem B2427101 : Blo 794341 2427101 := bstep (se 3 (by rfl) ⟨455081, by rfl⟩ : syracuseStep 2427101 = 910163) B910163
theorem B1345943 : Blo 794341 1345943 := bstep (se 1 (by rfl) ⟨1009457, by rfl⟩ : syracuseStep 1345943 = 2018915) B2018915
theorem B1509835 : Blo 794341 1509835 := bstep (se 1 (by rfl) ⟨1132376, by rfl⟩ : syracuseStep 1509835 = 2264753) B2264753
theorem B1509911 : Blo 794341 1509911 := bstep (se 1 (by rfl) ⟨1132433, by rfl⟩ : syracuseStep 1509911 = 2264867) B2264867
theorem B1346071 : Blo 794341 1346071 := bstep (se 1 (by rfl) ⟨1009553, by rfl⟩ : syracuseStep 1346071 = 2019107) B2019107
theorem B1870489 : Blo 794341 1870489 := bstep (se 2 (by rfl) ⟨701433, by rfl⟩ : syracuseStep 1870489 = 1402867) B1402867
theorem B2689739 : Blo 794341 2689739 := bstep (se 1 (by rfl) ⟨2017304, by rfl⟩ : syracuseStep 2689739 = 4034609) B4034609
theorem B6458129 : Blo 794341 6458129 := bstep (se 2 (by rfl) ⟨2421798, by rfl⟩ : syracuseStep 6458129 = 4843597) B4843597
theorem B34868033 : Blo 794341 34868033 := bstep (se 2 (by rfl) ⟨13075512, by rfl⟩ : syracuseStep 34868033 = 26151025) B26151025
theorem B1477441 : Blo 794341 1477441 := bstep (se 2 (by rfl) ⟨554040, by rfl⟩ : syracuseStep 1477441 = 1108081) B1108081
theorem B2690009 : Blo 794341 2690009 := bstep (se 2 (by rfl) ⟨1008753, by rfl⟩ : syracuseStep 2690009 = 2017507) B2017507
theorem B1346699 : Blo 794341 1346699 := bstep (se 1 (by rfl) ⟨1010024, by rfl⟩ : syracuseStep 1346699 = 2020049) B2020049
theorem B1510579 : Blo 794341 1510579 := bstep (se 1 (by rfl) ⟨1132934, by rfl⟩ : syracuseStep 1510579 = 2265869) B2265869
theorem B1346827 : Blo 794341 1346827 := bstep (se 1 (by rfl) ⟨1010120, by rfl⟩ : syracuseStep 1346827 = 2020241) B2020241
theorem B1510807 : Blo 794341 1510807 := bstep (se 1 (by rfl) ⟨1133105, by rfl⟩ : syracuseStep 1510807 = 2266211) B2266211
theorem B1346969 : Blo 794341 1346969 := bstep (se 2 (by rfl) ⟨505113, by rfl⟩ : syracuseStep 1346969 = 1010227) B1010227
theorem B2264537 : Blo 794341 2264537 := bstep (se 2 (by rfl) ⟨849201, by rfl⟩ : syracuseStep 2264537 = 1698403) B1698403
theorem B1510913 : Blo 794341 1510913 := bstep (se 2 (by rfl) ⟨566592, by rfl⟩ : syracuseStep 1510913 = 1133185) B1133185
theorem B1347097 : Blo 794341 1347097 := bstep (se 2 (by rfl) ⟨505161, by rfl⟩ : syracuseStep 1347097 = 1010323) B1010323
theorem B4034123 : Blo 794341 4034123 := bstep (se 1 (by rfl) ⟨3025592, by rfl⟩ : syracuseStep 4034123 = 6051185) B6051185
theorem B2690711 : Blo 794341 2690711 := bstep (se 1 (by rfl) ⟨2018033, by rfl⟩ : syracuseStep 2690711 = 4036067) B4036067
theorem B1511065 : Blo 794341 1511065 := bstep (se 2 (by rfl) ⟨566649, by rfl⟩ : syracuseStep 1511065 = 1133299) B1133299
theorem B5738597 : Blo 794341 5738597 := bstep (se 4 (by rfl) ⟨537993, by rfl⟩ : syracuseStep 5738597 = 1075987) B1075987
theorem B1020055 : Blo 794341 1020055 := bstep (se 1 (by rfl) ⟨765041, by rfl⟩ : syracuseStep 1020055 = 1530083) B1530083
theorem B2691251 : Blo 794341 2691251 := bstep (se 1 (by rfl) ⟨2018438, by rfl⟩ : syracuseStep 2691251 = 4036877) B4036877
theorem B3281075 : Blo 794341 3281075 := bstep (se 1 (by rfl) ⟨2460806, by rfl⟩ : syracuseStep 3281075 = 4921613) B4921613
theorem B2298059 : Blo 794341 2298059 := bstep (se 1 (by rfl) ⟨1723544, by rfl⟩ : syracuseStep 2298059 = 3447089) B3447089
theorem B3019139 : Blo 794341 3019139 := bstep (se 1 (by rfl) ⟨2264354, by rfl⟩ : syracuseStep 3019139 = 4528709) B4528709
theorem B3019153 : Blo 794341 3019153 := bstep (se 2 (by rfl) ⟨1132182, by rfl⟩ : syracuseStep 3019153 = 2264365) B2264365
theorem B2691521 : Blo 794341 2691521 := bstep (se 2 (by rfl) ⟨1009320, by rfl⟩ : syracuseStep 2691521 = 2018641) B2018641
theorem B14750221 : Blo 794341 14750221 := bstep (se 3 (by rfl) ⟨2765666, by rfl⟩ : syracuseStep 14750221 = 5531333) B5531333
theorem B2626141 : Blo 794341 2626141 := bstep (se 3 (by rfl) ⟨492401, by rfl⟩ : syracuseStep 2626141 = 984803) B984803
theorem B3019457 : Blo 794341 3019457 := bstep (se 2 (by rfl) ⟨1132296, by rfl⟩ : syracuseStep 3019457 = 2264593) B2264593
theorem B4526999 : Blo 794341 4526999 := bstep (se 1 (by rfl) ⟨3395249, by rfl⟩ : syracuseStep 4526999 = 6790499) B6790499
theorem B1512371 : Blo 794341 1512371 := bstep (se 1 (by rfl) ⟨1134278, by rfl⟩ : syracuseStep 1512371 = 2268557) B2268557
theorem B2692061 : Blo 794341 2692061 := bstep (se 3 (by rfl) ⟨504761, by rfl⟩ : syracuseStep 2692061 = 1009523) B1009523
theorem B7640081 : Blo 794341 7640081 := bstep (se 2 (by rfl) ⟨2865030, by rfl⟩ : syracuseStep 7640081 = 5730061) B5730061
theorem B2266177 : Blo 794341 2266177 := bstep (se 2 (by rfl) ⟨849816, by rfl⟩ : syracuseStep 2266177 = 1699633) B1699633
theorem B1512523 : Blo 794341 1512523 := bstep (se 1 (by rfl) ⟨1134392, by rfl⟩ : syracuseStep 1512523 = 2268785) B2268785
theorem B2954519 : Blo 794341 2954519 := bstep (se 1 (by rfl) ⟨2215889, by rfl⟩ : syracuseStep 2954519 = 4431779) B4431779
theorem B4035905 : Blo 794341 4035905 := bstep (se 2 (by rfl) ⟨1513464, by rfl⟩ : syracuseStep 4035905 = 3026929) B3026929
theorem B3020125 : Blo 794341 3020125 := bstep (se 3 (by rfl) ⟨566273, by rfl⟩ : syracuseStep 3020125 = 1132547) B1132547
theorem B1512857 : Blo 794341 1512857 := bstep (se 2 (by rfl) ⟨567321, by rfl⟩ : syracuseStep 1512857 = 1134643) B1134643
theorem B9049805 : Blo 794341 9049805 := bstep (se 3 (by rfl) ⟨1696838, by rfl⟩ : syracuseStep 9049805 = 3393677) B3393677
theorem B2299927 : Blo 794341 2299927 := bstep (se 1 (by rfl) ⟨1724945, by rfl⟩ : syracuseStep 2299927 = 3449891) B3449891
theorem B1513495 : Blo 794341 1513495 := bstep (se 1 (by rfl) ⟨1135121, by rfl⟩ : syracuseStep 1513495 = 2270243) B2270243
theorem B2693195 : Blo 794341 2693195 := bstep (se 1 (by rfl) ⟨2019896, by rfl⟩ : syracuseStep 2693195 = 4039793) B4039793
theorem B4298845 : Blo 794341 4298845 := bstep (se 3 (by rfl) ⟨806033, by rfl⟩ : syracuseStep 4298845 = 1612067) B1612067
theorem B6035633 : Blo 794341 6035633 := bstep (se 2 (by rfl) ⟨2263362, by rfl⟩ : syracuseStep 6035633 = 4526725) B4526725
theorem B2693465 : Blo 794341 2693465 := bstep (se 2 (by rfl) ⟨1010049, by rfl⟩ : syracuseStep 2693465 = 2020099) B2020099
theorem B3021401 : Blo 794341 3021401 := bstep (se 2 (by rfl) ⟨1133025, by rfl⟩ : syracuseStep 3021401 = 2266051) B2266051
theorem B6036119 : Blo 794341 6036119 := bstep (se 1 (by rfl) ⟨4527089, by rfl⟩ : syracuseStep 6036119 = 9054179) B9054179
theorem B2267851 : Blo 794341 2267851 := bstep (se 1 (by rfl) ⟨1700888, by rfl⟩ : syracuseStep 2267851 = 3401777) B3401777
theorem B1612619 : Blo 794341 1612619 := bstep (se 1 (by rfl) ⟨1209464, by rfl⟩ : syracuseStep 1612619 = 2418929) B2418929
theorem B1514315 : Blo 794341 1514315 := bstep (se 1 (by rfl) ⟨1135736, by rfl⟩ : syracuseStep 1514315 = 2271473) B2271473
theorem B1514369 : Blo 794341 1514369 := bstep (se 2 (by rfl) ⟨567888, by rfl⟩ : syracuseStep 1514369 = 1135777) B1135777
theorem B2268125 : Blo 794341 2268125 := bstep (se 3 (by rfl) ⟨425273, by rfl⟩ : syracuseStep 2268125 = 850547) B850547
theorem B2694167 : Blo 794341 2694167 := bstep (se 1 (by rfl) ⟨2020625, by rfl⟩ : syracuseStep 2694167 = 4041251) B4041251
theorem B1088587 : Blo 794341 1088587 := bstep (se 1 (by rfl) ⟨816440, by rfl⟩ : syracuseStep 1088587 = 1632881) B1632881
theorem B4037849 : Blo 794341 4037849 := bstep (se 2 (by rfl) ⟨1514193, by rfl⟩ : syracuseStep 4037849 = 3028387) B3028387
theorem B794347 : Blo 794341 794347 := bstep (se 1 (by rfl) ⟨595760, by rfl⟩ : syracuseStep 794347 = 1191521) B1191521
theorem B794359 : Blo 794341 794359 := bstep (se 1 (by rfl) ⟨595769, by rfl⟩ : syracuseStep 794359 = 1191539) B1191539
theorem B794379 : Blo 794341 794379 := bstep (se 1 (by rfl) ⟨595784, by rfl⟩ : syracuseStep 794379 = 1191569) B1191569
theorem B794391 : Blo 794341 794391 := bstep (se 1 (by rfl) ⟨595793, by rfl⟩ : syracuseStep 794391 = 1191587) B1191587
theorem B859927 : Blo 794341 859927 := bstep (se 1 (by rfl) ⟨644945, by rfl⟩ : syracuseStep 859927 = 1289891) B1289891
theorem B1515287 : Blo 794341 1515287 := bstep (se 1 (by rfl) ⟨1136465, by rfl⟩ : syracuseStep 1515287 = 2272931) B2272931
theorem B794411 : Blo 794341 794411 := bstep (se 1 (by rfl) ⟨595808, by rfl⟩ : syracuseStep 794411 = 1191617) B1191617
theorem B794423 : Blo 794341 794423 := bstep (se 1 (by rfl) ⟨595817, by rfl⟩ : syracuseStep 794423 = 1191635) B1191635
theorem B794443 : Blo 794341 794443 := bstep (se 1 (by rfl) ⟨595832, by rfl⟩ : syracuseStep 794443 = 1191665) B1191665
theorem B2727755 : Blo 794341 2727755 := bstep (se 1 (by rfl) ⟨2045816, by rfl⟩ : syracuseStep 2727755 = 4091633) B4091633
theorem B794455 : Blo 794341 794455 := bstep (se 1 (by rfl) ⟨595841, by rfl⟩ : syracuseStep 794455 = 1191683) B1191683
theorem B1613657 : Blo 794341 1613657 := bstep (se 2 (by rfl) ⟨605121, by rfl⟩ : syracuseStep 1613657 = 1210243) B1210243
theorem B794475 : Blo 794341 794475 := bstep (se 1 (by rfl) ⟨595856, by rfl⟩ : syracuseStep 794475 = 1191713) B1191713
theorem B794487 : Blo 794341 794487 := bstep (se 1 (by rfl) ⟨595865, by rfl⟩ : syracuseStep 794487 = 1191731) B1191731
theorem B794507 : Blo 794341 794507 := bstep (se 1 (by rfl) ⟨595880, by rfl⟩ : syracuseStep 794507 = 1191761) B1191761
theorem B794519 : Blo 794341 794519 := bstep (se 1 (by rfl) ⟨595889, by rfl⟩ : syracuseStep 794519 = 1191779) B1191779
theorem B794539 : Blo 794341 794539 := bstep (se 1 (by rfl) ⟨595904, by rfl⟩ : syracuseStep 794539 = 1191809) B1191809
theorem B794551 : Blo 794341 794551 := bstep (se 1 (by rfl) ⟨595913, by rfl⟩ : syracuseStep 794551 = 1191827) B1191827
theorem B794571 : Blo 794341 794571 := bstep (se 1 (by rfl) ⟨595928, by rfl⟩ : syracuseStep 794571 = 1191857) B1191857
theorem B794583 : Blo 794341 794583 := bstep (se 1 (by rfl) ⟨595937, by rfl⟩ : syracuseStep 794583 = 1191875) B1191875
theorem B794603 : Blo 794341 794603 := bstep (se 1 (by rfl) ⟨595952, by rfl⟩ : syracuseStep 794603 = 1191905) B1191905
theorem B794615 : Blo 794341 794615 := bstep (se 1 (by rfl) ⟨595961, by rfl⟩ : syracuseStep 794615 = 1191923) B1191923
theorem B794635 : Blo 794341 794635 := bstep (se 1 (by rfl) ⟨595976, by rfl⟩ : syracuseStep 794635 = 1191953) B1191953
theorem B794647 : Blo 794341 794647 := bstep (se 1 (by rfl) ⟨595985, by rfl⟩ : syracuseStep 794647 = 1191971) B1191971
theorem B794667 : Blo 794341 794667 := bstep (se 1 (by rfl) ⟨596000, by rfl⟩ : syracuseStep 794667 = 1192001) B1192001
theorem B794679 : Blo 794341 794679 := bstep (se 1 (by rfl) ⟨596009, by rfl⟩ : syracuseStep 794679 = 1192019) B1192019
theorem B794699 : Blo 794341 794699 := bstep (se 1 (by rfl) ⟨596024, by rfl⟩ : syracuseStep 794699 = 1192049) B1192049
theorem B8298571 : Blo 794341 8298571 := bstep (se 1 (by rfl) ⟨6223928, by rfl⟩ : syracuseStep 8298571 = 12447857) B12447857
theorem B794711 : Blo 794341 794711 := bstep (se 1 (by rfl) ⟨596033, by rfl⟩ : syracuseStep 794711 = 1192067) B1192067
theorem B794731 : Blo 794341 794731 := bstep (se 1 (by rfl) ⟨596048, by rfl⟩ : syracuseStep 794731 = 1192097) B1192097
theorem B794743 : Blo 794341 794743 := bstep (se 1 (by rfl) ⟨596057, by rfl⟩ : syracuseStep 794743 = 1192115) B1192115
theorem B794763 : Blo 794341 794763 := bstep (se 1 (by rfl) ⟨596072, by rfl⟩ : syracuseStep 794763 = 1192145) B1192145
theorem B794775 : Blo 794341 794775 := bstep (se 1 (by rfl) ⟨596081, by rfl⟩ : syracuseStep 794775 = 1192163) B1192163
theorem B794795 : Blo 794341 794795 := bstep (se 1 (by rfl) ⟨596096, by rfl⟩ : syracuseStep 794795 = 1192193) B1192193
theorem B3023027 : Blo 794341 3023027 := bstep (se 1 (by rfl) ⟨2267270, by rfl⟩ : syracuseStep 3023027 = 4534541) B4534541
theorem B794807 : Blo 794341 794807 := bstep (se 1 (by rfl) ⟨596105, by rfl⟩ : syracuseStep 794807 = 1192211) B1192211
theorem B3023041 : Blo 794341 3023041 := bstep (se 2 (by rfl) ⟨1133640, by rfl⟩ : syracuseStep 3023041 = 2267281) B2267281
theorem B794827 : Blo 794341 794827 := bstep (se 1 (by rfl) ⟨596120, by rfl⟩ : syracuseStep 794827 = 1192241) B1192241
theorem B794839 : Blo 794341 794839 := bstep (se 1 (by rfl) ⟨596129, by rfl⟩ : syracuseStep 794839 = 1192259) B1192259
theorem B794859 : Blo 794341 794859 := bstep (se 1 (by rfl) ⟨596144, by rfl⟩ : syracuseStep 794859 = 1192289) B1192289
theorem B794871 : Blo 794341 794871 := bstep (se 1 (by rfl) ⟨596153, by rfl⟩ : syracuseStep 794871 = 1192307) B1192307
theorem B794891 : Blo 794341 794891 := bstep (se 1 (by rfl) ⟨596168, by rfl⟩ : syracuseStep 794891 = 1192337) B1192337
theorem B794903 : Blo 794341 794903 := bstep (se 1 (by rfl) ⟨596177, by rfl⟩ : syracuseStep 794903 = 1192355) B1192355
theorem B794923 : Blo 794341 794923 := bstep (se 1 (by rfl) ⟨596192, by rfl⟩ : syracuseStep 794923 = 1192385) B1192385
theorem B794935 : Blo 794341 794935 := bstep (se 1 (by rfl) ⟨596201, by rfl⟩ : syracuseStep 794935 = 1192403) B1192403
theorem B794955 : Blo 794341 794955 := bstep (se 1 (by rfl) ⟨596216, by rfl⟩ : syracuseStep 794955 = 1192433) B1192433
theorem B794967 : Blo 794341 794967 := bstep (se 1 (by rfl) ⟨596225, by rfl⟩ : syracuseStep 794967 = 1192451) B1192451
theorem B6791525 : Blo 794341 6791525 := bstep (se 4 (by rfl) ⟨636705, by rfl⟩ : syracuseStep 6791525 = 1273411) B1273411
theorem B794987 : Blo 794341 794987 := bstep (se 1 (by rfl) ⟨596240, by rfl⟩ : syracuseStep 794987 = 1192481) B1192481
theorem B794999 : Blo 794341 794999 := bstep (se 1 (by rfl) ⟨596249, by rfl⟩ : syracuseStep 794999 = 1192499) B1192499
theorem B795019 : Blo 794341 795019 := bstep (se 1 (by rfl) ⟨596264, by rfl⟩ : syracuseStep 795019 = 1192529) B1192529
theorem B795031 : Blo 794341 795031 := bstep (se 1 (by rfl) ⟨596273, by rfl⟩ : syracuseStep 795031 = 1192547) B1192547
theorem B795051 : Blo 794341 795051 := bstep (se 1 (by rfl) ⟨596288, by rfl⟩ : syracuseStep 795051 = 1192577) B1192577
theorem B795063 : Blo 794341 795063 := bstep (se 1 (by rfl) ⟨596297, by rfl⟩ : syracuseStep 795063 = 1192595) B1192595
theorem B795083 : Blo 794341 795083 := bstep (se 1 (by rfl) ⟨596312, by rfl⟩ : syracuseStep 795083 = 1192625) B1192625
theorem B795095 : Blo 794341 795095 := bstep (se 1 (by rfl) ⟨596321, by rfl⟩ : syracuseStep 795095 = 1192643) B1192643
theorem B795115 : Blo 794341 795115 := bstep (se 1 (by rfl) ⟨596336, by rfl⟩ : syracuseStep 795115 = 1192673) B1192673
theorem B795127 : Blo 794341 795127 := bstep (se 1 (by rfl) ⟨596345, by rfl⟩ : syracuseStep 795127 = 1192691) B1192691
theorem B795147 : Blo 794341 795147 := bstep (se 1 (by rfl) ⟨596360, by rfl⟩ : syracuseStep 795147 = 1192721) B1192721
theorem B795159 : Blo 794341 795159 := bstep (se 1 (by rfl) ⟨596369, by rfl⟩ : syracuseStep 795159 = 1192739) B1192739
theorem B795179 : Blo 794341 795179 := bstep (se 1 (by rfl) ⟨596384, by rfl⟩ : syracuseStep 795179 = 1192769) B1192769
theorem B795191 : Blo 794341 795191 := bstep (se 1 (by rfl) ⟨596393, by rfl⟩ : syracuseStep 795191 = 1192787) B1192787
theorem B795211 : Blo 794341 795211 := bstep (se 1 (by rfl) ⟨596408, by rfl⟩ : syracuseStep 795211 = 1192817) B1192817
theorem B795223 : Blo 794341 795223 := bstep (se 1 (by rfl) ⟨596417, by rfl⟩ : syracuseStep 795223 = 1192835) B1192835
theorem B795243 : Blo 794341 795243 := bstep (se 1 (by rfl) ⟨596432, by rfl⟩ : syracuseStep 795243 = 1192865) B1192865
theorem B795255 : Blo 794341 795255 := bstep (se 1 (by rfl) ⟨596441, by rfl⟩ : syracuseStep 795255 = 1192883) B1192883
theorem B795275 : Blo 794341 795275 := bstep (se 1 (by rfl) ⟨596456, by rfl⟩ : syracuseStep 795275 = 1192913) B1192913
theorem B795287 : Blo 794341 795287 := bstep (se 1 (by rfl) ⟨596465, by rfl⟩ : syracuseStep 795287 = 1192931) B1192931
theorem B795307 : Blo 794341 795307 := bstep (se 1 (by rfl) ⟨596480, by rfl⟩ : syracuseStep 795307 = 1192961) B1192961
theorem B795319 : Blo 794341 795319 := bstep (se 1 (by rfl) ⟨596489, by rfl⟩ : syracuseStep 795319 = 1192979) B1192979
theorem B2990785 : Blo 794341 2990785 := bstep (se 2 (by rfl) ⟨1121544, by rfl⟩ : syracuseStep 2990785 = 2243089) B2243089
theorem B795339 : Blo 794341 795339 := bstep (se 1 (by rfl) ⟨596504, by rfl⟩ : syracuseStep 795339 = 1193009) B1193009
theorem B795351 : Blo 794341 795351 := bstep (se 1 (by rfl) ⟨596513, by rfl⟩ : syracuseStep 795351 = 1193027) B1193027
theorem B795371 : Blo 794341 795371 := bstep (se 1 (by rfl) ⟨596528, by rfl⟩ : syracuseStep 795371 = 1193057) B1193057
theorem B795383 : Blo 794341 795383 := bstep (se 1 (by rfl) ⟨596537, by rfl⟩ : syracuseStep 795383 = 1193075) B1193075
theorem B795403 : Blo 794341 795403 := bstep (se 1 (by rfl) ⟨596552, by rfl⟩ : syracuseStep 795403 = 1193105) B1193105
theorem B795415 : Blo 794341 795415 := bstep (se 1 (by rfl) ⟨596561, by rfl⟩ : syracuseStep 795415 = 1193123) B1193123
theorem B795435 : Blo 794341 795435 := bstep (se 1 (by rfl) ⟨596576, by rfl⟩ : syracuseStep 795435 = 1193153) B1193153
theorem B4039469 : Blo 794341 4039469 := bstep (se 3 (by rfl) ⟨757400, by rfl⟩ : syracuseStep 4039469 = 1514801) B1514801
theorem B795447 : Blo 794341 795447 := bstep (se 1 (by rfl) ⟨596585, by rfl⟩ : syracuseStep 795447 = 1193171) B1193171
theorem B795467 : Blo 794341 795467 := bstep (se 1 (by rfl) ⟨596600, by rfl⟩ : syracuseStep 795467 = 1193201) B1193201
theorem B795479 : Blo 794341 795479 := bstep (se 1 (by rfl) ⟨596609, by rfl⟩ : syracuseStep 795479 = 1193219) B1193219
theorem B893803 : Blo 794341 893803 := bstep (se 1 (by rfl) ⟨670352, by rfl⟩ : syracuseStep 893803 = 1340705) B1340705
theorem B795499 : Blo 794341 795499 := bstep (se 1 (by rfl) ⟨596624, by rfl⟩ : syracuseStep 795499 = 1193249) B1193249
theorem B795511 : Blo 794341 795511 := bstep (se 1 (by rfl) ⟨596633, by rfl⟩ : syracuseStep 795511 = 1193267) B1193267
theorem B795531 : Blo 794341 795531 := bstep (se 1 (by rfl) ⟨596648, by rfl⟩ : syracuseStep 795531 = 1193297) B1193297
theorem B795543 : Blo 794341 795543 := bstep (se 1 (by rfl) ⟨596657, by rfl⟩ : syracuseStep 795543 = 1193315) B1193315
theorem B795563 : Blo 794341 795563 := bstep (se 1 (by rfl) ⟨596672, by rfl⟩ : syracuseStep 795563 = 1193345) B1193345
theorem B4301747 : Blo 794341 4301747 := bstep (se 1 (by rfl) ⟨3226310, by rfl⟩ : syracuseStep 4301747 = 6452621) B6452621
theorem B795575 : Blo 794341 795575 := bstep (se 1 (by rfl) ⟨596681, by rfl⟩ : syracuseStep 795575 = 1193363) B1193363
theorem B795595 : Blo 794341 795595 := bstep (se 1 (by rfl) ⟨596696, by rfl⟩ : syracuseStep 795595 = 1193393) B1193393
theorem B3449803 : Blo 794341 3449803 := bstep (se 1 (by rfl) ⟨2587352, by rfl⟩ : syracuseStep 3449803 = 5174705) B5174705
theorem B893911 : Blo 794341 893911 := bstep (se 1 (by rfl) ⟨670433, by rfl⟩ : syracuseStep 893911 = 1340867) B1340867
theorem B795607 : Blo 794341 795607 := bstep (se 1 (by rfl) ⟨596705, by rfl⟩ : syracuseStep 795607 = 1193411) B1193411
theorem B795627 : Blo 794341 795627 := bstep (se 1 (by rfl) ⟨596720, by rfl⟩ : syracuseStep 795627 = 1193441) B1193441
theorem B795639 : Blo 794341 795639 := bstep (se 1 (by rfl) ⟨596729, by rfl⟩ : syracuseStep 795639 = 1193459) B1193459
theorem B1451009 : Blo 794341 1451009 := bstep (se 2 (by rfl) ⟨544128, by rfl⟩ : syracuseStep 1451009 = 1088257) B1088257
theorem B795659 : Blo 794341 795659 := bstep (se 1 (by rfl) ⟨596744, by rfl⟩ : syracuseStep 795659 = 1193489) B1193489
theorem B795671 : Blo 794341 795671 := bstep (se 1 (by rfl) ⟨596753, by rfl⟩ : syracuseStep 795671 = 1193507) B1193507
theorem B795691 : Blo 794341 795691 := bstep (se 1 (by rfl) ⟨596768, by rfl⟩ : syracuseStep 795691 = 1193537) B1193537
theorem B795703 : Blo 794341 795703 := bstep (se 1 (by rfl) ⟨596777, by rfl⟩ : syracuseStep 795703 = 1193555) B1193555
theorem B795723 : Blo 794341 795723 := bstep (se 1 (by rfl) ⟨596792, by rfl⟩ : syracuseStep 795723 = 1193585) B1193585
theorem B795735 : Blo 794341 795735 := bstep (se 1 (by rfl) ⟨596801, by rfl⟩ : syracuseStep 795735 = 1193603) B1193603
theorem B795755 : Blo 794341 795755 := bstep (se 1 (by rfl) ⟨596816, by rfl⟩ : syracuseStep 795755 = 1193633) B1193633
theorem B795767 : Blo 794341 795767 := bstep (se 1 (by rfl) ⟨596825, by rfl⟩ : syracuseStep 795767 = 1193651) B1193651
theorem B894091 : Blo 794341 894091 := bstep (se 1 (by rfl) ⟨670568, by rfl⟩ : syracuseStep 894091 = 1341137) B1341137
theorem B795787 : Blo 794341 795787 := bstep (se 1 (by rfl) ⟨596840, by rfl⟩ : syracuseStep 795787 = 1193681) B1193681
theorem B795799 : Blo 794341 795799 := bstep (se 1 (by rfl) ⟨596849, by rfl⟩ : syracuseStep 795799 = 1193699) B1193699
theorem B795819 : Blo 794341 795819 := bstep (se 1 (by rfl) ⟨596864, by rfl⟩ : syracuseStep 795819 = 1193729) B1193729
theorem B795831 : Blo 794341 795831 := bstep (se 1 (by rfl) ⟨596873, by rfl⟩ : syracuseStep 795831 = 1193747) B1193747
theorem B795851 : Blo 794341 795851 := bstep (se 1 (by rfl) ⟨596888, by rfl⟩ : syracuseStep 795851 = 1193777) B1193777
theorem B795863 : Blo 794341 795863 := bstep (se 1 (by rfl) ⟨596897, by rfl⟩ : syracuseStep 795863 = 1193795) B1193795
theorem B2270425 : Blo 794341 2270425 := bstep (se 2 (by rfl) ⟨851409, by rfl⟩ : syracuseStep 2270425 = 1702819) B1702819
theorem B795883 : Blo 794341 795883 := bstep (se 1 (by rfl) ⟨596912, by rfl⟩ : syracuseStep 795883 = 1193825) B1193825
theorem B894199 : Blo 794341 894199 := bstep (se 1 (by rfl) ⟨670649, by rfl⟩ : syracuseStep 894199 = 1341299) B1341299
theorem B795895 : Blo 794341 795895 := bstep (se 1 (by rfl) ⟨596921, by rfl⟩ : syracuseStep 795895 = 1193843) B1193843
theorem B795915 : Blo 794341 795915 := bstep (se 1 (by rfl) ⟨596936, by rfl⟩ : syracuseStep 795915 = 1193873) B1193873
theorem B795927 : Blo 794341 795927 := bstep (se 1 (by rfl) ⟨596945, by rfl⟩ : syracuseStep 795927 = 1193891) B1193891
theorem B795947 : Blo 794341 795947 := bstep (se 1 (by rfl) ⟨596960, by rfl⟩ : syracuseStep 795947 = 1193921) B1193921
theorem B795959 : Blo 794341 795959 := bstep (se 1 (by rfl) ⟨596969, by rfl⟩ : syracuseStep 795959 = 1193939) B1193939
theorem B795979 : Blo 794341 795979 := bstep (se 1 (by rfl) ⟨596984, by rfl⟩ : syracuseStep 795979 = 1193969) B1193969
theorem B795991 : Blo 794341 795991 := bstep (se 1 (by rfl) ⟨596993, by rfl⟩ : syracuseStep 795991 = 1193987) B1193987
theorem B796011 : Blo 794341 796011 := bstep (se 1 (by rfl) ⟨597008, by rfl⟩ : syracuseStep 796011 = 1194017) B1194017
theorem B796023 : Blo 794341 796023 := bstep (se 1 (by rfl) ⟨597017, by rfl⟩ : syracuseStep 796023 = 1194035) B1194035
theorem B796043 : Blo 794341 796043 := bstep (se 1 (by rfl) ⟨597032, by rfl⟩ : syracuseStep 796043 = 1194065) B1194065
theorem B796055 : Blo 794341 796055 := bstep (se 1 (by rfl) ⟨597041, by rfl⟩ : syracuseStep 796055 = 1194083) B1194083
theorem B894379 : Blo 794341 894379 := bstep (se 1 (by rfl) ⟨670784, by rfl⟩ : syracuseStep 894379 = 1341569) B1341569
theorem B796075 : Blo 794341 796075 := bstep (se 1 (by rfl) ⟨597056, by rfl⟩ : syracuseStep 796075 = 1194113) B1194113
theorem B796087 : Blo 794341 796087 := bstep (se 1 (by rfl) ⟨597065, by rfl⟩ : syracuseStep 796087 = 1194131) B1194131
theorem B796107 : Blo 794341 796107 := bstep (se 1 (by rfl) ⟨597080, by rfl⟩ : syracuseStep 796107 = 1194161) B1194161
theorem B796119 : Blo 794341 796119 := bstep (se 1 (by rfl) ⟨597089, by rfl⟩ : syracuseStep 796119 = 1194179) B1194179
theorem B796139 : Blo 794341 796139 := bstep (se 1 (by rfl) ⟨597104, by rfl⟩ : syracuseStep 796139 = 1194209) B1194209
theorem B796151 : Blo 794341 796151 := bstep (se 1 (by rfl) ⟨597113, by rfl⟩ : syracuseStep 796151 = 1194227) B1194227
theorem B796171 : Blo 794341 796171 := bstep (se 1 (by rfl) ⟨597128, by rfl⟩ : syracuseStep 796171 = 1194257) B1194257
theorem B894487 : Blo 794341 894487 := bstep (se 1 (by rfl) ⟨670865, by rfl⟩ : syracuseStep 894487 = 1341731) B1341731
theorem B796183 : Blo 794341 796183 := bstep (se 1 (by rfl) ⟨597137, by rfl⟩ : syracuseStep 796183 = 1194275) B1194275
theorem B796203 : Blo 794341 796203 := bstep (se 1 (by rfl) ⟨597152, by rfl⟩ : syracuseStep 796203 = 1194305) B1194305
theorem B796215 : Blo 794341 796215 := bstep (se 1 (by rfl) ⟨597161, by rfl⟩ : syracuseStep 796215 = 1194323) B1194323
theorem B796235 : Blo 794341 796235 := bstep (se 1 (by rfl) ⟨597176, by rfl⟩ : syracuseStep 796235 = 1194353) B1194353
theorem B796247 : Blo 794341 796247 := bstep (se 1 (by rfl) ⟨597185, by rfl⟩ : syracuseStep 796247 = 1194371) B1194371
theorem B796267 : Blo 794341 796267 := bstep (se 1 (by rfl) ⟨597200, by rfl⟩ : syracuseStep 796267 = 1194401) B1194401
theorem B796279 : Blo 794341 796279 := bstep (se 1 (by rfl) ⟨597209, by rfl⟩ : syracuseStep 796279 = 1194419) B1194419
theorem B796299 : Blo 794341 796299 := bstep (se 1 (by rfl) ⟨597224, by rfl⟩ : syracuseStep 796299 = 1194449) B1194449
theorem B796311 : Blo 794341 796311 := bstep (se 1 (by rfl) ⟨597233, by rfl⟩ : syracuseStep 796311 = 1194467) B1194467
theorem B796331 : Blo 794341 796331 := bstep (se 1 (by rfl) ⟨597248, by rfl⟩ : syracuseStep 796331 = 1194497) B1194497
theorem B796343 : Blo 794341 796343 := bstep (se 1 (by rfl) ⟨597257, by rfl⟩ : syracuseStep 796343 = 1194515) B1194515
theorem B894667 : Blo 794341 894667 := bstep (se 1 (by rfl) ⟨671000, by rfl⟩ : syracuseStep 894667 = 1342001) B1342001
theorem B796363 : Blo 794341 796363 := bstep (se 1 (by rfl) ⟨597272, by rfl⟩ : syracuseStep 796363 = 1194545) B1194545
theorem B8726221 : Blo 794341 8726221 := bstep (se 3 (by rfl) ⟨1636166, by rfl⟩ : syracuseStep 8726221 = 3272333) B3272333
theorem B796375 : Blo 794341 796375 := bstep (se 1 (by rfl) ⟨597281, by rfl⟩ : syracuseStep 796375 = 1194563) B1194563
theorem B796395 : Blo 794341 796395 := bstep (se 1 (by rfl) ⟨597296, by rfl⟩ : syracuseStep 796395 = 1194593) B1194593
theorem B796407 : Blo 794341 796407 := bstep (se 1 (by rfl) ⟨597305, by rfl⟩ : syracuseStep 796407 = 1194611) B1194611
theorem B796427 : Blo 794341 796427 := bstep (se 1 (by rfl) ⟨597320, by rfl⟩ : syracuseStep 796427 = 1194641) B1194641
theorem B796439 : Blo 794341 796439 := bstep (se 1 (by rfl) ⟨597329, by rfl⟩ : syracuseStep 796439 = 1194659) B1194659
theorem B796459 : Blo 794341 796459 := bstep (se 1 (by rfl) ⟨597344, by rfl⟩ : syracuseStep 796459 = 1194689) B1194689
theorem B894775 : Blo 794341 894775 := bstep (se 1 (by rfl) ⟨671081, by rfl⟩ : syracuseStep 894775 = 1342163) B1342163
theorem B796471 : Blo 794341 796471 := bstep (se 1 (by rfl) ⟨597353, by rfl⟩ : syracuseStep 796471 = 1194707) B1194707
theorem B2271041 : Blo 794341 2271041 := bstep (se 2 (by rfl) ⟨851640, by rfl⟩ : syracuseStep 2271041 = 1703281) B1703281
theorem B14559041 : Blo 794341 14559041 := bstep (se 2 (by rfl) ⟨5459640, by rfl⟩ : syracuseStep 14559041 = 10919281) B10919281
theorem B796491 : Blo 794341 796491 := bstep (se 1 (by rfl) ⟨597368, by rfl⟩ : syracuseStep 796491 = 1194737) B1194737
theorem B796503 : Blo 794341 796503 := bstep (se 1 (by rfl) ⟨597377, by rfl⟩ : syracuseStep 796503 = 1194755) B1194755
theorem B12887909 : Blo 794341 12887909 := bstep (se 4 (by rfl) ⟨1208241, by rfl⟩ : syracuseStep 12887909 = 2416483) B2416483
theorem B796523 : Blo 794341 796523 := bstep (se 1 (by rfl) ⟨597392, by rfl⟩ : syracuseStep 796523 = 1194785) B1194785
theorem B796535 : Blo 794341 796535 := bstep (se 1 (by rfl) ⟨597401, by rfl⟩ : syracuseStep 796535 = 1194803) B1194803
theorem B796555 : Blo 794341 796555 := bstep (se 1 (by rfl) ⟨597416, by rfl⟩ : syracuseStep 796555 = 1194833) B1194833
theorem B796567 : Blo 794341 796567 := bstep (se 1 (by rfl) ⟨597425, by rfl⟩ : syracuseStep 796567 = 1194851) B1194851
theorem B796587 : Blo 794341 796587 := bstep (se 1 (by rfl) ⟨597440, by rfl⟩ : syracuseStep 796587 = 1194881) B1194881
theorem B796599 : Blo 794341 796599 := bstep (se 1 (by rfl) ⟨597449, by rfl⟩ : syracuseStep 796599 = 1194899) B1194899
theorem B2041793 : Blo 794341 2041793 := bstep (se 2 (by rfl) ⟨765672, by rfl⟩ : syracuseStep 2041793 = 1531345) B1531345
theorem B796619 : Blo 794341 796619 := bstep (se 1 (by rfl) ⟨597464, by rfl⟩ : syracuseStep 796619 = 1194929) B1194929
theorem B796631 : Blo 794341 796631 := bstep (se 1 (by rfl) ⟨597473, by rfl⟩ : syracuseStep 796631 = 1194947) B1194947
theorem B894955 : Blo 794341 894955 := bstep (se 1 (by rfl) ⟨671216, by rfl⟩ : syracuseStep 894955 = 1342433) B1342433
theorem B796651 : Blo 794341 796651 := bstep (se 1 (by rfl) ⟨597488, by rfl⟩ : syracuseStep 796651 = 1194977) B1194977
theorem B796663 : Blo 794341 796663 := bstep (se 1 (by rfl) ⟨597497, by rfl⟩ : syracuseStep 796663 = 1194995) B1194995
theorem B796683 : Blo 794341 796683 := bstep (se 1 (by rfl) ⟨597512, by rfl⟩ : syracuseStep 796683 = 1195025) B1195025
theorem B796695 : Blo 794341 796695 := bstep (se 1 (by rfl) ⟨597521, by rfl⟩ : syracuseStep 796695 = 1195043) B1195043
theorem B796715 : Blo 794341 796715 := bstep (se 1 (by rfl) ⟨597536, by rfl⟩ : syracuseStep 796715 = 1195073) B1195073
theorem B796727 : Blo 794341 796727 := bstep (se 1 (by rfl) ⟨597545, by rfl⟩ : syracuseStep 796727 = 1195091) B1195091
theorem B3024971 : Blo 794341 3024971 := bstep (se 1 (by rfl) ⟨2268728, by rfl⟩ : syracuseStep 3024971 = 4537457) B4537457
theorem B796747 : Blo 794341 796747 := bstep (se 1 (by rfl) ⟨597560, by rfl⟩ : syracuseStep 796747 = 1195121) B1195121
theorem B895063 : Blo 794341 895063 := bstep (se 1 (by rfl) ⟨671297, by rfl⟩ : syracuseStep 895063 = 1342595) B1342595
theorem B796759 : Blo 794341 796759 := bstep (se 1 (by rfl) ⟨597569, by rfl⟩ : syracuseStep 796759 = 1195139) B1195139
theorem B3024985 : Blo 794341 3024985 := bstep (se 2 (by rfl) ⟨1134369, by rfl⟩ : syracuseStep 3024985 = 2268739) B2268739
theorem B796779 : Blo 794341 796779 := bstep (se 1 (by rfl) ⟨597584, by rfl⟩ : syracuseStep 796779 = 1195169) B1195169
theorem B796791 : Blo 794341 796791 := bstep (se 1 (by rfl) ⟨597593, by rfl⟩ : syracuseStep 796791 = 1195187) B1195187
theorem B796811 : Blo 794341 796811 := bstep (se 1 (by rfl) ⟨597608, by rfl⟩ : syracuseStep 796811 = 1195217) B1195217
theorem B4532375 : Blo 794341 4532375 := bstep (se 1 (by rfl) ⟨3399281, by rfl⟩ : syracuseStep 4532375 = 6798563) B6798563
theorem B796823 : Blo 794341 796823 := bstep (se 1 (by rfl) ⟨597617, by rfl⟩ : syracuseStep 796823 = 1195235) B1195235
theorem B796843 : Blo 794341 796843 := bstep (se 1 (by rfl) ⟨597632, by rfl⟩ : syracuseStep 796843 = 1195265) B1195265
theorem B796855 : Blo 794341 796855 := bstep (se 1 (by rfl) ⟨597641, by rfl⟩ : syracuseStep 796855 = 1195283) B1195283
theorem B796875 : Blo 794341 796875 := bstep (se 1 (by rfl) ⟨597656, by rfl⟩ : syracuseStep 796875 = 1195313) B1195313
theorem B796887 : Blo 794341 796887 := bstep (se 1 (by rfl) ⟨597665, by rfl⟩ : syracuseStep 796887 = 1195331) B1195331
theorem B796907 : Blo 794341 796907 := bstep (se 1 (by rfl) ⟨597680, by rfl⟩ : syracuseStep 796907 = 1195361) B1195361
theorem B796919 : Blo 794341 796919 := bstep (se 1 (by rfl) ⟨597689, by rfl⟩ : syracuseStep 796919 = 1195379) B1195379
theorem B895243 : Blo 794341 895243 := bstep (se 1 (by rfl) ⟨671432, by rfl⟩ : syracuseStep 895243 = 1342865) B1342865
theorem B796939 : Blo 794341 796939 := bstep (se 1 (by rfl) ⟨597704, by rfl⟩ : syracuseStep 796939 = 1195409) B1195409
theorem B796951 : Blo 794341 796951 := bstep (se 1 (by rfl) ⟨597713, by rfl⟩ : syracuseStep 796951 = 1195427) B1195427
theorem B796971 : Blo 794341 796971 := bstep (se 1 (by rfl) ⟨597728, by rfl⟩ : syracuseStep 796971 = 1195457) B1195457
theorem B796983 : Blo 794341 796983 := bstep (se 1 (by rfl) ⟨597737, by rfl⟩ : syracuseStep 796983 = 1195475) B1195475
theorem B797003 : Blo 794341 797003 := bstep (se 1 (by rfl) ⟨597752, by rfl⟩ : syracuseStep 797003 = 1195505) B1195505
theorem B797015 : Blo 794341 797015 := bstep (se 1 (by rfl) ⟨597761, by rfl⟩ : syracuseStep 797015 = 1195523) B1195523
theorem B13805923 : Blo 794341 13805923 := bstep (se 1 (by rfl) ⟨10354442, by rfl⟩ : syracuseStep 13805923 = 20708885) B20708885
theorem B797035 : Blo 794341 797035 := bstep (se 1 (by rfl) ⟨597776, by rfl⟩ : syracuseStep 797035 = 1195553) B1195553
theorem B895351 : Blo 794341 895351 := bstep (se 1 (by rfl) ⟨671513, by rfl⟩ : syracuseStep 895351 = 1343027) B1343027
theorem B797047 : Blo 794341 797047 := bstep (se 1 (by rfl) ⟨597785, by rfl⟩ : syracuseStep 797047 = 1195571) B1195571
theorem B797067 : Blo 794341 797067 := bstep (se 1 (by rfl) ⟨597800, by rfl⟩ : syracuseStep 797067 = 1195601) B1195601
theorem B797079 : Blo 794341 797079 := bstep (se 1 (by rfl) ⟨597809, by rfl⟩ : syracuseStep 797079 = 1195619) B1195619
theorem B797099 : Blo 794341 797099 := bstep (se 1 (by rfl) ⟨597824, by rfl⟩ : syracuseStep 797099 = 1195649) B1195649
theorem B797111 : Blo 794341 797111 := bstep (se 1 (by rfl) ⟨597833, by rfl⟩ : syracuseStep 797111 = 1195667) B1195667
theorem B797131 : Blo 794341 797131 := bstep (se 1 (by rfl) ⟨597848, by rfl⟩ : syracuseStep 797131 = 1195697) B1195697
theorem B797143 : Blo 794341 797143 := bstep (se 1 (by rfl) ⟨597857, by rfl⟩ : syracuseStep 797143 = 1195715) B1195715
theorem B5745113 : Blo 794341 5745113 := bstep (se 2 (by rfl) ⟨2154417, by rfl⟩ : syracuseStep 5745113 = 4308835) B4308835
theorem B797163 : Blo 794341 797163 := bstep (se 1 (by rfl) ⟨597872, by rfl⟩ : syracuseStep 797163 = 1195745) B1195745
theorem B797175 : Blo 794341 797175 := bstep (se 1 (by rfl) ⟨597881, by rfl⟩ : syracuseStep 797175 = 1195763) B1195763
theorem B797195 : Blo 794341 797195 := bstep (se 1 (by rfl) ⟨597896, by rfl⟩ : syracuseStep 797195 = 1195793) B1195793
theorem B797207 : Blo 794341 797207 := bstep (se 1 (by rfl) ⟨597905, by rfl⟩ : syracuseStep 797207 = 1195811) B1195811
theorem B895531 : Blo 794341 895531 := bstep (se 1 (by rfl) ⟨671648, by rfl⟩ : syracuseStep 895531 = 1343297) B1343297
theorem B797227 : Blo 794341 797227 := bstep (se 1 (by rfl) ⟨597920, by rfl⟩ : syracuseStep 797227 = 1195841) B1195841
theorem B797239 : Blo 794341 797239 := bstep (se 1 (by rfl) ⟨597929, by rfl⟩ : syracuseStep 797239 = 1195859) B1195859
theorem B797259 : Blo 794341 797259 := bstep (se 1 (by rfl) ⟨597944, by rfl⟩ : syracuseStep 797259 = 1195889) B1195889
theorem B797271 : Blo 794341 797271 := bstep (se 1 (by rfl) ⟨597953, by rfl⟩ : syracuseStep 797271 = 1195907) B1195907
theorem B797291 : Blo 794341 797291 := bstep (se 1 (by rfl) ⟨597968, by rfl⟩ : syracuseStep 797291 = 1195937) B1195937
theorem B797303 : Blo 794341 797303 := bstep (se 1 (by rfl) ⟨597977, by rfl⟩ : syracuseStep 797303 = 1195955) B1195955
theorem B797323 : Blo 794341 797323 := bstep (se 1 (by rfl) ⟨597992, by rfl⟩ : syracuseStep 797323 = 1195985) B1195985
theorem B895639 : Blo 794341 895639 := bstep (se 1 (by rfl) ⟨671729, by rfl⟩ : syracuseStep 895639 = 1343459) B1343459
theorem B797335 : Blo 794341 797335 := bstep (se 1 (by rfl) ⟨598001, by rfl⟩ : syracuseStep 797335 = 1196003) B1196003
theorem B797355 : Blo 794341 797355 := bstep (se 1 (by rfl) ⟨598016, by rfl⟩ : syracuseStep 797355 = 1196033) B1196033
theorem B797367 : Blo 794341 797367 := bstep (se 1 (by rfl) ⟨598025, by rfl⟩ : syracuseStep 797367 = 1196051) B1196051
theorem B797387 : Blo 794341 797387 := bstep (se 1 (by rfl) ⟨598040, by rfl⟩ : syracuseStep 797387 = 1196081) B1196081
theorem B797399 : Blo 794341 797399 := bstep (se 1 (by rfl) ⟨598049, by rfl⟩ : syracuseStep 797399 = 1196099) B1196099
theorem B797419 : Blo 794341 797419 := bstep (se 1 (by rfl) ⟨598064, by rfl⟩ : syracuseStep 797419 = 1196129) B1196129
theorem B797431 : Blo 794341 797431 := bstep (se 1 (by rfl) ⟨598073, by rfl⟩ : syracuseStep 797431 = 1196147) B1196147
theorem B797451 : Blo 794341 797451 := bstep (se 1 (by rfl) ⟨598088, by rfl⟩ : syracuseStep 797451 = 1196177) B1196177
theorem B797463 : Blo 794341 797463 := bstep (se 1 (by rfl) ⟨598097, by rfl⟩ : syracuseStep 797463 = 1196195) B1196195
theorem B797483 : Blo 794341 797483 := bstep (se 1 (by rfl) ⟨598112, by rfl⟩ : syracuseStep 797483 = 1196225) B1196225
theorem B3222317 : Blo 794341 3222317 := bstep (se 3 (by rfl) ⟨604184, by rfl⟩ : syracuseStep 3222317 = 1208369) B1208369
theorem B797495 : Blo 794341 797495 := bstep (se 1 (by rfl) ⟨598121, by rfl⟩ : syracuseStep 797495 = 1196243) B1196243
theorem B895819 : Blo 794341 895819 := bstep (se 1 (by rfl) ⟨671864, by rfl⟩ : syracuseStep 895819 = 1343729) B1343729
theorem B797515 : Blo 794341 797515 := bstep (se 1 (by rfl) ⟨598136, by rfl⟩ : syracuseStep 797515 = 1196273) B1196273
theorem B797527 : Blo 794341 797527 := bstep (se 1 (by rfl) ⟨598145, by rfl⟩ : syracuseStep 797527 = 1196291) B1196291
theorem B797547 : Blo 794341 797547 := bstep (se 1 (by rfl) ⟨598160, by rfl⟩ : syracuseStep 797547 = 1196321) B1196321
theorem B797559 : Blo 794341 797559 := bstep (se 1 (by rfl) ⟨598169, by rfl⟩ : syracuseStep 797559 = 1196339) B1196339
theorem B797579 : Blo 794341 797579 := bstep (se 1 (by rfl) ⟨598184, by rfl⟩ : syracuseStep 797579 = 1196369) B1196369
theorem B1420183 : Blo 794341 1420183 := bstep (se 1 (by rfl) ⟨1065137, by rfl⟩ : syracuseStep 1420183 = 2130275) B2130275
theorem B797591 : Blo 794341 797591 := bstep (se 1 (by rfl) ⟨598193, by rfl⟩ : syracuseStep 797591 = 1196387) B1196387
theorem B797611 : Blo 794341 797611 := bstep (se 1 (by rfl) ⟨598208, by rfl⟩ : syracuseStep 797611 = 1196417) B1196417
theorem B895927 : Blo 794341 895927 := bstep (se 1 (by rfl) ⟨671945, by rfl⟩ : syracuseStep 895927 = 1343891) B1343891
theorem B797623 : Blo 794341 797623 := bstep (se 1 (by rfl) ⟨598217, by rfl⟩ : syracuseStep 797623 = 1196435) B1196435
theorem B797643 : Blo 794341 797643 := bstep (se 1 (by rfl) ⟨598232, by rfl⟩ : syracuseStep 797643 = 1196465) B1196465
theorem B6794189 : Blo 794341 6794189 := bstep (se 3 (by rfl) ⟨1273910, by rfl⟩ : syracuseStep 6794189 = 2547821) B2547821
theorem B797655 : Blo 794341 797655 := bstep (se 1 (by rfl) ⟨598241, by rfl⟩ : syracuseStep 797655 = 1196483) B1196483
theorem B797675 : Blo 794341 797675 := bstep (se 1 (by rfl) ⟨598256, by rfl⟩ : syracuseStep 797675 = 1196513) B1196513
theorem B797687 : Blo 794341 797687 := bstep (se 1 (by rfl) ⟨598265, by rfl⟩ : syracuseStep 797687 = 1196531) B1196531
theorem B797707 : Blo 794341 797707 := bstep (se 1 (by rfl) ⟨598280, by rfl⟩ : syracuseStep 797707 = 1196561) B1196561
theorem B3025943 : Blo 794341 3025943 := bstep (se 1 (by rfl) ⟨2269457, by rfl⟩ : syracuseStep 3025943 = 4538915) B4538915
theorem B797719 : Blo 794341 797719 := bstep (se 1 (by rfl) ⟨598289, by rfl⟩ : syracuseStep 797719 = 1196579) B1196579
theorem B797739 : Blo 794341 797739 := bstep (se 1 (by rfl) ⟨598304, by rfl⟩ : syracuseStep 797739 = 1196609) B1196609
theorem B797751 : Blo 794341 797751 := bstep (se 1 (by rfl) ⟨598313, by rfl⟩ : syracuseStep 797751 = 1196627) B1196627
theorem B797771 : Blo 794341 797771 := bstep (se 1 (by rfl) ⟨598328, by rfl⟩ : syracuseStep 797771 = 1196657) B1196657
theorem B797783 : Blo 794341 797783 := bstep (se 1 (by rfl) ⟨598337, by rfl⟩ : syracuseStep 797783 = 1196675) B1196675
theorem B896107 : Blo 794341 896107 := bstep (se 1 (by rfl) ⟨672080, by rfl⟩ : syracuseStep 896107 = 1344161) B1344161
theorem B797803 : Blo 794341 797803 := bstep (se 1 (by rfl) ⟨598352, by rfl⟩ : syracuseStep 797803 = 1196705) B1196705
theorem B797815 : Blo 794341 797815 := bstep (se 1 (by rfl) ⟨598361, by rfl⟩ : syracuseStep 797815 = 1196723) B1196723
theorem B797835 : Blo 794341 797835 := bstep (se 1 (by rfl) ⟨598376, by rfl⟩ : syracuseStep 797835 = 1196753) B1196753
theorem B797847 : Blo 794341 797847 := bstep (se 1 (by rfl) ⟨598385, by rfl⟩ : syracuseStep 797847 = 1196771) B1196771
theorem B797867 : Blo 794341 797867 := bstep (se 1 (by rfl) ⟨598400, by rfl⟩ : syracuseStep 797867 = 1196801) B1196801
theorem B797879 : Blo 794341 797879 := bstep (se 1 (by rfl) ⟨598409, by rfl⟩ : syracuseStep 797879 = 1196819) B1196819
theorem B797899 : Blo 794341 797899 := bstep (se 1 (by rfl) ⟨598424, by rfl⟩ : syracuseStep 797899 = 1196849) B1196849
theorem B896215 : Blo 794341 896215 := bstep (se 1 (by rfl) ⟨672161, by rfl⟩ : syracuseStep 896215 = 1344323) B1344323
theorem B797911 : Blo 794341 797911 := bstep (se 1 (by rfl) ⟨598433, by rfl⟩ : syracuseStep 797911 = 1196867) B1196867
theorem B797931 : Blo 794341 797931 := bstep (se 1 (by rfl) ⟨598448, by rfl⟩ : syracuseStep 797931 = 1196897) B1196897
theorem B797943 : Blo 794341 797943 := bstep (se 1 (by rfl) ⟨598457, by rfl⟩ : syracuseStep 797943 = 1196915) B1196915
theorem B797963 : Blo 794341 797963 := bstep (se 1 (by rfl) ⟨598472, by rfl⟩ : syracuseStep 797963 = 1196945) B1196945
theorem B797975 : Blo 794341 797975 := bstep (se 1 (by rfl) ⟨598481, by rfl⟩ : syracuseStep 797975 = 1196963) B1196963
theorem B797995 : Blo 794341 797995 := bstep (se 1 (by rfl) ⟨598496, by rfl⟩ : syracuseStep 797995 = 1196993) B1196993
theorem B798007 : Blo 794341 798007 := bstep (se 1 (by rfl) ⟨598505, by rfl⟩ : syracuseStep 798007 = 1197011) B1197011
theorem B798027 : Blo 794341 798027 := bstep (se 1 (by rfl) ⟨598520, by rfl⟩ : syracuseStep 798027 = 1197041) B1197041
theorem B798039 : Blo 794341 798039 := bstep (se 1 (by rfl) ⟨598529, by rfl⟩ : syracuseStep 798039 = 1197059) B1197059
theorem B798059 : Blo 794341 798059 := bstep (se 1 (by rfl) ⟨598544, by rfl⟩ : syracuseStep 798059 = 1197089) B1197089
theorem B798071 : Blo 794341 798071 := bstep (se 1 (by rfl) ⟨598553, by rfl⟩ : syracuseStep 798071 = 1197107) B1197107
theorem B896395 : Blo 794341 896395 := bstep (se 1 (by rfl) ⟨672296, by rfl⟩ : syracuseStep 896395 = 1344593) B1344593
theorem B798091 : Blo 794341 798091 := bstep (se 1 (by rfl) ⟨598568, by rfl⟩ : syracuseStep 798091 = 1197137) B1197137
theorem B798103 : Blo 794341 798103 := bstep (se 1 (by rfl) ⟨598577, by rfl⟩ : syracuseStep 798103 = 1197155) B1197155
theorem B798123 : Blo 794341 798123 := bstep (se 1 (by rfl) ⟨598592, by rfl⟩ : syracuseStep 798123 = 1197185) B1197185
theorem B798135 : Blo 794341 798135 := bstep (se 1 (by rfl) ⟨598601, by rfl⟩ : syracuseStep 798135 = 1197203) B1197203
theorem B798155 : Blo 794341 798155 := bstep (se 1 (by rfl) ⟨598616, by rfl⟩ : syracuseStep 798155 = 1197233) B1197233
theorem B798167 : Blo 794341 798167 := bstep (se 1 (by rfl) ⟨598625, by rfl⟩ : syracuseStep 798167 = 1197251) B1197251
theorem B31075811 : Blo 794341 31075811 := bstep (se 1 (by rfl) ⟨23306858, by rfl⟩ : syracuseStep 31075811 = 46613717) B46613717
theorem B798187 : Blo 794341 798187 := bstep (se 1 (by rfl) ⟨598640, by rfl⟩ : syracuseStep 798187 = 1197281) B1197281
theorem B896503 : Blo 794341 896503 := bstep (se 1 (by rfl) ⟨672377, by rfl⟩ : syracuseStep 896503 = 1344755) B1344755
theorem B798199 : Blo 794341 798199 := bstep (se 1 (by rfl) ⟨598649, by rfl⟩ : syracuseStep 798199 = 1197299) B1197299
theorem B798219 : Blo 794341 798219 := bstep (se 1 (by rfl) ⟨598664, by rfl⟩ : syracuseStep 798219 = 1197329) B1197329
theorem B863767 : Blo 794341 863767 := bstep (se 1 (by rfl) ⟨647825, by rfl⟩ : syracuseStep 863767 = 1295651) B1295651
theorem B798231 : Blo 794341 798231 := bstep (se 1 (by rfl) ⟨598673, by rfl⟩ : syracuseStep 798231 = 1197347) B1197347
theorem B798251 : Blo 794341 798251 := bstep (se 1 (by rfl) ⟨598688, by rfl⟩ : syracuseStep 798251 = 1197377) B1197377
theorem B798263 : Blo 794341 798263 := bstep (se 1 (by rfl) ⟨598697, by rfl⟩ : syracuseStep 798263 = 1197395) B1197395
theorem B798283 : Blo 794341 798283 := bstep (se 1 (by rfl) ⟨598712, by rfl⟩ : syracuseStep 798283 = 1197425) B1197425
theorem B798295 : Blo 794341 798295 := bstep (se 1 (by rfl) ⟨598721, by rfl⟩ : syracuseStep 798295 = 1197443) B1197443
theorem B798315 : Blo 794341 798315 := bstep (se 1 (by rfl) ⟨598736, by rfl⟩ : syracuseStep 798315 = 1197473) B1197473
theorem B798327 : Blo 794341 798327 := bstep (se 1 (by rfl) ⟨598745, by rfl⟩ : syracuseStep 798327 = 1197491) B1197491
theorem B1191563 : Blo 794341 1191563 := bstep (se 1 (by rfl) ⟨893672, by rfl⟩ : syracuseStep 1191563 = 1787345) B1787345
theorem B1191575 : Blo 794341 1191575 := bstep (se 1 (by rfl) ⟨893681, by rfl⟩ : syracuseStep 1191575 = 1787363) B1787363
theorem B896683 : Blo 794341 896683 := bstep (se 1 (by rfl) ⟨672512, by rfl⟩ : syracuseStep 896683 = 1345025) B1345025
theorem B1191641 : Blo 794341 1191641 := bstep (se 2 (by rfl) ⟨446865, by rfl⟩ : syracuseStep 1191641 = 893731) B893731
theorem B896791 : Blo 794341 896791 := bstep (se 1 (by rfl) ⟨672593, by rfl⟩ : syracuseStep 896791 = 1345187) B1345187
theorem B1191755 : Blo 794341 1191755 := bstep (se 1 (by rfl) ⟨893816, by rfl⟩ : syracuseStep 1191755 = 1787633) B1787633
theorem B1191767 : Blo 794341 1191767 := bstep (se 1 (by rfl) ⟨893825, by rfl⟩ : syracuseStep 1191767 = 1787651) B1787651
theorem B2273113 : Blo 794341 2273113 := bstep (se 2 (by rfl) ⟨852417, by rfl⟩ : syracuseStep 2273113 = 1704835) B1704835
theorem B1191833 : Blo 794341 1191833 := bstep (se 2 (by rfl) ⟨446937, by rfl⟩ : syracuseStep 1191833 = 893875) B893875
theorem B7647155 : Blo 794341 7647155 := bstep (se 1 (by rfl) ⟨5735366, by rfl⟩ : syracuseStep 7647155 = 11470733) B11470733
theorem B896971 : Blo 794341 896971 := bstep (se 1 (by rfl) ⟨672728, by rfl⟩ : syracuseStep 896971 = 1345457) B1345457
theorem B1191947 : Blo 794341 1191947 := bstep (se 1 (by rfl) ⟨893960, by rfl⟩ : syracuseStep 1191947 = 1787921) B1787921
theorem B4534289 : Blo 794341 4534289 := bstep (se 2 (by rfl) ⟨1700358, by rfl⟩ : syracuseStep 4534289 = 3400717) B3400717
theorem B1191959 : Blo 794341 1191959 := bstep (se 1 (by rfl) ⟨893969, by rfl⟩ : syracuseStep 1191959 = 1787939) B1787939
theorem B897079 : Blo 794341 897079 := bstep (se 1 (by rfl) ⟨672809, by rfl⟩ : syracuseStep 897079 = 1345619) B1345619
theorem B1192025 : Blo 794341 1192025 := bstep (se 2 (by rfl) ⟨447009, by rfl⟩ : syracuseStep 1192025 = 894019) B894019
theorem B1192139 : Blo 794341 1192139 := bstep (se 1 (by rfl) ⟨894104, by rfl⟩ : syracuseStep 1192139 = 1788209) B1788209
theorem B1192151 : Blo 794341 1192151 := bstep (se 1 (by rfl) ⟨894113, by rfl⟩ : syracuseStep 1192151 = 1788227) B1788227
theorem B897259 : Blo 794341 897259 := bstep (se 1 (by rfl) ⟨672944, by rfl⟩ : syracuseStep 897259 = 1345889) B1345889
theorem B3027203 : Blo 794341 3027203 := bstep (se 1 (by rfl) ⟨2270402, by rfl⟩ : syracuseStep 3027203 = 4540805) B4540805
theorem B1192217 : Blo 794341 1192217 := bstep (se 2 (by rfl) ⟨447081, by rfl⟩ : syracuseStep 1192217 = 894163) B894163
theorem B897367 : Blo 794341 897367 := bstep (se 1 (by rfl) ⟨673025, by rfl⟩ : syracuseStep 897367 = 1346051) B1346051
theorem B1192331 : Blo 794341 1192331 := bstep (se 1 (by rfl) ⟨894248, by rfl⟩ : syracuseStep 1192331 = 1788497) B1788497
theorem B1192343 : Blo 794341 1192343 := bstep (se 1 (by rfl) ⟨894257, by rfl⟩ : syracuseStep 1192343 = 1788515) B1788515
theorem B1192409 : Blo 794341 1192409 := bstep (se 2 (by rfl) ⟨447153, by rfl⟩ : syracuseStep 1192409 = 894307) B894307
theorem B897547 : Blo 794341 897547 := bstep (se 1 (by rfl) ⟨673160, by rfl⟩ : syracuseStep 897547 = 1346321) B1346321
theorem B1192523 : Blo 794341 1192523 := bstep (se 1 (by rfl) ⟨894392, by rfl⟩ : syracuseStep 1192523 = 1788785) B1788785
theorem B13775435 : Blo 794341 13775435 := bstep (se 1 (by rfl) ⟨10331576, by rfl⟩ : syracuseStep 13775435 = 20663153) B20663153
theorem B1192535 : Blo 794341 1192535 := bstep (se 1 (by rfl) ⟨894401, by rfl⟩ : syracuseStep 1192535 = 1788803) B1788803
theorem B897655 : Blo 794341 897655 := bstep (se 1 (by rfl) ⟨673241, by rfl⟩ : syracuseStep 897655 = 1346483) B1346483
theorem B1192601 : Blo 794341 1192601 := bstep (se 2 (by rfl) ⟨447225, by rfl⟩ : syracuseStep 1192601 = 894451) B894451
theorem B1192715 : Blo 794341 1192715 := bstep (se 1 (by rfl) ⟨894536, by rfl⟩ : syracuseStep 1192715 = 1789073) B1789073
theorem B1192727 : Blo 794341 1192727 := bstep (se 1 (by rfl) ⟨894545, by rfl⟩ : syracuseStep 1192727 = 1789091) B1789091
theorem B897835 : Blo 794341 897835 := bstep (se 1 (by rfl) ⟨673376, by rfl⟩ : syracuseStep 897835 = 1346753) B1346753
theorem B2011979 : Blo 794341 2011979 := bstep (se 1 (by rfl) ⟨1508984, by rfl⟩ : syracuseStep 2011979 = 3017969) B3017969
theorem B1192793 : Blo 794341 1192793 := bstep (se 2 (by rfl) ⟨447297, by rfl⟩ : syracuseStep 1192793 = 894595) B894595
theorem B897943 : Blo 794341 897943 := bstep (se 1 (by rfl) ⟨673457, by rfl⟩ : syracuseStep 897943 = 1346915) B1346915
theorem B1192907 : Blo 794341 1192907 := bstep (se 1 (by rfl) ⟨894680, by rfl⟩ : syracuseStep 1192907 = 1789361) B1789361
theorem B1192919 : Blo 794341 1192919 := bstep (se 1 (by rfl) ⟨894689, by rfl⟩ : syracuseStep 1192919 = 1789379) B1789379
theorem B1192985 : Blo 794341 1192985 := bstep (se 2 (by rfl) ⟨447369, by rfl⟩ : syracuseStep 1192985 = 894739) B894739
theorem B898123 : Blo 794341 898123 := bstep (se 1 (by rfl) ⟨673592, by rfl⟩ : syracuseStep 898123 = 1347185) B1347185
theorem B1193099 : Blo 794341 1193099 := bstep (se 1 (by rfl) ⟨894824, by rfl⟩ : syracuseStep 1193099 = 1789649) B1789649
theorem B1193111 : Blo 794341 1193111 := bstep (se 1 (by rfl) ⟨894833, by rfl⟩ : syracuseStep 1193111 = 1789667) B1789667
theorem B1193177 : Blo 794341 1193177 := bstep (se 2 (by rfl) ⟨447441, by rfl⟩ : syracuseStep 1193177 = 894883) B894883
theorem B1193291 : Blo 794341 1193291 := bstep (se 1 (by rfl) ⟨894968, by rfl⟩ : syracuseStep 1193291 = 1789937) B1789937
theorem B1193303 : Blo 794341 1193303 := bstep (se 1 (by rfl) ⟨894977, by rfl⟩ : syracuseStep 1193303 = 1789955) B1789955
theorem B1193369 : Blo 794341 1193369 := bstep (se 2 (by rfl) ⟨447513, by rfl⟩ : syracuseStep 1193369 = 895027) B895027
theorem B3225091 : Blo 794341 3225091 := bstep (se 1 (by rfl) ⟨2418818, by rfl⟩ : syracuseStep 3225091 = 4837637) B4837637
theorem B1193483 : Blo 794341 1193483 := bstep (se 1 (by rfl) ⟨895112, by rfl⟩ : syracuseStep 1193483 = 1790225) B1790225
theorem B1193495 : Blo 794341 1193495 := bstep (se 1 (by rfl) ⟨895121, by rfl⟩ : syracuseStep 1193495 = 1790243) B1790243
theorem B1193561 : Blo 794341 1193561 := bstep (se 2 (by rfl) ⟨447585, by rfl⟩ : syracuseStep 1193561 = 895171) B895171
theorem B1193675 : Blo 794341 1193675 := bstep (se 1 (by rfl) ⟨895256, by rfl⟩ : syracuseStep 1193675 = 1790513) B1790513
theorem B1193687 : Blo 794341 1193687 := bstep (se 1 (by rfl) ⟨895265, by rfl⟩ : syracuseStep 1193687 = 1790531) B1790531
theorem B6043409 : Blo 794341 6043409 := bstep (se 2 (by rfl) ⟨2266278, by rfl⟩ : syracuseStep 6043409 = 4532557) B4532557
theorem B2012951 : Blo 794341 2012951 := bstep (se 1 (by rfl) ⟨1509713, by rfl⟩ : syracuseStep 2012951 = 3019427) B3019427
theorem B1193753 : Blo 794341 1193753 := bstep (se 2 (by rfl) ⟨447657, by rfl⟩ : syracuseStep 1193753 = 895315) B895315
theorem B5748515 : Blo 794341 5748515 := bstep (se 1 (by rfl) ⟨4311386, by rfl⟩ : syracuseStep 5748515 = 8622773) B8622773
theorem B1193867 : Blo 794341 1193867 := bstep (se 1 (by rfl) ⟨895400, by rfl⟩ : syracuseStep 1193867 = 1790801) B1790801
theorem B1193879 : Blo 794341 1193879 := bstep (se 1 (by rfl) ⟨895409, by rfl⟩ : syracuseStep 1193879 = 1790819) B1790819
theorem B1193945 : Blo 794341 1193945 := bstep (se 2 (by rfl) ⟨447729, by rfl⟩ : syracuseStep 1193945 = 895459) B895459
theorem B5093441 : Blo 794341 5093441 := bstep (se 2 (by rfl) ⟨1910040, by rfl⟩ : syracuseStep 5093441 = 3820081) B3820081
theorem B1194059 : Blo 794341 1194059 := bstep (se 1 (by rfl) ⟨895544, by rfl⟩ : syracuseStep 1194059 = 1791089) B1791089
theorem B1194071 : Blo 794341 1194071 := bstep (se 1 (by rfl) ⟨895553, by rfl⟩ : syracuseStep 1194071 = 1791107) B1791107
theorem B1194137 : Blo 794341 1194137 := bstep (se 2 (by rfl) ⟨447801, by rfl⟩ : syracuseStep 1194137 = 895603) B895603
theorem B1194251 : Blo 794341 1194251 := bstep (se 1 (by rfl) ⟨895688, by rfl⟩ : syracuseStep 1194251 = 1791377) B1791377
theorem B1194263 : Blo 794341 1194263 := bstep (se 1 (by rfl) ⟨895697, by rfl⟩ : syracuseStep 1194263 = 1791395) B1791395
theorem B1194329 : Blo 794341 1194329 := bstep (se 2 (by rfl) ⟨447873, by rfl⟩ : syracuseStep 1194329 = 895747) B895747
theorem B2013619 : Blo 794341 2013619 := bstep (se 1 (by rfl) ⟨1510214, by rfl⟩ : syracuseStep 2013619 = 3020429) B3020429
theorem B1194443 : Blo 794341 1194443 := bstep (se 1 (by rfl) ⟨895832, by rfl⟩ : syracuseStep 1194443 = 1791665) B1791665
theorem B1194455 : Blo 794341 1194455 := bstep (se 1 (by rfl) ⟨895841, by rfl⟩ : syracuseStep 1194455 = 1791683) B1791683
theorem B1194521 : Blo 794341 1194521 := bstep (se 2 (by rfl) ⟨447945, by rfl⟩ : syracuseStep 1194521 = 895891) B895891
theorem B2013761 : Blo 794341 2013761 := bstep (se 2 (by rfl) ⟨755160, by rfl⟩ : syracuseStep 2013761 = 1510321) B1510321
theorem B1194635 : Blo 794341 1194635 := bstep (se 1 (by rfl) ⟨895976, by rfl⟩ : syracuseStep 1194635 = 1791953) B1791953
theorem B1194647 : Blo 794341 1194647 := bstep (se 1 (by rfl) ⟨895985, by rfl⟩ : syracuseStep 1194647 = 1791971) B1791971
theorem B1194713 : Blo 794341 1194713 := bstep (se 2 (by rfl) ⟨448017, by rfl⟩ : syracuseStep 1194713 = 896035) B896035
theorem B3226391 : Blo 794341 3226391 := bstep (se 1 (by rfl) ⟨2419793, by rfl⟩ : syracuseStep 3226391 = 4839587) B4839587
theorem B1194827 : Blo 794341 1194827 := bstep (se 1 (by rfl) ⟨896120, by rfl⟩ : syracuseStep 1194827 = 1792241) B1792241
theorem B1194839 : Blo 794341 1194839 := bstep (se 1 (by rfl) ⟨896129, by rfl⟩ : syracuseStep 1194839 = 1792259) B1792259
theorem B1194905 : Blo 794341 1194905 := bstep (se 2 (by rfl) ⟨448089, by rfl⟩ : syracuseStep 1194905 = 896179) B896179
theorem B7748531 : Blo 794341 7748531 := bstep (se 1 (by rfl) ⟨5811398, by rfl⟩ : syracuseStep 7748531 = 11622797) B11622797
theorem B1195019 : Blo 794341 1195019 := bstep (se 1 (by rfl) ⟨896264, by rfl⟩ : syracuseStep 1195019 = 1792529) B1792529
theorem B1195031 : Blo 794341 1195031 := bstep (se 1 (by rfl) ⟨896273, by rfl⟩ : syracuseStep 1195031 = 1792547) B1792547
theorem B1915979 : Blo 794341 1915979 := bstep (se 1 (by rfl) ⟨1436984, by rfl⟩ : syracuseStep 1915979 = 2873969) B2873969
theorem B1195097 : Blo 794341 1195097 := bstep (se 2 (by rfl) ⟨448161, by rfl⟩ : syracuseStep 1195097 = 896323) B896323
theorem B3456179 : Blo 794341 3456179 := bstep (se 1 (by rfl) ⟨2592134, by rfl⟩ : syracuseStep 3456179 = 5184269) B5184269
theorem B1195211 : Blo 794341 1195211 := bstep (se 1 (by rfl) ⟨896408, by rfl⟩ : syracuseStep 1195211 = 1792817) B1792817
theorem B1195223 : Blo 794341 1195223 := bstep (se 1 (by rfl) ⟨896417, by rfl⟩ : syracuseStep 1195223 = 1792835) B1792835
theorem B4308185 : Blo 794341 4308185 := bstep (se 2 (by rfl) ⟨1615569, by rfl⟩ : syracuseStep 4308185 = 3231139) B3231139
theorem B1195289 : Blo 794341 1195289 := bstep (se 2 (by rfl) ⟨448233, by rfl⟩ : syracuseStep 1195289 = 896467) B896467
theorem B3030317 : Blo 794341 3030317 := bstep (se 3 (by rfl) ⟨568184, by rfl⟩ : syracuseStep 3030317 = 1136369) B1136369
theorem B3063091 : Blo 794341 3063091 := bstep (se 1 (by rfl) ⟨2297318, by rfl⟩ : syracuseStep 3063091 = 4594637) B4594637
theorem B1195403 : Blo 794341 1195403 := bstep (se 1 (by rfl) ⟨896552, by rfl⟩ : syracuseStep 1195403 = 1793105) B1793105
theorem B1195415 : Blo 794341 1195415 := bstep (se 1 (by rfl) ⟨896561, by rfl⟩ : syracuseStep 1195415 = 1793123) B1793123
theorem B1195481 : Blo 794341 1195481 := bstep (se 2 (by rfl) ⟨448305, by rfl⟩ : syracuseStep 1195481 = 896611) B896611
theorem B1195595 : Blo 794341 1195595 := bstep (se 1 (by rfl) ⟨896696, by rfl⟩ : syracuseStep 1195595 = 1793393) B1793393
theorem B1195607 : Blo 794341 1195607 := bstep (se 1 (by rfl) ⟨896705, by rfl⟩ : syracuseStep 1195607 = 1793411) B1793411
theorem B1359511 : Blo 794341 1359511 := bstep (se 1 (by rfl) ⟨1019633, by rfl⟩ : syracuseStep 1359511 = 2039267) B2039267
theorem B1195673 : Blo 794341 1195673 := bstep (se 2 (by rfl) ⟨448377, by rfl⟩ : syracuseStep 1195673 = 896755) B896755
theorem B1195787 : Blo 794341 1195787 := bstep (se 1 (by rfl) ⟨896840, by rfl⟩ : syracuseStep 1195787 = 1793681) B1793681
theorem B1195799 : Blo 794341 1195799 := bstep (se 1 (by rfl) ⟨896849, by rfl⟩ : syracuseStep 1195799 = 1793699) B1793699
theorem B2015027 : Blo 794341 2015027 := bstep (se 1 (by rfl) ⟨1511270, by rfl⟩ : syracuseStep 2015027 = 3022541) B3022541
theorem B11452225 : Blo 794341 11452225 := bstep (se 2 (by rfl) ⟨4294584, by rfl⟩ : syracuseStep 11452225 = 8589169) B8589169
theorem B1195865 : Blo 794341 1195865 := bstep (se 2 (by rfl) ⟨448449, by rfl⟩ : syracuseStep 1195865 = 896899) B896899
theorem B1195979 : Blo 794341 1195979 := bstep (se 1 (by rfl) ⟨896984, by rfl⟩ : syracuseStep 1195979 = 1793969) B1793969
theorem B1195991 : Blo 794341 1195991 := bstep (se 1 (by rfl) ⟨896993, by rfl⟩ : syracuseStep 1195991 = 1793987) B1793987
theorem B1196057 : Blo 794341 1196057 := bstep (se 2 (by rfl) ⟨448521, by rfl⟩ : syracuseStep 1196057 = 897043) B897043
theorem B3031091 : Blo 794341 3031091 := bstep (se 1 (by rfl) ⟨2273318, by rfl⟩ : syracuseStep 3031091 = 4546637) B4546637
theorem B1818713 : Blo 794341 1818713 := bstep (se 2 (by rfl) ⟨682017, by rfl⟩ : syracuseStep 1818713 = 1364035) B1364035
theorem B7258243 : Blo 794341 7258243 := bstep (se 1 (by rfl) ⟨5443682, by rfl⟩ : syracuseStep 7258243 = 10887365) B10887365
theorem B1196171 : Blo 794341 1196171 := bstep (se 1 (by rfl) ⟨897128, by rfl⟩ : syracuseStep 1196171 = 1794257) B1794257
theorem B4833431 : Blo 794341 4833431 := bstep (se 1 (by rfl) ⟨3625073, by rfl⟩ : syracuseStep 4833431 = 7250147) B7250147
theorem B1196183 : Blo 794341 1196183 := bstep (se 1 (by rfl) ⟨897137, by rfl⟩ : syracuseStep 1196183 = 1794275) B1794275
theorem B1196249 : Blo 794341 1196249 := bstep (se 2 (by rfl) ⟨448593, by rfl⟩ : syracuseStep 1196249 = 897187) B897187
theorem B2015563 : Blo 794341 2015563 := bstep (se 1 (by rfl) ⟨1511672, by rfl⟩ : syracuseStep 2015563 = 3023345) B3023345
theorem B1196363 : Blo 794341 1196363 := bstep (se 1 (by rfl) ⟨897272, by rfl⟩ : syracuseStep 1196363 = 1794545) B1794545
theorem B1196375 : Blo 794341 1196375 := bstep (se 1 (by rfl) ⟨897281, by rfl⟩ : syracuseStep 1196375 = 1794563) B1794563
theorem B1196441 : Blo 794341 1196441 := bstep (se 2 (by rfl) ⟨448665, by rfl⟩ : syracuseStep 1196441 = 897331) B897331
theorem B3686849 : Blo 794341 3686849 := bstep (se 2 (by rfl) ⟨1382568, by rfl⟩ : syracuseStep 3686849 = 2765137) B2765137
theorem B2015705 : Blo 794341 2015705 := bstep (se 2 (by rfl) ⟨755889, by rfl⟩ : syracuseStep 2015705 = 1511779) B1511779
theorem B1196555 : Blo 794341 1196555 := bstep (se 1 (by rfl) ⟨897416, by rfl⟩ : syracuseStep 1196555 = 1794833) B1794833
theorem B1196567 : Blo 794341 1196567 := bstep (se 1 (by rfl) ⟨897425, by rfl⟩ : syracuseStep 1196567 = 1794851) B1794851
theorem B1196633 : Blo 794341 1196633 := bstep (se 2 (by rfl) ⟨448737, by rfl⟩ : syracuseStep 1196633 = 897475) B897475
theorem B1196747 : Blo 794341 1196747 := bstep (se 1 (by rfl) ⟨897560, by rfl⟩ : syracuseStep 1196747 = 1795121) B1795121
theorem B1196759 : Blo 794341 1196759 := bstep (se 1 (by rfl) ⟨897569, by rfl⟩ : syracuseStep 1196759 = 1795139) B1795139
theorem B1196825 : Blo 794341 1196825 := bstep (se 2 (by rfl) ⟨448809, by rfl⟩ : syracuseStep 1196825 = 897619) B897619
theorem B1131403 : Blo 794341 1131403 := bstep (se 1 (by rfl) ⟨848552, by rfl⟩ : syracuseStep 1131403 = 1697105) B1697105
theorem B1196939 : Blo 794341 1196939 := bstep (se 1 (by rfl) ⟨897704, by rfl⟩ : syracuseStep 1196939 = 1795409) B1795409
theorem B1196951 : Blo 794341 1196951 := bstep (se 1 (by rfl) ⟨897713, by rfl⟩ : syracuseStep 1196951 = 1795427) B1795427
theorem B1197017 : Blo 794341 1197017 := bstep (se 2 (by rfl) ⟨448881, by rfl⟩ : syracuseStep 1197017 = 897763) B897763
theorem B1197131 : Blo 794341 1197131 := bstep (se 1 (by rfl) ⟨897848, by rfl⟩ : syracuseStep 1197131 = 1795697) B1795697
theorem B1197143 : Blo 794341 1197143 := bstep (se 1 (by rfl) ⟨897857, by rfl⟩ : syracuseStep 1197143 = 1795715) B1795715
theorem B9061469 : Blo 794341 9061469 := bstep (se 3 (by rfl) ⟨1699025, by rfl⟩ : syracuseStep 9061469 = 3398051) B3398051
theorem B1197209 : Blo 794341 1197209 := bstep (se 2 (by rfl) ⟨448953, by rfl⟩ : syracuseStep 1197209 = 897907) B897907
theorem B1197323 : Blo 794341 1197323 := bstep (se 1 (by rfl) ⟨897992, by rfl⟩ : syracuseStep 1197323 = 1795985) B1795985
theorem B4539665 : Blo 794341 4539665 := bstep (se 2 (by rfl) ⟨1702374, by rfl⟩ : syracuseStep 4539665 = 3404749) B3404749
theorem B2016535 : Blo 794341 2016535 := bstep (se 1 (by rfl) ⟨1512401, by rfl⟩ : syracuseStep 2016535 = 3024803) B3024803
theorem B1197335 : Blo 794341 1197335 := bstep (se 1 (by rfl) ⟨898001, by rfl⟩ : syracuseStep 1197335 = 1796003) B1796003
theorem B9684269 : Blo 794341 9684269 := bstep (se 3 (by rfl) ⟨1815800, by rfl⟩ : syracuseStep 9684269 = 3631601) B3631601
theorem B4310347 : Blo 794341 4310347 := bstep (se 1 (by rfl) ⟨3232760, by rfl⟩ : syracuseStep 4310347 = 6465521) B6465521
theorem B1197401 : Blo 794341 1197401 := bstep (se 2 (by rfl) ⟨449025, by rfl⟩ : syracuseStep 1197401 = 898051) B898051
theorem B2147735 : Blo 794341 2147735 := bstep (se 1 (by rfl) ⟨1610801, by rfl⟩ : syracuseStep 2147735 = 3221603) B3221603
theorem B1787417 : Blo 794341 1787417 := bstep (se 2 (by rfl) ⟨670281, by rfl⟩ : syracuseStep 1787417 = 1340563) B1340563
theorem B6047297 : Blo 794341 6047297 := bstep (se 2 (by rfl) ⟨2267736, by rfl⟩ : syracuseStep 6047297 = 4535473) B4535473
theorem B21841501 : Blo 794341 21841501 := bstep (se 3 (by rfl) ⟨4095281, by rfl⟩ : syracuseStep 21841501 = 8190563) B8190563
theorem B1787507 : Blo 794341 1787507 := bstep (se 1 (by rfl) ⟨1340630, by rfl⟩ : syracuseStep 1787507 = 2681261) B2681261
theorem B4081283 : Blo 794341 4081283 := bstep (se 1 (by rfl) ⟨3060962, by rfl⟩ : syracuseStep 4081283 = 6121925) B6121925
theorem B1787543 : Blo 794341 1787543 := bstep (se 1 (by rfl) ⟨1340657, by rfl⟩ : syracuseStep 1787543 = 2681315) B2681315
theorem B2016971 : Blo 794341 2016971 := bstep (se 1 (by rfl) ⟨1512728, by rfl⟩ : syracuseStep 2016971 = 3025457) B3025457
theorem B4540121 : Blo 794341 4540121 := bstep (se 2 (by rfl) ⟨1702545, by rfl⟩ : syracuseStep 4540121 = 3405091) B3405091
theorem B1787723 : Blo 794341 1787723 := bstep (se 1 (by rfl) ⟨1340792, by rfl⟩ : syracuseStep 1787723 = 2681585) B2681585
theorem B2869067 : Blo 794341 2869067 := bstep (se 1 (by rfl) ⟨2151800, by rfl⟩ : syracuseStep 2869067 = 4303601) B4303601
theorem B1787777 : Blo 794341 1787777 := bstep (se 2 (by rfl) ⟨670416, by rfl⟩ : syracuseStep 1787777 = 1340833) B1340833
theorem B2017345 : Blo 794341 2017345 := bstep (se 2 (by rfl) ⟨756504, by rfl⟩ : syracuseStep 2017345 = 1513009) B1513009
theorem B1787993 : Blo 794341 1787993 := bstep (se 2 (by rfl) ⟨670497, by rfl⟩ : syracuseStep 1787993 = 1340995) B1340995
theorem B1132633 : Blo 794341 1132633 := bstep (se 2 (by rfl) ⟨424737, by rfl⟩ : syracuseStep 1132633 = 849475) B849475
theorem B3360941 : Blo 794341 3360941 := bstep (se 3 (by rfl) ⟨630176, by rfl⟩ : syracuseStep 3360941 = 1260353) B1260353
theorem B1788083 : Blo 794341 1788083 := bstep (se 1 (by rfl) ⟨1341062, by rfl⟩ : syracuseStep 1788083 = 2682125) B2682125
theorem B1788119 : Blo 794341 1788119 := bstep (se 1 (by rfl) ⟨1341089, by rfl⟩ : syracuseStep 1788119 = 2682179) B2682179
theorem B4081985 : Blo 794341 4081985 := bstep (se 2 (by rfl) ⟨1530744, by rfl⟩ : syracuseStep 4081985 = 3061489) B3061489
theorem B3819869 : Blo 794341 3819869 := bstep (se 3 (by rfl) ⟨716225, by rfl⟩ : syracuseStep 3819869 = 1432451) B1432451
theorem B1788299 : Blo 794341 1788299 := bstep (se 1 (by rfl) ⟨1341224, by rfl⟩ : syracuseStep 1788299 = 2682449) B2682449
theorem B1788353 : Blo 794341 1788353 := bstep (se 2 (by rfl) ⟨670632, by rfl⟩ : syracuseStep 1788353 = 1341265) B1341265
theorem B2017943 : Blo 794341 2017943 := bstep (se 1 (by rfl) ⟨1513457, by rfl⟩ : syracuseStep 2017943 = 3026915) B3026915
theorem B1788569 : Blo 794341 1788569 := bstep (se 2 (by rfl) ⟨670713, by rfl⟩ : syracuseStep 1788569 = 1341427) B1341427
theorem B4311731 : Blo 794341 4311731 := bstep (se 1 (by rfl) ⟨3233798, by rfl⟩ : syracuseStep 4311731 = 6467597) B6467597
theorem B1788659 : Blo 794341 1788659 := bstep (se 1 (by rfl) ⟨1341494, by rfl⟩ : syracuseStep 1788659 = 2682989) B2682989
theorem B1788695 : Blo 794341 1788695 := bstep (se 1 (by rfl) ⟨1341521, by rfl⟩ : syracuseStep 1788695 = 2683043) B2683043
theorem B1788875 : Blo 794341 1788875 := bstep (se 1 (by rfl) ⟨1341656, by rfl⟩ : syracuseStep 1788875 = 2683313) B2683313
theorem B1133527 : Blo 794341 1133527 := bstep (se 1 (by rfl) ⟨850145, by rfl⟩ : syracuseStep 1133527 = 1700291) B1700291
theorem B1788929 : Blo 794341 1788929 := bstep (se 2 (by rfl) ⟨670848, by rfl⟩ : syracuseStep 1788929 = 1341697) B1341697
theorem B1363159 : Blo 794341 1363159 := bstep (se 1 (by rfl) ⟨1022369, by rfl⟩ : syracuseStep 1363159 = 2044739) B2044739
theorem B1789145 : Blo 794341 1789145 := bstep (se 2 (by rfl) ⟨670929, by rfl⟩ : syracuseStep 1789145 = 1341859) B1341859
theorem B10898693 : Blo 794341 10898693 := bstep (se 4 (by rfl) ⟨1021752, by rfl⟩ : syracuseStep 10898693 = 2043505) B2043505
theorem B1789235 : Blo 794341 1789235 := bstep (se 1 (by rfl) ⟨1341926, by rfl⟩ : syracuseStep 1789235 = 2683853) B2683853
theorem B1789271 : Blo 794341 1789271 := bstep (se 1 (by rfl) ⟨1341953, by rfl⟩ : syracuseStep 1789271 = 2683907) B2683907
theorem B2018753 : Blo 794341 2018753 := bstep (se 2 (by rfl) ⟨757032, by rfl⟩ : syracuseStep 2018753 = 1514065) B1514065
theorem B6049241 : Blo 794341 6049241 := bstep (se 2 (by rfl) ⟨2268465, by rfl⟩ : syracuseStep 6049241 = 4536931) B4536931
theorem B1789451 : Blo 794341 1789451 := bstep (se 1 (by rfl) ⟨1342088, by rfl⟩ : syracuseStep 1789451 = 2684177) B2684177
theorem B1134091 : Blo 794341 1134091 := bstep (se 1 (by rfl) ⟨850568, by rfl⟩ : syracuseStep 1134091 = 1701137) B1701137
theorem B1789505 : Blo 794341 1789505 := bstep (se 2 (by rfl) ⟨671064, by rfl⟩ : syracuseStep 1789505 = 1342129) B1342129
theorem B10210967 : Blo 794341 10210967 := bstep (se 1 (by rfl) ⟨7658225, by rfl⟩ : syracuseStep 10210967 = 15316451) B15316451
theorem B1724147 : Blo 794341 1724147 := bstep (se 1 (by rfl) ⟨1293110, by rfl⟩ : syracuseStep 1724147 = 2586221) B2586221
theorem B1789721 : Blo 794341 1789721 := bstep (se 2 (by rfl) ⟨671145, by rfl⟩ : syracuseStep 1789721 = 1342291) B1342291
theorem B3067723 : Blo 794341 3067723 := bstep (se 1 (by rfl) ⟨2300792, by rfl⟩ : syracuseStep 3067723 = 4601585) B4601585
theorem B4312925 : Blo 794341 4312925 := bstep (se 3 (by rfl) ⟨808673, by rfl⟩ : syracuseStep 4312925 = 1617347) B1617347
theorem B1789811 : Blo 794341 1789811 := bstep (se 1 (by rfl) ⟨1342358, by rfl⟩ : syracuseStep 1789811 = 2684717) B2684717
theorem B1789847 : Blo 794341 1789847 := bstep (se 1 (by rfl) ⟨1342385, by rfl⟩ : syracuseStep 1789847 = 2684771) B2684771
theorem B37277617 : Blo 794341 37277617 := bstep (se 2 (by rfl) ⟨13979106, by rfl⟩ : syracuseStep 37277617 = 27958213) B27958213
theorem B2019289 : Blo 794341 2019289 := bstep (se 2 (by rfl) ⟨757233, by rfl⟩ : syracuseStep 2019289 = 1514467) B1514467
theorem B5099537 : Blo 794341 5099537 := bstep (se 2 (by rfl) ⟨1912326, by rfl⟩ : syracuseStep 5099537 = 3824653) B3824653
theorem B1790027 : Blo 794341 1790027 := bstep (se 1 (by rfl) ⟨1342520, by rfl⟩ : syracuseStep 1790027 = 2685041) B2685041
theorem B1790081 : Blo 794341 1790081 := bstep (se 2 (by rfl) ⟨671280, by rfl⟩ : syracuseStep 1790081 = 1342561) B1342561
theorem B3625181 : Blo 794341 3625181 := bstep (se 3 (by rfl) ⟨679721, by rfl⟩ : syracuseStep 3625181 = 1359443) B1359443
theorem B1790297 : Blo 794341 1790297 := bstep (se 2 (by rfl) ⟨671361, by rfl⟩ : syracuseStep 1790297 = 1342723) B1342723
theorem B1790387 : Blo 794341 1790387 := bstep (se 1 (by rfl) ⟨1342790, by rfl⟩ : syracuseStep 1790387 = 2685581) B2685581
theorem B1790423 : Blo 794341 1790423 := bstep (se 1 (by rfl) ⟨1342817, by rfl⟩ : syracuseStep 1790423 = 2685635) B2685635
theorem B1790603 : Blo 794341 1790603 := bstep (se 1 (by rfl) ⟨1342952, by rfl⟩ : syracuseStep 1790603 = 2685905) B2685905
theorem B1725067 : Blo 794341 1725067 := bstep (se 1 (by rfl) ⟨1293800, by rfl⟩ : syracuseStep 1725067 = 2587601) B2587601
theorem B3396275 : Blo 794341 3396275 := bstep (se 1 (by rfl) ⟨2547206, by rfl⟩ : syracuseStep 3396275 = 5094413) B5094413
theorem B807607 : Blo 794341 807607 := bstep (se 1 (by rfl) ⟨605705, by rfl⟩ : syracuseStep 807607 = 1211411) B1211411
theorem B1790657 : Blo 794341 1790657 := bstep (se 2 (by rfl) ⟨671496, by rfl⟩ : syracuseStep 1790657 = 1342993) B1342993
theorem B905963 : Blo 794341 905963 := bstep (se 1 (by rfl) ⟨679472, by rfl⟩ : syracuseStep 905963 = 1358945) B1358945
theorem B1790873 : Blo 794341 1790873 := bstep (se 2 (by rfl) ⟨671577, by rfl⟩ : syracuseStep 1790873 = 1343155) B1343155
theorem B1135577 : Blo 794341 1135577 := bstep (se 2 (by rfl) ⟨425841, by rfl⟩ : syracuseStep 1135577 = 851683) B851683
theorem B1790963 : Blo 794341 1790963 := bstep (se 1 (by rfl) ⟨1343222, by rfl⟩ : syracuseStep 1790963 = 2686445) B2686445
theorem B1790999 : Blo 794341 1790999 := bstep (se 1 (by rfl) ⟨1343249, by rfl⟩ : syracuseStep 1790999 = 2686499) B2686499
theorem B18600995 : Blo 794341 18600995 := bstep (se 1 (by rfl) ⟨13950746, by rfl⟩ : syracuseStep 18600995 = 27901493) B27901493
theorem B2020403 : Blo 794341 2020403 := bstep (se 1 (by rfl) ⟨1515302, by rfl⟩ : syracuseStep 2020403 = 3030605) B3030605
theorem B1791179 : Blo 794341 1791179 := bstep (se 1 (by rfl) ⟨1343384, by rfl⟩ : syracuseStep 1791179 = 2686769) B2686769
theorem B1791233 : Blo 794341 1791233 := bstep (se 2 (by rfl) ⟨671712, by rfl⟩ : syracuseStep 1791233 = 1343425) B1343425
theorem B2020697 : Blo 794341 2020697 := bstep (se 2 (by rfl) ⟨757761, by rfl⟩ : syracuseStep 2020697 = 1515523) B1515523
theorem B1791449 : Blo 794341 1791449 := bstep (se 2 (by rfl) ⟨671793, by rfl⟩ : syracuseStep 1791449 = 1343587) B1343587
theorem B1791539 : Blo 794341 1791539 := bstep (se 1 (by rfl) ⟨1343654, by rfl⟩ : syracuseStep 1791539 = 2687309) B2687309
theorem B1791575 : Blo 794341 1791575 := bstep (se 1 (by rfl) ⟨1343681, by rfl⟩ : syracuseStep 1791575 = 2687363) B2687363
theorem B1136215 : Blo 794341 1136215 := bstep (se 1 (by rfl) ⟨852161, by rfl⟩ : syracuseStep 1136215 = 1704323) B1704323
theorem B1791755 : Blo 794341 1791755 := bstep (se 1 (by rfl) ⟨1343816, by rfl⟩ : syracuseStep 1791755 = 2687633) B2687633
theorem B1791809 : Blo 794341 1791809 := bstep (se 2 (by rfl) ⟨671928, by rfl⟩ : syracuseStep 1791809 = 1343857) B1343857
theorem B6117221 : Blo 794341 6117221 := bstep (se 4 (by rfl) ⟨573489, by rfl⟩ : syracuseStep 6117221 = 1146979) B1146979
theorem B1005463 : Blo 794341 1005463 := bstep (se 1 (by rfl) ⟨754097, by rfl⟩ : syracuseStep 1005463 = 1508195) B1508195
theorem B1431449 : Blo 794341 1431449 := bstep (se 2 (by rfl) ⟨536793, by rfl⟩ : syracuseStep 1431449 = 1073587) B1073587
theorem B1792025 : Blo 794341 1792025 := bstep (se 2 (by rfl) ⟨672009, by rfl⟩ : syracuseStep 1792025 = 1344019) B1344019
theorem B1792115 : Blo 794341 1792115 := bstep (se 1 (by rfl) ⟨1344086, by rfl⟩ : syracuseStep 1792115 = 2688173) B2688173
theorem B1792151 : Blo 794341 1792151 := bstep (se 1 (by rfl) ⟨1344113, by rfl⟩ : syracuseStep 1792151 = 2688227) B2688227
theorem B3233965 : Blo 794341 3233965 := bstep (se 3 (by rfl) ⟨606368, by rfl⟩ : syracuseStep 3233965 = 1212737) B1212737
theorem B1792331 : Blo 794341 1792331 := bstep (se 1 (by rfl) ⟨1344248, by rfl⟩ : syracuseStep 1792331 = 2688497) B2688497
theorem B1792385 : Blo 794341 1792385 := bstep (se 2 (by rfl) ⟨672144, by rfl⟩ : syracuseStep 1792385 = 1344289) B1344289
theorem B1792601 : Blo 794341 1792601 := bstep (se 2 (by rfl) ⟨672225, by rfl⟩ : syracuseStep 1792601 = 1344451) B1344451
theorem B1792691 : Blo 794341 1792691 := bstep (se 1 (by rfl) ⟨1344518, by rfl⟩ : syracuseStep 1792691 = 2689037) B2689037
theorem B1006283 : Blo 794341 1006283 := bstep (se 1 (by rfl) ⟨754712, by rfl⟩ : syracuseStep 1006283 = 1509425) B1509425
theorem B1792727 : Blo 794341 1792727 := bstep (se 1 (by rfl) ⟨1344545, by rfl⟩ : syracuseStep 1792727 = 2689091) B2689091
theorem B1432343 : Blo 794341 1432343 := bstep (se 1 (by rfl) ⟨1074257, by rfl⟩ : syracuseStep 1432343 = 2148515) B2148515
theorem B6052643 : Blo 794341 6052643 := bstep (se 1 (by rfl) ⟨4539482, by rfl⟩ : syracuseStep 6052643 = 9078965) B9078965
theorem B1792907 : Blo 794341 1792907 := bstep (se 1 (by rfl) ⟨1344680, by rfl⟩ : syracuseStep 1792907 = 2689361) B2689361
theorem B1792961 : Blo 794341 1792961 := bstep (se 2 (by rfl) ⟨672360, by rfl⟩ : syracuseStep 1792961 = 1344721) B1344721
theorem B4545497 : Blo 794341 4545497 := bstep (se 2 (by rfl) ⟨1704561, by rfl⟩ : syracuseStep 4545497 = 3409123) B3409123
theorem B1793177 : Blo 794341 1793177 := bstep (se 2 (by rfl) ⟨672441, by rfl⟩ : syracuseStep 1793177 = 1344883) B1344883
theorem B1531097 : Blo 794341 1531097 := bstep (se 2 (by rfl) ⟨574161, by rfl⟩ : syracuseStep 1531097 = 1148323) B1148323
theorem B1432819 : Blo 794341 1432819 := bstep (se 1 (by rfl) ⟨1074614, by rfl⟩ : syracuseStep 1432819 = 2149229) B2149229
theorem B1793267 : Blo 794341 1793267 := bstep (se 1 (by rfl) ⟨1344950, by rfl⟩ : syracuseStep 1793267 = 2689901) B2689901
theorem B1793303 : Blo 794341 1793303 := bstep (se 1 (by rfl) ⟨1344977, by rfl⟩ : syracuseStep 1793303 = 2689955) B2689955
theorem B3399043 : Blo 794341 3399043 := bstep (se 1 (by rfl) ⟨2549282, by rfl⟩ : syracuseStep 3399043 = 5098565) B5098565
theorem B1006987 : Blo 794341 1006987 := bstep (se 1 (by rfl) ⟨755240, by rfl⟩ : syracuseStep 1006987 = 1510481) B1510481
theorem B2907571 : Blo 794341 2907571 := bstep (se 1 (by rfl) ⟨2180678, by rfl⟩ : syracuseStep 2907571 = 4361357) B4361357
theorem B1793483 : Blo 794341 1793483 := bstep (se 1 (by rfl) ⟨1345112, by rfl⟩ : syracuseStep 1793483 = 2690225) B2690225
theorem B1793537 : Blo 794341 1793537 := bstep (se 2 (by rfl) ⟨672576, by rfl⟩ : syracuseStep 1793537 = 1345153) B1345153
theorem B2154073 : Blo 794341 2154073 := bstep (se 2 (by rfl) ⟨807777, by rfl⟩ : syracuseStep 2154073 = 1615555) B1615555
theorem B1007255 : Blo 794341 1007255 := bstep (se 1 (by rfl) ⟨755441, by rfl⟩ : syracuseStep 1007255 = 1510883) B1510883
theorem B1793753 : Blo 794341 1793753 := bstep (se 2 (by rfl) ⟨672657, by rfl⟩ : syracuseStep 1793753 = 1345315) B1345315
theorem B1793843 : Blo 794341 1793843 := bstep (se 1 (by rfl) ⟨1345382, by rfl⟩ : syracuseStep 1793843 = 2690765) B2690765
theorem B1793879 : Blo 794341 1793879 := bstep (se 1 (by rfl) ⟨1345409, by rfl⟩ : syracuseStep 1793879 = 2690819) B2690819
theorem B1794059 : Blo 794341 1794059 := bstep (se 1 (by rfl) ⟨1345544, by rfl⟩ : syracuseStep 1794059 = 2691089) B2691089
theorem B1794113 : Blo 794341 1794113 := bstep (se 2 (by rfl) ⟨672792, by rfl⟩ : syracuseStep 1794113 = 1345585) B1345585
theorem B1794329 : Blo 794341 1794329 := bstep (se 2 (by rfl) ⟨672873, by rfl⟩ : syracuseStep 1794329 = 1345747) B1345747
theorem B3400001 : Blo 794341 3400001 := bstep (se 2 (by rfl) ⟨1275000, by rfl⟩ : syracuseStep 3400001 = 2550001) B2550001
theorem B1007959 : Blo 794341 1007959 := bstep (se 1 (by rfl) ⟨755969, by rfl⟩ : syracuseStep 1007959 = 1511939) B1511939
theorem B4022621 : Blo 794341 4022621 := bstep (se 3 (by rfl) ⟨754241, by rfl⟩ : syracuseStep 4022621 = 1508483) B1508483
theorem B1794419 : Blo 794341 1794419 := bstep (se 1 (by rfl) ⟨1345814, by rfl⟩ : syracuseStep 1794419 = 2691629) B2691629
theorem B1794455 : Blo 794341 1794455 := bstep (se 1 (by rfl) ⟨1345841, by rfl⟩ : syracuseStep 1794455 = 2691683) B2691683
theorem B1794635 : Blo 794341 1794635 := bstep (se 1 (by rfl) ⟨1345976, by rfl⟩ : syracuseStep 1794635 = 2691953) B2691953
theorem B2482781 : Blo 794341 2482781 := bstep (se 3 (by rfl) ⟨465521, by rfl⟩ : syracuseStep 2482781 = 931043) B931043
theorem B11067997 : Blo 794341 11067997 := bstep (se 3 (by rfl) ⟨2075249, by rfl⟩ : syracuseStep 11067997 = 4150499) B4150499
theorem B1794689 : Blo 794341 1794689 := bstep (se 2 (by rfl) ⟨673008, by rfl⟩ : syracuseStep 1794689 = 1346017) B1346017
theorem B1434433 : Blo 794341 1434433 := bstep (se 2 (by rfl) ⟨537912, by rfl⟩ : syracuseStep 1434433 = 1075825) B1075825
theorem B1794905 : Blo 794341 1794905 := bstep (se 2 (by rfl) ⟨673089, by rfl⟩ : syracuseStep 1794905 = 1346179) B1346179
theorem B1794995 : Blo 794341 1794995 := bstep (se 1 (by rfl) ⟨1346246, by rfl⟩ : syracuseStep 1794995 = 2692493) B2692493
theorem B1795031 : Blo 794341 1795031 := bstep (se 1 (by rfl) ⟨1346273, by rfl⟩ : syracuseStep 1795031 = 2692547) B2692547
theorem B1696907 : Blo 794341 1696907 := bstep (se 1 (by rfl) ⟨1272680, by rfl⟩ : syracuseStep 1696907 = 2545361) B2545361
theorem B1795211 : Blo 794341 1795211 := bstep (se 1 (by rfl) ⟨1346408, by rfl⟩ : syracuseStep 1795211 = 2692817) B2692817
theorem B1795265 : Blo 794341 1795265 := bstep (se 2 (by rfl) ⟨673224, by rfl⟩ : syracuseStep 1795265 = 1346449) B1346449
theorem B2876737 : Blo 794341 2876737 := bstep (se 2 (by rfl) ⟨1078776, by rfl⟩ : syracuseStep 2876737 = 2157553) B2157553
theorem B1795481 : Blo 794341 1795481 := bstep (se 2 (by rfl) ⟨673305, by rfl⟩ : syracuseStep 1795481 = 1346611) B1346611
theorem B1697267 : Blo 794341 1697267 := bstep (se 1 (by rfl) ⟨1272950, by rfl⟩ : syracuseStep 1697267 = 2545901) B2545901
theorem B1795571 : Blo 794341 1795571 := bstep (se 1 (by rfl) ⟨1346678, by rfl⟩ : syracuseStep 1795571 = 2693357) B2693357
theorem B1795607 : Blo 794341 1795607 := bstep (se 1 (by rfl) ⟨1346705, by rfl⟩ : syracuseStep 1795607 = 2693411) B2693411
theorem B1795787 : Blo 794341 1795787 := bstep (se 1 (by rfl) ⟨1346840, by rfl⟩ : syracuseStep 1795787 = 2693681) B2693681
theorem B1795841 : Blo 794341 1795841 := bstep (se 2 (by rfl) ⟨673440, by rfl⟩ : syracuseStep 1795841 = 1346881) B1346881
theorem B6448913 : Blo 794341 6448913 := bstep (se 2 (by rfl) ⟨2418342, by rfl⟩ : syracuseStep 6448913 = 4836685) B4836685
theorem B1435457 : Blo 794341 1435457 := bstep (se 2 (by rfl) ⟨538296, by rfl⟩ : syracuseStep 1435457 = 1076593) B1076593
theorem B3401675 : Blo 794341 3401675 := bstep (se 1 (by rfl) ⟨2551256, by rfl⟩ : syracuseStep 3401675 = 5102513) B5102513
theorem B1796057 : Blo 794341 1796057 := bstep (se 2 (by rfl) ⟨673521, by rfl⟩ : syracuseStep 1796057 = 1347043) B1347043
theorem B1009675 : Blo 794341 1009675 := bstep (se 1 (by rfl) ⟨757256, by rfl⟩ : syracuseStep 1009675 = 1514513) B1514513
theorem B3827729 : Blo 794341 3827729 := bstep (se 2 (by rfl) ⟨1435398, by rfl⟩ : syracuseStep 3827729 = 2870797) B2870797
theorem B1796147 : Blo 794341 1796147 := bstep (se 1 (by rfl) ⟨1347110, by rfl⟩ : syracuseStep 1796147 = 2694221) B2694221
theorem B1796183 : Blo 794341 1796183 := bstep (se 1 (by rfl) ⟨1347137, by rfl⟩ : syracuseStep 1796183 = 2694275) B2694275
theorem B2681153 : Blo 794341 2681153 := bstep (se 2 (by rfl) ⟨1005432, by rfl⟩ : syracuseStep 2681153 = 2010865) B2010865
theorem B1632599 : Blo 794341 1632599 := bstep (se 1 (by rfl) ⟨1224449, by rfl⟩ : syracuseStep 1632599 = 2448899) B2448899
theorem B4024727 : Blo 794341 4024727 := bstep (se 1 (by rfl) ⟨3018545, by rfl⟩ : syracuseStep 4024727 = 6037091) B6037091
theorem B1534423 : Blo 794341 1534423 := bstep (se 1 (by rfl) ⟨1150817, by rfl⟩ : syracuseStep 1534423 = 2301635) B2301635
theorem B7269041 : Blo 794341 7269041 := bstep (se 2 (by rfl) ⟨2725890, by rfl⟩ : syracuseStep 7269041 = 5451781) B5451781
theorem B1436467 : Blo 794341 1436467 := bstep (se 1 (by rfl) ⟨1077350, by rfl⟩ : syracuseStep 1436467 = 2154701) B2154701
theorem B2681693 : Blo 794341 2681693 := bstep (se 3 (by rfl) ⟨502817, by rfl⟩ : syracuseStep 2681693 = 1005635) B1005635
theorem B5106563 : Blo 794341 5106563 := bstep (se 1 (by rfl) ⟨3829922, by rfl⟩ : syracuseStep 5106563 = 7659845) B7659845
theorem B1076171 : Blo 794341 1076171 := bstep (se 1 (by rfl) ⟨807128, by rfl⟩ : syracuseStep 1076171 = 1614257) B1614257
theorem B1633241 : Blo 794341 1633241 := bstep (se 2 (by rfl) ⟨612465, by rfl⟩ : syracuseStep 1633241 = 1224931) B1224931
theorem B10218757 : Blo 794341 10218757 := bstep (se 4 (by rfl) ⟨958008, by rfl⟩ : syracuseStep 10218757 = 1916017) B1916017
theorem B1699265 : Blo 794341 1699265 := bstep (se 2 (by rfl) ⟨637224, by rfl⟩ : syracuseStep 1699265 = 1274449) B1274449
theorem B1273495 : Blo 794341 1273495 := bstep (se 1 (by rfl) ⟨955121, by rfl⟩ : syracuseStep 1273495 = 1910243) B1910243
theorem B2420375 : Blo 794341 2420375 := bstep (se 1 (by rfl) ⟨1815281, by rfl⟩ : syracuseStep 2420375 = 3630563) B3630563
theorem B2682827 : Blo 794341 2682827 := bstep (se 1 (by rfl) ⟨2012120, by rfl⟩ : syracuseStep 2682827 = 4024241) B4024241
theorem B2551769 : Blo 794341 2551769 := bstep (se 2 (by rfl) ⟨956913, by rfl⟩ : syracuseStep 2551769 = 1913827) B1913827
theorem B6057989 : Blo 794341 6057989 := bstep (se 4 (by rfl) ⟨567936, by rfl⟩ : syracuseStep 6057989 = 1135873) B1135873
theorem B1274059 : Blo 794341 1274059 := bstep (se 1 (by rfl) ⟨955544, by rfl⟩ : syracuseStep 1274059 = 1911089) B1911089
theorem B2683097 : Blo 794341 2683097 := bstep (se 2 (by rfl) ⟨1006161, by rfl⟩ : syracuseStep 2683097 = 2012323) B2012323
theorem B1700119 : Blo 794341 1700119 := bstep (se 1 (by rfl) ⟨1275089, by rfl⟩ : syracuseStep 1700119 = 2550179) B2550179
theorem B1438067 : Blo 794341 1438067 := bstep (se 1 (by rfl) ⟨1078550, by rfl⟩ : syracuseStep 1438067 = 2157101) B2157101
theorem B848279 : Blo 794341 848279 := bstep (se 1 (by rfl) ⟨636209, by rfl⟩ : syracuseStep 848279 = 1272419) B1272419
theorem B3404339 : Blo 794341 3404339 := bstep (se 1 (by rfl) ⟨2553254, by rfl⟩ : syracuseStep 3404339 = 5106509) B5106509
theorem B1635073 : Blo 794341 1635073 := bstep (se 2 (by rfl) ⟨613152, by rfl⟩ : syracuseStep 1635073 = 1226305) B1226305
theorem B3633923 : Blo 794341 3633923 := bstep (se 1 (by rfl) ⟨2725442, by rfl⟩ : syracuseStep 3633923 = 5450885) B5450885
theorem B2683799 : Blo 794341 2683799 := bstep (se 1 (by rfl) ⟨2012849, by rfl⟩ : syracuseStep 2683799 = 4025699) B4025699
theorem B2552897 : Blo 794341 2552897 := bstep (se 2 (by rfl) ⟨957336, by rfl⟩ : syracuseStep 2552897 = 1914673) B1914673
theorem B6812747 : Blo 794341 6812747 := bstep (se 1 (by rfl) ⟨5109560, by rfl⟩ : syracuseStep 6812747 = 10219121) B10219121
theorem B2553049 : Blo 794341 2553049 := bstep (se 2 (by rfl) ⟨957393, by rfl⟩ : syracuseStep 2553049 = 1914787) B1914787
theorem B1340759 : Blo 794341 1340759 := bstep (se 1 (by rfl) ⟨1005569, by rfl⟩ : syracuseStep 1340759 = 2011139) B2011139
theorem B5600663 : Blo 794341 5600663 := bstep (se 1 (by rfl) ⟨4200497, by rfl⟩ : syracuseStep 5600663 = 8400995) B8400995
theorem B2684339 : Blo 794341 2684339 := bstep (se 1 (by rfl) ⟨2013254, by rfl⟩ : syracuseStep 2684339 = 4026509) B4026509
theorem B1701299 : Blo 794341 1701299 := bstep (se 1 (by rfl) ⟨1275974, by rfl⟩ : syracuseStep 1701299 = 2551949) B2551949
theorem B1340887 : Blo 794341 1340887 := bstep (se 1 (by rfl) ⟨1005665, by rfl⟩ : syracuseStep 1340887 = 2011331) B2011331
theorem B8713763 : Blo 794341 8713763 := bstep (se 1 (by rfl) ⟨6535322, by rfl⟩ : syracuseStep 8713763 = 13070645) B13070645
theorem B849547 : Blo 794341 849547 := bstep (se 1 (by rfl) ⟨637160, by rfl⟩ : syracuseStep 849547 = 1274321) B1274321
theorem B1275545 : Blo 794341 1275545 := bstep (se 2 (by rfl) ⟨478329, by rfl⟩ : syracuseStep 1275545 = 956659) B956659
theorem B2684609 : Blo 794341 2684609 := bstep (se 2 (by rfl) ⟨1006728, by rfl⟩ : syracuseStep 2684609 = 2013457) B2013457
theorem B4028291 : Blo 794341 4028291 := bstep (se 1 (by rfl) ⟨3021218, by rfl⟩ : syracuseStep 4028291 = 6042437) B6042437
theorem B3405827 : Blo 794341 3405827 := bstep (se 1 (by rfl) ⟨2554370, by rfl⟩ : syracuseStep 3405827 = 5108741) B5108741
theorem B1341515 : Blo 794341 1341515 := bstep (se 1 (by rfl) ⟨1006136, by rfl⟩ : syracuseStep 1341515 = 2012273) B2012273
theorem B1341643 : Blo 794341 1341643 := bstep (se 1 (by rfl) ⟨1006232, by rfl⟩ : syracuseStep 1341643 = 2012465) B2012465
theorem B2685149 : Blo 794341 2685149 := bstep (se 3 (by rfl) ⟨503465, by rfl⟩ : syracuseStep 2685149 = 1006931) B1006931
theorem B1341785 : Blo 794341 1341785 := bstep (se 2 (by rfl) ⟨503169, by rfl⟩ : syracuseStep 1341785 = 1006339) B1006339
theorem B850295 : Blo 794341 850295 := bstep (se 1 (by rfl) ⟨637721, by rfl⟩ : syracuseStep 850295 = 1275443) B1275443
theorem B6060419 : Blo 794341 6060419 := bstep (se 1 (by rfl) ⟨4545314, by rfl⟩ : syracuseStep 6060419 = 9090629) B9090629
theorem B1210777 : Blo 794341 1210777 := bstep (se 2 (by rfl) ⟨454041, by rfl⟩ : syracuseStep 1210777 = 908083) B908083
theorem B1341913 : Blo 794341 1341913 := bstep (se 2 (by rfl) ⟨503217, by rfl⟩ : syracuseStep 1341913 = 1006435) B1006435
theorem B4094509 : Blo 794341 4094509 := bstep (se 3 (by rfl) ⟨767720, by rfl⟩ : syracuseStep 4094509 = 1535441) B1535441
theorem B4356709 : Blo 794341 4356709 := bstep (se 4 (by rfl) ⟨408441, by rfl⟩ : syracuseStep 4356709 = 816883) B816883
theorem B1702529 : Blo 794341 1702529 := bstep (se 2 (by rfl) ⟨638448, by rfl⟩ : syracuseStep 1702529 = 1276897) B1276897
theorem B1342487 : Blo 794341 1342487 := bstep (se 1 (by rfl) ⟨1006865, by rfl⟩ : syracuseStep 1342487 = 2013731) B2013731
theorem B1342615 : Blo 794341 1342615 := bstep (se 1 (by rfl) ⟨1006961, by rfl⟩ : syracuseStep 1342615 = 2013923) B2013923
theorem B2423987 : Blo 794341 2423987 := bstep (se 1 (by rfl) ⟨1817990, by rfl⟩ : syracuseStep 2423987 = 3635981) B3635981
theorem B2686283 : Blo 794341 2686283 := bstep (se 1 (by rfl) ⟨2014712, by rfl⟩ : syracuseStep 2686283 = 4029425) B4029425
theorem B818635 : Blo 794341 818635 := bstep (se 1 (by rfl) ⟨613976, by rfl⟩ : syracuseStep 818635 = 1227953) B1227953
theorem B3636697 : Blo 794341 3636697 := bstep (se 2 (by rfl) ⟨1363761, by rfl⟩ : syracuseStep 3636697 = 2727523) B2727523
theorem B9698777 : Blo 794341 9698777 := bstep (se 2 (by rfl) ⟨3637041, by rfl⟩ : syracuseStep 9698777 = 7274083) B7274083
theorem B3833419 : Blo 794341 3833419 := bstep (se 1 (by rfl) ⟨2875064, by rfl⟩ : syracuseStep 3833419 = 5750129) B5750129
theorem B2686553 : Blo 794341 2686553 := bstep (se 2 (by rfl) ⟨1007457, by rfl⟩ : syracuseStep 2686553 = 2014915) B2014915
theorem B1703639 : Blo 794341 1703639 := bstep (se 1 (by rfl) ⟨1277729, by rfl⟩ : syracuseStep 1703639 = 2555459) B2555459
theorem B11501297 : Blo 794341 11501297 := bstep (se 2 (by rfl) ⟨4312986, by rfl⟩ : syracuseStep 11501297 = 8625973) B8625973
theorem B1343243 : Blo 794341 1343243 := bstep (se 1 (by rfl) ⟨1007432, by rfl⟩ : syracuseStep 1343243 = 2014865) B2014865
theorem B1343371 : Blo 794341 1343371 := bstep (se 1 (by rfl) ⟨1007528, by rfl⟩ : syracuseStep 1343371 = 2015057) B2015057
theorem B2555869 : Blo 794341 2555869 := bstep (se 3 (by rfl) ⟨479225, by rfl⟩ : syracuseStep 2555869 = 958451) B958451
theorem B13598765 : Blo 794341 13598765 := bstep (se 3 (by rfl) ⟨2549768, by rfl⟩ : syracuseStep 13598765 = 5099537) B5099537
theorem B2293879 : Blo 794341 2293879 := bstep (se 1 (by rfl) ⟨1720409, by rfl⟩ : syracuseStep 2293879 = 3440819) B3440819
theorem B1704083 : Blo 794341 1704083 := bstep (se 1 (by rfl) ⟨1278062, by rfl⟩ : syracuseStep 1704083 = 2556125) B2556125
theorem B4849901 : Blo 794341 4849901 := bstep (se 3 (by rfl) ⟨909356, by rfl⟩ : syracuseStep 4849901 = 1818713) B1818713
theorem B4030721 : Blo 794341 4030721 := bstep (se 2 (by rfl) ⟨1511520, by rfl⟩ : syracuseStep 4030721 = 3023041) B3023041
theorem B2457899 : Blo 794341 2457899 := bstep (se 1 (by rfl) ⟨1843424, by rfl⟩ : syracuseStep 2457899 = 3686849) B3686849
theorem B1343803 : Blo 794341 1343803 := bstep (se 1 (by rfl) ⟨1007852, by rfl⟩ : syracuseStep 1343803 = 2015705) B2015705
theorem B6816059 : Blo 794341 6816059 := bstep (se 1 (by rfl) ⟨5112044, by rfl⟩ : syracuseStep 6816059 = 10224089) B10224089
theorem B2687417 : Blo 794341 2687417 := bstep (se 2 (by rfl) ⟨1007781, by rfl⟩ : syracuseStep 2687417 = 2015563) B2015563
theorem B1343945 : Blo 794341 1343945 := bstep (se 2 (by rfl) ⟨503979, by rfl⟩ : syracuseStep 1343945 = 1007959) B1007959
theorem B1245755 : Blo 794341 1245755 := bstep (se 1 (by rfl) ⟨934316, by rfl⟩ : syracuseStep 1245755 = 1868633) B1868633
theorem B2556535 : Blo 794341 2556535 := bstep (se 1 (by rfl) ⟨1917401, by rfl⟩ : syracuseStep 2556535 = 3834803) B3834803
theorem B2294419 : Blo 794341 2294419 := bstep (se 1 (by rfl) ⟨1720814, by rfl⟩ : syracuseStep 2294419 = 3441629) B3441629
theorem B4653883 : Blo 794341 4653883 := bstep (se 1 (by rfl) ⟨3490412, by rfl⟩ : syracuseStep 4653883 = 6980825) B6980825
theorem B6456179 : Blo 794341 6456179 := bstep (se 1 (by rfl) ⟨4842134, by rfl⟩ : syracuseStep 6456179 = 9684269) B9684269
theorem B1180535 : Blo 794341 1180535 := bstep (se 1 (by rfl) ⟨885401, by rfl⟩ : syracuseStep 1180535 = 1770803) B1770803
theorem B2688011 : Blo 794341 2688011 := bstep (se 1 (by rfl) ⟨2016008, by rfl⟩ : syracuseStep 2688011 = 4032017) B4032017
theorem B4031531 : Blo 794341 4031531 := bstep (se 1 (by rfl) ⟨3023648, by rfl⟩ : syracuseStep 4031531 = 6047297) B6047297
theorem B2262077 : Blo 794341 2262077 := bstep (se 3 (by rfl) ⟨424139, by rfl⟩ : syracuseStep 2262077 = 848279) B848279
theorem B2720855 : Blo 794341 2720855 := bstep (se 1 (by rfl) ⟨2040641, by rfl⟩ : syracuseStep 2720855 = 4081283) B4081283
theorem B2688119 : Blo 794341 2688119 := bstep (se 1 (by rfl) ⟨2016089, by rfl⟩ : syracuseStep 2688119 = 4032179) B4032179
theorem B1344647 : Blo 794341 1344647 := bstep (se 1 (by rfl) ⟨1008485, by rfl⟩ : syracuseStep 1344647 = 2016971) B2016971
theorem B1508537 : Blo 794341 1508537 := bstep (se 2 (by rfl) ⟨565701, by rfl⟩ : syracuseStep 1508537 = 1131403) B1131403
theorem B4851089 : Blo 794341 4851089 := bstep (se 2 (by rfl) ⟨1819158, by rfl⟩ : syracuseStep 4851089 = 3638317) B3638317
theorem B2721323 : Blo 794341 2721323 := bstep (se 1 (by rfl) ⟨2040992, by rfl⟩ : syracuseStep 2721323 = 4081985) B4081985
theorem B2688713 : Blo 794341 2688713 := bstep (se 2 (by rfl) ⟨1008267, by rfl⟩ : syracuseStep 2688713 = 2016535) B2016535
theorem B3835649 : Blo 794341 3835649 := bstep (se 2 (by rfl) ⟨1438368, by rfl⟩ : syracuseStep 3835649 = 2876737) B2876737
theorem B1345295 : Blo 794341 1345295 := bstep (se 1 (by rfl) ⟨1008971, by rfl⟩ : syracuseStep 1345295 = 2017943) B2017943
theorem B6457477 : Blo 794341 6457477 := bstep (se 4 (by rfl) ⟨605388, by rfl⟩ : syracuseStep 6457477 = 1210777) B1210777
theorem B15337673 : Blo 794341 15337673 := bstep (se 2 (by rfl) ⟨5751627, by rfl⟩ : syracuseStep 15337673 = 11503255) B11503255
theorem B11634961 : Blo 794341 11634961 := bstep (se 2 (by rfl) ⟨4363110, by rfl⟩ : syracuseStep 11634961 = 8726221) B8726221
theorem B1345835 : Blo 794341 1345835 := bstep (se 1 (by rfl) ⟨1009376, by rfl⟩ : syracuseStep 1345835 = 2018753) B2018753
theorem B1509691 : Blo 794341 1509691 := bstep (se 1 (by rfl) ⟨1132268, by rfl⟩ : syracuseStep 1509691 = 2264537) B2264537
theorem B4032827 : Blo 794341 4032827 := bstep (se 1 (by rfl) ⟨3024620, by rfl⟩ : syracuseStep 4032827 = 6049241) B6049241
theorem B2689415 : Blo 794341 2689415 := bstep (se 1 (by rfl) ⟨2017061, by rfl⟩ : syracuseStep 2689415 = 4034123) B4034123
theorem B4032989 : Blo 794341 4032989 := bstep (se 3 (by rfl) ⟨756185, by rfl⟩ : syracuseStep 4032989 = 1512371) B1512371
theorem B1149431 : Blo 794341 1149431 := bstep (se 1 (by rfl) ⟨862073, by rfl⟩ : syracuseStep 1149431 = 1724147) B1724147
theorem B1346233 : Blo 794341 1346233 := bstep (se 2 (by rfl) ⟨504837, by rfl⟩ : syracuseStep 1346233 = 1009675) B1009675
theorem B2689793 : Blo 794341 2689793 := bstep (se 2 (by rfl) ⟨1008672, by rfl⟩ : syracuseStep 2689793 = 2017345) B2017345
theorem B1510177 : Blo 794341 1510177 := bstep (se 2 (by rfl) ⟨566316, by rfl⟩ : syracuseStep 1510177 = 1132633) B1132633
theorem B4033313 : Blo 794341 4033313 := bstep (se 2 (by rfl) ⟨1512492, by rfl⟩ : syracuseStep 4033313 = 3024985) B3024985
theorem B3017681 : Blo 794341 3017681 := bstep (se 2 (by rfl) ⟨1131630, by rfl⟩ : syracuseStep 3017681 = 2263261) B2263261
theorem B4525085 : Blo 794341 4525085 := bstep (se 3 (by rfl) ⟨848453, by rfl⟩ : syracuseStep 4525085 = 1696907) B1696907
theorem B2264183 : Blo 794341 2264183 := bstep (se 1 (by rfl) ⟨1698137, by rfl⟩ : syracuseStep 2264183 = 3396275) B3396275
theorem B3017999 : Blo 794341 3017999 := bstep (se 1 (by rfl) ⟨2263499, by rfl⟩ : syracuseStep 3017999 = 4526999) B4526999
theorem B1346935 : Blo 794341 1346935 := bstep (se 1 (by rfl) ⟨1010201, by rfl⟩ : syracuseStep 1346935 = 2020403) B2020403
theorem B1969679 : Blo 794341 1969679 := bstep (se 1 (by rfl) ⟨1477259, by rfl⟩ : syracuseStep 1969679 = 2954519) B2954519
theorem B2493985 : Blo 794341 2493985 := bstep (se 2 (by rfl) ⟨935244, by rfl⟩ : syracuseStep 2493985 = 1870489) B1870489
theorem B2690603 : Blo 794341 2690603 := bstep (se 1 (by rfl) ⟨2017952, by rfl⟩ : syracuseStep 2690603 = 4035905) B4035905
theorem B1347131 : Blo 794341 1347131 := bstep (se 1 (by rfl) ⟨1010348, by rfl⟩ : syracuseStep 1347131 = 2020697) B2020697
theorem B4034285 : Blo 794341 4034285 := bstep (se 3 (by rfl) ⟨756428, by rfl⟩ : syracuseStep 4034285 = 1512857) B1512857
theorem B1969921 : Blo 794341 1969921 := bstep (se 2 (by rfl) ⟨738720, by rfl⟩ : syracuseStep 1969921 = 1477441) B1477441
theorem B6033203 : Blo 794341 6033203 := bstep (se 1 (by rfl) ⟨4524902, by rfl⟩ : syracuseStep 6033203 = 9049805) B9049805
theorem B954299 : Blo 794341 954299 := bstep (se 1 (by rfl) ⟨715724, by rfl⟩ : syracuseStep 954299 = 1431449) B1431449
theorem B1511369 : Blo 794341 1511369 := bstep (se 2 (by rfl) ⟨566763, by rfl⟩ : syracuseStep 1511369 = 1133527) B1133527
theorem B8720389 : Blo 794341 8720389 := bstep (se 4 (by rfl) ⟨817536, by rfl⟩ : syracuseStep 8720389 = 1635073) B1635073
theorem B4035095 : Blo 794341 4035095 := bstep (se 1 (by rfl) ⟨3026321, by rfl⟩ : syracuseStep 4035095 = 6052643) B6052643
theorem B1512083 : Blo 794341 1512083 := bstep (se 1 (by rfl) ⟨1134062, by rfl⟩ : syracuseStep 1512083 = 2268125) B2268125
theorem B1512121 : Blo 794341 1512121 := bstep (se 2 (by rfl) ⟨567045, by rfl⟩ : syracuseStep 1512121 = 1134091) B1134091
theorem B31462181 : Blo 794341 31462181 := bstep (se 4 (by rfl) ⟨2949579, by rfl⟩ : syracuseStep 31462181 = 5899159) B5899159
theorem B7574309 : Blo 794341 7574309 := bstep (se 4 (by rfl) ⟨710091, by rfl⟩ : syracuseStep 7574309 = 1420183) B1420183
theorem B1020731 : Blo 794341 1020731 := bstep (se 1 (by rfl) ⟨765548, by rfl⟩ : syracuseStep 1020731 = 1531097) B1531097
theorem B2691899 : Blo 794341 2691899 := bstep (se 1 (by rfl) ⟨2018924, by rfl⟩ : syracuseStep 2691899 = 4037849) B4037849
theorem B2692385 : Blo 794341 2692385 := bstep (se 2 (by rfl) ⟨1009644, by rfl⟩ : syracuseStep 2692385 = 2019289) B2019289
theorem B2266667 : Blo 794341 2266667 := bstep (se 1 (by rfl) ⟨1700000, by rfl⟩ : syracuseStep 2266667 = 3400001) B3400001
theorem B4527683 : Blo 794341 4527683 := bstep (se 1 (by rfl) ⟨3395762, by rfl⟩ : syracuseStep 4527683 = 6791525) B6791525
theorem B2692979 : Blo 794341 2692979 := bstep (se 1 (by rfl) ⟨2019734, by rfl⟩ : syracuseStep 2692979 = 4039469) B4039469
theorem B19666961 : Blo 794341 19666961 := bstep (se 2 (by rfl) ⟨7375110, by rfl⟩ : syracuseStep 19666961 = 14750221) B14750221
theorem B2300089 : Blo 794341 2300089 := bstep (se 2 (by rfl) ⟨862533, by rfl⟩ : syracuseStep 2300089 = 1725067) B1725067
theorem B26482997 : Blo 794341 26482997 := bstep (se 5 (by rfl) ⟨1241390, by rfl⟩ : syracuseStep 26482997 = 2482781) B2482781
theorem B2267453 : Blo 794341 2267453 := bstep (se 3 (by rfl) ⟨425147, by rfl⟩ : syracuseStep 2267453 = 850295) B850295
theorem B4299275 : Blo 794341 4299275 := bstep (se 1 (by rfl) ⟨3224456, by rfl⟩ : syracuseStep 4299275 = 6448913) B6448913
theorem B956971 : Blo 794341 956971 := bstep (se 1 (by rfl) ⟨717728, by rfl⟩ : syracuseStep 956971 = 1435457) B1435457
theorem B1514027 : Blo 794341 1514027 := bstep (se 1 (by rfl) ⟨1135520, by rfl⟩ : syracuseStep 1514027 = 2271041) B2271041
theorem B9706027 : Blo 794341 9706027 := bstep (se 1 (by rfl) ⟨7279520, by rfl⟩ : syracuseStep 9706027 = 14559041) B14559041
theorem B8591939 : Blo 794341 8591939 := bstep (se 1 (by rfl) ⟨6443954, by rfl⟩ : syracuseStep 8591939 = 12887909) B12887909
theorem B2267783 : Blo 794341 2267783 := bstep (se 1 (by rfl) ⟨1700837, by rfl⟩ : syracuseStep 2267783 = 3401675) B3401675
theorem B3021569 : Blo 794341 3021569 := bstep (se 2 (by rfl) ⟨1133088, by rfl⟩ : syracuseStep 3021569 = 2266177) B2266177
theorem B3021583 : Blo 794341 3021583 := bstep (se 1 (by rfl) ⟨2266187, by rfl⟩ : syracuseStep 3021583 = 4532375) B4532375
theorem B1088399 : Blo 794341 1088399 := bstep (se 1 (by rfl) ⟨816299, by rfl⟩ : syracuseStep 1088399 = 1632599) B1632599
theorem B4529459 : Blo 794341 4529459 := bstep (se 1 (by rfl) ⟨3397094, by rfl⟩ : syracuseStep 4529459 = 6794189) B6794189
theorem B4300121 : Blo 794341 4300121 := bstep (se 2 (by rfl) ⟨1612545, by rfl⟩ : syracuseStep 4300121 = 3225091) B3225091
theorem B1514953 : Blo 794341 1514953 := bstep (se 2 (by rfl) ⟨568107, by rfl⟩ : syracuseStep 1514953 = 1136215) B1136215
theorem B4038173 : Blo 794341 4038173 := bstep (se 3 (by rfl) ⟨757157, by rfl⟩ : syracuseStep 4038173 = 1514315) B1514315
theorem B20717207 : Blo 794341 20717207 := bstep (se 1 (by rfl) ⟨15537905, by rfl⟩ : syracuseStep 20717207 = 31075811) B31075811
theorem B794375 : Blo 794341 794375 := bstep (se 1 (by rfl) ⟨595781, by rfl⟩ : syracuseStep 794375 = 1191563) B1191563
theorem B794383 : Blo 794341 794383 := bstep (se 1 (by rfl) ⟨595787, by rfl⟩ : syracuseStep 794383 = 1191575) B1191575
theorem B794427 : Blo 794341 794427 := bstep (se 1 (by rfl) ⟨595820, by rfl⟩ : syracuseStep 794427 = 1191641) B1191641
theorem B794503 : Blo 794341 794503 := bstep (se 1 (by rfl) ⟨595877, by rfl⟩ : syracuseStep 794503 = 1191755) B1191755
theorem B794511 : Blo 794341 794511 := bstep (se 1 (by rfl) ⟨595883, by rfl⟩ : syracuseStep 794511 = 1191767) B1191767
theorem B794555 : Blo 794341 794555 := bstep (se 1 (by rfl) ⟨595916, by rfl⟩ : syracuseStep 794555 = 1191833) B1191833
theorem B4038659 : Blo 794341 4038659 := bstep (se 1 (by rfl) ⟨3028994, by rfl⟩ : syracuseStep 4038659 = 6057989) B6057989
theorem B794631 : Blo 794341 794631 := bstep (se 1 (by rfl) ⟨595973, by rfl⟩ : syracuseStep 794631 = 1191947) B1191947
theorem B3022859 : Blo 794341 3022859 := bstep (se 1 (by rfl) ⟨2267144, by rfl⟩ : syracuseStep 3022859 = 4534289) B4534289
theorem B794639 : Blo 794341 794639 := bstep (se 1 (by rfl) ⟨595979, by rfl⟩ : syracuseStep 794639 = 1191959) B1191959
theorem B794683 : Blo 794341 794683 := bstep (se 1 (by rfl) ⟨596012, by rfl⟩ : syracuseStep 794683 = 1192025) B1192025
theorem B794759 : Blo 794341 794759 := bstep (se 1 (by rfl) ⟨596069, by rfl⟩ : syracuseStep 794759 = 1192139) B1192139
theorem B794767 : Blo 794341 794767 := bstep (se 1 (by rfl) ⟨596075, by rfl⟩ : syracuseStep 794767 = 1192151) B1192151
theorem B794811 : Blo 794341 794811 := bstep (se 1 (by rfl) ⟨596108, by rfl⟩ : syracuseStep 794811 = 1192217) B1192217
theorem B958711 : Blo 794341 958711 := bstep (se 1 (by rfl) ⟨719033, by rfl⟩ : syracuseStep 958711 = 1438067) B1438067
theorem B794887 : Blo 794341 794887 := bstep (se 1 (by rfl) ⟨596165, by rfl⟩ : syracuseStep 794887 = 1192331) B1192331
theorem B794895 : Blo 794341 794895 := bstep (se 1 (by rfl) ⟨596171, by rfl⟩ : syracuseStep 794895 = 1192343) B1192343
theorem B794939 : Blo 794341 794939 := bstep (se 1 (by rfl) ⟨596204, by rfl⟩ : syracuseStep 794939 = 1192409) B1192409
theorem B2269559 : Blo 794341 2269559 := bstep (se 1 (by rfl) ⟨1702169, by rfl⟩ : syracuseStep 2269559 = 3404339) B3404339
theorem B795015 : Blo 794341 795015 := bstep (se 1 (by rfl) ⟨596261, by rfl⟩ : syracuseStep 795015 = 1192523) B1192523
theorem B9183623 : Blo 794341 9183623 := bstep (se 1 (by rfl) ⟨6887717, by rfl⟩ : syracuseStep 9183623 = 13775435) B13775435
theorem B795023 : Blo 794341 795023 := bstep (se 1 (by rfl) ⟨596267, by rfl⟩ : syracuseStep 795023 = 1192535) B1192535
theorem B795067 : Blo 794341 795067 := bstep (se 1 (by rfl) ⟨596300, by rfl⟩ : syracuseStep 795067 = 1192601) B1192601
theorem B795143 : Blo 794341 795143 := bstep (se 1 (by rfl) ⟨596357, by rfl⟩ : syracuseStep 795143 = 1192715) B1192715
theorem B795151 : Blo 794341 795151 := bstep (se 1 (by rfl) ⟨596363, by rfl⟩ : syracuseStep 795151 = 1192727) B1192727
theorem B795195 : Blo 794341 795195 := bstep (se 1 (by rfl) ⟨596396, by rfl⟩ : syracuseStep 795195 = 1192793) B1192793
theorem B795271 : Blo 794341 795271 := bstep (se 1 (by rfl) ⟨596453, by rfl⟩ : syracuseStep 795271 = 1192907) B1192907
theorem B795279 : Blo 794341 795279 := bstep (se 1 (by rfl) ⟨596459, by rfl⟩ : syracuseStep 795279 = 1192919) B1192919
theorem B795323 : Blo 794341 795323 := bstep (se 1 (by rfl) ⟨596492, by rfl⟩ : syracuseStep 795323 = 1192985) B1192985
theorem B4530917 : Blo 794341 4530917 := bstep (se 4 (by rfl) ⟨424773, by rfl⟩ : syracuseStep 4530917 = 849547) B849547
theorem B795399 : Blo 794341 795399 := bstep (se 1 (by rfl) ⟨596549, by rfl⟩ : syracuseStep 795399 = 1193099) B1193099
theorem B795407 : Blo 794341 795407 := bstep (se 1 (by rfl) ⟨596555, by rfl⟩ : syracuseStep 795407 = 1193111) B1193111
theorem B7250725 : Blo 794341 7250725 := bstep (se 4 (by rfl) ⟨679755, by rfl⟩ : syracuseStep 7250725 = 1359511) B1359511
theorem B795451 : Blo 794341 795451 := bstep (se 1 (by rfl) ⟨596588, by rfl⟩ : syracuseStep 795451 = 1193177) B1193177
theorem B795527 : Blo 794341 795527 := bstep (se 1 (by rfl) ⟨596645, by rfl⟩ : syracuseStep 795527 = 1193291) B1193291
theorem B893839 : Blo 794341 893839 := bstep (se 1 (by rfl) ⟨670379, by rfl⟩ : syracuseStep 893839 = 1340759) B1340759
theorem B795535 : Blo 794341 795535 := bstep (se 1 (by rfl) ⟨596651, by rfl⟩ : syracuseStep 795535 = 1193303) B1193303
theorem B3023801 : Blo 794341 3023801 := bstep (se 2 (by rfl) ⟨1133925, by rfl⟩ : syracuseStep 3023801 = 2267851) B2267851
theorem B795579 : Blo 794341 795579 := bstep (se 1 (by rfl) ⟨596684, by rfl⟩ : syracuseStep 795579 = 1193369) B1193369
theorem B795655 : Blo 794341 795655 := bstep (se 1 (by rfl) ⟨596741, by rfl⟩ : syracuseStep 795655 = 1193483) B1193483
theorem B795663 : Blo 794341 795663 := bstep (se 1 (by rfl) ⟨596747, by rfl⟩ : syracuseStep 795663 = 1193495) B1193495
theorem B5809175 : Blo 794341 5809175 := bstep (se 1 (by rfl) ⟨4356881, by rfl⟩ : syracuseStep 5809175 = 8713763) B8713763
theorem B795707 : Blo 794341 795707 := bstep (se 1 (by rfl) ⟨596780, by rfl⟩ : syracuseStep 795707 = 1193561) B1193561
theorem B795783 : Blo 794341 795783 := bstep (se 1 (by rfl) ⟨596837, by rfl⟩ : syracuseStep 795783 = 1193675) B1193675
theorem B795791 : Blo 794341 795791 := bstep (se 1 (by rfl) ⟨596843, by rfl⟩ : syracuseStep 795791 = 1193687) B1193687
theorem B4531373 : Blo 794341 4531373 := bstep (se 3 (by rfl) ⟨849632, by rfl⟩ : syracuseStep 4531373 = 1699265) B1699265
theorem B795835 : Blo 794341 795835 := bstep (se 1 (by rfl) ⟨596876, by rfl⟩ : syracuseStep 795835 = 1193753) B1193753
theorem B795911 : Blo 794341 795911 := bstep (se 1 (by rfl) ⟨596933, by rfl⟩ : syracuseStep 795911 = 1193867) B1193867
theorem B795919 : Blo 794341 795919 := bstep (se 1 (by rfl) ⟨596939, by rfl⟩ : syracuseStep 795919 = 1193879) B1193879
theorem B795963 : Blo 794341 795963 := bstep (se 1 (by rfl) ⟨596972, by rfl⟩ : syracuseStep 795963 = 1193945) B1193945
theorem B2270551 : Blo 794341 2270551 := bstep (se 1 (by rfl) ⟨1702913, by rfl⟩ : syracuseStep 2270551 = 3405827) B3405827
theorem B894343 : Blo 794341 894343 := bstep (se 1 (by rfl) ⟨670757, by rfl⟩ : syracuseStep 894343 = 1341515) B1341515
theorem B796039 : Blo 794341 796039 := bstep (se 1 (by rfl) ⟨597029, by rfl⟩ : syracuseStep 796039 = 1194059) B1194059
theorem B796047 : Blo 794341 796047 := bstep (se 1 (by rfl) ⟨597035, by rfl⟩ : syracuseStep 796047 = 1194071) B1194071
theorem B1451449 : Blo 794341 1451449 := bstep (se 2 (by rfl) ⟨544293, by rfl⟩ : syracuseStep 1451449 = 1088587) B1088587
theorem B796091 : Blo 794341 796091 := bstep (se 1 (by rfl) ⟨597068, by rfl⟩ : syracuseStep 796091 = 1194137) B1194137
theorem B796167 : Blo 794341 796167 := bstep (se 1 (by rfl) ⟨597125, by rfl⟩ : syracuseStep 796167 = 1194251) B1194251
theorem B796175 : Blo 794341 796175 := bstep (se 1 (by rfl) ⟨597131, by rfl⟩ : syracuseStep 796175 = 1194263) B1194263
theorem B894523 : Blo 794341 894523 := bstep (se 1 (by rfl) ⟨670892, by rfl⟩ : syracuseStep 894523 = 1341785) B1341785
theorem B796219 : Blo 794341 796219 := bstep (se 1 (by rfl) ⟨597164, by rfl⟩ : syracuseStep 796219 = 1194329) B1194329
theorem B4040279 : Blo 794341 4040279 := bstep (se 1 (by rfl) ⟨3030209, by rfl⟩ : syracuseStep 4040279 = 6060419) B6060419
theorem B796295 : Blo 794341 796295 := bstep (se 1 (by rfl) ⟨597221, by rfl⟩ : syracuseStep 796295 = 1194443) B1194443
theorem B796303 : Blo 794341 796303 := bstep (se 1 (by rfl) ⟨597227, by rfl⟩ : syracuseStep 796303 = 1194455) B1194455
theorem B1910425 : Blo 794341 1910425 := bstep (se 2 (by rfl) ⟨716409, by rfl⟩ : syracuseStep 1910425 = 1432819) B1432819
theorem B796347 : Blo 794341 796347 := bstep (se 1 (by rfl) ⟨597260, by rfl⟩ : syracuseStep 796347 = 1194521) B1194521
theorem B16361189 : Blo 794341 16361189 := bstep (se 4 (by rfl) ⟨1533861, by rfl⟩ : syracuseStep 16361189 = 3067723) B3067723
theorem B796423 : Blo 794341 796423 := bstep (se 1 (by rfl) ⟨597317, by rfl⟩ : syracuseStep 796423 = 1194635) B1194635
theorem B796431 : Blo 794341 796431 := bstep (se 1 (by rfl) ⟨597323, by rfl⟩ : syracuseStep 796431 = 1194647) B1194647
theorem B796475 : Blo 794341 796475 := bstep (se 1 (by rfl) ⟨597356, by rfl⟩ : syracuseStep 796475 = 1194713) B1194713
theorem B4532057 : Blo 794341 4532057 := bstep (se 2 (by rfl) ⟨1699521, by rfl⟩ : syracuseStep 4532057 = 3399043) B3399043
theorem B796551 : Blo 794341 796551 := bstep (se 1 (by rfl) ⟨597413, by rfl⟩ : syracuseStep 796551 = 1194827) B1194827
theorem B796559 : Blo 794341 796559 := bstep (se 1 (by rfl) ⟨597419, by rfl⟩ : syracuseStep 796559 = 1194839) B1194839
theorem B3876761 : Blo 794341 3876761 := bstep (se 2 (by rfl) ⟨1453785, by rfl⟩ : syracuseStep 3876761 = 2907571) B2907571
theorem B1091513 : Blo 794341 1091513 := bstep (se 2 (by rfl) ⟨409317, by rfl⟩ : syracuseStep 1091513 = 818635) B818635
theorem B796603 : Blo 794341 796603 := bstep (se 1 (by rfl) ⟨597452, by rfl⟩ : syracuseStep 796603 = 1194905) B1194905
theorem B796679 : Blo 794341 796679 := bstep (se 1 (by rfl) ⟨597509, by rfl⟩ : syracuseStep 796679 = 1195019) B1195019
theorem B894991 : Blo 794341 894991 := bstep (se 1 (by rfl) ⟨671243, by rfl⟩ : syracuseStep 894991 = 1342487) B1342487
theorem B796687 : Blo 794341 796687 := bstep (se 1 (by rfl) ⟨597515, by rfl⟩ : syracuseStep 796687 = 1195031) B1195031
theorem B796731 : Blo 794341 796731 := bstep (se 1 (by rfl) ⟨597548, by rfl⟩ : syracuseStep 796731 = 1195097) B1195097
theorem B4040765 : Blo 794341 4040765 := bstep (se 3 (by rfl) ⟨757643, by rfl⟩ : syracuseStep 4040765 = 1515287) B1515287
theorem B1615991 : Blo 794341 1615991 := bstep (se 1 (by rfl) ⟨1211993, by rfl⟩ : syracuseStep 1615991 = 2423987) B2423987
theorem B2304119 : Blo 794341 2304119 := bstep (se 1 (by rfl) ⟨1728089, by rfl⟩ : syracuseStep 2304119 = 3456179) B3456179
theorem B796807 : Blo 794341 796807 := bstep (se 1 (by rfl) ⟨597605, by rfl⟩ : syracuseStep 796807 = 1195211) B1195211
theorem B796815 : Blo 794341 796815 := bstep (se 1 (by rfl) ⟨597611, by rfl⟩ : syracuseStep 796815 = 1195223) B1195223
theorem B796859 : Blo 794341 796859 := bstep (se 1 (by rfl) ⟨597644, by rfl⟩ : syracuseStep 796859 = 1195289) B1195289
theorem B796935 : Blo 794341 796935 := bstep (se 1 (by rfl) ⟨597701, by rfl⟩ : syracuseStep 796935 = 1195403) B1195403
theorem B796943 : Blo 794341 796943 := bstep (se 1 (by rfl) ⟨597707, by rfl⟩ : syracuseStep 796943 = 1195415) B1195415
theorem B6465851 : Blo 794341 6465851 := bstep (se 1 (by rfl) ⟨4849388, by rfl⟩ : syracuseStep 6465851 = 9698777) B9698777
theorem B796987 : Blo 794341 796987 := bstep (se 1 (by rfl) ⟨597740, by rfl⟩ : syracuseStep 796987 = 1195481) B1195481
theorem B797063 : Blo 794341 797063 := bstep (se 1 (by rfl) ⟨597797, by rfl⟩ : syracuseStep 797063 = 1195595) B1195595
theorem B797071 : Blo 794341 797071 := bstep (se 1 (by rfl) ⟨597803, by rfl⟩ : syracuseStep 797071 = 1195607) B1195607
theorem B797115 : Blo 794341 797115 := bstep (se 1 (by rfl) ⟨597836, by rfl⟩ : syracuseStep 797115 = 1195673) B1195673
theorem B895495 : Blo 794341 895495 := bstep (se 1 (by rfl) ⟨671621, by rfl⟩ : syracuseStep 895495 = 1343243) B1343243
theorem B797191 : Blo 794341 797191 := bstep (se 1 (by rfl) ⟨597893, by rfl⟩ : syracuseStep 797191 = 1195787) B1195787
theorem B797199 : Blo 794341 797199 := bstep (se 1 (by rfl) ⟨597899, by rfl⟩ : syracuseStep 797199 = 1195799) B1195799
theorem B797243 : Blo 794341 797243 := bstep (se 1 (by rfl) ⟨597932, by rfl⟩ : syracuseStep 797243 = 1195865) B1195865
theorem B797319 : Blo 794341 797319 := bstep (se 1 (by rfl) ⟨597989, by rfl⟩ : syracuseStep 797319 = 1195979) B1195979
theorem B797327 : Blo 794341 797327 := bstep (se 1 (by rfl) ⟨597995, by rfl⟩ : syracuseStep 797327 = 1195991) B1195991
theorem B895675 : Blo 794341 895675 := bstep (se 1 (by rfl) ⟨671756, by rfl⟩ : syracuseStep 895675 = 1343513) B1343513
theorem B797371 : Blo 794341 797371 := bstep (se 1 (by rfl) ⟨598028, by rfl⟩ : syracuseStep 797371 = 1196057) B1196057
theorem B797447 : Blo 794341 797447 := bstep (se 1 (by rfl) ⟨598085, by rfl⟩ : syracuseStep 797447 = 1196171) B1196171
theorem B3222287 : Blo 794341 3222287 := bstep (se 1 (by rfl) ⟨2416715, by rfl⟩ : syracuseStep 3222287 = 4833431) B4833431
theorem B797455 : Blo 794341 797455 := bstep (se 1 (by rfl) ⟨598091, by rfl⟩ : syracuseStep 797455 = 1196183) B1196183
theorem B2272043 : Blo 794341 2272043 := bstep (se 1 (by rfl) ⟨1704032, by rfl⟩ : syracuseStep 2272043 = 3408065) B3408065
theorem B797499 : Blo 794341 797499 := bstep (se 1 (by rfl) ⟨598124, by rfl⟩ : syracuseStep 797499 = 1196249) B1196249
theorem B9677657 : Blo 794341 9677657 := bstep (se 2 (by rfl) ⟨3629121, by rfl⟩ : syracuseStep 9677657 = 7258243) B7258243
theorem B797575 : Blo 794341 797575 := bstep (se 1 (by rfl) ⟨598181, by rfl⟩ : syracuseStep 797575 = 1196363) B1196363
theorem B797583 : Blo 794341 797583 := bstep (se 1 (by rfl) ⟨598187, by rfl⟩ : syracuseStep 797583 = 1196375) B1196375
theorem B797627 : Blo 794341 797627 := bstep (se 1 (by rfl) ⟨598220, by rfl⟩ : syracuseStep 797627 = 1196441) B1196441
theorem B797703 : Blo 794341 797703 := bstep (se 1 (by rfl) ⟨598277, by rfl⟩ : syracuseStep 797703 = 1196555) B1196555
theorem B797711 : Blo 794341 797711 := bstep (se 1 (by rfl) ⟨598283, by rfl⟩ : syracuseStep 797711 = 1196567) B1196567
theorem B7646231 : Blo 794341 7646231 := bstep (se 1 (by rfl) ⟨5734673, by rfl⟩ : syracuseStep 7646231 = 11469347) B11469347
theorem B797755 : Blo 794341 797755 := bstep (se 1 (by rfl) ⟨598316, by rfl⟩ : syracuseStep 797755 = 1196633) B1196633
theorem B797831 : Blo 794341 797831 := bstep (se 1 (by rfl) ⟨598373, by rfl⟩ : syracuseStep 797831 = 1196747) B1196747
theorem B896143 : Blo 794341 896143 := bstep (se 1 (by rfl) ⟨672107, by rfl⟩ : syracuseStep 896143 = 1344215) B1344215
theorem B797839 : Blo 794341 797839 := bstep (se 1 (by rfl) ⟨598379, by rfl⟩ : syracuseStep 797839 = 1196759) B1196759
theorem B797883 : Blo 794341 797883 := bstep (se 1 (by rfl) ⟨598412, by rfl⟩ : syracuseStep 797883 = 1196825) B1196825
theorem B797959 : Blo 794341 797959 := bstep (se 1 (by rfl) ⟨598469, by rfl⟩ : syracuseStep 797959 = 1196939) B1196939
theorem B797967 : Blo 794341 797967 := bstep (se 1 (by rfl) ⟨598475, by rfl⟩ : syracuseStep 797967 = 1196951) B1196951
theorem B798011 : Blo 794341 798011 := bstep (se 1 (by rfl) ⟨598508, by rfl⟩ : syracuseStep 798011 = 1197017) B1197017
theorem B798087 : Blo 794341 798087 := bstep (se 1 (by rfl) ⟨598565, by rfl⟩ : syracuseStep 798087 = 1197131) B1197131
theorem B798095 : Blo 794341 798095 := bstep (se 1 (by rfl) ⟨598571, by rfl⟩ : syracuseStep 798095 = 1197143) B1197143
theorem B6040979 : Blo 794341 6040979 := bstep (se 1 (by rfl) ⟨4530734, by rfl⟩ : syracuseStep 6040979 = 9061469) B9061469
theorem B798139 : Blo 794341 798139 := bstep (se 1 (by rfl) ⟨598604, by rfl⟩ : syracuseStep 798139 = 1197209) B1197209
theorem B14757329 : Blo 794341 14757329 := bstep (se 2 (by rfl) ⟨5533998, by rfl⟩ : syracuseStep 14757329 = 11067997) B11067997
theorem B798215 : Blo 794341 798215 := bstep (se 1 (by rfl) ⟨598661, by rfl⟩ : syracuseStep 798215 = 1197323) B1197323
theorem B3026443 : Blo 794341 3026443 := bstep (se 1 (by rfl) ⟨2269832, by rfl⟩ : syracuseStep 3026443 = 4539665) B4539665
theorem B798223 : Blo 794341 798223 := bstep (se 1 (by rfl) ⟨598667, by rfl⟩ : syracuseStep 798223 = 1197335) B1197335
theorem B2010683 : Blo 794341 2010683 := bstep (se 1 (by rfl) ⟨1508012, by rfl⟩ : syracuseStep 2010683 = 3016025) B3016025
theorem B798267 : Blo 794341 798267 := bstep (se 1 (by rfl) ⟨598700, by rfl⟩ : syracuseStep 798267 = 1197401) B1197401
theorem B896647 : Blo 794341 896647 := bstep (se 1 (by rfl) ⟨672485, by rfl⟩ : syracuseStep 896647 = 1344971) B1344971
theorem B1191611 : Blo 794341 1191611 := bstep (se 1 (by rfl) ⟨893708, by rfl⟩ : syracuseStep 1191611 = 1787417) B1787417
theorem B1191671 : Blo 794341 1191671 := bstep (se 1 (by rfl) ⟨893753, by rfl⟩ : syracuseStep 1191671 = 1787507) B1787507
theorem B1912577 : Blo 794341 1912577 := bstep (se 2 (by rfl) ⟨717216, by rfl⟩ : syracuseStep 1912577 = 1434433) B1434433
theorem B1191695 : Blo 794341 1191695 := bstep (se 1 (by rfl) ⟨893771, by rfl⟩ : syracuseStep 1191695 = 1787543) B1787543
theorem B1814287 : Blo 794341 1814287 := bstep (se 1 (by rfl) ⟨1360715, by rfl⟩ : syracuseStep 1814287 = 2721431) B2721431
theorem B1191737 : Blo 794341 1191737 := bstep (se 2 (by rfl) ⟨446901, by rfl⟩ : syracuseStep 1191737 = 893803) B893803
theorem B3026747 : Blo 794341 3026747 := bstep (se 1 (by rfl) ⟨2270060, by rfl⟩ : syracuseStep 3026747 = 4540121) B4540121
theorem B896827 : Blo 794341 896827 := bstep (se 1 (by rfl) ⟨672620, by rfl⟩ : syracuseStep 896827 = 1345241) B1345241
theorem B1191815 : Blo 794341 1191815 := bstep (se 1 (by rfl) ⟨893861, by rfl⟩ : syracuseStep 1191815 = 1787723) B1787723
theorem B2273159 : Blo 794341 2273159 := bstep (se 1 (by rfl) ⟨1704869, by rfl⟩ : syracuseStep 2273159 = 3409739) B3409739
theorem B2011027 : Blo 794341 2011027 := bstep (se 1 (by rfl) ⟨1508270, by rfl⟩ : syracuseStep 2011027 = 3016541) B3016541
theorem B1191851 : Blo 794341 1191851 := bstep (se 1 (by rfl) ⟨893888, by rfl⟩ : syracuseStep 1191851 = 1787777) B1787777
theorem B4599737 : Blo 794341 4599737 := bstep (se 2 (by rfl) ⟨1724901, by rfl⟩ : syracuseStep 4599737 = 3449803) B3449803
theorem B1191881 : Blo 794341 1191881 := bstep (se 2 (by rfl) ⟨446955, by rfl⟩ : syracuseStep 1191881 = 893911) B893911
theorem B2011169 : Blo 794341 2011169 := bstep (se 2 (by rfl) ⟨754188, by rfl⟩ : syracuseStep 2011169 = 1508377) B1508377
theorem B1191995 : Blo 794341 1191995 := bstep (se 1 (by rfl) ⟨893996, by rfl⟩ : syracuseStep 1191995 = 1787993) B1787993
theorem B2273341 : Blo 794341 2273341 := bstep (se 3 (by rfl) ⟨426251, by rfl⟩ : syracuseStep 2273341 = 852503) B852503
theorem B2240627 : Blo 794341 2240627 := bstep (se 1 (by rfl) ⟨1680470, by rfl⟩ : syracuseStep 2240627 = 3360941) B3360941
theorem B1192055 : Blo 794341 1192055 := bstep (se 1 (by rfl) ⟨894041, by rfl⟩ : syracuseStep 1192055 = 1788083) B1788083
theorem B1192079 : Blo 794341 1192079 := bstep (se 1 (by rfl) ⟨894059, by rfl⟩ : syracuseStep 1192079 = 1788119) B1788119
theorem B1618067 : Blo 794341 1618067 := bstep (se 1 (by rfl) ⟨1213550, by rfl⟩ : syracuseStep 1618067 = 2427101) B2427101
theorem B1192121 : Blo 794341 1192121 := bstep (se 2 (by rfl) ⟨447045, by rfl⟩ : syracuseStep 1192121 = 894091) B894091
theorem B1192199 : Blo 794341 1192199 := bstep (se 1 (by rfl) ⟨894149, by rfl⟩ : syracuseStep 1192199 = 1788299) B1788299
theorem B897295 : Blo 794341 897295 := bstep (se 1 (by rfl) ⟨672971, by rfl⟩ : syracuseStep 897295 = 1345943) B1345943
theorem B3027233 : Blo 794341 3027233 := bstep (se 2 (by rfl) ⟨1135212, by rfl⟩ : syracuseStep 3027233 = 2270425) B2270425
theorem B1192235 : Blo 794341 1192235 := bstep (se 1 (by rfl) ⟨894176, by rfl⟩ : syracuseStep 1192235 = 1788353) B1788353
theorem B1192265 : Blo 794341 1192265 := bstep (se 2 (by rfl) ⟨447099, by rfl⟩ : syracuseStep 1192265 = 894199) B894199
theorem B5747129 : Blo 794341 5747129 := bstep (se 2 (by rfl) ⟨2155173, by rfl⟩ : syracuseStep 5747129 = 4310347) B4310347
theorem B1192379 : Blo 794341 1192379 := bstep (se 1 (by rfl) ⟨894284, by rfl⟩ : syracuseStep 1192379 = 1788569) B1788569
theorem B1192439 : Blo 794341 1192439 := bstep (se 1 (by rfl) ⟨894329, by rfl⟩ : syracuseStep 1192439 = 1788659) B1788659
theorem B4305419 : Blo 794341 4305419 := bstep (se 1 (by rfl) ⟨3229064, by rfl⟩ : syracuseStep 4305419 = 6458129) B6458129
theorem B1192463 : Blo 794341 1192463 := bstep (se 1 (by rfl) ⟨894347, by rfl⟩ : syracuseStep 1192463 = 1788695) B1788695
theorem B23245355 : Blo 794341 23245355 := bstep (se 1 (by rfl) ⟨17434016, by rfl⟩ : syracuseStep 23245355 = 34868033) B34868033
theorem B1192505 : Blo 794341 1192505 := bstep (se 2 (by rfl) ⟨447189, by rfl⟩ : syracuseStep 1192505 = 894379) B894379
theorem B1192583 : Blo 794341 1192583 := bstep (se 1 (by rfl) ⟨894437, by rfl⟩ : syracuseStep 1192583 = 1788875) B1788875
theorem B1192619 : Blo 794341 1192619 := bstep (se 1 (by rfl) ⟨894464, by rfl⟩ : syracuseStep 1192619 = 1788929) B1788929
theorem B1192649 : Blo 794341 1192649 := bstep (se 2 (by rfl) ⟨447243, by rfl⟩ : syracuseStep 1192649 = 894487) B894487
theorem B897799 : Blo 794341 897799 := bstep (se 1 (by rfl) ⟨673349, by rfl⟩ : syracuseStep 897799 = 1346699) B1346699
theorem B92943125 : Blo 794341 92943125 := bstep (se 6 (by rfl) ⟨2178354, by rfl⟩ : syracuseStep 92943125 = 4356709) B4356709
theorem B1192763 : Blo 794341 1192763 := bstep (se 1 (by rfl) ⟨894572, by rfl⟩ : syracuseStep 1192763 = 1789145) B1789145
theorem B1192823 : Blo 794341 1192823 := bstep (se 1 (by rfl) ⟨894617, by rfl⟩ : syracuseStep 1192823 = 1789235) B1789235
theorem B1192847 : Blo 794341 1192847 := bstep (se 1 (by rfl) ⟨894635, by rfl⟩ : syracuseStep 1192847 = 1789271) B1789271
theorem B1192889 : Blo 794341 1192889 := bstep (se 2 (by rfl) ⟨447333, by rfl⟩ : syracuseStep 1192889 = 894667) B894667
theorem B897979 : Blo 794341 897979 := bstep (se 1 (by rfl) ⟨673484, by rfl⟩ : syracuseStep 897979 = 1346969) B1346969
theorem B4371421 : Blo 794341 4371421 := bstep (se 3 (by rfl) ⟨819641, by rfl⟩ : syracuseStep 4371421 = 1639283) B1639283
theorem B2012161 : Blo 794341 2012161 := bstep (se 2 (by rfl) ⟨754560, by rfl⟩ : syracuseStep 2012161 = 1509121) B1509121
theorem B1192967 : Blo 794341 1192967 := bstep (se 1 (by rfl) ⟨894725, by rfl⟩ : syracuseStep 1192967 = 1789451) B1789451
theorem B1193003 : Blo 794341 1193003 := bstep (se 1 (by rfl) ⟨894752, by rfl⟩ : syracuseStep 1193003 = 1789505) B1789505
theorem B1193033 : Blo 794341 1193033 := bstep (se 2 (by rfl) ⟨447387, by rfl⟩ : syracuseStep 1193033 = 894775) B894775
theorem B1193147 : Blo 794341 1193147 := bstep (se 1 (by rfl) ⟨894860, by rfl⟩ : syracuseStep 1193147 = 1789721) B1789721
theorem B3028205 : Blo 794341 3028205 := bstep (se 3 (by rfl) ⟨567788, by rfl⟩ : syracuseStep 3028205 = 1135577) B1135577
theorem B1193207 : Blo 794341 1193207 := bstep (se 1 (by rfl) ⟨894905, by rfl⟩ : syracuseStep 1193207 = 1789811) B1789811
theorem B1193231 : Blo 794341 1193231 := bstep (se 1 (by rfl) ⟨894923, by rfl⟩ : syracuseStep 1193231 = 1789847) B1789847
theorem B1193273 : Blo 794341 1193273 := bstep (se 2 (by rfl) ⟨447477, by rfl⟩ : syracuseStep 1193273 = 894955) B894955
theorem B1193351 : Blo 794341 1193351 := bstep (se 1 (by rfl) ⟨895013, by rfl⟩ : syracuseStep 1193351 = 1790027) B1790027
theorem B1193387 : Blo 794341 1193387 := bstep (se 1 (by rfl) ⟨895040, by rfl⟩ : syracuseStep 1193387 = 1790081) B1790081
theorem B1193417 : Blo 794341 1193417 := bstep (se 2 (by rfl) ⟨447531, by rfl⟩ : syracuseStep 1193417 = 895063) B895063
theorem B1193531 : Blo 794341 1193531 := bstep (se 1 (by rfl) ⟨895148, by rfl⟩ : syracuseStep 1193531 = 1790297) B1790297
theorem B2012759 : Blo 794341 2012759 := bstep (se 1 (by rfl) ⟨1509569, by rfl⟩ : syracuseStep 2012759 = 3019139) B3019139
theorem B1193591 : Blo 794341 1193591 := bstep (se 1 (by rfl) ⟨895193, by rfl⟩ : syracuseStep 1193591 = 1790387) B1790387
theorem B1193615 : Blo 794341 1193615 := bstep (se 1 (by rfl) ⟨895211, by rfl⟩ : syracuseStep 1193615 = 1790423) B1790423
theorem B1193657 : Blo 794341 1193657 := bstep (se 2 (by rfl) ⟨447621, by rfl⟩ : syracuseStep 1193657 = 895243) B895243
theorem B1193735 : Blo 794341 1193735 := bstep (se 1 (by rfl) ⟨895301, by rfl⟩ : syracuseStep 1193735 = 1790603) B1790603
theorem B2012971 : Blo 794341 2012971 := bstep (se 1 (by rfl) ⟨1509728, by rfl⟩ : syracuseStep 2012971 = 3019457) B3019457
theorem B1193771 : Blo 794341 1193771 := bstep (se 1 (by rfl) ⟨895328, by rfl⟩ : syracuseStep 1193771 = 1790657) B1790657
theorem B1193801 : Blo 794341 1193801 := bstep (se 2 (by rfl) ⟨447675, by rfl⟩ : syracuseStep 1193801 = 895351) B895351
theorem B2013113 : Blo 794341 2013113 := bstep (se 2 (by rfl) ⟨754917, by rfl⟩ : syracuseStep 2013113 = 1509835) B1509835
theorem B1193915 : Blo 794341 1193915 := bstep (se 1 (by rfl) ⟨895436, by rfl⟩ : syracuseStep 1193915 = 1790873) B1790873
theorem B2045897 : Blo 794341 2045897 := bstep (se 2 (by rfl) ⟨767211, by rfl⟩ : syracuseStep 2045897 = 1534423) B1534423
theorem B1193975 : Blo 794341 1193975 := bstep (se 1 (by rfl) ⟨895481, by rfl⟩ : syracuseStep 1193975 = 1790963) B1790963
theorem B5093387 : Blo 794341 5093387 := bstep (se 1 (by rfl) ⟨3820040, by rfl⟩ : syracuseStep 5093387 = 7640081) B7640081
theorem B1193999 : Blo 794341 1193999 := bstep (se 1 (by rfl) ⟨895499, by rfl⟩ : syracuseStep 1193999 = 1790999) B1790999
theorem B12400663 : Blo 794341 12400663 := bstep (se 1 (by rfl) ⟨9300497, by rfl⟩ : syracuseStep 12400663 = 18600995) B18600995
theorem B1194041 : Blo 794341 1194041 := bstep (se 2 (by rfl) ⟨447765, by rfl⟩ : syracuseStep 1194041 = 895531) B895531
theorem B1194119 : Blo 794341 1194119 := bstep (se 1 (by rfl) ⟨895589, by rfl⟩ : syracuseStep 1194119 = 1791179) B1791179
theorem B1194155 : Blo 794341 1194155 := bstep (se 1 (by rfl) ⟨895616, by rfl⟩ : syracuseStep 1194155 = 1791233) B1791233
theorem B1194185 : Blo 794341 1194185 := bstep (se 2 (by rfl) ⟨447819, by rfl⟩ : syracuseStep 1194185 = 895639) B895639
theorem B1194299 : Blo 794341 1194299 := bstep (se 1 (by rfl) ⟨895724, by rfl⟩ : syracuseStep 1194299 = 1791449) B1791449
theorem B1194359 : Blo 794341 1194359 := bstep (se 1 (by rfl) ⟨895769, by rfl⟩ : syracuseStep 1194359 = 1791539) B1791539
theorem B1194383 : Blo 794341 1194383 := bstep (se 1 (by rfl) ⟨895787, by rfl⟩ : syracuseStep 1194383 = 1791575) B1791575
theorem B1915289 : Blo 794341 1915289 := bstep (se 2 (by rfl) ⟨718233, by rfl⟩ : syracuseStep 1915289 = 1436467) B1436467
theorem B1194425 : Blo 794341 1194425 := bstep (se 2 (by rfl) ⟨447909, by rfl⟩ : syracuseStep 1194425 = 895819) B895819
theorem B1194503 : Blo 794341 1194503 := bstep (se 1 (by rfl) ⟨895877, by rfl⟩ : syracuseStep 1194503 = 1791755) B1791755
theorem B1194539 : Blo 794341 1194539 := bstep (se 1 (by rfl) ⟨895904, by rfl⟩ : syracuseStep 1194539 = 1791809) B1791809
theorem B4078147 : Blo 794341 4078147 := bstep (se 1 (by rfl) ⟨3058610, by rfl⟩ : syracuseStep 4078147 = 6117221) B6117221
theorem B1194569 : Blo 794341 1194569 := bstep (se 2 (by rfl) ⟨447963, by rfl⟩ : syracuseStep 1194569 = 895927) B895927
theorem B1194683 : Blo 794341 1194683 := bstep (se 1 (by rfl) ⟨896012, by rfl⟩ : syracuseStep 1194683 = 1792025) B1792025
theorem B1194743 : Blo 794341 1194743 := bstep (se 1 (by rfl) ⟨896057, by rfl⟩ : syracuseStep 1194743 = 1792115) B1792115
theorem B1194767 : Blo 794341 1194767 := bstep (se 1 (by rfl) ⟨896075, by rfl⟩ : syracuseStep 1194767 = 1792151) B1792151
theorem B1194809 : Blo 794341 1194809 := bstep (se 2 (by rfl) ⟨448053, by rfl⟩ : syracuseStep 1194809 = 896107) B896107
theorem B1194887 : Blo 794341 1194887 := bstep (se 1 (by rfl) ⟨896165, by rfl⟩ : syracuseStep 1194887 = 1792331) B1792331
theorem B2014105 : Blo 794341 2014105 := bstep (se 2 (by rfl) ⟨755289, by rfl⟩ : syracuseStep 2014105 = 1510579) B1510579
theorem B1194923 : Blo 794341 1194923 := bstep (se 1 (by rfl) ⟨896192, by rfl⟩ : syracuseStep 1194923 = 1792385) B1792385
theorem B1194953 : Blo 794341 1194953 := bstep (se 2 (by rfl) ⟨448107, by rfl⟩ : syracuseStep 1194953 = 896215) B896215
theorem B2014267 : Blo 794341 2014267 := bstep (se 1 (by rfl) ⟨1510700, by rfl⟩ : syracuseStep 2014267 = 3021401) B3021401
theorem B1195067 : Blo 794341 1195067 := bstep (se 1 (by rfl) ⟨896300, by rfl⟩ : syracuseStep 1195067 = 1792601) B1792601
theorem B1195127 : Blo 794341 1195127 := bstep (se 1 (by rfl) ⟨896345, by rfl⟩ : syracuseStep 1195127 = 1792691) B1792691
theorem B1195151 : Blo 794341 1195151 := bstep (se 1 (by rfl) ⟨896363, by rfl⟩ : syracuseStep 1195151 = 1792727) B1792727
theorem B1195193 : Blo 794341 1195193 := bstep (se 2 (by rfl) ⟨448197, by rfl⟩ : syracuseStep 1195193 = 896395) B896395
theorem B2014409 : Blo 794341 2014409 := bstep (se 2 (by rfl) ⟨755403, by rfl⟩ : syracuseStep 2014409 = 1510807) B1510807
theorem B1195271 : Blo 794341 1195271 := bstep (se 1 (by rfl) ⟨896453, by rfl⟩ : syracuseStep 1195271 = 1792907) B1792907
theorem B1195307 : Blo 794341 1195307 := bstep (se 1 (by rfl) ⟨896480, by rfl⟩ : syracuseStep 1195307 = 1792961) B1792961
theorem B3030331 : Blo 794341 3030331 := bstep (se 1 (by rfl) ⟨2272748, by rfl⟩ : syracuseStep 3030331 = 4545497) B4545497
theorem B1195337 : Blo 794341 1195337 := bstep (se 2 (by rfl) ⟨448251, by rfl⟩ : syracuseStep 1195337 = 896503) B896503
theorem B1195451 : Blo 794341 1195451 := bstep (se 1 (by rfl) ⟨896588, by rfl⟩ : syracuseStep 1195451 = 1793177) B1793177
theorem B1195511 : Blo 794341 1195511 := bstep (se 1 (by rfl) ⟨896633, by rfl⟩ : syracuseStep 1195511 = 1793267) B1793267
theorem B1195535 : Blo 794341 1195535 := bstep (se 1 (by rfl) ⟨896651, by rfl⟩ : syracuseStep 1195535 = 1793303) B1793303
theorem B7650845 : Blo 794341 7650845 := bstep (se 3 (by rfl) ⟨1434533, by rfl⟩ : syracuseStep 7650845 = 2869067) B2869067
theorem B2014753 : Blo 794341 2014753 := bstep (se 2 (by rfl) ⟨755532, by rfl⟩ : syracuseStep 2014753 = 1511065) B1511065
theorem B1195577 : Blo 794341 1195577 := bstep (se 2 (by rfl) ⟨448341, by rfl⟩ : syracuseStep 1195577 = 896683) B896683
theorem B1195655 : Blo 794341 1195655 := bstep (se 1 (by rfl) ⟨896741, by rfl⟩ : syracuseStep 1195655 = 1793483) B1793483
theorem B1195691 : Blo 794341 1195691 := bstep (se 1 (by rfl) ⟨896768, by rfl⟩ : syracuseStep 1195691 = 1793537) B1793537
theorem B1195721 : Blo 794341 1195721 := bstep (se 2 (by rfl) ⟨448395, by rfl⟩ : syracuseStep 1195721 = 896791) B896791
theorem B3030817 : Blo 794341 3030817 := bstep (se 2 (by rfl) ⟨1136556, by rfl⟩ : syracuseStep 3030817 = 2273113) B2273113
theorem B1195835 : Blo 794341 1195835 := bstep (se 1 (by rfl) ⟨896876, by rfl⟩ : syracuseStep 1195835 = 1793753) B1793753
theorem B1195895 : Blo 794341 1195895 := bstep (se 1 (by rfl) ⟨896921, by rfl⟩ : syracuseStep 1195895 = 1793843) B1793843
theorem B1818503 : Blo 794341 1818503 := bstep (se 1 (by rfl) ⟨1363877, by rfl⟩ : syracuseStep 1818503 = 2727755) B2727755
theorem B1195919 : Blo 794341 1195919 := bstep (se 1 (by rfl) ⟨896939, by rfl⟩ : syracuseStep 1195919 = 1793879) B1793879
theorem B1195961 : Blo 794341 1195961 := bstep (se 2 (by rfl) ⟨448485, by rfl⟩ : syracuseStep 1195961 = 896971) B896971
theorem B1196039 : Blo 794341 1196039 := bstep (se 1 (by rfl) ⟨897029, by rfl⟩ : syracuseStep 1196039 = 1794059) B1794059
theorem B1196075 : Blo 794341 1196075 := bstep (se 1 (by rfl) ⟨897056, by rfl⟩ : syracuseStep 1196075 = 1794113) B1794113
theorem B1196105 : Blo 794341 1196105 := bstep (se 2 (by rfl) ⟨448539, by rfl⟩ : syracuseStep 1196105 = 897079) B897079
theorem B2015351 : Blo 794341 2015351 := bstep (se 1 (by rfl) ⟨1511513, by rfl⟩ : syracuseStep 2015351 = 3023027) B3023027
theorem B1196219 : Blo 794341 1196219 := bstep (se 1 (by rfl) ⟨897164, by rfl⟩ : syracuseStep 1196219 = 1794329) B1794329
theorem B1360073 : Blo 794341 1360073 := bstep (se 2 (by rfl) ⟨510027, by rfl⟩ : syracuseStep 1360073 = 1020055) B1020055
theorem B1196279 : Blo 794341 1196279 := bstep (se 1 (by rfl) ⟨897209, by rfl⟩ : syracuseStep 1196279 = 1794419) B1794419
theorem B1196303 : Blo 794341 1196303 := bstep (se 1 (by rfl) ⟨897227, by rfl⟩ : syracuseStep 1196303 = 1794455) B1794455
theorem B1196345 : Blo 794341 1196345 := bstep (se 2 (by rfl) ⟨448629, by rfl⟩ : syracuseStep 1196345 = 897259) B897259
theorem B1196423 : Blo 794341 1196423 := bstep (se 1 (by rfl) ⟨897317, by rfl⟩ : syracuseStep 1196423 = 1794635) B1794635
theorem B1196459 : Blo 794341 1196459 := bstep (se 1 (by rfl) ⟨897344, by rfl⟩ : syracuseStep 1196459 = 1794689) B1794689
theorem B1196489 : Blo 794341 1196489 := bstep (se 2 (by rfl) ⟨448683, by rfl⟩ : syracuseStep 1196489 = 897367) B897367
theorem B1196603 : Blo 794341 1196603 := bstep (se 1 (by rfl) ⟨897452, by rfl⟩ : syracuseStep 1196603 = 1794905) B1794905
theorem B2867831 : Blo 794341 2867831 := bstep (se 1 (by rfl) ⟨2150873, by rfl⟩ : syracuseStep 2867831 = 4301747) B4301747
theorem B1196663 : Blo 794341 1196663 := bstep (se 1 (by rfl) ⟨897497, by rfl⟩ : syracuseStep 1196663 = 1794995) B1794995
theorem B1196687 : Blo 794341 1196687 := bstep (se 1 (by rfl) ⟨897515, by rfl⟩ : syracuseStep 1196687 = 1795031) B1795031
theorem B967339 : Blo 794341 967339 := bstep (se 1 (by rfl) ⟨725504, by rfl⟩ : syracuseStep 967339 = 1451009) B1451009
theorem B1196729 : Blo 794341 1196729 := bstep (se 2 (by rfl) ⟨448773, by rfl⟩ : syracuseStep 1196729 = 897547) B897547
theorem B1196807 : Blo 794341 1196807 := bstep (se 1 (by rfl) ⟨897605, by rfl⟩ : syracuseStep 1196807 = 1795211) B1795211
theorem B1196843 : Blo 794341 1196843 := bstep (se 1 (by rfl) ⟨897632, by rfl⟩ : syracuseStep 1196843 = 1795265) B1795265
theorem B1196873 : Blo 794341 1196873 := bstep (se 2 (by rfl) ⟨448827, by rfl⟩ : syracuseStep 1196873 = 897655) B897655
theorem B1196987 : Blo 794341 1196987 := bstep (se 1 (by rfl) ⟨897740, by rfl⟩ : syracuseStep 1196987 = 1795481) B1795481
theorem B1131511 : Blo 794341 1131511 := bstep (se 1 (by rfl) ⟨848633, by rfl⟩ : syracuseStep 1131511 = 1697267) B1697267
theorem B1197047 : Blo 794341 1197047 := bstep (se 1 (by rfl) ⟨897785, by rfl⟩ : syracuseStep 1197047 = 1795571) B1795571
theorem B1197071 : Blo 794341 1197071 := bstep (se 1 (by rfl) ⟨897803, by rfl⟩ : syracuseStep 1197071 = 1795607) B1795607
theorem B1197113 : Blo 794341 1197113 := bstep (se 2 (by rfl) ⟨448917, by rfl⟩ : syracuseStep 1197113 = 897835) B897835
theorem B13616261 : Blo 794341 13616261 := bstep (se 4 (by rfl) ⟨1276524, by rfl⟩ : syracuseStep 13616261 = 2553049) B2553049
theorem B1197191 : Blo 794341 1197191 := bstep (se 1 (by rfl) ⟨897893, by rfl⟩ : syracuseStep 1197191 = 1795787) B1795787
theorem B1197227 : Blo 794341 1197227 := bstep (se 1 (by rfl) ⟨897920, by rfl⟩ : syracuseStep 1197227 = 1795841) B1795841
theorem B1197257 : Blo 794341 1197257 := bstep (se 2 (by rfl) ⟨448971, by rfl⟩ : syracuseStep 1197257 = 897943) B897943
theorem B1361195 : Blo 794341 1361195 := bstep (se 1 (by rfl) ⟨1020896, by rfl⟩ : syracuseStep 1361195 = 2041793) B2041793
theorem B1197371 : Blo 794341 1197371 := bstep (se 1 (by rfl) ⟨898028, by rfl⟩ : syracuseStep 1197371 = 1796057) B1796057
theorem B1197431 : Blo 794341 1197431 := bstep (se 1 (by rfl) ⟨898073, by rfl⟩ : syracuseStep 1197431 = 1796147) B1796147
theorem B2016647 : Blo 794341 2016647 := bstep (se 1 (by rfl) ⟨1512485, by rfl⟩ : syracuseStep 2016647 = 3024971) B3024971
theorem B1197455 : Blo 794341 1197455 := bstep (se 1 (by rfl) ⟨898091, by rfl⟩ : syracuseStep 1197455 = 1796183) B1796183
theorem B2016697 : Blo 794341 2016697 := bstep (se 2 (by rfl) ⟨756261, by rfl⟩ : syracuseStep 2016697 = 1512523) B1512523
theorem B1197497 : Blo 794341 1197497 := bstep (se 2 (by rfl) ⟨449061, by rfl⟩ : syracuseStep 1197497 = 898123) B898123
theorem B1787435 : Blo 794341 1787435 := bstep (se 1 (by rfl) ⟨1340576, by rfl⟩ : syracuseStep 1787435 = 2681153) B2681153
theorem B19384109 : Blo 794341 19384109 := bstep (se 3 (by rfl) ⟨3634520, by rfl⟩ : syracuseStep 19384109 = 7269041) B7269041
theorem B2148211 : Blo 794341 2148211 := bstep (se 1 (by rfl) ⟨1611158, by rfl⟩ : syracuseStep 2148211 = 3222317) B3222317
theorem B1787795 : Blo 794341 1787795 := bstep (se 1 (by rfl) ⟨1340846, by rfl⟩ : syracuseStep 1787795 = 2681693) B2681693
theorem B1787849 : Blo 794341 1787849 := bstep (se 2 (by rfl) ⟨670443, by rfl⟩ : syracuseStep 1787849 = 1340887) B1340887
theorem B2017295 : Blo 794341 2017295 := bstep (se 1 (by rfl) ⟨1512971, by rfl⟩ : syracuseStep 2017295 = 3025943) B3025943
theorem B3819581 : Blo 794341 3819581 := bstep (se 3 (by rfl) ⟨716171, by rfl⟩ : syracuseStep 3819581 = 1432343) B1432343
theorem B2869789 : Blo 794341 2869789 := bstep (se 3 (by rfl) ⟨538085, by rfl⟩ : syracuseStep 2869789 = 1076171) B1076171
theorem B5098103 : Blo 794341 5098103 := bstep (se 1 (by rfl) ⟨3823577, by rfl⟩ : syracuseStep 5098103 = 7647155) B7647155
theorem B1788551 : Blo 794341 1788551 := bstep (se 1 (by rfl) ⟨1341413, by rfl⟩ : syracuseStep 1788551 = 2682827) B2682827
theorem B3066569 : Blo 794341 3066569 := bstep (se 2 (by rfl) ⟨1149963, by rfl⟩ : syracuseStep 3066569 = 2299927) B2299927
theorem B2017993 : Blo 794341 2017993 := bstep (se 2 (by rfl) ⟨756747, by rfl⟩ : syracuseStep 2017993 = 1513495) B1513495
theorem B4606757 : Blo 794341 4606757 := bstep (se 4 (by rfl) ⟨431883, by rfl⟩ : syracuseStep 4606757 = 863767) B863767
theorem B1788731 : Blo 794341 1788731 := bstep (se 1 (by rfl) ⟨1341548, by rfl⟩ : syracuseStep 1788731 = 2683097) B2683097
theorem B2018135 : Blo 794341 2018135 := bstep (se 1 (by rfl) ⟨1513601, by rfl⟩ : syracuseStep 2018135 = 3027203) B3027203
theorem B4311953 : Blo 794341 4311953 := bstep (se 2 (by rfl) ⟨1616982, by rfl⟩ : syracuseStep 4311953 = 3233965) B3233965
theorem B1788857 : Blo 794341 1788857 := bstep (se 2 (by rfl) ⟨670821, by rfl⟩ : syracuseStep 1788857 = 1341643) B1341643
theorem B11488493 : Blo 794341 11488493 := bstep (se 3 (by rfl) ⟨2154092, by rfl⟩ : syracuseStep 11488493 = 4308185) B4308185
theorem B1789199 : Blo 794341 1789199 := bstep (se 1 (by rfl) ⟨1341899, by rfl⟩ : syracuseStep 1789199 = 2683799) B2683799
theorem B1789217 : Blo 794341 1789217 := bstep (se 2 (by rfl) ⟨670956, by rfl⟩ : syracuseStep 1789217 = 1341913) B1341913
theorem B4541831 : Blo 794341 4541831 := bstep (se 1 (by rfl) ⟨3406373, by rfl⟩ : syracuseStep 4541831 = 6812747) B6812747
theorem B5459345 : Blo 794341 5459345 := bstep (se 2 (by rfl) ⟨2047254, by rfl⟩ : syracuseStep 5459345 = 4094509) B4094509
theorem B1789559 : Blo 794341 1789559 := bstep (se 1 (by rfl) ⟨1342169, by rfl⟩ : syracuseStep 1789559 = 2684339) B2684339
theorem B1134199 : Blo 794341 1134199 := bstep (se 1 (by rfl) ⟨850649, by rfl⟩ : syracuseStep 1134199 = 1701299) B1701299
theorem B1789739 : Blo 794341 1789739 := bstep (se 1 (by rfl) ⟨1342304, by rfl⟩ : syracuseStep 1789739 = 2684609) B2684609
theorem B3395627 : Blo 794341 3395627 := bstep (se 1 (by rfl) ⟨2546720, by rfl⟩ : syracuseStep 3395627 = 5093441) B5093441
theorem B1790099 : Blo 794341 1790099 := bstep (se 1 (by rfl) ⟨1342574, by rfl⟩ : syracuseStep 1790099 = 2685149) B2685149
theorem B1790153 : Blo 794341 1790153 := bstep (se 2 (by rfl) ⟨671307, by rfl⟩ : syracuseStep 1790153 = 1342615) B1342615
theorem B4084121 : Blo 794341 4084121 := bstep (se 2 (by rfl) ⟨1531545, by rfl⟩ : syracuseStep 4084121 = 3063091) B3063091
theorem B1135019 : Blo 794341 1135019 := bstep (se 1 (by rfl) ⟨851264, by rfl⟩ : syracuseStep 1135019 = 1702529) B1702529
theorem B2150927 : Blo 794341 2150927 := bstep (se 1 (by rfl) ⟨1613195, by rfl⟩ : syracuseStep 2150927 = 3226391) B3226391
theorem B4543037 : Blo 794341 4543037 := bstep (se 3 (by rfl) ⟨851819, by rfl⟩ : syracuseStep 4543037 = 1703639) B1703639
theorem B5165687 : Blo 794341 5165687 := bstep (se 1 (by rfl) ⟨3874265, by rfl⟩ : syracuseStep 5165687 = 7748531) B7748531
theorem B2872097 : Blo 794341 2872097 := bstep (se 2 (by rfl) ⟨1077036, by rfl⟩ : syracuseStep 2872097 = 2154073) B2154073
theorem B2020211 : Blo 794341 2020211 := bstep (se 1 (by rfl) ⟨1515158, by rfl⟩ : syracuseStep 2020211 = 3030317) B3030317
theorem B1790855 : Blo 794341 1790855 := bstep (se 1 (by rfl) ⟨1343141, by rfl⟩ : syracuseStep 1790855 = 2686283) B2686283
theorem B1791035 : Blo 794341 1791035 := bstep (se 1 (by rfl) ⟨1343276, by rfl⟩ : syracuseStep 1791035 = 2686553) B2686553
theorem B1791161 : Blo 794341 1791161 := bstep (se 2 (by rfl) ⟨671685, by rfl⟩ : syracuseStep 1791161 = 1343371) B1343371
theorem B2020727 : Blo 794341 2020727 := bstep (se 1 (by rfl) ⟨1515545, by rfl⟩ : syracuseStep 2020727 = 3031091) B3031091
theorem B6116755 : Blo 794341 6116755 := bstep (se 1 (by rfl) ⟨4587566, by rfl⟩ : syracuseStep 6116755 = 9175133) B9175133
theorem B11064761 : Blo 794341 11064761 := bstep (se 2 (by rfl) ⟨4149285, by rfl⟩ : syracuseStep 11064761 = 8298571) B8298571
theorem B1791503 : Blo 794341 1791503 := bstep (se 1 (by rfl) ⟨1343627, by rfl⟩ : syracuseStep 1791503 = 2687255) B2687255
theorem B1791521 : Blo 794341 1791521 := bstep (se 2 (by rfl) ⟨671820, by rfl⟩ : syracuseStep 1791521 = 1343641) B1343641
theorem B1136443 : Blo 794341 1136443 := bstep (se 1 (by rfl) ⟨852332, by rfl⟩ : syracuseStep 1136443 = 1704665) B1704665
theorem B1791863 : Blo 794341 1791863 := bstep (se 1 (by rfl) ⟨1343897, by rfl⟩ : syracuseStep 1791863 = 2687795) B2687795
theorem B1792043 : Blo 794341 1792043 := bstep (se 1 (by rfl) ⟨1344032, by rfl⟩ : syracuseStep 1792043 = 2688065) B2688065
theorem B3987713 : Blo 794341 3987713 := bstep (se 2 (by rfl) ⟨1495392, by rfl⟩ : syracuseStep 3987713 = 2990785) B2990785
theorem B1005959 : Blo 794341 1005959 := bstep (se 1 (by rfl) ⟨754469, by rfl⟩ : syracuseStep 1005959 = 1508939) B1508939
theorem B1792403 : Blo 794341 1792403 := bstep (se 1 (by rfl) ⟨1344302, by rfl⟩ : syracuseStep 1792403 = 2688605) B2688605
theorem B1792457 : Blo 794341 1792457 := bstep (se 2 (by rfl) ⟨672171, by rfl⟩ : syracuseStep 1792457 = 1344343) B1344343
theorem B9067301 : Blo 794341 9067301 := bstep (se 4 (by rfl) ⟨850059, by rfl⟩ : syracuseStep 9067301 = 1700119) B1700119
theorem B2546579 : Blo 794341 2546579 := bstep (se 1 (by rfl) ⟨1909934, by rfl⟩ : syracuseStep 2546579 = 3819869) B3819869
theorem B1006607 : Blo 794341 1006607 := bstep (se 1 (by rfl) ⟨754955, by rfl⟩ : syracuseStep 1006607 = 1509911) B1509911
theorem B1793159 : Blo 794341 1793159 := bstep (se 1 (by rfl) ⟨1344869, by rfl⟩ : syracuseStep 1793159 = 2689739) B2689739
theorem B2415901 : Blo 794341 2415901 := bstep (se 3 (by rfl) ⟨452981, by rfl⟩ : syracuseStep 2415901 = 905963) B905963
theorem B1793339 : Blo 794341 1793339 := bstep (se 1 (by rfl) ⟨1345004, by rfl⟩ : syracuseStep 1793339 = 2690009) B2690009
theorem B9690461 : Blo 794341 9690461 := bstep (se 3 (by rfl) ⟨1816961, by rfl⟩ : syracuseStep 9690461 = 3633923) B3633923
theorem B4021649 : Blo 794341 4021649 := bstep (se 2 (by rfl) ⟨1508118, by rfl⟩ : syracuseStep 4021649 = 3016237) B3016237
theorem B1793465 : Blo 794341 1793465 := bstep (se 2 (by rfl) ⟨672549, by rfl⟩ : syracuseStep 1793465 = 1345099) B1345099
theorem B29122001 : Blo 794341 29122001 := bstep (se 2 (by rfl) ⟨10920750, by rfl⟩ : syracuseStep 29122001 = 21841501) B21841501
theorem B7265795 : Blo 794341 7265795 := bstep (se 1 (by rfl) ⟨5449346, by rfl⟩ : syracuseStep 7265795 = 10898693) B10898693
theorem B6807311 : Blo 794341 6807311 := bstep (se 1 (by rfl) ⟨5105483, by rfl⟩ : syracuseStep 6807311 = 10210967) B10210967
theorem B1793807 : Blo 794341 1793807 := bstep (se 1 (by rfl) ⟨1345355, by rfl⟩ : syracuseStep 1793807 = 2690711) B2690711
theorem B1793825 : Blo 794341 1793825 := bstep (se 2 (by rfl) ⟨672684, by rfl⟩ : syracuseStep 1793825 = 1345369) B1345369
theorem B2875283 : Blo 794341 2875283 := bstep (se 1 (by rfl) ⟨2156462, by rfl⟩ : syracuseStep 2875283 = 4312925) B4312925
theorem B3825731 : Blo 794341 3825731 := bstep (se 1 (by rfl) ⟨2869298, by rfl⟩ : syracuseStep 3825731 = 5738597) B5738597
theorem B1794167 : Blo 794341 1794167 := bstep (se 1 (by rfl) ⟨1345625, by rfl⟩ : syracuseStep 1794167 = 2691251) B2691251
theorem B2187383 : Blo 794341 2187383 := bstep (se 1 (by rfl) ⟨1640537, by rfl⟩ : syracuseStep 2187383 = 3281075) B3281075
theorem B1532039 : Blo 794341 1532039 := bstep (se 1 (by rfl) ⟨1149029, by rfl⟩ : syracuseStep 1532039 = 2298059) B2298059
theorem B2416787 : Blo 794341 2416787 := bstep (se 1 (by rfl) ⟨1812590, by rfl⟩ : syracuseStep 2416787 = 3625181) B3625181
theorem B1794347 : Blo 794341 1794347 := bstep (se 1 (by rfl) ⟨1345760, by rfl⟩ : syracuseStep 1794347 = 2691521) B2691521
theorem B18407897 : Blo 794341 18407897 := bstep (se 2 (by rfl) ⟨6902961, by rfl⟩ : syracuseStep 18407897 = 13805923) B13805923
theorem B1794707 : Blo 794341 1794707 := bstep (se 1 (by rfl) ⟨1346030, by rfl⟩ : syracuseStep 1794707 = 2692061) B2692061
theorem B1794761 : Blo 794341 1794761 := bstep (se 2 (by rfl) ⟨673035, by rfl⟩ : syracuseStep 1794761 = 1346071) B1346071
theorem B5727293 : Blo 794341 5727293 := bstep (se 3 (by rfl) ⟨1073867, by rfl⟩ : syracuseStep 5727293 = 2147735) B2147735
theorem B1795463 : Blo 794341 1795463 := bstep (se 1 (by rfl) ⟨1346597, by rfl⟩ : syracuseStep 1795463 = 2693195) B2693195
theorem B4023755 : Blo 794341 4023755 := bstep (se 1 (by rfl) ⟨3017816, by rfl⟩ : syracuseStep 4023755 = 6035633) B6035633
theorem B1795643 : Blo 794341 1795643 := bstep (se 1 (by rfl) ⟨1346732, by rfl⟩ : syracuseStep 1795643 = 2693465) B2693465
theorem B13625009 : Blo 794341 13625009 := bstep (se 2 (by rfl) ⟨5109378, by rfl⟩ : syracuseStep 13625009 = 10218757) B10218757
theorem B1795769 : Blo 794341 1795769 := bstep (se 2 (by rfl) ⟨673413, by rfl⟩ : syracuseStep 1795769 = 1346827) B1346827
theorem B3401453 : Blo 794341 3401453 := bstep (se 3 (by rfl) ⟨637772, by rfl⟩ : syracuseStep 3401453 = 1275545) B1275545
theorem B4024079 : Blo 794341 4024079 := bstep (se 1 (by rfl) ⟨3018059, by rfl⟩ : syracuseStep 4024079 = 6036119) B6036119
theorem B1075079 : Blo 794341 1075079 := bstep (se 1 (by rfl) ⟨806309, by rfl⟩ : syracuseStep 1075079 = 1612619) B1612619
theorem B1009579 : Blo 794341 1009579 := bstep (se 1 (by rfl) ⟨757184, by rfl⟩ : syracuseStep 1009579 = 1514369) B1514369
theorem B1796111 : Blo 794341 1796111 := bstep (se 1 (by rfl) ⟨1347083, by rfl⟩ : syracuseStep 1796111 = 2694167) B2694167
theorem B1796129 : Blo 794341 1796129 := bstep (se 2 (by rfl) ⟨673548, by rfl⟩ : syracuseStep 1796129 = 1347097) B1347097
theorem B1697993 : Blo 794341 1697993 := bstep (se 2 (by rfl) ⟨636747, by rfl⟩ : syracuseStep 1697993 = 1273495) B1273495
theorem B1075771 : Blo 794341 1075771 := bstep (se 1 (by rfl) ⟨806828, by rfl⟩ : syracuseStep 1075771 = 1613657) B1613657
theorem B49703489 : Blo 794341 49703489 := bstep (se 2 (by rfl) ⟨18638808, by rfl⟩ : syracuseStep 49703489 = 37277617) B37277617
theorem B2681747 : Blo 794341 2681747 := bstep (se 1 (by rfl) ⟨2011310, by rfl⟩ : syracuseStep 2681747 = 4022621) B4022621
theorem B1698745 : Blo 794341 1698745 := bstep (se 2 (by rfl) ⟨637029, by rfl⟩ : syracuseStep 1698745 = 1274059) B1274059
theorem B4025537 : Blo 794341 4025537 := bstep (se 2 (by rfl) ⟨1509576, by rfl⟩ : syracuseStep 4025537 = 3019153) B3019153
theorem B3501521 : Blo 794341 3501521 := bstep (se 2 (by rfl) ⟨1313070, by rfl⟩ : syracuseStep 3501521 = 2626141) B2626141
theorem B1076809 : Blo 794341 1076809 := bstep (se 2 (by rfl) ⟨403803, by rfl⟩ : syracuseStep 1076809 = 807607) B807607
theorem B7270181 : Blo 794341 7270181 := bstep (se 4 (by rfl) ⟨681579, by rfl⟩ : syracuseStep 7270181 = 1363159) B1363159
theorem B2551819 : Blo 794341 2551819 := bstep (se 1 (by rfl) ⟨1913864, by rfl⟩ : syracuseStep 2551819 = 3827729) B3827729
theorem B2683151 : Blo 794341 2683151 := bstep (se 1 (by rfl) ⟨2012363, by rfl⟩ : syracuseStep 2683151 = 4024727) B4024727
theorem B3830075 : Blo 794341 3830075 := bstep (se 1 (by rfl) ⟨2872556, by rfl⟩ : syracuseStep 3830075 = 5745113) B5745113
theorem B4026833 : Blo 794341 4026833 := bstep (se 2 (by rfl) ⟨1510062, by rfl⟩ : syracuseStep 4026833 = 3020125) B3020125
theorem B11497949 : Blo 794341 11497949 := bstep (se 3 (by rfl) ⟨2155865, by rfl⟩ : syracuseStep 11497949 = 4311731) B4311731
theorem B2683421 : Blo 794341 2683421 := bstep (se 3 (by rfl) ⟨503141, by rfl⟩ : syracuseStep 2683421 = 1006283) B1006283
theorem B3404375 : Blo 794341 3404375 := bstep (se 1 (by rfl) ⟨2553281, by rfl⟩ : syracuseStep 3404375 = 5106563) B5106563
theorem B1340617 : Blo 794341 1340617 := bstep (se 2 (by rfl) ⟨502731, by rfl⟩ : syracuseStep 1340617 = 1005463) B1005463
theorem B4355309 : Blo 794341 4355309 := bstep (se 3 (by rfl) ⟨816620, by rfl⟩ : syracuseStep 4355309 = 1633241) B1633241
theorem B1701179 : Blo 794341 1701179 := bstep (se 1 (by rfl) ⟨1275884, by rfl⟩ : syracuseStep 1701179 = 2551769) B2551769
theorem B5731793 : Blo 794341 5731793 := bstep (se 2 (by rfl) ⟨2149422, by rfl⟩ : syracuseStep 5731793 = 4298845) B4298845
theorem B5109277 : Blo 794341 5109277 := bstep (se 3 (by rfl) ⟨957989, by rfl⟩ : syracuseStep 5109277 = 1915979) B1915979
theorem B1341319 : Blo 794341 1341319 := bstep (se 1 (by rfl) ⟨1005989, by rfl⟩ : syracuseStep 1341319 = 2011979) B2011979
theorem B2684825 : Blo 794341 2684825 := bstep (se 2 (by rfl) ⟨1006809, by rfl⟩ : syracuseStep 2684825 = 2013619) B2013619
theorem B1701931 : Blo 794341 1701931 := bstep (se 1 (by rfl) ⟨1276448, by rfl⟩ : syracuseStep 1701931 = 2552897) B2552897
theorem B3733775 : Blo 794341 3733775 := bstep (se 1 (by rfl) ⟨2800331, by rfl⟩ : syracuseStep 3733775 = 5600663) B5600663
theorem B4028939 : Blo 794341 4028939 := bstep (se 1 (by rfl) ⟨3021704, by rfl⟩ : syracuseStep 4028939 = 6043409) B6043409
theorem B1341967 : Blo 794341 1341967 := bstep (se 1 (by rfl) ⟨1006475, by rfl⟩ : syracuseStep 1341967 = 2012951) B2012951
theorem B3832343 : Blo 794341 3832343 := bstep (se 1 (by rfl) ⟨2874257, by rfl⟩ : syracuseStep 3832343 = 5748515) B5748515
theorem B2685527 : Blo 794341 2685527 := bstep (se 1 (by rfl) ⟨2014145, by rfl⟩ : syracuseStep 2685527 = 4028291) B4028291
theorem B4029101 : Blo 794341 4029101 := bstep (se 3 (by rfl) ⟨755456, by rfl⟩ : syracuseStep 4029101 = 1510913) B1510913
theorem B1342507 : Blo 794341 1342507 := bstep (se 1 (by rfl) ⟨1006880, by rfl⟩ : syracuseStep 1342507 = 2013761) B2013761
theorem B2686013 : Blo 794341 2686013 := bstep (se 3 (by rfl) ⟨503627, by rfl⟩ : syracuseStep 2686013 = 1007255) B1007255
theorem B6454333 : Blo 794341 6454333 := bstep (se 3 (by rfl) ⟨1210187, by rfl⟩ : syracuseStep 6454333 = 2420375) B2420375
theorem B1342649 : Blo 794341 1342649 := bstep (se 2 (by rfl) ⟨503493, by rfl⟩ : syracuseStep 1342649 = 1006987) B1006987
theorem B4848929 : Blo 794341 4848929 := bstep (se 2 (by rfl) ⟨1818348, by rfl⟩ : syracuseStep 4848929 = 3636697) B3636697
theorem B5111225 : Blo 794341 5111225 := bstep (se 2 (by rfl) ⟨1916709, by rfl⟩ : syracuseStep 5111225 = 3833419) B3833419
theorem B1146569 : Blo 794341 1146569 := bstep (se 2 (by rfl) ⟨429963, by rfl⟩ : syracuseStep 1146569 = 859927) B859927
theorem B15269633 : Blo 794341 15269633 := bstep (se 2 (by rfl) ⟨5726112, by rfl⟩ : syracuseStep 15269633 = 11452225) B11452225
theorem B7667531 : Blo 794341 7667531 := bstep (se 1 (by rfl) ⟨5750648, by rfl⟩ : syracuseStep 7667531 = 11501297) B11501297
theorem B1343351 : Blo 794341 1343351 := bstep (se 1 (by rfl) ⟨1007513, by rfl⟩ : syracuseStep 1343351 = 2015027) B2015027
theorem B3407825 : Blo 794341 3407825 := bstep (se 2 (by rfl) ⟨1277934, by rfl⟩ : syracuseStep 3407825 = 2555869) B2555869
theorem B1343567 : Blo 794341 1343567 := bstep (se 1 (by rfl) ⟨1007675, by rfl⟩ : syracuseStep 1343567 = 2015351) B2015351
theorem B2687147 : Blo 794341 2687147 := bstep (se 1 (by rfl) ⟨2015360, by rfl⟩ : syracuseStep 2687147 = 4030721) B4030721
theorem B1638599 : Blo 794341 1638599 := bstep (se 1 (by rfl) ⟨1228949, by rfl⟩ : syracuseStep 1638599 = 2457899) B2457899
theorem B5833021 : Blo 794341 5833021 := bstep (se 3 (by rfl) ⟨1093691, by rfl⟩ : syracuseStep 5833021 = 2187383) B2187383
theorem B1278281 : Blo 794341 1278281 := bstep (se 2 (by rfl) ⟨479355, by rfl⟩ : syracuseStep 1278281 = 958711) B958711
theorem B2687687 : Blo 794341 2687687 := bstep (se 1 (by rfl) ⟨2015765, by rfl⟩ : syracuseStep 2687687 = 4031531) B4031531
theorem B1508051 : Blo 794341 1508051 := bstep (se 1 (by rfl) ⟨1131038, by rfl⟩ : syracuseStep 1508051 = 2262077) B2262077
theorem B9077507 : Blo 794341 9077507 := bstep (se 1 (by rfl) ⟨6808130, by rfl⟩ : syracuseStep 9077507 = 13616261) B13616261
theorem B3408713 : Blo 794341 3408713 := bstep (se 2 (by rfl) ⟨1278267, by rfl⟩ : syracuseStep 3408713 = 2556535) B2556535
theorem B1344431 : Blo 794341 1344431 := bstep (se 1 (by rfl) ⟨1008323, by rfl⟩ : syracuseStep 1344431 = 2016647) B2016647
theorem B2557099 : Blo 794341 2557099 := bstep (se 1 (by rfl) ⟨1917824, by rfl⟩ : syracuseStep 2557099 = 3835649) B3835649
theorem B1508681 : Blo 794341 1508681 := bstep (se 2 (by rfl) ⟨565755, by rfl⟩ : syracuseStep 1508681 = 1131511) B1131511
theorem B1344863 : Blo 794341 1344863 := bstep (se 1 (by rfl) ⟨1008647, by rfl⟩ : syracuseStep 1344863 = 2017295) B2017295
theorem B10225115 : Blo 794341 10225115 := bstep (se 1 (by rfl) ⟨7668836, by rfl⟩ : syracuseStep 10225115 = 15337673) B15337673
theorem B2688551 : Blo 794341 2688551 := bstep (se 1 (by rfl) ⟨2016413, by rfl⟩ : syracuseStep 2688551 = 4032827) B4032827
theorem B2688659 : Blo 794341 2688659 := bstep (se 1 (by rfl) ⟨2016494, by rfl⟩ : syracuseStep 2688659 = 4032989) B4032989
theorem B2688875 : Blo 794341 2688875 := bstep (se 1 (by rfl) ⟨2016656, by rfl⟩ : syracuseStep 2688875 = 4033313) B4033313
theorem B1345423 : Blo 794341 1345423 := bstep (se 1 (by rfl) ⟨1009067, by rfl⟩ : syracuseStep 1345423 = 2018135) B2018135
theorem B1935265 : Blo 794341 1935265 := bstep (se 2 (by rfl) ⟨725724, by rfl⟩ : syracuseStep 1935265 = 1451449) B1451449
theorem B2688929 : Blo 794341 2688929 := bstep (se 2 (by rfl) ⟨1008348, by rfl⟩ : syracuseStep 2688929 = 2016697) B2016697
theorem B3016723 : Blo 794341 3016723 := bstep (se 1 (by rfl) ⟨2262542, by rfl⟩ : syracuseStep 3016723 = 4525085) B4525085
theorem B1509455 : Blo 794341 1509455 := bstep (se 1 (by rfl) ⟨1132091, by rfl⟩ : syracuseStep 1509455 = 2264183) B2264183
theorem B3639563 : Blo 794341 3639563 := bstep (se 1 (by rfl) ⟨2729672, by rfl⟩ : syracuseStep 3639563 = 5459345) B5459345
theorem B3148093 : Blo 794341 3148093 := bstep (se 3 (by rfl) ⟨590267, by rfl⟩ : syracuseStep 3148093 = 1180535) B1180535
theorem B1313119 : Blo 794341 1313119 := bstep (se 1 (by rfl) ⟨984839, by rfl⟩ : syracuseStep 1313119 = 1969679) B1969679
theorem B2689523 : Blo 794341 2689523 := bstep (se 1 (by rfl) ⟨2017142, by rfl⟩ : syracuseStep 2689523 = 4034285) B4034285
theorem B1346105 : Blo 794341 1346105 := bstep (se 2 (by rfl) ⟨504789, by rfl⟩ : syracuseStep 1346105 = 1009579) B1009579
theorem B2263751 : Blo 794341 2263751 := bstep (se 1 (by rfl) ⟨1697813, by rfl⟩ : syracuseStep 2263751 = 3395627) B3395627
theorem B2722747 : Blo 794341 2722747 := bstep (se 1 (by rfl) ⟨2042060, by rfl⟩ : syracuseStep 2722747 = 4084121) B4084121
theorem B2690063 : Blo 794341 2690063 := bstep (se 1 (by rfl) ⟨2017547, by rfl⟩ : syracuseStep 2690063 = 4035095) B4035095
theorem B3443791 : Blo 794341 3443791 := bstep (se 1 (by rfl) ⟨2582843, by rfl⟩ : syracuseStep 3443791 = 5165687) B5165687
theorem B20974787 : Blo 794341 20974787 := bstep (se 1 (by rfl) ⟨15731090, by rfl⟩ : syracuseStep 20974787 = 31462181) B31462181
theorem B5049539 : Blo 794341 5049539 := bstep (se 1 (by rfl) ⟨3787154, by rfl⟩ : syracuseStep 5049539 = 7574309) B7574309
theorem B1346807 : Blo 794341 1346807 := bstep (se 1 (by rfl) ⟨1010105, by rfl⟩ : syracuseStep 1346807 = 2020211) B2020211
theorem B1347151 : Blo 794341 1347151 := bstep (se 1 (by rfl) ⟨1010363, by rfl⟩ : syracuseStep 1347151 = 2020727) B2020727
theorem B2690657 : Blo 794341 2690657 := bstep (se 2 (by rfl) ⟨1008996, by rfl⟩ : syracuseStep 2690657 = 2017993) B2017993
theorem B7376507 : Blo 794341 7376507 := bstep (se 1 (by rfl) ⟨5532380, by rfl⟩ : syracuseStep 7376507 = 11064761) B11064761
theorem B1511111 : Blo 794341 1511111 := bstep (se 1 (by rfl) ⟨1133333, by rfl⟩ : syracuseStep 1511111 = 2266667) B2266667
theorem B3018455 : Blo 794341 3018455 := bstep (se 1 (by rfl) ⟨2263841, by rfl⟩ : syracuseStep 3018455 = 4527683) B4527683
theorem B2264993 : Blo 794341 2264993 := bstep (se 2 (by rfl) ⟨849372, by rfl⟩ : syracuseStep 2264993 = 1698745) B1698745
theorem B13111307 : Blo 794341 13111307 := bstep (se 1 (by rfl) ⟨9833480, by rfl⟩ : syracuseStep 13111307 = 19666961) B19666961
theorem B2658475 : Blo 794341 2658475 := bstep (se 1 (by rfl) ⟨1993856, by rfl⟩ : syracuseStep 2658475 = 3987713) B3987713
theorem B38670533 : Blo 794341 38670533 := bstep (se 4 (by rfl) ⟨3625362, by rfl⟩ : syracuseStep 38670533 = 7250725) B7250725
theorem B1511635 : Blo 794341 1511635 := bstep (se 1 (by rfl) ⟨1133726, by rfl⟩ : syracuseStep 1511635 = 2267453) B2267453
theorem B1511855 : Blo 794341 1511855 := bstep (se 1 (by rfl) ⟨1133891, by rfl⟩ : syracuseStep 1511855 = 2267783) B2267783
theorem B4035257 : Blo 794341 4035257 := bstep (se 2 (by rfl) ⟨1513221, by rfl⟩ : syracuseStep 4035257 = 3026443) B3026443
theorem B1512265 : Blo 794341 1512265 := bstep (se 2 (by rfl) ⟨567099, by rfl⟩ : syracuseStep 1512265 = 1134199) B1134199
theorem B3019639 : Blo 794341 3019639 := bstep (se 1 (by rfl) ⟨2264729, by rfl⟩ : syracuseStep 3019639 = 4529459) B4529459
theorem B6460307 : Blo 794341 6460307 := bstep (se 1 (by rfl) ⟨4845230, by rfl⟩ : syracuseStep 6460307 = 9690461) B9690461
theorem B2626561 : Blo 794341 2626561 := bstep (se 2 (by rfl) ⟨984960, by rfl⟩ : syracuseStep 2626561 = 1969921) B1969921
theorem B2692115 : Blo 794341 2692115 := bstep (se 1 (by rfl) ⟨2019086, by rfl⟩ : syracuseStep 2692115 = 4038173) B4038173
theorem B2692439 : Blo 794341 2692439 := bstep (se 1 (by rfl) ⟨2019329, by rfl⟩ : syracuseStep 2692439 = 4038659) B4038659
theorem B1611191 : Blo 794341 1611191 := bstep (se 1 (by rfl) ⟨1208393, by rfl⟩ : syracuseStep 1611191 = 2416787) B2416787
theorem B3020611 : Blo 794341 3020611 := bstep (se 1 (by rfl) ⟨2265458, by rfl⟩ : syracuseStep 3020611 = 4530917) B4530917
theorem B3872783 : Blo 794341 3872783 := bstep (se 1 (by rfl) ⟨2904587, by rfl⟩ : syracuseStep 3872783 = 5809175) B5809175
theorem B3020915 : Blo 794341 3020915 := bstep (se 1 (by rfl) ⟨2265686, by rfl⟩ : syracuseStep 3020915 = 4531373) B4531373
theorem B2693519 : Blo 794341 2693519 := bstep (se 1 (by rfl) ⟨2020139, by rfl⟩ : syracuseStep 2693519 = 4040279) B4040279
theorem B9083339 : Blo 794341 9083339 := bstep (se 1 (by rfl) ⟨6812504, by rfl⟩ : syracuseStep 9083339 = 13625009) B13625009
theorem B2267635 : Blo 794341 2267635 := bstep (se 1 (by rfl) ⟨1700726, by rfl⟩ : syracuseStep 2267635 = 3401453) B3401453
theorem B3021371 : Blo 794341 3021371 := bstep (se 1 (by rfl) ⟨2266028, by rfl⟩ : syracuseStep 3021371 = 4532057) B4532057
theorem B2693843 : Blo 794341 2693843 := bstep (se 1 (by rfl) ⟨2020382, by rfl⟩ : syracuseStep 2693843 = 4040765) B4040765
theorem B33135659 : Blo 794341 33135659 := bstep (se 1 (by rfl) ⟨24851744, by rfl⟩ : syracuseStep 33135659 = 49703489) B49703489
theorem B1514695 : Blo 794341 1514695 := bstep (se 1 (by rfl) ⟨1136021, by rfl⟩ : syracuseStep 1514695 = 2272043) B2272043
theorem B2334347 : Blo 794341 2334347 := bstep (se 1 (by rfl) ⟨1750760, by rfl⟩ : syracuseStep 2334347 = 3501521) B3501521
theorem B9838219 : Blo 794341 9838219 := bstep (se 1 (by rfl) ⟨7378664, by rfl⟩ : syracuseStep 9838219 = 14757329) B14757329
theorem B6790877 : Blo 794341 6790877 := bstep (se 3 (by rfl) ⟨1273289, by rfl⟩ : syracuseStep 6790877 = 2546579) B2546579
theorem B1515257 : Blo 794341 1515257 := bstep (se 2 (by rfl) ⟨568221, by rfl⟩ : syracuseStep 1515257 = 1136443) B1136443
theorem B794407 : Blo 794341 794407 := bstep (se 1 (by rfl) ⟨595805, by rfl⟩ : syracuseStep 794407 = 1191611) B1191611
theorem B794447 : Blo 794341 794447 := bstep (se 1 (by rfl) ⟨595835, by rfl⟩ : syracuseStep 794447 = 1191671) B1191671
theorem B794463 : Blo 794341 794463 := bstep (se 1 (by rfl) ⟨595847, by rfl⟩ : syracuseStep 794463 = 1191695) B1191695
theorem B794491 : Blo 794341 794491 := bstep (se 1 (by rfl) ⟨595868, by rfl⟩ : syracuseStep 794491 = 1191737) B1191737
theorem B794543 : Blo 794341 794543 := bstep (se 1 (by rfl) ⟨595907, by rfl⟩ : syracuseStep 794543 = 1191815) B1191815
theorem B1515439 : Blo 794341 1515439 := bstep (se 1 (by rfl) ⟨1136579, by rfl⟩ : syracuseStep 1515439 = 2273159) B2273159
theorem B794567 : Blo 794341 794567 := bstep (se 1 (by rfl) ⟨595925, by rfl⟩ : syracuseStep 794567 = 1191851) B1191851
theorem B794587 : Blo 794341 794587 := bstep (se 1 (by rfl) ⟨595940, by rfl⟩ : syracuseStep 794587 = 1191881) B1191881
theorem B794663 : Blo 794341 794663 := bstep (se 1 (by rfl) ⟨595997, by rfl⟩ : syracuseStep 794663 = 1191995) B1191995
theorem B2269241 : Blo 794341 2269241 := bstep (se 2 (by rfl) ⟨850965, by rfl⟩ : syracuseStep 2269241 = 1701931) B1701931
theorem B794703 : Blo 794341 794703 := bstep (se 1 (by rfl) ⟨596027, by rfl⟩ : syracuseStep 794703 = 1192055) B1192055
theorem B794719 : Blo 794341 794719 := bstep (se 1 (by rfl) ⟨596039, by rfl⟩ : syracuseStep 794719 = 1192079) B1192079
theorem B794747 : Blo 794341 794747 := bstep (se 1 (by rfl) ⟨596060, by rfl⟩ : syracuseStep 794747 = 1192121) B1192121
theorem B794799 : Blo 794341 794799 := bstep (se 1 (by rfl) ⟨596099, by rfl⟩ : syracuseStep 794799 = 1192199) B1192199
theorem B794823 : Blo 794341 794823 := bstep (se 1 (by rfl) ⟨596117, by rfl⟩ : syracuseStep 794823 = 1192235) B1192235
theorem B794843 : Blo 794341 794843 := bstep (se 1 (by rfl) ⟨596132, by rfl⟩ : syracuseStep 794843 = 1192265) B1192265
theorem B794919 : Blo 794341 794919 := bstep (se 1 (by rfl) ⟨596189, by rfl⟩ : syracuseStep 794919 = 1192379) B1192379
theorem B794959 : Blo 794341 794959 := bstep (se 1 (by rfl) ⟨596219, by rfl⟩ : syracuseStep 794959 = 1192439) B1192439
theorem B794975 : Blo 794341 794975 := bstep (se 1 (by rfl) ⟨596231, by rfl⟩ : syracuseStep 794975 = 1192463) B1192463
theorem B795003 : Blo 794341 795003 := bstep (se 1 (by rfl) ⟨596252, by rfl⟩ : syracuseStep 795003 = 1192505) B1192505
theorem B2269583 : Blo 794341 2269583 := bstep (se 1 (by rfl) ⟨1702187, by rfl⟩ : syracuseStep 2269583 = 3404375) B3404375
theorem B795055 : Blo 794341 795055 := bstep (se 1 (by rfl) ⟨596291, by rfl⟩ : syracuseStep 795055 = 1192583) B1192583
theorem B795079 : Blo 794341 795079 := bstep (se 1 (by rfl) ⟨596309, by rfl⟩ : syracuseStep 795079 = 1192619) B1192619
theorem B795099 : Blo 794341 795099 := bstep (se 1 (by rfl) ⟨596324, by rfl⟩ : syracuseStep 795099 = 1192649) B1192649
theorem B795175 : Blo 794341 795175 := bstep (se 1 (by rfl) ⟨596381, by rfl⟩ : syracuseStep 795175 = 1192763) B1192763
theorem B795215 : Blo 794341 795215 := bstep (se 1 (by rfl) ⟨596411, by rfl⟩ : syracuseStep 795215 = 1192823) B1192823
theorem B795231 : Blo 794341 795231 := bstep (se 1 (by rfl) ⟨596423, by rfl⟩ : syracuseStep 795231 = 1192847) B1192847
theorem B10887797 : Blo 794341 10887797 := bstep (se 5 (by rfl) ⟨510365, by rfl⟩ : syracuseStep 10887797 = 1020731) B1020731
theorem B795259 : Blo 794341 795259 := bstep (se 1 (by rfl) ⟨596444, by rfl⟩ : syracuseStep 795259 = 1192889) B1192889
theorem B795311 : Blo 794341 795311 := bstep (se 1 (by rfl) ⟨596483, by rfl⟩ : syracuseStep 795311 = 1192967) B1192967
theorem B795335 : Blo 794341 795335 := bstep (se 1 (by rfl) ⟨596501, by rfl⟩ : syracuseStep 795335 = 1193003) B1193003
theorem B795355 : Blo 794341 795355 := bstep (se 1 (by rfl) ⟨596516, by rfl⟩ : syracuseStep 795355 = 1193033) B1193033
theorem B795431 : Blo 794341 795431 := bstep (se 1 (by rfl) ⟨596573, by rfl⟩ : syracuseStep 795431 = 1193147) B1193147
theorem B795471 : Blo 794341 795471 := bstep (se 1 (by rfl) ⟨596603, by rfl⟩ : syracuseStep 795471 = 1193207) B1193207
theorem B795487 : Blo 794341 795487 := bstep (se 1 (by rfl) ⟨596615, by rfl⟩ : syracuseStep 795487 = 1193231) B1193231
theorem B795515 : Blo 794341 795515 := bstep (se 1 (by rfl) ⟨596636, by rfl⟩ : syracuseStep 795515 = 1193273) B1193273
theorem B795567 : Blo 794341 795567 := bstep (se 1 (by rfl) ⟨596675, by rfl⟩ : syracuseStep 795567 = 1193351) B1193351
theorem B795591 : Blo 794341 795591 := bstep (se 1 (by rfl) ⟨596693, by rfl⟩ : syracuseStep 795591 = 1193387) B1193387
theorem B795611 : Blo 794341 795611 := bstep (se 1 (by rfl) ⟨596708, by rfl⟩ : syracuseStep 795611 = 1193417) B1193417
theorem B795687 : Blo 794341 795687 := bstep (se 1 (by rfl) ⟨596765, by rfl⟩ : syracuseStep 795687 = 1193531) B1193531
theorem B795727 : Blo 794341 795727 := bstep (se 1 (by rfl) ⟨596795, by rfl⟩ : syracuseStep 795727 = 1193591) B1193591
theorem B795743 : Blo 794341 795743 := bstep (se 1 (by rfl) ⟨596807, by rfl⟩ : syracuseStep 795743 = 1193615) B1193615
theorem B795771 : Blo 794341 795771 := bstep (se 1 (by rfl) ⟨596828, by rfl⟩ : syracuseStep 795771 = 1193657) B1193657
theorem B795823 : Blo 794341 795823 := bstep (se 1 (by rfl) ⟨596867, by rfl⟩ : syracuseStep 795823 = 1193735) B1193735
theorem B795847 : Blo 794341 795847 := bstep (se 1 (by rfl) ⟨596885, by rfl⟩ : syracuseStep 795847 = 1193771) B1193771
theorem B795867 : Blo 794341 795867 := bstep (se 1 (by rfl) ⟨596900, by rfl⟩ : syracuseStep 795867 = 1193801) B1193801
theorem B795943 : Blo 794341 795943 := bstep (se 1 (by rfl) ⟨596957, by rfl⟩ : syracuseStep 795943 = 1193915) B1193915
theorem B795983 : Blo 794341 795983 := bstep (se 1 (by rfl) ⟨596987, by rfl⟩ : syracuseStep 795983 = 1193975) B1193975
theorem B19375453 : Blo 794341 19375453 := bstep (se 3 (by rfl) ⟨3632897, by rfl⟩ : syracuseStep 19375453 = 7265795) B7265795
theorem B795999 : Blo 794341 795999 := bstep (se 1 (by rfl) ⟨596999, by rfl⟩ : syracuseStep 795999 = 1193999) B1193999
theorem B796027 : Blo 794341 796027 := bstep (se 1 (by rfl) ⟨597020, by rfl⟩ : syracuseStep 796027 = 1194041) B1194041
theorem B796079 : Blo 794341 796079 := bstep (se 1 (by rfl) ⟨597059, by rfl⟩ : syracuseStep 796079 = 1194119) B1194119
theorem B796103 : Blo 794341 796103 := bstep (se 1 (by rfl) ⟨597077, by rfl⟩ : syracuseStep 796103 = 1194155) B1194155
theorem B796123 : Blo 794341 796123 := bstep (se 1 (by rfl) ⟨597092, by rfl⟩ : syracuseStep 796123 = 1194185) B1194185
theorem B796199 : Blo 794341 796199 := bstep (se 1 (by rfl) ⟨597149, by rfl⟩ : syracuseStep 796199 = 1194299) B1194299
theorem B796239 : Blo 794341 796239 := bstep (se 1 (by rfl) ⟨597179, by rfl⟩ : syracuseStep 796239 = 1194359) B1194359
theorem B796255 : Blo 794341 796255 := bstep (se 1 (by rfl) ⟨597191, by rfl⟩ : syracuseStep 796255 = 1194383) B1194383
theorem B796283 : Blo 794341 796283 := bstep (se 1 (by rfl) ⟨597212, by rfl⟩ : syracuseStep 796283 = 1194425) B1194425
theorem B796335 : Blo 794341 796335 := bstep (se 1 (by rfl) ⟨597251, by rfl⟩ : syracuseStep 796335 = 1194503) B1194503
theorem B796359 : Blo 794341 796359 := bstep (se 1 (by rfl) ⟨597269, by rfl⟩ : syracuseStep 796359 = 1194539) B1194539
theorem B3221201 : Blo 794341 3221201 := bstep (se 2 (by rfl) ⟨1207950, by rfl⟩ : syracuseStep 3221201 = 2415901) B2415901
theorem B796379 : Blo 794341 796379 := bstep (se 1 (by rfl) ⟨597284, by rfl⟩ : syracuseStep 796379 = 1194569) B1194569
theorem B4040441 : Blo 794341 4040441 := bstep (se 2 (by rfl) ⟨1515165, by rfl⟩ : syracuseStep 4040441 = 3030331) B3030331
theorem B796455 : Blo 794341 796455 := bstep (se 1 (by rfl) ⟨597341, by rfl⟩ : syracuseStep 796455 = 1194683) B1194683
theorem B796495 : Blo 794341 796495 := bstep (se 1 (by rfl) ⟨597371, by rfl⟩ : syracuseStep 796495 = 1194743) B1194743
theorem B796511 : Blo 794341 796511 := bstep (se 1 (by rfl) ⟨597383, by rfl⟩ : syracuseStep 796511 = 1194767) B1194767
theorem B3057517 : Blo 794341 3057517 := bstep (se 3 (by rfl) ⟨573284, by rfl⟩ : syracuseStep 3057517 = 1146569) B1146569
theorem B796539 : Blo 794341 796539 := bstep (se 1 (by rfl) ⟨597404, by rfl⟩ : syracuseStep 796539 = 1194809) B1194809
theorem B796591 : Blo 794341 796591 := bstep (se 1 (by rfl) ⟨597443, by rfl⟩ : syracuseStep 796591 = 1194887) B1194887
theorem B796615 : Blo 794341 796615 := bstep (se 1 (by rfl) ⟨597461, by rfl⟩ : syracuseStep 796615 = 1194923) B1194923
theorem B796635 : Blo 794341 796635 := bstep (se 1 (by rfl) ⟨597476, by rfl⟩ : syracuseStep 796635 = 1194953) B1194953
theorem B796711 : Blo 794341 796711 := bstep (se 1 (by rfl) ⟨597533, by rfl⟩ : syracuseStep 796711 = 1195067) B1195067
theorem B796751 : Blo 794341 796751 := bstep (se 1 (by rfl) ⟨597563, by rfl⟩ : syracuseStep 796751 = 1195127) B1195127
theorem B796767 : Blo 794341 796767 := bstep (se 1 (by rfl) ⟨597575, by rfl⟩ : syracuseStep 796767 = 1195151) B1195151
theorem B895099 : Blo 794341 895099 := bstep (se 1 (by rfl) ⟨671324, by rfl⟩ : syracuseStep 895099 = 1342649) B1342649
theorem B796795 : Blo 794341 796795 := bstep (se 1 (by rfl) ⟨597596, by rfl⟩ : syracuseStep 796795 = 1195193) B1195193
theorem B796847 : Blo 794341 796847 := bstep (se 1 (by rfl) ⟨597635, by rfl⟩ : syracuseStep 796847 = 1195271) B1195271
theorem B796871 : Blo 794341 796871 := bstep (se 1 (by rfl) ⟨597653, by rfl⟩ : syracuseStep 796871 = 1195307) B1195307
theorem B796891 : Blo 794341 796891 := bstep (se 1 (by rfl) ⟨597668, by rfl⟩ : syracuseStep 796891 = 1195337) B1195337
theorem B796967 : Blo 794341 796967 := bstep (se 1 (by rfl) ⟨597725, by rfl⟩ : syracuseStep 796967 = 1195451) B1195451
theorem B797007 : Blo 794341 797007 := bstep (se 1 (by rfl) ⟨597755, by rfl⟩ : syracuseStep 797007 = 1195511) B1195511
theorem B797023 : Blo 794341 797023 := bstep (se 1 (by rfl) ⟨597767, by rfl⟩ : syracuseStep 797023 = 1195535) B1195535
theorem B797051 : Blo 794341 797051 := bstep (se 1 (by rfl) ⟨597788, by rfl⟩ : syracuseStep 797051 = 1195577) B1195577
theorem B4041089 : Blo 794341 4041089 := bstep (se 2 (by rfl) ⟨1515408, by rfl⟩ : syracuseStep 4041089 = 3030817) B3030817
theorem B797103 : Blo 794341 797103 := bstep (se 1 (by rfl) ⟨597827, by rfl⟩ : syracuseStep 797103 = 1195655) B1195655
theorem B797127 : Blo 794341 797127 := bstep (se 1 (by rfl) ⟨597845, by rfl⟩ : syracuseStep 797127 = 1195691) B1195691
theorem B797147 : Blo 794341 797147 := bstep (se 1 (by rfl) ⟨597860, by rfl⟩ : syracuseStep 797147 = 1195721) B1195721
theorem B797223 : Blo 794341 797223 := bstep (se 1 (by rfl) ⟨597917, by rfl⟩ : syracuseStep 797223 = 1195835) B1195835
theorem B895567 : Blo 794341 895567 := bstep (se 1 (by rfl) ⟨671675, by rfl⟩ : syracuseStep 895567 = 1343351) B1343351
theorem B797263 : Blo 794341 797263 := bstep (se 1 (by rfl) ⟨597947, by rfl⟩ : syracuseStep 797263 = 1195895) B1195895
theorem B797279 : Blo 794341 797279 := bstep (se 1 (by rfl) ⟨597959, by rfl⟩ : syracuseStep 797279 = 1195919) B1195919
theorem B797307 : Blo 794341 797307 := bstep (se 1 (by rfl) ⟨597980, by rfl⟩ : syracuseStep 797307 = 1195961) B1195961
theorem B2271883 : Blo 794341 2271883 := bstep (se 1 (by rfl) ⟨1703912, by rfl⟩ : syracuseStep 2271883 = 3407825) B3407825
theorem B797359 : Blo 794341 797359 := bstep (se 1 (by rfl) ⟨598019, by rfl⟩ : syracuseStep 797359 = 1196039) B1196039
theorem B797383 : Blo 794341 797383 := bstep (se 1 (by rfl) ⟨598037, by rfl⟩ : syracuseStep 797383 = 1196075) B1196075
theorem B797403 : Blo 794341 797403 := bstep (se 1 (by rfl) ⟨598052, by rfl⟩ : syracuseStep 797403 = 1196105) B1196105
theorem B797479 : Blo 794341 797479 := bstep (se 1 (by rfl) ⟨598109, by rfl⟩ : syracuseStep 797479 = 1196219) B1196219
theorem B3058505 : Blo 794341 3058505 := bstep (se 2 (by rfl) ⟨1146939, by rfl⟩ : syracuseStep 3058505 = 2293879) B2293879
theorem B797519 : Blo 794341 797519 := bstep (se 1 (by rfl) ⟨598139, by rfl⟩ : syracuseStep 797519 = 1196279) B1196279
theorem B797535 : Blo 794341 797535 := bstep (se 1 (by rfl) ⟨598151, by rfl⟩ : syracuseStep 797535 = 1196303) B1196303
theorem B797563 : Blo 794341 797563 := bstep (se 1 (by rfl) ⟨598172, by rfl⟩ : syracuseStep 797563 = 1196345) B1196345
theorem B797615 : Blo 794341 797615 := bstep (se 1 (by rfl) ⟨598211, by rfl⟩ : syracuseStep 797615 = 1196423) B1196423
theorem B797639 : Blo 794341 797639 := bstep (se 1 (by rfl) ⟨598229, by rfl⟩ : syracuseStep 797639 = 1196459) B1196459
theorem B895963 : Blo 794341 895963 := bstep (se 1 (by rfl) ⟨671972, by rfl⟩ : syracuseStep 895963 = 1343945) B1343945
theorem B797659 : Blo 794341 797659 := bstep (se 1 (by rfl) ⟨598244, by rfl⟩ : syracuseStep 797659 = 1196489) B1196489
theorem B5975005 : Blo 794341 5975005 := bstep (se 3 (by rfl) ⟨1120313, by rfl⟩ : syracuseStep 5975005 = 2240627) B2240627
theorem B830503 : Blo 794341 830503 := bstep (se 1 (by rfl) ⟨622877, by rfl⟩ : syracuseStep 830503 = 1245755) B1245755
theorem B797735 : Blo 794341 797735 := bstep (se 1 (by rfl) ⟨598301, by rfl⟩ : syracuseStep 797735 = 1196603) B1196603
theorem B1911887 : Blo 794341 1911887 := bstep (se 1 (by rfl) ⟨1433915, by rfl⟩ : syracuseStep 1911887 = 2867831) B2867831
theorem B797775 : Blo 794341 797775 := bstep (se 1 (by rfl) ⟨598331, by rfl⟩ : syracuseStep 797775 = 1196663) B1196663
theorem B797791 : Blo 794341 797791 := bstep (se 1 (by rfl) ⟨598343, by rfl⟩ : syracuseStep 797791 = 1196687) B1196687
theorem B797819 : Blo 794341 797819 := bstep (se 1 (by rfl) ⟨598364, by rfl⟩ : syracuseStep 797819 = 1196729) B1196729
theorem B797871 : Blo 794341 797871 := bstep (se 1 (by rfl) ⟨598403, by rfl⟩ : syracuseStep 797871 = 1196807) B1196807
theorem B797895 : Blo 794341 797895 := bstep (se 1 (by rfl) ⟨598421, by rfl⟩ : syracuseStep 797895 = 1196843) B1196843
theorem B797915 : Blo 794341 797915 := bstep (se 1 (by rfl) ⟨598436, by rfl⟩ : syracuseStep 797915 = 1196873) B1196873
theorem B4304119 : Blo 794341 4304119 := bstep (se 1 (by rfl) ⟨3228089, by rfl⟩ : syracuseStep 4304119 = 6456179) B6456179
theorem B797991 : Blo 794341 797991 := bstep (se 1 (by rfl) ⟨598493, by rfl⟩ : syracuseStep 797991 = 1196987) B1196987
theorem B798031 : Blo 794341 798031 := bstep (se 1 (by rfl) ⟨598523, by rfl⟩ : syracuseStep 798031 = 1197047) B1197047
theorem B798047 : Blo 794341 798047 := bstep (se 1 (by rfl) ⟨598535, by rfl⟩ : syracuseStep 798047 = 1197071) B1197071
theorem B798075 : Blo 794341 798075 := bstep (se 1 (by rfl) ⟨598556, by rfl⟩ : syracuseStep 798075 = 1197113) B1197113
theorem B1813903 : Blo 794341 1813903 := bstep (se 1 (by rfl) ⟨1360427, by rfl⟩ : syracuseStep 1813903 = 2720855) B2720855
theorem B896431 : Blo 794341 896431 := bstep (se 1 (by rfl) ⟨672323, by rfl⟩ : syracuseStep 896431 = 1344647) B1344647
theorem B798127 : Blo 794341 798127 := bstep (se 1 (by rfl) ⟨598595, by rfl⟩ : syracuseStep 798127 = 1197191) B1197191
theorem B798151 : Blo 794341 798151 := bstep (se 1 (by rfl) ⟨598613, by rfl⟩ : syracuseStep 798151 = 1197227) B1197227
theorem B798171 : Blo 794341 798171 := bstep (se 1 (by rfl) ⟨598628, by rfl⟩ : syracuseStep 798171 = 1197257) B1197257
theorem B3059225 : Blo 794341 3059225 := bstep (se 2 (by rfl) ⟨1147209, by rfl⟩ : syracuseStep 3059225 = 2294419) B2294419
theorem B798247 : Blo 794341 798247 := bstep (se 1 (by rfl) ⟨598685, by rfl⟩ : syracuseStep 798247 = 1197371) B1197371
theorem B1289785 : Blo 794341 1289785 := bstep (se 2 (by rfl) ⟨483669, by rfl⟩ : syracuseStep 1289785 = 967339) B967339
theorem B798287 : Blo 794341 798287 := bstep (se 1 (by rfl) ⟨598715, by rfl⟩ : syracuseStep 798287 = 1197431) B1197431
theorem B798303 : Blo 794341 798303 := bstep (se 1 (by rfl) ⟨598727, by rfl⟩ : syracuseStep 798303 = 1197455) B1197455
theorem B798331 : Blo 794341 798331 := bstep (se 1 (by rfl) ⟨598748, by rfl⟩ : syracuseStep 798331 = 1197497) B1197497
theorem B24489661 : Blo 794341 24489661 := bstep (se 3 (by rfl) ⟨4591811, by rfl⟩ : syracuseStep 24489661 = 9183623) B9183623
theorem B1191623 : Blo 794341 1191623 := bstep (se 1 (by rfl) ⟨893717, by rfl⟩ : syracuseStep 1191623 = 1787435) B1787435
theorem B6205177 : Blo 794341 6205177 := bstep (se 2 (by rfl) ⟨2326941, by rfl⟩ : syracuseStep 6205177 = 4653883) B4653883
theorem B3026717 : Blo 794341 3026717 := bstep (se 3 (by rfl) ⟨567509, by rfl⟩ : syracuseStep 3026717 = 1135019) B1135019
theorem B896863 : Blo 794341 896863 := bstep (se 1 (by rfl) ⟨672647, by rfl⟩ : syracuseStep 896863 = 1345295) B1345295
theorem B1191785 : Blo 794341 1191785 := bstep (se 2 (by rfl) ⟨446919, by rfl⟩ : syracuseStep 1191785 = 893839) B893839
theorem B12922739 : Blo 794341 12922739 := bstep (se 1 (by rfl) ⟨9692054, by rfl⟩ : syracuseStep 12922739 = 19384109) B19384109
theorem B1191863 : Blo 794341 1191863 := bstep (se 1 (by rfl) ⟨893897, by rfl⟩ : syracuseStep 1191863 = 1787795) B1787795
theorem B1191899 : Blo 794341 1191899 := bstep (se 1 (by rfl) ⟨893924, by rfl⟩ : syracuseStep 1191899 = 1787849) B1787849
theorem B897223 : Blo 794341 897223 := bstep (se 1 (by rfl) ⟨672917, by rfl⟩ : syracuseStep 897223 = 1345835) B1345835
theorem B1192367 : Blo 794341 1192367 := bstep (se 1 (by rfl) ⟨894275, by rfl⟩ : syracuseStep 1192367 = 1788551) B1788551
theorem B3027401 : Blo 794341 3027401 := bstep (se 2 (by rfl) ⟨1135275, by rfl⟩ : syracuseStep 3027401 = 2270551) B2270551
theorem B2044379 : Blo 794341 2044379 := bstep (se 1 (by rfl) ⟨1533284, by rfl⟩ : syracuseStep 2044379 = 3066569) B3066569
theorem B1192457 : Blo 794341 1192457 := bstep (se 2 (by rfl) ⟨447171, by rfl⟩ : syracuseStep 1192457 = 894343) B894343
theorem B1192487 : Blo 794341 1192487 := bstep (se 1 (by rfl) ⟨894365, by rfl⟩ : syracuseStep 1192487 = 1788731) B1788731
theorem B1192571 : Blo 794341 1192571 := bstep (se 1 (by rfl) ⟨894428, by rfl⟩ : syracuseStep 1192571 = 1788857) B1788857
theorem B2011787 : Blo 794341 2011787 := bstep (se 1 (by rfl) ⟨1508840, by rfl⟩ : syracuseStep 2011787 = 3017681) B3017681
theorem B1192697 : Blo 794341 1192697 := bstep (se 2 (by rfl) ⟨447261, by rfl⟩ : syracuseStep 1192697 = 894523) B894523
theorem B2011999 : Blo 794341 2011999 := bstep (se 1 (by rfl) ⟨1508999, by rfl⟩ : syracuseStep 2011999 = 3017999) B3017999
theorem B1192799 : Blo 794341 1192799 := bstep (se 1 (by rfl) ⟨894599, by rfl⟩ : syracuseStep 1192799 = 1789199) B1789199
theorem B1192811 : Blo 794341 1192811 := bstep (se 1 (by rfl) ⟨894608, by rfl⟩ : syracuseStep 1192811 = 1789217) B1789217
theorem B3027887 : Blo 794341 3027887 := bstep (se 1 (by rfl) ⟨2270915, by rfl⟩ : syracuseStep 3027887 = 4541831) B4541831
theorem B898087 : Blo 794341 898087 := bstep (se 1 (by rfl) ⟨673565, by rfl⟩ : syracuseStep 898087 = 1347131) B1347131
theorem B1193039 : Blo 794341 1193039 := bstep (se 1 (by rfl) ⟨894779, by rfl⟩ : syracuseStep 1193039 = 1789559) B1789559
theorem B1193159 : Blo 794341 1193159 := bstep (se 1 (by rfl) ⟨894869, by rfl⟩ : syracuseStep 1193159 = 1789739) B1789739
theorem B1193321 : Blo 794341 1193321 := bstep (se 2 (by rfl) ⟨447495, by rfl⟩ : syracuseStep 1193321 = 894991) B894991
theorem B1193399 : Blo 794341 1193399 := bstep (se 1 (by rfl) ⟨895049, by rfl⟩ : syracuseStep 1193399 = 1790099) B1790099
theorem B1193435 : Blo 794341 1193435 := bstep (se 1 (by rfl) ⟨895076, by rfl⟩ : syracuseStep 1193435 = 1790153) B1790153
theorem B15513281 : Blo 794341 15513281 := bstep (se 2 (by rfl) ⟨5817480, by rfl⟩ : syracuseStep 15513281 = 11634961) B11634961
theorem B3028691 : Blo 794341 3028691 := bstep (se 1 (by rfl) ⟨2271518, by rfl⟩ : syracuseStep 3028691 = 4543037) B4543037
theorem B2012921 : Blo 794341 2012921 := bstep (se 2 (by rfl) ⟨754845, by rfl⟩ : syracuseStep 2012921 = 1509691) B1509691
theorem B1914731 : Blo 794341 1914731 := bstep (se 1 (by rfl) ⟨1436048, by rfl⟩ : syracuseStep 1914731 = 2872097) B2872097
theorem B1193903 : Blo 794341 1193903 := bstep (se 1 (by rfl) ⟨895427, by rfl⟩ : syracuseStep 1193903 = 1790855) B1790855
theorem B1193993 : Blo 794341 1193993 := bstep (se 2 (by rfl) ⟨447747, by rfl⟩ : syracuseStep 1193993 = 895495) B895495
theorem B1194023 : Blo 794341 1194023 := bstep (se 1 (by rfl) ⟨895517, by rfl⟩ : syracuseStep 1194023 = 1791035) B1791035
theorem B1194107 : Blo 794341 1194107 := bstep (se 1 (by rfl) ⟨895580, by rfl⟩ : syracuseStep 1194107 = 1791161) B1791161
theorem B1194233 : Blo 794341 1194233 := bstep (se 2 (by rfl) ⟨447837, by rfl⟩ : syracuseStep 1194233 = 895675) B895675
theorem B1194335 : Blo 794341 1194335 := bstep (se 1 (by rfl) ⟨895751, by rfl⟩ : syracuseStep 1194335 = 1791503) B1791503
theorem B1194347 : Blo 794341 1194347 := bstep (se 1 (by rfl) ⟨895760, by rfl⟩ : syracuseStep 1194347 = 1791521) B1791521
theorem B2013569 : Blo 794341 2013569 := bstep (se 2 (by rfl) ⟨755088, by rfl⟩ : syracuseStep 2013569 = 1510177) B1510177
theorem B1194575 : Blo 794341 1194575 := bstep (se 1 (by rfl) ⟨895931, by rfl⟩ : syracuseStep 1194575 = 1791863) B1791863
theorem B1194695 : Blo 794341 1194695 := bstep (se 1 (by rfl) ⟨896021, by rfl⟩ : syracuseStep 1194695 = 1792043) B1792043
theorem B7256861 : Blo 794341 7256861 := bstep (se 3 (by rfl) ⟨1360661, by rfl⟩ : syracuseStep 7256861 = 2721323) B2721323
theorem B1194857 : Blo 794341 1194857 := bstep (se 2 (by rfl) ⟨448071, by rfl⟩ : syracuseStep 1194857 = 896143) B896143
theorem B1194935 : Blo 794341 1194935 := bstep (se 1 (by rfl) ⟨896201, by rfl⟩ : syracuseStep 1194935 = 1792403) B1792403
theorem B1194971 : Blo 794341 1194971 := bstep (se 1 (by rfl) ⟨896228, by rfl⟩ : syracuseStep 1194971 = 1792457) B1792457
theorem B2014379 : Blo 794341 2014379 := bstep (se 1 (by rfl) ⟨1510784, by rfl⟩ : syracuseStep 2014379 = 3021569) B3021569
theorem B6044867 : Blo 794341 6044867 := bstep (se 1 (by rfl) ⟨4533650, by rfl⟩ : syracuseStep 6044867 = 9067301) B9067301
theorem B3325313 : Blo 794341 3325313 := bstep (se 2 (by rfl) ⟨1246992, by rfl⟩ : syracuseStep 3325313 = 2493985) B2493985
theorem B1195439 : Blo 794341 1195439 := bstep (se 1 (by rfl) ⟨896579, by rfl⟩ : syracuseStep 1195439 = 1793159) B1793159
theorem B1195529 : Blo 794341 1195529 := bstep (se 2 (by rfl) ⟨448323, by rfl⟩ : syracuseStep 1195529 = 896647) B896647
theorem B1195559 : Blo 794341 1195559 := bstep (se 1 (by rfl) ⟨896669, by rfl⟩ : syracuseStep 1195559 = 1793339) B1793339
theorem B2866747 : Blo 794341 2866747 := bstep (se 1 (by rfl) ⟨2150060, by rfl⟩ : syracuseStep 2866747 = 4300121) B4300121
theorem B1195643 : Blo 794341 1195643 := bstep (se 1 (by rfl) ⟨896732, by rfl⟩ : syracuseStep 1195643 = 1793465) B1793465
theorem B19414667 : Blo 794341 19414667 := bstep (se 1 (by rfl) ⟨14561000, by rfl⟩ : syracuseStep 19414667 = 29122001) B29122001
theorem B2866877 : Blo 794341 2866877 := bstep (se 3 (by rfl) ⟨537539, by rfl⟩ : syracuseStep 2866877 = 1075079) B1075079
theorem B1195769 : Blo 794341 1195769 := bstep (se 2 (by rfl) ⟨448413, by rfl⟩ : syracuseStep 1195769 = 896827) B896827
theorem B13811471 : Blo 794341 13811471 := bstep (se 1 (by rfl) ⟨10358603, by rfl⟩ : syracuseStep 13811471 = 20717207) B20717207
theorem B4538207 : Blo 794341 4538207 := bstep (se 1 (by rfl) ⟨3403655, by rfl⟩ : syracuseStep 4538207 = 6807311) B6807311
theorem B1195871 : Blo 794341 1195871 := bstep (se 1 (by rfl) ⟨896903, by rfl⟩ : syracuseStep 1195871 = 1793807) B1793807
theorem B1195883 : Blo 794341 1195883 := bstep (se 1 (by rfl) ⟨896912, by rfl⟩ : syracuseStep 1195883 = 1793825) B1793825
theorem B1916855 : Blo 794341 1916855 := bstep (se 1 (by rfl) ⟨1437641, by rfl⟩ : syracuseStep 1916855 = 2875283) B2875283
theorem B2015239 : Blo 794341 2015239 := bstep (se 1 (by rfl) ⟨1511429, by rfl⟩ : syracuseStep 2015239 = 3022859) B3022859
theorem B1196111 : Blo 794341 1196111 := bstep (se 1 (by rfl) ⟨897083, by rfl⟩ : syracuseStep 1196111 = 1794167) B1794167
theorem B3031121 : Blo 794341 3031121 := bstep (se 2 (by rfl) ⟨1136670, by rfl⟩ : syracuseStep 3031121 = 2273341) B2273341
theorem B1196231 : Blo 794341 1196231 := bstep (se 1 (by rfl) ⟨897173, by rfl⟩ : syracuseStep 1196231 = 1794347) B1794347
theorem B12271931 : Blo 794341 12271931 := bstep (se 1 (by rfl) ⟨9203948, by rfl⟩ : syracuseStep 12271931 = 18407897) B18407897
theorem B4309309 : Blo 794341 4309309 := bstep (se 3 (by rfl) ⟨807995, by rfl⟩ : syracuseStep 4309309 = 1615991) B1615991
theorem B1196393 : Blo 794341 1196393 := bstep (se 2 (by rfl) ⟨448647, by rfl⟩ : syracuseStep 1196393 = 897295) B897295
theorem B1196471 : Blo 794341 1196471 := bstep (se 1 (by rfl) ⟨897353, by rfl⟩ : syracuseStep 1196471 = 1794707) B1794707
theorem B1196507 : Blo 794341 1196507 := bstep (se 1 (by rfl) ⟨897380, by rfl⟩ : syracuseStep 1196507 = 1794761) B1794761
theorem B2015867 : Blo 794341 2015867 := bstep (se 1 (by rfl) ⟨1511900, by rfl⟩ : syracuseStep 2015867 = 3023801) B3023801
theorem B3818195 : Blo 794341 3818195 := bstep (se 1 (by rfl) ⟨2863646, by rfl⟩ : syracuseStep 3818195 = 5727293) B5727293
theorem B2016161 : Blo 794341 2016161 := bstep (se 2 (by rfl) ⟨756060, by rfl⟩ : syracuseStep 2016161 = 1512121) B1512121
theorem B1196975 : Blo 794341 1196975 := bstep (se 1 (by rfl) ⟨897731, by rfl⟩ : syracuseStep 1196975 = 1795463) B1795463
theorem B1197065 : Blo 794341 1197065 := bstep (se 2 (by rfl) ⟨448899, by rfl⟩ : syracuseStep 1197065 = 897799) B897799
theorem B1197095 : Blo 794341 1197095 := bstep (se 1 (by rfl) ⟨897821, by rfl⟩ : syracuseStep 1197095 = 1795643) B1795643
theorem B1197179 : Blo 794341 1197179 := bstep (se 1 (by rfl) ⟨897884, by rfl⟩ : syracuseStep 1197179 = 1795769) B1795769
theorem B1197305 : Blo 794341 1197305 := bstep (se 2 (by rfl) ⟨448989, by rfl⟩ : syracuseStep 1197305 = 897979) B897979
theorem B3065149 : Blo 794341 3065149 := bstep (se 3 (by rfl) ⟨574715, by rfl⟩ : syracuseStep 3065149 = 1149431) B1149431
theorem B1197407 : Blo 794341 1197407 := bstep (se 1 (by rfl) ⟨898055, by rfl⟩ : syracuseStep 1197407 = 1796111) B1796111
theorem B1197419 : Blo 794341 1197419 := bstep (se 1 (by rfl) ⟨898064, by rfl⟩ : syracuseStep 1197419 = 1796129) B1796129
theorem B1131995 : Blo 794341 1131995 := bstep (se 1 (by rfl) ⟨848996, by rfl⟩ : syracuseStep 1131995 = 1697993) B1697993
theorem B4310567 : Blo 794341 4310567 := bstep (se 1 (by rfl) ⟨3232925, by rfl⟩ : syracuseStep 4310567 = 6465851) B6465851
theorem B1787489 : Blo 794341 1787489 := bstep (se 2 (by rfl) ⟨670308, by rfl⟩ : syracuseStep 1787489 = 1340617) B1340617
theorem B2148191 : Blo 794341 2148191 := bstep (se 1 (by rfl) ⟨1611143, by rfl⟩ : syracuseStep 2148191 = 3222287) B3222287
theorem B1787831 : Blo 794341 1787831 := bstep (se 1 (by rfl) ⟨1340873, by rfl⟩ : syracuseStep 1787831 = 2681747) B2681747
theorem B5097487 : Blo 794341 5097487 := bstep (se 1 (by rfl) ⟨3823115, by rfl⟩ : syracuseStep 5097487 = 7646231) B7646231
theorem B2902397 : Blo 794341 2902397 := bstep (se 3 (by rfl) ⟨544199, by rfl⟩ : syracuseStep 2902397 = 1088399) B1088399
theorem B1788425 : Blo 794341 1788425 := bstep (se 2 (by rfl) ⟨670659, by rfl⟩ : syracuseStep 1788425 = 1341319) B1341319
theorem B2017831 : Blo 794341 2017831 := bstep (se 1 (by rfl) ⟨1513373, by rfl⟩ : syracuseStep 2017831 = 3026747) B3026747
theorem B3066491 : Blo 794341 3066491 := bstep (se 1 (by rfl) ⟨2299868, by rfl⟩ : syracuseStep 3066491 = 4599737) B4599737
theorem B16534217 : Blo 794341 16534217 := bstep (se 2 (by rfl) ⟨6200331, by rfl⟩ : syracuseStep 16534217 = 12400663) B12400663
theorem B1788767 : Blo 794341 1788767 := bstep (se 1 (by rfl) ⟨1341575, by rfl⟩ : syracuseStep 1788767 = 2683151) B2683151
theorem B2018155 : Blo 794341 2018155 := bstep (se 1 (by rfl) ⟨1513616, by rfl⟩ : syracuseStep 2018155 = 3027233) B3027233
theorem B3066785 : Blo 794341 3066785 := bstep (se 2 (by rfl) ⟨1150044, by rfl⟩ : syracuseStep 3066785 = 2300089) B2300089
theorem B2870279 : Blo 794341 2870279 := bstep (se 1 (by rfl) ⟨2152709, by rfl⟩ : syracuseStep 2870279 = 4305419) B4305419
theorem B1788947 : Blo 794341 1788947 := bstep (se 1 (by rfl) ⟨1341710, by rfl⟩ : syracuseStep 1788947 = 2683421) B2683421
theorem B1789289 : Blo 794341 1789289 := bstep (se 2 (by rfl) ⟨670983, by rfl⟩ : syracuseStep 1789289 = 1341967) B1341967
theorem B2903539 : Blo 794341 2903539 := bstep (se 1 (by rfl) ⟨2177654, by rfl⟩ : syracuseStep 2903539 = 4355309) B4355309
theorem B2018803 : Blo 794341 2018803 := bstep (se 1 (by rfl) ⟨1514102, by rfl⟩ : syracuseStep 2018803 = 3028205) B3028205
theorem B1134119 : Blo 794341 1134119 := bstep (se 1 (by rfl) ⟨850589, by rfl⟩ : syracuseStep 1134119 = 1701179) B1701179
theorem B3821195 : Blo 794341 3821195 := bstep (se 1 (by rfl) ⟨2865896, by rfl⟩ : syracuseStep 3821195 = 5731793) B5731793
theorem B1789883 : Blo 794341 1789883 := bstep (se 1 (by rfl) ⟨1342412, by rfl⟩ : syracuseStep 1789883 = 2684825) B2684825
theorem B1363931 : Blo 794341 1363931 := bstep (se 1 (by rfl) ⟨1022948, by rfl⟩ : syracuseStep 1363931 = 2045897) B2045897
theorem B3395591 : Blo 794341 3395591 := bstep (se 1 (by rfl) ⟨2546693, by rfl⟩ : syracuseStep 3395591 = 5093387) B5093387
theorem B1790009 : Blo 794341 1790009 := bstep (se 2 (by rfl) ⟨671253, by rfl⟩ : syracuseStep 1790009 = 1342507) B1342507
theorem B8605777 : Blo 794341 8605777 := bstep (se 2 (by rfl) ⟨3227166, by rfl⟩ : syracuseStep 8605777 = 6454333) B6454333
theorem B1790351 : Blo 794341 1790351 := bstep (se 1 (by rfl) ⟨1342763, by rfl⟩ : syracuseStep 1790351 = 2685527) B2685527
theorem B2019937 : Blo 794341 2019937 := bstep (se 2 (by rfl) ⟨757476, by rfl⟩ : syracuseStep 2019937 = 1514953) B1514953
theorem B11457125 : Blo 794341 11457125 := bstep (se 4 (by rfl) ⟨1074105, by rfl⟩ : syracuseStep 11457125 = 2148211) B2148211
theorem B5100205 : Blo 794341 5100205 := bstep (se 3 (by rfl) ⟨956288, by rfl⟩ : syracuseStep 5100205 = 1912577) B1912577
theorem B1790675 : Blo 794341 1790675 := bstep (se 1 (by rfl) ⟨1343006, by rfl⟩ : syracuseStep 1790675 = 2686013) B2686013
theorem B3232619 : Blo 794341 3232619 := bstep (se 1 (by rfl) ⟨2424464, by rfl⟩ : syracuseStep 3232619 = 4848929) B4848929
theorem B5100563 : Blo 794341 5100563 := bstep (se 1 (by rfl) ⟨3825422, by rfl⟩ : syracuseStep 5100563 = 7650845) B7650845
theorem B2544797 : Blo 794341 2544797 := bstep (se 3 (by rfl) ⟨477149, by rfl⟩ : syracuseStep 2544797 = 954299) B954299
theorem B10179755 : Blo 794341 10179755 := bstep (se 1 (by rfl) ⟨7634816, by rfl⟩ : syracuseStep 10179755 = 15269633) B15269633
theorem B9065843 : Blo 794341 9065843 := bstep (se 1 (by rfl) ⟨6799382, by rfl⟩ : syracuseStep 9065843 = 13598765) B13598765
theorem B906715 : Blo 794341 906715 := bstep (se 1 (by rfl) ⟨680036, by rfl⟩ : syracuseStep 906715 = 1360073) B1360073
theorem B3233267 : Blo 794341 3233267 := bstep (se 1 (by rfl) ⟨2424950, by rfl⟩ : syracuseStep 3233267 = 4849901) B4849901
theorem B4544039 : Blo 794341 4544039 := bstep (se 1 (by rfl) ⟨3408029, by rfl⟩ : syracuseStep 4544039 = 6816059) B6816059
theorem B1791611 : Blo 794341 1791611 := bstep (se 1 (by rfl) ⟨1343708, by rfl⟩ : syracuseStep 1791611 = 2687417) B2687417
theorem B4085437 : Blo 794341 4085437 := bstep (se 3 (by rfl) ⟨766019, by rfl⟩ : syracuseStep 4085437 = 1532039) B1532039
theorem B4544221 : Blo 794341 4544221 := bstep (se 3 (by rfl) ⟨852041, by rfl⟩ : syracuseStep 4544221 = 1704083) B1704083
theorem B4314845 : Blo 794341 4314845 := bstep (se 3 (by rfl) ⟨809033, by rfl⟩ : syracuseStep 4314845 = 1618067) B1618067
theorem B1791737 : Blo 794341 1791737 := bstep (se 2 (by rfl) ⟨671901, by rfl⟩ : syracuseStep 1791737 = 1343803) B1343803
theorem B1792007 : Blo 794341 1792007 := bstep (se 1 (by rfl) ⟨1344005, by rfl⟩ : syracuseStep 1792007 = 2688011) B2688011
theorem B1792079 : Blo 794341 1792079 := bstep (se 1 (by rfl) ⟨1344059, by rfl⟩ : syracuseStep 1792079 = 2688119) B2688119
theorem B1005691 : Blo 794341 1005691 := bstep (se 1 (by rfl) ⟨754268, by rfl⟩ : syracuseStep 1005691 = 1508537) B1508537
theorem B907463 : Blo 794341 907463 := bstep (se 1 (by rfl) ⟨680597, by rfl⟩ : syracuseStep 907463 = 1361195) B1361195
theorem B3234059 : Blo 794341 3234059 := bstep (se 1 (by rfl) ⟨2425544, by rfl⟩ : syracuseStep 3234059 = 4851089) B4851089
theorem B6052157 : Blo 794341 6052157 := bstep (se 3 (by rfl) ⟨1134779, by rfl⟩ : syracuseStep 6052157 = 2269559) B2269559
theorem B1792475 : Blo 794341 1792475 := bstep (se 1 (by rfl) ⟨1344356, by rfl⟩ : syracuseStep 1792475 = 2688713) B2688713
theorem B2546387 : Blo 794341 2546387 := bstep (se 1 (by rfl) ⟨1909790, by rfl⟩ : syracuseStep 2546387 = 3819581) B3819581
theorem B1792943 : Blo 794341 1792943 := bstep (se 1 (by rfl) ⟨1344707, by rfl⟩ : syracuseStep 1792943 = 2689415) B2689415
theorem B3398735 : Blo 794341 3398735 := bstep (se 1 (by rfl) ⟨2549051, by rfl⟩ : syracuseStep 3398735 = 5098103) B5098103
theorem B1793195 : Blo 794341 1793195 := bstep (se 1 (by rfl) ⟨1344896, by rfl⟩ : syracuseStep 1793195 = 2689793) B2689793
theorem B3071171 : Blo 794341 3071171 := bstep (se 1 (by rfl) ⟨2303378, by rfl⟩ : syracuseStep 3071171 = 4606757) B4606757
theorem B2874635 : Blo 794341 2874635 := bstep (se 1 (by rfl) ⟨2155976, by rfl⟩ : syracuseStep 2874635 = 4311953) B4311953
theorem B7658995 : Blo 794341 7658995 := bstep (se 1 (by rfl) ⟨5744246, by rfl⟩ : syracuseStep 7658995 = 11488493) B11488493
theorem B2547233 : Blo 794341 2547233 := bstep (se 2 (by rfl) ⟨955212, by rfl⟩ : syracuseStep 2547233 = 1910425) B1910425
theorem B1793735 : Blo 794341 1793735 := bstep (se 1 (by rfl) ⟨1345301, by rfl⟩ : syracuseStep 1793735 = 2690603) B2690603
theorem B4022135 : Blo 794341 4022135 := bstep (se 1 (by rfl) ⟨3016601, by rfl⟩ : syracuseStep 4022135 = 6033203) B6033203
theorem B1007579 : Blo 794341 1007579 := bstep (se 1 (by rfl) ⟨755684, by rfl⟩ : syracuseStep 1007579 = 1511369) B1511369
theorem B8609969 : Blo 794341 8609969 := bstep (se 2 (by rfl) ⟨3228738, by rfl⟩ : syracuseStep 8609969 = 6457477) B6457477
theorem B1433951 : Blo 794341 1433951 := bstep (se 1 (by rfl) ⟨1075463, by rfl⟩ : syracuseStep 1433951 = 2150927) B2150927
theorem B1008055 : Blo 794341 1008055 := bstep (se 1 (by rfl) ⟨756041, by rfl⟩ : syracuseStep 1008055 = 1512083) B1512083
theorem B1794599 : Blo 794341 1794599 := bstep (se 1 (by rfl) ⟨1345949, by rfl⟩ : syracuseStep 1794599 = 2691899) B2691899
theorem B3826385 : Blo 794341 3826385 := bstep (se 2 (by rfl) ⟨1434894, by rfl⟩ : syracuseStep 3826385 = 2869789) B2869789
theorem B1434361 : Blo 794341 1434361 := bstep (se 2 (by rfl) ⟨537885, by rfl⟩ : syracuseStep 1434361 = 1075771) B1075771
theorem B1794923 : Blo 794341 1794923 := bstep (se 1 (by rfl) ⟨1346192, by rfl⟩ : syracuseStep 1794923 = 2692385) B2692385
theorem B1794977 : Blo 794341 1794977 := bstep (se 2 (by rfl) ⟨673116, by rfl⟩ : syracuseStep 1794977 = 1346233) B1346233
theorem B1795319 : Blo 794341 1795319 := bstep (se 1 (by rfl) ⟨1346489, by rfl⟩ : syracuseStep 1795319 = 2692979) B2692979
theorem B17655331 : Blo 794341 17655331 := bstep (se 1 (by rfl) ⟨13241498, by rfl⟩ : syracuseStep 17655331 = 26482997) B26482997
theorem B1009351 : Blo 794341 1009351 := bstep (se 1 (by rfl) ⟨757013, by rfl⟩ : syracuseStep 1009351 = 1514027) B1514027
theorem B5727959 : Blo 794341 5727959 := bstep (se 1 (by rfl) ⟨4295969, by rfl⟩ : syracuseStep 5727959 = 8591939) B8591939
theorem B1795913 : Blo 794341 1795913 := bstep (se 2 (by rfl) ⟨673467, by rfl⟩ : syracuseStep 1795913 = 1346935) B1346935
theorem B1435745 : Blo 794341 1435745 := bstep (se 2 (by rfl) ⟨538404, by rfl⟩ : syracuseStep 1435745 = 1076809) B1076809
theorem B2681099 : Blo 794341 2681099 := bstep (se 1 (by rfl) ⟨2010824, by rfl⟩ : syracuseStep 2681099 = 4021649) B4021649
theorem B2419049 : Blo 794341 2419049 := bstep (se 2 (by rfl) ⟨907143, by rfl⟩ : syracuseStep 2419049 = 1814287) B1814287
theorem B2910701 : Blo 794341 2910701 := bstep (se 3 (by rfl) ⟨545756, by rfl⟩ : syracuseStep 2910701 = 1091513) B1091513
theorem B2681369 : Blo 794341 2681369 := bstep (se 2 (by rfl) ⟨1005513, by rfl⟩ : syracuseStep 2681369 = 2011027) B2011027
theorem B11627185 : Blo 794341 11627185 := bstep (se 2 (by rfl) ⟨4360194, by rfl⟩ : syracuseStep 11627185 = 8720389) B8720389
theorem B3402425 : Blo 794341 3402425 := bstep (se 2 (by rfl) ⟨1275909, by rfl⟩ : syracuseStep 3402425 = 2551819) B2551819
theorem B2550487 : Blo 794341 2550487 := bstep (se 1 (by rfl) ⟨1912865, by rfl⟩ : syracuseStep 2550487 = 3825731) B3825731
theorem B2682503 : Blo 794341 2682503 := bstep (se 1 (by rfl) ⟨2011877, by rfl⟩ : syracuseStep 2682503 = 4023755) B4023755
theorem B2682557 : Blo 794341 2682557 := bstep (se 3 (by rfl) ⟨502979, by rfl⟩ : syracuseStep 2682557 = 1005959) B1005959
theorem B10907459 : Blo 794341 10907459 := bstep (se 1 (by rfl) ⟨8180594, by rfl⟩ : syracuseStep 10907459 = 16361189) B16361189
theorem B2682719 : Blo 794341 2682719 := bstep (se 1 (by rfl) ⟨2012039, by rfl⟩ : syracuseStep 2682719 = 4024079) B4024079
theorem B2584507 : Blo 794341 2584507 := bstep (se 1 (by rfl) ⟨1938380, by rfl⟩ : syracuseStep 2584507 = 3876761) B3876761
theorem B5828561 : Blo 794341 5828561 := bstep (se 2 (by rfl) ⟨2185710, by rfl⟩ : syracuseStep 5828561 = 4371421) B4371421
theorem B2682881 : Blo 794341 2682881 := bstep (se 2 (by rfl) ⟨1006080, by rfl⟩ : syracuseStep 2682881 = 2012161) B2012161
theorem B11464733 : Blo 794341 11464733 := bstep (se 3 (by rfl) ⟨2149637, by rfl⟩ : syracuseStep 11464733 = 4299275) B4299275
theorem B1536079 : Blo 794341 1536079 := bstep (se 1 (by rfl) ⟨1152059, by rfl⟩ : syracuseStep 1536079 = 2304119) B2304119
theorem B8155673 : Blo 794341 8155673 := bstep (se 2 (by rfl) ⟨3058377, by rfl⟩ : syracuseStep 8155673 = 6116755) B6116755
theorem B6451771 : Blo 794341 6451771 := bstep (se 1 (by rfl) ⟨4838828, by rfl⟩ : syracuseStep 6451771 = 9677657) B9677657
theorem B6812369 : Blo 794341 6812369 := bstep (se 2 (by rfl) ⟨2554638, by rfl⟩ : syracuseStep 6812369 = 5109277) B5109277
theorem B2683691 : Blo 794341 2683691 := bstep (se 1 (by rfl) ⟨2012768, by rfl⟩ : syracuseStep 2683691 = 4025537) B4025537
theorem B4027319 : Blo 794341 4027319 := bstep (se 1 (by rfl) ⟨3020489, by rfl⟩ : syracuseStep 4027319 = 6040979) B6040979
theorem B1340455 : Blo 794341 1340455 := bstep (se 1 (by rfl) ⟨1005341, by rfl⟩ : syracuseStep 1340455 = 2010683) B2010683
theorem B2683961 : Blo 794341 2683961 := bstep (se 2 (by rfl) ⟨1006485, by rfl⟩ : syracuseStep 2683961 = 2012971) B2012971
theorem B4846787 : Blo 794341 4846787 := bstep (se 1 (by rfl) ⟨3635090, by rfl⟩ : syracuseStep 4846787 = 7270181) B7270181
theorem B1340779 : Blo 794341 1340779 := bstep (se 1 (by rfl) ⟨1005584, by rfl⟩ : syracuseStep 1340779 = 2011169) B2011169
theorem B2684285 : Blo 794341 2684285 := bstep (se 3 (by rfl) ⟨503303, by rfl⟩ : syracuseStep 2684285 = 1006607) B1006607
theorem B2553383 : Blo 794341 2553383 := bstep (se 1 (by rfl) ⟨1915037, by rfl⟩ : syracuseStep 2553383 = 3830075) B3830075
theorem B3831419 : Blo 794341 3831419 := bstep (se 1 (by rfl) ⟨2873564, by rfl⟩ : syracuseStep 3831419 = 5747129) B5747129
theorem B2684555 : Blo 794341 2684555 := bstep (se 1 (by rfl) ⟨2013416, by rfl⟩ : syracuseStep 2684555 = 4026833) B4026833
theorem B7665299 : Blo 794341 7665299 := bstep (se 1 (by rfl) ⟨5748974, by rfl⟩ : syracuseStep 7665299 = 11497949) B11497949
theorem B15496903 : Blo 794341 15496903 := bstep (se 1 (by rfl) ⟨11622677, by rfl⟩ : syracuseStep 15496903 = 23245355) B23245355
theorem B61962083 : Blo 794341 61962083 := bstep (se 1 (by rfl) ⟨46471562, by rfl⟩ : syracuseStep 61962083 = 92943125) B92943125
theorem B1275961 : Blo 794341 1275961 := bstep (se 2 (by rfl) ⟨478485, by rfl⟩ : syracuseStep 1275961 = 956971) B956971
theorem B12941369 : Blo 794341 12941369 := bstep (se 2 (by rfl) ⟨4853013, by rfl⟩ : syracuseStep 12941369 = 9706027) B9706027
theorem B5437529 : Blo 794341 5437529 := bstep (se 2 (by rfl) ⟨2039073, by rfl⟩ : syracuseStep 5437529 = 4078147) B4078147
theorem B4028777 : Blo 794341 4028777 := bstep (se 2 (by rfl) ⟨1510791, by rfl⟩ : syracuseStep 4028777 = 3021583) B3021583
theorem B1341839 : Blo 794341 1341839 := bstep (se 1 (by rfl) ⟨1006379, by rfl⟩ : syracuseStep 1341839 = 2012759) B2012759
theorem B2685473 : Blo 794341 2685473 := bstep (se 2 (by rfl) ⟨1007052, by rfl⟩ : syracuseStep 2685473 = 2014105) B2014105
theorem B1342075 : Blo 794341 1342075 := bstep (se 1 (by rfl) ⟨1006556, by rfl⟩ : syracuseStep 1342075 = 2013113) B2013113
theorem B2685689 : Blo 794341 2685689 := bstep (se 2 (by rfl) ⟨1007133, by rfl⟩ : syracuseStep 2685689 = 2014267) B2014267
theorem B2489183 : Blo 794341 2489183 := bstep (se 1 (by rfl) ⟨1866887, by rfl⟩ : syracuseStep 2489183 = 3733775) B3733775
theorem B1276859 : Blo 794341 1276859 := bstep (se 1 (by rfl) ⟨957644, by rfl⟩ : syracuseStep 1276859 = 1915289) B1915289
theorem B2685959 : Blo 794341 2685959 := bstep (se 1 (by rfl) ⟨2014469, by rfl⟩ : syracuseStep 2685959 = 4028939) B4028939
theorem B2554895 : Blo 794341 2554895 := bstep (se 1 (by rfl) ⟨1916171, by rfl⟩ : syracuseStep 2554895 = 3832343) B3832343
theorem B2686067 : Blo 794341 2686067 := bstep (se 1 (by rfl) ⟨2014550, by rfl⟩ : syracuseStep 2686067 = 4029101) B4029101
theorem B2686337 : Blo 794341 2686337 := bstep (se 2 (by rfl) ⟨1007376, by rfl⟩ : syracuseStep 2686337 = 2014753) B2014753
theorem B1342939 : Blo 794341 1342939 := bstep (se 1 (by rfl) ⟨1007204, by rfl⟩ : syracuseStep 1342939 = 2014409) B2014409
theorem B3407483 : Blo 794341 3407483 := bstep (se 1 (by rfl) ⟨2555612, by rfl⟩ : syracuseStep 3407483 = 5111225) B5111225
theorem B5111687 : Blo 794341 5111687 := bstep (se 1 (by rfl) ⟨3833765, by rfl⟩ : syracuseStep 5111687 = 7667531) B7667531
theorem B1212335 : Blo 794341 1212335 := bstep (se 1 (by rfl) ⟨909251, by rfl⟩ : syracuseStep 1212335 = 1818503) B1818503
theorem B2686985 : Blo 794341 2686985 := bstep (se 2 (by rfl) ⟨1007619, by rfl⟩ : syracuseStep 2686985 = 2015239) B2015239
theorem B1343911 : Blo 794341 1343911 := bstep (se 1 (by rfl) ⟨1007933, by rfl⟩ : syracuseStep 1343911 = 2015867) B2015867
theorem B1344073 : Blo 794341 1344073 := bstep (se 2 (by rfl) ⟨504027, by rfl⟩ : syracuseStep 1344073 = 1008055) B1008055
theorem B1344107 : Blo 794341 1344107 := bstep (se 1 (by rfl) ⟨1008080, by rfl⟩ : syracuseStep 1344107 = 2016161) B2016161
theorem B3408749 : Blo 794341 3408749 := bstep (se 3 (by rfl) ⟨639140, by rfl⟩ : syracuseStep 3408749 = 1278281) B1278281
theorem B6816743 : Blo 794341 6816743 := bstep (se 1 (by rfl) ⟨5112557, by rfl⟩ : syracuseStep 6816743 = 10225115) B10225115
theorem B2426375 : Blo 794341 2426375 := bstep (se 1 (by rfl) ⟨1819781, by rfl⟩ : syracuseStep 2426375 = 3639563) B3639563
theorem B3409465 : Blo 794341 3409465 := bstep (se 2 (by rfl) ⟨1278549, by rfl⟩ : syracuseStep 3409465 = 2557099) B2557099
theorem B1509167 : Blo 794341 1509167 := bstep (se 1 (by rfl) ⟨1131875, by rfl⟩ : syracuseStep 1509167 = 2263751) B2263751
theorem B1345801 : Blo 794341 1345801 := bstep (se 2 (by rfl) ⟨504675, by rfl⟩ : syracuseStep 1345801 = 1009351) B1009351
theorem B4917671 : Blo 794341 4917671 := bstep (se 1 (by rfl) ⟨3688253, by rfl⟩ : syracuseStep 4917671 = 7376507) B7376507
theorem B1509995 : Blo 794341 1509995 := bstep (se 1 (by rfl) ⟨1132496, by rfl⟩ : syracuseStep 1509995 = 2264993) B2264993
theorem B2263727 : Blo 794341 2263727 := bstep (se 1 (by rfl) ⟨1697795, by rfl⟩ : syracuseStep 2263727 = 3395591) B3395591
theorem B7638083 : Blo 794341 7638083 := bstep (se 1 (by rfl) ⟨5728562, by rfl⟩ : syracuseStep 7638083 = 11457125) B11457125
theorem B6786125 : Blo 794341 6786125 := bstep (se 3 (by rfl) ⟨1272398, by rfl⟩ : syracuseStep 6786125 = 2544797) B2544797
theorem B4197457 : Blo 794341 4197457 := bstep (se 2 (by rfl) ⟨1574046, by rfl⟩ : syracuseStep 4197457 = 3148093) B3148093
theorem B2690171 : Blo 794341 2690171 := bstep (se 1 (by rfl) ⟨2017628, by rfl⟩ : syracuseStep 2690171 = 4035257) B4035257
theorem B2690441 : Blo 794341 2690441 := bstep (se 2 (by rfl) ⟨1008915, by rfl⟩ : syracuseStep 2690441 = 2017831) B2017831
theorem B6786503 : Blo 794341 6786503 := bstep (se 1 (by rfl) ⟨5089877, by rfl⟩ : syracuseStep 6786503 = 10179755) B10179755
theorem B15502913 : Blo 794341 15502913 := bstep (se 2 (by rfl) ⟨5813592, by rfl⟩ : syracuseStep 15502913 = 11627185) B11627185
theorem B2690873 : Blo 794341 2690873 := bstep (se 2 (by rfl) ⟨1009077, by rfl⟩ : syracuseStep 2690873 = 2018155) B2018155
theorem B4296509 : Blo 794341 4296509 := bstep (se 3 (by rfl) ⟨805595, by rfl⟩ : syracuseStep 4296509 = 1611191) B1611191
theorem B3018653 : Blo 794341 3018653 := bstep (se 3 (by rfl) ⟨565997, by rfl⟩ : syracuseStep 3018653 = 1131995) B1131995
theorem B7966673 : Blo 794341 7966673 := bstep (se 2 (by rfl) ⟨2987502, by rfl⟩ : syracuseStep 7966673 = 5975005) B5975005
theorem B4591721 : Blo 794341 4591721 := bstep (se 2 (by rfl) ⟨1721895, by rfl⟩ : syracuseStep 4591721 = 3443791) B3443791
theorem B4034771 : Blo 794341 4034771 := bstep (se 1 (by rfl) ⟨3026078, by rfl⟩ : syracuseStep 4034771 = 6052157) B6052157
theorem B5738825 : Blo 794341 5738825 := bstep (se 2 (by rfl) ⟨2152059, by rfl⟩ : syracuseStep 5738825 = 4304119) B4304119
theorem B3871385 : Blo 794341 3871385 := bstep (se 2 (by rfl) ⟨1451769, by rfl⟩ : syracuseStep 3871385 = 2903539) B2903539
theorem B2691737 : Blo 794341 2691737 := bstep (se 2 (by rfl) ⟨1009401, by rfl⟩ : syracuseStep 2691737 = 2018803) B2018803
theorem B22090439 : Blo 794341 22090439 := bstep (se 1 (by rfl) ⟨16567829, by rfl⟩ : syracuseStep 22090439 = 33135659) B33135659
theorem B2265823 : Blo 794341 2265823 := bstep (se 1 (by rfl) ⟨1699367, by rfl⟩ : syracuseStep 2265823 = 3398735) B3398735
theorem B4527251 : Blo 794341 4527251 := bstep (se 1 (by rfl) ⟨3395438, by rfl⟩ : syracuseStep 4527251 = 6790877) B6790877
theorem B3446009 : Blo 794341 3446009 := bstep (se 2 (by rfl) ⟨1292253, by rfl⟩ : syracuseStep 3446009 = 2584507) B2584507
theorem B1512827 : Blo 794341 1512827 := bstep (se 1 (by rfl) ⟨1134620, by rfl⟩ : syracuseStep 1512827 = 2269241) B2269241
theorem B10327421 : Blo 794341 10327421 := bstep (se 3 (by rfl) ⟨1936391, by rfl⟩ : syracuseStep 10327421 = 3872783) B3872783
theorem B11474369 : Blo 794341 11474369 := bstep (se 2 (by rfl) ⟨4302888, by rfl⟩ : syracuseStep 11474369 = 8605777) B8605777
theorem B5739979 : Blo 794341 5739979 := bstep (se 1 (by rfl) ⟨4304984, by rfl⟩ : syracuseStep 5739979 = 8609969) B8609969
theorem B3544633 : Blo 794341 3544633 := bstep (se 2 (by rfl) ⟨1329237, by rfl⟩ : syracuseStep 3544633 = 2658475) B2658475
theorem B955967 : Blo 794341 955967 := bstep (se 1 (by rfl) ⟨716975, by rfl⟩ : syracuseStep 955967 = 1433951) B1433951
theorem B1513055 : Blo 794341 1513055 := bstep (se 1 (by rfl) ⟨1134791, by rfl⟩ : syracuseStep 1513055 = 2269583) B2269583
theorem B2693249 : Blo 794341 2693249 := bstep (se 2 (by rfl) ⟨1009968, by rfl⟩ : syracuseStep 2693249 = 2019937) B2019937
theorem B7739725 : Blo 794341 7739725 := bstep (se 3 (by rfl) ⟨1451198, by rfl⟩ : syracuseStep 7739725 = 2902397) B2902397
theorem B2693627 : Blo 794341 2693627 := bstep (se 1 (by rfl) ⟨2020220, by rfl⟩ : syracuseStep 2693627 = 4040441) B4040441
theorem B1612699 : Blo 794341 1612699 := bstep (se 1 (by rfl) ⟨1209524, by rfl⟩ : syracuseStep 1612699 = 2419049) B2419049
theorem B2694059 : Blo 794341 2694059 := bstep (se 1 (by rfl) ⟨2020544, by rfl⟩ : syracuseStep 2694059 = 4041089) B4041089
theorem B2039003 : Blo 794341 2039003 := bstep (se 1 (by rfl) ⟨1529252, by rfl⟩ : syracuseStep 2039003 = 3058505) B3058505
theorem B9674149 : Blo 794341 9674149 := bstep (se 4 (by rfl) ⟨906951, by rfl⟩ : syracuseStep 9674149 = 1813903) B1813903
theorem B5447249 : Blo 794341 5447249 := bstep (se 2 (by rfl) ⟨2042718, by rfl⟩ : syracuseStep 5447249 = 4085437) B4085437
theorem B2039483 : Blo 794341 2039483 := bstep (se 1 (by rfl) ⟨1529612, by rfl⟩ : syracuseStep 2039483 = 3059225) B3059225
theorem B794415 : Blo 794341 794415 := bstep (se 1 (by rfl) ⟨595811, by rfl⟩ : syracuseStep 794415 = 1191623) B1191623
theorem B794523 : Blo 794341 794523 := bstep (se 1 (by rfl) ⟨595892, by rfl⟩ : syracuseStep 794523 = 1191785) B1191785
theorem B794575 : Blo 794341 794575 := bstep (se 1 (by rfl) ⟨595931, by rfl⟩ : syracuseStep 794575 = 1191863) B1191863
theorem B794599 : Blo 794341 794599 := bstep (se 1 (by rfl) ⟨595949, by rfl⟩ : syracuseStep 794599 = 1191899) B1191899
theorem B7643155 : Blo 794341 7643155 := bstep (se 1 (by rfl) ⟨5732366, by rfl⟩ : syracuseStep 7643155 = 11464733) B11464733
theorem B794911 : Blo 794341 794911 := bstep (se 1 (by rfl) ⟨596183, by rfl⟩ : syracuseStep 794911 = 1192367) B1192367
theorem B794971 : Blo 794341 794971 := bstep (se 1 (by rfl) ⟨596228, by rfl⟩ : syracuseStep 794971 = 1192457) B1192457
theorem B794991 : Blo 794341 794991 := bstep (se 1 (by rfl) ⟨596243, by rfl⟩ : syracuseStep 794991 = 1192487) B1192487
theorem B795047 : Blo 794341 795047 := bstep (se 1 (by rfl) ⟨596285, by rfl⟩ : syracuseStep 795047 = 1192571) B1192571
theorem B795131 : Blo 794341 795131 := bstep (se 1 (by rfl) ⟨596348, by rfl⟩ : syracuseStep 795131 = 1192697) B1192697
theorem B795199 : Blo 794341 795199 := bstep (se 1 (by rfl) ⟨596399, by rfl⟩ : syracuseStep 795199 = 1192799) B1192799
theorem B795207 : Blo 794341 795207 := bstep (se 1 (by rfl) ⟨596405, by rfl⟩ : syracuseStep 795207 = 1192811) B1192811
theorem B3023513 : Blo 794341 3023513 := bstep (se 2 (by rfl) ⟨1133817, by rfl⟩ : syracuseStep 3023513 = 2267635) B2267635
theorem B795359 : Blo 794341 795359 := bstep (se 1 (by rfl) ⟨596519, by rfl⟩ : syracuseStep 795359 = 1193039) B1193039
theorem B795439 : Blo 794341 795439 := bstep (se 1 (by rfl) ⟨596579, by rfl⟩ : syracuseStep 795439 = 1193159) B1193159
theorem B795547 : Blo 794341 795547 := bstep (se 1 (by rfl) ⟨596660, by rfl⟩ : syracuseStep 795547 = 1193321) B1193321
theorem B795599 : Blo 794341 795599 := bstep (se 1 (by rfl) ⟨596699, by rfl⟩ : syracuseStep 795599 = 1193399) B1193399
theorem B795623 : Blo 794341 795623 := bstep (se 1 (by rfl) ⟨596717, by rfl⟩ : syracuseStep 795623 = 1193435) B1193435
theorem B795935 : Blo 794341 795935 := bstep (se 1 (by rfl) ⟨596951, by rfl⟩ : syracuseStep 795935 = 1193903) B1193903
theorem B795995 : Blo 794341 795995 := bstep (se 1 (by rfl) ⟨596996, by rfl⟩ : syracuseStep 795995 = 1193993) B1193993
theorem B796015 : Blo 794341 796015 := bstep (se 1 (by rfl) ⟨597011, by rfl⟩ : syracuseStep 796015 = 1194023) B1194023
theorem B8627579 : Blo 794341 8627579 := bstep (se 1 (by rfl) ⟨6470684, by rfl⟩ : syracuseStep 8627579 = 12941369) B12941369
theorem B796071 : Blo 794341 796071 := bstep (se 1 (by rfl) ⟨597053, by rfl⟩ : syracuseStep 796071 = 1194107) B1194107
theorem B3024317 : Blo 794341 3024317 := bstep (se 3 (by rfl) ⟨567059, by rfl⟩ : syracuseStep 3024317 = 1134119) B1134119
theorem B796155 : Blo 794341 796155 := bstep (se 1 (by rfl) ⟨597116, by rfl⟩ : syracuseStep 796155 = 1194233) B1194233
theorem B796223 : Blo 794341 796223 := bstep (se 1 (by rfl) ⟨597167, by rfl⟩ : syracuseStep 796223 = 1194335) B1194335
theorem B796231 : Blo 794341 796231 := bstep (se 1 (by rfl) ⟨597173, by rfl⟩ : syracuseStep 796231 = 1194347) B1194347
theorem B894559 : Blo 794341 894559 := bstep (se 1 (by rfl) ⟨670919, by rfl⟩ : syracuseStep 894559 = 1341839) B1341839
theorem B796383 : Blo 794341 796383 := bstep (se 1 (by rfl) ⟨597287, by rfl⟩ : syracuseStep 796383 = 1194575) B1194575
theorem B796463 : Blo 794341 796463 := bstep (se 1 (by rfl) ⟨597347, by rfl⟩ : syracuseStep 796463 = 1194695) B1194695
theorem B796571 : Blo 794341 796571 := bstep (se 1 (by rfl) ⟨597428, by rfl⟩ : syracuseStep 796571 = 1194857) B1194857
theorem B796623 : Blo 794341 796623 := bstep (se 1 (by rfl) ⟨597467, by rfl⟩ : syracuseStep 796623 = 1194935) B1194935
theorem B796647 : Blo 794341 796647 := bstep (se 1 (by rfl) ⟨597485, by rfl⟩ : syracuseStep 796647 = 1194971) B1194971
theorem B13117625 : Blo 794341 13117625 := bstep (se 2 (by rfl) ⟨4919109, by rfl⟩ : syracuseStep 13117625 = 9838219) B9838219
theorem B796959 : Blo 794341 796959 := bstep (se 1 (by rfl) ⟨597719, by rfl⟩ : syracuseStep 796959 = 1195439) B1195439
theorem B797019 : Blo 794341 797019 := bstep (se 1 (by rfl) ⟨597764, by rfl⟩ : syracuseStep 797019 = 1195529) B1195529
theorem B797039 : Blo 794341 797039 := bstep (se 1 (by rfl) ⟨597779, by rfl⟩ : syracuseStep 797039 = 1195559) B1195559
theorem B797095 : Blo 794341 797095 := bstep (se 1 (by rfl) ⟨597821, by rfl⟩ : syracuseStep 797095 = 1195643) B1195643
theorem B2271655 : Blo 794341 2271655 := bstep (se 1 (by rfl) ⟨1703741, by rfl⟩ : syracuseStep 2271655 = 3407483) B3407483
theorem B1911251 : Blo 794341 1911251 := bstep (se 1 (by rfl) ⟨1433438, by rfl⟩ : syracuseStep 1911251 = 2866877) B2866877
theorem B797179 : Blo 794341 797179 := bstep (se 1 (by rfl) ⟨597884, by rfl⟩ : syracuseStep 797179 = 1195769) B1195769
theorem B3025471 : Blo 794341 3025471 := bstep (se 1 (by rfl) ⟨2269103, by rfl⟩ : syracuseStep 3025471 = 4538207) B4538207
theorem B797247 : Blo 794341 797247 := bstep (se 1 (by rfl) ⟨597935, by rfl⟩ : syracuseStep 797247 = 1195871) B1195871
theorem B797255 : Blo 794341 797255 := bstep (se 1 (by rfl) ⟨597941, by rfl⟩ : syracuseStep 797255 = 1195883) B1195883
theorem B895711 : Blo 794341 895711 := bstep (se 1 (by rfl) ⟨671783, by rfl⟩ : syracuseStep 895711 = 1343567) B1343567
theorem B797407 : Blo 794341 797407 := bstep (se 1 (by rfl) ⟨598055, by rfl⟩ : syracuseStep 797407 = 1196111) B1196111
theorem B797487 : Blo 794341 797487 := bstep (se 1 (by rfl) ⟨598115, by rfl⟩ : syracuseStep 797487 = 1196231) B1196231
theorem B797595 : Blo 794341 797595 := bstep (se 1 (by rfl) ⟨598196, by rfl⟩ : syracuseStep 797595 = 1196393) B1196393
theorem B797647 : Blo 794341 797647 := bstep (se 1 (by rfl) ⟨598235, by rfl⟩ : syracuseStep 797647 = 1196471) B1196471
theorem B797671 : Blo 794341 797671 := bstep (se 1 (by rfl) ⟨598253, by rfl⟩ : syracuseStep 797671 = 1196507) B1196507
theorem B5745745 : Blo 794341 5745745 := bstep (se 2 (by rfl) ⟨2154654, by rfl⟩ : syracuseStep 5745745 = 4309309) B4309309
theorem B7777361 : Blo 794341 7777361 := bstep (se 2 (by rfl) ⟨2916510, by rfl⟩ : syracuseStep 7777361 = 5833021) B5833021
theorem B2272475 : Blo 794341 2272475 := bstep (se 1 (by rfl) ⟨1704356, by rfl⟩ : syracuseStep 2272475 = 3408713) B3408713
theorem B896287 : Blo 794341 896287 := bstep (se 1 (by rfl) ⟨672215, by rfl⟩ : syracuseStep 896287 = 1344431) B1344431
theorem B797983 : Blo 794341 797983 := bstep (se 1 (by rfl) ⟨598487, by rfl⟩ : syracuseStep 797983 = 1196975) B1196975
theorem B798043 : Blo 794341 798043 := bstep (se 1 (by rfl) ⟨598532, by rfl⟩ : syracuseStep 798043 = 1197065) B1197065
theorem B798063 : Blo 794341 798063 := bstep (se 1 (by rfl) ⟨598547, by rfl⟩ : syracuseStep 798063 = 1197095) B1197095
theorem B798119 : Blo 794341 798119 := bstep (se 1 (by rfl) ⟨598589, by rfl⟩ : syracuseStep 798119 = 1197179) B1197179
theorem B798203 : Blo 794341 798203 := bstep (se 1 (by rfl) ⟨598652, by rfl⟩ : syracuseStep 798203 = 1197305) B1197305
theorem B896575 : Blo 794341 896575 := bstep (se 1 (by rfl) ⟨672431, by rfl⟩ : syracuseStep 896575 = 1344863) B1344863
theorem B798271 : Blo 794341 798271 := bstep (se 1 (by rfl) ⟨598703, by rfl⟩ : syracuseStep 798271 = 1197407) B1197407
theorem B798279 : Blo 794341 798279 := bstep (se 1 (by rfl) ⟨598709, by rfl⟩ : syracuseStep 798279 = 1197419) B1197419
theorem B1912481 : Blo 794341 1912481 := bstep (se 2 (by rfl) ⟨717180, by rfl⟩ : syracuseStep 1912481 = 1434361) B1434361
theorem B1191659 : Blo 794341 1191659 := bstep (se 1 (by rfl) ⟨893744, by rfl⟩ : syracuseStep 1191659 = 1787489) B1787489
theorem B1191887 : Blo 794341 1191887 := bstep (se 1 (by rfl) ⟨893915, by rfl⟩ : syracuseStep 1191887 = 1787831) B1787831
theorem B1192283 : Blo 794341 1192283 := bstep (se 1 (by rfl) ⟨894212, by rfl⟩ : syracuseStep 1192283 = 1788425) B1788425
theorem B897403 : Blo 794341 897403 := bstep (se 1 (by rfl) ⟨673052, by rfl⟩ : syracuseStep 897403 = 1346105) B1346105
theorem B2044327 : Blo 794341 2044327 := bstep (se 1 (by rfl) ⟨1533245, by rfl⟩ : syracuseStep 2044327 = 3066491) B3066491
theorem B25833937 : Blo 794341 25833937 := bstep (se 2 (by rfl) ⟨9687726, by rfl⟩ : syracuseStep 25833937 = 19375453) B19375453
theorem B1192511 : Blo 794341 1192511 := bstep (se 1 (by rfl) ⟨894383, by rfl⟩ : syracuseStep 1192511 = 1788767) B1788767
theorem B2044523 : Blo 794341 2044523 := bstep (se 1 (by rfl) ⟨1533392, by rfl⟩ : syracuseStep 2044523 = 3066785) B3066785
theorem B1913519 : Blo 794341 1913519 := bstep (se 1 (by rfl) ⟨1435139, by rfl⟩ : syracuseStep 1913519 = 2870279) B2870279
theorem B1192631 : Blo 794341 1192631 := bstep (se 1 (by rfl) ⟨894473, by rfl⟩ : syracuseStep 1192631 = 1788947) B1788947
theorem B23540441 : Blo 794341 23540441 := bstep (se 2 (by rfl) ⟨8827665, by rfl⟩ : syracuseStep 23540441 = 17655331) B17655331
theorem B17478389 : Blo 794341 17478389 := bstep (se 5 (by rfl) ⟨819299, by rfl⟩ : syracuseStep 17478389 = 1638599) B1638599
theorem B897871 : Blo 794341 897871 := bstep (se 1 (by rfl) ⟨673403, by rfl⟩ : syracuseStep 897871 = 1346807) B1346807
theorem B1192859 : Blo 794341 1192859 := bstep (se 1 (by rfl) ⟨894644, by rfl⟩ : syracuseStep 1192859 = 1789289) B1789289
theorem B2012303 : Blo 794341 2012303 := bstep (se 1 (by rfl) ⟨1509227, by rfl⟩ : syracuseStep 2012303 = 3018455) B3018455
theorem B4076689 : Blo 794341 4076689 := bstep (se 2 (by rfl) ⟨1528758, by rfl⟩ : syracuseStep 4076689 = 3057517) B3057517
theorem B1193255 : Blo 794341 1193255 := bstep (se 1 (by rfl) ⟨894941, by rfl⟩ : syracuseStep 1193255 = 1789883) B1789883
theorem B6796649 : Blo 794341 6796649 := bstep (se 2 (by rfl) ⟨2548743, by rfl⟩ : syracuseStep 6796649 = 5097487) B5097487
theorem B1193339 : Blo 794341 1193339 := bstep (se 1 (by rfl) ⟨895004, by rfl⟩ : syracuseStep 1193339 = 1790009) B1790009
theorem B1193465 : Blo 794341 1193465 := bstep (se 2 (by rfl) ⟨447549, by rfl⟩ : syracuseStep 1193465 = 895099) B895099
theorem B1193567 : Blo 794341 1193567 := bstep (se 1 (by rfl) ⟨895175, by rfl⟩ : syracuseStep 1193567 = 1790351) B1790351
theorem B1750825 : Blo 794341 1750825 := bstep (se 2 (by rfl) ⟨656559, by rfl⟩ : syracuseStep 1750825 = 1313119) B1313119
theorem B1193783 : Blo 794341 1193783 := bstep (se 1 (by rfl) ⟨895337, by rfl⟩ : syracuseStep 1193783 = 1790675) B1790675
theorem B4306871 : Blo 794341 4306871 := bstep (se 1 (by rfl) ⟨3230153, by rfl⟩ : syracuseStep 4306871 = 6460307) B6460307
theorem B1194089 : Blo 794341 1194089 := bstep (se 2 (by rfl) ⟨447783, by rfl⟩ : syracuseStep 1194089 = 895567) B895567
theorem B3029177 : Blo 794341 3029177 := bstep (se 2 (by rfl) ⟨1135941, by rfl⟩ : syracuseStep 3029177 = 2271883) B2271883
theorem B6043895 : Blo 794341 6043895 := bstep (se 1 (by rfl) ⟨4532921, by rfl⟩ : syracuseStep 6043895 = 9065843) B9065843
theorem B3029359 : Blo 794341 3029359 := bstep (se 1 (by rfl) ⟨2272019, by rfl⟩ : syracuseStep 3029359 = 4544039) B4544039
theorem B1194407 : Blo 794341 1194407 := bstep (se 1 (by rfl) ⟨895805, by rfl⟩ : syracuseStep 1194407 = 1791611) B1791611
theorem B1194491 : Blo 794341 1194491 := bstep (se 1 (by rfl) ⟨895868, by rfl⟩ : syracuseStep 1194491 = 1791737) B1791737
theorem B1194617 : Blo 794341 1194617 := bstep (se 2 (by rfl) ⟨447981, by rfl⟩ : syracuseStep 1194617 = 895963) B895963
theorem B1194671 : Blo 794341 1194671 := bstep (se 1 (by rfl) ⟨896003, by rfl⟩ : syracuseStep 1194671 = 1792007) B1792007
theorem B1194719 : Blo 794341 1194719 := bstep (se 1 (by rfl) ⟨896039, by rfl⟩ : syracuseStep 1194719 = 1792079) B1792079
theorem B2013943 : Blo 794341 2013943 := bstep (se 1 (by rfl) ⟨1510457, by rfl⟩ : syracuseStep 2013943 = 3020915) B3020915
theorem B1194983 : Blo 794341 1194983 := bstep (se 1 (by rfl) ⟨896237, by rfl⟩ : syracuseStep 1194983 = 1792475) B1792475
theorem B2014247 : Blo 794341 2014247 := bstep (se 1 (by rfl) ⟨1510685, by rfl⟩ : syracuseStep 2014247 = 3021371) B3021371
theorem B1195241 : Blo 794341 1195241 := bstep (se 2 (by rfl) ⟨448215, by rfl⟩ : syracuseStep 1195241 = 896431) B896431
theorem B1195295 : Blo 794341 1195295 := bstep (se 1 (by rfl) ⟨896471, by rfl⟩ : syracuseStep 1195295 = 1792943) B1792943
theorem B1719713 : Blo 794341 1719713 := bstep (se 2 (by rfl) ⟨644892, by rfl⟩ : syracuseStep 1719713 = 1289785) B1289785
theorem B1195463 : Blo 794341 1195463 := bstep (se 1 (by rfl) ⟨896597, by rfl⟩ : syracuseStep 1195463 = 1793195) B1793195
theorem B2047447 : Blo 794341 2047447 := bstep (se 1 (by rfl) ⟨1535585, by rfl⟩ : syracuseStep 2047447 = 3071171) B3071171
theorem B1916423 : Blo 794341 1916423 := bstep (se 1 (by rfl) ⟨1437317, by rfl⟩ : syracuseStep 1916423 = 2874635) B2874635
theorem B32652881 : Blo 794341 32652881 := bstep (se 2 (by rfl) ⟨12244830, by rfl⟩ : syracuseStep 32652881 = 24489661) B24489661
theorem B1556231 : Blo 794341 1556231 := bstep (se 1 (by rfl) ⟨1167173, by rfl⟩ : syracuseStep 1556231 = 2334347) B2334347
theorem B1195817 : Blo 794341 1195817 := bstep (se 2 (by rfl) ⟨448431, by rfl⟩ : syracuseStep 1195817 = 896863) B896863
theorem B1195823 : Blo 794341 1195823 := bstep (se 1 (by rfl) ⟨896867, by rfl⟩ : syracuseStep 1195823 = 1793735) B1793735
theorem B2048105 : Blo 794341 2048105 := bstep (se 2 (by rfl) ⟨768039, by rfl⟩ : syracuseStep 2048105 = 1536079) B1536079
theorem B1196297 : Blo 794341 1196297 := bstep (se 2 (by rfl) ⟨448611, by rfl⟩ : syracuseStep 1196297 = 897223) B897223
theorem B2015513 : Blo 794341 2015513 := bstep (se 2 (by rfl) ⟨755817, by rfl⟩ : syracuseStep 2015513 = 1511635) B1511635
theorem B1196399 : Blo 794341 1196399 := bstep (se 1 (by rfl) ⟨897299, by rfl⟩ : syracuseStep 1196399 = 1794599) B1794599
theorem B7258531 : Blo 794341 7258531 := bstep (se 1 (by rfl) ⟨5443898, by rfl⟩ : syracuseStep 7258531 = 10887797) B10887797
theorem B1196615 : Blo 794341 1196615 := bstep (se 1 (by rfl) ⟨897461, by rfl⟩ : syracuseStep 1196615 = 1794923) B1794923
theorem B1196651 : Blo 794341 1196651 := bstep (se 1 (by rfl) ⟨897488, by rfl⟩ : syracuseStep 1196651 = 1794977) B1794977
theorem B8602361 : Blo 794341 8602361 := bstep (se 2 (by rfl) ⟨3225885, by rfl⟩ : syracuseStep 8602361 = 6451771) B6451771
theorem B1196879 : Blo 794341 1196879 := bstep (se 1 (by rfl) ⟨897659, by rfl⟩ : syracuseStep 1196879 = 1795319) B1795319
theorem B6800273 : Blo 794341 6800273 := bstep (se 2 (by rfl) ⟨2550102, by rfl⟩ : syracuseStep 6800273 = 5100205) B5100205
theorem B2016353 : Blo 794341 2016353 := bstep (se 2 (by rfl) ⟨756132, by rfl⟩ : syracuseStep 2016353 = 1512265) B1512265
theorem B2147467 : Blo 794341 2147467 := bstep (se 1 (by rfl) ⟨1610600, by rfl⟩ : syracuseStep 2147467 = 3221201) B3221201
theorem B3818639 : Blo 794341 3818639 := bstep (se 1 (by rfl) ⟨2863979, by rfl⟩ : syracuseStep 3818639 = 5727959) B5727959
theorem B1197275 : Blo 794341 1197275 := bstep (se 1 (by rfl) ⟨897956, by rfl⟩ : syracuseStep 1197275 = 1795913) B1795913
theorem B1787273 : Blo 794341 1787273 := bstep (se 2 (by rfl) ⟨670227, by rfl⟩ : syracuseStep 1787273 = 1340455) B1340455
theorem B1197449 : Blo 794341 1197449 := bstep (se 2 (by rfl) ⟨449043, by rfl⟩ : syracuseStep 1197449 = 898087) B898087
theorem B1787399 : Blo 794341 1787399 := bstep (se 1 (by rfl) ⟨1340549, by rfl⟩ : syracuseStep 1787399 = 2681099) B2681099
theorem B1787579 : Blo 794341 1787579 := bstep (se 1 (by rfl) ⟨1340684, by rfl⟩ : syracuseStep 1787579 = 2681369) B2681369
theorem B1787705 : Blo 794341 1787705 := bstep (se 2 (by rfl) ⟨670389, by rfl⟩ : syracuseStep 1787705 = 1340779) B1340779
theorem B44091245 : Blo 794341 44091245 := bstep (se 3 (by rfl) ⟨8267108, by rfl⟩ : syracuseStep 44091245 = 16534217) B16534217
theorem B20662537 : Blo 794341 20662537 := bstep (se 2 (by rfl) ⟨7748451, by rfl⟩ : syracuseStep 20662537 = 15496903) B15496903
theorem B1788335 : Blo 794341 1788335 := bstep (se 1 (by rfl) ⟨1341251, by rfl⟩ : syracuseStep 1788335 = 2682503) B2682503
theorem B1788371 : Blo 794341 1788371 := bstep (se 1 (by rfl) ⟨1341278, by rfl⟩ : syracuseStep 1788371 = 2682557) B2682557
theorem B2017811 : Blo 794341 2017811 := bstep (se 1 (by rfl) ⟨1513358, by rfl⟩ : syracuseStep 2017811 = 3026717) B3026717
theorem B1788479 : Blo 794341 1788479 := bstep (se 1 (by rfl) ⟨1341359, by rfl⟩ : syracuseStep 1788479 = 2682719) B2682719
theorem B3885707 : Blo 794341 3885707 := bstep (se 1 (by rfl) ⟨2914280, by rfl⟩ : syracuseStep 3885707 = 5828561) B5828561
theorem B1788587 : Blo 794341 1788587 := bstep (se 1 (by rfl) ⟨1341440, by rfl⟩ : syracuseStep 1788587 = 2682881) B2682881
theorem B2018267 : Blo 794341 2018267 := bstep (se 1 (by rfl) ⟨1513700, by rfl⟩ : syracuseStep 2018267 = 3027401) B3027401
theorem B1362919 : Blo 794341 1362919 := bstep (se 1 (by rfl) ⟨1022189, by rfl⟩ : syracuseStep 1362919 = 2044379) B2044379
theorem B4541579 : Blo 794341 4541579 := bstep (se 1 (by rfl) ⟨3406184, by rfl⟩ : syracuseStep 4541579 = 6812369) B6812369
theorem B1789127 : Blo 794341 1789127 := bstep (se 1 (by rfl) ⟨1341845, by rfl⟩ : syracuseStep 1789127 = 2683691) B2683691
theorem B2018591 : Blo 794341 2018591 := bstep (se 1 (by rfl) ⟨1513943, by rfl⟩ : syracuseStep 2018591 = 3027887) B3027887
theorem B1789307 : Blo 794341 1789307 := bstep (se 1 (by rfl) ⟨1341980, by rfl⟩ : syracuseStep 1789307 = 2683961) B2683961
theorem B3231191 : Blo 794341 3231191 := bstep (se 1 (by rfl) ⟨2423393, by rfl⟩ : syracuseStep 3231191 = 4846787) B4846787
theorem B1789433 : Blo 794341 1789433 := bstep (se 2 (by rfl) ⟨671037, by rfl⟩ : syracuseStep 1789433 = 1342075) B1342075
theorem B1789523 : Blo 794341 1789523 := bstep (se 1 (by rfl) ⟨1342142, by rfl⟩ : syracuseStep 1789523 = 2684285) B2684285
theorem B8867501 : Blo 794341 8867501 := bstep (se 3 (by rfl) ⟨1662656, by rfl⟩ : syracuseStep 8867501 = 3325313) B3325313
theorem B1789703 : Blo 794341 1789703 := bstep (se 1 (by rfl) ⟨1342277, by rfl⟩ : syracuseStep 1789703 = 2684555) B2684555
theorem B10342187 : Blo 794341 10342187 := bstep (se 1 (by rfl) ⟨7756640, by rfl⟩ : syracuseStep 10342187 = 15513281) B15513281
theorem B2019127 : Blo 794341 2019127 := bstep (se 1 (by rfl) ⟨1514345, by rfl⟩ : syracuseStep 2019127 = 3028691) B3028691
theorem B41308055 : Blo 794341 41308055 := bstep (se 1 (by rfl) ⟨30981041, by rfl⟩ : syracuseStep 41308055 = 61962083) B61962083
theorem B3625019 : Blo 794341 3625019 := bstep (se 1 (by rfl) ⟨2718764, by rfl⟩ : syracuseStep 3625019 = 5437529) B5437529
theorem B2019593 : Blo 794341 2019593 := bstep (se 2 (by rfl) ⟨757347, by rfl⟩ : syracuseStep 2019593 = 1514695) B1514695
theorem B1790315 : Blo 794341 1790315 := bstep (se 1 (by rfl) ⟨1342736, by rfl⟩ : syracuseStep 1790315 = 2685473) B2685473
theorem B1790459 : Blo 794341 1790459 := bstep (se 1 (by rfl) ⟨1342844, by rfl⟩ : syracuseStep 1790459 = 2685689) B2685689
theorem B4837907 : Blo 794341 4837907 := bstep (se 1 (by rfl) ⟨3628430, by rfl⟩ : syracuseStep 4837907 = 7256861) B7256861
theorem B1659455 : Blo 794341 1659455 := bstep (se 1 (by rfl) ⟨1244591, by rfl⟩ : syracuseStep 1659455 = 2489183) B2489183
theorem B1790585 : Blo 794341 1790585 := bstep (se 2 (by rfl) ⟨671469, by rfl⟩ : syracuseStep 1790585 = 1342939) B1342939
theorem B10211993 : Blo 794341 10211993 := bstep (se 2 (by rfl) ⟨3829497, by rfl⟩ : syracuseStep 10211993 = 7658995) B7658995
theorem B1790639 : Blo 794341 1790639 := bstep (se 1 (by rfl) ⟨1342979, by rfl⟩ : syracuseStep 1790639 = 2685959) B2685959
theorem B1790711 : Blo 794341 1790711 := bstep (se 1 (by rfl) ⟨1343033, by rfl⟩ : syracuseStep 1790711 = 2686067) B2686067
theorem B3822329 : Blo 794341 3822329 := bstep (se 2 (by rfl) ⟨1433373, by rfl⟩ : syracuseStep 3822329 = 2866747) B2866747
theorem B1790891 : Blo 794341 1790891 := bstep (se 1 (by rfl) ⟨1343168, by rfl⟩ : syracuseStep 1790891 = 2686337) B2686337
theorem B2020585 : Blo 794341 2020585 := bstep (se 2 (by rfl) ⟨757719, by rfl⟩ : syracuseStep 2020585 = 1515439) B1515439
theorem B808223 : Blo 794341 808223 := bstep (se 1 (by rfl) ⟨606167, by rfl⟩ : syracuseStep 808223 = 1212335) B1212335
theorem B2020747 : Blo 794341 2020747 := bstep (se 1 (by rfl) ⟨1515560, by rfl⟩ : syracuseStep 2020747 = 3031121) B3031121
theorem B1791431 : Blo 794341 1791431 := bstep (se 1 (by rfl) ⟨1343573, by rfl⟩ : syracuseStep 1791431 = 2687147) B2687147
theorem B8181287 : Blo 794341 8181287 := bstep (se 1 (by rfl) ⟨6135965, by rfl⟩ : syracuseStep 8181287 = 12271931) B12271931
theorem B1791791 : Blo 794341 1791791 := bstep (se 1 (by rfl) ⟨1343843, by rfl⟩ : syracuseStep 1791791 = 2687687) B2687687
theorem B1005367 : Blo 794341 1005367 := bstep (se 1 (by rfl) ⟨754025, by rfl⟩ : syracuseStep 1005367 = 1508051) B1508051
theorem B2545463 : Blo 794341 2545463 := bstep (se 1 (by rfl) ⟨1909097, by rfl⟩ : syracuseStep 2545463 = 3818195) B3818195
theorem B6051671 : Blo 794341 6051671 := bstep (se 1 (by rfl) ⟨4538753, by rfl⟩ : syracuseStep 6051671 = 9077507) B9077507
theorem B1005787 : Blo 794341 1005787 := bstep (se 1 (by rfl) ⟨754340, by rfl⟩ : syracuseStep 1005787 = 1508681) B1508681
theorem B1792367 : Blo 794341 1792367 := bstep (se 1 (by rfl) ⟨1344275, by rfl⟩ : syracuseStep 1792367 = 2688551) B2688551
theorem B2873711 : Blo 794341 2873711 := bstep (se 1 (by rfl) ⟨2155283, by rfl⟩ : syracuseStep 2873711 = 4310567) B4310567
theorem B1792439 : Blo 794341 1792439 := bstep (se 1 (by rfl) ⟨1344329, by rfl⟩ : syracuseStep 1792439 = 2688659) B2688659
theorem B1432127 : Blo 794341 1432127 := bstep (se 1 (by rfl) ⟨1074095, by rfl⟩ : syracuseStep 1432127 = 2148191) B2148191
theorem B1792583 : Blo 794341 1792583 := bstep (se 1 (by rfl) ⟨1344437, by rfl⟩ : syracuseStep 1792583 = 2688875) B2688875
theorem B1792619 : Blo 794341 1792619 := bstep (se 1 (by rfl) ⟨1344464, by rfl⟩ : syracuseStep 1792619 = 2688929) B2688929
theorem B1793015 : Blo 794341 1793015 := bstep (se 1 (by rfl) ⟨1344761, by rfl⟩ : syracuseStep 1793015 = 2689523) B2689523
theorem B4086865 : Blo 794341 4086865 := bstep (se 2 (by rfl) ⟨1532574, by rfl⟩ : syracuseStep 4086865 = 3065149) B3065149
theorem B1793375 : Blo 794341 1793375 := bstep (se 1 (by rfl) ⟨1345031, by rfl⟩ : syracuseStep 1793375 = 2690063) B2690063
theorem B13983191 : Blo 794341 13983191 := bstep (se 1 (by rfl) ⟨10487393, by rfl⟩ : syracuseStep 13983191 = 20974787) B20974787
theorem B3366359 : Blo 794341 3366359 := bstep (se 1 (by rfl) ⟨2524769, by rfl⟩ : syracuseStep 3366359 = 5049539) B5049539
theorem B1793771 : Blo 794341 1793771 := bstep (se 1 (by rfl) ⟨1345328, by rfl⟩ : syracuseStep 1793771 = 2690657) B2690657
theorem B2547463 : Blo 794341 2547463 := bstep (se 1 (by rfl) ⟨1910597, by rfl⟩ : syracuseStep 2547463 = 3821195) B3821195
theorem B1007407 : Blo 794341 1007407 := bstep (se 1 (by rfl) ⟨755555, by rfl⟩ : syracuseStep 1007407 = 1511111) B1511111
theorem B1793897 : Blo 794341 1793897 := bstep (se 2 (by rfl) ⟨672711, by rfl⟩ : syracuseStep 1793897 = 1345423) B1345423
theorem B2580353 : Blo 794341 2580353 := bstep (se 2 (by rfl) ⟨967632, by rfl⟩ : syracuseStep 2580353 = 1935265) B1935265
theorem B909287 : Blo 794341 909287 := bstep (se 1 (by rfl) ⟨681965, by rfl⟩ : syracuseStep 909287 = 1363931) B1363931
theorem B8740871 : Blo 794341 8740871 := bstep (se 1 (by rfl) ⟨6555653, by rfl⟩ : syracuseStep 8740871 = 13111307) B13111307
theorem B4022297 : Blo 794341 4022297 := bstep (se 2 (by rfl) ⟨1508361, by rfl⟩ : syracuseStep 4022297 = 3016723) B3016723
theorem B25780355 : Blo 794341 25780355 := bstep (se 1 (by rfl) ⟨19335266, by rfl⟩ : syracuseStep 25780355 = 38670533) B38670533
theorem B1007903 : Blo 794341 1007903 := bstep (se 1 (by rfl) ⟨755927, by rfl⟩ : syracuseStep 1007903 = 1511855) B1511855
theorem B2155079 : Blo 794341 2155079 := bstep (se 1 (by rfl) ⟨1616309, by rfl⟩ : syracuseStep 2155079 = 3232619) B3232619
theorem B3400375 : Blo 794341 3400375 := bstep (se 1 (by rfl) ⟨2550281, by rfl⟩ : syracuseStep 3400375 = 5100563) B5100563
theorem B1794743 : Blo 794341 1794743 := bstep (se 1 (by rfl) ⟨1346057, by rfl⟩ : syracuseStep 1794743 = 2692115) B2692115
theorem B1794959 : Blo 794341 1794959 := bstep (se 1 (by rfl) ⟨1346219, by rfl⟩ : syracuseStep 1794959 = 2692439) B2692439
theorem B3400649 : Blo 794341 3400649 := bstep (se 2 (by rfl) ⟨1275243, by rfl⟩ : syracuseStep 3400649 = 2550487) B2550487
theorem B2155511 : Blo 794341 2155511 := bstep (se 1 (by rfl) ⟨1616633, by rfl⟩ : syracuseStep 2155511 = 3233267) B3233267
theorem B2876563 : Blo 794341 2876563 := bstep (se 1 (by rfl) ⟨2157422, by rfl⟩ : syracuseStep 2876563 = 4314845) B4314845
theorem B3630329 : Blo 794341 3630329 := bstep (se 2 (by rfl) ⟨1361373, by rfl⟩ : syracuseStep 3630329 = 2722747) B2722747
theorem B1107337 : Blo 794341 1107337 := bstep (se 2 (by rfl) ⟨415251, by rfl⟩ : syracuseStep 1107337 = 830503) B830503
theorem B6809021 : Blo 794341 6809021 := bstep (se 3 (by rfl) ⟨1276691, by rfl⟩ : syracuseStep 6809021 = 2553383) B2553383
theorem B2156039 : Blo 794341 2156039 := bstep (se 1 (by rfl) ⟨1617029, by rfl⟩ : syracuseStep 2156039 = 3234059) B3234059
theorem B1795679 : Blo 794341 1795679 := bstep (se 1 (by rfl) ⟨1346759, by rfl⟩ : syracuseStep 1795679 = 2693519) B2693519
theorem B6055559 : Blo 794341 6055559 := bstep (se 1 (by rfl) ⟨4541669, by rfl⟩ : syracuseStep 6055559 = 9083339) B9083339
theorem B10217117 : Blo 794341 10217117 := bstep (se 3 (by rfl) ⟨1915709, by rfl⟩ : syracuseStep 10217117 = 3831419) B3831419
theorem B1697591 : Blo 794341 1697591 := bstep (se 1 (by rfl) ⟨1273193, by rfl⟩ : syracuseStep 1697591 = 2546387) B2546387
theorem B1795895 : Blo 794341 1795895 := bstep (se 1 (by rfl) ⟨1346921, by rfl⟩ : syracuseStep 1795895 = 2693843) B2693843
theorem B1796201 : Blo 794341 1796201 := bstep (se 2 (by rfl) ⟨673575, by rfl⟩ : syracuseStep 1796201 = 1347151) B1347151
theorem B1698155 : Blo 794341 1698155 := bstep (se 1 (by rfl) ⟨1273616, by rfl⟩ : syracuseStep 1698155 = 2547233) B2547233
theorem B1010171 : Blo 794341 1010171 := bstep (se 1 (by rfl) ⟨757628, by rfl⟩ : syracuseStep 1010171 = 1515257) B1515257
theorem B2681423 : Blo 794341 2681423 := bstep (se 1 (by rfl) ⟨2011067, by rfl⟩ : syracuseStep 2681423 = 4022135) B4022135
theorem B4025213 : Blo 794341 4025213 := bstep (se 3 (by rfl) ⟨754727, by rfl⟩ : syracuseStep 4025213 = 1509455) B1509455
theorem B3828653 : Blo 794341 3828653 := bstep (se 3 (by rfl) ⟨717872, by rfl⟩ : syracuseStep 3828653 = 1435745) B1435745
theorem B2550923 : Blo 794341 2550923 := bstep (se 1 (by rfl) ⟨1913192, by rfl⟩ : syracuseStep 2550923 = 3826385) B3826385
theorem B2419901 : Blo 794341 2419901 := bstep (se 3 (by rfl) ⟨453731, by rfl⟩ : syracuseStep 2419901 = 907463) B907463
theorem B2682665 : Blo 794341 2682665 := bstep (se 2 (by rfl) ⟨1005999, by rfl⟩ : syracuseStep 2682665 = 2011999) B2011999
theorem B4026185 : Blo 794341 4026185 := bstep (se 2 (by rfl) ⟨1509819, by rfl⟩ : syracuseStep 4026185 = 3019639) B3019639
theorem B7761869 : Blo 794341 7761869 := bstep (se 3 (by rfl) ⟨1455350, by rfl⟩ : syracuseStep 7761869 = 2910701) B2910701
theorem B3502081 : Blo 794341 3502081 := bstep (se 2 (by rfl) ⟨1313280, by rfl⟩ : syracuseStep 3502081 = 2626561) B2626561
theorem B9073133 : Blo 794341 9073133 := bstep (se 3 (by rfl) ⟨1701212, by rfl⟩ : syracuseStep 9073133 = 3402425) B3402425
theorem B1208953 : Blo 794341 1208953 := bstep (se 2 (by rfl) ⟨453357, by rfl⟩ : syracuseStep 1208953 = 906715) B906715
theorem B1274591 : Blo 794341 1274591 := bstep (se 1 (by rfl) ⟨955943, by rfl⟩ : syracuseStep 1274591 = 1911887) B1911887
theorem B6058961 : Blo 794341 6058961 := bstep (se 2 (by rfl) ⟨2272110, by rfl⟩ : syracuseStep 6058961 = 4544221) B4544221
theorem B4027481 : Blo 794341 4027481 := bstep (se 2 (by rfl) ⟨1510305, by rfl⟩ : syracuseStep 4027481 = 3020611) B3020611
theorem B7271639 : Blo 794341 7271639 := bstep (se 1 (by rfl) ⟨5453729, by rfl⟩ : syracuseStep 7271639 = 10907459) B10907459
theorem B8615159 : Blo 794341 8615159 := bstep (se 1 (by rfl) ⟨6461369, by rfl⟩ : syracuseStep 8615159 = 12922739) B12922739
theorem B1701281 : Blo 794341 1701281 := bstep (se 2 (by rfl) ⟨637980, by rfl⟩ : syracuseStep 1701281 = 1275961) B1275961
theorem B1340921 : Blo 794341 1340921 := bstep (se 2 (by rfl) ⟨502845, by rfl⟩ : syracuseStep 1340921 = 1005691) B1005691
theorem B5437115 : Blo 794341 5437115 := bstep (se 1 (by rfl) ⟨4077836, by rfl⟩ : syracuseStep 5437115 = 8155673) B8155673
theorem B1341191 : Blo 794341 1341191 := bstep (se 1 (by rfl) ⟨1005893, by rfl⟩ : syracuseStep 1341191 = 2011787) B2011787
theorem B2684879 : Blo 794341 2684879 := bstep (se 1 (by rfl) ⟨2013659, by rfl⟩ : syracuseStep 2684879 = 4027319) B4027319
theorem B5110199 : Blo 794341 5110199 := bstep (se 1 (by rfl) ⟨3832649, by rfl⟩ : syracuseStep 5110199 = 7665299) B7665299
theorem B1341947 : Blo 794341 1341947 := bstep (se 1 (by rfl) ⟨1006460, by rfl⟩ : syracuseStep 1341947 = 2012921) B2012921
theorem B1276487 : Blo 794341 1276487 := bstep (se 1 (by rfl) ⟨957365, by rfl⟩ : syracuseStep 1276487 = 1914731) B1914731
theorem B33094277 : Blo 794341 33094277 := bstep (se 4 (by rfl) ⟨3102588, by rfl⟩ : syracuseStep 33094277 = 6205177) B6205177
theorem B2685851 : Blo 794341 2685851 := bstep (se 1 (by rfl) ⟨2014388, by rfl⟩ : syracuseStep 2685851 = 4028777) B4028777
theorem B1342379 : Blo 794341 1342379 := bstep (se 1 (by rfl) ⟨1006784, by rfl⟩ : syracuseStep 1342379 = 2013569) B2013569
theorem B851239 : Blo 794341 851239 := bstep (se 1 (by rfl) ⟨638429, by rfl⟩ : syracuseStep 851239 = 1276859) B1276859
theorem B1703263 : Blo 794341 1703263 := bstep (se 1 (by rfl) ⟨1277447, by rfl⟩ : syracuseStep 1703263 = 2554895) B2554895
theorem B1342919 : Blo 794341 1342919 := bstep (se 1 (by rfl) ⟨1007189, by rfl⟩ : syracuseStep 1342919 = 2014379) B2014379
theorem B4029911 : Blo 794341 4029911 := bstep (se 1 (by rfl) ⟨3022433, by rfl⟩ : syracuseStep 4029911 = 6044867) B6044867
theorem B12943111 : Blo 794341 12943111 := bstep (se 1 (by rfl) ⟨9707333, by rfl⟩ : syracuseStep 12943111 = 19414667) B19414667
theorem B9207647 : Blo 794341 9207647 := bstep (se 1 (by rfl) ⟨6905735, by rfl⟩ : syracuseStep 9207647 = 13811471) B13811471
theorem B2686877 : Blo 794341 2686877 := bstep (se 3 (by rfl) ⟨503789, by rfl⟩ : syracuseStep 2686877 = 1007579) B1007579
theorem B3407791 : Blo 794341 3407791 := bstep (se 1 (by rfl) ⟨2555843, by rfl⟩ : syracuseStep 3407791 = 5111687) B5111687
theorem B1277903 : Blo 794341 1277903 := bstep (se 1 (by rfl) ⟨958427, by rfl⟩ : syracuseStep 1277903 = 1916855) B1916855
theorem B18677765 : Blo 794341 18677765 := bstep (se 4 (by rfl) ⟨1751040, by rfl⟩ : syracuseStep 18677765 = 3502081) B3502081
theorem B10190873 : Blo 794341 10190873 := bstep (se 2 (by rfl) ⟨3821577, by rfl⟩ : syracuseStep 10190873 = 7643155) B7643155
theorem B1343675 : Blo 794341 1343675 := bstep (se 1 (by rfl) ⟨1007756, by rfl⟩ : syracuseStep 1343675 = 2015513) B2015513
theorem B5734907 : Blo 794341 5734907 := bstep (se 1 (by rfl) ⟨4301180, by rfl⟩ : syracuseStep 5734907 = 8602361) B8602361
theorem B1344235 : Blo 794341 1344235 := bstep (se 1 (by rfl) ⟨1008176, by rfl⟩ : syracuseStep 1344235 = 2016353) B2016353
theorem B2687741 : Blo 794341 2687741 := bstep (se 3 (by rfl) ⟨503951, by rfl⟩ : syracuseStep 2687741 = 1007903) B1007903
theorem B29394163 : Blo 794341 29394163 := bstep (se 1 (by rfl) ⟨22045622, by rfl⟩ : syracuseStep 29394163 = 44091245) B44091245
theorem B3278447 : Blo 794341 3278447 := bstep (se 1 (by rfl) ⟨2458835, by rfl⟩ : syracuseStep 3278447 = 4917671) B4917671
theorem B1345207 : Blo 794341 1345207 := bstep (se 1 (by rfl) ⟨1008905, by rfl⟩ : syracuseStep 1345207 = 2017811) B2017811
theorem B2590471 : Blo 794341 2590471 := bstep (se 1 (by rfl) ⟨1942853, by rfl⟩ : syracuseStep 2590471 = 3885707) B3885707
theorem B1476449 : Blo 794341 1476449 := bstep (se 2 (by rfl) ⟨553668, by rfl⟩ : syracuseStep 1476449 = 1107337) B1107337
theorem B1345511 : Blo 794341 1345511 := bstep (se 1 (by rfl) ⟨1009133, by rfl⟩ : syracuseStep 1345511 = 2018267) B2018267
theorem B10192877 : Blo 794341 10192877 := bstep (se 3 (by rfl) ⟨1911164, by rfl⟩ : syracuseStep 10192877 = 3822329) B3822329
theorem B4524083 : Blo 794341 4524083 := bstep (se 1 (by rfl) ⟨3393062, by rfl⟩ : syracuseStep 4524083 = 6786125) B6786125
theorem B1345727 : Blo 794341 1345727 := bstep (se 1 (by rfl) ⟨1009295, by rfl⟩ : syracuseStep 1345727 = 2018591) B2018591
theorem B4524335 : Blo 794341 4524335 := bstep (se 1 (by rfl) ⟨3393251, by rfl⟩ : syracuseStep 4524335 = 6786503) B6786503
theorem B5311115 : Blo 794341 5311115 := bstep (se 1 (by rfl) ⟨3983336, by rfl⟩ : syracuseStep 5311115 = 7966673) B7966673
theorem B2689847 : Blo 794341 2689847 := bstep (se 1 (by rfl) ⟨2017385, by rfl⟩ : syracuseStep 2689847 = 4034771) B4034771
theorem B1346395 : Blo 794341 1346395 := bstep (se 1 (by rfl) ⟨1009796, by rfl⟩ : syracuseStep 1346395 = 2019593) B2019593
theorem B4033961 : Blo 794341 4033961 := bstep (se 2 (by rfl) ⟨1512735, by rfl⟩ : syracuseStep 4033961 = 3025471) B3025471
theorem B3018167 : Blo 794341 3018167 := bstep (se 1 (by rfl) ⟨2263625, by rfl⟩ : syracuseStep 3018167 = 4527251) B4527251
theorem B2297339 : Blo 794341 2297339 := bstep (se 1 (by rfl) ⟨1723004, by rfl⟩ : syracuseStep 2297339 = 3446009) B3446009
theorem B6884947 : Blo 794341 6884947 := bstep (se 1 (by rfl) ⟨5163710, by rfl⟩ : syracuseStep 6884947 = 10327421) B10327421
theorem B4034447 : Blo 794341 4034447 := bstep (se 1 (by rfl) ⟨3025835, by rfl⟩ : syracuseStep 4034447 = 6051671) B6051671
theorem B954751 : Blo 794341 954751 := bstep (se 1 (by rfl) ⟨716063, by rfl⟩ : syracuseStep 954751 = 1432127) B1432127
theorem B6787901 : Blo 794341 6787901 := bstep (se 3 (by rfl) ⟨1272731, by rfl⟩ : syracuseStep 6787901 = 2545463) B2545463
theorem B2692169 : Blo 794341 2692169 := bstep (se 2 (by rfl) ⟨1009563, by rfl⟩ : syracuseStep 2692169 = 2019127) B2019127
theorem B21796613 : Blo 794341 21796613 := bstep (se 4 (by rfl) ⟨2043432, by rfl⟩ : syracuseStep 21796613 = 4086865) B4086865
theorem B2725769 : Blo 794341 2725769 := bstep (se 2 (by rfl) ⟨1022163, by rfl⟩ : syracuseStep 2725769 = 2044327) B2044327
theorem B34445249 : Blo 794341 34445249 := bstep (se 2 (by rfl) ⟨12916968, by rfl⟩ : syracuseStep 34445249 = 25833937) B25833937
theorem B2267099 : Blo 794341 2267099 := bstep (se 1 (by rfl) ⟨1700324, by rfl⟩ : syracuseStep 2267099 = 3400649) B3400649
theorem B15341669 : Blo 794341 15341669 := bstep (se 4 (by rfl) ⟨1438281, by rfl⟩ : syracuseStep 15341669 = 2876563) B2876563
theorem B1611937 : Blo 794341 1611937 := bstep (se 2 (by rfl) ⟨604476, by rfl⟩ : syracuseStep 1611937 = 1208953) B1208953
theorem B3021097 : Blo 794341 3021097 := bstep (se 2 (by rfl) ⟨1132911, by rfl⟩ : syracuseStep 3021097 = 2265823) B2265823
theorem B4037039 : Blo 794341 4037039 := bstep (se 1 (by rfl) ⟨3027779, by rfl⟩ : syracuseStep 4037039 = 6055559) B6055559
theorem B2693789 : Blo 794341 2693789 := bstep (se 3 (by rfl) ⟨505085, by rfl⟩ : syracuseStep 2693789 = 1010171) B1010171
theorem B2694113 : Blo 794341 2694113 := bstep (se 2 (by rfl) ⟨1010292, by rfl⟩ : syracuseStep 2694113 = 2020585) B2020585
theorem B6036605 : Blo 794341 6036605 := bstep (se 3 (by rfl) ⟨1131863, by rfl⟩ : syracuseStep 6036605 = 2263727) B2263727
theorem B2694329 : Blo 794341 2694329 := bstep (se 2 (by rfl) ⟨1010373, by rfl⟩ : syracuseStep 2694329 = 2020747) B2020747
theorem B1613267 : Blo 794341 1613267 := bstep (se 1 (by rfl) ⟨1209950, by rfl⟩ : syracuseStep 1613267 = 2419901) B2419901
theorem B2334433 : Blo 794341 2334433 := bstep (se 2 (by rfl) ⟨875412, by rfl⟩ : syracuseStep 2334433 = 1750825) B1750825
theorem B794439 : Blo 794341 794439 := bstep (se 1 (by rfl) ⟨595829, by rfl⟩ : syracuseStep 794439 = 1191659) B1191659
theorem B794591 : Blo 794341 794591 := bstep (se 1 (by rfl) ⟨595943, by rfl⟩ : syracuseStep 794591 = 1191887) B1191887
theorem B794855 : Blo 794341 794855 := bstep (se 1 (by rfl) ⟨596141, by rfl⟩ : syracuseStep 794855 = 1192283) B1192283
theorem B795007 : Blo 794341 795007 := bstep (se 1 (by rfl) ⟨596255, by rfl⟩ : syracuseStep 795007 = 1192511) B1192511
theorem B795087 : Blo 794341 795087 := bstep (se 1 (by rfl) ⟨596315, by rfl⟩ : syracuseStep 795087 = 1192631) B1192631
theorem B4039145 : Blo 794341 4039145 := bstep (se 2 (by rfl) ⟨1514679, by rfl⟩ : syracuseStep 4039145 = 3029359) B3029359
theorem B795239 : Blo 794341 795239 := bstep (se 1 (by rfl) ⟨596429, by rfl⟩ : syracuseStep 795239 = 1192859) B1192859
theorem B4039307 : Blo 794341 4039307 := bstep (se 1 (by rfl) ⟨3029480, by rfl⟩ : syracuseStep 4039307 = 6058961) B6058961
theorem B5743439 : Blo 794341 5743439 := bstep (se 1 (by rfl) ⟨4307579, by rfl⟩ : syracuseStep 5743439 = 8615159) B8615159
theorem B795503 : Blo 794341 795503 := bstep (se 1 (by rfl) ⟨596627, by rfl⟩ : syracuseStep 795503 = 1193255) B1193255
theorem B4531099 : Blo 794341 4531099 := bstep (se 1 (by rfl) ⟨3398324, by rfl⟩ : syracuseStep 4531099 = 6796649) B6796649
theorem B795559 : Blo 794341 795559 := bstep (se 1 (by rfl) ⟨596669, by rfl⟩ : syracuseStep 795559 = 1193339) B1193339
theorem B893947 : Blo 794341 893947 := bstep (se 1 (by rfl) ⟨670460, by rfl⟩ : syracuseStep 893947 = 1340921) B1340921
theorem B795643 : Blo 794341 795643 := bstep (se 1 (by rfl) ⟨596732, by rfl⟩ : syracuseStep 795643 = 1193465) B1193465
theorem B795711 : Blo 794341 795711 := bstep (se 1 (by rfl) ⟨596783, by rfl⟩ : syracuseStep 795711 = 1193567) B1193567
theorem B894127 : Blo 794341 894127 := bstep (se 1 (by rfl) ⟨670595, by rfl⟩ : syracuseStep 894127 = 1341191) B1341191
theorem B795855 : Blo 794341 795855 := bstep (se 1 (by rfl) ⟨596891, by rfl⟩ : syracuseStep 795855 = 1193783) B1193783
theorem B796059 : Blo 794341 796059 := bstep (se 1 (by rfl) ⟨597044, by rfl⟩ : syracuseStep 796059 = 1194089) B1194089
theorem B796271 : Blo 794341 796271 := bstep (se 1 (by rfl) ⟨597203, by rfl⟩ : syracuseStep 796271 = 1194407) B1194407
theorem B894631 : Blo 794341 894631 := bstep (se 1 (by rfl) ⟨670973, by rfl⟩ : syracuseStep 894631 = 1341947) B1341947
theorem B796327 : Blo 794341 796327 := bstep (se 1 (by rfl) ⟨597245, by rfl⟩ : syracuseStep 796327 = 1194491) B1194491
theorem B796411 : Blo 794341 796411 := bstep (se 1 (by rfl) ⟨597308, by rfl⟩ : syracuseStep 796411 = 1194617) B1194617
theorem B22062851 : Blo 794341 22062851 := bstep (se 1 (by rfl) ⟨16547138, by rfl⟩ : syracuseStep 22062851 = 33094277) B33094277
theorem B796447 : Blo 794341 796447 := bstep (se 1 (by rfl) ⟨597335, by rfl⟩ : syracuseStep 796447 = 1194671) B1194671
theorem B2271017 : Blo 794341 2271017 := bstep (se 2 (by rfl) ⟨851631, by rfl⟩ : syracuseStep 2271017 = 1703263) B1703263
theorem B796479 : Blo 794341 796479 := bstep (se 1 (by rfl) ⟨597359, by rfl⟩ : syracuseStep 796479 = 1194719) B1194719
theorem B894919 : Blo 794341 894919 := bstep (se 1 (by rfl) ⟨671189, by rfl⟩ : syracuseStep 894919 = 1342379) B1342379
theorem B2729929 : Blo 794341 2729929 := bstep (se 2 (by rfl) ⟨1023723, by rfl⟩ : syracuseStep 2729929 = 2047447) B2047447
theorem B796655 : Blo 794341 796655 := bstep (se 1 (by rfl) ⟨597491, by rfl⟩ : syracuseStep 796655 = 1194983) B1194983
theorem B796827 : Blo 794341 796827 := bstep (se 1 (by rfl) ⟨597620, by rfl⟩ : syracuseStep 796827 = 1195241) B1195241
theorem B796863 : Blo 794341 796863 := bstep (se 1 (by rfl) ⟨597647, by rfl⟩ : syracuseStep 796863 = 1195295) B1195295
theorem B895279 : Blo 794341 895279 := bstep (se 1 (by rfl) ⟨671459, by rfl⟩ : syracuseStep 895279 = 1342919) B1342919
theorem B796975 : Blo 794341 796975 := bstep (se 1 (by rfl) ⟨597731, by rfl⟩ : syracuseStep 796975 = 1195463) B1195463
theorem B21768587 : Blo 794341 21768587 := bstep (se 1 (by rfl) ⟨16326440, by rfl⟩ : syracuseStep 21768587 = 32652881) B32652881
theorem B797211 : Blo 794341 797211 := bstep (se 1 (by rfl) ⟨597908, by rfl⟩ : syracuseStep 797211 = 1195817) B1195817
theorem B797215 : Blo 794341 797215 := bstep (se 1 (by rfl) ⟨597911, by rfl⟩ : syracuseStep 797215 = 1195823) B1195823
theorem B6138431 : Blo 794341 6138431 := bstep (se 1 (by rfl) ⟨4603823, by rfl⟩ : syracuseStep 6138431 = 9207647) B9207647
theorem B797531 : Blo 794341 797531 := bstep (se 1 (by rfl) ⟨598148, by rfl⟩ : syracuseStep 797531 = 1196297) B1196297
theorem B797599 : Blo 794341 797599 := bstep (se 1 (by rfl) ⟨598199, by rfl⟩ : syracuseStep 797599 = 1196399) B1196399
theorem B797743 : Blo 794341 797743 := bstep (se 1 (by rfl) ⟨598307, by rfl⟩ : syracuseStep 797743 = 1196615) B1196615
theorem B896071 : Blo 794341 896071 := bstep (se 1 (by rfl) ⟨672053, by rfl⟩ : syracuseStep 896071 = 1344107) B1344107
theorem B797767 : Blo 794341 797767 := bstep (se 1 (by rfl) ⟨598325, by rfl⟩ : syracuseStep 797767 = 1196651) B1196651
theorem B9678041 : Blo 794341 9678041 := bstep (se 2 (by rfl) ⟨3629265, by rfl⟩ : syracuseStep 9678041 = 7258531) B7258531
theorem B797919 : Blo 794341 797919 := bstep (se 1 (by rfl) ⟨598439, by rfl⟩ : syracuseStep 797919 = 1196879) B1196879
theorem B2272499 : Blo 794341 2272499 := bstep (se 1 (by rfl) ⟨1704374, by rfl⟩ : syracuseStep 2272499 = 3408749) B3408749
theorem B4533515 : Blo 794341 4533515 := bstep (se 1 (by rfl) ⟨3400136, by rfl⟩ : syracuseStep 4533515 = 6800273) B6800273
theorem B798183 : Blo 794341 798183 := bstep (se 1 (by rfl) ⟨598637, by rfl⟩ : syracuseStep 798183 = 1197275) B1197275
theorem B4533833 : Blo 794341 4533833 := bstep (se 2 (by rfl) ⟨1700187, by rfl⟩ : syracuseStep 4533833 = 3400375) B3400375
theorem B1191515 : Blo 794341 1191515 := bstep (se 1 (by rfl) ⟨893636, by rfl⟩ : syracuseStep 1191515 = 1787273) B1787273
theorem B798299 : Blo 794341 798299 := bstep (se 1 (by rfl) ⟨598724, by rfl⟩ : syracuseStep 798299 = 1197449) B1197449
theorem B1191599 : Blo 794341 1191599 := bstep (se 1 (by rfl) ⟨893699, by rfl⟩ : syracuseStep 1191599 = 1787399) B1787399
theorem B1617583 : Blo 794341 1617583 := bstep (se 1 (by rfl) ⟨1213187, by rfl⟩ : syracuseStep 1617583 = 2426375) B2426375
theorem B1191719 : Blo 794341 1191719 := bstep (se 1 (by rfl) ⟨893789, by rfl⟩ : syracuseStep 1191719 = 1787579) B1787579
theorem B1191803 : Blo 794341 1191803 := bstep (se 1 (by rfl) ⟨893852, by rfl⟩ : syracuseStep 1191803 = 1787705) B1787705
theorem B2863289 : Blo 794341 2863289 := bstep (se 2 (by rfl) ⟨1073733, by rfl⟩ : syracuseStep 2863289 = 2147467) B2147467
theorem B1192223 : Blo 794341 1192223 := bstep (se 1 (by rfl) ⟨894167, by rfl⟩ : syracuseStep 1192223 = 1788335) B1788335
theorem B1192247 : Blo 794341 1192247 := bstep (se 1 (by rfl) ⟨894185, by rfl⟩ : syracuseStep 1192247 = 1788371) B1788371
theorem B1192319 : Blo 794341 1192319 := bstep (se 1 (by rfl) ⟨894239, by rfl⟩ : syracuseStep 1192319 = 1788479) B1788479
theorem B1192391 : Blo 794341 1192391 := bstep (se 1 (by rfl) ⟨894293, by rfl⟩ : syracuseStep 1192391 = 1788587) B1788587
theorem B46609037 : Blo 794341 46609037 := bstep (se 3 (by rfl) ⟨8739194, by rfl⟩ : syracuseStep 46609037 = 17478389) B17478389
theorem B5092055 : Blo 794341 5092055 := bstep (se 1 (by rfl) ⟨3819041, by rfl⟩ : syracuseStep 5092055 = 7638083) B7638083
theorem B3027719 : Blo 794341 3027719 := bstep (se 1 (by rfl) ⟨2270789, by rfl⟩ : syracuseStep 3027719 = 4541579) B4541579
theorem B1192745 : Blo 794341 1192745 := bstep (se 2 (by rfl) ⟨447279, by rfl⟩ : syracuseStep 1192745 = 894559) B894559
theorem B1192751 : Blo 794341 1192751 := bstep (se 1 (by rfl) ⟨894563, by rfl⟩ : syracuseStep 1192751 = 1789127) B1789127
theorem B1192871 : Blo 794341 1192871 := bstep (se 1 (by rfl) ⟨894653, by rfl⟩ : syracuseStep 1192871 = 1789307) B1789307
theorem B1192955 : Blo 794341 1192955 := bstep (se 1 (by rfl) ⟨894716, by rfl⟩ : syracuseStep 1192955 = 1789433) B1789433
theorem B10335275 : Blo 794341 10335275 := bstep (se 1 (by rfl) ⟨7751456, by rfl⟩ : syracuseStep 10335275 = 15502913) B15502913
theorem B1193015 : Blo 794341 1193015 := bstep (se 1 (by rfl) ⟨894761, by rfl⟩ : syracuseStep 1193015 = 1789523) B1789523
theorem B5911667 : Blo 794341 5911667 := bstep (se 1 (by rfl) ⟨4433750, by rfl⟩ : syracuseStep 5911667 = 8867501) B8867501
theorem B1193135 : Blo 794341 1193135 := bstep (se 1 (by rfl) ⟨894851, by rfl⟩ : syracuseStep 1193135 = 1789703) B1789703
theorem B6894791 : Blo 794341 6894791 := bstep (se 1 (by rfl) ⟨5171093, by rfl⟩ : syracuseStep 6894791 = 10342187) B10342187
theorem B2864339 : Blo 794341 2864339 := bstep (se 1 (by rfl) ⟨2148254, by rfl⟩ : syracuseStep 2864339 = 4296509) B4296509
theorem B27538703 : Blo 794341 27538703 := bstep (se 1 (by rfl) ⟨20654027, by rfl⟩ : syracuseStep 27538703 = 41308055) B41308055
theorem B2012435 : Blo 794341 2012435 := bstep (se 1 (by rfl) ⟨1509326, by rfl⟩ : syracuseStep 2012435 = 3018653) B3018653
theorem B5748029 : Blo 794341 5748029 := bstep (se 3 (by rfl) ⟨1077755, by rfl⟩ : syracuseStep 5748029 = 2155511) B2155511
theorem B3061147 : Blo 794341 3061147 := bstep (se 1 (by rfl) ⟨2295860, by rfl⟩ : syracuseStep 3061147 = 4591721) B4591721
theorem B1193543 : Blo 794341 1193543 := bstep (se 1 (by rfl) ⟨895157, by rfl⟩ : syracuseStep 1193543 = 1790315) B1790315
theorem B1193639 : Blo 794341 1193639 := bstep (se 1 (by rfl) ⟨895229, by rfl⟩ : syracuseStep 1193639 = 1790459) B1790459
theorem B3225271 : Blo 794341 3225271 := bstep (se 1 (by rfl) ⟨2418953, by rfl⟩ : syracuseStep 3225271 = 4837907) B4837907
theorem B1193723 : Blo 794341 1193723 := bstep (se 1 (by rfl) ⟨895292, by rfl⟩ : syracuseStep 1193723 = 1790585) B1790585
theorem B1193759 : Blo 794341 1193759 := bstep (se 1 (by rfl) ⟨895319, by rfl⟩ : syracuseStep 1193759 = 1790639) B1790639
theorem B1193807 : Blo 794341 1193807 := bstep (se 1 (by rfl) ⟨895355, by rfl⟩ : syracuseStep 1193807 = 1790711) B1790711
theorem B3028873 : Blo 794341 3028873 := bstep (se 2 (by rfl) ⟨1135827, by rfl⟩ : syracuseStep 3028873 = 2271655) B2271655
theorem B1193927 : Blo 794341 1193927 := bstep (se 1 (by rfl) ⟨895445, by rfl⟩ : syracuseStep 1193927 = 1790891) B1790891
theorem B1194281 : Blo 794341 1194281 := bstep (se 2 (by rfl) ⟨447855, by rfl⟩ : syracuseStep 1194281 = 895711) B895711
theorem B7649579 : Blo 794341 7649579 := bstep (se 1 (by rfl) ⟨5737184, by rfl⟩ : syracuseStep 7649579 = 11474369) B11474369
theorem B1194287 : Blo 794341 1194287 := bstep (se 1 (by rfl) ⟨895715, by rfl⟩ : syracuseStep 1194287 = 1791431) B1791431
theorem B5454191 : Blo 794341 5454191 := bstep (se 1 (by rfl) ⟨4090643, by rfl⟩ : syracuseStep 5454191 = 8181287) B8181287
theorem B4536749 : Blo 794341 4536749 := bstep (se 3 (by rfl) ⟨850640, by rfl⟩ : syracuseStep 4536749 = 1701281) B1701281
theorem B1194527 : Blo 794341 1194527 := bstep (se 1 (by rfl) ⟨895895, by rfl⟩ : syracuseStep 1194527 = 1791791) B1791791
theorem B1817225 : Blo 794341 1817225 := bstep (se 2 (by rfl) ⟨681459, by rfl⟩ : syracuseStep 1817225 = 1362919) B1362919
theorem B1194911 : Blo 794341 1194911 := bstep (se 1 (by rfl) ⟨896183, by rfl⟩ : syracuseStep 1194911 = 1792367) B1792367
theorem B1915807 : Blo 794341 1915807 := bstep (se 1 (by rfl) ⟨1436855, by rfl⟩ : syracuseStep 1915807 = 2873711) B2873711
theorem B1194959 : Blo 794341 1194959 := bstep (se 1 (by rfl) ⟨896219, by rfl⟩ : syracuseStep 1194959 = 1792439) B1792439
theorem B1195049 : Blo 794341 1195049 := bstep (se 2 (by rfl) ⟨448143, by rfl⟩ : syracuseStep 1195049 = 896287) B896287
theorem B1195055 : Blo 794341 1195055 := bstep (se 1 (by rfl) ⟨896291, by rfl⟩ : syracuseStep 1195055 = 1792583) B1792583
theorem B1195079 : Blo 794341 1195079 := bstep (se 1 (by rfl) ⟨896309, by rfl⟩ : syracuseStep 1195079 = 1792619) B1792619
theorem B1195343 : Blo 794341 1195343 := bstep (se 1 (by rfl) ⟨896507, by rfl⟩ : syracuseStep 1195343 = 1793015) B1793015
theorem B1195433 : Blo 794341 1195433 := bstep (se 2 (by rfl) ⟨448287, by rfl⟩ : syracuseStep 1195433 = 896575) B896575
theorem B8601061 : Blo 794341 8601061 := bstep (se 4 (by rfl) ⟨806349, by rfl⟩ : syracuseStep 8601061 = 1612699) B1612699
theorem B1359335 : Blo 794341 1359335 := bstep (se 1 (by rfl) ⟨1019501, by rfl⟩ : syracuseStep 1359335 = 2039003) B2039003
theorem B1195583 : Blo 794341 1195583 := bstep (se 1 (by rfl) ⟨896687, by rfl⟩ : syracuseStep 1195583 = 1793375) B1793375
theorem B9322127 : Blo 794341 9322127 := bstep (se 1 (by rfl) ⟨6991595, by rfl⟩ : syracuseStep 9322127 = 13983191) B13983191
theorem B2244239 : Blo 794341 2244239 := bstep (se 1 (by rfl) ⟨1683179, by rfl⟩ : syracuseStep 2244239 = 3366359) B3366359
theorem B1195847 : Blo 794341 1195847 := bstep (se 1 (by rfl) ⟨896885, by rfl⟩ : syracuseStep 1195847 = 1793771) B1793771
theorem B1195931 : Blo 794341 1195931 := bstep (se 1 (by rfl) ⟨896948, by rfl⟩ : syracuseStep 1195931 = 1793897) B1793897
theorem B1720235 : Blo 794341 1720235 := bstep (se 1 (by rfl) ⟨1290176, by rfl⟩ : syracuseStep 1720235 = 2580353) B2580353
theorem B17186903 : Blo 794341 17186903 := bstep (se 1 (by rfl) ⟨12890177, by rfl⟩ : syracuseStep 17186903 = 25780355) B25780355
theorem B2015675 : Blo 794341 2015675 := bstep (se 1 (by rfl) ⟨1511756, by rfl⟩ : syracuseStep 2015675 = 3023513) B3023513
theorem B1196495 : Blo 794341 1196495 := bstep (se 1 (by rfl) ⟨897371, by rfl⟩ : syracuseStep 1196495 = 1794743) B1794743
theorem B1196537 : Blo 794341 1196537 := bstep (se 2 (by rfl) ⟨448701, by rfl⟩ : syracuseStep 1196537 = 897403) B897403
theorem B1196639 : Blo 794341 1196639 := bstep (se 1 (by rfl) ⟨897479, by rfl⟩ : syracuseStep 1196639 = 1794959) B1794959
theorem B5751719 : Blo 794341 5751719 := bstep (se 1 (by rfl) ⟨4313789, by rfl⟩ : syracuseStep 5751719 = 8627579) B8627579
theorem B2016211 : Blo 794341 2016211 := bstep (se 1 (by rfl) ⟨1512158, by rfl⟩ : syracuseStep 2016211 = 3024317) B3024317
theorem B4539347 : Blo 794341 4539347 := bstep (se 1 (by rfl) ⟨3404510, by rfl⟩ : syracuseStep 4539347 = 6809021) B6809021
theorem B1197119 : Blo 794341 1197119 := bstep (se 1 (by rfl) ⟨897839, by rfl⟩ : syracuseStep 1197119 = 1795679) B1795679
theorem B1197161 : Blo 794341 1197161 := bstep (se 2 (by rfl) ⟨448935, by rfl⟩ : syracuseStep 1197161 = 897871) B897871
theorem B1131727 : Blo 794341 1131727 := bstep (se 1 (by rfl) ⟨848795, by rfl⟩ : syracuseStep 1131727 = 1697591) B1697591
theorem B1197263 : Blo 794341 1197263 := bstep (se 1 (by rfl) ⟨897947, by rfl⟩ : syracuseStep 1197263 = 1795895) B1795895
theorem B1197467 : Blo 794341 1197467 := bstep (se 1 (by rfl) ⟨898100, by rfl⟩ : syracuseStep 1197467 = 1796201) B1796201
theorem B1132103 : Blo 794341 1132103 := bstep (se 1 (by rfl) ⟨849077, by rfl⟩ : syracuseStep 1132103 = 1698155) B1698155
theorem B1787615 : Blo 794341 1787615 := bstep (se 1 (by rfl) ⟨1340711, by rfl⟩ : syracuseStep 1787615 = 2681423) B2681423
theorem B7653305 : Blo 794341 7653305 := bstep (se 2 (by rfl) ⟨2869989, by rfl⟩ : syracuseStep 7653305 = 5739979) B5739979
theorem B1788443 : Blo 794341 1788443 := bstep (se 1 (by rfl) ⟨1341332, by rfl⟩ : syracuseStep 1788443 = 2682665) B2682665
theorem B6048755 : Blo 794341 6048755 := bstep (se 1 (by rfl) ⟨4536566, by rfl⟩ : syracuseStep 6048755 = 9073133) B9073133
theorem B1363015 : Blo 794341 1363015 := bstep (se 1 (by rfl) ⟨1022261, by rfl⟩ : syracuseStep 1363015 = 2044523) B2044523
theorem B3624743 : Blo 794341 3624743 := bstep (se 1 (by rfl) ⟨2718557, by rfl⟩ : syracuseStep 3624743 = 5437115) B5437115
theorem B2871247 : Blo 794341 2871247 := bstep (se 1 (by rfl) ⟨2153435, by rfl⟩ : syracuseStep 2871247 = 4306871) B4306871
theorem B1789919 : Blo 794341 1789919 := bstep (se 1 (by rfl) ⟨1342439, by rfl⟩ : syracuseStep 1789919 = 2684879) B2684879
theorem B2019451 : Blo 794341 2019451 := bstep (se 1 (by rfl) ⟨1514588, by rfl⟩ : syracuseStep 2019451 = 3029177) B3029177
theorem B1134985 : Blo 794341 1134985 := bstep (se 2 (by rfl) ⟨425619, by rfl⟩ : syracuseStep 1134985 = 851239) B851239
theorem B12898865 : Blo 794341 12898865 := bstep (se 2 (by rfl) ⟨4837074, by rfl⟩ : syracuseStep 12898865 = 9674149) B9674149
theorem B1790567 : Blo 794341 1790567 := bstep (se 1 (by rfl) ⟨1342925, by rfl⟩ : syracuseStep 1790567 = 2685851) B2685851
theorem B4149949 : Blo 794341 4149949 := bstep (se 3 (by rfl) ⟨778115, by rfl⟩ : syracuseStep 4149949 = 1556231) B1556231
theorem B3396617 : Blo 794341 3396617 := bstep (se 2 (by rfl) ⟨1273731, by rfl⟩ : syracuseStep 3396617 = 2547463) B2547463
theorem B17257481 : Blo 794341 17257481 := bstep (se 2 (by rfl) ⟨6471555, by rfl⟩ : syracuseStep 17257481 = 12943111) B12943111
theorem B4543721 : Blo 794341 4543721 := bstep (se 2 (by rfl) ⟨1703895, by rfl⟩ : syracuseStep 4543721 = 3407791) B3407791
theorem B1791251 : Blo 794341 1791251 := bstep (se 1 (by rfl) ⟨1343438, by rfl⟩ : syracuseStep 1791251 = 2686877) B2686877
theorem B1791323 : Blo 794341 1791323 := bstep (se 1 (by rfl) ⟨1343492, by rfl⟩ : syracuseStep 1791323 = 2686985) B2686985
theorem B5461613 : Blo 794341 5461613 := bstep (se 3 (by rfl) ⟨1024052, by rfl⟩ : syracuseStep 5461613 = 2048105) B2048105
theorem B1791881 : Blo 794341 1791881 := bstep (se 2 (by rfl) ⟨671955, by rfl⟩ : syracuseStep 1791881 = 1343911) B1343911
theorem B4544495 : Blo 794341 4544495 := bstep (se 1 (by rfl) ⟨3408371, by rfl⟩ : syracuseStep 4544495 = 6816743) B6816743
theorem B2545759 : Blo 794341 2545759 := bstep (se 1 (by rfl) ⟨1909319, by rfl⟩ : syracuseStep 2545759 = 3818639) B3818639
theorem B1792097 : Blo 794341 1792097 := bstep (se 2 (by rfl) ⟨672036, by rfl⟩ : syracuseStep 1792097 = 1344073) B1344073
theorem B1006111 : Blo 794341 1006111 := bstep (se 1 (by rfl) ⟨754583, by rfl⟩ : syracuseStep 1006111 = 1509167) B1509167
theorem B1006663 : Blo 794341 1006663 := bstep (se 1 (by rfl) ⟨754997, by rfl⟩ : syracuseStep 1006663 = 1509995) B1509995
theorem B58907837 : Blo 794341 58907837 := bstep (se 3 (by rfl) ⟨11045219, by rfl⟩ : syracuseStep 58907837 = 22090439) B22090439
theorem B62774509 : Blo 794341 62774509 := bstep (se 3 (by rfl) ⟨11770220, by rfl⟩ : syracuseStep 62774509 = 23540441) B23540441
theorem B4545953 : Blo 794341 4545953 := bstep (se 2 (by rfl) ⟨1704732, by rfl⟩ : syracuseStep 4545953 = 3409465) B3409465
theorem B1793447 : Blo 794341 1793447 := bstep (se 1 (by rfl) ⟨1345085, by rfl⟩ : syracuseStep 1793447 = 2690171) B2690171
theorem B1793627 : Blo 794341 1793627 := bstep (se 1 (by rfl) ⟨1345220, by rfl⟩ : syracuseStep 1793627 = 2690441) B2690441
theorem B2154127 : Blo 794341 2154127 := bstep (se 1 (by rfl) ⟨1615595, by rfl⟩ : syracuseStep 2154127 = 3231191) B3231191
theorem B1793915 : Blo 794341 1793915 := bstep (se 1 (by rfl) ⟨1345436, by rfl⟩ : syracuseStep 1793915 = 2690873) B2690873
theorem B2416679 : Blo 794341 2416679 := bstep (se 1 (by rfl) ⟨1812509, by rfl⟩ : syracuseStep 2416679 = 3625019) B3625019
theorem B3825883 : Blo 794341 3825883 := bstep (se 1 (by rfl) ⟨2869412, by rfl⟩ : syracuseStep 3825883 = 5738825) B5738825
theorem B27550049 : Blo 794341 27550049 := bstep (se 2 (by rfl) ⟨10331268, by rfl⟩ : syracuseStep 27550049 = 20662537) B20662537
theorem B1794401 : Blo 794341 1794401 := bstep (se 2 (by rfl) ⟨672900, by rfl⟩ : syracuseStep 1794401 = 1345801) B1345801
theorem B1106303 : Blo 794341 1106303 := bstep (se 1 (by rfl) ⟨829727, by rfl⟩ : syracuseStep 1106303 = 1659455) B1659455
theorem B2580923 : Blo 794341 2580923 := bstep (se 1 (by rfl) ⟨1935692, by rfl⟩ : syracuseStep 2580923 = 3871385) B3871385
theorem B6807995 : Blo 794341 6807995 := bstep (se 1 (by rfl) ⟨5105996, by rfl⟩ : syracuseStep 6807995 = 10211993) B10211993
theorem B1794491 : Blo 794341 1794491 := bstep (se 1 (by rfl) ⟨1345868, by rfl⟩ : syracuseStep 1794491 = 2691737) B2691737
theorem B2155261 : Blo 794341 2155261 := bstep (se 3 (by rfl) ⟨404111, by rfl⟩ : syracuseStep 2155261 = 808223) B808223
theorem B1008551 : Blo 794341 1008551 := bstep (se 1 (by rfl) ⟨756413, by rfl⟩ : syracuseStep 1008551 = 1512827) B1512827
theorem B1008703 : Blo 794341 1008703 := bstep (se 1 (by rfl) ⟨756527, by rfl⟩ : syracuseStep 1008703 = 1513055) B1513055
theorem B1795499 : Blo 794341 1795499 := bstep (se 1 (by rfl) ⟨1346624, by rfl⟩ : syracuseStep 1795499 = 2693249) B2693249
theorem B5596609 : Blo 794341 5596609 := bstep (se 2 (by rfl) ⟨2098728, by rfl⟩ : syracuseStep 5596609 = 4197457) B4197457
theorem B7660993 : Blo 794341 7660993 := bstep (se 2 (by rfl) ⟨2872872, by rfl⟩ : syracuseStep 7660993 = 5745745) B5745745
theorem B2549245 : Blo 794341 2549245 := bstep (se 3 (by rfl) ⟨477983, by rfl⟩ : syracuseStep 2549245 = 955967) B955967
theorem B1795751 : Blo 794341 1795751 := bstep (se 1 (by rfl) ⟨1346813, by rfl⟩ : syracuseStep 1795751 = 2693627) B2693627
theorem B1796039 : Blo 794341 1796039 := bstep (se 1 (by rfl) ⟨1347029, by rfl⟩ : syracuseStep 1796039 = 2694059) B2694059
theorem B3631499 : Blo 794341 3631499 := bstep (se 1 (by rfl) ⟨2723624, by rfl⟩ : syracuseStep 3631499 = 5447249) B5447249
theorem B5827247 : Blo 794341 5827247 := bstep (se 1 (by rfl) ⟨4370435, by rfl⟩ : syracuseStep 5827247 = 8740871) B8740871
theorem B2681531 : Blo 794341 2681531 := bstep (se 1 (by rfl) ⟨2011148, by rfl⟩ : syracuseStep 2681531 = 4022297) B4022297
theorem B1436719 : Blo 794341 1436719 := bstep (se 1 (by rfl) ⟨1077539, by rfl⟩ : syracuseStep 1436719 = 2155079) B2155079
theorem B2420219 : Blo 794341 2420219 := bstep (se 1 (by rfl) ⟨1815164, by rfl⟩ : syracuseStep 2420219 = 3630329) B3630329
theorem B1437359 : Blo 794341 1437359 := bstep (se 1 (by rfl) ⟨1078019, by rfl⟩ : syracuseStep 1437359 = 2156039) B2156039
theorem B6811411 : Blo 794341 6811411 := bstep (se 1 (by rfl) ⟨5108558, by rfl⟩ : syracuseStep 6811411 = 10217117) B10217117
theorem B8745083 : Blo 794341 8745083 := bstep (se 1 (by rfl) ⟨6558812, by rfl⟩ : syracuseStep 8745083 = 13117625) B13117625
theorem B5435585 : Blo 794341 5435585 := bstep (se 2 (by rfl) ⟨2038344, by rfl⟩ : syracuseStep 5435585 = 4076689) B4076689
theorem B1274167 : Blo 794341 1274167 := bstep (se 1 (by rfl) ⟨955625, by rfl⟩ : syracuseStep 1274167 = 1911251) B1911251
theorem B2683475 : Blo 794341 2683475 := bstep (se 1 (by rfl) ⟨2012606, by rfl⟩ : syracuseStep 2683475 = 4025213) B4025213
theorem B2552435 : Blo 794341 2552435 := bstep (se 1 (by rfl) ⟨1914326, by rfl⟩ : syracuseStep 2552435 = 3828653) B3828653
theorem B1700615 : Blo 794341 1700615 := bstep (se 1 (by rfl) ⟨1275461, by rfl⟩ : syracuseStep 1700615 = 2550923) B2550923
theorem B1340489 : Blo 794341 1340489 := bstep (se 2 (by rfl) ⟨502683, by rfl⟩ : syracuseStep 1340489 = 1005367) B1005367
theorem B1274987 : Blo 794341 1274987 := bstep (se 1 (by rfl) ⟨956240, by rfl⟩ : syracuseStep 1274987 = 1912481) B1912481
theorem B2684123 : Blo 794341 2684123 := bstep (se 1 (by rfl) ⟨2013092, by rfl⟩ : syracuseStep 2684123 = 4026185) B4026185
theorem B5174579 : Blo 794341 5174579 := bstep (se 1 (by rfl) ⟨3880934, by rfl⟩ : syracuseStep 5174579 = 7761869) B7761869
theorem B20739629 : Blo 794341 20739629 := bstep (se 3 (by rfl) ⟨3888680, by rfl⟩ : syracuseStep 20739629 = 7777361) B7777361
theorem B1341049 : Blo 794341 1341049 := bstep (se 2 (by rfl) ⟨502893, by rfl⟩ : syracuseStep 1341049 = 1005787) B1005787
theorem B18904709 : Blo 794341 18904709 := bstep (se 4 (by rfl) ⟨1772316, by rfl⟩ : syracuseStep 18904709 = 3544633) B3544633
theorem B10319633 : Blo 794341 10319633 := bstep (se 2 (by rfl) ⟨3869862, by rfl⟩ : syracuseStep 10319633 = 7739725) B7739725
theorem B1275679 : Blo 794341 1275679 := bstep (se 1 (by rfl) ⟨956759, by rfl⟩ : syracuseStep 1275679 = 1913519) B1913519
theorem B849727 : Blo 794341 849727 := bstep (se 1 (by rfl) ⟨637295, by rfl⟩ : syracuseStep 849727 = 1274591) B1274591
theorem B6059933 : Blo 794341 6059933 := bstep (se 3 (by rfl) ⟨1136237, by rfl⟩ : syracuseStep 6059933 = 2272475) B2272475
theorem B2684987 : Blo 794341 2684987 := bstep (se 1 (by rfl) ⟨2013740, by rfl⟩ : syracuseStep 2684987 = 4027481) B4027481
theorem B1341535 : Blo 794341 1341535 := bstep (se 1 (by rfl) ⟨1006151, by rfl⟩ : syracuseStep 1341535 = 2012303) B2012303
theorem B4847759 : Blo 794341 4847759 := bstep (se 1 (by rfl) ⟨3635819, by rfl⟩ : syracuseStep 4847759 = 7271639) B7271639
theorem B2685257 : Blo 794341 2685257 := bstep (se 2 (by rfl) ⟨1006971, by rfl⟩ : syracuseStep 2685257 = 2013943) B2013943
theorem B4029263 : Blo 794341 4029263 := bstep (se 1 (by rfl) ⟨3021947, by rfl⟩ : syracuseStep 4029263 = 6043895) B6043895
theorem B3406799 : Blo 794341 3406799 := bstep (se 1 (by rfl) ⟨2555099, by rfl⟩ : syracuseStep 3406799 = 5110199) B5110199
theorem B850991 : Blo 794341 850991 := bstep (se 1 (by rfl) ⟨638243, by rfl⟩ : syracuseStep 850991 = 1276487) B1276487
theorem B5438621 : Blo 794341 5438621 := bstep (se 3 (by rfl) ⟨1019741, by rfl⟩ : syracuseStep 5438621 = 2039483) B2039483
theorem B1342831 : Blo 794341 1342831 := bstep (se 1 (by rfl) ⟨1007123, by rfl⟩ : syracuseStep 1342831 = 2014247) B2014247
theorem B1146475 : Blo 794341 1146475 := bstep (se 1 (by rfl) ⟨859856, by rfl⟩ : syracuseStep 1146475 = 1719713) B1719713
theorem B2686607 : Blo 794341 2686607 := bstep (se 1 (by rfl) ⟨2014955, by rfl⟩ : syracuseStep 2686607 = 4029911) B4029911
theorem B1277615 : Blo 794341 1277615 := bstep (se 1 (by rfl) ⟨958211, by rfl⟩ : syracuseStep 1277615 = 1916423) B1916423
theorem B1343209 : Blo 794341 1343209 := bstep (se 2 (by rfl) ⟨503703, by rfl⟩ : syracuseStep 1343209 = 1007407) B1007407
theorem B9699061 : Blo 794341 9699061 := bstep (se 5 (by rfl) ⟨454643, by rfl⟩ : syracuseStep 9699061 = 909287) B909287
theorem B3407741 : Blo 794341 3407741 := bstep (se 3 (by rfl) ⟨638951, by rfl⟩ : syracuseStep 3407741 = 1277903) B1277903
theorem B12451843 : Blo 794341 12451843 := bstep (se 1 (by rfl) ⟨9338882, by rfl⟩ : syracuseStep 12451843 = 18677765) B18677765
theorem B1343783 : Blo 794341 1343783 := bstep (se 1 (by rfl) ⟨1007837, by rfl⟩ : syracuseStep 1343783 = 2015675) B2015675
theorem B3834479 : Blo 794341 3834479 := bstep (se 1 (by rfl) ⟨2875859, by rfl⟩ : syracuseStep 3834479 = 5751719) B5751719
theorem B73466797 : Blo 794341 73466797 := bstep (se 3 (by rfl) ⟨13775024, by rfl⟩ : syracuseStep 73466797 = 27550049) B27550049
theorem B2950141 : Blo 794341 2950141 := bstep (se 3 (by rfl) ⟨553151, by rfl⟩ : syracuseStep 2950141 = 1106303) B1106303
theorem B984299 : Blo 794341 984299 := bstep (se 1 (by rfl) ⟨738224, by rfl⟩ : syracuseStep 984299 = 1476449) B1476449
theorem B2688281 : Blo 794341 2688281 := bstep (se 2 (by rfl) ⟨1008105, by rfl⟩ : syracuseStep 2688281 = 2016211) B2016211
theorem B3016055 : Blo 794341 3016055 := bstep (se 1 (by rfl) ⟨2262041, by rfl⟩ : syracuseStep 3016055 = 4524083) B4524083
theorem B1344937 : Blo 794341 1344937 := bstep (se 2 (by rfl) ⟨504351, by rfl⟩ : syracuseStep 1344937 = 1008703) B1008703
theorem B3016223 : Blo 794341 3016223 := bstep (se 1 (by rfl) ⟨2262167, by rfl⟩ : syracuseStep 3016223 = 4524335) B4524335
theorem B1508969 : Blo 794341 1508969 := bstep (se 2 (by rfl) ⟨565863, by rfl⟩ : syracuseStep 1508969 = 1131727) B1131727
theorem B39192217 : Blo 794341 39192217 := bstep (se 2 (by rfl) ⟨14697081, by rfl⟩ : syracuseStep 39192217 = 29394163) B29394163
theorem B3540743 : Blo 794341 3540743 := bstep (se 1 (by rfl) ⟨2655557, by rfl⟩ : syracuseStep 3540743 = 5311115) B5311115
theorem B4032503 : Blo 794341 4032503 := bstep (se 1 (by rfl) ⟨3024377, by rfl⟩ : syracuseStep 4032503 = 6048755) B6048755
theorem B2689307 : Blo 794341 2689307 := bstep (se 1 (by rfl) ⟨2016980, by rfl⟩ : syracuseStep 2689307 = 4033961) B4033961
theorem B2689469 : Blo 794341 2689469 := bstep (se 3 (by rfl) ⟨504275, by rfl⟩ : syracuseStep 2689469 = 1008551) B1008551
theorem B2689631 : Blo 794341 2689631 := bstep (se 1 (by rfl) ⟨2017223, by rfl⟩ : syracuseStep 2689631 = 4034447) B4034447
theorem B3639905 : Blo 794341 3639905 := bstep (se 2 (by rfl) ⟨1364964, by rfl⟩ : syracuseStep 3639905 = 2729929) B2729929
theorem B4525267 : Blo 794341 4525267 := bstep (se 1 (by rfl) ⟨3393950, by rfl⟩ : syracuseStep 4525267 = 6787901) B6787901
theorem B2264411 : Blo 794341 2264411 := bstep (se 1 (by rfl) ⟨1698308, by rfl⟩ : syracuseStep 2264411 = 3396617) B3396617
theorem B11504987 : Blo 794341 11504987 := bstep (se 1 (by rfl) ⟨8628740, by rfl⟩ : syracuseStep 11504987 = 17257481) B17257481
theorem B3641075 : Blo 794341 3641075 := bstep (se 1 (by rfl) ⟨2730806, by rfl⟩ : syracuseStep 3641075 = 5461613) B5461613
theorem B1511399 : Blo 794341 1511399 := bstep (se 1 (by rfl) ⟨1133549, by rfl⟩ : syracuseStep 1511399 = 2267099) B2267099
theorem B10227779 : Blo 794341 10227779 := bstep (se 1 (by rfl) ⟨7670834, by rfl⟩ : syracuseStep 10227779 = 15341669) B15341669
theorem B3018941 : Blo 794341 3018941 := bstep (se 3 (by rfl) ⟨566051, by rfl⟩ : syracuseStep 3018941 = 1132103) B1132103
theorem B2691359 : Blo 794341 2691359 := bstep (se 1 (by rfl) ⟨2018519, by rfl⟩ : syracuseStep 2691359 = 4037039) B4037039
theorem B9179929 : Blo 794341 9179929 := bstep (se 2 (by rfl) ⟨3442473, by rfl⟩ : syracuseStep 9179929 = 6884947) B6884947
theorem B9081881 : Blo 794341 9081881 := bstep (se 2 (by rfl) ⟨3405705, by rfl⟩ : syracuseStep 9081881 = 6811411) B6811411
theorem B1611119 : Blo 794341 1611119 := bstep (se 1 (by rfl) ⟨1208339, by rfl⟩ : syracuseStep 1611119 = 2416679) B2416679
theorem B2692601 : Blo 794341 2692601 := bstep (se 2 (by rfl) ⟨1009725, by rfl⟩ : syracuseStep 2692601 = 2019451) B2019451
theorem B2692763 : Blo 794341 2692763 := bstep (se 1 (by rfl) ⟨2019572, by rfl⟩ : syracuseStep 2692763 = 4039145) B4039145
theorem B2692871 : Blo 794341 2692871 := bstep (se 1 (by rfl) ⟨2019653, by rfl⟩ : syracuseStep 2692871 = 4039307) B4039307
theorem B1513313 : Blo 794341 1513313 := bstep (se 2 (by rfl) ⟨567492, by rfl⟩ : syracuseStep 1513313 = 1134985) B1134985
theorem B1514999 : Blo 794341 1514999 := bstep (se 1 (by rfl) ⟨1136249, by rfl⟩ : syracuseStep 1514999 = 2272499) B2272499
theorem B3022343 : Blo 794341 3022343 := bstep (se 1 (by rfl) ⟨2266757, by rfl⟩ : syracuseStep 3022343 = 4533515) B4533515
theorem B4300361 : Blo 794341 4300361 := bstep (se 2 (by rfl) ⟨1612635, by rfl⟩ : syracuseStep 4300361 = 3225271) B3225271
theorem B1613479 : Blo 794341 1613479 := bstep (se 1 (by rfl) ⟨1210109, by rfl⟩ : syracuseStep 1613479 = 2420219) B2420219
theorem B3022555 : Blo 794341 3022555 := bstep (se 1 (by rfl) ⟨2266916, by rfl⟩ : syracuseStep 3022555 = 4533833) B4533833
theorem B794343 : Blo 794341 794343 := bstep (se 1 (by rfl) ⟨595757, by rfl⟩ : syracuseStep 794343 = 1191515) B1191515
theorem B794399 : Blo 794341 794399 := bstep (se 1 (by rfl) ⟨595799, by rfl⟩ : syracuseStep 794399 = 1191599) B1191599
theorem B4038497 : Blo 794341 4038497 := bstep (se 2 (by rfl) ⟨1514436, by rfl⟩ : syracuseStep 4038497 = 3028873) B3028873
theorem B794479 : Blo 794341 794479 := bstep (se 1 (by rfl) ⟨595859, by rfl⟩ : syracuseStep 794479 = 1191719) B1191719
theorem B9084797 : Blo 794341 9084797 := bstep (se 3 (by rfl) ⟨1703399, by rfl⟩ : syracuseStep 9084797 = 3406799) B3406799
theorem B794535 : Blo 794341 794535 := bstep (se 1 (by rfl) ⟨595901, by rfl⟩ : syracuseStep 794535 = 1191803) B1191803
theorem B1908859 : Blo 794341 1908859 := bstep (se 1 (by rfl) ⟨1431644, by rfl⟩ : syracuseStep 1908859 = 2863289) B2863289
theorem B2269309 : Blo 794341 2269309 := bstep (se 3 (by rfl) ⟨425495, by rfl⟩ : syracuseStep 2269309 = 850991) B850991
theorem B794815 : Blo 794341 794815 := bstep (se 1 (by rfl) ⟨596111, by rfl⟩ : syracuseStep 794815 = 1192223) B1192223
theorem B794831 : Blo 794341 794831 := bstep (se 1 (by rfl) ⟨596123, by rfl⟩ : syracuseStep 794831 = 1192247) B1192247
theorem B794879 : Blo 794341 794879 := bstep (se 1 (by rfl) ⟨596159, by rfl⟩ : syracuseStep 794879 = 1192319) B1192319
theorem B794927 : Blo 794341 794927 := bstep (se 1 (by rfl) ⟨596195, by rfl⟩ : syracuseStep 794927 = 1192391) B1192391
theorem B31072691 : Blo 794341 31072691 := bstep (se 1 (by rfl) ⟨23304518, by rfl⟩ : syracuseStep 31072691 = 46609037) B46609037
theorem B795163 : Blo 794341 795163 := bstep (se 1 (by rfl) ⟨596372, by rfl⟩ : syracuseStep 795163 = 1192745) B1192745
theorem B795167 : Blo 794341 795167 := bstep (se 1 (by rfl) ⟨596375, by rfl⟩ : syracuseStep 795167 = 1192751) B1192751
theorem B795247 : Blo 794341 795247 := bstep (se 1 (by rfl) ⟨596435, by rfl⟩ : syracuseStep 795247 = 1192871) B1192871
theorem B795303 : Blo 794341 795303 := bstep (se 1 (by rfl) ⟨596477, by rfl⟩ : syracuseStep 795303 = 1192955) B1192955
theorem B6890183 : Blo 794341 6890183 := bstep (se 1 (by rfl) ⟨5167637, by rfl⟩ : syracuseStep 6890183 = 10335275) B10335275
theorem B795343 : Blo 794341 795343 := bstep (se 1 (by rfl) ⟨596507, by rfl⟩ : syracuseStep 795343 = 1193015) B1193015
theorem B893659 : Blo 794341 893659 := bstep (se 1 (by rfl) ⟨670244, by rfl⟩ : syracuseStep 893659 = 1340489) B1340489
theorem B3941111 : Blo 794341 3941111 := bstep (se 1 (by rfl) ⟨2955833, by rfl⟩ : syracuseStep 3941111 = 5911667) B5911667
theorem B795423 : Blo 794341 795423 := bstep (se 1 (by rfl) ⟨596567, by rfl⟩ : syracuseStep 795423 = 1193135) B1193135
theorem B4596527 : Blo 794341 4596527 := bstep (se 1 (by rfl) ⟨3447395, by rfl⟩ : syracuseStep 4596527 = 6894791) B6894791
theorem B1909559 : Blo 794341 1909559 := bstep (se 1 (by rfl) ⟨1432169, by rfl⟩ : syracuseStep 1909559 = 2864339) B2864339
theorem B18359135 : Blo 794341 18359135 := bstep (se 1 (by rfl) ⟨13769351, by rfl⟩ : syracuseStep 18359135 = 27538703) B27538703
theorem B3449719 : Blo 794341 3449719 := bstep (se 1 (by rfl) ⟨2587289, by rfl⟩ : syracuseStep 3449719 = 5174579) B5174579
theorem B795695 : Blo 794341 795695 := bstep (se 1 (by rfl) ⟨596771, by rfl⟩ : syracuseStep 795695 = 1193543) B1193543
theorem B795759 : Blo 794341 795759 := bstep (se 1 (by rfl) ⟨596819, by rfl⟩ : syracuseStep 795759 = 1193639) B1193639
theorem B795815 : Blo 794341 795815 := bstep (se 1 (by rfl) ⟨596861, by rfl⟩ : syracuseStep 795815 = 1193723) B1193723
theorem B795839 : Blo 794341 795839 := bstep (se 1 (by rfl) ⟨596879, by rfl⟩ : syracuseStep 795839 = 1193759) B1193759
theorem B795871 : Blo 794341 795871 := bstep (se 1 (by rfl) ⟨596903, by rfl⟩ : syracuseStep 795871 = 1193807) B1193807
theorem B4039955 : Blo 794341 4039955 := bstep (se 1 (by rfl) ⟨3029966, by rfl⟩ : syracuseStep 4039955 = 6059933) B6059933
theorem B795951 : Blo 794341 795951 := bstep (se 1 (by rfl) ⟨596963, by rfl⟩ : syracuseStep 795951 = 1193927) B1193927
theorem B796187 : Blo 794341 796187 := bstep (se 1 (by rfl) ⟨597140, by rfl⟩ : syracuseStep 796187 = 1194281) B1194281
theorem B796191 : Blo 794341 796191 := bstep (se 1 (by rfl) ⟨597143, by rfl⟩ : syracuseStep 796191 = 1194287) B1194287
theorem B3024499 : Blo 794341 3024499 := bstep (se 1 (by rfl) ⟨2268374, by rfl⟩ : syracuseStep 3024499 = 4536749) B4536749
theorem B83699345 : Blo 794341 83699345 := bstep (se 2 (by rfl) ⟨31387254, by rfl⟩ : syracuseStep 83699345 = 62774509) B62774509
theorem B796351 : Blo 794341 796351 := bstep (se 1 (by rfl) ⟨597263, by rfl⟩ : syracuseStep 796351 = 1194527) B1194527
theorem B796607 : Blo 794341 796607 := bstep (se 1 (by rfl) ⟨597455, by rfl⟩ : syracuseStep 796607 = 1194911) B1194911
theorem B796639 : Blo 794341 796639 := bstep (se 1 (by rfl) ⟨597479, by rfl⟩ : syracuseStep 796639 = 1194959) B1194959
theorem B796699 : Blo 794341 796699 := bstep (se 1 (by rfl) ⟨597524, by rfl⟩ : syracuseStep 796699 = 1195049) B1195049
theorem B796703 : Blo 794341 796703 := bstep (se 1 (by rfl) ⟨597527, by rfl⟩ : syracuseStep 796703 = 1195055) B1195055
theorem B796719 : Blo 794341 796719 := bstep (se 1 (by rfl) ⟨597539, by rfl⟩ : syracuseStep 796719 = 1195079) B1195079
theorem B796895 : Blo 794341 796895 := bstep (se 1 (by rfl) ⟨597671, by rfl⟩ : syracuseStep 796895 = 1195343) B1195343
theorem B796955 : Blo 794341 796955 := bstep (se 1 (by rfl) ⟨597716, by rfl⟩ : syracuseStep 796955 = 1195433) B1195433
theorem B797055 : Blo 794341 797055 := bstep (se 1 (by rfl) ⟨597791, by rfl⟩ : syracuseStep 797055 = 1195583) B1195583
theorem B797231 : Blo 794341 797231 := bstep (se 1 (by rfl) ⟨597923, by rfl⟩ : syracuseStep 797231 = 1195847) B1195847
theorem B2271827 : Blo 794341 2271827 := bstep (se 1 (by rfl) ⟨1703870, by rfl⟩ : syracuseStep 2271827 = 3407741) B3407741
theorem B797287 : Blo 794341 797287 := bstep (se 1 (by rfl) ⟨597965, by rfl⟩ : syracuseStep 797287 = 1195931) B1195931
theorem B6793915 : Blo 794341 6793915 := bstep (se 1 (by rfl) ⟨5095436, by rfl⟩ : syracuseStep 6793915 = 10190873) B10190873
theorem B895783 : Blo 794341 895783 := bstep (se 1 (by rfl) ⟨671837, by rfl⟩ : syracuseStep 895783 = 1343675) B1343675
theorem B797663 : Blo 794341 797663 := bstep (se 1 (by rfl) ⟨598247, by rfl⟩ : syracuseStep 797663 = 1196495) B1196495
theorem B797691 : Blo 794341 797691 := bstep (se 1 (by rfl) ⟨598268, by rfl⟩ : syracuseStep 797691 = 1196537) B1196537
theorem B797759 : Blo 794341 797759 := bstep (se 1 (by rfl) ⟨598319, by rfl⟩ : syracuseStep 797759 = 1196639) B1196639
theorem B3026231 : Blo 794341 3026231 := bstep (se 1 (by rfl) ⟨2269673, by rfl⟩ : syracuseStep 3026231 = 4539347) B4539347
theorem B798079 : Blo 794341 798079 := bstep (se 1 (by rfl) ⟨598559, by rfl⟩ : syracuseStep 798079 = 1197119) B1197119
theorem B798107 : Blo 794341 798107 := bstep (se 1 (by rfl) ⟨598580, by rfl⟩ : syracuseStep 798107 = 1197161) B1197161
theorem B798175 : Blo 794341 798175 := bstep (se 1 (by rfl) ⟨598631, by rfl⟩ : syracuseStep 798175 = 1197263) B1197263
theorem B798311 : Blo 794341 798311 := bstep (se 1 (by rfl) ⟨598733, by rfl⟩ : syracuseStep 798311 = 1197467) B1197467
theorem B1191743 : Blo 794341 1191743 := bstep (se 1 (by rfl) ⟨893807, by rfl⟩ : syracuseStep 1191743 = 1787615) B1787615
theorem B6041465 : Blo 794341 6041465 := bstep (se 2 (by rfl) ⟨2265549, by rfl⟩ : syracuseStep 6041465 = 4531099) B4531099
theorem B897007 : Blo 794341 897007 := bstep (se 1 (by rfl) ⟨672755, by rfl⟩ : syracuseStep 897007 = 1345511) B1345511
theorem B6795251 : Blo 794341 6795251 := bstep (se 1 (by rfl) ⟨5096438, by rfl⟩ : syracuseStep 6795251 = 10192877) B10192877
theorem B1191929 : Blo 794341 1191929 := bstep (se 2 (by rfl) ⟨446973, by rfl⟩ : syracuseStep 1191929 = 893947) B893947
theorem B897151 : Blo 794341 897151 := bstep (se 1 (by rfl) ⟨672863, by rfl⟩ : syracuseStep 897151 = 1345727) B1345727
theorem B1192169 : Blo 794341 1192169 := bstep (se 2 (by rfl) ⟨447063, by rfl⟩ : syracuseStep 1192169 = 894127) B894127
theorem B1192295 : Blo 794341 1192295 := bstep (se 1 (by rfl) ⟨894221, by rfl⟩ : syracuseStep 1192295 = 1788443) B1788443
theorem B4534973 : Blo 794341 4534973 := bstep (se 3 (by rfl) ⟨850307, by rfl⟩ : syracuseStep 4534973 = 1700615) B1700615
theorem B1192841 : Blo 794341 1192841 := bstep (se 2 (by rfl) ⟨447315, by rfl⟩ : syracuseStep 1192841 = 894631) B894631
theorem B2012111 : Blo 794341 2012111 := bstep (se 1 (by rfl) ⟨1509083, by rfl⟩ : syracuseStep 2012111 = 3018167) B3018167
theorem B3453961 : Blo 794341 3453961 := bstep (se 2 (by rfl) ⟨1295235, by rfl⟩ : syracuseStep 3453961 = 2590471) B2590471
theorem B1193225 : Blo 794341 1193225 := bstep (se 2 (by rfl) ⟨447459, by rfl⟩ : syracuseStep 1193225 = 894919) B894919
theorem B1193279 : Blo 794341 1193279 := bstep (se 1 (by rfl) ⟨894959, by rfl⟩ : syracuseStep 1193279 = 1789919) B1789919
theorem B8599243 : Blo 794341 8599243 := bstep (se 1 (by rfl) ⟨6449432, by rfl⟩ : syracuseStep 8599243 = 12898865) B12898865
theorem B1193705 : Blo 794341 1193705 := bstep (se 2 (by rfl) ⟨447639, by rfl⟩ : syracuseStep 1193705 = 895279) B895279
theorem B1193711 : Blo 794341 1193711 := bstep (se 1 (by rfl) ⟨895283, by rfl⟩ : syracuseStep 1193711 = 1790567) B1790567
theorem B3029147 : Blo 794341 3029147 := bstep (se 1 (by rfl) ⟨2271860, by rfl⟩ : syracuseStep 3029147 = 4543721) B4543721
theorem B1194167 : Blo 794341 1194167 := bstep (se 1 (by rfl) ⟨895625, by rfl⟩ : syracuseStep 1194167 = 1791251) B1791251
theorem B1194215 : Blo 794341 1194215 := bstep (se 1 (by rfl) ⟨895661, by rfl⟩ : syracuseStep 1194215 = 1791323) B1791323
theorem B14531075 : Blo 794341 14531075 := bstep (se 1 (by rfl) ⟨10898306, by rfl⟩ : syracuseStep 14531075 = 21796613) B21796613
theorem B1194587 : Blo 794341 1194587 := bstep (se 1 (by rfl) ⟨895940, by rfl⟩ : syracuseStep 1194587 = 1791881) B1791881
theorem B3029663 : Blo 794341 3029663 := bstep (se 1 (by rfl) ⟨2272247, by rfl⟩ : syracuseStep 3029663 = 4544495) B4544495
theorem B1915625 : Blo 794341 1915625 := bstep (se 2 (by rfl) ⟨718359, by rfl⟩ : syracuseStep 1915625 = 1436719) B1436719
theorem B1194731 : Blo 794341 1194731 := bstep (se 1 (by rfl) ⟨896048, by rfl⟩ : syracuseStep 1194731 = 1792097) B1792097
theorem B1194761 : Blo 794341 1194761 := bstep (se 2 (by rfl) ⟨448035, by rfl⟩ : syracuseStep 1194761 = 896071) B896071
theorem B1817353 : Blo 794341 1817353 := bstep (se 2 (by rfl) ⟨681507, by rfl⟩ : syracuseStep 1817353 = 1363015) B1363015
theorem B50412557 : Blo 794341 50412557 := bstep (se 3 (by rfl) ⟨9452354, by rfl⟩ : syracuseStep 50412557 = 18904709) B18904709
theorem B39271891 : Blo 794341 39271891 := bstep (se 1 (by rfl) ⟨29453918, by rfl⟩ : syracuseStep 39271891 = 58907837) B58907837
theorem B3030635 : Blo 794341 3030635 := bstep (se 1 (by rfl) ⟨2272976, by rfl⟩ : syracuseStep 3030635 = 4545953) B4545953
theorem B1195631 : Blo 794341 1195631 := bstep (se 1 (by rfl) ⟨896723, by rfl⟩ : syracuseStep 1195631 = 1793447) B1793447
theorem B1195751 : Blo 794341 1195751 := bstep (se 1 (by rfl) ⟨896813, by rfl⟩ : syracuseStep 1195751 = 1793627) B1793627
theorem B1195943 : Blo 794341 1195943 := bstep (se 1 (by rfl) ⟨896957, by rfl⟩ : syracuseStep 1195943 = 1793915) B1793915
theorem B1196267 : Blo 794341 1196267 := bstep (se 1 (by rfl) ⟨897200, by rfl⟩ : syracuseStep 1196267 = 1794401) B1794401
theorem B1720615 : Blo 794341 1720615 := bstep (se 1 (by rfl) ⟨1290461, by rfl⟩ : syracuseStep 1720615 = 2580923) B2580923
theorem B4538663 : Blo 794341 4538663 := bstep (se 1 (by rfl) ⟨3403997, by rfl⟩ : syracuseStep 4538663 = 6807995) B6807995
theorem B1196327 : Blo 794341 1196327 := bstep (se 1 (by rfl) ⟨897245, by rfl⟩ : syracuseStep 1196327 = 1794491) B1794491
theorem B1196999 : Blo 794341 1196999 := bstep (se 1 (by rfl) ⟨897749, by rfl⟩ : syracuseStep 1196999 = 1795499) B1795499
theorem B1197167 : Blo 794341 1197167 := bstep (se 1 (by rfl) ⟨897875, by rfl⟩ : syracuseStep 1197167 = 1795751) B1795751
theorem B1197359 : Blo 794341 1197359 := bstep (se 1 (by rfl) ⟨898019, by rfl⟩ : syracuseStep 1197359 = 1796039) B1796039
theorem B3884831 : Blo 794341 3884831 := bstep (se 1 (by rfl) ⟨2913623, by rfl⟩ : syracuseStep 3884831 = 5827247) B5827247
theorem B1787687 : Blo 794341 1787687 := bstep (se 1 (by rfl) ⟨1340765, by rfl⟩ : syracuseStep 1787687 = 2681531) B2681531
theorem B4081529 : Blo 794341 4081529 := bstep (se 2 (by rfl) ⟨1530573, by rfl⟩ : syracuseStep 4081529 = 3061147) B3061147
theorem B1788065 : Blo 794341 1788065 := bstep (se 2 (by rfl) ⟨670524, by rfl⟩ : syracuseStep 1788065 = 1341049) B1341049
theorem B1132969 : Blo 794341 1132969 := bstep (se 2 (by rfl) ⟨424863, by rfl⟩ : syracuseStep 1132969 = 849727) B849727
theorem B3394345 : Blo 794341 3394345 := bstep (se 2 (by rfl) ⟨1272879, by rfl⟩ : syracuseStep 3394345 = 2545759) B2545759
theorem B1788713 : Blo 794341 1788713 := bstep (se 2 (by rfl) ⟨670767, by rfl⟩ : syracuseStep 1788713 = 1341535) B1341535
theorem B3623723 : Blo 794341 3623723 := bstep (se 1 (by rfl) ⟨2717792, by rfl⟩ : syracuseStep 3623723 = 5435585) B5435585
theorem B2149249 : Blo 794341 2149249 := bstep (se 2 (by rfl) ⟨805968, by rfl⟩ : syracuseStep 2149249 = 1611937) B1611937
theorem B1788983 : Blo 794341 1788983 := bstep (se 1 (by rfl) ⟨1341737, by rfl⟩ : syracuseStep 1788983 = 2683475) B2683475
theorem B14502989 : Blo 794341 14502989 := bstep (se 3 (by rfl) ⟨2719310, by rfl⟩ : syracuseStep 14502989 = 5438621) B5438621
theorem B3394703 : Blo 794341 3394703 := bstep (se 1 (by rfl) ⟨2546027, by rfl⟩ : syracuseStep 3394703 = 5092055) B5092055
theorem B2018479 : Blo 794341 2018479 := bstep (se 1 (by rfl) ⟨1513859, by rfl⟩ : syracuseStep 2018479 = 3027719) B3027719
theorem B1789415 : Blo 794341 1789415 := bstep (se 1 (by rfl) ⟨1342061, by rfl⟩ : syracuseStep 1789415 = 2684123) B2684123
theorem B1789991 : Blo 794341 1789991 := bstep (se 1 (by rfl) ⟨1342493, by rfl⟩ : syracuseStep 1789991 = 2684987) B2684987
theorem B3231839 : Blo 794341 3231839 := bstep (se 1 (by rfl) ⟨2423879, by rfl⟩ : syracuseStep 3231839 = 4847759) B4847759
theorem B6803621 : Blo 794341 6803621 := bstep (se 4 (by rfl) ⟨637839, by rfl⟩ : syracuseStep 6803621 = 1275679) B1275679
theorem B5099719 : Blo 794341 5099719 := bstep (se 1 (by rfl) ⟨3824789, by rfl⟩ : syracuseStep 5099719 = 7649579) B7649579
theorem B1790171 : Blo 794341 1790171 := bstep (se 1 (by rfl) ⟨1342628, by rfl⟩ : syracuseStep 1790171 = 2685257) B2685257
theorem B1790441 : Blo 794341 1790441 := bstep (se 2 (by rfl) ⟨671415, by rfl⟩ : syracuseStep 1790441 = 1342831) B1342831
theorem B1528633 : Blo 794341 1528633 := bstep (se 2 (by rfl) ⟨573237, by rfl⟩ : syracuseStep 1528633 = 1146475) B1146475
theorem B2872169 : Blo 794341 2872169 := bstep (se 2 (by rfl) ⟨1077063, by rfl⟩ : syracuseStep 2872169 = 2154127) B2154127
theorem B1790945 : Blo 794341 1790945 := bstep (se 2 (by rfl) ⟨671604, by rfl⟩ : syracuseStep 1790945 = 1343209) B1343209
theorem B906223 : Blo 794341 906223 := bstep (se 1 (by rfl) ⟨679667, by rfl⟩ : syracuseStep 906223 = 1359335) B1359335
theorem B12932081 : Blo 794341 12932081 := bstep (se 2 (by rfl) ⟨4849530, by rfl⟩ : syracuseStep 12932081 = 9699061) B9699061
theorem B1791071 : Blo 794341 1791071 := bstep (se 1 (by rfl) ⟨1343303, by rfl⟩ : syracuseStep 1791071 = 2686607) B2686607
theorem B6214751 : Blo 794341 6214751 := bstep (se 1 (by rfl) ⟨4661063, by rfl⟩ : syracuseStep 6214751 = 9322127) B9322127
theorem B1496159 : Blo 794341 1496159 := bstep (se 1 (by rfl) ⟨1122119, by rfl⟩ : syracuseStep 1496159 = 2244239) B2244239
theorem B11457935 : Blo 794341 11457935 := bstep (se 1 (by rfl) ⟨8593451, by rfl⟩ : syracuseStep 11457935 = 17186903) B17186903
theorem B3823271 : Blo 794341 3823271 := bstep (se 1 (by rfl) ⟨2867453, by rfl⟩ : syracuseStep 3823271 = 5734907) B5734907
theorem B1791827 : Blo 794341 1791827 := bstep (se 1 (by rfl) ⟨1343870, by rfl⟩ : syracuseStep 1791827 = 2687741) B2687741
theorem B1792313 : Blo 794341 1792313 := bstep (se 2 (by rfl) ⟨672117, by rfl⟩ : syracuseStep 1792313 = 1344235) B1344235
theorem B2873681 : Blo 794341 2873681 := bstep (se 2 (by rfl) ⟨1077630, by rfl⟩ : syracuseStep 2873681 = 2155261) B2155261
theorem B2185631 : Blo 794341 2185631 := bstep (se 1 (by rfl) ⟨1639223, by rfl⟩ : syracuseStep 2185631 = 3278447) B3278447
theorem B20404709 : Blo 794341 20404709 := bstep (se 4 (by rfl) ⟨1912941, by rfl⟩ : syracuseStep 20404709 = 3825883) B3825883
theorem B5102203 : Blo 794341 5102203 := bstep (se 1 (by rfl) ⟨3826652, by rfl⟩ : syracuseStep 5102203 = 7653305) B7653305
theorem B1793231 : Blo 794341 1793231 := bstep (se 1 (by rfl) ⟨1344923, by rfl⟩ : syracuseStep 1793231 = 2689847) B2689847
theorem B7462145 : Blo 794341 7462145 := bstep (se 2 (by rfl) ⟨2798304, by rfl⟩ : syracuseStep 7462145 = 5596609) B5596609
theorem B10214657 : Blo 794341 10214657 := bstep (se 2 (by rfl) ⟨3830496, by rfl⟩ : syracuseStep 10214657 = 7660993) B7660993
theorem B3398993 : Blo 794341 3398993 := bstep (se 2 (by rfl) ⟨1274622, by rfl⟩ : syracuseStep 3398993 = 2549245) B2549245
theorem B1793609 : Blo 794341 1793609 := bstep (se 2 (by rfl) ⟨672603, by rfl⟩ : syracuseStep 1793609 = 1345207) B1345207
theorem B1531559 : Blo 794341 1531559 := bstep (se 1 (by rfl) ⟨1148669, by rfl⟩ : syracuseStep 1531559 = 2297339) B2297339
theorem B2416495 : Blo 794341 2416495 := bstep (se 1 (by rfl) ⟨1812371, by rfl⟩ : syracuseStep 2416495 = 3624743) B3624743
theorem B3399965 : Blo 794341 3399965 := bstep (se 3 (by rfl) ⟨637493, by rfl⟩ : syracuseStep 3399965 = 1274987) B1274987
theorem B1794779 : Blo 794341 1794779 := bstep (se 1 (by rfl) ⟨1346084, by rfl⟩ : syracuseStep 1794779 = 2692169) B2692169
theorem B1795193 : Blo 794341 1795193 := bstep (se 2 (by rfl) ⟨673197, by rfl⟩ : syracuseStep 1795193 = 1346395) B1346395
theorem B22963499 : Blo 794341 22963499 := bstep (se 1 (by rfl) ⟨17222624, by rfl⟩ : syracuseStep 22963499 = 34445249) B34445249
theorem B1795859 : Blo 794341 1795859 := bstep (se 1 (by rfl) ⟨1346894, by rfl⟩ : syracuseStep 1795859 = 2693789) B2693789
theorem B1796075 : Blo 794341 1796075 := bstep (se 1 (by rfl) ⟨1347056, by rfl⟩ : syracuseStep 1796075 = 2694113) B2694113
theorem B4024403 : Blo 794341 4024403 := bstep (se 1 (by rfl) ⟨3018302, by rfl⟩ : syracuseStep 4024403 = 6036605) B6036605
theorem B6056045 : Blo 794341 6056045 := bstep (se 3 (by rfl) ⟨1135508, by rfl⟩ : syracuseStep 6056045 = 2271017) B2271017
theorem B1796219 : Blo 794341 1796219 := bstep (se 1 (by rfl) ⟨1347164, by rfl⟩ : syracuseStep 1796219 = 2694329) B2694329
theorem B2156777 : Blo 794341 2156777 := bstep (se 2 (by rfl) ⟨808791, by rfl⟩ : syracuseStep 2156777 = 1617583) B1617583
theorem B1075511 : Blo 794341 1075511 := bstep (se 1 (by rfl) ⟨806633, by rfl⟩ : syracuseStep 1075511 = 1613267) B1613267
theorem B7268717 : Blo 794341 7268717 := bstep (se 3 (by rfl) ⟨1362884, by rfl⟩ : syracuseStep 7268717 = 2725769) B2725769
theorem B3828329 : Blo 794341 3828329 := bstep (se 2 (by rfl) ⟨1435623, by rfl⟩ : syracuseStep 3828329 = 2871247) B2871247
theorem B1698889 : Blo 794341 1698889 := bstep (se 2 (by rfl) ⟨637083, by rfl⟩ : syracuseStep 1698889 = 1274167) B1274167
theorem B1273001 : Blo 794341 1273001 := bstep (se 2 (by rfl) ⟨477375, by rfl⟩ : syracuseStep 1273001 = 954751) B954751
theorem B3828959 : Blo 794341 3828959 := bstep (se 1 (by rfl) ⟨2871719, by rfl⟩ : syracuseStep 3828959 = 5743439) B5743439
theorem B5533265 : Blo 794341 5533265 := bstep (se 2 (by rfl) ⟨2074974, by rfl⟩ : syracuseStep 5533265 = 4149949) B4149949
theorem B14708567 : Blo 794341 14708567 := bstep (se 1 (by rfl) ⟨11031425, by rfl⟩ : syracuseStep 14708567 = 22062851) B22062851
theorem B14512391 : Blo 794341 14512391 := bstep (se 1 (by rfl) ⟨10884293, by rfl⟩ : syracuseStep 14512391 = 21768587) B21768587
theorem B2420999 : Blo 794341 2420999 := bstep (se 1 (by rfl) ⟨1815749, by rfl⟩ : syracuseStep 2420999 = 3631499) B3631499
theorem B4092287 : Blo 794341 4092287 := bstep (se 1 (by rfl) ⟨3069215, by rfl⟩ : syracuseStep 4092287 = 6138431) B6138431
theorem B6452027 : Blo 794341 6452027 := bstep (se 1 (by rfl) ⟨4839020, by rfl⟩ : syracuseStep 6452027 = 9678041) B9678041
theorem B5830055 : Blo 794341 5830055 := bstep (se 1 (by rfl) ⟨4372541, by rfl⟩ : syracuseStep 5830055 = 8745083) B8745083
theorem B4028129 : Blo 794341 4028129 := bstep (se 2 (by rfl) ⟨1510548, by rfl⟩ : syracuseStep 4028129 = 3021097) B3021097
theorem B1701623 : Blo 794341 1701623 := bstep (se 1 (by rfl) ⟨1276217, by rfl⟩ : syracuseStep 1701623 = 2552435) B2552435
theorem B1341481 : Blo 794341 1341481 := bstep (se 2 (by rfl) ⟨503055, by rfl⟩ : syracuseStep 1341481 = 1006111) B1006111
theorem B1341623 : Blo 794341 1341623 := bstep (se 1 (by rfl) ⟨1006217, by rfl⟩ : syracuseStep 1341623 = 2012435) B2012435
theorem B3832019 : Blo 794341 3832019 := bstep (se 1 (by rfl) ⟨2874014, by rfl⟩ : syracuseStep 3832019 = 5748029) B5748029
theorem B13826419 : Blo 794341 13826419 := bstep (se 1 (by rfl) ⟨10369814, by rfl⟩ : syracuseStep 13826419 = 20739629) B20739629
theorem B6879755 : Blo 794341 6879755 := bstep (se 1 (by rfl) ⟨5159816, by rfl⟩ : syracuseStep 6879755 = 10319633) B10319633
theorem B2554409 : Blo 794341 2554409 := bstep (se 2 (by rfl) ⟨957903, by rfl⟩ : syracuseStep 2554409 = 1915807) B1915807
theorem B1342217 : Blo 794341 1342217 := bstep (se 2 (by rfl) ⟨503331, by rfl⟩ : syracuseStep 1342217 = 1006663) B1006663
theorem B3636127 : Blo 794341 3636127 := bstep (se 1 (by rfl) ⟨2727095, by rfl⟩ : syracuseStep 3636127 = 5454191) B5454191
theorem B1211483 : Blo 794341 1211483 := bstep (se 1 (by rfl) ⟨908612, by rfl⟩ : syracuseStep 1211483 = 1817225) B1817225
theorem B3832957 : Blo 794341 3832957 := bstep (se 3 (by rfl) ⟨718679, by rfl⟩ : syracuseStep 3832957 = 1437359) B1437359
theorem B2686175 : Blo 794341 2686175 := bstep (se 1 (by rfl) ⟨2014631, by rfl⟩ : syracuseStep 2686175 = 4029263) B4029263
theorem B11468081 : Blo 794341 11468081 := bstep (se 2 (by rfl) ⟨4300530, by rfl⟩ : syracuseStep 11468081 = 8601061) B8601061
theorem B3112577 : Blo 794341 3112577 := bstep (se 2 (by rfl) ⟨1167216, by rfl⟩ : syracuseStep 3112577 = 2334433) B2334433
theorem B4587293 : Blo 794341 4587293 := bstep (se 3 (by rfl) ⟨860117, by rfl⟩ : syracuseStep 4587293 = 1720235) B1720235
theorem B851743 : Blo 794341 851743 := bstep (se 1 (by rfl) ⟨638807, by rfl⟩ : syracuseStep 851743 = 1277615) B1277615
theorem B8618237 : Blo 794341 8618237 := bstep (se 3 (by rfl) ⟨1615919, by rfl⟩ : syracuseStep 8618237 = 3231839) B3231839
theorem B2294153 : Blo 794341 2294153 := bstep (se 2 (by rfl) ⟨860307, by rfl⟩ : syracuseStep 2294153 = 1720615) B1720615
theorem B2556319 : Blo 794341 2556319 := bstep (se 1 (by rfl) ⟨1917239, by rfl⟩ : syracuseStep 2556319 = 3834479) B3834479
theorem B10912765 : Blo 794341 10912765 := bstep (se 3 (by rfl) ⟨2046143, by rfl⟩ : syracuseStep 10912765 = 4092287) B4092287
theorem B2360495 : Blo 794341 2360495 := bstep (se 1 (by rfl) ⟨1770371, by rfl⟩ : syracuseStep 2360495 = 3540743) B3540743
theorem B2589887 : Blo 794341 2589887 := bstep (se 1 (by rfl) ⟨1942415, by rfl⟩ : syracuseStep 2589887 = 3884831) B3884831
theorem B2688335 : Blo 794341 2688335 := bstep (se 1 (by rfl) ⟨2016251, by rfl⟩ : syracuseStep 2688335 = 4032503) B4032503
theorem B3933521 : Blo 794341 3933521 := bstep (se 2 (by rfl) ⟨1475070, by rfl⟩ : syracuseStep 3933521 = 2950141) B2950141
theorem B2426603 : Blo 794341 2426603 := bstep (se 1 (by rfl) ⟨1819952, by rfl⟩ : syracuseStep 2426603 = 3639905) B3639905
theorem B9668659 : Blo 794341 9668659 := bstep (se 1 (by rfl) ⟨7251494, by rfl⟩ : syracuseStep 9668659 = 14502989) B14502989
theorem B2263135 : Blo 794341 2263135 := bstep (se 1 (by rfl) ⟨1697351, by rfl⟩ : syracuseStep 2263135 = 3394703) B3394703
theorem B4032665 : Blo 794341 4032665 := bstep (se 2 (by rfl) ⟨1512249, by rfl⟩ : syracuseStep 4032665 = 3024499) B3024499
theorem B1509607 : Blo 794341 1509607 := bstep (se 1 (by rfl) ⟨1132205, by rfl⟩ : syracuseStep 1509607 = 2264411) B2264411
theorem B7669991 : Blo 794341 7669991 := bstep (se 1 (by rfl) ⟨5752493, by rfl⟩ : syracuseStep 7669991 = 11504987) B11504987
theorem B2427383 : Blo 794341 2427383 := bstep (se 1 (by rfl) ⟨1820537, by rfl⟩ : syracuseStep 2427383 = 3641075) B3641075
theorem B6818519 : Blo 794341 6818519 := bstep (se 1 (by rfl) ⟨5113889, by rfl⟩ : syracuseStep 6818519 = 10227779) B10227779
theorem B1510625 : Blo 794341 1510625 := bstep (se 2 (by rfl) ⟨566484, by rfl⟩ : syracuseStep 1510625 = 1132969) B1132969
theorem B2624797 : Blo 794341 2624797 := bstep (se 3 (by rfl) ⟨492149, by rfl⟩ : syracuseStep 2624797 = 984299) B984299
theorem B8621387 : Blo 794341 8621387 := bstep (se 1 (by rfl) ⟨6466040, by rfl⟩ : syracuseStep 8621387 = 12932081) B12932081
theorem B7638623 : Blo 794341 7638623 := bstep (se 1 (by rfl) ⟨5728967, by rfl⟩ : syracuseStep 7638623 = 11457935) B11457935
theorem B4525793 : Blo 794341 4525793 := bstep (se 2 (by rfl) ⟨1697172, by rfl⟩ : syracuseStep 4525793 = 3394345) B3394345
theorem B2265185 : Blo 794341 2265185 := bstep (se 2 (by rfl) ⟨849444, by rfl⟩ : syracuseStep 2265185 = 1698889) B1698889
theorem B2691305 : Blo 794341 2691305 := bstep (se 2 (by rfl) ⟨1009239, by rfl⟩ : syracuseStep 2691305 = 2018479) B2018479
theorem B6033689 : Blo 794341 6033689 := bstep (se 2 (by rfl) ⟨2262633, by rfl⟩ : syracuseStep 6033689 = 4525267) B4525267
theorem B13603139 : Blo 794341 13603139 := bstep (se 1 (by rfl) ⟨10202354, by rfl⟩ : syracuseStep 13603139 = 20404709) B20404709
theorem B2265995 : Blo 794341 2265995 := bstep (se 1 (by rfl) ⟨1699496, by rfl⟩ : syracuseStep 2265995 = 3398993) B3398993
theorem B10884077 : Blo 794341 10884077 := bstep (se 3 (by rfl) ⟨2040764, by rfl⟩ : syracuseStep 10884077 = 4081529) B4081529
theorem B2692331 : Blo 794341 2692331 := bstep (se 1 (by rfl) ⟨2019248, by rfl⟩ : syracuseStep 2692331 = 4038497) B4038497
theorem B2266643 : Blo 794341 2266643 := bstep (se 1 (by rfl) ⟨1699982, by rfl⟩ : syracuseStep 2266643 = 3399965) B3399965
theorem B4593455 : Blo 794341 4593455 := bstep (se 1 (by rfl) ⟨3445091, by rfl⟩ : syracuseStep 4593455 = 6890183) B6890183
theorem B2627407 : Blo 794341 2627407 := bstep (se 1 (by rfl) ⟨1970555, by rfl⟩ : syracuseStep 2627407 = 3941111) B3941111
theorem B2693303 : Blo 794341 2693303 := bstep (se 1 (by rfl) ⟨2019977, by rfl⟩ : syracuseStep 2693303 = 4039955) B4039955
theorem B15308999 : Blo 794341 15308999 := bstep (se 1 (by rfl) ⟨11481749, by rfl⟩ : syracuseStep 15308999 = 22963499) B22963499
theorem B4037363 : Blo 794341 4037363 := bstep (se 1 (by rfl) ⟨3028022, by rfl⟩ : syracuseStep 4037363 = 6056045) B6056045
theorem B1514551 : Blo 794341 1514551 := bstep (se 1 (by rfl) ⟨1135913, by rfl⟩ : syracuseStep 1514551 = 2271827) B2271827
theorem B794495 : Blo 794341 794495 := bstep (se 1 (by rfl) ⟨595871, by rfl⟩ : syracuseStep 794495 = 1191743) B1191743
theorem B9805711 : Blo 794341 9805711 := bstep (se 1 (by rfl) ⟨7354283, by rfl⟩ : syracuseStep 9805711 = 14708567) B14708567
theorem B4530167 : Blo 794341 4530167 := bstep (se 1 (by rfl) ⟨3397625, by rfl⟩ : syracuseStep 4530167 = 6795251) B6795251
theorem B794619 : Blo 794341 794619 := bstep (se 1 (by rfl) ⟨595964, by rfl⟩ : syracuseStep 794619 = 1191929) B1191929
theorem B794779 : Blo 794341 794779 := bstep (se 1 (by rfl) ⟨596084, by rfl⟩ : syracuseStep 794779 = 1192169) B1192169
theorem B9674927 : Blo 794341 9674927 := bstep (se 1 (by rfl) ⟨7256195, by rfl⟩ : syracuseStep 9674927 = 14512391) B14512391
theorem B1613999 : Blo 794341 1613999 := bstep (se 1 (by rfl) ⟨1210499, by rfl⟩ : syracuseStep 1613999 = 2420999) B2420999
theorem B794863 : Blo 794341 794863 := bstep (se 1 (by rfl) ⟨596147, by rfl⟩ : syracuseStep 794863 = 1192295) B1192295
theorem B3023315 : Blo 794341 3023315 := bstep (se 1 (by rfl) ⟨2267486, by rfl⟩ : syracuseStep 3023315 = 4534973) B4534973
theorem B4301351 : Blo 794341 4301351 := bstep (se 1 (by rfl) ⟨3226013, by rfl⟩ : syracuseStep 4301351 = 6452027) B6452027
theorem B795227 : Blo 794341 795227 := bstep (se 1 (by rfl) ⟨596420, by rfl⟩ : syracuseStep 795227 = 1192841) B1192841
theorem B19899053 : Blo 794341 19899053 := bstep (se 3 (by rfl) ⟨3731072, by rfl⟩ : syracuseStep 19899053 = 7462145) B7462145
theorem B795483 : Blo 794341 795483 := bstep (se 1 (by rfl) ⟨596612, by rfl⟩ : syracuseStep 795483 = 1193225) B1193225
theorem B795519 : Blo 794341 795519 := bstep (se 1 (by rfl) ⟨596639, by rfl⟩ : syracuseStep 795519 = 1193279) B1193279
theorem B795803 : Blo 794341 795803 := bstep (se 1 (by rfl) ⟨596852, by rfl⟩ : syracuseStep 795803 = 1193705) B1193705
theorem B795807 : Blo 794341 795807 := bstep (se 1 (by rfl) ⟨596855, by rfl⟩ : syracuseStep 795807 = 1193711) B1193711
theorem B894415 : Blo 794341 894415 := bstep (se 1 (by rfl) ⟨670811, by rfl⟩ : syracuseStep 894415 = 1341623) B1341623
theorem B796111 : Blo 794341 796111 := bstep (se 1 (by rfl) ⟨597083, by rfl⟩ : syracuseStep 796111 = 1194167) B1194167
theorem B796143 : Blo 794341 796143 := bstep (se 1 (by rfl) ⟨597107, by rfl⟩ : syracuseStep 796143 = 1194215) B1194215
theorem B796391 : Blo 794341 796391 := bstep (se 1 (by rfl) ⟨597293, by rfl⟩ : syracuseStep 796391 = 1194587) B1194587
theorem B796487 : Blo 794341 796487 := bstep (se 1 (by rfl) ⟨597365, by rfl⟩ : syracuseStep 796487 = 1194731) B1194731
theorem B894811 : Blo 794341 894811 := bstep (se 1 (by rfl) ⟨671108, by rfl⟩ : syracuseStep 894811 = 1342217) B1342217
theorem B796507 : Blo 794341 796507 := bstep (se 1 (by rfl) ⟨597380, by rfl⟩ : syracuseStep 796507 = 1194761) B1194761
theorem B12232781 : Blo 794341 12232781 := bstep (se 3 (by rfl) ⟨2293646, by rfl⟩ : syracuseStep 12232781 = 4587293) B4587293
theorem B7645387 : Blo 794341 7645387 := bstep (se 1 (by rfl) ⟨5734040, by rfl⟩ : syracuseStep 7645387 = 11468081) B11468081
theorem B797087 : Blo 794341 797087 := bstep (se 1 (by rfl) ⟨597815, by rfl⟩ : syracuseStep 797087 = 1195631) B1195631
theorem B2075051 : Blo 794341 2075051 := bstep (se 1 (by rfl) ⟨1556288, by rfl⟩ : syracuseStep 2075051 = 3112577) B3112577
theorem B3221993 : Blo 794341 3221993 := bstep (se 2 (by rfl) ⟨1208247, by rfl⟩ : syracuseStep 3221993 = 2416495) B2416495
theorem B797167 : Blo 794341 797167 := bstep (se 1 (by rfl) ⟨597875, by rfl⟩ : syracuseStep 797167 = 1195751) B1195751
theorem B797295 : Blo 794341 797295 := bstep (se 1 (by rfl) ⟨597971, by rfl⟩ : syracuseStep 797295 = 1195943) B1195943
theorem B797511 : Blo 794341 797511 := bstep (se 1 (by rfl) ⟨598133, by rfl⟩ : syracuseStep 797511 = 1196267) B1196267
theorem B3025745 : Blo 794341 3025745 := bstep (se 2 (by rfl) ⟨1134654, by rfl⟩ : syracuseStep 3025745 = 2269309) B2269309
theorem B895855 : Blo 794341 895855 := bstep (se 1 (by rfl) ⟨671891, by rfl⟩ : syracuseStep 895855 = 1343783) B1343783
theorem B3025775 : Blo 794341 3025775 := bstep (se 1 (by rfl) ⟨2269331, by rfl⟩ : syracuseStep 3025775 = 4538663) B4538663
theorem B797551 : Blo 794341 797551 := bstep (se 1 (by rfl) ⟨598163, by rfl⟩ : syracuseStep 797551 = 1196327) B1196327
theorem B797999 : Blo 794341 797999 := bstep (se 1 (by rfl) ⟨598499, by rfl⟩ : syracuseStep 797999 = 1196999) B1196999
theorem B798111 : Blo 794341 798111 := bstep (se 1 (by rfl) ⟨598583, by rfl⟩ : syracuseStep 798111 = 1197167) B1197167
theorem B798239 : Blo 794341 798239 := bstep (se 1 (by rfl) ⟨598679, by rfl⟩ : syracuseStep 798239 = 1197359) B1197359
theorem B2010703 : Blo 794341 2010703 := bstep (se 1 (by rfl) ⟨1508027, by rfl⟩ : syracuseStep 2010703 = 3016055) B3016055
theorem B1191545 : Blo 794341 1191545 := bstep (se 2 (by rfl) ⟨446829, by rfl⟩ : syracuseStep 1191545 = 893659) B893659
theorem B2010815 : Blo 794341 2010815 := bstep (se 1 (by rfl) ⟨1508111, by rfl⟩ : syracuseStep 2010815 = 3016223) B3016223
theorem B1191791 : Blo 794341 1191791 := bstep (se 1 (by rfl) ⟨893843, by rfl⟩ : syracuseStep 1191791 = 1787687) B1787687
theorem B97955729 : Blo 794341 97955729 := bstep (se 2 (by rfl) ⟨36733398, by rfl⟩ : syracuseStep 97955729 = 73466797) B73466797
theorem B1192043 : Blo 794341 1192043 := bstep (se 1 (by rfl) ⟨894032, by rfl⟩ : syracuseStep 1192043 = 1788065) B1788065
theorem B1192475 : Blo 794341 1192475 := bstep (se 1 (by rfl) ⟨894356, by rfl⟩ : syracuseStep 1192475 = 1788713) B1788713
theorem B73740901 : Blo 794341 73740901 := bstep (se 4 (by rfl) ⟨6913209, by rfl⟩ : syracuseStep 73740901 = 13826419) B13826419
theorem B1192655 : Blo 794341 1192655 := bstep (se 1 (by rfl) ⟨894491, by rfl⟩ : syracuseStep 1192655 = 1788983) B1788983
theorem B1192943 : Blo 794341 1192943 := bstep (se 1 (by rfl) ⟨894707, by rfl⟩ : syracuseStep 1192943 = 1789415) B1789415
theorem B1193327 : Blo 794341 1193327 := bstep (se 1 (by rfl) ⟨894995, by rfl⟩ : syracuseStep 1193327 = 1789991) B1789991
theorem B4535747 : Blo 794341 4535747 := bstep (se 1 (by rfl) ⟨3401810, by rfl⟩ : syracuseStep 4535747 = 6803621) B6803621
theorem B2012627 : Blo 794341 2012627 := bstep (se 1 (by rfl) ⟨1509470, by rfl⟩ : syracuseStep 2012627 = 3018941) B3018941
theorem B1193447 : Blo 794341 1193447 := bstep (se 1 (by rfl) ⟨895085, by rfl⟩ : syracuseStep 1193447 = 1790171) B1790171
theorem B1193627 : Blo 794341 1193627 := bstep (se 1 (by rfl) ⟨895220, by rfl⟩ : syracuseStep 1193627 = 1790441) B1790441
theorem B1914779 : Blo 794341 1914779 := bstep (se 1 (by rfl) ⟨1436084, by rfl⟩ : syracuseStep 1914779 = 2872169) B2872169
theorem B1193963 : Blo 794341 1193963 := bstep (se 1 (by rfl) ⟨895472, by rfl⟩ : syracuseStep 1193963 = 1790945) B1790945
theorem B1194047 : Blo 794341 1194047 := bstep (se 1 (by rfl) ⟨895535, by rfl⟩ : syracuseStep 1194047 = 1791071) B1791071
theorem B4143167 : Blo 794341 4143167 := bstep (se 1 (by rfl) ⟨3107375, by rfl⟩ : syracuseStep 4143167 = 6214751) B6214751
theorem B997439 : Blo 794341 997439 := bstep (se 1 (by rfl) ⟨748079, by rfl⟩ : syracuseStep 997439 = 1496159) B1496159
theorem B9058553 : Blo 794341 9058553 := bstep (se 2 (by rfl) ⟨3396957, by rfl⟩ : syracuseStep 9058553 = 6793915) B6793915
theorem B1194377 : Blo 794341 1194377 := bstep (se 2 (by rfl) ⟨447891, by rfl⟩ : syracuseStep 1194377 = 895783) B895783
theorem B2865665 : Blo 794341 2865665 := bstep (se 2 (by rfl) ⟨1074624, by rfl⟩ : syracuseStep 2865665 = 2149249) B2149249
theorem B1194551 : Blo 794341 1194551 := bstep (se 1 (by rfl) ⟨895913, by rfl⟩ : syracuseStep 1194551 = 1791827) B1791827
theorem B1194875 : Blo 794341 1194875 := bstep (se 1 (by rfl) ⟨896156, by rfl⟩ : syracuseStep 1194875 = 1792313) B1792313
theorem B1915787 : Blo 794341 1915787 := bstep (se 1 (by rfl) ⟨1436840, by rfl⟩ : syracuseStep 1915787 = 2873681) B2873681
theorem B1457087 : Blo 794341 1457087 := bstep (se 1 (by rfl) ⟨1092815, by rfl⟩ : syracuseStep 1457087 = 2185631) B2185631
theorem B18398501 : Blo 794341 18398501 := bstep (se 4 (by rfl) ⟨1724859, by rfl⟩ : syracuseStep 18398501 = 3449719) B3449719
theorem B1195487 : Blo 794341 1195487 := bstep (se 1 (by rfl) ⟨896615, by rfl⟩ : syracuseStep 1195487 = 1793231) B1793231
theorem B2014895 : Blo 794341 2014895 := bstep (se 1 (by rfl) ⟨1511171, by rfl⟩ : syracuseStep 2014895 = 3022343) B3022343
theorem B2866907 : Blo 794341 2866907 := bstep (se 1 (by rfl) ⟨2150180, by rfl⟩ : syracuseStep 2866907 = 4300361) B4300361
theorem B1195739 : Blo 794341 1195739 := bstep (se 1 (by rfl) ⟨896804, by rfl⟩ : syracuseStep 1195739 = 1793609) B1793609
theorem B1196009 : Blo 794341 1196009 := bstep (se 2 (by rfl) ⟨448503, by rfl⟩ : syracuseStep 1196009 = 897007) B897007
theorem B1196201 : Blo 794341 1196201 := bstep (se 2 (by rfl) ⟨448575, by rfl⟩ : syracuseStep 1196201 = 897151) B897151
theorem B6799625 : Blo 794341 6799625 := bstep (se 2 (by rfl) ⟨2549859, by rfl⟩ : syracuseStep 6799625 = 5099719) B5099719
theorem B1196519 : Blo 794341 1196519 := bstep (se 1 (by rfl) ⟨897389, by rfl⟩ : syracuseStep 1196519 = 1794779) B1794779
theorem B3064351 : Blo 794341 3064351 := bstep (se 1 (by rfl) ⟨2298263, by rfl⟩ : syracuseStep 3064351 = 4596527) B4596527
theorem B12239423 : Blo 794341 12239423 := bstep (se 1 (by rfl) ⟨9179567, by rfl⟩ : syracuseStep 12239423 = 18359135) B18359135
theorem B1196795 : Blo 794341 1196795 := bstep (se 1 (by rfl) ⟨897596, by rfl⟩ : syracuseStep 1196795 = 1795193) B1795193
theorem B2868029 : Blo 794341 2868029 := bstep (se 3 (by rfl) ⟨537755, by rfl⟩ : syracuseStep 2868029 = 1075511) B1075511
theorem B19383245 : Blo 794341 19383245 := bstep (se 3 (by rfl) ⟨3634358, by rfl⟩ : syracuseStep 19383245 = 7268717) B7268717
theorem B12239905 : Blo 794341 12239905 := bstep (se 2 (by rfl) ⟨4589964, by rfl⟩ : syracuseStep 12239905 = 9179929) B9179929
theorem B1197239 : Blo 794341 1197239 := bstep (se 1 (by rfl) ⟨897929, by rfl⟩ : syracuseStep 1197239 = 1795859) B1795859
theorem B1197383 : Blo 794341 1197383 := bstep (se 1 (by rfl) ⟨898037, by rfl⟩ : syracuseStep 1197383 = 1796075) B1796075
theorem B4605281 : Blo 794341 4605281 := bstep (se 2 (by rfl) ⟨1726980, by rfl⟩ : syracuseStep 4605281 = 3453961) B3453961
theorem B1197479 : Blo 794341 1197479 := bstep (se 1 (by rfl) ⟨898109, by rfl⟩ : syracuseStep 1197479 = 1796219) B1796219
theorem B2017487 : Blo 794341 2017487 := bstep (se 1 (by rfl) ⟨1513115, by rfl⟩ : syracuseStep 2017487 = 3026231) B3026231
theorem B3688843 : Blo 794341 3688843 := bstep (se 1 (by rfl) ⟨2766632, by rfl⟩ : syracuseStep 3688843 = 5533265) B5533265
theorem B1788641 : Blo 794341 1788641 := bstep (se 2 (by rfl) ⟨670740, by rfl⟩ : syracuseStep 1788641 = 1341481) B1341481
theorem B3230621 : Blo 794341 3230621 := bstep (se 3 (by rfl) ⟨605741, by rfl⟩ : syracuseStep 3230621 = 1211483) B1211483
theorem B3394669 : Blo 794341 3394669 := bstep (se 3 (by rfl) ⟨636500, by rfl⟩ : syracuseStep 3394669 = 1273001) B1273001
theorem B6802937 : Blo 794341 6802937 := bstep (se 2 (by rfl) ⟨2551101, by rfl⟩ : syracuseStep 6802937 = 5102203) B5102203
theorem B3886703 : Blo 794341 3886703 := bstep (se 1 (by rfl) ⟨2915027, by rfl⟩ : syracuseStep 3886703 = 5830055) B5830055
theorem B1134415 : Blo 794341 1134415 := bstep (se 1 (by rfl) ⟨850811, by rfl⟩ : syracuseStep 1134415 = 1701623) B1701623
theorem B2019431 : Blo 794341 2019431 := bstep (se 1 (by rfl) ⟨1514573, by rfl⟩ : syracuseStep 2019431 = 3029147) B3029147
theorem B9687383 : Blo 794341 9687383 := bstep (se 1 (by rfl) ⟨7265537, by rfl⟩ : syracuseStep 9687383 = 14531075) B14531075
theorem B4084157 : Blo 794341 4084157 := bstep (se 3 (by rfl) ⟨765779, by rfl⟩ : syracuseStep 4084157 = 1531559) B1531559
theorem B2019775 : Blo 794341 2019775 := bstep (se 1 (by rfl) ⟨1514831, by rfl⟩ : syracuseStep 2019775 = 3029663) B3029663
theorem B33608371 : Blo 794341 33608371 := bstep (se 1 (by rfl) ⟨25206278, by rfl⟩ : syracuseStep 33608371 = 50412557) B50412557
theorem B1790783 : Blo 794341 1790783 := bstep (se 1 (by rfl) ⟨1343087, by rfl⟩ : syracuseStep 1790783 = 2686175) B2686175
theorem B2151305 : Blo 794341 2151305 := bstep (se 2 (by rfl) ⟨806739, by rfl⟩ : syracuseStep 2151305 = 1613479) B1613479
theorem B1135657 : Blo 794341 1135657 := bstep (se 2 (by rfl) ⟨425871, by rfl⟩ : syracuseStep 1135657 = 851743) B851743
theorem B2020423 : Blo 794341 2020423 := bstep (se 1 (by rfl) ⟨1515317, by rfl⟩ : syracuseStep 2020423 = 3030635) B3030635
theorem B16602457 : Blo 794341 16602457 := bstep (se 2 (by rfl) ⟨6225921, by rfl⟩ : syracuseStep 16602457 = 12451843) B12451843
theorem B2545145 : Blo 794341 2545145 := bstep (se 2 (by rfl) ⟨954429, by rfl⟩ : syracuseStep 2545145 = 1908859) B1908859
theorem B1792187 : Blo 794341 1792187 := bstep (se 1 (by rfl) ⟨1344140, by rfl⟩ : syracuseStep 1792187 = 2688281) B2688281
theorem B82860509 : Blo 794341 82860509 := bstep (se 3 (by rfl) ⟨15536345, by rfl⟩ : syracuseStep 82860509 = 31072691) B31072691
theorem B1792871 : Blo 794341 1792871 := bstep (se 1 (by rfl) ⟨1344653, by rfl⟩ : syracuseStep 1792871 = 2689307) B2689307
theorem B1792979 : Blo 794341 1792979 := bstep (se 1 (by rfl) ⟨1344734, by rfl⟩ : syracuseStep 1792979 = 2689469) B2689469
theorem B1793087 : Blo 794341 1793087 := bstep (se 1 (by rfl) ⟨1344815, by rfl⟩ : syracuseStep 1793087 = 2689631) B2689631
theorem B2415815 : Blo 794341 2415815 := bstep (se 1 (by rfl) ⟨1811861, by rfl⟩ : syracuseStep 2415815 = 3623723) B3623723
theorem B1793249 : Blo 794341 1793249 := bstep (se 2 (by rfl) ⟨672468, by rfl⟩ : syracuseStep 1793249 = 1344937) B1344937
theorem B1794239 : Blo 794341 1794239 := bstep (se 1 (by rfl) ⟨1345679, by rfl⟩ : syracuseStep 1794239 = 2691359) B2691359
theorem B6054587 : Blo 794341 6054587 := bstep (se 1 (by rfl) ⟨4540940, by rfl⟩ : syracuseStep 6054587 = 9081881) B9081881
theorem B1074079 : Blo 794341 1074079 := bstep (se 1 (by rfl) ⟨805559, by rfl⟩ : syracuseStep 1074079 = 1611119) B1611119
theorem B1795067 : Blo 794341 1795067 := bstep (se 1 (by rfl) ⟨1346300, by rfl⟩ : syracuseStep 1795067 = 2692601) B2692601
theorem B1795175 : Blo 794341 1795175 := bstep (se 1 (by rfl) ⟨1346381, by rfl⟩ : syracuseStep 1795175 = 2692763) B2692763
theorem B2548847 : Blo 794341 2548847 := bstep (se 1 (by rfl) ⟨1911635, by rfl⟩ : syracuseStep 2548847 = 3823271) B3823271
theorem B1795247 : Blo 794341 1795247 := bstep (se 1 (by rfl) ⟨1346435, by rfl⟩ : syracuseStep 1795247 = 2692871) B2692871
theorem B1008875 : Blo 794341 1008875 := bstep (se 1 (by rfl) ⟨756656, by rfl⟩ : syracuseStep 1008875 = 1513313) B1513313
theorem B4023917 : Blo 794341 4023917 := bstep (se 3 (by rfl) ⟨754484, by rfl⟩ : syracuseStep 4023917 = 1508969) B1508969
theorem B8152709 : Blo 794341 8152709 := bstep (se 4 (by rfl) ⟨764316, by rfl⟩ : syracuseStep 8152709 = 1528633) B1528633
theorem B6809771 : Blo 794341 6809771 := bstep (se 1 (by rfl) ⟨5107328, by rfl⟩ : syracuseStep 6809771 = 10214657) B10214657
theorem B1009999 : Blo 794341 1009999 := bstep (se 1 (by rfl) ⟨757499, by rfl⟩ : syracuseStep 1009999 = 1514999) B1514999
theorem B6056531 : Blo 794341 6056531 := bstep (se 1 (by rfl) ⟨4542398, by rfl⟩ : syracuseStep 6056531 = 9084797) B9084797
theorem B1273039 : Blo 794341 1273039 := bstep (se 1 (by rfl) ⟨954779, by rfl⟩ : syracuseStep 1273039 = 1909559) B1909559
theorem B55799563 : Blo 794341 55799563 := bstep (se 1 (by rfl) ⟨41849672, by rfl⟩ : syracuseStep 55799563 = 83699345) B83699345
theorem B1208297 : Blo 794341 1208297 := bstep (se 2 (by rfl) ⟨453111, by rfl⟩ : syracuseStep 1208297 = 906223) B906223
theorem B18346013 : Blo 794341 18346013 := bstep (se 3 (by rfl) ⟨3439877, by rfl⟩ : syracuseStep 18346013 = 6879755) B6879755
theorem B2682935 : Blo 794341 2682935 := bstep (se 1 (by rfl) ⟨2012201, by rfl⟩ : syracuseStep 2682935 = 4024403) B4024403
theorem B1437851 : Blo 794341 1437851 := bstep (se 1 (by rfl) ⟨1078388, by rfl⟩ : syracuseStep 1437851 = 2156777) B2156777
theorem B2552219 : Blo 794341 2552219 := bstep (se 1 (by rfl) ⟨1914164, by rfl⟩ : syracuseStep 2552219 = 3828329) B3828329
theorem B2552639 : Blo 794341 2552639 := bstep (se 1 (by rfl) ⟨1914479, by rfl⟩ : syracuseStep 2552639 = 3828959) B3828959
theorem B11465657 : Blo 794341 11465657 := bstep (se 2 (by rfl) ⟨4299621, by rfl⟩ : syracuseStep 11465657 = 8599243) B8599243
theorem B4027643 : Blo 794341 4027643 := bstep (se 1 (by rfl) ⟨3020732, by rfl⟩ : syracuseStep 4027643 = 6041465) B6041465
theorem B1341407 : Blo 794341 1341407 := bstep (se 1 (by rfl) ⟨1006055, by rfl⟩ : syracuseStep 1341407 = 2012111) B2012111
theorem B209025157 : Blo 794341 209025157 := bstep (se 4 (by rfl) ⟨19596108, by rfl⟩ : syracuseStep 209025157 = 39192217) B39192217
theorem B2423137 : Blo 794341 2423137 := bstep (se 2 (by rfl) ⟨908676, by rfl⟩ : syracuseStep 2423137 = 1817353) B1817353
theorem B2685419 : Blo 794341 2685419 := bstep (se 1 (by rfl) ⟨2014064, by rfl⟩ : syracuseStep 2685419 = 4028129) B4028129
theorem B4848169 : Blo 794341 4848169 := bstep (se 2 (by rfl) ⟨1818063, by rfl⟩ : syracuseStep 4848169 = 3636127) B3636127
theorem B2554679 : Blo 794341 2554679 := bstep (se 1 (by rfl) ⟨1916009, by rfl⟩ : syracuseStep 2554679 = 3832019) B3832019
theorem B5110609 : Blo 794341 5110609 := bstep (se 2 (by rfl) ⟨1916478, by rfl⟩ : syracuseStep 5110609 = 3832957) B3832957
theorem B1702939 : Blo 794341 1702939 := bstep (se 1 (by rfl) ⟨1277204, by rfl⟩ : syracuseStep 1702939 = 2554409) B2554409
theorem B1277083 : Blo 794341 1277083 := bstep (se 1 (by rfl) ⟨957812, by rfl⟩ : syracuseStep 1277083 = 1915625) B1915625
theorem B52362521 : Blo 794341 52362521 := bstep (se 2 (by rfl) ⟨19635945, by rfl⟩ : syracuseStep 52362521 = 39271891) B39271891
theorem B4030073 : Blo 794341 4030073 := bstep (se 2 (by rfl) ⟨1511277, by rfl⟩ : syracuseStep 4030073 = 3022555) B3022555
theorem B4030397 : Blo 794341 4030397 := bstep (se 3 (by rfl) ⟨755699, by rfl⟩ : syracuseStep 4030397 = 1511399) B1511399
theorem B8159615 : Blo 794341 8159615 := bstep (se 1 (by rfl) ⟨6119711, by rfl⟩ : syracuseStep 8159615 = 12239423) B12239423
theorem B3408425 : Blo 794341 3408425 := bstep (se 2 (by rfl) ⟨1278159, by rfl⟩ : syracuseStep 3408425 = 2556319) B2556319
theorem B1573663 : Blo 794341 1573663 := bstep (se 1 (by rfl) ⟨1180247, by rfl⟩ : syracuseStep 1573663 = 2360495) B2360495
theorem B2622347 : Blo 794341 2622347 := bstep (se 1 (by rfl) ⟨1966760, by rfl⟩ : syracuseStep 2622347 = 3933521) B3933521
theorem B14550353 : Blo 794341 14550353 := bstep (se 2 (by rfl) ⟨5456382, by rfl⟩ : syracuseStep 14550353 = 10912765) B10912765
theorem B16319873 : Blo 794341 16319873 := bstep (se 2 (by rfl) ⟨6119952, by rfl⟩ : syracuseStep 16319873 = 12239905) B12239905
theorem B2688443 : Blo 794341 2688443 := bstep (se 1 (by rfl) ⟨2016332, by rfl⟩ : syracuseStep 2688443 = 4032665) B4032665
theorem B1344991 : Blo 794341 1344991 := bstep (se 1 (by rfl) ⟨1008743, by rfl⟩ : syracuseStep 1344991 = 2017487) B2017487
theorem B5113327 : Blo 794341 5113327 := bstep (se 1 (by rfl) ⟨3834995, by rfl⟩ : syracuseStep 5113327 = 7669991) B7669991
theorem B2591135 : Blo 794341 2591135 := bstep (se 1 (by rfl) ⟨1943351, by rfl⟩ : syracuseStep 2591135 = 3886703) B3886703
theorem B3017195 : Blo 794341 3017195 := bstep (se 1 (by rfl) ⟨2262896, by rfl⟩ : syracuseStep 3017195 = 4525793) B4525793
theorem B1346287 : Blo 794341 1346287 := bstep (se 1 (by rfl) ⟨1009715, by rfl⟩ : syracuseStep 1346287 = 2019431) B2019431
theorem B3017513 : Blo 794341 3017513 := bstep (se 2 (by rfl) ⟨1131567, by rfl⟩ : syracuseStep 3017513 = 2263135) B2263135
theorem B6458255 : Blo 794341 6458255 := bstep (se 1 (by rfl) ⟨4843691, by rfl⟩ : syracuseStep 6458255 = 9687383) B9687383
theorem B10193849 : Blo 794341 10193849 := bstep (se 2 (by rfl) ⟨3822693, by rfl⟩ : syracuseStep 10193849 = 7645387) B7645387
theorem B2722771 : Blo 794341 2722771 := bstep (se 1 (by rfl) ⟨2042078, by rfl⟩ : syracuseStep 2722771 = 4084157) B4084157
theorem B1346665 : Blo 794341 1346665 := bstep (se 2 (by rfl) ⟨504999, by rfl⟩ : syracuseStep 1346665 = 1009999) B1009999
theorem B4918457 : Blo 794341 4918457 := bstep (se 2 (by rfl) ⟨1844421, by rfl⟩ : syracuseStep 4918457 = 3688843) B3688843
theorem B1510663 : Blo 794341 1510663 := bstep (se 1 (by rfl) ⟨1132997, by rfl⟩ : syracuseStep 1510663 = 2265995) B2265995
theorem B2690333 : Blo 794341 2690333 := bstep (se 3 (by rfl) ⟨504437, by rfl⟩ : syracuseStep 2690333 = 1008875) B1008875
theorem B4526225 : Blo 794341 4526225 := bstep (se 2 (by rfl) ⟨1697334, by rfl⟩ : syracuseStep 4526225 = 3394669) B3394669
theorem B2691575 : Blo 794341 2691575 := bstep (se 1 (by rfl) ⟨2018681, by rfl⟩ : syracuseStep 2691575 = 4037363) B4037363
theorem B1610543 : Blo 794341 1610543 := bstep (se 1 (by rfl) ⟨1207907, by rfl⟩ : syracuseStep 1610543 = 2415815) B2415815
theorem B3020111 : Blo 794341 3020111 := bstep (se 1 (by rfl) ⟨2265083, by rfl⟩ : syracuseStep 3020111 = 4530167) B4530167
theorem B2659837 : Blo 794341 2659837 := bstep (se 3 (by rfl) ⟨498719, by rfl⟩ : syracuseStep 2659837 = 997439) B997439
theorem B4036391 : Blo 794341 4036391 := bstep (se 1 (by rfl) ⟨3027293, by rfl⟩ : syracuseStep 4036391 = 6054587) B6054587
theorem B2693033 : Blo 794341 2693033 := bstep (se 2 (by rfl) ⟨1009887, by rfl⟩ : syracuseStep 2693033 = 2019775) B2019775
theorem B6789541 : Blo 794341 6789541 := bstep (se 4 (by rfl) ⟨636519, by rfl⟩ : syracuseStep 6789541 = 1273039) B1273039
theorem B7641773 : Blo 794341 7641773 := bstep (se 3 (by rfl) ⟨1432832, by rfl⟩ : syracuseStep 7641773 = 2865665) B2865665
theorem B1514209 : Blo 794341 1514209 := bstep (se 2 (by rfl) ⟨567828, by rfl⟩ : syracuseStep 1514209 = 1135657) B1135657
theorem B2693897 : Blo 794341 2693897 := bstep (se 2 (by rfl) ⟨1010211, by rfl⟩ : syracuseStep 2693897 = 2020423) B2020423
theorem B13998917 : Blo 794341 13998917 := bstep (se 4 (by rfl) ⟨1312398, by rfl⟩ : syracuseStep 13998917 = 2624797) B2624797
theorem B1383367 : Blo 794341 1383367 := bstep (se 1 (by rfl) ⟨1037525, by rfl⟩ : syracuseStep 1383367 = 2075051) B2075051
theorem B4037687 : Blo 794341 4037687 := bstep (se 1 (by rfl) ⟨3028265, by rfl⟩ : syracuseStep 4037687 = 6056531) B6056531
theorem B794363 : Blo 794341 794363 := bstep (se 1 (by rfl) ⟨595772, by rfl⟩ : syracuseStep 794363 = 1191545) B1191545
theorem B794527 : Blo 794341 794527 := bstep (se 1 (by rfl) ⟨595895, by rfl⟩ : syracuseStep 794527 = 1191791) B1191791
theorem B12230675 : Blo 794341 12230675 := bstep (se 1 (by rfl) ⟨9173006, by rfl⟩ : syracuseStep 12230675 = 18346013) B18346013
theorem B794695 : Blo 794341 794695 := bstep (se 1 (by rfl) ⟨596021, by rfl⟩ : syracuseStep 794695 = 1192043) B1192043
theorem B958567 : Blo 794341 958567 := bstep (se 1 (by rfl) ⟨718925, by rfl⟩ : syracuseStep 958567 = 1437851) B1437851
theorem B278700209 : Blo 794341 278700209 := bstep (se 2 (by rfl) ⟨104512578, by rfl⟩ : syracuseStep 278700209 = 209025157) B209025157
theorem B794983 : Blo 794341 794983 := bstep (se 1 (by rfl) ⟨596237, by rfl⟩ : syracuseStep 794983 = 1192475) B1192475
theorem B795103 : Blo 794341 795103 := bstep (se 1 (by rfl) ⟨596327, by rfl⟩ : syracuseStep 795103 = 1192655) B1192655
theorem B7643771 : Blo 794341 7643771 := bstep (se 1 (by rfl) ⟨5732828, by rfl⟩ : syracuseStep 7643771 = 11465657) B11465657
theorem B795295 : Blo 794341 795295 := bstep (se 1 (by rfl) ⟨596471, by rfl⟩ : syracuseStep 795295 = 1192943) B1192943
theorem B6464225 : Blo 794341 6464225 := bstep (se 2 (by rfl) ⟨2424084, by rfl⟩ : syracuseStep 6464225 = 4848169) B4848169
theorem B795551 : Blo 794341 795551 := bstep (se 1 (by rfl) ⟨596663, by rfl⟩ : syracuseStep 795551 = 1193327) B1193327
theorem B3023831 : Blo 794341 3023831 := bstep (se 1 (by rfl) ⟨2267873, by rfl⟩ : syracuseStep 3023831 = 4535747) B4535747
theorem B795631 : Blo 794341 795631 := bstep (se 1 (by rfl) ⟨596723, by rfl⟩ : syracuseStep 795631 = 1193447) B1193447
theorem B795751 : Blo 794341 795751 := bstep (se 1 (by rfl) ⟨596813, by rfl⟩ : syracuseStep 795751 = 1193627) B1193627
theorem B894271 : Blo 794341 894271 := bstep (se 1 (by rfl) ⟨670703, by rfl⟩ : syracuseStep 894271 = 1341407) B1341407
theorem B795975 : Blo 794341 795975 := bstep (se 1 (by rfl) ⟨596981, by rfl⟩ : syracuseStep 795975 = 1193963) B1193963
theorem B2270585 : Blo 794341 2270585 := bstep (se 2 (by rfl) ⟨851469, by rfl⟩ : syracuseStep 2270585 = 1702939) B1702939
theorem B796031 : Blo 794341 796031 := bstep (se 1 (by rfl) ⟨597023, by rfl⟩ : syracuseStep 796031 = 1194047) B1194047
theorem B2762111 : Blo 794341 2762111 := bstep (se 1 (by rfl) ⟨2071583, by rfl⟩ : syracuseStep 2762111 = 4143167) B4143167
theorem B6039035 : Blo 794341 6039035 := bstep (se 1 (by rfl) ⟨4529276, by rfl⟩ : syracuseStep 6039035 = 9058553) B9058553
theorem B796251 : Blo 794341 796251 := bstep (se 1 (by rfl) ⟨597188, by rfl⟩ : syracuseStep 796251 = 1194377) B1194377
theorem B796367 : Blo 794341 796367 := bstep (se 1 (by rfl) ⟨597275, by rfl⟩ : syracuseStep 796367 = 1194551) B1194551
theorem B796583 : Blo 794341 796583 := bstep (se 1 (by rfl) ⟨597437, by rfl⟩ : syracuseStep 796583 = 1194875) B1194875
theorem B34908347 : Blo 794341 34908347 := bstep (se 1 (by rfl) ⟨26181260, by rfl⟩ : syracuseStep 34908347 = 52362521) B52362521
theorem B12265667 : Blo 794341 12265667 := bstep (se 1 (by rfl) ⟨9199250, by rfl⟩ : syracuseStep 12265667 = 18398501) B18398501
theorem B796991 : Blo 794341 796991 := bstep (se 1 (by rfl) ⟨597743, by rfl⟩ : syracuseStep 796991 = 1195487) B1195487
theorem B1911271 : Blo 794341 1911271 := bstep (se 1 (by rfl) ⟨1433453, by rfl⟩ : syracuseStep 1911271 = 2866907) B2866907
theorem B797159 : Blo 794341 797159 := bstep (se 1 (by rfl) ⟨597869, by rfl⟩ : syracuseStep 797159 = 1195739) B1195739
theorem B3222125 : Blo 794341 3222125 := bstep (se 3 (by rfl) ⟨604148, by rfl⟩ : syracuseStep 3222125 = 1208297) B1208297
theorem B797339 : Blo 794341 797339 := bstep (se 1 (by rfl) ⟨598004, by rfl⟩ : syracuseStep 797339 = 1196009) B1196009
theorem B797467 : Blo 794341 797467 := bstep (se 1 (by rfl) ⟨598100, by rfl⟩ : syracuseStep 797467 = 1196201) B1196201
theorem B5745491 : Blo 794341 5745491 := bstep (se 1 (by rfl) ⟨4309118, by rfl⟩ : syracuseStep 5745491 = 8618237) B8618237
theorem B4533083 : Blo 794341 4533083 := bstep (se 1 (by rfl) ⟨3399812, by rfl⟩ : syracuseStep 4533083 = 6799625) B6799625
theorem B6040493 : Blo 794341 6040493 := bstep (se 3 (by rfl) ⟨1132592, by rfl⟩ : syracuseStep 6040493 = 2265185) B2265185
theorem B797679 : Blo 794341 797679 := bstep (se 1 (by rfl) ⟨598259, by rfl⟩ : syracuseStep 797679 = 1196519) B1196519
theorem B797863 : Blo 794341 797863 := bstep (se 1 (by rfl) ⟨598397, by rfl⟩ : syracuseStep 797863 = 1196795) B1196795
theorem B1912019 : Blo 794341 1912019 := bstep (se 1 (by rfl) ⟨1434014, by rfl⟩ : syracuseStep 1912019 = 2868029) B2868029
theorem B12922163 : Blo 794341 12922163 := bstep (se 1 (by rfl) ⟨9691622, by rfl⟩ : syracuseStep 12922163 = 19383245) B19383245
theorem B798159 : Blo 794341 798159 := bstep (se 1 (by rfl) ⟨598619, by rfl⟩ : syracuseStep 798159 = 1197239) B1197239
theorem B798255 : Blo 794341 798255 := bstep (se 1 (by rfl) ⟨598691, by rfl⟩ : syracuseStep 798255 = 1197383) B1197383
theorem B798319 : Blo 794341 798319 := bstep (se 1 (by rfl) ⟨598739, by rfl⟩ : syracuseStep 798319 = 1197479) B1197479
theorem B1618255 : Blo 794341 1618255 := bstep (se 1 (by rfl) ⟨1213691, by rfl⟩ : syracuseStep 1618255 = 2427383) B2427383
theorem B1192427 : Blo 794341 1192427 := bstep (se 1 (by rfl) ⟨894320, by rfl⟩ : syracuseStep 1192427 = 1788641) B1788641
theorem B1192553 : Blo 794341 1192553 := bstep (se 2 (by rfl) ⟨447207, by rfl⟩ : syracuseStep 1192553 = 894415) B894415
theorem B5747591 : Blo 794341 5747591 := bstep (se 1 (by rfl) ⟨4310693, by rfl⟩ : syracuseStep 5747591 = 8621387) B8621387
theorem B4535291 : Blo 794341 4535291 := bstep (se 1 (by rfl) ⟨3401468, by rfl⟩ : syracuseStep 4535291 = 6802937) B6802937
theorem B5092415 : Blo 794341 5092415 := bstep (se 1 (by rfl) ⟨3819311, by rfl⟩ : syracuseStep 5092415 = 7638623) B7638623
theorem B1193081 : Blo 794341 1193081 := bstep (se 2 (by rfl) ⟨447405, by rfl⟩ : syracuseStep 1193081 = 894811) B894811
theorem B12891545 : Blo 794341 12891545 := bstep (se 2 (by rfl) ⟨4834329, by rfl⟩ : syracuseStep 12891545 = 9668659) B9668659
theorem B2012809 : Blo 794341 2012809 := bstep (se 2 (by rfl) ⟨754803, by rfl⟩ : syracuseStep 2012809 = 1509607) B1509607
theorem B1193855 : Blo 794341 1193855 := bstep (se 1 (by rfl) ⟨895391, by rfl⟩ : syracuseStep 1193855 = 1790783) B1790783
theorem B7256051 : Blo 794341 7256051 := bstep (se 1 (by rfl) ⟨5442038, by rfl⟩ : syracuseStep 7256051 = 10884077) B10884077
theorem B1194473 : Blo 794341 1194473 := bstep (se 2 (by rfl) ⟨447927, by rfl⟩ : syracuseStep 1194473 = 895855) B895855
theorem B3062303 : Blo 794341 3062303 := bstep (se 1 (by rfl) ⟨2296727, by rfl⟩ : syracuseStep 3062303 = 4593455) B4593455
theorem B6044381 : Blo 794341 6044381 := bstep (se 3 (by rfl) ⟨1133321, by rfl⟩ : syracuseStep 6044381 = 2266643) B2266643
theorem B1194791 : Blo 794341 1194791 := bstep (se 1 (by rfl) ⟨896093, by rfl⟩ : syracuseStep 1194791 = 1792187) B1792187
theorem B10205999 : Blo 794341 10205999 := bstep (se 1 (by rfl) ⟨7654499, by rfl⟩ : syracuseStep 10205999 = 15308999) B15308999
theorem B21740557 : Blo 794341 21740557 := bstep (se 3 (by rfl) ⟨4076354, by rfl⟩ : syracuseStep 21740557 = 8152709) B8152709
theorem B1195247 : Blo 794341 1195247 := bstep (se 1 (by rfl) ⟨896435, by rfl⟩ : syracuseStep 1195247 = 1792871) B1792871
theorem B6470941 : Blo 794341 6470941 := bstep (se 3 (by rfl) ⟨1213301, by rfl⟩ : syracuseStep 6470941 = 2426603) B2426603
theorem B1195319 : Blo 794341 1195319 := bstep (se 1 (by rfl) ⟨896489, by rfl⟩ : syracuseStep 1195319 = 1792979) B1792979
theorem B1195391 : Blo 794341 1195391 := bstep (se 1 (by rfl) ⟨896543, by rfl⟩ : syracuseStep 1195391 = 1793087) B1793087
theorem B1195499 : Blo 794341 1195499 := bstep (se 1 (by rfl) ⟨896624, by rfl⟩ : syracuseStep 1195499 = 1793249) B1793249
theorem B74399417 : Blo 794341 74399417 := bstep (se 2 (by rfl) ⟨27899781, by rfl⟩ : syracuseStep 74399417 = 55799563) B55799563
theorem B1196159 : Blo 794341 1196159 := bstep (se 1 (by rfl) ⟨897119, by rfl⟩ : syracuseStep 1196159 = 1794239) B1794239
theorem B2015543 : Blo 794341 2015543 := bstep (se 1 (by rfl) ⟨1511657, by rfl⟩ : syracuseStep 2015543 = 3023315) B3023315
theorem B2867567 : Blo 794341 2867567 := bstep (se 1 (by rfl) ⟨2150675, by rfl⟩ : syracuseStep 2867567 = 4301351) B4301351
theorem B1196711 : Blo 794341 1196711 := bstep (se 1 (by rfl) ⟨897533, by rfl⟩ : syracuseStep 1196711 = 1795067) B1795067
theorem B1196783 : Blo 794341 1196783 := bstep (se 1 (by rfl) ⟨897587, by rfl⟩ : syracuseStep 1196783 = 1795175) B1795175
theorem B1196831 : Blo 794341 1196831 := bstep (se 1 (by rfl) ⟨897623, by rfl⟩ : syracuseStep 1196831 = 1795247) B1795247
theorem B98321201 : Blo 794341 98321201 := bstep (se 2 (by rfl) ⟨36870450, by rfl⟩ : syracuseStep 98321201 = 73740901) B73740901
theorem B44811161 : Blo 794341 44811161 := bstep (se 2 (by rfl) ⟨16804185, by rfl⟩ : syracuseStep 44811161 = 33608371) B33608371
theorem B4539847 : Blo 794341 4539847 := bstep (se 1 (by rfl) ⟨3404885, by rfl⟩ : syracuseStep 4539847 = 6809771) B6809771
theorem B2147995 : Blo 794341 2147995 := bstep (se 1 (by rfl) ⟨1610996, by rfl⟩ : syracuseStep 2147995 = 3221993) B3221993
theorem B22136609 : Blo 794341 22136609 := bstep (se 2 (by rfl) ⟨8301228, by rfl⟩ : syracuseStep 22136609 = 16602457) B16602457
theorem B2017163 : Blo 794341 2017163 := bstep (se 1 (by rfl) ⟨1512872, by rfl⟩ : syracuseStep 2017163 = 3025745) B3025745
theorem B2017183 : Blo 794341 2017183 := bstep (se 1 (by rfl) ⟨1512887, by rfl⟩ : syracuseStep 2017183 = 3025775) B3025775
theorem B3885565 : Blo 794341 3885565 := bstep (se 3 (by rfl) ⟨728543, by rfl⟩ : syracuseStep 3885565 = 1457087) B1457087
theorem B1788623 : Blo 794341 1788623 := bstep (se 1 (by rfl) ⟨1341467, by rfl⟩ : syracuseStep 1788623 = 2682935) B2682935
theorem B3230849 : Blo 794341 3230849 := bstep (se 2 (by rfl) ⟨1211568, by rfl⟩ : syracuseStep 3230849 = 2423137) B2423137
theorem B2019401 : Blo 794341 2019401 := bstep (se 2 (by rfl) ⟨757275, by rfl⟩ : syracuseStep 2019401 = 1514551) B1514551
theorem B1790279 : Blo 794341 1790279 := bstep (se 1 (by rfl) ⟨1342709, by rfl⟩ : syracuseStep 1790279 = 2685419) B2685419
theorem B6050213 : Blo 794341 6050213 := bstep (se 4 (by rfl) ⟨567207, by rfl⟩ : syracuseStep 6050213 = 1134415) B1134415
theorem B1529435 : Blo 794341 1529435 := bstep (se 1 (by rfl) ⟨1147076, by rfl⟩ : syracuseStep 1529435 = 2294153) B2294153
theorem B4085801 : Blo 794341 4085801 := bstep (se 2 (by rfl) ⟨1532175, by rfl⟩ : syracuseStep 4085801 = 3064351) B3064351
theorem B1726591 : Blo 794341 1726591 := bstep (se 1 (by rfl) ⟨1294943, by rfl⟩ : syracuseStep 1726591 = 2589887) B2589887
theorem B1792223 : Blo 794341 1792223 := bstep (se 1 (by rfl) ⟨1344167, by rfl⟩ : syracuseStep 1792223 = 2688335) B2688335
theorem B3070187 : Blo 794341 3070187 := bstep (se 1 (by rfl) ⟨2302640, by rfl⟩ : syracuseStep 3070187 = 4605281) B4605281
theorem B4545679 : Blo 794341 4545679 := bstep (se 1 (by rfl) ⟨3409259, by rfl⟩ : syracuseStep 4545679 = 6818519) B6818519
theorem B2153747 : Blo 794341 2153747 := bstep (se 1 (by rfl) ⟨1615310, by rfl⟩ : syracuseStep 2153747 = 3230621) B3230621
theorem B1007083 : Blo 794341 1007083 := bstep (se 1 (by rfl) ⟨755312, by rfl⟩ : syracuseStep 1007083 = 1510625) B1510625
theorem B6807037 : Blo 794341 6807037 := bstep (se 3 (by rfl) ⟨1276319, by rfl⟩ : syracuseStep 6807037 = 2552639) B2552639
theorem B1794203 : Blo 794341 1794203 := bstep (se 1 (by rfl) ⟨1345652, by rfl⟩ : syracuseStep 1794203 = 2691305) B2691305
theorem B4022459 : Blo 794341 4022459 := bstep (se 1 (by rfl) ⟨3016844, by rfl⟩ : syracuseStep 4022459 = 6033689) B6033689
theorem B9068759 : Blo 794341 9068759 := bstep (se 1 (by rfl) ⟨6801569, by rfl⟩ : syracuseStep 9068759 = 13603139) B13603139
theorem B1434203 : Blo 794341 1434203 := bstep (se 1 (by rfl) ⟨1075652, by rfl⟩ : syracuseStep 1434203 = 2151305) B2151305
theorem B1794887 : Blo 794341 1794887 := bstep (se 1 (by rfl) ⟨1346165, by rfl⟩ : syracuseStep 1794887 = 2692331) B2692331
theorem B1696763 : Blo 794341 1696763 := bstep (se 1 (by rfl) ⟨1272572, by rfl⟩ : syracuseStep 1696763 = 2545145) B2545145
theorem B1795535 : Blo 794341 1795535 := bstep (se 1 (by rfl) ⟨1346651, by rfl⟩ : syracuseStep 1795535 = 2693303) B2693303
theorem B55240339 : Blo 794341 55240339 := bstep (se 1 (by rfl) ⟨41430254, by rfl⟩ : syracuseStep 55240339 = 82860509) B82860509
theorem B2680937 : Blo 794341 2680937 := bstep (se 2 (by rfl) ⟨1005351, by rfl⟩ : syracuseStep 2680937 = 2010703) B2010703
theorem B5728421 : Blo 794341 5728421 := bstep (se 4 (by rfl) ⟨537039, by rfl⟩ : syracuseStep 5728421 = 1074079) B1074079
theorem B5106077 : Blo 794341 5106077 := bstep (se 3 (by rfl) ⟨957389, by rfl⟩ : syracuseStep 5106077 = 1914779) B1914779
theorem B6449951 : Blo 794341 6449951 := bstep (se 1 (by rfl) ⟨4837463, by rfl⟩ : syracuseStep 6449951 = 9674927) B9674927
theorem B1075999 : Blo 794341 1075999 := bstep (se 1 (by rfl) ⟨806999, by rfl⟩ : syracuseStep 1075999 = 1613999) B1613999
theorem B13266035 : Blo 794341 13266035 := bstep (se 1 (by rfl) ⟨9949526, by rfl⟩ : syracuseStep 13266035 = 19899053) B19899053
theorem B1699231 : Blo 794341 1699231 := bstep (se 1 (by rfl) ⟨1274423, by rfl⟩ : syracuseStep 1699231 = 2548847) B2548847
theorem B2682611 : Blo 794341 2682611 := bstep (se 1 (by rfl) ⟨2011958, by rfl⟩ : syracuseStep 2682611 = 4023917) B4023917
theorem B8155187 : Blo 794341 8155187 := bstep (se 1 (by rfl) ⟨6116390, by rfl⟩ : syracuseStep 8155187 = 12232781) B12232781
theorem B3503209 : Blo 794341 3503209 := bstep (se 2 (by rfl) ⟨1313703, by rfl⟩ : syracuseStep 3503209 = 2627407) B2627407
theorem B1340543 : Blo 794341 1340543 := bstep (se 1 (by rfl) ⟨1005407, by rfl⟩ : syracuseStep 1340543 = 2010815) B2010815
theorem B65303819 : Blo 794341 65303819 := bstep (se 1 (by rfl) ⟨48977864, by rfl⟩ : syracuseStep 65303819 = 97955729) B97955729
theorem B1701479 : Blo 794341 1701479 := bstep (se 1 (by rfl) ⟨1276109, by rfl⟩ : syracuseStep 1701479 = 2552219) B2552219
theorem B27228149 : Blo 794341 27228149 := bstep (se 5 (by rfl) ⟨1276319, by rfl⟩ : syracuseStep 27228149 = 2552639) B2552639
theorem B2685095 : Blo 794341 2685095 := bstep (se 1 (by rfl) ⟨2013821, by rfl⟩ : syracuseStep 2685095 = 4027643) B4027643
theorem B1341751 : Blo 794341 1341751 := bstep (se 1 (by rfl) ⟨1006313, by rfl⟩ : syracuseStep 1341751 = 2012627) B2012627
theorem B6814145 : Blo 794341 6814145 := bstep (se 2 (by rfl) ⟨2555304, by rfl⟩ : syracuseStep 6814145 = 5110609) B5110609
theorem B1702777 : Blo 794341 1702777 := bstep (se 2 (by rfl) ⟨638541, by rfl⟩ : syracuseStep 1702777 = 1277083) B1277083
theorem B1703119 : Blo 794341 1703119 := bstep (se 1 (by rfl) ⟨1277339, by rfl⟩ : syracuseStep 1703119 = 2554679) B2554679
theorem B1277191 : Blo 794341 1277191 := bstep (se 1 (by rfl) ⟨957893, by rfl⟩ : syracuseStep 1277191 = 1915787) B1915787
theorem B2686715 : Blo 794341 2686715 := bstep (se 1 (by rfl) ⟨2015036, by rfl⟩ : syracuseStep 2686715 = 4030073) B4030073
theorem B1343263 : Blo 794341 1343263 := bstep (se 1 (by rfl) ⟨1007447, by rfl⟩ : syracuseStep 1343263 = 2014895) B2014895
theorem B13074281 : Blo 794341 13074281 := bstep (se 2 (by rfl) ⟨4902855, by rfl⟩ : syracuseStep 13074281 = 9805711) B9805711
theorem B2686931 : Blo 794341 2686931 := bstep (se 1 (by rfl) ⟨2015198, by rfl⟩ : syracuseStep 2686931 = 4030397) B4030397
theorem B1278089 : Blo 794341 1278089 := bstep (se 2 (by rfl) ⟨479283, by rfl⟩ : syracuseStep 1278089 = 958567) B958567
theorem B1343695 : Blo 794341 1343695 := bstep (se 1 (by rfl) ⟨1007771, by rfl⟩ : syracuseStep 1343695 = 2015543) B2015543
theorem B5439743 : Blo 794341 5439743 := bstep (se 1 (by rfl) ⟨4079807, by rfl⟩ : syracuseStep 5439743 = 8159615) B8159615
theorem B9700235 : Blo 794341 9700235 := bstep (se 1 (by rfl) ⟨7275176, by rfl⟩ : syracuseStep 9700235 = 14550353) B14550353
theorem B10879915 : Blo 794341 10879915 := bstep (se 1 (by rfl) ⟨8159936, by rfl⟩ : syracuseStep 10879915 = 16319873) B16319873
theorem B2098217 : Blo 794341 2098217 := bstep (se 2 (by rfl) ⟨786831, by rfl⟩ : syracuseStep 2098217 = 1573663) B1573663
theorem B1344775 : Blo 794341 1344775 := bstep (se 1 (by rfl) ⟨1008581, by rfl⟩ : syracuseStep 1344775 = 2017163) B2017163
theorem B17237933 : Blo 794341 17237933 := bstep (se 3 (by rfl) ⟨3232112, by rfl⟩ : syracuseStep 17237933 = 6464225) B6464225
theorem B6817769 : Blo 794341 6817769 := bstep (se 2 (by rfl) ⟨2556663, by rfl⟩ : syracuseStep 6817769 = 5113327) B5113327
theorem B3278971 : Blo 794341 3278971 := bstep (se 1 (by rfl) ⟨2459228, by rfl⟩ : syracuseStep 3278971 = 4918457) B4918457
theorem B4294781 : Blo 794341 4294781 := bstep (se 3 (by rfl) ⟨805271, by rfl⟩ : syracuseStep 4294781 = 1610543) B1610543
theorem B2689577 : Blo 794341 2689577 := bstep (se 2 (by rfl) ⟨1008591, by rfl⟩ : syracuseStep 2689577 = 2017183) B2017183
theorem B1346267 : Blo 794341 1346267 := bstep (se 1 (by rfl) ⟨1009700, by rfl⟩ : syracuseStep 1346267 = 2019401) B2019401
theorem B3017483 : Blo 794341 3017483 := bstep (se 1 (by rfl) ⟨2263112, by rfl⟩ : syracuseStep 3017483 = 4526225) B4526225
theorem B4033475 : Blo 794341 4033475 := bstep (se 1 (by rfl) ⟨3025106, by rfl⟩ : syracuseStep 4033475 = 6050213) B6050213
theorem B5180753 : Blo 794341 5180753 := bstep (se 2 (by rfl) ⟨1942782, by rfl⟩ : syracuseStep 5180753 = 3885565) B3885565
theorem B1019623 : Blo 794341 1019623 := bstep (se 1 (by rfl) ⟨764717, by rfl⟩ : syracuseStep 1019623 = 1529435) B1529435
theorem B2690927 : Blo 794341 2690927 := bstep (se 1 (by rfl) ⟨2018195, by rfl⟩ : syracuseStep 2690927 = 4036391) B4036391
theorem B2723867 : Blo 794341 2723867 := bstep (se 1 (by rfl) ⟨2042900, by rfl⟩ : syracuseStep 2723867 = 4085801) B4085801
theorem B2265641 : Blo 794341 2265641 := bstep (se 2 (by rfl) ⟨849615, by rfl⟩ : syracuseStep 2265641 = 1699231) B1699231
theorem B2691791 : Blo 794341 2691791 := bstep (se 1 (by rfl) ⟨2018843, by rfl⟩ : syracuseStep 2691791 = 4037687) B4037687
theorem B185800139 : Blo 794341 185800139 := bstep (se 1 (by rfl) ⟨139350104, by rfl⟩ : syracuseStep 185800139 = 278700209) B278700209
theorem B956135 : Blo 794341 956135 := bstep (se 1 (by rfl) ⟨717101, by rfl⟩ : syracuseStep 956135 = 1434203) B1434203
theorem B1513723 : Blo 794341 1513723 := bstep (se 1 (by rfl) ⟨1135292, by rfl⟩ : syracuseStep 1513723 = 2270585) B2270585
theorem B4299967 : Blo 794341 4299967 := bstep (se 1 (by rfl) ⟨3224975, by rfl⟩ : syracuseStep 4299967 = 6449951) B6449951
theorem B3022055 : Blo 794341 3022055 := bstep (se 1 (by rfl) ⟨2266541, by rfl⟩ : syracuseStep 3022055 = 4533083) B4533083
theorem B3546449 : Blo 794341 3546449 := bstep (se 2 (by rfl) ⟨1329918, by rfl⟩ : syracuseStep 3546449 = 2659837) B2659837
theorem B37330445 : Blo 794341 37330445 := bstep (se 3 (by rfl) ⟨6999458, by rfl⟩ : syracuseStep 37330445 = 13998917) B13998917
theorem B2302121 : Blo 794341 2302121 := bstep (se 2 (by rfl) ⟨863295, by rfl⟩ : syracuseStep 2302121 = 1726591) B1726591
theorem B794951 : Blo 794341 794951 := bstep (se 1 (by rfl) ⟨596213, by rfl⟩ : syracuseStep 794951 = 1192427) B1192427
theorem B795035 : Blo 794341 795035 := bstep (se 1 (by rfl) ⟨596276, by rfl⟩ : syracuseStep 795035 = 1192553) B1192553
theorem B9052721 : Blo 794341 9052721 := bstep (se 2 (by rfl) ⟨3394770, by rfl⟩ : syracuseStep 9052721 = 6789541) B6789541
theorem B3023527 : Blo 794341 3023527 := bstep (se 1 (by rfl) ⟨2267645, by rfl⟩ : syracuseStep 3023527 = 4535291) B4535291
theorem B5743325 : Blo 794341 5743325 := bstep (se 3 (by rfl) ⟨1076873, by rfl⟩ : syracuseStep 5743325 = 2153747) B2153747
theorem B795387 : Blo 794341 795387 := bstep (se 1 (by rfl) ⟨596540, by rfl⟩ : syracuseStep 795387 = 1193081) B1193081
theorem B893695 : Blo 794341 893695 := bstep (se 1 (by rfl) ⟨670271, by rfl⟩ : syracuseStep 893695 = 1340543) B1340543
theorem B8594363 : Blo 794341 8594363 := bstep (se 1 (by rfl) ⟨6445772, by rfl⟩ : syracuseStep 8594363 = 12891545) B12891545
theorem B2270369 : Blo 794341 2270369 := bstep (se 2 (by rfl) ⟨851388, by rfl⟩ : syracuseStep 2270369 = 1702777) B1702777
theorem B795903 : Blo 794341 795903 := bstep (se 1 (by rfl) ⟨596927, by rfl⟩ : syracuseStep 795903 = 1193855) B1193855
theorem B1844489 : Blo 794341 1844489 := bstep (se 2 (by rfl) ⟨691683, by rfl⟩ : syracuseStep 1844489 = 1383367) B1383367
theorem B2270825 : Blo 794341 2270825 := bstep (se 2 (by rfl) ⟨851559, by rfl⟩ : syracuseStep 2270825 = 1703119) B1703119
theorem B796315 : Blo 794341 796315 := bstep (se 1 (by rfl) ⟨597236, by rfl⟩ : syracuseStep 796315 = 1194473) B1194473
theorem B2041535 : Blo 794341 2041535 := bstep (se 1 (by rfl) ⟨1531151, by rfl⟩ : syracuseStep 2041535 = 3062303) B3062303
theorem B8627921 : Blo 794341 8627921 := bstep (se 2 (by rfl) ⟨3235470, by rfl⟩ : syracuseStep 8627921 = 6470941) B6470941
theorem B796527 : Blo 794341 796527 := bstep (se 1 (by rfl) ⟨597395, by rfl⟩ : syracuseStep 796527 = 1194791) B1194791
theorem B796831 : Blo 794341 796831 := bstep (se 1 (by rfl) ⟨597623, by rfl⟩ : syracuseStep 796831 = 1195247) B1195247
theorem B796879 : Blo 794341 796879 := bstep (se 1 (by rfl) ⟨597659, by rfl⟩ : syracuseStep 796879 = 1195319) B1195319
theorem B796927 : Blo 794341 796927 := bstep (se 1 (by rfl) ⟨597695, by rfl⟩ : syracuseStep 796927 = 1195391) B1195391
theorem B796999 : Blo 794341 796999 := bstep (se 1 (by rfl) ⟨597749, by rfl⟩ : syracuseStep 796999 = 1195499) B1195499
theorem B797439 : Blo 794341 797439 := bstep (se 1 (by rfl) ⟨598079, by rfl⟩ : syracuseStep 797439 = 1196159) B1196159
theorem B2272283 : Blo 794341 2272283 := bstep (se 1 (by rfl) ⟨1704212, by rfl⟩ : syracuseStep 2272283 = 3408425) B3408425
theorem B797807 : Blo 794341 797807 := bstep (se 1 (by rfl) ⟨598355, by rfl⟩ : syracuseStep 797807 = 1196711) B1196711
theorem B797855 : Blo 794341 797855 := bstep (se 1 (by rfl) ⟨598391, by rfl⟩ : syracuseStep 797855 = 1196783) B1196783
theorem B797887 : Blo 794341 797887 := bstep (se 1 (by rfl) ⟨598415, by rfl⟩ : syracuseStep 797887 = 1196831) B1196831
theorem B65547467 : Blo 794341 65547467 := bstep (se 1 (by rfl) ⟨49160600, by rfl⟩ : syracuseStep 65547467 = 98321201) B98321201
theorem B1748231 : Blo 794341 1748231 := bstep (se 1 (by rfl) ⟨1311173, by rfl⟩ : syracuseStep 1748231 = 2622347) B2622347
theorem B2011463 : Blo 794341 2011463 := bstep (se 1 (by rfl) ⟨1508597, by rfl⟩ : syracuseStep 2011463 = 3017195) B3017195
theorem B1192361 : Blo 794341 1192361 := bstep (se 2 (by rfl) ⟨447135, by rfl⟩ : syracuseStep 1192361 = 894271) B894271
theorem B1192415 : Blo 794341 1192415 := bstep (se 1 (by rfl) ⟨894311, by rfl⟩ : syracuseStep 1192415 = 1788623) B1788623
theorem B2011675 : Blo 794341 2011675 := bstep (se 1 (by rfl) ⟨1508756, by rfl⟩ : syracuseStep 2011675 = 3017513) B3017513
theorem B4305503 : Blo 794341 4305503 := bstep (se 1 (by rfl) ⟨3229127, by rfl⟩ : syracuseStep 4305503 = 6458255) B6458255
theorem B6795899 : Blo 794341 6795899 := bstep (se 1 (by rfl) ⟨5096924, by rfl⟩ : syracuseStep 6795899 = 10193849) B10193849
theorem B2863993 : Blo 794341 2863993 := bstep (se 2 (by rfl) ⟨1073997, by rfl⟩ : syracuseStep 2863993 = 2147995) B2147995
theorem B1193519 : Blo 794341 1193519 := bstep (se 1 (by rfl) ⟨895139, by rfl⟩ : syracuseStep 1193519 = 1790279) B1790279
theorem B2013407 : Blo 794341 2013407 := bstep (se 1 (by rfl) ⟨1510055, by rfl⟩ : syracuseStep 2013407 = 3020111) B3020111
theorem B30587381 : Blo 794341 30587381 := bstep (se 5 (by rfl) ⟨1433783, by rfl⟩ : syracuseStep 30587381 = 2867567) B2867567
theorem B1194815 : Blo 794341 1194815 := bstep (se 1 (by rfl) ⟨896111, by rfl⟩ : syracuseStep 1194815 = 1792223) B1792223
theorem B2046791 : Blo 794341 2046791 := bstep (se 1 (by rfl) ⟨1535093, by rfl⟩ : syracuseStep 2046791 = 3070187) B3070187
theorem B2014217 : Blo 794341 2014217 := bstep (se 2 (by rfl) ⟨755331, by rfl⟩ : syracuseStep 2014217 = 1510663) B1510663
theorem B5094515 : Blo 794341 5094515 := bstep (se 1 (by rfl) ⟨3820886, by rfl⟩ : syracuseStep 5094515 = 7641773) B7641773
theorem B59030957 : Blo 794341 59030957 := bstep (se 3 (by rfl) ⟨11068304, by rfl⟩ : syracuseStep 59030957 = 22136609) B22136609
theorem B1196135 : Blo 794341 1196135 := bstep (se 1 (by rfl) ⟨897101, by rfl⟩ : syracuseStep 1196135 = 1794203) B1794203
theorem B6045839 : Blo 794341 6045839 := bstep (se 1 (by rfl) ⟨4534379, by rfl⟩ : syracuseStep 6045839 = 9068759) B9068759
theorem B5095847 : Blo 794341 5095847 := bstep (se 1 (by rfl) ⟨3821885, by rfl⟩ : syracuseStep 5095847 = 7643771) B7643771
theorem B1196591 : Blo 794341 1196591 := bstep (se 1 (by rfl) ⟨897443, by rfl⟩ : syracuseStep 1196591 = 1794887) B1794887
theorem B2015887 : Blo 794341 2015887 := bstep (se 1 (by rfl) ⟨1511915, by rfl⟩ : syracuseStep 2015887 = 3023831) B3023831
theorem B1131175 : Blo 794341 1131175 := bstep (se 1 (by rfl) ⟨848381, by rfl⟩ : syracuseStep 1131175 = 1696763) B1696763
theorem B1197023 : Blo 794341 1197023 := bstep (se 1 (by rfl) ⟨897767, by rfl⟩ : syracuseStep 1197023 = 1795535) B1795535
theorem B1787291 : Blo 794341 1787291 := bstep (se 1 (by rfl) ⟨1340468, by rfl⟩ : syracuseStep 1787291 = 2680937) B2680937
theorem B3818947 : Blo 794341 3818947 := bstep (se 1 (by rfl) ⟨2864210, by rfl⟩ : syracuseStep 3818947 = 5728421) B5728421
theorem B8177111 : Blo 794341 8177111 := bstep (se 1 (by rfl) ⟨6132833, by rfl⟩ : syracuseStep 8177111 = 12265667) B12265667
theorem B4670945 : Blo 794341 4670945 := bstep (se 2 (by rfl) ⟨1751604, by rfl⟩ : syracuseStep 4670945 = 3503209) B3503209
theorem B2148083 : Blo 794341 2148083 := bstep (se 1 (by rfl) ⟨1611062, by rfl⟩ : syracuseStep 2148083 = 3222125) B3222125
theorem B1788407 : Blo 794341 1788407 := bstep (se 1 (by rfl) ⟨1341305, by rfl⟩ : syracuseStep 1788407 = 2682611) B2682611
theorem B1789001 : Blo 794341 1789001 := bstep (se 2 (by rfl) ⟨670875, by rfl⟩ : syracuseStep 1789001 = 1341751) B1341751
theorem B5098717 : Blo 794341 5098717 := bstep (se 3 (by rfl) ⟨956009, by rfl⟩ : syracuseStep 5098717 = 1912019) B1912019
theorem B3394943 : Blo 794341 3394943 := bstep (se 1 (by rfl) ⟨2546207, by rfl⟩ : syracuseStep 3394943 = 5092415) B5092415
theorem B43535879 : Blo 794341 43535879 := bstep (se 1 (by rfl) ⟨32651909, by rfl⟩ : syracuseStep 43535879 = 65303819) B65303819
theorem B2018945 : Blo 794341 2018945 := bstep (se 2 (by rfl) ⟨757104, by rfl⟩ : syracuseStep 2018945 = 1514209) B1514209
theorem B1134319 : Blo 794341 1134319 := bstep (se 1 (by rfl) ⟨850739, by rfl⟩ : syracuseStep 1134319 = 1701479) B1701479
theorem B4837367 : Blo 794341 4837367 := bstep (se 1 (by rfl) ⟨3628025, by rfl⟩ : syracuseStep 4837367 = 7256051) B7256051
theorem B28987409 : Blo 794341 28987409 := bstep (se 2 (by rfl) ⟨10870278, by rfl⟩ : syracuseStep 28987409 = 21740557) B21740557
theorem B1790063 : Blo 794341 1790063 := bstep (se 1 (by rfl) ⟨1342547, by rfl⟩ : syracuseStep 1790063 = 2685095) B2685095
theorem B4542763 : Blo 794341 4542763 := bstep (se 1 (by rfl) ⟨3407072, by rfl⟩ : syracuseStep 4542763 = 6814145) B6814145
theorem B6803999 : Blo 794341 6803999 := bstep (se 1 (by rfl) ⟨5102999, by rfl⟩ : syracuseStep 6803999 = 10205999) B10205999
theorem B1791017 : Blo 794341 1791017 := bstep (se 2 (by rfl) ⟨671631, by rfl⟩ : syracuseStep 1791017 = 1343263) B1343263
theorem B49599611 : Blo 794341 49599611 := bstep (se 1 (by rfl) ⟨37199708, by rfl⟩ : syracuseStep 49599611 = 74399417) B74399417
theorem B1791143 : Blo 794341 1791143 := bstep (se 1 (by rfl) ⟨1343357, by rfl⟩ : syracuseStep 1791143 = 2686715) B2686715
theorem B1791287 : Blo 794341 1791287 := bstep (se 1 (by rfl) ⟨1343465, by rfl⟩ : syracuseStep 1791287 = 2686931) B2686931
theorem B29874107 : Blo 794341 29874107 := bstep (se 1 (by rfl) ⟨22405580, by rfl⟩ : syracuseStep 29874107 = 44811161) B44811161
theorem B1792295 : Blo 794341 1792295 := bstep (se 1 (by rfl) ⟨1344221, by rfl⟩ : syracuseStep 1792295 = 2688443) B2688443
theorem B1727423 : Blo 794341 1727423 := bstep (se 1 (by rfl) ⟨1295567, by rfl⟩ : syracuseStep 1727423 = 2591135) B2591135
theorem B6053129 : Blo 794341 6053129 := bstep (se 2 (by rfl) ⟨2269923, by rfl⟩ : syracuseStep 6053129 = 4539847) B4539847
theorem B1793321 : Blo 794341 1793321 := bstep (se 2 (by rfl) ⟨672495, by rfl⟩ : syracuseStep 1793321 = 1344991) B1344991
theorem B2153899 : Blo 794341 2153899 := bstep (se 1 (by rfl) ⟨1615424, by rfl⟩ : syracuseStep 2153899 = 3230849) B3230849
theorem B1793555 : Blo 794341 1793555 := bstep (se 1 (by rfl) ⟨1345166, by rfl⟩ : syracuseStep 1793555 = 2690333) B2690333
theorem B73653785 : Blo 794341 73653785 := bstep (se 2 (by rfl) ⟨27620169, by rfl⟩ : syracuseStep 73653785 = 55240339) B55240339
theorem B1794383 : Blo 794341 1794383 := bstep (se 1 (by rfl) ⟨1345787, by rfl⟩ : syracuseStep 1794383 = 2691575) B2691575
theorem B2548361 : Blo 794341 2548361 := bstep (se 2 (by rfl) ⟨955635, by rfl⟩ : syracuseStep 2548361 = 1911271) B1911271
theorem B1795049 : Blo 794341 1795049 := bstep (se 2 (by rfl) ⟨673143, by rfl⟩ : syracuseStep 1795049 = 1346287) B1346287
theorem B7365629 : Blo 794341 7365629 := bstep (se 3 (by rfl) ⟨1381055, by rfl⟩ : syracuseStep 7365629 = 2762111) B2762111
theorem B1434665 : Blo 794341 1434665 := bstep (se 2 (by rfl) ⟨537999, by rfl⟩ : syracuseStep 1434665 = 1075999) B1075999
theorem B3630361 : Blo 794341 3630361 := bstep (se 2 (by rfl) ⟨1361385, by rfl⟩ : syracuseStep 3630361 = 2722771) B2722771
theorem B1795355 : Blo 794341 1795355 := bstep (se 1 (by rfl) ⟨1346516, by rfl⟩ : syracuseStep 1795355 = 2693033) B2693033
theorem B1795553 : Blo 794341 1795553 := bstep (se 2 (by rfl) ⟨673332, by rfl⟩ : syracuseStep 1795553 = 1346665) B1346665
theorem B1795931 : Blo 794341 1795931 := bstep (se 1 (by rfl) ⟨1346948, by rfl⟩ : syracuseStep 1795931 = 2693897) B2693897
theorem B8153783 : Blo 794341 8153783 := bstep (se 1 (by rfl) ⟨6115337, by rfl⟩ : syracuseStep 8153783 = 12230675) B12230675
theorem B2681639 : Blo 794341 2681639 := bstep (se 1 (by rfl) ⟨2011229, by rfl⟩ : syracuseStep 2681639 = 4022459) B4022459
theorem B2157673 : Blo 794341 2157673 := bstep (se 2 (by rfl) ⟨809127, by rfl⟩ : syracuseStep 2157673 = 1618255) B1618255
theorem B93088925 : Blo 794341 93088925 := bstep (se 3 (by rfl) ⟨17454173, by rfl⟩ : syracuseStep 93088925 = 34908347) B34908347
theorem B4026023 : Blo 794341 4026023 := bstep (se 1 (by rfl) ⟨3019517, by rfl⟩ : syracuseStep 4026023 = 6039035) B6039035
theorem B6811685 : Blo 794341 6811685 := bstep (se 4 (by rfl) ⟨638595, by rfl⟩ : syracuseStep 6811685 = 1277191) B1277191
theorem B3404051 : Blo 794341 3404051 := bstep (se 1 (by rfl) ⟨2553038, by rfl⟩ : syracuseStep 3404051 = 5106077) B5106077
theorem B3830327 : Blo 794341 3830327 := bstep (se 1 (by rfl) ⟨2872745, by rfl⟩ : syracuseStep 3830327 = 5745491) B5745491
theorem B4026995 : Blo 794341 4026995 := bstep (se 1 (by rfl) ⟨3020246, by rfl⟩ : syracuseStep 4026995 = 6040493) B6040493
theorem B8844023 : Blo 794341 8844023 := bstep (se 1 (by rfl) ⟨6633017, by rfl⟩ : syracuseStep 8844023 = 13266035) B13266035
theorem B2683745 : Blo 794341 2683745 := bstep (se 2 (by rfl) ⟨1006404, by rfl⟩ : syracuseStep 2683745 = 2012809) B2012809
theorem B8614775 : Blo 794341 8614775 := bstep (se 1 (by rfl) ⟨6461081, by rfl⟩ : syracuseStep 8614775 = 12922163) B12922163
theorem B5436791 : Blo 794341 5436791 := bstep (se 1 (by rfl) ⟨4077593, by rfl⟩ : syracuseStep 5436791 = 8155187) B8155187
theorem B3831727 : Blo 794341 3831727 := bstep (se 1 (by rfl) ⟨2873795, by rfl⟩ : syracuseStep 3831727 = 5747591) B5747591
theorem B18152099 : Blo 794341 18152099 := bstep (se 1 (by rfl) ⟨13614074, by rfl⟩ : syracuseStep 18152099 = 27228149) B27228149
theorem B6060905 : Blo 794341 6060905 := bstep (se 2 (by rfl) ⟨2272839, by rfl⟩ : syracuseStep 6060905 = 4545679) B4545679
theorem B4029587 : Blo 794341 4029587 := bstep (se 1 (by rfl) ⟨3022190, by rfl⟩ : syracuseStep 4029587 = 6044381) B6044381
theorem B1342777 : Blo 794341 1342777 := bstep (se 2 (by rfl) ⟨503541, by rfl⟩ : syracuseStep 1342777 = 1007083) B1007083
theorem B9076049 : Blo 794341 9076049 := bstep (se 2 (by rfl) ⟨3403518, by rfl⟩ : syracuseStep 9076049 = 6807037) B6807037
theorem B8716187 : Blo 794341 8716187 := bstep (se 1 (by rfl) ⟨6537140, by rfl⟩ : syracuseStep 8716187 = 13074281) B13074281
theorem B77299757 : Blo 794341 77299757 := bstep (se 3 (by rfl) ⟨14493704, by rfl⟩ : syracuseStep 77299757 = 28987409) B28987409
theorem B852059 : Blo 794341 852059 := bstep (se 1 (by rfl) ⟨639044, by rfl⟩ : syracuseStep 852059 = 1278089) B1278089
theorem B4030559 : Blo 794341 4030559 := bstep (se 1 (by rfl) ⟨3022919, by rfl⟩ : syracuseStep 4030559 = 6045839) B6045839
theorem B2687849 : Blo 794341 2687849 := bstep (se 2 (by rfl) ⟨1007943, by rfl⟩ : syracuseStep 2687849 = 2015887) B2015887
theorem B1508233 : Blo 794341 1508233 := bstep (se 2 (by rfl) ⟨565587, by rfl⟩ : syracuseStep 1508233 = 1131175) B1131175
theorem B4031369 : Blo 794341 4031369 := bstep (se 2 (by rfl) ⟨1511763, by rfl⟩ : syracuseStep 4031369 = 3023527) B3023527
theorem B3113963 : Blo 794341 3113963 := bstep (se 1 (by rfl) ⟨2335472, by rfl⟩ : syracuseStep 3113963 = 4670945) B4670945
theorem B2688983 : Blo 794341 2688983 := bstep (se 1 (by rfl) ⟨2016737, by rfl⟩ : syracuseStep 2688983 = 4033475) B4033475
theorem B2263295 : Blo 794341 2263295 := bstep (se 1 (by rfl) ⟨1697471, by rfl⟩ : syracuseStep 2263295 = 3394943) B3394943
theorem B1345963 : Blo 794341 1345963 := bstep (se 1 (by rfl) ⟨1009472, by rfl⟩ : syracuseStep 1345963 = 2018945) B2018945
theorem B1510427 : Blo 794341 1510427 := bstep (se 1 (by rfl) ⟨1132820, by rfl⟩ : syracuseStep 1510427 = 2265641) B2265641
theorem B4918637 : Blo 794341 4918637 := bstep (se 3 (by rfl) ⟨922244, by rfl⟩ : syracuseStep 4918637 = 1844489) B1844489
theorem B33066407 : Blo 794341 33066407 := bstep (se 1 (by rfl) ⟨24799805, by rfl⟩ : syracuseStep 33066407 = 49599611) B49599611
theorem B123866759 : Blo 794341 123866759 := bstep (se 1 (by rfl) ⟨92900069, by rfl⟩ : syracuseStep 123866759 = 185800139) B185800139
theorem B5444093 : Blo 794341 5444093 := bstep (se 3 (by rfl) ⟨1020767, by rfl⟩ : syracuseStep 5444093 = 2041535) B2041535
theorem B1151615 : Blo 794341 1151615 := bstep (se 1 (by rfl) ⟨863711, by rfl⟩ : syracuseStep 1151615 = 1727423) B1727423
theorem B4035419 : Blo 794341 4035419 := bstep (se 1 (by rfl) ⟨3026564, by rfl⟩ : syracuseStep 4035419 = 6053129) B6053129
theorem B2364299 : Blo 794341 2364299 := bstep (se 1 (by rfl) ⟨1773224, by rfl⟩ : syracuseStep 2364299 = 3546449) B3546449
theorem B1512425 : Blo 794341 1512425 := bstep (se 2 (by rfl) ⟨567159, by rfl⟩ : syracuseStep 1512425 = 1134319) B1134319
theorem B79664285 : Blo 794341 79664285 := bstep (se 3 (by rfl) ⟨14937053, by rfl⟩ : syracuseStep 79664285 = 29874107) B29874107
theorem B6035147 : Blo 794341 6035147 := bstep (se 1 (by rfl) ⟨4526360, by rfl⟩ : syracuseStep 6035147 = 9052721) B9052721
theorem B956443 : Blo 794341 956443 := bstep (se 1 (by rfl) ⟨717332, by rfl⟩ : syracuseStep 956443 = 1434665) B1434665
theorem B1513579 : Blo 794341 1513579 := bstep (se 1 (by rfl) ⟨1135184, by rfl⟩ : syracuseStep 1513579 = 2270369) B2270369
theorem B1513883 : Blo 794341 1513883 := bstep (se 1 (by rfl) ⟨1135412, by rfl⟩ : syracuseStep 1513883 = 2270825) B2270825
theorem B1514855 : Blo 794341 1514855 := bstep (se 1 (by rfl) ⟨1136141, by rfl⟩ : syracuseStep 1514855 = 2272283) B2272283
theorem B2269367 : Blo 794341 2269367 := bstep (se 1 (by rfl) ⟨1702025, by rfl⟩ : syracuseStep 2269367 = 3404051) B3404051
theorem B794907 : Blo 794341 794907 := bstep (se 1 (by rfl) ⟨596180, by rfl⟩ : syracuseStep 794907 = 1192361) B1192361
theorem B794943 : Blo 794341 794943 := bstep (se 1 (by rfl) ⟨596207, by rfl⟩ : syracuseStep 794943 = 1192415) B1192415
theorem B4530599 : Blo 794341 4530599 := bstep (se 1 (by rfl) ⟨3397949, by rfl⟩ : syracuseStep 4530599 = 6795899) B6795899
theorem B5743183 : Blo 794341 5743183 := bstep (se 1 (by rfl) ⟨4307387, by rfl⟩ : syracuseStep 5743183 = 8614775) B8614775
theorem B795679 : Blo 794341 795679 := bstep (se 1 (by rfl) ⟨596759, by rfl⟩ : syracuseStep 795679 = 1193519) B1193519
theorem B20391587 : Blo 794341 20391587 := bstep (se 1 (by rfl) ⟨15293690, by rfl⟩ : syracuseStep 20391587 = 30587381) B30587381
theorem B12101399 : Blo 794341 12101399 := bstep (se 1 (by rfl) ⟨9076049, by rfl⟩ : syracuseStep 12101399 = 18152099) B18152099
theorem B796543 : Blo 794341 796543 := bstep (se 1 (by rfl) ⟨597407, by rfl⟩ : syracuseStep 796543 = 1194815) B1194815
theorem B4040603 : Blo 794341 4040603 := bstep (se 1 (by rfl) ⟨3030452, by rfl⟩ : syracuseStep 4040603 = 6060905) B6060905
theorem B5810791 : Blo 794341 5810791 := bstep (se 1 (by rfl) ⟨4358093, by rfl⟩ : syracuseStep 5810791 = 8716187) B8716187
theorem B797423 : Blo 794341 797423 := bstep (se 1 (by rfl) ⟨598067, by rfl⟩ : syracuseStep 797423 = 1196135) B1196135
theorem B74591189 : Blo 794341 74591189 := bstep (se 7 (by rfl) ⟨874115, by rfl⟩ : syracuseStep 74591189 = 1748231) B1748231
theorem B797727 : Blo 794341 797727 := bstep (se 1 (by rfl) ⟨598295, by rfl⟩ : syracuseStep 797727 = 1196591) B1196591
theorem B6466823 : Blo 794341 6466823 := bstep (se 1 (by rfl) ⟨4850117, by rfl⟩ : syracuseStep 6466823 = 9700235) B9700235
theorem B798015 : Blo 794341 798015 := bstep (se 1 (by rfl) ⟨598511, by rfl⟩ : syracuseStep 798015 = 1197023) B1197023
theorem B1191527 : Blo 794341 1191527 := bstep (se 1 (by rfl) ⟨893645, by rfl⟩ : syracuseStep 1191527 = 1787291) B1787291
theorem B5451407 : Blo 794341 5451407 := bstep (se 1 (by rfl) ⟨4088555, by rfl⟩ : syracuseStep 5451407 = 8177111) B8177111
theorem B1191593 : Blo 794341 1191593 := bstep (se 2 (by rfl) ⟨446847, by rfl⟩ : syracuseStep 1191593 = 893695) B893695
theorem B2863187 : Blo 794341 2863187 := bstep (se 1 (by rfl) ⟨2147390, by rfl⟩ : syracuseStep 2863187 = 4294781) B4294781
theorem B1192271 : Blo 794341 1192271 := bstep (se 1 (by rfl) ⟨894203, by rfl⟩ : syracuseStep 1192271 = 1788407) B1788407
theorem B897511 : Blo 794341 897511 := bstep (se 1 (by rfl) ⟨673133, by rfl⟩ : syracuseStep 897511 = 1346267) B1346267
theorem B2011655 : Blo 794341 2011655 := bstep (se 1 (by rfl) ⟨1508741, by rfl⟩ : syracuseStep 2011655 = 3017483) B3017483
theorem B5091929 : Blo 794341 5091929 := bstep (se 2 (by rfl) ⟨1909473, by rfl⟩ : syracuseStep 5091929 = 3818947) B3818947
theorem B1192667 : Blo 794341 1192667 := bstep (se 1 (by rfl) ⟨894500, by rfl⟩ : syracuseStep 1192667 = 1789001) B1789001
theorem B3453835 : Blo 794341 3453835 := bstep (se 1 (by rfl) ⟨2590376, by rfl⟩ : syracuseStep 3453835 = 5180753) B5180753
theorem B1815911 : Blo 794341 1815911 := bstep (se 1 (by rfl) ⟨1361933, by rfl⟩ : syracuseStep 1815911 = 2723867) B2723867
theorem B1193375 : Blo 794341 1193375 := bstep (se 1 (by rfl) ⟨895031, by rfl⟩ : syracuseStep 1193375 = 1790063) B1790063
theorem B4371961 : Blo 794341 4371961 := bstep (se 2 (by rfl) ⟨1639485, by rfl⟩ : syracuseStep 4371961 = 3278971) B3278971
theorem B4535999 : Blo 794341 4535999 := bstep (se 1 (by rfl) ⟨3401999, by rfl⟩ : syracuseStep 4535999 = 6803999) B6803999
theorem B1194011 : Blo 794341 1194011 := bstep (se 1 (by rfl) ⟨895508, by rfl⟩ : syracuseStep 1194011 = 1791017) B1791017
theorem B1194095 : Blo 794341 1194095 := bstep (se 1 (by rfl) ⟨895571, by rfl⟩ : syracuseStep 1194095 = 1791143) B1791143
theorem B1194191 : Blo 794341 1194191 := bstep (se 1 (by rfl) ⟨895643, by rfl⟩ : syracuseStep 1194191 = 1791287) B1791287
theorem B1194863 : Blo 794341 1194863 := bstep (se 1 (by rfl) ⟨896147, by rfl⟩ : syracuseStep 1194863 = 1792295) B1792295
theorem B6798289 : Blo 794341 6798289 := bstep (se 2 (by rfl) ⟨2549358, by rfl⟩ : syracuseStep 6798289 = 5098717) B5098717
theorem B2014703 : Blo 794341 2014703 := bstep (se 1 (by rfl) ⟨1511027, by rfl⟩ : syracuseStep 2014703 = 3022055) B3022055
theorem B1195547 : Blo 794341 1195547 := bstep (se 1 (by rfl) ⟨896660, by rfl⟩ : syracuseStep 1195547 = 1793321) B1793321
theorem B1359497 : Blo 794341 1359497 := bstep (se 2 (by rfl) ⟨509811, by rfl⟩ : syracuseStep 1359497 = 1019623) B1019623
theorem B24886963 : Blo 794341 24886963 := bstep (se 1 (by rfl) ⟨18665222, by rfl⟩ : syracuseStep 24886963 = 37330445) B37330445
theorem B1195703 : Blo 794341 1195703 := bstep (se 1 (by rfl) ⟨896777, by rfl⟩ : syracuseStep 1195703 = 1793555) B1793555
theorem B49102523 : Blo 794341 49102523 := bstep (se 1 (by rfl) ⟨36826892, by rfl⟩ : syracuseStep 49102523 = 73653785) B73653785
theorem B1196255 : Blo 794341 1196255 := bstep (se 1 (by rfl) ⟨897191, by rfl⟩ : syracuseStep 1196255 = 1794383) B1794383
theorem B1196699 : Blo 794341 1196699 := bstep (se 1 (by rfl) ⟨897524, by rfl⟩ : syracuseStep 1196699 = 1795049) B1795049
theorem B1196903 : Blo 794341 1196903 := bstep (se 1 (by rfl) ⟨897677, by rfl⟩ : syracuseStep 1196903 = 1795355) B1795355
theorem B1197035 : Blo 794341 1197035 := bstep (se 1 (by rfl) ⟨897776, by rfl⟩ : syracuseStep 1197035 = 1795553) B1795553
theorem B5751947 : Blo 794341 5751947 := bstep (se 1 (by rfl) ⟨4313960, by rfl⟩ : syracuseStep 5751947 = 8627921) B8627921
theorem B3818657 : Blo 794341 3818657 := bstep (se 2 (by rfl) ⟨1431996, by rfl⟩ : syracuseStep 3818657 = 2863993) B2863993
theorem B1197287 : Blo 794341 1197287 := bstep (se 1 (by rfl) ⟨897965, by rfl⟩ : syracuseStep 1197287 = 1795931) B1795931
theorem B1787759 : Blo 794341 1787759 := bstep (se 1 (by rfl) ⟨1340819, by rfl⟩ : syracuseStep 1787759 = 2681639) B2681639
theorem B43698311 : Blo 794341 43698311 := bstep (se 1 (by rfl) ⟨32773733, by rfl⟩ : syracuseStep 43698311 = 65547467) B65547467
theorem B4541123 : Blo 794341 4541123 := bstep (se 1 (by rfl) ⟨3405842, by rfl⟩ : syracuseStep 4541123 = 6811685) B6811685
theorem B2018297 : Blo 794341 2018297 := bstep (se 2 (by rfl) ⟨756861, by rfl⟩ : syracuseStep 2018297 = 1513723) B1513723
theorem B2870335 : Blo 794341 2870335 := bstep (se 1 (by rfl) ⟨2152751, by rfl⟩ : syracuseStep 2870335 = 4305503) B4305503
theorem B1789163 : Blo 794341 1789163 := bstep (se 1 (by rfl) ⟨1341872, by rfl⟩ : syracuseStep 1789163 = 2683745) B2683745
theorem B3624527 : Blo 794341 3624527 := bstep (se 1 (by rfl) ⟨2718395, by rfl⟩ : syracuseStep 3624527 = 5436791) B5436791
theorem B1790369 : Blo 794341 1790369 := bstep (se 2 (by rfl) ⟨671388, by rfl⟩ : syracuseStep 1790369 = 1342777) B1342777
theorem B1364527 : Blo 794341 1364527 := bstep (se 1 (by rfl) ⟨1023395, by rfl⟩ : syracuseStep 1364527 = 2046791) B2046791
theorem B2871865 : Blo 794341 2871865 := bstep (se 2 (by rfl) ⟨1076949, by rfl⟩ : syracuseStep 2871865 = 2153899) B2153899
theorem B3396343 : Blo 794341 3396343 := bstep (se 1 (by rfl) ⟨2547257, by rfl⟩ : syracuseStep 3396343 = 5094515) B5094515
theorem B6050699 : Blo 794341 6050699 := bstep (se 1 (by rfl) ⟨4538024, by rfl⟩ : syracuseStep 6050699 = 9076049) B9076049
theorem B12899645 : Blo 794341 12899645 := bstep (se 3 (by rfl) ⟨2418683, by rfl⟩ : syracuseStep 12899645 = 4837367) B4837367
theorem B3626495 : Blo 794341 3626495 := bstep (se 1 (by rfl) ⟨2719871, by rfl⟩ : syracuseStep 3626495 = 5439743) B5439743
theorem B1791593 : Blo 794341 1791593 := bstep (se 2 (by rfl) ⟨671847, by rfl⟩ : syracuseStep 1791593 = 1343695) B1343695
theorem B3397231 : Blo 794341 3397231 := bstep (se 1 (by rfl) ⟨2547923, by rfl⟩ : syracuseStep 3397231 = 5095847) B5095847
theorem B1398811 : Blo 794341 1398811 := bstep (se 1 (by rfl) ⟨1049108, by rfl⟩ : syracuseStep 1398811 = 2098217) B2098217
theorem B1432055 : Blo 794341 1432055 := bstep (se 1 (by rfl) ⟨1074041, by rfl⟩ : syracuseStep 1432055 = 2148083) B2148083
theorem B14506553 : Blo 794341 14506553 := bstep (se 2 (by rfl) ⟨5439957, by rfl⟩ : syracuseStep 14506553 = 10879915) B10879915
theorem B11491955 : Blo 794341 11491955 := bstep (se 1 (by rfl) ⟨8618966, by rfl⟩ : syracuseStep 11491955 = 17237933) B17237933
theorem B4545179 : Blo 794341 4545179 := bstep (se 1 (by rfl) ⟨3408884, by rfl⟩ : syracuseStep 4545179 = 6817769) B6817769
theorem B1793033 : Blo 794341 1793033 := bstep (se 2 (by rfl) ⟨672387, by rfl⟩ : syracuseStep 1793033 = 1344775) B1344775
theorem B1793051 : Blo 794341 1793051 := bstep (se 1 (by rfl) ⟨1344788, by rfl⟩ : syracuseStep 1793051 = 2689577) B2689577
theorem B4840481 : Blo 794341 4840481 := bstep (se 2 (by rfl) ⟨1815180, by rfl⟩ : syracuseStep 4840481 = 3630361) B3630361
theorem B23584061 : Blo 794341 23584061 := bstep (se 3 (by rfl) ⟨4422011, by rfl⟩ : syracuseStep 23584061 = 8844023) B8844023
theorem B29023919 : Blo 794341 29023919 := bstep (se 1 (by rfl) ⟨21767939, by rfl⟩ : syracuseStep 29023919 = 43535879) B43535879
theorem B1793951 : Blo 794341 1793951 := bstep (se 1 (by rfl) ⟨1345463, by rfl⟩ : syracuseStep 1793951 = 2690927) B2690927
theorem B1794527 : Blo 794341 1794527 := bstep (se 1 (by rfl) ⟨1345895, by rfl⟩ : syracuseStep 1794527 = 2691791) B2691791
theorem B2876897 : Blo 794341 2876897 := bstep (se 2 (by rfl) ⟨1078836, by rfl⟩ : syracuseStep 2876897 = 2157673) B2157673
theorem B2549693 : Blo 794341 2549693 := bstep (se 3 (by rfl) ⟨478067, by rfl⟩ : syracuseStep 2549693 = 956135) B956135
theorem B1534747 : Blo 794341 1534747 := bstep (se 1 (by rfl) ⟨1151060, by rfl⟩ : syracuseStep 1534747 = 2302121) B2302121
theorem B6057017 : Blo 794341 6057017 := bstep (se 2 (by rfl) ⟨2271381, by rfl⟩ : syracuseStep 6057017 = 4542763) B4542763
theorem B1698907 : Blo 794341 1698907 := bstep (se 1 (by rfl) ⟨1274180, by rfl⟩ : syracuseStep 1698907 = 2548361) B2548361
theorem B3828883 : Blo 794341 3828883 := bstep (se 1 (by rfl) ⟨2871662, by rfl⟩ : syracuseStep 3828883 = 5743325) B5743325
theorem B5729575 : Blo 794341 5729575 := bstep (se 1 (by rfl) ⟨4297181, by rfl⟩ : syracuseStep 5729575 = 8594363) B8594363
theorem B4910419 : Blo 794341 4910419 := bstep (se 1 (by rfl) ⟨3682814, by rfl⟩ : syracuseStep 4910419 = 7365629) B7365629
theorem B2682233 : Blo 794341 2682233 := bstep (se 2 (by rfl) ⟨1005837, by rfl⟩ : syracuseStep 2682233 = 2011675) B2011675
theorem B5435855 : Blo 794341 5435855 := bstep (se 1 (by rfl) ⟨4076891, by rfl⟩ : syracuseStep 5435855 = 8153783) B8153783
theorem B62059283 : Blo 794341 62059283 := bstep (se 1 (by rfl) ⟨46544462, by rfl⟩ : syracuseStep 62059283 = 93088925) B93088925
theorem B2684015 : Blo 794341 2684015 := bstep (se 1 (by rfl) ⟨2013011, by rfl⟩ : syracuseStep 2684015 = 4026023) B4026023
theorem B5108969 : Blo 794341 5108969 := bstep (se 2 (by rfl) ⟨1915863, by rfl⟩ : syracuseStep 5108969 = 3831727) B3831727
theorem B1340975 : Blo 794341 1340975 := bstep (se 1 (by rfl) ⟨1005731, by rfl⟩ : syracuseStep 1340975 = 2011463) B2011463
theorem B2553551 : Blo 794341 2553551 := bstep (se 1 (by rfl) ⟨1915163, by rfl⟩ : syracuseStep 2553551 = 3830327) B3830327
theorem B2684663 : Blo 794341 2684663 := bstep (se 1 (by rfl) ⟨2013497, by rfl⟩ : syracuseStep 2684663 = 4026995) B4026995
theorem B1342271 : Blo 794341 1342271 := bstep (se 1 (by rfl) ⟨1006703, by rfl⟩ : syracuseStep 1342271 = 2013407) B2013407
theorem B5733289 : Blo 794341 5733289 := bstep (se 2 (by rfl) ⟨2149983, by rfl⟩ : syracuseStep 5733289 = 4299967) B4299967
theorem B1342811 : Blo 794341 1342811 := bstep (se 1 (by rfl) ⟨1007108, by rfl⟩ : syracuseStep 1342811 = 2014217) B2014217
theorem B2686391 : Blo 794341 2686391 := bstep (se 1 (by rfl) ⟨2014793, by rfl⟩ : syracuseStep 2686391 = 4029587) B4029587
theorem B39353971 : Blo 794341 39353971 := bstep (se 1 (by rfl) ⟨29515478, by rfl⟩ : syracuseStep 39353971 = 59030957) B59030957
theorem B2687039 : Blo 794341 2687039 := bstep (se 1 (by rfl) ⟨2015279, by rfl⟩ : syracuseStep 2687039 = 4030559) B4030559
theorem B2687579 : Blo 794341 2687579 := bstep (se 1 (by rfl) ⟨2015684, by rfl⟩ : syracuseStep 2687579 = 4031369) B4031369
theorem B3834631 : Blo 794341 3834631 := bstep (se 1 (by rfl) ⟨2875973, by rfl⟩ : syracuseStep 3834631 = 5751947) B5751947
theorem B29132207 : Blo 794341 29132207 := bstep (se 1 (by rfl) ⟨21849155, by rfl⟩ : syracuseStep 29132207 = 43698311) B43698311
theorem B1508863 : Blo 794341 1508863 := bstep (se 1 (by rfl) ⟨1131647, by rfl⟩ : syracuseStep 1508863 = 2263295) B2263295
theorem B1345531 : Blo 794341 1345531 := bstep (se 1 (by rfl) ⟨1009148, by rfl⟩ : syracuseStep 1345531 = 2018297) B2018297
theorem B3279091 : Blo 794341 3279091 := bstep (se 1 (by rfl) ⟨2459318, by rfl⟩ : syracuseStep 3279091 = 4918637) B4918637
theorem B82577839 : Blo 794341 82577839 := bstep (se 1 (by rfl) ⟨61933379, by rfl⟩ : syracuseStep 82577839 = 123866759) B123866759
theorem B2690279 : Blo 794341 2690279 := bstep (se 1 (by rfl) ⟨2017709, by rfl⟩ : syracuseStep 2690279 = 4035419) B4035419
theorem B4033799 : Blo 794341 4033799 := bstep (se 1 (by rfl) ⟨3025349, by rfl⟩ : syracuseStep 4033799 = 6050699) B6050699
theorem B1576199 : Blo 794341 1576199 := bstep (se 1 (by rfl) ⟨1182149, by rfl⟩ : syracuseStep 1576199 = 2364299) B2364299
theorem B2265209 : Blo 794341 2265209 := bstep (se 2 (by rfl) ⟨849453, by rfl⟩ : syracuseStep 2265209 = 1698907) B1698907
theorem B954703 : Blo 794341 954703 := bstep (se 1 (by rfl) ⟨716027, by rfl⟩ : syracuseStep 954703 = 1432055) B1432055
theorem B9671035 : Blo 794341 9671035 := bstep (se 1 (by rfl) ⟨7253276, by rfl⟩ : syracuseStep 9671035 = 14506553) B14506553
theorem B7639433 : Blo 794341 7639433 := bstep (se 2 (by rfl) ⟨2864787, by rfl⟩ : syracuseStep 7639433 = 5729575) B5729575
theorem B1512911 : Blo 794341 1512911 := bstep (se 1 (by rfl) ⟨1134683, by rfl⟩ : syracuseStep 1512911 = 2269367) B2269367
theorem B3020399 : Blo 794341 3020399 := bstep (se 1 (by rfl) ⟨2265299, by rfl⟩ : syracuseStep 3020399 = 4530599) B4530599
theorem B15308453 : Blo 794341 15308453 := bstep (se 4 (by rfl) ⟨1435167, by rfl⟩ : syracuseStep 15308453 = 2870335) B2870335
theorem B4528457 : Blo 794341 4528457 := bstep (se 2 (by rfl) ⟨1698171, by rfl⟩ : syracuseStep 4528457 = 3396343) B3396343
theorem B8067599 : Blo 794341 8067599 := bstep (se 1 (by rfl) ⟨6050699, by rfl⟩ : syracuseStep 8067599 = 12101399) B12101399
theorem B2693735 : Blo 794341 2693735 := bstep (se 1 (by rfl) ⟨2020301, by rfl⟩ : syracuseStep 2693735 = 4040603) B4040603
theorem B4038011 : Blo 794341 4038011 := bstep (se 1 (by rfl) ⟨3028508, by rfl⟩ : syracuseStep 4038011 = 6057017) B6057017
theorem B4529641 : Blo 794341 4529641 := bstep (se 2 (by rfl) ⟨1698615, by rfl⟩ : syracuseStep 4529641 = 3397231) B3397231
theorem B794351 : Blo 794341 794351 := bstep (se 1 (by rfl) ⟨595763, by rfl⟩ : syracuseStep 794351 = 1191527) B1191527
theorem B794395 : Blo 794341 794395 := bstep (se 1 (by rfl) ⟨595796, by rfl⟩ : syracuseStep 794395 = 1191593) B1191593
theorem B1908791 : Blo 794341 1908791 := bstep (se 1 (by rfl) ⟨1431593, by rfl⟩ : syracuseStep 1908791 = 2863187) B2863187
theorem B794847 : Blo 794341 794847 := bstep (se 1 (by rfl) ⟨596135, by rfl⟩ : syracuseStep 794847 = 1192271) B1192271
theorem B795111 : Blo 794341 795111 := bstep (se 1 (by rfl) ⟨596333, by rfl⟩ : syracuseStep 795111 = 1192667) B1192667
theorem B62890829 : Blo 794341 62890829 := bstep (se 3 (by rfl) ⟨11792030, by rfl⟩ : syracuseStep 62890829 = 23584061) B23584061
theorem B795583 : Blo 794341 795583 := bstep (se 1 (by rfl) ⟨596687, by rfl⟩ : syracuseStep 795583 = 1193375) B1193375
theorem B893983 : Blo 794341 893983 := bstep (se 1 (by rfl) ⟨670487, by rfl⟩ : syracuseStep 893983 = 1340975) B1340975
theorem B3023999 : Blo 794341 3023999 := bstep (se 1 (by rfl) ⟨2267999, by rfl⟩ : syracuseStep 3023999 = 4535999) B4535999
theorem B7644385 : Blo 794341 7644385 := bstep (se 2 (by rfl) ⟨2866644, by rfl⟩ : syracuseStep 7644385 = 5733289) B5733289
theorem B796007 : Blo 794341 796007 := bstep (se 1 (by rfl) ⟨597005, by rfl⟩ : syracuseStep 796007 = 1194011) B1194011
theorem B796063 : Blo 794341 796063 := bstep (se 1 (by rfl) ⟨597047, by rfl⟩ : syracuseStep 796063 = 1194095) B1194095
theorem B796127 : Blo 794341 796127 := bstep (se 1 (by rfl) ⟨597095, by rfl⟩ : syracuseStep 796127 = 1194191) B1194191
theorem B894847 : Blo 794341 894847 := bstep (se 1 (by rfl) ⟨671135, by rfl⟩ : syracuseStep 894847 = 1342271) B1342271
theorem B796575 : Blo 794341 796575 := bstep (se 1 (by rfl) ⟨597431, by rfl⟩ : syracuseStep 796575 = 1194863) B1194863
theorem B52471961 : Blo 794341 52471961 := bstep (se 2 (by rfl) ⟨19676985, by rfl⟩ : syracuseStep 52471961 = 39353971) B39353971
theorem B895207 : Blo 794341 895207 := bstep (se 1 (by rfl) ⟨671405, by rfl⟩ : syracuseStep 895207 = 1342811) B1342811
theorem B797031 : Blo 794341 797031 := bstep (se 1 (by rfl) ⟨597773, by rfl⟩ : syracuseStep 797031 = 1195547) B1195547
theorem B797135 : Blo 794341 797135 := bstep (se 1 (by rfl) ⟨597851, by rfl⟩ : syracuseStep 797135 = 1195703) B1195703
theorem B797503 : Blo 794341 797503 := bstep (se 1 (by rfl) ⟨598127, by rfl⟩ : syracuseStep 797503 = 1196255) B1196255
theorem B2272157 : Blo 794341 2272157 := bstep (se 3 (by rfl) ⟨426029, by rfl⟩ : syracuseStep 2272157 = 852059) B852059
theorem B797799 : Blo 794341 797799 := bstep (se 1 (by rfl) ⟨598349, by rfl⟩ : syracuseStep 797799 = 1196699) B1196699
theorem B797935 : Blo 794341 797935 := bstep (se 1 (by rfl) ⟨598451, by rfl⟩ : syracuseStep 797935 = 1196903) B1196903
theorem B798023 : Blo 794341 798023 := bstep (se 1 (by rfl) ⟨598517, by rfl⟩ : syracuseStep 798023 = 1197035) B1197035
theorem B2075975 : Blo 794341 2075975 := bstep (se 1 (by rfl) ⟨1556981, by rfl⟩ : syracuseStep 2075975 = 3113963) B3113963
theorem B798191 : Blo 794341 798191 := bstep (se 1 (by rfl) ⟨598643, by rfl⟩ : syracuseStep 798191 = 1197287) B1197287
theorem B2010977 : Blo 794341 2010977 := bstep (se 2 (by rfl) ⟨754116, by rfl⟩ : syracuseStep 2010977 = 1508233) B1508233
theorem B1191839 : Blo 794341 1191839 := bstep (se 1 (by rfl) ⟨893879, by rfl⟩ : syracuseStep 1191839 = 1787759) B1787759
theorem B3027415 : Blo 794341 3027415 := bstep (se 1 (by rfl) ⟨2270561, by rfl⟩ : syracuseStep 3027415 = 4541123) B4541123
theorem B1192775 : Blo 794341 1192775 := bstep (se 1 (by rfl) ⟨894581, by rfl⟩ : syracuseStep 1192775 = 1789163) B1789163
theorem B1193579 : Blo 794341 1193579 := bstep (se 1 (by rfl) ⟨895184, by rfl⟩ : syracuseStep 1193579 = 1790369) B1790369
theorem B7747721 : Blo 794341 7747721 := bstep (se 2 (by rfl) ⟨2905395, by rfl⟩ : syracuseStep 7747721 = 5810791) B5810791
theorem B8599763 : Blo 794341 8599763 := bstep (se 1 (by rfl) ⟨6449822, by rfl⟩ : syracuseStep 8599763 = 12899645) B12899645
theorem B2046329 : Blo 794341 2046329 := bstep (se 2 (by rfl) ⟨767373, by rfl⟩ : syracuseStep 2046329 = 1534747) B1534747
theorem B1194395 : Blo 794341 1194395 := bstep (se 1 (by rfl) ⟨895796, by rfl⟩ : syracuseStep 1194395 = 1791593) B1791593
theorem B3030119 : Blo 794341 3030119 := bstep (se 1 (by rfl) ⟨2272589, by rfl⟩ : syracuseStep 3030119 = 4545179) B4545179
theorem B1195355 : Blo 794341 1195355 := bstep (se 1 (by rfl) ⟨896516, by rfl⟩ : syracuseStep 1195355 = 1793033) B1793033
theorem B1195367 : Blo 794341 1195367 := bstep (se 1 (by rfl) ⟨896525, by rfl⟩ : syracuseStep 1195367 = 1793051) B1793051
theorem B3226987 : Blo 794341 3226987 := bstep (se 1 (by rfl) ⟨2420240, by rfl⟩ : syracuseStep 3226987 = 4840481) B4840481
theorem B19349279 : Blo 794341 19349279 := bstep (se 1 (by rfl) ⟨14511959, by rfl⟩ : syracuseStep 19349279 = 29023919) B29023919
theorem B1195967 : Blo 794341 1195967 := bstep (se 1 (by rfl) ⟨896975, by rfl⟩ : syracuseStep 1195967 = 1793951) B1793951
theorem B1196351 : Blo 794341 1196351 := bstep (se 1 (by rfl) ⟨897263, by rfl⟩ : syracuseStep 1196351 = 1794527) B1794527
theorem B1196681 : Blo 794341 1196681 := bstep (se 2 (by rfl) ⟨448755, by rfl⟩ : syracuseStep 1196681 = 897511) B897511
theorem B1819369 : Blo 794341 1819369 := bstep (se 2 (by rfl) ⟨682263, by rfl⟩ : syracuseStep 1819369 = 1364527) B1364527
theorem B1917931 : Blo 794341 1917931 := bstep (se 1 (by rfl) ⟨1438448, by rfl⟩ : syracuseStep 1917931 = 2876897) B2876897
theorem B4605113 : Blo 794341 4605113 := bstep (se 2 (by rfl) ⟨1726917, by rfl⟩ : syracuseStep 4605113 = 3453835) B3453835
theorem B49727459 : Blo 794341 49727459 := bstep (se 1 (by rfl) ⟨37295594, by rfl⟩ : syracuseStep 49727459 = 74591189) B74591189
theorem B4311215 : Blo 794341 4311215 := bstep (se 1 (by rfl) ⟨3233411, by rfl⟩ : syracuseStep 4311215 = 6466823) B6466823
theorem B1788155 : Blo 794341 1788155 := bstep (se 1 (by rfl) ⟨1341116, by rfl⟩ : syracuseStep 1788155 = 2682233) B2682233
theorem B2018105 : Blo 794341 2018105 := bstep (se 2 (by rfl) ⟨756789, by rfl⟩ : syracuseStep 2018105 = 1513579) B1513579
theorem B3623903 : Blo 794341 3623903 := bstep (se 1 (by rfl) ⟨2717927, by rfl⟩ : syracuseStep 3623903 = 5435855) B5435855
theorem B3394619 : Blo 794341 3394619 := bstep (se 1 (by rfl) ⟨2545964, by rfl⟩ : syracuseStep 3394619 = 5091929) B5091929
theorem B41372855 : Blo 794341 41372855 := bstep (se 1 (by rfl) ⟨31029641, by rfl⟩ : syracuseStep 41372855 = 62059283) B62059283
theorem B1789343 : Blo 794341 1789343 := bstep (se 1 (by rfl) ⟨1342007, by rfl⟩ : syracuseStep 1789343 = 2684015) B2684015
theorem B1789775 : Blo 794341 1789775 := bstep (se 1 (by rfl) ⟨1342331, by rfl⟩ : syracuseStep 1789775 = 2684663) B2684663
theorem B9064385 : Blo 794341 9064385 := bstep (se 2 (by rfl) ⟨3399144, by rfl⟩ : syracuseStep 9064385 = 6798289) B6798289
theorem B3625325 : Blo 794341 3625325 := bstep (se 3 (by rfl) ⟨679748, by rfl⟩ : syracuseStep 3625325 = 1359497) B1359497
theorem B33182617 : Blo 794341 33182617 := bstep (se 2 (by rfl) ⟨12443481, by rfl⟩ : syracuseStep 33182617 = 24886963) B24886963
theorem B1790927 : Blo 794341 1790927 := bstep (se 1 (by rfl) ⟨1343195, by rfl⟩ : syracuseStep 1790927 = 2686391) B2686391
theorem B51533171 : Blo 794341 51533171 := bstep (se 1 (by rfl) ⟨38649878, by rfl⟩ : syracuseStep 51533171 = 77299757) B77299757
theorem B1791899 : Blo 794341 1791899 := bstep (se 1 (by rfl) ⟨1343924, by rfl⟩ : syracuseStep 1791899 = 2687849) B2687849
theorem B7657577 : Blo 794341 7657577 := bstep (se 2 (by rfl) ⟨2871591, by rfl⟩ : syracuseStep 7657577 = 5743183) B5743183
theorem B2545771 : Blo 794341 2545771 := bstep (se 1 (by rfl) ⟨1909328, by rfl⟩ : syracuseStep 2545771 = 3818657) B3818657
theorem B1792655 : Blo 794341 1792655 := bstep (se 1 (by rfl) ⟨1344491, by rfl⟩ : syracuseStep 1792655 = 2688983) B2688983
theorem B3070973 : Blo 794341 3070973 := bstep (se 3 (by rfl) ⟨575807, by rfl⟩ : syracuseStep 3070973 = 1151615) B1151615
theorem B2416351 : Blo 794341 2416351 := bstep (se 1 (by rfl) ⟨1812263, by rfl⟩ : syracuseStep 2416351 = 3624527) B3624527
theorem B3629395 : Blo 794341 3629395 := bstep (se 1 (by rfl) ⟨2722046, by rfl⟩ : syracuseStep 3629395 = 5444093) B5444093
theorem B1794617 : Blo 794341 1794617 := bstep (se 2 (by rfl) ⟨672981, by rfl⟩ : syracuseStep 1794617 = 1345963) B1345963
theorem B1008283 : Blo 794341 1008283 := bstep (se 1 (by rfl) ⟨756212, by rfl⟩ : syracuseStep 1008283 = 1512425) B1512425
theorem B53109523 : Blo 794341 53109523 := bstep (se 1 (by rfl) ⟨39832142, by rfl⟩ : syracuseStep 53109523 = 79664285) B79664285
theorem B2417663 : Blo 794341 2417663 := bstep (se 1 (by rfl) ⟨1813247, by rfl⟩ : syracuseStep 2417663 = 3626495) B3626495
theorem B4023431 : Blo 794341 4023431 := bstep (se 1 (by rfl) ⟨3017573, by rfl⟩ : syracuseStep 4023431 = 6035147) B6035147
theorem B5105177 : Blo 794341 5105177 := bstep (se 2 (by rfl) ⟨1914441, by rfl⟩ : syracuseStep 5105177 = 3828883) B3828883
theorem B1009255 : Blo 794341 1009255 := bstep (se 1 (by rfl) ⟨756941, by rfl⟩ : syracuseStep 1009255 = 1513883) B1513883
theorem B7661303 : Blo 794341 7661303 := bstep (se 1 (by rfl) ⟨5745977, by rfl⟩ : syracuseStep 7661303 = 11491955) B11491955
theorem B6547225 : Blo 794341 6547225 := bstep (se 2 (by rfl) ⟨2455209, by rfl⟩ : syracuseStep 6547225 = 4910419) B4910419
theorem B1009903 : Blo 794341 1009903 := bstep (se 1 (by rfl) ⟨757427, by rfl⟩ : syracuseStep 1009903 = 1514855) B1514855
theorem B3829153 : Blo 794341 3829153 := bstep (se 2 (by rfl) ⟨1435932, by rfl⟩ : syracuseStep 3829153 = 2871865) B2871865
theorem B13594391 : Blo 794341 13594391 := bstep (se 1 (by rfl) ⟨10195793, by rfl⟩ : syracuseStep 13594391 = 20391587) B20391587
theorem B1699795 : Blo 794341 1699795 := bstep (se 1 (by rfl) ⟨1274846, by rfl⟩ : syracuseStep 1699795 = 2549693) B2549693
theorem B5829281 : Blo 794341 5829281 := bstep (se 2 (by rfl) ⟨2185980, by rfl⟩ : syracuseStep 5829281 = 4371961) B4371961
theorem B3634271 : Blo 794341 3634271 := bstep (se 1 (by rfl) ⟨2725703, by rfl⟩ : syracuseStep 3634271 = 5451407) B5451407
theorem B1865081 : Blo 794341 1865081 := bstep (se 2 (by rfl) ⟨699405, by rfl⟩ : syracuseStep 1865081 = 1398811) B1398811
theorem B1275257 : Blo 794341 1275257 := bstep (se 2 (by rfl) ⟨478221, by rfl⟩ : syracuseStep 1275257 = 956443) B956443
theorem B4027805 : Blo 794341 4027805 := bstep (se 3 (by rfl) ⟨755213, by rfl⟩ : syracuseStep 4027805 = 1510427) B1510427
theorem B1341103 : Blo 794341 1341103 := bstep (se 1 (by rfl) ⟨1005827, by rfl⟩ : syracuseStep 1341103 = 2011655) B2011655
theorem B3405979 : Blo 794341 3405979 := bstep (se 1 (by rfl) ⟨2554484, by rfl⟩ : syracuseStep 3405979 = 5108969) B5108969
theorem B1210607 : Blo 794341 1210607 := bstep (se 1 (by rfl) ⟨907955, by rfl⟩ : syracuseStep 1210607 = 1815911) B1815911
theorem B88177085 : Blo 794341 88177085 := bstep (se 3 (by rfl) ⟨16533203, by rfl⟩ : syracuseStep 88177085 = 33066407) B33066407
theorem B1702367 : Blo 794341 1702367 := bstep (se 1 (by rfl) ⟨1276775, by rfl⟩ : syracuseStep 1702367 = 2553551) B2553551
theorem B1343135 : Blo 794341 1343135 := bstep (se 1 (by rfl) ⟨1007351, by rfl⟩ : syracuseStep 1343135 = 2014703) B2014703
theorem B32735015 : Blo 794341 32735015 := bstep (se 1 (by rfl) ⟨24551261, by rfl⟩ : syracuseStep 32735015 = 49102523) B49102523
theorem B1344377 : Blo 794341 1344377 := bstep (se 2 (by rfl) ⟨504141, by rfl⟩ : syracuseStep 1344377 = 1008283) B1008283
theorem B2425825 : Blo 794341 2425825 := bstep (se 2 (by rfl) ⟨909684, by rfl⟩ : syracuseStep 2425825 = 1819369) B1819369
theorem B5112841 : Blo 794341 5112841 := bstep (se 2 (by rfl) ⟨1917315, by rfl⟩ : syracuseStep 5112841 = 3834631) B3834631
theorem B2557241 : Blo 794341 2557241 := bstep (se 2 (by rfl) ⟨958965, by rfl⟩ : syracuseStep 2557241 = 1917931) B1917931
theorem B10192513 : Blo 794341 10192513 := bstep (se 2 (by rfl) ⟨3822192, by rfl⟩ : syracuseStep 10192513 = 7644385) B7644385
theorem B1345403 : Blo 794341 1345403 := bstep (se 1 (by rfl) ⟨1009052, by rfl⟩ : syracuseStep 1345403 = 2018105) B2018105
theorem B2263079 : Blo 794341 2263079 := bstep (se 1 (by rfl) ⟨1697309, by rfl⟩ : syracuseStep 2263079 = 3394619) B3394619
theorem B1345673 : Blo 794341 1345673 := bstep (se 2 (by rfl) ⟨504627, by rfl⟩ : syracuseStep 1345673 = 1009255) B1009255
theorem B2689199 : Blo 794341 2689199 := bstep (se 1 (by rfl) ⟨2016899, by rfl⟩ : syracuseStep 2689199 = 4033799) B4033799
theorem B12913141 : Blo 794341 12913141 := bstep (se 5 (by rfl) ⟨605303, by rfl⟩ : syracuseStep 12913141 = 1210607) B1210607
theorem B1510139 : Blo 794341 1510139 := bstep (se 1 (by rfl) ⟨1132604, by rfl⟩ : syracuseStep 1510139 = 2265209) B2265209
theorem B1346537 : Blo 794341 1346537 := bstep (se 2 (by rfl) ⟨504951, by rfl⟩ : syracuseStep 1346537 = 1009903) B1009903
theorem B110103785 : Blo 794341 110103785 := bstep (se 2 (by rfl) ⟨41288919, by rfl⟩ : syracuseStep 110103785 = 82577839) B82577839
theorem B283250789 : Blo 794341 283250789 := bstep (se 4 (by rfl) ⟨26554761, by rfl⟩ : syracuseStep 283250789 = 53109523) B53109523
theorem B3018971 : Blo 794341 3018971 := bstep (se 1 (by rfl) ⟨2264228, by rfl⟩ : syracuseStep 3018971 = 4528457) B4528457
theorem B5378399 : Blo 794341 5378399 := bstep (se 1 (by rfl) ⟨4033799, by rfl⟩ : syracuseStep 5378399 = 8067599) B8067599
theorem B2692007 : Blo 794341 2692007 := bstep (se 1 (by rfl) ⟨2019005, by rfl⟩ : syracuseStep 2692007 = 4038011) B4038011
theorem B2266393 : Blo 794341 2266393 := bstep (se 2 (by rfl) ⟨849897, by rfl⟩ : syracuseStep 2266393 = 1699795) B1699795
theorem B4036553 : Blo 794341 4036553 := bstep (se 2 (by rfl) ⟨1513707, by rfl⟩ : syracuseStep 4036553 = 3027415) B3027415
theorem B1611775 : Blo 794341 1611775 := bstep (se 1 (by rfl) ⟨1208831, by rfl⟩ : syracuseStep 1611775 = 2417663) B2417663
theorem B44243489 : Blo 794341 44243489 := bstep (se 2 (by rfl) ⟨16591308, by rfl⟩ : syracuseStep 44243489 = 33182617) B33182617
theorem B1514771 : Blo 794341 1514771 := bstep (se 1 (by rfl) ⟨1136078, by rfl⟩ : syracuseStep 1514771 = 2272157) B2272157
theorem B1383983 : Blo 794341 1383983 := bstep (se 1 (by rfl) ⟨1037987, by rfl⟩ : syracuseStep 1383983 = 2075975) B2075975
theorem B794559 : Blo 794341 794559 := bstep (se 1 (by rfl) ⟨595919, by rfl⟩ : syracuseStep 794559 = 1191839) B1191839
theorem B795183 : Blo 794341 795183 := bstep (se 1 (by rfl) ⟨596387, by rfl⟩ : syracuseStep 795183 = 1192775) B1192775
theorem B4203197 : Blo 794341 4203197 := bstep (se 3 (by rfl) ⟨788099, by rfl⟩ : syracuseStep 4203197 = 1576199) B1576199
theorem B795719 : Blo 794341 795719 := bstep (se 1 (by rfl) ⟨596789, by rfl⟩ : syracuseStep 795719 = 1193579) B1193579
theorem B796263 : Blo 794341 796263 := bstep (se 1 (by rfl) ⟨597197, by rfl⟩ : syracuseStep 796263 = 1194395) B1194395
theorem B4302649 : Blo 794341 4302649 := bstep (se 2 (by rfl) ⟨1613493, by rfl⟩ : syracuseStep 4302649 = 3226987) B3226987
theorem B6039521 : Blo 794341 6039521 := bstep (se 2 (by rfl) ⟨2264820, by rfl⟩ : syracuseStep 6039521 = 4529641) B4529641
theorem B796903 : Blo 794341 796903 := bstep (se 1 (by rfl) ⟨597677, by rfl⟩ : syracuseStep 796903 = 1195355) B1195355
theorem B796911 : Blo 794341 796911 := bstep (se 1 (by rfl) ⟨597683, by rfl⟩ : syracuseStep 796911 = 1195367) B1195367
theorem B3221801 : Blo 794341 3221801 := bstep (se 2 (by rfl) ⟨1208175, by rfl⟩ : syracuseStep 3221801 = 2416351) B2416351
theorem B895423 : Blo 794341 895423 := bstep (se 1 (by rfl) ⟨671567, by rfl⟩ : syracuseStep 895423 = 1343135) B1343135
theorem B797311 : Blo 794341 797311 := bstep (se 1 (by rfl) ⟨597983, by rfl⟩ : syracuseStep 797311 = 1195967) B1195967
theorem B797567 : Blo 794341 797567 := bstep (se 1 (by rfl) ⟨598175, by rfl⟩ : syracuseStep 797567 = 1196351) B1196351
theorem B797787 : Blo 794341 797787 := bstep (se 1 (by rfl) ⟨598340, by rfl⟩ : syracuseStep 797787 = 1196681) B1196681
theorem B1191977 : Blo 794341 1191977 := bstep (se 2 (by rfl) ⟨446991, by rfl⟩ : syracuseStep 1191977 = 893983) B893983
theorem B1192103 : Blo 794341 1192103 := bstep (se 1 (by rfl) ⟨894077, by rfl⟩ : syracuseStep 1192103 = 1788155) B1788155
theorem B2011817 : Blo 794341 2011817 := bstep (se 2 (by rfl) ⟨754431, by rfl⟩ : syracuseStep 2011817 = 1508863) B1508863
theorem B1192895 : Blo 794341 1192895 := bstep (se 1 (by rfl) ⟨894671, by rfl⟩ : syracuseStep 1192895 = 1789343) B1789343
theorem B8729633 : Blo 794341 8729633 := bstep (se 2 (by rfl) ⟨3273612, by rfl⟩ : syracuseStep 8729633 = 6547225) B6547225
theorem B1193129 : Blo 794341 1193129 := bstep (se 2 (by rfl) ⟨447423, by rfl⟩ : syracuseStep 1193129 = 894847) B894847
theorem B1193183 : Blo 794341 1193183 := bstep (se 1 (by rfl) ⟨894887, by rfl⟩ : syracuseStep 1193183 = 1789775) B1789775
theorem B6042923 : Blo 794341 6042923 := bstep (se 1 (by rfl) ⟨4532192, by rfl⟩ : syracuseStep 6042923 = 9064385) B9064385
theorem B5092955 : Blo 794341 5092955 := bstep (se 1 (by rfl) ⟨3819716, by rfl⟩ : syracuseStep 5092955 = 7639433) B7639433
theorem B1193609 : Blo 794341 1193609 := bstep (se 2 (by rfl) ⟨447603, by rfl⟩ : syracuseStep 1193609 = 895207) B895207
theorem B4372121 : Blo 794341 4372121 := bstep (se 2 (by rfl) ⟨1639545, by rfl⟩ : syracuseStep 4372121 = 3279091) B3279091
theorem B1193951 : Blo 794341 1193951 := bstep (se 1 (by rfl) ⟨895463, by rfl⟩ : syracuseStep 1193951 = 1790927) B1790927
theorem B34355447 : Blo 794341 34355447 := bstep (se 1 (by rfl) ⟨25766585, by rfl⟩ : syracuseStep 34355447 = 51533171) B51533171
theorem B2013599 : Blo 794341 2013599 := bstep (se 1 (by rfl) ⟨1510199, by rfl⟩ : syracuseStep 2013599 = 3020399) B3020399
theorem B10205635 : Blo 794341 10205635 := bstep (se 1 (by rfl) ⟨7654226, by rfl⟩ : syracuseStep 10205635 = 15308453) B15308453
theorem B1194599 : Blo 794341 1194599 := bstep (se 1 (by rfl) ⟨895949, by rfl⟩ : syracuseStep 1194599 = 1791899) B1791899
theorem B1195103 : Blo 794341 1195103 := bstep (se 1 (by rfl) ⟨896327, by rfl⟩ : syracuseStep 1195103 = 1792655) B1792655
theorem B2047315 : Blo 794341 2047315 := bstep (se 1 (by rfl) ⟨1535486, by rfl⟩ : syracuseStep 2047315 = 3070973) B3070973
theorem B1196411 : Blo 794341 1196411 := bstep (se 1 (by rfl) ⟨897308, by rfl⟩ : syracuseStep 1196411 = 1794617) B1794617
theorem B12894713 : Blo 794341 12894713 := bstep (se 2 (by rfl) ⟨4835517, by rfl⟩ : syracuseStep 12894713 = 9671035) B9671035
theorem B41927219 : Blo 794341 41927219 := bstep (se 1 (by rfl) ⟨31445414, by rfl⟩ : syracuseStep 41927219 = 62890829) B62890829
theorem B2015999 : Blo 794341 2015999 := bstep (se 1 (by rfl) ⟨1511999, by rfl⟩ : syracuseStep 2015999 = 3023999) B3023999
theorem B34981307 : Blo 794341 34981307 := bstep (se 1 (by rfl) ⟨26235980, by rfl⟩ : syracuseStep 34981307 = 52471961) B52471961
theorem B1788137 : Blo 794341 1788137 := bstep (se 2 (by rfl) ⟨670551, by rfl⟩ : syracuseStep 1788137 = 1341103) B1341103
theorem B9062927 : Blo 794341 9062927 := bstep (se 1 (by rfl) ⟨6797195, by rfl⟩ : syracuseStep 9062927 = 13594391) B13594391
theorem B3394361 : Blo 794341 3394361 := bstep (se 2 (by rfl) ⟨1272885, by rfl⟩ : syracuseStep 3394361 = 2545771) B2545771
theorem B4541305 : Blo 794341 4541305 := bstep (se 2 (by rfl) ⟨1702989, by rfl⟩ : syracuseStep 4541305 = 3405979) B3405979
theorem B3886187 : Blo 794341 3886187 := bstep (se 1 (by rfl) ⟨2914640, by rfl⟩ : syracuseStep 3886187 = 5829281) B5829281
theorem B5165147 : Blo 794341 5165147 := bstep (se 1 (by rfl) ⟨3873860, by rfl⟩ : syracuseStep 5165147 = 7747721) B7747721
theorem B1364219 : Blo 794341 1364219 := bstep (se 1 (by rfl) ⟨1023164, by rfl⟩ : syracuseStep 1364219 = 2046329) B2046329
theorem B1134911 : Blo 794341 1134911 := bstep (se 1 (by rfl) ⟨851183, by rfl⟩ : syracuseStep 1134911 = 1702367) B1702367
theorem B2020079 : Blo 794341 2020079 := bstep (se 1 (by rfl) ⟨1515059, by rfl⟩ : syracuseStep 2020079 = 3030119) B3030119
theorem B12899519 : Blo 794341 12899519 := bstep (se 1 (by rfl) ⟨9674639, by rfl⟩ : syracuseStep 12899519 = 19349279) B19349279
theorem B1791359 : Blo 794341 1791359 := bstep (se 1 (by rfl) ⟨1343519, by rfl⟩ : syracuseStep 1791359 = 2687039) B2687039
theorem B1791719 : Blo 794341 1791719 := bstep (se 1 (by rfl) ⟨1343789, by rfl⟩ : syracuseStep 1791719 = 2687579) B2687579
theorem B4839193 : Blo 794341 4839193 := bstep (se 2 (by rfl) ⟨1814697, by rfl⟩ : syracuseStep 4839193 = 3629395) B3629395
theorem B3070075 : Blo 794341 3070075 := bstep (se 1 (by rfl) ⟨2302556, by rfl⟩ : syracuseStep 3070075 = 4605113) B4605113
theorem B19421471 : Blo 794341 19421471 := bstep (se 1 (by rfl) ⟨14566103, by rfl⟩ : syracuseStep 19421471 = 29132207) B29132207
theorem B33151639 : Blo 794341 33151639 := bstep (se 1 (by rfl) ⟨24863729, by rfl⟩ : syracuseStep 33151639 = 49727459) B49727459
theorem B2874143 : Blo 794341 2874143 := bstep (se 1 (by rfl) ⟨2155607, by rfl⟩ : syracuseStep 2874143 = 4311215) B4311215
theorem B2415935 : Blo 794341 2415935 := bstep (se 1 (by rfl) ⟨1811951, by rfl⟩ : syracuseStep 2415935 = 3623903) B3623903
theorem B27581903 : Blo 794341 27581903 := bstep (se 1 (by rfl) ⟨20686427, by rfl⟩ : syracuseStep 27581903 = 41372855) B41372855
theorem B1793519 : Blo 794341 1793519 := bstep (se 1 (by rfl) ⟨1345139, by rfl⟩ : syracuseStep 1793519 = 2690279) B2690279
theorem B1794041 : Blo 794341 1794041 := bstep (se 2 (by rfl) ⟨672765, by rfl⟩ : syracuseStep 1794041 = 1345531) B1345531
theorem B2416883 : Blo 794341 2416883 := bstep (se 1 (by rfl) ⟨1812662, by rfl⟩ : syracuseStep 2416883 = 3625325) B3625325
theorem B1008607 : Blo 794341 1008607 := bstep (se 1 (by rfl) ⟨756455, by rfl⟩ : syracuseStep 1008607 = 1512911) B1512911
theorem B5105051 : Blo 794341 5105051 := bstep (se 1 (by rfl) ⟨3828788, by rfl⟩ : syracuseStep 5105051 = 7657577) B7657577
theorem B1795823 : Blo 794341 1795823 := bstep (se 1 (by rfl) ⟨1346867, by rfl⟩ : syracuseStep 1795823 = 2693735) B2693735
theorem B5105537 : Blo 794341 5105537 := bstep (se 2 (by rfl) ⟨1914576, by rfl⟩ : syracuseStep 5105537 = 3829153) B3829153
theorem B1272527 : Blo 794341 1272527 := bstep (se 1 (by rfl) ⟨954395, by rfl⟩ : syracuseStep 1272527 = 1908791) B1908791
theorem B1272937 : Blo 794341 1272937 := bstep (se 2 (by rfl) ⟨477351, by rfl⟩ : syracuseStep 1272937 = 954703) B954703
theorem B2682287 : Blo 794341 2682287 := bstep (se 1 (by rfl) ⟨2011715, by rfl⟩ : syracuseStep 2682287 = 4023431) B4023431
theorem B3403451 : Blo 794341 3403451 := bstep (se 1 (by rfl) ⟨2552588, by rfl⟩ : syracuseStep 3403451 = 5105177) B5105177
theorem B5107535 : Blo 794341 5107535 := bstep (se 1 (by rfl) ⟨3830651, by rfl⟩ : syracuseStep 5107535 = 7661303) B7661303
theorem B1340651 : Blo 794341 1340651 := bstep (se 1 (by rfl) ⟨1005488, by rfl⟩ : syracuseStep 1340651 = 2010977) B2010977
theorem B2422847 : Blo 794341 2422847 := bstep (se 1 (by rfl) ⟨1817135, by rfl⟩ : syracuseStep 2422847 = 3634271) B3634271
theorem B1243387 : Blo 794341 1243387 := bstep (se 1 (by rfl) ⟨932540, by rfl⟩ : syracuseStep 1243387 = 1865081) B1865081
theorem B850171 : Blo 794341 850171 := bstep (se 1 (by rfl) ⟨637628, by rfl⟩ : syracuseStep 850171 = 1275257) B1275257
theorem B2685203 : Blo 794341 2685203 := bstep (se 1 (by rfl) ⟨2013902, by rfl⟩ : syracuseStep 2685203 = 4027805) B4027805
theorem B5733175 : Blo 794341 5733175 := bstep (se 1 (by rfl) ⟨4299881, by rfl⟩ : syracuseStep 5733175 = 8599763) B8599763
theorem B58784723 : Blo 794341 58784723 := bstep (se 1 (by rfl) ⟨44088542, by rfl⟩ : syracuseStep 58784723 = 88177085) B88177085
theorem B21823343 : Blo 794341 21823343 := bstep (se 1 (by rfl) ⟨16367507, by rfl⟩ : syracuseStep 21823343 = 32735015) B32735015
theorem B27951479 : Blo 794341 27951479 := bstep (se 1 (by rfl) ⟨20963609, by rfl⟩ : syracuseStep 27951479 = 41927219) B41927219
theorem B1343999 : Blo 794341 1343999 := bstep (se 1 (by rfl) ⟨1007999, by rfl⟩ : syracuseStep 1343999 = 2015999) B2015999
theorem B1704827 : Blo 794341 1704827 := bstep (se 1 (by rfl) ⟨1278620, by rfl⟩ : syracuseStep 1704827 = 2557241) B2557241
theorem B41452661 : Blo 794341 41452661 := bstep (se 5 (by rfl) ⟨1943093, by rfl⟩ : syracuseStep 41452661 = 3886187) B3886187
theorem B1344809 : Blo 794341 1344809 := bstep (se 2 (by rfl) ⟨504303, by rfl⟩ : syracuseStep 1344809 = 1008607) B1008607
theorem B6817121 : Blo 794341 6817121 := bstep (se 2 (by rfl) ⟨2556420, by rfl⟩ : syracuseStep 6817121 = 5112841) B5112841
theorem B1508719 : Blo 794341 1508719 := bstep (se 1 (by rfl) ⟨1131539, by rfl⟩ : syracuseStep 1508719 = 2263079) B2263079
theorem B2262907 : Blo 794341 2262907 := bstep (se 1 (by rfl) ⟨1697180, by rfl⟩ : syracuseStep 2262907 = 3394361) B3394361
theorem B73402523 : Blo 794341 73402523 := bstep (se 1 (by rfl) ⟨55051892, by rfl⟩ : syracuseStep 73402523 = 110103785) B110103785
theorem B1346719 : Blo 794341 1346719 := bstep (se 1 (by rfl) ⟨1010039, by rfl⟩ : syracuseStep 1346719 = 2020079) B2020079
theorem B2691035 : Blo 794341 2691035 := bstep (se 1 (by rfl) ⟨2018276, by rfl⟩ : syracuseStep 2691035 = 4036553) B4036553
theorem B29495659 : Blo 794341 29495659 := bstep (se 1 (by rfl) ⟨22121744, by rfl⟩ : syracuseStep 29495659 = 44243489) B44243489
theorem B1610623 : Blo 794341 1610623 := bstep (se 1 (by rfl) ⟨1207967, by rfl⟩ : syracuseStep 1610623 = 2415935) B2415935
theorem B18387935 : Blo 794341 18387935 := bstep (se 1 (by rfl) ⟨13790951, by rfl⟩ : syracuseStep 18387935 = 27581903) B27581903
theorem B922655 : Blo 794341 922655 := bstep (se 1 (by rfl) ⟨691991, by rfl⟩ : syracuseStep 922655 = 1383983) B1383983
theorem B3021857 : Blo 794341 3021857 := bstep (se 2 (by rfl) ⟨1133196, by rfl⟩ : syracuseStep 3021857 = 2266393) B2266393
theorem B2268967 : Blo 794341 2268967 := bstep (se 1 (by rfl) ⟨1701725, by rfl⟩ : syracuseStep 2268967 = 3403451) B3403451
theorem B794651 : Blo 794341 794651 := bstep (se 1 (by rfl) ⟨595988, by rfl⟩ : syracuseStep 794651 = 1191977) B1191977
theorem B794735 : Blo 794341 794735 := bstep (se 1 (by rfl) ⟨596051, by rfl⟩ : syracuseStep 794735 = 1192103) B1192103
theorem B13607513 : Blo 794341 13607513 := bstep (se 2 (by rfl) ⟨5102817, by rfl⟩ : syracuseStep 13607513 = 10205635) B10205635
theorem B795263 : Blo 794341 795263 := bstep (se 1 (by rfl) ⟨596447, by rfl⟩ : syracuseStep 795263 = 1192895) B1192895
theorem B795419 : Blo 794341 795419 := bstep (se 1 (by rfl) ⟨596564, by rfl⟩ : syracuseStep 795419 = 1193129) B1193129
theorem B795455 : Blo 794341 795455 := bstep (se 1 (by rfl) ⟨596591, by rfl⟩ : syracuseStep 795455 = 1193183) B1193183
theorem B893767 : Blo 794341 893767 := bstep (se 1 (by rfl) ⟨670325, by rfl⟩ : syracuseStep 893767 = 1340651) B1340651
theorem B7644233 : Blo 794341 7644233 := bstep (se 2 (by rfl) ⟨2866587, by rfl⟩ : syracuseStep 7644233 = 5733175) B5733175
theorem B795739 : Blo 794341 795739 := bstep (se 1 (by rfl) ⟨596804, by rfl⟩ : syracuseStep 795739 = 1193609) B1193609
theorem B795967 : Blo 794341 795967 := bstep (se 1 (by rfl) ⟨596975, by rfl⟩ : syracuseStep 795967 = 1193951) B1193951
theorem B1615231 : Blo 794341 1615231 := bstep (se 1 (by rfl) ⟨1211423, by rfl⟩ : syracuseStep 1615231 = 2422847) B2422847
theorem B22947461 : Blo 794341 22947461 := bstep (se 4 (by rfl) ⟨2151324, by rfl⟩ : syracuseStep 22947461 = 4302649) B4302649
theorem B796399 : Blo 794341 796399 := bstep (se 1 (by rfl) ⟨597299, by rfl⟩ : syracuseStep 796399 = 1194599) B1194599
theorem B2729753 : Blo 794341 2729753 := bstep (se 2 (by rfl) ⟨1023657, by rfl⟩ : syracuseStep 2729753 = 2047315) B2047315
theorem B796735 : Blo 794341 796735 := bstep (se 1 (by rfl) ⟨597551, by rfl⟩ : syracuseStep 796735 = 1195103) B1195103
theorem B13773725 : Blo 794341 13773725 := bstep (se 3 (by rfl) ⟨2582573, by rfl⟩ : syracuseStep 13773725 = 5165147) B5165147
theorem B797607 : Blo 794341 797607 := bstep (se 1 (by rfl) ⟨598205, by rfl⟩ : syracuseStep 797607 = 1196411) B1196411
theorem B8596475 : Blo 794341 8596475 := bstep (se 1 (by rfl) ⟨6447356, by rfl⟩ : syracuseStep 8596475 = 12894713) B12894713
theorem B896251 : Blo 794341 896251 := bstep (se 1 (by rfl) ⟨672188, by rfl⟩ : syracuseStep 896251 = 1344377) B1344377
theorem B3026429 : Blo 794341 3026429 := bstep (se 3 (by rfl) ⟨567455, by rfl⟩ : syracuseStep 3026429 = 1134911) B1134911
theorem B896935 : Blo 794341 896935 := bstep (se 1 (by rfl) ⟨672701, by rfl⟩ : syracuseStep 896935 = 1345403) B1345403
theorem B897115 : Blo 794341 897115 := bstep (se 1 (by rfl) ⟨672836, by rfl⟩ : syracuseStep 897115 = 1345673) B1345673
theorem B1192091 : Blo 794341 1192091 := bstep (se 1 (by rfl) ⟨894068, by rfl⟩ : syracuseStep 1192091 = 1788137) B1788137
theorem B6041951 : Blo 794341 6041951 := bstep (se 1 (by rfl) ⟨4531463, by rfl⟩ : syracuseStep 6041951 = 9062927) B9062927
theorem B897691 : Blo 794341 897691 := bstep (se 1 (by rfl) ⟨673268, by rfl⟩ : syracuseStep 897691 = 1346537) B1346537
theorem B23279021 : Blo 794341 23279021 := bstep (se 3 (by rfl) ⟨4364816, by rfl⟩ : syracuseStep 23279021 = 8729633) B8729633
theorem B2012647 : Blo 794341 2012647 := bstep (se 1 (by rfl) ⟨1509485, by rfl⟩ : syracuseStep 2012647 = 3018971) B3018971
theorem B3585599 : Blo 794341 3585599 := bstep (se 1 (by rfl) ⟨2689199, by rfl⟩ : syracuseStep 3585599 = 5378399) B5378399
theorem B1193897 : Blo 794341 1193897 := bstep (se 2 (by rfl) ⟨447711, by rfl⟩ : syracuseStep 1193897 = 895423) B895423
theorem B17217521 : Blo 794341 17217521 := bstep (se 2 (by rfl) ⟨6456570, by rfl⟩ : syracuseStep 17217521 = 12913141) B12913141
theorem B8599679 : Blo 794341 8599679 := bstep (se 1 (by rfl) ⟨6449759, by rfl⟩ : syracuseStep 8599679 = 12899519) B12899519
theorem B1194239 : Blo 794341 1194239 := bstep (se 1 (by rfl) ⟨895679, by rfl⟩ : syracuseStep 1194239 = 1791359) B1791359
theorem B1194479 : Blo 794341 1194479 := bstep (se 1 (by rfl) ⟨895859, by rfl⟩ : syracuseStep 1194479 = 1791719) B1791719
theorem B1916095 : Blo 794341 1916095 := bstep (se 1 (by rfl) ⟨1437071, by rfl⟩ : syracuseStep 1916095 = 2874143) B2874143
theorem B1195679 : Blo 794341 1195679 := bstep (se 1 (by rfl) ⟨896759, by rfl⟩ : syracuseStep 1195679 = 1793519) B1793519
theorem B1196027 : Blo 794341 1196027 := bstep (se 1 (by rfl) ⟨897020, by rfl⟩ : syracuseStep 1196027 = 1794041) B1794041
theorem B2802131 : Blo 794341 2802131 := bstep (se 1 (by rfl) ⟨2101598, by rfl⟩ : syracuseStep 2802131 = 4203197) B4203197
theorem B51790589 : Blo 794341 51790589 := bstep (se 3 (by rfl) ⟨9710735, by rfl⟩ : syracuseStep 51790589 = 19421471) B19421471
theorem B1197215 : Blo 794341 1197215 := bstep (se 1 (by rfl) ⟨897911, by rfl⟩ : syracuseStep 1197215 = 1795823) B1795823
theorem B2147867 : Blo 794341 2147867 := bstep (se 1 (by rfl) ⟨1610900, by rfl⟩ : syracuseStep 2147867 = 3221801) B3221801
theorem B1788191 : Blo 794341 1788191 := bstep (se 1 (by rfl) ⟨1341143, by rfl⟩ : syracuseStep 1788191 = 2682287) B2682287
theorem B2149033 : Blo 794341 2149033 := bstep (se 2 (by rfl) ⟨805887, by rfl⟩ : syracuseStep 2149033 = 1611775) B1611775
theorem B1657849 : Blo 794341 1657849 := bstep (se 2 (by rfl) ⟨621693, by rfl⟩ : syracuseStep 1657849 = 1243387) B1243387
theorem B1133561 : Blo 794341 1133561 := bstep (se 2 (by rfl) ⟨425085, by rfl⟩ : syracuseStep 1133561 = 850171) B850171
theorem B3395303 : Blo 794341 3395303 := bstep (se 1 (by rfl) ⟨2546477, by rfl⟩ : syracuseStep 3395303 = 5092955) B5092955
theorem B25809029 : Blo 794341 25809029 := bstep (se 4 (by rfl) ⟨2419596, by rfl⟩ : syracuseStep 25809029 = 4839193) B4839193
theorem B1790135 : Blo 794341 1790135 := bstep (se 1 (by rfl) ⟨1342601, by rfl⟩ : syracuseStep 1790135 = 2685203) B2685203
theorem B6445021 : Blo 794341 6445021 := bstep (se 3 (by rfl) ⟨1208441, by rfl⟩ : syracuseStep 6445021 = 2416883) B2416883
theorem B23320871 : Blo 794341 23320871 := bstep (se 1 (by rfl) ⟨17490653, by rfl⟩ : syracuseStep 23320871 = 34981307) B34981307
theorem B3234433 : Blo 794341 3234433 := bstep (se 2 (by rfl) ⟨1212912, by rfl⟩ : syracuseStep 3234433 = 2425825) B2425825
theorem B1792799 : Blo 794341 1792799 := bstep (se 1 (by rfl) ⟨1344599, by rfl⟩ : syracuseStep 1792799 = 2689199) B2689199
theorem B1006759 : Blo 794341 1006759 := bstep (se 1 (by rfl) ⟨755069, by rfl⟩ : syracuseStep 1006759 = 1510139) B1510139
theorem B13590017 : Blo 794341 13590017 := bstep (se 2 (by rfl) ⟨5096256, by rfl⟩ : syracuseStep 13590017 = 10192513) B10192513
theorem B188833859 : Blo 794341 188833859 := bstep (se 1 (by rfl) ⟨141625394, by rfl⟩ : syracuseStep 188833859 = 283250789) B283250789
theorem B909479 : Blo 794341 909479 := bstep (se 1 (by rfl) ⟨682109, by rfl⟩ : syracuseStep 909479 = 1364219) B1364219
theorem B1794671 : Blo 794341 1794671 := bstep (se 1 (by rfl) ⟨1346003, by rfl⟩ : syracuseStep 1794671 = 2692007) B2692007
theorem B6055073 : Blo 794341 6055073 := bstep (se 2 (by rfl) ⟨2270652, by rfl⟩ : syracuseStep 6055073 = 4541305) B4541305
theorem B1697249 : Blo 794341 1697249 := bstep (se 2 (by rfl) ⟨636468, by rfl⟩ : syracuseStep 1697249 = 1272937) B1272937
theorem B1009847 : Blo 794341 1009847 := bstep (se 1 (by rfl) ⟨757385, by rfl⟩ : syracuseStep 1009847 = 1514771) B1514771
theorem B3403367 : Blo 794341 3403367 := bstep (se 1 (by rfl) ⟨2552525, by rfl⟩ : syracuseStep 3403367 = 5105051) B5105051
theorem B3403691 : Blo 794341 3403691 := bstep (se 1 (by rfl) ⟨2552768, by rfl⟩ : syracuseStep 3403691 = 5105537) B5105537
theorem B4026347 : Blo 794341 4026347 := bstep (se 1 (by rfl) ⟨3019760, by rfl⟩ : syracuseStep 4026347 = 6039521) B6039521
theorem B848351 : Blo 794341 848351 := bstep (se 1 (by rfl) ⟨636263, by rfl⟩ : syracuseStep 848351 = 1272527) B1272527
theorem B3405023 : Blo 794341 3405023 := bstep (se 1 (by rfl) ⟨2553767, by rfl⟩ : syracuseStep 3405023 = 5107535) B5107535
theorem B4093433 : Blo 794341 4093433 := bstep (se 2 (by rfl) ⟨1535037, by rfl⟩ : syracuseStep 4093433 = 3070075) B3070075
theorem B1341211 : Blo 794341 1341211 := bstep (se 1 (by rfl) ⟨1005908, by rfl⟩ : syracuseStep 1341211 = 2011817) B2011817
theorem B4028615 : Blo 794341 4028615 := bstep (se 1 (by rfl) ⟨3021461, by rfl⟩ : syracuseStep 4028615 = 6042923) B6042923
theorem B44202185 : Blo 794341 44202185 := bstep (se 2 (by rfl) ⟨16575819, by rfl⟩ : syracuseStep 44202185 = 33151639) B33151639
theorem B2914747 : Blo 794341 2914747 := bstep (se 1 (by rfl) ⟨2186060, by rfl⟩ : syracuseStep 2914747 = 4372121) B4372121
theorem B22903631 : Blo 794341 22903631 := bstep (se 1 (by rfl) ⟨17177723, by rfl⟩ : syracuseStep 22903631 = 34355447) B34355447
theorem B1342399 : Blo 794341 1342399 := bstep (se 1 (by rfl) ⟨1006799, by rfl⟩ : syracuseStep 1342399 = 2013599) B2013599
theorem B39189815 : Blo 794341 39189815 := bstep (se 1 (by rfl) ⟨29392361, by rfl⟩ : syracuseStep 39189815 = 58784723) B58784723
theorem B14548895 : Blo 794341 14548895 := bstep (se 1 (by rfl) ⟨10911671, by rfl⟩ : syracuseStep 14548895 = 21823343) B21823343
theorem B1868087 : Blo 794341 1868087 := bstep (se 1 (by rfl) ⟨1401065, by rfl⟩ : syracuseStep 1868087 = 2802131) B2802131
theorem B2425277 : Blo 794341 2425277 := bstep (se 3 (by rfl) ⟨454739, by rfl⟩ : syracuseStep 2425277 = 909479) B909479
theorem B2262269 : Blo 794341 2262269 := bstep (se 3 (by rfl) ⟨424175, by rfl⟩ : syracuseStep 2262269 = 848351) B848351
theorem B2263535 : Blo 794341 2263535 := bstep (se 1 (by rfl) ⟨1697651, by rfl⟩ : syracuseStep 2263535 = 3395303) B3395303
theorem B3017209 : Blo 794341 3017209 := bstep (se 2 (by rfl) ⟨1131453, by rfl⟩ : syracuseStep 3017209 = 2262907) B2262907
theorem B2460413 : Blo 794341 2460413 := bstep (se 3 (by rfl) ⟨461327, by rfl⟩ : syracuseStep 2460413 = 922655) B922655
theorem B17206019 : Blo 794341 17206019 := bstep (se 1 (by rfl) ⟨12904514, by rfl⟩ : syracuseStep 17206019 = 25809029) B25809029
theorem B12258623 : Blo 794341 12258623 := bstep (se 1 (by rfl) ⟨9193967, by rfl⟩ : syracuseStep 12258623 = 18387935) B18387935
theorem B8589989 : Blo 794341 8589989 := bstep (se 4 (by rfl) ⟨805311, by rfl⟩ : syracuseStep 8589989 = 1610623) B1610623
theorem B39327545 : Blo 794341 39327545 := bstep (se 2 (by rfl) ⟨14747829, by rfl⟩ : syracuseStep 39327545 = 29495659) B29495659
theorem B2692925 : Blo 794341 2692925 := bstep (se 3 (by rfl) ⟨504923, by rfl⟩ : syracuseStep 2692925 = 1009847) B1009847
theorem B4036715 : Blo 794341 4036715 := bstep (se 1 (by rfl) ⟨3027536, by rfl⟩ : syracuseStep 4036715 = 6055073) B6055073
theorem B9182483 : Blo 794341 9182483 := bstep (se 1 (by rfl) ⟨6886862, by rfl⟩ : syracuseStep 9182483 = 13773725) B13773725
theorem B2268911 : Blo 794341 2268911 := bstep (se 1 (by rfl) ⟨1701683, by rfl⟩ : syracuseStep 2268911 = 3403367) B3403367
theorem B2269127 : Blo 794341 2269127 := bstep (se 1 (by rfl) ⟨1701845, by rfl⟩ : syracuseStep 2269127 = 3403691) B3403691
theorem B8593361 : Blo 794341 8593361 := bstep (se 2 (by rfl) ⟨3222510, by rfl⟩ : syracuseStep 8593361 = 6445021) B6445021
theorem B3022829 : Blo 794341 3022829 := bstep (se 3 (by rfl) ⟨566780, by rfl⟩ : syracuseStep 3022829 = 1133561) B1133561
theorem B794727 : Blo 794341 794727 := bstep (se 1 (by rfl) ⟨596045, by rfl⟩ : syracuseStep 794727 = 1192091) B1192091
theorem B2270015 : Blo 794341 2270015 := bstep (se 1 (by rfl) ⟨1702511, by rfl⟩ : syracuseStep 2270015 = 3405023) B3405023
theorem B2728955 : Blo 794341 2728955 := bstep (se 1 (by rfl) ⟨2046716, by rfl⟩ : syracuseStep 2728955 = 4093433) B4093433
theorem B795931 : Blo 794341 795931 := bstep (se 1 (by rfl) ⟨596948, by rfl⟩ : syracuseStep 795931 = 1193897) B1193897
theorem B11478347 : Blo 794341 11478347 := bstep (se 1 (by rfl) ⟨8608760, by rfl⟩ : syracuseStep 11478347 = 17217521) B17217521
theorem B29468123 : Blo 794341 29468123 := bstep (se 1 (by rfl) ⟨22101092, by rfl⟩ : syracuseStep 29468123 = 44202185) B44202185
theorem B796159 : Blo 794341 796159 := bstep (se 1 (by rfl) ⟨597119, by rfl⟩ : syracuseStep 796159 = 1194239) B1194239
theorem B796319 : Blo 794341 796319 := bstep (se 1 (by rfl) ⟨597239, by rfl⟩ : syracuseStep 796319 = 1194479) B1194479
theorem B26126543 : Blo 794341 26126543 := bstep (se 1 (by rfl) ⟨19594907, by rfl⟩ : syracuseStep 26126543 = 39189815) B39189815
theorem B3025289 : Blo 794341 3025289 := bstep (se 2 (by rfl) ⟨1134483, by rfl⟩ : syracuseStep 3025289 = 2268967) B2268967
theorem B797119 : Blo 794341 797119 := bstep (se 1 (by rfl) ⟨597839, by rfl⟩ : syracuseStep 797119 = 1195679) B1195679
theorem B797351 : Blo 794341 797351 := bstep (se 1 (by rfl) ⟨598013, by rfl⟩ : syracuseStep 797351 = 1196027) B1196027
theorem B895999 : Blo 794341 895999 := bstep (se 1 (by rfl) ⟨671999, by rfl⟩ : syracuseStep 895999 = 1343999) B1343999
theorem B27635107 : Blo 794341 27635107 := bstep (se 1 (by rfl) ⟨20726330, by rfl⟩ : syracuseStep 27635107 = 41452661) B41452661
theorem B798143 : Blo 794341 798143 := bstep (se 1 (by rfl) ⟨598607, by rfl⟩ : syracuseStep 798143 = 1197215) B1197215
theorem B896539 : Blo 794341 896539 := bstep (se 1 (by rfl) ⟨672404, by rfl⟩ : syracuseStep 896539 = 1344809) B1344809
theorem B1191689 : Blo 794341 1191689 := bstep (se 2 (by rfl) ⟨446883, by rfl⟩ : syracuseStep 1191689 = 893767) B893767
theorem B48935015 : Blo 794341 48935015 := bstep (se 1 (by rfl) ⟨36701261, by rfl⟩ : syracuseStep 48935015 = 73402523) B73402523
theorem B1192127 : Blo 794341 1192127 := bstep (se 1 (by rfl) ⟨894095, by rfl⟩ : syracuseStep 1192127 = 1788191) B1788191
theorem B2011625 : Blo 794341 2011625 := bstep (se 2 (by rfl) ⟨754359, by rfl⟩ : syracuseStep 2011625 = 1508719) B1508719
theorem B15545317 : Blo 794341 15545317 := bstep (se 4 (by rfl) ⟨1457373, by rfl⟩ : syracuseStep 15545317 = 2914747) B2914747
theorem B1193423 : Blo 794341 1193423 := bstep (se 1 (by rfl) ⟨895067, by rfl⟩ : syracuseStep 1193423 = 1790135) B1790135
theorem B2865377 : Blo 794341 2865377 := bstep (se 2 (by rfl) ⟨1074516, by rfl⟩ : syracuseStep 2865377 = 2149033) B2149033
theorem B2210465 : Blo 794341 2210465 := bstep (se 2 (by rfl) ⟨828924, by rfl⟩ : syracuseStep 2210465 = 1657849) B1657849
theorem B15547247 : Blo 794341 15547247 := bstep (se 1 (by rfl) ⟨11660435, by rfl⟩ : syracuseStep 15547247 = 23320871) B23320871
theorem B1195001 : Blo 794341 1195001 := bstep (se 2 (by rfl) ⟨448125, by rfl⟩ : syracuseStep 1195001 = 896251) B896251
theorem B1195199 : Blo 794341 1195199 := bstep (se 1 (by rfl) ⟨896399, by rfl⟩ : syracuseStep 1195199 = 1792799) B1792799
theorem B2014571 : Blo 794341 2014571 := bstep (se 1 (by rfl) ⟨1510928, by rfl⟩ : syracuseStep 2014571 = 3021857) B3021857
theorem B9060011 : Blo 794341 9060011 := bstep (se 1 (by rfl) ⟨6795008, by rfl⟩ : syracuseStep 9060011 = 13590017) B13590017
theorem B1195913 : Blo 794341 1195913 := bstep (se 2 (by rfl) ⟨448467, by rfl⟩ : syracuseStep 1195913 = 896935) B896935
theorem B1196153 : Blo 794341 1196153 := bstep (se 2 (by rfl) ⟨448557, by rfl⟩ : syracuseStep 1196153 = 897115) B897115
theorem B1196447 : Blo 794341 1196447 := bstep (se 1 (by rfl) ⟨897335, by rfl⟩ : syracuseStep 1196447 = 1794671) B1794671
theorem B5096155 : Blo 794341 5096155 := bstep (se 1 (by rfl) ⟨3822116, by rfl⟩ : syracuseStep 5096155 = 7644233) B7644233
theorem B1196921 : Blo 794341 1196921 := bstep (se 2 (by rfl) ⟨448845, by rfl⟩ : syracuseStep 1196921 = 897691) B897691
theorem B1131499 : Blo 794341 1131499 := bstep (se 1 (by rfl) ⟨848624, by rfl⟩ : syracuseStep 1131499 = 1697249) B1697249
theorem B1819835 : Blo 794341 1819835 := bstep (se 1 (by rfl) ⟨1364876, by rfl⟩ : syracuseStep 1819835 = 2729753) B2729753
theorem B2017619 : Blo 794341 2017619 := bstep (se 1 (by rfl) ⟨1513214, by rfl⟩ : syracuseStep 2017619 = 3026429) B3026429
theorem B1788281 : Blo 794341 1788281 := bstep (se 2 (by rfl) ⟨670605, by rfl⟩ : syracuseStep 1788281 = 1341211) B1341211
theorem B4312577 : Blo 794341 4312577 := bstep (se 2 (by rfl) ⟨1617216, by rfl⟩ : syracuseStep 4312577 = 3234433) B3234433
theorem B15519347 : Blo 794341 15519347 := bstep (se 1 (by rfl) ⟨11639510, by rfl⟩ : syracuseStep 15519347 = 23279021) B23279021
theorem B1789865 : Blo 794341 1789865 := bstep (se 2 (by rfl) ⟨671199, by rfl⟩ : syracuseStep 1789865 = 1342399) B1342399
theorem B18634319 : Blo 794341 18634319 := bstep (se 1 (by rfl) ⟨13975739, by rfl⟩ : syracuseStep 18634319 = 27951479) B27951479
theorem B34527059 : Blo 794341 34527059 := bstep (se 1 (by rfl) ⟨25895294, by rfl⟩ : syracuseStep 34527059 = 51790589) B51790589
theorem B4544747 : Blo 794341 4544747 := bstep (se 1 (by rfl) ⟨3408560, by rfl⟩ : syracuseStep 4544747 = 6817121) B6817121
theorem B1431911 : Blo 794341 1431911 := bstep (se 1 (by rfl) ⟨1073933, by rfl⟩ : syracuseStep 1431911 = 2147867) B2147867
theorem B2153641 : Blo 794341 2153641 := bstep (se 2 (by rfl) ⟨807615, by rfl⟩ : syracuseStep 2153641 = 1615231) B1615231
theorem B4546205 : Blo 794341 4546205 := bstep (se 3 (by rfl) ⟨852413, by rfl⟩ : syracuseStep 4546205 = 1704827) B1704827
theorem B1794023 : Blo 794341 1794023 := bstep (se 1 (by rfl) ⟨1345517, by rfl⟩ : syracuseStep 1794023 = 2691035) B2691035
theorem B1795625 : Blo 794341 1795625 := bstep (se 2 (by rfl) ⟨673359, by rfl⟩ : syracuseStep 1795625 = 1346719) B1346719
theorem B125889239 : Blo 794341 125889239 := bstep (se 1 (by rfl) ⟨94416929, by rfl⟩ : syracuseStep 125889239 = 188833859) B188833859
theorem B9071675 : Blo 794341 9071675 := bstep (se 1 (by rfl) ⟨6803756, by rfl⟩ : syracuseStep 9071675 = 13607513) B13607513
theorem B15298307 : Blo 794341 15298307 := bstep (se 1 (by rfl) ⟨11473730, by rfl⟩ : syracuseStep 15298307 = 22947461) B22947461
theorem B2683529 : Blo 794341 2683529 := bstep (se 2 (by rfl) ⟨1006323, by rfl⟩ : syracuseStep 2683529 = 2012647) B2012647
theorem B5730983 : Blo 794341 5730983 := bstep (se 1 (by rfl) ⟨4298237, by rfl⟩ : syracuseStep 5730983 = 8596475) B8596475
theorem B2684231 : Blo 794341 2684231 := bstep (se 1 (by rfl) ⟨2013173, by rfl⟩ : syracuseStep 2684231 = 4026347) B4026347
theorem B4027967 : Blo 794341 4027967 := bstep (se 1 (by rfl) ⟨3020975, by rfl⟩ : syracuseStep 4027967 = 6041951) B6041951
theorem B2390399 : Blo 794341 2390399 := bstep (se 1 (by rfl) ⟨1792799, by rfl⟩ : syracuseStep 2390399 = 3585599) B3585599
theorem B5733119 : Blo 794341 5733119 := bstep (se 1 (by rfl) ⟨4299839, by rfl⟩ : syracuseStep 5733119 = 8599679) B8599679
theorem B2685743 : Blo 794341 2685743 := bstep (se 1 (by rfl) ⟨2014307, by rfl⟩ : syracuseStep 2685743 = 4028615) B4028615
theorem B1342345 : Blo 794341 1342345 := bstep (se 2 (by rfl) ⟨503379, by rfl⟩ : syracuseStep 1342345 = 1006759) B1006759
theorem B2554793 : Blo 794341 2554793 := bstep (se 2 (by rfl) ⟨958047, by rfl⟩ : syracuseStep 2554793 = 1916095) B1916095
theorem B15269087 : Blo 794341 15269087 := bstep (se 1 (by rfl) ⟨11451815, by rfl⟩ : syracuseStep 15269087 = 22903631) B22903631
theorem B9699263 : Blo 794341 9699263 := bstep (se 1 (by rfl) ⟨7274447, by rfl⟩ : syracuseStep 9699263 = 14548895) B14548895
theorem B1213223 : Blo 794341 1213223 := bstep (se 1 (by rfl) ⟨909917, by rfl⟩ : syracuseStep 1213223 = 1819835) B1819835
theorem B4981565 : Blo 794341 4981565 := bstep (se 3 (by rfl) ⟨934043, by rfl⟩ : syracuseStep 4981565 = 1868087) B1868087
theorem B1345079 : Blo 794341 1345079 := bstep (se 1 (by rfl) ⟨1008809, by rfl⟩ : syracuseStep 1345079 = 2017619) B2017619
theorem B1509023 : Blo 794341 1509023 := bstep (se 1 (by rfl) ⟨1131767, by rfl⟩ : syracuseStep 1509023 = 2263535) B2263535
theorem B22906637 : Blo 794341 22906637 := bstep (se 3 (by rfl) ⟨4294994, by rfl⟩ : syracuseStep 22906637 = 8589989) B8589989
theorem B11470679 : Blo 794341 11470679 := bstep (se 1 (by rfl) ⟨8603009, by rfl⟩ : syracuseStep 11470679 = 17206019) B17206019
theorem B7277213 : Blo 794341 7277213 := bstep (se 3 (by rfl) ⟨1364477, by rfl⟩ : syracuseStep 7277213 = 2728955) B2728955
theorem B6032717 : Blo 794341 6032717 := bstep (se 3 (by rfl) ⟨1131134, by rfl⟩ : syracuseStep 6032717 = 2262269) B2262269
theorem B12422879 : Blo 794341 12422879 := bstep (se 1 (by rfl) ⟨9317159, by rfl⟩ : syracuseStep 12422879 = 18634319) B18634319
theorem B2691143 : Blo 794341 2691143 := bstep (se 1 (by rfl) ⟨2018357, by rfl⟩ : syracuseStep 2691143 = 4036715) B4036715
theorem B954607 : Blo 794341 954607 := bstep (se 1 (by rfl) ⟨715955, by rfl⟩ : syracuseStep 954607 = 1431911) B1431911
theorem B1512607 : Blo 794341 1512607 := bstep (se 1 (by rfl) ⟨1134455, by rfl⟩ : syracuseStep 1512607 = 2268911) B2268911
theorem B6034661 : Blo 794341 6034661 := bstep (se 4 (by rfl) ⟨565749, by rfl⟩ : syracuseStep 6034661 = 1131499) B1131499
theorem B1512751 : Blo 794341 1512751 := bstep (se 1 (by rfl) ⟨1134563, by rfl⟩ : syracuseStep 1512751 = 2269127) B2269127
theorem B69670781 : Blo 794341 69670781 := bstep (se 3 (by rfl) ⟨13063271, by rfl⟩ : syracuseStep 69670781 = 26126543) B26126543
theorem B1513343 : Blo 794341 1513343 := bstep (se 1 (by rfl) ⟨1135007, by rfl⟩ : syracuseStep 1513343 = 2270015) B2270015
theorem B6561101 : Blo 794341 6561101 := bstep (se 3 (by rfl) ⟨1230206, by rfl⟩ : syracuseStep 6561101 = 2460413) B2460413
theorem B10198871 : Blo 794341 10198871 := bstep (se 1 (by rfl) ⟨7649153, by rfl⟩ : syracuseStep 10198871 = 15298307) B15298307
theorem B794459 : Blo 794341 794459 := bstep (se 1 (by rfl) ⟨595844, by rfl⟩ : syracuseStep 794459 = 1191689) B1191689
theorem B794751 : Blo 794341 794751 := bstep (se 1 (by rfl) ⟨596063, by rfl⟩ : syracuseStep 794751 = 1192127) B1192127
theorem B795615 : Blo 794341 795615 := bstep (se 1 (by rfl) ⟨596711, by rfl⟩ : syracuseStep 795615 = 1193423) B1193423
theorem B1910251 : Blo 794341 1910251 := bstep (se 1 (by rfl) ⟨1432688, by rfl⟩ : syracuseStep 1910251 = 2865377) B2865377
theorem B10364831 : Blo 794341 10364831 := bstep (se 1 (by rfl) ⟨7773623, by rfl⟩ : syracuseStep 10364831 = 15547247) B15547247
theorem B796667 : Blo 794341 796667 := bstep (se 1 (by rfl) ⟨597500, by rfl⟩ : syracuseStep 796667 = 1195001) B1195001
theorem B796799 : Blo 794341 796799 := bstep (se 1 (by rfl) ⟨597599, by rfl⟩ : syracuseStep 796799 = 1195199) B1195199
theorem B6040007 : Blo 794341 6040007 := bstep (se 1 (by rfl) ⟨4530005, by rfl⟩ : syracuseStep 6040007 = 9060011) B9060011
theorem B797275 : Blo 794341 797275 := bstep (se 1 (by rfl) ⟨597956, by rfl⟩ : syracuseStep 797275 = 1195913) B1195913
theorem B6466175 : Blo 794341 6466175 := bstep (se 1 (by rfl) ⟨4849631, by rfl⟩ : syracuseStep 6466175 = 9699263) B9699263
theorem B797435 : Blo 794341 797435 := bstep (se 1 (by rfl) ⟨598076, by rfl⟩ : syracuseStep 797435 = 1196153) B1196153
theorem B797631 : Blo 794341 797631 := bstep (se 1 (by rfl) ⟨598223, by rfl⟩ : syracuseStep 797631 = 1196447) B1196447
theorem B1616851 : Blo 794341 1616851 := bstep (se 1 (by rfl) ⟨1212638, by rfl⟩ : syracuseStep 1616851 = 2425277) B2425277
theorem B797947 : Blo 794341 797947 := bstep (se 1 (by rfl) ⟨598460, by rfl⟩ : syracuseStep 797947 = 1196921) B1196921
theorem B6794873 : Blo 794341 6794873 := bstep (se 2 (by rfl) ⟨2548077, by rfl⟩ : syracuseStep 6794873 = 5096155) B5096155
theorem B1192187 : Blo 794341 1192187 := bstep (se 1 (by rfl) ⟨894140, by rfl⟩ : syracuseStep 1192187 = 1788281) B1788281
theorem B8172415 : Blo 794341 8172415 := bstep (se 1 (by rfl) ⟨6129311, by rfl⟩ : syracuseStep 8172415 = 12258623) B12258623
theorem B1193243 : Blo 794341 1193243 := bstep (se 1 (by rfl) ⟨894932, by rfl⟩ : syracuseStep 1193243 = 1789865) B1789865
theorem B23018039 : Blo 794341 23018039 := bstep (se 1 (by rfl) ⟨17263529, by rfl⟩ : syracuseStep 23018039 = 34527059) B34527059
theorem B1194665 : Blo 794341 1194665 := bstep (se 2 (by rfl) ⟨447999, by rfl⟩ : syracuseStep 1194665 = 895999) B895999
theorem B3029831 : Blo 794341 3029831 := bstep (se 1 (by rfl) ⟨2272373, by rfl⟩ : syracuseStep 3029831 = 4544747) B4544747
theorem B36846809 : Blo 794341 36846809 := bstep (se 2 (by rfl) ⟨13817553, by rfl⟩ : syracuseStep 36846809 = 27635107) B27635107
theorem B1195385 : Blo 794341 1195385 := bstep (se 2 (by rfl) ⟨448269, by rfl⟩ : syracuseStep 1195385 = 896539) B896539
theorem B104873453 : Blo 794341 104873453 := bstep (se 3 (by rfl) ⟨19663772, by rfl⟩ : syracuseStep 104873453 = 39327545) B39327545
theorem B3030803 : Blo 794341 3030803 := bstep (se 1 (by rfl) ⟨2273102, by rfl⟩ : syracuseStep 3030803 = 4546205) B4546205
theorem B1196015 : Blo 794341 1196015 := bstep (se 1 (by rfl) ⟨897011, by rfl⟩ : syracuseStep 1196015 = 1794023) B1794023
theorem B2015219 : Blo 794341 2015219 := bstep (se 1 (by rfl) ⟨1511414, by rfl⟩ : syracuseStep 2015219 = 3022829) B3022829
theorem B7652231 : Blo 794341 7652231 := bstep (se 1 (by rfl) ⟨5739173, by rfl⟩ : syracuseStep 7652231 = 11478347) B11478347
theorem B19645415 : Blo 794341 19645415 := bstep (se 1 (by rfl) ⟨14734061, by rfl⟩ : syracuseStep 19645415 = 29468123) B29468123
theorem B1197083 : Blo 794341 1197083 := bstep (se 1 (by rfl) ⟨897812, by rfl⟩ : syracuseStep 1197083 = 1795625) B1795625
theorem B20727089 : Blo 794341 20727089 := bstep (se 2 (by rfl) ⟨7772658, by rfl⟩ : syracuseStep 20727089 = 15545317) B15545317
theorem B2016859 : Blo 794341 2016859 := bstep (se 1 (by rfl) ⟨1512644, by rfl⟩ : syracuseStep 2016859 = 3025289) B3025289
theorem B6047783 : Blo 794341 6047783 := bstep (se 1 (by rfl) ⟨4535837, by rfl⟩ : syracuseStep 6047783 = 9071675) B9071675
theorem B32623343 : Blo 794341 32623343 := bstep (se 1 (by rfl) ⟨24467507, by rfl⟩ : syracuseStep 32623343 = 48935015) B48935015
theorem B1789019 : Blo 794341 1789019 := bstep (se 1 (by rfl) ⟨1341764, by rfl⟩ : syracuseStep 1789019 = 2683529) B2683529
theorem B3820655 : Blo 794341 3820655 := bstep (se 1 (by rfl) ⟨2865491, by rfl⟩ : syracuseStep 3820655 = 5730983) B5730983
theorem B1789487 : Blo 794341 1789487 := bstep (se 1 (by rfl) ⟨1342115, by rfl⟩ : syracuseStep 1789487 = 2684231) B2684231
theorem B1789793 : Blo 794341 1789793 := bstep (se 2 (by rfl) ⟨671172, by rfl⟩ : syracuseStep 1789793 = 1342345) B1342345
theorem B2871521 : Blo 794341 2871521 := bstep (se 2 (by rfl) ⟨1076820, by rfl⟩ : syracuseStep 2871521 = 2153641) B2153641
theorem B1593599 : Blo 794341 1593599 := bstep (se 1 (by rfl) ⟨1195199, by rfl⟩ : syracuseStep 1593599 = 2390399) B2390399
theorem B3822079 : Blo 794341 3822079 := bstep (se 1 (by rfl) ⟨2866559, by rfl⟩ : syracuseStep 3822079 = 5733119) B5733119
theorem B1790495 : Blo 794341 1790495 := bstep (se 1 (by rfl) ⟨1342871, by rfl⟩ : syracuseStep 1790495 = 2685743) B2685743
theorem B10179391 : Blo 794341 10179391 := bstep (se 1 (by rfl) ⟨7634543, by rfl⟩ : syracuseStep 10179391 = 15269087) B15269087
theorem B2875051 : Blo 794341 2875051 := bstep (se 1 (by rfl) ⟨2156288, by rfl⟩ : syracuseStep 2875051 = 4312577) B4312577
theorem B10346231 : Blo 794341 10346231 := bstep (se 1 (by rfl) ⟨7759673, by rfl⟩ : syracuseStep 10346231 = 15519347) B15519347
theorem B4022945 : Blo 794341 4022945 := bstep (se 2 (by rfl) ⟨1508604, by rfl⟩ : syracuseStep 4022945 = 3017209) B3017209
theorem B1795283 : Blo 794341 1795283 := bstep (se 1 (by rfl) ⟨1346462, by rfl⟩ : syracuseStep 1795283 = 2692925) B2692925
theorem B6121655 : Blo 794341 6121655 := bstep (se 1 (by rfl) ⟨4591241, by rfl⟩ : syracuseStep 6121655 = 9182483) B9182483
theorem B5728907 : Blo 794341 5728907 := bstep (se 1 (by rfl) ⟨4296680, by rfl⟩ : syracuseStep 5728907 = 8593361) B8593361
theorem B335704637 : Blo 794341 335704637 := bstep (se 3 (by rfl) ⟨62944619, by rfl⟩ : syracuseStep 335704637 = 125889239) B125889239
theorem B1341083 : Blo 794341 1341083 := bstep (se 1 (by rfl) ⟨1005812, by rfl⟩ : syracuseStep 1341083 = 2011625) B2011625
theorem B2685311 : Blo 794341 2685311 := bstep (se 1 (by rfl) ⟨2013983, by rfl⟩ : syracuseStep 2685311 = 4027967) B4027967
theorem B1473643 : Blo 794341 1473643 := bstep (se 1 (by rfl) ⟨1105232, by rfl⟩ : syracuseStep 1473643 = 2210465) B2210465
theorem B1703195 : Blo 794341 1703195 := bstep (se 1 (by rfl) ⟨1277396, by rfl⟩ : syracuseStep 1703195 = 2554793) B2554793
theorem B1343047 : Blo 794341 1343047 := bstep (se 1 (by rfl) ⟨1007285, by rfl⟩ : syracuseStep 1343047 = 2014571) B2014571
theorem B15271091 : Blo 794341 15271091 := bstep (se 1 (by rfl) ⟨11453318, by rfl⟩ : syracuseStep 15271091 = 22906637) B22906637
theorem B4031855 : Blo 794341 4031855 := bstep (se 1 (by rfl) ⟨3023891, by rfl⟩ : syracuseStep 4031855 = 6047783) B6047783
theorem B2689145 : Blo 794341 2689145 := bstep (se 2 (by rfl) ⟨1008429, by rfl⟩ : syracuseStep 2689145 = 2016859) B2016859
theorem B4035581 : Blo 794341 4035581 := bstep (se 3 (by rfl) ⟨756671, by rfl⟩ : syracuseStep 4035581 = 1513343) B1513343
theorem B8623205 : Blo 794341 8623205 := bstep (se 4 (by rfl) ⟨808425, by rfl⟩ : syracuseStep 8623205 = 1616851) B1616851
theorem B13572521 : Blo 794341 13572521 := bstep (se 2 (by rfl) ⟨5089695, by rfl⟩ : syracuseStep 13572521 = 10179391) B10179391
theorem B15277085 : Blo 794341 15277085 := bstep (se 3 (by rfl) ⟨2864453, by rfl⟩ : syracuseStep 15277085 = 5728907) B5728907
theorem B19405901 : Blo 794341 19405901 := bstep (se 3 (by rfl) ⟨3638606, by rfl⟩ : syracuseStep 19405901 = 7277213) B7277213
theorem B4529915 : Blo 794341 4529915 := bstep (se 1 (by rfl) ⟨3397436, by rfl⟩ : syracuseStep 4529915 = 6794873) B6794873
theorem B794791 : Blo 794341 794791 := bstep (se 1 (by rfl) ⟨596093, by rfl⟩ : syracuseStep 794791 = 1192187) B1192187
theorem B795495 : Blo 794341 795495 := bstep (se 1 (by rfl) ⟨596621, by rfl⟩ : syracuseStep 795495 = 1193243) B1193243
theorem B894055 : Blo 794341 894055 := bstep (se 1 (by rfl) ⟨670541, by rfl⟩ : syracuseStep 894055 = 1341083) B1341083
theorem B15345359 : Blo 794341 15345359 := bstep (se 1 (by rfl) ⟨11509019, by rfl⟩ : syracuseStep 15345359 = 23018039) B23018039
theorem B796443 : Blo 794341 796443 := bstep (se 1 (by rfl) ⟨597332, by rfl⟩ : syracuseStep 796443 = 1194665) B1194665
theorem B796923 : Blo 794341 796923 := bstep (se 1 (by rfl) ⟨597692, by rfl⟩ : syracuseStep 796923 = 1195385) B1195385
theorem B797343 : Blo 794341 797343 := bstep (se 1 (by rfl) ⟨598007, by rfl⟩ : syracuseStep 797343 = 1196015) B1196015
theorem B3321043 : Blo 794341 3321043 := bstep (se 1 (by rfl) ⟨2490782, by rfl⟩ : syracuseStep 3321043 = 4981565) B4981565
theorem B798055 : Blo 794341 798055 := bstep (se 1 (by rfl) ⟨598541, by rfl⟩ : syracuseStep 798055 = 1197083) B1197083
theorem B896719 : Blo 794341 896719 := bstep (se 1 (by rfl) ⟨672539, by rfl⟩ : syracuseStep 896719 = 1345079) B1345079
theorem B7647119 : Blo 794341 7647119 := bstep (se 1 (by rfl) ⟨5735339, by rfl⟩ : syracuseStep 7647119 = 11470679) B11470679
theorem B1192679 : Blo 794341 1192679 := bstep (se 1 (by rfl) ⟨894509, by rfl⟩ : syracuseStep 1192679 = 1789019) B1789019
theorem B1192991 : Blo 794341 1192991 := bstep (se 1 (by rfl) ⟨894743, by rfl⟩ : syracuseStep 1192991 = 1789487) B1789487
theorem B1193195 : Blo 794341 1193195 := bstep (se 1 (by rfl) ⟨894896, by rfl⟩ : syracuseStep 1193195 = 1789793) B1789793
theorem B1914347 : Blo 794341 1914347 := bstep (se 1 (by rfl) ⟨1435760, by rfl⟩ : syracuseStep 1914347 = 2871521) B2871521
theorem B1193663 : Blo 794341 1193663 := bstep (se 1 (by rfl) ⟨895247, by rfl⟩ : syracuseStep 1193663 = 1790495) B1790495
theorem B46447187 : Blo 794341 46447187 := bstep (se 1 (by rfl) ⟨34835390, by rfl⟩ : syracuseStep 46447187 = 69670781) B69670781
theorem B4374067 : Blo 794341 4374067 := bstep (se 1 (by rfl) ⟨3280550, by rfl⟩ : syracuseStep 4374067 = 6561101) B6561101
theorem B6897487 : Blo 794341 6897487 := bstep (se 1 (by rfl) ⟨5173115, by rfl⟩ : syracuseStep 6897487 = 10346231) B10346231
theorem B6799247 : Blo 794341 6799247 := bstep (se 1 (by rfl) ⟨5099435, by rfl⟩ : syracuseStep 6799247 = 10198871) B10198871
theorem B5096105 : Blo 794341 5096105 := bstep (se 2 (by rfl) ⟨1911039, by rfl⟩ : syracuseStep 5096105 = 3822079) B3822079
theorem B1196855 : Blo 794341 1196855 := bstep (se 1 (by rfl) ⟨897641, by rfl⟩ : syracuseStep 1196855 = 1795283) B1795283
theorem B10896553 : Blo 794341 10896553 := bstep (se 2 (by rfl) ⟨4086207, by rfl⟩ : syracuseStep 10896553 = 8172415) B8172415
theorem B4081103 : Blo 794341 4081103 := bstep (se 1 (by rfl) ⟨3060827, by rfl⟩ : syracuseStep 4081103 = 6121655) B6121655
theorem B2016809 : Blo 794341 2016809 := bstep (se 2 (by rfl) ⟨756303, by rfl⟩ : syracuseStep 2016809 = 1512607) B1512607
theorem B2017001 : Blo 794341 2017001 := bstep (se 2 (by rfl) ⟨756375, by rfl⟩ : syracuseStep 2017001 = 1512751) B1512751
theorem B4310783 : Blo 794341 4310783 := bstep (se 1 (by rfl) ⟨3233087, by rfl⟩ : syracuseStep 4310783 = 6466175) B6466175
theorem B1790207 : Blo 794341 1790207 := bstep (se 1 (by rfl) ⟨1342655, by rfl⟩ : syracuseStep 1790207 = 2685311) B2685311
theorem B2019887 : Blo 794341 2019887 := bstep (se 1 (by rfl) ⟨1514915, by rfl⟩ : syracuseStep 2019887 = 3029831) B3029831
theorem B1790729 : Blo 794341 1790729 := bstep (se 2 (by rfl) ⟨671523, by rfl⟩ : syracuseStep 1790729 = 1343047) B1343047
theorem B24564539 : Blo 794341 24564539 := bstep (se 1 (by rfl) ⟨18423404, by rfl⟩ : syracuseStep 24564539 = 36846809) B36846809
theorem B1135463 : Blo 794341 1135463 := bstep (se 1 (by rfl) ⟨851597, by rfl⟩ : syracuseStep 1135463 = 1703195) B1703195
theorem B69915635 : Blo 794341 69915635 := bstep (se 1 (by rfl) ⟨52436726, by rfl⟩ : syracuseStep 69915635 = 104873453) B104873453
theorem B2020535 : Blo 794341 2020535 := bstep (se 1 (by rfl) ⟨1515401, by rfl⟩ : syracuseStep 2020535 = 3030803) B3030803
theorem B5101487 : Blo 794341 5101487 := bstep (se 1 (by rfl) ⟨3826115, by rfl⟩ : syracuseStep 5101487 = 7652231) B7652231
theorem B13096943 : Blo 794341 13096943 := bstep (se 1 (by rfl) ⟨9822707, by rfl⟩ : syracuseStep 13096943 = 19645415) B19645415
theorem B4249597 : Blo 794341 4249597 := bstep (se 3 (by rfl) ⟨796799, by rfl⟩ : syracuseStep 4249597 = 1593599) B1593599
theorem B13818059 : Blo 794341 13818059 := bstep (se 1 (by rfl) ⟨10363544, by rfl⟩ : syracuseStep 13818059 = 20727089) B20727089
theorem B1006015 : Blo 794341 1006015 := bstep (se 1 (by rfl) ⟨754511, by rfl⟩ : syracuseStep 1006015 = 1509023) B1509023
theorem B21748895 : Blo 794341 21748895 := bstep (se 1 (by rfl) ⟨16311671, by rfl⟩ : syracuseStep 21748895 = 32623343) B32623343
theorem B2547001 : Blo 794341 2547001 := bstep (se 2 (by rfl) ⟨955125, by rfl⟩ : syracuseStep 2547001 = 1910251) B1910251
theorem B3235261 : Blo 794341 3235261 := bstep (se 3 (by rfl) ⟨606611, by rfl⟩ : syracuseStep 3235261 = 1213223) B1213223
theorem B4021811 : Blo 794341 4021811 := bstep (se 1 (by rfl) ⟨3016358, by rfl⟩ : syracuseStep 4021811 = 6032717) B6032717
theorem B8281919 : Blo 794341 8281919 := bstep (se 1 (by rfl) ⟨6211439, by rfl⟩ : syracuseStep 8281919 = 12422879) B12422879
theorem B1794095 : Blo 794341 1794095 := bstep (se 1 (by rfl) ⟨1345571, by rfl⟩ : syracuseStep 1794095 = 2691143) B2691143
theorem B4023107 : Blo 794341 4023107 := bstep (se 1 (by rfl) ⟨3017330, by rfl⟩ : syracuseStep 4023107 = 6034661) B6034661
theorem B1272809 : Blo 794341 1272809 := bstep (se 2 (by rfl) ⟨477303, by rfl⟩ : syracuseStep 1272809 = 954607) B954607
theorem B2681963 : Blo 794341 2681963 := bstep (se 1 (by rfl) ⟨2011472, by rfl⟩ : syracuseStep 2681963 = 4022945) B4022945
theorem B7859429 : Blo 794341 7859429 := bstep (se 4 (by rfl) ⟨736821, by rfl⟩ : syracuseStep 7859429 = 1473643) B1473643
theorem B6909887 : Blo 794341 6909887 := bstep (se 1 (by rfl) ⟨5182415, by rfl⟩ : syracuseStep 6909887 = 10364831) B10364831
theorem B4026671 : Blo 794341 4026671 := bstep (se 1 (by rfl) ⟨3020003, by rfl⟩ : syracuseStep 4026671 = 6040007) B6040007
theorem B10188413 : Blo 794341 10188413 := bstep (se 3 (by rfl) ⟨1910327, by rfl⟩ : syracuseStep 10188413 = 3820655) B3820655
theorem B223803091 : Blo 794341 223803091 := bstep (se 1 (by rfl) ⟨167852318, by rfl⟩ : syracuseStep 223803091 = 335704637) B335704637
theorem B3833401 : Blo 794341 3833401 := bstep (se 2 (by rfl) ⟨1437525, by rfl⟩ : syracuseStep 3833401 = 2875051) B2875051
theorem B1343479 : Blo 794341 1343479 := bstep (se 1 (by rfl) ⟨1007609, by rfl⟩ : syracuseStep 1343479 = 2015219) B2015219
theorem B2687903 : Blo 794341 2687903 := bstep (se 1 (by rfl) ⟨2015927, by rfl⟩ : syracuseStep 2687903 = 4031855) B4031855
theorem B2720735 : Blo 794341 2720735 := bstep (se 1 (by rfl) ⟨2040551, by rfl⟩ : syracuseStep 2720735 = 4081103) B4081103
theorem B1344539 : Blo 794341 1344539 := bstep (se 1 (by rfl) ⟨1008404, by rfl⟩ : syracuseStep 1344539 = 2016809) B2016809
theorem B1344667 : Blo 794341 1344667 := bstep (se 1 (by rfl) ⟨1008500, by rfl⟩ : syracuseStep 1344667 = 2017001) B2017001
theorem B1346591 : Blo 794341 1346591 := bstep (se 1 (by rfl) ⟨1009943, by rfl⟩ : syracuseStep 1346591 = 2019887) B2019887
theorem B2690387 : Blo 794341 2690387 := bstep (se 1 (by rfl) ⟨2017790, by rfl⟩ : syracuseStep 2690387 = 4035581) B4035581
theorem B1347023 : Blo 794341 1347023 := bstep (se 1 (by rfl) ⟨1010267, by rfl⟩ : syracuseStep 1347023 = 2020535) B2020535
theorem B9212039 : Blo 794341 9212039 := bstep (se 1 (by rfl) ⟨6909029, by rfl⟩ : syracuseStep 9212039 = 13818059) B13818059
theorem B9048347 : Blo 794341 9048347 := bstep (se 1 (by rfl) ⟨6786260, by rfl⟩ : syracuseStep 9048347 = 13572521) B13572521
theorem B3019943 : Blo 794341 3019943 := bstep (se 1 (by rfl) ⟨2264957, by rfl⟩ : syracuseStep 3019943 = 4529915) B4529915
theorem B10230239 : Blo 794341 10230239 := bstep (se 1 (by rfl) ⟨7672679, by rfl⟩ : syracuseStep 10230239 = 15345359) B15345359
theorem B795119 : Blo 794341 795119 := bstep (se 1 (by rfl) ⟨596339, by rfl⟩ : syracuseStep 795119 = 1192679) B1192679
theorem B795327 : Blo 794341 795327 := bstep (se 1 (by rfl) ⟨596495, by rfl⟩ : syracuseStep 795327 = 1192991) B1192991
theorem B795463 : Blo 794341 795463 := bstep (se 1 (by rfl) ⟨596597, by rfl⟩ : syracuseStep 795463 = 1193195) B1193195
theorem B6792275 : Blo 794341 6792275 := bstep (se 1 (by rfl) ⟨5094206, by rfl⟩ : syracuseStep 6792275 = 10188413) B10188413
theorem B1193616485 : Blo 794341 1193616485 := bstep (se 4 (by rfl) ⟨111901545, by rfl⟩ : syracuseStep 1193616485 = 223803091) B223803091
theorem B795775 : Blo 794341 795775 := bstep (se 1 (by rfl) ⟨596831, by rfl⟩ : syracuseStep 795775 = 1193663) B1193663
theorem B18426365 : Blo 794341 18426365 := bstep (se 3 (by rfl) ⟨3454943, by rfl⟩ : syracuseStep 18426365 = 6909887) B6909887
theorem B4532831 : Blo 794341 4532831 := bstep (se 1 (by rfl) ⟨3399623, by rfl⟩ : syracuseStep 4532831 = 6799247) B6799247
theorem B797903 : Blo 794341 797903 := bstep (se 1 (by rfl) ⟨598427, by rfl⟩ : syracuseStep 797903 = 1196855) B1196855
theorem B1192073 : Blo 794341 1192073 := bstep (se 2 (by rfl) ⟨447027, by rfl⟩ : syracuseStep 1192073 = 894055) B894055
theorem B14528737 : Blo 794341 14528737 := bstep (se 2 (by rfl) ⟨5448276, by rfl⟩ : syracuseStep 14528737 = 10896553) B10896553
theorem B3027901 : Blo 794341 3027901 := bstep (se 3 (by rfl) ⟨567731, by rfl⟩ : syracuseStep 3027901 = 1135463) B1135463
theorem B1193471 : Blo 794341 1193471 := bstep (se 1 (by rfl) ⟨895103, by rfl⟩ : syracuseStep 1193471 = 1790207) B1790207
theorem B1193819 : Blo 794341 1193819 := bstep (se 1 (by rfl) ⟨895364, by rfl⟩ : syracuseStep 1193819 = 1790729) B1790729
theorem B46610423 : Blo 794341 46610423 := bstep (se 1 (by rfl) ⟨34957817, by rfl⟩ : syracuseStep 46610423 = 69915635) B69915635
theorem B5748803 : Blo 794341 5748803 := bstep (se 1 (by rfl) ⟨4311602, by rfl⟩ : syracuseStep 5748803 = 8623205) B8623205
theorem B8731295 : Blo 794341 8731295 := bstep (se 1 (by rfl) ⟨6548471, by rfl⟩ : syracuseStep 8731295 = 13096943) B13096943
theorem B14499263 : Blo 794341 14499263 := bstep (se 1 (by rfl) ⟨10874447, by rfl⟩ : syracuseStep 14499263 = 21748895) B21748895
theorem B1195625 : Blo 794341 1195625 := bstep (se 2 (by rfl) ⟨448359, by rfl⟩ : syracuseStep 1195625 = 896719) B896719
theorem B5521279 : Blo 794341 5521279 := bstep (se 1 (by rfl) ⟨4140959, by rfl⟩ : syracuseStep 5521279 = 8281919) B8281919
theorem B1196063 : Blo 794341 1196063 := bstep (se 1 (by rfl) ⟨897047, by rfl⟩ : syracuseStep 1196063 = 1794095) B1794095
theorem B495436661 : Blo 794341 495436661 := bstep (se 5 (by rfl) ⟨23223593, by rfl⟩ : syracuseStep 495436661 = 46447187) B46447187
theorem B17712229 : Blo 794341 17712229 := bstep (se 4 (by rfl) ⟨1660521, by rfl⟩ : syracuseStep 17712229 = 3321043) B3321043
theorem B1787975 : Blo 794341 1787975 := bstep (se 1 (by rfl) ⟨1340981, by rfl⟩ : syracuseStep 1787975 = 2681963) B2681963
theorem B5098079 : Blo 794341 5098079 := bstep (se 1 (by rfl) ⟨3823559, by rfl⟩ : syracuseStep 5098079 = 7647119) B7647119
theorem B3396001 : Blo 794341 3396001 := bstep (se 2 (by rfl) ⟨1273500, by rfl⟩ : syracuseStep 3396001 = 2547001) B2547001
theorem B4313681 : Blo 794341 4313681 := bstep (se 2 (by rfl) ⟨1617630, by rfl⟩ : syracuseStep 4313681 = 3235261) B3235261
theorem B9196649 : Blo 794341 9196649 := bstep (se 2 (by rfl) ⟨3448743, by rfl⟩ : syracuseStep 9196649 = 6897487) B6897487
theorem B1791305 : Blo 794341 1791305 := bstep (se 2 (by rfl) ⟨671739, by rfl⟩ : syracuseStep 1791305 = 1343479) B1343479
theorem B3397403 : Blo 794341 3397403 := bstep (se 1 (by rfl) ⟨2548052, by rfl⟩ : syracuseStep 3397403 = 5096105) B5096105
theorem B10180727 : Blo 794341 10180727 := bstep (se 1 (by rfl) ⟨7635545, by rfl⟩ : syracuseStep 10180727 = 15271091) B15271091
theorem B2873855 : Blo 794341 2873855 := bstep (se 1 (by rfl) ⟨2155391, by rfl⟩ : syracuseStep 2873855 = 4310783) B4310783
theorem B1792763 : Blo 794341 1792763 := bstep (se 1 (by rfl) ⟨1344572, by rfl⟩ : syracuseStep 1792763 = 2689145) B2689145
theorem B16376359 : Blo 794341 16376359 := bstep (se 1 (by rfl) ⟨12282269, by rfl⟩ : syracuseStep 16376359 = 24564539) B24564539
theorem B3400991 : Blo 794341 3400991 := bstep (se 1 (by rfl) ⟨2550743, by rfl⟩ : syracuseStep 3400991 = 5101487) B5101487
theorem B10184723 : Blo 794341 10184723 := bstep (se 1 (by rfl) ⟨7638542, by rfl⟩ : syracuseStep 10184723 = 15277085) B15277085
theorem B12937267 : Blo 794341 12937267 := bstep (se 1 (by rfl) ⟨9702950, by rfl⟩ : syracuseStep 12937267 = 19405901) B19405901
theorem B2681207 : Blo 794341 2681207 := bstep (se 1 (by rfl) ⟨2010905, by rfl⟩ : syracuseStep 2681207 = 4021811) B4021811
theorem B2682071 : Blo 794341 2682071 := bstep (se 1 (by rfl) ⟨2011553, by rfl⟩ : syracuseStep 2682071 = 4023107) B4023107
theorem B848539 : Blo 794341 848539 := bstep (se 1 (by rfl) ⟨636404, by rfl⟩ : syracuseStep 848539 = 1272809) B1272809
theorem B5239619 : Blo 794341 5239619 := bstep (se 1 (by rfl) ⟨3929714, by rfl⟩ : syracuseStep 5239619 = 7859429) B7859429
theorem B5666129 : Blo 794341 5666129 := bstep (se 2 (by rfl) ⟨2124798, by rfl⟩ : syracuseStep 5666129 = 4249597) B4249597
theorem B2684447 : Blo 794341 2684447 := bstep (se 1 (by rfl) ⟨2013335, by rfl⟩ : syracuseStep 2684447 = 4026671) B4026671
theorem B1341353 : Blo 794341 1341353 := bstep (se 2 (by rfl) ⟨503007, by rfl⟩ : syracuseStep 1341353 = 1006015) B1006015
theorem B1276231 : Blo 794341 1276231 := bstep (se 1 (by rfl) ⟨957173, by rfl⟩ : syracuseStep 1276231 = 1914347) B1914347
theorem B5832089 : Blo 794341 5832089 := bstep (se 2 (by rfl) ⟨2187033, by rfl⟩ : syracuseStep 5832089 = 4374067) B4374067
theorem B5111201 : Blo 794341 5111201 := bstep (se 2 (by rfl) ⟨1916700, by rfl⟩ : syracuseStep 5111201 = 3833401) B3833401
theorem B6032231 : Blo 794341 6032231 := bstep (se 1 (by rfl) ⟨4524173, by rfl⟩ : syracuseStep 6032231 = 9048347) B9048347
theorem B6131099 : Blo 794341 6131099 := bstep (se 1 (by rfl) ⟨4598324, by rfl⟩ : syracuseStep 6131099 = 9196649) B9196649
theorem B4525541 : Blo 794341 4525541 := bstep (se 4 (by rfl) ⟨424269, by rfl⟩ : syracuseStep 4525541 = 848539) B848539
theorem B2264935 : Blo 794341 2264935 := bstep (se 1 (by rfl) ⟨1698701, by rfl⟩ : syracuseStep 2264935 = 3397403) B3397403
theorem B6787151 : Blo 794341 6787151 := bstep (se 1 (by rfl) ⟨5090363, by rfl⟩ : syracuseStep 6787151 = 10180727) B10180727
theorem B6820159 : Blo 794341 6820159 := bstep (se 1 (by rfl) ⟨5115119, by rfl⟩ : syracuseStep 6820159 = 10230239) B10230239
theorem B19371649 : Blo 794341 19371649 := bstep (se 2 (by rfl) ⟨7264368, by rfl⟩ : syracuseStep 19371649 = 14528737) B14528737
theorem B4528001 : Blo 794341 4528001 := bstep (se 2 (by rfl) ⟨1698000, by rfl⟩ : syracuseStep 4528001 = 3396001) B3396001
theorem B4528183 : Blo 794341 4528183 := bstep (se 1 (by rfl) ⟨3396137, by rfl⟩ : syracuseStep 4528183 = 6792275) B6792275
theorem B795744323 : Blo 794341 795744323 := bstep (se 1 (by rfl) ⟨596808242, by rfl⟩ : syracuseStep 795744323 = 1193616485) B1193616485
theorem B2267327 : Blo 794341 2267327 := bstep (se 1 (by rfl) ⟨1700495, by rfl⟩ : syracuseStep 2267327 = 3400991) B3400991
theorem B4037201 : Blo 794341 4037201 := bstep (se 2 (by rfl) ⟨1513950, by rfl⟩ : syracuseStep 4037201 = 3027901) B3027901
theorem B6789815 : Blo 794341 6789815 := bstep (se 1 (by rfl) ⟨5092361, by rfl⟩ : syracuseStep 6789815 = 10184723) B10184723
theorem B3021887 : Blo 794341 3021887 := bstep (se 1 (by rfl) ⟨2266415, by rfl⟩ : syracuseStep 3021887 = 4532831) B4532831
theorem B794715 : Blo 794341 794715 := bstep (se 1 (by rfl) ⟨596036, by rfl⟩ : syracuseStep 794715 = 1192073) B1192073
theorem B3777419 : Blo 794341 3777419 := bstep (se 1 (by rfl) ⟨2833064, by rfl⟩ : syracuseStep 3777419 = 5666129) B5666129
theorem B795647 : Blo 794341 795647 := bstep (se 1 (by rfl) ⟨596735, by rfl⟩ : syracuseStep 795647 = 1193471) B1193471
theorem B795879 : Blo 794341 795879 := bstep (se 1 (by rfl) ⟨596909, by rfl⟩ : syracuseStep 795879 = 1193819) B1193819
theorem B894235 : Blo 794341 894235 := bstep (se 1 (by rfl) ⟨670676, by rfl⟩ : syracuseStep 894235 = 1341353) B1341353
theorem B31073615 : Blo 794341 31073615 := bstep (se 1 (by rfl) ⟨23305211, by rfl⟩ : syracuseStep 31073615 = 46610423) B46610423
theorem B797083 : Blo 794341 797083 := bstep (se 1 (by rfl) ⟨597812, by rfl⟩ : syracuseStep 797083 = 1195625) B1195625
theorem B797375 : Blo 794341 797375 := bstep (se 1 (by rfl) ⟨598031, by rfl⟩ : syracuseStep 797375 = 1196063) B1196063
theorem B1813823 : Blo 794341 1813823 := bstep (se 1 (by rfl) ⟨1360367, by rfl⟩ : syracuseStep 1813823 = 2720735) B2720735
theorem B896359 : Blo 794341 896359 := bstep (se 1 (by rfl) ⟨672269, by rfl⟩ : syracuseStep 896359 = 1344539) B1344539
theorem B21835145 : Blo 794341 21835145 := bstep (se 2 (by rfl) ⟨8188179, by rfl⟩ : syracuseStep 21835145 = 16376359) B16376359
theorem B1191983 : Blo 794341 1191983 := bstep (se 1 (by rfl) ⟨893987, by rfl⟩ : syracuseStep 1191983 = 1787975) B1787975
theorem B897727 : Blo 794341 897727 := bstep (se 1 (by rfl) ⟨673295, by rfl⟩ : syracuseStep 897727 = 1346591) B1346591
theorem B898015 : Blo 794341 898015 := bstep (se 1 (by rfl) ⟨673511, by rfl⟩ : syracuseStep 898015 = 1347023) B1347023
theorem B17249689 : Blo 794341 17249689 := bstep (se 2 (by rfl) ⟨6468633, by rfl⟩ : syracuseStep 17249689 = 12937267) B12937267
theorem B6141359 : Blo 794341 6141359 := bstep (se 1 (by rfl) ⟨4606019, by rfl⟩ : syracuseStep 6141359 = 9212039) B9212039
theorem B2013295 : Blo 794341 2013295 := bstep (se 1 (by rfl) ⟨1509971, by rfl⟩ : syracuseStep 2013295 = 3019943) B3019943
theorem B1194203 : Blo 794341 1194203 := bstep (se 1 (by rfl) ⟨895652, by rfl⟩ : syracuseStep 1194203 = 1791305) B1791305
theorem B1915903 : Blo 794341 1915903 := bstep (se 1 (by rfl) ⟨1436927, by rfl⟩ : syracuseStep 1915903 = 2873855) B2873855
theorem B1195175 : Blo 794341 1195175 := bstep (se 1 (by rfl) ⟨896381, by rfl⟩ : syracuseStep 1195175 = 1792763) B1792763
theorem B1787471 : Blo 794341 1787471 := bstep (se 1 (by rfl) ⟨1340603, by rfl⟩ : syracuseStep 1787471 = 2681207) B2681207
theorem B1788047 : Blo 794341 1788047 := bstep (se 1 (by rfl) ⟨1341035, by rfl⟩ : syracuseStep 1788047 = 2682071) B2682071
theorem B3493079 : Blo 794341 3493079 := bstep (se 1 (by rfl) ⟨2619809, by rfl⟩ : syracuseStep 3493079 = 5239619) B5239619
theorem B1789631 : Blo 794341 1789631 := bstep (se 1 (by rfl) ⟨1342223, by rfl⟩ : syracuseStep 1789631 = 2684447) B2684447
theorem B5820863 : Blo 794341 5820863 := bstep (se 1 (by rfl) ⟨4365647, by rfl⟩ : syracuseStep 5820863 = 8731295) B8731295
theorem B3888059 : Blo 794341 3888059 := bstep (se 1 (by rfl) ⟨2916044, by rfl⟩ : syracuseStep 3888059 = 5832089) B5832089
theorem B7361705 : Blo 794341 7361705 := bstep (se 2 (by rfl) ⟨2760639, by rfl⟩ : syracuseStep 7361705 = 5521279) B5521279
theorem B330291107 : Blo 794341 330291107 := bstep (se 1 (by rfl) ⟨247718330, by rfl⟩ : syracuseStep 330291107 = 495436661) B495436661
theorem B1791935 : Blo 794341 1791935 := bstep (se 1 (by rfl) ⟨1343951, by rfl⟩ : syracuseStep 1791935 = 2687903) B2687903
theorem B23616305 : Blo 794341 23616305 := bstep (se 2 (by rfl) ⟨8856114, by rfl⟩ : syracuseStep 23616305 = 17712229) B17712229
theorem B1792889 : Blo 794341 1792889 := bstep (se 2 (by rfl) ⟨672333, by rfl⟩ : syracuseStep 1792889 = 1344667) B1344667
theorem B3398719 : Blo 794341 3398719 := bstep (se 1 (by rfl) ⟨2549039, by rfl⟩ : syracuseStep 3398719 = 5098079) B5098079
theorem B1793591 : Blo 794341 1793591 := bstep (se 1 (by rfl) ⟨1345193, by rfl⟩ : syracuseStep 1793591 = 2690387) B2690387
theorem B2875787 : Blo 794341 2875787 := bstep (se 1 (by rfl) ⟨2156840, by rfl⟩ : syracuseStep 2875787 = 4313681) B4313681
theorem B12284243 : Blo 794341 12284243 := bstep (se 1 (by rfl) ⟨9213182, by rfl⟩ : syracuseStep 12284243 = 18426365) B18426365
theorem B1701641 : Blo 794341 1701641 := bstep (se 2 (by rfl) ⟨638115, by rfl⟩ : syracuseStep 1701641 = 1276231) B1276231
theorem B3832535 : Blo 794341 3832535 := bstep (se 1 (by rfl) ⟨2874401, by rfl⟩ : syracuseStep 3832535 = 5748803) B5748803
theorem B3407467 : Blo 794341 3407467 := bstep (se 1 (by rfl) ⟨2555600, by rfl⟩ : syracuseStep 3407467 = 5111201) B5111201
theorem B9666175 : Blo 794341 9666175 := bstep (se 1 (by rfl) ⟨7249631, by rfl⟩ : syracuseStep 9666175 = 14499263) B14499263
theorem B37259509 : Blo 794341 37259509 := bstep (se 5 (by rfl) ⟨1746539, by rfl⟩ : syracuseStep 37259509 = 3493079) B3493079
theorem B3017027 : Blo 794341 3017027 := bstep (se 1 (by rfl) ⟨2262770, by rfl⟩ : syracuseStep 3017027 = 4525541) B4525541
theorem B4524767 : Blo 794341 4524767 := bstep (se 1 (by rfl) ⟨3393575, by rfl⟩ : syracuseStep 4524767 = 6787151) B6787151
theorem B3018667 : Blo 794341 3018667 := bstep (se 1 (by rfl) ⟨2264000, by rfl⟩ : syracuseStep 3018667 = 4528001) B4528001
theorem B1511551 : Blo 794341 1511551 := bstep (se 1 (by rfl) ⟨1133663, by rfl⟩ : syracuseStep 1511551 = 2267327) B2267327
theorem B2691467 : Blo 794341 2691467 := bstep (se 1 (by rfl) ⟨2018600, by rfl⟩ : syracuseStep 2691467 = 4037201) B4037201
theorem B4526543 : Blo 794341 4526543 := bstep (se 1 (by rfl) ⟨3394907, by rfl⟩ : syracuseStep 4526543 = 6789815) B6789815
theorem B3019913 : Blo 794341 3019913 := bstep (se 2 (by rfl) ⟨1132467, by rfl⟩ : syracuseStep 3019913 = 2264935) B2264935
theorem B20715743 : Blo 794341 20715743 := bstep (se 1 (by rfl) ⟨15536807, by rfl⟩ : syracuseStep 20715743 = 31073615) B31073615
theorem B25828865 : Blo 794341 25828865 := bstep (se 2 (by rfl) ⟨9685824, by rfl⟩ : syracuseStep 25828865 = 19371649) B19371649
theorem B14556763 : Blo 794341 14556763 := bstep (se 1 (by rfl) ⟨10917572, by rfl⟩ : syracuseStep 14556763 = 21835145) B21835145
theorem B794655 : Blo 794341 794655 := bstep (se 1 (by rfl) ⟨595991, by rfl⟩ : syracuseStep 794655 = 1191983) B1191983
theorem B6037577 : Blo 794341 6037577 := bstep (se 2 (by rfl) ⟨2264091, by rfl⟩ : syracuseStep 6037577 = 4528183) B4528183
theorem B4531625 : Blo 794341 4531625 := bstep (se 2 (by rfl) ⟨1699359, by rfl⟩ : syracuseStep 4531625 = 3398719) B3398719
theorem B796135 : Blo 794341 796135 := bstep (se 1 (by rfl) ⟨597101, by rfl⟩ : syracuseStep 796135 = 1194203) B1194203
theorem B796783 : Blo 794341 796783 := bstep (se 1 (by rfl) ⟨597587, by rfl⟩ : syracuseStep 796783 = 1195175) B1195175
theorem B12888233 : Blo 794341 12888233 := bstep (se 2 (by rfl) ⟨4833087, by rfl⟩ : syracuseStep 12888233 = 9666175) B9666175
theorem B1191647 : Blo 794341 1191647 := bstep (se 1 (by rfl) ⟨893735, by rfl⟩ : syracuseStep 1191647 = 1787471) B1787471
theorem B1192031 : Blo 794341 1192031 := bstep (se 1 (by rfl) ⟨894023, by rfl⟩ : syracuseStep 1192031 = 1788047) B1788047
theorem B1192313 : Blo 794341 1192313 := bstep (se 2 (by rfl) ⟨447117, by rfl⟩ : syracuseStep 1192313 = 894235) B894235
theorem B10073117 : Blo 794341 10073117 := bstep (se 3 (by rfl) ⟨1888709, by rfl⟩ : syracuseStep 10073117 = 3777419) B3777419
theorem B1193087 : Blo 794341 1193087 := bstep (se 1 (by rfl) ⟨894815, by rfl⟩ : syracuseStep 1193087 = 1789631) B1789631
theorem B10368157 : Blo 794341 10368157 := bstep (se 3 (by rfl) ⟨1944029, by rfl⟩ : syracuseStep 10368157 = 3888059) B3888059
theorem B1194623 : Blo 794341 1194623 := bstep (se 1 (by rfl) ⟨895967, by rfl⟩ : syracuseStep 1194623 = 1791935) B1791935
theorem B530496215 : Blo 794341 530496215 := bstep (se 1 (by rfl) ⟨397872161, by rfl⟩ : syracuseStep 530496215 = 795744323) B795744323
theorem B1195145 : Blo 794341 1195145 := bstep (se 2 (by rfl) ⟨448179, by rfl⟩ : syracuseStep 1195145 = 896359) B896359
theorem B15744203 : Blo 794341 15744203 := bstep (se 1 (by rfl) ⟨11808152, by rfl⟩ : syracuseStep 15744203 = 23616305) B23616305
theorem B1195259 : Blo 794341 1195259 := bstep (se 1 (by rfl) ⟨896444, by rfl⟩ : syracuseStep 1195259 = 1792889) B1792889
theorem B2014591 : Blo 794341 2014591 := bstep (se 1 (by rfl) ⟨1510943, by rfl⟩ : syracuseStep 2014591 = 3021887) B3021887
theorem B1195727 : Blo 794341 1195727 := bstep (se 1 (by rfl) ⟨896795, by rfl⟩ : syracuseStep 1195727 = 1793591) B1793591
theorem B1917191 : Blo 794341 1917191 := bstep (se 1 (by rfl) ⟨1437893, by rfl⟩ : syracuseStep 1917191 = 2875787) B2875787
theorem B9093545 : Blo 794341 9093545 := bstep (se 2 (by rfl) ⟨3410079, by rfl⟩ : syracuseStep 9093545 = 6820159) B6820159
theorem B1196969 : Blo 794341 1196969 := bstep (se 2 (by rfl) ⟨448863, by rfl⟩ : syracuseStep 1196969 = 897727) B897727
theorem B1197353 : Blo 794341 1197353 := bstep (se 2 (by rfl) ⟨449007, by rfl⟩ : syracuseStep 1197353 = 898015) B898015
theorem B1134427 : Blo 794341 1134427 := bstep (se 1 (by rfl) ⟨850820, by rfl⟩ : syracuseStep 1134427 = 1701641) B1701641
theorem B4543289 : Blo 794341 4543289 := bstep (se 2 (by rfl) ⟨1703733, by rfl⟩ : syracuseStep 4543289 = 3407467) B3407467
theorem B15522301 : Blo 794341 15522301 := bstep (se 3 (by rfl) ⟨2910431, by rfl⟩ : syracuseStep 15522301 = 5820863) B5820863
theorem B4021487 : Blo 794341 4021487 := bstep (se 1 (by rfl) ⟨3016115, by rfl⟩ : syracuseStep 4021487 = 6032231) B6032231
theorem B4907803 : Blo 794341 4907803 := bstep (se 1 (by rfl) ⟨3680852, by rfl⟩ : syracuseStep 4907803 = 7361705) B7361705
theorem B220194071 : Blo 794341 220194071 := bstep (se 1 (by rfl) ⟨165145553, by rfl⟩ : syracuseStep 220194071 = 330291107) B330291107
theorem B22999585 : Blo 794341 22999585 := bstep (se 2 (by rfl) ⟨8624844, by rfl⟩ : syracuseStep 22999585 = 17249689) B17249689
theorem B10220093 : Blo 794341 10220093 := bstep (se 3 (by rfl) ⟨1916267, by rfl⟩ : syracuseStep 10220093 = 3832535) B3832535
theorem B1209215 : Blo 794341 1209215 := bstep (se 1 (by rfl) ⟨906911, by rfl⟩ : syracuseStep 1209215 = 1813823) B1813823
theorem B2684393 : Blo 794341 2684393 := bstep (se 2 (by rfl) ⟨1006647, by rfl⟩ : syracuseStep 2684393 = 2013295) B2013295
theorem B8189495 : Blo 794341 8189495 := bstep (se 1 (by rfl) ⟨6142121, by rfl⟩ : syracuseStep 8189495 = 12284243) B12284243
theorem B4094239 : Blo 794341 4094239 := bstep (se 1 (by rfl) ⟨3070679, by rfl⟩ : syracuseStep 4094239 = 6141359) B6141359
theorem B16349597 : Blo 794341 16349597 := bstep (se 3 (by rfl) ⟨3065549, by rfl⟩ : syracuseStep 16349597 = 6131099) B6131099
theorem B2554537 : Blo 794341 2554537 := bstep (se 2 (by rfl) ⟨957951, by rfl⟩ : syracuseStep 2554537 = 1915903) B1915903
theorem B1278127 : Blo 794341 1278127 := bstep (se 1 (by rfl) ⟨958595, by rfl⟩ : syracuseStep 1278127 = 1917191) B1917191
theorem B6062363 : Blo 794341 6062363 := bstep (se 1 (by rfl) ⟨4546772, by rfl⟩ : syracuseStep 6062363 = 9093545) B9093545
theorem B3016511 : Blo 794341 3016511 := bstep (se 1 (by rfl) ⟨2262383, by rfl⟩ : syracuseStep 3016511 = 4524767) B4524767
theorem B3017695 : Blo 794341 3017695 := bstep (se 1 (by rfl) ⟨2263271, by rfl⟩ : syracuseStep 3017695 = 4526543) B4526543
theorem B49679345 : Blo 794341 49679345 := bstep (se 2 (by rfl) ⟨18629754, by rfl⟩ : syracuseStep 49679345 = 37259509) B37259509
theorem B1512569 : Blo 794341 1512569 := bstep (se 2 (by rfl) ⟨567213, by rfl⟩ : syracuseStep 1512569 = 1134427) B1134427
theorem B3021083 : Blo 794341 3021083 := bstep (se 1 (by rfl) ⟨2265812, by rfl⟩ : syracuseStep 3021083 = 4531625) B4531625
theorem B8592155 : Blo 794341 8592155 := bstep (se 1 (by rfl) ⟨6444116, by rfl⟩ : syracuseStep 8592155 = 12888233) B12888233
theorem B794431 : Blo 794341 794431 := bstep (se 1 (by rfl) ⟨595823, by rfl⟩ : syracuseStep 794431 = 1191647) B1191647
theorem B794687 : Blo 794341 794687 := bstep (se 1 (by rfl) ⟨596015, by rfl⟩ : syracuseStep 794687 = 1192031) B1192031
theorem B794875 : Blo 794341 794875 := bstep (se 1 (by rfl) ⟨596156, by rfl⟩ : syracuseStep 794875 = 1192313) B1192313
theorem B795391 : Blo 794341 795391 := bstep (se 1 (by rfl) ⟨596543, by rfl⟩ : syracuseStep 795391 = 1193087) B1193087
theorem B796415 : Blo 794341 796415 := bstep (se 1 (by rfl) ⟨597311, by rfl⟩ : syracuseStep 796415 = 1194623) B1194623
theorem B796763 : Blo 794341 796763 := bstep (se 1 (by rfl) ⟨597572, by rfl⟩ : syracuseStep 796763 = 1195145) B1195145
theorem B19409017 : Blo 794341 19409017 := bstep (se 2 (by rfl) ⟨7278381, by rfl⟩ : syracuseStep 19409017 = 14556763) B14556763
theorem B10496135 : Blo 794341 10496135 := bstep (se 1 (by rfl) ⟨7872101, by rfl⟩ : syracuseStep 10496135 = 15744203) B15744203
theorem B796839 : Blo 794341 796839 := bstep (se 1 (by rfl) ⟨597629, by rfl⟩ : syracuseStep 796839 = 1195259) B1195259
theorem B797151 : Blo 794341 797151 := bstep (se 1 (by rfl) ⟨597863, by rfl⟩ : syracuseStep 797151 = 1195727) B1195727
theorem B797979 : Blo 794341 797979 := bstep (se 1 (by rfl) ⟨598484, by rfl⟩ : syracuseStep 797979 = 1196969) B1196969
theorem B798235 : Blo 794341 798235 := bstep (se 1 (by rfl) ⟨598676, by rfl⟩ : syracuseStep 798235 = 1197353) B1197353
theorem B2011351 : Blo 794341 2011351 := bstep (se 1 (by rfl) ⟨1508513, by rfl⟩ : syracuseStep 2011351 = 3017027) B3017027
theorem B3224573 : Blo 794341 3224573 := bstep (se 3 (by rfl) ⟨604607, by rfl⟩ : syracuseStep 3224573 = 1209215) B1209215
theorem B3028859 : Blo 794341 3028859 := bstep (se 1 (by rfl) ⟨2271644, by rfl⟩ : syracuseStep 3028859 = 4543289) B4543289
theorem B2013275 : Blo 794341 2013275 := bstep (se 1 (by rfl) ⟨1509956, by rfl⟩ : syracuseStep 2013275 = 3019913) B3019913
theorem B13810495 : Blo 794341 13810495 := bstep (se 1 (by rfl) ⟨10357871, by rfl⟩ : syracuseStep 13810495 = 20715743) B20715743
theorem B17219243 : Blo 794341 17219243 := bstep (se 1 (by rfl) ⟨12914432, by rfl⟩ : syracuseStep 17219243 = 25828865) B25828865
theorem B2015401 : Blo 794341 2015401 := bstep (se 2 (by rfl) ⟨755775, by rfl⟩ : syracuseStep 2015401 = 1511551) B1511551
theorem B5458985 : Blo 794341 5458985 := bstep (se 2 (by rfl) ⟨2047119, by rfl⟩ : syracuseStep 5458985 = 4094239) B4094239
theorem B20696401 : Blo 794341 20696401 := bstep (se 2 (by rfl) ⟨7761150, by rfl⟩ : syracuseStep 20696401 = 15522301) B15522301
theorem B1789595 : Blo 794341 1789595 := bstep (se 1 (by rfl) ⟨1342196, by rfl⟩ : syracuseStep 1789595 = 2684393) B2684393
theorem B5459663 : Blo 794341 5459663 := bstep (se 1 (by rfl) ⟨4094747, by rfl⟩ : syracuseStep 5459663 = 8189495) B8189495
theorem B10899731 : Blo 794341 10899731 := bstep (se 1 (by rfl) ⟨8174798, by rfl⟩ : syracuseStep 10899731 = 16349597) B16349597
theorem B6543737 : Blo 794341 6543737 := bstep (se 2 (by rfl) ⟨2453901, by rfl⟩ : syracuseStep 6543737 = 4907803) B4907803
theorem B26861645 : Blo 794341 26861645 := bstep (se 3 (by rfl) ⟨5036558, by rfl⟩ : syracuseStep 26861645 = 10073117) B10073117
theorem B1794311 : Blo 794341 1794311 := bstep (se 1 (by rfl) ⟨1345733, by rfl⟩ : syracuseStep 1794311 = 2691467) B2691467
theorem B2680991 : Blo 794341 2680991 := bstep (se 1 (by rfl) ⟨2010743, by rfl⟩ : syracuseStep 2680991 = 4021487) B4021487
theorem B4024889 : Blo 794341 4024889 := bstep (se 2 (by rfl) ⟨1509333, by rfl⟩ : syracuseStep 4024889 = 3018667) B3018667
theorem B4025051 : Blo 794341 4025051 := bstep (se 1 (by rfl) ⟨3018788, by rfl⟩ : syracuseStep 4025051 = 6037577) B6037577
theorem B30666113 : Blo 794341 30666113 := bstep (se 2 (by rfl) ⟨11499792, by rfl⟩ : syracuseStep 30666113 = 22999585) B22999585
theorem B146796047 : Blo 794341 146796047 := bstep (se 1 (by rfl) ⟨110097035, by rfl⟩ : syracuseStep 146796047 = 220194071) B220194071
theorem B13824209 : Blo 794341 13824209 := bstep (se 2 (by rfl) ⟨5184078, by rfl⟩ : syracuseStep 13824209 = 10368157) B10368157
theorem B6813395 : Blo 794341 6813395 := bstep (se 1 (by rfl) ⟨5110046, by rfl⟩ : syracuseStep 6813395 = 10220093) B10220093
theorem B3406049 : Blo 794341 3406049 := bstep (se 2 (by rfl) ⟨1277268, by rfl⟩ : syracuseStep 3406049 = 2554537) B2554537
theorem B353664143 : Blo 794341 353664143 := bstep (se 1 (by rfl) ⟨265248107, by rfl⟩ : syracuseStep 353664143 = 530496215) B530496215
theorem B2686121 : Blo 794341 2686121 := bstep (se 2 (by rfl) ⟨1007295, by rfl⟩ : syracuseStep 2686121 = 2014591) B2014591
theorem B71631053 : Blo 794341 71631053 := bstep (se 3 (by rfl) ⟨13430822, by rfl⟩ : syracuseStep 71631053 = 26861645) B26861645
theorem B2687201 : Blo 794341 2687201 := bstep (se 2 (by rfl) ⟨1007700, by rfl⟩ : syracuseStep 2687201 = 2015401) B2015401
theorem B1704169 : Blo 794341 1704169 := bstep (se 2 (by rfl) ⟨639063, by rfl⟩ : syracuseStep 1704169 = 1278127) B1278127
theorem B29065949 : Blo 794341 29065949 := bstep (se 3 (by rfl) ⟨5449865, by rfl⟩ : syracuseStep 29065949 = 10899731) B10899731
theorem B3639323 : Blo 794341 3639323 := bstep (se 1 (by rfl) ⟨2729492, by rfl⟩ : syracuseStep 3639323 = 5458985) B5458985
theorem B4362491 : Blo 794341 4362491 := bstep (se 1 (by rfl) ⟨3271868, by rfl⟩ : syracuseStep 4362491 = 6543737) B6543737
theorem B27595201 : Blo 794341 27595201 := bstep (se 2 (by rfl) ⟨10348200, by rfl⟩ : syracuseStep 27595201 = 20696401) B20696401
theorem B9216139 : Blo 794341 9216139 := bstep (se 1 (by rfl) ⟨6912104, by rfl⟩ : syracuseStep 9216139 = 13824209) B13824209
theorem B2270699 : Blo 794341 2270699 := bstep (se 1 (by rfl) ⟨1703024, by rfl⟩ : syracuseStep 2270699 = 3406049) B3406049
theorem B14559101 : Blo 794341 14559101 := bstep (se 3 (by rfl) ⟨2729831, by rfl⟩ : syracuseStep 14559101 = 5459663) B5459663
theorem B235776095 : Blo 794341 235776095 := bstep (se 1 (by rfl) ⟨176832071, by rfl⟩ : syracuseStep 235776095 = 353664143) B353664143
theorem B11479495 : Blo 794341 11479495 := bstep (se 1 (by rfl) ⟨8609621, by rfl⟩ : syracuseStep 11479495 = 17219243) B17219243
theorem B4041575 : Blo 794341 4041575 := bstep (se 1 (by rfl) ⟨3031181, by rfl⟩ : syracuseStep 4041575 = 6062363) B6062363
theorem B2011007 : Blo 794341 2011007 := bstep (se 1 (by rfl) ⟨1508255, by rfl⟩ : syracuseStep 2011007 = 3016511) B3016511
theorem B1193063 : Blo 794341 1193063 := bstep (se 1 (by rfl) ⟨894797, by rfl⟩ : syracuseStep 1193063 = 1789595) B1789595
theorem B2014055 : Blo 794341 2014055 := bstep (se 1 (by rfl) ⟨1510541, by rfl⟩ : syracuseStep 2014055 = 3021083) B3021083
theorem B1196207 : Blo 794341 1196207 := bstep (se 1 (by rfl) ⟨897155, by rfl⟩ : syracuseStep 1196207 = 1794311) B1794311
theorem B6997423 : Blo 794341 6997423 := bstep (se 1 (by rfl) ⟨5248067, by rfl⟩ : syracuseStep 6997423 = 10496135) B10496135
theorem B1787327 : Blo 794341 1787327 := bstep (se 1 (by rfl) ⟨1340495, by rfl⟩ : syracuseStep 1787327 = 2680991) B2680991
theorem B97864031 : Blo 794341 97864031 := bstep (se 1 (by rfl) ⟨73398023, by rfl⟩ : syracuseStep 97864031 = 146796047) B146796047
theorem B2149715 : Blo 794341 2149715 := bstep (se 1 (by rfl) ⟨1612286, by rfl⟩ : syracuseStep 2149715 = 3224573) B3224573
theorem B4542263 : Blo 794341 4542263 := bstep (se 1 (by rfl) ⟨3406697, by rfl⟩ : syracuseStep 4542263 = 6813395) B6813395
theorem B2019239 : Blo 794341 2019239 := bstep (se 1 (by rfl) ⟨1514429, by rfl⟩ : syracuseStep 2019239 = 3028859) B3028859
theorem B1790747 : Blo 794341 1790747 := bstep (se 1 (by rfl) ⟨1343060, by rfl⟩ : syracuseStep 1790747 = 2686121) B2686121
theorem B33119563 : Blo 794341 33119563 := bstep (se 1 (by rfl) ⟨24839672, by rfl⟩ : syracuseStep 33119563 = 49679345) B49679345
theorem B25878689 : Blo 794341 25878689 := bstep (se 2 (by rfl) ⟨9704508, by rfl⟩ : syracuseStep 25878689 = 19409017) B19409017
theorem B1008379 : Blo 794341 1008379 := bstep (se 1 (by rfl) ⟨756284, by rfl⟩ : syracuseStep 1008379 = 1512569) B1512569
theorem B4023593 : Blo 794341 4023593 := bstep (se 2 (by rfl) ⟨1508847, by rfl⟩ : syracuseStep 4023593 = 3017695) B3017695
theorem B5728103 : Blo 794341 5728103 := bstep (se 1 (by rfl) ⟨4296077, by rfl⟩ : syracuseStep 5728103 = 8592155) B8592155
theorem B2681801 : Blo 794341 2681801 := bstep (se 2 (by rfl) ⟨1005675, by rfl⟩ : syracuseStep 2681801 = 2011351) B2011351
theorem B2683259 : Blo 794341 2683259 := bstep (se 1 (by rfl) ⟨2012444, by rfl⟩ : syracuseStep 2683259 = 4024889) B4024889
theorem B2683367 : Blo 794341 2683367 := bstep (se 1 (by rfl) ⟨2012525, by rfl⟩ : syracuseStep 2683367 = 4025051) B4025051
theorem B20444075 : Blo 794341 20444075 := bstep (se 1 (by rfl) ⟨15333056, by rfl⟩ : syracuseStep 20444075 = 30666113) B30666113
theorem B18413993 : Blo 794341 18413993 := bstep (se 2 (by rfl) ⟨6905247, by rfl⟩ : syracuseStep 18413993 = 13810495) B13810495
theorem B1342183 : Blo 794341 1342183 := bstep (se 1 (by rfl) ⟨1006637, by rfl⟩ : syracuseStep 1342183 = 2013275) B2013275
theorem B12288185 : Blo 794341 12288185 := bstep (se 2 (by rfl) ⟨4608069, by rfl⟩ : syracuseStep 12288185 = 9216139) B9216139
theorem B11633309 : Blo 794341 11633309 := bstep (se 3 (by rfl) ⟨2181245, by rfl⟩ : syracuseStep 11633309 = 4362491) B4362491
theorem B1344505 : Blo 794341 1344505 := bstep (se 2 (by rfl) ⟨504189, by rfl⟩ : syracuseStep 1344505 = 1008379) B1008379
theorem B2426215 : Blo 794341 2426215 := bstep (se 1 (by rfl) ⟨1819661, by rfl⟩ : syracuseStep 2426215 = 3639323) B3639323
theorem B65242687 : Blo 794341 65242687 := bstep (se 1 (by rfl) ⟨48932015, by rfl⟩ : syracuseStep 65242687 = 97864031) B97864031
theorem B1346159 : Blo 794341 1346159 := bstep (se 1 (by rfl) ⟨1009619, by rfl⟩ : syracuseStep 1346159 = 2019239) B2019239
theorem B15305993 : Blo 794341 15305993 := bstep (se 2 (by rfl) ⟨5739747, by rfl⟩ : syracuseStep 15305993 = 11479495) B11479495
theorem B1513799 : Blo 794341 1513799 := bstep (se 1 (by rfl) ⟨1135349, by rfl⟩ : syracuseStep 1513799 = 2270699) B2270699
theorem B9706067 : Blo 794341 9706067 := bstep (se 1 (by rfl) ⟨7279550, by rfl⟩ : syracuseStep 9706067 = 14559101) B14559101
theorem B2694383 : Blo 794341 2694383 := bstep (se 1 (by rfl) ⟨2020787, by rfl⟩ : syracuseStep 2694383 = 4041575) B4041575
theorem B795375 : Blo 794341 795375 := bstep (se 1 (by rfl) ⟨596531, by rfl⟩ : syracuseStep 795375 = 1193063) B1193063
theorem B797471 : Blo 794341 797471 := bstep (se 1 (by rfl) ⟨598103, by rfl⟩ : syracuseStep 797471 = 1196207) B1196207
theorem B47754035 : Blo 794341 47754035 := bstep (se 1 (by rfl) ⟨35815526, by rfl⟩ : syracuseStep 47754035 = 71631053) B71631053
theorem B2272225 : Blo 794341 2272225 := bstep (se 2 (by rfl) ⟨852084, by rfl⟩ : syracuseStep 2272225 = 1704169) B1704169
theorem B19377299 : Blo 794341 19377299 := bstep (se 1 (by rfl) ⟨14532974, by rfl⟩ : syracuseStep 19377299 = 29065949) B29065949
theorem B1191551 : Blo 794341 1191551 := bstep (se 1 (by rfl) ⟨893663, by rfl⟩ : syracuseStep 1191551 = 1787327) B1787327
theorem B3028175 : Blo 794341 3028175 := bstep (se 1 (by rfl) ⟨2271131, by rfl⟩ : syracuseStep 3028175 = 4542263) B4542263
theorem B1193831 : Blo 794341 1193831 := bstep (se 1 (by rfl) ⟨895373, by rfl⟩ : syracuseStep 1193831 = 1790747) B1790747
theorem B17252459 : Blo 794341 17252459 := bstep (se 1 (by rfl) ⟨12939344, by rfl⟩ : syracuseStep 17252459 = 25878689) B25878689
theorem B49103981 : Blo 794341 49103981 := bstep (se 3 (by rfl) ⟨9206996, by rfl⟩ : syracuseStep 49103981 = 18413993) B18413993
theorem B3818735 : Blo 794341 3818735 := bstep (se 1 (by rfl) ⟨2864051, by rfl⟩ : syracuseStep 3818735 = 5728103) B5728103
theorem B1787867 : Blo 794341 1787867 := bstep (se 1 (by rfl) ⟨1340900, by rfl⟩ : syracuseStep 1787867 = 2681801) B2681801
theorem B1788839 : Blo 794341 1788839 := bstep (se 1 (by rfl) ⟨1341629, by rfl⟩ : syracuseStep 1788839 = 2683259) B2683259
theorem B1788911 : Blo 794341 1788911 := bstep (se 1 (by rfl) ⟨1341683, by rfl⟩ : syracuseStep 1788911 = 2683367) B2683367
theorem B1789577 : Blo 794341 1789577 := bstep (se 2 (by rfl) ⟨671091, by rfl⟩ : syracuseStep 1789577 = 1342183) B1342183
theorem B44159417 : Blo 794341 44159417 := bstep (se 2 (by rfl) ⟨16559781, by rfl⟩ : syracuseStep 44159417 = 33119563) B33119563
theorem B1791467 : Blo 794341 1791467 := bstep (se 1 (by rfl) ⟨1343600, by rfl⟩ : syracuseStep 1791467 = 2687201) B2687201
theorem B9329897 : Blo 794341 9329897 := bstep (se 2 (by rfl) ⟨3498711, by rfl⟩ : syracuseStep 9329897 = 6997423) B6997423
theorem B1433143 : Blo 794341 1433143 := bstep (se 1 (by rfl) ⟨1074857, by rfl⟩ : syracuseStep 1433143 = 2149715) B2149715
theorem B36793601 : Blo 794341 36793601 := bstep (se 2 (by rfl) ⟨13797600, by rfl⟩ : syracuseStep 36793601 = 27595201) B27595201
theorem B2682395 : Blo 794341 2682395 := bstep (se 1 (by rfl) ⟨2011796, by rfl⟩ : syracuseStep 2682395 = 4023593) B4023593
theorem B157184063 : Blo 794341 157184063 := bstep (se 1 (by rfl) ⟨117888047, by rfl⟩ : syracuseStep 157184063 = 235776095) B235776095
theorem B1340671 : Blo 794341 1340671 := bstep (se 1 (by rfl) ⟨1005503, by rfl⟩ : syracuseStep 1340671 = 2011007) B2011007
theorem B13629383 : Blo 794341 13629383 := bstep (se 1 (by rfl) ⟨10222037, by rfl⟩ : syracuseStep 13629383 = 20444075) B20444075
theorem B1342703 : Blo 794341 1342703 := bstep (se 1 (by rfl) ⟨1007027, by rfl⟩ : syracuseStep 1342703 = 2014055) B2014055
theorem B11501639 : Blo 794341 11501639 := bstep (se 1 (by rfl) ⟨8626229, by rfl⟩ : syracuseStep 11501639 = 17252459) B17252459
theorem B8192123 : Blo 794341 8192123 := bstep (se 1 (by rfl) ⟨6144092, by rfl⟩ : syracuseStep 8192123 = 12288185) B12288185
theorem B32735987 : Blo 794341 32735987 := bstep (se 1 (by rfl) ⟨24551990, by rfl⟩ : syracuseStep 32735987 = 49103981) B49103981
theorem B12918199 : Blo 794341 12918199 := bstep (se 1 (by rfl) ⟨9688649, by rfl⟩ : syracuseStep 12918199 = 19377299) B19377299
theorem B794367 : Blo 794341 794367 := bstep (se 1 (by rfl) ⟨595775, by rfl⟩ : syracuseStep 794367 = 1191551) B1191551
theorem B7643429 : Blo 794341 7643429 := bstep (se 4 (by rfl) ⟨716571, by rfl⟩ : syracuseStep 7643429 = 1433143) B1433143
theorem B795887 : Blo 794341 795887 := bstep (se 1 (by rfl) ⟨596915, by rfl⟩ : syracuseStep 795887 = 1193831) B1193831
theorem B9086255 : Blo 794341 9086255 := bstep (se 1 (by rfl) ⟨6814691, by rfl⟩ : syracuseStep 9086255 = 13629383) B13629383
theorem B895135 : Blo 794341 895135 := bstep (se 1 (by rfl) ⟨671351, by rfl⟩ : syracuseStep 895135 = 1342703) B1342703
theorem B1191911 : Blo 794341 1191911 := bstep (se 1 (by rfl) ⟨893933, by rfl⟩ : syracuseStep 1191911 = 1787867) B1787867
theorem B897439 : Blo 794341 897439 := bstep (se 1 (by rfl) ⟨673079, by rfl⟩ : syracuseStep 897439 = 1346159) B1346159
theorem B1192559 : Blo 794341 1192559 := bstep (se 1 (by rfl) ⟨894419, by rfl⟩ : syracuseStep 1192559 = 1788839) B1788839
theorem B1192607 : Blo 794341 1192607 := bstep (se 1 (by rfl) ⟨894455, by rfl⟩ : syracuseStep 1192607 = 1788911) B1788911
theorem B10203995 : Blo 794341 10203995 := bstep (se 1 (by rfl) ⟨7652996, by rfl⟩ : syracuseStep 10203995 = 15305993) B15305993
theorem B1193051 : Blo 794341 1193051 := bstep (se 1 (by rfl) ⟨894788, by rfl⟩ : syracuseStep 1193051 = 1789577) B1789577
theorem B29439611 : Blo 794341 29439611 := bstep (se 1 (by rfl) ⟨22079708, by rfl⟩ : syracuseStep 29439611 = 44159417) B44159417
theorem B1194311 : Blo 794341 1194311 := bstep (se 1 (by rfl) ⟨895733, by rfl⟩ : syracuseStep 1194311 = 1791467) B1791467
theorem B3029633 : Blo 794341 3029633 := bstep (se 2 (by rfl) ⟨1136112, by rfl⟩ : syracuseStep 3029633 = 2272225) B2272225
theorem B6470711 : Blo 794341 6470711 := bstep (se 1 (by rfl) ⟨4853033, by rfl⟩ : syracuseStep 6470711 = 9706067) B9706067
theorem B1787561 : Blo 794341 1787561 := bstep (se 2 (by rfl) ⟨670335, by rfl⟩ : syracuseStep 1787561 = 1340671) B1340671
theorem B31836023 : Blo 794341 31836023 := bstep (se 1 (by rfl) ⟨23877017, by rfl⟩ : syracuseStep 31836023 = 47754035) B47754035
theorem B24529067 : Blo 794341 24529067 := bstep (se 1 (by rfl) ⟨18396800, by rfl⟩ : syracuseStep 24529067 = 36793601) B36793601
theorem B1788263 : Blo 794341 1788263 := bstep (se 1 (by rfl) ⟨1341197, by rfl⟩ : syracuseStep 1788263 = 2682395) B2682395
theorem B2018783 : Blo 794341 2018783 := bstep (se 1 (by rfl) ⟨1514087, by rfl⟩ : syracuseStep 2018783 = 3028175) B3028175
theorem B7755539 : Blo 794341 7755539 := bstep (se 1 (by rfl) ⟨5816654, by rfl⟩ : syracuseStep 7755539 = 11633309) B11633309
theorem B2545823 : Blo 794341 2545823 := bstep (se 1 (by rfl) ⟨1909367, by rfl⟩ : syracuseStep 2545823 = 3818735) B3818735
theorem B1792673 : Blo 794341 1792673 := bstep (se 2 (by rfl) ⟨672252, by rfl⟩ : syracuseStep 1792673 = 1344505) B1344505
theorem B3234953 : Blo 794341 3234953 := bstep (se 2 (by rfl) ⟨1213107, by rfl⟩ : syracuseStep 3234953 = 2426215) B2426215
theorem B86990249 : Blo 794341 86990249 := bstep (se 2 (by rfl) ⟨32621343, by rfl⟩ : syracuseStep 86990249 = 65242687) B65242687
theorem B1009199 : Blo 794341 1009199 := bstep (se 1 (by rfl) ⟨756899, by rfl⟩ : syracuseStep 1009199 = 1513799) B1513799
theorem B6219931 : Blo 794341 6219931 := bstep (se 1 (by rfl) ⟨4664948, by rfl⟩ : syracuseStep 6219931 = 9329897) B9329897
theorem B1796255 : Blo 794341 1796255 := bstep (se 1 (by rfl) ⟨1347191, by rfl⟩ : syracuseStep 1796255 = 2694383) B2694383
theorem B104789375 : Blo 794341 104789375 := bstep (se 1 (by rfl) ⟨78592031, by rfl⟩ : syracuseStep 104789375 = 157184063) B157184063
theorem B7667759 : Blo 794341 7667759 := bstep (se 1 (by rfl) ⟨5750819, by rfl⟩ : syracuseStep 7667759 = 11501639) B11501639
theorem B21823991 : Blo 794341 21823991 := bstep (se 1 (by rfl) ⟨16367993, by rfl⟩ : syracuseStep 21823991 = 32735987) B32735987
theorem B16352711 : Blo 794341 16352711 := bstep (se 1 (by rfl) ⟨12264533, by rfl⟩ : syracuseStep 16352711 = 24529067) B24529067
theorem B1345855 : Blo 794341 1345855 := bstep (se 1 (by rfl) ⟨1009391, by rfl⟩ : syracuseStep 1345855 = 2018783) B2018783
theorem B8293241 : Blo 794341 8293241 := bstep (se 2 (by rfl) ⟨3109965, by rfl⟩ : syracuseStep 8293241 = 6219931) B6219931
theorem B2691197 : Blo 794341 2691197 := bstep (se 3 (by rfl) ⟨504599, by rfl⟩ : syracuseStep 2691197 = 1009199) B1009199
theorem B20681437 : Blo 794341 20681437 := bstep (se 3 (by rfl) ⟨3877769, by rfl⟩ : syracuseStep 20681437 = 7755539) B7755539
theorem B794607 : Blo 794341 794607 := bstep (se 1 (by rfl) ⟨595955, by rfl⟩ : syracuseStep 794607 = 1191911) B1191911
theorem B795039 : Blo 794341 795039 := bstep (se 1 (by rfl) ⟨596279, by rfl⟩ : syracuseStep 795039 = 1192559) B1192559
theorem B795071 : Blo 794341 795071 := bstep (se 1 (by rfl) ⟨596303, by rfl⟩ : syracuseStep 795071 = 1192607) B1192607
theorem B795367 : Blo 794341 795367 := bstep (se 1 (by rfl) ⟨596525, by rfl⟩ : syracuseStep 795367 = 1193051) B1193051
theorem B796207 : Blo 794341 796207 := bstep (se 1 (by rfl) ⟨597155, by rfl⟩ : syracuseStep 796207 = 1194311) B1194311
theorem B1191707 : Blo 794341 1191707 := bstep (se 1 (by rfl) ⟨893780, by rfl⟩ : syracuseStep 1191707 = 1787561) B1787561
theorem B1192175 : Blo 794341 1192175 := bstep (se 1 (by rfl) ⟨894131, by rfl⟩ : syracuseStep 1192175 = 1788263) B1788263
theorem B1193513 : Blo 794341 1193513 := bstep (se 2 (by rfl) ⟨447567, by rfl⟩ : syracuseStep 1193513 = 895135) B895135
theorem B1195115 : Blo 794341 1195115 := bstep (se 1 (by rfl) ⟨896336, by rfl⟩ : syracuseStep 1195115 = 1792673) B1792673
theorem B5095619 : Blo 794341 5095619 := bstep (se 1 (by rfl) ⟨3821714, by rfl⟩ : syracuseStep 5095619 = 7643429) B7643429
theorem B1196585 : Blo 794341 1196585 := bstep (se 2 (by rfl) ⟨448719, by rfl⟩ : syracuseStep 1196585 = 897439) B897439
theorem B1197503 : Blo 794341 1197503 := bstep (se 1 (by rfl) ⟨898127, by rfl⟩ : syracuseStep 1197503 = 1796255) B1796255
theorem B6802663 : Blo 794341 6802663 := bstep (se 1 (by rfl) ⟨5101997, by rfl⟩ : syracuseStep 6802663 = 10203995) B10203995
theorem B2019755 : Blo 794341 2019755 := bstep (se 1 (by rfl) ⟨1514816, by rfl⟩ : syracuseStep 2019755 = 3029633) B3029633
theorem B17224265 : Blo 794341 17224265 := bstep (se 2 (by rfl) ⟨6459099, by rfl⟩ : syracuseStep 17224265 = 12918199) B12918199
theorem B4313807 : Blo 794341 4313807 := bstep (se 1 (by rfl) ⟨3235355, by rfl⟩ : syracuseStep 4313807 = 6470711) B6470711
theorem B5461415 : Blo 794341 5461415 := bstep (se 1 (by rfl) ⟨4096061, by rfl⟩ : syracuseStep 5461415 = 8192123) B8192123
theorem B21224015 : Blo 794341 21224015 := bstep (se 1 (by rfl) ⟨15918011, by rfl⟩ : syracuseStep 21224015 = 31836023) B31836023
theorem B1697215 : Blo 794341 1697215 := bstep (se 1 (by rfl) ⟨1272911, by rfl⟩ : syracuseStep 1697215 = 2545823) B2545823
theorem B2156635 : Blo 794341 2156635 := bstep (se 1 (by rfl) ⟨1617476, by rfl⟩ : syracuseStep 2156635 = 3234953) B3234953
theorem B57993499 : Blo 794341 57993499 := bstep (se 1 (by rfl) ⟨43495124, by rfl⟩ : syracuseStep 57993499 = 86990249) B86990249
theorem B6057503 : Blo 794341 6057503 := bstep (se 1 (by rfl) ⟨4543127, by rfl⟩ : syracuseStep 6057503 = 9086255) B9086255
theorem B69859583 : Blo 794341 69859583 := bstep (se 1 (by rfl) ⟨52394687, by rfl⟩ : syracuseStep 69859583 = 104789375) B104789375
theorem B19626407 : Blo 794341 19626407 := bstep (se 1 (by rfl) ⟨14719805, by rfl⟩ : syracuseStep 19626407 = 29439611) B29439611
theorem B5111839 : Blo 794341 5111839 := bstep (se 1 (by rfl) ⟨3833879, by rfl⟩ : syracuseStep 5111839 = 7667759) B7667759
theorem B14549327 : Blo 794341 14549327 := bstep (se 1 (by rfl) ⟨10911995, by rfl⟩ : syracuseStep 14549327 = 21823991) B21823991
theorem B2262953 : Blo 794341 2262953 := bstep (se 2 (by rfl) ⟨848607, by rfl⟩ : syracuseStep 2262953 = 1697215) B1697215
theorem B1346503 : Blo 794341 1346503 := bstep (se 1 (by rfl) ⟨1009877, by rfl⟩ : syracuseStep 1346503 = 2019755) B2019755
theorem B3640943 : Blo 794341 3640943 := bstep (se 1 (by rfl) ⟨2730707, by rfl⟩ : syracuseStep 3640943 = 5461415) B5461415
theorem B4038335 : Blo 794341 4038335 := bstep (se 1 (by rfl) ⟨3028751, by rfl⟩ : syracuseStep 4038335 = 6057503) B6057503
theorem B794471 : Blo 794341 794471 := bstep (se 1 (by rfl) ⟨595853, by rfl⟩ : syracuseStep 794471 = 1191707) B1191707
theorem B794783 : Blo 794341 794783 := bstep (se 1 (by rfl) ⟨596087, by rfl⟩ : syracuseStep 794783 = 1192175) B1192175
theorem B795675 : Blo 794341 795675 := bstep (se 1 (by rfl) ⟨596756, by rfl⟩ : syracuseStep 795675 = 1193513) B1193513
theorem B46573055 : Blo 794341 46573055 := bstep (se 1 (by rfl) ⟨34929791, by rfl⟩ : syracuseStep 46573055 = 69859583) B69859583
theorem B13084271 : Blo 794341 13084271 := bstep (se 1 (by rfl) ⟨9813203, by rfl⟩ : syracuseStep 13084271 = 19626407) B19626407
theorem B796743 : Blo 794341 796743 := bstep (se 1 (by rfl) ⟨597557, by rfl⟩ : syracuseStep 796743 = 1195115) B1195115
theorem B797723 : Blo 794341 797723 := bstep (se 1 (by rfl) ⟨598292, by rfl⟩ : syracuseStep 797723 = 1196585) B1196585
theorem B798335 : Blo 794341 798335 := bstep (se 1 (by rfl) ⟨598751, by rfl⟩ : syracuseStep 798335 = 1197503) B1197503
theorem B11482843 : Blo 794341 11482843 := bstep (se 1 (by rfl) ⟨8612132, by rfl⟩ : syracuseStep 11482843 = 17224265) B17224265
theorem B27575249 : Blo 794341 27575249 := bstep (se 2 (by rfl) ⟨10340718, by rfl⟩ : syracuseStep 27575249 = 20681437) B20681437
theorem B3397079 : Blo 794341 3397079 := bstep (se 1 (by rfl) ⟨2547809, by rfl⟩ : syracuseStep 3397079 = 5095619) B5095619
theorem B10901807 : Blo 794341 10901807 := bstep (se 1 (by rfl) ⟨8176355, by rfl⟩ : syracuseStep 10901807 = 16352711) B16352711
theorem B5528827 : Blo 794341 5528827 := bstep (se 1 (by rfl) ⟨4146620, by rfl⟩ : syracuseStep 5528827 = 8293241) B8293241
theorem B1794131 : Blo 794341 1794131 := bstep (se 1 (by rfl) ⟨1345598, by rfl⟩ : syracuseStep 1794131 = 2691197) B2691197
theorem B2875513 : Blo 794341 2875513 := bstep (se 2 (by rfl) ⟨1078317, by rfl⟩ : syracuseStep 2875513 = 2156635) B2156635
theorem B77324665 : Blo 794341 77324665 := bstep (se 2 (by rfl) ⟨28996749, by rfl⟩ : syracuseStep 77324665 = 57993499) B57993499
theorem B1794473 : Blo 794341 1794473 := bstep (se 2 (by rfl) ⟨672927, by rfl⟩ : syracuseStep 1794473 = 1345855) B1345855
theorem B2875871 : Blo 794341 2875871 := bstep (se 1 (by rfl) ⟨2156903, by rfl⟩ : syracuseStep 2875871 = 4313807) B4313807
theorem B9070217 : Blo 794341 9070217 := bstep (se 2 (by rfl) ⟨3401331, by rfl⟩ : syracuseStep 9070217 = 6802663) B6802663
theorem B14149343 : Blo 794341 14149343 := bstep (se 1 (by rfl) ⟨10612007, by rfl⟩ : syracuseStep 14149343 = 21224015) B21224015
theorem B6815785 : Blo 794341 6815785 := bstep (se 2 (by rfl) ⟨2555919, by rfl⟩ : syracuseStep 6815785 = 5111839) B5111839
theorem B3834017 : Blo 794341 3834017 := bstep (se 2 (by rfl) ⟨1437756, by rfl⟩ : syracuseStep 3834017 = 2875513) B2875513
theorem B9699551 : Blo 794341 9699551 := bstep (se 1 (by rfl) ⟨7274663, by rfl⟩ : syracuseStep 9699551 = 14549327) B14549327
theorem B7668989 : Blo 794341 7668989 := bstep (se 3 (by rfl) ⟨1437935, by rfl⟩ : syracuseStep 7668989 = 2875871) B2875871
theorem B1508635 : Blo 794341 1508635 := bstep (se 1 (by rfl) ⟨1131476, by rfl⟩ : syracuseStep 1508635 = 2262953) B2262953
theorem B2427295 : Blo 794341 2427295 := bstep (se 1 (by rfl) ⟨1820471, by rfl⟩ : syracuseStep 2427295 = 3640943) B3640943
theorem B73533997 : Blo 794341 73533997 := bstep (se 3 (by rfl) ⟨13787624, by rfl⟩ : syracuseStep 73533997 = 27575249) B27575249
theorem B2264719 : Blo 794341 2264719 := bstep (se 1 (by rfl) ⟨1698539, by rfl⟩ : syracuseStep 2264719 = 3397079) B3397079
theorem B2692223 : Blo 794341 2692223 := bstep (se 1 (by rfl) ⟨2019167, by rfl⟩ : syracuseStep 2692223 = 4038335) B4038335
theorem B8722847 : Blo 794341 8722847 := bstep (se 1 (by rfl) ⟨6542135, by rfl⟩ : syracuseStep 8722847 = 13084271) B13084271
theorem B15310457 : Blo 794341 15310457 := bstep (se 2 (by rfl) ⟨5741421, by rfl⟩ : syracuseStep 15310457 = 11482843) B11482843
theorem B103099553 : Blo 794341 103099553 := bstep (se 2 (by rfl) ⟨38662332, by rfl⟩ : syracuseStep 103099553 = 77324665) B77324665
theorem B1196087 : Blo 794341 1196087 := bstep (se 1 (by rfl) ⟨897065, by rfl⟩ : syracuseStep 1196087 = 1794131) B1794131
theorem B1196315 : Blo 794341 1196315 := bstep (se 1 (by rfl) ⟨897236, by rfl⟩ : syracuseStep 1196315 = 1794473) B1794473
theorem B31048703 : Blo 794341 31048703 := bstep (se 1 (by rfl) ⟨23286527, by rfl⟩ : syracuseStep 31048703 = 46573055) B46573055
theorem B6046811 : Blo 794341 6046811 := bstep (se 1 (by rfl) ⟨4535108, by rfl⟩ : syracuseStep 6046811 = 9070217) B9070217
theorem B1795337 : Blo 794341 1795337 := bstep (se 2 (by rfl) ⟨673251, by rfl⟩ : syracuseStep 1795337 = 1346503) B1346503
theorem B7267871 : Blo 794341 7267871 := bstep (se 1 (by rfl) ⟨5450903, by rfl⟩ : syracuseStep 7267871 = 10901807) B10901807
theorem B9432895 : Blo 794341 9432895 := bstep (se 1 (by rfl) ⟨7074671, by rfl⟩ : syracuseStep 9432895 = 14149343) B14149343
theorem B7371769 : Blo 794341 7371769 := bstep (se 2 (by rfl) ⟨2764413, by rfl⟩ : syracuseStep 7371769 = 5528827) B5528827
theorem B2556011 : Blo 794341 2556011 := bstep (se 1 (by rfl) ⟨1917008, by rfl⟩ : syracuseStep 2556011 = 3834017) B3834017
theorem B4031207 : Blo 794341 4031207 := bstep (se 1 (by rfl) ⟨3023405, by rfl⟩ : syracuseStep 4031207 = 6046811) B6046811
theorem B5112659 : Blo 794341 5112659 := bstep (se 1 (by rfl) ⟨3834494, by rfl⟩ : syracuseStep 5112659 = 7668989) B7668989
theorem B98045329 : Blo 794341 98045329 := bstep (se 2 (by rfl) ⟨36766998, by rfl⟩ : syracuseStep 98045329 = 73533997) B73533997
theorem B3019625 : Blo 794341 3019625 := bstep (se 2 (by rfl) ⟨1132359, by rfl⟩ : syracuseStep 3019625 = 2264719) B2264719
theorem B797391 : Blo 794341 797391 := bstep (se 1 (by rfl) ⟨598043, by rfl⟩ : syracuseStep 797391 = 1196087) B1196087
theorem B9087713 : Blo 794341 9087713 := bstep (se 2 (by rfl) ⟨3407892, by rfl⟩ : syracuseStep 9087713 = 6815785) B6815785
theorem B6466367 : Blo 794341 6466367 := bstep (se 1 (by rfl) ⟨4849775, by rfl⟩ : syracuseStep 6466367 = 9699551) B9699551
theorem B797543 : Blo 794341 797543 := bstep (se 1 (by rfl) ⟨598157, by rfl⟩ : syracuseStep 797543 = 1196315) B1196315
theorem B2011513 : Blo 794341 2011513 := bstep (se 2 (by rfl) ⟨754317, by rfl⟩ : syracuseStep 2011513 = 1508635) B1508635
theorem B19380989 : Blo 794341 19380989 := bstep (se 3 (by rfl) ⟨3633935, by rfl⟩ : syracuseStep 19380989 = 7267871) B7267871
theorem B10206971 : Blo 794341 10206971 := bstep (se 1 (by rfl) ⟨7655228, by rfl⟩ : syracuseStep 10206971 = 15310457) B15310457
theorem B1196891 : Blo 794341 1196891 := bstep (se 1 (by rfl) ⟨897668, by rfl⟩ : syracuseStep 1196891 = 1795337) B1795337
theorem B68733035 : Blo 794341 68733035 := bstep (se 1 (by rfl) ⟨51549776, by rfl⟩ : syracuseStep 68733035 = 103099553) B103099553
theorem B20699135 : Blo 794341 20699135 := bstep (se 1 (by rfl) ⟨15524351, by rfl⟩ : syracuseStep 20699135 = 31048703) B31048703
theorem B3236393 : Blo 794341 3236393 := bstep (se 2 (by rfl) ⟨1213647, by rfl⟩ : syracuseStep 3236393 = 2427295) B2427295
theorem B1794815 : Blo 794341 1794815 := bstep (se 1 (by rfl) ⟨1346111, by rfl⟩ : syracuseStep 1794815 = 2692223) B2692223
theorem B12577193 : Blo 794341 12577193 := bstep (se 2 (by rfl) ⟨4716447, by rfl⟩ : syracuseStep 12577193 = 9432895) B9432895
theorem B23260925 : Blo 794341 23260925 := bstep (se 3 (by rfl) ⟨4361423, by rfl⟩ : syracuseStep 23260925 = 8722847) B8722847
theorem B9829025 : Blo 794341 9829025 := bstep (se 2 (by rfl) ⟨3685884, by rfl⟩ : syracuseStep 9829025 = 7371769) B7371769
theorem B1704007 : Blo 794341 1704007 := bstep (se 1 (by rfl) ⟨1278005, by rfl⟩ : syracuseStep 1704007 = 2556011) B2556011
theorem B2687471 : Blo 794341 2687471 := bstep (se 1 (by rfl) ⟨2015603, by rfl⟩ : syracuseStep 2687471 = 4031207) B4031207
theorem B13633757 : Blo 794341 13633757 := bstep (se 3 (by rfl) ⟨2556329, by rfl⟩ : syracuseStep 13633757 = 5112659) B5112659
theorem B13799423 : Blo 794341 13799423 := bstep (se 1 (by rfl) ⟨10349567, by rfl⟩ : syracuseStep 13799423 = 20699135) B20699135
theorem B51682637 : Blo 794341 51682637 := bstep (se 3 (by rfl) ⟨9690494, by rfl⟩ : syracuseStep 51682637 = 19380989) B19380989
theorem B15507283 : Blo 794341 15507283 := bstep (se 1 (by rfl) ⟨11630462, by rfl⟩ : syracuseStep 15507283 = 23260925) B23260925
theorem B797927 : Blo 794341 797927 := bstep (se 1 (by rfl) ⟨598445, by rfl⟩ : syracuseStep 797927 = 1196891) B1196891
theorem B45822023 : Blo 794341 45822023 := bstep (se 1 (by rfl) ⟨34366517, by rfl⟩ : syracuseStep 45822023 = 68733035) B68733035
theorem B8630381 : Blo 794341 8630381 := bstep (se 3 (by rfl) ⟨1618196, by rfl⟩ : syracuseStep 8630381 = 3236393) B3236393
theorem B2013083 : Blo 794341 2013083 := bstep (se 1 (by rfl) ⟨1509812, by rfl⟩ : syracuseStep 2013083 = 3019625) B3019625
theorem B130727105 : Blo 794341 130727105 := bstep (se 2 (by rfl) ⟨49022664, by rfl⟩ : syracuseStep 130727105 = 98045329) B98045329
theorem B1196543 : Blo 794341 1196543 := bstep (se 1 (by rfl) ⟨897407, by rfl⟩ : syracuseStep 1196543 = 1794815) B1794815
theorem B4310911 : Blo 794341 4310911 := bstep (se 1 (by rfl) ⟨3233183, by rfl⟩ : syracuseStep 4310911 = 6466367) B6466367
theorem B6804647 : Blo 794341 6804647 := bstep (se 1 (by rfl) ⟨5103485, by rfl⟩ : syracuseStep 6804647 = 10206971) B10206971
theorem B2682017 : Blo 794341 2682017 := bstep (se 2 (by rfl) ⟨1005756, by rfl⟩ : syracuseStep 2682017 = 2011513) B2011513
theorem B8384795 : Blo 794341 8384795 := bstep (se 1 (by rfl) ⟨6288596, by rfl⟩ : syracuseStep 8384795 = 12577193) B12577193
theorem B6058475 : Blo 794341 6058475 := bstep (se 1 (by rfl) ⟨4543856, by rfl⟩ : syracuseStep 6058475 = 9087713) B9087713
theorem B6552683 : Blo 794341 6552683 := bstep (se 1 (by rfl) ⟨4914512, by rfl⟩ : syracuseStep 6552683 = 9829025) B9829025
theorem B30548015 : Blo 794341 30548015 := bstep (se 1 (by rfl) ⟨22911011, by rfl⟩ : syracuseStep 30548015 = 45822023) B45822023
theorem B4038983 : Blo 794341 4038983 := bstep (se 1 (by rfl) ⟨3029237, by rfl⟩ : syracuseStep 4038983 = 6058475) B6058475
theorem B4368455 : Blo 794341 4368455 := bstep (se 1 (by rfl) ⟨3276341, by rfl⟩ : syracuseStep 4368455 = 6552683) B6552683
theorem B2272009 : Blo 794341 2272009 := bstep (se 2 (by rfl) ⟨852003, by rfl⟩ : syracuseStep 2272009 = 1704007) B1704007
theorem B797695 : Blo 794341 797695 := bstep (se 1 (by rfl) ⟨598271, by rfl⟩ : syracuseStep 797695 = 1196543) B1196543
theorem B9089171 : Blo 794341 9089171 := bstep (se 1 (by rfl) ⟨6816878, by rfl⟩ : syracuseStep 9089171 = 13633757) B13633757
theorem B5747881 : Blo 794341 5747881 := bstep (se 2 (by rfl) ⟨2155455, by rfl⟩ : syracuseStep 5747881 = 4310911) B4310911
theorem B4536431 : Blo 794341 4536431 := bstep (se 1 (by rfl) ⟨3402323, by rfl⟩ : syracuseStep 4536431 = 6804647) B6804647
theorem B34455091 : Blo 794341 34455091 := bstep (se 1 (by rfl) ⟨25841318, by rfl⟩ : syracuseStep 34455091 = 51682637) B51682637
theorem B1788011 : Blo 794341 1788011 := bstep (se 1 (by rfl) ⟨1341008, by rfl⟩ : syracuseStep 1788011 = 2682017) B2682017
theorem B5753587 : Blo 794341 5753587 := bstep (se 1 (by rfl) ⟨4315190, by rfl⟩ : syracuseStep 5753587 = 8630381) B8630381
theorem B5589863 : Blo 794341 5589863 := bstep (se 1 (by rfl) ⟨4192397, by rfl⟩ : syracuseStep 5589863 = 8384795) B8384795
theorem B87151403 : Blo 794341 87151403 := bstep (se 1 (by rfl) ⟨65363552, by rfl⟩ : syracuseStep 87151403 = 130727105) B130727105
theorem B1791647 : Blo 794341 1791647 := bstep (se 1 (by rfl) ⟨1343735, by rfl⟩ : syracuseStep 1791647 = 2687471) B2687471
theorem B9199615 : Blo 794341 9199615 := bstep (se 1 (by rfl) ⟨6899711, by rfl⟩ : syracuseStep 9199615 = 13799423) B13799423
theorem B1342055 : Blo 794341 1342055 := bstep (se 1 (by rfl) ⟨1006541, by rfl⟩ : syracuseStep 1342055 = 2013083) B2013083
theorem B20676377 : Blo 794341 20676377 := bstep (se 2 (by rfl) ⟨7753641, by rfl⟩ : syracuseStep 20676377 = 15507283) B15507283
theorem B58100935 : Blo 794341 58100935 := bstep (se 1 (by rfl) ⟨43575701, by rfl⟩ : syracuseStep 58100935 = 87151403) B87151403
theorem B7671449 : Blo 794341 7671449 := bstep (se 2 (by rfl) ⟨2876793, by rfl⟩ : syracuseStep 7671449 = 5753587) B5753587
theorem B2692655 : Blo 794341 2692655 := bstep (se 1 (by rfl) ⟨2019491, by rfl⟩ : syracuseStep 2692655 = 4038983) B4038983
theorem B3024287 : Blo 794341 3024287 := bstep (se 1 (by rfl) ⟨2268215, by rfl⟩ : syracuseStep 3024287 = 4536431) B4536431
theorem B894703 : Blo 794341 894703 := bstep (se 1 (by rfl) ⟨671027, by rfl⟩ : syracuseStep 894703 = 1342055) B1342055
theorem B12266153 : Blo 794341 12266153 := bstep (se 2 (by rfl) ⟨4599807, by rfl⟩ : syracuseStep 12266153 = 9199615) B9199615
theorem B1192007 : Blo 794341 1192007 := bstep (se 1 (by rfl) ⟨894005, by rfl⟩ : syracuseStep 1192007 = 1788011) B1788011
theorem B3029345 : Blo 794341 3029345 := bstep (se 2 (by rfl) ⟨1136004, by rfl⟩ : syracuseStep 3029345 = 2272009) B2272009
theorem B1194431 : Blo 794341 1194431 := bstep (se 1 (by rfl) ⟨895823, by rfl⟩ : syracuseStep 1194431 = 1791647) B1791647
theorem B20365343 : Blo 794341 20365343 := bstep (se 1 (by rfl) ⟨15274007, by rfl⟩ : syracuseStep 20365343 = 30548015) B30548015
theorem B13784251 : Blo 794341 13784251 := bstep (se 1 (by rfl) ⟨10338188, by rfl⟩ : syracuseStep 13784251 = 20676377) B20676377
theorem B3726575 : Blo 794341 3726575 := bstep (se 1 (by rfl) ⟨2794931, by rfl⟩ : syracuseStep 3726575 = 5589863) B5589863
theorem B2912303 : Blo 794341 2912303 := bstep (se 1 (by rfl) ⟨2184227, by rfl⟩ : syracuseStep 2912303 = 4368455) B4368455
theorem B7663841 : Blo 794341 7663841 := bstep (se 2 (by rfl) ⟨2873940, by rfl⟩ : syracuseStep 7663841 = 5747881) B5747881
theorem B6059447 : Blo 794341 6059447 := bstep (se 1 (by rfl) ⟨4544585, by rfl⟩ : syracuseStep 6059447 = 9089171) B9089171
theorem B45940121 : Blo 794341 45940121 := bstep (se 2 (by rfl) ⟨17227545, by rfl⟩ : syracuseStep 45940121 = 34455091) B34455091
theorem B77467913 : Blo 794341 77467913 := bstep (se 2 (by rfl) ⟨29050467, by rfl⟩ : syracuseStep 77467913 = 58100935) B58100935
theorem B1941535 : Blo 794341 1941535 := bstep (se 1 (by rfl) ⟨1456151, by rfl⟩ : syracuseStep 1941535 = 2912303) B2912303
theorem B794671 : Blo 794341 794671 := bstep (se 1 (by rfl) ⟨596003, by rfl⟩ : syracuseStep 794671 = 1192007) B1192007
theorem B4039631 : Blo 794341 4039631 := bstep (se 1 (by rfl) ⟨3029723, by rfl⟩ : syracuseStep 4039631 = 6059447) B6059447
theorem B796287 : Blo 794341 796287 := bstep (se 1 (by rfl) ⟨597215, by rfl⟩ : syracuseStep 796287 = 1194431) B1194431
theorem B20457197 : Blo 794341 20457197 := bstep (se 3 (by rfl) ⟨3835724, by rfl⟩ : syracuseStep 20457197 = 7671449) B7671449
theorem B13576895 : Blo 794341 13576895 := bstep (se 1 (by rfl) ⟨10182671, by rfl⟩ : syracuseStep 13576895 = 20365343) B20365343
theorem B1192937 : Blo 794341 1192937 := bstep (se 2 (by rfl) ⟨447351, by rfl⟩ : syracuseStep 1192937 = 894703) B894703
theorem B2016191 : Blo 794341 2016191 := bstep (se 1 (by rfl) ⟨1512143, by rfl⟩ : syracuseStep 2016191 = 3024287) B3024287
theorem B8177435 : Blo 794341 8177435 := bstep (se 1 (by rfl) ⟨6133076, by rfl⟩ : syracuseStep 8177435 = 12266153) B12266153
theorem B2019563 : Blo 794341 2019563 := bstep (se 1 (by rfl) ⟨1514672, by rfl⟩ : syracuseStep 2019563 = 3029345) B3029345
theorem B30626747 : Blo 794341 30626747 := bstep (se 1 (by rfl) ⟨22970060, by rfl⟩ : syracuseStep 30626747 = 45940121) B45940121
theorem B1795103 : Blo 794341 1795103 := bstep (se 1 (by rfl) ⟨1346327, by rfl⟩ : syracuseStep 1795103 = 2692655) B2692655
theorem B2484383 : Blo 794341 2484383 := bstep (se 1 (by rfl) ⟨1863287, by rfl⟩ : syracuseStep 2484383 = 3726575) B3726575
theorem B18379001 : Blo 794341 18379001 := bstep (se 2 (by rfl) ⟨6892125, by rfl⟩ : syracuseStep 18379001 = 13784251) B13784251
theorem B5109227 : Blo 794341 5109227 := bstep (se 1 (by rfl) ⟨3831920, by rfl⟩ : syracuseStep 5109227 = 7663841) B7663841
theorem B10354853 : Blo 794341 10354853 := bstep (se 4 (by rfl) ⟨970767, by rfl⟩ : syracuseStep 10354853 = 1941535) B1941535
theorem B1344127 : Blo 794341 1344127 := bstep (se 1 (by rfl) ⟨1008095, by rfl⟩ : syracuseStep 1344127 = 2016191) B2016191
theorem B1346375 : Blo 794341 1346375 := bstep (se 1 (by rfl) ⟨1009781, by rfl⟩ : syracuseStep 1346375 = 2019563) B2019563
theorem B51645275 : Blo 794341 51645275 := bstep (se 1 (by rfl) ⟨38733956, by rfl⟩ : syracuseStep 51645275 = 77467913) B77467913
theorem B20417831 : Blo 794341 20417831 := bstep (se 1 (by rfl) ⟨15313373, by rfl⟩ : syracuseStep 20417831 = 30626747) B30626747
theorem B2693087 : Blo 794341 2693087 := bstep (se 1 (by rfl) ⟨2019815, by rfl⟩ : syracuseStep 2693087 = 4039631) B4039631
theorem B13638131 : Blo 794341 13638131 := bstep (se 1 (by rfl) ⟨10228598, by rfl⟩ : syracuseStep 13638131 = 20457197) B20457197
theorem B9051263 : Blo 794341 9051263 := bstep (se 1 (by rfl) ⟨6788447, by rfl⟩ : syracuseStep 9051263 = 13576895) B13576895
theorem B795291 : Blo 794341 795291 := bstep (se 1 (by rfl) ⟨596468, by rfl⟩ : syracuseStep 795291 = 1192937) B1192937
theorem B5451623 : Blo 794341 5451623 := bstep (se 1 (by rfl) ⟨4088717, by rfl⟩ : syracuseStep 5451623 = 8177435) B8177435
theorem B1196735 : Blo 794341 1196735 := bstep (se 1 (by rfl) ⟨897551, by rfl⟩ : syracuseStep 1196735 = 1795103) B1795103
theorem B49010669 : Blo 794341 49010669 := bstep (se 3 (by rfl) ⟨9189500, by rfl⟩ : syracuseStep 49010669 = 18379001) B18379001
theorem B26500085 : Blo 794341 26500085 := bstep (se 5 (by rfl) ⟨1242191, by rfl⟩ : syracuseStep 26500085 = 2484383) B2484383
theorem B3406151 : Blo 794341 3406151 := bstep (se 1 (by rfl) ⟨2554613, by rfl⟩ : syracuseStep 3406151 = 5109227) B5109227
theorem B32673779 : Blo 794341 32673779 := bstep (se 1 (by rfl) ⟨24505334, by rfl⟩ : syracuseStep 32673779 = 49010669) B49010669
theorem B17666723 : Blo 794341 17666723 := bstep (se 1 (by rfl) ⟨13250042, by rfl⟩ : syracuseStep 17666723 = 26500085) B26500085
theorem B6034175 : Blo 794341 6034175 := bstep (se 1 (by rfl) ⟨4525631, by rfl⟩ : syracuseStep 6034175 = 9051263) B9051263
theorem B2270767 : Blo 794341 2270767 := bstep (se 1 (by rfl) ⟨1703075, by rfl⟩ : syracuseStep 2270767 = 3406151) B3406151
theorem B797823 : Blo 794341 797823 := bstep (se 1 (by rfl) ⟨598367, by rfl⟩ : syracuseStep 797823 = 1196735) B1196735
theorem B897583 : Blo 794341 897583 := bstep (se 1 (by rfl) ⟨673187, by rfl⟩ : syracuseStep 897583 = 1346375) B1346375
theorem B13611887 : Blo 794341 13611887 := bstep (se 1 (by rfl) ⟨10208915, by rfl⟩ : syracuseStep 13611887 = 20417831) B20417831
theorem B9092087 : Blo 794341 9092087 := bstep (se 1 (by rfl) ⟨6819065, by rfl⟩ : syracuseStep 9092087 = 13638131) B13638131
theorem B6903235 : Blo 794341 6903235 := bstep (se 1 (by rfl) ⟨5177426, by rfl⟩ : syracuseStep 6903235 = 10354853) B10354853
theorem B1792169 : Blo 794341 1792169 := bstep (se 2 (by rfl) ⟨672063, by rfl⟩ : syracuseStep 1792169 = 1344127) B1344127
theorem B34430183 : Blo 794341 34430183 := bstep (se 1 (by rfl) ⟨25822637, by rfl⟩ : syracuseStep 34430183 = 51645275) B51645275
theorem B1795391 : Blo 794341 1795391 := bstep (se 1 (by rfl) ⟨1346543, by rfl⟩ : syracuseStep 1795391 = 2693087) B2693087
theorem B3634415 : Blo 794341 3634415 := bstep (se 1 (by rfl) ⟨2725811, by rfl⟩ : syracuseStep 3634415 = 5451623) B5451623
theorem B3027689 : Blo 794341 3027689 := bstep (se 2 (by rfl) ⟨1135383, by rfl⟩ : syracuseStep 3027689 = 2270767) B2270767
theorem B11777815 : Blo 794341 11777815 := bstep (se 1 (by rfl) ⟨8833361, by rfl⟩ : syracuseStep 11777815 = 17666723) B17666723
theorem B1194779 : Blo 794341 1194779 := bstep (se 1 (by rfl) ⟨896084, by rfl⟩ : syracuseStep 1194779 = 1792169) B1792169
theorem B22953455 : Blo 794341 22953455 := bstep (se 1 (by rfl) ⟨17215091, by rfl⟩ : syracuseStep 22953455 = 34430183) B34430183
theorem B1196777 : Blo 794341 1196777 := bstep (se 2 (by rfl) ⟨448791, by rfl⟩ : syracuseStep 1196777 = 897583) B897583
theorem B1196927 : Blo 794341 1196927 := bstep (se 1 (by rfl) ⟨897695, by rfl⟩ : syracuseStep 1196927 = 1795391) B1795391
theorem B21782519 : Blo 794341 21782519 := bstep (se 1 (by rfl) ⟨16336889, by rfl⟩ : syracuseStep 21782519 = 32673779) B32673779
theorem B4022783 : Blo 794341 4022783 := bstep (se 1 (by rfl) ⟨3017087, by rfl⟩ : syracuseStep 4022783 = 6034175) B6034175
theorem B9204313 : Blo 794341 9204313 := bstep (se 2 (by rfl) ⟨3451617, by rfl⟩ : syracuseStep 9204313 = 6903235) B6903235
theorem B9074591 : Blo 794341 9074591 := bstep (se 1 (by rfl) ⟨6805943, by rfl⟩ : syracuseStep 9074591 = 13611887) B13611887
theorem B2422943 : Blo 794341 2422943 := bstep (se 1 (by rfl) ⟨1817207, by rfl⟩ : syracuseStep 2422943 = 3634415) B3634415
theorem B6061391 : Blo 794341 6061391 := bstep (se 1 (by rfl) ⟨4546043, by rfl⟩ : syracuseStep 6061391 = 9092087) B9092087
theorem B14521679 : Blo 794341 14521679 := bstep (se 1 (by rfl) ⟨10891259, by rfl⟩ : syracuseStep 14521679 = 21782519) B21782519
theorem B15703753 : Blo 794341 15703753 := bstep (se 2 (by rfl) ⟨5888907, by rfl⟩ : syracuseStep 15703753 = 11777815) B11777815
theorem B1615295 : Blo 794341 1615295 := bstep (se 1 (by rfl) ⟨1211471, by rfl⟩ : syracuseStep 1615295 = 2422943) B2422943
theorem B796519 : Blo 794341 796519 := bstep (se 1 (by rfl) ⟨597389, by rfl⟩ : syracuseStep 796519 = 1194779) B1194779
theorem B4040927 : Blo 794341 4040927 := bstep (se 1 (by rfl) ⟨3030695, by rfl⟩ : syracuseStep 4040927 = 6061391) B6061391
theorem B797851 : Blo 794341 797851 := bstep (se 1 (by rfl) ⟨598388, by rfl⟩ : syracuseStep 797851 = 1196777) B1196777
theorem B797951 : Blo 794341 797951 := bstep (se 1 (by rfl) ⟨598463, by rfl⟩ : syracuseStep 797951 = 1196927) B1196927
theorem B12272417 : Blo 794341 12272417 := bstep (se 2 (by rfl) ⟨4602156, by rfl⟩ : syracuseStep 12272417 = 9204313) B9204313
theorem B2018459 : Blo 794341 2018459 := bstep (se 1 (by rfl) ⟨1513844, by rfl⟩ : syracuseStep 2018459 = 3027689) B3027689
theorem B6049727 : Blo 794341 6049727 := bstep (se 1 (by rfl) ⟨4537295, by rfl⟩ : syracuseStep 6049727 = 9074591) B9074591
theorem B2681855 : Blo 794341 2681855 := bstep (se 1 (by rfl) ⟨2011391, by rfl⟩ : syracuseStep 2681855 = 4022783) B4022783
theorem B15302303 : Blo 794341 15302303 := bstep (se 1 (by rfl) ⟨11476727, by rfl⟩ : syracuseStep 15302303 = 22953455) B22953455
theorem B1345639 : Blo 794341 1345639 := bstep (se 1 (by rfl) ⟨1009229, by rfl⟩ : syracuseStep 1345639 = 2018459) B2018459
theorem B4033151 : Blo 794341 4033151 := bstep (se 1 (by rfl) ⟨3024863, by rfl⟩ : syracuseStep 4033151 = 6049727) B6049727
theorem B2693951 : Blo 794341 2693951 := bstep (se 1 (by rfl) ⟨2020463, by rfl⟩ : syracuseStep 2693951 = 4040927) B4040927
theorem B10201535 : Blo 794341 10201535 := bstep (se 1 (by rfl) ⟨7651151, by rfl⟩ : syracuseStep 10201535 = 15302303) B15302303
theorem B9681119 : Blo 794341 9681119 := bstep (se 1 (by rfl) ⟨7260839, by rfl⟩ : syracuseStep 9681119 = 14521679) B14521679
theorem B1787903 : Blo 794341 1787903 := bstep (se 1 (by rfl) ⟨1340927, by rfl⟩ : syracuseStep 1787903 = 2681855) B2681855
theorem B8181611 : Blo 794341 8181611 := bstep (se 1 (by rfl) ⟨6136208, by rfl⟩ : syracuseStep 8181611 = 12272417) B12272417
theorem B1076863 : Blo 794341 1076863 := bstep (se 1 (by rfl) ⟨807647, by rfl⟩ : syracuseStep 1076863 = 1615295) B1615295
theorem B20938337 : Blo 794341 20938337 := bstep (se 2 (by rfl) ⟨7851876, by rfl⟩ : syracuseStep 20938337 = 15703753) B15703753
theorem B2688767 : Blo 794341 2688767 := bstep (se 1 (by rfl) ⟨2016575, by rfl⟩ : syracuseStep 2688767 = 4033151) B4033151
theorem B1191935 : Blo 794341 1191935 := bstep (se 1 (by rfl) ⟨893951, by rfl⟩ : syracuseStep 1191935 = 1787903) B1787903
theorem B5454407 : Blo 794341 5454407 := bstep (se 1 (by rfl) ⟨4090805, by rfl⟩ : syracuseStep 5454407 = 8181611) B8181611
theorem B6801023 : Blo 794341 6801023 := bstep (se 1 (by rfl) ⟨5100767, by rfl⟩ : syracuseStep 6801023 = 10201535) B10201535
theorem B1794185 : Blo 794341 1794185 := bstep (se 2 (by rfl) ⟨672819, by rfl⟩ : syracuseStep 1794185 = 1345639) B1345639
theorem B1795967 : Blo 794341 1795967 := bstep (se 1 (by rfl) ⟨1346975, by rfl⟩ : syracuseStep 1795967 = 2693951) B2693951
theorem B1435817 : Blo 794341 1435817 := bstep (se 2 (by rfl) ⟨538431, by rfl⟩ : syracuseStep 1435817 = 1076863) B1076863
theorem B6454079 : Blo 794341 6454079 := bstep (se 1 (by rfl) ⟨4840559, by rfl⟩ : syracuseStep 6454079 = 9681119) B9681119
theorem B13958891 : Blo 794341 13958891 := bstep (se 1 (by rfl) ⟨10469168, by rfl⟩ : syracuseStep 13958891 = 20938337) B20938337
theorem B794623 : Blo 794341 794623 := bstep (se 1 (by rfl) ⟨595967, by rfl⟩ : syracuseStep 794623 = 1191935) B1191935
theorem B4302719 : Blo 794341 4302719 := bstep (se 1 (by rfl) ⟨3227039, by rfl⟩ : syracuseStep 4302719 = 6454079) B6454079
theorem B4534015 : Blo 794341 4534015 := bstep (se 1 (by rfl) ⟨3400511, by rfl⟩ : syracuseStep 4534015 = 6801023) B6801023
theorem B1196123 : Blo 794341 1196123 := bstep (se 1 (by rfl) ⟨897092, by rfl⟩ : syracuseStep 1196123 = 1794185) B1794185
theorem B1197311 : Blo 794341 1197311 := bstep (se 1 (by rfl) ⟨897983, by rfl⟩ : syracuseStep 1197311 = 1795967) B1795967
theorem B1792511 : Blo 794341 1792511 := bstep (se 1 (by rfl) ⟨1344383, by rfl⟩ : syracuseStep 1792511 = 2688767) B2688767
theorem B3828845 : Blo 794341 3828845 := bstep (se 3 (by rfl) ⟨717908, by rfl⟩ : syracuseStep 3828845 = 1435817) B1435817
theorem B3636271 : Blo 794341 3636271 := bstep (se 1 (by rfl) ⟨2727203, by rfl⟩ : syracuseStep 3636271 = 5454407) B5454407
theorem B9305927 : Blo 794341 9305927 := bstep (se 1 (by rfl) ⟨6979445, by rfl⟩ : syracuseStep 9305927 = 13958891) B13958891
theorem B6203951 : Blo 794341 6203951 := bstep (se 1 (by rfl) ⟨4652963, by rfl⟩ : syracuseStep 6203951 = 9305927) B9305927
theorem B797415 : Blo 794341 797415 := bstep (se 1 (by rfl) ⟨598061, by rfl⟩ : syracuseStep 797415 = 1196123) B1196123
theorem B798207 : Blo 794341 798207 := bstep (se 1 (by rfl) ⟨598655, by rfl⟩ : syracuseStep 798207 = 1197311) B1197311
theorem B1195007 : Blo 794341 1195007 := bstep (se 1 (by rfl) ⟨896255, by rfl⟩ : syracuseStep 1195007 = 1792511) B1792511
theorem B6045353 : Blo 794341 6045353 := bstep (se 2 (by rfl) ⟨2267007, by rfl⟩ : syracuseStep 6045353 = 4534015) B4534015
theorem B2868479 : Blo 794341 2868479 := bstep (se 1 (by rfl) ⟨2151359, by rfl⟩ : syracuseStep 2868479 = 4302719) B4302719
theorem B19393445 : Blo 794341 19393445 := bstep (se 4 (by rfl) ⟨1818135, by rfl⟩ : syracuseStep 19393445 = 3636271) B3636271
theorem B2552563 : Blo 794341 2552563 := bstep (se 1 (by rfl) ⟨1914422, by rfl⟩ : syracuseStep 2552563 = 3828845) B3828845
theorem B4135967 : Blo 794341 4135967 := bstep (se 1 (by rfl) ⟨3101975, by rfl⟩ : syracuseStep 4135967 = 6203951) B6203951
theorem B51715853 : Blo 794341 51715853 := bstep (se 3 (by rfl) ⟨9696722, by rfl⟩ : syracuseStep 51715853 = 19393445) B19393445
theorem B796671 : Blo 794341 796671 := bstep (se 1 (by rfl) ⟨597503, by rfl⟩ : syracuseStep 796671 = 1195007) B1195007
theorem B1912319 : Blo 794341 1912319 := bstep (se 1 (by rfl) ⟨1434239, by rfl⟩ : syracuseStep 1912319 = 2868479) B2868479
theorem B3403417 : Blo 794341 3403417 := bstep (se 2 (by rfl) ⟨1276281, by rfl⟩ : syracuseStep 3403417 = 2552563) B2552563
theorem B4030235 : Blo 794341 4030235 := bstep (se 1 (by rfl) ⟨3022676, by rfl⟩ : syracuseStep 4030235 = 6045353) B6045353
theorem B2757311 : Blo 794341 2757311 := bstep (se 1 (by rfl) ⟨2067983, by rfl⟩ : syracuseStep 2757311 = 4135967) B4135967
theorem B34477235 : Blo 794341 34477235 := bstep (se 1 (by rfl) ⟨25857926, by rfl⟩ : syracuseStep 34477235 = 51715853) B51715853
theorem B4537889 : Blo 794341 4537889 := bstep (se 2 (by rfl) ⟨1701708, by rfl⟩ : syracuseStep 4537889 = 3403417) B3403417
theorem B1274879 : Blo 794341 1274879 := bstep (se 1 (by rfl) ⟨956159, by rfl⟩ : syracuseStep 1274879 = 1912319) B1912319
theorem B2686823 : Blo 794341 2686823 := bstep (se 1 (by rfl) ⟨2015117, by rfl⟩ : syracuseStep 2686823 = 4030235) B4030235
theorem B1838207 : Blo 794341 1838207 := bstep (se 1 (by rfl) ⟨1378655, by rfl⟩ : syracuseStep 1838207 = 2757311) B2757311
theorem B3025259 : Blo 794341 3025259 := bstep (se 1 (by rfl) ⟨2268944, by rfl⟩ : syracuseStep 3025259 = 4537889) B4537889
theorem B22984823 : Blo 794341 22984823 := bstep (se 1 (by rfl) ⟨17238617, by rfl⟩ : syracuseStep 22984823 = 34477235) B34477235
theorem B1791215 : Blo 794341 1791215 := bstep (se 1 (by rfl) ⟨1343411, by rfl⟩ : syracuseStep 1791215 = 2686823) B2686823
theorem B3399677 : Blo 794341 3399677 := bstep (se 3 (by rfl) ⟨637439, by rfl⟩ : syracuseStep 3399677 = 1274879) B1274879
theorem B2266451 : Blo 794341 2266451 := bstep (se 1 (by rfl) ⟨1699838, by rfl⟩ : syracuseStep 2266451 = 3399677) B3399677
theorem B1194143 : Blo 794341 1194143 := bstep (se 1 (by rfl) ⟨895607, by rfl⟩ : syracuseStep 1194143 = 1791215) B1791215
theorem B2016839 : Blo 794341 2016839 := bstep (se 1 (by rfl) ⟨1512629, by rfl⟩ : syracuseStep 2016839 = 3025259) B3025259
theorem B4901885 : Blo 794341 4901885 := bstep (se 3 (by rfl) ⟨919103, by rfl⟩ : syracuseStep 4901885 = 1838207) B1838207
theorem B15323215 : Blo 794341 15323215 := bstep (se 1 (by rfl) ⟨11492411, by rfl⟩ : syracuseStep 15323215 = 22984823) B22984823
theorem B1344559 : Blo 794341 1344559 := bstep (se 1 (by rfl) ⟨1008419, by rfl⟩ : syracuseStep 1344559 = 2016839) B2016839
theorem B1510967 : Blo 794341 1510967 := bstep (se 1 (by rfl) ⟨1133225, by rfl⟩ : syracuseStep 1510967 = 2266451) B2266451
theorem B796095 : Blo 794341 796095 := bstep (se 1 (by rfl) ⟨597071, by rfl⟩ : syracuseStep 796095 = 1194143) B1194143
theorem B20430953 : Blo 794341 20430953 := bstep (se 2 (by rfl) ⟨7661607, by rfl⟩ : syracuseStep 20430953 = 15323215) B15323215
theorem B3267923 : Blo 794341 3267923 := bstep (se 1 (by rfl) ⟨2450942, by rfl⟩ : syracuseStep 3267923 = 4901885) B4901885
theorem B13620635 : Blo 794341 13620635 := bstep (se 1 (by rfl) ⟨10215476, by rfl⟩ : syracuseStep 13620635 = 20430953) B20430953
theorem B1792745 : Blo 794341 1792745 := bstep (se 2 (by rfl) ⟨672279, by rfl⟩ : syracuseStep 1792745 = 1344559) B1344559
theorem B1007311 : Blo 794341 1007311 := bstep (se 1 (by rfl) ⟨755483, by rfl⟩ : syracuseStep 1007311 = 1510967) B1510967
theorem B8714461 : Blo 794341 8714461 := bstep (se 3 (by rfl) ⟨1633961, by rfl⟩ : syracuseStep 8714461 = 3267923) B3267923
theorem B9080423 : Blo 794341 9080423 := bstep (se 1 (by rfl) ⟨6810317, by rfl⟩ : syracuseStep 9080423 = 13620635) B13620635
theorem B1195163 : Blo 794341 1195163 := bstep (se 1 (by rfl) ⟨896372, by rfl⟩ : syracuseStep 1195163 = 1792745) B1792745
theorem B11619281 : Blo 794341 11619281 := bstep (se 2 (by rfl) ⟨4357230, by rfl⟩ : syracuseStep 11619281 = 8714461) B8714461
theorem B1343081 : Blo 794341 1343081 := bstep (se 2 (by rfl) ⟨503655, by rfl⟩ : syracuseStep 1343081 = 1007311) B1007311
theorem B796775 : Blo 794341 796775 := bstep (se 1 (by rfl) ⟨597581, by rfl⟩ : syracuseStep 796775 = 1195163) B1195163
theorem B895387 : Blo 794341 895387 := bstep (se 1 (by rfl) ⟨671540, by rfl⟩ : syracuseStep 895387 = 1343081) B1343081
theorem B7746187 : Blo 794341 7746187 := bstep (se 1 (by rfl) ⟨5809640, by rfl⟩ : syracuseStep 7746187 = 11619281) B11619281
theorem B6053615 : Blo 794341 6053615 := bstep (se 1 (by rfl) ⟨4540211, by rfl⟩ : syracuseStep 6053615 = 9080423) B9080423
theorem B4035743 : Blo 794341 4035743 := bstep (se 1 (by rfl) ⟨3026807, by rfl⟩ : syracuseStep 4035743 = 6053615) B6053615
theorem B10328249 : Blo 794341 10328249 := bstep (se 2 (by rfl) ⟨3873093, by rfl⟩ : syracuseStep 10328249 = 7746187) B7746187
theorem B1193849 : Blo 794341 1193849 := bstep (se 2 (by rfl) ⟨447693, by rfl⟩ : syracuseStep 1193849 = 895387) B895387
theorem B2690495 : Blo 794341 2690495 := bstep (se 1 (by rfl) ⟨2017871, by rfl⟩ : syracuseStep 2690495 = 4035743) B4035743
theorem B795899 : Blo 794341 795899 := bstep (se 1 (by rfl) ⟨596924, by rfl⟩ : syracuseStep 795899 = 1193849) B1193849
theorem B27541997 : Blo 794341 27541997 := bstep (se 3 (by rfl) ⟨5164124, by rfl⟩ : syracuseStep 27541997 = 10328249) B10328249
theorem B18361331 : Blo 794341 18361331 := bstep (se 1 (by rfl) ⟨13770998, by rfl⟩ : syracuseStep 18361331 = 27541997) B27541997
theorem B1793663 : Blo 794341 1793663 := bstep (se 1 (by rfl) ⟨1345247, by rfl⟩ : syracuseStep 1793663 = 2690495) B2690495
theorem B1195775 : Blo 794341 1195775 := bstep (se 1 (by rfl) ⟨896831, by rfl⟩ : syracuseStep 1195775 = 1793663) B1793663
theorem B12240887 : Blo 794341 12240887 := bstep (se 1 (by rfl) ⟨9180665, by rfl⟩ : syracuseStep 12240887 = 18361331) B18361331
theorem B32642365 : Blo 794341 32642365 := bstep (se 3 (by rfl) ⟨6120443, by rfl⟩ : syracuseStep 32642365 = 12240887) B12240887
theorem B797183 : Blo 794341 797183 := bstep (se 1 (by rfl) ⟨597887, by rfl⟩ : syracuseStep 797183 = 1195775) B1195775
theorem B43523153 : Blo 794341 43523153 := bstep (se 2 (by rfl) ⟨16321182, by rfl⟩ : syracuseStep 43523153 = 32642365) B32642365
theorem B29015435 : Blo 794341 29015435 := bstep (se 1 (by rfl) ⟨21761576, by rfl⟩ : syracuseStep 29015435 = 43523153) B43523153
theorem B19343623 : Blo 794341 19343623 := bstep (se 1 (by rfl) ⟨14507717, by rfl⟩ : syracuseStep 19343623 = 29015435) B29015435
theorem B25791497 : Blo 794341 25791497 := bstep (se 2 (by rfl) ⟨9671811, by rfl⟩ : syracuseStep 25791497 = 19343623) B19343623
theorem B17194331 : Blo 794341 17194331 := bstep (se 1 (by rfl) ⟨12895748, by rfl⟩ : syracuseStep 17194331 = 25791497) B25791497
theorem B11462887 : Blo 794341 11462887 := bstep (se 1 (by rfl) ⟨8597165, by rfl⟩ : syracuseStep 11462887 = 17194331) B17194331
theorem B15283849 : Blo 794341 15283849 := bstep (se 2 (by rfl) ⟨5731443, by rfl⟩ : syracuseStep 15283849 = 11462887) B11462887
theorem B20378465 : Blo 794341 20378465 := bstep (se 2 (by rfl) ⟨7641924, by rfl⟩ : syracuseStep 20378465 = 15283849) B15283849
theorem B13585643 : Blo 794341 13585643 := bstep (se 1 (by rfl) ⟨10189232, by rfl⟩ : syracuseStep 13585643 = 20378465) B20378465
theorem B9057095 : Blo 794341 9057095 := bstep (se 1 (by rfl) ⟨6792821, by rfl⟩ : syracuseStep 9057095 = 13585643) B13585643
theorem B6038063 : Blo 794341 6038063 := bstep (se 1 (by rfl) ⟨4528547, by rfl⟩ : syracuseStep 6038063 = 9057095) B9057095
theorem B4025375 : Blo 794341 4025375 := bstep (se 1 (by rfl) ⟨3019031, by rfl⟩ : syracuseStep 4025375 = 6038063) B6038063
theorem B2683583 : Blo 794341 2683583 := bstep (se 1 (by rfl) ⟨2012687, by rfl⟩ : syracuseStep 2683583 = 4025375) B4025375
theorem B1789055 : Blo 794341 1789055 := bstep (se 1 (by rfl) ⟨1341791, by rfl⟩ : syracuseStep 1789055 = 2683583) B2683583
theorem B1192703 : Blo 794341 1192703 := bstep (se 1 (by rfl) ⟨894527, by rfl⟩ : syracuseStep 1192703 = 1789055) B1789055
theorem B795135 : Blo 794341 795135 := bstep (se 1 (by rfl) ⟨596351, by rfl⟩ : syracuseStep 795135 = 1192703) B1192703

theorem C0 (j : ℕ) (h1 : 198585 ≤ j) (h2 : j ≤ 199284) : Blo 794341 (4 * j + 3) := by
  interval_cases j
  · exact B794343
  · exact B794347
  · exact B794351
  · exact B794355
  · exact B794359
  · exact B794363
  · exact B794367
  · exact B794371
  · exact B794375
  · exact B794379
  · exact B794383
  · exact B794387
  · exact B794391
  · exact B794395
  · exact B794399
  · exact B794403
  · exact B794407
  · exact B794411
  · exact B794415
  · exact B794419
  · exact B794423
  · exact B794427
  · exact B794431
  · exact B794435
  · exact B794439
  · exact B794443
  · exact B794447
  · exact B794451
  · exact B794455
  · exact B794459
  · exact B794463
  · exact B794467
  · exact B794471
  · exact B794475
  · exact B794479
  · exact B794483
  · exact B794487
  · exact B794491
  · exact B794495
  · exact B794499
  · exact B794503
  · exact B794507
  · exact B794511
  · exact B794515
  · exact B794519
  · exact B794523
  · exact B794527
  · exact B794531
  · exact B794535
  · exact B794539
  · exact B794543
  · exact B794547
  · exact B794551
  · exact B794555
  · exact B794559
  · exact B794563
  · exact B794567
  · exact B794571
  · exact B794575
  · exact B794579
  · exact B794583
  · exact B794587
  · exact B794591
  · exact B794595
  · exact B794599
  · exact B794603
  · exact B794607
  · exact B794611
  · exact B794615
  · exact B794619
  · exact B794623
  · exact B794627
  · exact B794631
  · exact B794635
  · exact B794639
  · exact B794643
  · exact B794647
  · exact B794651
  · exact B794655
  · exact B794659
  · exact B794663
  · exact B794667
  · exact B794671
  · exact B794675
  · exact B794679
  · exact B794683
  · exact B794687
  · exact B794691
  · exact B794695
  · exact B794699
  · exact B794703
  · exact B794707
  · exact B794711
  · exact B794715
  · exact B794719
  · exact B794723
  · exact B794727
  · exact B794731
  · exact B794735
  · exact B794739
  · exact B794743
  · exact B794747
  · exact B794751
  · exact B794755
  · exact B794759
  · exact B794763
  · exact B794767
  · exact B794771
  · exact B794775
  · exact B794779
  · exact B794783
  · exact B794787
  · exact B794791
  · exact B794795
  · exact B794799
  · exact B794803
  · exact B794807
  · exact B794811
  · exact B794815
  · exact B794819
  · exact B794823
  · exact B794827
  · exact B794831
  · exact B794835
  · exact B794839
  · exact B794843
  · exact B794847
  · exact B794851
  · exact B794855
  · exact B794859
  · exact B794863
  · exact B794867
  · exact B794871
  · exact B794875
  · exact B794879
  · exact B794883
  · exact B794887
  · exact B794891
  · exact B794895
  · exact B794899
  · exact B794903
  · exact B794907
  · exact B794911
  · exact B794915
  · exact B794919
  · exact B794923
  · exact B794927
  · exact B794931
  · exact B794935
  · exact B794939
  · exact B794943
  · exact B794947
  · exact B794951
  · exact B794955
  · exact B794959
  · exact B794963
  · exact B794967
  · exact B794971
  · exact B794975
  · exact B794979
  · exact B794983
  · exact B794987
  · exact B794991
  · exact B794995
  · exact B794999
  · exact B795003
  · exact B795007
  · exact B795011
  · exact B795015
  · exact B795019
  · exact B795023
  · exact B795027
  · exact B795031
  · exact B795035
  · exact B795039
  · exact B795043
  · exact B795047
  · exact B795051
  · exact B795055
  · exact B795059
  · exact B795063
  · exact B795067
  · exact B795071
  · exact B795075
  · exact B795079
  · exact B795083
  · exact B795087
  · exact B795091
  · exact B795095
  · exact B795099
  · exact B795103
  · exact B795107
  · exact B795111
  · exact B795115
  · exact B795119
  · exact B795123
  · exact B795127
  · exact B795131
  · exact B795135
  · exact B795139
  · exact B795143
  · exact B795147
  · exact B795151
  · exact B795155
  · exact B795159
  · exact B795163
  · exact B795167
  · exact B795171
  · exact B795175
  · exact B795179
  · exact B795183
  · exact B795187
  · exact B795191
  · exact B795195
  · exact B795199
  · exact B795203
  · exact B795207
  · exact B795211
  · exact B795215
  · exact B795219
  · exact B795223
  · exact B795227
  · exact B795231
  · exact B795235
  · exact B795239
  · exact B795243
  · exact B795247
  · exact B795251
  · exact B795255
  · exact B795259
  · exact B795263
  · exact B795267
  · exact B795271
  · exact B795275
  · exact B795279
  · exact B795283
  · exact B795287
  · exact B795291
  · exact B795295
  · exact B795299
  · exact B795303
  · exact B795307
  · exact B795311
  · exact B795315
  · exact B795319
  · exact B795323
  · exact B795327
  · exact B795331
  · exact B795335
  · exact B795339
  · exact B795343
  · exact B795347
  · exact B795351
  · exact B795355
  · exact B795359
  · exact B795363
  · exact B795367
  · exact B795371
  · exact B795375
  · exact B795379
  · exact B795383
  · exact B795387
  · exact B795391
  · exact B795395
  · exact B795399
  · exact B795403
  · exact B795407
  · exact B795411
  · exact B795415
  · exact B795419
  · exact B795423
  · exact B795427
  · exact B795431
  · exact B795435
  · exact B795439
  · exact B795443
  · exact B795447
  · exact B795451
  · exact B795455
  · exact B795459
  · exact B795463
  · exact B795467
  · exact B795471
  · exact B795475
  · exact B795479
  · exact B795483
  · exact B795487
  · exact B795491
  · exact B795495
  · exact B795499
  · exact B795503
  · exact B795507
  · exact B795511
  · exact B795515
  · exact B795519
  · exact B795523
  · exact B795527
  · exact B795531
  · exact B795535
  · exact B795539
  · exact B795543
  · exact B795547
  · exact B795551
  · exact B795555
  · exact B795559
  · exact B795563
  · exact B795567
  · exact B795571
  · exact B795575
  · exact B795579
  · exact B795583
  · exact B795587
  · exact B795591
  · exact B795595
  · exact B795599
  · exact B795603
  · exact B795607
  · exact B795611
  · exact B795615
  · exact B795619
  · exact B795623
  · exact B795627
  · exact B795631
  · exact B795635
  · exact B795639
  · exact B795643
  · exact B795647
  · exact B795651
  · exact B795655
  · exact B795659
  · exact B795663
  · exact B795667
  · exact B795671
  · exact B795675
  · exact B795679
  · exact B795683
  · exact B795687
  · exact B795691
  · exact B795695
  · exact B795699
  · exact B795703
  · exact B795707
  · exact B795711
  · exact B795715
  · exact B795719
  · exact B795723
  · exact B795727
  · exact B795731
  · exact B795735
  · exact B795739
  · exact B795743
  · exact B795747
  · exact B795751
  · exact B795755
  · exact B795759
  · exact B795763
  · exact B795767
  · exact B795771
  · exact B795775
  · exact B795779
  · exact B795783
  · exact B795787
  · exact B795791
  · exact B795795
  · exact B795799
  · exact B795803
  · exact B795807
  · exact B795811
  · exact B795815
  · exact B795819
  · exact B795823
  · exact B795827
  · exact B795831
  · exact B795835
  · exact B795839
  · exact B795843
  · exact B795847
  · exact B795851
  · exact B795855
  · exact B795859
  · exact B795863
  · exact B795867
  · exact B795871
  · exact B795875
  · exact B795879
  · exact B795883
  · exact B795887
  · exact B795891
  · exact B795895
  · exact B795899
  · exact B795903
  · exact B795907
  · exact B795911
  · exact B795915
  · exact B795919
  · exact B795923
  · exact B795927
  · exact B795931
  · exact B795935
  · exact B795939
  · exact B795943
  · exact B795947
  · exact B795951
  · exact B795955
  · exact B795959
  · exact B795963
  · exact B795967
  · exact B795971
  · exact B795975
  · exact B795979
  · exact B795983
  · exact B795987
  · exact B795991
  · exact B795995
  · exact B795999
  · exact B796003
  · exact B796007
  · exact B796011
  · exact B796015
  · exact B796019
  · exact B796023
  · exact B796027
  · exact B796031
  · exact B796035
  · exact B796039
  · exact B796043
  · exact B796047
  · exact B796051
  · exact B796055
  · exact B796059
  · exact B796063
  · exact B796067
  · exact B796071
  · exact B796075
  · exact B796079
  · exact B796083
  · exact B796087
  · exact B796091
  · exact B796095
  · exact B796099
  · exact B796103
  · exact B796107
  · exact B796111
  · exact B796115
  · exact B796119
  · exact B796123
  · exact B796127
  · exact B796131
  · exact B796135
  · exact B796139
  · exact B796143
  · exact B796147
  · exact B796151
  · exact B796155
  · exact B796159
  · exact B796163
  · exact B796167
  · exact B796171
  · exact B796175
  · exact B796179
  · exact B796183
  · exact B796187
  · exact B796191
  · exact B796195
  · exact B796199
  · exact B796203
  · exact B796207
  · exact B796211
  · exact B796215
  · exact B796219
  · exact B796223
  · exact B796227
  · exact B796231
  · exact B796235
  · exact B796239
  · exact B796243
  · exact B796247
  · exact B796251
  · exact B796255
  · exact B796259
  · exact B796263
  · exact B796267
  · exact B796271
  · exact B796275
  · exact B796279
  · exact B796283
  · exact B796287
  · exact B796291
  · exact B796295
  · exact B796299
  · exact B796303
  · exact B796307
  · exact B796311
  · exact B796315
  · exact B796319
  · exact B796323
  · exact B796327
  · exact B796331
  · exact B796335
  · exact B796339
  · exact B796343
  · exact B796347
  · exact B796351
  · exact B796355
  · exact B796359
  · exact B796363
  · exact B796367
  · exact B796371
  · exact B796375
  · exact B796379
  · exact B796383
  · exact B796387
  · exact B796391
  · exact B796395
  · exact B796399
  · exact B796403
  · exact B796407
  · exact B796411
  · exact B796415
  · exact B796419
  · exact B796423
  · exact B796427
  · exact B796431
  · exact B796435
  · exact B796439
  · exact B796443
  · exact B796447
  · exact B796451
  · exact B796455
  · exact B796459
  · exact B796463
  · exact B796467
  · exact B796471
  · exact B796475
  · exact B796479
  · exact B796483
  · exact B796487
  · exact B796491
  · exact B796495
  · exact B796499
  · exact B796503
  · exact B796507
  · exact B796511
  · exact B796515
  · exact B796519
  · exact B796523
  · exact B796527
  · exact B796531
  · exact B796535
  · exact B796539
  · exact B796543
  · exact B796547
  · exact B796551
  · exact B796555
  · exact B796559
  · exact B796563
  · exact B796567
  · exact B796571
  · exact B796575
  · exact B796579
  · exact B796583
  · exact B796587
  · exact B796591
  · exact B796595
  · exact B796599
  · exact B796603
  · exact B796607
  · exact B796611
  · exact B796615
  · exact B796619
  · exact B796623
  · exact B796627
  · exact B796631
  · exact B796635
  · exact B796639
  · exact B796643
  · exact B796647
  · exact B796651
  · exact B796655
  · exact B796659
  · exact B796663
  · exact B796667
  · exact B796671
  · exact B796675
  · exact B796679
  · exact B796683
  · exact B796687
  · exact B796691
  · exact B796695
  · exact B796699
  · exact B796703
  · exact B796707
  · exact B796711
  · exact B796715
  · exact B796719
  · exact B796723
  · exact B796727
  · exact B796731
  · exact B796735
  · exact B796739
  · exact B796743
  · exact B796747
  · exact B796751
  · exact B796755
  · exact B796759
  · exact B796763
  · exact B796767
  · exact B796771
  · exact B796775
  · exact B796779
  · exact B796783
  · exact B796787
  · exact B796791
  · exact B796795
  · exact B796799
  · exact B796803
  · exact B796807
  · exact B796811
  · exact B796815
  · exact B796819
  · exact B796823
  · exact B796827
  · exact B796831
  · exact B796835
  · exact B796839
  · exact B796843
  · exact B796847
  · exact B796851
  · exact B796855
  · exact B796859
  · exact B796863
  · exact B796867
  · exact B796871
  · exact B796875
  · exact B796879
  · exact B796883
  · exact B796887
  · exact B796891
  · exact B796895
  · exact B796899
  · exact B796903
  · exact B796907
  · exact B796911
  · exact B796915
  · exact B796919
  · exact B796923
  · exact B796927
  · exact B796931
  · exact B796935
  · exact B796939
  · exact B796943
  · exact B796947
  · exact B796951
  · exact B796955
  · exact B796959
  · exact B796963
  · exact B796967
  · exact B796971
  · exact B796975
  · exact B796979
  · exact B796983
  · exact B796987
  · exact B796991
  · exact B796995
  · exact B796999
  · exact B797003
  · exact B797007
  · exact B797011
  · exact B797015
  · exact B797019
  · exact B797023
  · exact B797027
  · exact B797031
  · exact B797035
  · exact B797039
  · exact B797043
  · exact B797047
  · exact B797051
  · exact B797055
  · exact B797059
  · exact B797063
  · exact B797067
  · exact B797071
  · exact B797075
  · exact B797079
  · exact B797083
  · exact B797087
  · exact B797091
  · exact B797095
  · exact B797099
  · exact B797103
  · exact B797107
  · exact B797111
  · exact B797115
  · exact B797119
  · exact B797123
  · exact B797127
  · exact B797131
  · exact B797135
  · exact B797139

theorem C1 (j : ℕ) (h1 : 199285 ≤ j) (h2 : j ≤ 199584) : Blo 794341 (4 * j + 3) := by
  interval_cases j
  · exact B797143
  · exact B797147
  · exact B797151
  · exact B797155
  · exact B797159
  · exact B797163
  · exact B797167
  · exact B797171
  · exact B797175
  · exact B797179
  · exact B797183
  · exact B797187
  · exact B797191
  · exact B797195
  · exact B797199
  · exact B797203
  · exact B797207
  · exact B797211
  · exact B797215
  · exact B797219
  · exact B797223
  · exact B797227
  · exact B797231
  · exact B797235
  · exact B797239
  · exact B797243
  · exact B797247
  · exact B797251
  · exact B797255
  · exact B797259
  · exact B797263
  · exact B797267
  · exact B797271
  · exact B797275
  · exact B797279
  · exact B797283
  · exact B797287
  · exact B797291
  · exact B797295
  · exact B797299
  · exact B797303
  · exact B797307
  · exact B797311
  · exact B797315
  · exact B797319
  · exact B797323
  · exact B797327
  · exact B797331
  · exact B797335
  · exact B797339
  · exact B797343
  · exact B797347
  · exact B797351
  · exact B797355
  · exact B797359
  · exact B797363
  · exact B797367
  · exact B797371
  · exact B797375
  · exact B797379
  · exact B797383
  · exact B797387
  · exact B797391
  · exact B797395
  · exact B797399
  · exact B797403
  · exact B797407
  · exact B797411
  · exact B797415
  · exact B797419
  · exact B797423
  · exact B797427
  · exact B797431
  · exact B797435
  · exact B797439
  · exact B797443
  · exact B797447
  · exact B797451
  · exact B797455
  · exact B797459
  · exact B797463
  · exact B797467
  · exact B797471
  · exact B797475
  · exact B797479
  · exact B797483
  · exact B797487
  · exact B797491
  · exact B797495
  · exact B797499
  · exact B797503
  · exact B797507
  · exact B797511
  · exact B797515
  · exact B797519
  · exact B797523
  · exact B797527
  · exact B797531
  · exact B797535
  · exact B797539
  · exact B797543
  · exact B797547
  · exact B797551
  · exact B797555
  · exact B797559
  · exact B797563
  · exact B797567
  · exact B797571
  · exact B797575
  · exact B797579
  · exact B797583
  · exact B797587
  · exact B797591
  · exact B797595
  · exact B797599
  · exact B797603
  · exact B797607
  · exact B797611
  · exact B797615
  · exact B797619
  · exact B797623
  · exact B797627
  · exact B797631
  · exact B797635
  · exact B797639
  · exact B797643
  · exact B797647
  · exact B797651
  · exact B797655
  · exact B797659
  · exact B797663
  · exact B797667
  · exact B797671
  · exact B797675
  · exact B797679
  · exact B797683
  · exact B797687
  · exact B797691
  · exact B797695
  · exact B797699
  · exact B797703
  · exact B797707
  · exact B797711
  · exact B797715
  · exact B797719
  · exact B797723
  · exact B797727
  · exact B797731
  · exact B797735
  · exact B797739
  · exact B797743
  · exact B797747
  · exact B797751
  · exact B797755
  · exact B797759
  · exact B797763
  · exact B797767
  · exact B797771
  · exact B797775
  · exact B797779
  · exact B797783
  · exact B797787
  · exact B797791
  · exact B797795
  · exact B797799
  · exact B797803
  · exact B797807
  · exact B797811
  · exact B797815
  · exact B797819
  · exact B797823
  · exact B797827
  · exact B797831
  · exact B797835
  · exact B797839
  · exact B797843
  · exact B797847
  · exact B797851
  · exact B797855
  · exact B797859
  · exact B797863
  · exact B797867
  · exact B797871
  · exact B797875
  · exact B797879
  · exact B797883
  · exact B797887
  · exact B797891
  · exact B797895
  · exact B797899
  · exact B797903
  · exact B797907
  · exact B797911
  · exact B797915
  · exact B797919
  · exact B797923
  · exact B797927
  · exact B797931
  · exact B797935
  · exact B797939
  · exact B797943
  · exact B797947
  · exact B797951
  · exact B797955
  · exact B797959
  · exact B797963
  · exact B797967
  · exact B797971
  · exact B797975
  · exact B797979
  · exact B797983
  · exact B797987
  · exact B797991
  · exact B797995
  · exact B797999
  · exact B798003
  · exact B798007
  · exact B798011
  · exact B798015
  · exact B798019
  · exact B798023
  · exact B798027
  · exact B798031
  · exact B798035
  · exact B798039
  · exact B798043
  · exact B798047
  · exact B798051
  · exact B798055
  · exact B798059
  · exact B798063
  · exact B798067
  · exact B798071
  · exact B798075
  · exact B798079
  · exact B798083
  · exact B798087
  · exact B798091
  · exact B798095
  · exact B798099
  · exact B798103
  · exact B798107
  · exact B798111
  · exact B798115
  · exact B798119
  · exact B798123
  · exact B798127
  · exact B798131
  · exact B798135
  · exact B798139
  · exact B798143
  · exact B798147
  · exact B798151
  · exact B798155
  · exact B798159
  · exact B798163
  · exact B798167
  · exact B798171
  · exact B798175
  · exact B798179
  · exact B798183
  · exact B798187
  · exact B798191
  · exact B798195
  · exact B798199
  · exact B798203
  · exact B798207
  · exact B798211
  · exact B798215
  · exact B798219
  · exact B798223
  · exact B798227
  · exact B798231
  · exact B798235
  · exact B798239
  · exact B798243
  · exact B798247
  · exact B798251
  · exact B798255
  · exact B798259
  · exact B798263
  · exact B798267
  · exact B798271
  · exact B798275
  · exact B798279
  · exact B798283
  · exact B798287
  · exact B798291
  · exact B798295
  · exact B798299
  · exact B798303
  · exact B798307
  · exact B798311
  · exact B798315
  · exact B798319
  · exact B798323
  · exact B798327
  · exact B798331
  · exact B798335
  · exact B798339

theorem solution (m : ℕ) (hlo : 794341 ≤ m) (hhi : m ≤ 798341) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 198585 ≤ j := by omega
    have hj2 : j ≤ 199584 := by omega
    have hb : Blo 794341 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 199285 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
