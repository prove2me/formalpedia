-- Prove2me | solution 1 for syracuse_descends_range_1419529_1421529
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:41:29.157933+00:00
-- url     : https://prove2.me/submissions/21cacefb-8500-478d-a26b-8bd96258d41f

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


theorem B1597441 : Blo 1419529 1597441 := bbase (se 2 (by rfl) ⟨599040, by rfl⟩ : syracuseStep 1597441 = 1198081) (by norm_num)
theorem B2129933 : Blo 1419529 2129933 := bbase (se 3 (by rfl) ⟨399362, by rfl⟩ : syracuseStep 2129933 = 798725) (by norm_num)
theorem B2695189 : Blo 1419529 2695189 := bbase (se 6 (by rfl) ⟨63168, by rfl⟩ : syracuseStep 2695189 = 126337) (by norm_num)
theorem B3596309 : Blo 1419529 3596309 := bbase (se 6 (by rfl) ⟨84288, by rfl⟩ : syracuseStep 3596309 = 168577) (by norm_num)
theorem B3194909 : Blo 1419529 3194909 := bbase (se 3 (by rfl) ⟨599045, by rfl⟩ : syracuseStep 3194909 = 1198091) (by norm_num)
theorem B2129957 : Blo 1419529 2129957 := bbase (se 4 (by rfl) ⟨199683, by rfl⟩ : syracuseStep 2129957 = 399367) (by norm_num)
theorem B1597477 : Blo 1419529 1597477 := bbase (se 4 (by rfl) ⟨149763, by rfl⟩ : syracuseStep 1597477 = 299527) (by norm_num)
theorem B4612133 : Blo 1419529 4612133 := bbase (se 4 (by rfl) ⟨432387, by rfl⟩ : syracuseStep 4612133 = 864775) (by norm_num)
theorem B4046885 : Blo 1419529 4046885 := bbase (se 4 (by rfl) ⟨379395, by rfl⟩ : syracuseStep 4046885 = 758791) (by norm_num)
theorem B2129981 : Blo 1419529 2129981 := bbase (se 3 (by rfl) ⟨399371, by rfl⟩ : syracuseStep 2129981 = 798743) (by norm_num)
theorem B1597513 : Blo 1419529 1597513 := bbase (se 2 (by rfl) ⟨599067, by rfl⟩ : syracuseStep 1597513 = 1198135) (by norm_num)
theorem B2130005 : Blo 1419529 2130005 := bbase (se 8 (by rfl) ⟨12480, by rfl⟩ : syracuseStep 2130005 = 24961) (by norm_num)
theorem B3194981 : Blo 1419529 3194981 := bbase (se 4 (by rfl) ⟨299529, by rfl⟩ : syracuseStep 3194981 = 599059) (by norm_num)
theorem B2130029 : Blo 1419529 2130029 := bbase (se 3 (by rfl) ⟨399380, by rfl⟩ : syracuseStep 2130029 = 798761) (by norm_num)
theorem B1597549 : Blo 1419529 1597549 := bbase (se 3 (by rfl) ⟨299540, by rfl⟩ : syracuseStep 1597549 = 599081) (by norm_num)
theorem B2130053 : Blo 1419529 2130053 := bbase (se 4 (by rfl) ⟨199692, by rfl⟩ : syracuseStep 2130053 = 399385) (by norm_num)
theorem B1597585 : Blo 1419529 1597585 := bbase (se 2 (by rfl) ⟨599094, by rfl⟩ : syracuseStep 1597585 = 1198189) (by norm_num)
theorem B23052437 : Blo 1419529 23052437 := bbase (se 6 (by rfl) ⟨540291, by rfl⟩ : syracuseStep 23052437 = 1080583) (by norm_num)
theorem B2130077 : Blo 1419529 2130077 := bbase (se 3 (by rfl) ⟨399389, by rfl⟩ : syracuseStep 2130077 = 798779) (by norm_num)
theorem B3195053 : Blo 1419529 3195053 := bbase (se 3 (by rfl) ⟨599072, by rfl⟩ : syracuseStep 3195053 = 1198145) (by norm_num)
theorem B2695349 : Blo 1419529 2695349 := bbase (se 5 (by rfl) ⟨126344, by rfl⟩ : syracuseStep 2695349 = 252689) (by norm_num)
theorem B2130101 : Blo 1419529 2130101 := bbase (se 5 (by rfl) ⟨99848, by rfl⟩ : syracuseStep 2130101 = 199697) (by norm_num)
theorem B1597621 : Blo 1419529 1597621 := bbase (se 5 (by rfl) ⟨74888, by rfl⟩ : syracuseStep 1597621 = 149777) (by norm_num)
theorem B2130125 : Blo 1419529 2130125 := bbase (se 3 (by rfl) ⟨399398, by rfl⟩ : syracuseStep 2130125 = 798797) (by norm_num)
theorem B8536277 : Blo 1419529 8536277 := bbase (se 7 (by rfl) ⟨100034, by rfl⟩ : syracuseStep 8536277 = 200069) (by norm_num)
theorem B3596501 : Blo 1419529 3596501 := bbase (se 7 (by rfl) ⟨42146, by rfl⟩ : syracuseStep 3596501 = 84293) (by norm_num)
theorem B1597657 : Blo 1419529 1597657 := bbase (se 2 (by rfl) ⟨599121, by rfl⟩ : syracuseStep 1597657 = 1198243) (by norm_num)
theorem B2130149 : Blo 1419529 2130149 := bbase (se 4 (by rfl) ⟨199701, by rfl⟩ : syracuseStep 2130149 = 399403) (by norm_num)
theorem B3195125 : Blo 1419529 3195125 := bbase (se 5 (by rfl) ⟨149771, by rfl⟩ : syracuseStep 3195125 = 299543) (by norm_num)
theorem B2130173 : Blo 1419529 2130173 := bbase (se 3 (by rfl) ⟨399407, by rfl⟩ : syracuseStep 2130173 = 798815) (by norm_num)
theorem B1597693 : Blo 1419529 1597693 := bbase (se 3 (by rfl) ⟨299567, by rfl⟩ : syracuseStep 1597693 = 599135) (by norm_num)
theorem B2130197 : Blo 1419529 2130197 := bbase (se 6 (by rfl) ⟨49926, by rfl⟩ : syracuseStep 2130197 = 99853) (by norm_num)
theorem B8642837 : Blo 1419529 8642837 := bbase (se 6 (by rfl) ⟨202566, by rfl⟩ : syracuseStep 8642837 = 405133) (by norm_num)
theorem B1597729 : Blo 1419529 1597729 := bbase (se 2 (by rfl) ⟨599148, by rfl⟩ : syracuseStep 1597729 = 1198297) (by norm_num)
theorem B6070565 : Blo 1419529 6070565 := bbase (se 4 (by rfl) ⟨569115, by rfl⟩ : syracuseStep 6070565 = 1138231) (by norm_num)
theorem B2130221 : Blo 1419529 2130221 := bbase (se 3 (by rfl) ⟨399416, by rfl⟩ : syracuseStep 2130221 = 798833) (by norm_num)
theorem B13844789 : Blo 1419529 13844789 := bbase (se 5 (by rfl) ⟨648974, by rfl⟩ : syracuseStep 13844789 = 1297949) (by norm_num)
theorem B3195197 : Blo 1419529 3195197 := bbase (se 3 (by rfl) ⟨599099, by rfl⟩ : syracuseStep 3195197 = 1198199) (by norm_num)
theorem B2695493 : Blo 1419529 2695493 := bbase (se 4 (by rfl) ⟨252702, by rfl⟩ : syracuseStep 2695493 = 505405) (by norm_num)
theorem B2130245 : Blo 1419529 2130245 := bbase (se 4 (by rfl) ⟨199710, by rfl⟩ : syracuseStep 2130245 = 399421) (by norm_num)
theorem B1597765 : Blo 1419529 1597765 := bbase (se 4 (by rfl) ⟨149790, by rfl⟩ : syracuseStep 1597765 = 299581) (by norm_num)
theorem B4792661 : Blo 1419529 4792661 := bbase (se 10 (by rfl) ⟨7020, by rfl⟩ : syracuseStep 4792661 = 14041) (by norm_num)
theorem B2130269 : Blo 1419529 2130269 := bbase (se 3 (by rfl) ⟨399425, by rfl⟩ : syracuseStep 2130269 = 798851) (by norm_num)
theorem B1597801 : Blo 1419529 1597801 := bbase (se 2 (by rfl) ⟨599175, by rfl⟩ : syracuseStep 1597801 = 1198351) (by norm_num)
theorem B2130293 : Blo 1419529 2130293 := bbase (se 5 (by rfl) ⟨99857, by rfl⟩ : syracuseStep 2130293 = 199715) (by norm_num)
theorem B3195269 : Blo 1419529 3195269 := bbase (se 4 (by rfl) ⟨299556, by rfl⟩ : syracuseStep 3195269 = 599113) (by norm_num)
theorem B2130317 : Blo 1419529 2130317 := bbase (se 3 (by rfl) ⟨399434, by rfl⟩ : syracuseStep 2130317 = 798869) (by norm_num)
theorem B1597837 : Blo 1419529 1597837 := bbase (se 3 (by rfl) ⟨299594, by rfl⟩ : syracuseStep 1597837 = 599189) (by norm_num)
theorem B2130341 : Blo 1419529 2130341 := bbase (se 4 (by rfl) ⟨199719, by rfl⟩ : syracuseStep 2130341 = 399439) (by norm_num)
theorem B1597873 : Blo 1419529 1597873 := bbase (se 2 (by rfl) ⟨599202, by rfl⟩ : syracuseStep 1597873 = 1198405) (by norm_num)
theorem B2130365 : Blo 1419529 2130365 := bbase (se 3 (by rfl) ⟨399443, by rfl⟩ : syracuseStep 2130365 = 798887) (by norm_num)
theorem B3195341 : Blo 1419529 3195341 := bbase (se 3 (by rfl) ⟨599126, by rfl⟩ : syracuseStep 3195341 = 1198253) (by norm_num)
theorem B2769365 : Blo 1419529 2769365 := bbase (se 7 (by rfl) ⟨32453, by rfl⟩ : syracuseStep 2769365 = 64907) (by norm_num)
theorem B2130389 : Blo 1419529 2130389 := bbase (se 7 (by rfl) ⟨24965, by rfl⟩ : syracuseStep 2130389 = 49931) (by norm_num)
theorem B1597909 : Blo 1419529 1597909 := bbase (se 7 (by rfl) ⟨18725, by rfl⟩ : syracuseStep 1597909 = 37451) (by norm_num)
theorem B4047317 : Blo 1419529 4047317 := bbase (se 7 (by rfl) ⟨47429, by rfl⟩ : syracuseStep 4047317 = 94859) (by norm_num)
theorem B1516001 : Blo 1419529 1516001 := bbase (se 2 (by rfl) ⟨568500, by rfl⟩ : syracuseStep 1516001 = 1137001) (by norm_num)
theorem B2130413 : Blo 1419529 2130413 := bbase (se 3 (by rfl) ⟨399452, by rfl⟩ : syracuseStep 2130413 = 798905) (by norm_num)
theorem B1597945 : Blo 1419529 1597945 := bbase (se 2 (by rfl) ⟨599229, by rfl⟩ : syracuseStep 1597945 = 1198459) (by norm_num)
theorem B2130437 : Blo 1419529 2130437 := bbase (se 4 (by rfl) ⟨199728, by rfl⟩ : syracuseStep 2130437 = 399457) (by norm_num)
theorem B3195413 : Blo 1419529 3195413 := bbase (se 6 (by rfl) ⟨74892, by rfl⟩ : syracuseStep 3195413 = 149785) (by norm_num)
theorem B2130461 : Blo 1419529 2130461 := bbase (se 3 (by rfl) ⟨399461, by rfl⟩ : syracuseStep 2130461 = 798923) (by norm_num)
theorem B1597981 : Blo 1419529 1597981 := bbase (se 3 (by rfl) ⟨299621, by rfl⟩ : syracuseStep 1597981 = 599243) (by norm_num)
theorem B3596845 : Blo 1419529 3596845 := bbase (se 3 (by rfl) ⟨674408, by rfl⟩ : syracuseStep 3596845 = 1348817) (by norm_num)
theorem B2130485 : Blo 1419529 2130485 := bbase (se 5 (by rfl) ⟨99866, by rfl⟩ : syracuseStep 2130485 = 199733) (by norm_num)
theorem B1598017 : Blo 1419529 1598017 := bbase (se 2 (by rfl) ⟨599256, by rfl⟩ : syracuseStep 1598017 = 1198513) (by norm_num)
theorem B2130509 : Blo 1419529 2130509 := bbase (se 3 (by rfl) ⟨399470, by rfl⟩ : syracuseStep 2130509 = 798941) (by norm_num)
theorem B3195485 : Blo 1419529 3195485 := bbase (se 3 (by rfl) ⟨599153, by rfl⟩ : syracuseStep 3195485 = 1198307) (by norm_num)
theorem B2695781 : Blo 1419529 2695781 := bbase (se 4 (by rfl) ⟨252729, by rfl⟩ : syracuseStep 2695781 = 505459) (by norm_num)
theorem B2130533 : Blo 1419529 2130533 := bbase (se 4 (by rfl) ⟨199737, by rfl⟩ : syracuseStep 2130533 = 399475) (by norm_num)
theorem B1598053 : Blo 1419529 1598053 := bbase (se 4 (by rfl) ⟨149817, by rfl⟩ : syracuseStep 1598053 = 299635) (by norm_num)
theorem B2130557 : Blo 1419529 2130557 := bbase (se 3 (by rfl) ⟨399479, by rfl⟩ : syracuseStep 2130557 = 798959) (by norm_num)
theorem B1598089 : Blo 1419529 1598089 := bbase (se 2 (by rfl) ⟨599283, by rfl⟩ : syracuseStep 1598089 = 1198567) (by norm_num)
theorem B2130581 : Blo 1419529 2130581 := bbase (se 6 (by rfl) ⟨49935, by rfl⟩ : syracuseStep 2130581 = 99871) (by norm_num)
theorem B3596957 : Blo 1419529 3596957 := bbase (se 3 (by rfl) ⟨674429, by rfl⟩ : syracuseStep 3596957 = 1348859) (by norm_num)
theorem B3195557 : Blo 1419529 3195557 := bbase (se 4 (by rfl) ⟨299583, by rfl⟩ : syracuseStep 3195557 = 599167) (by norm_num)
theorem B2130605 : Blo 1419529 2130605 := bbase (se 3 (by rfl) ⟨399488, by rfl⟩ : syracuseStep 2130605 = 798977) (by norm_num)
theorem B1598125 : Blo 1419529 1598125 := bbase (se 3 (by rfl) ⟨299648, by rfl⟩ : syracuseStep 1598125 = 599297) (by norm_num)
theorem B2130629 : Blo 1419529 2130629 := bbase (se 4 (by rfl) ⟨199746, by rfl⟩ : syracuseStep 2130629 = 399493) (by norm_num)
theorem B7193285 : Blo 1419529 7193285 := bbase (se 4 (by rfl) ⟨674370, by rfl⟩ : syracuseStep 7193285 = 1348741) (by norm_num)
theorem B1598161 : Blo 1419529 1598161 := bbase (se 2 (by rfl) ⟨599310, by rfl⟩ : syracuseStep 1598161 = 1198621) (by norm_num)
theorem B8086229 : Blo 1419529 8086229 := bbase (se 7 (by rfl) ⟨94760, by rfl⟩ : syracuseStep 8086229 = 189521) (by norm_num)
theorem B1516249 : Blo 1419529 1516249 := bbase (se 2 (by rfl) ⟨568593, by rfl⟩ : syracuseStep 1516249 = 1137187) (by norm_num)
theorem B2130653 : Blo 1419529 2130653 := bbase (se 3 (by rfl) ⟨399497, by rfl⟩ : syracuseStep 2130653 = 798995) (by norm_num)
theorem B3195629 : Blo 1419529 3195629 := bbase (se 3 (by rfl) ⟨599180, by rfl⟩ : syracuseStep 3195629 = 1198361) (by norm_num)
theorem B2130677 : Blo 1419529 2130677 := bbase (se 5 (by rfl) ⟨99875, by rfl⟩ : syracuseStep 2130677 = 199751) (by norm_num)
theorem B1598197 : Blo 1419529 1598197 := bbase (se 5 (by rfl) ⟨74915, by rfl⟩ : syracuseStep 1598197 = 149831) (by norm_num)
theorem B2695933 : Blo 1419529 2695933 := bbase (se 3 (by rfl) ⟨505487, by rfl⟩ : syracuseStep 2695933 = 1010975) (by norm_num)
theorem B4793093 : Blo 1419529 4793093 := bbase (se 4 (by rfl) ⟨449352, by rfl⟩ : syracuseStep 4793093 = 898705) (by norm_num)
theorem B2130701 : Blo 1419529 2130701 := bbase (se 3 (by rfl) ⟨399506, by rfl⟩ : syracuseStep 2130701 = 799013) (by norm_num)
theorem B1598233 : Blo 1419529 1598233 := bbase (se 2 (by rfl) ⟨599337, by rfl⟩ : syracuseStep 1598233 = 1198675) (by norm_num)
theorem B2130725 : Blo 1419529 2130725 := bbase (se 4 (by rfl) ⟨199755, by rfl⟩ : syracuseStep 2130725 = 399511) (by norm_num)
theorem B3195701 : Blo 1419529 3195701 := bbase (se 5 (by rfl) ⟨149798, by rfl⟩ : syracuseStep 3195701 = 299597) (by norm_num)
theorem B10789685 : Blo 1419529 10789685 := bbase (se 5 (by rfl) ⟨505766, by rfl⟩ : syracuseStep 10789685 = 1011533) (by norm_num)
theorem B2130749 : Blo 1419529 2130749 := bbase (se 3 (by rfl) ⟨399515, by rfl⟩ : syracuseStep 2130749 = 799031) (by norm_num)
theorem B1598269 : Blo 1419529 1598269 := bbase (se 3 (by rfl) ⟨299675, by rfl⟩ : syracuseStep 1598269 = 599351) (by norm_num)
theorem B6824773 : Blo 1419529 6824773 := bbase (se 4 (by rfl) ⟨639822, by rfl⟩ : syracuseStep 6824773 = 1279645) (by norm_num)
theorem B2130773 : Blo 1419529 2130773 := bbase (se 9 (by rfl) ⟨6242, by rfl⟩ : syracuseStep 2130773 = 12485) (by norm_num)
theorem B3597149 : Blo 1419529 3597149 := bbase (se 3 (by rfl) ⟨674465, by rfl⟩ : syracuseStep 3597149 = 1348931) (by norm_num)
theorem B1598305 : Blo 1419529 1598305 := bbase (se 2 (by rfl) ⟨599364, by rfl⟩ : syracuseStep 1598305 = 1198729) (by norm_num)
theorem B2130797 : Blo 1419529 2130797 := bbase (se 3 (by rfl) ⟨399524, by rfl⟩ : syracuseStep 2130797 = 799049) (by norm_num)
theorem B3195773 : Blo 1419529 3195773 := bbase (se 3 (by rfl) ⟨599207, by rfl⟩ : syracuseStep 3195773 = 1198415) (by norm_num)
theorem B2130821 : Blo 1419529 2130821 := bbase (se 4 (by rfl) ⟨199764, by rfl⟩ : syracuseStep 2130821 = 399529) (by norm_num)
theorem B1598341 : Blo 1419529 1598341 := bbase (se 4 (by rfl) ⟨149844, by rfl⟩ : syracuseStep 1598341 = 299689) (by norm_num)
theorem B2130845 : Blo 1419529 2130845 := bbase (se 3 (by rfl) ⟨399533, by rfl⟩ : syracuseStep 2130845 = 799067) (by norm_num)
theorem B1598377 : Blo 1419529 1598377 := bbase (se 2 (by rfl) ⟨599391, by rfl⟩ : syracuseStep 1598377 = 1198783) (by norm_num)
theorem B2130869 : Blo 1419529 2130869 := bbase (se 5 (by rfl) ⟨99884, by rfl⟩ : syracuseStep 2130869 = 199769) (by norm_num)
theorem B3195845 : Blo 1419529 3195845 := bbase (se 4 (by rfl) ⟨299610, by rfl⟩ : syracuseStep 3195845 = 599221) (by norm_num)
theorem B2130893 : Blo 1419529 2130893 := bbase (se 3 (by rfl) ⟨399542, by rfl⟩ : syracuseStep 2130893 = 799085) (by norm_num)
theorem B1598413 : Blo 1419529 1598413 := bbase (se 3 (by rfl) ⟨299702, by rfl⟩ : syracuseStep 1598413 = 599405) (by norm_num)
theorem B2130917 : Blo 1419529 2130917 := bbase (se 4 (by rfl) ⟨199773, by rfl⟩ : syracuseStep 2130917 = 399547) (by norm_num)
theorem B1598449 : Blo 1419529 1598449 := bbase (se 2 (by rfl) ⟨599418, by rfl⟩ : syracuseStep 1598449 = 1198837) (by norm_num)
theorem B2130941 : Blo 1419529 2130941 := bbase (se 3 (by rfl) ⟨399551, by rfl⟩ : syracuseStep 2130941 = 799103) (by norm_num)
theorem B3195917 : Blo 1419529 3195917 := bbase (se 3 (by rfl) ⟨599234, by rfl⟩ : syracuseStep 3195917 = 1198469) (by norm_num)
theorem B2130965 : Blo 1419529 2130965 := bbase (se 6 (by rfl) ⟨49944, by rfl⟩ : syracuseStep 2130965 = 99889) (by norm_num)
theorem B1598485 : Blo 1419529 1598485 := bbase (se 6 (by rfl) ⟨37464, by rfl⟩ : syracuseStep 1598485 = 74929) (by norm_num)
theorem B2696237 : Blo 1419529 2696237 := bbase (se 3 (by rfl) ⟨505544, by rfl⟩ : syracuseStep 2696237 = 1011089) (by norm_num)
theorem B2130989 : Blo 1419529 2130989 := bbase (se 3 (by rfl) ⟨399560, by rfl⟩ : syracuseStep 2130989 = 799121) (by norm_num)
theorem B1598521 : Blo 1419529 1598521 := bbase (se 2 (by rfl) ⟨599445, by rfl⟩ : syracuseStep 1598521 = 1198891) (by norm_num)
theorem B2131013 : Blo 1419529 2131013 := bbase (se 4 (by rfl) ⟨199782, by rfl⟩ : syracuseStep 2131013 = 399565) (by norm_num)
theorem B3195989 : Blo 1419529 3195989 := bbase (se 8 (by rfl) ⟨18726, by rfl⟩ : syracuseStep 3195989 = 37453) (by norm_num)
theorem B2131037 : Blo 1419529 2131037 := bbase (se 3 (by rfl) ⟨399569, by rfl⟩ : syracuseStep 2131037 = 799139) (by norm_num)
theorem B1598557 : Blo 1419529 1598557 := bbase (se 3 (by rfl) ⟨299729, by rfl⟩ : syracuseStep 1598557 = 599459) (by norm_num)
theorem B2131061 : Blo 1419529 2131061 := bbase (se 5 (by rfl) ⟨99893, by rfl⟩ : syracuseStep 2131061 = 199787) (by norm_num)
theorem B1598593 : Blo 1419529 1598593 := bbase (se 2 (by rfl) ⟨599472, by rfl⟩ : syracuseStep 1598593 = 1198945) (by norm_num)
theorem B1516681 : Blo 1419529 1516681 := bbase (se 2 (by rfl) ⟨568755, by rfl⟩ : syracuseStep 1516681 = 1137511) (by norm_num)
theorem B2131085 : Blo 1419529 2131085 := bbase (se 3 (by rfl) ⟨399578, by rfl⟩ : syracuseStep 2131085 = 799157) (by norm_num)
theorem B6915221 : Blo 1419529 6915221 := bbase (se 6 (by rfl) ⟨162075, by rfl⟩ : syracuseStep 6915221 = 324151) (by norm_num)
theorem B3196061 : Blo 1419529 3196061 := bbase (se 3 (by rfl) ⟨599261, by rfl⟩ : syracuseStep 3196061 = 1198523) (by norm_num)
theorem B2131109 : Blo 1419529 2131109 := bbase (se 4 (by rfl) ⟨199791, by rfl⟩ : syracuseStep 2131109 = 399583) (by norm_num)
theorem B1598629 : Blo 1419529 1598629 := bbase (se 4 (by rfl) ⟨149871, by rfl⟩ : syracuseStep 1598629 = 299743) (by norm_num)
theorem B4793525 : Blo 1419529 4793525 := bbase (se 5 (by rfl) ⟨224696, by rfl⟩ : syracuseStep 4793525 = 449393) (by norm_num)
theorem B3597493 : Blo 1419529 3597493 := bbase (se 5 (by rfl) ⟨168632, by rfl⟩ : syracuseStep 3597493 = 337265) (by norm_num)
theorem B2131133 : Blo 1419529 2131133 := bbase (se 3 (by rfl) ⟨399587, by rfl⟩ : syracuseStep 2131133 = 799175) (by norm_num)
theorem B1598665 : Blo 1419529 1598665 := bbase (se 2 (by rfl) ⟨599499, by rfl⟩ : syracuseStep 1598665 = 1198999) (by norm_num)
theorem B1516753 : Blo 1419529 1516753 := bbase (se 2 (by rfl) ⟨568782, by rfl⟩ : syracuseStep 1516753 = 1137565) (by norm_num)
theorem B10781909 : Blo 1419529 10781909 := bbase (se 7 (by rfl) ⟨126350, by rfl⟩ : syracuseStep 10781909 = 252701) (by norm_num)
theorem B2131157 : Blo 1419529 2131157 := bbase (se 7 (by rfl) ⟨24974, by rfl⟩ : syracuseStep 2131157 = 49949) (by norm_num)
theorem B3196133 : Blo 1419529 3196133 := bbase (se 4 (by rfl) ⟨299637, by rfl⟩ : syracuseStep 3196133 = 599275) (by norm_num)
theorem B2131181 : Blo 1419529 2131181 := bbase (se 3 (by rfl) ⟨399596, by rfl⟩ : syracuseStep 2131181 = 799193) (by norm_num)
theorem B1598701 : Blo 1419529 1598701 := bbase (se 3 (by rfl) ⟨299756, by rfl⟩ : syracuseStep 1598701 = 599513) (by norm_num)
theorem B2131205 : Blo 1419529 2131205 := bbase (se 4 (by rfl) ⟨199800, by rfl⟩ : syracuseStep 2131205 = 399601) (by norm_num)
theorem B6071557 : Blo 1419529 6071557 := bbase (se 4 (by rfl) ⟨569208, by rfl⟩ : syracuseStep 6071557 = 1138417) (by norm_num)
theorem B1598737 : Blo 1419529 1598737 := bbase (se 2 (by rfl) ⟨599526, by rfl⟩ : syracuseStep 1598737 = 1199053) (by norm_num)
theorem B2131229 : Blo 1419529 2131229 := bbase (se 3 (by rfl) ⟨399605, by rfl⟩ : syracuseStep 2131229 = 799211) (by norm_num)
theorem B3597605 : Blo 1419529 3597605 := bbase (se 4 (by rfl) ⟨337275, by rfl⟩ : syracuseStep 3597605 = 674551) (by norm_num)
theorem B3196205 : Blo 1419529 3196205 := bbase (se 3 (by rfl) ⟨599288, by rfl⟩ : syracuseStep 3196205 = 1198577) (by norm_num)
theorem B2131253 : Blo 1419529 2131253 := bbase (se 5 (by rfl) ⟨99902, by rfl⟩ : syracuseStep 2131253 = 199805) (by norm_num)
theorem B1598773 : Blo 1419529 1598773 := bbase (se 5 (by rfl) ⟨74942, by rfl⟩ : syracuseStep 1598773 = 149885) (by norm_num)
theorem B2131277 : Blo 1419529 2131277 := bbase (se 3 (by rfl) ⟨399614, by rfl⟩ : syracuseStep 2131277 = 799229) (by norm_num)
theorem B1598809 : Blo 1419529 1598809 := bbase (se 2 (by rfl) ⟨599553, by rfl⟩ : syracuseStep 1598809 = 1199107) (by norm_num)
theorem B2131301 : Blo 1419529 2131301 := bbase (se 4 (by rfl) ⟨199809, by rfl⟩ : syracuseStep 2131301 = 399619) (by norm_num)
theorem B3196277 : Blo 1419529 3196277 := bbase (se 5 (by rfl) ⟨149825, by rfl⟩ : syracuseStep 3196277 = 299651) (by norm_num)
theorem B2131325 : Blo 1419529 2131325 := bbase (se 3 (by rfl) ⟨399623, by rfl⟩ : syracuseStep 2131325 = 799247) (by norm_num)
theorem B1598845 : Blo 1419529 1598845 := bbase (se 3 (by rfl) ⟨299783, by rfl⟩ : syracuseStep 1598845 = 599567) (by norm_num)
theorem B2131349 : Blo 1419529 2131349 := bbase (se 6 (by rfl) ⟨49953, by rfl⟩ : syracuseStep 2131349 = 99907) (by norm_num)
theorem B1598881 : Blo 1419529 1598881 := bbase (se 2 (by rfl) ⟨599580, by rfl⟩ : syracuseStep 1598881 = 1199161) (by norm_num)
theorem B2131373 : Blo 1419529 2131373 := bbase (se 3 (by rfl) ⟨399632, by rfl⟩ : syracuseStep 2131373 = 799265) (by norm_num)
theorem B9102773 : Blo 1419529 9102773 := bbase (se 5 (by rfl) ⟨426692, by rfl⟩ : syracuseStep 9102773 = 853385) (by norm_num)
theorem B3196349 : Blo 1419529 3196349 := bbase (se 3 (by rfl) ⟨599315, by rfl⟩ : syracuseStep 3196349 = 1198631) (by norm_num)
theorem B2131397 : Blo 1419529 2131397 := bbase (se 4 (by rfl) ⟨199818, by rfl⟩ : syracuseStep 2131397 = 399637) (by norm_num)
theorem B1598917 : Blo 1419529 1598917 := bbase (se 4 (by rfl) ⟨149898, by rfl⟩ : syracuseStep 1598917 = 299797) (by norm_num)
theorem B2131421 : Blo 1419529 2131421 := bbase (se 3 (by rfl) ⟨399641, by rfl⟩ : syracuseStep 2131421 = 799283) (by norm_num)
theorem B3597797 : Blo 1419529 3597797 := bbase (se 4 (by rfl) ⟨337293, by rfl⟩ : syracuseStep 3597797 = 674587) (by norm_num)
theorem B1598953 : Blo 1419529 1598953 := bbase (se 2 (by rfl) ⟨599607, by rfl⟩ : syracuseStep 1598953 = 1199215) (by norm_num)
theorem B2131445 : Blo 1419529 2131445 := bbase (se 5 (by rfl) ⟨99911, by rfl⟩ : syracuseStep 2131445 = 199823) (by norm_num)
theorem B3196421 : Blo 1419529 3196421 := bbase (se 4 (by rfl) ⟨299664, by rfl⟩ : syracuseStep 3196421 = 599329) (by norm_num)
theorem B2131469 : Blo 1419529 2131469 := bbase (se 3 (by rfl) ⟨399650, by rfl⟩ : syracuseStep 2131469 = 799301) (by norm_num)
theorem B1598989 : Blo 1419529 1598989 := bbase (se 3 (by rfl) ⟨299810, by rfl⟩ : syracuseStep 1598989 = 599621) (by norm_num)
theorem B2131493 : Blo 1419529 2131493 := bbase (se 4 (by rfl) ⟨199827, by rfl⟩ : syracuseStep 2131493 = 399655) (by norm_num)
theorem B1599025 : Blo 1419529 1599025 := bbase (se 2 (by rfl) ⟨599634, by rfl⟩ : syracuseStep 1599025 = 1199269) (by norm_num)
theorem B2131517 : Blo 1419529 2131517 := bbase (se 3 (by rfl) ⟨399659, by rfl⟩ : syracuseStep 2131517 = 799319) (by norm_num)
theorem B1517125 : Blo 1419529 1517125 := bbase (se 4 (by rfl) ⟨142230, by rfl⟩ : syracuseStep 1517125 = 284461) (by norm_num)
theorem B3196493 : Blo 1419529 3196493 := bbase (se 3 (by rfl) ⟨599342, by rfl⟩ : syracuseStep 3196493 = 1198685) (by norm_num)
theorem B2131541 : Blo 1419529 2131541 := bbase (se 8 (by rfl) ⟨12489, by rfl⟩ : syracuseStep 2131541 = 24979) (by norm_num)
theorem B1599061 : Blo 1419529 1599061 := bbase (se 8 (by rfl) ⟨9369, by rfl⟩ : syracuseStep 1599061 = 18739) (by norm_num)
theorem B4793957 : Blo 1419529 4793957 := bbase (se 4 (by rfl) ⟨449433, by rfl⟩ : syracuseStep 4793957 = 898867) (by norm_num)
theorem B2131565 : Blo 1419529 2131565 := bbase (se 3 (by rfl) ⟨399668, by rfl⟩ : syracuseStep 2131565 = 799337) (by norm_num)
theorem B1599097 : Blo 1419529 1599097 := bbase (se 2 (by rfl) ⟨599661, by rfl⟩ : syracuseStep 1599097 = 1199323) (by norm_num)
theorem B2131589 : Blo 1419529 2131589 := bbase (se 4 (by rfl) ⟨199836, by rfl⟩ : syracuseStep 2131589 = 399673) (by norm_num)
theorem B3196565 : Blo 1419529 3196565 := bbase (se 6 (by rfl) ⟨74919, by rfl⟩ : syracuseStep 3196565 = 149839) (by norm_num)
theorem B2131613 : Blo 1419529 2131613 := bbase (se 3 (by rfl) ⟨399677, by rfl⟩ : syracuseStep 2131613 = 799355) (by norm_num)
theorem B1599133 : Blo 1419529 1599133 := bbase (se 3 (by rfl) ⟨299837, by rfl⟩ : syracuseStep 1599133 = 599675) (by norm_num)
theorem B2131637 : Blo 1419529 2131637 := bbase (se 5 (by rfl) ⟨99920, by rfl⟩ : syracuseStep 2131637 = 199841) (by norm_num)
theorem B1599169 : Blo 1419529 1599169 := bbase (se 2 (by rfl) ⟨599688, by rfl⟩ : syracuseStep 1599169 = 1199377) (by norm_num)
theorem B2131661 : Blo 1419529 2131661 := bbase (se 3 (by rfl) ⟨399686, by rfl⟩ : syracuseStep 2131661 = 799373) (by norm_num)
theorem B24610517 : Blo 1419529 24610517 := bbase (se 7 (by rfl) ⟨288404, by rfl⟩ : syracuseStep 24610517 = 576809) (by norm_num)
theorem B3196637 : Blo 1419529 3196637 := bbase (se 3 (by rfl) ⟨599369, by rfl⟩ : syracuseStep 3196637 = 1198739) (by norm_num)
theorem B2131685 : Blo 1419529 2131685 := bbase (se 4 (by rfl) ⟨199845, by rfl⟩ : syracuseStep 2131685 = 399691) (by norm_num)
theorem B1599205 : Blo 1419529 1599205 := bbase (se 4 (by rfl) ⟨149925, by rfl⟩ : syracuseStep 1599205 = 299851) (by norm_num)
theorem B2131709 : Blo 1419529 2131709 := bbase (se 3 (by rfl) ⟨399695, by rfl⟩ : syracuseStep 2131709 = 799391) (by norm_num)
theorem B4859669 : Blo 1419529 4859669 := bbase (se 6 (by rfl) ⟨113898, by rfl⟩ : syracuseStep 4859669 = 227797) (by norm_num)
theorem B2131733 : Blo 1419529 2131733 := bbase (se 6 (by rfl) ⟨49962, by rfl⟩ : syracuseStep 2131733 = 99925) (by norm_num)
theorem B2696989 : Blo 1419529 2696989 := bbase (se 3 (by rfl) ⟨505685, by rfl⟩ : syracuseStep 2696989 = 1011371) (by norm_num)
theorem B3196709 : Blo 1419529 3196709 := bbase (se 4 (by rfl) ⟨299691, by rfl⟩ : syracuseStep 3196709 = 599383) (by norm_num)
theorem B2131757 : Blo 1419529 2131757 := bbase (se 3 (by rfl) ⟨399704, by rfl⟩ : syracuseStep 2131757 = 799409) (by norm_num)
theorem B3598141 : Blo 1419529 3598141 := bbase (se 3 (by rfl) ⟨674651, by rfl⟩ : syracuseStep 3598141 = 1349303) (by norm_num)
theorem B2131781 : Blo 1419529 2131781 := bbase (se 4 (by rfl) ⟨199854, by rfl⟩ : syracuseStep 2131781 = 399709) (by norm_num)
theorem B2131805 : Blo 1419529 2131805 := bbase (se 3 (by rfl) ⟨399713, by rfl⟩ : syracuseStep 2131805 = 799427) (by norm_num)
theorem B1664869 : Blo 1419529 1664869 := bbase (se 4 (by rfl) ⟨156081, by rfl⟩ : syracuseStep 1664869 = 312163) (by norm_num)
theorem B3196781 : Blo 1419529 3196781 := bbase (se 3 (by rfl) ⟨599396, by rfl⟩ : syracuseStep 3196781 = 1198793) (by norm_num)
theorem B2131829 : Blo 1419529 2131829 := bbase (se 5 (by rfl) ⟨99929, by rfl⟩ : syracuseStep 2131829 = 199859) (by norm_num)
theorem B2131853 : Blo 1419529 2131853 := bbase (se 3 (by rfl) ⟨399722, by rfl⟩ : syracuseStep 2131853 = 799445) (by norm_num)
theorem B5392277 : Blo 1419529 5392277 := bbase (se 6 (by rfl) ⟨126381, by rfl⟩ : syracuseStep 5392277 = 252763) (by norm_num)
theorem B2131877 : Blo 1419529 2131877 := bbase (se 4 (by rfl) ⟨199863, by rfl⟩ : syracuseStep 2131877 = 399727) (by norm_num)
theorem B2697133 : Blo 1419529 2697133 := bbase (se 3 (by rfl) ⟨505712, by rfl⟩ : syracuseStep 2697133 = 1011425) (by norm_num)
theorem B8636341 : Blo 1419529 8636341 := bbase (se 5 (by rfl) ⟨404828, by rfl⟩ : syracuseStep 8636341 = 809657) (by norm_num)
theorem B3196853 : Blo 1419529 3196853 := bbase (se 5 (by rfl) ⟨149852, by rfl⟩ : syracuseStep 3196853 = 299705) (by norm_num)
theorem B1517501 : Blo 1419529 1517501 := bbase (se 3 (by rfl) ⟨284531, by rfl⟩ : syracuseStep 1517501 = 569063) (by norm_num)
theorem B2131901 : Blo 1419529 2131901 := bbase (se 3 (by rfl) ⟨399731, by rfl⟩ : syracuseStep 2131901 = 799463) (by norm_num)
theorem B7194581 : Blo 1419529 7194581 := bbase (se 7 (by rfl) ⟨84311, by rfl⟩ : syracuseStep 7194581 = 168623) (by norm_num)
theorem B2131925 : Blo 1419529 2131925 := bbase (se 7 (by rfl) ⟨24983, by rfl⟩ : syracuseStep 2131925 = 49967) (by norm_num)
theorem B2131949 : Blo 1419529 2131949 := bbase (se 3 (by rfl) ⟨399740, by rfl⟩ : syracuseStep 2131949 = 799481) (by norm_num)
theorem B3196925 : Blo 1419529 3196925 := bbase (se 3 (by rfl) ⟨599423, by rfl⟩ : syracuseStep 3196925 = 1198847) (by norm_num)
theorem B1517573 : Blo 1419529 1517573 := bbase (se 4 (by rfl) ⟨142272, by rfl⟩ : syracuseStep 1517573 = 284545) (by norm_num)
theorem B2131973 : Blo 1419529 2131973 := bbase (se 4 (by rfl) ⟨199872, by rfl⟩ : syracuseStep 2131973 = 399745) (by norm_num)
theorem B4794389 : Blo 1419529 4794389 := bbase (se 6 (by rfl) ⟨112368, by rfl⟩ : syracuseStep 4794389 = 224737) (by norm_num)
theorem B2131997 : Blo 1419529 2131997 := bbase (se 3 (by rfl) ⟨399749, by rfl⟩ : syracuseStep 2131997 = 799499) (by norm_num)
theorem B2132021 : Blo 1419529 2132021 := bbase (se 5 (by rfl) ⟨99938, by rfl⟩ : syracuseStep 2132021 = 199877) (by norm_num)
theorem B3196997 : Blo 1419529 3196997 := bbase (se 4 (by rfl) ⟨299718, by rfl⟩ : syracuseStep 3196997 = 599437) (by norm_num)
theorem B2697293 : Blo 1419529 2697293 := bbase (se 3 (by rfl) ⟨505742, by rfl⟩ : syracuseStep 2697293 = 1011485) (by norm_num)
theorem B2132045 : Blo 1419529 2132045 := bbase (se 3 (by rfl) ⟨399758, by rfl⟩ : syracuseStep 2132045 = 799517) (by norm_num)
theorem B7784533 : Blo 1419529 7784533 := bbase (se 8 (by rfl) ⟨45612, by rfl⟩ : syracuseStep 7784533 = 91225) (by norm_num)
theorem B2132069 : Blo 1419529 2132069 := bbase (se 4 (by rfl) ⟨199881, by rfl⟩ : syracuseStep 2132069 = 399763) (by norm_num)
theorem B2132093 : Blo 1419529 2132093 := bbase (se 3 (by rfl) ⟨399767, by rfl⟩ : syracuseStep 2132093 = 799535) (by norm_num)
theorem B3197069 : Blo 1419529 3197069 := bbase (se 3 (by rfl) ⟨599450, by rfl⟩ : syracuseStep 3197069 = 1198901) (by norm_num)
theorem B2132117 : Blo 1419529 2132117 := bbase (se 6 (by rfl) ⟨49971, by rfl⟩ : syracuseStep 2132117 = 99943) (by norm_num)
theorem B4548773 : Blo 1419529 4548773 := bbase (se 4 (by rfl) ⟨426447, by rfl⟩ : syracuseStep 4548773 = 852895) (by norm_num)
theorem B2132141 : Blo 1419529 2132141 := bbase (se 3 (by rfl) ⟨399776, by rfl⟩ : syracuseStep 2132141 = 799553) (by norm_num)
theorem B5392565 : Blo 1419529 5392565 := bbase (se 5 (by rfl) ⟨252776, by rfl⟩ : syracuseStep 5392565 = 505553) (by norm_num)
theorem B1517761 : Blo 1419529 1517761 := bbase (se 2 (by rfl) ⟨569160, by rfl⟩ : syracuseStep 1517761 = 1138321) (by norm_num)
theorem B2132165 : Blo 1419529 2132165 := bbase (se 4 (by rfl) ⟨199890, by rfl⟩ : syracuseStep 2132165 = 399781) (by norm_num)
theorem B3033301 : Blo 1419529 3033301 := bbase (se 7 (by rfl) ⟨35546, by rfl⟩ : syracuseStep 3033301 = 71093) (by norm_num)
theorem B3197141 : Blo 1419529 3197141 := bbase (se 7 (by rfl) ⟨37466, by rfl⟩ : syracuseStep 3197141 = 74933) (by norm_num)
theorem B2697437 : Blo 1419529 2697437 := bbase (se 3 (by rfl) ⟨505769, by rfl⟩ : syracuseStep 2697437 = 1011539) (by norm_num)
theorem B2132189 : Blo 1419529 2132189 := bbase (se 3 (by rfl) ⟨399785, by rfl⟩ : syracuseStep 2132189 = 799571) (by norm_num)
theorem B1730797 : Blo 1419529 1730797 := bbase (se 3 (by rfl) ⟨324524, by rfl⟩ : syracuseStep 1730797 = 649049) (by norm_num)
theorem B11520245 : Blo 1419529 11520245 := bbase (se 5 (by rfl) ⟨540011, by rfl⟩ : syracuseStep 11520245 = 1080023) (by norm_num)
theorem B2132213 : Blo 1419529 2132213 := bbase (se 5 (by rfl) ⟨99947, by rfl⟩ : syracuseStep 2132213 = 199895) (by norm_num)
theorem B2132237 : Blo 1419529 2132237 := bbase (se 3 (by rfl) ⟨399794, by rfl⟩ : syracuseStep 2132237 = 799589) (by norm_num)
theorem B3197213 : Blo 1419529 3197213 := bbase (se 3 (by rfl) ⟨599477, by rfl⟩ : syracuseStep 3197213 = 1198955) (by norm_num)
theorem B2132261 : Blo 1419529 2132261 := bbase (se 4 (by rfl) ⟨199899, by rfl⟩ : syracuseStep 2132261 = 399799) (by norm_num)
theorem B2132285 : Blo 1419529 2132285 := bbase (se 3 (by rfl) ⟨399803, by rfl⟩ : syracuseStep 2132285 = 799607) (by norm_num)
theorem B3197285 : Blo 1419529 3197285 := bbase (se 4 (by rfl) ⟨299745, by rfl⟩ : syracuseStep 3197285 = 599491) (by norm_num)
theorem B7186805 : Blo 1419529 7186805 := bbase (se 5 (by rfl) ⟨336881, by rfl⟩ : syracuseStep 7186805 = 673763) (by norm_num)
theorem B5835125 : Blo 1419529 5835125 := bbase (se 5 (by rfl) ⟨273521, by rfl⟩ : syracuseStep 5835125 = 547043) (by norm_num)
theorem B1517945 : Blo 1419529 1517945 := bbase (se 2 (by rfl) ⟨569229, by rfl⟩ : syracuseStep 1517945 = 1138459) (by norm_num)
theorem B1919381 : Blo 1419529 1919381 := bbase (se 6 (by rfl) ⟨44985, by rfl⟩ : syracuseStep 1919381 = 89971) (by norm_num)
theorem B1706405 : Blo 1419529 1706405 := bbase (se 4 (by rfl) ⟨159975, by rfl⟩ : syracuseStep 1706405 = 319951) (by norm_num)
theorem B3197357 : Blo 1419529 3197357 := bbase (se 3 (by rfl) ⟨599504, by rfl⟩ : syracuseStep 3197357 = 1199009) (by norm_num)
theorem B4794821 : Blo 1419529 4794821 := bbase (se 4 (by rfl) ⟨449514, by rfl⟩ : syracuseStep 4794821 = 899029) (by norm_num)
theorem B3238373 : Blo 1419529 3238373 := bbase (se 4 (by rfl) ⟨303597, by rfl⟩ : syracuseStep 3238373 = 607195) (by norm_num)
theorem B3197429 : Blo 1419529 3197429 := bbase (se 5 (by rfl) ⟨149879, by rfl⟩ : syracuseStep 3197429 = 299759) (by norm_num)
theorem B2697725 : Blo 1419529 2697725 := bbase (se 3 (by rfl) ⟨505823, by rfl⟩ : syracuseStep 2697725 = 1011647) (by norm_num)
theorem B1706501 : Blo 1419529 1706501 := bbase (se 4 (by rfl) ⟨159984, by rfl⟩ : syracuseStep 1706501 = 319969) (by norm_num)
theorem B1706521 : Blo 1419529 1706521 := bbase (se 2 (by rfl) ⟨639945, by rfl⟩ : syracuseStep 1706521 = 1279891) (by norm_num)
theorem B1919533 : Blo 1419529 1919533 := bbase (se 3 (by rfl) ⟨359912, by rfl⟩ : syracuseStep 1919533 = 719825) (by norm_num)
theorem B3197501 : Blo 1419529 3197501 := bbase (se 3 (by rfl) ⟨599531, by rfl⟩ : syracuseStep 3197501 = 1199063) (by norm_num)
theorem B1796681 : Blo 1419529 1796681 := bbase (se 2 (by rfl) ⟨673755, by rfl⟩ : syracuseStep 1796681 = 1347511) (by norm_num)
theorem B6064757 : Blo 1419529 6064757 := bbase (se 5 (by rfl) ⟨284285, by rfl⟩ : syracuseStep 6064757 = 568571) (by norm_num)
theorem B1796737 : Blo 1419529 1796737 := bbase (se 2 (by rfl) ⟨673776, by rfl⟩ : syracuseStep 1796737 = 1347553) (by norm_num)
theorem B3197573 : Blo 1419529 3197573 := bbase (se 4 (by rfl) ⟨299772, by rfl⟩ : syracuseStep 3197573 = 599545) (by norm_num)
theorem B2697877 : Blo 1419529 2697877 := bbase (se 6 (by rfl) ⟨63231, by rfl⟩ : syracuseStep 2697877 = 126463) (by norm_num)
theorem B1706665 : Blo 1419529 1706665 := bbase (se 2 (by rfl) ⟨639999, by rfl⟩ : syracuseStep 1706665 = 1279999) (by norm_num)
theorem B3197645 : Blo 1419529 3197645 := bbase (se 3 (by rfl) ⟨599558, by rfl⟩ : syracuseStep 3197645 = 1199117) (by norm_num)
theorem B12143317 : Blo 1419529 12143317 := bbase (se 7 (by rfl) ⟨142304, by rfl⟩ : syracuseStep 12143317 = 284609) (by norm_num)
theorem B1796833 : Blo 1419529 1796833 := bbase (se 2 (by rfl) ⟨673812, by rfl⟩ : syracuseStep 1796833 = 1347625) (by norm_num)
theorem B3197717 : Blo 1419529 3197717 := bbase (se 6 (by rfl) ⟨74946, by rfl⟩ : syracuseStep 3197717 = 149893) (by norm_num)
theorem B2558765 : Blo 1419529 2558765 := bbase (se 3 (by rfl) ⟨479768, by rfl⟩ : syracuseStep 2558765 = 959537) (by norm_num)
theorem B3197789 : Blo 1419529 3197789 := bbase (se 3 (by rfl) ⟨599585, by rfl⟩ : syracuseStep 3197789 = 1199171) (by norm_num)
theorem B8088437 : Blo 1419529 8088437 := bbase (se 5 (by rfl) ⟨379145, by rfl⟩ : syracuseStep 8088437 = 758291) (by norm_num)
theorem B4795253 : Blo 1419529 4795253 := bbase (se 5 (by rfl) ⟨224777, by rfl⟩ : syracuseStep 4795253 = 449555) (by norm_num)
theorem B1797005 : Blo 1419529 1797005 := bbase (se 3 (by rfl) ⟨336938, by rfl⟩ : syracuseStep 1797005 = 673877) (by norm_num)
theorem B3197861 : Blo 1419529 3197861 := bbase (se 4 (by rfl) ⟨299799, by rfl⟩ : syracuseStep 3197861 = 599599) (by norm_num)
theorem B1846189 : Blo 1419529 1846189 := bbase (se 3 (by rfl) ⟨346160, by rfl⟩ : syracuseStep 1846189 = 692321) (by norm_num)
theorem B12127157 : Blo 1419529 12127157 := bbase (se 5 (by rfl) ⟨568460, by rfl⟩ : syracuseStep 12127157 = 1136921) (by norm_num)
theorem B1797061 : Blo 1419529 1797061 := bbase (se 4 (by rfl) ⟨168474, by rfl⟩ : syracuseStep 1797061 = 336949) (by norm_num)
theorem B2698181 : Blo 1419529 2698181 := bbase (se 4 (by rfl) ⟨252954, by rfl⟩ : syracuseStep 2698181 = 505909) (by norm_num)
theorem B3197933 : Blo 1419529 3197933 := bbase (se 3 (by rfl) ⟨599612, by rfl⟩ : syracuseStep 3197933 = 1199225) (by norm_num)
theorem B12471317 : Blo 1419529 12471317 := bbase (se 6 (by rfl) ⟨292296, by rfl⟩ : syracuseStep 12471317 = 584593) (by norm_num)
theorem B1797157 : Blo 1419529 1797157 := bbase (se 4 (by rfl) ⟨168483, by rfl⟩ : syracuseStep 1797157 = 336967) (by norm_num)
theorem B3198005 : Blo 1419529 3198005 := bbase (se 5 (by rfl) ⟨149906, by rfl⟩ : syracuseStep 3198005 = 299813) (by norm_num)
theorem B3034189 : Blo 1419529 3034189 := bbase (se 3 (by rfl) ⟨568910, by rfl⟩ : syracuseStep 3034189 = 1137821) (by norm_num)
theorem B3198077 : Blo 1419529 3198077 := bbase (se 3 (by rfl) ⟨599639, by rfl⟩ : syracuseStep 3198077 = 1199279) (by norm_num)
theorem B3198149 : Blo 1419529 3198149 := bbase (se 4 (by rfl) ⟨299826, by rfl⟩ : syracuseStep 3198149 = 599653) (by norm_num)
theorem B1797329 : Blo 1419529 1797329 := bbase (se 2 (by rfl) ⟨673998, by rfl⟩ : syracuseStep 1797329 = 1347997) (by norm_num)
theorem B7195877 : Blo 1419529 7195877 := bbase (se 4 (by rfl) ⟨674613, by rfl⟩ : syracuseStep 7195877 = 1349227) (by norm_num)
theorem B3411197 : Blo 1419529 3411197 := bbase (se 3 (by rfl) ⟨639599, by rfl⟩ : syracuseStep 3411197 = 1279199) (by norm_num)
theorem B1797385 : Blo 1419529 1797385 := bbase (se 2 (by rfl) ⟨674019, by rfl⟩ : syracuseStep 1797385 = 1348039) (by norm_num)
theorem B3198221 : Blo 1419529 3198221 := bbase (se 3 (by rfl) ⟨599666, by rfl⟩ : syracuseStep 3198221 = 1199333) (by norm_num)
theorem B4795685 : Blo 1419529 4795685 := bbase (se 4 (by rfl) ⟨449595, by rfl⟩ : syracuseStep 4795685 = 899191) (by norm_num)
theorem B5393749 : Blo 1419529 5393749 := bbase (se 11 (by rfl) ⟨3950, by rfl⟩ : syracuseStep 5393749 = 7901) (by norm_num)
theorem B3198293 : Blo 1419529 3198293 := bbase (se 11 (by rfl) ⟨2342, by rfl⟩ : syracuseStep 3198293 = 4685) (by norm_num)
theorem B1797481 : Blo 1419529 1797481 := bbase (se 2 (by rfl) ⟨674055, by rfl⟩ : syracuseStep 1797481 = 1348111) (by norm_num)
theorem B2395541 : Blo 1419529 2395541 := bbase (se 6 (by rfl) ⟨56145, by rfl⟩ : syracuseStep 2395541 = 112291) (by norm_num)
theorem B3198365 : Blo 1419529 3198365 := bbase (se 3 (by rfl) ⟨599693, by rfl⟩ : syracuseStep 3198365 = 1199387) (by norm_num)
theorem B44330453 : Blo 1419529 44330453 := bbase (se 7 (by rfl) ⟨519497, by rfl⟩ : syracuseStep 44330453 = 1038995) (by norm_num)
theorem B3198437 : Blo 1419529 3198437 := bbase (se 4 (by rfl) ⟨299853, by rfl⟩ : syracuseStep 3198437 = 599707) (by norm_num)
theorem B2395669 : Blo 1419529 2395669 := bbase (se 6 (by rfl) ⟨56148, by rfl⟩ : syracuseStep 2395669 = 112297) (by norm_num)
theorem B9096725 : Blo 1419529 9096725 := bbase (se 6 (by rfl) ⟨213204, by rfl⟩ : syracuseStep 9096725 = 426409) (by norm_num)
theorem B1797653 : Blo 1419529 1797653 := bbase (se 6 (by rfl) ⟨42132, by rfl⟩ : syracuseStep 1797653 = 84265) (by norm_num)
theorem B3034685 : Blo 1419529 3034685 := bbase (se 3 (by rfl) ⟨569003, by rfl⟩ : syracuseStep 3034685 = 1138007) (by norm_num)
theorem B3411533 : Blo 1419529 3411533 := bbase (se 3 (by rfl) ⟨639662, by rfl⟩ : syracuseStep 3411533 = 1279325) (by norm_num)
theorem B1797709 : Blo 1419529 1797709 := bbase (se 3 (by rfl) ⟨337070, by rfl⟩ : syracuseStep 1797709 = 674141) (by norm_num)
theorem B2395757 : Blo 1419529 2395757 := bbase (se 3 (by rfl) ⟨449204, by rfl⟩ : syracuseStep 2395757 = 898409) (by norm_num)
theorem B7188101 : Blo 1419529 7188101 := bbase (se 4 (by rfl) ⟨673884, by rfl⟩ : syracuseStep 7188101 = 1347769) (by norm_num)
theorem B5394053 : Blo 1419529 5394053 := bbase (se 4 (by rfl) ⟨505692, by rfl⟩ : syracuseStep 5394053 = 1011385) (by norm_num)
theorem B1797805 : Blo 1419529 1797805 := bbase (se 3 (by rfl) ⟨337088, by rfl⟩ : syracuseStep 1797805 = 674177) (by norm_num)
theorem B3239605 : Blo 1419529 3239605 := bbase (se 5 (by rfl) ⟨151856, by rfl⟩ : syracuseStep 3239605 = 303713) (by norm_num)
theorem B13643477 : Blo 1419529 13643477 := bbase (se 7 (by rfl) ⟨159884, by rfl⟩ : syracuseStep 13643477 = 319769) (by norm_num)
theorem B10235605 : Blo 1419529 10235605 := bbase (se 7 (by rfl) ⟨119948, by rfl⟩ : syracuseStep 10235605 = 239897) (by norm_num)
theorem B18706133 : Blo 1419529 18706133 := bbase (se 7 (by rfl) ⟨219212, by rfl⟩ : syracuseStep 18706133 = 438425) (by norm_num)
theorem B4796117 : Blo 1419529 4796117 := bbase (se 7 (by rfl) ⟨56204, by rfl⟩ : syracuseStep 4796117 = 112409) (by norm_num)
theorem B2559709 : Blo 1419529 2559709 := bbase (se 3 (by rfl) ⟨479945, by rfl⟩ : syracuseStep 2559709 = 959891) (by norm_num)
theorem B2395885 : Blo 1419529 2395885 := bbase (se 3 (by rfl) ⟨449228, by rfl⟩ : syracuseStep 2395885 = 898457) (by norm_num)
theorem B2395973 : Blo 1419529 2395973 := bbase (se 4 (by rfl) ⟨224622, by rfl⟩ : syracuseStep 2395973 = 449245) (by norm_num)
theorem B1797977 : Blo 1419529 1797977 := bbase (se 2 (by rfl) ⟨674241, by rfl⟩ : syracuseStep 1797977 = 1348483) (by norm_num)
theorem B2158429 : Blo 1419529 2158429 := bbase (se 3 (by rfl) ⟨404705, by rfl⟩ : syracuseStep 2158429 = 809411) (by norm_num)
theorem B1798033 : Blo 1419529 1798033 := bbase (se 2 (by rfl) ⟨674262, by rfl⟩ : syracuseStep 1798033 = 1348525) (by norm_num)
theorem B2879389 : Blo 1419529 2879389 := bbase (se 3 (by rfl) ⟨539885, by rfl⟩ : syracuseStep 2879389 = 1079771) (by norm_num)
theorem B2396101 : Blo 1419529 2396101 := bbase (se 4 (by rfl) ⟨224634, by rfl⟩ : syracuseStep 2396101 = 449269) (by norm_num)
theorem B3411925 : Blo 1419529 3411925 := bbase (se 7 (by rfl) ⟨39983, by rfl⟩ : syracuseStep 3411925 = 79967) (by norm_num)
theorem B1798129 : Blo 1419529 1798129 := bbase (se 2 (by rfl) ⟨674298, by rfl⟩ : syracuseStep 1798129 = 1348597) (by norm_num)
theorem B2396189 : Blo 1419529 2396189 := bbase (se 3 (by rfl) ⟨449285, by rfl⟩ : syracuseStep 2396189 = 898571) (by norm_num)
theorem B1642609 : Blo 1419529 1642609 := bbase (se 2 (by rfl) ⟨615978, by rfl⟩ : syracuseStep 1642609 = 1231957) (by norm_num)
theorem B3076213 : Blo 1419529 3076213 := bbase (se 5 (by rfl) ⟨144197, by rfl⟩ : syracuseStep 3076213 = 288395) (by norm_num)
theorem B4796549 : Blo 1419529 4796549 := bbase (se 4 (by rfl) ⟨449676, by rfl⟩ : syracuseStep 4796549 = 899353) (by norm_num)
theorem B2396317 : Blo 1419529 2396317 := bbase (se 3 (by rfl) ⟨449309, by rfl⟩ : syracuseStep 2396317 = 898619) (by norm_num)
theorem B1798301 : Blo 1419529 1798301 := bbase (se 3 (by rfl) ⟨337181, by rfl⟩ : syracuseStep 1798301 = 674363) (by norm_num)
theorem B5763269 : Blo 1419529 5763269 := bbase (se 4 (by rfl) ⟨540306, by rfl⟩ : syracuseStep 5763269 = 1080613) (by norm_num)
theorem B1798357 : Blo 1419529 1798357 := bbase (se 7 (by rfl) ⟨21074, by rfl⟩ : syracuseStep 1798357 = 42149) (by norm_num)
theorem B2396405 : Blo 1419529 2396405 := bbase (se 5 (by rfl) ⟨112331, by rfl⟩ : syracuseStep 2396405 = 224663) (by norm_num)
theorem B6828293 : Blo 1419529 6828293 := bbase (se 4 (by rfl) ⟨640152, by rfl⟩ : syracuseStep 6828293 = 1280305) (by norm_num)
theorem B1798453 : Blo 1419529 1798453 := bbase (se 5 (by rfl) ⟨84302, by rfl⟩ : syracuseStep 1798453 = 168605) (by norm_num)
theorem B1823033 : Blo 1419529 1823033 := bbase (se 2 (by rfl) ⟨683637, by rfl⟩ : syracuseStep 1823033 = 1367275) (by norm_num)
theorem B4043125 : Blo 1419529 4043125 := bbase (se 5 (by rfl) ⟨189521, by rfl⟩ : syracuseStep 4043125 = 379043) (by norm_num)
theorem B1732981 : Blo 1419529 1732981 := bbase (se 5 (by rfl) ⟨81233, by rfl⟩ : syracuseStep 1732981 = 162467) (by norm_num)
theorem B2396533 : Blo 1419529 2396533 := bbase (se 5 (by rfl) ⟨112337, by rfl⟩ : syracuseStep 2396533 = 224675) (by norm_num)
theorem B4551029 : Blo 1419529 4551029 := bbase (se 5 (by rfl) ⟨213329, by rfl⟩ : syracuseStep 4551029 = 426659) (by norm_num)
theorem B3035549 : Blo 1419529 3035549 := bbase (se 3 (by rfl) ⟨569165, by rfl⟩ : syracuseStep 3035549 = 1138331) (by norm_num)
theorem B2396621 : Blo 1419529 2396621 := bbase (se 3 (by rfl) ⟨449366, by rfl⟩ : syracuseStep 2396621 = 898733) (by norm_num)
theorem B15364565 : Blo 1419529 15364565 := bbase (se 7 (by rfl) ⟨180053, by rfl⟩ : syracuseStep 15364565 = 360107) (by norm_num)
theorem B1798625 : Blo 1419529 1798625 := bbase (se 2 (by rfl) ⟨674484, by rfl⟩ : syracuseStep 1798625 = 1348969) (by norm_num)
theorem B1798681 : Blo 1419529 1798681 := bbase (se 2 (by rfl) ⟨674505, by rfl⟩ : syracuseStep 1798681 = 1349011) (by norm_num)
theorem B3035693 : Blo 1419529 3035693 := bbase (se 3 (by rfl) ⟨569192, by rfl⟩ : syracuseStep 3035693 = 1138385) (by norm_num)
theorem B4796981 : Blo 1419529 4796981 := bbase (se 5 (by rfl) ⟨224858, by rfl⟩ : syracuseStep 4796981 = 449717) (by norm_num)
theorem B2396749 : Blo 1419529 2396749 := bbase (se 3 (by rfl) ⟨449390, by rfl⟩ : syracuseStep 2396749 = 898781) (by norm_num)
theorem B1798777 : Blo 1419529 1798777 := bbase (se 2 (by rfl) ⟨674541, by rfl⟩ : syracuseStep 1798777 = 1349083) (by norm_num)
theorem B2396837 : Blo 1419529 2396837 := bbase (se 4 (by rfl) ⟨224703, by rfl⟩ : syracuseStep 2396837 = 449407) (by norm_num)
theorem B4862693 : Blo 1419529 4862693 := bbase (se 4 (by rfl) ⟨455877, by rfl⟩ : syracuseStep 4862693 = 911755) (by norm_num)
theorem B2274053 : Blo 1419529 2274053 := bbase (se 4 (by rfl) ⟨213192, by rfl⟩ : syracuseStep 2274053 = 426385) (by norm_num)
theorem B2396965 : Blo 1419529 2396965 := bbase (se 4 (by rfl) ⟨224715, by rfl⟩ : syracuseStep 2396965 = 449431) (by norm_num)
theorem B1798949 : Blo 1419529 1798949 := bbase (se 4 (by rfl) ⟨168651, by rfl⟩ : syracuseStep 1798949 = 337303) (by norm_num)
theorem B1799005 : Blo 1419529 1799005 := bbase (se 3 (by rfl) ⟨337313, by rfl⟩ : syracuseStep 1799005 = 674627) (by norm_num)
theorem B2397053 : Blo 1419529 2397053 := bbase (se 3 (by rfl) ⟨449447, by rfl⟩ : syracuseStep 2397053 = 898895) (by norm_num)
theorem B7189397 : Blo 1419529 7189397 := bbase (se 6 (by rfl) ⟨168501, by rfl⟩ : syracuseStep 7189397 = 337003) (by norm_num)
theorem B1799101 : Blo 1419529 1799101 := bbase (se 3 (by rfl) ⟨337331, by rfl⟩ : syracuseStep 1799101 = 674663) (by norm_num)
theorem B4797413 : Blo 1419529 4797413 := bbase (se 4 (by rfl) ⟨449757, by rfl⟩ : syracuseStep 4797413 = 899515) (by norm_num)
theorem B2397181 : Blo 1419529 2397181 := bbase (se 3 (by rfl) ⟨449471, by rfl⟩ : syracuseStep 2397181 = 898943) (by norm_num)
theorem B3593261 : Blo 1419529 3593261 := bbase (se 3 (by rfl) ⟨673736, by rfl⟩ : syracuseStep 3593261 = 1347473) (by norm_num)
theorem B2593853 : Blo 1419529 2593853 := bbase (se 3 (by rfl) ⟨486347, by rfl⟩ : syracuseStep 2593853 = 972695) (by norm_num)
theorem B2397269 : Blo 1419529 2397269 := bbase (se 8 (by rfl) ⟨14046, by rfl⟩ : syracuseStep 2397269 = 28093) (by norm_num)
theorem B4551797 : Blo 1419529 4551797 := bbase (se 5 (by rfl) ⟨213365, by rfl⟩ : syracuseStep 4551797 = 426731) (by norm_num)
theorem B2462861 : Blo 1419529 2462861 := bbase (se 3 (by rfl) ⟨461786, by rfl⟩ : syracuseStep 2462861 = 923573) (by norm_num)
theorem B2397397 : Blo 1419529 2397397 := bbase (se 7 (by rfl) ⟨28094, by rfl⟩ : syracuseStep 2397397 = 56189) (by norm_num)
theorem B1438993 : Blo 1419529 1438993 := bbase (se 2 (by rfl) ⟨539622, by rfl⟩ : syracuseStep 1438993 = 1079245) (by norm_num)
theorem B2561309 : Blo 1419529 2561309 := bbase (se 3 (by rfl) ⟨480245, by rfl⟩ : syracuseStep 2561309 = 960491) (by norm_num)
theorem B4322597 : Blo 1419529 4322597 := bbase (se 4 (by rfl) ⟨405243, by rfl⟩ : syracuseStep 4322597 = 810487) (by norm_num)
theorem B2397485 : Blo 1419529 2397485 := bbase (se 3 (by rfl) ⟨449528, by rfl⟩ : syracuseStep 2397485 = 899057) (by norm_num)
theorem B3593605 : Blo 1419529 3593605 := bbase (se 4 (by rfl) ⟨336900, by rfl⟩ : syracuseStep 3593605 = 673801) (by norm_num)
theorem B1619365 : Blo 1419529 1619365 := bbase (se 4 (by rfl) ⟨151815, by rfl⟩ : syracuseStep 1619365 = 303631) (by norm_num)
theorem B2274733 : Blo 1419529 2274733 := bbase (se 3 (by rfl) ⟨426512, by rfl⟩ : syracuseStep 2274733 = 853025) (by norm_num)
theorem B2397613 : Blo 1419529 2397613 := bbase (se 3 (by rfl) ⟨449552, by rfl⟩ : syracuseStep 2397613 = 899105) (by norm_num)
theorem B13661621 : Blo 1419529 13661621 := bbase (se 5 (by rfl) ⟨640388, by rfl⟩ : syracuseStep 13661621 = 1280777) (by norm_num)
theorem B6829541 : Blo 1419529 6829541 := bbase (se 4 (by rfl) ⟨640269, by rfl⟩ : syracuseStep 6829541 = 1280539) (by norm_num)
theorem B2274797 : Blo 1419529 2274797 := bbase (se 3 (by rfl) ⟨426524, by rfl⟩ : syracuseStep 2274797 = 853049) (by norm_num)
theorem B3593717 : Blo 1419529 3593717 := bbase (se 5 (by rfl) ⟨168455, by rfl⟩ : syracuseStep 3593717 = 336911) (by norm_num)
theorem B2397701 : Blo 1419529 2397701 := bbase (se 4 (by rfl) ⟨224784, by rfl⟩ : syracuseStep 2397701 = 449569) (by norm_num)
theorem B1619525 : Blo 1419529 1619525 := bbase (se 4 (by rfl) ⟨151830, by rfl⟩ : syracuseStep 1619525 = 303661) (by norm_num)
theorem B4552309 : Blo 1419529 4552309 := bbase (se 5 (by rfl) ⟨213389, by rfl⟩ : syracuseStep 4552309 = 426779) (by norm_num)
theorem B2160253 : Blo 1419529 2160253 := bbase (se 3 (by rfl) ⟨405047, by rfl⟩ : syracuseStep 2160253 = 810095) (by norm_num)
theorem B5117573 : Blo 1419529 5117573 := bbase (se 4 (by rfl) ⟨479772, by rfl⟩ : syracuseStep 5117573 = 959545) (by norm_num)
theorem B2397829 : Blo 1419529 2397829 := bbase (se 4 (by rfl) ⟨224796, by rfl⟩ : syracuseStep 2397829 = 449593) (by norm_num)
theorem B3118765 : Blo 1419529 3118765 := bbase (se 3 (by rfl) ⟨584768, by rfl⟩ : syracuseStep 3118765 = 1169537) (by norm_num)
theorem B3593909 : Blo 1419529 3593909 := bbase (se 5 (by rfl) ⟨168464, by rfl⟩ : syracuseStep 3593909 = 336929) (by norm_num)
theorem B5396165 : Blo 1419529 5396165 := bbase (se 4 (by rfl) ⟨505890, by rfl⟩ : syracuseStep 5396165 = 1011781) (by norm_num)
theorem B2397917 : Blo 1419529 2397917 := bbase (se 3 (by rfl) ⟨449609, by rfl⟩ : syracuseStep 2397917 = 899219) (by norm_num)
theorem B5117717 : Blo 1419529 5117717 := bbase (se 6 (by rfl) ⟨119946, by rfl⟩ : syracuseStep 5117717 = 239893) (by norm_num)
theorem B4044629 : Blo 1419529 4044629 := bbase (se 9 (by rfl) ⟨11849, by rfl⟩ : syracuseStep 4044629 = 23699) (by norm_num)
theorem B2398045 : Blo 1419529 2398045 := bbase (se 3 (by rfl) ⟨449633, by rfl⟩ : syracuseStep 2398045 = 899267) (by norm_num)
theorem B2021221 : Blo 1419529 2021221 := bbase (se 4 (by rfl) ⟨189489, by rfl⟩ : syracuseStep 2021221 = 378979) (by norm_num)
theorem B2398133 : Blo 1419529 2398133 := bbase (se 5 (by rfl) ⟨112412, by rfl⟩ : syracuseStep 2398133 = 224825) (by norm_num)
theorem B5396453 : Blo 1419529 5396453 := bbase (se 4 (by rfl) ⟨505917, by rfl⟩ : syracuseStep 5396453 = 1011835) (by norm_num)
theorem B3594253 : Blo 1419529 3594253 := bbase (se 3 (by rfl) ⟨673922, by rfl⟩ : syracuseStep 3594253 = 1347845) (by norm_num)
theorem B1619989 : Blo 1419529 1619989 := bbase (se 6 (by rfl) ⟨37968, by rfl⟩ : syracuseStep 1619989 = 75937) (by norm_num)
theorem B5118005 : Blo 1419529 5118005 := bbase (se 5 (by rfl) ⟨239906, by rfl⟩ : syracuseStep 5118005 = 479813) (by norm_num)
theorem B14784565 : Blo 1419529 14784565 := bbase (se 5 (by rfl) ⟨693026, by rfl⟩ : syracuseStep 14784565 = 1386053) (by norm_num)
theorem B2398261 : Blo 1419529 2398261 := bbase (se 5 (by rfl) ⟨112418, by rfl⟩ : syracuseStep 2398261 = 224837) (by norm_num)
theorem B2734157 : Blo 1419529 2734157 := bbase (se 3 (by rfl) ⟨512654, by rfl⟩ : syracuseStep 2734157 = 1025309) (by norm_num)
theorem B3594365 : Blo 1419529 3594365 := bbase (se 3 (by rfl) ⟨673943, by rfl⟩ : syracuseStep 3594365 = 1347887) (by norm_num)
theorem B2398349 : Blo 1419529 2398349 := bbase (se 3 (by rfl) ⟨449690, by rfl⟩ : syracuseStep 2398349 = 899381) (by norm_num)
theorem B7190693 : Blo 1419529 7190693 := bbase (se 4 (by rfl) ⟨674127, by rfl⟩ : syracuseStep 7190693 = 1348255) (by norm_num)
theorem B1579225 : Blo 1419529 1579225 := bbase (se 2 (by rfl) ⟨592209, by rfl⟩ : syracuseStep 1579225 = 1184419) (by norm_num)
theorem B12957941 : Blo 1419529 12957941 := bbase (se 5 (by rfl) ⟨607403, by rfl⟩ : syracuseStep 12957941 = 1214807) (by norm_num)
theorem B2398477 : Blo 1419529 2398477 := bbase (se 3 (by rfl) ⟨449714, by rfl⟩ : syracuseStep 2398477 = 899429) (by norm_num)
theorem B3594557 : Blo 1419529 3594557 := bbase (se 3 (by rfl) ⟨673979, by rfl⟩ : syracuseStep 3594557 = 1347959) (by norm_num)
theorem B2398565 : Blo 1419529 2398565 := bbase (se 4 (by rfl) ⟨224865, by rfl⟩ : syracuseStep 2398565 = 449731) (by norm_num)
theorem B1620337 : Blo 1419529 1620337 := bbase (se 2 (by rfl) ⟨607626, by rfl⟩ : syracuseStep 1620337 = 1215253) (by norm_num)
theorem B1538417 : Blo 1419529 1538417 := bbase (se 2 (by rfl) ⟨576906, by rfl⟩ : syracuseStep 1538417 = 1153813) (by norm_num)
theorem B1440137 : Blo 1419529 1440137 := bbase (se 2 (by rfl) ⟨540051, by rfl⟩ : syracuseStep 1440137 = 1080103) (by norm_num)
theorem B5757365 : Blo 1419529 5757365 := bbase (se 5 (by rfl) ⟨269876, by rfl⟩ : syracuseStep 5757365 = 539753) (by norm_num)
theorem B2398693 : Blo 1419529 2398693 := bbase (se 4 (by rfl) ⟨224877, by rfl⟩ : syracuseStep 2398693 = 449755) (by norm_num)
theorem B2595349 : Blo 1419529 2595349 := bbase (se 6 (by rfl) ⟨60828, by rfl⟩ : syracuseStep 2595349 = 121657) (by norm_num)
theorem B2431517 : Blo 1419529 2431517 := bbase (se 3 (by rfl) ⟨455909, by rfl⟩ : syracuseStep 2431517 = 911819) (by norm_num)
theorem B6068789 : Blo 1419529 6068789 := bbase (se 5 (by rfl) ⟨284474, by rfl⟩ : syracuseStep 6068789 = 568949) (by norm_num)
theorem B2398781 : Blo 1419529 2398781 := bbase (se 3 (by rfl) ⟨449771, by rfl⟩ : syracuseStep 2398781 = 899543) (by norm_num)
theorem B2808389 : Blo 1419529 2808389 := bbase (se 4 (by rfl) ⟨263286, by rfl⟩ : syracuseStep 2808389 = 526573) (by norm_num)
theorem B2022013 : Blo 1419529 2022013 := bbase (se 3 (by rfl) ⟨379127, by rfl⟩ : syracuseStep 2022013 = 758255) (by norm_num)
theorem B4790933 : Blo 1419529 4790933 := bbase (se 6 (by rfl) ⟨112287, by rfl⟩ : syracuseStep 4790933 = 224575) (by norm_num)
theorem B3594901 : Blo 1419529 3594901 := bbase (se 6 (by rfl) ⟨84255, by rfl⟩ : syracuseStep 3594901 = 168511) (by norm_num)
theorem B1538713 : Blo 1419529 1538713 := bbase (se 2 (by rfl) ⟨577017, by rfl⟩ : syracuseStep 1538713 = 1154035) (by norm_num)
theorem B3595013 : Blo 1419529 3595013 := bbase (se 4 (by rfl) ⟨337032, by rfl⟩ : syracuseStep 3595013 = 674065) (by norm_num)
theorem B7289605 : Blo 1419529 7289605 := bbase (se 4 (by rfl) ⟨683400, by rfl⟩ : syracuseStep 7289605 = 1366801) (by norm_num)
theorem B2276117 : Blo 1419529 2276117 := bbase (se 6 (by rfl) ⟨53346, by rfl⟩ : syracuseStep 2276117 = 106693) (by norm_num)
theorem B3644237 : Blo 1419529 3644237 := bbase (se 3 (by rfl) ⟨683294, by rfl⟩ : syracuseStep 3644237 = 1366589) (by norm_num)
theorem B3595205 : Blo 1419529 3595205 := bbase (se 4 (by rfl) ⟨337050, by rfl⟩ : syracuseStep 3595205 = 674101) (by norm_num)
theorem B2022349 : Blo 1419529 2022349 := bbase (se 3 (by rfl) ⟨379190, by rfl⟩ : syracuseStep 2022349 = 758381) (by norm_num)
theorem B2276309 : Blo 1419529 2276309 := bbase (se 7 (by rfl) ⟨26675, by rfl⟩ : syracuseStep 2276309 = 53351) (by norm_num)
theorem B3283997 : Blo 1419529 3283997 := bbase (se 3 (by rfl) ⟨615749, by rfl⟩ : syracuseStep 3283997 = 1231499) (by norm_num)
theorem B3415069 : Blo 1419529 3415069 := bbase (se 3 (by rfl) ⟨640325, by rfl⟩ : syracuseStep 3415069 = 1280651) (by norm_num)
theorem B4791365 : Blo 1419529 4791365 := bbase (se 4 (by rfl) ⟨449190, by rfl⟩ : syracuseStep 4791365 = 898381) (by norm_num)
theorem B3415117 : Blo 1419529 3415117 := bbase (se 3 (by rfl) ⟨640334, by rfl⟩ : syracuseStep 3415117 = 1280669) (by norm_num)
theorem B2276437 : Blo 1419529 2276437 := bbase (se 8 (by rfl) ⟨13338, by rfl⟩ : syracuseStep 2276437 = 26677) (by norm_num)
theorem B3193973 : Blo 1419529 3193973 := bbase (se 5 (by rfl) ⟨149717, by rfl⟩ : syracuseStep 3193973 = 299435) (by norm_num)
theorem B2022565 : Blo 1419529 2022565 := bbase (se 4 (by rfl) ⟨189615, by rfl⟩ : syracuseStep 2022565 = 379231) (by norm_num)
theorem B3194045 : Blo 1419529 3194045 := bbase (se 3 (by rfl) ⟨598883, by rfl⟩ : syracuseStep 3194045 = 1197767) (by norm_num)
theorem B3194117 : Blo 1419529 3194117 := bbase (se 4 (by rfl) ⟨299448, by rfl⟩ : syracuseStep 3194117 = 598897) (by norm_num)
theorem B3595549 : Blo 1419529 3595549 := bbase (se 3 (by rfl) ⟨674165, by rfl⟩ : syracuseStep 3595549 = 1348331) (by norm_num)
theorem B11672885 : Blo 1419529 11672885 := bbase (se 5 (by rfl) ⟨547166, by rfl⟩ : syracuseStep 11672885 = 1094333) (by norm_num)
theorem B3194189 : Blo 1419529 3194189 := bbase (se 3 (by rfl) ⟨598910, by rfl⟩ : syracuseStep 3194189 = 1197821) (by norm_num)
theorem B4046213 : Blo 1419529 4046213 := bbase (se 4 (by rfl) ⟨379332, by rfl⟩ : syracuseStep 4046213 = 758665) (by norm_num)
theorem B3595661 : Blo 1419529 3595661 := bbase (se 3 (by rfl) ⟨674186, by rfl⟩ : syracuseStep 3595661 = 1348373) (by norm_num)
theorem B3194261 : Blo 1419529 3194261 := bbase (se 6 (by rfl) ⟨74865, by rfl⟩ : syracuseStep 3194261 = 149731) (by norm_num)
theorem B2129309 : Blo 1419529 2129309 := bbase (se 3 (by rfl) ⟨399245, by rfl⟩ : syracuseStep 2129309 = 798491) (by norm_num)
theorem B2129333 : Blo 1419529 2129333 := bbase (se 5 (by rfl) ⟨99812, by rfl⟩ : syracuseStep 2129333 = 199625) (by norm_num)
theorem B7191989 : Blo 1419529 7191989 := bbase (se 5 (by rfl) ⟨337124, by rfl⟩ : syracuseStep 7191989 = 674249) (by norm_num)
theorem B2129357 : Blo 1419529 2129357 := bbase (se 3 (by rfl) ⟨399254, by rfl⟩ : syracuseStep 2129357 = 798509) (by norm_num)
theorem B3194333 : Blo 1419529 3194333 := bbase (se 3 (by rfl) ⟨598937, by rfl⟩ : syracuseStep 3194333 = 1197875) (by norm_num)
theorem B2129381 : Blo 1419529 2129381 := bbase (se 4 (by rfl) ⟨199629, by rfl⟩ : syracuseStep 2129381 = 399259) (by norm_num)
theorem B4791797 : Blo 1419529 4791797 := bbase (se 5 (by rfl) ⟨224615, by rfl⟩ : syracuseStep 4791797 = 449231) (by norm_num)
theorem B2129405 : Blo 1419529 2129405 := bbase (se 3 (by rfl) ⟨399263, by rfl⟩ : syracuseStep 2129405 = 798527) (by norm_num)
theorem B2129429 : Blo 1419529 2129429 := bbase (se 6 (by rfl) ⟨49908, by rfl⟩ : syracuseStep 2129429 = 99817) (by norm_num)
theorem B2022941 : Blo 1419529 2022941 := bbase (se 3 (by rfl) ⟨379301, by rfl⟩ : syracuseStep 2022941 = 758603) (by norm_num)
theorem B5389861 : Blo 1419529 5389861 := bbase (se 4 (by rfl) ⟨505299, by rfl⟩ : syracuseStep 5389861 = 1010599) (by norm_num)
theorem B3194405 : Blo 1419529 3194405 := bbase (se 4 (by rfl) ⟨299475, by rfl⟩ : syracuseStep 3194405 = 598951) (by norm_num)
theorem B1596973 : Blo 1419529 1596973 := bbase (se 3 (by rfl) ⟨299432, by rfl⟩ : syracuseStep 1596973 = 598865) (by norm_num)
theorem B2129453 : Blo 1419529 2129453 := bbase (se 3 (by rfl) ⟨399272, by rfl⟩ : syracuseStep 2129453 = 798545) (by norm_num)
theorem B2129477 : Blo 1419529 2129477 := bbase (se 4 (by rfl) ⟨199638, by rfl⟩ : syracuseStep 2129477 = 399277) (by norm_num)
theorem B3595853 : Blo 1419529 3595853 := bbase (se 3 (by rfl) ⟨674222, by rfl⟩ : syracuseStep 3595853 = 1348445) (by norm_num)
theorem B1597009 : Blo 1419529 1597009 := bbase (se 2 (by rfl) ⟨598878, by rfl⟩ : syracuseStep 1597009 = 1197757) (by norm_num)
theorem B2129501 : Blo 1419529 2129501 := bbase (se 3 (by rfl) ⟨399281, by rfl⟩ : syracuseStep 2129501 = 798563) (by norm_num)
theorem B3194477 : Blo 1419529 3194477 := bbase (se 3 (by rfl) ⟨598964, by rfl⟩ : syracuseStep 3194477 = 1197929) (by norm_num)
theorem B1597045 : Blo 1419529 1597045 := bbase (se 5 (by rfl) ⟨74861, by rfl⟩ : syracuseStep 1597045 = 149723) (by norm_num)
theorem B2129525 : Blo 1419529 2129525 := bbase (se 5 (by rfl) ⟨99821, by rfl⟩ : syracuseStep 2129525 = 199643) (by norm_num)
theorem B2129549 : Blo 1419529 2129549 := bbase (se 3 (by rfl) ⟨399290, by rfl⟩ : syracuseStep 2129549 = 798581) (by norm_num)
theorem B1597081 : Blo 1419529 1597081 := bbase (se 2 (by rfl) ⟨598905, by rfl⟩ : syracuseStep 1597081 = 1197811) (by norm_num)
theorem B2129573 : Blo 1419529 2129573 := bbase (se 4 (by rfl) ⟨199647, by rfl⟩ : syracuseStep 2129573 = 399295) (by norm_num)
theorem B3194549 : Blo 1419529 3194549 := bbase (se 5 (by rfl) ⟨149744, by rfl⟩ : syracuseStep 3194549 = 299489) (by norm_num)
theorem B1597117 : Blo 1419529 1597117 := bbase (se 3 (by rfl) ⟨299459, by rfl⟩ : syracuseStep 1597117 = 598919) (by norm_num)
theorem B2129597 : Blo 1419529 2129597 := bbase (se 3 (by rfl) ⟨399299, by rfl⟩ : syracuseStep 2129597 = 798599) (by norm_num)
theorem B2129621 : Blo 1419529 2129621 := bbase (se 7 (by rfl) ⟨24956, by rfl⟩ : syracuseStep 2129621 = 49913) (by norm_num)
theorem B1597153 : Blo 1419529 1597153 := bbase (se 2 (by rfl) ⟨598932, by rfl⟩ : syracuseStep 1597153 = 1197865) (by norm_num)
theorem B2129645 : Blo 1419529 2129645 := bbase (se 3 (by rfl) ⟨399308, by rfl⟩ : syracuseStep 2129645 = 798617) (by norm_num)
theorem B5119733 : Blo 1419529 5119733 := bbase (se 5 (by rfl) ⟨239987, by rfl⟩ : syracuseStep 5119733 = 479975) (by norm_num)
theorem B3194621 : Blo 1419529 3194621 := bbase (se 3 (by rfl) ⟨598991, by rfl⟩ : syracuseStep 3194621 = 1197983) (by norm_num)
theorem B1597189 : Blo 1419529 1597189 := bbase (se 4 (by rfl) ⟨149736, by rfl⟩ : syracuseStep 1597189 = 299473) (by norm_num)
theorem B2129669 : Blo 1419529 2129669 := bbase (se 4 (by rfl) ⟨199656, by rfl⟩ : syracuseStep 2129669 = 399313) (by norm_num)
theorem B2129693 : Blo 1419529 2129693 := bbase (se 3 (by rfl) ⟨399317, by rfl⟩ : syracuseStep 2129693 = 798635) (by norm_num)
theorem B1597225 : Blo 1419529 1597225 := bbase (se 2 (by rfl) ⟨598959, by rfl⟩ : syracuseStep 1597225 = 1197919) (by norm_num)
theorem B2129717 : Blo 1419529 2129717 := bbase (se 5 (by rfl) ⟨99830, by rfl⟩ : syracuseStep 2129717 = 199661) (by norm_num)
theorem B3194693 : Blo 1419529 3194693 := bbase (se 4 (by rfl) ⟨299502, by rfl⟩ : syracuseStep 3194693 = 599005) (by norm_num)
theorem B1597261 : Blo 1419529 1597261 := bbase (se 3 (by rfl) ⟨299486, by rfl⟩ : syracuseStep 1597261 = 598973) (by norm_num)
theorem B2129741 : Blo 1419529 2129741 := bbase (se 3 (by rfl) ⟨399326, by rfl⟩ : syracuseStep 2129741 = 798653) (by norm_num)
theorem B5390165 : Blo 1419529 5390165 := bbase (se 9 (by rfl) ⟨15791, by rfl⟩ : syracuseStep 5390165 = 31583) (by norm_num)
theorem B2129765 : Blo 1419529 2129765 := bbase (se 4 (by rfl) ⟨199665, by rfl⟩ : syracuseStep 2129765 = 399331) (by norm_num)
theorem B1597297 : Blo 1419529 1597297 := bbase (se 2 (by rfl) ⟨598986, by rfl⟩ : syracuseStep 1597297 = 1197973) (by norm_num)
theorem B2129789 : Blo 1419529 2129789 := bbase (se 3 (by rfl) ⟨399335, by rfl⟩ : syracuseStep 2129789 = 798671) (by norm_num)
theorem B2695045 : Blo 1419529 2695045 := bbase (se 4 (by rfl) ⟨252660, by rfl⟩ : syracuseStep 2695045 = 505321) (by norm_num)
theorem B3194765 : Blo 1419529 3194765 := bbase (se 3 (by rfl) ⟨599018, by rfl⟩ : syracuseStep 3194765 = 1198037) (by norm_num)
theorem B1597333 : Blo 1419529 1597333 := bbase (se 6 (by rfl) ⟨37437, by rfl⟩ : syracuseStep 1597333 = 74875) (by norm_num)
theorem B2129813 : Blo 1419529 2129813 := bbase (se 6 (by rfl) ⟨49917, by rfl⟩ : syracuseStep 2129813 = 99835) (by norm_num)
theorem B4792229 : Blo 1419529 4792229 := bbase (se 4 (by rfl) ⟨449271, by rfl⟩ : syracuseStep 4792229 = 898543) (by norm_num)
theorem B3596197 : Blo 1419529 3596197 := bbase (se 4 (by rfl) ⟨337143, by rfl⟩ : syracuseStep 3596197 = 674287) (by norm_num)
theorem B2129837 : Blo 1419529 2129837 := bbase (se 3 (by rfl) ⟨399344, by rfl⟩ : syracuseStep 2129837 = 798689) (by norm_num)
theorem B1597369 : Blo 1419529 1597369 := bbase (se 2 (by rfl) ⟨599013, by rfl⟩ : syracuseStep 1597369 = 1198027) (by norm_num)
theorem B2129861 : Blo 1419529 2129861 := bbase (se 4 (by rfl) ⟨199674, by rfl⟩ : syracuseStep 2129861 = 399349) (by norm_num)
theorem B3194837 : Blo 1419529 3194837 := bbase (se 7 (by rfl) ⟨37439, by rfl⟩ : syracuseStep 3194837 = 74879) (by norm_num)
theorem B1597405 : Blo 1419529 1597405 := bbase (se 3 (by rfl) ⟨299513, by rfl⟩ : syracuseStep 1597405 = 599027) (by norm_num)
theorem B2129885 : Blo 1419529 2129885 := bbase (se 3 (by rfl) ⟨399353, by rfl⟩ : syracuseStep 2129885 = 798707) (by norm_num)
theorem B2129909 : Blo 1419529 2129909 := bbase (se 5 (by rfl) ⟨99839, by rfl⟩ : syracuseStep 2129909 = 199679) (by norm_num)
theorem B2129921 : Blo 1419529 2129921 := bstep (se 2 (by rfl) ⟨798720, by rfl⟩ : syracuseStep 2129921 = 1597441) B1597441
theorem B4046861 : Blo 1419529 4046861 := bstep (se 3 (by rfl) ⟨758786, by rfl⟩ : syracuseStep 4046861 = 1517573) B1517573
theorem B4792337 : Blo 1419529 4792337 := bstep (se 2 (by rfl) ⟨1797126, by rfl⟩ : syracuseStep 4792337 = 3594253) B3594253
theorem B2129939 : Blo 1419529 2129939 := bstep (se 1 (by rfl) ⟨1597454, by rfl⟩ : syracuseStep 2129939 = 3194909) B3194909
theorem B1597459 : Blo 1419529 1597459 := bstep (se 1 (by rfl) ⟨1198094, by rfl⟩ : syracuseStep 1597459 = 2396189) B2396189
theorem B2129969 : Blo 1419529 2129969 := bstep (se 2 (by rfl) ⟨798738, by rfl⟩ : syracuseStep 2129969 = 1597477) B1597477
theorem B2129987 : Blo 1419529 2129987 := bstep (se 1 (by rfl) ⟨1597490, by rfl⟩ : syracuseStep 2129987 = 3194981) B3194981
theorem B8757325 : Blo 1419529 8757325 := bstep (se 3 (by rfl) ⟨1641998, by rfl⟩ : syracuseStep 8757325 = 3283997) B3283997
theorem B2130017 : Blo 1419529 2130017 := bstep (se 2 (by rfl) ⟨798756, by rfl⟩ : syracuseStep 2130017 = 1597513) B1597513
theorem B15368291 : Blo 1419529 15368291 := bstep (se 1 (by rfl) ⟨11526218, by rfl⟩ : syracuseStep 15368291 = 23052437) B23052437
theorem B10379377 : Blo 1419529 10379377 := bstep (se 2 (by rfl) ⟨3892266, by rfl⟩ : syracuseStep 10379377 = 7784533) B7784533
theorem B2130035 : Blo 1419529 2130035 := bstep (se 1 (by rfl) ⟨1597526, by rfl⟩ : syracuseStep 2130035 = 3195053) B3195053
theorem B2130065 : Blo 1419529 2130065 := bstep (se 2 (by rfl) ⟨798774, by rfl⟩ : syracuseStep 2130065 = 1597549) B1597549
theorem B2130083 : Blo 1419529 2130083 := bstep (se 1 (by rfl) ⟨1597562, by rfl⟩ : syracuseStep 2130083 = 3195125) B3195125
theorem B1597603 : Blo 1419529 1597603 := bstep (se 1 (by rfl) ⟨1198202, by rfl⟩ : syracuseStep 1597603 = 2396405) B2396405
theorem B2130113 : Blo 1419529 2130113 := bstep (se 2 (by rfl) ⟨798792, by rfl⟩ : syracuseStep 2130113 = 1597585) B1597585
theorem B3195089 : Blo 1419529 3195089 := bstep (se 2 (by rfl) ⟨1198158, by rfl⟩ : syracuseStep 3195089 = 2396317) B2396317
theorem B2130131 : Blo 1419529 2130131 := bstep (se 1 (by rfl) ⟨1597598, by rfl⟩ : syracuseStep 2130131 = 3195197) B3195197
theorem B3195107 : Blo 1419529 3195107 := bstep (se 1 (by rfl) ⟨2396330, by rfl⟩ : syracuseStep 3195107 = 4792661) B4792661
theorem B2130161 : Blo 1419529 2130161 := bstep (se 2 (by rfl) ⟨798810, by rfl⟩ : syracuseStep 2130161 = 1597621) B1597621
theorem B2130179 : Blo 1419529 2130179 := bstep (se 1 (by rfl) ⟨1597634, by rfl⟩ : syracuseStep 2130179 = 3195269) B3195269
theorem B2023699 : Blo 1419529 2023699 := bstep (se 1 (by rfl) ⟨1517774, by rfl⟩ : syracuseStep 2023699 = 3035549) B3035549
theorem B2105633 : Blo 1419529 2105633 := bstep (se 2 (by rfl) ⟨789612, by rfl⟩ : syracuseStep 2105633 = 1579225) B1579225
theorem B2130209 : Blo 1419529 2130209 := bstep (se 2 (by rfl) ⟨798828, by rfl⟩ : syracuseStep 2130209 = 1597657) B1597657
theorem B2130227 : Blo 1419529 2130227 := bstep (se 1 (by rfl) ⟨1597670, by rfl⟩ : syracuseStep 2130227 = 3195341) B3195341
theorem B1597747 : Blo 1419529 1597747 := bstep (se 1 (by rfl) ⟨1198310, by rfl⟩ : syracuseStep 1597747 = 2396621) B2396621
theorem B2130257 : Blo 1419529 2130257 := bstep (se 2 (by rfl) ⟨798846, by rfl⟩ : syracuseStep 2130257 = 1597693) B1597693
theorem B2130275 : Blo 1419529 2130275 := bstep (se 1 (by rfl) ⟨1597706, by rfl⟩ : syracuseStep 2130275 = 3195413) B3195413
theorem B2023795 : Blo 1419529 2023795 := bstep (se 1 (by rfl) ⟨1517846, by rfl⟩ : syracuseStep 2023795 = 3035693) B3035693
theorem B2130305 : Blo 1419529 2130305 := bstep (se 2 (by rfl) ⟨798864, by rfl⟩ : syracuseStep 2130305 = 1597729) B1597729
theorem B2130323 : Blo 1419529 2130323 := bstep (se 1 (by rfl) ⟨1597742, by rfl⟩ : syracuseStep 2130323 = 3195485) B3195485
theorem B2130353 : Blo 1419529 2130353 := bstep (se 2 (by rfl) ⟨798882, by rfl⟩ : syracuseStep 2130353 = 1597765) B1597765
theorem B2130371 : Blo 1419529 2130371 := bstep (se 1 (by rfl) ⟨1597778, by rfl⟩ : syracuseStep 2130371 = 3195557) B3195557
theorem B1597891 : Blo 1419529 1597891 := bstep (se 1 (by rfl) ⟨1198418, by rfl⟩ : syracuseStep 1597891 = 2396837) B2396837
theorem B2130401 : Blo 1419529 2130401 := bstep (se 2 (by rfl) ⟨798900, by rfl⟩ : syracuseStep 2130401 = 1597801) B1597801
theorem B5390819 : Blo 1419529 5390819 := bstep (se 1 (by rfl) ⟨4043114, by rfl⟩ : syracuseStep 5390819 = 8086229) B8086229
theorem B5390833 : Blo 1419529 5390833 := bstep (se 2 (by rfl) ⟨2021562, by rfl⟩ : syracuseStep 5390833 = 4043125) B4043125
theorem B3195377 : Blo 1419529 3195377 := bstep (se 2 (by rfl) ⟨1198266, by rfl⟩ : syracuseStep 3195377 = 2396533) B2396533
theorem B2130419 : Blo 1419529 2130419 := bstep (se 1 (by rfl) ⟨1597814, by rfl⟩ : syracuseStep 2130419 = 3195629) B3195629
theorem B3195395 : Blo 1419529 3195395 := bstep (se 1 (by rfl) ⟨2396546, by rfl⟩ : syracuseStep 3195395 = 4793093) B4793093
theorem B15368717 : Blo 1419529 15368717 := bstep (se 3 (by rfl) ⟨2881634, by rfl⟩ : syracuseStep 15368717 = 5763269) B5763269
theorem B2130449 : Blo 1419529 2130449 := bstep (se 2 (by rfl) ⟨798918, by rfl⟩ : syracuseStep 2130449 = 1597837) B1597837
theorem B2130467 : Blo 1419529 2130467 := bstep (se 1 (by rfl) ⟨1597850, by rfl⟩ : syracuseStep 2130467 = 3195701) B3195701
theorem B7193123 : Blo 1419529 7193123 := bstep (se 1 (by rfl) ⟨5394842, by rfl⟩ : syracuseStep 7193123 = 10789685) B10789685
theorem B4792877 : Blo 1419529 4792877 := bstep (se 3 (by rfl) ⟨898664, by rfl⟩ : syracuseStep 4792877 = 1797329) B1797329
theorem B2130497 : Blo 1419529 2130497 := bstep (se 2 (by rfl) ⟨798936, by rfl⟩ : syracuseStep 2130497 = 1597873) B1597873
theorem B2130515 : Blo 1419529 2130515 := bstep (se 1 (by rfl) ⟨1597886, by rfl⟩ : syracuseStep 2130515 = 3195773) B3195773
theorem B1598035 : Blo 1419529 1598035 := bstep (se 1 (by rfl) ⟨1198526, by rfl⟩ : syracuseStep 1598035 = 2397053) B2397053
theorem B4792931 : Blo 1419529 4792931 := bstep (se 1 (by rfl) ⟨3594698, by rfl⟩ : syracuseStep 4792931 = 7189397) B7189397
theorem B2130545 : Blo 1419529 2130545 := bstep (se 2 (by rfl) ⟨798954, by rfl⟩ : syracuseStep 2130545 = 1597909) B1597909
theorem B2130563 : Blo 1419529 2130563 := bstep (se 1 (by rfl) ⟨1597922, by rfl⟩ : syracuseStep 2130563 = 3195845) B3195845
theorem B34554509 : Blo 1419529 34554509 := bstep (se 3 (by rfl) ⟨6478970, by rfl⟩ : syracuseStep 34554509 = 12957941) B12957941
theorem B30720653 : Blo 1419529 30720653 := bstep (se 3 (by rfl) ⟨5760122, by rfl⟩ : syracuseStep 30720653 = 11520245) B11520245
theorem B2130593 : Blo 1419529 2130593 := bstep (se 2 (by rfl) ⟨798972, by rfl⟩ : syracuseStep 2130593 = 1597945) B1597945
theorem B2130611 : Blo 1419529 2130611 := bstep (se 1 (by rfl) ⟨1597958, by rfl⟩ : syracuseStep 2130611 = 3195917) B3195917
theorem B2130641 : Blo 1419529 2130641 := bstep (se 2 (by rfl) ⟨798990, by rfl⟩ : syracuseStep 2130641 = 1597981) B1597981
theorem B1729235 : Blo 1419529 1729235 := bstep (se 1 (by rfl) ⟨1296926, by rfl⟩ : syracuseStep 1729235 = 2593853) B2593853
theorem B2130659 : Blo 1419529 2130659 := bstep (se 1 (by rfl) ⟨1597994, by rfl⟩ : syracuseStep 2130659 = 3195989) B3195989
theorem B1598179 : Blo 1419529 1598179 := bstep (se 1 (by rfl) ⟨1198634, by rfl⟩ : syracuseStep 1598179 = 2397269) B2397269
theorem B2130689 : Blo 1419529 2130689 := bstep (se 2 (by rfl) ⟨799008, by rfl⟩ : syracuseStep 2130689 = 1598017) B1598017
theorem B16188173 : Blo 1419529 16188173 := bstep (se 3 (by rfl) ⟨3035282, by rfl⟩ : syracuseStep 16188173 = 6070565) B6070565
theorem B3195665 : Blo 1419529 3195665 := bstep (se 2 (by rfl) ⟨1198374, by rfl⟩ : syracuseStep 3195665 = 2396749) B2396749
theorem B2130707 : Blo 1419529 2130707 := bstep (se 1 (by rfl) ⟨1598030, by rfl⟩ : syracuseStep 2130707 = 3196061) B3196061
theorem B3195683 : Blo 1419529 3195683 := bstep (se 1 (by rfl) ⟨2396762, by rfl⟩ : syracuseStep 3195683 = 4793525) B4793525
theorem B2130737 : Blo 1419529 2130737 := bstep (se 2 (by rfl) ⟨799026, by rfl⟩ : syracuseStep 2130737 = 1598053) B1598053
theorem B2130755 : Blo 1419529 2130755 := bstep (se 1 (by rfl) ⟨1598066, by rfl⟩ : syracuseStep 2130755 = 3196133) B3196133
theorem B2696017 : Blo 1419529 2696017 := bstep (se 2 (by rfl) ⟨1011006, by rfl⟩ : syracuseStep 2696017 = 2022013) B2022013
theorem B2130785 : Blo 1419529 2130785 := bstep (se 2 (by rfl) ⟨799044, by rfl⟩ : syracuseStep 2130785 = 1598089) B1598089
theorem B4793201 : Blo 1419529 4793201 := bstep (se 2 (by rfl) ⟨1797450, by rfl⟩ : syracuseStep 4793201 = 3594901) B3594901
theorem B3597169 : Blo 1419529 3597169 := bstep (se 2 (by rfl) ⟨1348938, by rfl⟩ : syracuseStep 3597169 = 2697877) B2697877
theorem B2130803 : Blo 1419529 2130803 := bstep (se 1 (by rfl) ⟨1598102, by rfl⟩ : syracuseStep 2130803 = 3196205) B3196205
theorem B1598323 : Blo 1419529 1598323 := bstep (se 1 (by rfl) ⟨1198742, by rfl⟩ : syracuseStep 1598323 = 2397485) B2397485
theorem B2130833 : Blo 1419529 2130833 := bstep (se 2 (by rfl) ⟨799062, by rfl⟩ : syracuseStep 2130833 = 1598125) B1598125
theorem B2130851 : Blo 1419529 2130851 := bstep (se 1 (by rfl) ⟨1598138, by rfl⟩ : syracuseStep 2130851 = 3196277) B3196277
theorem B2130881 : Blo 1419529 2130881 := bstep (se 2 (by rfl) ⟨799080, by rfl⟩ : syracuseStep 2130881 = 1598161) B1598161
theorem B17277893 : Blo 1419529 17277893 := bstep (se 4 (by rfl) ⟨1619802, by rfl⟩ : syracuseStep 17277893 = 3239605) B3239605
theorem B2130899 : Blo 1419529 2130899 := bstep (se 1 (by rfl) ⟨1598174, by rfl⟩ : syracuseStep 2130899 = 3196349) B3196349
theorem B4047853 : Blo 1419529 4047853 := bstep (se 3 (by rfl) ⟨758972, by rfl⟩ : syracuseStep 4047853 = 1517945) B1517945
theorem B2130929 : Blo 1419529 2130929 := bstep (se 2 (by rfl) ⟨799098, by rfl⟩ : syracuseStep 2130929 = 1598197) B1598197
theorem B1516531 : Blo 1419529 1516531 := bstep (se 1 (by rfl) ⟨1137398, by rfl⟩ : syracuseStep 1516531 = 2274797) B2274797
theorem B2130947 : Blo 1419529 2130947 := bstep (se 1 (by rfl) ⟨1598210, by rfl⟩ : syracuseStep 2130947 = 3196421) B3196421
theorem B1598467 : Blo 1419529 1598467 := bstep (se 1 (by rfl) ⟨1198850, by rfl⟩ : syracuseStep 1598467 = 2397701) B2397701
theorem B8094725 : Blo 1419529 8094725 := bstep (se 4 (by rfl) ⟨758880, by rfl⟩ : syracuseStep 8094725 = 1517761) B1517761
theorem B2130977 : Blo 1419529 2130977 := bstep (se 2 (by rfl) ⟨799116, by rfl⟩ : syracuseStep 2130977 = 1598233) B1598233
theorem B3195953 : Blo 1419529 3195953 := bstep (se 2 (by rfl) ⟨1198482, by rfl⟩ : syracuseStep 3195953 = 2396965) B2396965
theorem B2130995 : Blo 1419529 2130995 := bstep (se 1 (by rfl) ⟨1598246, by rfl⟩ : syracuseStep 2130995 = 3196493) B3196493
theorem B3195971 : Blo 1419529 3195971 := bstep (se 1 (by rfl) ⟨2396978, by rfl⟩ : syracuseStep 3195971 = 4793957) B4793957
theorem B2131025 : Blo 1419529 2131025 := bstep (se 2 (by rfl) ⟨799134, by rfl⟩ : syracuseStep 2131025 = 1598269) B1598269
theorem B2131043 : Blo 1419529 2131043 := bstep (se 1 (by rfl) ⟨1598282, by rfl⟩ : syracuseStep 2131043 = 3196565) B3196565
theorem B2131073 : Blo 1419529 2131073 := bstep (se 2 (by rfl) ⟨799152, by rfl⟩ : syracuseStep 2131073 = 1598305) B1598305
theorem B3597443 : Blo 1419529 3597443 := bstep (se 1 (by rfl) ⟨2698082, by rfl⟩ : syracuseStep 3597443 = 5396165) B5396165
theorem B8086661 : Blo 1419529 8086661 := bstep (se 4 (by rfl) ⟨758124, by rfl⟩ : syracuseStep 8086661 = 1516249) B1516249
theorem B15352973 : Blo 1419529 15352973 := bstep (se 3 (by rfl) ⟨2878682, by rfl⟩ : syracuseStep 15352973 = 5757365) B5757365
theorem B2131091 : Blo 1419529 2131091 := bstep (se 1 (by rfl) ⟨1598318, by rfl⟩ : syracuseStep 2131091 = 3196637) B3196637
theorem B1598611 : Blo 1419529 1598611 := bstep (se 1 (by rfl) ⟨1198958, by rfl⟩ : syracuseStep 1598611 = 2397917) B2397917
theorem B2131121 : Blo 1419529 2131121 := bstep (se 2 (by rfl) ⟨799170, by rfl⟩ : syracuseStep 2131121 = 1598341) B1598341
theorem B2131139 : Blo 1419529 2131139 := bstep (se 1 (by rfl) ⟨1598354, by rfl⟩ : syracuseStep 2131139 = 3196709) B3196709
theorem B2131169 : Blo 1419529 2131169 := bstep (se 2 (by rfl) ⟨799188, by rfl⟩ : syracuseStep 2131169 = 1598377) B1598377
theorem B2696419 : Blo 1419529 2696419 := bstep (se 1 (by rfl) ⟨2022314, by rfl⟩ : syracuseStep 2696419 = 4044629) B4044629
theorem B2131187 : Blo 1419529 2131187 := bstep (se 1 (by rfl) ⟨1598390, by rfl⟩ : syracuseStep 2131187 = 3196781) B3196781
theorem B2696465 : Blo 1419529 2696465 := bstep (se 2 (by rfl) ⟨1011174, by rfl⟩ : syracuseStep 2696465 = 2022349) B2022349
theorem B2131217 : Blo 1419529 2131217 := bstep (se 2 (by rfl) ⟨799206, by rfl⟩ : syracuseStep 2131217 = 1598413) B1598413
theorem B2131235 : Blo 1419529 2131235 := bstep (se 1 (by rfl) ⟨1598426, by rfl⟩ : syracuseStep 2131235 = 3196853) B3196853
theorem B1598755 : Blo 1419529 1598755 := bstep (se 1 (by rfl) ⟨1199066, by rfl⟩ : syracuseStep 1598755 = 2398133) B2398133
theorem B2131265 : Blo 1419529 2131265 := bstep (se 2 (by rfl) ⟨799224, by rfl⟩ : syracuseStep 2131265 = 1598449) B1598449
theorem B3597635 : Blo 1419529 3597635 := bstep (se 1 (by rfl) ⟨2698226, by rfl⟩ : syracuseStep 3597635 = 5396453) B5396453
theorem B7193933 : Blo 1419529 7193933 := bstep (se 3 (by rfl) ⟨1348862, by rfl⟩ : syracuseStep 7193933 = 2697725) B2697725
theorem B3196241 : Blo 1419529 3196241 := bstep (se 2 (by rfl) ⟨1198590, by rfl⟩ : syracuseStep 3196241 = 2397181) B2397181
theorem B2131283 : Blo 1419529 2131283 := bstep (se 1 (by rfl) ⟨1598462, by rfl⟩ : syracuseStep 2131283 = 3196925) B3196925
theorem B3196259 : Blo 1419529 3196259 := bstep (se 1 (by rfl) ⟨2397194, by rfl⟩ : syracuseStep 3196259 = 4794389) B4794389
theorem B2131313 : Blo 1419529 2131313 := bstep (se 2 (by rfl) ⟨799242, by rfl⟩ : syracuseStep 2131313 = 1598485) B1598485
theorem B2131331 : Blo 1419529 2131331 := bstep (se 1 (by rfl) ⟨1598498, by rfl⟩ : syracuseStep 2131331 = 3196997) B3196997
theorem B4793741 : Blo 1419529 4793741 := bstep (se 3 (by rfl) ⟨898826, by rfl⟩ : syracuseStep 4793741 = 1797653) B1797653
theorem B2131361 : Blo 1419529 2131361 := bstep (se 2 (by rfl) ⟨799260, by rfl⟩ : syracuseStep 2131361 = 1598521) B1598521
theorem B2131379 : Blo 1419529 2131379 := bstep (se 1 (by rfl) ⟨1598534, by rfl⟩ : syracuseStep 2131379 = 3197069) B3197069
theorem B1598899 : Blo 1419529 1598899 := bstep (se 1 (by rfl) ⟨1199174, by rfl⟩ : syracuseStep 1598899 = 2398349) B2398349
theorem B3032515 : Blo 1419529 3032515 := bstep (se 1 (by rfl) ⟨2274386, by rfl⟩ : syracuseStep 3032515 = 4548773) B4548773
theorem B4793795 : Blo 1419529 4793795 := bstep (se 1 (by rfl) ⟨3595346, by rfl⟩ : syracuseStep 4793795 = 7190693) B7190693
theorem B2131409 : Blo 1419529 2131409 := bstep (se 2 (by rfl) ⟨799278, by rfl⟩ : syracuseStep 2131409 = 1598557) B1598557
theorem B2131427 : Blo 1419529 2131427 := bstep (se 1 (by rfl) ⟨1598570, by rfl⟩ : syracuseStep 2131427 = 3197141) B3197141
theorem B2131457 : Blo 1419529 2131457 := bstep (se 2 (by rfl) ⟨799296, by rfl⟩ : syracuseStep 2131457 = 1598593) B1598593
theorem B4318733 : Blo 1419529 4318733 := bstep (se 3 (by rfl) ⟨809762, by rfl⟩ : syracuseStep 4318733 = 1619525) B1619525
theorem B7489037 : Blo 1419529 7489037 := bstep (se 3 (by rfl) ⟨1404194, by rfl⟩ : syracuseStep 7489037 = 2808389) B2808389
theorem B2131475 : Blo 1419529 2131475 := bstep (se 1 (by rfl) ⟨1598606, by rfl⟩ : syracuseStep 2131475 = 3197213) B3197213
theorem B2696753 : Blo 1419529 2696753 := bstep (se 2 (by rfl) ⟨1011282, by rfl⟩ : syracuseStep 2696753 = 2022565) B2022565
theorem B2131505 : Blo 1419529 2131505 := bstep (se 2 (by rfl) ⟨799314, by rfl⟩ : syracuseStep 2131505 = 1598629) B1598629
theorem B20473397 : Blo 1419529 20473397 := bstep (se 5 (by rfl) ⟨959690, by rfl⟩ : syracuseStep 20473397 = 1919381) B1919381
theorem B2131523 : Blo 1419529 2131523 := bstep (se 1 (by rfl) ⟨1598642, by rfl⟩ : syracuseStep 2131523 = 3197285) B3197285
theorem B1599043 : Blo 1419529 1599043 := bstep (se 1 (by rfl) ⟨1199282, by rfl⟩ : syracuseStep 1599043 = 2398565) B2398565
theorem B2131553 : Blo 1419529 2131553 := bstep (se 2 (by rfl) ⟨799332, by rfl⟩ : syracuseStep 2131553 = 1598665) B1598665
theorem B3196529 : Blo 1419529 3196529 := bstep (se 2 (by rfl) ⟨1198698, by rfl⟩ : syracuseStep 3196529 = 2397397) B2397397
theorem B2131571 : Blo 1419529 2131571 := bstep (se 1 (by rfl) ⟨1598678, by rfl⟩ : syracuseStep 2131571 = 3197357) B3197357
theorem B3196547 : Blo 1419529 3196547 := bstep (se 1 (by rfl) ⟨2397410, by rfl⟩ : syracuseStep 3196547 = 4794821) B4794821
theorem B2131601 : Blo 1419529 2131601 := bstep (se 2 (by rfl) ⟨799350, by rfl⟩ : syracuseStep 2131601 = 1598701) B1598701
theorem B2131619 : Blo 1419529 2131619 := bstep (se 1 (by rfl) ⟨1598714, by rfl⟩ : syracuseStep 2131619 = 3197429) B3197429
theorem B8095409 : Blo 1419529 8095409 := bstep (se 2 (by rfl) ⟨3035778, by rfl⟩ : syracuseStep 8095409 = 6071557) B6071557
theorem B1918657 : Blo 1419529 1918657 := bstep (se 2 (by rfl) ⟨719496, by rfl⟩ : syracuseStep 1918657 = 1438993) B1438993
theorem B2131649 : Blo 1419529 2131649 := bstep (se 2 (by rfl) ⟨799368, by rfl⟩ : syracuseStep 2131649 = 1598737) B1598737
theorem B4794065 : Blo 1419529 4794065 := bstep (se 2 (by rfl) ⟨1797774, by rfl⟩ : syracuseStep 4794065 = 3595549) B3595549
theorem B2131667 : Blo 1419529 2131667 := bstep (se 1 (by rfl) ⟨1598750, by rfl⟩ : syracuseStep 2131667 = 3197501) B3197501
theorem B1599187 : Blo 1419529 1599187 := bstep (se 1 (by rfl) ⟨1199390, by rfl⟩ : syracuseStep 1599187 = 2398781) B2398781
theorem B2131697 : Blo 1419529 2131697 := bstep (se 2 (by rfl) ⟨799386, by rfl⟩ : syracuseStep 2131697 = 1598773) B1598773
theorem B2131715 : Blo 1419529 2131715 := bstep (se 1 (by rfl) ⟨1598786, by rfl⟩ : syracuseStep 2131715 = 3197573) B3197573
theorem B2131745 : Blo 1419529 2131745 := bstep (se 2 (by rfl) ⟨799404, by rfl⟩ : syracuseStep 2131745 = 1598809) B1598809
theorem B2131763 : Blo 1419529 2131763 := bstep (se 1 (by rfl) ⟨1598822, by rfl⟩ : syracuseStep 2131763 = 3197645) B3197645
theorem B2131793 : Blo 1419529 2131793 := bstep (se 2 (by rfl) ⟨799422, by rfl⟩ : syracuseStep 2131793 = 1598845) B1598845
theorem B1517411 : Blo 1419529 1517411 := bstep (se 1 (by rfl) ⟨1138058, by rfl⟩ : syracuseStep 1517411 = 2276117) B2276117
theorem B2131811 : Blo 1419529 2131811 := bstep (se 1 (by rfl) ⟨1598858, by rfl⟩ : syracuseStep 2131811 = 3197717) B3197717
theorem B1705843 : Blo 1419529 1705843 := bstep (se 1 (by rfl) ⟨1279382, by rfl⟩ : syracuseStep 1705843 = 2558765) B2558765
theorem B2131841 : Blo 1419529 2131841 := bstep (se 2 (by rfl) ⟨799440, by rfl⟩ : syracuseStep 2131841 = 1598881) B1598881
theorem B3032977 : Blo 1419529 3032977 := bstep (se 2 (by rfl) ⟨1137366, by rfl⟩ : syracuseStep 3032977 = 2274733) B2274733
theorem B3196817 : Blo 1419529 3196817 := bstep (se 2 (by rfl) ⟨1198806, by rfl⟩ : syracuseStep 3196817 = 2397613) B2397613
theorem B2131859 : Blo 1419529 2131859 := bstep (se 1 (by rfl) ⟨1598894, by rfl⟩ : syracuseStep 2131859 = 3197789) B3197789
theorem B5392291 : Blo 1419529 5392291 := bstep (se 1 (by rfl) ⟨4044218, by rfl⟩ : syracuseStep 5392291 = 8088437) B8088437
theorem B3196835 : Blo 1419529 3196835 := bstep (se 1 (by rfl) ⟨2397626, by rfl⟩ : syracuseStep 3196835 = 4795253) B4795253
theorem B2131889 : Blo 1419529 2131889 := bstep (se 2 (by rfl) ⟨799458, by rfl⟩ : syracuseStep 2131889 = 1598917) B1598917
theorem B2131907 : Blo 1419529 2131907 := bstep (se 1 (by rfl) ⟨1598930, by rfl⟩ : syracuseStep 2131907 = 3197861) B3197861
theorem B2131937 : Blo 1419529 2131937 := bstep (se 2 (by rfl) ⟨799476, by rfl⟩ : syracuseStep 2131937 = 1598953) B1598953
theorem B1517539 : Blo 1419529 1517539 := bstep (se 1 (by rfl) ⟨1138154, by rfl⟩ : syracuseStep 1517539 = 2276309) B2276309
theorem B2131955 : Blo 1419529 2131955 := bstep (se 1 (by rfl) ⟨1598966, by rfl⟩ : syracuseStep 2131955 = 3197933) B3197933
theorem B6064141 : Blo 1419529 6064141 := bstep (se 3 (by rfl) ⟨1137026, by rfl⟩ : syracuseStep 6064141 = 2274053) B2274053
theorem B2131985 : Blo 1419529 2131985 := bstep (se 2 (by rfl) ⟨799494, by rfl⟩ : syracuseStep 2131985 = 1598989) B1598989
theorem B2132003 : Blo 1419529 2132003 := bstep (se 1 (by rfl) ⟨1599002, by rfl⟩ : syracuseStep 2132003 = 3198005) B3198005
theorem B7186481 : Blo 1419529 7186481 := bstep (se 2 (by rfl) ⟨2694930, by rfl⟩ : syracuseStep 7186481 = 5389861) B5389861
theorem B2132033 : Blo 1419529 2132033 := bstep (se 2 (by rfl) ⟨799512, by rfl⟩ : syracuseStep 2132033 = 1599025) B1599025
theorem B2132051 : Blo 1419529 2132051 := bstep (se 1 (by rfl) ⟨1599038, by rfl⟩ : syracuseStep 2132051 = 3198077) B3198077
theorem B2132081 : Blo 1419529 2132081 := bstep (se 2 (by rfl) ⟨799530, by rfl⟩ : syracuseStep 2132081 = 1599061) B1599061
theorem B2132099 : Blo 1419529 2132099 := bstep (se 1 (by rfl) ⟨1599074, by rfl⟩ : syracuseStep 2132099 = 3198149) B3198149
theorem B2132129 : Blo 1419529 2132129 := bstep (se 2 (by rfl) ⟨799548, by rfl⟩ : syracuseStep 2132129 = 1599097) B1599097
theorem B3197105 : Blo 1419529 3197105 := bstep (se 2 (by rfl) ⟨1198914, by rfl⟩ : syracuseStep 3197105 = 2397829) B2397829
theorem B2132147 : Blo 1419529 2132147 := bstep (se 1 (by rfl) ⟨1599110, by rfl⟩ : syracuseStep 2132147 = 3198221) B3198221
theorem B3197123 : Blo 1419529 3197123 := bstep (se 1 (by rfl) ⟨2397842, by rfl⟩ : syracuseStep 3197123 = 4795685) B4795685
theorem B9717965 : Blo 1419529 9717965 := bstep (se 3 (by rfl) ⟨1822118, by rfl⟩ : syracuseStep 9717965 = 3644237) B3644237
theorem B2132177 : Blo 1419529 2132177 := bstep (se 2 (by rfl) ⟨799566, by rfl⟩ : syracuseStep 2132177 = 1599133) B1599133
theorem B2132195 : Blo 1419529 2132195 := bstep (se 1 (by rfl) ⟨1599146, by rfl⟩ : syracuseStep 2132195 = 3198293) B3198293
theorem B4794605 : Blo 1419529 4794605 := bstep (se 3 (by rfl) ⟨898988, by rfl⟩ : syracuseStep 4794605 = 1797977) B1797977
theorem B2132225 : Blo 1419529 2132225 := bstep (se 2 (by rfl) ⟨799584, by rfl⟩ : syracuseStep 2132225 = 1599169) B1599169
theorem B2697475 : Blo 1419529 2697475 := bstep (se 1 (by rfl) ⟨2023106, by rfl⟩ : syracuseStep 2697475 = 4046213) B4046213
theorem B1419539 : Blo 1419529 1419539 := bstep (se 1 (by rfl) ⟨1064654, by rfl⟩ : syracuseStep 1419539 = 2129309) B2129309
theorem B2132243 : Blo 1419529 2132243 := bstep (se 1 (by rfl) ⟨1599182, by rfl⟩ : syracuseStep 2132243 = 3198365) B3198365
theorem B1419555 : Blo 1419529 1419555 := bstep (se 1 (by rfl) ⟨1064666, by rfl⟩ : syracuseStep 1419555 = 2129333) B2129333
theorem B4794659 : Blo 1419529 4794659 := bstep (se 1 (by rfl) ⟨3595994, by rfl⟩ : syracuseStep 4794659 = 7191989) B7191989
theorem B2132273 : Blo 1419529 2132273 := bstep (se 2 (by rfl) ⟨799602, by rfl⟩ : syracuseStep 2132273 = 1599205) B1599205
theorem B1419571 : Blo 1419529 1419571 := bstep (se 1 (by rfl) ⟨1064678, by rfl⟩ : syracuseStep 1419571 = 2129357) B2129357
theorem B1419587 : Blo 1419529 1419587 := bstep (se 1 (by rfl) ⟨1064690, by rfl⟩ : syracuseStep 1419587 = 2129381) B2129381
theorem B2132291 : Blo 1419529 2132291 := bstep (se 1 (by rfl) ⟨1599218, by rfl⟩ : syracuseStep 2132291 = 3198437) B3198437
theorem B1419603 : Blo 1419529 1419603 := bstep (se 1 (by rfl) ⟨1064702, by rfl⟩ : syracuseStep 1419603 = 2129405) B2129405
theorem B1419619 : Blo 1419529 1419619 := bstep (se 1 (by rfl) ⟨1064714, by rfl⟩ : syracuseStep 1419619 = 2129429) B2129429
theorem B6064483 : Blo 1419529 6064483 := bstep (se 1 (by rfl) ⟨4548362, by rfl⟩ : syracuseStep 6064483 = 9096725) B9096725
theorem B1419635 : Blo 1419529 1419635 := bstep (se 1 (by rfl) ⟨1064726, by rfl⟩ : syracuseStep 1419635 = 2129453) B2129453
theorem B1419651 : Blo 1419529 1419651 := bstep (se 1 (by rfl) ⟨1064738, by rfl⟩ : syracuseStep 1419651 = 2129477) B2129477
theorem B1419667 : Blo 1419529 1419667 := bstep (se 1 (by rfl) ⟨1064750, by rfl⟩ : syracuseStep 1419667 = 2129501) B2129501
theorem B1419683 : Blo 1419529 1419683 := bstep (se 1 (by rfl) ⟨1064762, by rfl⟩ : syracuseStep 1419683 = 2129525) B2129525
theorem B1419699 : Blo 1419529 1419699 := bstep (se 1 (by rfl) ⟨1064774, by rfl⟩ : syracuseStep 1419699 = 2129549) B2129549
theorem B1419715 : Blo 1419529 1419715 := bstep (se 1 (by rfl) ⟨1064786, by rfl⟩ : syracuseStep 1419715 = 2129573) B2129573
theorem B18196933 : Blo 1419529 18196933 := bstep (se 4 (by rfl) ⟨1705962, by rfl⟩ : syracuseStep 18196933 = 3411925) B3411925
theorem B2877905 : Blo 1419529 2877905 := bstep (se 2 (by rfl) ⟨1079214, by rfl⟩ : syracuseStep 2877905 = 2158429) B2158429
theorem B3197393 : Blo 1419529 3197393 := bstep (se 2 (by rfl) ⟨1199022, by rfl⟩ : syracuseStep 3197393 = 2398045) B2398045
theorem B1419731 : Blo 1419529 1419731 := bstep (se 1 (by rfl) ⟨1064798, by rfl⟩ : syracuseStep 1419731 = 2129597) B2129597
theorem B9095651 : Blo 1419529 9095651 := bstep (se 1 (by rfl) ⟨6821738, by rfl⟩ : syracuseStep 9095651 = 13643477) B13643477
theorem B1419747 : Blo 1419529 1419747 := bstep (se 1 (by rfl) ⟨1064810, by rfl⟩ : syracuseStep 1419747 = 2129621) B2129621
theorem B12470755 : Blo 1419529 12470755 := bstep (se 1 (by rfl) ⟨9353066, by rfl⟩ : syracuseStep 12470755 = 18706133) B18706133
theorem B3197411 : Blo 1419529 3197411 := bstep (se 1 (by rfl) ⟨2398058, by rfl⟩ : syracuseStep 3197411 = 4796117) B4796117
theorem B1419763 : Blo 1419529 1419763 := bstep (se 1 (by rfl) ⟨1064822, by rfl⟩ : syracuseStep 1419763 = 2129645) B2129645
theorem B1419779 : Blo 1419529 1419779 := bstep (se 1 (by rfl) ⟨1064834, by rfl⟩ : syracuseStep 1419779 = 2129669) B2129669
theorem B1419795 : Blo 1419529 1419795 := bstep (se 1 (by rfl) ⟨1064846, by rfl⟩ : syracuseStep 1419795 = 2129693) B2129693
theorem B1419811 : Blo 1419529 1419811 := bstep (se 1 (by rfl) ⟨1064858, by rfl⟩ : syracuseStep 1419811 = 2129717) B2129717
theorem B4794929 : Blo 1419529 4794929 := bstep (se 2 (by rfl) ⟨1798098, by rfl⟩ : syracuseStep 4794929 = 3596197) B3596197
theorem B1419827 : Blo 1419529 1419827 := bstep (se 1 (by rfl) ⟨1064870, by rfl⟩ : syracuseStep 1419827 = 2129741) B2129741
theorem B1419843 : Blo 1419529 1419843 := bstep (se 1 (by rfl) ⟨1064882, by rfl⟩ : syracuseStep 1419843 = 2129765) B2129765
theorem B1419859 : Blo 1419529 1419859 := bstep (se 1 (by rfl) ⟨1064894, by rfl⟩ : syracuseStep 1419859 = 2129789) B2129789
theorem B1419875 : Blo 1419529 1419875 := bstep (se 1 (by rfl) ⟨1064906, by rfl⟩ : syracuseStep 1419875 = 2129813) B2129813
theorem B1419891 : Blo 1419529 1419891 := bstep (se 1 (by rfl) ⟨1064918, by rfl⟩ : syracuseStep 1419891 = 2129837) B2129837
theorem B1419907 : Blo 1419529 1419907 := bstep (se 1 (by rfl) ⟨1064930, by rfl⟩ : syracuseStep 1419907 = 2129861) B2129861
theorem B1419923 : Blo 1419529 1419923 := bstep (se 1 (by rfl) ⟨1064942, by rfl⟩ : syracuseStep 1419923 = 2129885) B2129885
theorem B1419939 : Blo 1419529 1419939 := bstep (se 1 (by rfl) ⟨1064954, by rfl⟩ : syracuseStep 1419939 = 2129909) B2129909
theorem B1419955 : Blo 1419529 1419955 := bstep (se 1 (by rfl) ⟨1064966, by rfl⟩ : syracuseStep 1419955 = 2129933) B2129933
theorem B1419971 : Blo 1419529 1419971 := bstep (se 1 (by rfl) ⟨1064978, by rfl⟩ : syracuseStep 1419971 = 2129957) B2129957
theorem B3074755 : Blo 1419529 3074755 := bstep (se 1 (by rfl) ⟨2306066, by rfl⟩ : syracuseStep 3074755 = 4612133) B4612133
theorem B2697923 : Blo 1419529 2697923 := bstep (se 1 (by rfl) ⟨2023442, by rfl⟩ : syracuseStep 2697923 = 4046885) B4046885
theorem B1419987 : Blo 1419529 1419987 := bstep (se 1 (by rfl) ⟨1064990, by rfl⟩ : syracuseStep 1419987 = 2129981) B2129981
theorem B1420003 : Blo 1419529 1420003 := bstep (se 1 (by rfl) ⟨1065002, by rfl⟩ : syracuseStep 1420003 = 2130005) B2130005
theorem B19712753 : Blo 1419529 19712753 := bstep (se 2 (by rfl) ⟨7392282, by rfl⟩ : syracuseStep 19712753 = 14784565) B14784565
theorem B3197681 : Blo 1419529 3197681 := bstep (se 2 (by rfl) ⟨1199130, by rfl⟩ : syracuseStep 3197681 = 2398261) B2398261
theorem B1420019 : Blo 1419529 1420019 := bstep (se 1 (by rfl) ⟨1065014, by rfl⟩ : syracuseStep 1420019 = 2130029) B2130029
theorem B1420035 : Blo 1419529 1420035 := bstep (se 1 (by rfl) ⟨1065026, by rfl⟩ : syracuseStep 1420035 = 2130053) B2130053
theorem B3197699 : Blo 1419529 3197699 := bstep (se 1 (by rfl) ⟨2398274, by rfl⟩ : syracuseStep 3197699 = 4796549) B4796549
theorem B1420051 : Blo 1419529 1420051 := bstep (se 1 (by rfl) ⟨1065038, by rfl⟩ : syracuseStep 1420051 = 2130077) B2130077
theorem B1796899 : Blo 1419529 1796899 := bstep (se 1 (by rfl) ⟨1347674, by rfl⟩ : syracuseStep 1796899 = 2695349) B2695349
theorem B1420067 : Blo 1419529 1420067 := bstep (se 1 (by rfl) ⟨1065050, by rfl⟩ : syracuseStep 1420067 = 2130101) B2130101
theorem B1420083 : Blo 1419529 1420083 := bstep (se 1 (by rfl) ⟨1065062, by rfl⟩ : syracuseStep 1420083 = 2130125) B2130125
theorem B1420099 : Blo 1419529 1420099 := bstep (se 1 (by rfl) ⟨1065074, by rfl⟩ : syracuseStep 1420099 = 2130149) B2130149
theorem B1420115 : Blo 1419529 1420115 := bstep (se 1 (by rfl) ⟨1065086, by rfl⟩ : syracuseStep 1420115 = 2130173) B2130173
theorem B1420131 : Blo 1419529 1420131 := bstep (se 1 (by rfl) ⟨1065098, by rfl⟩ : syracuseStep 1420131 = 2130197) B2130197
theorem B5761891 : Blo 1419529 5761891 := bstep (se 1 (by rfl) ⟨4321418, by rfl⟩ : syracuseStep 5761891 = 8642837) B8642837
theorem B1420147 : Blo 1419529 1420147 := bstep (se 1 (by rfl) ⟨1065110, by rfl⟩ : syracuseStep 1420147 = 2130221) B2130221
theorem B1796995 : Blo 1419529 1796995 := bstep (se 1 (by rfl) ⟨1347746, by rfl⟩ : syracuseStep 1796995 = 2695493) B2695493
theorem B1420163 : Blo 1419529 1420163 := bstep (se 1 (by rfl) ⟨1065122, by rfl⟩ : syracuseStep 1420163 = 2130245) B2130245
theorem B1420179 : Blo 1419529 1420179 := bstep (se 1 (by rfl) ⟨1065134, by rfl⟩ : syracuseStep 1420179 = 2130269) B2130269
theorem B1420195 : Blo 1419529 1420195 := bstep (se 1 (by rfl) ⟨1065146, by rfl⟩ : syracuseStep 1420195 = 2130293) B2130293
theorem B3034019 : Blo 1419529 3034019 := bstep (se 1 (by rfl) ⟨2275514, by rfl⟩ : syracuseStep 3034019 = 4551029) B4551029
theorem B1420211 : Blo 1419529 1420211 := bstep (se 1 (by rfl) ⟨1065158, by rfl⟩ : syracuseStep 1420211 = 2130317) B2130317
theorem B1420227 : Blo 1419529 1420227 := bstep (se 1 (by rfl) ⟨1065170, by rfl⟩ : syracuseStep 1420227 = 2130341) B2130341
theorem B1420243 : Blo 1419529 1420243 := bstep (se 1 (by rfl) ⟨1065182, by rfl⟩ : syracuseStep 1420243 = 2130365) B2130365
theorem B1846243 : Blo 1419529 1846243 := bstep (se 1 (by rfl) ⟨1384682, by rfl⟩ : syracuseStep 1846243 = 2769365) B2769365
theorem B1420259 : Blo 1419529 1420259 := bstep (se 1 (by rfl) ⟨1065194, by rfl⟩ : syracuseStep 1420259 = 2130389) B2130389
theorem B10243043 : Blo 1419529 10243043 := bstep (se 1 (by rfl) ⟨7682282, by rfl⟩ : syracuseStep 10243043 = 15364565) B15364565
theorem B2698211 : Blo 1419529 2698211 := bstep (se 1 (by rfl) ⟨2023658, by rfl⟩ : syracuseStep 2698211 = 4047317) B4047317
theorem B1420275 : Blo 1419529 1420275 := bstep (se 1 (by rfl) ⟨1065206, by rfl⟩ : syracuseStep 1420275 = 2130413) B2130413
theorem B1420291 : Blo 1419529 1420291 := bstep (se 1 (by rfl) ⟨1065218, by rfl⟩ : syracuseStep 1420291 = 2130437) B2130437
theorem B3197969 : Blo 1419529 3197969 := bstep (se 2 (by rfl) ⟨1199238, by rfl⟩ : syracuseStep 3197969 = 2398477) B2398477
theorem B1420307 : Blo 1419529 1420307 := bstep (se 1 (by rfl) ⟨1065230, by rfl⟩ : syracuseStep 1420307 = 2130461) B2130461
theorem B1420323 : Blo 1419529 1420323 := bstep (se 1 (by rfl) ⟨1065242, by rfl⟩ : syracuseStep 1420323 = 2130485) B2130485
theorem B3197987 : Blo 1419529 3197987 := bstep (se 1 (by rfl) ⟨2398490, by rfl⟩ : syracuseStep 3197987 = 4796981) B4796981
theorem B1420339 : Blo 1419529 1420339 := bstep (se 1 (by rfl) ⟨1065254, by rfl⟩ : syracuseStep 1420339 = 2130509) B2130509
theorem B46107701 : Blo 1419529 46107701 := bstep (se 5 (by rfl) ⟨2161298, by rfl⟩ : syracuseStep 46107701 = 4322597) B4322597
theorem B1420355 : Blo 1419529 1420355 := bstep (se 1 (by rfl) ⟨1065266, by rfl⟩ : syracuseStep 1420355 = 2130533) B2130533
theorem B16182341 : Blo 1419529 16182341 := bstep (se 4 (by rfl) ⟨1517094, by rfl⟩ : syracuseStep 16182341 = 3034189) B3034189
theorem B4795469 : Blo 1419529 4795469 := bstep (se 3 (by rfl) ⟨899150, by rfl⟩ : syracuseStep 4795469 = 1798301) B1798301
theorem B1420371 : Blo 1419529 1420371 := bstep (se 1 (by rfl) ⟨1065278, by rfl⟩ : syracuseStep 1420371 = 2130557) B2130557
theorem B1420387 : Blo 1419529 1420387 := bstep (se 1 (by rfl) ⟨1065290, by rfl⟩ : syracuseStep 1420387 = 2130581) B2130581
theorem B1420403 : Blo 1419529 1420403 := bstep (se 1 (by rfl) ⟨1065302, by rfl⟩ : syracuseStep 1420403 = 2130605) B2130605
theorem B1420419 : Blo 1419529 1420419 := bstep (se 1 (by rfl) ⟨1065314, by rfl⟩ : syracuseStep 1420419 = 2130629) B2130629
theorem B4795523 : Blo 1419529 4795523 := bstep (se 1 (by rfl) ⟨3596642, by rfl⟩ : syracuseStep 4795523 = 7193285) B7193285
theorem B1420435 : Blo 1419529 1420435 := bstep (se 1 (by rfl) ⟨1065326, by rfl⟩ : syracuseStep 1420435 = 2130653) B2130653
theorem B1420451 : Blo 1419529 1420451 := bstep (se 1 (by rfl) ⟨1065338, by rfl⟩ : syracuseStep 1420451 = 2130677) B2130677
theorem B1420467 : Blo 1419529 1420467 := bstep (se 1 (by rfl) ⟨1065350, by rfl⟩ : syracuseStep 1420467 = 2130701) B2130701
theorem B1420483 : Blo 1419529 1420483 := bstep (se 1 (by rfl) ⟨1065362, by rfl⟩ : syracuseStep 1420483 = 2130725) B2130725
theorem B1420499 : Blo 1419529 1420499 := bstep (se 1 (by rfl) ⟨1065374, by rfl⟩ : syracuseStep 1420499 = 2130749) B2130749
theorem B1420515 : Blo 1419529 1420515 := bstep (se 1 (by rfl) ⟨1065386, by rfl⟩ : syracuseStep 1420515 = 2130773) B2130773
theorem B1420531 : Blo 1419529 1420531 := bstep (se 1 (by rfl) ⟨1065398, by rfl⟩ : syracuseStep 1420531 = 2130797) B2130797
theorem B1420547 : Blo 1419529 1420547 := bstep (se 1 (by rfl) ⟨1065410, by rfl⟩ : syracuseStep 1420547 = 2130821) B2130821
theorem B8760581 : Blo 1419529 8760581 := bstep (se 4 (by rfl) ⟨821304, by rfl⟩ : syracuseStep 8760581 = 1642609) B1642609
theorem B1420563 : Blo 1419529 1420563 := bstep (se 1 (by rfl) ⟨1065422, by rfl⟩ : syracuseStep 1420563 = 2130845) B2130845
theorem B1420579 : Blo 1419529 1420579 := bstep (se 1 (by rfl) ⟨1065434, by rfl⟩ : syracuseStep 1420579 = 2130869) B2130869
theorem B3198257 : Blo 1419529 3198257 := bstep (se 2 (by rfl) ⟨1199346, by rfl⟩ : syracuseStep 3198257 = 2398693) B2398693
theorem B1420595 : Blo 1419529 1420595 := bstep (se 1 (by rfl) ⟨1065446, by rfl⟩ : syracuseStep 1420595 = 2130893) B2130893
theorem B1420611 : Blo 1419529 1420611 := bstep (se 1 (by rfl) ⟨1065458, by rfl⟩ : syracuseStep 1420611 = 2130917) B2130917
theorem B3198275 : Blo 1419529 3198275 := bstep (se 1 (by rfl) ⟨2398706, by rfl⟩ : syracuseStep 3198275 = 4797413) B4797413
theorem B11521349 : Blo 1419529 11521349 := bstep (se 4 (by rfl) ⟨1080126, by rfl⟩ : syracuseStep 11521349 = 2160253) B2160253
theorem B1420627 : Blo 1419529 1420627 := bstep (se 1 (by rfl) ⟨1065470, by rfl⟩ : syracuseStep 1420627 = 2130941) B2130941
theorem B1420643 : Blo 1419529 1420643 := bstep (se 1 (by rfl) ⟨1065482, by rfl⟩ : syracuseStep 1420643 = 2130965) B2130965
theorem B3460465 : Blo 1419529 3460465 := bstep (se 2 (by rfl) ⟨1297674, by rfl⟩ : syracuseStep 3460465 = 2595349) B2595349
theorem B2395507 : Blo 1419529 2395507 := bstep (se 1 (by rfl) ⟨1796630, by rfl⟩ : syracuseStep 2395507 = 3593261) B3593261
theorem B1797491 : Blo 1419529 1797491 := bstep (se 1 (by rfl) ⟨1348118, by rfl⟩ : syracuseStep 1797491 = 2696237) B2696237
theorem B1420659 : Blo 1419529 1420659 := bstep (se 1 (by rfl) ⟨1065494, by rfl⟩ : syracuseStep 1420659 = 2130989) B2130989
theorem B1420675 : Blo 1419529 1420675 := bstep (se 1 (by rfl) ⟨1065506, by rfl⟩ : syracuseStep 1420675 = 2131013) B2131013
theorem B2559377 : Blo 1419529 2559377 := bstep (se 2 (by rfl) ⟨959766, by rfl⟩ : syracuseStep 2559377 = 1919533) B1919533
theorem B4795793 : Blo 1419529 4795793 := bstep (se 2 (by rfl) ⟨1798422, by rfl⟩ : syracuseStep 4795793 = 3596845) B3596845
theorem B1420691 : Blo 1419529 1420691 := bstep (se 1 (by rfl) ⟨1065518, by rfl⟩ : syracuseStep 1420691 = 2131037) B2131037
theorem B1420707 : Blo 1419529 1420707 := bstep (se 1 (by rfl) ⟨1065530, by rfl⟩ : syracuseStep 1420707 = 2131061) B2131061
theorem B3034531 : Blo 1419529 3034531 := bstep (se 1 (by rfl) ⟨2275898, by rfl⟩ : syracuseStep 3034531 = 4551797) B4551797
theorem B1641907 : Blo 1419529 1641907 := bstep (se 1 (by rfl) ⟨1231430, by rfl⟩ : syracuseStep 1641907 = 2462861) B2462861
theorem B1420723 : Blo 1419529 1420723 := bstep (se 1 (by rfl) ⟨1065542, by rfl⟩ : syracuseStep 1420723 = 2131085) B2131085
theorem B1420739 : Blo 1419529 1420739 := bstep (se 1 (by rfl) ⟨1065554, by rfl⟩ : syracuseStep 1420739 = 2131109) B2131109
theorem B1420755 : Blo 1419529 1420755 := bstep (se 1 (by rfl) ⟨1065566, by rfl⟩ : syracuseStep 1420755 = 2131133) B2131133
theorem B7187939 : Blo 1419529 7187939 := bstep (se 1 (by rfl) ⟨5390954, by rfl⟩ : syracuseStep 7187939 = 10781909) B10781909
theorem B1420771 : Blo 1419529 1420771 := bstep (se 1 (by rfl) ⟨1065578, by rfl⟩ : syracuseStep 1420771 = 2131157) B2131157
theorem B4861421 : Blo 1419529 4861421 := bstep (se 3 (by rfl) ⟨911516, by rfl⟩ : syracuseStep 4861421 = 1823033) B1823033
theorem B1420787 : Blo 1419529 1420787 := bstep (se 1 (by rfl) ⟨1065590, by rfl⟩ : syracuseStep 1420787 = 2131181) B2131181
theorem B2395649 : Blo 1419529 2395649 := bstep (se 2 (by rfl) ⟨898368, by rfl⟩ : syracuseStep 2395649 = 1796737) B1796737
theorem B1420803 : Blo 1419529 1420803 := bstep (se 1 (by rfl) ⟨1065602, by rfl⟩ : syracuseStep 1420803 = 2131205) B2131205
theorem B1420819 : Blo 1419529 1420819 := bstep (se 1 (by rfl) ⟨1065614, by rfl⟩ : syracuseStep 1420819 = 2131229) B2131229
theorem B1707539 : Blo 1419529 1707539 := bstep (se 1 (by rfl) ⟨1280654, by rfl⟩ : syracuseStep 1707539 = 2561309) B2561309
theorem B2051617 : Blo 1419529 2051617 := bstep (se 2 (by rfl) ⟨769356, by rfl⟩ : syracuseStep 2051617 = 1538713) B1538713
theorem B1420835 : Blo 1419529 1420835 := bstep (se 1 (by rfl) ⟨1065626, by rfl⟩ : syracuseStep 1420835 = 2131253) B2131253
theorem B1420851 : Blo 1419529 1420851 := bstep (se 1 (by rfl) ⟨1065638, by rfl⟩ : syracuseStep 1420851 = 2131277) B2131277
theorem B1420867 : Blo 1419529 1420867 := bstep (se 1 (by rfl) ⟨1065650, by rfl⟩ : syracuseStep 1420867 = 2131301) B2131301
theorem B1420883 : Blo 1419529 1420883 := bstep (se 1 (by rfl) ⟨1065662, by rfl⟩ : syracuseStep 1420883 = 2131325) B2131325
theorem B1420899 : Blo 1419529 1420899 := bstep (se 1 (by rfl) ⟨1065674, by rfl⟩ : syracuseStep 1420899 = 2131349) B2131349
theorem B16191089 : Blo 1419529 16191089 := bstep (se 2 (by rfl) ⟨6071658, by rfl⟩ : syracuseStep 16191089 = 12143317) B12143317
theorem B1420915 : Blo 1419529 1420915 := bstep (se 1 (by rfl) ⟨1065686, by rfl⟩ : syracuseStep 1420915 = 2131373) B2131373
theorem B2395777 : Blo 1419529 2395777 := bstep (se 2 (by rfl) ⟨898416, by rfl⟩ : syracuseStep 2395777 = 1796833) B1796833
theorem B1420931 : Blo 1419529 1420931 := bstep (se 1 (by rfl) ⟨1065698, by rfl⟩ : syracuseStep 1420931 = 2131397) B2131397
theorem B15560333 : Blo 1419529 15560333 := bstep (se 3 (by rfl) ⟨2917562, by rfl⟩ : syracuseStep 15560333 = 5835125) B5835125
theorem B1420947 : Blo 1419529 1420947 := bstep (se 1 (by rfl) ⟨1065710, by rfl⟩ : syracuseStep 1420947 = 2131421) B2131421
theorem B2395811 : Blo 1419529 2395811 := bstep (se 1 (by rfl) ⟨1796858, by rfl⟩ : syracuseStep 2395811 = 3593717) B3593717
theorem B1420963 : Blo 1419529 1420963 := bstep (se 1 (by rfl) ⟨1065722, by rfl⟩ : syracuseStep 1420963 = 2131445) B2131445
theorem B9719473 : Blo 1419529 9719473 := bstep (se 2 (by rfl) ⟨3644802, by rfl⟩ : syracuseStep 9719473 = 7289605) B7289605
theorem B1420979 : Blo 1419529 1420979 := bstep (se 1 (by rfl) ⟨1065734, by rfl⟩ : syracuseStep 1420979 = 2131469) B2131469
theorem B1420995 : Blo 1419529 1420995 := bstep (se 1 (by rfl) ⟨1065746, by rfl⟩ : syracuseStep 1420995 = 2131493) B2131493
theorem B1421011 : Blo 1419529 1421011 := bstep (se 1 (by rfl) ⟨1065758, by rfl⟩ : syracuseStep 1421011 = 2131517) B2131517
theorem B1421027 : Blo 1419529 1421027 := bstep (se 1 (by rfl) ⟨1065770, by rfl⟩ : syracuseStep 1421027 = 2131541) B2131541
theorem B1421043 : Blo 1419529 1421043 := bstep (se 1 (by rfl) ⟨1065782, by rfl⟩ : syracuseStep 1421043 = 2131565) B2131565
theorem B3411715 : Blo 1419529 3411715 := bstep (se 1 (by rfl) ⟨2558786, by rfl⟩ : syracuseStep 3411715 = 5117573) B5117573
theorem B1421059 : Blo 1419529 1421059 := bstep (se 1 (by rfl) ⟨1065794, by rfl⟩ : syracuseStep 1421059 = 2131589) B2131589
theorem B4550413 : Blo 1419529 4550413 := bstep (se 3 (by rfl) ⟨853202, by rfl⟩ : syracuseStep 4550413 = 1706405) B1706405
theorem B1421075 : Blo 1419529 1421075 := bstep (se 1 (by rfl) ⟨1065806, by rfl⟩ : syracuseStep 1421075 = 2131613) B2131613
theorem B2395939 : Blo 1419529 2395939 := bstep (se 1 (by rfl) ⟨1796954, by rfl⟩ : syracuseStep 2395939 = 3593909) B3593909
theorem B1421091 : Blo 1419529 1421091 := bstep (se 1 (by rfl) ⟨1065818, by rfl⟩ : syracuseStep 1421091 = 2131637) B2131637
theorem B1421107 : Blo 1419529 1421107 := bstep (se 1 (by rfl) ⟨1065830, by rfl⟩ : syracuseStep 1421107 = 2131661) B2131661
theorem B1421123 : Blo 1419529 1421123 := bstep (se 1 (by rfl) ⟨1065842, by rfl⟩ : syracuseStep 1421123 = 2131685) B2131685
theorem B1421139 : Blo 1419529 1421139 := bstep (se 1 (by rfl) ⟨1065854, by rfl⟩ : syracuseStep 1421139 = 2131709) B2131709
theorem B3411811 : Blo 1419529 3411811 := bstep (se 1 (by rfl) ⟨2558858, by rfl⟩ : syracuseStep 3411811 = 5117717) B5117717
theorem B3239779 : Blo 1419529 3239779 := bstep (se 1 (by rfl) ⟨2429834, by rfl⟩ : syracuseStep 3239779 = 4859669) B4859669
theorem B1421155 : Blo 1419529 1421155 := bstep (se 1 (by rfl) ⟨1065866, by rfl⟩ : syracuseStep 1421155 = 2131733) B2131733
theorem B1421171 : Blo 1419529 1421171 := bstep (se 1 (by rfl) ⟨1065878, by rfl⟩ : syracuseStep 1421171 = 2131757) B2131757
theorem B1421187 : Blo 1419529 1421187 := bstep (se 1 (by rfl) ⟨1065890, by rfl⟩ : syracuseStep 1421187 = 2131781) B2131781
theorem B2461585 : Blo 1419529 2461585 := bstep (se 2 (by rfl) ⟨923094, by rfl⟩ : syracuseStep 2461585 = 1846189) B1846189
theorem B1421203 : Blo 1419529 1421203 := bstep (se 1 (by rfl) ⟨1065902, by rfl⟩ : syracuseStep 1421203 = 2131805) B2131805
theorem B1421219 : Blo 1419529 1421219 := bstep (se 1 (by rfl) ⟨1065914, by rfl⟩ : syracuseStep 1421219 = 2131829) B2131829
theorem B4796333 : Blo 1419529 4796333 := bstep (se 3 (by rfl) ⟨899312, by rfl⟩ : syracuseStep 4796333 = 1798625) B1798625
theorem B2396081 : Blo 1419529 2396081 := bstep (se 2 (by rfl) ⟨898530, by rfl⟩ : syracuseStep 2396081 = 1797061) B1797061
theorem B1421235 : Blo 1419529 1421235 := bstep (se 1 (by rfl) ⟨1065926, by rfl⟩ : syracuseStep 1421235 = 2131853) B2131853
theorem B1421251 : Blo 1419529 1421251 := bstep (se 1 (by rfl) ⟨1065938, by rfl⟩ : syracuseStep 1421251 = 2131877) B2131877
theorem B1421267 : Blo 1419529 1421267 := bstep (se 1 (by rfl) ⟨1065950, by rfl⟩ : syracuseStep 1421267 = 2131901) B2131901
theorem B4796387 : Blo 1419529 4796387 := bstep (se 1 (by rfl) ⟨3597290, by rfl⟩ : syracuseStep 4796387 = 7194581) B7194581
theorem B1421283 : Blo 1419529 1421283 := bstep (se 1 (by rfl) ⟨1065962, by rfl⟩ : syracuseStep 1421283 = 2131925) B2131925
theorem B1421299 : Blo 1419529 1421299 := bstep (se 1 (by rfl) ⟨1065974, by rfl⟩ : syracuseStep 1421299 = 2131949) B2131949
theorem B1421315 : Blo 1419529 1421315 := bstep (se 1 (by rfl) ⟨1065986, by rfl⟩ : syracuseStep 1421315 = 2131973) B2131973
theorem B4550669 : Blo 1419529 4550669 := bstep (se 3 (by rfl) ⟨853250, by rfl⟩ : syracuseStep 4550669 = 1706501) B1706501
theorem B1421331 : Blo 1419529 1421331 := bstep (se 1 (by rfl) ⟨1065998, by rfl⟩ : syracuseStep 1421331 = 2131997) B2131997
theorem B3412003 : Blo 1419529 3412003 := bstep (se 1 (by rfl) ⟨2559002, by rfl⟩ : syracuseStep 3412003 = 5118005) B5118005
theorem B1421347 : Blo 1419529 1421347 := bstep (se 1 (by rfl) ⟨1066010, by rfl⟩ : syracuseStep 1421347 = 2132021) B2132021
theorem B2396209 : Blo 1419529 2396209 := bstep (se 2 (by rfl) ⟨898578, by rfl⟩ : syracuseStep 2396209 = 1797157) B1797157
theorem B1798195 : Blo 1419529 1798195 := bstep (se 1 (by rfl) ⟨1348646, by rfl⟩ : syracuseStep 1798195 = 2697293) B2697293
theorem B1822771 : Blo 1419529 1822771 := bstep (se 1 (by rfl) ⟨1367078, by rfl⟩ : syracuseStep 1822771 = 2734157) B2734157
theorem B1421363 : Blo 1419529 1421363 := bstep (se 1 (by rfl) ⟨1066022, by rfl⟩ : syracuseStep 1421363 = 2132045) B2132045
theorem B1421379 : Blo 1419529 1421379 := bstep (se 1 (by rfl) ⟨1066034, by rfl⟩ : syracuseStep 1421379 = 2132069) B2132069
theorem B5394509 : Blo 1419529 5394509 := bstep (se 3 (by rfl) ⟨1011470, by rfl⟩ : syracuseStep 5394509 = 2022941) B2022941
theorem B6484045 : Blo 1419529 6484045 := bstep (se 3 (by rfl) ⟨1215758, by rfl⟩ : syracuseStep 6484045 = 2431517) B2431517
theorem B2396243 : Blo 1419529 2396243 := bstep (se 1 (by rfl) ⟨1797182, by rfl⟩ : syracuseStep 2396243 = 3594365) B3594365
theorem B1421395 : Blo 1419529 1421395 := bstep (se 1 (by rfl) ⟨1066046, by rfl⟩ : syracuseStep 1421395 = 2132093) B2132093
theorem B1421411 : Blo 1419529 1421411 := bstep (se 1 (by rfl) ⟨1066058, by rfl⟩ : syracuseStep 1421411 = 2132117) B2132117
theorem B3035249 : Blo 1419529 3035249 := bstep (se 2 (by rfl) ⟨1138218, by rfl⟩ : syracuseStep 3035249 = 2276437) B2276437
theorem B1421427 : Blo 1419529 1421427 := bstep (se 1 (by rfl) ⟨1066070, by rfl⟩ : syracuseStep 1421427 = 2132141) B2132141
theorem B1421443 : Blo 1419529 1421443 := bstep (se 1 (by rfl) ⟨1066082, by rfl⟩ : syracuseStep 1421443 = 2132165) B2132165
theorem B1798291 : Blo 1419529 1798291 := bstep (se 1 (by rfl) ⟨1348718, by rfl⟩ : syracuseStep 1798291 = 2697437) B2697437
theorem B1421459 : Blo 1419529 1421459 := bstep (se 1 (by rfl) ⟨1066094, by rfl⟩ : syracuseStep 1421459 = 2132189) B2132189
theorem B1421475 : Blo 1419529 1421475 := bstep (se 1 (by rfl) ⟨1066106, by rfl⟩ : syracuseStep 1421475 = 2132213) B2132213
theorem B1421491 : Blo 1419529 1421491 := bstep (se 1 (by rfl) ⟨1066118, by rfl⟩ : syracuseStep 1421491 = 2132237) B2132237
theorem B1421507 : Blo 1419529 1421507 := bstep (se 1 (by rfl) ⟨1066130, by rfl⟩ : syracuseStep 1421507 = 2132261) B2132261
theorem B2396371 : Blo 1419529 2396371 := bstep (se 1 (by rfl) ⟨1797278, by rfl⟩ : syracuseStep 2396371 = 3594557) B3594557
theorem B1421523 : Blo 1419529 1421523 := bstep (se 1 (by rfl) ⟨1066142, by rfl⟩ : syracuseStep 1421523 = 2132285) B2132285
theorem B4796657 : Blo 1419529 4796657 := bstep (se 2 (by rfl) ⟨1798746, by rfl⟩ : syracuseStep 4796657 = 3597493) B3597493
theorem B7188749 : Blo 1419529 7188749 := bstep (se 3 (by rfl) ⟨1347890, by rfl⟩ : syracuseStep 7188749 = 2695781) B2695781
theorem B2158915 : Blo 1419529 2158915 := bstep (se 1 (by rfl) ⟨1619186, by rfl⟩ : syracuseStep 2158915 = 3238373) B3238373
theorem B2396513 : Blo 1419529 2396513 := bstep (se 2 (by rfl) ⟨898692, by rfl⟩ : syracuseStep 2396513 = 1797385) B1797385
theorem B4043171 : Blo 1419529 4043171 := bstep (se 1 (by rfl) ⟨3032378, by rfl⟩ : syracuseStep 4043171 = 6064757) B6064757
theorem B2396641 : Blo 1419529 2396641 := bstep (se 2 (by rfl) ⟨898740, by rfl⟩ : syracuseStep 2396641 = 1797481) B1797481
theorem B2396675 : Blo 1419529 2396675 := bstep (se 1 (by rfl) ⟨1797506, by rfl⟩ : syracuseStep 2396675 = 3595013) B3595013
theorem B2159153 : Blo 1419529 2159153 := bstep (se 2 (by rfl) ⟨809682, by rfl⟩ : syracuseStep 2159153 = 1619365) B1619365
theorem B2396803 : Blo 1419529 2396803 := bstep (se 1 (by rfl) ⟨1797602, by rfl⟩ : syracuseStep 2396803 = 3595205) B3595205
theorem B1798787 : Blo 1419529 1798787 := bstep (se 1 (by rfl) ⟨1349090, by rfl⟩ : syracuseStep 1798787 = 2698181) B2698181
theorem B13652621 : Blo 1419529 13652621 := bstep (se 3 (by rfl) ⟨2559866, by rfl⟩ : syracuseStep 13652621 = 5119733) B5119733
theorem B4797197 : Blo 1419529 4797197 := bstep (se 3 (by rfl) ⟨899474, by rfl⟩ : syracuseStep 4797197 = 1798949) B1798949
theorem B2396945 : Blo 1419529 2396945 := bstep (se 2 (by rfl) ⟨898854, by rfl⟩ : syracuseStep 2396945 = 1797709) B1797709
theorem B35517205 : Blo 1419529 35517205 := bstep (se 6 (by rfl) ⟨832434, by rfl⟩ : syracuseStep 35517205 = 1664869) B1664869
theorem B4797251 : Blo 1419529 4797251 := bstep (se 1 (by rfl) ⟨3597938, by rfl⟩ : syracuseStep 4797251 = 7195877) B7195877
theorem B2274131 : Blo 1419529 2274131 := bstep (se 1 (by rfl) ⟨1705598, by rfl⟩ : syracuseStep 2274131 = 3411197) B3411197
theorem B2397073 : Blo 1419529 2397073 := bstep (se 2 (by rfl) ⟨898902, by rfl⟩ : syracuseStep 2397073 = 1797805) B1797805
theorem B4158353 : Blo 1419529 4158353 := bstep (se 2 (by rfl) ⟨1559382, by rfl⟩ : syracuseStep 4158353 = 3118765) B3118765
theorem B2397107 : Blo 1419529 2397107 := bstep (se 1 (by rfl) ⟨1797830, by rfl⟩ : syracuseStep 2397107 = 3595661) B3595661
theorem B3412945 : Blo 1419529 3412945 := bstep (se 2 (by rfl) ⟨1279854, by rfl⟩ : syracuseStep 3412945 = 2559709) B2559709
theorem B2274355 : Blo 1419529 2274355 := bstep (se 1 (by rfl) ⟨1705766, by rfl⟩ : syracuseStep 2274355 = 3411533) B3411533
theorem B2397235 : Blo 1419529 2397235 := bstep (se 1 (by rfl) ⟨1797926, by rfl⟩ : syracuseStep 2397235 = 3595853) B3595853
theorem B4797521 : Blo 1419529 4797521 := bstep (se 2 (by rfl) ⟨1799070, by rfl⟩ : syracuseStep 4797521 = 3598141) B3598141
theorem B3593393 : Blo 1419529 3593393 := bstep (se 2 (by rfl) ⟨1347522, by rfl⟩ : syracuseStep 3593393 = 2695045) B2695045
theorem B2397377 : Blo 1419529 2397377 := bstep (se 2 (by rfl) ⟨899016, by rfl⟩ : syracuseStep 2397377 = 1798033) B1798033
theorem B3839185 : Blo 1419529 3839185 := bstep (se 2 (by rfl) ⟨1439694, by rfl⟩ : syracuseStep 3839185 = 2879389) B2879389
theorem B3593443 : Blo 1419529 3593443 := bstep (se 1 (by rfl) ⟨2695082, by rfl⟩ : syracuseStep 3593443 = 5390165) B5390165
theorem B11515121 : Blo 1419529 11515121 := bstep (se 2 (by rfl) ⟨4318170, by rfl⟩ : syracuseStep 11515121 = 8636341) B8636341
theorem B2397505 : Blo 1419529 2397505 := bstep (se 2 (by rfl) ⟨899064, by rfl⟩ : syracuseStep 2397505 = 1798129) B1798129
theorem B2397539 : Blo 1419529 2397539 := bstep (se 1 (by rfl) ⟨1798154, by rfl⟩ : syracuseStep 2397539 = 3596309) B3596309
theorem B3593585 : Blo 1419529 3593585 := bstep (se 2 (by rfl) ⟨1347594, by rfl⟩ : syracuseStep 3593585 = 2695189) B2695189
theorem B8639941 : Blo 1419529 8639941 := bstep (se 4 (by rfl) ⟨809994, by rfl⟩ : syracuseStep 8639941 = 1619989) B1619989
theorem B2397667 : Blo 1419529 2397667 := bstep (se 1 (by rfl) ⟨1798250, by rfl⟩ : syracuseStep 2397667 = 3596501) B3596501
theorem B4101617 : Blo 1419529 4101617 := bstep (se 2 (by rfl) ⟨1538106, by rfl⟩ : syracuseStep 4101617 = 3076213) B3076213
theorem B4552195 : Blo 1419529 4552195 := bstep (se 1 (by rfl) ⟨3414146, by rfl⟩ : syracuseStep 4552195 = 6828293) B6828293
theorem B9229859 : Blo 1419529 9229859 := bstep (se 1 (by rfl) ⟨6922394, by rfl⟩ : syracuseStep 9229859 = 13844789) B13844789
theorem B4044401 : Blo 1419529 4044401 := bstep (se 2 (by rfl) ⟨1516650, by rfl⟩ : syracuseStep 4044401 = 3033301) B3033301
theorem B2397809 : Blo 1419529 2397809 := bstep (se 2 (by rfl) ⟨899178, by rfl⟩ : syracuseStep 2397809 = 1798357) B1798357
theorem B2397937 : Blo 1419529 2397937 := bstep (se 2 (by rfl) ⟨899226, by rfl⟩ : syracuseStep 2397937 = 1798453) B1798453
theorem B2397971 : Blo 1419529 2397971 := bstep (se 1 (by rfl) ⟨1798478, by rfl⟩ : syracuseStep 2397971 = 3596957) B3596957
theorem B2160449 : Blo 1419529 2160449 := bstep (se 2 (by rfl) ⟨810168, by rfl⟩ : syracuseStep 2160449 = 1620337) B1620337
theorem B3241795 : Blo 1419529 3241795 := bstep (se 1 (by rfl) ⟨2431346, by rfl⟩ : syracuseStep 3241795 = 4862693) B4862693
theorem B22763405 : Blo 1419529 22763405 := bstep (se 3 (by rfl) ⟨4268138, by rfl⟩ : syracuseStep 22763405 = 8536277) B8536277
theorem B2398099 : Blo 1419529 2398099 := bstep (se 1 (by rfl) ⟨1798574, by rfl⟩ : syracuseStep 2398099 = 3597149) B3597149
theorem B2275361 : Blo 1419529 2275361 := bstep (se 2 (by rfl) ⟨853260, by rfl⟩ : syracuseStep 2275361 = 1706521) B1706521
theorem B2398241 : Blo 1419529 2398241 := bstep (se 2 (by rfl) ⟨899340, by rfl⟩ : syracuseStep 2398241 = 1798681) B1798681
theorem B4610147 : Blo 1419529 4610147 := bstep (se 1 (by rfl) ⟨3457610, by rfl⟩ : syracuseStep 4610147 = 6915221) B6915221
theorem B2398369 : Blo 1419529 2398369 := bstep (se 2 (by rfl) ⟨899388, by rfl⟩ : syracuseStep 2398369 = 1798777) B1798777
theorem B2398403 : Blo 1419529 2398403 := bstep (se 1 (by rfl) ⟨1798802, by rfl⟩ : syracuseStep 2398403 = 3597605) B3597605
theorem B2275553 : Blo 1419529 2275553 := bstep (se 2 (by rfl) ⟨853332, by rfl⟩ : syracuseStep 2275553 = 1706665) B1706665
theorem B6068515 : Blo 1419529 6068515 := bstep (se 1 (by rfl) ⟨4551386, by rfl⟩ : syracuseStep 6068515 = 9102773) B9102773
theorem B9107747 : Blo 1419529 9107747 := bstep (se 1 (by rfl) ⟨6830810, by rfl⟩ : syracuseStep 9107747 = 13661621) B13661621
theorem B4102445 : Blo 1419529 4102445 := bstep (se 3 (by rfl) ⟨769208, by rfl⟩ : syracuseStep 4102445 = 1538417) B1538417
theorem B4553027 : Blo 1419529 4553027 := bstep (se 1 (by rfl) ⟨3414770, by rfl⟩ : syracuseStep 4553027 = 6829541) B6829541
theorem B2398531 : Blo 1419529 2398531 := bstep (se 1 (by rfl) ⟨1798898, by rfl⟩ : syracuseStep 2398531 = 3597797) B3597797
theorem B3594577 : Blo 1419529 3594577 := bstep (se 2 (by rfl) ⟨1347966, by rfl⟩ : syracuseStep 3594577 = 2695933) B2695933
theorem B3840365 : Blo 1419529 3840365 := bstep (se 3 (by rfl) ⟨720068, by rfl⟩ : syracuseStep 3840365 = 1440137) B1440137
theorem B9099697 : Blo 1419529 9099697 := bstep (se 2 (by rfl) ⟨3412386, by rfl⟩ : syracuseStep 9099697 = 6824773) B6824773
theorem B2398673 : Blo 1419529 2398673 := bstep (se 2 (by rfl) ⟨899502, by rfl⟩ : syracuseStep 2398673 = 1799005) B1799005
theorem B16407011 : Blo 1419529 16407011 := bstep (se 1 (by rfl) ⟨12305258, by rfl⟩ : syracuseStep 16407011 = 24610517) B24610517
theorem B9230917 : Blo 1419529 9230917 := bstep (se 4 (by rfl) ⟨865398, by rfl⟩ : syracuseStep 9230917 = 1730797) B1730797
theorem B2398801 : Blo 1419529 2398801 := bstep (se 2 (by rfl) ⟨899550, by rfl⟩ : syracuseStep 2398801 = 1799101) B1799101
theorem B3594851 : Blo 1419529 3594851 := bstep (se 1 (by rfl) ⟨2696138, by rfl⟩ : syracuseStep 3594851 = 5392277) B5392277
theorem B4553425 : Blo 1419529 4553425 := bstep (se 2 (by rfl) ⟨1707534, by rfl⟩ : syracuseStep 4553425 = 3415069) B3415069
theorem B4553489 : Blo 1419529 4553489 := bstep (se 2 (by rfl) ⟨1707558, by rfl⟩ : syracuseStep 4553489 = 3415117) B3415117
theorem B3595043 : Blo 1419529 3595043 := bstep (se 1 (by rfl) ⟨2696282, by rfl⟩ : syracuseStep 3595043 = 5392565) B5392565
theorem B8092493 : Blo 1419529 8092493 := bstep (se 3 (by rfl) ⟨1517342, by rfl⟩ : syracuseStep 8092493 = 3034685) B3034685
theorem B2022241 : Blo 1419529 2022241 := bstep (se 2 (by rfl) ⟨758340, by rfl⟩ : syracuseStep 2022241 = 1516681) B1516681
theorem B4791149 : Blo 1419529 4791149 := bstep (se 3 (by rfl) ⟨898340, by rfl⟩ : syracuseStep 4791149 = 1796681) B1796681
theorem B4791203 : Blo 1419529 4791203 := bstep (se 1 (by rfl) ⟨3593402, by rfl⟩ : syracuseStep 4791203 = 7186805) B7186805
theorem B2022337 : Blo 1419529 2022337 := bstep (se 2 (by rfl) ⟨758376, by rfl⟩ : syracuseStep 2022337 = 1516753) B1516753
theorem B4045859 : Blo 1419529 4045859 := bstep (se 1 (by rfl) ⟨3034394, by rfl⟩ : syracuseStep 4045859 = 6068789) B6068789
theorem B147881045 : Blo 1419529 147881045 := bstep (se 8 (by rfl) ⟨866490, by rfl⟩ : syracuseStep 147881045 = 1732981) B1732981
theorem B3193955 : Blo 1419529 3193955 := bstep (se 1 (by rfl) ⟨2395466, by rfl⟩ : syracuseStep 3193955 = 4790933) B4790933
theorem B7191665 : Blo 1419529 7191665 := bstep (se 2 (by rfl) ⟨2696874, by rfl⟩ : syracuseStep 7191665 = 5393749) B5393749
theorem B4791473 : Blo 1419529 4791473 := bstep (se 2 (by rfl) ⟨1796802, by rfl⟩ : syracuseStep 4791473 = 3593605) B3593605
theorem B8084771 : Blo 1419529 8084771 := bstep (se 1 (by rfl) ⟨6063578, by rfl⟩ : syracuseStep 8084771 = 12127157) B12127157
theorem B8314211 : Blo 1419529 8314211 := bstep (se 1 (by rfl) ⟨6235658, by rfl⟩ : syracuseStep 8314211 = 12471317) B12471317
theorem B3194225 : Blo 1419529 3194225 := bstep (se 2 (by rfl) ⟨1197834, by rfl⟩ : syracuseStep 3194225 = 2395669) B2395669
theorem B3194243 : Blo 1419529 3194243 := bstep (se 1 (by rfl) ⟨2395682, by rfl⟩ : syracuseStep 3194243 = 4791365) B4791365
theorem B2129297 : Blo 1419529 2129297 := bstep (se 2 (by rfl) ⟨798486, by rfl⟩ : syracuseStep 2129297 = 1596973) B1596973
theorem B2129315 : Blo 1419529 2129315 := bstep (se 1 (by rfl) ⟨1596986, by rfl⟩ : syracuseStep 2129315 = 3193973) B3193973
theorem B2022833 : Blo 1419529 2022833 := bstep (se 2 (by rfl) ⟨758562, by rfl⟩ : syracuseStep 2022833 = 1517125) B1517125
theorem B2129345 : Blo 1419529 2129345 := bstep (se 2 (by rfl) ⟨798504, by rfl⟩ : syracuseStep 2129345 = 1597009) B1597009
theorem B2129363 : Blo 1419529 2129363 := bstep (se 1 (by rfl) ⟨1597022, by rfl⟩ : syracuseStep 2129363 = 3194045) B3194045
theorem B2129393 : Blo 1419529 2129393 := bstep (se 2 (by rfl) ⟨798522, by rfl⟩ : syracuseStep 2129393 = 1597045) B1597045
theorem B6069745 : Blo 1419529 6069745 := bstep (se 2 (by rfl) ⟨2276154, by rfl⟩ : syracuseStep 6069745 = 4552309) B4552309
theorem B2129411 : Blo 1419529 2129411 := bstep (se 1 (by rfl) ⟨1597058, by rfl⟩ : syracuseStep 2129411 = 3194117) B3194117
theorem B2129441 : Blo 1419529 2129441 := bstep (se 2 (by rfl) ⟨798540, by rfl⟩ : syracuseStep 2129441 = 1597081) B1597081
theorem B7781923 : Blo 1419529 7781923 := bstep (se 1 (by rfl) ⟨5836442, by rfl⟩ : syracuseStep 7781923 = 11672885) B11672885
theorem B2129459 : Blo 1419529 2129459 := bstep (se 1 (by rfl) ⟨1597094, by rfl⟩ : syracuseStep 2129459 = 3194189) B3194189
theorem B472858165 : Blo 1419529 472858165 := bstep (se 5 (by rfl) ⟨22165226, by rfl⟩ : syracuseStep 472858165 = 44330453) B44330453
theorem B2129489 : Blo 1419529 2129489 := bstep (se 2 (by rfl) ⟨798558, by rfl⟩ : syracuseStep 2129489 = 1597117) B1597117
theorem B1597027 : Blo 1419529 1597027 := bstep (se 1 (by rfl) ⟨1197770, by rfl⟩ : syracuseStep 1597027 = 2395541) B2395541
theorem B2129507 : Blo 1419529 2129507 := bstep (se 1 (by rfl) ⟨1597130, by rfl⟩ : syracuseStep 2129507 = 3194261) B3194261
theorem B13647473 : Blo 1419529 13647473 := bstep (se 2 (by rfl) ⟨5117802, by rfl⟩ : syracuseStep 13647473 = 10235605) B10235605
theorem B2129537 : Blo 1419529 2129537 := bstep (se 2 (by rfl) ⟨798576, by rfl⟩ : syracuseStep 2129537 = 1597153) B1597153
theorem B3194513 : Blo 1419529 3194513 := bstep (se 2 (by rfl) ⟨1197942, by rfl⟩ : syracuseStep 3194513 = 2395885) B2395885
theorem B2129555 : Blo 1419529 2129555 := bstep (se 1 (by rfl) ⟨1597166, by rfl⟩ : syracuseStep 2129555 = 3194333) B3194333
theorem B3194531 : Blo 1419529 3194531 := bstep (se 1 (by rfl) ⟨2395898, by rfl⟩ : syracuseStep 3194531 = 4791797) B4791797
theorem B2129585 : Blo 1419529 2129585 := bstep (se 2 (by rfl) ⟨798594, by rfl⟩ : syracuseStep 2129585 = 1597189) B1597189
theorem B16170677 : Blo 1419529 16170677 := bstep (se 5 (by rfl) ⟨758000, by rfl⟩ : syracuseStep 16170677 = 1516001) B1516001
theorem B2129603 : Blo 1419529 2129603 := bstep (se 1 (by rfl) ⟨1597202, by rfl⟩ : syracuseStep 2129603 = 3194405) B3194405
theorem B4792013 : Blo 1419529 4792013 := bstep (se 3 (by rfl) ⟨898502, by rfl⟩ : syracuseStep 4792013 = 1797005) B1797005
theorem B3595985 : Blo 1419529 3595985 := bstep (se 2 (by rfl) ⟨1348494, by rfl⟩ : syracuseStep 3595985 = 2696989) B2696989
theorem B2129633 : Blo 1419529 2129633 := bstep (se 2 (by rfl) ⟨798612, by rfl⟩ : syracuseStep 2129633 = 1597225) B1597225
theorem B1597171 : Blo 1419529 1597171 := bstep (se 1 (by rfl) ⟨1197878, by rfl⟩ : syracuseStep 1597171 = 2395757) B2395757
theorem B2129651 : Blo 1419529 2129651 := bstep (se 1 (by rfl) ⟨1597238, by rfl⟩ : syracuseStep 2129651 = 3194477) B3194477
theorem B4792067 : Blo 1419529 4792067 := bstep (se 1 (by rfl) ⟨3594050, by rfl⟩ : syracuseStep 4792067 = 7188101) B7188101
theorem B3596035 : Blo 1419529 3596035 := bstep (se 1 (by rfl) ⟨2697026, by rfl⟩ : syracuseStep 3596035 = 5394053) B5394053
theorem B2129681 : Blo 1419529 2129681 := bstep (se 2 (by rfl) ⟨798630, by rfl⟩ : syracuseStep 2129681 = 1597261) B1597261
theorem B2129699 : Blo 1419529 2129699 := bstep (se 1 (by rfl) ⟨1597274, by rfl⟩ : syracuseStep 2129699 = 3194549) B3194549
theorem B2694961 : Blo 1419529 2694961 := bstep (se 2 (by rfl) ⟨1010610, by rfl⟩ : syracuseStep 2694961 = 2021221) B2021221
theorem B2129729 : Blo 1419529 2129729 := bstep (se 2 (by rfl) ⟨798648, by rfl⟩ : syracuseStep 2129729 = 1597297) B1597297
theorem B4046669 : Blo 1419529 4046669 := bstep (se 3 (by rfl) ⟨758750, by rfl⟩ : syracuseStep 4046669 = 1517501) B1517501
theorem B2129747 : Blo 1419529 2129747 := bstep (se 1 (by rfl) ⟨1597310, by rfl⟩ : syracuseStep 2129747 = 3194621) B3194621
theorem B2129777 : Blo 1419529 2129777 := bstep (se 2 (by rfl) ⟨798666, by rfl⟩ : syracuseStep 2129777 = 1597333) B1597333
theorem B1597315 : Blo 1419529 1597315 := bstep (se 1 (by rfl) ⟨1197986, by rfl⟩ : syracuseStep 1597315 = 2395973) B2395973
theorem B2129795 : Blo 1419529 2129795 := bstep (se 1 (by rfl) ⟨1597346, by rfl⟩ : syracuseStep 2129795 = 3194693) B3194693
theorem B3596177 : Blo 1419529 3596177 := bstep (se 2 (by rfl) ⟨1348566, by rfl⟩ : syracuseStep 3596177 = 2697133) B2697133
theorem B2129825 : Blo 1419529 2129825 := bstep (se 2 (by rfl) ⟨798684, by rfl⟩ : syracuseStep 2129825 = 1597369) B1597369
theorem B3194801 : Blo 1419529 3194801 := bstep (se 2 (by rfl) ⟨1198050, by rfl⟩ : syracuseStep 3194801 = 2396101) B2396101
theorem B2129843 : Blo 1419529 2129843 := bstep (se 1 (by rfl) ⟨1597382, by rfl⟩ : syracuseStep 2129843 = 3194765) B3194765
theorem B3194819 : Blo 1419529 3194819 := bstep (se 1 (by rfl) ⟨2396114, by rfl⟩ : syracuseStep 3194819 = 4792229) B4792229
theorem B2129873 : Blo 1419529 2129873 := bstep (se 2 (by rfl) ⟨798702, by rfl⟩ : syracuseStep 2129873 = 1597405) B1597405
theorem B2129891 : Blo 1419529 2129891 := bstep (se 1 (by rfl) ⟨1597418, by rfl⟩ : syracuseStep 2129891 = 3194837) B3194837
theorem B3194891 : Blo 1419529 3194891 := bstep (se 1 (by rfl) ⟨2396168, by rfl⟩ : syracuseStep 3194891 = 4792337) B4792337
theorem B8085521 : Blo 1419529 8085521 := bstep (se 2 (by rfl) ⟨3032070, by rfl⟩ : syracuseStep 8085521 = 6064141) B6064141
theorem B2129945 : Blo 1419529 2129945 := bstep (se 2 (by rfl) ⟨798729, by rfl⟩ : syracuseStep 2129945 = 1597459) B1597459
theorem B3596339 : Blo 1419529 3596339 := bstep (se 1 (by rfl) ⟨2697254, by rfl⟩ : syracuseStep 3596339 = 5394509) B5394509
theorem B1597495 : Blo 1419529 1597495 := bstep (se 1 (by rfl) ⟨1198121, by rfl⟩ : syracuseStep 1597495 = 2396243) B2396243
theorem B3194945 : Blo 1419529 3194945 := bstep (se 2 (by rfl) ⟨1198104, by rfl⟩ : syracuseStep 3194945 = 2396209) B2396209
theorem B2023499 : Blo 1419529 2023499 := bstep (se 1 (by rfl) ⟨1517624, by rfl⟩ : syracuseStep 2023499 = 3035249) B3035249
theorem B2130059 : Blo 1419529 2130059 := bstep (se 1 (by rfl) ⟨1597544, by rfl⟩ : syracuseStep 2130059 = 3195089) B3195089
theorem B2130071 : Blo 1419529 2130071 := bstep (se 1 (by rfl) ⟨1597553, by rfl⟩ : syracuseStep 2130071 = 3195107) B3195107
theorem B4792499 : Blo 1419529 4792499 := bstep (se 1 (by rfl) ⟨3594374, by rfl⟩ : syracuseStep 4792499 = 7188749) B7188749
theorem B2130137 : Blo 1419529 2130137 := bstep (se 2 (by rfl) ⟨798801, by rfl⟩ : syracuseStep 2130137 = 1597603) B1597603
theorem B1597675 : Blo 1419529 1597675 := bstep (se 1 (by rfl) ⟨1198256, by rfl⟩ : syracuseStep 1597675 = 2396513) B2396513
theorem B2695447 : Blo 1419529 2695447 := bstep (se 1 (by rfl) ⟨2021585, by rfl⟩ : syracuseStep 2695447 = 4043171) B4043171
theorem B3195161 : Blo 1419529 3195161 := bstep (se 2 (by rfl) ⟨1198185, by rfl⟩ : syracuseStep 3195161 = 2396371) B2396371
theorem B2130251 : Blo 1419529 2130251 := bstep (se 1 (by rfl) ⟨1597688, by rfl⟩ : syracuseStep 2130251 = 3195377) B3195377
theorem B2130263 : Blo 1419529 2130263 := bstep (se 1 (by rfl) ⟨1597697, by rfl⟩ : syracuseStep 2130263 = 3195395) B3195395
theorem B1597783 : Blo 1419529 1597783 := bstep (se 1 (by rfl) ⟨1198337, by rfl⟩ : syracuseStep 1597783 = 2396675) B2396675
theorem B3596633 : Blo 1419529 3596633 := bstep (se 2 (by rfl) ⟨1348737, by rfl⟩ : syracuseStep 3596633 = 2697475) B2697475
theorem B3195251 : Blo 1419529 3195251 := bstep (se 1 (by rfl) ⟨2396438, by rfl⟩ : syracuseStep 3195251 = 4792877) B4792877
theorem B3195287 : Blo 1419529 3195287 := bstep (se 1 (by rfl) ⟨2396465, by rfl⟩ : syracuseStep 3195287 = 4792931) B4792931
theorem B2130329 : Blo 1419529 2130329 := bstep (se 2 (by rfl) ⟨798873, by rfl⟩ : syracuseStep 2130329 = 1597747) B1597747
theorem B23036339 : Blo 1419529 23036339 := bstep (se 1 (by rfl) ⟨17277254, by rfl⟩ : syracuseStep 23036339 = 34554509) B34554509
theorem B9101747 : Blo 1419529 9101747 := bstep (se 1 (by rfl) ⟨6826310, by rfl⟩ : syracuseStep 9101747 = 13652621) B13652621
theorem B20480435 : Blo 1419529 20480435 := bstep (se 1 (by rfl) ⟨15360326, by rfl⟩ : syracuseStep 20480435 = 30720653) B30720653
theorem B4792769 : Blo 1419529 4792769 := bstep (se 2 (by rfl) ⟨1797288, by rfl⟩ : syracuseStep 4792769 = 3594577) B3594577
theorem B8085977 : Blo 1419529 8085977 := bstep (se 2 (by rfl) ⟨3032241, by rfl⟩ : syracuseStep 8085977 = 6064483) B6064483
theorem B2130443 : Blo 1419529 2130443 := bstep (se 1 (by rfl) ⟨1597832, by rfl⟩ : syracuseStep 2130443 = 3195665) B3195665
theorem B1597963 : Blo 1419529 1597963 := bstep (se 1 (by rfl) ⟨1198472, by rfl⟩ : syracuseStep 1597963 = 2396945) B2396945
theorem B2130455 : Blo 1419529 2130455 := bstep (se 1 (by rfl) ⟨1597841, by rfl⟩ : syracuseStep 2130455 = 3195683) B3195683
theorem B1516087 : Blo 1419529 1516087 := bstep (se 1 (by rfl) ⟨1137065, by rfl⟩ : syracuseStep 1516087 = 2274131) B2274131
theorem B12132929 : Blo 1419529 12132929 := bstep (se 2 (by rfl) ⟨4549848, by rfl⟩ : syracuseStep 12132929 = 9099697) B9099697
theorem B3195467 : Blo 1419529 3195467 := bstep (se 1 (by rfl) ⟨2396600, by rfl⟩ : syracuseStep 3195467 = 4793201) B4793201
theorem B2130521 : Blo 1419529 2130521 := bstep (se 2 (by rfl) ⟨798945, by rfl⟩ : syracuseStep 2130521 = 1597891) B1597891
theorem B1598071 : Blo 1419529 1598071 := bstep (se 1 (by rfl) ⟨1198553, by rfl⟩ : syracuseStep 1598071 = 2397107) B2397107
theorem B3195521 : Blo 1419529 3195521 := bstep (se 2 (by rfl) ⟨1198320, by rfl⟩ : syracuseStep 3195521 = 2396641) B2396641
theorem B11518595 : Blo 1419529 11518595 := bstep (se 1 (by rfl) ⟨8638946, by rfl⟩ : syracuseStep 11518595 = 17277893) B17277893
theorem B2130635 : Blo 1419529 2130635 := bstep (se 1 (by rfl) ⟨1597976, by rfl⟩ : syracuseStep 2130635 = 3195953) B3195953
theorem B2130647 : Blo 1419529 2130647 := bstep (se 1 (by rfl) ⟨1597985, by rfl⟩ : syracuseStep 2130647 = 3195971) B3195971
theorem B5391107 : Blo 1419529 5391107 := bstep (se 1 (by rfl) ⟨4043330, by rfl⟩ : syracuseStep 5391107 = 8086661) B8086661
theorem B2130713 : Blo 1419529 2130713 := bstep (se 2 (by rfl) ⟨799017, by rfl⟩ : syracuseStep 2130713 = 1598035) B1598035
theorem B1598251 : Blo 1419529 1598251 := bstep (se 1 (by rfl) ⟨1198688, by rfl⟩ : syracuseStep 1598251 = 2397377) B2397377
theorem B7676747 : Blo 1419529 7676747 := bstep (se 1 (by rfl) ⟨5757560, by rfl⟩ : syracuseStep 7676747 = 11515121) B11515121
theorem B3195737 : Blo 1419529 3195737 := bstep (se 2 (by rfl) ⟨1198401, by rfl⟩ : syracuseStep 3195737 = 2396803) B2396803
theorem B2130827 : Blo 1419529 2130827 := bstep (se 1 (by rfl) ⟨1598120, by rfl⟩ : syracuseStep 2130827 = 3196241) B3196241
theorem B2130839 : Blo 1419529 2130839 := bstep (se 1 (by rfl) ⟨1598129, by rfl⟩ : syracuseStep 2130839 = 3196259) B3196259
theorem B1598359 : Blo 1419529 1598359 := bstep (se 1 (by rfl) ⟨1198769, by rfl⟩ : syracuseStep 1598359 = 2397539) B2397539
theorem B3195827 : Blo 1419529 3195827 := bstep (se 1 (by rfl) ⟨2396870, by rfl⟩ : syracuseStep 3195827 = 4793741) B4793741
theorem B6071233 : Blo 1419529 6071233 := bstep (se 2 (by rfl) ⟨2276712, by rfl⟩ : syracuseStep 6071233 = 4553425) B4553425
theorem B3195863 : Blo 1419529 3195863 := bstep (se 1 (by rfl) ⟨2396897, by rfl⟩ : syracuseStep 3195863 = 4793795) B4793795
theorem B2130905 : Blo 1419529 2130905 := bstep (se 2 (by rfl) ⟨799089, by rfl⟩ : syracuseStep 2130905 = 1598179) B1598179
theorem B4793309 : Blo 1419529 4793309 := bstep (se 3 (by rfl) ⟨898745, by rfl⟩ : syracuseStep 4793309 = 1797491) B1797491
theorem B10232837 : Blo 1419529 10232837 := bstep (se 4 (by rfl) ⟨959328, by rfl⟩ : syracuseStep 10232837 = 1918657) B1918657
theorem B6153239 : Blo 1419529 6153239 := bstep (se 1 (by rfl) ⟨4614929, by rfl⟩ : syracuseStep 6153239 = 9229859) B9229859
theorem B13648931 : Blo 1419529 13648931 := bstep (se 1 (by rfl) ⟨10236698, by rfl⟩ : syracuseStep 13648931 = 20473397) B20473397
theorem B6825005 : Blo 1419529 6825005 := bstep (se 3 (by rfl) ⟨1279688, by rfl⟩ : syracuseStep 6825005 = 2559377) B2559377
theorem B2696267 : Blo 1419529 2696267 := bstep (se 1 (by rfl) ⟨2022200, by rfl⟩ : syracuseStep 2696267 = 4044401) B4044401
theorem B2131019 : Blo 1419529 2131019 := bstep (se 1 (by rfl) ⟨1598264, by rfl⟩ : syracuseStep 2131019 = 3196529) B3196529
theorem B1598539 : Blo 1419529 1598539 := bstep (se 1 (by rfl) ⟨1198904, by rfl⟩ : syracuseStep 1598539 = 2397809) B2397809
theorem B2131031 : Blo 1419529 2131031 := bstep (se 1 (by rfl) ⟨1598273, by rfl⟩ : syracuseStep 2131031 = 3196547) B3196547
theorem B2696321 : Blo 1419529 2696321 := bstep (se 2 (by rfl) ⟨1011120, by rfl⟩ : syracuseStep 2696321 = 2022241) B2022241
theorem B3196043 : Blo 1419529 3196043 := bstep (se 1 (by rfl) ⟨2397032, by rfl⟩ : syracuseStep 3196043 = 4794065) B4794065
theorem B2131097 : Blo 1419529 2131097 := bstep (se 2 (by rfl) ⟨799161, by rfl⟩ : syracuseStep 2131097 = 1598323) B1598323
theorem B1598647 : Blo 1419529 1598647 := bstep (se 1 (by rfl) ⟨1198985, by rfl⟩ : syracuseStep 1598647 = 2397971) B2397971
theorem B3196097 : Blo 1419529 3196097 := bstep (se 2 (by rfl) ⟨1198536, by rfl⟩ : syracuseStep 3196097 = 2397073) B2397073
theorem B2131211 : Blo 1419529 2131211 := bstep (se 1 (by rfl) ⟨1598408, by rfl⟩ : syracuseStep 2131211 = 3196817) B3196817
theorem B2131223 : Blo 1419529 2131223 := bstep (se 1 (by rfl) ⟨1598417, by rfl⟩ : syracuseStep 2131223 = 3196835) B3196835
theorem B2131289 : Blo 1419529 2131289 := bstep (se 2 (by rfl) ⟨799233, by rfl⟩ : syracuseStep 2131289 = 1598467) B1598467
theorem B1516907 : Blo 1419529 1516907 := bstep (se 1 (by rfl) ⟨1137680, by rfl⟩ : syracuseStep 1516907 = 2275361) B2275361
theorem B1598827 : Blo 1419529 1598827 := bstep (se 1 (by rfl) ⟨1199120, by rfl⟩ : syracuseStep 1598827 = 2398241) B2398241
theorem B3032473 : Blo 1419529 3032473 := bstep (se 2 (by rfl) ⟨1137177, by rfl⟩ : syracuseStep 3032473 = 2274355) B2274355
theorem B3196313 : Blo 1419529 3196313 := bstep (se 2 (by rfl) ⟨1198617, by rfl⟩ : syracuseStep 3196313 = 2397235) B2397235
theorem B2131403 : Blo 1419529 2131403 := bstep (se 1 (by rfl) ⟨1598552, by rfl⟩ : syracuseStep 2131403 = 3197105) B3197105
theorem B2131415 : Blo 1419529 2131415 := bstep (se 1 (by rfl) ⟨1598561, by rfl⟩ : syracuseStep 2131415 = 3197123) B3197123
theorem B1598935 : Blo 1419529 1598935 := bstep (se 1 (by rfl) ⟨1199201, by rfl⟩ : syracuseStep 1598935 = 2398403) B2398403
theorem B3196403 : Blo 1419529 3196403 := bstep (se 1 (by rfl) ⟨2397302, by rfl⟩ : syracuseStep 3196403 = 4794605) B4794605
theorem B3196439 : Blo 1419529 3196439 := bstep (se 1 (by rfl) ⟨2397329, by rfl⟩ : syracuseStep 3196439 = 4794659) B4794659
theorem B6071831 : Blo 1419529 6071831 := bstep (se 1 (by rfl) ⟨4553873, by rfl⟩ : syracuseStep 6071831 = 9107747) B9107747
theorem B2131481 : Blo 1419529 2131481 := bstep (se 2 (by rfl) ⟨799305, by rfl⟩ : syracuseStep 2131481 = 1598611) B1598611
theorem B1918603 : Blo 1419529 1918603 := bstep (se 1 (by rfl) ⟨1438952, by rfl⟩ : syracuseStep 1918603 = 2877905) B2877905
theorem B2131595 : Blo 1419529 2131595 := bstep (se 1 (by rfl) ⟨1598696, by rfl⟩ : syracuseStep 2131595 = 3197393) B3197393
theorem B1599115 : Blo 1419529 1599115 := bstep (se 1 (by rfl) ⟨1199336, by rfl⟩ : syracuseStep 1599115 = 2398673) B2398673
theorem B6063767 : Blo 1419529 6063767 := bstep (se 1 (by rfl) ⟨4547825, by rfl⟩ : syracuseStep 6063767 = 9095651) B9095651
theorem B10938007 : Blo 1419529 10938007 := bstep (se 1 (by rfl) ⟨8203505, by rfl⟩ : syracuseStep 10938007 = 16407011) B16407011
theorem B2131607 : Blo 1419529 2131607 := bstep (se 1 (by rfl) ⟨1598705, by rfl⟩ : syracuseStep 2131607 = 3197411) B3197411
theorem B3196619 : Blo 1419529 3196619 := bstep (se 1 (by rfl) ⟨2397464, by rfl⟩ : syracuseStep 3196619 = 4794929) B4794929
theorem B2131673 : Blo 1419529 2131673 := bstep (se 2 (by rfl) ⟨799377, by rfl⟩ : syracuseStep 2131673 = 1598755) B1598755
theorem B3196673 : Blo 1419529 3196673 := bstep (se 2 (by rfl) ⟨1198752, by rfl⟩ : syracuseStep 3196673 = 2397505) B2397505
theorem B13141835 : Blo 1419529 13141835 := bstep (se 1 (by rfl) ⟨9856376, by rfl⟩ : syracuseStep 13141835 = 19712753) B19712753
theorem B2131787 : Blo 1419529 2131787 := bstep (se 1 (by rfl) ⟨1598840, by rfl⟩ : syracuseStep 2131787 = 3197681) B3197681
theorem B2131799 : Blo 1419529 2131799 := bstep (se 1 (by rfl) ⟨1598849, by rfl⟩ : syracuseStep 2131799 = 3197699) B3197699
theorem B2189209 : Blo 1419529 2189209 := bstep (se 2 (by rfl) ⟨820953, by rfl⟩ : syracuseStep 2189209 = 1641907) B1641907
theorem B2131865 : Blo 1419529 2131865 := bstep (se 2 (by rfl) ⟨799449, by rfl⟩ : syracuseStep 2131865 = 1598899) B1598899
theorem B11519921 : Blo 1419529 11519921 := bstep (se 2 (by rfl) ⟨4319970, by rfl⟩ : syracuseStep 11519921 = 8639941) B8639941
theorem B3196889 : Blo 1419529 3196889 := bstep (se 2 (by rfl) ⟨1198833, by rfl⟩ : syracuseStep 3196889 = 2397667) B2397667
theorem B2131979 : Blo 1419529 2131979 := bstep (se 1 (by rfl) ⟨1598984, by rfl⟩ : syracuseStep 2131979 = 3197969) B3197969
theorem B2697239 : Blo 1419529 2697239 := bstep (se 1 (by rfl) ⟨2022929, by rfl⟩ : syracuseStep 2697239 = 4045859) B4045859
theorem B2131991 : Blo 1419529 2131991 := bstep (se 1 (by rfl) ⟨1598993, by rfl⟩ : syracuseStep 2131991 = 3197987) B3197987
theorem B30738467 : Blo 1419529 30738467 := bstep (se 1 (by rfl) ⟨23053850, by rfl⟩ : syracuseStep 30738467 = 46107701) B46107701
theorem B3196979 : Blo 1419529 3196979 := bstep (se 1 (by rfl) ⟨2397734, by rfl⟩ : syracuseStep 3196979 = 4795469) B4795469
theorem B4794443 : Blo 1419529 4794443 := bstep (se 1 (by rfl) ⟨3595832, by rfl⟩ : syracuseStep 4794443 = 7191665) B7191665
theorem B3197015 : Blo 1419529 3197015 := bstep (se 1 (by rfl) ⟨2397761, by rfl⟩ : syracuseStep 3197015 = 4795523) B4795523
theorem B2132057 : Blo 1419529 2132057 := bstep (se 2 (by rfl) ⟨799521, by rfl⟩ : syracuseStep 2132057 = 1599043) B1599043
theorem B2132171 : Blo 1419529 2132171 := bstep (se 1 (by rfl) ⟨1599128, by rfl⟩ : syracuseStep 2132171 = 3198257) B3198257
theorem B2132183 : Blo 1419529 2132183 := bstep (se 1 (by rfl) ⟨1599137, by rfl⟩ : syracuseStep 2132183 = 3198275) B3198275
theorem B1419531 : Blo 1419529 1419531 := bstep (se 1 (by rfl) ⟨1064648, by rfl⟩ : syracuseStep 1419531 = 2129297) B2129297
theorem B3197195 : Blo 1419529 3197195 := bstep (se 1 (by rfl) ⟨2397896, by rfl⟩ : syracuseStep 3197195 = 4795793) B4795793
theorem B1419543 : Blo 1419529 1419543 := bstep (se 1 (by rfl) ⟨1064657, by rfl⟩ : syracuseStep 1419543 = 2129315) B2129315
theorem B2132249 : Blo 1419529 2132249 := bstep (se 2 (by rfl) ⟨799593, by rfl⟩ : syracuseStep 2132249 = 1599187) B1599187
theorem B1419563 : Blo 1419529 1419563 := bstep (se 1 (by rfl) ⟨1064672, by rfl⟩ : syracuseStep 1419563 = 2129345) B2129345
theorem B1419575 : Blo 1419529 1419575 := bstep (se 1 (by rfl) ⟨1064681, by rfl⟩ : syracuseStep 1419575 = 2129363) B2129363
theorem B3197249 : Blo 1419529 3197249 := bstep (se 2 (by rfl) ⟨1198968, by rfl⟩ : syracuseStep 3197249 = 2397937) B2397937
theorem B1419595 : Blo 1419529 1419595 := bstep (se 1 (by rfl) ⟨1064696, by rfl⟩ : syracuseStep 1419595 = 2129393) B2129393
theorem B1419607 : Blo 1419529 1419607 := bstep (se 1 (by rfl) ⟨1064705, by rfl⟩ : syracuseStep 1419607 = 2129411) B2129411
theorem B4548953 : Blo 1419529 4548953 := bstep (se 2 (by rfl) ⟨1705857, by rfl⟩ : syracuseStep 4548953 = 3411715) B3411715
theorem B4794713 : Blo 1419529 4794713 := bstep (se 2 (by rfl) ⟨1798017, by rfl⟩ : syracuseStep 4794713 = 3596035) B3596035
theorem B1419627 : Blo 1419529 1419627 := bstep (se 1 (by rfl) ⟨1064720, by rfl⟩ : syracuseStep 1419627 = 2129441) B2129441
theorem B1419639 : Blo 1419529 1419639 := bstep (se 1 (by rfl) ⟨1064729, by rfl⟩ : syracuseStep 1419639 = 2129459) B2129459
theorem B1419659 : Blo 1419529 1419659 := bstep (se 1 (by rfl) ⟨1064744, by rfl⟩ : syracuseStep 1419659 = 2129489) B2129489
theorem B1419671 : Blo 1419529 1419671 := bstep (se 1 (by rfl) ⟨1064753, by rfl⟩ : syracuseStep 1419671 = 2129507) B2129507
theorem B1419691 : Blo 1419529 1419691 := bstep (se 1 (by rfl) ⟨1064768, by rfl⟩ : syracuseStep 1419691 = 2129537) B2129537
theorem B10373555 : Blo 1419529 10373555 := bstep (se 1 (by rfl) ⟨7780166, by rfl⟩ : syracuseStep 10373555 = 15560333) B15560333
theorem B1419703 : Blo 1419529 1419703 := bstep (se 1 (by rfl) ⟨1064777, by rfl⟩ : syracuseStep 1419703 = 2129555) B2129555
theorem B1419723 : Blo 1419529 1419723 := bstep (se 1 (by rfl) ⟨1064792, by rfl⟩ : syracuseStep 1419723 = 2129585) B2129585
theorem B1419735 : Blo 1419529 1419735 := bstep (se 1 (by rfl) ⟨1064801, by rfl⟩ : syracuseStep 1419735 = 2129603) B2129603
theorem B4549081 : Blo 1419529 4549081 := bstep (se 2 (by rfl) ⟨1705905, by rfl⟩ : syracuseStep 4549081 = 3411811) B3411811
theorem B4319705 : Blo 1419529 4319705 := bstep (se 2 (by rfl) ⟨1619889, by rfl⟩ : syracuseStep 4319705 = 3239779) B3239779
theorem B1419755 : Blo 1419529 1419755 := bstep (se 1 (by rfl) ⟨1064816, by rfl⟩ : syracuseStep 1419755 = 2129633) B2129633
theorem B1419767 : Blo 1419529 1419767 := bstep (se 1 (by rfl) ⟨1064825, by rfl⟩ : syracuseStep 1419767 = 2129651) B2129651
theorem B1419787 : Blo 1419529 1419787 := bstep (se 1 (by rfl) ⟨1064840, by rfl⟩ : syracuseStep 1419787 = 2129681) B2129681
theorem B1419799 : Blo 1419529 1419799 := bstep (se 1 (by rfl) ⟨1064849, by rfl⟩ : syracuseStep 1419799 = 2129699) B2129699
theorem B3197465 : Blo 1419529 3197465 := bstep (se 2 (by rfl) ⟨1199049, by rfl⟩ : syracuseStep 3197465 = 2398099) B2398099
theorem B1419819 : Blo 1419529 1419819 := bstep (se 1 (by rfl) ⟨1064864, by rfl⟩ : syracuseStep 1419819 = 2129729) B2129729
theorem B2697779 : Blo 1419529 2697779 := bstep (se 1 (by rfl) ⟨2023334, by rfl⟩ : syracuseStep 2697779 = 4046669) B4046669
theorem B1419831 : Blo 1419529 1419831 := bstep (se 1 (by rfl) ⟨1064873, by rfl⟩ : syracuseStep 1419831 = 2129747) B2129747
theorem B1419851 : Blo 1419529 1419851 := bstep (se 1 (by rfl) ⟨1064888, by rfl⟩ : syracuseStep 1419851 = 2129777) B2129777
theorem B1419863 : Blo 1419529 1419863 := bstep (se 1 (by rfl) ⟨1064897, by rfl⟩ : syracuseStep 1419863 = 2129795) B2129795
theorem B7195229 : Blo 1419529 7195229 := bstep (se 3 (by rfl) ⟨1349105, by rfl⟩ : syracuseStep 7195229 = 2698211) B2698211
theorem B1419883 : Blo 1419529 1419883 := bstep (se 1 (by rfl) ⟨1064912, by rfl⟩ : syracuseStep 1419883 = 2129825) B2129825
theorem B3197555 : Blo 1419529 3197555 := bstep (se 1 (by rfl) ⟨2398166, by rfl⟩ : syracuseStep 3197555 = 4796333) B4796333
theorem B1419895 : Blo 1419529 1419895 := bstep (se 1 (by rfl) ⟨1064921, by rfl⟩ : syracuseStep 1419895 = 2129843) B2129843
theorem B1419915 : Blo 1419529 1419915 := bstep (se 1 (by rfl) ⟨1064936, by rfl⟩ : syracuseStep 1419915 = 2129873) B2129873
theorem B1419927 : Blo 1419529 1419927 := bstep (se 1 (by rfl) ⟨1064945, by rfl⟩ : syracuseStep 1419927 = 2129891) B2129891
theorem B3197591 : Blo 1419529 3197591 := bstep (se 1 (by rfl) ⟨2398193, by rfl⟩ : syracuseStep 3197591 = 4796387) B4796387
theorem B1419947 : Blo 1419529 1419947 := bstep (se 1 (by rfl) ⟨1064960, by rfl⟩ : syracuseStep 1419947 = 2129921) B2129921
theorem B3033779 : Blo 1419529 3033779 := bstep (se 1 (by rfl) ⟨2275334, by rfl⟩ : syracuseStep 3033779 = 4550669) B4550669
theorem B1419959 : Blo 1419529 1419959 := bstep (se 1 (by rfl) ⟨1064969, by rfl⟩ : syracuseStep 1419959 = 2129939) B2129939
theorem B1419979 : Blo 1419529 1419979 := bstep (se 1 (by rfl) ⟨1064984, by rfl⟩ : syracuseStep 1419979 = 2129969) B2129969
theorem B10791629 : Blo 1419529 10791629 := bstep (se 3 (by rfl) ⟨2023430, by rfl⟩ : syracuseStep 10791629 = 4046861) B4046861
theorem B1419991 : Blo 1419529 1419991 := bstep (se 1 (by rfl) ⟨1064993, by rfl⟩ : syracuseStep 1419991 = 2129987) B2129987
theorem B4549337 : Blo 1419529 4549337 := bstep (se 2 (by rfl) ⟨1706001, by rfl⟩ : syracuseStep 4549337 = 3412003) B3412003
theorem B1420011 : Blo 1419529 1420011 := bstep (se 1 (by rfl) ⟨1065008, by rfl⟩ : syracuseStep 1420011 = 2130017) B2130017
theorem B1420023 : Blo 1419529 1420023 := bstep (se 1 (by rfl) ⟨1065017, by rfl⟩ : syracuseStep 1420023 = 2130035) B2130035
theorem B1420043 : Blo 1419529 1420043 := bstep (se 1 (by rfl) ⟨1065032, by rfl⟩ : syracuseStep 1420043 = 2130065) B2130065
theorem B11676433 : Blo 1419529 11676433 := bstep (se 2 (by rfl) ⟨4378662, by rfl⟩ : syracuseStep 11676433 = 8757325) B8757325
theorem B8645393 : Blo 1419529 8645393 := bstep (se 2 (by rfl) ⟨3242022, by rfl⟩ : syracuseStep 8645393 = 6484045) B6484045
theorem B1420055 : Blo 1419529 1420055 := bstep (se 1 (by rfl) ⟨1065041, by rfl⟩ : syracuseStep 1420055 = 2130083) B2130083
theorem B1420075 : Blo 1419529 1420075 := bstep (se 1 (by rfl) ⟨1065056, by rfl⟩ : syracuseStep 1420075 = 2130113) B2130113
theorem B1420087 : Blo 1419529 1420087 := bstep (se 1 (by rfl) ⟨1065065, by rfl⟩ : syracuseStep 1420087 = 2130131) B2130131
theorem B13839169 : Blo 1419529 13839169 := bstep (se 2 (by rfl) ⟨5189688, by rfl⟩ : syracuseStep 13839169 = 10379377) B10379377
theorem B1420107 : Blo 1419529 1420107 := bstep (se 1 (by rfl) ⟨1065080, by rfl⟩ : syracuseStep 1420107 = 2130161) B2130161
theorem B3197771 : Blo 1419529 3197771 := bstep (se 1 (by rfl) ⟨2398328, by rfl⟩ : syracuseStep 3197771 = 4796657) B4796657
theorem B1420119 : Blo 1419529 1420119 := bstep (se 1 (by rfl) ⟨1065089, by rfl⟩ : syracuseStep 1420119 = 2130179) B2130179
theorem B41503589 : Blo 1419529 41503589 := bstep (se 4 (by rfl) ⟨3890961, by rfl⟩ : syracuseStep 41503589 = 7781923) B7781923
theorem B1420139 : Blo 1419529 1420139 := bstep (se 1 (by rfl) ⟨1065104, by rfl⟩ : syracuseStep 1420139 = 2130209) B2130209
theorem B1420151 : Blo 1419529 1420151 := bstep (se 1 (by rfl) ⟨1065113, by rfl⟩ : syracuseStep 1420151 = 2130227) B2130227
theorem B3197825 : Blo 1419529 3197825 := bstep (se 2 (by rfl) ⟨1199184, by rfl⟩ : syracuseStep 3197825 = 2398369) B2398369
theorem B1420171 : Blo 1419529 1420171 := bstep (se 1 (by rfl) ⟨1065128, by rfl⟩ : syracuseStep 1420171 = 2130257) B2130257
theorem B1420183 : Blo 1419529 1420183 := bstep (se 1 (by rfl) ⟨1065137, by rfl⟩ : syracuseStep 1420183 = 2130275) B2130275
theorem B1420203 : Blo 1419529 1420203 := bstep (se 1 (by rfl) ⟨1065152, by rfl⟩ : syracuseStep 1420203 = 2130305) B2130305
theorem B1420215 : Blo 1419529 1420215 := bstep (se 1 (by rfl) ⟨1065161, by rfl⟩ : syracuseStep 1420215 = 2130323) B2130323
theorem B1420235 : Blo 1419529 1420235 := bstep (se 1 (by rfl) ⟨1065176, by rfl⟩ : syracuseStep 1420235 = 2130353) B2130353
theorem B1420247 : Blo 1419529 1420247 := bstep (se 1 (by rfl) ⟨1065185, by rfl⟩ : syracuseStep 1420247 = 2130371) B2130371
theorem B1420267 : Blo 1419529 1420267 := bstep (se 1 (by rfl) ⟨1065200, by rfl⟩ : syracuseStep 1420267 = 2130401) B2130401
theorem B1420279 : Blo 1419529 1420279 := bstep (se 1 (by rfl) ⟨1065209, by rfl⟩ : syracuseStep 1420279 = 2130419) B2130419
theorem B1420299 : Blo 1419529 1420299 := bstep (se 1 (by rfl) ⟨1065224, by rfl⟩ : syracuseStep 1420299 = 2130449) B2130449
theorem B1420311 : Blo 1419529 1420311 := bstep (se 1 (by rfl) ⟨1065233, by rfl⟩ : syracuseStep 1420311 = 2130467) B2130467
theorem B4795415 : Blo 1419529 4795415 := bstep (se 1 (by rfl) ⟨3596561, by rfl⟩ : syracuseStep 4795415 = 7193123) B7193123
theorem B2698265 : Blo 1419529 2698265 := bstep (se 2 (by rfl) ⟨1011849, by rfl⟩ : syracuseStep 2698265 = 2023699) B2023699
theorem B1420331 : Blo 1419529 1420331 := bstep (se 1 (by rfl) ⟨1065248, by rfl⟩ : syracuseStep 1420331 = 2130497) B2130497
theorem B1420343 : Blo 1419529 1420343 := bstep (se 1 (by rfl) ⟨1065257, by rfl⟩ : syracuseStep 1420343 = 2130515) B2130515
theorem B1420363 : Blo 1419529 1420363 := bstep (se 1 (by rfl) ⟨1065272, by rfl⟩ : syracuseStep 1420363 = 2130545) B2130545
theorem B1420375 : Blo 1419529 1420375 := bstep (se 1 (by rfl) ⟨1065281, by rfl⟩ : syracuseStep 1420375 = 2130563) B2130563
theorem B2878553 : Blo 1419529 2878553 := bstep (se 2 (by rfl) ⟨1079457, by rfl⟩ : syracuseStep 2878553 = 2158915) B2158915
theorem B3198041 : Blo 1419529 3198041 := bstep (se 2 (by rfl) ⟨1199265, by rfl⟩ : syracuseStep 3198041 = 2398531) B2398531
theorem B1420395 : Blo 1419529 1420395 := bstep (se 1 (by rfl) ⟨1065296, by rfl⟩ : syracuseStep 1420395 = 2130593) B2130593
theorem B1420407 : Blo 1419529 1420407 := bstep (se 1 (by rfl) ⟨1065305, by rfl⟩ : syracuseStep 1420407 = 2130611) B2130611
theorem B1420427 : Blo 1419529 1420427 := bstep (se 1 (by rfl) ⟨1065320, by rfl⟩ : syracuseStep 1420427 = 2130641) B2130641
theorem B1420439 : Blo 1419529 1420439 := bstep (se 1 (by rfl) ⟨1065329, by rfl⟩ : syracuseStep 1420439 = 2130659) B2130659
theorem B1420459 : Blo 1419529 1420459 := bstep (se 1 (by rfl) ⟨1065344, by rfl⟩ : syracuseStep 1420459 = 2130689) B2130689
theorem B10792115 : Blo 1419529 10792115 := bstep (se 1 (by rfl) ⟨8094086, by rfl⟩ : syracuseStep 10792115 = 16188173) B16188173
theorem B3198131 : Blo 1419529 3198131 := bstep (se 1 (by rfl) ⟨2398598, by rfl⟩ : syracuseStep 3198131 = 4797197) B4797197
theorem B1420471 : Blo 1419529 1420471 := bstep (se 1 (by rfl) ⟨1065353, by rfl⟩ : syracuseStep 1420471 = 2130707) B2130707
theorem B1420491 : Blo 1419529 1420491 := bstep (se 1 (by rfl) ⟨1065368, by rfl⟩ : syracuseStep 1420491 = 2130737) B2130737
theorem B1420503 : Blo 1419529 1420503 := bstep (se 1 (by rfl) ⟨1065377, by rfl⟩ : syracuseStep 1420503 = 2130755) B2130755
theorem B3198167 : Blo 1419529 3198167 := bstep (se 1 (by rfl) ⟨2398625, by rfl⟩ : syracuseStep 3198167 = 4797251) B4797251
theorem B1420523 : Blo 1419529 1420523 := bstep (se 1 (by rfl) ⟨1065392, by rfl⟩ : syracuseStep 1420523 = 2130785) B2130785
theorem B1420535 : Blo 1419529 1420535 := bstep (se 1 (by rfl) ⟨1065401, by rfl⟩ : syracuseStep 1420535 = 2130803) B2130803
theorem B1420555 : Blo 1419529 1420555 := bstep (se 1 (by rfl) ⟨1065416, by rfl⟩ : syracuseStep 1420555 = 2130833) B2130833
theorem B2772235 : Blo 1419529 2772235 := bstep (se 1 (by rfl) ⟨2079176, by rfl⟩ : syracuseStep 2772235 = 4158353) B4158353
theorem B1420567 : Blo 1419529 1420567 := bstep (se 1 (by rfl) ⟨1065425, by rfl⟩ : syracuseStep 1420567 = 2130851) B2130851
theorem B1420587 : Blo 1419529 1420587 := bstep (se 1 (by rfl) ⟨1065440, by rfl⟩ : syracuseStep 1420587 = 2130881) B2130881
theorem B1420599 : Blo 1419529 1420599 := bstep (se 1 (by rfl) ⟨1065449, by rfl⟩ : syracuseStep 1420599 = 2130899) B2130899
theorem B7187777 : Blo 1419529 7187777 := bstep (se 2 (by rfl) ⟨2695416, by rfl⟩ : syracuseStep 7187777 = 5390833) B5390833
theorem B1420619 : Blo 1419529 1420619 := bstep (se 1 (by rfl) ⟨1065464, by rfl⟩ : syracuseStep 1420619 = 2130929) B2130929
theorem B1420631 : Blo 1419529 1420631 := bstep (se 1 (by rfl) ⟨1065473, by rfl⟩ : syracuseStep 1420631 = 2130947) B2130947
theorem B1420651 : Blo 1419529 1420651 := bstep (se 1 (by rfl) ⟨1065488, by rfl⟩ : syracuseStep 1420651 = 2130977) B2130977
theorem B1420663 : Blo 1419529 1420663 := bstep (se 1 (by rfl) ⟨1065497, by rfl⟩ : syracuseStep 1420663 = 2130995) B2130995
theorem B1420683 : Blo 1419529 1420683 := bstep (se 1 (by rfl) ⟨1065512, by rfl⟩ : syracuseStep 1420683 = 2131025) B2131025
theorem B3198347 : Blo 1419529 3198347 := bstep (se 1 (by rfl) ⟨2398760, by rfl⟩ : syracuseStep 3198347 = 4797521) B4797521
theorem B1420695 : Blo 1419529 1420695 := bstep (se 1 (by rfl) ⟨1065521, by rfl⟩ : syracuseStep 1420695 = 2131043) B2131043
theorem B1420715 : Blo 1419529 1420715 := bstep (se 1 (by rfl) ⟨1065536, by rfl⟩ : syracuseStep 1420715 = 2131073) B2131073
theorem B5615021 : Blo 1419529 5615021 := bstep (se 3 (by rfl) ⟨1052816, by rfl⟩ : syracuseStep 5615021 = 2105633) B2105633
theorem B12307889 : Blo 1419529 12307889 := bstep (se 2 (by rfl) ⟨4615458, by rfl⟩ : syracuseStep 12307889 = 9230917) B9230917
theorem B10235315 : Blo 1419529 10235315 := bstep (se 1 (by rfl) ⟨7676486, by rfl⟩ : syracuseStep 10235315 = 15352973) B15352973
theorem B1420727 : Blo 1419529 1420727 := bstep (se 1 (by rfl) ⟨1065545, by rfl⟩ : syracuseStep 1420727 = 2131091) B2131091
theorem B3198401 : Blo 1419529 3198401 := bstep (se 2 (by rfl) ⟨1199400, by rfl⟩ : syracuseStep 3198401 = 2398801) B2398801
theorem B2395595 : Blo 1419529 2395595 := bstep (se 1 (by rfl) ⟨1796696, by rfl⟩ : syracuseStep 2395595 = 3593393) B3593393
theorem B1420747 : Blo 1419529 1420747 := bstep (se 1 (by rfl) ⟨1065560, by rfl⟩ : syracuseStep 1420747 = 2131121) B2131121
theorem B10939853 : Blo 1419529 10939853 := bstep (se 3 (by rfl) ⟨2051222, by rfl⟩ : syracuseStep 10939853 = 4102445) B4102445
theorem B1420759 : Blo 1419529 1420759 := bstep (se 1 (by rfl) ⟨1065569, by rfl⟩ : syracuseStep 1420759 = 2131139) B2131139
theorem B1420779 : Blo 1419529 1420779 := bstep (se 1 (by rfl) ⟨1065584, by rfl⟩ : syracuseStep 1420779 = 2131169) B2131169
theorem B1420791 : Blo 1419529 1420791 := bstep (se 1 (by rfl) ⟨1065593, by rfl⟩ : syracuseStep 1420791 = 2131187) B2131187
theorem B1797643 : Blo 1419529 1797643 := bstep (se 1 (by rfl) ⟨1348232, by rfl⟩ : syracuseStep 1797643 = 2696465) B2696465
theorem B1420811 : Blo 1419529 1420811 := bstep (se 1 (by rfl) ⟨1065608, by rfl⟩ : syracuseStep 1420811 = 2131217) B2131217
theorem B1420823 : Blo 1419529 1420823 := bstep (se 1 (by rfl) ⟨1065617, by rfl⟩ : syracuseStep 1420823 = 2131235) B2131235
theorem B1420843 : Blo 1419529 1420843 := bstep (se 1 (by rfl) ⟨1065632, by rfl⟩ : syracuseStep 1420843 = 2131265) B2131265
theorem B4795955 : Blo 1419529 4795955 := bstep (se 1 (by rfl) ⟨3596966, by rfl⟩ : syracuseStep 4795955 = 7193933) B7193933
theorem B1420855 : Blo 1419529 1420855 := bstep (se 1 (by rfl) ⟨1065641, by rfl⟩ : syracuseStep 1420855 = 2131283) B2131283
theorem B2395723 : Blo 1419529 2395723 := bstep (se 1 (by rfl) ⟨1796792, by rfl⟩ : syracuseStep 2395723 = 3593585) B3593585
theorem B1420875 : Blo 1419529 1420875 := bstep (se 1 (by rfl) ⟨1065656, by rfl⟩ : syracuseStep 1420875 = 2131313) B2131313
theorem B1420887 : Blo 1419529 1420887 := bstep (se 1 (by rfl) ⟨1065665, by rfl⟩ : syracuseStep 1420887 = 2131331) B2131331
theorem B4099673 : Blo 1419529 4099673 := bstep (se 2 (by rfl) ⟨1537377, by rfl⟩ : syracuseStep 4099673 = 3074755) B3074755
theorem B22171229 : Blo 1419529 22171229 := bstep (se 3 (by rfl) ⟨4157105, by rfl⟩ : syracuseStep 22171229 = 8314211) B8314211
theorem B1420907 : Blo 1419529 1420907 := bstep (se 1 (by rfl) ⟨1065680, by rfl⟩ : syracuseStep 1420907 = 2131361) B2131361
theorem B1420919 : Blo 1419529 1420919 := bstep (se 1 (by rfl) ⟨1065689, by rfl⟩ : syracuseStep 1420919 = 2131379) B2131379
theorem B1420939 : Blo 1419529 1420939 := bstep (se 1 (by rfl) ⟨1065704, by rfl⟩ : syracuseStep 1420939 = 2131409) B2131409
theorem B1420951 : Blo 1419529 1420951 := bstep (se 1 (by rfl) ⟨1065713, by rfl⟩ : syracuseStep 1420951 = 2131427) B2131427
theorem B1420971 : Blo 1419529 1420971 := bstep (se 1 (by rfl) ⟨1065728, by rfl⟩ : syracuseStep 1420971 = 2131457) B2131457
theorem B2879155 : Blo 1419529 2879155 := bstep (se 1 (by rfl) ⟨2159366, by rfl⟩ : syracuseStep 2879155 = 4318733) B4318733
theorem B4992691 : Blo 1419529 4992691 := bstep (se 1 (by rfl) ⟨3744518, by rfl⟩ : syracuseStep 4992691 = 7489037) B7489037
theorem B1420983 : Blo 1419529 1420983 := bstep (se 1 (by rfl) ⟨1065737, by rfl⟩ : syracuseStep 1420983 = 2131475) B2131475
theorem B1421003 : Blo 1419529 1421003 := bstep (se 1 (by rfl) ⟨1065752, by rfl⟩ : syracuseStep 1421003 = 2131505) B2131505
theorem B1421015 : Blo 1419529 1421015 := bstep (se 1 (by rfl) ⟨1065761, by rfl⟩ : syracuseStep 1421015 = 2131523) B2131523
theorem B2395865 : Blo 1419529 2395865 := bstep (se 2 (by rfl) ⟨898449, by rfl⟩ : syracuseStep 2395865 = 1796899) B1796899
theorem B1421035 : Blo 1419529 1421035 := bstep (se 1 (by rfl) ⟨1065776, by rfl⟩ : syracuseStep 1421035 = 2131553) B2131553
theorem B1421047 : Blo 1419529 1421047 := bstep (se 1 (by rfl) ⟨1065785, by rfl⟩ : syracuseStep 1421047 = 2131571) B2131571
theorem B1421067 : Blo 1419529 1421067 := bstep (se 1 (by rfl) ⟨1065800, by rfl⟩ : syracuseStep 1421067 = 2131601) B2131601
theorem B1421079 : Blo 1419529 1421079 := bstep (se 1 (by rfl) ⟨1065809, by rfl⟩ : syracuseStep 1421079 = 2131619) B2131619
theorem B1421099 : Blo 1419529 1421099 := bstep (se 1 (by rfl) ⟨1065824, by rfl⟩ : syracuseStep 1421099 = 2131649) B2131649
theorem B5394221 : Blo 1419529 5394221 := bstep (se 3 (by rfl) ⟨1011416, by rfl⟩ : syracuseStep 5394221 = 2022833) B2022833
theorem B1421111 : Blo 1419529 1421111 := bstep (se 1 (by rfl) ⟨1065833, by rfl⟩ : syracuseStep 1421111 = 2131667) B2131667
theorem B4796225 : Blo 1419529 4796225 := bstep (se 2 (by rfl) ⟨1798584, by rfl⟩ : syracuseStep 4796225 = 3597169) B3597169
theorem B1421131 : Blo 1419529 1421131 := bstep (se 1 (by rfl) ⟨1065848, by rfl⟩ : syracuseStep 1421131 = 2131697) B2131697
theorem B1421143 : Blo 1419529 1421143 := bstep (se 1 (by rfl) ⟨1065857, by rfl⟩ : syracuseStep 1421143 = 2131715) B2131715
theorem B2395993 : Blo 1419529 2395993 := bstep (se 2 (by rfl) ⟨898497, by rfl⟩ : syracuseStep 2395993 = 1796995) B1796995
theorem B1421163 : Blo 1419529 1421163 := bstep (se 1 (by rfl) ⟨1065872, by rfl⟩ : syracuseStep 1421163 = 2131745) B2131745
theorem B1421175 : Blo 1419529 1421175 := bstep (se 1 (by rfl) ⟨1065881, by rfl⟩ : syracuseStep 1421175 = 2131763) B2131763
theorem B1421195 : Blo 1419529 1421195 := bstep (se 1 (by rfl) ⟨1065896, by rfl⟩ : syracuseStep 1421195 = 2131793) B2131793
theorem B1421207 : Blo 1419529 1421207 := bstep (se 1 (by rfl) ⟨1065905, by rfl⟩ : syracuseStep 1421207 = 2131811) B2131811
theorem B1421227 : Blo 1419529 1421227 := bstep (se 1 (by rfl) ⟨1065920, by rfl⟩ : syracuseStep 1421227 = 2131841) B2131841
theorem B15175603 : Blo 1419529 15175603 := bstep (se 1 (by rfl) ⟨11381702, by rfl⟩ : syracuseStep 15175603 = 22763405) B22763405
theorem B1421239 : Blo 1419529 1421239 := bstep (se 1 (by rfl) ⟨1065929, by rfl⟩ : syracuseStep 1421239 = 2131859) B2131859
theorem B4550593 : Blo 1419529 4550593 := bstep (se 2 (by rfl) ⟨1706472, by rfl⟩ : syracuseStep 4550593 = 3412945) B3412945
theorem B1421259 : Blo 1419529 1421259 := bstep (se 1 (by rfl) ⟨1065944, by rfl⟩ : syracuseStep 1421259 = 2131889) B2131889
theorem B1421271 : Blo 1419529 1421271 := bstep (se 1 (by rfl) ⟨1065953, by rfl⟩ : syracuseStep 1421271 = 2131907) B2131907
theorem B2461657 : Blo 1419529 2461657 := bstep (se 2 (by rfl) ⟨923121, by rfl⟩ : syracuseStep 2461657 = 1846243) B1846243
theorem B1421291 : Blo 1419529 1421291 := bstep (se 1 (by rfl) ⟨1065968, by rfl⟩ : syracuseStep 1421291 = 2131937) B2131937
theorem B1421303 : Blo 1419529 1421303 := bstep (se 1 (by rfl) ⟨1065977, by rfl⟩ : syracuseStep 1421303 = 2131955) B2131955
theorem B1421323 : Blo 1419529 1421323 := bstep (se 1 (by rfl) ⟨1065992, by rfl⟩ : syracuseStep 1421323 = 2131985) B2131985
theorem B1421335 : Blo 1419529 1421335 := bstep (se 1 (by rfl) ⟨1066001, by rfl⟩ : syracuseStep 1421335 = 2132003) B2132003
theorem B1421355 : Blo 1419529 1421355 := bstep (se 1 (by rfl) ⟨1066016, by rfl⟩ : syracuseStep 1421355 = 2132033) B2132033
theorem B1421367 : Blo 1419529 1421367 := bstep (se 1 (by rfl) ⟨1066025, by rfl⟩ : syracuseStep 1421367 = 2132051) B2132051
theorem B1421387 : Blo 1419529 1421387 := bstep (se 1 (by rfl) ⟨1066040, by rfl⟩ : syracuseStep 1421387 = 2132081) B2132081
theorem B1421399 : Blo 1419529 1421399 := bstep (se 1 (by rfl) ⟨1066049, by rfl⟩ : syracuseStep 1421399 = 2132099) B2132099
theorem B1421419 : Blo 1419529 1421419 := bstep (se 1 (by rfl) ⟨1066064, by rfl⟩ : syracuseStep 1421419 = 2132129) B2132129
theorem B1421431 : Blo 1419529 1421431 := bstep (se 1 (by rfl) ⟨1066073, by rfl⟩ : syracuseStep 1421431 = 2132147) B2132147
theorem B1421451 : Blo 1419529 1421451 := bstep (se 1 (by rfl) ⟨1066088, by rfl⟩ : syracuseStep 1421451 = 2132177) B2132177
theorem B1421463 : Blo 1419529 1421463 := bstep (se 1 (by rfl) ⟨1066097, by rfl⟩ : syracuseStep 1421463 = 2132195) B2132195
theorem B1421483 : Blo 1419529 1421483 := bstep (se 1 (by rfl) ⟨1066112, by rfl⟩ : syracuseStep 1421483 = 2132225) B2132225
theorem B1421495 : Blo 1419529 1421495 := bstep (se 1 (by rfl) ⟨1066121, by rfl⟩ : syracuseStep 1421495 = 2132243) B2132243
theorem B1421515 : Blo 1419529 1421515 := bstep (se 1 (by rfl) ⟨1066136, by rfl⟩ : syracuseStep 1421515 = 2132273) B2132273
theorem B3035351 : Blo 1419529 3035351 := bstep (se 1 (by rfl) ⟨2276513, by rfl⟩ : syracuseStep 3035351 = 4553027) B4553027
theorem B1421527 : Blo 1419529 1421527 := bstep (se 1 (by rfl) ⟨1066145, by rfl⟩ : syracuseStep 1421527 = 2132291) B2132291
theorem B2560243 : Blo 1419529 2560243 := bstep (se 1 (by rfl) ⟨1920182, by rfl⟩ : syracuseStep 2560243 = 3840365) B3840365
theorem B4796765 : Blo 1419529 4796765 := bstep (se 3 (by rfl) ⟨899393, by rfl⟩ : syracuseStep 4796765 = 1798787) B1798787
theorem B2396567 : Blo 1419529 2396567 := bstep (se 1 (by rfl) ⟨1797425, by rfl⟩ : syracuseStep 2396567 = 3594851) B3594851
theorem B1798615 : Blo 1419529 1798615 := bstep (se 1 (by rfl) ⟨1348961, by rfl⟩ : syracuseStep 1798615 = 2697923) B2697923
theorem B3035659 : Blo 1419529 3035659 := bstep (se 1 (by rfl) ⟨2276744, by rfl⟩ : syracuseStep 3035659 = 4553489) B4553489
theorem B2396695 : Blo 1419529 2396695 := bstep (se 1 (by rfl) ⟨1797521, by rfl⟩ : syracuseStep 2396695 = 3595043) B3595043
theorem B5394995 : Blo 1419529 5394995 := bstep (se 1 (by rfl) ⟨4046246, by rfl⟩ : syracuseStep 5394995 = 8092493) B8092493
theorem B4043353 : Blo 1419529 4043353 := bstep (se 2 (by rfl) ⟨1516257, by rfl⟩ : syracuseStep 4043353 = 3032515) B3032515
theorem B9097829 : Blo 1419529 9097829 := bstep (se 4 (by rfl) ⟨852921, by rfl⟩ : syracuseStep 9097829 = 1705843) B1705843
theorem B10793573 : Blo 1419529 10793573 := bstep (se 4 (by rfl) ⟨1011897, by rfl⟩ : syracuseStep 10793573 = 2023795) B2023795
theorem B6828695 : Blo 1419529 6828695 := bstep (se 1 (by rfl) ⟨5121521, by rfl⟩ : syracuseStep 6828695 = 10243043) B10243043
theorem B98587363 : Blo 1419529 98587363 := bstep (se 1 (by rfl) ⟨73940522, by rfl⟩ : syracuseStep 98587363 = 147881045) B147881045
theorem B630477553 : Blo 1419529 630477553 := bstep (se 2 (by rfl) ⟨236429082, by rfl⟩ : syracuseStep 630477553 = 472858165) B472858165
theorem B7680899 : Blo 1419529 7680899 := bstep (se 1 (by rfl) ⟨5760674, by rfl⟩ : syracuseStep 7680899 = 11521349) B11521349
theorem B3240947 : Blo 1419529 3240947 := bstep (se 1 (by rfl) ⟨2430710, by rfl⟩ : syracuseStep 3240947 = 4861421) B4861421
theorem B10785797 : Blo 1419529 10785797 := bstep (se 4 (by rfl) ⟨1011168, by rfl⟩ : syracuseStep 10785797 = 2022337) B2022337
theorem B6067217 : Blo 1419529 6067217 := bstep (se 2 (by rfl) ⟨2275206, by rfl⟩ : syracuseStep 6067217 = 4550413) B4550413
theorem B3593281 : Blo 1419529 3593281 := bstep (se 2 (by rfl) ⟨1347480, by rfl⟩ : syracuseStep 3593281 = 2694961) B2694961
theorem B9098315 : Blo 1419529 9098315 := bstep (se 1 (by rfl) ⟨6823736, by rfl⟩ : syracuseStep 9098315 = 13647473) B13647473
theorem B10794059 : Blo 1419529 10794059 := bstep (se 1 (by rfl) ⟨8095544, by rfl⟩ : syracuseStep 10794059 = 16191089) B16191089
theorem B4322393 : Blo 1419529 4322393 := bstep (se 2 (by rfl) ⟨1620897, by rfl⟩ : syracuseStep 4322393 = 3241795) B3241795
theorem B2397323 : Blo 1419529 2397323 := bstep (se 1 (by rfl) ⟨1797992, by rfl⟩ : syracuseStep 2397323 = 3595985) B3595985
theorem B3282113 : Blo 1419529 3282113 := bstep (se 2 (by rfl) ⟨1230792, by rfl⟩ : syracuseStep 3282113 = 2461585) B2461585
theorem B4043969 : Blo 1419529 4043969 := bstep (se 2 (by rfl) ⟨1516488, by rfl⟩ : syracuseStep 4043969 = 3032977) B3032977
theorem B7189721 : Blo 1419529 7189721 := bstep (se 2 (by rfl) ⟨2696145, by rfl⟩ : syracuseStep 7189721 = 5392291) B5392291
theorem B2397451 : Blo 1419529 2397451 := bstep (se 1 (by rfl) ⟨1798088, by rfl⟩ : syracuseStep 2397451 = 3596177) B3596177
theorem B10245527 : Blo 1419529 10245527 := bstep (se 1 (by rfl) ⟨7684145, by rfl⟩ : syracuseStep 10245527 = 15368291) B15368291
theorem B2397593 : Blo 1419529 2397593 := bstep (se 2 (by rfl) ⟨899097, by rfl⟩ : syracuseStep 2397593 = 1798195) B1798195
theorem B2430361 : Blo 1419529 2430361 := bstep (se 2 (by rfl) ⟨911385, by rfl⟩ : syracuseStep 2430361 = 1822771) B1822771
theorem B2397721 : Blo 1419529 2397721 := bstep (se 2 (by rfl) ⟨899145, by rfl⟩ : syracuseStep 2397721 = 1798291) B1798291
theorem B3593879 : Blo 1419529 3593879 := bstep (se 1 (by rfl) ⟨2695409, by rfl⟩ : syracuseStep 3593879 = 5390819) B5390819
theorem B10245811 : Blo 1419529 10245811 := bstep (se 1 (by rfl) ⟨7684358, by rfl⟩ : syracuseStep 10245811 = 15368717) B15368717
theorem B1439435 : Blo 1419529 1439435 := bstep (se 1 (by rfl) ⟨1079576, by rfl⟩ : syracuseStep 1439435 = 2159153) B2159153
theorem B8091353 : Blo 1419529 8091353 := bstep (se 2 (by rfl) ⟨3034257, by rfl⟩ : syracuseStep 8091353 = 6068515) B6068515
theorem B6068141 : Blo 1419529 6068141 := bstep (se 3 (by rfl) ⟨1137776, by rfl⟩ : syracuseStep 6068141 = 2275553) B2275553
theorem B24262577 : Blo 1419529 24262577 := bstep (se 2 (by rfl) ⟨9098466, by rfl⟩ : syracuseStep 24262577 = 18196933) B18196933
theorem B16627673 : Blo 1419529 16627673 := bstep (se 2 (by rfl) ⟨6235377, by rfl⟩ : syracuseStep 16627673 = 12470755) B12470755
theorem B5396483 : Blo 1419529 5396483 := bstep (se 1 (by rfl) ⟨4047362, by rfl⟩ : syracuseStep 5396483 = 8094725) B8094725
theorem B2398295 : Blo 1419529 2398295 := bstep (se 1 (by rfl) ⟨1798721, by rfl⟩ : syracuseStep 2398295 = 3597443) B3597443
theorem B2398423 : Blo 1419529 2398423 := bstep (se 1 (by rfl) ⟨1798817, by rfl⟩ : syracuseStep 2398423 = 3597635) B3597635
theorem B2734411 : Blo 1419529 2734411 := bstep (se 1 (by rfl) ⟨2050808, by rfl⟩ : syracuseStep 2734411 = 4101617) B4101617
theorem B47356273 : Blo 1419529 47356273 := bstep (se 2 (by rfl) ⟨17758602, by rfl⟩ : syracuseStep 47356273 = 35517205) B35517205
theorem B49174901 : Blo 1419529 49174901 := bstep (se 5 (by rfl) ⟨2305073, by rfl⟩ : syracuseStep 49174901 = 4610147) B4610147
theorem B3594689 : Blo 1419529 3594689 := bstep (se 2 (by rfl) ⟨1348008, by rfl⟩ : syracuseStep 3594689 = 2696017) B2696017
theorem B5396939 : Blo 1419529 5396939 := bstep (se 1 (by rfl) ⟨4047704, by rfl⟩ : syracuseStep 5396939 = 8095409) B8095409
theorem B7682521 : Blo 1419529 7682521 := bstep (se 2 (by rfl) ⟨2880945, by rfl⟩ : syracuseStep 7682521 = 5761891) B5761891
theorem B1440299 : Blo 1419529 1440299 := bstep (se 1 (by rfl) ⟨1080224, by rfl⟩ : syracuseStep 1440299 = 2160449) B2160449
theorem B5397137 : Blo 1419529 5397137 := bstep (se 2 (by rfl) ⟨2023926, by rfl⟩ : syracuseStep 5397137 = 4047853) B4047853
theorem B2022041 : Blo 1419529 2022041 := bstep (se 2 (by rfl) ⟨758265, by rfl⟩ : syracuseStep 2022041 = 1516531) B1516531
theorem B4790987 : Blo 1419529 4790987 := bstep (se 1 (by rfl) ⟨3593240, by rfl⟩ : syracuseStep 4790987 = 7186481) B7186481
theorem B4553437 : Blo 1419529 4553437 := bstep (se 3 (by rfl) ⟨853769, by rfl⟩ : syracuseStep 4553437 = 1707539) B1707539
theorem B7191341 : Blo 1419529 7191341 := bstep (se 3 (by rfl) ⟨1348376, by rfl⟩ : syracuseStep 7191341 = 2696753) B2696753
theorem B6478643 : Blo 1419529 6478643 := bstep (se 1 (by rfl) ⟨4858982, by rfl⟩ : syracuseStep 6478643 = 9717965) B9717965
theorem B5118913 : Blo 1419529 5118913 := bstep (se 2 (by rfl) ⟨1919592, by rfl⟩ : syracuseStep 5118913 = 3839185) B3839185
theorem B4791257 : Blo 1419529 4791257 := bstep (se 2 (by rfl) ⟨1796721, by rfl⟩ : syracuseStep 4791257 = 3593443) B3593443
theorem B3595225 : Blo 1419529 3595225 := bstep (se 2 (by rfl) ⟨1348209, by rfl⟩ : syracuseStep 3595225 = 2696419) B2696419
theorem B3194009 : Blo 1419529 3194009 := bstep (se 2 (by rfl) ⟨1197753, by rfl⟩ : syracuseStep 3194009 = 2395507) B2395507
theorem B4046041 : Blo 1419529 4046041 := bstep (se 2 (by rfl) ⟨1517265, by rfl⟩ : syracuseStep 4046041 = 3034531) B3034531
theorem B4611293 : Blo 1419529 4611293 := bstep (se 3 (by rfl) ⟨864617, by rfl⟩ : syracuseStep 4611293 = 1729235) B1729235
theorem B3194099 : Blo 1419529 3194099 := bstep (se 1 (by rfl) ⟨2395574, by rfl⟩ : syracuseStep 3194099 = 4791149) B4791149
theorem B18455813 : Blo 1419529 18455813 := bstep (se 4 (by rfl) ⟨1730232, by rfl⟩ : syracuseStep 18455813 = 3460465) B3460465
theorem B3194135 : Blo 1419529 3194135 := bstep (se 1 (by rfl) ⟨2395601, by rfl⟩ : syracuseStep 3194135 = 4791203) B4791203
theorem B2022679 : Blo 1419529 2022679 := bstep (se 1 (by rfl) ⟨1517009, by rfl⟩ : syracuseStep 2022679 = 3034019) B3034019
theorem B8092993 : Blo 1419529 8092993 := bstep (se 2 (by rfl) ⟨3034872, by rfl⟩ : syracuseStep 8092993 = 6069745) B6069745
theorem B6069593 : Blo 1419529 6069593 := bstep (se 2 (by rfl) ⟨2276097, by rfl⟩ : syracuseStep 6069593 = 4552195) B4552195
theorem B2735489 : Blo 1419529 2735489 := bstep (se 2 (by rfl) ⟨1025808, by rfl⟩ : syracuseStep 2735489 = 2051617) B2051617
theorem B10788227 : Blo 1419529 10788227 := bstep (se 1 (by rfl) ⟨8091170, by rfl⟩ : syracuseStep 10788227 = 16182341) B16182341
theorem B2129303 : Blo 1419529 2129303 := bstep (se 1 (by rfl) ⟨1596977, by rfl⟩ : syracuseStep 2129303 = 3193955) B3193955
theorem B3194315 : Blo 1419529 3194315 := bstep (se 1 (by rfl) ⟨2395736, by rfl⟩ : syracuseStep 3194315 = 4791473) B4791473
theorem B2129369 : Blo 1419529 2129369 := bstep (se 2 (by rfl) ⟨798513, by rfl⟩ : syracuseStep 2129369 = 1597027) B1597027
theorem B3194369 : Blo 1419529 3194369 := bstep (se 2 (by rfl) ⟨1197888, by rfl⟩ : syracuseStep 3194369 = 2395777) B2395777
theorem B5840387 : Blo 1419529 5840387 := bstep (se 1 (by rfl) ⟨4380290, by rfl⟩ : syracuseStep 5840387 = 8760581) B8760581
theorem B5389847 : Blo 1419529 5389847 := bstep (se 1 (by rfl) ⟨4042385, by rfl⟩ : syracuseStep 5389847 = 8084771) B8084771
theorem B12959297 : Blo 1419529 12959297 := bstep (se 2 (by rfl) ⟨4859736, by rfl⟩ : syracuseStep 12959297 = 9719473) B9719473
theorem B2129483 : Blo 1419529 2129483 := bstep (se 1 (by rfl) ⟨1597112, by rfl⟩ : syracuseStep 2129483 = 3194225) B3194225
theorem B2129495 : Blo 1419529 2129495 := bstep (se 1 (by rfl) ⟨1597121, by rfl⟩ : syracuseStep 2129495 = 3194243) B3194243
theorem B4046429 : Blo 1419529 4046429 := bstep (se 3 (by rfl) ⟨758705, by rfl⟩ : syracuseStep 4046429 = 1517411) B1517411
theorem B4791959 : Blo 1419529 4791959 := bstep (se 1 (by rfl) ⟨3593969, by rfl⟩ : syracuseStep 4791959 = 7187939) B7187939
theorem B2129561 : Blo 1419529 2129561 := bstep (se 2 (by rfl) ⟨798585, by rfl⟩ : syracuseStep 2129561 = 1597171) B1597171
theorem B1597099 : Blo 1419529 1597099 := bstep (se 1 (by rfl) ⟨1197824, by rfl⟩ : syracuseStep 1597099 = 2395649) B2395649
theorem B3194585 : Blo 1419529 3194585 := bstep (se 2 (by rfl) ⟨1197969, by rfl⟩ : syracuseStep 3194585 = 2395939) B2395939
theorem B2129675 : Blo 1419529 2129675 := bstep (se 1 (by rfl) ⟨1597256, by rfl⟩ : syracuseStep 2129675 = 3194513) B3194513
theorem B1597207 : Blo 1419529 1597207 := bstep (se 1 (by rfl) ⟨1197905, by rfl⟩ : syracuseStep 1597207 = 2395811) B2395811
theorem B2129687 : Blo 1419529 2129687 := bstep (se 1 (by rfl) ⟨1597265, by rfl⟩ : syracuseStep 2129687 = 3194531) B3194531
theorem B10780451 : Blo 1419529 10780451 := bstep (se 1 (by rfl) ⟨8085338, by rfl⟩ : syracuseStep 10780451 = 16170677) B16170677
theorem B3194675 : Blo 1419529 3194675 := bstep (se 1 (by rfl) ⟨2396006, by rfl⟩ : syracuseStep 3194675 = 4792013) B4792013
theorem B3194711 : Blo 1419529 3194711 := bstep (se 1 (by rfl) ⟨2396033, by rfl⟩ : syracuseStep 3194711 = 4792067) B4792067
theorem B2129753 : Blo 1419529 2129753 := bstep (se 2 (by rfl) ⟨798657, by rfl⟩ : syracuseStep 2129753 = 1597315) B1597315
theorem B1597387 : Blo 1419529 1597387 := bstep (se 1 (by rfl) ⟨1198040, by rfl⟩ : syracuseStep 1597387 = 2396081) B2396081
theorem B2129867 : Blo 1419529 2129867 := bstep (se 1 (by rfl) ⟨1597400, by rfl⟩ : syracuseStep 2129867 = 3194801) B3194801
theorem B2129879 : Blo 1419529 2129879 := bstep (se 1 (by rfl) ⟨1597409, by rfl⟩ : syracuseStep 2129879 = 3194819) B3194819
theorem B2023385 : Blo 1419529 2023385 := bstep (se 2 (by rfl) ⟨758769, by rfl⟩ : syracuseStep 2023385 = 1517539) B1517539
theorem B2129927 : Blo 1419529 2129927 := bstep (se 1 (by rfl) ⟨1597445, by rfl⟩ : syracuseStep 2129927 = 3194891) B3194891
theorem B5390347 : Blo 1419529 5390347 := bstep (se 1 (by rfl) ⟨4042760, by rfl⟩ : syracuseStep 5390347 = 8085521) B8085521
theorem B2129963 : Blo 1419529 2129963 := bstep (se 1 (by rfl) ⟨1597472, by rfl⟩ : syracuseStep 2129963 = 3194945) B3194945
theorem B7192637 : Blo 1419529 7192637 := bstep (se 3 (by rfl) ⟨1348619, by rfl⟩ : syracuseStep 7192637 = 2697239) B2697239
theorem B2129993 : Blo 1419529 2129993 := bstep (se 2 (by rfl) ⟨798747, by rfl⟩ : syracuseStep 2129993 = 1597495) B1597495
theorem B3194999 : Blo 1419529 3194999 := bstep (se 1 (by rfl) ⟨2396249, by rfl⟩ : syracuseStep 3194999 = 4792499) B4792499
theorem B2130107 : Blo 1419529 2130107 := bstep (se 1 (by rfl) ⟨1597580, by rfl⟩ : syracuseStep 2130107 = 3195161) B3195161
theorem B2130167 : Blo 1419529 2130167 := bstep (se 1 (by rfl) ⟨1597625, by rfl⟩ : syracuseStep 2130167 = 3195251) B3195251
theorem B2130191 : Blo 1419529 2130191 := bstep (se 1 (by rfl) ⟨1597643, by rfl⟩ : syracuseStep 2130191 = 3195287) B3195287
theorem B1597711 : Blo 1419529 1597711 := bstep (se 1 (by rfl) ⟨1198283, by rfl⟩ : syracuseStep 1597711 = 2396567) B2396567
theorem B3195179 : Blo 1419529 3195179 := bstep (se 1 (by rfl) ⟨2396384, by rfl⟩ : syracuseStep 3195179 = 4792769) B4792769
theorem B2130233 : Blo 1419529 2130233 := bstep (se 2 (by rfl) ⟨798837, by rfl⟩ : syracuseStep 2130233 = 1597675) B1597675
theorem B5390651 : Blo 1419529 5390651 := bstep (se 1 (by rfl) ⟨4042988, by rfl⟩ : syracuseStep 5390651 = 8085977) B8085977
theorem B3596663 : Blo 1419529 3596663 := bstep (se 1 (by rfl) ⟨2697497, by rfl⟩ : syracuseStep 3596663 = 5394995) B5394995
theorem B2130311 : Blo 1419529 2130311 := bstep (se 1 (by rfl) ⟨1597733, by rfl⟩ : syracuseStep 2130311 = 3195467) B3195467
theorem B2130347 : Blo 1419529 2130347 := bstep (se 1 (by rfl) ⟨1597760, by rfl⟩ : syracuseStep 2130347 = 3195521) B3195521
theorem B3645881 : Blo 1419529 3645881 := bstep (se 2 (by rfl) ⟨1367205, by rfl⟩ : syracuseStep 3645881 = 2734411) B2734411
theorem B2130377 : Blo 1419529 2130377 := bstep (se 2 (by rfl) ⟨798891, by rfl⟩ : syracuseStep 2130377 = 1597783) B1597783
theorem B2130491 : Blo 1419529 2130491 := bstep (se 1 (by rfl) ⟨1597868, by rfl⟩ : syracuseStep 2130491 = 3195737) B3195737
theorem B8094269 : Blo 1419529 8094269 := bstep (se 3 (by rfl) ⟨1517675, by rfl⟩ : syracuseStep 8094269 = 3035351) B3035351
theorem B5120599 : Blo 1419529 5120599 := bstep (se 1 (by rfl) ⟨3840449, by rfl⟩ : syracuseStep 5120599 = 7680899) B7680899
theorem B2130551 : Blo 1419529 2130551 := bstep (se 1 (by rfl) ⟨1597913, by rfl⟩ : syracuseStep 2130551 = 3195827) B3195827
theorem B2130575 : Blo 1419529 2130575 := bstep (se 1 (by rfl) ⟨1597931, by rfl⟩ : syracuseStep 2130575 = 3195863) B3195863
theorem B3195539 : Blo 1419529 3195539 := bstep (se 1 (by rfl) ⟨2396654, by rfl⟩ : syracuseStep 3195539 = 4793309) B4793309
theorem B2130617 : Blo 1419529 2130617 := bstep (se 2 (by rfl) ⟨798981, by rfl⟩ : syracuseStep 2130617 = 1597963) B1597963
theorem B4047545 : Blo 1419529 4047545 := bstep (se 2 (by rfl) ⟨1517829, by rfl⟩ : syracuseStep 4047545 = 3035659) B3035659
theorem B3195593 : Blo 1419529 3195593 := bstep (se 2 (by rfl) ⟨1198347, by rfl⟩ : syracuseStep 3195593 = 2396695) B2396695
theorem B2130695 : Blo 1419529 2130695 := bstep (se 1 (by rfl) ⟨1598021, by rfl⟩ : syracuseStep 2130695 = 3196043) B3196043
theorem B1598215 : Blo 1419529 1598215 := bstep (se 1 (by rfl) ⟨1198661, by rfl⟩ : syracuseStep 1598215 = 2397323) B2397323
theorem B5391137 : Blo 1419529 5391137 := bstep (se 2 (by rfl) ⟨2021676, by rfl⟩ : syracuseStep 5391137 = 4043353) B4043353
theorem B58336037 : Blo 1419529 58336037 := bstep (se 4 (by rfl) ⟨5469003, by rfl⟩ : syracuseStep 58336037 = 10938007) B10938007
theorem B2188075 : Blo 1419529 2188075 := bstep (se 1 (by rfl) ⟨1641056, by rfl⟩ : syracuseStep 2188075 = 3282113) B3282113
theorem B2695979 : Blo 1419529 2695979 := bstep (se 1 (by rfl) ⟨2021984, by rfl⟩ : syracuseStep 2695979 = 4043969) B4043969
theorem B2130731 : Blo 1419529 2130731 := bstep (se 1 (by rfl) ⟨1598048, by rfl⟩ : syracuseStep 2130731 = 3196097) B3196097
theorem B4793147 : Blo 1419529 4793147 := bstep (se 1 (by rfl) ⟨3594860, by rfl⟩ : syracuseStep 4793147 = 7189721) B7189721
theorem B2130761 : Blo 1419529 2130761 := bstep (se 2 (by rfl) ⟨799035, by rfl⟩ : syracuseStep 2130761 = 1598071) B1598071
theorem B2130875 : Blo 1419529 2130875 := bstep (se 1 (by rfl) ⟨1598156, by rfl⟩ : syracuseStep 2130875 = 3196313) B3196313
theorem B1598395 : Blo 1419529 1598395 := bstep (se 1 (by rfl) ⟨1198796, by rfl⟩ : syracuseStep 1598395 = 2397593) B2397593
theorem B6071249 : Blo 1419529 6071249 := bstep (se 2 (by rfl) ⟨2276718, by rfl⟩ : syracuseStep 6071249 = 4553437) B4553437
theorem B131449817 : Blo 1419529 131449817 := bstep (se 2 (by rfl) ⟨49293681, by rfl⟩ : syracuseStep 131449817 = 98587363) B98587363
theorem B2130935 : Blo 1419529 2130935 := bstep (se 1 (by rfl) ⟨1598201, by rfl⟩ : syracuseStep 2130935 = 3196403) B3196403
theorem B2130959 : Blo 1419529 2130959 := bstep (se 1 (by rfl) ⟨1598219, by rfl⟩ : syracuseStep 2130959 = 3196439) B3196439
theorem B4047887 : Blo 1419529 4047887 := bstep (se 1 (by rfl) ⟨3035915, by rfl⟩ : syracuseStep 4047887 = 6071831) B6071831
theorem B2131001 : Blo 1419529 2131001 := bstep (se 2 (by rfl) ⟨799125, by rfl⟩ : syracuseStep 2131001 = 1598251) B1598251
theorem B2131079 : Blo 1419529 2131079 := bstep (se 1 (by rfl) ⟨1598309, by rfl⟩ : syracuseStep 2131079 = 3196619) B3196619
theorem B2131115 : Blo 1419529 2131115 := bstep (se 1 (by rfl) ⟨1598336, by rfl⟩ : syracuseStep 2131115 = 3196673) B3196673
theorem B2131145 : Blo 1419529 2131145 := bstep (se 2 (by rfl) ⟨799179, by rfl⟩ : syracuseStep 2131145 = 1598359) B1598359
theorem B6825217 : Blo 1419529 6825217 := bstep (se 2 (by rfl) ⟨2559456, by rfl⟩ : syracuseStep 6825217 = 5118913) B5118913
theorem B8094977 : Blo 1419529 8094977 := bstep (se 2 (by rfl) ⟨3035616, by rfl⟩ : syracuseStep 8094977 = 6071233) B6071233
theorem B4793633 : Blo 1419529 4793633 := bstep (se 2 (by rfl) ⟨1797612, by rfl⟩ : syracuseStep 4793633 = 3595225) B3595225
theorem B11085115 : Blo 1419529 11085115 := bstep (se 1 (by rfl) ⟨8313836, by rfl⟩ : syracuseStep 11085115 = 16627673) B16627673
theorem B2131259 : Blo 1419529 2131259 := bstep (se 1 (by rfl) ⟨1598444, by rfl⟩ : syracuseStep 2131259 = 3196889) B3196889
theorem B3597655 : Blo 1419529 3597655 := bstep (se 1 (by rfl) ⟨2698241, by rfl⟩ : syracuseStep 3597655 = 5396483) B5396483
theorem B2131319 : Blo 1419529 2131319 := bstep (se 1 (by rfl) ⟨1598489, by rfl⟩ : syracuseStep 2131319 = 3196979) B3196979
theorem B3196295 : Blo 1419529 3196295 := bstep (se 1 (by rfl) ⟨2397221, by rfl⟩ : syracuseStep 3196295 = 4794443) B4794443
theorem B2131343 : Blo 1419529 2131343 := bstep (se 1 (by rfl) ⟨1598507, by rfl⟩ : syracuseStep 2131343 = 3197015) B3197015
theorem B1598863 : Blo 1419529 1598863 := bstep (se 1 (by rfl) ⟨1199147, by rfl⟩ : syracuseStep 1598863 = 2398295) B2398295
theorem B2131385 : Blo 1419529 2131385 := bstep (se 2 (by rfl) ⟨799269, by rfl⟩ : syracuseStep 2131385 = 1598539) B1598539
theorem B2131463 : Blo 1419529 2131463 := bstep (se 1 (by rfl) ⟨1598597, by rfl⟩ : syracuseStep 2131463 = 3197195) B3197195
theorem B2131499 : Blo 1419529 2131499 := bstep (se 1 (by rfl) ⟨1598624, by rfl⟩ : syracuseStep 2131499 = 3197249) B3197249
theorem B3032635 : Blo 1419529 3032635 := bstep (se 1 (by rfl) ⟨2274476, by rfl⟩ : syracuseStep 3032635 = 4548953) B4548953
theorem B3196475 : Blo 1419529 3196475 := bstep (se 1 (by rfl) ⟨2397356, by rfl⟩ : syracuseStep 3196475 = 4794713) B4794713
theorem B2131529 : Blo 1419529 2131529 := bstep (se 2 (by rfl) ⟨799323, by rfl⟩ : syracuseStep 2131529 = 1598647) B1598647
theorem B3597959 : Blo 1419529 3597959 := bstep (se 1 (by rfl) ⟨2698469, by rfl⟩ : syracuseStep 3597959 = 5396939) B5396939
theorem B3196601 : Blo 1419529 3196601 := bstep (se 2 (by rfl) ⟨1198725, by rfl⟩ : syracuseStep 3196601 = 2397451) B2397451
theorem B3696313 : Blo 1419529 3696313 := bstep (se 2 (by rfl) ⟨1386117, by rfl⟩ : syracuseStep 3696313 = 2772235) B2772235
theorem B2131643 : Blo 1419529 2131643 := bstep (se 1 (by rfl) ⟨1598732, by rfl⟩ : syracuseStep 2131643 = 3197465) B3197465
theorem B2696905 : Blo 1419529 2696905 := bstep (se 2 (by rfl) ⟨1011339, by rfl⟩ : syracuseStep 2696905 = 2022679) B2022679
theorem B5392109 : Blo 1419529 5392109 := bstep (se 3 (by rfl) ⟨1011020, by rfl⟩ : syracuseStep 5392109 = 2022041) B2022041
theorem B2131703 : Blo 1419529 2131703 := bstep (se 1 (by rfl) ⟨1598777, by rfl⟩ : syracuseStep 2131703 = 3197555) B3197555
theorem B10790657 : Blo 1419529 10790657 := bstep (se 2 (by rfl) ⟨4046496, by rfl⟩ : syracuseStep 10790657 = 8092993) B8092993
theorem B3598091 : Blo 1419529 3598091 := bstep (se 1 (by rfl) ⟨2698568, by rfl⟩ : syracuseStep 3598091 = 5397137) B5397137
theorem B2131727 : Blo 1419529 2131727 := bstep (se 1 (by rfl) ⟨1598795, by rfl⟩ : syracuseStep 2131727 = 3197591) B3197591
theorem B7194419 : Blo 1419529 7194419 := bstep (se 1 (by rfl) ⟨5395814, by rfl⟩ : syracuseStep 7194419 = 10791629) B10791629
theorem B2131769 : Blo 1419529 2131769 := bstep (se 2 (by rfl) ⟨799413, by rfl⟩ : syracuseStep 2131769 = 1598827) B1598827
theorem B3032891 : Blo 1419529 3032891 := bstep (se 1 (by rfl) ⟨2274668, by rfl⟩ : syracuseStep 3032891 = 4549337) B4549337
theorem B4794227 : Blo 1419529 4794227 := bstep (se 1 (by rfl) ⟨3595670, by rfl⟩ : syracuseStep 4794227 = 7191341) B7191341
theorem B4319095 : Blo 1419529 4319095 := bstep (se 1 (by rfl) ⟨3239321, by rfl⟩ : syracuseStep 4319095 = 6478643) B6478643
theorem B2131847 : Blo 1419529 2131847 := bstep (se 1 (by rfl) ⟨1598885, by rfl⟩ : syracuseStep 2131847 = 3197771) B3197771
theorem B2131883 : Blo 1419529 2131883 := bstep (se 1 (by rfl) ⟨1598912, by rfl⟩ : syracuseStep 2131883 = 3197825) B3197825
theorem B2131913 : Blo 1419529 2131913 := bstep (se 2 (by rfl) ⟨799467, by rfl⟩ : syracuseStep 2131913 = 1598935) B1598935
theorem B3196943 : Blo 1419529 3196943 := bstep (se 1 (by rfl) ⟨2397707, by rfl⟩ : syracuseStep 3196943 = 4795415) B4795415
theorem B3196961 : Blo 1419529 3196961 := bstep (se 2 (by rfl) ⟨1198860, by rfl⟩ : syracuseStep 3196961 = 2397721) B2397721
theorem B1919035 : Blo 1419529 1919035 := bstep (se 1 (by rfl) ⟨1439276, by rfl⟩ : syracuseStep 1919035 = 2878553) B2878553
theorem B2132027 : Blo 1419529 2132027 := bstep (se 1 (by rfl) ⟨1599020, by rfl⟩ : syracuseStep 2132027 = 3198041) B3198041
theorem B7194743 : Blo 1419529 7194743 := bstep (se 1 (by rfl) ⟨5396057, by rfl⟩ : syracuseStep 7194743 = 10792115) B10792115
theorem B2132087 : Blo 1419529 2132087 := bstep (se 1 (by rfl) ⟨1599065, by rfl⟩ : syracuseStep 2132087 = 3198131) B3198131
theorem B2132111 : Blo 1419529 2132111 := bstep (se 1 (by rfl) ⟨1599083, by rfl⟩ : syracuseStep 2132111 = 3198167) B3198167
theorem B3074195 : Blo 1419529 3074195 := bstep (se 1 (by rfl) ⟨2305646, by rfl⟩ : syracuseStep 3074195 = 4611293) B4611293
theorem B2558137 : Blo 1419529 2558137 := bstep (se 2 (by rfl) ⟨959301, by rfl⟩ : syracuseStep 2558137 = 1918603) B1918603
theorem B2132153 : Blo 1419529 2132153 := bstep (se 2 (by rfl) ⟨799557, by rfl⟩ : syracuseStep 2132153 = 1599115) B1599115
theorem B2132231 : Blo 1419529 2132231 := bstep (se 1 (by rfl) ⟨1599173, by rfl⟩ : syracuseStep 2132231 = 3198347) B3198347
theorem B1419535 : Blo 1419529 1419535 := bstep (se 1 (by rfl) ⟨1064651, by rfl⟩ : syracuseStep 1419535 = 2129303) B2129303
theorem B2132267 : Blo 1419529 2132267 := bstep (se 1 (by rfl) ⟨1599200, by rfl⟩ : syracuseStep 2132267 = 3198401) B3198401
theorem B7293235 : Blo 1419529 7293235 := bstep (se 1 (by rfl) ⟨5469926, by rfl⟩ : syracuseStep 7293235 = 10939853) B10939853
theorem B1419579 : Blo 1419529 1419579 := bstep (se 1 (by rfl) ⟨1064684, by rfl⟩ : syracuseStep 1419579 = 2129369) B2129369
theorem B3893591 : Blo 1419529 3893591 := bstep (se 1 (by rfl) ⟨2920193, by rfl⟩ : syracuseStep 3893591 = 5840387) B5840387
theorem B3197303 : Blo 1419529 3197303 := bstep (se 1 (by rfl) ⟨2397977, by rfl⟩ : syracuseStep 3197303 = 4795955) B4795955
theorem B1419655 : Blo 1419529 1419655 := bstep (se 1 (by rfl) ⟨1064741, by rfl⟩ : syracuseStep 1419655 = 2129483) B2129483
theorem B1419663 : Blo 1419529 1419663 := bstep (se 1 (by rfl) ⟨1064747, by rfl⟩ : syracuseStep 1419663 = 2129495) B2129495
theorem B14780819 : Blo 1419529 14780819 := bstep (se 1 (by rfl) ⟨11085614, by rfl⟩ : syracuseStep 14780819 = 22171229) B22171229
theorem B2697619 : Blo 1419529 2697619 := bstep (se 1 (by rfl) ⟨2023214, by rfl⟩ : syracuseStep 2697619 = 4046429) B4046429
theorem B1419707 : Blo 1419529 1419707 := bstep (se 1 (by rfl) ⟨1064780, by rfl⟩ : syracuseStep 1419707 = 2129561) B2129561
theorem B1419783 : Blo 1419529 1419783 := bstep (se 1 (by rfl) ⟨1064837, by rfl⟩ : syracuseStep 1419783 = 2129675) B2129675
theorem B1419791 : Blo 1419529 1419791 := bstep (se 1 (by rfl) ⟨1064843, by rfl⟩ : syracuseStep 1419791 = 2129687) B2129687
theorem B7186967 : Blo 1419529 7186967 := bstep (se 1 (by rfl) ⟨5390225, by rfl⟩ : syracuseStep 7186967 = 10780451) B10780451
theorem B2918945 : Blo 1419529 2918945 := bstep (se 2 (by rfl) ⟨1094604, by rfl⟩ : syracuseStep 2918945 = 2189209) B2189209
theorem B3197483 : Blo 1419529 3197483 := bstep (se 1 (by rfl) ⟨2398112, by rfl⟩ : syracuseStep 3197483 = 4796225) B4796225
theorem B1419835 : Blo 1419529 1419835 := bstep (se 1 (by rfl) ⟨1064876, by rfl⟩ : syracuseStep 1419835 = 2129753) B2129753
theorem B1419911 : Blo 1419529 1419911 := bstep (se 1 (by rfl) ⟨1064933, by rfl⟩ : syracuseStep 1419911 = 2129867) B2129867
theorem B1419919 : Blo 1419529 1419919 := bstep (se 1 (by rfl) ⟨1064939, by rfl⟩ : syracuseStep 1419919 = 2129879) B2129879
theorem B1419963 : Blo 1419529 1419963 := bstep (se 1 (by rfl) ⟨1064972, by rfl⟩ : syracuseStep 1419963 = 2129945) B2129945
theorem B1420039 : Blo 1419529 1420039 := bstep (se 1 (by rfl) ⟨1065029, by rfl⟩ : syracuseStep 1420039 = 2130059) B2130059
theorem B1420047 : Blo 1419529 1420047 := bstep (se 1 (by rfl) ⟨1065035, by rfl⟩ : syracuseStep 1420047 = 2130071) B2130071
theorem B1420091 : Blo 1419529 1420091 := bstep (se 1 (by rfl) ⟨1065068, by rfl⟩ : syracuseStep 1420091 = 2130137) B2130137
theorem B1420167 : Blo 1419529 1420167 := bstep (se 1 (by rfl) ⟨1065125, by rfl⟩ : syracuseStep 1420167 = 2130251) B2130251
theorem B1420175 : Blo 1419529 1420175 := bstep (se 1 (by rfl) ⟨1065131, by rfl⟩ : syracuseStep 1420175 = 2130263) B2130263
theorem B3197843 : Blo 1419529 3197843 := bstep (se 1 (by rfl) ⟨2398382, by rfl⟩ : syracuseStep 3197843 = 4796765) B4796765
theorem B1420219 : Blo 1419529 1420219 := bstep (se 1 (by rfl) ⟨1065164, by rfl⟩ : syracuseStep 1420219 = 2130329) B2130329
theorem B3197897 : Blo 1419529 3197897 := bstep (se 2 (by rfl) ⟨1199211, by rfl⟩ : syracuseStep 3197897 = 2398423) B2398423
theorem B1420295 : Blo 1419529 1420295 := bstep (se 1 (by rfl) ⟨1065221, by rfl⟩ : syracuseStep 1420295 = 2130443) B2130443
theorem B1420303 : Blo 1419529 1420303 := bstep (se 1 (by rfl) ⟨1065227, by rfl⟩ : syracuseStep 1420303 = 2130455) B2130455
theorem B8088619 : Blo 1419529 8088619 := bstep (se 1 (by rfl) ⟨6066464, by rfl⟩ : syracuseStep 8088619 = 12132929) B12132929
theorem B1420347 : Blo 1419529 1420347 := bstep (se 1 (by rfl) ⟨1065260, by rfl⟩ : syracuseStep 1420347 = 2130521) B2130521
theorem B6065219 : Blo 1419529 6065219 := bstep (se 1 (by rfl) ⟨4548914, by rfl⟩ : syracuseStep 6065219 = 9097829) B9097829
theorem B7195715 : Blo 1419529 7195715 := bstep (se 1 (by rfl) ⟨5396786, by rfl⟩ : syracuseStep 7195715 = 10793573) B10793573
theorem B7679063 : Blo 1419529 7679063 := bstep (se 1 (by rfl) ⟨5759297, by rfl⟩ : syracuseStep 7679063 = 11518595) B11518595
theorem B1420423 : Blo 1419529 1420423 := bstep (se 1 (by rfl) ⟨1065317, by rfl⟩ : syracuseStep 1420423 = 2130635) B2130635
theorem B1420431 : Blo 1419529 1420431 := bstep (se 1 (by rfl) ⟨1065323, by rfl⟩ : syracuseStep 1420431 = 2130647) B2130647
theorem B1420475 : Blo 1419529 1420475 := bstep (se 1 (by rfl) ⟨1065356, by rfl⟩ : syracuseStep 1420475 = 2130713) B2130713
theorem B1420551 : Blo 1419529 1420551 := bstep (se 1 (by rfl) ⟨1065413, by rfl⟩ : syracuseStep 1420551 = 2130827) B2130827
theorem B1420559 : Blo 1419529 1420559 := bstep (se 1 (by rfl) ⟨1065419, by rfl⟩ : syracuseStep 1420559 = 2130839) B2130839
theorem B6065441 : Blo 1419529 6065441 := bstep (se 2 (by rfl) ⟨2274540, by rfl⟩ : syracuseStep 6065441 = 4549081) B4549081
theorem B10243361 : Blo 1419529 10243361 := bstep (se 2 (by rfl) ⟨3841260, by rfl⟩ : syracuseStep 10243361 = 7682521) B7682521
theorem B1420603 : Blo 1419529 1420603 := bstep (se 1 (by rfl) ⟨1065452, by rfl⟩ : syracuseStep 1420603 = 2130905) B2130905
theorem B4550003 : Blo 1419529 4550003 := bstep (se 1 (by rfl) ⟨3412502, by rfl⟩ : syracuseStep 4550003 = 6825005) B6825005
theorem B6065543 : Blo 1419529 6065543 := bstep (se 1 (by rfl) ⟨4549157, by rfl⟩ : syracuseStep 6065543 = 9098315) B9098315
theorem B1420679 : Blo 1419529 1420679 := bstep (se 1 (by rfl) ⟨1065509, by rfl⟩ : syracuseStep 1420679 = 2131019) B2131019
theorem B7196039 : Blo 1419529 7196039 := bstep (se 1 (by rfl) ⟨5397029, by rfl⟩ : syracuseStep 7196039 = 10794059) B10794059
theorem B1420687 : Blo 1419529 1420687 := bstep (se 1 (by rfl) ⟨1065515, by rfl⟩ : syracuseStep 1420687 = 2131031) B2131031
theorem B1797547 : Blo 1419529 1797547 := bstep (se 1 (by rfl) ⟨1348160, by rfl⟩ : syracuseStep 1797547 = 2696321) B2696321
theorem B1420731 : Blo 1419529 1420731 := bstep (se 1 (by rfl) ⟨1065548, by rfl⟩ : syracuseStep 1420731 = 2131097) B2131097
theorem B1420807 : Blo 1419529 1420807 := bstep (se 1 (by rfl) ⟨1065605, by rfl⟩ : syracuseStep 1420807 = 2131211) B2131211
theorem B1420815 : Blo 1419529 1420815 := bstep (se 1 (by rfl) ⟨1065611, by rfl⟩ : syracuseStep 1420815 = 2131223) B2131223
theorem B1420859 : Blo 1419529 1420859 := bstep (se 1 (by rfl) ⟨1065644, by rfl⟩ : syracuseStep 1420859 = 2131289) B2131289
theorem B1420935 : Blo 1419529 1420935 := bstep (se 1 (by rfl) ⟨1065701, by rfl⟩ : syracuseStep 1420935 = 2131403) B2131403
theorem B1420943 : Blo 1419529 1420943 := bstep (se 1 (by rfl) ⟨1065707, by rfl⟩ : syracuseStep 1420943 = 2131415) B2131415
theorem B7294637 : Blo 1419529 7294637 := bstep (se 3 (by rfl) ⟨1367744, by rfl⟩ : syracuseStep 7294637 = 2735489) B2735489
theorem B1420987 : Blo 1419529 1420987 := bstep (se 1 (by rfl) ⟨1065740, by rfl⟩ : syracuseStep 1420987 = 2131481) B2131481
theorem B15568577 : Blo 1419529 15568577 := bstep (se 2 (by rfl) ⟨5838216, by rfl⟩ : syracuseStep 15568577 = 11676433) B11676433
theorem B18452225 : Blo 1419529 18452225 := bstep (se 2 (by rfl) ⟨6919584, by rfl⟩ : syracuseStep 18452225 = 13839169) B13839169
theorem B1421063 : Blo 1419529 1421063 := bstep (se 1 (by rfl) ⟨1065797, by rfl⟩ : syracuseStep 1421063 = 2131595) B2131595
theorem B4042511 : Blo 1419529 4042511 := bstep (se 1 (by rfl) ⟨3031883, by rfl⟩ : syracuseStep 4042511 = 6063767) B6063767
theorem B2395919 : Blo 1419529 2395919 := bstep (se 1 (by rfl) ⟨1796939, by rfl⟩ : syracuseStep 2395919 = 3593879) B3593879
theorem B1421071 : Blo 1419529 1421071 := bstep (se 1 (by rfl) ⟨1065803, by rfl⟩ : syracuseStep 1421071 = 2131607) B2131607
theorem B5394235 : Blo 1419529 5394235 := bstep (se 1 (by rfl) ⟨4045676, by rfl⟩ : syracuseStep 5394235 = 8091353) B8091353
theorem B1421115 : Blo 1419529 1421115 := bstep (se 1 (by rfl) ⟨1065836, by rfl⟩ : syracuseStep 1421115 = 2131673) B2131673
theorem B8761223 : Blo 1419529 8761223 := bstep (se 1 (by rfl) ⟨6570917, by rfl⟩ : syracuseStep 8761223 = 13141835) B13141835
theorem B1421191 : Blo 1419529 1421191 := bstep (se 1 (by rfl) ⟨1065893, by rfl⟩ : syracuseStep 1421191 = 2131787) B2131787
theorem B1421199 : Blo 1419529 1421199 := bstep (se 1 (by rfl) ⟨1065899, by rfl⟩ : syracuseStep 1421199 = 2131799) B2131799
theorem B1421243 : Blo 1419529 1421243 := bstep (se 1 (by rfl) ⟨1065932, by rfl⟩ : syracuseStep 1421243 = 2131865) B2131865
theorem B16175051 : Blo 1419529 16175051 := bstep (se 1 (by rfl) ⟨12131288, by rfl⟩ : syracuseStep 16175051 = 24262577) B24262577
theorem B7679947 : Blo 1419529 7679947 := bstep (se 1 (by rfl) ⟨5759960, by rfl⟩ : syracuseStep 7679947 = 11519921) B11519921
theorem B1421319 : Blo 1419529 1421319 := bstep (se 1 (by rfl) ⟨1065989, by rfl⟩ : syracuseStep 1421319 = 2131979) B2131979
theorem B1421327 : Blo 1419529 1421327 := bstep (se 1 (by rfl) ⟨1065995, by rfl⟩ : syracuseStep 1421327 = 2131991) B2131991
theorem B20492311 : Blo 1419529 20492311 := bstep (se 1 (by rfl) ⟨15369233, by rfl⟩ : syracuseStep 20492311 = 30738467) B30738467
theorem B1421371 : Blo 1419529 1421371 := bstep (se 1 (by rfl) ⟨1066028, by rfl⟩ : syracuseStep 1421371 = 2132057) B2132057
theorem B1421447 : Blo 1419529 1421447 := bstep (se 1 (by rfl) ⟨1066085, by rfl⟩ : syracuseStep 1421447 = 2132171) B2132171
theorem B1421455 : Blo 1419529 1421455 := bstep (se 1 (by rfl) ⟨1066091, by rfl⟩ : syracuseStep 1421455 = 2132183) B2132183
theorem B1421499 : Blo 1419529 1421499 := bstep (se 1 (by rfl) ⟨1066124, by rfl⟩ : syracuseStep 1421499 = 2132249) B2132249
theorem B10932461 : Blo 1419529 10932461 := bstep (se 3 (by rfl) ⟨2049836, by rfl⟩ : syracuseStep 10932461 = 4099673) B4099673
theorem B5394721 : Blo 1419529 5394721 := bstep (se 2 (by rfl) ⟨2023020, by rfl⟩ : syracuseStep 5394721 = 4046041) B4046041
theorem B2396459 : Blo 1419529 2396459 := bstep (se 1 (by rfl) ⟨1797344, by rfl⟩ : syracuseStep 2396459 = 3594689) B3594689
theorem B2879803 : Blo 1419529 2879803 := bstep (se 1 (by rfl) ⟨2159852, by rfl⟩ : syracuseStep 2879803 = 4319705) B4319705
theorem B1798519 : Blo 1419529 1798519 := bstep (se 1 (by rfl) ⟨1348889, by rfl⟩ : syracuseStep 1798519 = 2697779) B2697779
theorem B4796819 : Blo 1419529 4796819 := bstep (se 1 (by rfl) ⟨3597614, by rfl⟩ : syracuseStep 4796819 = 7195229) B7195229
theorem B8090077 : Blo 1419529 8090077 := bstep (se 3 (by rfl) ⟨1516889, by rfl⟩ : syracuseStep 8090077 = 3033779) B3033779
theorem B5763595 : Blo 1419529 5763595 := bstep (se 1 (by rfl) ⟨4322696, by rfl⟩ : syracuseStep 5763595 = 8645393) B8645393
theorem B3838493 : Blo 1419529 3838493 := bstep (se 3 (by rfl) ⟨719717, by rfl⟩ : syracuseStep 3838493 = 1439435) B1439435
theorem B4043297 : Blo 1419529 4043297 := bstep (se 2 (by rfl) ⟨1516236, by rfl⟩ : syracuseStep 4043297 = 3032473) B3032473
theorem B3240481 : Blo 1419529 3240481 := bstep (se 2 (by rfl) ⟨1215180, by rfl⟩ : syracuseStep 3240481 = 2430361) B2430361
theorem B27669059 : Blo 1419529 27669059 := bstep (se 1 (by rfl) ⟨20751794, by rfl⟩ : syracuseStep 27669059 = 41503589) B41503589
theorem B2396857 : Blo 1419529 2396857 := bstep (se 2 (by rfl) ⟨898821, by rfl⟩ : syracuseStep 2396857 = 1797643) B1797643
theorem B1798843 : Blo 1419529 1798843 := bstep (se 1 (by rfl) ⟨1349132, by rfl⟩ : syracuseStep 1798843 = 2698265) B2698265
theorem B3838873 : Blo 1419529 3838873 := bstep (se 2 (by rfl) ⟨1439577, by rfl⟩ : syracuseStep 3838873 = 2879155) B2879155
theorem B6656921 : Blo 1419529 6656921 := bstep (se 2 (by rfl) ⟨2496345, by rfl⟩ : syracuseStep 6656921 = 4992691) B4992691
theorem B13661081 : Blo 1419529 13661081 := bstep (se 2 (by rfl) ⟨5122905, by rfl⟩ : syracuseStep 13661081 = 10245811) B10245811
theorem B8205259 : Blo 1419529 8205259 := bstep (se 1 (by rfl) ⟨6153944, by rfl⟩ : syracuseStep 8205259 = 12307889) B12307889
theorem B3593231 : Blo 1419529 3593231 := bstep (se 1 (by rfl) ⟨2694923, by rfl⟩ : syracuseStep 3593231 = 5389847) B5389847
theorem B8639531 : Blo 1419529 8639531 := bstep (se 1 (by rfl) ⟨6479648, by rfl⟩ : syracuseStep 8639531 = 12959297) B12959297
theorem B5395693 : Blo 1419529 5395693 := bstep (se 3 (by rfl) ⟨1011692, by rfl⟩ : syracuseStep 5395693 = 2023385) B2023385
theorem B6067457 : Blo 1419529 6067457 := bstep (se 2 (by rfl) ⟨2275296, by rfl⟩ : syracuseStep 6067457 = 4550593) B4550593
theorem B3282209 : Blo 1419529 3282209 := bstep (se 2 (by rfl) ⟨1230828, by rfl⟩ : syracuseStep 3282209 = 2461657) B2461657
theorem B2397559 : Blo 1419529 2397559 := bstep (se 1 (by rfl) ⟨1798169, by rfl⟩ : syracuseStep 2397559 = 3596339) B3596339
theorem B7190045 : Blo 1419529 7190045 := bstep (se 3 (by rfl) ⟨1348133, by rfl⟩ : syracuseStep 7190045 = 2696267) B2696267
theorem B5395997 : Blo 1419529 5395997 := bstep (se 3 (by rfl) ⟨1011749, by rfl⟩ : syracuseStep 5395997 = 2023499) B2023499
theorem B2397755 : Blo 1419529 2397755 := bstep (se 1 (by rfl) ⟨1798316, by rfl⟩ : syracuseStep 2397755 = 3596633) B3596633
theorem B15357559 : Blo 1419529 15357559 := bstep (se 1 (by rfl) ⟨11518169, by rfl⟩ : syracuseStep 15357559 = 23036339) B23036339
theorem B13653623 : Blo 1419529 13653623 := bstep (se 1 (by rfl) ⟨10240217, by rfl⟩ : syracuseStep 13653623 = 20480435) B20480435
theorem B3413657 : Blo 1419529 3413657 := bstep (se 2 (by rfl) ⟨1280121, by rfl⟩ : syracuseStep 3413657 = 2560243) B2560243
theorem B3593929 : Blo 1419529 3593929 := bstep (se 2 (by rfl) ⟨1347723, by rfl⟩ : syracuseStep 3593929 = 2695447) B2695447
theorem B4552463 : Blo 1419529 4552463 := bstep (se 1 (by rfl) ⟨3414347, by rfl⟩ : syracuseStep 4552463 = 6828695) B6828695
theorem B63141697 : Blo 1419529 63141697 := bstep (se 2 (by rfl) ⟨23678136, by rfl⟩ : syracuseStep 63141697 = 47356273) B47356273
theorem B3594071 : Blo 1419529 3594071 := bstep (se 1 (by rfl) ⟨2695553, by rfl⟩ : syracuseStep 3594071 = 5391107) B5391107
theorem B5117831 : Blo 1419529 5117831 := bstep (se 1 (by rfl) ⟨3838373, by rfl⟩ : syracuseStep 5117831 = 7676747) B7676747
theorem B2398153 : Blo 1419529 2398153 := bstep (se 2 (by rfl) ⟨899307, by rfl⟩ : syracuseStep 2398153 = 1798615) B1798615
theorem B2160631 : Blo 1419529 2160631 := bstep (se 1 (by rfl) ⟨1620473, by rfl⟩ : syracuseStep 2160631 = 3240947) B3240947
theorem B6821891 : Blo 1419529 6821891 := bstep (se 1 (by rfl) ⟨5116418, by rfl⟩ : syracuseStep 6821891 = 10232837) B10232837
theorem B7190531 : Blo 1419529 7190531 := bstep (se 1 (by rfl) ⟨5392898, by rfl⟩ : syracuseStep 7190531 = 10785797) B10785797
theorem B4044811 : Blo 1419529 4044811 := bstep (se 1 (by rfl) ⟨3033608, by rfl⟩ : syracuseStep 4044811 = 6067217) B6067217
theorem B4102159 : Blo 1419529 4102159 := bstep (se 1 (by rfl) ⟨3076619, by rfl⟩ : syracuseStep 4102159 = 6153239) B6153239
theorem B9099287 : Blo 1419529 9099287 := bstep (se 1 (by rfl) ⟨6824465, by rfl⟩ : syracuseStep 9099287 = 13648931) B13648931
theorem B2881595 : Blo 1419529 2881595 := bstep (se 1 (by rfl) ⟨2161196, by rfl⟩ : syracuseStep 2881595 = 4322393) B4322393
theorem B2021449 : Blo 1419529 2021449 := bstep (se 2 (by rfl) ⟨758043, by rfl⟩ : syracuseStep 2021449 = 1516087) B1516087
theorem B6830351 : Blo 1419529 6830351 := bstep (se 1 (by rfl) ⟨5122763, by rfl⟩ : syracuseStep 6830351 = 10245527) B10245527
theorem B4045085 : Blo 1419529 4045085 := bstep (se 3 (by rfl) ⟨758453, by rfl⟩ : syracuseStep 4045085 = 1516907) B1516907
theorem B840636737 : Blo 1419529 840636737 := bstep (se 2 (by rfl) ⟨315238776, by rfl⟩ : syracuseStep 840636737 = 630477553) B630477553
theorem B27662813 : Blo 1419529 27662813 := bstep (se 3 (by rfl) ⟨5186777, by rfl⟩ : syracuseStep 27662813 = 10373555) B10373555
theorem B24271325 : Blo 1419529 24271325 := bstep (se 3 (by rfl) ⟨4550873, by rfl⟩ : syracuseStep 24271325 = 9101747) B9101747
theorem B4045427 : Blo 1419529 4045427 := bstep (se 1 (by rfl) ⟨3034070, by rfl⟩ : syracuseStep 4045427 = 6068141) B6068141
theorem B4791041 : Blo 1419529 4791041 := bstep (se 2 (by rfl) ⟨1796640, by rfl⟩ : syracuseStep 4791041 = 3593281) B3593281
theorem B3840797 : Blo 1419529 3840797 := bstep (se 3 (by rfl) ⟨720149, by rfl⟩ : syracuseStep 3840797 = 1440299) B1440299
theorem B32783267 : Blo 1419529 32783267 := bstep (se 1 (by rfl) ⟨24587450, by rfl⟩ : syracuseStep 32783267 = 49174901) B49174901
theorem B3193991 : Blo 1419529 3193991 := bstep (se 1 (by rfl) ⟨2395493, by rfl⟩ : syracuseStep 3193991 = 4790987) B4790987
theorem B3194171 : Blo 1419529 3194171 := bstep (se 1 (by rfl) ⟨2395628, by rfl⟩ : syracuseStep 3194171 = 4791257) B4791257
theorem B3194297 : Blo 1419529 3194297 := bstep (se 2 (by rfl) ⟨1197861, by rfl⟩ : syracuseStep 3194297 = 2395723) B2395723
theorem B2129339 : Blo 1419529 2129339 := bstep (se 1 (by rfl) ⟨1597004, by rfl⟩ : syracuseStep 2129339 = 3194009) B3194009
theorem B2129399 : Blo 1419529 2129399 := bstep (se 1 (by rfl) ⟨1597049, by rfl⟩ : syracuseStep 2129399 = 3194099) B3194099
theorem B12303875 : Blo 1419529 12303875 := bstep (se 1 (by rfl) ⟨9227906, by rfl⟩ : syracuseStep 12303875 = 18455813) B18455813
theorem B2129423 : Blo 1419529 2129423 := bstep (se 1 (by rfl) ⟨1597067, by rfl⟩ : syracuseStep 2129423 = 3194135) B3194135
theorem B4791851 : Blo 1419529 4791851 := bstep (se 1 (by rfl) ⟨3593888, by rfl⟩ : syracuseStep 4791851 = 7187777) B7187777
theorem B2129465 : Blo 1419529 2129465 := bstep (se 2 (by rfl) ⟨798549, by rfl⟩ : syracuseStep 2129465 = 1597099) B1597099
theorem B4046395 : Blo 1419529 4046395 := bstep (se 1 (by rfl) ⟨3034796, by rfl⟩ : syracuseStep 4046395 = 6069593) B6069593
theorem B7192151 : Blo 1419529 7192151 := bstep (se 1 (by rfl) ⟨5394113, by rfl⟩ : syracuseStep 7192151 = 10788227) B10788227
theorem B3743347 : Blo 1419529 3743347 := bstep (se 1 (by rfl) ⟨2807510, by rfl⟩ : syracuseStep 3743347 = 5615021) B5615021
theorem B6823543 : Blo 1419529 6823543 := bstep (se 1 (by rfl) ⟨5117657, by rfl⟩ : syracuseStep 6823543 = 10235315) B10235315
theorem B1597063 : Blo 1419529 1597063 := bstep (se 1 (by rfl) ⟨1197797, by rfl⟩ : syracuseStep 1597063 = 2395595) B2395595
theorem B2129543 : Blo 1419529 2129543 := bstep (se 1 (by rfl) ⟨1597157, by rfl⟩ : syracuseStep 2129543 = 3194315) B3194315
theorem B2129579 : Blo 1419529 2129579 := bstep (se 1 (by rfl) ⟨1597184, by rfl⟩ : syracuseStep 2129579 = 3194369) B3194369
theorem B2129609 : Blo 1419529 2129609 := bstep (se 2 (by rfl) ⟨798603, by rfl⟩ : syracuseStep 2129609 = 1597207) B1597207
theorem B3194639 : Blo 1419529 3194639 := bstep (se 1 (by rfl) ⟨2395979, by rfl⟩ : syracuseStep 3194639 = 4791959) B4791959
theorem B3194657 : Blo 1419529 3194657 := bstep (se 2 (by rfl) ⟨1197996, by rfl⟩ : syracuseStep 3194657 = 2395993) B2395993
theorem B1597243 : Blo 1419529 1597243 := bstep (se 1 (by rfl) ⟨1197932, by rfl⟩ : syracuseStep 1597243 = 2395865) B2395865
theorem B2129723 : Blo 1419529 2129723 := bstep (se 1 (by rfl) ⟨1597292, by rfl⟩ : syracuseStep 2129723 = 3194585) B3194585
theorem B3596147 : Blo 1419529 3596147 := bstep (se 1 (by rfl) ⟨2697110, by rfl⟩ : syracuseStep 3596147 = 5394221) B5394221
theorem B2129783 : Blo 1419529 2129783 := bstep (se 1 (by rfl) ⟨1597337, by rfl⟩ : syracuseStep 2129783 = 3194675) B3194675
theorem B2129807 : Blo 1419529 2129807 := bstep (se 1 (by rfl) ⟨1597355, by rfl⟩ : syracuseStep 2129807 = 3194711) B3194711
theorem B20234137 : Blo 1419529 20234137 := bstep (se 2 (by rfl) ⟨7587801, by rfl⟩ : syracuseStep 20234137 = 15175603) B15175603
theorem B2129849 : Blo 1419529 2129849 := bstep (se 2 (by rfl) ⟨798693, by rfl⟩ : syracuseStep 2129849 = 1597387) B1597387
theorem B2129999 : Blo 1419529 2129999 := bstep (se 1 (by rfl) ⟨1597499, by rfl⟩ : syracuseStep 2129999 = 3194999) B3194999
theorem B2695265 : Blo 1419529 2695265 := bstep (se 2 (by rfl) ⟨1010724, by rfl⟩ : syracuseStep 2695265 = 2021449) B2021449
theorem B7684253 : Blo 1419529 7684253 := bstep (se 3 (by rfl) ⟨1440797, by rfl⟩ : syracuseStep 7684253 = 2881595) B2881595
theorem B2130119 : Blo 1419529 2130119 := bstep (se 1 (by rfl) ⟨1597589, by rfl⟩ : syracuseStep 2130119 = 3195179) B3195179
theorem B1597639 : Blo 1419529 1597639 := bstep (se 1 (by rfl) ⟨1198229, by rfl⟩ : syracuseStep 1597639 = 2396459) B2396459
theorem B2130281 : Blo 1419529 2130281 := bstep (se 2 (by rfl) ⟨798855, by rfl⟩ : syracuseStep 2130281 = 1597711) B1597711
theorem B2695531 : Blo 1419529 2695531 := bstep (se 1 (by rfl) ⟨2021648, by rfl⟩ : syracuseStep 2695531 = 4043297) B4043297
theorem B7192961 : Blo 1419529 7192961 := bstep (se 2 (by rfl) ⟨2697360, by rfl⟩ : syracuseStep 7192961 = 5394721) B5394721
theorem B9724313 : Blo 1419529 9724313 := bstep (se 2 (by rfl) ⟨3646617, by rfl⟩ : syracuseStep 9724313 = 7293235) B7293235
theorem B2130359 : Blo 1419529 2130359 := bstep (se 1 (by rfl) ⟨1597769, by rfl⟩ : syracuseStep 2130359 = 3195539) B3195539
theorem B2130395 : Blo 1419529 2130395 := bstep (se 1 (by rfl) ⟨1597796, by rfl⟩ : syracuseStep 2130395 = 3195593) B3195593
theorem B3596825 : Blo 1419529 3596825 := bstep (se 2 (by rfl) ⟨1348809, by rfl⟩ : syracuseStep 3596825 = 2697619) B2697619
theorem B3195431 : Blo 1419529 3195431 := bstep (se 1 (by rfl) ⟨2396573, by rfl⟩ : syracuseStep 3195431 = 4793147) B4793147
theorem B4047499 : Blo 1419529 4047499 := bstep (se 1 (by rfl) ⟨3035624, by rfl⟩ : syracuseStep 4047499 = 6071249) B6071249
theorem B7684793 : Blo 1419529 7684793 := bstep (se 2 (by rfl) ⟨2881797, by rfl⟩ : syracuseStep 7684793 = 5763595) B5763595
theorem B5759687 : Blo 1419529 5759687 := bstep (se 1 (by rfl) ⟨4319765, by rfl⟩ : syracuseStep 5759687 = 8639531) B8639531
theorem B2188139 : Blo 1419529 2188139 := bstep (se 1 (by rfl) ⟨1641104, by rfl⟩ : syracuseStep 2188139 = 3282209) B3282209
theorem B3195755 : Blo 1419529 3195755 := bstep (se 1 (by rfl) ⟨2396816, by rfl⟩ : syracuseStep 3195755 = 4793633) B4793633
theorem B3195809 : Blo 1419529 3195809 := bstep (se 2 (by rfl) ⟨1198428, by rfl⟩ : syracuseStep 3195809 = 2396857) B2396857
theorem B2130863 : Blo 1419529 2130863 := bstep (se 1 (by rfl) ⟨1598147, by rfl⟩ : syracuseStep 2130863 = 3196295) B3196295
theorem B2130953 : Blo 1419529 2130953 := bstep (se 2 (by rfl) ⟨799107, by rfl⟩ : syracuseStep 2130953 = 1598215) B1598215
theorem B4793363 : Blo 1419529 4793363 := bstep (se 1 (by rfl) ⟨3595022, by rfl⟩ : syracuseStep 4793363 = 7190045) B7190045
theorem B3597331 : Blo 1419529 3597331 := bstep (se 1 (by rfl) ⟨2697998, by rfl⟩ : syracuseStep 3597331 = 5395997) B5395997
theorem B2130983 : Blo 1419529 2130983 := bstep (se 1 (by rfl) ⟨1598237, by rfl⟩ : syracuseStep 2130983 = 3196475) B3196475
theorem B1598503 : Blo 1419529 1598503 := bstep (se 1 (by rfl) ⟨1198877, by rfl⟩ : syracuseStep 1598503 = 2397755) B2397755
theorem B2917433 : Blo 1419529 2917433 := bstep (se 2 (by rfl) ⟨1094037, by rfl⟩ : syracuseStep 2917433 = 2188075) B2188075
theorem B9102415 : Blo 1419529 9102415 := bstep (se 1 (by rfl) ⟨6826811, by rfl⟩ : syracuseStep 9102415 = 13653623) B13653623
theorem B2131067 : Blo 1419529 2131067 := bstep (se 1 (by rfl) ⟨1598300, by rfl⟩ : syracuseStep 2131067 = 3196601) B3196601
theorem B7193771 : Blo 1419529 7193771 := bstep (se 1 (by rfl) ⟨5395328, by rfl⟩ : syracuseStep 7193771 = 10790657) B10790657
theorem B3196151 : Blo 1419529 3196151 := bstep (se 1 (by rfl) ⟨2397113, by rfl⟩ : syracuseStep 3196151 = 4794227) B4794227
theorem B2131193 : Blo 1419529 2131193 := bstep (se 2 (by rfl) ⟨799197, by rfl⟩ : syracuseStep 2131193 = 1598395) B1598395
theorem B4547927 : Blo 1419529 4547927 := bstep (se 1 (by rfl) ⟨3410945, by rfl⟩ : syracuseStep 4547927 = 6821891) B6821891
theorem B4793687 : Blo 1419529 4793687 := bstep (se 1 (by rfl) ⟨3595265, by rfl⟩ : syracuseStep 4793687 = 7190531) B7190531
theorem B2131295 : Blo 1419529 2131295 := bstep (se 1 (by rfl) ⟨1598471, by rfl⟩ : syracuseStep 2131295 = 3196943) B3196943
theorem B2131307 : Blo 1419529 2131307 := bstep (se 1 (by rfl) ⟨1598480, by rfl⟩ : syracuseStep 2131307 = 3196961) B3196961
theorem B2049463 : Blo 1419529 2049463 := bstep (se 1 (by rfl) ⟨1537097, by rfl⟩ : syracuseStep 2049463 = 3074195) B3074195
theorem B2696723 : Blo 1419529 2696723 := bstep (se 1 (by rfl) ⟨2022542, by rfl⟩ : syracuseStep 2696723 = 4045085) B4045085
theorem B560424491 : Blo 1419529 560424491 := bstep (se 1 (by rfl) ⟨420318368, by rfl⟩ : syracuseStep 560424491 = 840636737) B840636737
theorem B2131535 : Blo 1419529 2131535 := bstep (se 1 (by rfl) ⟨1598651, by rfl⟩ : syracuseStep 2131535 = 3197303) B3197303
theorem B7194257 : Blo 1419529 7194257 := bstep (se 2 (by rfl) ⟨2697846, by rfl⟩ : syracuseStep 7194257 = 5395693) B5395693
theorem B18441875 : Blo 1419529 18441875 := bstep (se 1 (by rfl) ⟨13831406, by rfl⟩ : syracuseStep 18441875 = 27662813) B27662813
theorem B16180883 : Blo 1419529 16180883 := bstep (se 1 (by rfl) ⟨12135662, by rfl⟩ : syracuseStep 16180883 = 24271325) B24271325
theorem B2131655 : Blo 1419529 2131655 := bstep (se 1 (by rfl) ⟨1598741, by rfl⟩ : syracuseStep 2131655 = 3197483) B3197483
theorem B2696951 : Blo 1419529 2696951 := bstep (se 1 (by rfl) ⟨2022713, by rfl⟩ : syracuseStep 2696951 = 4045427) B4045427
theorem B14780153 : Blo 1419529 14780153 := bstep (se 2 (by rfl) ⟨5542557, by rfl⟩ : syracuseStep 14780153 = 11085115) B11085115
theorem B3196745 : Blo 1419529 3196745 := bstep (se 2 (by rfl) ⟨1198779, by rfl⟩ : syracuseStep 3196745 = 2397559) B2397559
theorem B2131817 : Blo 1419529 2131817 := bstep (se 2 (by rfl) ⟨799431, by rfl⟩ : syracuseStep 2131817 = 1598863) B1598863
theorem B2131895 : Blo 1419529 2131895 := bstep (se 1 (by rfl) ⟨1598921, by rfl⟩ : syracuseStep 2131895 = 3197843) B3197843
theorem B2131931 : Blo 1419529 2131931 := bstep (se 1 (by rfl) ⟨1598948, by rfl⟩ : syracuseStep 2131931 = 3197897) B3197897
theorem B4991129 : Blo 1419529 4991129 := bstep (se 2 (by rfl) ⟨1871673, by rfl⟩ : syracuseStep 4991129 = 3743347) B3743347
theorem B3033335 : Blo 1419529 3033335 := bstep (se 1 (by rfl) ⟨2275001, by rfl⟩ : syracuseStep 3033335 = 4550003) B4550003
theorem B1419559 : Blo 1419529 1419559 := bstep (se 1 (by rfl) ⟨1064669, by rfl⟩ : syracuseStep 1419559 = 2129339) B2129339
theorem B1419599 : Blo 1419529 1419599 := bstep (se 1 (by rfl) ⟨1064699, by rfl⟩ : syracuseStep 1419599 = 2129399) B2129399
theorem B8202583 : Blo 1419529 8202583 := bstep (se 1 (by rfl) ⟨6151937, by rfl⟩ : syracuseStep 8202583 = 12303875) B12303875
theorem B1419615 : Blo 1419529 1419615 := bstep (se 1 (by rfl) ⟨1064711, by rfl⟩ : syracuseStep 1419615 = 2129423) B2129423
theorem B1419643 : Blo 1419529 1419643 := bstep (se 1 (by rfl) ⟨1064732, by rfl⟩ : syracuseStep 1419643 = 2129465) B2129465
theorem B4794767 : Blo 1419529 4794767 := bstep (se 1 (by rfl) ⟨3596075, by rfl⟩ : syracuseStep 4794767 = 7192151) B7192151
theorem B1419695 : Blo 1419529 1419695 := bstep (se 1 (by rfl) ⟨1064771, by rfl⟩ : syracuseStep 1419695 = 2129543) B2129543
theorem B1419719 : Blo 1419529 1419719 := bstep (se 1 (by rfl) ⟨1064789, by rfl⟩ : syracuseStep 1419719 = 2129579) B2129579
theorem B1419739 : Blo 1419529 1419739 := bstep (se 1 (by rfl) ⟨1064804, by rfl⟩ : syracuseStep 1419739 = 2129609) B2129609
theorem B26978849 : Blo 1419529 26978849 := bstep (se 2 (by rfl) ⟨10117068, by rfl⟩ : syracuseStep 26978849 = 20234137) B20234137
theorem B1419815 : Blo 1419529 1419815 := bstep (se 1 (by rfl) ⟨1064861, by rfl⟩ : syracuseStep 1419815 = 2129723) B2129723
theorem B1419855 : Blo 1419529 1419855 := bstep (se 1 (by rfl) ⟨1064891, by rfl⟩ : syracuseStep 1419855 = 2129783) B2129783
theorem B1419871 : Blo 1419529 1419871 := bstep (se 1 (by rfl) ⟨1064903, by rfl⟩ : syracuseStep 1419871 = 2129807) B2129807
theorem B3197537 : Blo 1419529 3197537 := bstep (se 2 (by rfl) ⟨1199076, by rfl⟩ : syracuseStep 3197537 = 2398153) B2398153
theorem B1419899 : Blo 1419529 1419899 := bstep (se 1 (by rfl) ⟨1064924, by rfl⟩ : syracuseStep 1419899 = 2129849) B2129849
theorem B10783367 : Blo 1419529 10783367 := bstep (se 1 (by rfl) ⟨8087525, by rfl⟩ : syracuseStep 10783367 = 16175051) B16175051
theorem B1419951 : Blo 1419529 1419951 := bstep (se 1 (by rfl) ⟨1064963, by rfl⟩ : syracuseStep 1419951 = 2129927) B2129927
theorem B7187129 : Blo 1419529 7187129 := bstep (se 2 (by rfl) ⟨2695173, by rfl⟩ : syracuseStep 7187129 = 5390347) B5390347
theorem B5393081 : Blo 1419529 5393081 := bstep (se 2 (by rfl) ⟨2022405, by rfl⟩ : syracuseStep 5393081 = 4044811) B4044811
theorem B1419975 : Blo 1419529 1419975 := bstep (se 1 (by rfl) ⟨1064981, by rfl⟩ : syracuseStep 1419975 = 2129963) B2129963
theorem B27323081 : Blo 1419529 27323081 := bstep (se 2 (by rfl) ⟨10246155, by rfl⟩ : syracuseStep 27323081 = 20492311) B20492311
theorem B4795091 : Blo 1419529 4795091 := bstep (se 1 (by rfl) ⟨3596318, by rfl⟩ : syracuseStep 4795091 = 7192637) B7192637
theorem B1419995 : Blo 1419529 1419995 := bstep (se 1 (by rfl) ⟨1064996, by rfl⟩ : syracuseStep 1419995 = 2129993) B2129993
theorem B1420071 : Blo 1419529 1420071 := bstep (se 1 (by rfl) ⟨1065053, by rfl⟩ : syracuseStep 1420071 = 2130107) B2130107
theorem B1420111 : Blo 1419529 1420111 := bstep (se 1 (by rfl) ⟨1065083, by rfl⟩ : syracuseStep 1420111 = 2130167) B2130167
theorem B1420127 : Blo 1419529 1420127 := bstep (se 1 (by rfl) ⟨1065095, by rfl⟩ : syracuseStep 1420127 = 2130191) B2130191
theorem B1420155 : Blo 1419529 1420155 := bstep (se 1 (by rfl) ⟨1065116, by rfl⟩ : syracuseStep 1420155 = 2130233) B2130233
theorem B3410849 : Blo 1419529 3410849 := bstep (se 2 (by rfl) ⟨1279068, by rfl⟩ : syracuseStep 3410849 = 2558137) B2558137
theorem B1420207 : Blo 1419529 1420207 := bstep (se 1 (by rfl) ⟨1065155, by rfl⟩ : syracuseStep 1420207 = 2130311) B2130311
theorem B3197879 : Blo 1419529 3197879 := bstep (se 1 (by rfl) ⟨2398409, by rfl⟩ : syracuseStep 3197879 = 4796819) B4796819
theorem B1420231 : Blo 1419529 1420231 := bstep (se 1 (by rfl) ⟨1065173, by rfl⟩ : syracuseStep 1420231 = 2130347) B2130347
theorem B1420251 : Blo 1419529 1420251 := bstep (se 1 (by rfl) ⟨1065188, by rfl⟩ : syracuseStep 1420251 = 2130377) B2130377
theorem B10234853 : Blo 1419529 10234853 := bstep (se 4 (by rfl) ⟨959517, by rfl⟩ : syracuseStep 10234853 = 1919035) B1919035
theorem B2558995 : Blo 1419529 2558995 := bstep (se 1 (by rfl) ⟨1919246, by rfl⟩ : syracuseStep 2558995 = 3838493) B3838493
theorem B1420327 : Blo 1419529 1420327 := bstep (se 1 (by rfl) ⟨1065245, by rfl⟩ : syracuseStep 1420327 = 2130491) B2130491
theorem B1420367 : Blo 1419529 1420367 := bstep (se 1 (by rfl) ⟨1065275, by rfl⟩ : syracuseStep 1420367 = 2130551) B2130551
theorem B1420383 : Blo 1419529 1420383 := bstep (se 1 (by rfl) ⟨1065287, by rfl⟩ : syracuseStep 1420383 = 2130575) B2130575
theorem B1420411 : Blo 1419529 1420411 := bstep (se 1 (by rfl) ⟨1065308, by rfl⟩ : syracuseStep 1420411 = 2130617) B2130617
theorem B2698363 : Blo 1419529 2698363 := bstep (se 1 (by rfl) ⟨2023772, by rfl⟩ : syracuseStep 2698363 = 4047545) B4047545
theorem B1420463 : Blo 1419529 1420463 := bstep (se 1 (by rfl) ⟨1065347, by rfl⟩ : syracuseStep 1420463 = 2130695) B2130695
theorem B38890691 : Blo 1419529 38890691 := bstep (se 1 (by rfl) ⟨29168018, by rfl⟩ : syracuseStep 38890691 = 58336037) B58336037
theorem B1797319 : Blo 1419529 1797319 := bstep (se 1 (by rfl) ⟨1347989, by rfl⟩ : syracuseStep 1797319 = 2695979) B2695979
theorem B1420487 : Blo 1419529 1420487 := bstep (se 1 (by rfl) ⟨1065365, by rfl⟩ : syracuseStep 1420487 = 2130731) B2130731
theorem B1420507 : Blo 1419529 1420507 := bstep (se 1 (by rfl) ⟨1065380, by rfl⟩ : syracuseStep 1420507 = 2130761) B2130761
theorem B1420583 : Blo 1419529 1420583 := bstep (se 1 (by rfl) ⟨1065437, by rfl⟩ : syracuseStep 1420583 = 2130875) B2130875
theorem B87633211 : Blo 1419529 87633211 := bstep (se 1 (by rfl) ⟨65724908, by rfl⟩ : syracuseStep 87633211 = 131449817) B131449817
theorem B1420623 : Blo 1419529 1420623 := bstep (se 1 (by rfl) ⟨1065467, by rfl⟩ : syracuseStep 1420623 = 2130935) B2130935
theorem B2395487 : Blo 1419529 2395487 := bstep (se 1 (by rfl) ⟨1796615, by rfl⟩ : syracuseStep 2395487 = 3593231) B3593231
theorem B1420639 : Blo 1419529 1420639 := bstep (se 1 (by rfl) ⟨1065479, by rfl⟩ : syracuseStep 1420639 = 2130959) B2130959
theorem B2698591 : Blo 1419529 2698591 := bstep (se 1 (by rfl) ⟨2023943, by rfl⟩ : syracuseStep 2698591 = 4047887) B4047887
theorem B1420667 : Blo 1419529 1420667 := bstep (se 1 (by rfl) ⟨1065500, by rfl⟩ : syracuseStep 1420667 = 2131001) B2131001
theorem B4320641 : Blo 1419529 4320641 := bstep (se 2 (by rfl) ⟨1620240, by rfl⟩ : syracuseStep 4320641 = 3240481) B3240481
theorem B27315629 : Blo 1419529 27315629 := bstep (se 3 (by rfl) ⟨5121680, by rfl⟩ : syracuseStep 27315629 = 10243361) B10243361
theorem B1420719 : Blo 1419529 1420719 := bstep (se 1 (by rfl) ⟨1065539, by rfl⟩ : syracuseStep 1420719 = 2131079) B2131079
theorem B1420743 : Blo 1419529 1420743 := bstep (se 1 (by rfl) ⟨1065557, by rfl⟩ : syracuseStep 1420743 = 2131115) B2131115
theorem B6827465 : Blo 1419529 6827465 := bstep (se 2 (by rfl) ⟨2560299, by rfl⟩ : syracuseStep 6827465 = 5120599) B5120599
theorem B1420763 : Blo 1419529 1420763 := bstep (se 1 (by rfl) ⟨1065572, by rfl⟩ : syracuseStep 1420763 = 2131145) B2131145
theorem B1420839 : Blo 1419529 1420839 := bstep (se 1 (by rfl) ⟨1065629, by rfl⟩ : syracuseStep 1420839 = 2131259) B2131259
theorem B1420879 : Blo 1419529 1420879 := bstep (se 1 (by rfl) ⟨1065659, by rfl⟩ : syracuseStep 1420879 = 2131319) B2131319
theorem B1420895 : Blo 1419529 1420895 := bstep (se 1 (by rfl) ⟨1065671, by rfl⟩ : syracuseStep 1420895 = 2131343) B2131343
theorem B1420923 : Blo 1419529 1420923 := bstep (se 1 (by rfl) ⟨1065692, by rfl⟩ : syracuseStep 1420923 = 2131385) B2131385
theorem B1420975 : Blo 1419529 1420975 := bstep (se 1 (by rfl) ⟨1065731, by rfl⟩ : syracuseStep 1420975 = 2131463) B2131463
theorem B1420999 : Blo 1419529 1420999 := bstep (se 1 (by rfl) ⟨1065749, by rfl⟩ : syracuseStep 1420999 = 2131499) B2131499
theorem B1421019 : Blo 1419529 1421019 := bstep (se 1 (by rfl) ⟨1065764, by rfl⟩ : syracuseStep 1421019 = 2131529) B2131529
theorem B39415517 : Blo 1419529 39415517 := bstep (se 3 (by rfl) ⟨7390409, by rfl⟩ : syracuseStep 39415517 = 14780819) B14780819
theorem B1421095 : Blo 1419529 1421095 := bstep (se 1 (by rfl) ⟨1065821, by rfl⟩ : syracuseStep 1421095 = 2131643) B2131643
theorem B1421135 : Blo 1419529 1421135 := bstep (se 1 (by rfl) ⟨1065851, by rfl⟩ : syracuseStep 1421135 = 2131703) B2131703
theorem B1421151 : Blo 1419529 1421151 := bstep (se 1 (by rfl) ⟨1065863, by rfl⟩ : syracuseStep 1421151 = 2131727) B2131727
theorem B4796279 : Blo 1419529 4796279 := bstep (se 1 (by rfl) ⟨3597209, by rfl⟩ : syracuseStep 4796279 = 7194419) B7194419
theorem B1421179 : Blo 1419529 1421179 := bstep (se 1 (by rfl) ⟨1065884, by rfl⟩ : syracuseStep 1421179 = 2131769) B2131769
theorem B2396047 : Blo 1419529 2396047 := bstep (se 1 (by rfl) ⟨1797035, by rfl⟩ : syracuseStep 2396047 = 3594071) B3594071
theorem B3411887 : Blo 1419529 3411887 := bstep (se 1 (by rfl) ⟨2558915, by rfl⟩ : syracuseStep 3411887 = 5117831) B5117831
theorem B1421231 : Blo 1419529 1421231 := bstep (se 1 (by rfl) ⟨1065923, by rfl⟩ : syracuseStep 1421231 = 2131847) B2131847
theorem B10940345 : Blo 1419529 10940345 := bstep (se 2 (by rfl) ⟨4102629, by rfl⟩ : syracuseStep 10940345 = 8205259) B8205259
theorem B1421255 : Blo 1419529 1421255 := bstep (se 1 (by rfl) ⟨1065941, by rfl⟩ : syracuseStep 1421255 = 2131883) B2131883
theorem B1421275 : Blo 1419529 1421275 := bstep (se 1 (by rfl) ⟨1065956, by rfl⟩ : syracuseStep 1421275 = 2131913) B2131913
theorem B6066191 : Blo 1419529 6066191 := bstep (se 1 (by rfl) ⟨4549643, by rfl⟩ : syracuseStep 6066191 = 9099287) B9099287
theorem B1421351 : Blo 1419529 1421351 := bstep (se 1 (by rfl) ⟨1066013, by rfl⟩ : syracuseStep 1421351 = 2132027) B2132027
theorem B10784825 : Blo 1419529 10784825 := bstep (se 2 (by rfl) ⟨4044309, by rfl⟩ : syracuseStep 10784825 = 8088619) B8088619
theorem B4796495 : Blo 1419529 4796495 := bstep (se 1 (by rfl) ⟨3597371, by rfl⟩ : syracuseStep 4796495 = 7194743) B7194743
theorem B1421391 : Blo 1419529 1421391 := bstep (se 1 (by rfl) ⟨1066043, by rfl⟩ : syracuseStep 1421391 = 2132087) B2132087
theorem B1421407 : Blo 1419529 1421407 := bstep (se 1 (by rfl) ⟨1066055, by rfl⟩ : syracuseStep 1421407 = 2132111) B2132111
theorem B1421435 : Blo 1419529 1421435 := bstep (se 1 (by rfl) ⟨1066076, by rfl⟩ : syracuseStep 1421435 = 2132153) B2132153
theorem B1421487 : Blo 1419529 1421487 := bstep (se 1 (by rfl) ⟨1066115, by rfl⟩ : syracuseStep 1421487 = 2132231) B2132231
theorem B1421511 : Blo 1419529 1421511 := bstep (se 1 (by rfl) ⟨1066133, by rfl⟩ : syracuseStep 1421511 = 2132267) B2132267
theorem B1945963 : Blo 1419529 1945963 := bstep (se 1 (by rfl) ⟨1459472, by rfl⟩ : syracuseStep 1945963 = 2918945) B2918945
theorem B4796873 : Blo 1419529 4796873 := bstep (se 2 (by rfl) ⟨1798827, by rfl⟩ : syracuseStep 4796873 = 3597655) B3597655
theorem B2560531 : Blo 1419529 2560531 := bstep (se 1 (by rfl) ⟨1920398, by rfl⟩ : syracuseStep 2560531 = 3840797) B3840797
theorem B2396729 : Blo 1419529 2396729 := bstep (se 2 (by rfl) ⟨898773, by rfl⟩ : syracuseStep 2396729 = 1797547) B1797547
theorem B4043479 : Blo 1419529 4043479 := bstep (se 1 (by rfl) ⟨3032609, by rfl⟩ : syracuseStep 4043479 = 6065219) B6065219
theorem B4797143 : Blo 1419529 4797143 := bstep (se 1 (by rfl) ⟨3597857, by rfl⟩ : syracuseStep 4797143 = 7195715) B7195715
theorem B4043513 : Blo 1419529 4043513 := bstep (se 2 (by rfl) ⟨1516317, by rfl⟩ : syracuseStep 4043513 = 3032635) B3032635
theorem B5395193 : Blo 1419529 5395193 := bstep (se 2 (by rfl) ⟨2023197, by rfl⟩ : syracuseStep 5395193 = 4046395) B4046395
theorem B9098057 : Blo 1419529 9098057 := bstep (se 2 (by rfl) ⟨3411771, by rfl⟩ : syracuseStep 9098057 = 6823543) B6823543
theorem B20476745 : Blo 1419529 20476745 := bstep (se 2 (by rfl) ⟨7678779, by rfl⟩ : syracuseStep 20476745 = 15357559) B15357559
theorem B4043627 : Blo 1419529 4043627 := bstep (se 1 (by rfl) ⟨3032720, by rfl⟩ : syracuseStep 4043627 = 6065441) B6065441
theorem B4928417 : Blo 1419529 4928417 := bstep (se 2 (by rfl) ⟨1848156, by rfl⟩ : syracuseStep 4928417 = 3696313) B3696313
theorem B4043695 : Blo 1419529 4043695 := bstep (se 1 (by rfl) ⟨3032771, by rfl⟩ : syracuseStep 4043695 = 6065543) B6065543
theorem B4797359 : Blo 1419529 4797359 := bstep (se 1 (by rfl) ⟨3598019, by rfl⟩ : syracuseStep 4797359 = 7196039) B7196039
theorem B4863091 : Blo 1419529 4863091 := bstep (se 1 (by rfl) ⟨3647318, by rfl⟩ : syracuseStep 4863091 = 7294637) B7294637
theorem B12301483 : Blo 1419529 12301483 := bstep (se 1 (by rfl) ⟨9226112, by rfl⟩ : syracuseStep 12301483 = 18452225) B18452225
theorem B2397431 : Blo 1419529 2397431 := bstep (se 1 (by rfl) ⟨1798073, by rfl⟩ : syracuseStep 2397431 = 3596147) B3596147
theorem B2880841 : Blo 1419529 2880841 := bstep (se 2 (by rfl) ⟨1080315, by rfl⟩ : syracuseStep 2880841 = 2160631) B2160631
theorem B5469545 : Blo 1419529 5469545 := bstep (se 2 (by rfl) ⟨2051079, by rfl⟩ : syracuseStep 5469545 = 4102159) B4102159
theorem B7288307 : Blo 1419529 7288307 := bstep (se 1 (by rfl) ⟨5466230, by rfl⟩ : syracuseStep 7288307 = 10932461) B10932461
theorem B3593767 : Blo 1419529 3593767 := bstep (se 1 (by rfl) ⟨2695325, by rfl⟩ : syracuseStep 3593767 = 5390651) B5390651
theorem B2397775 : Blo 1419529 2397775 := bstep (se 1 (by rfl) ⟨1798331, by rfl⟩ : syracuseStep 2397775 = 3596663) B3596663
theorem B2430587 : Blo 1419529 2430587 := bstep (se 1 (by rfl) ⟨1822940, by rfl⟩ : syracuseStep 2430587 = 3645881) B3645881
theorem B5396179 : Blo 1419529 5396179 := bstep (se 1 (by rfl) ⟨4047134, by rfl⟩ : syracuseStep 5396179 = 8094269) B8094269
theorem B18446039 : Blo 1419529 18446039 := bstep (se 1 (by rfl) ⟨13834529, by rfl⟩ : syracuseStep 18446039 = 27669059) B27669059
theorem B3839737 : Blo 1419529 3839737 := bstep (se 2 (by rfl) ⟨1439901, by rfl⟩ : syracuseStep 3839737 = 2879803) B2879803
theorem B2398025 : Blo 1419529 2398025 := bstep (se 2 (by rfl) ⟨899259, by rfl⟩ : syracuseStep 2398025 = 1798519) B1798519
theorem B3594091 : Blo 1419529 3594091 := bstep (se 1 (by rfl) ⟨2695568, by rfl⟩ : syracuseStep 3594091 = 5391137) B5391137
theorem B4437947 : Blo 1419529 4437947 := bstep (se 1 (by rfl) ⟨3328460, by rfl⟩ : syracuseStep 4437947 = 6656921) B6656921
theorem B9107387 : Blo 1419529 9107387 := bstep (se 1 (by rfl) ⟨6830540, by rfl⟩ : syracuseStep 9107387 = 13661081) B13661081
theorem B10786769 : Blo 1419529 10786769 := bstep (se 2 (by rfl) ⟨4045038, by rfl⟩ : syracuseStep 10786769 = 8090077) B8090077
theorem B4044971 : Blo 1419529 4044971 := bstep (se 1 (by rfl) ⟨3033728, by rfl⟩ : syracuseStep 4044971 = 6067457) B6067457
theorem B5396651 : Blo 1419529 5396651 := bstep (se 1 (by rfl) ⟨4047488, by rfl⟩ : syracuseStep 5396651 = 8094977) B8094977
theorem B2398457 : Blo 1419529 2398457 := bstep (se 2 (by rfl) ⟨899421, by rfl⟩ : syracuseStep 2398457 = 1798843) B1798843
theorem B2398639 : Blo 1419529 2398639 := bstep (se 1 (by rfl) ⟨1798979, by rfl⟩ : syracuseStep 2398639 = 3597959) B3597959
theorem B2275771 : Blo 1419529 2275771 := bstep (se 1 (by rfl) ⟨1706828, by rfl⟩ : syracuseStep 2275771 = 3413657) B3413657
theorem B3594739 : Blo 1419529 3594739 := bstep (se 1 (by rfl) ⟨2696054, by rfl⟩ : syracuseStep 3594739 = 5392109) B5392109
theorem B2398727 : Blo 1419529 2398727 := bstep (se 1 (by rfl) ⟨1799045, by rfl⟩ : syracuseStep 2398727 = 3598091) B3598091
theorem B5118497 : Blo 1419529 5118497 := bstep (se 2 (by rfl) ⟨1919436, by rfl⟩ : syracuseStep 5118497 = 3838873) B3838873
theorem B2021927 : Blo 1419529 2021927 := bstep (se 1 (by rfl) ⟨1516445, by rfl⟩ : syracuseStep 2021927 = 3032891) B3032891
theorem B4553567 : Blo 1419529 4553567 := bstep (se 1 (by rfl) ⟨3415175, by rfl⟩ : syracuseStep 4553567 = 6830351) B6830351
theorem B2595727 : Blo 1419529 2595727 := bstep (se 1 (by rfl) ⟨1946795, by rfl⟩ : syracuseStep 2595727 = 3893591) B3893591
theorem B9100289 : Blo 1419529 9100289 := bstep (se 2 (by rfl) ⟨3412608, by rfl⟩ : syracuseStep 9100289 = 6825217) B6825217
theorem B4791311 : Blo 1419529 4791311 := bstep (se 1 (by rfl) ⟨3593483, by rfl⟩ : syracuseStep 4791311 = 7186967) B7186967
theorem B3194027 : Blo 1419529 3194027 := bstep (se 1 (by rfl) ⟨2395520, by rfl⟩ : syracuseStep 3194027 = 4791041) B4791041
theorem B21855511 : Blo 1419529 21855511 := bstep (se 1 (by rfl) ⟨16391633, by rfl⟩ : syracuseStep 21855511 = 32783267) B32783267
theorem B12139901 : Blo 1419529 12139901 := bstep (se 3 (by rfl) ⟨2276231, by rfl⟩ : syracuseStep 12139901 = 4552463) B4552463
theorem B5119375 : Blo 1419529 5119375 := bstep (se 1 (by rfl) ⟨3839531, by rfl⟩ : syracuseStep 5119375 = 7679063) B7679063
theorem B2129327 : Blo 1419529 2129327 := bstep (se 1 (by rfl) ⟨1596995, by rfl⟩ : syracuseStep 2129327 = 3193991) B3193991
theorem B2129417 : Blo 1419529 2129417 := bstep (se 2 (by rfl) ⟨798531, by rfl⟩ : syracuseStep 2129417 = 1597063) B1597063
theorem B2129447 : Blo 1419529 2129447 := bstep (se 1 (by rfl) ⟨1597085, by rfl⟩ : syracuseStep 2129447 = 3194171) B3194171
theorem B4791905 : Blo 1419529 4791905 := bstep (se 2 (by rfl) ⟨1796964, by rfl⟩ : syracuseStep 4791905 = 3593929) B3593929
theorem B3595873 : Blo 1419529 3595873 := bstep (se 2 (by rfl) ⟨1348452, by rfl⟩ : syracuseStep 3595873 = 2696905) B2696905
theorem B2129531 : Blo 1419529 2129531 := bstep (se 1 (by rfl) ⟨1597148, by rfl⟩ : syracuseStep 2129531 = 3194297) B3194297
theorem B23363261 : Blo 1419529 23363261 := bstep (se 3 (by rfl) ⟨4380611, by rfl⟩ : syracuseStep 23363261 = 8761223) B8761223
theorem B3194567 : Blo 1419529 3194567 := bstep (se 1 (by rfl) ⟨2395925, by rfl⟩ : syracuseStep 3194567 = 4791851) B4791851
theorem B2129657 : Blo 1419529 2129657 := bstep (se 2 (by rfl) ⟨798621, by rfl⟩ : syracuseStep 2129657 = 1597243) B1597243
theorem B7192313 : Blo 1419529 7192313 := bstep (se 2 (by rfl) ⟨2697117, by rfl⟩ : syracuseStep 7192313 = 5394235) B5394235
theorem B84188929 : Blo 1419529 84188929 := bstep (se 2 (by rfl) ⟨31570848, by rfl⟩ : syracuseStep 84188929 = 63141697) B63141697
theorem B10379051 : Blo 1419529 10379051 := bstep (se 1 (by rfl) ⟨7784288, by rfl⟩ : syracuseStep 10379051 = 15568577) B15568577
theorem B5758793 : Blo 1419529 5758793 := bstep (se 2 (by rfl) ⟨2159547, by rfl⟩ : syracuseStep 5758793 = 4319095) B4319095
theorem B2695007 : Blo 1419529 2695007 := bstep (se 1 (by rfl) ⟨2021255, by rfl⟩ : syracuseStep 2695007 = 4042511) B4042511
theorem B1597279 : Blo 1419529 1597279 := bstep (se 1 (by rfl) ⟨1197959, by rfl⟩ : syracuseStep 1597279 = 2395919) B2395919
theorem B2129759 : Blo 1419529 2129759 := bstep (se 1 (by rfl) ⟨1597319, by rfl⟩ : syracuseStep 2129759 = 3194639) B3194639
theorem B2129771 : Blo 1419529 2129771 := bstep (se 1 (by rfl) ⟨1597328, by rfl⟩ : syracuseStep 2129771 = 3194657) B3194657
theorem B10239929 : Blo 1419529 10239929 := bstep (se 2 (by rfl) ⟨3839973, by rfl⟩ : syracuseStep 10239929 = 7679947) B7679947
theorem B13647973 : Blo 1419529 13647973 := bstep (se 4 (by rfl) ⟨1279497, by rfl⟩ : syracuseStep 13647973 = 2558995) B2558995
theorem B2130185 : Blo 1419529 2130185 := bstep (se 2 (by rfl) ⟨798819, by rfl⟩ : syracuseStep 2130185 = 1597639) B1597639
theorem B2130287 : Blo 1419529 2130287 := bstep (se 1 (by rfl) ⟨1597715, by rfl⟩ : syracuseStep 2130287 = 3195431) B3195431
theorem B1597819 : Blo 1419529 1597819 := bstep (se 1 (by rfl) ⟨1198364, by rfl⟩ : syracuseStep 1597819 = 2396729) B2396729
theorem B10936777 : Blo 1419529 10936777 := bstep (se 2 (by rfl) ⟨4101291, by rfl⟩ : syracuseStep 10936777 = 8202583) B8202583
theorem B2695675 : Blo 1419529 2695675 := bstep (se 1 (by rfl) ⟨2021756, by rfl⟩ : syracuseStep 2695675 = 4043513) B4043513
theorem B3596795 : Blo 1419529 3596795 := bstep (se 1 (by rfl) ⟨2697596, by rfl⟩ : syracuseStep 3596795 = 5395193) B5395193
theorem B2695751 : Blo 1419529 2695751 := bstep (se 1 (by rfl) ⟨2021813, by rfl⟩ : syracuseStep 2695751 = 4043627) B4043627
theorem B2130503 : Blo 1419529 2130503 := bstep (se 1 (by rfl) ⟨1597877, by rfl⟩ : syracuseStep 2130503 = 3195755) B3195755
theorem B2130539 : Blo 1419529 2130539 := bstep (se 1 (by rfl) ⟨1597904, by rfl⟩ : syracuseStep 2130539 = 3195809) B3195809
theorem B3285611 : Blo 1419529 3285611 := bstep (se 1 (by rfl) ⟨2464208, by rfl⟩ : syracuseStep 3285611 = 4928417) B4928417
theorem B4792985 : Blo 1419529 4792985 := bstep (se 2 (by rfl) ⟨1797369, by rfl⟩ : syracuseStep 4792985 = 3594739) B3594739
theorem B3195575 : Blo 1419529 3195575 := bstep (se 1 (by rfl) ⟨2396681, by rfl⟩ : syracuseStep 3195575 = 4793363) B4793363
theorem B2130767 : Blo 1419529 2130767 := bstep (se 1 (by rfl) ⟨1598075, by rfl⟩ : syracuseStep 2130767 = 3196151) B3196151
theorem B1598287 : Blo 1419529 1598287 := bstep (se 1 (by rfl) ⟨1198715, by rfl⟩ : syracuseStep 1598287 = 2397431) B2397431
theorem B3195791 : Blo 1419529 3195791 := bstep (se 1 (by rfl) ⟨2396843, by rfl⟩ : syracuseStep 3195791 = 4793687) B4793687
theorem B5391305 : Blo 1419529 5391305 := bstep (se 2 (by rfl) ⟨2021739, by rfl⟩ : syracuseStep 5391305 = 4043479) B4043479
theorem B4858871 : Blo 1419529 4858871 := bstep (se 1 (by rfl) ⟨3644153, by rfl⟩ : syracuseStep 4858871 = 7288307) B7288307
theorem B12297359 : Blo 1419529 12297359 := bstep (se 1 (by rfl) ⟨9223019, by rfl⟩ : syracuseStep 12297359 = 18446039) B18446039
theorem B2131163 : Blo 1419529 2131163 := bstep (se 1 (by rfl) ⟨1598372, by rfl⟩ : syracuseStep 2131163 = 3196745) B3196745
theorem B1598683 : Blo 1419529 1598683 := bstep (se 1 (by rfl) ⟨1199012, by rfl⟩ : syracuseStep 1598683 = 2398025) B2398025
theorem B5391593 : Blo 1419529 5391593 := bstep (se 2 (by rfl) ⟨2021847, by rfl⟩ : syracuseStep 5391593 = 4043695) B4043695
theorem B6071591 : Blo 1419529 6071591 := bstep (se 1 (by rfl) ⟨4553693, by rfl⟩ : syracuseStep 6071591 = 9107387) B9107387
theorem B2131337 : Blo 1419529 2131337 := bstep (se 2 (by rfl) ⟨799251, by rfl⟩ : syracuseStep 2131337 = 1598503) B1598503
theorem B3327419 : Blo 1419529 3327419 := bstep (se 1 (by rfl) ⟨2495564, by rfl⟩ : syracuseStep 3327419 = 4991129) B4991129
theorem B5391805 : Blo 1419529 5391805 := bstep (se 3 (by rfl) ⟨1010963, by rfl⟩ : syracuseStep 5391805 = 2021927) B2021927
theorem B2696647 : Blo 1419529 2696647 := bstep (se 1 (by rfl) ⟨2022485, by rfl⟩ : syracuseStep 2696647 = 4044971) B4044971
theorem B3597767 : Blo 1419529 3597767 := bstep (se 1 (by rfl) ⟨2698325, by rfl⟩ : syracuseStep 3597767 = 5396651) B5396651
theorem B3597817 : Blo 1419529 3597817 := bstep (se 2 (by rfl) ⟨1349181, by rfl⟩ : syracuseStep 3597817 = 2698363) B2698363
theorem B1598971 : Blo 1419529 1598971 := bstep (se 1 (by rfl) ⟨1199228, by rfl⟩ : syracuseStep 1598971 = 2398457) B2398457
theorem B16401977 : Blo 1419529 16401977 := bstep (se 2 (by rfl) ⟨6150741, by rfl⟩ : syracuseStep 16401977 = 12301483) B12301483
theorem B3196511 : Blo 1419529 3196511 := bstep (se 1 (by rfl) ⟨2397383, by rfl⟩ : syracuseStep 3196511 = 4794767) B4794767
theorem B1599151 : Blo 1419529 1599151 := bstep (se 1 (by rfl) ⟨1199363, by rfl⟩ : syracuseStep 1599151 = 2398727) B2398727
theorem B49178333 : Blo 1419529 49178333 := bstep (se 3 (by rfl) ⟨9220937, by rfl⟩ : syracuseStep 49178333 = 18441875) B18441875
theorem B2131691 : Blo 1419529 2131691 := bstep (se 1 (by rfl) ⟨1598768, by rfl⟩ : syracuseStep 2131691 = 3197537) B3197537
theorem B116844281 : Blo 1419529 116844281 := bstep (se 2 (by rfl) ⟨43816605, by rfl⟩ : syracuseStep 116844281 = 87633211) B87633211
theorem B3598121 : Blo 1419529 3598121 := bstep (se 2 (by rfl) ⟨1349295, by rfl⟩ : syracuseStep 3598121 = 2698591) B2698591
theorem B3196727 : Blo 1419529 3196727 := bstep (se 1 (by rfl) ⟨2397545, by rfl⟩ : syracuseStep 3196727 = 4795091) B4795091
theorem B6825833 : Blo 1419529 6825833 := bstep (se 2 (by rfl) ⟨2559687, by rfl⟩ : syracuseStep 6825833 = 5119375) B5119375
theorem B2131919 : Blo 1419529 2131919 := bstep (se 1 (by rfl) ⟨1598939, by rfl⟩ : syracuseStep 2131919 = 3197879) B3197879
theorem B3197033 : Blo 1419529 3197033 := bstep (se 2 (by rfl) ⟨1198887, by rfl⟩ : syracuseStep 3197033 = 2397775) B2397775
theorem B4794497 : Blo 1419529 4794497 := bstep (se 2 (by rfl) ⟨1797936, by rfl⟩ : syracuseStep 4794497 = 3595873) B3595873
theorem B7194905 : Blo 1419529 7194905 := bstep (se 2 (by rfl) ⟨2698089, by rfl⟩ : syracuseStep 7194905 = 5396179) B5396179
theorem B5835037 : Blo 1419529 5835037 := bstep (se 3 (by rfl) ⟨1094069, by rfl⟩ : syracuseStep 5835037 = 2188139) B2188139
theorem B1419551 : Blo 1419529 1419551 := bstep (se 1 (by rfl) ⟨1064663, by rfl⟩ : syracuseStep 1419551 = 2129327) B2129327
theorem B1419611 : Blo 1419529 1419611 := bstep (se 1 (by rfl) ⟨1064708, by rfl⟩ : syracuseStep 1419611 = 2129417) B2129417
theorem B1419631 : Blo 1419529 1419631 := bstep (se 1 (by rfl) ⟨1064723, by rfl⟩ : syracuseStep 1419631 = 2129447) B2129447
theorem B1419687 : Blo 1419529 1419687 := bstep (se 1 (by rfl) ⟨1064765, by rfl⟩ : syracuseStep 1419687 = 2129531) B2129531
theorem B9095597 : Blo 1419529 9095597 := bstep (se 3 (by rfl) ⟨1705424, by rfl⟩ : syracuseStep 9095597 = 3410849) B3410849
theorem B15575507 : Blo 1419529 15575507 := bstep (se 1 (by rfl) ⟨11681630, by rfl⟩ : syracuseStep 15575507 = 23363261) B23363261
theorem B1419771 : Blo 1419529 1419771 := bstep (se 1 (by rfl) ⟨1064828, by rfl⟩ : syracuseStep 1419771 = 2129657) B2129657
theorem B4794875 : Blo 1419529 4794875 := bstep (se 1 (by rfl) ⟨3596156, by rfl⟩ : syracuseStep 4794875 = 7192313) B7192313
theorem B1796671 : Blo 1419529 1796671 := bstep (se 1 (by rfl) ⟨1347503, by rfl⟩ : syracuseStep 1796671 = 2695007) B2695007
theorem B1419839 : Blo 1419529 1419839 := bstep (se 1 (by rfl) ⟨1064879, by rfl⟩ : syracuseStep 1419839 = 2129759) B2129759
theorem B1419847 : Blo 1419529 1419847 := bstep (se 1 (by rfl) ⟨1064885, by rfl⟩ : syracuseStep 1419847 = 2129771) B2129771
theorem B3197519 : Blo 1419529 3197519 := bstep (se 1 (by rfl) ⟨2398139, by rfl⟩ : syracuseStep 3197519 = 4796279) B4796279
theorem B6826619 : Blo 1419529 6826619 := bstep (se 1 (by rfl) ⟨5119964, by rfl⟩ : syracuseStep 6826619 = 10239929) B10239929
theorem B7293563 : Blo 1419529 7293563 := bstep (se 1 (by rfl) ⟨5470172, by rfl⟩ : syracuseStep 7293563 = 10940345) B10940345
theorem B1419999 : Blo 1419529 1419999 := bstep (se 1 (by rfl) ⟨1064999, by rfl⟩ : syracuseStep 1419999 = 2129999) B2129999
theorem B3197663 : Blo 1419529 3197663 := bstep (se 1 (by rfl) ⟨2398247, by rfl⟩ : syracuseStep 3197663 = 4796495) B4796495
theorem B1796843 : Blo 1419529 1796843 := bstep (se 1 (by rfl) ⟨1347632, by rfl⟩ : syracuseStep 1796843 = 2695265) B2695265
theorem B5122835 : Blo 1419529 5122835 := bstep (se 1 (by rfl) ⟨3842126, by rfl⟩ : syracuseStep 5122835 = 7684253) B7684253
theorem B1420079 : Blo 1419529 1420079 := bstep (se 1 (by rfl) ⟨1065059, by rfl⟩ : syracuseStep 1420079 = 2130119) B2130119
theorem B1420187 : Blo 1419529 1420187 := bstep (se 1 (by rfl) ⟨1065140, by rfl⟩ : syracuseStep 1420187 = 2130281) B2130281
theorem B4795307 : Blo 1419529 4795307 := bstep (se 1 (by rfl) ⟨3596480, by rfl⟩ : syracuseStep 4795307 = 7192961) B7192961
theorem B1420239 : Blo 1419529 1420239 := bstep (se 1 (by rfl) ⟨1065179, by rfl⟩ : syracuseStep 1420239 = 2130359) B2130359
theorem B3197915 : Blo 1419529 3197915 := bstep (se 1 (by rfl) ⟨2398436, by rfl⟩ : syracuseStep 3197915 = 4796873) B4796873
theorem B1420263 : Blo 1419529 1420263 := bstep (se 1 (by rfl) ⟨1065197, by rfl⟩ : syracuseStep 1420263 = 2130395) B2130395
theorem B5123195 : Blo 1419529 5123195 := bstep (se 1 (by rfl) ⟨3842396, by rfl⟩ : syracuseStep 5123195 = 7684793) B7684793
theorem B3198095 : Blo 1419529 3198095 := bstep (se 1 (by rfl) ⟨2398571, by rfl⟩ : syracuseStep 3198095 = 4797143) B4797143
theorem B6065371 : Blo 1419529 6065371 := bstep (se 1 (by rfl) ⟨4549028, by rfl⟩ : syracuseStep 6065371 = 9098057) B9098057
theorem B13651163 : Blo 1419529 13651163 := bstep (se 1 (by rfl) ⟨10238372, by rfl⟩ : syracuseStep 13651163 = 20476745) B20476745
theorem B3198185 : Blo 1419529 3198185 := bstep (se 2 (by rfl) ⟨1199319, by rfl⟩ : syracuseStep 3198185 = 2398639) B2398639
theorem B3034361 : Blo 1419529 3034361 := bstep (se 2 (by rfl) ⟨1137885, by rfl⟩ : syracuseStep 3034361 = 2275771) B2275771
theorem B1420575 : Blo 1419529 1420575 := bstep (se 1 (by rfl) ⟨1065431, by rfl⟩ : syracuseStep 1420575 = 2130863) B2130863
theorem B3198239 : Blo 1419529 3198239 := bstep (se 1 (by rfl) ⟨2398679, by rfl⟩ : syracuseStep 3198239 = 4797359) B4797359
theorem B8088893 : Blo 1419529 8088893 := bstep (se 3 (by rfl) ⟨1516667, by rfl⟩ : syracuseStep 8088893 = 3033335) B3033335
theorem B1420635 : Blo 1419529 1420635 := bstep (se 1 (by rfl) ⟨1065476, by rfl⟩ : syracuseStep 1420635 = 2130953) B2130953
theorem B1420655 : Blo 1419529 1420655 := bstep (se 1 (by rfl) ⟨1065491, by rfl⟩ : syracuseStep 1420655 = 2130983) B2130983
theorem B1944955 : Blo 1419529 1944955 := bstep (se 1 (by rfl) ⟨1458716, by rfl⟩ : syracuseStep 1944955 = 2917433) B2917433
theorem B1420711 : Blo 1419529 1420711 := bstep (se 1 (by rfl) ⟨1065533, by rfl⟩ : syracuseStep 1420711 = 2131067) B2131067
theorem B4795847 : Blo 1419529 4795847 := bstep (se 1 (by rfl) ⟨3596885, by rfl⟩ : syracuseStep 4795847 = 7193771) B7193771
theorem B1420795 : Blo 1419529 1420795 := bstep (se 1 (by rfl) ⟨1065596, by rfl⟩ : syracuseStep 1420795 = 2131193) B2131193
theorem B12127805 : Blo 1419529 12127805 := bstep (se 3 (by rfl) ⟨2273963, by rfl⟩ : syracuseStep 12127805 = 4547927) B4547927
theorem B1420863 : Blo 1419529 1420863 := bstep (se 1 (by rfl) ⟨1065647, by rfl⟩ : syracuseStep 1420863 = 2131295) B2131295
theorem B1420871 : Blo 1419529 1420871 := bstep (se 1 (by rfl) ⟨1065653, by rfl⟩ : syracuseStep 1420871 = 2131307) B2131307
theorem B14585453 : Blo 1419529 14585453 := bstep (se 3 (by rfl) ⟨2734772, by rfl⟩ : syracuseStep 14585453 = 5469545) B5469545
theorem B11521709 : Blo 1419529 11521709 := bstep (se 3 (by rfl) ⟨2160320, by rfl⟩ : syracuseStep 11521709 = 4320641) B4320641
theorem B1797815 : Blo 1419529 1797815 := bstep (se 1 (by rfl) ⟨1348361, by rfl⟩ : syracuseStep 1797815 = 2696723) B2696723
theorem B373616327 : Blo 1419529 373616327 := bstep (se 1 (by rfl) ⟨280212245, by rfl⟩ : syracuseStep 373616327 = 560424491) B560424491
theorem B1421023 : Blo 1419529 1421023 := bstep (se 1 (by rfl) ⟨1065767, by rfl⟩ : syracuseStep 1421023 = 2131535) B2131535
theorem B25931501 : Blo 1419529 25931501 := bstep (se 3 (by rfl) ⟨4862156, by rfl⟩ : syracuseStep 25931501 = 9724313) B9724313
theorem B4796171 : Blo 1419529 4796171 := bstep (se 1 (by rfl) ⟨3597128, by rfl⟩ : syracuseStep 4796171 = 7194257) B7194257
theorem B1421103 : Blo 1419529 1421103 := bstep (se 1 (by rfl) ⟨1065827, by rfl⟩ : syracuseStep 1421103 = 2131655) B2131655
theorem B1797967 : Blo 1419529 1797967 := bstep (se 1 (by rfl) ⟨1348475, by rfl⟩ : syracuseStep 1797967 = 2696951) B2696951
theorem B1421211 : Blo 1419529 1421211 := bstep (se 1 (by rfl) ⟨1065908, by rfl⟩ : syracuseStep 1421211 = 2131817) B2131817
theorem B1421263 : Blo 1419529 1421263 := bstep (se 1 (by rfl) ⟨1065947, by rfl⟩ : syracuseStep 1421263 = 2131895) B2131895
theorem B1421287 : Blo 1419529 1421287 := bstep (se 1 (by rfl) ⟨1065965, by rfl⟩ : syracuseStep 1421287 = 2131931) B2131931
theorem B4796441 : Blo 1419529 4796441 := bstep (se 2 (by rfl) ⟨1798665, by rfl⟩ : syracuseStep 4796441 = 3597331) B3597331
theorem B12136553 : Blo 1419529 12136553 := bstep (se 2 (by rfl) ⟨4551207, by rfl⟩ : syracuseStep 12136553 = 9102415) B9102415
theorem B6484121 : Blo 1419529 6484121 := bstep (se 2 (by rfl) ⟨2431545, by rfl⟩ : syracuseStep 6484121 = 4863091) B4863091
theorem B2396425 : Blo 1419529 2396425 := bstep (se 2 (by rfl) ⟨898659, by rfl⟩ : syracuseStep 2396425 = 1797319) B1797319
theorem B17985899 : Blo 1419529 17985899 := bstep (se 1 (by rfl) ⟨13489424, by rfl⟩ : syracuseStep 17985899 = 26978849) B26978849
theorem B3412331 : Blo 1419529 3412331 := bstep (se 1 (by rfl) ⟨2559248, by rfl⟩ : syracuseStep 3412331 = 5118497) B5118497
theorem B7188911 : Blo 1419529 7188911 := bstep (se 1 (by rfl) ⟨5391683, by rfl⟩ : syracuseStep 7188911 = 10783367) B10783367
theorem B18215387 : Blo 1419529 18215387 := bstep (se 1 (by rfl) ⟨13661540, by rfl⟩ : syracuseStep 18215387 = 27323081) B27323081
theorem B3035711 : Blo 1419529 3035711 := bstep (se 1 (by rfl) ⟨2276783, by rfl⟩ : syracuseStep 3035711 = 4553567) B4553567
theorem B2732617 : Blo 1419529 2732617 := bstep (se 2 (by rfl) ⟨1024731, by rfl⟩ : syracuseStep 2732617 = 2049463) B2049463
theorem B6066859 : Blo 1419529 6066859 := bstep (se 1 (by rfl) ⟨4550144, by rfl⟩ : syracuseStep 6066859 = 9100289) B9100289
theorem B4551643 : Blo 1419529 4551643 := bstep (se 1 (by rfl) ⟨3413732, by rfl⟩ : syracuseStep 4551643 = 6827465) B6827465
theorem B112251905 : Blo 1419529 112251905 := bstep (se 2 (by rfl) ⟨42094464, by rfl⟩ : syracuseStep 112251905 = 84188929) B84188929
theorem B9098365 : Blo 1419529 9098365 := bstep (se 3 (by rfl) ⟨1705943, by rfl⟩ : syracuseStep 9098365 = 3411887) B3411887
theorem B26277011 : Blo 1419529 26277011 := bstep (se 1 (by rfl) ⟨19707758, by rfl⟩ : syracuseStep 26277011 = 39415517) B39415517
theorem B11834525 : Blo 1419529 11834525 := bstep (se 3 (by rfl) ⟨2218973, by rfl⟩ : syracuseStep 11834525 = 4437947) B4437947
theorem B6919367 : Blo 1419529 6919367 := bstep (se 1 (by rfl) ⟨5189525, by rfl⟩ : syracuseStep 6919367 = 10379051) B10379051
theorem B3839195 : Blo 1419529 3839195 := bstep (se 1 (by rfl) ⟨2879396, by rfl⟩ : syracuseStep 3839195 = 5758793) B5758793
theorem B7189883 : Blo 1419529 7189883 := bstep (se 1 (by rfl) ⟨5392412, by rfl⟩ : syracuseStep 7189883 = 10784825) B10784825
theorem B16176509 : Blo 1419529 16176509 := bstep (se 3 (by rfl) ⟨3033095, by rfl⟩ : syracuseStep 16176509 = 6066191) B6066191
theorem B2397883 : Blo 1419529 2397883 := bstep (se 1 (by rfl) ⟨1798412, by rfl⟩ : syracuseStep 2397883 = 3596825) B3596825
theorem B3594041 : Blo 1419529 3594041 := bstep (se 2 (by rfl) ⟨1347765, by rfl⟩ : syracuseStep 3594041 = 2695531) B2695531
theorem B3414041 : Blo 1419529 3414041 := bstep (se 2 (by rfl) ⟨1280265, by rfl⟩ : syracuseStep 3414041 = 2560531) B2560531
theorem B5396665 : Blo 1419529 5396665 := bstep (se 2 (by rfl) ⟨2023749, by rfl⟩ : syracuseStep 5396665 = 4047499) B4047499
theorem B1620391 : Blo 1419529 1620391 := bstep (se 1 (by rfl) ⟨1215293, by rfl⟩ : syracuseStep 1620391 = 2430587) B2430587
theorem B10787255 : Blo 1419529 10787255 := bstep (se 1 (by rfl) ⟨8090441, by rfl⟩ : syracuseStep 10787255 = 16180883) B16180883
theorem B9853435 : Blo 1419529 9853435 := bstep (se 1 (by rfl) ⟨7390076, by rfl⟩ : syracuseStep 9853435 = 14780153) B14780153
theorem B7191179 : Blo 1419529 7191179 := bstep (se 1 (by rfl) ⟨5393384, by rfl⟩ : syracuseStep 7191179 = 10786769) B10786769
theorem B116562725 : Blo 1419529 116562725 := bstep (se 4 (by rfl) ⟨10927755, by rfl⟩ : syracuseStep 116562725 = 21855511) B21855511
theorem B3841121 : Blo 1419529 3841121 := bstep (se 2 (by rfl) ⟨1440420, by rfl⟩ : syracuseStep 3841121 = 2880841) B2880841
theorem B4791419 : Blo 1419529 4791419 := bstep (se 1 (by rfl) ⟨3593564, by rfl⟩ : syracuseStep 4791419 = 7187129) B7187129
theorem B3595387 : Blo 1419529 3595387 := bstep (se 1 (by rfl) ⟨2696540, by rfl⟩ : syracuseStep 3595387 = 5393081) B5393081
theorem B15359165 : Blo 1419529 15359165 := bstep (se 3 (by rfl) ⟨2879843, by rfl⟩ : syracuseStep 15359165 = 5759687) B5759687
theorem B10378469 : Blo 1419529 10378469 := bstep (se 4 (by rfl) ⟨972981, by rfl⟩ : syracuseStep 10378469 = 1945963) B1945963
theorem B6823235 : Blo 1419529 6823235 := bstep (se 1 (by rfl) ⟨5117426, by rfl⟩ : syracuseStep 6823235 = 10234853) B10234853
theorem B3194207 : Blo 1419529 3194207 := bstep (se 1 (by rfl) ⟨2395655, by rfl⟩ : syracuseStep 3194207 = 4791311) B4791311
theorem B4791689 : Blo 1419529 4791689 := bstep (se 2 (by rfl) ⟨1796883, by rfl⟩ : syracuseStep 4791689 = 3593767) B3593767
theorem B13843877 : Blo 1419529 13843877 := bstep (se 4 (by rfl) ⟨1297863, by rfl⟩ : syracuseStep 13843877 = 2595727) B2595727
theorem B2129351 : Blo 1419529 2129351 := bstep (se 1 (by rfl) ⟨1597013, by rfl⟩ : syracuseStep 2129351 = 3194027) B3194027
theorem B25927127 : Blo 1419529 25927127 := bstep (se 1 (by rfl) ⟨19445345, by rfl⟩ : syracuseStep 25927127 = 38890691) B38890691
theorem B1596991 : Blo 1419529 1596991 := bstep (se 1 (by rfl) ⟨1197743, by rfl⟩ : syracuseStep 1596991 = 2395487) B2395487
theorem B8093267 : Blo 1419529 8093267 := bstep (se 1 (by rfl) ⟨6069950, by rfl⟩ : syracuseStep 8093267 = 12139901) B12139901
theorem B18210419 : Blo 1419529 18210419 := bstep (se 1 (by rfl) ⟨13657814, by rfl⟩ : syracuseStep 18210419 = 27315629) B27315629
theorem B5119649 : Blo 1419529 5119649 := bstep (se 2 (by rfl) ⟨1919868, by rfl⟩ : syracuseStep 5119649 = 3839737) B3839737
theorem B3194603 : Blo 1419529 3194603 := bstep (se 1 (by rfl) ⟨2395952, by rfl⟩ : syracuseStep 3194603 = 4791905) B4791905
theorem B2129705 : Blo 1419529 2129705 := bstep (se 2 (by rfl) ⟨798639, by rfl⟩ : syracuseStep 2129705 = 1597279) B1597279
theorem B2129711 : Blo 1419529 2129711 := bstep (se 1 (by rfl) ⟨1597283, by rfl⟩ : syracuseStep 2129711 = 3194567) B3194567
theorem B4792121 : Blo 1419529 4792121 := bstep (se 2 (by rfl) ⟨1797045, by rfl⟩ : syracuseStep 4792121 = 3594091) B3594091
theorem B3194729 : Blo 1419529 3194729 := bstep (se 2 (by rfl) ⟨1198023, by rfl⟩ : syracuseStep 3194729 = 2396047) B2396047
theorem B4792607 : Blo 1419529 4792607 := bstep (se 1 (by rfl) ⟨3594455, by rfl⟩ : syracuseStep 4792607 = 7188911) B7188911
theorem B3195233 : Blo 1419529 3195233 := bstep (se 2 (by rfl) ⟨1198212, by rfl⟩ : syracuseStep 3195233 = 2396425) B2396425
theorem B32792957 : Blo 1419529 32792957 := bstep (se 3 (by rfl) ⟨6148679, by rfl⟩ : syracuseStep 32792957 = 12297359) B12297359
theorem B2023807 : Blo 1419529 2023807 := bstep (se 1 (by rfl) ⟨1517855, by rfl⟩ : syracuseStep 2023807 = 3035711) B3035711
theorem B3195323 : Blo 1419529 3195323 := bstep (se 1 (by rfl) ⟨2396492, by rfl⟩ : syracuseStep 3195323 = 4792985) B4792985
theorem B2130383 : Blo 1419529 2130383 := bstep (se 1 (by rfl) ⟨1597787, by rfl⟩ : syracuseStep 2130383 = 3195575) B3195575
theorem B2130425 : Blo 1419529 2130425 := bstep (se 2 (by rfl) ⟨798909, by rfl⟩ : syracuseStep 2130425 = 1597819) B1597819
theorem B2130527 : Blo 1419529 2130527 := bstep (se 1 (by rfl) ⟨1597895, by rfl⟩ : syracuseStep 2130527 = 3195791) B3195791
theorem B14582369 : Blo 1419529 14582369 := bstep (se 2 (by rfl) ⟨5468388, by rfl⟩ : syracuseStep 14582369 = 10936777) B10936777
theorem B74834603 : Blo 1419529 74834603 := bstep (se 1 (by rfl) ⟨56125952, by rfl⟩ : syracuseStep 74834603 = 112251905) B112251905
theorem B7889683 : Blo 1419529 7889683 := bstep (se 1 (by rfl) ⟨5917262, by rfl⟩ : syracuseStep 7889683 = 11834525) B11834525
theorem B18195293 : Blo 1419529 18195293 := bstep (se 3 (by rfl) ⟨3411617, by rfl⟩ : syracuseStep 18195293 = 6823235) B6823235
theorem B4047727 : Blo 1419529 4047727 := bstep (se 1 (by rfl) ⟨3035795, by rfl⟩ : syracuseStep 4047727 = 6071591) B6071591
theorem B4793255 : Blo 1419529 4793255 := bstep (se 1 (by rfl) ⟨3594941, by rfl⟩ : syracuseStep 4793255 = 7189883) B7189883
theorem B2131007 : Blo 1419529 2131007 := bstep (se 1 (by rfl) ⟨1598255, by rfl⟩ : syracuseStep 2131007 = 3196511) B3196511
theorem B2131049 : Blo 1419529 2131049 := bstep (se 2 (by rfl) ⟨799143, by rfl⟩ : syracuseStep 2131049 = 1598287) B1598287
theorem B32785555 : Blo 1419529 32785555 := bstep (se 1 (by rfl) ⟨24589166, by rfl⟩ : syracuseStep 32785555 = 49178333) B49178333
theorem B2131151 : Blo 1419529 2131151 := bstep (se 1 (by rfl) ⟨1598363, by rfl⟩ : syracuseStep 2131151 = 3196727) B3196727
theorem B2131355 : Blo 1419529 2131355 := bstep (se 1 (by rfl) ⟨1598516, by rfl⟩ : syracuseStep 2131355 = 3197033) B3197033
theorem B3196331 : Blo 1419529 3196331 := bstep (se 1 (by rfl) ⟨2397248, by rfl⟩ : syracuseStep 3196331 = 4794497) B4794497
theorem B4793849 : Blo 1419529 4793849 := bstep (se 2 (by rfl) ⟨1797693, by rfl⟩ : syracuseStep 4793849 = 3595387) B3595387
theorem B6063731 : Blo 1419529 6063731 := bstep (se 1 (by rfl) ⟨4547798, by rfl⟩ : syracuseStep 6063731 = 9095597) B9095597
theorem B8087161 : Blo 1419529 8087161 := bstep (se 2 (by rfl) ⟨3032685, by rfl⟩ : syracuseStep 8087161 = 6065371) B6065371
theorem B2131577 : Blo 1419529 2131577 := bstep (se 2 (by rfl) ⟨799341, by rfl⟩ : syracuseStep 2131577 = 1598683) B1598683
theorem B3196583 : Blo 1419529 3196583 := bstep (se 1 (by rfl) ⟨2397437, by rfl⟩ : syracuseStep 3196583 = 4794875) B4794875
theorem B2131679 : Blo 1419529 2131679 := bstep (se 1 (by rfl) ⟨1598759, by rfl⟩ : syracuseStep 2131679 = 3197519) B3197519
theorem B4794119 : Blo 1419529 4794119 := bstep (se 1 (by rfl) ⟨3595589, by rfl⟩ : syracuseStep 4794119 = 7191179) B7191179
theorem B4794173 : Blo 1419529 4794173 := bstep (se 3 (by rfl) ⟨898907, by rfl⟩ : syracuseStep 4794173 = 1797815) B1797815
theorem B2131775 : Blo 1419529 2131775 := bstep (se 1 (by rfl) ⟨1598831, by rfl⟩ : syracuseStep 2131775 = 3197663) B3197663
theorem B3196871 : Blo 1419529 3196871 := bstep (se 1 (by rfl) ⟨2397653, by rfl⟩ : syracuseStep 3196871 = 4795307) B4795307
theorem B10373093 : Blo 1419529 10373093 := bstep (se 4 (by rfl) ⟨972477, by rfl⟩ : syracuseStep 10373093 = 1944955) B1944955
theorem B2131943 : Blo 1419529 2131943 := bstep (se 1 (by rfl) ⟨1598957, by rfl⟩ : syracuseStep 2131943 = 3197915) B3197915
theorem B2131961 : Blo 1419529 2131961 := bstep (se 2 (by rfl) ⟨799485, by rfl⟩ : syracuseStep 2131961 = 1598971) B1598971
theorem B2132063 : Blo 1419529 2132063 := bstep (se 1 (by rfl) ⟨1599047, by rfl⟩ : syracuseStep 2132063 = 3198095) B3198095
theorem B2132123 : Blo 1419529 2132123 := bstep (se 1 (by rfl) ⟨1599092, by rfl⟩ : syracuseStep 2132123 = 3198185) B3198185
theorem B2132159 : Blo 1419529 2132159 := bstep (se 1 (by rfl) ⟨1599119, by rfl⟩ : syracuseStep 2132159 = 3198239) B3198239
theorem B5392595 : Blo 1419529 5392595 := bstep (se 1 (by rfl) ⟨4044446, by rfl⟩ : syracuseStep 5392595 = 8088893) B8088893
theorem B2132201 : Blo 1419529 2132201 := bstep (se 2 (by rfl) ⟨799575, by rfl⟩ : syracuseStep 2132201 = 1599151) B1599151
theorem B3197177 : Blo 1419529 3197177 := bstep (se 2 (by rfl) ⟨1198941, by rfl⟩ : syracuseStep 3197177 = 2397883) B2397883
theorem B1419567 : Blo 1419529 1419567 := bstep (se 1 (by rfl) ⟨1064675, by rfl⟩ : syracuseStep 1419567 = 2129351) B2129351
theorem B3197231 : Blo 1419529 3197231 := bstep (se 1 (by rfl) ⟨2397923, by rfl⟩ : syracuseStep 3197231 = 4795847) B4795847
theorem B17287667 : Blo 1419529 17287667 := bstep (se 1 (by rfl) ⟨12965750, by rfl⟩ : syracuseStep 17287667 = 25931501) B25931501
theorem B3197447 : Blo 1419529 3197447 := bstep (se 1 (by rfl) ⟨2398085, by rfl⟩ : syracuseStep 3197447 = 4796171) B4796171
theorem B1419803 : Blo 1419529 1419803 := bstep (se 1 (by rfl) ⟨1064852, by rfl⟩ : syracuseStep 1419803 = 2129705) B2129705
theorem B1419807 : Blo 1419529 1419807 := bstep (se 1 (by rfl) ⟨1064855, by rfl⟩ : syracuseStep 1419807 = 2129711) B2129711
theorem B3197627 : Blo 1419529 3197627 := bstep (se 1 (by rfl) ⟨2398220, by rfl⟩ : syracuseStep 3197627 = 4796441) B4796441
theorem B18197297 : Blo 1419529 18197297 := bstep (se 2 (by rfl) ⟨6823986, by rfl⟩ : syracuseStep 18197297 = 13647973) B13647973
theorem B1420123 : Blo 1419529 1420123 := bstep (se 1 (by rfl) ⟨1065092, by rfl⟩ : syracuseStep 1420123 = 2130185) B2130185
theorem B1420191 : Blo 1419529 1420191 := bstep (se 1 (by rfl) ⟨1065143, by rfl⟩ : syracuseStep 1420191 = 2130287) B2130287
theorem B7195553 : Blo 1419529 7195553 := bstep (se 2 (by rfl) ⟨2698332, by rfl⟩ : syracuseStep 7195553 = 5396665) B5396665
theorem B12143591 : Blo 1419529 12143591 := bstep (se 1 (by rfl) ⟨9107693, by rfl⟩ : syracuseStep 12143591 = 18215387) B18215387
theorem B1797167 : Blo 1419529 1797167 := bstep (se 1 (by rfl) ⟨1347875, by rfl⟩ : syracuseStep 1797167 = 2695751) B2695751
theorem B1420335 : Blo 1419529 1420335 := bstep (se 1 (by rfl) ⟨1065251, by rfl⟩ : syracuseStep 1420335 = 2130503) B2130503
theorem B1420359 : Blo 1419529 1420359 := bstep (se 1 (by rfl) ⟨1065269, by rfl⟩ : syracuseStep 1420359 = 2130539) B2130539
theorem B2190407 : Blo 1419529 2190407 := bstep (se 1 (by rfl) ⟨1642805, by rfl⟩ : syracuseStep 2190407 = 3285611) B3285611
theorem B18451645 : Blo 1419529 18451645 := bstep (se 3 (by rfl) ⟨3459683, by rfl⟩ : syracuseStep 18451645 = 6919367) B6919367
theorem B1420511 : Blo 1419529 1420511 := bstep (se 1 (by rfl) ⟨1065383, by rfl⟩ : syracuseStep 1420511 = 2130767) B2130767
theorem B27675917 : Blo 1419529 27675917 := bstep (se 3 (by rfl) ⟨5189234, by rfl⟩ : syracuseStep 27675917 = 10378469) B10378469
theorem B2395561 : Blo 1419529 2395561 := bstep (se 2 (by rfl) ⟨898335, by rfl⟩ : syracuseStep 2395561 = 1796671) B1796671
theorem B17518007 : Blo 1419529 17518007 := bstep (se 1 (by rfl) ⟨13138505, by rfl⟩ : syracuseStep 17518007 = 26277011) B26277011
theorem B1420775 : Blo 1419529 1420775 := bstep (se 1 (by rfl) ⟨1065581, by rfl⟩ : syracuseStep 1420775 = 2131163) B2131163
theorem B8089145 : Blo 1419529 8089145 := bstep (se 2 (by rfl) ⟨3033429, by rfl⟩ : syracuseStep 8089145 = 6066859) B6066859
theorem B10784339 : Blo 1419529 10784339 := bstep (se 1 (by rfl) ⟨8088254, by rfl⟩ : syracuseStep 10784339 = 16176509) B16176509
theorem B1420891 : Blo 1419529 1420891 := bstep (se 1 (by rfl) ⟨1065668, by rfl⟩ : syracuseStep 1420891 = 2131337) B2131337
theorem B36917005 : Blo 1419529 36917005 := bstep (se 3 (by rfl) ⟨6921938, by rfl⟩ : syracuseStep 36917005 = 13843877) B13843877
theorem B1421127 : Blo 1419529 1421127 := bstep (se 1 (by rfl) ⟨1065845, by rfl⟩ : syracuseStep 1421127 = 2131691) B2131691
theorem B2396027 : Blo 1419529 2396027 := bstep (se 1 (by rfl) ⟨1797020, by rfl⟩ : syracuseStep 2396027 = 3594041) B3594041
theorem B4550555 : Blo 1419529 4550555 := bstep (se 1 (by rfl) ⟨3412916, by rfl⟩ : syracuseStep 4550555 = 6825833) B6825833
theorem B1421279 : Blo 1419529 1421279 := bstep (se 1 (by rfl) ⟨1065959, by rfl⟩ : syracuseStep 1421279 = 2131919) B2131919
theorem B4796603 : Blo 1419529 4796603 := bstep (se 1 (by rfl) ⟨3597452, by rfl⟩ : syracuseStep 4796603 = 7194905) B7194905
theorem B10383671 : Blo 1419529 10383671 := bstep (se 1 (by rfl) ⟨7787753, by rfl⟩ : syracuseStep 10383671 = 15575507) B15575507
theorem B4551079 : Blo 1419529 4551079 := bstep (se 1 (by rfl) ⟨3413309, by rfl⟩ : syracuseStep 4551079 = 6826619) B6826619
theorem B4862375 : Blo 1419529 4862375 := bstep (se 1 (by rfl) ⟨3646781, by rfl⟩ : syracuseStep 4862375 = 7293563) B7293563
theorem B7189073 : Blo 1419529 7189073 := bstep (se 2 (by rfl) ⟨2695902, by rfl⟩ : syracuseStep 7189073 = 5391805) B5391805
theorem B4797089 : Blo 1419529 4797089 := bstep (se 2 (by rfl) ⟨1798908, by rfl⟩ : syracuseStep 4797089 = 3597817) B3597817
theorem B2560747 : Blo 1419529 2560747 := bstep (se 1 (by rfl) ⟨1920560, by rfl⟩ : syracuseStep 2560747 = 3841121) B3841121
theorem B5395511 : Blo 1419529 5395511 := bstep (se 1 (by rfl) ⟨4046633, by rfl⟩ : syracuseStep 5395511 = 8093267) B8093267
theorem B2397289 : Blo 1419529 2397289 := bstep (se 2 (by rfl) ⟨898983, by rfl⟩ : syracuseStep 2397289 = 1797967) B1797967
theorem B3413099 : Blo 1419529 3413099 := bstep (se 1 (by rfl) ⟨2559824, by rfl⟩ : syracuseStep 3413099 = 5119649) B5119649
theorem B7681139 : Blo 1419529 7681139 := bstep (se 1 (by rfl) ⟨5760854, by rfl⟩ : syracuseStep 7681139 = 11521709) B11521709
theorem B12956989 : Blo 1419529 12956989 := bstep (se 3 (by rfl) ⟨2429435, by rfl⟩ : syracuseStep 12956989 = 4858871) B4858871
theorem B8091035 : Blo 1419529 8091035 := bstep (se 1 (by rfl) ⟨6068276, by rfl⟩ : syracuseStep 8091035 = 12136553) B12136553
theorem B4322747 : Blo 1419529 4322747 := bstep (se 1 (by rfl) ⟨3242060, by rfl⟩ : syracuseStep 4322747 = 6484121) B6484121
theorem B2274887 : Blo 1419529 2274887 := bstep (se 1 (by rfl) ⟨1706165, by rfl⟩ : syracuseStep 2274887 = 3412331) B3412331
theorem B2397863 : Blo 1419529 2397863 := bstep (se 1 (by rfl) ⟨1798397, by rfl⟩ : syracuseStep 2397863 = 3596795) B3596795
theorem B7780049 : Blo 1419529 7780049 := bstep (se 2 (by rfl) ⟨2917518, by rfl⟩ : syracuseStep 7780049 = 5835037) B5835037
theorem B2160521 : Blo 1419529 2160521 := bstep (se 2 (by rfl) ⟨810195, by rfl⟩ : syracuseStep 2160521 = 1620391) B1620391
theorem B10237853 : Blo 1419529 10237853 := bstep (se 3 (by rfl) ⟨1919597, by rfl⟩ : syracuseStep 10237853 = 3839195) B3839195
theorem B3594203 : Blo 1419529 3594203 := bstep (se 1 (by rfl) ⟨2695652, by rfl⟩ : syracuseStep 3594203 = 5391305) B5391305
theorem B3594233 : Blo 1419529 3594233 := bstep (se 2 (by rfl) ⟨1347837, by rfl⟩ : syracuseStep 3594233 = 2695675) B2695675
theorem B13137913 : Blo 1419529 13137913 := bstep (se 2 (by rfl) ⟨4926717, by rfl⟩ : syracuseStep 13137913 = 9853435) B9853435
theorem B3643489 : Blo 1419529 3643489 := bstep (se 2 (by rfl) ⟨1366308, by rfl⟩ : syracuseStep 3643489 = 2732617) B2732617
theorem B3594395 : Blo 1419529 3594395 := bstep (se 1 (by rfl) ⟨2695796, by rfl⟩ : syracuseStep 3594395 = 5391593) B5391593
theorem B47962397 : Blo 1419529 47962397 := bstep (se 3 (by rfl) ⟨8992949, by rfl⟩ : syracuseStep 47962397 = 17985899) B17985899
theorem B2218279 : Blo 1419529 2218279 := bstep (se 1 (by rfl) ⟨1663709, by rfl⟩ : syracuseStep 2218279 = 3327419) B3327419
theorem B2398511 : Blo 1419529 2398511 := bstep (se 1 (by rfl) ⟨1798883, by rfl⟩ : syracuseStep 2398511 = 3597767) B3597767
theorem B10934651 : Blo 1419529 10934651 := bstep (se 1 (by rfl) ⟨8200988, by rfl⟩ : syracuseStep 10934651 = 16401977) B16401977
theorem B77896187 : Blo 1419529 77896187 := bstep (se 1 (by rfl) ⟨58422140, by rfl⟩ : syracuseStep 77896187 = 116844281) B116844281
theorem B2398747 : Blo 1419529 2398747 := bstep (se 1 (by rfl) ⟨1799060, by rfl⟩ : syracuseStep 2398747 = 3598121) B3598121
theorem B6068857 : Blo 1419529 6068857 := bstep (se 2 (by rfl) ⟨2275821, by rfl⟩ : syracuseStep 6068857 = 4551643) B4551643
theorem B2276027 : Blo 1419529 2276027 := bstep (se 1 (by rfl) ⟨1707020, by rfl⟩ : syracuseStep 2276027 = 3414041) B3414041
theorem B12131153 : Blo 1419529 12131153 := bstep (se 2 (by rfl) ⟨4549182, by rfl⟩ : syracuseStep 12131153 = 9098365) B9098365
theorem B7191503 : Blo 1419529 7191503 := bstep (se 1 (by rfl) ⟨5393627, by rfl⟩ : syracuseStep 7191503 = 10787255) B10787255
theorem B3415223 : Blo 1419529 3415223 := bstep (se 1 (by rfl) ⟨2561417, by rfl⟩ : syracuseStep 3415223 = 5122835) B5122835
theorem B77708483 : Blo 1419529 77708483 := bstep (se 1 (by rfl) ⟨58281362, by rfl⟩ : syracuseStep 77708483 = 116562725) B116562725
theorem B3595529 : Blo 1419529 3595529 := bstep (se 2 (by rfl) ⟨1348323, by rfl⟩ : syracuseStep 3595529 = 2696647) B2696647
theorem B4791581 : Blo 1419529 4791581 := bstep (se 3 (by rfl) ⟨898421, by rfl⟩ : syracuseStep 4791581 = 1796843) B1796843
theorem B3194279 : Blo 1419529 3194279 := bstep (se 1 (by rfl) ⟨2395709, by rfl⟩ : syracuseStep 3194279 = 4791419) B4791419
theorem B3415463 : Blo 1419529 3415463 := bstep (se 1 (by rfl) ⟨2561597, by rfl⟩ : syracuseStep 3415463 = 5123195) B5123195
theorem B2129321 : Blo 1419529 2129321 := bstep (se 2 (by rfl) ⟨798495, by rfl⟩ : syracuseStep 2129321 = 1596991) B1596991
theorem B10239443 : Blo 1419529 10239443 := bstep (se 1 (by rfl) ⟨7679582, by rfl⟩ : syracuseStep 10239443 = 15359165) B15359165
theorem B9100775 : Blo 1419529 9100775 := bstep (se 1 (by rfl) ⟨6825581, by rfl⟩ : syracuseStep 9100775 = 13651163) B13651163
theorem B2022907 : Blo 1419529 2022907 := bstep (se 1 (by rfl) ⟨1517180, by rfl⟩ : syracuseStep 2022907 = 3034361) B3034361
theorem B2129471 : Blo 1419529 2129471 := bstep (se 1 (by rfl) ⟨1597103, by rfl⟩ : syracuseStep 2129471 = 3194207) B3194207
theorem B3194459 : Blo 1419529 3194459 := bstep (se 1 (by rfl) ⟨2395844, by rfl⟩ : syracuseStep 3194459 = 4791689) B4791689
theorem B17284751 : Blo 1419529 17284751 := bstep (se 1 (by rfl) ⟨12963563, by rfl⟩ : syracuseStep 17284751 = 25927127) B25927127
theorem B8085203 : Blo 1419529 8085203 := bstep (se 1 (by rfl) ⟨6063902, by rfl⟩ : syracuseStep 8085203 = 12127805) B12127805
theorem B9723635 : Blo 1419529 9723635 := bstep (se 1 (by rfl) ⟨7292726, by rfl⟩ : syracuseStep 9723635 = 14585453) B14585453
theorem B12140279 : Blo 1419529 12140279 := bstep (se 1 (by rfl) ⟨9105209, by rfl⟩ : syracuseStep 12140279 = 18210419) B18210419
theorem B249077551 : Blo 1419529 249077551 := bstep (se 1 (by rfl) ⟨186808163, by rfl⟩ : syracuseStep 249077551 = 373616327) B373616327
theorem B2129735 : Blo 1419529 2129735 := bstep (se 1 (by rfl) ⟨1597301, by rfl⟩ : syracuseStep 2129735 = 3194603) B3194603
theorem B3194747 : Blo 1419529 3194747 := bstep (se 1 (by rfl) ⟨2396060, by rfl⟩ : syracuseStep 3194747 = 4792121) B4792121
theorem B2129819 : Blo 1419529 2129819 := bstep (se 1 (by rfl) ⟨1597364, by rfl⟩ : syracuseStep 2129819 = 3194729) B3194729
theorem B4792445 : Blo 1419529 4792445 := bstep (se 3 (by rfl) ⟨898583, by rfl⟩ : syracuseStep 4792445 = 1797167) B1797167
theorem B4857985 : Blo 1419529 4857985 := bstep (se 2 (by rfl) ⟨1821744, by rfl⟩ : syracuseStep 4857985 = 3643489) B3643489
theorem B5841085 : Blo 1419529 5841085 := bstep (se 3 (by rfl) ⟨1095203, by rfl⟩ : syracuseStep 5841085 = 2190407) B2190407
theorem B3195071 : Blo 1419529 3195071 := bstep (se 1 (by rfl) ⟨2396303, by rfl⟩ : syracuseStep 3195071 = 4792607) B4792607
theorem B2130155 : Blo 1419529 2130155 := bstep (se 1 (by rfl) ⟨1597616, by rfl⟩ : syracuseStep 2130155 = 3195233) B3195233
theorem B2130215 : Blo 1419529 2130215 := bstep (se 1 (by rfl) ⟨1597661, by rfl⟩ : syracuseStep 2130215 = 3195323) B3195323
theorem B2957705 : Blo 1419529 2957705 := bstep (se 2 (by rfl) ⟨1109139, by rfl⟩ : syracuseStep 2957705 = 2218279) B2218279
theorem B4792715 : Blo 1419529 4792715 := bstep (se 1 (by rfl) ⟨3594536, by rfl⟩ : syracuseStep 4792715 = 7189073) B7189073
theorem B49889735 : Blo 1419529 49889735 := bstep (se 1 (by rfl) ⟨37417301, by rfl⟩ : syracuseStep 49889735 = 74834603) B74834603
theorem B3195503 : Blo 1419529 3195503 := bstep (se 1 (by rfl) ⟨2396627, by rfl⟩ : syracuseStep 3195503 = 4793255) B4793255
theorem B3597007 : Blo 1419529 3597007 := bstep (se 1 (by rfl) ⟨2697755, by rfl⟩ : syracuseStep 3597007 = 5395511) B5395511
theorem B5120759 : Blo 1419529 5120759 := bstep (se 1 (by rfl) ⟨3840569, by rfl⟩ : syracuseStep 5120759 = 7681139) B7681139
theorem B27689789 : Blo 1419529 27689789 := bstep (se 3 (by rfl) ⟨5191835, by rfl⟩ : syracuseStep 27689789 = 10383671) B10383671
theorem B2130887 : Blo 1419529 2130887 := bstep (se 1 (by rfl) ⟨1598165, by rfl⟩ : syracuseStep 2130887 = 3196331) B3196331
theorem B3195899 : Blo 1419529 3195899 := bstep (se 1 (by rfl) ⟨2396924, by rfl⟩ : syracuseStep 3195899 = 4793849) B4793849
theorem B10519577 : Blo 1419529 10519577 := bstep (se 2 (by rfl) ⟨3944841, by rfl⟩ : syracuseStep 10519577 = 7889683) B7889683
theorem B1516591 : Blo 1419529 1516591 := bstep (se 1 (by rfl) ⟨1137443, by rfl⟩ : syracuseStep 1516591 = 2274887) B2274887
theorem B2131055 : Blo 1419529 2131055 := bstep (se 1 (by rfl) ⟨1598291, by rfl⟩ : syracuseStep 2131055 = 3196583) B3196583
theorem B1598575 : Blo 1419529 1598575 := bstep (se 1 (by rfl) ⟨1198931, by rfl⟩ : syracuseStep 1598575 = 2397863) B2397863
theorem B5186699 : Blo 1419529 5186699 := bstep (se 1 (by rfl) ⟨3890024, by rfl⟩ : syracuseStep 5186699 = 7780049) B7780049
theorem B3196079 : Blo 1419529 3196079 := bstep (se 1 (by rfl) ⟨2397059, by rfl⟩ : syracuseStep 3196079 = 4794119) B4794119
theorem B3196115 : Blo 1419529 3196115 := bstep (se 1 (by rfl) ⟨2397086, by rfl⟩ : syracuseStep 3196115 = 4794173) B4794173
theorem B6825235 : Blo 1419529 6825235 := bstep (se 1 (by rfl) ⟨5118926, by rfl⟩ : syracuseStep 6825235 = 10237853) B10237853
theorem B2131247 : Blo 1419529 2131247 := bstep (se 1 (by rfl) ⟨1598435, by rfl⟩ : syracuseStep 2131247 = 3196871) B3196871
theorem B6915395 : Blo 1419529 6915395 := bstep (se 1 (by rfl) ⟨5186546, by rfl⟩ : syracuseStep 6915395 = 10373093) B10373093
theorem B3196385 : Blo 1419529 3196385 := bstep (se 2 (by rfl) ⟨1198644, by rfl⟩ : syracuseStep 3196385 = 2397289) B2397289
theorem B2131451 : Blo 1419529 2131451 := bstep (se 1 (by rfl) ⟨1598588, by rfl⟩ : syracuseStep 2131451 = 3197177) B3197177
theorem B31974931 : Blo 1419529 31974931 := bstep (se 1 (by rfl) ⟨23981198, by rfl⟩ : syracuseStep 31974931 = 47962397) B47962397
theorem B43714073 : Blo 1419529 43714073 := bstep (se 2 (by rfl) ⟨16392777, by rfl⟩ : syracuseStep 43714073 = 32785555) B32785555
theorem B2131487 : Blo 1419529 2131487 := bstep (se 1 (by rfl) ⟨1598615, by rfl⟩ : syracuseStep 2131487 = 3197231) B3197231
theorem B1599007 : Blo 1419529 1599007 := bstep (se 1 (by rfl) ⟨1199255, by rfl⟩ : syracuseStep 1599007 = 2398511) B2398511
theorem B51930791 : Blo 1419529 51930791 := bstep (se 1 (by rfl) ⟨38948093, by rfl⟩ : syracuseStep 51930791 = 77896187) B77896187
theorem B2131631 : Blo 1419529 2131631 := bstep (se 1 (by rfl) ⟨1598723, by rfl⟩ : syracuseStep 2131631 = 3197447) B3197447
theorem B1517351 : Blo 1419529 1517351 := bstep (se 1 (by rfl) ⟨1138013, by rfl⟩ : syracuseStep 1517351 = 2276027) B2276027
theorem B2131751 : Blo 1419529 2131751 := bstep (se 1 (by rfl) ⟨1598813, by rfl⟩ : syracuseStep 2131751 = 3197627) B3197627
theorem B8087435 : Blo 1419529 8087435 := bstep (se 1 (by rfl) ⟨6065576, by rfl⟩ : syracuseStep 8087435 = 12131153) B12131153
theorem B4794335 : Blo 1419529 4794335 := bstep (se 1 (by rfl) ⟨3595751, by rfl⟩ : syracuseStep 4794335 = 7191503) B7191503
theorem B8095727 : Blo 1419529 8095727 := bstep (se 1 (by rfl) ⟨6071795, by rfl⟩ : syracuseStep 8095727 = 12143591) B12143591
theorem B2697209 : Blo 1419529 2697209 := bstep (se 2 (by rfl) ⟨1011453, by rfl⟩ : syracuseStep 2697209 = 2022907) B2022907
theorem B10782881 : Blo 1419529 10782881 := bstep (se 2 (by rfl) ⟨4043580, by rfl⟩ : syracuseStep 10782881 = 8087161) B8087161
theorem B18450611 : Blo 1419529 18450611 := bstep (se 1 (by rfl) ⟨13837958, by rfl⟩ : syracuseStep 18450611 = 27675917) B27675917
theorem B1419547 : Blo 1419529 1419547 := bstep (se 1 (by rfl) ⟨1064660, by rfl⟩ : syracuseStep 1419547 = 2129321) B2129321
theorem B6826295 : Blo 1419529 6826295 := bstep (se 1 (by rfl) ⟨5119721, by rfl⟩ : syracuseStep 6826295 = 10239443) B10239443
theorem B5392763 : Blo 1419529 5392763 := bstep (se 1 (by rfl) ⟨4044572, by rfl⟩ : syracuseStep 5392763 = 8089145) B8089145
theorem B1419647 : Blo 1419529 1419647 := bstep (se 1 (by rfl) ⟨1064735, by rfl⟩ : syracuseStep 1419647 = 2129471) B2129471
theorem B6482423 : Blo 1419529 6482423 := bstep (se 1 (by rfl) ⟨4861817, by rfl⟩ : syracuseStep 6482423 = 9723635) B9723635
theorem B1419823 : Blo 1419529 1419823 := bstep (se 1 (by rfl) ⟨1064867, by rfl⟩ : syracuseStep 1419823 = 2129735) B2129735
theorem B1419879 : Blo 1419529 1419879 := bstep (se 1 (by rfl) ⟨1064909, by rfl⟩ : syracuseStep 1419879 = 2129819) B2129819
theorem B3033703 : Blo 1419529 3033703 := bstep (se 1 (by rfl) ⟨2275277, by rfl⟩ : syracuseStep 3033703 = 4550555) B4550555
theorem B17517217 : Blo 1419529 17517217 := bstep (se 2 (by rfl) ⟨6568956, by rfl⟩ : syracuseStep 17517217 = 13137913) B13137913
theorem B3197735 : Blo 1419529 3197735 := bstep (se 1 (by rfl) ⟨2398301, by rfl⟩ : syracuseStep 3197735 = 4796603) B4796603
theorem B1420255 : Blo 1419529 1420255 := bstep (se 1 (by rfl) ⟨1065191, by rfl⟩ : syracuseStep 1420255 = 2130383) B2130383
theorem B1420283 : Blo 1419529 1420283 := bstep (se 1 (by rfl) ⟨1065212, by rfl⟩ : syracuseStep 1420283 = 2130425) B2130425
theorem B1420351 : Blo 1419529 1420351 := bstep (se 1 (by rfl) ⟨1065263, by rfl⟩ : syracuseStep 1420351 = 2130527) B2130527
theorem B3198059 : Blo 1419529 3198059 := bstep (se 1 (by rfl) ⟨2398544, by rfl⟩ : syracuseStep 3198059 = 4797089) B4797089
theorem B2698409 : Blo 1419529 2698409 := bstep (se 2 (by rfl) ⟨1011903, by rfl⟩ : syracuseStep 2698409 = 2023807) B2023807
theorem B3198329 : Blo 1419529 3198329 := bstep (se 2 (by rfl) ⟨1199373, by rfl⟩ : syracuseStep 3198329 = 2398747) B2398747
theorem B1420671 : Blo 1419529 1420671 := bstep (se 1 (by rfl) ⟨1065503, by rfl⟩ : syracuseStep 1420671 = 2131007) B2131007
theorem B1420699 : Blo 1419529 1420699 := bstep (se 1 (by rfl) ⟨1065524, by rfl⟩ : syracuseStep 1420699 = 2131049) B2131049
theorem B1420767 : Blo 1419529 1420767 := bstep (se 1 (by rfl) ⟨1065575, by rfl⟩ : syracuseStep 1420767 = 2131151) B2131151
theorem B5394023 : Blo 1419529 5394023 := bstep (se 1 (by rfl) ⟨4045517, by rfl⟩ : syracuseStep 5394023 = 8091035) B8091035
theorem B1420903 : Blo 1419529 1420903 := bstep (se 1 (by rfl) ⟨1065677, by rfl⟩ : syracuseStep 1420903 = 2131355) B2131355
theorem B4042487 : Blo 1419529 4042487 := bstep (se 1 (by rfl) ⟨3031865, by rfl⟩ : syracuseStep 4042487 = 6063731) B6063731
theorem B1421051 : Blo 1419529 1421051 := bstep (se 1 (by rfl) ⟨1065788, by rfl⟩ : syracuseStep 1421051 = 2131577) B2131577
theorem B1421119 : Blo 1419529 1421119 := bstep (se 1 (by rfl) ⟨1065839, by rfl⟩ : syracuseStep 1421119 = 2131679) B2131679
theorem B1421183 : Blo 1419529 1421183 := bstep (se 1 (by rfl) ⟨1065887, by rfl⟩ : syracuseStep 1421183 = 2131775) B2131775
theorem B2396135 : Blo 1419529 2396135 := bstep (se 1 (by rfl) ⟨1797101, by rfl⟩ : syracuseStep 2396135 = 3594203) B3594203
theorem B1421295 : Blo 1419529 1421295 := bstep (se 1 (by rfl) ⟨1065971, by rfl⟩ : syracuseStep 1421295 = 2131943) B2131943
theorem B2396155 : Blo 1419529 2396155 := bstep (se 1 (by rfl) ⟨1797116, by rfl⟩ : syracuseStep 2396155 = 3594233) B3594233
theorem B1421307 : Blo 1419529 1421307 := bstep (se 1 (by rfl) ⟨1065980, by rfl⟩ : syracuseStep 1421307 = 2131961) B2131961
theorem B1421375 : Blo 1419529 1421375 := bstep (se 1 (by rfl) ⟨1066031, by rfl⟩ : syracuseStep 1421375 = 2132063) B2132063
theorem B2396263 : Blo 1419529 2396263 := bstep (se 1 (by rfl) ⟨1797197, by rfl⟩ : syracuseStep 2396263 = 3594395) B3594395
theorem B1421415 : Blo 1419529 1421415 := bstep (se 1 (by rfl) ⟨1066061, by rfl⟩ : syracuseStep 1421415 = 2132123) B2132123
theorem B1421439 : Blo 1419529 1421439 := bstep (se 1 (by rfl) ⟨1066079, by rfl⟩ : syracuseStep 1421439 = 2132159) B2132159
theorem B1421467 : Blo 1419529 1421467 := bstep (se 1 (by rfl) ⟨1066100, by rfl⟩ : syracuseStep 1421467 = 2132201) B2132201
theorem B4797035 : Blo 1419529 4797035 := bstep (se 1 (by rfl) ⟨3597776, by rfl⟩ : syracuseStep 4797035 = 7195553) B7195553
theorem B2397019 : Blo 1419529 2397019 := bstep (se 1 (by rfl) ⟨1797764, by rfl⟩ : syracuseStep 2397019 = 3595529) B3595529
theorem B11678671 : Blo 1419529 11678671 := bstep (se 1 (by rfl) ⟨8759003, by rfl⟩ : syracuseStep 11678671 = 17518007) B17518007
theorem B6067183 : Blo 1419529 6067183 := bstep (se 1 (by rfl) ⟨4550387, by rfl⟩ : syracuseStep 6067183 = 9100775) B9100775
theorem B49222673 : Blo 1419529 49222673 := bstep (se 2 (by rfl) ⟨18458502, by rfl⟩ : syracuseStep 49222673 = 36917005) B36917005
theorem B7189559 : Blo 1419529 7189559 := bstep (se 1 (by rfl) ⟨5392169, by rfl⟩ : syracuseStep 7189559 = 10784339) B10784339
theorem B11523167 : Blo 1419529 11523167 := bstep (se 1 (by rfl) ⟨8642375, by rfl⟩ : syracuseStep 11523167 = 17284751) B17284751
theorem B21861971 : Blo 1419529 21861971 := bstep (se 1 (by rfl) ⟨16396478, by rfl⟩ : syracuseStep 21861971 = 32792957) B32792957
theorem B3241583 : Blo 1419529 3241583 := bstep (se 1 (by rfl) ⟨2431187, by rfl⟩ : syracuseStep 3241583 = 4862375) B4862375
theorem B9721579 : Blo 1419529 9721579 := bstep (se 1 (by rfl) ⟨7291184, by rfl⟩ : syracuseStep 9721579 = 14582369) B14582369
theorem B9107261 : Blo 1419529 9107261 := bstep (se 3 (by rfl) ⟨1707611, by rfl⟩ : syracuseStep 9107261 = 3415223) B3415223
theorem B6068105 : Blo 1419529 6068105 := bstep (se 2 (by rfl) ⟨2275539, by rfl⟩ : syracuseStep 6068105 = 4551079) B4551079
theorem B12130195 : Blo 1419529 12130195 := bstep (se 1 (by rfl) ⟨9097646, by rfl⟩ : syracuseStep 12130195 = 18195293) B18195293
theorem B2275399 : Blo 1419529 2275399 := bstep (se 1 (by rfl) ⟨1706549, by rfl⟩ : syracuseStep 2275399 = 3413099) B3413099
theorem B8091809 : Blo 1419529 8091809 := bstep (se 2 (by rfl) ⟨3034428, by rfl⟩ : syracuseStep 8091809 = 6068857) B6068857
theorem B2881831 : Blo 1419529 2881831 := bstep (se 1 (by rfl) ⟨2161373, by rfl⟩ : syracuseStep 2881831 = 4322747) B4322747
theorem B3414329 : Blo 1419529 3414329 := bstep (se 2 (by rfl) ⟨1280373, by rfl⟩ : syracuseStep 3414329 = 2560747) B2560747
theorem B98408773 : Blo 1419529 98408773 := bstep (se 4 (by rfl) ⟨9225822, by rfl⟩ : syracuseStep 98408773 = 18451645) B18451645
theorem B5396969 : Blo 1419529 5396969 := bstep (se 2 (by rfl) ⟨2023863, by rfl⟩ : syracuseStep 5396969 = 4047727) B4047727
theorem B1440347 : Blo 1419529 1440347 := bstep (se 1 (by rfl) ⟨1080260, by rfl⟩ : syracuseStep 1440347 = 2160521) B2160521
theorem B3595063 : Blo 1419529 3595063 := bstep (se 1 (by rfl) ⟨2696297, by rfl⟩ : syracuseStep 3595063 = 5392595) B5392595
theorem B7289767 : Blo 1419529 7289767 := bstep (se 1 (by rfl) ⟨5467325, by rfl⟩ : syracuseStep 7289767 = 10934651) B10934651
theorem B11525111 : Blo 1419529 11525111 := bstep (se 1 (by rfl) ⟨8643833, by rfl⟩ : syracuseStep 11525111 = 17287667) B17287667
theorem B17275985 : Blo 1419529 17275985 := bstep (se 2 (by rfl) ⟨6478494, by rfl⟩ : syracuseStep 17275985 = 12956989) B12956989
theorem B12131531 : Blo 1419529 12131531 := bstep (se 1 (by rfl) ⟨9098648, by rfl⟩ : syracuseStep 12131531 = 18197297) B18197297
theorem B3194081 : Blo 1419529 3194081 := bstep (se 2 (by rfl) ⟨1197780, by rfl⟩ : syracuseStep 3194081 = 2395561) B2395561
theorem B51805655 : Blo 1419529 51805655 := bstep (se 1 (by rfl) ⟨38854241, by rfl⟩ : syracuseStep 51805655 = 77708483) B77708483
theorem B3194387 : Blo 1419529 3194387 := bstep (se 1 (by rfl) ⟨2395790, by rfl⟩ : syracuseStep 3194387 = 4791581) B4791581
theorem B2129519 : Blo 1419529 2129519 := bstep (se 1 (by rfl) ⟨1597139, by rfl⟩ : syracuseStep 2129519 = 3194279) B3194279
theorem B2276975 : Blo 1419529 2276975 := bstep (se 1 (by rfl) ⟨1707731, by rfl⟩ : syracuseStep 2276975 = 3415463) B3415463
theorem B2129639 : Blo 1419529 2129639 := bstep (se 1 (by rfl) ⟨1597229, by rfl⟩ : syracuseStep 2129639 = 3194459) B3194459
theorem B332103401 : Blo 1419529 332103401 := bstep (se 2 (by rfl) ⟨124538775, by rfl⟩ : syracuseStep 332103401 = 249077551) B249077551
theorem B5390135 : Blo 1419529 5390135 := bstep (se 1 (by rfl) ⟨4042601, by rfl⟩ : syracuseStep 5390135 = 8085203) B8085203
theorem B8093519 : Blo 1419529 8093519 := bstep (se 1 (by rfl) ⟨6070139, by rfl⟩ : syracuseStep 8093519 = 12140279) B12140279
theorem B1597351 : Blo 1419529 1597351 := bstep (se 1 (by rfl) ⟨1198013, by rfl⟩ : syracuseStep 1597351 = 2396027) B2396027
theorem B2129831 : Blo 1419529 2129831 := bstep (se 1 (by rfl) ⟨1597373, by rfl⟩ : syracuseStep 2129831 = 3194747) B3194747
theorem B3194963 : Blo 1419529 3194963 := bstep (se 1 (by rfl) ⟨2396222, by rfl⟩ : syracuseStep 3194963 = 4792445) B4792445
theorem B170532965 : Blo 1419529 170532965 := bstep (se 4 (by rfl) ⟨15987465, by rfl⟩ : syracuseStep 170532965 = 31974931) B31974931
theorem B2130047 : Blo 1419529 2130047 := bstep (se 1 (by rfl) ⟨1597535, by rfl⟩ : syracuseStep 2130047 = 3195071) B3195071
theorem B3195017 : Blo 1419529 3195017 := bstep (se 2 (by rfl) ⟨1198131, by rfl⟩ : syracuseStep 3195017 = 2396263) B2396263
theorem B3195143 : Blo 1419529 3195143 := bstep (se 1 (by rfl) ⟨2396357, by rfl⟩ : syracuseStep 3195143 = 4792715) B4792715
theorem B33259823 : Blo 1419529 33259823 := bstep (se 1 (by rfl) ⟨24944867, by rfl⟩ : syracuseStep 33259823 = 49889735) B49889735
theorem B3842441 : Blo 1419529 3842441 := bstep (se 2 (by rfl) ⟨1440915, by rfl⟩ : syracuseStep 3842441 = 2881831) B2881831
theorem B2130335 : Blo 1419529 2130335 := bstep (se 1 (by rfl) ⟨1597751, by rfl⟩ : syracuseStep 2130335 = 3195503) B3195503
theorem B131211697 : Blo 1419529 131211697 := bstep (se 2 (by rfl) ⟨49204386, by rfl⟩ : syracuseStep 131211697 = 98408773) B98408773
theorem B2130599 : Blo 1419529 2130599 := bstep (se 1 (by rfl) ⟨1597949, by rfl⟩ : syracuseStep 2130599 = 3195899) B3195899
theorem B7013051 : Blo 1419529 7013051 := bstep (se 1 (by rfl) ⟨5259788, by rfl⟩ : syracuseStep 7013051 = 10519577) B10519577
theorem B4793039 : Blo 1419529 4793039 := bstep (se 1 (by rfl) ⟨3594779, by rfl⟩ : syracuseStep 4793039 = 7189559) B7189559
theorem B3457799 : Blo 1419529 3457799 := bstep (se 1 (by rfl) ⟨2593349, by rfl⟩ : syracuseStep 3457799 = 5186699) B5186699
theorem B2130719 : Blo 1419529 2130719 := bstep (se 1 (by rfl) ⟨1598039, by rfl⟩ : syracuseStep 2130719 = 3196079) B3196079
theorem B2130743 : Blo 1419529 2130743 := bstep (se 1 (by rfl) ⟨1598057, by rfl⟩ : syracuseStep 2130743 = 3196115) B3196115
theorem B23356289 : Blo 1419529 23356289 := bstep (se 2 (by rfl) ⟨8758608, by rfl⟩ : syracuseStep 23356289 = 17517217) B17517217
theorem B2130923 : Blo 1419529 2130923 := bstep (se 1 (by rfl) ⟨1598192, by rfl⟩ : syracuseStep 2130923 = 3196385) B3196385
theorem B14574647 : Blo 1419529 14574647 := bstep (se 1 (by rfl) ⟨10930985, by rfl⟩ : syracuseStep 14574647 = 21861971) B21861971
theorem B4793417 : Blo 1419529 4793417 := bstep (se 2 (by rfl) ⟨1797531, by rfl⟩ : syracuseStep 4793417 = 3595063) B3595063
theorem B34620527 : Blo 1419529 34620527 := bstep (se 1 (by rfl) ⟨25965395, by rfl⟩ : syracuseStep 34620527 = 51930791) B51930791
theorem B3196025 : Blo 1419529 3196025 := bstep (se 2 (by rfl) ⟨1198509, by rfl⟩ : syracuseStep 3196025 = 2397019) B2397019
theorem B6071507 : Blo 1419529 6071507 := bstep (se 1 (by rfl) ⟨4553630, by rfl⟩ : syracuseStep 6071507 = 9107261) B9107261
theorem B5391623 : Blo 1419529 5391623 := bstep (se 1 (by rfl) ⟨4043717, by rfl⟩ : syracuseStep 5391623 = 8087435) B8087435
theorem B3196223 : Blo 1419529 3196223 := bstep (se 1 (by rfl) ⟨2397167, by rfl⟩ : syracuseStep 3196223 = 4794335) B4794335
theorem B2131433 : Blo 1419529 2131433 := bstep (se 2 (by rfl) ⟨799287, by rfl⟩ : syracuseStep 2131433 = 1598575) B1598575
theorem B3597979 : Blo 1419529 3597979 := bstep (se 1 (by rfl) ⟨2698484, by rfl⟩ : syracuseStep 3597979 = 5396969) B5396969
theorem B2131823 : Blo 1419529 2131823 := bstep (se 1 (by rfl) ⟨1598867, by rfl⟩ : syracuseStep 2131823 = 3197735) B3197735
theorem B2132009 : Blo 1419529 2132009 := bstep (se 2 (by rfl) ⟨799503, by rfl⟩ : syracuseStep 2132009 = 1599007) B1599007
theorem B2132039 : Blo 1419529 2132039 := bstep (se 1 (by rfl) ⟨1599029, by rfl⟩ : syracuseStep 2132039 = 3198059) B3198059
theorem B8087687 : Blo 1419529 8087687 := bstep (se 1 (by rfl) ⟨6065765, by rfl⟩ : syracuseStep 8087687 = 12131531) B12131531
theorem B2132219 : Blo 1419529 2132219 := bstep (se 1 (by rfl) ⟨1599164, by rfl⟩ : syracuseStep 2132219 = 3198329) B3198329
theorem B12962105 : Blo 1419529 12962105 := bstep (se 2 (by rfl) ⟨4860789, by rfl⟩ : syracuseStep 12962105 = 9721579) B9721579
theorem B1419679 : Blo 1419529 1419679 := bstep (se 1 (by rfl) ⟨1064759, by rfl⟩ : syracuseStep 1419679 = 2129519) B2129519
theorem B1517983 : Blo 1419529 1517983 := bstep (se 1 (by rfl) ⟨1138487, by rfl⟩ : syracuseStep 1517983 = 2276975) B2276975
theorem B1419759 : Blo 1419529 1419759 := bstep (se 1 (by rfl) ⟨1064819, by rfl⟩ : syracuseStep 1419759 = 2129639) B2129639
theorem B16173593 : Blo 1419529 16173593 := bstep (se 2 (by rfl) ⟨6065097, by rfl⟩ : syracuseStep 16173593 = 12130195) B12130195
theorem B1419887 : Blo 1419529 1419887 := bstep (se 1 (by rfl) ⟨1064915, by rfl⟩ : syracuseStep 1419887 = 2129831) B2129831
theorem B3033865 : Blo 1419529 3033865 := bstep (se 2 (by rfl) ⟨1137699, by rfl⟩ : syracuseStep 3033865 = 2275399) B2275399
theorem B1420103 : Blo 1419529 1420103 := bstep (se 1 (by rfl) ⟨1065077, by rfl⟩ : syracuseStep 1420103 = 2130155) B2130155
theorem B1420143 : Blo 1419529 1420143 := bstep (se 1 (by rfl) ⟨1065107, by rfl⟩ : syracuseStep 1420143 = 2130215) B2130215
theorem B3198023 : Blo 1419529 3198023 := bstep (se 1 (by rfl) ⟨2398517, by rfl⟩ : syracuseStep 3198023 = 4797035) B4797035
theorem B18459859 : Blo 1419529 18459859 := bstep (se 1 (by rfl) ⟨13844894, by rfl⟩ : syracuseStep 18459859 = 27689789) B27689789
theorem B1420591 : Blo 1419529 1420591 := bstep (se 1 (by rfl) ⟨1065443, by rfl⟩ : syracuseStep 1420591 = 2130887) B2130887
theorem B1420703 : Blo 1419529 1420703 := bstep (se 1 (by rfl) ⟨1065527, by rfl⟩ : syracuseStep 1420703 = 2131055) B2131055
theorem B1420831 : Blo 1419529 1420831 := bstep (se 1 (by rfl) ⟨1065623, by rfl⟩ : syracuseStep 1420831 = 2131247) B2131247
theorem B4796009 : Blo 1419529 4796009 := bstep (se 2 (by rfl) ⟨1798503, by rfl⟩ : syracuseStep 4796009 = 3597007) B3597007
theorem B1420967 : Blo 1419529 1420967 := bstep (se 1 (by rfl) ⟨1065725, by rfl⟩ : syracuseStep 1420967 = 2131451) B2131451
theorem B29142715 : Blo 1419529 29142715 := bstep (se 1 (by rfl) ⟨21857036, by rfl⟩ : syracuseStep 29142715 = 43714073) B43714073
theorem B1420991 : Blo 1419529 1420991 := bstep (se 1 (by rfl) ⟨1065743, by rfl⟩ : syracuseStep 1420991 = 2131487) B2131487
theorem B1421087 : Blo 1419529 1421087 := bstep (se 1 (by rfl) ⟨1065815, by rfl⟩ : syracuseStep 1421087 = 2131631) B2131631
theorem B1421167 : Blo 1419529 1421167 := bstep (se 1 (by rfl) ⟨1065875, by rfl⟩ : syracuseStep 1421167 = 2131751) B2131751
theorem B9719689 : Blo 1419529 9719689 := bstep (se 2 (by rfl) ⟨3644883, by rfl⟩ : syracuseStep 9719689 = 7289767) B7289767
theorem B8089577 : Blo 1419529 8089577 := bstep (se 2 (by rfl) ⟨3033591, by rfl⟩ : syracuseStep 8089577 = 6067183) B6067183
theorem B1798139 : Blo 1419529 1798139 := bstep (se 1 (by rfl) ⟨1348604, by rfl⟩ : syracuseStep 1798139 = 2697209) B2697209
theorem B7188587 : Blo 1419529 7188587 := bstep (se 1 (by rfl) ⟨5391440, by rfl⟩ : syracuseStep 7188587 = 10782881) B10782881
theorem B5394539 : Blo 1419529 5394539 := bstep (se 1 (by rfl) ⟨4045904, by rfl⟩ : syracuseStep 5394539 = 8091809) B8091809
theorem B12300407 : Blo 1419529 12300407 := bstep (se 1 (by rfl) ⟨9225305, by rfl⟩ : syracuseStep 12300407 = 18450611) B18450611
theorem B4550863 : Blo 1419529 4550863 := bstep (se 1 (by rfl) ⟨3413147, by rfl⟩ : syracuseStep 4550863 = 6826295) B6826295
theorem B4321615 : Blo 1419529 4321615 := bstep (se 1 (by rfl) ⟨3241211, by rfl⟩ : syracuseStep 4321615 = 6482423) B6482423
theorem B1798939 : Blo 1419529 1798939 := bstep (se 1 (by rfl) ⟨1349204, by rfl⟩ : syracuseStep 1798939 = 2698409) B2698409
theorem B221402267 : Blo 1419529 221402267 := bstep (se 1 (by rfl) ⟨166051700, by rfl⟩ : syracuseStep 221402267 = 332103401) B332103401
theorem B3593423 : Blo 1419529 3593423 := bstep (se 1 (by rfl) ⟨2695067, by rfl⟩ : syracuseStep 3593423 = 5390135) B5390135
theorem B5395679 : Blo 1419529 5395679 := bstep (se 1 (by rfl) ⟨4046759, by rfl⟩ : syracuseStep 5395679 = 8093519) B8093519
theorem B7788113 : Blo 1419529 7788113 := bstep (se 2 (by rfl) ⟨2920542, by rfl⟩ : syracuseStep 7788113 = 5841085) B5841085
theorem B1971803 : Blo 1419529 1971803 := bstep (se 1 (by rfl) ⟨1478852, by rfl⟩ : syracuseStep 1971803 = 2957705) B2957705
theorem B3413839 : Blo 1419529 3413839 := bstep (se 1 (by rfl) ⟨2560379, by rfl⟩ : syracuseStep 3413839 = 5120759) B5120759
theorem B25909253 : Blo 1419529 25909253 := bstep (se 4 (by rfl) ⟨2428992, by rfl⟩ : syracuseStep 25909253 = 4857985) B4857985
theorem B32815115 : Blo 1419529 32815115 := bstep (se 1 (by rfl) ⟨24611336, by rfl⟩ : syracuseStep 32815115 = 49222673) B49222673
theorem B7682111 : Blo 1419529 7682111 := bstep (se 1 (by rfl) ⟨5761583, by rfl⟩ : syracuseStep 7682111 = 11523167) B11523167
theorem B4044937 : Blo 1419529 4044937 := bstep (se 2 (by rfl) ⟨1516851, by rfl⟩ : syracuseStep 4044937 = 3033703) B3033703
theorem B4610263 : Blo 1419529 4610263 := bstep (se 1 (by rfl) ⟨3457697, by rfl⟩ : syracuseStep 4610263 = 6915395) B6915395
theorem B2161055 : Blo 1419529 2161055 := bstep (se 1 (by rfl) ⟨1620791, by rfl⟩ : syracuseStep 2161055 = 3241583) B3241583
theorem B4045403 : Blo 1419529 4045403 := bstep (se 1 (by rfl) ⟨3034052, by rfl⟩ : syracuseStep 4045403 = 6068105) B6068105
theorem B15571561 : Blo 1419529 15571561 := bstep (se 2 (by rfl) ⟨5839335, by rfl⟩ : syracuseStep 15571561 = 11678671) B11678671
theorem B5397151 : Blo 1419529 5397151 := bstep (se 1 (by rfl) ⟨4047863, by rfl⟩ : syracuseStep 5397151 = 8095727) B8095727
theorem B2022121 : Blo 1419529 2022121 := bstep (se 2 (by rfl) ⟨758295, by rfl⟩ : syracuseStep 2022121 = 1516591) B1516591
theorem B2276219 : Blo 1419529 2276219 := bstep (se 1 (by rfl) ⟨1707164, by rfl⟩ : syracuseStep 2276219 = 3414329) B3414329
theorem B3840925 : Blo 1419529 3840925 := bstep (se 3 (by rfl) ⟨720173, by rfl⟩ : syracuseStep 3840925 = 1440347) B1440347
theorem B3595175 : Blo 1419529 3595175 := bstep (se 1 (by rfl) ⟨2696381, by rfl⟩ : syracuseStep 3595175 = 5392763) B5392763
theorem B9100313 : Blo 1419529 9100313 := bstep (se 2 (by rfl) ⟨3412617, by rfl⟩ : syracuseStep 9100313 = 6825235) B6825235
theorem B10779965 : Blo 1419529 10779965 := bstep (se 3 (by rfl) ⟨2021243, by rfl⟩ : syracuseStep 10779965 = 4042487) B4042487
theorem B7683407 : Blo 1419529 7683407 := bstep (se 1 (by rfl) ⟨5762555, by rfl⟩ : syracuseStep 7683407 = 11525111) B11525111
theorem B11517323 : Blo 1419529 11517323 := bstep (se 1 (by rfl) ⟨8637992, by rfl⟩ : syracuseStep 11517323 = 17275985) B17275985
theorem B4046269 : Blo 1419529 4046269 := bstep (se 3 (by rfl) ⟨758675, by rfl⟩ : syracuseStep 4046269 = 1517351) B1517351
theorem B2129387 : Blo 1419529 2129387 := bstep (se 1 (by rfl) ⟨1597040, by rfl⟩ : syracuseStep 2129387 = 3194081) B3194081
theorem B34537103 : Blo 1419529 34537103 := bstep (se 1 (by rfl) ⟨25902827, by rfl⟩ : syracuseStep 34537103 = 51805655) B51805655
theorem B2129591 : Blo 1419529 2129591 := bstep (se 1 (by rfl) ⟨1597193, by rfl⟩ : syracuseStep 2129591 = 3194387) B3194387
theorem B3596015 : Blo 1419529 3596015 := bstep (se 1 (by rfl) ⟨2697011, by rfl⟩ : syracuseStep 3596015 = 5394023) B5394023
theorem B2129801 : Blo 1419529 2129801 := bstep (se 2 (by rfl) ⟨798675, by rfl⟩ : syracuseStep 2129801 = 1597351) B1597351
theorem B1597423 : Blo 1419529 1597423 := bstep (se 1 (by rfl) ⟨1198067, by rfl⟩ : syracuseStep 1597423 = 2396135) B2396135
theorem B3194873 : Blo 1419529 3194873 := bstep (se 2 (by rfl) ⟨1198077, by rfl⟩ : syracuseStep 3194873 = 2396155) B2396155
theorem B2129975 : Blo 1419529 2129975 := bstep (se 1 (by rfl) ⟨1597481, by rfl⟩ : syracuseStep 2129975 = 3194963) B3194963
theorem B113688643 : Blo 1419529 113688643 := bstep (se 1 (by rfl) ⟨85266482, by rfl⟩ : syracuseStep 113688643 = 170532965) B170532965
theorem B4792391 : Blo 1419529 4792391 := bstep (se 1 (by rfl) ⟨3594293, by rfl⟩ : syracuseStep 4792391 = 7188587) B7188587
theorem B3596359 : Blo 1419529 3596359 := bstep (se 1 (by rfl) ⟨2697269, by rfl⟩ : syracuseStep 3596359 = 5394539) B5394539
theorem B8200271 : Blo 1419529 8200271 := bstep (se 1 (by rfl) ⟨6150203, by rfl⟩ : syracuseStep 8200271 = 12300407) B12300407
theorem B2130011 : Blo 1419529 2130011 := bstep (se 1 (by rfl) ⟨1597508, by rfl⟩ : syracuseStep 2130011 = 3195017) B3195017
theorem B2130095 : Blo 1419529 2130095 := bstep (se 1 (by rfl) ⟨1597571, by rfl⟩ : syracuseStep 2130095 = 3195143) B3195143
theorem B3195359 : Blo 1419529 3195359 := bstep (se 1 (by rfl) ⟨2396519, by rfl⟩ : syracuseStep 3195359 = 4793039) B4793039
theorem B174948929 : Blo 1419529 174948929 := bstep (se 2 (by rfl) ⟨65605848, by rfl⟩ : syracuseStep 174948929 = 131211697) B131211697
theorem B9716431 : Blo 1419529 9716431 := bstep (se 1 (by rfl) ⟨7287323, by rfl⟩ : syracuseStep 9716431 = 14574647) B14574647
theorem B3195611 : Blo 1419529 3195611 := bstep (se 1 (by rfl) ⟨2396708, by rfl⟩ : syracuseStep 3195611 = 4793417) B4793417
theorem B2130683 : Blo 1419529 2130683 := bstep (se 1 (by rfl) ⟨1598012, by rfl⟩ : syracuseStep 2130683 = 3196025) B3196025
theorem B4047671 : Blo 1419529 4047671 := bstep (se 1 (by rfl) ⟨3035753, by rfl⟩ : syracuseStep 4047671 = 6071507) B6071507
theorem B3597119 : Blo 1419529 3597119 := bstep (se 1 (by rfl) ⟨2697839, by rfl⟩ : syracuseStep 3597119 = 5395679) B5395679
theorem B2130815 : Blo 1419529 2130815 := bstep (se 1 (by rfl) ⟨1598111, by rfl⟩ : syracuseStep 2130815 = 3196223) B3196223
theorem B2696161 : Blo 1419529 2696161 := bstep (se 2 (by rfl) ⟨1011060, by rfl⟩ : syracuseStep 2696161 = 2022121) B2022121
theorem B30712861 : Blo 1419529 30712861 := bstep (se 3 (by rfl) ⟨5758661, by rfl⟩ : syracuseStep 30712861 = 11517323) B11517323
theorem B5121233 : Blo 1419529 5121233 := bstep (se 2 (by rfl) ⟨1920462, by rfl⟩ : syracuseStep 5121233 = 3840925) B3840925
theorem B5121407 : Blo 1419529 5121407 := bstep (se 1 (by rfl) ⟨3841055, by rfl⟩ : syracuseStep 5121407 = 7682111) B7682111
theorem B5391791 : Blo 1419529 5391791 := bstep (se 1 (by rfl) ⟨4043843, by rfl⟩ : syracuseStep 5391791 = 8087687) B8087687
theorem B10782395 : Blo 1419529 10782395 := bstep (se 1 (by rfl) ⟨8086796, by rfl⟩ : syracuseStep 10782395 = 16173593) B16173593
theorem B2132015 : Blo 1419529 2132015 := bstep (se 1 (by rfl) ⟨1599011, by rfl⟩ : syracuseStep 2132015 = 3198023) B3198023
theorem B8095909 : Blo 1419529 8095909 := bstep (se 4 (by rfl) ⟨758991, by rfl⟩ : syracuseStep 8095909 = 1517983) B1517983
theorem B7186643 : Blo 1419529 7186643 := bstep (se 1 (by rfl) ⟨5389982, by rfl⟩ : syracuseStep 7186643 = 10779965) B10779965
theorem B5122271 : Blo 1419529 5122271 := bstep (se 1 (by rfl) ⟨3841703, by rfl⟩ : syracuseStep 5122271 = 7683407) B7683407
theorem B38856953 : Blo 1419529 38856953 := bstep (se 2 (by rfl) ⟨14571357, by rfl⟩ : syracuseStep 38856953 = 29142715) B29142715
theorem B1419591 : Blo 1419529 1419591 := bstep (se 1 (by rfl) ⟨1064693, by rfl⟩ : syracuseStep 1419591 = 2129387) B2129387
theorem B3197339 : Blo 1419529 3197339 := bstep (se 1 (by rfl) ⟨2398004, by rfl⟩ : syracuseStep 3197339 = 4796009) B4796009
theorem B1419727 : Blo 1419529 1419727 := bstep (se 1 (by rfl) ⟨1064795, by rfl⟩ : syracuseStep 1419727 = 2129591) B2129591
theorem B1419867 : Blo 1419529 1419867 := bstep (se 1 (by rfl) ⟨1064900, by rfl⟩ : syracuseStep 1419867 = 2129801) B2129801
theorem B5393051 : Blo 1419529 5393051 := bstep (se 1 (by rfl) ⟨4044788, by rfl⟩ : syracuseStep 5393051 = 8089577) B8089577
theorem B4795037 : Blo 1419529 4795037 := bstep (se 3 (by rfl) ⟨899069, by rfl⟩ : syracuseStep 4795037 = 1798139) B1798139
theorem B1420031 : Blo 1419529 1420031 := bstep (se 1 (by rfl) ⟨1065023, by rfl⟩ : syracuseStep 1420031 = 2130047) B2130047
theorem B5393249 : Blo 1419529 5393249 := bstep (se 2 (by rfl) ⟨2022468, by rfl⟩ : syracuseStep 5393249 = 4044937) B4044937
theorem B1420223 : Blo 1419529 1420223 := bstep (se 1 (by rfl) ⟨1065167, by rfl⟩ : syracuseStep 1420223 = 2130335) B2130335
theorem B6147017 : Blo 1419529 6147017 := bstep (se 2 (by rfl) ⟨2305131, by rfl⟩ : syracuseStep 6147017 = 4610263) B4610263
theorem B5762153 : Blo 1419529 5762153 := bstep (se 2 (by rfl) ⟨2160807, by rfl⟩ : syracuseStep 5762153 = 4321615) B4321615
theorem B1420399 : Blo 1419529 1420399 := bstep (se 1 (by rfl) ⟨1065299, by rfl⟩ : syracuseStep 1420399 = 2130599) B2130599
theorem B2305199 : Blo 1419529 2305199 := bstep (se 1 (by rfl) ⟨1728899, by rfl⟩ : syracuseStep 2305199 = 3457799) B3457799
theorem B1420479 : Blo 1419529 1420479 := bstep (se 1 (by rfl) ⟨1065359, by rfl⟩ : syracuseStep 1420479 = 2130719) B2130719
theorem B1420495 : Blo 1419529 1420495 := bstep (se 1 (by rfl) ⟨1065371, by rfl⟩ : syracuseStep 1420495 = 2130743) B2130743
theorem B1420615 : Blo 1419529 1420615 := bstep (se 1 (by rfl) ⟨1065461, by rfl⟩ : syracuseStep 1420615 = 2130923) B2130923
theorem B23080351 : Blo 1419529 23080351 := bstep (se 1 (by rfl) ⟨17310263, by rfl⟩ : syracuseStep 23080351 = 34620527) B34620527
theorem B2395615 : Blo 1419529 2395615 := bstep (se 1 (by rfl) ⟨1796711, by rfl⟩ : syracuseStep 2395615 = 3593423) B3593423
theorem B20762081 : Blo 1419529 20762081 := bstep (se 2 (by rfl) ⟨7785780, by rfl⟩ : syracuseStep 20762081 = 15571561) B15571561
theorem B7196201 : Blo 1419529 7196201 := bstep (se 2 (by rfl) ⟨2698575, by rfl⟩ : syracuseStep 7196201 = 5397151) B5397151
theorem B1420955 : Blo 1419529 1420955 := bstep (se 1 (by rfl) ⟨1065716, by rfl⟩ : syracuseStep 1420955 = 2131433) B2131433
theorem B1421215 : Blo 1419529 1421215 := bstep (se 1 (by rfl) ⟨1065911, by rfl⟩ : syracuseStep 1421215 = 2131823) B2131823
theorem B92205013 : Blo 1419529 92205013 := bstep (se 7 (by rfl) ⟨1080527, by rfl⟩ : syracuseStep 92205013 = 2161055) B2161055
theorem B17272835 : Blo 1419529 17272835 := bstep (se 1 (by rfl) ⟨12954626, by rfl⟩ : syracuseStep 17272835 = 25909253) B25909253
theorem B21876743 : Blo 1419529 21876743 := bstep (se 1 (by rfl) ⟨16407557, by rfl⟩ : syracuseStep 21876743 = 32815115) B32815115
theorem B1421339 : Blo 1419529 1421339 := bstep (se 1 (by rfl) ⟨1066004, by rfl⟩ : syracuseStep 1421339 = 2132009) B2132009
theorem B1421359 : Blo 1419529 1421359 := bstep (se 1 (by rfl) ⟨1066019, by rfl⟩ : syracuseStep 1421359 = 2132039) B2132039
theorem B1421479 : Blo 1419529 1421479 := bstep (se 1 (by rfl) ⟨1066109, by rfl⟩ : syracuseStep 1421479 = 2132219) B2132219
theorem B24613145 : Blo 1419529 24613145 := bstep (se 2 (by rfl) ⟨9229929, by rfl⟩ : syracuseStep 24613145 = 18459859) B18459859
theorem B5395025 : Blo 1419529 5395025 := bstep (se 2 (by rfl) ⟨2023134, by rfl⟩ : syracuseStep 5395025 = 4046269) B4046269
theorem B2396783 : Blo 1419529 2396783 := bstep (se 1 (by rfl) ⟨1797587, by rfl⟩ : syracuseStep 2396783 = 3595175) B3595175
theorem B6066875 : Blo 1419529 6066875 := bstep (se 1 (by rfl) ⟨4550156, by rfl⟩ : syracuseStep 6066875 = 9100313) B9100313
theorem B4797305 : Blo 1419529 4797305 := bstep (se 2 (by rfl) ⟨1798989, by rfl⟩ : syracuseStep 4797305 = 3597979) B3597979
theorem B23024735 : Blo 1419529 23024735 := bstep (se 1 (by rfl) ⟨17268551, by rfl⟩ : syracuseStep 23024735 = 34537103) B34537103
theorem B4551785 : Blo 1419529 4551785 := bstep (se 2 (by rfl) ⟨1706919, by rfl⟩ : syracuseStep 4551785 = 3413839) B3413839
theorem B2397343 : Blo 1419529 2397343 := bstep (se 1 (by rfl) ⟨1798007, by rfl⟩ : syracuseStep 2397343 = 3596015) B3596015
theorem B22173215 : Blo 1419529 22173215 := bstep (se 1 (by rfl) ⟨16629911, by rfl⟩ : syracuseStep 22173215 = 33259823) B33259823
theorem B2561627 : Blo 1419529 2561627 := bstep (se 1 (by rfl) ⟨1921220, by rfl⟩ : syracuseStep 2561627 = 3842441) B3842441
theorem B6067817 : Blo 1419529 6067817 := bstep (se 2 (by rfl) ⟨2275431, by rfl⟩ : syracuseStep 6067817 = 4550863) B4550863
theorem B4675367 : Blo 1419529 4675367 := bstep (se 1 (by rfl) ⟨3506525, by rfl⟩ : syracuseStep 4675367 = 7013051) B7013051
theorem B147601511 : Blo 1419529 147601511 := bstep (se 1 (by rfl) ⟨110701133, by rfl⟩ : syracuseStep 147601511 = 221402267) B221402267
theorem B3594415 : Blo 1419529 3594415 := bstep (se 1 (by rfl) ⟨2695811, by rfl⟩ : syracuseStep 3594415 = 5391623) B5391623
theorem B4045153 : Blo 1419529 4045153 := bstep (se 2 (by rfl) ⟨1516932, by rfl⟩ : syracuseStep 4045153 = 3033865) B3033865
theorem B2398585 : Blo 1419529 2398585 := bstep (se 2 (by rfl) ⟨899469, by rfl⟩ : syracuseStep 2398585 = 1798939) B1798939
theorem B5192075 : Blo 1419529 5192075 := bstep (se 1 (by rfl) ⟨3894056, by rfl⟩ : syracuseStep 5192075 = 7788113) B7788113
theorem B8641403 : Blo 1419529 8641403 := bstep (se 1 (by rfl) ⟨6481052, by rfl⟩ : syracuseStep 8641403 = 12962105) B12962105
theorem B5258141 : Blo 1419529 5258141 := bstep (se 3 (by rfl) ⟨985901, by rfl⟩ : syracuseStep 5258141 = 1971803) B1971803
theorem B10787741 : Blo 1419529 10787741 := bstep (se 3 (by rfl) ⟨2022701, by rfl⟩ : syracuseStep 10787741 = 4045403) B4045403
theorem B6069917 : Blo 1419529 6069917 := bstep (se 3 (by rfl) ⟨1138109, by rfl⟩ : syracuseStep 6069917 = 2276219) B2276219
theorem B62283437 : Blo 1419529 62283437 := bstep (se 3 (by rfl) ⟨11678144, by rfl⟩ : syracuseStep 62283437 = 23356289) B23356289
theorem B12959585 : Blo 1419529 12959585 := bstep (se 2 (by rfl) ⟨4859844, by rfl⟩ : syracuseStep 12959585 = 9719689) B9719689
theorem B2129897 : Blo 1419529 2129897 := bstep (se 2 (by rfl) ⟨798711, by rfl⟩ : syracuseStep 2129897 = 1597423) B1597423
theorem B2129915 : Blo 1419529 2129915 := bstep (se 1 (by rfl) ⟨1597436, by rfl⟩ : syracuseStep 2129915 = 3194873) B3194873
theorem B3194927 : Blo 1419529 3194927 := bstep (se 1 (by rfl) ⟨2396195, by rfl⟩ : syracuseStep 3194927 = 4792391) B4792391
theorem B151584857 : Blo 1419529 151584857 := bstep (se 2 (by rfl) ⟨56844321, by rfl⟩ : syracuseStep 151584857 = 113688643) B113688643
theorem B16408763 : Blo 1419529 16408763 := bstep (se 1 (by rfl) ⟨12306572, by rfl⟩ : syracuseStep 16408763 = 24613145) B24613145
theorem B4792553 : Blo 1419529 4792553 := bstep (se 2 (by rfl) ⟨1797207, by rfl⟩ : syracuseStep 4792553 = 3594415) B3594415
theorem B2130239 : Blo 1419529 2130239 := bstep (se 1 (by rfl) ⟨1597679, by rfl⟩ : syracuseStep 2130239 = 3195359) B3195359
theorem B3596683 : Blo 1419529 3596683 := bstep (se 1 (by rfl) ⟨2697512, by rfl⟩ : syracuseStep 3596683 = 5395025) B5395025
theorem B1597855 : Blo 1419529 1597855 := bstep (se 1 (by rfl) ⟨1198391, by rfl⟩ : syracuseStep 1597855 = 2396783) B2396783
theorem B2130407 : Blo 1419529 2130407 := bstep (se 1 (by rfl) ⟨1597805, by rfl⟩ : syracuseStep 2130407 = 3195611) B3195611
theorem B13657085 : Blo 1419529 13657085 := bstep (se 3 (by rfl) ⟨2560703, by rfl⟩ : syracuseStep 13657085 = 5121407) B5121407
theorem B3196457 : Blo 1419529 3196457 := bstep (se 2 (by rfl) ⟨1198671, by rfl⟩ : syracuseStep 3196457 = 2397343) B2397343
theorem B2131559 : Blo 1419529 2131559 := bstep (se 1 (by rfl) ⟨1598669, by rfl⟩ : syracuseStep 2131559 = 3197339) B3197339
theorem B3196691 : Blo 1419529 3196691 := bstep (se 1 (by rfl) ⟨2397518, by rfl⟩ : syracuseStep 3196691 = 4795037) B4795037
theorem B5760935 : Blo 1419529 5760935 := bstep (se 1 (by rfl) ⟨4320701, by rfl⟩ : syracuseStep 5760935 = 8641403) B8641403
theorem B4098011 : Blo 1419529 4098011 := bstep (se 1 (by rfl) ⟨3073508, by rfl⟩ : syracuseStep 4098011 = 6147017) B6147017
theorem B122940017 : Blo 1419529 122940017 := bstep (se 2 (by rfl) ⟨46102506, by rfl⟩ : syracuseStep 122940017 = 92205013) B92205013
theorem B1419931 : Blo 1419529 1419931 := bstep (se 1 (by rfl) ⟨1064948, by rfl⟩ : syracuseStep 1419931 = 2129897) B2129897
theorem B1419943 : Blo 1419529 1419943 := bstep (se 1 (by rfl) ⟨1064957, by rfl⟩ : syracuseStep 1419943 = 2129915) B2129915
theorem B58337981 : Blo 1419529 58337981 := bstep (se 3 (by rfl) ⟨10938371, by rfl⟩ : syracuseStep 58337981 = 21876743) B21876743
theorem B1419983 : Blo 1419529 1419983 := bstep (se 1 (by rfl) ⟨1064987, by rfl⟩ : syracuseStep 1419983 = 2129975) B2129975
theorem B5466847 : Blo 1419529 5466847 := bstep (se 1 (by rfl) ⟨4100135, by rfl⟩ : syracuseStep 5466847 = 8200271) B8200271
theorem B1420007 : Blo 1419529 1420007 := bstep (se 1 (by rfl) ⟨1065005, by rfl⟩ : syracuseStep 1420007 = 2130011) B2130011
theorem B4795145 : Blo 1419529 4795145 := bstep (se 2 (by rfl) ⟨1798179, by rfl⟩ : syracuseStep 4795145 = 3596359) B3596359
theorem B1420063 : Blo 1419529 1420063 := bstep (se 1 (by rfl) ⟨1065047, by rfl⟩ : syracuseStep 1420063 = 2130095) B2130095
theorem B116632619 : Blo 1419529 116632619 := bstep (se 1 (by rfl) ⟨87474464, by rfl⟩ : syracuseStep 116632619 = 174948929) B174948929
theorem B6147197 : Blo 1419529 6147197 := bstep (se 3 (by rfl) ⟨1152599, by rfl⟩ : syracuseStep 6147197 = 2305199) B2305199
theorem B5393537 : Blo 1419529 5393537 := bstep (se 2 (by rfl) ⟨2022576, by rfl⟩ : syracuseStep 5393537 = 4045153) B4045153
theorem B3198113 : Blo 1419529 3198113 := bstep (se 2 (by rfl) ⟨1199292, by rfl⟩ : syracuseStep 3198113 = 2398585) B2398585
theorem B1420455 : Blo 1419529 1420455 := bstep (se 1 (by rfl) ⟨1065341, by rfl⟩ : syracuseStep 1420455 = 2130683) B2130683
theorem B2698447 : Blo 1419529 2698447 := bstep (se 1 (by rfl) ⟨2023835, by rfl⟩ : syracuseStep 2698447 = 4047671) B4047671
theorem B3198203 : Blo 1419529 3198203 := bstep (se 1 (by rfl) ⟨2398652, by rfl⟩ : syracuseStep 3198203 = 4797305) B4797305
theorem B1420543 : Blo 1419529 1420543 := bstep (se 1 (by rfl) ⟨1065407, by rfl⟩ : syracuseStep 1420543 = 2130815) B2130815
theorem B3034523 : Blo 1419529 3034523 := bstep (se 1 (by rfl) ⟨2275892, by rfl⟩ : syracuseStep 3034523 = 4551785) B4551785
theorem B12955241 : Blo 1419529 12955241 := bstep (se 2 (by rfl) ⟨4858215, by rfl⟩ : syracuseStep 12955241 = 9716431) B9716431
theorem B1707751 : Blo 1419529 1707751 := bstep (se 1 (by rfl) ⟨1280813, by rfl⟩ : syracuseStep 1707751 = 2561627) B2561627
theorem B7188263 : Blo 1419529 7188263 := bstep (se 1 (by rfl) ⟨5391197, by rfl⟩ : syracuseStep 7188263 = 10782395) B10782395
theorem B3116911 : Blo 1419529 3116911 := bstep (se 1 (by rfl) ⟨2337683, by rfl⟩ : syracuseStep 3116911 = 4675367) B4675367
theorem B1421343 : Blo 1419529 1421343 := bstep (se 1 (by rfl) ⟨1066007, by rfl⟩ : syracuseStep 1421343 = 2132015) B2132015
theorem B3461383 : Blo 1419529 3461383 := bstep (se 1 (by rfl) ⟨2596037, by rfl⟩ : syracuseStep 3461383 = 5192075) B5192075
theorem B30773801 : Blo 1419529 30773801 := bstep (se 2 (by rfl) ⟨11540175, by rfl⟩ : syracuseStep 30773801 = 23080351) B23080351
theorem B13841387 : Blo 1419529 13841387 := bstep (se 1 (by rfl) ⟨10381040, by rfl⟩ : syracuseStep 13841387 = 20762081) B20762081
theorem B4797467 : Blo 1419529 4797467 := bstep (se 1 (by rfl) ⟨3598100, by rfl⟩ : syracuseStep 4797467 = 7196201) B7196201
theorem B41522291 : Blo 1419529 41522291 := bstep (se 1 (by rfl) ⟨31141718, by rfl⟩ : syracuseStep 41522291 = 62283437) B62283437
theorem B8639723 : Blo 1419529 8639723 := bstep (se 1 (by rfl) ⟨6479792, by rfl⟩ : syracuseStep 8639723 = 12959585) B12959585
theorem B11515223 : Blo 1419529 11515223 := bstep (se 1 (by rfl) ⟨8636417, by rfl⟩ : syracuseStep 11515223 = 17272835) B17272835
theorem B10794545 : Blo 1419529 10794545 := bstep (se 2 (by rfl) ⟨4047954, by rfl⟩ : syracuseStep 10794545 = 8095909) B8095909
theorem B4044583 : Blo 1419529 4044583 := bstep (se 1 (by rfl) ⟨3033437, by rfl⟩ : syracuseStep 4044583 = 6066875) B6066875
theorem B2398079 : Blo 1419529 2398079 := bstep (se 1 (by rfl) ⟨1798559, by rfl⟩ : syracuseStep 2398079 = 3597119) B3597119
theorem B103618541 : Blo 1419529 103618541 := bstep (se 3 (by rfl) ⟨19428476, by rfl⟩ : syracuseStep 103618541 = 38856953) B38856953
theorem B15349823 : Blo 1419529 15349823 := bstep (se 1 (by rfl) ⟨11512367, by rfl⟩ : syracuseStep 15349823 = 23024735) B23024735
theorem B3414155 : Blo 1419529 3414155 := bstep (se 1 (by rfl) ⟨2560616, by rfl⟩ : syracuseStep 3414155 = 5121233) B5121233
theorem B3594527 : Blo 1419529 3594527 := bstep (se 1 (by rfl) ⟨2695895, by rfl⟩ : syracuseStep 3594527 = 5391791) B5391791
theorem B4045211 : Blo 1419529 4045211 := bstep (se 1 (by rfl) ⟨3033908, by rfl⟩ : syracuseStep 4045211 = 6067817) B6067817
theorem B3594881 : Blo 1419529 3594881 := bstep (se 2 (by rfl) ⟨1348080, by rfl⟩ : syracuseStep 3594881 = 2696161) B2696161
theorem B40950481 : Blo 1419529 40950481 := bstep (se 2 (by rfl) ⟨15356430, by rfl⟩ : syracuseStep 40950481 = 30712861) B30712861
theorem B98401007 : Blo 1419529 98401007 := bstep (se 1 (by rfl) ⟨73800755, by rfl⟩ : syracuseStep 98401007 = 147601511) B147601511
theorem B59128573 : Blo 1419529 59128573 := bstep (se 3 (by rfl) ⟨11086607, by rfl⟩ : syracuseStep 59128573 = 22173215) B22173215
theorem B4791095 : Blo 1419529 4791095 := bstep (se 1 (by rfl) ⟨3593321, by rfl⟩ : syracuseStep 4791095 = 7186643) B7186643
theorem B3414847 : Blo 1419529 3414847 := bstep (se 1 (by rfl) ⟨2561135, by rfl⟩ : syracuseStep 3414847 = 5122271) B5122271
theorem B3595367 : Blo 1419529 3595367 := bstep (se 1 (by rfl) ⟨2696525, by rfl⟩ : syracuseStep 3595367 = 5393051) B5393051
theorem B3595499 : Blo 1419529 3595499 := bstep (se 1 (by rfl) ⟨2696624, by rfl⟩ : syracuseStep 3595499 = 5393249) B5393249
theorem B3505427 : Blo 1419529 3505427 := bstep (se 1 (by rfl) ⟨2629070, by rfl⟩ : syracuseStep 3505427 = 5258141) B5258141
theorem B7191827 : Blo 1419529 7191827 := bstep (se 1 (by rfl) ⟨5393870, by rfl⟩ : syracuseStep 7191827 = 10787741) B10787741
theorem B3194153 : Blo 1419529 3194153 := bstep (se 2 (by rfl) ⟨1197807, by rfl⟩ : syracuseStep 3194153 = 2395615) B2395615
theorem B3841435 : Blo 1419529 3841435 := bstep (se 1 (by rfl) ⟨2881076, by rfl⟩ : syracuseStep 3841435 = 5762153) B5762153
theorem B4046611 : Blo 1419529 4046611 := bstep (se 1 (by rfl) ⟨3034958, by rfl⟩ : syracuseStep 4046611 = 6069917) B6069917
theorem B2129951 : Blo 1419529 2129951 := bstep (se 1 (by rfl) ⟨1597463, by rfl⟩ : syracuseStep 2129951 = 3194927) B3194927
theorem B101056571 : Blo 1419529 101056571 := bstep (se 1 (by rfl) ⟨75792428, by rfl⟩ : syracuseStep 101056571 = 151584857) B151584857
theorem B3195035 : Blo 1419529 3195035 := bstep (se 1 (by rfl) ⟨2396276, by rfl⟩ : syracuseStep 3195035 = 4792553) B4792553
theorem B2130473 : Blo 1419529 2130473 := bstep (se 2 (by rfl) ⟨798927, by rfl⟩ : syracuseStep 2130473 = 1597855) B1597855
theorem B27681527 : Blo 1419529 27681527 := bstep (se 1 (by rfl) ⟨20761145, by rfl⟩ : syracuseStep 27681527 = 41522291) B41522291
theorem B7676815 : Blo 1419529 7676815 := bstep (se 1 (by rfl) ⟨5757611, by rfl⟩ : syracuseStep 7676815 = 11515223) B11515223
theorem B54600641 : Blo 1419529 54600641 := bstep (se 2 (by rfl) ⟨20475240, by rfl⟩ : syracuseStep 54600641 = 40950481) B40950481
theorem B2130971 : Blo 1419529 2130971 := bstep (se 1 (by rfl) ⟨1598228, by rfl⟩ : syracuseStep 2130971 = 3196457) B3196457
theorem B2131127 : Blo 1419529 2131127 := bstep (se 1 (by rfl) ⟨1598345, by rfl⟩ : syracuseStep 2131127 = 3196691) B3196691
theorem B1598719 : Blo 1419529 1598719 := bstep (se 1 (by rfl) ⟨1199039, by rfl⟩ : syracuseStep 1598719 = 2398079) B2398079
theorem B10233215 : Blo 1419529 10233215 := bstep (se 1 (by rfl) ⟨7674911, by rfl⟩ : syracuseStep 10233215 = 15349823) B15349823
theorem B2696807 : Blo 1419529 2696807 := bstep (se 1 (by rfl) ⟨2022605, by rfl⟩ : syracuseStep 2696807 = 4045211) B4045211
theorem B3597929 : Blo 1419529 3597929 := bstep (se 2 (by rfl) ⟨1349223, by rfl⟩ : syracuseStep 3597929 = 2698447) B2698447
theorem B34547309 : Blo 1419529 34547309 := bstep (se 3 (by rfl) ⟨6477620, by rfl⟩ : syracuseStep 34547309 = 12955241) B12955241
theorem B3196763 : Blo 1419529 3196763 := bstep (se 1 (by rfl) ⟨2397572, by rfl⟩ : syracuseStep 3196763 = 4795145) B4795145
theorem B5121913 : Blo 1419529 5121913 := bstep (se 2 (by rfl) ⟨1920717, by rfl⟩ : syracuseStep 5121913 = 3841435) B3841435
theorem B4098131 : Blo 1419529 4098131 := bstep (se 1 (by rfl) ⟨3073598, by rfl⟩ : syracuseStep 4098131 = 6147197) B6147197
theorem B2132075 : Blo 1419529 2132075 := bstep (se 1 (by rfl) ⟨1599056, by rfl⟩ : syracuseStep 2132075 = 3198113) B3198113
theorem B2132135 : Blo 1419529 2132135 := bstep (se 1 (by rfl) ⟨1599101, by rfl⟩ : syracuseStep 2132135 = 3198203) B3198203
theorem B2336951 : Blo 1419529 2336951 := bstep (se 1 (by rfl) ⟨1752713, by rfl⟩ : syracuseStep 2336951 = 3505427) B3505427
theorem B4794551 : Blo 1419529 4794551 := bstep (se 1 (by rfl) ⟨3595913, by rfl⟩ : syracuseStep 4794551 = 7191827) B7191827
theorem B5392777 : Blo 1419529 5392777 := bstep (se 2 (by rfl) ⟨2022291, by rfl⟩ : syracuseStep 5392777 = 4044583) B4044583
theorem B4155881 : Blo 1419529 4155881 := bstep (se 2 (by rfl) ⟨1558455, by rfl⟩ : syracuseStep 4155881 = 3116911) B3116911
theorem B10939175 : Blo 1419529 10939175 := bstep (se 1 (by rfl) ⟨8204381, by rfl⟩ : syracuseStep 10939175 = 16408763) B16408763
theorem B1420159 : Blo 1419529 1420159 := bstep (se 1 (by rfl) ⟨1065119, by rfl⟩ : syracuseStep 1420159 = 2130239) B2130239
theorem B1420271 : Blo 1419529 1420271 := bstep (se 1 (by rfl) ⟨1065203, by rfl⟩ : syracuseStep 1420271 = 2130407) B2130407
theorem B9104413 : Blo 1419529 9104413 := bstep (se 3 (by rfl) ⟨1707077, by rfl⟩ : syracuseStep 9104413 = 3414155) B3414155
theorem B4795577 : Blo 1419529 4795577 := bstep (se 2 (by rfl) ⟨1798341, by rfl⟩ : syracuseStep 4795577 = 3596683) B3596683
theorem B23039261 : Blo 1419529 23039261 := bstep (se 3 (by rfl) ⟨4319861, by rfl⟩ : syracuseStep 23039261 = 8639723) B8639723
theorem B9227591 : Blo 1419529 9227591 := bstep (se 1 (by rfl) ⟨6920693, by rfl⟩ : syracuseStep 9227591 = 13841387) B13841387
theorem B9104723 : Blo 1419529 9104723 := bstep (se 1 (by rfl) ⟨6828542, by rfl⟩ : syracuseStep 9104723 = 13657085) B13657085
theorem B3198311 : Blo 1419529 3198311 := bstep (se 1 (by rfl) ⟨2398733, by rfl⟩ : syracuseStep 3198311 = 4797467) B4797467
theorem B7196363 : Blo 1419529 7196363 := bstep (se 1 (by rfl) ⟨5397272, by rfl⟩ : syracuseStep 7196363 = 10794545) B10794545
theorem B1421039 : Blo 1419529 1421039 := bstep (se 1 (by rfl) ⟨1065779, by rfl⟩ : syracuseStep 1421039 = 2131559) B2131559
theorem B69079027 : Blo 1419529 69079027 := bstep (se 1 (by rfl) ⟨51809270, by rfl⟩ : syracuseStep 69079027 = 103618541) B103618541
theorem B18460709 : Blo 1419529 18460709 := bstep (se 4 (by rfl) ⟨1730691, by rfl⟩ : syracuseStep 18460709 = 3461383) B3461383
theorem B82063469 : Blo 1419529 82063469 := bstep (se 3 (by rfl) ⟨15386900, by rfl⟩ : syracuseStep 82063469 = 30773801) B30773801
theorem B2396351 : Blo 1419529 2396351 := bstep (se 1 (by rfl) ⟨1797263, by rfl⟩ : syracuseStep 2396351 = 3594527) B3594527
theorem B2396587 : Blo 1419529 2396587 := bstep (se 1 (by rfl) ⟨1797440, by rfl⟩ : syracuseStep 2396587 = 3594881) B3594881
theorem B38891987 : Blo 1419529 38891987 := bstep (se 1 (by rfl) ⟨29168990, by rfl⟩ : syracuseStep 38891987 = 58337981) B58337981
theorem B262402685 : Blo 1419529 262402685 := bstep (se 3 (by rfl) ⟨49200503, by rfl⟩ : syracuseStep 262402685 = 98401007) B98401007
theorem B77755079 : Blo 1419529 77755079 := bstep (se 1 (by rfl) ⟨58316309, by rfl⟩ : syracuseStep 77755079 = 116632619) B116632619
theorem B2396911 : Blo 1419529 2396911 := bstep (se 1 (by rfl) ⟨1797683, by rfl⟩ : syracuseStep 2396911 = 3595367) B3595367
theorem B2396999 : Blo 1419529 2396999 := bstep (se 1 (by rfl) ⟨1797749, by rfl⟩ : syracuseStep 2396999 = 3595499) B3595499
theorem B5395481 : Blo 1419529 5395481 := bstep (se 2 (by rfl) ⟨2023305, by rfl⟩ : syracuseStep 5395481 = 4046611) B4046611
theorem B1261409557 : Blo 1419529 1261409557 := bstep (se 6 (by rfl) ⟨29564286, by rfl⟩ : syracuseStep 1261409557 = 59128573) B59128573
theorem B7289129 : Blo 1419529 7289129 := bstep (se 2 (by rfl) ⟨2733423, by rfl⟩ : syracuseStep 7289129 = 5466847) B5466847
theorem B8092061 : Blo 1419529 8092061 := bstep (se 3 (by rfl) ⟨1517261, by rfl⟩ : syracuseStep 8092061 = 3034523) B3034523
theorem B4553129 : Blo 1419529 4553129 := bstep (se 2 (by rfl) ⟨1707423, by rfl⟩ : syracuseStep 4553129 = 3414847) B3414847
theorem B3840623 : Blo 1419529 3840623 := bstep (se 1 (by rfl) ⟨2880467, by rfl⟩ : syracuseStep 3840623 = 5760935) B5760935
theorem B81960011 : Blo 1419529 81960011 := bstep (se 1 (by rfl) ⟨61470008, by rfl⟩ : syracuseStep 81960011 = 122940017) B122940017
theorem B3194063 : Blo 1419529 3194063 := bstep (se 1 (by rfl) ⟨2395547, by rfl⟩ : syracuseStep 3194063 = 4791095) B4791095
theorem B3595691 : Blo 1419529 3595691 := bstep (se 1 (by rfl) ⟨2696768, by rfl⟩ : syracuseStep 3595691 = 5393537) B5393537
theorem B2129435 : Blo 1419529 2129435 := bstep (se 1 (by rfl) ⟨1597076, by rfl⟩ : syracuseStep 2129435 = 3194153) B3194153
theorem B2277001 : Blo 1419529 2277001 := bstep (se 2 (by rfl) ⟨853875, by rfl⟩ : syracuseStep 2277001 = 1707751) B1707751
theorem B4792175 : Blo 1419529 4792175 := bstep (se 1 (by rfl) ⟨3594131, by rfl⟩ : syracuseStep 4792175 = 7188263) B7188263
theorem B10928029 : Blo 1419529 10928029 := bstep (se 3 (by rfl) ⟨2049005, by rfl⟩ : syracuseStep 10928029 = 4098011) B4098011
theorem B67371047 : Blo 1419529 67371047 := bstep (se 1 (by rfl) ⟨50528285, by rfl⟩ : syracuseStep 67371047 = 101056571) B101056571
theorem B2130023 : Blo 1419529 2130023 := bstep (se 1 (by rfl) ⟨1597517, by rfl⟩ : syracuseStep 2130023 = 3195035) B3195035
theorem B1597567 : Blo 1419529 1597567 := bstep (se 1 (by rfl) ⟨1198175, by rfl⟩ : syracuseStep 1597567 = 2396351) B2396351
theorem B25927991 : Blo 1419529 25927991 := bstep (se 1 (by rfl) ⟨19445993, by rfl⟩ : syracuseStep 25927991 = 38891987) B38891987
theorem B1597999 : Blo 1419529 1597999 := bstep (se 1 (by rfl) ⟨1198499, by rfl⟩ : syracuseStep 1597999 = 2396999) B2396999
theorem B3195449 : Blo 1419529 3195449 := bstep (se 2 (by rfl) ⟨1198293, by rfl⟩ : syracuseStep 3195449 = 2396587) B2396587
theorem B3596987 : Blo 1419529 3596987 := bstep (se 1 (by rfl) ⟨2697740, by rfl⟩ : syracuseStep 3596987 = 5395481) B5395481
theorem B3195881 : Blo 1419529 3195881 := bstep (se 2 (by rfl) ⟨1198455, by rfl⟩ : syracuseStep 3195881 = 2396911) B2396911
theorem B12141677 : Blo 1419529 12141677 := bstep (se 3 (by rfl) ⟨2276564, by rfl⟩ : syracuseStep 12141677 = 4553129) B4553129
theorem B2131175 : Blo 1419529 2131175 := bstep (se 1 (by rfl) ⟨1598381, by rfl⟩ : syracuseStep 2131175 = 3196763) B3196763
theorem B3196367 : Blo 1419529 3196367 := bstep (se 1 (by rfl) ⟨2397275, by rfl⟩ : syracuseStep 3196367 = 4794551) B4794551
theorem B2131625 : Blo 1419529 2131625 := bstep (se 2 (by rfl) ⟨799359, by rfl⟩ : syracuseStep 2131625 = 1598719) B1598719
theorem B7292783 : Blo 1419529 7292783 := bstep (se 1 (by rfl) ⟨5469587, by rfl⟩ : syracuseStep 7292783 = 10939175) B10939175
theorem B3197051 : Blo 1419529 3197051 := bstep (se 1 (by rfl) ⟨2397788, by rfl⟩ : syracuseStep 3197051 = 4795577) B4795577
theorem B2132207 : Blo 1419529 2132207 := bstep (se 1 (by rfl) ⟨1599155, by rfl⟩ : syracuseStep 2132207 = 3198311) B3198311
theorem B1419623 : Blo 1419529 1419623 := bstep (se 1 (by rfl) ⟨1064717, by rfl⟩ : syracuseStep 1419623 = 2129435) B2129435
theorem B92105369 : Blo 1419529 92105369 := bstep (se 2 (by rfl) ⟨34539513, by rfl⟩ : syracuseStep 92105369 = 69079027) B69079027
theorem B1419967 : Blo 1419529 1419967 := bstep (se 1 (by rfl) ⟨1064975, by rfl⟩ : syracuseStep 1419967 = 2129951) B2129951
theorem B12307139 : Blo 1419529 12307139 := bstep (se 1 (by rfl) ⟨9230354, by rfl⟩ : syracuseStep 12307139 = 18460709) B18460709
theorem B54708979 : Blo 1419529 54708979 := bstep (se 1 (by rfl) ⟨41031734, by rfl⟩ : syracuseStep 54708979 = 82063469) B82063469
theorem B1420315 : Blo 1419529 1420315 := bstep (se 1 (by rfl) ⟨1065236, by rfl⟩ : syracuseStep 1420315 = 2130473) B2130473
theorem B174935123 : Blo 1419529 174935123 := bstep (se 1 (by rfl) ⟨131201342, by rfl⟩ : syracuseStep 174935123 = 262402685) B262402685
theorem B36400427 : Blo 1419529 36400427 := bstep (se 1 (by rfl) ⟨27300320, by rfl⟩ : syracuseStep 36400427 = 54600641) B54600641
theorem B1420647 : Blo 1419529 1420647 := bstep (se 1 (by rfl) ⟨1065485, by rfl⟩ : syracuseStep 1420647 = 2130971) B2130971
theorem B1420751 : Blo 1419529 1420751 := bstep (se 1 (by rfl) ⟨1065563, by rfl⟩ : syracuseStep 1420751 = 2131127) B2131127
theorem B1797871 : Blo 1419529 1797871 := bstep (se 1 (by rfl) ⟨1348403, by rfl⟩ : syracuseStep 1797871 = 2696807) B2696807
theorem B23031539 : Blo 1419529 23031539 := bstep (se 1 (by rfl) ⟨17273654, by rfl⟩ : syracuseStep 23031539 = 34547309) B34547309
theorem B10235753 : Blo 1419529 10235753 := bstep (se 2 (by rfl) ⟨3838407, by rfl⟩ : syracuseStep 10235753 = 7676815) B7676815
theorem B2732087 : Blo 1419529 2732087 := bstep (se 1 (by rfl) ⟨2049065, by rfl⟩ : syracuseStep 2732087 = 4098131) B4098131
theorem B1421383 : Blo 1419529 1421383 := bstep (se 1 (by rfl) ⟨1066037, by rfl⟩ : syracuseStep 1421383 = 2132075) B2132075
theorem B1421423 : Blo 1419529 1421423 := bstep (se 1 (by rfl) ⟨1066067, by rfl⟩ : syracuseStep 1421423 = 2132135) B2132135
theorem B5394707 : Blo 1419529 5394707 := bstep (se 1 (by rfl) ⟨4046030, by rfl⟩ : syracuseStep 5394707 = 8092061) B8092061
theorem B1681879409 : Blo 1419529 1681879409 := bstep (se 2 (by rfl) ⟨630704778, by rfl⟩ : syracuseStep 1681879409 = 1261409557) B1261409557
theorem B2560415 : Blo 1419529 2560415 := bstep (se 1 (by rfl) ⟨1920311, by rfl⟩ : syracuseStep 2560415 = 3840623) B3840623
theorem B3036001 : Blo 1419529 3036001 := bstep (se 2 (by rfl) ⟨1138500, by rfl⟩ : syracuseStep 3036001 = 2277001) B2277001
theorem B2397127 : Blo 1419529 2397127 := bstep (se 1 (by rfl) ⟨1797845, by rfl⟩ : syracuseStep 2397127 = 3595691) B3595691
theorem B4797575 : Blo 1419529 4797575 := bstep (se 1 (by rfl) ⟨3598181, by rfl⟩ : syracuseStep 4797575 = 7196363) B7196363
theorem B6829217 : Blo 1419529 6829217 := bstep (se 2 (by rfl) ⟨2560956, by rfl⟩ : syracuseStep 6829217 = 5121913) B5121913
theorem B14570705 : Blo 1419529 14570705 := bstep (se 2 (by rfl) ⟨5464014, by rfl⟩ : syracuseStep 14570705 = 10928029) B10928029
theorem B51836719 : Blo 1419529 51836719 := bstep (se 1 (by rfl) ⟨38877539, by rfl⟩ : syracuseStep 51836719 = 77755079) B77755079
theorem B6231869 : Blo 1419529 6231869 := bstep (se 3 (by rfl) ⟨1168475, by rfl⟩ : syracuseStep 6231869 = 2336951) B2336951
theorem B18454351 : Blo 1419529 18454351 := bstep (se 1 (by rfl) ⟨13840763, by rfl⟩ : syracuseStep 18454351 = 27681527) B27681527
theorem B7190369 : Blo 1419529 7190369 := bstep (se 2 (by rfl) ⟨2696388, by rfl⟩ : syracuseStep 7190369 = 5392777) B5392777
theorem B19437677 : Blo 1419529 19437677 := bstep (se 3 (by rfl) ⟨3644564, by rfl⟩ : syracuseStep 19437677 = 7289129) B7289129
theorem B6822143 : Blo 1419529 6822143 := bstep (se 1 (by rfl) ⟨5116607, by rfl⟩ : syracuseStep 6822143 = 10233215) B10233215
theorem B2398619 : Blo 1419529 2398619 := bstep (se 1 (by rfl) ⟨1798964, by rfl⟩ : syracuseStep 2398619 = 3597929) B3597929
theorem B11082349 : Blo 1419529 11082349 := bstep (se 3 (by rfl) ⟨2077940, by rfl⟩ : syracuseStep 11082349 = 4155881) B4155881
theorem B12139217 : Blo 1419529 12139217 := bstep (se 2 (by rfl) ⟨4552206, by rfl⟩ : syracuseStep 12139217 = 9104413) B9104413
theorem B54640007 : Blo 1419529 54640007 := bstep (se 1 (by rfl) ⟨40980005, by rfl⟩ : syracuseStep 54640007 = 81960011) B81960011
theorem B2129375 : Blo 1419529 2129375 := bstep (se 1 (by rfl) ⟨1597031, by rfl⟩ : syracuseStep 2129375 = 3194063) B3194063
theorem B15359507 : Blo 1419529 15359507 := bstep (se 1 (by rfl) ⟨11519630, by rfl⟩ : syracuseStep 15359507 = 23039261) B23039261
theorem B6151727 : Blo 1419529 6151727 := bstep (se 1 (by rfl) ⟨4613795, by rfl⟩ : syracuseStep 6151727 = 9227591) B9227591
theorem B6069815 : Blo 1419529 6069815 := bstep (se 1 (by rfl) ⟨4552361, by rfl⟩ : syracuseStep 6069815 = 9104723) B9104723
theorem B3194783 : Blo 1419529 3194783 := bstep (se 1 (by rfl) ⟨2396087, by rfl⟩ : syracuseStep 3194783 = 4792175) B4792175
theorem B2130089 : Blo 1419529 2130089 := bstep (se 2 (by rfl) ⟨798783, by rfl⟩ : syracuseStep 2130089 = 1597567) B1597567
theorem B3596471 : Blo 1419529 3596471 := bstep (se 1 (by rfl) ⟨2697353, by rfl⟩ : syracuseStep 3596471 = 5394707) B5394707
theorem B17285327 : Blo 1419529 17285327 := bstep (se 1 (by rfl) ⟨12963995, by rfl⟩ : syracuseStep 17285327 = 25927991) B25927991
theorem B2130299 : Blo 1419529 2130299 := bstep (se 1 (by rfl) ⟨1597724, by rfl⟩ : syracuseStep 2130299 = 3195449) B3195449
theorem B2130587 : Blo 1419529 2130587 := bstep (se 1 (by rfl) ⟨1597940, by rfl⟩ : syracuseStep 2130587 = 3195881) B3195881
theorem B2130665 : Blo 1419529 2130665 := bstep (se 2 (by rfl) ⟨798999, by rfl⟩ : syracuseStep 2130665 = 1597999) B1597999
theorem B8094451 : Blo 1419529 8094451 := bstep (se 1 (by rfl) ⟨6070838, by rfl⟩ : syracuseStep 8094451 = 12141677) B12141677
theorem B2130911 : Blo 1419529 2130911 := bstep (se 1 (by rfl) ⟨1598183, by rfl⟩ : syracuseStep 2130911 = 3196367) B3196367
theorem B4048001 : Blo 1419529 4048001 := bstep (se 2 (by rfl) ⟨1518000, by rfl⟩ : syracuseStep 4048001 = 3036001) B3036001
theorem B4154579 : Blo 1419529 4154579 := bstep (se 1 (by rfl) ⟨3115934, by rfl⟩ : syracuseStep 4154579 = 6231869) B6231869
theorem B4793579 : Blo 1419529 4793579 := bstep (se 1 (by rfl) ⟨3595184, by rfl⟩ : syracuseStep 4793579 = 7190369) B7190369
theorem B3196169 : Blo 1419529 3196169 := bstep (se 2 (by rfl) ⟨1198563, by rfl⟩ : syracuseStep 3196169 = 2397127) B2397127
theorem B2131367 : Blo 1419529 2131367 := bstep (se 1 (by rfl) ⟨1598525, by rfl⟩ : syracuseStep 2131367 = 3197051) B3197051
theorem B4548095 : Blo 1419529 4548095 := bstep (se 1 (by rfl) ⟨3411071, by rfl⟩ : syracuseStep 4548095 = 6822143) B6822143
theorem B1599079 : Blo 1419529 1599079 := bstep (se 1 (by rfl) ⟨1199309, by rfl⟩ : syracuseStep 1599079 = 2398619) B2398619
theorem B116623415 : Blo 1419529 116623415 := bstep (se 1 (by rfl) ⟨87467561, by rfl⟩ : syracuseStep 116623415 = 174935123) B174935123
theorem B24266951 : Blo 1419529 24266951 := bstep (se 1 (by rfl) ⟨18200213, by rfl⟩ : syracuseStep 24266951 = 36400427) B36400427
theorem B1419583 : Blo 1419529 1419583 := bstep (se 1 (by rfl) ⟨1064687, by rfl⟩ : syracuseStep 1419583 = 2129375) B2129375
theorem B15354359 : Blo 1419529 15354359 := bstep (se 1 (by rfl) ⟨11515769, by rfl⟩ : syracuseStep 15354359 = 23031539) B23031539
theorem B1420015 : Blo 1419529 1420015 := bstep (se 1 (by rfl) ⟨1065011, by rfl⟩ : syracuseStep 1420015 = 2130023) B2130023
theorem B7285565 : Blo 1419529 7285565 := bstep (se 3 (by rfl) ⟨1366043, by rfl⟩ : syracuseStep 7285565 = 2732087) B2732087
theorem B3198383 : Blo 1419529 3198383 := bstep (se 1 (by rfl) ⟨2398787, by rfl⟩ : syracuseStep 3198383 = 4797575) B4797575
theorem B1420783 : Blo 1419529 1420783 := bstep (se 1 (by rfl) ⟨1065587, by rfl⟩ : syracuseStep 1420783 = 2131175) B2131175
theorem B72945305 : Blo 1419529 72945305 := bstep (se 2 (by rfl) ⟨27354489, by rfl⟩ : syracuseStep 72945305 = 54708979) B54708979
theorem B6827773 : Blo 1419529 6827773 := bstep (se 3 (by rfl) ⟨1280207, by rfl⟩ : syracuseStep 6827773 = 2560415) B2560415
theorem B1421083 : Blo 1419529 1421083 := bstep (se 1 (by rfl) ⟨1065812, by rfl⟩ : syracuseStep 1421083 = 2131625) B2131625
theorem B4861855 : Blo 1419529 4861855 := bstep (se 1 (by rfl) ⟨3646391, by rfl⟩ : syracuseStep 4861855 = 7292783) B7292783
theorem B1421471 : Blo 1419529 1421471 := bstep (se 1 (by rfl) ⟨1066103, by rfl⟩ : syracuseStep 1421471 = 2132207) B2132207
theorem B61403579 : Blo 1419529 61403579 := bstep (se 1 (by rfl) ⟨46052684, by rfl⟩ : syracuseStep 61403579 = 92105369) B92105369
theorem B8204759 : Blo 1419529 8204759 := bstep (se 1 (by rfl) ⟨6153569, by rfl⟩ : syracuseStep 8204759 = 12307139) B12307139
theorem B36426671 : Blo 1419529 36426671 := bstep (se 1 (by rfl) ⟨27320003, by rfl⟩ : syracuseStep 36426671 = 54640007) B54640007
theorem B2397161 : Blo 1419529 2397161 := bstep (se 2 (by rfl) ⟨898935, by rfl⟩ : syracuseStep 2397161 = 1797871) B1797871
theorem B4101151 : Blo 1419529 4101151 := bstep (se 1 (by rfl) ⟨3075863, by rfl⟩ : syracuseStep 4101151 = 6151727) B6151727
theorem B24605801 : Blo 1419529 24605801 := bstep (se 2 (by rfl) ⟨9227175, by rfl⟩ : syracuseStep 24605801 = 18454351) B18454351
theorem B44914031 : Blo 1419529 44914031 := bstep (se 1 (by rfl) ⟨33685523, by rfl⟩ : syracuseStep 44914031 = 67371047) B67371047
theorem B1121252939 : Blo 1419529 1121252939 := bstep (se 1 (by rfl) ⟨840939704, by rfl⟩ : syracuseStep 1121252939 = 1681879409) B1681879409
theorem B2397991 : Blo 1419529 2397991 := bstep (se 1 (by rfl) ⟨1798493, by rfl⟩ : syracuseStep 2397991 = 3596987) B3596987
theorem B4552811 : Blo 1419529 4552811 := bstep (se 1 (by rfl) ⟨3414608, by rfl⟩ : syracuseStep 4552811 = 6829217) B6829217
theorem B9713803 : Blo 1419529 9713803 := bstep (se 1 (by rfl) ⟨7285352, by rfl⟩ : syracuseStep 9713803 = 14570705) B14570705
theorem B14776465 : Blo 1419529 14776465 := bstep (se 2 (by rfl) ⟨5541174, by rfl⟩ : syracuseStep 14776465 = 11082349) B11082349
theorem B12958451 : Blo 1419529 12958451 := bstep (se 1 (by rfl) ⟨9718838, by rfl⟩ : syracuseStep 12958451 = 19437677) B19437677
theorem B8092811 : Blo 1419529 8092811 := bstep (se 1 (by rfl) ⟨6069608, by rfl⟩ : syracuseStep 8092811 = 12139217) B12139217
theorem B10239671 : Blo 1419529 10239671 := bstep (se 1 (by rfl) ⟨7679753, by rfl⟩ : syracuseStep 10239671 = 15359507) B15359507
theorem B4046543 : Blo 1419529 4046543 := bstep (se 1 (by rfl) ⟨3034907, by rfl⟩ : syracuseStep 4046543 = 6069815) B6069815
theorem B69115625 : Blo 1419529 69115625 := bstep (se 2 (by rfl) ⟨25918359, by rfl⟩ : syracuseStep 69115625 = 51836719) B51836719
theorem B6823835 : Blo 1419529 6823835 := bstep (se 1 (by rfl) ⟨5117876, by rfl⟩ : syracuseStep 6823835 = 10235753) B10235753
theorem B2129855 : Blo 1419529 2129855 := bstep (se 1 (by rfl) ⟨1597391, by rfl⟩ : syracuseStep 2129855 = 3194783) B3194783
theorem B12951737 : Blo 1419529 12951737 := bstep (se 2 (by rfl) ⟨4856901, by rfl⟩ : syracuseStep 12951737 = 9713803) B9713803
theorem B19701953 : Blo 1419529 19701953 := bstep (se 2 (by rfl) ⟨7388232, by rfl⟩ : syracuseStep 19701953 = 14776465) B14776465
theorem B40935719 : Blo 1419529 40935719 := bstep (se 1 (by rfl) ⟨30701789, by rfl⟩ : syracuseStep 40935719 = 61403579) B61403579
theorem B1598107 : Blo 1419529 1598107 := bstep (se 1 (by rfl) ⟨1198580, by rfl⟩ : syracuseStep 1598107 = 2397161) B2397161
theorem B2769719 : Blo 1419529 2769719 := bstep (se 1 (by rfl) ⟨2077289, by rfl⟩ : syracuseStep 2769719 = 4154579) B4154579
theorem B3195719 : Blo 1419529 3195719 := bstep (se 1 (by rfl) ⟨2396789, by rfl⟩ : syracuseStep 3195719 = 4793579) B4793579
theorem B2130779 : Blo 1419529 2130779 := bstep (se 1 (by rfl) ⟨1598084, by rfl⟩ : syracuseStep 2130779 = 3196169) B3196169
theorem B29942687 : Blo 1419529 29942687 := bstep (se 1 (by rfl) ⟨22457015, by rfl⟩ : syracuseStep 29942687 = 44914031) B44914031
theorem B3032063 : Blo 1419529 3032063 := bstep (se 1 (by rfl) ⟨2274047, by rfl⟩ : syracuseStep 3032063 = 4548095) B4548095
theorem B2132105 : Blo 1419529 2132105 := bstep (se 2 (by rfl) ⟨799539, by rfl⟩ : syracuseStep 2132105 = 1599079) B1599079
theorem B2132255 : Blo 1419529 2132255 := bstep (se 1 (by rfl) ⟨1599191, by rfl⟩ : syracuseStep 2132255 = 3198383) B3198383
theorem B9103697 : Blo 1419529 9103697 := bstep (se 2 (by rfl) ⟨3413886, by rfl⟩ : syracuseStep 9103697 = 6827773) B6827773
theorem B3197321 : Blo 1419529 3197321 := bstep (se 2 (by rfl) ⟨1198995, by rfl⟩ : syracuseStep 3197321 = 2397991) B2397991
theorem B48630203 : Blo 1419529 48630203 := bstep (se 1 (by rfl) ⟨36472652, by rfl⟩ : syracuseStep 48630203 = 72945305) B72945305
theorem B6826447 : Blo 1419529 6826447 := bstep (se 1 (by rfl) ⟨5119835, by rfl⟩ : syracuseStep 6826447 = 10239671) B10239671
theorem B2697695 : Blo 1419529 2697695 := bstep (se 1 (by rfl) ⟨2023271, by rfl⟩ : syracuseStep 2697695 = 4046543) B4046543
theorem B6482473 : Blo 1419529 6482473 := bstep (se 2 (by rfl) ⟨2430927, by rfl⟩ : syracuseStep 6482473 = 4861855) B4861855
theorem B4549223 : Blo 1419529 4549223 := bstep (se 1 (by rfl) ⟨3411917, by rfl⟩ : syracuseStep 4549223 = 6823835) B6823835
theorem B1419903 : Blo 1419529 1419903 := bstep (se 1 (by rfl) ⟨1064927, by rfl⟩ : syracuseStep 1419903 = 2129855) B2129855
theorem B1420059 : Blo 1419529 1420059 := bstep (se 1 (by rfl) ⟨1065044, by rfl⟩ : syracuseStep 1420059 = 2130089) B2130089
theorem B1420199 : Blo 1419529 1420199 := bstep (se 1 (by rfl) ⟨1065149, by rfl⟩ : syracuseStep 1420199 = 2130299) B2130299
theorem B1420391 : Blo 1419529 1420391 := bstep (se 1 (by rfl) ⟨1065293, by rfl⟩ : syracuseStep 1420391 = 2130587) B2130587
theorem B1420443 : Blo 1419529 1420443 := bstep (se 1 (by rfl) ⟨1065332, by rfl⟩ : syracuseStep 1420443 = 2130665) B2130665
theorem B24284447 : Blo 1419529 24284447 := bstep (se 1 (by rfl) ⟨18213335, by rfl⟩ : syracuseStep 24284447 = 36426671) B36426671
theorem B1420607 : Blo 1419529 1420607 := bstep (se 1 (by rfl) ⟨1065455, by rfl⟩ : syracuseStep 1420607 = 2130911) B2130911
theorem B16403867 : Blo 1419529 16403867 := bstep (se 1 (by rfl) ⟨12302900, by rfl⟩ : syracuseStep 16403867 = 24605801) B24605801
theorem B2698667 : Blo 1419529 2698667 := bstep (se 1 (by rfl) ⟨2024000, by rfl⟩ : syracuseStep 2698667 = 4048001) B4048001
theorem B1420911 : Blo 1419529 1420911 := bstep (se 1 (by rfl) ⟨1065683, by rfl⟩ : syracuseStep 1420911 = 2131367) B2131367
theorem B10792601 : Blo 1419529 10792601 := bstep (se 2 (by rfl) ⟨4047225, by rfl⟩ : syracuseStep 10792601 = 8094451) B8094451
theorem B5468201 : Blo 1419529 5468201 := bstep (se 2 (by rfl) ⟨2050575, by rfl⟩ : syracuseStep 5468201 = 4101151) B4101151
theorem B3035207 : Blo 1419529 3035207 := bstep (se 1 (by rfl) ⟨2276405, by rfl⟩ : syracuseStep 3035207 = 4552811) B4552811
theorem B10236239 : Blo 1419529 10236239 := bstep (se 1 (by rfl) ⟨7677179, by rfl⟩ : syracuseStep 10236239 = 15354359) B15354359
theorem B8638967 : Blo 1419529 8638967 := bstep (se 1 (by rfl) ⟨6479225, by rfl⟩ : syracuseStep 8638967 = 12958451) B12958451
theorem B5395207 : Blo 1419529 5395207 := bstep (se 1 (by rfl) ⟨4046405, by rfl⟩ : syracuseStep 5395207 = 8092811) B8092811
theorem B46077083 : Blo 1419529 46077083 := bstep (se 1 (by rfl) ⟨34557812, by rfl⟩ : syracuseStep 46077083 = 69115625) B69115625
theorem B2397647 : Blo 1419529 2397647 := bstep (se 1 (by rfl) ⟨1798235, by rfl⟩ : syracuseStep 2397647 = 3596471) B3596471
theorem B11523551 : Blo 1419529 11523551 := bstep (se 1 (by rfl) ⟨8642663, by rfl⟩ : syracuseStep 11523551 = 17285327) B17285327
theorem B5469839 : Blo 1419529 5469839 := bstep (se 1 (by rfl) ⟨4102379, by rfl⟩ : syracuseStep 5469839 = 8204759) B8204759
theorem B747501959 : Blo 1419529 747501959 := bstep (se 1 (by rfl) ⟨560626469, by rfl⟩ : syracuseStep 747501959 = 1121252939) B1121252939
theorem B77748943 : Blo 1419529 77748943 := bstep (se 1 (by rfl) ⟨58311707, by rfl⟩ : syracuseStep 77748943 = 116623415) B116623415
theorem B16177967 : Blo 1419529 16177967 := bstep (se 1 (by rfl) ⟨12133475, by rfl⟩ : syracuseStep 16177967 = 24266951) B24266951
theorem B4857043 : Blo 1419529 4857043 := bstep (se 1 (by rfl) ⟨3642782, by rfl⟩ : syracuseStep 4857043 = 7285565) B7285565
theorem B3645467 : Blo 1419529 3645467 := bstep (se 1 (by rfl) ⟨2734100, by rfl⟩ : syracuseStep 3645467 = 5468201) B5468201
theorem B2023471 : Blo 1419529 2023471 := bstep (se 1 (by rfl) ⟨1517603, by rfl⟩ : syracuseStep 2023471 = 3035207) B3035207
theorem B8634491 : Blo 1419529 8634491 := bstep (se 1 (by rfl) ⟨6475868, by rfl⟩ : syracuseStep 8634491 = 12951737) B12951737
theorem B6824159 : Blo 1419529 6824159 := bstep (se 1 (by rfl) ⟨5118119, by rfl⟩ : syracuseStep 6824159 = 10236239) B10236239
theorem B5759311 : Blo 1419529 5759311 := bstep (se 1 (by rfl) ⟨4319483, by rfl⟩ : syracuseStep 5759311 = 8638967) B8638967
theorem B2130479 : Blo 1419529 2130479 := bstep (se 1 (by rfl) ⟨1597859, by rfl⟩ : syracuseStep 2130479 = 3195719) B3195719
theorem B9101929 : Blo 1419529 9101929 := bstep (se 2 (by rfl) ⟨3413223, by rfl⟩ : syracuseStep 9101929 = 6826447) B6826447
theorem B2130809 : Blo 1419529 2130809 := bstep (se 2 (by rfl) ⟨799053, by rfl⟩ : syracuseStep 2130809 = 1598107) B1598107
theorem B1598431 : Blo 1419529 1598431 := bstep (se 1 (by rfl) ⟨1198823, by rfl⟩ : syracuseStep 1598431 = 2397647) B2397647
theorem B7193609 : Blo 1419529 7193609 := bstep (se 2 (by rfl) ⟨2697603, by rfl⟩ : syracuseStep 7193609 = 5395207) B5395207
theorem B3646559 : Blo 1419529 3646559 := bstep (se 1 (by rfl) ⟨2734919, by rfl⟩ : syracuseStep 3646559 = 5469839) B5469839
theorem B30729469 : Blo 1419529 30729469 := bstep (se 3 (by rfl) ⟨5761775, by rfl⟩ : syracuseStep 30729469 = 11523551) B11523551
theorem B2131547 : Blo 1419529 2131547 := bstep (se 1 (by rfl) ⟨1598660, by rfl⟩ : syracuseStep 2131547 = 3197321) B3197321
theorem B3032815 : Blo 1419529 3032815 := bstep (se 1 (by rfl) ⟨2274611, by rfl⟩ : syracuseStep 3032815 = 4549223) B4549223
theorem B16189631 : Blo 1419529 16189631 := bstep (se 1 (by rfl) ⟨12142223, by rfl⟩ : syracuseStep 16189631 = 24284447) B24284447
theorem B7195067 : Blo 1419529 7195067 := bstep (se 1 (by rfl) ⟨5396300, by rfl⟩ : syracuseStep 7195067 = 10792601) B10792601
theorem B13134635 : Blo 1419529 13134635 := bstep (se 1 (by rfl) ⟨9850976, by rfl⟩ : syracuseStep 13134635 = 19701953) B19701953
theorem B27290479 : Blo 1419529 27290479 := bstep (se 1 (by rfl) ⟨20467859, by rfl⟩ : syracuseStep 27290479 = 40935719) B40935719
theorem B1420519 : Blo 1419529 1420519 := bstep (se 1 (by rfl) ⟨1065389, by rfl⟩ : syracuseStep 1420519 = 2130779) B2130779
theorem B138292757 : Blo 1419529 138292757 := bstep (se 6 (by rfl) ⟨3241236, by rfl⟩ : syracuseStep 138292757 = 6482473) B6482473
theorem B103665257 : Blo 1419529 103665257 := bstep (se 2 (by rfl) ⟨38874471, by rfl⟩ : syracuseStep 103665257 = 77748943) B77748943
theorem B1421403 : Blo 1419529 1421403 := bstep (se 1 (by rfl) ⟨1066052, by rfl⟩ : syracuseStep 1421403 = 2132105) B2132105
theorem B1421503 : Blo 1419529 1421503 := bstep (se 1 (by rfl) ⟨1066127, by rfl⟩ : syracuseStep 1421503 = 2132255) B2132255
theorem B6476057 : Blo 1419529 6476057 := bstep (se 2 (by rfl) ⟨2428521, by rfl⟩ : syracuseStep 6476057 = 4857043) B4857043
theorem B32420135 : Blo 1419529 32420135 := bstep (se 1 (by rfl) ⟨24315101, by rfl⟩ : syracuseStep 32420135 = 48630203) B48630203
theorem B1798463 : Blo 1419529 1798463 := bstep (se 1 (by rfl) ⟨1348847, by rfl⟩ : syracuseStep 1798463 = 2697695) B2697695
theorem B10785311 : Blo 1419529 10785311 := bstep (se 1 (by rfl) ⟨8088983, by rfl⟩ : syracuseStep 10785311 = 16177967) B16177967
theorem B7385917 : Blo 1419529 7385917 := bstep (se 3 (by rfl) ⟨1384859, by rfl⟩ : syracuseStep 7385917 = 2769719) B2769719
theorem B1799111 : Blo 1419529 1799111 := bstep (se 1 (by rfl) ⟨1349333, by rfl⟩ : syracuseStep 1799111 = 2698667) B2698667
theorem B2021375 : Blo 1419529 2021375 := bstep (se 1 (by rfl) ⟨1516031, by rfl⟩ : syracuseStep 2021375 = 3032063) B3032063
theorem B30718055 : Blo 1419529 30718055 := bstep (se 1 (by rfl) ⟨23038541, by rfl⟩ : syracuseStep 30718055 = 46077083) B46077083
theorem B6069131 : Blo 1419529 6069131 := bstep (se 1 (by rfl) ⟨4551848, by rfl⟩ : syracuseStep 6069131 = 9103697) B9103697
theorem B498334639 : Blo 1419529 498334639 := bstep (se 1 (by rfl) ⟨373750979, by rfl⟩ : syracuseStep 498334639 = 747501959) B747501959
theorem B10935911 : Blo 1419529 10935911 := bstep (se 1 (by rfl) ⟨8201933, by rfl⟩ : syracuseStep 10935911 = 16403867) B16403867
theorem B79847165 : Blo 1419529 79847165 := bstep (se 3 (by rfl) ⟨14971343, by rfl⟩ : syracuseStep 79847165 = 29942687) B29942687
theorem B4317371 : Blo 1419529 4317371 := bstep (se 1 (by rfl) ⟨3238028, by rfl⟩ : syracuseStep 4317371 = 6476057) B6476057
theorem B9847889 : Blo 1419529 9847889 := bstep (se 2 (by rfl) ⟨3692958, by rfl⟩ : syracuseStep 9847889 = 7385917) B7385917
theorem B664446185 : Blo 1419529 664446185 := bstep (se 2 (by rfl) ⟨249167319, by rfl⟩ : syracuseStep 664446185 = 498334639) B498334639
theorem B2131241 : Blo 1419529 2131241 := bstep (se 2 (by rfl) ⟨799215, by rfl⟩ : syracuseStep 2131241 = 1598431) B1598431
theorem B92195171 : Blo 1419529 92195171 := bstep (se 1 (by rfl) ⟨69146378, by rfl⟩ : syracuseStep 92195171 = 138292757) B138292757
theorem B69110171 : Blo 1419529 69110171 := bstep (se 1 (by rfl) ⟨51832628, by rfl⟩ : syracuseStep 69110171 = 103665257) B103665257
theorem B2697961 : Blo 1419529 2697961 := bstep (se 2 (by rfl) ⟨1011735, by rfl⟩ : syracuseStep 2697961 = 2023471) B2023471
theorem B4549439 : Blo 1419529 4549439 := bstep (se 1 (by rfl) ⟨3412079, by rfl⟩ : syracuseStep 4549439 = 6824159) B6824159
theorem B21613423 : Blo 1419529 21613423 := bstep (se 1 (by rfl) ⟨16210067, by rfl⟩ : syracuseStep 21613423 = 32420135) B32420135
theorem B1420319 : Blo 1419529 1420319 := bstep (se 1 (by rfl) ⟨1065239, by rfl⟩ : syracuseStep 1420319 = 2130479) B2130479
theorem B7679081 : Blo 1419529 7679081 := bstep (se 2 (by rfl) ⟨2879655, by rfl⟩ : syracuseStep 7679081 = 5759311) B5759311
theorem B1420539 : Blo 1419529 1420539 := bstep (se 1 (by rfl) ⟨1065404, by rfl⟩ : syracuseStep 1420539 = 2130809) B2130809
theorem B4795739 : Blo 1419529 4795739 := bstep (se 1 (by rfl) ⟨3596804, by rfl⟩ : syracuseStep 4795739 = 7193609) B7193609
theorem B12135905 : Blo 1419529 12135905 := bstep (se 2 (by rfl) ⟨4550964, by rfl⟩ : syracuseStep 12135905 = 9101929) B9101929
theorem B4795901 : Blo 1419529 4795901 := bstep (se 3 (by rfl) ⟨899231, by rfl⟩ : syracuseStep 4795901 = 1798463) B1798463
theorem B1421031 : Blo 1419529 1421031 := bstep (se 1 (by rfl) ⟨1065773, by rfl⟩ : syracuseStep 1421031 = 2131547) B2131547
theorem B10793087 : Blo 1419529 10793087 := bstep (se 1 (by rfl) ⟨8094815, by rfl⟩ : syracuseStep 10793087 = 16189631) B16189631
theorem B4796711 : Blo 1419529 4796711 := bstep (se 1 (by rfl) ⟨3597533, by rfl⟩ : syracuseStep 4796711 = 7195067) B7195067
theorem B40972625 : Blo 1419529 40972625 := bstep (se 2 (by rfl) ⟨15364734, by rfl⟩ : syracuseStep 40972625 = 30729469) B30729469
theorem B4043753 : Blo 1419529 4043753 := bstep (se 2 (by rfl) ⟨1516407, by rfl⟩ : syracuseStep 4043753 = 3032815) B3032815
theorem B4797629 : Blo 1419529 4797629 := bstep (se 3 (by rfl) ⟨899555, by rfl⟩ : syracuseStep 4797629 = 1799111) B1799111
theorem B5756327 : Blo 1419529 5756327 := bstep (se 1 (by rfl) ⟨4317245, by rfl⟩ : syracuseStep 5756327 = 8634491) B8634491
theorem B38884981 : Blo 1419529 38884981 := bstep (se 5 (by rfl) ⟨1822733, by rfl⟩ : syracuseStep 38884981 = 3645467) B3645467
theorem B7190207 : Blo 1419529 7190207 := bstep (se 1 (by rfl) ⟨5392655, by rfl⟩ : syracuseStep 7190207 = 10785311) B10785311
theorem B2431039 : Blo 1419529 2431039 := bstep (se 1 (by rfl) ⟨1823279, by rfl⟩ : syracuseStep 2431039 = 3646559) B3646559
theorem B36387305 : Blo 1419529 36387305 := bstep (se 2 (by rfl) ⟨13645239, by rfl⟩ : syracuseStep 36387305 = 27290479) B27290479
theorem B20478703 : Blo 1419529 20478703 := bstep (se 1 (by rfl) ⟨15359027, by rfl⟩ : syracuseStep 20478703 = 30718055) B30718055
theorem B29162429 : Blo 1419529 29162429 := bstep (se 3 (by rfl) ⟨5467955, by rfl⟩ : syracuseStep 29162429 = 10935911) B10935911
theorem B8756423 : Blo 1419529 8756423 := bstep (se 1 (by rfl) ⟨6567317, by rfl⟩ : syracuseStep 8756423 = 13134635) B13134635
theorem B4046087 : Blo 1419529 4046087 := bstep (se 1 (by rfl) ⟨3034565, by rfl⟩ : syracuseStep 4046087 = 6069131) B6069131
theorem B212925773 : Blo 1419529 212925773 := bstep (se 3 (by rfl) ⟨39923582, by rfl⟩ : syracuseStep 212925773 = 79847165) B79847165
theorem B5390333 : Blo 1419529 5390333 := bstep (se 3 (by rfl) ⟨1010687, by rfl⟩ : syracuseStep 5390333 = 2021375) B2021375
theorem B2695835 : Blo 1419529 2695835 := bstep (se 1 (by rfl) ⟨2021876, by rfl⟩ : syracuseStep 2695835 = 4043753) B4043753
theorem B3597281 : Blo 1419529 3597281 := bstep (se 2 (by rfl) ⟨1348980, by rfl⟩ : syracuseStep 3597281 = 2697961) B2697961
theorem B27304937 : Blo 1419529 27304937 := bstep (se 2 (by rfl) ⟨10239351, by rfl⟩ : syracuseStep 27304937 = 20478703) B20478703
theorem B4793471 : Blo 1419529 4793471 := bstep (se 1 (by rfl) ⟨3595103, by rfl⟩ : syracuseStep 4793471 = 7190207) B7190207
theorem B46073447 : Blo 1419529 46073447 := bstep (se 1 (by rfl) ⟨34555085, by rfl⟩ : syracuseStep 46073447 = 69110171) B69110171
theorem B24258203 : Blo 1419529 24258203 := bstep (se 1 (by rfl) ⟨18193652, by rfl⟩ : syracuseStep 24258203 = 36387305) B36387305
theorem B3032959 : Blo 1419529 3032959 := bstep (se 1 (by rfl) ⟨2274719, by rfl⟩ : syracuseStep 3032959 = 4549439) B4549439
theorem B19441619 : Blo 1419529 19441619 := bstep (se 1 (by rfl) ⟨14581214, by rfl⟩ : syracuseStep 19441619 = 29162429) B29162429
theorem B2697391 : Blo 1419529 2697391 := bstep (se 1 (by rfl) ⟨2023043, by rfl⟩ : syracuseStep 2697391 = 4046087) B4046087
theorem B3197159 : Blo 1419529 3197159 := bstep (se 1 (by rfl) ⟨2397869, by rfl⟩ : syracuseStep 3197159 = 4795739) B4795739
theorem B3197267 : Blo 1419529 3197267 := bstep (se 1 (by rfl) ⟨2397950, by rfl⟩ : syracuseStep 3197267 = 4795901) B4795901
theorem B7195391 : Blo 1419529 7195391 := bstep (se 1 (by rfl) ⟨5396543, by rfl⟩ : syracuseStep 7195391 = 10793087) B10793087
theorem B2878247 : Blo 1419529 2878247 := bstep (se 1 (by rfl) ⟨2158685, by rfl⟩ : syracuseStep 2878247 = 4317371) B4317371
theorem B3197807 : Blo 1419529 3197807 := bstep (se 1 (by rfl) ⟨2398355, by rfl⟩ : syracuseStep 3197807 = 4796711) B4796711
theorem B27315083 : Blo 1419529 27315083 := bstep (se 1 (by rfl) ⟨20486312, by rfl⟩ : syracuseStep 27315083 = 40972625) B40972625
theorem B6565259 : Blo 1419529 6565259 := bstep (se 1 (by rfl) ⟨4923944, by rfl⟩ : syracuseStep 6565259 = 9847889) B9847889
theorem B3198419 : Blo 1419529 3198419 := bstep (se 1 (by rfl) ⟨2398814, by rfl⟩ : syracuseStep 3198419 = 4797629) B4797629
theorem B1420827 : Blo 1419529 1420827 := bstep (se 1 (by rfl) ⟨1065620, by rfl⟩ : syracuseStep 1420827 = 2131241) B2131241
theorem B3837551 : Blo 1419529 3837551 := bstep (se 1 (by rfl) ⟨2878163, by rfl⟩ : syracuseStep 3837551 = 5756327) B5756327
theorem B5837615 : Blo 1419529 5837615 := bstep (se 1 (by rfl) ⟨4378211, by rfl⟩ : syracuseStep 5837615 = 8756423) B8756423
theorem B8090603 : Blo 1419529 8090603 := bstep (se 1 (by rfl) ⟨6067952, by rfl⟩ : syracuseStep 8090603 = 12135905) B12135905
theorem B3593555 : Blo 1419529 3593555 := bstep (se 1 (by rfl) ⟨2695166, by rfl⟩ : syracuseStep 3593555 = 5390333) B5390333
theorem B3241385 : Blo 1419529 3241385 := bstep (se 2 (by rfl) ⟨1215519, by rfl⟩ : syracuseStep 3241385 = 2431039) B2431039
theorem B20477549 : Blo 1419529 20477549 := bstep (se 3 (by rfl) ⟨3839540, by rfl⟩ : syracuseStep 20477549 = 7679081) B7679081
theorem B442964123 : Blo 1419529 442964123 := bstep (se 1 (by rfl) ⟨332223092, by rfl⟩ : syracuseStep 442964123 = 664446185) B664446185
theorem B28817897 : Blo 1419529 28817897 := bstep (se 2 (by rfl) ⟨10806711, by rfl⟩ : syracuseStep 28817897 = 21613423) B21613423
theorem B61463447 : Blo 1419529 61463447 := bstep (se 1 (by rfl) ⟨46097585, by rfl⟩ : syracuseStep 61463447 = 92195171) B92195171
theorem B51846641 : Blo 1419529 51846641 := bstep (se 2 (by rfl) ⟨19442490, by rfl⟩ : syracuseStep 51846641 = 38884981) B38884981
theorem B141950515 : Blo 1419529 141950515 := bstep (se 1 (by rfl) ⟨106462886, by rfl⟩ : syracuseStep 141950515 = 212925773) B212925773
theorem B3596521 : Blo 1419529 3596521 := bstep (se 2 (by rfl) ⟨1348695, by rfl⟩ : syracuseStep 3596521 = 2697391) B2697391
theorem B3891743 : Blo 1419529 3891743 := bstep (se 1 (by rfl) ⟨2918807, by rfl⟩ : syracuseStep 3891743 = 5837615) B5837615
theorem B18203291 : Blo 1419529 18203291 := bstep (se 1 (by rfl) ⟨13652468, by rfl⟩ : syracuseStep 18203291 = 27304937) B27304937
theorem B3195647 : Blo 1419529 3195647 := bstep (se 1 (by rfl) ⟨2396735, by rfl⟩ : syracuseStep 3195647 = 4793471) B4793471
theorem B17507357 : Blo 1419529 17507357 := bstep (se 3 (by rfl) ⟨3282629, by rfl⟩ : syracuseStep 17507357 = 6565259) B6565259
theorem B16172135 : Blo 1419529 16172135 := bstep (se 1 (by rfl) ⟨12129101, by rfl⟩ : syracuseStep 16172135 = 24258203) B24258203
theorem B12961079 : Blo 1419529 12961079 := bstep (se 1 (by rfl) ⟨9720809, by rfl⟩ : syracuseStep 12961079 = 19441619) B19441619
theorem B2131439 : Blo 1419529 2131439 := bstep (se 1 (by rfl) ⟨1598579, by rfl⟩ : syracuseStep 2131439 = 3197159) B3197159
theorem B2131511 : Blo 1419529 2131511 := bstep (se 1 (by rfl) ⟨1598633, by rfl⟩ : syracuseStep 2131511 = 3197267) B3197267
theorem B10233469 : Blo 1419529 10233469 := bstep (se 3 (by rfl) ⟨1918775, by rfl⟩ : syracuseStep 10233469 = 3837551) B3837551
theorem B1918831 : Blo 1419529 1918831 := bstep (se 1 (by rfl) ⟨1439123, by rfl⟩ : syracuseStep 1918831 = 2878247) B2878247
theorem B2131871 : Blo 1419529 2131871 := bstep (se 1 (by rfl) ⟨1598903, by rfl⟩ : syracuseStep 2131871 = 3197807) B3197807
theorem B2132279 : Blo 1419529 2132279 := bstep (se 1 (by rfl) ⟨1599209, by rfl⟩ : syracuseStep 2132279 = 3198419) B3198419
theorem B34564427 : Blo 1419529 34564427 := bstep (se 1 (by rfl) ⟨25923320, by rfl⟩ : syracuseStep 34564427 = 51846641) B51846641
theorem B1797223 : Blo 1419529 1797223 := bstep (se 1 (by rfl) ⟨1347917, by rfl⟩ : syracuseStep 1797223 = 2695835) B2695835
theorem B5393735 : Blo 1419529 5393735 := bstep (se 1 (by rfl) ⟨4045301, by rfl⟩ : syracuseStep 5393735 = 8090603) B8090603
theorem B2395703 : Blo 1419529 2395703 := bstep (se 1 (by rfl) ⟨1796777, by rfl⟩ : syracuseStep 2395703 = 3593555) B3593555
theorem B30715631 : Blo 1419529 30715631 := bstep (se 1 (by rfl) ⟨23036723, by rfl⟩ : syracuseStep 30715631 = 46073447) B46073447
theorem B13651699 : Blo 1419529 13651699 := bstep (se 1 (by rfl) ⟨10238774, by rfl⟩ : syracuseStep 13651699 = 20477549) B20477549
theorem B295309415 : Blo 1419529 295309415 := bstep (se 1 (by rfl) ⟨221482061, by rfl⟩ : syracuseStep 295309415 = 442964123) B442964123
theorem B4796927 : Blo 1419529 4796927 := bstep (se 1 (by rfl) ⟨3597695, by rfl⟩ : syracuseStep 4796927 = 7195391) B7195391
theorem B4043945 : Blo 1419529 4043945 := bstep (se 2 (by rfl) ⟨1516479, by rfl⟩ : syracuseStep 4043945 = 3032959) B3032959
theorem B2398187 : Blo 1419529 2398187 := bstep (se 1 (by rfl) ⟨1798640, by rfl⟩ : syracuseStep 2398187 = 3597281) B3597281
theorem B2160923 : Blo 1419529 2160923 := bstep (se 1 (by rfl) ⟨1620692, by rfl⟩ : syracuseStep 2160923 = 3241385) B3241385
theorem B76847725 : Blo 1419529 76847725 := bstep (se 3 (by rfl) ⟨14408948, by rfl⟩ : syracuseStep 76847725 = 28817897) B28817897
theorem B18210055 : Blo 1419529 18210055 := bstep (se 1 (by rfl) ⟨13657541, by rfl⟩ : syracuseStep 18210055 = 27315083) B27315083
theorem B40975631 : Blo 1419529 40975631 := bstep (se 1 (by rfl) ⟨30731723, by rfl⟩ : syracuseStep 40975631 = 61463447) B61463447
theorem B189267353 : Blo 1419529 189267353 := bstep (se 2 (by rfl) ⟨70975257, by rfl⟩ : syracuseStep 189267353 = 141950515) B141950515
theorem B2130431 : Blo 1419529 2130431 := bstep (se 1 (by rfl) ⟨1597823, by rfl⟩ : syracuseStep 2130431 = 3195647) B3195647
theorem B10781423 : Blo 1419529 10781423 := bstep (se 1 (by rfl) ⟨8086067, by rfl⟩ : syracuseStep 10781423 = 16172135) B16172135
theorem B1598791 : Blo 1419529 1598791 := bstep (se 1 (by rfl) ⟨1199093, by rfl⟩ : syracuseStep 1598791 = 2398187) B2398187
theorem B2558441 : Blo 1419529 2558441 := bstep (se 2 (by rfl) ⟨959415, by rfl⟩ : syracuseStep 2558441 = 1918831) B1918831
theorem B196872943 : Blo 1419529 196872943 := bstep (se 1 (by rfl) ⟨147654707, by rfl⟩ : syracuseStep 196872943 = 295309415) B295309415
theorem B4795361 : Blo 1419529 4795361 := bstep (se 2 (by rfl) ⟨1798260, by rfl⟩ : syracuseStep 4795361 = 3596521) B3596521
theorem B3197951 : Blo 1419529 3197951 := bstep (se 1 (by rfl) ⟨2398463, by rfl⟩ : syracuseStep 3197951 = 4796927) B4796927
theorem B12135527 : Blo 1419529 12135527 := bstep (se 1 (by rfl) ⟨9101645, by rfl⟩ : syracuseStep 12135527 = 18203291) B18203291
theorem B10783853 : Blo 1419529 10783853 := bstep (se 3 (by rfl) ⟨2021972, by rfl⟩ : syracuseStep 10783853 = 4043945) B4043945
theorem B5762461 : Blo 1419529 5762461 := bstep (se 3 (by rfl) ⟨1080461, by rfl⟩ : syracuseStep 5762461 = 2160923) B2160923
theorem B1420959 : Blo 1419529 1420959 := bstep (se 1 (by rfl) ⟨1065719, by rfl⟩ : syracuseStep 1420959 = 2131439) B2131439
theorem B1421007 : Blo 1419529 1421007 := bstep (se 1 (by rfl) ⟨1065755, by rfl⟩ : syracuseStep 1421007 = 2131511) B2131511
theorem B1421247 : Blo 1419529 1421247 := bstep (se 1 (by rfl) ⟨1065935, by rfl⟩ : syracuseStep 1421247 = 2131871) B2131871
theorem B2396297 : Blo 1419529 2396297 := bstep (se 2 (by rfl) ⟨898611, by rfl⟩ : syracuseStep 2396297 = 1797223) B1797223
theorem B1421519 : Blo 1419529 1421519 := bstep (se 1 (by rfl) ⟨1066139, by rfl⟩ : syracuseStep 1421519 = 2132279) B2132279
theorem B13644625 : Blo 1419529 13644625 := bstep (se 2 (by rfl) ⟨5116734, by rfl⟩ : syracuseStep 13644625 = 10233469) B10233469
theorem B27317087 : Blo 1419529 27317087 := bstep (se 1 (by rfl) ⟨20487815, by rfl⟩ : syracuseStep 27317087 = 40975631) B40975631
theorem B126178235 : Blo 1419529 126178235 := bstep (se 1 (by rfl) ⟨94633676, by rfl⟩ : syracuseStep 126178235 = 189267353) B189267353
theorem B20477087 : Blo 1419529 20477087 := bstep (se 1 (by rfl) ⟨15357815, by rfl⟩ : syracuseStep 20477087 = 30715631) B30715631
theorem B2594495 : Blo 1419529 2594495 := bstep (se 1 (by rfl) ⟨1945871, by rfl⟩ : syracuseStep 2594495 = 3891743) B3891743
theorem B11671571 : Blo 1419529 11671571 := bstep (se 1 (by rfl) ⟨8753678, by rfl⟩ : syracuseStep 11671571 = 17507357) B17507357
theorem B102463633 : Blo 1419529 102463633 := bstep (se 2 (by rfl) ⟨38423862, by rfl⟩ : syracuseStep 102463633 = 76847725) B76847725
theorem B8640719 : Blo 1419529 8640719 := bstep (se 1 (by rfl) ⟨6480539, by rfl⟩ : syracuseStep 8640719 = 12961079) B12961079
theorem B23042951 : Blo 1419529 23042951 := bstep (se 1 (by rfl) ⟨17282213, by rfl⟩ : syracuseStep 23042951 = 34564427) B34564427
theorem B24280073 : Blo 1419529 24280073 := bstep (se 2 (by rfl) ⟨9105027, by rfl⟩ : syracuseStep 24280073 = 18210055) B18210055
theorem B3595823 : Blo 1419529 3595823 := bstep (se 1 (by rfl) ⟨2696867, by rfl⟩ : syracuseStep 3595823 = 5393735) B5393735
theorem B18202265 : Blo 1419529 18202265 := bstep (se 2 (by rfl) ⟨6825849, by rfl⟩ : syracuseStep 18202265 = 13651699) B13651699
theorem B1597135 : Blo 1419529 1597135 := bstep (se 1 (by rfl) ⟨1197851, by rfl⟩ : syracuseStep 1597135 = 2395703) B2395703
theorem B1597531 : Blo 1419529 1597531 := bstep (se 1 (by rfl) ⟨1198148, by rfl⟩ : syracuseStep 1597531 = 2396297) B2396297
theorem B136618177 : Blo 1419529 136618177 := bstep (se 2 (by rfl) ⟨51231816, by rfl⟩ : syracuseStep 136618177 = 102463633) B102463633
theorem B18211391 : Blo 1419529 18211391 := bstep (se 1 (by rfl) ⟨13658543, by rfl⟩ : syracuseStep 18211391 = 27317087) B27317087
theorem B262497257 : Blo 1419529 262497257 := bstep (se 2 (by rfl) ⟨98436471, by rfl⟩ : syracuseStep 262497257 = 196872943) B196872943
theorem B1729663 : Blo 1419529 1729663 := bstep (se 1 (by rfl) ⟨1297247, by rfl⟩ : syracuseStep 1729663 = 2594495) B2594495
theorem B5760479 : Blo 1419529 5760479 := bstep (se 1 (by rfl) ⟨4320359, by rfl⟩ : syracuseStep 5760479 = 8640719) B8640719
theorem B1705627 : Blo 1419529 1705627 := bstep (se 1 (by rfl) ⟨1279220, by rfl⟩ : syracuseStep 1705627 = 2558441) B2558441
theorem B2131721 : Blo 1419529 2131721 := bstep (se 2 (by rfl) ⟨799395, by rfl⟩ : syracuseStep 2131721 = 1598791) B1598791
theorem B15361967 : Blo 1419529 15361967 := bstep (se 1 (by rfl) ⟨11521475, by rfl⟩ : syracuseStep 15361967 = 23042951) B23042951
theorem B3196907 : Blo 1419529 3196907 := bstep (se 1 (by rfl) ⟨2397680, by rfl⟩ : syracuseStep 3196907 = 4795361) B4795361
theorem B2131967 : Blo 1419529 2131967 := bstep (se 1 (by rfl) ⟨1598975, by rfl⟩ : syracuseStep 2131967 = 3197951) B3197951
theorem B12134843 : Blo 1419529 12134843 := bstep (se 1 (by rfl) ⟨9101132, by rfl⟩ : syracuseStep 12134843 = 18202265) B18202265
theorem B31124189 : Blo 1419529 31124189 := bstep (se 3 (by rfl) ⟨5835785, by rfl⟩ : syracuseStep 31124189 = 11671571) B11671571
theorem B1420287 : Blo 1419529 1420287 := bstep (se 1 (by rfl) ⟨1065215, by rfl⟩ : syracuseStep 1420287 = 2130431) B2130431
theorem B7187615 : Blo 1419529 7187615 := bstep (se 1 (by rfl) ⟨5390711, by rfl⟩ : syracuseStep 7187615 = 10781423) B10781423
theorem B84118823 : Blo 1419529 84118823 := bstep (se 1 (by rfl) ⟨63089117, by rfl⟩ : syracuseStep 84118823 = 126178235) B126178235
theorem B13651391 : Blo 1419529 13651391 := bstep (se 1 (by rfl) ⟨10238543, by rfl⟩ : syracuseStep 13651391 = 20477087) B20477087
theorem B8090351 : Blo 1419529 8090351 := bstep (se 1 (by rfl) ⟨6067763, by rfl⟩ : syracuseStep 8090351 = 12135527) B12135527
theorem B7189235 : Blo 1419529 7189235 := bstep (se 1 (by rfl) ⟨5391926, by rfl⟩ : syracuseStep 7189235 = 10783853) B10783853
theorem B2397215 : Blo 1419529 2397215 := bstep (se 1 (by rfl) ⟨1797911, by rfl⟩ : syracuseStep 2397215 = 3595823) B3595823
theorem B18192833 : Blo 1419529 18192833 := bstep (se 2 (by rfl) ⟨6822312, by rfl⟩ : syracuseStep 18192833 = 13644625) B13644625
theorem B7683281 : Blo 1419529 7683281 := bstep (se 2 (by rfl) ⟨2881230, by rfl⟩ : syracuseStep 7683281 = 5762461) B5762461
theorem B16186715 : Blo 1419529 16186715 := bstep (se 1 (by rfl) ⟨12140036, by rfl⟩ : syracuseStep 16186715 = 24280073) B24280073
theorem B2129513 : Blo 1419529 2129513 := bstep (se 2 (by rfl) ⟨798567, by rfl⟩ : syracuseStep 2129513 = 1597135) B1597135
theorem B2130041 : Blo 1419529 2130041 := bstep (se 2 (by rfl) ⟨798765, by rfl⟩ : syracuseStep 2130041 = 1597531) B1597531
theorem B182157569 : Blo 1419529 182157569 := bstep (se 2 (by rfl) ⟨68309088, by rfl⟩ : syracuseStep 182157569 = 136618177) B136618177
theorem B12140927 : Blo 1419529 12140927 := bstep (se 1 (by rfl) ⟨9105695, by rfl⟩ : syracuseStep 12140927 = 18211391) B18211391
theorem B4792823 : Blo 1419529 4792823 := bstep (se 1 (by rfl) ⟨3594617, by rfl⟩ : syracuseStep 4792823 = 7189235) B7189235
theorem B174998171 : Blo 1419529 174998171 := bstep (se 1 (by rfl) ⟨131248628, by rfl⟩ : syracuseStep 174998171 = 262497257) B262497257
theorem B9224869 : Blo 1419529 9224869 := bstep (se 4 (by rfl) ⟨864831, by rfl⟩ : syracuseStep 9224869 = 1729663) B1729663
theorem B1598143 : Blo 1419529 1598143 := bstep (se 1 (by rfl) ⟨1198607, by rfl⟩ : syracuseStep 1598143 = 2397215) B2397215
theorem B10241311 : Blo 1419529 10241311 := bstep (se 1 (by rfl) ⟨7680983, by rfl⟩ : syracuseStep 10241311 = 15361967) B15361967
theorem B2131271 : Blo 1419529 2131271 := bstep (se 1 (by rfl) ⟨1598453, by rfl⟩ : syracuseStep 2131271 = 3196907) B3196907
theorem B5122187 : Blo 1419529 5122187 := bstep (se 1 (by rfl) ⟨3841640, by rfl⟩ : syracuseStep 5122187 = 7683281) B7683281
theorem B10791143 : Blo 1419529 10791143 := bstep (se 1 (by rfl) ⟨8093357, by rfl⟩ : syracuseStep 10791143 = 16186715) B16186715
theorem B1419675 : Blo 1419529 1419675 := bstep (se 1 (by rfl) ⟨1064756, by rfl⟩ : syracuseStep 1419675 = 2129513) B2129513
theorem B5393567 : Blo 1419529 5393567 := bstep (se 1 (by rfl) ⟨4045175, by rfl⟩ : syracuseStep 5393567 = 8090351) B8090351
theorem B1421147 : Blo 1419529 1421147 := bstep (se 1 (by rfl) ⟨1065860, by rfl⟩ : syracuseStep 1421147 = 2131721) B2131721
theorem B1421311 : Blo 1419529 1421311 := bstep (se 1 (by rfl) ⟨1065983, by rfl⟩ : syracuseStep 1421311 = 2131967) B2131967
theorem B8089895 : Blo 1419529 8089895 := bstep (se 1 (by rfl) ⟨6067421, by rfl⟩ : syracuseStep 8089895 = 12134843) B12134843
theorem B12128555 : Blo 1419529 12128555 := bstep (se 1 (by rfl) ⟨9096416, by rfl⟩ : syracuseStep 12128555 = 18192833) B18192833
theorem B56079215 : Blo 1419529 56079215 := bstep (se 1 (by rfl) ⟨42059411, by rfl⟩ : syracuseStep 56079215 = 84118823) B84118823
theorem B2274169 : Blo 1419529 2274169 := bstep (se 2 (by rfl) ⟨852813, by rfl⟩ : syracuseStep 2274169 = 1705627) B1705627
theorem B3840319 : Blo 1419529 3840319 := bstep (se 1 (by rfl) ⟨2880239, by rfl⟩ : syracuseStep 3840319 = 5760479) B5760479
theorem B20749459 : Blo 1419529 20749459 := bstep (se 1 (by rfl) ⟨15562094, by rfl⟩ : syracuseStep 20749459 = 31124189) B31124189
theorem B4791743 : Blo 1419529 4791743 := bstep (se 1 (by rfl) ⟨3593807, by rfl⟩ : syracuseStep 4791743 = 7187615) B7187615
theorem B9100927 : Blo 1419529 9100927 := bstep (se 1 (by rfl) ⟨6825695, by rfl⟩ : syracuseStep 9100927 = 13651391) B13651391
theorem B121438379 : Blo 1419529 121438379 := bstep (se 1 (by rfl) ⟨91078784, by rfl⟩ : syracuseStep 121438379 = 182157569) B182157569
theorem B8085703 : Blo 1419529 8085703 := bstep (se 1 (by rfl) ⟨6064277, by rfl⟩ : syracuseStep 8085703 = 12128555) B12128555
theorem B8093951 : Blo 1419529 8093951 := bstep (se 1 (by rfl) ⟨6070463, by rfl⟩ : syracuseStep 8093951 = 12140927) B12140927
theorem B3195215 : Blo 1419529 3195215 := bstep (se 1 (by rfl) ⟨2396411, by rfl⟩ : syracuseStep 3195215 = 4792823) B4792823
theorem B5120425 : Blo 1419529 5120425 := bstep (se 2 (by rfl) ⟨1920159, by rfl⟩ : syracuseStep 5120425 = 3840319) B3840319
theorem B2130857 : Blo 1419529 2130857 := bstep (se 2 (by rfl) ⟨799071, by rfl⟩ : syracuseStep 2130857 = 1598143) B1598143
theorem B3032225 : Blo 1419529 3032225 := bstep (se 2 (by rfl) ⟨1137084, by rfl⟩ : syracuseStep 3032225 = 2274169) B2274169
theorem B7194095 : Blo 1419529 7194095 := bstep (se 1 (by rfl) ⟨5395571, by rfl⟩ : syracuseStep 7194095 = 10791143) B10791143
theorem B27665945 : Blo 1419529 27665945 := bstep (se 2 (by rfl) ⟨10374729, by rfl⟩ : syracuseStep 27665945 = 20749459) B20749459
theorem B12134569 : Blo 1419529 12134569 := bstep (se 2 (by rfl) ⟨4550463, by rfl⟩ : syracuseStep 12134569 = 9100927) B9100927
theorem B1420027 : Blo 1419529 1420027 := bstep (se 1 (by rfl) ⟨1065020, by rfl⟩ : syracuseStep 1420027 = 2130041) B2130041
theorem B5393263 : Blo 1419529 5393263 := bstep (se 1 (by rfl) ⟨4044947, by rfl⟩ : syracuseStep 5393263 = 8089895) B8089895
theorem B116665447 : Blo 1419529 116665447 := bstep (se 1 (by rfl) ⟨87499085, by rfl⟩ : syracuseStep 116665447 = 174998171) B174998171
theorem B1420847 : Blo 1419529 1420847 := bstep (se 1 (by rfl) ⟨1065635, by rfl⟩ : syracuseStep 1420847 = 2131271) B2131271
theorem B12299825 : Blo 1419529 12299825 := bstep (se 2 (by rfl) ⟨4612434, by rfl⟩ : syracuseStep 12299825 = 9224869) B9224869
theorem B37386143 : Blo 1419529 37386143 := bstep (se 1 (by rfl) ⟨28039607, by rfl⟩ : syracuseStep 37386143 = 56079215) B56079215
theorem B3414791 : Blo 1419529 3414791 := bstep (se 1 (by rfl) ⟨2561093, by rfl⟩ : syracuseStep 3414791 = 5122187) B5122187
theorem B13655081 : Blo 1419529 13655081 := bstep (se 2 (by rfl) ⟨5120655, by rfl⟩ : syracuseStep 13655081 = 10241311) B10241311
theorem B3595711 : Blo 1419529 3595711 := bstep (se 1 (by rfl) ⟨2696783, by rfl⟩ : syracuseStep 3595711 = 5393567) B5393567
theorem B3194495 : Blo 1419529 3194495 := bstep (se 1 (by rfl) ⟨2395871, by rfl⟩ : syracuseStep 3194495 = 4791743) B4791743
theorem B36413549 : Blo 1419529 36413549 := bstep (se 3 (by rfl) ⟨6827540, by rfl⟩ : syracuseStep 36413549 = 13655081) B13655081
theorem B2130143 : Blo 1419529 2130143 := bstep (se 1 (by rfl) ⟨1597607, by rfl⟩ : syracuseStep 2130143 = 3195215) B3195215
theorem B16179425 : Blo 1419529 16179425 := bstep (se 2 (by rfl) ⟨6067284, by rfl⟩ : syracuseStep 16179425 = 12134569) B12134569
theorem B10780937 : Blo 1419529 10780937 := bstep (se 2 (by rfl) ⟨4042851, by rfl⟩ : syracuseStep 10780937 = 8085703) B8085703
theorem B4794281 : Blo 1419529 4794281 := bstep (se 2 (by rfl) ⟨1797855, by rfl⟩ : syracuseStep 4794281 = 3595711) B3595711
theorem B1420571 : Blo 1419529 1420571 := bstep (se 1 (by rfl) ⟨1065428, by rfl⟩ : syracuseStep 1420571 = 2130857) B2130857
theorem B4796063 : Blo 1419529 4796063 := bstep (se 1 (by rfl) ⟨3597047, by rfl⟩ : syracuseStep 4796063 = 7194095) B7194095
theorem B18443963 : Blo 1419529 18443963 := bstep (se 1 (by rfl) ⟨13832972, by rfl⟩ : syracuseStep 18443963 = 27665945) B27665945
theorem B24924095 : Blo 1419529 24924095 := bstep (se 1 (by rfl) ⟨18693071, by rfl⟩ : syracuseStep 24924095 = 37386143) B37386143
theorem B155553929 : Blo 1419529 155553929 := bstep (se 2 (by rfl) ⟨58332723, by rfl⟩ : syracuseStep 155553929 = 116665447) B116665447
theorem B27308933 : Blo 1419529 27308933 := bstep (se 4 (by rfl) ⟨2560212, by rfl⟩ : syracuseStep 27308933 = 5120425) B5120425
theorem B80958919 : Blo 1419529 80958919 := bstep (se 1 (by rfl) ⟨60719189, by rfl⟩ : syracuseStep 80958919 = 121438379) B121438379
theorem B5395967 : Blo 1419529 5395967 := bstep (se 1 (by rfl) ⟨4046975, by rfl⟩ : syracuseStep 5395967 = 8093951) B8093951
theorem B2021483 : Blo 1419529 2021483 := bstep (se 1 (by rfl) ⟨1516112, by rfl⟩ : syracuseStep 2021483 = 3032225) B3032225
theorem B7191017 : Blo 1419529 7191017 := bstep (se 2 (by rfl) ⟨2696631, by rfl⟩ : syracuseStep 7191017 = 5393263) B5393263
theorem B2276527 : Blo 1419529 2276527 := bstep (se 1 (by rfl) ⟨1707395, by rfl⟩ : syracuseStep 2276527 = 3414791) B3414791
theorem B8199883 : Blo 1419529 8199883 := bstep (se 1 (by rfl) ⟨6149912, by rfl⟩ : syracuseStep 8199883 = 12299825) B12299825
theorem B2129663 : Blo 1419529 2129663 := bstep (se 1 (by rfl) ⟨1597247, by rfl⟩ : syracuseStep 2129663 = 3194495) B3194495
theorem B103702619 : Blo 1419529 103702619 := bstep (se 1 (by rfl) ⟨77776964, by rfl⟩ : syracuseStep 103702619 = 155553929) B155553929
theorem B5390621 : Blo 1419529 5390621 := bstep (se 3 (by rfl) ⟨1010741, by rfl⟩ : syracuseStep 5390621 = 2021483) B2021483
theorem B3597311 : Blo 1419529 3597311 := bstep (se 1 (by rfl) ⟨2697983, by rfl⟩ : syracuseStep 3597311 = 5395967) B5395967
theorem B3196187 : Blo 1419529 3196187 := bstep (se 1 (by rfl) ⟨2397140, by rfl⟩ : syracuseStep 3196187 = 4794281) B4794281
theorem B4794011 : Blo 1419529 4794011 := bstep (se 1 (by rfl) ⟨3595508, by rfl⟩ : syracuseStep 4794011 = 7191017) B7191017
theorem B3197375 : Blo 1419529 3197375 := bstep (se 1 (by rfl) ⟨2398031, by rfl⟩ : syracuseStep 3197375 = 4796063) B4796063
theorem B1419775 : Blo 1419529 1419775 := bstep (se 1 (by rfl) ⟨1064831, by rfl⟩ : syracuseStep 1419775 = 2129663) B2129663
theorem B16616063 : Blo 1419529 16616063 := bstep (se 1 (by rfl) ⟨12462047, by rfl⟩ : syracuseStep 16616063 = 24924095) B24924095
theorem B24275699 : Blo 1419529 24275699 := bstep (se 1 (by rfl) ⟨18206774, by rfl⟩ : syracuseStep 24275699 = 36413549) B36413549
theorem B1420095 : Blo 1419529 1420095 := bstep (se 1 (by rfl) ⟨1065071, by rfl⟩ : syracuseStep 1420095 = 2130143) B2130143
theorem B7187291 : Blo 1419529 7187291 := bstep (se 1 (by rfl) ⟨5390468, by rfl⟩ : syracuseStep 7187291 = 10780937) B10780937
theorem B18205955 : Blo 1419529 18205955 := bstep (se 1 (by rfl) ⟨13654466, by rfl⟩ : syracuseStep 18205955 = 27308933) B27308933
theorem B43732709 : Blo 1419529 43732709 := bstep (se 4 (by rfl) ⟨4099941, by rfl⟩ : syracuseStep 43732709 = 8199883) B8199883
theorem B3035369 : Blo 1419529 3035369 := bstep (se 2 (by rfl) ⟨1138263, by rfl⟩ : syracuseStep 3035369 = 2276527) B2276527
theorem B10786283 : Blo 1419529 10786283 := bstep (se 1 (by rfl) ⟨8089712, by rfl⟩ : syracuseStep 10786283 = 16179425) B16179425
theorem B107945225 : Blo 1419529 107945225 := bstep (se 2 (by rfl) ⟨40479459, by rfl⟩ : syracuseStep 107945225 = 80958919) B80958919
theorem B12295975 : Blo 1419529 12295975 := bstep (se 1 (by rfl) ⟨9221981, by rfl⟩ : syracuseStep 12295975 = 18443963) B18443963
theorem B2023579 : Blo 1419529 2023579 := bstep (se 1 (by rfl) ⟨1517684, by rfl⟩ : syracuseStep 2023579 = 3035369) B3035369
theorem B2130791 : Blo 1419529 2130791 := bstep (se 1 (by rfl) ⟨1598093, by rfl⟩ : syracuseStep 2130791 = 3196187) B3196187
theorem B3196007 : Blo 1419529 3196007 := bstep (se 1 (by rfl) ⟨2397005, by rfl⟩ : syracuseStep 3196007 = 4794011) B4794011
theorem B2131583 : Blo 1419529 2131583 := bstep (se 1 (by rfl) ⟨1598687, by rfl⟩ : syracuseStep 2131583 = 3197375) B3197375
theorem B16394633 : Blo 1419529 16394633 := bstep (se 2 (by rfl) ⟨6147987, by rfl⟩ : syracuseStep 16394633 = 12295975) B12295975
theorem B69135079 : Blo 1419529 69135079 := bstep (se 1 (by rfl) ⟨51851309, by rfl⟩ : syracuseStep 69135079 = 103702619) B103702619
theorem B16183799 : Blo 1419529 16183799 := bstep (se 1 (by rfl) ⟨12137849, by rfl⟩ : syracuseStep 16183799 = 24275699) B24275699
theorem B12137303 : Blo 1419529 12137303 := bstep (se 1 (by rfl) ⟨9102977, by rfl⟩ : syracuseStep 12137303 = 18205955) B18205955
theorem B71963483 : Blo 1419529 71963483 := bstep (se 1 (by rfl) ⟨53972612, by rfl⟩ : syracuseStep 71963483 = 107945225) B107945225
theorem B3593747 : Blo 1419529 3593747 := bstep (se 1 (by rfl) ⟨2695310, by rfl⟩ : syracuseStep 3593747 = 5390621) B5390621
theorem B2398207 : Blo 1419529 2398207 := bstep (se 1 (by rfl) ⟨1798655, by rfl⟩ : syracuseStep 2398207 = 3597311) B3597311
theorem B7190855 : Blo 1419529 7190855 := bstep (se 1 (by rfl) ⟨5393141, by rfl⟩ : syracuseStep 7190855 = 10786283) B10786283
theorem B44309501 : Blo 1419529 44309501 := bstep (se 3 (by rfl) ⟨8308031, by rfl⟩ : syracuseStep 44309501 = 16616063) B16616063
theorem B4791527 : Blo 1419529 4791527 := bstep (se 1 (by rfl) ⟨3593645, by rfl⟩ : syracuseStep 4791527 = 7187291) B7187291
theorem B29155139 : Blo 1419529 29155139 := bstep (se 1 (by rfl) ⟨21866354, by rfl⟩ : syracuseStep 29155139 = 43732709) B43732709
theorem B10789199 : Blo 1419529 10789199 := bstep (se 1 (by rfl) ⟨8091899, by rfl⟩ : syracuseStep 10789199 = 16183799) B16183799
theorem B2130671 : Blo 1419529 2130671 := bstep (se 1 (by rfl) ⟨1598003, by rfl⟩ : syracuseStep 2130671 = 3196007) B3196007
theorem B4793903 : Blo 1419529 4793903 := bstep (se 1 (by rfl) ⟨3595427, by rfl⟩ : syracuseStep 4793903 = 7190855) B7190855
theorem B10929755 : Blo 1419529 10929755 := bstep (se 1 (by rfl) ⟨8197316, by rfl⟩ : syracuseStep 10929755 = 16394633) B16394633
theorem B3197609 : Blo 1419529 3197609 := bstep (se 2 (by rfl) ⟨1199103, by rfl⟩ : syracuseStep 3197609 = 2398207) B2398207
theorem B2698105 : Blo 1419529 2698105 := bstep (se 2 (by rfl) ⟨1011789, by rfl⟩ : syracuseStep 2698105 = 2023579) B2023579
theorem B1420527 : Blo 1419529 1420527 := bstep (se 1 (by rfl) ⟨1065395, by rfl⟩ : syracuseStep 1420527 = 2130791) B2130791
theorem B92180105 : Blo 1419529 92180105 := bstep (se 2 (by rfl) ⟨34567539, by rfl⟩ : syracuseStep 92180105 = 69135079) B69135079
theorem B2395831 : Blo 1419529 2395831 := bstep (se 1 (by rfl) ⟨1796873, by rfl⟩ : syracuseStep 2395831 = 3593747) B3593747
theorem B1421055 : Blo 1419529 1421055 := bstep (se 1 (by rfl) ⟨1065791, by rfl⟩ : syracuseStep 1421055 = 2131583) B2131583
theorem B191902621 : Blo 1419529 191902621 := bstep (se 3 (by rfl) ⟨35981741, by rfl⟩ : syracuseStep 191902621 = 71963483) B71963483
theorem B19436759 : Blo 1419529 19436759 := bstep (se 1 (by rfl) ⟨14577569, by rfl⟩ : syracuseStep 19436759 = 29155139) B29155139
theorem B8091535 : Blo 1419529 8091535 := bstep (se 1 (by rfl) ⟨6068651, by rfl⟩ : syracuseStep 8091535 = 12137303) B12137303
theorem B29539667 : Blo 1419529 29539667 := bstep (se 1 (by rfl) ⟨22154750, by rfl⟩ : syracuseStep 29539667 = 44309501) B44309501
theorem B3194351 : Blo 1419529 3194351 := bstep (se 1 (by rfl) ⟨2395763, by rfl⟩ : syracuseStep 3194351 = 4791527) B4791527
theorem B7192799 : Blo 1419529 7192799 := bstep (se 1 (by rfl) ⟨5394599, by rfl⟩ : syracuseStep 7192799 = 10789199) B10789199
theorem B3195935 : Blo 1419529 3195935 := bstep (se 1 (by rfl) ⟨2396951, by rfl⟩ : syracuseStep 3195935 = 4793903) B4793903
theorem B3597473 : Blo 1419529 3597473 := bstep (se 2 (by rfl) ⟨1349052, by rfl⟩ : syracuseStep 3597473 = 2698105) B2698105
theorem B255870161 : Blo 1419529 255870161 := bstep (se 2 (by rfl) ⟨95951310, by rfl⟩ : syracuseStep 255870161 = 191902621) B191902621
theorem B2131739 : Blo 1419529 2131739 := bstep (se 1 (by rfl) ⟨1598804, by rfl⟩ : syracuseStep 2131739 = 3197609) B3197609
theorem B1420447 : Blo 1419529 1420447 := bstep (se 1 (by rfl) ⟨1065335, by rfl⟩ : syracuseStep 1420447 = 2130671) B2130671
theorem B61453403 : Blo 1419529 61453403 := bstep (se 1 (by rfl) ⟨46090052, by rfl⟩ : syracuseStep 61453403 = 92180105) B92180105
theorem B12957839 : Blo 1419529 12957839 := bstep (se 1 (by rfl) ⟨9718379, by rfl⟩ : syracuseStep 12957839 = 19436759) B19436759
theorem B78772445 : Blo 1419529 78772445 := bstep (se 3 (by rfl) ⟨14769833, by rfl⟩ : syracuseStep 78772445 = 29539667) B29539667
theorem B29146013 : Blo 1419529 29146013 := bstep (se 3 (by rfl) ⟨5464877, by rfl⟩ : syracuseStep 29146013 = 10929755) B10929755
theorem B3194441 : Blo 1419529 3194441 := bstep (se 2 (by rfl) ⟨1197915, by rfl⟩ : syracuseStep 3194441 = 2395831) B2395831
theorem B2129567 : Blo 1419529 2129567 := bstep (se 1 (by rfl) ⟨1597175, by rfl⟩ : syracuseStep 2129567 = 3194351) B3194351
theorem B10788713 : Blo 1419529 10788713 := bstep (se 2 (by rfl) ⟨4045767, by rfl⟩ : syracuseStep 10788713 = 8091535) B8091535
theorem B2130623 : Blo 1419529 2130623 := bstep (se 1 (by rfl) ⟨1597967, by rfl⟩ : syracuseStep 2130623 = 3195935) B3195935
theorem B40968935 : Blo 1419529 40968935 := bstep (se 1 (by rfl) ⟨30726701, by rfl⟩ : syracuseStep 40968935 = 61453403) B61453403
theorem B1419711 : Blo 1419529 1419711 := bstep (se 1 (by rfl) ⟨1064783, by rfl⟩ : syracuseStep 1419711 = 2129567) B2129567
theorem B4795199 : Blo 1419529 4795199 := bstep (se 1 (by rfl) ⟨3596399, by rfl⟩ : syracuseStep 4795199 = 7192799) B7192799
theorem B1421159 : Blo 1419529 1421159 := bstep (se 1 (by rfl) ⟨1065869, by rfl⟩ : syracuseStep 1421159 = 2131739) B2131739
theorem B8638559 : Blo 1419529 8638559 := bstep (se 1 (by rfl) ⟨6478919, by rfl⟩ : syracuseStep 8638559 = 12957839) B12957839
theorem B52514963 : Blo 1419529 52514963 := bstep (se 1 (by rfl) ⟨39386222, by rfl⟩ : syracuseStep 52514963 = 78772445) B78772445
theorem B2398315 : Blo 1419529 2398315 := bstep (se 1 (by rfl) ⟨1798736, by rfl⟩ : syracuseStep 2398315 = 3597473) B3597473
theorem B170580107 : Blo 1419529 170580107 := bstep (se 1 (by rfl) ⟨127935080, by rfl⟩ : syracuseStep 170580107 = 255870161) B255870161
theorem B19430675 : Blo 1419529 19430675 := bstep (se 1 (by rfl) ⟨14573006, by rfl⟩ : syracuseStep 19430675 = 29146013) B29146013
theorem B2129627 : Blo 1419529 2129627 := bstep (se 1 (by rfl) ⟨1597220, by rfl⟩ : syracuseStep 2129627 = 3194441) B3194441
theorem B7192475 : Blo 1419529 7192475 := bstep (se 1 (by rfl) ⟨5394356, by rfl⟩ : syracuseStep 7192475 = 10788713) B10788713
theorem B5759039 : Blo 1419529 5759039 := bstep (se 1 (by rfl) ⟨4319279, by rfl⟩ : syracuseStep 5759039 = 8638559) B8638559
theorem B27312623 : Blo 1419529 27312623 := bstep (se 1 (by rfl) ⟨20484467, by rfl⟩ : syracuseStep 27312623 = 40968935) B40968935
theorem B3196799 : Blo 1419529 3196799 := bstep (se 1 (by rfl) ⟨2397599, by rfl⟩ : syracuseStep 3196799 = 4795199) B4795199
theorem B12953783 : Blo 1419529 12953783 := bstep (se 1 (by rfl) ⟨9715337, by rfl⟩ : syracuseStep 12953783 = 19430675) B19430675
theorem B1419751 : Blo 1419529 1419751 := bstep (se 1 (by rfl) ⟨1064813, by rfl⟩ : syracuseStep 1419751 = 2129627) B2129627
theorem B4794983 : Blo 1419529 4794983 := bstep (se 1 (by rfl) ⟨3596237, by rfl⟩ : syracuseStep 4794983 = 7192475) B7192475
theorem B3197753 : Blo 1419529 3197753 := bstep (se 2 (by rfl) ⟨1199157, by rfl⟩ : syracuseStep 3197753 = 2398315) B2398315
theorem B1420415 : Blo 1419529 1420415 := bstep (se 1 (by rfl) ⟨1065311, by rfl⟩ : syracuseStep 1420415 = 2130623) B2130623
theorem B35009975 : Blo 1419529 35009975 := bstep (se 1 (by rfl) ⟨26257481, by rfl⟩ : syracuseStep 35009975 = 52514963) B52514963
theorem B113720071 : Blo 1419529 113720071 := bstep (se 1 (by rfl) ⟨85290053, by rfl⟩ : syracuseStep 113720071 = 170580107) B170580107
theorem B23339983 : Blo 1419529 23339983 := bstep (se 1 (by rfl) ⟨17504987, by rfl⟩ : syracuseStep 23339983 = 35009975) B35009975
theorem B151626761 : Blo 1419529 151626761 := bstep (se 2 (by rfl) ⟨56860035, by rfl⟩ : syracuseStep 151626761 = 113720071) B113720071
theorem B2131199 : Blo 1419529 2131199 := bstep (se 1 (by rfl) ⟨1598399, by rfl⟩ : syracuseStep 2131199 = 3196799) B3196799
theorem B8635855 : Blo 1419529 8635855 := bstep (se 1 (by rfl) ⟨6476891, by rfl⟩ : syracuseStep 8635855 = 12953783) B12953783
theorem B3196655 : Blo 1419529 3196655 := bstep (se 1 (by rfl) ⟨2397491, by rfl⟩ : syracuseStep 3196655 = 4794983) B4794983
theorem B2131835 : Blo 1419529 2131835 := bstep (se 1 (by rfl) ⟨1598876, by rfl⟩ : syracuseStep 2131835 = 3197753) B3197753
theorem B3839359 : Blo 1419529 3839359 := bstep (se 1 (by rfl) ⟨2879519, by rfl⟩ : syracuseStep 3839359 = 5759039) B5759039
theorem B18208415 : Blo 1419529 18208415 := bstep (se 1 (by rfl) ⟨13656311, by rfl⟩ : syracuseStep 18208415 = 27312623) B27312623
theorem B2131103 : Blo 1419529 2131103 := bstep (se 1 (by rfl) ⟨1598327, by rfl⟩ : syracuseStep 2131103 = 3196655) B3196655
theorem B101084507 : Blo 1419529 101084507 := bstep (se 1 (by rfl) ⟨75813380, by rfl⟩ : syracuseStep 101084507 = 151626761) B151626761
theorem B1420799 : Blo 1419529 1420799 := bstep (se 1 (by rfl) ⟨1065599, by rfl⟩ : syracuseStep 1420799 = 2131199) B2131199
theorem B1421223 : Blo 1419529 1421223 := bstep (se 1 (by rfl) ⟨1065917, by rfl⟩ : syracuseStep 1421223 = 2131835) B2131835
theorem B11514473 : Blo 1419529 11514473 := bstep (se 2 (by rfl) ⟨4317927, by rfl⟩ : syracuseStep 11514473 = 8635855) B8635855
theorem B12138943 : Blo 1419529 12138943 := bstep (se 1 (by rfl) ⟨9104207, by rfl⟩ : syracuseStep 12138943 = 18208415) B18208415
theorem B31119977 : Blo 1419529 31119977 := bstep (se 2 (by rfl) ⟨11669991, by rfl⟩ : syracuseStep 31119977 = 23339983) B23339983
theorem B5119145 : Blo 1419529 5119145 := bstep (se 2 (by rfl) ⟨1919679, by rfl⟩ : syracuseStep 5119145 = 3839359) B3839359
theorem B7676315 : Blo 1419529 7676315 := bstep (se 1 (by rfl) ⟨5757236, by rfl⟩ : syracuseStep 7676315 = 11514473) B11514473
theorem B82986605 : Blo 1419529 82986605 := bstep (se 3 (by rfl) ⟨15559988, by rfl⟩ : syracuseStep 82986605 = 31119977) B31119977
theorem B67389671 : Blo 1419529 67389671 := bstep (se 1 (by rfl) ⟨50542253, by rfl⟩ : syracuseStep 67389671 = 101084507) B101084507
theorem B1420735 : Blo 1419529 1420735 := bstep (se 1 (by rfl) ⟨1065551, by rfl⟩ : syracuseStep 1420735 = 2131103) B2131103
theorem B3412763 : Blo 1419529 3412763 := bstep (se 1 (by rfl) ⟨2559572, by rfl⟩ : syracuseStep 3412763 = 5119145) B5119145
theorem B16185257 : Blo 1419529 16185257 := bstep (se 2 (by rfl) ⟨6069471, by rfl⟩ : syracuseStep 16185257 = 12138943) B12138943
theorem B10790171 : Blo 1419529 10790171 := bstep (se 1 (by rfl) ⟨8092628, by rfl⟩ : syracuseStep 10790171 = 16185257) B16185257
theorem B55324403 : Blo 1419529 55324403 := bstep (se 1 (by rfl) ⟨41493302, by rfl⟩ : syracuseStep 55324403 = 82986605) B82986605
theorem B5117543 : Blo 1419529 5117543 := bstep (se 1 (by rfl) ⟨3838157, by rfl⟩ : syracuseStep 5117543 = 7676315) B7676315
theorem B2275175 : Blo 1419529 2275175 := bstep (se 1 (by rfl) ⟨1706381, by rfl⟩ : syracuseStep 2275175 = 3412763) B3412763
theorem B179705789 : Blo 1419529 179705789 := bstep (se 3 (by rfl) ⟨33694835, by rfl⟩ : syracuseStep 179705789 = 67389671) B67389671
theorem B7193447 : Blo 1419529 7193447 := bstep (se 1 (by rfl) ⟨5395085, by rfl⟩ : syracuseStep 7193447 = 10790171) B10790171
theorem B36882935 : Blo 1419529 36882935 := bstep (se 1 (by rfl) ⟨27662201, by rfl⟩ : syracuseStep 36882935 = 55324403) B55324403
theorem B3411695 : Blo 1419529 3411695 := bstep (se 1 (by rfl) ⟨2558771, by rfl⟩ : syracuseStep 3411695 = 5117543) B5117543
theorem B119803859 : Blo 1419529 119803859 := bstep (se 1 (by rfl) ⟨89852894, by rfl⟩ : syracuseStep 119803859 = 179705789) B179705789
theorem B6067133 : Blo 1419529 6067133 := bstep (se 3 (by rfl) ⟨1137587, by rfl⟩ : syracuseStep 6067133 = 2275175) B2275175
theorem B4795631 : Blo 1419529 4795631 := bstep (se 1 (by rfl) ⟨3596723, by rfl⟩ : syracuseStep 4795631 = 7193447) B7193447
theorem B24588623 : Blo 1419529 24588623 := bstep (se 1 (by rfl) ⟨18441467, by rfl⟩ : syracuseStep 24588623 = 36882935) B36882935
theorem B2274463 : Blo 1419529 2274463 := bstep (se 1 (by rfl) ⟨1705847, by rfl⟩ : syracuseStep 2274463 = 3411695) B3411695
theorem B79869239 : Blo 1419529 79869239 := bstep (se 1 (by rfl) ⟨59901929, by rfl⟩ : syracuseStep 79869239 = 119803859) B119803859
theorem B4044755 : Blo 1419529 4044755 := bstep (se 1 (by rfl) ⟨3033566, by rfl⟩ : syracuseStep 4044755 = 6067133) B6067133
theorem B16392415 : Blo 1419529 16392415 := bstep (se 1 (by rfl) ⟨12294311, by rfl⟩ : syracuseStep 16392415 = 24588623) B24588623
theorem B2696503 : Blo 1419529 2696503 := bstep (se 1 (by rfl) ⟨2022377, by rfl⟩ : syracuseStep 2696503 = 4044755) B4044755
theorem B3197087 : Blo 1419529 3197087 := bstep (se 1 (by rfl) ⟨2397815, by rfl⟩ : syracuseStep 3197087 = 4795631) B4795631
theorem B12130469 : Blo 1419529 12130469 := bstep (se 4 (by rfl) ⟨1137231, by rfl⟩ : syracuseStep 12130469 = 2274463) B2274463
theorem B53246159 : Blo 1419529 53246159 := bstep (se 1 (by rfl) ⟨39934619, by rfl⟩ : syracuseStep 53246159 = 79869239) B79869239
theorem B21856553 : Blo 1419529 21856553 := bstep (se 2 (by rfl) ⟨8196207, by rfl⟩ : syracuseStep 21856553 = 16392415) B16392415
theorem B2131391 : Blo 1419529 2131391 := bstep (se 1 (by rfl) ⟨1598543, by rfl⟩ : syracuseStep 2131391 = 3197087) B3197087
theorem B8086979 : Blo 1419529 8086979 := bstep (se 1 (by rfl) ⟨6065234, by rfl⟩ : syracuseStep 8086979 = 12130469) B12130469
theorem B35497439 : Blo 1419529 35497439 := bstep (se 1 (by rfl) ⟨26623079, by rfl⟩ : syracuseStep 35497439 = 53246159) B53246159
theorem B3595337 : Blo 1419529 3595337 := bstep (se 2 (by rfl) ⟨1348251, by rfl⟩ : syracuseStep 3595337 = 2696503) B2696503
theorem B5391319 : Blo 1419529 5391319 := bstep (se 1 (by rfl) ⟨4043489, by rfl⟩ : syracuseStep 5391319 = 8086979) B8086979
theorem B1420927 : Blo 1419529 1420927 := bstep (se 1 (by rfl) ⟨1065695, by rfl⟩ : syracuseStep 1420927 = 2131391) B2131391
theorem B2396891 : Blo 1419529 2396891 := bstep (se 1 (by rfl) ⟨1797668, by rfl⟩ : syracuseStep 2396891 = 3595337) B3595337
theorem B14571035 : Blo 1419529 14571035 := bstep (se 1 (by rfl) ⟨10928276, by rfl⟩ : syracuseStep 14571035 = 21856553) B21856553
theorem B23664959 : Blo 1419529 23664959 := bstep (se 1 (by rfl) ⟨17748719, by rfl⟩ : syracuseStep 23664959 = 35497439) B35497439
theorem B1597927 : Blo 1419529 1597927 := bstep (se 1 (by rfl) ⟨1198445, by rfl⟩ : syracuseStep 1597927 = 2396891) B2396891
theorem B7188425 : Blo 1419529 7188425 := bstep (se 2 (by rfl) ⟨2695659, by rfl⟩ : syracuseStep 7188425 = 5391319) B5391319
theorem B9714023 : Blo 1419529 9714023 := bstep (se 1 (by rfl) ⟨7285517, by rfl⟩ : syracuseStep 9714023 = 14571035) B14571035
theorem B15776639 : Blo 1419529 15776639 := bstep (se 1 (by rfl) ⟨11832479, by rfl⟩ : syracuseStep 15776639 = 23664959) B23664959
theorem B2130569 : Blo 1419529 2130569 := bstep (se 2 (by rfl) ⟨798963, by rfl⟩ : syracuseStep 2130569 = 1597927) B1597927
theorem B6476015 : Blo 1419529 6476015 := bstep (se 1 (by rfl) ⟨4857011, by rfl⟩ : syracuseStep 6476015 = 9714023) B9714023
theorem B10517759 : Blo 1419529 10517759 := bstep (se 1 (by rfl) ⟨7888319, by rfl⟩ : syracuseStep 10517759 = 15776639) B15776639
theorem B4792283 : Blo 1419529 4792283 := bstep (se 1 (by rfl) ⟨3594212, by rfl⟩ : syracuseStep 4792283 = 7188425) B7188425
theorem B4317343 : Blo 1419529 4317343 := bstep (se 1 (by rfl) ⟨3238007, by rfl⟩ : syracuseStep 4317343 = 6476015) B6476015
theorem B1420379 : Blo 1419529 1420379 := bstep (se 1 (by rfl) ⟨1065284, by rfl⟩ : syracuseStep 1420379 = 2130569) B2130569
theorem B7011839 : Blo 1419529 7011839 := bstep (se 1 (by rfl) ⟨5258879, by rfl⟩ : syracuseStep 7011839 = 10517759) B10517759
theorem B3194855 : Blo 1419529 3194855 := bstep (se 1 (by rfl) ⟨2396141, by rfl⟩ : syracuseStep 3194855 = 4792283) B4792283
theorem B4674559 : Blo 1419529 4674559 := bstep (se 1 (by rfl) ⟨3505919, by rfl⟩ : syracuseStep 4674559 = 7011839) B7011839
theorem B23025829 : Blo 1419529 23025829 := bstep (se 4 (by rfl) ⟨2158671, by rfl⟩ : syracuseStep 23025829 = 4317343) B4317343
theorem B2129903 : Blo 1419529 2129903 := bstep (se 1 (by rfl) ⟨1597427, by rfl⟩ : syracuseStep 2129903 = 3194855) B3194855
theorem B1419935 : Blo 1419529 1419935 := bstep (se 1 (by rfl) ⟨1064951, by rfl⟩ : syracuseStep 1419935 = 2129903) B2129903
theorem B30701105 : Blo 1419529 30701105 := bstep (se 2 (by rfl) ⟨11512914, by rfl⟩ : syracuseStep 30701105 = 23025829) B23025829
theorem B6232745 : Blo 1419529 6232745 := bstep (se 2 (by rfl) ⟨2337279, by rfl⟩ : syracuseStep 6232745 = 4674559) B4674559
theorem B20467403 : Blo 1419529 20467403 := bstep (se 1 (by rfl) ⟨15350552, by rfl⟩ : syracuseStep 20467403 = 30701105) B30701105
theorem B16620653 : Blo 1419529 16620653 := bstep (se 3 (by rfl) ⟨3116372, by rfl⟩ : syracuseStep 16620653 = 6232745) B6232745
theorem B44321741 : Blo 1419529 44321741 := bstep (se 3 (by rfl) ⟨8310326, by rfl⟩ : syracuseStep 44321741 = 16620653) B16620653
theorem B13644935 : Blo 1419529 13644935 := bstep (se 1 (by rfl) ⟨10233701, by rfl⟩ : syracuseStep 13644935 = 20467403) B20467403
theorem B9096623 : Blo 1419529 9096623 := bstep (se 1 (by rfl) ⟨6822467, by rfl⟩ : syracuseStep 9096623 = 13644935) B13644935
theorem B29547827 : Blo 1419529 29547827 := bstep (se 1 (by rfl) ⟨22160870, by rfl⟩ : syracuseStep 29547827 = 44321741) B44321741
theorem B6064415 : Blo 1419529 6064415 := bstep (se 1 (by rfl) ⟨4548311, by rfl⟩ : syracuseStep 6064415 = 9096623) B9096623
theorem B19698551 : Blo 1419529 19698551 := bstep (se 1 (by rfl) ⟨14773913, by rfl⟩ : syracuseStep 19698551 = 29547827) B29547827
theorem B13132367 : Blo 1419529 13132367 := bstep (se 1 (by rfl) ⟨9849275, by rfl⟩ : syracuseStep 13132367 = 19698551) B19698551
theorem B4042943 : Blo 1419529 4042943 := bstep (se 1 (by rfl) ⟨3032207, by rfl⟩ : syracuseStep 4042943 = 6064415) B6064415
theorem B2695295 : Blo 1419529 2695295 := bstep (se 1 (by rfl) ⟨2021471, by rfl⟩ : syracuseStep 2695295 = 4042943) B4042943
theorem B8754911 : Blo 1419529 8754911 := bstep (se 1 (by rfl) ⟨6566183, by rfl⟩ : syracuseStep 8754911 = 13132367) B13132367
theorem B7187453 : Blo 1419529 7187453 := bstep (se 3 (by rfl) ⟨1347647, by rfl⟩ : syracuseStep 7187453 = 2695295) B2695295
theorem B5836607 : Blo 1419529 5836607 := bstep (se 1 (by rfl) ⟨4377455, by rfl⟩ : syracuseStep 5836607 = 8754911) B8754911
theorem B4791635 : Blo 1419529 4791635 := bstep (se 1 (by rfl) ⟨3593726, by rfl⟩ : syracuseStep 4791635 = 7187453) B7187453
theorem B3891071 : Blo 1419529 3891071 := bstep (se 1 (by rfl) ⟨2918303, by rfl⟩ : syracuseStep 3891071 = 5836607) B5836607
theorem B10376189 : Blo 1419529 10376189 := bstep (se 3 (by rfl) ⟨1945535, by rfl⟩ : syracuseStep 10376189 = 3891071) B3891071
theorem B3194423 : Blo 1419529 3194423 := bstep (se 1 (by rfl) ⟨2395817, by rfl⟩ : syracuseStep 3194423 = 4791635) B4791635
theorem B6917459 : Blo 1419529 6917459 := bstep (se 1 (by rfl) ⟨5188094, by rfl⟩ : syracuseStep 6917459 = 10376189) B10376189
theorem B2129615 : Blo 1419529 2129615 := bstep (se 1 (by rfl) ⟨1597211, by rfl⟩ : syracuseStep 2129615 = 3194423) B3194423
theorem B1419743 : Blo 1419529 1419743 := bstep (se 1 (by rfl) ⟨1064807, by rfl⟩ : syracuseStep 1419743 = 2129615) B2129615
theorem B18446557 : Blo 1419529 18446557 := bstep (se 3 (by rfl) ⟨3458729, by rfl⟩ : syracuseStep 18446557 = 6917459) B6917459
theorem B24595409 : Blo 1419529 24595409 := bstep (se 2 (by rfl) ⟨9223278, by rfl⟩ : syracuseStep 24595409 = 18446557) B18446557
theorem B16396939 : Blo 1419529 16396939 := bstep (se 1 (by rfl) ⟨12297704, by rfl⟩ : syracuseStep 16396939 = 24595409) B24595409
theorem B21862585 : Blo 1419529 21862585 := bstep (se 2 (by rfl) ⟨8198469, by rfl⟩ : syracuseStep 21862585 = 16396939) B16396939
theorem B29150113 : Blo 1419529 29150113 := bstep (se 2 (by rfl) ⟨10931292, by rfl⟩ : syracuseStep 29150113 = 21862585) B21862585
theorem B38866817 : Blo 1419529 38866817 := bstep (se 2 (by rfl) ⟨14575056, by rfl⟩ : syracuseStep 38866817 = 29150113) B29150113
theorem B25911211 : Blo 1419529 25911211 := bstep (se 1 (by rfl) ⟨19433408, by rfl⟩ : syracuseStep 25911211 = 38866817) B38866817
theorem B34548281 : Blo 1419529 34548281 := bstep (se 2 (by rfl) ⟨12955605, by rfl⟩ : syracuseStep 34548281 = 25911211) B25911211
theorem B23032187 : Blo 1419529 23032187 := bstep (se 1 (by rfl) ⟨17274140, by rfl⟩ : syracuseStep 23032187 = 34548281) B34548281
theorem B15354791 : Blo 1419529 15354791 := bstep (se 1 (by rfl) ⟨11516093, by rfl⟩ : syracuseStep 15354791 = 23032187) B23032187
theorem B10236527 : Blo 1419529 10236527 := bstep (se 1 (by rfl) ⟨7677395, by rfl⟩ : syracuseStep 10236527 = 15354791) B15354791
theorem B6824351 : Blo 1419529 6824351 := bstep (se 1 (by rfl) ⟨5118263, by rfl⟩ : syracuseStep 6824351 = 10236527) B10236527
theorem B18198269 : Blo 1419529 18198269 := bstep (se 3 (by rfl) ⟨3412175, by rfl⟩ : syracuseStep 18198269 = 6824351) B6824351
theorem B12132179 : Blo 1419529 12132179 := bstep (se 1 (by rfl) ⟨9099134, by rfl⟩ : syracuseStep 12132179 = 18198269) B18198269
theorem B8088119 : Blo 1419529 8088119 := bstep (se 1 (by rfl) ⟨6066089, by rfl⟩ : syracuseStep 8088119 = 12132179) B12132179
theorem B5392079 : Blo 1419529 5392079 := bstep (se 1 (by rfl) ⟨4044059, by rfl⟩ : syracuseStep 5392079 = 8088119) B8088119
theorem B3594719 : Blo 1419529 3594719 := bstep (se 1 (by rfl) ⟨2696039, by rfl⟩ : syracuseStep 3594719 = 5392079) B5392079
theorem B2396479 : Blo 1419529 2396479 := bstep (se 1 (by rfl) ⟨1797359, by rfl⟩ : syracuseStep 2396479 = 3594719) B3594719
theorem B3195305 : Blo 1419529 3195305 := bstep (se 2 (by rfl) ⟨1198239, by rfl⟩ : syracuseStep 3195305 = 2396479) B2396479
theorem B2130203 : Blo 1419529 2130203 := bstep (se 1 (by rfl) ⟨1597652, by rfl⟩ : syracuseStep 2130203 = 3195305) B3195305
theorem B1420135 : Blo 1419529 1420135 := bstep (se 1 (by rfl) ⟨1065101, by rfl⟩ : syracuseStep 1420135 = 2130203) B2130203

theorem C0 (j : ℕ) (h1 : 354882 ≤ j) (h2 : j ≤ 355381) : Blo 1419529 (4 * j + 3) := by
  interval_cases j
  · exact B1419531
  · exact B1419535
  · exact B1419539
  · exact B1419543
  · exact B1419547
  · exact B1419551
  · exact B1419555
  · exact B1419559
  · exact B1419563
  · exact B1419567
  · exact B1419571
  · exact B1419575
  · exact B1419579
  · exact B1419583
  · exact B1419587
  · exact B1419591
  · exact B1419595
  · exact B1419599
  · exact B1419603
  · exact B1419607
  · exact B1419611
  · exact B1419615
  · exact B1419619
  · exact B1419623
  · exact B1419627
  · exact B1419631
  · exact B1419635
  · exact B1419639
  · exact B1419643
  · exact B1419647
  · exact B1419651
  · exact B1419655
  · exact B1419659
  · exact B1419663
  · exact B1419667
  · exact B1419671
  · exact B1419675
  · exact B1419679
  · exact B1419683
  · exact B1419687
  · exact B1419691
  · exact B1419695
  · exact B1419699
  · exact B1419703
  · exact B1419707
  · exact B1419711
  · exact B1419715
  · exact B1419719
  · exact B1419723
  · exact B1419727
  · exact B1419731
  · exact B1419735
  · exact B1419739
  · exact B1419743
  · exact B1419747
  · exact B1419751
  · exact B1419755
  · exact B1419759
  · exact B1419763
  · exact B1419767
  · exact B1419771
  · exact B1419775
  · exact B1419779
  · exact B1419783
  · exact B1419787
  · exact B1419791
  · exact B1419795
  · exact B1419799
  · exact B1419803
  · exact B1419807
  · exact B1419811
  · exact B1419815
  · exact B1419819
  · exact B1419823
  · exact B1419827
  · exact B1419831
  · exact B1419835
  · exact B1419839
  · exact B1419843
  · exact B1419847
  · exact B1419851
  · exact B1419855
  · exact B1419859
  · exact B1419863
  · exact B1419867
  · exact B1419871
  · exact B1419875
  · exact B1419879
  · exact B1419883
  · exact B1419887
  · exact B1419891
  · exact B1419895
  · exact B1419899
  · exact B1419903
  · exact B1419907
  · exact B1419911
  · exact B1419915
  · exact B1419919
  · exact B1419923
  · exact B1419927
  · exact B1419931
  · exact B1419935
  · exact B1419939
  · exact B1419943
  · exact B1419947
  · exact B1419951
  · exact B1419955
  · exact B1419959
  · exact B1419963
  · exact B1419967
  · exact B1419971
  · exact B1419975
  · exact B1419979
  · exact B1419983
  · exact B1419987
  · exact B1419991
  · exact B1419995
  · exact B1419999
  · exact B1420003
  · exact B1420007
  · exact B1420011
  · exact B1420015
  · exact B1420019
  · exact B1420023
  · exact B1420027
  · exact B1420031
  · exact B1420035
  · exact B1420039
  · exact B1420043
  · exact B1420047
  · exact B1420051
  · exact B1420055
  · exact B1420059
  · exact B1420063
  · exact B1420067
  · exact B1420071
  · exact B1420075
  · exact B1420079
  · exact B1420083
  · exact B1420087
  · exact B1420091
  · exact B1420095
  · exact B1420099
  · exact B1420103
  · exact B1420107
  · exact B1420111
  · exact B1420115
  · exact B1420119
  · exact B1420123
  · exact B1420127
  · exact B1420131
  · exact B1420135
  · exact B1420139
  · exact B1420143
  · exact B1420147
  · exact B1420151
  · exact B1420155
  · exact B1420159
  · exact B1420163
  · exact B1420167
  · exact B1420171
  · exact B1420175
  · exact B1420179
  · exact B1420183
  · exact B1420187
  · exact B1420191
  · exact B1420195
  · exact B1420199
  · exact B1420203
  · exact B1420207
  · exact B1420211
  · exact B1420215
  · exact B1420219
  · exact B1420223
  · exact B1420227
  · exact B1420231
  · exact B1420235
  · exact B1420239
  · exact B1420243
  · exact B1420247
  · exact B1420251
  · exact B1420255
  · exact B1420259
  · exact B1420263
  · exact B1420267
  · exact B1420271
  · exact B1420275
  · exact B1420279
  · exact B1420283
  · exact B1420287
  · exact B1420291
  · exact B1420295
  · exact B1420299
  · exact B1420303
  · exact B1420307
  · exact B1420311
  · exact B1420315
  · exact B1420319
  · exact B1420323
  · exact B1420327
  · exact B1420331
  · exact B1420335
  · exact B1420339
  · exact B1420343
  · exact B1420347
  · exact B1420351
  · exact B1420355
  · exact B1420359
  · exact B1420363
  · exact B1420367
  · exact B1420371
  · exact B1420375
  · exact B1420379
  · exact B1420383
  · exact B1420387
  · exact B1420391
  · exact B1420395
  · exact B1420399
  · exact B1420403
  · exact B1420407
  · exact B1420411
  · exact B1420415
  · exact B1420419
  · exact B1420423
  · exact B1420427
  · exact B1420431
  · exact B1420435
  · exact B1420439
  · exact B1420443
  · exact B1420447
  · exact B1420451
  · exact B1420455
  · exact B1420459
  · exact B1420463
  · exact B1420467
  · exact B1420471
  · exact B1420475
  · exact B1420479
  · exact B1420483
  · exact B1420487
  · exact B1420491
  · exact B1420495
  · exact B1420499
  · exact B1420503
  · exact B1420507
  · exact B1420511
  · exact B1420515
  · exact B1420519
  · exact B1420523
  · exact B1420527
  · exact B1420531
  · exact B1420535
  · exact B1420539
  · exact B1420543
  · exact B1420547
  · exact B1420551
  · exact B1420555
  · exact B1420559
  · exact B1420563
  · exact B1420567
  · exact B1420571
  · exact B1420575
  · exact B1420579
  · exact B1420583
  · exact B1420587
  · exact B1420591
  · exact B1420595
  · exact B1420599
  · exact B1420603
  · exact B1420607
  · exact B1420611
  · exact B1420615
  · exact B1420619
  · exact B1420623
  · exact B1420627
  · exact B1420631
  · exact B1420635
  · exact B1420639
  · exact B1420643
  · exact B1420647
  · exact B1420651
  · exact B1420655
  · exact B1420659
  · exact B1420663
  · exact B1420667
  · exact B1420671
  · exact B1420675
  · exact B1420679
  · exact B1420683
  · exact B1420687
  · exact B1420691
  · exact B1420695
  · exact B1420699
  · exact B1420703
  · exact B1420707
  · exact B1420711
  · exact B1420715
  · exact B1420719
  · exact B1420723
  · exact B1420727
  · exact B1420731
  · exact B1420735
  · exact B1420739
  · exact B1420743
  · exact B1420747
  · exact B1420751
  · exact B1420755
  · exact B1420759
  · exact B1420763
  · exact B1420767
  · exact B1420771
  · exact B1420775
  · exact B1420779
  · exact B1420783
  · exact B1420787
  · exact B1420791
  · exact B1420795
  · exact B1420799
  · exact B1420803
  · exact B1420807
  · exact B1420811
  · exact B1420815
  · exact B1420819
  · exact B1420823
  · exact B1420827
  · exact B1420831
  · exact B1420835
  · exact B1420839
  · exact B1420843
  · exact B1420847
  · exact B1420851
  · exact B1420855
  · exact B1420859
  · exact B1420863
  · exact B1420867
  · exact B1420871
  · exact B1420875
  · exact B1420879
  · exact B1420883
  · exact B1420887
  · exact B1420891
  · exact B1420895
  · exact B1420899
  · exact B1420903
  · exact B1420907
  · exact B1420911
  · exact B1420915
  · exact B1420919
  · exact B1420923
  · exact B1420927
  · exact B1420931
  · exact B1420935
  · exact B1420939
  · exact B1420943
  · exact B1420947
  · exact B1420951
  · exact B1420955
  · exact B1420959
  · exact B1420963
  · exact B1420967
  · exact B1420971
  · exact B1420975
  · exact B1420979
  · exact B1420983
  · exact B1420987
  · exact B1420991
  · exact B1420995
  · exact B1420999
  · exact B1421003
  · exact B1421007
  · exact B1421011
  · exact B1421015
  · exact B1421019
  · exact B1421023
  · exact B1421027
  · exact B1421031
  · exact B1421035
  · exact B1421039
  · exact B1421043
  · exact B1421047
  · exact B1421051
  · exact B1421055
  · exact B1421059
  · exact B1421063
  · exact B1421067
  · exact B1421071
  · exact B1421075
  · exact B1421079
  · exact B1421083
  · exact B1421087
  · exact B1421091
  · exact B1421095
  · exact B1421099
  · exact B1421103
  · exact B1421107
  · exact B1421111
  · exact B1421115
  · exact B1421119
  · exact B1421123
  · exact B1421127
  · exact B1421131
  · exact B1421135
  · exact B1421139
  · exact B1421143
  · exact B1421147
  · exact B1421151
  · exact B1421155
  · exact B1421159
  · exact B1421163
  · exact B1421167
  · exact B1421171
  · exact B1421175
  · exact B1421179
  · exact B1421183
  · exact B1421187
  · exact B1421191
  · exact B1421195
  · exact B1421199
  · exact B1421203
  · exact B1421207
  · exact B1421211
  · exact B1421215
  · exact B1421219
  · exact B1421223
  · exact B1421227
  · exact B1421231
  · exact B1421235
  · exact B1421239
  · exact B1421243
  · exact B1421247
  · exact B1421251
  · exact B1421255
  · exact B1421259
  · exact B1421263
  · exact B1421267
  · exact B1421271
  · exact B1421275
  · exact B1421279
  · exact B1421283
  · exact B1421287
  · exact B1421291
  · exact B1421295
  · exact B1421299
  · exact B1421303
  · exact B1421307
  · exact B1421311
  · exact B1421315
  · exact B1421319
  · exact B1421323
  · exact B1421327
  · exact B1421331
  · exact B1421335
  · exact B1421339
  · exact B1421343
  · exact B1421347
  · exact B1421351
  · exact B1421355
  · exact B1421359
  · exact B1421363
  · exact B1421367
  · exact B1421371
  · exact B1421375
  · exact B1421379
  · exact B1421383
  · exact B1421387
  · exact B1421391
  · exact B1421395
  · exact B1421399
  · exact B1421403
  · exact B1421407
  · exact B1421411
  · exact B1421415
  · exact B1421419
  · exact B1421423
  · exact B1421427
  · exact B1421431
  · exact B1421435
  · exact B1421439
  · exact B1421443
  · exact B1421447
  · exact B1421451
  · exact B1421455
  · exact B1421459
  · exact B1421463
  · exact B1421467
  · exact B1421471
  · exact B1421475
  · exact B1421479
  · exact B1421483
  · exact B1421487
  · exact B1421491
  · exact B1421495
  · exact B1421499
  · exact B1421503
  · exact B1421507
  · exact B1421511
  · exact B1421515
  · exact B1421519
  · exact B1421523
  · exact B1421527

theorem solution (m : ℕ) (hlo : 1419529 ≤ m) (hhi : m ≤ 1421529) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 354882 ≤ j := by omega
    have hj2 : j ≤ 355381 := by omega
    have hb : Blo 1419529 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
