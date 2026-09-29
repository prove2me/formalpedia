-- Prove2me | solution 1 for syracuse_descends_range_896573_900573
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:21:47.98882+00:00
-- url     : https://prove2.me/submissions/c2b9eff9-5ffd-4e69-97fa-9373f6adce01

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


theorem B1081369 : Blo 896573 1081369 := bbase (se 2 (by rfl) ⟨405513, by rfl⟩ : syracuseStep 1081369 = 811027) (by norm_num)
theorem B1704053 : Blo 896573 1704053 := bbase (se 5 (by rfl) ⟨79877, by rfl⟩ : syracuseStep 1704053 = 159755) (by norm_num)
theorem B6816149 : Blo 896573 6816149 := bbase (se 6 (by rfl) ⟨159753, by rfl⟩ : syracuseStep 6816149 = 319507) (by norm_num)
theorem B1704341 : Blo 896573 1704341 := bbase (se 6 (by rfl) ⟨39945, by rfl⟩ : syracuseStep 1704341 = 79891) (by norm_num)
theorem B2916773 : Blo 896573 2916773 := bbase (se 4 (by rfl) ⟨273447, by rfl⟩ : syracuseStep 2916773 = 546895) (by norm_num)
theorem B1278461 : Blo 896573 1278461 := bbase (se 3 (by rfl) ⟨239711, by rfl⟩ : syracuseStep 1278461 = 479423) (by norm_num)
theorem B2425349 : Blo 896573 2425349 := bbase (se 4 (by rfl) ⟨227376, by rfl⟩ : syracuseStep 2425349 = 454753) (by norm_num)
theorem B5112341 : Blo 896573 5112341 := bbase (se 6 (by rfl) ⟨119820, by rfl⟩ : syracuseStep 5112341 = 239641) (by norm_num)
theorem B1704493 : Blo 896573 1704493 := bbase (se 3 (by rfl) ⟨319592, by rfl⟩ : syracuseStep 1704493 = 639185) (by norm_num)
theorem B1278541 : Blo 896573 1278541 := bbase (se 3 (by rfl) ⟨239726, by rfl⟩ : syracuseStep 1278541 = 479453) (by norm_num)
theorem B2163277 : Blo 896573 2163277 := bbase (se 3 (by rfl) ⟨405614, by rfl⟩ : syracuseStep 2163277 = 811229) (by norm_num)
theorem B1278661 : Blo 896573 1278661 := bbase (se 4 (by rfl) ⟨119874, by rfl⟩ : syracuseStep 1278661 = 239749) (by norm_num)
theorem B2425589 : Blo 896573 2425589 := bbase (se 5 (by rfl) ⟨113699, by rfl⟩ : syracuseStep 2425589 = 227399) (by norm_num)
theorem B4326149 : Blo 896573 4326149 := bbase (se 4 (by rfl) ⟨405576, by rfl⟩ : syracuseStep 4326149 = 811153) (by norm_num)
theorem B1278757 : Blo 896573 1278757 := bbase (se 4 (by rfl) ⟨119883, by rfl⟩ : syracuseStep 1278757 = 239767) (by norm_num)
theorem B1704797 : Blo 896573 1704797 := bbase (se 3 (by rfl) ⟨319649, by rfl⟩ : syracuseStep 1704797 = 639299) (by norm_num)
theorem B4555925 : Blo 896573 4555925 := bbase (se 6 (by rfl) ⟨106779, by rfl⟩ : syracuseStep 4555925 = 213559) (by norm_num)
theorem B2426021 : Blo 896573 2426021 := bbase (se 4 (by rfl) ⟨227439, by rfl⟩ : syracuseStep 2426021 = 454879) (by norm_num)
theorem B1279253 : Blo 896573 1279253 := bbase (se 6 (by rfl) ⟨29982, by rfl⟩ : syracuseStep 1279253 = 59965) (by norm_num)
theorem B1344869 : Blo 896573 1344869 := bbase (se 4 (by rfl) ⟨126081, by rfl⟩ : syracuseStep 1344869 = 252163) (by norm_num)
theorem B1344893 : Blo 896573 1344893 := bbase (se 3 (by rfl) ⟨252167, by rfl⟩ : syracuseStep 1344893 = 504335) (by norm_num)
theorem B4097413 : Blo 896573 4097413 := bbase (se 4 (by rfl) ⟨384132, by rfl⟩ : syracuseStep 4097413 = 768265) (by norm_num)
theorem B1344917 : Blo 896573 1344917 := bbase (se 6 (by rfl) ⟨31521, by rfl⟩ : syracuseStep 1344917 = 63043) (by norm_num)
theorem B1344941 : Blo 896573 1344941 := bbase (se 3 (by rfl) ⟨252176, by rfl⟩ : syracuseStep 1344941 = 504353) (by norm_num)
theorem B1344965 : Blo 896573 1344965 := bbase (se 4 (by rfl) ⟨126090, by rfl⟩ : syracuseStep 1344965 = 252181) (by norm_num)
theorem B1344989 : Blo 896573 1344989 := bbase (se 3 (by rfl) ⟨252185, by rfl⟩ : syracuseStep 1344989 = 504371) (by norm_num)
theorem B1345013 : Blo 896573 1345013 := bbase (se 5 (by rfl) ⟨63047, by rfl⟩ : syracuseStep 1345013 = 126095) (by norm_num)
theorem B3409397 : Blo 896573 3409397 := bbase (se 5 (by rfl) ⟨159815, by rfl⟩ : syracuseStep 3409397 = 319631) (by norm_num)
theorem B1345037 : Blo 896573 1345037 := bbase (se 3 (by rfl) ⟨252194, by rfl⟩ : syracuseStep 1345037 = 504389) (by norm_num)
theorem B1345061 : Blo 896573 1345061 := bbase (se 4 (by rfl) ⟨126099, by rfl⟩ : syracuseStep 1345061 = 252199) (by norm_num)
theorem B1345085 : Blo 896573 1345085 := bbase (se 3 (by rfl) ⟨252203, by rfl⟩ : syracuseStep 1345085 = 504407) (by norm_num)
theorem B1705549 : Blo 896573 1705549 := bbase (se 3 (by rfl) ⟨319790, by rfl⟩ : syracuseStep 1705549 = 639581) (by norm_num)
theorem B1345109 : Blo 896573 1345109 := bbase (se 8 (by rfl) ⟨7881, by rfl⟩ : syracuseStep 1345109 = 15763) (by norm_num)
theorem B1082981 : Blo 896573 1082981 := bbase (se 4 (by rfl) ⟨101529, by rfl⟩ : syracuseStep 1082981 = 203059) (by norm_num)
theorem B1345133 : Blo 896573 1345133 := bbase (se 3 (by rfl) ⟨252212, by rfl⟩ : syracuseStep 1345133 = 504425) (by norm_num)
theorem B1345157 : Blo 896573 1345157 := bbase (se 4 (by rfl) ⟨126108, by rfl⟩ : syracuseStep 1345157 = 252217) (by norm_num)
theorem B1312405 : Blo 896573 1312405 := bbase (se 6 (by rfl) ⟨30759, by rfl⟩ : syracuseStep 1312405 = 61519) (by norm_num)
theorem B1345181 : Blo 896573 1345181 := bbase (se 3 (by rfl) ⟨252221, by rfl⟩ : syracuseStep 1345181 = 504443) (by norm_num)
theorem B1345205 : Blo 896573 1345205 := bbase (se 5 (by rfl) ⟨63056, by rfl⟩ : syracuseStep 1345205 = 126113) (by norm_num)
theorem B1345229 : Blo 896573 1345229 := bbase (se 3 (by rfl) ⟨252230, by rfl⟩ : syracuseStep 1345229 = 504461) (by norm_num)
theorem B24610517 : Blo 896573 24610517 := bbase (se 7 (by rfl) ⟨288404, by rfl⟩ : syracuseStep 24610517 = 576809) (by norm_num)
theorem B1705693 : Blo 896573 1705693 := bbase (se 3 (by rfl) ⟨319817, by rfl⟩ : syracuseStep 1705693 = 639635) (by norm_num)
theorem B1345253 : Blo 896573 1345253 := bbase (se 4 (by rfl) ⟨126117, by rfl⟩ : syracuseStep 1345253 = 252235) (by norm_num)
theorem B1345277 : Blo 896573 1345277 := bbase (se 3 (by rfl) ⟨252239, by rfl⟩ : syracuseStep 1345277 = 504479) (by norm_num)
theorem B1214221 : Blo 896573 1214221 := bbase (se 3 (by rfl) ⟨227666, by rfl⟩ : syracuseStep 1214221 = 455333) (by norm_num)
theorem B1345301 : Blo 896573 1345301 := bbase (se 6 (by rfl) ⟨31530, by rfl⟩ : syracuseStep 1345301 = 63061) (by norm_num)
theorem B3409685 : Blo 896573 3409685 := bbase (se 6 (by rfl) ⟨79914, by rfl⟩ : syracuseStep 3409685 = 159829) (by norm_num)
theorem B1345325 : Blo 896573 1345325 := bbase (se 3 (by rfl) ⟨252248, by rfl⟩ : syracuseStep 1345325 = 504497) (by norm_num)
theorem B1279805 : Blo 896573 1279805 := bbase (se 3 (by rfl) ⟨239963, by rfl⟩ : syracuseStep 1279805 = 479927) (by norm_num)
theorem B1345349 : Blo 896573 1345349 := bbase (se 4 (by rfl) ⟨126126, by rfl⟩ : syracuseStep 1345349 = 252253) (by norm_num)
theorem B1345373 : Blo 896573 1345373 := bbase (se 3 (by rfl) ⟨252257, by rfl⟩ : syracuseStep 1345373 = 504515) (by norm_num)
theorem B1345397 : Blo 896573 1345397 := bbase (se 5 (by rfl) ⟨63065, by rfl⟩ : syracuseStep 1345397 = 126131) (by norm_num)
theorem B1705853 : Blo 896573 1705853 := bbase (se 3 (by rfl) ⟨319847, by rfl⟩ : syracuseStep 1705853 = 639695) (by norm_num)
theorem B1345421 : Blo 896573 1345421 := bbase (se 3 (by rfl) ⟨252266, by rfl⟩ : syracuseStep 1345421 = 504533) (by norm_num)
theorem B1345445 : Blo 896573 1345445 := bbase (se 4 (by rfl) ⟨126135, by rfl⟩ : syracuseStep 1345445 = 252271) (by norm_num)
theorem B1345469 : Blo 896573 1345469 := bbase (se 3 (by rfl) ⟨252275, by rfl⟩ : syracuseStep 1345469 = 504551) (by norm_num)
theorem B1345493 : Blo 896573 1345493 := bbase (se 7 (by rfl) ⟨15767, by rfl⟩ : syracuseStep 1345493 = 31535) (by norm_num)
theorem B2557925 : Blo 896573 2557925 := bbase (se 4 (by rfl) ⟨239805, by rfl⟩ : syracuseStep 2557925 = 479611) (by norm_num)
theorem B1345517 : Blo 896573 1345517 := bbase (se 3 (by rfl) ⟨252284, by rfl⟩ : syracuseStep 1345517 = 504569) (by norm_num)
theorem B1345541 : Blo 896573 1345541 := bbase (se 4 (by rfl) ⟨126144, by rfl⟩ : syracuseStep 1345541 = 252289) (by norm_num)
theorem B1705997 : Blo 896573 1705997 := bbase (se 3 (by rfl) ⟨319874, by rfl⟩ : syracuseStep 1705997 = 639749) (by norm_num)
theorem B1345565 : Blo 896573 1345565 := bbase (se 3 (by rfl) ⟨252293, by rfl⟩ : syracuseStep 1345565 = 504587) (by norm_num)
theorem B1345589 : Blo 896573 1345589 := bbase (se 5 (by rfl) ⟨63074, by rfl⟩ : syracuseStep 1345589 = 126149) (by norm_num)
theorem B1345613 : Blo 896573 1345613 := bbase (se 3 (by rfl) ⟨252302, by rfl⟩ : syracuseStep 1345613 = 504605) (by norm_num)
theorem B1345637 : Blo 896573 1345637 := bbase (se 4 (by rfl) ⟨126153, by rfl⟩ : syracuseStep 1345637 = 252307) (by norm_num)
theorem B1345661 : Blo 896573 1345661 := bbase (se 3 (by rfl) ⟨252311, by rfl⟩ : syracuseStep 1345661 = 504623) (by norm_num)
theorem B1345685 : Blo 896573 1345685 := bbase (se 6 (by rfl) ⟨31539, by rfl⟩ : syracuseStep 1345685 = 63079) (by norm_num)
theorem B1345709 : Blo 896573 1345709 := bbase (se 3 (by rfl) ⟨252320, by rfl⟩ : syracuseStep 1345709 = 504641) (by norm_num)
theorem B1345733 : Blo 896573 1345733 := bbase (se 4 (by rfl) ⟨126162, by rfl⟩ : syracuseStep 1345733 = 252325) (by norm_num)
theorem B1345757 : Blo 896573 1345757 := bbase (se 3 (by rfl) ⟨252329, by rfl⟩ : syracuseStep 1345757 = 504659) (by norm_num)
theorem B1345781 : Blo 896573 1345781 := bbase (se 5 (by rfl) ⟨63083, by rfl⟩ : syracuseStep 1345781 = 126167) (by norm_num)
theorem B1345805 : Blo 896573 1345805 := bbase (se 3 (by rfl) ⟨252338, by rfl⟩ : syracuseStep 1345805 = 504677) (by norm_num)
theorem B1345829 : Blo 896573 1345829 := bbase (se 4 (by rfl) ⟨126171, by rfl⟩ : syracuseStep 1345829 = 252343) (by norm_num)
theorem B1706285 : Blo 896573 1706285 := bbase (se 3 (by rfl) ⟨319928, by rfl⟩ : syracuseStep 1706285 = 639857) (by norm_num)
theorem B1345853 : Blo 896573 1345853 := bbase (se 3 (by rfl) ⟨252347, by rfl⟩ : syracuseStep 1345853 = 504695) (by norm_num)
theorem B1345877 : Blo 896573 1345877 := bbase (se 10 (by rfl) ⟨1971, by rfl⟩ : syracuseStep 1345877 = 3943) (by norm_num)
theorem B1345901 : Blo 896573 1345901 := bbase (se 3 (by rfl) ⟨252356, by rfl⟩ : syracuseStep 1345901 = 504713) (by norm_num)
theorem B1345925 : Blo 896573 1345925 := bbase (se 4 (by rfl) ⟨126180, by rfl⟩ : syracuseStep 1345925 = 252361) (by norm_num)
theorem B3279253 : Blo 896573 3279253 := bbase (se 6 (by rfl) ⟨76857, by rfl⟩ : syracuseStep 3279253 = 153715) (by norm_num)
theorem B1345949 : Blo 896573 1345949 := bbase (se 3 (by rfl) ⟨252365, by rfl⟩ : syracuseStep 1345949 = 504731) (by norm_num)
theorem B4557221 : Blo 896573 4557221 := bbase (se 4 (by rfl) ⟨427239, by rfl⟩ : syracuseStep 4557221 = 854479) (by norm_num)
theorem B1345973 : Blo 896573 1345973 := bbase (se 5 (by rfl) ⟨63092, by rfl⟩ : syracuseStep 1345973 = 126185) (by norm_num)
theorem B1706437 : Blo 896573 1706437 := bbase (se 4 (by rfl) ⟨159978, by rfl⟩ : syracuseStep 1706437 = 319957) (by norm_num)
theorem B1345997 : Blo 896573 1345997 := bbase (se 3 (by rfl) ⟨252374, by rfl⟩ : syracuseStep 1345997 = 504749) (by norm_num)
theorem B1346021 : Blo 896573 1346021 := bbase (se 4 (by rfl) ⟨126189, by rfl⟩ : syracuseStep 1346021 = 252379) (by norm_num)
theorem B1346045 : Blo 896573 1346045 := bbase (se 3 (by rfl) ⟨252383, by rfl⟩ : syracuseStep 1346045 = 504767) (by norm_num)
theorem B1346069 : Blo 896573 1346069 := bbase (se 6 (by rfl) ⟨31548, by rfl⟩ : syracuseStep 1346069 = 63097) (by norm_num)
theorem B1346093 : Blo 896573 1346093 := bbase (se 3 (by rfl) ⟨252392, by rfl⟩ : syracuseStep 1346093 = 504785) (by norm_num)
theorem B1280557 : Blo 896573 1280557 := bbase (se 3 (by rfl) ⟨240104, by rfl⟩ : syracuseStep 1280557 = 480209) (by norm_num)
theorem B1346117 : Blo 896573 1346117 := bbase (se 4 (by rfl) ⟨126198, by rfl⟩ : syracuseStep 1346117 = 252397) (by norm_num)
theorem B1346141 : Blo 896573 1346141 := bbase (se 3 (by rfl) ⟨252401, by rfl⟩ : syracuseStep 1346141 = 504803) (by norm_num)
theorem B1346165 : Blo 896573 1346165 := bbase (se 5 (by rfl) ⟨63101, by rfl⟩ : syracuseStep 1346165 = 126203) (by norm_num)
theorem B1346189 : Blo 896573 1346189 := bbase (se 3 (by rfl) ⟨252410, by rfl⟩ : syracuseStep 1346189 = 504821) (by norm_num)
theorem B1346213 : Blo 896573 1346213 := bbase (se 4 (by rfl) ⟨126207, by rfl⟩ : syracuseStep 1346213 = 252415) (by norm_num)
theorem B1215157 : Blo 896573 1215157 := bbase (se 5 (by rfl) ⟨56960, by rfl⟩ : syracuseStep 1215157 = 113921) (by norm_num)
theorem B1346237 : Blo 896573 1346237 := bbase (se 3 (by rfl) ⟨252419, by rfl⟩ : syracuseStep 1346237 = 504839) (by norm_num)
theorem B1346261 : Blo 896573 1346261 := bbase (se 7 (by rfl) ⟨15776, by rfl⟩ : syracuseStep 1346261 = 31553) (by norm_num)
theorem B1346285 : Blo 896573 1346285 := bbase (se 3 (by rfl) ⟨252428, by rfl⟩ : syracuseStep 1346285 = 504857) (by norm_num)
theorem B1706741 : Blo 896573 1706741 := bbase (se 5 (by rfl) ⟨80003, by rfl⟩ : syracuseStep 1706741 = 160007) (by norm_num)
theorem B1346309 : Blo 896573 1346309 := bbase (se 4 (by rfl) ⟨126216, by rfl⟩ : syracuseStep 1346309 = 252433) (by norm_num)
theorem B1346333 : Blo 896573 1346333 := bbase (se 3 (by rfl) ⟨252437, by rfl⟩ : syracuseStep 1346333 = 504875) (by norm_num)
theorem B1346357 : Blo 896573 1346357 := bbase (se 5 (by rfl) ⟨63110, by rfl⟩ : syracuseStep 1346357 = 126221) (by norm_num)
theorem B1346381 : Blo 896573 1346381 := bbase (se 3 (by rfl) ⟨252446, by rfl⟩ : syracuseStep 1346381 = 504893) (by norm_num)
theorem B1346405 : Blo 896573 1346405 := bbase (se 4 (by rfl) ⟨126225, by rfl⟩ : syracuseStep 1346405 = 252451) (by norm_num)
theorem B1346429 : Blo 896573 1346429 := bbase (se 3 (by rfl) ⟨252455, by rfl⟩ : syracuseStep 1346429 = 504911) (by norm_num)
theorem B1346453 : Blo 896573 1346453 := bbase (se 6 (by rfl) ⟨31557, by rfl⟩ : syracuseStep 1346453 = 63115) (by norm_num)
theorem B1346477 : Blo 896573 1346477 := bbase (se 3 (by rfl) ⟨252464, by rfl⟩ : syracuseStep 1346477 = 504929) (by norm_num)
theorem B3410869 : Blo 896573 3410869 := bbase (se 5 (by rfl) ⟨159884, by rfl⟩ : syracuseStep 3410869 = 319769) (by norm_num)
theorem B1346501 : Blo 896573 1346501 := bbase (se 4 (by rfl) ⟨126234, by rfl⟩ : syracuseStep 1346501 = 252469) (by norm_num)
theorem B1346525 : Blo 896573 1346525 := bbase (se 3 (by rfl) ⟨252473, by rfl⟩ : syracuseStep 1346525 = 504947) (by norm_num)
theorem B2558965 : Blo 896573 2558965 := bbase (se 5 (by rfl) ⟨119951, by rfl⟩ : syracuseStep 2558965 = 239903) (by norm_num)
theorem B1346549 : Blo 896573 1346549 := bbase (se 5 (by rfl) ⟨63119, by rfl⟩ : syracuseStep 1346549 = 126239) (by norm_num)
theorem B1346573 : Blo 896573 1346573 := bbase (se 3 (by rfl) ⟨252482, by rfl⟩ : syracuseStep 1346573 = 504965) (by norm_num)
theorem B1346597 : Blo 896573 1346597 := bbase (se 4 (by rfl) ⟨126243, by rfl⟩ : syracuseStep 1346597 = 252487) (by norm_num)
theorem B1346621 : Blo 896573 1346621 := bbase (se 3 (by rfl) ⟨252491, by rfl⟩ : syracuseStep 1346621 = 504983) (by norm_num)
theorem B1346645 : Blo 896573 1346645 := bbase (se 8 (by rfl) ⟨7890, by rfl⟩ : syracuseStep 1346645 = 15781) (by norm_num)
theorem B1346669 : Blo 896573 1346669 := bbase (se 3 (by rfl) ⟨252500, by rfl⟩ : syracuseStep 1346669 = 505001) (by norm_num)
theorem B1215605 : Blo 896573 1215605 := bbase (se 5 (by rfl) ⟨56981, by rfl⟩ : syracuseStep 1215605 = 113963) (by norm_num)
theorem B1346693 : Blo 896573 1346693 := bbase (se 4 (by rfl) ⟨126252, by rfl⟩ : syracuseStep 1346693 = 252505) (by norm_num)
theorem B2559109 : Blo 896573 2559109 := bbase (se 4 (by rfl) ⟨239916, by rfl⟩ : syracuseStep 2559109 = 479833) (by norm_num)
theorem B3837077 : Blo 896573 3837077 := bbase (se 6 (by rfl) ⟨89931, by rfl⟩ : syracuseStep 3837077 = 179863) (by norm_num)
theorem B1346717 : Blo 896573 1346717 := bbase (se 3 (by rfl) ⟨252509, by rfl⟩ : syracuseStep 1346717 = 505019) (by norm_num)
theorem B1346741 : Blo 896573 1346741 := bbase (se 5 (by rfl) ⟨63128, by rfl⟩ : syracuseStep 1346741 = 126257) (by norm_num)
theorem B1346765 : Blo 896573 1346765 := bbase (se 3 (by rfl) ⟨252518, by rfl⟩ : syracuseStep 1346765 = 505037) (by norm_num)
theorem B1346789 : Blo 896573 1346789 := bbase (se 4 (by rfl) ⟨126261, by rfl⟩ : syracuseStep 1346789 = 252523) (by norm_num)
theorem B3411173 : Blo 896573 3411173 := bbase (se 4 (by rfl) ⟨319797, by rfl⟩ : syracuseStep 3411173 = 639595) (by norm_num)
theorem B1346813 : Blo 896573 1346813 := bbase (se 3 (by rfl) ⟨252527, by rfl⟩ : syracuseStep 1346813 = 505055) (by norm_num)
theorem B1346837 : Blo 896573 1346837 := bbase (se 6 (by rfl) ⟨31566, by rfl⟩ : syracuseStep 1346837 = 63133) (by norm_num)
theorem B2559269 : Blo 896573 2559269 := bbase (se 4 (by rfl) ⟨239931, by rfl⟩ : syracuseStep 2559269 = 479863) (by norm_num)
theorem B1346861 : Blo 896573 1346861 := bbase (se 3 (by rfl) ⟨252536, by rfl⟩ : syracuseStep 1346861 = 505073) (by norm_num)
theorem B1346885 : Blo 896573 1346885 := bbase (se 4 (by rfl) ⟨126270, by rfl⟩ : syracuseStep 1346885 = 252541) (by norm_num)
theorem B1281349 : Blo 896573 1281349 := bbase (se 4 (by rfl) ⟨120126, by rfl⟩ : syracuseStep 1281349 = 240253) (by norm_num)
theorem B1346909 : Blo 896573 1346909 := bbase (se 3 (by rfl) ⟨252545, by rfl⟩ : syracuseStep 1346909 = 505091) (by norm_num)
theorem B1346933 : Blo 896573 1346933 := bbase (se 5 (by rfl) ⟨63137, by rfl⟩ : syracuseStep 1346933 = 126275) (by norm_num)
theorem B1346957 : Blo 896573 1346957 := bbase (se 3 (by rfl) ⟨252554, by rfl⟩ : syracuseStep 1346957 = 505109) (by norm_num)
theorem B1346981 : Blo 896573 1346981 := bbase (se 4 (by rfl) ⟨126279, by rfl⟩ : syracuseStep 1346981 = 252559) (by norm_num)
theorem B3837365 : Blo 896573 3837365 := bbase (se 5 (by rfl) ⟨179876, by rfl⟩ : syracuseStep 3837365 = 359753) (by norm_num)
theorem B1347005 : Blo 896573 1347005 := bbase (se 3 (by rfl) ⟨252563, by rfl⟩ : syracuseStep 1347005 = 505127) (by norm_num)
theorem B1347029 : Blo 896573 1347029 := bbase (se 7 (by rfl) ⟨15785, by rfl⟩ : syracuseStep 1347029 = 31571) (by norm_num)
theorem B1707493 : Blo 896573 1707493 := bbase (se 4 (by rfl) ⟨160077, by rfl⟩ : syracuseStep 1707493 = 320155) (by norm_num)
theorem B1347053 : Blo 896573 1347053 := bbase (se 3 (by rfl) ⟨252572, by rfl⟩ : syracuseStep 1347053 = 505145) (by norm_num)
theorem B1150457 : Blo 896573 1150457 := bbase (se 2 (by rfl) ⟨431421, by rfl⟩ : syracuseStep 1150457 = 862843) (by norm_num)
theorem B1347077 : Blo 896573 1347077 := bbase (se 4 (by rfl) ⟨126288, by rfl⟩ : syracuseStep 1347077 = 252577) (by norm_num)
theorem B2559509 : Blo 896573 2559509 := bbase (se 6 (by rfl) ⟨59988, by rfl⟩ : syracuseStep 2559509 = 119977) (by norm_num)
theorem B1347101 : Blo 896573 1347101 := bbase (se 3 (by rfl) ⟨252581, by rfl⟩ : syracuseStep 1347101 = 505163) (by norm_num)
theorem B1347125 : Blo 896573 1347125 := bbase (se 5 (by rfl) ⟨63146, by rfl⟩ : syracuseStep 1347125 = 126293) (by norm_num)
theorem B1347149 : Blo 896573 1347149 := bbase (se 3 (by rfl) ⟨252590, by rfl⟩ : syracuseStep 1347149 = 505181) (by norm_num)
theorem B1347173 : Blo 896573 1347173 := bbase (se 4 (by rfl) ⟨126297, by rfl⟩ : syracuseStep 1347173 = 252595) (by norm_num)
theorem B1707637 : Blo 896573 1707637 := bbase (se 5 (by rfl) ⟨80045, by rfl⟩ : syracuseStep 1707637 = 160091) (by norm_num)
theorem B1347197 : Blo 896573 1347197 := bbase (se 3 (by rfl) ⟨252599, by rfl⟩ : syracuseStep 1347197 = 505199) (by norm_num)
theorem B1347221 : Blo 896573 1347221 := bbase (se 6 (by rfl) ⟨31575, by rfl⟩ : syracuseStep 1347221 = 63151) (by norm_num)
theorem B1281685 : Blo 896573 1281685 := bbase (se 6 (by rfl) ⟨30039, by rfl⟩ : syracuseStep 1281685 = 60079) (by norm_num)
theorem B1347245 : Blo 896573 1347245 := bbase (se 3 (by rfl) ⟨252608, by rfl⟩ : syracuseStep 1347245 = 505217) (by norm_num)
theorem B4558517 : Blo 896573 4558517 := bbase (se 5 (by rfl) ⟨213680, by rfl⟩ : syracuseStep 4558517 = 427361) (by norm_num)
theorem B1347269 : Blo 896573 1347269 := bbase (se 4 (by rfl) ⟨126306, by rfl⟩ : syracuseStep 1347269 = 252613) (by norm_num)
theorem B2559701 : Blo 896573 2559701 := bbase (se 7 (by rfl) ⟨29996, by rfl⟩ : syracuseStep 2559701 = 59993) (by norm_num)
theorem B1347293 : Blo 896573 1347293 := bbase (se 3 (by rfl) ⟨252617, by rfl⟩ : syracuseStep 1347293 = 505235) (by norm_num)
theorem B1347317 : Blo 896573 1347317 := bbase (se 5 (by rfl) ⟨63155, by rfl⟩ : syracuseStep 1347317 = 126311) (by norm_num)
theorem B1347341 : Blo 896573 1347341 := bbase (se 3 (by rfl) ⟨252626, by rfl⟩ : syracuseStep 1347341 = 505253) (by norm_num)
theorem B1707797 : Blo 896573 1707797 := bbase (se 6 (by rfl) ⟨40026, by rfl⟩ : syracuseStep 1707797 = 80053) (by norm_num)
theorem B1347365 : Blo 896573 1347365 := bbase (se 4 (by rfl) ⟨126315, by rfl⟩ : syracuseStep 1347365 = 252631) (by norm_num)
theorem B1347389 : Blo 896573 1347389 := bbase (se 3 (by rfl) ⟨252635, by rfl⟩ : syracuseStep 1347389 = 505271) (by norm_num)
theorem B1347413 : Blo 896573 1347413 := bbase (se 9 (by rfl) ⟨3947, by rfl⟩ : syracuseStep 1347413 = 7895) (by norm_num)
theorem B1347437 : Blo 896573 1347437 := bbase (se 3 (by rfl) ⟨252644, by rfl⟩ : syracuseStep 1347437 = 505289) (by norm_num)
theorem B1281901 : Blo 896573 1281901 := bbase (se 3 (by rfl) ⟨240356, by rfl⟩ : syracuseStep 1281901 = 480713) (by norm_num)
theorem B1347461 : Blo 896573 1347461 := bbase (se 4 (by rfl) ⟨126324, by rfl⟩ : syracuseStep 1347461 = 252649) (by norm_num)
theorem B1347485 : Blo 896573 1347485 := bbase (se 3 (by rfl) ⟨252653, by rfl⟩ : syracuseStep 1347485 = 505307) (by norm_num)
theorem B1707941 : Blo 896573 1707941 := bbase (se 4 (by rfl) ⟨160119, by rfl⟩ : syracuseStep 1707941 = 320239) (by norm_num)
theorem B1347509 : Blo 896573 1347509 := bbase (se 5 (by rfl) ⟨63164, by rfl⟩ : syracuseStep 1347509 = 126329) (by norm_num)
theorem B1347533 : Blo 896573 1347533 := bbase (se 3 (by rfl) ⟨252662, by rfl⟩ : syracuseStep 1347533 = 505325) (by norm_num)
theorem B1347557 : Blo 896573 1347557 := bbase (se 4 (by rfl) ⟨126333, by rfl⟩ : syracuseStep 1347557 = 252667) (by norm_num)
theorem B1347581 : Blo 896573 1347581 := bbase (se 3 (by rfl) ⟨252671, by rfl⟩ : syracuseStep 1347581 = 505343) (by norm_num)
theorem B1347605 : Blo 896573 1347605 := bbase (se 6 (by rfl) ⟨31584, by rfl⟩ : syracuseStep 1347605 = 63169) (by norm_num)
theorem B1347629 : Blo 896573 1347629 := bbase (se 3 (by rfl) ⟨252680, by rfl⟩ : syracuseStep 1347629 = 505361) (by norm_num)
theorem B1347653 : Blo 896573 1347653 := bbase (se 4 (by rfl) ⟨126342, by rfl⟩ : syracuseStep 1347653 = 252685) (by norm_num)
theorem B1347677 : Blo 896573 1347677 := bbase (se 3 (by rfl) ⟨252689, by rfl⟩ : syracuseStep 1347677 = 505379) (by norm_num)
theorem B1347701 : Blo 896573 1347701 := bbase (se 5 (by rfl) ⟨63173, by rfl⟩ : syracuseStep 1347701 = 126347) (by norm_num)
theorem B1347725 : Blo 896573 1347725 := bbase (se 3 (by rfl) ⟨252698, by rfl⟩ : syracuseStep 1347725 = 505397) (by norm_num)
theorem B1347749 : Blo 896573 1347749 := bbase (se 4 (by rfl) ⟨126351, by rfl⟩ : syracuseStep 1347749 = 252703) (by norm_num)
theorem B3838117 : Blo 896573 3838117 := bbase (se 4 (by rfl) ⟨359823, by rfl⟩ : syracuseStep 3838117 = 719647) (by norm_num)
theorem B1347773 : Blo 896573 1347773 := bbase (se 3 (by rfl) ⟨252707, by rfl⟩ : syracuseStep 1347773 = 505415) (by norm_num)
theorem B1708229 : Blo 896573 1708229 := bbase (se 4 (by rfl) ⟨160146, by rfl⟩ : syracuseStep 1708229 = 320293) (by norm_num)
theorem B1347797 : Blo 896573 1347797 := bbase (se 7 (by rfl) ⟨15794, by rfl⟩ : syracuseStep 1347797 = 31589) (by norm_num)
theorem B1347821 : Blo 896573 1347821 := bbase (se 3 (by rfl) ⟨252716, by rfl⟩ : syracuseStep 1347821 = 505433) (by norm_num)
theorem B1347845 : Blo 896573 1347845 := bbase (se 4 (by rfl) ⟨126360, by rfl⟩ : syracuseStep 1347845 = 252721) (by norm_num)
theorem B1347869 : Blo 896573 1347869 := bbase (se 3 (by rfl) ⟨252725, by rfl⟩ : syracuseStep 1347869 = 505451) (by norm_num)
theorem B1347893 : Blo 896573 1347893 := bbase (se 5 (by rfl) ⟨63182, by rfl⟩ : syracuseStep 1347893 = 126365) (by norm_num)
theorem B1347917 : Blo 896573 1347917 := bbase (se 3 (by rfl) ⟨252734, by rfl⟩ : syracuseStep 1347917 = 505469) (by norm_num)
theorem B1708381 : Blo 896573 1708381 := bbase (se 3 (by rfl) ⟨320321, by rfl⟩ : syracuseStep 1708381 = 640643) (by norm_num)
theorem B1347941 : Blo 896573 1347941 := bbase (se 4 (by rfl) ⟨126369, by rfl⟩ : syracuseStep 1347941 = 252739) (by norm_num)
theorem B1347965 : Blo 896573 1347965 := bbase (se 3 (by rfl) ⟨252743, by rfl⟩ : syracuseStep 1347965 = 505487) (by norm_num)
theorem B1347989 : Blo 896573 1347989 := bbase (se 6 (by rfl) ⟨31593, by rfl⟩ : syracuseStep 1347989 = 63187) (by norm_num)
theorem B1348013 : Blo 896573 1348013 := bbase (se 3 (by rfl) ⟨252752, by rfl⟩ : syracuseStep 1348013 = 505505) (by norm_num)
theorem B1348037 : Blo 896573 1348037 := bbase (se 4 (by rfl) ⟨126378, by rfl⟩ : syracuseStep 1348037 = 252757) (by norm_num)
theorem B1348061 : Blo 896573 1348061 := bbase (se 3 (by rfl) ⟨252761, by rfl⟩ : syracuseStep 1348061 = 505523) (by norm_num)
theorem B922097 : Blo 896573 922097 := bbase (se 2 (by rfl) ⟨345786, by rfl⟩ : syracuseStep 922097 = 691573) (by norm_num)
theorem B1348085 : Blo 896573 1348085 := bbase (se 5 (by rfl) ⟨63191, by rfl⟩ : syracuseStep 1348085 = 126383) (by norm_num)
theorem B1348109 : Blo 896573 1348109 := bbase (se 3 (by rfl) ⟨252770, by rfl⟩ : syracuseStep 1348109 = 505541) (by norm_num)
theorem B1348133 : Blo 896573 1348133 := bbase (se 4 (by rfl) ⟨126387, by rfl⟩ : syracuseStep 1348133 = 252775) (by norm_num)
theorem B1348157 : Blo 896573 1348157 := bbase (se 3 (by rfl) ⟨252779, by rfl⟩ : syracuseStep 1348157 = 505559) (by norm_num)
theorem B1348181 : Blo 896573 1348181 := bbase (se 8 (by rfl) ⟨7899, by rfl⟩ : syracuseStep 1348181 = 15799) (by norm_num)
theorem B1348205 : Blo 896573 1348205 := bbase (se 3 (by rfl) ⟨252788, by rfl⟩ : syracuseStep 1348205 = 505577) (by norm_num)
theorem B1348229 : Blo 896573 1348229 := bbase (se 4 (by rfl) ⟨126396, by rfl⟩ : syracuseStep 1348229 = 252793) (by norm_num)
theorem B1708685 : Blo 896573 1708685 := bbase (se 3 (by rfl) ⟨320378, by rfl⟩ : syracuseStep 1708685 = 640757) (by norm_num)
theorem B1348253 : Blo 896573 1348253 := bbase (se 3 (by rfl) ⟨252797, by rfl⟩ : syracuseStep 1348253 = 505595) (by norm_num)
theorem B8622773 : Blo 896573 8622773 := bbase (se 5 (by rfl) ⟨404192, by rfl⟩ : syracuseStep 8622773 = 808385) (by norm_num)
theorem B1348277 : Blo 896573 1348277 := bbase (se 5 (by rfl) ⟨63200, by rfl⟩ : syracuseStep 1348277 = 126401) (by norm_num)
theorem B2560693 : Blo 896573 2560693 := bbase (se 5 (by rfl) ⟨120032, by rfl⟩ : syracuseStep 2560693 = 240065) (by norm_num)
theorem B1348301 : Blo 896573 1348301 := bbase (se 3 (by rfl) ⟨252806, by rfl⟩ : syracuseStep 1348301 = 505613) (by norm_num)
theorem B1348325 : Blo 896573 1348325 := bbase (se 4 (by rfl) ⟨126405, by rfl⟩ : syracuseStep 1348325 = 252811) (by norm_num)
theorem B1348349 : Blo 896573 1348349 := bbase (se 3 (by rfl) ⟨252815, by rfl⟩ : syracuseStep 1348349 = 505631) (by norm_num)
theorem B1348373 : Blo 896573 1348373 := bbase (se 6 (by rfl) ⟨31602, by rfl⟩ : syracuseStep 1348373 = 63205) (by norm_num)
theorem B1348397 : Blo 896573 1348397 := bbase (se 3 (by rfl) ⟨252824, by rfl⟩ : syracuseStep 1348397 = 505649) (by norm_num)
theorem B1348421 : Blo 896573 1348421 := bbase (se 4 (by rfl) ⟨126414, by rfl⟩ : syracuseStep 1348421 = 252829) (by norm_num)
theorem B1348445 : Blo 896573 1348445 := bbase (se 3 (by rfl) ⟨252833, by rfl⟩ : syracuseStep 1348445 = 505667) (by norm_num)
theorem B1348469 : Blo 896573 1348469 := bbase (se 5 (by rfl) ⟨63209, by rfl⟩ : syracuseStep 1348469 = 126419) (by norm_num)
theorem B3838853 : Blo 896573 3838853 := bbase (se 4 (by rfl) ⟨359892, by rfl⟩ : syracuseStep 3838853 = 719785) (by norm_num)
theorem B1348493 : Blo 896573 1348493 := bbase (se 3 (by rfl) ⟨252842, by rfl⟩ : syracuseStep 1348493 = 505685) (by norm_num)
theorem B1348517 : Blo 896573 1348517 := bbase (se 4 (by rfl) ⟨126423, by rfl⟩ : syracuseStep 1348517 = 252847) (by norm_num)
theorem B1872821 : Blo 896573 1872821 := bbase (se 5 (by rfl) ⟨87788, by rfl⟩ : syracuseStep 1872821 = 175577) (by norm_num)
theorem B1348541 : Blo 896573 1348541 := bbase (se 3 (by rfl) ⟨252851, by rfl⟩ : syracuseStep 1348541 = 505703) (by norm_num)
theorem B1348565 : Blo 896573 1348565 := bbase (se 7 (by rfl) ⟨15803, by rfl⟩ : syracuseStep 1348565 = 31607) (by norm_num)
theorem B1348589 : Blo 896573 1348589 := bbase (se 3 (by rfl) ⟨252860, by rfl⟩ : syracuseStep 1348589 = 505721) (by norm_num)
theorem B1348613 : Blo 896573 1348613 := bbase (se 4 (by rfl) ⟨126432, by rfl⟩ : syracuseStep 1348613 = 252865) (by norm_num)
theorem B1348637 : Blo 896573 1348637 := bbase (se 3 (by rfl) ⟨252869, by rfl⟩ : syracuseStep 1348637 = 505739) (by norm_num)
theorem B1348661 : Blo 896573 1348661 := bbase (se 5 (by rfl) ⟨63218, by rfl⟩ : syracuseStep 1348661 = 126437) (by norm_num)
theorem B1348685 : Blo 896573 1348685 := bbase (se 3 (by rfl) ⟨252878, by rfl⟩ : syracuseStep 1348685 = 505757) (by norm_num)
theorem B1348709 : Blo 896573 1348709 := bbase (se 4 (by rfl) ⟨126441, by rfl⟩ : syracuseStep 1348709 = 252883) (by norm_num)
theorem B1348733 : Blo 896573 1348733 := bbase (se 3 (by rfl) ⟨252887, by rfl⟩ : syracuseStep 1348733 = 505775) (by norm_num)
theorem B1348757 : Blo 896573 1348757 := bbase (se 6 (by rfl) ⟨31611, by rfl⟩ : syracuseStep 1348757 = 63223) (by norm_num)
theorem B1348781 : Blo 896573 1348781 := bbase (se 3 (by rfl) ⟨252896, by rfl⟩ : syracuseStep 1348781 = 505793) (by norm_num)
theorem B1348805 : Blo 896573 1348805 := bbase (se 4 (by rfl) ⟨126450, by rfl⟩ : syracuseStep 1348805 = 252901) (by norm_num)
theorem B1348829 : Blo 896573 1348829 := bbase (se 3 (by rfl) ⟨252905, by rfl⟩ : syracuseStep 1348829 = 505811) (by norm_num)
theorem B1348853 : Blo 896573 1348853 := bbase (se 5 (by rfl) ⟨63227, by rfl⟩ : syracuseStep 1348853 = 126455) (by norm_num)
theorem B1348877 : Blo 896573 1348877 := bbase (se 3 (by rfl) ⟨252914, by rfl⟩ : syracuseStep 1348877 = 505829) (by norm_num)
theorem B3413285 : Blo 896573 3413285 := bbase (se 4 (by rfl) ⟨319995, by rfl⟩ : syracuseStep 3413285 = 639991) (by norm_num)
theorem B1348901 : Blo 896573 1348901 := bbase (se 4 (by rfl) ⟨126459, by rfl⟩ : syracuseStep 1348901 = 252919) (by norm_num)
theorem B1348925 : Blo 896573 1348925 := bbase (se 3 (by rfl) ⟨252923, by rfl⟩ : syracuseStep 1348925 = 505847) (by norm_num)
theorem B1348949 : Blo 896573 1348949 := bbase (se 14 (by rfl) ⟨123, by rfl⟩ : syracuseStep 1348949 = 247) (by norm_num)
theorem B1348973 : Blo 896573 1348973 := bbase (se 3 (by rfl) ⟨252932, by rfl⟩ : syracuseStep 1348973 = 505865) (by norm_num)
theorem B1709437 : Blo 896573 1709437 := bbase (se 3 (by rfl) ⟨320519, by rfl⟩ : syracuseStep 1709437 = 641039) (by norm_num)
theorem B1348997 : Blo 896573 1348997 := bbase (se 4 (by rfl) ⟨126468, by rfl⟩ : syracuseStep 1348997 = 252937) (by norm_num)
theorem B1349021 : Blo 896573 1349021 := bbase (se 3 (by rfl) ⟨252941, by rfl⟩ : syracuseStep 1349021 = 505883) (by norm_num)
theorem B1349045 : Blo 896573 1349045 := bbase (se 5 (by rfl) ⟨63236, by rfl⟩ : syracuseStep 1349045 = 126473) (by norm_num)
theorem B1349069 : Blo 896573 1349069 := bbase (se 3 (by rfl) ⟨252950, by rfl⟩ : syracuseStep 1349069 = 505901) (by norm_num)
theorem B1349093 : Blo 896573 1349093 := bbase (se 4 (by rfl) ⟨126477, by rfl⟩ : syracuseStep 1349093 = 252955) (by norm_num)
theorem B1349117 : Blo 896573 1349117 := bbase (se 3 (by rfl) ⟨252959, by rfl⟩ : syracuseStep 1349117 = 505919) (by norm_num)
theorem B1709581 : Blo 896573 1709581 := bbase (se 3 (by rfl) ⟨320546, by rfl⟩ : syracuseStep 1709581 = 641093) (by norm_num)
theorem B1349141 : Blo 896573 1349141 := bbase (se 6 (by rfl) ⟨31620, by rfl⟩ : syracuseStep 1349141 = 63241) (by norm_num)
theorem B1349165 : Blo 896573 1349165 := bbase (se 3 (by rfl) ⟨252968, by rfl⟩ : syracuseStep 1349165 = 505937) (by norm_num)
theorem B3413573 : Blo 896573 3413573 := bbase (se 4 (by rfl) ⟨320022, by rfl⟩ : syracuseStep 3413573 = 640045) (by norm_num)
theorem B1349189 : Blo 896573 1349189 := bbase (se 4 (by rfl) ⟨126486, by rfl⟩ : syracuseStep 1349189 = 252973) (by norm_num)
theorem B1349213 : Blo 896573 1349213 := bbase (se 3 (by rfl) ⟨252977, by rfl⟩ : syracuseStep 1349213 = 505955) (by norm_num)
theorem B1349237 : Blo 896573 1349237 := bbase (se 5 (by rfl) ⟨63245, by rfl⟩ : syracuseStep 1349237 = 126491) (by norm_num)
theorem B1513093 : Blo 896573 1513093 := bbase (se 4 (by rfl) ⟨141852, by rfl⟩ : syracuseStep 1513093 = 283705) (by norm_num)
theorem B1349261 : Blo 896573 1349261 := bbase (se 3 (by rfl) ⟨252986, by rfl⟩ : syracuseStep 1349261 = 505973) (by norm_num)
theorem B1349285 : Blo 896573 1349285 := bbase (se 4 (by rfl) ⟨126495, by rfl⟩ : syracuseStep 1349285 = 252991) (by norm_num)
theorem B1349309 : Blo 896573 1349309 := bbase (se 3 (by rfl) ⟨252995, by rfl⟩ : syracuseStep 1349309 = 505991) (by norm_num)
theorem B1349333 : Blo 896573 1349333 := bbase (se 7 (by rfl) ⟨15812, by rfl⟩ : syracuseStep 1349333 = 31625) (by norm_num)
theorem B1513181 : Blo 896573 1513181 := bbase (se 3 (by rfl) ⟨283721, by rfl⟩ : syracuseStep 1513181 = 567443) (by norm_num)
theorem B1349357 : Blo 896573 1349357 := bbase (se 3 (by rfl) ⟨253004, by rfl⟩ : syracuseStep 1349357 = 506009) (by norm_num)
theorem B1349381 : Blo 896573 1349381 := bbase (se 4 (by rfl) ⟨126504, by rfl⟩ : syracuseStep 1349381 = 253009) (by norm_num)
theorem B2561797 : Blo 896573 2561797 := bbase (se 4 (by rfl) ⟨240168, by rfl⟩ : syracuseStep 2561797 = 480337) (by norm_num)
theorem B1349405 : Blo 896573 1349405 := bbase (se 3 (by rfl) ⟨253013, by rfl⟩ : syracuseStep 1349405 = 506027) (by norm_num)
theorem B1349429 : Blo 896573 1349429 := bbase (se 5 (by rfl) ⟨63254, by rfl⟩ : syracuseStep 1349429 = 126509) (by norm_num)
theorem B1349453 : Blo 896573 1349453 := bbase (se 3 (by rfl) ⟨253022, by rfl⟩ : syracuseStep 1349453 = 506045) (by norm_num)
theorem B1513309 : Blo 896573 1513309 := bbase (se 3 (by rfl) ⟨283745, by rfl⟩ : syracuseStep 1513309 = 567491) (by norm_num)
theorem B1349477 : Blo 896573 1349477 := bbase (se 4 (by rfl) ⟨126513, by rfl⟩ : syracuseStep 1349477 = 253027) (by norm_num)
theorem B1349501 : Blo 896573 1349501 := bbase (se 3 (by rfl) ⟨253031, by rfl⟩ : syracuseStep 1349501 = 506063) (by norm_num)
theorem B1349525 : Blo 896573 1349525 := bbase (se 6 (by rfl) ⟨31629, by rfl⟩ : syracuseStep 1349525 = 63259) (by norm_num)
theorem B1349549 : Blo 896573 1349549 := bbase (se 3 (by rfl) ⟨253040, by rfl⟩ : syracuseStep 1349549 = 506081) (by norm_num)
theorem B1513397 : Blo 896573 1513397 := bbase (se 5 (by rfl) ⟨70940, by rfl⟩ : syracuseStep 1513397 = 141881) (by norm_num)
theorem B1349573 : Blo 896573 1349573 := bbase (se 4 (by rfl) ⟨126522, by rfl⟩ : syracuseStep 1349573 = 253045) (by norm_num)
theorem B1349597 : Blo 896573 1349597 := bbase (se 3 (by rfl) ⟨253049, by rfl⟩ : syracuseStep 1349597 = 506099) (by norm_num)
theorem B1349621 : Blo 896573 1349621 := bbase (se 5 (by rfl) ⟨63263, by rfl⟩ : syracuseStep 1349621 = 126527) (by norm_num)
theorem B1349645 : Blo 896573 1349645 := bbase (se 3 (by rfl) ⟨253058, by rfl⟩ : syracuseStep 1349645 = 506117) (by norm_num)
theorem B1480733 : Blo 896573 1480733 := bbase (se 3 (by rfl) ⟨277637, by rfl⟩ : syracuseStep 1480733 = 555275) (by norm_num)
theorem B1349669 : Blo 896573 1349669 := bbase (se 4 (by rfl) ⟨126531, by rfl⟩ : syracuseStep 1349669 = 253063) (by norm_num)
theorem B1513525 : Blo 896573 1513525 := bbase (se 5 (by rfl) ⟨70946, by rfl⟩ : syracuseStep 1513525 = 141893) (by norm_num)
theorem B8296501 : Blo 896573 8296501 := bbase (se 5 (by rfl) ⟨388898, by rfl⟩ : syracuseStep 8296501 = 777797) (by norm_num)
theorem B1349693 : Blo 896573 1349693 := bbase (se 3 (by rfl) ⟨253067, by rfl⟩ : syracuseStep 1349693 = 506135) (by norm_num)
theorem B1349717 : Blo 896573 1349717 := bbase (se 8 (by rfl) ⟨7908, by rfl⟩ : syracuseStep 1349717 = 15817) (by norm_num)
theorem B1153121 : Blo 896573 1153121 := bbase (se 2 (by rfl) ⟨432420, by rfl⟩ : syracuseStep 1153121 = 864841) (by norm_num)
theorem B1349741 : Blo 896573 1349741 := bbase (se 3 (by rfl) ⟨253076, by rfl⟩ : syracuseStep 1349741 = 506153) (by norm_num)
theorem B1349765 : Blo 896573 1349765 := bbase (se 4 (by rfl) ⟨126540, by rfl⟩ : syracuseStep 1349765 = 253081) (by norm_num)
theorem B1513613 : Blo 896573 1513613 := bbase (se 3 (by rfl) ⟨283802, by rfl⟩ : syracuseStep 1513613 = 567605) (by norm_num)
theorem B1349789 : Blo 896573 1349789 := bbase (se 3 (by rfl) ⟨253085, by rfl⟩ : syracuseStep 1349789 = 506171) (by norm_num)
theorem B1349813 : Blo 896573 1349813 := bbase (se 5 (by rfl) ⟨63272, by rfl⟩ : syracuseStep 1349813 = 126545) (by norm_num)
theorem B1349837 : Blo 896573 1349837 := bbase (se 3 (by rfl) ⟨253094, by rfl⟩ : syracuseStep 1349837 = 506189) (by norm_num)
theorem B9214165 : Blo 896573 9214165 := bbase (se 7 (by rfl) ⟨107978, by rfl⟩ : syracuseStep 9214165 = 215957) (by norm_num)
theorem B1349861 : Blo 896573 1349861 := bbase (se 4 (by rfl) ⟨126549, by rfl⟩ : syracuseStep 1349861 = 253099) (by norm_num)
theorem B1349885 : Blo 896573 1349885 := bbase (se 3 (by rfl) ⟨253103, by rfl⟩ : syracuseStep 1349885 = 506207) (by norm_num)
theorem B1513741 : Blo 896573 1513741 := bbase (se 3 (by rfl) ⟨283826, by rfl⟩ : syracuseStep 1513741 = 567653) (by norm_num)
theorem B1349909 : Blo 896573 1349909 := bbase (se 6 (by rfl) ⟨31638, by rfl⟩ : syracuseStep 1349909 = 63277) (by norm_num)
theorem B1349933 : Blo 896573 1349933 := bbase (se 3 (by rfl) ⟨253112, by rfl⟩ : syracuseStep 1349933 = 506225) (by norm_num)
theorem B1349957 : Blo 896573 1349957 := bbase (se 4 (by rfl) ⟨126558, by rfl⟩ : syracuseStep 1349957 = 253117) (by norm_num)
theorem B4921685 : Blo 896573 4921685 := bbase (se 10 (by rfl) ⟨7209, by rfl⟩ : syracuseStep 4921685 = 14419) (by norm_num)
theorem B1349981 : Blo 896573 1349981 := bbase (se 3 (by rfl) ⟨253121, by rfl⟩ : syracuseStep 1349981 = 506243) (by norm_num)
theorem B1513829 : Blo 896573 1513829 := bbase (se 4 (by rfl) ⟨141921, by rfl⟩ : syracuseStep 1513829 = 283843) (by norm_num)
theorem B1350005 : Blo 896573 1350005 := bbase (se 5 (by rfl) ⟨63281, by rfl⟩ : syracuseStep 1350005 = 126563) (by norm_num)
theorem B1350029 : Blo 896573 1350029 := bbase (se 3 (by rfl) ⟨253130, by rfl⟩ : syracuseStep 1350029 = 506261) (by norm_num)
theorem B1350053 : Blo 896573 1350053 := bbase (se 4 (by rfl) ⟨126567, by rfl⟩ : syracuseStep 1350053 = 253135) (by norm_num)
theorem B1350077 : Blo 896573 1350077 := bbase (se 3 (by rfl) ⟨253139, by rfl⟩ : syracuseStep 1350077 = 506279) (by norm_num)
theorem B1350101 : Blo 896573 1350101 := bbase (se 7 (by rfl) ⟨15821, by rfl⟩ : syracuseStep 1350101 = 31643) (by norm_num)
theorem B1513957 : Blo 896573 1513957 := bbase (se 4 (by rfl) ⟨141933, by rfl⟩ : syracuseStep 1513957 = 283867) (by norm_num)
theorem B1350125 : Blo 896573 1350125 := bbase (se 3 (by rfl) ⟨253148, by rfl⟩ : syracuseStep 1350125 = 506297) (by norm_num)
theorem B1350149 : Blo 896573 1350149 := bbase (se 4 (by rfl) ⟨126576, by rfl⟩ : syracuseStep 1350149 = 253153) (by norm_num)
theorem B7281173 : Blo 896573 7281173 := bbase (se 6 (by rfl) ⟨170652, by rfl⟩ : syracuseStep 7281173 = 341305) (by norm_num)
theorem B1350173 : Blo 896573 1350173 := bbase (se 3 (by rfl) ⟨253157, by rfl⟩ : syracuseStep 1350173 = 506315) (by norm_num)
theorem B1350197 : Blo 896573 1350197 := bbase (se 5 (by rfl) ⟨63290, by rfl⟩ : syracuseStep 1350197 = 126581) (by norm_num)
theorem B1514045 : Blo 896573 1514045 := bbase (se 3 (by rfl) ⟨283883, by rfl⟩ : syracuseStep 1514045 = 567767) (by norm_num)
theorem B1350221 : Blo 896573 1350221 := bbase (se 3 (by rfl) ⟨253166, by rfl⟩ : syracuseStep 1350221 = 506333) (by norm_num)
theorem B1350245 : Blo 896573 1350245 := bbase (se 4 (by rfl) ⟨126585, by rfl⟩ : syracuseStep 1350245 = 253171) (by norm_num)
theorem B1350269 : Blo 896573 1350269 := bbase (se 3 (by rfl) ⟨253175, by rfl⟩ : syracuseStep 1350269 = 506351) (by norm_num)
theorem B1350293 : Blo 896573 1350293 := bbase (se 6 (by rfl) ⟨31647, by rfl⟩ : syracuseStep 1350293 = 63295) (by norm_num)
theorem B1350317 : Blo 896573 1350317 := bbase (se 3 (by rfl) ⟨253184, by rfl⟩ : syracuseStep 1350317 = 506369) (by norm_num)
theorem B1153721 : Blo 896573 1153721 := bbase (se 2 (by rfl) ⟨432645, by rfl⟩ : syracuseStep 1153721 = 865291) (by norm_num)
theorem B1514173 : Blo 896573 1514173 := bbase (se 3 (by rfl) ⟨283907, by rfl⟩ : syracuseStep 1514173 = 567815) (by norm_num)
theorem B1350341 : Blo 896573 1350341 := bbase (se 4 (by rfl) ⟨126594, by rfl⟩ : syracuseStep 1350341 = 253189) (by norm_num)
theorem B1350365 : Blo 896573 1350365 := bbase (se 3 (by rfl) ⟨253193, by rfl⟩ : syracuseStep 1350365 = 506387) (by norm_num)
theorem B3414757 : Blo 896573 3414757 := bbase (se 4 (by rfl) ⟨320133, by rfl⟩ : syracuseStep 3414757 = 640267) (by norm_num)
theorem B1350389 : Blo 896573 1350389 := bbase (se 5 (by rfl) ⟨63299, by rfl⟩ : syracuseStep 1350389 = 126599) (by norm_num)
theorem B1350413 : Blo 896573 1350413 := bbase (se 3 (by rfl) ⟨253202, by rfl⟩ : syracuseStep 1350413 = 506405) (by norm_num)
theorem B1514261 : Blo 896573 1514261 := bbase (se 6 (by rfl) ⟨35490, by rfl⟩ : syracuseStep 1514261 = 70981) (by norm_num)
theorem B1350437 : Blo 896573 1350437 := bbase (se 4 (by rfl) ⟨126603, by rfl⟩ : syracuseStep 1350437 = 253207) (by norm_num)
theorem B1350461 : Blo 896573 1350461 := bbase (se 3 (by rfl) ⟨253211, by rfl⟩ : syracuseStep 1350461 = 506423) (by norm_num)
theorem B3119957 : Blo 896573 3119957 := bbase (se 9 (by rfl) ⟨9140, by rfl⟩ : syracuseStep 3119957 = 18281) (by norm_num)
theorem B1350485 : Blo 896573 1350485 := bbase (se 9 (by rfl) ⟨3956, by rfl⟩ : syracuseStep 1350485 = 7913) (by norm_num)
theorem B1350509 : Blo 896573 1350509 := bbase (se 3 (by rfl) ⟨253220, by rfl⟩ : syracuseStep 1350509 = 506441) (by norm_num)
theorem B1350533 : Blo 896573 1350533 := bbase (se 4 (by rfl) ⟨126612, by rfl⟩ : syracuseStep 1350533 = 253225) (by norm_num)
theorem B1514389 : Blo 896573 1514389 := bbase (se 6 (by rfl) ⟨35493, by rfl⟩ : syracuseStep 1514389 = 70987) (by norm_num)
theorem B1350557 : Blo 896573 1350557 := bbase (se 3 (by rfl) ⟨253229, by rfl⟩ : syracuseStep 1350557 = 506459) (by norm_num)
theorem B1350581 : Blo 896573 1350581 := bbase (se 5 (by rfl) ⟨63308, by rfl⟩ : syracuseStep 1350581 = 126617) (by norm_num)
theorem B1350605 : Blo 896573 1350605 := bbase (se 3 (by rfl) ⟨253238, by rfl⟩ : syracuseStep 1350605 = 506477) (by norm_num)
theorem B1350629 : Blo 896573 1350629 := bbase (se 4 (by rfl) ⟨126621, by rfl⟩ : syracuseStep 1350629 = 253243) (by norm_num)
theorem B1514477 : Blo 896573 1514477 := bbase (se 3 (by rfl) ⟨283964, by rfl⟩ : syracuseStep 1514477 = 567929) (by norm_num)
theorem B2104301 : Blo 896573 2104301 := bbase (se 3 (by rfl) ⟨394556, by rfl⟩ : syracuseStep 2104301 = 789113) (by norm_num)
theorem B1350653 : Blo 896573 1350653 := bbase (se 3 (by rfl) ⟨253247, by rfl⟩ : syracuseStep 1350653 = 506495) (by norm_num)
theorem B3415061 : Blo 896573 3415061 := bbase (se 6 (by rfl) ⟨80040, by rfl⟩ : syracuseStep 3415061 = 160081) (by norm_num)
theorem B1350677 : Blo 896573 1350677 := bbase (se 6 (by rfl) ⟨31656, by rfl⟩ : syracuseStep 1350677 = 63313) (by norm_num)
theorem B1350701 : Blo 896573 1350701 := bbase (se 3 (by rfl) ⟨253256, by rfl⟩ : syracuseStep 1350701 = 506513) (by norm_num)
theorem B1350725 : Blo 896573 1350725 := bbase (se 4 (by rfl) ⟨126630, by rfl⟩ : syracuseStep 1350725 = 253261) (by norm_num)
theorem B1350749 : Blo 896573 1350749 := bbase (se 3 (by rfl) ⟨253265, by rfl⟩ : syracuseStep 1350749 = 506531) (by norm_num)
theorem B1514605 : Blo 896573 1514605 := bbase (se 3 (by rfl) ⟨283988, by rfl⟩ : syracuseStep 1514605 = 567977) (by norm_num)
theorem B1350773 : Blo 896573 1350773 := bbase (se 5 (by rfl) ⟨63317, by rfl⟩ : syracuseStep 1350773 = 126635) (by norm_num)
theorem B1350797 : Blo 896573 1350797 := bbase (se 3 (by rfl) ⟨253274, by rfl⟩ : syracuseStep 1350797 = 506549) (by norm_num)
theorem B1350821 : Blo 896573 1350821 := bbase (se 4 (by rfl) ⟨126639, by rfl⟩ : syracuseStep 1350821 = 253279) (by norm_num)
theorem B957629 : Blo 896573 957629 := bbase (se 3 (by rfl) ⟨179555, by rfl⟩ : syracuseStep 957629 = 359111) (by norm_num)
theorem B1350845 : Blo 896573 1350845 := bbase (se 3 (by rfl) ⟨253283, by rfl⟩ : syracuseStep 1350845 = 506567) (by norm_num)
theorem B1514693 : Blo 896573 1514693 := bbase (se 4 (by rfl) ⟨142002, by rfl⟩ : syracuseStep 1514693 = 284005) (by norm_num)
theorem B2923733 : Blo 896573 2923733 := bbase (se 7 (by rfl) ⟨34262, by rfl⟩ : syracuseStep 2923733 = 68525) (by norm_num)
theorem B2563301 : Blo 896573 2563301 := bbase (se 4 (by rfl) ⟨240309, by rfl⟩ : syracuseStep 2563301 = 480619) (by norm_num)
theorem B957701 : Blo 896573 957701 := bbase (se 4 (by rfl) ⟨89784, by rfl⟩ : syracuseStep 957701 = 179569) (by norm_num)
theorem B1514821 : Blo 896573 1514821 := bbase (se 4 (by rfl) ⟨142014, by rfl⟩ : syracuseStep 1514821 = 284029) (by norm_num)
theorem B1514909 : Blo 896573 1514909 := bbase (se 3 (by rfl) ⟨284045, by rfl⟩ : syracuseStep 1514909 = 568091) (by norm_num)
theorem B3644837 : Blo 896573 3644837 := bbase (se 4 (by rfl) ⟨341703, by rfl⟩ : syracuseStep 3644837 = 683407) (by norm_num)
theorem B957889 : Blo 896573 957889 := bbase (se 2 (by rfl) ⟨359208, by rfl⟩ : syracuseStep 957889 = 718417) (by norm_num)
theorem B1515037 : Blo 896573 1515037 := bbase (se 3 (by rfl) ⟨284069, by rfl⟩ : syracuseStep 1515037 = 568139) (by norm_num)
theorem B1515125 : Blo 896573 1515125 := bbase (se 5 (by rfl) ⟨71021, by rfl⟩ : syracuseStep 1515125 = 142043) (by norm_num)
theorem B958073 : Blo 896573 958073 := bbase (se 2 (by rfl) ⟨359277, by rfl⟩ : syracuseStep 958073 = 718555) (by norm_num)
theorem B1515253 : Blo 896573 1515253 := bbase (se 5 (by rfl) ⟨71027, by rfl⟩ : syracuseStep 1515253 = 142055) (by norm_num)
theorem B2629397 : Blo 896573 2629397 := bbase (se 6 (by rfl) ⟨61626, by rfl⟩ : syracuseStep 2629397 = 123253) (by norm_num)
theorem B1515341 : Blo 896573 1515341 := bbase (se 3 (by rfl) ⟨284126, by rfl⟩ : syracuseStep 1515341 = 568253) (by norm_num)
theorem B1515469 : Blo 896573 1515469 := bbase (se 3 (by rfl) ⟨284150, by rfl⟩ : syracuseStep 1515469 = 568301) (by norm_num)
theorem B6823925 : Blo 896573 6823925 := bbase (se 5 (by rfl) ⟨319871, by rfl⟩ : syracuseStep 6823925 = 639743) (by norm_num)
theorem B1843205 : Blo 896573 1843205 := bbase (se 4 (by rfl) ⟨172800, by rfl⟩ : syracuseStep 1843205 = 345601) (by norm_num)
theorem B1515557 : Blo 896573 1515557 := bbase (se 4 (by rfl) ⟨142083, by rfl⟩ : syracuseStep 1515557 = 284167) (by norm_num)
theorem B3842149 : Blo 896573 3842149 := bbase (se 4 (by rfl) ⟨360201, by rfl⟩ : syracuseStep 3842149 = 720403) (by norm_num)
theorem B1024121 : Blo 896573 1024121 := bbase (se 2 (by rfl) ⟨384045, by rfl⟩ : syracuseStep 1024121 = 768091) (by norm_num)
theorem B1515685 : Blo 896573 1515685 := bbase (se 4 (by rfl) ⟨142095, by rfl⟩ : syracuseStep 1515685 = 284191) (by norm_num)
theorem B1515773 : Blo 896573 1515773 := bbase (se 3 (by rfl) ⟨284207, by rfl⟩ : syracuseStep 1515773 = 568415) (by norm_num)
theorem B958825 : Blo 896573 958825 := bbase (se 2 (by rfl) ⟨359559, by rfl⟩ : syracuseStep 958825 = 719119) (by norm_num)
theorem B1515901 : Blo 896573 1515901 := bbase (se 3 (by rfl) ⟨284231, by rfl⟩ : syracuseStep 1515901 = 568463) (by norm_num)
theorem B5120405 : Blo 896573 5120405 := bbase (se 6 (by rfl) ⟨120009, by rfl⟩ : syracuseStep 5120405 = 240019) (by norm_num)
theorem B958897 : Blo 896573 958897 := bbase (se 2 (by rfl) ⟨359586, by rfl⟩ : syracuseStep 958897 = 719173) (by norm_num)
theorem B1515989 : Blo 896573 1515989 := bbase (se 7 (by rfl) ⟨17765, by rfl⟩ : syracuseStep 1515989 = 35531) (by norm_num)
theorem B2269741 : Blo 896573 2269741 := bbase (se 3 (by rfl) ⟨425576, by rfl⟩ : syracuseStep 2269741 = 851153) (by norm_num)
theorem B1516117 : Blo 896573 1516117 := bbase (se 8 (by rfl) ⟨8883, by rfl⟩ : syracuseStep 1516117 = 17767) (by norm_num)
theorem B39428693 : Blo 896573 39428693 := bbase (se 8 (by rfl) ⟨231027, by rfl⟩ : syracuseStep 39428693 = 462055) (by norm_num)
theorem B959077 : Blo 896573 959077 := bbase (se 4 (by rfl) ⟨89913, by rfl⟩ : syracuseStep 959077 = 179827) (by norm_num)
theorem B2433653 : Blo 896573 2433653 := bbase (se 5 (by rfl) ⟨114077, by rfl⟩ : syracuseStep 2433653 = 228155) (by norm_num)
theorem B2269853 : Blo 896573 2269853 := bbase (se 3 (by rfl) ⟨425597, by rfl⟩ : syracuseStep 2269853 = 851195) (by norm_num)
theorem B1516205 : Blo 896573 1516205 := bbase (se 3 (by rfl) ⟨284288, by rfl⟩ : syracuseStep 1516205 = 568577) (by norm_num)
theorem B13837013 : Blo 896573 13837013 := bbase (se 7 (by rfl) ⟨162152, by rfl⟩ : syracuseStep 13837013 = 324305) (by norm_num)
theorem B1516333 : Blo 896573 1516333 := bbase (se 3 (by rfl) ⟨284312, by rfl⟩ : syracuseStep 1516333 = 568625) (by norm_num)
theorem B2270045 : Blo 896573 2270045 := bbase (se 3 (by rfl) ⟨425633, by rfl⟩ : syracuseStep 2270045 = 851267) (by norm_num)
theorem B1516421 : Blo 896573 1516421 := bbase (se 4 (by rfl) ⟨142164, by rfl⟩ : syracuseStep 1516421 = 284329) (by norm_num)
theorem B1516549 : Blo 896573 1516549 := bbase (se 4 (by rfl) ⟨142176, by rfl⟩ : syracuseStep 1516549 = 284353) (by norm_num)
theorem B959521 : Blo 896573 959521 := bbase (se 2 (by rfl) ⟨359820, by rfl⟩ : syracuseStep 959521 = 719641) (by norm_num)
theorem B3417173 : Blo 896573 3417173 := bbase (se 8 (by rfl) ⟨20022, by rfl⟩ : syracuseStep 3417173 = 40045) (by norm_num)
theorem B1516637 : Blo 896573 1516637 := bbase (se 3 (by rfl) ⟨284369, by rfl⟩ : syracuseStep 1516637 = 568739) (by norm_num)
theorem B3286165 : Blo 896573 3286165 := bbase (se 6 (by rfl) ⟨77019, by rfl⟩ : syracuseStep 3286165 = 154039) (by norm_num)
theorem B959645 : Blo 896573 959645 := bbase (se 3 (by rfl) ⟨179933, by rfl⟩ : syracuseStep 959645 = 359867) (by norm_num)
theorem B2270389 : Blo 896573 2270389 := bbase (se 5 (by rfl) ⟨106424, by rfl⟩ : syracuseStep 2270389 = 212849) (by norm_num)
theorem B1516765 : Blo 896573 1516765 := bbase (se 3 (by rfl) ⟨284393, by rfl⟩ : syracuseStep 1516765 = 568787) (by norm_num)
theorem B2303213 : Blo 896573 2303213 := bbase (se 3 (by rfl) ⟨431852, by rfl⟩ : syracuseStep 2303213 = 863705) (by norm_num)
theorem B2270501 : Blo 896573 2270501 := bbase (se 4 (by rfl) ⟨212859, by rfl⟩ : syracuseStep 2270501 = 425719) (by norm_num)
theorem B1516853 : Blo 896573 1516853 := bbase (se 5 (by rfl) ⟨71102, by rfl⟩ : syracuseStep 1516853 = 142205) (by norm_num)
theorem B3417461 : Blo 896573 3417461 := bbase (se 5 (by rfl) ⟨160193, by rfl⟩ : syracuseStep 3417461 = 320387) (by norm_num)
theorem B959897 : Blo 896573 959897 := bbase (se 2 (by rfl) ⟨359961, by rfl⟩ : syracuseStep 959897 = 719923) (by norm_num)
theorem B1516981 : Blo 896573 1516981 := bbase (se 5 (by rfl) ⟨71108, by rfl⟩ : syracuseStep 1516981 = 142217) (by norm_num)
theorem B2270693 : Blo 896573 2270693 := bbase (se 4 (by rfl) ⟨212877, by rfl⟩ : syracuseStep 2270693 = 425755) (by norm_num)
theorem B2336261 : Blo 896573 2336261 := bbase (se 4 (by rfl) ⟨219024, by rfl⟩ : syracuseStep 2336261 = 438049) (by norm_num)
theorem B1517069 : Blo 896573 1517069 := bbase (se 3 (by rfl) ⟨284450, by rfl⟩ : syracuseStep 1517069 = 568901) (by norm_num)
theorem B5121589 : Blo 896573 5121589 := bbase (se 5 (by rfl) ⟨240074, by rfl⟩ : syracuseStep 5121589 = 480149) (by norm_num)
theorem B1517197 : Blo 896573 1517197 := bbase (se 3 (by rfl) ⟨284474, by rfl⟩ : syracuseStep 1517197 = 568949) (by norm_num)
theorem B1517285 : Blo 896573 1517285 := bbase (se 4 (by rfl) ⟨142245, by rfl⟩ : syracuseStep 1517285 = 284491) (by norm_num)
theorem B2271037 : Blo 896573 2271037 := bbase (se 3 (by rfl) ⟨425819, by rfl⟩ : syracuseStep 2271037 = 851639) (by norm_num)
theorem B960341 : Blo 896573 960341 := bbase (se 9 (by rfl) ⟨2813, by rfl⟩ : syracuseStep 960341 = 5627) (by norm_num)
theorem B1517413 : Blo 896573 1517413 := bbase (se 4 (by rfl) ⟨142257, by rfl⟩ : syracuseStep 1517413 = 284515) (by norm_num)
theorem B2074493 : Blo 896573 2074493 := bbase (se 3 (by rfl) ⟨388967, by rfl⟩ : syracuseStep 2074493 = 777935) (by norm_num)
theorem B2271149 : Blo 896573 2271149 := bbase (se 3 (by rfl) ⟨425840, by rfl⟩ : syracuseStep 2271149 = 851681) (by norm_num)
theorem B1517501 : Blo 896573 1517501 := bbase (se 3 (by rfl) ⟨284531, by rfl⟩ : syracuseStep 1517501 = 569063) (by norm_num)
theorem B1517629 : Blo 896573 1517629 := bbase (se 3 (by rfl) ⟨284555, by rfl⟩ : syracuseStep 1517629 = 569111) (by norm_num)
theorem B960589 : Blo 896573 960589 := bbase (se 3 (by rfl) ⟨180110, by rfl⟩ : syracuseStep 960589 = 360221) (by norm_num)
theorem B2271341 : Blo 896573 2271341 := bbase (se 3 (by rfl) ⟨425876, by rfl⟩ : syracuseStep 2271341 = 851753) (by norm_num)
theorem B1517717 : Blo 896573 1517717 := bbase (se 6 (by rfl) ⟨35571, by rfl⟩ : syracuseStep 1517717 = 71143) (by norm_num)
theorem B1517845 : Blo 896573 1517845 := bbase (se 6 (by rfl) ⟨35574, by rfl⟩ : syracuseStep 1517845 = 71149) (by norm_num)
theorem B3451189 : Blo 896573 3451189 := bbase (se 5 (by rfl) ⟨161774, by rfl⟩ : syracuseStep 3451189 = 323549) (by norm_num)
theorem B1517933 : Blo 896573 1517933 := bbase (se 3 (by rfl) ⟨284612, by rfl⟩ : syracuseStep 1517933 = 569225) (by norm_num)
theorem B2271685 : Blo 896573 2271685 := bbase (se 4 (by rfl) ⟨212970, by rfl⟩ : syracuseStep 2271685 = 425941) (by norm_num)
theorem B7678421 : Blo 896573 7678421 := bbase (se 7 (by rfl) ⟨89981, by rfl⟩ : syracuseStep 7678421 = 179963) (by norm_num)
theorem B1518061 : Blo 896573 1518061 := bbase (se 3 (by rfl) ⟨284636, by rfl⟩ : syracuseStep 1518061 = 569273) (by norm_num)
theorem B961033 : Blo 896573 961033 := bbase (se 2 (by rfl) ⟨360387, by rfl⟩ : syracuseStep 961033 = 720775) (by norm_num)
theorem B3418645 : Blo 896573 3418645 := bbase (se 6 (by rfl) ⟨80124, by rfl⟩ : syracuseStep 3418645 = 160249) (by norm_num)
theorem B1944101 : Blo 896573 1944101 := bbase (se 4 (by rfl) ⟨182259, by rfl⟩ : syracuseStep 1944101 = 364519) (by norm_num)
theorem B2271797 : Blo 896573 2271797 := bbase (se 5 (by rfl) ⟨106490, by rfl⟩ : syracuseStep 2271797 = 212981) (by norm_num)
theorem B1518149 : Blo 896573 1518149 := bbase (se 4 (by rfl) ⟨142326, by rfl⟩ : syracuseStep 1518149 = 284653) (by norm_num)
theorem B961093 : Blo 896573 961093 := bbase (se 4 (by rfl) ⟨90102, by rfl⟩ : syracuseStep 961093 = 180205) (by norm_num)
theorem B1616525 : Blo 896573 1616525 := bbase (se 3 (by rfl) ⟨303098, by rfl⟩ : syracuseStep 1616525 = 606197) (by norm_num)
theorem B1518277 : Blo 896573 1518277 := bbase (se 4 (by rfl) ⟨142338, by rfl⟩ : syracuseStep 1518277 = 284677) (by norm_num)
theorem B2271989 : Blo 896573 2271989 := bbase (se 5 (by rfl) ⟨106499, by rfl⟩ : syracuseStep 2271989 = 212999) (by norm_num)
theorem B1518365 : Blo 896573 1518365 := bbase (se 3 (by rfl) ⟨284693, by rfl⟩ : syracuseStep 1518365 = 569387) (by norm_num)
theorem B3418949 : Blo 896573 3418949 := bbase (se 4 (by rfl) ⟨320526, by rfl⟩ : syracuseStep 3418949 = 641053) (by norm_num)
theorem B961409 : Blo 896573 961409 := bbase (se 2 (by rfl) ⟨360528, by rfl⟩ : syracuseStep 961409 = 721057) (by norm_num)
theorem B1518493 : Blo 896573 1518493 := bbase (se 3 (by rfl) ⟨284717, by rfl⟩ : syracuseStep 1518493 = 569435) (by norm_num)
theorem B1518581 : Blo 896573 1518581 := bbase (se 5 (by rfl) ⟨71183, by rfl⟩ : syracuseStep 1518581 = 142367) (by norm_num)
theorem B3845141 : Blo 896573 3845141 := bbase (se 6 (by rfl) ⟨90120, by rfl⟩ : syracuseStep 3845141 = 180241) (by norm_num)
theorem B2272333 : Blo 896573 2272333 := bbase (se 3 (by rfl) ⟨426062, by rfl⟩ : syracuseStep 2272333 = 852125) (by norm_num)
theorem B1518709 : Blo 896573 1518709 := bbase (se 5 (by rfl) ⟨71189, by rfl⟩ : syracuseStep 1518709 = 142379) (by norm_num)
theorem B2272445 : Blo 896573 2272445 := bbase (se 3 (by rfl) ⟨426083, by rfl⟩ : syracuseStep 2272445 = 852167) (by norm_num)
theorem B1518797 : Blo 896573 1518797 := bbase (se 3 (by rfl) ⟨284774, by rfl⟩ : syracuseStep 1518797 = 569549) (by norm_num)
theorem B3026213 : Blo 896573 3026213 := bbase (se 4 (by rfl) ⟨283707, by rfl⟩ : syracuseStep 3026213 = 567415) (by norm_num)
theorem B1518925 : Blo 896573 1518925 := bbase (se 3 (by rfl) ⟨284798, by rfl⟩ : syracuseStep 1518925 = 569597) (by norm_num)
theorem B2272637 : Blo 896573 2272637 := bbase (se 3 (by rfl) ⟨426119, by rfl⟩ : syracuseStep 2272637 = 852239) (by norm_num)
theorem B1519013 : Blo 896573 1519013 := bbase (se 4 (by rfl) ⟨142407, by rfl⟩ : syracuseStep 1519013 = 284815) (by norm_num)
theorem B3452357 : Blo 896573 3452357 := bbase (se 4 (by rfl) ⟨323658, by rfl⟩ : syracuseStep 3452357 = 647317) (by norm_num)
theorem B1617389 : Blo 896573 1617389 := bbase (se 3 (by rfl) ⟨303260, by rfl⟩ : syracuseStep 1617389 = 606521) (by norm_num)
theorem B5123573 : Blo 896573 5123573 := bbase (se 5 (by rfl) ⟨240167, by rfl⟩ : syracuseStep 5123573 = 480335) (by norm_num)
theorem B1519141 : Blo 896573 1519141 := bbase (se 4 (by rfl) ⟨142419, by rfl⟩ : syracuseStep 1519141 = 284839) (by norm_num)
theorem B10923605 : Blo 896573 10923605 := bbase (se 8 (by rfl) ⟨64005, by rfl⟩ : syracuseStep 10923605 = 128011) (by norm_num)
theorem B1519229 : Blo 896573 1519229 := bbase (se 3 (by rfl) ⟨284855, by rfl⟩ : syracuseStep 1519229 = 569711) (by norm_num)
theorem B3026645 : Blo 896573 3026645 := bbase (se 7 (by rfl) ⟨35468, by rfl⟩ : syracuseStep 3026645 = 70937) (by norm_num)
theorem B2272981 : Blo 896573 2272981 := bbase (se 7 (by rfl) ⟨26636, by rfl⟩ : syracuseStep 2272981 = 53273) (by norm_num)
theorem B1519357 : Blo 896573 1519357 := bbase (se 3 (by rfl) ⟨284879, by rfl⟩ : syracuseStep 1519357 = 569759) (by norm_num)
theorem B1093441 : Blo 896573 1093441 := bbase (se 2 (by rfl) ⟨410040, by rfl⟩ : syracuseStep 1093441 = 820081) (by norm_num)
theorem B2273093 : Blo 896573 2273093 := bbase (se 4 (by rfl) ⟨213102, by rfl⟩ : syracuseStep 2273093 = 426205) (by norm_num)
theorem B1519445 : Blo 896573 1519445 := bbase (se 9 (by rfl) ⟨4451, by rfl⟩ : syracuseStep 1519445 = 8903) (by norm_num)
theorem B1519573 : Blo 896573 1519573 := bbase (se 7 (by rfl) ⟨17807, by rfl⟩ : syracuseStep 1519573 = 35615) (by norm_num)
theorem B2273285 : Blo 896573 2273285 := bbase (se 4 (by rfl) ⟨213120, by rfl⟩ : syracuseStep 2273285 = 426241) (by norm_num)
theorem B3846149 : Blo 896573 3846149 := bbase (se 4 (by rfl) ⟨360576, by rfl⟩ : syracuseStep 3846149 = 721153) (by norm_num)
theorem B1519661 : Blo 896573 1519661 := bbase (se 3 (by rfl) ⟨284936, by rfl⟩ : syracuseStep 1519661 = 569873) (by norm_num)
theorem B3649637 : Blo 896573 3649637 := bbase (se 4 (by rfl) ⟨342153, by rfl⟩ : syracuseStep 3649637 = 684307) (by norm_num)
theorem B3027077 : Blo 896573 3027077 := bbase (se 4 (by rfl) ⟨283788, by rfl⟩ : syracuseStep 3027077 = 567577) (by norm_num)
theorem B2273629 : Blo 896573 2273629 := bbase (se 3 (by rfl) ⟨426305, by rfl⟩ : syracuseStep 2273629 = 852611) (by norm_num)
theorem B2273741 : Blo 896573 2273741 := bbase (se 3 (by rfl) ⟨426326, by rfl⟩ : syracuseStep 2273741 = 852653) (by norm_num)
theorem B3027509 : Blo 896573 3027509 := bbase (se 5 (by rfl) ⟨141914, by rfl⟩ : syracuseStep 3027509 = 283829) (by norm_num)
theorem B2273933 : Blo 896573 2273933 := bbase (se 3 (by rfl) ⟨426362, by rfl⟩ : syracuseStep 2273933 = 852725) (by norm_num)
theorem B1618717 : Blo 896573 1618717 := bbase (se 3 (by rfl) ⟨303509, by rfl⟩ : syracuseStep 1618717 = 607019) (by norm_num)
theorem B1618861 : Blo 896573 1618861 := bbase (se 3 (by rfl) ⟨303536, by rfl⟩ : syracuseStep 1618861 = 607073) (by norm_num)
theorem B3027941 : Blo 896573 3027941 := bbase (se 4 (by rfl) ⟨283869, by rfl⟩ : syracuseStep 3027941 = 567739) (by norm_num)
theorem B2274277 : Blo 896573 2274277 := bbase (se 4 (by rfl) ⟨213213, by rfl⟩ : syracuseStep 2274277 = 426427) (by norm_num)
theorem B2274389 : Blo 896573 2274389 := bbase (se 8 (by rfl) ⟨13326, by rfl⟩ : syracuseStep 2274389 = 26653) (by norm_num)
theorem B3650741 : Blo 896573 3650741 := bbase (se 5 (by rfl) ⟨171128, by rfl⟩ : syracuseStep 3650741 = 342257) (by norm_num)
theorem B2274581 : Blo 896573 2274581 := bbase (se 6 (by rfl) ⟨53310, by rfl⟩ : syracuseStep 2274581 = 106621) (by norm_num)
theorem B1946933 : Blo 896573 1946933 := bbase (se 5 (by rfl) ⟨91262, by rfl⟩ : syracuseStep 1946933 = 182525) (by norm_num)
theorem B1619293 : Blo 896573 1619293 := bbase (se 3 (by rfl) ⟨303617, by rfl⟩ : syracuseStep 1619293 = 607235) (by norm_num)
theorem B3028373 : Blo 896573 3028373 := bbase (se 6 (by rfl) ⟨70977, by rfl⟩ : syracuseStep 3028373 = 141955) (by norm_num)
theorem B2274925 : Blo 896573 2274925 := bbase (se 3 (by rfl) ⟨426548, by rfl⟩ : syracuseStep 2274925 = 853097) (by norm_num)
theorem B1619581 : Blo 896573 1619581 := bbase (se 3 (by rfl) ⟨303671, by rfl⟩ : syracuseStep 1619581 = 607343) (by norm_num)
theorem B5125781 : Blo 896573 5125781 := bbase (se 6 (by rfl) ⟨120135, by rfl⟩ : syracuseStep 5125781 = 240271) (by norm_num)
theorem B2275037 : Blo 896573 2275037 := bbase (se 3 (by rfl) ⟨426569, by rfl⟩ : syracuseStep 2275037 = 853139) (by norm_num)
theorem B3028805 : Blo 896573 3028805 := bbase (se 4 (by rfl) ⟨283950, by rfl⟩ : syracuseStep 3028805 = 567901) (by norm_num)
theorem B2275229 : Blo 896573 2275229 := bbase (se 3 (by rfl) ⟨426605, by rfl⟩ : syracuseStep 2275229 = 853211) (by norm_num)
theorem B1914941 : Blo 896573 1914941 := bbase (se 3 (by rfl) ⟨359051, by rfl⟩ : syracuseStep 1914941 = 718103) (by norm_num)
theorem B1095773 : Blo 896573 1095773 := bbase (se 3 (by rfl) ⟨205457, by rfl⟩ : syracuseStep 1095773 = 410915) (by norm_num)
theorem B2046053 : Blo 896573 2046053 := bbase (se 4 (by rfl) ⟨191817, by rfl⟩ : syracuseStep 2046053 = 383635) (by norm_num)
theorem B1620101 : Blo 896573 1620101 := bbase (se 4 (by rfl) ⟨151884, by rfl⟩ : syracuseStep 1620101 = 303769) (by norm_num)
theorem B3029237 : Blo 896573 3029237 := bbase (se 5 (by rfl) ⟨141995, by rfl⟩ : syracuseStep 3029237 = 283991) (by norm_num)
theorem B2275573 : Blo 896573 2275573 := bbase (se 5 (by rfl) ⟨106667, by rfl⟩ : syracuseStep 2275573 = 213335) (by norm_num)
theorem B1620245 : Blo 896573 1620245 := bbase (se 6 (by rfl) ⟨37974, by rfl⟩ : syracuseStep 1620245 = 75949) (by norm_num)
theorem B1849645 : Blo 896573 1849645 := bbase (se 3 (by rfl) ⟨346808, by rfl⟩ : syracuseStep 1849645 = 693617) (by norm_num)
theorem B2275685 : Blo 896573 2275685 := bbase (se 4 (by rfl) ⟨213345, by rfl⟩ : syracuseStep 2275685 = 426691) (by norm_num)
theorem B2308541 : Blo 896573 2308541 := bbase (se 3 (by rfl) ⟨432851, by rfl⟩ : syracuseStep 2308541 = 865703) (by norm_num)
theorem B1620461 : Blo 896573 1620461 := bbase (se 3 (by rfl) ⟨303836, by rfl⟩ : syracuseStep 1620461 = 607673) (by norm_num)
theorem B2275877 : Blo 896573 2275877 := bbase (se 4 (by rfl) ⟨213363, by rfl⟩ : syracuseStep 2275877 = 426727) (by norm_num)
theorem B1620533 : Blo 896573 1620533 := bbase (se 5 (by rfl) ⟨75962, by rfl⟩ : syracuseStep 1620533 = 151925) (by norm_num)
theorem B2964053 : Blo 896573 2964053 := bbase (se 8 (by rfl) ⟨17367, by rfl⟩ : syracuseStep 2964053 = 34735) (by norm_num)
theorem B3029669 : Blo 896573 3029669 := bbase (se 4 (by rfl) ⟨284031, by rfl⟩ : syracuseStep 3029669 = 568063) (by norm_num)
theorem B2276221 : Blo 896573 2276221 := bbase (se 3 (by rfl) ⟨426791, by rfl⟩ : syracuseStep 2276221 = 853583) (by norm_num)
theorem B1915805 : Blo 896573 1915805 := bbase (se 3 (by rfl) ⟨359213, by rfl⟩ : syracuseStep 1915805 = 718427) (by norm_num)
theorem B1620901 : Blo 896573 1620901 := bbase (se 4 (by rfl) ⟨151959, by rfl⟩ : syracuseStep 1620901 = 303919) (by norm_num)
theorem B2276333 : Blo 896573 2276333 := bbase (se 3 (by rfl) ⟨426812, by rfl⟩ : syracuseStep 2276333 = 853625) (by norm_num)
theorem B2046973 : Blo 896573 2046973 := bbase (se 3 (by rfl) ⟨383807, by rfl⟩ : syracuseStep 2046973 = 767615) (by norm_num)
theorem B1915949 : Blo 896573 1915949 := bbase (se 3 (by rfl) ⟨359240, by rfl⟩ : syracuseStep 1915949 = 718481) (by norm_num)
theorem B3030101 : Blo 896573 3030101 := bbase (se 8 (by rfl) ⟨17754, by rfl⟩ : syracuseStep 3030101 = 35509) (by norm_num)
theorem B2276525 : Blo 896573 2276525 := bbase (se 3 (by rfl) ⟨426848, by rfl⟩ : syracuseStep 2276525 = 853697) (by norm_num)
theorem B2735477 : Blo 896573 2735477 := bbase (se 5 (by rfl) ⟨128225, by rfl⟩ : syracuseStep 2735477 = 256451) (by norm_num)
theorem B2735525 : Blo 896573 2735525 := bbase (se 4 (by rfl) ⟨256455, by rfl⟩ : syracuseStep 2735525 = 512911) (by norm_num)
theorem B3030533 : Blo 896573 3030533 := bbase (se 4 (by rfl) ⟨284112, by rfl⟩ : syracuseStep 3030533 = 568225) (by norm_num)
theorem B2276869 : Blo 896573 2276869 := bbase (se 4 (by rfl) ⟨213456, by rfl⟩ : syracuseStep 2276869 = 426913) (by norm_num)
theorem B4439573 : Blo 896573 4439573 := bbase (se 6 (by rfl) ⟨104052, by rfl⟩ : syracuseStep 4439573 = 208105) (by norm_num)
theorem B1621541 : Blo 896573 1621541 := bbase (se 4 (by rfl) ⟨152019, by rfl⟩ : syracuseStep 1621541 = 304039) (by norm_num)
theorem B6831701 : Blo 896573 6831701 := bbase (se 8 (by rfl) ⟨40029, by rfl⟩ : syracuseStep 6831701 = 80059) (by norm_num)
theorem B2276981 : Blo 896573 2276981 := bbase (se 5 (by rfl) ⟨106733, by rfl⟩ : syracuseStep 2276981 = 213467) (by norm_num)
theorem B1916693 : Blo 896573 1916693 := bbase (se 6 (by rfl) ⟨44922, by rfl⟩ : syracuseStep 1916693 = 89845) (by norm_num)
theorem B2277173 : Blo 896573 2277173 := bbase (se 5 (by rfl) ⟨106742, by rfl⟩ : syracuseStep 2277173 = 213485) (by norm_num)
theorem B4308869 : Blo 896573 4308869 := bbase (se 4 (by rfl) ⟨403956, by rfl⟩ : syracuseStep 4308869 = 807913) (by norm_num)
theorem B3030965 : Blo 896573 3030965 := bbase (se 5 (by rfl) ⟨142076, by rfl⟩ : syracuseStep 3030965 = 284153) (by norm_num)
theorem B2277517 : Blo 896573 2277517 := bbase (se 3 (by rfl) ⟨427034, by rfl⟩ : syracuseStep 2277517 = 854069) (by norm_num)
theorem B2277629 : Blo 896573 2277629 := bbase (se 3 (by rfl) ⟨427055, by rfl⟩ : syracuseStep 2277629 = 854111) (by norm_num)
theorem B1622285 : Blo 896573 1622285 := bbase (se 3 (by rfl) ⟨304178, by rfl⟩ : syracuseStep 1622285 = 608357) (by norm_num)
theorem B7389461 : Blo 896573 7389461 := bbase (se 6 (by rfl) ⟨173190, by rfl⟩ : syracuseStep 7389461 = 346381) (by norm_num)
theorem B2736437 : Blo 896573 2736437 := bbase (se 5 (by rfl) ⟨128270, by rfl⟩ : syracuseStep 2736437 = 256541) (by norm_num)
theorem B1818949 : Blo 896573 1818949 := bbase (se 4 (by rfl) ⟨170526, by rfl⟩ : syracuseStep 1818949 = 341053) (by norm_num)
theorem B3031397 : Blo 896573 3031397 := bbase (se 4 (by rfl) ⟨284193, by rfl⟩ : syracuseStep 3031397 = 568387) (by norm_num)
theorem B1458589 : Blo 896573 1458589 := bbase (se 3 (by rfl) ⟨273485, by rfl⟩ : syracuseStep 1458589 = 546971) (by norm_num)
theorem B2277821 : Blo 896573 2277821 := bbase (se 3 (by rfl) ⟨427091, by rfl⟩ : syracuseStep 2277821 = 854183) (by norm_num)
theorem B1917445 : Blo 896573 1917445 := bbase (se 4 (by rfl) ⟨179760, by rfl⟩ : syracuseStep 1917445 = 359521) (by norm_num)
theorem B1917589 : Blo 896573 1917589 := bbase (se 6 (by rfl) ⟨44943, by rfl⟩ : syracuseStep 1917589 = 89887) (by norm_num)
theorem B4539077 : Blo 896573 4539077 := bbase (se 4 (by rfl) ⟨425538, by rfl⟩ : syracuseStep 4539077 = 851077) (by norm_num)
theorem B3031829 : Blo 896573 3031829 := bbase (se 6 (by rfl) ⟨71058, by rfl⟩ : syracuseStep 3031829 = 142117) (by norm_num)
theorem B2278165 : Blo 896573 2278165 := bbase (se 6 (by rfl) ⟨53394, by rfl⟩ : syracuseStep 2278165 = 106789) (by norm_num)
theorem B1459037 : Blo 896573 1459037 := bbase (se 3 (by rfl) ⟨273569, by rfl⟩ : syracuseStep 1459037 = 547139) (by norm_num)
theorem B2278277 : Blo 896573 2278277 := bbase (se 4 (by rfl) ⟨213588, by rfl⟩ : syracuseStep 2278277 = 427177) (by norm_num)
theorem B1917965 : Blo 896573 1917965 := bbase (se 3 (by rfl) ⟨359618, by rfl⟩ : syracuseStep 1917965 = 719237) (by norm_num)
theorem B2278469 : Blo 896573 2278469 := bbase (se 4 (by rfl) ⟨213606, by rfl⟩ : syracuseStep 2278469 = 427213) (by norm_num)
theorem B4310117 : Blo 896573 4310117 := bbase (se 4 (by rfl) ⟨404073, by rfl⟩ : syracuseStep 4310117 = 808147) (by norm_num)
theorem B3032261 : Blo 896573 3032261 := bbase (se 4 (by rfl) ⟨284274, by rfl⟩ : syracuseStep 3032261 = 568549) (by norm_num)
theorem B1918333 : Blo 896573 1918333 := bbase (se 3 (by rfl) ⟨359687, by rfl⟩ : syracuseStep 1918333 = 719375) (by norm_num)
theorem B2278813 : Blo 896573 2278813 := bbase (se 3 (by rfl) ⟨427277, by rfl⟩ : syracuseStep 2278813 = 854555) (by norm_num)
theorem B2278925 : Blo 896573 2278925 := bbase (se 3 (by rfl) ⟨427298, by rfl⟩ : syracuseStep 2278925 = 854597) (by norm_num)
theorem B26297941 : Blo 896573 26297941 := bbase (se 8 (by rfl) ⟨154089, by rfl⟩ : syracuseStep 26297941 = 308179) (by norm_num)
theorem B2049637 : Blo 896573 2049637 := bbase (se 4 (by rfl) ⟨192153, by rfl⟩ : syracuseStep 2049637 = 384307) (by norm_num)
theorem B3032693 : Blo 896573 3032693 := bbase (se 5 (by rfl) ⟨142157, by rfl⟩ : syracuseStep 3032693 = 284315) (by norm_num)
theorem B2049709 : Blo 896573 2049709 := bbase (se 3 (by rfl) ⟨384320, by rfl⟩ : syracuseStep 2049709 = 768641) (by norm_num)
theorem B2279117 : Blo 896573 2279117 := bbase (se 3 (by rfl) ⟨427334, by rfl⟩ : syracuseStep 2279117 = 854669) (by norm_num)
theorem B4540373 : Blo 896573 4540373 := bbase (se 7 (by rfl) ⟨53207, by rfl⟩ : syracuseStep 4540373 = 106415) (by norm_num)
theorem B3033125 : Blo 896573 3033125 := bbase (se 4 (by rfl) ⟨284355, by rfl⟩ : syracuseStep 3033125 = 568711) (by norm_num)
theorem B2279461 : Blo 896573 2279461 := bbase (se 4 (by rfl) ⟨213699, by rfl⟩ : syracuseStep 2279461 = 427399) (by norm_num)
theorem B2017349 : Blo 896573 2017349 := bbase (se 4 (by rfl) ⟨189126, by rfl⟩ : syracuseStep 2017349 = 378253) (by norm_num)
theorem B2017421 : Blo 896573 2017421 := bbase (se 3 (by rfl) ⟨378266, by rfl⟩ : syracuseStep 2017421 = 756533) (by norm_num)
theorem B2279573 : Blo 896573 2279573 := bbase (se 6 (by rfl) ⟨53427, by rfl⟩ : syracuseStep 2279573 = 106855) (by norm_num)
theorem B1820861 : Blo 896573 1820861 := bbase (se 3 (by rfl) ⟨341411, by rfl⟩ : syracuseStep 1820861 = 682823) (by norm_num)
theorem B2017493 : Blo 896573 2017493 := bbase (se 7 (by rfl) ⟨23642, by rfl⟩ : syracuseStep 2017493 = 47285) (by norm_num)
theorem B2017565 : Blo 896573 2017565 := bbase (se 3 (by rfl) ⟨378293, by rfl⟩ : syracuseStep 2017565 = 756587) (by norm_num)
theorem B7686485 : Blo 896573 7686485 := bbase (se 10 (by rfl) ⟨11259, by rfl⟩ : syracuseStep 7686485 = 22519) (by norm_num)
theorem B2017637 : Blo 896573 2017637 := bbase (se 4 (by rfl) ⟨189153, by rfl⟩ : syracuseStep 2017637 = 378307) (by norm_num)
theorem B2017709 : Blo 896573 2017709 := bbase (se 3 (by rfl) ⟨378320, by rfl⟩ : syracuseStep 2017709 = 756641) (by norm_num)
theorem B6244789 : Blo 896573 6244789 := bbase (se 5 (by rfl) ⟨292724, by rfl⟩ : syracuseStep 6244789 = 585449) (by norm_num)
theorem B3033557 : Blo 896573 3033557 := bbase (se 7 (by rfl) ⟨35549, by rfl⟩ : syracuseStep 3033557 = 71099) (by norm_num)
theorem B2017781 : Blo 896573 2017781 := bbase (se 5 (by rfl) ⟨94583, by rfl⟩ : syracuseStep 2017781 = 189167) (by norm_num)
theorem B2017853 : Blo 896573 2017853 := bbase (se 3 (by rfl) ⟨378347, by rfl⟩ : syracuseStep 2017853 = 756695) (by norm_num)
theorem B2017925 : Blo 896573 2017925 := bbase (se 4 (by rfl) ⟨189180, by rfl⟩ : syracuseStep 2017925 = 378361) (by norm_num)
theorem B2017997 : Blo 896573 2017997 := bbase (se 3 (by rfl) ⟨378374, by rfl⟩ : syracuseStep 2017997 = 756749) (by norm_num)
theorem B2018069 : Blo 896573 2018069 := bbase (se 6 (by rfl) ⟨47298, by rfl⟩ : syracuseStep 2018069 = 94597) (by norm_num)
theorem B4606757 : Blo 896573 4606757 := bbase (se 4 (by rfl) ⟨431883, by rfl⟩ : syracuseStep 4606757 = 863767) (by norm_num)
theorem B1821509 : Blo 896573 1821509 := bbase (se 4 (by rfl) ⟨170766, by rfl⟩ : syracuseStep 1821509 = 341533) (by norm_num)
theorem B2018141 : Blo 896573 2018141 := bbase (se 3 (by rfl) ⟨378401, by rfl⟩ : syracuseStep 2018141 = 756803) (by norm_num)
theorem B1919837 : Blo 896573 1919837 := bbase (se 3 (by rfl) ⟨359969, by rfl⟩ : syracuseStep 1919837 = 719939) (by norm_num)
theorem B3033989 : Blo 896573 3033989 := bbase (se 4 (by rfl) ⟨284436, by rfl⟩ : syracuseStep 3033989 = 568873) (by norm_num)
theorem B2018213 : Blo 896573 2018213 := bbase (se 4 (by rfl) ⟨189207, by rfl⟩ : syracuseStep 2018213 = 378415) (by norm_num)
theorem B2018285 : Blo 896573 2018285 := bbase (se 3 (by rfl) ⟨378428, by rfl⟩ : syracuseStep 2018285 = 756857) (by norm_num)
theorem B1919981 : Blo 896573 1919981 := bbase (se 3 (by rfl) ⟨359996, by rfl⟩ : syracuseStep 1919981 = 719993) (by norm_num)
theorem B2018357 : Blo 896573 2018357 := bbase (se 5 (by rfl) ⟨94610, by rfl⟩ : syracuseStep 2018357 = 189221) (by norm_num)
theorem B2018429 : Blo 896573 2018429 := bbase (se 3 (by rfl) ⟨378455, by rfl⟩ : syracuseStep 2018429 = 756911) (by norm_num)
theorem B2018501 : Blo 896573 2018501 := bbase (se 4 (by rfl) ⟨189234, by rfl⟩ : syracuseStep 2018501 = 378469) (by norm_num)
theorem B4541669 : Blo 896573 4541669 := bbase (se 4 (by rfl) ⟨425781, by rfl⟩ : syracuseStep 4541669 = 851563) (by norm_num)
theorem B2018573 : Blo 896573 2018573 := bbase (se 3 (by rfl) ⟨378482, by rfl⟩ : syracuseStep 2018573 = 756965) (by norm_num)
theorem B3034421 : Blo 896573 3034421 := bbase (se 5 (by rfl) ⟨142238, by rfl⟩ : syracuseStep 3034421 = 284477) (by norm_num)
theorem B1461557 : Blo 896573 1461557 := bbase (se 5 (by rfl) ⟨68510, by rfl⟩ : syracuseStep 1461557 = 137021) (by norm_num)
theorem B2018645 : Blo 896573 2018645 := bbase (se 11 (by rfl) ⟨1478, by rfl⟩ : syracuseStep 2018645 = 2957) (by norm_num)
theorem B1920341 : Blo 896573 1920341 := bbase (se 11 (by rfl) ⟨1406, by rfl⟩ : syracuseStep 1920341 = 2813) (by norm_num)
theorem B2018717 : Blo 896573 2018717 := bbase (se 3 (by rfl) ⟨378509, by rfl⟩ : syracuseStep 2018717 = 757019) (by norm_num)
theorem B2018789 : Blo 896573 2018789 := bbase (se 4 (by rfl) ⟨189261, by rfl⟩ : syracuseStep 2018789 = 378523) (by norm_num)
theorem B2018861 : Blo 896573 2018861 := bbase (se 3 (by rfl) ⟨378536, by rfl⟩ : syracuseStep 2018861 = 757073) (by norm_num)
theorem B2018933 : Blo 896573 2018933 := bbase (se 5 (by rfl) ⟨94637, by rfl⟩ : syracuseStep 2018933 = 189275) (by norm_num)
theorem B2019005 : Blo 896573 2019005 := bbase (se 3 (by rfl) ⟨378563, by rfl⟩ : syracuseStep 2019005 = 757127) (by norm_num)
theorem B3034853 : Blo 896573 3034853 := bbase (se 4 (by rfl) ⟨284517, by rfl⟩ : syracuseStep 3034853 = 569035) (by norm_num)
theorem B4116197 : Blo 896573 4116197 := bbase (se 4 (by rfl) ⟨385893, by rfl⟩ : syracuseStep 4116197 = 771787) (by norm_num)
theorem B2019077 : Blo 896573 2019077 := bbase (se 4 (by rfl) ⟨189288, by rfl⟩ : syracuseStep 2019077 = 378577) (by norm_num)
theorem B4312885 : Blo 896573 4312885 := bbase (se 5 (by rfl) ⟨202166, by rfl⟩ : syracuseStep 4312885 = 404333) (by norm_num)
theorem B2019149 : Blo 896573 2019149 := bbase (se 3 (by rfl) ⟨378590, by rfl⟩ : syracuseStep 2019149 = 757181) (by norm_num)
theorem B1560421 : Blo 896573 1560421 := bbase (se 4 (by rfl) ⟨146289, by rfl⟩ : syracuseStep 1560421 = 292579) (by norm_num)
theorem B2019221 : Blo 896573 2019221 := bbase (se 6 (by rfl) ⟨47325, by rfl⟩ : syracuseStep 2019221 = 94651) (by norm_num)
theorem B2019293 : Blo 896573 2019293 := bbase (se 3 (by rfl) ⟨378617, by rfl⟩ : syracuseStep 2019293 = 757235) (by norm_num)
theorem B970729 : Blo 896573 970729 := bbase (se 2 (by rfl) ⟨364023, by rfl⟩ : syracuseStep 970729 = 728047) (by norm_num)
theorem B2019365 : Blo 896573 2019365 := bbase (se 4 (by rfl) ⟨189315, by rfl⟩ : syracuseStep 2019365 = 378631) (by norm_num)
theorem B2019437 : Blo 896573 2019437 := bbase (se 3 (by rfl) ⟨378644, by rfl⟩ : syracuseStep 2019437 = 757289) (by norm_num)
theorem B3035285 : Blo 896573 3035285 := bbase (se 6 (by rfl) ⟨71139, by rfl⟩ : syracuseStep 3035285 = 142279) (by norm_num)
theorem B1134749 : Blo 896573 1134749 := bbase (se 3 (by rfl) ⟨212765, by rfl⟩ : syracuseStep 1134749 = 425531) (by norm_num)
theorem B2019509 : Blo 896573 2019509 := bbase (se 5 (by rfl) ⟨94664, by rfl⟩ : syracuseStep 2019509 = 189329) (by norm_num)
theorem B1921229 : Blo 896573 1921229 := bbase (se 3 (by rfl) ⟨360230, by rfl⟩ : syracuseStep 1921229 = 720461) (by norm_num)
theorem B1134805 : Blo 896573 1134805 := bbase (se 7 (by rfl) ⟨13298, by rfl⟩ : syracuseStep 1134805 = 26597) (by norm_num)
theorem B2019581 : Blo 896573 2019581 := bbase (se 3 (by rfl) ⟨378671, by rfl⟩ : syracuseStep 2019581 = 757343) (by norm_num)
theorem B1134901 : Blo 896573 1134901 := bbase (se 5 (by rfl) ⟨53198, by rfl⟩ : syracuseStep 1134901 = 106397) (by norm_num)
theorem B2019653 : Blo 896573 2019653 := bbase (se 4 (by rfl) ⟨189342, by rfl⟩ : syracuseStep 2019653 = 378685) (by norm_num)
theorem B2019725 : Blo 896573 2019725 := bbase (se 3 (by rfl) ⟨378698, by rfl⟩ : syracuseStep 2019725 = 757397) (by norm_num)
theorem B1921477 : Blo 896573 1921477 := bbase (se 4 (by rfl) ⟨180138, by rfl⟩ : syracuseStep 1921477 = 360277) (by norm_num)
theorem B2019797 : Blo 896573 2019797 := bbase (se 7 (by rfl) ⟨23669, by rfl⟩ : syracuseStep 2019797 = 47339) (by norm_num)
theorem B1135073 : Blo 896573 1135073 := bbase (se 2 (by rfl) ⟨425652, by rfl⟩ : syracuseStep 1135073 = 851305) (by norm_num)
theorem B4542965 : Blo 896573 4542965 := bbase (se 5 (by rfl) ⟨212951, by rfl⟩ : syracuseStep 4542965 = 425903) (by norm_num)
theorem B18469397 : Blo 896573 18469397 := bbase (se 6 (by rfl) ⟨432876, by rfl⟩ : syracuseStep 18469397 = 865753) (by norm_num)
theorem B1135129 : Blo 896573 1135129 := bbase (se 2 (by rfl) ⟨425673, by rfl⟩ : syracuseStep 1135129 = 851347) (by norm_num)
theorem B2019869 : Blo 896573 2019869 := bbase (se 3 (by rfl) ⟨378725, by rfl⟩ : syracuseStep 2019869 = 757451) (by norm_num)
theorem B3035717 : Blo 896573 3035717 := bbase (se 4 (by rfl) ⟨284598, by rfl⟩ : syracuseStep 3035717 = 569197) (by norm_num)
theorem B2019941 : Blo 896573 2019941 := bbase (se 4 (by rfl) ⟨189369, by rfl⟩ : syracuseStep 2019941 = 378739) (by norm_num)
theorem B1135225 : Blo 896573 1135225 := bbase (se 2 (by rfl) ⟨425709, by rfl⟩ : syracuseStep 1135225 = 851419) (by norm_num)
theorem B2020013 : Blo 896573 2020013 := bbase (se 3 (by rfl) ⟨378752, by rfl⟩ : syracuseStep 2020013 = 757505) (by norm_num)
theorem B2020085 : Blo 896573 2020085 := bbase (se 5 (by rfl) ⟨94691, by rfl⟩ : syracuseStep 2020085 = 189383) (by norm_num)
theorem B5755637 : Blo 896573 5755637 := bbase (se 5 (by rfl) ⟨269795, by rfl⟩ : syracuseStep 5755637 = 539591) (by norm_num)
theorem B1135397 : Blo 896573 1135397 := bbase (se 4 (by rfl) ⟨106443, by rfl⟩ : syracuseStep 1135397 = 212887) (by norm_num)
theorem B6476597 : Blo 896573 6476597 := bbase (se 5 (by rfl) ⟨303590, by rfl⟩ : syracuseStep 6476597 = 607181) (by norm_num)
theorem B2020157 : Blo 896573 2020157 := bbase (se 3 (by rfl) ⟨378779, by rfl⟩ : syracuseStep 2020157 = 757559) (by norm_num)
theorem B1135453 : Blo 896573 1135453 := bbase (se 3 (by rfl) ⟨212897, by rfl⟩ : syracuseStep 1135453 = 425795) (by norm_num)
theorem B2020229 : Blo 896573 2020229 := bbase (se 4 (by rfl) ⟨189396, by rfl⟩ : syracuseStep 2020229 = 378793) (by norm_num)
theorem B1135549 : Blo 896573 1135549 := bbase (se 3 (by rfl) ⟨212915, by rfl⟩ : syracuseStep 1135549 = 425831) (by norm_num)
theorem B1921981 : Blo 896573 1921981 := bbase (se 3 (by rfl) ⟨360371, by rfl⟩ : syracuseStep 1921981 = 720743) (by norm_num)
theorem B2020301 : Blo 896573 2020301 := bbase (se 3 (by rfl) ⟨378806, by rfl⟩ : syracuseStep 2020301 = 757613) (by norm_num)
theorem B2053085 : Blo 896573 2053085 := bbase (se 3 (by rfl) ⟨384953, by rfl⟩ : syracuseStep 2053085 = 769907) (by norm_num)
theorem B3036149 : Blo 896573 3036149 := bbase (se 5 (by rfl) ⟨142319, by rfl⟩ : syracuseStep 3036149 = 284639) (by norm_num)
theorem B2020373 : Blo 896573 2020373 := bbase (se 6 (by rfl) ⟨47352, by rfl⟩ : syracuseStep 2020373 = 94705) (by norm_num)
theorem B2020445 : Blo 896573 2020445 := bbase (se 3 (by rfl) ⟨378833, by rfl⟩ : syracuseStep 2020445 = 757667) (by norm_num)
theorem B1135721 : Blo 896573 1135721 := bbase (se 2 (by rfl) ⟨425895, by rfl⟩ : syracuseStep 1135721 = 851791) (by norm_num)
theorem B1135777 : Blo 896573 1135777 := bbase (se 2 (by rfl) ⟨425916, by rfl⟩ : syracuseStep 1135777 = 851833) (by norm_num)
theorem B2020517 : Blo 896573 2020517 := bbase (se 4 (by rfl) ⟨189423, by rfl⟩ : syracuseStep 2020517 = 378847) (by norm_num)
theorem B2020589 : Blo 896573 2020589 := bbase (se 3 (by rfl) ⟨378860, by rfl⟩ : syracuseStep 2020589 = 757721) (by norm_num)
theorem B1135873 : Blo 896573 1135873 := bbase (se 2 (by rfl) ⟨425952, by rfl⟩ : syracuseStep 1135873 = 851905) (by norm_num)
theorem B2020661 : Blo 896573 2020661 := bbase (se 5 (by rfl) ⟨94718, by rfl⟩ : syracuseStep 2020661 = 189437) (by norm_num)
theorem B2872693 : Blo 896573 2872693 := bbase (se 5 (by rfl) ⟨134657, by rfl⟩ : syracuseStep 2872693 = 269315) (by norm_num)
theorem B2020733 : Blo 896573 2020733 := bbase (se 3 (by rfl) ⟨378887, by rfl⟩ : syracuseStep 2020733 = 757775) (by norm_num)
theorem B3036581 : Blo 896573 3036581 := bbase (se 4 (by rfl) ⟨284679, by rfl⟩ : syracuseStep 3036581 = 569359) (by norm_num)
theorem B1136045 : Blo 896573 1136045 := bbase (se 3 (by rfl) ⟨213008, by rfl⟩ : syracuseStep 1136045 = 426017) (by norm_num)
theorem B2020805 : Blo 896573 2020805 := bbase (se 4 (by rfl) ⟨189450, by rfl⟩ : syracuseStep 2020805 = 378901) (by norm_num)
theorem B1136101 : Blo 896573 1136101 := bbase (se 4 (by rfl) ⟨106509, by rfl⟩ : syracuseStep 1136101 = 213019) (by norm_num)
theorem B2020877 : Blo 896573 2020877 := bbase (se 3 (by rfl) ⟨378914, by rfl⟩ : syracuseStep 2020877 = 757829) (by norm_num)
theorem B2053669 : Blo 896573 2053669 := bbase (se 4 (by rfl) ⟨192531, by rfl⟩ : syracuseStep 2053669 = 385063) (by norm_num)
theorem B1136197 : Blo 896573 1136197 := bbase (se 4 (by rfl) ⟨106518, by rfl⟩ : syracuseStep 1136197 = 213037) (by norm_num)
theorem B2020949 : Blo 896573 2020949 := bbase (se 8 (by rfl) ⟨11841, by rfl⟩ : syracuseStep 2020949 = 23683) (by norm_num)
theorem B1824365 : Blo 896573 1824365 := bbase (se 3 (by rfl) ⟨342068, by rfl⟩ : syracuseStep 1824365 = 684137) (by norm_num)
theorem B2021021 : Blo 896573 2021021 := bbase (se 3 (by rfl) ⟨378941, by rfl⟩ : syracuseStep 2021021 = 757883) (by norm_num)
theorem B2021093 : Blo 896573 2021093 := bbase (se 4 (by rfl) ⟨189477, by rfl⟩ : syracuseStep 2021093 = 378955) (by norm_num)
theorem B1136369 : Blo 896573 1136369 := bbase (se 2 (by rfl) ⟨426138, by rfl⟩ : syracuseStep 1136369 = 852277) (by norm_num)
theorem B4544261 : Blo 896573 4544261 := bbase (se 4 (by rfl) ⟨426024, by rfl⟩ : syracuseStep 4544261 = 852049) (by norm_num)
theorem B1136425 : Blo 896573 1136425 := bbase (se 2 (by rfl) ⟨426159, by rfl⟩ : syracuseStep 1136425 = 852319) (by norm_num)
theorem B2021165 : Blo 896573 2021165 := bbase (se 3 (by rfl) ⟨378968, by rfl⟩ : syracuseStep 2021165 = 757937) (by norm_num)
theorem B1922869 : Blo 896573 1922869 := bbase (se 5 (by rfl) ⟨90134, by rfl⟩ : syracuseStep 1922869 = 180269) (by norm_num)
theorem B13850453 : Blo 896573 13850453 := bbase (se 9 (by rfl) ⟨40577, by rfl⟩ : syracuseStep 13850453 = 81155) (by norm_num)
theorem B3037013 : Blo 896573 3037013 := bbase (se 9 (by rfl) ⟨8897, by rfl⟩ : syracuseStep 3037013 = 17795) (by norm_num)
theorem B2021237 : Blo 896573 2021237 := bbase (se 5 (by rfl) ⟨94745, by rfl⟩ : syracuseStep 2021237 = 189491) (by norm_num)
theorem B1136521 : Blo 896573 1136521 := bbase (se 2 (by rfl) ⟨426195, by rfl⟩ : syracuseStep 1136521 = 852391) (by norm_num)
theorem B2021309 : Blo 896573 2021309 := bbase (se 3 (by rfl) ⟨378995, by rfl⟩ : syracuseStep 2021309 = 757991) (by norm_num)
theorem B2021381 : Blo 896573 2021381 := bbase (se 4 (by rfl) ⟨189504, by rfl⟩ : syracuseStep 2021381 = 379009) (by norm_num)
theorem B1136693 : Blo 896573 1136693 := bbase (se 5 (by rfl) ⟨53282, by rfl⟩ : syracuseStep 1136693 = 106565) (by norm_num)
theorem B2021453 : Blo 896573 2021453 := bbase (se 3 (by rfl) ⟨379022, by rfl⟩ : syracuseStep 2021453 = 758045) (by norm_num)
theorem B1136749 : Blo 896573 1136749 := bbase (se 3 (by rfl) ⟨213140, by rfl⟩ : syracuseStep 1136749 = 426281) (by norm_num)
theorem B2021525 : Blo 896573 2021525 := bbase (se 6 (by rfl) ⟨47379, by rfl⟩ : syracuseStep 2021525 = 94759) (by norm_num)
theorem B1136845 : Blo 896573 1136845 := bbase (se 3 (by rfl) ⟨213158, by rfl⟩ : syracuseStep 1136845 = 426317) (by norm_num)
theorem B2021597 : Blo 896573 2021597 := bbase (se 3 (by rfl) ⟨379049, by rfl⟩ : syracuseStep 2021597 = 758099) (by norm_num)
theorem B1825013 : Blo 896573 1825013 := bbase (se 5 (by rfl) ⟨85547, by rfl⟩ : syracuseStep 1825013 = 171095) (by norm_num)
theorem B3037445 : Blo 896573 3037445 := bbase (se 4 (by rfl) ⟨284760, by rfl⟩ : syracuseStep 3037445 = 569521) (by norm_num)
theorem B2021669 : Blo 896573 2021669 := bbase (se 4 (by rfl) ⟨189531, by rfl⟩ : syracuseStep 2021669 = 379063) (by norm_num)
theorem B1923365 : Blo 896573 1923365 := bbase (se 4 (by rfl) ⟨180315, by rfl⟩ : syracuseStep 1923365 = 360631) (by norm_num)
theorem B2021741 : Blo 896573 2021741 := bbase (se 3 (by rfl) ⟨379076, by rfl⟩ : syracuseStep 2021741 = 758153) (by norm_num)
theorem B1137017 : Blo 896573 1137017 := bbase (se 2 (by rfl) ⟨426381, by rfl⟩ : syracuseStep 1137017 = 852763) (by norm_num)
theorem B1137073 : Blo 896573 1137073 := bbase (se 2 (by rfl) ⟨426402, by rfl⟩ : syracuseStep 1137073 = 852805) (by norm_num)
theorem B2021813 : Blo 896573 2021813 := bbase (se 5 (by rfl) ⟨94772, by rfl⟩ : syracuseStep 2021813 = 189545) (by norm_num)
theorem B4610533 : Blo 896573 4610533 := bbase (se 4 (by rfl) ⟨432237, by rfl⟩ : syracuseStep 4610533 = 864475) (by norm_num)
theorem B2021885 : Blo 896573 2021885 := bbase (se 3 (by rfl) ⟨379103, by rfl⟩ : syracuseStep 2021885 = 758207) (by norm_num)
theorem B1137169 : Blo 896573 1137169 := bbase (se 2 (by rfl) ⟨426438, by rfl⟩ : syracuseStep 1137169 = 852877) (by norm_num)
theorem B2021957 : Blo 896573 2021957 := bbase (se 4 (by rfl) ⟨189558, by rfl⟩ : syracuseStep 2021957 = 379117) (by norm_num)
theorem B2022029 : Blo 896573 2022029 := bbase (se 3 (by rfl) ⟨379130, by rfl⟩ : syracuseStep 2022029 = 758261) (by norm_num)
theorem B3037877 : Blo 896573 3037877 := bbase (se 5 (by rfl) ⟨142400, by rfl⟩ : syracuseStep 3037877 = 284801) (by norm_num)
theorem B1137341 : Blo 896573 1137341 := bbase (se 3 (by rfl) ⟨213251, by rfl⟩ : syracuseStep 1137341 = 426503) (by norm_num)
theorem B2022101 : Blo 896573 2022101 := bbase (se 7 (by rfl) ⟨23696, by rfl⟩ : syracuseStep 2022101 = 47393) (by norm_num)
theorem B1137397 : Blo 896573 1137397 := bbase (se 5 (by rfl) ⟨53315, by rfl⟩ : syracuseStep 1137397 = 106631) (by norm_num)
theorem B6478613 : Blo 896573 6478613 := bbase (se 6 (by rfl) ⟨151842, by rfl⟩ : syracuseStep 6478613 = 303685) (by norm_num)
theorem B2022173 : Blo 896573 2022173 := bbase (se 3 (by rfl) ⟨379157, by rfl⟩ : syracuseStep 2022173 = 758315) (by norm_num)
theorem B1137493 : Blo 896573 1137493 := bbase (se 9 (by rfl) ⟨3332, by rfl⟩ : syracuseStep 1137493 = 6665) (by norm_num)
theorem B2022245 : Blo 896573 2022245 := bbase (se 4 (by rfl) ⟨189585, by rfl⟩ : syracuseStep 2022245 = 379171) (by norm_num)
theorem B1825661 : Blo 896573 1825661 := bbase (se 3 (by rfl) ⟨342311, by rfl⟩ : syracuseStep 1825661 = 684623) (by norm_num)
theorem B2022317 : Blo 896573 2022317 := bbase (se 3 (by rfl) ⟨379184, by rfl⟩ : syracuseStep 2022317 = 758369) (by norm_num)
theorem B2022389 : Blo 896573 2022389 := bbase (se 5 (by rfl) ⟨94799, by rfl⟩ : syracuseStep 2022389 = 189599) (by norm_num)
theorem B4676597 : Blo 896573 4676597 := bbase (se 5 (by rfl) ⟨219215, by rfl⟩ : syracuseStep 4676597 = 438431) (by norm_num)
theorem B1137665 : Blo 896573 1137665 := bbase (se 2 (by rfl) ⟨426624, by rfl⟩ : syracuseStep 1137665 = 853249) (by norm_num)
theorem B4545557 : Blo 896573 4545557 := bbase (se 6 (by rfl) ⟨106536, by rfl⟩ : syracuseStep 4545557 = 213073) (by norm_num)
theorem B1137721 : Blo 896573 1137721 := bbase (se 2 (by rfl) ⟨426645, by rfl⟩ : syracuseStep 1137721 = 853291) (by norm_num)
theorem B2022461 : Blo 896573 2022461 := bbase (se 3 (by rfl) ⟨379211, by rfl⟩ : syracuseStep 2022461 = 758423) (by norm_num)
theorem B2874437 : Blo 896573 2874437 := bbase (se 4 (by rfl) ⟨269478, by rfl⟩ : syracuseStep 2874437 = 538957) (by norm_num)
theorem B3038309 : Blo 896573 3038309 := bbase (se 4 (by rfl) ⟨284841, by rfl⟩ : syracuseStep 3038309 = 569683) (by norm_num)
theorem B2022533 : Blo 896573 2022533 := bbase (se 4 (by rfl) ⟨189612, by rfl⟩ : syracuseStep 2022533 = 379225) (by norm_num)
theorem B1137817 : Blo 896573 1137817 := bbase (se 2 (by rfl) ⟨426681, by rfl⟩ : syracuseStep 1137817 = 853363) (by norm_num)
theorem B2022605 : Blo 896573 2022605 := bbase (se 3 (by rfl) ⟨379238, by rfl⟩ : syracuseStep 2022605 = 758477) (by norm_num)
theorem B2874629 : Blo 896573 2874629 := bbase (se 4 (by rfl) ⟨269496, by rfl⟩ : syracuseStep 2874629 = 538993) (by norm_num)
theorem B2022677 : Blo 896573 2022677 := bbase (se 6 (by rfl) ⟨47406, by rfl⟩ : syracuseStep 2022677 = 94813) (by norm_num)
theorem B1727797 : Blo 896573 1727797 := bbase (se 5 (by rfl) ⟨80990, by rfl⟩ : syracuseStep 1727797 = 161981) (by norm_num)
theorem B1137989 : Blo 896573 1137989 := bbase (se 4 (by rfl) ⟨106686, by rfl⟩ : syracuseStep 1137989 = 213373) (by norm_num)
theorem B2022749 : Blo 896573 2022749 := bbase (se 3 (by rfl) ⟨379265, by rfl⟩ : syracuseStep 2022749 = 758531) (by norm_num)
theorem B1138045 : Blo 896573 1138045 := bbase (se 3 (by rfl) ⟨213383, by rfl⟩ : syracuseStep 1138045 = 426767) (by norm_num)
theorem B2022821 : Blo 896573 2022821 := bbase (se 4 (by rfl) ⟨189639, by rfl⟩ : syracuseStep 2022821 = 379279) (by norm_num)
theorem B1138141 : Blo 896573 1138141 := bbase (se 3 (by rfl) ⟨213401, by rfl⟩ : syracuseStep 1138141 = 426803) (by norm_num)
theorem B2022893 : Blo 896573 2022893 := bbase (se 3 (by rfl) ⟨379292, by rfl⟩ : syracuseStep 2022893 = 758585) (by norm_num)
theorem B3038741 : Blo 896573 3038741 := bbase (se 6 (by rfl) ⟨71220, by rfl⟩ : syracuseStep 3038741 = 142441) (by norm_num)
theorem B2022965 : Blo 896573 2022965 := bbase (se 5 (by rfl) ⟨94826, by rfl⟩ : syracuseStep 2022965 = 189653) (by norm_num)
theorem B2252405 : Blo 896573 2252405 := bbase (se 5 (by rfl) ⟨105581, by rfl⟩ : syracuseStep 2252405 = 211163) (by norm_num)
theorem B2023037 : Blo 896573 2023037 := bbase (se 3 (by rfl) ⟨379319, by rfl⟩ : syracuseStep 2023037 = 758639) (by norm_num)
theorem B1138313 : Blo 896573 1138313 := bbase (se 2 (by rfl) ⟨426867, by rfl⟩ : syracuseStep 1138313 = 853735) (by norm_num)
theorem B5758613 : Blo 896573 5758613 := bbase (se 6 (by rfl) ⟨134967, by rfl⟩ : syracuseStep 5758613 = 269935) (by norm_num)
theorem B1138369 : Blo 896573 1138369 := bbase (se 2 (by rfl) ⟨426888, by rfl⟩ : syracuseStep 1138369 = 853777) (by norm_num)
theorem B2023109 : Blo 896573 2023109 := bbase (se 4 (by rfl) ⟨189666, by rfl⟩ : syracuseStep 2023109 = 379333) (by norm_num)
theorem B2023181 : Blo 896573 2023181 := bbase (se 3 (by rfl) ⟨379346, by rfl⟩ : syracuseStep 2023181 = 758693) (by norm_num)
theorem B1138465 : Blo 896573 1138465 := bbase (se 2 (by rfl) ⟨426924, by rfl⟩ : syracuseStep 1138465 = 853849) (by norm_num)
theorem B2023253 : Blo 896573 2023253 := bbase (se 9 (by rfl) ⟨5927, by rfl⟩ : syracuseStep 2023253 = 11855) (by norm_num)
theorem B4317077 : Blo 896573 4317077 := bbase (se 6 (by rfl) ⟨101181, by rfl⟩ : syracuseStep 4317077 = 202363) (by norm_num)
theorem B2023325 : Blo 896573 2023325 := bbase (se 3 (by rfl) ⟨379373, by rfl⟩ : syracuseStep 2023325 = 758747) (by norm_num)
theorem B974749 : Blo 896573 974749 := bbase (se 3 (by rfl) ⟨182765, by rfl⟩ : syracuseStep 974749 = 365531) (by norm_num)
theorem B3039173 : Blo 896573 3039173 := bbase (se 4 (by rfl) ⟨284922, by rfl⟩ : syracuseStep 3039173 = 569845) (by norm_num)
theorem B1138637 : Blo 896573 1138637 := bbase (se 3 (by rfl) ⟨213494, by rfl⟩ : syracuseStep 1138637 = 426989) (by norm_num)
theorem B2023397 : Blo 896573 2023397 := bbase (se 4 (by rfl) ⟨189693, by rfl⟩ : syracuseStep 2023397 = 379387) (by norm_num)
theorem B2187269 : Blo 896573 2187269 := bbase (se 4 (by rfl) ⟨205056, by rfl⟩ : syracuseStep 2187269 = 410113) (by norm_num)
theorem B1138693 : Blo 896573 1138693 := bbase (se 4 (by rfl) ⟨106752, by rfl⟩ : syracuseStep 1138693 = 213505) (by norm_num)
theorem B2023469 : Blo 896573 2023469 := bbase (se 3 (by rfl) ⟨379400, by rfl⟩ : syracuseStep 2023469 = 758801) (by norm_num)
theorem B1138789 : Blo 896573 1138789 := bbase (se 4 (by rfl) ⟨106761, by rfl⟩ : syracuseStep 1138789 = 213523) (by norm_num)
theorem B2023541 : Blo 896573 2023541 := bbase (se 5 (by rfl) ⟨94853, by rfl⟩ : syracuseStep 2023541 = 189707) (by norm_num)
theorem B2187445 : Blo 896573 2187445 := bbase (se 5 (by rfl) ⟨102536, by rfl⟩ : syracuseStep 2187445 = 205073) (by norm_num)
theorem B2023613 : Blo 896573 2023613 := bbase (se 3 (by rfl) ⟨379427, by rfl⟩ : syracuseStep 2023613 = 758855) (by norm_num)
theorem B2023685 : Blo 896573 2023685 := bbase (se 4 (by rfl) ⟨189720, by rfl⟩ : syracuseStep 2023685 = 379441) (by norm_num)
theorem B1138961 : Blo 896573 1138961 := bbase (se 2 (by rfl) ⟨427110, by rfl⟩ : syracuseStep 1138961 = 854221) (by norm_num)
theorem B4546853 : Blo 896573 4546853 := bbase (se 4 (by rfl) ⟨426267, by rfl⟩ : syracuseStep 4546853 = 852535) (by norm_num)
theorem B1139017 : Blo 896573 1139017 := bbase (se 2 (by rfl) ⟨427131, by rfl⟩ : syracuseStep 1139017 = 854263) (by norm_num)
theorem B2023757 : Blo 896573 2023757 := bbase (se 3 (by rfl) ⟨379454, by rfl⟩ : syracuseStep 2023757 = 758909) (by norm_num)
theorem B6906197 : Blo 896573 6906197 := bbase (se 10 (by rfl) ⟨10116, by rfl⟩ : syracuseStep 6906197 = 20233) (by norm_num)
theorem B2023829 : Blo 896573 2023829 := bbase (se 6 (by rfl) ⟨47433, by rfl⟩ : syracuseStep 2023829 = 94867) (by norm_num)
theorem B1139113 : Blo 896573 1139113 := bbase (se 2 (by rfl) ⟨427167, by rfl⟩ : syracuseStep 1139113 = 854335) (by norm_num)
theorem B2023901 : Blo 896573 2023901 := bbase (se 3 (by rfl) ⟨379481, by rfl⟩ : syracuseStep 2023901 = 758963) (by norm_num)
theorem B2023973 : Blo 896573 2023973 := bbase (se 4 (by rfl) ⟨189747, by rfl⟩ : syracuseStep 2023973 = 379495) (by norm_num)
theorem B1139285 : Blo 896573 1139285 := bbase (se 8 (by rfl) ⟨6675, by rfl⟩ : syracuseStep 1139285 = 13351) (by norm_num)
theorem B2024045 : Blo 896573 2024045 := bbase (se 3 (by rfl) ⟨379508, by rfl⟩ : syracuseStep 2024045 = 759017) (by norm_num)
theorem B1139341 : Blo 896573 1139341 := bbase (se 3 (by rfl) ⟨213626, by rfl⟩ : syracuseStep 1139341 = 427253) (by norm_num)
theorem B2024117 : Blo 896573 2024117 := bbase (se 5 (by rfl) ⟨94880, by rfl⟩ : syracuseStep 2024117 = 189761) (by norm_num)
theorem B1139437 : Blo 896573 1139437 := bbase (se 3 (by rfl) ⟨213644, by rfl⟩ : syracuseStep 1139437 = 427289) (by norm_num)
theorem B2024189 : Blo 896573 2024189 := bbase (se 3 (by rfl) ⟨379535, by rfl⟩ : syracuseStep 2024189 = 759071) (by norm_num)
theorem B6808373 : Blo 896573 6808373 := bbase (se 5 (by rfl) ⟨319142, by rfl⟩ : syracuseStep 6808373 = 638285) (by norm_num)
theorem B2024261 : Blo 896573 2024261 := bbase (se 4 (by rfl) ⟨189774, by rfl⟩ : syracuseStep 2024261 = 379549) (by norm_num)
theorem B2155357 : Blo 896573 2155357 := bbase (se 3 (by rfl) ⟨404129, by rfl⟩ : syracuseStep 2155357 = 808259) (by norm_num)
theorem B2155405 : Blo 896573 2155405 := bbase (se 3 (by rfl) ⟨404138, by rfl⟩ : syracuseStep 2155405 = 808277) (by norm_num)
theorem B2024333 : Blo 896573 2024333 := bbase (se 3 (by rfl) ⟨379562, by rfl⟩ : syracuseStep 2024333 = 759125) (by norm_num)
theorem B1139609 : Blo 896573 1139609 := bbase (se 2 (by rfl) ⟨427353, by rfl⟩ : syracuseStep 1139609 = 854707) (by norm_num)
theorem B1139665 : Blo 896573 1139665 := bbase (se 2 (by rfl) ⟨427374, by rfl⟩ : syracuseStep 1139665 = 854749) (by norm_num)
theorem B2024405 : Blo 896573 2024405 := bbase (se 7 (by rfl) ⟨23723, by rfl⟩ : syracuseStep 2024405 = 47447) (by norm_num)
theorem B1008661 : Blo 896573 1008661 := bbase (se 6 (by rfl) ⟨23640, by rfl⟩ : syracuseStep 1008661 = 47281) (by norm_num)
theorem B2024477 : Blo 896573 2024477 := bbase (se 3 (by rfl) ⟨379589, by rfl⟩ : syracuseStep 2024477 = 759179) (by norm_num)
theorem B1139761 : Blo 896573 1139761 := bbase (se 2 (by rfl) ⟨427410, by rfl⟩ : syracuseStep 1139761 = 854821) (by norm_num)
theorem B1008697 : Blo 896573 1008697 := bbase (se 2 (by rfl) ⟨378261, by rfl⟩ : syracuseStep 1008697 = 756523) (by norm_num)
theorem B10937429 : Blo 896573 10937429 := bbase (se 8 (by rfl) ⟨64086, by rfl⟩ : syracuseStep 10937429 = 128173) (by norm_num)
theorem B1008733 : Blo 896573 1008733 := bbase (se 3 (by rfl) ⟨189137, by rfl⟩ : syracuseStep 1008733 = 378275) (by norm_num)
theorem B2024549 : Blo 896573 2024549 := bbase (se 4 (by rfl) ⟨189801, by rfl⟩ : syracuseStep 2024549 = 379603) (by norm_num)
theorem B1008769 : Blo 896573 1008769 := bbase (se 2 (by rfl) ⟨378288, by rfl⟩ : syracuseStep 1008769 = 756577) (by norm_num)
theorem B1008805 : Blo 896573 1008805 := bbase (se 4 (by rfl) ⟨94575, by rfl⟩ : syracuseStep 1008805 = 189151) (by norm_num)
theorem B3237029 : Blo 896573 3237029 := bbase (se 4 (by rfl) ⟨303471, by rfl⟩ : syracuseStep 3237029 = 606943) (by norm_num)
theorem B2024621 : Blo 896573 2024621 := bbase (se 3 (by rfl) ⟨379616, by rfl⟩ : syracuseStep 2024621 = 759233) (by norm_num)
theorem B1008841 : Blo 896573 1008841 := bbase (se 2 (by rfl) ⟨378315, by rfl⟩ : syracuseStep 1008841 = 756631) (by norm_num)
theorem B7300309 : Blo 896573 7300309 := bbase (se 7 (by rfl) ⟨85550, by rfl⟩ : syracuseStep 7300309 = 171101) (by norm_num)
theorem B1008877 : Blo 896573 1008877 := bbase (se 3 (by rfl) ⟨189164, by rfl⟩ : syracuseStep 1008877 = 378329) (by norm_num)
theorem B2024693 : Blo 896573 2024693 := bbase (se 5 (by rfl) ⟨94907, by rfl⟩ : syracuseStep 2024693 = 189815) (by norm_num)
theorem B1008913 : Blo 896573 1008913 := bbase (se 2 (by rfl) ⟨378342, by rfl⟩ : syracuseStep 1008913 = 756685) (by norm_num)
theorem B1729829 : Blo 896573 1729829 := bbase (se 4 (by rfl) ⟨162171, by rfl⟩ : syracuseStep 1729829 = 324343) (by norm_num)
theorem B1008949 : Blo 896573 1008949 := bbase (se 5 (by rfl) ⟨47294, by rfl⟩ : syracuseStep 1008949 = 94589) (by norm_num)
theorem B2024765 : Blo 896573 2024765 := bbase (se 3 (by rfl) ⟨379643, by rfl⟩ : syracuseStep 2024765 = 759287) (by norm_num)
theorem B1008985 : Blo 896573 1008985 := bbase (se 2 (by rfl) ⟨378369, by rfl⟩ : syracuseStep 1008985 = 756739) (by norm_num)
theorem B1009021 : Blo 896573 1009021 := bbase (se 3 (by rfl) ⟨189191, by rfl⟩ : syracuseStep 1009021 = 378383) (by norm_num)
theorem B2024837 : Blo 896573 2024837 := bbase (se 4 (by rfl) ⟨189828, by rfl⟩ : syracuseStep 2024837 = 379657) (by norm_num)
theorem B1009057 : Blo 896573 1009057 := bbase (se 2 (by rfl) ⟨378396, by rfl⟩ : syracuseStep 1009057 = 756793) (by norm_num)
theorem B1009093 : Blo 896573 1009093 := bbase (se 4 (by rfl) ⟨94602, by rfl⟩ : syracuseStep 1009093 = 189205) (by norm_num)
theorem B3237317 : Blo 896573 3237317 := bbase (se 4 (by rfl) ⟨303498, by rfl⟩ : syracuseStep 3237317 = 606997) (by norm_num)
theorem B2024909 : Blo 896573 2024909 := bbase (se 3 (by rfl) ⟨379670, by rfl⟩ : syracuseStep 2024909 = 759341) (by norm_num)
theorem B1009129 : Blo 896573 1009129 := bbase (se 2 (by rfl) ⟨378423, by rfl⟩ : syracuseStep 1009129 = 756847) (by norm_num)
theorem B2156021 : Blo 896573 2156021 := bbase (se 5 (by rfl) ⟨101063, by rfl⟩ : syracuseStep 2156021 = 202127) (by norm_num)
theorem B1009165 : Blo 896573 1009165 := bbase (se 3 (by rfl) ⟨189218, by rfl⟩ : syracuseStep 1009165 = 378437) (by norm_num)
theorem B2024981 : Blo 896573 2024981 := bbase (se 6 (by rfl) ⟨47460, by rfl⟩ : syracuseStep 2024981 = 94921) (by norm_num)
theorem B1009201 : Blo 896573 1009201 := bbase (se 2 (by rfl) ⟨378450, by rfl⟩ : syracuseStep 1009201 = 756901) (by norm_num)
theorem B4548149 : Blo 896573 4548149 := bbase (se 5 (by rfl) ⟨213194, by rfl⟩ : syracuseStep 4548149 = 426389) (by norm_num)
theorem B1009237 : Blo 896573 1009237 := bbase (se 8 (by rfl) ⟨5913, by rfl⟩ : syracuseStep 1009237 = 11827) (by norm_num)
theorem B2025053 : Blo 896573 2025053 := bbase (se 3 (by rfl) ⟨379697, by rfl⟩ : syracuseStep 2025053 = 759395) (by norm_num)
theorem B1009273 : Blo 896573 1009273 := bbase (se 2 (by rfl) ⟨378477, by rfl⟩ : syracuseStep 1009273 = 756955) (by norm_num)
theorem B1009309 : Blo 896573 1009309 := bbase (se 3 (by rfl) ⟨189245, by rfl⟩ : syracuseStep 1009309 = 378491) (by norm_num)
theorem B2025125 : Blo 896573 2025125 := bbase (se 4 (by rfl) ⟨189855, by rfl⟩ : syracuseStep 2025125 = 379711) (by norm_num)
theorem B1009345 : Blo 896573 1009345 := bbase (se 2 (by rfl) ⟨378504, by rfl⟩ : syracuseStep 1009345 = 757009) (by norm_num)
theorem B1009381 : Blo 896573 1009381 := bbase (se 4 (by rfl) ⟨94629, by rfl⟩ : syracuseStep 1009381 = 189259) (by norm_num)
theorem B2025197 : Blo 896573 2025197 := bbase (se 3 (by rfl) ⟨379724, by rfl⟩ : syracuseStep 2025197 = 759449) (by norm_num)
theorem B1009417 : Blo 896573 1009417 := bbase (se 2 (by rfl) ⟨378531, by rfl⟩ : syracuseStep 1009417 = 757063) (by norm_num)
theorem B1009453 : Blo 896573 1009453 := bbase (se 3 (by rfl) ⟨189272, by rfl⟩ : syracuseStep 1009453 = 378545) (by norm_num)
theorem B2025269 : Blo 896573 2025269 := bbase (se 5 (by rfl) ⟨94934, by rfl⟩ : syracuseStep 2025269 = 189869) (by norm_num)
theorem B2156365 : Blo 896573 2156365 := bbase (se 3 (by rfl) ⟨404318, by rfl⟩ : syracuseStep 2156365 = 808637) (by norm_num)
theorem B1009489 : Blo 896573 1009489 := bbase (se 2 (by rfl) ⟨378558, by rfl⟩ : syracuseStep 1009489 = 757117) (by norm_num)
theorem B1009525 : Blo 896573 1009525 := bbase (se 5 (by rfl) ⟨47321, by rfl⟩ : syracuseStep 1009525 = 94643) (by norm_num)
theorem B3073909 : Blo 896573 3073909 := bbase (se 5 (by rfl) ⟨144089, by rfl⟩ : syracuseStep 3073909 = 288179) (by norm_num)
theorem B2025341 : Blo 896573 2025341 := bbase (se 3 (by rfl) ⟨379751, by rfl⟩ : syracuseStep 2025341 = 759503) (by norm_num)
theorem B1009561 : Blo 896573 1009561 := bbase (se 2 (by rfl) ⟨378585, by rfl⟩ : syracuseStep 1009561 = 757171) (by norm_num)
theorem B1009597 : Blo 896573 1009597 := bbase (se 3 (by rfl) ⟨189299, by rfl⟩ : syracuseStep 1009597 = 378599) (by norm_num)
theorem B2025413 : Blo 896573 2025413 := bbase (se 4 (by rfl) ⟨189882, by rfl⟩ : syracuseStep 2025413 = 379765) (by norm_num)
theorem B1533917 : Blo 896573 1533917 := bbase (se 3 (by rfl) ⟨287609, by rfl⟩ : syracuseStep 1533917 = 575219) (by norm_num)
theorem B1009633 : Blo 896573 1009633 := bbase (se 2 (by rfl) ⟨378612, by rfl⟩ : syracuseStep 1009633 = 757225) (by norm_num)
theorem B1009669 : Blo 896573 1009669 := bbase (se 4 (by rfl) ⟨94656, by rfl⟩ : syracuseStep 1009669 = 189313) (by norm_num)
theorem B2025485 : Blo 896573 2025485 := bbase (se 3 (by rfl) ⟨379778, by rfl⟩ : syracuseStep 2025485 = 759557) (by norm_num)
theorem B1009705 : Blo 896573 1009705 := bbase (se 2 (by rfl) ⟨378639, by rfl⟩ : syracuseStep 1009705 = 757279) (by norm_num)
theorem B2156597 : Blo 896573 2156597 := bbase (se 5 (by rfl) ⟨101090, by rfl⟩ : syracuseStep 2156597 = 202181) (by norm_num)
theorem B1009741 : Blo 896573 1009741 := bbase (se 3 (by rfl) ⟨189326, by rfl⟩ : syracuseStep 1009741 = 378653) (by norm_num)
theorem B2025557 : Blo 896573 2025557 := bbase (se 8 (by rfl) ⟨11868, by rfl⟩ : syracuseStep 2025557 = 23737) (by norm_num)
theorem B1009777 : Blo 896573 1009777 := bbase (se 2 (by rfl) ⟨378666, by rfl⟩ : syracuseStep 1009777 = 757333) (by norm_num)
theorem B1108081 : Blo 896573 1108081 := bbase (se 2 (by rfl) ⟨415530, by rfl⟩ : syracuseStep 1108081 = 831061) (by norm_num)
theorem B4384901 : Blo 896573 4384901 := bbase (se 4 (by rfl) ⟨411084, by rfl⟩ : syracuseStep 4384901 = 822169) (by norm_num)
theorem B1009813 : Blo 896573 1009813 := bbase (se 6 (by rfl) ⟨23667, by rfl⟩ : syracuseStep 1009813 = 47335) (by norm_num)
theorem B2025629 : Blo 896573 2025629 := bbase (se 3 (by rfl) ⟨379805, by rfl⟩ : syracuseStep 2025629 = 759611) (by norm_num)
theorem B1009849 : Blo 896573 1009849 := bbase (se 2 (by rfl) ⟨378693, by rfl⟩ : syracuseStep 1009849 = 757387) (by norm_num)
theorem B1009885 : Blo 896573 1009885 := bbase (se 3 (by rfl) ⟨189353, by rfl⟩ : syracuseStep 1009885 = 378707) (by norm_num)
theorem B2025701 : Blo 896573 2025701 := bbase (se 4 (by rfl) ⟨189909, by rfl⟩ : syracuseStep 2025701 = 379819) (by norm_num)
theorem B2156789 : Blo 896573 2156789 := bbase (se 5 (by rfl) ⟨101099, by rfl⟩ : syracuseStep 2156789 = 202199) (by norm_num)
theorem B1009921 : Blo 896573 1009921 := bbase (se 2 (by rfl) ⟨378720, by rfl⟩ : syracuseStep 1009921 = 757441) (by norm_num)
theorem B1009957 : Blo 896573 1009957 := bbase (se 4 (by rfl) ⟨94683, by rfl⟩ : syracuseStep 1009957 = 189367) (by norm_num)
theorem B2025773 : Blo 896573 2025773 := bbase (se 3 (by rfl) ⟨379832, by rfl⟩ : syracuseStep 2025773 = 759665) (by norm_num)
theorem B1009993 : Blo 896573 1009993 := bbase (se 2 (by rfl) ⟨378747, by rfl⟩ : syracuseStep 1009993 = 757495) (by norm_num)
theorem B1010029 : Blo 896573 1010029 := bbase (se 3 (by rfl) ⟨189380, by rfl⟩ : syracuseStep 1010029 = 378761) (by norm_num)
theorem B2025845 : Blo 896573 2025845 := bbase (se 5 (by rfl) ⟨94961, by rfl⟩ : syracuseStep 2025845 = 189923) (by norm_num)
theorem B1010065 : Blo 896573 1010065 := bbase (se 2 (by rfl) ⟨378774, by rfl⟩ : syracuseStep 1010065 = 757549) (by norm_num)
theorem B1010101 : Blo 896573 1010101 := bbase (se 5 (by rfl) ⟨47348, by rfl⟩ : syracuseStep 1010101 = 94697) (by norm_num)
theorem B2025917 : Blo 896573 2025917 := bbase (se 3 (by rfl) ⟨379859, by rfl⟩ : syracuseStep 2025917 = 759719) (by norm_num)
theorem B1010137 : Blo 896573 1010137 := bbase (se 2 (by rfl) ⟨378801, by rfl⟩ : syracuseStep 1010137 = 757603) (by norm_num)
theorem B1010173 : Blo 896573 1010173 := bbase (se 3 (by rfl) ⟨189407, by rfl⟩ : syracuseStep 1010173 = 378815) (by norm_num)
theorem B2025989 : Blo 896573 2025989 := bbase (se 4 (by rfl) ⟨189936, by rfl⟩ : syracuseStep 2025989 = 379873) (by norm_num)
theorem B2157077 : Blo 896573 2157077 := bbase (se 6 (by rfl) ⟨50556, by rfl⟩ : syracuseStep 2157077 = 101113) (by norm_num)
theorem B1010209 : Blo 896573 1010209 := bbase (se 2 (by rfl) ⟨378828, by rfl⟩ : syracuseStep 1010209 = 757657) (by norm_num)
theorem B1010245 : Blo 896573 1010245 := bbase (se 4 (by rfl) ⟨94710, by rfl⟩ : syracuseStep 1010245 = 189421) (by norm_num)
theorem B3238469 : Blo 896573 3238469 := bbase (se 4 (by rfl) ⟨303606, by rfl⟩ : syracuseStep 3238469 = 607213) (by norm_num)
theorem B2026061 : Blo 896573 2026061 := bbase (se 3 (by rfl) ⟨379886, by rfl⟩ : syracuseStep 2026061 = 759773) (by norm_num)
theorem B1010281 : Blo 896573 1010281 := bbase (se 2 (by rfl) ⟨378855, by rfl⟩ : syracuseStep 1010281 = 757711) (by norm_num)
theorem B1534573 : Blo 896573 1534573 := bbase (se 3 (by rfl) ⟨287732, by rfl⟩ : syracuseStep 1534573 = 575465) (by norm_num)
theorem B1010317 : Blo 896573 1010317 := bbase (se 3 (by rfl) ⟨189434, by rfl⟩ : syracuseStep 1010317 = 378869) (by norm_num)
theorem B1436309 : Blo 896573 1436309 := bbase (se 6 (by rfl) ⟨33663, by rfl⟩ : syracuseStep 1436309 = 67327) (by norm_num)
theorem B2026133 : Blo 896573 2026133 := bbase (se 6 (by rfl) ⟨47487, by rfl⟩ : syracuseStep 2026133 = 94975) (by norm_num)
theorem B1010353 : Blo 896573 1010353 := bbase (se 2 (by rfl) ⟨378882, by rfl⟩ : syracuseStep 1010353 = 757765) (by norm_num)
theorem B1010389 : Blo 896573 1010389 := bbase (se 7 (by rfl) ⟨11840, by rfl⟩ : syracuseStep 1010389 = 23681) (by norm_num)
theorem B2026205 : Blo 896573 2026205 := bbase (se 3 (by rfl) ⟨379913, by rfl⟩ : syracuseStep 2026205 = 759827) (by norm_num)
theorem B912101 : Blo 896573 912101 := bbase (se 4 (by rfl) ⟨85509, by rfl⟩ : syracuseStep 912101 = 171019) (by norm_num)
theorem B1010425 : Blo 896573 1010425 := bbase (se 2 (by rfl) ⟨378909, by rfl⟩ : syracuseStep 1010425 = 757819) (by norm_num)
theorem B2878229 : Blo 896573 2878229 := bbase (se 6 (by rfl) ⟨67458, by rfl⟩ : syracuseStep 2878229 = 134917) (by norm_num)
theorem B1010461 : Blo 896573 1010461 := bbase (se 3 (by rfl) ⟨189461, by rfl⟩ : syracuseStep 1010461 = 378923) (by norm_num)
theorem B2026277 : Blo 896573 2026277 := bbase (se 4 (by rfl) ⟨189963, by rfl⟩ : syracuseStep 2026277 = 379927) (by norm_num)
theorem B1010497 : Blo 896573 1010497 := bbase (se 2 (by rfl) ⟨378936, by rfl⟩ : syracuseStep 1010497 = 757873) (by norm_num)
theorem B4549445 : Blo 896573 4549445 := bbase (se 4 (by rfl) ⟨426510, by rfl⟩ : syracuseStep 4549445 = 853021) (by norm_num)
theorem B1436501 : Blo 896573 1436501 := bbase (se 9 (by rfl) ⟨4208, by rfl⟩ : syracuseStep 1436501 = 8417) (by norm_num)
theorem B1010533 : Blo 896573 1010533 := bbase (se 4 (by rfl) ⟨94737, by rfl⟩ : syracuseStep 1010533 = 189475) (by norm_num)
theorem B1010569 : Blo 896573 1010569 := bbase (se 2 (by rfl) ⟨378963, by rfl⟩ : syracuseStep 1010569 = 757927) (by norm_num)
theorem B14740373 : Blo 896573 14740373 := bbase (se 6 (by rfl) ⟨345477, by rfl⟩ : syracuseStep 14740373 = 690955) (by norm_num)
theorem B1010605 : Blo 896573 1010605 := bbase (se 3 (by rfl) ⟨189488, by rfl⟩ : syracuseStep 1010605 = 378977) (by norm_num)
theorem B1010641 : Blo 896573 1010641 := bbase (se 2 (by rfl) ⟨378990, by rfl⟩ : syracuseStep 1010641 = 757981) (by norm_num)
theorem B1436629 : Blo 896573 1436629 := bbase (se 7 (by rfl) ⟨16835, by rfl⟩ : syracuseStep 1436629 = 33671) (by norm_num)
theorem B1010677 : Blo 896573 1010677 := bbase (se 5 (by rfl) ⟨47375, by rfl⟩ : syracuseStep 1010677 = 94751) (by norm_num)
theorem B1010713 : Blo 896573 1010713 := bbase (se 2 (by rfl) ⟨379017, by rfl⟩ : syracuseStep 1010713 = 758035) (by norm_num)
theorem B1010749 : Blo 896573 1010749 := bbase (se 3 (by rfl) ⟨189515, by rfl⟩ : syracuseStep 1010749 = 379031) (by norm_num)
theorem B1010785 : Blo 896573 1010785 := bbase (se 2 (by rfl) ⟨379044, by rfl⟩ : syracuseStep 1010785 = 758089) (by norm_num)
theorem B1010821 : Blo 896573 1010821 := bbase (se 4 (by rfl) ⟨94764, by rfl⟩ : syracuseStep 1010821 = 189529) (by norm_num)
theorem B1010857 : Blo 896573 1010857 := bbase (se 2 (by rfl) ⟨379071, by rfl⟩ : syracuseStep 1010857 = 758143) (by norm_num)
theorem B1010893 : Blo 896573 1010893 := bbase (se 3 (by rfl) ⟨189542, by rfl⟩ : syracuseStep 1010893 = 379085) (by norm_num)
theorem B1010929 : Blo 896573 1010929 := bbase (se 2 (by rfl) ⟨379098, by rfl⟩ : syracuseStep 1010929 = 758197) (by norm_num)
theorem B1010965 : Blo 896573 1010965 := bbase (se 6 (by rfl) ⟨23694, by rfl⟩ : syracuseStep 1010965 = 47389) (by norm_num)
theorem B912665 : Blo 896573 912665 := bbase (se 2 (by rfl) ⟨342249, by rfl⟩ : syracuseStep 912665 = 684499) (by norm_num)
theorem B1011001 : Blo 896573 1011001 := bbase (se 2 (by rfl) ⟨379125, by rfl⟩ : syracuseStep 1011001 = 758251) (by norm_num)
theorem B1011037 : Blo 896573 1011037 := bbase (se 3 (by rfl) ⟨189569, by rfl⟩ : syracuseStep 1011037 = 379139) (by norm_num)
theorem B1011073 : Blo 896573 1011073 := bbase (se 2 (by rfl) ⟨379152, by rfl⟩ : syracuseStep 1011073 = 758305) (by norm_num)
theorem B4091285 : Blo 896573 4091285 := bbase (se 6 (by rfl) ⟨95889, by rfl⟩ : syracuseStep 4091285 = 191779) (by norm_num)
theorem B1011109 : Blo 896573 1011109 := bbase (se 4 (by rfl) ⟨94791, by rfl⟩ : syracuseStep 1011109 = 189583) (by norm_num)
theorem B1011145 : Blo 896573 1011145 := bbase (se 2 (by rfl) ⟨379179, by rfl⟩ : syracuseStep 1011145 = 758359) (by norm_num)
theorem B1011181 : Blo 896573 1011181 := bbase (se 3 (by rfl) ⟨189596, by rfl⟩ : syracuseStep 1011181 = 379193) (by norm_num)
theorem B1011217 : Blo 896573 1011217 := bbase (se 2 (by rfl) ⟨379206, by rfl⟩ : syracuseStep 1011217 = 758413) (by norm_num)
theorem B1011253 : Blo 896573 1011253 := bbase (se 5 (by rfl) ⟨47402, by rfl⟩ : syracuseStep 1011253 = 94805) (by norm_num)
theorem B1437269 : Blo 896573 1437269 := bbase (se 8 (by rfl) ⟨8421, by rfl⟩ : syracuseStep 1437269 = 16843) (by norm_num)
theorem B1011289 : Blo 896573 1011289 := bbase (se 2 (by rfl) ⟨379233, by rfl⟩ : syracuseStep 1011289 = 758467) (by norm_num)
theorem B1011325 : Blo 896573 1011325 := bbase (se 3 (by rfl) ⟨189623, by rfl⟩ : syracuseStep 1011325 = 379247) (by norm_num)
theorem B1011361 : Blo 896573 1011361 := bbase (se 2 (by rfl) ⟨379260, by rfl⟩ : syracuseStep 1011361 = 758521) (by norm_num)
theorem B1011397 : Blo 896573 1011397 := bbase (se 4 (by rfl) ⟨94818, by rfl⟩ : syracuseStep 1011397 = 189637) (by norm_num)
theorem B1011433 : Blo 896573 1011433 := bbase (se 2 (by rfl) ⟨379287, by rfl⟩ : syracuseStep 1011433 = 758575) (by norm_num)
theorem B1011469 : Blo 896573 1011469 := bbase (se 3 (by rfl) ⟨189650, by rfl⟩ : syracuseStep 1011469 = 379301) (by norm_num)
theorem B1011505 : Blo 896573 1011505 := bbase (se 2 (by rfl) ⟨379314, by rfl⟩ : syracuseStep 1011505 = 758629) (by norm_num)
theorem B1011541 : Blo 896573 1011541 := bbase (se 9 (by rfl) ⟨2963, by rfl⟩ : syracuseStep 1011541 = 5927) (by norm_num)
theorem B6647669 : Blo 896573 6647669 := bbase (se 5 (by rfl) ⟨311609, by rfl⟩ : syracuseStep 6647669 = 623219) (by norm_num)
theorem B3239797 : Blo 896573 3239797 := bbase (se 5 (by rfl) ⟨151865, by rfl⟩ : syracuseStep 3239797 = 303731) (by norm_num)
theorem B1011577 : Blo 896573 1011577 := bbase (se 2 (by rfl) ⟨379341, by rfl⟩ : syracuseStep 1011577 = 758683) (by norm_num)
theorem B1011613 : Blo 896573 1011613 := bbase (se 3 (by rfl) ⟨189677, by rfl⟩ : syracuseStep 1011613 = 379355) (by norm_num)
theorem B1011649 : Blo 896573 1011649 := bbase (se 2 (by rfl) ⟨379368, by rfl⟩ : syracuseStep 1011649 = 758737) (by norm_num)
theorem B1011685 : Blo 896573 1011685 := bbase (se 4 (by rfl) ⟨94845, by rfl⟩ : syracuseStep 1011685 = 189691) (by norm_num)
theorem B1011721 : Blo 896573 1011721 := bbase (se 2 (by rfl) ⟨379395, by rfl⟩ : syracuseStep 1011721 = 758791) (by norm_num)
theorem B1437725 : Blo 896573 1437725 := bbase (se 3 (by rfl) ⟨269573, by rfl⟩ : syracuseStep 1437725 = 539147) (by norm_num)
theorem B1011757 : Blo 896573 1011757 := bbase (se 3 (by rfl) ⟨189704, by rfl⟩ : syracuseStep 1011757 = 379409) (by norm_num)
theorem B1011793 : Blo 896573 1011793 := bbase (se 2 (by rfl) ⟨379422, by rfl⟩ : syracuseStep 1011793 = 758845) (by norm_num)
theorem B4550741 : Blo 896573 4550741 := bbase (se 8 (by rfl) ⟨26664, by rfl⟩ : syracuseStep 4550741 = 53329) (by norm_num)
theorem B1011829 : Blo 896573 1011829 := bbase (se 5 (by rfl) ⟨47429, by rfl⟩ : syracuseStep 1011829 = 94859) (by norm_num)
theorem B1011865 : Blo 896573 1011865 := bbase (se 2 (by rfl) ⟨379449, by rfl⟩ : syracuseStep 1011865 = 758899) (by norm_num)
theorem B1011901 : Blo 896573 1011901 := bbase (se 3 (by rfl) ⟨189731, by rfl⟩ : syracuseStep 1011901 = 379463) (by norm_num)
theorem B1011937 : Blo 896573 1011937 := bbase (se 2 (by rfl) ⟨379476, by rfl⟩ : syracuseStep 1011937 = 758953) (by norm_num)
theorem B1437949 : Blo 896573 1437949 := bbase (se 3 (by rfl) ⟨269615, by rfl⟩ : syracuseStep 1437949 = 539231) (by norm_num)
theorem B1011973 : Blo 896573 1011973 := bbase (se 4 (by rfl) ⟨94872, by rfl⟩ : syracuseStep 1011973 = 189745) (by norm_num)
theorem B1012009 : Blo 896573 1012009 := bbase (se 2 (by rfl) ⟨379503, by rfl⟩ : syracuseStep 1012009 = 759007) (by norm_num)
theorem B1438013 : Blo 896573 1438013 := bbase (se 3 (by rfl) ⟨269627, by rfl⟩ : syracuseStep 1438013 = 539255) (by norm_num)
theorem B1012045 : Blo 896573 1012045 := bbase (se 3 (by rfl) ⟨189758, by rfl⟩ : syracuseStep 1012045 = 379517) (by norm_num)
theorem B1012081 : Blo 896573 1012081 := bbase (se 2 (by rfl) ⟨379530, by rfl⟩ : syracuseStep 1012081 = 759061) (by norm_num)
theorem B1012117 : Blo 896573 1012117 := bbase (se 6 (by rfl) ⟨23721, by rfl⟩ : syracuseStep 1012117 = 47443) (by norm_num)
theorem B1012153 : Blo 896573 1012153 := bbase (se 2 (by rfl) ⟨379557, by rfl⟩ : syracuseStep 1012153 = 759115) (by norm_num)
theorem B1438141 : Blo 896573 1438141 := bbase (se 3 (by rfl) ⟨269651, by rfl⟩ : syracuseStep 1438141 = 539303) (by norm_num)
theorem B1012189 : Blo 896573 1012189 := bbase (se 3 (by rfl) ⟨189785, by rfl⟩ : syracuseStep 1012189 = 379571) (by norm_num)
theorem B1012225 : Blo 896573 1012225 := bbase (se 2 (by rfl) ⟨379584, by rfl⟩ : syracuseStep 1012225 = 759169) (by norm_num)
theorem B1012261 : Blo 896573 1012261 := bbase (se 4 (by rfl) ⟨94899, by rfl⟩ : syracuseStep 1012261 = 189799) (by norm_num)
theorem B1012297 : Blo 896573 1012297 := bbase (se 2 (by rfl) ⟨379611, by rfl⟩ : syracuseStep 1012297 = 759223) (by norm_num)
theorem B1012333 : Blo 896573 1012333 := bbase (se 3 (by rfl) ⟨189812, by rfl⟩ : syracuseStep 1012333 = 379625) (by norm_num)
theorem B1012369 : Blo 896573 1012369 := bbase (se 2 (by rfl) ⟨379638, by rfl⟩ : syracuseStep 1012369 = 759277) (by norm_num)
theorem B16642709 : Blo 896573 16642709 := bbase (se 6 (by rfl) ⟨390063, by rfl⟩ : syracuseStep 16642709 = 780127) (by norm_num)
theorem B4321957 : Blo 896573 4321957 := bbase (se 4 (by rfl) ⟨405183, by rfl⟩ : syracuseStep 4321957 = 810367) (by norm_num)
theorem B1012405 : Blo 896573 1012405 := bbase (se 5 (by rfl) ⟨47456, by rfl⟩ : syracuseStep 1012405 = 94913) (by norm_num)
theorem B7664341 : Blo 896573 7664341 := bbase (se 7 (by rfl) ⟨89816, by rfl⟩ : syracuseStep 7664341 = 179633) (by norm_num)
theorem B1012441 : Blo 896573 1012441 := bbase (se 2 (by rfl) ⟨379665, by rfl⟩ : syracuseStep 1012441 = 759331) (by norm_num)
theorem B1012477 : Blo 896573 1012477 := bbase (se 3 (by rfl) ⟨189839, by rfl⟩ : syracuseStep 1012477 = 379679) (by norm_num)
theorem B1012513 : Blo 896573 1012513 := bbase (se 2 (by rfl) ⟨379692, by rfl⟩ : syracuseStep 1012513 = 759385) (by norm_num)
theorem B1012549 : Blo 896573 1012549 := bbase (se 4 (by rfl) ⟨94926, by rfl⟩ : syracuseStep 1012549 = 189853) (by norm_num)
theorem B1012585 : Blo 896573 1012585 := bbase (se 2 (by rfl) ⟨379719, by rfl⟩ : syracuseStep 1012585 = 759439) (by norm_num)
theorem B1012621 : Blo 896573 1012621 := bbase (se 3 (by rfl) ⟨189866, by rfl⟩ : syracuseStep 1012621 = 379733) (by norm_num)
theorem B1012657 : Blo 896573 1012657 := bbase (se 2 (by rfl) ⟨379746, by rfl⟩ : syracuseStep 1012657 = 759493) (by norm_num)
theorem B1012693 : Blo 896573 1012693 := bbase (se 7 (by rfl) ⟨11867, by rfl⟩ : syracuseStep 1012693 = 23735) (by norm_num)
theorem B2880485 : Blo 896573 2880485 := bbase (se 4 (by rfl) ⟨270045, by rfl⟩ : syracuseStep 2880485 = 540091) (by norm_num)
theorem B9204725 : Blo 896573 9204725 := bbase (se 5 (by rfl) ⟨431471, by rfl⟩ : syracuseStep 9204725 = 862943) (by norm_num)
theorem B1012729 : Blo 896573 1012729 := bbase (se 2 (by rfl) ⟨379773, by rfl⟩ : syracuseStep 1012729 = 759547) (by norm_num)
theorem B1012765 : Blo 896573 1012765 := bbase (se 3 (by rfl) ⟨189893, by rfl⟩ : syracuseStep 1012765 = 379787) (by norm_num)
theorem B1012801 : Blo 896573 1012801 := bbase (se 2 (by rfl) ⟨379800, by rfl⟩ : syracuseStep 1012801 = 759601) (by norm_num)
theorem B2880613 : Blo 896573 2880613 := bbase (se 4 (by rfl) ⟨270057, by rfl⟩ : syracuseStep 2880613 = 540115) (by norm_num)
theorem B1012837 : Blo 896573 1012837 := bbase (se 4 (by rfl) ⟨94953, by rfl⟩ : syracuseStep 1012837 = 189907) (by norm_num)
theorem B1012873 : Blo 896573 1012873 := bbase (se 2 (by rfl) ⟨379827, by rfl⟩ : syracuseStep 1012873 = 759655) (by norm_num)
theorem B1799309 : Blo 896573 1799309 := bbase (se 3 (by rfl) ⟨337370, by rfl⟩ : syracuseStep 1799309 = 674741) (by norm_num)
theorem B1012909 : Blo 896573 1012909 := bbase (se 3 (by rfl) ⟨189920, by rfl⟩ : syracuseStep 1012909 = 379841) (by norm_num)
theorem B1012945 : Blo 896573 1012945 := bbase (se 2 (by rfl) ⟨379854, by rfl⟩ : syracuseStep 1012945 = 759709) (by norm_num)
theorem B1012981 : Blo 896573 1012981 := bbase (se 5 (by rfl) ⟨47483, by rfl⟩ : syracuseStep 1012981 = 94967) (by norm_num)
theorem B3241237 : Blo 896573 3241237 := bbase (se 6 (by rfl) ⟨75966, by rfl⟩ : syracuseStep 3241237 = 151933) (by norm_num)
theorem B1013017 : Blo 896573 1013017 := bbase (se 2 (by rfl) ⟨379881, by rfl⟩ : syracuseStep 1013017 = 759763) (by norm_num)
theorem B3831077 : Blo 896573 3831077 := bbase (se 4 (by rfl) ⟨359163, by rfl⟩ : syracuseStep 3831077 = 718327) (by norm_num)
theorem B1013053 : Blo 896573 1013053 := bbase (se 3 (by rfl) ⟨189947, by rfl⟩ : syracuseStep 1013053 = 379895) (by norm_num)
theorem B1078601 : Blo 896573 1078601 := bbase (se 2 (by rfl) ⟨404475, by rfl⟩ : syracuseStep 1078601 = 808951) (by norm_num)
theorem B1013089 : Blo 896573 1013089 := bbase (se 2 (by rfl) ⟨379908, by rfl⟩ : syracuseStep 1013089 = 759817) (by norm_num)
theorem B4552037 : Blo 896573 4552037 := bbase (se 4 (by rfl) ⟨426753, by rfl⟩ : syracuseStep 4552037 = 853507) (by norm_num)
theorem B2553221 : Blo 896573 2553221 := bbase (se 4 (by rfl) ⟨239364, by rfl⟩ : syracuseStep 2553221 = 478729) (by norm_num)
theorem B1013125 : Blo 896573 1013125 := bbase (se 4 (by rfl) ⟨94980, by rfl⟩ : syracuseStep 1013125 = 189961) (by norm_num)
theorem B8189461 : Blo 896573 8189461 := bbase (se 6 (by rfl) ⟨191940, by rfl⟩ : syracuseStep 8189461 = 383881) (by norm_num)
theorem B1439365 : Blo 896573 1439365 := bbase (se 4 (by rfl) ⟨134940, by rfl⟩ : syracuseStep 1439365 = 269881) (by norm_num)
theorem B1078933 : Blo 896573 1078933 := bbase (se 6 (by rfl) ⟨25287, by rfl⟩ : syracuseStep 1078933 = 50575) (by norm_num)
theorem B3405509 : Blo 896573 3405509 := bbase (se 4 (by rfl) ⟨319266, by rfl⟩ : syracuseStep 3405509 = 638533) (by norm_num)
theorem B1079077 : Blo 896573 1079077 := bbase (se 4 (by rfl) ⟨101163, by rfl⟩ : syracuseStep 1079077 = 202327) (by norm_num)
theorem B2160517 : Blo 896573 2160517 := bbase (se 4 (by rfl) ⟨202548, by rfl⟩ : syracuseStep 2160517 = 405097) (by norm_num)
theorem B4618133 : Blo 896573 4618133 := bbase (se 6 (by rfl) ⟨108237, by rfl⟩ : syracuseStep 4618133 = 216475) (by norm_num)
theorem B3405797 : Blo 896573 3405797 := bbase (se 4 (by rfl) ⟨319293, by rfl⟩ : syracuseStep 3405797 = 638587) (by norm_num)
theorem B2553893 : Blo 896573 2553893 := bbase (se 4 (by rfl) ⟨239427, by rfl⟩ : syracuseStep 2553893 = 478855) (by norm_num)
theorem B2160749 : Blo 896573 2160749 := bbase (se 3 (by rfl) ⟨405140, by rfl⟩ : syracuseStep 2160749 = 810281) (by norm_num)
theorem B1702109 : Blo 896573 1702109 := bbase (se 3 (by rfl) ⟨319145, by rfl⟩ : syracuseStep 1702109 = 638291) (by norm_num)
theorem B2160893 : Blo 896573 2160893 := bbase (se 3 (by rfl) ⟨405167, by rfl⟩ : syracuseStep 2160893 = 810335) (by norm_num)
theorem B3832069 : Blo 896573 3832069 := bbase (se 4 (by rfl) ⟨359256, by rfl⟩ : syracuseStep 3832069 = 718513) (by norm_num)
theorem B1440037 : Blo 896573 1440037 := bbase (se 4 (by rfl) ⟨135003, by rfl⟩ : syracuseStep 1440037 = 270007) (by norm_num)
theorem B2554325 : Blo 896573 2554325 := bbase (se 7 (by rfl) ⟨29933, by rfl⟩ : syracuseStep 2554325 = 59867) (by norm_num)
theorem B10222037 : Blo 896573 10222037 := bbase (se 7 (by rfl) ⟨119789, by rfl⟩ : syracuseStep 10222037 = 239579) (by norm_num)
theorem B2161133 : Blo 896573 2161133 := bbase (se 3 (by rfl) ⟨405212, by rfl⟩ : syracuseStep 2161133 = 810425) (by norm_num)
theorem B1702397 : Blo 896573 1702397 := bbase (se 3 (by rfl) ⟨319199, by rfl⟩ : syracuseStep 1702397 = 638399) (by norm_num)
theorem B3111509 : Blo 896573 3111509 := bbase (se 8 (by rfl) ⟨18231, by rfl⟩ : syracuseStep 3111509 = 36463) (by norm_num)
theorem B4553333 : Blo 896573 4553333 := bbase (se 5 (by rfl) ⟨213437, by rfl⟩ : syracuseStep 4553333 = 426875) (by norm_num)
theorem B1702549 : Blo 896573 1702549 := bbase (se 6 (by rfl) ⟨39903, by rfl⟩ : syracuseStep 1702549 = 79807) (by norm_num)
theorem B7666325 : Blo 896573 7666325 := bbase (se 6 (by rfl) ⟨179679, by rfl⟩ : syracuseStep 7666325 = 359359) (by norm_num)
theorem B1080101 : Blo 896573 1080101 := bbase (se 4 (by rfl) ⟨101259, by rfl⟩ : syracuseStep 1080101 = 202519) (by norm_num)
theorem B2423621 : Blo 896573 2423621 := bbase (se 4 (by rfl) ⟨227214, by rfl⟩ : syracuseStep 2423621 = 454429) (by norm_num)
theorem B2423749 : Blo 896573 2423749 := bbase (se 4 (by rfl) ⟨227226, by rfl⟩ : syracuseStep 2423749 = 454453) (by norm_num)
theorem B1702853 : Blo 896573 1702853 := bbase (se 4 (by rfl) ⟨159642, by rfl⟩ : syracuseStep 1702853 = 319285) (by norm_num)
theorem B3406981 : Blo 896573 3406981 := bbase (se 4 (by rfl) ⟨319404, by rfl⟩ : syracuseStep 3406981 = 638809) (by norm_num)
theorem B3636389 : Blo 896573 3636389 := bbase (se 4 (by rfl) ⟨340911, by rfl⟩ : syracuseStep 3636389 = 681823) (by norm_num)
theorem B2555077 : Blo 896573 2555077 := bbase (se 4 (by rfl) ⟨239538, by rfl⟩ : syracuseStep 2555077 = 479077) (by norm_num)
theorem B2161901 : Blo 896573 2161901 := bbase (se 3 (by rfl) ⟨405356, by rfl⟩ : syracuseStep 2161901 = 810713) (by norm_num)
theorem B1441037 : Blo 896573 1441037 := bbase (se 3 (by rfl) ⟨270194, by rfl⟩ : syracuseStep 1441037 = 540389) (by norm_num)
theorem B3407285 : Blo 896573 3407285 := bbase (se 5 (by rfl) ⟨159716, by rfl⟩ : syracuseStep 3407285 = 319433) (by norm_num)
theorem B5766709 : Blo 896573 5766709 := bbase (se 5 (by rfl) ⟨270314, by rfl⟩ : syracuseStep 5766709 = 540629) (by norm_num)
theorem B1703605 : Blo 896573 1703605 := bbase (se 5 (by rfl) ⟨79856, by rfl⟩ : syracuseStep 1703605 = 159713) (by norm_num)
theorem B1703749 : Blo 896573 1703749 := bbase (se 4 (by rfl) ⟨159726, by rfl⟩ : syracuseStep 1703749 = 319453) (by norm_num)
theorem B10944341 : Blo 896573 10944341 := bbase (se 9 (by rfl) ⟨32063, by rfl⟩ : syracuseStep 10944341 = 64127) (by norm_num)
theorem B1539965 : Blo 896573 1539965 := bbase (se 3 (by rfl) ⟨288743, by rfl⟩ : syracuseStep 1539965 = 577487) (by norm_num)
theorem B4554629 : Blo 896573 4554629 := bbase (se 4 (by rfl) ⟨426996, by rfl⟩ : syracuseStep 4554629 = 853993) (by norm_num)
theorem B1277869 : Blo 896573 1277869 := bbase (se 3 (by rfl) ⟨239600, by rfl⟩ : syracuseStep 1277869 = 479201) (by norm_num)
theorem B2883509 : Blo 896573 2883509 := bbase (se 5 (by rfl) ⟨135164, by rfl⟩ : syracuseStep 2883509 = 270329) (by norm_num)
theorem B1081297 : Blo 896573 1081297 := bbase (se 2 (by rfl) ⟨405486, by rfl⟩ : syracuseStep 1081297 = 810973) (by norm_num)
theorem B1703909 : Blo 896573 1703909 := bbase (se 4 (by rfl) ⟨159741, by rfl⟩ : syracuseStep 1703909 = 319483) (by norm_num)
theorem B19660853 : Blo 896573 19660853 := bstep (se 5 (by rfl) ⟨921602, by rfl⟩ : syracuseStep 19660853 = 1843205) B1843205
theorem B5767301 : Blo 896573 5767301 := bstep (se 4 (by rfl) ⟨540684, by rfl⟩ : syracuseStep 5767301 = 1081369) B1081369
theorem B1081523 : Blo 896573 1081523 := bstep (se 1 (by rfl) ⟨811142, by rfl⟩ : syracuseStep 1081523 = 1622285) B1622285
theorem B2916593 : Blo 896573 2916593 := bstep (se 2 (by rfl) ⟨1093722, by rfl⟩ : syracuseStep 2916593 = 2187445) B2187445
theorem B3408227 : Blo 896573 3408227 := bstep (se 1 (by rfl) ⟨2556170, by rfl⟩ : syracuseStep 3408227 = 5112341) B5112341
theorem B2425265 : Blo 896573 2425265 := bstep (se 2 (by rfl) ⟨909474, by rfl⟩ : syracuseStep 2425265 = 1818949) B1818949
theorem B1278433 : Blo 896573 1278433 := bstep (se 2 (by rfl) ⟨479412, by rfl⟩ : syracuseStep 1278433 = 958825) B958825
theorem B2884099 : Blo 896573 2884099 := bstep (se 1 (by rfl) ⟨2163074, by rfl⟩ : syracuseStep 2884099 = 4326149) B4326149
theorem B4555277 : Blo 896573 4555277 := bstep (se 3 (by rfl) ⟨854114, by rfl⟩ : syracuseStep 4555277 = 1708229) B1708229
theorem B2556593 : Blo 896573 2556593 := bstep (se 2 (by rfl) ⟨958722, by rfl⟩ : syracuseStep 2556593 = 1917445) B1917445
theorem B1704721 : Blo 896573 1704721 := bstep (se 2 (by rfl) ⟨639270, by rfl⟩ : syracuseStep 1704721 = 1278541) B1278541
theorem B2884369 : Blo 896573 2884369 := bstep (se 2 (by rfl) ⟨1081638, by rfl⟩ : syracuseStep 2884369 = 2163277) B2163277
theorem B1278769 : Blo 896573 1278769 := bstep (se 2 (by rfl) ⟨479538, by rfl⟩ : syracuseStep 1278769 = 959077) B959077
theorem B3834701 : Blo 896573 3834701 := bstep (se 3 (by rfl) ⟨719006, by rfl⟩ : syracuseStep 3834701 = 1438013) B1438013
theorem B2556785 : Blo 896573 2556785 := bstep (se 2 (by rfl) ⟨958794, by rfl⟩ : syracuseStep 2556785 = 1917589) B1917589
theorem B1704881 : Blo 896573 1704881 := bstep (se 2 (by rfl) ⟨639330, by rfl⟩ : syracuseStep 1704881 = 1278661) B1278661
theorem B2458925 : Blo 896573 2458925 := bstep (se 3 (by rfl) ⟨461048, by rfl⟩ : syracuseStep 2458925 = 922097) B922097
theorem B1705283 : Blo 896573 1705283 := bstep (se 1 (by rfl) ⟨1278962, by rfl⟩ : syracuseStep 1705283 = 2557925) B2557925
theorem B3409229 : Blo 896573 3409229 := bstep (se 3 (by rfl) ⟨639230, by rfl⟩ : syracuseStep 3409229 = 1278461) B1278461
theorem B1344881 : Blo 896573 1344881 := bstep (se 2 (by rfl) ⟨504330, by rfl⟩ : syracuseStep 1344881 = 1008661) B1008661
theorem B1279361 : Blo 896573 1279361 := bstep (se 2 (by rfl) ⟨479760, by rfl⟩ : syracuseStep 1279361 = 959521) B959521
theorem B1344899 : Blo 896573 1344899 := bstep (se 1 (by rfl) ⟨1008674, by rfl⟩ : syracuseStep 1344899 = 2017349) B2017349
theorem B1344929 : Blo 896573 1344929 := bstep (se 2 (by rfl) ⟨504348, by rfl⟩ : syracuseStep 1344929 = 1008697) B1008697
theorem B1344947 : Blo 896573 1344947 := bstep (se 1 (by rfl) ⟨1008710, by rfl⟩ : syracuseStep 1344947 = 2017421) B2017421
theorem B1344977 : Blo 896573 1344977 := bstep (se 2 (by rfl) ⟨504366, by rfl⟩ : syracuseStep 1344977 = 1008733) B1008733
theorem B1213907 : Blo 896573 1213907 := bstep (se 1 (by rfl) ⟨910430, by rfl⟩ : syracuseStep 1213907 = 1820861) B1820861
theorem B1344995 : Blo 896573 1344995 := bstep (se 1 (by rfl) ⟨1008746, by rfl⟩ : syracuseStep 1344995 = 2017493) B2017493
theorem B1345025 : Blo 896573 1345025 := bstep (se 2 (by rfl) ⟨504384, by rfl⟩ : syracuseStep 1345025 = 1008769) B1008769
theorem B1345043 : Blo 896573 1345043 := bstep (se 1 (by rfl) ⟨1008782, by rfl⟩ : syracuseStep 1345043 = 2017565) B2017565
theorem B1345073 : Blo 896573 1345073 := bstep (se 2 (by rfl) ⟨504402, by rfl⟩ : syracuseStep 1345073 = 1008805) B1008805
theorem B1345091 : Blo 896573 1345091 := bstep (se 1 (by rfl) ⟨1008818, by rfl⟩ : syracuseStep 1345091 = 2017637) B2017637
theorem B9864773 : Blo 896573 9864773 := bstep (se 4 (by rfl) ⟨924822, by rfl⟩ : syracuseStep 9864773 = 1849645) B1849645
theorem B1345121 : Blo 896573 1345121 := bstep (se 2 (by rfl) ⟨504420, by rfl⟩ : syracuseStep 1345121 = 1008841) B1008841
theorem B9733745 : Blo 896573 9733745 := bstep (se 2 (by rfl) ⟨3650154, by rfl⟩ : syracuseStep 9733745 = 7300309) B7300309
theorem B1345139 : Blo 896573 1345139 := bstep (se 1 (by rfl) ⟨1008854, by rfl⟩ : syracuseStep 1345139 = 2017709) B2017709
theorem B1345169 : Blo 896573 1345169 := bstep (se 2 (by rfl) ⟨504438, by rfl⟩ : syracuseStep 1345169 = 1008877) B1008877
theorem B1345187 : Blo 896573 1345187 := bstep (se 1 (by rfl) ⟨1008890, by rfl⟩ : syracuseStep 1345187 = 2017781) B2017781
theorem B1345217 : Blo 896573 1345217 := bstep (se 2 (by rfl) ⟨504456, by rfl⟩ : syracuseStep 1345217 = 1008913) B1008913
theorem B1345235 : Blo 896573 1345235 := bstep (se 1 (by rfl) ⟨1008926, by rfl⟩ : syracuseStep 1345235 = 2017853) B2017853
theorem B1345265 : Blo 896573 1345265 := bstep (se 2 (by rfl) ⟨504474, by rfl⟩ : syracuseStep 1345265 = 1008949) B1008949
theorem B1345283 : Blo 896573 1345283 := bstep (se 1 (by rfl) ⟨1008962, by rfl⟩ : syracuseStep 1345283 = 2017925) B2017925
theorem B1345313 : Blo 896573 1345313 := bstep (se 2 (by rfl) ⟨504492, by rfl⟩ : syracuseStep 1345313 = 1008985) B1008985
theorem B1345331 : Blo 896573 1345331 := bstep (se 1 (by rfl) ⟨1008998, by rfl⟩ : syracuseStep 1345331 = 2017997) B2017997
theorem B1345361 : Blo 896573 1345361 := bstep (se 2 (by rfl) ⟨504510, by rfl⟩ : syracuseStep 1345361 = 1009021) B1009021
theorem B2557777 : Blo 896573 2557777 := bstep (se 2 (by rfl) ⟨959166, by rfl⟩ : syracuseStep 2557777 = 1918333) B1918333
theorem B1345379 : Blo 896573 1345379 := bstep (se 1 (by rfl) ⟨1009034, by rfl⟩ : syracuseStep 1345379 = 2018069) B2018069
theorem B1345409 : Blo 896573 1345409 := bstep (se 2 (by rfl) ⟨504528, by rfl⟩ : syracuseStep 1345409 = 1009057) B1009057
theorem B1345427 : Blo 896573 1345427 := bstep (se 1 (by rfl) ⟨1009070, by rfl⟩ : syracuseStep 1345427 = 2018141) B2018141
theorem B1279891 : Blo 896573 1279891 := bstep (se 1 (by rfl) ⟨959918, by rfl⟩ : syracuseStep 1279891 = 1919837) B1919837
theorem B1345457 : Blo 896573 1345457 := bstep (se 2 (by rfl) ⟨504546, by rfl⟩ : syracuseStep 1345457 = 1009093) B1009093
theorem B1345475 : Blo 896573 1345475 := bstep (se 1 (by rfl) ⟨1009106, by rfl⟩ : syracuseStep 1345475 = 2018213) B2018213
theorem B1345505 : Blo 896573 1345505 := bstep (se 2 (by rfl) ⟨504564, by rfl⟩ : syracuseStep 1345505 = 1009129) B1009129
theorem B1345523 : Blo 896573 1345523 := bstep (se 1 (by rfl) ⟨1009142, by rfl⟩ : syracuseStep 1345523 = 2018285) B2018285
theorem B1345553 : Blo 896573 1345553 := bstep (se 2 (by rfl) ⟨504582, by rfl⟩ : syracuseStep 1345553 = 1009165) B1009165
theorem B1345571 : Blo 896573 1345571 := bstep (se 1 (by rfl) ⟨1009178, by rfl⟩ : syracuseStep 1345571 = 2018357) B2018357
theorem B1345601 : Blo 896573 1345601 := bstep (se 2 (by rfl) ⟨504600, by rfl⟩ : syracuseStep 1345601 = 1009201) B1009201
theorem B1345619 : Blo 896573 1345619 := bstep (se 1 (by rfl) ⟨1009214, by rfl⟩ : syracuseStep 1345619 = 2018429) B2018429
theorem B2558051 : Blo 896573 2558051 := bstep (se 1 (by rfl) ⟨1918538, by rfl⟩ : syracuseStep 2558051 = 3837077) B3837077
theorem B1345649 : Blo 896573 1345649 := bstep (se 2 (by rfl) ⟨504618, by rfl⟩ : syracuseStep 1345649 = 1009237) B1009237
theorem B35063921 : Blo 896573 35063921 := bstep (se 2 (by rfl) ⟨13148970, by rfl⟩ : syracuseStep 35063921 = 26297941) B26297941
theorem B1345667 : Blo 896573 1345667 := bstep (se 1 (by rfl) ⟨1009250, by rfl⟩ : syracuseStep 1345667 = 2018501) B2018501
theorem B1345697 : Blo 896573 1345697 := bstep (se 2 (by rfl) ⟨504636, by rfl⟩ : syracuseStep 1345697 = 1009273) B1009273
theorem B1345715 : Blo 896573 1345715 := bstep (se 1 (by rfl) ⟨1009286, by rfl⟩ : syracuseStep 1345715 = 2018573) B2018573
theorem B1706179 : Blo 896573 1706179 := bstep (se 1 (by rfl) ⟨1279634, by rfl⟩ : syracuseStep 1706179 = 2559269) B2559269
theorem B1345745 : Blo 896573 1345745 := bstep (se 2 (by rfl) ⟨504654, by rfl⟩ : syracuseStep 1345745 = 1009309) B1009309
theorem B1345763 : Blo 896573 1345763 := bstep (se 1 (by rfl) ⟨1009322, by rfl⟩ : syracuseStep 1345763 = 2018645) B2018645
theorem B1280227 : Blo 896573 1280227 := bstep (se 1 (by rfl) ⟨960170, by rfl⟩ : syracuseStep 1280227 = 1920341) B1920341
theorem B1345793 : Blo 896573 1345793 := bstep (se 2 (by rfl) ⟨504672, by rfl⟩ : syracuseStep 1345793 = 1009345) B1009345
theorem B5114117 : Blo 896573 5114117 := bstep (se 4 (by rfl) ⟨479448, by rfl⟩ : syracuseStep 5114117 = 958897) B958897
theorem B1345811 : Blo 896573 1345811 := bstep (se 1 (by rfl) ⟨1009358, by rfl⟩ : syracuseStep 1345811 = 2018717) B2018717
theorem B2558243 : Blo 896573 2558243 := bstep (se 1 (by rfl) ⟨1918682, by rfl⟩ : syracuseStep 2558243 = 3837365) B3837365
theorem B1345841 : Blo 896573 1345841 := bstep (se 2 (by rfl) ⟨504690, by rfl⟩ : syracuseStep 1345841 = 1009381) B1009381
theorem B1345859 : Blo 896573 1345859 := bstep (se 1 (by rfl) ⟨1009394, by rfl⟩ : syracuseStep 1345859 = 2018789) B2018789
theorem B1345889 : Blo 896573 1345889 := bstep (se 2 (by rfl) ⟨504708, by rfl⟩ : syracuseStep 1345889 = 1009417) B1009417
theorem B1706339 : Blo 896573 1706339 := bstep (se 1 (by rfl) ⟨1279754, by rfl⟩ : syracuseStep 1706339 = 2559509) B2559509
theorem B1345907 : Blo 896573 1345907 := bstep (se 1 (by rfl) ⟨1009430, by rfl⟩ : syracuseStep 1345907 = 2018861) B2018861
theorem B1345937 : Blo 896573 1345937 := bstep (se 2 (by rfl) ⟨504726, by rfl⟩ : syracuseStep 1345937 = 1009453) B1009453
theorem B1345955 : Blo 896573 1345955 := bstep (se 1 (by rfl) ⟨1009466, by rfl⟩ : syracuseStep 1345955 = 2018933) B2018933
theorem B1345985 : Blo 896573 1345985 := bstep (se 2 (by rfl) ⟨504744, by rfl⟩ : syracuseStep 1345985 = 1009489) B1009489
theorem B1346003 : Blo 896573 1346003 := bstep (se 1 (by rfl) ⟨1009502, by rfl⟩ : syracuseStep 1346003 = 2019005) B2019005
theorem B1346033 : Blo 896573 1346033 := bstep (se 2 (by rfl) ⟨504762, by rfl⟩ : syracuseStep 1346033 = 1009525) B1009525
theorem B4098545 : Blo 896573 4098545 := bstep (se 2 (by rfl) ⟨1536954, by rfl⟩ : syracuseStep 4098545 = 3073909) B3073909
theorem B1346051 : Blo 896573 1346051 := bstep (se 1 (by rfl) ⟨1009538, by rfl⟩ : syracuseStep 1346051 = 2019077) B2019077
theorem B1346081 : Blo 896573 1346081 := bstep (se 2 (by rfl) ⟨504780, by rfl⟩ : syracuseStep 1346081 = 1009561) B1009561
theorem B1346099 : Blo 896573 1346099 := bstep (se 1 (by rfl) ⟨1009574, by rfl⟩ : syracuseStep 1346099 = 2019149) B2019149
theorem B5474893 : Blo 896573 5474893 := bstep (se 3 (by rfl) ⟨1026542, by rfl⟩ : syracuseStep 5474893 = 2053085) B2053085
theorem B1346129 : Blo 896573 1346129 := bstep (se 2 (by rfl) ⟨504798, by rfl⟩ : syracuseStep 1346129 = 1009597) B1009597
theorem B1346147 : Blo 896573 1346147 := bstep (se 1 (by rfl) ⟨1009610, by rfl⟩ : syracuseStep 1346147 = 2019221) B2019221
theorem B1346177 : Blo 896573 1346177 := bstep (se 2 (by rfl) ⟨504816, by rfl⟩ : syracuseStep 1346177 = 1009633) B1009633
theorem B1346195 : Blo 896573 1346195 := bstep (se 1 (by rfl) ⟨1009646, by rfl⟩ : syracuseStep 1346195 = 2019293) B2019293
theorem B1346225 : Blo 896573 1346225 := bstep (se 2 (by rfl) ⟨504834, by rfl⟩ : syracuseStep 1346225 = 1009669) B1009669
theorem B1346243 : Blo 896573 1346243 := bstep (se 1 (by rfl) ⟨1009682, by rfl⟩ : syracuseStep 1346243 = 2019365) B2019365
theorem B5114573 : Blo 896573 5114573 := bstep (se 3 (by rfl) ⟨958982, by rfl⟩ : syracuseStep 5114573 = 1917965) B1917965
theorem B1346273 : Blo 896573 1346273 := bstep (se 2 (by rfl) ⟨504852, by rfl⟩ : syracuseStep 1346273 = 1009705) B1009705
theorem B1346291 : Blo 896573 1346291 := bstep (se 1 (by rfl) ⟨1009718, by rfl⟩ : syracuseStep 1346291 = 2019437) B2019437
theorem B1346321 : Blo 896573 1346321 := bstep (se 2 (by rfl) ⟨504870, by rfl⟩ : syracuseStep 1346321 = 1009741) B1009741
theorem B1280785 : Blo 896573 1280785 := bstep (se 2 (by rfl) ⟨480294, by rfl⟩ : syracuseStep 1280785 = 960589) B960589
theorem B1346339 : Blo 896573 1346339 := bstep (se 1 (by rfl) ⟨1009754, by rfl⟩ : syracuseStep 1346339 = 2019509) B2019509
theorem B1280819 : Blo 896573 1280819 := bstep (se 1 (by rfl) ⟨960614, by rfl⟩ : syracuseStep 1280819 = 1921229) B1921229
theorem B1346369 : Blo 896573 1346369 := bstep (se 2 (by rfl) ⟨504888, by rfl⟩ : syracuseStep 1346369 = 1009777) B1009777
theorem B1477441 : Blo 896573 1477441 := bstep (se 2 (by rfl) ⟨554040, by rfl⟩ : syracuseStep 1477441 = 1108081) B1108081
theorem B1346387 : Blo 896573 1346387 := bstep (se 1 (by rfl) ⟨1009790, by rfl⟩ : syracuseStep 1346387 = 2019581) B2019581
theorem B1346417 : Blo 896573 1346417 := bstep (se 2 (by rfl) ⟨504906, by rfl⟩ : syracuseStep 1346417 = 1009813) B1009813
theorem B1346435 : Blo 896573 1346435 := bstep (se 1 (by rfl) ⟨1009826, by rfl⟩ : syracuseStep 1346435 = 2019653) B2019653
theorem B1346465 : Blo 896573 1346465 := bstep (se 2 (by rfl) ⟨504924, by rfl⟩ : syracuseStep 1346465 = 1009849) B1009849
theorem B1346483 : Blo 896573 1346483 := bstep (se 1 (by rfl) ⟨1009862, by rfl⟩ : syracuseStep 1346483 = 2019725) B2019725
theorem B1346513 : Blo 896573 1346513 := bstep (se 2 (by rfl) ⟨504942, by rfl⟩ : syracuseStep 1346513 = 1009885) B1009885
theorem B1346531 : Blo 896573 1346531 := bstep (se 1 (by rfl) ⟨1009898, by rfl⟩ : syracuseStep 1346531 = 2019797) B2019797
theorem B1346561 : Blo 896573 1346561 := bstep (se 2 (by rfl) ⟨504960, by rfl⟩ : syracuseStep 1346561 = 1009921) B1009921
theorem B1346579 : Blo 896573 1346579 := bstep (se 1 (by rfl) ⟨1009934, by rfl⟩ : syracuseStep 1346579 = 2019869) B2019869
theorem B1346609 : Blo 896573 1346609 := bstep (se 2 (by rfl) ⟨504978, by rfl⟩ : syracuseStep 1346609 = 1009957) B1009957
theorem B1346627 : Blo 896573 1346627 := bstep (se 1 (by rfl) ⟨1009970, by rfl⟩ : syracuseStep 1346627 = 2019941) B2019941
theorem B2559053 : Blo 896573 2559053 := bstep (se 3 (by rfl) ⟨479822, by rfl⟩ : syracuseStep 2559053 = 959645) B959645
theorem B1346657 : Blo 896573 1346657 := bstep (se 2 (by rfl) ⟨504996, by rfl⟩ : syracuseStep 1346657 = 1009993) B1009993
theorem B1346675 : Blo 896573 1346675 := bstep (se 1 (by rfl) ⟨1010006, by rfl⟩ : syracuseStep 1346675 = 2020013) B2020013
theorem B1346705 : Blo 896573 1346705 := bstep (se 2 (by rfl) ⟨505014, by rfl⟩ : syracuseStep 1346705 = 1010029) B1010029
theorem B1346723 : Blo 896573 1346723 := bstep (se 1 (by rfl) ⟨1010042, by rfl⟩ : syracuseStep 1346723 = 2020085) B2020085
theorem B1346753 : Blo 896573 1346753 := bstep (se 2 (by rfl) ⟨505032, by rfl⟩ : syracuseStep 1346753 = 1010065) B1010065
theorem B1346771 : Blo 896573 1346771 := bstep (se 1 (by rfl) ⟨1010078, by rfl⟩ : syracuseStep 1346771 = 2020157) B2020157
theorem B1346801 : Blo 896573 1346801 := bstep (se 2 (by rfl) ⟨505050, by rfl⟩ : syracuseStep 1346801 = 1010101) B1010101
theorem B8326385 : Blo 896573 8326385 := bstep (se 2 (by rfl) ⟨3122394, by rfl⟩ : syracuseStep 8326385 = 6244789) B6244789
theorem B1346819 : Blo 896573 1346819 := bstep (se 1 (by rfl) ⟨1010114, by rfl⟩ : syracuseStep 1346819 = 2020229) B2020229
theorem B2559235 : Blo 896573 2559235 := bstep (se 1 (by rfl) ⟨1919426, by rfl⟩ : syracuseStep 2559235 = 3838853) B3838853
theorem B1346849 : Blo 896573 1346849 := bstep (se 2 (by rfl) ⟨505068, by rfl⟩ : syracuseStep 1346849 = 1010137) B1010137
theorem B1248547 : Blo 896573 1248547 := bstep (se 1 (by rfl) ⟨936410, by rfl⟩ : syracuseStep 1248547 = 1872821) B1872821
theorem B1346867 : Blo 896573 1346867 := bstep (se 1 (by rfl) ⟨1010150, by rfl⟩ : syracuseStep 1346867 = 2020301) B2020301
theorem B1346897 : Blo 896573 1346897 := bstep (se 2 (by rfl) ⟨505086, by rfl⟩ : syracuseStep 1346897 = 1010173) B1010173
theorem B1281377 : Blo 896573 1281377 := bstep (se 2 (by rfl) ⟨480516, by rfl⟩ : syracuseStep 1281377 = 961033) B961033
theorem B1346915 : Blo 896573 1346915 := bstep (se 1 (by rfl) ⟨1010186, by rfl⟩ : syracuseStep 1346915 = 2020373) B2020373
theorem B4558193 : Blo 896573 4558193 := bstep (se 2 (by rfl) ⟨1709322, by rfl⟩ : syracuseStep 4558193 = 3418645) B3418645
theorem B1346945 : Blo 896573 1346945 := bstep (se 2 (by rfl) ⟨505104, by rfl⟩ : syracuseStep 1346945 = 1010209) B1010209
theorem B3411341 : Blo 896573 3411341 := bstep (se 3 (by rfl) ⟨639626, by rfl⟩ : syracuseStep 3411341 = 1279253) B1279253
theorem B1707409 : Blo 896573 1707409 := bstep (se 2 (by rfl) ⟨640278, by rfl⟩ : syracuseStep 1707409 = 1280557) B1280557
theorem B1346963 : Blo 896573 1346963 := bstep (se 1 (by rfl) ⟨1010222, by rfl⟩ : syracuseStep 1346963 = 2020445) B2020445
theorem B1346993 : Blo 896573 1346993 := bstep (se 2 (by rfl) ⟨505122, by rfl⟩ : syracuseStep 1346993 = 1010245) B1010245
theorem B1281457 : Blo 896573 1281457 := bstep (se 2 (by rfl) ⟨480546, by rfl⟩ : syracuseStep 1281457 = 961093) B961093
theorem B11505077 : Blo 896573 11505077 := bstep (se 5 (by rfl) ⟨539300, by rfl⟩ : syracuseStep 11505077 = 1078601) B1078601
theorem B1347011 : Blo 896573 1347011 := bstep (se 1 (by rfl) ⟨1010258, by rfl⟩ : syracuseStep 1347011 = 2020517) B2020517
theorem B1347041 : Blo 896573 1347041 := bstep (se 2 (by rfl) ⟨505140, by rfl⟩ : syracuseStep 1347041 = 1010281) B1010281
theorem B1347059 : Blo 896573 1347059 := bstep (se 1 (by rfl) ⟨1010294, by rfl⟩ : syracuseStep 1347059 = 2020589) B2020589
theorem B1347089 : Blo 896573 1347089 := bstep (se 2 (by rfl) ⟨505158, by rfl⟩ : syracuseStep 1347089 = 1010317) B1010317
theorem B1347107 : Blo 896573 1347107 := bstep (se 1 (by rfl) ⟨1010330, by rfl⟩ : syracuseStep 1347107 = 2020661) B2020661
theorem B1347137 : Blo 896573 1347137 := bstep (se 2 (by rfl) ⟨505176, by rfl⟩ : syracuseStep 1347137 = 1010353) B1010353
theorem B1347155 : Blo 896573 1347155 := bstep (se 1 (by rfl) ⟨1010366, by rfl⟩ : syracuseStep 1347155 = 2020733) B2020733
theorem B1347185 : Blo 896573 1347185 := bstep (se 2 (by rfl) ⟨505194, by rfl⟩ : syracuseStep 1347185 = 1010389) B1010389
theorem B1347203 : Blo 896573 1347203 := bstep (se 1 (by rfl) ⟨1010402, by rfl⟩ : syracuseStep 1347203 = 2020805) B2020805
theorem B1347233 : Blo 896573 1347233 := bstep (se 2 (by rfl) ⟨505212, by rfl⟩ : syracuseStep 1347233 = 1010425) B1010425
theorem B1347251 : Blo 896573 1347251 := bstep (se 1 (by rfl) ⟨1010438, by rfl⟩ : syracuseStep 1347251 = 2020877) B2020877
theorem B1347281 : Blo 896573 1347281 := bstep (se 2 (by rfl) ⟨505230, by rfl⟩ : syracuseStep 1347281 = 1010461) B1010461
theorem B1347299 : Blo 896573 1347299 := bstep (se 1 (by rfl) ⟨1010474, by rfl⟩ : syracuseStep 1347299 = 2020949) B2020949
theorem B2559725 : Blo 896573 2559725 := bstep (se 3 (by rfl) ⟨479948, by rfl⟩ : syracuseStep 2559725 = 959897) B959897
theorem B1216243 : Blo 896573 1216243 := bstep (se 1 (by rfl) ⟨912182, by rfl⟩ : syracuseStep 1216243 = 1824365) B1824365
theorem B1347329 : Blo 896573 1347329 := bstep (se 2 (by rfl) ⟨505248, by rfl⟩ : syracuseStep 1347329 = 1010497) B1010497
theorem B1347347 : Blo 896573 1347347 := bstep (se 1 (by rfl) ⟨1010510, by rfl⟩ : syracuseStep 1347347 = 2021021) B2021021
theorem B1347377 : Blo 896573 1347377 := bstep (se 2 (by rfl) ⟨505266, by rfl⟩ : syracuseStep 1347377 = 1010533) B1010533
theorem B1347395 : Blo 896573 1347395 := bstep (se 1 (by rfl) ⟨1010546, by rfl⟩ : syracuseStep 1347395 = 2021093) B2021093
theorem B1347425 : Blo 896573 1347425 := bstep (se 2 (by rfl) ⟨505284, by rfl⟩ : syracuseStep 1347425 = 1010569) B1010569
theorem B1347443 : Blo 896573 1347443 := bstep (se 1 (by rfl) ⟨1010582, by rfl⟩ : syracuseStep 1347443 = 2021165) B2021165
theorem B1347473 : Blo 896573 1347473 := bstep (se 2 (by rfl) ⟨505302, by rfl⟩ : syracuseStep 1347473 = 1010605) B1010605
theorem B1347491 : Blo 896573 1347491 := bstep (se 1 (by rfl) ⟨1010618, by rfl⟩ : syracuseStep 1347491 = 2021237) B2021237
theorem B1347521 : Blo 896573 1347521 := bstep (se 2 (by rfl) ⟨505320, by rfl⟩ : syracuseStep 1347521 = 1010641) B1010641
theorem B1347539 : Blo 896573 1347539 := bstep (se 1 (by rfl) ⟨1010654, by rfl⟩ : syracuseStep 1347539 = 2021309) B2021309
theorem B3411953 : Blo 896573 3411953 := bstep (se 2 (by rfl) ⟨1279482, by rfl⟩ : syracuseStep 3411953 = 2558965) B2558965
theorem B1347569 : Blo 896573 1347569 := bstep (se 2 (by rfl) ⟨505338, by rfl⟩ : syracuseStep 1347569 = 1010677) B1010677
theorem B1347587 : Blo 896573 1347587 := bstep (se 1 (by rfl) ⟨1010690, by rfl⟩ : syracuseStep 1347587 = 2021381) B2021381
theorem B6230029 : Blo 896573 6230029 := bstep (se 3 (by rfl) ⟨1168130, by rfl⟩ : syracuseStep 6230029 = 2336261) B2336261
theorem B987155 : Blo 896573 987155 := bstep (se 1 (by rfl) ⟨740366, by rfl⟩ : syracuseStep 987155 = 1480733) B1480733
theorem B1347617 : Blo 896573 1347617 := bstep (se 2 (by rfl) ⟨505356, by rfl⟩ : syracuseStep 1347617 = 1010713) B1010713
theorem B1347635 : Blo 896573 1347635 := bstep (se 1 (by rfl) ⟨1010726, by rfl⟩ : syracuseStep 1347635 = 2021453) B2021453
theorem B1347665 : Blo 896573 1347665 := bstep (se 2 (by rfl) ⟨505374, by rfl⟩ : syracuseStep 1347665 = 1010749) B1010749
theorem B1347683 : Blo 896573 1347683 := bstep (se 1 (by rfl) ⟨1010762, by rfl⟩ : syracuseStep 1347683 = 2021525) B2021525
theorem B1347713 : Blo 896573 1347713 := bstep (se 2 (by rfl) ⟨505392, by rfl⟩ : syracuseStep 1347713 = 1010785) B1010785
theorem B1347731 : Blo 896573 1347731 := bstep (se 1 (by rfl) ⟨1010798, by rfl⟩ : syracuseStep 1347731 = 2021597) B2021597
theorem B1216675 : Blo 896573 1216675 := bstep (se 1 (by rfl) ⟨912506, by rfl⟩ : syracuseStep 1216675 = 1825013) B1825013
theorem B1347761 : Blo 896573 1347761 := bstep (se 2 (by rfl) ⟨505410, by rfl⟩ : syracuseStep 1347761 = 1010821) B1010821
theorem B3412145 : Blo 896573 3412145 := bstep (se 2 (by rfl) ⟨1279554, by rfl⟩ : syracuseStep 3412145 = 2559109) B2559109
theorem B1347779 : Blo 896573 1347779 := bstep (se 1 (by rfl) ⟨1010834, by rfl⟩ : syracuseStep 1347779 = 2021669) B2021669
theorem B1282243 : Blo 896573 1282243 := bstep (se 1 (by rfl) ⟨961682, by rfl⟩ : syracuseStep 1282243 = 1923365) B1923365
theorem B6820037 : Blo 896573 6820037 := bstep (se 4 (by rfl) ⟨639378, by rfl⟩ : syracuseStep 6820037 = 1278757) B1278757
theorem B1347809 : Blo 896573 1347809 := bstep (se 2 (by rfl) ⟨505428, by rfl⟩ : syracuseStep 1347809 = 1010857) B1010857
theorem B3281123 : Blo 896573 3281123 := bstep (se 1 (by rfl) ⟨2460842, by rfl⟩ : syracuseStep 3281123 = 4921685) B4921685
theorem B1347827 : Blo 896573 1347827 := bstep (se 1 (by rfl) ⟨1010870, by rfl⟩ : syracuseStep 1347827 = 2021741) B2021741
theorem B2887949 : Blo 896573 2887949 := bstep (se 3 (by rfl) ⟨541490, by rfl⟩ : syracuseStep 2887949 = 1082981) B1082981
theorem B1347857 : Blo 896573 1347857 := bstep (se 2 (by rfl) ⟨505446, by rfl⟩ : syracuseStep 1347857 = 1010893) B1010893
theorem B1347875 : Blo 896573 1347875 := bstep (se 1 (by rfl) ⟨1010906, by rfl⟩ : syracuseStep 1347875 = 2021813) B2021813
theorem B1347905 : Blo 896573 1347905 := bstep (se 2 (by rfl) ⟨505464, by rfl⟩ : syracuseStep 1347905 = 1010929) B1010929
theorem B1347923 : Blo 896573 1347923 := bstep (se 1 (by rfl) ⟨1010942, by rfl⟩ : syracuseStep 1347923 = 2021885) B2021885
theorem B4854115 : Blo 896573 4854115 := bstep (se 1 (by rfl) ⟨3640586, by rfl⟩ : syracuseStep 4854115 = 7281173) B7281173
theorem B1347953 : Blo 896573 1347953 := bstep (se 2 (by rfl) ⟨505482, by rfl⟩ : syracuseStep 1347953 = 1010965) B1010965
theorem B1347971 : Blo 896573 1347971 := bstep (se 1 (by rfl) ⟨1010978, by rfl⟩ : syracuseStep 1347971 = 2021957) B2021957
theorem B1348001 : Blo 896573 1348001 := bstep (se 2 (by rfl) ⟨505500, by rfl⟩ : syracuseStep 1348001 = 1011001) B1011001
theorem B1708465 : Blo 896573 1708465 := bstep (se 2 (by rfl) ⟨640674, by rfl⟩ : syracuseStep 1708465 = 1281349) B1281349
theorem B1348019 : Blo 896573 1348019 := bstep (se 1 (by rfl) ⟨1011014, by rfl⟩ : syracuseStep 1348019 = 2022029) B2022029
theorem B1348049 : Blo 896573 1348049 := bstep (se 2 (by rfl) ⟨505518, by rfl⟩ : syracuseStep 1348049 = 1011037) B1011037
theorem B1348067 : Blo 896573 1348067 := bstep (se 1 (by rfl) ⟨1011050, by rfl⟩ : syracuseStep 1348067 = 2022101) B2022101
theorem B1348097 : Blo 896573 1348097 := bstep (se 2 (by rfl) ⟨505536, by rfl⟩ : syracuseStep 1348097 = 1011073) B1011073
theorem B1348115 : Blo 896573 1348115 := bstep (se 1 (by rfl) ⟨1011086, by rfl⟩ : syracuseStep 1348115 = 2022173) B2022173
theorem B1348145 : Blo 896573 1348145 := bstep (se 2 (by rfl) ⟨505554, by rfl⟩ : syracuseStep 1348145 = 1011109) B1011109
theorem B1348163 : Blo 896573 1348163 := bstep (se 1 (by rfl) ⟨1011122, by rfl⟩ : syracuseStep 1348163 = 2022245) B2022245
theorem B1348193 : Blo 896573 1348193 := bstep (se 2 (by rfl) ⟨505572, by rfl⟩ : syracuseStep 1348193 = 1011145) B1011145
theorem B1348211 : Blo 896573 1348211 := bstep (se 1 (by rfl) ⟨1011158, by rfl⟩ : syracuseStep 1348211 = 2022317) B2022317
theorem B1348241 : Blo 896573 1348241 := bstep (se 2 (by rfl) ⟨505590, by rfl⟩ : syracuseStep 1348241 = 1011181) B1011181
theorem B1348259 : Blo 896573 1348259 := bstep (se 1 (by rfl) ⟨1011194, by rfl⟩ : syracuseStep 1348259 = 2022389) B2022389
theorem B3117731 : Blo 896573 3117731 := bstep (se 1 (by rfl) ⟨2338298, by rfl⟩ : syracuseStep 3117731 = 4676597) B4676597
theorem B1348289 : Blo 896573 1348289 := bstep (se 2 (by rfl) ⟨505608, by rfl⟩ : syracuseStep 1348289 = 1011217) B1011217
theorem B1348307 : Blo 896573 1348307 := bstep (se 1 (by rfl) ⟨1011230, by rfl⟩ : syracuseStep 1348307 = 2022461) B2022461
theorem B1348337 : Blo 896573 1348337 := bstep (se 2 (by rfl) ⟨505626, by rfl⟩ : syracuseStep 1348337 = 1011253) B1011253
theorem B1348355 : Blo 896573 1348355 := bstep (se 1 (by rfl) ⟨1011266, by rfl⟩ : syracuseStep 1348355 = 2022533) B2022533
theorem B1348385 : Blo 896573 1348385 := bstep (se 2 (by rfl) ⟨505644, by rfl⟩ : syracuseStep 1348385 = 1011289) B1011289
theorem B1348403 : Blo 896573 1348403 := bstep (se 1 (by rfl) ⟨1011302, by rfl⟩ : syracuseStep 1348403 = 2022605) B2022605
theorem B1708867 : Blo 896573 1708867 := bstep (se 1 (by rfl) ⟨1281650, by rfl⟩ : syracuseStep 1708867 = 2563301) B2563301
theorem B3412813 : Blo 896573 3412813 := bstep (se 3 (by rfl) ⟨639902, by rfl⟩ : syracuseStep 3412813 = 1279805) B1279805
theorem B1348433 : Blo 896573 1348433 := bstep (se 2 (by rfl) ⟨505662, by rfl⟩ : syracuseStep 1348433 = 1011325) B1011325
theorem B1348451 : Blo 896573 1348451 := bstep (se 1 (by rfl) ⟨1011338, by rfl⟩ : syracuseStep 1348451 = 2022677) B2022677
theorem B1708913 : Blo 896573 1708913 := bstep (se 2 (by rfl) ⟨640842, by rfl⟩ : syracuseStep 1708913 = 1281685) B1281685
theorem B1348481 : Blo 896573 1348481 := bstep (se 2 (by rfl) ⟨505680, by rfl⟩ : syracuseStep 1348481 = 1011361) B1011361
theorem B2560909 : Blo 896573 2560909 := bstep (se 3 (by rfl) ⟨480170, by rfl⟩ : syracuseStep 2560909 = 960341) B960341
theorem B1348499 : Blo 896573 1348499 := bstep (se 1 (by rfl) ⟨1011374, by rfl⟩ : syracuseStep 1348499 = 2022749) B2022749
theorem B1348529 : Blo 896573 1348529 := bstep (se 2 (by rfl) ⟨505698, by rfl⟩ : syracuseStep 1348529 = 1011397) B1011397
theorem B2429891 : Blo 896573 2429891 := bstep (se 1 (by rfl) ⟨1822418, by rfl⟩ : syracuseStep 2429891 = 3644837) B3644837
theorem B1348547 : Blo 896573 1348547 := bstep (se 1 (by rfl) ⟨1011410, by rfl⟩ : syracuseStep 1348547 = 2022821) B2022821
theorem B1348577 : Blo 896573 1348577 := bstep (se 2 (by rfl) ⟨505716, by rfl⟩ : syracuseStep 1348577 = 1011433) B1011433
theorem B1348595 : Blo 896573 1348595 := bstep (se 1 (by rfl) ⟨1011446, by rfl⟩ : syracuseStep 1348595 = 2022893) B2022893
theorem B1348625 : Blo 896573 1348625 := bstep (se 2 (by rfl) ⟨505734, by rfl⟩ : syracuseStep 1348625 = 1011469) B1011469
theorem B1348643 : Blo 896573 1348643 := bstep (se 1 (by rfl) ⟨1011482, by rfl⟩ : syracuseStep 1348643 = 2022965) B2022965
theorem B1348673 : Blo 896573 1348673 := bstep (se 2 (by rfl) ⟨505752, by rfl⟩ : syracuseStep 1348673 = 1011505) B1011505
theorem B1348691 : Blo 896573 1348691 := bstep (se 1 (by rfl) ⟨1011518, by rfl⟩ : syracuseStep 1348691 = 2023037) B2023037
theorem B3839075 : Blo 896573 3839075 := bstep (se 1 (by rfl) ⟨2879306, by rfl⟩ : syracuseStep 3839075 = 5758613) B5758613
theorem B1348721 : Blo 896573 1348721 := bstep (se 2 (by rfl) ⟨505770, by rfl⟩ : syracuseStep 1348721 = 1011541) B1011541
theorem B1348739 : Blo 896573 1348739 := bstep (se 1 (by rfl) ⟨1011554, by rfl⟩ : syracuseStep 1348739 = 2023109) B2023109
theorem B1709201 : Blo 896573 1709201 := bstep (se 2 (by rfl) ⟨640950, by rfl⟩ : syracuseStep 1709201 = 1281901) B1281901
theorem B1348769 : Blo 896573 1348769 := bstep (se 2 (by rfl) ⟨505788, by rfl⟩ : syracuseStep 1348769 = 1011577) B1011577
theorem B1348787 : Blo 896573 1348787 := bstep (se 1 (by rfl) ⟨1011590, by rfl⟩ : syracuseStep 1348787 = 2023181) B2023181
theorem B1348817 : Blo 896573 1348817 := bstep (se 2 (by rfl) ⟨505806, by rfl⟩ : syracuseStep 1348817 = 1011613) B1011613
theorem B1348835 : Blo 896573 1348835 := bstep (se 1 (by rfl) ⟨1011626, by rfl⟩ : syracuseStep 1348835 = 2023253) B2023253
theorem B1348865 : Blo 896573 1348865 := bstep (se 2 (by rfl) ⟨505824, by rfl⟩ : syracuseStep 1348865 = 1011649) B1011649
theorem B1348883 : Blo 896573 1348883 := bstep (se 1 (by rfl) ⟨1011662, by rfl⟩ : syracuseStep 1348883 = 2023325) B2023325
theorem B1348913 : Blo 896573 1348913 := bstep (se 2 (by rfl) ⟨505842, by rfl⟩ : syracuseStep 1348913 = 1011685) B1011685
theorem B1348931 : Blo 896573 1348931 := bstep (se 1 (by rfl) ⟨1011698, by rfl⟩ : syracuseStep 1348931 = 2023397) B2023397
theorem B1348961 : Blo 896573 1348961 := bstep (se 2 (by rfl) ⟨505860, by rfl⟩ : syracuseStep 1348961 = 1011721) B1011721
theorem B1348979 : Blo 896573 1348979 := bstep (se 1 (by rfl) ⟨1011734, by rfl⟩ : syracuseStep 1348979 = 2023469) B2023469
theorem B1349009 : Blo 896573 1349009 := bstep (se 2 (by rfl) ⟨505878, by rfl⟩ : syracuseStep 1349009 = 1011757) B1011757
theorem B1349027 : Blo 896573 1349027 := bstep (se 1 (by rfl) ⟨1011770, by rfl⟩ : syracuseStep 1349027 = 2023541) B2023541
theorem B1349057 : Blo 896573 1349057 := bstep (se 2 (by rfl) ⟨505896, by rfl⟩ : syracuseStep 1349057 = 1011793) B1011793
theorem B1349075 : Blo 896573 1349075 := bstep (se 1 (by rfl) ⟨1011806, by rfl⟩ : syracuseStep 1349075 = 2023613) B2023613
theorem B1349105 : Blo 896573 1349105 := bstep (se 2 (by rfl) ⟨505914, by rfl⟩ : syracuseStep 1349105 = 1011829) B1011829
theorem B1349123 : Blo 896573 1349123 := bstep (se 1 (by rfl) ⟨1011842, by rfl⟩ : syracuseStep 1349123 = 2023685) B2023685
theorem B1349153 : Blo 896573 1349153 := bstep (se 2 (by rfl) ⟨505932, by rfl⟩ : syracuseStep 1349153 = 1011865) B1011865
theorem B5117489 : Blo 896573 5117489 := bstep (se 2 (by rfl) ⟨1919058, by rfl⟩ : syracuseStep 5117489 = 3838117) B3838117
theorem B1349171 : Blo 896573 1349171 := bstep (se 1 (by rfl) ⟨1011878, by rfl⟩ : syracuseStep 1349171 = 2023757) B2023757
theorem B1349201 : Blo 896573 1349201 := bstep (se 2 (by rfl) ⟨505950, by rfl⟩ : syracuseStep 1349201 = 1011901) B1011901
theorem B3413603 : Blo 896573 3413603 := bstep (se 1 (by rfl) ⟨2560202, by rfl⟩ : syracuseStep 3413603 = 5120405) B5120405
theorem B1349219 : Blo 896573 1349219 := bstep (se 1 (by rfl) ⟨1011914, by rfl⟩ : syracuseStep 1349219 = 2023829) B2023829
theorem B1513073 : Blo 896573 1513073 := bstep (se 2 (by rfl) ⟨567402, by rfl⟩ : syracuseStep 1513073 = 1134805) B1134805
theorem B1349249 : Blo 896573 1349249 := bstep (se 2 (by rfl) ⟨505968, by rfl⟩ : syracuseStep 1349249 = 1011937) B1011937
theorem B1349267 : Blo 896573 1349267 := bstep (se 1 (by rfl) ⟨1011950, by rfl⟩ : syracuseStep 1349267 = 2023901) B2023901
theorem B1349297 : Blo 896573 1349297 := bstep (se 2 (by rfl) ⟨505986, by rfl⟩ : syracuseStep 1349297 = 1011973) B1011973
theorem B1349315 : Blo 896573 1349315 := bstep (se 1 (by rfl) ⟨1011986, by rfl⟩ : syracuseStep 1349315 = 2023973) B2023973
theorem B1349345 : Blo 896573 1349345 := bstep (se 2 (by rfl) ⟨506004, by rfl⟩ : syracuseStep 1349345 = 1012009) B1012009
theorem B26285795 : Blo 896573 26285795 := bstep (se 1 (by rfl) ⟨19714346, by rfl⟩ : syracuseStep 26285795 = 39428693) B39428693
theorem B1513201 : Blo 896573 1513201 := bstep (se 2 (by rfl) ⟨567450, by rfl⟩ : syracuseStep 1513201 = 1134901) B1134901
theorem B1349363 : Blo 896573 1349363 := bstep (se 1 (by rfl) ⟨1012022, by rfl⟩ : syracuseStep 1349363 = 2024045) B2024045
theorem B1349393 : Blo 896573 1349393 := bstep (se 2 (by rfl) ⟨506022, by rfl⟩ : syracuseStep 1349393 = 1012045) B1012045
theorem B1513235 : Blo 896573 1513235 := bstep (se 1 (by rfl) ⟨1134926, by rfl⟩ : syracuseStep 1513235 = 2269853) B2269853
theorem B1349411 : Blo 896573 1349411 := bstep (se 1 (by rfl) ⟨1012058, by rfl⟩ : syracuseStep 1349411 = 2024117) B2024117
theorem B1349441 : Blo 896573 1349441 := bstep (se 2 (by rfl) ⟨506040, by rfl⟩ : syracuseStep 1349441 = 1012081) B1012081
theorem B1349459 : Blo 896573 1349459 := bstep (se 1 (by rfl) ⟨1012094, by rfl⟩ : syracuseStep 1349459 = 2024189) B2024189
theorem B1349489 : Blo 896573 1349489 := bstep (se 2 (by rfl) ⟨506058, by rfl⟩ : syracuseStep 1349489 = 1012117) B1012117
theorem B1349507 : Blo 896573 1349507 := bstep (se 1 (by rfl) ⟨1012130, by rfl⟩ : syracuseStep 1349507 = 2024261) B2024261
theorem B1513363 : Blo 896573 1513363 := bstep (se 1 (by rfl) ⟨1135022, by rfl⟩ : syracuseStep 1513363 = 2270045) B2270045
theorem B1349537 : Blo 896573 1349537 := bstep (se 2 (by rfl) ⟨506076, by rfl⟩ : syracuseStep 1349537 = 1012153) B1012153
theorem B2561969 : Blo 896573 2561969 := bstep (se 2 (by rfl) ⟨960738, by rfl⟩ : syracuseStep 2561969 = 1921477) B1921477
theorem B1349555 : Blo 896573 1349555 := bstep (se 1 (by rfl) ⟨1012166, by rfl⟩ : syracuseStep 1349555 = 2024333) B2024333
theorem B1349585 : Blo 896573 1349585 := bstep (se 2 (by rfl) ⟨506094, by rfl⟩ : syracuseStep 1349585 = 1012189) B1012189
theorem B1349603 : Blo 896573 1349603 := bstep (se 1 (by rfl) ⟨1012202, by rfl⟩ : syracuseStep 1349603 = 2024405) B2024405
theorem B1349633 : Blo 896573 1349633 := bstep (se 2 (by rfl) ⟨506112, by rfl⟩ : syracuseStep 1349633 = 1012225) B1012225
theorem B1349651 : Blo 896573 1349651 := bstep (se 1 (by rfl) ⟨1012238, by rfl⟩ : syracuseStep 1349651 = 2024477) B2024477
theorem B1513505 : Blo 896573 1513505 := bstep (se 2 (by rfl) ⟨567564, by rfl⟩ : syracuseStep 1513505 = 1135129) B1135129
theorem B1349681 : Blo 896573 1349681 := bstep (se 2 (by rfl) ⟨506130, by rfl⟩ : syracuseStep 1349681 = 1012261) B1012261
theorem B1349699 : Blo 896573 1349699 := bstep (se 1 (by rfl) ⟨1012274, by rfl⟩ : syracuseStep 1349699 = 2024549) B2024549
theorem B1349729 : Blo 896573 1349729 := bstep (se 2 (by rfl) ⟨506148, by rfl⟩ : syracuseStep 1349729 = 1012297) B1012297
theorem B1349747 : Blo 896573 1349747 := bstep (se 1 (by rfl) ⟨1012310, by rfl⟩ : syracuseStep 1349747 = 2024621) B2024621
theorem B1349777 : Blo 896573 1349777 := bstep (se 2 (by rfl) ⟨506166, by rfl⟩ : syracuseStep 1349777 = 1012333) B1012333
theorem B1513633 : Blo 896573 1513633 := bstep (se 2 (by rfl) ⟨567612, by rfl⟩ : syracuseStep 1513633 = 1135225) B1135225
theorem B1349795 : Blo 896573 1349795 := bstep (se 1 (by rfl) ⟨1012346, by rfl⟩ : syracuseStep 1349795 = 2024693) B2024693
theorem B1349825 : Blo 896573 1349825 := bstep (se 2 (by rfl) ⟨506184, by rfl⟩ : syracuseStep 1349825 = 1012369) B1012369
theorem B1513667 : Blo 896573 1513667 := bstep (se 1 (by rfl) ⟨1135250, by rfl⟩ : syracuseStep 1513667 = 2270501) B2270501
theorem B1153219 : Blo 896573 1153219 := bstep (se 1 (by rfl) ⟨864914, by rfl⟩ : syracuseStep 1153219 = 1729829) B1729829
theorem B1349843 : Blo 896573 1349843 := bstep (se 1 (by rfl) ⟨1012382, by rfl⟩ : syracuseStep 1349843 = 2024765) B2024765
theorem B3414257 : Blo 896573 3414257 := bstep (se 2 (by rfl) ⟨1280346, by rfl⟩ : syracuseStep 3414257 = 2560693) B2560693
theorem B1349873 : Blo 896573 1349873 := bstep (se 2 (by rfl) ⟨506202, by rfl⟩ : syracuseStep 1349873 = 1012405) B1012405
theorem B1349891 : Blo 896573 1349891 := bstep (se 1 (by rfl) ⟨1012418, by rfl⟩ : syracuseStep 1349891 = 2024837) B2024837
theorem B1349921 : Blo 896573 1349921 := bstep (se 2 (by rfl) ⟨506220, by rfl⟩ : syracuseStep 1349921 = 1012441) B1012441
theorem B1349939 : Blo 896573 1349939 := bstep (se 1 (by rfl) ⟨1012454, by rfl⟩ : syracuseStep 1349939 = 2024909) B2024909
theorem B1513795 : Blo 896573 1513795 := bstep (se 1 (by rfl) ⟨1135346, by rfl⟩ : syracuseStep 1513795 = 2270693) B2270693
theorem B1349969 : Blo 896573 1349969 := bstep (se 2 (by rfl) ⟨506238, by rfl⟩ : syracuseStep 1349969 = 1012477) B1012477
theorem B1349987 : Blo 896573 1349987 := bstep (se 1 (by rfl) ⟨1012490, by rfl⟩ : syracuseStep 1349987 = 2024981) B2024981
theorem B1350017 : Blo 896573 1350017 := bstep (se 2 (by rfl) ⟨506256, by rfl⟩ : syracuseStep 1350017 = 1012513) B1012513
theorem B1350035 : Blo 896573 1350035 := bstep (se 1 (by rfl) ⟨1012526, by rfl⟩ : syracuseStep 1350035 = 2025053) B2025053
theorem B1350065 : Blo 896573 1350065 := bstep (se 2 (by rfl) ⟨506274, by rfl⟩ : syracuseStep 1350065 = 1012549) B1012549
theorem B1350083 : Blo 896573 1350083 := bstep (se 1 (by rfl) ⟨1012562, by rfl⟩ : syracuseStep 1350083 = 2025125) B2025125
theorem B1513937 : Blo 896573 1513937 := bstep (se 2 (by rfl) ⟨567726, by rfl⟩ : syracuseStep 1513937 = 1135453) B1135453
theorem B1350113 : Blo 896573 1350113 := bstep (se 2 (by rfl) ⟨506292, by rfl⟩ : syracuseStep 1350113 = 1012585) B1012585
theorem B1350131 : Blo 896573 1350131 := bstep (se 1 (by rfl) ⟨1012598, by rfl⟩ : syracuseStep 1350131 = 2025197) B2025197
theorem B1350161 : Blo 896573 1350161 := bstep (se 2 (by rfl) ⟨506310, by rfl⟩ : syracuseStep 1350161 = 1012621) B1012621
theorem B1350179 : Blo 896573 1350179 := bstep (se 1 (by rfl) ⟨1012634, by rfl⟩ : syracuseStep 1350179 = 2025269) B2025269
theorem B1350209 : Blo 896573 1350209 := bstep (se 2 (by rfl) ⟨506328, by rfl⟩ : syracuseStep 1350209 = 1012657) B1012657
theorem B1514065 : Blo 896573 1514065 := bstep (se 2 (by rfl) ⟨567774, by rfl⟩ : syracuseStep 1514065 = 1135549) B1135549
theorem B2562641 : Blo 896573 2562641 := bstep (se 2 (by rfl) ⟨960990, by rfl⟩ : syracuseStep 2562641 = 1921981) B1921981
theorem B1350227 : Blo 896573 1350227 := bstep (se 1 (by rfl) ⟨1012670, by rfl⟩ : syracuseStep 1350227 = 2025341) B2025341
theorem B1350257 : Blo 896573 1350257 := bstep (se 2 (by rfl) ⟨506346, by rfl⟩ : syracuseStep 1350257 = 1012693) B1012693
theorem B1514099 : Blo 896573 1514099 := bstep (se 1 (by rfl) ⟨1135574, by rfl⟩ : syracuseStep 1514099 = 2271149) B2271149
theorem B1350275 : Blo 896573 1350275 := bstep (se 1 (by rfl) ⟨1012706, by rfl⟩ : syracuseStep 1350275 = 2025413) B2025413
theorem B1022611 : Blo 896573 1022611 := bstep (se 1 (by rfl) ⟨766958, by rfl⟩ : syracuseStep 1022611 = 1533917) B1533917
theorem B1350305 : Blo 896573 1350305 := bstep (se 2 (by rfl) ⟨506364, by rfl⟩ : syracuseStep 1350305 = 1012729) B1012729
theorem B1350323 : Blo 896573 1350323 := bstep (se 1 (by rfl) ⟨1012742, by rfl⟩ : syracuseStep 1350323 = 2025485) B2025485
theorem B1350353 : Blo 896573 1350353 := bstep (se 2 (by rfl) ⟨506382, by rfl⟩ : syracuseStep 1350353 = 1012765) B1012765
theorem B1350371 : Blo 896573 1350371 := bstep (se 1 (by rfl) ⟨1012778, by rfl⟩ : syracuseStep 1350371 = 2025557) B2025557
theorem B1514227 : Blo 896573 1514227 := bstep (se 1 (by rfl) ⟨1135670, by rfl⟩ : syracuseStep 1514227 = 2271341) B2271341
theorem B1350401 : Blo 896573 1350401 := bstep (se 2 (by rfl) ⟨506400, by rfl⟩ : syracuseStep 1350401 = 1012801) B1012801
theorem B5184269 : Blo 896573 5184269 := bstep (se 3 (by rfl) ⟨972050, by rfl⟩ : syracuseStep 5184269 = 1944101) B1944101
theorem B1350419 : Blo 896573 1350419 := bstep (se 1 (by rfl) ⟨1012814, by rfl⟩ : syracuseStep 1350419 = 2025629) B2025629
theorem B3840817 : Blo 896573 3840817 := bstep (se 2 (by rfl) ⟨1440306, by rfl⟩ : syracuseStep 3840817 = 2880613) B2880613
theorem B1350449 : Blo 896573 1350449 := bstep (se 2 (by rfl) ⟨506418, by rfl⟩ : syracuseStep 1350449 = 1012837) B1012837
theorem B1350467 : Blo 896573 1350467 := bstep (se 1 (by rfl) ⟨1012850, by rfl⟩ : syracuseStep 1350467 = 2025701) B2025701
theorem B1350497 : Blo 896573 1350497 := bstep (se 2 (by rfl) ⟨506436, by rfl⟩ : syracuseStep 1350497 = 1012873) B1012873
theorem B1350515 : Blo 896573 1350515 := bstep (se 1 (by rfl) ⟨1012886, by rfl⟩ : syracuseStep 1350515 = 2025773) B2025773
theorem B1514369 : Blo 896573 1514369 := bstep (se 2 (by rfl) ⟨567888, by rfl⟩ : syracuseStep 1514369 = 1135777) B1135777
theorem B1350545 : Blo 896573 1350545 := bstep (se 2 (by rfl) ⟨506454, by rfl⟩ : syracuseStep 1350545 = 1012909) B1012909
theorem B1350563 : Blo 896573 1350563 := bstep (se 1 (by rfl) ⟨1012922, by rfl⟩ : syracuseStep 1350563 = 2025845) B2025845
theorem B1350593 : Blo 896573 1350593 := bstep (se 2 (by rfl) ⟨506472, by rfl⟩ : syracuseStep 1350593 = 1012945) B1012945
theorem B1350611 : Blo 896573 1350611 := bstep (se 1 (by rfl) ⟨1012958, by rfl⟩ : syracuseStep 1350611 = 2025917) B2025917
theorem B5118947 : Blo 896573 5118947 := bstep (se 1 (by rfl) ⟨3839210, by rfl⟩ : syracuseStep 5118947 = 7678421) B7678421
theorem B1350641 : Blo 896573 1350641 := bstep (se 2 (by rfl) ⟨506490, by rfl⟩ : syracuseStep 1350641 = 1012981) B1012981
theorem B1514497 : Blo 896573 1514497 := bstep (se 2 (by rfl) ⟨567936, by rfl⟩ : syracuseStep 1514497 = 1135873) B1135873
theorem B1350659 : Blo 896573 1350659 := bstep (se 1 (by rfl) ⟨1012994, by rfl⟩ : syracuseStep 1350659 = 2025989) B2025989
theorem B1350689 : Blo 896573 1350689 := bstep (se 2 (by rfl) ⟨506508, by rfl⟩ : syracuseStep 1350689 = 1013017) B1013017
theorem B1514531 : Blo 896573 1514531 := bstep (se 1 (by rfl) ⟨1135898, by rfl⟩ : syracuseStep 1514531 = 2271797) B2271797
theorem B1350707 : Blo 896573 1350707 := bstep (se 1 (by rfl) ⟨1013030, by rfl⟩ : syracuseStep 1350707 = 2026061) B2026061
theorem B1350737 : Blo 896573 1350737 := bstep (se 2 (by rfl) ⟨506526, by rfl⟩ : syracuseStep 1350737 = 1013053) B1013053
theorem B957539 : Blo 896573 957539 := bstep (se 1 (by rfl) ⟨718154, by rfl⟩ : syracuseStep 957539 = 1436309) B1436309
theorem B1350755 : Blo 896573 1350755 := bstep (se 1 (by rfl) ⟨1013066, by rfl⟩ : syracuseStep 1350755 = 2026133) B2026133
theorem B1350785 : Blo 896573 1350785 := bstep (se 2 (by rfl) ⟨506544, by rfl⟩ : syracuseStep 1350785 = 1013089) B1013089
theorem B1350803 : Blo 896573 1350803 := bstep (se 1 (by rfl) ⟨1013102, by rfl⟩ : syracuseStep 1350803 = 2026205) B2026205
theorem B1514659 : Blo 896573 1514659 := bstep (se 1 (by rfl) ⟨1135994, by rfl⟩ : syracuseStep 1514659 = 2271989) B2271989
theorem B1350833 : Blo 896573 1350833 := bstep (se 2 (by rfl) ⟨506562, by rfl⟩ : syracuseStep 1350833 = 1013125) B1013125
theorem B1350851 : Blo 896573 1350851 := bstep (se 1 (by rfl) ⟨1013138, by rfl⟩ : syracuseStep 1350851 = 2026277) B2026277
theorem B957667 : Blo 896573 957667 := bstep (se 1 (by rfl) ⟨718250, by rfl⟩ : syracuseStep 957667 = 1436501) B1436501
theorem B2432269 : Blo 896573 2432269 := bstep (se 3 (by rfl) ⟨456050, by rfl⟩ : syracuseStep 2432269 = 912101) B912101
theorem B1514801 : Blo 896573 1514801 := bstep (se 2 (by rfl) ⟨568050, by rfl⟩ : syracuseStep 1514801 = 1136101) B1136101
theorem B2563427 : Blo 896573 2563427 := bstep (se 1 (by rfl) ⟨1922570, by rfl⟩ : syracuseStep 2563427 = 3845141) B3845141
theorem B10919281 : Blo 896573 10919281 := bstep (se 2 (by rfl) ⟨4094730, by rfl⟩ : syracuseStep 10919281 = 8189461) B8189461
theorem B1514929 : Blo 896573 1514929 := bstep (se 2 (by rfl) ⟨568098, by rfl⟩ : syracuseStep 1514929 = 1136197) B1136197
theorem B1514963 : Blo 896573 1514963 := bstep (se 1 (by rfl) ⟨1136222, by rfl⟩ : syracuseStep 1514963 = 2272445) B2272445
theorem B1515091 : Blo 896573 1515091 := bstep (se 1 (by rfl) ⟨1136318, by rfl⟩ : syracuseStep 1515091 = 2272637) B2272637
theorem B2727523 : Blo 896573 2727523 := bstep (se 1 (by rfl) ⟨2045642, by rfl⟩ : syracuseStep 2727523 = 4091285) B4091285
theorem B2301571 : Blo 896573 2301571 := bstep (se 1 (by rfl) ⟨1726178, by rfl⟩ : syracuseStep 2301571 = 3452357) B3452357
theorem B3415715 : Blo 896573 3415715 := bstep (se 1 (by rfl) ⟨2561786, by rfl⟩ : syracuseStep 3415715 = 5123573) B5123573
theorem B2563757 : Blo 896573 2563757 := bstep (se 3 (by rfl) ⟨480704, by rfl⟩ : syracuseStep 2563757 = 961409) B961409
theorem B3415729 : Blo 896573 3415729 := bstep (se 2 (by rfl) ⟨1280898, by rfl⟩ : syracuseStep 3415729 = 2561797) B2561797
theorem B1515233 : Blo 896573 1515233 := bstep (se 2 (by rfl) ⟨568212, by rfl⟩ : syracuseStep 1515233 = 1136425) B1136425
theorem B7282403 : Blo 896573 7282403 := bstep (se 1 (by rfl) ⟨5461802, by rfl⟩ : syracuseStep 7282403 = 10923605) B10923605
theorem B2563825 : Blo 896573 2563825 := bstep (se 2 (by rfl) ⟨961434, by rfl⟩ : syracuseStep 2563825 = 1922869) B1922869
theorem B1515361 : Blo 896573 1515361 := bstep (se 2 (by rfl) ⟨568260, by rfl⟩ : syracuseStep 1515361 = 1136521) B1136521
theorem B1515395 : Blo 896573 1515395 := bstep (se 1 (by rfl) ⟨1136546, by rfl⟩ : syracuseStep 1515395 = 2273093) B2273093
theorem B4431779 : Blo 896573 4431779 := bstep (se 1 (by rfl) ⟨3323834, by rfl⟩ : syracuseStep 4431779 = 6647669) B6647669
theorem B5119949 : Blo 896573 5119949 := bstep (se 3 (by rfl) ⟨959990, by rfl⟩ : syracuseStep 5119949 = 1919981) B1919981
theorem B1515523 : Blo 896573 1515523 := bstep (se 1 (by rfl) ⟨1136642, by rfl⟩ : syracuseStep 1515523 = 2273285) B2273285
theorem B2564099 : Blo 896573 2564099 := bstep (se 1 (by rfl) ⟨1923074, by rfl⟩ : syracuseStep 2564099 = 3846149) B3846149
theorem B958483 : Blo 896573 958483 := bstep (se 1 (by rfl) ⟨718862, by rfl⟩ : syracuseStep 958483 = 1437725) B1437725
theorem B2433091 : Blo 896573 2433091 := bstep (se 1 (by rfl) ⟨1824818, by rfl⟩ : syracuseStep 2433091 = 3649637) B3649637
theorem B1515665 : Blo 896573 1515665 := bstep (se 2 (by rfl) ⟨568374, by rfl⟩ : syracuseStep 1515665 = 1136749) B1136749
theorem B1515793 : Blo 896573 1515793 := bstep (se 2 (by rfl) ⟨568422, by rfl⟩ : syracuseStep 1515793 = 1136845) B1136845
theorem B1515827 : Blo 896573 1515827 := bstep (se 1 (by rfl) ⟨1136870, by rfl⟩ : syracuseStep 1515827 = 2273741) B2273741
theorem B1515955 : Blo 896573 1515955 := bstep (se 1 (by rfl) ⟨1136966, by rfl⟩ : syracuseStep 1515955 = 2273933) B2273933
theorem B1516097 : Blo 896573 1516097 := bstep (se 2 (by rfl) ⟨568536, by rfl⟩ : syracuseStep 1516097 = 1137073) B1137073
theorem B6136483 : Blo 896573 6136483 := bstep (se 1 (by rfl) ⟨4602362, by rfl⟩ : syracuseStep 6136483 = 9204725) B9204725
theorem B1516225 : Blo 896573 1516225 := bstep (se 2 (by rfl) ⟨568584, by rfl⟩ : syracuseStep 1516225 = 1137169) B1137169
theorem B3842765 : Blo 896573 3842765 := bstep (se 3 (by rfl) ⟨720518, by rfl⟩ : syracuseStep 3842765 = 1441037) B1441037
theorem B1516259 : Blo 896573 1516259 := bstep (se 1 (by rfl) ⟨1137194, by rfl⟩ : syracuseStep 1516259 = 2274389) B2274389
theorem B2433773 : Blo 896573 2433773 := bstep (se 3 (by rfl) ⟨456332, by rfl⟩ : syracuseStep 2433773 = 912665) B912665
theorem B2433827 : Blo 896573 2433827 := bstep (se 1 (by rfl) ⟨1825370, by rfl⟩ : syracuseStep 2433827 = 3650741) B3650741
theorem B1516387 : Blo 896573 1516387 := bstep (se 1 (by rfl) ⟨1137290, by rfl⟩ : syracuseStep 1516387 = 2274581) B2274581
theorem B2270065 : Blo 896573 2270065 := bstep (se 2 (by rfl) ⟨851274, by rfl⟩ : syracuseStep 2270065 = 1702549) B1702549
theorem B1516529 : Blo 896573 1516529 := bstep (se 2 (by rfl) ⟨568698, by rfl⟩ : syracuseStep 1516529 = 1137397) B1137397
theorem B3417187 : Blo 896573 3417187 := bstep (se 1 (by rfl) ⟨2562890, by rfl⟩ : syracuseStep 3417187 = 5125781) B5125781
theorem B1516657 : Blo 896573 1516657 := bstep (se 2 (by rfl) ⟨568746, by rfl⟩ : syracuseStep 1516657 = 1137493) B1137493
theorem B2270339 : Blo 896573 2270339 := bstep (se 1 (by rfl) ⟨1702754, by rfl⟩ : syracuseStep 2270339 = 3405509) B3405509
theorem B1516691 : Blo 896573 1516691 := bstep (se 1 (by rfl) ⟨1137518, by rfl⟩ : syracuseStep 1516691 = 2275037) B2275037
theorem B1516819 : Blo 896573 1516819 := bstep (se 1 (by rfl) ⟨1137614, by rfl⟩ : syracuseStep 1516819 = 2275229) B2275229
theorem B2270531 : Blo 896573 2270531 := bstep (se 1 (by rfl) ⟨1702898, by rfl⟩ : syracuseStep 2270531 = 3405797) B3405797
theorem B2729297 : Blo 896573 2729297 := bstep (se 2 (by rfl) ⟨1023486, by rfl⟩ : syracuseStep 2729297 = 2046973) B2046973
theorem B1516961 : Blo 896573 1516961 := bstep (se 2 (by rfl) ⟨568860, by rfl⟩ : syracuseStep 1516961 = 1137721) B1137721
theorem B1517089 : Blo 896573 1517089 := bstep (se 2 (by rfl) ⟨568908, by rfl⟩ : syracuseStep 1517089 = 1137817) B1137817
theorem B1517123 : Blo 896573 1517123 := bstep (se 1 (by rfl) ⟨1137842, by rfl⟩ : syracuseStep 1517123 = 2275685) B2275685
theorem B6006413 : Blo 896573 6006413 := bstep (se 3 (by rfl) ⟨1126202, by rfl⟩ : syracuseStep 6006413 = 2252405) B2252405
theorem B1517251 : Blo 896573 1517251 := bstep (se 1 (by rfl) ⟨1137938, by rfl⟩ : syracuseStep 1517251 = 2275877) B2275877
theorem B2074339 : Blo 896573 2074339 := bstep (se 1 (by rfl) ⟨1555754, by rfl⟩ : syracuseStep 2074339 = 3111509) B3111509
theorem B1976035 : Blo 896573 1976035 := bstep (se 1 (by rfl) ⟨1482026, by rfl⟩ : syracuseStep 1976035 = 2964053) B2964053
theorem B2303729 : Blo 896573 2303729 := bstep (se 2 (by rfl) ⟨863898, by rfl⟩ : syracuseStep 2303729 = 1727797) B1727797
theorem B1517393 : Blo 896573 1517393 := bstep (se 2 (by rfl) ⟨569022, by rfl⟩ : syracuseStep 1517393 = 1138045) B1138045
theorem B1615747 : Blo 896573 1615747 := bstep (se 1 (by rfl) ⟨1211810, by rfl⟩ : syracuseStep 1615747 = 2423621) B2423621
theorem B6825869 : Blo 896573 6825869 := bstep (se 3 (by rfl) ⟨1279850, by rfl⟩ : syracuseStep 6825869 = 2559701) B2559701
theorem B1517521 : Blo 896573 1517521 := bstep (se 2 (by rfl) ⟨569070, by rfl⟩ : syracuseStep 1517521 = 1138141) B1138141
theorem B1517555 : Blo 896573 1517555 := bstep (se 1 (by rfl) ⟨1138166, by rfl⟩ : syracuseStep 1517555 = 2276333) B2276333
theorem B1517683 : Blo 896573 1517683 := bstep (se 1 (by rfl) ⟨1138262, by rfl⟩ : syracuseStep 1517683 = 2276525) B2276525
theorem B2271473 : Blo 896573 2271473 := bstep (se 2 (by rfl) ⟨851802, by rfl⟩ : syracuseStep 2271473 = 1703605) B1703605
theorem B1517825 : Blo 896573 1517825 := bstep (se 2 (by rfl) ⟨569184, by rfl⟩ : syracuseStep 1517825 = 1138369) B1138369
theorem B2271523 : Blo 896573 2271523 := bstep (se 1 (by rfl) ⟨1703642, by rfl⟩ : syracuseStep 2271523 = 3407285) B3407285
theorem B2959715 : Blo 896573 2959715 := bstep (se 1 (by rfl) ⟨2219786, by rfl⟩ : syracuseStep 2959715 = 4439573) B4439573
theorem B1517953 : Blo 896573 1517953 := bstep (se 2 (by rfl) ⟨569232, by rfl⟩ : syracuseStep 1517953 = 1138465) B1138465
theorem B1517987 : Blo 896573 1517987 := bstep (se 1 (by rfl) ⟨1138490, by rfl⟩ : syracuseStep 1517987 = 2276981) B2276981
theorem B2271665 : Blo 896573 2271665 := bstep (se 2 (by rfl) ⟨851874, by rfl⟩ : syracuseStep 2271665 = 1703749) B1703749
theorem B1518115 : Blo 896573 1518115 := bstep (se 1 (by rfl) ⟨1138586, by rfl⟩ : syracuseStep 1518115 = 2277173) B2277173
theorem B1026643 : Blo 896573 1026643 := bstep (se 1 (by rfl) ⟨769982, by rfl⟩ : syracuseStep 1026643 = 1539965) B1539965
theorem B1518257 : Blo 896573 1518257 := bstep (se 2 (by rfl) ⟨569346, by rfl⟩ : syracuseStep 1518257 = 1138693) B1138693
theorem B5122865 : Blo 896573 5122865 := bstep (se 2 (by rfl) ⟨1921074, by rfl⟩ : syracuseStep 5122865 = 3842149) B3842149
theorem B1518385 : Blo 896573 1518385 := bstep (se 2 (by rfl) ⟨569394, by rfl⟩ : syracuseStep 1518385 = 1138789) B1138789
theorem B1518419 : Blo 896573 1518419 := bstep (se 1 (by rfl) ⟨1138814, by rfl⟩ : syracuseStep 1518419 = 2277629) B2277629
theorem B4926307 : Blo 896573 4926307 := bstep (se 1 (by rfl) ⟨3694730, by rfl⟩ : syracuseStep 4926307 = 7389461) B7389461
theorem B1944515 : Blo 896573 1944515 := bstep (se 1 (by rfl) ⟨1458386, by rfl⟩ : syracuseStep 1944515 = 2916773) B2916773
theorem B1518547 : Blo 896573 1518547 := bstep (se 1 (by rfl) ⟨1138910, by rfl⟩ : syracuseStep 1518547 = 2277821) B2277821
theorem B2730989 : Blo 896573 2730989 := bstep (se 3 (by rfl) ⟨512060, by rfl⟩ : syracuseStep 2730989 = 1024121) B1024121
theorem B3025997 : Blo 896573 3025997 := bstep (se 3 (by rfl) ⟨567374, by rfl⟩ : syracuseStep 3025997 = 1134749) B1134749
theorem B1518689 : Blo 896573 1518689 := bstep (se 2 (by rfl) ⟨569508, by rfl⟩ : syracuseStep 1518689 = 1139017) B1139017
theorem B3026051 : Blo 896573 3026051 := bstep (se 1 (by rfl) ⟨2269538, by rfl⟩ : syracuseStep 3026051 = 4539077) B4539077
theorem B1617059 : Blo 896573 1617059 := bstep (se 1 (by rfl) ⟨1212794, by rfl⟩ : syracuseStep 1617059 = 2425589) B2425589
theorem B1944785 : Blo 896573 1944785 := bstep (se 2 (by rfl) ⟨729294, by rfl⟩ : syracuseStep 1944785 = 1458589) B1458589
theorem B1518817 : Blo 896573 1518817 := bstep (se 2 (by rfl) ⟨569556, by rfl⟩ : syracuseStep 1518817 = 1139113) B1139113
theorem B1518851 : Blo 896573 1518851 := bstep (se 1 (by rfl) ⟨1139138, by rfl⟩ : syracuseStep 1518851 = 2278277) B2278277
theorem B1518979 : Blo 896573 1518979 := bstep (se 1 (by rfl) ⟨1139234, by rfl⟩ : syracuseStep 1518979 = 2278469) B2278469
theorem B3026321 : Blo 896573 3026321 := bstep (se 2 (by rfl) ⟨1134870, by rfl⟩ : syracuseStep 3026321 = 2269741) B2269741
theorem B2272657 : Blo 896573 2272657 := bstep (se 2 (by rfl) ⟨852246, by rfl⟩ : syracuseStep 2272657 = 1704493) B1704493
theorem B1617347 : Blo 896573 1617347 := bstep (se 1 (by rfl) ⟨1213010, by rfl⟩ : syracuseStep 1617347 = 2426021) B2426021
theorem B1519121 : Blo 896573 1519121 := bstep (se 2 (by rfl) ⟨569670, by rfl⟩ : syracuseStep 1519121 = 1139341) B1139341
theorem B896579 : Blo 896573 896579 := bstep (se 1 (by rfl) ⟨672434, by rfl⟩ : syracuseStep 896579 = 1344869) B1344869
theorem B896595 : Blo 896573 896595 := bstep (se 1 (by rfl) ⟨672446, by rfl⟩ : syracuseStep 896595 = 1344893) B1344893
theorem B896611 : Blo 896573 896611 := bstep (se 1 (by rfl) ⟨672458, by rfl⟩ : syracuseStep 896611 = 1344917) B1344917
theorem B896627 : Blo 896573 896627 := bstep (se 1 (by rfl) ⟨672470, by rfl⟩ : syracuseStep 896627 = 1344941) B1344941
theorem B896643 : Blo 896573 896643 := bstep (se 1 (by rfl) ⟨672482, by rfl⟩ : syracuseStep 896643 = 1344965) B1344965
theorem B1519249 : Blo 896573 1519249 := bstep (se 2 (by rfl) ⟨569718, by rfl⟩ : syracuseStep 1519249 = 1139437) B1139437
theorem B896659 : Blo 896573 896659 := bstep (se 1 (by rfl) ⟨672494, by rfl⟩ : syracuseStep 896659 = 1344989) B1344989
theorem B896675 : Blo 896573 896675 := bstep (se 1 (by rfl) ⟨672506, by rfl⟩ : syracuseStep 896675 = 1345013) B1345013
theorem B2272931 : Blo 896573 2272931 := bstep (se 1 (by rfl) ⟨1704698, by rfl⟩ : syracuseStep 2272931 = 3409397) B3409397
theorem B896691 : Blo 896573 896691 := bstep (se 1 (by rfl) ⟨672518, by rfl⟩ : syracuseStep 896691 = 1345037) B1345037
theorem B1519283 : Blo 896573 1519283 := bstep (se 1 (by rfl) ⟨1139462, by rfl⟩ : syracuseStep 1519283 = 2278925) B2278925
theorem B896707 : Blo 896573 896707 := bstep (se 1 (by rfl) ⟨672530, by rfl⟩ : syracuseStep 896707 = 1345061) B1345061
theorem B896723 : Blo 896573 896723 := bstep (se 1 (by rfl) ⟨672542, by rfl⟩ : syracuseStep 896723 = 1345085) B1345085
theorem B896739 : Blo 896573 896739 := bstep (se 1 (by rfl) ⟨672554, by rfl⟩ : syracuseStep 896739 = 1345109) B1345109
theorem B896755 : Blo 896573 896755 := bstep (se 1 (by rfl) ⟨672566, by rfl⟩ : syracuseStep 896755 = 1345133) B1345133
theorem B896771 : Blo 896573 896771 := bstep (se 1 (by rfl) ⟨672578, by rfl⟩ : syracuseStep 896771 = 1345157) B1345157
theorem B896787 : Blo 896573 896787 := bstep (se 1 (by rfl) ⟨672590, by rfl⟩ : syracuseStep 896787 = 1345181) B1345181
theorem B896803 : Blo 896573 896803 := bstep (se 1 (by rfl) ⟨672602, by rfl⟩ : syracuseStep 896803 = 1345205) B1345205
theorem B896819 : Blo 896573 896819 := bstep (se 1 (by rfl) ⟨672614, by rfl⟩ : syracuseStep 896819 = 1345229) B1345229
theorem B1519411 : Blo 896573 1519411 := bstep (se 1 (by rfl) ⟨1139558, by rfl⟩ : syracuseStep 1519411 = 2279117) B2279117
theorem B896835 : Blo 896573 896835 := bstep (se 1 (by rfl) ⟨672626, by rfl⟩ : syracuseStep 896835 = 1345253) B1345253
theorem B896851 : Blo 896573 896851 := bstep (se 1 (by rfl) ⟨672638, by rfl⟩ : syracuseStep 896851 = 1345277) B1345277
theorem B896867 : Blo 896573 896867 := bstep (se 1 (by rfl) ⟨672650, by rfl⟩ : syracuseStep 896867 = 1345301) B1345301
theorem B2273123 : Blo 896573 2273123 := bstep (se 1 (by rfl) ⟨1704842, by rfl⟩ : syracuseStep 2273123 = 3409685) B3409685
theorem B896883 : Blo 896573 896883 := bstep (se 1 (by rfl) ⟨672662, by rfl⟩ : syracuseStep 896883 = 1345325) B1345325
theorem B896899 : Blo 896573 896899 := bstep (se 1 (by rfl) ⟨672674, by rfl⟩ : syracuseStep 896899 = 1345349) B1345349
theorem B896915 : Blo 896573 896915 := bstep (se 1 (by rfl) ⟨672686, by rfl⟩ : syracuseStep 896915 = 1345373) B1345373
theorem B896931 : Blo 896573 896931 := bstep (se 1 (by rfl) ⟨672698, by rfl⟩ : syracuseStep 896931 = 1345397) B1345397
theorem B3026861 : Blo 896573 3026861 := bstep (se 3 (by rfl) ⟨567536, by rfl⟩ : syracuseStep 3026861 = 1135073) B1135073
theorem B896947 : Blo 896573 896947 := bstep (se 1 (by rfl) ⟨672710, by rfl⟩ : syracuseStep 896947 = 1345421) B1345421
theorem B1519553 : Blo 896573 1519553 := bstep (se 2 (by rfl) ⟨569832, by rfl⟩ : syracuseStep 1519553 = 1139665) B1139665
theorem B896963 : Blo 896573 896963 := bstep (se 1 (by rfl) ⟨672722, by rfl⟩ : syracuseStep 896963 = 1345445) B1345445
theorem B896979 : Blo 896573 896979 := bstep (se 1 (by rfl) ⟨672734, by rfl⟩ : syracuseStep 896979 = 1345469) B1345469
theorem B3026915 : Blo 896573 3026915 := bstep (se 1 (by rfl) ⟨2270186, by rfl⟩ : syracuseStep 3026915 = 4540373) B4540373
theorem B896995 : Blo 896573 896995 := bstep (se 1 (by rfl) ⟨672746, by rfl⟩ : syracuseStep 896995 = 1345493) B1345493
theorem B897011 : Blo 896573 897011 := bstep (se 1 (by rfl) ⟨672758, by rfl⟩ : syracuseStep 897011 = 1345517) B1345517
theorem B897027 : Blo 896573 897027 := bstep (se 1 (by rfl) ⟨672770, by rfl⟩ : syracuseStep 897027 = 1345541) B1345541
theorem B6467597 : Blo 896573 6467597 := bstep (se 3 (by rfl) ⟨1212674, by rfl⟩ : syracuseStep 6467597 = 2425349) B2425349
theorem B897043 : Blo 896573 897043 := bstep (se 1 (by rfl) ⟨672782, by rfl⟩ : syracuseStep 897043 = 1345565) B1345565
theorem B897059 : Blo 896573 897059 := bstep (se 1 (by rfl) ⟨672794, by rfl⟩ : syracuseStep 897059 = 1345589) B1345589
theorem B897075 : Blo 896573 897075 := bstep (se 1 (by rfl) ⟨672806, by rfl⟩ : syracuseStep 897075 = 1345613) B1345613
theorem B1519681 : Blo 896573 1519681 := bstep (se 2 (by rfl) ⟨569880, by rfl⟩ : syracuseStep 1519681 = 1139761) B1139761
theorem B897091 : Blo 896573 897091 := bstep (se 1 (by rfl) ⟨672818, by rfl⟩ : syracuseStep 897091 = 1345637) B1345637
theorem B897107 : Blo 896573 897107 := bstep (se 1 (by rfl) ⟨672830, by rfl⟩ : syracuseStep 897107 = 1345661) B1345661
theorem B897123 : Blo 896573 897123 := bstep (se 1 (by rfl) ⟨672842, by rfl⟩ : syracuseStep 897123 = 1345685) B1345685
theorem B1519715 : Blo 896573 1519715 := bstep (se 1 (by rfl) ⟨1139786, by rfl⟩ : syracuseStep 1519715 = 2279573) B2279573
theorem B897139 : Blo 896573 897139 := bstep (se 1 (by rfl) ⟨672854, by rfl⟩ : syracuseStep 897139 = 1345709) B1345709
theorem B897155 : Blo 896573 897155 := bstep (se 1 (by rfl) ⟨672866, by rfl⟩ : syracuseStep 897155 = 1345733) B1345733
theorem B897171 : Blo 896573 897171 := bstep (se 1 (by rfl) ⟨672878, by rfl⟩ : syracuseStep 897171 = 1345757) B1345757
theorem B897187 : Blo 896573 897187 := bstep (se 1 (by rfl) ⟨672890, by rfl⟩ : syracuseStep 897187 = 1345781) B1345781
theorem B897203 : Blo 896573 897203 := bstep (se 1 (by rfl) ⟨672902, by rfl⟩ : syracuseStep 897203 = 1345805) B1345805
theorem B897219 : Blo 896573 897219 := bstep (se 1 (by rfl) ⟨672914, by rfl⟩ : syracuseStep 897219 = 1345829) B1345829
theorem B7680197 : Blo 896573 7680197 := bstep (se 4 (by rfl) ⟨720018, by rfl⟩ : syracuseStep 7680197 = 1440037) B1440037
theorem B897235 : Blo 896573 897235 := bstep (se 1 (by rfl) ⟨672926, by rfl⟩ : syracuseStep 897235 = 1345853) B1345853
theorem B897251 : Blo 896573 897251 := bstep (se 1 (by rfl) ⟨672938, by rfl⟩ : syracuseStep 897251 = 1345877) B1345877
theorem B5124323 : Blo 896573 5124323 := bstep (se 1 (by rfl) ⟨3843242, by rfl⟩ : syracuseStep 5124323 = 7686485) B7686485
theorem B3027185 : Blo 896573 3027185 := bstep (se 2 (by rfl) ⟨1135194, by rfl⟩ : syracuseStep 3027185 = 2270389) B2270389
theorem B897267 : Blo 896573 897267 := bstep (se 1 (by rfl) ⟨672950, by rfl⟩ : syracuseStep 897267 = 1345901) B1345901
theorem B897283 : Blo 896573 897283 := bstep (se 1 (by rfl) ⟨672962, by rfl⟩ : syracuseStep 897283 = 1345925) B1345925
theorem B897299 : Blo 896573 897299 := bstep (se 1 (by rfl) ⟨672974, by rfl⟩ : syracuseStep 897299 = 1345949) B1345949
theorem B897315 : Blo 896573 897315 := bstep (se 1 (by rfl) ⟨672986, by rfl⟩ : syracuseStep 897315 = 1345973) B1345973
theorem B897331 : Blo 896573 897331 := bstep (se 1 (by rfl) ⟨672998, by rfl⟩ : syracuseStep 897331 = 1345997) B1345997
theorem B897347 : Blo 896573 897347 := bstep (se 1 (by rfl) ⟨673010, by rfl⟩ : syracuseStep 897347 = 1346021) B1346021
theorem B897363 : Blo 896573 897363 := bstep (se 1 (by rfl) ⟨673022, by rfl⟩ : syracuseStep 897363 = 1346045) B1346045
theorem B897379 : Blo 896573 897379 := bstep (se 1 (by rfl) ⟨673034, by rfl⟩ : syracuseStep 897379 = 1346069) B1346069
theorem B897395 : Blo 896573 897395 := bstep (se 1 (by rfl) ⟨673046, by rfl⟩ : syracuseStep 897395 = 1346093) B1346093
theorem B897411 : Blo 896573 897411 := bstep (se 1 (by rfl) ⟨673058, by rfl⟩ : syracuseStep 897411 = 1346117) B1346117
theorem B897427 : Blo 896573 897427 := bstep (se 1 (by rfl) ⟨673070, by rfl⟩ : syracuseStep 897427 = 1346141) B1346141
theorem B897443 : Blo 896573 897443 := bstep (se 1 (by rfl) ⟨673082, by rfl⟩ : syracuseStep 897443 = 1346165) B1346165
theorem B897459 : Blo 896573 897459 := bstep (se 1 (by rfl) ⟨673094, by rfl⟩ : syracuseStep 897459 = 1346189) B1346189
theorem B897475 : Blo 896573 897475 := bstep (se 1 (by rfl) ⟨673106, by rfl⟩ : syracuseStep 897475 = 1346213) B1346213
theorem B897491 : Blo 896573 897491 := bstep (se 1 (by rfl) ⟨673118, by rfl⟩ : syracuseStep 897491 = 1346237) B1346237
theorem B897507 : Blo 896573 897507 := bstep (se 1 (by rfl) ⟨673130, by rfl⟩ : syracuseStep 897507 = 1346261) B1346261
theorem B897523 : Blo 896573 897523 := bstep (se 1 (by rfl) ⟨673142, by rfl⟩ : syracuseStep 897523 = 1346285) B1346285
theorem B897539 : Blo 896573 897539 := bstep (se 1 (by rfl) ⟨673154, by rfl⟩ : syracuseStep 897539 = 1346309) B1346309
theorem B897555 : Blo 896573 897555 := bstep (se 1 (by rfl) ⟨673166, by rfl⟩ : syracuseStep 897555 = 1346333) B1346333
theorem B897571 : Blo 896573 897571 := bstep (se 1 (by rfl) ⟨673178, by rfl⟩ : syracuseStep 897571 = 1346357) B1346357
theorem B897587 : Blo 896573 897587 := bstep (se 1 (by rfl) ⟨673190, by rfl⟩ : syracuseStep 897587 = 1346381) B1346381
theorem B897603 : Blo 896573 897603 := bstep (se 1 (by rfl) ⟨673202, by rfl⟩ : syracuseStep 897603 = 1346405) B1346405
theorem B897619 : Blo 896573 897619 := bstep (se 1 (by rfl) ⟨673214, by rfl⟩ : syracuseStep 897619 = 1346429) B1346429
theorem B897635 : Blo 896573 897635 := bstep (se 1 (by rfl) ⟨673226, by rfl⟩ : syracuseStep 897635 = 1346453) B1346453
theorem B897651 : Blo 896573 897651 := bstep (se 1 (by rfl) ⟨673238, by rfl⟩ : syracuseStep 897651 = 1346477) B1346477
theorem B897667 : Blo 896573 897667 := bstep (se 1 (by rfl) ⟨673250, by rfl⟩ : syracuseStep 897667 = 1346501) B1346501
theorem B15348365 : Blo 896573 15348365 := bstep (se 3 (by rfl) ⟨2877818, by rfl⟩ : syracuseStep 15348365 = 5755637) B5755637
theorem B897683 : Blo 896573 897683 := bstep (se 1 (by rfl) ⟨673262, by rfl⟩ : syracuseStep 897683 = 1346525) B1346525
theorem B897699 : Blo 896573 897699 := bstep (se 1 (by rfl) ⟨673274, by rfl⟩ : syracuseStep 897699 = 1346549) B1346549
theorem B897715 : Blo 896573 897715 := bstep (se 1 (by rfl) ⟨673286, by rfl⟩ : syracuseStep 897715 = 1346573) B1346573
theorem B897731 : Blo 896573 897731 := bstep (se 1 (by rfl) ⟨673298, by rfl⟩ : syracuseStep 897731 = 1346597) B1346597
theorem B897747 : Blo 896573 897747 := bstep (se 1 (by rfl) ⟨673310, by rfl⟩ : syracuseStep 897747 = 1346621) B1346621
theorem B897763 : Blo 896573 897763 := bstep (se 1 (by rfl) ⟨673322, by rfl⟩ : syracuseStep 897763 = 1346645) B1346645
theorem B6828785 : Blo 896573 6828785 := bstep (se 2 (by rfl) ⟨2560794, by rfl⟩ : syracuseStep 6828785 = 5121589) B5121589
theorem B897779 : Blo 896573 897779 := bstep (se 1 (by rfl) ⟨673334, by rfl⟩ : syracuseStep 897779 = 1346669) B1346669
theorem B897795 : Blo 896573 897795 := bstep (se 1 (by rfl) ⟨673346, by rfl⟩ : syracuseStep 897795 = 1346693) B1346693
theorem B3027725 : Blo 896573 3027725 := bstep (se 3 (by rfl) ⟨567698, by rfl⟩ : syracuseStep 3027725 = 1135397) B1135397
theorem B2274065 : Blo 896573 2274065 := bstep (se 2 (by rfl) ⟨852774, by rfl⟩ : syracuseStep 2274065 = 1705549) B1705549
theorem B897811 : Blo 896573 897811 := bstep (se 1 (by rfl) ⟨673358, by rfl⟩ : syracuseStep 897811 = 1346717) B1346717
theorem B897827 : Blo 896573 897827 := bstep (se 1 (by rfl) ⟨673370, by rfl⟩ : syracuseStep 897827 = 1346741) B1346741
theorem B2732849 : Blo 896573 2732849 := bstep (se 2 (by rfl) ⟨1024818, by rfl⟩ : syracuseStep 2732849 = 2049637) B2049637
theorem B897843 : Blo 896573 897843 := bstep (se 1 (by rfl) ⟨673382, by rfl⟩ : syracuseStep 897843 = 1346765) B1346765
theorem B3027779 : Blo 896573 3027779 := bstep (se 1 (by rfl) ⟨2270834, by rfl⟩ : syracuseStep 3027779 = 4541669) B4541669
theorem B897859 : Blo 896573 897859 := bstep (se 1 (by rfl) ⟨673394, by rfl⟩ : syracuseStep 897859 = 1346789) B1346789
theorem B2274115 : Blo 896573 2274115 := bstep (se 1 (by rfl) ⟨1705586, by rfl⟩ : syracuseStep 2274115 = 3411173) B3411173
theorem B897875 : Blo 896573 897875 := bstep (se 1 (by rfl) ⟨673406, by rfl⟩ : syracuseStep 897875 = 1346813) B1346813
theorem B897891 : Blo 896573 897891 := bstep (se 1 (by rfl) ⟨673418, by rfl⟩ : syracuseStep 897891 = 1346837) B1346837
theorem B897907 : Blo 896573 897907 := bstep (se 1 (by rfl) ⟨673430, by rfl⟩ : syracuseStep 897907 = 1346861) B1346861
theorem B897923 : Blo 896573 897923 := bstep (se 1 (by rfl) ⟨673442, by rfl⟩ : syracuseStep 897923 = 1346885) B1346885
theorem B2732945 : Blo 896573 2732945 := bstep (se 2 (by rfl) ⟨1024854, by rfl⟩ : syracuseStep 2732945 = 2049709) B2049709
theorem B897939 : Blo 896573 897939 := bstep (se 1 (by rfl) ⟨673454, by rfl⟩ : syracuseStep 897939 = 1346909) B1346909
theorem B897955 : Blo 896573 897955 := bstep (se 1 (by rfl) ⟨673466, by rfl⟩ : syracuseStep 897955 = 1346933) B1346933
theorem B897971 : Blo 896573 897971 := bstep (se 1 (by rfl) ⟨673478, by rfl⟩ : syracuseStep 897971 = 1346957) B1346957
theorem B897987 : Blo 896573 897987 := bstep (se 1 (by rfl) ⟨673490, by rfl⟩ : syracuseStep 897987 = 1346981) B1346981
theorem B2274257 : Blo 896573 2274257 := bstep (se 2 (by rfl) ⟨852846, by rfl⟩ : syracuseStep 2274257 = 1705693) B1705693
theorem B898003 : Blo 896573 898003 := bstep (se 1 (by rfl) ⟨673502, by rfl⟩ : syracuseStep 898003 = 1347005) B1347005
theorem B898019 : Blo 896573 898019 := bstep (se 1 (by rfl) ⟨673514, by rfl⟩ : syracuseStep 898019 = 1347029) B1347029
theorem B898035 : Blo 896573 898035 := bstep (se 1 (by rfl) ⟨673526, by rfl⟩ : syracuseStep 898035 = 1347053) B1347053
theorem B898051 : Blo 896573 898051 := bstep (se 1 (by rfl) ⟨673538, by rfl⟩ : syracuseStep 898051 = 1347077) B1347077
theorem B1618961 : Blo 896573 1618961 := bstep (se 2 (by rfl) ⟨607110, by rfl⟩ : syracuseStep 1618961 = 1214221) B1214221
theorem B898067 : Blo 896573 898067 := bstep (se 1 (by rfl) ⟨673550, by rfl⟩ : syracuseStep 898067 = 1347101) B1347101
theorem B898083 : Blo 896573 898083 := bstep (se 1 (by rfl) ⟨673562, by rfl⟩ : syracuseStep 898083 = 1347125) B1347125
theorem B898099 : Blo 896573 898099 := bstep (se 1 (by rfl) ⟨673574, by rfl⟩ : syracuseStep 898099 = 1347149) B1347149
theorem B898115 : Blo 896573 898115 := bstep (se 1 (by rfl) ⟨673586, by rfl⟩ : syracuseStep 898115 = 1347173) B1347173
theorem B3028049 : Blo 896573 3028049 := bstep (se 2 (by rfl) ⟨1135518, by rfl⟩ : syracuseStep 3028049 = 2271037) B2271037
theorem B898131 : Blo 896573 898131 := bstep (se 1 (by rfl) ⟨673598, by rfl⟩ : syracuseStep 898131 = 1347197) B1347197
theorem B898147 : Blo 896573 898147 := bstep (se 1 (by rfl) ⟨673610, by rfl⟩ : syracuseStep 898147 = 1347221) B1347221
theorem B898163 : Blo 896573 898163 := bstep (se 1 (by rfl) ⟨673622, by rfl⟩ : syracuseStep 898163 = 1347245) B1347245
theorem B898179 : Blo 896573 898179 := bstep (se 1 (by rfl) ⟨673634, by rfl⟩ : syracuseStep 898179 = 1347269) B1347269
theorem B898195 : Blo 896573 898195 := bstep (se 1 (by rfl) ⟨673646, by rfl⟩ : syracuseStep 898195 = 1347293) B1347293
theorem B898211 : Blo 896573 898211 := bstep (se 1 (by rfl) ⟨673658, by rfl⟩ : syracuseStep 898211 = 1347317) B1347317
theorem B898227 : Blo 896573 898227 := bstep (se 1 (by rfl) ⟨673670, by rfl⟩ : syracuseStep 898227 = 1347341) B1347341
theorem B898243 : Blo 896573 898243 := bstep (se 1 (by rfl) ⟨673682, by rfl⟩ : syracuseStep 898243 = 1347365) B1347365
theorem B898259 : Blo 896573 898259 := bstep (se 1 (by rfl) ⟨673694, by rfl⟩ : syracuseStep 898259 = 1347389) B1347389
theorem B898275 : Blo 896573 898275 := bstep (se 1 (by rfl) ⟨673706, by rfl⟩ : syracuseStep 898275 = 1347413) B1347413
theorem B898291 : Blo 896573 898291 := bstep (se 1 (by rfl) ⟨673718, by rfl⟩ : syracuseStep 898291 = 1347437) B1347437
theorem B898307 : Blo 896573 898307 := bstep (se 1 (by rfl) ⟨673730, by rfl⟩ : syracuseStep 898307 = 1347461) B1347461
theorem B898323 : Blo 896573 898323 := bstep (se 1 (by rfl) ⟨673742, by rfl⟩ : syracuseStep 898323 = 1347485) B1347485
theorem B898339 : Blo 896573 898339 := bstep (se 1 (by rfl) ⟨673754, by rfl⟩ : syracuseStep 898339 = 1347509) B1347509
theorem B898355 : Blo 896573 898355 := bstep (se 1 (by rfl) ⟨673766, by rfl⟩ : syracuseStep 898355 = 1347533) B1347533
theorem B898371 : Blo 896573 898371 := bstep (se 1 (by rfl) ⟨673778, by rfl⟩ : syracuseStep 898371 = 1347557) B1347557
theorem B898387 : Blo 896573 898387 := bstep (se 1 (by rfl) ⟨673790, by rfl⟩ : syracuseStep 898387 = 1347581) B1347581
theorem B898403 : Blo 896573 898403 := bstep (se 1 (by rfl) ⟨673802, by rfl⟩ : syracuseStep 898403 = 1347605) B1347605
theorem B898419 : Blo 896573 898419 := bstep (se 1 (by rfl) ⟨673814, by rfl⟩ : syracuseStep 898419 = 1347629) B1347629
theorem B898435 : Blo 896573 898435 := bstep (se 1 (by rfl) ⟨673826, by rfl⟩ : syracuseStep 898435 = 1347653) B1347653
theorem B898451 : Blo 896573 898451 := bstep (se 1 (by rfl) ⟨673838, by rfl⟩ : syracuseStep 898451 = 1347677) B1347677
theorem B898467 : Blo 896573 898467 := bstep (se 1 (by rfl) ⟨673850, by rfl⟩ : syracuseStep 898467 = 1347701) B1347701
theorem B898483 : Blo 896573 898483 := bstep (se 1 (by rfl) ⟨673862, by rfl⟩ : syracuseStep 898483 = 1347725) B1347725
theorem B898499 : Blo 896573 898499 := bstep (se 1 (by rfl) ⟨673874, by rfl⟩ : syracuseStep 898499 = 1347749) B1347749
theorem B898515 : Blo 896573 898515 := bstep (se 1 (by rfl) ⟨673886, by rfl⟩ : syracuseStep 898515 = 1347773) B1347773
theorem B898531 : Blo 896573 898531 := bstep (se 1 (by rfl) ⟨673898, by rfl⟩ : syracuseStep 898531 = 1347797) B1347797
theorem B898547 : Blo 896573 898547 := bstep (se 1 (by rfl) ⟨673910, by rfl⟩ : syracuseStep 898547 = 1347821) B1347821
theorem B898563 : Blo 896573 898563 := bstep (se 1 (by rfl) ⟨673922, by rfl⟩ : syracuseStep 898563 = 1347845) B1347845
theorem B898579 : Blo 896573 898579 := bstep (se 1 (by rfl) ⟨673934, by rfl⟩ : syracuseStep 898579 = 1347869) B1347869
theorem B898595 : Blo 896573 898595 := bstep (se 1 (by rfl) ⟨673946, by rfl⟩ : syracuseStep 898595 = 1347893) B1347893
theorem B898611 : Blo 896573 898611 := bstep (se 1 (by rfl) ⟨673958, by rfl⟩ : syracuseStep 898611 = 1347917) B1347917
theorem B898627 : Blo 896573 898627 := bstep (se 1 (by rfl) ⟨673970, by rfl⟩ : syracuseStep 898627 = 1347941) B1347941
theorem B898643 : Blo 896573 898643 := bstep (se 1 (by rfl) ⟨673982, by rfl⟩ : syracuseStep 898643 = 1347965) B1347965
theorem B898659 : Blo 896573 898659 := bstep (se 1 (by rfl) ⟨673994, by rfl⟩ : syracuseStep 898659 = 1347989) B1347989
theorem B3028589 : Blo 896573 3028589 := bstep (se 3 (by rfl) ⟨567860, by rfl⟩ : syracuseStep 3028589 = 1135721) B1135721
theorem B898675 : Blo 896573 898675 := bstep (se 1 (by rfl) ⟨674006, by rfl⟩ : syracuseStep 898675 = 1348013) B1348013
theorem B898691 : Blo 896573 898691 := bstep (se 1 (by rfl) ⟨674018, by rfl⟩ : syracuseStep 898691 = 1348037) B1348037
theorem B898707 : Blo 896573 898707 := bstep (se 1 (by rfl) ⟨674030, by rfl⟩ : syracuseStep 898707 = 1348061) B1348061
theorem B3028643 : Blo 896573 3028643 := bstep (se 1 (by rfl) ⟨2271482, by rfl⟩ : syracuseStep 3028643 = 4542965) B4542965
theorem B898723 : Blo 896573 898723 := bstep (se 1 (by rfl) ⟨674042, by rfl⟩ : syracuseStep 898723 = 1348085) B1348085
theorem B898739 : Blo 896573 898739 := bstep (se 1 (by rfl) ⟨674054, by rfl⟩ : syracuseStep 898739 = 1348109) B1348109
theorem B898755 : Blo 896573 898755 := bstep (se 1 (by rfl) ⟨674066, by rfl⟩ : syracuseStep 898755 = 1348133) B1348133
theorem B898771 : Blo 896573 898771 := bstep (se 1 (by rfl) ⟨674078, by rfl⟩ : syracuseStep 898771 = 1348157) B1348157
theorem B898787 : Blo 896573 898787 := bstep (se 1 (by rfl) ⟨674090, by rfl⟩ : syracuseStep 898787 = 1348181) B1348181
theorem B4601585 : Blo 896573 4601585 := bstep (se 2 (by rfl) ⟨1725594, by rfl⟩ : syracuseStep 4601585 = 3451189) B3451189
theorem B898803 : Blo 896573 898803 := bstep (se 1 (by rfl) ⟨674102, by rfl⟩ : syracuseStep 898803 = 1348205) B1348205
theorem B898819 : Blo 896573 898819 := bstep (se 1 (by rfl) ⟨674114, by rfl⟩ : syracuseStep 898819 = 1348229) B1348229
theorem B898835 : Blo 896573 898835 := bstep (se 1 (by rfl) ⟨674126, by rfl⟩ : syracuseStep 898835 = 1348253) B1348253
theorem B27997973 : Blo 896573 27997973 := bstep (se 6 (by rfl) ⟨656202, by rfl⟩ : syracuseStep 27997973 = 1312405) B1312405
theorem B5748515 : Blo 896573 5748515 := bstep (se 1 (by rfl) ⟨4311386, by rfl⟩ : syracuseStep 5748515 = 8622773) B8622773
theorem B898851 : Blo 896573 898851 := bstep (se 1 (by rfl) ⟨674138, by rfl⟩ : syracuseStep 898851 = 1348277) B1348277
theorem B898867 : Blo 896573 898867 := bstep (se 1 (by rfl) ⟨674150, by rfl⟩ : syracuseStep 898867 = 1348301) B1348301
theorem B898883 : Blo 896573 898883 := bstep (se 1 (by rfl) ⟨674162, by rfl⟩ : syracuseStep 898883 = 1348325) B1348325
theorem B898899 : Blo 896573 898899 := bstep (se 1 (by rfl) ⟨674174, by rfl⟩ : syracuseStep 898899 = 1348349) B1348349
theorem B898915 : Blo 896573 898915 := bstep (se 1 (by rfl) ⟨674186, by rfl⟩ : syracuseStep 898915 = 1348373) B1348373
theorem B4372337 : Blo 896573 4372337 := bstep (se 2 (by rfl) ⟨1639626, by rfl⟩ : syracuseStep 4372337 = 3279253) B3279253
theorem B898931 : Blo 896573 898931 := bstep (se 1 (by rfl) ⟨674198, by rfl⟩ : syracuseStep 898931 = 1348397) B1348397
theorem B898947 : Blo 896573 898947 := bstep (se 1 (by rfl) ⟨674210, by rfl⟩ : syracuseStep 898947 = 1348421) B1348421
theorem B898963 : Blo 896573 898963 := bstep (se 1 (by rfl) ⟨674222, by rfl⟩ : syracuseStep 898963 = 1348445) B1348445
theorem B898979 : Blo 896573 898979 := bstep (se 1 (by rfl) ⟨674234, by rfl⟩ : syracuseStep 898979 = 1348469) B1348469
theorem B3028913 : Blo 896573 3028913 := bstep (se 2 (by rfl) ⟨1135842, by rfl⟩ : syracuseStep 3028913 = 2271685) B2271685
theorem B2275249 : Blo 896573 2275249 := bstep (se 2 (by rfl) ⟨853218, by rfl⟩ : syracuseStep 2275249 = 1706437) B1706437
theorem B898995 : Blo 896573 898995 := bstep (se 1 (by rfl) ⟨674246, by rfl⟩ : syracuseStep 898995 = 1348493) B1348493
theorem B899011 : Blo 896573 899011 := bstep (se 1 (by rfl) ⟨674258, by rfl⟩ : syracuseStep 899011 = 1348517) B1348517
theorem B6141901 : Blo 896573 6141901 := bstep (se 3 (by rfl) ⟨1151606, by rfl⟩ : syracuseStep 6141901 = 2303213) B2303213
theorem B899027 : Blo 896573 899027 := bstep (se 1 (by rfl) ⟨674270, by rfl⟩ : syracuseStep 899027 = 1348541) B1348541
theorem B899043 : Blo 896573 899043 := bstep (se 1 (by rfl) ⟨674282, by rfl⟩ : syracuseStep 899043 = 1348565) B1348565
theorem B899059 : Blo 896573 899059 := bstep (se 1 (by rfl) ⟨674294, by rfl⟩ : syracuseStep 899059 = 1348589) B1348589
theorem B899075 : Blo 896573 899075 := bstep (se 1 (by rfl) ⟨674306, by rfl⟩ : syracuseStep 899075 = 1348613) B1348613
theorem B899091 : Blo 896573 899091 := bstep (se 1 (by rfl) ⟨674318, by rfl⟩ : syracuseStep 899091 = 1348637) B1348637
theorem B899107 : Blo 896573 899107 := bstep (se 1 (by rfl) ⟨674330, by rfl⟩ : syracuseStep 899107 = 1348661) B1348661
theorem B899123 : Blo 896573 899123 := bstep (se 1 (by rfl) ⟨674342, by rfl⟩ : syracuseStep 899123 = 1348685) B1348685
theorem B899139 : Blo 896573 899139 := bstep (se 1 (by rfl) ⟨674354, by rfl⟩ : syracuseStep 899139 = 1348709) B1348709
theorem B899155 : Blo 896573 899155 := bstep (se 1 (by rfl) ⟨674366, by rfl⟩ : syracuseStep 899155 = 1348733) B1348733
theorem B899171 : Blo 896573 899171 := bstep (se 1 (by rfl) ⟨674378, by rfl⟩ : syracuseStep 899171 = 1348757) B1348757
theorem B899187 : Blo 896573 899187 := bstep (se 1 (by rfl) ⟨674390, by rfl⟩ : syracuseStep 899187 = 1348781) B1348781
theorem B899203 : Blo 896573 899203 := bstep (se 1 (by rfl) ⟨674402, by rfl⟩ : syracuseStep 899203 = 1348805) B1348805
theorem B2046097 : Blo 896573 2046097 := bstep (se 2 (by rfl) ⟨767286, by rfl⟩ : syracuseStep 2046097 = 1534573) B1534573
theorem B899219 : Blo 896573 899219 := bstep (se 1 (by rfl) ⟨674414, by rfl⟩ : syracuseStep 899219 = 1348829) B1348829
theorem B899235 : Blo 896573 899235 := bstep (se 1 (by rfl) ⟨674426, by rfl⟩ : syracuseStep 899235 = 1348853) B1348853
theorem B899251 : Blo 896573 899251 := bstep (se 1 (by rfl) ⟨674438, by rfl⟩ : syracuseStep 899251 = 1348877) B1348877
theorem B2275523 : Blo 896573 2275523 := bstep (se 1 (by rfl) ⟨1706642, by rfl⟩ : syracuseStep 2275523 = 3413285) B3413285
theorem B899267 : Blo 896573 899267 := bstep (se 1 (by rfl) ⟨674450, by rfl⟩ : syracuseStep 899267 = 1348901) B1348901
theorem B899283 : Blo 896573 899283 := bstep (se 1 (by rfl) ⟨674462, by rfl⟩ : syracuseStep 899283 = 1348925) B1348925
theorem B899299 : Blo 896573 899299 := bstep (se 1 (by rfl) ⟨674474, by rfl⟩ : syracuseStep 899299 = 1348949) B1348949
theorem B1620209 : Blo 896573 1620209 := bstep (se 2 (by rfl) ⟨607578, by rfl⟩ : syracuseStep 1620209 = 1215157) B1215157
theorem B899315 : Blo 896573 899315 := bstep (se 1 (by rfl) ⟨674486, by rfl⟩ : syracuseStep 899315 = 1348973) B1348973
theorem B899331 : Blo 896573 899331 := bstep (se 1 (by rfl) ⟨674498, by rfl⟩ : syracuseStep 899331 = 1348997) B1348997
theorem B899347 : Blo 896573 899347 := bstep (se 1 (by rfl) ⟨674510, by rfl⟩ : syracuseStep 899347 = 1349021) B1349021
theorem B899363 : Blo 896573 899363 := bstep (se 1 (by rfl) ⟨674522, by rfl⟩ : syracuseStep 899363 = 1349045) B1349045
theorem B899379 : Blo 896573 899379 := bstep (se 1 (by rfl) ⟨674534, by rfl⟩ : syracuseStep 899379 = 1349069) B1349069
theorem B899395 : Blo 896573 899395 := bstep (se 1 (by rfl) ⟨674546, by rfl⟩ : syracuseStep 899395 = 1349093) B1349093
theorem B899411 : Blo 896573 899411 := bstep (se 1 (by rfl) ⟨674558, by rfl⟩ : syracuseStep 899411 = 1349117) B1349117
theorem B899427 : Blo 896573 899427 := bstep (se 1 (by rfl) ⟨674570, by rfl⟩ : syracuseStep 899427 = 1349141) B1349141
theorem B899443 : Blo 896573 899443 := bstep (se 1 (by rfl) ⟨674582, by rfl⟩ : syracuseStep 899443 = 1349165) B1349165
theorem B2275715 : Blo 896573 2275715 := bstep (se 1 (by rfl) ⟨1706786, by rfl⟩ : syracuseStep 2275715 = 3413573) B3413573
theorem B899459 : Blo 896573 899459 := bstep (se 1 (by rfl) ⟨674594, by rfl⟩ : syracuseStep 899459 = 1349189) B1349189
theorem B899475 : Blo 896573 899475 := bstep (se 1 (by rfl) ⟨674606, by rfl⟩ : syracuseStep 899475 = 1349213) B1349213
theorem B899491 : Blo 896573 899491 := bstep (se 1 (by rfl) ⟨674618, by rfl⟩ : syracuseStep 899491 = 1349237) B1349237
theorem B899507 : Blo 896573 899507 := bstep (se 1 (by rfl) ⟨674630, by rfl⟩ : syracuseStep 899507 = 1349261) B1349261
theorem B899523 : Blo 896573 899523 := bstep (se 1 (by rfl) ⟨674642, by rfl⟩ : syracuseStep 899523 = 1349285) B1349285
theorem B3029453 : Blo 896573 3029453 := bstep (se 3 (by rfl) ⟨568022, by rfl⟩ : syracuseStep 3029453 = 1136045) B1136045
theorem B899539 : Blo 896573 899539 := bstep (se 1 (by rfl) ⟨674654, by rfl⟩ : syracuseStep 899539 = 1349309) B1349309
theorem B899555 : Blo 896573 899555 := bstep (se 1 (by rfl) ⟨674666, by rfl⟩ : syracuseStep 899555 = 1349333) B1349333
theorem B899571 : Blo 896573 899571 := bstep (se 1 (by rfl) ⟨674678, by rfl⟩ : syracuseStep 899571 = 1349357) B1349357
theorem B3029507 : Blo 896573 3029507 := bstep (se 1 (by rfl) ⟨2272130, by rfl⟩ : syracuseStep 3029507 = 4544261) B4544261
theorem B899587 : Blo 896573 899587 := bstep (se 1 (by rfl) ⟨674690, by rfl⟩ : syracuseStep 899587 = 1349381) B1349381
theorem B899603 : Blo 896573 899603 := bstep (se 1 (by rfl) ⟨674702, by rfl⟩ : syracuseStep 899603 = 1349405) B1349405
theorem B899619 : Blo 896573 899619 := bstep (se 1 (by rfl) ⟨674714, by rfl⟩ : syracuseStep 899619 = 1349429) B1349429
theorem B899635 : Blo 896573 899635 := bstep (se 1 (by rfl) ⟨674726, by rfl⟩ : syracuseStep 899635 = 1349453) B1349453
theorem B899651 : Blo 896573 899651 := bstep (se 1 (by rfl) ⟨674738, by rfl⟩ : syracuseStep 899651 = 1349477) B1349477
theorem B899667 : Blo 896573 899667 := bstep (se 1 (by rfl) ⟨674750, by rfl⟩ : syracuseStep 899667 = 1349501) B1349501
theorem B899683 : Blo 896573 899683 := bstep (se 1 (by rfl) ⟨674762, by rfl⟩ : syracuseStep 899683 = 1349525) B1349525
theorem B1915505 : Blo 896573 1915505 := bstep (se 2 (by rfl) ⟨718314, by rfl⟩ : syracuseStep 1915505 = 1436629) B1436629
theorem B899699 : Blo 896573 899699 := bstep (se 1 (by rfl) ⟨674774, by rfl⟩ : syracuseStep 899699 = 1349549) B1349549
theorem B899715 : Blo 896573 899715 := bstep (se 1 (by rfl) ⟨674786, by rfl⟩ : syracuseStep 899715 = 1349573) B1349573
theorem B899731 : Blo 896573 899731 := bstep (se 1 (by rfl) ⟨674798, by rfl⟩ : syracuseStep 899731 = 1349597) B1349597
theorem B899747 : Blo 896573 899747 := bstep (se 1 (by rfl) ⟨674810, by rfl⟩ : syracuseStep 899747 = 1349621) B1349621
theorem B899763 : Blo 896573 899763 := bstep (se 1 (by rfl) ⟨674822, by rfl⟩ : syracuseStep 899763 = 1349645) B1349645
theorem B899779 : Blo 896573 899779 := bstep (se 1 (by rfl) ⟨674834, by rfl⟩ : syracuseStep 899779 = 1349669) B1349669
theorem B899795 : Blo 896573 899795 := bstep (se 1 (by rfl) ⟨674846, by rfl⟩ : syracuseStep 899795 = 1349693) B1349693
theorem B899811 : Blo 896573 899811 := bstep (se 1 (by rfl) ⟨674858, by rfl⟩ : syracuseStep 899811 = 1349717) B1349717
theorem B899827 : Blo 896573 899827 := bstep (se 1 (by rfl) ⟨674870, by rfl⟩ : syracuseStep 899827 = 1349741) B1349741
theorem B899843 : Blo 896573 899843 := bstep (se 1 (by rfl) ⟨674882, by rfl⟩ : syracuseStep 899843 = 1349765) B1349765
theorem B3029777 : Blo 896573 3029777 := bstep (se 2 (by rfl) ⟨1136166, by rfl⟩ : syracuseStep 3029777 = 2272333) B2272333
theorem B899859 : Blo 896573 899859 := bstep (se 1 (by rfl) ⟨674894, by rfl⟩ : syracuseStep 899859 = 1349789) B1349789
theorem B899875 : Blo 896573 899875 := bstep (se 1 (by rfl) ⟨674906, by rfl⟩ : syracuseStep 899875 = 1349813) B1349813
theorem B899891 : Blo 896573 899891 := bstep (se 1 (by rfl) ⟨674918, by rfl⟩ : syracuseStep 899891 = 1349837) B1349837
theorem B899907 : Blo 896573 899907 := bstep (se 1 (by rfl) ⟨674930, by rfl⟩ : syracuseStep 899907 = 1349861) B1349861
theorem B899923 : Blo 896573 899923 := bstep (se 1 (by rfl) ⟨674942, by rfl⟩ : syracuseStep 899923 = 1349885) B1349885
theorem B899939 : Blo 896573 899939 := bstep (se 1 (by rfl) ⟨674954, by rfl⟩ : syracuseStep 899939 = 1349909) B1349909
theorem B899955 : Blo 896573 899955 := bstep (se 1 (by rfl) ⟨674966, by rfl⟩ : syracuseStep 899955 = 1349933) B1349933
theorem B899971 : Blo 896573 899971 := bstep (se 1 (by rfl) ⟨674978, by rfl⟩ : syracuseStep 899971 = 1349957) B1349957
theorem B899987 : Blo 896573 899987 := bstep (se 1 (by rfl) ⟨674990, by rfl⟩ : syracuseStep 899987 = 1349981) B1349981
theorem B900003 : Blo 896573 900003 := bstep (se 1 (by rfl) ⟨675002, by rfl⟩ : syracuseStep 900003 = 1350005) B1350005
theorem B900019 : Blo 896573 900019 := bstep (se 1 (by rfl) ⟨675014, by rfl⟩ : syracuseStep 900019 = 1350029) B1350029
theorem B900035 : Blo 896573 900035 := bstep (se 1 (by rfl) ⟨675026, by rfl⟩ : syracuseStep 900035 = 1350053) B1350053
theorem B900051 : Blo 896573 900051 := bstep (se 1 (by rfl) ⟨675038, by rfl⟩ : syracuseStep 900051 = 1350077) B1350077
theorem B900067 : Blo 896573 900067 := bstep (se 1 (by rfl) ⟨675050, by rfl⟩ : syracuseStep 900067 = 1350101) B1350101
theorem B900083 : Blo 896573 900083 := bstep (se 1 (by rfl) ⟨675062, by rfl⟩ : syracuseStep 900083 = 1350125) B1350125
theorem B900099 : Blo 896573 900099 := bstep (se 1 (by rfl) ⟨675074, by rfl⟩ : syracuseStep 900099 = 1350149) B1350149
theorem B900115 : Blo 896573 900115 := bstep (se 1 (by rfl) ⟨675086, by rfl⟩ : syracuseStep 900115 = 1350173) B1350173
theorem B900131 : Blo 896573 900131 := bstep (se 1 (by rfl) ⟨675098, by rfl⟩ : syracuseStep 900131 = 1350197) B1350197
theorem B900147 : Blo 896573 900147 := bstep (se 1 (by rfl) ⟨675110, by rfl⟩ : syracuseStep 900147 = 1350221) B1350221
theorem B900163 : Blo 896573 900163 := bstep (se 1 (by rfl) ⟨675122, by rfl⟩ : syracuseStep 900163 = 1350245) B1350245
theorem B900179 : Blo 896573 900179 := bstep (se 1 (by rfl) ⟨675134, by rfl⟩ : syracuseStep 900179 = 1350269) B1350269
theorem B900195 : Blo 896573 900195 := bstep (se 1 (by rfl) ⟨675146, by rfl⟩ : syracuseStep 900195 = 1350293) B1350293
theorem B900211 : Blo 896573 900211 := bstep (se 1 (by rfl) ⟨675158, by rfl⟩ : syracuseStep 900211 = 1350317) B1350317
theorem B900227 : Blo 896573 900227 := bstep (se 1 (by rfl) ⟨675170, by rfl⟩ : syracuseStep 900227 = 1350341) B1350341
theorem B900243 : Blo 896573 900243 := bstep (se 1 (by rfl) ⟨675182, by rfl⟩ : syracuseStep 900243 = 1350365) B1350365
theorem B900259 : Blo 896573 900259 := bstep (se 1 (by rfl) ⟨675194, by rfl⟩ : syracuseStep 900259 = 1350389) B1350389
theorem B900275 : Blo 896573 900275 := bstep (se 1 (by rfl) ⟨675206, by rfl⟩ : syracuseStep 900275 = 1350413) B1350413
theorem B900291 : Blo 896573 900291 := bstep (se 1 (by rfl) ⟨675218, by rfl⟩ : syracuseStep 900291 = 1350437) B1350437
theorem B900307 : Blo 896573 900307 := bstep (se 1 (by rfl) ⟨675230, by rfl⟩ : syracuseStep 900307 = 1350461) B1350461
theorem B2079971 : Blo 896573 2079971 := bstep (se 1 (by rfl) ⟨1559978, by rfl⟩ : syracuseStep 2079971 = 3119957) B3119957
theorem B900323 : Blo 896573 900323 := bstep (se 1 (by rfl) ⟨675242, by rfl⟩ : syracuseStep 900323 = 1350485) B1350485
theorem B900339 : Blo 896573 900339 := bstep (se 1 (by rfl) ⟨675254, by rfl⟩ : syracuseStep 900339 = 1350509) B1350509
theorem B900355 : Blo 896573 900355 := bstep (se 1 (by rfl) ⟨675266, by rfl⟩ : syracuseStep 900355 = 1350533) B1350533
theorem B900371 : Blo 896573 900371 := bstep (se 1 (by rfl) ⟨675278, by rfl⟩ : syracuseStep 900371 = 1350557) B1350557
theorem B900387 : Blo 896573 900387 := bstep (se 1 (by rfl) ⟨675290, by rfl⟩ : syracuseStep 900387 = 1350581) B1350581
theorem B3030317 : Blo 896573 3030317 := bstep (se 3 (by rfl) ⟨568184, by rfl⟩ : syracuseStep 3030317 = 1136369) B1136369
theorem B2276657 : Blo 896573 2276657 := bstep (se 2 (by rfl) ⟨853746, by rfl⟩ : syracuseStep 2276657 = 1707493) B1707493
theorem B900403 : Blo 896573 900403 := bstep (se 1 (by rfl) ⟨675302, by rfl⟩ : syracuseStep 900403 = 1350605) B1350605
theorem B900419 : Blo 896573 900419 := bstep (se 1 (by rfl) ⟨675314, by rfl⟩ : syracuseStep 900419 = 1350629) B1350629
theorem B900435 : Blo 896573 900435 := bstep (se 1 (by rfl) ⟨675326, by rfl⟩ : syracuseStep 900435 = 1350653) B1350653
theorem B3030371 : Blo 896573 3030371 := bstep (se 1 (by rfl) ⟨2272778, by rfl⟩ : syracuseStep 3030371 = 4545557) B4545557
theorem B2276707 : Blo 896573 2276707 := bstep (se 1 (by rfl) ⟨1707530, by rfl⟩ : syracuseStep 2276707 = 3415061) B3415061
theorem B900451 : Blo 896573 900451 := bstep (se 1 (by rfl) ⟨675338, by rfl⟩ : syracuseStep 900451 = 1350677) B1350677
theorem B900467 : Blo 896573 900467 := bstep (se 1 (by rfl) ⟨675350, by rfl⟩ : syracuseStep 900467 = 1350701) B1350701
theorem B1916291 : Blo 896573 1916291 := bstep (se 1 (by rfl) ⟨1437218, by rfl⟩ : syracuseStep 1916291 = 2874437) B2874437
theorem B900483 : Blo 896573 900483 := bstep (se 1 (by rfl) ⟨675362, by rfl⟩ : syracuseStep 900483 = 1350725) B1350725
theorem B900499 : Blo 896573 900499 := bstep (se 1 (by rfl) ⟨675374, by rfl⟩ : syracuseStep 900499 = 1350749) B1350749
theorem B900515 : Blo 896573 900515 := bstep (se 1 (by rfl) ⟨675386, by rfl⟩ : syracuseStep 900515 = 1350773) B1350773
theorem B900531 : Blo 896573 900531 := bstep (se 1 (by rfl) ⟨675398, by rfl⟩ : syracuseStep 900531 = 1350797) B1350797
theorem B900547 : Blo 896573 900547 := bstep (se 1 (by rfl) ⟨675410, by rfl⟩ : syracuseStep 900547 = 1350821) B1350821
theorem B900563 : Blo 896573 900563 := bstep (se 1 (by rfl) ⟨675422, by rfl⟩ : syracuseStep 900563 = 1350845) B1350845
theorem B2276849 : Blo 896573 2276849 := bstep (se 2 (by rfl) ⟨853818, by rfl⟩ : syracuseStep 2276849 = 1707637) B1707637
theorem B3030641 : Blo 896573 3030641 := bstep (se 2 (by rfl) ⟨1136490, by rfl⟩ : syracuseStep 3030641 = 2272981) B2272981
theorem B5750513 : Blo 896573 5750513 := bstep (se 2 (by rfl) ⟨2156442, by rfl⟩ : syracuseStep 5750513 = 4312885) B4312885
theorem B1457921 : Blo 896573 1457921 := bstep (se 2 (by rfl) ⟨546720, by rfl⟩ : syracuseStep 1457921 = 1093441) B1093441
theorem B2080561 : Blo 896573 2080561 := bstep (se 2 (by rfl) ⟨780210, by rfl⟩ : syracuseStep 2080561 = 1560421) B1560421
theorem B17252149 : Blo 896573 17252149 := bstep (se 5 (by rfl) ⟨808694, by rfl⟩ : syracuseStep 17252149 = 1617389) B1617389
theorem B1752931 : Blo 896573 1752931 := bstep (se 1 (by rfl) ⟨1314698, by rfl⟩ : syracuseStep 1752931 = 2629397) B2629397
theorem B1458179 : Blo 896573 1458179 := bstep (se 1 (by rfl) ⟨1093634, by rfl⟩ : syracuseStep 1458179 = 2187269) B2187269
theorem B3031181 : Blo 896573 3031181 := bstep (se 3 (by rfl) ⟨568346, by rfl⟩ : syracuseStep 3031181 = 1136693) B1136693
theorem B3031235 : Blo 896573 3031235 := bstep (se 1 (by rfl) ⟨2273426, by rfl⟩ : syracuseStep 3031235 = 4546853) B4546853
theorem B4604131 : Blo 896573 4604131 := bstep (se 1 (by rfl) ⟨3453098, by rfl⟩ : syracuseStep 4604131 = 6906197) B6906197
theorem B1917265 : Blo 896573 1917265 := bstep (se 2 (by rfl) ⟨718974, by rfl⟩ : syracuseStep 1917265 = 1437949) B1437949
theorem B1622435 : Blo 896573 1622435 := bstep (se 1 (by rfl) ⟨1216826, by rfl⟩ : syracuseStep 1622435 = 2433653) B2433653
theorem B3031505 : Blo 896573 3031505 := bstep (se 2 (by rfl) ⟨1136814, by rfl⟩ : syracuseStep 3031505 = 2273629) B2273629
theorem B2277841 : Blo 896573 2277841 := bstep (se 2 (by rfl) ⟨854190, by rfl⟩ : syracuseStep 2277841 = 1708381) B1708381
theorem B9224675 : Blo 896573 9224675 := bstep (se 1 (by rfl) ⟨6918506, by rfl⟩ : syracuseStep 9224675 = 13837013) B13837013
theorem B4538915 : Blo 896573 4538915 := bstep (se 1 (by rfl) ⟨3404186, by rfl⟩ : syracuseStep 4538915 = 6808373) B6808373
theorem B1917521 : Blo 896573 1917521 := bstep (se 2 (by rfl) ⟨719070, by rfl⟩ : syracuseStep 1917521 = 1438141) B1438141
theorem B7291619 : Blo 896573 7291619 := bstep (se 1 (by rfl) ⟨5468714, by rfl⟩ : syracuseStep 7291619 = 10937429) B10937429
theorem B2278115 : Blo 896573 2278115 := bstep (se 1 (by rfl) ⟨1708586, by rfl⟩ : syracuseStep 2278115 = 3417173) B3417173
theorem B2278307 : Blo 896573 2278307 := bstep (se 1 (by rfl) ⟨1708730, by rfl⟩ : syracuseStep 2278307 = 3417461) B3417461
theorem B3032045 : Blo 896573 3032045 := bstep (se 3 (by rfl) ⟨568508, by rfl⟩ : syracuseStep 3032045 = 1137017) B1137017
theorem B3032099 : Blo 896573 3032099 := bstep (se 1 (by rfl) ⟨2274074, by rfl⟩ : syracuseStep 3032099 = 4548149) B4548149
theorem B3032369 : Blo 896573 3032369 := bstep (se 2 (by rfl) ⟨1137138, by rfl⟩ : syracuseStep 3032369 = 2274277) B2274277
theorem B4539725 : Blo 896573 4539725 := bstep (se 3 (by rfl) ⟨851198, by rfl⟩ : syracuseStep 4539725 = 1702397) B1702397
theorem B5752205 : Blo 896573 5752205 := bstep (se 3 (by rfl) ⟨1078538, by rfl⟩ : syracuseStep 5752205 = 2157077) B2157077
theorem B3032909 : Blo 896573 3032909 := bstep (se 3 (by rfl) ⟨568670, by rfl⟩ : syracuseStep 3032909 = 1137341) B1137341
theorem B2279249 : Blo 896573 2279249 := bstep (se 2 (by rfl) ⟨854718, by rfl⟩ : syracuseStep 2279249 = 1709437) B1709437
theorem B1918819 : Blo 896573 1918819 := bstep (se 1 (by rfl) ⟨1439114, by rfl⟩ : syracuseStep 1918819 = 2878229) B2878229
theorem B3032963 : Blo 896573 3032963 := bstep (se 1 (by rfl) ⟨2274722, by rfl⟩ : syracuseStep 3032963 = 4549445) B4549445
theorem B2279299 : Blo 896573 2279299 := bstep (se 1 (by rfl) ⟨1709474, by rfl⟩ : syracuseStep 2279299 = 3418949) B3418949
theorem B2279441 : Blo 896573 2279441 := bstep (se 2 (by rfl) ⟨854790, by rfl⟩ : syracuseStep 2279441 = 1709581) B1709581
theorem B2738225 : Blo 896573 2738225 := bstep (se 2 (by rfl) ⟨1026834, by rfl⟩ : syracuseStep 2738225 = 2053669) B2053669
theorem B3033233 : Blo 896573 3033233 := bstep (se 2 (by rfl) ⟨1137462, by rfl⟩ : syracuseStep 3033233 = 2274925) B2274925
theorem B2017457 : Blo 896573 2017457 := bstep (se 2 (by rfl) ⟨756546, by rfl⟩ : syracuseStep 2017457 = 1513093) B1513093
theorem B1919153 : Blo 896573 1919153 := bstep (se 2 (by rfl) ⟨719682, by rfl⟩ : syracuseStep 1919153 = 1439365) B1439365
theorem B2017475 : Blo 896573 2017475 := bstep (se 1 (by rfl) ⟨1513106, by rfl⟩ : syracuseStep 2017475 = 3026213) B3026213
theorem B4868429 : Blo 896573 4868429 := bstep (se 3 (by rfl) ⟨912830, by rfl⟩ : syracuseStep 4868429 = 1825661) B1825661
theorem B2017745 : Blo 896573 2017745 := bstep (se 2 (by rfl) ⟨756654, by rfl⟩ : syracuseStep 2017745 = 1513309) B1513309
theorem B2017763 : Blo 896573 2017763 := bstep (se 1 (by rfl) ⟨1513322, by rfl⟩ : syracuseStep 2017763 = 3026645) B3026645
theorem B3033773 : Blo 896573 3033773 := bstep (se 3 (by rfl) ⟨568832, by rfl⟩ : syracuseStep 3033773 = 1137665) B1137665
theorem B3033827 : Blo 896573 3033827 := bstep (se 1 (by rfl) ⟨2275370, by rfl⟩ : syracuseStep 3033827 = 4550741) B4550741
theorem B2018033 : Blo 896573 2018033 := bstep (se 2 (by rfl) ⟨756762, by rfl⟩ : syracuseStep 2018033 = 1513525) B1513525
theorem B11062001 : Blo 896573 11062001 := bstep (se 2 (by rfl) ⟨4148250, by rfl⟩ : syracuseStep 11062001 = 8296501) B8296501
theorem B2018051 : Blo 896573 2018051 := bstep (se 1 (by rfl) ⟨1513538, by rfl⟩ : syracuseStep 2018051 = 3027077) B3027077
theorem B3034097 : Blo 896573 3034097 := bstep (se 2 (by rfl) ⟨1137786, by rfl⟩ : syracuseStep 3034097 = 2275573) B2275573
theorem B2018321 : Blo 896573 2018321 := bstep (se 2 (by rfl) ⟨756870, by rfl⟩ : syracuseStep 2018321 = 1513741) B1513741
theorem B2018339 : Blo 896573 2018339 := bstep (se 1 (by rfl) ⟨1513754, by rfl⟩ : syracuseStep 2018339 = 3027509) B3027509
theorem B11095139 : Blo 896573 11095139 := bstep (se 1 (by rfl) ⟨8321354, by rfl⟩ : syracuseStep 11095139 = 16642709) B16642709
theorem B2018609 : Blo 896573 2018609 := bstep (se 2 (by rfl) ⟨756978, by rfl⟩ : syracuseStep 2018609 = 1513957) B1513957
theorem B6147377 : Blo 896573 6147377 := bstep (se 2 (by rfl) ⟨2305266, by rfl⟩ : syracuseStep 6147377 = 4610533) B4610533
theorem B2018627 : Blo 896573 2018627 := bstep (se 1 (by rfl) ⟨1513970, by rfl⟩ : syracuseStep 2018627 = 3027941) B3027941
theorem B1920323 : Blo 896573 1920323 := bstep (se 1 (by rfl) ⟨1440242, by rfl⟩ : syracuseStep 1920323 = 2880485) B2880485
theorem B1199539 : Blo 896573 1199539 := bstep (se 1 (by rfl) ⟨899654, by rfl⟩ : syracuseStep 1199539 = 1799309) B1799309
theorem B3034637 : Blo 896573 3034637 := bstep (se 3 (by rfl) ⟨568994, by rfl⟩ : syracuseStep 3034637 = 1137989) B1137989
theorem B1297955 : Blo 896573 1297955 := bstep (se 1 (by rfl) ⟨973466, by rfl⟩ : syracuseStep 1297955 = 1946933) B1946933
theorem B3034691 : Blo 896573 3034691 := bstep (se 1 (by rfl) ⟨2276018, by rfl⟩ : syracuseStep 3034691 = 4552037) B4552037
theorem B2018897 : Blo 896573 2018897 := bstep (se 2 (by rfl) ⟨757086, by rfl⟩ : syracuseStep 2018897 = 1514173) B1514173
theorem B2018915 : Blo 896573 2018915 := bstep (se 1 (by rfl) ⟨1514186, by rfl⟩ : syracuseStep 2018915 = 3028373) B3028373
theorem B3034961 : Blo 896573 3034961 := bstep (se 2 (by rfl) ⟨1138110, by rfl⟩ : syracuseStep 3034961 = 2276221) B2276221
theorem B2019185 : Blo 896573 2019185 := bstep (se 2 (by rfl) ⟨757194, by rfl⟩ : syracuseStep 2019185 = 1514389) B1514389
theorem B2019203 : Blo 896573 2019203 := bstep (se 1 (by rfl) ⟨1514402, by rfl⟩ : syracuseStep 2019203 = 3028805) B3028805
theorem B3231665 : Blo 896573 3231665 := bstep (se 2 (by rfl) ⟨1211874, by rfl⟩ : syracuseStep 3231665 = 2423749) B2423749
theorem B3067885 : Blo 896573 3067885 := bstep (se 3 (by rfl) ⟨575228, by rfl⟩ : syracuseStep 3067885 = 1150457) B1150457
theorem B1364035 : Blo 896573 1364035 := bstep (se 1 (by rfl) ⟨1023026, by rfl⟩ : syracuseStep 1364035 = 2046053) B2046053
theorem B2019473 : Blo 896573 2019473 := bstep (se 2 (by rfl) ⟨757302, by rfl⟩ : syracuseStep 2019473 = 1514605) B1514605
theorem B1134739 : Blo 896573 1134739 := bstep (se 1 (by rfl) ⟨851054, by rfl⟩ : syracuseStep 1134739 = 1702109) B1702109
theorem B2019491 : Blo 896573 2019491 := bstep (se 1 (by rfl) ⟨1514618, by rfl⟩ : syracuseStep 2019491 = 3029237) B3029237
theorem B4542641 : Blo 896573 4542641 := bstep (se 2 (by rfl) ⟨1703490, by rfl⟩ : syracuseStep 4542641 = 3406981) B3406981
theorem B3035501 : Blo 896573 3035501 := bstep (se 3 (by rfl) ⟨569156, by rfl⟩ : syracuseStep 3035501 = 1138313) B1138313
theorem B3035555 : Blo 896573 3035555 := bstep (se 1 (by rfl) ⟨2276666, by rfl⟩ : syracuseStep 3035555 = 4553333) B4553333
theorem B2019761 : Blo 896573 2019761 := bstep (se 2 (by rfl) ⟨757410, by rfl⟩ : syracuseStep 2019761 = 1514821) B1514821
theorem B2019779 : Blo 896573 2019779 := bstep (se 1 (by rfl) ⟨1514834, by rfl⟩ : syracuseStep 2019779 = 3029669) B3029669
theorem B1135235 : Blo 896573 1135235 := bstep (se 1 (by rfl) ⟨851426, by rfl⟩ : syracuseStep 1135235 = 1702853) B1702853
theorem B3035825 : Blo 896573 3035825 := bstep (se 2 (by rfl) ⟨1138434, by rfl⟩ : syracuseStep 3035825 = 2276869) B2276869
theorem B2020049 : Blo 896573 2020049 := bstep (se 2 (by rfl) ⟨757518, by rfl⟩ : syracuseStep 2020049 = 1515037) B1515037
theorem B2020067 : Blo 896573 2020067 := bstep (se 1 (by rfl) ⟨1515050, by rfl⟩ : syracuseStep 2020067 = 3030101) B3030101
theorem B7688945 : Blo 896573 7688945 := bstep (se 2 (by rfl) ⟨2883354, by rfl⟩ : syracuseStep 7688945 = 5766709) B5766709
theorem B1823651 : Blo 896573 1823651 := bstep (se 1 (by rfl) ⟨1367738, by rfl⟩ : syracuseStep 1823651 = 2735477) B2735477
theorem B1823683 : Blo 896573 1823683 := bstep (se 1 (by rfl) ⟨1367762, by rfl⟩ : syracuseStep 1823683 = 2735525) B2735525
theorem B2020337 : Blo 896573 2020337 := bstep (se 2 (by rfl) ⟨757626, by rfl⟩ : syracuseStep 2020337 = 1515253) B1515253
theorem B2020355 : Blo 896573 2020355 := bstep (se 1 (by rfl) ⟨1515266, by rfl⟩ : syracuseStep 2020355 = 3030533) B3030533
theorem B3036365 : Blo 896573 3036365 := bstep (se 3 (by rfl) ⟨569318, by rfl⟩ : syracuseStep 3036365 = 1138637) B1138637
theorem B1299665 : Blo 896573 1299665 := bstep (se 2 (by rfl) ⟨487374, by rfl⟩ : syracuseStep 1299665 = 974749) B974749
theorem B7296227 : Blo 896573 7296227 := bstep (se 1 (by rfl) ⟨5472170, by rfl⟩ : syracuseStep 7296227 = 10944341) B10944341
theorem B2872579 : Blo 896573 2872579 := bstep (se 1 (by rfl) ⟨2154434, by rfl⟩ : syracuseStep 2872579 = 4308869) B4308869
theorem B3036419 : Blo 896573 3036419 := bstep (se 1 (by rfl) ⟨2277314, by rfl⟩ : syracuseStep 3036419 = 4554629) B4554629
theorem B2020625 : Blo 896573 2020625 := bstep (se 2 (by rfl) ⟨757734, by rfl⟩ : syracuseStep 2020625 = 1515469) B1515469
theorem B2020643 : Blo 896573 2020643 := bstep (se 1 (by rfl) ⟨1515482, by rfl⟩ : syracuseStep 2020643 = 3030965) B3030965
theorem B1922339 : Blo 896573 1922339 := bstep (se 1 (by rfl) ⟨1441754, by rfl⟩ : syracuseStep 1922339 = 2883509) B2883509
theorem B1135939 : Blo 896573 1135939 := bstep (se 1 (by rfl) ⟨851954, by rfl⟩ : syracuseStep 1135939 = 1703909) B1703909
theorem B1136035 : Blo 896573 1136035 := bstep (se 1 (by rfl) ⟨852026, by rfl⟩ : syracuseStep 1136035 = 1704053) B1704053
theorem B3036689 : Blo 896573 3036689 := bstep (se 2 (by rfl) ⟨1138758, by rfl⟩ : syracuseStep 3036689 = 2277517) B2277517
theorem B2020913 : Blo 896573 2020913 := bstep (se 2 (by rfl) ⟨757842, by rfl⟩ : syracuseStep 2020913 = 1515685) B1515685
theorem B2020931 : Blo 896573 2020931 := bstep (se 1 (by rfl) ⟨1515698, by rfl⟩ : syracuseStep 2020931 = 3031397) B3031397
theorem B4544099 : Blo 896573 4544099 := bstep (se 1 (by rfl) ⟨3408074, by rfl⟩ : syracuseStep 4544099 = 6816149) B6816149
theorem B2021201 : Blo 896573 2021201 := bstep (se 2 (by rfl) ⟨757950, by rfl⟩ : syracuseStep 2021201 = 1515901) B1515901
theorem B2021219 : Blo 896573 2021219 := bstep (se 1 (by rfl) ⟨1515914, by rfl⟩ : syracuseStep 2021219 = 3031829) B3031829
theorem B1136531 : Blo 896573 1136531 := bstep (se 1 (by rfl) ⟨852398, by rfl⟩ : syracuseStep 1136531 = 1704797) B1704797
theorem B972691 : Blo 896573 972691 := bstep (se 1 (by rfl) ⟨729518, by rfl⟩ : syracuseStep 972691 = 1459037) B1459037
theorem B3037229 : Blo 896573 3037229 := bstep (se 3 (by rfl) ⟨569480, by rfl⟩ : syracuseStep 3037229 = 1138961) B1138961
theorem B2873411 : Blo 896573 2873411 := bstep (se 1 (by rfl) ⟨2155058, by rfl⟩ : syracuseStep 2873411 = 4310117) B4310117
theorem B3037283 : Blo 896573 3037283 := bstep (se 1 (by rfl) ⟨2277962, by rfl⟩ : syracuseStep 3037283 = 4555925) B4555925
theorem B2021489 : Blo 896573 2021489 := bstep (se 2 (by rfl) ⟨758058, by rfl⟩ : syracuseStep 2021489 = 1516117) B1516117
theorem B2021507 : Blo 896573 2021507 := bstep (se 1 (by rfl) ⟨1516130, by rfl⟩ : syracuseStep 2021507 = 3032261) B3032261
theorem B7297165 : Blo 896573 7297165 := bstep (se 3 (by rfl) ⟨1368218, by rfl⟩ : syracuseStep 7297165 = 2736437) B2736437
theorem B11688245 : Blo 896573 11688245 := bstep (se 5 (by rfl) ⟨547886, by rfl⟩ : syracuseStep 11688245 = 1095773) B1095773
theorem B3037553 : Blo 896573 3037553 := bstep (se 2 (by rfl) ⟨1139082, by rfl⟩ : syracuseStep 3037553 = 2278165) B2278165
theorem B4544909 : Blo 896573 4544909 := bstep (se 3 (by rfl) ⟨852170, by rfl⟩ : syracuseStep 4544909 = 1704341) B1704341
theorem B2021777 : Blo 896573 2021777 := bstep (se 2 (by rfl) ⟨758166, by rfl⟩ : syracuseStep 2021777 = 1516333) B1516333
theorem B2021795 : Blo 896573 2021795 := bstep (se 1 (by rfl) ⟨1516346, by rfl⟩ : syracuseStep 2021795 = 3032693) B3032693
theorem B2873809 : Blo 896573 2873809 := bstep (se 2 (by rfl) ⟨1077678, by rfl⟩ : syracuseStep 2873809 = 2155357) B2155357
theorem B16407011 : Blo 896573 16407011 := bstep (se 1 (by rfl) ⟨12305258, by rfl⟩ : syracuseStep 16407011 = 24610517) B24610517
theorem B2873873 : Blo 896573 2873873 := bstep (se 2 (by rfl) ⟨1077702, by rfl⟩ : syracuseStep 2873873 = 2155405) B2155405
theorem B1137235 : Blo 896573 1137235 := bstep (se 1 (by rfl) ⟨852926, by rfl⟩ : syracuseStep 1137235 = 1705853) B1705853
theorem B2022065 : Blo 896573 2022065 := bstep (se 2 (by rfl) ⟨758274, by rfl⟩ : syracuseStep 2022065 = 1516549) B1516549
theorem B1137331 : Blo 896573 1137331 := bstep (se 1 (by rfl) ⟨852998, by rfl⟩ : syracuseStep 1137331 = 1705997) B1705997
theorem B2022083 : Blo 896573 2022083 := bstep (se 1 (by rfl) ⟨1516562, by rfl⟩ : syracuseStep 2022083 = 3033125) B3033125
theorem B4381553 : Blo 896573 4381553 := bstep (se 2 (by rfl) ⟨1643082, by rfl⟩ : syracuseStep 4381553 = 3286165) B3286165
theorem B3038093 : Blo 896573 3038093 := bstep (se 3 (by rfl) ⟨569642, by rfl⟩ : syracuseStep 3038093 = 1139285) B1139285
theorem B3038147 : Blo 896573 3038147 := bstep (se 1 (by rfl) ⟨2278610, by rfl⟩ : syracuseStep 3038147 = 4557221) B4557221
theorem B2022353 : Blo 896573 2022353 := bstep (se 2 (by rfl) ⟨758382, by rfl⟩ : syracuseStep 2022353 = 1516765) B1516765
theorem B2022371 : Blo 896573 2022371 := bstep (se 1 (by rfl) ⟨1516778, by rfl⟩ : syracuseStep 2022371 = 3033557) B3033557
theorem B1137827 : Blo 896573 1137827 := bstep (se 1 (by rfl) ⟨853370, by rfl⟩ : syracuseStep 1137827 = 1706741) B1706741
theorem B5463217 : Blo 896573 5463217 := bstep (se 2 (by rfl) ⟨2048706, by rfl⟩ : syracuseStep 5463217 = 4097413) B4097413
theorem B3071171 : Blo 896573 3071171 := bstep (se 1 (by rfl) ⟨2303378, by rfl⟩ : syracuseStep 3071171 = 4606757) B4606757
theorem B3038417 : Blo 896573 3038417 := bstep (se 2 (by rfl) ⟨1139406, by rfl⟩ : syracuseStep 3038417 = 2278813) B2278813
theorem B2022641 : Blo 896573 2022641 := bstep (se 2 (by rfl) ⟨758490, by rfl⟩ : syracuseStep 2022641 = 1516981) B1516981
theorem B2022659 : Blo 896573 2022659 := bstep (se 1 (by rfl) ⟨1516994, by rfl⟩ : syracuseStep 2022659 = 3033989) B3033989
theorem B2022929 : Blo 896573 2022929 := bstep (se 2 (by rfl) ⟨758598, by rfl⟩ : syracuseStep 2022929 = 1517197) B1517197
theorem B2022947 : Blo 896573 2022947 := bstep (se 1 (by rfl) ⟨1517210, by rfl⟩ : syracuseStep 2022947 = 3034421) B3034421
theorem B3038957 : Blo 896573 3038957 := bstep (se 3 (by rfl) ⟨569804, by rfl⟩ : syracuseStep 3038957 = 1139609) B1139609
theorem B3039011 : Blo 896573 3039011 := bstep (se 1 (by rfl) ⟨2279258, by rfl⟩ : syracuseStep 3039011 = 4558517) B4558517
theorem B2023217 : Blo 896573 2023217 := bstep (se 2 (by rfl) ⟨758706, by rfl⟩ : syracuseStep 2023217 = 1517413) B1517413
theorem B2023235 : Blo 896573 2023235 := bstep (se 1 (by rfl) ⟨1517426, by rfl⟩ : syracuseStep 2023235 = 3034853) B3034853
theorem B2744131 : Blo 896573 2744131 := bstep (se 1 (by rfl) ⟨2058098, by rfl⟩ : syracuseStep 2744131 = 4116197) B4116197
theorem B1138531 : Blo 896573 1138531 := bstep (se 1 (by rfl) ⟨853898, by rfl⟩ : syracuseStep 1138531 = 1707797) B1707797
theorem B1138627 : Blo 896573 1138627 := bstep (se 1 (by rfl) ⟨853970, by rfl⟩ : syracuseStep 1138627 = 1707941) B1707941
theorem B3039281 : Blo 896573 3039281 := bstep (se 2 (by rfl) ⟨1139730, by rfl⟩ : syracuseStep 3039281 = 2279461) B2279461
theorem B2023505 : Blo 896573 2023505 := bstep (se 2 (by rfl) ⟨758814, by rfl⟩ : syracuseStep 2023505 = 1517629) B1517629
theorem B2023523 : Blo 896573 2023523 := bstep (se 1 (by rfl) ⟨1517642, by rfl⟩ : syracuseStep 2023523 = 3035285) B3035285
theorem B12312931 : Blo 896573 12312931 := bstep (se 1 (by rfl) ⟨9234698, by rfl⟩ : syracuseStep 12312931 = 18469397) B18469397
theorem B2023793 : Blo 896573 2023793 := bstep (se 2 (by rfl) ⟨758922, by rfl⟩ : syracuseStep 2023793 = 1517845) B1517845
theorem B2023811 : Blo 896573 2023811 := bstep (se 1 (by rfl) ⟨1517858, by rfl⟩ : syracuseStep 2023811 = 3035717) B3035717
theorem B1139123 : Blo 896573 1139123 := bstep (se 1 (by rfl) ⟨854342, by rfl⟩ : syracuseStep 1139123 = 1708685) B1708685
theorem B4317731 : Blo 896573 4317731 := bstep (se 1 (by rfl) ⟨3238298, by rfl⟩ : syracuseStep 4317731 = 6476597) B6476597
theorem B2024081 : Blo 896573 2024081 := bstep (se 2 (by rfl) ⟨759030, by rfl⟩ : syracuseStep 2024081 = 1518061) B1518061
theorem B2024099 : Blo 896573 2024099 := bstep (se 1 (by rfl) ⟨1518074, by rfl⟩ : syracuseStep 2024099 = 3036149) B3036149
theorem B10216205 : Blo 896573 10216205 := bstep (se 3 (by rfl) ⟨1915538, by rfl⟩ : syracuseStep 10216205 = 3831077) B3831077
theorem B2024369 : Blo 896573 2024369 := bstep (se 2 (by rfl) ⟨759138, by rfl⟩ : syracuseStep 2024369 = 1518277) B1518277
theorem B2024387 : Blo 896573 2024387 := bstep (se 1 (by rfl) ⟨1518290, by rfl⟩ : syracuseStep 2024387 = 3036581) B3036581
theorem B1008787 : Blo 896573 1008787 := bstep (se 1 (by rfl) ⟨756590, by rfl⟩ : syracuseStep 1008787 = 1513181) B1513181
theorem B2024657 : Blo 896573 2024657 := bstep (se 2 (by rfl) ⟨759246, by rfl⟩ : syracuseStep 2024657 = 1518493) B1518493
theorem B9233635 : Blo 896573 9233635 := bstep (se 1 (by rfl) ⟨6925226, by rfl⟩ : syracuseStep 9233635 = 13850453) B13850453
theorem B2024675 : Blo 896573 2024675 := bstep (se 1 (by rfl) ⟨1518506, by rfl⟩ : syracuseStep 2024675 = 3037013) B3037013
theorem B4547825 : Blo 896573 4547825 := bstep (se 2 (by rfl) ⟨1705434, by rfl⟩ : syracuseStep 4547825 = 3410869) B3410869
theorem B1008931 : Blo 896573 1008931 := bstep (se 1 (by rfl) ⟨756698, by rfl⟩ : syracuseStep 1008931 = 1513397) B1513397
theorem B1009075 : Blo 896573 1009075 := bstep (se 1 (by rfl) ⟨756806, by rfl⟩ : syracuseStep 1009075 = 1513613) B1513613
theorem B2024945 : Blo 896573 2024945 := bstep (se 2 (by rfl) ⟨759354, by rfl⟩ : syracuseStep 2024945 = 1518709) B1518709
theorem B2024963 : Blo 896573 2024963 := bstep (se 1 (by rfl) ⟨1518722, by rfl⟩ : syracuseStep 2024963 = 3037445) B3037445
theorem B1009219 : Blo 896573 1009219 := bstep (se 1 (by rfl) ⟨756914, by rfl⟩ : syracuseStep 1009219 = 1513829) B1513829
theorem B1009363 : Blo 896573 1009363 := bstep (se 1 (by rfl) ⟨757022, by rfl⟩ : syracuseStep 1009363 = 1514045) B1514045
theorem B2025233 : Blo 896573 2025233 := bstep (se 2 (by rfl) ⟨759462, by rfl⟩ : syracuseStep 2025233 = 1518925) B1518925
theorem B2025251 : Blo 896573 2025251 := bstep (se 1 (by rfl) ⟨1518938, by rfl⟩ : syracuseStep 2025251 = 3037877) B3037877
theorem B1009507 : Blo 896573 1009507 := bstep (se 1 (by rfl) ⟨757130, by rfl⟩ : syracuseStep 1009507 = 1514261) B1514261
theorem B4319075 : Blo 896573 4319075 := bstep (se 1 (by rfl) ⟨3239306, by rfl⟩ : syracuseStep 4319075 = 6478613) B6478613
theorem B1009651 : Blo 896573 1009651 := bstep (se 1 (by rfl) ⟨757238, by rfl⟩ : syracuseStep 1009651 = 1514477) B1514477
theorem B1402867 : Blo 896573 1402867 := bstep (se 1 (by rfl) ⟨1052150, by rfl⟩ : syracuseStep 1402867 = 2104301) B2104301
theorem B2025521 : Blo 896573 2025521 := bstep (se 2 (by rfl) ⟨759570, by rfl⟩ : syracuseStep 2025521 = 1519141) B1519141
theorem B2025539 : Blo 896573 2025539 := bstep (se 1 (by rfl) ⟨1519154, by rfl⟩ : syracuseStep 2025539 = 3038309) B3038309
theorem B1009795 : Blo 896573 1009795 := bstep (se 1 (by rfl) ⟨757346, by rfl⟩ : syracuseStep 1009795 = 1514693) B1514693
theorem B1009939 : Blo 896573 1009939 := bstep (se 1 (by rfl) ⟨757454, by rfl⟩ : syracuseStep 1009939 = 1514909) B1514909
theorem B5531981 : Blo 896573 5531981 := bstep (se 3 (by rfl) ⟨1037246, by rfl⟩ : syracuseStep 5531981 = 2074493) B2074493
theorem B2025809 : Blo 896573 2025809 := bstep (se 2 (by rfl) ⟨759678, by rfl⟩ : syracuseStep 2025809 = 1519357) B1519357
theorem B2025827 : Blo 896573 2025827 := bstep (se 1 (by rfl) ⟨1519370, by rfl⟩ : syracuseStep 2025827 = 3038741) B3038741
theorem B1010083 : Blo 896573 1010083 := bstep (se 1 (by rfl) ⟨757562, by rfl⟩ : syracuseStep 1010083 = 1515125) B1515125
theorem B4319729 : Blo 896573 4319729 := bstep (se 2 (by rfl) ⟨1619898, by rfl⟩ : syracuseStep 4319729 = 3239797) B3239797
theorem B1010227 : Blo 896573 1010227 := bstep (se 1 (by rfl) ⟨757670, by rfl⟩ : syracuseStep 1010227 = 1515341) B1515341
theorem B2878051 : Blo 896573 2878051 := bstep (se 1 (by rfl) ⟨2158538, by rfl⟩ : syracuseStep 2878051 = 4317077) B4317077
theorem B2026097 : Blo 896573 2026097 := bstep (se 2 (by rfl) ⟨759786, by rfl⟩ : syracuseStep 2026097 = 1519573) B1519573
theorem B2026115 : Blo 896573 2026115 := bstep (se 1 (by rfl) ⟨1519586, by rfl⟩ : syracuseStep 2026115 = 3039173) B3039173
theorem B4549283 : Blo 896573 4549283 := bstep (se 1 (by rfl) ⟨3411962, by rfl⟩ : syracuseStep 4549283 = 6823925) B6823925
theorem B1010371 : Blo 896573 1010371 := bstep (se 1 (by rfl) ⟨757778, by rfl⟩ : syracuseStep 1010371 = 1515557) B1515557
theorem B5106509 : Blo 896573 5106509 := bstep (se 3 (by rfl) ⟨957470, by rfl⟩ : syracuseStep 5106509 = 1914941) B1914941
theorem B1010515 : Blo 896573 1010515 := bstep (se 1 (by rfl) ⟨757886, by rfl⟩ : syracuseStep 1010515 = 1515773) B1515773
theorem B3074989 : Blo 896573 3074989 := bstep (se 3 (by rfl) ⟨576560, by rfl⟩ : syracuseStep 3074989 = 1153121) B1153121
theorem B1010659 : Blo 896573 1010659 := bstep (se 1 (by rfl) ⟨757994, by rfl⟩ : syracuseStep 1010659 = 1515989) B1515989
theorem B11693069 : Blo 896573 11693069 := bstep (se 3 (by rfl) ⟨2192450, by rfl⟩ : syracuseStep 11693069 = 4384901) B4384901
theorem B1010803 : Blo 896573 1010803 := bstep (se 1 (by rfl) ⟨758102, by rfl⟩ : syracuseStep 1010803 = 1516205) B1516205
theorem B1010947 : Blo 896573 1010947 := bstep (se 1 (by rfl) ⟨758210, by rfl⟩ : syracuseStep 1010947 = 1516421) B1516421
theorem B1011091 : Blo 896573 1011091 := bstep (se 1 (by rfl) ⟨758318, by rfl⟩ : syracuseStep 1011091 = 1516637) B1516637
theorem B2158019 : Blo 896573 2158019 := bstep (se 1 (by rfl) ⟨1618514, by rfl⟩ : syracuseStep 2158019 = 3237029) B3237029
theorem B4550093 : Blo 896573 4550093 := bstep (se 3 (by rfl) ⟨853142, by rfl⟩ : syracuseStep 4550093 = 1706285) B1706285
theorem B1011235 : Blo 896573 1011235 := bstep (se 1 (by rfl) ⟨758426, by rfl⟩ : syracuseStep 1011235 = 1516853) B1516853
theorem B5762609 : Blo 896573 5762609 := bstep (se 2 (by rfl) ⟨2160978, by rfl⟩ : syracuseStep 5762609 = 4321957) B4321957
theorem B15330869 : Blo 896573 15330869 := bstep (se 5 (by rfl) ⟨718634, by rfl⟩ : syracuseStep 15330869 = 1437269) B1437269
theorem B10219121 : Blo 896573 10219121 := bstep (se 2 (by rfl) ⟨3832170, by rfl⟩ : syracuseStep 10219121 = 7664341) B7664341
theorem B2158211 : Blo 896573 2158211 := bstep (se 1 (by rfl) ⟨1618658, by rfl⟩ : syracuseStep 2158211 = 3237317) B3237317
theorem B1437347 : Blo 896573 1437347 := bstep (se 1 (by rfl) ⟨1078010, by rfl⟩ : syracuseStep 1437347 = 2156021) B2156021
theorem B1011379 : Blo 896573 1011379 := bstep (se 1 (by rfl) ⟨758534, by rfl⟩ : syracuseStep 1011379 = 1517069) B1517069
theorem B2158289 : Blo 896573 2158289 := bstep (se 2 (by rfl) ⟨809358, by rfl⟩ : syracuseStep 2158289 = 1618717) B1618717
theorem B1011523 : Blo 896573 1011523 := bstep (se 1 (by rfl) ⟨758642, by rfl⟩ : syracuseStep 1011523 = 1517285) B1517285
theorem B6156109 : Blo 896573 6156109 := bstep (se 3 (by rfl) ⟨1154270, by rfl⟩ : syracuseStep 6156109 = 2308541) B2308541
theorem B2158481 : Blo 896573 2158481 := bstep (se 2 (by rfl) ⟨809430, by rfl⟩ : syracuseStep 2158481 = 1618861) B1618861
theorem B1011667 : Blo 896573 1011667 := bstep (se 1 (by rfl) ⟨758750, by rfl⟩ : syracuseStep 1011667 = 1517501) B1517501
theorem B1437731 : Blo 896573 1437731 := bstep (se 1 (by rfl) ⟨1078298, by rfl⟩ : syracuseStep 1437731 = 2156597) B2156597
theorem B1011811 : Blo 896573 1011811 := bstep (se 1 (by rfl) ⟨758858, by rfl⟩ : syracuseStep 1011811 = 1517717) B1517717
theorem B4321421 : Blo 896573 4321421 := bstep (se 3 (by rfl) ⟨810266, by rfl⟩ : syracuseStep 4321421 = 1620533) B1620533
theorem B1437859 : Blo 896573 1437859 := bstep (se 1 (by rfl) ⟨1078394, by rfl⟩ : syracuseStep 1437859 = 2156789) B2156789
theorem B1011955 : Blo 896573 1011955 := bstep (se 1 (by rfl) ⟨758966, by rfl⟩ : syracuseStep 1011955 = 1517933) B1517933
theorem B4321649 : Blo 896573 4321649 := bstep (se 2 (by rfl) ⟨1620618, by rfl⟩ : syracuseStep 4321649 = 3241237) B3241237
theorem B2158979 : Blo 896573 2158979 := bstep (se 1 (by rfl) ⟨1619234, by rfl⟩ : syracuseStep 2158979 = 3238469) B3238469
theorem B1012099 : Blo 896573 1012099 := bstep (se 1 (by rfl) ⟨759074, by rfl⟩ : syracuseStep 1012099 = 1518149) B1518149
theorem B1077683 : Blo 896573 1077683 := bstep (se 1 (by rfl) ⟨808262, by rfl⟩ : syracuseStep 1077683 = 1616525) B1616525
theorem B2159057 : Blo 896573 2159057 := bstep (se 2 (by rfl) ⟨809646, by rfl⟩ : syracuseStep 2159057 = 1619293) B1619293
theorem B3076589 : Blo 896573 3076589 := bstep (se 3 (by rfl) ⟨576860, by rfl⟩ : syracuseStep 3076589 = 1153721) B1153721
theorem B3830257 : Blo 896573 3830257 := bstep (se 2 (by rfl) ⟨1436346, by rfl⟩ : syracuseStep 3830257 = 2872693) B2872693
theorem B1012243 : Blo 896573 1012243 := bstep (se 1 (by rfl) ⟨759182, by rfl⟩ : syracuseStep 1012243 = 1518365) B1518365
theorem B9826915 : Blo 896573 9826915 := bstep (se 1 (by rfl) ⟨7370186, by rfl⟩ : syracuseStep 9826915 = 14740373) B14740373
theorem B1012387 : Blo 896573 1012387 := bstep (se 1 (by rfl) ⟨759290, by rfl⟩ : syracuseStep 1012387 = 1518581) B1518581
theorem B2880269 : Blo 896573 2880269 := bstep (se 3 (by rfl) ⟨540050, by rfl⟩ : syracuseStep 2880269 = 1080101) B1080101
theorem B1012531 : Blo 896573 1012531 := bstep (se 1 (by rfl) ⟨759398, by rfl⟩ : syracuseStep 1012531 = 1518797) B1518797
theorem B2159441 : Blo 896573 2159441 := bstep (se 2 (by rfl) ⟨809790, by rfl⟩ : syracuseStep 2159441 = 1619581) B1619581
theorem B1438577 : Blo 896573 1438577 := bstep (se 2 (by rfl) ⟨539466, by rfl⟩ : syracuseStep 1438577 = 1078933) B1078933
theorem B1012675 : Blo 896573 1012675 := bstep (se 1 (by rfl) ⟨759506, by rfl⟩ : syracuseStep 1012675 = 1519013) B1519013
theorem B5108741 : Blo 896573 5108741 := bstep (se 4 (by rfl) ⟨478944, by rfl⟩ : syracuseStep 5108741 = 957889) B957889
theorem B1438769 : Blo 896573 1438769 := bstep (se 2 (by rfl) ⟨539538, by rfl⟩ : syracuseStep 1438769 = 1079077) B1079077
theorem B1012819 : Blo 896573 1012819 := bstep (se 1 (by rfl) ⟨759614, by rfl⟩ : syracuseStep 1012819 = 1519229) B1519229
theorem B2880689 : Blo 896573 2880689 := bstep (se 2 (by rfl) ⟨1080258, by rfl⟩ : syracuseStep 2880689 = 2160517) B2160517
theorem B1012963 : Blo 896573 1012963 := bstep (se 1 (by rfl) ⟨759722, by rfl⟩ : syracuseStep 1012963 = 1519445) B1519445
theorem B1013107 : Blo 896573 1013107 := bstep (se 1 (by rfl) ⟨759830, by rfl⟩ : syracuseStep 1013107 = 1519661) B1519661
theorem B12285553 : Blo 896573 12285553 := bstep (se 2 (by rfl) ⟨4607082, by rfl⟩ : syracuseStep 12285553 = 9214165) B9214165
theorem B3241613 : Blo 896573 3241613 := bstep (se 3 (by rfl) ⟨607802, by rfl⟩ : syracuseStep 3241613 = 1215605) B1215605
theorem B5109425 : Blo 896573 5109425 := bstep (se 2 (by rfl) ⟨1916034, by rfl⟩ : syracuseStep 5109425 = 3832069) B3832069
theorem B2553677 : Blo 896573 2553677 := bstep (se 3 (by rfl) ⟨478814, by rfl⟩ : syracuseStep 2553677 = 957629) B957629
theorem B7796621 : Blo 896573 7796621 := bstep (se 3 (by rfl) ⟨1461866, by rfl⟩ : syracuseStep 7796621 = 2923733) B2923733
theorem B5765069 : Blo 896573 5765069 := bstep (se 3 (by rfl) ⟨1080950, by rfl⟩ : syracuseStep 5765069 = 2161901) B2161901
theorem B2553869 : Blo 896573 2553869 := bstep (se 3 (by rfl) ⟨478850, by rfl⟩ : syracuseStep 2553869 = 957701) B957701
theorem B7665677 : Blo 896573 7665677 := bstep (se 3 (by rfl) ⟨1437314, by rfl⟩ : syracuseStep 7665677 = 2874629) B2874629
theorem B19429429 : Blo 896573 19429429 := bstep (se 5 (by rfl) ⟨910754, by rfl⟩ : syracuseStep 19429429 = 1821509) B1821509
theorem B3897485 : Blo 896573 3897485 := bstep (se 3 (by rfl) ⟨730778, by rfl⟩ : syracuseStep 3897485 = 1461557) B1461557
theorem B1702147 : Blo 896573 1702147 := bstep (se 1 (by rfl) ⟨1276610, by rfl⟩ : syracuseStep 1702147 = 2553221) B2553221
theorem B4553009 : Blo 896573 4553009 := bstep (se 2 (by rfl) ⟨1707378, by rfl⟩ : syracuseStep 4553009 = 3414757) B3414757
theorem B2161201 : Blo 896573 2161201 := bstep (se 2 (by rfl) ⟨810450, by rfl⟩ : syracuseStep 2161201 = 1620901) B1620901
theorem B3078755 : Blo 896573 3078755 := bstep (se 1 (by rfl) ⟨2309066, by rfl⟩ : syracuseStep 3078755 = 4618133) B4618133
theorem B1702595 : Blo 896573 1702595 := bstep (se 1 (by rfl) ⟨1276946, by rfl⟩ : syracuseStep 1702595 = 2553893) B2553893
theorem B1440499 : Blo 896573 1440499 := bstep (se 1 (by rfl) ⟨1080374, by rfl⟩ : syracuseStep 1440499 = 2160749) B2160749
theorem B1080067 : Blo 896573 1080067 := bstep (se 1 (by rfl) ⟨810050, by rfl⟩ : syracuseStep 1080067 = 1620101) B1620101
theorem B4324109 : Blo 896573 4324109 := bstep (se 3 (by rfl) ⟨810770, by rfl⟩ : syracuseStep 4324109 = 1621541) B1621541
theorem B1440595 : Blo 896573 1440595 := bstep (se 1 (by rfl) ⟨1080446, by rfl⟩ : syracuseStep 1440595 = 2160893) B2160893
theorem B1080163 : Blo 896573 1080163 := bstep (se 1 (by rfl) ⟨810122, by rfl⟩ : syracuseStep 1080163 = 1620245) B1620245
theorem B3406769 : Blo 896573 3406769 := bstep (se 2 (by rfl) ⟨1277538, by rfl⟩ : syracuseStep 3406769 = 2555077) B2555077
theorem B1702883 : Blo 896573 1702883 := bstep (se 1 (by rfl) ⟨1277162, by rfl⟩ : syracuseStep 1702883 = 2554325) B2554325
theorem B6814691 : Blo 896573 6814691 := bstep (se 1 (by rfl) ⟨5111018, by rfl⟩ : syracuseStep 6814691 = 10222037) B10222037
theorem B2554861 : Blo 896573 2554861 := bstep (se 3 (by rfl) ⟨479036, by rfl⟩ : syracuseStep 2554861 = 958073) B958073
theorem B1080307 : Blo 896573 1080307 := bstep (se 1 (by rfl) ⟨810230, by rfl⟩ : syracuseStep 1080307 = 1620461) B1620461
theorem B1440755 : Blo 896573 1440755 := bstep (se 1 (by rfl) ⟨1080566, by rfl⟩ : syracuseStep 1440755 = 2161133) B2161133
theorem B11500613 : Blo 896573 11500613 := bstep (se 4 (by rfl) ⟨1078182, by rfl⟩ : syracuseStep 11500613 = 2156365) B2156365
theorem B5110883 : Blo 896573 5110883 := bstep (se 1 (by rfl) ⟨3833162, by rfl⟩ : syracuseStep 5110883 = 7666325) B7666325
theorem B1277203 : Blo 896573 1277203 := bstep (se 1 (by rfl) ⟨957902, by rfl⟩ : syracuseStep 1277203 = 1915805) B1915805
theorem B1277299 : Blo 896573 1277299 := bstep (se 1 (by rfl) ⟨957974, by rfl⟩ : syracuseStep 1277299 = 1915949) B1915949
theorem B2424259 : Blo 896573 2424259 := bstep (se 1 (by rfl) ⟨1818194, by rfl⟩ : syracuseStep 2424259 = 3636389) B3636389
theorem B20708885 : Blo 896573 20708885 := bstep (se 6 (by rfl) ⟨485364, by rfl⟩ : syracuseStep 20708885 = 970729) B970729
theorem B4554467 : Blo 896573 4554467 := bstep (se 1 (by rfl) ⟨3415850, by rfl⟩ : syracuseStep 4554467 = 6831701) B6831701
theorem B1277795 : Blo 896573 1277795 := bstep (se 1 (by rfl) ⟨958346, by rfl⟩ : syracuseStep 1277795 = 1916693) B1916693
theorem B1703825 : Blo 896573 1703825 := bstep (se 2 (by rfl) ⟨638934, by rfl⟩ : syracuseStep 1703825 = 1277869) B1277869
theorem B1441729 : Blo 896573 1441729 := bstep (se 2 (by rfl) ⟨540648, by rfl⟩ : syracuseStep 1441729 = 1081297) B1081297
theorem B3244121 : Blo 896573 3244121 := bstep (se 2 (by rfl) ⟨1216545, by rfl⟩ : syracuseStep 3244121 = 2433091) B2433091
theorem B5111909 : Blo 896573 5111909 := bstep (se 4 (by rfl) ⟨479241, by rfl⟩ : syracuseStep 5111909 = 958483) B958483
theorem B52428941 : Blo 896573 52428941 := bstep (se 3 (by rfl) ⟨9830426, by rfl⟩ : syracuseStep 52428941 = 19660853) B19660853
theorem B1278347 : Blo 896573 1278347 := bstep (se 1 (by rfl) ⟨958760, by rfl⟩ : syracuseStep 1278347 = 1917521) B1917521
theorem B2556353 : Blo 896573 2556353 := bstep (se 2 (by rfl) ⟨958632, by rfl⟩ : syracuseStep 2556353 = 1917265) B1917265
theorem B1704395 : Blo 896573 1704395 := bstep (se 1 (by rfl) ⟨1278296, by rfl⟩ : syracuseStep 1704395 = 2556593) B2556593
theorem B16417241 : Blo 896573 16417241 := bstep (se 2 (by rfl) ⟨6156465, by rfl⟩ : syracuseStep 16417241 = 12312931) B12312931
theorem B2884061 : Blo 896573 2884061 := bstep (se 3 (by rfl) ⟨540761, by rfl⟩ : syracuseStep 2884061 = 1081523) B1081523
theorem B2556467 : Blo 896573 2556467 := bstep (se 1 (by rfl) ⟨1917350, by rfl⟩ : syracuseStep 2556467 = 3834701) B3834701
theorem B1704577 : Blo 896573 1704577 := bstep (se 2 (by rfl) ⟨639216, by rfl⟩ : syracuseStep 1704577 = 1278433) B1278433
theorem B1639283 : Blo 896573 1639283 := bstep (se 1 (by rfl) ⟨1229462, by rfl⟩ : syracuseStep 1639283 = 2458925) B2458925
theorem B3834803 : Blo 896573 3834803 := bstep (se 1 (by rfl) ⟨2876102, by rfl⟩ : syracuseStep 3834803 = 5752205) B5752205
theorem B1705025 : Blo 896573 1705025 := bstep (se 2 (by rfl) ⟨639384, by rfl⟩ : syracuseStep 1705025 = 1278769) B1278769
theorem B6489163 : Blo 896573 6489163 := bstep (se 1 (by rfl) ⟨4866872, by rfl⟩ : syracuseStep 6489163 = 9733745) B9733745
theorem B1705367 : Blo 896573 1705367 := bstep (se 1 (by rfl) ⟨1279025, by rfl⟩ : syracuseStep 1705367 = 2558051) B2558051
theorem B1344971 : Blo 896573 1344971 := bstep (se 1 (by rfl) ⟨1008728, by rfl⟩ : syracuseStep 1344971 = 2017457) B2017457
theorem B1344983 : Blo 896573 1344983 := bstep (se 1 (by rfl) ⟨1008737, by rfl⟩ : syracuseStep 1344983 = 2017475) B2017475
theorem B4556249 : Blo 896573 4556249 := bstep (se 2 (by rfl) ⟨1708593, by rfl⟩ : syracuseStep 4556249 = 3417187) B3417187
theorem B3409411 : Blo 896573 3409411 := bstep (se 1 (by rfl) ⟨2557058, by rfl⟩ : syracuseStep 3409411 = 5114117) B5114117
theorem B1345049 : Blo 896573 1345049 := bstep (se 2 (by rfl) ⟨504393, by rfl⟩ : syracuseStep 1345049 = 1008787) B1008787
theorem B1345163 : Blo 896573 1345163 := bstep (se 1 (by rfl) ⟨1008872, by rfl⟩ : syracuseStep 1345163 = 2017745) B2017745
theorem B1345175 : Blo 896573 1345175 := bstep (se 1 (by rfl) ⟨1008881, by rfl⟩ : syracuseStep 1345175 = 2017763) B2017763
theorem B1345241 : Blo 896573 1345241 := bstep (se 2 (by rfl) ⟨504465, by rfl⟩ : syracuseStep 1345241 = 1008931) B1008931
theorem B3409715 : Blo 896573 3409715 := bstep (se 1 (by rfl) ⟨2557286, by rfl⟩ : syracuseStep 3409715 = 5114573) B5114573
theorem B1345355 : Blo 896573 1345355 := bstep (se 1 (by rfl) ⟨1009016, by rfl⟩ : syracuseStep 1345355 = 2018033) B2018033
theorem B7374667 : Blo 896573 7374667 := bstep (se 1 (by rfl) ⟨5531000, by rfl⟩ : syracuseStep 7374667 = 11062001) B11062001
theorem B1345367 : Blo 896573 1345367 := bstep (se 1 (by rfl) ⟨1009025, by rfl⟩ : syracuseStep 1345367 = 2018051) B2018051
theorem B1345433 : Blo 896573 1345433 := bstep (se 2 (by rfl) ⟨504537, by rfl⟩ : syracuseStep 1345433 = 1009075) B1009075
theorem B1345547 : Blo 896573 1345547 := bstep (se 1 (by rfl) ⟨1009160, by rfl⟩ : syracuseStep 1345547 = 2018321) B2018321
theorem B1345559 : Blo 896573 1345559 := bstep (se 1 (by rfl) ⟨1009169, by rfl⟩ : syracuseStep 1345559 = 2018339) B2018339
theorem B1706035 : Blo 896573 1706035 := bstep (se 1 (by rfl) ⟨1279526, by rfl⟩ : syracuseStep 1706035 = 2559053) B2559053
theorem B1345625 : Blo 896573 1345625 := bstep (se 2 (by rfl) ⟨504609, by rfl⟩ : syracuseStep 1345625 = 1009219) B1009219
theorem B6490205 : Blo 896573 6490205 := bstep (se 3 (by rfl) ⟨1216913, by rfl⟩ : syracuseStep 6490205 = 2433827) B2433827
theorem B1345739 : Blo 896573 1345739 := bstep (se 1 (by rfl) ⟨1009304, by rfl⟩ : syracuseStep 1345739 = 2018609) B2018609
theorem B4098251 : Blo 896573 4098251 := bstep (se 1 (by rfl) ⟨3073688, by rfl⟩ : syracuseStep 4098251 = 6147377) B6147377
theorem B1345751 : Blo 896573 1345751 := bstep (se 1 (by rfl) ⟨1009313, by rfl⟩ : syracuseStep 1345751 = 2018627) B2018627
theorem B1280215 : Blo 896573 1280215 := bstep (se 1 (by rfl) ⟨960161, by rfl⟩ : syracuseStep 1280215 = 1920323) B1920323
theorem B1345817 : Blo 896573 1345817 := bstep (se 2 (by rfl) ⟨504681, by rfl⟩ : syracuseStep 1345817 = 1009363) B1009363
theorem B7670051 : Blo 896573 7670051 := bstep (se 1 (by rfl) ⟨5752538, by rfl⟩ : syracuseStep 7670051 = 11505077) B11505077
theorem B6818093 : Blo 896573 6818093 := bstep (se 3 (by rfl) ⟨1278392, by rfl⟩ : syracuseStep 6818093 = 2556785) B2556785
theorem B1345931 : Blo 896573 1345931 := bstep (se 1 (by rfl) ⟨1009448, by rfl⟩ : syracuseStep 1345931 = 2018897) B2018897
theorem B1345943 : Blo 896573 1345943 := bstep (se 1 (by rfl) ⟨1009457, by rfl⟩ : syracuseStep 1345943 = 2018915) B2018915
theorem B3410369 : Blo 896573 3410369 := bstep (se 2 (by rfl) ⟨1278888, by rfl⟩ : syracuseStep 3410369 = 2557777) B2557777
theorem B1346009 : Blo 896573 1346009 := bstep (se 2 (by rfl) ⟨504753, by rfl⟩ : syracuseStep 1346009 = 1009507) B1009507
theorem B1706483 : Blo 896573 1706483 := bstep (se 1 (by rfl) ⟨1279862, by rfl⟩ : syracuseStep 1706483 = 2559725) B2559725
theorem B1706521 : Blo 896573 1706521 := bstep (se 2 (by rfl) ⟨639945, by rfl⟩ : syracuseStep 1706521 = 1279891) B1279891
theorem B1346123 : Blo 896573 1346123 := bstep (se 1 (by rfl) ⟨1009592, by rfl⟩ : syracuseStep 1346123 = 2019185) B2019185
theorem B1346135 : Blo 896573 1346135 := bstep (se 1 (by rfl) ⟨1009601, by rfl⟩ : syracuseStep 1346135 = 2019203) B2019203
theorem B1346201 : Blo 896573 1346201 := bstep (se 2 (by rfl) ⟨504825, by rfl⟩ : syracuseStep 1346201 = 1009651) B1009651
theorem B1870489 : Blo 896573 1870489 := bstep (se 2 (by rfl) ⟨701433, by rfl⟩ : syracuseStep 1870489 = 1402867) B1402867
theorem B1346315 : Blo 896573 1346315 := bstep (se 1 (by rfl) ⟨1009736, by rfl⟩ : syracuseStep 1346315 = 2019473) B2019473
theorem B1346327 : Blo 896573 1346327 := bstep (se 1 (by rfl) ⟨1009745, by rfl⟩ : syracuseStep 1346327 = 2019491) B2019491
theorem B3836717 : Blo 896573 3836717 := bstep (se 3 (by rfl) ⟨719384, by rfl⟩ : syracuseStep 3836717 = 1438769) B1438769
theorem B1346393 : Blo 896573 1346393 := bstep (se 2 (by rfl) ⟨504897, by rfl⟩ : syracuseStep 1346393 = 1009795) B1009795
theorem B1346507 : Blo 896573 1346507 := bstep (se 1 (by rfl) ⟨1009880, by rfl⟩ : syracuseStep 1346507 = 2019761) B2019761
theorem B1346519 : Blo 896573 1346519 := bstep (se 1 (by rfl) ⟨1009889, by rfl⟩ : syracuseStep 1346519 = 2019779) B2019779
theorem B1706969 : Blo 896573 1706969 := bstep (se 2 (by rfl) ⟨640113, by rfl⟩ : syracuseStep 1706969 = 1280227) B1280227
theorem B1346585 : Blo 896573 1346585 := bstep (se 2 (by rfl) ⟨504969, by rfl⟩ : syracuseStep 1346585 = 1009939) B1009939
theorem B4557869 : Blo 896573 4557869 := bstep (se 3 (by rfl) ⟨854600, by rfl⟩ : syracuseStep 4557869 = 1709201) B1709201
theorem B1346699 : Blo 896573 1346699 := bstep (se 1 (by rfl) ⟨1010024, by rfl⟩ : syracuseStep 1346699 = 2020049) B2020049
theorem B1346711 : Blo 896573 1346711 := bstep (se 1 (by rfl) ⟨1010033, by rfl⟩ : syracuseStep 1346711 = 2020067) B2020067
theorem B1346777 : Blo 896573 1346777 := bstep (se 2 (by rfl) ⟨505041, by rfl⟩ : syracuseStep 1346777 = 1010083) B1010083
theorem B1215767 : Blo 896573 1215767 := bstep (se 1 (by rfl) ⟨911825, by rfl⟩ : syracuseStep 1215767 = 1823651) B1823651
theorem B1346891 : Blo 896573 1346891 := bstep (se 1 (by rfl) ⟨1010168, by rfl⟩ : syracuseStep 1346891 = 2020337) B2020337
theorem B1346903 : Blo 896573 1346903 := bstep (se 1 (by rfl) ⟨1010177, by rfl⟩ : syracuseStep 1346903 = 2020355) B2020355
theorem B2559383 : Blo 896573 2559383 := bstep (se 1 (by rfl) ⟨1919537, by rfl⟩ : syracuseStep 2559383 = 3839075) B3839075
theorem B1346969 : Blo 896573 1346969 := bstep (se 2 (by rfl) ⟨505113, by rfl⟩ : syracuseStep 1346969 = 1010227) B1010227
theorem B3837401 : Blo 896573 3837401 := bstep (se 2 (by rfl) ⟨1439025, by rfl⟩ : syracuseStep 3837401 = 2878051) B2878051
theorem B1347083 : Blo 896573 1347083 := bstep (se 1 (by rfl) ⟨1010312, by rfl⟩ : syracuseStep 1347083 = 2020625) B2020625
theorem B1347095 : Blo 896573 1347095 := bstep (se 1 (by rfl) ⟨1010321, by rfl⟩ : syracuseStep 1347095 = 2020643) B2020643
theorem B1347161 : Blo 896573 1347161 := bstep (se 2 (by rfl) ⟨505185, by rfl⟩ : syracuseStep 1347161 = 1010371) B1010371
theorem B3411629 : Blo 896573 3411629 := bstep (se 3 (by rfl) ⟨639680, by rfl⟩ : syracuseStep 3411629 = 1279361) B1279361
theorem B1707713 : Blo 896573 1707713 := bstep (se 2 (by rfl) ⟨640392, by rfl⟩ : syracuseStep 1707713 = 1280785) B1280785
theorem B1347275 : Blo 896573 1347275 := bstep (se 1 (by rfl) ⟨1010456, by rfl⟩ : syracuseStep 1347275 = 2020913) B2020913
theorem B3411659 : Blo 896573 3411659 := bstep (se 1 (by rfl) ⟨2558744, by rfl⟩ : syracuseStep 3411659 = 5117489) B5117489
theorem B1347287 : Blo 896573 1347287 := bstep (se 1 (by rfl) ⟨1010465, by rfl⟩ : syracuseStep 1347287 = 2020931) B2020931
theorem B1969921 : Blo 896573 1969921 := bstep (se 2 (by rfl) ⟨738720, by rfl⟩ : syracuseStep 1969921 = 1477441) B1477441
theorem B1347353 : Blo 896573 1347353 := bstep (se 2 (by rfl) ⟨505257, by rfl⟩ : syracuseStep 1347353 = 1010515) B1010515
theorem B1347467 : Blo 896573 1347467 := bstep (se 1 (by rfl) ⟨1010600, by rfl⟩ : syracuseStep 1347467 = 2021201) B2021201
theorem B4099985 : Blo 896573 4099985 := bstep (se 2 (by rfl) ⟨1537494, by rfl⟩ : syracuseStep 4099985 = 3074989) B3074989
theorem B1347479 : Blo 896573 1347479 := bstep (se 1 (by rfl) ⟨1010609, by rfl⟩ : syracuseStep 1347479 = 2021219) B2021219
theorem B1707979 : Blo 896573 1707979 := bstep (se 1 (by rfl) ⟨1280984, by rfl⟩ : syracuseStep 1707979 = 2561969) B2561969
theorem B1347545 : Blo 896573 1347545 := bstep (se 2 (by rfl) ⟨505329, by rfl⟩ : syracuseStep 1347545 = 1010659) B1010659
theorem B1347659 : Blo 896573 1347659 := bstep (se 1 (by rfl) ⟨1010744, by rfl⟩ : syracuseStep 1347659 = 2021489) B2021489
theorem B1347671 : Blo 896573 1347671 := bstep (se 1 (by rfl) ⟨1010753, by rfl⟩ : syracuseStep 1347671 = 2021507) B2021507
theorem B1347737 : Blo 896573 1347737 := bstep (se 2 (by rfl) ⟨505401, by rfl⟩ : syracuseStep 1347737 = 1010803) B1010803
theorem B1347851 : Blo 896573 1347851 := bstep (se 1 (by rfl) ⟨1010888, by rfl⟩ : syracuseStep 1347851 = 2021777) B2021777
theorem B1347863 : Blo 896573 1347863 := bstep (se 1 (by rfl) ⟨1010897, by rfl⟩ : syracuseStep 1347863 = 2021795) B2021795
theorem B1347929 : Blo 896573 1347929 := bstep (se 2 (by rfl) ⟨505473, by rfl⟩ : syracuseStep 1347929 = 1010947) B1010947
theorem B3412313 : Blo 896573 3412313 := bstep (se 2 (by rfl) ⟨1279617, by rfl⟩ : syracuseStep 3412313 = 2559235) B2559235
theorem B17305973 : Blo 896573 17305973 := bstep (se 5 (by rfl) ⟨811217, by rfl⟩ : syracuseStep 17305973 = 1622435) B1622435
theorem B1708427 : Blo 896573 1708427 := bstep (se 1 (by rfl) ⟨1281320, by rfl⟩ : syracuseStep 1708427 = 2562641) B2562641
theorem B1348043 : Blo 896573 1348043 := bstep (se 1 (by rfl) ⟨1011032, by rfl⟩ : syracuseStep 1348043 = 2022065) B2022065
theorem B1348055 : Blo 896573 1348055 := bstep (se 1 (by rfl) ⟨1011041, by rfl⟩ : syracuseStep 1348055 = 2022083) B2022083
theorem B1348121 : Blo 896573 1348121 := bstep (se 2 (by rfl) ⟨505545, by rfl⟩ : syracuseStep 1348121 = 1011091) B1011091
theorem B1708609 : Blo 896573 1708609 := bstep (se 2 (by rfl) ⟨640728, by rfl⟩ : syracuseStep 1708609 = 1281457) B1281457
theorem B2921035 : Blo 896573 2921035 := bstep (se 1 (by rfl) ⟨2190776, by rfl⟩ : syracuseStep 2921035 = 4381553) B4381553
theorem B1348235 : Blo 896573 1348235 := bstep (se 1 (by rfl) ⟨1011176, by rfl⟩ : syracuseStep 1348235 = 2022353) B2022353
theorem B3412631 : Blo 896573 3412631 := bstep (se 1 (by rfl) ⟨2559473, by rfl⟩ : syracuseStep 3412631 = 5118947) B5118947
theorem B1348247 : Blo 896573 1348247 := bstep (se 1 (by rfl) ⟨1011185, by rfl⟩ : syracuseStep 1348247 = 2022371) B2022371
theorem B1348313 : Blo 896573 1348313 := bstep (se 2 (by rfl) ⟨505617, by rfl⟩ : syracuseStep 1348313 = 1011235) B1011235
theorem B1348427 : Blo 896573 1348427 := bstep (se 1 (by rfl) ⟨1011320, by rfl⟩ : syracuseStep 1348427 = 2022641) B2022641
theorem B1348439 : Blo 896573 1348439 := bstep (se 1 (by rfl) ⟨1011329, by rfl⟩ : syracuseStep 1348439 = 2022659) B2022659
theorem B1708951 : Blo 896573 1708951 := bstep (se 1 (by rfl) ⟨1281713, by rfl⟩ : syracuseStep 1708951 = 2563427) B2563427
theorem B1348505 : Blo 896573 1348505 := bstep (se 2 (by rfl) ⟨505689, by rfl⟩ : syracuseStep 1348505 = 1011379) B1011379
theorem B1348619 : Blo 896573 1348619 := bstep (se 1 (by rfl) ⟨1011464, by rfl⟩ : syracuseStep 1348619 = 2022929) B2022929
theorem B1348631 : Blo 896573 1348631 := bstep (se 1 (by rfl) ⟨1011473, by rfl⟩ : syracuseStep 1348631 = 2022947) B2022947
theorem B1348697 : Blo 896573 1348697 := bstep (se 2 (by rfl) ⟨505761, by rfl⟩ : syracuseStep 1348697 = 1011523) B1011523
theorem B1709171 : Blo 896573 1709171 := bstep (se 1 (by rfl) ⟨1281878, by rfl⟩ : syracuseStep 1709171 = 2563757) B2563757
theorem B4854935 : Blo 896573 4854935 := bstep (se 1 (by rfl) ⟨3641201, by rfl⟩ : syracuseStep 4854935 = 7282403) B7282403
theorem B1348811 : Blo 896573 1348811 := bstep (se 1 (by rfl) ⟨1011608, by rfl⟩ : syracuseStep 1348811 = 2023217) B2023217
theorem B1348823 : Blo 896573 1348823 := bstep (se 1 (by rfl) ⟨1011617, by rfl⟩ : syracuseStep 1348823 = 2023235) B2023235
theorem B2954519 : Blo 896573 2954519 := bstep (se 1 (by rfl) ⟨2215889, by rfl⟩ : syracuseStep 2954519 = 4431779) B4431779
theorem B1348889 : Blo 896573 1348889 := bstep (se 2 (by rfl) ⟨505833, by rfl⟩ : syracuseStep 1348889 = 1011667) B1011667
theorem B3413299 : Blo 896573 3413299 := bstep (se 1 (by rfl) ⟨2559974, by rfl⟩ : syracuseStep 3413299 = 5119949) B5119949
theorem B1709399 : Blo 896573 1709399 := bstep (se 1 (by rfl) ⟨1282049, by rfl⟩ : syracuseStep 1709399 = 2564099) B2564099
theorem B1349003 : Blo 896573 1349003 := bstep (se 1 (by rfl) ⟨1011752, by rfl⟩ : syracuseStep 1349003 = 2023505) B2023505
theorem B1349015 : Blo 896573 1349015 := bstep (se 1 (by rfl) ⟨1011761, by rfl⟩ : syracuseStep 1349015 = 2023523) B2023523
theorem B1349081 : Blo 896573 1349081 := bstep (se 2 (by rfl) ⟨505905, by rfl⟩ : syracuseStep 1349081 = 1011811) B1011811
theorem B1512985 : Blo 896573 1512985 := bstep (se 2 (by rfl) ⟨567369, by rfl⟩ : syracuseStep 1512985 = 1134739) B1134739
theorem B1349195 : Blo 896573 1349195 := bstep (se 1 (by rfl) ⟨1011896, by rfl⟩ : syracuseStep 1349195 = 2023793) B2023793
theorem B1349207 : Blo 896573 1349207 := bstep (se 1 (by rfl) ⟨1011905, by rfl⟩ : syracuseStep 1349207 = 2023811) B2023811
theorem B1709657 : Blo 896573 1709657 := bstep (se 2 (by rfl) ⟨641121, by rfl⟩ : syracuseStep 1709657 = 1282243) B1282243
theorem B1349273 : Blo 896573 1349273 := bstep (se 2 (by rfl) ⟨505977, by rfl⟩ : syracuseStep 1349273 = 1011955) B1011955
theorem B1349387 : Blo 896573 1349387 := bstep (se 1 (by rfl) ⟨1012040, by rfl⟩ : syracuseStep 1349387 = 2024081) B2024081
theorem B1349399 : Blo 896573 1349399 := bstep (se 1 (by rfl) ⟨1012049, by rfl⟩ : syracuseStep 1349399 = 2024099) B2024099
theorem B5117741 : Blo 896573 5117741 := bstep (se 3 (by rfl) ⟨959576, by rfl⟩ : syracuseStep 5117741 = 1919153) B1919153
theorem B2561843 : Blo 896573 2561843 := bstep (se 1 (by rfl) ⟨1921382, by rfl⟩ : syracuseStep 2561843 = 3842765) B3842765
theorem B1349465 : Blo 896573 1349465 := bstep (se 2 (by rfl) ⟨506049, by rfl⟩ : syracuseStep 1349465 = 1012099) B1012099
theorem B1349579 : Blo 896573 1349579 := bstep (se 1 (by rfl) ⟨1012184, by rfl⟩ : syracuseStep 1349579 = 2024369) B2024369
theorem B1349591 : Blo 896573 1349591 := bstep (se 1 (by rfl) ⟨1012193, by rfl⟩ : syracuseStep 1349591 = 2024387) B2024387
theorem B1349657 : Blo 896573 1349657 := bstep (se 2 (by rfl) ⟨506121, by rfl⟩ : syracuseStep 1349657 = 1012243) B1012243
theorem B1513559 : Blo 896573 1513559 := bstep (se 1 (by rfl) ⟨1135169, by rfl⟩ : syracuseStep 1513559 = 2270339) B2270339
theorem B6821981 : Blo 896573 6821981 := bstep (se 3 (by rfl) ⟨1279121, by rfl⟩ : syracuseStep 6821981 = 2558243) B2558243
theorem B1349771 : Blo 896573 1349771 := bstep (se 1 (by rfl) ⟨1012328, by rfl⟩ : syracuseStep 1349771 = 2024657) B2024657
theorem B1349783 : Blo 896573 1349783 := bstep (se 1 (by rfl) ⟨1012337, by rfl⟩ : syracuseStep 1349783 = 2024675) B2024675
theorem B12982477 : Blo 896573 12982477 := bstep (se 3 (by rfl) ⟨2434214, by rfl⟩ : syracuseStep 12982477 = 4868429) B4868429
theorem B1513687 : Blo 896573 1513687 := bstep (se 1 (by rfl) ⟨1135265, by rfl⟩ : syracuseStep 1513687 = 2270531) B2270531
theorem B1349849 : Blo 896573 1349849 := bstep (se 2 (by rfl) ⟨506193, by rfl⟩ : syracuseStep 1349849 = 1012387) B1012387
theorem B1349963 : Blo 896573 1349963 := bstep (se 1 (by rfl) ⟨1012472, by rfl⟩ : syracuseStep 1349963 = 2024945) B2024945
theorem B1349975 : Blo 896573 1349975 := bstep (se 1 (by rfl) ⟨1012481, by rfl⟩ : syracuseStep 1349975 = 2024963) B2024963
theorem B1350041 : Blo 896573 1350041 := bstep (se 2 (by rfl) ⟨506265, by rfl⟩ : syracuseStep 1350041 = 1012531) B1012531
theorem B4004275 : Blo 896573 4004275 := bstep (se 1 (by rfl) ⟨3003206, by rfl⟩ : syracuseStep 4004275 = 6006413) B6006413
theorem B1350155 : Blo 896573 1350155 := bstep (se 1 (by rfl) ⟨1012616, by rfl⟩ : syracuseStep 1350155 = 2025233) B2025233
theorem B3414545 : Blo 896573 3414545 := bstep (se 2 (by rfl) ⟨1280454, by rfl⟩ : syracuseStep 3414545 = 2560909) B2560909
theorem B1350167 : Blo 896573 1350167 := bstep (se 1 (by rfl) ⟨1012625, by rfl⟩ : syracuseStep 1350167 = 2025251) B2025251
theorem B2431577 : Blo 896573 2431577 := bstep (se 2 (by rfl) ⟨911841, by rfl⟩ : syracuseStep 2431577 = 1823683) B1823683
theorem B1350233 : Blo 896573 1350233 := bstep (se 2 (by rfl) ⟨506337, by rfl⟩ : syracuseStep 1350233 = 1012675) B1012675
theorem B1350347 : Blo 896573 1350347 := bstep (se 1 (by rfl) ⟨1012760, by rfl⟩ : syracuseStep 1350347 = 2025521) B2025521
theorem B1350359 : Blo 896573 1350359 := bstep (se 1 (by rfl) ⟨1012769, by rfl⟩ : syracuseStep 1350359 = 2025539) B2025539
theorem B1350425 : Blo 896573 1350425 := bstep (se 2 (by rfl) ⟨506409, by rfl⟩ : syracuseStep 1350425 = 1012819) B1012819
theorem B1514315 : Blo 896573 1514315 := bstep (se 1 (by rfl) ⟨1135736, by rfl⟩ : syracuseStep 1514315 = 2271473) B2271473
theorem B1350539 : Blo 896573 1350539 := bstep (se 1 (by rfl) ⟨1012904, by rfl⟩ : syracuseStep 1350539 = 2025809) B2025809
theorem B1973143 : Blo 896573 1973143 := bstep (se 1 (by rfl) ⟨1479857, by rfl⟩ : syracuseStep 1973143 = 2959715) B2959715
theorem B1350551 : Blo 896573 1350551 := bstep (se 1 (by rfl) ⟨1012913, by rfl⟩ : syracuseStep 1350551 = 2025827) B2025827
theorem B1514443 : Blo 896573 1514443 := bstep (se 1 (by rfl) ⟨1135832, by rfl⟩ : syracuseStep 1514443 = 2271665) B2271665
theorem B1350617 : Blo 896573 1350617 := bstep (se 2 (by rfl) ⟨506481, by rfl⟩ : syracuseStep 1350617 = 1012963) B1012963
theorem B1350731 : Blo 896573 1350731 := bstep (se 1 (by rfl) ⟨1013048, by rfl⟩ : syracuseStep 1350731 = 2026097) B2026097
theorem B1350743 : Blo 896573 1350743 := bstep (se 1 (by rfl) ⟨1013057, by rfl⟩ : syracuseStep 1350743 = 2026115) B2026115
theorem B1514585 : Blo 896573 1514585 := bstep (se 2 (by rfl) ⟨567969, by rfl⟩ : syracuseStep 1514585 = 1135939) B1135939
theorem B1350809 : Blo 896573 1350809 := bstep (se 2 (by rfl) ⟨506553, by rfl⟩ : syracuseStep 1350809 = 1013107) B1013107
theorem B3415243 : Blo 896573 3415243 := bstep (se 1 (by rfl) ⟨2561432, by rfl⟩ : syracuseStep 3415243 = 5122865) B5122865
theorem B1514713 : Blo 896573 1514713 := bstep (se 2 (by rfl) ⟨568017, by rfl⟩ : syracuseStep 1514713 = 1136035) B1136035
theorem B3415517 : Blo 896573 3415517 := bstep (se 3 (by rfl) ⟨640409, by rfl⟩ : syracuseStep 3415517 = 1280819) B1280819
theorem B3841739 : Blo 896573 3841739 := bstep (se 1 (by rfl) ⟨2881304, by rfl⟩ : syracuseStep 3841739 = 5762609) B5762609
theorem B958231 : Blo 896573 958231 := bstep (se 1 (by rfl) ⟨718673, by rfl⟩ : syracuseStep 958231 = 1437347) B1437347
theorem B1515287 : Blo 896573 1515287 := bstep (se 1 (by rfl) ⟨1136465, by rfl⟩ : syracuseStep 1515287 = 2272931) B2272931
theorem B1515415 : Blo 896573 1515415 := bstep (se 1 (by rfl) ⟨1136561, by rfl⟩ : syracuseStep 1515415 = 2273123) B2273123
theorem B958487 : Blo 896573 958487 := bstep (se 1 (by rfl) ⟨718865, by rfl⟩ : syracuseStep 958487 = 1437731) B1437731
theorem B5120131 : Blo 896573 5120131 := bstep (se 1 (by rfl) ⟨3840098, by rfl⟩ : syracuseStep 5120131 = 7680197) B7680197
theorem B3416215 : Blo 896573 3416215 := bstep (se 1 (by rfl) ⟨2562161, by rfl⟩ : syracuseStep 3416215 = 5124323) B5124323
theorem B2728129 : Blo 896573 2728129 := bstep (se 2 (by rfl) ⟨1023048, by rfl⟩ : syracuseStep 2728129 = 2046097) B2046097
theorem B2269529 : Blo 896573 2269529 := bstep (se 2 (by rfl) ⟨851073, by rfl⟩ : syracuseStep 2269529 = 1702147) B1702147
theorem B10232243 : Blo 896573 10232243 := bstep (se 1 (by rfl) ⟨7674182, by rfl⟩ : syracuseStep 10232243 = 15348365) B15348365
theorem B1516043 : Blo 896573 1516043 := bstep (se 1 (by rfl) ⟨1137032, by rfl⟩ : syracuseStep 1516043 = 2274065) B2274065
theorem B959051 : Blo 896573 959051 := bstep (se 1 (by rfl) ⟨719288, by rfl⟩ : syracuseStep 959051 = 1438577) B1438577
theorem B1516171 : Blo 896573 1516171 := bstep (se 1 (by rfl) ⟨1137128, by rfl⟩ : syracuseStep 1516171 = 2274257) B2274257
theorem B1516313 : Blo 896573 1516313 := bstep (se 2 (by rfl) ⟨568617, by rfl⟩ : syracuseStep 1516313 = 1137235) B1137235
theorem B1516441 : Blo 896573 1516441 := bstep (se 2 (by rfl) ⟨568665, by rfl⟩ : syracuseStep 1516441 = 1137331) B1137331
theorem B3417005 : Blo 896573 3417005 := bstep (se 3 (by rfl) ⟨640688, by rfl⟩ : syracuseStep 3417005 = 1281377) B1281377
theorem B5121089 : Blo 896573 5121089 := bstep (se 2 (by rfl) ⟨1920408, by rfl⟩ : syracuseStep 5121089 = 3840817) B3840817
theorem B3843379 : Blo 896573 3843379 := bstep (se 1 (by rfl) ⟨2882534, by rfl⟩ : syracuseStep 3843379 = 5765069) B5765069
theorem B2598323 : Blo 896573 2598323 := bstep (se 1 (by rfl) ⟨1948742, by rfl⟩ : syracuseStep 2598323 = 3897485) B3897485
theorem B1517015 : Blo 896573 1517015 := bstep (se 1 (by rfl) ⟨1137761, by rfl⟩ : syracuseStep 1517015 = 2275523) B2275523
theorem B7284289 : Blo 896573 7284289 := bstep (se 2 (by rfl) ⟨2731608, by rfl⟩ : syracuseStep 7284289 = 5463217) B5463217
theorem B1517143 : Blo 896573 1517143 := bstep (se 1 (by rfl) ⟨1137857, by rfl⟩ : syracuseStep 1517143 = 2275715) B2275715
theorem B14559041 : Blo 896573 14559041 := bstep (se 2 (by rfl) ⟨5459640, by rfl⟩ : syracuseStep 14559041 = 10919281) B10919281
theorem B10233701 : Blo 896573 10233701 := bstep (se 4 (by rfl) ⟨959409, by rfl⟩ : syracuseStep 10233701 = 1918819) B1918819
theorem B9348965 : Blo 896573 9348965 := bstep (se 4 (by rfl) ⟨876465, by rfl⟩ : syracuseStep 9348965 = 1752931) B1752931
theorem B2271179 : Blo 896573 2271179 := bstep (se 1 (by rfl) ⟨1703384, by rfl⟩ : syracuseStep 2271179 = 3406769) B3406769
theorem B960503 : Blo 896573 960503 := bstep (se 1 (by rfl) ⟨720377, by rfl⟩ : syracuseStep 960503 = 1440755) B1440755
theorem B5187685 : Blo 896573 5187685 := bstep (se 4 (by rfl) ⟨486345, by rfl⟩ : syracuseStep 5187685 = 972691) B972691
theorem B1386647 : Blo 896573 1386647 := bstep (se 1 (by rfl) ⟨1039985, by rfl⟩ : syracuseStep 1386647 = 2079971) B2079971
theorem B1517771 : Blo 896573 1517771 := bstep (se 1 (by rfl) ⟨1138328, by rfl⟩ : syracuseStep 1517771 = 2276657) B2276657
theorem B3418433 : Blo 896573 3418433 := bstep (se 2 (by rfl) ⟨1281912, by rfl⟩ : syracuseStep 3418433 = 2563825) B2563825
theorem B1517899 : Blo 896573 1517899 := bstep (se 1 (by rfl) ⟨1138424, by rfl⟩ : syracuseStep 1517899 = 2276849) B2276849
theorem B13805923 : Blo 896573 13805923 := bstep (se 1 (by rfl) ⟨10354442, by rfl⟩ : syracuseStep 13805923 = 20708885) B20708885
theorem B1518041 : Blo 896573 1518041 := bstep (se 2 (by rfl) ⟨569265, by rfl⟩ : syracuseStep 1518041 = 1138531) B1138531
theorem B16362053 : Blo 896573 16362053 := bstep (se 4 (by rfl) ⟨1533942, by rfl⟩ : syracuseStep 16362053 = 3067885) B3067885
theorem B1518169 : Blo 896573 1518169 := bstep (se 2 (by rfl) ⟨569313, by rfl⟩ : syracuseStep 1518169 = 1138627) B1138627
theorem B3844867 : Blo 896573 3844867 := bstep (se 1 (by rfl) ⟨2883650, by rfl⟩ : syracuseStep 3844867 = 5767301) B5767301
theorem B1944395 : Blo 896573 1944395 := bstep (se 1 (by rfl) ⟨1458296, by rfl⟩ : syracuseStep 1944395 = 2916593) B2916593
theorem B2272151 : Blo 896573 2272151 := bstep (se 1 (by rfl) ⟨1704113, by rfl⟩ : syracuseStep 2272151 = 3408227) B3408227
theorem B1616843 : Blo 896573 1616843 := bstep (se 1 (by rfl) ⟨1212632, by rfl⟩ : syracuseStep 1616843 = 2425265) B2425265
theorem B6138841 : Blo 896573 6138841 := bstep (se 2 (by rfl) ⟨2302065, by rfl⟩ : syracuseStep 6138841 = 4604131) B4604131
theorem B3025943 : Blo 896573 3025943 := bstep (se 1 (by rfl) ⟨2269457, by rfl⟩ : syracuseStep 3025943 = 4538915) B4538915
theorem B4861079 : Blo 896573 4861079 := bstep (se 1 (by rfl) ⟨3645809, by rfl⟩ : syracuseStep 4861079 = 7291619) B7291619
theorem B1518743 : Blo 896573 1518743 := bstep (se 1 (by rfl) ⟨1139057, by rfl⟩ : syracuseStep 1518743 = 2278115) B2278115
theorem B1518871 : Blo 896573 1518871 := bstep (se 1 (by rfl) ⟨1139153, by rfl⟩ : syracuseStep 1518871 = 2278307) B2278307
theorem B3845465 : Blo 896573 3845465 := bstep (se 2 (by rfl) ⟨1442049, by rfl⟩ : syracuseStep 3845465 = 2884099) B2884099
theorem B42118613 : Blo 896573 42118613 := bstep (se 7 (by rfl) ⟨493577, by rfl⟩ : syracuseStep 42118613 = 987155) B987155
theorem B3026483 : Blo 896573 3026483 := bstep (se 1 (by rfl) ⟨2269862, by rfl⟩ : syracuseStep 3026483 = 4539725) B4539725
theorem B2272819 : Blo 896573 2272819 := bstep (se 1 (by rfl) ⟨1704614, by rfl⟩ : syracuseStep 2272819 = 3409229) B3409229
theorem B896587 : Blo 896573 896587 := bstep (se 1 (by rfl) ⟨672440, by rfl⟩ : syracuseStep 896587 = 1344881) B1344881
theorem B896599 : Blo 896573 896599 := bstep (se 1 (by rfl) ⟨672449, by rfl⟩ : syracuseStep 896599 = 1344899) B1344899
theorem B896619 : Blo 896573 896619 := bstep (se 1 (by rfl) ⟨672464, by rfl⟩ : syracuseStep 896619 = 1344929) B1344929
theorem B896631 : Blo 896573 896631 := bstep (se 1 (by rfl) ⟨672473, by rfl⟩ : syracuseStep 896631 = 1344947) B1344947
theorem B896651 : Blo 896573 896651 := bstep (se 1 (by rfl) ⟨672488, by rfl⟩ : syracuseStep 896651 = 1344977) B1344977
theorem B896663 : Blo 896573 896663 := bstep (se 1 (by rfl) ⟨672497, by rfl⟩ : syracuseStep 896663 = 1344995) B1344995
theorem B896683 : Blo 896573 896683 := bstep (se 1 (by rfl) ⟨672512, by rfl⟩ : syracuseStep 896683 = 1345025) B1345025
theorem B896695 : Blo 896573 896695 := bstep (se 1 (by rfl) ⟨672521, by rfl⟩ : syracuseStep 896695 = 1345043) B1345043
theorem B2272961 : Blo 896573 2272961 := bstep (se 2 (by rfl) ⟨852360, by rfl⟩ : syracuseStep 2272961 = 1704721) B1704721
theorem B3845825 : Blo 896573 3845825 := bstep (se 2 (by rfl) ⟨1442184, by rfl⟩ : syracuseStep 3845825 = 2884369) B2884369
theorem B896715 : Blo 896573 896715 := bstep (se 1 (by rfl) ⟨672536, by rfl⟩ : syracuseStep 896715 = 1345073) B1345073
theorem B896727 : Blo 896573 896727 := bstep (se 1 (by rfl) ⟨672545, by rfl⟩ : syracuseStep 896727 = 1345091) B1345091
theorem B896747 : Blo 896573 896747 := bstep (se 1 (by rfl) ⟨672560, by rfl⟩ : syracuseStep 896747 = 1345121) B1345121
theorem B896759 : Blo 896573 896759 := bstep (se 1 (by rfl) ⟨672569, by rfl⟩ : syracuseStep 896759 = 1345139) B1345139
theorem B896779 : Blo 896573 896779 := bstep (se 1 (by rfl) ⟨672584, by rfl⟩ : syracuseStep 896779 = 1345169) B1345169
theorem B896791 : Blo 896573 896791 := bstep (se 1 (by rfl) ⟨672593, by rfl⟩ : syracuseStep 896791 = 1345187) B1345187
theorem B896811 : Blo 896573 896811 := bstep (se 1 (by rfl) ⟨672608, by rfl⟩ : syracuseStep 896811 = 1345217) B1345217
theorem B896823 : Blo 896573 896823 := bstep (se 1 (by rfl) ⟨672617, by rfl⟩ : syracuseStep 896823 = 1345235) B1345235
theorem B3026753 : Blo 896573 3026753 := bstep (se 2 (by rfl) ⟨1135032, by rfl⟩ : syracuseStep 3026753 = 2270065) B2270065
theorem B896843 : Blo 896573 896843 := bstep (se 1 (by rfl) ⟨672632, by rfl⟩ : syracuseStep 896843 = 1345265) B1345265
theorem B896855 : Blo 896573 896855 := bstep (se 1 (by rfl) ⟨672641, by rfl⟩ : syracuseStep 896855 = 1345283) B1345283
theorem B896875 : Blo 896573 896875 := bstep (se 1 (by rfl) ⟨672656, by rfl⟩ : syracuseStep 896875 = 1345313) B1345313
theorem B896887 : Blo 896573 896887 := bstep (se 1 (by rfl) ⟨672665, by rfl⟩ : syracuseStep 896887 = 1345331) B1345331
theorem B896907 : Blo 896573 896907 := bstep (se 1 (by rfl) ⟨672680, by rfl⟩ : syracuseStep 896907 = 1345361) B1345361
theorem B1519499 : Blo 896573 1519499 := bstep (se 1 (by rfl) ⟨1139624, by rfl⟩ : syracuseStep 1519499 = 2279249) B2279249
theorem B896919 : Blo 896573 896919 := bstep (se 1 (by rfl) ⟨672689, by rfl⟩ : syracuseStep 896919 = 1345379) B1345379
theorem B896939 : Blo 896573 896939 := bstep (se 1 (by rfl) ⟨672704, by rfl⟩ : syracuseStep 896939 = 1345409) B1345409
theorem B896951 : Blo 896573 896951 := bstep (se 1 (by rfl) ⟨672713, by rfl⟩ : syracuseStep 896951 = 1345427) B1345427
theorem B896971 : Blo 896573 896971 := bstep (se 1 (by rfl) ⟨672728, by rfl⟩ : syracuseStep 896971 = 1345457) B1345457
theorem B8204237 : Blo 896573 8204237 := bstep (se 3 (by rfl) ⟨1538294, by rfl⟩ : syracuseStep 8204237 = 3076589) B3076589
theorem B896983 : Blo 896573 896983 := bstep (se 1 (by rfl) ⟨672737, by rfl⟩ : syracuseStep 896983 = 1345475) B1345475
theorem B897003 : Blo 896573 897003 := bstep (se 1 (by rfl) ⟨672752, by rfl⟩ : syracuseStep 897003 = 1345505) B1345505
theorem B897015 : Blo 896573 897015 := bstep (se 1 (by rfl) ⟨672761, by rfl⟩ : syracuseStep 897015 = 1345523) B1345523
theorem B897035 : Blo 896573 897035 := bstep (se 1 (by rfl) ⟨672776, by rfl⟩ : syracuseStep 897035 = 1345553) B1345553
theorem B1519627 : Blo 896573 1519627 := bstep (se 1 (by rfl) ⟨1139720, by rfl⟩ : syracuseStep 1519627 = 2279441) B2279441
theorem B897047 : Blo 896573 897047 := bstep (se 1 (by rfl) ⟨672785, by rfl⟩ : syracuseStep 897047 = 1345571) B1345571
theorem B897067 : Blo 896573 897067 := bstep (se 1 (by rfl) ⟨672800, by rfl⟩ : syracuseStep 897067 = 1345601) B1345601
theorem B897079 : Blo 896573 897079 := bstep (se 1 (by rfl) ⟨672809, by rfl⟩ : syracuseStep 897079 = 1345619) B1345619
theorem B897099 : Blo 896573 897099 := bstep (se 1 (by rfl) ⟨672824, by rfl⟩ : syracuseStep 897099 = 1345649) B1345649
theorem B23375947 : Blo 896573 23375947 := bstep (se 1 (by rfl) ⟨17531960, by rfl⟩ : syracuseStep 23375947 = 35063921) B35063921
theorem B897111 : Blo 896573 897111 := bstep (se 1 (by rfl) ⟨672833, by rfl⟩ : syracuseStep 897111 = 1345667) B1345667
theorem B897131 : Blo 896573 897131 := bstep (se 1 (by rfl) ⟨672848, by rfl⟩ : syracuseStep 897131 = 1345697) B1345697
theorem B897143 : Blo 896573 897143 := bstep (se 1 (by rfl) ⟨672857, by rfl⟩ : syracuseStep 897143 = 1345715) B1345715
theorem B897163 : Blo 896573 897163 := bstep (se 1 (by rfl) ⟨672872, by rfl⟩ : syracuseStep 897163 = 1345745) B1345745
theorem B897175 : Blo 896573 897175 := bstep (se 1 (by rfl) ⟨672881, by rfl⟩ : syracuseStep 897175 = 1345763) B1345763
theorem B897195 : Blo 896573 897195 := bstep (se 1 (by rfl) ⟨672896, by rfl⟩ : syracuseStep 897195 = 1345793) B1345793
theorem B897207 : Blo 896573 897207 := bstep (se 1 (by rfl) ⟨672905, by rfl⟩ : syracuseStep 897207 = 1345811) B1345811
theorem B897227 : Blo 896573 897227 := bstep (se 1 (by rfl) ⟨672920, by rfl⟩ : syracuseStep 897227 = 1345841) B1345841
theorem B897239 : Blo 896573 897239 := bstep (se 1 (by rfl) ⟨672929, by rfl⟩ : syracuseStep 897239 = 1345859) B1345859
theorem B897259 : Blo 896573 897259 := bstep (se 1 (by rfl) ⟨672944, by rfl⟩ : syracuseStep 897259 = 1345889) B1345889
theorem B897271 : Blo 896573 897271 := bstep (se 1 (by rfl) ⟨672953, by rfl⟩ : syracuseStep 897271 = 1345907) B1345907
theorem B897291 : Blo 896573 897291 := bstep (se 1 (by rfl) ⟨672968, by rfl⟩ : syracuseStep 897291 = 1345937) B1345937
theorem B897303 : Blo 896573 897303 := bstep (se 1 (by rfl) ⟨672977, by rfl⟩ : syracuseStep 897303 = 1345955) B1345955
theorem B897323 : Blo 896573 897323 := bstep (se 1 (by rfl) ⟨672992, by rfl⟩ : syracuseStep 897323 = 1345985) B1345985
theorem B897335 : Blo 896573 897335 := bstep (se 1 (by rfl) ⟨673001, by rfl⟩ : syracuseStep 897335 = 1346003) B1346003
theorem B897355 : Blo 896573 897355 := bstep (se 1 (by rfl) ⟨673016, by rfl⟩ : syracuseStep 897355 = 1346033) B1346033
theorem B2732363 : Blo 896573 2732363 := bstep (se 1 (by rfl) ⟨2049272, by rfl⟩ : syracuseStep 2732363 = 4098545) B4098545
theorem B897367 : Blo 896573 897367 := bstep (se 1 (by rfl) ⟨673025, by rfl⟩ : syracuseStep 897367 = 1346051) B1346051
theorem B3027293 : Blo 896573 3027293 := bstep (se 3 (by rfl) ⟨567617, by rfl⟩ : syracuseStep 3027293 = 1135235) B1135235
theorem B897387 : Blo 896573 897387 := bstep (se 1 (by rfl) ⟨673040, by rfl⟩ : syracuseStep 897387 = 1346081) B1346081
theorem B897399 : Blo 896573 897399 := bstep (se 1 (by rfl) ⟨673049, by rfl⟩ : syracuseStep 897399 = 1346099) B1346099
theorem B897419 : Blo 896573 897419 := bstep (se 1 (by rfl) ⟨673064, by rfl⟩ : syracuseStep 897419 = 1346129) B1346129
theorem B897431 : Blo 896573 897431 := bstep (se 1 (by rfl) ⟨673073, by rfl⟩ : syracuseStep 897431 = 1346147) B1346147
theorem B897451 : Blo 896573 897451 := bstep (se 1 (by rfl) ⟨673088, by rfl⟩ : syracuseStep 897451 = 1346177) B1346177
theorem B897463 : Blo 896573 897463 := bstep (se 1 (by rfl) ⟨673097, by rfl⟩ : syracuseStep 897463 = 1346195) B1346195
theorem B897483 : Blo 896573 897483 := bstep (se 1 (by rfl) ⟨673112, by rfl⟩ : syracuseStep 897483 = 1346225) B1346225
theorem B897495 : Blo 896573 897495 := bstep (se 1 (by rfl) ⟨673121, by rfl⟩ : syracuseStep 897495 = 1346243) B1346243
theorem B897515 : Blo 896573 897515 := bstep (se 1 (by rfl) ⟨673136, by rfl⟩ : syracuseStep 897515 = 1346273) B1346273
theorem B897527 : Blo 896573 897527 := bstep (se 1 (by rfl) ⟨673145, by rfl⟩ : syracuseStep 897527 = 1346291) B1346291
theorem B897547 : Blo 896573 897547 := bstep (se 1 (by rfl) ⟨673160, by rfl⟩ : syracuseStep 897547 = 1346321) B1346321
theorem B897559 : Blo 896573 897559 := bstep (se 1 (by rfl) ⟨673169, by rfl⟩ : syracuseStep 897559 = 1346339) B1346339
theorem B897579 : Blo 896573 897579 := bstep (se 1 (by rfl) ⟨673184, by rfl⟩ : syracuseStep 897579 = 1346369) B1346369
theorem B897591 : Blo 896573 897591 := bstep (se 1 (by rfl) ⟨673193, by rfl⟩ : syracuseStep 897591 = 1346387) B1346387
theorem B897611 : Blo 896573 897611 := bstep (se 1 (by rfl) ⟨673208, by rfl⟩ : syracuseStep 897611 = 1346417) B1346417
theorem B897623 : Blo 896573 897623 := bstep (se 1 (by rfl) ⟨673217, by rfl⟩ : syracuseStep 897623 = 1346435) B1346435
theorem B897643 : Blo 896573 897643 := bstep (se 1 (by rfl) ⟨673232, by rfl⟩ : syracuseStep 897643 = 1346465) B1346465
theorem B897655 : Blo 896573 897655 := bstep (se 1 (by rfl) ⟨673241, by rfl⟩ : syracuseStep 897655 = 1346483) B1346483
theorem B897675 : Blo 896573 897675 := bstep (se 1 (by rfl) ⟨673256, by rfl⟩ : syracuseStep 897675 = 1346513) B1346513
theorem B897687 : Blo 896573 897687 := bstep (se 1 (by rfl) ⟨673265, by rfl⟩ : syracuseStep 897687 = 1346531) B1346531
theorem B897707 : Blo 896573 897707 := bstep (se 1 (by rfl) ⟨673280, by rfl⟩ : syracuseStep 897707 = 1346561) B1346561
theorem B897719 : Blo 896573 897719 := bstep (se 1 (by rfl) ⟨673289, by rfl⟩ : syracuseStep 897719 = 1346579) B1346579
theorem B897739 : Blo 896573 897739 := bstep (se 1 (by rfl) ⟨673304, by rfl⟩ : syracuseStep 897739 = 1346609) B1346609
theorem B897751 : Blo 896573 897751 := bstep (se 1 (by rfl) ⟨673313, by rfl⟩ : syracuseStep 897751 = 1346627) B1346627
theorem B897771 : Blo 896573 897771 := bstep (se 1 (by rfl) ⟨673328, by rfl⟩ : syracuseStep 897771 = 1346657) B1346657
theorem B897783 : Blo 896573 897783 := bstep (se 1 (by rfl) ⟨673337, by rfl⟩ : syracuseStep 897783 = 1346675) B1346675
theorem B897803 : Blo 896573 897803 := bstep (se 1 (by rfl) ⟨673352, by rfl⟩ : syracuseStep 897803 = 1346705) B1346705
theorem B897815 : Blo 896573 897815 := bstep (se 1 (by rfl) ⟨673361, by rfl⟩ : syracuseStep 897815 = 1346723) B1346723
theorem B897835 : Blo 896573 897835 := bstep (se 1 (by rfl) ⟨673376, by rfl⟩ : syracuseStep 897835 = 1346753) B1346753
theorem B897847 : Blo 896573 897847 := bstep (se 1 (by rfl) ⟨673385, by rfl⟩ : syracuseStep 897847 = 1346771) B1346771
theorem B897867 : Blo 896573 897867 := bstep (se 1 (by rfl) ⟨673400, by rfl⟩ : syracuseStep 897867 = 1346801) B1346801
theorem B5550923 : Blo 896573 5550923 := bstep (se 1 (by rfl) ⟨4163192, by rfl⟩ : syracuseStep 5550923 = 8326385) B8326385
theorem B897879 : Blo 896573 897879 := bstep (se 1 (by rfl) ⟨673409, by rfl⟩ : syracuseStep 897879 = 1346819) B1346819
theorem B897899 : Blo 896573 897899 := bstep (se 1 (by rfl) ⟨673424, by rfl⟩ : syracuseStep 897899 = 1346849) B1346849
theorem B897911 : Blo 896573 897911 := bstep (se 1 (by rfl) ⟨673433, by rfl⟩ : syracuseStep 897911 = 1346867) B1346867
theorem B897931 : Blo 896573 897931 := bstep (se 1 (by rfl) ⟨673448, by rfl⟩ : syracuseStep 897931 = 1346897) B1346897
theorem B897943 : Blo 896573 897943 := bstep (se 1 (by rfl) ⟨673457, by rfl⟩ : syracuseStep 897943 = 1346915) B1346915
theorem B897963 : Blo 896573 897963 := bstep (se 1 (by rfl) ⟨673472, by rfl⟩ : syracuseStep 897963 = 1346945) B1346945
theorem B2274227 : Blo 896573 2274227 := bstep (se 1 (by rfl) ⟨1705670, by rfl⟩ : syracuseStep 2274227 = 3411341) B3411341
theorem B897975 : Blo 896573 897975 := bstep (se 1 (by rfl) ⟨673481, by rfl⟩ : syracuseStep 897975 = 1346963) B1346963
theorem B897995 : Blo 896573 897995 := bstep (se 1 (by rfl) ⟨673496, by rfl⟩ : syracuseStep 897995 = 1346993) B1346993
theorem B898007 : Blo 896573 898007 := bstep (se 1 (by rfl) ⟨673505, by rfl⟩ : syracuseStep 898007 = 1347011) B1347011
theorem B2765785 : Blo 896573 2765785 := bstep (se 2 (by rfl) ⟨1037169, by rfl⟩ : syracuseStep 2765785 = 2074339) B2074339
theorem B2634713 : Blo 896573 2634713 := bstep (se 2 (by rfl) ⟨988017, by rfl⟩ : syracuseStep 2634713 = 1976035) B1976035
theorem B898027 : Blo 896573 898027 := bstep (se 1 (by rfl) ⟨673520, by rfl⟩ : syracuseStep 898027 = 1347041) B1347041
theorem B898039 : Blo 896573 898039 := bstep (se 1 (by rfl) ⟨673529, by rfl⟩ : syracuseStep 898039 = 1347059) B1347059
theorem B898059 : Blo 896573 898059 := bstep (se 1 (by rfl) ⟨673544, by rfl⟩ : syracuseStep 898059 = 1347089) B1347089
theorem B898071 : Blo 896573 898071 := bstep (se 1 (by rfl) ⟨673553, by rfl⟩ : syracuseStep 898071 = 1347107) B1347107
theorem B898091 : Blo 896573 898091 := bstep (se 1 (by rfl) ⟨673568, by rfl⟩ : syracuseStep 898091 = 1347137) B1347137
theorem B898103 : Blo 896573 898103 := bstep (se 1 (by rfl) ⟨673577, by rfl⟩ : syracuseStep 898103 = 1347155) B1347155
theorem B898123 : Blo 896573 898123 := bstep (se 1 (by rfl) ⟨673592, by rfl⟩ : syracuseStep 898123 = 1347185) B1347185
theorem B898135 : Blo 896573 898135 := bstep (se 1 (by rfl) ⟨673601, by rfl⟩ : syracuseStep 898135 = 1347203) B1347203
theorem B898155 : Blo 896573 898155 := bstep (se 1 (by rfl) ⟨673616, by rfl⟩ : syracuseStep 898155 = 1347233) B1347233
theorem B898167 : Blo 896573 898167 := bstep (se 1 (by rfl) ⟨673625, by rfl⟩ : syracuseStep 898167 = 1347251) B1347251
theorem B898187 : Blo 896573 898187 := bstep (se 1 (by rfl) ⟨673640, by rfl⟩ : syracuseStep 898187 = 1347281) B1347281
theorem B898199 : Blo 896573 898199 := bstep (se 1 (by rfl) ⟨673649, by rfl⟩ : syracuseStep 898199 = 1347299) B1347299
theorem B898219 : Blo 896573 898219 := bstep (se 1 (by rfl) ⟨673664, by rfl⟩ : syracuseStep 898219 = 1347329) B1347329
theorem B898231 : Blo 896573 898231 := bstep (se 1 (by rfl) ⟨673673, by rfl⟩ : syracuseStep 898231 = 1347347) B1347347
theorem B898251 : Blo 896573 898251 := bstep (se 1 (by rfl) ⟨673688, by rfl⟩ : syracuseStep 898251 = 1347377) B1347377
theorem B898263 : Blo 896573 898263 := bstep (se 1 (by rfl) ⟨673697, by rfl⟩ : syracuseStep 898263 = 1347395) B1347395
theorem B898283 : Blo 896573 898283 := bstep (se 1 (by rfl) ⟨673712, by rfl⟩ : syracuseStep 898283 = 1347425) B1347425
theorem B898295 : Blo 896573 898295 := bstep (se 1 (by rfl) ⟨673721, by rfl⟩ : syracuseStep 898295 = 1347443) B1347443
theorem B898315 : Blo 896573 898315 := bstep (se 1 (by rfl) ⟨673736, by rfl⟩ : syracuseStep 898315 = 1347473) B1347473
theorem B898327 : Blo 896573 898327 := bstep (se 1 (by rfl) ⟨673745, by rfl⟩ : syracuseStep 898327 = 1347491) B1347491
theorem B898347 : Blo 896573 898347 := bstep (se 1 (by rfl) ⟨673760, by rfl⟩ : syracuseStep 898347 = 1347521) B1347521
theorem B898359 : Blo 896573 898359 := bstep (se 1 (by rfl) ⟨673769, by rfl⟩ : syracuseStep 898359 = 1347539) B1347539
theorem B2274635 : Blo 896573 2274635 := bstep (se 1 (by rfl) ⟨1705976, by rfl⟩ : syracuseStep 2274635 = 3411953) B3411953
theorem B898379 : Blo 896573 898379 := bstep (se 1 (by rfl) ⟨673784, by rfl⟩ : syracuseStep 898379 = 1347569) B1347569
theorem B898391 : Blo 896573 898391 := bstep (se 1 (by rfl) ⟨673793, by rfl⟩ : syracuseStep 898391 = 1347587) B1347587
theorem B898411 : Blo 896573 898411 := bstep (se 1 (by rfl) ⟨673808, by rfl⟩ : syracuseStep 898411 = 1347617) B1347617
theorem B898423 : Blo 896573 898423 := bstep (se 1 (by rfl) ⟨673817, by rfl⟩ : syracuseStep 898423 = 1347635) B1347635
theorem B898443 : Blo 896573 898443 := bstep (se 1 (by rfl) ⟨673832, by rfl⟩ : syracuseStep 898443 = 1347665) B1347665
theorem B898455 : Blo 896573 898455 := bstep (se 1 (by rfl) ⟨673841, by rfl⟩ : syracuseStep 898455 = 1347683) B1347683
theorem B898475 : Blo 896573 898475 := bstep (se 1 (by rfl) ⟨673856, by rfl⟩ : syracuseStep 898475 = 1347713) B1347713
theorem B898487 : Blo 896573 898487 := bstep (se 1 (by rfl) ⟨673865, by rfl⟩ : syracuseStep 898487 = 1347731) B1347731
theorem B3028427 : Blo 896573 3028427 := bstep (se 1 (by rfl) ⟨2271320, by rfl⟩ : syracuseStep 3028427 = 4542641) B4542641
theorem B898507 : Blo 896573 898507 := bstep (se 1 (by rfl) ⟨673880, by rfl⟩ : syracuseStep 898507 = 1347761) B1347761
theorem B2274763 : Blo 896573 2274763 := bstep (se 1 (by rfl) ⟨1706072, by rfl⟩ : syracuseStep 2274763 = 3412145) B3412145
theorem B898519 : Blo 896573 898519 := bstep (se 1 (by rfl) ⟨673889, by rfl⟩ : syracuseStep 898519 = 1347779) B1347779
theorem B898539 : Blo 896573 898539 := bstep (se 1 (by rfl) ⟨673904, by rfl⟩ : syracuseStep 898539 = 1347809) B1347809
theorem B898551 : Blo 896573 898551 := bstep (se 1 (by rfl) ⟨673913, by rfl⟩ : syracuseStep 898551 = 1347827) B1347827
theorem B898571 : Blo 896573 898571 := bstep (se 1 (by rfl) ⟨673928, by rfl⟩ : syracuseStep 898571 = 1347857) B1347857
theorem B898583 : Blo 896573 898583 := bstep (se 1 (by rfl) ⟨673937, by rfl⟩ : syracuseStep 898583 = 1347875) B1347875
theorem B898603 : Blo 896573 898603 := bstep (se 1 (by rfl) ⟨673952, by rfl⟩ : syracuseStep 898603 = 1347905) B1347905
theorem B898615 : Blo 896573 898615 := bstep (se 1 (by rfl) ⟨673961, by rfl⟩ : syracuseStep 898615 = 1347923) B1347923
theorem B898635 : Blo 896573 898635 := bstep (se 1 (by rfl) ⟨673976, by rfl⟩ : syracuseStep 898635 = 1347953) B1347953
theorem B898647 : Blo 896573 898647 := bstep (se 1 (by rfl) ⟨673985, by rfl⟩ : syracuseStep 898647 = 1347971) B1347971
theorem B2274905 : Blo 896573 2274905 := bstep (se 2 (by rfl) ⟨853089, by rfl⟩ : syracuseStep 2274905 = 1706179) B1706179
theorem B898667 : Blo 896573 898667 := bstep (se 1 (by rfl) ⟨674000, by rfl⟩ : syracuseStep 898667 = 1348001) B1348001
theorem B898679 : Blo 896573 898679 := bstep (se 1 (by rfl) ⟨674009, by rfl⟩ : syracuseStep 898679 = 1348019) B1348019
theorem B898699 : Blo 896573 898699 := bstep (se 1 (by rfl) ⟨674024, by rfl⟩ : syracuseStep 898699 = 1348049) B1348049
theorem B898711 : Blo 896573 898711 := bstep (se 1 (by rfl) ⟨674033, by rfl⟩ : syracuseStep 898711 = 1348067) B1348067
theorem B898731 : Blo 896573 898731 := bstep (se 1 (by rfl) ⟨674048, by rfl⟩ : syracuseStep 898731 = 1348097) B1348097
theorem B898743 : Blo 896573 898743 := bstep (se 1 (by rfl) ⟨674057, by rfl⟩ : syracuseStep 898743 = 1348115) B1348115
theorem B898763 : Blo 896573 898763 := bstep (se 1 (by rfl) ⟨674072, by rfl⟩ : syracuseStep 898763 = 1348145) B1348145
theorem B898775 : Blo 896573 898775 := bstep (se 1 (by rfl) ⟨674081, by rfl⟩ : syracuseStep 898775 = 1348163) B1348163
theorem B3028697 : Blo 896573 3028697 := bstep (se 2 (by rfl) ⟨1135761, by rfl⟩ : syracuseStep 3028697 = 2271523) B2271523
theorem B898795 : Blo 896573 898795 := bstep (se 1 (by rfl) ⟨674096, by rfl⟩ : syracuseStep 898795 = 1348193) B1348193
theorem B898807 : Blo 896573 898807 := bstep (se 1 (by rfl) ⟨674105, by rfl⟩ : syracuseStep 898807 = 1348211) B1348211
theorem B898827 : Blo 896573 898827 := bstep (se 1 (by rfl) ⟨674120, by rfl⟩ : syracuseStep 898827 = 1348241) B1348241
theorem B898839 : Blo 896573 898839 := bstep (se 1 (by rfl) ⟨674129, by rfl⟩ : syracuseStep 898839 = 1348259) B1348259
theorem B898859 : Blo 896573 898859 := bstep (se 1 (by rfl) ⟨674144, by rfl⟩ : syracuseStep 898859 = 1348289) B1348289
theorem B7681837 : Blo 896573 7681837 := bstep (se 3 (by rfl) ⟨1440344, by rfl⟩ : syracuseStep 7681837 = 2880689) B2880689
theorem B898871 : Blo 896573 898871 := bstep (se 1 (by rfl) ⟨674153, by rfl⟩ : syracuseStep 898871 = 1348307) B1348307
theorem B898891 : Blo 896573 898891 := bstep (se 1 (by rfl) ⟨674168, by rfl⟩ : syracuseStep 898891 = 1348337) B1348337
theorem B5125963 : Blo 896573 5125963 := bstep (se 1 (by rfl) ⟨3844472, by rfl⟩ : syracuseStep 5125963 = 7688945) B7688945
theorem B898903 : Blo 896573 898903 := bstep (se 1 (by rfl) ⟨674177, by rfl⟩ : syracuseStep 898903 = 1348355) B1348355
theorem B898923 : Blo 896573 898923 := bstep (se 1 (by rfl) ⟨674192, by rfl⟩ : syracuseStep 898923 = 1348385) B1348385
theorem B898935 : Blo 896573 898935 := bstep (se 1 (by rfl) ⟨674201, by rfl⟩ : syracuseStep 898935 = 1348403) B1348403
theorem B898955 : Blo 896573 898955 := bstep (se 1 (by rfl) ⟨674216, by rfl⟩ : syracuseStep 898955 = 1348433) B1348433
theorem B898967 : Blo 896573 898967 := bstep (se 1 (by rfl) ⟨674225, by rfl⟩ : syracuseStep 898967 = 1348451) B1348451
theorem B898987 : Blo 896573 898987 := bstep (se 1 (by rfl) ⟨674240, by rfl⟩ : syracuseStep 898987 = 1348481) B1348481
theorem B898999 : Blo 896573 898999 := bstep (se 1 (by rfl) ⟨674249, by rfl⟩ : syracuseStep 898999 = 1348499) B1348499
theorem B899019 : Blo 896573 899019 := bstep (se 1 (by rfl) ⟨674264, by rfl⟩ : syracuseStep 899019 = 1348529) B1348529
theorem B1619927 : Blo 896573 1619927 := bstep (se 1 (by rfl) ⟨1214945, by rfl⟩ : syracuseStep 1619927 = 2429891) B2429891
theorem B899031 : Blo 896573 899031 := bstep (se 1 (by rfl) ⟨674273, by rfl⟩ : syracuseStep 899031 = 1348547) B1348547
theorem B899051 : Blo 896573 899051 := bstep (se 1 (by rfl) ⟨674288, by rfl⟩ : syracuseStep 899051 = 1348577) B1348577
theorem B899063 : Blo 896573 899063 := bstep (se 1 (by rfl) ⟨674297, by rfl⟩ : syracuseStep 899063 = 1348595) B1348595
theorem B899083 : Blo 896573 899083 := bstep (se 1 (by rfl) ⟨674312, by rfl⟩ : syracuseStep 899083 = 1348625) B1348625
theorem B899095 : Blo 896573 899095 := bstep (se 1 (by rfl) ⟨674321, by rfl⟩ : syracuseStep 899095 = 1348643) B1348643
theorem B899115 : Blo 896573 899115 := bstep (se 1 (by rfl) ⟨674336, by rfl⟩ : syracuseStep 899115 = 1348673) B1348673
theorem B899127 : Blo 896573 899127 := bstep (se 1 (by rfl) ⟨674345, by rfl⟩ : syracuseStep 899127 = 1348691) B1348691
theorem B899147 : Blo 896573 899147 := bstep (se 1 (by rfl) ⟨674360, by rfl⟩ : syracuseStep 899147 = 1348721) B1348721
theorem B899159 : Blo 896573 899159 := bstep (se 1 (by rfl) ⟨674369, by rfl⟩ : syracuseStep 899159 = 1348739) B1348739
theorem B5126237 : Blo 896573 5126237 := bstep (se 3 (by rfl) ⟨961169, by rfl⟩ : syracuseStep 5126237 = 1922339) B1922339
theorem B899179 : Blo 896573 899179 := bstep (se 1 (by rfl) ⟨674384, by rfl⟩ : syracuseStep 899179 = 1348769) B1348769
theorem B899191 : Blo 896573 899191 := bstep (se 1 (by rfl) ⟨674393, by rfl⟩ : syracuseStep 899191 = 1348787) B1348787
theorem B899211 : Blo 896573 899211 := bstep (se 1 (by rfl) ⟨674408, by rfl⟩ : syracuseStep 899211 = 1348817) B1348817
theorem B899223 : Blo 896573 899223 := bstep (se 1 (by rfl) ⟨674417, by rfl⟩ : syracuseStep 899223 = 1348835) B1348835
theorem B4864151 : Blo 896573 4864151 := bstep (se 1 (by rfl) ⟨3648113, by rfl⟩ : syracuseStep 4864151 = 7296227) B7296227
theorem B899243 : Blo 896573 899243 := bstep (se 1 (by rfl) ⟨674432, by rfl⟩ : syracuseStep 899243 = 1348865) B1348865
theorem B899255 : Blo 896573 899255 := bstep (se 1 (by rfl) ⟨674441, by rfl⟩ : syracuseStep 899255 = 1348883) B1348883
theorem B899275 : Blo 896573 899275 := bstep (se 1 (by rfl) ⟨674456, by rfl⟩ : syracuseStep 899275 = 1348913) B1348913
theorem B899287 : Blo 896573 899287 := bstep (se 1 (by rfl) ⟨674465, by rfl⟩ : syracuseStep 899287 = 1348931) B1348931
theorem B899307 : Blo 896573 899307 := bstep (se 1 (by rfl) ⟨674480, by rfl⟩ : syracuseStep 899307 = 1348961) B1348961
theorem B899319 : Blo 896573 899319 := bstep (se 1 (by rfl) ⟨674489, by rfl⟩ : syracuseStep 899319 = 1348979) B1348979
theorem B899339 : Blo 896573 899339 := bstep (se 1 (by rfl) ⟨674504, by rfl⟩ : syracuseStep 899339 = 1349009) B1349009
theorem B899351 : Blo 896573 899351 := bstep (se 1 (by rfl) ⟨674513, by rfl⟩ : syracuseStep 899351 = 1349027) B1349027
theorem B899371 : Blo 896573 899371 := bstep (se 1 (by rfl) ⟨674528, by rfl⟩ : syracuseStep 899371 = 1349057) B1349057
theorem B899383 : Blo 896573 899383 := bstep (se 1 (by rfl) ⟨674537, by rfl⟩ : syracuseStep 899383 = 1349075) B1349075
theorem B899403 : Blo 896573 899403 := bstep (se 1 (by rfl) ⟨674552, by rfl⟩ : syracuseStep 899403 = 1349105) B1349105
theorem B899415 : Blo 896573 899415 := bstep (se 1 (by rfl) ⟨674561, by rfl⟩ : syracuseStep 899415 = 1349123) B1349123
theorem B899435 : Blo 896573 899435 := bstep (se 1 (by rfl) ⟨674576, by rfl⟩ : syracuseStep 899435 = 1349153) B1349153
theorem B899447 : Blo 896573 899447 := bstep (se 1 (by rfl) ⟨674585, by rfl⟩ : syracuseStep 899447 = 1349171) B1349171
theorem B899467 : Blo 896573 899467 := bstep (se 1 (by rfl) ⟨674600, by rfl⟩ : syracuseStep 899467 = 1349201) B1349201
theorem B3029399 : Blo 896573 3029399 := bstep (se 1 (by rfl) ⟨2272049, by rfl⟩ : syracuseStep 3029399 = 4544099) B4544099
theorem B2275735 : Blo 896573 2275735 := bstep (se 1 (by rfl) ⟨1706801, by rfl⟩ : syracuseStep 2275735 = 3413603) B3413603
theorem B899479 : Blo 896573 899479 := bstep (se 1 (by rfl) ⟨674609, by rfl⟩ : syracuseStep 899479 = 1349219) B1349219
theorem B899499 : Blo 896573 899499 := bstep (se 1 (by rfl) ⟨674624, by rfl⟩ : syracuseStep 899499 = 1349249) B1349249
theorem B899511 : Blo 896573 899511 := bstep (se 1 (by rfl) ⟨674633, by rfl⟩ : syracuseStep 899511 = 1349267) B1349267
theorem B899531 : Blo 896573 899531 := bstep (se 1 (by rfl) ⟨674648, by rfl⟩ : syracuseStep 899531 = 1349297) B1349297
theorem B899543 : Blo 896573 899543 := bstep (se 1 (by rfl) ⟨674657, by rfl⟩ : syracuseStep 899543 = 1349315) B1349315
theorem B6568409 : Blo 896573 6568409 := bstep (se 2 (by rfl) ⟨2463153, by rfl⟩ : syracuseStep 6568409 = 4926307) B4926307
theorem B899563 : Blo 896573 899563 := bstep (se 1 (by rfl) ⟨674672, by rfl⟩ : syracuseStep 899563 = 1349345) B1349345
theorem B899575 : Blo 896573 899575 := bstep (se 1 (by rfl) ⟨674681, by rfl⟩ : syracuseStep 899575 = 1349363) B1349363
theorem B899595 : Blo 896573 899595 := bstep (se 1 (by rfl) ⟨674696, by rfl⟩ : syracuseStep 899595 = 1349393) B1349393
theorem B899607 : Blo 896573 899607 := bstep (se 1 (by rfl) ⟨674705, by rfl⟩ : syracuseStep 899607 = 1349411) B1349411
theorem B899627 : Blo 896573 899627 := bstep (se 1 (by rfl) ⟨674720, by rfl⟩ : syracuseStep 899627 = 1349441) B1349441
theorem B899639 : Blo 896573 899639 := bstep (se 1 (by rfl) ⟨674729, by rfl⟩ : syracuseStep 899639 = 1349459) B1349459
theorem B899659 : Blo 896573 899659 := bstep (se 1 (by rfl) ⟨674744, by rfl⟩ : syracuseStep 899659 = 1349489) B1349489
theorem B899671 : Blo 896573 899671 := bstep (se 1 (by rfl) ⟨674753, by rfl⟩ : syracuseStep 899671 = 1349507) B1349507
theorem B899691 : Blo 896573 899691 := bstep (se 1 (by rfl) ⟨674768, by rfl⟩ : syracuseStep 899691 = 1349537) B1349537
theorem B899703 : Blo 896573 899703 := bstep (se 1 (by rfl) ⟨674777, by rfl⟩ : syracuseStep 899703 = 1349555) B1349555
theorem B899723 : Blo 896573 899723 := bstep (se 1 (by rfl) ⟨674792, by rfl⟩ : syracuseStep 899723 = 1349585) B1349585
theorem B899735 : Blo 896573 899735 := bstep (se 1 (by rfl) ⟨674801, by rfl⟩ : syracuseStep 899735 = 1349603) B1349603
theorem B899755 : Blo 896573 899755 := bstep (se 1 (by rfl) ⟨674816, by rfl⟩ : syracuseStep 899755 = 1349633) B1349633
theorem B899767 : Blo 896573 899767 := bstep (se 1 (by rfl) ⟨674825, by rfl⟩ : syracuseStep 899767 = 1349651) B1349651
theorem B899787 : Blo 896573 899787 := bstep (se 1 (by rfl) ⟨674840, by rfl⟩ : syracuseStep 899787 = 1349681) B1349681
theorem B1915607 : Blo 896573 1915607 := bstep (se 1 (by rfl) ⟨1436705, by rfl⟩ : syracuseStep 1915607 = 2873411) B2873411
theorem B899799 : Blo 896573 899799 := bstep (se 1 (by rfl) ⟨674849, by rfl⟩ : syracuseStep 899799 = 1349699) B1349699
theorem B899819 : Blo 896573 899819 := bstep (se 1 (by rfl) ⟨674864, by rfl⟩ : syracuseStep 899819 = 1349729) B1349729
theorem B899831 : Blo 896573 899831 := bstep (se 1 (by rfl) ⟨674873, by rfl⟩ : syracuseStep 899831 = 1349747) B1349747
theorem B899851 : Blo 896573 899851 := bstep (se 1 (by rfl) ⟨674888, by rfl⟩ : syracuseStep 899851 = 1349777) B1349777
theorem B899863 : Blo 896573 899863 := bstep (se 1 (by rfl) ⟨674897, by rfl⟩ : syracuseStep 899863 = 1349795) B1349795
theorem B899883 : Blo 896573 899883 := bstep (se 1 (by rfl) ⟨674912, by rfl⟩ : syracuseStep 899883 = 1349825) B1349825
theorem B899895 : Blo 896573 899895 := bstep (se 1 (by rfl) ⟨674921, by rfl⟩ : syracuseStep 899895 = 1349843) B1349843
theorem B2276171 : Blo 896573 2276171 := bstep (se 1 (by rfl) ⟨1707128, by rfl⟩ : syracuseStep 2276171 = 3414257) B3414257
theorem B899915 : Blo 896573 899915 := bstep (se 1 (by rfl) ⟨674936, by rfl⟩ : syracuseStep 899915 = 1349873) B1349873
theorem B899927 : Blo 896573 899927 := bstep (se 1 (by rfl) ⟨674945, by rfl⟩ : syracuseStep 899927 = 1349891) B1349891
theorem B899947 : Blo 896573 899947 := bstep (se 1 (by rfl) ⟨674960, by rfl⟩ : syracuseStep 899947 = 1349921) B1349921
theorem B899959 : Blo 896573 899959 := bstep (se 1 (by rfl) ⟨674969, by rfl⟩ : syracuseStep 899959 = 1349939) B1349939
theorem B899979 : Blo 896573 899979 := bstep (se 1 (by rfl) ⟨674984, by rfl⟩ : syracuseStep 899979 = 1349969) B1349969
theorem B899991 : Blo 896573 899991 := bstep (se 1 (by rfl) ⟨674993, by rfl⟩ : syracuseStep 899991 = 1349987) B1349987
theorem B900011 : Blo 896573 900011 := bstep (se 1 (by rfl) ⟨675008, by rfl⟩ : syracuseStep 900011 = 1350017) B1350017
theorem B3029939 : Blo 896573 3029939 := bstep (se 1 (by rfl) ⟨2272454, by rfl⟩ : syracuseStep 3029939 = 4544909) B4544909
theorem B900023 : Blo 896573 900023 := bstep (se 1 (by rfl) ⟨675017, by rfl⟩ : syracuseStep 900023 = 1350035) B1350035
theorem B900043 : Blo 896573 900043 := bstep (se 1 (by rfl) ⟨675032, by rfl⟩ : syracuseStep 900043 = 1350065) B1350065
theorem B900055 : Blo 896573 900055 := bstep (se 1 (by rfl) ⟨675041, by rfl⟩ : syracuseStep 900055 = 1350083) B1350083
theorem B900075 : Blo 896573 900075 := bstep (se 1 (by rfl) ⟨675056, by rfl⟩ : syracuseStep 900075 = 1350113) B1350113
theorem B900087 : Blo 896573 900087 := bstep (se 1 (by rfl) ⟨675065, by rfl⟩ : syracuseStep 900087 = 1350131) B1350131
theorem B1915915 : Blo 896573 1915915 := bstep (se 1 (by rfl) ⟨1436936, by rfl⟩ : syracuseStep 1915915 = 2873873) B2873873
theorem B900107 : Blo 896573 900107 := bstep (se 1 (by rfl) ⟨675080, by rfl⟩ : syracuseStep 900107 = 1350161) B1350161
theorem B900119 : Blo 896573 900119 := bstep (se 1 (by rfl) ⟨675089, by rfl⟩ : syracuseStep 900119 = 1350179) B1350179
theorem B900139 : Blo 896573 900139 := bstep (se 1 (by rfl) ⟨675104, by rfl⟩ : syracuseStep 900139 = 1350209) B1350209
theorem B900151 : Blo 896573 900151 := bstep (se 1 (by rfl) ⟨675113, by rfl⟩ : syracuseStep 900151 = 1350227) B1350227
theorem B900171 : Blo 896573 900171 := bstep (se 1 (by rfl) ⟨675128, by rfl⟩ : syracuseStep 900171 = 1350257) B1350257
theorem B900183 : Blo 896573 900183 := bstep (se 1 (by rfl) ⟨675137, by rfl⟩ : syracuseStep 900183 = 1350275) B1350275
theorem B7683173 : Blo 896573 7683173 := bstep (se 4 (by rfl) ⟨720297, by rfl⟩ : syracuseStep 7683173 = 1440595) B1440595
theorem B900203 : Blo 896573 900203 := bstep (se 1 (by rfl) ⟨675152, by rfl⟩ : syracuseStep 900203 = 1350305) B1350305
theorem B900215 : Blo 896573 900215 := bstep (se 1 (by rfl) ⟨675161, by rfl⟩ : syracuseStep 900215 = 1350323) B1350323
theorem B900235 : Blo 896573 900235 := bstep (se 1 (by rfl) ⟨675176, by rfl⟩ : syracuseStep 900235 = 1350353) B1350353
theorem B900247 : Blo 896573 900247 := bstep (se 1 (by rfl) ⟨675185, by rfl⟩ : syracuseStep 900247 = 1350371) B1350371
theorem B900267 : Blo 896573 900267 := bstep (se 1 (by rfl) ⟨675200, by rfl⟩ : syracuseStep 900267 = 1350401) B1350401
theorem B3456179 : Blo 896573 3456179 := bstep (se 1 (by rfl) ⟨2592134, by rfl⟩ : syracuseStep 3456179 = 5184269) B5184269
theorem B900279 : Blo 896573 900279 := bstep (se 1 (by rfl) ⟨675209, by rfl⟩ : syracuseStep 900279 = 1350419) B1350419
theorem B3030209 : Blo 896573 3030209 := bstep (se 2 (by rfl) ⟨1136328, by rfl⟩ : syracuseStep 3030209 = 2272657) B2272657
theorem B2276545 : Blo 896573 2276545 := bstep (se 2 (by rfl) ⟨853704, by rfl⟩ : syracuseStep 2276545 = 1707409) B1707409
theorem B900299 : Blo 896573 900299 := bstep (se 1 (by rfl) ⟨675224, by rfl⟩ : syracuseStep 900299 = 1350449) B1350449
theorem B900311 : Blo 896573 900311 := bstep (se 1 (by rfl) ⟨675233, by rfl⟩ : syracuseStep 900311 = 1350467) B1350467
theorem B900331 : Blo 896573 900331 := bstep (se 1 (by rfl) ⟨675248, by rfl⟩ : syracuseStep 900331 = 1350497) B1350497
theorem B900343 : Blo 896573 900343 := bstep (se 1 (by rfl) ⟨675257, by rfl⟩ : syracuseStep 900343 = 1350515) B1350515
theorem B900363 : Blo 896573 900363 := bstep (se 1 (by rfl) ⟨675272, by rfl⟩ : syracuseStep 900363 = 1350545) B1350545
theorem B900375 : Blo 896573 900375 := bstep (se 1 (by rfl) ⟨675281, by rfl⟩ : syracuseStep 900375 = 1350563) B1350563
theorem B900395 : Blo 896573 900395 := bstep (se 1 (by rfl) ⟨675296, by rfl⟩ : syracuseStep 900395 = 1350593) B1350593
theorem B900407 : Blo 896573 900407 := bstep (se 1 (by rfl) ⟨675305, by rfl⟩ : syracuseStep 900407 = 1350611) B1350611
theorem B900427 : Blo 896573 900427 := bstep (se 1 (by rfl) ⟨675320, by rfl⟩ : syracuseStep 900427 = 1350641) B1350641
theorem B900439 : Blo 896573 900439 := bstep (se 1 (by rfl) ⟨675329, by rfl⟩ : syracuseStep 900439 = 1350659) B1350659
theorem B900459 : Blo 896573 900459 := bstep (se 1 (by rfl) ⟨675344, by rfl⟩ : syracuseStep 900459 = 1350689) B1350689
theorem B900471 : Blo 896573 900471 := bstep (se 1 (by rfl) ⟨675353, by rfl⟩ : syracuseStep 900471 = 1350707) B1350707
theorem B900491 : Blo 896573 900491 := bstep (se 1 (by rfl) ⟨675368, by rfl⟩ : syracuseStep 900491 = 1350737) B1350737
theorem B900503 : Blo 896573 900503 := bstep (se 1 (by rfl) ⟨675377, by rfl⟩ : syracuseStep 900503 = 1350755) B1350755
theorem B900523 : Blo 896573 900523 := bstep (se 1 (by rfl) ⟨675392, by rfl⟩ : syracuseStep 900523 = 1350785) B1350785
theorem B900535 : Blo 896573 900535 := bstep (se 1 (by rfl) ⟨675401, by rfl⟩ : syracuseStep 900535 = 1350803) B1350803
theorem B900555 : Blo 896573 900555 := bstep (se 1 (by rfl) ⟨675416, by rfl⟩ : syracuseStep 900555 = 1350833) B1350833
theorem B2047447 : Blo 896573 2047447 := bstep (se 1 (by rfl) ⟨1535585, by rfl⟩ : syracuseStep 2047447 = 3071171) B3071171
theorem B900567 : Blo 896573 900567 := bstep (se 1 (by rfl) ⟨675425, by rfl⟩ : syracuseStep 900567 = 1350851) B1350851
theorem B1621657 : Blo 896573 1621657 := bstep (se 2 (by rfl) ⟨608121, by rfl⟩ : syracuseStep 1621657 = 1216243) B1216243
theorem B20790989 : Blo 896573 20790989 := bstep (se 3 (by rfl) ⟨3898310, by rfl⟩ : syracuseStep 20790989 = 7796621) B7796621
theorem B3030749 : Blo 896573 3030749 := bstep (se 3 (by rfl) ⟨568265, by rfl⟩ : syracuseStep 3030749 = 1136531) B1136531
theorem B8208145 : Blo 896573 8208145 := bstep (se 2 (by rfl) ⟨3078054, by rfl⟩ : syracuseStep 8208145 = 6156109) B6156109
theorem B2277143 : Blo 896573 2277143 := bstep (se 1 (by rfl) ⟨1707857, by rfl⟩ : syracuseStep 2277143 = 3415715) B3415715
theorem B8306705 : Blo 896573 8306705 := bstep (se 2 (by rfl) ⟨3115014, by rfl⟩ : syracuseStep 8306705 = 6230029) B6230029
theorem B1818713 : Blo 896573 1818713 := bstep (se 2 (by rfl) ⟨682017, by rfl⟩ : syracuseStep 1818713 = 1364035) B1364035
theorem B1917145 : Blo 896573 1917145 := bstep (se 2 (by rfl) ⟨718929, by rfl⟩ : syracuseStep 1917145 = 1437859) B1437859
theorem B1622233 : Blo 896573 1622233 := bstep (se 2 (by rfl) ⟨608337, by rfl⟩ : syracuseStep 1622233 = 1216675) B1216675
theorem B6472153 : Blo 896573 6472153 := bstep (se 2 (by rfl) ⟨2427057, by rfl⟩ : syracuseStep 6472153 = 4854115) B4854115
theorem B1622515 : Blo 896573 1622515 := bstep (se 1 (by rfl) ⟨1216886, by rfl⟩ : syracuseStep 1622515 = 2433773) B2433773
theorem B2277953 : Blo 896573 2277953 := bstep (se 2 (by rfl) ⟨854232, by rfl⟩ : syracuseStep 2277953 = 1708465) B1708465
theorem B3031883 : Blo 896573 3031883 := bstep (se 1 (by rfl) ⟨2273912, by rfl⟩ : syracuseStep 3031883 = 4547825) B4547825
theorem B1819531 : Blo 896573 1819531 := bstep (se 1 (by rfl) ⟨1364648, by rfl⟩ : syracuseStep 1819531 = 2729297) B2729297
theorem B3032153 : Blo 896573 3032153 := bstep (se 2 (by rfl) ⟨1137057, by rfl⟩ : syracuseStep 3032153 = 2274115) B2274115
theorem B2278489 : Blo 896573 2278489 := bstep (se 2 (by rfl) ⟨854433, by rfl⟩ : syracuseStep 2278489 = 1708867) B1708867
theorem B3032855 : Blo 896573 3032855 := bstep (se 1 (by rfl) ⟨2274641, by rfl⟩ : syracuseStep 3032855 = 4549283) B4549283
theorem B1296343 : Blo 896573 1296343 := bstep (se 1 (by rfl) ⟨972257, by rfl⟩ : syracuseStep 1296343 = 1944515) B1944515
theorem B1820659 : Blo 896573 1820659 := bstep (se 1 (by rfl) ⟨1365494, by rfl⟩ : syracuseStep 1820659 = 2730989) B2730989
theorem B2017331 : Blo 896573 2017331 := bstep (se 1 (by rfl) ⟨1512998, by rfl⟩ : syracuseStep 2017331 = 3025997) B3025997
theorem B2017367 : Blo 896573 2017367 := bstep (se 1 (by rfl) ⟨1513025, by rfl⟩ : syracuseStep 2017367 = 3026051) B3026051
theorem B1296523 : Blo 896573 1296523 := bstep (se 1 (by rfl) ⟨972392, by rfl⟩ : syracuseStep 1296523 = 1944785) B1944785
theorem B2017547 : Blo 896573 2017547 := bstep (se 1 (by rfl) ⟨1513160, by rfl⟩ : syracuseStep 2017547 = 3026321) B3026321
theorem B3033395 : Blo 896573 3033395 := bstep (se 1 (by rfl) ⟨2275046, by rfl⟩ : syracuseStep 3033395 = 4550093) B4550093
theorem B2017601 : Blo 896573 2017601 := bstep (se 2 (by rfl) ⟨756600, by rfl⟩ : syracuseStep 2017601 = 1513201) B1513201
theorem B2017817 : Blo 896573 2017817 := bstep (se 2 (by rfl) ⟨756681, by rfl⟩ : syracuseStep 2017817 = 1513363) B1513363
theorem B3033665 : Blo 896573 3033665 := bstep (se 2 (by rfl) ⟨1137624, by rfl⟩ : syracuseStep 3033665 = 2275249) B2275249
theorem B4541021 : Blo 896573 4541021 := bstep (se 3 (by rfl) ⟨851441, by rfl⟩ : syracuseStep 4541021 = 1702883) B1702883
theorem B2017907 : Blo 896573 2017907 := bstep (se 1 (by rfl) ⟨1513430, by rfl⟩ : syracuseStep 2017907 = 3026861) B3026861
theorem B2017943 : Blo 896573 2017943 := bstep (se 1 (by rfl) ⟨1513457, by rfl⟩ : syracuseStep 2017943 = 3026915) B3026915
theorem B4311731 : Blo 896573 4311731 := bstep (se 1 (by rfl) ⟨3233798, by rfl⟩ : syracuseStep 4311731 = 6467597) B6467597
theorem B25905905 : Blo 896573 25905905 := bstep (se 2 (by rfl) ⟨9714714, by rfl⟩ : syracuseStep 25905905 = 19429429) B19429429
theorem B2018123 : Blo 896573 2018123 := bstep (se 1 (by rfl) ⟨1513592, by rfl⟩ : syracuseStep 2018123 = 3027185) B3027185
theorem B2018177 : Blo 896573 2018177 := bstep (se 2 (by rfl) ⟨756816, by rfl⟩ : syracuseStep 2018177 = 1513633) B1513633
theorem B2018393 : Blo 896573 2018393 := bstep (se 2 (by rfl) ⟨756897, by rfl⟩ : syracuseStep 2018393 = 1513795) B1513795
theorem B3034205 : Blo 896573 3034205 := bstep (se 3 (by rfl) ⟨568913, by rfl⟩ : syracuseStep 3034205 = 1137827) B1137827
theorem B2018483 : Blo 896573 2018483 := bstep (se 1 (by rfl) ⟨1513862, by rfl⟩ : syracuseStep 2018483 = 3027725) B3027725
theorem B1920179 : Blo 896573 1920179 := bstep (se 1 (by rfl) ⟨1440134, by rfl⟩ : syracuseStep 1920179 = 2880269) B2880269
theorem B1821899 : Blo 896573 1821899 := bstep (se 1 (by rfl) ⟨1366424, by rfl⟩ : syracuseStep 1821899 = 2732849) B2732849
theorem B2018519 : Blo 896573 2018519 := bstep (se 1 (by rfl) ⟨1513889, by rfl⟩ : syracuseStep 2018519 = 3027779) B3027779
theorem B2018699 : Blo 896573 2018699 := bstep (se 1 (by rfl) ⟨1514024, by rfl⟩ : syracuseStep 2018699 = 3028049) B3028049
theorem B2018753 : Blo 896573 2018753 := bstep (se 2 (by rfl) ⟨757032, by rfl⟩ : syracuseStep 2018753 = 1514065) B1514065
theorem B1363481 : Blo 896573 1363481 := bstep (se 2 (by rfl) ⟨511305, by rfl⟩ : syracuseStep 1363481 = 1022611) B1022611
theorem B2018969 : Blo 896573 2018969 := bstep (se 2 (by rfl) ⟨757113, by rfl⟩ : syracuseStep 2018969 = 1514227) B1514227
theorem B1920665 : Blo 896573 1920665 := bstep (se 2 (by rfl) ⟨720249, by rfl⟩ : syracuseStep 1920665 = 1440499) B1440499
theorem B2019059 : Blo 896573 2019059 := bstep (se 1 (by rfl) ⟨1514294, by rfl⟩ : syracuseStep 2019059 = 3028589) B3028589
theorem B2019095 : Blo 896573 2019095 := bstep (se 1 (by rfl) ⟨1514321, by rfl⟩ : syracuseStep 2019095 = 3028643) B3028643
theorem B3067723 : Blo 896573 3067723 := bstep (se 1 (by rfl) ⟨2300792, by rfl⟩ : syracuseStep 3067723 = 4601585) B4601585
theorem B4312925 : Blo 896573 4312925 := bstep (se 3 (by rfl) ⟨808673, by rfl⟩ : syracuseStep 4312925 = 1617347) B1617347
theorem B18665315 : Blo 896573 18665315 := bstep (se 1 (by rfl) ⟨13998986, by rfl⟩ : syracuseStep 18665315 = 27997973) B27997973
theorem B2019275 : Blo 896573 2019275 := bstep (se 1 (by rfl) ⟨1514456, by rfl⟩ : syracuseStep 2019275 = 3028913) B3028913
theorem B2019329 : Blo 896573 2019329 := bstep (se 2 (by rfl) ⟨757248, by rfl⟩ : syracuseStep 2019329 = 1514497) B1514497
theorem B3461213 : Blo 896573 3461213 := bstep (se 3 (by rfl) ⟨648977, by rfl⟩ : syracuseStep 3461213 = 1297955) B1297955
theorem B29151413 : Blo 896573 29151413 := bstep (se 5 (by rfl) ⟨1366472, by rfl⟩ : syracuseStep 29151413 = 2732945) B2732945
theorem B3035339 : Blo 896573 3035339 := bstep (se 1 (by rfl) ⟨2276504, by rfl⟩ : syracuseStep 3035339 = 4553009) B4553009
theorem B2019545 : Blo 896573 2019545 := bstep (se 2 (by rfl) ⟨757329, by rfl⟩ : syracuseStep 2019545 = 1514659) B1514659
theorem B2019635 : Blo 896573 2019635 := bstep (se 1 (by rfl) ⟨1514726, by rfl⟩ : syracuseStep 2019635 = 3029453) B3029453
theorem B2019671 : Blo 896573 2019671 := bstep (se 1 (by rfl) ⟨1514753, by rfl⟩ : syracuseStep 2019671 = 3029507) B3029507
theorem B2052503 : Blo 896573 2052503 := bstep (se 1 (by rfl) ⟨1539377, by rfl⟩ : syracuseStep 2052503 = 3078755) B3078755
theorem B1135063 : Blo 896573 1135063 := bstep (se 1 (by rfl) ⟨851297, by rfl⟩ : syracuseStep 1135063 = 1702595) B1702595
theorem B3035609 : Blo 896573 3035609 := bstep (se 2 (by rfl) ⟨1138353, by rfl⟩ : syracuseStep 3035609 = 2276707) B2276707
theorem B2019851 : Blo 896573 2019851 := bstep (se 1 (by rfl) ⟨1514888, by rfl⟩ : syracuseStep 2019851 = 3029777) B3029777
theorem B2019905 : Blo 896573 2019905 := bstep (se 2 (by rfl) ⟨757464, by rfl⟩ : syracuseStep 2019905 = 1514929) B1514929
theorem B3232345 : Blo 896573 3232345 := bstep (se 2 (by rfl) ⟨1212129, by rfl⟩ : syracuseStep 3232345 = 2424259) B2424259
theorem B4543127 : Blo 896573 4543127 := bstep (se 1 (by rfl) ⟨3407345, by rfl⟩ : syracuseStep 4543127 = 6814691) B6814691
theorem B2020121 : Blo 896573 2020121 := bstep (se 2 (by rfl) ⟨757545, by rfl⟩ : syracuseStep 2020121 = 1515091) B1515091
theorem B3068761 : Blo 896573 3068761 := bstep (se 2 (by rfl) ⟨1150785, by rfl⟩ : syracuseStep 3068761 = 2301571) B2301571
theorem B2020211 : Blo 896573 2020211 := bstep (se 1 (by rfl) ⟨1515158, by rfl⟩ : syracuseStep 2020211 = 3030317) B3030317
theorem B2020247 : Blo 896573 2020247 := bstep (se 1 (by rfl) ⟨1515185, by rfl⟩ : syracuseStep 2020247 = 3030371) B3030371
theorem B2774081 : Blo 896573 2774081 := bstep (se 2 (by rfl) ⟨1040280, by rfl⟩ : syracuseStep 2774081 = 2080561) B2080561
theorem B2020427 : Blo 896573 2020427 := bstep (se 1 (by rfl) ⟨1515320, by rfl⟩ : syracuseStep 2020427 = 3030641) B3030641
theorem B3658841 : Blo 896573 3658841 := bstep (se 2 (by rfl) ⟨1372065, by rfl⟩ : syracuseStep 3658841 = 2744131) B2744131
theorem B2020481 : Blo 896573 2020481 := bstep (se 2 (by rfl) ⟨757680, by rfl⟩ : syracuseStep 2020481 = 1515361) B1515361
theorem B3036311 : Blo 896573 3036311 := bstep (se 1 (by rfl) ⟨2277233, by rfl⟩ : syracuseStep 3036311 = 4554467) B4554467
theorem B971947 : Blo 896573 971947 := bstep (se 1 (by rfl) ⟨728960, by rfl⟩ : syracuseStep 971947 = 1457921) B1457921
theorem B1922305 : Blo 896573 1922305 := bstep (se 2 (by rfl) ⟨720864, by rfl⟩ : syracuseStep 1922305 = 1441729) B1441729
theorem B1135883 : Blo 896573 1135883 := bstep (se 1 (by rfl) ⟨851912, by rfl⟩ : syracuseStep 1135883 = 1703825) B1703825
theorem B972119 : Blo 896573 972119 := bstep (se 1 (by rfl) ⟨729089, by rfl⟩ : syracuseStep 972119 = 1458179) B1458179
theorem B2020697 : Blo 896573 2020697 := bstep (se 2 (by rfl) ⟨757761, by rfl⟩ : syracuseStep 2020697 = 1515523) B1515523
theorem B2020787 : Blo 896573 2020787 := bstep (se 1 (by rfl) ⟨1515590, by rfl⟩ : syracuseStep 2020787 = 3031181) B3031181
theorem B2020823 : Blo 896573 2020823 := bstep (se 1 (by rfl) ⟨1515617, by rfl⟩ : syracuseStep 2020823 = 3031235) B3031235
theorem B2021003 : Blo 896573 2021003 := bstep (se 1 (by rfl) ⟨1515752, by rfl⟩ : syracuseStep 2021003 = 3031505) B3031505
theorem B6149783 : Blo 896573 6149783 := bstep (se 1 (by rfl) ⟨4612337, by rfl⟩ : syracuseStep 6149783 = 9224675) B9224675
theorem B3036851 : Blo 896573 3036851 := bstep (se 1 (by rfl) ⟨2277638, by rfl⟩ : syracuseStep 3036851 = 4555277) B4555277
theorem B2021057 : Blo 896573 2021057 := bstep (se 2 (by rfl) ⟨757896, by rfl⟩ : syracuseStep 2021057 = 1515793) B1515793
theorem B2021273 : Blo 896573 2021273 := bstep (se 2 (by rfl) ⟨757977, by rfl⟩ : syracuseStep 2021273 = 1515955) B1515955
theorem B3037121 : Blo 896573 3037121 := bstep (se 2 (by rfl) ⟨1138920, by rfl⟩ : syracuseStep 3037121 = 2277841) B2277841
theorem B1136587 : Blo 896573 1136587 := bstep (se 1 (by rfl) ⟨852440, by rfl⟩ : syracuseStep 1136587 = 1704881) B1704881
theorem B2021363 : Blo 896573 2021363 := bstep (se 1 (by rfl) ⟨1516022, by rfl⟩ : syracuseStep 2021363 = 3032045) B3032045
theorem B2021399 : Blo 896573 2021399 := bstep (se 1 (by rfl) ⟨1516049, by rfl⟩ : syracuseStep 2021399 = 3032099) B3032099
theorem B2021579 : Blo 896573 2021579 := bstep (se 1 (by rfl) ⟨1516184, by rfl⟩ : syracuseStep 2021579 = 3032369) B3032369
theorem B1136855 : Blo 896573 1136855 := bstep (se 1 (by rfl) ⟨852641, by rfl⟩ : syracuseStep 1136855 = 1705283) B1705283
theorem B8181977 : Blo 896573 8181977 := bstep (se 2 (by rfl) ⟨3068241, by rfl⟩ : syracuseStep 8181977 = 6136483) B6136483
theorem B2021633 : Blo 896573 2021633 := bstep (se 2 (by rfl) ⟨758112, by rfl⟩ : syracuseStep 2021633 = 1516225) B1516225
theorem B6576515 : Blo 896573 6576515 := bstep (se 1 (by rfl) ⟨4932386, by rfl⟩ : syracuseStep 6576515 = 9864773) B9864773
theorem B2021849 : Blo 896573 2021849 := bstep (se 2 (by rfl) ⟨758193, by rfl⟩ : syracuseStep 2021849 = 1516387) B1516387
theorem B2873821 : Blo 896573 2873821 := bstep (se 3 (by rfl) ⟨538841, by rfl⟩ : syracuseStep 2873821 = 1077683) B1077683
theorem B3037661 : Blo 896573 3037661 := bstep (se 3 (by rfl) ⟨569561, by rfl⟩ : syracuseStep 3037661 = 1139123) B1139123
theorem B2021939 : Blo 896573 2021939 := bstep (se 1 (by rfl) ⟨1516454, by rfl⟩ : syracuseStep 2021939 = 3032909) B3032909
theorem B2021975 : Blo 896573 2021975 := bstep (se 1 (by rfl) ⟨1516481, by rfl⟩ : syracuseStep 2021975 = 3032963) B3032963
theorem B2022155 : Blo 896573 2022155 := bstep (se 1 (by rfl) ⟨1516616, by rfl⟩ : syracuseStep 2022155 = 3033233) B3033233
theorem B2022209 : Blo 896573 2022209 := bstep (se 2 (by rfl) ⟨758328, by rfl⟩ : syracuseStep 2022209 = 1516657) B1516657
theorem B1137559 : Blo 896573 1137559 := bstep (se 1 (by rfl) ⟨853169, by rfl⟩ : syracuseStep 1137559 = 1706339) B1706339
theorem B12311513 : Blo 896573 12311513 := bstep (se 2 (by rfl) ⟨4616817, by rfl⟩ : syracuseStep 12311513 = 9233635) B9233635
theorem B2022425 : Blo 896573 2022425 := bstep (se 2 (by rfl) ⟨758409, by rfl⟩ : syracuseStep 2022425 = 1516819) B1516819
theorem B8313949 : Blo 896573 8313949 := bstep (se 3 (by rfl) ⟨1558865, by rfl⟩ : syracuseStep 8313949 = 3117731) B3117731
theorem B2022515 : Blo 896573 2022515 := bstep (se 1 (by rfl) ⟨1516886, by rfl⟩ : syracuseStep 2022515 = 3033773) B3033773
theorem B2022551 : Blo 896573 2022551 := bstep (se 1 (by rfl) ⟨1516913, by rfl⟩ : syracuseStep 2022551 = 3033827) B3033827
theorem B2022731 : Blo 896573 2022731 := bstep (se 1 (by rfl) ⟨1517048, by rfl⟩ : syracuseStep 2022731 = 3034097) B3034097
theorem B2022785 : Blo 896573 2022785 := bstep (se 2 (by rfl) ⟨758544, by rfl⟩ : syracuseStep 2022785 = 1517089) B1517089
theorem B7396759 : Blo 896573 7396759 := bstep (se 1 (by rfl) ⟨5547569, by rfl⟩ : syracuseStep 7396759 = 11095139) B11095139
theorem B3038795 : Blo 896573 3038795 := bstep (se 1 (by rfl) ⟨2279096, by rfl⟩ : syracuseStep 3038795 = 4558193) B4558193
theorem B2023001 : Blo 896573 2023001 := bstep (se 2 (by rfl) ⟨758625, by rfl⟩ : syracuseStep 2023001 = 1517251) B1517251
theorem B2023091 : Blo 896573 2023091 := bstep (se 1 (by rfl) ⟨1517318, by rfl⟩ : syracuseStep 2023091 = 3034637) B3034637
theorem B2023127 : Blo 896573 2023127 := bstep (se 1 (by rfl) ⟨1517345, by rfl⟩ : syracuseStep 2023127 = 3034691) B3034691
theorem B2154329 : Blo 896573 2154329 := bstep (se 2 (by rfl) ⟨807873, by rfl⟩ : syracuseStep 2154329 = 1615747) B1615747
theorem B3039065 : Blo 896573 3039065 := bstep (se 2 (by rfl) ⟨1139649, by rfl⟩ : syracuseStep 3039065 = 2279299) B2279299
theorem B2023307 : Blo 896573 2023307 := bstep (se 1 (by rfl) ⟨1517480, by rfl⟩ : syracuseStep 2023307 = 3034961) B3034961
theorem B2023361 : Blo 896573 2023361 := bstep (se 2 (by rfl) ⟨758760, by rfl⟩ : syracuseStep 2023361 = 1517521) B1517521
theorem B2154443 : Blo 896573 2154443 := bstep (se 1 (by rfl) ⟨1615832, by rfl⟩ : syracuseStep 2154443 = 3231665) B3231665
theorem B4317229 : Blo 896573 4317229 := bstep (se 3 (by rfl) ⟨809480, by rfl⟩ : syracuseStep 4317229 = 1618961) B1618961
theorem B4546691 : Blo 896573 4546691 := bstep (se 1 (by rfl) ⟨3410018, by rfl⟩ : syracuseStep 4546691 = 6820037) B6820037
theorem B2187415 : Blo 896573 2187415 := bstep (se 1 (by rfl) ⟨1640561, by rfl⟩ : syracuseStep 2187415 = 3281123) B3281123
theorem B2023577 : Blo 896573 2023577 := bstep (se 2 (by rfl) ⟨758841, by rfl⟩ : syracuseStep 2023577 = 1517683) B1517683
theorem B1925299 : Blo 896573 1925299 := bstep (se 1 (by rfl) ⟨1443974, by rfl⟩ : syracuseStep 1925299 = 2887949) B2887949
theorem B2023667 : Blo 896573 2023667 := bstep (se 1 (by rfl) ⟨1517750, by rfl⟩ : syracuseStep 2023667 = 3035501) B3035501
theorem B2023703 : Blo 896573 2023703 := bstep (se 1 (by rfl) ⟨1517777, by rfl⟩ : syracuseStep 2023703 = 3035555) B3035555
theorem B2023883 : Blo 896573 2023883 := bstep (se 1 (by rfl) ⟨1517912, by rfl⟩ : syracuseStep 2023883 = 3035825) B3035825
theorem B2023937 : Blo 896573 2023937 := bstep (se 2 (by rfl) ⟨758976, by rfl⟩ : syracuseStep 2023937 = 1517953) B1517953
theorem B3465773 : Blo 896573 3465773 := bstep (se 3 (by rfl) ⟨649832, by rfl⟩ : syracuseStep 3465773 = 1299665) B1299665
theorem B1139275 : Blo 896573 1139275 := bstep (se 1 (by rfl) ⟨854456, by rfl⟩ : syracuseStep 1139275 = 1708913) B1708913
theorem B2024153 : Blo 896573 2024153 := bstep (se 2 (by rfl) ⟨759057, by rfl⟩ : syracuseStep 2024153 = 1518115) B1518115
theorem B7299857 : Blo 896573 7299857 := bstep (se 2 (by rfl) ⟨2737446, by rfl⟩ : syracuseStep 7299857 = 5474893) B5474893
theorem B1368857 : Blo 896573 1368857 := bstep (se 2 (by rfl) ⟨513321, by rfl⟩ : syracuseStep 1368857 = 1026643) B1026643
theorem B2024243 : Blo 896573 2024243 := bstep (se 1 (by rfl) ⟨1518182, by rfl⟩ : syracuseStep 2024243 = 3036365) B3036365
theorem B59007797 : Blo 896573 59007797 := bstep (se 5 (by rfl) ⟨2765990, by rfl⟩ : syracuseStep 59007797 = 5531981) B5531981
theorem B2024279 : Blo 896573 2024279 := bstep (se 1 (by rfl) ⟨1518209, by rfl⟩ : syracuseStep 2024279 = 3036419) B3036419
theorem B2024459 : Blo 896573 2024459 := bstep (se 1 (by rfl) ⟨1518344, by rfl⟩ : syracuseStep 2024459 = 3036689) B3036689
theorem B2024513 : Blo 896573 2024513 := bstep (se 2 (by rfl) ⟨759192, by rfl⟩ : syracuseStep 2024513 = 1518385) B1518385
theorem B1008715 : Blo 896573 1008715 := bstep (se 1 (by rfl) ⟨756536, by rfl⟩ : syracuseStep 1008715 = 1513073) B1513073
theorem B17523863 : Blo 896573 17523863 := bstep (se 1 (by rfl) ⟨13142897, by rfl⟩ : syracuseStep 17523863 = 26285795) B26285795
theorem B1008823 : Blo 896573 1008823 := bstep (se 1 (by rfl) ⟨756617, by rfl⟩ : syracuseStep 1008823 = 1513235) B1513235
theorem B3237085 : Blo 896573 3237085 := bstep (se 3 (by rfl) ⟨606953, by rfl⟩ : syracuseStep 3237085 = 1213907) B1213907
theorem B2024729 : Blo 896573 2024729 := bstep (se 2 (by rfl) ⟨759273, by rfl⟩ : syracuseStep 2024729 = 1518547) B1518547
theorem B1009003 : Blo 896573 1009003 := bstep (se 1 (by rfl) ⟨756752, by rfl⟩ : syracuseStep 1009003 = 1513505) B1513505
theorem B2024819 : Blo 896573 2024819 := bstep (se 1 (by rfl) ⟨1518614, by rfl⟩ : syracuseStep 2024819 = 3037229) B3037229
theorem B23029109 : Blo 896573 23029109 := bstep (se 5 (by rfl) ⟨1079489, by rfl⟩ : syracuseStep 23029109 = 2158979) B2158979
theorem B2024855 : Blo 896573 2024855 := bstep (se 1 (by rfl) ⟨1518641, by rfl⟩ : syracuseStep 2024855 = 3037283) B3037283
theorem B1009111 : Blo 896573 1009111 := bstep (se 1 (by rfl) ⟨756833, by rfl⟩ : syracuseStep 1009111 = 1513667) B1513667
theorem B7792163 : Blo 896573 7792163 := bstep (se 1 (by rfl) ⟨5844122, by rfl⟩ : syracuseStep 7792163 = 11688245) B11688245
theorem B2025035 : Blo 896573 2025035 := bstep (se 1 (by rfl) ⟨1518776, by rfl⟩ : syracuseStep 2025035 = 3037553) B3037553
theorem B2025089 : Blo 896573 2025089 := bstep (se 2 (by rfl) ⟨759408, by rfl⟩ : syracuseStep 2025089 = 1518817) B1518817
theorem B1009291 : Blo 896573 1009291 := bstep (se 1 (by rfl) ⟨756968, by rfl⟩ : syracuseStep 1009291 = 1513937) B1513937
theorem B10938007 : Blo 896573 10938007 := bstep (se 1 (by rfl) ⟨8203505, by rfl⟩ : syracuseStep 10938007 = 16407011) B16407011
theorem B1664729 : Blo 896573 1664729 := bstep (se 2 (by rfl) ⟨624273, by rfl⟩ : syracuseStep 1664729 = 1248547) B1248547
theorem B1009399 : Blo 896573 1009399 := bstep (se 1 (by rfl) ⟨757049, by rfl⟩ : syracuseStep 1009399 = 1514099) B1514099
theorem B2025305 : Blo 896573 2025305 := bstep (se 2 (by rfl) ⟨759489, by rfl⟩ : syracuseStep 2025305 = 1518979) B1518979
theorem B1599385 : Blo 896573 1599385 := bstep (se 2 (by rfl) ⟨599769, by rfl⟩ : syracuseStep 1599385 = 1199539) B1199539
theorem B1009579 : Blo 896573 1009579 := bstep (se 1 (by rfl) ⟨757184, by rfl⟩ : syracuseStep 1009579 = 1514369) B1514369
theorem B2025395 : Blo 896573 2025395 := bstep (se 1 (by rfl) ⟨1519046, by rfl⟩ : syracuseStep 2025395 = 3038093) B3038093
theorem B2025431 : Blo 896573 2025431 := bstep (se 1 (by rfl) ⟨1519073, by rfl⟩ : syracuseStep 2025431 = 3038147) B3038147
theorem B1009687 : Blo 896573 1009687 := bstep (se 1 (by rfl) ⟨757265, by rfl⟩ : syracuseStep 1009687 = 1514531) B1514531
theorem B2025611 : Blo 896573 2025611 := bstep (se 1 (by rfl) ⟨1519208, by rfl⟩ : syracuseStep 2025611 = 3038417) B3038417
theorem B2025665 : Blo 896573 2025665 := bstep (se 2 (by rfl) ⟨759624, by rfl⟩ : syracuseStep 2025665 = 1519249) B1519249
theorem B1009867 : Blo 896573 1009867 := bstep (se 1 (by rfl) ⟨757400, by rfl⟩ : syracuseStep 1009867 = 1514801) B1514801
theorem B11659565 : Blo 896573 11659565 := bstep (se 3 (by rfl) ⟨2186168, by rfl⟩ : syracuseStep 11659565 = 4372337) B4372337
theorem B1009975 : Blo 896573 1009975 := bstep (se 1 (by rfl) ⟨757481, by rfl⟩ : syracuseStep 1009975 = 1514963) B1514963
theorem B2025881 : Blo 896573 2025881 := bstep (se 2 (by rfl) ⟨759705, by rfl⟩ : syracuseStep 2025881 = 1519411) B1519411
theorem B1010155 : Blo 896573 1010155 := bstep (se 1 (by rfl) ⟨757616, by rfl⟩ : syracuseStep 1010155 = 1515233) B1515233
theorem B2025971 : Blo 896573 2025971 := bstep (se 1 (by rfl) ⟨1519478, by rfl⟩ : syracuseStep 2025971 = 3038957) B3038957
theorem B2026007 : Blo 896573 2026007 := bstep (se 1 (by rfl) ⟨1519505, by rfl⟩ : syracuseStep 2026007 = 3039011) B3039011
theorem B1010263 : Blo 896573 1010263 := bstep (se 1 (by rfl) ⟨757697, by rfl⟩ : syracuseStep 1010263 = 1515395) B1515395
theorem B5761637 : Blo 896573 5761637 := bstep (se 4 (by rfl) ⟨540153, by rfl⟩ : syracuseStep 5761637 = 1080307) B1080307
theorem B2026187 : Blo 896573 2026187 := bstep (se 1 (by rfl) ⟨1519640, by rfl⟩ : syracuseStep 2026187 = 3039281) B3039281
theorem B6810317 : Blo 896573 6810317 := bstep (se 3 (by rfl) ⟨1276934, by rfl⟩ : syracuseStep 6810317 = 2553869) B2553869
theorem B2026241 : Blo 896573 2026241 := bstep (se 2 (by rfl) ⟨759840, by rfl⟩ : syracuseStep 2026241 = 1519681) B1519681
theorem B1010443 : Blo 896573 1010443 := bstep (se 1 (by rfl) ⟨757832, by rfl⟩ : syracuseStep 1010443 = 1515665) B1515665
theorem B7301933 : Blo 896573 7301933 := bstep (se 3 (by rfl) ⟨1369112, by rfl⟩ : syracuseStep 7301933 = 2738225) B2738225
theorem B1010551 : Blo 896573 1010551 := bstep (se 1 (by rfl) ⟨757913, by rfl⟩ : syracuseStep 1010551 = 1515827) B1515827
theorem B2878487 : Blo 896573 2878487 := bstep (se 1 (by rfl) ⟨2158865, by rfl⟩ : syracuseStep 2878487 = 4317731) B4317731
theorem B1010731 : Blo 896573 1010731 := bstep (se 1 (by rfl) ⟨758048, by rfl⟩ : syracuseStep 1010731 = 1516097) B1516097
theorem B1010839 : Blo 896573 1010839 := bstep (se 1 (by rfl) ⟨758129, by rfl⟩ : syracuseStep 1010839 = 1516259) B1516259
theorem B6810803 : Blo 896573 6810803 := bstep (se 1 (by rfl) ⟨5108102, by rfl⟩ : syracuseStep 6810803 = 10216205) B10216205
theorem B5107009 : Blo 896573 5107009 := bstep (se 2 (by rfl) ⟨1915128, by rfl⟩ : syracuseStep 5107009 = 3830257) B3830257
theorem B1011019 : Blo 896573 1011019 := bstep (se 1 (by rfl) ⟨758264, by rfl⟩ : syracuseStep 1011019 = 1516529) B1516529
theorem B1011127 : Blo 896573 1011127 := bstep (se 1 (by rfl) ⟨758345, by rfl⟩ : syracuseStep 1011127 = 1516691) B1516691
theorem B13102553 : Blo 896573 13102553 := bstep (se 2 (by rfl) ⟨4913457, by rfl⟩ : syracuseStep 13102553 = 9826915) B9826915
theorem B1011307 : Blo 896573 1011307 := bstep (se 1 (by rfl) ⟨758480, by rfl⟩ : syracuseStep 1011307 = 1516961) B1516961
theorem B1011415 : Blo 896573 1011415 := bstep (se 1 (by rfl) ⟨758561, by rfl⟩ : syracuseStep 1011415 = 1517123) B1517123
theorem B4550417 : Blo 896573 4550417 := bstep (se 2 (by rfl) ⟨1706406, by rfl⟩ : syracuseStep 4550417 = 3412813) B3412813
theorem B1535819 : Blo 896573 1535819 := bstep (se 1 (by rfl) ⟨1151864, by rfl⟩ : syracuseStep 1535819 = 2303729) B2303729
theorem B1011595 : Blo 896573 1011595 := bstep (se 1 (by rfl) ⟨758696, by rfl⟩ : syracuseStep 1011595 = 1517393) B1517393
theorem B2879383 : Blo 896573 2879383 := bstep (se 1 (by rfl) ⟨2159537, by rfl⟩ : syracuseStep 2879383 = 4319075) B4319075
theorem B4550579 : Blo 896573 4550579 := bstep (se 1 (by rfl) ⟨3412934, by rfl⟩ : syracuseStep 4550579 = 6825869) B6825869
theorem B1011703 : Blo 896573 1011703 := bstep (se 1 (by rfl) ⟨758777, by rfl⟩ : syracuseStep 1011703 = 1517555) B1517555
theorem B1011883 : Blo 896573 1011883 := bstep (se 1 (by rfl) ⟨758912, by rfl⟩ : syracuseStep 1011883 = 1517825) B1517825
theorem B1011991 : Blo 896573 1011991 := bstep (se 1 (by rfl) ⟨758993, by rfl⟩ : syracuseStep 1011991 = 1517987) B1517987
theorem B2879819 : Blo 896573 2879819 := bstep (se 1 (by rfl) ⟨2159864, by rfl⟩ : syracuseStep 2879819 = 4319729) B4319729
theorem B3830105 : Blo 896573 3830105 := bstep (se 2 (by rfl) ⟨1436289, by rfl⟩ : syracuseStep 3830105 = 2872579) B2872579
theorem B1012171 : Blo 896573 1012171 := bstep (se 1 (by rfl) ⟨759128, by rfl⟩ : syracuseStep 1012171 = 1518257) B1518257
theorem B3404339 : Blo 896573 3404339 := bstep (se 1 (by rfl) ⟨2553254, by rfl⟩ : syracuseStep 3404339 = 5106509) B5106509
theorem B1012279 : Blo 896573 1012279 := bstep (se 1 (by rfl) ⟨759209, by rfl⟩ : syracuseStep 1012279 = 1518419) B1518419
theorem B6812261 : Blo 896573 6812261 := bstep (se 4 (by rfl) ⟨638649, by rfl⟩ : syracuseStep 6812261 = 1277299) B1277299
theorem B7795379 : Blo 896573 7795379 := bstep (se 1 (by rfl) ⟨5846534, by rfl⟩ : syracuseStep 7795379 = 11693069) B11693069
theorem B11530957 : Blo 896573 11530957 := bstep (se 3 (by rfl) ⟨2162054, by rfl⟩ : syracuseStep 11530957 = 4324109) B4324109
theorem B1012459 : Blo 896573 1012459 := bstep (se 1 (by rfl) ⟨759344, by rfl⟩ : syracuseStep 1012459 = 1518689) B1518689
theorem B1078039 : Blo 896573 1078039 := bstep (se 1 (by rfl) ⟨808529, by rfl⟩ : syracuseStep 1078039 = 1617059) B1617059
theorem B16380737 : Blo 896573 16380737 := bstep (se 2 (by rfl) ⟨6142776, by rfl⟩ : syracuseStep 16380737 = 12285553) B12285553
theorem B1012567 : Blo 896573 1012567 := bstep (se 1 (by rfl) ⟨759425, by rfl⟩ : syracuseStep 1012567 = 1518851) B1518851
theorem B1438679 : Blo 896573 1438679 := bstep (se 1 (by rfl) ⟨1079009, by rfl⟩ : syracuseStep 1438679 = 2158019) B2158019
theorem B1012747 : Blo 896573 1012747 := bstep (se 1 (by rfl) ⟨759560, by rfl⟩ : syracuseStep 1012747 = 1519121) B1519121
theorem B10220579 : Blo 896573 10220579 := bstep (se 1 (by rfl) ⟨7665434, by rfl⟩ : syracuseStep 10220579 = 15330869) B15330869
theorem B6812747 : Blo 896573 6812747 := bstep (se 1 (by rfl) ⟨5109560, by rfl⟩ : syracuseStep 6812747 = 10219121) B10219121
theorem B1438807 : Blo 896573 1438807 := bstep (se 1 (by rfl) ⟨1079105, by rfl⟩ : syracuseStep 1438807 = 2158211) B2158211
theorem B1012855 : Blo 896573 1012855 := bstep (se 1 (by rfl) ⟨759641, by rfl⟩ : syracuseStep 1012855 = 1519283) B1519283
theorem B1438859 : Blo 896573 1438859 := bstep (se 1 (by rfl) ⟨1079144, by rfl⟩ : syracuseStep 1438859 = 2158289) B2158289
theorem B1438987 : Blo 896573 1438987 := bstep (se 1 (by rfl) ⟨1079240, by rfl⟩ : syracuseStep 1438987 = 2158481) B2158481
theorem B8189201 : Blo 896573 8189201 := bstep (se 2 (by rfl) ⟨3070950, by rfl⟩ : syracuseStep 8189201 = 6141901) B6141901
theorem B1013035 : Blo 896573 1013035 := bstep (se 1 (by rfl) ⟨759776, by rfl⟩ : syracuseStep 1013035 = 1519553) B1519553
theorem B1013143 : Blo 896573 1013143 := bstep (se 1 (by rfl) ⟨759857, by rfl⟩ : syracuseStep 1013143 = 1519715) B1519715
theorem B2880947 : Blo 896573 2880947 := bstep (se 1 (by rfl) ⟨2160710, by rfl⟩ : syracuseStep 2880947 = 4321421) B4321421
theorem B9729553 : Blo 896573 9729553 := bstep (se 2 (by rfl) ⟨3648582, by rfl⟩ : syracuseStep 9729553 = 7297165) B7297165
theorem B2881099 : Blo 896573 2881099 := bstep (se 1 (by rfl) ⟨2160824, by rfl⟩ : syracuseStep 2881099 = 4321649) B4321649
theorem B1537625 : Blo 896573 1537625 := bstep (se 2 (by rfl) ⟨576609, by rfl⟩ : syracuseStep 1537625 = 1153219) B1153219
theorem B2553437 : Blo 896573 2553437 := bstep (se 3 (by rfl) ⟨478769, by rfl⟩ : syracuseStep 2553437 = 957539) B957539
theorem B1439371 : Blo 896573 1439371 := bstep (se 1 (by rfl) ⟨1079528, by rfl⟩ : syracuseStep 1439371 = 2159057) B2159057
theorem B4552523 : Blo 896573 4552523 := bstep (se 1 (by rfl) ⟨3414392, by rfl⟩ : syracuseStep 4552523 = 6828785) B6828785
theorem B1439627 : Blo 896573 1439627 := bstep (se 1 (by rfl) ⟨1079720, by rfl⟩ : syracuseStep 1439627 = 2159441) B2159441
theorem B3831745 : Blo 896573 3831745 := bstep (se 2 (by rfl) ⟨1436904, by rfl⟩ : syracuseStep 3831745 = 2873809) B2873809
theorem B3405827 : Blo 896573 3405827 := bstep (se 1 (by rfl) ⟨2554370, by rfl⟩ : syracuseStep 3405827 = 5108741) B5108741
theorem B2881601 : Blo 896573 2881601 := bstep (se 2 (by rfl) ⟨1080600, by rfl⟩ : syracuseStep 2881601 = 2161201) B2161201
theorem B1440089 : Blo 896573 1440089 := bstep (se 2 (by rfl) ⟨540033, by rfl⟩ : syracuseStep 1440089 = 1080067) B1080067
theorem B2161075 : Blo 896573 2161075 := bstep (se 1 (by rfl) ⟨1620806, by rfl⟩ : syracuseStep 2161075 = 3241613) B3241613
theorem B3406283 : Blo 896573 3406283 := bstep (se 1 (by rfl) ⟨2554712, by rfl⟩ : syracuseStep 3406283 = 5109425) B5109425
theorem B1440217 : Blo 896573 1440217 := bstep (se 2 (by rfl) ⟨540081, by rfl⟩ : syracuseStep 1440217 = 1080163) B1080163
theorem B3832343 : Blo 896573 3832343 := bstep (se 1 (by rfl) ⟨2874257, by rfl⟩ : syracuseStep 3832343 = 5748515) B5748515
theorem B1702451 : Blo 896573 1702451 := bstep (se 1 (by rfl) ⟨1276838, by rfl⟩ : syracuseStep 1702451 = 2553677) B2553677
theorem B3406481 : Blo 896573 3406481 := bstep (se 2 (by rfl) ⟨1277430, by rfl⟩ : syracuseStep 3406481 = 2554861) B2554861
theorem B5110451 : Blo 896573 5110451 := bstep (se 1 (by rfl) ⟨3832838, by rfl⟩ : syracuseStep 5110451 = 7665677) B7665677
theorem B1080139 : Blo 896573 1080139 := bstep (se 1 (by rfl) ⟨810104, by rfl⟩ : syracuseStep 1080139 = 1620209) B1620209
theorem B1276889 : Blo 896573 1276889 := bstep (se 2 (by rfl) ⟨478833, by rfl⟩ : syracuseStep 1276889 = 957667) B957667
theorem B3243025 : Blo 896573 3243025 := bstep (se 2 (by rfl) ⟨1216134, by rfl⟩ : syracuseStep 3243025 = 2432269) B2432269
theorem B1702937 : Blo 896573 1702937 := bstep (se 2 (by rfl) ⟨638601, by rfl⟩ : syracuseStep 1702937 = 1277203) B1277203
theorem B1277003 : Blo 896573 1277003 := bstep (se 1 (by rfl) ⟨957752, by rfl⟩ : syracuseStep 1277003 = 1915505) B1915505
theorem B7667075 : Blo 896573 7667075 := bstep (se 1 (by rfl) ⟨5750306, by rfl⟩ : syracuseStep 7667075 = 11500613) B11500613
theorem B3407255 : Blo 896573 3407255 := bstep (se 1 (by rfl) ⟨2555441, by rfl⟩ : syracuseStep 3407255 = 5110883) B5110883
theorem B3636697 : Blo 896573 3636697 := bstep (se 2 (by rfl) ⟨1363761, by rfl⟩ : syracuseStep 3636697 = 2727523) B2727523
theorem B4554305 : Blo 896573 4554305 := bstep (se 2 (by rfl) ⟨1707864, by rfl⟩ : syracuseStep 4554305 = 3415729) B3415729
theorem B1277527 : Blo 896573 1277527 := bstep (se 1 (by rfl) ⟨958145, by rfl⟩ : syracuseStep 1277527 = 1916291) B1916291
theorem B3407453 : Blo 896573 3407453 := bstep (se 3 (by rfl) ⟨638897, by rfl⟩ : syracuseStep 3407453 = 1277795) B1277795
theorem B23002865 : Blo 896573 23002865 := bstep (se 2 (by rfl) ⟨8626074, by rfl⟩ : syracuseStep 23002865 = 17252149) B17252149
theorem B3833675 : Blo 896573 3833675 := bstep (se 1 (by rfl) ⟨2875256, by rfl⟩ : syracuseStep 3833675 = 5750513) B5750513
theorem B5537803 : Blo 896573 5537803 := bstep (se 1 (by rfl) ⟨4153352, by rfl⟩ : syracuseStep 5537803 = 8306705) B8306705
theorem B2162747 : Blo 896573 2162747 := bstep (se 1 (by rfl) ⟨1622060, by rfl⟩ : syracuseStep 2162747 = 3244121) B3244121
theorem B2555965 : Blo 896573 2555965 := bstep (se 3 (by rfl) ⟨479243, by rfl⟩ : syracuseStep 2555965 = 958487) B958487
theorem B3407939 : Blo 896573 3407939 := bstep (se 1 (by rfl) ⟨2555954, by rfl⟩ : syracuseStep 3407939 = 5111909) B5111909
theorem B2916553 : Blo 896573 2916553 := bstep (se 2 (by rfl) ⟨1093707, by rfl⟩ : syracuseStep 2916553 = 2187415) B2187415
theorem B4554953 : Blo 896573 4554953 := bstep (se 2 (by rfl) ⟨1708107, by rfl⟩ : syracuseStep 4554953 = 3416215) B3416215
theorem B4849901 : Blo 896573 4849901 := bstep (se 3 (by rfl) ⟨909356, by rfl⟩ : syracuseStep 4849901 = 1818713) B1818713
theorem B3637505 : Blo 896573 3637505 := bstep (se 2 (by rfl) ⟨1364064, by rfl⟩ : syracuseStep 3637505 = 2728129) B2728129
theorem B2556193 : Blo 896573 2556193 := bstep (se 2 (by rfl) ⟨958572, by rfl⟩ : syracuseStep 2556193 = 1917145) B1917145
theorem B1704235 : Blo 896573 1704235 := bstep (se 1 (by rfl) ⟨1278176, by rfl⟩ : syracuseStep 1704235 = 2556353) B2556353
theorem B10944827 : Blo 896573 10944827 := bstep (se 1 (by rfl) ⟨8208620, by rfl⟩ : syracuseStep 10944827 = 16417241) B16417241
theorem B1704311 : Blo 896573 1704311 := bstep (se 1 (by rfl) ⟨1278233, by rfl⟩ : syracuseStep 1704311 = 2556467) B2556467
theorem B2556535 : Blo 896573 2556535 := bstep (se 1 (by rfl) ⟨1917401, by rfl⟩ : syracuseStep 2556535 = 3834803) B3834803
theorem B2163353 : Blo 896573 2163353 := bstep (se 2 (by rfl) ⟨811257, by rfl⟩ : syracuseStep 2163353 = 1622515) B1622515
theorem B3408925 : Blo 896573 3408925 := bstep (se 3 (by rfl) ⟨639173, by rfl⟩ : syracuseStep 3408925 = 1278347) B1278347
theorem B8651909 : Blo 896573 8651909 := bstep (se 4 (by rfl) ⟨811116, by rfl⟩ : syracuseStep 8651909 = 1622233) B1622233
theorem B2426041 : Blo 896573 2426041 := bstep (se 2 (by rfl) ⟨909765, by rfl⟩ : syracuseStep 2426041 = 1819531) B1819531
theorem B1344887 : Blo 896573 1344887 := bstep (se 1 (by rfl) ⟨1008665, by rfl⟩ : syracuseStep 1344887 = 2017331) B2017331
theorem B1344911 : Blo 896573 1344911 := bstep (se 1 (by rfl) ⟨1008683, by rfl⟩ : syracuseStep 1344911 = 2017367) B2017367
theorem B4326803 : Blo 896573 4326803 := bstep (se 1 (by rfl) ⟨3245102, by rfl⟩ : syracuseStep 4326803 = 6490205) B6490205
theorem B1344953 : Blo 896573 1344953 := bstep (se 2 (by rfl) ⟨504357, by rfl⟩ : syracuseStep 1344953 = 1008715) B1008715
theorem B8652217 : Blo 896573 8652217 := bstep (se 2 (by rfl) ⟨3244581, by rfl⟩ : syracuseStep 8652217 = 6489163) B6489163
theorem B1345031 : Blo 896573 1345031 := bstep (se 1 (by rfl) ⟨1008773, by rfl⟩ : syracuseStep 1345031 = 2017547) B2017547
theorem B5113367 : Blo 896573 5113367 := bstep (se 1 (by rfl) ⟨3835025, by rfl⟩ : syracuseStep 5113367 = 7670051) B7670051
theorem B2557469 : Blo 896573 2557469 := bstep (se 3 (by rfl) ⟨479525, by rfl⟩ : syracuseStep 2557469 = 959051) B959051
theorem B1345067 : Blo 896573 1345067 := bstep (se 1 (by rfl) ⟨1008800, by rfl⟩ : syracuseStep 1345067 = 2017601) B2017601
theorem B1345097 : Blo 896573 1345097 := bstep (se 2 (by rfl) ⟨504411, by rfl⟩ : syracuseStep 1345097 = 1008823) B1008823
theorem B1345211 : Blo 896573 1345211 := bstep (se 1 (by rfl) ⟨1008908, by rfl⟩ : syracuseStep 1345211 = 2017817) B2017817
theorem B1345271 : Blo 896573 1345271 := bstep (se 1 (by rfl) ⟨1008953, by rfl⟩ : syracuseStep 1345271 = 2017907) B2017907
theorem B1345295 : Blo 896573 1345295 := bstep (se 1 (by rfl) ⟨1008971, by rfl⟩ : syracuseStep 1345295 = 2017943) B2017943
theorem B1345337 : Blo 896573 1345337 := bstep (se 2 (by rfl) ⟨504501, by rfl⟩ : syracuseStep 1345337 = 1009003) B1009003
theorem B17270603 : Blo 896573 17270603 := bstep (se 1 (by rfl) ⟨12952952, by rfl⟩ : syracuseStep 17270603 = 25905905) B25905905
theorem B2557811 : Blo 896573 2557811 := bstep (se 1 (by rfl) ⟨1918358, by rfl⟩ : syracuseStep 2557811 = 3836717) B3836717
theorem B1345415 : Blo 896573 1345415 := bstep (se 1 (by rfl) ⟨1009061, by rfl⟩ : syracuseStep 1345415 = 2018123) B2018123
theorem B1345451 : Blo 896573 1345451 := bstep (se 1 (by rfl) ⟨1009088, by rfl⟩ : syracuseStep 1345451 = 2018177) B2018177
theorem B1345481 : Blo 896573 1345481 := bstep (se 2 (by rfl) ⟨504555, by rfl⟩ : syracuseStep 1345481 = 1009111) B1009111
theorem B1345595 : Blo 896573 1345595 := bstep (se 1 (by rfl) ⟨1009196, by rfl⟩ : syracuseStep 1345595 = 2018393) B2018393
theorem B1345655 : Blo 896573 1345655 := bstep (se 1 (by rfl) ⟨1009241, by rfl⟩ : syracuseStep 1345655 = 2018483) B2018483
theorem B1280119 : Blo 896573 1280119 := bstep (se 1 (by rfl) ⟨960089, by rfl⟩ : syracuseStep 1280119 = 1920179) B1920179
theorem B1214599 : Blo 896573 1214599 := bstep (se 1 (by rfl) ⟨910949, by rfl⟩ : syracuseStep 1214599 = 1821899) B1821899
theorem B1345679 : Blo 896573 1345679 := bstep (se 1 (by rfl) ⟨1009259, by rfl⟩ : syracuseStep 1345679 = 2018519) B2018519
theorem B1345721 : Blo 896573 1345721 := bstep (se 2 (by rfl) ⟨504645, by rfl⟩ : syracuseStep 1345721 = 1009291) B1009291
theorem B1345799 : Blo 896573 1345799 := bstep (se 1 (by rfl) ⟨1009349, by rfl⟩ : syracuseStep 1345799 = 2018699) B2018699
theorem B1706255 : Blo 896573 1706255 := bstep (se 1 (by rfl) ⟨1279691, by rfl⟩ : syracuseStep 1706255 = 2559383) B2559383
theorem B1345835 : Blo 896573 1345835 := bstep (se 1 (by rfl) ⟨1009376, by rfl⟩ : syracuseStep 1345835 = 2018753) B2018753
theorem B2558267 : Blo 896573 2558267 := bstep (se 1 (by rfl) ⟨1918700, by rfl⟩ : syracuseStep 2558267 = 3837401) B3837401
theorem B1345865 : Blo 896573 1345865 := bstep (se 2 (by rfl) ⟨504699, by rfl⟩ : syracuseStep 1345865 = 1009399) B1009399
theorem B9832889 : Blo 896573 9832889 := bstep (se 2 (by rfl) ⟨3687333, by rfl⟩ : syracuseStep 9832889 = 7374667) B7374667
theorem B1345979 : Blo 896573 1345979 := bstep (se 1 (by rfl) ⟨1009484, by rfl⟩ : syracuseStep 1345979 = 2018969) B2018969
theorem B1280443 : Blo 896573 1280443 := bstep (se 1 (by rfl) ⟨960332, by rfl⟩ : syracuseStep 1280443 = 1920665) B1920665
theorem B1346039 : Blo 896573 1346039 := bstep (se 1 (by rfl) ⟨1009529, by rfl⟩ : syracuseStep 1346039 = 2019059) B2019059
theorem B1346063 : Blo 896573 1346063 := bstep (se 1 (by rfl) ⟨1009547, by rfl⟩ : syracuseStep 1346063 = 2019095) B2019095
theorem B2132513 : Blo 896573 2132513 := bstep (se 2 (by rfl) ⟨799692, by rfl⟩ : syracuseStep 2132513 = 1599385) B1599385
theorem B1346105 : Blo 896573 1346105 := bstep (se 2 (by rfl) ⟨504789, by rfl⟩ : syracuseStep 1346105 = 1009579) B1009579
theorem B3836477 : Blo 896573 3836477 := bstep (se 3 (by rfl) ⟨719339, by rfl⟩ : syracuseStep 3836477 = 1438679) B1438679
theorem B1346183 : Blo 896573 1346183 := bstep (se 1 (by rfl) ⟨1009637, by rfl⟩ : syracuseStep 1346183 = 2019275) B2019275
theorem B2427545 : Blo 896573 2427545 := bstep (se 2 (by rfl) ⟨910329, by rfl⟩ : syracuseStep 2427545 = 1820659) B1820659
theorem B1346219 : Blo 896573 1346219 := bstep (se 1 (by rfl) ⟨1009664, by rfl⟩ : syracuseStep 1346219 = 2019329) B2019329
theorem B1346249 : Blo 896573 1346249 := bstep (se 2 (by rfl) ⟨504843, by rfl⟩ : syracuseStep 1346249 = 1009687) B1009687
theorem B19434275 : Blo 896573 19434275 := bstep (se 1 (by rfl) ⟨14575706, by rfl⟩ : syracuseStep 19434275 = 29151413) B29151413
theorem B6916913 : Blo 896573 6916913 := bstep (se 2 (by rfl) ⟨2593842, by rfl⟩ : syracuseStep 6916913 = 5187685) B5187685
theorem B1346363 : Blo 896573 1346363 := bstep (se 1 (by rfl) ⟨1009772, by rfl⟩ : syracuseStep 1346363 = 2019545) B2019545
theorem B1346423 : Blo 896573 1346423 := bstep (se 1 (by rfl) ⟨1009817, by rfl⟩ : syracuseStep 1346423 = 2019635) B2019635
theorem B1346447 : Blo 896573 1346447 := bstep (se 1 (by rfl) ⟨1009835, by rfl⟩ : syracuseStep 1346447 = 2019671) B2019671
theorem B11537315 : Blo 896573 11537315 := bstep (se 1 (by rfl) ⟨8652986, by rfl⟩ : syracuseStep 11537315 = 17305973) B17305973
theorem B1346489 : Blo 896573 1346489 := bstep (se 2 (by rfl) ⟨504933, by rfl⟩ : syracuseStep 1346489 = 1009867) B1009867
theorem B1346567 : Blo 896573 1346567 := bstep (se 1 (by rfl) ⟨1009925, by rfl⟩ : syracuseStep 1346567 = 2019851) B2019851
theorem B1346603 : Blo 896573 1346603 := bstep (se 1 (by rfl) ⟨1009952, by rfl⟩ : syracuseStep 1346603 = 2019905) B2019905
theorem B12946493 : Blo 896573 12946493 := bstep (se 3 (by rfl) ⟨2427467, by rfl⟩ : syracuseStep 12946493 = 4854935) B4854935
theorem B1346633 : Blo 896573 1346633 := bstep (se 2 (by rfl) ⟨504987, by rfl⟩ : syracuseStep 1346633 = 1009975) B1009975
theorem B1346747 : Blo 896573 1346747 := bstep (se 1 (by rfl) ⟨1010060, by rfl⟩ : syracuseStep 1346747 = 2020121) B2020121
theorem B1346807 : Blo 896573 1346807 := bstep (se 1 (by rfl) ⟨1010105, by rfl⟩ : syracuseStep 1346807 = 2020211) B2020211
theorem B1346831 : Blo 896573 1346831 := bstep (se 1 (by rfl) ⟨1010123, by rfl⟩ : syracuseStep 1346831 = 2020247) B2020247
theorem B1346873 : Blo 896573 1346873 := bstep (se 2 (by rfl) ⟨505077, by rfl⟩ : syracuseStep 1346873 = 1010155) B1010155
theorem B1346951 : Blo 896573 1346951 := bstep (se 1 (by rfl) ⟨1010213, by rfl⟩ : syracuseStep 1346951 = 2020427) B2020427
theorem B1346987 : Blo 896573 1346987 := bstep (se 1 (by rfl) ⟨1010240, by rfl⟩ : syracuseStep 1346987 = 2020481) B2020481
theorem B1347017 : Blo 896573 1347017 := bstep (se 2 (by rfl) ⟨505131, by rfl⟩ : syracuseStep 1347017 = 1010263) B1010263
theorem B1969679 : Blo 896573 1969679 := bstep (se 1 (by rfl) ⟨1477259, by rfl⟩ : syracuseStep 1969679 = 2954519) B2954519
theorem B2493985 : Blo 896573 2493985 := bstep (se 2 (by rfl) ⟨935244, by rfl⟩ : syracuseStep 2493985 = 1870489) B1870489
theorem B1347131 : Blo 896573 1347131 := bstep (se 1 (by rfl) ⟨1010348, by rfl⟩ : syracuseStep 1347131 = 2020697) B2020697
theorem B2592317 : Blo 896573 2592317 := bstep (se 3 (by rfl) ⟨486059, by rfl⟩ : syracuseStep 2592317 = 972119) B972119
theorem B1347191 : Blo 896573 1347191 := bstep (se 1 (by rfl) ⟨1010393, by rfl⟩ : syracuseStep 1347191 = 2020787) B2020787
theorem B1347215 : Blo 896573 1347215 := bstep (se 1 (by rfl) ⟨1010411, by rfl⟩ : syracuseStep 1347215 = 2020823) B2020823
theorem B1347257 : Blo 896573 1347257 := bstep (se 2 (by rfl) ⟨505221, by rfl⟩ : syracuseStep 1347257 = 1010443) B1010443
theorem B1347335 : Blo 896573 1347335 := bstep (se 1 (by rfl) ⟨1010501, by rfl⟩ : syracuseStep 1347335 = 2021003) B2021003
theorem B1347371 : Blo 896573 1347371 := bstep (se 1 (by rfl) ⟨1010528, by rfl⟩ : syracuseStep 1347371 = 2021057) B2021057
theorem B1347401 : Blo 896573 1347401 := bstep (se 2 (by rfl) ⟨505275, by rfl⟩ : syracuseStep 1347401 = 1010551) B1010551
theorem B3411827 : Blo 896573 3411827 := bstep (se 1 (by rfl) ⟨2558870, by rfl⟩ : syracuseStep 3411827 = 5117741) B5117741
theorem B1707895 : Blo 896573 1707895 := bstep (se 1 (by rfl) ⟨1280921, by rfl⟩ : syracuseStep 1707895 = 2561843) B2561843
theorem B1347515 : Blo 896573 1347515 := bstep (se 1 (by rfl) ⟨1010636, by rfl⟩ : syracuseStep 1347515 = 2021273) B2021273
theorem B1347575 : Blo 896573 1347575 := bstep (se 1 (by rfl) ⟨1010681, by rfl⟩ : syracuseStep 1347575 = 2021363) B2021363
theorem B1347599 : Blo 896573 1347599 := bstep (se 1 (by rfl) ⟨1010699, by rfl⟩ : syracuseStep 1347599 = 2021399) B2021399
theorem B1347641 : Blo 896573 1347641 := bstep (se 2 (by rfl) ⟨505365, by rfl⟩ : syracuseStep 1347641 = 1010731) B1010731
theorem B1347719 : Blo 896573 1347719 := bstep (se 1 (by rfl) ⟨1010789, by rfl⟩ : syracuseStep 1347719 = 2021579) B2021579
theorem B1347755 : Blo 896573 1347755 := bstep (se 1 (by rfl) ⟨1010816, by rfl⟩ : syracuseStep 1347755 = 2021633) B2021633
theorem B1347785 : Blo 896573 1347785 := bstep (se 2 (by rfl) ⟨505419, by rfl⟩ : syracuseStep 1347785 = 1010839) B1010839
theorem B1347899 : Blo 896573 1347899 := bstep (se 1 (by rfl) ⟨1010924, by rfl⟩ : syracuseStep 1347899 = 2021849) B2021849
theorem B1347959 : Blo 896573 1347959 := bstep (se 1 (by rfl) ⟨1010969, by rfl⟩ : syracuseStep 1347959 = 2021939) B2021939
theorem B1347983 : Blo 896573 1347983 := bstep (se 1 (by rfl) ⟨1010987, by rfl⟩ : syracuseStep 1347983 = 2021975) B2021975
theorem B1348025 : Blo 896573 1348025 := bstep (se 2 (by rfl) ⟨505509, by rfl⟩ : syracuseStep 1348025 = 1011019) B1011019
theorem B1348103 : Blo 896573 1348103 := bstep (se 1 (by rfl) ⟨1011077, by rfl⟩ : syracuseStep 1348103 = 2022155) B2022155
theorem B1348139 : Blo 896573 1348139 := bstep (se 1 (by rfl) ⟨1011104, by rfl⟩ : syracuseStep 1348139 = 2022209) B2022209
theorem B1348169 : Blo 896573 1348169 := bstep (se 2 (by rfl) ⟨505563, by rfl⟩ : syracuseStep 1348169 = 1011127) B1011127
theorem B1348283 : Blo 896573 1348283 := bstep (se 1 (by rfl) ⟨1011212, by rfl⟩ : syracuseStep 1348283 = 2022425) B2022425
theorem B1348343 : Blo 896573 1348343 := bstep (se 1 (by rfl) ⟨1011257, by rfl⟩ : syracuseStep 1348343 = 2022515) B2022515
theorem B1348367 : Blo 896573 1348367 := bstep (se 1 (by rfl) ⟨1011275, by rfl⟩ : syracuseStep 1348367 = 2022551) B2022551
theorem B10523429 : Blo 896573 10523429 := bstep (se 4 (by rfl) ⟨986571, by rfl⟩ : syracuseStep 10523429 = 1973143) B1973143
theorem B1348409 : Blo 896573 1348409 := bstep (se 2 (by rfl) ⟨505653, by rfl⟩ : syracuseStep 1348409 = 1011307) B1011307
theorem B1348487 : Blo 896573 1348487 := bstep (se 1 (by rfl) ⟨1011365, by rfl⟩ : syracuseStep 1348487 = 2022731) B2022731
theorem B1348523 : Blo 896573 1348523 := bstep (se 1 (by rfl) ⟨1011392, by rfl⟩ : syracuseStep 1348523 = 2022785) B2022785
theorem B1348553 : Blo 896573 1348553 := bstep (se 2 (by rfl) ⟨505707, by rfl⟩ : syracuseStep 1348553 = 1011415) B1011415
theorem B2626561 : Blo 896573 2626561 := bstep (se 2 (by rfl) ⟨984960, by rfl⟩ : syracuseStep 2626561 = 1969921) B1969921
theorem B3839005 : Blo 896573 3839005 := bstep (se 3 (by rfl) ⟨719813, by rfl⟩ : syracuseStep 3839005 = 1439627) B1439627
theorem B1348667 : Blo 896573 1348667 := bstep (se 1 (by rfl) ⟨1011500, by rfl⟩ : syracuseStep 1348667 = 2023001) B2023001
theorem B1348727 : Blo 896573 1348727 := bstep (se 1 (by rfl) ⟨1011545, by rfl⟩ : syracuseStep 1348727 = 2023091) B2023091
theorem B2561159 : Blo 896573 2561159 := bstep (se 1 (by rfl) ⟨1920869, by rfl⟩ : syracuseStep 2561159 = 3841739) B3841739
theorem B1348751 : Blo 896573 1348751 := bstep (se 1 (by rfl) ⟨1011563, by rfl⟩ : syracuseStep 1348751 = 2023127) B2023127
theorem B1348793 : Blo 896573 1348793 := bstep (se 2 (by rfl) ⟨505797, by rfl⟩ : syracuseStep 1348793 = 1011595) B1011595
theorem B3839177 : Blo 896573 3839177 := bstep (se 2 (by rfl) ⟨1439691, by rfl⟩ : syracuseStep 3839177 = 2879383) B2879383
theorem B1348871 : Blo 896573 1348871 := bstep (se 1 (by rfl) ⟨1011653, by rfl⟩ : syracuseStep 1348871 = 2023307) B2023307
theorem B1348907 : Blo 896573 1348907 := bstep (se 1 (by rfl) ⟨1011680, by rfl⟩ : syracuseStep 1348907 = 2023361) B2023361
theorem B1348937 : Blo 896573 1348937 := bstep (se 2 (by rfl) ⟨505851, by rfl⟩ : syracuseStep 1348937 = 1011703) B1011703
theorem B31167929 : Blo 896573 31167929 := bstep (se 2 (by rfl) ⟨11687973, by rfl⟩ : syracuseStep 31167929 = 23375947) B23375947
theorem B1349051 : Blo 896573 1349051 := bstep (se 1 (by rfl) ⟨1011788, by rfl⟩ : syracuseStep 1349051 = 2023577) B2023577
theorem B1349111 : Blo 896573 1349111 := bstep (se 1 (by rfl) ⟨1011833, by rfl⟩ : syracuseStep 1349111 = 2023667) B2023667
theorem B1349135 : Blo 896573 1349135 := bstep (se 1 (by rfl) ⟨1011851, by rfl⟩ : syracuseStep 1349135 = 2023703) B2023703
theorem B1349177 : Blo 896573 1349177 := bstep (se 2 (by rfl) ⟨505941, by rfl⟩ : syracuseStep 1349177 = 1011883) B1011883
theorem B1513019 : Blo 896573 1513019 := bstep (se 1 (by rfl) ⟨1134764, by rfl⟩ : syracuseStep 1513019 = 2269529) B2269529
theorem B6821495 : Blo 896573 6821495 := bstep (se 1 (by rfl) ⟨5116121, by rfl⟩ : syracuseStep 6821495 = 10232243) B10232243
theorem B1349255 : Blo 896573 1349255 := bstep (se 1 (by rfl) ⟨1011941, by rfl⟩ : syracuseStep 1349255 = 2023883) B2023883
theorem B1349291 : Blo 896573 1349291 := bstep (se 1 (by rfl) ⟨1011968, by rfl⟩ : syracuseStep 1349291 = 2023937) B2023937
theorem B1349321 : Blo 896573 1349321 := bstep (se 2 (by rfl) ⟨505995, by rfl⟩ : syracuseStep 1349321 = 1011991) B1011991
theorem B1349435 : Blo 896573 1349435 := bstep (se 1 (by rfl) ⟨1012076, by rfl⟩ : syracuseStep 1349435 = 2024153) B2024153
theorem B1349495 : Blo 896573 1349495 := bstep (se 1 (by rfl) ⟨1012121, by rfl⟩ : syracuseStep 1349495 = 2024243) B2024243
theorem B1349519 : Blo 896573 1349519 := bstep (se 1 (by rfl) ⟨1012139, by rfl⟩ : syracuseStep 1349519 = 2024279) B2024279
theorem B1349561 : Blo 896573 1349561 := bstep (se 2 (by rfl) ⟨506085, by rfl⟩ : syracuseStep 1349561 = 1012171) B1012171
theorem B1513417 : Blo 896573 1513417 := bstep (se 2 (by rfl) ⟨567531, by rfl⟩ : syracuseStep 1513417 = 1135063) B1135063
theorem B1349639 : Blo 896573 1349639 := bstep (se 1 (by rfl) ⟨1012229, by rfl⟩ : syracuseStep 1349639 = 2024459) B2024459
theorem B3414059 : Blo 896573 3414059 := bstep (se 1 (by rfl) ⟨2560544, by rfl⟩ : syracuseStep 3414059 = 5121089) B5121089
theorem B1349675 : Blo 896573 1349675 := bstep (se 1 (by rfl) ⟨1012256, by rfl⟩ : syracuseStep 1349675 = 2024513) B2024513
theorem B1349705 : Blo 896573 1349705 := bstep (se 2 (by rfl) ⟨506139, by rfl⟩ : syracuseStep 1349705 = 1012279) B1012279
theorem B1349819 : Blo 896573 1349819 := bstep (se 1 (by rfl) ⟨1012364, by rfl⟩ : syracuseStep 1349819 = 2024729) B2024729
theorem B1349879 : Blo 896573 1349879 := bstep (se 1 (by rfl) ⟨1012409, by rfl⟩ : syracuseStep 1349879 = 2024819) B2024819
theorem B1349903 : Blo 896573 1349903 := bstep (se 1 (by rfl) ⟨1012427, by rfl⟩ : syracuseStep 1349903 = 2024855) B2024855
theorem B15374609 : Blo 896573 15374609 := bstep (se 2 (by rfl) ⟨5765478, by rfl⟩ : syracuseStep 15374609 = 11530957) B11530957
theorem B1349945 : Blo 896573 1349945 := bstep (se 2 (by rfl) ⟨506229, by rfl⟩ : syracuseStep 1349945 = 1012459) B1012459
theorem B1350023 : Blo 896573 1350023 := bstep (se 1 (by rfl) ⟨1012517, by rfl⟩ : syracuseStep 1350023 = 2025035) B2025035
theorem B1350059 : Blo 896573 1350059 := bstep (se 1 (by rfl) ⟨1012544, by rfl⟩ : syracuseStep 1350059 = 2025089) B2025089
theorem B1350089 : Blo 896573 1350089 := bstep (se 2 (by rfl) ⟨506283, by rfl⟩ : syracuseStep 1350089 = 1012567) B1012567
theorem B9706027 : Blo 896573 9706027 := bstep (se 1 (by rfl) ⟨7279520, by rfl⟩ : syracuseStep 9706027 = 14559041) B14559041
theorem B1350203 : Blo 896573 1350203 := bstep (se 1 (by rfl) ⟨1012652, by rfl⟩ : syracuseStep 1350203 = 2025305) B2025305
theorem B6822467 : Blo 896573 6822467 := bstep (se 1 (by rfl) ⟨5116850, by rfl⟩ : syracuseStep 6822467 = 10233701) B10233701
theorem B6232643 : Blo 896573 6232643 := bstep (se 1 (by rfl) ⟨4674482, by rfl⟩ : syracuseStep 6232643 = 9348965) B9348965
theorem B1350263 : Blo 896573 1350263 := bstep (se 1 (by rfl) ⟨1012697, by rfl⟩ : syracuseStep 1350263 = 2025395) B2025395
theorem B1514119 : Blo 896573 1514119 := bstep (se 1 (by rfl) ⟨1135589, by rfl⟩ : syracuseStep 1514119 = 2271179) B2271179
theorem B1350287 : Blo 896573 1350287 := bstep (se 1 (by rfl) ⟨1012715, by rfl⟩ : syracuseStep 1350287 = 2025431) B2025431
theorem B1350329 : Blo 896573 1350329 := bstep (se 2 (by rfl) ⟨506373, by rfl⟩ : syracuseStep 1350329 = 1012747) B1012747
theorem B1350407 : Blo 896573 1350407 := bstep (se 1 (by rfl) ⟨1012805, by rfl⟩ : syracuseStep 1350407 = 2025611) B2025611
theorem B924431 : Blo 896573 924431 := bstep (se 1 (by rfl) ⟨693323, by rfl⟩ : syracuseStep 924431 = 1386647) B1386647
theorem B1350443 : Blo 896573 1350443 := bstep (se 1 (by rfl) ⟨1012832, by rfl⟩ : syracuseStep 1350443 = 2025665) B2025665
theorem B1350473 : Blo 896573 1350473 := bstep (se 2 (by rfl) ⟨506427, by rfl⟩ : syracuseStep 1350473 = 1012855) B1012855
theorem B7773043 : Blo 896573 7773043 := bstep (se 1 (by rfl) ⟨5829782, by rfl⟩ : syracuseStep 7773043 = 11659565) B11659565
theorem B1350587 : Blo 896573 1350587 := bstep (se 1 (by rfl) ⟨1012940, by rfl⟩ : syracuseStep 1350587 = 2025881) B2025881
theorem B1350647 : Blo 896573 1350647 := bstep (se 1 (by rfl) ⟨1012985, by rfl⟩ : syracuseStep 1350647 = 2025971) B2025971
theorem B2563073 : Blo 896573 2563073 := bstep (se 2 (by rfl) ⟨961152, by rfl⟩ : syracuseStep 2563073 = 1922305) B1922305
theorem B1350671 : Blo 896573 1350671 := bstep (se 1 (by rfl) ⟨1013003, by rfl⟩ : syracuseStep 1350671 = 2026007) B2026007
theorem B1350713 : Blo 896573 1350713 := bstep (se 2 (by rfl) ⟨506517, by rfl⟩ : syracuseStep 1350713 = 1013035) B1013035
theorem B3841091 : Blo 896573 3841091 := bstep (se 1 (by rfl) ⟨2880818, by rfl⟩ : syracuseStep 3841091 = 5761637) B5761637
theorem B1350791 : Blo 896573 1350791 := bstep (se 1 (by rfl) ⟨1013093, by rfl⟩ : syracuseStep 1350791 = 2026187) B2026187
theorem B1350827 : Blo 896573 1350827 := bstep (se 1 (by rfl) ⟨1013120, by rfl⟩ : syracuseStep 1350827 = 2026241) B2026241
theorem B1350857 : Blo 896573 1350857 := bstep (se 2 (by rfl) ⟨506571, by rfl⟩ : syracuseStep 1350857 = 1013143) B1013143
theorem B1514767 : Blo 896573 1514767 := bstep (se 1 (by rfl) ⟨1136075, by rfl⟩ : syracuseStep 1514767 = 2272151) B2272151
theorem B2563643 : Blo 896573 2563643 := bstep (se 1 (by rfl) ⟨1922732, by rfl⟩ : syracuseStep 2563643 = 3845465) B3845465
theorem B1515307 : Blo 896573 1515307 := bstep (se 1 (by rfl) ⟨1136480, by rfl⟩ : syracuseStep 1515307 = 2272961) B2272961
theorem B2563883 : Blo 896573 2563883 := bstep (se 1 (by rfl) ⟨1922912, by rfl⟩ : syracuseStep 2563883 = 3845825) B3845825
theorem B1515449 : Blo 896573 1515449 := bstep (se 2 (by rfl) ⟨568293, by rfl⟩ : syracuseStep 1515449 = 1136587) B1136587
theorem B17309969 : Blo 896573 17309969 := bstep (se 2 (by rfl) ⟨6491238, by rfl⟩ : syracuseStep 17309969 = 12982477) B12982477
theorem B2269559 : Blo 896573 2269559 := bstep (se 1 (by rfl) ⟨1702169, by rfl⟩ : syracuseStep 2269559 = 3404339) B3404339
theorem B10920491 : Blo 896573 10920491 := bstep (se 1 (by rfl) ⟨8190368, by rfl⟩ : syracuseStep 10920491 = 16380737) B16380737
theorem B1516151 : Blo 896573 1516151 := bstep (se 1 (by rfl) ⟨1137113, by rfl⟩ : syracuseStep 1516151 = 2274227) B2274227
theorem B959239 : Blo 896573 959239 := bstep (se 1 (by rfl) ⟨719429, by rfl⟩ : syracuseStep 959239 = 1438859) B1438859
theorem B58336037 : Blo 896573 58336037 := bstep (se 4 (by rfl) ⟨5469003, by rfl⟩ : syracuseStep 58336037 = 10938007) B10938007
theorem B1516423 : Blo 896573 1516423 := bstep (se 1 (by rfl) ⟨1137317, by rfl⟩ : syracuseStep 1516423 = 2274635) B2274635
theorem B1516603 : Blo 896573 1516603 := bstep (se 1 (by rfl) ⟨1137452, by rfl⟩ : syracuseStep 1516603 = 2274905) B2274905
theorem B1025083 : Blo 896573 1025083 := bstep (se 1 (by rfl) ⟨768812, by rfl⟩ : syracuseStep 1025083 = 1537625) B1537625
theorem B1516745 : Blo 896573 1516745 := bstep (se 2 (by rfl) ⟨568779, by rfl⟩ : syracuseStep 1516745 = 1137559) B1137559
theorem B2270551 : Blo 896573 2270551 := bstep (se 1 (by rfl) ⟨1702913, by rfl⟩ : syracuseStep 2270551 = 3405827) B3405827
theorem B3417491 : Blo 896573 3417491 := bstep (se 1 (by rfl) ⟨2563118, by rfl⟩ : syracuseStep 3417491 = 5126237) B5126237
theorem B11085265 : Blo 896573 11085265 := bstep (se 2 (by rfl) ⟨4156974, by rfl⟩ : syracuseStep 11085265 = 8313949) B8313949
theorem B960059 : Blo 896573 960059 := bstep (se 1 (by rfl) ⟨720044, by rfl⟩ : syracuseStep 960059 = 1440089) B1440089
theorem B2270855 : Blo 896573 2270855 := bstep (se 1 (by rfl) ⟨1703141, by rfl⟩ : syracuseStep 2270855 = 3406283) B3406283
theorem B16361189 : Blo 896573 16361189 := bstep (se 4 (by rfl) ⟨1533861, by rfl⟩ : syracuseStep 16361189 = 3067723) B3067723
theorem B2270987 : Blo 896573 2270987 := bstep (se 1 (by rfl) ⟨1703240, by rfl⟩ : syracuseStep 2270987 = 3406481) B3406481
theorem B1517447 : Blo 896573 1517447 := bstep (se 1 (by rfl) ⟨1138085, by rfl⟩ : syracuseStep 1517447 = 2276171) B2276171
theorem B2729929 : Blo 896573 2729929 := bstep (se 2 (by rfl) ⟨1023723, by rfl⟩ : syracuseStep 2729929 = 2047447) B2047447
theorem B5122115 : Blo 896573 5122115 := bstep (se 1 (by rfl) ⟨3841586, by rfl⟩ : syracuseStep 5122115 = 7683173) B7683173
theorem B2304119 : Blo 896573 2304119 := bstep (se 1 (by rfl) ⟨1728089, by rfl⟩ : syracuseStep 2304119 = 3456179) B3456179
theorem B2271503 : Blo 896573 2271503 := bstep (se 1 (by rfl) ⟨1703627, by rfl⟩ : syracuseStep 2271503 = 3407255) B3407255
theorem B2271635 : Blo 896573 2271635 := bstep (se 1 (by rfl) ⟨1703726, by rfl⟩ : syracuseStep 2271635 = 3407453) B3407453
theorem B1518095 : Blo 896573 1518095 := bstep (se 1 (by rfl) ⟨1138571, by rfl⟩ : syracuseStep 1518095 = 2277143) B2277143
theorem B5745181 : Blo 896573 5745181 := bstep (se 3 (by rfl) ⟨1077221, by rfl⟩ : syracuseStep 5745181 = 2154443) B2154443
theorem B6826841 : Blo 896573 6826841 := bstep (se 2 (by rfl) ⟨2560065, by rfl⟩ : syracuseStep 6826841 = 5120131) B5120131
theorem B2567065 : Blo 896573 2567065 := bstep (se 2 (by rfl) ⟨962649, by rfl⟩ : syracuseStep 2567065 = 1925299) B1925299
theorem B1518635 : Blo 896573 1518635 := bstep (se 1 (by rfl) ⟨1138976, by rfl⟩ : syracuseStep 1518635 = 2277953) B2277953
theorem B8629537 : Blo 896573 8629537 := bstep (se 2 (by rfl) ⟨3236076, by rfl⟩ : syracuseStep 8629537 = 6472153) B6472153
theorem B1519033 : Blo 896573 1519033 := bstep (se 2 (by rfl) ⟨569637, by rfl⟩ : syracuseStep 1519033 = 1139275) B1139275
theorem B2272769 : Blo 896573 2272769 := bstep (se 2 (by rfl) ⟨852288, by rfl⟩ : syracuseStep 2272769 = 1704577) B1704577
theorem B896647 : Blo 896573 896647 := bstep (se 1 (by rfl) ⟨672485, by rfl⟩ : syracuseStep 896647 = 1344971) B1344971
theorem B896655 : Blo 896573 896655 := bstep (se 1 (by rfl) ⟨672491, by rfl⟩ : syracuseStep 896655 = 1344983) B1344983
theorem B896699 : Blo 896573 896699 := bstep (se 1 (by rfl) ⟨672524, by rfl⟩ : syracuseStep 896699 = 1345049) B1345049
theorem B896775 : Blo 896573 896775 := bstep (se 1 (by rfl) ⟨672581, by rfl⟩ : syracuseStep 896775 = 1345163) B1345163
theorem B896783 : Blo 896573 896783 := bstep (se 1 (by rfl) ⟨672587, by rfl⟩ : syracuseStep 896783 = 1345175) B1345175
theorem B6827813 : Blo 896573 6827813 := bstep (se 4 (by rfl) ⟨640107, by rfl⟩ : syracuseStep 6827813 = 1280215) B1280215
theorem B896827 : Blo 896573 896827 := bstep (se 1 (by rfl) ⟨672620, by rfl⟩ : syracuseStep 896827 = 1345241) B1345241
theorem B2273143 : Blo 896573 2273143 := bstep (se 1 (by rfl) ⟨1704857, by rfl⟩ : syracuseStep 2273143 = 3409715) B3409715
theorem B896903 : Blo 896573 896903 := bstep (se 1 (by rfl) ⟨672677, by rfl⟩ : syracuseStep 896903 = 1345355) B1345355
theorem B896911 : Blo 896573 896911 := bstep (se 1 (by rfl) ⟨672683, by rfl⟩ : syracuseStep 896911 = 1345367) B1345367
theorem B896955 : Blo 896573 896955 := bstep (se 1 (by rfl) ⟨672716, by rfl⟩ : syracuseStep 896955 = 1345433) B1345433
theorem B897031 : Blo 896573 897031 := bstep (se 1 (by rfl) ⟨672773, by rfl⟩ : syracuseStep 897031 = 1345547) B1345547
theorem B897039 : Blo 896573 897039 := bstep (se 1 (by rfl) ⟨672779, by rfl⟩ : syracuseStep 897039 = 1345559) B1345559
theorem B897083 : Blo 896573 897083 := bstep (se 1 (by rfl) ⟨672812, by rfl⟩ : syracuseStep 897083 = 1345625) B1345625
theorem B897159 : Blo 896573 897159 := bstep (se 1 (by rfl) ⟨672869, by rfl⟩ : syracuseStep 897159 = 1345739) B1345739
theorem B2732167 : Blo 896573 2732167 := bstep (se 1 (by rfl) ⟨2049125, by rfl⟩ : syracuseStep 2732167 = 4098251) B4098251
theorem B897167 : Blo 896573 897167 := bstep (se 1 (by rfl) ⟨672875, by rfl⟩ : syracuseStep 897167 = 1345751) B1345751
theorem B897211 : Blo 896573 897211 := bstep (se 1 (by rfl) ⟨672908, by rfl⟩ : syracuseStep 897211 = 1345817) B1345817
theorem B897287 : Blo 896573 897287 := bstep (se 1 (by rfl) ⟨672965, by rfl⟩ : syracuseStep 897287 = 1345931) B1345931
theorem B897295 : Blo 896573 897295 := bstep (se 1 (by rfl) ⟨672971, by rfl⟩ : syracuseStep 897295 = 1345943) B1345943
theorem B2273579 : Blo 896573 2273579 := bstep (se 1 (by rfl) ⟨1705184, by rfl⟩ : syracuseStep 2273579 = 3410369) B3410369
theorem B897339 : Blo 896573 897339 := bstep (se 1 (by rfl) ⟨673004, by rfl⟩ : syracuseStep 897339 = 1346009) B1346009
theorem B897415 : Blo 896573 897415 := bstep (se 1 (by rfl) ⟨673061, by rfl⟩ : syracuseStep 897415 = 1346123) B1346123
theorem B897423 : Blo 896573 897423 := bstep (se 1 (by rfl) ⟨673067, by rfl⟩ : syracuseStep 897423 = 1346135) B1346135
theorem B3027347 : Blo 896573 3027347 := bstep (se 1 (by rfl) ⟨2270510, by rfl⟩ : syracuseStep 3027347 = 4541021) B4541021
theorem B5124505 : Blo 896573 5124505 := bstep (se 2 (by rfl) ⟨1921689, by rfl⟩ : syracuseStep 5124505 = 3843379) B3843379
theorem B897467 : Blo 896573 897467 := bstep (se 1 (by rfl) ⟨673100, by rfl⟩ : syracuseStep 897467 = 1346201) B1346201
theorem B20787677 : Blo 896573 20787677 := bstep (se 3 (by rfl) ⟨3897689, by rfl⟩ : syracuseStep 20787677 = 7795379) B7795379
theorem B897543 : Blo 896573 897543 := bstep (se 1 (by rfl) ⟨673157, by rfl⟩ : syracuseStep 897543 = 1346315) B1346315
theorem B897551 : Blo 896573 897551 := bstep (se 1 (by rfl) ⟨673163, by rfl⟩ : syracuseStep 897551 = 1346327) B1346327
theorem B897595 : Blo 896573 897595 := bstep (se 1 (by rfl) ⟨673196, by rfl⟩ : syracuseStep 897595 = 1346393) B1346393
theorem B897671 : Blo 896573 897671 := bstep (se 1 (by rfl) ⟨673253, by rfl⟩ : syracuseStep 897671 = 1346507) B1346507
theorem B897679 : Blo 896573 897679 := bstep (se 1 (by rfl) ⟨673259, by rfl⟩ : syracuseStep 897679 = 1346519) B1346519
theorem B897723 : Blo 896573 897723 := bstep (se 1 (by rfl) ⟨673292, by rfl⟩ : syracuseStep 897723 = 1346585) B1346585
theorem B3650285 : Blo 896573 3650285 := bstep (se 3 (by rfl) ⟨684428, by rfl⟩ : syracuseStep 3650285 = 1368857) B1368857
theorem B9712385 : Blo 896573 9712385 := bstep (se 2 (by rfl) ⟨3642144, by rfl⟩ : syracuseStep 9712385 = 7284289) B7284289
theorem B897799 : Blo 896573 897799 := bstep (se 1 (by rfl) ⟨673349, by rfl⟩ : syracuseStep 897799 = 1346699) B1346699
theorem B897807 : Blo 896573 897807 := bstep (se 1 (by rfl) ⟨673355, by rfl⟩ : syracuseStep 897807 = 1346711) B1346711
theorem B897851 : Blo 896573 897851 := bstep (se 1 (by rfl) ⟨673388, by rfl⟩ : syracuseStep 897851 = 1346777) B1346777
theorem B897927 : Blo 896573 897927 := bstep (se 1 (by rfl) ⟨673445, by rfl⟩ : syracuseStep 897927 = 1346891) B1346891
theorem B897935 : Blo 896573 897935 := bstep (se 1 (by rfl) ⟨673451, by rfl⟩ : syracuseStep 897935 = 1346903) B1346903
theorem B87274421 : Blo 896573 87274421 := bstep (se 5 (by rfl) ⟨4090988, by rfl⟩ : syracuseStep 87274421 = 8181977) B8181977
theorem B897979 : Blo 896573 897979 := bstep (se 1 (by rfl) ⟨673484, by rfl⟩ : syracuseStep 897979 = 1346969) B1346969
theorem B4371421 : Blo 896573 4371421 := bstep (se 3 (by rfl) ⟨819641, by rfl⟩ : syracuseStep 4371421 = 1639283) B1639283
theorem B898055 : Blo 896573 898055 := bstep (se 1 (by rfl) ⟨673541, by rfl⟩ : syracuseStep 898055 = 1347083) B1347083
theorem B898063 : Blo 896573 898063 := bstep (se 1 (by rfl) ⟨673547, by rfl⟩ : syracuseStep 898063 = 1347095) B1347095
theorem B898107 : Blo 896573 898107 := bstep (se 1 (by rfl) ⟨673580, by rfl⟩ : syracuseStep 898107 = 1347161) B1347161
theorem B2274419 : Blo 896573 2274419 := bstep (se 1 (by rfl) ⟨1705814, by rfl⟩ : syracuseStep 2274419 = 3411629) B3411629
theorem B898183 : Blo 896573 898183 := bstep (se 1 (by rfl) ⟨673637, by rfl⟩ : syracuseStep 898183 = 1347275) B1347275
theorem B2274439 : Blo 896573 2274439 := bstep (se 1 (by rfl) ⟨1705829, by rfl⟩ : syracuseStep 2274439 = 3411659) B3411659
theorem B898191 : Blo 896573 898191 := bstep (se 1 (by rfl) ⟨673643, by rfl⟩ : syracuseStep 898191 = 1347287) B1347287
theorem B898235 : Blo 896573 898235 := bstep (se 1 (by rfl) ⟨673676, by rfl⟩ : syracuseStep 898235 = 1347353) B1347353
theorem B898311 : Blo 896573 898311 := bstep (se 1 (by rfl) ⟨673733, by rfl⟩ : syracuseStep 898311 = 1347467) B1347467
theorem B2733323 : Blo 896573 2733323 := bstep (se 1 (by rfl) ⟨2049992, by rfl⟩ : syracuseStep 2733323 = 4099985) B4099985
theorem B898319 : Blo 896573 898319 := bstep (se 1 (by rfl) ⟨673739, by rfl⟩ : syracuseStep 898319 = 1347479) B1347479
theorem B898363 : Blo 896573 898363 := bstep (se 1 (by rfl) ⟨673772, by rfl⟩ : syracuseStep 898363 = 1347545) B1347545
theorem B898439 : Blo 896573 898439 := bstep (se 1 (by rfl) ⟨673829, by rfl⟩ : syracuseStep 898439 = 1347659) B1347659
theorem B898447 : Blo 896573 898447 := bstep (se 1 (by rfl) ⟨673835, by rfl⟩ : syracuseStep 898447 = 1347671) B1347671
theorem B2307475 : Blo 896573 2307475 := bstep (se 1 (by rfl) ⟨1730606, by rfl⟩ : syracuseStep 2307475 = 3461213) B3461213
theorem B2274713 : Blo 896573 2274713 := bstep (se 2 (by rfl) ⟨853017, by rfl⟩ : syracuseStep 2274713 = 1706035) B1706035
theorem B898491 : Blo 896573 898491 := bstep (se 1 (by rfl) ⟨673868, by rfl⟩ : syracuseStep 898491 = 1347737) B1347737
theorem B898567 : Blo 896573 898567 := bstep (se 1 (by rfl) ⟨673925, by rfl⟩ : syracuseStep 898567 = 1347851) B1347851
theorem B898575 : Blo 896573 898575 := bstep (se 1 (by rfl) ⟨673931, by rfl⟩ : syracuseStep 898575 = 1347863) B1347863
theorem B898619 : Blo 896573 898619 := bstep (se 1 (by rfl) ⟨673964, by rfl⟩ : syracuseStep 898619 = 1347929) B1347929
theorem B2274875 : Blo 896573 2274875 := bstep (se 1 (by rfl) ⟨1706156, by rfl⟩ : syracuseStep 2274875 = 3412313) B3412313
theorem B898695 : Blo 896573 898695 := bstep (se 1 (by rfl) ⟨674021, by rfl⟩ : syracuseStep 898695 = 1348043) B1348043
theorem B898703 : Blo 896573 898703 := bstep (se 1 (by rfl) ⟨674027, by rfl⟩ : syracuseStep 898703 = 1348055) B1348055
theorem B898747 : Blo 896573 898747 := bstep (se 1 (by rfl) ⟨674060, by rfl⟩ : syracuseStep 898747 = 1348121) B1348121
theorem B898823 : Blo 896573 898823 := bstep (se 1 (by rfl) ⟨674117, by rfl⟩ : syracuseStep 898823 = 1348235) B1348235
theorem B3028751 : Blo 896573 3028751 := bstep (se 1 (by rfl) ⟨2271563, by rfl⟩ : syracuseStep 3028751 = 4543127) B4543127
theorem B2275087 : Blo 896573 2275087 := bstep (se 1 (by rfl) ⟨1706315, by rfl⟩ : syracuseStep 2275087 = 3412631) B3412631
theorem B898831 : Blo 896573 898831 := bstep (se 1 (by rfl) ⟨674123, by rfl⟩ : syracuseStep 898831 = 1348247) B1348247
theorem B898875 : Blo 896573 898875 := bstep (se 1 (by rfl) ⟨674156, by rfl⟩ : syracuseStep 898875 = 1348313) B1348313
theorem B898951 : Blo 896573 898951 := bstep (se 1 (by rfl) ⟨674213, by rfl⟩ : syracuseStep 898951 = 1348427) B1348427
theorem B898959 : Blo 896573 898959 := bstep (se 1 (by rfl) ⟨674219, by rfl⟩ : syracuseStep 898959 = 1348439) B1348439
theorem B899003 : Blo 896573 899003 := bstep (se 1 (by rfl) ⟨674252, by rfl⟩ : syracuseStep 899003 = 1348505) B1348505
theorem B899079 : Blo 896573 899079 := bstep (se 1 (by rfl) ⟨674309, by rfl⟩ : syracuseStep 899079 = 1348619) B1348619
theorem B899087 : Blo 896573 899087 := bstep (se 1 (by rfl) ⟨674315, by rfl⟩ : syracuseStep 899087 = 1348631) B1348631
theorem B3029021 : Blo 896573 3029021 := bstep (se 3 (by rfl) ⟨567941, by rfl⟩ : syracuseStep 3029021 = 1135883) B1135883
theorem B2275361 : Blo 896573 2275361 := bstep (se 2 (by rfl) ⟨853260, by rfl⟩ : syracuseStep 2275361 = 1706521) B1706521
theorem B1849387 : Blo 896573 1849387 := bstep (se 1 (by rfl) ⟨1387040, by rfl⟩ : syracuseStep 1849387 = 2774081) B2774081
theorem B21837869 : Blo 896573 21837869 := bstep (se 3 (by rfl) ⟨4094600, by rfl⟩ : syracuseStep 21837869 = 8189201) B8189201
theorem B899131 : Blo 896573 899131 := bstep (se 1 (by rfl) ⟨674348, by rfl⟩ : syracuseStep 899131 = 1348697) B1348697
theorem B2439227 : Blo 896573 2439227 := bstep (se 1 (by rfl) ⟨1829420, by rfl⟩ : syracuseStep 2439227 = 3658841) B3658841
theorem B899207 : Blo 896573 899207 := bstep (se 1 (by rfl) ⟨674405, by rfl⟩ : syracuseStep 899207 = 1348811) B1348811
theorem B899215 : Blo 896573 899215 := bstep (se 1 (by rfl) ⟨674411, by rfl⟩ : syracuseStep 899215 = 1348823) B1348823
theorem B899259 : Blo 896573 899259 := bstep (se 1 (by rfl) ⟨674444, by rfl⟩ : syracuseStep 899259 = 1348889) B1348889
theorem B899335 : Blo 896573 899335 := bstep (se 1 (by rfl) ⟨674501, by rfl⟩ : syracuseStep 899335 = 1349003) B1349003
theorem B899343 : Blo 896573 899343 := bstep (se 1 (by rfl) ⟨674507, by rfl⟩ : syracuseStep 899343 = 1349015) B1349015
theorem B899387 : Blo 896573 899387 := bstep (se 1 (by rfl) ⟨674540, by rfl⟩ : syracuseStep 899387 = 1349081) B1349081
theorem B5126489 : Blo 896573 5126489 := bstep (se 2 (by rfl) ⟨1922433, by rfl⟩ : syracuseStep 5126489 = 3844867) B3844867
theorem B899463 : Blo 896573 899463 := bstep (se 1 (by rfl) ⟨674597, by rfl⟩ : syracuseStep 899463 = 1349195) B1349195
theorem B899471 : Blo 896573 899471 := bstep (se 1 (by rfl) ⟨674603, by rfl⟩ : syracuseStep 899471 = 1349207) B1349207
theorem B899515 : Blo 896573 899515 := bstep (se 1 (by rfl) ⟨674636, by rfl⟩ : syracuseStep 899515 = 1349273) B1349273
theorem B6928861 : Blo 896573 6928861 := bstep (se 3 (by rfl) ⟨1299161, by rfl⟩ : syracuseStep 6928861 = 2598323) B2598323
theorem B899591 : Blo 896573 899591 := bstep (se 1 (by rfl) ⟨674693, by rfl⟩ : syracuseStep 899591 = 1349387) B1349387
theorem B899599 : Blo 896573 899599 := bstep (se 1 (by rfl) ⟨674699, by rfl⟩ : syracuseStep 899599 = 1349399) B1349399
theorem B899643 : Blo 896573 899643 := bstep (se 1 (by rfl) ⟨674732, by rfl⟩ : syracuseStep 899643 = 1349465) B1349465
theorem B899719 : Blo 896573 899719 := bstep (se 1 (by rfl) ⟨674789, by rfl⟩ : syracuseStep 899719 = 1349579) B1349579
theorem B899727 : Blo 896573 899727 := bstep (se 1 (by rfl) ⟨674795, by rfl⟩ : syracuseStep 899727 = 1349591) B1349591
theorem B899771 : Blo 896573 899771 := bstep (se 1 (by rfl) ⟨674828, by rfl⟩ : syracuseStep 899771 = 1349657) B1349657
theorem B899847 : Blo 896573 899847 := bstep (se 1 (by rfl) ⟨674885, by rfl⟩ : syracuseStep 899847 = 1349771) B1349771
theorem B899855 : Blo 896573 899855 := bstep (se 1 (by rfl) ⟨674891, by rfl⟩ : syracuseStep 899855 = 1349783) B1349783
theorem B5749541 : Blo 896573 5749541 := bstep (se 4 (by rfl) ⟨539019, by rfl⟩ : syracuseStep 5749541 = 1078039) B1078039
theorem B899899 : Blo 896573 899899 := bstep (se 1 (by rfl) ⟨674924, by rfl⟩ : syracuseStep 899899 = 1349849) B1349849
theorem B899975 : Blo 896573 899975 := bstep (se 1 (by rfl) ⟨674981, by rfl⟩ : syracuseStep 899975 = 1349963) B1349963
theorem B899983 : Blo 896573 899983 := bstep (se 1 (by rfl) ⟨674987, by rfl⟩ : syracuseStep 899983 = 1349975) B1349975
theorem B900027 : Blo 896573 900027 := bstep (se 1 (by rfl) ⟨675020, by rfl⟩ : syracuseStep 900027 = 1350041) B1350041
theorem B900103 : Blo 896573 900103 := bstep (se 1 (by rfl) ⟨675077, by rfl⟩ : syracuseStep 900103 = 1350155) B1350155
theorem B2276363 : Blo 896573 2276363 := bstep (se 1 (by rfl) ⟨1707272, by rfl⟩ : syracuseStep 2276363 = 3414545) B3414545
theorem B900111 : Blo 896573 900111 := bstep (se 1 (by rfl) ⟨675083, by rfl⟩ : syracuseStep 900111 = 1350167) B1350167
theorem B900155 : Blo 896573 900155 := bstep (se 1 (by rfl) ⟨675116, by rfl⟩ : syracuseStep 900155 = 1350233) B1350233
theorem B16399421 : Blo 896573 16399421 := bstep (se 3 (by rfl) ⟨3074891, by rfl⟩ : syracuseStep 16399421 = 6149783) B6149783
theorem B900231 : Blo 896573 900231 := bstep (se 1 (by rfl) ⟨675173, by rfl⟩ : syracuseStep 900231 = 1350347) B1350347
theorem B900239 : Blo 896573 900239 := bstep (se 1 (by rfl) ⟨675179, by rfl⟩ : syracuseStep 900239 = 1350359) B1350359
theorem B900283 : Blo 896573 900283 := bstep (se 1 (by rfl) ⟨675212, by rfl⟩ : syracuseStep 900283 = 1350425) B1350425
theorem B900359 : Blo 896573 900359 := bstep (se 1 (by rfl) ⟨675269, by rfl⟩ : syracuseStep 900359 = 1350539) B1350539
theorem B900367 : Blo 896573 900367 := bstep (se 1 (by rfl) ⟨675275, by rfl⟩ : syracuseStep 900367 = 1350551) B1350551
theorem B8207675 : Blo 896573 8207675 := bstep (se 1 (by rfl) ⟨6155756, by rfl⟩ : syracuseStep 8207675 = 12311513) B12311513
theorem B900411 : Blo 896573 900411 := bstep (se 1 (by rfl) ⟨675308, by rfl⟩ : syracuseStep 900411 = 1350617) B1350617
theorem B900487 : Blo 896573 900487 := bstep (se 1 (by rfl) ⟨675365, by rfl⟩ : syracuseStep 900487 = 1350731) B1350731
theorem B900495 : Blo 896573 900495 := bstep (se 1 (by rfl) ⟨675371, by rfl⟩ : syracuseStep 900495 = 1350743) B1350743
theorem B3030425 : Blo 896573 3030425 := bstep (se 2 (by rfl) ⟨1136409, by rfl⟩ : syracuseStep 3030425 = 2272819) B2272819
theorem B900539 : Blo 896573 900539 := bstep (se 1 (by rfl) ⟨675404, by rfl⟩ : syracuseStep 900539 = 1350809) B1350809
theorem B2277011 : Blo 896573 2277011 := bstep (se 1 (by rfl) ⟨1707758, by rfl⟩ : syracuseStep 2277011 = 3415517) B3415517
theorem B2277305 : Blo 896573 2277305 := bstep (se 2 (by rfl) ⟨853989, by rfl⟩ : syracuseStep 2277305 = 1707979) B1707979
theorem B3031127 : Blo 896573 3031127 := bstep (se 1 (by rfl) ⟨2273345, by rfl⟩ : syracuseStep 3031127 = 4546691) B4546691
theorem B2310515 : Blo 896573 2310515 := bstep (se 1 (by rfl) ⟨1732886, by rfl⟩ : syracuseStep 2310515 = 3465773) B3465773
theorem B4866571 : Blo 896573 4866571 := bstep (se 1 (by rfl) ⟨3649928, by rfl⟩ : syracuseStep 4866571 = 7299857) B7299857
theorem B39338531 : Blo 896573 39338531 := bstep (se 1 (by rfl) ⟨29503898, by rfl⟩ : syracuseStep 39338531 = 59007797) B59007797
theorem B3031613 : Blo 896573 3031613 := bstep (se 3 (by rfl) ⟨568427, by rfl⟩ : syracuseStep 3031613 = 1136855) B1136855
theorem B2278003 : Blo 896573 2278003 := bstep (se 1 (by rfl) ⟨1708502, by rfl⟩ : syracuseStep 2278003 = 3417005) B3417005
theorem B2278145 : Blo 896573 2278145 := bstep (se 2 (by rfl) ⟨854304, by rfl⟩ : syracuseStep 2278145 = 1708609) B1708609
theorem B11682575 : Blo 896573 11682575 := bstep (se 1 (by rfl) ⟨8761931, by rfl⟩ : syracuseStep 11682575 = 17523863) B17523863
theorem B4309793 : Blo 896573 4309793 := bstep (se 2 (by rfl) ⟨1616172, by rfl⟩ : syracuseStep 4309793 = 3232345) B3232345
theorem B15352739 : Blo 896573 15352739 := bstep (se 1 (by rfl) ⟨11514554, by rfl⟩ : syracuseStep 15352739 = 23029109) B23029109
theorem B5194775 : Blo 896573 5194775 := bstep (se 1 (by rfl) ⟨3896081, by rfl⟩ : syracuseStep 5194775 = 7792163) B7792163
theorem B2278601 : Blo 896573 2278601 := bstep (se 2 (by rfl) ⟨854475, by rfl⟩ : syracuseStep 2278601 = 1708951) B1708951
theorem B17515757 : Blo 896573 17515757 := bstep (se 3 (by rfl) ⟨3284204, by rfl⟩ : syracuseStep 17515757 = 6568409) B6568409
theorem B3687713 : Blo 896573 3687713 := bstep (se 2 (by rfl) ⟨1382892, by rfl⟩ : syracuseStep 3687713 = 2765785) B2765785
theorem B1918409 : Blo 896573 1918409 := bstep (se 2 (by rfl) ⟨719403, by rfl⟩ : syracuseStep 1918409 = 1438807) B1438807
theorem B2278955 : Blo 896573 2278955 := bstep (se 1 (by rfl) ⟨1709216, by rfl⟩ : syracuseStep 2278955 = 3418433) B3418433
theorem B1295929 : Blo 896573 1295929 := bstep (se 2 (by rfl) ⟨485973, by rfl⟩ : syracuseStep 1295929 = 971947) B971947
theorem B1918649 : Blo 896573 1918649 := bstep (se 2 (by rfl) ⟨719493, by rfl⟩ : syracuseStep 1918649 = 1438987) B1438987
theorem B4540211 : Blo 896573 4540211 := bstep (se 1 (by rfl) ⟨3405158, by rfl⟩ : syracuseStep 4540211 = 6810317) B6810317
theorem B4867955 : Blo 896573 4867955 := bstep (se 1 (by rfl) ⟨3650966, by rfl⟩ : syracuseStep 4867955 = 7301933) B7301933
theorem B1296263 : Blo 896573 1296263 := bstep (se 1 (by rfl) ⟨972197, by rfl⟩ : syracuseStep 1296263 = 1944395) B1944395
theorem B3033017 : Blo 896573 3033017 := bstep (se 2 (by rfl) ⟨1137381, by rfl⟩ : syracuseStep 3033017 = 2274763) B2274763
theorem B2017295 : Blo 896573 2017295 := bstep (se 1 (by rfl) ⟨1512971, by rfl⟩ : syracuseStep 2017295 = 3025943) B3025943
theorem B1918991 : Blo 896573 1918991 := bstep (se 1 (by rfl) ⟨1439243, by rfl⟩ : syracuseStep 1918991 = 2878487) B2878487
theorem B2017313 : Blo 896573 2017313 := bstep (se 2 (by rfl) ⟨756492, by rfl⟩ : syracuseStep 2017313 = 1512985) B1512985
theorem B4540535 : Blo 896573 4540535 := bstep (se 1 (by rfl) ⟨3405401, by rfl⟩ : syracuseStep 4540535 = 6810803) B6810803
theorem B1919161 : Blo 896573 1919161 := bstep (se 2 (by rfl) ⟨719685, by rfl⟩ : syracuseStep 1919161 = 1439371) B1439371
theorem B8735035 : Blo 896573 8735035 := bstep (se 1 (by rfl) ⟨6551276, by rfl⟩ : syracuseStep 8735035 = 13102553) B13102553
theorem B2017655 : Blo 896573 2017655 := bstep (se 1 (by rfl) ⟨1513241, by rfl⟩ : syracuseStep 2017655 = 3026483) B3026483
theorem B10242449 : Blo 896573 10242449 := bstep (se 2 (by rfl) ⟨3840918, by rfl⟩ : syracuseStep 10242449 = 7681837) B7681837
theorem B6834617 : Blo 896573 6834617 := bstep (se 2 (by rfl) ⟨2562981, by rfl⟩ : syracuseStep 6834617 = 5125963) B5125963
theorem B3033611 : Blo 896573 3033611 := bstep (se 1 (by rfl) ⟨2275208, by rfl⟩ : syracuseStep 3033611 = 4550417) B4550417
theorem B2017835 : Blo 896573 2017835 := bstep (se 1 (by rfl) ⟨1513376, by rfl⟩ : syracuseStep 2017835 = 3026753) B3026753
theorem B3033719 : Blo 896573 3033719 := bstep (se 1 (by rfl) ⟨2275289, by rfl⟩ : syracuseStep 3033719 = 4550579) B4550579
theorem B1821575 : Blo 896573 1821575 := bstep (se 1 (by rfl) ⟨1366181, by rfl⟩ : syracuseStep 1821575 = 2732363) B2732363
theorem B1919879 : Blo 896573 1919879 := bstep (se 1 (by rfl) ⟨1439909, by rfl⟩ : syracuseStep 1919879 = 2879819) B2879819
theorem B2018195 : Blo 896573 2018195 := bstep (se 1 (by rfl) ⟨1513646, by rfl⟩ : syracuseStep 2018195 = 3027293) B3027293
theorem B2018249 : Blo 896573 2018249 := bstep (se 2 (by rfl) ⟨756843, by rfl⟩ : syracuseStep 2018249 = 1513687) B1513687
theorem B4541507 : Blo 896573 4541507 := bstep (se 1 (by rfl) ⟨3406130, by rfl⟩ : syracuseStep 4541507 = 6812261) B6812261
theorem B3034313 : Blo 896573 3034313 := bstep (se 2 (by rfl) ⟨1137867, by rfl⟩ : syracuseStep 3034313 = 2275735) B2275735
theorem B1920289 : Blo 896573 1920289 := bstep (se 2 (by rfl) ⟨720108, by rfl⟩ : syracuseStep 1920289 = 1440217) B1440217
theorem B1756475 : Blo 896573 1756475 := bstep (se 1 (by rfl) ⟨1317356, by rfl⟩ : syracuseStep 1756475 = 2634713) B2634713
theorem B4541831 : Blo 896573 4541831 := bstep (se 1 (by rfl) ⟨3406373, by rfl⟩ : syracuseStep 4541831 = 6812747) B6812747
theorem B1920631 : Blo 896573 1920631 := bstep (se 1 (by rfl) ⟨1440473, by rfl⟩ : syracuseStep 1920631 = 2880947) B2880947
theorem B2018951 : Blo 896573 2018951 := bstep (se 1 (by rfl) ⟨1514213, by rfl⟩ : syracuseStep 2018951 = 3028427) B3028427
theorem B2019131 : Blo 896573 2019131 := bstep (se 1 (by rfl) ⟨1514348, by rfl⟩ : syracuseStep 2019131 = 3028697) B3028697
theorem B3035015 : Blo 896573 3035015 := bstep (se 1 (by rfl) ⟨2276261, by rfl⟩ : syracuseStep 3035015 = 4552523) B4552523
theorem B2019257 : Blo 896573 2019257 := bstep (se 2 (by rfl) ⟨757221, by rfl⟩ : syracuseStep 2019257 = 1514443) B1514443
theorem B1921067 : Blo 896573 1921067 := bstep (se 1 (by rfl) ⟨1440800, by rfl⟩ : syracuseStep 1921067 = 2881601) B2881601
theorem B3035393 : Blo 896573 3035393 := bstep (se 2 (by rfl) ⟨1138272, by rfl⟩ : syracuseStep 3035393 = 2276545) B2276545
theorem B2019599 : Blo 896573 2019599 := bstep (se 1 (by rfl) ⟨1514699, by rfl⟩ : syracuseStep 2019599 = 3029399) B3029399
theorem B2019617 : Blo 896573 2019617 := bstep (se 2 (by rfl) ⟨757356, by rfl⟩ : syracuseStep 2019617 = 1514713) B1514713
theorem B1134967 : Blo 896573 1134967 := bstep (se 1 (by rfl) ⟨851225, by rfl⟩ : syracuseStep 1134967 = 1702451) B1702451
theorem B2019959 : Blo 896573 2019959 := bstep (se 1 (by rfl) ⟨1514969, by rfl⟩ : syracuseStep 2019959 = 3029939) B3029939
theorem B1135291 : Blo 896573 1135291 := bstep (se 1 (by rfl) ⟨851468, by rfl⟩ : syracuseStep 1135291 = 1702937) B1702937
theorem B2020139 : Blo 896573 2020139 := bstep (se 1 (by rfl) ⟨1515104, by rfl⟩ : syracuseStep 2020139 = 3030209) B3030209
theorem B3036203 : Blo 896573 3036203 := bstep (se 1 (by rfl) ⟨2277152, by rfl⟩ : syracuseStep 3036203 = 4554305) B4554305
theorem B2020499 : Blo 896573 2020499 := bstep (se 1 (by rfl) ⟨1515374, by rfl⟩ : syracuseStep 2020499 = 3030749) B3030749
theorem B2020553 : Blo 896573 2020553 := bstep (se 2 (by rfl) ⟨757707, by rfl⟩ : syracuseStep 2020553 = 1515415) B1515415
theorem B10245365 : Blo 896573 10245365 := bstep (se 5 (by rfl) ⟨480251, by rfl⟩ : syracuseStep 10245365 = 960503) B960503
theorem B5756305 : Blo 896573 5756305 := bstep (se 2 (by rfl) ⟨2158614, by rfl⟩ : syracuseStep 5756305 = 4317229) B4317229
theorem B34952627 : Blo 896573 34952627 := bstep (se 1 (by rfl) ⟨26214470, by rfl⟩ : syracuseStep 34952627 = 52428941) B52428941
theorem B1136263 : Blo 896573 1136263 := bstep (se 1 (by rfl) ⟨852197, by rfl⟩ : syracuseStep 1136263 = 1704395) B1704395
theorem B1922707 : Blo 896573 1922707 := bstep (se 1 (by rfl) ⟨1442030, by rfl⟩ : syracuseStep 1922707 = 2884061) B2884061
theorem B2021255 : Blo 896573 2021255 := bstep (se 1 (by rfl) ⟨1515941, by rfl⟩ : syracuseStep 2021255 = 3031883) B3031883
theorem B1136683 : Blo 896573 1136683 := bstep (se 1 (by rfl) ⟨852512, by rfl⟩ : syracuseStep 1136683 = 1705025) B1705025
theorem B2021435 : Blo 896573 2021435 := bstep (se 1 (by rfl) ⟨1516076, by rfl⟩ : syracuseStep 2021435 = 3032153) B3032153
theorem B2021561 : Blo 896573 2021561 := bstep (se 2 (by rfl) ⟨758085, by rfl⟩ : syracuseStep 2021561 = 1516171) B1516171
theorem B1136911 : Blo 896573 1136911 := bstep (se 1 (by rfl) ⟨852683, by rfl⟩ : syracuseStep 1136911 = 1705367) B1705367
theorem B3037499 : Blo 896573 3037499 := bstep (se 1 (by rfl) ⟨2278124, by rfl⟩ : syracuseStep 3037499 = 4556249) B4556249
theorem B2021903 : Blo 896573 2021903 := bstep (se 1 (by rfl) ⟨1516427, by rfl⟩ : syracuseStep 2021903 = 3032855) B3032855
theorem B2021921 : Blo 896573 2021921 := bstep (se 2 (by rfl) ⟨758220, by rfl⟩ : syracuseStep 2021921 = 1516441) B1516441
theorem B3037985 : Blo 896573 3037985 := bstep (se 2 (by rfl) ⟨1139244, by rfl⟩ : syracuseStep 3037985 = 2278489) B2278489
theorem B4545395 : Blo 896573 4545395 := bstep (se 1 (by rfl) ⟨3409046, by rfl⟩ : syracuseStep 4545395 = 6818093) B6818093
theorem B2022263 : Blo 896573 2022263 := bstep (se 1 (by rfl) ⟨1516697, by rfl⟩ : syracuseStep 2022263 = 3033395) B3033395
theorem B4316113 : Blo 896573 4316113 := bstep (se 2 (by rfl) ⟨1618542, by rfl⟩ : syracuseStep 4316113 = 3237085) B3237085
theorem B1137655 : Blo 896573 1137655 := bstep (se 1 (by rfl) ⟨853241, by rfl⟩ : syracuseStep 1137655 = 1706483) B1706483
theorem B2022443 : Blo 896573 2022443 := bstep (se 1 (by rfl) ⟨1516832, by rfl⟩ : syracuseStep 2022443 = 3033665) B3033665
theorem B1137979 : Blo 896573 1137979 := bstep (se 1 (by rfl) ⟨853484, by rfl⟩ : syracuseStep 1137979 = 1706969) B1706969
theorem B4545881 : Blo 896573 4545881 := bstep (se 2 (by rfl) ⟨1704705, by rfl⟩ : syracuseStep 4545881 = 3409411) B3409411
theorem B3038579 : Blo 896573 3038579 := bstep (se 1 (by rfl) ⟨2278934, by rfl⟩ : syracuseStep 3038579 = 4557869) B4557869
theorem B2022803 : Blo 896573 2022803 := bstep (se 1 (by rfl) ⟨1517102, by rfl⟩ : syracuseStep 2022803 = 3034205) B3034205
theorem B2022857 : Blo 896573 2022857 := bstep (se 2 (by rfl) ⟨758571, by rfl⟩ : syracuseStep 2022857 = 1517143) B1517143
theorem B908987 : Blo 896573 908987 := bstep (se 1 (by rfl) ⟨681740, by rfl⟩ : syracuseStep 908987 = 1363481) B1363481
theorem B1138475 : Blo 896573 1138475 := bstep (se 1 (by rfl) ⟨853856, by rfl⟩ : syracuseStep 1138475 = 1707713) B1707713
theorem B2875283 : Blo 896573 2875283 := bstep (se 1 (by rfl) ⟨2156462, by rfl⟩ : syracuseStep 2875283 = 4312925) B4312925
theorem B12443543 : Blo 896573 12443543 := bstep (se 1 (by rfl) ⟨9332657, by rfl⟩ : syracuseStep 12443543 = 18665315) B18665315
theorem B2023559 : Blo 896573 2023559 := bstep (se 1 (by rfl) ⟨1517669, by rfl⟩ : syracuseStep 2023559 = 3035339) B3035339
theorem B1728697 : Blo 896573 1728697 := bstep (se 2 (by rfl) ⟨648261, by rfl⟩ : syracuseStep 1728697 = 1296523) B1296523
theorem B1138951 : Blo 896573 1138951 := bstep (se 1 (by rfl) ⟨854213, by rfl⟩ : syracuseStep 1138951 = 1708427) B1708427
theorem B1368335 : Blo 896573 1368335 := bstep (se 1 (by rfl) ⟨1026251, by rfl⟩ : syracuseStep 1368335 = 2052503) B2052503
theorem B2023739 : Blo 896573 2023739 := bstep (se 1 (by rfl) ⟨1517804, by rfl⟩ : syracuseStep 2023739 = 3035609) B3035609
theorem B2023865 : Blo 896573 2023865 := bstep (se 2 (by rfl) ⟨758949, by rfl⟩ : syracuseStep 2023865 = 1517899) B1517899
theorem B18407897 : Blo 896573 18407897 := bstep (se 2 (by rfl) ⟨6902961, by rfl⟩ : syracuseStep 18407897 = 13805923) B13805923
theorem B1139447 : Blo 896573 1139447 := bstep (se 1 (by rfl) ⟨854585, by rfl⟩ : syracuseStep 1139447 = 1709171) B1709171
theorem B2024207 : Blo 896573 2024207 := bstep (se 1 (by rfl) ⟨1518155, by rfl⟩ : syracuseStep 2024207 = 3036311) B3036311
theorem B2024225 : Blo 896573 2024225 := bstep (se 2 (by rfl) ⟨759084, by rfl⟩ : syracuseStep 2024225 = 1518169) B1518169
theorem B1139599 : Blo 896573 1139599 := bstep (se 1 (by rfl) ⟨854699, by rfl⟩ : syracuseStep 1139599 = 1709399) B1709399
theorem B1139771 : Blo 896573 1139771 := bstep (se 1 (by rfl) ⟨854828, by rfl⟩ : syracuseStep 1139771 = 1709657) B1709657
theorem B2024567 : Blo 896573 2024567 := bstep (se 1 (by rfl) ⟨1518425, by rfl⟩ : syracuseStep 2024567 = 3036851) B3036851
theorem B8185121 : Blo 896573 8185121 := bstep (se 2 (by rfl) ⟨3069420, by rfl⟩ : syracuseStep 8185121 = 6138841) B6138841
theorem B2024747 : Blo 896573 2024747 := bstep (se 1 (by rfl) ⟨1518560, by rfl⟩ : syracuseStep 2024747 = 3037121) B3037121
theorem B1009039 : Blo 896573 1009039 := bstep (se 1 (by rfl) ⟨756779, by rfl⟩ : syracuseStep 1009039 = 1513559) B1513559
theorem B4547987 : Blo 896573 4547987 := bstep (se 1 (by rfl) ⟨3410990, by rfl⟩ : syracuseStep 4547987 = 6821981) B6821981
theorem B4384343 : Blo 896573 4384343 := bstep (se 1 (by rfl) ⟨3288257, by rfl⟩ : syracuseStep 4384343 = 6576515) B6576515
theorem B2025107 : Blo 896573 2025107 := bstep (se 1 (by rfl) ⟨1518830, by rfl⟩ : syracuseStep 2025107 = 3037661) B3037661
theorem B2025161 : Blo 896573 2025161 := bstep (se 2 (by rfl) ⟨759435, by rfl⟩ : syracuseStep 2025161 = 1518871) B1518871
theorem B6809345 : Blo 896573 6809345 := bstep (se 2 (by rfl) ⟨2553504, by rfl⟩ : syracuseStep 6809345 = 5107009) B5107009
theorem B1009543 : Blo 896573 1009543 := bstep (se 1 (by rfl) ⟨757157, by rfl⟩ : syracuseStep 1009543 = 1514315) B1514315
theorem B1009723 : Blo 896573 1009723 := bstep (se 1 (by rfl) ⟨757292, by rfl⟩ : syracuseStep 1009723 = 1514585) B1514585
theorem B2025863 : Blo 896573 2025863 := bstep (se 1 (by rfl) ⟨1519397, by rfl⟩ : syracuseStep 2025863 = 3038795) B3038795
theorem B1010191 : Blo 896573 1010191 := bstep (se 1 (by rfl) ⟨757643, by rfl⟩ : syracuseStep 1010191 = 1515287) B1515287
theorem B1436219 : Blo 896573 1436219 := bstep (se 1 (by rfl) ⟨1077164, by rfl⟩ : syracuseStep 1436219 = 2154329) B2154329
theorem B2026043 : Blo 896573 2026043 := bstep (se 1 (by rfl) ⟨1519532, by rfl⟩ : syracuseStep 2026043 = 3039065) B3039065
theorem B2026169 : Blo 896573 2026169 := bstep (se 2 (by rfl) ⟨759813, by rfl⟩ : syracuseStep 2026169 = 1519627) B1519627
theorem B1010695 : Blo 896573 1010695 := bstep (se 1 (by rfl) ⟨758021, by rfl⟩ : syracuseStep 1010695 = 1516043) B1516043
theorem B1010875 : Blo 896573 1010875 := bstep (se 1 (by rfl) ⟨758156, by rfl⟩ : syracuseStep 1010875 = 1516313) B1516313
theorem B3894713 : Blo 896573 3894713 := bstep (se 2 (by rfl) ⟨1460517, by rfl⟩ : syracuseStep 3894713 = 2921035) B2921035
theorem B1011343 : Blo 896573 1011343 := bstep (se 1 (by rfl) ⟨758507, by rfl⟩ : syracuseStep 1011343 = 1517015) B1517015
theorem B4091681 : Blo 896573 4091681 := bstep (se 2 (by rfl) ⟨1534380, by rfl⟩ : syracuseStep 4091681 = 3068761) B3068761
theorem B1109819 : Blo 896573 1109819 := bstep (se 1 (by rfl) ⟨832364, by rfl⟩ : syracuseStep 1109819 = 1664729) B1664729
theorem B1011847 : Blo 896573 1011847 := bstep (se 1 (by rfl) ⟨758885, by rfl⟩ : syracuseStep 1011847 = 1517771) B1517771
theorem B6484205 : Blo 896573 6484205 := bstep (se 3 (by rfl) ⟨1215788, by rfl⟩ : syracuseStep 6484205 = 2431577) B2431577
theorem B1012027 : Blo 896573 1012027 := bstep (se 1 (by rfl) ⟨759020, by rfl⟩ : syracuseStep 1012027 = 1518041) B1518041
theorem B10908035 : Blo 896573 10908035 := bstep (se 1 (by rfl) ⟨8181026, by rfl⟩ : syracuseStep 10908035 = 16362053) B16362053
theorem B4551065 : Blo 896573 4551065 := bstep (se 2 (by rfl) ⟨1706649, by rfl⟩ : syracuseStep 4551065 = 3413299) B3413299
theorem B11497949 : Blo 896573 11497949 := bstep (se 3 (by rfl) ⟨2155865, by rfl⟩ : syracuseStep 11497949 = 4311731) B4311731
theorem B5108285 : Blo 896573 5108285 := bstep (se 3 (by rfl) ⟨957803, by rfl⟩ : syracuseStep 5108285 = 1915607) B1915607
theorem B1077895 : Blo 896573 1077895 := bstep (se 1 (by rfl) ⟨808421, by rfl⟩ : syracuseStep 1077895 = 1616843) B1616843
theorem B12972737 : Blo 896573 12972737 := bstep (se 2 (by rfl) ⟨4864776, by rfl⟩ : syracuseStep 12972737 = 9729553) B9729553
theorem B3240719 : Blo 896573 3240719 := bstep (se 1 (by rfl) ⟨2430539, by rfl⟩ : syracuseStep 3240719 = 4861079) B4861079
theorem B1012495 : Blo 896573 1012495 := bstep (se 1 (by rfl) ⟨759371, by rfl⟩ : syracuseStep 1012495 = 1518743) B1518743
theorem B28079075 : Blo 896573 28079075 := bstep (se 1 (by rfl) ⟨21059306, by rfl⟩ : syracuseStep 28079075 = 42118613) B42118613
theorem B3405037 : Blo 896573 3405037 := bstep (se 3 (by rfl) ⟨638444, by rfl⟩ : syracuseStep 3405037 = 1276889) B1276889
theorem B5108993 : Blo 896573 5108993 := bstep (se 2 (by rfl) ⟨1915872, by rfl⟩ : syracuseStep 5108993 = 3831745) B3831745
theorem B1012999 : Blo 896573 1012999 := bstep (se 1 (by rfl) ⟨759749, by rfl⟩ : syracuseStep 1012999 = 1519499) B1519499
theorem B5469491 : Blo 896573 5469491 := bstep (se 1 (by rfl) ⟨4102118, by rfl⟩ : syracuseStep 5469491 = 8204237) B8204237
theorem B3405341 : Blo 896573 3405341 := bstep (se 3 (by rfl) ⟨638501, by rfl⟩ : syracuseStep 3405341 = 1277003) B1277003
theorem B2553403 : Blo 896573 2553403 := bstep (se 1 (by rfl) ⟨1915052, by rfl⟩ : syracuseStep 2553403 = 3830105) B3830105
theorem B15365861 : Blo 896573 15365861 := bstep (se 4 (by rfl) ⟨1440549, by rfl⟩ : syracuseStep 15365861 = 2881099) B2881099
theorem B3700615 : Blo 896573 3700615 := bstep (se 1 (by rfl) ⟨2775461, by rfl⟩ : syracuseStep 3700615 = 5550923) B5550923
theorem B2881433 : Blo 896573 2881433 := bstep (se 2 (by rfl) ⟨1080537, by rfl⟩ : syracuseStep 2881433 = 2161075) B2161075
theorem B5339033 : Blo 896573 5339033 := bstep (se 2 (by rfl) ⟨2002137, by rfl⟩ : syracuseStep 5339033 = 4004275) B4004275
theorem B3831761 : Blo 896573 3831761 := bstep (se 2 (by rfl) ⟨1436910, by rfl⟩ : syracuseStep 3831761 = 2873821) B2873821
theorem B6813719 : Blo 896573 6813719 := bstep (se 1 (by rfl) ⟨5110289, by rfl⟩ : syracuseStep 6813719 = 10220579) B10220579
theorem B3242045 : Blo 896573 3242045 := bstep (se 3 (by rfl) ⟨607883, by rfl⟩ : syracuseStep 3242045 = 1215767) B1215767
theorem B1702291 : Blo 896573 1702291 := bstep (se 1 (by rfl) ⟨1276718, by rfl⟩ : syracuseStep 1702291 = 2553437) B2553437
theorem B1440185 : Blo 896573 1440185 := bstep (se 2 (by rfl) ⟨540069, by rfl⟩ : syracuseStep 1440185 = 1080139) B1080139
theorem B1079951 : Blo 896573 1079951 := bstep (se 1 (by rfl) ⟨809963, by rfl⟩ : syracuseStep 1079951 = 1619927) B1619927
theorem B2554553 : Blo 896573 2554553 := bstep (se 2 (by rfl) ⟨957957, by rfl⟩ : syracuseStep 2554553 = 1915915) B1915915
theorem B4324033 : Blo 896573 4324033 := bstep (se 2 (by rfl) ⟨1621512, by rfl⟩ : syracuseStep 4324033 = 3243025) B3243025
theorem B3242767 : Blo 896573 3242767 := bstep (se 1 (by rfl) ⟨2432075, by rfl⟩ : syracuseStep 3242767 = 4864151) B4864151
theorem B4553657 : Blo 896573 4553657 := bstep (se 2 (by rfl) ⟨1707621, by rfl⟩ : syracuseStep 4553657 = 3415243) B3415243
theorem B2554895 : Blo 896573 2554895 := bstep (se 1 (by rfl) ⟨1916171, by rfl⟩ : syracuseStep 2554895 = 3832343) B3832343
theorem B3406967 : Blo 896573 3406967 := bstep (se 1 (by rfl) ⟨2555225, by rfl⟩ : syracuseStep 3406967 = 5110451) B5110451
theorem B9862345 : Blo 896573 9862345 := bstep (se 2 (by rfl) ⟨3698379, by rfl⟩ : syracuseStep 9862345 = 7396759) B7396759
theorem B4848929 : Blo 896573 4848929 := bstep (se 2 (by rfl) ⟨1818348, by rfl⟩ : syracuseStep 4848929 = 3636697) B3636697
theorem B1703369 : Blo 896573 1703369 := bstep (se 2 (by rfl) ⟨638763, by rfl⟩ : syracuseStep 1703369 = 1277527) B1277527
theorem B4095517 : Blo 896573 4095517 := bstep (se 3 (by rfl) ⟨767909, by rfl⟩ : syracuseStep 4095517 = 1535819) B1535819
theorem B2162209 : Blo 896573 2162209 := bstep (se 2 (by rfl) ⟨810828, by rfl⟩ : syracuseStep 2162209 = 1621657) B1621657
theorem B5111383 : Blo 896573 5111383 := bstep (se 1 (by rfl) ⟨3833537, by rfl⟩ : syracuseStep 5111383 = 7667075) B7667075
theorem B10944193 : Blo 896573 10944193 := bstep (se 2 (by rfl) ⟨4104072, by rfl⟩ : syracuseStep 10944193 = 8208145) B8208145
theorem B1277641 : Blo 896573 1277641 := bstep (se 2 (by rfl) ⟨479115, by rfl⟩ : syracuseStep 1277641 = 958231) B958231
theorem B6913829 : Blo 896573 6913829 := bstep (se 4 (by rfl) ⟨648171, by rfl⟩ : syracuseStep 6913829 = 1296343) B1296343
theorem B13860659 : Blo 896573 13860659 := bstep (se 1 (by rfl) ⟨10395494, by rfl⟩ : syracuseStep 13860659 = 20790989) B20790989
theorem B15335243 : Blo 896573 15335243 := bstep (se 1 (by rfl) ⟨11501432, by rfl⟩ : syracuseStep 15335243 = 23002865) B23002865
theorem B2555783 : Blo 896573 2555783 := bstep (se 1 (by rfl) ⟨1916837, by rfl⟩ : syracuseStep 2555783 = 3833675) B3833675
theorem B3407953 : Blo 896573 3407953 := bstep (se 2 (by rfl) ⟨1277982, by rfl⟩ : syracuseStep 3407953 = 2555965) B2555965
theorem B5767325 : Blo 896573 5767325 := bstep (se 3 (by rfl) ⟨1081373, by rfl⟩ : syracuseStep 5767325 = 2162747) B2162747
theorem B1540343 : Blo 896573 1540343 := bstep (se 1 (by rfl) ⟨1155257, by rfl⟩ : syracuseStep 1540343 = 2310515) B2310515
theorem B3408257 : Blo 896573 3408257 := bstep (se 2 (by rfl) ⟨1278096, by rfl⟩ : syracuseStep 3408257 = 2556193) B2556193
theorem B9700013 : Blo 896573 9700013 := bstep (se 3 (by rfl) ⟨1818752, by rfl⟩ : syracuseStep 9700013 = 3637505) B3637505
theorem B6488761 : Blo 896573 6488761 := bstep (se 2 (by rfl) ⟨2433285, by rfl⟩ : syracuseStep 6488761 = 4866571) B4866571
theorem B5767939 : Blo 896573 5767939 := bstep (se 1 (by rfl) ⟨4325954, by rfl⟩ : syracuseStep 5767939 = 8651909) B8651909
theorem B3408713 : Blo 896573 3408713 := bstep (se 2 (by rfl) ⟨1278267, by rfl⟩ : syracuseStep 3408713 = 2556535) B2556535
theorem B2458475 : Blo 896573 2458475 := bstep (se 1 (by rfl) ⟨1843856, by rfl⟩ : syracuseStep 2458475 = 3687713) B3687713
theorem B2884535 : Blo 896573 2884535 := bstep (se 1 (by rfl) ⟨2163401, by rfl⟩ : syracuseStep 2884535 = 4326803) B4326803
theorem B1278985 : Blo 896573 1278985 := bstep (se 2 (by rfl) ⟨479619, by rfl⟩ : syracuseStep 1278985 = 959239) B959239
theorem B3408911 : Blo 896573 3408911 := bstep (se 1 (by rfl) ⟨2556683, by rfl⟩ : syracuseStep 3408911 = 5113367) B5113367
theorem B1704979 : Blo 896573 1704979 := bstep (se 1 (by rfl) ⟨1278734, by rfl⟩ : syracuseStep 1704979 = 2557469) B2557469
theorem B1279099 : Blo 896573 1279099 := bstep (se 1 (by rfl) ⟨959324, by rfl⟩ : syracuseStep 1279099 = 1918649) B1918649
theorem B1705207 : Blo 896573 1705207 := bstep (se 1 (by rfl) ⟨1278905, by rfl⟩ : syracuseStep 1705207 = 2557811) B2557811
theorem B3245303 : Blo 896573 3245303 := bstep (se 1 (by rfl) ⟨2433977, by rfl⟩ : syracuseStep 3245303 = 4867955) B4867955
theorem B1344863 : Blo 896573 1344863 := bstep (se 1 (by rfl) ⟨1008647, by rfl⟩ : syracuseStep 1344863 = 2017295) B2017295
theorem B1279327 : Blo 896573 1279327 := bstep (se 1 (by rfl) ⟨959495, by rfl⟩ : syracuseStep 1279327 = 1918991) B1918991
theorem B1344875 : Blo 896573 1344875 := bstep (se 1 (by rfl) ⟨1008656, by rfl⟩ : syracuseStep 1344875 = 2017313) B2017313
theorem B1705511 : Blo 896573 1705511 := bstep (se 1 (by rfl) ⟨1279133, by rfl⟩ : syracuseStep 1705511 = 2558267) B2558267
theorem B1345103 : Blo 896573 1345103 := bstep (se 1 (by rfl) ⟨1008827, by rfl⟩ : syracuseStep 1345103 = 2017655) B2017655
theorem B6555259 : Blo 896573 6555259 := bstep (se 1 (by rfl) ⟨4916444, by rfl⟩ : syracuseStep 6555259 = 9832889) B9832889
theorem B4556411 : Blo 896573 4556411 := bstep (se 1 (by rfl) ⟨3417308, by rfl⟩ : syracuseStep 4556411 = 6834617) B6834617
theorem B1345223 : Blo 896573 1345223 := bstep (se 1 (by rfl) ⟨1008917, by rfl⟩ : syracuseStep 1345223 = 2017835) B2017835
theorem B2557651 : Blo 896573 2557651 := bstep (se 1 (by rfl) ⟨1918238, by rfl⟩ : syracuseStep 2557651 = 3836477) B3836477
theorem B5768941 : Blo 896573 5768941 := bstep (se 3 (by rfl) ⟨1081676, by rfl⟩ : syracuseStep 5768941 = 2163353) B2163353
theorem B1345385 : Blo 896573 1345385 := bstep (se 2 (by rfl) ⟨504519, by rfl⟩ : syracuseStep 1345385 = 1009039) B1009039
theorem B11536289 : Blo 896573 11536289 := bstep (se 2 (by rfl) ⟨4326108, by rfl⟩ : syracuseStep 11536289 = 8652217) B8652217
theorem B1279919 : Blo 896573 1279919 := bstep (se 1 (by rfl) ⟨959939, by rfl⟩ : syracuseStep 1279919 = 1919879) B1919879
theorem B1345463 : Blo 896573 1345463 := bstep (se 1 (by rfl) ⟨1009097, by rfl⟩ : syracuseStep 1345463 = 2018195) B2018195
theorem B9734093 : Blo 896573 9734093 := bstep (se 3 (by rfl) ⟨1825142, by rfl⟩ : syracuseStep 9734093 = 3650285) B3650285
theorem B1345499 : Blo 896573 1345499 := bstep (se 1 (by rfl) ⟨1009124, by rfl⟩ : syracuseStep 1345499 = 2018249) B2018249
theorem B1313119 : Blo 896573 1313119 := bstep (se 1 (by rfl) ⟨984839, by rfl⟩ : syracuseStep 1313119 = 1969679) B1969679
theorem B1345967 : Blo 896573 1345967 := bstep (se 1 (by rfl) ⟨1009475, by rfl⟩ : syracuseStep 1345967 = 2018951) B2018951
theorem B1346057 : Blo 896573 1346057 := bstep (se 2 (by rfl) ⟨504771, by rfl⟩ : syracuseStep 1346057 = 1009543) B1009543
theorem B1346087 : Blo 896573 1346087 := bstep (se 1 (by rfl) ⟨1009565, by rfl⟩ : syracuseStep 1346087 = 2019131) B2019131
theorem B3639905 : Blo 896573 3639905 := bstep (se 2 (by rfl) ⟨1364964, by rfl⟩ : syracuseStep 3639905 = 2729929) B2729929
theorem B1346171 : Blo 896573 1346171 := bstep (se 1 (by rfl) ⟨1009628, by rfl⟩ : syracuseStep 1346171 = 2019257) B2019257
theorem B1280711 : Blo 896573 1280711 := bstep (se 1 (by rfl) ⟨960533, by rfl⟩ : syracuseStep 1280711 = 1921067) B1921067
theorem B1346297 : Blo 896573 1346297 := bstep (se 2 (by rfl) ⟨504861, by rfl⟩ : syracuseStep 1346297 = 1009723) B1009723
theorem B1706825 : Blo 896573 1706825 := bstep (se 2 (by rfl) ⟨640059, by rfl⟩ : syracuseStep 1706825 = 1280119) B1280119
theorem B1346399 : Blo 896573 1346399 := bstep (se 1 (by rfl) ⟨1009799, by rfl⟩ : syracuseStep 1346399 = 2019599) B2019599
theorem B1346411 : Blo 896573 1346411 := bstep (se 1 (by rfl) ⟨1009808, by rfl⟩ : syracuseStep 1346411 = 2019617) B2019617
theorem B2558881 : Blo 896573 2558881 := bstep (se 2 (by rfl) ⟨959580, by rfl⟩ : syracuseStep 2558881 = 1919161) B1919161
theorem B1346639 : Blo 896573 1346639 := bstep (se 1 (by rfl) ⟨1009979, by rfl⟩ : syracuseStep 1346639 = 2019959) B2019959
theorem B7015619 : Blo 896573 7015619 := bstep (se 1 (by rfl) ⟨5261714, by rfl⟩ : syracuseStep 7015619 = 10523429) B10523429
theorem B1346759 : Blo 896573 1346759 := bstep (se 1 (by rfl) ⟨1010069, by rfl⟩ : syracuseStep 1346759 = 2020139) B2020139
theorem B1707257 : Blo 896573 1707257 := bstep (se 2 (by rfl) ⟨640221, by rfl⟩ : syracuseStep 1707257 = 1280443) B1280443
theorem B1346921 : Blo 896573 1346921 := bstep (se 2 (by rfl) ⟨505095, by rfl⟩ : syracuseStep 1346921 = 1010191) B1010191
theorem B1346999 : Blo 896573 1346999 := bstep (se 1 (by rfl) ⟨1010249, by rfl⟩ : syracuseStep 1346999 = 2020499) B2020499
theorem B1347035 : Blo 896573 1347035 := bstep (se 1 (by rfl) ⟨1010276, by rfl⟩ : syracuseStep 1347035 = 2020553) B2020553
theorem B2559451 : Blo 896573 2559451 := bstep (se 1 (by rfl) ⟨1919588, by rfl⟩ : syracuseStep 2559451 = 3839177) B3839177
theorem B14585309 : Blo 896573 14585309 := bstep (se 3 (by rfl) ⟨2734745, by rfl⟩ : syracuseStep 14585309 = 5469491) B5469491
theorem B23301751 : Blo 896573 23301751 := bstep (se 1 (by rfl) ⟨17476313, by rfl⟩ : syracuseStep 23301751 = 34952627) B34952627
theorem B20778619 : Blo 896573 20778619 := bstep (se 1 (by rfl) ⟨15583964, by rfl⟩ : syracuseStep 20778619 = 31167929) B31167929
theorem B5115757 : Blo 896573 5115757 := bstep (se 3 (by rfl) ⟨959204, by rfl⟩ : syracuseStep 5115757 = 1918409) B1918409
theorem B1347503 : Blo 896573 1347503 := bstep (se 1 (by rfl) ⟨1010627, by rfl⟩ : syracuseStep 1347503 = 2021255) B2021255
theorem B1347593 : Blo 896573 1347593 := bstep (se 2 (by rfl) ⟨505347, by rfl⟩ : syracuseStep 1347593 = 1010695) B1010695
theorem B1347623 : Blo 896573 1347623 := bstep (se 1 (by rfl) ⟨1010717, by rfl⟩ : syracuseStep 1347623 = 2021435) B2021435
theorem B1347707 : Blo 896573 1347707 := bstep (se 1 (by rfl) ⟨1010780, by rfl⟩ : syracuseStep 1347707 = 2021561) B2021561
theorem B2560157 : Blo 896573 2560157 := bstep (se 3 (by rfl) ⟨480029, by rfl⟩ : syracuseStep 2560157 = 960059) B960059
theorem B1347833 : Blo 896573 1347833 := bstep (se 2 (by rfl) ⟨505437, by rfl⟩ : syracuseStep 1347833 = 1010875) B1010875
theorem B1347935 : Blo 896573 1347935 := bstep (se 1 (by rfl) ⟨1010951, by rfl⟩ : syracuseStep 1347935 = 2021903) B2021903
theorem B1347947 : Blo 896573 1347947 := bstep (se 1 (by rfl) ⟨1010960, by rfl⟩ : syracuseStep 1347947 = 2021921) B2021921
theorem B11506049 : Blo 896573 11506049 := bstep (se 2 (by rfl) ⟨4314768, by rfl⟩ : syracuseStep 11506049 = 8629537) B8629537
theorem B2560385 : Blo 896573 2560385 := bstep (se 2 (by rfl) ⟨960144, by rfl⟩ : syracuseStep 2560385 = 1920289) B1920289
theorem B1348175 : Blo 896573 1348175 := bstep (se 1 (by rfl) ⟨1011131, by rfl⟩ : syracuseStep 1348175 = 2022263) B2022263
theorem B1708715 : Blo 896573 1708715 := bstep (se 1 (by rfl) ⟨1281536, by rfl⟩ : syracuseStep 1708715 = 2563073) B2563073
theorem B1348295 : Blo 896573 1348295 := bstep (se 1 (by rfl) ⟨1011221, by rfl⟩ : syracuseStep 1348295 = 2022443) B2022443
theorem B2560727 : Blo 896573 2560727 := bstep (se 1 (by rfl) ⟨1920545, by rfl⟩ : syracuseStep 2560727 = 3841091) B3841091
theorem B2560841 : Blo 896573 2560841 := bstep (se 2 (by rfl) ⟨960315, by rfl⟩ : syracuseStep 2560841 = 1920631) B1920631
theorem B1348457 : Blo 896573 1348457 := bstep (se 2 (by rfl) ⟨505671, by rfl⟩ : syracuseStep 1348457 = 1011343) B1011343
theorem B1348535 : Blo 896573 1348535 := bstep (se 1 (by rfl) ⟨1011401, by rfl⟩ : syracuseStep 1348535 = 2022803) B2022803
theorem B1348571 : Blo 896573 1348571 := bstep (se 1 (by rfl) ⟨1011428, by rfl⟩ : syracuseStep 1348571 = 2022857) B2022857
theorem B1709095 : Blo 896573 1709095 := bstep (se 1 (by rfl) ⟨1281821, by rfl⟩ : syracuseStep 1709095 = 2563643) B2563643
theorem B1709255 : Blo 896573 1709255 := bstep (se 1 (by rfl) ⟨1281941, by rfl⟩ : syracuseStep 1709255 = 2563883) B2563883
theorem B8295695 : Blo 896573 8295695 := bstep (se 1 (by rfl) ⟨6221771, by rfl⟩ : syracuseStep 8295695 = 12443543) B12443543
theorem B1349039 : Blo 896573 1349039 := bstep (se 1 (by rfl) ⟨1011779, by rfl⟩ : syracuseStep 1349039 = 2023559) B2023559
theorem B3642889 : Blo 896573 3642889 := bstep (se 2 (by rfl) ⟨1366083, by rfl⟩ : syracuseStep 3642889 = 2732167) B2732167
theorem B1349129 : Blo 896573 1349129 := bstep (se 2 (by rfl) ⟨505923, by rfl⟩ : syracuseStep 1349129 = 1011847) B1011847
theorem B11539979 : Blo 896573 11539979 := bstep (se 1 (by rfl) ⟨8654984, by rfl⟩ : syracuseStep 11539979 = 17309969) B17309969
theorem B1349159 : Blo 896573 1349159 := bstep (se 1 (by rfl) ⟨1011869, by rfl⟩ : syracuseStep 1349159 = 2023739) B2023739
theorem B1513039 : Blo 896573 1513039 := bstep (se 1 (by rfl) ⟨1134779, by rfl⟩ : syracuseStep 1513039 = 2269559) B2269559
theorem B1349243 : Blo 896573 1349243 := bstep (se 1 (by rfl) ⟨1011932, by rfl⟩ : syracuseStep 1349243 = 2023865) B2023865
theorem B7280327 : Blo 896573 7280327 := bstep (se 1 (by rfl) ⟨5460245, by rfl⟩ : syracuseStep 7280327 = 10920491) B10920491
theorem B1349369 : Blo 896573 1349369 := bstep (se 2 (by rfl) ⟨506013, by rfl⟩ : syracuseStep 1349369 = 1012027) B1012027
theorem B1513289 : Blo 896573 1513289 := bstep (se 2 (by rfl) ⟨567483, by rfl⟩ : syracuseStep 1513289 = 1134967) B1134967
theorem B1349471 : Blo 896573 1349471 := bstep (se 1 (by rfl) ⟨1012103, by rfl⟩ : syracuseStep 1349471 = 2024207) B2024207
theorem B1349483 : Blo 896573 1349483 := bstep (se 1 (by rfl) ⟨1012112, by rfl⟩ : syracuseStep 1349483 = 2024225) B2024225
theorem B1349711 : Blo 896573 1349711 := bstep (se 1 (by rfl) ⟨1012283, by rfl⟩ : syracuseStep 1349711 = 2024567) B2024567
theorem B1349831 : Blo 896573 1349831 := bstep (se 1 (by rfl) ⟨1012373, by rfl⟩ : syracuseStep 1349831 = 2024747) B2024747
theorem B1513721 : Blo 896573 1513721 := bstep (se 2 (by rfl) ⟨567645, by rfl⟩ : syracuseStep 1513721 = 1135291) B1135291
theorem B1349993 : Blo 896573 1349993 := bstep (se 2 (by rfl) ⟨506247, by rfl⟩ : syracuseStep 1349993 = 1012495) B1012495
theorem B2922895 : Blo 896573 2922895 := bstep (se 1 (by rfl) ⟨2192171, by rfl⟩ : syracuseStep 2922895 = 4384343) B4384343
theorem B1513903 : Blo 896573 1513903 := bstep (se 1 (by rfl) ⟨1135427, by rfl⟩ : syracuseStep 1513903 = 2270855) B2270855
theorem B1350071 : Blo 896573 1350071 := bstep (se 1 (by rfl) ⟨1012553, by rfl⟩ : syracuseStep 1350071 = 2025107) B2025107
theorem B1350107 : Blo 896573 1350107 := bstep (se 1 (by rfl) ⟨1012580, by rfl⟩ : syracuseStep 1350107 = 2025161) B2025161
theorem B3840493 : Blo 896573 3840493 := bstep (se 3 (by rfl) ⟨720092, by rfl⟩ : syracuseStep 3840493 = 1440185) B1440185
theorem B1513991 : Blo 896573 1513991 := bstep (se 1 (by rfl) ⟨1135493, by rfl⟩ : syracuseStep 1513991 = 2270987) B2270987
theorem B5118673 : Blo 896573 5118673 := bstep (se 2 (by rfl) ⟨1919502, by rfl⟩ : syracuseStep 5118673 = 3839005) B3839005
theorem B3414743 : Blo 896573 3414743 := bstep (se 1 (by rfl) ⟨2561057, by rfl⟩ : syracuseStep 3414743 = 5122115) B5122115
theorem B1514335 : Blo 896573 1514335 := bstep (se 1 (by rfl) ⟨1135751, by rfl⟩ : syracuseStep 1514335 = 2271503) B2271503
theorem B1350575 : Blo 896573 1350575 := bstep (se 1 (by rfl) ⟨1012931, by rfl⟩ : syracuseStep 1350575 = 2025863) B2025863
theorem B1514423 : Blo 896573 1514423 := bstep (se 1 (by rfl) ⟨1135817, by rfl⟩ : syracuseStep 1514423 = 2271635) B2271635
theorem B1350665 : Blo 896573 1350665 := bstep (se 2 (by rfl) ⟨506499, by rfl⟩ : syracuseStep 1350665 = 1012999) B1012999
theorem B957479 : Blo 896573 957479 := bstep (se 1 (by rfl) ⟨718109, by rfl⟩ : syracuseStep 957479 = 1436219) B1436219
theorem B1350695 : Blo 896573 1350695 := bstep (se 1 (by rfl) ⟨1013021, by rfl⟩ : syracuseStep 1350695 = 2026043) B2026043
theorem B1350779 : Blo 896573 1350779 := bstep (se 1 (by rfl) ⟨1013084, by rfl⟩ : syracuseStep 1350779 = 2026169) B2026169
theorem B7675073 : Blo 896573 7675073 := bstep (se 2 (by rfl) ⟨2878152, by rfl⟩ : syracuseStep 7675073 = 5756305) B5756305
theorem B2465149 : Blo 896573 2465149 := bstep (se 3 (by rfl) ⟨462215, by rfl⟩ : syracuseStep 2465149 = 924431) B924431
theorem B1515017 : Blo 896573 1515017 := bstep (se 2 (by rfl) ⟨568131, by rfl⟩ : syracuseStep 1515017 = 1136263) B1136263
theorem B2563609 : Blo 896573 2563609 := bstep (se 2 (by rfl) ⟨961353, by rfl⟩ : syracuseStep 2563609 = 1922707) B1922707
theorem B2596475 : Blo 896573 2596475 := bstep (se 1 (by rfl) ⟨1947356, by rfl⟩ : syracuseStep 2596475 = 3894713) B3894713
theorem B1515179 : Blo 896573 1515179 := bstep (se 1 (by rfl) ⟨1136384, by rfl⟩ : syracuseStep 1515179 = 2272769) B2272769
theorem B4857533 : Blo 896573 4857533 := bstep (se 3 (by rfl) ⟨910787, by rfl⟩ : syracuseStep 4857533 = 1821575) B1821575
theorem B59121413 : Blo 896573 59121413 := bstep (se 4 (by rfl) ⟨5542632, by rfl⟩ : syracuseStep 59121413 = 11085265) B11085265
theorem B2727787 : Blo 896573 2727787 := bstep (se 1 (by rfl) ⟨2045840, by rfl⟩ : syracuseStep 2727787 = 4091681) B4091681
theorem B1515577 : Blo 896573 1515577 := bstep (se 2 (by rfl) ⟨568341, by rfl⟩ : syracuseStep 1515577 = 1136683) B1136683
theorem B2465849 : Blo 896573 2465849 := bstep (se 2 (by rfl) ⟨924693, by rfl⟩ : syracuseStep 2465849 = 1849387) B1849387
theorem B1515719 : Blo 896573 1515719 := bstep (se 1 (by rfl) ⟨1136789, by rfl⟩ : syracuseStep 1515719 = 2273579) B2273579
theorem B1515881 : Blo 896573 1515881 := bstep (se 2 (by rfl) ⟨568455, by rfl⟩ : syracuseStep 1515881 = 1136911) B1136911
theorem B2269721 : Blo 896573 2269721 := bstep (se 2 (by rfl) ⟨851145, by rfl⟩ : syracuseStep 2269721 = 1702291) B1702291
theorem B18719383 : Blo 896573 18719383 := bstep (se 1 (by rfl) ⟨14039537, by rfl⟩ : syracuseStep 18719383 = 28079075) B28079075
theorem B1516279 : Blo 896573 1516279 := bstep (se 1 (by rfl) ⟨1137209, by rfl⟩ : syracuseStep 1516279 = 2274419) B2274419
theorem B1516475 : Blo 896573 1516475 := bstep (se 1 (by rfl) ⟨1137356, by rfl⟩ : syracuseStep 1516475 = 2274713) B2274713
theorem B2270227 : Blo 896573 2270227 := bstep (se 1 (by rfl) ⟨1702670, by rfl⟩ : syracuseStep 2270227 = 3405341) B3405341
theorem B1516583 : Blo 896573 1516583 := bstep (se 1 (by rfl) ⟨1137437, by rfl⟩ : syracuseStep 1516583 = 2274875) B2274875
theorem B10364057 : Blo 896573 10364057 := bstep (se 2 (by rfl) ⟨3886521, by rfl⟩ : syracuseStep 10364057 = 7773043) B7773043
theorem B1516873 : Blo 896573 1516873 := bstep (se 2 (by rfl) ⟨568827, by rfl⟩ : syracuseStep 1516873 = 1137655) B1137655
theorem B1516907 : Blo 896573 1516907 := bstep (se 1 (by rfl) ⟨1137680, by rfl⟩ : syracuseStep 1516907 = 2275361) B2275361
theorem B14558579 : Blo 896573 14558579 := bstep (se 1 (by rfl) ⟨10918934, by rfl⟩ : syracuseStep 14558579 = 21837869) B21837869
theorem B3417659 : Blo 896573 3417659 := bstep (se 1 (by rfl) ⟨2563244, by rfl⟩ : syracuseStep 3417659 = 5126489) B5126489
theorem B13149793 : Blo 896573 13149793 := bstep (se 2 (by rfl) ⟨4931172, by rfl⟩ : syracuseStep 13149793 = 9862345) B9862345
theorem B1517305 : Blo 896573 1517305 := bstep (se 2 (by rfl) ⟨568989, by rfl⟩ : syracuseStep 1517305 = 1137979) B1137979
theorem B1517575 : Blo 896573 1517575 := bstep (se 1 (by rfl) ⟨1138181, by rfl⟩ : syracuseStep 1517575 = 2276363) B2276363
theorem B2271311 : Blo 896573 2271311 := bstep (se 1 (by rfl) ⟨1703483, by rfl⟩ : syracuseStep 2271311 = 3406967) B3406967
theorem B2959517 : Blo 896573 2959517 := bstep (se 3 (by rfl) ⟨554909, by rfl⟩ : syracuseStep 2959517 = 1109819) B1109819
theorem B14592257 : Blo 896573 14592257 := bstep (se 2 (by rfl) ⟨5472096, by rfl⟩ : syracuseStep 14592257 = 10944193) B10944193
theorem B1518007 : Blo 896573 1518007 := bstep (se 1 (by rfl) ⟨1138505, by rfl⟩ : syracuseStep 1518007 = 2277011) B2277011
theorem B1518203 : Blo 896573 1518203 := bstep (se 1 (by rfl) ⟨1138652, by rfl⟩ : syracuseStep 1518203 = 2277305) B2277305
theorem B7383737 : Blo 896573 7383737 := bstep (se 2 (by rfl) ⟨2768901, by rfl⟩ : syracuseStep 7383737 = 5537803) B5537803
theorem B2271959 : Blo 896573 2271959 := bstep (se 1 (by rfl) ⟨1703969, by rfl⟩ : syracuseStep 2271959 = 3407939) B3407939
theorem B2304929 : Blo 896573 2304929 := bstep (se 2 (by rfl) ⟨864348, by rfl⟩ : syracuseStep 2304929 = 1728697) B1728697
theorem B1518601 : Blo 896573 1518601 := bstep (se 2 (by rfl) ⟨569475, by rfl⟩ : syracuseStep 1518601 = 1138951) B1138951
theorem B26225687 : Blo 896573 26225687 := bstep (se 1 (by rfl) ⟨19669265, by rfl⟩ : syracuseStep 26225687 = 39338531) B39338531
theorem B2272313 : Blo 896573 2272313 := bstep (se 2 (by rfl) ⟨852117, by rfl⟩ : syracuseStep 2272313 = 1704235) B1704235
theorem B1518763 : Blo 896573 1518763 := bstep (se 1 (by rfl) ⟨1139072, by rfl⟩ : syracuseStep 1518763 = 2278145) B2278145
theorem B10235159 : Blo 896573 10235159 := bstep (se 1 (by rfl) ⟨7676369, by rfl⟩ : syracuseStep 10235159 = 15352739) B15352739
theorem B1519067 : Blo 896573 1519067 := bstep (se 1 (by rfl) ⟨1139300, by rfl⟩ : syracuseStep 1519067 = 2278601) B2278601
theorem B11677171 : Blo 896573 11677171 := bstep (se 1 (by rfl) ⟨8757878, by rfl⟩ : syracuseStep 11677171 = 17515757) B17515757
theorem B896591 : Blo 896573 896591 := bstep (se 1 (by rfl) ⟨672443, by rfl⟩ : syracuseStep 896591 = 1344887) B1344887
theorem B896607 : Blo 896573 896607 := bstep (se 1 (by rfl) ⟨672455, by rfl⟩ : syracuseStep 896607 = 1344911) B1344911
theorem B896635 : Blo 896573 896635 := bstep (se 1 (by rfl) ⟨672476, by rfl⟩ : syracuseStep 896635 = 1344953) B1344953
theorem B896687 : Blo 896573 896687 := bstep (se 1 (by rfl) ⟨672515, by rfl⟩ : syracuseStep 896687 = 1345031) B1345031
theorem B896711 : Blo 896573 896711 := bstep (se 1 (by rfl) ⟨672533, by rfl⟩ : syracuseStep 896711 = 1345067) B1345067
theorem B1519303 : Blo 896573 1519303 := bstep (se 1 (by rfl) ⟨1139477, by rfl⟩ : syracuseStep 1519303 = 2278955) B2278955
theorem B896731 : Blo 896573 896731 := bstep (se 1 (by rfl) ⟨672548, by rfl⟩ : syracuseStep 896731 = 1345097) B1345097
theorem B896807 : Blo 896573 896807 := bstep (se 1 (by rfl) ⟨672605, by rfl⟩ : syracuseStep 896807 = 1345211) B1345211
theorem B896847 : Blo 896573 896847 := bstep (se 1 (by rfl) ⟨672635, by rfl⟩ : syracuseStep 896847 = 1345271) B1345271
theorem B896863 : Blo 896573 896863 := bstep (se 1 (by rfl) ⟨672647, by rfl⟩ : syracuseStep 896863 = 1345295) B1345295
theorem B1519465 : Blo 896573 1519465 := bstep (se 2 (by rfl) ⟨569799, by rfl⟩ : syracuseStep 1519465 = 1139599) B1139599
theorem B3026807 : Blo 896573 3026807 := bstep (se 1 (by rfl) ⟨2270105, by rfl⟩ : syracuseStep 3026807 = 4540211) B4540211
theorem B896891 : Blo 896573 896891 := bstep (se 1 (by rfl) ⟨672668, by rfl⟩ : syracuseStep 896891 = 1345337) B1345337
theorem B11513735 : Blo 896573 11513735 := bstep (se 1 (by rfl) ⟨8635301, by rfl⟩ : syracuseStep 11513735 = 17270603) B17270603
theorem B896943 : Blo 896573 896943 := bstep (se 1 (by rfl) ⟨672707, by rfl⟩ : syracuseStep 896943 = 1345415) B1345415
theorem B896967 : Blo 896573 896967 := bstep (se 1 (by rfl) ⟨672725, by rfl⟩ : syracuseStep 896967 = 1345451) B1345451
theorem B896987 : Blo 896573 896987 := bstep (se 1 (by rfl) ⟨672740, by rfl⟩ : syracuseStep 896987 = 1345481) B1345481
theorem B897063 : Blo 896573 897063 := bstep (se 1 (by rfl) ⟨672797, by rfl⟩ : syracuseStep 897063 = 1345595) B1345595
theorem B3027023 : Blo 896573 3027023 := bstep (se 1 (by rfl) ⟨2270267, by rfl⟩ : syracuseStep 3027023 = 4540535) B4540535
theorem B897103 : Blo 896573 897103 := bstep (se 1 (by rfl) ⟨672827, by rfl⟩ : syracuseStep 897103 = 1345655) B1345655
theorem B897119 : Blo 896573 897119 := bstep (se 1 (by rfl) ⟨672839, by rfl⟩ : syracuseStep 897119 = 1345679) B1345679
theorem B897147 : Blo 896573 897147 := bstep (se 1 (by rfl) ⟨672860, by rfl⟩ : syracuseStep 897147 = 1345721) B1345721
theorem B897199 : Blo 896573 897199 := bstep (se 1 (by rfl) ⟨672899, by rfl⟩ : syracuseStep 897199 = 1345799) B1345799
theorem B897223 : Blo 896573 897223 := bstep (se 1 (by rfl) ⟨672917, by rfl⟩ : syracuseStep 897223 = 1345835) B1345835
theorem B897243 : Blo 896573 897243 := bstep (se 1 (by rfl) ⟨672932, by rfl⟩ : syracuseStep 897243 = 1345865) B1345865
theorem B6828299 : Blo 896573 6828299 := bstep (se 1 (by rfl) ⟨5121224, by rfl⟩ : syracuseStep 6828299 = 10242449) B10242449
theorem B897319 : Blo 896573 897319 := bstep (se 1 (by rfl) ⟨672989, by rfl⟩ : syracuseStep 897319 = 1345979) B1345979
theorem B897359 : Blo 896573 897359 := bstep (se 1 (by rfl) ⟨673019, by rfl⟩ : syracuseStep 897359 = 1346039) B1346039
theorem B897375 : Blo 896573 897375 := bstep (se 1 (by rfl) ⟨673031, by rfl⟩ : syracuseStep 897375 = 1346063) B1346063
theorem B1421675 : Blo 896573 1421675 := bstep (se 1 (by rfl) ⟨1066256, by rfl⟩ : syracuseStep 1421675 = 2132513) B2132513
theorem B897403 : Blo 896573 897403 := bstep (se 1 (by rfl) ⟨673052, by rfl⟩ : syracuseStep 897403 = 1346105) B1346105
theorem B897455 : Blo 896573 897455 := bstep (se 1 (by rfl) ⟨673091, by rfl⟩ : syracuseStep 897455 = 1346183) B1346183
theorem B1618363 : Blo 896573 1618363 := bstep (se 1 (by rfl) ⟨1213772, by rfl⟩ : syracuseStep 1618363 = 2427545) B2427545
theorem B897479 : Blo 896573 897479 := bstep (se 1 (by rfl) ⟨673109, by rfl⟩ : syracuseStep 897479 = 1346219) B1346219
theorem B3027401 : Blo 896573 3027401 := bstep (se 2 (by rfl) ⟨1135275, by rfl⟩ : syracuseStep 3027401 = 2270551) B2270551
theorem B897499 : Blo 896573 897499 := bstep (se 1 (by rfl) ⟨673124, by rfl⟩ : syracuseStep 897499 = 1346249) B1346249
theorem B12956183 : Blo 896573 12956183 := bstep (se 1 (by rfl) ⟨9717137, by rfl⟩ : syracuseStep 12956183 = 19434275) B19434275
theorem B897575 : Blo 896573 897575 := bstep (se 1 (by rfl) ⟨673181, by rfl⟩ : syracuseStep 897575 = 1346363) B1346363
theorem B897615 : Blo 896573 897615 := bstep (se 1 (by rfl) ⟨673211, by rfl⟩ : syracuseStep 897615 = 1346423) B1346423
theorem B897631 : Blo 896573 897631 := bstep (se 1 (by rfl) ⟨673223, by rfl⟩ : syracuseStep 897631 = 1346447) B1346447
theorem B897659 : Blo 896573 897659 := bstep (se 1 (by rfl) ⟨673244, by rfl⟩ : syracuseStep 897659 = 1346489) B1346489
theorem B897711 : Blo 896573 897711 := bstep (se 1 (by rfl) ⟨673283, by rfl⟩ : syracuseStep 897711 = 1346567) B1346567
theorem B897735 : Blo 896573 897735 := bstep (se 1 (by rfl) ⟨673301, by rfl⟩ : syracuseStep 897735 = 1346603) B1346603
theorem B3027671 : Blo 896573 3027671 := bstep (se 1 (by rfl) ⟨2270753, by rfl⟩ : syracuseStep 3027671 = 4541507) B4541507
theorem B897755 : Blo 896573 897755 := bstep (se 1 (by rfl) ⟨673316, by rfl⟩ : syracuseStep 897755 = 1346633) B1346633
theorem B897831 : Blo 896573 897831 := bstep (se 1 (by rfl) ⟨673373, by rfl⟩ : syracuseStep 897831 = 1346747) B1346747
theorem B897871 : Blo 896573 897871 := bstep (se 1 (by rfl) ⟨673403, by rfl⟩ : syracuseStep 897871 = 1346807) B1346807
theorem B897887 : Blo 896573 897887 := bstep (se 1 (by rfl) ⟨673415, by rfl⟩ : syracuseStep 897887 = 1346831) B1346831
theorem B897915 : Blo 896573 897915 := bstep (se 1 (by rfl) ⟨673436, by rfl⟩ : syracuseStep 897915 = 1346873) B1346873
theorem B3027887 : Blo 896573 3027887 := bstep (se 1 (by rfl) ⟨2270915, by rfl⟩ : syracuseStep 3027887 = 4541831) B4541831
theorem B897967 : Blo 896573 897967 := bstep (se 1 (by rfl) ⟨673475, by rfl⟩ : syracuseStep 897967 = 1346951) B1346951
theorem B897991 : Blo 896573 897991 := bstep (se 1 (by rfl) ⟨673493, by rfl⟩ : syracuseStep 897991 = 1346987) B1346987
theorem B898011 : Blo 896573 898011 := bstep (se 1 (by rfl) ⟨673508, by rfl⟩ : syracuseStep 898011 = 1347017) B1347017
theorem B898087 : Blo 896573 898087 := bstep (se 1 (by rfl) ⟨673565, by rfl⟩ : syracuseStep 898087 = 1347131) B1347131
theorem B898127 : Blo 896573 898127 := bstep (se 1 (by rfl) ⟨673595, by rfl⟩ : syracuseStep 898127 = 1347191) B1347191
theorem B898143 : Blo 896573 898143 := bstep (se 1 (by rfl) ⟨673607, by rfl⟩ : syracuseStep 898143 = 1347215) B1347215
theorem B898171 : Blo 896573 898171 := bstep (se 1 (by rfl) ⟨673628, by rfl⟩ : syracuseStep 898171 = 1347257) B1347257
theorem B898223 : Blo 896573 898223 := bstep (se 1 (by rfl) ⟨673667, by rfl⟩ : syracuseStep 898223 = 1347335) B1347335
theorem B898247 : Blo 896573 898247 := bstep (se 1 (by rfl) ⟨673685, by rfl⟩ : syracuseStep 898247 = 1347371) B1347371
theorem B898267 : Blo 896573 898267 := bstep (se 1 (by rfl) ⟨673700, by rfl⟩ : syracuseStep 898267 = 1347401) B1347401
theorem B2274551 : Blo 896573 2274551 := bstep (se 1 (by rfl) ⟨1705913, by rfl⟩ : syracuseStep 2274551 = 3411827) B3411827
theorem B898343 : Blo 896573 898343 := bstep (se 1 (by rfl) ⟨673757, by rfl⟩ : syracuseStep 898343 = 1347515) B1347515
theorem B898383 : Blo 896573 898383 := bstep (se 1 (by rfl) ⟨673787, by rfl⟩ : syracuseStep 898383 = 1347575) B1347575
theorem B898399 : Blo 896573 898399 := bstep (se 1 (by rfl) ⟨673799, by rfl⟩ : syracuseStep 898399 = 1347599) B1347599
theorem B898427 : Blo 896573 898427 := bstep (se 1 (by rfl) ⟨673820, by rfl⟩ : syracuseStep 898427 = 1347641) B1347641
theorem B898479 : Blo 896573 898479 := bstep (se 1 (by rfl) ⟨673859, by rfl⟩ : syracuseStep 898479 = 1347719) B1347719
theorem B898503 : Blo 896573 898503 := bstep (se 1 (by rfl) ⟨673877, by rfl⟩ : syracuseStep 898503 = 1347755) B1347755
theorem B898523 : Blo 896573 898523 := bstep (se 1 (by rfl) ⟨673892, by rfl⟩ : syracuseStep 898523 = 1347785) B1347785
theorem B1619465 : Blo 896573 1619465 := bstep (se 2 (by rfl) ⟨607299, by rfl⟩ : syracuseStep 1619465 = 1214599) B1214599
theorem B898599 : Blo 896573 898599 := bstep (se 1 (by rfl) ⟨673949, by rfl⟩ : syracuseStep 898599 = 1347899) B1347899
theorem B898639 : Blo 896573 898639 := bstep (se 1 (by rfl) ⟨673979, by rfl⟩ : syracuseStep 898639 = 1347959) B1347959
theorem B898655 : Blo 896573 898655 := bstep (se 1 (by rfl) ⟨673991, by rfl⟩ : syracuseStep 898655 = 1347983) B1347983
theorem B898683 : Blo 896573 898683 := bstep (se 1 (by rfl) ⟨674012, by rfl⟩ : syracuseStep 898683 = 1348025) B1348025
theorem B898735 : Blo 896573 898735 := bstep (se 1 (by rfl) ⟨674051, by rfl⟩ : syracuseStep 898735 = 1348103) B1348103
theorem B6829757 : Blo 896573 6829757 := bstep (se 3 (by rfl) ⟨1280579, by rfl⟩ : syracuseStep 6829757 = 2561159) B2561159
theorem B898759 : Blo 896573 898759 := bstep (se 1 (by rfl) ⟨674069, by rfl⟩ : syracuseStep 898759 = 1348139) B1348139
theorem B898779 : Blo 896573 898779 := bstep (se 1 (by rfl) ⟨674084, by rfl⟩ : syracuseStep 898779 = 1348169) B1348169
theorem B11646713 : Blo 896573 11646713 := bstep (se 2 (by rfl) ⟨4367517, by rfl⟩ : syracuseStep 11646713 = 8735035) B8735035
theorem B898855 : Blo 896573 898855 := bstep (se 1 (by rfl) ⟨674141, by rfl⟩ : syracuseStep 898855 = 1348283) B1348283
theorem B898895 : Blo 896573 898895 := bstep (se 1 (by rfl) ⟨674171, by rfl⟩ : syracuseStep 898895 = 1348343) B1348343
theorem B898911 : Blo 896573 898911 := bstep (se 1 (by rfl) ⟨674183, by rfl⟩ : syracuseStep 898911 = 1348367) B1348367
theorem B898939 : Blo 896573 898939 := bstep (se 1 (by rfl) ⟨674204, by rfl⟩ : syracuseStep 898939 = 1348409) B1348409
theorem B898991 : Blo 896573 898991 := bstep (se 1 (by rfl) ⟨674243, by rfl⟩ : syracuseStep 898991 = 1348487) B1348487
theorem B899015 : Blo 896573 899015 := bstep (se 1 (by rfl) ⟨674261, by rfl⟩ : syracuseStep 899015 = 1348523) B1348523
theorem B899035 : Blo 896573 899035 := bstep (se 1 (by rfl) ⟨674276, by rfl⟩ : syracuseStep 899035 = 1348553) B1348553
theorem B7288861 : Blo 896573 7288861 := bstep (se 3 (by rfl) ⟨1366661, by rfl⟩ : syracuseStep 7288861 = 2733323) B2733323
theorem B899111 : Blo 896573 899111 := bstep (se 1 (by rfl) ⟨674333, by rfl⟩ : syracuseStep 899111 = 1348667) B1348667
theorem B899151 : Blo 896573 899151 := bstep (se 1 (by rfl) ⟨674363, by rfl⟩ : syracuseStep 899151 = 1348727) B1348727
theorem B899167 : Blo 896573 899167 := bstep (se 1 (by rfl) ⟨674375, by rfl⟩ : syracuseStep 899167 = 1348751) B1348751
theorem B899195 : Blo 896573 899195 := bstep (se 1 (by rfl) ⟨674396, by rfl⟩ : syracuseStep 899195 = 1348793) B1348793
theorem B6830243 : Blo 896573 6830243 := bstep (se 1 (by rfl) ⟨5122682, by rfl⟩ : syracuseStep 6830243 = 10245365) B10245365
theorem B899247 : Blo 896573 899247 := bstep (se 1 (by rfl) ⟨674435, by rfl⟩ : syracuseStep 899247 = 1348871) B1348871
theorem B899271 : Blo 896573 899271 := bstep (se 1 (by rfl) ⟨674453, by rfl⟩ : syracuseStep 899271 = 1348907) B1348907
theorem B899291 : Blo 896573 899291 := bstep (se 1 (by rfl) ⟨674468, by rfl⟩ : syracuseStep 899291 = 1348937) B1348937
theorem B899367 : Blo 896573 899367 := bstep (se 1 (by rfl) ⟨674525, by rfl⟩ : syracuseStep 899367 = 1349051) B1349051
theorem B899407 : Blo 896573 899407 := bstep (se 1 (by rfl) ⟨674555, by rfl⟩ : syracuseStep 899407 = 1349111) B1349111
theorem B899423 : Blo 896573 899423 := bstep (se 1 (by rfl) ⟨674567, by rfl⟩ : syracuseStep 899423 = 1349135) B1349135
theorem B899451 : Blo 896573 899451 := bstep (se 1 (by rfl) ⟨674588, by rfl⟩ : syracuseStep 899451 = 1349177) B1349177
theorem B899503 : Blo 896573 899503 := bstep (se 1 (by rfl) ⟨674627, by rfl⟩ : syracuseStep 899503 = 1349255) B1349255
theorem B899527 : Blo 896573 899527 := bstep (se 1 (by rfl) ⟨674645, by rfl⟩ : syracuseStep 899527 = 1349291) B1349291
theorem B899547 : Blo 896573 899547 := bstep (se 1 (by rfl) ⟨674660, by rfl⟩ : syracuseStep 899547 = 1349321) B1349321
theorem B3422753 : Blo 896573 3422753 := bstep (se 2 (by rfl) ⟨1283532, by rfl⟩ : syracuseStep 3422753 = 2567065) B2567065
theorem B899623 : Blo 896573 899623 := bstep (se 1 (by rfl) ⟨674717, by rfl⟩ : syracuseStep 899623 = 1349435) B1349435
theorem B899663 : Blo 896573 899663 := bstep (se 1 (by rfl) ⟨674747, by rfl⟩ : syracuseStep 899663 = 1349495) B1349495
theorem B899679 : Blo 896573 899679 := bstep (se 1 (by rfl) ⟨674759, by rfl⟩ : syracuseStep 899679 = 1349519) B1349519
theorem B899707 : Blo 896573 899707 := bstep (se 1 (by rfl) ⟨674780, by rfl⟩ : syracuseStep 899707 = 1349561) B1349561
theorem B899759 : Blo 896573 899759 := bstep (se 1 (by rfl) ⟨674819, by rfl⟩ : syracuseStep 899759 = 1349639) B1349639
theorem B2276039 : Blo 896573 2276039 := bstep (se 1 (by rfl) ⟨1707029, by rfl⟩ : syracuseStep 2276039 = 3414059) B3414059
theorem B899783 : Blo 896573 899783 := bstep (se 1 (by rfl) ⟨674837, by rfl⟩ : syracuseStep 899783 = 1349675) B1349675
theorem B899803 : Blo 896573 899803 := bstep (se 1 (by rfl) ⟨674852, by rfl⟩ : syracuseStep 899803 = 1349705) B1349705
theorem B899879 : Blo 896573 899879 := bstep (se 1 (by rfl) ⟨674909, by rfl⟩ : syracuseStep 899879 = 1349819) B1349819
theorem B899919 : Blo 896573 899919 := bstep (se 1 (by rfl) ⟨674939, by rfl⟩ : syracuseStep 899919 = 1349879) B1349879
theorem B899935 : Blo 896573 899935 := bstep (se 1 (by rfl) ⟨674951, by rfl⟩ : syracuseStep 899935 = 1349903) B1349903
theorem B899963 : Blo 896573 899963 := bstep (se 1 (by rfl) ⟨674972, by rfl⟩ : syracuseStep 899963 = 1349945) B1349945
theorem B900015 : Blo 896573 900015 := bstep (se 1 (by rfl) ⟨675011, by rfl⟩ : syracuseStep 900015 = 1350023) B1350023
theorem B900039 : Blo 896573 900039 := bstep (se 1 (by rfl) ⟨675029, by rfl⟩ : syracuseStep 900039 = 1350059) B1350059
theorem B900059 : Blo 896573 900059 := bstep (se 1 (by rfl) ⟨675044, by rfl⟩ : syracuseStep 900059 = 1350089) B1350089
theorem B900135 : Blo 896573 900135 := bstep (se 1 (by rfl) ⟨675101, by rfl⟩ : syracuseStep 900135 = 1350203) B1350203
theorem B900175 : Blo 896573 900175 := bstep (se 1 (by rfl) ⟨675131, by rfl⟩ : syracuseStep 900175 = 1350263) B1350263
theorem B900191 : Blo 896573 900191 := bstep (se 1 (by rfl) ⟨675143, by rfl⟩ : syracuseStep 900191 = 1350287) B1350287
theorem B900219 : Blo 896573 900219 := bstep (se 1 (by rfl) ⟨675164, by rfl⟩ : syracuseStep 900219 = 1350329) B1350329
theorem B900271 : Blo 896573 900271 := bstep (se 1 (by rfl) ⟨675203, by rfl⟩ : syracuseStep 900271 = 1350407) B1350407
theorem B900295 : Blo 896573 900295 := bstep (se 1 (by rfl) ⟨675221, by rfl⟩ : syracuseStep 900295 = 1350443) B1350443
theorem B900315 : Blo 896573 900315 := bstep (se 1 (by rfl) ⟨675236, by rfl⟩ : syracuseStep 900315 = 1350473) B1350473
theorem B3030263 : Blo 896573 3030263 := bstep (se 1 (by rfl) ⟨2272697, by rfl⟩ : syracuseStep 3030263 = 4545395) B4545395
theorem B900391 : Blo 896573 900391 := bstep (se 1 (by rfl) ⟨675293, by rfl⟩ : syracuseStep 900391 = 1350587) B1350587
theorem B900431 : Blo 896573 900431 := bstep (se 1 (by rfl) ⟨675323, by rfl⟩ : syracuseStep 900431 = 1350647) B1350647
theorem B900447 : Blo 896573 900447 := bstep (se 1 (by rfl) ⟨675335, by rfl⟩ : syracuseStep 900447 = 1350671) B1350671
theorem B900475 : Blo 896573 900475 := bstep (se 1 (by rfl) ⟨675356, by rfl⟩ : syracuseStep 900475 = 1350713) B1350713
theorem B3325313 : Blo 896573 3325313 := bstep (se 2 (by rfl) ⟨1246992, by rfl⟩ : syracuseStep 3325313 = 2493985) B2493985
theorem B900527 : Blo 896573 900527 := bstep (se 1 (by rfl) ⟨675395, by rfl⟩ : syracuseStep 900527 = 1350791) B1350791
theorem B900551 : Blo 896573 900551 := bstep (se 1 (by rfl) ⟨675413, by rfl⟩ : syracuseStep 900551 = 1350827) B1350827
theorem B900571 : Blo 896573 900571 := bstep (se 1 (by rfl) ⟨675428, by rfl⟩ : syracuseStep 900571 = 1350857) B1350857
theorem B3030587 : Blo 896573 3030587 := bstep (se 1 (by rfl) ⟨2272940, by rfl⟩ : syracuseStep 3030587 = 4545881) B4545881
theorem B3456701 : Blo 896573 3456701 := bstep (se 3 (by rfl) ⟨648131, by rfl⟩ : syracuseStep 3456701 = 1296263) B1296263
theorem B7683821 : Blo 896573 7683821 := bstep (se 3 (by rfl) ⟨1440716, by rfl⟩ : syracuseStep 7683821 = 2881433) B2881433
theorem B3030857 : Blo 896573 3030857 := bstep (se 2 (by rfl) ⟨1136571, by rfl⟩ : syracuseStep 3030857 = 2273143) B2273143
theorem B2277193 : Blo 896573 2277193 := bstep (se 2 (by rfl) ⟨853947, by rfl⟩ : syracuseStep 2277193 = 1707895) B1707895
theorem B1916855 : Blo 896573 1916855 := bstep (se 1 (by rfl) ⟨1437641, by rfl⟩ : syracuseStep 1916855 = 2875283) B2875283
theorem B12271931 : Blo 896573 12271931 := bstep (se 1 (by rfl) ⟨9203948, by rfl⟩ : syracuseStep 12271931 = 18407897) B18407897
theorem B6832673 : Blo 896573 6832673 := bstep (se 2 (by rfl) ⟨2562252, by rfl⟩ : syracuseStep 6832673 = 5124505) B5124505
theorem B5456747 : Blo 896573 5456747 := bstep (se 1 (by rfl) ⟨4092560, by rfl⟩ : syracuseStep 5456747 = 8185121) B8185121
theorem B3031991 : Blo 896573 3031991 := bstep (se 1 (by rfl) ⟨2273993, by rfl⟩ : syracuseStep 3031991 = 4547987) B4547987
theorem B2278327 : Blo 896573 2278327 := bstep (se 1 (by rfl) ⟨1708745, by rfl⟩ : syracuseStep 2278327 = 3417491) B3417491
theorem B4539563 : Blo 896573 4539563 := bstep (se 1 (by rfl) ⟨3404672, by rfl⟩ : syracuseStep 4539563 = 6809345) B6809345
theorem B3032585 : Blo 896573 3032585 := bstep (se 2 (by rfl) ⟨1137219, by rfl⟩ : syracuseStep 3032585 = 2274439) B2274439
theorem B4540049 : Blo 896573 4540049 := bstep (se 2 (by rfl) ⟨1702518, by rfl⟩ : syracuseStep 4540049 = 3405037) B3405037
theorem B3033449 : Blo 896573 3033449 := bstep (se 2 (by rfl) ⟨1137543, by rfl⟩ : syracuseStep 3033449 = 2275087) B2275087
theorem B4934153 : Blo 896573 4934153 := bstep (se 2 (by rfl) ⟨1850307, by rfl⟩ : syracuseStep 4934153 = 3700615) B3700615
theorem B2017889 : Blo 896573 2017889 := bstep (se 2 (by rfl) ⟨756708, by rfl⟩ : syracuseStep 2017889 = 1513417) B1513417
theorem B34523981 : Blo 896573 34523981 := bstep (se 3 (by rfl) ⟨6473246, by rfl⟩ : syracuseStep 34523981 = 12946493) B12946493
theorem B2018231 : Blo 896573 2018231 := bstep (se 1 (by rfl) ⟨1513673, by rfl⟩ : syracuseStep 2018231 = 3027347) B3027347
theorem B3034043 : Blo 896573 3034043 := bstep (se 1 (by rfl) ⟨2275532, by rfl⟩ : syracuseStep 3034043 = 4551065) B4551065
theorem B6474923 : Blo 896573 6474923 := bstep (se 1 (by rfl) ⟨4856192, by rfl⟩ : syracuseStep 6474923 = 9712385) B9712385
theorem B58182947 : Blo 896573 58182947 := bstep (se 1 (by rfl) ⟨43637210, by rfl⟩ : syracuseStep 58182947 = 87274421) B87274421
theorem B2018825 : Blo 896573 2018825 := bstep (se 2 (by rfl) ⟨757059, by rfl⟩ : syracuseStep 2018825 = 1514119) B1514119
theorem B10243907 : Blo 896573 10243907 := bstep (se 1 (by rfl) ⟨7682930, by rfl⟩ : syracuseStep 10243907 = 15365861) B15365861
theorem B2019167 : Blo 896573 2019167 := bstep (se 1 (by rfl) ⟨1514375, by rfl⟩ : syracuseStep 2019167 = 3028751) B3028751
theorem B4542317 : Blo 896573 4542317 := bstep (se 3 (by rfl) ⟨851684, by rfl⟩ : syracuseStep 4542317 = 1703369) B1703369
theorem B3559355 : Blo 896573 3559355 := bstep (se 1 (by rfl) ⟨2669516, by rfl⟩ : syracuseStep 3559355 = 5339033) B5339033
theorem B5754817 : Blo 896573 5754817 := bstep (se 2 (by rfl) ⟨2158056, by rfl⟩ : syracuseStep 5754817 = 4316113) B4316113
theorem B4542479 : Blo 896573 4542479 := bstep (se 1 (by rfl) ⟨3406859, by rfl⟩ : syracuseStep 4542479 = 6813719) B6813719
theorem B2019347 : Blo 896573 2019347 := bstep (se 1 (by rfl) ⟨1514510, by rfl⟩ : syracuseStep 2019347 = 3029021) B3029021
theorem B1626151 : Blo 896573 1626151 := bstep (se 1 (by rfl) ⟨1219613, by rfl⟩ : syracuseStep 1626151 = 2439227) B2439227
theorem B2019689 : Blo 896573 2019689 := bstep (se 2 (by rfl) ⟨757383, by rfl⟩ : syracuseStep 2019689 = 1514767) B1514767
theorem B3035771 : Blo 896573 3035771 := bstep (se 1 (by rfl) ⟨2276828, by rfl⟩ : syracuseStep 3035771 = 4553657) B4553657
theorem B5460689 : Blo 896573 5460689 := bstep (se 2 (by rfl) ⟨2047758, by rfl⟩ : syracuseStep 5460689 = 4095517) B4095517
theorem B10932947 : Blo 896573 10932947 := bstep (se 1 (by rfl) ⟨8199710, by rfl⟩ : syracuseStep 10932947 = 16399421) B16399421
theorem B3035933 : Blo 896573 3035933 := bstep (se 3 (by rfl) ⟨569237, by rfl⟩ : syracuseStep 3035933 = 1138475) B1138475
theorem B3232619 : Blo 896573 3232619 := bstep (se 1 (by rfl) ⟨2424464, by rfl⟩ : syracuseStep 3232619 = 4848929) B4848929
theorem B2020283 : Blo 896573 2020283 := bstep (se 1 (by rfl) ⟨1515212, by rfl⟩ : syracuseStep 2020283 = 3030425) B3030425
theorem B2020409 : Blo 896573 2020409 := bstep (se 2 (by rfl) ⟨757653, by rfl⟩ : syracuseStep 2020409 = 1515307) B1515307
theorem B4609219 : Blo 896573 4609219 := bstep (se 1 (by rfl) ⟨3456914, by rfl⟩ : syracuseStep 4609219 = 6913829) B6913829
theorem B2020751 : Blo 896573 2020751 := bstep (se 1 (by rfl) ⟨1515563, by rfl⟩ : syracuseStep 2020751 = 3031127) B3031127
theorem B3036635 : Blo 896573 3036635 := bstep (se 1 (by rfl) ⟨2277476, by rfl⟩ : syracuseStep 3036635 = 4554953) B4554953
theorem B3233267 : Blo 896573 3233267 := bstep (se 1 (by rfl) ⟨2424950, by rfl⟩ : syracuseStep 3233267 = 4849901) B4849901
theorem B7296551 : Blo 896573 7296551 := bstep (se 1 (by rfl) ⟨5472413, by rfl⟩ : syracuseStep 7296551 = 10944827) B10944827
theorem B1136207 : Blo 896573 1136207 := bstep (se 1 (by rfl) ⟨852155, by rfl⟩ : syracuseStep 1136207 = 1704311) B1704311
theorem B3888737 : Blo 896573 3888737 := bstep (se 2 (by rfl) ⟨1458276, by rfl⟩ : syracuseStep 3888737 = 2916553) B2916553
theorem B2021075 : Blo 896573 2021075 := bstep (se 1 (by rfl) ⟨1515806, by rfl⟩ : syracuseStep 2021075 = 3031613) B3031613
theorem B7788383 : Blo 896573 7788383 := bstep (se 1 (by rfl) ⟨5841287, by rfl⟩ : syracuseStep 7788383 = 11682575) B11682575
theorem B2873195 : Blo 896573 2873195 := bstep (se 1 (by rfl) ⟨2154896, by rfl⟩ : syracuseStep 2873195 = 4309793) B4309793
theorem B3463183 : Blo 896573 3463183 := bstep (se 1 (by rfl) ⟨2597387, by rfl⟩ : syracuseStep 3463183 = 5194775) B5194775
theorem B3037337 : Blo 896573 3037337 := bstep (se 2 (by rfl) ⟨1139001, by rfl⟩ : syracuseStep 3037337 = 2278003) B2278003
theorem B2021897 : Blo 896573 2021897 := bstep (se 2 (by rfl) ⟨758211, by rfl⟩ : syracuseStep 2021897 = 1516423) B1516423
theorem B2022011 : Blo 896573 2022011 := bstep (se 1 (by rfl) ⟨1516508, by rfl⟩ : syracuseStep 2022011 = 3033017) B3033017
theorem B4545233 : Blo 896573 4545233 := bstep (se 2 (by rfl) ⟨1704462, by rfl⟩ : syracuseStep 4545233 = 3408925) B3408925
theorem B2022137 : Blo 896573 2022137 := bstep (se 2 (by rfl) ⟨758301, by rfl⟩ : syracuseStep 2022137 = 1516603) B1516603
theorem B1366777 : Blo 896573 1366777 := bstep (se 2 (by rfl) ⟨512541, by rfl⟩ : syracuseStep 1366777 = 1025083) B1025083
theorem B1137503 : Blo 896573 1137503 := bstep (se 1 (by rfl) ⟨853127, by rfl⟩ : syracuseStep 1137503 = 1706255) B1706255
theorem B2022407 : Blo 896573 2022407 := bstep (se 1 (by rfl) ⟨1516805, by rfl⟩ : syracuseStep 2022407 = 3033611) B3033611
theorem B2022479 : Blo 896573 2022479 := bstep (se 1 (by rfl) ⟨1516859, by rfl⟩ : syracuseStep 2022479 = 3033719) B3033719
theorem B4611275 : Blo 896573 4611275 := bstep (se 1 (by rfl) ⟨3458456, by rfl⟩ : syracuseStep 4611275 = 6916913) B6916913
theorem B7691543 : Blo 896573 7691543 := bstep (se 1 (by rfl) ⟨5768657, by rfl⟩ : syracuseStep 7691543 = 11537315) B11537315
theorem B3038525 : Blo 896573 3038525 := bstep (se 3 (by rfl) ⟨569723, by rfl⟩ : syracuseStep 3038525 = 1139447) B1139447
theorem B1727905 : Blo 896573 1727905 := bstep (se 2 (by rfl) ⟨647964, by rfl⟩ : syracuseStep 1727905 = 1295929) B1295929
theorem B2022875 : Blo 896573 2022875 := bstep (se 1 (by rfl) ⟨1517156, by rfl⟩ : syracuseStep 2022875 = 3034313) B3034313
theorem B1170983 : Blo 896573 1170983 := bstep (se 1 (by rfl) ⟨878237, by rfl⟩ : syracuseStep 1170983 = 1756475) B1756475
theorem B1728211 : Blo 896573 1728211 := bstep (se 1 (by rfl) ⟨1296158, by rfl⟩ : syracuseStep 1728211 = 2592317) B2592317
theorem B2023343 : Blo 896573 2023343 := bstep (se 1 (by rfl) ⟨1517507, by rfl⟩ : syracuseStep 2023343 = 3035015) B3035015
theorem B3039389 : Blo 896573 3039389 := bstep (se 3 (by rfl) ⟨569885, by rfl⟩ : syracuseStep 3039389 = 1139771) B1139771
theorem B2023595 : Blo 896573 2023595 := bstep (se 1 (by rfl) ⟨1517696, by rfl⟩ : syracuseStep 2023595 = 3035393) B3035393
theorem B2024135 : Blo 896573 2024135 := bstep (se 1 (by rfl) ⟨1518101, by rfl⟩ : syracuseStep 2024135 = 3036203) B3036203
theorem B7660241 : Blo 896573 7660241 := bstep (se 2 (by rfl) ⟨2872590, by rfl⟩ : syracuseStep 7660241 = 5745181) B5745181
theorem B1008679 : Blo 896573 1008679 := bstep (se 1 (by rfl) ⟨756509, by rfl⟩ : syracuseStep 1008679 = 1513019) B1513019
theorem B4547663 : Blo 896573 4547663 := bstep (se 1 (by rfl) ⟨3410747, by rfl⟩ : syracuseStep 4547663 = 6821495) B6821495
theorem B10249739 : Blo 896573 10249739 := bstep (se 1 (by rfl) ⟨7687304, by rfl⟩ : syracuseStep 10249739 = 15374609) B15374609
theorem B2024999 : Blo 896573 2024999 := bstep (se 1 (by rfl) ⟨1518749, by rfl⟩ : syracuseStep 2024999 = 3037499) B3037499
theorem B4548311 : Blo 896573 4548311 := bstep (se 1 (by rfl) ⟨3411233, by rfl⟩ : syracuseStep 4548311 = 6822467) B6822467
theorem B4155095 : Blo 896573 4155095 := bstep (se 1 (by rfl) ⟨3116321, by rfl⟩ : syracuseStep 4155095 = 6232643) B6232643
theorem B2025323 : Blo 896573 2025323 := bstep (se 1 (by rfl) ⟨1518992, by rfl⟩ : syracuseStep 2025323 = 3037985) B3037985
theorem B2025377 : Blo 896573 2025377 := bstep (se 2 (by rfl) ⟨759516, by rfl⟩ : syracuseStep 2025377 = 1519033) B1519033
theorem B2025719 : Blo 896573 2025719 := bstep (se 1 (by rfl) ⟨1519289, by rfl⟩ : syracuseStep 2025719 = 3038579) B3038579
theorem B1010299 : Blo 896573 1010299 := bstep (se 1 (by rfl) ⟨757724, by rfl⟩ : syracuseStep 1010299 = 1515449) B1515449
theorem B8645453 : Blo 896573 8645453 := bstep (se 3 (by rfl) ⟨1621022, by rfl⟩ : syracuseStep 8645453 = 3242045) B3242045
theorem B912223 : Blo 896573 912223 := bstep (se 1 (by rfl) ⟨684167, by rfl⟩ : syracuseStep 912223 = 1368335) B1368335
theorem B1010767 : Blo 896573 1010767 := bstep (se 1 (by rfl) ⟨758075, by rfl⟩ : syracuseStep 1010767 = 1516151) B1516151
theorem B38890691 : Blo 896573 38890691 := bstep (se 1 (by rfl) ⟨29168018, by rfl⟩ : syracuseStep 38890691 = 58336037) B58336037
theorem B1011163 : Blo 896573 1011163 := bstep (se 1 (by rfl) ⟨758372, by rfl⟩ : syracuseStep 1011163 = 1516745) B1516745
theorem B1437193 : Blo 896573 1437193 := bstep (se 2 (by rfl) ⟨538947, by rfl⟩ : syracuseStep 1437193 = 1077895) B1077895
theorem B12938885 : Blo 896573 12938885 := bstep (se 4 (by rfl) ⟨1213020, by rfl⟩ : syracuseStep 12938885 = 2426041) B2426041
theorem B10907459 : Blo 896573 10907459 := bstep (se 1 (by rfl) ⟨8180594, by rfl⟩ : syracuseStep 10907459 = 16361189) B16361189
theorem B1011631 : Blo 896573 1011631 := bstep (se 1 (by rfl) ⟨758723, by rfl⟩ : syracuseStep 1011631 = 1517447) B1517447
theorem B5828561 : Blo 896573 5828561 := bstep (se 2 (by rfl) ⟨2185710, by rfl⟩ : syracuseStep 5828561 = 4371421) B4371421
theorem B3502081 : Blo 896573 3502081 := bstep (se 2 (by rfl) ⟨1313280, by rfl⟩ : syracuseStep 3502081 = 2626561) B2626561
theorem B1536079 : Blo 896573 1536079 := bstep (se 1 (by rfl) ⟨1152059, by rfl⟩ : syracuseStep 1536079 = 2304119) B2304119
theorem B1012063 : Blo 896573 1012063 := bstep (se 1 (by rfl) ⟨759047, by rfl⟩ : syracuseStep 1012063 = 1518095) B1518095
theorem B2879869 : Blo 896573 2879869 := bstep (se 3 (by rfl) ⟨539975, by rfl⟩ : syracuseStep 2879869 = 1079951) B1079951
theorem B3076633 : Blo 896573 3076633 := bstep (se 2 (by rfl) ⟨1153737, by rfl⟩ : syracuseStep 3076633 = 2307475) B2307475
theorem B4551227 : Blo 896573 4551227 := bstep (se 1 (by rfl) ⟨3413420, by rfl⟩ : syracuseStep 4551227 = 6826841) B6826841
theorem B9695861 : Blo 896573 9695861 := bstep (se 5 (by rfl) ⟨454493, by rfl⟩ : syracuseStep 9695861 = 908987) B908987
theorem B1012423 : Blo 896573 1012423 := bstep (se 1 (by rfl) ⟨759317, by rfl⟩ : syracuseStep 1012423 = 1518635) B1518635
theorem B3404537 : Blo 896573 3404537 := bstep (se 2 (by rfl) ⟨1276701, by rfl⟩ : syracuseStep 3404537 = 2553403) B2553403
theorem B4551875 : Blo 896573 4551875 := bstep (se 1 (by rfl) ⟨3413906, by rfl⟩ : syracuseStep 4551875 = 6827813) B6827813
theorem B4322803 : Blo 896573 4322803 := bstep (se 1 (by rfl) ⟨3242102, by rfl⟩ : syracuseStep 4322803 = 6484205) B6484205
theorem B7272023 : Blo 896573 7272023 := bstep (se 1 (by rfl) ⟨5454017, by rfl⟩ : syracuseStep 7272023 = 10908035) B10908035
theorem B7665299 : Blo 896573 7665299 := bstep (se 1 (by rfl) ⟨5748974, by rfl⟩ : syracuseStep 7665299 = 11497949) B11497949
theorem B13858451 : Blo 896573 13858451 := bstep (se 1 (by rfl) ⟨10393838, by rfl⟩ : syracuseStep 13858451 = 20787677) B20787677
theorem B3405523 : Blo 896573 3405523 := bstep (se 1 (by rfl) ⟨2554142, by rfl⟩ : syracuseStep 3405523 = 5108285) B5108285
theorem B8648491 : Blo 896573 8648491 := bstep (se 1 (by rfl) ⟨6486368, by rfl⟩ : syracuseStep 8648491 = 12972737) B12972737
theorem B2160479 : Blo 896573 2160479 := bstep (se 1 (by rfl) ⟨1620359, by rfl⟩ : syracuseStep 2160479 = 3240719) B3240719
theorem B9238481 : Blo 896573 9238481 := bstep (se 2 (by rfl) ⟨3464430, by rfl⟩ : syracuseStep 9238481 = 6928861) B6928861
theorem B12941369 : Blo 896573 12941369 := bstep (se 2 (by rfl) ⟨4853013, by rfl⟩ : syracuseStep 12941369 = 9706027) B9706027
theorem B3405995 : Blo 896573 3405995 := bstep (se 1 (by rfl) ⟨2554496, by rfl⟩ : syracuseStep 3405995 = 5108993) B5108993
theorem B5765377 : Blo 896573 5765377 := bstep (se 2 (by rfl) ⟨2162016, by rfl⟩ : syracuseStep 5765377 = 4324033) B4324033
theorem B4323689 : Blo 896573 4323689 := bstep (se 2 (by rfl) ⟨1621383, by rfl⟩ : syracuseStep 4323689 = 3242767) B3242767
theorem B2554507 : Blo 896573 2554507 := bstep (se 1 (by rfl) ⟨1915880, by rfl⟩ : syracuseStep 2554507 = 3831761) B3831761
theorem B1703035 : Blo 896573 1703035 := bstep (se 1 (by rfl) ⟨1277276, by rfl⟩ : syracuseStep 1703035 = 2554553) B2554553
theorem B3833027 : Blo 896573 3833027 := bstep (se 1 (by rfl) ⟨2874770, by rfl⟩ : syracuseStep 3833027 = 5749541) B5749541
theorem B1703263 : Blo 896573 1703263 := bstep (se 1 (by rfl) ⟨1277447, by rfl⟩ : syracuseStep 1703263 = 2554895) B2554895
theorem B2882945 : Blo 896573 2882945 := bstep (se 2 (by rfl) ⟨1081104, by rfl⟩ : syracuseStep 2882945 = 2162209) B2162209
theorem B6815177 : Blo 896573 6815177 := bstep (se 2 (by rfl) ⟨2555691, by rfl⟩ : syracuseStep 6815177 = 5111383) B5111383
theorem B36961757 : Blo 896573 36961757 := bstep (se 3 (by rfl) ⟨6930329, by rfl⟩ : syracuseStep 36961757 = 13860659) B13860659
theorem B5471783 : Blo 896573 5471783 := bstep (se 1 (by rfl) ⟨4103837, by rfl⟩ : syracuseStep 5471783 = 8207675) B8207675
theorem B1703521 : Blo 896573 1703521 := bstep (se 2 (by rfl) ⟨638820, by rfl⟩ : syracuseStep 1703521 = 1277641) B1277641
theorem B10223495 : Blo 896573 10223495 := bstep (se 1 (by rfl) ⟨7667621, by rfl⟩ : syracuseStep 10223495 = 15335243) B15335243
theorem B1703855 : Blo 896573 1703855 := bstep (se 1 (by rfl) ⟨1277891, by rfl⟩ : syracuseStep 1703855 = 2555783) B2555783
theorem B18677765 : Blo 896573 18677765 := bstep (se 4 (by rfl) ⟨1751040, by rfl⟩ : syracuseStep 18677765 = 3502081) B3502081
theorem B4555115 : Blo 896573 4555115 := bstep (se 1 (by rfl) ⟨3416336, by rfl⟩ : syracuseStep 4555115 = 6832673) B6832673
theorem B3637831 : Blo 896573 3637831 := bstep (se 1 (by rfl) ⟨2728373, by rfl⟩ : syracuseStep 3637831 = 5456747) B5456747
theorem B1638983 : Blo 896573 1638983 := bstep (se 1 (by rfl) ⟨1229237, by rfl⟩ : syracuseStep 1638983 = 2458475) B2458475
theorem B8651681 : Blo 896573 8651681 := bstep (se 2 (by rfl) ⟨3244380, by rfl⟩ : syracuseStep 8651681 = 6488761) B6488761
theorem B6489395 : Blo 896573 6489395 := bstep (se 1 (by rfl) ⟨4867046, by rfl⟩ : syracuseStep 6489395 = 9734093) B9734093
theorem B1705313 : Blo 896573 1705313 := bstep (se 2 (by rfl) ⟨639492, by rfl⟩ : syracuseStep 1705313 = 1278985) B1278985
theorem B1344905 : Blo 896573 1344905 := bstep (se 2 (by rfl) ⟨504339, by rfl⟩ : syracuseStep 1344905 = 1008679) B1008679
theorem B1705465 : Blo 896573 1705465 := bstep (se 2 (by rfl) ⟨639549, by rfl⟩ : syracuseStep 1705465 = 1279099) B1279099
theorem B1345259 : Blo 896573 1345259 := bstep (se 1 (by rfl) ⟨1008944, by rfl⟩ : syracuseStep 1345259 = 2017889) B2017889
theorem B2426603 : Blo 896573 2426603 := bstep (se 1 (by rfl) ⟨1819952, by rfl⟩ : syracuseStep 2426603 = 3639905) B3639905
theorem B4556573 : Blo 896573 4556573 := bstep (se 3 (by rfl) ⟨854357, by rfl⟩ : syracuseStep 4556573 = 1708715) B1708715
theorem B1705769 : Blo 896573 1705769 := bstep (se 2 (by rfl) ⟨639663, by rfl⟩ : syracuseStep 1705769 = 1279327) B1279327
theorem B1345487 : Blo 896573 1345487 := bstep (se 1 (by rfl) ⟨1009115, by rfl⟩ : syracuseStep 1345487 = 2018231) B2018231
theorem B17533057 : Blo 896573 17533057 := bstep (se 2 (by rfl) ⟨6574896, by rfl⟩ : syracuseStep 17533057 = 13149793) B13149793
theorem B3410201 : Blo 896573 3410201 := bstep (se 2 (by rfl) ⟨1278825, by rfl⟩ : syracuseStep 3410201 = 2557651) B2557651
theorem B1345883 : Blo 896573 1345883 := bstep (se 1 (by rfl) ⟨1009412, by rfl⟩ : syracuseStep 1345883 = 2018825) B2018825
theorem B1346111 : Blo 896573 1346111 := bstep (se 1 (by rfl) ⟨1009583, by rfl⟩ : syracuseStep 1346111 = 2019167) B2019167
theorem B1346231 : Blo 896573 1346231 := bstep (se 1 (by rfl) ⟨1009673, by rfl⟩ : syracuseStep 1346231 = 2019347) B2019347
theorem B1706771 : Blo 896573 1706771 := bstep (se 1 (by rfl) ⟨1280078, by rfl⟩ : syracuseStep 1706771 = 2560157) B2560157
theorem B1346459 : Blo 896573 1346459 := bstep (se 1 (by rfl) ⟨1009844, by rfl⟩ : syracuseStep 1346459 = 2019689) B2019689
theorem B7670699 : Blo 896573 7670699 := bstep (se 1 (by rfl) ⟨5753024, by rfl⟩ : syracuseStep 7670699 = 11506049) B11506049
theorem B1706923 : Blo 896573 1706923 := bstep (se 1 (by rfl) ⟨1280192, by rfl⟩ : syracuseStep 1706923 = 2560385) B2560385
theorem B3640459 : Blo 896573 3640459 := bstep (se 1 (by rfl) ⟨2730344, by rfl⟩ : syracuseStep 3640459 = 5460689) B5460689
theorem B1707151 : Blo 896573 1707151 := bstep (se 1 (by rfl) ⟨1280363, by rfl⟩ : syracuseStep 1707151 = 2560727) B2560727
theorem B1707227 : Blo 896573 1707227 := bstep (se 1 (by rfl) ⟨1280420, by rfl⟩ : syracuseStep 1707227 = 2560841) B2560841
theorem B1346855 : Blo 896573 1346855 := bstep (se 1 (by rfl) ⟨1010141, by rfl⟩ : syracuseStep 1346855 = 2020283) B2020283
theorem B8654141 : Blo 896573 8654141 := bstep (se 3 (by rfl) ⟨1622651, by rfl⟩ : syracuseStep 8654141 = 3245303) B3245303
theorem B1346939 : Blo 896573 1346939 := bstep (se 1 (by rfl) ⟨1010204, by rfl⟩ : syracuseStep 1346939 = 2020409) B2020409
theorem B1347065 : Blo 896573 1347065 := bstep (se 2 (by rfl) ⟨505149, by rfl⟩ : syracuseStep 1347065 = 1010299) B1010299
theorem B1347167 : Blo 896573 1347167 := bstep (se 1 (by rfl) ⟨1010375, by rfl⟩ : syracuseStep 1347167 = 2020751) B2020751
theorem B2592491 : Blo 896573 2592491 := bstep (se 1 (by rfl) ⟨1944368, by rfl⟩ : syracuseStep 2592491 = 3888737) B3888737
theorem B1216297 : Blo 896573 1216297 := bstep (se 2 (by rfl) ⟨456111, by rfl⟩ : syracuseStep 1216297 = 912223) B912223
theorem B1347383 : Blo 896573 1347383 := bstep (se 1 (by rfl) ⟨1010537, by rfl⟩ : syracuseStep 1347383 = 2021075) B2021075
theorem B3411841 : Blo 896573 3411841 := bstep (se 2 (by rfl) ⟨1279440, by rfl⟩ : syracuseStep 3411841 = 2558881) B2558881
theorem B1347689 : Blo 896573 1347689 := bstep (se 2 (by rfl) ⟨505383, by rfl⟩ : syracuseStep 1347689 = 1010767) B1010767
theorem B1347931 : Blo 896573 1347931 := bstep (se 1 (by rfl) ⟨1010948, by rfl⟩ : syracuseStep 1347931 = 2021897) B2021897
theorem B1348007 : Blo 896573 1348007 := bstep (se 1 (by rfl) ⟨1011005, by rfl⟩ : syracuseStep 1348007 = 2022011) B2022011
theorem B1348091 : Blo 896573 1348091 := bstep (se 1 (by rfl) ⟨1011068, by rfl⟩ : syracuseStep 1348091 = 2022137) B2022137
theorem B11080253 : Blo 896573 11080253 := bstep (se 3 (by rfl) ⟨2077547, by rfl⟩ : syracuseStep 11080253 = 4155095) B4155095
theorem B3412601 : Blo 896573 3412601 := bstep (se 2 (by rfl) ⟨1279725, by rfl⟩ : syracuseStep 3412601 = 2559451) B2559451
theorem B1348217 : Blo 896573 1348217 := bstep (se 2 (by rfl) ⟨505581, by rfl⟩ : syracuseStep 1348217 = 1011163) B1011163
theorem B15569561 : Blo 896573 15569561 := bstep (se 2 (by rfl) ⟨5838585, by rfl⟩ : syracuseStep 15569561 = 11677171) B11677171
theorem B1348271 : Blo 896573 1348271 := bstep (se 1 (by rfl) ⟨1011203, by rfl⟩ : syracuseStep 1348271 = 2022407) B2022407
theorem B1348319 : Blo 896573 1348319 := bstep (se 1 (by rfl) ⟨1011239, by rfl⟩ : syracuseStep 1348319 = 2022479) B2022479
theorem B5116715 : Blo 896573 5116715 := bstep (se 1 (by rfl) ⟨3837536, by rfl⟩ : syracuseStep 5116715 = 7675073) B7675073
theorem B31069001 : Blo 896573 31069001 := bstep (se 2 (by rfl) ⟨11650875, by rfl⟩ : syracuseStep 31069001 = 23301751) B23301751
theorem B1348583 : Blo 896573 1348583 := bstep (se 1 (by rfl) ⟨1011437, by rfl⟩ : syracuseStep 1348583 = 2022875) B2022875
theorem B3413117 : Blo 896573 3413117 := bstep (se 3 (by rfl) ⟨639959, by rfl⟩ : syracuseStep 3413117 = 1279919) B1279919
theorem B6821009 : Blo 896573 6821009 := bstep (se 2 (by rfl) ⟨2557878, by rfl⟩ : syracuseStep 6821009 = 5115757) B5115757
theorem B1348841 : Blo 896573 1348841 := bstep (se 2 (by rfl) ⟨505815, by rfl⟩ : syracuseStep 1348841 = 1011631) B1011631
theorem B7673089 : Blo 896573 7673089 := bstep (se 2 (by rfl) ⟨2877408, by rfl⟩ : syracuseStep 7673089 = 5754817) B5754817
theorem B1348895 : Blo 896573 1348895 := bstep (se 1 (by rfl) ⟨1011671, by rfl⟩ : syracuseStep 1348895 = 2023343) B2023343
theorem B1643899 : Blo 896573 1643899 := bstep (se 1 (by rfl) ⟨1232924, by rfl⟩ : syracuseStep 1643899 = 2465849) B2465849
theorem B2168201 : Blo 896573 2168201 := bstep (se 2 (by rfl) ⟨813075, by rfl⟩ : syracuseStep 2168201 = 1626151) B1626151
theorem B17274293 : Blo 896573 17274293 := bstep (se 5 (by rfl) ⟨809732, by rfl⟩ : syracuseStep 17274293 = 1619465) B1619465
theorem B1349063 : Blo 896573 1349063 := bstep (se 1 (by rfl) ⟨1011797, by rfl⟩ : syracuseStep 1349063 = 2023595) B2023595
theorem B1513147 : Blo 896573 1513147 := bstep (se 1 (by rfl) ⟨1134860, by rfl⟩ : syracuseStep 1513147 = 2269721) B2269721
theorem B1349417 : Blo 896573 1349417 := bstep (se 2 (by rfl) ⟨506031, by rfl⟩ : syracuseStep 1349417 = 1012063) B1012063
theorem B1349423 : Blo 896573 1349423 := bstep (se 1 (by rfl) ⟨1012067, by rfl⟩ : syracuseStep 1349423 = 2024135) B2024135
theorem B3839825 : Blo 896573 3839825 := bstep (se 2 (by rfl) ⟨1439934, by rfl⟩ : syracuseStep 3839825 = 2879869) B2879869
theorem B4102177 : Blo 896573 4102177 := bstep (se 2 (by rfl) ⟨1538316, by rfl⟩ : syracuseStep 4102177 = 3076633) B3076633
theorem B9705719 : Blo 896573 9705719 := bstep (se 1 (by rfl) ⟨7279289, by rfl⟩ : syracuseStep 9705719 = 14558579) B14558579
theorem B1349897 : Blo 896573 1349897 := bstep (se 2 (by rfl) ⟨506211, by rfl⟩ : syracuseStep 1349897 = 1012423) B1012423
theorem B1349999 : Blo 896573 1349999 := bstep (se 1 (by rfl) ⟨1012499, by rfl⟩ : syracuseStep 1349999 = 2024999) B2024999
theorem B1350215 : Blo 896573 1350215 := bstep (se 1 (by rfl) ⟨1012661, by rfl⟩ : syracuseStep 1350215 = 2025323) B2025323
theorem B1350251 : Blo 896573 1350251 := bstep (se 1 (by rfl) ⟨1012688, by rfl⟩ : syracuseStep 1350251 = 2025377) B2025377
theorem B1514207 : Blo 896573 1514207 := bstep (se 1 (by rfl) ⟨1135655, by rfl⟩ : syracuseStep 1514207 = 2271311) B2271311
theorem B1350479 : Blo 896573 1350479 := bstep (se 1 (by rfl) ⟨1012859, by rfl⟩ : syracuseStep 1350479 = 2025719) B2025719
theorem B4922491 : Blo 896573 4922491 := bstep (se 1 (by rfl) ⟨3691868, by rfl⟩ : syracuseStep 4922491 = 7383737) B7383737
theorem B1514639 : Blo 896573 1514639 := bstep (se 1 (by rfl) ⟨1135979, by rfl⟩ : syracuseStep 1514639 = 2271959) B2271959
theorem B3415229 : Blo 896573 3415229 := bstep (se 3 (by rfl) ⟨640355, by rfl⟩ : syracuseStep 3415229 = 1280711) B1280711
theorem B4857185 : Blo 896573 4857185 := bstep (se 2 (by rfl) ⟨1821444, by rfl⟩ : syracuseStep 4857185 = 3642889) B3642889
theorem B1514875 : Blo 896573 1514875 := bstep (se 1 (by rfl) ⟨1136156, by rfl⟩ : syracuseStep 1514875 = 2272313) B2272313
theorem B25927127 : Blo 896573 25927127 := bstep (se 1 (by rfl) ⟨19445345, by rfl⟩ : syracuseStep 25927127 = 38890691) B38890691
theorem B6823439 : Blo 896573 6823439 := bstep (se 1 (by rfl) ⟨5117579, by rfl⟩ : syracuseStep 6823439 = 10235159) B10235159
theorem B8625923 : Blo 896573 8625923 := bstep (se 1 (by rfl) ⟨6469442, by rfl⟩ : syracuseStep 8625923 = 12938885) B12938885
theorem B7675823 : Blo 896573 7675823 := bstep (se 1 (by rfl) ⟨5756867, by rfl⟩ : syracuseStep 7675823 = 11513735) B11513735
theorem B6463907 : Blo 896573 6463907 := bstep (se 1 (by rfl) ⟨4847930, by rfl⟩ : syracuseStep 6463907 = 9695861) B9695861
theorem B2269691 : Blo 896573 2269691 := bstep (se 1 (by rfl) ⟨1702268, by rfl⟩ : syracuseStep 2269691 = 3404537) B3404537
theorem B5120657 : Blo 896573 5120657 := bstep (se 2 (by rfl) ⟨1920246, by rfl⟩ : syracuseStep 5120657 = 3840493) B3840493
theorem B1516367 : Blo 896573 1516367 := bstep (se 1 (by rfl) ⟨1137275, by rfl⟩ : syracuseStep 1516367 = 2274551) B2274551
theorem B6824897 : Blo 896573 6824897 := bstep (se 2 (by rfl) ⟨2559336, by rfl⟩ : syracuseStep 6824897 = 5118673) B5118673
theorem B8627579 : Blo 896573 8627579 := bstep (se 1 (by rfl) ⟨6470684, by rfl⟩ : syracuseStep 8627579 = 12941369) B12941369
theorem B3122621 : Blo 896573 3122621 := bstep (se 3 (by rfl) ⟨585491, by rfl⟩ : syracuseStep 3122621 = 1170983) B1170983
theorem B2270663 : Blo 896573 2270663 := bstep (se 1 (by rfl) ⟨1702997, by rfl⟩ : syracuseStep 2270663 = 3405995) B3405995
theorem B2270713 : Blo 896573 2270713 := bstep (se 2 (by rfl) ⟨851517, by rfl⟩ : syracuseStep 2270713 = 1703035) B1703035
theorem B2271017 : Blo 896573 2271017 := bstep (se 2 (by rfl) ⟨851631, by rfl⟩ : syracuseStep 2271017 = 1703263) B1703263
theorem B1517359 : Blo 896573 1517359 := bstep (se 1 (by rfl) ⟨1138019, by rfl⟩ : syracuseStep 1517359 = 2276039) B2276039
theorem B3286865 : Blo 896573 3286865 := bstep (se 2 (by rfl) ⟨1232574, by rfl⟩ : syracuseStep 3286865 = 2465149) B2465149
theorem B2303873 : Blo 896573 2303873 := bstep (se 2 (by rfl) ⟨863952, by rfl⟩ : syracuseStep 2303873 = 1727905) B1727905
theorem B3418145 : Blo 896573 3418145 := bstep (se 2 (by rfl) ⟨1281804, by rfl⟩ : syracuseStep 3418145 = 2563609) B2563609
theorem B2271361 : Blo 896573 2271361 := bstep (se 2 (by rfl) ⟨851760, by rfl⟩ : syracuseStep 2271361 = 1703521) B1703521
theorem B2304281 : Blo 896573 2304281 := bstep (se 2 (by rfl) ⟨864105, by rfl⟩ : syracuseStep 2304281 = 1728211) B1728211
theorem B3647855 : Blo 896573 3647855 := bstep (se 1 (by rfl) ⟨2735891, by rfl⟩ : syracuseStep 3647855 = 5471783) B5471783
theorem B2304467 : Blo 896573 2304467 := bstep (se 1 (by rfl) ⟨1728350, by rfl⟩ : syracuseStep 2304467 = 3456701) B3456701
theorem B5122547 : Blo 896573 5122547 := bstep (se 1 (by rfl) ⟨3841910, by rfl⟩ : syracuseStep 5122547 = 7683821) B7683821
theorem B3844883 : Blo 896573 3844883 := bstep (se 1 (by rfl) ⟨2883662, by rfl⟩ : syracuseStep 3844883 = 5767325) B5767325
theorem B2272171 : Blo 896573 2272171 := bstep (se 1 (by rfl) ⟨1704128, by rfl⟩ : syracuseStep 2272171 = 3408257) B3408257
theorem B6466675 : Blo 896573 6466675 := bstep (se 1 (by rfl) ⟨4850006, by rfl⟩ : syracuseStep 6466675 = 9700013) B9700013
theorem B2272475 : Blo 896573 2272475 := bstep (se 1 (by rfl) ⟨1704356, by rfl⟩ : syracuseStep 2272475 = 3408713) B3408713
theorem B4107581 : Blo 896573 4107581 := bstep (se 3 (by rfl) ⟨770171, by rfl⟩ : syracuseStep 4107581 = 1540343) B1540343
theorem B2272607 : Blo 896573 2272607 := bstep (se 1 (by rfl) ⟨1704455, by rfl⟩ : syracuseStep 2272607 = 3408911) B3408911
theorem B3026375 : Blo 896573 3026375 := bstep (se 1 (by rfl) ⟨2269781, by rfl⟩ : syracuseStep 3026375 = 4539563) B4539563
theorem B896575 : Blo 896573 896575 := bstep (se 1 (by rfl) ⟨672431, by rfl⟩ : syracuseStep 896575 = 1344863) B1344863
theorem B896583 : Blo 896573 896583 := bstep (se 1 (by rfl) ⟨672437, by rfl⟩ : syracuseStep 896583 = 1344875) B1344875
theorem B896735 : Blo 896573 896735 := bstep (se 1 (by rfl) ⟨672551, by rfl⟩ : syracuseStep 896735 = 1345103) B1345103
theorem B3026699 : Blo 896573 3026699 := bstep (se 1 (by rfl) ⟨2270024, by rfl⟩ : syracuseStep 3026699 = 4540049) B4540049
theorem B896815 : Blo 896573 896815 := bstep (se 1 (by rfl) ⟨672611, by rfl⟩ : syracuseStep 896815 = 1345223) B1345223
theorem B896923 : Blo 896573 896923 := bstep (se 1 (by rfl) ⟨672692, by rfl⟩ : syracuseStep 896923 = 1345385) B1345385
theorem B896975 : Blo 896573 896975 := bstep (se 1 (by rfl) ⟨672731, by rfl⟩ : syracuseStep 896975 = 1345463) B1345463
theorem B896999 : Blo 896573 896999 := bstep (se 1 (by rfl) ⟨672749, by rfl⟩ : syracuseStep 896999 = 1345499) B1345499
theorem B3026969 : Blo 896573 3026969 := bstep (se 2 (by rfl) ⟨1135113, by rfl⟩ : syracuseStep 3026969 = 2270227) B2270227
theorem B2273305 : Blo 896573 2273305 := bstep (se 2 (by rfl) ⟨852489, by rfl⟩ : syracuseStep 2273305 = 1704979) B1704979
theorem B897311 : Blo 896573 897311 := bstep (se 1 (by rfl) ⟨672983, by rfl⟩ : syracuseStep 897311 = 1345967) B1345967
theorem B2273609 : Blo 896573 2273609 := bstep (se 2 (by rfl) ⟨852603, by rfl⟩ : syracuseStep 2273609 = 1705207) B1705207
theorem B897371 : Blo 896573 897371 := bstep (se 1 (by rfl) ⟨673028, by rfl⟩ : syracuseStep 897371 = 1346057) B1346057
theorem B897391 : Blo 896573 897391 := bstep (se 1 (by rfl) ⟨673043, by rfl⟩ : syracuseStep 897391 = 1346087) B1346087
theorem B897447 : Blo 896573 897447 := bstep (se 1 (by rfl) ⟨673085, by rfl⟩ : syracuseStep 897447 = 1346171) B1346171
theorem B897531 : Blo 896573 897531 := bstep (se 1 (by rfl) ⟨673148, by rfl⟩ : syracuseStep 897531 = 1346297) B1346297
theorem B23015987 : Blo 896573 23015987 := bstep (se 1 (by rfl) ⟨17261990, by rfl⟩ : syracuseStep 23015987 = 34523981) B34523981
theorem B897599 : Blo 896573 897599 := bstep (se 1 (by rfl) ⟨673199, by rfl⟩ : syracuseStep 897599 = 1346399) B1346399
theorem B897607 : Blo 896573 897607 := bstep (se 1 (by rfl) ⟨673205, by rfl⟩ : syracuseStep 897607 = 1346411) B1346411
theorem B897759 : Blo 896573 897759 := bstep (se 1 (by rfl) ⟨673319, by rfl⟩ : syracuseStep 897759 = 1346639) B1346639
theorem B897839 : Blo 896573 897839 := bstep (se 1 (by rfl) ⟨673379, by rfl⟩ : syracuseStep 897839 = 1346759) B1346759
theorem B897947 : Blo 896573 897947 := bstep (se 1 (by rfl) ⟨673460, by rfl⟩ : syracuseStep 897947 = 1346921) B1346921
theorem B897999 : Blo 896573 897999 := bstep (se 1 (by rfl) ⟨673499, by rfl⟩ : syracuseStep 897999 = 1346999) B1346999
theorem B898023 : Blo 896573 898023 := bstep (se 1 (by rfl) ⟨673517, by rfl⟩ : syracuseStep 898023 = 1347035) B1347035
theorem B8631269 : Blo 896573 8631269 := bstep (se 4 (by rfl) ⟨809181, by rfl⟩ : syracuseStep 8631269 = 1618363) B1618363
theorem B6829271 : Blo 896573 6829271 := bstep (se 1 (by rfl) ⟨5121953, by rfl⟩ : syracuseStep 6829271 = 10243907) B10243907
theorem B3028211 : Blo 896573 3028211 := bstep (se 1 (by rfl) ⟨2271158, by rfl⟩ : syracuseStep 3028211 = 4542317) B4542317
theorem B898335 : Blo 896573 898335 := bstep (se 1 (by rfl) ⟨673751, by rfl⟩ : syracuseStep 898335 = 1347503) B1347503
theorem B2372903 : Blo 896573 2372903 := bstep (se 1 (by rfl) ⟨1779677, by rfl⟩ : syracuseStep 2372903 = 3559355) B3559355
theorem B898395 : Blo 896573 898395 := bstep (se 1 (by rfl) ⟨673796, by rfl⟩ : syracuseStep 898395 = 1347593) B1347593
theorem B3028319 : Blo 896573 3028319 := bstep (se 1 (by rfl) ⟨2271239, by rfl⟩ : syracuseStep 3028319 = 4542479) B4542479
theorem B898415 : Blo 896573 898415 := bstep (se 1 (by rfl) ⟨673811, by rfl⟩ : syracuseStep 898415 = 1347623) B1347623
theorem B898471 : Blo 896573 898471 := bstep (se 1 (by rfl) ⟨673853, by rfl⟩ : syracuseStep 898471 = 1347707) B1347707
theorem B898555 : Blo 896573 898555 := bstep (se 1 (by rfl) ⟨673916, by rfl⟩ : syracuseStep 898555 = 1347833) B1347833
theorem B898623 : Blo 896573 898623 := bstep (se 1 (by rfl) ⟨673967, by rfl⟩ : syracuseStep 898623 = 1347935) B1347935
theorem B898631 : Blo 896573 898631 := bstep (se 1 (by rfl) ⟨673973, by rfl⟩ : syracuseStep 898631 = 1347947) B1347947
theorem B898783 : Blo 896573 898783 := bstep (se 1 (by rfl) ⟨674087, by rfl⟩ : syracuseStep 898783 = 1348175) B1348175
theorem B1750825 : Blo 896573 1750825 := bstep (se 2 (by rfl) ⟨656559, by rfl⟩ : syracuseStep 1750825 = 1313119) B1313119
theorem B898863 : Blo 896573 898863 := bstep (se 1 (by rfl) ⟨674147, by rfl⟩ : syracuseStep 898863 = 1348295) B1348295
theorem B7288631 : Blo 896573 7288631 := bstep (se 1 (by rfl) ⟨5466473, by rfl⟩ : syracuseStep 7288631 = 10932947) B10932947
theorem B898971 : Blo 896573 898971 := bstep (se 1 (by rfl) ⟨674228, by rfl⟩ : syracuseStep 898971 = 1348457) B1348457
theorem B899023 : Blo 896573 899023 := bstep (se 1 (by rfl) ⟨674267, by rfl⟩ : syracuseStep 899023 = 1348535) B1348535
theorem B899047 : Blo 896573 899047 := bstep (se 1 (by rfl) ⟨674285, by rfl⟩ : syracuseStep 899047 = 1348571) B1348571
theorem B899359 : Blo 896573 899359 := bstep (se 1 (by rfl) ⟨674519, by rfl⟩ : syracuseStep 899359 = 1349039) B1349039
theorem B899419 : Blo 896573 899419 := bstep (se 1 (by rfl) ⟨674564, by rfl⟩ : syracuseStep 899419 = 1349129) B1349129
theorem B899439 : Blo 896573 899439 := bstep (se 1 (by rfl) ⟨674579, by rfl⟩ : syracuseStep 899439 = 1349159) B1349159
theorem B4864367 : Blo 896573 4864367 := bstep (se 1 (by rfl) ⟨3648275, by rfl⟩ : syracuseStep 4864367 = 7296551) B7296551
theorem B899495 : Blo 896573 899495 := bstep (se 1 (by rfl) ⟨674621, by rfl⟩ : syracuseStep 899495 = 1349243) B1349243
theorem B899579 : Blo 896573 899579 := bstep (se 1 (by rfl) ⟨674684, by rfl⟩ : syracuseStep 899579 = 1349369) B1349369
theorem B5192255 : Blo 896573 5192255 := bstep (se 1 (by rfl) ⟨3894191, by rfl⟩ : syracuseStep 5192255 = 7788383) B7788383
theorem B899647 : Blo 896573 899647 := bstep (se 1 (by rfl) ⟨674735, by rfl⟩ : syracuseStep 899647 = 1349471) B1349471
theorem B1915463 : Blo 896573 1915463 := bstep (se 1 (by rfl) ⟨1436597, by rfl⟩ : syracuseStep 1915463 = 2873195) B2873195
theorem B899655 : Blo 896573 899655 := bstep (se 1 (by rfl) ⟨674741, by rfl⟩ : syracuseStep 899655 = 1349483) B1349483
theorem B7289477 : Blo 896573 7289477 := bstep (se 4 (by rfl) ⟨683388, by rfl⟩ : syracuseStep 7289477 = 1366777) B1366777
theorem B899807 : Blo 896573 899807 := bstep (se 1 (by rfl) ⟨674855, by rfl⟩ : syracuseStep 899807 = 1349711) B1349711
theorem B899887 : Blo 896573 899887 := bstep (se 1 (by rfl) ⟨674915, by rfl⟩ : syracuseStep 899887 = 1349831) B1349831
theorem B3029885 : Blo 896573 3029885 := bstep (se 3 (by rfl) ⟨568103, by rfl⟩ : syracuseStep 3029885 = 1136207) B1136207
theorem B899995 : Blo 896573 899995 := bstep (se 1 (by rfl) ⟨674996, by rfl⟩ : syracuseStep 899995 = 1349993) B1349993
theorem B900047 : Blo 896573 900047 := bstep (se 1 (by rfl) ⟨675035, by rfl⟩ : syracuseStep 900047 = 1350071) B1350071
theorem B900071 : Blo 896573 900071 := bstep (se 1 (by rfl) ⟨675053, by rfl⟩ : syracuseStep 900071 = 1350107) B1350107
theorem B3030155 : Blo 896573 3030155 := bstep (se 1 (by rfl) ⟨2272616, by rfl⟩ : syracuseStep 3030155 = 4545233) B4545233
theorem B2276495 : Blo 896573 2276495 := bstep (se 1 (by rfl) ⟨1707371, by rfl⟩ : syracuseStep 2276495 = 3414743) B3414743
theorem B19414205 : Blo 896573 19414205 := bstep (se 3 (by rfl) ⟨3640163, by rfl⟩ : syracuseStep 19414205 = 7280327) B7280327
theorem B900383 : Blo 896573 900383 := bstep (se 1 (by rfl) ⟨675287, by rfl⟩ : syracuseStep 900383 = 1350575) B1350575
theorem B900443 : Blo 896573 900443 := bstep (se 1 (by rfl) ⟨675332, by rfl⟩ : syracuseStep 900443 = 1350665) B1350665
theorem B1916257 : Blo 896573 1916257 := bstep (se 2 (by rfl) ⟨718596, by rfl⟩ : syracuseStep 1916257 = 1437193) B1437193
theorem B900463 : Blo 896573 900463 := bstep (se 1 (by rfl) ⟨675347, by rfl⟩ : syracuseStep 900463 = 1350695) B1350695
theorem B900519 : Blo 896573 900519 := bstep (se 1 (by rfl) ⟨675389, by rfl⟩ : syracuseStep 900519 = 1350779) B1350779
theorem B27704825 : Blo 896573 27704825 := bstep (se 2 (by rfl) ⟨10389309, by rfl⟩ : syracuseStep 27704825 = 20778619) B20778619
theorem B5127695 : Blo 896573 5127695 := bstep (se 1 (by rfl) ⟨3845771, by rfl⟩ : syracuseStep 5127695 = 7691543) B7691543
theorem B2048105 : Blo 896573 2048105 := bstep (se 2 (by rfl) ⟨768039, by rfl⟩ : syracuseStep 2048105 = 1536079) B1536079
theorem B3031775 : Blo 896573 3031775 := bstep (se 1 (by rfl) ⟨2273831, by rfl⟩ : syracuseStep 3031775 = 4547663) B4547663
theorem B6833159 : Blo 896573 6833159 := bstep (se 1 (by rfl) ⟨5124869, by rfl⟩ : syracuseStep 6833159 = 10249739) B10249739
theorem B2278439 : Blo 896573 2278439 := bstep (se 1 (by rfl) ⟨1708829, by rfl⟩ : syracuseStep 2278439 = 3417659) B3417659
theorem B3032207 : Blo 896573 3032207 := bstep (se 1 (by rfl) ⟨2274155, by rfl⟩ : syracuseStep 3032207 = 4548311) B4548311
theorem B13157741 : Blo 896573 13157741 := bstep (se 3 (by rfl) ⟨2467076, by rfl⟩ : syracuseStep 13157741 = 4934153) B4934153
theorem B2278793 : Blo 896573 2278793 := bstep (se 2 (by rfl) ⟨854547, by rfl⟩ : syracuseStep 2278793 = 1709095) B1709095
theorem B6145625 : Blo 896573 6145625 := bstep (se 2 (by rfl) ⟨2304609, by rfl⟩ : syracuseStep 6145625 = 4609219) B4609219
theorem B17483791 : Blo 896573 17483791 := bstep (se 1 (by rfl) ⟨13112843, by rfl⟩ : syracuseStep 17483791 = 26225687) B26225687
theorem B2017385 : Blo 896573 2017385 := bstep (se 2 (by rfl) ⟨756519, by rfl⟩ : syracuseStep 2017385 = 1513039) B1513039
theorem B3033341 : Blo 896573 3033341 := bstep (se 3 (by rfl) ⟨568751, by rfl⟩ : syracuseStep 3033341 = 1137503) B1137503
theorem B4540697 : Blo 896573 4540697 := bstep (se 2 (by rfl) ⟨1702761, by rfl⟩ : syracuseStep 4540697 = 3405523) B3405523
theorem B2017871 : Blo 896573 2017871 := bstep (se 1 (by rfl) ⟨1513403, by rfl⟩ : syracuseStep 2017871 = 3026807) B3026807
theorem B3885707 : Blo 896573 3885707 := bstep (se 1 (by rfl) ⟨2914280, by rfl⟩ : syracuseStep 3885707 = 5828561) B5828561
theorem B9718481 : Blo 896573 9718481 := bstep (se 2 (by rfl) ⟨3644430, by rfl⟩ : syracuseStep 9718481 = 7288861) B7288861
theorem B2018015 : Blo 896573 2018015 := bstep (se 1 (by rfl) ⟨1513511, by rfl⟩ : syracuseStep 2018015 = 3027023) B3027023
theorem B2018267 : Blo 896573 2018267 := bstep (se 1 (by rfl) ⟨1513700, by rfl⟩ : syracuseStep 2018267 = 3027401) B3027401
theorem B7687169 : Blo 896573 7687169 := bstep (se 2 (by rfl) ⟨2882688, by rfl⟩ : syracuseStep 7687169 = 5765377) B5765377
theorem B8637455 : Blo 896573 8637455 := bstep (se 1 (by rfl) ⟨6478091, by rfl⟩ : syracuseStep 8637455 = 12956183) B12956183
theorem B3034151 : Blo 896573 3034151 := bstep (se 1 (by rfl) ⟨2275613, by rfl⟩ : syracuseStep 3034151 = 4551227) B4551227
theorem B2018447 : Blo 896573 2018447 := bstep (se 1 (by rfl) ⟨1513835, by rfl⟩ : syracuseStep 2018447 = 3027671) B3027671
theorem B2018537 : Blo 896573 2018537 := bstep (se 2 (by rfl) ⟨756951, by rfl⟩ : syracuseStep 2018537 = 1513903) B1513903
theorem B2018591 : Blo 896573 2018591 := bstep (se 1 (by rfl) ⟨1513943, by rfl⟩ : syracuseStep 2018591 = 3027887) B3027887
theorem B3034583 : Blo 896573 3034583 := bstep (se 1 (by rfl) ⟨2275937, by rfl⟩ : syracuseStep 3034583 = 4551875) B4551875
theorem B8867501 : Blo 896573 8867501 := bstep (se 3 (by rfl) ⟨1662656, by rfl⟩ : syracuseStep 8867501 = 3325313) B3325313
theorem B2019113 : Blo 896573 2019113 := bstep (se 2 (by rfl) ⟨757167, by rfl⟩ : syracuseStep 2019113 = 1514335) B1514335
theorem B2281835 : Blo 896573 2281835 := bstep (se 1 (by rfl) ⟨1711376, by rfl⟩ : syracuseStep 2281835 = 3422753) B3422753
theorem B2020175 : Blo 896573 2020175 := bstep (se 1 (by rfl) ⟨1515131, by rfl⟩ : syracuseStep 2020175 = 3030263) B3030263
theorem B1921963 : Blo 896573 1921963 := bstep (se 1 (by rfl) ⟨1441472, by rfl⟩ : syracuseStep 1921963 = 2882945) B2882945
theorem B4543451 : Blo 896573 4543451 := bstep (se 1 (by rfl) ⟨3407588, by rfl⟩ : syracuseStep 4543451 = 6815177) B6815177
theorem B2020391 : Blo 896573 2020391 := bstep (se 1 (by rfl) ⟨1515293, by rfl⟩ : syracuseStep 2020391 = 3030587) B3030587
theorem B3036257 : Blo 896573 3036257 := bstep (se 2 (by rfl) ⟨1138596, by rfl⟩ : syracuseStep 3036257 = 2277193) B2277193
theorem B4543613 : Blo 896573 4543613 := bstep (se 3 (by rfl) ⟨851927, by rfl⟩ : syracuseStep 4543613 = 1703855) B1703855
theorem B2020571 : Blo 896573 2020571 := bstep (se 1 (by rfl) ⟨1515428, by rfl⟩ : syracuseStep 2020571 = 3030857) B3030857
theorem B2020769 : Blo 896573 2020769 := bstep (se 2 (by rfl) ⟨757788, by rfl⟩ : syracuseStep 2020769 = 1515577) B1515577
theorem B4543937 : Blo 896573 4543937 := bstep (se 2 (by rfl) ⟨1703976, by rfl⟩ : syracuseStep 4543937 = 3407953) B3407953
theorem B8181287 : Blo 896573 8181287 := bstep (se 1 (by rfl) ⟨6135965, by rfl⟩ : syracuseStep 8181287 = 12271931) B12271931
theorem B2021327 : Blo 896573 2021327 := bstep (se 1 (by rfl) ⟨1515995, by rfl⟩ : syracuseStep 2021327 = 3031991) B3031991
theorem B1923023 : Blo 896573 1923023 := bstep (se 1 (by rfl) ⟨1442267, by rfl⟩ : syracuseStep 1923023 = 2884535) B2884535
theorem B24959177 : Blo 896573 24959177 := bstep (se 2 (by rfl) ⟨9359691, by rfl⟩ : syracuseStep 24959177 = 18719383) B18719383
theorem B2021705 : Blo 896573 2021705 := bstep (se 2 (by rfl) ⟨758139, by rfl⟩ : syracuseStep 2021705 = 1516279) B1516279
theorem B7690585 : Blo 896573 7690585 := bstep (se 2 (by rfl) ⟨2883969, by rfl⟩ : syracuseStep 7690585 = 5767939) B5767939
theorem B2021723 : Blo 896573 2021723 := bstep (se 1 (by rfl) ⟨1516292, by rfl⟩ : syracuseStep 2021723 = 3032585) B3032585
theorem B1137007 : Blo 896573 1137007 := bstep (se 1 (by rfl) ⟨852755, by rfl⟩ : syracuseStep 1137007 = 1705511) B1705511
theorem B3037607 : Blo 896573 3037607 := bstep (se 1 (by rfl) ⟨2278205, by rfl⟩ : syracuseStep 3037607 = 4556411) B4556411
theorem B3037769 : Blo 896573 3037769 := bstep (se 2 (by rfl) ⟨1139163, by rfl⟩ : syracuseStep 3037769 = 2278327) B2278327
theorem B7690859 : Blo 896573 7690859 := bstep (se 1 (by rfl) ⟨5768144, by rfl⟩ : syracuseStep 7690859 = 11536289) B11536289
theorem B2022299 : Blo 896573 2022299 := bstep (se 1 (by rfl) ⟨1516724, by rfl⟩ : syracuseStep 2022299 = 3033449) B3033449
theorem B2022497 : Blo 896573 2022497 := bstep (se 2 (by rfl) ⟨758436, by rfl⟩ : syracuseStep 2022497 = 1516873) B1516873
theorem B1137883 : Blo 896573 1137883 := bstep (se 1 (by rfl) ⟨853412, by rfl⟩ : syracuseStep 1137883 = 1706825) B1706825
theorem B2022695 : Blo 896573 2022695 := bstep (se 1 (by rfl) ⟨1517021, by rfl⟩ : syracuseStep 2022695 = 3034043) B3034043
theorem B4316615 : Blo 896573 4316615 := bstep (se 1 (by rfl) ⟨3237461, by rfl⟩ : syracuseStep 4316615 = 6474923) B6474923
theorem B8740345 : Blo 896573 8740345 := bstep (se 2 (by rfl) ⟨3277629, by rfl⟩ : syracuseStep 8740345 = 6555259) B6555259
theorem B38788631 : Blo 896573 38788631 := bstep (se 1 (by rfl) ⟨29091473, by rfl⟩ : syracuseStep 38788631 = 58182947) B58182947
theorem B7691921 : Blo 896573 7691921 := bstep (se 2 (by rfl) ⟨2884470, by rfl⟩ : syracuseStep 7691921 = 5768941) B5768941
theorem B9723539 : Blo 896573 9723539 := bstep (se 1 (by rfl) ⟨7292654, by rfl⟩ : syracuseStep 9723539 = 14585309) B14585309
theorem B2023073 : Blo 896573 2023073 := bstep (se 2 (by rfl) ⟨758652, by rfl⟩ : syracuseStep 2023073 = 1517305) B1517305
theorem B2023433 : Blo 896573 2023433 := bstep (se 2 (by rfl) ⟨758787, by rfl⟩ : syracuseStep 2023433 = 1517575) B1517575
theorem B2023847 : Blo 896573 2023847 := bstep (se 1 (by rfl) ⟨1517885, by rfl⟩ : syracuseStep 2023847 = 3035771) B3035771
theorem B2023955 : Blo 896573 2023955 := bstep (se 1 (by rfl) ⟨1517966, by rfl⟩ : syracuseStep 2023955 = 3035933) B3035933
theorem B2155079 : Blo 896573 2155079 := bstep (se 1 (by rfl) ⟨1616309, by rfl⟩ : syracuseStep 2155079 = 3232619) B3232619
theorem B2024009 : Blo 896573 2024009 := bstep (se 2 (by rfl) ⟨759003, by rfl⟩ : syracuseStep 2024009 = 1518007) B1518007
theorem B1139503 : Blo 896573 1139503 := bstep (se 1 (by rfl) ⟨854627, by rfl⟩ : syracuseStep 1139503 = 1709255) B1709255
theorem B5530463 : Blo 896573 5530463 := bstep (se 1 (by rfl) ⟨4147847, by rfl⟩ : syracuseStep 5530463 = 8295695) B8295695
theorem B2024423 : Blo 896573 2024423 := bstep (se 1 (by rfl) ⟨1518317, by rfl⟩ : syracuseStep 2024423 = 3036635) B3036635
theorem B2155511 : Blo 896573 2155511 := bstep (se 1 (by rfl) ⟨1616633, by rfl⟩ : syracuseStep 2155511 = 3233267) B3233267
theorem B7693319 : Blo 896573 7693319 := bstep (se 1 (by rfl) ⟨5769989, by rfl⟩ : syracuseStep 7693319 = 11539979) B11539979
theorem B1008859 : Blo 896573 1008859 := bstep (se 1 (by rfl) ⟨756644, by rfl⟩ : syracuseStep 1008859 = 1513289) B1513289
theorem B2024801 : Blo 896573 2024801 := bstep (se 2 (by rfl) ⟨759300, by rfl⟩ : syracuseStep 2024801 = 1518601) B1518601
theorem B2024891 : Blo 896573 2024891 := bstep (se 1 (by rfl) ⟨1518668, by rfl⟩ : syracuseStep 2024891 = 3037337) B3037337
theorem B1009147 : Blo 896573 1009147 := bstep (se 1 (by rfl) ⟨756860, by rfl⟩ : syracuseStep 1009147 = 1513721) B1513721
theorem B2025017 : Blo 896573 2025017 := bstep (se 2 (by rfl) ⟨759381, by rfl⟩ : syracuseStep 2025017 = 1518763) B1518763
theorem B19392061 : Blo 896573 19392061 := bstep (se 3 (by rfl) ⟨3636011, by rfl⟩ : syracuseStep 19392061 = 7272023) B7272023
theorem B1009327 : Blo 896573 1009327 := bstep (se 1 (by rfl) ⟨756995, by rfl⟩ : syracuseStep 1009327 = 1513991) B1513991
theorem B1009615 : Blo 896573 1009615 := bstep (se 1 (by rfl) ⟨757211, by rfl⟩ : syracuseStep 1009615 = 1514423) B1514423
theorem B31057901 : Blo 896573 31057901 := bstep (se 3 (by rfl) ⟨5823356, by rfl⟩ : syracuseStep 31057901 = 11646713) B11646713
theorem B3074183 : Blo 896573 3074183 := bstep (se 1 (by rfl) ⟨2305637, by rfl⟩ : syracuseStep 3074183 = 4611275) B4611275
theorem B2025683 : Blo 896573 2025683 := bstep (se 1 (by rfl) ⟨1519262, by rfl⟩ : syracuseStep 2025683 = 3038525) B3038525
theorem B5761277 : Blo 896573 5761277 := bstep (se 3 (by rfl) ⟨1080239, by rfl⟩ : syracuseStep 5761277 = 2160479) B2160479
theorem B2025737 : Blo 896573 2025737 := bstep (se 2 (by rfl) ⟨759651, by rfl⟩ : syracuseStep 2025737 = 1519303) B1519303
theorem B1010011 : Blo 896573 1010011 := bstep (se 1 (by rfl) ⟨757508, by rfl⟩ : syracuseStep 1010011 = 1515017) B1515017
theorem B1730983 : Blo 896573 1730983 := bstep (se 1 (by rfl) ⟨1298237, by rfl⟩ : syracuseStep 1730983 = 2596475) B2596475
theorem B1010119 : Blo 896573 1010119 := bstep (se 1 (by rfl) ⟨757589, by rfl⟩ : syracuseStep 1010119 = 1515179) B1515179
theorem B3238355 : Blo 896573 3238355 := bstep (se 1 (by rfl) ⟨2428766, by rfl⟩ : syracuseStep 3238355 = 4857533) B4857533
theorem B2025953 : Blo 896573 2025953 := bstep (se 2 (by rfl) ⟨759732, by rfl⟩ : syracuseStep 2025953 = 1519465) B1519465
theorem B39414275 : Blo 896573 39414275 := bstep (se 1 (by rfl) ⟨29560706, by rfl⟩ : syracuseStep 39414275 = 59121413) B59121413
theorem B2026259 : Blo 896573 2026259 := bstep (se 1 (by rfl) ⟨1519694, by rfl⟩ : syracuseStep 2026259 = 3039389) B3039389
theorem B1010479 : Blo 896573 1010479 := bstep (se 1 (by rfl) ⟨757859, by rfl⟩ : syracuseStep 1010479 = 1515719) B1515719
theorem B1010587 : Blo 896573 1010587 := bstep (se 1 (by rfl) ⟨757940, by rfl⟩ : syracuseStep 1010587 = 1515881) B1515881
theorem B7892045 : Blo 896573 7892045 := bstep (se 3 (by rfl) ⟨1479758, by rfl⟩ : syracuseStep 7892045 = 2959517) B2959517
theorem B5106827 : Blo 896573 5106827 := bstep (se 1 (by rfl) ⟨3830120, by rfl⟩ : syracuseStep 5106827 = 7660241) B7660241
theorem B1010983 : Blo 896573 1010983 := bstep (se 1 (by rfl) ⟨758237, by rfl⟩ : syracuseStep 1010983 = 1516475) B1516475
theorem B1011055 : Blo 896573 1011055 := bstep (se 1 (by rfl) ⟨758291, by rfl⟩ : syracuseStep 1011055 = 1516583) B1516583
theorem B6909371 : Blo 896573 6909371 := bstep (se 1 (by rfl) ⟨5182028, by rfl⟩ : syracuseStep 6909371 = 10364057) B10364057
theorem B1011271 : Blo 896573 1011271 := bstep (se 1 (by rfl) ⟨758453, by rfl⟩ : syracuseStep 1011271 = 1516907) B1516907
theorem B9728171 : Blo 896573 9728171 := bstep (se 1 (by rfl) ⟨7296128, by rfl⟩ : syracuseStep 9728171 = 14592257) B14592257
theorem B1012135 : Blo 896573 1012135 := bstep (se 1 (by rfl) ⟨759101, by rfl⟩ : syracuseStep 1012135 = 1518203) B1518203
theorem B5763635 : Blo 896573 5763635 := bstep (se 1 (by rfl) ⟨4322726, by rfl⟩ : syracuseStep 5763635 = 8645453) B8645453
theorem B1536619 : Blo 896573 1536619 := bstep (se 1 (by rfl) ⟨1152464, by rfl⟩ : syracuseStep 1536619 = 2304929) B2304929
theorem B5763737 : Blo 896573 5763737 := bstep (se 2 (by rfl) ⟨2161401, by rfl⟩ : syracuseStep 5763737 = 4322803) B4322803
theorem B58192789 : Blo 896573 58192789 := bstep (se 6 (by rfl) ⟨1363893, by rfl⟩ : syracuseStep 58192789 = 2727787) B2727787
theorem B1012711 : Blo 896573 1012711 := bstep (se 1 (by rfl) ⟨759533, by rfl⟩ : syracuseStep 1012711 = 1519067) B1519067
theorem B11531321 : Blo 896573 11531321 := bstep (se 2 (by rfl) ⟨4324245, by rfl⟩ : syracuseStep 11531321 = 8648491) B8648491
theorem B7271639 : Blo 896573 7271639 := bstep (se 1 (by rfl) ⟨5453729, by rfl⟩ : syracuseStep 7271639 = 10907459) B10907459
theorem B4617577 : Blo 896573 4617577 := bstep (se 2 (by rfl) ⟨1731591, by rfl⟩ : syracuseStep 4617577 = 3463183) B3463183
theorem B2553277 : Blo 896573 2553277 := bstep (se 3 (by rfl) ⟨478739, by rfl⟩ : syracuseStep 2553277 = 957479) B957479
theorem B4552199 : Blo 896573 4552199 := bstep (se 1 (by rfl) ⟨3414149, by rfl⟩ : syracuseStep 4552199 = 6828299) B6828299
theorem B947783 : Blo 896573 947783 := bstep (se 1 (by rfl) ⟨710837, by rfl⟩ : syracuseStep 947783 = 1421675) B1421675
theorem B18708317 : Blo 896573 18708317 := bstep (se 3 (by rfl) ⟨3507809, by rfl⟩ : syracuseStep 18708317 = 7015619) B7015619
theorem B3897193 : Blo 896573 3897193 := bstep (se 2 (by rfl) ⟨1461447, by rfl⟩ : syracuseStep 3897193 = 2922895) B2922895
theorem B4552685 : Blo 896573 4552685 := bstep (se 3 (by rfl) ⟨853628, by rfl⟩ : syracuseStep 4552685 = 1707257) B1707257
theorem B3406009 : Blo 896573 3406009 := bstep (se 2 (by rfl) ⟨1277253, by rfl⟩ : syracuseStep 3406009 = 2554507) B2554507
theorem B5110199 : Blo 896573 5110199 := bstep (se 1 (by rfl) ⟨3832649, by rfl⟩ : syracuseStep 5110199 = 7665299) B7665299
theorem B9238967 : Blo 896573 9238967 := bstep (se 1 (by rfl) ⟨6929225, by rfl⟩ : syracuseStep 9238967 = 13858451) B13858451
theorem B4553171 : Blo 896573 4553171 := bstep (se 1 (by rfl) ⟨3414878, by rfl⟩ : syracuseStep 4553171 = 6829757) B6829757
theorem B6158987 : Blo 896573 6158987 := bstep (se 1 (by rfl) ⟨4619240, by rfl⟩ : syracuseStep 6158987 = 9238481) B9238481
theorem B4553495 : Blo 896573 4553495 := bstep (se 1 (by rfl) ⟨3415121, by rfl⟩ : syracuseStep 4553495 = 6830243) B6830243
theorem B2882459 : Blo 896573 2882459 := bstep (se 1 (by rfl) ⟨2161844, by rfl⟩ : syracuseStep 2882459 = 4323689) B4323689
theorem B2555351 : Blo 896573 2555351 := bstep (se 1 (by rfl) ⟨1916513, by rfl⟩ : syracuseStep 2555351 = 3833027) B3833027
theorem B24641171 : Blo 896573 24641171 := bstep (se 1 (by rfl) ⟨18480878, by rfl⟩ : syracuseStep 24641171 = 36961757) B36961757
theorem B6815663 : Blo 896573 6815663 := bstep (se 1 (by rfl) ⟨5111747, by rfl⟩ : syracuseStep 6815663 = 10223495) B10223495
theorem B1277903 : Blo 896573 1277903 := bstep (se 1 (by rfl) ⟨958427, by rfl⟩ : syracuseStep 1277903 = 1916855) B1916855
theorem B12451843 : Blo 896573 12451843 := bstep (se 1 (by rfl) ⟨9338882, by rfl⟩ : syracuseStep 12451843 = 18677765) B18677765
theorem B5767787 : Blo 896573 5767787 := bstep (se 1 (by rfl) ⟨4325840, by rfl⟩ : syracuseStep 5767787 = 8651681) B8651681
theorem B4555439 : Blo 896573 4555439 := bstep (se 1 (by rfl) ⟨3416579, by rfl⟩ : syracuseStep 4555439 = 6833159) B6833159
theorem B4850441 : Blo 896573 4850441 := bstep (se 2 (by rfl) ⟨1818915, by rfl⟩ : syracuseStep 4850441 = 3637831) B3637831
theorem B4326263 : Blo 896573 4326263 := bstep (se 1 (by rfl) ⟨3244697, by rfl⟩ : syracuseStep 4326263 = 6489395) B6489395
theorem B4097083 : Blo 896573 4097083 := bstep (se 1 (by rfl) ⟨3072812, by rfl⟩ : syracuseStep 4097083 = 6145625) B6145625
theorem B1344923 : Blo 896573 1344923 := bstep (se 1 (by rfl) ⟨1008692, by rfl⟩ : syracuseStep 1344923 = 2017385) B2017385
theorem B1345145 : Blo 896573 1345145 := bstep (se 2 (by rfl) ⟨504429, by rfl⟩ : syracuseStep 1345145 = 1008859) B1008859
theorem B1345247 : Blo 896573 1345247 := bstep (se 1 (by rfl) ⟨1008935, by rfl⟩ : syracuseStep 1345247 = 2017871) B2017871
theorem B2590471 : Blo 896573 2590471 := bstep (se 1 (by rfl) ⟨1942853, by rfl⟩ : syracuseStep 2590471 = 3885707) B3885707
theorem B1345343 : Blo 896573 1345343 := bstep (se 1 (by rfl) ⟨1009007, by rfl⟩ : syracuseStep 1345343 = 2018015) B2018015
theorem B5113799 : Blo 896573 5113799 := bstep (se 1 (by rfl) ⟨3835349, by rfl⟩ : syracuseStep 5113799 = 7670699) B7670699
theorem B1345511 : Blo 896573 1345511 := bstep (se 1 (by rfl) ⟨1009133, by rfl⟩ : syracuseStep 1345511 = 2018267) B2018267
theorem B1345529 : Blo 896573 1345529 := bstep (se 2 (by rfl) ⟨504573, by rfl⟩ : syracuseStep 1345529 = 1009147) B1009147
theorem B25856081 : Blo 896573 25856081 := bstep (se 2 (by rfl) ⟨9696030, by rfl⟩ : syracuseStep 25856081 = 19392061) B19392061
theorem B1345631 : Blo 896573 1345631 := bstep (se 1 (by rfl) ⟨1009223, by rfl⟩ : syracuseStep 1345631 = 2018447) B2018447
theorem B1345691 : Blo 896573 1345691 := bstep (se 1 (by rfl) ⟨1009268, by rfl⟩ : syracuseStep 1345691 = 2018537) B2018537
theorem B1345727 : Blo 896573 1345727 := bstep (se 1 (by rfl) ⟨1009295, by rfl⟩ : syracuseStep 1345727 = 2018591) B2018591
theorem B5769427 : Blo 896573 5769427 := bstep (se 1 (by rfl) ⟨4327070, by rfl⟩ : syracuseStep 5769427 = 8654141) B8654141
theorem B1345769 : Blo 896573 1345769 := bstep (se 2 (by rfl) ⟨504663, by rfl⟩ : syracuseStep 1345769 = 1009327) B1009327
theorem B1346075 : Blo 896573 1346075 := bstep (se 1 (by rfl) ⟨1009556, by rfl⟩ : syracuseStep 1346075 = 2019113) B2019113
theorem B1346153 : Blo 896573 1346153 := bstep (se 2 (by rfl) ⟨504807, by rfl⟩ : syracuseStep 1346153 = 1009615) B1009615
theorem B1346681 : Blo 896573 1346681 := bstep (se 2 (by rfl) ⟨505005, by rfl⟩ : syracuseStep 1346681 = 1010011) B1010011
theorem B3411143 : Blo 896573 3411143 := bstep (se 1 (by rfl) ⟨2558357, by rfl⟩ : syracuseStep 3411143 = 5116715) B5116715
theorem B20712667 : Blo 896573 20712667 := bstep (se 1 (by rfl) ⟨15534500, by rfl⟩ : syracuseStep 20712667 = 31069001) B31069001
theorem B1346783 : Blo 896573 1346783 := bstep (se 1 (by rfl) ⟨1010087, by rfl⟩ : syracuseStep 1346783 = 2020175) B2020175
theorem B1346825 : Blo 896573 1346825 := bstep (se 2 (by rfl) ⟨505059, by rfl⟩ : syracuseStep 1346825 = 1010119) B1010119
theorem B1346927 : Blo 896573 1346927 := bstep (se 1 (by rfl) ⟨1010195, by rfl⟩ : syracuseStep 1346927 = 2020391) B2020391
theorem B1347047 : Blo 896573 1347047 := bstep (se 1 (by rfl) ⟨1010285, by rfl⟩ : syracuseStep 1347047 = 2020571) B2020571
theorem B1445467 : Blo 896573 1445467 := bstep (se 1 (by rfl) ⟨1084100, by rfl⟩ : syracuseStep 1445467 = 2168201) B2168201
theorem B1347179 : Blo 896573 1347179 := bstep (se 1 (by rfl) ⟨1010384, by rfl⟩ : syracuseStep 1347179 = 2020769) B2020769
theorem B1347305 : Blo 896573 1347305 := bstep (se 2 (by rfl) ⟨505239, by rfl⟩ : syracuseStep 1347305 = 1010479) B1010479
theorem B1347449 : Blo 896573 1347449 := bstep (se 2 (by rfl) ⟨505293, by rfl⟩ : syracuseStep 1347449 = 1010587) B1010587
theorem B1347551 : Blo 896573 1347551 := bstep (se 1 (by rfl) ⟨1010663, by rfl⟩ : syracuseStep 1347551 = 2021327) B2021327
theorem B1282015 : Blo 896573 1282015 := bstep (se 1 (by rfl) ⟨961511, by rfl⟩ : syracuseStep 1282015 = 1923023) B1923023
theorem B8622233 : Blo 896573 8622233 := bstep (se 2 (by rfl) ⟨3233337, by rfl⟩ : syracuseStep 8622233 = 6466675) B6466675
theorem B4853945 : Blo 896573 4853945 := bstep (se 2 (by rfl) ⟨1820229, by rfl⟩ : syracuseStep 4853945 = 3640459) B3640459
theorem B2527421 : Blo 896573 2527421 := bstep (se 3 (by rfl) ⟨473891, by rfl⟩ : syracuseStep 2527421 = 947783) B947783
theorem B1347803 : Blo 896573 1347803 := bstep (se 1 (by rfl) ⟨1010852, by rfl⟩ : syracuseStep 1347803 = 2021705) B2021705
theorem B1347815 : Blo 896573 1347815 := bstep (se 1 (by rfl) ⟨1010861, by rfl⟩ : syracuseStep 1347815 = 2021723) B2021723
theorem B1347977 : Blo 896573 1347977 := bstep (se 2 (by rfl) ⟨505491, by rfl⟩ : syracuseStep 1347977 = 1010983) B1010983
theorem B1348073 : Blo 896573 1348073 := bstep (se 2 (by rfl) ⟨505527, by rfl⟩ : syracuseStep 1348073 = 1011055) B1011055
theorem B1348199 : Blo 896573 1348199 := bstep (se 1 (by rfl) ⟨1011149, by rfl⟩ : syracuseStep 1348199 = 2022299) B2022299
theorem B1348331 : Blo 896573 1348331 := bstep (se 1 (by rfl) ⟨1011248, by rfl⟩ : syracuseStep 1348331 = 2022497) B2022497
theorem B1348361 : Blo 896573 1348361 := bstep (se 2 (by rfl) ⟨505635, by rfl⟩ : syracuseStep 1348361 = 1011271) B1011271
theorem B1348463 : Blo 896573 1348463 := bstep (se 1 (by rfl) ⟨1011347, by rfl⟩ : syracuseStep 1348463 = 2022695) B2022695
theorem B25859087 : Blo 896573 25859087 := bstep (se 1 (by rfl) ⟨19394315, by rfl⟩ : syracuseStep 25859087 = 38788631) B38788631
theorem B1348715 : Blo 896573 1348715 := bstep (se 1 (by rfl) ⟨1011536, by rfl⟩ : syracuseStep 1348715 = 2023073) B2023073
theorem B5117215 : Blo 896573 5117215 := bstep (se 1 (by rfl) ⟨3837911, by rfl⟩ : syracuseStep 5117215 = 7675823) B7675823
theorem B1348955 : Blo 896573 1348955 := bstep (se 1 (by rfl) ⟨1011716, by rfl⟩ : syracuseStep 1348955 = 2023433) B2023433
theorem B1349231 : Blo 896573 1349231 := bstep (se 1 (by rfl) ⟨1011923, by rfl⟩ : syracuseStep 1349231 = 2023847) B2023847
theorem B1513127 : Blo 896573 1513127 := bstep (se 1 (by rfl) ⟨1134845, by rfl⟩ : syracuseStep 1513127 = 2269691) B2269691
theorem B1349303 : Blo 896573 1349303 := bstep (se 1 (by rfl) ⟨1011977, by rfl⟩ : syracuseStep 1349303 = 2023955) B2023955
theorem B1349339 : Blo 896573 1349339 := bstep (se 1 (by rfl) ⟨1012004, by rfl⟩ : syracuseStep 1349339 = 2024009) B2024009
theorem B3413771 : Blo 896573 3413771 := bstep (se 1 (by rfl) ⟨2560328, by rfl⟩ : syracuseStep 3413771 = 5120657) B5120657
theorem B1349513 : Blo 896573 1349513 := bstep (se 2 (by rfl) ⟨506067, by rfl⟩ : syracuseStep 1349513 = 1012135) B1012135
theorem B1349615 : Blo 896573 1349615 := bstep (se 1 (by rfl) ⟨1012211, by rfl⟩ : syracuseStep 1349615 = 2024423) B2024423
theorem B1349867 : Blo 896573 1349867 := bstep (se 1 (by rfl) ⟨1012400, by rfl⟩ : syracuseStep 1349867 = 2024801) B2024801
theorem B1349927 : Blo 896573 1349927 := bstep (se 1 (by rfl) ⟨1012445, by rfl⟩ : syracuseStep 1349927 = 2024891) B2024891
theorem B1513775 : Blo 896573 1513775 := bstep (se 1 (by rfl) ⟨1135331, by rfl⟩ : syracuseStep 1513775 = 2270663) B2270663
theorem B1350011 : Blo 896573 1350011 := bstep (se 1 (by rfl) ⟨1012508, by rfl⟩ : syracuseStep 1350011 = 2025017) B2025017
theorem B1514011 : Blo 896573 1514011 := bstep (se 1 (by rfl) ⟨1135508, by rfl⟩ : syracuseStep 1514011 = 2271017) B2271017
theorem B2562617 : Blo 896573 2562617 := bstep (se 2 (by rfl) ⟨960981, by rfl⟩ : syracuseStep 2562617 = 1921963) B1921963
theorem B1350281 : Blo 896573 1350281 := bstep (se 2 (by rfl) ⟨506355, by rfl⟩ : syracuseStep 1350281 = 1012711) B1012711
theorem B1350455 : Blo 896573 1350455 := bstep (se 1 (by rfl) ⟨1012841, by rfl⟩ : syracuseStep 1350455 = 2025683) B2025683
theorem B3840851 : Blo 896573 3840851 := bstep (se 1 (by rfl) ⟨2880638, by rfl⟩ : syracuseStep 3840851 = 5761277) B5761277
theorem B1350491 : Blo 896573 1350491 := bstep (se 1 (by rfl) ⟨1012868, by rfl⟩ : syracuseStep 1350491 = 2025737) B2025737
theorem B2431903 : Blo 896573 2431903 := bstep (se 1 (by rfl) ⟨1823927, by rfl⟩ : syracuseStep 2431903 = 3647855) B3647855
theorem B1350635 : Blo 896573 1350635 := bstep (se 1 (by rfl) ⟨1012976, by rfl⟩ : syracuseStep 1350635 = 2025953) B2025953
theorem B3415031 : Blo 896573 3415031 := bstep (se 1 (by rfl) ⟨2561273, by rfl⟩ : syracuseStep 3415031 = 5122547) B5122547
theorem B10230785 : Blo 896573 10230785 := bstep (se 2 (by rfl) ⟨3836544, by rfl⟩ : syracuseStep 10230785 = 7673089) B7673089
theorem B2563255 : Blo 896573 2563255 := bstep (se 1 (by rfl) ⟨1922441, by rfl⟩ : syracuseStep 2563255 = 3844883) B3844883
theorem B1350839 : Blo 896573 1350839 := bstep (se 1 (by rfl) ⟨1013129, by rfl⟩ : syracuseStep 1350839 = 2026259) B2026259
theorem B1514983 : Blo 896573 1514983 := bstep (se 1 (by rfl) ⟨1136237, by rfl⟩ : syracuseStep 1514983 = 2272475) B2272475
theorem B1515071 : Blo 896573 1515071 := bstep (se 1 (by rfl) ⟨1136303, by rfl⟩ : syracuseStep 1515071 = 2272607) B2272607
theorem B2334433 : Blo 896573 2334433 := bstep (se 2 (by rfl) ⟨875412, by rfl⟩ : syracuseStep 2334433 = 1750825) B1750825
theorem B1515739 : Blo 896573 1515739 := bstep (se 1 (by rfl) ⟨1136804, by rfl⟩ : syracuseStep 1515739 = 2273609) B2273609
theorem B15343991 : Blo 896573 15343991 := bstep (se 1 (by rfl) ⟨11507993, by rfl⟩ : syracuseStep 15343991 = 23015987) B23015987
theorem B3842423 : Blo 896573 3842423 := bstep (se 1 (by rfl) ⟨2881817, by rfl⟩ : syracuseStep 3842423 = 5763635) B5763635
theorem B3842491 : Blo 896573 3842491 := bstep (se 1 (by rfl) ⟨2881868, by rfl⟩ : syracuseStep 3842491 = 5763737) B5763737
theorem B1516009 : Blo 896573 1516009 := bstep (se 2 (by rfl) ⟨568503, by rfl⟩ : syracuseStep 1516009 = 1137007) B1137007
theorem B1581935 : Blo 896573 1581935 := bstep (se 1 (by rfl) ⟨1186451, by rfl⟩ : syracuseStep 1581935 = 2372903) B2372903
theorem B12952493 : Blo 896573 12952493 := bstep (se 3 (by rfl) ⟨2428592, by rfl⟩ : syracuseStep 12952493 = 4857185) B4857185
theorem B4859087 : Blo 896573 4859087 := bstep (se 1 (by rfl) ⟨3644315, by rfl⟩ : syracuseStep 4859087 = 7288631) B7288631
theorem B6563321 : Blo 896573 6563321 := bstep (se 2 (by rfl) ⟨2461245, by rfl⟩ : syracuseStep 6563321 = 4922491) B4922491
theorem B1517177 : Blo 896573 1517177 := bstep (se 2 (by rfl) ⟨568941, by rfl⟩ : syracuseStep 1517177 = 1137883) B1137883
theorem B4859651 : Blo 896573 4859651 := bstep (se 1 (by rfl) ⟨3644738, by rfl⟩ : syracuseStep 4859651 = 7289477) B7289477
theorem B4105991 : Blo 896573 4105991 := bstep (se 1 (by rfl) ⟨3079493, by rfl⟩ : syracuseStep 4105991 = 6158987) B6158987
theorem B1517663 : Blo 896573 1517663 := bstep (se 1 (by rfl) ⟨1138247, by rfl⟩ : syracuseStep 1517663 = 2276495) B2276495
theorem B3418463 : Blo 896573 3418463 := bstep (se 1 (by rfl) ⟨2563847, by rfl⟩ : syracuseStep 3418463 = 5127695) B5127695
theorem B16427447 : Blo 896573 16427447 := bstep (se 1 (by rfl) ⟨12320585, by rfl⟩ : syracuseStep 16427447 = 24641171) B24641171
theorem B1092655 : Blo 896573 1092655 := bstep (se 1 (by rfl) ⟨819491, by rfl⟩ : syracuseStep 1092655 = 1638983) B1638983
theorem B1518959 : Blo 896573 1518959 := bstep (se 1 (by rfl) ⟨1139219, by rfl⟩ : syracuseStep 1518959 = 2278439) B2278439
theorem B896603 : Blo 896573 896603 := bstep (se 1 (by rfl) ⟨672452, by rfl⟩ : syracuseStep 896603 = 1344905) B1344905
theorem B1519195 : Blo 896573 1519195 := bstep (se 1 (by rfl) ⟨1139396, by rfl⟩ : syracuseStep 1519195 = 2278793) B2278793
theorem B1519337 : Blo 896573 1519337 := bstep (se 2 (by rfl) ⟨569751, by rfl⟩ : syracuseStep 1519337 = 1139503) B1139503
theorem B896839 : Blo 896573 896839 := bstep (se 1 (by rfl) ⟨672629, by rfl⟩ : syracuseStep 896839 = 1345259) B1345259
theorem B896991 : Blo 896573 896991 := bstep (se 1 (by rfl) ⟨672743, by rfl⟩ : syracuseStep 896991 = 1345487) B1345487
theorem B3027131 : Blo 896573 3027131 := bstep (se 1 (by rfl) ⟨2270348, by rfl⟩ : syracuseStep 3027131 = 4540697) B4540697
theorem B2273467 : Blo 896573 2273467 := bstep (se 1 (by rfl) ⟨1705100, by rfl⟩ : syracuseStep 2273467 = 3410201) B3410201
theorem B897255 : Blo 896573 897255 := bstep (se 1 (by rfl) ⟨672941, by rfl⟩ : syracuseStep 897255 = 1345883) B1345883
theorem B897407 : Blo 896573 897407 := bstep (se 1 (by rfl) ⟨673055, by rfl⟩ : syracuseStep 897407 = 1346111) B1346111
theorem B897487 : Blo 896573 897487 := bstep (se 1 (by rfl) ⟨673115, by rfl⟩ : syracuseStep 897487 = 1346231) B1346231
theorem B7188965 : Blo 896573 7188965 := bstep (se 4 (by rfl) ⟨673965, by rfl⟩ : syracuseStep 7188965 = 1347931) B1347931
theorem B897639 : Blo 896573 897639 := bstep (se 1 (by rfl) ⟨673229, by rfl⟩ : syracuseStep 897639 = 1346459) B1346459
theorem B3027617 : Blo 896573 3027617 := bstep (se 2 (by rfl) ⟨1135356, by rfl⟩ : syracuseStep 3027617 = 2270713) B2270713
theorem B2273953 : Blo 896573 2273953 := bstep (se 2 (by rfl) ⟨852732, by rfl⟩ : syracuseStep 2273953 = 1705465) B1705465
theorem B5124779 : Blo 896573 5124779 := bstep (se 1 (by rfl) ⟨3843584, by rfl⟩ : syracuseStep 5124779 = 7687169) B7687169
theorem B897903 : Blo 896573 897903 := bstep (se 1 (by rfl) ⟨673427, by rfl⟩ : syracuseStep 897903 = 1346855) B1346855
theorem B897959 : Blo 896573 897959 := bstep (se 1 (by rfl) ⟨673469, by rfl⟩ : syracuseStep 897959 = 1346939) B1346939
theorem B898043 : Blo 896573 898043 := bstep (se 1 (by rfl) ⟨673532, by rfl⟩ : syracuseStep 898043 = 1347065) B1347065
theorem B898111 : Blo 896573 898111 := bstep (se 1 (by rfl) ⟨673583, by rfl⟩ : syracuseStep 898111 = 1347167) B1347167
theorem B5911667 : Blo 896573 5911667 := bstep (se 1 (by rfl) ⟨4433750, by rfl⟩ : syracuseStep 5911667 = 8867501) B8867501
theorem B898255 : Blo 896573 898255 := bstep (se 1 (by rfl) ⟨673691, by rfl⟩ : syracuseStep 898255 = 1347383) B1347383
theorem B5748029 : Blo 896573 5748029 := bstep (se 3 (by rfl) ⟨1077755, by rfl⟩ : syracuseStep 5748029 = 2155511) B2155511
theorem B23311721 : Blo 896573 23311721 := bstep (se 2 (by rfl) ⟨8741895, by rfl⟩ : syracuseStep 23311721 = 17483791) B17483791
theorem B898459 : Blo 896573 898459 := bstep (se 1 (by rfl) ⟨673844, by rfl⟩ : syracuseStep 898459 = 1347689) B1347689
theorem B3028481 : Blo 896573 3028481 := bstep (se 2 (by rfl) ⟨1135680, by rfl⟩ : syracuseStep 3028481 = 2271361) B2271361
theorem B23377409 : Blo 896573 23377409 := bstep (se 2 (by rfl) ⟨8766528, by rfl⟩ : syracuseStep 23377409 = 17533057) B17533057
theorem B1521223 : Blo 896573 1521223 := bstep (se 1 (by rfl) ⟨1140917, by rfl⟩ : syracuseStep 1521223 = 2281835) B2281835
theorem B898671 : Blo 896573 898671 := bstep (se 1 (by rfl) ⟨674003, by rfl⟩ : syracuseStep 898671 = 1348007) B1348007
theorem B898727 : Blo 896573 898727 := bstep (se 1 (by rfl) ⟨674045, by rfl⟩ : syracuseStep 898727 = 1348091) B1348091
theorem B2275067 : Blo 896573 2275067 := bstep (se 1 (by rfl) ⟨1706300, by rfl⟩ : syracuseStep 2275067 = 3412601) B3412601
theorem B898811 : Blo 896573 898811 := bstep (se 1 (by rfl) ⟨674108, by rfl⟩ : syracuseStep 898811 = 1348217) B1348217
theorem B898847 : Blo 896573 898847 := bstep (se 1 (by rfl) ⟨674135, by rfl⟩ : syracuseStep 898847 = 1348271) B1348271
theorem B898879 : Blo 896573 898879 := bstep (se 1 (by rfl) ⟨674159, by rfl⟩ : syracuseStep 898879 = 1348319) B1348319
theorem B2307977 : Blo 896573 2307977 := bstep (se 2 (by rfl) ⟨865491, by rfl⟩ : syracuseStep 2307977 = 1730983) B1730983
theorem B3028967 : Blo 896573 3028967 := bstep (se 1 (by rfl) ⟨2271725, by rfl⟩ : syracuseStep 3028967 = 4543451) B4543451
theorem B899055 : Blo 896573 899055 := bstep (se 1 (by rfl) ⟨674291, by rfl⟩ : syracuseStep 899055 = 1348583) B1348583
theorem B3029075 : Blo 896573 3029075 := bstep (se 1 (by rfl) ⟨2271806, by rfl⟩ : syracuseStep 3029075 = 4543613) B4543613
theorem B2275411 : Blo 896573 2275411 := bstep (se 1 (by rfl) ⟨1706558, by rfl⟩ : syracuseStep 2275411 = 3413117) B3413117
theorem B899227 : Blo 896573 899227 := bstep (se 1 (by rfl) ⟨674420, by rfl⟩ : syracuseStep 899227 = 1348841) B1348841
theorem B899263 : Blo 896573 899263 := bstep (se 1 (by rfl) ⟨674447, by rfl⟩ : syracuseStep 899263 = 1348895) B1348895
theorem B11516195 : Blo 896573 11516195 := bstep (se 1 (by rfl) ⟨8637146, by rfl⟩ : syracuseStep 11516195 = 17274293) B17274293
theorem B3029291 : Blo 896573 3029291 := bstep (se 1 (by rfl) ⟨2271968, by rfl⟩ : syracuseStep 3029291 = 4543937) B4543937
theorem B899375 : Blo 896573 899375 := bstep (se 1 (by rfl) ⟨674531, by rfl⟩ : syracuseStep 899375 = 1349063) B1349063
theorem B5454191 : Blo 896573 5454191 := bstep (se 1 (by rfl) ⟨4090643, by rfl⟩ : syracuseStep 5454191 = 8181287) B8181287
theorem B899611 : Blo 896573 899611 := bstep (se 1 (by rfl) ⟨674708, by rfl⟩ : syracuseStep 899611 = 1349417) B1349417
theorem B899615 : Blo 896573 899615 := bstep (se 1 (by rfl) ⟨674711, by rfl⟩ : syracuseStep 899615 = 1349423) B1349423
theorem B3029561 : Blo 896573 3029561 := bstep (se 2 (by rfl) ⟨1136085, by rfl⟩ : syracuseStep 3029561 = 2272171) B2272171
theorem B2275897 : Blo 896573 2275897 := bstep (se 2 (by rfl) ⟨853461, by rfl⟩ : syracuseStep 2275897 = 1706923) B1706923
theorem B6470479 : Blo 896573 6470479 := bstep (se 1 (by rfl) ⟨4852859, by rfl⟩ : syracuseStep 6470479 = 9705719) B9705719
theorem B899931 : Blo 896573 899931 := bstep (se 1 (by rfl) ⟨674948, by rfl⟩ : syracuseStep 899931 = 1349897) B1349897
theorem B2276201 : Blo 896573 2276201 := bstep (se 2 (by rfl) ⟨853575, by rfl⟩ : syracuseStep 2276201 = 1707151) B1707151
theorem B899999 : Blo 896573 899999 := bstep (se 1 (by rfl) ⟨674999, by rfl⟩ : syracuseStep 899999 = 1349999) B1349999
theorem B900143 : Blo 896573 900143 := bstep (se 1 (by rfl) ⟨675107, by rfl⟩ : syracuseStep 900143 = 1350215) B1350215
theorem B900167 : Blo 896573 900167 := bstep (se 1 (by rfl) ⟨675125, by rfl⟩ : syracuseStep 900167 = 1350251) B1350251
theorem B5127239 : Blo 896573 5127239 := bstep (se 1 (by rfl) ⟨3845429, by rfl⟩ : syracuseStep 5127239 = 7690859) B7690859
theorem B900319 : Blo 896573 900319 := bstep (se 1 (by rfl) ⟨675239, by rfl⟩ : syracuseStep 900319 = 1350479) B1350479
theorem B6470941 : Blo 896573 6470941 := bstep (se 3 (by rfl) ⟨1213301, by rfl⟩ : syracuseStep 6470941 = 2426603) B2426603
theorem B2276819 : Blo 896573 2276819 := bstep (se 1 (by rfl) ⟨1707614, by rfl⟩ : syracuseStep 2276819 = 3415229) B3415229
theorem B10239533 : Blo 896573 10239533 := bstep (se 3 (by rfl) ⟨1919912, by rfl⟩ : syracuseStep 10239533 = 3839825) B3839825
theorem B8764973 : Blo 896573 8764973 := bstep (se 3 (by rfl) ⟨1643432, by rfl⟩ : syracuseStep 8764973 = 3286865) B3286865
theorem B17284751 : Blo 896573 17284751 := bstep (se 1 (by rfl) ⟨12963563, by rfl⟩ : syracuseStep 17284751 = 25927127) B25927127
theorem B1621729 : Blo 896573 1621729 := bstep (se 2 (by rfl) ⟨608148, by rfl⟩ : syracuseStep 1621729 = 1216297) B1216297
theorem B5127947 : Blo 896573 5127947 := bstep (se 1 (by rfl) ⟨3845960, by rfl⟩ : syracuseStep 5127947 = 7691921) B7691921
theorem B5750615 : Blo 896573 5750615 := bstep (se 1 (by rfl) ⟨4312961, by rfl⟩ : syracuseStep 5750615 = 8625923) B8625923
theorem B3031073 : Blo 896573 3031073 := bstep (se 2 (by rfl) ⟨1136652, by rfl⟩ : syracuseStep 3031073 = 2273305) B2273305
theorem B4309271 : Blo 896573 4309271 := bstep (se 1 (by rfl) ⟨3231953, by rfl⟩ : syracuseStep 4309271 = 6463907) B6463907
theorem B3686975 : Blo 896573 3686975 := bstep (se 1 (by rfl) ⟨2765231, by rfl⟩ : syracuseStep 3686975 = 5530463) B5530463
theorem B5128879 : Blo 896573 5128879 := bstep (se 1 (by rfl) ⟨3846659, by rfl⟩ : syracuseStep 5128879 = 7693319) B7693319
theorem B6144749 : Blo 896573 6144749 := bstep (se 3 (by rfl) ⟨1152140, by rfl⟩ : syracuseStep 6144749 = 2304281) B2304281
theorem B2048825 : Blo 896573 2048825 := bstep (se 2 (by rfl) ⟨768309, by rfl⟩ : syracuseStep 2048825 = 1536619) B1536619
theorem B5751719 : Blo 896573 5751719 := bstep (se 1 (by rfl) ⟨4313789, by rfl⟩ : syracuseStep 5751719 = 8627579) B8627579
theorem B2081747 : Blo 896573 2081747 := bstep (se 1 (by rfl) ⟨1561310, by rfl⟩ : syracuseStep 2081747 = 3122621) B3122621
theorem B2278763 : Blo 896573 2278763 := bstep (se 1 (by rfl) ⟨1709072, by rfl⟩ : syracuseStep 2278763 = 3418145) B3418145
theorem B2049455 : Blo 896573 2049455 := bstep (se 1 (by rfl) ⟨1537091, by rfl⟩ : syracuseStep 2049455 = 3074183) B3074183
theorem B24627077 : Blo 896573 24627077 := bstep (se 4 (by rfl) ⟨2308788, by rfl⟩ : syracuseStep 24627077 = 4617577) B4617577
theorem B5261363 : Blo 896573 5261363 := bstep (se 1 (by rfl) ⟨3946022, by rfl⟩ : syracuseStep 5261363 = 7892045) B7892045
theorem B2738387 : Blo 896573 2738387 := bstep (se 1 (by rfl) ⟨2053790, by rfl⟩ : syracuseStep 2738387 = 4107581) B4107581
theorem B2017529 : Blo 896573 2017529 := bstep (se 2 (by rfl) ⟨756573, by rfl⟩ : syracuseStep 2017529 = 1513147) B1513147
theorem B4606247 : Blo 896573 4606247 := bstep (se 1 (by rfl) ⟨3454685, by rfl⟩ : syracuseStep 4606247 = 6909371) B6909371
theorem B2017583 : Blo 896573 2017583 := bstep (se 1 (by rfl) ⟨1513187, by rfl⟩ : syracuseStep 2017583 = 3026375) B3026375
theorem B5196257 : Blo 896573 5196257 := bstep (se 2 (by rfl) ⟨1948596, by rfl⟩ : syracuseStep 5196257 = 3897193) B3897193
theorem B2017799 : Blo 896573 2017799 := bstep (se 1 (by rfl) ⟨1513349, by rfl⟩ : syracuseStep 2017799 = 3026699) B3026699
theorem B2017979 : Blo 896573 2017979 := bstep (se 1 (by rfl) ⟨1513484, by rfl⟩ : syracuseStep 2017979 = 3026969) B3026969
theorem B4541345 : Blo 896573 4541345 := bstep (se 2 (by rfl) ⟨1703004, by rfl⟩ : syracuseStep 4541345 = 3406009) B3406009
theorem B5754179 : Blo 896573 5754179 := bstep (se 1 (by rfl) ⟨4315634, by rfl⟩ : syracuseStep 5754179 = 8631269) B8631269
theorem B7687547 : Blo 896573 7687547 := bstep (se 1 (by rfl) ⟨5765660, by rfl⟩ : syracuseStep 7687547 = 11531321) B11531321
theorem B2018807 : Blo 896573 2018807 := bstep (se 1 (by rfl) ⟨1514105, by rfl⟩ : syracuseStep 2018807 = 3028211) B3028211
theorem B2018879 : Blo 896573 2018879 := bstep (se 1 (by rfl) ⟨1514159, by rfl⟩ : syracuseStep 2018879 = 3028319) B3028319
theorem B3034799 : Blo 896573 3034799 := bstep (se 1 (by rfl) ⟨2276099, by rfl⟩ : syracuseStep 3034799 = 4552199) B4552199
theorem B12472211 : Blo 896573 12472211 := bstep (se 1 (by rfl) ⟨9354158, by rfl⟩ : syracuseStep 12472211 = 18708317) B18708317
theorem B3035123 : Blo 896573 3035123 := bstep (se 1 (by rfl) ⟨2276342, by rfl⟩ : syracuseStep 3035123 = 4552685) B4552685
theorem B3035447 : Blo 896573 3035447 := bstep (se 1 (by rfl) ⟨2276585, by rfl⟩ : syracuseStep 3035447 = 4553171) B4553171
theorem B3461503 : Blo 896573 3461503 := bstep (se 1 (by rfl) ⟨2596127, by rfl⟩ : syracuseStep 3461503 = 5192255) B5192255
theorem B2019833 : Blo 896573 2019833 := bstep (se 2 (by rfl) ⟨757437, by rfl⟩ : syracuseStep 2019833 = 1514875) B1514875
theorem B3035663 : Blo 896573 3035663 := bstep (se 1 (by rfl) ⟨2276747, by rfl⟩ : syracuseStep 3035663 = 4553495) B4553495
theorem B2019923 : Blo 896573 2019923 := bstep (se 1 (by rfl) ⟨1514942, by rfl⟩ : syracuseStep 2019923 = 3029885) B3029885
theorem B1921639 : Blo 896573 1921639 := bstep (se 1 (by rfl) ⟨1441229, by rfl⟩ : syracuseStep 1921639 = 2882459) B2882459
theorem B11653793 : Blo 896573 11653793 := bstep (se 2 (by rfl) ⟨4370172, by rfl⟩ : syracuseStep 11653793 = 8740345) B8740345
theorem B2020103 : Blo 896573 2020103 := bstep (se 1 (by rfl) ⟨1515077, by rfl⟩ : syracuseStep 2020103 = 3030155) B3030155
theorem B18469883 : Blo 896573 18469883 := bstep (se 1 (by rfl) ⟨13852412, by rfl⟩ : syracuseStep 18469883 = 27704825) B27704825
theorem B4543775 : Blo 896573 4543775 := bstep (se 1 (by rfl) ⟨3407831, by rfl⟩ : syracuseStep 4543775 = 6815663) B6815663
theorem B3036743 : Blo 896573 3036743 := bstep (se 1 (by rfl) ⟨2277557, by rfl⟩ : syracuseStep 3036743 = 4555115) B4555115
theorem B5461613 : Blo 896573 5461613 := bstep (se 3 (by rfl) ⟨1024052, by rfl⟩ : syracuseStep 5461613 = 2048105) B2048105
theorem B2021183 : Blo 896573 2021183 := bstep (se 1 (by rfl) ⟨1515887, by rfl⟩ : syracuseStep 2021183 = 3031775) B3031775
theorem B2021471 : Blo 896573 2021471 := bstep (se 1 (by rfl) ⟨1516103, by rfl⟩ : syracuseStep 2021471 = 3032207) B3032207
theorem B8771827 : Blo 896573 8771827 := bstep (se 1 (by rfl) ⟨6578870, by rfl⟩ : syracuseStep 8771827 = 13157741) B13157741
theorem B3037715 : Blo 896573 3037715 := bstep (se 1 (by rfl) ⟨2278286, by rfl⟩ : syracuseStep 3037715 = 4556573) B4556573
theorem B1137179 : Blo 896573 1137179 := bstep (se 1 (by rfl) ⟨852884, by rfl⟩ : syracuseStep 1137179 = 1705769) B1705769
theorem B29547341 : Blo 896573 29547341 := bstep (se 3 (by rfl) ⟨5540126, by rfl⟩ : syracuseStep 29547341 = 11080253) B11080253
theorem B2022227 : Blo 896573 2022227 := bstep (se 1 (by rfl) ⟨1516670, by rfl⟩ : syracuseStep 2022227 = 3033341) B3033341
theorem B5758303 : Blo 896573 5758303 := bstep (se 1 (by rfl) ⟨4318727, by rfl⟩ : syracuseStep 5758303 = 8637455) B8637455
theorem B2022767 : Blo 896573 2022767 := bstep (se 1 (by rfl) ⟨1517075, by rfl⟩ : syracuseStep 2022767 = 3034151) B3034151
theorem B1138151 : Blo 896573 1138151 := bstep (se 1 (by rfl) ⟨853613, by rfl⟩ : syracuseStep 1138151 = 1707227) B1707227
theorem B2023055 : Blo 896573 2023055 := bstep (se 1 (by rfl) ⟨1517291, by rfl⟩ : syracuseStep 2023055 = 3034583) B3034583
theorem B2023145 : Blo 896573 2023145 := bstep (se 2 (by rfl) ⟨758679, by rfl⟩ : syracuseStep 2023145 = 1517359) B1517359
theorem B10379707 : Blo 896573 10379707 := bstep (se 1 (by rfl) ⟨7784780, by rfl⟩ : syracuseStep 10379707 = 15569561) B15569561
theorem B2024171 : Blo 896573 2024171 := bstep (se 1 (by rfl) ⟨1518128, by rfl⟩ : syracuseStep 2024171 = 3036257) B3036257
theorem B4547339 : Blo 896573 4547339 := bstep (se 1 (by rfl) ⟨3410504, by rfl⟩ : syracuseStep 4547339 = 6821009) B6821009
theorem B4547501 : Blo 896573 4547501 := bstep (se 3 (by rfl) ⟨852656, by rfl⟩ : syracuseStep 4547501 = 1705313) B1705313
theorem B16639451 : Blo 896573 16639451 := bstep (se 1 (by rfl) ⟨12479588, by rfl⟩ : syracuseStep 16639451 = 24959177) B24959177
theorem B2025071 : Blo 896573 2025071 := bstep (se 1 (by rfl) ⟨1518803, by rfl⟩ : syracuseStep 2025071 = 3037607) B3037607
theorem B2025179 : Blo 896573 2025179 := bstep (se 1 (by rfl) ⟨1518884, by rfl⟩ : syracuseStep 2025179 = 3037769) B3037769
theorem B1009471 : Blo 896573 1009471 := bstep (se 1 (by rfl) ⟨757103, by rfl⟩ : syracuseStep 1009471 = 1514207) B1514207
theorem B1009759 : Blo 896573 1009759 := bstep (se 1 (by rfl) ⟨757319, by rfl⟩ : syracuseStep 1009759 = 1514639) B1514639
theorem B2877743 : Blo 896573 2877743 := bstep (se 1 (by rfl) ⟨2158307, by rfl⟩ : syracuseStep 2877743 = 4316615) B4316615
theorem B4548959 : Blo 896573 4548959 := bstep (se 1 (by rfl) ⟨3411719, by rfl⟩ : syracuseStep 4548959 = 6823439) B6823439
theorem B6482359 : Blo 896573 6482359 := bstep (se 1 (by rfl) ⟨4861769, by rfl⟩ : syracuseStep 6482359 = 9723539) B9723539
theorem B4549121 : Blo 896573 4549121 := bstep (se 2 (by rfl) ⟨1705920, by rfl⟩ : syracuseStep 4549121 = 3411841) B3411841
theorem B1436719 : Blo 896573 1436719 := bstep (se 1 (by rfl) ⟨1077539, by rfl⟩ : syracuseStep 1436719 = 2155079) B2155079
theorem B1010911 : Blo 896573 1010911 := bstep (se 1 (by rfl) ⟨758183, by rfl⟩ : syracuseStep 1010911 = 1516367) B1516367
theorem B4549931 : Blo 896573 4549931 := bstep (se 1 (by rfl) ⟨3412448, by rfl⟩ : syracuseStep 4549931 = 6824897) B6824897
theorem B77590385 : Blo 896573 77590385 := bstep (se 2 (by rfl) ⟨29096394, by rfl⟩ : syracuseStep 77590385 = 58192789) B58192789
theorem B1535915 : Blo 896573 1535915 := bstep (se 1 (by rfl) ⟨1151936, by rfl⟩ : syracuseStep 1535915 = 2303873) B2303873
theorem B20705267 : Blo 896573 20705267 := bstep (se 1 (by rfl) ⟨15528950, by rfl⟩ : syracuseStep 20705267 = 31057901) B31057901
theorem B1536311 : Blo 896573 1536311 := bstep (se 1 (by rfl) ⟨1152233, by rfl⟩ : syracuseStep 1536311 = 2304467) B2304467
theorem B2158903 : Blo 896573 2158903 := bstep (se 1 (by rfl) ⟨1619177, by rfl⟩ : syracuseStep 2158903 = 3238355) B3238355
theorem B26276183 : Blo 896573 26276183 := bstep (se 1 (by rfl) ⟨19707137, by rfl⟩ : syracuseStep 26276183 = 39414275) B39414275
theorem B2191865 : Blo 896573 2191865 := bstep (se 2 (by rfl) ⟨821949, by rfl⟩ : syracuseStep 2191865 = 1643899) B1643899
theorem B25915949 : Blo 896573 25915949 := bstep (se 3 (by rfl) ⟨4859240, by rfl⟩ : syracuseStep 25915949 = 9718481) B9718481
theorem B3404369 : Blo 896573 3404369 := bstep (se 2 (by rfl) ⟨1276638, by rfl⟩ : syracuseStep 3404369 = 2553277) B2553277
theorem B4551389 : Blo 896573 4551389 := bstep (se 3 (by rfl) ⟨853385, by rfl⟩ : syracuseStep 4551389 = 1706771) B1706771
theorem B3404551 : Blo 896573 3404551 := bstep (se 1 (by rfl) ⟨2553413, by rfl⟩ : syracuseStep 3404551 = 5106827) B5106827
theorem B5469569 : Blo 896573 5469569 := bstep (se 2 (by rfl) ⟨2051088, by rfl⟩ : syracuseStep 5469569 = 4102177) B4102177
theorem B6485447 : Blo 896573 6485447 := bstep (se 1 (by rfl) ⟨4864085, by rfl⟩ : syracuseStep 6485447 = 9728171) B9728171
theorem B10254113 : Blo 896573 10254113 := bstep (se 2 (by rfl) ⟨3845292, by rfl⟩ : syracuseStep 10254113 = 7690585) B7690585
theorem B4847759 : Blo 896573 4847759 := bstep (se 1 (by rfl) ⟨3635819, by rfl⟩ : syracuseStep 4847759 = 7271639) B7271639
theorem B4552847 : Blo 896573 4552847 := bstep (se 1 (by rfl) ⟨3414635, by rfl⟩ : syracuseStep 4552847 = 6829271) B6829271
theorem B3242911 : Blo 896573 3242911 := bstep (se 1 (by rfl) ⟨2432183, by rfl⟩ : syracuseStep 3242911 = 4864367) B4864367
theorem B3406799 : Blo 896573 3406799 := bstep (se 1 (by rfl) ⟨2555099, by rfl⟩ : syracuseStep 3406799 = 5110199) B5110199
theorem B6159311 : Blo 896573 6159311 := bstep (se 1 (by rfl) ⟨4619483, by rfl⟩ : syracuseStep 6159311 = 9238967) B9238967
theorem B1276975 : Blo 896573 1276975 := bstep (se 1 (by rfl) ⟨957731, by rfl⟩ : syracuseStep 1276975 = 1915463) B1915463
theorem B2555009 : Blo 896573 2555009 := bstep (se 2 (by rfl) ⟨958128, by rfl⟩ : syracuseStep 2555009 = 1916257) B1916257
theorem B6913309 : Blo 896573 6913309 := bstep (se 3 (by rfl) ⟨1296245, by rfl⟩ : syracuseStep 6913309 = 2592491) B2592491
theorem B12942803 : Blo 896573 12942803 := bstep (se 1 (by rfl) ⟨9707102, by rfl⟩ : syracuseStep 12942803 = 19414205) B19414205
theorem B1703567 : Blo 896573 1703567 := bstep (se 1 (by rfl) ⟨1277675, by rfl⟩ : syracuseStep 1703567 = 2555351) B2555351
theorem B3407741 : Blo 896573 3407741 := bstep (se 3 (by rfl) ⟨638951, by rfl⟩ : syracuseStep 3407741 = 1277903) B1277903
theorem B2457983 : Blo 896573 2457983 := bstep (se 1 (by rfl) ⟨1843487, by rfl⟩ : syracuseStep 2457983 = 3686975) B3686975
theorem B4096499 : Blo 896573 4096499 := bstep (se 1 (by rfl) ⟨3072374, by rfl⟩ : syracuseStep 4096499 = 6144749) B6144749
theorem B2884175 : Blo 896573 2884175 := bstep (se 1 (by rfl) ⟨2163131, by rfl⟩ : syracuseStep 2884175 = 4326263) B4326263
theorem B3834479 : Blo 896573 3834479 := bstep (se 1 (by rfl) ⟨2875859, by rfl⟩ : syracuseStep 3834479 = 5751719) B5751719
theorem B16418051 : Blo 896573 16418051 := bstep (se 1 (by rfl) ⟨12313538, by rfl⟩ : syracuseStep 16418051 = 24627077) B24627077
theorem B3409199 : Blo 896573 3409199 := bstep (se 1 (by rfl) ⟨2556899, by rfl⟩ : syracuseStep 3409199 = 5113799) B5113799
theorem B3507575 : Blo 896573 3507575 := bstep (se 1 (by rfl) ⟨2630681, by rfl⟩ : syracuseStep 3507575 = 5261363) B5261363
theorem B17237387 : Blo 896573 17237387 := bstep (se 1 (by rfl) ⟨12928040, by rfl⟩ : syracuseStep 17237387 = 25856081) B25856081
theorem B1345019 : Blo 896573 1345019 := bstep (se 1 (by rfl) ⟨1008764, by rfl⟩ : syracuseStep 1345019 = 2017529) B2017529
theorem B1345055 : Blo 896573 1345055 := bstep (se 1 (by rfl) ⟨1008791, by rfl⟩ : syracuseStep 1345055 = 2017583) B2017583
theorem B1345199 : Blo 896573 1345199 := bstep (se 1 (by rfl) ⟨1008899, by rfl⟩ : syracuseStep 1345199 = 2017799) B2017799
theorem B1345319 : Blo 896573 1345319 := bstep (se 1 (by rfl) ⟨1008989, by rfl⟩ : syracuseStep 1345319 = 2017979) B2017979
theorem B3836119 : Blo 896573 3836119 := bstep (se 1 (by rfl) ⟨2877089, by rfl⟩ : syracuseStep 3836119 = 5754179) B5754179
theorem B1345871 : Blo 896573 1345871 := bstep (se 1 (by rfl) ⟨1009403, by rfl⟩ : syracuseStep 1345871 = 2018807) B2018807
theorem B1345919 : Blo 896573 1345919 := bstep (se 1 (by rfl) ⟨1009439, by rfl⟩ : syracuseStep 1345919 = 2018879) B2018879
theorem B1345961 : Blo 896573 1345961 := bstep (se 2 (by rfl) ⟨504735, by rfl⟩ : syracuseStep 1345961 = 1009471) B1009471
theorem B1346345 : Blo 896573 1346345 := bstep (se 2 (by rfl) ⟨504879, by rfl⟩ : syracuseStep 1346345 = 1009759) B1009759
theorem B1346555 : Blo 896573 1346555 := bstep (se 1 (by rfl) ⟨1009916, by rfl⟩ : syracuseStep 1346555 = 2019833) B2019833
theorem B1346615 : Blo 896573 1346615 := bstep (se 1 (by rfl) ⟨1009961, by rfl⟩ : syracuseStep 1346615 = 2019923) B2019923
theorem B7769195 : Blo 896573 7769195 := bstep (se 1 (by rfl) ⟨5826896, by rfl⟩ : syracuseStep 7769195 = 11653793) B11653793
theorem B1346735 : Blo 896573 1346735 := bstep (se 1 (by rfl) ⟨1010051, by rfl⟩ : syracuseStep 1346735 = 2020103) B2020103
theorem B17239391 : Blo 896573 17239391 := bstep (se 1 (by rfl) ⟨12929543, by rfl⟩ : syracuseStep 17239391 = 25859087) B25859087
theorem B3641075 : Blo 896573 3641075 := bstep (se 1 (by rfl) ⟨2730806, by rfl⟩ : syracuseStep 3641075 = 5461613) B5461613
theorem B1347455 : Blo 896573 1347455 := bstep (se 1 (by rfl) ⟨1010591, by rfl⟩ : syracuseStep 1347455 = 2021183) B2021183
theorem B1347647 : Blo 896573 1347647 := bstep (se 1 (by rfl) ⟨1010735, by rfl⟩ : syracuseStep 1347647 = 2021471) B2021471
theorem B1347881 : Blo 896573 1347881 := bstep (se 2 (by rfl) ⟨505455, by rfl⟩ : syracuseStep 1347881 = 1010911) B1010911
theorem B19698227 : Blo 896573 19698227 := bstep (se 1 (by rfl) ⟨14773670, by rfl⟩ : syracuseStep 19698227 = 29547341) B29547341
theorem B1348151 : Blo 896573 1348151 := bstep (se 1 (by rfl) ⟨1011113, by rfl⟩ : syracuseStep 1348151 = 2022227) B2022227
theorem B2560567 : Blo 896573 2560567 := bstep (se 1 (by rfl) ⟨1920425, by rfl⟩ : syracuseStep 2560567 = 3840851) B3840851
theorem B6820523 : Blo 896573 6820523 := bstep (se 1 (by rfl) ⟨5115392, by rfl⟩ : syracuseStep 6820523 = 10230785) B10230785
theorem B1348511 : Blo 896573 1348511 := bstep (se 1 (by rfl) ⟨1011383, by rfl⟩ : syracuseStep 1348511 = 2022767) B2022767
theorem B1348703 : Blo 896573 1348703 := bstep (se 1 (by rfl) ⟨1011527, by rfl⟩ : syracuseStep 1348703 = 2023055) B2023055
theorem B1348763 : Blo 896573 1348763 := bstep (se 1 (by rfl) ⟨1011572, by rfl⟩ : syracuseStep 1348763 = 2023145) B2023145
theorem B1709353 : Blo 896573 1709353 := bstep (se 2 (by rfl) ⟨641007, by rfl⟩ : syracuseStep 1709353 = 1282015) B1282015
theorem B2561615 : Blo 896573 2561615 := bstep (se 1 (by rfl) ⟨1921211, by rfl⟩ : syracuseStep 2561615 = 3842423) B3842423
theorem B10229327 : Blo 896573 10229327 := bstep (se 1 (by rfl) ⟨7671995, by rfl⟩ : syracuseStep 10229327 = 15343991) B15343991
theorem B1349447 : Blo 896573 1349447 := bstep (se 1 (by rfl) ⟨1012085, by rfl⟩ : syracuseStep 1349447 = 2024171) B2024171
theorem B2562185 : Blo 896573 2562185 := bstep (se 2 (by rfl) ⟨960819, by rfl⟩ : syracuseStep 2562185 = 1921639) B1921639
theorem B1350047 : Blo 896573 1350047 := bstep (se 1 (by rfl) ⟨1012535, by rfl⟩ : syracuseStep 1350047 = 2025071) B2025071
theorem B1350119 : Blo 896573 1350119 := bstep (se 1 (by rfl) ⟨1012589, by rfl⟩ : syracuseStep 1350119 = 2025179) B2025179
theorem B10951631 : Blo 896573 10951631 := bstep (se 1 (by rfl) ⟨8213723, by rfl⟩ : syracuseStep 10951631 = 16427447) B16427447
theorem B6822953 : Blo 896573 6822953 := bstep (se 2 (by rfl) ⟨2558607, by rfl⟩ : syracuseStep 6822953 = 5117215) B5117215
theorem B1023943 : Blo 896573 1023943 := bstep (se 1 (by rfl) ⟨767957, by rfl⟩ : syracuseStep 1023943 = 1535915) B1535915
theorem B1024207 : Blo 896573 1024207 := bstep (se 1 (by rfl) ⟨768155, by rfl⟩ : syracuseStep 1024207 = 1536311) B1536311
theorem B4792643 : Blo 896573 4792643 := bstep (se 1 (by rfl) ⟨3594482, by rfl⟩ : syracuseStep 4792643 = 7188965) B7188965
theorem B17277299 : Blo 896573 17277299 := bstep (se 1 (by rfl) ⟨12957974, by rfl⟩ : syracuseStep 17277299 = 25915949) B25915949
theorem B2269579 : Blo 896573 2269579 := bstep (se 1 (by rfl) ⟨1702184, by rfl⟩ : syracuseStep 2269579 = 3404369) B3404369
theorem B3416519 : Blo 896573 3416519 := bstep (se 1 (by rfl) ⟨2562389, by rfl⟩ : syracuseStep 3416519 = 5124779) B5124779
theorem B3941111 : Blo 896573 3941111 := bstep (se 1 (by rfl) ⟨2955833, by rfl⟩ : syracuseStep 3941111 = 5911667) B5911667
theorem B15541147 : Blo 896573 15541147 := bstep (se 1 (by rfl) ⟨11655860, by rfl⟩ : syracuseStep 15541147 = 23311721) B23311721
theorem B3646379 : Blo 896573 3646379 := bstep (se 1 (by rfl) ⟨2734784, by rfl⟩ : syracuseStep 3646379 = 5469569) B5469569
theorem B8627305 : Blo 896573 8627305 := bstep (se 2 (by rfl) ⟨3235239, by rfl⟩ : syracuseStep 8627305 = 6470479) B6470479
theorem B1516711 : Blo 896573 1516711 := bstep (se 1 (by rfl) ⟨1137533, by rfl⟩ : syracuseStep 1516711 = 2275067) B2275067
theorem B7677463 : Blo 896573 7677463 := bstep (se 1 (by rfl) ⟨5758097, by rfl⟩ : syracuseStep 7677463 = 11516195) B11516195
theorem B3417673 : Blo 896573 3417673 := bstep (se 2 (by rfl) ⟨1281627, by rfl⟩ : syracuseStep 3417673 = 2563255) B2563255
theorem B8627921 : Blo 896573 8627921 := bstep (se 2 (by rfl) ⟨3235470, by rfl⟩ : syracuseStep 8627921 = 6470941) B6470941
theorem B9217745 : Blo 896573 9217745 := bstep (se 2 (by rfl) ⟨3456654, by rfl⟩ : syracuseStep 9217745 = 6913309) B6913309
theorem B7677737 : Blo 896573 7677737 := bstep (se 2 (by rfl) ⟨2879151, by rfl⟩ : syracuseStep 7677737 = 5758303) B5758303
theorem B1517467 : Blo 896573 1517467 := bstep (se 1 (by rfl) ⟨1138100, by rfl⟩ : syracuseStep 1517467 = 2276201) B2276201
theorem B2271199 : Blo 896573 2271199 := bstep (se 1 (by rfl) ⟨1703399, by rfl⟩ : syracuseStep 2271199 = 3406799) B3406799
theorem B4106207 : Blo 896573 4106207 := bstep (se 1 (by rfl) ⟨3079655, by rfl⟩ : syracuseStep 4106207 = 6159311) B6159311
theorem B3418159 : Blo 896573 3418159 := bstep (se 1 (by rfl) ⟨2563619, by rfl⟩ : syracuseStep 3418159 = 5127239) B5127239
theorem B8628535 : Blo 896573 8628535 := bstep (se 1 (by rfl) ⟨6471401, by rfl⟩ : syracuseStep 8628535 = 12942803) B12942803
theorem B1517879 : Blo 896573 1517879 := bstep (se 1 (by rfl) ⟨1138409, by rfl⟩ : syracuseStep 1517879 = 2276819) B2276819
theorem B6826355 : Blo 896573 6826355 := bstep (se 1 (by rfl) ⟨5119766, by rfl⟩ : syracuseStep 6826355 = 10239533) B10239533
theorem B5843315 : Blo 896573 5843315 := bstep (se 1 (by rfl) ⟨4382486, by rfl⟩ : syracuseStep 5843315 = 8764973) B8764973
theorem B3418631 : Blo 896573 3418631 := bstep (se 1 (by rfl) ⟨2563973, by rfl⟩ : syracuseStep 3418631 = 5127947) B5127947
theorem B2271827 : Blo 896573 2271827 := bstep (se 1 (by rfl) ⟨1703870, by rfl⟩ : syracuseStep 2271827 = 3407741) B3407741
theorem B3845191 : Blo 896573 3845191 := bstep (se 1 (by rfl) ⟨2883893, by rfl⟩ : syracuseStep 3845191 = 5767787) B5767787
theorem B5123321 : Blo 896573 5123321 := bstep (se 2 (by rfl) ⟨1921245, by rfl⟩ : syracuseStep 5123321 = 3842491) B3842491
theorem B1519175 : Blo 896573 1519175 := bstep (se 1 (by rfl) ⟨1139381, by rfl⟩ : syracuseStep 1519175 = 2278763) B2278763
theorem B896615 : Blo 896573 896615 := bstep (se 1 (by rfl) ⟨672461, by rfl⟩ : syracuseStep 896615 = 1344923) B1344923
theorem B896763 : Blo 896573 896763 := bstep (se 1 (by rfl) ⟨672572, by rfl⟩ : syracuseStep 896763 = 1345145) B1345145
theorem B896831 : Blo 896573 896831 := bstep (se 1 (by rfl) ⟨672623, by rfl⟩ : syracuseStep 896831 = 1345247) B1345247
theorem B896895 : Blo 896573 896895 := bstep (se 1 (by rfl) ⟨672671, by rfl⟩ : syracuseStep 896895 = 1345343) B1345343
theorem B5844973 : Blo 896573 5844973 := bstep (se 3 (by rfl) ⟨1095932, by rfl⟩ : syracuseStep 5844973 = 2191865) B2191865
theorem B897007 : Blo 896573 897007 := bstep (se 1 (by rfl) ⟨672755, by rfl⟩ : syracuseStep 897007 = 1345511) B1345511
theorem B897019 : Blo 896573 897019 := bstep (se 1 (by rfl) ⟨672764, by rfl⟩ : syracuseStep 897019 = 1345529) B1345529
theorem B897087 : Blo 896573 897087 := bstep (se 1 (by rfl) ⟨672815, by rfl⟩ : syracuseStep 897087 = 1345631) B1345631
theorem B897127 : Blo 896573 897127 := bstep (se 1 (by rfl) ⟨672845, by rfl⟩ : syracuseStep 897127 = 1345691) B1345691
theorem B897151 : Blo 896573 897151 := bstep (se 1 (by rfl) ⟨672863, by rfl⟩ : syracuseStep 897151 = 1345727) B1345727
theorem B32452757 : Blo 896573 32452757 := bstep (se 6 (by rfl) ⟨760611, by rfl⟩ : syracuseStep 32452757 = 1521223) B1521223
theorem B897179 : Blo 896573 897179 := bstep (se 1 (by rfl) ⟨672884, by rfl⟩ : syracuseStep 897179 = 1345769) B1345769
theorem B897383 : Blo 896573 897383 := bstep (se 1 (by rfl) ⟨673037, by rfl⟩ : syracuseStep 897383 = 1346075) B1346075
theorem B897435 : Blo 896573 897435 := bstep (se 1 (by rfl) ⟨673076, by rfl⟩ : syracuseStep 897435 = 1346153) B1346153
theorem B3027563 : Blo 896573 3027563 := bstep (se 1 (by rfl) ⟨2270672, by rfl⟩ : syracuseStep 3027563 = 4541345) B4541345
theorem B897787 : Blo 896573 897787 := bstep (se 1 (by rfl) ⟨673340, by rfl⟩ : syracuseStep 897787 = 1346681) B1346681
theorem B2274095 : Blo 896573 2274095 := bstep (se 1 (by rfl) ⟨1705571, by rfl⟩ : syracuseStep 2274095 = 3411143) B3411143
theorem B897855 : Blo 896573 897855 := bstep (se 1 (by rfl) ⟨673391, by rfl⟩ : syracuseStep 897855 = 1346783) B1346783
theorem B897883 : Blo 896573 897883 := bstep (se 1 (by rfl) ⟨673412, by rfl⟩ : syracuseStep 897883 = 1346825) B1346825
theorem B897951 : Blo 896573 897951 := bstep (se 1 (by rfl) ⟨673463, by rfl⟩ : syracuseStep 897951 = 1346927) B1346927
theorem B5125031 : Blo 896573 5125031 := bstep (se 1 (by rfl) ⟨3843773, by rfl⟩ : syracuseStep 5125031 = 7687547) B7687547
theorem B55358437 : Blo 896573 55358437 := bstep (se 4 (by rfl) ⟨5189853, by rfl⟩ : syracuseStep 55358437 = 10379707) B10379707
theorem B898031 : Blo 896573 898031 := bstep (se 1 (by rfl) ⟨673523, by rfl⟩ : syracuseStep 898031 = 1347047) B1347047
theorem B3453961 : Blo 896573 3453961 := bstep (se 2 (by rfl) ⟨1295235, by rfl⟩ : syracuseStep 3453961 = 2590471) B2590471
theorem B898119 : Blo 896573 898119 := bstep (se 1 (by rfl) ⟨673589, by rfl⟩ : syracuseStep 898119 = 1347179) B1347179
theorem B898203 : Blo 896573 898203 := bstep (se 1 (by rfl) ⟨673652, by rfl⟩ : syracuseStep 898203 = 1347305) B1347305
theorem B5551325 : Blo 896573 5551325 := bstep (se 3 (by rfl) ⟨1040873, by rfl⟩ : syracuseStep 5551325 = 2081747) B2081747
theorem B898299 : Blo 896573 898299 := bstep (se 1 (by rfl) ⟨673724, by rfl⟩ : syracuseStep 898299 = 1347449) B1347449
theorem B898367 : Blo 896573 898367 := bstep (se 1 (by rfl) ⟨673775, by rfl⟩ : syracuseStep 898367 = 1347551) B1347551
theorem B5748155 : Blo 896573 5748155 := bstep (se 1 (by rfl) ⟨4311116, by rfl⟩ : syracuseStep 5748155 = 8622233) B8622233
theorem B898535 : Blo 896573 898535 := bstep (se 1 (by rfl) ⟨673901, by rfl⟩ : syracuseStep 898535 = 1347803) B1347803
theorem B898543 : Blo 896573 898543 := bstep (se 1 (by rfl) ⟨673907, by rfl⟩ : syracuseStep 898543 = 1347815) B1347815
theorem B898651 : Blo 896573 898651 := bstep (se 1 (by rfl) ⟨673988, by rfl⟩ : syracuseStep 898651 = 1347977) B1347977
theorem B898715 : Blo 896573 898715 := bstep (se 1 (by rfl) ⟨674036, by rfl⟩ : syracuseStep 898715 = 1348073) B1348073
theorem B898799 : Blo 896573 898799 := bstep (se 1 (by rfl) ⟨674099, by rfl⟩ : syracuseStep 898799 = 1348199) B1348199
theorem B898887 : Blo 896573 898887 := bstep (se 1 (by rfl) ⟨674165, by rfl⟩ : syracuseStep 898887 = 1348331) B1348331
theorem B898907 : Blo 896573 898907 := bstep (se 1 (by rfl) ⟨674180, by rfl⟩ : syracuseStep 898907 = 1348361) B1348361
theorem B12957565 : Blo 896573 12957565 := bstep (se 3 (by rfl) ⟨2429543, by rfl⟩ : syracuseStep 12957565 = 4859087) B4859087
theorem B898975 : Blo 896573 898975 := bstep (se 1 (by rfl) ⟨674231, by rfl⟩ : syracuseStep 898975 = 1348463) B1348463
theorem B899143 : Blo 896573 899143 := bstep (se 1 (by rfl) ⟨674357, by rfl⟩ : syracuseStep 899143 = 1348715) B1348715
theorem B3029183 : Blo 896573 3029183 := bstep (se 1 (by rfl) ⟨2271887, by rfl⟩ : syracuseStep 3029183 = 4543775) B4543775
theorem B899303 : Blo 896573 899303 := bstep (se 1 (by rfl) ⟨674477, by rfl⟩ : syracuseStep 899303 = 1348955) B1348955
theorem B899487 : Blo 896573 899487 := bstep (se 1 (by rfl) ⟨674615, by rfl⟩ : syracuseStep 899487 = 1349231) B1349231
theorem B899535 : Blo 896573 899535 := bstep (se 1 (by rfl) ⟨674651, by rfl⟩ : syracuseStep 899535 = 1349303) B1349303
theorem B899559 : Blo 896573 899559 := bstep (se 1 (by rfl) ⟨674669, by rfl⟩ : syracuseStep 899559 = 1349339) B1349339
theorem B2275847 : Blo 896573 2275847 := bstep (se 1 (by rfl) ⟨1706885, by rfl⟩ : syracuseStep 2275847 = 3413771) B3413771
theorem B899675 : Blo 896573 899675 := bstep (se 1 (by rfl) ⟨674756, by rfl⟩ : syracuseStep 899675 = 1349513) B1349513
theorem B899743 : Blo 896573 899743 := bstep (se 1 (by rfl) ⟨674807, by rfl⟩ : syracuseStep 899743 = 1349615) B1349615
theorem B1915625 : Blo 896573 1915625 := bstep (se 2 (by rfl) ⟨718359, by rfl⟩ : syracuseStep 1915625 = 1436719) B1436719
theorem B899911 : Blo 896573 899911 := bstep (se 1 (by rfl) ⟨674933, by rfl⟩ : syracuseStep 899911 = 1349867) B1349867
theorem B899951 : Blo 896573 899951 := bstep (se 1 (by rfl) ⟨674963, by rfl⟩ : syracuseStep 899951 = 1349927) B1349927
theorem B900007 : Blo 896573 900007 := bstep (se 1 (by rfl) ⟨675005, by rfl⟩ : syracuseStep 900007 = 1350011) B1350011
theorem B900187 : Blo 896573 900187 := bstep (se 1 (by rfl) ⟨675140, by rfl⟩ : syracuseStep 900187 = 1350281) B1350281
theorem B900303 : Blo 896573 900303 := bstep (se 1 (by rfl) ⟨675227, by rfl⟩ : syracuseStep 900303 = 1350455) B1350455
theorem B900327 : Blo 896573 900327 := bstep (se 1 (by rfl) ⟨675245, by rfl⟩ : syracuseStep 900327 = 1350491) B1350491
theorem B900423 : Blo 896573 900423 := bstep (se 1 (by rfl) ⟨675317, by rfl⟩ : syracuseStep 900423 = 1350635) B1350635
theorem B2276687 : Blo 896573 2276687 := bstep (se 1 (by rfl) ⟨1707515, by rfl⟩ : syracuseStep 2276687 = 3415031) B3415031
theorem B900559 : Blo 896573 900559 := bstep (se 1 (by rfl) ⟨675419, by rfl⟩ : syracuseStep 900559 = 1350839) B1350839
theorem B3031289 : Blo 896573 3031289 := bstep (se 2 (by rfl) ⟨1136733, by rfl⟩ : syracuseStep 3031289 = 2273467) B2273467
theorem B3031559 : Blo 896573 3031559 := bstep (se 1 (by rfl) ⟨2273669, by rfl⟩ : syracuseStep 3031559 = 4547339) B4547339
theorem B3031667 : Blo 896573 3031667 := bstep (se 1 (by rfl) ⟨2273750, by rfl⟩ : syracuseStep 3031667 = 4547501) B4547501
theorem B8634995 : Blo 896573 8634995 := bstep (se 1 (by rfl) ⟨6476246, by rfl⟩ : syracuseStep 8634995 = 12952493) B12952493
theorem B3031937 : Blo 896573 3031937 := bstep (se 2 (by rfl) ⟨1136976, by rfl⟩ : syracuseStep 3031937 = 2273953) B2273953
theorem B11092967 : Blo 896573 11092967 := bstep (se 1 (by rfl) ⟨8319725, by rfl⟩ : syracuseStep 11092967 = 16639451) B16639451
theorem B4375547 : Blo 896573 4375547 := bstep (se 1 (by rfl) ⟨3281660, by rfl⟩ : syracuseStep 4375547 = 6563321) B6563321
theorem B4539401 : Blo 896573 4539401 := bstep (se 2 (by rfl) ⟨1702275, by rfl⟩ : syracuseStep 4539401 = 3404551) B3404551
theorem B2737327 : Blo 896573 2737327 := bstep (se 1 (by rfl) ⟨2052995, by rfl⟩ : syracuseStep 2737327 = 4105991) B4105991
theorem B3032477 : Blo 896573 3032477 := bstep (se 3 (by rfl) ⟨568589, by rfl⟩ : syracuseStep 3032477 = 1137179) B1137179
theorem B6833645 : Blo 896573 6833645 := bstep (se 3 (by rfl) ⟨1281308, by rfl⟩ : syracuseStep 6833645 = 2562617) B2562617
theorem B1918495 : Blo 896573 1918495 := bstep (se 1 (by rfl) ⟨1438871, by rfl⟩ : syracuseStep 1918495 = 2877743) B2877743
theorem B3032639 : Blo 896573 3032639 := bstep (se 1 (by rfl) ⟨2274479, by rfl⟩ : syracuseStep 3032639 = 4548959) B4548959
theorem B2278975 : Blo 896573 2278975 := bstep (se 1 (by rfl) ⟨1709231, by rfl⟩ : syracuseStep 2278975 = 3418463) B3418463
theorem B3032747 : Blo 896573 3032747 := bstep (se 1 (by rfl) ⟨2274560, by rfl⟩ : syracuseStep 3032747 = 4549121) B4549121
theorem B3033287 : Blo 896573 3033287 := bstep (se 1 (by rfl) ⟨2274965, by rfl⟩ : syracuseStep 3033287 = 4549931) B4549931
theorem B51726923 : Blo 896573 51726923 := bstep (se 1 (by rfl) ⟨38795192, by rfl⟩ : syracuseStep 51726923 = 77590385) B77590385
theorem B3033881 : Blo 896573 3033881 := bstep (se 2 (by rfl) ⟨1137705, by rfl⟩ : syracuseStep 3033881 = 2275411) B2275411
theorem B2018087 : Blo 896573 2018087 := bstep (se 1 (by rfl) ⟨1513565, by rfl⟩ : syracuseStep 2018087 = 3027131) B3027131
theorem B17517455 : Blo 896573 17517455 := bstep (se 1 (by rfl) ⟨13138091, by rfl⟩ : syracuseStep 17517455 = 26276183) B26276183
theorem B2018411 : Blo 896573 2018411 := bstep (se 1 (by rfl) ⟨1513808, by rfl⟩ : syracuseStep 2018411 = 3027617) B3027617
theorem B3034259 : Blo 896573 3034259 := bstep (se 1 (by rfl) ⟨2275694, by rfl⟩ : syracuseStep 3034259 = 4551389) B4551389
theorem B2018681 : Blo 896573 2018681 := bstep (se 2 (by rfl) ⟨757005, by rfl⟩ : syracuseStep 2018681 = 1514011) B1514011
theorem B3034529 : Blo 896573 3034529 := bstep (se 2 (by rfl) ⟨1137948, by rfl⟩ : syracuseStep 3034529 = 2275897) B2275897
theorem B2018987 : Blo 896573 2018987 := bstep (se 1 (by rfl) ⟨1514240, by rfl⟩ : syracuseStep 2018987 = 3028481) B3028481
theorem B15584939 : Blo 896573 15584939 := bstep (se 1 (by rfl) ⟨11688704, by rfl⟩ : syracuseStep 15584939 = 23377409) B23377409
theorem B6836075 : Blo 896573 6836075 := bstep (se 1 (by rfl) ⟨5127056, by rfl⟩ : syracuseStep 6836075 = 10254113) B10254113
theorem B3035069 : Blo 896573 3035069 := bstep (se 3 (by rfl) ⟨569075, by rfl⟩ : syracuseStep 3035069 = 1138151) B1138151
theorem B2019311 : Blo 896573 2019311 := bstep (se 1 (by rfl) ⟨1514483, by rfl⟩ : syracuseStep 2019311 = 3028967) B3028967
theorem B2019383 : Blo 896573 2019383 := bstep (se 1 (by rfl) ⟨1514537, by rfl⟩ : syracuseStep 2019383 = 3029075) B3029075
theorem B3231839 : Blo 896573 3231839 := bstep (se 1 (by rfl) ⟨2423879, by rfl⟩ : syracuseStep 3231839 = 4847759) B4847759
theorem B3035231 : Blo 896573 3035231 := bstep (se 1 (by rfl) ⟨2276423, by rfl⟩ : syracuseStep 3035231 = 4552847) B4552847
theorem B2019527 : Blo 896573 2019527 := bstep (se 1 (by rfl) ⟨1514645, by rfl⟩ : syracuseStep 2019527 = 3029291) B3029291
theorem B2019707 : Blo 896573 2019707 := bstep (se 1 (by rfl) ⟨1514780, by rfl⟩ : syracuseStep 2019707 = 3029561) B3029561
theorem B2019977 : Blo 896573 2019977 := bstep (se 2 (by rfl) ⟨757491, by rfl⟩ : syracuseStep 2019977 = 1514983) B1514983
theorem B1135711 : Blo 896573 1135711 := bstep (se 1 (by rfl) ⟨851783, by rfl⟩ : syracuseStep 1135711 = 1703567) B1703567
theorem B11523167 : Blo 896573 11523167 := bstep (se 1 (by rfl) ⟨8642375, by rfl⟩ : syracuseStep 11523167 = 17284751) B17284751
theorem B16602457 : Blo 896573 16602457 := bstep (se 2 (by rfl) ⟨6225921, by rfl⟩ : syracuseStep 16602457 = 12451843) B12451843
theorem B2020715 : Blo 896573 2020715 := bstep (se 1 (by rfl) ⟨1515536, by rfl⟩ : syracuseStep 2020715 = 3031073) B3031073
theorem B2872847 : Blo 896573 2872847 := bstep (se 1 (by rfl) ⟨2154635, by rfl⟩ : syracuseStep 2872847 = 4309271) B4309271
theorem B2020985 : Blo 896573 2020985 := bstep (se 2 (by rfl) ⟨757869, by rfl⟩ : syracuseStep 2020985 = 1515739) B1515739
theorem B3036959 : Blo 896573 3036959 := bstep (se 1 (by rfl) ⟨2277719, by rfl⟩ : syracuseStep 3036959 = 4555439) B4555439
theorem B6739789 : Blo 896573 6739789 := bstep (se 3 (by rfl) ⟨1263710, by rfl⟩ : syracuseStep 6739789 = 2527421) B2527421
theorem B3233627 : Blo 896573 3233627 := bstep (se 1 (by rfl) ⟨2425220, by rfl⟩ : syracuseStep 3233627 = 4850441) B4850441
theorem B2021345 : Blo 896573 2021345 := bstep (se 2 (by rfl) ⟨758004, by rfl⟩ : syracuseStep 2021345 = 1516009) B1516009
theorem B6838505 : Blo 896573 6838505 := bstep (se 2 (by rfl) ⟨2564439, by rfl⟩ : syracuseStep 6838505 = 5128879) B5128879
theorem B1366303 : Blo 896573 1366303 := bstep (se 1 (by rfl) ⟨1024727, by rfl⟩ : syracuseStep 1366303 = 2049455) B2049455
theorem B5462777 : Blo 896573 5462777 := bstep (se 2 (by rfl) ⟨2048541, by rfl⟩ : syracuseStep 5462777 = 4097083) B4097083
theorem B1825591 : Blo 896573 1825591 := bstep (se 1 (by rfl) ⟨1369193, by rfl⟩ : syracuseStep 1825591 = 2738387) B2738387
theorem B3070831 : Blo 896573 3070831 := bstep (se 1 (by rfl) ⟨2303123, by rfl⟩ : syracuseStep 3070831 = 4606247) B4606247
theorem B3464171 : Blo 896573 3464171 := bstep (se 1 (by rfl) ⟨2598128, by rfl⟩ : syracuseStep 3464171 = 5196257) B5196257
theorem B5463533 : Blo 896573 5463533 := bstep (se 3 (by rfl) ⟨1024412, by rfl⟩ : syracuseStep 5463533 = 2048825) B2048825
theorem B4218493 : Blo 896573 4218493 := bstep (se 3 (by rfl) ⟨790967, by rfl⟩ : syracuseStep 4218493 = 1581935) B1581935
theorem B2023199 : Blo 896573 2023199 := bstep (se 1 (by rfl) ⟨1517399, by rfl⟩ : syracuseStep 2023199 = 3034799) B3034799
theorem B8314807 : Blo 896573 8314807 := bstep (se 1 (by rfl) ⟨6236105, by rfl⟩ : syracuseStep 8314807 = 12472211) B12472211
theorem B2023415 : Blo 896573 2023415 := bstep (se 1 (by rfl) ⟨1517561, by rfl⟩ : syracuseStep 2023415 = 3035123) B3035123
theorem B3235963 : Blo 896573 3235963 := bstep (se 1 (by rfl) ⟨2426972, by rfl⟩ : syracuseStep 3235963 = 4853945) B4853945
theorem B2023631 : Blo 896573 2023631 := bstep (se 1 (by rfl) ⟨1517723, by rfl⟩ : syracuseStep 2023631 = 3035447) B3035447
theorem B7692569 : Blo 896573 7692569 := bstep (se 2 (by rfl) ⟨2884713, by rfl⟩ : syracuseStep 7692569 = 5769427) B5769427
theorem B2023775 : Blo 896573 2023775 := bstep (se 1 (by rfl) ⟨1517831, by rfl⟩ : syracuseStep 2023775 = 3035663) B3035663
theorem B8643145 : Blo 896573 8643145 := bstep (se 2 (by rfl) ⟨3241179, by rfl⟩ : syracuseStep 8643145 = 6482359) B6482359
theorem B12313255 : Blo 896573 12313255 := bstep (se 1 (by rfl) ⟨9234941, by rfl⟩ : syracuseStep 12313255 = 18469883) B18469883
theorem B2024495 : Blo 896573 2024495 := bstep (se 1 (by rfl) ⟨1518371, by rfl⟩ : syracuseStep 2024495 = 3036743) B3036743
theorem B1008751 : Blo 896573 1008751 := bstep (se 1 (by rfl) ⟨756563, by rfl⟩ : syracuseStep 1008751 = 1513127) B1513127
theorem B1009183 : Blo 896573 1009183 := bstep (se 1 (by rfl) ⟨756887, by rfl⟩ : syracuseStep 1009183 = 1513775) B1513775
theorem B27616889 : Blo 896573 27616889 := bstep (se 2 (by rfl) ⟨10356333, by rfl⟩ : syracuseStep 27616889 = 20712667) B20712667
theorem B2025143 : Blo 896573 2025143 := bstep (se 1 (by rfl) ⟨1518857, by rfl⟩ : syracuseStep 2025143 = 3037715) B3037715
theorem B2025593 : Blo 896573 2025593 := bstep (se 2 (by rfl) ⟨759597, by rfl⟩ : syracuseStep 2025593 = 1519195) B1519195
theorem B1927289 : Blo 896573 1927289 := bstep (se 2 (by rfl) ⟨722733, by rfl⟩ : syracuseStep 1927289 = 1445467) B1445467
theorem B1010047 : Blo 896573 1010047 := bstep (se 1 (by rfl) ⟨757535, by rfl⟩ : syracuseStep 1010047 = 1515071) B1515071
theorem B5827493 : Blo 896573 5827493 := bstep (se 4 (by rfl) ⟨546327, by rfl⟩ : syracuseStep 5827493 = 1092655) B1092655
theorem B2878537 : Blo 896573 2878537 := bstep (se 2 (by rfl) ⟨1079451, by rfl⟩ : syracuseStep 2878537 = 2158903) B2158903
theorem B4615337 : Blo 896573 4615337 := bstep (se 2 (by rfl) ⟨1730751, by rfl⟩ : syracuseStep 4615337 = 3461503) B3461503
theorem B1011451 : Blo 896573 1011451 := bstep (se 1 (by rfl) ⟨758588, by rfl⟩ : syracuseStep 1011451 = 1517177) B1517177
theorem B3239767 : Blo 896573 3239767 := bstep (se 1 (by rfl) ⟨2429825, by rfl⟩ : syracuseStep 3239767 = 4859651) B4859651
theorem B1011775 : Blo 896573 1011775 := bstep (se 1 (by rfl) ⟨758831, by rfl⟩ : syracuseStep 1011775 = 1517663) B1517663
theorem B1012639 : Blo 896573 1012639 := bstep (se 1 (by rfl) ⟨759479, by rfl⟩ : syracuseStep 1012639 = 1518959) B1518959
theorem B1012891 : Blo 896573 1012891 := bstep (se 1 (by rfl) ⟨759668, by rfl⟩ : syracuseStep 1012891 = 1519337) B1519337
theorem B11695769 : Blo 896573 11695769 := bstep (se 2 (by rfl) ⟨4385913, by rfl⟩ : syracuseStep 11695769 = 8771827) B8771827
theorem B3832019 : Blo 896573 3832019 := bstep (se 1 (by rfl) ⟨2874014, by rfl⟩ : syracuseStep 3832019 = 5748029) B5748029
theorem B4323631 : Blo 896573 4323631 := bstep (se 1 (by rfl) ⟨3242723, by rfl⟩ : syracuseStep 4323631 = 6485447) B6485447
theorem B3242537 : Blo 896573 3242537 := bstep (se 2 (by rfl) ⟨1215951, by rfl⟩ : syracuseStep 3242537 = 2431903) B2431903
theorem B4323881 : Blo 896573 4323881 := bstep (se 2 (by rfl) ⟨1621455, by rfl⟩ : syracuseStep 4323881 = 3242911) B3242911
theorem B1538651 : Blo 896573 1538651 := bstep (se 1 (by rfl) ⟨1153988, by rfl⟩ : syracuseStep 1538651 = 2307977) B2307977
theorem B1702633 : Blo 896573 1702633 := bstep (se 2 (by rfl) ⟨638487, by rfl⟩ : syracuseStep 1702633 = 1276975) B1276975
theorem B3636127 : Blo 896573 3636127 := bstep (se 1 (by rfl) ⟨2727095, by rfl⟩ : syracuseStep 3636127 = 5454191) B5454191
theorem B1703339 : Blo 896573 1703339 := bstep (se 1 (by rfl) ⟨1277504, by rfl⟩ : syracuseStep 1703339 = 2555009) B2555009
theorem B3112577 : Blo 896573 3112577 := bstep (se 2 (by rfl) ⟨1167216, by rfl⟩ : syracuseStep 3112577 = 2334433) B2334433
theorem B2162305 : Blo 896573 2162305 := bstep (se 2 (by rfl) ⟨810864, by rfl⟩ : syracuseStep 2162305 = 1621729) B1621729
theorem B3833743 : Blo 896573 3833743 := bstep (se 1 (by rfl) ⟨2875307, by rfl⟩ : syracuseStep 3833743 = 5750615) B5750615
theorem B55214045 : Blo 896573 55214045 := bstep (se 3 (by rfl) ⟨10352633, by rfl⟩ : syracuseStep 55214045 = 20705267) B20705267
theorem B8618237 : Blo 896573 8618237 := bstep (se 3 (by rfl) ⟨1615919, by rfl⟩ : syracuseStep 8618237 = 3231839) B3231839
theorem B2556319 : Blo 896573 2556319 := bstep (se 1 (by rfl) ⟨1917239, by rfl⟩ : syracuseStep 2556319 = 3834479) B3834479
theorem B2917031 : Blo 896573 2917031 := bstep (se 1 (by rfl) ⟨2187773, by rfl⟩ : syracuseStep 2917031 = 4375547) B4375547
theorem B10945367 : Blo 896573 10945367 := bstep (se 1 (by rfl) ⟨8209025, by rfl⟩ : syracuseStep 10945367 = 16418051) B16418051
theorem B16417673 : Blo 896573 16417673 := bstep (se 2 (by rfl) ⟨6156627, by rfl⟩ : syracuseStep 16417673 = 12313255) B12313255
theorem B4555763 : Blo 896573 4555763 := bstep (se 1 (by rfl) ⟨3416822, by rfl⟩ : syracuseStep 4555763 = 6833645) B6833645
theorem B6554621 : Blo 896573 6554621 := bstep (se 3 (by rfl) ⟨1228991, by rfl⟩ : syracuseStep 6554621 = 2457983) B2457983
theorem B11503073 : Blo 896573 11503073 := bstep (se 2 (by rfl) ⟨4313652, by rfl⟩ : syracuseStep 11503073 = 8627305) B8627305
theorem B1345001 : Blo 896573 1345001 := bstep (se 2 (by rfl) ⟨504375, by rfl⟩ : syracuseStep 1345001 = 1008751) B1008751
theorem B1345391 : Blo 896573 1345391 := bstep (se 1 (by rfl) ⟨1009043, by rfl⟩ : syracuseStep 1345391 = 2018087) B2018087
theorem B1345577 : Blo 896573 1345577 := bstep (se 2 (by rfl) ⟨504591, by rfl⟩ : syracuseStep 1345577 = 1009183) B1009183
theorem B2557993 : Blo 896573 2557993 := bstep (se 2 (by rfl) ⟨959247, by rfl⟩ : syracuseStep 2557993 = 1918495) B1918495
theorem B1345607 : Blo 896573 1345607 := bstep (se 1 (by rfl) ⟨1009205, by rfl⟩ : syracuseStep 1345607 = 2018411) B2018411
theorem B5179463 : Blo 896573 5179463 := bstep (se 1 (by rfl) ⟨3884597, by rfl⟩ : syracuseStep 5179463 = 7769195) B7769195
theorem B4556897 : Blo 896573 4556897 := bstep (se 2 (by rfl) ⟨1708836, by rfl⟩ : syracuseStep 4556897 = 3417673) B3417673
theorem B1345787 : Blo 896573 1345787 := bstep (se 1 (by rfl) ⟨1009340, by rfl⟩ : syracuseStep 1345787 = 2018681) B2018681
theorem B1345991 : Blo 896573 1345991 := bstep (se 1 (by rfl) ⟨1009493, by rfl⟩ : syracuseStep 1345991 = 2018987) B2018987
theorem B10389959 : Blo 896573 10389959 := bstep (se 1 (by rfl) ⟨7792469, by rfl⟩ : syracuseStep 10389959 = 15584939) B15584939
theorem B2427383 : Blo 896573 2427383 := bstep (se 1 (by rfl) ⟨1820537, by rfl⟩ : syracuseStep 2427383 = 3641075) B3641075
theorem B4557383 : Blo 896573 4557383 := bstep (se 1 (by rfl) ⟨3418037, by rfl⟩ : syracuseStep 4557383 = 6836075) B6836075
theorem B1346207 : Blo 896573 1346207 := bstep (se 1 (by rfl) ⟨1009655, by rfl⟩ : syracuseStep 1346207 = 2019311) B2019311
theorem B1346255 : Blo 896573 1346255 := bstep (se 1 (by rfl) ⟨1009691, by rfl⟩ : syracuseStep 1346255 = 2019383) B2019383
theorem B4557545 : Blo 896573 4557545 := bstep (se 2 (by rfl) ⟨1709079, by rfl⟩ : syracuseStep 4557545 = 3418159) B3418159
theorem B1346351 : Blo 896573 1346351 := bstep (se 1 (by rfl) ⟨1009763, by rfl⟩ : syracuseStep 1346351 = 2019527) B2019527
theorem B1346471 : Blo 896573 1346471 := bstep (se 1 (by rfl) ⟨1009853, by rfl⟩ : syracuseStep 1346471 = 2019707) B2019707
theorem B5114825 : Blo 896573 5114825 := bstep (se 2 (by rfl) ⟨1918059, by rfl⟩ : syracuseStep 5114825 = 3836119) B3836119
theorem B11504713 : Blo 896573 11504713 := bstep (se 2 (by rfl) ⟨4314267, by rfl⟩ : syracuseStep 11504713 = 8628535) B8628535
theorem B1346651 : Blo 896573 1346651 := bstep (se 1 (by rfl) ⟨1009988, by rfl⟩ : syracuseStep 1346651 = 2019977) B2019977
theorem B1346729 : Blo 896573 1346729 := bstep (se 2 (by rfl) ⟨505023, by rfl⟩ : syracuseStep 1346729 = 1010047) B1010047
theorem B1347143 : Blo 896573 1347143 := bstep (se 1 (by rfl) ⟨1010357, by rfl⟩ : syracuseStep 1347143 = 2020715) B2020715
theorem B6819551 : Blo 896573 6819551 := bstep (se 1 (by rfl) ⟨5114663, by rfl⟩ : syracuseStep 6819551 = 10229327) B10229327
theorem B1707743 : Blo 896573 1707743 := bstep (se 1 (by rfl) ⟨1280807, by rfl⟩ : syracuseStep 1707743 = 2561615) B2561615
theorem B1347323 : Blo 896573 1347323 := bstep (se 1 (by rfl) ⟨1010492, by rfl⟩ : syracuseStep 1347323 = 2020985) B2020985
theorem B1347563 : Blo 896573 1347563 := bstep (se 1 (by rfl) ⟨1010672, by rfl⟩ : syracuseStep 1347563 = 2021345) B2021345
theorem B1708123 : Blo 896573 1708123 := bstep (se 1 (by rfl) ⟨1281092, by rfl⟩ : syracuseStep 1708123 = 2562185) B2562185
theorem B3838049 : Blo 896573 3838049 := bstep (se 2 (by rfl) ⟨1439268, by rfl⟩ : syracuseStep 3838049 = 2878537) B2878537
theorem B4559003 : Blo 896573 4559003 := bstep (se 1 (by rfl) ⟨3419252, by rfl⟩ : syracuseStep 4559003 = 6838505) B6838505
theorem B3641851 : Blo 896573 3641851 := bstep (se 1 (by rfl) ⟨2731388, by rfl⟩ : syracuseStep 3641851 = 5462777) B5462777
theorem B3642355 : Blo 896573 3642355 := bstep (se 1 (by rfl) ⟨2731766, by rfl⟩ : syracuseStep 3642355 = 5463533) B5463533
theorem B1348601 : Blo 896573 1348601 := bstep (se 2 (by rfl) ⟨505725, by rfl⟩ : syracuseStep 1348601 = 1011451) B1011451
theorem B1348799 : Blo 896573 1348799 := bstep (se 1 (by rfl) ⟨1011599, by rfl⟩ : syracuseStep 1348799 = 2023199) B2023199
theorem B1348943 : Blo 896573 1348943 := bstep (se 1 (by rfl) ⟨1011707, by rfl⟩ : syracuseStep 1348943 = 2023415) B2023415
theorem B1349033 : Blo 896573 1349033 := bstep (se 2 (by rfl) ⟨505887, by rfl⟩ : syracuseStep 1349033 = 1011775) B1011775
theorem B1349087 : Blo 896573 1349087 := bstep (se 1 (by rfl) ⟨1011815, by rfl⟩ : syracuseStep 1349087 = 2023631) B2023631
theorem B1349183 : Blo 896573 1349183 := bstep (se 1 (by rfl) ⟨1011887, by rfl⟩ : syracuseStep 1349183 = 2023775) B2023775
theorem B2627407 : Blo 896573 2627407 := bstep (se 1 (by rfl) ⟨1970555, by rfl⟩ : syracuseStep 2627407 = 3941111) B3941111
theorem B2430919 : Blo 896573 2430919 := bstep (se 1 (by rfl) ⟨1823189, by rfl⟩ : syracuseStep 2430919 = 3646379) B3646379
theorem B1349663 : Blo 896573 1349663 := bstep (se 1 (by rfl) ⟨1012247, by rfl⟩ : syracuseStep 1349663 = 2024495) B2024495
theorem B3414089 : Blo 896573 3414089 := bstep (se 2 (by rfl) ⟨1280283, by rfl⟩ : syracuseStep 3414089 = 2560567) B2560567
theorem B1350095 : Blo 896573 1350095 := bstep (se 1 (by rfl) ⟨1012571, by rfl⟩ : syracuseStep 1350095 = 2025143) B2025143
theorem B5118491 : Blo 896573 5118491 := bstep (se 1 (by rfl) ⟨3838868, by rfl⟩ : syracuseStep 5118491 = 7677737) B7677737
theorem B1350185 : Blo 896573 1350185 := bstep (se 2 (by rfl) ⟨506319, by rfl⟩ : syracuseStep 1350185 = 1012639) B1012639
theorem B1350395 : Blo 896573 1350395 := bstep (se 1 (by rfl) ⟨1012796, by rfl⟩ : syracuseStep 1350395 = 2025593) B2025593
theorem B1284859 : Blo 896573 1284859 := bstep (se 1 (by rfl) ⟨963644, by rfl⟩ : syracuseStep 1284859 = 1927289) B1927289
theorem B1514281 : Blo 896573 1514281 := bstep (se 2 (by rfl) ⟨567855, by rfl⟩ : syracuseStep 1514281 = 1135711) B1135711
theorem B1350521 : Blo 896573 1350521 := bstep (se 2 (by rfl) ⟨506445, by rfl⟩ : syracuseStep 1350521 = 1012891) B1012891
theorem B1514551 : Blo 896573 1514551 := bstep (se 1 (by rfl) ⟨1135913, by rfl⟩ : syracuseStep 1514551 = 2271827) B2271827
theorem B3415547 : Blo 896573 3415547 := bstep (se 1 (by rfl) ⟨2561660, by rfl⟩ : syracuseStep 3415547 = 5123321) B5123321
theorem B8986385 : Blo 896573 8986385 := bstep (se 2 (by rfl) ⟨3369894, by rfl⟩ : syracuseStep 8986385 = 6739789) B6739789
theorem B17276753 : Blo 896573 17276753 := bstep (se 2 (by rfl) ⟨6478782, by rfl⟩ : syracuseStep 17276753 = 12957565) B12957565
theorem B21635171 : Blo 896573 21635171 := bstep (se 1 (by rfl) ⟨16226378, by rfl⟩ : syracuseStep 21635171 = 32452757) B32452757
theorem B1516063 : Blo 896573 1516063 := bstep (se 1 (by rfl) ⟨1137047, by rfl⟩ : syracuseStep 1516063 = 2274095) B2274095
theorem B3416687 : Blo 896573 3416687 := bstep (se 1 (by rfl) ⟨2562515, by rfl⟩ : syracuseStep 3416687 = 5125031) B5125031
theorem B2270177 : Blo 896573 2270177 := bstep (se 2 (by rfl) ⟨851316, by rfl⟩ : syracuseStep 2270177 = 1702633) B1702633
theorem B2434121 : Blo 896573 2434121 := bstep (se 2 (by rfl) ⟨912795, by rfl⟩ : syracuseStep 2434121 = 1825591) B1825591
theorem B1517231 : Blo 896573 1517231 := bstep (se 1 (by rfl) ⟨1137923, by rfl⟩ : syracuseStep 1517231 = 2275847) B2275847
theorem B1025767 : Blo 896573 1025767 := bstep (se 1 (by rfl) ⟨769325, by rfl⟩ : syracuseStep 1025767 = 1538651) B1538651
theorem B17278757 : Blo 896573 17278757 := bstep (se 4 (by rfl) ⟨1619883, by rfl⟩ : syracuseStep 17278757 = 3239767) B3239767
theorem B1517791 : Blo 896573 1517791 := bstep (se 1 (by rfl) ⟨1138343, by rfl⟩ : syracuseStep 1517791 = 2276687) B2276687
theorem B2075051 : Blo 896573 2075051 := bstep (se 1 (by rfl) ⟨1556288, by rfl⟩ : syracuseStep 2075051 = 3112577) B3112577
theorem B11086409 : Blo 896573 11086409 := bstep (se 2 (by rfl) ⟨4157403, by rfl⟩ : syracuseStep 11086409 = 8314807) B8314807
theorem B36809363 : Blo 896573 36809363 := bstep (se 1 (by rfl) ⟨27607022, by rfl⟩ : syracuseStep 36809363 = 55214045) B55214045
theorem B3026105 : Blo 896573 3026105 := bstep (se 2 (by rfl) ⟨1134789, by rfl⟩ : syracuseStep 3026105 = 2269579) B2269579
theorem B3026267 : Blo 896573 3026267 := bstep (se 1 (by rfl) ⟨2269700, by rfl⟩ : syracuseStep 3026267 = 4539401) B4539401
theorem B2272799 : Blo 896573 2272799 := bstep (se 1 (by rfl) ⟨1704599, by rfl⟩ : syracuseStep 2272799 = 3409199) B3409199
theorem B896679 : Blo 896573 896679 := bstep (se 1 (by rfl) ⟨672509, by rfl⟩ : syracuseStep 896679 = 1345019) B1345019
theorem B896703 : Blo 896573 896703 := bstep (se 1 (by rfl) ⟨672527, by rfl⟩ : syracuseStep 896703 = 1345055) B1345055
theorem B896799 : Blo 896573 896799 := bstep (se 1 (by rfl) ⟨672599, by rfl⟩ : syracuseStep 896799 = 1345199) B1345199
theorem B896879 : Blo 896573 896879 := bstep (se 1 (by rfl) ⟨672659, by rfl⟩ : syracuseStep 896879 = 1345319) B1345319
theorem B20721529 : Blo 896573 20721529 := bstep (se 2 (by rfl) ⟨7770573, by rfl⟩ : syracuseStep 20721529 = 15541147) B15541147
theorem B10923997 : Blo 896573 10923997 := bstep (se 3 (by rfl) ⟨2048249, by rfl⟩ : syracuseStep 10923997 = 4096499) B4096499
theorem B897247 : Blo 896573 897247 := bstep (se 1 (by rfl) ⟨672935, by rfl⟩ : syracuseStep 897247 = 1345871) B1345871
theorem B3649769 : Blo 896573 3649769 := bstep (se 2 (by rfl) ⟨1368663, by rfl⟩ : syracuseStep 3649769 = 2737327) B2737327
theorem B897279 : Blo 896573 897279 := bstep (se 1 (by rfl) ⟨672959, by rfl⟩ : syracuseStep 897279 = 1345919) B1345919
theorem B897307 : Blo 896573 897307 := bstep (se 1 (by rfl) ⟨672980, by rfl⟩ : syracuseStep 897307 = 1345961) B1345961
theorem B34484615 : Blo 896573 34484615 := bstep (se 1 (by rfl) ⟨25863461, by rfl⟩ : syracuseStep 34484615 = 51726923) B51726923
theorem B897563 : Blo 896573 897563 := bstep (se 1 (by rfl) ⟨673172, by rfl⟩ : syracuseStep 897563 = 1346345) B1346345
theorem B11678303 : Blo 896573 11678303 := bstep (se 1 (by rfl) ⟨8758727, by rfl⟩ : syracuseStep 11678303 = 17517455) B17517455
theorem B897703 : Blo 896573 897703 := bstep (se 1 (by rfl) ⟨673277, by rfl⟩ : syracuseStep 897703 = 1346555) B1346555
theorem B10236617 : Blo 896573 10236617 := bstep (se 2 (by rfl) ⟨3838731, by rfl⟩ : syracuseStep 10236617 = 7677463) B7677463
theorem B897743 : Blo 896573 897743 := bstep (se 1 (by rfl) ⟨673307, by rfl⟩ : syracuseStep 897743 = 1346615) B1346615
theorem B897823 : Blo 896573 897823 := bstep (se 1 (by rfl) ⟨673367, by rfl⟩ : syracuseStep 897823 = 1346735) B1346735
theorem B898303 : Blo 896573 898303 := bstep (se 1 (by rfl) ⟨673727, by rfl⟩ : syracuseStep 898303 = 1347455) B1347455
theorem B3028265 : Blo 896573 3028265 := bstep (se 2 (by rfl) ⟨1135599, by rfl⟩ : syracuseStep 3028265 = 2271199) B2271199
theorem B898431 : Blo 896573 898431 := bstep (se 1 (by rfl) ⟨673823, by rfl⟩ : syracuseStep 898431 = 1347647) B1347647
theorem B898587 : Blo 896573 898587 := bstep (se 1 (by rfl) ⟨673940, by rfl⟩ : syracuseStep 898587 = 1347881) B1347881
theorem B898767 : Blo 896573 898767 := bstep (se 1 (by rfl) ⟨674075, by rfl⟩ : syracuseStep 898767 = 1348151) B1348151
theorem B899007 : Blo 896573 899007 := bstep (se 1 (by rfl) ⟨674255, by rfl⟩ : syracuseStep 899007 = 1348511) B1348511
theorem B899135 : Blo 896573 899135 := bstep (se 1 (by rfl) ⟨674351, by rfl⟩ : syracuseStep 899135 = 1348703) B1348703
theorem B7682111 : Blo 896573 7682111 := bstep (se 1 (by rfl) ⟨5761583, by rfl⟩ : syracuseStep 7682111 = 11523167) B11523167
theorem B899175 : Blo 896573 899175 := bstep (se 1 (by rfl) ⟨674381, by rfl⟩ : syracuseStep 899175 = 1348763) B1348763
theorem B899631 : Blo 896573 899631 := bstep (se 1 (by rfl) ⟨674723, by rfl⟩ : syracuseStep 899631 = 1349447) B1349447
theorem B5126921 : Blo 896573 5126921 := bstep (se 2 (by rfl) ⟨1922595, by rfl⟩ : syracuseStep 5126921 = 3845191) B3845191
theorem B900031 : Blo 896573 900031 := bstep (se 1 (by rfl) ⟨675023, by rfl⟩ : syracuseStep 900031 = 1350047) B1350047
theorem B900079 : Blo 896573 900079 := bstep (se 1 (by rfl) ⟨675059, by rfl⟩ : syracuseStep 900079 = 1350119) B1350119
theorem B2309447 : Blo 896573 2309447 := bstep (se 1 (by rfl) ⟨1732085, by rfl⟩ : syracuseStep 2309447 = 3464171) B3464171
theorem B5128379 : Blo 896573 5128379 := bstep (se 1 (by rfl) ⟨3846284, by rfl⟩ : syracuseStep 5128379 = 7692569) B7692569
theorem B3195095 : Blo 896573 3195095 := bstep (se 1 (by rfl) ⟨2396321, by rfl⟩ : syracuseStep 3195095 = 4792643) B4792643
theorem B11518199 : Blo 896573 11518199 := bstep (se 1 (by rfl) ⟨8638649, by rfl⟩ : syracuseStep 11518199 = 17277299) B17277299
theorem B2277679 : Blo 896573 2277679 := bstep (se 1 (by rfl) ⟨1708259, by rfl⟩ : syracuseStep 2277679 = 3416519) B3416519
theorem B5751947 : Blo 896573 5751947 := bstep (se 1 (by rfl) ⟨4313960, by rfl⟩ : syracuseStep 5751947 = 8627921) B8627921
theorem B6145163 : Blo 896573 6145163 := bstep (se 1 (by rfl) ⟨4608872, by rfl⟩ : syracuseStep 6145163 = 9217745) B9217745
theorem B73811249 : Blo 896573 73811249 := bstep (se 2 (by rfl) ⟨27679218, by rfl⟩ : syracuseStep 73811249 = 55358437) B55358437
theorem B2737471 : Blo 896573 2737471 := bstep (se 1 (by rfl) ⟨2053103, by rfl⟩ : syracuseStep 2737471 = 4106207) B4106207
theorem B4605281 : Blo 896573 4605281 := bstep (se 2 (by rfl) ⟨1726980, by rfl⟩ : syracuseStep 4605281 = 3453961) B3453961
theorem B2279087 : Blo 896573 2279087 := bstep (se 1 (by rfl) ⟨1709315, by rfl⟩ : syracuseStep 2279087 = 3418631) B3418631
theorem B2279137 : Blo 896573 2279137 := bstep (se 2 (by rfl) ⟨854676, by rfl⟩ : syracuseStep 2279137 = 1709353) B1709353
theorem B22136609 : Blo 896573 22136609 := bstep (se 2 (by rfl) ⟨8301228, by rfl⟩ : syracuseStep 22136609 = 16602457) B16602457
theorem B3884995 : Blo 896573 3884995 := bstep (se 1 (by rfl) ⟨2913746, by rfl⟩ : syracuseStep 3884995 = 5827493) B5827493
theorem B1821737 : Blo 896573 1821737 := bstep (se 2 (by rfl) ⟨683151, by rfl⟩ : syracuseStep 1821737 = 1366303) B1366303
theorem B2018375 : Blo 896573 2018375 := bstep (se 1 (by rfl) ⟨1513781, by rfl⟩ : syracuseStep 2018375 = 3027563) B3027563
theorem B12307565 : Blo 896573 12307565 := bstep (se 3 (by rfl) ⟨2307668, by rfl⟩ : syracuseStep 12307565 = 4615337) B4615337
theorem B2019455 : Blo 896573 2019455 := bstep (se 1 (by rfl) ⟨1514591, by rfl⟩ : syracuseStep 2019455 = 3029183) B3029183
theorem B5624657 : Blo 896573 5624657 := bstep (se 2 (by rfl) ⟨2109246, by rfl⟩ : syracuseStep 5624657 = 4218493) B4218493
theorem B1135559 : Blo 896573 1135559 := bstep (se 1 (by rfl) ⟨851669, by rfl⟩ : syracuseStep 1135559 = 1703339) B1703339
theorem B1365257 : Blo 896573 1365257 := bstep (se 2 (by rfl) ⟨511971, by rfl⟩ : syracuseStep 1365257 = 1023943) B1023943
theorem B4314617 : Blo 896573 4314617 := bstep (se 2 (by rfl) ⟨1617981, by rfl⟩ : syracuseStep 4314617 = 3235963) B3235963
theorem B2020859 : Blo 896573 2020859 := bstep (se 1 (by rfl) ⟨1515644, by rfl⟩ : syracuseStep 2020859 = 3031289) B3031289
theorem B2021039 : Blo 896573 2021039 := bstep (se 1 (by rfl) ⟨1515779, by rfl⟩ : syracuseStep 2021039 = 3031559) B3031559
theorem B1922783 : Blo 896573 1922783 := bstep (se 1 (by rfl) ⟨1442087, by rfl⟩ : syracuseStep 1922783 = 2884175) B2884175
theorem B2021111 : Blo 896573 2021111 := bstep (se 1 (by rfl) ⟨1515833, by rfl⟩ : syracuseStep 2021111 = 3031667) B3031667
theorem B5756663 : Blo 896573 5756663 := bstep (se 1 (by rfl) ⟨4317497, by rfl⟩ : syracuseStep 5756663 = 8634995) B8634995
theorem B2021291 : Blo 896573 2021291 := bstep (se 1 (by rfl) ⟨1515968, by rfl⟩ : syracuseStep 2021291 = 3031937) B3031937
theorem B7395311 : Blo 896573 7395311 := bstep (se 1 (by rfl) ⟨5546483, by rfl⟩ : syracuseStep 7395311 = 11092967) B11092967
theorem B11524193 : Blo 896573 11524193 := bstep (se 2 (by rfl) ⟨4321572, by rfl⟩ : syracuseStep 11524193 = 8643145) B8643145
theorem B11491591 : Blo 896573 11491591 := bstep (se 1 (by rfl) ⟨8618693, by rfl⟩ : syracuseStep 11491591 = 17237387) B17237387
theorem B2021651 : Blo 896573 2021651 := bstep (se 1 (by rfl) ⟨1516238, by rfl⟩ : syracuseStep 2021651 = 3032477) B3032477
theorem B2021759 : Blo 896573 2021759 := bstep (se 1 (by rfl) ⟨1516319, by rfl⟩ : syracuseStep 2021759 = 3032639) B3032639
theorem B2021831 : Blo 896573 2021831 := bstep (se 1 (by rfl) ⟨1516373, by rfl⟩ : syracuseStep 2021831 = 3032747) B3032747
theorem B2022191 : Blo 896573 2022191 := bstep (se 1 (by rfl) ⟨1516643, by rfl⟩ : syracuseStep 2022191 = 3033287) B3033287
theorem B2022281 : Blo 896573 2022281 := bstep (se 2 (by rfl) ⟨758355, by rfl⟩ : syracuseStep 2022281 = 1516711) B1516711
theorem B2022587 : Blo 896573 2022587 := bstep (se 1 (by rfl) ⟨1516940, by rfl⟩ : syracuseStep 2022587 = 3033881) B3033881
theorem B3038633 : Blo 896573 3038633 := bstep (se 2 (by rfl) ⟨1139487, by rfl⟩ : syracuseStep 3038633 = 2278975) B2278975
theorem B2022839 : Blo 896573 2022839 := bstep (se 1 (by rfl) ⟨1517129, by rfl⟩ : syracuseStep 2022839 = 3034259) B3034259
theorem B11492927 : Blo 896573 11492927 := bstep (se 1 (by rfl) ⟨8619695, by rfl⟩ : syracuseStep 11492927 = 17239391) B17239391
theorem B2023019 : Blo 896573 2023019 := bstep (se 1 (by rfl) ⟨1517264, by rfl⟩ : syracuseStep 2023019 = 3034529) B3034529
theorem B2023289 : Blo 896573 2023289 := bstep (se 2 (by rfl) ⟨758733, by rfl⟩ : syracuseStep 2023289 = 1517467) B1517467
theorem B2023379 : Blo 896573 2023379 := bstep (se 1 (by rfl) ⟨1517534, by rfl⟩ : syracuseStep 2023379 = 3035069) B3035069
theorem B2023487 : Blo 896573 2023487 := bstep (se 1 (by rfl) ⟨1517615, by rfl⟩ : syracuseStep 2023487 = 3035231) B3035231
theorem B13132151 : Blo 896573 13132151 := bstep (se 1 (by rfl) ⟨9849113, by rfl⟩ : syracuseStep 13132151 = 19698227) B19698227
theorem B4547015 : Blo 896573 4547015 := bstep (se 1 (by rfl) ⟨3410261, by rfl⟩ : syracuseStep 4547015 = 6820523) B6820523
theorem B2024639 : Blo 896573 2024639 := bstep (se 1 (by rfl) ⟨1518479, by rfl⟩ : syracuseStep 2024639 = 3036959) B3036959
theorem B2155751 : Blo 896573 2155751 := bstep (se 1 (by rfl) ⟨1616813, by rfl⟩ : syracuseStep 2155751 = 3233627) B3233627
theorem B37414133 : Blo 896573 37414133 := bstep (se 5 (by rfl) ⟨1753787, by rfl⟩ : syracuseStep 37414133 = 3507575) B3507575
theorem B7660925 : Blo 896573 7660925 := bstep (se 3 (by rfl) ⟨1436423, by rfl⟩ : syracuseStep 7660925 = 2872847) B2872847
theorem B21849749 : Blo 896573 21849749 := bstep (se 6 (by rfl) ⟨512103, by rfl⟩ : syracuseStep 21849749 = 1024207) B1024207
theorem B7301087 : Blo 896573 7301087 := bstep (se 1 (by rfl) ⟨5475815, by rfl⟩ : syracuseStep 7301087 = 10951631) B10951631
theorem B4548635 : Blo 896573 4548635 := bstep (se 1 (by rfl) ⟨3411476, by rfl⟩ : syracuseStep 4548635 = 6822953) B6822953
theorem B7793297 : Blo 896573 7793297 := bstep (se 2 (by rfl) ⟨2922486, by rfl⟩ : syracuseStep 7793297 = 5844973) B5844973
theorem B18411259 : Blo 896573 18411259 := bstep (se 1 (by rfl) ⟨13808444, by rfl⟩ : syracuseStep 18411259 = 27616889) B27616889
theorem B1011919 : Blo 896573 1011919 := bstep (se 1 (by rfl) ⟨758939, by rfl⟩ : syracuseStep 1011919 = 1517879) B1517879
theorem B4550903 : Blo 896573 4550903 := bstep (se 1 (by rfl) ⟨3413177, by rfl⟩ : syracuseStep 4550903 = 6826355) B6826355
theorem B3895543 : Blo 896573 3895543 := bstep (se 1 (by rfl) ⟨2921657, by rfl⟩ : syracuseStep 3895543 = 5843315) B5843315
theorem B1012783 : Blo 896573 1012783 := bstep (se 1 (by rfl) ⟨759587, by rfl⟩ : syracuseStep 1012783 = 1519175) B1519175
theorem B5764841 : Blo 896573 5764841 := bstep (se 2 (by rfl) ⟨2161815, by rfl⟩ : syracuseStep 5764841 = 4323631) B4323631
theorem B11532293 : Blo 896573 11532293 := bstep (se 4 (by rfl) ⟨1081152, by rfl⟩ : syracuseStep 11532293 = 2162305) B2162305
theorem B3700883 : Blo 896573 3700883 := bstep (se 1 (by rfl) ⟨2775662, by rfl⟩ : syracuseStep 3700883 = 5551325) B5551325
theorem B3832103 : Blo 896573 3832103 := bstep (se 1 (by rfl) ⟨2874077, by rfl⟩ : syracuseStep 3832103 = 5748155) B5748155
theorem B7797179 : Blo 896573 7797179 := bstep (se 1 (by rfl) ⟨5847884, by rfl⟩ : syracuseStep 7797179 = 11695769) B11695769
theorem B4094441 : Blo 896573 4094441 := bstep (se 2 (by rfl) ⟨1535415, by rfl⟩ : syracuseStep 4094441 = 3070831) B3070831
theorem B4848169 : Blo 896573 4848169 := bstep (se 2 (by rfl) ⟨1818063, by rfl⟩ : syracuseStep 4848169 = 3636127) B3636127
theorem B2554679 : Blo 896573 2554679 := bstep (se 1 (by rfl) ⟨1916009, by rfl⟩ : syracuseStep 2554679 = 3832019) B3832019
theorem B2161691 : Blo 896573 2161691 := bstep (se 1 (by rfl) ⟨1621268, by rfl⟩ : syracuseStep 2161691 = 3242537) B3242537
theorem B2882587 : Blo 896573 2882587 := bstep (se 1 (by rfl) ⟨2161940, by rfl⟩ : syracuseStep 2882587 = 4323881) B4323881
theorem B1277083 : Blo 896573 1277083 := bstep (se 1 (by rfl) ⟨957812, by rfl⟩ : syracuseStep 1277083 = 1915625) B1915625
theorem B5111657 : Blo 896573 5111657 := bstep (se 2 (by rfl) ⟨1916871, by rfl⟩ : syracuseStep 5111657 = 3833743) B3833743
theorem B3408425 : Blo 896573 3408425 := bstep (se 2 (by rfl) ⟨1278159, by rfl⟩ : syracuseStep 3408425 = 2556319) B2556319
theorem B10945115 : Blo 896573 10945115 := bstep (se 1 (by rfl) ⟨8208836, by rfl⟩ : syracuseStep 10945115 = 16417673) B16417673
theorem B3834631 : Blo 896573 3834631 := bstep (se 1 (by rfl) ⟨2875973, by rfl⟩ : syracuseStep 3834631 = 5751947) B5751947
theorem B4096775 : Blo 896573 4096775 := bstep (se 1 (by rfl) ⟨3072581, by rfl⟩ : syracuseStep 4096775 = 6145163) B6145163
theorem B7668715 : Blo 896573 7668715 := bstep (se 1 (by rfl) ⟨5751536, by rfl⟩ : syracuseStep 7668715 = 11503073) B11503073
theorem B3409883 : Blo 896573 3409883 := bstep (se 1 (by rfl) ⟨2557412, by rfl⟩ : syracuseStep 3409883 = 5114825) B5114825
theorem B1345583 : Blo 896573 1345583 := bstep (se 1 (by rfl) ⟨1009187, by rfl⟩ : syracuseStep 1345583 = 2018375) B2018375
theorem B34081013 : Blo 896573 34081013 := bstep (se 5 (by rfl) ⟨1597547, by rfl⟩ : syracuseStep 34081013 = 3195095) B3195095
theorem B5179993 : Blo 896573 5179993 := bstep (se 2 (by rfl) ⟨1942497, by rfl⟩ : syracuseStep 5179993 = 3884995) B3884995
theorem B3410657 : Blo 896573 3410657 := bstep (se 2 (by rfl) ⟨1278996, by rfl⟩ : syracuseStep 3410657 = 2557993) B2557993
theorem B2558699 : Blo 896573 2558699 := bstep (se 1 (by rfl) ⟨1919024, by rfl⟩ : syracuseStep 2558699 = 3838049) B3838049
theorem B1346303 : Blo 896573 1346303 := bstep (se 1 (by rfl) ⟨1009727, by rfl⟩ : syracuseStep 1346303 = 2019455) B2019455
theorem B1347239 : Blo 896573 1347239 := bstep (se 1 (by rfl) ⟨1010429, by rfl⟩ : syracuseStep 1347239 = 2020859) B2020859
theorem B1347359 : Blo 896573 1347359 := bstep (se 1 (by rfl) ⟨1010519, by rfl⟩ : syracuseStep 1347359 = 2021039) B2021039
theorem B1347407 : Blo 896573 1347407 := bstep (se 1 (by rfl) ⟨1010555, by rfl⟩ : syracuseStep 1347407 = 2021111) B2021111
theorem B3837775 : Blo 896573 3837775 := bstep (se 1 (by rfl) ⟨2878331, by rfl⟩ : syracuseStep 3837775 = 5756663) B5756663
theorem B1347527 : Blo 896573 1347527 := bstep (se 1 (by rfl) ⟨1010645, by rfl⟩ : syracuseStep 1347527 = 2021291) B2021291
theorem B15339617 : Blo 896573 15339617 := bstep (se 2 (by rfl) ⟨5752356, by rfl⟩ : syracuseStep 15339617 = 11504713) B11504713
theorem B1347767 : Blo 896573 1347767 := bstep (se 1 (by rfl) ⟨1010825, by rfl⟩ : syracuseStep 1347767 = 2021651) B2021651
theorem B1347839 : Blo 896573 1347839 := bstep (se 1 (by rfl) ⟨1010879, by rfl⟩ : syracuseStep 1347839 = 2021759) B2021759
theorem B1347887 : Blo 896573 1347887 := bstep (se 1 (by rfl) ⟨1010915, by rfl⟩ : syracuseStep 1347887 = 2021831) B2021831
theorem B3412327 : Blo 896573 3412327 := bstep (se 1 (by rfl) ⟨2559245, by rfl⟩ : syracuseStep 3412327 = 5118491) B5118491
theorem B1348127 : Blo 896573 1348127 := bstep (se 1 (by rfl) ⟨1011095, by rfl⟩ : syracuseStep 1348127 = 2022191) B2022191
theorem B1348187 : Blo 896573 1348187 := bstep (se 1 (by rfl) ⟨1011140, by rfl⟩ : syracuseStep 1348187 = 2022281) B2022281
theorem B1348391 : Blo 896573 1348391 := bstep (se 1 (by rfl) ⟨1011293, by rfl⟩ : syracuseStep 1348391 = 2022587) B2022587
theorem B1348559 : Blo 896573 1348559 := bstep (se 1 (by rfl) ⟨1011419, by rfl⟩ : syracuseStep 1348559 = 2022839) B2022839
theorem B24548345 : Blo 896573 24548345 := bstep (se 2 (by rfl) ⟨9205629, by rfl⟩ : syracuseStep 24548345 = 18411259) B18411259
theorem B1348679 : Blo 896573 1348679 := bstep (se 1 (by rfl) ⟨1011509, by rfl⟩ : syracuseStep 1348679 = 2023019) B2023019
theorem B27628705 : Blo 896573 27628705 := bstep (se 2 (by rfl) ⟨10360764, by rfl⟩ : syracuseStep 27628705 = 20721529) B20721529
theorem B1348859 : Blo 896573 1348859 := bstep (se 1 (by rfl) ⟨1011644, by rfl⟩ : syracuseStep 1348859 = 2023289) B2023289
theorem B1348919 : Blo 896573 1348919 := bstep (se 1 (by rfl) ⟨1011689, by rfl⟩ : syracuseStep 1348919 = 2023379) B2023379
theorem B1348991 : Blo 896573 1348991 := bstep (se 1 (by rfl) ⟨1011743, by rfl⟩ : syracuseStep 1348991 = 2023487) B2023487
theorem B14423447 : Blo 896573 14423447 := bstep (se 1 (by rfl) ⟨10817585, by rfl⟩ : syracuseStep 14423447 = 21635171) B21635171
theorem B8754767 : Blo 896573 8754767 := bstep (se 1 (by rfl) ⟨6566075, by rfl⟩ : syracuseStep 8754767 = 13132151) B13132151
theorem B1349225 : Blo 896573 1349225 := bstep (se 2 (by rfl) ⟨505959, by rfl⟩ : syracuseStep 1349225 = 1011919) B1011919
theorem B1513451 : Blo 896573 1513451 := bstep (se 1 (by rfl) ⟨1135088, by rfl⟩ : syracuseStep 1513451 = 2270177) B2270177
theorem B4855801 : Blo 896573 4855801 := bstep (se 2 (by rfl) ⟨1820925, by rfl⟩ : syracuseStep 4855801 = 3641851) B3641851
theorem B1349759 : Blo 896573 1349759 := bstep (se 1 (by rfl) ⟨1012319, by rfl⟩ : syracuseStep 1349759 = 2024639) B2024639
theorem B24942755 : Blo 896573 24942755 := bstep (se 1 (by rfl) ⟨18707066, by rfl⟩ : syracuseStep 24942755 = 37414133) B37414133
theorem B4856473 : Blo 896573 4856473 := bstep (se 2 (by rfl) ⟨1821177, by rfl⟩ : syracuseStep 4856473 = 3642355) B3642355
theorem B1350377 : Blo 896573 1350377 := bstep (se 2 (by rfl) ⟨506391, by rfl⟩ : syracuseStep 1350377 = 1012783) B1012783
theorem B1383367 : Blo 896573 1383367 := bstep (se 1 (by rfl) ⟨1037525, by rfl⟩ : syracuseStep 1383367 = 2075051) B2075051
theorem B1515199 : Blo 896573 1515199 := bstep (se 1 (by rfl) ⟨1136399, by rfl⟩ : syracuseStep 1515199 = 2272799) B2272799
theorem B4857965 : Blo 896573 4857965 := bstep (se 3 (by rfl) ⟨910868, by rfl⟩ : syracuseStep 4857965 = 1821737) B1821737
theorem B2433179 : Blo 896573 2433179 := bstep (se 1 (by rfl) ⟨1824884, by rfl⟩ : syracuseStep 2433179 = 3649769) B3649769
theorem B6824411 : Blo 896573 6824411 := bstep (se 1 (by rfl) ⟨5118308, by rfl⟩ : syracuseStep 6824411 = 10236617) B10236617
theorem B6464225 : Blo 896573 6464225 := bstep (se 2 (by rfl) ⟨2424084, by rfl⟩ : syracuseStep 6464225 = 4848169) B4848169
theorem B1713145 : Blo 896573 1713145 := bstep (se 2 (by rfl) ⟨642429, by rfl⟩ : syracuseStep 1713145 = 1284859) B1284859
theorem B3843227 : Blo 896573 3843227 := bstep (se 1 (by rfl) ⟨2882420, by rfl⟩ : syracuseStep 3843227 = 5764841) B5764841
theorem B3843449 : Blo 896573 3843449 := bstep (se 2 (by rfl) ⟨1441293, by rfl⟩ : syracuseStep 3843449 = 2882587) B2882587
theorem B5121407 : Blo 896573 5121407 := bstep (se 1 (by rfl) ⟨3841055, by rfl⟩ : syracuseStep 5121407 = 7682111) B7682111
theorem B2467255 : Blo 896573 2467255 := bstep (se 1 (by rfl) ⟨1850441, by rfl⟩ : syracuseStep 2467255 = 3700883) B3700883
theorem B2729627 : Blo 896573 2729627 := bstep (se 1 (by rfl) ⟨2047220, by rfl⟩ : syracuseStep 2729627 = 4094441) B4094441
theorem B3417947 : Blo 896573 3417947 := bstep (se 1 (by rfl) ⟨2563460, by rfl⟩ : syracuseStep 3417947 = 5126921) B5126921
theorem B3418919 : Blo 896573 3418919 := bstep (se 1 (by rfl) ⟨2564189, by rfl⟩ : syracuseStep 3418919 = 5128379) B5128379
theorem B7678799 : Blo 896573 7678799 := bstep (se 1 (by rfl) ⟨5759099, by rfl⟩ : syracuseStep 7678799 = 11518199) B11518199
theorem B5745491 : Blo 896573 5745491 := bstep (se 1 (by rfl) ⟨4309118, by rfl⟩ : syracuseStep 5745491 = 8618237) B8618237
theorem B4369747 : Blo 896573 4369747 := bstep (se 1 (by rfl) ⟨3277310, by rfl⟩ : syracuseStep 4369747 = 6554621) B6554621
theorem B896667 : Blo 896573 896667 := bstep (se 1 (by rfl) ⟨672500, by rfl⟩ : syracuseStep 896667 = 1345001) B1345001
theorem B1519391 : Blo 896573 1519391 := bstep (se 1 (by rfl) ⟨1139543, by rfl⟩ : syracuseStep 1519391 = 2279087) B2279087
theorem B896927 : Blo 896573 896927 := bstep (se 1 (by rfl) ⟨672695, by rfl⟩ : syracuseStep 896927 = 1345391) B1345391
theorem B897051 : Blo 896573 897051 := bstep (se 1 (by rfl) ⟨672788, by rfl⟩ : syracuseStep 897051 = 1345577) B1345577
theorem B897071 : Blo 896573 897071 := bstep (se 1 (by rfl) ⟨672803, by rfl⟩ : syracuseStep 897071 = 1345607) B1345607
theorem B3452975 : Blo 896573 3452975 := bstep (se 1 (by rfl) ⟨2589731, by rfl⟩ : syracuseStep 3452975 = 5179463) B5179463
theorem B897191 : Blo 896573 897191 := bstep (se 1 (by rfl) ⟨672893, by rfl⟩ : syracuseStep 897191 = 1345787) B1345787
theorem B31142141 : Blo 896573 31142141 := bstep (se 3 (by rfl) ⟨5839151, by rfl⟩ : syracuseStep 31142141 = 11678303) B11678303
theorem B897327 : Blo 896573 897327 := bstep (se 1 (by rfl) ⟨672995, by rfl⟩ : syracuseStep 897327 = 1345991) B1345991
theorem B6926639 : Blo 896573 6926639 := bstep (se 1 (by rfl) ⟨5194979, by rfl⟩ : syracuseStep 6926639 = 10389959) B10389959
theorem B1618255 : Blo 896573 1618255 := bstep (se 1 (by rfl) ⟨1213691, by rfl⟩ : syracuseStep 1618255 = 2427383) B2427383
theorem B3649961 : Blo 896573 3649961 := bstep (se 2 (by rfl) ⟨1368735, by rfl⟩ : syracuseStep 3649961 = 2737471) B2737471
theorem B7778749 : Blo 896573 7778749 := bstep (se 3 (by rfl) ⟨1458515, by rfl⟩ : syracuseStep 7778749 = 2917031) B2917031
theorem B897471 : Blo 896573 897471 := bstep (se 1 (by rfl) ⟨673103, by rfl⟩ : syracuseStep 897471 = 1346207) B1346207
theorem B897503 : Blo 896573 897503 := bstep (se 1 (by rfl) ⟨673127, by rfl⟩ : syracuseStep 897503 = 1346255) B1346255
theorem B897567 : Blo 896573 897567 := bstep (se 1 (by rfl) ⟨673175, by rfl⟩ : syracuseStep 897567 = 1346351) B1346351
theorem B897647 : Blo 896573 897647 := bstep (se 1 (by rfl) ⟨673235, by rfl⟩ : syracuseStep 897647 = 1346471) B1346471
theorem B897767 : Blo 896573 897767 := bstep (se 1 (by rfl) ⟨673325, by rfl⟩ : syracuseStep 897767 = 1346651) B1346651
theorem B897819 : Blo 896573 897819 := bstep (se 1 (by rfl) ⟨673364, by rfl⟩ : syracuseStep 897819 = 1346729) B1346729
theorem B898095 : Blo 896573 898095 := bstep (se 1 (by rfl) ⟨673571, by rfl⟩ : syracuseStep 898095 = 1347143) B1347143
theorem B898215 : Blo 896573 898215 := bstep (se 1 (by rfl) ⟨673661, by rfl⟩ : syracuseStep 898215 = 1347323) B1347323
theorem B3028157 : Blo 896573 3028157 := bstep (se 3 (by rfl) ⟨567779, by rfl⟩ : syracuseStep 3028157 = 1135559) B1135559
theorem B898375 : Blo 896573 898375 := bstep (se 1 (by rfl) ⟨673781, by rfl⟩ : syracuseStep 898375 = 1347563) B1347563
theorem B3749771 : Blo 896573 3749771 := bstep (se 1 (by rfl) ⟨2812328, by rfl⟩ : syracuseStep 3749771 = 5624657) B5624657
theorem B899067 : Blo 896573 899067 := bstep (se 1 (by rfl) ⟨674300, by rfl⟩ : syracuseStep 899067 = 1348601) B1348601
theorem B899199 : Blo 896573 899199 := bstep (se 1 (by rfl) ⟨674399, by rfl⟩ : syracuseStep 899199 = 1348799) B1348799
theorem B899295 : Blo 896573 899295 := bstep (se 1 (by rfl) ⟨674471, by rfl⟩ : syracuseStep 899295 = 1348943) B1348943
theorem B899355 : Blo 896573 899355 := bstep (se 1 (by rfl) ⟨674516, by rfl⟩ : syracuseStep 899355 = 1349033) B1349033
theorem B899391 : Blo 896573 899391 := bstep (se 1 (by rfl) ⟨674543, by rfl⟩ : syracuseStep 899391 = 1349087) B1349087
theorem B899455 : Blo 896573 899455 := bstep (se 1 (by rfl) ⟨674591, by rfl⟩ : syracuseStep 899455 = 1349183) B1349183
theorem B899775 : Blo 896573 899775 := bstep (se 1 (by rfl) ⟨674831, by rfl⟩ : syracuseStep 899775 = 1349663) B1349663
theorem B2276059 : Blo 896573 2276059 := bstep (se 1 (by rfl) ⟨1707044, by rfl⟩ : syracuseStep 2276059 = 3414089) B3414089
theorem B7682795 : Blo 896573 7682795 := bstep (se 1 (by rfl) ⟨5762096, by rfl⟩ : syracuseStep 7682795 = 11524193) B11524193
theorem B900063 : Blo 896573 900063 := bstep (se 1 (by rfl) ⟨675047, by rfl⟩ : syracuseStep 900063 = 1350095) B1350095
theorem B900123 : Blo 896573 900123 := bstep (se 1 (by rfl) ⟨675092, by rfl⟩ : syracuseStep 900123 = 1350185) B1350185
theorem B900263 : Blo 896573 900263 := bstep (se 1 (by rfl) ⟨675197, by rfl⟩ : syracuseStep 900263 = 1350395) B1350395
theorem B900347 : Blo 896573 900347 := bstep (se 1 (by rfl) ⟨675260, by rfl⟩ : syracuseStep 900347 = 1350521) B1350521
theorem B5127421 : Blo 896573 5127421 := bstep (se 3 (by rfl) ⟨961391, by rfl⟩ : syracuseStep 5127421 = 1922783) B1922783
theorem B59030957 : Blo 896573 59030957 := bstep (se 3 (by rfl) ⟨11068304, by rfl⟩ : syracuseStep 59030957 = 22136609) B22136609
theorem B2277031 : Blo 896573 2277031 := bstep (se 1 (by rfl) ⟨1707773, by rfl⟩ : syracuseStep 2277031 = 3415547) B3415547
theorem B11517835 : Blo 896573 11517835 := bstep (se 1 (by rfl) ⟨8638376, by rfl⟩ : syracuseStep 11517835 = 17276753) B17276753
theorem B14565329 : Blo 896573 14565329 := bstep (se 2 (by rfl) ⟨5461998, by rfl⟩ : syracuseStep 14565329 = 10923997) B10923997
theorem B2277497 : Blo 896573 2277497 := bstep (se 2 (by rfl) ⟨854061, by rfl⟩ : syracuseStep 2277497 = 1708123) B1708123
theorem B3031343 : Blo 896573 3031343 := bstep (se 1 (by rfl) ⟨2273507, by rfl⟩ : syracuseStep 3031343 = 4547015) B4547015
theorem B5194057 : Blo 896573 5194057 := bstep (se 2 (by rfl) ⟨1947771, by rfl⟩ : syracuseStep 5194057 = 3895543) B3895543
theorem B2277791 : Blo 896573 2277791 := bstep (se 1 (by rfl) ⟨1708343, by rfl⟩ : syracuseStep 2277791 = 3416687) B3416687
theorem B1622747 : Blo 896573 1622747 := bstep (se 1 (by rfl) ⟨1217060, by rfl⟩ : syracuseStep 1622747 = 2434121) B2434121
theorem B14566499 : Blo 896573 14566499 := bstep (se 1 (by rfl) ⟨10924874, by rfl⟩ : syracuseStep 14566499 = 21849749) B21849749
theorem B20792477 : Blo 896573 20792477 := bstep (se 3 (by rfl) ⟨3898589, by rfl⟩ : syracuseStep 20792477 = 7797179) B7797179
theorem B11519171 : Blo 896573 11519171 := bstep (se 1 (by rfl) ⟨8639378, by rfl⟩ : syracuseStep 11519171 = 17278757) B17278757
theorem B4867391 : Blo 896573 4867391 := bstep (se 1 (by rfl) ⟨3650543, by rfl⟩ : syracuseStep 4867391 = 7301087) B7301087
theorem B3032423 : Blo 896573 3032423 := bstep (se 1 (by rfl) ⟨2274317, by rfl⟩ : syracuseStep 3032423 = 4548635) B4548635
theorem B7390939 : Blo 896573 7390939 := bstep (se 1 (by rfl) ⟨5543204, by rfl⟩ : syracuseStep 7390939 = 11086409) B11086409
theorem B98158301 : Blo 896573 98158301 := bstep (se 3 (by rfl) ⟨18404681, by rfl⟩ : syracuseStep 98158301 = 36809363) B36809363
theorem B5195531 : Blo 896573 5195531 := bstep (se 1 (by rfl) ⟨3896648, by rfl⟩ : syracuseStep 5195531 = 7793297) B7793297
theorem B2017403 : Blo 896573 2017403 := bstep (se 1 (by rfl) ⟨1513052, by rfl⟩ : syracuseStep 2017403 = 3026105) B3026105
theorem B2017511 : Blo 896573 2017511 := bstep (se 1 (by rfl) ⟨1513133, by rfl⟩ : syracuseStep 2017511 = 3026267) B3026267
theorem B3033935 : Blo 896573 3033935 := bstep (se 1 (by rfl) ⟨2275451, by rfl⟩ : syracuseStep 3033935 = 4550903) B4550903
theorem B22989743 : Blo 896573 22989743 := bstep (se 1 (by rfl) ⟨17242307, by rfl⟩ : syracuseStep 22989743 = 34484615) B34484615
theorem B32820173 : Blo 896573 32820173 := bstep (se 3 (by rfl) ⟨6153782, by rfl⟩ : syracuseStep 32820173 = 12307565) B12307565
theorem B15322121 : Blo 896573 15322121 := bstep (se 2 (by rfl) ⟨5745795, by rfl⟩ : syracuseStep 15322121 = 11491591) B11491591
theorem B2018843 : Blo 896573 2018843 := bstep (se 1 (by rfl) ⟨1514132, by rfl⟩ : syracuseStep 2018843 = 3028265) B3028265
theorem B2019041 : Blo 896573 2019041 := bstep (se 2 (by rfl) ⟨757140, by rfl⟩ : syracuseStep 2019041 = 1514281) B1514281
theorem B7688195 : Blo 896573 7688195 := bstep (se 1 (by rfl) ⟨5766146, by rfl⟩ : syracuseStep 7688195 = 11532293) B11532293
theorem B2019401 : Blo 896573 2019401 := bstep (se 2 (by rfl) ⟨757275, by rfl⟩ : syracuseStep 2019401 = 1514551) B1514551
theorem B3036905 : Blo 896573 3036905 := bstep (se 2 (by rfl) ⟨1138839, by rfl⟩ : syracuseStep 3036905 = 2277679) B2277679
theorem B7296911 : Blo 896573 7296911 := bstep (se 1 (by rfl) ⟨5472683, by rfl⟩ : syracuseStep 7296911 = 10945367) B10945367
theorem B3037175 : Blo 896573 3037175 := bstep (se 1 (by rfl) ⟨2277881, by rfl⟩ : syracuseStep 3037175 = 4555763) B4555763
theorem B2021417 : Blo 896573 2021417 := bstep (se 2 (by rfl) ⟨758031, by rfl⟩ : syracuseStep 2021417 = 1516063) B1516063
theorem B49207499 : Blo 896573 49207499 := bstep (se 1 (by rfl) ⟨36905624, by rfl⟩ : syracuseStep 49207499 = 73811249) B73811249
theorem B3070187 : Blo 896573 3070187 := bstep (se 1 (by rfl) ⟨2302640, by rfl⟩ : syracuseStep 3070187 = 4605281) B4605281
theorem B3037931 : Blo 896573 3037931 := bstep (se 1 (by rfl) ⟨2278448, by rfl⟩ : syracuseStep 3037931 = 4556897) B4556897
theorem B3038255 : Blo 896573 3038255 := bstep (se 1 (by rfl) ⟨2278691, by rfl⟩ : syracuseStep 3038255 = 4557383) B4557383
theorem B3038363 : Blo 896573 3038363 := bstep (se 1 (by rfl) ⟨2278772, by rfl⟩ : syracuseStep 3038363 = 4557545) B4557545
theorem B3038849 : Blo 896573 3038849 := bstep (se 2 (by rfl) ⟨1139568, by rfl⟩ : syracuseStep 3038849 = 2279137) B2279137
theorem B1367689 : Blo 896573 1367689 := bstep (se 2 (by rfl) ⟨512883, by rfl⟩ : syracuseStep 1367689 = 1025767) B1025767
theorem B4546367 : Blo 896573 4546367 := bstep (se 1 (by rfl) ⟨3409775, by rfl⟩ : syracuseStep 4546367 = 6819551) B6819551
theorem B3039335 : Blo 896573 3039335 := bstep (se 1 (by rfl) ⟨2279501, by rfl⟩ : syracuseStep 3039335 = 4559003) B4559003
theorem B2023721 : Blo 896573 2023721 := bstep (se 2 (by rfl) ⟨758895, by rfl⟩ : syracuseStep 2023721 = 1517791) B1517791
theorem B910171 : Blo 896573 910171 := bstep (se 1 (by rfl) ⟨682628, by rfl⟩ : syracuseStep 910171 = 1365257) B1365257
theorem B2876411 : Blo 896573 2876411 := bstep (se 1 (by rfl) ⟨2157308, by rfl⟩ : syracuseStep 2876411 = 4314617) B4314617
theorem B2025755 : Blo 896573 2025755 := bstep (se 1 (by rfl) ⟨1519316, by rfl⟩ : syracuseStep 2025755 = 3038633) B3038633
theorem B7661951 : Blo 896573 7661951 := bstep (se 1 (by rfl) ⟨5746463, by rfl⟩ : syracuseStep 7661951 = 11492927) B11492927
theorem B5990923 : Blo 896573 5990923 := bstep (se 1 (by rfl) ⟨4493192, by rfl⟩ : syracuseStep 5990923 = 8986385) B8986385
theorem B19720829 : Blo 896573 19720829 := bstep (se 3 (by rfl) ⟨3697655, by rfl⟩ : syracuseStep 19720829 = 7395311) B7395311
theorem B1437167 : Blo 896573 1437167 := bstep (se 1 (by rfl) ⟨1077875, by rfl⟩ : syracuseStep 1437167 = 2155751) B2155751
theorem B5107283 : Blo 896573 5107283 := bstep (se 1 (by rfl) ⟨3830462, by rfl⟩ : syracuseStep 5107283 = 7660925) B7660925
theorem B1011487 : Blo 896573 1011487 := bstep (se 1 (by rfl) ⟨758615, by rfl⟩ : syracuseStep 1011487 = 1517231) B1517231
theorem B3503209 : Blo 896573 3503209 := bstep (se 2 (by rfl) ⟨1313703, by rfl⟩ : syracuseStep 3503209 = 2627407) B2627407
theorem B3241225 : Blo 896573 3241225 := bstep (se 2 (by rfl) ⟨1215459, by rfl⟩ : syracuseStep 3241225 = 2430919) B2430919
theorem B2554735 : Blo 896573 2554735 := bstep (se 1 (by rfl) ⟨1916051, by rfl⟩ : syracuseStep 2554735 = 3832103) B3832103
theorem B1702777 : Blo 896573 1702777 := bstep (se 2 (by rfl) ⟨638541, by rfl⟩ : syracuseStep 1702777 = 1277083) B1277083
theorem B1703119 : Blo 896573 1703119 := bstep (se 1 (by rfl) ⟨1277339, by rfl⟩ : syracuseStep 1703119 = 2554679) B2554679
theorem B4553981 : Blo 896573 4553981 := bstep (se 3 (by rfl) ⟨853871, by rfl⟩ : syracuseStep 4553981 = 1707743) B1707743
theorem B1441127 : Blo 896573 1441127 := bstep (se 1 (by rfl) ⟨1080845, by rfl⟩ : syracuseStep 1441127 = 2161691) B2161691
theorem B1539631 : Blo 896573 1539631 := bstep (se 1 (by rfl) ⟨1154723, by rfl⟩ : syracuseStep 1539631 = 2309447) B2309447
theorem B3407771 : Blo 896573 3407771 := bstep (se 1 (by rfl) ⟨2555828, by rfl⟩ : syracuseStep 3407771 = 5111657) B5111657
theorem B1081831 : Blo 896573 1081831 := bstep (se 1 (by rfl) ⟨811373, by rfl⟩ : syracuseStep 1081831 = 1622747) B1622747
theorem B13861651 : Blo 896573 13861651 := bstep (se 1 (by rfl) ⟨10396238, by rfl⟩ : syracuseStep 13861651 = 20792477) B20792477
theorem B5112841 : Blo 896573 5112841 := bstep (se 2 (by rfl) ⟨1917315, by rfl⟩ : syracuseStep 5112841 = 3834631) B3834631
theorem B9733229 : Blo 896573 9733229 := bstep (se 3 (by rfl) ⟨1824980, by rfl⟩ : syracuseStep 9733229 = 3649961) B3649961
theorem B1213561 : Blo 896573 1213561 := bstep (se 2 (by rfl) ⟨455085, by rfl⟩ : syracuseStep 1213561 = 910171) B910171
theorem B65438867 : Blo 896573 65438867 := bstep (se 1 (by rfl) ⟨49079150, by rfl⟩ : syracuseStep 65438867 = 98158301) B98158301
theorem B10224953 : Blo 896573 10224953 := bstep (se 2 (by rfl) ⟨3834357, by rfl⟩ : syracuseStep 10224953 = 7668715) B7668715
theorem B1344935 : Blo 896573 1344935 := bstep (se 1 (by rfl) ⟨1008701, by rfl⟩ : syracuseStep 1344935 = 2017403) B2017403
theorem B1345007 : Blo 896573 1345007 := bstep (se 1 (by rfl) ⟨1008755, by rfl⟩ : syracuseStep 1345007 = 2017511) B2017511
theorem B1705799 : Blo 896573 1705799 := bstep (se 1 (by rfl) ⟨1279349, by rfl⟩ : syracuseStep 1705799 = 2558699) B2558699
theorem B17237933 : Blo 896573 17237933 := bstep (se 3 (by rfl) ⟨3232112, by rfl⟩ : syracuseStep 17237933 = 6464225) B6464225
theorem B1345895 : Blo 896573 1345895 := bstep (se 1 (by rfl) ⟨1009421, by rfl⟩ : syracuseStep 1345895 = 2018843) B2018843
theorem B1346027 : Blo 896573 1346027 := bstep (se 1 (by rfl) ⟨1009520, by rfl⟩ : syracuseStep 1346027 = 2019041) B2019041
theorem B1346267 : Blo 896573 1346267 := bstep (se 1 (by rfl) ⟨1009700, by rfl⟩ : syracuseStep 1346267 = 2019401) B2019401
theorem B10226411 : Blo 896573 10226411 := bstep (se 1 (by rfl) ⟨7669808, by rfl⟩ : syracuseStep 10226411 = 15339617) B15339617
theorem B27626629 : Blo 896573 27626629 := bstep (se 4 (by rfl) ⟨2589996, by rfl⟩ : syracuseStep 27626629 = 5179993) B5179993
theorem B12979709 : Blo 896573 12979709 := bstep (se 3 (by rfl) ⟨2433695, by rfl⟩ : syracuseStep 12979709 = 4867391) B4867391
theorem B5836511 : Blo 896573 5836511 := bstep (se 1 (by rfl) ⟨4377383, by rfl⟩ : syracuseStep 5836511 = 8754767) B8754767
theorem B1347611 : Blo 896573 1347611 := bstep (se 1 (by rfl) ⟨1010708, by rfl⟩ : syracuseStep 1347611 = 2021417) B2021417
theorem B32804999 : Blo 896573 32804999 := bstep (se 1 (by rfl) ⟨24603749, by rfl⟩ : syracuseStep 32804999 = 49207499) B49207499
theorem B9999389 : Blo 896573 9999389 := bstep (se 3 (by rfl) ⟨1874885, by rfl⟩ : syracuseStep 9999389 = 3749771) B3749771
theorem B1348649 : Blo 896573 1348649 := bstep (se 2 (by rfl) ⟨505743, by rfl⟩ : syracuseStep 1348649 = 1011487) B1011487
theorem B5117033 : Blo 896573 5117033 := bstep (se 2 (by rfl) ⟨1918887, by rfl⟩ : syracuseStep 5117033 = 3837775) B3837775
theorem B1349147 : Blo 896573 1349147 := bstep (se 1 (by rfl) ⟨1011860, by rfl⟩ : syracuseStep 1349147 = 2023721) B2023721
theorem B2562151 : Blo 896573 2562151 := bstep (se 1 (by rfl) ⟨1921613, by rfl⟩ : syracuseStep 2562151 = 3843227) B3843227
theorem B2562299 : Blo 896573 2562299 := bstep (se 1 (by rfl) ⟨1921724, by rfl⟩ : syracuseStep 2562299 = 3843449) B3843449
theorem B3414271 : Blo 896573 3414271 := bstep (se 1 (by rfl) ⟨2560703, by rfl⟩ : syracuseStep 3414271 = 5121407) B5121407
theorem B1350503 : Blo 896573 1350503 := bstep (se 1 (by rfl) ⟨1012877, by rfl⟩ : syracuseStep 1350503 = 2025755) B2025755
theorem B36838273 : Blo 896573 36838273 := bstep (se 2 (by rfl) ⟨13814352, by rfl⟩ : syracuseStep 36838273 = 27628705) B27628705
theorem B13147219 : Blo 896573 13147219 := bstep (se 1 (by rfl) ⟨9860414, by rfl⟩ : syracuseStep 13147219 = 19720829) B19720829
theorem B5119199 : Blo 896573 5119199 := bstep (se 1 (by rfl) ⟨3839399, by rfl⟩ : syracuseStep 5119199 = 7678799) B7678799
theorem B958111 : Blo 896573 958111 := bstep (se 1 (by rfl) ⟨718583, by rfl⟩ : syracuseStep 958111 = 1437167) B1437167
theorem B2301983 : Blo 896573 2301983 := bstep (se 1 (by rfl) ⟨1726487, by rfl⟩ : syracuseStep 2301983 = 3452975) B3452975
theorem B2270369 : Blo 896573 2270369 := bstep (se 2 (by rfl) ⟨851388, by rfl⟩ : syracuseStep 2270369 = 1702777) B1702777
theorem B1844489 : Blo 896573 1844489 := bstep (se 2 (by rfl) ⟨691683, by rfl⟩ : syracuseStep 1844489 = 1383367) B1383367
theorem B2270825 : Blo 896573 2270825 := bstep (se 2 (by rfl) ⟨851559, by rfl⟩ : syracuseStep 2270825 = 1703119) B1703119
theorem B5121863 : Blo 896573 5121863 := bstep (se 1 (by rfl) ⟨3841397, by rfl⟩ : syracuseStep 5121863 = 7682795) B7682795
theorem B960751 : Blo 896573 960751 := bstep (se 1 (by rfl) ⟨720563, by rfl⟩ : syracuseStep 960751 = 1441127) B1441127
theorem B2271847 : Blo 896573 2271847 := bstep (se 1 (by rfl) ⟨1703885, by rfl⟩ : syracuseStep 2271847 = 3407771) B3407771
theorem B9710219 : Blo 896573 9710219 := bstep (se 1 (by rfl) ⟨7282664, by rfl⟩ : syracuseStep 9710219 = 14565329) B14565329
theorem B1518331 : Blo 896573 1518331 := bstep (se 1 (by rfl) ⟨1138748, by rfl⟩ : syracuseStep 1518331 = 2277497) B2277497
theorem B1518527 : Blo 896573 1518527 := bstep (se 1 (by rfl) ⟨1138895, by rfl⟩ : syracuseStep 1518527 = 2277791) B2277791
theorem B2272283 : Blo 896573 2272283 := bstep (se 1 (by rfl) ⟨1704212, by rfl⟩ : syracuseStep 2272283 = 3408425) B3408425
theorem B6925409 : Blo 896573 6925409 := bstep (se 2 (by rfl) ⟨2597028, by rfl⟩ : syracuseStep 6925409 = 5194057) B5194057
theorem B9710999 : Blo 896573 9710999 := bstep (se 1 (by rfl) ⟨7283249, by rfl⟩ : syracuseStep 9710999 = 14566499) B14566499
theorem B7679447 : Blo 896573 7679447 := bstep (se 1 (by rfl) ⟨5759585, by rfl⟩ : syracuseStep 7679447 = 11519171) B11519171
theorem B2273255 : Blo 896573 2273255 := bstep (se 1 (by rfl) ⟨1704941, by rfl⟩ : syracuseStep 2273255 = 3409883) B3409883
theorem B897055 : Blo 896573 897055 := bstep (se 1 (by rfl) ⟨672791, by rfl⟩ : syracuseStep 897055 = 1345583) B1345583
theorem B22720675 : Blo 896573 22720675 := bstep (se 1 (by rfl) ⟨17040506, by rfl⟩ : syracuseStep 22720675 = 34081013) B34081013
theorem B2273771 : Blo 896573 2273771 := bstep (se 1 (by rfl) ⟨1705328, by rfl⟩ : syracuseStep 2273771 = 3410657) B3410657
theorem B897535 : Blo 896573 897535 := bstep (se 1 (by rfl) ⟨673151, by rfl⟩ : syracuseStep 897535 = 1346303) B1346303
theorem B3289673 : Blo 896573 3289673 := bstep (se 2 (by rfl) ⟨1233627, by rfl⟩ : syracuseStep 3289673 = 2467255) B2467255
theorem B10924733 : Blo 896573 10924733 := bstep (se 3 (by rfl) ⟨2048387, by rfl⟩ : syracuseStep 10924733 = 4096775) B4096775
theorem B898159 : Blo 896573 898159 := bstep (se 1 (by rfl) ⟨673619, by rfl⟩ : syracuseStep 898159 = 1347239) B1347239
theorem B898239 : Blo 896573 898239 := bstep (se 1 (by rfl) ⟨673679, by rfl⟩ : syracuseStep 898239 = 1347359) B1347359
theorem B898271 : Blo 896573 898271 := bstep (se 1 (by rfl) ⟨673703, by rfl⟩ : syracuseStep 898271 = 1347407) B1347407
theorem B898351 : Blo 896573 898351 := bstep (se 1 (by rfl) ⟨673763, by rfl⟩ : syracuseStep 898351 = 1347527) B1347527
theorem B5125463 : Blo 896573 5125463 := bstep (se 1 (by rfl) ⟨3844097, by rfl⟩ : syracuseStep 5125463 = 7688195) B7688195
theorem B898511 : Blo 896573 898511 := bstep (se 1 (by rfl) ⟨673883, by rfl⟩ : syracuseStep 898511 = 1347767) B1347767
theorem B898559 : Blo 896573 898559 := bstep (se 1 (by rfl) ⟨673919, by rfl⟩ : syracuseStep 898559 = 1347839) B1347839
theorem B898591 : Blo 896573 898591 := bstep (se 1 (by rfl) ⟨673943, by rfl⟩ : syracuseStep 898591 = 1347887) B1347887
theorem B898751 : Blo 896573 898751 := bstep (se 1 (by rfl) ⟨674063, by rfl⟩ : syracuseStep 898751 = 1348127) B1348127
theorem B898791 : Blo 896573 898791 := bstep (se 1 (by rfl) ⟨674093, by rfl⟩ : syracuseStep 898791 = 1348187) B1348187
theorem B898927 : Blo 896573 898927 := bstep (se 1 (by rfl) ⟨674195, by rfl⟩ : syracuseStep 898927 = 1348391) B1348391
theorem B899039 : Blo 896573 899039 := bstep (se 1 (by rfl) ⟨674279, by rfl⟩ : syracuseStep 899039 = 1348559) B1348559
theorem B16365563 : Blo 896573 16365563 := bstep (se 1 (by rfl) ⟨12274172, by rfl⟩ : syracuseStep 16365563 = 24548345) B24548345
theorem B899119 : Blo 896573 899119 := bstep (se 1 (by rfl) ⟨674339, by rfl⟩ : syracuseStep 899119 = 1348679) B1348679
theorem B899239 : Blo 896573 899239 := bstep (se 1 (by rfl) ⟨674429, by rfl⟩ : syracuseStep 899239 = 1348859) B1348859
theorem B899279 : Blo 896573 899279 := bstep (se 1 (by rfl) ⟨674459, by rfl⟩ : syracuseStep 899279 = 1348919) B1348919
theorem B899327 : Blo 896573 899327 := bstep (se 1 (by rfl) ⟨674495, by rfl⟩ : syracuseStep 899327 = 1348991) B1348991
theorem B9615631 : Blo 896573 9615631 := bstep (se 1 (by rfl) ⟨7211723, by rfl⟩ : syracuseStep 9615631 = 14423447) B14423447
theorem B899483 : Blo 896573 899483 := bstep (se 1 (by rfl) ⟨674612, by rfl⟩ : syracuseStep 899483 = 1349225) B1349225
theorem B4864607 : Blo 896573 4864607 := bstep (se 1 (by rfl) ⟨3648455, by rfl⟩ : syracuseStep 4864607 = 7296911) B7296911
theorem B899839 : Blo 896573 899839 := bstep (se 1 (by rfl) ⟨674879, by rfl⟩ : syracuseStep 899839 = 1349759) B1349759
theorem B16628503 : Blo 896573 16628503 := bstep (se 1 (by rfl) ⟨12471377, by rfl⟩ : syracuseStep 16628503 = 24942755) B24942755
theorem B2046791 : Blo 896573 2046791 := bstep (se 1 (by rfl) ⟨1535093, by rfl⟩ : syracuseStep 2046791 = 3070187) B3070187
theorem B900251 : Blo 896573 900251 := bstep (se 1 (by rfl) ⟨675188, by rfl⟩ : syracuseStep 900251 = 1350377) B1350377
theorem B3030911 : Blo 896573 3030911 := bstep (se 1 (by rfl) ⟨2273183, by rfl⟩ : syracuseStep 3030911 = 4546367) B4546367
theorem B1622119 : Blo 896573 1622119 := bstep (se 1 (by rfl) ⟨1216589, by rfl⟩ : syracuseStep 1622119 = 2433179) B2433179
theorem B10371665 : Blo 896573 10371665 := bstep (se 2 (by rfl) ⟨3889374, by rfl⟩ : syracuseStep 10371665 = 7778749) B7778749
theorem B1917607 : Blo 896573 1917607 := bstep (se 1 (by rfl) ⟨1438205, by rfl⟩ : syracuseStep 1917607 = 2876411) B2876411
theorem B1819751 : Blo 896573 1819751 := bstep (se 1 (by rfl) ⟨1364813, by rfl⟩ : syracuseStep 1819751 = 2729627) B2729627
theorem B2278631 : Blo 896573 2278631 := bstep (se 1 (by rfl) ⟨1708973, by rfl⟩ : syracuseStep 2278631 = 3417947) B3417947
theorem B4670945 : Blo 896573 4670945 := bstep (se 2 (by rfl) ⟨1751604, by rfl⟩ : syracuseStep 4670945 = 3503209) B3503209
theorem B2279279 : Blo 896573 2279279 := bstep (se 1 (by rfl) ⟨1709459, by rfl⟩ : syracuseStep 2279279 = 3418919) B3418919
theorem B6474401 : Blo 896573 6474401 := bstep (se 2 (by rfl) ⟨2427900, by rfl⟩ : syracuseStep 6474401 = 4855801) B4855801
theorem B20761427 : Blo 896573 20761427 := bstep (se 1 (by rfl) ⟨15571070, by rfl⟩ : syracuseStep 20761427 = 31142141) B31142141
theorem B8211365 : Blo 896573 8211365 := bstep (se 4 (by rfl) ⟨769815, by rfl⟩ : syracuseStep 8211365 = 1539631) B1539631
theorem B2018771 : Blo 896573 2018771 := bstep (se 1 (by rfl) ⟨1514078, by rfl⟩ : syracuseStep 2018771 = 3028157) B3028157
theorem B6475297 : Blo 896573 6475297 := bstep (se 2 (by rfl) ⟨2428236, by rfl⟩ : syracuseStep 6475297 = 4856473) B4856473
theorem B3034745 : Blo 896573 3034745 := bstep (se 2 (by rfl) ⟨1138029, by rfl⟩ : syracuseStep 3034745 = 2276059) B2276059
theorem B6836561 : Blo 896573 6836561 := bstep (se 2 (by rfl) ⟨2563710, by rfl⟩ : syracuseStep 6836561 = 5127421) B5127421
theorem B3035987 : Blo 896573 3035987 := bstep (se 1 (by rfl) ⟨2276990, by rfl⟩ : syracuseStep 3035987 = 4553981) B4553981
theorem B1823585 : Blo 896573 1823585 := bstep (se 2 (by rfl) ⟨683844, by rfl⟩ : syracuseStep 1823585 = 1367689) B1367689
theorem B3036041 : Blo 896573 3036041 := bstep (se 2 (by rfl) ⟨1138515, by rfl⟩ : syracuseStep 3036041 = 2277031) B2277031
theorem B2020265 : Blo 896573 2020265 := bstep (se 2 (by rfl) ⟨757599, by rfl⟩ : syracuseStep 2020265 = 1515199) B1515199
theorem B15357113 : Blo 896573 15357113 := bstep (se 2 (by rfl) ⟨5758917, by rfl⟩ : syracuseStep 15357113 = 11517835) B11517835
theorem B2020895 : Blo 896573 2020895 := bstep (se 1 (by rfl) ⟨1515671, by rfl⟩ : syracuseStep 2020895 = 3031343) B3031343
theorem B7296743 : Blo 896573 7296743 := bstep (se 1 (by rfl) ⟨5472557, by rfl⟩ : syracuseStep 7296743 = 10945115) B10945115
theorem B18471037 : Blo 896573 18471037 := bstep (se 3 (by rfl) ⟨3463319, by rfl⟩ : syracuseStep 18471037 = 6926639) B6926639
theorem B2021615 : Blo 896573 2021615 := bstep (se 1 (by rfl) ⟨1516211, by rfl⟩ : syracuseStep 2021615 = 3032423) B3032423
theorem B3463687 : Blo 896573 3463687 := bstep (se 1 (by rfl) ⟨2597765, by rfl⟩ : syracuseStep 3463687 = 5195531) B5195531
theorem B2284193 : Blo 896573 2284193 := bstep (se 2 (by rfl) ⟨856572, by rfl⟩ : syracuseStep 2284193 = 1713145) B1713145
theorem B2022623 : Blo 896573 2022623 := bstep (se 1 (by rfl) ⟨1516967, by rfl⟩ : syracuseStep 2022623 = 3033935) B3033935
theorem B15326495 : Blo 896573 15326495 := bstep (se 1 (by rfl) ⟨11494871, by rfl⟩ : syracuseStep 15326495 = 22989743) B22989743
theorem B21880115 : Blo 896573 21880115 := bstep (se 1 (by rfl) ⟨16410086, by rfl⟩ : syracuseStep 21880115 = 32820173) B32820173
theorem B10214747 : Blo 896573 10214747 := bstep (se 1 (by rfl) ⟨7661060, by rfl⟩ : syracuseStep 10214747 = 15322121) B15322121
theorem B9854585 : Blo 896573 9854585 := bstep (se 2 (by rfl) ⟨3695469, by rfl⟩ : syracuseStep 9854585 = 7390939) B7390939
theorem B7987897 : Blo 896573 7987897 := bstep (se 2 (by rfl) ⟨2995461, by rfl⟩ : syracuseStep 7987897 = 5990923) B5990923
theorem B2024603 : Blo 896573 2024603 := bstep (se 1 (by rfl) ⟨1518452, by rfl⟩ : syracuseStep 2024603 = 3036905) B3036905
theorem B1008967 : Blo 896573 1008967 := bstep (se 1 (by rfl) ⟨756725, by rfl⟩ : syracuseStep 1008967 = 1513451) B1513451
theorem B2024783 : Blo 896573 2024783 := bstep (se 1 (by rfl) ⟨1518587, by rfl⟩ : syracuseStep 2024783 = 3037175) B3037175
theorem B5826329 : Blo 896573 5826329 := bstep (se 2 (by rfl) ⟨2184873, by rfl⟩ : syracuseStep 5826329 = 4369747) B4369747
theorem B2025287 : Blo 896573 2025287 := bstep (se 1 (by rfl) ⟨1518965, by rfl⟩ : syracuseStep 2025287 = 3037931) B3037931
theorem B2025503 : Blo 896573 2025503 := bstep (se 1 (by rfl) ⟨1519127, by rfl⟩ : syracuseStep 2025503 = 3038255) B3038255
theorem B2025575 : Blo 896573 2025575 := bstep (se 1 (by rfl) ⟨1519181, by rfl⟩ : syracuseStep 2025575 = 3038363) B3038363
theorem B2025899 : Blo 896573 2025899 := bstep (se 1 (by rfl) ⟨1519424, by rfl⟩ : syracuseStep 2025899 = 3038849) B3038849
theorem B2026223 : Blo 896573 2026223 := bstep (se 1 (by rfl) ⟨1519667, by rfl⟩ : syracuseStep 2026223 = 3039335) B3039335
theorem B3238643 : Blo 896573 3238643 := bstep (se 1 (by rfl) ⟨2428982, by rfl⟩ : syracuseStep 3238643 = 4857965) B4857965
theorem B4549607 : Blo 896573 4549607 := bstep (se 1 (by rfl) ⟨3412205, by rfl⟩ : syracuseStep 4549607 = 6824411) B6824411
theorem B2157673 : Blo 896573 2157673 := bstep (se 2 (by rfl) ⟨809127, by rfl⟩ : syracuseStep 2157673 = 1618255) B1618255
theorem B4549769 : Blo 896573 4549769 := bstep (se 2 (by rfl) ⟨1706163, by rfl⟩ : syracuseStep 4549769 = 3412327) B3412327
theorem B5107967 : Blo 896573 5107967 := bstep (se 1 (by rfl) ⟨3830975, by rfl⟩ : syracuseStep 5107967 = 7661951) B7661951
theorem B4321633 : Blo 896573 4321633 := bstep (se 2 (by rfl) ⟨1620612, by rfl⟩ : syracuseStep 4321633 = 3241225) B3241225
theorem B3830327 : Blo 896573 3830327 := bstep (se 1 (by rfl) ⟨2872745, by rfl⟩ : syracuseStep 3830327 = 5745491) B5745491
theorem B3404855 : Blo 896573 3404855 := bstep (se 1 (by rfl) ⟨2553641, by rfl⟩ : syracuseStep 3404855 = 5107283) B5107283
theorem B1012927 : Blo 896573 1012927 := bstep (se 1 (by rfl) ⟨759695, by rfl⟩ : syracuseStep 1012927 = 1519391) B1519391
theorem B3406313 : Blo 896573 3406313 := bstep (se 2 (by rfl) ⟨1277367, by rfl⟩ : syracuseStep 3406313 = 2554735) B2554735
theorem B39353971 : Blo 896573 39353971 := bstep (se 1 (by rfl) ⟨29515478, by rfl⟩ : syracuseStep 39353971 = 59030957) B59030957
theorem B2162825 : Blo 896573 2162825 := bstep (se 2 (by rfl) ⟨811059, by rfl⟩ : syracuseStep 2162825 = 1622119) B1622119
theorem B6914443 : Blo 896573 6914443 := bstep (se 1 (by rfl) ⟨5185832, by rfl⟩ : syracuseStep 6914443 = 10371665) B10371665
theorem B1442441 : Blo 896573 1442441 := bstep (se 2 (by rfl) ⟨540915, by rfl⟩ : syracuseStep 1442441 = 1081831) B1081831
theorem B6488819 : Blo 896573 6488819 := bstep (se 1 (by rfl) ⟨4866614, by rfl⟩ : syracuseStep 6488819 = 9733229) B9733229
theorem B6816635 : Blo 896573 6816635 := bstep (se 1 (by rfl) ⟨5112476, by rfl⟩ : syracuseStep 6816635 = 10224953) B10224953
theorem B2556809 : Blo 896573 2556809 := bstep (se 2 (by rfl) ⟨958803, by rfl⟩ : syracuseStep 2556809 = 1917607) B1917607
theorem B10650529 : Blo 896573 10650529 := bstep (se 2 (by rfl) ⟨3993948, by rfl⟩ : syracuseStep 10650529 = 7987897) B7987897
theorem B3113963 : Blo 896573 3113963 := bstep (se 1 (by rfl) ⟨2335472, by rfl⟩ : syracuseStep 3113963 = 4670945) B4670945
theorem B18482201 : Blo 896573 18482201 := bstep (se 2 (by rfl) ⟨6930825, by rfl⟩ : syracuseStep 18482201 = 13861651) B13861651
theorem B6817121 : Blo 896573 6817121 := bstep (se 2 (by rfl) ⟨2556420, by rfl⟩ : syracuseStep 6817121 = 5112841) B5112841
theorem B1345289 : Blo 896573 1345289 := bstep (se 2 (by rfl) ⟨504483, by rfl⟩ : syracuseStep 1345289 = 1008967) B1008967
theorem B6817607 : Blo 896573 6817607 := bstep (se 1 (by rfl) ⟨5113205, by rfl⟩ : syracuseStep 6817607 = 10226411) B10226411
theorem B5474243 : Blo 896573 5474243 := bstep (se 1 (by rfl) ⟨4105682, by rfl⟩ : syracuseStep 5474243 = 8211365) B8211365
theorem B1345847 : Blo 896573 1345847 := bstep (se 1 (by rfl) ⟨1009385, by rfl⟩ : syracuseStep 1345847 = 2018771) B2018771
theorem B8653139 : Blo 896573 8653139 := bstep (se 1 (by rfl) ⟨6489854, by rfl⟩ : syracuseStep 8653139 = 12979709) B12979709
theorem B4557707 : Blo 896573 4557707 := bstep (se 1 (by rfl) ⟨3418280, by rfl⟩ : syracuseStep 4557707 = 6836561) B6836561
theorem B4852669 : Blo 896573 4852669 := bstep (se 3 (by rfl) ⟨909875, by rfl⟩ : syracuseStep 4852669 = 1819751) B1819751
theorem B1346843 : Blo 896573 1346843 := bstep (se 1 (by rfl) ⟨1010132, by rfl⟩ : syracuseStep 1346843 = 2020265) B2020265
theorem B4918637 : Blo 896573 4918637 := bstep (se 3 (by rfl) ⟨922244, by rfl⟩ : syracuseStep 4918637 = 1844489) B1844489
theorem B3411355 : Blo 896573 3411355 := bstep (se 1 (by rfl) ⟨2558516, by rfl⟩ : syracuseStep 3411355 = 5117033) B5117033
theorem B1347263 : Blo 896573 1347263 := bstep (se 1 (by rfl) ⟨1010447, by rfl⟩ : syracuseStep 1347263 = 2020895) B2020895
theorem B1347743 : Blo 896573 1347743 := bstep (se 1 (by rfl) ⟨1010807, by rfl⟩ : syracuseStep 1347743 = 2021615) B2021615
theorem B1708199 : Blo 896573 1708199 := bstep (se 1 (by rfl) ⟨1281149, by rfl⟩ : syracuseStep 1708199 = 2562299) B2562299
theorem B36835505 : Blo 896573 36835505 := bstep (se 2 (by rfl) ⟨13813314, by rfl⟩ : syracuseStep 36835505 = 27626629) B27626629
theorem B3412799 : Blo 896573 3412799 := bstep (se 1 (by rfl) ⟨2559599, by rfl⟩ : syracuseStep 3412799 = 5119199) B5119199
theorem B1348415 : Blo 896573 1348415 := bstep (se 1 (by rfl) ⟨1011311, by rfl⟩ : syracuseStep 1348415 = 2022623) B2022623
theorem B14586743 : Blo 896573 14586743 := bstep (se 1 (by rfl) ⟨10940057, by rfl⟩ : syracuseStep 14586743 = 21880115) B21880115
theorem B1349735 : Blo 896573 1349735 := bstep (se 1 (by rfl) ⟨1012301, by rfl⟩ : syracuseStep 1349735 = 2024603) B2024603
theorem B1513579 : Blo 896573 1513579 := bstep (se 1 (by rfl) ⟨1135184, by rfl⟩ : syracuseStep 1513579 = 2270369) B2270369
theorem B1349855 : Blo 896573 1349855 := bstep (se 1 (by rfl) ⟨1012391, by rfl⟩ : syracuseStep 1349855 = 2024783) B2024783
theorem B1513883 : Blo 896573 1513883 := bstep (se 1 (by rfl) ⟨1135412, by rfl⟩ : syracuseStep 1513883 = 2270825) B2270825
theorem B3414575 : Blo 896573 3414575 := bstep (se 1 (by rfl) ⟨2560931, by rfl⟩ : syracuseStep 3414575 = 5121863) B5121863
theorem B1350191 : Blo 896573 1350191 := bstep (se 1 (by rfl) ⟨1012643, by rfl⟩ : syracuseStep 1350191 = 2025287) B2025287
theorem B1350335 : Blo 896573 1350335 := bstep (se 1 (by rfl) ⟨1012751, by rfl⟩ : syracuseStep 1350335 = 2025503) B2025503
theorem B1350383 : Blo 896573 1350383 := bstep (se 1 (by rfl) ⟨1012787, by rfl⟩ : syracuseStep 1350383 = 2025575) B2025575
theorem B1350569 : Blo 896573 1350569 := bstep (se 2 (by rfl) ⟨506463, by rfl⟩ : syracuseStep 1350569 = 1012927) B1012927
theorem B1350599 : Blo 896573 1350599 := bstep (se 1 (by rfl) ⟨1012949, by rfl⟩ : syracuseStep 1350599 = 2025899) B2025899
theorem B1350815 : Blo 896573 1350815 := bstep (se 1 (by rfl) ⟨1013111, by rfl⟩ : syracuseStep 1350815 = 2026223) B2026223
theorem B1514855 : Blo 896573 1514855 := bstep (se 1 (by rfl) ⟨1136141, by rfl⟩ : syracuseStep 1514855 = 2272283) B2272283
theorem B5119631 : Blo 896573 5119631 := bstep (se 1 (by rfl) ⟨3839723, by rfl⟩ : syracuseStep 5119631 = 7679447) B7679447
theorem B1515503 : Blo 896573 1515503 := bstep (se 1 (by rfl) ⟨1136627, by rfl⟩ : syracuseStep 1515503 = 2273255) B2273255
theorem B3416201 : Blo 896573 3416201 := bstep (se 2 (by rfl) ⟨1281075, by rfl⟩ : syracuseStep 3416201 = 2562151) B2562151
theorem B1515847 : Blo 896573 1515847 := bstep (se 1 (by rfl) ⟨1136885, by rfl⟩ : syracuseStep 1515847 = 2273771) B2273771
theorem B12820841 : Blo 896573 12820841 := bstep (se 2 (by rfl) ⟨4807815, by rfl⟩ : syracuseStep 12820841 = 9615631) B9615631
theorem B7283155 : Blo 896573 7283155 := bstep (se 1 (by rfl) ⟨5462366, by rfl⟩ : syracuseStep 7283155 = 10924733) B10924733
theorem B2269903 : Blo 896573 2269903 := bstep (se 1 (by rfl) ⟨1702427, by rfl⟩ : syracuseStep 2269903 = 3404855) B3404855
theorem B3416975 : Blo 896573 3416975 := bstep (se 1 (by rfl) ⟨2562731, by rfl⟩ : syracuseStep 3416975 = 5125463) B5125463
theorem B2270875 : Blo 896573 2270875 := bstep (se 1 (by rfl) ⟨1703156, by rfl⟩ : syracuseStep 2270875 = 3406313) B3406313
theorem B52471961 : Blo 896573 52471961 := bstep (se 2 (by rfl) ⟨19676985, by rfl⟩ : syracuseStep 52471961 = 39353971) B39353971
theorem B43625911 : Blo 896573 43625911 := bstep (se 1 (by rfl) ⟨32719433, by rfl⟩ : syracuseStep 43625911 = 65438867) B65438867
theorem B1519087 : Blo 896573 1519087 := bstep (se 1 (by rfl) ⟨1139315, by rfl⟩ : syracuseStep 1519087 = 2278631) B2278631
theorem B896623 : Blo 896573 896623 := bstep (se 1 (by rfl) ⟨672467, by rfl⟩ : syracuseStep 896623 = 1344935) B1344935
theorem B896671 : Blo 896573 896671 := bstep (se 1 (by rfl) ⟨672503, by rfl⟩ : syracuseStep 896671 = 1345007) B1345007
theorem B1519519 : Blo 896573 1519519 := bstep (se 1 (by rfl) ⟨1139639, by rfl⟩ : syracuseStep 1519519 = 2279279) B2279279
theorem B5124005 : Blo 896573 5124005 := bstep (se 4 (by rfl) ⟨480375, by rfl⟩ : syracuseStep 5124005 = 960751) B960751
theorem B897263 : Blo 896573 897263 := bstep (se 1 (by rfl) ⟨672947, by rfl⟩ : syracuseStep 897263 = 1345895) B1345895
theorem B897351 : Blo 896573 897351 := bstep (se 1 (by rfl) ⟨673013, by rfl⟩ : syracuseStep 897351 = 1346027) B1346027
theorem B897511 : Blo 896573 897511 := bstep (se 1 (by rfl) ⟨673133, by rfl⟩ : syracuseStep 897511 = 1346267) B1346267
theorem B13840951 : Blo 896573 13840951 := bstep (se 1 (by rfl) ⟨10380713, by rfl⟩ : syracuseStep 13840951 = 20761427) B20761427
theorem B898407 : Blo 896573 898407 := bstep (se 1 (by rfl) ⟨673805, by rfl⟩ : syracuseStep 898407 = 1347611) B1347611
theorem B21869999 : Blo 896573 21869999 := bstep (se 1 (by rfl) ⟨16402499, by rfl⟩ : syracuseStep 21869999 = 32804999) B32804999
theorem B6666259 : Blo 896573 6666259 := bstep (se 1 (by rfl) ⟨4999694, by rfl⟩ : syracuseStep 6666259 = 9999389) B9999389
theorem B899099 : Blo 896573 899099 := bstep (se 1 (by rfl) ⟨674324, by rfl⟩ : syracuseStep 899099 = 1348649) B1348649
theorem B10238075 : Blo 896573 10238075 := bstep (se 1 (by rfl) ⟨7678556, by rfl⟩ : syracuseStep 10238075 = 15357113) B15357113
theorem B3029129 : Blo 896573 3029129 := bstep (se 2 (by rfl) ⟨1135923, by rfl⟩ : syracuseStep 3029129 = 2271847) B2271847
theorem B899431 : Blo 896573 899431 := bstep (se 1 (by rfl) ⟨674573, by rfl⟩ : syracuseStep 899431 = 1349147) B1349147
theorem B1522795 : Blo 896573 1522795 := bstep (se 1 (by rfl) ⟨1142096, by rfl⟩ : syracuseStep 1522795 = 2284193) B2284193
theorem B900335 : Blo 896573 900335 := bstep (se 1 (by rfl) ⟨675251, by rfl⟩ : syracuseStep 900335 = 1350503) B1350503
theorem B8633729 : Blo 896573 8633729 := bstep (se 2 (by rfl) ⟨3237648, by rfl⟩ : syracuseStep 8633729 = 6475297) B6475297
theorem B6569723 : Blo 896573 6569723 := bstep (se 1 (by rfl) ⟨4927292, by rfl⟩ : syracuseStep 6569723 = 9854585) B9854585
theorem B30294233 : Blo 896573 30294233 := bstep (se 2 (by rfl) ⟨11360337, by rfl⟩ : syracuseStep 30294233 = 22720675) B22720675
theorem B6472325 : Blo 896573 6472325 := bstep (se 4 (by rfl) ⟨606780, by rfl⟩ : syracuseStep 6472325 = 1213561) B1213561
theorem B3884219 : Blo 896573 3884219 := bstep (se 1 (by rfl) ⟨2913164, by rfl⟩ : syracuseStep 3884219 = 5826329) B5826329
theorem B6473479 : Blo 896573 6473479 := bstep (se 1 (by rfl) ⟨4855109, by rfl⟩ : syracuseStep 6473479 = 9710219) B9710219
theorem B8636381 : Blo 896573 8636381 := bstep (se 3 (by rfl) ⟨1619321, by rfl⟩ : syracuseStep 8636381 = 3238643) B3238643
theorem B3033071 : Blo 896573 3033071 := bstep (se 1 (by rfl) ⟨2274803, by rfl⟩ : syracuseStep 3033071 = 4549607) B4549607
theorem B3033179 : Blo 896573 3033179 := bstep (se 1 (by rfl) ⟨2274884, by rfl⟩ : syracuseStep 3033179 = 4549769) B4549769
theorem B6473999 : Blo 896573 6473999 := bstep (se 1 (by rfl) ⟨4855499, by rfl⟩ : syracuseStep 6473999 = 9710999) B9710999
theorem B24628049 : Blo 896573 24628049 := bstep (se 2 (by rfl) ⟨9235518, by rfl⟩ : syracuseStep 24628049 = 18471037) B18471037
theorem B19451573 : Blo 896573 19451573 := bstep (se 5 (by rfl) ⟨911792, by rfl⟩ : syracuseStep 19451573 = 1823585) B1823585
theorem B22171337 : Blo 896573 22171337 := bstep (se 2 (by rfl) ⟨8314251, by rfl⟩ : syracuseStep 22171337 = 16628503) B16628503
theorem B1364527 : Blo 896573 1364527 := bstep (se 1 (by rfl) ⟨1023395, by rfl⟩ : syracuseStep 1364527 = 2046791) B2046791
theorem B2020607 : Blo 896573 2020607 := bstep (se 1 (by rfl) ⟨1515455, by rfl⟩ : syracuseStep 2020607 = 3030911) B3030911
theorem B11491955 : Blo 896573 11491955 := bstep (se 1 (by rfl) ⟨8618966, by rfl⟩ : syracuseStep 11491955 = 17237933) B17237933
theorem B4316267 : Blo 896573 4316267 := bstep (se 1 (by rfl) ⟨3237200, by rfl⟩ : syracuseStep 4316267 = 6474401) B6474401
theorem B2023163 : Blo 896573 2023163 := bstep (se 1 (by rfl) ⟨1517372, by rfl⟩ : syracuseStep 2023163 = 3034745) B3034745
theorem B3891007 : Blo 896573 3891007 := bstep (se 1 (by rfl) ⟨2918255, by rfl⟩ : syracuseStep 3891007 = 5836511) B5836511
theorem B18472997 : Blo 896573 18472997 := bstep (se 4 (by rfl) ⟨1731843, by rfl⟩ : syracuseStep 18472997 = 3463687) B3463687
theorem B2023991 : Blo 896573 2023991 := bstep (se 1 (by rfl) ⟨1517993, by rfl⟩ : syracuseStep 2023991 = 3035987) B3035987
theorem B2024027 : Blo 896573 2024027 := bstep (se 1 (by rfl) ⟨1518020, by rfl⟩ : syracuseStep 2024027 = 3036041) B3036041
theorem B2024441 : Blo 896573 2024441 := bstep (se 2 (by rfl) ⟨759165, by rfl⟩ : syracuseStep 2024441 = 1518331) B1518331
theorem B2876897 : Blo 896573 2876897 := bstep (se 2 (by rfl) ⟨1078836, by rfl⟩ : syracuseStep 2876897 = 2157673) B2157673
theorem B19457981 : Blo 896573 19457981 := bstep (se 3 (by rfl) ⟨3648371, by rfl⟩ : syracuseStep 19457981 = 7296743) B7296743
theorem B4548797 : Blo 896573 4548797 := bstep (se 3 (by rfl) ⟨852899, by rfl⟩ : syracuseStep 4548797 = 1705799) B1705799
theorem B10217663 : Blo 896573 10217663 := bstep (se 1 (by rfl) ⟨7663247, by rfl⟩ : syracuseStep 10217663 = 15326495) B15326495
theorem B6809831 : Blo 896573 6809831 := bstep (se 1 (by rfl) ⟨5107373, by rfl⟩ : syracuseStep 6809831 = 10214747) B10214747
theorem B1534655 : Blo 896573 1534655 := bstep (se 1 (by rfl) ⟨1150991, by rfl⟩ : syracuseStep 1534655 = 2301983) B2301983
theorem B5762177 : Blo 896573 5762177 := bstep (se 2 (by rfl) ⟨2160816, by rfl⟩ : syracuseStep 5762177 = 4321633) B4321633
theorem B1012351 : Blo 896573 1012351 := bstep (se 1 (by rfl) ⟨759263, by rfl⟩ : syracuseStep 1012351 = 1518527) B1518527
theorem B4616939 : Blo 896573 4616939 := bstep (se 1 (by rfl) ⟨3462704, by rfl⟩ : syracuseStep 4616939 = 6925409) B6925409
theorem B3405311 : Blo 896573 3405311 := bstep (se 1 (by rfl) ⟨2553983, by rfl⟩ : syracuseStep 3405311 = 5107967) B5107967
theorem B4552361 : Blo 896573 4552361 := bstep (se 2 (by rfl) ⟨1707135, by rfl⟩ : syracuseStep 4552361 = 3414271) B3414271
theorem B2553551 : Blo 896573 2553551 := bstep (se 1 (by rfl) ⟨1915163, by rfl⟩ : syracuseStep 2553551 = 3830327) B3830327
theorem B2193115 : Blo 896573 2193115 := bstep (se 1 (by rfl) ⟨1644836, by rfl⟩ : syracuseStep 2193115 = 3289673) B3289673
theorem B5109925 : Blo 896573 5109925 := bstep (se 4 (by rfl) ⟨479055, by rfl⟩ : syracuseStep 5109925 = 958111) B958111
theorem B49117697 : Blo 896573 49117697 := bstep (se 2 (by rfl) ⟨18419136, by rfl⟩ : syracuseStep 49117697 = 36838273) B36838273
theorem B10910375 : Blo 896573 10910375 := bstep (se 1 (by rfl) ⟨8182781, by rfl⟩ : syracuseStep 10910375 = 16365563) B16365563
theorem B17529625 : Blo 896573 17529625 := bstep (se 2 (by rfl) ⟨6573609, by rfl⟩ : syracuseStep 17529625 = 13147219) B13147219
theorem B3243071 : Blo 896573 3243071 := bstep (se 1 (by rfl) ⟨2432303, by rfl⟩ : syracuseStep 3243071 = 4864607) B4864607
theorem B1441883 : Blo 896573 1441883 := bstep (se 1 (by rfl) ⟨1081412, by rfl⟩ : syracuseStep 1441883 = 2162825) B2162825
theorem B4325879 : Blo 896573 4325879 := bstep (se 1 (by rfl) ⟨3244409, by rfl⟩ : syracuseStep 4325879 = 6488819) B6488819
theorem B1704539 : Blo 896573 1704539 := bstep (se 1 (by rfl) ⟨1278404, by rfl⟩ : syracuseStep 1704539 = 2556809) B2556809
theorem B12321467 : Blo 896573 12321467 := bstep (se 1 (by rfl) ⟨9241100, by rfl⟩ : syracuseStep 12321467 = 18482201) B18482201
theorem B2589479 : Blo 896573 2589479 := bstep (se 1 (by rfl) ⟨1942109, by rfl⟩ : syracuseStep 2589479 = 3884219) B3884219
theorem B5768759 : Blo 896573 5768759 := bstep (se 1 (by rfl) ⟨4326569, by rfl⟩ : syracuseStep 5768759 = 8653139) B8653139
theorem B16418699 : Blo 896573 16418699 := bstep (se 1 (by rfl) ⟨12314024, by rfl⟩ : syracuseStep 16418699 = 24628049) B24628049
theorem B3279091 : Blo 896573 3279091 := bstep (se 1 (by rfl) ⟨2459318, by rfl⟩ : syracuseStep 3279091 = 4918637) B4918637
theorem B14780891 : Blo 896573 14780891 := bstep (se 1 (by rfl) ⟨11085668, by rfl⟩ : syracuseStep 14780891 = 22171337) B22171337
theorem B1347071 : Blo 896573 1347071 := bstep (se 1 (by rfl) ⟨1010303, by rfl⟩ : syracuseStep 1347071 = 2020607) B2020607
theorem B93491333 : Blo 896573 93491333 := bstep (se 4 (by rfl) ⟨8764812, by rfl⟩ : syracuseStep 93491333 = 17529625) B17529625
theorem B58167881 : Blo 896573 58167881 := bstep (se 2 (by rfl) ⟨21812955, by rfl⟩ : syracuseStep 58167881 = 43625911) B43625911
theorem B3413087 : Blo 896573 3413087 := bstep (se 1 (by rfl) ⟨2559815, by rfl⟩ : syracuseStep 3413087 = 5119631) B5119631
theorem B1348775 : Blo 896573 1348775 := bstep (se 1 (by rfl) ⟨1011581, by rfl⟩ : syracuseStep 1348775 = 2023163) B2023163
theorem B1349327 : Blo 896573 1349327 := bstep (se 1 (by rfl) ⟨1011995, by rfl⟩ : syracuseStep 1349327 = 2023991) B2023991
theorem B1349351 : Blo 896573 1349351 := bstep (se 1 (by rfl) ⟨1012013, by rfl⟩ : syracuseStep 1349351 = 2024027) B2024027
theorem B1349627 : Blo 896573 1349627 := bstep (se 1 (by rfl) ⟨1012220, by rfl⟩ : syracuseStep 1349627 = 2024441) B2024441
theorem B18454601 : Blo 896573 18454601 := bstep (se 2 (by rfl) ⟨6920475, by rfl⟩ : syracuseStep 18454601 = 13840951) B13840951
theorem B1349801 : Blo 896573 1349801 := bstep (se 2 (by rfl) ⟨506175, by rfl⟩ : syracuseStep 1349801 = 1012351) B1012351
theorem B1023103 : Blo 896573 1023103 := bstep (se 1 (by rfl) ⟨767327, by rfl⟩ : syracuseStep 1023103 = 1534655) B1534655
theorem B3841451 : Blo 896573 3841451 := bstep (se 1 (by rfl) ⟨2881088, by rfl⟩ : syracuseStep 3841451 = 5762177) B5762177
theorem B2924153 : Blo 896573 2924153 := bstep (se 2 (by rfl) ⟨1096557, by rfl⟩ : syracuseStep 2924153 = 2193115) B2193115
theorem B3416003 : Blo 896573 3416003 := bstep (se 1 (by rfl) ⟨2562002, by rfl⟩ : syracuseStep 3416003 = 5124005) B5124005
theorem B8888345 : Blo 896573 8888345 := bstep (se 2 (by rfl) ⟨3333129, by rfl⟩ : syracuseStep 8888345 = 6666259) B6666259
theorem B11510045 : Blo 896573 11510045 := bstep (se 3 (by rfl) ⟨2158133, by rfl⟩ : syracuseStep 11510045 = 4316267) B4316267
theorem B2270207 : Blo 896573 2270207 := bstep (se 1 (by rfl) ⟨1702655, by rfl⟩ : syracuseStep 2270207 = 3405311) B3405311
theorem B6825383 : Blo 896573 6825383 := bstep (se 1 (by rfl) ⟨5119037, by rfl⟩ : syracuseStep 6825383 = 10238075) B10238075
theorem B32745131 : Blo 896573 32745131 := bstep (se 1 (by rfl) ⟨24558848, by rfl⟩ : syracuseStep 32745131 = 49117697) B49117697
theorem B5188009 : Blo 896573 5188009 := bstep (se 2 (by rfl) ⟨1945503, by rfl⟩ : syracuseStep 5188009 = 3891007) B3891007
theorem B20196155 : Blo 896573 20196155 := bstep (se 1 (by rfl) ⟨15147116, by rfl⟩ : syracuseStep 20196155 = 30294233) B30294233
theorem B961627 : Blo 896573 961627 := bstep (se 1 (by rfl) ⟨721220, by rfl⟩ : syracuseStep 961627 = 1442441) B1442441
theorem B9219257 : Blo 896573 9219257 := bstep (se 2 (by rfl) ⟨3457221, by rfl⟩ : syracuseStep 9219257 = 6914443) B6914443
theorem B9710873 : Blo 896573 9710873 := bstep (se 2 (by rfl) ⟨3641577, by rfl⟩ : syracuseStep 9710873 = 7283155) B7283155
theorem B2075975 : Blo 896573 2075975 := bstep (se 1 (by rfl) ⟨1556981, by rfl⟩ : syracuseStep 2075975 = 3113963) B3113963
theorem B3026537 : Blo 896573 3026537 := bstep (se 2 (by rfl) ⟨1134951, by rfl⟩ : syracuseStep 3026537 = 2269903) B2269903
theorem B896859 : Blo 896573 896859 := bstep (se 1 (by rfl) ⟨672644, by rfl⟩ : syracuseStep 896859 = 1345289) B1345289
theorem B14200705 : Blo 896573 14200705 := bstep (se 2 (by rfl) ⟨5325264, by rfl⟩ : syracuseStep 14200705 = 10650529) B10650529
theorem B3649495 : Blo 896573 3649495 := bstep (se 1 (by rfl) ⟨2737121, by rfl⟩ : syracuseStep 3649495 = 5474243) B5474243
theorem B897231 : Blo 896573 897231 := bstep (se 1 (by rfl) ⟨672923, by rfl⟩ : syracuseStep 897231 = 1345847) B1345847
theorem B897895 : Blo 896573 897895 := bstep (se 1 (by rfl) ⟨673421, by rfl⟩ : syracuseStep 897895 = 1346843) B1346843
theorem B3027833 : Blo 896573 3027833 := bstep (se 2 (by rfl) ⟨1135437, by rfl⟩ : syracuseStep 3027833 = 2270875) B2270875
theorem B8631305 : Blo 896573 8631305 := bstep (se 2 (by rfl) ⟨3236739, by rfl⟩ : syracuseStep 8631305 = 6473479) B6473479
theorem B898175 : Blo 896573 898175 := bstep (se 1 (by rfl) ⟨673631, by rfl⟩ : syracuseStep 898175 = 1347263) B1347263
theorem B898495 : Blo 896573 898495 := bstep (se 1 (by rfl) ⟨673871, by rfl⟩ : syracuseStep 898495 = 1347743) B1347743
theorem B24557003 : Blo 896573 24557003 := bstep (se 1 (by rfl) ⟨18417752, by rfl⟩ : syracuseStep 24557003 = 36835505) B36835505
theorem B2275199 : Blo 896573 2275199 := bstep (se 1 (by rfl) ⟨1706399, by rfl⟩ : syracuseStep 2275199 = 3412799) B3412799
theorem B898943 : Blo 896573 898943 := bstep (se 1 (by rfl) ⟨674207, by rfl⟩ : syracuseStep 898943 = 1348415) B1348415
theorem B6470225 : Blo 896573 6470225 := bstep (se 2 (by rfl) ⟨2426334, by rfl⟩ : syracuseStep 6470225 = 4852669) B4852669
theorem B899823 : Blo 896573 899823 := bstep (se 1 (by rfl) ⟨674867, by rfl⟩ : syracuseStep 899823 = 1349735) B1349735
theorem B899903 : Blo 896573 899903 := bstep (se 1 (by rfl) ⟨674927, by rfl⟩ : syracuseStep 899903 = 1349855) B1349855
theorem B2276383 : Blo 896573 2276383 := bstep (se 1 (by rfl) ⟨1707287, by rfl⟩ : syracuseStep 2276383 = 3414575) B3414575
theorem B900127 : Blo 896573 900127 := bstep (se 1 (by rfl) ⟨675095, by rfl⟩ : syracuseStep 900127 = 1350191) B1350191
theorem B900223 : Blo 896573 900223 := bstep (se 1 (by rfl) ⟨675167, by rfl⟩ : syracuseStep 900223 = 1350335) B1350335
theorem B900255 : Blo 896573 900255 := bstep (se 1 (by rfl) ⟨675191, by rfl⟩ : syracuseStep 900255 = 1350383) B1350383
theorem B900379 : Blo 896573 900379 := bstep (se 1 (by rfl) ⟨675284, by rfl⟩ : syracuseStep 900379 = 1350569) B1350569
theorem B900399 : Blo 896573 900399 := bstep (se 1 (by rfl) ⟨675299, by rfl⟩ : syracuseStep 900399 = 1350599) B1350599
theorem B900543 : Blo 896573 900543 := bstep (se 1 (by rfl) ⟨675407, by rfl⟩ : syracuseStep 900543 = 1350815) B1350815
theorem B2277467 : Blo 896573 2277467 := bstep (se 1 (by rfl) ⟨1708100, by rfl⟩ : syracuseStep 2277467 = 3416201) B3416201
theorem B2277983 : Blo 896573 2277983 := bstep (se 1 (by rfl) ⟨1708487, by rfl⟩ : syracuseStep 2277983 = 3416975) B3416975
theorem B1819369 : Blo 896573 1819369 := bstep (se 2 (by rfl) ⟨682263, by rfl⟩ : syracuseStep 1819369 = 1364527) B1364527
theorem B1917931 : Blo 896573 1917931 := bstep (se 1 (by rfl) ⟨1438448, by rfl⟩ : syracuseStep 1917931 = 2876897) B2876897
theorem B34981307 : Blo 896573 34981307 := bstep (se 1 (by rfl) ⟨26235980, by rfl⟩ : syracuseStep 34981307 = 52471961) B52471961
theorem B3032531 : Blo 896573 3032531 := bstep (se 1 (by rfl) ⟨2274398, by rfl⟩ : syracuseStep 3032531 = 4548797) B4548797
theorem B4539887 : Blo 896573 4539887 := bstep (se 1 (by rfl) ⟨3404915, by rfl⟩ : syracuseStep 4539887 = 6809831) B6809831
theorem B2018105 : Blo 896573 2018105 := bstep (se 2 (by rfl) ⟨756789, by rfl⟩ : syracuseStep 2018105 = 1513579) B1513579
theorem B3034907 : Blo 896573 3034907 := bstep (se 1 (by rfl) ⟨2276180, by rfl⟩ : syracuseStep 3034907 = 4552361) B4552361
theorem B2019419 : Blo 896573 2019419 := bstep (se 1 (by rfl) ⟨1514564, by rfl⟩ : syracuseStep 2019419 = 3029129) B3029129
theorem B5755819 : Blo 896573 5755819 := bstep (se 1 (by rfl) ⟨4316864, by rfl⟩ : syracuseStep 5755819 = 8633729) B8633729
theorem B4379815 : Blo 896573 4379815 := bstep (se 1 (by rfl) ⟨3284861, by rfl⟩ : syracuseStep 4379815 = 6569723) B6569723
theorem B4314883 : Blo 896573 4314883 := bstep (se 1 (by rfl) ⟨3236162, by rfl⟩ : syracuseStep 4314883 = 6472325) B6472325
theorem B2021129 : Blo 896573 2021129 := bstep (se 2 (by rfl) ⟨757923, by rfl⟩ : syracuseStep 2021129 = 1515847) B1515847
theorem B4544423 : Blo 896573 4544423 := bstep (se 1 (by rfl) ⟨3408317, by rfl⟩ : syracuseStep 4544423 = 6816635) B6816635
theorem B4544747 : Blo 896573 4544747 := bstep (se 1 (by rfl) ⟨3408560, by rfl⟩ : syracuseStep 4544747 = 6817121) B6817121
theorem B4545071 : Blo 896573 4545071 := bstep (se 1 (by rfl) ⟨3408803, by rfl⟩ : syracuseStep 4545071 = 6817607) B6817607
theorem B5757587 : Blo 896573 5757587 := bstep (se 1 (by rfl) ⟨4318190, by rfl⟩ : syracuseStep 5757587 = 8636381) B8636381
theorem B2022047 : Blo 896573 2022047 := bstep (se 1 (by rfl) ⟨1516535, by rfl⟩ : syracuseStep 2022047 = 3033071) B3033071
theorem B2022119 : Blo 896573 2022119 := bstep (se 1 (by rfl) ⟨1516589, by rfl⟩ : syracuseStep 2022119 = 3033179) B3033179
theorem B4315999 : Blo 896573 4315999 := bstep (se 1 (by rfl) ⟨3236999, by rfl⟩ : syracuseStep 4315999 = 6473999) B6473999
theorem B3038471 : Blo 896573 3038471 := bstep (se 1 (by rfl) ⟨2278853, by rfl⟩ : syracuseStep 3038471 = 4557707) B4557707
theorem B12967715 : Blo 896573 12967715 := bstep (se 1 (by rfl) ⟨9725786, by rfl⟩ : syracuseStep 12967715 = 19451573) B19451573
theorem B1138799 : Blo 896573 1138799 := bstep (se 1 (by rfl) ⟨854099, by rfl⟩ : syracuseStep 1138799 = 1708199) B1708199
theorem B9724495 : Blo 896573 9724495 := bstep (se 1 (by rfl) ⟨7293371, by rfl⟩ : syracuseStep 9724495 = 14586743) B14586743
theorem B1009255 : Blo 896573 1009255 := bstep (se 1 (by rfl) ⟨756941, by rfl⟩ : syracuseStep 1009255 = 1513883) B1513883
theorem B7661303 : Blo 896573 7661303 := bstep (se 1 (by rfl) ⟨5745977, by rfl⟩ : syracuseStep 7661303 = 11491955) B11491955
theorem B4548473 : Blo 896573 4548473 := bstep (se 2 (by rfl) ⟨1705677, by rfl⟩ : syracuseStep 4548473 = 3411355) B3411355
theorem B2025449 : Blo 896573 2025449 := bstep (se 2 (by rfl) ⟨759543, by rfl⟩ : syracuseStep 2025449 = 1519087) B1519087
theorem B1009903 : Blo 896573 1009903 := bstep (se 1 (by rfl) ⟨757427, by rfl⟩ : syracuseStep 1009903 = 1514855) B1514855
theorem B2026025 : Blo 896573 2026025 := bstep (se 2 (by rfl) ⟨759759, by rfl⟩ : syracuseStep 2026025 = 1519519) B1519519
theorem B1010335 : Blo 896573 1010335 := bstep (se 1 (by rfl) ⟨757751, by rfl⟩ : syracuseStep 1010335 = 1515503) B1515503
theorem B12315331 : Blo 896573 12315331 := bstep (se 1 (by rfl) ⟨9236498, by rfl⟩ : syracuseStep 12315331 = 18472997) B18472997
theorem B8547227 : Blo 896573 8547227 := bstep (se 1 (by rfl) ⟨6410420, by rfl⟩ : syracuseStep 8547227 = 12820841) B12820841
theorem B12971987 : Blo 896573 12971987 := bstep (se 1 (by rfl) ⟨9728990, by rfl⟩ : syracuseStep 12971987 = 19457981) B19457981
theorem B6811775 : Blo 896573 6811775 := bstep (se 1 (by rfl) ⟨5108831, by rfl⟩ : syracuseStep 6811775 = 10217663) B10217663
theorem B6813233 : Blo 896573 6813233 := bstep (se 2 (by rfl) ⟨2554962, by rfl⟩ : syracuseStep 6813233 = 5109925) B5109925
theorem B3077959 : Blo 896573 3077959 := bstep (se 1 (by rfl) ⟨2308469, by rfl⟩ : syracuseStep 3077959 = 4616939) B4616939
theorem B14579999 : Blo 896573 14579999 := bstep (se 1 (by rfl) ⟨10934999, by rfl⟩ : syracuseStep 14579999 = 21869999) B21869999
theorem B1702367 : Blo 896573 1702367 := bstep (se 1 (by rfl) ⟨1276775, by rfl⟩ : syracuseStep 1702367 = 2553551) B2553551
theorem B2030393 : Blo 896573 2030393 := bstep (se 2 (by rfl) ⟨761397, by rfl⟩ : syracuseStep 2030393 = 1522795) B1522795
theorem B7273583 : Blo 896573 7273583 := bstep (se 1 (by rfl) ⟨5455187, by rfl⟩ : syracuseStep 7273583 = 10910375) B10910375
theorem B2162047 : Blo 896573 2162047 := bstep (se 1 (by rfl) ⟨1621535, by rfl⟩ : syracuseStep 2162047 = 3243071) B3243071
theorem B2883919 : Blo 896573 2883919 := bstep (se 1 (by rfl) ⟨2162939, by rfl⟩ : syracuseStep 2883919 = 4325879) B4325879
theorem B2425825 : Blo 896573 2425825 := bstep (se 2 (by rfl) ⟨909684, by rfl⟩ : syracuseStep 2425825 = 1819369) B1819369
theorem B10945799 : Blo 896573 10945799 := bstep (se 1 (by rfl) ⟨8209349, by rfl⟩ : syracuseStep 10945799 = 16418699) B16418699
theorem B2557241 : Blo 896573 2557241 := bstep (se 2 (by rfl) ⟨958965, by rfl⟩ : syracuseStep 2557241 = 1917931) B1917931
theorem B1345403 : Blo 896573 1345403 := bstep (se 1 (by rfl) ⟨1009052, by rfl⟩ : syracuseStep 1345403 = 2018105) B2018105
theorem B1345673 : Blo 896573 1345673 := bstep (se 2 (by rfl) ⟨504627, by rfl⟩ : syracuseStep 1345673 = 1009255) B1009255
theorem B1346279 : Blo 896573 1346279 := bstep (se 1 (by rfl) ⟨1009709, by rfl⟩ : syracuseStep 1346279 = 2019419) B2019419
theorem B62327555 : Blo 896573 62327555 := bstep (se 1 (by rfl) ⟨46745666, by rfl⟩ : syracuseStep 62327555 = 93491333) B93491333
theorem B1346537 : Blo 896573 1346537 := bstep (se 2 (by rfl) ⟨504951, by rfl⟩ : syracuseStep 1346537 = 1009903) B1009903
theorem B6917345 : Blo 896573 6917345 := bstep (se 2 (by rfl) ⟨2594004, by rfl⟩ : syracuseStep 6917345 = 5188009) B5188009
theorem B1347113 : Blo 896573 1347113 := bstep (se 2 (by rfl) ⟨505167, by rfl⟩ : syracuseStep 1347113 = 1010335) B1010335
theorem B16420441 : Blo 896573 16420441 := bstep (se 2 (by rfl) ⟨6157665, by rfl⟩ : syracuseStep 16420441 = 12315331) B12315331
theorem B1347419 : Blo 896573 1347419 := bstep (se 1 (by rfl) ⟨1010564, by rfl⟩ : syracuseStep 1347419 = 2021129) B2021129
theorem B1282169 : Blo 896573 1282169 := bstep (se 2 (by rfl) ⟨480813, by rfl⟩ : syracuseStep 1282169 = 961627) B961627
theorem B3838391 : Blo 896573 3838391 := bstep (se 1 (by rfl) ⟨2878793, by rfl⟩ : syracuseStep 3838391 = 5757587) B5757587
theorem B1348031 : Blo 896573 1348031 := bstep (se 1 (by rfl) ⟨1011023, by rfl⟩ : syracuseStep 1348031 = 2022047) B2022047
theorem B1348079 : Blo 896573 1348079 := bstep (se 1 (by rfl) ⟨1011059, by rfl⟩ : syracuseStep 1348079 = 2022119) B2022119
theorem B2560967 : Blo 896573 2560967 := bstep (se 1 (by rfl) ⟨1920725, by rfl⟩ : syracuseStep 2560967 = 3841451) B3841451
theorem B7673363 : Blo 896573 7673363 := bstep (se 1 (by rfl) ⟨5755022, by rfl⟩ : syracuseStep 7673363 = 11510045) B11510045
theorem B1513471 : Blo 896573 1513471 := bstep (se 1 (by rfl) ⟨1135103, by rfl⟩ : syracuseStep 1513471 = 2270207) B2270207
theorem B21830087 : Blo 896573 21830087 := bstep (se 1 (by rfl) ⟨16372565, by rfl⟩ : syracuseStep 21830087 = 32745131) B32745131
theorem B7674425 : Blo 896573 7674425 := bstep (se 2 (by rfl) ⟨2877909, by rfl⟩ : syracuseStep 7674425 = 5755819) B5755819
theorem B1350299 : Blo 896573 1350299 := bstep (se 1 (by rfl) ⟨1012724, by rfl⟩ : syracuseStep 1350299 = 2025449) B2025449
theorem B1350683 : Blo 896573 1350683 := bstep (se 1 (by rfl) ⟨1013012, by rfl⟩ : syracuseStep 1350683 = 2026025) B2026025
theorem B5414381 : Blo 896573 5414381 := bstep (se 3 (by rfl) ⟨1015196, by rfl⟩ : syracuseStep 5414381 = 2030393) B2030393
theorem B1383983 : Blo 896573 1383983 := bstep (se 1 (by rfl) ⟨1037987, by rfl⟩ : syracuseStep 1383983 = 2075975) B2075975
theorem B4103945 : Blo 896573 4103945 := bstep (se 2 (by rfl) ⟨1538979, by rfl⟩ : syracuseStep 4103945 = 3077959) B3077959
theorem B1516799 : Blo 896573 1516799 := bstep (se 1 (by rfl) ⟨1137599, by rfl⟩ : syracuseStep 1516799 = 2275199) B2275199
theorem B1518311 : Blo 896573 1518311 := bstep (se 1 (by rfl) ⟨1138733, by rfl⟩ : syracuseStep 1518311 = 2277467) B2277467
theorem B961255 : Blo 896573 961255 := bstep (se 1 (by rfl) ⟨720941, by rfl⟩ : syracuseStep 961255 = 1441883) B1441883
theorem B1518655 : Blo 896573 1518655 := bstep (se 1 (by rfl) ⟨1138991, by rfl⟩ : syracuseStep 1518655 = 2277983) B2277983
theorem B3026591 : Blo 896573 3026591 := bstep (se 1 (by rfl) ⟨2269943, by rfl⟩ : syracuseStep 3026591 = 4539887) B4539887
theorem B898047 : Blo 896573 898047 := bstep (se 1 (by rfl) ⟨673535, by rfl⟩ : syracuseStep 898047 = 1347071) B1347071
theorem B4372121 : Blo 896573 4372121 := bstep (se 2 (by rfl) ⟨1639545, by rfl⟩ : syracuseStep 4372121 = 3279091) B3279091
theorem B38778587 : Blo 896573 38778587 := bstep (se 1 (by rfl) ⟨29083940, by rfl⟩ : syracuseStep 38778587 = 58167881) B58167881
theorem B2275391 : Blo 896573 2275391 := bstep (se 1 (by rfl) ⟨1706543, by rfl⟩ : syracuseStep 2275391 = 3413087) B3413087
theorem B899183 : Blo 896573 899183 := bstep (se 1 (by rfl) ⟨674387, by rfl⟩ : syracuseStep 899183 = 1348775) B1348775
theorem B899551 : Blo 896573 899551 := bstep (se 1 (by rfl) ⟨674663, by rfl⟩ : syracuseStep 899551 = 1349327) B1349327
theorem B899567 : Blo 896573 899567 := bstep (se 1 (by rfl) ⟨674675, by rfl⟩ : syracuseStep 899567 = 1349351) B1349351
theorem B3029615 : Blo 896573 3029615 := bstep (se 1 (by rfl) ⟨2272211, by rfl⟩ : syracuseStep 3029615 = 4544423) B4544423
theorem B899751 : Blo 896573 899751 := bstep (se 1 (by rfl) ⟨674813, by rfl⟩ : syracuseStep 899751 = 1349627) B1349627
theorem B899867 : Blo 896573 899867 := bstep (se 1 (by rfl) ⟨674900, by rfl⟩ : syracuseStep 899867 = 1349801) B1349801
theorem B15383357 : Blo 896573 15383357 := bstep (se 3 (by rfl) ⟨2884379, by rfl⟩ : syracuseStep 15383357 = 5768759) B5768759
theorem B3029831 : Blo 896573 3029831 := bstep (se 1 (by rfl) ⟨2272373, by rfl⟩ : syracuseStep 3029831 = 4544747) B4544747
theorem B3030047 : Blo 896573 3030047 := bstep (se 1 (by rfl) ⟨2272535, by rfl⟩ : syracuseStep 3030047 = 4545071) B4545071
theorem B1949435 : Blo 896573 1949435 := bstep (se 1 (by rfl) ⟨1462076, by rfl⟩ : syracuseStep 1949435 = 2924153) B2924153
theorem B4865993 : Blo 896573 4865993 := bstep (se 2 (by rfl) ⟨1824747, by rfl⟩ : syracuseStep 4865993 = 3649495) B3649495
theorem B2277335 : Blo 896573 2277335 := bstep (se 1 (by rfl) ⟨1708001, by rfl⟩ : syracuseStep 2277335 = 3416003) B3416003
theorem B3032315 : Blo 896573 3032315 := bstep (se 1 (by rfl) ⟨2274236, by rfl⟩ : syracuseStep 3032315 = 4548473) B4548473
theorem B6146171 : Blo 896573 6146171 := bstep (se 1 (by rfl) ⟨4609628, by rfl⟩ : syracuseStep 6146171 = 9219257) B9219257
theorem B6473915 : Blo 896573 6473915 := bstep (se 1 (by rfl) ⟨4855436, by rfl⟩ : syracuseStep 6473915 = 9710873) B9710873
theorem B5753177 : Blo 896573 5753177 := bstep (se 2 (by rfl) ⟨2157441, by rfl⟩ : syracuseStep 5753177 = 4314883) B4314883
theorem B2017691 : Blo 896573 2017691 := bstep (se 1 (by rfl) ⟨1513268, by rfl⟩ : syracuseStep 2017691 = 3026537) B3026537
theorem B4541183 : Blo 896573 4541183 := bstep (se 1 (by rfl) ⟨3405887, by rfl⟩ : syracuseStep 4541183 = 6811775) B6811775
theorem B2018555 : Blo 896573 2018555 := bstep (se 1 (by rfl) ⟨1513916, by rfl⟩ : syracuseStep 2018555 = 3027833) B3027833
theorem B5754203 : Blo 896573 5754203 := bstep (se 1 (by rfl) ⟨4315652, by rfl⟩ : syracuseStep 5754203 = 8631305) B8631305
theorem B16371335 : Blo 896573 16371335 := bstep (se 1 (by rfl) ⟨12278501, by rfl⟩ : syracuseStep 16371335 = 24557003) B24557003
theorem B4542155 : Blo 896573 4542155 := bstep (se 1 (by rfl) ⟨3406616, by rfl⟩ : syracuseStep 4542155 = 6813233) B6813233
theorem B5754665 : Blo 896573 5754665 := bstep (se 2 (by rfl) ⟨2157999, by rfl⟩ : syracuseStep 5754665 = 4315999) B4315999
theorem B3035177 : Blo 896573 3035177 := bstep (se 2 (by rfl) ⟨1138191, by rfl⟩ : syracuseStep 3035177 = 2276383) B2276383
theorem B1364137 : Blo 896573 1364137 := bstep (se 2 (by rfl) ⟨511551, by rfl⟩ : syracuseStep 1364137 = 1023103) B1023103
theorem B9719999 : Blo 896573 9719999 := bstep (se 1 (by rfl) ⟨7289999, by rfl⟩ : syracuseStep 9719999 = 14579999) B14579999
theorem B1134911 : Blo 896573 1134911 := bstep (se 1 (by rfl) ⟨851183, by rfl⟩ : syracuseStep 1134911 = 1702367) B1702367
theorem B4313483 : Blo 896573 4313483 := bstep (se 1 (by rfl) ⟨3235112, by rfl⟩ : syracuseStep 4313483 = 6470225) B6470225
theorem B3036797 : Blo 896573 3036797 := bstep (se 3 (by rfl) ⟨569399, by rfl⟩ : syracuseStep 3036797 = 1138799) B1138799
theorem B1136359 : Blo 896573 1136359 := bstep (se 1 (by rfl) ⟨852269, by rfl⟩ : syracuseStep 1136359 = 1704539) B1704539
theorem B8214311 : Blo 896573 8214311 := bstep (se 1 (by rfl) ⟨6160733, by rfl⟩ : syracuseStep 8214311 = 12321467) B12321467
theorem B1726319 : Blo 896573 1726319 := bstep (se 1 (by rfl) ⟨1294739, by rfl⟩ : syracuseStep 1726319 = 2589479) B2589479
theorem B12965993 : Blo 896573 12965993 := bstep (se 2 (by rfl) ⟨4862247, by rfl⟩ : syracuseStep 12965993 = 9724495) B9724495
theorem B23320871 : Blo 896573 23320871 := bstep (se 1 (by rfl) ⟨17490653, by rfl⟩ : syracuseStep 23320871 = 34981307) B34981307
theorem B2021687 : Blo 896573 2021687 := bstep (se 1 (by rfl) ⟨1516265, by rfl⟩ : syracuseStep 2021687 = 3032531) B3032531
theorem B2023271 : Blo 896573 2023271 := bstep (se 1 (by rfl) ⟨1517453, by rfl⟩ : syracuseStep 2023271 = 3034907) B3034907
theorem B2025647 : Blo 896573 2025647 := bstep (se 1 (by rfl) ⟨1519235, by rfl⟩ : syracuseStep 2025647 = 3038471) B3038471
theorem B18934273 : Blo 896573 18934273 := bstep (se 2 (by rfl) ⟨7100352, by rfl⟩ : syracuseStep 18934273 = 14200705) B14200705
theorem B8645143 : Blo 896573 8645143 := bstep (se 1 (by rfl) ⟨6483857, by rfl⟩ : syracuseStep 8645143 = 12967715) B12967715
theorem B5925563 : Blo 896573 5925563 := bstep (se 1 (by rfl) ⟨4444172, by rfl⟩ : syracuseStep 5925563 = 8888345) B8888345
theorem B49212269 : Blo 896573 49212269 := bstep (se 3 (by rfl) ⟨9227300, by rfl⟩ : syracuseStep 49212269 = 18454601) B18454601
theorem B23359013 : Blo 896573 23359013 := bstep (se 4 (by rfl) ⟨2189907, by rfl⟩ : syracuseStep 23359013 = 4379815) B4379815
theorem B4550255 : Blo 896573 4550255 := bstep (se 1 (by rfl) ⟨3412691, by rfl⟩ : syracuseStep 4550255 = 6825383) B6825383
theorem B5107535 : Blo 896573 5107535 := bstep (se 1 (by rfl) ⟨3830651, by rfl⟩ : syracuseStep 5107535 = 7661303) B7661303
theorem B39415709 : Blo 896573 39415709 := bstep (se 3 (by rfl) ⟨7390445, by rfl⟩ : syracuseStep 39415709 = 14780891) B14780891
theorem B13464103 : Blo 896573 13464103 := bstep (se 1 (by rfl) ⟨10098077, by rfl⟩ : syracuseStep 13464103 = 20196155) B20196155
theorem B5698151 : Blo 896573 5698151 := bstep (se 1 (by rfl) ⟨4273613, by rfl⟩ : syracuseStep 5698151 = 8547227) B8547227
theorem B8647991 : Blo 896573 8647991 := bstep (se 1 (by rfl) ⟨6485993, by rfl⟩ : syracuseStep 8647991 = 12971987) B12971987
theorem B2882729 : Blo 896573 2882729 := bstep (se 2 (by rfl) ⟨1081023, by rfl⟩ : syracuseStep 2882729 = 2162047) B2162047
theorem B4849055 : Blo 896573 4849055 := bstep (se 1 (by rfl) ⟨3636791, by rfl⟩ : syracuseStep 4849055 = 7273583) B7273583
theorem B1704827 : Blo 896573 1704827 := bstep (se 1 (by rfl) ⟨1278620, by rfl⟩ : syracuseStep 1704827 = 2557241) B2557241
theorem B4097447 : Blo 896573 4097447 := bstep (se 1 (by rfl) ⟨3073085, by rfl⟩ : syracuseStep 4097447 = 6146171) B6146171
theorem B3835451 : Blo 896573 3835451 := bstep (se 1 (by rfl) ⟨2876588, by rfl⟩ : syracuseStep 3835451 = 5753177) B5753177
theorem B1345127 : Blo 896573 1345127 := bstep (se 1 (by rfl) ⟨1008845, by rfl⟩ : syracuseStep 1345127 = 2017691) B2017691
theorem B41551703 : Blo 896573 41551703 := bstep (se 1 (by rfl) ⟨31163777, by rfl⟩ : syracuseStep 41551703 = 62327555) B62327555
theorem B1345703 : Blo 896573 1345703 := bstep (se 1 (by rfl) ⟨1009277, by rfl⟩ : syracuseStep 1345703 = 2018555) B2018555
theorem B3836135 : Blo 896573 3836135 := bstep (se 1 (by rfl) ⟨2877101, by rfl⟩ : syracuseStep 3836135 = 5754203) B5754203
theorem B3836443 : Blo 896573 3836443 := bstep (se 1 (by rfl) ⟨2877332, by rfl⟩ : syracuseStep 3836443 = 5754665) B5754665
theorem B2558927 : Blo 896573 2558927 := bstep (se 1 (by rfl) ⟨1919195, by rfl⟩ : syracuseStep 2558927 = 3838391) B3838391
theorem B1707311 : Blo 896573 1707311 := bstep (se 1 (by rfl) ⟨1280483, by rfl⟩ : syracuseStep 1707311 = 2560967) B2560967
theorem B29101589 : Blo 896573 29101589 := bstep (se 6 (by rfl) ⟨682068, by rfl⟩ : syracuseStep 29101589 = 1364137) B1364137
theorem B1281673 : Blo 896573 1281673 := bstep (se 2 (by rfl) ⟨480627, by rfl⟩ : syracuseStep 1281673 = 961255) B961255
theorem B5115575 : Blo 896573 5115575 := bstep (se 1 (by rfl) ⟨3836681, by rfl⟩ : syracuseStep 5115575 = 7673363) B7673363
theorem B5476207 : Blo 896573 5476207 := bstep (se 1 (by rfl) ⟨4107155, by rfl⟩ : syracuseStep 5476207 = 8214311) B8214311
theorem B1347791 : Blo 896573 1347791 := bstep (se 1 (by rfl) ⟨1010843, by rfl⟩ : syracuseStep 1347791 = 2021687) B2021687
theorem B14553391 : Blo 896573 14553391 := bstep (se 1 (by rfl) ⟨10915043, by rfl⟩ : syracuseStep 14553391 = 21830087) B21830087
theorem B5116283 : Blo 896573 5116283 := bstep (se 1 (by rfl) ⟨3837212, by rfl⟩ : syracuseStep 5116283 = 7674425) B7674425
theorem B21893921 : Blo 896573 21893921 := bstep (se 2 (by rfl) ⟨8210220, by rfl⟩ : syracuseStep 21893921 = 16420441) B16420441
theorem B3609587 : Blo 896573 3609587 := bstep (se 1 (by rfl) ⟨2707190, by rfl⟩ : syracuseStep 3609587 = 5414381) B5414381
theorem B922655 : Blo 896573 922655 := bstep (se 1 (by rfl) ⟨691991, by rfl⟩ : syracuseStep 922655 = 1383983) B1383983
theorem B1348847 : Blo 896573 1348847 := bstep (se 1 (by rfl) ⟨1011635, by rfl⟩ : syracuseStep 1348847 = 2023271) B2023271
theorem B1350431 : Blo 896573 1350431 := bstep (se 1 (by rfl) ⟨1012823, by rfl⟩ : syracuseStep 1350431 = 2025647) B2025647
theorem B32808179 : Blo 896573 32808179 := bstep (se 1 (by rfl) ⟨24606134, by rfl⟩ : syracuseStep 32808179 = 49212269) B49212269
theorem B1515145 : Blo 896573 1515145 := bstep (se 2 (by rfl) ⟨568179, by rfl⟩ : syracuseStep 1515145 = 1136359) B1136359
theorem B15572675 : Blo 896573 15572675 := bstep (se 1 (by rfl) ⟨11679506, by rfl⟩ : syracuseStep 15572675 = 23359013) B23359013
theorem B1516927 : Blo 896573 1516927 := bstep (se 1 (by rfl) ⟨1137695, by rfl⟩ : syracuseStep 1516927 = 2275391) B2275391
theorem B43656893 : Blo 896573 43656893 := bstep (se 3 (by rfl) ⟨8185667, by rfl⟩ : syracuseStep 43656893 = 16371335) B16371335
theorem B1518223 : Blo 896573 1518223 := bstep (se 1 (by rfl) ⟨1138667, by rfl⟩ : syracuseStep 1518223 = 2277335) B2277335
theorem B3419117 : Blo 896573 3419117 := bstep (se 3 (by rfl) ⟨641084, by rfl⟩ : syracuseStep 3419117 = 1282169) B1282169
theorem B3845225 : Blo 896573 3845225 := bstep (se 2 (by rfl) ⟨1441959, by rfl⟩ : syracuseStep 3845225 = 2883919) B2883919
theorem B3026429 : Blo 896573 3026429 := bstep (se 3 (by rfl) ⟨567455, by rfl⟩ : syracuseStep 3026429 = 1134911) B1134911
theorem B896935 : Blo 896573 896935 := bstep (se 1 (by rfl) ⟨672701, by rfl⟩ : syracuseStep 896935 = 1345403) B1345403
theorem B897115 : Blo 896573 897115 := bstep (se 1 (by rfl) ⟨672836, by rfl⟩ : syracuseStep 897115 = 1345673) B1345673
theorem B897519 : Blo 896573 897519 := bstep (se 1 (by rfl) ⟨673139, by rfl⟩ : syracuseStep 897519 = 1346279) B1346279
theorem B3027455 : Blo 896573 3027455 := bstep (se 1 (by rfl) ⟨2270591, by rfl⟩ : syracuseStep 3027455 = 4541183) B4541183
theorem B897691 : Blo 896573 897691 := bstep (se 1 (by rfl) ⟨673268, by rfl⟩ : syracuseStep 897691 = 1346537) B1346537
theorem B898075 : Blo 896573 898075 := bstep (se 1 (by rfl) ⟨673556, by rfl⟩ : syracuseStep 898075 = 1347113) B1347113
theorem B3028103 : Blo 896573 3028103 := bstep (se 1 (by rfl) ⟨2271077, by rfl⟩ : syracuseStep 3028103 = 4542155) B4542155
theorem B898279 : Blo 896573 898279 := bstep (se 1 (by rfl) ⟨673709, by rfl⟩ : syracuseStep 898279 = 1347419) B1347419
theorem B898687 : Blo 896573 898687 := bstep (se 1 (by rfl) ⟨674015, by rfl⟩ : syracuseStep 898687 = 1348031) B1348031
theorem B898719 : Blo 896573 898719 := bstep (se 1 (by rfl) ⟨674039, by rfl⟩ : syracuseStep 898719 = 1348079) B1348079
theorem B25245697 : Blo 896573 25245697 := bstep (se 2 (by rfl) ⟨9467136, by rfl⟩ : syracuseStep 25245697 = 18934273) B18934273
theorem B15547247 : Blo 896573 15547247 := bstep (se 1 (by rfl) ⟨11660435, by rfl⟩ : syracuseStep 15547247 = 23320871) B23320871
theorem B900199 : Blo 896573 900199 := bstep (se 1 (by rfl) ⟨675149, by rfl⟩ : syracuseStep 900199 = 1350299) B1350299
theorem B900455 : Blo 896573 900455 := bstep (se 1 (by rfl) ⟨675341, by rfl⟩ : syracuseStep 900455 = 1350683) B1350683
theorem B4603517 : Blo 896573 4603517 := bstep (se 3 (by rfl) ⟨863159, by rfl⟩ : syracuseStep 4603517 = 1726319) B1726319
theorem B2735963 : Blo 896573 2735963 := bstep (se 1 (by rfl) ⟨2051972, by rfl⟩ : syracuseStep 2735963 = 4103945) B4103945
theorem B3950375 : Blo 896573 3950375 := bstep (se 1 (by rfl) ⟨2962781, by rfl⟩ : syracuseStep 3950375 = 5925563) B5925563
theorem B3033503 : Blo 896573 3033503 := bstep (se 1 (by rfl) ⟨2275127, by rfl⟩ : syracuseStep 3033503 = 4550255) B4550255
theorem B2017727 : Blo 896573 2017727 := bstep (se 1 (by rfl) ⟨1513295, by rfl⟩ : syracuseStep 2017727 = 3026591) B3026591
theorem B2017961 : Blo 896573 2017961 := bstep (se 2 (by rfl) ⟨756735, by rfl⟩ : syracuseStep 2017961 = 1513471) B1513471
theorem B2019743 : Blo 896573 2019743 := bstep (se 1 (by rfl) ⟨1514807, by rfl⟩ : syracuseStep 2019743 = 3029615) B3029615
theorem B2019887 : Blo 896573 2019887 := bstep (se 1 (by rfl) ⟨1514915, by rfl⟩ : syracuseStep 2019887 = 3029831) B3029831
theorem B2020031 : Blo 896573 2020031 := bstep (se 1 (by rfl) ⟨1515023, by rfl⟩ : syracuseStep 2020031 = 3030047) B3030047
theorem B1921819 : Blo 896573 1921819 := bstep (se 1 (by rfl) ⟨1441364, by rfl⟩ : syracuseStep 1921819 = 2882729) B2882729
theorem B3232703 : Blo 896573 3232703 := bstep (se 1 (by rfl) ⟨2424527, by rfl⟩ : syracuseStep 3232703 = 4849055) B4849055
theorem B1299623 : Blo 896573 1299623 := bstep (se 1 (by rfl) ⟨974717, by rfl⟩ : syracuseStep 1299623 = 1949435) B1949435
theorem B2021543 : Blo 896573 2021543 := bstep (se 1 (by rfl) ⟨1516157, by rfl⟩ : syracuseStep 2021543 = 3032315) B3032315
theorem B7297199 : Blo 896573 7297199 := bstep (se 1 (by rfl) ⟨5472899, by rfl⟩ : syracuseStep 7297199 = 10945799) B10945799
theorem B3234433 : Blo 896573 3234433 := bstep (se 2 (by rfl) ⟨1212912, by rfl⟩ : syracuseStep 3234433 = 2425825) B2425825
theorem B4315943 : Blo 896573 4315943 := bstep (se 1 (by rfl) ⟨3236957, by rfl⟩ : syracuseStep 4315943 = 6473915) B6473915
theorem B4611563 : Blo 896573 4611563 := bstep (se 1 (by rfl) ⟨3458672, by rfl⟩ : syracuseStep 4611563 = 6917345) B6917345
theorem B2023451 : Blo 896573 2023451 := bstep (se 1 (by rfl) ⟨1517588, by rfl⟩ : syracuseStep 2023451 = 3035177) B3035177
theorem B6479999 : Blo 896573 6479999 := bstep (se 1 (by rfl) ⟨4859999, by rfl⟩ : syracuseStep 6479999 = 9719999) B9719999
theorem B2875655 : Blo 896573 2875655 := bstep (se 1 (by rfl) ⟨2156741, by rfl⟩ : syracuseStep 2875655 = 4313483) B4313483
theorem B11526857 : Blo 896573 11526857 := bstep (se 2 (by rfl) ⟨4322571, by rfl⟩ : syracuseStep 11526857 = 8645143) B8645143
theorem B2024531 : Blo 896573 2024531 := bstep (se 1 (by rfl) ⟨1518398, by rfl⟩ : syracuseStep 2024531 = 3036797) B3036797
theorem B8643995 : Blo 896573 8643995 := bstep (se 1 (by rfl) ⟨6482996, by rfl⟩ : syracuseStep 8643995 = 12965993) B12965993
theorem B2024873 : Blo 896573 2024873 := bstep (se 2 (by rfl) ⟨759327, by rfl⟩ : syracuseStep 2024873 = 1518655) B1518655
theorem B17952137 : Blo 896573 17952137 := bstep (se 2 (by rfl) ⟨6732051, by rfl⟩ : syracuseStep 17952137 = 13464103) B13464103
theorem B1011199 : Blo 896573 1011199 := bstep (se 1 (by rfl) ⟨758399, by rfl⟩ : syracuseStep 1011199 = 1516799) B1516799
theorem B1012207 : Blo 896573 1012207 := bstep (se 1 (by rfl) ⟨759155, by rfl⟩ : syracuseStep 1012207 = 1518311) B1518311
theorem B3405023 : Blo 896573 3405023 := bstep (se 1 (by rfl) ⟨2553767, by rfl⟩ : syracuseStep 3405023 = 5107535) B5107535
theorem B26277139 : Blo 896573 26277139 := bstep (se 1 (by rfl) ⟨19707854, by rfl⟩ : syracuseStep 26277139 = 39415709) B39415709
theorem B3798767 : Blo 896573 3798767 := bstep (se 1 (by rfl) ⟨2849075, by rfl⟩ : syracuseStep 3798767 = 5698151) B5698151
theorem B5765327 : Blo 896573 5765327 := bstep (se 1 (by rfl) ⟨4323995, by rfl⟩ : syracuseStep 5765327 = 8647991) B8647991
theorem B2914747 : Blo 896573 2914747 := bstep (se 1 (by rfl) ⟨2186060, by rfl⟩ : syracuseStep 2914747 = 4372121) B4372121
theorem B25852391 : Blo 896573 25852391 := bstep (se 1 (by rfl) ⟨19389293, by rfl⟩ : syracuseStep 25852391 = 38778587) B38778587
theorem B10255571 : Blo 896573 10255571 := bstep (se 1 (by rfl) ⟨7691678, by rfl⟩ : syracuseStep 10255571 = 15383357) B15383357
theorem B3243995 : Blo 896573 3243995 := bstep (se 1 (by rfl) ⟨2432996, by rfl⟩ : syracuseStep 3243995 = 4865993) B4865993
theorem B2557423 : Blo 896573 2557423 := bstep (se 1 (by rfl) ⟨1918067, by rfl⟩ : syracuseStep 2557423 = 3836135) B3836135
theorem B1345151 : Blo 896573 1345151 := bstep (se 1 (by rfl) ⟨1008863, by rfl⟩ : syracuseStep 1345151 = 2017727) B2017727
theorem B1345307 : Blo 896573 1345307 := bstep (se 1 (by rfl) ⟨1008980, by rfl⟩ : syracuseStep 1345307 = 2017961) B2017961
theorem B1705951 : Blo 896573 1705951 := bstep (se 1 (by rfl) ⟨1279463, by rfl⟩ : syracuseStep 1705951 = 2558927) B2558927
theorem B19401059 : Blo 896573 19401059 := bstep (se 1 (by rfl) ⟨14550794, by rfl⟩ : syracuseStep 19401059 = 29101589) B29101589
theorem B3410383 : Blo 896573 3410383 := bstep (se 1 (by rfl) ⟨2557787, by rfl⟩ : syracuseStep 3410383 = 5115575) B5115575
theorem B2460413 : Blo 896573 2460413 := bstep (se 3 (by rfl) ⟨461327, by rfl⟩ : syracuseStep 2460413 = 922655) B922655
theorem B3410855 : Blo 896573 3410855 := bstep (se 1 (by rfl) ⟨2558141, by rfl⟩ : syracuseStep 3410855 = 5116283) B5116283
theorem B1346495 : Blo 896573 1346495 := bstep (se 1 (by rfl) ⟨1009871, by rfl⟩ : syracuseStep 1346495 = 2019743) B2019743
theorem B1346591 : Blo 896573 1346591 := bstep (se 1 (by rfl) ⟨1009943, by rfl⟩ : syracuseStep 1346591 = 2019887) B2019887
theorem B1346687 : Blo 896573 1346687 := bstep (se 1 (by rfl) ⟨1010015, by rfl⟩ : syracuseStep 1346687 = 2020031) B2020031
theorem B5115257 : Blo 896573 5115257 := bstep (se 2 (by rfl) ⟨1918221, by rfl⟩ : syracuseStep 5115257 = 3836443) B3836443
theorem B1347695 : Blo 896573 1347695 := bstep (se 1 (by rfl) ⟨1010771, by rfl⟩ : syracuseStep 1347695 = 2021543) B2021543
theorem B10227869 : Blo 896573 10227869 := bstep (se 3 (by rfl) ⟨1917725, by rfl⟩ : syracuseStep 10227869 = 3835451) B3835451
theorem B1348265 : Blo 896573 1348265 := bstep (se 2 (by rfl) ⟨505599, by rfl⟩ : syracuseStep 1348265 = 1011199) B1011199
theorem B1348967 : Blo 896573 1348967 := bstep (se 1 (by rfl) ⟨1011725, by rfl⟩ : syracuseStep 1348967 = 2023451) B2023451
theorem B19404521 : Blo 896573 19404521 := bstep (se 2 (by rfl) ⟨7276695, by rfl⟩ : syracuseStep 19404521 = 14553391) B14553391
theorem B1349609 : Blo 896573 1349609 := bstep (se 2 (by rfl) ⟨506103, by rfl⟩ : syracuseStep 1349609 = 1012207) B1012207
theorem B1349687 : Blo 896573 1349687 := bstep (se 1 (by rfl) ⟨1012265, by rfl⟩ : syracuseStep 1349687 = 2024531) B2024531
theorem B1349915 : Blo 896573 1349915 := bstep (se 1 (by rfl) ⟨1012436, by rfl⟩ : syracuseStep 1349915 = 2024873) B2024873
theorem B2562425 : Blo 896573 2562425 := bstep (se 2 (by rfl) ⟨960909, by rfl⟩ : syracuseStep 2562425 = 1921819) B1921819
theorem B29104595 : Blo 896573 29104595 := bstep (se 1 (by rfl) ⟨21828446, by rfl⟩ : syracuseStep 29104595 = 43656893) B43656893
theorem B35036185 : Blo 896573 35036185 := bstep (se 2 (by rfl) ⟨13138569, by rfl⟩ : syracuseStep 35036185 = 26277139) B26277139
theorem B2563483 : Blo 896573 2563483 := bstep (se 1 (by rfl) ⟨1922612, by rfl⟩ : syracuseStep 2563483 = 3845225) B3845225
theorem B11968091 : Blo 896573 11968091 := bstep (se 1 (by rfl) ⟨8976068, by rfl⟩ : syracuseStep 11968091 = 17952137) B17952137
theorem B33660929 : Blo 896573 33660929 := bstep (se 2 (by rfl) ⟨12622848, by rfl⟩ : syracuseStep 33660929 = 25245697) B25245697
theorem B2270015 : Blo 896573 2270015 := bstep (se 1 (by rfl) ⟨1702511, by rfl⟩ : syracuseStep 2270015 = 3405023) B3405023
theorem B2532511 : Blo 896573 2532511 := bstep (se 1 (by rfl) ⟨1899383, by rfl⟩ : syracuseStep 2532511 = 3798767) B3798767
theorem B3843551 : Blo 896573 3843551 := bstep (se 1 (by rfl) ⟨2882663, by rfl⟩ : syracuseStep 3843551 = 5765327) B5765327
theorem B41527133 : Blo 896573 41527133 := bstep (se 3 (by rfl) ⟨7786337, by rfl⟩ : syracuseStep 41527133 = 15572675) B15572675
theorem B10364831 : Blo 896573 10364831 := bstep (se 1 (by rfl) ⟨7773623, by rfl⟩ : syracuseStep 10364831 = 15547247) B15547247
theorem B896751 : Blo 896573 896751 := bstep (se 1 (by rfl) ⟨672563, by rfl⟩ : syracuseStep 896751 = 1345127) B1345127
theorem B27701135 : Blo 896573 27701135 := bstep (se 1 (by rfl) ⟨20775851, by rfl⟩ : syracuseStep 27701135 = 41551703) B41551703
theorem B897135 : Blo 896573 897135 := bstep (se 1 (by rfl) ⟨672851, by rfl⟩ : syracuseStep 897135 = 1345703) B1345703
theorem B15545317 : Blo 896573 15545317 := bstep (se 4 (by rfl) ⟨1457373, by rfl⟩ : syracuseStep 15545317 = 2914747) B2914747
theorem B898527 : Blo 896573 898527 := bstep (se 1 (by rfl) ⟨673895, by rfl⟩ : syracuseStep 898527 = 1347791) B1347791
theorem B14595947 : Blo 896573 14595947 := bstep (se 1 (by rfl) ⟨10946960, by rfl⟩ : syracuseStep 14595947 = 21893921) B21893921
theorem B2406391 : Blo 896573 2406391 := bstep (se 1 (by rfl) ⟨1804793, by rfl⟩ : syracuseStep 2406391 = 3609587) B3609587
theorem B899231 : Blo 896573 899231 := bstep (se 1 (by rfl) ⟨674423, by rfl⟩ : syracuseStep 899231 = 1348847) B1348847
theorem B4864799 : Blo 896573 4864799 := bstep (se 1 (by rfl) ⟨3648599, by rfl⟩ : syracuseStep 4864799 = 7297199) B7297199
theorem B900287 : Blo 896573 900287 := bstep (se 1 (by rfl) ⟨675215, by rfl⟩ : syracuseStep 900287 = 1350431) B1350431
theorem B21872119 : Blo 896573 21872119 := bstep (se 1 (by rfl) ⟨16404089, by rfl⟩ : syracuseStep 21872119 = 32808179) B32808179
theorem B1917103 : Blo 896573 1917103 := bstep (se 1 (by rfl) ⟨1437827, by rfl⟩ : syracuseStep 1917103 = 2875655) B2875655
theorem B7684571 : Blo 896573 7684571 := bstep (se 1 (by rfl) ⟨5763428, by rfl⟩ : syracuseStep 7684571 = 11526857) B11526857
theorem B2279411 : Blo 896573 2279411 := bstep (se 1 (by rfl) ⟨1709558, by rfl⟩ : syracuseStep 2279411 = 3419117) B3419117
theorem B2017619 : Blo 896573 2017619 := bstep (se 1 (by rfl) ⟨1513214, by rfl⟩ : syracuseStep 2017619 = 3026429) B3026429
theorem B2018303 : Blo 896573 2018303 := bstep (se 1 (by rfl) ⟨1513727, by rfl⟩ : syracuseStep 2018303 = 3027455) B3027455
theorem B6835589 : Blo 896573 6835589 := bstep (se 4 (by rfl) ⟨640836, by rfl⟩ : syracuseStep 6835589 = 1281673) B1281673
theorem B2018735 : Blo 896573 2018735 := bstep (se 1 (by rfl) ⟨1514051, by rfl⟩ : syracuseStep 2018735 = 3028103) B3028103
theorem B4312577 : Blo 896573 4312577 := bstep (se 2 (by rfl) ⟨1617216, by rfl⟩ : syracuseStep 4312577 = 3234433) B3234433
theorem B6837047 : Blo 896573 6837047 := bstep (se 1 (by rfl) ⟨5127785, by rfl⟩ : syracuseStep 6837047 = 10255571) B10255571
theorem B2020193 : Blo 896573 2020193 := bstep (se 2 (by rfl) ⟨757572, by rfl⟩ : syracuseStep 2020193 = 1515145) B1515145
theorem B3069011 : Blo 896573 3069011 := bstep (se 1 (by rfl) ⟨2301758, by rfl⟩ : syracuseStep 3069011 = 4603517) B4603517
theorem B1823975 : Blo 896573 1823975 := bstep (se 1 (by rfl) ⟨1367981, by rfl⟩ : syracuseStep 1823975 = 2735963) B2735963
theorem B2022335 : Blo 896573 2022335 := bstep (se 1 (by rfl) ⟨1516751, by rfl⟩ : syracuseStep 2022335 = 3033503) B3033503
theorem B2022569 : Blo 896573 2022569 := bstep (se 2 (by rfl) ⟨758463, by rfl⟩ : syracuseStep 2022569 = 1516927) B1516927
theorem B1138207 : Blo 896573 1138207 := bstep (se 1 (by rfl) ⟨853655, by rfl⟩ : syracuseStep 1138207 = 1707311) B1707311
theorem B4546205 : Blo 896573 4546205 := bstep (se 3 (by rfl) ⟨852413, by rfl⟩ : syracuseStep 4546205 = 1704827) B1704827
theorem B3465661 : Blo 896573 3465661 := bstep (se 3 (by rfl) ⟨649811, by rfl⟩ : syracuseStep 3465661 = 1299623) B1299623
theorem B2155135 : Blo 896573 2155135 := bstep (se 1 (by rfl) ⟨1616351, by rfl⟩ : syracuseStep 2155135 = 3232703) B3232703
theorem B2024297 : Blo 896573 2024297 := bstep (se 2 (by rfl) ⟨759111, by rfl⟩ : syracuseStep 2024297 = 1518223) B1518223
theorem B43706101 : Blo 896573 43706101 := bstep (se 5 (by rfl) ⟨2048723, by rfl⟩ : syracuseStep 43706101 = 4097447) B4097447
theorem B2877295 : Blo 896573 2877295 := bstep (se 1 (by rfl) ⟨2157971, by rfl⟩ : syracuseStep 2877295 = 4315943) B4315943
theorem B3074375 : Blo 896573 3074375 := bstep (se 1 (by rfl) ⟨2305781, by rfl⟩ : syracuseStep 3074375 = 4611563) B4611563
theorem B7301609 : Blo 896573 7301609 := bstep (se 2 (by rfl) ⟨2738103, by rfl⟩ : syracuseStep 7301609 = 5476207) B5476207
theorem B4319999 : Blo 896573 4319999 := bstep (se 1 (by rfl) ⟨3239999, by rfl⟩ : syracuseStep 4319999 = 6479999) B6479999
theorem B5762663 : Blo 896573 5762663 := bstep (se 1 (by rfl) ⟨4321997, by rfl⟩ : syracuseStep 5762663 = 8643995) B8643995
theorem B42137333 : Blo 896573 42137333 := bstep (se 5 (by rfl) ⟨1975187, by rfl⟩ : syracuseStep 42137333 = 3950375) B3950375
theorem B17234927 : Blo 896573 17234927 := bstep (se 1 (by rfl) ⟨12926195, by rfl⟩ : syracuseStep 17234927 = 25852391) B25852391
theorem B2162663 : Blo 896573 2162663 := bstep (se 1 (by rfl) ⟨1621997, by rfl⟩ : syracuseStep 2162663 = 3243995) B3243995
theorem B2556137 : Blo 896573 2556137 := bstep (se 2 (by rfl) ⟨958551, by rfl⟩ : syracuseStep 2556137 = 1917103) B1917103
theorem B4620881 : Blo 896573 4620881 := bstep (se 2 (by rfl) ⟨1732830, by rfl⟩ : syracuseStep 4620881 = 3465661) B3465661
theorem B1345079 : Blo 896573 1345079 := bstep (se 1 (by rfl) ⟨1008809, by rfl⟩ : syracuseStep 1345079 = 2017619) B2017619
theorem B3409897 : Blo 896573 3409897 := bstep (se 2 (by rfl) ⟨1278711, by rfl⟩ : syracuseStep 3409897 = 2557423) B2557423
theorem B1345535 : Blo 896573 1345535 := bstep (se 1 (by rfl) ⟨1009151, by rfl⟩ : syracuseStep 1345535 = 2018303) B2018303
theorem B3410171 : Blo 896573 3410171 := bstep (se 1 (by rfl) ⟨2557628, by rfl⟩ : syracuseStep 3410171 = 5115257) B5115257
theorem B4557059 : Blo 896573 4557059 := bstep (se 1 (by rfl) ⟨3417794, by rfl⟩ : syracuseStep 4557059 = 6835589) B6835589
theorem B1345823 : Blo 896573 1345823 := bstep (se 1 (by rfl) ⟨1009367, by rfl⟩ : syracuseStep 1345823 = 2018735) B2018735
theorem B3836393 : Blo 896573 3836393 := bstep (se 2 (by rfl) ⟨1438647, by rfl⟩ : syracuseStep 3836393 = 2877295) B2877295
theorem B6818579 : Blo 896573 6818579 := bstep (se 1 (by rfl) ⟨5113934, by rfl⟩ : syracuseStep 6818579 = 10227869) B10227869
theorem B4558031 : Blo 896573 4558031 := bstep (se 1 (by rfl) ⟨3418523, by rfl⟩ : syracuseStep 4558031 = 6837047) B6837047
theorem B1346795 : Blo 896573 1346795 := bstep (se 1 (by rfl) ⟨1010096, by rfl⟩ : syracuseStep 1346795 = 2020193) B2020193
theorem B1215983 : Blo 896573 1215983 := bstep (se 1 (by rfl) ⟨911987, by rfl⟩ : syracuseStep 1215983 = 1823975) B1823975
theorem B1708283 : Blo 896573 1708283 := bstep (se 1 (by rfl) ⟨1281212, by rfl⟩ : syracuseStep 1708283 = 2562425) B2562425
theorem B19403063 : Blo 896573 19403063 := bstep (se 1 (by rfl) ⟨14552297, by rfl⟩ : syracuseStep 19403063 = 29104595) B29104595
theorem B1348223 : Blo 896573 1348223 := bstep (se 1 (by rfl) ⟨1011167, by rfl⟩ : syracuseStep 1348223 = 2022335) B2022335
theorem B1348379 : Blo 896573 1348379 := bstep (se 1 (by rfl) ⟨1011284, by rfl⟩ : syracuseStep 1348379 = 2022569) B2022569
theorem B1513343 : Blo 896573 1513343 := bstep (se 1 (by rfl) ⟨1135007, by rfl⟩ : syracuseStep 1513343 = 2270015) B2270015
theorem B1349531 : Blo 896573 1349531 := bstep (se 1 (by rfl) ⟨1012148, by rfl⟩ : syracuseStep 1349531 = 2024297) B2024297
theorem B13506725 : Blo 896573 13506725 := bstep (se 4 (by rfl) ⟨1266255, by rfl⟩ : syracuseStep 13506725 = 2532511) B2532511
theorem B8198333 : Blo 896573 8198333 := bstep (se 3 (by rfl) ⟨1537187, by rfl⟩ : syracuseStep 8198333 = 3074375) B3074375
theorem B2562367 : Blo 896573 2562367 := bstep (se 1 (by rfl) ⟨1921775, by rfl⟩ : syracuseStep 2562367 = 3843551) B3843551
theorem B6561101 : Blo 896573 6561101 := bstep (se 3 (by rfl) ⟨1230206, by rfl⟩ : syracuseStep 6561101 = 2460413) B2460413
theorem B3841775 : Blo 896573 3841775 := bstep (se 1 (by rfl) ⟨2881331, by rfl⟩ : syracuseStep 3841775 = 5762663) B5762663
theorem B28091555 : Blo 896573 28091555 := bstep (se 1 (by rfl) ⟨21068666, by rfl⟩ : syracuseStep 28091555 = 42137333) B42137333
theorem B3417977 : Blo 896573 3417977 := bstep (se 2 (by rfl) ⟨1281741, by rfl⟩ : syracuseStep 3417977 = 2563483) B2563483
theorem B1517609 : Blo 896573 1517609 := bstep (se 2 (by rfl) ⟨569103, by rfl⟩ : syracuseStep 1517609 = 1138207) B1138207
theorem B5123047 : Blo 896573 5123047 := bstep (se 1 (by rfl) ⟨3842285, by rfl⟩ : syracuseStep 5123047 = 7684571) B7684571
theorem B896767 : Blo 896573 896767 := bstep (se 1 (by rfl) ⟨672575, by rfl⟩ : syracuseStep 896767 = 1345151) B1345151
theorem B896871 : Blo 896573 896871 := bstep (se 1 (by rfl) ⟨672653, by rfl⟩ : syracuseStep 896871 = 1345307) B1345307
theorem B1519607 : Blo 896573 1519607 := bstep (se 1 (by rfl) ⟨1139705, by rfl⟩ : syracuseStep 1519607 = 2279411) B2279411
theorem B2273903 : Blo 896573 2273903 := bstep (se 1 (by rfl) ⟨1705427, by rfl⟩ : syracuseStep 2273903 = 3410855) B3410855
theorem B897663 : Blo 896573 897663 := bstep (se 1 (by rfl) ⟨673247, by rfl⟩ : syracuseStep 897663 = 1346495) B1346495
theorem B897727 : Blo 896573 897727 := bstep (se 1 (by rfl) ⟨673295, by rfl⟩ : syracuseStep 897727 = 1346591) B1346591
theorem B897791 : Blo 896573 897791 := bstep (se 1 (by rfl) ⟨673343, by rfl⟩ : syracuseStep 897791 = 1346687) B1346687
theorem B58274801 : Blo 896573 58274801 := bstep (se 2 (by rfl) ⟨21853050, by rfl⟩ : syracuseStep 58274801 = 43706101) B43706101
theorem B2274601 : Blo 896573 2274601 := bstep (se 2 (by rfl) ⟨852975, by rfl⟩ : syracuseStep 2274601 = 1705951) B1705951
theorem B898463 : Blo 896573 898463 := bstep (se 1 (by rfl) ⟨673847, by rfl⟩ : syracuseStep 898463 = 1347695) B1347695
theorem B898843 : Blo 896573 898843 := bstep (se 1 (by rfl) ⟨674132, by rfl⟩ : syracuseStep 898843 = 1348265) B1348265
theorem B2046007 : Blo 896573 2046007 := bstep (se 1 (by rfl) ⟨1534505, by rfl⟩ : syracuseStep 2046007 = 3069011) B3069011
theorem B899311 : Blo 896573 899311 := bstep (se 1 (by rfl) ⟨674483, by rfl⟩ : syracuseStep 899311 = 1348967) B1348967
theorem B899739 : Blo 896573 899739 := bstep (se 1 (by rfl) ⟨674804, by rfl⟩ : syracuseStep 899739 = 1349609) B1349609
theorem B899791 : Blo 896573 899791 := bstep (se 1 (by rfl) ⟨674843, by rfl⟩ : syracuseStep 899791 = 1349687) B1349687
theorem B899943 : Blo 896573 899943 := bstep (se 1 (by rfl) ⟨674957, by rfl⟩ : syracuseStep 899943 = 1349915) B1349915
theorem B7978727 : Blo 896573 7978727 := bstep (se 1 (by rfl) ⟨5984045, by rfl⟩ : syracuseStep 7978727 = 11968091) B11968091
theorem B3030803 : Blo 896573 3030803 := bstep (se 1 (by rfl) ⟨2273102, by rfl⟩ : syracuseStep 3030803 = 4546205) B4546205
theorem B20727089 : Blo 896573 20727089 := bstep (se 2 (by rfl) ⟨7772658, by rfl⟩ : syracuseStep 20727089 = 15545317) B15545317
theorem B4867739 : Blo 896573 4867739 := bstep (se 1 (by rfl) ⟨3650804, by rfl⟩ : syracuseStep 4867739 = 7301609) B7301609
theorem B18467423 : Blo 896573 18467423 := bstep (se 1 (by rfl) ⟨13850567, by rfl⟩ : syracuseStep 18467423 = 27701135) B27701135
theorem B46714913 : Blo 896573 46714913 := bstep (se 2 (by rfl) ⟨17518092, by rfl⟩ : syracuseStep 46714913 = 35036185) B35036185
theorem B11489951 : Blo 896573 11489951 := bstep (se 1 (by rfl) ⟨8617463, by rfl⟩ : syracuseStep 11489951 = 17234927) B17234927
theorem B51336341 : Blo 896573 51336341 := bstep (se 6 (by rfl) ⟨1203195, by rfl⟩ : syracuseStep 51336341 = 2406391) B2406391
theorem B2873513 : Blo 896573 2873513 := bstep (se 2 (by rfl) ⟨1077567, by rfl⟩ : syracuseStep 2873513 = 2155135) B2155135
theorem B12934039 : Blo 896573 12934039 := bstep (se 1 (by rfl) ⟨9700529, by rfl⟩ : syracuseStep 12934039 = 19401059) B19401059
theorem B2875051 : Blo 896573 2875051 := bstep (se 1 (by rfl) ⟨2156288, by rfl⟩ : syracuseStep 2875051 = 4312577) B4312577
theorem B4547177 : Blo 896573 4547177 := bstep (se 2 (by rfl) ⟨1705191, by rfl⟩ : syracuseStep 4547177 = 3410383) B3410383
theorem B12936347 : Blo 896573 12936347 := bstep (se 1 (by rfl) ⟨9702260, by rfl⟩ : syracuseStep 12936347 = 19404521) B19404521
theorem B22440619 : Blo 896573 22440619 := bstep (se 1 (by rfl) ⟨16830464, by rfl⟩ : syracuseStep 22440619 = 33660929) B33660929
theorem B27684755 : Blo 896573 27684755 := bstep (se 1 (by rfl) ⟨20763566, by rfl⟩ : syracuseStep 27684755 = 41527133) B41527133
theorem B6909887 : Blo 896573 6909887 := bstep (se 1 (by rfl) ⟨5182415, by rfl⟩ : syracuseStep 6909887 = 10364831) B10364831
theorem B2879999 : Blo 896573 2879999 := bstep (se 1 (by rfl) ⟨2159999, by rfl⟩ : syracuseStep 2879999 = 4319999) B4319999
theorem B9730631 : Blo 896573 9730631 := bstep (se 1 (by rfl) ⟨7297973, by rfl⟩ : syracuseStep 9730631 = 14595947) B14595947
theorem B3243199 : Blo 896573 3243199 := bstep (se 1 (by rfl) ⟨2432399, by rfl⟩ : syracuseStep 3243199 = 4864799) B4864799
theorem B29162825 : Blo 896573 29162825 := bstep (se 2 (by rfl) ⟨10936059, by rfl⟩ : syracuseStep 29162825 = 21872119) B21872119
theorem B1441775 : Blo 896573 1441775 := bstep (se 1 (by rfl) ⟨1081331, by rfl⟩ : syracuseStep 1441775 = 2162663) B2162663
theorem B1704091 : Blo 896573 1704091 := bstep (se 1 (by rfl) ⟨1278068, by rfl⟩ : syracuseStep 1704091 = 2556137) B2556137
theorem B3080587 : Blo 896573 3080587 := bstep (se 1 (by rfl) ⟨2310440, by rfl⟩ : syracuseStep 3080587 = 4620881) B4620881
theorem B3245159 : Blo 896573 3245159 := bstep (se 1 (by rfl) ⟨2433869, by rfl⟩ : syracuseStep 3245159 = 4867739) B4867739
theorem B2557595 : Blo 896573 2557595 := bstep (se 1 (by rfl) ⟨1918196, by rfl⟩ : syracuseStep 2557595 = 3836393) B3836393
theorem B29920825 : Blo 896573 29920825 := bstep (se 2 (by rfl) ⟨11220309, by rfl⟩ : syracuseStep 29920825 = 22440619) B22440619
theorem B2561183 : Blo 896573 2561183 := bstep (se 1 (by rfl) ⟨1920887, by rfl⟩ : syracuseStep 2561183 = 3841775) B3841775
theorem B8624231 : Blo 896573 8624231 := bstep (se 1 (by rfl) ⟨6468173, by rfl⟩ : syracuseStep 8624231 = 12936347) B12936347
theorem B18456503 : Blo 896573 18456503 := bstep (se 1 (by rfl) ⟨13842377, by rfl⟩ : syracuseStep 18456503 = 27684755) B27684755
theorem B2728009 : Blo 896573 2728009 := bstep (se 2 (by rfl) ⟨1023003, by rfl⟩ : syracuseStep 2728009 = 2046007) B2046007
theorem B1515935 : Blo 896573 1515935 := bstep (se 1 (by rfl) ⟨1136951, by rfl⟩ : syracuseStep 1515935 = 2273903) B2273903
theorem B3416489 : Blo 896573 3416489 := bstep (se 2 (by rfl) ⟨1281183, by rfl⟩ : syracuseStep 3416489 = 2562367) B2562367
theorem B17245385 : Blo 896573 17245385 := bstep (se 2 (by rfl) ⟨6467019, by rfl⟩ : syracuseStep 17245385 = 12934039) B12934039
theorem B21276605 : Blo 896573 21276605 := bstep (se 3 (by rfl) ⟨3989363, by rfl⟩ : syracuseStep 21276605 = 7978727) B7978727
theorem B19441883 : Blo 896573 19441883 := bstep (se 1 (by rfl) ⟨14581412, by rfl⟩ : syracuseStep 19441883 = 29162825) B29162825
theorem B18426365 : Blo 896573 18426365 := bstep (se 3 (by rfl) ⟨3454943, by rfl⟩ : syracuseStep 18426365 = 6909887) B6909887
theorem B961183 : Blo 896573 961183 := bstep (se 1 (by rfl) ⟨720887, by rfl⟩ : syracuseStep 961183 = 1441775) B1441775
theorem B896719 : Blo 896573 896719 := bstep (se 1 (by rfl) ⟨672539, by rfl⟩ : syracuseStep 896719 = 1345079) B1345079
theorem B897023 : Blo 896573 897023 := bstep (se 1 (by rfl) ⟨672767, by rfl⟩ : syracuseStep 897023 = 1345535) B1345535
theorem B2273447 : Blo 896573 2273447 := bstep (se 1 (by rfl) ⟨1705085, by rfl⟩ : syracuseStep 2273447 = 3410171) B3410171
theorem B897215 : Blo 896573 897215 := bstep (se 1 (by rfl) ⟨672911, by rfl⟩ : syracuseStep 897215 = 1345823) B1345823
theorem B897863 : Blo 896573 897863 := bstep (se 1 (by rfl) ⟨673397, by rfl⟩ : syracuseStep 897863 = 1346795) B1346795
theorem B31143275 : Blo 896573 31143275 := bstep (se 1 (by rfl) ⟨23357456, by rfl⟩ : syracuseStep 31143275 = 46714913) B46714913
theorem B898815 : Blo 896573 898815 := bstep (se 1 (by rfl) ⟨674111, by rfl⟩ : syracuseStep 898815 = 1348223) B1348223
theorem B898919 : Blo 896573 898919 := bstep (se 1 (by rfl) ⟨674189, by rfl⟩ : syracuseStep 898919 = 1348379) B1348379
theorem B34224227 : Blo 896573 34224227 := bstep (se 1 (by rfl) ⟨25668170, by rfl⟩ : syracuseStep 34224227 = 51336341) B51336341
theorem B899687 : Blo 896573 899687 := bstep (se 1 (by rfl) ⟨674765, by rfl⟩ : syracuseStep 899687 = 1349531) B1349531
theorem B6830729 : Blo 896573 6830729 := bstep (se 2 (by rfl) ⟨2561523, by rfl⟩ : syracuseStep 6830729 = 5123047) B5123047
theorem B4374067 : Blo 896573 4374067 := bstep (se 1 (by rfl) ⟨3280550, by rfl⟩ : syracuseStep 4374067 = 6561101) B6561101
theorem B3031451 : Blo 896573 3031451 := bstep (se 1 (by rfl) ⟨2273588, by rfl⟩ : syracuseStep 3031451 = 4547177) B4547177
theorem B18727703 : Blo 896573 18727703 := bstep (se 1 (by rfl) ⟨14045777, by rfl⟩ : syracuseStep 18727703 = 28091555) B28091555
theorem B2278651 : Blo 896573 2278651 := bstep (se 1 (by rfl) ⟨1708988, by rfl⟩ : syracuseStep 2278651 = 3417977) B3417977
theorem B3032801 : Blo 896573 3032801 := bstep (se 2 (by rfl) ⟨1137300, by rfl⟩ : syracuseStep 3032801 = 2274601) B2274601
theorem B1919999 : Blo 896573 1919999 := bstep (se 1 (by rfl) ⟨1439999, by rfl⟩ : syracuseStep 1919999 = 2879999) B2879999
theorem B38849867 : Blo 896573 38849867 := bstep (se 1 (by rfl) ⟨29137400, by rfl⟩ : syracuseStep 38849867 = 58274801) B58274801
theorem B2020535 : Blo 896573 2020535 := bstep (se 1 (by rfl) ⟨1515401, by rfl⟩ : syracuseStep 2020535 = 3030803) B3030803
theorem B13818059 : Blo 896573 13818059 := bstep (se 1 (by rfl) ⟨10363544, by rfl⟩ : syracuseStep 13818059 = 20727089) B20727089
theorem B3038039 : Blo 896573 3038039 := bstep (se 1 (by rfl) ⟨2278529, by rfl⟩ : syracuseStep 3038039 = 4557059) B4557059
theorem B12311615 : Blo 896573 12311615 := bstep (se 1 (by rfl) ⟨9233711, by rfl⟩ : syracuseStep 12311615 = 18467423) B18467423
theorem B4545719 : Blo 896573 4545719 := bstep (se 1 (by rfl) ⟨3409289, by rfl⟩ : syracuseStep 4545719 = 6818579) B6818579
theorem B3038687 : Blo 896573 3038687 := bstep (se 1 (by rfl) ⟨2279015, by rfl⟩ : syracuseStep 3038687 = 4558031) B4558031
theorem B4546529 : Blo 896573 4546529 := bstep (se 2 (by rfl) ⟨1704948, by rfl⟩ : syracuseStep 4546529 = 3409897) B3409897
theorem B1138855 : Blo 896573 1138855 := bstep (se 1 (by rfl) ⟨854141, by rfl⟩ : syracuseStep 1138855 = 1708283) B1708283
theorem B12935375 : Blo 896573 12935375 := bstep (se 1 (by rfl) ⟨9701531, by rfl⟩ : syracuseStep 12935375 = 19403063) B19403063
theorem B7659967 : Blo 896573 7659967 := bstep (se 1 (by rfl) ⟨5744975, by rfl⟩ : syracuseStep 7659967 = 11489951) B11489951
theorem B1008895 : Blo 896573 1008895 := bstep (se 1 (by rfl) ⟨756671, by rfl⟩ : syracuseStep 1008895 = 1513343) B1513343
theorem B9004483 : Blo 896573 9004483 := bstep (se 1 (by rfl) ⟨6753362, by rfl⟩ : syracuseStep 9004483 = 13506725) B13506725
theorem B5465555 : Blo 896573 5465555 := bstep (se 1 (by rfl) ⟨4099166, by rfl⟩ : syracuseStep 5465555 = 8198333) B8198333
theorem B7662701 : Blo 896573 7662701 := bstep (se 3 (by rfl) ⟨1436756, by rfl⟩ : syracuseStep 7662701 = 2873513) B2873513
theorem B1011739 : Blo 896573 1011739 := bstep (se 1 (by rfl) ⟨758804, by rfl⟩ : syracuseStep 1011739 = 1517609) B1517609
theorem B1013071 : Blo 896573 1013071 := bstep (se 1 (by rfl) ⟨759803, by rfl⟩ : syracuseStep 1013071 = 1519607) B1519607
theorem B3242621 : Blo 896573 3242621 := bstep (se 3 (by rfl) ⟨607991, by rfl⟩ : syracuseStep 3242621 = 1215983) B1215983
theorem B4324265 : Blo 896573 4324265 := bstep (se 2 (by rfl) ⟨1621599, by rfl⟩ : syracuseStep 4324265 = 3243199) B3243199
theorem B6487087 : Blo 896573 6487087 := bstep (se 1 (by rfl) ⟨4865315, by rfl⟩ : syracuseStep 6487087 = 9730631) B9730631
theorem B3833401 : Blo 896573 3833401 := bstep (se 2 (by rfl) ⟨1437525, by rfl⟩ : syracuseStep 3833401 = 2875051) B2875051
theorem B14549381 : Blo 896573 14549381 := bstep (se 4 (by rfl) ⟨1364004, by rfl⟩ : syracuseStep 14549381 = 2728009) B2728009
theorem B12485135 : Blo 896573 12485135 := bstep (se 1 (by rfl) ⟨9363851, by rfl⟩ : syracuseStep 12485135 = 18727703) B18727703
theorem B2163439 : Blo 896573 2163439 := bstep (se 1 (by rfl) ⟨1622579, by rfl⟩ : syracuseStep 2163439 = 3245159) B3245159
theorem B1705063 : Blo 896573 1705063 := bstep (se 1 (by rfl) ⟨1278797, by rfl⟩ : syracuseStep 1705063 = 2557595) B2557595
theorem B1345193 : Blo 896573 1345193 := bstep (se 2 (by rfl) ⟨504447, by rfl⟩ : syracuseStep 1345193 = 1008895) B1008895
theorem B1279999 : Blo 896573 1279999 := bstep (se 1 (by rfl) ⟨959999, by rfl⟩ : syracuseStep 1279999 = 1919999) B1919999
theorem B1707455 : Blo 896573 1707455 := bstep (se 1 (by rfl) ⟨1280591, by rfl⟩ : syracuseStep 1707455 = 2561183) B2561183
theorem B1347023 : Blo 896573 1347023 := bstep (se 1 (by rfl) ⟨1010267, by rfl⟩ : syracuseStep 1347023 = 2020535) B2020535
theorem B1281577 : Blo 896573 1281577 := bstep (se 2 (by rfl) ⟨480591, by rfl⟩ : syracuseStep 1281577 = 961183) B961183
theorem B9212039 : Blo 896573 9212039 := bstep (se 1 (by rfl) ⟨6909029, by rfl⟩ : syracuseStep 9212039 = 13818059) B13818059
theorem B1348985 : Blo 896573 1348985 := bstep (se 2 (by rfl) ⟨505869, by rfl⟩ : syracuseStep 1348985 = 1011739) B1011739
theorem B8623583 : Blo 896573 8623583 := bstep (se 1 (by rfl) ⟨6467687, by rfl⟩ : syracuseStep 8623583 = 12935375) B12935375
theorem B51845021 : Blo 896573 51845021 := bstep (se 3 (by rfl) ⟨9720941, by rfl⟩ : syracuseStep 51845021 = 19441883) B19441883
theorem B3643703 : Blo 896573 3643703 := bstep (se 1 (by rfl) ⟨2732777, by rfl⟩ : syracuseStep 3643703 = 5465555) B5465555
theorem B1350761 : Blo 896573 1350761 := bstep (se 2 (by rfl) ⟨506535, by rfl⟩ : syracuseStep 1350761 = 1013071) B1013071
theorem B1515631 : Blo 896573 1515631 := bstep (se 1 (by rfl) ⟨1136723, by rfl⟩ : syracuseStep 1515631 = 2273447) B2273447
theorem B22816151 : Blo 896573 22816151 := bstep (se 1 (by rfl) ⟨17112113, by rfl⟩ : syracuseStep 22816151 = 34224227) B34224227
theorem B2272121 : Blo 896573 2272121 := bstep (se 2 (by rfl) ⟨852045, by rfl⟩ : syracuseStep 2272121 = 1704091) B1704091
theorem B1518473 : Blo 896573 1518473 := bstep (se 2 (by rfl) ⟨569427, by rfl⟩ : syracuseStep 1518473 = 1138855) B1138855
theorem B4107449 : Blo 896573 4107449 := bstep (se 2 (by rfl) ⟨1540293, by rfl⟩ : syracuseStep 4107449 = 3080587) B3080587
theorem B12005977 : Blo 896573 12005977 := bstep (se 2 (by rfl) ⟨4502241, by rfl⟩ : syracuseStep 12005977 = 9004483) B9004483
theorem B25899911 : Blo 896573 25899911 := bstep (se 1 (by rfl) ⟨19424933, by rfl⟩ : syracuseStep 25899911 = 38849867) B38849867
theorem B5749487 : Blo 896573 5749487 := bstep (se 1 (by rfl) ⟨4312115, by rfl⟩ : syracuseStep 5749487 = 8624231) B8624231
theorem B8207743 : Blo 896573 8207743 := bstep (se 1 (by rfl) ⟨6155807, by rfl⟩ : syracuseStep 8207743 = 12311615) B12311615
theorem B39894433 : Blo 896573 39894433 := bstep (se 2 (by rfl) ⟨14960412, by rfl⟩ : syracuseStep 39894433 = 29920825) B29920825
theorem B3030479 : Blo 896573 3030479 := bstep (se 1 (by rfl) ⟨2272859, by rfl⟩ : syracuseStep 3030479 = 4545719) B4545719
theorem B56737613 : Blo 896573 56737613 := bstep (se 3 (by rfl) ⟨10638302, by rfl⟩ : syracuseStep 56737613 = 21276605) B21276605
theorem B3031019 : Blo 896573 3031019 := bstep (se 1 (by rfl) ⟨2273264, by rfl⟩ : syracuseStep 3031019 = 4546529) B4546529
theorem B2277659 : Blo 896573 2277659 := bstep (se 1 (by rfl) ⟨1708244, by rfl⟩ : syracuseStep 2277659 = 3416489) B3416489
theorem B20762183 : Blo 896573 20762183 := bstep (se 1 (by rfl) ⟨15571637, by rfl⟩ : syracuseStep 20762183 = 31143275) B31143275
theorem B2020967 : Blo 896573 2020967 := bstep (se 1 (by rfl) ⟨1515725, by rfl⟩ : syracuseStep 2020967 = 3031451) B3031451
theorem B10213289 : Blo 896573 10213289 := bstep (se 2 (by rfl) ⟨3829983, by rfl⟩ : syracuseStep 10213289 = 7659967) B7659967
theorem B2021867 : Blo 896573 2021867 := bstep (se 1 (by rfl) ⟨1516400, by rfl⟩ : syracuseStep 2021867 = 3032801) B3032801
theorem B3038201 : Blo 896573 3038201 := bstep (se 2 (by rfl) ⟨1139325, by rfl⟩ : syracuseStep 3038201 = 2278651) B2278651
theorem B2025359 : Blo 896573 2025359 := bstep (se 1 (by rfl) ⟨1519019, by rfl⟩ : syracuseStep 2025359 = 3038039) B3038039
theorem B2025791 : Blo 896573 2025791 := bstep (se 1 (by rfl) ⟨1519343, by rfl⟩ : syracuseStep 2025791 = 3038687) B3038687
theorem B1010623 : Blo 896573 1010623 := bstep (se 1 (by rfl) ⟨757967, by rfl⟩ : syracuseStep 1010623 = 1515935) B1515935
theorem B11496923 : Blo 896573 11496923 := bstep (se 1 (by rfl) ⟨8622692, by rfl⟩ : syracuseStep 11496923 = 17245385) B17245385
theorem B12284243 : Blo 896573 12284243 := bstep (se 1 (by rfl) ⟨9213182, by rfl⟩ : syracuseStep 12284243 = 18426365) B18426365
theorem B5108467 : Blo 896573 5108467 := bstep (se 1 (by rfl) ⟨3831350, by rfl⟩ : syracuseStep 5108467 = 7662701) B7662701
theorem B8649449 : Blo 896573 8649449 := bstep (se 2 (by rfl) ⟨3243543, by rfl⟩ : syracuseStep 8649449 = 6487087) B6487087
theorem B2161747 : Blo 896573 2161747 := bstep (se 1 (by rfl) ⟨1621310, by rfl⟩ : syracuseStep 2161747 = 3242621) B3242621
theorem B4553819 : Blo 896573 4553819 := bstep (se 1 (by rfl) ⟨3415364, by rfl⟩ : syracuseStep 4553819 = 6830729) B6830729
theorem B2882843 : Blo 896573 2882843 := bstep (se 1 (by rfl) ⟨2162132, by rfl⟩ : syracuseStep 2882843 = 4324265) B4324265
theorem B5832089 : Blo 896573 5832089 := bstep (se 2 (by rfl) ⟨2187033, by rfl⟩ : syracuseStep 5832089 = 4374067) B4374067
theorem B5111201 : Blo 896573 5111201 := bstep (se 2 (by rfl) ⟨1916700, by rfl⟩ : syracuseStep 5111201 = 3833401) B3833401
theorem B49217341 : Blo 896573 49217341 := bstep (se 3 (by rfl) ⟨9228251, by rfl⟩ : syracuseStep 49217341 = 18456503) B18456503
theorem B9699587 : Blo 896573 9699587 := bstep (se 1 (by rfl) ⟨7274690, by rfl⟩ : syracuseStep 9699587 = 14549381) B14549381
theorem B2884585 : Blo 896573 2884585 := bstep (se 2 (by rfl) ⟨1081719, by rfl⟩ : syracuseStep 2884585 = 2163439) B2163439
theorem B33293693 : Blo 896573 33293693 := bstep (se 3 (by rfl) ⟨6242567, by rfl⟩ : syracuseStep 33293693 = 12485135) B12485135
theorem B1706665 : Blo 896573 1706665 := bstep (se 2 (by rfl) ⟨639999, by rfl⟩ : syracuseStep 1706665 = 1279999) B1279999
theorem B1347311 : Blo 896573 1347311 := bstep (se 1 (by rfl) ⟨1010483, by rfl⟩ : syracuseStep 1347311 = 2020967) B2020967
theorem B1347497 : Blo 896573 1347497 := bstep (se 2 (by rfl) ⟨505311, by rfl⟩ : syracuseStep 1347497 = 1010623) B1010623
theorem B2429135 : Blo 896573 2429135 := bstep (se 1 (by rfl) ⟨1821851, by rfl⟩ : syracuseStep 2429135 = 3643703) B3643703
theorem B1347911 : Blo 896573 1347911 := bstep (se 1 (by rfl) ⟨1010933, by rfl⟩ : syracuseStep 1347911 = 2021867) B2021867
theorem B1708769 : Blo 896573 1708769 := bstep (se 2 (by rfl) ⟨640788, by rfl⟩ : syracuseStep 1708769 = 1281577) B1281577
theorem B15210767 : Blo 896573 15210767 := bstep (se 1 (by rfl) ⟨11408075, by rfl⟩ : syracuseStep 15210767 = 22816151) B22816151
theorem B1350239 : Blo 896573 1350239 := bstep (se 1 (by rfl) ⟨1012679, by rfl⟩ : syracuseStep 1350239 = 2025359) B2025359
theorem B1350527 : Blo 896573 1350527 := bstep (se 1 (by rfl) ⟨1012895, by rfl⟩ : syracuseStep 1350527 = 2025791) B2025791
theorem B1514747 : Blo 896573 1514747 := bstep (se 1 (by rfl) ⟨1136060, by rfl⟩ : syracuseStep 1514747 = 2272121) B2272121
theorem B212770309 : Blo 896573 212770309 := bstep (se 4 (by rfl) ⟨19947216, by rfl⟩ : syracuseStep 212770309 = 39894433) B39894433
theorem B37825075 : Blo 896573 37825075 := bstep (se 1 (by rfl) ⟨28368806, by rfl⟩ : syracuseStep 37825075 = 56737613) B56737613
theorem B1518439 : Blo 896573 1518439 := bstep (se 1 (by rfl) ⟨1138829, by rfl⟩ : syracuseStep 1518439 = 2277659) B2277659
theorem B896795 : Blo 896573 896795 := bstep (se 1 (by rfl) ⟨672596, by rfl⟩ : syracuseStep 896795 = 1345193) B1345193
theorem B2273417 : Blo 896573 2273417 := bstep (se 2 (by rfl) ⟨852531, by rfl⟩ : syracuseStep 2273417 = 1705063) B1705063
theorem B898015 : Blo 896573 898015 := bstep (se 1 (by rfl) ⟨673511, by rfl⟩ : syracuseStep 898015 = 1347023) B1347023
theorem B13841455 : Blo 896573 13841455 := bstep (se 1 (by rfl) ⟨10381091, by rfl⟩ : syracuseStep 13841455 = 20762183) B20762183
theorem B6141359 : Blo 896573 6141359 := bstep (se 1 (by rfl) ⟨4606019, by rfl⟩ : syracuseStep 6141359 = 9212039) B9212039
theorem B899323 : Blo 896573 899323 := bstep (se 1 (by rfl) ⟨674492, by rfl⟩ : syracuseStep 899323 = 1348985) B1348985
theorem B5749055 : Blo 896573 5749055 := bstep (se 1 (by rfl) ⟨4311791, by rfl⟩ : syracuseStep 5749055 = 8623583) B8623583
theorem B900507 : Blo 896573 900507 := bstep (se 1 (by rfl) ⟨675380, by rfl⟩ : syracuseStep 900507 = 1350761) B1350761
theorem B16007969 : Blo 896573 16007969 := bstep (se 2 (by rfl) ⟨6002988, by rfl⟩ : syracuseStep 16007969 = 12005977) B12005977
theorem B2738299 : Blo 896573 2738299 := bstep (se 1 (by rfl) ⟨2053724, by rfl⟩ : syracuseStep 2738299 = 4107449) B4107449
theorem B3035879 : Blo 896573 3035879 := bstep (se 1 (by rfl) ⟨2276909, by rfl⟩ : syracuseStep 3035879 = 4553819) B4553819
theorem B1921895 : Blo 896573 1921895 := bstep (se 1 (by rfl) ⟨1441421, by rfl⟩ : syracuseStep 1921895 = 2882843) B2882843
theorem B3888059 : Blo 896573 3888059 := bstep (se 1 (by rfl) ⟨2916044, by rfl⟩ : syracuseStep 3888059 = 5832089) B5832089
theorem B2020319 : Blo 896573 2020319 := bstep (se 1 (by rfl) ⟨1515239, by rfl⟩ : syracuseStep 2020319 = 3030479) B3030479
theorem B65623121 : Blo 896573 65623121 := bstep (se 2 (by rfl) ⟨24608670, by rfl⟩ : syracuseStep 65623121 = 49217341) B49217341
theorem B2020679 : Blo 896573 2020679 := bstep (se 1 (by rfl) ⟨1515509, by rfl⟩ : syracuseStep 2020679 = 3031019) B3031019
theorem B2020841 : Blo 896573 2020841 := bstep (se 2 (by rfl) ⟨757815, by rfl⟩ : syracuseStep 2020841 = 1515631) B1515631
theorem B1138303 : Blo 896573 1138303 := bstep (se 1 (by rfl) ⟨853727, by rfl⟩ : syracuseStep 1138303 = 1707455) B1707455
theorem B34563347 : Blo 896573 34563347 := bstep (se 1 (by rfl) ⟨25922510, by rfl⟩ : syracuseStep 34563347 = 51845021) B51845021
theorem B6808859 : Blo 896573 6808859 := bstep (se 1 (by rfl) ⟨5106644, by rfl⟩ : syracuseStep 6808859 = 10213289) B10213289
theorem B2025467 : Blo 896573 2025467 := bstep (se 1 (by rfl) ⟨1519100, by rfl⟩ : syracuseStep 2025467 = 3038201) B3038201
theorem B11529317 : Blo 896573 11529317 := bstep (se 4 (by rfl) ⟨1080873, by rfl⟩ : syracuseStep 11529317 = 2161747) B2161747
theorem B6811289 : Blo 896573 6811289 := bstep (se 2 (by rfl) ⟨2554233, by rfl⟩ : syracuseStep 6811289 = 5108467) B5108467
theorem B1012315 : Blo 896573 1012315 := bstep (se 1 (by rfl) ⟨759236, by rfl⟩ : syracuseStep 1012315 = 1518473) B1518473
theorem B7664615 : Blo 896573 7664615 := bstep (se 1 (by rfl) ⟨5748461, by rfl⟩ : syracuseStep 7664615 = 11496923) B11496923
theorem B8189495 : Blo 896573 8189495 := bstep (se 1 (by rfl) ⟨6142121, by rfl⟩ : syracuseStep 8189495 = 12284243) B12284243
theorem B17266607 : Blo 896573 17266607 := bstep (se 1 (by rfl) ⟨12949955, by rfl⟩ : syracuseStep 17266607 = 25899911) B25899911
theorem B5766299 : Blo 896573 5766299 := bstep (se 1 (by rfl) ⟨4324724, by rfl⟩ : syracuseStep 5766299 = 8649449) B8649449
theorem B3832991 : Blo 896573 3832991 := bstep (se 1 (by rfl) ⟨2874743, by rfl⟩ : syracuseStep 3832991 = 5749487) B5749487
theorem B10943657 : Blo 896573 10943657 := bstep (se 2 (by rfl) ⟨4103871, by rfl⟩ : syracuseStep 10943657 = 8207743) B8207743
theorem B3407467 : Blo 896573 3407467 := bstep (se 1 (by rfl) ⟨2555600, by rfl⟩ : syracuseStep 3407467 = 5111201) B5111201
theorem B1281263 : Blo 896573 1281263 := bstep (se 1 (by rfl) ⟨960947, by rfl⟩ : syracuseStep 1281263 = 1921895) B1921895
theorem B1346879 : Blo 896573 1346879 := bstep (se 1 (by rfl) ⟨1010159, by rfl⟩ : syracuseStep 1346879 = 2020319) B2020319
theorem B43748747 : Blo 896573 43748747 := bstep (se 1 (by rfl) ⟨32811560, by rfl⟩ : syracuseStep 43748747 = 65623121) B65623121
theorem B1347119 : Blo 896573 1347119 := bstep (se 1 (by rfl) ⟨1010339, by rfl⟩ : syracuseStep 1347119 = 2020679) B2020679
theorem B1347227 : Blo 896573 1347227 := bstep (se 1 (by rfl) ⟨1010420, by rfl⟩ : syracuseStep 1347227 = 2020841) B2020841
theorem B1349753 : Blo 896573 1349753 := bstep (se 2 (by rfl) ⟨506157, by rfl⟩ : syracuseStep 1349753 = 1012315) B1012315
theorem B23042231 : Blo 896573 23042231 := bstep (se 1 (by rfl) ⟨17281673, by rfl⟩ : syracuseStep 23042231 = 34563347) B34563347
theorem B1350311 : Blo 896573 1350311 := bstep (se 1 (by rfl) ⟨1012733, by rfl⟩ : syracuseStep 1350311 = 2025467) B2025467
theorem B18455273 : Blo 896573 18455273 := bstep (se 2 (by rfl) ⟨6920727, by rfl⟩ : syracuseStep 18455273 = 13841455) B13841455
theorem B1515611 : Blo 896573 1515611 := bstep (se 1 (by rfl) ⟨1136708, by rfl⟩ : syracuseStep 1515611 = 2273417) B2273417
theorem B11511071 : Blo 896573 11511071 := bstep (se 1 (by rfl) ⟨8633303, by rfl⟩ : syracuseStep 11511071 = 17266607) B17266607
theorem B3844199 : Blo 896573 3844199 := bstep (se 1 (by rfl) ⟨2883149, by rfl⟩ : syracuseStep 3844199 = 5766299) B5766299
theorem B1517737 : Blo 896573 1517737 := bstep (se 2 (by rfl) ⟨569151, by rfl⟩ : syracuseStep 1517737 = 1138303) B1138303
theorem B6466391 : Blo 896573 6466391 := bstep (se 1 (by rfl) ⟨4849793, by rfl⟩ : syracuseStep 6466391 = 9699587) B9699587
theorem B22195795 : Blo 896573 22195795 := bstep (se 1 (by rfl) ⟨16646846, by rfl⟩ : syracuseStep 22195795 = 33293693) B33293693
theorem B3846113 : Blo 896573 3846113 := bstep (se 2 (by rfl) ⟨1442292, by rfl⟩ : syracuseStep 3846113 = 2884585) B2884585
theorem B10368157 : Blo 896573 10368157 := bstep (se 3 (by rfl) ⟨1944029, by rfl⟩ : syracuseStep 10368157 = 3888059) B3888059
theorem B898207 : Blo 896573 898207 := bstep (se 1 (by rfl) ⟨673655, by rfl⟩ : syracuseStep 898207 = 1347311) B1347311
theorem B898331 : Blo 896573 898331 := bstep (se 1 (by rfl) ⟨673748, by rfl⟩ : syracuseStep 898331 = 1347497) B1347497
theorem B1619423 : Blo 896573 1619423 := bstep (se 1 (by rfl) ⟨1214567, by rfl⟩ : syracuseStep 1619423 = 2429135) B2429135
theorem B3651065 : Blo 896573 3651065 := bstep (se 2 (by rfl) ⟨1369149, by rfl⟩ : syracuseStep 3651065 = 2738299) B2738299
theorem B898607 : Blo 896573 898607 := bstep (se 1 (by rfl) ⟨673955, by rfl⟩ : syracuseStep 898607 = 1347911) B1347911
theorem B201733733 : Blo 896573 201733733 := bstep (se 4 (by rfl) ⟨18912537, by rfl⟩ : syracuseStep 201733733 = 37825075) B37825075
theorem B2275553 : Blo 896573 2275553 := bstep (se 2 (by rfl) ⟨853332, by rfl⟩ : syracuseStep 2275553 = 1706665) B1706665
theorem B900159 : Blo 896573 900159 := bstep (se 1 (by rfl) ⟨675119, by rfl⟩ : syracuseStep 900159 = 1350239) B1350239
theorem B900351 : Blo 896573 900351 := bstep (se 1 (by rfl) ⟨675263, by rfl⟩ : syracuseStep 900351 = 1350527) B1350527
theorem B4539239 : Blo 896573 4539239 := bstep (se 1 (by rfl) ⟨3404429, by rfl⟩ : syracuseStep 4539239 = 6808859) B6808859
theorem B7686211 : Blo 896573 7686211 := bstep (se 1 (by rfl) ⟨5764658, by rfl⟩ : syracuseStep 7686211 = 11529317) B11529317
theorem B4540859 : Blo 896573 4540859 := bstep (se 1 (by rfl) ⟨3405644, by rfl⟩ : syracuseStep 4540859 = 6811289) B6811289
theorem B5459663 : Blo 896573 5459663 := bstep (se 1 (by rfl) ⟨4094747, by rfl⟩ : syracuseStep 5459663 = 8189495) B8189495
theorem B283693745 : Blo 896573 283693745 := bstep (se 2 (by rfl) ⟨106385154, by rfl⟩ : syracuseStep 283693745 = 212770309) B212770309
theorem B7295771 : Blo 896573 7295771 := bstep (se 1 (by rfl) ⟨5471828, by rfl⟩ : syracuseStep 7295771 = 10943657) B10943657
theorem B4543289 : Blo 896573 4543289 := bstep (se 2 (by rfl) ⟨1703733, by rfl⟩ : syracuseStep 4543289 = 3407467) B3407467
theorem B42687917 : Blo 896573 42687917 := bstep (se 3 (by rfl) ⟨8003984, by rfl⟩ : syracuseStep 42687917 = 16007969) B16007969
theorem B1139179 : Blo 896573 1139179 := bstep (se 1 (by rfl) ⟨854384, by rfl⟩ : syracuseStep 1139179 = 1708769) B1708769
theorem B2023919 : Blo 896573 2023919 := bstep (se 1 (by rfl) ⟨1517939, by rfl⟩ : syracuseStep 2023919 = 3035879) B3035879
theorem B2024585 : Blo 896573 2024585 := bstep (se 2 (by rfl) ⟨759219, by rfl⟩ : syracuseStep 2024585 = 1518439) B1518439
theorem B1009831 : Blo 896573 1009831 := bstep (se 1 (by rfl) ⟨757373, by rfl⟩ : syracuseStep 1009831 = 1514747) B1514747
theorem B40562045 : Blo 896573 40562045 := bstep (se 3 (by rfl) ⟨7605383, by rfl⟩ : syracuseStep 40562045 = 15210767) B15210767
theorem B5109743 : Blo 896573 5109743 := bstep (se 1 (by rfl) ⟨3832307, by rfl⟩ : syracuseStep 5109743 = 7664615) B7664615
theorem B4094239 : Blo 896573 4094239 := bstep (se 1 (by rfl) ⟨3070679, by rfl⟩ : syracuseStep 4094239 = 6141359) B6141359
theorem B3832703 : Blo 896573 3832703 := bstep (se 1 (by rfl) ⟨2874527, by rfl⟩ : syracuseStep 3832703 = 5749055) B5749055
theorem B2555327 : Blo 896573 2555327 := bstep (se 1 (by rfl) ⟨1916495, by rfl⟩ : syracuseStep 2555327 = 3832991) B3832991
theorem B29165831 : Blo 896573 29165831 := bstep (se 1 (by rfl) ⟨21874373, by rfl⟩ : syracuseStep 29165831 = 43748747) B43748747
theorem B1346441 : Blo 896573 1346441 := bstep (se 2 (by rfl) ⟨504915, by rfl⟩ : syracuseStep 1346441 = 1009831) B1009831
theorem B29594393 : Blo 896573 29594393 := bstep (se 2 (by rfl) ⟨11097897, by rfl⟩ : syracuseStep 29594393 = 22195795) B22195795
theorem B1349279 : Blo 896573 1349279 := bstep (se 1 (by rfl) ⟨1011959, by rfl⟩ : syracuseStep 1349279 = 2023919) B2023919
theorem B1349723 : Blo 896573 1349723 := bstep (se 1 (by rfl) ⟨1012292, by rfl⟩ : syracuseStep 1349723 = 2024585) B2024585
theorem B7674047 : Blo 896573 7674047 := bstep (se 1 (by rfl) ⟨5755535, by rfl⟩ : syracuseStep 7674047 = 11511071) B11511071
theorem B27041363 : Blo 896573 27041363 := bstep (se 1 (by rfl) ⟨20281022, by rfl⟩ : syracuseStep 27041363 = 40562045) B40562045
theorem B2564075 : Blo 896573 2564075 := bstep (se 1 (by rfl) ⟨1923056, by rfl⟩ : syracuseStep 2564075 = 3846113) B3846113
theorem B3416701 : Blo 896573 3416701 := bstep (se 3 (by rfl) ⟨640631, by rfl⟩ : syracuseStep 3416701 = 1281263) B1281263
theorem B2434043 : Blo 896573 2434043 := bstep (se 1 (by rfl) ⟨1825532, by rfl⟩ : syracuseStep 2434043 = 3651065) B3651065
theorem B134489155 : Blo 896573 134489155 := bstep (se 1 (by rfl) ⟨100866866, by rfl⟩ : syracuseStep 134489155 = 201733733) B201733733
theorem B1517035 : Blo 896573 1517035 := bstep (se 1 (by rfl) ⟨1137776, by rfl⟩ : syracuseStep 1517035 = 2275553) B2275553
theorem B14559101 : Blo 896573 14559101 := bstep (se 3 (by rfl) ⟨2729831, by rfl⟩ : syracuseStep 14559101 = 5459663) B5459663
theorem B3026159 : Blo 896573 3026159 := bstep (se 1 (by rfl) ⟨2269619, by rfl⟩ : syracuseStep 3026159 = 4539239) B4539239
theorem B1518905 : Blo 896573 1518905 := bstep (se 2 (by rfl) ⟨569589, by rfl⟩ : syracuseStep 1518905 = 1139179) B1139179
theorem B3027239 : Blo 896573 3027239 := bstep (se 1 (by rfl) ⟨2270429, by rfl⟩ : syracuseStep 3027239 = 4540859) B4540859
theorem B897919 : Blo 896573 897919 := bstep (se 1 (by rfl) ⟨673439, by rfl⟩ : syracuseStep 897919 = 1346879) B1346879
theorem B898079 : Blo 896573 898079 := bstep (se 1 (by rfl) ⟨673559, by rfl⟩ : syracuseStep 898079 = 1347119) B1347119
theorem B898151 : Blo 896573 898151 := bstep (se 1 (by rfl) ⟨673613, by rfl⟩ : syracuseStep 898151 = 1347227) B1347227
theorem B4863847 : Blo 896573 4863847 := bstep (se 1 (by rfl) ⟨3647885, by rfl⟩ : syracuseStep 4863847 = 7295771) B7295771
theorem B3028859 : Blo 896573 3028859 := bstep (se 1 (by rfl) ⟨2271644, by rfl⟩ : syracuseStep 3028859 = 4543289) B4543289
theorem B899835 : Blo 896573 899835 := bstep (se 1 (by rfl) ⟨674876, by rfl⟩ : syracuseStep 899835 = 1349753) B1349753
theorem B900207 : Blo 896573 900207 := bstep (se 1 (by rfl) ⟨675155, by rfl⟩ : syracuseStep 900207 = 1350311) B1350311
theorem B12303515 : Blo 896573 12303515 := bstep (se 1 (by rfl) ⟨9227636, by rfl⟩ : syracuseStep 12303515 = 18455273) B18455273
theorem B28458611 : Blo 896573 28458611 := bstep (se 1 (by rfl) ⟨21343958, by rfl⟩ : syracuseStep 28458611 = 42687917) B42687917
theorem B4310927 : Blo 896573 4310927 := bstep (se 1 (by rfl) ⟨3233195, by rfl⟩ : syracuseStep 4310927 = 6466391) B6466391
theorem B5458985 : Blo 896573 5458985 := bstep (se 2 (by rfl) ⟨2047119, by rfl⟩ : syracuseStep 5458985 = 4094239) B4094239
theorem B10248281 : Blo 896573 10248281 := bstep (se 2 (by rfl) ⟨3843105, by rfl⟩ : syracuseStep 10248281 = 7686211) B7686211
theorem B2023649 : Blo 896573 2023649 := bstep (se 2 (by rfl) ⟨758868, by rfl⟩ : syracuseStep 2023649 = 1517737) B1517737
theorem B189129163 : Blo 896573 189129163 := bstep (se 1 (by rfl) ⟨141846872, by rfl⟩ : syracuseStep 189129163 = 283693745) B283693745
theorem B15361487 : Blo 896573 15361487 := bstep (se 1 (by rfl) ⟨11521115, by rfl⟩ : syracuseStep 15361487 = 23042231) B23042231
theorem B1010407 : Blo 896573 1010407 := bstep (se 1 (by rfl) ⟨757805, by rfl⟩ : syracuseStep 1010407 = 1515611) B1515611
theorem B10251197 : Blo 896573 10251197 := bstep (se 3 (by rfl) ⟨1922099, by rfl⟩ : syracuseStep 10251197 = 3844199) B3844199
theorem B13824209 : Blo 896573 13824209 := bstep (se 2 (by rfl) ⟨5184078, by rfl⟩ : syracuseStep 13824209 = 10368157) B10368157
theorem B1079615 : Blo 896573 1079615 := bstep (se 1 (by rfl) ⟨809711, by rfl⟩ : syracuseStep 1079615 = 1619423) B1619423
theorem B6814205 : Blo 896573 6814205 := bstep (se 3 (by rfl) ⟨1277663, by rfl⟩ : syracuseStep 6814205 = 2555327) B2555327
theorem B3406495 : Blo 896573 3406495 := bstep (se 1 (by rfl) ⟨2554871, by rfl⟩ : syracuseStep 3406495 = 5109743) B5109743
theorem B2555135 : Blo 896573 2555135 := bstep (se 1 (by rfl) ⟨1916351, by rfl⟩ : syracuseStep 2555135 = 3832703) B3832703
theorem B4555601 : Blo 896573 4555601 := bstep (se 2 (by rfl) ⟨1708350, by rfl⟩ : syracuseStep 4555601 = 3416701) B3416701
theorem B3639323 : Blo 896573 3639323 := bstep (se 1 (by rfl) ⟨2729492, by rfl⟩ : syracuseStep 3639323 = 5458985) B5458985
theorem B19729595 : Blo 896573 19729595 := bstep (se 1 (by rfl) ⟨14797196, by rfl⟩ : syracuseStep 19729595 = 29594393) B29594393
theorem B1347209 : Blo 896573 1347209 := bstep (se 2 (by rfl) ⟨505203, by rfl⟩ : syracuseStep 1347209 = 1010407) B1010407
theorem B5116031 : Blo 896573 5116031 := bstep (se 1 (by rfl) ⟨3837023, by rfl⟩ : syracuseStep 5116031 = 7674047) B7674047
theorem B18027575 : Blo 896573 18027575 := bstep (se 1 (by rfl) ⟨13520681, by rfl⟩ : syracuseStep 18027575 = 27041363) B27041363
theorem B1349099 : Blo 896573 1349099 := bstep (se 1 (by rfl) ⟨1011824, by rfl⟩ : syracuseStep 1349099 = 2023649) B2023649
theorem B9706067 : Blo 896573 9706067 := bstep (se 1 (by rfl) ⟨7279550, by rfl⟩ : syracuseStep 9706067 = 14559101) B14559101
theorem B9216139 : Blo 896573 9216139 := bstep (se 1 (by rfl) ⟨6912104, by rfl⟩ : syracuseStep 9216139 = 13824209) B13824209
theorem B8202343 : Blo 896573 8202343 := bstep (se 1 (by rfl) ⟨6151757, by rfl⟩ : syracuseStep 8202343 = 12303515) B12303515
theorem B179318873 : Blo 896573 179318873 := bstep (se 2 (by rfl) ⟨67244577, by rfl⟩ : syracuseStep 179318873 = 134489155) B134489155
theorem B19443887 : Blo 896573 19443887 := bstep (se 1 (by rfl) ⟨14582915, by rfl⟩ : syracuseStep 19443887 = 29165831) B29165831
theorem B897627 : Blo 896573 897627 := bstep (se 1 (by rfl) ⟨673220, by rfl⟩ : syracuseStep 897627 = 1346441) B1346441
theorem B899519 : Blo 896573 899519 := bstep (se 1 (by rfl) ⟨674639, by rfl⟩ : syracuseStep 899519 = 1349279) B1349279
theorem B899815 : Blo 896573 899815 := bstep (se 1 (by rfl) ⟨674861, by rfl⟩ : syracuseStep 899815 = 1349723) B1349723
theorem B6832187 : Blo 896573 6832187 := bstep (se 1 (by rfl) ⟨5124140, by rfl⟩ : syracuseStep 6832187 = 10248281) B10248281
theorem B1622695 : Blo 896573 1622695 := bstep (se 1 (by rfl) ⟨1217021, by rfl⟩ : syracuseStep 1622695 = 2434043) B2434043
theorem B10240991 : Blo 896573 10240991 := bstep (se 1 (by rfl) ⟨7680743, by rfl⟩ : syracuseStep 10240991 = 15361487) B15361487
theorem B6834131 : Blo 896573 6834131 := bstep (se 1 (by rfl) ⟨5125598, by rfl⟩ : syracuseStep 6834131 = 10251197) B10251197
theorem B2017439 : Blo 896573 2017439 := bstep (se 1 (by rfl) ⟨1513079, by rfl⟩ : syracuseStep 2017439 = 3026159) B3026159
theorem B2018159 : Blo 896573 2018159 := bstep (se 1 (by rfl) ⟨1513619, by rfl⟩ : syracuseStep 2018159 = 3027239) B3027239
theorem B4541993 : Blo 896573 4541993 := bstep (se 2 (by rfl) ⟨1703247, by rfl⟩ : syracuseStep 4541993 = 3406495) B3406495
theorem B2019239 : Blo 896573 2019239 := bstep (se 1 (by rfl) ⟨1514429, by rfl⟩ : syracuseStep 2019239 = 3028859) B3028859
theorem B4542803 : Blo 896573 4542803 := bstep (se 1 (by rfl) ⟨3407102, by rfl⟩ : syracuseStep 4542803 = 6814205) B6814205
theorem B6837533 : Blo 896573 6837533 := bstep (se 3 (by rfl) ⟨1282037, by rfl⟩ : syracuseStep 6837533 = 2564075) B2564075
theorem B252172217 : Blo 896573 252172217 := bstep (se 2 (by rfl) ⟨94564581, by rfl⟩ : syracuseStep 252172217 = 189129163) B189129163
theorem B2873951 : Blo 896573 2873951 := bstep (se 1 (by rfl) ⟨2155463, by rfl⟩ : syracuseStep 2873951 = 4310927) B4310927
theorem B2022713 : Blo 896573 2022713 := bstep (se 2 (by rfl) ⟨758517, by rfl⟩ : syracuseStep 2022713 = 1517035) B1517035
theorem B2878973 : Blo 896573 2878973 := bstep (se 3 (by rfl) ⟨539807, by rfl⟩ : syracuseStep 2878973 = 1079615) B1079615
theorem B1012603 : Blo 896573 1012603 := bstep (se 1 (by rfl) ⟨759452, by rfl⟩ : syracuseStep 1012603 = 1518905) B1518905
theorem B6485129 : Blo 896573 6485129 := bstep (se 2 (by rfl) ⟨2431923, by rfl⟩ : syracuseStep 6485129 = 4863847) B4863847
theorem B1703423 : Blo 896573 1703423 := bstep (se 1 (by rfl) ⟨1277567, by rfl⟩ : syracuseStep 1703423 = 2555135) B2555135
theorem B18972407 : Blo 896573 18972407 := bstep (se 1 (by rfl) ⟨14229305, by rfl⟩ : syracuseStep 18972407 = 28458611) B28458611
theorem B4554791 : Blo 896573 4554791 := bstep (se 1 (by rfl) ⟨3416093, by rfl⟩ : syracuseStep 4554791 = 6832187) B6832187
theorem B12288185 : Blo 896573 12288185 := bstep (se 2 (by rfl) ⟨4608069, by rfl⟩ : syracuseStep 12288185 = 9216139) B9216139
theorem B2163593 : Blo 896573 2163593 := bstep (se 2 (by rfl) ⟨811347, by rfl⟩ : syracuseStep 2163593 = 1622695) B1622695
theorem B4556087 : Blo 896573 4556087 := bstep (se 1 (by rfl) ⟨3417065, by rfl⟩ : syracuseStep 4556087 = 6834131) B6834131
theorem B2426215 : Blo 896573 2426215 := bstep (se 1 (by rfl) ⟨1819661, by rfl⟩ : syracuseStep 2426215 = 3639323) B3639323
theorem B1344959 : Blo 896573 1344959 := bstep (se 1 (by rfl) ⟨1008719, by rfl⟩ : syracuseStep 1344959 = 2017439) B2017439
theorem B1345439 : Blo 896573 1345439 := bstep (se 1 (by rfl) ⟨1009079, by rfl⟩ : syracuseStep 1345439 = 2018159) B2018159
theorem B1346159 : Blo 896573 1346159 := bstep (se 1 (by rfl) ⟨1009619, by rfl⟩ : syracuseStep 1346159 = 2019239) B2019239
theorem B3410687 : Blo 896573 3410687 := bstep (se 1 (by rfl) ⟨2558015, by rfl⟩ : syracuseStep 3410687 = 5116031) B5116031
theorem B4558355 : Blo 896573 4558355 := bstep (se 1 (by rfl) ⟨3418766, by rfl⟩ : syracuseStep 4558355 = 6837533) B6837533
theorem B1348475 : Blo 896573 1348475 := bstep (se 1 (by rfl) ⟨1011356, by rfl⟩ : syracuseStep 1348475 = 2022713) B2022713
theorem B1350137 : Blo 896573 1350137 := bstep (se 2 (by rfl) ⟨506301, by rfl⟩ : syracuseStep 1350137 = 1012603) B1012603
theorem B119545915 : Blo 896573 119545915 := bstep (se 1 (by rfl) ⟨89659436, by rfl⟩ : syracuseStep 119545915 = 179318873) B179318873
theorem B6827327 : Blo 896573 6827327 := bstep (se 1 (by rfl) ⟨5120495, by rfl⟩ : syracuseStep 6827327 = 10240991) B10240991
theorem B13153063 : Blo 896573 13153063 := bstep (se 1 (by rfl) ⟨9864797, by rfl⟩ : syracuseStep 13153063 = 19729595) B19729595
theorem B3027995 : Blo 896573 3027995 := bstep (se 1 (by rfl) ⟨2270996, by rfl⟩ : syracuseStep 3027995 = 4541993) B4541993
theorem B898139 : Blo 896573 898139 := bstep (se 1 (by rfl) ⟨673604, by rfl⟩ : syracuseStep 898139 = 1347209) B1347209
theorem B3028535 : Blo 896573 3028535 := bstep (se 1 (by rfl) ⟨2271401, by rfl⟩ : syracuseStep 3028535 = 4542803) B4542803
theorem B899399 : Blo 896573 899399 := bstep (se 1 (by rfl) ⟨674549, by rfl⟩ : syracuseStep 899399 = 1349099) B1349099
theorem B168114811 : Blo 896573 168114811 := bstep (se 1 (by rfl) ⟨126086108, by rfl⟩ : syracuseStep 168114811 = 252172217) B252172217
theorem B6470711 : Blo 896573 6470711 := bstep (se 1 (by rfl) ⟨4853033, by rfl⟩ : syracuseStep 6470711 = 9706067) B9706067
theorem B1915967 : Blo 896573 1915967 := bstep (se 1 (by rfl) ⟨1436975, by rfl⟩ : syracuseStep 1915967 = 2873951) B2873951
theorem B1919315 : Blo 896573 1919315 := bstep (se 1 (by rfl) ⟨1439486, by rfl⟩ : syracuseStep 1919315 = 2878973) B2878973
theorem B12962591 : Blo 896573 12962591 := bstep (se 1 (by rfl) ⟨9721943, by rfl⟩ : syracuseStep 12962591 = 19443887) B19443887
theorem B1135615 : Blo 896573 1135615 := bstep (se 1 (by rfl) ⟨851711, by rfl⟩ : syracuseStep 1135615 = 1703423) B1703423
theorem B3037067 : Blo 896573 3037067 := bstep (se 1 (by rfl) ⟨2277800, by rfl⟩ : syracuseStep 3037067 = 4555601) B4555601
theorem B10936457 : Blo 896573 10936457 := bstep (se 2 (by rfl) ⟨4101171, by rfl⟩ : syracuseStep 10936457 = 8202343) B8202343
theorem B12018383 : Blo 896573 12018383 := bstep (se 1 (by rfl) ⟨9013787, by rfl⟩ : syracuseStep 12018383 = 18027575) B18027575
theorem B4323419 : Blo 896573 4323419 := bstep (se 1 (by rfl) ⟨3242564, by rfl⟩ : syracuseStep 4323419 = 6485129) B6485129
theorem B12648271 : Blo 896573 12648271 := bstep (se 1 (by rfl) ⟨9486203, by rfl⟩ : syracuseStep 12648271 = 18972407) B18972407
theorem B8192123 : Blo 896573 8192123 := bstep (se 1 (by rfl) ⟨6144092, by rfl⟩ : syracuseStep 8192123 = 12288185) B12288185
theorem B1442395 : Blo 896573 1442395 := bstep (se 1 (by rfl) ⟨1081796, by rfl⟩ : syracuseStep 1442395 = 2163593) B2163593
theorem B5118173 : Blo 896573 5118173 := bstep (se 3 (by rfl) ⟨959657, by rfl⟩ : syracuseStep 5118173 = 1919315) B1919315
theorem B17537417 : Blo 896573 17537417 := bstep (se 2 (by rfl) ⟨6576531, by rfl⟩ : syracuseStep 17537417 = 13153063) B13153063
theorem B1514153 : Blo 896573 1514153 := bstep (se 2 (by rfl) ⟨567807, by rfl⟩ : syracuseStep 1514153 = 1135615) B1135615
theorem B159394553 : Blo 896573 159394553 := bstep (se 2 (by rfl) ⟨59772957, by rfl⟩ : syracuseStep 159394553 = 119545915) B119545915
theorem B896639 : Blo 896573 896639 := bstep (se 1 (by rfl) ⟨672479, by rfl⟩ : syracuseStep 896639 = 1344959) B1344959
theorem B896959 : Blo 896573 896959 := bstep (se 1 (by rfl) ⟨672719, by rfl⟩ : syracuseStep 896959 = 1345439) B1345439
theorem B897439 : Blo 896573 897439 := bstep (se 1 (by rfl) ⟨673079, by rfl⟩ : syracuseStep 897439 = 1346159) B1346159
theorem B2273791 : Blo 896573 2273791 := bstep (se 1 (by rfl) ⟨1705343, by rfl⟩ : syracuseStep 2273791 = 3410687) B3410687
theorem B898983 : Blo 896573 898983 := bstep (se 1 (by rfl) ⟨674237, by rfl⟩ : syracuseStep 898983 = 1348475) B1348475
theorem B900091 : Blo 896573 900091 := bstep (se 1 (by rfl) ⟨675068, by rfl⟩ : syracuseStep 900091 = 1350137) B1350137
theorem B7290971 : Blo 896573 7290971 := bstep (se 1 (by rfl) ⟨5468228, by rfl⟩ : syracuseStep 7290971 = 10936457) B10936457
theorem B8012255 : Blo 896573 8012255 := bstep (se 1 (by rfl) ⟨6009191, by rfl⟩ : syracuseStep 8012255 = 12018383) B12018383
theorem B2018663 : Blo 896573 2018663 := bstep (se 1 (by rfl) ⟨1513997, by rfl⟩ : syracuseStep 2018663 = 3027995) B3027995
theorem B224153081 : Blo 896573 224153081 := bstep (se 2 (by rfl) ⟨84057405, by rfl⟩ : syracuseStep 224153081 = 168114811) B168114811
theorem B2019023 : Blo 896573 2019023 := bstep (se 1 (by rfl) ⟨1514267, by rfl⟩ : syracuseStep 2019023 = 3028535) B3028535
theorem B4313807 : Blo 896573 4313807 := bstep (se 1 (by rfl) ⟨3235355, by rfl⟩ : syracuseStep 4313807 = 6470711) B6470711
theorem B16864361 : Blo 896573 16864361 := bstep (se 2 (by rfl) ⟨6324135, by rfl⟩ : syracuseStep 16864361 = 12648271) B12648271
theorem B3036527 : Blo 896573 3036527 := bstep (se 1 (by rfl) ⟨2277395, by rfl⟩ : syracuseStep 3036527 = 4554791) B4554791
theorem B3037391 : Blo 896573 3037391 := bstep (se 1 (by rfl) ⟨2278043, by rfl⟩ : syracuseStep 3037391 = 4556087) B4556087
theorem B3234953 : Blo 896573 3234953 := bstep (se 2 (by rfl) ⟨1213107, by rfl⟩ : syracuseStep 3234953 = 2426215) B2426215
theorem B8641727 : Blo 896573 8641727 := bstep (se 1 (by rfl) ⟨6481295, by rfl⟩ : syracuseStep 8641727 = 12962591) B12962591
theorem B3038903 : Blo 896573 3038903 := bstep (se 1 (by rfl) ⟨2279177, by rfl⟩ : syracuseStep 3038903 = 4558355) B4558355
theorem B2024711 : Blo 896573 2024711 := bstep (se 1 (by rfl) ⟨1518533, by rfl⟩ : syracuseStep 2024711 = 3037067) B3037067
theorem B4551551 : Blo 896573 4551551 := bstep (se 1 (by rfl) ⟨3413663, by rfl⟩ : syracuseStep 4551551 = 6827327) B6827327
theorem B2882279 : Blo 896573 2882279 := bstep (se 1 (by rfl) ⟨2161709, by rfl⟩ : syracuseStep 2882279 = 4323419) B4323419
theorem B1277311 : Blo 896573 1277311 := bstep (se 1 (by rfl) ⟨957983, by rfl⟩ : syracuseStep 1277311 = 1915967) B1915967
theorem B21366013 : Blo 896573 21366013 := bstep (se 3 (by rfl) ⟨4006127, by rfl⟩ : syracuseStep 21366013 = 8012255) B8012255
theorem B1345775 : Blo 896573 1345775 := bstep (se 1 (by rfl) ⟨1009331, by rfl⟩ : syracuseStep 1345775 = 2018663) B2018663
theorem B1346015 : Blo 896573 1346015 := bstep (se 1 (by rfl) ⟨1009511, by rfl⟩ : syracuseStep 1346015 = 2019023) B2019023
theorem B11242907 : Blo 896573 11242907 := bstep (se 1 (by rfl) ⟨8432180, by rfl⟩ : syracuseStep 11242907 = 16864361) B16864361
theorem B3412115 : Blo 896573 3412115 := bstep (se 1 (by rfl) ⟨2559086, by rfl⟩ : syracuseStep 3412115 = 5118173) B5118173
theorem B1349807 : Blo 896573 1349807 := bstep (se 1 (by rfl) ⟨1012355, by rfl⟩ : syracuseStep 1349807 = 2024711) B2024711
theorem B4860647 : Blo 896573 4860647 := bstep (se 1 (by rfl) ⟨3645485, by rfl⟩ : syracuseStep 4860647 = 7290971) B7290971
theorem B149435387 : Blo 896573 149435387 := bstep (se 1 (by rfl) ⟨112076540, by rfl⟩ : syracuseStep 149435387 = 224153081) B224153081
theorem B3031721 : Blo 896573 3031721 := bstep (se 2 (by rfl) ⟨1136895, by rfl⟩ : syracuseStep 3031721 = 2273791) B2273791
theorem B3034367 : Blo 896573 3034367 := bstep (se 1 (by rfl) ⟨2275775, by rfl⟩ : syracuseStep 3034367 = 4551551) B4551551
theorem B1921519 : Blo 896573 1921519 := bstep (se 1 (by rfl) ⟨1441139, by rfl⟩ : syracuseStep 1921519 = 2882279) B2882279
theorem B5461415 : Blo 896573 5461415 := bstep (se 1 (by rfl) ⟨4096061, by rfl⟩ : syracuseStep 5461415 = 8192123) B8192123
theorem B1923193 : Blo 896573 1923193 := bstep (se 2 (by rfl) ⟨721197, by rfl⟩ : syracuseStep 1923193 = 1442395) B1442395
theorem B2875871 : Blo 896573 2875871 := bstep (se 1 (by rfl) ⟨2156903, by rfl⟩ : syracuseStep 2875871 = 4313807) B4313807
theorem B2024351 : Blo 896573 2024351 := bstep (se 1 (by rfl) ⟨1518263, by rfl⟩ : syracuseStep 2024351 = 3036527) B3036527
theorem B2024927 : Blo 896573 2024927 := bstep (se 1 (by rfl) ⟨1518695, by rfl⟩ : syracuseStep 2024927 = 3037391) B3037391
theorem B11691611 : Blo 896573 11691611 := bstep (se 1 (by rfl) ⟨8768708, by rfl⟩ : syracuseStep 11691611 = 17537417) B17537417
theorem B1009435 : Blo 896573 1009435 := bstep (se 1 (by rfl) ⟨757076, by rfl⟩ : syracuseStep 1009435 = 1514153) B1514153
theorem B2156635 : Blo 896573 2156635 := bstep (se 1 (by rfl) ⟨1617476, by rfl⟩ : syracuseStep 2156635 = 3234953) B3234953
theorem B5761151 : Blo 896573 5761151 := bstep (se 1 (by rfl) ⟨4320863, by rfl⟩ : syracuseStep 5761151 = 8641727) B8641727
theorem B2025935 : Blo 896573 2025935 := bstep (se 1 (by rfl) ⟨1519451, by rfl⟩ : syracuseStep 2025935 = 3038903) B3038903
theorem B106263035 : Blo 896573 106263035 := bstep (se 1 (by rfl) ⟨79697276, by rfl⟩ : syracuseStep 106263035 = 159394553) B159394553
theorem B1703081 : Blo 896573 1703081 := bstep (se 2 (by rfl) ⟨638655, by rfl⟩ : syracuseStep 1703081 = 1277311) B1277311
theorem B10257029 : Blo 896573 10257029 := bstep (se 4 (by rfl) ⟨961596, by rfl⟩ : syracuseStep 10257029 = 1923193) B1923193
theorem B7668989 : Blo 896573 7668989 := bstep (se 3 (by rfl) ⟨1437935, by rfl⟩ : syracuseStep 7668989 = 2875871) B2875871
theorem B1345913 : Blo 896573 1345913 := bstep (se 2 (by rfl) ⟨504717, by rfl⟩ : syracuseStep 1345913 = 1009435) B1009435
theorem B3640943 : Blo 896573 3640943 := bstep (se 1 (by rfl) ⟨2730707, by rfl⟩ : syracuseStep 3640943 = 5461415) B5461415
theorem B1349567 : Blo 896573 1349567 := bstep (se 1 (by rfl) ⟨1012175, by rfl⟩ : syracuseStep 1349567 = 2024351) B2024351
theorem B2562025 : Blo 896573 2562025 := bstep (se 2 (by rfl) ⟨960759, by rfl⟩ : syracuseStep 2562025 = 1921519) B1921519
theorem B1349951 : Blo 896573 1349951 := bstep (se 1 (by rfl) ⟨1012463, by rfl⟩ : syracuseStep 1349951 = 2024927) B2024927
theorem B3840767 : Blo 896573 3840767 := bstep (se 1 (by rfl) ⟨2880575, by rfl⟩ : syracuseStep 3840767 = 5761151) B5761151
theorem B1350623 : Blo 896573 1350623 := bstep (se 1 (by rfl) ⟨1012967, by rfl⟩ : syracuseStep 1350623 = 2025935) B2025935
theorem B99623591 : Blo 896573 99623591 := bstep (se 1 (by rfl) ⟨74717693, by rfl⟩ : syracuseStep 99623591 = 149435387) B149435387
theorem B897183 : Blo 896573 897183 := bstep (se 1 (by rfl) ⟨672887, by rfl⟩ : syracuseStep 897183 = 1345775) B1345775
theorem B897343 : Blo 896573 897343 := bstep (se 1 (by rfl) ⟨673007, by rfl⟩ : syracuseStep 897343 = 1346015) B1346015
theorem B28488017 : Blo 896573 28488017 := bstep (se 2 (by rfl) ⟨10683006, by rfl⟩ : syracuseStep 28488017 = 21366013) B21366013
theorem B2274743 : Blo 896573 2274743 := bstep (se 1 (by rfl) ⟨1706057, by rfl⟩ : syracuseStep 2274743 = 3412115) B3412115
theorem B899871 : Blo 896573 899871 := bstep (se 1 (by rfl) ⟨674903, by rfl⟩ : syracuseStep 899871 = 1349807) B1349807
theorem B1135387 : Blo 896573 1135387 := bstep (se 1 (by rfl) ⟨851540, by rfl⟩ : syracuseStep 1135387 = 1703081) B1703081
theorem B2021147 : Blo 896573 2021147 := bstep (se 1 (by rfl) ⟨1515860, by rfl⟩ : syracuseStep 2021147 = 3031721) B3031721
theorem B2022911 : Blo 896573 2022911 := bstep (se 1 (by rfl) ⟨1517183, by rfl⟩ : syracuseStep 2022911 = 3034367) B3034367
theorem B7495271 : Blo 896573 7495271 := bstep (se 1 (by rfl) ⟨5621453, by rfl⟩ : syracuseStep 7495271 = 11242907) B11242907
theorem B2875513 : Blo 896573 2875513 := bstep (se 2 (by rfl) ⟨1078317, by rfl⟩ : syracuseStep 2875513 = 2156635) B2156635
theorem B7794407 : Blo 896573 7794407 := bstep (se 1 (by rfl) ⟨5845805, by rfl⟩ : syracuseStep 7794407 = 11691611) B11691611
theorem B3240431 : Blo 896573 3240431 := bstep (se 1 (by rfl) ⟨2430323, by rfl⟩ : syracuseStep 3240431 = 4860647) B4860647
theorem B70842023 : Blo 896573 70842023 := bstep (se 1 (by rfl) ⟨53131517, by rfl⟩ : syracuseStep 70842023 = 106263035) B106263035
theorem B3834017 : Blo 896573 3834017 := bstep (se 2 (by rfl) ⟨1437756, by rfl⟩ : syracuseStep 3834017 = 2875513) B2875513
theorem B5112659 : Blo 896573 5112659 := bstep (se 1 (by rfl) ⟨3834494, by rfl⟩ : syracuseStep 5112659 = 7668989) B7668989
theorem B2427295 : Blo 896573 2427295 := bstep (se 1 (by rfl) ⟨1820471, by rfl⟩ : syracuseStep 2427295 = 3640943) B3640943
theorem B1347431 : Blo 896573 1347431 := bstep (se 1 (by rfl) ⟨1010573, by rfl⟩ : syracuseStep 1347431 = 2021147) B2021147
theorem B2560511 : Blo 896573 2560511 := bstep (se 1 (by rfl) ⟨1920383, by rfl⟩ : syracuseStep 2560511 = 3840767) B3840767
theorem B1348607 : Blo 896573 1348607 := bstep (se 1 (by rfl) ⟨1011455, by rfl⟩ : syracuseStep 1348607 = 2022911) B2022911
theorem B1513849 : Blo 896573 1513849 := bstep (se 2 (by rfl) ⟨567693, by rfl⟩ : syracuseStep 1513849 = 1135387) B1135387
theorem B3416033 : Blo 896573 3416033 := bstep (se 2 (by rfl) ⟨1281012, by rfl⟩ : syracuseStep 3416033 = 2562025) B2562025
theorem B1516495 : Blo 896573 1516495 := bstep (se 1 (by rfl) ⟨1137371, by rfl⟩ : syracuseStep 1516495 = 2274743) B2274743
theorem B47228015 : Blo 896573 47228015 := bstep (se 1 (by rfl) ⟨35421011, by rfl⟩ : syracuseStep 47228015 = 70842023) B70842023
theorem B897275 : Blo 896573 897275 := bstep (se 1 (by rfl) ⟨672956, by rfl⟩ : syracuseStep 897275 = 1345913) B1345913
theorem B899711 : Blo 896573 899711 := bstep (se 1 (by rfl) ⟨674783, by rfl⟩ : syracuseStep 899711 = 1349567) B1349567
theorem B899967 : Blo 896573 899967 := bstep (se 1 (by rfl) ⟨674975, by rfl⟩ : syracuseStep 899967 = 1349951) B1349951
theorem B900415 : Blo 896573 900415 := bstep (se 1 (by rfl) ⟨675311, by rfl⟩ : syracuseStep 900415 = 1350623) B1350623
theorem B4996847 : Blo 896573 4996847 := bstep (se 1 (by rfl) ⟨3747635, by rfl⟩ : syracuseStep 4996847 = 7495271) B7495271
theorem B5196271 : Blo 896573 5196271 := bstep (se 1 (by rfl) ⟨3897203, by rfl⟩ : syracuseStep 5196271 = 7794407) B7794407
theorem B18992011 : Blo 896573 18992011 := bstep (se 1 (by rfl) ⟨14244008, by rfl⟩ : syracuseStep 18992011 = 28488017) B28488017
theorem B6838019 : Blo 896573 6838019 := bstep (se 1 (by rfl) ⟨5128514, by rfl⟩ : syracuseStep 6838019 = 10257029) B10257029
theorem B66415727 : Blo 896573 66415727 := bstep (se 1 (by rfl) ⟨49811795, by rfl⟩ : syracuseStep 66415727 = 99623591) B99623591
theorem B2160287 : Blo 896573 2160287 := bstep (se 1 (by rfl) ⟨1620215, by rfl⟩ : syracuseStep 2160287 = 3240431) B3240431
theorem B2556011 : Blo 896573 2556011 := bstep (se 1 (by rfl) ⟨1917008, by rfl⟩ : syracuseStep 2556011 = 3834017) B3834017
theorem B3408439 : Blo 896573 3408439 := bstep (se 1 (by rfl) ⟨2556329, by rfl⟩ : syracuseStep 3408439 = 5112659) B5112659
theorem B1707007 : Blo 896573 1707007 := bstep (se 1 (by rfl) ⟨1280255, by rfl⟩ : syracuseStep 1707007 = 2560511) B2560511
theorem B4558679 : Blo 896573 4558679 := bstep (se 1 (by rfl) ⟨3419009, by rfl⟩ : syracuseStep 4558679 = 6838019) B6838019
theorem B44277151 : Blo 896573 44277151 := bstep (se 1 (by rfl) ⟨33207863, by rfl⟩ : syracuseStep 44277151 = 66415727) B66415727
theorem B898287 : Blo 896573 898287 := bstep (se 1 (by rfl) ⟨673715, by rfl⟩ : syracuseStep 898287 = 1347431) B1347431
theorem B6928361 : Blo 896573 6928361 := bstep (se 2 (by rfl) ⟨2598135, by rfl⟩ : syracuseStep 6928361 = 5196271) B5196271
theorem B899071 : Blo 896573 899071 := bstep (se 1 (by rfl) ⟨674303, by rfl⟩ : syracuseStep 899071 = 1348607) B1348607
theorem B2277355 : Blo 896573 2277355 := bstep (se 1 (by rfl) ⟨1708016, by rfl⟩ : syracuseStep 2277355 = 3416033) B3416033
theorem B2018465 : Blo 896573 2018465 := bstep (se 2 (by rfl) ⟨756924, by rfl⟩ : syracuseStep 2018465 = 1513849) B1513849
theorem B13324925 : Blo 896573 13324925 := bstep (se 3 (by rfl) ⟨2498423, by rfl⟩ : syracuseStep 13324925 = 4996847) B4996847
theorem B2021993 : Blo 896573 2021993 := bstep (se 2 (by rfl) ⟨758247, by rfl⟩ : syracuseStep 2021993 = 1516495) B1516495
theorem B3236393 : Blo 896573 3236393 := bstep (se 2 (by rfl) ⟨1213647, by rfl⟩ : syracuseStep 3236393 = 2427295) B2427295
theorem B25322681 : Blo 896573 25322681 := bstep (se 2 (by rfl) ⟨9496005, by rfl⟩ : syracuseStep 25322681 = 18992011) B18992011
theorem B31485343 : Blo 896573 31485343 := bstep (se 1 (by rfl) ⟨23614007, by rfl⟩ : syracuseStep 31485343 = 47228015) B47228015
theorem B1440191 : Blo 896573 1440191 := bstep (se 1 (by rfl) ⟨1080143, by rfl⟩ : syracuseStep 1440191 = 2160287) B2160287
theorem B1704007 : Blo 896573 1704007 := bstep (se 1 (by rfl) ⟨1278005, by rfl⟩ : syracuseStep 1704007 = 2556011) B2556011
theorem B1345643 : Blo 896573 1345643 := bstep (se 1 (by rfl) ⟨1009232, by rfl⟩ : syracuseStep 1345643 = 2018465) B2018465
theorem B8883283 : Blo 896573 8883283 := bstep (se 1 (by rfl) ⟨6662462, by rfl⟩ : syracuseStep 8883283 = 13324925) B13324925
theorem B1347995 : Blo 896573 1347995 := bstep (se 1 (by rfl) ⟨1010996, by rfl⟩ : syracuseStep 1347995 = 2021993) B2021993
theorem B41980457 : Blo 896573 41980457 := bstep (se 2 (by rfl) ⟨15742671, by rfl⟩ : syracuseStep 41980457 = 31485343) B31485343
theorem B16881787 : Blo 896573 16881787 := bstep (se 1 (by rfl) ⟨12661340, by rfl⟩ : syracuseStep 16881787 = 25322681) B25322681
theorem B3840509 : Blo 896573 3840509 := bstep (se 3 (by rfl) ⟨720095, by rfl⟩ : syracuseStep 3840509 = 1440191) B1440191
theorem B8630381 : Blo 896573 8630381 := bstep (se 3 (by rfl) ⟨1618196, by rfl⟩ : syracuseStep 8630381 = 3236393) B3236393
theorem B2276009 : Blo 896573 2276009 := bstep (se 2 (by rfl) ⟨853503, by rfl⟩ : syracuseStep 2276009 = 1707007) B1707007
theorem B59036201 : Blo 896573 59036201 := bstep (se 2 (by rfl) ⟨22138575, by rfl⟩ : syracuseStep 59036201 = 44277151) B44277151
theorem B3036473 : Blo 896573 3036473 := bstep (se 2 (by rfl) ⟨1138677, by rfl⟩ : syracuseStep 3036473 = 2277355) B2277355
theorem B4544585 : Blo 896573 4544585 := bstep (se 2 (by rfl) ⟨1704219, by rfl⟩ : syracuseStep 4544585 = 3408439) B3408439
theorem B3039119 : Blo 896573 3039119 := bstep (se 1 (by rfl) ⟨2279339, by rfl⟩ : syracuseStep 3039119 = 4558679) B4558679
theorem B4618907 : Blo 896573 4618907 := bstep (se 1 (by rfl) ⟨3464180, by rfl⟩ : syracuseStep 4618907 = 6928361) B6928361
theorem B27986971 : Blo 896573 27986971 := bstep (se 1 (by rfl) ⟨20990228, by rfl⟩ : syracuseStep 27986971 = 41980457) B41980457
theorem B39357467 : Blo 896573 39357467 := bstep (se 1 (by rfl) ⟨29518100, by rfl⟩ : syracuseStep 39357467 = 59036201) B59036201
theorem B2560339 : Blo 896573 2560339 := bstep (se 1 (by rfl) ⟨1920254, by rfl⟩ : syracuseStep 2560339 = 3840509) B3840509
theorem B1517339 : Blo 896573 1517339 := bstep (se 1 (by rfl) ⟨1138004, by rfl⟩ : syracuseStep 1517339 = 2276009) B2276009
theorem B2272009 : Blo 896573 2272009 := bstep (se 2 (by rfl) ⟨852003, by rfl⟩ : syracuseStep 2272009 = 1704007) B1704007
theorem B897095 : Blo 896573 897095 := bstep (se 1 (by rfl) ⟨672821, by rfl⟩ : syracuseStep 897095 = 1345643) B1345643
theorem B898663 : Blo 896573 898663 := bstep (se 1 (by rfl) ⟨673997, by rfl⟩ : syracuseStep 898663 = 1347995) B1347995
theorem B3029723 : Blo 896573 3029723 := bstep (se 1 (by rfl) ⟨2272292, by rfl⟩ : syracuseStep 3029723 = 4544585) B4544585
theorem B11844377 : Blo 896573 11844377 := bstep (se 2 (by rfl) ⟨4441641, by rfl⟩ : syracuseStep 11844377 = 8883283) B8883283
theorem B5753587 : Blo 896573 5753587 := bstep (se 1 (by rfl) ⟨4315190, by rfl⟩ : syracuseStep 5753587 = 8630381) B8630381
theorem B2024315 : Blo 896573 2024315 := bstep (se 1 (by rfl) ⟨1518236, by rfl⟩ : syracuseStep 2024315 = 3036473) B3036473
theorem B2026079 : Blo 896573 2026079 := bstep (se 1 (by rfl) ⟨1519559, by rfl⟩ : syracuseStep 2026079 = 3039119) B3039119
theorem B22509049 : Blo 896573 22509049 := bstep (se 2 (by rfl) ⟨8440893, by rfl⟩ : syracuseStep 22509049 = 16881787) B16881787
theorem B3079271 : Blo 896573 3079271 := bstep (se 1 (by rfl) ⟨2309453, by rfl⟩ : syracuseStep 3079271 = 4618907) B4618907
theorem B7671449 : Blo 896573 7671449 := bstep (se 2 (by rfl) ⟨2876793, by rfl⟩ : syracuseStep 7671449 = 5753587) B5753587
theorem B3413785 : Blo 896573 3413785 := bstep (se 2 (by rfl) ⟨1280169, by rfl⟩ : syracuseStep 3413785 = 2560339) B2560339
theorem B1349543 : Blo 896573 1349543 := bstep (se 1 (by rfl) ⟨1012157, by rfl⟩ : syracuseStep 1349543 = 2024315) B2024315
theorem B1350719 : Blo 896573 1350719 := bstep (se 1 (by rfl) ⟨1013039, by rfl⟩ : syracuseStep 1350719 = 2026079) B2026079
theorem B3029345 : Blo 896573 3029345 := bstep (se 2 (by rfl) ⟨1136004, by rfl⟩ : syracuseStep 3029345 = 2272009) B2272009
theorem B2019815 : Blo 896573 2019815 := bstep (se 1 (by rfl) ⟨1514861, by rfl⟩ : syracuseStep 2019815 = 3029723) B3029723
theorem B2052847 : Blo 896573 2052847 := bstep (se 1 (by rfl) ⟨1539635, by rfl⟩ : syracuseStep 2052847 = 3079271) B3079271
theorem B26238311 : Blo 896573 26238311 := bstep (se 1 (by rfl) ⟨19678733, by rfl⟩ : syracuseStep 26238311 = 39357467) B39357467
theorem B37315961 : Blo 896573 37315961 := bstep (se 2 (by rfl) ⟨13993485, by rfl⟩ : syracuseStep 37315961 = 27986971) B27986971
theorem B1011559 : Blo 896573 1011559 := bstep (se 1 (by rfl) ⟨758669, by rfl⟩ : syracuseStep 1011559 = 1517339) B1517339
theorem B30012065 : Blo 896573 30012065 := bstep (se 2 (by rfl) ⟨11254524, by rfl⟩ : syracuseStep 30012065 = 22509049) B22509049
theorem B7896251 : Blo 896573 7896251 := bstep (se 1 (by rfl) ⟨5922188, by rfl⟩ : syracuseStep 7896251 = 11844377) B11844377
theorem B5114299 : Blo 896573 5114299 := bstep (se 1 (by rfl) ⟨3835724, by rfl⟩ : syracuseStep 5114299 = 7671449) B7671449
theorem B1346543 : Blo 896573 1346543 := bstep (se 1 (by rfl) ⟨1009907, by rfl⟩ : syracuseStep 1346543 = 2019815) B2019815
theorem B1348745 : Blo 896573 1348745 := bstep (se 2 (by rfl) ⟨505779, by rfl⟩ : syracuseStep 1348745 = 1011559) B1011559
theorem B24877307 : Blo 896573 24877307 := bstep (se 1 (by rfl) ⟨18657980, by rfl⟩ : syracuseStep 24877307 = 37315961) B37315961
theorem B899695 : Blo 896573 899695 := bstep (se 1 (by rfl) ⟨674771, by rfl⟩ : syracuseStep 899695 = 1349543) B1349543
theorem B900479 : Blo 896573 900479 := bstep (se 1 (by rfl) ⟨675359, by rfl⟩ : syracuseStep 900479 = 1350719) B1350719
theorem B2737129 : Blo 896573 2737129 := bstep (se 2 (by rfl) ⟨1026423, by rfl⟩ : syracuseStep 2737129 = 2052847) B2052847
theorem B20008043 : Blo 896573 20008043 := bstep (se 1 (by rfl) ⟨15006032, by rfl⟩ : syracuseStep 20008043 = 30012065) B30012065
theorem B21056669 : Blo 896573 21056669 := bstep (se 3 (by rfl) ⟨3948125, by rfl⟩ : syracuseStep 21056669 = 7896251) B7896251
theorem B2019563 : Blo 896573 2019563 := bstep (se 1 (by rfl) ⟨1514672, by rfl⟩ : syracuseStep 2019563 = 3029345) B3029345
theorem B17492207 : Blo 896573 17492207 := bstep (se 1 (by rfl) ⟨13119155, by rfl⟩ : syracuseStep 17492207 = 26238311) B26238311
theorem B4551713 : Blo 896573 4551713 := bstep (se 2 (by rfl) ⟨1706892, by rfl⟩ : syracuseStep 4551713 = 3413785) B3413785
theorem B13338695 : Blo 896573 13338695 := bstep (se 1 (by rfl) ⟨10004021, by rfl⟩ : syracuseStep 13338695 = 20008043) B20008043
theorem B1346375 : Blo 896573 1346375 := bstep (se 1 (by rfl) ⟨1009781, by rfl⟩ : syracuseStep 1346375 = 2019563) B2019563
theorem B6819065 : Blo 896573 6819065 := bstep (se 2 (by rfl) ⟨2557149, by rfl⟩ : syracuseStep 6819065 = 5114299) B5114299
theorem B16584871 : Blo 896573 16584871 := bstep (se 1 (by rfl) ⟨12438653, by rfl⟩ : syracuseStep 16584871 = 24877307) B24877307
theorem B3649505 : Blo 896573 3649505 := bstep (se 2 (by rfl) ⟨1368564, by rfl⟩ : syracuseStep 3649505 = 2737129) B2737129
theorem B897695 : Blo 896573 897695 := bstep (se 1 (by rfl) ⟨673271, by rfl⟩ : syracuseStep 897695 = 1346543) B1346543
theorem B14037779 : Blo 896573 14037779 := bstep (se 1 (by rfl) ⟨10528334, by rfl⟩ : syracuseStep 14037779 = 21056669) B21056669
theorem B899163 : Blo 896573 899163 := bstep (se 1 (by rfl) ⟨674372, by rfl⟩ : syracuseStep 899163 = 1348745) B1348745
theorem B46645885 : Blo 896573 46645885 := bstep (se 3 (by rfl) ⟨8746103, by rfl⟩ : syracuseStep 46645885 = 17492207) B17492207
theorem B3034475 : Blo 896573 3034475 := bstep (se 1 (by rfl) ⟨2275856, by rfl⟩ : syracuseStep 3034475 = 4551713) B4551713
theorem B248778053 : Blo 896573 248778053 := bstep (se 4 (by rfl) ⟨23322942, by rfl⟩ : syracuseStep 248778053 = 46645885) B46645885
theorem B8892463 : Blo 896573 8892463 := bstep (se 1 (by rfl) ⟨6669347, by rfl⟩ : syracuseStep 8892463 = 13338695) B13338695
theorem B897583 : Blo 896573 897583 := bstep (se 1 (by rfl) ⟨673187, by rfl⟩ : syracuseStep 897583 = 1346375) B1346375
theorem B9358519 : Blo 896573 9358519 := bstep (se 1 (by rfl) ⟨7018889, by rfl⟩ : syracuseStep 9358519 = 14037779) B14037779
theorem B4546043 : Blo 896573 4546043 := bstep (se 1 (by rfl) ⟨3409532, by rfl⟩ : syracuseStep 4546043 = 6819065) B6819065
theorem B2022983 : Blo 896573 2022983 := bstep (se 1 (by rfl) ⟨1517237, by rfl⟩ : syracuseStep 2022983 = 3034475) B3034475
theorem B22113161 : Blo 896573 22113161 := bstep (se 2 (by rfl) ⟨8292435, by rfl⟩ : syracuseStep 22113161 = 16584871) B16584871
theorem B38928053 : Blo 896573 38928053 := bstep (se 5 (by rfl) ⟨1824752, by rfl⟩ : syracuseStep 38928053 = 3649505) B3649505
theorem B1348655 : Blo 896573 1348655 := bstep (se 1 (by rfl) ⟨1011491, by rfl⟩ : syracuseStep 1348655 = 2022983) B2022983
theorem B165852035 : Blo 896573 165852035 := bstep (se 1 (by rfl) ⟨124389026, by rfl⟩ : syracuseStep 165852035 = 248778053) B248778053
theorem B3030695 : Blo 896573 3030695 := bstep (se 1 (by rfl) ⟨2273021, by rfl⟩ : syracuseStep 3030695 = 4546043) B4546043
theorem B12478025 : Blo 896573 12478025 := bstep (se 2 (by rfl) ⟨4679259, by rfl⟩ : syracuseStep 12478025 = 9358519) B9358519
theorem B11856617 : Blo 896573 11856617 := bstep (se 2 (by rfl) ⟨4446231, by rfl⟩ : syracuseStep 11856617 = 8892463) B8892463
theorem B14742107 : Blo 896573 14742107 := bstep (se 1 (by rfl) ⟨11056580, by rfl⟩ : syracuseStep 14742107 = 22113161) B22113161
theorem B25952035 : Blo 896573 25952035 := bstep (se 1 (by rfl) ⟨19464026, by rfl⟩ : syracuseStep 25952035 = 38928053) B38928053
theorem B7904411 : Blo 896573 7904411 := bstep (se 1 (by rfl) ⟨5928308, by rfl⟩ : syracuseStep 7904411 = 11856617) B11856617
theorem B110568023 : Blo 896573 110568023 := bstep (se 1 (by rfl) ⟨82926017, by rfl⟩ : syracuseStep 110568023 = 165852035) B165852035
theorem B899103 : Blo 896573 899103 := bstep (se 1 (by rfl) ⟨674327, by rfl⟩ : syracuseStep 899103 = 1348655) B1348655
theorem B2020463 : Blo 896573 2020463 := bstep (se 1 (by rfl) ⟨1515347, by rfl⟩ : syracuseStep 2020463 = 3030695) B3030695
theorem B8318683 : Blo 896573 8318683 := bstep (se 1 (by rfl) ⟨6239012, by rfl⟩ : syracuseStep 8318683 = 12478025) B12478025
theorem B9828071 : Blo 896573 9828071 := bstep (se 1 (by rfl) ⟨7371053, by rfl⟩ : syracuseStep 9828071 = 14742107) B14742107
theorem B34602713 : Blo 896573 34602713 := bstep (se 2 (by rfl) ⟨12976017, by rfl⟩ : syracuseStep 34602713 = 25952035) B25952035
theorem B1346975 : Blo 896573 1346975 := bstep (se 1 (by rfl) ⟨1010231, by rfl⟩ : syracuseStep 1346975 = 2020463) B2020463
theorem B11091577 : Blo 896573 11091577 := bstep (se 2 (by rfl) ⟨4159341, by rfl⟩ : syracuseStep 11091577 = 8318683) B8318683
theorem B73712015 : Blo 896573 73712015 := bstep (se 1 (by rfl) ⟨55284011, by rfl⟩ : syracuseStep 73712015 = 110568023) B110568023
theorem B5269607 : Blo 896573 5269607 := bstep (se 1 (by rfl) ⟨3952205, by rfl⟩ : syracuseStep 5269607 = 7904411) B7904411
theorem B6552047 : Blo 896573 6552047 := bstep (se 1 (by rfl) ⟨4914035, by rfl⟩ : syracuseStep 6552047 = 9828071) B9828071
theorem B23068475 : Blo 896573 23068475 := bstep (se 1 (by rfl) ⟨17301356, by rfl⟩ : syracuseStep 23068475 = 34602713) B34602713
theorem B17472125 : Blo 896573 17472125 := bstep (se 3 (by rfl) ⟨3276023, by rfl⟩ : syracuseStep 17472125 = 6552047) B6552047
theorem B3513071 : Blo 896573 3513071 := bstep (se 1 (by rfl) ⟨2634803, by rfl⟩ : syracuseStep 3513071 = 5269607) B5269607
theorem B14788769 : Blo 896573 14788769 := bstep (se 2 (by rfl) ⟨5545788, by rfl⟩ : syracuseStep 14788769 = 11091577) B11091577
theorem B15378983 : Blo 896573 15378983 := bstep (se 1 (by rfl) ⟨11534237, by rfl⟩ : syracuseStep 15378983 = 23068475) B23068475
theorem B897983 : Blo 896573 897983 := bstep (se 1 (by rfl) ⟨673487, by rfl⟩ : syracuseStep 897983 = 1346975) B1346975
theorem B49141343 : Blo 896573 49141343 := bstep (se 1 (by rfl) ⟨36856007, by rfl⟩ : syracuseStep 49141343 = 73712015) B73712015
theorem B11648083 : Blo 896573 11648083 := bstep (se 1 (by rfl) ⟨8736062, by rfl⟩ : syracuseStep 11648083 = 17472125) B17472125
theorem B2342047 : Blo 896573 2342047 := bstep (se 1 (by rfl) ⟨1756535, by rfl⟩ : syracuseStep 2342047 = 3513071) B3513071
theorem B39436717 : Blo 896573 39436717 := bstep (se 3 (by rfl) ⟨7394384, by rfl⟩ : syracuseStep 39436717 = 14788769) B14788769
theorem B32760895 : Blo 896573 32760895 := bstep (se 1 (by rfl) ⟨24570671, by rfl⟩ : syracuseStep 32760895 = 49141343) B49141343
theorem B10252655 : Blo 896573 10252655 := bstep (se 1 (by rfl) ⟨7689491, by rfl⟩ : syracuseStep 10252655 = 15378983) B15378983
theorem B43681193 : Blo 896573 43681193 := bstep (se 2 (by rfl) ⟨16380447, by rfl⟩ : syracuseStep 43681193 = 32760895) B32760895
theorem B3122729 : Blo 896573 3122729 := bstep (se 2 (by rfl) ⟨1171023, by rfl⟩ : syracuseStep 3122729 = 2342047) B2342047
theorem B6835103 : Blo 896573 6835103 := bstep (se 1 (by rfl) ⟨5126327, by rfl⟩ : syracuseStep 6835103 = 10252655) B10252655
theorem B52582289 : Blo 896573 52582289 := bstep (se 2 (by rfl) ⟨19718358, by rfl⟩ : syracuseStep 52582289 = 39436717) B39436717
theorem B15530777 : Blo 896573 15530777 := bstep (se 2 (by rfl) ⟨5824041, by rfl⟩ : syracuseStep 15530777 = 11648083) B11648083
theorem B4556735 : Blo 896573 4556735 := bstep (se 1 (by rfl) ⟨3417551, by rfl⟩ : syracuseStep 4556735 = 6835103) B6835103
theorem B140219437 : Blo 896573 140219437 := bstep (se 3 (by rfl) ⟨26291144, by rfl⟩ : syracuseStep 140219437 = 52582289) B52582289
theorem B2081819 : Blo 896573 2081819 := bstep (se 1 (by rfl) ⟨1561364, by rfl⟩ : syracuseStep 2081819 = 3122729) B3122729
theorem B29120795 : Blo 896573 29120795 := bstep (se 1 (by rfl) ⟨21840596, by rfl⟩ : syracuseStep 29120795 = 43681193) B43681193
theorem B10353851 : Blo 896573 10353851 := bstep (se 1 (by rfl) ⟨7765388, by rfl⟩ : syracuseStep 10353851 = 15530777) B15530777
theorem B5551517 : Blo 896573 5551517 := bstep (se 3 (by rfl) ⟨1040909, by rfl⟩ : syracuseStep 5551517 = 2081819) B2081819
theorem B19413863 : Blo 896573 19413863 := bstep (se 1 (by rfl) ⟨14560397, by rfl⟩ : syracuseStep 19413863 = 29120795) B29120795
theorem B186959249 : Blo 896573 186959249 := bstep (se 2 (by rfl) ⟨70109718, by rfl⟩ : syracuseStep 186959249 = 140219437) B140219437
theorem B6902567 : Blo 896573 6902567 := bstep (se 1 (by rfl) ⟨5176925, by rfl⟩ : syracuseStep 6902567 = 10353851) B10353851
theorem B3037823 : Blo 896573 3037823 := bstep (se 1 (by rfl) ⟨2278367, by rfl⟩ : syracuseStep 3037823 = 4556735) B4556735
theorem B4601711 : Blo 896573 4601711 := bstep (se 1 (by rfl) ⟨3451283, by rfl⟩ : syracuseStep 4601711 = 6902567) B6902567
theorem B124639499 : Blo 896573 124639499 := bstep (se 1 (by rfl) ⟨93479624, by rfl⟩ : syracuseStep 124639499 = 186959249) B186959249
theorem B14804045 : Blo 896573 14804045 := bstep (se 3 (by rfl) ⟨2775758, by rfl⟩ : syracuseStep 14804045 = 5551517) B5551517
theorem B2025215 : Blo 896573 2025215 := bstep (se 1 (by rfl) ⟨1518911, by rfl⟩ : syracuseStep 2025215 = 3037823) B3037823
theorem B12942575 : Blo 896573 12942575 := bstep (se 1 (by rfl) ⟨9706931, by rfl⟩ : syracuseStep 12942575 = 19413863) B19413863
theorem B9869363 : Blo 896573 9869363 := bstep (se 1 (by rfl) ⟨7402022, by rfl⟩ : syracuseStep 9869363 = 14804045) B14804045
theorem B1350143 : Blo 896573 1350143 := bstep (se 1 (by rfl) ⟨1012607, by rfl⟩ : syracuseStep 1350143 = 2025215) B2025215
theorem B8628383 : Blo 896573 8628383 := bstep (se 1 (by rfl) ⟨6471287, by rfl⟩ : syracuseStep 8628383 = 12942575) B12942575
theorem B3067807 : Blo 896573 3067807 := bstep (se 1 (by rfl) ⟨2300855, by rfl⟩ : syracuseStep 3067807 = 4601711) B4601711
theorem B83092999 : Blo 896573 83092999 := bstep (se 1 (by rfl) ⟨62319749, by rfl⟩ : syracuseStep 83092999 = 124639499) B124639499
theorem B110790665 : Blo 896573 110790665 := bstep (se 2 (by rfl) ⟨41546499, by rfl⟩ : syracuseStep 110790665 = 83092999) B83092999
theorem B900095 : Blo 896573 900095 := bstep (se 1 (by rfl) ⟨675071, by rfl⟩ : syracuseStep 900095 = 1350143) B1350143
theorem B5752255 : Blo 896573 5752255 := bstep (se 1 (by rfl) ⟨4314191, by rfl⟩ : syracuseStep 5752255 = 8628383) B8628383
theorem B6579575 : Blo 896573 6579575 := bstep (se 1 (by rfl) ⟨4934681, by rfl⟩ : syracuseStep 6579575 = 9869363) B9869363
theorem B4090409 : Blo 896573 4090409 := bstep (se 2 (by rfl) ⟨1533903, by rfl⟩ : syracuseStep 4090409 = 3067807) B3067807
theorem B73860443 : Blo 896573 73860443 := bstep (se 1 (by rfl) ⟨55395332, by rfl⟩ : syracuseStep 73860443 = 110790665) B110790665
theorem B7669673 : Blo 896573 7669673 := bstep (se 2 (by rfl) ⟨2876127, by rfl⟩ : syracuseStep 7669673 = 5752255) B5752255
theorem B2726939 : Blo 896573 2726939 := bstep (se 1 (by rfl) ⟨2045204, by rfl⟩ : syracuseStep 2726939 = 4090409) B4090409
theorem B4386383 : Blo 896573 4386383 := bstep (se 1 (by rfl) ⟨3289787, by rfl⟩ : syracuseStep 4386383 = 6579575) B6579575
theorem B5113115 : Blo 896573 5113115 := bstep (se 1 (by rfl) ⟨3834836, by rfl⟩ : syracuseStep 5113115 = 7669673) B7669673
theorem B2924255 : Blo 896573 2924255 := bstep (se 1 (by rfl) ⟨2193191, by rfl⟩ : syracuseStep 2924255 = 4386383) B4386383
theorem B1817959 : Blo 896573 1817959 := bstep (se 1 (by rfl) ⟨1363469, by rfl⟩ : syracuseStep 1817959 = 2726939) B2726939
theorem B49240295 : Blo 896573 49240295 := bstep (se 1 (by rfl) ⟨36930221, by rfl⟩ : syracuseStep 49240295 = 73860443) B73860443
theorem B3408743 : Blo 896573 3408743 := bstep (se 1 (by rfl) ⟨2556557, by rfl⟩ : syracuseStep 3408743 = 5113115) B5113115
theorem B1949503 : Blo 896573 1949503 := bstep (se 1 (by rfl) ⟨1462127, by rfl⟩ : syracuseStep 1949503 = 2924255) B2924255
theorem B32826863 : Blo 896573 32826863 := bstep (se 1 (by rfl) ⟨24620147, by rfl⟩ : syracuseStep 32826863 = 49240295) B49240295
theorem B2423945 : Blo 896573 2423945 := bstep (se 2 (by rfl) ⟨908979, by rfl⟩ : syracuseStep 2423945 = 1817959) B1817959
theorem B1615963 : Blo 896573 1615963 := bstep (se 1 (by rfl) ⟨1211972, by rfl⟩ : syracuseStep 1615963 = 2423945) B2423945
theorem B2599337 : Blo 896573 2599337 := bstep (se 2 (by rfl) ⟨974751, by rfl⟩ : syracuseStep 2599337 = 1949503) B1949503
theorem B2272495 : Blo 896573 2272495 := bstep (se 1 (by rfl) ⟨1704371, by rfl⟩ : syracuseStep 2272495 = 3408743) B3408743
theorem B21884575 : Blo 896573 21884575 := bstep (se 1 (by rfl) ⟨16413431, by rfl⟩ : syracuseStep 21884575 = 32826863) B32826863
theorem B3029993 : Blo 896573 3029993 := bstep (se 2 (by rfl) ⟨1136247, by rfl⟩ : syracuseStep 3029993 = 2272495) B2272495
theorem B29179433 : Blo 896573 29179433 := bstep (se 2 (by rfl) ⟨10942287, by rfl⟩ : syracuseStep 29179433 = 21884575) B21884575
theorem B6931565 : Blo 896573 6931565 := bstep (se 3 (by rfl) ⟨1299668, by rfl⟩ : syracuseStep 6931565 = 2599337) B2599337
theorem B2154617 : Blo 896573 2154617 := bstep (se 2 (by rfl) ⟨807981, by rfl⟩ : syracuseStep 2154617 = 1615963) B1615963
theorem B4621043 : Blo 896573 4621043 := bstep (se 1 (by rfl) ⟨3465782, by rfl⟩ : syracuseStep 4621043 = 6931565) B6931565
theorem B2019995 : Blo 896573 2019995 := bstep (se 1 (by rfl) ⟨1514996, by rfl⟩ : syracuseStep 2019995 = 3029993) B3029993
theorem B19452955 : Blo 896573 19452955 := bstep (se 1 (by rfl) ⟨14589716, by rfl⟩ : syracuseStep 19452955 = 29179433) B29179433
theorem B1436411 : Blo 896573 1436411 := bstep (se 1 (by rfl) ⟨1077308, by rfl⟩ : syracuseStep 1436411 = 2154617) B2154617
theorem B3080695 : Blo 896573 3080695 := bstep (se 1 (by rfl) ⟨2310521, by rfl⟩ : syracuseStep 3080695 = 4621043) B4621043
theorem B1346663 : Blo 896573 1346663 := bstep (se 1 (by rfl) ⟨1009997, by rfl⟩ : syracuseStep 1346663 = 2019995) B2019995
theorem B25937273 : Blo 896573 25937273 := bstep (se 2 (by rfl) ⟨9726477, by rfl⟩ : syracuseStep 25937273 = 19452955) B19452955
theorem B3830429 : Blo 896573 3830429 := bstep (se 3 (by rfl) ⟨718205, by rfl⟩ : syracuseStep 3830429 = 1436411) B1436411
theorem B4107593 : Blo 896573 4107593 := bstep (se 2 (by rfl) ⟨1540347, by rfl⟩ : syracuseStep 4107593 = 3080695) B3080695
theorem B897775 : Blo 896573 897775 := bstep (se 1 (by rfl) ⟨673331, by rfl⟩ : syracuseStep 897775 = 1346663) B1346663
theorem B17291515 : Blo 896573 17291515 := bstep (se 1 (by rfl) ⟨12968636, by rfl⟩ : syracuseStep 17291515 = 25937273) B25937273
theorem B2553619 : Blo 896573 2553619 := bstep (se 1 (by rfl) ⟨1915214, by rfl⟩ : syracuseStep 2553619 = 3830429) B3830429
theorem B2738395 : Blo 896573 2738395 := bstep (se 1 (by rfl) ⟨2053796, by rfl⟩ : syracuseStep 2738395 = 4107593) B4107593
theorem B23055353 : Blo 896573 23055353 := bstep (se 2 (by rfl) ⟨8645757, by rfl⟩ : syracuseStep 23055353 = 17291515) B17291515
theorem B3404825 : Blo 896573 3404825 := bstep (se 2 (by rfl) ⟨1276809, by rfl⟩ : syracuseStep 3404825 = 2553619) B2553619
theorem B15370235 : Blo 896573 15370235 := bstep (se 1 (by rfl) ⟨11527676, by rfl⟩ : syracuseStep 15370235 = 23055353) B23055353
theorem B2269883 : Blo 896573 2269883 := bstep (se 1 (by rfl) ⟨1702412, by rfl⟩ : syracuseStep 2269883 = 3404825) B3404825
theorem B3651193 : Blo 896573 3651193 := bstep (se 2 (by rfl) ⟨1369197, by rfl⟩ : syracuseStep 3651193 = 2738395) B2738395
theorem B1513255 : Blo 896573 1513255 := bstep (se 1 (by rfl) ⟨1134941, by rfl⟩ : syracuseStep 1513255 = 2269883) B2269883
theorem B4868257 : Blo 896573 4868257 := bstep (se 2 (by rfl) ⟨1825596, by rfl⟩ : syracuseStep 4868257 = 3651193) B3651193
theorem B10246823 : Blo 896573 10246823 := bstep (se 1 (by rfl) ⟨7685117, by rfl⟩ : syracuseStep 10246823 = 15370235) B15370235
theorem B6491009 : Blo 896573 6491009 := bstep (se 2 (by rfl) ⟨2434128, by rfl⟩ : syracuseStep 6491009 = 4868257) B4868257
theorem B6831215 : Blo 896573 6831215 := bstep (se 1 (by rfl) ⟨5123411, by rfl⟩ : syracuseStep 6831215 = 10246823) B10246823
theorem B2017673 : Blo 896573 2017673 := bstep (se 2 (by rfl) ⟨756627, by rfl⟩ : syracuseStep 2017673 = 1513255) B1513255
theorem B1345115 : Blo 896573 1345115 := bstep (se 1 (by rfl) ⟨1008836, by rfl⟩ : syracuseStep 1345115 = 2017673) B2017673
theorem B4327339 : Blo 896573 4327339 := bstep (se 1 (by rfl) ⟨3245504, by rfl⟩ : syracuseStep 4327339 = 6491009) B6491009
theorem B4554143 : Blo 896573 4554143 := bstep (se 1 (by rfl) ⟨3415607, by rfl⟩ : syracuseStep 4554143 = 6831215) B6831215
theorem B5769785 : Blo 896573 5769785 := bstep (se 2 (by rfl) ⟨2163669, by rfl⟩ : syracuseStep 5769785 = 4327339) B4327339
theorem B896743 : Blo 896573 896743 := bstep (se 1 (by rfl) ⟨672557, by rfl⟩ : syracuseStep 896743 = 1345115) B1345115
theorem B3036095 : Blo 896573 3036095 := bstep (se 1 (by rfl) ⟨2277071, by rfl⟩ : syracuseStep 3036095 = 4554143) B4554143
theorem B3846523 : Blo 896573 3846523 := bstep (se 1 (by rfl) ⟨2884892, by rfl⟩ : syracuseStep 3846523 = 5769785) B5769785
theorem B2024063 : Blo 896573 2024063 := bstep (se 1 (by rfl) ⟨1518047, by rfl⟩ : syracuseStep 2024063 = 3036095) B3036095
theorem B1349375 : Blo 896573 1349375 := bstep (se 1 (by rfl) ⟨1012031, by rfl⟩ : syracuseStep 1349375 = 2024063) B2024063
theorem B5128697 : Blo 896573 5128697 := bstep (se 2 (by rfl) ⟨1923261, by rfl⟩ : syracuseStep 5128697 = 3846523) B3846523
theorem B3419131 : Blo 896573 3419131 := bstep (se 1 (by rfl) ⟨2564348, by rfl⟩ : syracuseStep 3419131 = 5128697) B5128697
theorem B899583 : Blo 896573 899583 := bstep (se 1 (by rfl) ⟨674687, by rfl⟩ : syracuseStep 899583 = 1349375) B1349375
theorem B4558841 : Blo 896573 4558841 := bstep (se 2 (by rfl) ⟨1709565, by rfl⟩ : syracuseStep 4558841 = 3419131) B3419131
theorem B3039227 : Blo 896573 3039227 := bstep (se 1 (by rfl) ⟨2279420, by rfl⟩ : syracuseStep 3039227 = 4558841) B4558841
theorem B2026151 : Blo 896573 2026151 := bstep (se 1 (by rfl) ⟨1519613, by rfl⟩ : syracuseStep 2026151 = 3039227) B3039227
theorem B1350767 : Blo 896573 1350767 := bstep (se 1 (by rfl) ⟨1013075, by rfl⟩ : syracuseStep 1350767 = 2026151) B2026151
theorem B900511 : Blo 896573 900511 := bstep (se 1 (by rfl) ⟨675383, by rfl⟩ : syracuseStep 900511 = 1350767) B1350767

theorem C0 (j : ℕ) (h1 : 224143 ≤ j) (h2 : j ≤ 224842) : Blo 896573 (4 * j + 3) := by
  interval_cases j
  · exact B896575
  · exact B896579
  · exact B896583
  · exact B896587
  · exact B896591
  · exact B896595
  · exact B896599
  · exact B896603
  · exact B896607
  · exact B896611
  · exact B896615
  · exact B896619
  · exact B896623
  · exact B896627
  · exact B896631
  · exact B896635
  · exact B896639
  · exact B896643
  · exact B896647
  · exact B896651
  · exact B896655
  · exact B896659
  · exact B896663
  · exact B896667
  · exact B896671
  · exact B896675
  · exact B896679
  · exact B896683
  · exact B896687
  · exact B896691
  · exact B896695
  · exact B896699
  · exact B896703
  · exact B896707
  · exact B896711
  · exact B896715
  · exact B896719
  · exact B896723
  · exact B896727
  · exact B896731
  · exact B896735
  · exact B896739
  · exact B896743
  · exact B896747
  · exact B896751
  · exact B896755
  · exact B896759
  · exact B896763
  · exact B896767
  · exact B896771
  · exact B896775
  · exact B896779
  · exact B896783
  · exact B896787
  · exact B896791
  · exact B896795
  · exact B896799
  · exact B896803
  · exact B896807
  · exact B896811
  · exact B896815
  · exact B896819
  · exact B896823
  · exact B896827
  · exact B896831
  · exact B896835
  · exact B896839
  · exact B896843
  · exact B896847
  · exact B896851
  · exact B896855
  · exact B896859
  · exact B896863
  · exact B896867
  · exact B896871
  · exact B896875
  · exact B896879
  · exact B896883
  · exact B896887
  · exact B896891
  · exact B896895
  · exact B896899
  · exact B896903
  · exact B896907
  · exact B896911
  · exact B896915
  · exact B896919
  · exact B896923
  · exact B896927
  · exact B896931
  · exact B896935
  · exact B896939
  · exact B896943
  · exact B896947
  · exact B896951
  · exact B896955
  · exact B896959
  · exact B896963
  · exact B896967
  · exact B896971
  · exact B896975
  · exact B896979
  · exact B896983
  · exact B896987
  · exact B896991
  · exact B896995
  · exact B896999
  · exact B897003
  · exact B897007
  · exact B897011
  · exact B897015
  · exact B897019
  · exact B897023
  · exact B897027
  · exact B897031
  · exact B897035
  · exact B897039
  · exact B897043
  · exact B897047
  · exact B897051
  · exact B897055
  · exact B897059
  · exact B897063
  · exact B897067
  · exact B897071
  · exact B897075
  · exact B897079
  · exact B897083
  · exact B897087
  · exact B897091
  · exact B897095
  · exact B897099
  · exact B897103
  · exact B897107
  · exact B897111
  · exact B897115
  · exact B897119
  · exact B897123
  · exact B897127
  · exact B897131
  · exact B897135
  · exact B897139
  · exact B897143
  · exact B897147
  · exact B897151
  · exact B897155
  · exact B897159
  · exact B897163
  · exact B897167
  · exact B897171
  · exact B897175
  · exact B897179
  · exact B897183
  · exact B897187
  · exact B897191
  · exact B897195
  · exact B897199
  · exact B897203
  · exact B897207
  · exact B897211
  · exact B897215
  · exact B897219
  · exact B897223
  · exact B897227
  · exact B897231
  · exact B897235
  · exact B897239
  · exact B897243
  · exact B897247
  · exact B897251
  · exact B897255
  · exact B897259
  · exact B897263
  · exact B897267
  · exact B897271
  · exact B897275
  · exact B897279
  · exact B897283
  · exact B897287
  · exact B897291
  · exact B897295
  · exact B897299
  · exact B897303
  · exact B897307
  · exact B897311
  · exact B897315
  · exact B897319
  · exact B897323
  · exact B897327
  · exact B897331
  · exact B897335
  · exact B897339
  · exact B897343
  · exact B897347
  · exact B897351
  · exact B897355
  · exact B897359
  · exact B897363
  · exact B897367
  · exact B897371
  · exact B897375
  · exact B897379
  · exact B897383
  · exact B897387
  · exact B897391
  · exact B897395
  · exact B897399
  · exact B897403
  · exact B897407
  · exact B897411
  · exact B897415
  · exact B897419
  · exact B897423
  · exact B897427
  · exact B897431
  · exact B897435
  · exact B897439
  · exact B897443
  · exact B897447
  · exact B897451
  · exact B897455
  · exact B897459
  · exact B897463
  · exact B897467
  · exact B897471
  · exact B897475
  · exact B897479
  · exact B897483
  · exact B897487
  · exact B897491
  · exact B897495
  · exact B897499
  · exact B897503
  · exact B897507
  · exact B897511
  · exact B897515
  · exact B897519
  · exact B897523
  · exact B897527
  · exact B897531
  · exact B897535
  · exact B897539
  · exact B897543
  · exact B897547
  · exact B897551
  · exact B897555
  · exact B897559
  · exact B897563
  · exact B897567
  · exact B897571
  · exact B897575
  · exact B897579
  · exact B897583
  · exact B897587
  · exact B897591
  · exact B897595
  · exact B897599
  · exact B897603
  · exact B897607
  · exact B897611
  · exact B897615
  · exact B897619
  · exact B897623
  · exact B897627
  · exact B897631
  · exact B897635
  · exact B897639
  · exact B897643
  · exact B897647
  · exact B897651
  · exact B897655
  · exact B897659
  · exact B897663
  · exact B897667
  · exact B897671
  · exact B897675
  · exact B897679
  · exact B897683
  · exact B897687
  · exact B897691
  · exact B897695
  · exact B897699
  · exact B897703
  · exact B897707
  · exact B897711
  · exact B897715
  · exact B897719
  · exact B897723
  · exact B897727
  · exact B897731
  · exact B897735
  · exact B897739
  · exact B897743
  · exact B897747
  · exact B897751
  · exact B897755
  · exact B897759
  · exact B897763
  · exact B897767
  · exact B897771
  · exact B897775
  · exact B897779
  · exact B897783
  · exact B897787
  · exact B897791
  · exact B897795
  · exact B897799
  · exact B897803
  · exact B897807
  · exact B897811
  · exact B897815
  · exact B897819
  · exact B897823
  · exact B897827
  · exact B897831
  · exact B897835
  · exact B897839
  · exact B897843
  · exact B897847
  · exact B897851
  · exact B897855
  · exact B897859
  · exact B897863
  · exact B897867
  · exact B897871
  · exact B897875
  · exact B897879
  · exact B897883
  · exact B897887
  · exact B897891
  · exact B897895
  · exact B897899
  · exact B897903
  · exact B897907
  · exact B897911
  · exact B897915
  · exact B897919
  · exact B897923
  · exact B897927
  · exact B897931
  · exact B897935
  · exact B897939
  · exact B897943
  · exact B897947
  · exact B897951
  · exact B897955
  · exact B897959
  · exact B897963
  · exact B897967
  · exact B897971
  · exact B897975
  · exact B897979
  · exact B897983
  · exact B897987
  · exact B897991
  · exact B897995
  · exact B897999
  · exact B898003
  · exact B898007
  · exact B898011
  · exact B898015
  · exact B898019
  · exact B898023
  · exact B898027
  · exact B898031
  · exact B898035
  · exact B898039
  · exact B898043
  · exact B898047
  · exact B898051
  · exact B898055
  · exact B898059
  · exact B898063
  · exact B898067
  · exact B898071
  · exact B898075
  · exact B898079
  · exact B898083
  · exact B898087
  · exact B898091
  · exact B898095
  · exact B898099
  · exact B898103
  · exact B898107
  · exact B898111
  · exact B898115
  · exact B898119
  · exact B898123
  · exact B898127
  · exact B898131
  · exact B898135
  · exact B898139
  · exact B898143
  · exact B898147
  · exact B898151
  · exact B898155
  · exact B898159
  · exact B898163
  · exact B898167
  · exact B898171
  · exact B898175
  · exact B898179
  · exact B898183
  · exact B898187
  · exact B898191
  · exact B898195
  · exact B898199
  · exact B898203
  · exact B898207
  · exact B898211
  · exact B898215
  · exact B898219
  · exact B898223
  · exact B898227
  · exact B898231
  · exact B898235
  · exact B898239
  · exact B898243
  · exact B898247
  · exact B898251
  · exact B898255
  · exact B898259
  · exact B898263
  · exact B898267
  · exact B898271
  · exact B898275
  · exact B898279
  · exact B898283
  · exact B898287
  · exact B898291
  · exact B898295
  · exact B898299
  · exact B898303
  · exact B898307
  · exact B898311
  · exact B898315
  · exact B898319
  · exact B898323
  · exact B898327
  · exact B898331
  · exact B898335
  · exact B898339
  · exact B898343
  · exact B898347
  · exact B898351
  · exact B898355
  · exact B898359
  · exact B898363
  · exact B898367
  · exact B898371
  · exact B898375
  · exact B898379
  · exact B898383
  · exact B898387
  · exact B898391
  · exact B898395
  · exact B898399
  · exact B898403
  · exact B898407
  · exact B898411
  · exact B898415
  · exact B898419
  · exact B898423
  · exact B898427
  · exact B898431
  · exact B898435
  · exact B898439
  · exact B898443
  · exact B898447
  · exact B898451
  · exact B898455
  · exact B898459
  · exact B898463
  · exact B898467
  · exact B898471
  · exact B898475
  · exact B898479
  · exact B898483
  · exact B898487
  · exact B898491
  · exact B898495
  · exact B898499
  · exact B898503
  · exact B898507
  · exact B898511
  · exact B898515
  · exact B898519
  · exact B898523
  · exact B898527
  · exact B898531
  · exact B898535
  · exact B898539
  · exact B898543
  · exact B898547
  · exact B898551
  · exact B898555
  · exact B898559
  · exact B898563
  · exact B898567
  · exact B898571
  · exact B898575
  · exact B898579
  · exact B898583
  · exact B898587
  · exact B898591
  · exact B898595
  · exact B898599
  · exact B898603
  · exact B898607
  · exact B898611
  · exact B898615
  · exact B898619
  · exact B898623
  · exact B898627
  · exact B898631
  · exact B898635
  · exact B898639
  · exact B898643
  · exact B898647
  · exact B898651
  · exact B898655
  · exact B898659
  · exact B898663
  · exact B898667
  · exact B898671
  · exact B898675
  · exact B898679
  · exact B898683
  · exact B898687
  · exact B898691
  · exact B898695
  · exact B898699
  · exact B898703
  · exact B898707
  · exact B898711
  · exact B898715
  · exact B898719
  · exact B898723
  · exact B898727
  · exact B898731
  · exact B898735
  · exact B898739
  · exact B898743
  · exact B898747
  · exact B898751
  · exact B898755
  · exact B898759
  · exact B898763
  · exact B898767
  · exact B898771
  · exact B898775
  · exact B898779
  · exact B898783
  · exact B898787
  · exact B898791
  · exact B898795
  · exact B898799
  · exact B898803
  · exact B898807
  · exact B898811
  · exact B898815
  · exact B898819
  · exact B898823
  · exact B898827
  · exact B898831
  · exact B898835
  · exact B898839
  · exact B898843
  · exact B898847
  · exact B898851
  · exact B898855
  · exact B898859
  · exact B898863
  · exact B898867
  · exact B898871
  · exact B898875
  · exact B898879
  · exact B898883
  · exact B898887
  · exact B898891
  · exact B898895
  · exact B898899
  · exact B898903
  · exact B898907
  · exact B898911
  · exact B898915
  · exact B898919
  · exact B898923
  · exact B898927
  · exact B898931
  · exact B898935
  · exact B898939
  · exact B898943
  · exact B898947
  · exact B898951
  · exact B898955
  · exact B898959
  · exact B898963
  · exact B898967
  · exact B898971
  · exact B898975
  · exact B898979
  · exact B898983
  · exact B898987
  · exact B898991
  · exact B898995
  · exact B898999
  · exact B899003
  · exact B899007
  · exact B899011
  · exact B899015
  · exact B899019
  · exact B899023
  · exact B899027
  · exact B899031
  · exact B899035
  · exact B899039
  · exact B899043
  · exact B899047
  · exact B899051
  · exact B899055
  · exact B899059
  · exact B899063
  · exact B899067
  · exact B899071
  · exact B899075
  · exact B899079
  · exact B899083
  · exact B899087
  · exact B899091
  · exact B899095
  · exact B899099
  · exact B899103
  · exact B899107
  · exact B899111
  · exact B899115
  · exact B899119
  · exact B899123
  · exact B899127
  · exact B899131
  · exact B899135
  · exact B899139
  · exact B899143
  · exact B899147
  · exact B899151
  · exact B899155
  · exact B899159
  · exact B899163
  · exact B899167
  · exact B899171
  · exact B899175
  · exact B899179
  · exact B899183
  · exact B899187
  · exact B899191
  · exact B899195
  · exact B899199
  · exact B899203
  · exact B899207
  · exact B899211
  · exact B899215
  · exact B899219
  · exact B899223
  · exact B899227
  · exact B899231
  · exact B899235
  · exact B899239
  · exact B899243
  · exact B899247
  · exact B899251
  · exact B899255
  · exact B899259
  · exact B899263
  · exact B899267
  · exact B899271
  · exact B899275
  · exact B899279
  · exact B899283
  · exact B899287
  · exact B899291
  · exact B899295
  · exact B899299
  · exact B899303
  · exact B899307
  · exact B899311
  · exact B899315
  · exact B899319
  · exact B899323
  · exact B899327
  · exact B899331
  · exact B899335
  · exact B899339
  · exact B899343
  · exact B899347
  · exact B899351
  · exact B899355
  · exact B899359
  · exact B899363
  · exact B899367
  · exact B899371

theorem C1 (j : ℕ) (h1 : 224843 ≤ j) (h2 : j ≤ 225142) : Blo 896573 (4 * j + 3) := by
  interval_cases j
  · exact B899375
  · exact B899379
  · exact B899383
  · exact B899387
  · exact B899391
  · exact B899395
  · exact B899399
  · exact B899403
  · exact B899407
  · exact B899411
  · exact B899415
  · exact B899419
  · exact B899423
  · exact B899427
  · exact B899431
  · exact B899435
  · exact B899439
  · exact B899443
  · exact B899447
  · exact B899451
  · exact B899455
  · exact B899459
  · exact B899463
  · exact B899467
  · exact B899471
  · exact B899475
  · exact B899479
  · exact B899483
  · exact B899487
  · exact B899491
  · exact B899495
  · exact B899499
  · exact B899503
  · exact B899507
  · exact B899511
  · exact B899515
  · exact B899519
  · exact B899523
  · exact B899527
  · exact B899531
  · exact B899535
  · exact B899539
  · exact B899543
  · exact B899547
  · exact B899551
  · exact B899555
  · exact B899559
  · exact B899563
  · exact B899567
  · exact B899571
  · exact B899575
  · exact B899579
  · exact B899583
  · exact B899587
  · exact B899591
  · exact B899595
  · exact B899599
  · exact B899603
  · exact B899607
  · exact B899611
  · exact B899615
  · exact B899619
  · exact B899623
  · exact B899627
  · exact B899631
  · exact B899635
  · exact B899639
  · exact B899643
  · exact B899647
  · exact B899651
  · exact B899655
  · exact B899659
  · exact B899663
  · exact B899667
  · exact B899671
  · exact B899675
  · exact B899679
  · exact B899683
  · exact B899687
  · exact B899691
  · exact B899695
  · exact B899699
  · exact B899703
  · exact B899707
  · exact B899711
  · exact B899715
  · exact B899719
  · exact B899723
  · exact B899727
  · exact B899731
  · exact B899735
  · exact B899739
  · exact B899743
  · exact B899747
  · exact B899751
  · exact B899755
  · exact B899759
  · exact B899763
  · exact B899767
  · exact B899771
  · exact B899775
  · exact B899779
  · exact B899783
  · exact B899787
  · exact B899791
  · exact B899795
  · exact B899799
  · exact B899803
  · exact B899807
  · exact B899811
  · exact B899815
  · exact B899819
  · exact B899823
  · exact B899827
  · exact B899831
  · exact B899835
  · exact B899839
  · exact B899843
  · exact B899847
  · exact B899851
  · exact B899855
  · exact B899859
  · exact B899863
  · exact B899867
  · exact B899871
  · exact B899875
  · exact B899879
  · exact B899883
  · exact B899887
  · exact B899891
  · exact B899895
  · exact B899899
  · exact B899903
  · exact B899907
  · exact B899911
  · exact B899915
  · exact B899919
  · exact B899923
  · exact B899927
  · exact B899931
  · exact B899935
  · exact B899939
  · exact B899943
  · exact B899947
  · exact B899951
  · exact B899955
  · exact B899959
  · exact B899963
  · exact B899967
  · exact B899971
  · exact B899975
  · exact B899979
  · exact B899983
  · exact B899987
  · exact B899991
  · exact B899995
  · exact B899999
  · exact B900003
  · exact B900007
  · exact B900011
  · exact B900015
  · exact B900019
  · exact B900023
  · exact B900027
  · exact B900031
  · exact B900035
  · exact B900039
  · exact B900043
  · exact B900047
  · exact B900051
  · exact B900055
  · exact B900059
  · exact B900063
  · exact B900067
  · exact B900071
  · exact B900075
  · exact B900079
  · exact B900083
  · exact B900087
  · exact B900091
  · exact B900095
  · exact B900099
  · exact B900103
  · exact B900107
  · exact B900111
  · exact B900115
  · exact B900119
  · exact B900123
  · exact B900127
  · exact B900131
  · exact B900135
  · exact B900139
  · exact B900143
  · exact B900147
  · exact B900151
  · exact B900155
  · exact B900159
  · exact B900163
  · exact B900167
  · exact B900171
  · exact B900175
  · exact B900179
  · exact B900183
  · exact B900187
  · exact B900191
  · exact B900195
  · exact B900199
  · exact B900203
  · exact B900207
  · exact B900211
  · exact B900215
  · exact B900219
  · exact B900223
  · exact B900227
  · exact B900231
  · exact B900235
  · exact B900239
  · exact B900243
  · exact B900247
  · exact B900251
  · exact B900255
  · exact B900259
  · exact B900263
  · exact B900267
  · exact B900271
  · exact B900275
  · exact B900279
  · exact B900283
  · exact B900287
  · exact B900291
  · exact B900295
  · exact B900299
  · exact B900303
  · exact B900307
  · exact B900311
  · exact B900315
  · exact B900319
  · exact B900323
  · exact B900327
  · exact B900331
  · exact B900335
  · exact B900339
  · exact B900343
  · exact B900347
  · exact B900351
  · exact B900355
  · exact B900359
  · exact B900363
  · exact B900367
  · exact B900371
  · exact B900375
  · exact B900379
  · exact B900383
  · exact B900387
  · exact B900391
  · exact B900395
  · exact B900399
  · exact B900403
  · exact B900407
  · exact B900411
  · exact B900415
  · exact B900419
  · exact B900423
  · exact B900427
  · exact B900431
  · exact B900435
  · exact B900439
  · exact B900443
  · exact B900447
  · exact B900451
  · exact B900455
  · exact B900459
  · exact B900463
  · exact B900467
  · exact B900471
  · exact B900475
  · exact B900479
  · exact B900483
  · exact B900487
  · exact B900491
  · exact B900495
  · exact B900499
  · exact B900503
  · exact B900507
  · exact B900511
  · exact B900515
  · exact B900519
  · exact B900523
  · exact B900527
  · exact B900531
  · exact B900535
  · exact B900539
  · exact B900543
  · exact B900547
  · exact B900551
  · exact B900555
  · exact B900559
  · exact B900563
  · exact B900567
  · exact B900571

theorem solution (m : ℕ) (hlo : 896573 ≤ m) (hhi : m ≤ 900573) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 224143 ≤ j := by omega
    have hj2 : j ≤ 225142 := by omega
    have hb : Blo 896573 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 224843 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
