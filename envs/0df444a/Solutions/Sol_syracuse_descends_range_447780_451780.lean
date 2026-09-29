-- Prove2me | solution 1 for syracuse_descends_range_447780_451780
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:47:58.291005+00:00
-- url     : https://prove2.me/submissions/8639814b-3d10-4a4b-ba50-2bd875a6880e

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


theorem B1015829 : Blo 447780 1015829 := bbase (se 6 (by rfl) ⟨23808, by rfl⟩ : syracuseStep 1015829 = 47617) (by norm_num)
theorem B1015901 : Blo 447780 1015901 := bbase (se 3 (by rfl) ⟨190481, by rfl⟩ : syracuseStep 1015901 = 380963) (by norm_num)
theorem B1704037 : Blo 447780 1704037 := bbase (se 4 (by rfl) ⟨159753, by rfl⟩ : syracuseStep 1704037 = 319507) (by norm_num)
theorem B852133 : Blo 447780 852133 := bbase (se 4 (by rfl) ⟨79887, by rfl⟩ : syracuseStep 852133 = 159775) (by norm_num)
theorem B1015973 : Blo 447780 1015973 := bbase (se 4 (by rfl) ⟨95247, by rfl⟩ : syracuseStep 1015973 = 190495) (by norm_num)
theorem B1016045 : Blo 447780 1016045 := bbase (se 3 (by rfl) ⟨190508, by rfl⟩ : syracuseStep 1016045 = 381017) (by norm_num)
theorem B852277 : Blo 447780 852277 := bbase (se 5 (by rfl) ⟨39950, by rfl⟩ : syracuseStep 852277 = 79901) (by norm_num)
theorem B1016117 : Blo 447780 1016117 := bbase (se 5 (by rfl) ⟨47630, by rfl⟩ : syracuseStep 1016117 = 95261) (by norm_num)
theorem B1016189 : Blo 447780 1016189 := bbase (se 3 (by rfl) ⟨190535, by rfl⟩ : syracuseStep 1016189 = 381071) (by norm_num)
theorem B1704341 : Blo 447780 1704341 := bbase (se 6 (by rfl) ⟨39945, by rfl⟩ : syracuseStep 1704341 = 79891) (by norm_num)
theorem B1016261 : Blo 447780 1016261 := bbase (se 4 (by rfl) ⟨95274, by rfl⟩ : syracuseStep 1016261 = 190549) (by norm_num)
theorem B852437 : Blo 447780 852437 := bbase (se 7 (by rfl) ⟨9989, by rfl⟩ : syracuseStep 852437 = 19979) (by norm_num)
theorem B1016333 : Blo 447780 1016333 := bbase (se 3 (by rfl) ⟨190562, by rfl⟩ : syracuseStep 1016333 = 381125) (by norm_num)
theorem B1016405 : Blo 447780 1016405 := bbase (se 8 (by rfl) ⟨5955, by rfl⟩ : syracuseStep 1016405 = 11911) (by norm_num)
theorem B852581 : Blo 447780 852581 := bbase (se 4 (by rfl) ⟨79929, by rfl⟩ : syracuseStep 852581 = 159859) (by norm_num)
theorem B1016477 : Blo 447780 1016477 := bbase (se 3 (by rfl) ⟨190589, by rfl⟩ : syracuseStep 1016477 = 381179) (by norm_num)
theorem B1442549 : Blo 447780 1442549 := bbase (se 5 (by rfl) ⟨67619, by rfl⟩ : syracuseStep 1442549 = 135239) (by norm_num)
theorem B721685 : Blo 447780 721685 := bbase (se 6 (by rfl) ⟨16914, by rfl⟩ : syracuseStep 721685 = 33829) (by norm_num)
theorem B1278757 : Blo 447780 1278757 := bbase (se 4 (by rfl) ⟨119883, by rfl⟩ : syracuseStep 1278757 = 239767) (by norm_num)
theorem B1082173 : Blo 447780 1082173 := bbase (se 3 (by rfl) ⟨202907, by rfl⟩ : syracuseStep 1082173 = 405815) (by norm_num)
theorem B852869 : Blo 447780 852869 := bbase (se 4 (by rfl) ⟨79956, by rfl⟩ : syracuseStep 852869 = 159913) (by norm_num)
theorem B721813 : Blo 447780 721813 := bbase (se 6 (by rfl) ⟨16917, by rfl⟩ : syracuseStep 721813 = 33835) (by norm_num)
theorem B721877 : Blo 447780 721877 := bbase (se 7 (by rfl) ⟨8459, by rfl⟩ : syracuseStep 721877 = 16919) (by norm_num)
theorem B9765845 : Blo 447780 9765845 := bbase (se 7 (by rfl) ⟨114443, by rfl⟩ : syracuseStep 9765845 = 228887) (by norm_num)
theorem B853021 : Blo 447780 853021 := bbase (se 3 (by rfl) ⟨159941, by rfl⟩ : syracuseStep 853021 = 319883) (by norm_num)
theorem B853325 : Blo 447780 853325 := bbase (se 3 (by rfl) ⟨159998, by rfl⟩ : syracuseStep 853325 = 319997) (by norm_num)
theorem B460261 : Blo 447780 460261 := bbase (se 4 (by rfl) ⟨43149, by rfl⟩ : syracuseStep 460261 = 86299) (by norm_num)
theorem B2557493 : Blo 447780 2557493 := bbase (se 5 (by rfl) ⟨119882, by rfl⟩ : syracuseStep 2557493 = 239765) (by norm_num)
theorem B1443653 : Blo 447780 1443653 := bbase (se 4 (by rfl) ⟨135342, by rfl⟩ : syracuseStep 1443653 = 270685) (by norm_num)
theorem B755669 : Blo 447780 755669 := bbase (se 7 (by rfl) ⟨8855, by rfl⟩ : syracuseStep 755669 = 17711) (by norm_num)
theorem B526357 : Blo 447780 526357 := bbase (se 6 (by rfl) ⟨12336, by rfl⟩ : syracuseStep 526357 = 24673) (by norm_num)
theorem B854077 : Blo 447780 854077 := bbase (se 3 (by rfl) ⟨160139, by rfl⟩ : syracuseStep 854077 = 320279) (by norm_num)
theorem B755797 : Blo 447780 755797 := bbase (se 8 (by rfl) ⟨4428, by rfl⟩ : syracuseStep 755797 = 8857) (by norm_num)
theorem B7702613 : Blo 447780 7702613 := bbase (se 8 (by rfl) ⟨45132, by rfl⟩ : syracuseStep 7702613 = 90265) (by norm_num)
theorem B1083557 : Blo 447780 1083557 := bbase (se 4 (by rfl) ⟨101583, by rfl⟩ : syracuseStep 1083557 = 203167) (by norm_num)
theorem B755885 : Blo 447780 755885 := bbase (se 3 (by rfl) ⟨141728, by rfl⟩ : syracuseStep 755885 = 283457) (by norm_num)
theorem B1083565 : Blo 447780 1083565 := bbase (se 3 (by rfl) ⟨203168, by rfl⟩ : syracuseStep 1083565 = 406337) (by norm_num)
theorem B854221 : Blo 447780 854221 := bbase (se 3 (by rfl) ⟨160166, by rfl⟩ : syracuseStep 854221 = 320333) (by norm_num)
theorem B723197 : Blo 447780 723197 := bbase (se 3 (by rfl) ⟨135599, by rfl⟩ : syracuseStep 723197 = 271199) (by norm_num)
theorem B1280261 : Blo 447780 1280261 := bbase (se 4 (by rfl) ⟨120024, by rfl⟩ : syracuseStep 1280261 = 240049) (by norm_num)
theorem B756013 : Blo 447780 756013 := bbase (se 3 (by rfl) ⟨141752, by rfl⟩ : syracuseStep 756013 = 283505) (by norm_num)
theorem B3410261 : Blo 447780 3410261 := bbase (se 10 (by rfl) ⟨4995, by rfl⟩ : syracuseStep 3410261 = 9991) (by norm_num)
theorem B854381 : Blo 447780 854381 := bbase (se 3 (by rfl) ⟨160196, by rfl⟩ : syracuseStep 854381 = 320393) (by norm_num)
theorem B723325 : Blo 447780 723325 := bbase (se 3 (by rfl) ⟨135623, by rfl⟩ : syracuseStep 723325 = 271247) (by norm_num)
theorem B756101 : Blo 447780 756101 := bbase (se 4 (by rfl) ⟨70884, by rfl⟩ : syracuseStep 756101 = 141769) (by norm_num)
theorem B1706453 : Blo 447780 1706453 := bbase (se 7 (by rfl) ⟨19997, by rfl⟩ : syracuseStep 1706453 = 39995) (by norm_num)
theorem B854525 : Blo 447780 854525 := bbase (se 3 (by rfl) ⟨160223, by rfl⟩ : syracuseStep 854525 = 320447) (by norm_num)
theorem B756229 : Blo 447780 756229 := bbase (se 4 (by rfl) ⟨70896, by rfl⟩ : syracuseStep 756229 = 141793) (by norm_num)
theorem B2165285 : Blo 447780 2165285 := bbase (se 4 (by rfl) ⟨202995, by rfl⟩ : syracuseStep 2165285 = 405991) (by norm_num)
theorem B756317 : Blo 447780 756317 := bbase (se 3 (by rfl) ⟨141809, by rfl⟩ : syracuseStep 756317 = 283619) (by norm_num)
theorem B756445 : Blo 447780 756445 := bbase (se 3 (by rfl) ⟨141833, by rfl⟩ : syracuseStep 756445 = 283667) (by norm_num)
theorem B1706741 : Blo 447780 1706741 := bbase (se 5 (by rfl) ⟨80003, by rfl⟩ : syracuseStep 1706741 = 160007) (by norm_num)
theorem B854813 : Blo 447780 854813 := bbase (se 3 (by rfl) ⟨160277, by rfl⟩ : syracuseStep 854813 = 320555) (by norm_num)
theorem B756533 : Blo 447780 756533 := bbase (se 5 (by rfl) ⟨35462, by rfl⟩ : syracuseStep 756533 = 70925) (by norm_num)
theorem B461657 : Blo 447780 461657 := bbase (se 2 (by rfl) ⟨173121, by rfl⟩ : syracuseStep 461657 = 346243) (by norm_num)
theorem B756661 : Blo 447780 756661 := bbase (se 5 (by rfl) ⟨35468, by rfl⟩ : syracuseStep 756661 = 70937) (by norm_num)
theorem B854965 : Blo 447780 854965 := bbase (se 5 (by rfl) ⟨40076, by rfl⟩ : syracuseStep 854965 = 80153) (by norm_num)
theorem B756749 : Blo 447780 756749 := bbase (se 3 (by rfl) ⟨141890, by rfl⟩ : syracuseStep 756749 = 283781) (by norm_num)
theorem B756877 : Blo 447780 756877 := bbase (se 3 (by rfl) ⟨141914, by rfl⟩ : syracuseStep 756877 = 283829) (by norm_num)
theorem B1084565 : Blo 447780 1084565 := bbase (se 6 (by rfl) ⟨25419, by rfl⟩ : syracuseStep 1084565 = 50839) (by norm_num)
theorem B756965 : Blo 447780 756965 := bbase (se 4 (by rfl) ⟨70965, by rfl⟩ : syracuseStep 756965 = 141931) (by norm_num)
theorem B855269 : Blo 447780 855269 := bbase (se 4 (by rfl) ⟨80181, by rfl⟩ : syracuseStep 855269 = 160363) (by norm_num)
theorem B462061 : Blo 447780 462061 := bbase (se 3 (by rfl) ⟨86636, by rfl⟩ : syracuseStep 462061 = 173273) (by norm_num)
theorem B757093 : Blo 447780 757093 := bbase (se 4 (by rfl) ⟨70977, by rfl⟩ : syracuseStep 757093 = 141955) (by norm_num)
theorem B3837365 : Blo 447780 3837365 := bbase (se 5 (by rfl) ⟨179876, by rfl⟩ : syracuseStep 3837365 = 359753) (by norm_num)
theorem B757181 : Blo 447780 757181 := bbase (se 3 (by rfl) ⟨141971, by rfl⟩ : syracuseStep 757181 = 283943) (by norm_num)
theorem B757309 : Blo 447780 757309 := bbase (se 3 (by rfl) ⟨141995, by rfl⟩ : syracuseStep 757309 = 283991) (by norm_num)
theorem B2362949 : Blo 447780 2362949 := bbase (se 4 (by rfl) ⟨221526, by rfl⟩ : syracuseStep 2362949 = 443053) (by norm_num)
theorem B757397 : Blo 447780 757397 := bbase (se 6 (by rfl) ⟨17751, by rfl⟩ : syracuseStep 757397 = 35503) (by norm_num)
theorem B1445573 : Blo 447780 1445573 := bbase (se 4 (by rfl) ⟨135522, by rfl⟩ : syracuseStep 1445573 = 271045) (by norm_num)
theorem B2559701 : Blo 447780 2559701 := bbase (se 7 (by rfl) ⟨29996, by rfl⟩ : syracuseStep 2559701 = 59993) (by norm_num)
theorem B757525 : Blo 447780 757525 := bbase (se 6 (by rfl) ⟨17754, by rfl⟩ : syracuseStep 757525 = 35509) (by norm_num)
theorem B1281845 : Blo 447780 1281845 := bbase (se 5 (by rfl) ⟨60086, by rfl⟩ : syracuseStep 1281845 = 120173) (by norm_num)
theorem B757613 : Blo 447780 757613 := bbase (se 3 (by rfl) ⟨142052, by rfl⟩ : syracuseStep 757613 = 284105) (by norm_num)
theorem B1707925 : Blo 447780 1707925 := bbase (se 6 (by rfl) ⟨40029, by rfl⟩ : syracuseStep 1707925 = 80059) (by norm_num)
theorem B1085333 : Blo 447780 1085333 := bbase (se 6 (by rfl) ⟨25437, by rfl⟩ : syracuseStep 1085333 = 50875) (by norm_num)
theorem B2166709 : Blo 447780 2166709 := bbase (se 5 (by rfl) ⟨101564, by rfl⟩ : syracuseStep 2166709 = 203129) (by norm_num)
theorem B856021 : Blo 447780 856021 := bbase (se 7 (by rfl) ⟨10031, by rfl⟩ : syracuseStep 856021 = 20063) (by norm_num)
theorem B757741 : Blo 447780 757741 := bbase (se 3 (by rfl) ⟨142076, by rfl⟩ : syracuseStep 757741 = 284153) (by norm_num)
theorem B757829 : Blo 447780 757829 := bbase (se 4 (by rfl) ⟨71046, by rfl⟩ : syracuseStep 757829 = 142093) (by norm_num)
theorem B856165 : Blo 447780 856165 := bbase (se 4 (by rfl) ⟨80265, by rfl⟩ : syracuseStep 856165 = 160531) (by norm_num)
theorem B1511621 : Blo 447780 1511621 := bbase (se 4 (by rfl) ⟨141714, by rfl⟩ : syracuseStep 1511621 = 283429) (by norm_num)
theorem B757957 : Blo 447780 757957 := bbase (se 4 (by rfl) ⟨71058, by rfl⟩ : syracuseStep 757957 = 142117) (by norm_num)
theorem B1708229 : Blo 447780 1708229 := bbase (se 4 (by rfl) ⟨160146, by rfl⟩ : syracuseStep 1708229 = 320293) (by norm_num)
theorem B856325 : Blo 447780 856325 := bbase (se 4 (by rfl) ⟨80280, by rfl⟩ : syracuseStep 856325 = 160561) (by norm_num)
theorem B758045 : Blo 447780 758045 := bbase (se 3 (by rfl) ⟨142133, by rfl⟩ : syracuseStep 758045 = 284267) (by norm_num)
theorem B856469 : Blo 447780 856469 := bbase (se 6 (by rfl) ⟨20073, by rfl⟩ : syracuseStep 856469 = 40147) (by norm_num)
theorem B758173 : Blo 447780 758173 := bbase (se 3 (by rfl) ⟨142157, by rfl⟩ : syracuseStep 758173 = 284315) (by norm_num)
theorem B2298293 : Blo 447780 2298293 := bbase (se 5 (by rfl) ⟨107732, by rfl⟩ : syracuseStep 2298293 = 215465) (by norm_num)
theorem B1282517 : Blo 447780 1282517 := bbase (se 7 (by rfl) ⟨15029, by rfl⟩ : syracuseStep 1282517 = 30059) (by norm_num)
theorem B758261 : Blo 447780 758261 := bbase (se 5 (by rfl) ⟨35543, by rfl⟩ : syracuseStep 758261 = 71087) (by norm_num)
theorem B1512053 : Blo 447780 1512053 := bbase (se 5 (by rfl) ⟨70877, by rfl⟩ : syracuseStep 1512053 = 141755) (by norm_num)
theorem B758389 : Blo 447780 758389 := bbase (se 5 (by rfl) ⟨35549, by rfl⟩ : syracuseStep 758389 = 71099) (by norm_num)
theorem B856757 : Blo 447780 856757 := bbase (se 5 (by rfl) ⟨40160, by rfl⟩ : syracuseStep 856757 = 80321) (by norm_num)
theorem B758477 : Blo 447780 758477 := bbase (se 3 (by rfl) ⟨142214, by rfl⟩ : syracuseStep 758477 = 284429) (by norm_num)
theorem B758605 : Blo 447780 758605 := bbase (se 3 (by rfl) ⟨142238, by rfl⟩ : syracuseStep 758605 = 284477) (by norm_num)
theorem B856909 : Blo 447780 856909 := bbase (se 3 (by rfl) ⟨160670, by rfl⟩ : syracuseStep 856909 = 321341) (by norm_num)
theorem B1282949 : Blo 447780 1282949 := bbase (se 4 (by rfl) ⟨120276, by rfl⟩ : syracuseStep 1282949 = 240553) (by norm_num)
theorem B758693 : Blo 447780 758693 := bbase (se 4 (by rfl) ⟨71127, by rfl⟩ : syracuseStep 758693 = 142255) (by norm_num)
theorem B1512485 : Blo 447780 1512485 := bbase (se 4 (by rfl) ⟨141795, by rfl⟩ : syracuseStep 1512485 = 283591) (by norm_num)
theorem B758821 : Blo 447780 758821 := bbase (se 4 (by rfl) ⟨71139, by rfl⟩ : syracuseStep 758821 = 142279) (by norm_num)
theorem B1446997 : Blo 447780 1446997 := bbase (se 8 (by rfl) ⟨8478, by rfl⟩ : syracuseStep 1446997 = 16957) (by norm_num)
theorem B758909 : Blo 447780 758909 := bbase (se 3 (by rfl) ⟨142295, by rfl⟩ : syracuseStep 758909 = 284591) (by norm_num)
theorem B857213 : Blo 447780 857213 := bbase (se 3 (by rfl) ⟨160727, by rfl⟩ : syracuseStep 857213 = 321455) (by norm_num)
theorem B759037 : Blo 447780 759037 := bbase (se 3 (by rfl) ⟨142319, by rfl⟩ : syracuseStep 759037 = 284639) (by norm_num)
theorem B759125 : Blo 447780 759125 := bbase (se 14 (by rfl) ⟨69, by rfl⟩ : syracuseStep 759125 = 139) (by norm_num)
theorem B1512917 : Blo 447780 1512917 := bbase (se 7 (by rfl) ⟨17729, by rfl⟩ : syracuseStep 1512917 = 35459) (by norm_num)
theorem B759253 : Blo 447780 759253 := bbase (se 7 (by rfl) ⟨8897, by rfl⟩ : syracuseStep 759253 = 17795) (by norm_num)
theorem B759341 : Blo 447780 759341 := bbase (se 3 (by rfl) ⟨142376, by rfl⟩ : syracuseStep 759341 = 284753) (by norm_num)
theorem B1283701 : Blo 447780 1283701 := bbase (se 5 (by rfl) ⟨60173, by rfl⟩ : syracuseStep 1283701 = 120347) (by norm_num)
theorem B759469 : Blo 447780 759469 := bbase (se 3 (by rfl) ⟨142400, by rfl⟩ : syracuseStep 759469 = 284801) (by norm_num)
theorem B759557 : Blo 447780 759557 := bbase (se 4 (by rfl) ⟨71208, by rfl⟩ : syracuseStep 759557 = 142417) (by norm_num)
theorem B1513349 : Blo 447780 1513349 := bbase (se 4 (by rfl) ⟨141876, by rfl⟩ : syracuseStep 1513349 = 283753) (by norm_num)
theorem B759685 : Blo 447780 759685 := bbase (se 4 (by rfl) ⟨71220, by rfl⟩ : syracuseStep 759685 = 142441) (by norm_num)
theorem B759773 : Blo 447780 759773 := bbase (se 3 (by rfl) ⟨142457, by rfl⟩ : syracuseStep 759773 = 284915) (by norm_num)
theorem B694261 : Blo 447780 694261 := bbase (se 5 (by rfl) ⟨32543, by rfl⟩ : syracuseStep 694261 = 65087) (by norm_num)
theorem B2267189 : Blo 447780 2267189 := bbase (se 5 (by rfl) ⟨106274, by rfl⟩ : syracuseStep 2267189 = 212549) (by norm_num)
theorem B759901 : Blo 447780 759901 := bbase (se 3 (by rfl) ⟨142481, by rfl⟩ : syracuseStep 759901 = 284963) (by norm_num)
theorem B759989 : Blo 447780 759989 := bbase (se 5 (by rfl) ⟨35624, by rfl⟩ : syracuseStep 759989 = 71249) (by norm_num)
theorem B1710341 : Blo 447780 1710341 := bbase (se 4 (by rfl) ⟨160344, by rfl⟩ : syracuseStep 1710341 = 320689) (by norm_num)
theorem B1513781 : Blo 447780 1513781 := bbase (se 5 (by rfl) ⟨70958, by rfl⟩ : syracuseStep 1513781 = 141917) (by norm_num)
theorem B760117 : Blo 447780 760117 := bbase (se 5 (by rfl) ⟨35630, by rfl⟩ : syracuseStep 760117 = 71261) (by norm_num)
theorem B760205 : Blo 447780 760205 := bbase (se 3 (by rfl) ⟨142538, by rfl⟩ : syracuseStep 760205 = 285077) (by norm_num)
theorem B760333 : Blo 447780 760333 := bbase (se 3 (by rfl) ⟨142562, by rfl⟩ : syracuseStep 760333 = 285125) (by norm_num)
theorem B1710629 : Blo 447780 1710629 := bbase (se 4 (by rfl) ⟨160371, by rfl⟩ : syracuseStep 1710629 = 320743) (by norm_num)
theorem B760421 : Blo 447780 760421 := bbase (se 4 (by rfl) ⟨71289, by rfl⟩ : syracuseStep 760421 = 142579) (by norm_num)
theorem B1317541 : Blo 447780 1317541 := bbase (se 4 (by rfl) ⟨123519, by rfl⟩ : syracuseStep 1317541 = 247039) (by norm_num)
theorem B1514213 : Blo 447780 1514213 := bbase (se 4 (by rfl) ⟨141957, by rfl⟩ : syracuseStep 1514213 = 283915) (by norm_num)
theorem B760549 : Blo 447780 760549 := bbase (se 4 (by rfl) ⟨71301, by rfl⟩ : syracuseStep 760549 = 142603) (by norm_num)
theorem B760637 : Blo 447780 760637 := bbase (se 3 (by rfl) ⟨142619, by rfl⟩ : syracuseStep 760637 = 285239) (by norm_num)
theorem B760765 : Blo 447780 760765 := bbase (se 3 (by rfl) ⟨142643, by rfl⟩ : syracuseStep 760765 = 285287) (by norm_num)
theorem B760853 : Blo 447780 760853 := bbase (se 6 (by rfl) ⟨17832, by rfl⟩ : syracuseStep 760853 = 35665) (by norm_num)
theorem B957557 : Blo 447780 957557 := bbase (se 5 (by rfl) ⟨44885, by rfl⟩ : syracuseStep 957557 = 89771) (by norm_num)
theorem B760981 : Blo 447780 760981 := bbase (se 6 (by rfl) ⟨17835, by rfl⟩ : syracuseStep 760981 = 35671) (by norm_num)
theorem B1514645 : Blo 447780 1514645 := bbase (se 6 (by rfl) ⟨35499, by rfl⟩ : syracuseStep 1514645 = 70999) (by norm_num)
theorem B2923733 : Blo 447780 2923733 := bbase (se 7 (by rfl) ⟨34262, by rfl⟩ : syracuseStep 2923733 = 68525) (by norm_num)
theorem B761069 : Blo 447780 761069 := bbase (se 3 (by rfl) ⟨142700, by rfl⟩ : syracuseStep 761069 = 285401) (by norm_num)
theorem B957701 : Blo 447780 957701 := bbase (se 4 (by rfl) ⟨89784, by rfl⟩ : syracuseStep 957701 = 179569) (by norm_num)
theorem B2268485 : Blo 447780 2268485 := bbase (se 4 (by rfl) ⟨212670, by rfl⟩ : syracuseStep 2268485 = 425341) (by norm_num)
theorem B761197 : Blo 447780 761197 := bbase (se 3 (by rfl) ⟨142724, by rfl⟩ : syracuseStep 761197 = 285449) (by norm_num)
theorem B761285 : Blo 447780 761285 := bbase (se 4 (by rfl) ⟨71370, by rfl⟩ : syracuseStep 761285 = 142741) (by norm_num)
theorem B1515077 : Blo 447780 1515077 := bbase (se 4 (by rfl) ⟨142038, by rfl⟩ : syracuseStep 1515077 = 284077) (by norm_num)
theorem B761413 : Blo 447780 761413 := bbase (se 4 (by rfl) ⟨71382, by rfl⟩ : syracuseStep 761413 = 142765) (by norm_num)
theorem B958061 : Blo 447780 958061 := bbase (se 3 (by rfl) ⟨179636, by rfl⟩ : syracuseStep 958061 = 359273) (by norm_num)
theorem B761501 : Blo 447780 761501 := bbase (se 3 (by rfl) ⟨142781, by rfl⟩ : syracuseStep 761501 = 285563) (by norm_num)
theorem B1711813 : Blo 447780 1711813 := bbase (se 4 (by rfl) ⟨160482, by rfl⟩ : syracuseStep 1711813 = 320965) (by norm_num)
theorem B1220309 : Blo 447780 1220309 := bbase (se 7 (by rfl) ⟨14300, by rfl⟩ : syracuseStep 1220309 = 28601) (by norm_num)
theorem B761629 : Blo 447780 761629 := bbase (se 3 (by rfl) ⟨142805, by rfl⟩ : syracuseStep 761629 = 285611) (by norm_num)
theorem B761717 : Blo 447780 761717 := bbase (se 5 (by rfl) ⟨35705, by rfl⟩ : syracuseStep 761717 = 71411) (by norm_num)
theorem B1515509 : Blo 447780 1515509 := bbase (se 5 (by rfl) ⟨71039, by rfl⟩ : syracuseStep 1515509 = 142079) (by norm_num)
theorem B1712117 : Blo 447780 1712117 := bbase (se 5 (by rfl) ⟨80255, by rfl⟩ : syracuseStep 1712117 = 160511) (by norm_num)
theorem B761845 : Blo 447780 761845 := bbase (se 5 (by rfl) ⟨35711, by rfl⟩ : syracuseStep 761845 = 71423) (by norm_num)
theorem B761933 : Blo 447780 761933 := bbase (se 3 (by rfl) ⟨142862, by rfl⟩ : syracuseStep 761933 = 285725) (by norm_num)
theorem B762061 : Blo 447780 762061 := bbase (se 3 (by rfl) ⟨142886, by rfl⟩ : syracuseStep 762061 = 285773) (by norm_num)
theorem B2728181 : Blo 447780 2728181 := bbase (se 5 (by rfl) ⟨127883, by rfl⟩ : syracuseStep 2728181 = 255767) (by norm_num)
theorem B762149 : Blo 447780 762149 := bbase (se 4 (by rfl) ⟨71451, by rfl⟩ : syracuseStep 762149 = 142903) (by norm_num)
theorem B1515941 : Blo 447780 1515941 := bbase (se 4 (by rfl) ⟨142119, by rfl⟩ : syracuseStep 1515941 = 284239) (by norm_num)
theorem B762277 : Blo 447780 762277 := bbase (se 4 (by rfl) ⟨71463, by rfl⟩ : syracuseStep 762277 = 142927) (by norm_num)
theorem B958949 : Blo 447780 958949 := bbase (se 4 (by rfl) ⟨89901, by rfl⟩ : syracuseStep 958949 = 179803) (by norm_num)
theorem B762365 : Blo 447780 762365 := bbase (se 3 (by rfl) ⟨142943, by rfl⟩ : syracuseStep 762365 = 285887) (by norm_num)
theorem B2269781 : Blo 447780 2269781 := bbase (se 8 (by rfl) ⟨13299, by rfl⟩ : syracuseStep 2269781 = 26599) (by norm_num)
theorem B959197 : Blo 447780 959197 := bbase (se 3 (by rfl) ⟨179849, by rfl⟩ : syracuseStep 959197 = 359699) (by norm_num)
theorem B1516373 : Blo 447780 1516373 := bbase (se 9 (by rfl) ⟨4442, by rfl⟩ : syracuseStep 1516373 = 8885) (by norm_num)
theorem B1614725 : Blo 447780 1614725 := bbase (se 4 (by rfl) ⟨151380, by rfl⟩ : syracuseStep 1614725 = 302761) (by norm_num)
theorem B959701 : Blo 447780 959701 := bbase (se 7 (by rfl) ⟨11246, by rfl⟩ : syracuseStep 959701 = 22493) (by norm_num)
theorem B1516805 : Blo 447780 1516805 := bbase (se 4 (by rfl) ⟨142200, by rfl⟩ : syracuseStep 1516805 = 284401) (by norm_num)
theorem B1156445 : Blo 447780 1156445 := bbase (se 3 (by rfl) ⟨216833, by rfl⟩ : syracuseStep 1156445 = 433667) (by norm_num)
theorem B4335029 : Blo 447780 4335029 := bbase (se 5 (by rfl) ⟨203204, by rfl⟩ : syracuseStep 4335029 = 406409) (by norm_num)
theorem B566777 : Blo 447780 566777 := bbase (se 2 (by rfl) ⟨212541, by rfl⟩ : syracuseStep 566777 = 425083) (by norm_num)
theorem B566833 : Blo 447780 566833 := bbase (se 2 (by rfl) ⟨212562, by rfl⟩ : syracuseStep 566833 = 425125) (by norm_num)
theorem B566929 : Blo 447780 566929 := bbase (se 2 (by rfl) ⟨212598, by rfl⟩ : syracuseStep 566929 = 425197) (by norm_num)
theorem B1517237 : Blo 447780 1517237 := bbase (se 5 (by rfl) ⟨71120, by rfl⟩ : syracuseStep 1517237 = 142241) (by norm_num)
theorem B567101 : Blo 447780 567101 := bbase (se 3 (by rfl) ⟨106331, by rfl⟩ : syracuseStep 567101 = 212663) (by norm_num)
theorem B2271077 : Blo 447780 2271077 := bbase (se 4 (by rfl) ⟨212913, by rfl⟩ : syracuseStep 2271077 = 425827) (by norm_num)
theorem B567157 : Blo 447780 567157 := bbase (se 5 (by rfl) ⟨26585, by rfl⟩ : syracuseStep 567157 = 53171) (by norm_num)
theorem B3418037 : Blo 447780 3418037 := bbase (se 5 (by rfl) ⟨160220, by rfl⟩ : syracuseStep 3418037 = 320441) (by norm_num)
theorem B567253 : Blo 447780 567253 := bbase (se 7 (by rfl) ⟨6647, by rfl⟩ : syracuseStep 567253 = 13295) (by norm_num)
theorem B1714229 : Blo 447780 1714229 := bbase (se 5 (by rfl) ⟨80354, by rfl⟩ : syracuseStep 1714229 = 160709) (by norm_num)
theorem B960589 : Blo 447780 960589 := bbase (se 3 (by rfl) ⟨180110, by rfl⟩ : syracuseStep 960589 = 360221) (by norm_num)
theorem B1517669 : Blo 447780 1517669 := bbase (se 4 (by rfl) ⟨142281, by rfl⟩ : syracuseStep 1517669 = 284563) (by norm_num)
theorem B567425 : Blo 447780 567425 := bbase (se 2 (by rfl) ⟨212784, by rfl⟩ : syracuseStep 567425 = 425569) (by norm_num)
theorem B567481 : Blo 447780 567481 := bbase (se 2 (by rfl) ⟨212805, by rfl⟩ : syracuseStep 567481 = 425611) (by norm_num)
theorem B2894069 : Blo 447780 2894069 := bbase (se 5 (by rfl) ⟨135659, by rfl⟩ : syracuseStep 2894069 = 271319) (by norm_num)
theorem B567577 : Blo 447780 567577 := bbase (se 2 (by rfl) ⟨212841, by rfl⟩ : syracuseStep 567577 = 425683) (by norm_num)
theorem B3451189 : Blo 447780 3451189 := bbase (se 5 (by rfl) ⟨161774, by rfl⟩ : syracuseStep 3451189 = 323549) (by norm_num)
theorem B1714517 : Blo 447780 1714517 := bbase (se 10 (by rfl) ⟨2511, by rfl⟩ : syracuseStep 1714517 = 5023) (by norm_num)
theorem B3451253 : Blo 447780 3451253 := bbase (se 5 (by rfl) ⟨161777, by rfl⟩ : syracuseStep 3451253 = 323555) (by norm_num)
theorem B567749 : Blo 447780 567749 := bbase (se 4 (by rfl) ⟨53226, by rfl⟩ : syracuseStep 567749 = 106453) (by norm_num)
theorem B731605 : Blo 447780 731605 := bbase (se 7 (by rfl) ⟨8573, by rfl⟩ : syracuseStep 731605 = 17147) (by norm_num)
theorem B567805 : Blo 447780 567805 := bbase (se 3 (by rfl) ⟨106463, by rfl⟩ : syracuseStep 567805 = 212927) (by norm_num)
theorem B1518101 : Blo 447780 1518101 := bbase (se 6 (by rfl) ⟨35580, by rfl⟩ : syracuseStep 1518101 = 71161) (by norm_num)
theorem B1944101 : Blo 447780 1944101 := bbase (se 4 (by rfl) ⟨182259, by rfl⟩ : syracuseStep 1944101 = 364519) (by norm_num)
theorem B961085 : Blo 447780 961085 := bbase (se 3 (by rfl) ⟨180203, by rfl⟩ : syracuseStep 961085 = 360407) (by norm_num)
theorem B567901 : Blo 447780 567901 := bbase (se 3 (by rfl) ⟨106481, by rfl⟩ : syracuseStep 567901 = 212963) (by norm_num)
theorem B1092197 : Blo 447780 1092197 := bbase (se 4 (by rfl) ⟨102393, by rfl⟩ : syracuseStep 1092197 = 204787) (by norm_num)
theorem B2730709 : Blo 447780 2730709 := bbase (se 7 (by rfl) ⟨32000, by rfl⟩ : syracuseStep 2730709 = 64001) (by norm_num)
theorem B568073 : Blo 447780 568073 := bbase (se 2 (by rfl) ⟨213027, by rfl⟩ : syracuseStep 568073 = 426055) (by norm_num)
theorem B568129 : Blo 447780 568129 := bbase (se 2 (by rfl) ⟨213048, by rfl⟩ : syracuseStep 568129 = 426097) (by norm_num)
theorem B7875413 : Blo 447780 7875413 := bbase (se 9 (by rfl) ⟨23072, by rfl⟩ : syracuseStep 7875413 = 46145) (by norm_num)
theorem B4107125 : Blo 447780 4107125 := bbase (se 5 (by rfl) ⟨192521, by rfl⟩ : syracuseStep 4107125 = 385043) (by norm_num)
theorem B568225 : Blo 447780 568225 := bbase (se 2 (by rfl) ⟨213084, by rfl⟩ : syracuseStep 568225 = 426169) (by norm_num)
theorem B1518533 : Blo 447780 1518533 := bbase (se 4 (by rfl) ⟨142362, by rfl⟩ : syracuseStep 1518533 = 284725) (by norm_num)
theorem B1158085 : Blo 447780 1158085 := bbase (se 4 (by rfl) ⟨108570, by rfl⟩ : syracuseStep 1158085 = 217141) (by norm_num)
theorem B568397 : Blo 447780 568397 := bbase (se 3 (by rfl) ⟨106574, by rfl⟩ : syracuseStep 568397 = 213149) (by norm_num)
theorem B2272373 : Blo 447780 2272373 := bbase (se 5 (by rfl) ⟨106517, by rfl⟩ : syracuseStep 2272373 = 213035) (by norm_num)
theorem B568453 : Blo 447780 568453 := bbase (se 4 (by rfl) ⟨53292, by rfl⟩ : syracuseStep 568453 = 106585) (by norm_num)
theorem B568549 : Blo 447780 568549 := bbase (se 4 (by rfl) ⟨53301, by rfl⟩ : syracuseStep 568549 = 106603) (by norm_num)
theorem B1092973 : Blo 447780 1092973 := bbase (se 3 (by rfl) ⟨204932, by rfl⟩ : syracuseStep 1092973 = 409865) (by norm_num)
theorem B1518965 : Blo 447780 1518965 := bbase (se 5 (by rfl) ⟨71201, by rfl⟩ : syracuseStep 1518965 = 142403) (by norm_num)
theorem B568721 : Blo 447780 568721 := bbase (se 2 (by rfl) ⟨213270, by rfl⟩ : syracuseStep 568721 = 426541) (by norm_num)
theorem B961973 : Blo 447780 961973 := bbase (se 5 (by rfl) ⟨45092, by rfl⟩ : syracuseStep 961973 = 90185) (by norm_num)
theorem B568777 : Blo 447780 568777 := bbase (se 2 (by rfl) ⟨213291, by rfl⟩ : syracuseStep 568777 = 426583) (by norm_num)
theorem B568873 : Blo 447780 568873 := bbase (se 2 (by rfl) ⟨213327, by rfl⟩ : syracuseStep 568873 = 426655) (by norm_num)
theorem B962093 : Blo 447780 962093 := bbase (se 3 (by rfl) ⟨180392, by rfl⟩ : syracuseStep 962093 = 360785) (by norm_num)
theorem B10923605 : Blo 447780 10923605 := bbase (se 8 (by rfl) ⟨64005, by rfl⟩ : syracuseStep 10923605 = 128011) (by norm_num)
theorem B569045 : Blo 447780 569045 := bbase (se 7 (by rfl) ⟨6668, by rfl⟩ : syracuseStep 569045 = 13337) (by norm_num)
theorem B569101 : Blo 447780 569101 := bbase (se 3 (by rfl) ⟨106706, by rfl⟩ : syracuseStep 569101 = 213413) (by norm_num)
theorem B1519397 : Blo 447780 1519397 := bbase (se 4 (by rfl) ⟨142443, by rfl⟩ : syracuseStep 1519397 = 284887) (by norm_num)
theorem B1027885 : Blo 447780 1027885 := bbase (se 3 (by rfl) ⟨192728, by rfl⟩ : syracuseStep 1027885 = 385457) (by norm_num)
theorem B569197 : Blo 447780 569197 := bbase (se 3 (by rfl) ⟨106724, by rfl⟩ : syracuseStep 569197 = 213449) (by norm_num)
theorem B1027957 : Blo 447780 1027957 := bbase (se 5 (by rfl) ⟨48185, by rfl⟩ : syracuseStep 1027957 = 96371) (by norm_num)
theorem B503761 : Blo 447780 503761 := bbase (se 2 (by rfl) ⟨188910, by rfl⟩ : syracuseStep 503761 = 377821) (by norm_num)
theorem B1912805 : Blo 447780 1912805 := bbase (se 4 (by rfl) ⟨179325, by rfl⟩ : syracuseStep 1912805 = 358651) (by norm_num)
theorem B503797 : Blo 447780 503797 := bbase (se 5 (by rfl) ⟨23615, by rfl⟩ : syracuseStep 503797 = 47231) (by norm_num)
theorem B503833 : Blo 447780 503833 := bbase (se 2 (by rfl) ⟨188937, by rfl⟩ : syracuseStep 503833 = 377875) (by norm_num)
theorem B569369 : Blo 447780 569369 := bbase (se 2 (by rfl) ⟨213513, by rfl⟩ : syracuseStep 569369 = 427027) (by norm_num)
theorem B503869 : Blo 447780 503869 := bbase (se 3 (by rfl) ⟨94475, by rfl⟩ : syracuseStep 503869 = 188951) (by norm_num)
theorem B569425 : Blo 447780 569425 := bbase (se 2 (by rfl) ⟨213534, by rfl⟩ : syracuseStep 569425 = 427069) (by norm_num)
theorem B503905 : Blo 447780 503905 := bbase (se 2 (by rfl) ⟨188964, by rfl⟩ : syracuseStep 503905 = 377929) (by norm_num)
theorem B503941 : Blo 447780 503941 := bbase (se 4 (by rfl) ⟨47244, by rfl⟩ : syracuseStep 503941 = 94489) (by norm_num)
theorem B962725 : Blo 447780 962725 := bbase (se 4 (by rfl) ⟨90255, by rfl⟩ : syracuseStep 962725 = 180511) (by norm_num)
theorem B503977 : Blo 447780 503977 := bbase (se 2 (by rfl) ⟨188991, by rfl⟩ : syracuseStep 503977 = 377983) (by norm_num)
theorem B569521 : Blo 447780 569521 := bbase (se 2 (by rfl) ⟨213570, by rfl⟩ : syracuseStep 569521 = 427141) (by norm_num)
theorem B504013 : Blo 447780 504013 := bbase (se 3 (by rfl) ⟨94502, by rfl⟩ : syracuseStep 504013 = 189005) (by norm_num)
theorem B1519829 : Blo 447780 1519829 := bbase (se 7 (by rfl) ⟨17810, by rfl⟩ : syracuseStep 1519829 = 35621) (by norm_num)
theorem B504049 : Blo 447780 504049 := bbase (se 2 (by rfl) ⟨189018, by rfl⟩ : syracuseStep 504049 = 378037) (by norm_num)
theorem B504085 : Blo 447780 504085 := bbase (se 6 (by rfl) ⟨11814, by rfl⟩ : syracuseStep 504085 = 23629) (by norm_num)
theorem B504121 : Blo 447780 504121 := bbase (se 2 (by rfl) ⟨189045, by rfl⟩ : syracuseStep 504121 = 378091) (by norm_num)
theorem B504157 : Blo 447780 504157 := bbase (se 3 (by rfl) ⟨94529, by rfl⟩ : syracuseStep 504157 = 189059) (by norm_num)
theorem B569693 : Blo 447780 569693 := bbase (se 3 (by rfl) ⟨106817, by rfl⟩ : syracuseStep 569693 = 213635) (by norm_num)
theorem B504193 : Blo 447780 504193 := bbase (se 2 (by rfl) ⟨189072, by rfl⟩ : syracuseStep 504193 = 378145) (by norm_num)
theorem B2273669 : Blo 447780 2273669 := bbase (se 4 (by rfl) ⟨213156, by rfl⟩ : syracuseStep 2273669 = 426313) (by norm_num)
theorem B569749 : Blo 447780 569749 := bbase (se 6 (by rfl) ⟨13353, by rfl⟩ : syracuseStep 569749 = 26707) (by norm_num)
theorem B504229 : Blo 447780 504229 := bbase (se 4 (by rfl) ⟨47271, by rfl⟩ : syracuseStep 504229 = 94543) (by norm_num)
theorem B2306501 : Blo 447780 2306501 := bbase (se 4 (by rfl) ⟨216234, by rfl⟩ : syracuseStep 2306501 = 432469) (by norm_num)
theorem B504265 : Blo 447780 504265 := bbase (se 2 (by rfl) ⟨189099, by rfl⟩ : syracuseStep 504265 = 378199) (by norm_num)
theorem B504301 : Blo 447780 504301 := bbase (se 3 (by rfl) ⟨94556, by rfl⟩ : syracuseStep 504301 = 189113) (by norm_num)
theorem B569845 : Blo 447780 569845 := bbase (se 5 (by rfl) ⟨26711, by rfl⟩ : syracuseStep 569845 = 53423) (by norm_num)
theorem B504337 : Blo 447780 504337 := bbase (se 2 (by rfl) ⟨189126, by rfl⟩ : syracuseStep 504337 = 378253) (by norm_num)
theorem B504373 : Blo 447780 504373 := bbase (se 5 (by rfl) ⟨23642, by rfl⟩ : syracuseStep 504373 = 47285) (by norm_num)
theorem B504409 : Blo 447780 504409 := bbase (se 2 (by rfl) ⟨189153, by rfl⟩ : syracuseStep 504409 = 378307) (by norm_num)
theorem B504445 : Blo 447780 504445 := bbase (se 3 (by rfl) ⟨94583, by rfl⟩ : syracuseStep 504445 = 189167) (by norm_num)
theorem B1520261 : Blo 447780 1520261 := bbase (se 4 (by rfl) ⟨142524, by rfl⟩ : syracuseStep 1520261 = 285049) (by norm_num)
theorem B504481 : Blo 447780 504481 := bbase (se 2 (by rfl) ⟨189180, by rfl⟩ : syracuseStep 504481 = 378361) (by norm_num)
theorem B570017 : Blo 447780 570017 := bbase (se 2 (by rfl) ⟨213756, by rfl⟩ : syracuseStep 570017 = 427513) (by norm_num)
theorem B4108981 : Blo 447780 4108981 := bbase (se 5 (by rfl) ⟨192608, by rfl⟩ : syracuseStep 4108981 = 385217) (by norm_num)
theorem B504517 : Blo 447780 504517 := bbase (se 4 (by rfl) ⟨47298, by rfl⟩ : syracuseStep 504517 = 94597) (by norm_num)
theorem B1913557 : Blo 447780 1913557 := bbase (se 7 (by rfl) ⟨22424, by rfl⟩ : syracuseStep 1913557 = 44849) (by norm_num)
theorem B570073 : Blo 447780 570073 := bbase (se 2 (by rfl) ⟨213777, by rfl⟩ : syracuseStep 570073 = 427555) (by norm_num)
theorem B504553 : Blo 447780 504553 := bbase (se 2 (by rfl) ⟨189207, by rfl⟩ : syracuseStep 504553 = 378415) (by norm_num)
theorem B504589 : Blo 447780 504589 := bbase (se 3 (by rfl) ⟨94610, by rfl⟩ : syracuseStep 504589 = 189221) (by norm_num)
theorem B504625 : Blo 447780 504625 := bbase (se 2 (by rfl) ⟨189234, by rfl⟩ : syracuseStep 504625 = 378469) (by norm_num)
theorem B570169 : Blo 447780 570169 := bbase (se 2 (by rfl) ⟨213813, by rfl⟩ : syracuseStep 570169 = 427627) (by norm_num)
theorem B504661 : Blo 447780 504661 := bbase (se 9 (by rfl) ⟨1478, by rfl⟩ : syracuseStep 504661 = 2957) (by norm_num)
theorem B504697 : Blo 447780 504697 := bbase (se 2 (by rfl) ⟨189261, by rfl⟩ : syracuseStep 504697 = 378523) (by norm_num)
theorem B1848197 : Blo 447780 1848197 := bbase (se 4 (by rfl) ⟨173268, by rfl⟩ : syracuseStep 1848197 = 346537) (by norm_num)
theorem B504733 : Blo 447780 504733 := bbase (se 3 (by rfl) ⟨94637, by rfl⟩ : syracuseStep 504733 = 189275) (by norm_num)
theorem B504769 : Blo 447780 504769 := bbase (se 2 (by rfl) ⟨189288, by rfl⟩ : syracuseStep 504769 = 378577) (by norm_num)
theorem B504805 : Blo 447780 504805 := bbase (se 4 (by rfl) ⟨47325, by rfl⟩ : syracuseStep 504805 = 94651) (by norm_num)
theorem B570341 : Blo 447780 570341 := bbase (se 4 (by rfl) ⟨53469, by rfl⟩ : syracuseStep 570341 = 106939) (by norm_num)
theorem B504841 : Blo 447780 504841 := bbase (se 2 (by rfl) ⟨189315, by rfl⟩ : syracuseStep 504841 = 378631) (by norm_num)
theorem B570397 : Blo 447780 570397 := bbase (se 3 (by rfl) ⟨106949, by rfl⟩ : syracuseStep 570397 = 213899) (by norm_num)
theorem B963613 : Blo 447780 963613 := bbase (se 3 (by rfl) ⟨180677, by rfl⟩ : syracuseStep 963613 = 361355) (by norm_num)
theorem B504877 : Blo 447780 504877 := bbase (se 3 (by rfl) ⟨94664, by rfl⟩ : syracuseStep 504877 = 189329) (by norm_num)
theorem B1520693 : Blo 447780 1520693 := bbase (se 5 (by rfl) ⟨71282, by rfl⟩ : syracuseStep 1520693 = 142565) (by norm_num)
theorem B504913 : Blo 447780 504913 := bbase (se 2 (by rfl) ⟨189342, by rfl⟩ : syracuseStep 504913 = 378685) (by norm_num)
theorem B504949 : Blo 447780 504949 := bbase (se 5 (by rfl) ⟨23669, by rfl⟩ : syracuseStep 504949 = 47339) (by norm_num)
theorem B570493 : Blo 447780 570493 := bbase (se 3 (by rfl) ⟨106967, by rfl⟩ : syracuseStep 570493 = 213935) (by norm_num)
theorem B963733 : Blo 447780 963733 := bbase (se 6 (by rfl) ⟨22587, by rfl⟩ : syracuseStep 963733 = 45175) (by norm_num)
theorem B504985 : Blo 447780 504985 := bbase (se 2 (by rfl) ⟨189369, by rfl⟩ : syracuseStep 504985 = 378739) (by norm_num)
theorem B505021 : Blo 447780 505021 := bbase (se 3 (by rfl) ⟨94691, by rfl⟩ : syracuseStep 505021 = 189383) (by norm_num)
theorem B505057 : Blo 447780 505057 := bbase (se 2 (by rfl) ⟨189396, by rfl⟩ : syracuseStep 505057 = 378793) (by norm_num)
theorem B505093 : Blo 447780 505093 := bbase (se 4 (by rfl) ⟨47352, by rfl⟩ : syracuseStep 505093 = 94705) (by norm_num)
theorem B505129 : Blo 447780 505129 := bbase (se 2 (by rfl) ⟨189423, by rfl⟩ : syracuseStep 505129 = 378847) (by norm_num)
theorem B570665 : Blo 447780 570665 := bbase (se 2 (by rfl) ⟨213999, by rfl⟩ : syracuseStep 570665 = 427999) (by norm_num)
theorem B505165 : Blo 447780 505165 := bbase (se 3 (by rfl) ⟨94718, by rfl⟩ : syracuseStep 505165 = 189437) (by norm_num)
theorem B570721 : Blo 447780 570721 := bbase (se 2 (by rfl) ⟨214020, by rfl⟩ : syracuseStep 570721 = 428041) (by norm_num)
theorem B505201 : Blo 447780 505201 := bbase (se 2 (by rfl) ⟨189450, by rfl⟩ : syracuseStep 505201 = 378901) (by norm_num)
theorem B2569589 : Blo 447780 2569589 := bbase (se 5 (by rfl) ⟨120449, by rfl⟩ : syracuseStep 2569589 = 240899) (by norm_num)
theorem B505237 : Blo 447780 505237 := bbase (se 6 (by rfl) ⟨11841, by rfl⟩ : syracuseStep 505237 = 23683) (by norm_num)
theorem B963989 : Blo 447780 963989 := bbase (se 6 (by rfl) ⟨22593, by rfl⟩ : syracuseStep 963989 = 45187) (by norm_num)
theorem B1914293 : Blo 447780 1914293 := bbase (se 5 (by rfl) ⟨89732, by rfl⟩ : syracuseStep 1914293 = 179465) (by norm_num)
theorem B505273 : Blo 447780 505273 := bbase (se 2 (by rfl) ⟨189477, by rfl⟩ : syracuseStep 505273 = 378955) (by norm_num)
theorem B570817 : Blo 447780 570817 := bbase (se 2 (by rfl) ⟨214056, by rfl⟩ : syracuseStep 570817 = 428113) (by norm_num)
theorem B505309 : Blo 447780 505309 := bbase (se 3 (by rfl) ⟨94745, by rfl⟩ : syracuseStep 505309 = 189491) (by norm_num)
theorem B1521125 : Blo 447780 1521125 := bbase (se 4 (by rfl) ⟨142605, by rfl⟩ : syracuseStep 1521125 = 285211) (by norm_num)
theorem B505345 : Blo 447780 505345 := bbase (se 2 (by rfl) ⟨189504, by rfl⟩ : syracuseStep 505345 = 379009) (by norm_num)
theorem B505381 : Blo 447780 505381 := bbase (se 4 (by rfl) ⟨47379, by rfl⟩ : syracuseStep 505381 = 94759) (by norm_num)
theorem B538169 : Blo 447780 538169 := bbase (se 2 (by rfl) ⟨201813, by rfl⟩ : syracuseStep 538169 = 403627) (by norm_num)
theorem B767549 : Blo 447780 767549 := bbase (se 3 (by rfl) ⟨143915, by rfl⟩ : syracuseStep 767549 = 287831) (by norm_num)
theorem B505417 : Blo 447780 505417 := bbase (se 2 (by rfl) ⟨189531, by rfl⟩ : syracuseStep 505417 = 379063) (by norm_num)
theorem B505453 : Blo 447780 505453 := bbase (se 3 (by rfl) ⟨94772, by rfl⟩ : syracuseStep 505453 = 189545) (by norm_num)
theorem B570989 : Blo 447780 570989 := bbase (se 3 (by rfl) ⟨107060, by rfl⟩ : syracuseStep 570989 = 214121) (by norm_num)
theorem B505489 : Blo 447780 505489 := bbase (se 2 (by rfl) ⟨189558, by rfl⟩ : syracuseStep 505489 = 379117) (by norm_num)
theorem B2274965 : Blo 447780 2274965 := bbase (se 6 (by rfl) ⟨53319, by rfl⟩ : syracuseStep 2274965 = 106639) (by norm_num)
theorem B571045 : Blo 447780 571045 := bbase (se 4 (by rfl) ⟨53535, by rfl⟩ : syracuseStep 571045 = 107071) (by norm_num)
theorem B505525 : Blo 447780 505525 := bbase (se 5 (by rfl) ⟨23696, by rfl⟩ : syracuseStep 505525 = 47393) (by norm_num)
theorem B505561 : Blo 447780 505561 := bbase (se 2 (by rfl) ⟨189585, by rfl⟩ : syracuseStep 505561 = 379171) (by norm_num)
theorem B997085 : Blo 447780 997085 := bbase (se 3 (by rfl) ⟨186953, by rfl⟩ : syracuseStep 997085 = 373907) (by norm_num)
theorem B505597 : Blo 447780 505597 := bbase (se 3 (by rfl) ⟨94799, by rfl⟩ : syracuseStep 505597 = 189599) (by norm_num)
theorem B571141 : Blo 447780 571141 := bbase (se 4 (by rfl) ⟨53544, by rfl⟩ : syracuseStep 571141 = 107089) (by norm_num)
theorem B3127061 : Blo 447780 3127061 := bbase (se 6 (by rfl) ⟨73290, by rfl⟩ : syracuseStep 3127061 = 146581) (by norm_num)
theorem B505633 : Blo 447780 505633 := bbase (se 2 (by rfl) ⟨189612, by rfl⟩ : syracuseStep 505633 = 379225) (by norm_num)
theorem B505669 : Blo 447780 505669 := bbase (se 4 (by rfl) ⟨47406, by rfl⟩ : syracuseStep 505669 = 94813) (by norm_num)
theorem B1947493 : Blo 447780 1947493 := bbase (se 4 (by rfl) ⟨182577, by rfl⟩ : syracuseStep 1947493 = 365155) (by norm_num)
theorem B505705 : Blo 447780 505705 := bbase (se 2 (by rfl) ⟨189639, by rfl⟩ : syracuseStep 505705 = 379279) (by norm_num)
theorem B505741 : Blo 447780 505741 := bbase (se 3 (by rfl) ⟨94826, by rfl⟩ : syracuseStep 505741 = 189653) (by norm_num)
theorem B1521557 : Blo 447780 1521557 := bbase (se 6 (by rfl) ⟨35661, by rfl⟩ : syracuseStep 1521557 = 71323) (by norm_num)
theorem B505777 : Blo 447780 505777 := bbase (se 2 (by rfl) ⟨189666, by rfl⟩ : syracuseStep 505777 = 379333) (by norm_num)
theorem B571313 : Blo 447780 571313 := bbase (se 2 (by rfl) ⟨214242, by rfl⟩ : syracuseStep 571313 = 428485) (by norm_num)
theorem B505813 : Blo 447780 505813 := bbase (se 7 (by rfl) ⟨5927, by rfl⟩ : syracuseStep 505813 = 11855) (by norm_num)
theorem B571369 : Blo 447780 571369 := bbase (se 2 (by rfl) ⟨214263, by rfl⟩ : syracuseStep 571369 = 428527) (by norm_num)
theorem B505849 : Blo 447780 505849 := bbase (se 2 (by rfl) ⟨189693, by rfl⟩ : syracuseStep 505849 = 379387) (by norm_num)
theorem B505885 : Blo 447780 505885 := bbase (se 3 (by rfl) ⟨94853, by rfl⟩ : syracuseStep 505885 = 189707) (by norm_num)
theorem B505921 : Blo 447780 505921 := bbase (se 2 (by rfl) ⟨189720, by rfl⟩ : syracuseStep 505921 = 379441) (by norm_num)
theorem B571465 : Blo 447780 571465 := bbase (se 2 (by rfl) ⟨214299, by rfl⟩ : syracuseStep 571465 = 428599) (by norm_num)
theorem B505957 : Blo 447780 505957 := bbase (se 4 (by rfl) ⟨47433, by rfl⟩ : syracuseStep 505957 = 94867) (by norm_num)
theorem B1620101 : Blo 447780 1620101 := bbase (se 4 (by rfl) ⟨151884, by rfl⟩ : syracuseStep 1620101 = 303769) (by norm_num)
theorem B505993 : Blo 447780 505993 := bbase (se 2 (by rfl) ⟨189747, by rfl⟩ : syracuseStep 505993 = 379495) (by norm_num)
theorem B506029 : Blo 447780 506029 := bbase (se 3 (by rfl) ⟨94880, by rfl⟩ : syracuseStep 506029 = 189761) (by norm_num)
theorem B506065 : Blo 447780 506065 := bbase (se 2 (by rfl) ⟨189774, by rfl⟩ : syracuseStep 506065 = 379549) (by norm_num)
theorem B538861 : Blo 447780 538861 := bbase (se 3 (by rfl) ⟨101036, by rfl⟩ : syracuseStep 538861 = 202073) (by norm_num)
theorem B506101 : Blo 447780 506101 := bbase (se 5 (by rfl) ⟨23723, by rfl⟩ : syracuseStep 506101 = 47447) (by norm_num)
theorem B571637 : Blo 447780 571637 := bbase (se 5 (by rfl) ⟨26795, by rfl⟩ : syracuseStep 571637 = 53591) (by norm_num)
theorem B964877 : Blo 447780 964877 := bbase (se 3 (by rfl) ⟨180914, by rfl⟩ : syracuseStep 964877 = 361829) (by norm_num)
theorem B506137 : Blo 447780 506137 := bbase (se 2 (by rfl) ⟨189801, by rfl⟩ : syracuseStep 506137 = 379603) (by norm_num)
theorem B571693 : Blo 447780 571693 := bbase (se 3 (by rfl) ⟨107192, by rfl⟩ : syracuseStep 571693 = 214385) (by norm_num)
theorem B506173 : Blo 447780 506173 := bbase (se 3 (by rfl) ⟨94907, by rfl⟩ : syracuseStep 506173 = 189815) (by norm_num)
theorem B1521989 : Blo 447780 1521989 := bbase (se 4 (by rfl) ⟨142686, by rfl⟩ : syracuseStep 1521989 = 285373) (by norm_num)
theorem B538957 : Blo 447780 538957 := bbase (se 3 (by rfl) ⟨101054, by rfl⟩ : syracuseStep 538957 = 202109) (by norm_num)
theorem B506209 : Blo 447780 506209 := bbase (se 2 (by rfl) ⟨189828, by rfl⟩ : syracuseStep 506209 = 379657) (by norm_num)
theorem B506245 : Blo 447780 506245 := bbase (se 4 (by rfl) ⟨47460, by rfl⟩ : syracuseStep 506245 = 94921) (by norm_num)
theorem B1980805 : Blo 447780 1980805 := bbase (se 4 (by rfl) ⟨185700, by rfl⟩ : syracuseStep 1980805 = 371401) (by norm_num)
theorem B506281 : Blo 447780 506281 := bbase (se 2 (by rfl) ⟨189855, by rfl⟩ : syracuseStep 506281 = 379711) (by norm_num)
theorem B506317 : Blo 447780 506317 := bbase (se 3 (by rfl) ⟨94934, by rfl⟩ : syracuseStep 506317 = 189869) (by norm_num)
theorem B506353 : Blo 447780 506353 := bbase (se 2 (by rfl) ⟨189882, by rfl⟩ : syracuseStep 506353 = 379765) (by norm_num)
theorem B506389 : Blo 447780 506389 := bbase (se 6 (by rfl) ⟨11868, by rfl⟩ : syracuseStep 506389 = 23737) (by norm_num)
theorem B1620533 : Blo 447780 1620533 := bbase (se 5 (by rfl) ⟨75962, by rfl⟩ : syracuseStep 1620533 = 151925) (by norm_num)
theorem B506425 : Blo 447780 506425 := bbase (se 2 (by rfl) ⟨189909, by rfl⟩ : syracuseStep 506425 = 379819) (by norm_num)
theorem B2964053 : Blo 447780 2964053 := bbase (se 8 (by rfl) ⟨17367, by rfl⟩ : syracuseStep 2964053 = 34735) (by norm_num)
theorem B506461 : Blo 447780 506461 := bbase (se 3 (by rfl) ⟨94961, by rfl⟩ : syracuseStep 506461 = 189923) (by norm_num)
theorem B506497 : Blo 447780 506497 := bbase (se 2 (by rfl) ⟨189936, by rfl⟩ : syracuseStep 506497 = 379873) (by norm_num)
theorem B506533 : Blo 447780 506533 := bbase (se 4 (by rfl) ⟨47487, by rfl⟩ : syracuseStep 506533 = 94975) (by norm_num)
theorem B506569 : Blo 447780 506569 := bbase (se 2 (by rfl) ⟨189963, by rfl⟩ : syracuseStep 506569 = 379927) (by norm_num)
theorem B506605 : Blo 447780 506605 := bbase (se 3 (by rfl) ⟨94988, by rfl⟩ : syracuseStep 506605 = 189977) (by norm_num)
theorem B1522421 : Blo 447780 1522421 := bbase (se 5 (by rfl) ⟨71363, by rfl⟩ : syracuseStep 1522421 = 142727) (by norm_num)
theorem B506641 : Blo 447780 506641 := bbase (se 2 (by rfl) ⟨189990, by rfl⟩ : syracuseStep 506641 = 379981) (by norm_num)
theorem B637733 : Blo 447780 637733 := bbase (se 4 (by rfl) ⟨59787, by rfl⟩ : syracuseStep 637733 = 119575) (by norm_num)
theorem B506677 : Blo 447780 506677 := bbase (se 5 (by rfl) ⟨23750, by rfl⟩ : syracuseStep 506677 = 47501) (by norm_num)
theorem B867125 : Blo 447780 867125 := bbase (se 5 (by rfl) ⟨40646, by rfl⟩ : syracuseStep 867125 = 81293) (by norm_num)
theorem B2308949 : Blo 447780 2308949 := bbase (se 9 (by rfl) ⟨6764, by rfl⟩ : syracuseStep 2308949 = 13529) (by norm_num)
theorem B506713 : Blo 447780 506713 := bbase (se 2 (by rfl) ⟨190017, by rfl⟩ : syracuseStep 506713 = 380035) (by norm_num)
theorem B506749 : Blo 447780 506749 := bbase (se 3 (by rfl) ⟨95015, by rfl⟩ : syracuseStep 506749 = 190031) (by norm_num)
theorem B506785 : Blo 447780 506785 := bbase (se 2 (by rfl) ⟨190044, by rfl⟩ : syracuseStep 506785 = 380089) (by norm_num)
theorem B2276261 : Blo 447780 2276261 := bbase (se 4 (by rfl) ⟨213399, by rfl⟩ : syracuseStep 2276261 = 426799) (by norm_num)
theorem B506821 : Blo 447780 506821 := bbase (se 4 (by rfl) ⟨47514, by rfl⟩ : syracuseStep 506821 = 95029) (by norm_num)
theorem B506857 : Blo 447780 506857 := bbase (se 2 (by rfl) ⟨190071, by rfl⟩ : syracuseStep 506857 = 380143) (by norm_num)
theorem B506893 : Blo 447780 506893 := bbase (se 3 (by rfl) ⟨95042, by rfl⟩ : syracuseStep 506893 = 190085) (by norm_num)
theorem B506929 : Blo 447780 506929 := bbase (se 2 (by rfl) ⟨190098, by rfl⟩ : syracuseStep 506929 = 380197) (by norm_num)
theorem B506965 : Blo 447780 506965 := bbase (se 8 (by rfl) ⟨2970, by rfl⟩ : syracuseStep 506965 = 5941) (by norm_num)
theorem B539741 : Blo 447780 539741 := bbase (se 3 (by rfl) ⟨101201, by rfl⟩ : syracuseStep 539741 = 202403) (by norm_num)
theorem B507001 : Blo 447780 507001 := bbase (se 2 (by rfl) ⟨190125, by rfl⟩ : syracuseStep 507001 = 380251) (by norm_num)
theorem B507037 : Blo 447780 507037 := bbase (se 3 (by rfl) ⟨95069, by rfl⟩ : syracuseStep 507037 = 190139) (by norm_num)
theorem B1522853 : Blo 447780 1522853 := bbase (se 4 (by rfl) ⟨142767, by rfl⟩ : syracuseStep 1522853 = 285535) (by norm_num)
theorem B507073 : Blo 447780 507073 := bbase (se 2 (by rfl) ⟨190152, by rfl⟩ : syracuseStep 507073 = 380305) (by norm_num)
theorem B507109 : Blo 447780 507109 := bbase (se 4 (by rfl) ⟨47541, by rfl⟩ : syracuseStep 507109 = 95083) (by norm_num)
theorem B572653 : Blo 447780 572653 := bbase (se 3 (by rfl) ⟨107372, by rfl⟩ : syracuseStep 572653 = 214745) (by norm_num)
theorem B507145 : Blo 447780 507145 := bbase (se 2 (by rfl) ⟨190179, by rfl⟩ : syracuseStep 507145 = 380359) (by norm_num)
theorem B507181 : Blo 447780 507181 := bbase (se 3 (by rfl) ⟨95096, by rfl⟩ : syracuseStep 507181 = 190193) (by norm_num)
theorem B638285 : Blo 447780 638285 := bbase (se 3 (by rfl) ⟨119678, by rfl⟩ : syracuseStep 638285 = 239357) (by norm_num)
theorem B507217 : Blo 447780 507217 := bbase (se 2 (by rfl) ⟨190206, by rfl⟩ : syracuseStep 507217 = 380413) (by norm_num)
theorem B2735477 : Blo 447780 2735477 := bbase (se 5 (by rfl) ⟨128225, by rfl⟩ : syracuseStep 2735477 = 256451) (by norm_num)
theorem B507253 : Blo 447780 507253 := bbase (se 5 (by rfl) ⟨23777, by rfl⟩ : syracuseStep 507253 = 47555) (by norm_num)
theorem B540049 : Blo 447780 540049 := bbase (se 2 (by rfl) ⟨202518, by rfl⟩ : syracuseStep 540049 = 405037) (by norm_num)
theorem B507289 : Blo 447780 507289 := bbase (se 2 (by rfl) ⟨190233, by rfl⟩ : syracuseStep 507289 = 380467) (by norm_num)
theorem B507325 : Blo 447780 507325 := bbase (se 3 (by rfl) ⟨95123, by rfl⟩ : syracuseStep 507325 = 190247) (by norm_num)
theorem B507361 : Blo 447780 507361 := bbase (se 2 (by rfl) ⟨190260, by rfl⟩ : syracuseStep 507361 = 380521) (by norm_num)
theorem B507397 : Blo 447780 507397 := bbase (se 4 (by rfl) ⟨47568, by rfl⟩ : syracuseStep 507397 = 95137) (by norm_num)
theorem B507433 : Blo 447780 507433 := bbase (se 2 (by rfl) ⟨190287, by rfl⟩ : syracuseStep 507433 = 380575) (by norm_num)
theorem B605765 : Blo 447780 605765 := bbase (se 4 (by rfl) ⟨56790, by rfl⟩ : syracuseStep 605765 = 113581) (by norm_num)
theorem B507469 : Blo 447780 507469 := bbase (se 3 (by rfl) ⟨95150, by rfl⟩ : syracuseStep 507469 = 190301) (by norm_num)
theorem B1523285 : Blo 447780 1523285 := bbase (se 8 (by rfl) ⟨8925, by rfl⟩ : syracuseStep 1523285 = 17851) (by norm_num)
theorem B507505 : Blo 447780 507505 := bbase (se 2 (by rfl) ⟨190314, by rfl⟩ : syracuseStep 507505 = 380629) (by norm_num)
theorem B507541 : Blo 447780 507541 := bbase (se 6 (by rfl) ⟨11895, by rfl⟩ : syracuseStep 507541 = 23791) (by norm_num)
theorem B507577 : Blo 447780 507577 := bbase (se 2 (by rfl) ⟨190341, by rfl⟩ : syracuseStep 507577 = 380683) (by norm_num)
theorem B507613 : Blo 447780 507613 := bbase (se 3 (by rfl) ⟨95177, by rfl⟩ : syracuseStep 507613 = 190355) (by norm_num)
theorem B769765 : Blo 447780 769765 := bbase (se 4 (by rfl) ⟨72165, by rfl⟩ : syracuseStep 769765 = 144331) (by norm_num)
theorem B507649 : Blo 447780 507649 := bbase (se 2 (by rfl) ⟨190368, by rfl⟩ : syracuseStep 507649 = 380737) (by norm_num)
theorem B540437 : Blo 447780 540437 := bbase (se 6 (by rfl) ⟨12666, by rfl⟩ : syracuseStep 540437 = 25333) (by norm_num)
theorem B507685 : Blo 447780 507685 := bbase (se 4 (by rfl) ⟨47595, by rfl⟩ : syracuseStep 507685 = 95191) (by norm_num)
theorem B507721 : Blo 447780 507721 := bbase (se 2 (by rfl) ⟨190395, by rfl⟩ : syracuseStep 507721 = 380791) (by norm_num)
theorem B507757 : Blo 447780 507757 := bbase (se 3 (by rfl) ⟨95204, by rfl⟩ : syracuseStep 507757 = 190409) (by norm_num)
theorem B507793 : Blo 447780 507793 := bbase (se 2 (by rfl) ⟨190422, by rfl⟩ : syracuseStep 507793 = 380845) (by norm_num)
theorem B606133 : Blo 447780 606133 := bbase (se 5 (by rfl) ⟨28412, by rfl⟩ : syracuseStep 606133 = 56825) (by norm_num)
theorem B507829 : Blo 447780 507829 := bbase (se 5 (by rfl) ⟨23804, by rfl⟩ : syracuseStep 507829 = 47609) (by norm_num)
theorem B671693 : Blo 447780 671693 := bbase (se 3 (by rfl) ⟨125942, by rfl⟩ : syracuseStep 671693 = 251885) (by norm_num)
theorem B507865 : Blo 447780 507865 := bbase (se 2 (by rfl) ⟨190449, by rfl⟩ : syracuseStep 507865 = 380899) (by norm_num)
theorem B671717 : Blo 447780 671717 := bbase (se 4 (by rfl) ⟨62973, by rfl⟩ : syracuseStep 671717 = 125947) (by norm_num)
theorem B671741 : Blo 447780 671741 := bbase (se 3 (by rfl) ⟨125951, by rfl⟩ : syracuseStep 671741 = 251903) (by norm_num)
theorem B507901 : Blo 447780 507901 := bbase (se 3 (by rfl) ⟨95231, by rfl⟩ : syracuseStep 507901 = 190463) (by norm_num)
theorem B1523717 : Blo 447780 1523717 := bbase (se 4 (by rfl) ⟨142848, by rfl⟩ : syracuseStep 1523717 = 285697) (by norm_num)
theorem B671765 : Blo 447780 671765 := bbase (se 6 (by rfl) ⟨15744, by rfl⟩ : syracuseStep 671765 = 31489) (by norm_num)
theorem B507937 : Blo 447780 507937 := bbase (se 2 (by rfl) ⟨190476, by rfl⟩ : syracuseStep 507937 = 380953) (by norm_num)
theorem B671789 : Blo 447780 671789 := bbase (se 3 (by rfl) ⟨125960, by rfl⟩ : syracuseStep 671789 = 251921) (by norm_num)
theorem B3293237 : Blo 447780 3293237 := bbase (se 5 (by rfl) ⟨154370, by rfl⟩ : syracuseStep 3293237 = 308741) (by norm_num)
theorem B639037 : Blo 447780 639037 := bbase (se 3 (by rfl) ⟨119819, by rfl⟩ : syracuseStep 639037 = 239639) (by norm_num)
theorem B671813 : Blo 447780 671813 := bbase (se 4 (by rfl) ⟨62982, by rfl⟩ : syracuseStep 671813 = 125965) (by norm_num)
theorem B507973 : Blo 447780 507973 := bbase (se 4 (by rfl) ⟨47622, by rfl⟩ : syracuseStep 507973 = 95245) (by norm_num)
theorem B671837 : Blo 447780 671837 := bbase (se 3 (by rfl) ⟨125969, by rfl⟩ : syracuseStep 671837 = 251939) (by norm_num)
theorem B508009 : Blo 447780 508009 := bbase (se 2 (by rfl) ⟨190503, by rfl⟩ : syracuseStep 508009 = 381007) (by norm_num)
theorem B671861 : Blo 447780 671861 := bbase (se 5 (by rfl) ⟨31493, by rfl⟩ : syracuseStep 671861 = 62987) (by norm_num)
theorem B540793 : Blo 447780 540793 := bbase (se 2 (by rfl) ⟨202797, by rfl⟩ : syracuseStep 540793 = 405595) (by norm_num)
theorem B671885 : Blo 447780 671885 := bbase (se 3 (by rfl) ⟨125978, by rfl⟩ : syracuseStep 671885 = 251957) (by norm_num)
theorem B508045 : Blo 447780 508045 := bbase (se 3 (by rfl) ⟨95258, by rfl⟩ : syracuseStep 508045 = 190517) (by norm_num)
theorem B671909 : Blo 447780 671909 := bbase (se 4 (by rfl) ⟨62991, by rfl⟩ : syracuseStep 671909 = 125983) (by norm_num)
theorem B508081 : Blo 447780 508081 := bbase (se 2 (by rfl) ⟨190530, by rfl⟩ : syracuseStep 508081 = 381061) (by norm_num)
theorem B2277557 : Blo 447780 2277557 := bbase (se 5 (by rfl) ⟨106760, by rfl⟩ : syracuseStep 2277557 = 213521) (by norm_num)
theorem B671933 : Blo 447780 671933 := bbase (se 3 (by rfl) ⟨125987, by rfl⟩ : syracuseStep 671933 = 251975) (by norm_num)
theorem B671957 : Blo 447780 671957 := bbase (se 7 (by rfl) ⟨7874, by rfl⟩ : syracuseStep 671957 = 15749) (by norm_num)
theorem B508117 : Blo 447780 508117 := bbase (se 7 (by rfl) ⟨5954, by rfl⟩ : syracuseStep 508117 = 11909) (by norm_num)
theorem B671981 : Blo 447780 671981 := bbase (se 3 (by rfl) ⟨125996, by rfl⟩ : syracuseStep 671981 = 251993) (by norm_num)
theorem B508153 : Blo 447780 508153 := bbase (se 2 (by rfl) ⟨190557, by rfl⟩ : syracuseStep 508153 = 381115) (by norm_num)
theorem B672005 : Blo 447780 672005 := bbase (se 4 (by rfl) ⟨63000, by rfl⟩ : syracuseStep 672005 = 126001) (by norm_num)
theorem B672029 : Blo 447780 672029 := bbase (se 3 (by rfl) ⟨126005, by rfl⟩ : syracuseStep 672029 = 252011) (by norm_num)
theorem B508189 : Blo 447780 508189 := bbase (se 3 (by rfl) ⟨95285, by rfl⟩ : syracuseStep 508189 = 190571) (by norm_num)
theorem B672053 : Blo 447780 672053 := bbase (se 5 (by rfl) ⟨31502, by rfl⟩ : syracuseStep 672053 = 63005) (by norm_num)
theorem B508225 : Blo 447780 508225 := bbase (se 2 (by rfl) ⟨190584, by rfl⟩ : syracuseStep 508225 = 381169) (by norm_num)
theorem B1818949 : Blo 447780 1818949 := bbase (se 4 (by rfl) ⟨170526, by rfl⟩ : syracuseStep 1818949 = 341053) (by norm_num)
theorem B672077 : Blo 447780 672077 := bbase (se 3 (by rfl) ⟨126014, by rfl⟩ : syracuseStep 672077 = 252029) (by norm_num)
theorem B672101 : Blo 447780 672101 := bbase (se 4 (by rfl) ⟨63009, by rfl⟩ : syracuseStep 672101 = 126019) (by norm_num)
theorem B868709 : Blo 447780 868709 := bbase (se 4 (by rfl) ⟨81441, by rfl⟩ : syracuseStep 868709 = 162883) (by norm_num)
theorem B672125 : Blo 447780 672125 := bbase (se 3 (by rfl) ⟨126023, by rfl⟩ : syracuseStep 672125 = 252047) (by norm_num)
theorem B672149 : Blo 447780 672149 := bbase (se 6 (by rfl) ⟨15753, by rfl⟩ : syracuseStep 672149 = 31507) (by norm_num)
theorem B672173 : Blo 447780 672173 := bbase (se 3 (by rfl) ⟨126032, by rfl⟩ : syracuseStep 672173 = 252065) (by norm_num)
theorem B1524149 : Blo 447780 1524149 := bbase (se 5 (by rfl) ⟨71444, by rfl⟩ : syracuseStep 1524149 = 142889) (by norm_num)
theorem B672197 : Blo 447780 672197 := bbase (se 4 (by rfl) ⟨63018, by rfl⟩ : syracuseStep 672197 = 126037) (by norm_num)
theorem B541129 : Blo 447780 541129 := bbase (se 2 (by rfl) ⟨202923, by rfl⟩ : syracuseStep 541129 = 405847) (by norm_num)
theorem B672221 : Blo 447780 672221 := bbase (se 3 (by rfl) ⟨126041, by rfl⟩ : syracuseStep 672221 = 252083) (by norm_num)
theorem B3228149 : Blo 447780 3228149 := bbase (se 5 (by rfl) ⟨151319, by rfl⟩ : syracuseStep 3228149 = 302639) (by norm_num)
theorem B672245 : Blo 447780 672245 := bbase (se 5 (by rfl) ⟨31511, by rfl⟩ : syracuseStep 672245 = 63023) (by norm_num)
theorem B672269 : Blo 447780 672269 := bbase (se 3 (by rfl) ⟨126050, by rfl⟩ : syracuseStep 672269 = 252101) (by norm_num)
theorem B672293 : Blo 447780 672293 := bbase (se 4 (by rfl) ⟨63027, by rfl⟩ : syracuseStep 672293 = 126055) (by norm_num)
theorem B672317 : Blo 447780 672317 := bbase (se 3 (by rfl) ⟨126059, by rfl⟩ : syracuseStep 672317 = 252119) (by norm_num)
theorem B672341 : Blo 447780 672341 := bbase (se 8 (by rfl) ⟨3939, by rfl⟩ : syracuseStep 672341 = 7879) (by norm_num)
theorem B672365 : Blo 447780 672365 := bbase (se 3 (by rfl) ⟨126068, by rfl⟩ : syracuseStep 672365 = 252137) (by norm_num)
theorem B672389 : Blo 447780 672389 := bbase (se 4 (by rfl) ⟨63036, by rfl⟩ : syracuseStep 672389 = 126073) (by norm_num)
theorem B1917589 : Blo 447780 1917589 := bbase (se 6 (by rfl) ⟨44943, by rfl⟩ : syracuseStep 1917589 = 89887) (by norm_num)
theorem B672413 : Blo 447780 672413 := bbase (se 3 (by rfl) ⟨126077, by rfl⟩ : syracuseStep 672413 = 252155) (by norm_num)
theorem B672437 : Blo 447780 672437 := bbase (se 5 (by rfl) ⟨31520, by rfl⟩ : syracuseStep 672437 = 63041) (by norm_num)
theorem B672461 : Blo 447780 672461 := bbase (se 3 (by rfl) ⟨126086, by rfl⟩ : syracuseStep 672461 = 252173) (by norm_num)
theorem B672485 : Blo 447780 672485 := bbase (se 4 (by rfl) ⟨63045, by rfl⟩ : syracuseStep 672485 = 126091) (by norm_num)
theorem B672509 : Blo 447780 672509 := bbase (se 3 (by rfl) ⟨126095, by rfl⟩ : syracuseStep 672509 = 252191) (by norm_num)
theorem B672533 : Blo 447780 672533 := bbase (se 6 (by rfl) ⟨15762, by rfl⟩ : syracuseStep 672533 = 31525) (by norm_num)
theorem B672557 : Blo 447780 672557 := bbase (se 3 (by rfl) ⟨126104, by rfl⟩ : syracuseStep 672557 = 252209) (by norm_num)
theorem B672581 : Blo 447780 672581 := bbase (se 4 (by rfl) ⟨63054, by rfl⟩ : syracuseStep 672581 = 126109) (by norm_num)
theorem B639829 : Blo 447780 639829 := bbase (se 9 (by rfl) ⟨1874, by rfl⟩ : syracuseStep 639829 = 3749) (by norm_num)
theorem B672605 : Blo 447780 672605 := bbase (se 3 (by rfl) ⟨126113, by rfl⟩ : syracuseStep 672605 = 252227) (by norm_num)
theorem B1524581 : Blo 447780 1524581 := bbase (se 4 (by rfl) ⟨142929, by rfl⟩ : syracuseStep 1524581 = 285859) (by norm_num)
theorem B672629 : Blo 447780 672629 := bbase (se 5 (by rfl) ⟨31529, by rfl⟩ : syracuseStep 672629 = 63059) (by norm_num)
theorem B672653 : Blo 447780 672653 := bbase (se 3 (by rfl) ⟨126122, by rfl⟩ : syracuseStep 672653 = 252245) (by norm_num)
theorem B672677 : Blo 447780 672677 := bbase (se 4 (by rfl) ⟨63063, by rfl⟩ : syracuseStep 672677 = 126127) (by norm_num)
theorem B672701 : Blo 447780 672701 := bbase (se 3 (by rfl) ⟨126131, by rfl⟩ : syracuseStep 672701 = 252263) (by norm_num)
theorem B607181 : Blo 447780 607181 := bbase (se 3 (by rfl) ⟨113846, by rfl⟩ : syracuseStep 607181 = 227693) (by norm_num)
theorem B672725 : Blo 447780 672725 := bbase (se 7 (by rfl) ⟨7883, by rfl⟩ : syracuseStep 672725 = 15767) (by norm_num)
theorem B672749 : Blo 447780 672749 := bbase (se 3 (by rfl) ⟨126140, by rfl⟩ : syracuseStep 672749 = 252281) (by norm_num)
theorem B607213 : Blo 447780 607213 := bbase (se 3 (by rfl) ⟨113852, by rfl⟩ : syracuseStep 607213 = 227705) (by norm_num)
theorem B672773 : Blo 447780 672773 := bbase (se 4 (by rfl) ⟨63072, by rfl⟩ : syracuseStep 672773 = 126145) (by norm_num)
theorem B1295365 : Blo 447780 1295365 := bbase (se 4 (by rfl) ⟨121440, by rfl⟩ : syracuseStep 1295365 = 242881) (by norm_num)
theorem B672797 : Blo 447780 672797 := bbase (se 3 (by rfl) ⟨126149, by rfl⟩ : syracuseStep 672797 = 252299) (by norm_num)
theorem B672821 : Blo 447780 672821 := bbase (se 5 (by rfl) ⟨31538, by rfl⟩ : syracuseStep 672821 = 63077) (by norm_num)
theorem B672845 : Blo 447780 672845 := bbase (se 3 (by rfl) ⟨126158, by rfl⟩ : syracuseStep 672845 = 252317) (by norm_num)
theorem B672869 : Blo 447780 672869 := bbase (se 4 (by rfl) ⟨63081, by rfl⟩ : syracuseStep 672869 = 126163) (by norm_num)
theorem B672893 : Blo 447780 672893 := bbase (se 3 (by rfl) ⟨126167, by rfl⟩ : syracuseStep 672893 = 252335) (by norm_num)
theorem B672917 : Blo 447780 672917 := bbase (se 6 (by rfl) ⟨15771, by rfl⟩ : syracuseStep 672917 = 31543) (by norm_num)
theorem B640165 : Blo 447780 640165 := bbase (se 4 (by rfl) ⟨60015, by rfl⟩ : syracuseStep 640165 = 120031) (by norm_num)
theorem B672941 : Blo 447780 672941 := bbase (se 3 (by rfl) ⟨126176, by rfl⟩ : syracuseStep 672941 = 252353) (by norm_num)
theorem B672965 : Blo 447780 672965 := bbase (se 4 (by rfl) ⟨63090, by rfl⟩ : syracuseStep 672965 = 126181) (by norm_num)
theorem B672989 : Blo 447780 672989 := bbase (se 3 (by rfl) ⟨126185, by rfl⟩ : syracuseStep 672989 = 252371) (by norm_num)
theorem B673013 : Blo 447780 673013 := bbase (se 5 (by rfl) ⟨31547, by rfl⟩ : syracuseStep 673013 = 63095) (by norm_num)
theorem B673037 : Blo 447780 673037 := bbase (se 3 (by rfl) ⟨126194, by rfl⟩ : syracuseStep 673037 = 252389) (by norm_num)
theorem B673061 : Blo 447780 673061 := bbase (se 4 (by rfl) ⟨63099, by rfl⟩ : syracuseStep 673061 = 126199) (by norm_num)
theorem B542009 : Blo 447780 542009 := bbase (se 2 (by rfl) ⟨203253, by rfl⟩ : syracuseStep 542009 = 406507) (by norm_num)
theorem B673085 : Blo 447780 673085 := bbase (se 3 (by rfl) ⟨126203, by rfl⟩ : syracuseStep 673085 = 252407) (by norm_num)
theorem B673109 : Blo 447780 673109 := bbase (se 12 (by rfl) ⟨246, by rfl⟩ : syracuseStep 673109 = 493) (by norm_num)
theorem B673133 : Blo 447780 673133 := bbase (se 3 (by rfl) ⟨126212, by rfl⟩ : syracuseStep 673133 = 252425) (by norm_num)
theorem B640381 : Blo 447780 640381 := bbase (se 3 (by rfl) ⟨120071, by rfl⟩ : syracuseStep 640381 = 240143) (by norm_num)
theorem B673157 : Blo 447780 673157 := bbase (se 4 (by rfl) ⟨63108, by rfl⟩ : syracuseStep 673157 = 126217) (by norm_num)
theorem B771461 : Blo 447780 771461 := bbase (se 4 (by rfl) ⟨72324, by rfl⟩ : syracuseStep 771461 = 144649) (by norm_num)
theorem B673181 : Blo 447780 673181 := bbase (se 3 (by rfl) ⟨126221, by rfl⟩ : syracuseStep 673181 = 252443) (by norm_num)
theorem B673205 : Blo 447780 673205 := bbase (se 5 (by rfl) ⟨31556, by rfl⟩ : syracuseStep 673205 = 63113) (by norm_num)
theorem B2278853 : Blo 447780 2278853 := bbase (se 4 (by rfl) ⟨213642, by rfl⟩ : syracuseStep 2278853 = 427285) (by norm_num)
theorem B673229 : Blo 447780 673229 := bbase (se 3 (by rfl) ⟨126230, by rfl⟩ : syracuseStep 673229 = 252461) (by norm_num)
theorem B673253 : Blo 447780 673253 := bbase (se 4 (by rfl) ⟨63117, by rfl⟩ : syracuseStep 673253 = 126235) (by norm_num)
theorem B673277 : Blo 447780 673277 := bbase (se 3 (by rfl) ⟨126239, by rfl⟩ : syracuseStep 673277 = 252479) (by norm_num)
theorem B673301 : Blo 447780 673301 := bbase (se 6 (by rfl) ⟨15780, by rfl⟩ : syracuseStep 673301 = 31561) (by norm_num)
theorem B3425813 : Blo 447780 3425813 := bbase (se 6 (by rfl) ⟨80292, by rfl⟩ : syracuseStep 3425813 = 160585) (by norm_num)
theorem B673325 : Blo 447780 673325 := bbase (se 3 (by rfl) ⟨126248, by rfl⟩ : syracuseStep 673325 = 252497) (by norm_num)
theorem B673349 : Blo 447780 673349 := bbase (se 4 (by rfl) ⟨63126, by rfl⟩ : syracuseStep 673349 = 126253) (by norm_num)
theorem B771653 : Blo 447780 771653 := bbase (se 4 (by rfl) ⟨72342, by rfl⟩ : syracuseStep 771653 = 144685) (by norm_num)
theorem B673373 : Blo 447780 673373 := bbase (se 3 (by rfl) ⟨126257, by rfl⟩ : syracuseStep 673373 = 252515) (by norm_num)
theorem B542317 : Blo 447780 542317 := bbase (se 3 (by rfl) ⟨101684, by rfl⟩ : syracuseStep 542317 = 203369) (by norm_num)
theorem B673397 : Blo 447780 673397 := bbase (se 5 (by rfl) ⟨31565, by rfl⟩ : syracuseStep 673397 = 63131) (by norm_num)
theorem B673421 : Blo 447780 673421 := bbase (se 3 (by rfl) ⟨126266, by rfl⟩ : syracuseStep 673421 = 252533) (by norm_num)
theorem B673445 : Blo 447780 673445 := bbase (se 4 (by rfl) ⟨63135, by rfl⟩ : syracuseStep 673445 = 126271) (by norm_num)
theorem B673469 : Blo 447780 673469 := bbase (se 3 (by rfl) ⟨126275, by rfl⟩ : syracuseStep 673469 = 252551) (by norm_num)
theorem B673493 : Blo 447780 673493 := bbase (se 7 (by rfl) ⟨7892, by rfl⟩ : syracuseStep 673493 = 15785) (by norm_num)
theorem B673517 : Blo 447780 673517 := bbase (se 3 (by rfl) ⟨126284, by rfl⟩ : syracuseStep 673517 = 252569) (by norm_num)
theorem B640757 : Blo 447780 640757 := bbase (se 5 (by rfl) ⟨30035, by rfl⟩ : syracuseStep 640757 = 60071) (by norm_num)
theorem B673541 : Blo 447780 673541 := bbase (se 4 (by rfl) ⟨63144, by rfl⟩ : syracuseStep 673541 = 126289) (by norm_num)
theorem B673565 : Blo 447780 673565 := bbase (se 3 (by rfl) ⟨126293, by rfl⟩ : syracuseStep 673565 = 252587) (by norm_num)
theorem B673589 : Blo 447780 673589 := bbase (se 5 (by rfl) ⟨31574, by rfl⟩ : syracuseStep 673589 = 63149) (by norm_num)
theorem B673613 : Blo 447780 673613 := bbase (se 3 (by rfl) ⟨126302, by rfl⟩ : syracuseStep 673613 = 252605) (by norm_num)
theorem B673637 : Blo 447780 673637 := bbase (se 4 (by rfl) ⟨63153, by rfl⟩ : syracuseStep 673637 = 126307) (by norm_num)
theorem B673661 : Blo 447780 673661 := bbase (se 3 (by rfl) ⟨126311, by rfl⟩ : syracuseStep 673661 = 252623) (by norm_num)
theorem B673685 : Blo 447780 673685 := bbase (se 6 (by rfl) ⟨15789, by rfl⟩ : syracuseStep 673685 = 31579) (by norm_num)
theorem B673709 : Blo 447780 673709 := bbase (se 3 (by rfl) ⟨126320, by rfl⟩ : syracuseStep 673709 = 252641) (by norm_num)
theorem B673733 : Blo 447780 673733 := bbase (se 4 (by rfl) ⟨63162, by rfl⟩ : syracuseStep 673733 = 126325) (by norm_num)
theorem B673757 : Blo 447780 673757 := bbase (se 3 (by rfl) ⟨126329, by rfl⟩ : syracuseStep 673757 = 252659) (by norm_num)
theorem B542701 : Blo 447780 542701 := bbase (se 3 (by rfl) ⟨101756, by rfl⟩ : syracuseStep 542701 = 203513) (by norm_num)
theorem B542705 : Blo 447780 542705 := bbase (se 2 (by rfl) ⟨203514, by rfl⟩ : syracuseStep 542705 = 407029) (by norm_num)
theorem B673781 : Blo 447780 673781 := bbase (se 5 (by rfl) ⟨31583, by rfl⟩ : syracuseStep 673781 = 63167) (by norm_num)
theorem B673805 : Blo 447780 673805 := bbase (se 3 (by rfl) ⟨126338, by rfl⟩ : syracuseStep 673805 = 252677) (by norm_num)
theorem B673829 : Blo 447780 673829 := bbase (se 4 (by rfl) ⟨63171, by rfl⟩ : syracuseStep 673829 = 126343) (by norm_num)
theorem B673853 : Blo 447780 673853 := bbase (se 3 (by rfl) ⟨126347, by rfl⟩ : syracuseStep 673853 = 252695) (by norm_num)
theorem B673877 : Blo 447780 673877 := bbase (se 8 (by rfl) ⟨3948, by rfl⟩ : syracuseStep 673877 = 7897) (by norm_num)
theorem B673901 : Blo 447780 673901 := bbase (se 3 (by rfl) ⟨126356, by rfl⟩ : syracuseStep 673901 = 252713) (by norm_num)
theorem B673925 : Blo 447780 673925 := bbase (se 4 (by rfl) ⟨63180, by rfl⟩ : syracuseStep 673925 = 126361) (by norm_num)
theorem B1099909 : Blo 447780 1099909 := bbase (se 4 (by rfl) ⟨103116, by rfl⟩ : syracuseStep 1099909 = 206233) (by norm_num)
theorem B673949 : Blo 447780 673949 := bbase (se 3 (by rfl) ⟨126365, by rfl⟩ : syracuseStep 673949 = 252731) (by norm_num)
theorem B673973 : Blo 447780 673973 := bbase (se 5 (by rfl) ⟨31592, by rfl⟩ : syracuseStep 673973 = 63185) (by norm_num)
theorem B673997 : Blo 447780 673997 := bbase (se 3 (by rfl) ⟨126374, by rfl⟩ : syracuseStep 673997 = 252749) (by norm_num)
theorem B674021 : Blo 447780 674021 := bbase (se 4 (by rfl) ⟨63189, by rfl⟩ : syracuseStep 674021 = 126379) (by norm_num)
theorem B674045 : Blo 447780 674045 := bbase (se 3 (by rfl) ⟨126383, by rfl⟩ : syracuseStep 674045 = 252767) (by norm_num)
theorem B674069 : Blo 447780 674069 := bbase (se 6 (by rfl) ⟨15798, by rfl⟩ : syracuseStep 674069 = 31597) (by norm_num)
theorem B674093 : Blo 447780 674093 := bbase (se 3 (by rfl) ⟨126392, by rfl⟩ : syracuseStep 674093 = 252785) (by norm_num)
theorem B674117 : Blo 447780 674117 := bbase (se 4 (by rfl) ⟨63198, by rfl⟩ : syracuseStep 674117 = 126397) (by norm_num)
theorem B674141 : Blo 447780 674141 := bbase (se 3 (by rfl) ⟨126401, by rfl⟩ : syracuseStep 674141 = 252803) (by norm_num)
theorem B674165 : Blo 447780 674165 := bbase (se 5 (by rfl) ⟨31601, by rfl⟩ : syracuseStep 674165 = 63203) (by norm_num)
theorem B674189 : Blo 447780 674189 := bbase (se 3 (by rfl) ⟨126410, by rfl⟩ : syracuseStep 674189 = 252821) (by norm_num)
theorem B674213 : Blo 447780 674213 := bbase (se 4 (by rfl) ⟨63207, by rfl⟩ : syracuseStep 674213 = 126415) (by norm_num)
theorem B674237 : Blo 447780 674237 := bbase (se 3 (by rfl) ⟨126419, by rfl⟩ : syracuseStep 674237 = 252839) (by norm_num)
theorem B3230165 : Blo 447780 3230165 := bbase (se 7 (by rfl) ⟨37853, by rfl⟩ : syracuseStep 3230165 = 75707) (by norm_num)
theorem B674261 : Blo 447780 674261 := bbase (se 7 (by rfl) ⟨7901, by rfl⟩ : syracuseStep 674261 = 15803) (by norm_num)
theorem B674285 : Blo 447780 674285 := bbase (se 3 (by rfl) ⟨126428, by rfl⟩ : syracuseStep 674285 = 252857) (by norm_num)
theorem B674309 : Blo 447780 674309 := bbase (se 4 (by rfl) ⟨63216, by rfl⟩ : syracuseStep 674309 = 126433) (by norm_num)
theorem B674333 : Blo 447780 674333 := bbase (se 3 (by rfl) ⟨126437, by rfl⟩ : syracuseStep 674333 = 252875) (by norm_num)
theorem B674357 : Blo 447780 674357 := bbase (se 5 (by rfl) ⟨31610, by rfl⟩ : syracuseStep 674357 = 63221) (by norm_num)
theorem B674381 : Blo 447780 674381 := bbase (se 3 (by rfl) ⟨126446, by rfl⟩ : syracuseStep 674381 = 252893) (by norm_num)
theorem B674405 : Blo 447780 674405 := bbase (se 4 (by rfl) ⟨63225, by rfl⟩ : syracuseStep 674405 = 126451) (by norm_num)
theorem B674429 : Blo 447780 674429 := bbase (se 3 (by rfl) ⟨126455, by rfl⟩ : syracuseStep 674429 = 252911) (by norm_num)
theorem B674453 : Blo 447780 674453 := bbase (se 6 (by rfl) ⟨15807, by rfl⟩ : syracuseStep 674453 = 31615) (by norm_num)
theorem B674477 : Blo 447780 674477 := bbase (se 3 (by rfl) ⟨126464, by rfl⟩ : syracuseStep 674477 = 252929) (by norm_num)
theorem B674501 : Blo 447780 674501 := bbase (se 4 (by rfl) ⟨63234, by rfl⟩ : syracuseStep 674501 = 126469) (by norm_num)
theorem B2280149 : Blo 447780 2280149 := bbase (se 7 (by rfl) ⟨26720, by rfl⟩ : syracuseStep 2280149 = 53441) (by norm_num)
theorem B674525 : Blo 447780 674525 := bbase (se 3 (by rfl) ⟨126473, by rfl⟩ : syracuseStep 674525 = 252947) (by norm_num)
theorem B674549 : Blo 447780 674549 := bbase (se 5 (by rfl) ⟨31619, by rfl⟩ : syracuseStep 674549 = 63239) (by norm_num)
theorem B674573 : Blo 447780 674573 := bbase (se 3 (by rfl) ⟨126482, by rfl⟩ : syracuseStep 674573 = 252965) (by norm_num)
theorem B6146837 : Blo 447780 6146837 := bbase (se 6 (by rfl) ⟨144066, by rfl⟩ : syracuseStep 6146837 = 288133) (by norm_num)
theorem B674597 : Blo 447780 674597 := bbase (se 4 (by rfl) ⟨63243, by rfl⟩ : syracuseStep 674597 = 126487) (by norm_num)
theorem B674621 : Blo 447780 674621 := bbase (se 3 (by rfl) ⟨126491, by rfl⟩ : syracuseStep 674621 = 252983) (by norm_num)
theorem B674645 : Blo 447780 674645 := bbase (se 9 (by rfl) ⟨1976, by rfl⟩ : syracuseStep 674645 = 3953) (by norm_num)
theorem B674669 : Blo 447780 674669 := bbase (se 3 (by rfl) ⟨126500, by rfl⟩ : syracuseStep 674669 = 253001) (by norm_num)
theorem B674693 : Blo 447780 674693 := bbase (se 4 (by rfl) ⟨63252, by rfl⟩ : syracuseStep 674693 = 126505) (by norm_num)
theorem B1133453 : Blo 447780 1133453 := bbase (se 3 (by rfl) ⟨212522, by rfl⟩ : syracuseStep 1133453 = 425045) (by norm_num)
theorem B510877 : Blo 447780 510877 := bbase (se 3 (by rfl) ⟨95789, by rfl⟩ : syracuseStep 510877 = 191579) (by norm_num)
theorem B674717 : Blo 447780 674717 := bbase (se 3 (by rfl) ⟨126509, by rfl⟩ : syracuseStep 674717 = 253019) (by norm_num)
theorem B674741 : Blo 447780 674741 := bbase (se 5 (by rfl) ⟨31628, by rfl⟩ : syracuseStep 674741 = 63257) (by norm_num)
theorem B969661 : Blo 447780 969661 := bbase (se 3 (by rfl) ⟨181811, by rfl⟩ : syracuseStep 969661 = 363623) (by norm_num)
theorem B674765 : Blo 447780 674765 := bbase (se 3 (by rfl) ⟨126518, by rfl⟩ : syracuseStep 674765 = 253037) (by norm_num)
theorem B674789 : Blo 447780 674789 := bbase (se 4 (by rfl) ⟨63261, by rfl⟩ : syracuseStep 674789 = 126523) (by norm_num)
theorem B674813 : Blo 447780 674813 := bbase (se 3 (by rfl) ⟨126527, by rfl⟩ : syracuseStep 674813 = 253055) (by norm_num)
theorem B674837 : Blo 447780 674837 := bbase (se 6 (by rfl) ⟨15816, by rfl⟩ : syracuseStep 674837 = 31633) (by norm_num)
theorem B674861 : Blo 447780 674861 := bbase (se 3 (by rfl) ⟨126536, by rfl⟩ : syracuseStep 674861 = 253073) (by norm_num)
theorem B674885 : Blo 447780 674885 := bbase (se 4 (by rfl) ⟨63270, by rfl⟩ : syracuseStep 674885 = 126541) (by norm_num)
theorem B674909 : Blo 447780 674909 := bbase (se 3 (by rfl) ⟨126545, by rfl⟩ : syracuseStep 674909 = 253091) (by norm_num)
theorem B674933 : Blo 447780 674933 := bbase (se 5 (by rfl) ⟨31637, by rfl⟩ : syracuseStep 674933 = 63275) (by norm_num)
theorem B642181 : Blo 447780 642181 := bbase (se 4 (by rfl) ⟨60204, by rfl⟩ : syracuseStep 642181 = 120409) (by norm_num)
theorem B674957 : Blo 447780 674957 := bbase (se 3 (by rfl) ⟨126554, by rfl⟩ : syracuseStep 674957 = 253109) (by norm_num)
theorem B674981 : Blo 447780 674981 := bbase (se 4 (by rfl) ⟨63279, by rfl⟩ : syracuseStep 674981 = 126559) (by norm_num)
theorem B478381 : Blo 447780 478381 := bbase (se 3 (by rfl) ⟨89696, by rfl⟩ : syracuseStep 478381 = 179393) (by norm_num)
theorem B675005 : Blo 447780 675005 := bbase (se 3 (by rfl) ⟨126563, by rfl⟩ : syracuseStep 675005 = 253127) (by norm_num)
theorem B675029 : Blo 447780 675029 := bbase (se 7 (by rfl) ⟨7910, by rfl⟩ : syracuseStep 675029 = 15821) (by norm_num)
theorem B511201 : Blo 447780 511201 := bbase (se 2 (by rfl) ⟨191700, by rfl⟩ : syracuseStep 511201 = 383401) (by norm_num)
theorem B1133797 : Blo 447780 1133797 := bbase (se 4 (by rfl) ⟨106293, by rfl⟩ : syracuseStep 1133797 = 212587) (by norm_num)
theorem B675053 : Blo 447780 675053 := bbase (se 3 (by rfl) ⟨126572, by rfl⟩ : syracuseStep 675053 = 253145) (by norm_num)
theorem B675077 : Blo 447780 675077 := bbase (se 4 (by rfl) ⟨63288, by rfl⟩ : syracuseStep 675077 = 126577) (by norm_num)
theorem B675101 : Blo 447780 675101 := bbase (se 3 (by rfl) ⟨126581, by rfl⟩ : syracuseStep 675101 = 253163) (by norm_num)
theorem B478505 : Blo 447780 478505 := bbase (se 2 (by rfl) ⟨179439, by rfl⟩ : syracuseStep 478505 = 358879) (by norm_num)
theorem B1461557 : Blo 447780 1461557 := bbase (se 5 (by rfl) ⟨68510, by rfl⟩ : syracuseStep 1461557 = 137021) (by norm_num)
theorem B675125 : Blo 447780 675125 := bbase (se 5 (by rfl) ⟨31646, by rfl⟩ : syracuseStep 675125 = 63293) (by norm_num)
theorem B675149 : Blo 447780 675149 := bbase (se 3 (by rfl) ⟨126590, by rfl⟩ : syracuseStep 675149 = 253181) (by norm_num)
theorem B1133909 : Blo 447780 1133909 := bbase (se 11 (by rfl) ⟨830, by rfl⟩ : syracuseStep 1133909 = 1661) (by norm_num)
theorem B675173 : Blo 447780 675173 := bbase (se 4 (by rfl) ⟨63297, by rfl⟩ : syracuseStep 675173 = 126595) (by norm_num)
theorem B675197 : Blo 447780 675197 := bbase (se 3 (by rfl) ⟨126599, by rfl⟩ : syracuseStep 675197 = 253199) (by norm_num)
theorem B675221 : Blo 447780 675221 := bbase (se 6 (by rfl) ⟨15825, by rfl⟩ : syracuseStep 675221 = 31651) (by norm_num)
theorem B675245 : Blo 447780 675245 := bbase (se 3 (by rfl) ⟨126608, by rfl⟩ : syracuseStep 675245 = 253217) (by norm_num)
theorem B675269 : Blo 447780 675269 := bbase (se 4 (by rfl) ⟨63306, by rfl⟩ : syracuseStep 675269 = 126613) (by norm_num)
theorem B675293 : Blo 447780 675293 := bbase (se 3 (by rfl) ⟨126617, by rfl⟩ : syracuseStep 675293 = 253235) (by norm_num)
theorem B675317 : Blo 447780 675317 := bbase (se 5 (by rfl) ⟨31655, by rfl⟩ : syracuseStep 675317 = 63311) (by norm_num)
theorem B675341 : Blo 447780 675341 := bbase (se 3 (by rfl) ⟨126626, by rfl⟩ : syracuseStep 675341 = 253253) (by norm_num)
theorem B1134101 : Blo 447780 1134101 := bbase (se 6 (by rfl) ⟨26580, by rfl⟩ : syracuseStep 1134101 = 53161) (by norm_num)
theorem B478757 : Blo 447780 478757 := bbase (se 4 (by rfl) ⟨44883, by rfl⟩ : syracuseStep 478757 = 89767) (by norm_num)
theorem B675365 : Blo 447780 675365 := bbase (se 4 (by rfl) ⟨63315, by rfl⟩ : syracuseStep 675365 = 126631) (by norm_num)
theorem B675389 : Blo 447780 675389 := bbase (se 3 (by rfl) ⟨126635, by rfl⟩ : syracuseStep 675389 = 253271) (by norm_num)
theorem B1920581 : Blo 447780 1920581 := bbase (se 4 (by rfl) ⟨180054, by rfl⟩ : syracuseStep 1920581 = 360109) (by norm_num)
theorem B675413 : Blo 447780 675413 := bbase (se 8 (by rfl) ⟨3957, by rfl⟩ : syracuseStep 675413 = 7915) (by norm_num)
theorem B675437 : Blo 447780 675437 := bbase (se 3 (by rfl) ⟨126644, by rfl⟩ : syracuseStep 675437 = 253289) (by norm_num)
theorem B1298053 : Blo 447780 1298053 := bbase (se 4 (by rfl) ⟨121692, by rfl⟩ : syracuseStep 1298053 = 243385) (by norm_num)
theorem B675461 : Blo 447780 675461 := bbase (se 4 (by rfl) ⟨63324, by rfl⟩ : syracuseStep 675461 = 126649) (by norm_num)
theorem B1232533 : Blo 447780 1232533 := bbase (se 6 (by rfl) ⟨28887, by rfl⟩ : syracuseStep 1232533 = 57775) (by norm_num)
theorem B675485 : Blo 447780 675485 := bbase (se 3 (by rfl) ⟨126653, by rfl⟩ : syracuseStep 675485 = 253307) (by norm_num)
theorem B609949 : Blo 447780 609949 := bbase (se 3 (by rfl) ⟨114365, by rfl⟩ : syracuseStep 609949 = 228731) (by norm_num)
theorem B675509 : Blo 447780 675509 := bbase (se 5 (by rfl) ⟨31664, by rfl⟩ : syracuseStep 675509 = 63329) (by norm_num)
theorem B675533 : Blo 447780 675533 := bbase (se 3 (by rfl) ⟨126662, by rfl⟩ : syracuseStep 675533 = 253325) (by norm_num)
theorem B642773 : Blo 447780 642773 := bbase (se 7 (by rfl) ⟨7532, by rfl⟩ : syracuseStep 642773 = 15065) (by norm_num)
theorem B675557 : Blo 447780 675557 := bbase (se 4 (by rfl) ⟨63333, by rfl⟩ : syracuseStep 675557 = 126667) (by norm_num)
theorem B675581 : Blo 447780 675581 := bbase (se 3 (by rfl) ⟨126671, by rfl⟩ : syracuseStep 675581 = 253343) (by norm_num)
theorem B675605 : Blo 447780 675605 := bbase (se 6 (by rfl) ⟨15834, by rfl⟩ : syracuseStep 675605 = 31669) (by norm_num)
theorem B642853 : Blo 447780 642853 := bbase (se 4 (by rfl) ⟨60267, by rfl⟩ : syracuseStep 642853 = 120535) (by norm_num)
theorem B675629 : Blo 447780 675629 := bbase (se 3 (by rfl) ⟨126680, by rfl⟩ : syracuseStep 675629 = 253361) (by norm_num)
theorem B4312885 : Blo 447780 4312885 := bbase (se 5 (by rfl) ⟨202166, by rfl⟩ : syracuseStep 4312885 = 404333) (by norm_num)
theorem B1953589 : Blo 447780 1953589 := bbase (se 5 (by rfl) ⟨91574, by rfl⟩ : syracuseStep 1953589 = 183149) (by norm_num)
theorem B675653 : Blo 447780 675653 := bbase (se 4 (by rfl) ⟨63342, by rfl⟩ : syracuseStep 675653 = 126685) (by norm_num)
theorem B675677 : Blo 447780 675677 := bbase (se 3 (by rfl) ⟨126689, by rfl⟩ : syracuseStep 675677 = 253379) (by norm_num)
theorem B1560421 : Blo 447780 1560421 := bbase (se 4 (by rfl) ⟨146289, by rfl⟩ : syracuseStep 1560421 = 292579) (by norm_num)
theorem B1134445 : Blo 447780 1134445 := bbase (se 3 (by rfl) ⟨212708, by rfl⟩ : syracuseStep 1134445 = 425417) (by norm_num)
theorem B675701 : Blo 447780 675701 := bbase (se 5 (by rfl) ⟨31673, by rfl⟩ : syracuseStep 675701 = 63347) (by norm_num)
theorem B675725 : Blo 447780 675725 := bbase (se 3 (by rfl) ⟨126698, by rfl⟩ : syracuseStep 675725 = 253397) (by norm_num)
theorem B642973 : Blo 447780 642973 := bbase (se 3 (by rfl) ⟨120557, by rfl⟩ : syracuseStep 642973 = 241115) (by norm_num)
theorem B675749 : Blo 447780 675749 := bbase (se 4 (by rfl) ⟨63351, by rfl⟩ : syracuseStep 675749 = 126703) (by norm_num)
theorem B675773 : Blo 447780 675773 := bbase (se 3 (by rfl) ⟨126707, by rfl⟩ : syracuseStep 675773 = 253415) (by norm_num)
theorem B675797 : Blo 447780 675797 := bbase (se 7 (by rfl) ⟨7919, by rfl⟩ : syracuseStep 675797 = 15839) (by norm_num)
theorem B1134557 : Blo 447780 1134557 := bbase (se 3 (by rfl) ⟨212729, by rfl⟩ : syracuseStep 1134557 = 425459) (by norm_num)
theorem B479201 : Blo 447780 479201 := bbase (se 2 (by rfl) ⟨179700, by rfl⟩ : syracuseStep 479201 = 359401) (by norm_num)
theorem B2281445 : Blo 447780 2281445 := bbase (se 4 (by rfl) ⟨213885, by rfl⟩ : syracuseStep 2281445 = 427771) (by norm_num)
theorem B675821 : Blo 447780 675821 := bbase (se 3 (by rfl) ⟨126716, by rfl⟩ : syracuseStep 675821 = 253433) (by norm_num)
theorem B643069 : Blo 447780 643069 := bbase (se 3 (by rfl) ⟨120575, by rfl⟩ : syracuseStep 643069 = 241151) (by norm_num)
theorem B675845 : Blo 447780 675845 := bbase (se 4 (by rfl) ⟨63360, by rfl⟩ : syracuseStep 675845 = 126721) (by norm_num)
theorem B675869 : Blo 447780 675869 := bbase (se 3 (by rfl) ⟨126725, by rfl⟩ : syracuseStep 675869 = 253451) (by norm_num)
theorem B675893 : Blo 447780 675893 := bbase (se 5 (by rfl) ⟨31682, by rfl⟩ : syracuseStep 675893 = 63365) (by norm_num)
theorem B675917 : Blo 447780 675917 := bbase (se 3 (by rfl) ⟨126734, by rfl⟩ : syracuseStep 675917 = 253469) (by norm_num)
theorem B675941 : Blo 447780 675941 := bbase (se 4 (by rfl) ⟨63369, by rfl⟩ : syracuseStep 675941 = 126739) (by norm_num)
theorem B675965 : Blo 447780 675965 := bbase (se 3 (by rfl) ⟨126743, by rfl⟩ : syracuseStep 675965 = 253487) (by norm_num)
theorem B675989 : Blo 447780 675989 := bbase (se 6 (by rfl) ⟨15843, by rfl⟩ : syracuseStep 675989 = 31687) (by norm_num)
theorem B1134749 : Blo 447780 1134749 := bbase (se 3 (by rfl) ⟨212765, by rfl⟩ : syracuseStep 1134749 = 425531) (by norm_num)
theorem B512173 : Blo 447780 512173 := bbase (se 3 (by rfl) ⟨96032, by rfl⟩ : syracuseStep 512173 = 192065) (by norm_num)
theorem B676013 : Blo 447780 676013 := bbase (se 3 (by rfl) ⟨126752, by rfl⟩ : syracuseStep 676013 = 253505) (by norm_num)
theorem B577729 : Blo 447780 577729 := bbase (se 2 (by rfl) ⟨216648, by rfl⟩ : syracuseStep 577729 = 433297) (by norm_num)
theorem B676037 : Blo 447780 676037 := bbase (se 4 (by rfl) ⟨63378, by rfl⟩ : syracuseStep 676037 = 126757) (by norm_num)
theorem B479449 : Blo 447780 479449 := bbase (se 2 (by rfl) ⟨179793, by rfl⟩ : syracuseStep 479449 = 359587) (by norm_num)
theorem B676061 : Blo 447780 676061 := bbase (se 3 (by rfl) ⟨126761, by rfl⟩ : syracuseStep 676061 = 253523) (by norm_num)
theorem B676085 : Blo 447780 676085 := bbase (se 5 (by rfl) ⟨31691, by rfl⟩ : syracuseStep 676085 = 63383) (by norm_num)
theorem B676109 : Blo 447780 676109 := bbase (se 3 (by rfl) ⟨126770, by rfl⟩ : syracuseStep 676109 = 253541) (by norm_num)
theorem B676133 : Blo 447780 676133 := bbase (se 4 (by rfl) ⟨63387, by rfl⟩ : syracuseStep 676133 = 126775) (by norm_num)
theorem B676157 : Blo 447780 676157 := bbase (se 3 (by rfl) ⟨126779, by rfl⟩ : syracuseStep 676157 = 253559) (by norm_num)
theorem B676181 : Blo 447780 676181 := bbase (se 10 (by rfl) ⟨990, by rfl⟩ : syracuseStep 676181 = 1981) (by norm_num)
theorem B676205 : Blo 447780 676205 := bbase (se 3 (by rfl) ⟨126788, by rfl⟩ : syracuseStep 676205 = 253577) (by norm_num)
theorem B676229 : Blo 447780 676229 := bbase (se 4 (by rfl) ⟨63396, by rfl⟩ : syracuseStep 676229 = 126793) (by norm_num)
theorem B676253 : Blo 447780 676253 := bbase (se 3 (by rfl) ⟨126797, by rfl⟩ : syracuseStep 676253 = 253595) (by norm_num)
theorem B676277 : Blo 447780 676277 := bbase (se 5 (by rfl) ⟨31700, by rfl⟩ : syracuseStep 676277 = 63401) (by norm_num)
theorem B676301 : Blo 447780 676301 := bbase (se 3 (by rfl) ⟨126806, by rfl⟩ : syracuseStep 676301 = 253613) (by norm_num)
theorem B2314709 : Blo 447780 2314709 := bbase (se 7 (by rfl) ⟨27125, by rfl⟩ : syracuseStep 2314709 = 54251) (by norm_num)
theorem B676325 : Blo 447780 676325 := bbase (se 4 (by rfl) ⟨63405, by rfl⟩ : syracuseStep 676325 = 126811) (by norm_num)
theorem B1135093 : Blo 447780 1135093 := bbase (se 5 (by rfl) ⟨53207, by rfl⟩ : syracuseStep 1135093 = 106415) (by norm_num)
theorem B676349 : Blo 447780 676349 := bbase (se 3 (by rfl) ⟨126815, by rfl⟩ : syracuseStep 676349 = 253631) (by norm_num)
theorem B676373 : Blo 447780 676373 := bbase (se 6 (by rfl) ⟨15852, by rfl⟩ : syracuseStep 676373 = 31705) (by norm_num)
theorem B676397 : Blo 447780 676397 := bbase (se 3 (by rfl) ⟨126824, by rfl⟩ : syracuseStep 676397 = 253649) (by norm_num)
theorem B1921589 : Blo 447780 1921589 := bbase (se 5 (by rfl) ⟨90074, by rfl⟩ : syracuseStep 1921589 = 180149) (by norm_num)
theorem B676421 : Blo 447780 676421 := bbase (se 4 (by rfl) ⟨63414, by rfl⟩ : syracuseStep 676421 = 126829) (by norm_num)
theorem B1167949 : Blo 447780 1167949 := bbase (se 3 (by rfl) ⟨218990, by rfl⟩ : syracuseStep 1167949 = 437981) (by norm_num)
theorem B676445 : Blo 447780 676445 := bbase (se 3 (by rfl) ⟨126833, by rfl⟩ : syracuseStep 676445 = 253667) (by norm_num)
theorem B1135205 : Blo 447780 1135205 := bbase (se 4 (by rfl) ⟨106425, by rfl⟩ : syracuseStep 1135205 = 212851) (by norm_num)
theorem B676469 : Blo 447780 676469 := bbase (se 5 (by rfl) ⟨31709, by rfl⟩ : syracuseStep 676469 = 63419) (by norm_num)
theorem B676493 : Blo 447780 676493 := bbase (se 3 (by rfl) ⟨126842, by rfl⟩ : syracuseStep 676493 = 253685) (by norm_num)
theorem B479893 : Blo 447780 479893 := bbase (se 6 (by rfl) ⟨11247, by rfl⟩ : syracuseStep 479893 = 22495) (by norm_num)
theorem B676517 : Blo 447780 676517 := bbase (se 4 (by rfl) ⟨63423, by rfl⟩ : syracuseStep 676517 = 126847) (by norm_num)
theorem B676541 : Blo 447780 676541 := bbase (se 3 (by rfl) ⟨126851, by rfl⟩ : syracuseStep 676541 = 253703) (by norm_num)
theorem B545473 : Blo 447780 545473 := bbase (se 2 (by rfl) ⟨204552, by rfl⟩ : syracuseStep 545473 = 409105) (by norm_num)
theorem B479953 : Blo 447780 479953 := bbase (se 2 (by rfl) ⟨179982, by rfl⟩ : syracuseStep 479953 = 359965) (by norm_num)
theorem B676565 : Blo 447780 676565 := bbase (se 7 (by rfl) ⟨7928, by rfl⟩ : syracuseStep 676565 = 15857) (by norm_num)
theorem B676589 : Blo 447780 676589 := bbase (se 3 (by rfl) ⟨126860, by rfl⟩ : syracuseStep 676589 = 253721) (by norm_num)
theorem B676613 : Blo 447780 676613 := bbase (se 4 (by rfl) ⟨63432, by rfl⟩ : syracuseStep 676613 = 126865) (by norm_num)
theorem B676637 : Blo 447780 676637 := bbase (se 3 (by rfl) ⟨126869, by rfl⟩ : syracuseStep 676637 = 253739) (by norm_num)
theorem B1135397 : Blo 447780 1135397 := bbase (se 4 (by rfl) ⟨106443, by rfl⟩ : syracuseStep 1135397 = 212887) (by norm_num)
theorem B578345 : Blo 447780 578345 := bbase (se 2 (by rfl) ⟨216879, by rfl⟩ : syracuseStep 578345 = 433759) (by norm_num)
theorem B676661 : Blo 447780 676661 := bbase (se 5 (by rfl) ⟨31718, by rfl⟩ : syracuseStep 676661 = 63437) (by norm_num)
theorem B676685 : Blo 447780 676685 := bbase (se 3 (by rfl) ⟨126878, by rfl⟩ : syracuseStep 676685 = 253757) (by norm_num)
theorem B676709 : Blo 447780 676709 := bbase (se 4 (by rfl) ⟨63441, by rfl⟩ : syracuseStep 676709 = 126883) (by norm_num)
theorem B676733 : Blo 447780 676733 := bbase (se 3 (by rfl) ⟨126887, by rfl⟩ : syracuseStep 676733 = 253775) (by norm_num)
theorem B971669 : Blo 447780 971669 := bbase (se 6 (by rfl) ⟨22773, by rfl⟩ : syracuseStep 971669 = 45547) (by norm_num)
theorem B676757 : Blo 447780 676757 := bbase (se 6 (by rfl) ⟨15861, by rfl⟩ : syracuseStep 676757 = 31723) (by norm_num)
theorem B676781 : Blo 447780 676781 := bbase (se 3 (by rfl) ⟨126896, by rfl⟩ : syracuseStep 676781 = 253793) (by norm_num)
theorem B676805 : Blo 447780 676805 := bbase (se 4 (by rfl) ⟨63450, by rfl⟩ : syracuseStep 676805 = 126901) (by norm_num)
theorem B676829 : Blo 447780 676829 := bbase (se 3 (by rfl) ⟨126905, by rfl⟩ : syracuseStep 676829 = 253811) (by norm_num)
theorem B676853 : Blo 447780 676853 := bbase (se 5 (by rfl) ⟨31727, by rfl⟩ : syracuseStep 676853 = 63455) (by norm_num)
theorem B480269 : Blo 447780 480269 := bbase (se 3 (by rfl) ⟨90050, by rfl⟩ : syracuseStep 480269 = 180101) (by norm_num)
theorem B676877 : Blo 447780 676877 := bbase (se 3 (by rfl) ⟨126914, by rfl⟩ : syracuseStep 676877 = 253829) (by norm_num)
theorem B676901 : Blo 447780 676901 := bbase (se 4 (by rfl) ⟨63459, by rfl⟩ : syracuseStep 676901 = 126919) (by norm_num)
theorem B676925 : Blo 447780 676925 := bbase (se 3 (by rfl) ⟨126923, by rfl⟩ : syracuseStep 676925 = 253847) (by norm_num)
theorem B676949 : Blo 447780 676949 := bbase (se 8 (by rfl) ⟨3966, by rfl⟩ : syracuseStep 676949 = 7933) (by norm_num)
theorem B676973 : Blo 447780 676973 := bbase (se 3 (by rfl) ⟨126932, by rfl⟩ : syracuseStep 676973 = 253865) (by norm_num)
theorem B1135741 : Blo 447780 1135741 := bbase (se 3 (by rfl) ⟨212951, by rfl⟩ : syracuseStep 1135741 = 425903) (by norm_num)
theorem B676997 : Blo 447780 676997 := bbase (se 4 (by rfl) ⟨63468, by rfl⟩ : syracuseStep 676997 = 126937) (by norm_num)
theorem B677021 : Blo 447780 677021 := bbase (se 3 (by rfl) ⟨126941, by rfl⟩ : syracuseStep 677021 = 253883) (by norm_num)
theorem B677045 : Blo 447780 677045 := bbase (se 5 (by rfl) ⟨31736, by rfl⟩ : syracuseStep 677045 = 63473) (by norm_num)
theorem B677069 : Blo 447780 677069 := bbase (se 3 (by rfl) ⟨126950, by rfl⟩ : syracuseStep 677069 = 253901) (by norm_num)
theorem B677093 : Blo 447780 677093 := bbase (se 4 (by rfl) ⟨63477, by rfl⟩ : syracuseStep 677093 = 126955) (by norm_num)
theorem B1135853 : Blo 447780 1135853 := bbase (se 3 (by rfl) ⟨212972, by rfl⟩ : syracuseStep 1135853 = 425945) (by norm_num)
theorem B2282741 : Blo 447780 2282741 := bbase (se 5 (by rfl) ⟨107003, by rfl⟩ : syracuseStep 2282741 = 214007) (by norm_num)
theorem B677117 : Blo 447780 677117 := bbase (se 3 (by rfl) ⟨126959, by rfl⟩ : syracuseStep 677117 = 253919) (by norm_num)
theorem B677141 : Blo 447780 677141 := bbase (se 6 (by rfl) ⟨15870, by rfl⟩ : syracuseStep 677141 = 31741) (by norm_num)
theorem B677165 : Blo 447780 677165 := bbase (se 3 (by rfl) ⟨126968, by rfl⟩ : syracuseStep 677165 = 253937) (by norm_num)
theorem B677189 : Blo 447780 677189 := bbase (se 4 (by rfl) ⟨63486, by rfl⟩ : syracuseStep 677189 = 126973) (by norm_num)
theorem B808285 : Blo 447780 808285 := bbase (se 3 (by rfl) ⟨151553, by rfl⟩ : syracuseStep 808285 = 303107) (by norm_num)
theorem B677213 : Blo 447780 677213 := bbase (se 3 (by rfl) ⟨126977, by rfl⟩ : syracuseStep 677213 = 253955) (by norm_num)
theorem B677237 : Blo 447780 677237 := bbase (se 5 (by rfl) ⟨31745, by rfl⟩ : syracuseStep 677237 = 63491) (by norm_num)
theorem B677261 : Blo 447780 677261 := bbase (se 3 (by rfl) ⟨126986, by rfl⟩ : syracuseStep 677261 = 253973) (by norm_num)
theorem B677285 : Blo 447780 677285 := bbase (se 4 (by rfl) ⟨63495, by rfl⟩ : syracuseStep 677285 = 126991) (by norm_num)
theorem B1136045 : Blo 447780 1136045 := bbase (se 3 (by rfl) ⟨213008, by rfl⟩ : syracuseStep 1136045 = 426017) (by norm_num)
theorem B677309 : Blo 447780 677309 := bbase (se 3 (by rfl) ⟨126995, by rfl⟩ : syracuseStep 677309 = 253991) (by norm_num)
theorem B480713 : Blo 447780 480713 := bbase (se 2 (by rfl) ⟨180267, by rfl⟩ : syracuseStep 480713 = 360535) (by norm_num)
theorem B677333 : Blo 447780 677333 := bbase (se 7 (by rfl) ⟨7937, by rfl⟩ : syracuseStep 677333 = 15875) (by norm_num)
theorem B677357 : Blo 447780 677357 := bbase (se 3 (by rfl) ⟨127004, by rfl⟩ : syracuseStep 677357 = 254009) (by norm_num)
theorem B480773 : Blo 447780 480773 := bbase (se 4 (by rfl) ⟨45072, by rfl⟩ : syracuseStep 480773 = 90145) (by norm_num)
theorem B677381 : Blo 447780 677381 := bbase (se 4 (by rfl) ⟨63504, by rfl⟩ : syracuseStep 677381 = 127009) (by norm_num)
theorem B677405 : Blo 447780 677405 := bbase (se 3 (by rfl) ⟨127013, by rfl⟩ : syracuseStep 677405 = 254027) (by norm_num)
theorem B677429 : Blo 447780 677429 := bbase (se 5 (by rfl) ⟨31754, by rfl⟩ : syracuseStep 677429 = 63509) (by norm_num)
theorem B677453 : Blo 447780 677453 := bbase (se 3 (by rfl) ⟨127022, by rfl⟩ : syracuseStep 677453 = 254045) (by norm_num)
theorem B677477 : Blo 447780 677477 := bbase (se 4 (by rfl) ⟨63513, by rfl⟩ : syracuseStep 677477 = 127027) (by norm_num)
theorem B677501 : Blo 447780 677501 := bbase (se 3 (by rfl) ⟨127031, by rfl⟩ : syracuseStep 677501 = 254063) (by norm_num)
theorem B480901 : Blo 447780 480901 := bbase (se 4 (by rfl) ⟨45084, by rfl⟩ : syracuseStep 480901 = 90169) (by norm_num)
theorem B677525 : Blo 447780 677525 := bbase (se 6 (by rfl) ⟨15879, by rfl⟩ : syracuseStep 677525 = 31759) (by norm_num)
theorem B677549 : Blo 447780 677549 := bbase (se 3 (by rfl) ⟨127040, by rfl⟩ : syracuseStep 677549 = 254081) (by norm_num)
theorem B677573 : Blo 447780 677573 := bbase (se 4 (by rfl) ⟨63522, by rfl⟩ : syracuseStep 677573 = 127045) (by norm_num)
theorem B677597 : Blo 447780 677597 := bbase (se 3 (by rfl) ⟨127049, by rfl⟩ : syracuseStep 677597 = 254099) (by norm_num)
theorem B677621 : Blo 447780 677621 := bbase (se 5 (by rfl) ⟨31763, by rfl⟩ : syracuseStep 677621 = 63527) (by norm_num)
theorem B513793 : Blo 447780 513793 := bbase (se 2 (by rfl) ⟨192672, by rfl⟩ : syracuseStep 513793 = 385345) (by norm_num)
theorem B1136389 : Blo 447780 1136389 := bbase (se 4 (by rfl) ⟨106536, by rfl⟩ : syracuseStep 1136389 = 213073) (by norm_num)
theorem B677645 : Blo 447780 677645 := bbase (se 3 (by rfl) ⟨127058, by rfl⟩ : syracuseStep 677645 = 254117) (by norm_num)
theorem B677669 : Blo 447780 677669 := bbase (se 4 (by rfl) ⟨63531, by rfl⟩ : syracuseStep 677669 = 127063) (by norm_num)
theorem B1136501 : Blo 447780 1136501 := bbase (se 5 (by rfl) ⟨53273, by rfl⟩ : syracuseStep 1136501 = 106547) (by norm_num)
theorem B1136693 : Blo 447780 1136693 := bbase (se 5 (by rfl) ⟨53282, by rfl⟩ : syracuseStep 1136693 = 106565) (by norm_num)
theorem B481345 : Blo 447780 481345 := bbase (se 2 (by rfl) ⟨180504, by rfl⟩ : syracuseStep 481345 = 361009) (by norm_num)
theorem B1824869 : Blo 447780 1824869 := bbase (se 4 (by rfl) ⟨171081, by rfl⟩ : syracuseStep 1824869 = 342163) (by norm_num)
theorem B481465 : Blo 447780 481465 := bbase (se 2 (by rfl) ⟨180549, by rfl⟩ : syracuseStep 481465 = 361099) (by norm_num)
theorem B1923365 : Blo 447780 1923365 := bbase (se 4 (by rfl) ⟨180315, by rfl⟩ : syracuseStep 1923365 = 360631) (by norm_num)
theorem B1137037 : Blo 447780 1137037 := bbase (se 3 (by rfl) ⟨213194, by rfl⟩ : syracuseStep 1137037 = 426389) (by norm_num)
theorem B481717 : Blo 447780 481717 := bbase (se 5 (by rfl) ⟨22580, by rfl⟩ : syracuseStep 481717 = 45161) (by norm_num)
theorem B481721 : Blo 447780 481721 := bbase (se 2 (by rfl) ⟨180645, by rfl⟩ : syracuseStep 481721 = 361291) (by norm_num)
theorem B1137149 : Blo 447780 1137149 := bbase (se 3 (by rfl) ⟨213215, by rfl⟩ : syracuseStep 1137149 = 426431) (by norm_num)
theorem B2284037 : Blo 447780 2284037 := bbase (se 4 (by rfl) ⟨214128, by rfl⟩ : syracuseStep 2284037 = 428257) (by norm_num)
theorem B907853 : Blo 447780 907853 := bbase (se 3 (by rfl) ⟨170222, by rfl⟩ : syracuseStep 907853 = 340445) (by norm_num)
theorem B514669 : Blo 447780 514669 := bbase (se 3 (by rfl) ⟨96500, by rfl⟩ : syracuseStep 514669 = 193001) (by norm_num)
theorem B1137341 : Blo 447780 1137341 := bbase (se 3 (by rfl) ⟨213251, by rfl⟩ : syracuseStep 1137341 = 426503) (by norm_num)
theorem B482285 : Blo 447780 482285 := bbase (se 3 (by rfl) ⟨90428, by rfl⟩ : syracuseStep 482285 = 180857) (by norm_num)
theorem B4676597 : Blo 447780 4676597 := bbase (se 5 (by rfl) ⟨219215, by rfl⟩ : syracuseStep 4676597 = 438431) (by norm_num)
theorem B1137685 : Blo 447780 1137685 := bbase (se 6 (by rfl) ⟨26664, by rfl⟩ : syracuseStep 1137685 = 53329) (by norm_num)
theorem B1137797 : Blo 447780 1137797 := bbase (se 4 (by rfl) ⟨106668, by rfl⟩ : syracuseStep 1137797 = 213337) (by norm_num)
theorem B908437 : Blo 447780 908437 := bbase (se 6 (by rfl) ⟨21291, by rfl⟩ : syracuseStep 908437 = 42583) (by norm_num)
theorem B973973 : Blo 447780 973973 := bbase (se 6 (by rfl) ⟨22827, by rfl⟩ : syracuseStep 973973 = 45655) (by norm_num)
theorem B1137989 : Blo 447780 1137989 := bbase (se 4 (by rfl) ⟨106686, by rfl⟩ : syracuseStep 1137989 = 213373) (by norm_num)
theorem B1564085 : Blo 447780 1564085 := bbase (se 5 (by rfl) ⟨73316, by rfl⟩ : syracuseStep 1564085 = 146633) (by norm_num)
theorem B2252405 : Blo 447780 2252405 := bbase (se 5 (by rfl) ⟨105581, by rfl⟩ : syracuseStep 2252405 = 211163) (by norm_num)
theorem B5758613 : Blo 447780 5758613 := bbase (se 6 (by rfl) ⟨134967, by rfl⟩ : syracuseStep 5758613 = 269935) (by norm_num)
theorem B1138333 : Blo 447780 1138333 := bbase (se 3 (by rfl) ⟨213437, by rfl⟩ : syracuseStep 1138333 = 426875) (by norm_num)
theorem B1138445 : Blo 447780 1138445 := bbase (se 3 (by rfl) ⟨213458, by rfl⟩ : syracuseStep 1138445 = 426917) (by norm_num)
theorem B2285333 : Blo 447780 2285333 := bbase (se 6 (by rfl) ⟨53562, by rfl⟩ : syracuseStep 2285333 = 107125) (by norm_num)
theorem B1007549 : Blo 447780 1007549 := bbase (se 3 (by rfl) ⟨188915, by rfl⟩ : syracuseStep 1007549 = 377831) (by norm_num)
theorem B1138637 : Blo 447780 1138637 := bbase (se 3 (by rfl) ⟨213494, by rfl⟩ : syracuseStep 1138637 = 426989) (by norm_num)
theorem B810973 : Blo 447780 810973 := bbase (se 3 (by rfl) ⟨152057, by rfl⟩ : syracuseStep 810973 = 304115) (by norm_num)
theorem B1007621 : Blo 447780 1007621 := bbase (se 4 (by rfl) ⟨94464, by rfl⟩ : syracuseStep 1007621 = 188929) (by norm_num)
theorem B1007693 : Blo 447780 1007693 := bbase (se 3 (by rfl) ⟨188942, by rfl⟩ : syracuseStep 1007693 = 377885) (by norm_num)
theorem B1007765 : Blo 447780 1007765 := bbase (se 6 (by rfl) ⟨23619, by rfl⟩ : syracuseStep 1007765 = 47239) (by norm_num)
theorem B647317 : Blo 447780 647317 := bbase (se 6 (by rfl) ⟨15171, by rfl⟩ : syracuseStep 647317 = 30343) (by norm_num)
theorem B5136533 : Blo 447780 5136533 := bbase (se 6 (by rfl) ⟨120387, by rfl⟩ : syracuseStep 5136533 = 240775) (by norm_num)
theorem B1007837 : Blo 447780 1007837 := bbase (se 3 (by rfl) ⟨188969, by rfl⟩ : syracuseStep 1007837 = 377939) (by norm_num)
theorem B7266581 : Blo 447780 7266581 := bbase (se 6 (by rfl) ⟨170310, by rfl⟩ : syracuseStep 7266581 = 340621) (by norm_num)
theorem B1007909 : Blo 447780 1007909 := bbase (se 4 (by rfl) ⟨94491, by rfl⟩ : syracuseStep 1007909 = 188983) (by norm_num)
theorem B909605 : Blo 447780 909605 := bbase (se 4 (by rfl) ⟨85275, by rfl⟩ : syracuseStep 909605 = 170551) (by norm_num)
theorem B1138981 : Blo 447780 1138981 := bbase (se 4 (by rfl) ⟨106779, by rfl⟩ : syracuseStep 1138981 = 213559) (by norm_num)
theorem B1007981 : Blo 447780 1007981 := bbase (se 3 (by rfl) ⟨188996, by rfl⟩ : syracuseStep 1007981 = 377993) (by norm_num)
theorem B2154869 : Blo 447780 2154869 := bbase (se 5 (by rfl) ⟨101009, by rfl⟩ : syracuseStep 2154869 = 202019) (by norm_num)
theorem B1139093 : Blo 447780 1139093 := bbase (se 6 (by rfl) ⟨26697, by rfl⟩ : syracuseStep 1139093 = 53395) (by norm_num)
theorem B1008053 : Blo 447780 1008053 := bbase (se 5 (by rfl) ⟨47252, by rfl⟩ : syracuseStep 1008053 = 94505) (by norm_num)
theorem B1008125 : Blo 447780 1008125 := bbase (se 3 (by rfl) ⟨189023, by rfl⟩ : syracuseStep 1008125 = 378047) (by norm_num)
theorem B1008197 : Blo 447780 1008197 := bbase (se 4 (by rfl) ⟨94518, by rfl⟩ : syracuseStep 1008197 = 189037) (by norm_num)
theorem B1139285 : Blo 447780 1139285 := bbase (se 8 (by rfl) ⟨6675, by rfl⟩ : syracuseStep 1139285 = 13351) (by norm_num)
theorem B1008269 : Blo 447780 1008269 := bbase (se 3 (by rfl) ⟨189050, by rfl⟩ : syracuseStep 1008269 = 378101) (by norm_num)
theorem B615061 : Blo 447780 615061 := bbase (se 6 (by rfl) ⟨14415, by rfl⟩ : syracuseStep 615061 = 28831) (by norm_num)
theorem B1008341 : Blo 447780 1008341 := bbase (se 7 (by rfl) ⟨11816, by rfl⟩ : syracuseStep 1008341 = 23633) (by norm_num)
theorem B1008413 : Blo 447780 1008413 := bbase (se 3 (by rfl) ⟨189077, by rfl⟩ : syracuseStep 1008413 = 378155) (by norm_num)
theorem B1008485 : Blo 447780 1008485 := bbase (se 4 (by rfl) ⟨94545, by rfl⟩ : syracuseStep 1008485 = 189091) (by norm_num)
theorem B615325 : Blo 447780 615325 := bbase (se 3 (by rfl) ⟨115373, by rfl⟩ : syracuseStep 615325 = 230747) (by norm_num)
theorem B1008557 : Blo 447780 1008557 := bbase (se 3 (by rfl) ⟨189104, by rfl⟩ : syracuseStep 1008557 = 378209) (by norm_num)
theorem B1139629 : Blo 447780 1139629 := bbase (se 3 (by rfl) ⟨213680, by rfl⟩ : syracuseStep 1139629 = 427361) (by norm_num)
theorem B1008629 : Blo 447780 1008629 := bbase (se 5 (by rfl) ⟨47279, by rfl⟩ : syracuseStep 1008629 = 94559) (by norm_num)
theorem B1139741 : Blo 447780 1139741 := bbase (se 3 (by rfl) ⟨213701, by rfl⟩ : syracuseStep 1139741 = 427403) (by norm_num)
theorem B2286629 : Blo 447780 2286629 := bbase (se 4 (by rfl) ⟨214371, by rfl⟩ : syracuseStep 2286629 = 428743) (by norm_num)
theorem B1008701 : Blo 447780 1008701 := bbase (se 3 (by rfl) ⟨189131, by rfl⟩ : syracuseStep 1008701 = 378263) (by norm_num)
theorem B1008773 : Blo 447780 1008773 := bbase (se 4 (by rfl) ⟨94572, by rfl⟩ : syracuseStep 1008773 = 189145) (by norm_num)
theorem B8316053 : Blo 447780 8316053 := bbase (se 6 (by rfl) ⟨194907, by rfl⟩ : syracuseStep 8316053 = 389815) (by norm_num)
theorem B2057413 : Blo 447780 2057413 := bbase (se 4 (by rfl) ⟨192882, by rfl⟩ : syracuseStep 2057413 = 385765) (by norm_num)
theorem B1008845 : Blo 447780 1008845 := bbase (se 3 (by rfl) ⟨189158, by rfl⟩ : syracuseStep 1008845 = 378317) (by norm_num)
theorem B1139933 : Blo 447780 1139933 := bbase (se 3 (by rfl) ⟨213737, by rfl⟩ : syracuseStep 1139933 = 427475) (by norm_num)
theorem B1008917 : Blo 447780 1008917 := bbase (se 6 (by rfl) ⟨23646, by rfl⟩ : syracuseStep 1008917 = 47293) (by norm_num)
theorem B812357 : Blo 447780 812357 := bbase (se 4 (by rfl) ⟨76158, by rfl⟩ : syracuseStep 812357 = 152317) (by norm_num)
theorem B1008989 : Blo 447780 1008989 := bbase (se 3 (by rfl) ⟨189185, by rfl⟩ : syracuseStep 1008989 = 378371) (by norm_num)
theorem B1009061 : Blo 447780 1009061 := bbase (se 4 (by rfl) ⟨94599, by rfl⟩ : syracuseStep 1009061 = 189199) (by norm_num)
theorem B1369541 : Blo 447780 1369541 := bbase (se 4 (by rfl) ⟨128394, by rfl⟩ : syracuseStep 1369541 = 256789) (by norm_num)
theorem B1009133 : Blo 447780 1009133 := bbase (se 3 (by rfl) ⟨189212, by rfl⟩ : syracuseStep 1009133 = 378425) (by norm_num)
theorem B910877 : Blo 447780 910877 := bbase (se 3 (by rfl) ⟨170789, by rfl⟩ : syracuseStep 910877 = 341579) (by norm_num)
theorem B1009205 : Blo 447780 1009205 := bbase (se 5 (by rfl) ⟨47306, by rfl⟩ : syracuseStep 1009205 = 94613) (by norm_num)
theorem B1140277 : Blo 447780 1140277 := bbase (se 5 (by rfl) ⟨53450, by rfl⟩ : syracuseStep 1140277 = 106901) (by norm_num)
theorem B1009277 : Blo 447780 1009277 := bbase (se 3 (by rfl) ⟨189239, by rfl⟩ : syracuseStep 1009277 = 378479) (by norm_num)
theorem B1140389 : Blo 447780 1140389 := bbase (se 4 (by rfl) ⟨106911, by rfl⟩ : syracuseStep 1140389 = 213823) (by norm_num)
theorem B1009349 : Blo 447780 1009349 := bbase (se 4 (by rfl) ⟨94626, by rfl⟩ : syracuseStep 1009349 = 189253) (by norm_num)
theorem B1009421 : Blo 447780 1009421 := bbase (se 3 (by rfl) ⟨189266, by rfl⟩ : syracuseStep 1009421 = 378533) (by norm_num)
theorem B1009493 : Blo 447780 1009493 := bbase (se 9 (by rfl) ⟨2957, by rfl⟩ : syracuseStep 1009493 = 5915) (by norm_num)
theorem B1140581 : Blo 447780 1140581 := bbase (se 4 (by rfl) ⟨106929, by rfl⟩ : syracuseStep 1140581 = 213859) (by norm_num)
theorem B3073909 : Blo 447780 3073909 := bbase (se 5 (by rfl) ⟨144089, by rfl⟩ : syracuseStep 3073909 = 288179) (by norm_num)
theorem B1009565 : Blo 447780 1009565 := bbase (se 3 (by rfl) ⟨189293, by rfl⟩ : syracuseStep 1009565 = 378587) (by norm_num)
theorem B4319189 : Blo 447780 4319189 := bbase (se 7 (by rfl) ⟨50615, by rfl⟩ : syracuseStep 4319189 = 101231) (by norm_num)
theorem B1009637 : Blo 447780 1009637 := bbase (se 4 (by rfl) ⟨94653, by rfl⟩ : syracuseStep 1009637 = 189307) (by norm_num)
theorem B1009709 : Blo 447780 1009709 := bbase (se 3 (by rfl) ⟨189320, by rfl⟩ : syracuseStep 1009709 = 378641) (by norm_num)
theorem B911405 : Blo 447780 911405 := bbase (se 3 (by rfl) ⟨170888, by rfl⟩ : syracuseStep 911405 = 341777) (by norm_num)
theorem B1009781 : Blo 447780 1009781 := bbase (se 5 (by rfl) ⟨47333, by rfl⟩ : syracuseStep 1009781 = 94667) (by norm_num)
theorem B649397 : Blo 447780 649397 := bbase (se 5 (by rfl) ⟨30440, by rfl⟩ : syracuseStep 649397 = 60881) (by norm_num)
theorem B1009853 : Blo 447780 1009853 := bbase (se 3 (by rfl) ⟨189347, by rfl⟩ : syracuseStep 1009853 = 378695) (by norm_num)
theorem B1140925 : Blo 447780 1140925 := bbase (se 3 (by rfl) ⟨213923, by rfl⟩ : syracuseStep 1140925 = 427847) (by norm_num)
theorem B1894661 : Blo 447780 1894661 := bbase (se 4 (by rfl) ⟨177624, by rfl⟩ : syracuseStep 1894661 = 355249) (by norm_num)
theorem B1009925 : Blo 447780 1009925 := bbase (se 4 (by rfl) ⟨94680, by rfl⟩ : syracuseStep 1009925 = 189361) (by norm_num)
theorem B1141037 : Blo 447780 1141037 := bbase (se 3 (by rfl) ⟨213944, by rfl⟩ : syracuseStep 1141037 = 427889) (by norm_num)
theorem B1009997 : Blo 447780 1009997 := bbase (se 3 (by rfl) ⟨189374, by rfl⟩ : syracuseStep 1009997 = 378749) (by norm_num)
theorem B4811093 : Blo 447780 4811093 := bbase (se 10 (by rfl) ⟨7047, by rfl⟩ : syracuseStep 4811093 = 14095) (by norm_num)
theorem B616837 : Blo 447780 616837 := bbase (se 4 (by rfl) ⟨57828, by rfl⟩ : syracuseStep 616837 = 115657) (by norm_num)
theorem B1010069 : Blo 447780 1010069 := bbase (se 6 (by rfl) ⟨23673, by rfl⟩ : syracuseStep 1010069 = 47347) (by norm_num)
theorem B1927637 : Blo 447780 1927637 := bbase (se 7 (by rfl) ⟨22589, by rfl⟩ : syracuseStep 1927637 = 45179) (by norm_num)
theorem B1010141 : Blo 447780 1010141 := bbase (se 3 (by rfl) ⟨189401, by rfl⟩ : syracuseStep 1010141 = 378803) (by norm_num)
theorem B1141229 : Blo 447780 1141229 := bbase (se 3 (by rfl) ⟨213980, by rfl⟩ : syracuseStep 1141229 = 427961) (by norm_num)
theorem B1010213 : Blo 447780 1010213 := bbase (se 4 (by rfl) ⟨94707, by rfl⟩ : syracuseStep 1010213 = 189415) (by norm_num)
theorem B1010285 : Blo 447780 1010285 := bbase (se 3 (by rfl) ⟨189428, by rfl⟩ : syracuseStep 1010285 = 378857) (by norm_num)
theorem B1010357 : Blo 447780 1010357 := bbase (se 5 (by rfl) ⟨47360, by rfl⟩ : syracuseStep 1010357 = 94721) (by norm_num)
theorem B3402485 : Blo 447780 3402485 := bbase (se 5 (by rfl) ⟨159491, by rfl⟩ : syracuseStep 3402485 = 318983) (by norm_num)
theorem B1010429 : Blo 447780 1010429 := bbase (se 3 (by rfl) ⟨189455, by rfl⟩ : syracuseStep 1010429 = 378911) (by norm_num)
theorem B2878229 : Blo 447780 2878229 := bbase (se 6 (by rfl) ⟨67458, by rfl⟩ : syracuseStep 2878229 = 134917) (by norm_num)
theorem B1010501 : Blo 447780 1010501 := bbase (se 4 (by rfl) ⟨94734, by rfl⟩ : syracuseStep 1010501 = 189469) (by norm_num)
theorem B1141573 : Blo 447780 1141573 := bbase (se 4 (by rfl) ⟨107022, by rfl⟩ : syracuseStep 1141573 = 214045) (by norm_num)
theorem B813901 : Blo 447780 813901 := bbase (se 3 (by rfl) ⟨152606, by rfl⟩ : syracuseStep 813901 = 305213) (by norm_num)
theorem B1010573 : Blo 447780 1010573 := bbase (se 3 (by rfl) ⟨189482, by rfl⟩ : syracuseStep 1010573 = 378965) (by norm_num)
theorem B1141685 : Blo 447780 1141685 := bbase (se 5 (by rfl) ⟨53516, by rfl⟩ : syracuseStep 1141685 = 107033) (by norm_num)
theorem B1010645 : Blo 447780 1010645 := bbase (se 7 (by rfl) ⟨11843, by rfl⟩ : syracuseStep 1010645 = 23687) (by norm_num)
theorem B1010717 : Blo 447780 1010717 := bbase (se 3 (by rfl) ⟨189509, by rfl⟩ : syracuseStep 1010717 = 379019) (by norm_num)
theorem B1010789 : Blo 447780 1010789 := bbase (se 4 (by rfl) ⟨94761, by rfl⟩ : syracuseStep 1010789 = 189523) (by norm_num)
theorem B1141877 : Blo 447780 1141877 := bbase (se 5 (by rfl) ⟨53525, by rfl⟩ : syracuseStep 1141877 = 107051) (by norm_num)
theorem B1010861 : Blo 447780 1010861 := bbase (se 3 (by rfl) ⟨189536, by rfl⟩ : syracuseStep 1010861 = 379073) (by norm_num)
theorem B1010933 : Blo 447780 1010933 := bbase (se 5 (by rfl) ⟨47387, by rfl⟩ : syracuseStep 1010933 = 94775) (by norm_num)
theorem B1011005 : Blo 447780 1011005 := bbase (se 3 (by rfl) ⟨189563, by rfl⟩ : syracuseStep 1011005 = 379127) (by norm_num)
theorem B1011077 : Blo 447780 1011077 := bbase (se 4 (by rfl) ⟨94788, by rfl⟩ : syracuseStep 1011077 = 189577) (by norm_num)
theorem B1011149 : Blo 447780 1011149 := bbase (se 3 (by rfl) ⟨189590, by rfl⟩ : syracuseStep 1011149 = 379181) (by norm_num)
theorem B1142221 : Blo 447780 1142221 := bbase (se 3 (by rfl) ⟨214166, by rfl⟩ : syracuseStep 1142221 = 428333) (by norm_num)
theorem B1011221 : Blo 447780 1011221 := bbase (se 6 (by rfl) ⟨23700, by rfl⟩ : syracuseStep 1011221 = 47401) (by norm_num)
theorem B3829301 : Blo 447780 3829301 := bbase (se 5 (by rfl) ⟨179498, by rfl⟩ : syracuseStep 3829301 = 358997) (by norm_num)
theorem B1142333 : Blo 447780 1142333 := bbase (se 3 (by rfl) ⟨214187, by rfl⟩ : syracuseStep 1142333 = 428375) (by norm_num)
theorem B1437269 : Blo 447780 1437269 := bbase (se 8 (by rfl) ⟨8421, by rfl⟩ : syracuseStep 1437269 = 16843) (by norm_num)
theorem B1011293 : Blo 447780 1011293 := bbase (se 3 (by rfl) ⟨189617, by rfl⟩ : syracuseStep 1011293 = 379235) (by norm_num)
theorem B1011365 : Blo 447780 1011365 := bbase (se 4 (by rfl) ⟨94815, by rfl⟩ : syracuseStep 1011365 = 189631) (by norm_num)
theorem B585449 : Blo 447780 585449 := bbase (se 2 (by rfl) ⟨219543, by rfl⟩ : syracuseStep 585449 = 439087) (by norm_num)
theorem B1011437 : Blo 447780 1011437 := bbase (se 3 (by rfl) ⟨189644, by rfl⟩ : syracuseStep 1011437 = 379289) (by norm_num)
theorem B1142525 : Blo 447780 1142525 := bbase (se 3 (by rfl) ⟨214223, by rfl⟩ : syracuseStep 1142525 = 428447) (by norm_num)
theorem B683797 : Blo 447780 683797 := bbase (se 6 (by rfl) ⟨16026, by rfl⟩ : syracuseStep 683797 = 32053) (by norm_num)
theorem B1011509 : Blo 447780 1011509 := bbase (se 5 (by rfl) ⟨47414, by rfl⟩ : syracuseStep 1011509 = 94829) (by norm_num)
theorem B1011581 : Blo 447780 1011581 := bbase (se 3 (by rfl) ⟨189671, by rfl⟩ : syracuseStep 1011581 = 379343) (by norm_num)
theorem B913285 : Blo 447780 913285 := bbase (se 4 (by rfl) ⟨85620, by rfl⟩ : syracuseStep 913285 = 171241) (by norm_num)
theorem B2158501 : Blo 447780 2158501 := bbase (se 4 (by rfl) ⟨202359, by rfl⟩ : syracuseStep 2158501 = 404719) (by norm_num)
theorem B1011653 : Blo 447780 1011653 := bbase (se 4 (by rfl) ⟨94842, by rfl⟩ : syracuseStep 1011653 = 189685) (by norm_num)
theorem B1830853 : Blo 447780 1830853 := bbase (se 4 (by rfl) ⟨171642, by rfl⟩ : syracuseStep 1830853 = 343285) (by norm_num)
theorem B3502037 : Blo 447780 3502037 := bbase (se 7 (by rfl) ⟨41039, by rfl⟩ : syracuseStep 3502037 = 82079) (by norm_num)
theorem B1011725 : Blo 447780 1011725 := bbase (se 3 (by rfl) ⟨189698, by rfl⟩ : syracuseStep 1011725 = 379397) (by norm_num)
theorem B454681 : Blo 447780 454681 := bbase (se 2 (by rfl) ⟨170505, by rfl⟩ : syracuseStep 454681 = 341011) (by norm_num)
theorem B1011797 : Blo 447780 1011797 := bbase (se 8 (by rfl) ⟨5928, by rfl⟩ : syracuseStep 1011797 = 11857) (by norm_num)
theorem B1142869 : Blo 447780 1142869 := bbase (se 8 (by rfl) ⟨6696, by rfl⟩ : syracuseStep 1142869 = 13393) (by norm_num)
theorem B1011869 : Blo 447780 1011869 := bbase (se 3 (by rfl) ⟨189725, by rfl⟩ : syracuseStep 1011869 = 379451) (by norm_num)
theorem B1142981 : Blo 447780 1142981 := bbase (se 4 (by rfl) ⟨107154, by rfl⟩ : syracuseStep 1142981 = 214309) (by norm_num)
theorem B1929413 : Blo 447780 1929413 := bbase (se 4 (by rfl) ⟨180882, by rfl⟩ : syracuseStep 1929413 = 361765) (by norm_num)
theorem B1011941 : Blo 447780 1011941 := bbase (se 4 (by rfl) ⟨94869, by rfl⟩ : syracuseStep 1011941 = 189739) (by norm_num)
theorem B487705 : Blo 447780 487705 := bbase (se 2 (by rfl) ⟨182889, by rfl⟩ : syracuseStep 487705 = 365779) (by norm_num)
theorem B1012013 : Blo 447780 1012013 := bbase (se 3 (by rfl) ⟨189752, by rfl⟩ : syracuseStep 1012013 = 379505) (by norm_num)
theorem B782669 : Blo 447780 782669 := bbase (se 3 (by rfl) ⟨146750, by rfl⟩ : syracuseStep 782669 = 293501) (by norm_num)
theorem B454997 : Blo 447780 454997 := bbase (se 10 (by rfl) ⟨666, by rfl⟩ : syracuseStep 454997 = 1333) (by norm_num)
theorem B1012085 : Blo 447780 1012085 := bbase (se 5 (by rfl) ⟨47441, by rfl⟩ : syracuseStep 1012085 = 94883) (by norm_num)
theorem B487805 : Blo 447780 487805 := bbase (se 3 (by rfl) ⟨91463, by rfl⟩ : syracuseStep 487805 = 182927) (by norm_num)
theorem B1077637 : Blo 447780 1077637 := bbase (se 4 (by rfl) ⟨101028, by rfl⟩ : syracuseStep 1077637 = 202057) (by norm_num)
theorem B1143173 : Blo 447780 1143173 := bbase (se 4 (by rfl) ⟨107172, by rfl⟩ : syracuseStep 1143173 = 214345) (by norm_num)
theorem B1929653 : Blo 447780 1929653 := bbase (se 5 (by rfl) ⟨90452, by rfl⟩ : syracuseStep 1929653 = 180905) (by norm_num)
theorem B1012157 : Blo 447780 1012157 := bbase (se 3 (by rfl) ⟨189779, by rfl⟩ : syracuseStep 1012157 = 379559) (by norm_num)
theorem B717277 : Blo 447780 717277 := bbase (se 3 (by rfl) ⟨134489, by rfl⟩ : syracuseStep 717277 = 268979) (by norm_num)
theorem B1438181 : Blo 447780 1438181 := bbase (se 4 (by rfl) ⟨134829, by rfl⟩ : syracuseStep 1438181 = 269659) (by norm_num)
theorem B1012229 : Blo 447780 1012229 := bbase (se 4 (by rfl) ⟨94896, by rfl⟩ : syracuseStep 1012229 = 189793) (by norm_num)
theorem B487949 : Blo 447780 487949 := bbase (se 3 (by rfl) ⟨91490, by rfl⟩ : syracuseStep 487949 = 182981) (by norm_num)
theorem B1012301 : Blo 447780 1012301 := bbase (se 3 (by rfl) ⟨189806, by rfl⟩ : syracuseStep 1012301 = 379613) (by norm_num)
theorem B455257 : Blo 447780 455257 := bbase (se 2 (by rfl) ⟨170721, by rfl⟩ : syracuseStep 455257 = 341443) (by norm_num)
theorem B1700453 : Blo 447780 1700453 := bbase (se 4 (by rfl) ⟨159417, by rfl⟩ : syracuseStep 1700453 = 318835) (by norm_num)
theorem B1012373 : Blo 447780 1012373 := bbase (se 6 (by rfl) ⟨23727, by rfl⟩ : syracuseStep 1012373 = 47455) (by norm_num)
theorem B1012445 : Blo 447780 1012445 := bbase (se 3 (by rfl) ⟨189833, by rfl⟩ : syracuseStep 1012445 = 379667) (by norm_num)
theorem B1143517 : Blo 447780 1143517 := bbase (se 3 (by rfl) ⟨214409, by rfl⟩ : syracuseStep 1143517 = 428819) (by norm_num)
theorem B1012517 : Blo 447780 1012517 := bbase (se 4 (by rfl) ⟨94923, by rfl⟩ : syracuseStep 1012517 = 189847) (by norm_num)
theorem B717661 : Blo 447780 717661 := bbase (se 3 (by rfl) ⟨134561, by rfl⟩ : syracuseStep 717661 = 269123) (by norm_num)
theorem B1012589 : Blo 447780 1012589 := bbase (se 3 (by rfl) ⟨189860, by rfl⟩ : syracuseStep 1012589 = 379721) (by norm_num)
theorem B1930133 : Blo 447780 1930133 := bbase (se 6 (by rfl) ⟨45237, by rfl⟩ : syracuseStep 1930133 = 90475) (by norm_num)
theorem B1012661 : Blo 447780 1012661 := bbase (se 5 (by rfl) ⟨47468, by rfl⟩ : syracuseStep 1012661 = 94937) (by norm_num)
theorem B1012733 : Blo 447780 1012733 := bbase (se 3 (by rfl) ⟨189887, by rfl⟩ : syracuseStep 1012733 = 379775) (by norm_num)
theorem B1373237 : Blo 447780 1373237 := bbase (se 5 (by rfl) ⟨64370, by rfl⟩ : syracuseStep 1373237 = 128741) (by norm_num)
theorem B1012805 : Blo 447780 1012805 := bbase (se 4 (by rfl) ⟨94950, by rfl⟩ : syracuseStep 1012805 = 189901) (by norm_num)
theorem B717917 : Blo 447780 717917 := bbase (se 3 (by rfl) ⟨134609, by rfl⟩ : syracuseStep 717917 = 269219) (by norm_num)
theorem B1012877 : Blo 447780 1012877 := bbase (se 3 (by rfl) ⟨189914, by rfl⟩ : syracuseStep 1012877 = 379829) (by norm_num)
theorem B1012949 : Blo 447780 1012949 := bbase (se 7 (by rfl) ⟨11870, by rfl⟩ : syracuseStep 1012949 = 23741) (by norm_num)
theorem B3241237 : Blo 447780 3241237 := bbase (se 6 (by rfl) ⟨75966, by rfl⟩ : syracuseStep 3241237 = 151933) (by norm_num)
theorem B1013021 : Blo 447780 1013021 := bbase (se 3 (by rfl) ⟨189941, by rfl⟩ : syracuseStep 1013021 = 379883) (by norm_num)
theorem B1013093 : Blo 447780 1013093 := bbase (se 4 (by rfl) ⟨94977, by rfl⟩ : syracuseStep 1013093 = 189955) (by norm_num)
theorem B1013165 : Blo 447780 1013165 := bbase (se 3 (by rfl) ⟨189968, by rfl⟩ : syracuseStep 1013165 = 379937) (by norm_num)
theorem B521677 : Blo 447780 521677 := bbase (se 3 (by rfl) ⟨97814, by rfl⟩ : syracuseStep 521677 = 195629) (by norm_num)
theorem B1013237 : Blo 447780 1013237 := bbase (se 5 (by rfl) ⟨47495, by rfl⟩ : syracuseStep 1013237 = 94991) (by norm_num)
theorem B1013309 : Blo 447780 1013309 := bbase (se 3 (by rfl) ⟨189995, by rfl⟩ : syracuseStep 1013309 = 379991) (by norm_num)
theorem B1013381 : Blo 447780 1013381 := bbase (se 4 (by rfl) ⟨95004, by rfl⟩ : syracuseStep 1013381 = 190009) (by norm_num)
theorem B1013453 : Blo 447780 1013453 := bbase (se 3 (by rfl) ⟨190022, by rfl⟩ : syracuseStep 1013453 = 380045) (by norm_num)
theorem B456445 : Blo 447780 456445 := bbase (se 3 (by rfl) ⟨85583, by rfl⟩ : syracuseStep 456445 = 171167) (by norm_num)
theorem B1013525 : Blo 447780 1013525 := bbase (se 6 (by rfl) ⟨23754, by rfl⟩ : syracuseStep 1013525 = 47509) (by norm_num)
theorem B1439525 : Blo 447780 1439525 := bbase (se 4 (by rfl) ⟨134955, by rfl⟩ : syracuseStep 1439525 = 269911) (by norm_num)
theorem B1013597 : Blo 447780 1013597 := bbase (se 3 (by rfl) ⟨190049, by rfl⟩ : syracuseStep 1013597 = 380099) (by norm_num)
theorem B1013669 : Blo 447780 1013669 := bbase (se 4 (by rfl) ⟨95031, by rfl⟩ : syracuseStep 1013669 = 190063) (by norm_num)
theorem B718789 : Blo 447780 718789 := bbase (se 4 (by rfl) ⟨67386, by rfl⟩ : syracuseStep 718789 = 134773) (by norm_num)
theorem B1013741 : Blo 447780 1013741 := bbase (se 3 (by rfl) ⟨190076, by rfl⟩ : syracuseStep 1013741 = 380153) (by norm_num)
theorem B718885 : Blo 447780 718885 := bbase (se 4 (by rfl) ⟨67395, by rfl⟩ : syracuseStep 718885 = 134791) (by norm_num)
theorem B1013813 : Blo 447780 1013813 := bbase (se 5 (by rfl) ⟨47522, by rfl⟩ : syracuseStep 1013813 = 95045) (by norm_num)
theorem B456821 : Blo 447780 456821 := bbase (se 5 (by rfl) ⟨21413, by rfl⟩ : syracuseStep 456821 = 42827) (by norm_num)
theorem B1013885 : Blo 447780 1013885 := bbase (se 3 (by rfl) ⟨190103, by rfl⟩ : syracuseStep 1013885 = 380207) (by norm_num)
theorem B1276069 : Blo 447780 1276069 := bbase (se 4 (by rfl) ⟨119631, by rfl⟩ : syracuseStep 1276069 = 239263) (by norm_num)
theorem B719045 : Blo 447780 719045 := bbase (se 4 (by rfl) ⟨67410, by rfl⟩ : syracuseStep 719045 = 134821) (by norm_num)
theorem B1013957 : Blo 447780 1013957 := bbase (se 4 (by rfl) ⟨95058, by rfl⟩ : syracuseStep 1013957 = 190117) (by norm_num)
theorem B850189 : Blo 447780 850189 := bbase (se 3 (by rfl) ⟨159410, by rfl⟩ : syracuseStep 850189 = 318821) (by norm_num)
theorem B1014029 : Blo 447780 1014029 := bbase (se 3 (by rfl) ⟨190130, by rfl⟩ : syracuseStep 1014029 = 380261) (by norm_num)
theorem B1276229 : Blo 447780 1276229 := bbase (se 4 (by rfl) ⟨119646, by rfl⟩ : syracuseStep 1276229 = 239293) (by norm_num)
theorem B1014101 : Blo 447780 1014101 := bbase (se 10 (by rfl) ⟨1485, by rfl⟩ : syracuseStep 1014101 = 2971) (by norm_num)
theorem B2423189 : Blo 447780 2423189 := bbase (se 6 (by rfl) ⟨56793, by rfl⟩ : syracuseStep 2423189 = 113587) (by norm_num)
theorem B850333 : Blo 447780 850333 := bbase (se 3 (by rfl) ⟨159437, by rfl⟩ : syracuseStep 850333 = 318875) (by norm_num)
theorem B1014173 : Blo 447780 1014173 := bbase (se 3 (by rfl) ⟨190157, by rfl⟩ : syracuseStep 1014173 = 380315) (by norm_num)
theorem B2554325 : Blo 447780 2554325 := bbase (se 7 (by rfl) ⟨29933, by rfl⟩ : syracuseStep 2554325 = 59867) (by norm_num)
theorem B1014245 : Blo 447780 1014245 := bbase (se 4 (by rfl) ⟨95085, by rfl⟩ : syracuseStep 1014245 = 190171) (by norm_num)
theorem B1735157 : Blo 447780 1735157 := bbase (se 5 (by rfl) ⟨81335, by rfl⟩ : syracuseStep 1735157 = 162671) (by norm_num)
theorem B1014317 : Blo 447780 1014317 := bbase (se 3 (by rfl) ⟨190184, by rfl⟩ : syracuseStep 1014317 = 380369) (by norm_num)
theorem B1276469 : Blo 447780 1276469 := bbase (se 5 (by rfl) ⟨59834, by rfl⟩ : syracuseStep 1276469 = 119669) (by norm_num)
theorem B2882101 : Blo 447780 2882101 := bbase (se 5 (by rfl) ⟨135098, by rfl⟩ : syracuseStep 2882101 = 270197) (by norm_num)
theorem B850493 : Blo 447780 850493 := bbase (se 3 (by rfl) ⟨159467, by rfl⟩ : syracuseStep 850493 = 318935) (by norm_num)
theorem B1014389 : Blo 447780 1014389 := bbase (se 5 (by rfl) ⟨47549, by rfl⟩ : syracuseStep 1014389 = 95099) (by norm_num)
theorem B1702565 : Blo 447780 1702565 := bbase (se 4 (by rfl) ⟨159615, by rfl⟩ : syracuseStep 1702565 = 319231) (by norm_num)
theorem B457385 : Blo 447780 457385 := bbase (se 2 (by rfl) ⟨171519, by rfl⟩ : syracuseStep 457385 = 343039) (by norm_num)
theorem B1014461 : Blo 447780 1014461 := bbase (se 3 (by rfl) ⟨190211, by rfl⟩ : syracuseStep 1014461 = 380423) (by norm_num)
theorem B850637 : Blo 447780 850637 := bbase (se 3 (by rfl) ⟨159494, by rfl⟩ : syracuseStep 850637 = 318989) (by norm_num)
theorem B457421 : Blo 447780 457421 := bbase (se 3 (by rfl) ⟨85766, by rfl⟩ : syracuseStep 457421 = 171533) (by norm_num)
theorem B1080029 : Blo 447780 1080029 := bbase (se 3 (by rfl) ⟨202505, by rfl⟩ : syracuseStep 1080029 = 405011) (by norm_num)
theorem B1276661 : Blo 447780 1276661 := bbase (se 5 (by rfl) ⟨59843, by rfl⟩ : syracuseStep 1276661 = 119687) (by norm_num)
theorem B1014533 : Blo 447780 1014533 := bbase (se 4 (by rfl) ⟨95112, by rfl⟩ : syracuseStep 1014533 = 190225) (by norm_num)
theorem B1014605 : Blo 447780 1014605 := bbase (se 3 (by rfl) ⟨190238, by rfl⟩ : syracuseStep 1014605 = 380477) (by norm_num)
theorem B1080173 : Blo 447780 1080173 := bbase (se 3 (by rfl) ⟨202532, by rfl⟩ : syracuseStep 1080173 = 405065) (by norm_num)
theorem B1014677 : Blo 447780 1014677 := bbase (se 6 (by rfl) ⟨23781, by rfl⟩ : syracuseStep 1014677 = 47563) (by norm_num)
theorem B1702853 : Blo 447780 1702853 := bbase (se 4 (by rfl) ⟨159642, by rfl⟩ : syracuseStep 1702853 = 319285) (by norm_num)
theorem B1014749 : Blo 447780 1014749 := bbase (se 3 (by rfl) ⟨190265, by rfl⟩ : syracuseStep 1014749 = 380531) (by norm_num)
theorem B850925 : Blo 447780 850925 := bbase (se 3 (by rfl) ⟨159548, by rfl⟩ : syracuseStep 850925 = 319097) (by norm_num)
theorem B1014821 : Blo 447780 1014821 := bbase (se 4 (by rfl) ⟨95139, by rfl⟩ : syracuseStep 1014821 = 190279) (by norm_num)
theorem B1014893 : Blo 447780 1014893 := bbase (se 3 (by rfl) ⟨190292, by rfl⟩ : syracuseStep 1014893 = 380585) (by norm_num)
theorem B851077 : Blo 447780 851077 := bbase (se 4 (by rfl) ⟨79788, by rfl⟩ : syracuseStep 851077 = 159577) (by norm_num)
theorem B1440949 : Blo 447780 1440949 := bbase (se 5 (by rfl) ⟨67544, by rfl⟩ : syracuseStep 1440949 = 135089) (by norm_num)
theorem B1014965 : Blo 447780 1014965 := bbase (se 5 (by rfl) ⟨47576, by rfl⟩ : syracuseStep 1014965 = 95153) (by norm_num)
theorem B1015037 : Blo 447780 1015037 := bbase (se 3 (by rfl) ⟨190319, by rfl⟩ : syracuseStep 1015037 = 380639) (by norm_num)
theorem B720173 : Blo 447780 720173 := bbase (se 3 (by rfl) ⟨135032, by rfl⟩ : syracuseStep 720173 = 270065) (by norm_num)
theorem B1015109 : Blo 447780 1015109 := bbase (se 4 (by rfl) ⟨95166, by rfl⟩ : syracuseStep 1015109 = 190333) (by norm_num)
theorem B1015181 : Blo 447780 1015181 := bbase (se 3 (by rfl) ⟨190346, by rfl⟩ : syracuseStep 1015181 = 380693) (by norm_num)
theorem B851381 : Blo 447780 851381 := bbase (se 5 (by rfl) ⟨39908, by rfl⟩ : syracuseStep 851381 = 79817) (by norm_num)
theorem B1015253 : Blo 447780 1015253 := bbase (se 7 (by rfl) ⟨11897, by rfl⟩ : syracuseStep 1015253 = 23795) (by norm_num)
theorem B1015325 : Blo 447780 1015325 := bbase (se 3 (by rfl) ⟨190373, by rfl⟩ : syracuseStep 1015325 = 380747) (by norm_num)
theorem B1212005 : Blo 447780 1212005 := bbase (se 4 (by rfl) ⟨113625, by rfl⟩ : syracuseStep 1212005 = 227251) (by norm_num)
theorem B1015397 : Blo 447780 1015397 := bbase (se 4 (by rfl) ⟨95193, by rfl⟩ : syracuseStep 1015397 = 190387) (by norm_num)
theorem B2555509 : Blo 447780 2555509 := bbase (se 5 (by rfl) ⟨119789, by rfl⟩ : syracuseStep 2555509 = 239579) (by norm_num)
theorem B1015469 : Blo 447780 1015469 := bbase (se 3 (by rfl) ⟨190400, by rfl⟩ : syracuseStep 1015469 = 380801) (by norm_num)
theorem B1277653 : Blo 447780 1277653 := bbase (se 7 (by rfl) ⟨14972, by rfl⟩ : syracuseStep 1277653 = 29945) (by norm_num)
theorem B1015541 : Blo 447780 1015541 := bbase (se 5 (by rfl) ⟨47603, by rfl⟩ : syracuseStep 1015541 = 95207) (by norm_num)
theorem B720685 : Blo 447780 720685 := bbase (se 3 (by rfl) ⟨135128, by rfl⟩ : syracuseStep 720685 = 270257) (by norm_num)
theorem B1015613 : Blo 447780 1015613 := bbase (se 3 (by rfl) ⟨190427, by rfl⟩ : syracuseStep 1015613 = 380855) (by norm_num)
theorem B1015685 : Blo 447780 1015685 := bbase (se 4 (by rfl) ⟨95220, by rfl⟩ : syracuseStep 1015685 = 190441) (by norm_num)
theorem B1015757 : Blo 447780 1015757 := bbase (se 3 (by rfl) ⟨190454, by rfl⟩ : syracuseStep 1015757 = 380909) (by norm_num)
theorem B1015811 : Blo 447780 1015811 := bstep (se 1 (by rfl) ⟨761858, by rfl⟩ : syracuseStep 1015811 = 1523717) B1523717
theorem B852049 : Blo 447780 852049 := bstep (se 2 (by rfl) ⟨319518, by rfl⟩ : syracuseStep 852049 = 639037) B639037
theorem B8781965 : Blo 447780 8781965 := bstep (se 3 (by rfl) ⟨1646618, by rfl⟩ : syracuseStep 8781965 = 3293237) B3293237
theorem B721057 : Blo 447780 721057 := bstep (se 2 (by rfl) ⟨270396, by rfl⟩ : syracuseStep 721057 = 540793) B540793
theorem B3834053 : Blo 447780 3834053 := bstep (se 4 (by rfl) ⟨359442, by rfl⟩ : syracuseStep 3834053 = 718885) B718885
theorem B1016081 : Blo 447780 1016081 := bstep (se 2 (by rfl) ⟨381030, by rfl⟩ : syracuseStep 1016081 = 762061) B762061
theorem B1016099 : Blo 447780 1016099 := bstep (se 1 (by rfl) ⟨762074, by rfl⟩ : syracuseStep 1016099 = 1524149) B1524149
theorem B2425265 : Blo 447780 2425265 := bstep (se 2 (by rfl) ⟨909474, by rfl⟩ : syracuseStep 2425265 = 1818949) B1818949
theorem B1016369 : Blo 447780 1016369 := bstep (se 2 (by rfl) ⟨381138, by rfl⟩ : syracuseStep 1016369 = 762277) B762277
theorem B1016387 : Blo 447780 1016387 := bstep (se 1 (by rfl) ⟨762290, by rfl⟩ : syracuseStep 1016387 = 1524581) B1524581
theorem B721505 : Blo 447780 721505 := bstep (se 2 (by rfl) ⟨270564, by rfl⟩ : syracuseStep 721505 = 541129) B541129
theorem B2556785 : Blo 447780 2556785 := bstep (se 2 (by rfl) ⟨958794, by rfl⟩ : syracuseStep 2556785 = 1917589) B1917589
theorem B820081 : Blo 447780 820081 := bstep (se 2 (by rfl) ⟨307530, by rfl⟩ : syracuseStep 820081 = 615061) B615061
theorem B1213325 : Blo 447780 1213325 := bstep (se 3 (by rfl) ⟨227498, by rfl⟩ : syracuseStep 1213325 = 454997) B454997
theorem B1278929 : Blo 447780 1278929 := bstep (se 2 (by rfl) ⟨479598, by rfl⟩ : syracuseStep 1278929 = 959197) B959197
theorem B1704995 : Blo 447780 1704995 := bstep (se 1 (by rfl) ⟨1278746, by rfl⟩ : syracuseStep 1704995 = 2557493) B2557493
theorem B1705009 : Blo 447780 1705009 := bstep (se 2 (by rfl) ⟨639378, by rfl⟩ : syracuseStep 1705009 = 1278757) B1278757
theorem B1442897 : Blo 447780 1442897 := bstep (se 2 (by rfl) ⟨541086, by rfl⟩ : syracuseStep 1442897 = 1082173) B1082173
theorem B853105 : Blo 447780 853105 := bstep (se 2 (by rfl) ⟨319914, by rfl⟩ : syracuseStep 853105 = 639829) B639829
theorem B820433 : Blo 447780 820433 := bstep (se 2 (by rfl) ⟨307662, by rfl⟩ : syracuseStep 820433 = 615325) B615325
theorem B722371 : Blo 447780 722371 := bstep (se 1 (by rfl) ⟨541778, by rfl⟩ : syracuseStep 722371 = 1083557) B1083557
theorem B853507 : Blo 447780 853507 := bstep (se 1 (by rfl) ⟨640130, by rfl⟩ : syracuseStep 853507 = 1280261) B1280261
theorem B853553 : Blo 447780 853553 := bstep (se 2 (by rfl) ⟨320082, by rfl⟩ : syracuseStep 853553 = 640165) B640165
theorem B1279601 : Blo 447780 1279601 := bstep (se 2 (by rfl) ⟨479850, by rfl⟩ : syracuseStep 1279601 = 959701) B959701
theorem B1443523 : Blo 447780 1443523 := bstep (se 1 (by rfl) ⟨1082642, by rfl⟩ : syracuseStep 1443523 = 2165285) B2165285
theorem B853841 : Blo 447780 853841 := bstep (se 2 (by rfl) ⟨320190, by rfl⟩ : syracuseStep 853841 = 640381) B640381
theorem B4097891 : Blo 447780 4097891 := bstep (se 1 (by rfl) ⟨3073418, by rfl⟩ : syracuseStep 4097891 = 6146837) B6146837
theorem B755635 : Blo 447780 755635 := bstep (se 1 (by rfl) ⟨566726, by rfl⟩ : syracuseStep 755635 = 1133453) B1133453
theorem B755777 : Blo 447780 755777 := bstep (se 2 (by rfl) ⟨283416, by rfl⟩ : syracuseStep 755777 = 566833) B566833
theorem B723043 : Blo 447780 723043 := bstep (se 1 (by rfl) ⟨542282, by rfl⟩ : syracuseStep 723043 = 1084565) B1084565
theorem B1542253 : Blo 447780 1542253 := bstep (se 3 (by rfl) ⟨289172, by rfl⟩ : syracuseStep 1542253 = 578345) B578345
theorem B723089 : Blo 447780 723089 := bstep (se 2 (by rfl) ⟨271158, by rfl⟩ : syracuseStep 723089 = 542317) B542317
theorem B755905 : Blo 447780 755905 := bstep (se 2 (by rfl) ⟨283464, by rfl⟩ : syracuseStep 755905 = 566929) B566929
theorem B755939 : Blo 447780 755939 := bstep (se 1 (by rfl) ⟨566954, by rfl⟩ : syracuseStep 755939 = 1133909) B1133909
theorem B2558243 : Blo 447780 2558243 := bstep (se 1 (by rfl) ⟨1918682, by rfl⟩ : syracuseStep 2558243 = 3837365) B3837365
theorem B756067 : Blo 447780 756067 := bstep (se 1 (by rfl) ⟨567050, by rfl⟩ : syracuseStep 756067 = 1134101) B1134101
theorem B1575299 : Blo 447780 1575299 := bstep (se 1 (by rfl) ⟨1181474, by rfl⟩ : syracuseStep 1575299 = 2362949) B2362949
theorem B1280387 : Blo 447780 1280387 := bstep (se 1 (by rfl) ⟨960290, by rfl⟩ : syracuseStep 1280387 = 1920581) B1920581
theorem B2591117 : Blo 447780 2591117 := bstep (se 3 (by rfl) ⟨485834, by rfl⟩ : syracuseStep 2591117 = 971669) B971669
theorem B5147021 : Blo 447780 5147021 := bstep (se 3 (by rfl) ⟨965066, by rfl⟩ : syracuseStep 5147021 = 1930133) B1930133
theorem B1706467 : Blo 447780 1706467 := bstep (se 1 (by rfl) ⟨1279850, by rfl⟩ : syracuseStep 1706467 = 2559701) B2559701
theorem B756209 : Blo 447780 756209 := bstep (se 2 (by rfl) ⟨283578, by rfl⟩ : syracuseStep 756209 = 567157) B567157
theorem B4098545 : Blo 447780 4098545 := bstep (se 2 (by rfl) ⟨1536954, by rfl⟩ : syracuseStep 4098545 = 3073909) B3073909
theorem B854563 : Blo 447780 854563 := bstep (se 1 (by rfl) ⟨640922, by rfl⟩ : syracuseStep 854563 = 1281845) B1281845
theorem B756337 : Blo 447780 756337 := bstep (se 2 (by rfl) ⟨283626, by rfl⟩ : syracuseStep 756337 = 567253) B567253
theorem B723601 : Blo 447780 723601 := bstep (se 2 (by rfl) ⟨271350, by rfl⟩ : syracuseStep 723601 = 542701) B542701
theorem B756371 : Blo 447780 756371 := bstep (se 1 (by rfl) ⟨567278, by rfl⟩ : syracuseStep 756371 = 1134557) B1134557
theorem B1280717 : Blo 447780 1280717 := bstep (se 3 (by rfl) ⟨240134, by rfl⟩ : syracuseStep 1280717 = 480269) B480269
theorem B1280785 : Blo 447780 1280785 := bstep (se 2 (by rfl) ⟨480294, by rfl⟩ : syracuseStep 1280785 = 960589) B960589
theorem B756499 : Blo 447780 756499 := bstep (se 1 (by rfl) ⟨567374, by rfl⟩ : syracuseStep 756499 = 1134749) B1134749
theorem B1444753 : Blo 447780 1444753 := bstep (se 2 (by rfl) ⟨541782, by rfl⟩ : syracuseStep 1444753 = 1083565) B1083565
theorem B756641 : Blo 447780 756641 := bstep (se 2 (by rfl) ⟨283740, by rfl⟩ : syracuseStep 756641 = 567481) B567481
theorem B855011 : Blo 447780 855011 := bstep (se 1 (by rfl) ⟨641258, by rfl⟩ : syracuseStep 855011 = 1282517) B1282517
theorem B1543139 : Blo 447780 1543139 := bstep (se 1 (by rfl) ⟨1157354, by rfl⟩ : syracuseStep 1543139 = 2314709) B2314709
theorem B756769 : Blo 447780 756769 := bstep (se 2 (by rfl) ⟨283788, by rfl⟩ : syracuseStep 756769 = 567577) B567577
theorem B1281059 : Blo 447780 1281059 := bstep (se 1 (by rfl) ⟨960794, by rfl⟩ : syracuseStep 1281059 = 1921589) B1921589
theorem B756803 : Blo 447780 756803 := bstep (se 1 (by rfl) ⟨567602, by rfl⟩ : syracuseStep 756803 = 1135205) B1135205
theorem B822449 : Blo 447780 822449 := bstep (se 2 (by rfl) ⟨308418, by rfl⟩ : syracuseStep 822449 = 616837) B616837
theorem B756931 : Blo 447780 756931 := bstep (se 1 (by rfl) ⟨567698, by rfl⟩ : syracuseStep 756931 = 1135397) B1135397
theorem B855299 : Blo 447780 855299 := bstep (se 1 (by rfl) ⟨641474, by rfl⟩ : syracuseStep 855299 = 1282949) B1282949
theorem B757073 : Blo 447780 757073 := bstep (se 2 (by rfl) ⟨283902, by rfl⟩ : syracuseStep 757073 = 567805) B567805
theorem B757201 : Blo 447780 757201 := bstep (se 2 (by rfl) ⟨283950, by rfl⟩ : syracuseStep 757201 = 567901) B567901
theorem B1445357 : Blo 447780 1445357 := bstep (se 3 (by rfl) ⟨271004, by rfl⟩ : syracuseStep 1445357 = 542009) B542009
theorem B757235 : Blo 447780 757235 := bstep (se 1 (by rfl) ⟨567926, by rfl⟩ : syracuseStep 757235 = 1135853) B1135853
theorem B3640945 : Blo 447780 3640945 := bstep (se 2 (by rfl) ⟨1365354, by rfl⟩ : syracuseStep 3640945 = 2730709) B2730709
theorem B757363 : Blo 447780 757363 := bstep (se 1 (by rfl) ⟨568022, by rfl⟩ : syracuseStep 757363 = 1136045) B1136045
theorem B757505 : Blo 447780 757505 := bstep (se 2 (by rfl) ⟨284064, by rfl⟩ : syracuseStep 757505 = 568129) B568129
theorem B1085201 : Blo 447780 1085201 := bstep (se 2 (by rfl) ⟨406950, by rfl⟩ : syracuseStep 1085201 = 813901) B813901
theorem B1281901 : Blo 447780 1281901 := bstep (se 3 (by rfl) ⟨240356, by rfl⟩ : syracuseStep 1281901 = 480713) B480713
theorem B757633 : Blo 447780 757633 := bstep (se 2 (by rfl) ⟨284112, by rfl⟩ : syracuseStep 757633 = 568225) B568225
theorem B757667 : Blo 447780 757667 := bstep (se 1 (by rfl) ⟨568250, by rfl⟩ : syracuseStep 757667 = 1136501) B1136501
theorem B1544113 : Blo 447780 1544113 := bstep (se 2 (by rfl) ⟨579042, by rfl⟩ : syracuseStep 1544113 = 1158085) B1158085
theorem B1511405 : Blo 447780 1511405 := bstep (se 3 (by rfl) ⟨283388, by rfl⟩ : syracuseStep 1511405 = 566777) B566777
theorem B1282061 : Blo 447780 1282061 := bstep (se 3 (by rfl) ⟨240386, by rfl⟩ : syracuseStep 1282061 = 480773) B480773
theorem B1511459 : Blo 447780 1511459 := bstep (se 1 (by rfl) ⟨1133594, by rfl⟩ : syracuseStep 1511459 = 2267189) B2267189
theorem B757795 : Blo 447780 757795 := bstep (se 1 (by rfl) ⟨568346, by rfl⟩ : syracuseStep 757795 = 1136693) B1136693
theorem B757937 : Blo 447780 757937 := bstep (se 2 (by rfl) ⟨284226, by rfl⟩ : syracuseStep 757937 = 568453) B568453
theorem B856241 : Blo 447780 856241 := bstep (se 2 (by rfl) ⟨321090, by rfl⟩ : syracuseStep 856241 = 642181) B642181
theorem B1282243 : Blo 447780 1282243 := bstep (se 1 (by rfl) ⟨961682, by rfl⟩ : syracuseStep 1282243 = 1923365) B1923365
theorem B1511729 : Blo 447780 1511729 := bstep (se 2 (by rfl) ⟨566898, by rfl⟩ : syracuseStep 1511729 = 1133797) B1133797
theorem B758065 : Blo 447780 758065 := bstep (se 2 (by rfl) ⟨284274, by rfl⟩ : syracuseStep 758065 = 568549) B568549
theorem B758099 : Blo 447780 758099 := bstep (se 1 (by rfl) ⟨568574, by rfl⟩ : syracuseStep 758099 = 1137149) B1137149
theorem B758227 : Blo 447780 758227 := bstep (se 1 (by rfl) ⟨568670, by rfl⟩ : syracuseStep 758227 = 1137341) B1137341
theorem B758369 : Blo 447780 758369 := bstep (se 2 (by rfl) ⟨284388, by rfl⟩ : syracuseStep 758369 = 568777) B568777
theorem B1708685 : Blo 447780 1708685 := bstep (se 3 (by rfl) ⟨320378, by rfl⟩ : syracuseStep 1708685 = 640757) B640757
theorem B3117731 : Blo 447780 3117731 := bstep (se 1 (by rfl) ⟨2338298, by rfl⟩ : syracuseStep 3117731 = 4676597) B4676597
theorem B758497 : Blo 447780 758497 := bstep (se 2 (by rfl) ⟨284436, by rfl⟩ : syracuseStep 758497 = 568873) B568873
theorem B758531 : Blo 447780 758531 := bstep (se 1 (by rfl) ⟨568898, by rfl⟩ : syracuseStep 758531 = 1137797) B1137797
theorem B2724677 : Blo 447780 2724677 := bstep (se 4 (by rfl) ⟨255438, by rfl⟩ : syracuseStep 2724677 = 510877) B510877
theorem B1512269 : Blo 447780 1512269 := bstep (se 3 (by rfl) ⟨283550, by rfl⟩ : syracuseStep 1512269 = 567101) B567101
theorem B1643377 : Blo 447780 1643377 := bstep (se 2 (by rfl) ⟨616266, by rfl⟩ : syracuseStep 1643377 = 1232533) B1232533
theorem B1512323 : Blo 447780 1512323 := bstep (se 1 (by rfl) ⟨1134242, by rfl⟩ : syracuseStep 1512323 = 2268485) B2268485
theorem B758659 : Blo 447780 758659 := bstep (se 1 (by rfl) ⟨568994, by rfl⟩ : syracuseStep 758659 = 1137989) B1137989
theorem B758801 : Blo 447780 758801 := bstep (se 2 (by rfl) ⟨284550, by rfl⟩ : syracuseStep 758801 = 569101) B569101
theorem B857137 : Blo 447780 857137 := bstep (se 2 (by rfl) ⟨321426, by rfl⟩ : syracuseStep 857137 = 642853) B642853
theorem B3839075 : Blo 447780 3839075 := bstep (se 1 (by rfl) ⟨2879306, by rfl⟩ : syracuseStep 3839075 = 5758613) B5758613
theorem B1512593 : Blo 447780 1512593 := bstep (se 2 (by rfl) ⟨567222, by rfl⟩ : syracuseStep 1512593 = 1134445) B1134445
theorem B758929 : Blo 447780 758929 := bstep (se 2 (by rfl) ⟨284598, by rfl⟩ : syracuseStep 758929 = 569197) B569197
theorem B758963 : Blo 447780 758963 := bstep (se 1 (by rfl) ⟨569222, by rfl⟩ : syracuseStep 758963 = 1138445) B1138445
theorem B857297 : Blo 447780 857297 := bstep (se 2 (by rfl) ⟨321486, by rfl⟩ : syracuseStep 857297 = 642973) B642973
theorem B2888945 : Blo 447780 2888945 := bstep (se 2 (by rfl) ⟨1083354, by rfl⟩ : syracuseStep 2888945 = 2166709) B2166709
theorem B759091 : Blo 447780 759091 := bstep (se 1 (by rfl) ⟨569318, by rfl⟩ : syracuseStep 759091 = 1138637) B1138637
theorem B759233 : Blo 447780 759233 := bstep (se 2 (by rfl) ⟨284712, by rfl⟩ : syracuseStep 759233 = 569425) B569425
theorem B1283633 : Blo 447780 1283633 := bstep (se 2 (by rfl) ⟨481362, by rfl⟩ : syracuseStep 1283633 = 962725) B962725
theorem B759361 : Blo 447780 759361 := bstep (se 2 (by rfl) ⟨284760, by rfl⟩ : syracuseStep 759361 = 569521) B569521
theorem B759395 : Blo 447780 759395 := bstep (se 1 (by rfl) ⟨569546, by rfl⟩ : syracuseStep 759395 = 1139093) B1139093
theorem B1513133 : Blo 447780 1513133 := bstep (se 3 (by rfl) ⟨283712, by rfl⟩ : syracuseStep 1513133 = 567425) B567425
theorem B1513187 : Blo 447780 1513187 := bstep (se 1 (by rfl) ⟨1134890, by rfl⟩ : syracuseStep 1513187 = 2269781) B2269781
theorem B759523 : Blo 447780 759523 := bstep (se 1 (by rfl) ⟨569642, by rfl⟩ : syracuseStep 759523 = 1139285) B1139285
theorem B759665 : Blo 447780 759665 := bstep (se 2 (by rfl) ⟨284874, by rfl⟩ : syracuseStep 759665 = 569749) B569749
theorem B956369 : Blo 447780 956369 := bstep (se 2 (by rfl) ⟨358638, by rfl⟩ : syracuseStep 956369 = 717277) B717277
theorem B1513457 : Blo 447780 1513457 := bstep (se 2 (by rfl) ⟨567546, by rfl⟩ : syracuseStep 1513457 = 1135093) B1135093
theorem B759793 : Blo 447780 759793 := bstep (se 2 (by rfl) ⟨284922, by rfl⟩ : syracuseStep 759793 = 569845) B569845
theorem B759827 : Blo 447780 759827 := bstep (se 1 (by rfl) ⟨569870, by rfl⟩ : syracuseStep 759827 = 1139741) B1139741
theorem B5544035 : Blo 447780 5544035 := bstep (se 1 (by rfl) ⟨4158026, by rfl⟩ : syracuseStep 5544035 = 8316053) B8316053
theorem B759955 : Blo 447780 759955 := bstep (se 1 (by rfl) ⟨569966, by rfl⟩ : syracuseStep 759955 = 1139933) B1139933
theorem B5478641 : Blo 447780 5478641 := bstep (se 2 (by rfl) ⟨2054490, by rfl⟩ : syracuseStep 5478641 = 4108981) B4108981
theorem B760097 : Blo 447780 760097 := bstep (se 2 (by rfl) ⟨285036, by rfl⟩ : syracuseStep 760097 = 570073) B570073
theorem B2890019 : Blo 447780 2890019 := bstep (se 1 (by rfl) ⟨2167514, by rfl⟩ : syracuseStep 2890019 = 4335029) B4335029
theorem B760225 : Blo 447780 760225 := bstep (se 2 (by rfl) ⟨285084, by rfl⟩ : syracuseStep 760225 = 570169) B570169
theorem B760259 : Blo 447780 760259 := bstep (se 1 (by rfl) ⟨570194, by rfl⟩ : syracuseStep 760259 = 1140389) B1140389
theorem B956881 : Blo 447780 956881 := bstep (se 2 (by rfl) ⟨358830, by rfl⟩ : syracuseStep 956881 = 717661) B717661
theorem B1284589 : Blo 447780 1284589 := bstep (se 3 (by rfl) ⟨240860, by rfl⟩ : syracuseStep 1284589 = 481721) B481721
theorem B1513997 : Blo 447780 1513997 := bstep (se 3 (by rfl) ⟨283874, by rfl⟩ : syracuseStep 1513997 = 567749) B567749
theorem B1514051 : Blo 447780 1514051 := bstep (se 1 (by rfl) ⟨1135538, by rfl⟩ : syracuseStep 1514051 = 2271077) B2271077
theorem B760387 : Blo 447780 760387 := bstep (se 1 (by rfl) ⟨570290, by rfl⟩ : syracuseStep 760387 = 1140581) B1140581
theorem B760529 : Blo 447780 760529 := bstep (se 2 (by rfl) ⟨285198, by rfl⟩ : syracuseStep 760529 = 570397) B570397
theorem B1284817 : Blo 447780 1284817 := bstep (se 2 (by rfl) ⟨481806, by rfl⟩ : syracuseStep 1284817 = 963613) B963613
theorem B5184269 : Blo 447780 5184269 := bstep (se 3 (by rfl) ⟨972050, by rfl⟩ : syracuseStep 5184269 = 1944101) B1944101
theorem B1514321 : Blo 447780 1514321 := bstep (se 2 (by rfl) ⟨567870, by rfl⟩ : syracuseStep 1514321 = 1135741) B1135741
theorem B760657 : Blo 447780 760657 := bstep (se 2 (by rfl) ⟨285246, by rfl⟩ : syracuseStep 760657 = 570493) B570493
theorem B1284977 : Blo 447780 1284977 := bstep (se 2 (by rfl) ⟨481866, by rfl⟩ : syracuseStep 1284977 = 963733) B963733
theorem B760691 : Blo 447780 760691 := bstep (se 1 (by rfl) ⟨570518, by rfl⟩ : syracuseStep 760691 = 1141037) B1141037
theorem B1285091 : Blo 447780 1285091 := bstep (se 1 (by rfl) ⟨963818, by rfl⟩ : syracuseStep 1285091 = 1927637) B1927637
theorem B760819 : Blo 447780 760819 := bstep (se 1 (by rfl) ⟨570614, by rfl⟩ : syracuseStep 760819 = 1141229) B1141229
theorem B728131 : Blo 447780 728131 := bstep (se 1 (by rfl) ⟨546098, by rfl⟩ : syracuseStep 728131 = 1092197) B1092197
theorem B1219693 : Blo 447780 1219693 := bstep (se 3 (by rfl) ⟨228692, by rfl⟩ : syracuseStep 1219693 = 457385) B457385
theorem B760961 : Blo 447780 760961 := bstep (se 2 (by rfl) ⟨285360, by rfl⟩ : syracuseStep 760961 = 570721) B570721
theorem B2268323 : Blo 447780 2268323 := bstep (se 1 (by rfl) ⟨1701242, by rfl⟩ : syracuseStep 2268323 = 3402485) B3402485
theorem B1219789 : Blo 447780 1219789 := bstep (se 3 (by rfl) ⟨228710, by rfl⟩ : syracuseStep 1219789 = 457421) B457421
theorem B5250275 : Blo 447780 5250275 := bstep (se 1 (by rfl) ⟨3937706, by rfl⟩ : syracuseStep 5250275 = 7875413) B7875413
theorem B761089 : Blo 447780 761089 := bstep (se 2 (by rfl) ⟨285408, by rfl⟩ : syracuseStep 761089 = 570817) B570817
theorem B695569 : Blo 447780 695569 := bstep (se 2 (by rfl) ⟨260838, by rfl⟩ : syracuseStep 695569 = 521677) B521677
theorem B761123 : Blo 447780 761123 := bstep (se 1 (by rfl) ⟨570842, by rfl⟩ : syracuseStep 761123 = 1141685) B1141685
theorem B1514861 : Blo 447780 1514861 := bstep (se 3 (by rfl) ⟨284036, by rfl⟩ : syracuseStep 1514861 = 568073) B568073
theorem B1514915 : Blo 447780 1514915 := bstep (se 1 (by rfl) ⟨1136186, by rfl⟩ : syracuseStep 1514915 = 2272373) B2272373
theorem B761251 : Blo 447780 761251 := bstep (se 1 (by rfl) ⟨570938, by rfl⟩ : syracuseStep 761251 = 1141877) B1141877
theorem B1711601 : Blo 447780 1711601 := bstep (se 2 (by rfl) ⟨641850, by rfl⟩ : syracuseStep 1711601 = 1283701) B1283701
theorem B761393 : Blo 447780 761393 := bstep (se 2 (by rfl) ⟨285522, by rfl⟩ : syracuseStep 761393 = 571045) B571045
theorem B1515185 : Blo 447780 1515185 := bstep (se 2 (by rfl) ⟨568194, by rfl⟩ : syracuseStep 1515185 = 1136389) B1136389
theorem B761521 : Blo 447780 761521 := bstep (se 2 (by rfl) ⟨285570, by rfl⟩ : syracuseStep 761521 = 571141) B571141
theorem B761555 : Blo 447780 761555 := bstep (se 1 (by rfl) ⟨571166, by rfl⟩ : syracuseStep 761555 = 1142333) B1142333
theorem B7282403 : Blo 447780 7282403 := bstep (se 1 (by rfl) ⟨5461802, by rfl⟩ : syracuseStep 7282403 = 10923605) B10923605
theorem B761683 : Blo 447780 761683 := bstep (se 1 (by rfl) ⟨571262, by rfl⟩ : syracuseStep 761683 = 1142525) B1142525
theorem B958385 : Blo 447780 958385 := bstep (se 2 (by rfl) ⟨359394, by rfl⟩ : syracuseStep 958385 = 718789) B718789
theorem B2269133 : Blo 447780 2269133 := bstep (se 3 (by rfl) ⟨425462, by rfl⟩ : syracuseStep 2269133 = 850925) B850925
theorem B1286093 : Blo 447780 1286093 := bstep (se 3 (by rfl) ⟨241142, by rfl⟩ : syracuseStep 1286093 = 482285) B482285
theorem B761825 : Blo 447780 761825 := bstep (se 2 (by rfl) ⟨285684, by rfl⟩ : syracuseStep 761825 = 571369) B571369
theorem B2334691 : Blo 447780 2334691 := bstep (se 1 (by rfl) ⟨1751018, by rfl⟩ : syracuseStep 2334691 = 3502037) B3502037
theorem B761953 : Blo 447780 761953 := bstep (se 2 (by rfl) ⟨285732, by rfl⟩ : syracuseStep 761953 = 571465) B571465
theorem B761987 : Blo 447780 761987 := bstep (se 1 (by rfl) ⟨571490, by rfl⟩ : syracuseStep 761987 = 1142981) B1142981
theorem B1286275 : Blo 447780 1286275 := bstep (se 1 (by rfl) ⟨964706, by rfl⟩ : syracuseStep 1286275 = 1929413) B1929413
theorem B1515725 : Blo 447780 1515725 := bstep (se 3 (by rfl) ⟨284198, by rfl⟩ : syracuseStep 1515725 = 568397) B568397
theorem B1515779 : Blo 447780 1515779 := bstep (se 1 (by rfl) ⟨1136834, by rfl⟩ : syracuseStep 1515779 = 2273669) B2273669
theorem B762115 : Blo 447780 762115 := bstep (se 1 (by rfl) ⟨571586, by rfl⟩ : syracuseStep 762115 = 1143173) B1143173
theorem B1286435 : Blo 447780 1286435 := bstep (se 1 (by rfl) ⟨964826, by rfl⟩ : syracuseStep 1286435 = 1929653) B1929653
theorem B958787 : Blo 447780 958787 := bstep (se 1 (by rfl) ⟨719090, by rfl⟩ : syracuseStep 958787 = 1438181) B1438181
theorem B762257 : Blo 447780 762257 := bstep (se 2 (by rfl) ⟨285846, by rfl⟩ : syracuseStep 762257 = 571693) B571693
theorem B1516049 : Blo 447780 1516049 := bstep (se 2 (by rfl) ⟨568518, by rfl⟩ : syracuseStep 1516049 = 1137037) B1137037
theorem B3842801 : Blo 447780 3842801 := bstep (se 2 (by rfl) ⟨1441050, by rfl⟩ : syracuseStep 3842801 = 2882101) B2882101
theorem B3253061 : Blo 447780 3253061 := bstep (se 4 (by rfl) ⟨304974, by rfl⟩ : syracuseStep 3253061 = 609949) B609949
theorem B1713059 : Blo 447780 1713059 := bstep (se 1 (by rfl) ⟨1284794, by rfl⟩ : syracuseStep 1713059 = 2569589) B2569589
theorem B1516589 : Blo 447780 1516589 := bstep (se 3 (by rfl) ⟨284360, by rfl⟩ : syracuseStep 1516589 = 568721) B568721
theorem B1516643 : Blo 447780 1516643 := bstep (se 1 (by rfl) ⟨1137482, by rfl⟩ : syracuseStep 1516643 = 2274965) B2274965
theorem B664723 : Blo 447780 664723 := bstep (se 1 (by rfl) ⟨498542, by rfl⟩ : syracuseStep 664723 = 997085) B997085
theorem B959683 : Blo 447780 959683 := bstep (se 1 (by rfl) ⟨719762, by rfl⟩ : syracuseStep 959683 = 1439525) B1439525
theorem B2434373 : Blo 447780 2434373 := bstep (se 4 (by rfl) ⟨228222, by rfl⟩ : syracuseStep 2434373 = 456445) B456445
theorem B1516913 : Blo 447780 1516913 := bstep (se 2 (by rfl) ⟨568842, by rfl⟩ : syracuseStep 1516913 = 1137685) B1137685
theorem B1615373 : Blo 447780 1615373 := bstep (se 3 (by rfl) ⟨302882, by rfl⟩ : syracuseStep 1615373 = 605765) B605765
theorem B1615459 : Blo 447780 1615459 := bstep (se 1 (by rfl) ⟨1211594, by rfl⟩ : syracuseStep 1615459 = 2423189) B2423189
theorem B6006413 : Blo 447780 6006413 := bstep (se 3 (by rfl) ⟨1126202, by rfl⟩ : syracuseStep 6006413 = 2252405) B2252405
theorem B763537 : Blo 447780 763537 := bstep (se 2 (by rfl) ⟨286326, by rfl⟩ : syracuseStep 763537 = 572653) B572653
theorem B1156771 : Blo 447780 1156771 := bstep (se 1 (by rfl) ⟨867578, by rfl⟩ : syracuseStep 1156771 = 1735157) B1735157
theorem B566995 : Blo 447780 566995 := bstep (se 1 (by rfl) ⟨425246, by rfl⟩ : syracuseStep 566995 = 850493) B850493
theorem B1976035 : Blo 447780 1976035 := bstep (se 1 (by rfl) ⟨1482026, by rfl⟩ : syracuseStep 1976035 = 2964053) B2964053
theorem B567091 : Blo 447780 567091 := bstep (se 1 (by rfl) ⟨425318, by rfl⟩ : syracuseStep 567091 = 850637) B850637
theorem B1517453 : Blo 447780 1517453 := bstep (se 3 (by rfl) ⟨284522, by rfl⟩ : syracuseStep 1517453 = 569045) B569045
theorem B1714061 : Blo 447780 1714061 := bstep (se 3 (by rfl) ⟨321386, by rfl⟩ : syracuseStep 1714061 = 642773) B642773
theorem B1517507 : Blo 447780 1517507 := bstep (se 1 (by rfl) ⟨1138130, by rfl⟩ : syracuseStep 1517507 = 2276261) B2276261
theorem B1517777 : Blo 447780 1517777 := bstep (se 2 (by rfl) ⟨569166, by rfl⟩ : syracuseStep 1517777 = 1138333) B1138333
theorem B567587 : Blo 447780 567587 := bstep (se 1 (by rfl) ⟨425690, by rfl⟩ : syracuseStep 567587 = 851381) B851381
theorem B1026353 : Blo 447780 1026353 := bstep (se 2 (by rfl) ⟨384882, by rfl⟩ : syracuseStep 1026353 = 769765) B769765
theorem B2894221 : Blo 447780 2894221 := bstep (se 3 (by rfl) ⟨542666, by rfl⟩ : syracuseStep 2894221 = 1085333) B1085333
theorem B960913 : Blo 447780 960913 := bstep (se 2 (by rfl) ⟨360342, by rfl⟩ : syracuseStep 960913 = 720685) B720685
theorem B1518317 : Blo 447780 1518317 := bstep (se 3 (by rfl) ⟨284684, by rfl⟩ : syracuseStep 1518317 = 569369) B569369
theorem B1518371 : Blo 447780 1518371 := bstep (se 1 (by rfl) ⟨1138778, by rfl⟩ : syracuseStep 1518371 = 2277557) B2277557
theorem B2272049 : Blo 447780 2272049 := bstep (se 2 (by rfl) ⟨852018, by rfl⟩ : syracuseStep 2272049 = 1704037) B1704037
theorem B568291 : Blo 447780 568291 := bstep (se 1 (by rfl) ⟨426218, by rfl⟩ : syracuseStep 568291 = 852437) B852437
theorem B2567173 : Blo 447780 2567173 := bstep (se 4 (by rfl) ⟨240672, by rfl⟩ : syracuseStep 2567173 = 481345) B481345
theorem B1518641 : Blo 447780 1518641 := bstep (se 2 (by rfl) ⟨569490, by rfl⟩ : syracuseStep 1518641 = 1138981) B1138981
theorem B568387 : Blo 447780 568387 := bstep (se 1 (by rfl) ⟨426290, by rfl⟩ : syracuseStep 568387 = 852581) B852581
theorem B3452357 : Blo 447780 3452357 := bstep (se 4 (by rfl) ⟨323658, by rfl⟩ : syracuseStep 3452357 = 647317) B647317
theorem B568883 : Blo 447780 568883 := bstep (se 1 (by rfl) ⟨426662, by rfl⟩ : syracuseStep 568883 = 853325) B853325
theorem B1519181 : Blo 447780 1519181 := bstep (se 3 (by rfl) ⟨284846, by rfl⟩ : syracuseStep 1519181 = 569693) B569693
theorem B1519235 : Blo 447780 1519235 := bstep (se 1 (by rfl) ⟨1139426, by rfl⟩ : syracuseStep 1519235 = 2278853) B2278853
theorem B962417 : Blo 447780 962417 := bstep (se 2 (by rfl) ⟨360906, by rfl⟩ : syracuseStep 962417 = 721813) B721813
theorem B962435 : Blo 447780 962435 := bstep (se 1 (by rfl) ⟨721826, by rfl⟩ : syracuseStep 962435 = 1443653) B1443653
theorem B1519505 : Blo 447780 1519505 := bstep (se 2 (by rfl) ⟨569814, by rfl⟩ : syracuseStep 1519505 = 1139629) B1139629
theorem B503779 : Blo 447780 503779 := bstep (se 1 (by rfl) ⟨377834, by rfl⟩ : syracuseStep 503779 = 755669) B755669
theorem B503923 : Blo 447780 503923 := bstep (se 1 (by rfl) ⟨377942, by rfl⟩ : syracuseStep 503923 = 755885) B755885
theorem B2273507 : Blo 447780 2273507 := bstep (se 1 (by rfl) ⟨1705130, by rfl⟩ : syracuseStep 2273507 = 3410261) B3410261
theorem B569587 : Blo 447780 569587 := bstep (se 1 (by rfl) ⟨427190, by rfl⟩ : syracuseStep 569587 = 854381) B854381
theorem B504067 : Blo 447780 504067 := bstep (se 1 (by rfl) ⟨378050, by rfl⟩ : syracuseStep 504067 = 756101) B756101
theorem B569683 : Blo 447780 569683 := bstep (se 1 (by rfl) ⟨427262, by rfl⟩ : syracuseStep 569683 = 854525) B854525
theorem B504211 : Blo 447780 504211 := bstep (se 1 (by rfl) ⟨378158, by rfl⟩ : syracuseStep 504211 = 756317) B756317
theorem B1520045 : Blo 447780 1520045 := bstep (se 3 (by rfl) ⟨285008, by rfl⟩ : syracuseStep 1520045 = 570017) B570017
theorem B1520099 : Blo 447780 1520099 := bstep (se 1 (by rfl) ⟨1140074, by rfl⟩ : syracuseStep 1520099 = 2280149) B2280149
theorem B504355 : Blo 447780 504355 := bstep (se 1 (by rfl) ⟨378266, by rfl⟩ : syracuseStep 504355 = 756533) B756533
theorem B3846797 : Blo 447780 3846797 := bstep (se 3 (by rfl) ⟨721274, by rfl⟩ : syracuseStep 3846797 = 1442549) B1442549
theorem B504499 : Blo 447780 504499 := bstep (se 1 (by rfl) ⟨378374, by rfl⟩ : syracuseStep 504499 = 756749) B756749
theorem B1520369 : Blo 447780 1520369 := bstep (se 2 (by rfl) ⟨570138, by rfl⟩ : syracuseStep 1520369 = 1140277) B1140277
theorem B504643 : Blo 447780 504643 := bstep (se 1 (by rfl) ⟨378482, by rfl⟩ : syracuseStep 504643 = 756965) B756965
theorem B570179 : Blo 447780 570179 := bstep (se 1 (by rfl) ⟨427634, by rfl⟩ : syracuseStep 570179 = 855269) B855269
theorem B2569157 : Blo 447780 2569157 := bstep (se 4 (by rfl) ⟨240858, by rfl⟩ : syracuseStep 2569157 = 481717) B481717
theorem B504787 : Blo 447780 504787 := bstep (se 1 (by rfl) ⟨378590, by rfl⟩ : syracuseStep 504787 = 757181) B757181
theorem B2274317 : Blo 447780 2274317 := bstep (se 3 (by rfl) ⟨426434, by rfl⟩ : syracuseStep 2274317 = 852869) B852869
theorem B504931 : Blo 447780 504931 := bstep (se 1 (by rfl) ⟨378698, by rfl⟩ : syracuseStep 504931 = 757397) B757397
theorem B505075 : Blo 447780 505075 := bstep (se 1 (by rfl) ⟨378806, by rfl⟩ : syracuseStep 505075 = 757613) B757613
theorem B1520909 : Blo 447780 1520909 := bstep (se 3 (by rfl) ⟨285170, by rfl⟩ : syracuseStep 1520909 = 570341) B570341
theorem B1520963 : Blo 447780 1520963 := bstep (se 1 (by rfl) ⟨1140722, by rfl⟩ : syracuseStep 1520963 = 2281445) B2281445
theorem B505219 : Blo 447780 505219 := bstep (se 1 (by rfl) ⟨378914, by rfl⟩ : syracuseStep 505219 = 757829) B757829
theorem B570883 : Blo 447780 570883 := bstep (se 1 (by rfl) ⟨428162, by rfl⟩ : syracuseStep 570883 = 856325) B856325
theorem B505363 : Blo 447780 505363 := bstep (se 1 (by rfl) ⟨379022, by rfl⟩ : syracuseStep 505363 = 758045) B758045
theorem B1914445 : Blo 447780 1914445 := bstep (se 3 (by rfl) ⟨358958, by rfl⟩ : syracuseStep 1914445 = 717917) B717917
theorem B1521233 : Blo 447780 1521233 := bstep (se 2 (by rfl) ⟨570462, by rfl⟩ : syracuseStep 1521233 = 1140925) B1140925
theorem B570979 : Blo 447780 570979 := bstep (se 1 (by rfl) ⟨428234, by rfl⟩ : syracuseStep 570979 = 856469) B856469
theorem B505507 : Blo 447780 505507 := bstep (se 1 (by rfl) ⟨379130, by rfl⟩ : syracuseStep 505507 = 758261) B758261
theorem B4601585 : Blo 447780 4601585 := bstep (se 2 (by rfl) ⟨1725594, by rfl⟩ : syracuseStep 4601585 = 3451189) B3451189
theorem B505651 : Blo 447780 505651 := bstep (se 1 (by rfl) ⟨379238, by rfl⟩ : syracuseStep 505651 = 758477) B758477
theorem B964433 : Blo 447780 964433 := bstep (se 2 (by rfl) ⟨361662, by rfl⟩ : syracuseStep 964433 = 723325) B723325
theorem B505795 : Blo 447780 505795 := bstep (se 1 (by rfl) ⟨379346, by rfl⟩ : syracuseStep 505795 = 758693) B758693
theorem B505939 : Blo 447780 505939 := bstep (se 1 (by rfl) ⟨379454, by rfl⟩ : syracuseStep 505939 = 758909) B758909
theorem B571475 : Blo 447780 571475 := bstep (se 1 (by rfl) ⟨428606, by rfl⟩ : syracuseStep 571475 = 857213) B857213
theorem B1521773 : Blo 447780 1521773 := bstep (se 3 (by rfl) ⟨285332, by rfl⟩ : syracuseStep 1521773 = 570665) B570665
theorem B1521827 : Blo 447780 1521827 := bstep (se 1 (by rfl) ⟨1141370, by rfl⟩ : syracuseStep 1521827 = 2282741) B2282741
theorem B506083 : Blo 447780 506083 := bstep (se 1 (by rfl) ⟨379562, by rfl⟩ : syracuseStep 506083 = 759125) B759125
theorem B506227 : Blo 447780 506227 := bstep (se 1 (by rfl) ⟨379670, by rfl⟩ : syracuseStep 506227 = 759341) B759341
theorem B1522097 : Blo 447780 1522097 := bstep (se 2 (by rfl) ⟨570786, by rfl⟩ : syracuseStep 1522097 = 1141573) B1141573
theorem B506371 : Blo 447780 506371 := bstep (se 1 (by rfl) ⟨379778, by rfl⟩ : syracuseStep 506371 = 759557) B759557
theorem B1292881 : Blo 447780 1292881 := bstep (se 2 (by rfl) ⟨484830, by rfl⟩ : syracuseStep 1292881 = 969661) B969661
theorem B506515 : Blo 447780 506515 := bstep (se 1 (by rfl) ⟨379886, by rfl⟩ : syracuseStep 506515 = 759773) B759773
theorem B506659 : Blo 447780 506659 := bstep (se 1 (by rfl) ⟨379994, by rfl⟩ : syracuseStep 506659 = 759989) B759989
theorem B637841 : Blo 447780 637841 := bstep (se 2 (by rfl) ⟨239190, by rfl⟩ : syracuseStep 637841 = 478381) B478381
theorem B506803 : Blo 447780 506803 := bstep (se 1 (by rfl) ⟨380102, by rfl⟩ : syracuseStep 506803 = 760205) B760205
theorem B1522637 : Blo 447780 1522637 := bstep (se 3 (by rfl) ⟨285494, by rfl⟩ : syracuseStep 1522637 = 570989) B570989
theorem B1522691 : Blo 447780 1522691 := bstep (se 1 (by rfl) ⟨1142018, by rfl⟩ : syracuseStep 1522691 = 2284037) B2284037
theorem B506947 : Blo 447780 506947 := bstep (se 1 (by rfl) ⟨380210, by rfl⟩ : syracuseStep 506947 = 760421) B760421
theorem B1457297 : Blo 447780 1457297 := bstep (se 2 (by rfl) ⟨546486, by rfl⟩ : syracuseStep 1457297 = 1092973) B1092973
theorem B507091 : Blo 447780 507091 := bstep (se 1 (by rfl) ⟨380318, by rfl⟩ : syracuseStep 507091 = 760637) B760637
theorem B1522961 : Blo 447780 1522961 := bstep (se 2 (by rfl) ⟨571110, by rfl⟩ : syracuseStep 1522961 = 1142221) B1142221
theorem B507235 : Blo 447780 507235 := bstep (se 1 (by rfl) ⟨380426, by rfl⟩ : syracuseStep 507235 = 760853) B760853
theorem B638371 : Blo 447780 638371 := bstep (se 1 (by rfl) ⟨478778, by rfl⟩ : syracuseStep 638371 = 957557) B957557
theorem B507379 : Blo 447780 507379 := bstep (se 1 (by rfl) ⟨380534, by rfl⟩ : syracuseStep 507379 = 761069) B761069
theorem B507523 : Blo 447780 507523 := bstep (se 1 (by rfl) ⟨380642, by rfl⟩ : syracuseStep 507523 = 761285) B761285
theorem B5750513 : Blo 447780 5750513 := bstep (se 2 (by rfl) ⟨2156442, by rfl⟩ : syracuseStep 5750513 = 4312885) B4312885
theorem B638707 : Blo 447780 638707 := bstep (se 1 (by rfl) ⟨479030, by rfl⟩ : syracuseStep 638707 = 958061) B958061
theorem B507667 : Blo 447780 507667 := bstep (se 1 (by rfl) ⟨380750, by rfl⟩ : syracuseStep 507667 = 761501) B761501
theorem B1523501 : Blo 447780 1523501 := bstep (se 3 (by rfl) ⟨285656, by rfl⟩ : syracuseStep 1523501 = 571313) B571313
theorem B2080561 : Blo 447780 2080561 := bstep (se 2 (by rfl) ⟨780210, by rfl⟩ : syracuseStep 2080561 = 1560421) B1560421
theorem B1523555 : Blo 447780 1523555 := bstep (se 1 (by rfl) ⟨1142666, by rfl⟩ : syracuseStep 1523555 = 2285333) B2285333
theorem B2277233 : Blo 447780 2277233 := bstep (se 2 (by rfl) ⟨853962, by rfl⟩ : syracuseStep 2277233 = 1707925) B1707925
theorem B507811 : Blo 447780 507811 := bstep (se 1 (by rfl) ⟨380858, by rfl⟩ : syracuseStep 507811 = 761717) B761717
theorem B2441137 : Blo 447780 2441137 := bstep (se 2 (by rfl) ⟨915426, by rfl⟩ : syracuseStep 2441137 = 1830853) B1830853
theorem B671681 : Blo 447780 671681 := bstep (se 2 (by rfl) ⟨251880, by rfl⟩ : syracuseStep 671681 = 503761) B503761
theorem B671699 : Blo 447780 671699 := bstep (se 1 (by rfl) ⟨503774, by rfl⟩ : syracuseStep 671699 = 1007549) B1007549
theorem B671729 : Blo 447780 671729 := bstep (se 2 (by rfl) ⟨251898, by rfl⟩ : syracuseStep 671729 = 503797) B503797
theorem B671747 : Blo 447780 671747 := bstep (se 1 (by rfl) ⟨503810, by rfl⟩ : syracuseStep 671747 = 1007621) B1007621
theorem B671777 : Blo 447780 671777 := bstep (se 2 (by rfl) ⟨251916, by rfl⟩ : syracuseStep 671777 = 503833) B503833
theorem B606241 : Blo 447780 606241 := bstep (se 2 (by rfl) ⟨227340, by rfl⟩ : syracuseStep 606241 = 454681) B454681
theorem B671795 : Blo 447780 671795 := bstep (se 1 (by rfl) ⟨503846, by rfl⟩ : syracuseStep 671795 = 1007693) B1007693
theorem B507955 : Blo 447780 507955 := bstep (se 1 (by rfl) ⟨380966, by rfl⟩ : syracuseStep 507955 = 761933) B761933
theorem B671825 : Blo 447780 671825 := bstep (se 2 (by rfl) ⟨251934, by rfl⟩ : syracuseStep 671825 = 503869) B503869
theorem B671843 : Blo 447780 671843 := bstep (se 1 (by rfl) ⟨503882, by rfl⟩ : syracuseStep 671843 = 1007765) B1007765
theorem B3424355 : Blo 447780 3424355 := bstep (se 1 (by rfl) ⟨2568266, by rfl⟩ : syracuseStep 3424355 = 5136533) B5136533
theorem B1523825 : Blo 447780 1523825 := bstep (se 2 (by rfl) ⟨571434, by rfl⟩ : syracuseStep 1523825 = 1142869) B1142869
theorem B671873 : Blo 447780 671873 := bstep (se 2 (by rfl) ⟨251952, by rfl⟩ : syracuseStep 671873 = 503905) B503905
theorem B671891 : Blo 447780 671891 := bstep (se 1 (by rfl) ⟨503918, by rfl⟩ : syracuseStep 671891 = 1007837) B1007837
theorem B1818787 : Blo 447780 1818787 := bstep (se 1 (by rfl) ⟨1364090, by rfl⟩ : syracuseStep 1818787 = 2728181) B2728181
theorem B671921 : Blo 447780 671921 := bstep (se 2 (by rfl) ⟨251970, by rfl⟩ : syracuseStep 671921 = 503941) B503941
theorem B671939 : Blo 447780 671939 := bstep (se 1 (by rfl) ⟨503954, by rfl⟩ : syracuseStep 671939 = 1007909) B1007909
theorem B606403 : Blo 447780 606403 := bstep (se 1 (by rfl) ⟨454802, by rfl⟩ : syracuseStep 606403 = 909605) B909605
theorem B508099 : Blo 447780 508099 := bstep (se 1 (by rfl) ⟨381074, by rfl⟩ : syracuseStep 508099 = 762149) B762149
theorem B671969 : Blo 447780 671969 := bstep (se 2 (by rfl) ⟨251988, by rfl⟩ : syracuseStep 671969 = 503977) B503977
theorem B671987 : Blo 447780 671987 := bstep (se 1 (by rfl) ⟨503990, by rfl⟩ : syracuseStep 671987 = 1007981) B1007981
theorem B770305 : Blo 447780 770305 := bstep (se 2 (by rfl) ⟨288864, by rfl⟩ : syracuseStep 770305 = 577729) B577729
theorem B4866317 : Blo 447780 4866317 := bstep (se 3 (by rfl) ⟨912434, by rfl⟩ : syracuseStep 4866317 = 1824869) B1824869
theorem B672017 : Blo 447780 672017 := bstep (se 2 (by rfl) ⟨252006, by rfl⟩ : syracuseStep 672017 = 504013) B504013
theorem B639265 : Blo 447780 639265 := bstep (se 2 (by rfl) ⟨239724, by rfl⟩ : syracuseStep 639265 = 479449) B479449
theorem B672035 : Blo 447780 672035 := bstep (se 1 (by rfl) ⟨504026, by rfl⟩ : syracuseStep 672035 = 1008053) B1008053
theorem B9716021 : Blo 447780 9716021 := bstep (se 5 (by rfl) ⟨455438, by rfl⟩ : syracuseStep 9716021 = 910877) B910877
theorem B672065 : Blo 447780 672065 := bstep (se 2 (by rfl) ⟨252024, by rfl⟩ : syracuseStep 672065 = 504049) B504049
theorem B639299 : Blo 447780 639299 := bstep (se 1 (by rfl) ⟨479474, by rfl⟩ : syracuseStep 639299 = 958949) B958949
theorem B672083 : Blo 447780 672083 := bstep (se 1 (by rfl) ⟨504062, by rfl⟩ : syracuseStep 672083 = 1008125) B1008125
theorem B508243 : Blo 447780 508243 := bstep (se 1 (by rfl) ⟨381182, by rfl⟩ : syracuseStep 508243 = 762365) B762365
theorem B672113 : Blo 447780 672113 := bstep (se 2 (by rfl) ⟨252042, by rfl⟩ : syracuseStep 672113 = 504085) B504085
theorem B672131 : Blo 447780 672131 := bstep (se 1 (by rfl) ⟨504098, by rfl⟩ : syracuseStep 672131 = 1008197) B1008197
theorem B672161 : Blo 447780 672161 := bstep (se 2 (by rfl) ⟨252060, by rfl⟩ : syracuseStep 672161 = 504121) B504121
theorem B672179 : Blo 447780 672179 := bstep (se 1 (by rfl) ⟨504134, by rfl⟩ : syracuseStep 672179 = 1008269) B1008269
theorem B672209 : Blo 447780 672209 := bstep (se 2 (by rfl) ⟨252078, by rfl⟩ : syracuseStep 672209 = 504157) B504157
theorem B672227 : Blo 447780 672227 := bstep (se 1 (by rfl) ⟨504170, by rfl⟩ : syracuseStep 672227 = 1008341) B1008341
theorem B672257 : Blo 447780 672257 := bstep (se 2 (by rfl) ⟨252096, by rfl⟩ : syracuseStep 672257 = 504193) B504193
theorem B672275 : Blo 447780 672275 := bstep (se 1 (by rfl) ⟨504206, by rfl⟩ : syracuseStep 672275 = 1008413) B1008413
theorem B672305 : Blo 447780 672305 := bstep (se 2 (by rfl) ⟨252114, by rfl⟩ : syracuseStep 672305 = 504229) B504229
theorem B672323 : Blo 447780 672323 := bstep (se 1 (by rfl) ⟨504242, by rfl⟩ : syracuseStep 672323 = 1008485) B1008485
theorem B672353 : Blo 447780 672353 := bstep (se 2 (by rfl) ⟨252132, by rfl⟩ : syracuseStep 672353 = 504265) B504265
theorem B672371 : Blo 447780 672371 := bstep (se 1 (by rfl) ⟨504278, by rfl⟩ : syracuseStep 672371 = 1008557) B1008557
theorem B1524365 : Blo 447780 1524365 := bstep (se 3 (by rfl) ⟨285818, by rfl⟩ : syracuseStep 1524365 = 571637) B571637
theorem B672401 : Blo 447780 672401 := bstep (se 2 (by rfl) ⟨252150, by rfl⟩ : syracuseStep 672401 = 504301) B504301
theorem B672419 : Blo 447780 672419 := bstep (se 1 (by rfl) ⟨504314, by rfl⟩ : syracuseStep 672419 = 1008629) B1008629
theorem B672449 : Blo 447780 672449 := bstep (se 2 (by rfl) ⟨252168, by rfl⟩ : syracuseStep 672449 = 504337) B504337
theorem B1524419 : Blo 447780 1524419 := bstep (se 1 (by rfl) ⟨1143314, by rfl⟩ : syracuseStep 1524419 = 2286629) B2286629
theorem B2573005 : Blo 447780 2573005 := bstep (se 3 (by rfl) ⟨482438, by rfl⟩ : syracuseStep 2573005 = 964877) B964877
theorem B672467 : Blo 447780 672467 := bstep (se 1 (by rfl) ⟨504350, by rfl⟩ : syracuseStep 672467 = 1008701) B1008701
theorem B672497 : Blo 447780 672497 := bstep (se 2 (by rfl) ⟨252186, by rfl⟩ : syracuseStep 672497 = 504373) B504373
theorem B672515 : Blo 447780 672515 := bstep (se 1 (by rfl) ⟨504386, by rfl⟩ : syracuseStep 672515 = 1008773) B1008773
theorem B1557265 : Blo 447780 1557265 := bstep (se 2 (by rfl) ⟨583974, by rfl⟩ : syracuseStep 1557265 = 1167949) B1167949
theorem B672545 : Blo 447780 672545 := bstep (se 2 (by rfl) ⟨252204, by rfl⟩ : syracuseStep 672545 = 504409) B504409
theorem B607009 : Blo 447780 607009 := bstep (se 2 (by rfl) ⟨227628, by rfl⟩ : syracuseStep 607009 = 455257) B455257
theorem B672563 : Blo 447780 672563 := bstep (se 1 (by rfl) ⟨504422, by rfl⟩ : syracuseStep 672563 = 1008845) B1008845
theorem B672593 : Blo 447780 672593 := bstep (se 2 (by rfl) ⟨252222, by rfl⟩ : syracuseStep 672593 = 504445) B504445
theorem B672611 : Blo 447780 672611 := bstep (se 1 (by rfl) ⟨504458, by rfl⟩ : syracuseStep 672611 = 1008917) B1008917
theorem B639857 : Blo 447780 639857 := bstep (se 2 (by rfl) ⟨239946, by rfl⟩ : syracuseStep 639857 = 479893) B479893
theorem B672641 : Blo 447780 672641 := bstep (se 2 (by rfl) ⟨252240, by rfl⟩ : syracuseStep 672641 = 504481) B504481
theorem B541571 : Blo 447780 541571 := bstep (se 1 (by rfl) ⟨406178, by rfl⟩ : syracuseStep 541571 = 812357) B812357
theorem B672659 : Blo 447780 672659 := bstep (se 1 (by rfl) ⟨504494, by rfl⟩ : syracuseStep 672659 = 1008989) B1008989
theorem B770963 : Blo 447780 770963 := bstep (se 1 (by rfl) ⟨578222, by rfl⟩ : syracuseStep 770963 = 1156445) B1156445
theorem B672689 : Blo 447780 672689 := bstep (se 2 (by rfl) ⟨252258, by rfl⟩ : syracuseStep 672689 = 504517) B504517
theorem B639937 : Blo 447780 639937 := bstep (se 2 (by rfl) ⟨239976, by rfl⟩ : syracuseStep 639937 = 479953) B479953
theorem B672707 : Blo 447780 672707 := bstep (se 1 (by rfl) ⟨504530, by rfl⟩ : syracuseStep 672707 = 1009061) B1009061
theorem B1524689 : Blo 447780 1524689 := bstep (se 2 (by rfl) ⟨571758, by rfl⟩ : syracuseStep 1524689 = 1143517) B1143517
theorem B672737 : Blo 447780 672737 := bstep (se 2 (by rfl) ⟨252276, by rfl⟩ : syracuseStep 672737 = 504553) B504553
theorem B672755 : Blo 447780 672755 := bstep (se 1 (by rfl) ⟨504566, by rfl⟩ : syracuseStep 672755 = 1009133) B1009133
theorem B672785 : Blo 447780 672785 := bstep (se 2 (by rfl) ⟨252294, by rfl⟩ : syracuseStep 672785 = 504589) B504589
theorem B672803 : Blo 447780 672803 := bstep (se 1 (by rfl) ⟨504602, by rfl⟩ : syracuseStep 672803 = 1009205) B1009205
theorem B672833 : Blo 447780 672833 := bstep (se 2 (by rfl) ⟨252312, by rfl⟩ : syracuseStep 672833 = 504625) B504625
theorem B672851 : Blo 447780 672851 := bstep (se 1 (by rfl) ⟨504638, by rfl⟩ : syracuseStep 672851 = 1009277) B1009277
theorem B672881 : Blo 447780 672881 := bstep (se 2 (by rfl) ⟨252330, by rfl⟩ : syracuseStep 672881 = 504661) B504661
theorem B672899 : Blo 447780 672899 := bstep (se 1 (by rfl) ⟨504674, by rfl⟩ : syracuseStep 672899 = 1009349) B1009349
theorem B672929 : Blo 447780 672929 := bstep (se 2 (by rfl) ⟨252348, by rfl⟩ : syracuseStep 672929 = 504697) B504697
theorem B672947 : Blo 447780 672947 := bstep (se 1 (by rfl) ⟨504710, by rfl⟩ : syracuseStep 672947 = 1009421) B1009421
theorem B672977 : Blo 447780 672977 := bstep (se 2 (by rfl) ⟨252366, by rfl⟩ : syracuseStep 672977 = 504733) B504733
theorem B672995 : Blo 447780 672995 := bstep (se 1 (by rfl) ⟨504746, by rfl⟩ : syracuseStep 672995 = 1009493) B1009493
theorem B673025 : Blo 447780 673025 := bstep (se 2 (by rfl) ⟨252384, by rfl⟩ : syracuseStep 673025 = 504769) B504769
theorem B673043 : Blo 447780 673043 := bstep (se 1 (by rfl) ⟨504782, by rfl⟩ : syracuseStep 673043 = 1009565) B1009565
theorem B2278691 : Blo 447780 2278691 := bstep (se 1 (by rfl) ⟨1709018, by rfl⟩ : syracuseStep 2278691 = 3418037) B3418037
theorem B673073 : Blo 447780 673073 := bstep (se 2 (by rfl) ⟨252402, by rfl⟩ : syracuseStep 673073 = 504805) B504805
theorem B673091 : Blo 447780 673091 := bstep (se 1 (by rfl) ⟨504818, by rfl⟩ : syracuseStep 673091 = 1009637) B1009637
theorem B673121 : Blo 447780 673121 := bstep (se 2 (by rfl) ⟨252420, by rfl⟩ : syracuseStep 673121 = 504841) B504841
theorem B673139 : Blo 447780 673139 := bstep (se 1 (by rfl) ⟨504854, by rfl⟩ : syracuseStep 673139 = 1009709) B1009709
theorem B607603 : Blo 447780 607603 := bstep (se 1 (by rfl) ⟨455702, by rfl⟩ : syracuseStep 607603 = 911405) B911405
theorem B673169 : Blo 447780 673169 := bstep (se 2 (by rfl) ⟨252438, by rfl⟩ : syracuseStep 673169 = 504877) B504877
theorem B673187 : Blo 447780 673187 := bstep (se 1 (by rfl) ⟨504890, by rfl⟩ : syracuseStep 673187 = 1009781) B1009781
theorem B673217 : Blo 447780 673217 := bstep (se 2 (by rfl) ⟨252456, by rfl⟩ : syracuseStep 673217 = 504913) B504913
theorem B673235 : Blo 447780 673235 := bstep (se 1 (by rfl) ⟨504926, by rfl⟩ : syracuseStep 673235 = 1009853) B1009853
theorem B673265 : Blo 447780 673265 := bstep (se 2 (by rfl) ⟨252474, by rfl⟩ : syracuseStep 673265 = 504949) B504949
theorem B1263107 : Blo 447780 1263107 := bstep (se 1 (by rfl) ⟨947330, by rfl⟩ : syracuseStep 1263107 = 1894661) B1894661
theorem B673283 : Blo 447780 673283 := bstep (se 1 (by rfl) ⟨504962, by rfl⟩ : syracuseStep 673283 = 1009925) B1009925
theorem B673313 : Blo 447780 673313 := bstep (se 2 (by rfl) ⟨252492, by rfl⟩ : syracuseStep 673313 = 504985) B504985
theorem B673331 : Blo 447780 673331 := bstep (se 1 (by rfl) ⟨504998, by rfl⟩ : syracuseStep 673331 = 1009997) B1009997
theorem B673361 : Blo 447780 673361 := bstep (se 2 (by rfl) ⟨252510, by rfl⟩ : syracuseStep 673361 = 505021) B505021
theorem B673379 : Blo 447780 673379 := bstep (se 1 (by rfl) ⟨505034, by rfl⟩ : syracuseStep 673379 = 1010069) B1010069
theorem B673409 : Blo 447780 673409 := bstep (se 2 (by rfl) ⟨252528, by rfl⟩ : syracuseStep 673409 = 505057) B505057
theorem B673427 : Blo 447780 673427 := bstep (se 1 (by rfl) ⟨505070, by rfl⟩ : syracuseStep 673427 = 1010141) B1010141
theorem B673457 : Blo 447780 673457 := bstep (se 2 (by rfl) ⟨252546, by rfl⟩ : syracuseStep 673457 = 505093) B505093
theorem B673475 : Blo 447780 673475 := bstep (se 1 (by rfl) ⟨505106, by rfl⟩ : syracuseStep 673475 = 1010213) B1010213
theorem B640723 : Blo 447780 640723 := bstep (se 1 (by rfl) ⟨480542, by rfl⟩ : syracuseStep 640723 = 961085) B961085
theorem B673505 : Blo 447780 673505 := bstep (se 2 (by rfl) ⟨252564, by rfl⟩ : syracuseStep 673505 = 505129) B505129
theorem B673523 : Blo 447780 673523 := bstep (se 1 (by rfl) ⟨505142, by rfl⟩ : syracuseStep 673523 = 1010285) B1010285
theorem B673553 : Blo 447780 673553 := bstep (se 2 (by rfl) ⟨252582, by rfl⟩ : syracuseStep 673553 = 505165) B505165
theorem B673571 : Blo 447780 673571 := bstep (se 1 (by rfl) ⟨505178, by rfl⟩ : syracuseStep 673571 = 1010357) B1010357
theorem B673601 : Blo 447780 673601 := bstep (se 2 (by rfl) ⟨252600, by rfl⟩ : syracuseStep 673601 = 505201) B505201
theorem B673619 : Blo 447780 673619 := bstep (se 1 (by rfl) ⟨505214, by rfl⟩ : syracuseStep 673619 = 1010429) B1010429
theorem B1918819 : Blo 447780 1918819 := bstep (se 1 (by rfl) ⟨1439114, by rfl⟩ : syracuseStep 1918819 = 2878229) B2878229
theorem B673649 : Blo 447780 673649 := bstep (se 2 (by rfl) ⟨252618, by rfl⟩ : syracuseStep 673649 = 505237) B505237
theorem B673667 : Blo 447780 673667 := bstep (se 1 (by rfl) ⟨505250, by rfl⟩ : syracuseStep 673667 = 1010501) B1010501
theorem B673697 : Blo 447780 673697 := bstep (se 2 (by rfl) ⟨252636, by rfl⟩ : syracuseStep 673697 = 505273) B505273
theorem B2738083 : Blo 447780 2738083 := bstep (se 1 (by rfl) ⟨2053562, by rfl⟩ : syracuseStep 2738083 = 4107125) B4107125
theorem B673715 : Blo 447780 673715 := bstep (se 1 (by rfl) ⟨505286, by rfl⟩ : syracuseStep 673715 = 1010573) B1010573
theorem B673745 : Blo 447780 673745 := bstep (se 2 (by rfl) ⟨252654, by rfl⟩ : syracuseStep 673745 = 505309) B505309
theorem B673763 : Blo 447780 673763 := bstep (se 1 (by rfl) ⟨505322, by rfl⟩ : syracuseStep 673763 = 1010645) B1010645
theorem B673793 : Blo 447780 673793 := bstep (se 2 (by rfl) ⟨252672, by rfl⟩ : syracuseStep 673793 = 505345) B505345
theorem B673811 : Blo 447780 673811 := bstep (se 1 (by rfl) ⟨505358, by rfl⟩ : syracuseStep 673811 = 1010717) B1010717
theorem B673841 : Blo 447780 673841 := bstep (se 2 (by rfl) ⟨252690, by rfl⟩ : syracuseStep 673841 = 505381) B505381
theorem B673859 : Blo 447780 673859 := bstep (se 1 (by rfl) ⟨505394, by rfl⟩ : syracuseStep 673859 = 1010789) B1010789
theorem B2279501 : Blo 447780 2279501 := bstep (se 3 (by rfl) ⟨427406, by rfl⟩ : syracuseStep 2279501 = 854813) B854813
theorem B673889 : Blo 447780 673889 := bstep (se 2 (by rfl) ⟨252708, by rfl⟩ : syracuseStep 673889 = 505417) B505417
theorem B673907 : Blo 447780 673907 := bstep (se 1 (by rfl) ⟨505430, by rfl⟩ : syracuseStep 673907 = 1010861) B1010861
theorem B2312333 : Blo 447780 2312333 := bstep (se 3 (by rfl) ⟨433562, by rfl⟩ : syracuseStep 2312333 = 867125) B867125
theorem B673937 : Blo 447780 673937 := bstep (se 2 (by rfl) ⟨252726, by rfl⟩ : syracuseStep 673937 = 505453) B505453
theorem B673955 : Blo 447780 673955 := bstep (se 1 (by rfl) ⟨505466, by rfl⟩ : syracuseStep 673955 = 1010933) B1010933
theorem B641201 : Blo 447780 641201 := bstep (se 2 (by rfl) ⟨240450, by rfl⟩ : syracuseStep 641201 = 480901) B480901
theorem B673985 : Blo 447780 673985 := bstep (se 2 (by rfl) ⟨252744, by rfl⟩ : syracuseStep 673985 = 505489) B505489
theorem B674003 : Blo 447780 674003 := bstep (se 1 (by rfl) ⟨505502, by rfl⟩ : syracuseStep 674003 = 1011005) B1011005
theorem B1231085 : Blo 447780 1231085 := bstep (se 3 (by rfl) ⟨230828, by rfl⟩ : syracuseStep 1231085 = 461657) B461657
theorem B674033 : Blo 447780 674033 := bstep (se 2 (by rfl) ⟨252762, by rfl⟩ : syracuseStep 674033 = 505525) B505525
theorem B674051 : Blo 447780 674051 := bstep (se 1 (by rfl) ⟨505538, by rfl⟩ : syracuseStep 674051 = 1011077) B1011077
theorem B674081 : Blo 447780 674081 := bstep (se 2 (by rfl) ⟨252780, by rfl⟩ : syracuseStep 674081 = 505561) B505561
theorem B641315 : Blo 447780 641315 := bstep (se 1 (by rfl) ⟨480986, by rfl⟩ : syracuseStep 641315 = 961973) B961973
theorem B674099 : Blo 447780 674099 := bstep (se 1 (by rfl) ⟨505574, by rfl⟩ : syracuseStep 674099 = 1011149) B1011149
theorem B674129 : Blo 447780 674129 := bstep (se 2 (by rfl) ⟨252798, by rfl⟩ : syracuseStep 674129 = 505597) B505597
theorem B674147 : Blo 447780 674147 := bstep (se 1 (by rfl) ⟨505610, by rfl⟩ : syracuseStep 674147 = 1011221) B1011221
theorem B641395 : Blo 447780 641395 := bstep (se 1 (by rfl) ⟨481046, by rfl⟩ : syracuseStep 641395 = 962093) B962093
theorem B674177 : Blo 447780 674177 := bstep (se 2 (by rfl) ⟨252816, by rfl⟩ : syracuseStep 674177 = 505633) B505633
theorem B674195 : Blo 447780 674195 := bstep (se 1 (by rfl) ⟨505646, by rfl⟩ : syracuseStep 674195 = 1011293) B1011293
theorem B674225 : Blo 447780 674225 := bstep (se 2 (by rfl) ⟨252834, by rfl⟩ : syracuseStep 674225 = 505669) B505669
theorem B6244789 : Blo 447780 6244789 := bstep (se 5 (by rfl) ⟨292724, by rfl⟩ : syracuseStep 6244789 = 585449) B585449
theorem B674243 : Blo 447780 674243 := bstep (se 1 (by rfl) ⟨505682, by rfl⟩ : syracuseStep 674243 = 1011365) B1011365
theorem B674273 : Blo 447780 674273 := bstep (se 2 (by rfl) ⟨252852, by rfl⟩ : syracuseStep 674273 = 505705) B505705
theorem B674291 : Blo 447780 674291 := bstep (se 1 (by rfl) ⟨505718, by rfl⟩ : syracuseStep 674291 = 1011437) B1011437
theorem B674321 : Blo 447780 674321 := bstep (se 2 (by rfl) ⟨252870, by rfl⟩ : syracuseStep 674321 = 505741) B505741
theorem B674339 : Blo 447780 674339 := bstep (se 1 (by rfl) ⟨505754, by rfl⟩ : syracuseStep 674339 = 1011509) B1011509
theorem B674369 : Blo 447780 674369 := bstep (se 2 (by rfl) ⟨252888, by rfl⟩ : syracuseStep 674369 = 505777) B505777
theorem B674387 : Blo 447780 674387 := bstep (se 1 (by rfl) ⟨505790, by rfl⟩ : syracuseStep 674387 = 1011581) B1011581
theorem B674417 : Blo 447780 674417 := bstep (se 2 (by rfl) ⟨252906, by rfl⟩ : syracuseStep 674417 = 505813) B505813
theorem B674435 : Blo 447780 674435 := bstep (se 1 (by rfl) ⟨505826, by rfl⟩ : syracuseStep 674435 = 1011653) B1011653
theorem B674465 : Blo 447780 674465 := bstep (se 2 (by rfl) ⟨252924, by rfl⟩ : syracuseStep 674465 = 505849) B505849
theorem B674483 : Blo 447780 674483 := bstep (se 1 (by rfl) ⟨505862, by rfl⟩ : syracuseStep 674483 = 1011725) B1011725
theorem B674513 : Blo 447780 674513 := bstep (se 2 (by rfl) ⟨252942, by rfl⟩ : syracuseStep 674513 = 505885) B505885
theorem B674531 : Blo 447780 674531 := bstep (se 1 (by rfl) ⟨505898, by rfl⟩ : syracuseStep 674531 = 1011797) B1011797
theorem B674561 : Blo 447780 674561 := bstep (se 2 (by rfl) ⟨252960, by rfl⟩ : syracuseStep 674561 = 505921) B505921
theorem B674579 : Blo 447780 674579 := bstep (se 1 (by rfl) ⟨505934, by rfl⟩ : syracuseStep 674579 = 1011869) B1011869
theorem B42257173 : Blo 447780 42257173 := bstep (se 6 (by rfl) ⟨990402, by rfl⟩ : syracuseStep 42257173 = 1980805) B1980805
theorem B674609 : Blo 447780 674609 := bstep (se 2 (by rfl) ⟨252978, by rfl⟩ : syracuseStep 674609 = 505957) B505957
theorem B674627 : Blo 447780 674627 := bstep (se 1 (by rfl) ⟨505970, by rfl⟩ : syracuseStep 674627 = 1011941) B1011941
theorem B674657 : Blo 447780 674657 := bstep (se 2 (by rfl) ⟨252996, by rfl⟩ : syracuseStep 674657 = 505993) B505993
theorem B674675 : Blo 447780 674675 := bstep (se 1 (by rfl) ⟨506006, by rfl⟩ : syracuseStep 674675 = 1012013) B1012013
theorem B674705 : Blo 447780 674705 := bstep (se 2 (by rfl) ⟨253014, by rfl⟩ : syracuseStep 674705 = 506029) B506029
theorem B641953 : Blo 447780 641953 := bstep (se 2 (by rfl) ⟨240732, by rfl⟩ : syracuseStep 641953 = 481465) B481465
theorem B674723 : Blo 447780 674723 := bstep (se 1 (by rfl) ⟨506042, by rfl⟩ : syracuseStep 674723 = 1012085) B1012085
theorem B674753 : Blo 447780 674753 := bstep (se 2 (by rfl) ⟨253032, by rfl⟩ : syracuseStep 674753 = 506065) B506065
theorem B674771 : Blo 447780 674771 := bstep (se 1 (by rfl) ⟨506078, by rfl⟩ : syracuseStep 674771 = 1012157) B1012157
theorem B674801 : Blo 447780 674801 := bstep (se 2 (by rfl) ⟨253050, by rfl⟩ : syracuseStep 674801 = 506101) B506101
theorem B674819 : Blo 447780 674819 := bstep (se 1 (by rfl) ⟨506114, by rfl⟩ : syracuseStep 674819 = 1012229) B1012229
theorem B1133585 : Blo 447780 1133585 := bstep (se 2 (by rfl) ⟨425094, by rfl⟩ : syracuseStep 1133585 = 850189) B850189
theorem B674849 : Blo 447780 674849 := bstep (se 2 (by rfl) ⟨253068, by rfl⟩ : syracuseStep 674849 = 506137) B506137
theorem B674867 : Blo 447780 674867 := bstep (se 1 (by rfl) ⟨506150, by rfl⟩ : syracuseStep 674867 = 1012301) B1012301
theorem B1133635 : Blo 447780 1133635 := bstep (se 1 (by rfl) ⟨850226, by rfl⟩ : syracuseStep 1133635 = 1700453) B1700453
theorem B674897 : Blo 447780 674897 := bstep (se 2 (by rfl) ⟨253086, by rfl⟩ : syracuseStep 674897 = 506173) B506173
theorem B674915 : Blo 447780 674915 := bstep (se 1 (by rfl) ⟨506186, by rfl⟩ : syracuseStep 674915 = 1012373) B1012373
theorem B674945 : Blo 447780 674945 := bstep (se 2 (by rfl) ⟨253104, by rfl⟩ : syracuseStep 674945 = 506209) B506209
theorem B674963 : Blo 447780 674963 := bstep (se 1 (by rfl) ⟨506222, by rfl⟩ : syracuseStep 674963 = 1012445) B1012445
theorem B674993 : Blo 447780 674993 := bstep (se 2 (by rfl) ⟨253122, by rfl⟩ : syracuseStep 674993 = 506245) B506245
theorem B675011 : Blo 447780 675011 := bstep (se 1 (by rfl) ⟨506258, by rfl⟩ : syracuseStep 675011 = 1012517) B1012517
theorem B1133777 : Blo 447780 1133777 := bstep (se 2 (by rfl) ⟨425166, by rfl⟩ : syracuseStep 1133777 = 850333) B850333
theorem B675041 : Blo 447780 675041 := bstep (se 2 (by rfl) ⟨253140, by rfl⟩ : syracuseStep 675041 = 506281) B506281
theorem B675059 : Blo 447780 675059 := bstep (se 1 (by rfl) ⟨506294, by rfl⟩ : syracuseStep 675059 = 1012589) B1012589
theorem B1232131 : Blo 447780 1232131 := bstep (se 1 (by rfl) ⟨924098, by rfl⟩ : syracuseStep 1232131 = 1848197) B1848197
theorem B675089 : Blo 447780 675089 := bstep (se 2 (by rfl) ⟨253158, by rfl⟩ : syracuseStep 675089 = 506317) B506317
theorem B675107 : Blo 447780 675107 := bstep (se 1 (by rfl) ⟨506330, by rfl⟩ : syracuseStep 675107 = 1012661) B1012661
theorem B675137 : Blo 447780 675137 := bstep (se 2 (by rfl) ⟨253176, by rfl⟩ : syracuseStep 675137 = 506353) B506353
theorem B675155 : Blo 447780 675155 := bstep (se 1 (by rfl) ⟨506366, by rfl⟩ : syracuseStep 675155 = 1012733) B1012733
theorem B675185 : Blo 447780 675185 := bstep (se 2 (by rfl) ⟨253194, by rfl⟩ : syracuseStep 675185 = 506389) B506389
theorem B675203 : Blo 447780 675203 := bstep (se 1 (by rfl) ⟨506402, by rfl⟩ : syracuseStep 675203 = 1012805) B1012805
theorem B675233 : Blo 447780 675233 := bstep (se 2 (by rfl) ⟨253212, by rfl⟩ : syracuseStep 675233 = 506425) B506425
theorem B675251 : Blo 447780 675251 := bstep (se 1 (by rfl) ⟨506438, by rfl⟩ : syracuseStep 675251 = 1012877) B1012877
theorem B675281 : Blo 447780 675281 := bstep (se 2 (by rfl) ⟨253230, by rfl⟩ : syracuseStep 675281 = 506461) B506461
theorem B675299 : Blo 447780 675299 := bstep (se 1 (by rfl) ⟨506474, by rfl⟩ : syracuseStep 675299 = 1012949) B1012949
theorem B675329 : Blo 447780 675329 := bstep (se 2 (by rfl) ⟨253248, by rfl⟩ : syracuseStep 675329 = 506497) B506497
theorem B675347 : Blo 447780 675347 := bstep (se 1 (by rfl) ⟨506510, by rfl⟩ : syracuseStep 675347 = 1013021) B1013021
theorem B675377 : Blo 447780 675377 := bstep (se 2 (by rfl) ⟨253266, by rfl⟩ : syracuseStep 675377 = 506533) B506533
theorem B1756721 : Blo 447780 1756721 := bstep (se 2 (by rfl) ⟨658770, by rfl⟩ : syracuseStep 1756721 = 1317541) B1317541
theorem B675395 : Blo 447780 675395 := bstep (se 1 (by rfl) ⟨506546, by rfl⟩ : syracuseStep 675395 = 1013093) B1013093
theorem B675425 : Blo 447780 675425 := bstep (se 2 (by rfl) ⟨253284, by rfl⟩ : syracuseStep 675425 = 506569) B506569
theorem B642659 : Blo 447780 642659 := bstep (se 1 (by rfl) ⟨481994, by rfl⟩ : syracuseStep 642659 = 963989) B963989
theorem B675443 : Blo 447780 675443 := bstep (se 1 (by rfl) ⟨506582, by rfl⟩ : syracuseStep 675443 = 1013165) B1013165
theorem B675473 : Blo 447780 675473 := bstep (se 2 (by rfl) ⟨253302, by rfl⟩ : syracuseStep 675473 = 506605) B506605
theorem B675491 : Blo 447780 675491 := bstep (se 1 (by rfl) ⟨506618, by rfl⟩ : syracuseStep 675491 = 1013237) B1013237
theorem B675521 : Blo 447780 675521 := bstep (se 2 (by rfl) ⟨253320, by rfl⟩ : syracuseStep 675521 = 506641) B506641
theorem B511699 : Blo 447780 511699 := bstep (se 1 (by rfl) ⟨383774, by rfl⟩ : syracuseStep 511699 = 767549) B767549
theorem B675539 : Blo 447780 675539 := bstep (se 1 (by rfl) ⟨506654, by rfl⟩ : syracuseStep 675539 = 1013309) B1013309
theorem B675569 : Blo 447780 675569 := bstep (se 2 (by rfl) ⟨253338, by rfl⟩ : syracuseStep 675569 = 506677) B506677
theorem B675587 : Blo 447780 675587 := bstep (se 1 (by rfl) ⟨506690, by rfl⟩ : syracuseStep 675587 = 1013381) B1013381
theorem B675617 : Blo 447780 675617 := bstep (se 2 (by rfl) ⟨253356, by rfl⟩ : syracuseStep 675617 = 506713) B506713
theorem B675635 : Blo 447780 675635 := bstep (se 1 (by rfl) ⟨506726, by rfl⟩ : syracuseStep 675635 = 1013453) B1013453
theorem B675665 : Blo 447780 675665 := bstep (se 2 (by rfl) ⟨253374, by rfl⟩ : syracuseStep 675665 = 506749) B506749
theorem B675683 : Blo 447780 675683 := bstep (se 1 (by rfl) ⟨506762, by rfl⟩ : syracuseStep 675683 = 1013525) B1013525
theorem B2084707 : Blo 447780 2084707 := bstep (se 1 (by rfl) ⟨1563530, by rfl⟩ : syracuseStep 2084707 = 3127061) B3127061
theorem B675713 : Blo 447780 675713 := bstep (se 2 (by rfl) ⟨253392, by rfl⟩ : syracuseStep 675713 = 506785) B506785
theorem B675731 : Blo 447780 675731 := bstep (se 1 (by rfl) ⟨506798, by rfl⟩ : syracuseStep 675731 = 1013597) B1013597
theorem B675761 : Blo 447780 675761 := bstep (se 2 (by rfl) ⟨253410, by rfl⟩ : syracuseStep 675761 = 506821) B506821
theorem B675779 : Blo 447780 675779 := bstep (se 1 (by rfl) ⟨506834, by rfl⟩ : syracuseStep 675779 = 1013669) B1013669
theorem B675809 : Blo 447780 675809 := bstep (se 2 (by rfl) ⟨253428, by rfl⟩ : syracuseStep 675809 = 506857) B506857
theorem B675827 : Blo 447780 675827 := bstep (se 1 (by rfl) ⟨506870, by rfl⟩ : syracuseStep 675827 = 1013741) B1013741
theorem B2740229 : Blo 447780 2740229 := bstep (se 4 (by rfl) ⟨256896, by rfl⟩ : syracuseStep 2740229 = 513793) B513793
theorem B675857 : Blo 447780 675857 := bstep (se 2 (by rfl) ⟨253446, by rfl⟩ : syracuseStep 675857 = 506893) B506893
theorem B675875 : Blo 447780 675875 := bstep (se 1 (by rfl) ⟨506906, by rfl⟩ : syracuseStep 675875 = 1013813) B1013813
theorem B675905 : Blo 447780 675905 := bstep (se 2 (by rfl) ⟨253464, by rfl⟩ : syracuseStep 675905 = 506929) B506929
theorem B675923 : Blo 447780 675923 := bstep (se 1 (by rfl) ⟨506942, by rfl⟩ : syracuseStep 675923 = 1013885) B1013885
theorem B675953 : Blo 447780 675953 := bstep (se 2 (by rfl) ⟨253482, by rfl⟩ : syracuseStep 675953 = 506965) B506965
theorem B479363 : Blo 447780 479363 := bstep (se 1 (by rfl) ⟨359522, by rfl⟩ : syracuseStep 479363 = 719045) B719045
theorem B675971 : Blo 447780 675971 := bstep (se 1 (by rfl) ⟨506978, by rfl⟩ : syracuseStep 675971 = 1013957) B1013957
theorem B676001 : Blo 447780 676001 := bstep (se 2 (by rfl) ⟨253500, by rfl⟩ : syracuseStep 676001 = 507001) B507001
theorem B1134769 : Blo 447780 1134769 := bstep (se 2 (by rfl) ⟨425538, by rfl⟩ : syracuseStep 1134769 = 851077) B851077
theorem B676019 : Blo 447780 676019 := bstep (se 1 (by rfl) ⟨507014, by rfl⟩ : syracuseStep 676019 = 1014029) B1014029
theorem B676049 : Blo 447780 676049 := bstep (se 2 (by rfl) ⟨253518, by rfl⟩ : syracuseStep 676049 = 507037) B507037
theorem B676067 : Blo 447780 676067 := bstep (se 1 (by rfl) ⟨507050, by rfl⟩ : syracuseStep 676067 = 1014101) B1014101
theorem B1921265 : Blo 447780 1921265 := bstep (se 2 (by rfl) ⟨720474, by rfl⟩ : syracuseStep 1921265 = 1440949) B1440949
theorem B676097 : Blo 447780 676097 := bstep (se 2 (by rfl) ⟨253536, by rfl⟩ : syracuseStep 676097 = 507073) B507073
theorem B676115 : Blo 447780 676115 := bstep (se 1 (by rfl) ⟨507086, by rfl⟩ : syracuseStep 676115 = 1014173) B1014173
theorem B676145 : Blo 447780 676145 := bstep (se 2 (by rfl) ⟨253554, by rfl⟩ : syracuseStep 676145 = 507109) B507109
theorem B676163 : Blo 447780 676163 := bstep (se 1 (by rfl) ⟨507122, by rfl⟩ : syracuseStep 676163 = 1014245) B1014245
theorem B676193 : Blo 447780 676193 := bstep (se 2 (by rfl) ⟨253572, by rfl⟩ : syracuseStep 676193 = 507145) B507145
theorem B676211 : Blo 447780 676211 := bstep (se 1 (by rfl) ⟨507158, by rfl⟩ : syracuseStep 676211 = 1014317) B1014317
theorem B676241 : Blo 447780 676241 := bstep (se 2 (by rfl) ⟨253590, by rfl⟩ : syracuseStep 676241 = 507181) B507181
theorem B676259 : Blo 447780 676259 := bstep (se 1 (by rfl) ⟨507194, by rfl⟩ : syracuseStep 676259 = 1014389) B1014389
theorem B676289 : Blo 447780 676289 := bstep (se 2 (by rfl) ⟨253608, by rfl⟩ : syracuseStep 676289 = 507217) B507217
theorem B1135043 : Blo 447780 1135043 := bstep (se 1 (by rfl) ⟨851282, by rfl⟩ : syracuseStep 1135043 = 1702565) B1702565
theorem B676307 : Blo 447780 676307 := bstep (se 1 (by rfl) ⟨507230, by rfl⟩ : syracuseStep 676307 = 1014461) B1014461
theorem B676337 : Blo 447780 676337 := bstep (se 2 (by rfl) ⟨253626, by rfl⟩ : syracuseStep 676337 = 507253) B507253
theorem B676355 : Blo 447780 676355 := bstep (se 1 (by rfl) ⟨507266, by rfl⟩ : syracuseStep 676355 = 1014533) B1014533
theorem B3854861 : Blo 447780 3854861 := bstep (se 3 (by rfl) ⟨722786, by rfl⟩ : syracuseStep 3854861 = 1445573) B1445573
theorem B676385 : Blo 447780 676385 := bstep (se 2 (by rfl) ⟨253644, by rfl⟩ : syracuseStep 676385 = 507289) B507289
theorem B676403 : Blo 447780 676403 := bstep (se 1 (by rfl) ⟨507302, by rfl⟩ : syracuseStep 676403 = 1014605) B1014605
theorem B676433 : Blo 447780 676433 := bstep (se 2 (by rfl) ⟨253662, by rfl⟩ : syracuseStep 676433 = 507325) B507325
theorem B676451 : Blo 447780 676451 := bstep (se 1 (by rfl) ⟨507338, by rfl⟩ : syracuseStep 676451 = 1014677) B1014677
theorem B676481 : Blo 447780 676481 := bstep (se 2 (by rfl) ⟨253680, by rfl⟩ : syracuseStep 676481 = 507361) B507361
theorem B1135235 : Blo 447780 1135235 := bstep (se 1 (by rfl) ⟨851426, by rfl⟩ : syracuseStep 1135235 = 1702853) B1702853
theorem B676499 : Blo 447780 676499 := bstep (se 1 (by rfl) ⟨507374, by rfl⟩ : syracuseStep 676499 = 1014749) B1014749
theorem B676529 : Blo 447780 676529 := bstep (se 2 (by rfl) ⟨253698, by rfl⟩ : syracuseStep 676529 = 507397) B507397
theorem B676547 : Blo 447780 676547 := bstep (se 1 (by rfl) ⟨507410, by rfl⟩ : syracuseStep 676547 = 1014821) B1014821
theorem B4870853 : Blo 447780 4870853 := bstep (se 4 (by rfl) ⟨456642, by rfl⟩ : syracuseStep 4870853 = 913285) B913285
theorem B676577 : Blo 447780 676577 := bstep (se 2 (by rfl) ⟨253716, by rfl⟩ : syracuseStep 676577 = 507433) B507433
theorem B676595 : Blo 447780 676595 := bstep (se 1 (by rfl) ⟨507446, by rfl⟩ : syracuseStep 676595 = 1014893) B1014893
theorem B676625 : Blo 447780 676625 := bstep (se 2 (by rfl) ⟨253734, by rfl⟩ : syracuseStep 676625 = 507469) B507469
theorem B676643 : Blo 447780 676643 := bstep (se 1 (by rfl) ⟨507482, by rfl⟩ : syracuseStep 676643 = 1014965) B1014965
theorem B6476597 : Blo 447780 6476597 := bstep (se 5 (by rfl) ⟨303590, by rfl⟩ : syracuseStep 6476597 = 607181) B607181
theorem B676673 : Blo 447780 676673 := bstep (se 2 (by rfl) ⟨253752, by rfl⟩ : syracuseStep 676673 = 507505) B507505
theorem B676691 : Blo 447780 676691 := bstep (se 1 (by rfl) ⟨507518, by rfl⟩ : syracuseStep 676691 = 1015037) B1015037
theorem B676721 : Blo 447780 676721 := bstep (se 2 (by rfl) ⟨253770, by rfl⟩ : syracuseStep 676721 = 507541) B507541
theorem B480115 : Blo 447780 480115 := bstep (se 1 (by rfl) ⟨360086, by rfl⟩ : syracuseStep 480115 = 720173) B720173
theorem B676739 : Blo 447780 676739 := bstep (se 1 (by rfl) ⟨507554, by rfl⟩ : syracuseStep 676739 = 1015109) B1015109
theorem B676769 : Blo 447780 676769 := bstep (se 2 (by rfl) ⟨253788, by rfl⟩ : syracuseStep 676769 = 507577) B507577
theorem B1823651 : Blo 447780 1823651 := bstep (se 1 (by rfl) ⟨1367738, by rfl⟩ : syracuseStep 1823651 = 2735477) B2735477
theorem B2282417 : Blo 447780 2282417 := bstep (se 2 (by rfl) ⟨855906, by rfl⟩ : syracuseStep 2282417 = 1711813) B1711813
theorem B676787 : Blo 447780 676787 := bstep (se 1 (by rfl) ⟨507590, by rfl⟩ : syracuseStep 676787 = 1015181) B1015181
theorem B676817 : Blo 447780 676817 := bstep (se 2 (by rfl) ⟨253806, by rfl⟩ : syracuseStep 676817 = 507613) B507613
theorem B676835 : Blo 447780 676835 := bstep (se 1 (by rfl) ⟨507626, by rfl⟩ : syracuseStep 676835 = 1015253) B1015253
theorem B676865 : Blo 447780 676865 := bstep (se 2 (by rfl) ⟨253824, by rfl⟩ : syracuseStep 676865 = 507649) B507649
theorem B676883 : Blo 447780 676883 := bstep (se 1 (by rfl) ⟨507662, by rfl⟩ : syracuseStep 676883 = 1015325) B1015325
theorem B676913 : Blo 447780 676913 := bstep (se 2 (by rfl) ⟨253842, by rfl⟩ : syracuseStep 676913 = 507685) B507685
theorem B808003 : Blo 447780 808003 := bstep (se 1 (by rfl) ⟨606002, by rfl⟩ : syracuseStep 808003 = 1212005) B1212005
theorem B676931 : Blo 447780 676931 := bstep (se 1 (by rfl) ⟨507698, by rfl⟩ : syracuseStep 676931 = 1015397) B1015397
theorem B676961 : Blo 447780 676961 := bstep (se 2 (by rfl) ⟨253860, by rfl⟩ : syracuseStep 676961 = 507721) B507721
theorem B676979 : Blo 447780 676979 := bstep (se 1 (by rfl) ⟨507734, by rfl⟩ : syracuseStep 676979 = 1015469) B1015469
theorem B677009 : Blo 447780 677009 := bstep (se 2 (by rfl) ⟨253878, by rfl⟩ : syracuseStep 677009 = 507757) B507757
theorem B677027 : Blo 447780 677027 := bstep (se 1 (by rfl) ⟨507770, by rfl⟩ : syracuseStep 677027 = 1015541) B1015541
theorem B5788853 : Blo 447780 5788853 := bstep (se 5 (by rfl) ⟨271352, by rfl⟩ : syracuseStep 5788853 = 542705) B542705
theorem B677057 : Blo 447780 677057 := bstep (se 2 (by rfl) ⟨253896, by rfl⟩ : syracuseStep 677057 = 507793) B507793
theorem B677075 : Blo 447780 677075 := bstep (se 1 (by rfl) ⟨507806, by rfl⟩ : syracuseStep 677075 = 1015613) B1015613
theorem B808177 : Blo 447780 808177 := bstep (se 2 (by rfl) ⟨303066, by rfl⟩ : syracuseStep 808177 = 606133) B606133
theorem B677105 : Blo 447780 677105 := bstep (se 2 (by rfl) ⟨253914, by rfl⟩ : syracuseStep 677105 = 507829) B507829
theorem B677123 : Blo 447780 677123 := bstep (se 1 (by rfl) ⟨507842, by rfl⟩ : syracuseStep 677123 = 1015685) B1015685
theorem B677153 : Blo 447780 677153 := bstep (se 2 (by rfl) ⟨253932, by rfl⟩ : syracuseStep 677153 = 507865) B507865
theorem B447795 : Blo 447780 447795 := bstep (se 1 (by rfl) ⟨335846, by rfl⟩ : syracuseStep 447795 = 671693) B671693
theorem B677171 : Blo 447780 677171 := bstep (se 1 (by rfl) ⟨507878, by rfl⟩ : syracuseStep 677171 = 1015757) B1015757
theorem B447811 : Blo 447780 447811 := bstep (se 1 (by rfl) ⟨335858, by rfl⟩ : syracuseStep 447811 = 671717) B671717
theorem B3429701 : Blo 447780 3429701 := bstep (se 4 (by rfl) ⟨321534, by rfl⟩ : syracuseStep 3429701 = 643069) B643069
theorem B677201 : Blo 447780 677201 := bstep (se 2 (by rfl) ⟨253950, by rfl⟩ : syracuseStep 677201 = 507901) B507901
theorem B447827 : Blo 447780 447827 := bstep (se 1 (by rfl) ⟨335870, by rfl⟩ : syracuseStep 447827 = 671741) B671741
theorem B447843 : Blo 447780 447843 := bstep (se 1 (by rfl) ⟨335882, by rfl⟩ : syracuseStep 447843 = 671765) B671765
theorem B677219 : Blo 447780 677219 := bstep (se 1 (by rfl) ⟨507914, by rfl⟩ : syracuseStep 677219 = 1015829) B1015829
theorem B447859 : Blo 447780 447859 := bstep (se 1 (by rfl) ⟨335894, by rfl⟩ : syracuseStep 447859 = 671789) B671789
theorem B677249 : Blo 447780 677249 := bstep (se 2 (by rfl) ⟨253968, by rfl⟩ : syracuseStep 677249 = 507937) B507937
theorem B447875 : Blo 447780 447875 := bstep (se 1 (by rfl) ⟨335906, by rfl⟩ : syracuseStep 447875 = 671813) B671813
theorem B447891 : Blo 447780 447891 := bstep (se 1 (by rfl) ⟨335918, by rfl⟩ : syracuseStep 447891 = 671837) B671837
theorem B677267 : Blo 447780 677267 := bstep (se 1 (by rfl) ⟨507950, by rfl⟩ : syracuseStep 677267 = 1015901) B1015901
theorem B447907 : Blo 447780 447907 := bstep (se 1 (by rfl) ⟨335930, by rfl⟩ : syracuseStep 447907 = 671861) B671861
theorem B677297 : Blo 447780 677297 := bstep (se 2 (by rfl) ⟨253986, by rfl⟩ : syracuseStep 677297 = 507973) B507973
theorem B447923 : Blo 447780 447923 := bstep (se 1 (by rfl) ⟨335942, by rfl⟩ : syracuseStep 447923 = 671885) B671885
theorem B447939 : Blo 447780 447939 := bstep (se 1 (by rfl) ⟨335954, by rfl⟩ : syracuseStep 447939 = 671909) B671909
theorem B2807237 : Blo 447780 2807237 := bstep (se 4 (by rfl) ⟨263178, by rfl⟩ : syracuseStep 2807237 = 526357) B526357
theorem B677315 : Blo 447780 677315 := bstep (se 1 (by rfl) ⟨507986, by rfl⟩ : syracuseStep 677315 = 1015973) B1015973
theorem B447955 : Blo 447780 447955 := bstep (se 1 (by rfl) ⟨335966, by rfl⟩ : syracuseStep 447955 = 671933) B671933
theorem B677345 : Blo 447780 677345 := bstep (se 2 (by rfl) ⟨254004, by rfl⟩ : syracuseStep 677345 = 508009) B508009
theorem B447971 : Blo 447780 447971 := bstep (se 1 (by rfl) ⟨335978, by rfl⟩ : syracuseStep 447971 = 671957) B671957
theorem B447987 : Blo 447780 447987 := bstep (se 1 (by rfl) ⟨335990, by rfl⟩ : syracuseStep 447987 = 671981) B671981
theorem B677363 : Blo 447780 677363 := bstep (se 1 (by rfl) ⟨508022, by rfl⟩ : syracuseStep 677363 = 1016045) B1016045
theorem B448003 : Blo 447780 448003 := bstep (se 1 (by rfl) ⟨336002, by rfl⟩ : syracuseStep 448003 = 672005) B672005
theorem B677393 : Blo 447780 677393 := bstep (se 2 (by rfl) ⟨254022, by rfl⟩ : syracuseStep 677393 = 508045) B508045
theorem B448019 : Blo 447780 448019 := bstep (se 1 (by rfl) ⟨336014, by rfl⟩ : syracuseStep 448019 = 672029) B672029
theorem B448035 : Blo 447780 448035 := bstep (se 1 (by rfl) ⟨336026, by rfl⟩ : syracuseStep 448035 = 672053) B672053
theorem B677411 : Blo 447780 677411 := bstep (se 1 (by rfl) ⟨508058, by rfl⟩ : syracuseStep 677411 = 1016117) B1016117
theorem B1136177 : Blo 447780 1136177 := bstep (se 2 (by rfl) ⟨426066, by rfl⟩ : syracuseStep 1136177 = 852133) B852133
theorem B448051 : Blo 447780 448051 := bstep (se 1 (by rfl) ⟨336038, by rfl⟩ : syracuseStep 448051 = 672077) B672077
theorem B677441 : Blo 447780 677441 := bstep (se 2 (by rfl) ⟨254040, by rfl⟩ : syracuseStep 677441 = 508081) B508081
theorem B448067 : Blo 447780 448067 := bstep (se 1 (by rfl) ⟨336050, by rfl⟩ : syracuseStep 448067 = 672101) B672101
theorem B448083 : Blo 447780 448083 := bstep (se 1 (by rfl) ⟨336062, by rfl⟩ : syracuseStep 448083 = 672125) B672125
theorem B677459 : Blo 447780 677459 := bstep (se 1 (by rfl) ⟨508094, by rfl⟩ : syracuseStep 677459 = 1016189) B1016189
theorem B448099 : Blo 447780 448099 := bstep (se 1 (by rfl) ⟨336074, by rfl⟩ : syracuseStep 448099 = 672149) B672149
theorem B1136227 : Blo 447780 1136227 := bstep (se 1 (by rfl) ⟨852170, by rfl⟩ : syracuseStep 1136227 = 1704341) B1704341
theorem B677489 : Blo 447780 677489 := bstep (se 2 (by rfl) ⟨254058, by rfl⟩ : syracuseStep 677489 = 508117) B508117
theorem B448115 : Blo 447780 448115 := bstep (se 1 (by rfl) ⟨336086, by rfl⟩ : syracuseStep 448115 = 672173) B672173
theorem B448131 : Blo 447780 448131 := bstep (se 1 (by rfl) ⟨336098, by rfl⟩ : syracuseStep 448131 = 672197) B672197
theorem B677507 : Blo 447780 677507 := bstep (se 1 (by rfl) ⟨508130, by rfl⟩ : syracuseStep 677507 = 1016261) B1016261
theorem B448147 : Blo 447780 448147 := bstep (se 1 (by rfl) ⟨336110, by rfl⟩ : syracuseStep 448147 = 672221) B672221
theorem B677537 : Blo 447780 677537 := bstep (se 2 (by rfl) ⟨254076, by rfl⟩ : syracuseStep 677537 = 508153) B508153
theorem B2152099 : Blo 447780 2152099 := bstep (se 1 (by rfl) ⟨1614074, by rfl⟩ : syracuseStep 2152099 = 3228149) B3228149
theorem B448163 : Blo 447780 448163 := bstep (se 1 (by rfl) ⟨336122, by rfl⟩ : syracuseStep 448163 = 672245) B672245
theorem B448179 : Blo 447780 448179 := bstep (se 1 (by rfl) ⟨336134, by rfl⟩ : syracuseStep 448179 = 672269) B672269
theorem B677555 : Blo 447780 677555 := bstep (se 1 (by rfl) ⟨508166, by rfl⟩ : syracuseStep 677555 = 1016333) B1016333
theorem B448195 : Blo 447780 448195 := bstep (se 1 (by rfl) ⟨336146, by rfl⟩ : syracuseStep 448195 = 672293) B672293
theorem B677585 : Blo 447780 677585 := bstep (se 2 (by rfl) ⟨254094, by rfl⟩ : syracuseStep 677585 = 508189) B508189
theorem B448211 : Blo 447780 448211 := bstep (se 1 (by rfl) ⟨336158, by rfl⟩ : syracuseStep 448211 = 672317) B672317
theorem B448227 : Blo 447780 448227 := bstep (se 1 (by rfl) ⟨336170, by rfl⟩ : syracuseStep 448227 = 672341) B672341
theorem B677603 : Blo 447780 677603 := bstep (se 1 (by rfl) ⟨508202, by rfl⟩ : syracuseStep 677603 = 1016405) B1016405
theorem B1136369 : Blo 447780 1136369 := bstep (se 2 (by rfl) ⟨426138, by rfl⟩ : syracuseStep 1136369 = 852277) B852277
theorem B448243 : Blo 447780 448243 := bstep (se 1 (by rfl) ⟨336182, by rfl⟩ : syracuseStep 448243 = 672365) B672365
theorem B677633 : Blo 447780 677633 := bstep (se 2 (by rfl) ⟨254112, by rfl⟩ : syracuseStep 677633 = 508225) B508225
theorem B448259 : Blo 447780 448259 := bstep (se 1 (by rfl) ⟨336194, by rfl⟩ : syracuseStep 448259 = 672389) B672389
theorem B448275 : Blo 447780 448275 := bstep (se 1 (by rfl) ⟨336206, by rfl⟩ : syracuseStep 448275 = 672413) B672413
theorem B677651 : Blo 447780 677651 := bstep (se 1 (by rfl) ⟨508238, by rfl⟩ : syracuseStep 677651 = 1016477) B1016477
theorem B448291 : Blo 447780 448291 := bstep (se 1 (by rfl) ⟨336218, by rfl⟩ : syracuseStep 448291 = 672437) B672437
theorem B448307 : Blo 447780 448307 := bstep (se 1 (by rfl) ⟨336230, by rfl⟩ : syracuseStep 448307 = 672461) B672461
theorem B448323 : Blo 447780 448323 := bstep (se 1 (by rfl) ⟨336242, by rfl⟩ : syracuseStep 448323 = 672485) B672485
theorem B448339 : Blo 447780 448339 := bstep (se 1 (by rfl) ⟨336254, by rfl⟩ : syracuseStep 448339 = 672509) B672509
theorem B448355 : Blo 447780 448355 := bstep (se 1 (by rfl) ⟨336266, by rfl⟩ : syracuseStep 448355 = 672533) B672533
theorem B481123 : Blo 447780 481123 := bstep (se 1 (by rfl) ⟨360842, by rfl⟩ : syracuseStep 481123 = 721685) B721685
theorem B448371 : Blo 447780 448371 := bstep (se 1 (by rfl) ⟨336278, by rfl⟩ : syracuseStep 448371 = 672557) B672557
theorem B448387 : Blo 447780 448387 := bstep (se 1 (by rfl) ⟨336290, by rfl⟩ : syracuseStep 448387 = 672581) B672581
theorem B448403 : Blo 447780 448403 := bstep (se 1 (by rfl) ⟨336302, by rfl⟩ : syracuseStep 448403 = 672605) B672605
theorem B448419 : Blo 447780 448419 := bstep (se 1 (by rfl) ⟨336314, by rfl⟩ : syracuseStep 448419 = 672629) B672629
theorem B448435 : Blo 447780 448435 := bstep (se 1 (by rfl) ⟨336326, by rfl⟩ : syracuseStep 448435 = 672653) B672653
theorem B448451 : Blo 447780 448451 := bstep (se 1 (by rfl) ⟨336338, by rfl⟩ : syracuseStep 448451 = 672677) B672677
theorem B448467 : Blo 447780 448467 := bstep (se 1 (by rfl) ⟨336350, by rfl⟩ : syracuseStep 448467 = 672701) B672701
theorem B448483 : Blo 447780 448483 := bstep (se 1 (by rfl) ⟨336362, by rfl⟩ : syracuseStep 448483 = 672725) B672725
theorem B6510563 : Blo 447780 6510563 := bstep (se 1 (by rfl) ⟨4882922, by rfl⟩ : syracuseStep 6510563 = 9765845) B9765845
theorem B448499 : Blo 447780 448499 := bstep (se 1 (by rfl) ⟨336374, by rfl⟩ : syracuseStep 448499 = 672749) B672749
theorem B448515 : Blo 447780 448515 := bstep (se 1 (by rfl) ⟨336386, by rfl⟩ : syracuseStep 448515 = 672773) B672773
theorem B448531 : Blo 447780 448531 := bstep (se 1 (by rfl) ⟨336398, by rfl⟩ : syracuseStep 448531 = 672797) B672797
theorem B448547 : Blo 447780 448547 := bstep (se 1 (by rfl) ⟨336410, by rfl⟩ : syracuseStep 448547 = 672821) B672821
theorem B448563 : Blo 447780 448563 := bstep (se 1 (by rfl) ⟨336422, by rfl⟩ : syracuseStep 448563 = 672845) B672845
theorem B448579 : Blo 447780 448579 := bstep (se 1 (by rfl) ⟨336434, by rfl⟩ : syracuseStep 448579 = 672869) B672869
theorem B448595 : Blo 447780 448595 := bstep (se 1 (by rfl) ⟨336446, by rfl⟩ : syracuseStep 448595 = 672893) B672893
theorem B448611 : Blo 447780 448611 := bstep (se 1 (by rfl) ⟨336458, by rfl⟩ : syracuseStep 448611 = 672917) B672917
theorem B448627 : Blo 447780 448627 := bstep (se 1 (by rfl) ⟨336470, by rfl⟩ : syracuseStep 448627 = 672941) B672941
theorem B448643 : Blo 447780 448643 := bstep (se 1 (by rfl) ⟨336482, by rfl⟩ : syracuseStep 448643 = 672965) B672965
theorem B448659 : Blo 447780 448659 := bstep (se 1 (by rfl) ⟨336494, by rfl⟩ : syracuseStep 448659 = 672989) B672989
theorem B448675 : Blo 447780 448675 := bstep (se 1 (by rfl) ⟨336506, by rfl⟩ : syracuseStep 448675 = 673013) B673013
theorem B448691 : Blo 447780 448691 := bstep (se 1 (by rfl) ⟨336518, by rfl⟩ : syracuseStep 448691 = 673037) B673037
theorem B448707 : Blo 447780 448707 := bstep (se 1 (by rfl) ⟨336530, by rfl⟩ : syracuseStep 448707 = 673061) B673061
theorem B2087117 : Blo 447780 2087117 := bstep (se 3 (by rfl) ⟨391334, by rfl⟩ : syracuseStep 2087117 = 782669) B782669
theorem B448723 : Blo 447780 448723 := bstep (se 1 (by rfl) ⟨336542, by rfl⟩ : syracuseStep 448723 = 673085) B673085
theorem B448739 : Blo 447780 448739 := bstep (se 1 (by rfl) ⟨336554, by rfl⟩ : syracuseStep 448739 = 673109) B673109
theorem B448755 : Blo 447780 448755 := bstep (se 1 (by rfl) ⟨336566, by rfl⟩ : syracuseStep 448755 = 673133) B673133
theorem B448771 : Blo 447780 448771 := bstep (se 1 (by rfl) ⟨336578, by rfl⟩ : syracuseStep 448771 = 673157) B673157
theorem B514307 : Blo 447780 514307 := bstep (se 1 (by rfl) ⟨385730, by rfl⟩ : syracuseStep 514307 = 771461) B771461
theorem B2316557 : Blo 447780 2316557 := bstep (se 3 (by rfl) ⟨434354, by rfl⟩ : syracuseStep 2316557 = 868709) B868709
theorem B448787 : Blo 447780 448787 := bstep (se 1 (by rfl) ⟨336590, by rfl⟩ : syracuseStep 448787 = 673181) B673181
theorem B448803 : Blo 447780 448803 := bstep (se 1 (by rfl) ⟨336602, by rfl⟩ : syracuseStep 448803 = 673205) B673205
theorem B448819 : Blo 447780 448819 := bstep (se 1 (by rfl) ⟨336614, by rfl⟩ : syracuseStep 448819 = 673229) B673229
theorem B448835 : Blo 447780 448835 := bstep (se 1 (by rfl) ⟨336626, by rfl⟩ : syracuseStep 448835 = 673253) B673253
theorem B448851 : Blo 447780 448851 := bstep (se 1 (by rfl) ⟨336638, by rfl⟩ : syracuseStep 448851 = 673277) B673277
theorem B448867 : Blo 447780 448867 := bstep (se 1 (by rfl) ⟨336650, by rfl⟩ : syracuseStep 448867 = 673301) B673301
theorem B2283875 : Blo 447780 2283875 := bstep (se 1 (by rfl) ⟨1712906, by rfl⟩ : syracuseStep 2283875 = 3425813) B3425813
theorem B448883 : Blo 447780 448883 := bstep (se 1 (by rfl) ⟨336662, by rfl⟩ : syracuseStep 448883 = 673325) B673325
theorem B448899 : Blo 447780 448899 := bstep (se 1 (by rfl) ⟨336674, by rfl⟩ : syracuseStep 448899 = 673349) B673349
theorem B514435 : Blo 447780 514435 := bstep (se 1 (by rfl) ⟨385826, by rfl⟩ : syracuseStep 514435 = 771653) B771653
theorem B448915 : Blo 447780 448915 := bstep (se 1 (by rfl) ⟨336686, by rfl⟩ : syracuseStep 448915 = 673373) B673373
theorem B448931 : Blo 447780 448931 := bstep (se 1 (by rfl) ⟨336698, by rfl⟩ : syracuseStep 448931 = 673397) B673397
theorem B448947 : Blo 447780 448947 := bstep (se 1 (by rfl) ⟨336710, by rfl⟩ : syracuseStep 448947 = 673421) B673421
theorem B448963 : Blo 447780 448963 := bstep (se 1 (by rfl) ⟨336722, by rfl⟩ : syracuseStep 448963 = 673445) B673445
theorem B448979 : Blo 447780 448979 := bstep (se 1 (by rfl) ⟨336734, by rfl⟩ : syracuseStep 448979 = 673469) B673469
theorem B448995 : Blo 447780 448995 := bstep (se 1 (by rfl) ⟨336746, by rfl⟩ : syracuseStep 448995 = 673493) B673493
theorem B449011 : Blo 447780 449011 := bstep (se 1 (by rfl) ⟨336758, by rfl⟩ : syracuseStep 449011 = 673517) B673517
theorem B449027 : Blo 447780 449027 := bstep (se 1 (by rfl) ⟨336770, by rfl⟩ : syracuseStep 449027 = 673541) B673541
theorem B449043 : Blo 447780 449043 := bstep (se 1 (by rfl) ⟨336782, by rfl⟩ : syracuseStep 449043 = 673565) B673565
theorem B449059 : Blo 447780 449059 := bstep (se 1 (by rfl) ⟨336794, by rfl⟩ : syracuseStep 449059 = 673589) B673589
theorem B449075 : Blo 447780 449075 := bstep (se 1 (by rfl) ⟨336806, by rfl⟩ : syracuseStep 449075 = 673613) B673613
theorem B4872757 : Blo 447780 4872757 := bstep (se 5 (by rfl) ⟨228410, by rfl⟩ : syracuseStep 4872757 = 456821) B456821
theorem B449091 : Blo 447780 449091 := bstep (se 1 (by rfl) ⟨336818, by rfl⟩ : syracuseStep 449091 = 673637) B673637
theorem B449107 : Blo 447780 449107 := bstep (se 1 (by rfl) ⟨336830, by rfl⟩ : syracuseStep 449107 = 673661) B673661
theorem B449123 : Blo 447780 449123 := bstep (se 1 (by rfl) ⟨336842, by rfl⟩ : syracuseStep 449123 = 673685) B673685
theorem B449139 : Blo 447780 449139 := bstep (se 1 (by rfl) ⟨336854, by rfl⟩ : syracuseStep 449139 = 673709) B673709
theorem B449155 : Blo 447780 449155 := bstep (se 1 (by rfl) ⟨336866, by rfl⟩ : syracuseStep 449155 = 673733) B673733
theorem B449171 : Blo 447780 449171 := bstep (se 1 (by rfl) ⟨336878, by rfl⟩ : syracuseStep 449171 = 673757) B673757
theorem B449187 : Blo 447780 449187 := bstep (se 1 (by rfl) ⟨336890, by rfl⟩ : syracuseStep 449187 = 673781) B673781
theorem B1727153 : Blo 447780 1727153 := bstep (se 2 (by rfl) ⟨647682, by rfl⟩ : syracuseStep 1727153 = 1295365) B1295365
theorem B449203 : Blo 447780 449203 := bstep (se 1 (by rfl) ⟨336902, by rfl⟩ : syracuseStep 449203 = 673805) B673805
theorem B449219 : Blo 447780 449219 := bstep (se 1 (by rfl) ⟨336914, by rfl⟩ : syracuseStep 449219 = 673829) B673829
theorem B1301197 : Blo 447780 1301197 := bstep (se 3 (by rfl) ⟨243974, by rfl⟩ : syracuseStep 1301197 = 487949) B487949
theorem B1137361 : Blo 447780 1137361 := bstep (se 2 (by rfl) ⟨426510, by rfl⟩ : syracuseStep 1137361 = 853021) B853021
theorem B449235 : Blo 447780 449235 := bstep (se 1 (by rfl) ⟨336926, by rfl⟩ : syracuseStep 449235 = 673853) B673853
theorem B449251 : Blo 447780 449251 := bstep (se 1 (by rfl) ⟨336938, by rfl⟩ : syracuseStep 449251 = 673877) B673877
theorem B5135075 : Blo 447780 5135075 := bstep (se 1 (by rfl) ⟨3851306, by rfl⟩ : syracuseStep 5135075 = 7702613) B7702613
theorem B449267 : Blo 447780 449267 := bstep (se 1 (by rfl) ⟨336950, by rfl⟩ : syracuseStep 449267 = 673901) B673901
theorem B449283 : Blo 447780 449283 := bstep (se 1 (by rfl) ⟨336962, by rfl⟩ : syracuseStep 449283 = 673925) B673925
theorem B449299 : Blo 447780 449299 := bstep (se 1 (by rfl) ⟨336974, by rfl⟩ : syracuseStep 449299 = 673949) B673949
theorem B449315 : Blo 447780 449315 := bstep (se 1 (by rfl) ⟨336986, by rfl⟩ : syracuseStep 449315 = 673973) B673973
theorem B449331 : Blo 447780 449331 := bstep (se 1 (by rfl) ⟨336998, by rfl⟩ : syracuseStep 449331 = 673997) B673997
theorem B449347 : Blo 447780 449347 := bstep (se 1 (by rfl) ⟨337010, by rfl⟩ : syracuseStep 449347 = 674021) B674021
theorem B449363 : Blo 447780 449363 := bstep (se 1 (by rfl) ⟨337022, by rfl⟩ : syracuseStep 449363 = 674045) B674045
theorem B482131 : Blo 447780 482131 := bstep (se 1 (by rfl) ⟨361598, by rfl⟩ : syracuseStep 482131 = 723197) B723197
theorem B449379 : Blo 447780 449379 := bstep (se 1 (by rfl) ⟨337034, by rfl⟩ : syracuseStep 449379 = 674069) B674069
theorem B449395 : Blo 447780 449395 := bstep (se 1 (by rfl) ⟨337046, by rfl⟩ : syracuseStep 449395 = 674093) B674093
theorem B449411 : Blo 447780 449411 := bstep (se 1 (by rfl) ⟨337058, by rfl⟩ : syracuseStep 449411 = 674117) B674117
theorem B449427 : Blo 447780 449427 := bstep (se 1 (by rfl) ⟨337070, by rfl⟩ : syracuseStep 449427 = 674141) B674141
theorem B449443 : Blo 447780 449443 := bstep (se 1 (by rfl) ⟨337082, by rfl⟩ : syracuseStep 449443 = 674165) B674165
theorem B2743217 : Blo 447780 2743217 := bstep (se 2 (by rfl) ⟨1028706, by rfl⟩ : syracuseStep 2743217 = 2057413) B2057413
theorem B449459 : Blo 447780 449459 := bstep (se 1 (by rfl) ⟨337094, by rfl⟩ : syracuseStep 449459 = 674189) B674189
theorem B449475 : Blo 447780 449475 := bstep (se 1 (by rfl) ⟨337106, by rfl⟩ : syracuseStep 449475 = 674213) B674213
theorem B449491 : Blo 447780 449491 := bstep (se 1 (by rfl) ⟨337118, by rfl⟩ : syracuseStep 449491 = 674237) B674237
theorem B1137635 : Blo 447780 1137635 := bstep (se 1 (by rfl) ⟨853226, by rfl⟩ : syracuseStep 1137635 = 1706453) B1706453
theorem B449507 : Blo 447780 449507 := bstep (se 1 (by rfl) ⟨337130, by rfl⟩ : syracuseStep 449507 = 674261) B674261
theorem B449523 : Blo 447780 449523 := bstep (se 1 (by rfl) ⟨337142, by rfl⟩ : syracuseStep 449523 = 674285) B674285
theorem B449539 : Blo 447780 449539 := bstep (se 1 (by rfl) ⟨337154, by rfl⟩ : syracuseStep 449539 = 674309) B674309
theorem B449555 : Blo 447780 449555 := bstep (se 1 (by rfl) ⟨337166, by rfl⟩ : syracuseStep 449555 = 674333) B674333
theorem B449571 : Blo 447780 449571 := bstep (se 1 (by rfl) ⟨337178, by rfl⟩ : syracuseStep 449571 = 674357) B674357
theorem B449587 : Blo 447780 449587 := bstep (se 1 (by rfl) ⟨337190, by rfl⟩ : syracuseStep 449587 = 674381) B674381
theorem B449603 : Blo 447780 449603 := bstep (se 1 (by rfl) ⟨337202, by rfl⟩ : syracuseStep 449603 = 674405) B674405
theorem B2874437 : Blo 447780 2874437 := bstep (se 4 (by rfl) ⟨269478, by rfl⟩ : syracuseStep 2874437 = 538957) B538957
theorem B449619 : Blo 447780 449619 := bstep (se 1 (by rfl) ⟨337214, by rfl⟩ : syracuseStep 449619 = 674429) B674429
theorem B449635 : Blo 447780 449635 := bstep (se 1 (by rfl) ⟨337226, by rfl⟩ : syracuseStep 449635 = 674453) B674453
theorem B449651 : Blo 447780 449651 := bstep (se 1 (by rfl) ⟨337238, by rfl⟩ : syracuseStep 449651 = 674477) B674477
theorem B449667 : Blo 447780 449667 := bstep (se 1 (by rfl) ⟨337250, by rfl⟩ : syracuseStep 449667 = 674501) B674501
theorem B2284685 : Blo 447780 2284685 := bstep (se 3 (by rfl) ⟨428378, by rfl⟩ : syracuseStep 2284685 = 856757) B856757
theorem B449683 : Blo 447780 449683 := bstep (se 1 (by rfl) ⟨337262, by rfl⟩ : syracuseStep 449683 = 674525) B674525
theorem B1137827 : Blo 447780 1137827 := bstep (se 1 (by rfl) ⟨853370, by rfl⟩ : syracuseStep 1137827 = 1706741) B1706741
theorem B449699 : Blo 447780 449699 := bstep (se 1 (by rfl) ⟨337274, by rfl⟩ : syracuseStep 449699 = 674549) B674549
theorem B449715 : Blo 447780 449715 := bstep (se 1 (by rfl) ⟨337286, by rfl⟩ : syracuseStep 449715 = 674573) B674573
theorem B449731 : Blo 447780 449731 := bstep (se 1 (by rfl) ⟨337298, by rfl⟩ : syracuseStep 449731 = 674597) B674597
theorem B449747 : Blo 447780 449747 := bstep (se 1 (by rfl) ⟨337310, by rfl⟩ : syracuseStep 449747 = 674621) B674621
theorem B449763 : Blo 447780 449763 := bstep (se 1 (by rfl) ⟨337322, by rfl⟩ : syracuseStep 449763 = 674645) B674645
theorem B449779 : Blo 447780 449779 := bstep (se 1 (by rfl) ⟨337334, by rfl⟩ : syracuseStep 449779 = 674669) B674669
theorem B449795 : Blo 447780 449795 := bstep (se 1 (by rfl) ⟨337346, by rfl⟩ : syracuseStep 449795 = 674693) B674693
theorem B449811 : Blo 447780 449811 := bstep (se 1 (by rfl) ⟨337358, by rfl⟩ : syracuseStep 449811 = 674717) B674717
theorem B449827 : Blo 447780 449827 := bstep (se 1 (by rfl) ⟨337370, by rfl⟩ : syracuseStep 449827 = 674741) B674741
theorem B449843 : Blo 447780 449843 := bstep (se 1 (by rfl) ⟨337382, by rfl⟩ : syracuseStep 449843 = 674765) B674765
theorem B449859 : Blo 447780 449859 := bstep (se 1 (by rfl) ⟨337394, by rfl⟩ : syracuseStep 449859 = 674789) B674789
theorem B449875 : Blo 447780 449875 := bstep (se 1 (by rfl) ⟨337406, by rfl⟩ : syracuseStep 449875 = 674813) B674813
theorem B449891 : Blo 447780 449891 := bstep (se 1 (by rfl) ⟨337418, by rfl⟩ : syracuseStep 449891 = 674837) B674837
theorem B449907 : Blo 447780 449907 := bstep (se 1 (by rfl) ⟨337430, by rfl⟩ : syracuseStep 449907 = 674861) B674861
theorem B449923 : Blo 447780 449923 := bstep (se 1 (by rfl) ⟨337442, by rfl⟩ : syracuseStep 449923 = 674885) B674885
theorem B449939 : Blo 447780 449939 := bstep (se 1 (by rfl) ⟨337454, by rfl⟩ : syracuseStep 449939 = 674909) B674909
theorem B449955 : Blo 447780 449955 := bstep (se 1 (by rfl) ⟨337466, by rfl⟩ : syracuseStep 449955 = 674933) B674933
theorem B449971 : Blo 447780 449971 := bstep (se 1 (by rfl) ⟨337478, by rfl⟩ : syracuseStep 449971 = 674957) B674957
theorem B449987 : Blo 447780 449987 := bstep (se 1 (by rfl) ⟨337490, by rfl⟩ : syracuseStep 449987 = 674981) B674981
theorem B450003 : Blo 447780 450003 := bstep (se 1 (by rfl) ⟨337502, by rfl⟩ : syracuseStep 450003 = 675005) B675005
theorem B450019 : Blo 447780 450019 := bstep (se 1 (by rfl) ⟨337514, by rfl⟩ : syracuseStep 450019 = 675029) B675029
theorem B450035 : Blo 447780 450035 := bstep (se 1 (by rfl) ⟨337526, by rfl⟩ : syracuseStep 450035 = 675053) B675053
theorem B450051 : Blo 447780 450051 := bstep (se 1 (by rfl) ⟨337538, by rfl⟩ : syracuseStep 450051 = 675077) B675077
theorem B450067 : Blo 447780 450067 := bstep (se 1 (by rfl) ⟨337550, by rfl⟩ : syracuseStep 450067 = 675101) B675101
theorem B450083 : Blo 447780 450083 := bstep (se 1 (by rfl) ⟨337562, by rfl⟩ : syracuseStep 450083 = 675125) B675125
theorem B450099 : Blo 447780 450099 := bstep (se 1 (by rfl) ⟨337574, by rfl⟩ : syracuseStep 450099 = 675149) B675149
theorem B450115 : Blo 447780 450115 := bstep (se 1 (by rfl) ⟨337586, by rfl⟩ : syracuseStep 450115 = 675173) B675173
theorem B450131 : Blo 447780 450131 := bstep (se 1 (by rfl) ⟨337598, by rfl⟩ : syracuseStep 450131 = 675197) B675197
theorem B450147 : Blo 447780 450147 := bstep (se 1 (by rfl) ⟨337610, by rfl⟩ : syracuseStep 450147 = 675221) B675221
theorem B450163 : Blo 447780 450163 := bstep (se 1 (by rfl) ⟨337622, by rfl⟩ : syracuseStep 450163 = 675245) B675245
theorem B450179 : Blo 447780 450179 := bstep (se 1 (by rfl) ⟨337634, by rfl⟩ : syracuseStep 450179 = 675269) B675269
theorem B450195 : Blo 447780 450195 := bstep (se 1 (by rfl) ⟨337646, by rfl⟩ : syracuseStep 450195 = 675293) B675293
theorem B450211 : Blo 447780 450211 := bstep (se 1 (by rfl) ⟨337658, by rfl⟩ : syracuseStep 450211 = 675317) B675317
theorem B450227 : Blo 447780 450227 := bstep (se 1 (by rfl) ⟨337670, by rfl⟩ : syracuseStep 450227 = 675341) B675341
theorem B450243 : Blo 447780 450243 := bstep (se 1 (by rfl) ⟨337682, by rfl⟩ : syracuseStep 450243 = 675365) B675365
theorem B450259 : Blo 447780 450259 := bstep (se 1 (by rfl) ⟨337694, by rfl⟩ : syracuseStep 450259 = 675389) B675389
theorem B450275 : Blo 447780 450275 := bstep (se 1 (by rfl) ⟨337706, by rfl⟩ : syracuseStep 450275 = 675413) B675413
theorem B450291 : Blo 447780 450291 := bstep (se 1 (by rfl) ⟨337718, by rfl⟩ : syracuseStep 450291 = 675437) B675437
theorem B450307 : Blo 447780 450307 := bstep (se 1 (by rfl) ⟨337730, by rfl⟩ : syracuseStep 450307 = 675461) B675461
theorem B450323 : Blo 447780 450323 := bstep (se 1 (by rfl) ⟨337742, by rfl⟩ : syracuseStep 450323 = 675485) B675485
theorem B450339 : Blo 447780 450339 := bstep (se 1 (by rfl) ⟨337754, by rfl⟩ : syracuseStep 450339 = 675509) B675509
theorem B450355 : Blo 447780 450355 := bstep (se 1 (by rfl) ⟨337766, by rfl⟩ : syracuseStep 450355 = 675533) B675533
theorem B450371 : Blo 447780 450371 := bstep (se 1 (by rfl) ⟨337778, by rfl⟩ : syracuseStep 450371 = 675557) B675557
theorem B450387 : Blo 447780 450387 := bstep (se 1 (by rfl) ⟨337790, by rfl⟩ : syracuseStep 450387 = 675581) B675581
theorem B450403 : Blo 447780 450403 := bstep (se 1 (by rfl) ⟨337802, by rfl⟩ : syracuseStep 450403 = 675605) B675605
theorem B450419 : Blo 447780 450419 := bstep (se 1 (by rfl) ⟨337814, by rfl⟩ : syracuseStep 450419 = 675629) B675629
theorem B450435 : Blo 447780 450435 := bstep (se 1 (by rfl) ⟨337826, by rfl⟩ : syracuseStep 450435 = 675653) B675653
theorem B1925005 : Blo 447780 1925005 := bstep (se 3 (by rfl) ⟨360938, by rfl⟩ : syracuseStep 1925005 = 721877) B721877
theorem B450451 : Blo 447780 450451 := bstep (se 1 (by rfl) ⟨337838, by rfl⟩ : syracuseStep 450451 = 675677) B675677
theorem B450467 : Blo 447780 450467 := bstep (se 1 (by rfl) ⟨337850, by rfl⟩ : syracuseStep 450467 = 675701) B675701
theorem B450483 : Blo 447780 450483 := bstep (se 1 (by rfl) ⟨337862, by rfl⟩ : syracuseStep 450483 = 675725) B675725
theorem B450499 : Blo 447780 450499 := bstep (se 1 (by rfl) ⟨337874, by rfl⟩ : syracuseStep 450499 = 675749) B675749
theorem B450515 : Blo 447780 450515 := bstep (se 1 (by rfl) ⟨337886, by rfl⟩ : syracuseStep 450515 = 675773) B675773
theorem B450531 : Blo 447780 450531 := bstep (se 1 (by rfl) ⟨337898, by rfl⟩ : syracuseStep 450531 = 675797) B675797
theorem B450547 : Blo 447780 450547 := bstep (se 1 (by rfl) ⟨337910, by rfl⟩ : syracuseStep 450547 = 675821) B675821
theorem B450563 : Blo 447780 450563 := bstep (se 1 (by rfl) ⟨337922, by rfl⟩ : syracuseStep 450563 = 675845) B675845
theorem B450579 : Blo 447780 450579 := bstep (se 1 (by rfl) ⟨337934, by rfl⟩ : syracuseStep 450579 = 675869) B675869
theorem B450595 : Blo 447780 450595 := bstep (se 1 (by rfl) ⟨337946, by rfl⟩ : syracuseStep 450595 = 675893) B675893
theorem B450611 : Blo 447780 450611 := bstep (se 1 (by rfl) ⟨337958, by rfl⟩ : syracuseStep 450611 = 675917) B675917
theorem B450627 : Blo 447780 450627 := bstep (se 1 (by rfl) ⟨337970, by rfl⟩ : syracuseStep 450627 = 675941) B675941
theorem B1138769 : Blo 447780 1138769 := bstep (se 2 (by rfl) ⟨427038, by rfl⟩ : syracuseStep 1138769 = 854077) B854077
theorem B450643 : Blo 447780 450643 := bstep (se 1 (by rfl) ⟨337982, by rfl⟩ : syracuseStep 450643 = 675965) B675965
theorem B450659 : Blo 447780 450659 := bstep (se 1 (by rfl) ⟨337994, by rfl⟩ : syracuseStep 450659 = 675989) B675989
theorem B1007729 : Blo 447780 1007729 := bstep (se 2 (by rfl) ⟨377898, by rfl⟩ : syracuseStep 1007729 = 755797) B755797
theorem B450675 : Blo 447780 450675 := bstep (se 1 (by rfl) ⟨338006, by rfl⟩ : syracuseStep 450675 = 676013) B676013
theorem B1007747 : Blo 447780 1007747 := bstep (se 1 (by rfl) ⟨755810, by rfl⟩ : syracuseStep 1007747 = 1511621) B1511621
theorem B1138819 : Blo 447780 1138819 := bstep (se 1 (by rfl) ⟨854114, by rfl⟩ : syracuseStep 1138819 = 1708229) B1708229
theorem B450691 : Blo 447780 450691 := bstep (se 1 (by rfl) ⟨338018, by rfl⟩ : syracuseStep 450691 = 676037) B676037
theorem B450707 : Blo 447780 450707 := bstep (se 1 (by rfl) ⟨338030, by rfl⟩ : syracuseStep 450707 = 676061) B676061
theorem B450723 : Blo 447780 450723 := bstep (se 1 (by rfl) ⟨338042, by rfl⟩ : syracuseStep 450723 = 676085) B676085
theorem B1466545 : Blo 447780 1466545 := bstep (se 2 (by rfl) ⟨549954, by rfl⟩ : syracuseStep 1466545 = 1099909) B1099909
theorem B450739 : Blo 447780 450739 := bstep (se 1 (by rfl) ⟨338054, by rfl⟩ : syracuseStep 450739 = 676109) B676109
theorem B450755 : Blo 447780 450755 := bstep (se 1 (by rfl) ⟨338066, by rfl⟩ : syracuseStep 450755 = 676133) B676133
theorem B450771 : Blo 447780 450771 := bstep (se 1 (by rfl) ⟨338078, by rfl⟩ : syracuseStep 450771 = 676157) B676157
theorem B450787 : Blo 447780 450787 := bstep (se 1 (by rfl) ⟨338090, by rfl⟩ : syracuseStep 450787 = 676181) B676181
theorem B450803 : Blo 447780 450803 := bstep (se 1 (by rfl) ⟨338102, by rfl⟩ : syracuseStep 450803 = 676205) B676205
theorem B450819 : Blo 447780 450819 := bstep (se 1 (by rfl) ⟨338114, by rfl⟩ : syracuseStep 450819 = 676229) B676229
theorem B1138961 : Blo 447780 1138961 := bstep (se 2 (by rfl) ⟨427110, by rfl⟩ : syracuseStep 1138961 = 854221) B854221
theorem B450835 : Blo 447780 450835 := bstep (se 1 (by rfl) ⟨338126, by rfl⟩ : syracuseStep 450835 = 676253) B676253
theorem B1532195 : Blo 447780 1532195 := bstep (se 1 (by rfl) ⟨1149146, by rfl⟩ : syracuseStep 1532195 = 2298293) B2298293
theorem B450851 : Blo 447780 450851 := bstep (se 1 (by rfl) ⟨338138, by rfl⟩ : syracuseStep 450851 = 676277) B676277
theorem B450867 : Blo 447780 450867 := bstep (se 1 (by rfl) ⟨338150, by rfl⟩ : syracuseStep 450867 = 676301) B676301
theorem B450883 : Blo 447780 450883 := bstep (se 1 (by rfl) ⟨338162, by rfl⟩ : syracuseStep 450883 = 676325) B676325
theorem B450899 : Blo 447780 450899 := bstep (se 1 (by rfl) ⟨338174, by rfl⟩ : syracuseStep 450899 = 676349) B676349
theorem B450915 : Blo 447780 450915 := bstep (se 1 (by rfl) ⟨338186, by rfl⟩ : syracuseStep 450915 = 676373) B676373
theorem B450931 : Blo 447780 450931 := bstep (se 1 (by rfl) ⟨338198, by rfl⟩ : syracuseStep 450931 = 676397) B676397
theorem B450947 : Blo 447780 450947 := bstep (se 1 (by rfl) ⟨338210, by rfl⟩ : syracuseStep 450947 = 676421) B676421
theorem B1008017 : Blo 447780 1008017 := bstep (se 2 (by rfl) ⟨378006, by rfl⟩ : syracuseStep 1008017 = 756013) B756013
theorem B450963 : Blo 447780 450963 := bstep (se 1 (by rfl) ⟨338222, by rfl⟩ : syracuseStep 450963 = 676445) B676445
theorem B1008035 : Blo 447780 1008035 := bstep (se 1 (by rfl) ⟨756026, by rfl⟩ : syracuseStep 1008035 = 1512053) B1512053
theorem B450979 : Blo 447780 450979 := bstep (se 1 (by rfl) ⟨338234, by rfl⟩ : syracuseStep 450979 = 676469) B676469
theorem B450995 : Blo 447780 450995 := bstep (se 1 (by rfl) ⟨338246, by rfl⟩ : syracuseStep 450995 = 676493) B676493
theorem B451011 : Blo 447780 451011 := bstep (se 1 (by rfl) ⟨338258, by rfl⟩ : syracuseStep 451011 = 676517) B676517
theorem B451027 : Blo 447780 451027 := bstep (se 1 (by rfl) ⟨338270, by rfl⟩ : syracuseStep 451027 = 676541) B676541
theorem B451043 : Blo 447780 451043 := bstep (se 1 (by rfl) ⟨338282, by rfl⟩ : syracuseStep 451043 = 676565) B676565
theorem B451059 : Blo 447780 451059 := bstep (se 1 (by rfl) ⟨338294, by rfl⟩ : syracuseStep 451059 = 676589) B676589
theorem B451075 : Blo 447780 451075 := bstep (se 1 (by rfl) ⟨338306, by rfl⟩ : syracuseStep 451075 = 676613) B676613
theorem B451091 : Blo 447780 451091 := bstep (se 1 (by rfl) ⟨338318, by rfl⟩ : syracuseStep 451091 = 676637) B676637
theorem B451107 : Blo 447780 451107 := bstep (se 1 (by rfl) ⟨338330, by rfl⟩ : syracuseStep 451107 = 676661) B676661
theorem B451123 : Blo 447780 451123 := bstep (se 1 (by rfl) ⟨338342, by rfl⟩ : syracuseStep 451123 = 676685) B676685
theorem B451139 : Blo 447780 451139 := bstep (se 1 (by rfl) ⟨338354, by rfl⟩ : syracuseStep 451139 = 676709) B676709
theorem B451155 : Blo 447780 451155 := bstep (se 1 (by rfl) ⟨338366, by rfl⟩ : syracuseStep 451155 = 676733) B676733
theorem B451171 : Blo 447780 451171 := bstep (se 1 (by rfl) ⟨338378, by rfl⟩ : syracuseStep 451171 = 676757) B676757
theorem B975473 : Blo 447780 975473 := bstep (se 2 (by rfl) ⟨365802, by rfl⟩ : syracuseStep 975473 = 731605) B731605
theorem B451187 : Blo 447780 451187 := bstep (se 1 (by rfl) ⟨338390, by rfl⟩ : syracuseStep 451187 = 676781) B676781
theorem B451203 : Blo 447780 451203 := bstep (se 1 (by rfl) ⟨338402, by rfl⟩ : syracuseStep 451203 = 676805) B676805
theorem B451219 : Blo 447780 451219 := bstep (se 1 (by rfl) ⟨338414, by rfl⟩ : syracuseStep 451219 = 676829) B676829
theorem B451235 : Blo 447780 451235 := bstep (se 1 (by rfl) ⟨338426, by rfl⟩ : syracuseStep 451235 = 676853) B676853
theorem B1008305 : Blo 447780 1008305 := bstep (se 2 (by rfl) ⟨378114, by rfl⟩ : syracuseStep 1008305 = 756229) B756229
theorem B451251 : Blo 447780 451251 := bstep (se 1 (by rfl) ⟨338438, by rfl⟩ : syracuseStep 451251 = 676877) B676877
theorem B1008323 : Blo 447780 1008323 := bstep (se 1 (by rfl) ⟨756242, by rfl⟩ : syracuseStep 1008323 = 1512485) B1512485
theorem B451267 : Blo 447780 451267 := bstep (se 1 (by rfl) ⟨338450, by rfl⟩ : syracuseStep 451267 = 676901) B676901
theorem B451283 : Blo 447780 451283 := bstep (se 1 (by rfl) ⟨338462, by rfl⟩ : syracuseStep 451283 = 676925) B676925
theorem B451299 : Blo 447780 451299 := bstep (se 1 (by rfl) ⟨338474, by rfl⟩ : syracuseStep 451299 = 676949) B676949
theorem B451315 : Blo 447780 451315 := bstep (se 1 (by rfl) ⟨338486, by rfl⟩ : syracuseStep 451315 = 676973) B676973
theorem B451331 : Blo 447780 451331 := bstep (se 1 (by rfl) ⟨338498, by rfl⟩ : syracuseStep 451331 = 676997) B676997
theorem B451347 : Blo 447780 451347 := bstep (se 1 (by rfl) ⟨338510, by rfl⟩ : syracuseStep 451347 = 677021) B677021
theorem B451363 : Blo 447780 451363 := bstep (se 1 (by rfl) ⟨338522, by rfl⟩ : syracuseStep 451363 = 677045) B677045
theorem B451379 : Blo 447780 451379 := bstep (se 1 (by rfl) ⟨338534, by rfl⟩ : syracuseStep 451379 = 677069) B677069
theorem B451395 : Blo 447780 451395 := bstep (se 1 (by rfl) ⟨338546, by rfl⟩ : syracuseStep 451395 = 677093) B677093
theorem B451411 : Blo 447780 451411 := bstep (se 1 (by rfl) ⟨338558, by rfl⟩ : syracuseStep 451411 = 677117) B677117
theorem B451427 : Blo 447780 451427 := bstep (se 1 (by rfl) ⟨338570, by rfl⟩ : syracuseStep 451427 = 677141) B677141
theorem B451443 : Blo 447780 451443 := bstep (se 1 (by rfl) ⟨338582, by rfl⟩ : syracuseStep 451443 = 677165) B677165
theorem B451459 : Blo 447780 451459 := bstep (se 1 (by rfl) ⟨338594, by rfl⟩ : syracuseStep 451459 = 677189) B677189
theorem B451475 : Blo 447780 451475 := bstep (se 1 (by rfl) ⟨338606, by rfl⟩ : syracuseStep 451475 = 677213) B677213
theorem B451491 : Blo 447780 451491 := bstep (se 1 (by rfl) ⟨338618, by rfl⟩ : syracuseStep 451491 = 677237) B677237
theorem B451507 : Blo 447780 451507 := bstep (se 1 (by rfl) ⟨338630, by rfl⟩ : syracuseStep 451507 = 677261) B677261
theorem B451523 : Blo 447780 451523 := bstep (se 1 (by rfl) ⟨338642, by rfl⟩ : syracuseStep 451523 = 677285) B677285
theorem B1008593 : Blo 447780 1008593 := bstep (se 2 (by rfl) ⟨378222, by rfl⟩ : syracuseStep 1008593 = 756445) B756445
theorem B451539 : Blo 447780 451539 := bstep (se 1 (by rfl) ⟨338654, by rfl⟩ : syracuseStep 451539 = 677309) B677309
theorem B1008611 : Blo 447780 1008611 := bstep (se 1 (by rfl) ⟨756458, by rfl⟩ : syracuseStep 1008611 = 1512917) B1512917
theorem B451555 : Blo 447780 451555 := bstep (se 1 (by rfl) ⟨338666, by rfl⟩ : syracuseStep 451555 = 677333) B677333
theorem B451571 : Blo 447780 451571 := bstep (se 1 (by rfl) ⟨338678, by rfl⟩ : syracuseStep 451571 = 677357) B677357
theorem B451587 : Blo 447780 451587 := bstep (se 1 (by rfl) ⟨338690, by rfl⟩ : syracuseStep 451587 = 677381) B677381
theorem B2909189 : Blo 447780 2909189 := bstep (se 4 (by rfl) ⟨272736, by rfl⟩ : syracuseStep 2909189 = 545473) B545473
theorem B451603 : Blo 447780 451603 := bstep (se 1 (by rfl) ⟨338702, by rfl⟩ : syracuseStep 451603 = 677405) B677405
theorem B451619 : Blo 447780 451619 := bstep (se 1 (by rfl) ⟨338714, by rfl⟩ : syracuseStep 451619 = 677429) B677429
theorem B451635 : Blo 447780 451635 := bstep (se 1 (by rfl) ⟨338726, by rfl⟩ : syracuseStep 451635 = 677453) B677453
theorem B451651 : Blo 447780 451651 := bstep (se 1 (by rfl) ⟨338738, by rfl⟩ : syracuseStep 451651 = 677477) B677477
theorem B451667 : Blo 447780 451667 := bstep (se 1 (by rfl) ⟨338750, by rfl⟩ : syracuseStep 451667 = 677501) B677501
theorem B451683 : Blo 447780 451683 := bstep (se 1 (by rfl) ⟨338762, by rfl⟩ : syracuseStep 451683 = 677525) B677525
theorem B451699 : Blo 447780 451699 := bstep (se 1 (by rfl) ⟨338774, by rfl⟩ : syracuseStep 451699 = 677549) B677549
theorem B451715 : Blo 447780 451715 := bstep (se 1 (by rfl) ⟨338786, by rfl⟩ : syracuseStep 451715 = 677573) B677573
theorem B451731 : Blo 447780 451731 := bstep (se 1 (by rfl) ⟨338798, by rfl⟩ : syracuseStep 451731 = 677597) B677597
theorem B451747 : Blo 447780 451747 := bstep (se 1 (by rfl) ⟨338810, by rfl⟩ : syracuseStep 451747 = 677621) B677621
theorem B451763 : Blo 447780 451763 := bstep (se 1 (by rfl) ⟨338822, by rfl⟩ : syracuseStep 451763 = 677645) B677645
theorem B451779 : Blo 447780 451779 := bstep (se 1 (by rfl) ⟨338834, by rfl⟩ : syracuseStep 451779 = 677669) B677669
theorem B1008881 : Blo 447780 1008881 := bstep (se 2 (by rfl) ⟨378330, by rfl⟩ : syracuseStep 1008881 = 756661) B756661
theorem B1139953 : Blo 447780 1139953 := bstep (se 2 (by rfl) ⟨427482, by rfl⟩ : syracuseStep 1139953 = 854965) B854965
theorem B1008899 : Blo 447780 1008899 := bstep (se 1 (by rfl) ⟨756674, by rfl⟩ : syracuseStep 1008899 = 1513349) B1513349
theorem B5203253 : Blo 447780 5203253 := bstep (se 5 (by rfl) ⟨243902, by rfl⟩ : syracuseStep 5203253 = 487805) B487805
theorem B1435117 : Blo 447780 1435117 := bstep (se 3 (by rfl) ⟨269084, by rfl⟩ : syracuseStep 1435117 = 538169) B538169
theorem B1140227 : Blo 447780 1140227 := bstep (se 1 (by rfl) ⟨855170, by rfl⟩ : syracuseStep 1140227 = 1710341) B1710341
theorem B1009169 : Blo 447780 1009169 := bstep (se 2 (by rfl) ⟨378438, by rfl⟩ : syracuseStep 1009169 = 756877) B756877
theorem B1009187 : Blo 447780 1009187 := bstep (se 1 (by rfl) ⟨756890, by rfl⟩ : syracuseStep 1009187 = 1513781) B1513781
theorem B681601 : Blo 447780 681601 := bstep (se 2 (by rfl) ⟨255600, by rfl⟩ : syracuseStep 681601 = 511201) B511201
theorem B616081 : Blo 447780 616081 := bstep (se 2 (by rfl) ⟨231030, by rfl⟩ : syracuseStep 616081 = 462061) B462061
theorem B1140419 : Blo 447780 1140419 := bstep (se 1 (by rfl) ⟨855314, by rfl⟩ : syracuseStep 1140419 = 1710629) B1710629
theorem B1009457 : Blo 447780 1009457 := bstep (se 2 (by rfl) ⟨378546, by rfl⟩ : syracuseStep 1009457 = 757093) B757093
theorem B1009475 : Blo 447780 1009475 := bstep (se 1 (by rfl) ⟨757106, by rfl⟩ : syracuseStep 1009475 = 1514213) B1514213
theorem B1009745 : Blo 447780 1009745 := bstep (se 2 (by rfl) ⟨378654, by rfl⟩ : syracuseStep 1009745 = 757309) B757309
theorem B1009763 : Blo 447780 1009763 := bstep (se 1 (by rfl) ⟨757322, by rfl⟩ : syracuseStep 1009763 = 1514645) B1514645
theorem B649315 : Blo 447780 649315 := bstep (se 1 (by rfl) ⟨486986, by rfl⟩ : syracuseStep 649315 = 973973) B973973
theorem B1730737 : Blo 447780 1730737 := bstep (se 2 (by rfl) ⟨649026, by rfl⟩ : syracuseStep 1730737 = 1298053) B1298053
theorem B1042723 : Blo 447780 1042723 := bstep (se 1 (by rfl) ⟨782042, by rfl⟩ : syracuseStep 1042723 = 1564085) B1564085
theorem B1010033 : Blo 447780 1010033 := bstep (se 2 (by rfl) ⟨378762, by rfl⟩ : syracuseStep 1010033 = 757525) B757525
theorem B911729 : Blo 447780 911729 := bstep (se 2 (by rfl) ⟨341898, by rfl⟩ : syracuseStep 911729 = 683797) B683797
theorem B1010051 : Blo 447780 1010051 := bstep (se 1 (by rfl) ⟨757538, by rfl⟩ : syracuseStep 1010051 = 1515077) B1515077
theorem B1370513 : Blo 447780 1370513 := bstep (se 2 (by rfl) ⟨513942, by rfl⟩ : syracuseStep 1370513 = 1027885) B1027885
theorem B813539 : Blo 447780 813539 := bstep (se 1 (by rfl) ⟨610154, by rfl⟩ : syracuseStep 813539 = 1220309) B1220309
theorem B1370609 : Blo 447780 1370609 := bstep (se 2 (by rfl) ⟨513978, by rfl⟩ : syracuseStep 1370609 = 1027957) B1027957
theorem B2878001 : Blo 447780 2878001 := bstep (se 2 (by rfl) ⟨1079250, by rfl⟩ : syracuseStep 2878001 = 2158501) B2158501
theorem B3238469 : Blo 447780 3238469 := bstep (se 4 (by rfl) ⟨303606, by rfl⟩ : syracuseStep 3238469 = 607213) B607213
theorem B1141361 : Blo 447780 1141361 := bstep (se 2 (by rfl) ⟨428010, by rfl⟩ : syracuseStep 1141361 = 856021) B856021
theorem B1010321 : Blo 447780 1010321 := bstep (se 2 (by rfl) ⟨378870, by rfl⟩ : syracuseStep 1010321 = 757741) B757741
theorem B1010339 : Blo 447780 1010339 := bstep (se 1 (by rfl) ⟨757754, by rfl⟩ : syracuseStep 1010339 = 1515509) B1515509
theorem B1141411 : Blo 447780 1141411 := bstep (se 1 (by rfl) ⟨856058, by rfl⟩ : syracuseStep 1141411 = 1712117) B1712117
theorem B1141553 : Blo 447780 1141553 := bstep (se 2 (by rfl) ⟨428082, by rfl⟩ : syracuseStep 1141553 = 856165) B856165
theorem B4844387 : Blo 447780 4844387 := bstep (se 1 (by rfl) ⟨3633290, by rfl⟩ : syracuseStep 4844387 = 7266581) B7266581
theorem B682897 : Blo 447780 682897 := bstep (se 2 (by rfl) ⟨256086, by rfl⟩ : syracuseStep 682897 = 512173) B512173
theorem B1436579 : Blo 447780 1436579 := bstep (se 1 (by rfl) ⟨1077434, by rfl⟩ : syracuseStep 1436579 = 2154869) B2154869
theorem B1010609 : Blo 447780 1010609 := bstep (se 2 (by rfl) ⟨378978, by rfl⟩ : syracuseStep 1010609 = 757957) B757957
theorem B1010627 : Blo 447780 1010627 := bstep (se 1 (by rfl) ⟨757970, by rfl⟩ : syracuseStep 1010627 = 1515941) B1515941
theorem B650273 : Blo 447780 650273 := bstep (se 2 (by rfl) ⟨243852, by rfl⟩ : syracuseStep 650273 = 487705) B487705
theorem B1731725 : Blo 447780 1731725 := bstep (se 3 (by rfl) ⟨324698, by rfl⟩ : syracuseStep 1731725 = 649397) B649397
theorem B1436849 : Blo 447780 1436849 := bstep (se 2 (by rfl) ⟨538818, by rfl⟩ : syracuseStep 1436849 = 1077637) B1077637
theorem B1010897 : Blo 447780 1010897 := bstep (se 2 (by rfl) ⟨379086, by rfl⟩ : syracuseStep 1010897 = 758173) B758173
theorem B1010915 : Blo 447780 1010915 := bstep (se 1 (by rfl) ⟨758186, by rfl⟩ : syracuseStep 1010915 = 1516373) B1516373
theorem B1076483 : Blo 447780 1076483 := bstep (se 1 (by rfl) ⟨807362, by rfl⟩ : syracuseStep 1076483 = 1614725) B1614725
theorem B1011185 : Blo 447780 1011185 := bstep (se 2 (by rfl) ⟨379194, by rfl⟩ : syracuseStep 1011185 = 758389) B758389
theorem B1011203 : Blo 447780 1011203 := bstep (se 1 (by rfl) ⟨758402, by rfl⟩ : syracuseStep 1011203 = 1516805) B1516805
theorem B2551409 : Blo 447780 2551409 := bstep (se 2 (by rfl) ⟨956778, by rfl⟩ : syracuseStep 2551409 = 1913557) B1913557
theorem B913027 : Blo 447780 913027 := bstep (se 1 (by rfl) ⟨684770, by rfl⟩ : syracuseStep 913027 = 1369541) B1369541
theorem B9203341 : Blo 447780 9203341 := bstep (se 3 (by rfl) ⟨1725626, by rfl⟩ : syracuseStep 9203341 = 3451253) B3451253
theorem B1011473 : Blo 447780 1011473 := bstep (se 2 (by rfl) ⟨379302, by rfl⟩ : syracuseStep 1011473 = 758605) B758605
theorem B1142545 : Blo 447780 1142545 := bstep (se 2 (by rfl) ⟨428454, by rfl⟩ : syracuseStep 1142545 = 856909) B856909
theorem B41676565 : Blo 447780 41676565 := bstep (se 6 (by rfl) ⟨976794, by rfl⟩ : syracuseStep 41676565 = 1953589) B1953589
theorem B1011491 : Blo 447780 1011491 := bstep (se 1 (by rfl) ⟨758618, by rfl⟩ : syracuseStep 1011491 = 1517237) B1517237
theorem B8613773 : Blo 447780 8613773 := bstep (se 3 (by rfl) ⟨1615082, by rfl⟩ : syracuseStep 8613773 = 3230165) B3230165
theorem B2879459 : Blo 447780 2879459 := bstep (se 1 (by rfl) ⟨2159594, by rfl⟩ : syracuseStep 2879459 = 4319189) B4319189
theorem B1142819 : Blo 447780 1142819 := bstep (se 1 (by rfl) ⟨857114, by rfl⟩ : syracuseStep 1142819 = 1714229) B1714229
theorem B1011761 : Blo 447780 1011761 := bstep (se 2 (by rfl) ⟨379410, by rfl⟩ : syracuseStep 1011761 = 758821) B758821
theorem B1011779 : Blo 447780 1011779 := bstep (se 1 (by rfl) ⟨758834, by rfl⟩ : syracuseStep 1011779 = 1517669) B1517669
theorem B1929329 : Blo 447780 1929329 := bstep (se 2 (by rfl) ⟨723498, by rfl⟩ : syracuseStep 1929329 = 1446997) B1446997
theorem B4321421 : Blo 447780 4321421 := bstep (se 3 (by rfl) ⟨810266, by rfl⟩ : syracuseStep 4321421 = 1620533) B1620533
theorem B1929379 : Blo 447780 1929379 := bstep (se 1 (by rfl) ⟨1447034, by rfl⟩ : syracuseStep 1929379 = 2894069) B2894069
theorem B2420941 : Blo 447780 2420941 := bstep (se 3 (by rfl) ⟨453926, by rfl⟩ : syracuseStep 2420941 = 907853) B907853
theorem B3207395 : Blo 447780 3207395 := bstep (se 1 (by rfl) ⟨2405546, by rfl⟩ : syracuseStep 3207395 = 4811093) B4811093
theorem B1143011 : Blo 447780 1143011 := bstep (se 1 (by rfl) ⟨857258, by rfl⟩ : syracuseStep 1143011 = 1714517) B1714517
theorem B1012049 : Blo 447780 1012049 := bstep (se 2 (by rfl) ⟨379518, by rfl⟩ : syracuseStep 1012049 = 759037) B759037
theorem B1012067 : Blo 447780 1012067 := bstep (se 1 (by rfl) ⟨759050, by rfl⟩ : syracuseStep 1012067 = 1518101) B1518101
theorem B4321649 : Blo 447780 4321649 := bstep (se 2 (by rfl) ⟨1620618, by rfl⟩ : syracuseStep 4321649 = 3241237) B3241237
theorem B1077713 : Blo 447780 1077713 := bstep (se 2 (by rfl) ⟨404142, by rfl⟩ : syracuseStep 1077713 = 808285) B808285
theorem B1012337 : Blo 447780 1012337 := bstep (se 2 (by rfl) ⟨379626, by rfl⟩ : syracuseStep 1012337 = 759253) B759253
theorem B1012355 : Blo 447780 1012355 := bstep (se 1 (by rfl) ⟨759266, by rfl⟩ : syracuseStep 1012355 = 1518533) B1518533
theorem B3404429 : Blo 447780 3404429 := bstep (se 3 (by rfl) ⟨638330, by rfl⟩ : syracuseStep 3404429 = 1276661) B1276661
theorem B1700621 : Blo 447780 1700621 := bstep (se 3 (by rfl) ⟨318866, by rfl⟩ : syracuseStep 1700621 = 637733) B637733
theorem B1012625 : Blo 447780 1012625 := bstep (se 2 (by rfl) ⟨379734, by rfl⟩ : syracuseStep 1012625 = 759469) B759469
theorem B1012643 : Blo 447780 1012643 := bstep (se 1 (by rfl) ⟨759482, by rfl⟩ : syracuseStep 1012643 = 1518965) B1518965
theorem B2880461 : Blo 447780 2880461 := bstep (se 3 (by rfl) ⟨540086, by rfl⟩ : syracuseStep 2880461 = 1080173) B1080173
theorem B2552867 : Blo 447780 2552867 := bstep (se 1 (by rfl) ⟨1914650, by rfl⟩ : syracuseStep 2552867 = 3829301) B3829301
theorem B1012913 : Blo 447780 1012913 := bstep (se 2 (by rfl) ⟨379842, by rfl⟩ : syracuseStep 1012913 = 759685) B759685
theorem B1012931 : Blo 447780 1012931 := bstep (se 1 (by rfl) ⟨759698, by rfl⟩ : syracuseStep 1012931 = 1519397) B1519397
theorem B2454725 : Blo 447780 2454725 := bstep (se 4 (by rfl) ⟨230130, by rfl⟩ : syracuseStep 2454725 = 460261) B460261
theorem B1275203 : Blo 447780 1275203 := bstep (se 1 (by rfl) ⟨956402, by rfl⟩ : syracuseStep 1275203 = 1912805) B1912805
theorem B1013201 : Blo 447780 1013201 := bstep (se 2 (by rfl) ⟨379950, by rfl⟩ : syracuseStep 1013201 = 759901) B759901
theorem B1013219 : Blo 447780 1013219 := bstep (se 1 (by rfl) ⟨759914, by rfl⟩ : syracuseStep 1013219 = 1519829) B1519829
theorem B1701425 : Blo 447780 1701425 := bstep (se 2 (by rfl) ⟨638034, by rfl⟩ : syracuseStep 1701425 = 1276069) B1276069
theorem B1439309 : Blo 447780 1439309 := bstep (se 3 (by rfl) ⟨269870, by rfl⟩ : syracuseStep 1439309 = 539741) B539741
theorem B1537667 : Blo 447780 1537667 := bstep (se 1 (by rfl) ⟨1153250, by rfl⟩ : syracuseStep 1537667 = 2306501) B2306501
theorem B718481 : Blo 447780 718481 := bstep (se 2 (by rfl) ⟨269430, by rfl⟩ : syracuseStep 718481 = 538861) B538861
theorem B1013489 : Blo 447780 1013489 := bstep (se 2 (by rfl) ⟨380058, by rfl⟩ : syracuseStep 1013489 = 760117) B760117
theorem B1013507 : Blo 447780 1013507 := bstep (se 1 (by rfl) ⟨760130, by rfl⟩ : syracuseStep 1013507 = 1520261) B1520261
theorem B7796621 : Blo 447780 7796621 := bstep (se 3 (by rfl) ⟨1461866, by rfl⟩ : syracuseStep 7796621 = 2923733) B2923733
theorem B2553869 : Blo 447780 2553869 := bstep (se 3 (by rfl) ⟨478850, by rfl⟩ : syracuseStep 2553869 = 957701) B957701
theorem B1013777 : Blo 447780 1013777 := bstep (se 2 (by rfl) ⟨380166, by rfl⟩ : syracuseStep 1013777 = 760333) B760333
theorem B1013795 : Blo 447780 1013795 := bstep (se 1 (by rfl) ⟨760346, by rfl⟩ : syracuseStep 1013795 = 1520693) B1520693
theorem B915491 : Blo 447780 915491 := bstep (se 1 (by rfl) ⟨686618, by rfl⟩ : syracuseStep 915491 = 1373237) B1373237
theorem B1276013 : Blo 447780 1276013 := bstep (se 3 (by rfl) ⟨239252, by rfl⟩ : syracuseStep 1276013 = 478505) B478505
theorem B3897485 : Blo 447780 3897485 := bstep (se 3 (by rfl) ⟨730778, by rfl⟩ : syracuseStep 3897485 = 1461557) B1461557
theorem B686225 : Blo 447780 686225 := bstep (se 2 (by rfl) ⟨257334, by rfl⟩ : syracuseStep 686225 = 514669) B514669
theorem B1702093 : Blo 447780 1702093 := bstep (se 3 (by rfl) ⟨319142, by rfl⟩ : syracuseStep 1702093 = 638285) B638285
theorem B1276195 : Blo 447780 1276195 := bstep (se 1 (by rfl) ⟨957146, by rfl⟩ : syracuseStep 1276195 = 1914293) B1914293
theorem B1014065 : Blo 447780 1014065 := bstep (se 2 (by rfl) ⟨380274, by rfl⟩ : syracuseStep 1014065 = 760549) B760549
theorem B1014083 : Blo 447780 1014083 := bstep (se 1 (by rfl) ⟨760562, by rfl⟩ : syracuseStep 1014083 = 1521125) B1521125
theorem B1014353 : Blo 447780 1014353 := bstep (se 2 (by rfl) ⟨380382, by rfl⟩ : syracuseStep 1014353 = 760765) B760765
theorem B1014371 : Blo 447780 1014371 := bstep (se 1 (by rfl) ⟨760778, by rfl⟩ : syracuseStep 1014371 = 1521557) B1521557
theorem B1080067 : Blo 447780 1080067 := bstep (se 1 (by rfl) ⟨810050, by rfl⟩ : syracuseStep 1080067 = 1620101) B1620101
theorem B1276685 : Blo 447780 1276685 := bstep (se 3 (by rfl) ⟨239378, by rfl⟩ : syracuseStep 1276685 = 478757) B478757
theorem B1211249 : Blo 447780 1211249 := bstep (se 2 (by rfl) ⟨454218, by rfl⟩ : syracuseStep 1211249 = 908437) B908437
theorem B1014641 : Blo 447780 1014641 := bstep (se 2 (by rfl) ⟨380490, by rfl⟩ : syracuseStep 1014641 = 760981) B760981
theorem B850819 : Blo 447780 850819 := bstep (se 1 (by rfl) ⟨638114, by rfl⟩ : syracuseStep 850819 = 1276229) B1276229
theorem B1014659 : Blo 447780 1014659 := bstep (se 1 (by rfl) ⟨760994, by rfl⟩ : syracuseStep 1014659 = 1521989) B1521989
theorem B3832717 : Blo 447780 3832717 := bstep (se 3 (by rfl) ⟨718634, by rfl⟩ : syracuseStep 3832717 = 1437269) B1437269
theorem B1702883 : Blo 447780 1702883 := bstep (se 1 (by rfl) ⟨1277162, by rfl⟩ : syracuseStep 1702883 = 2554325) B2554325
theorem B850979 : Blo 447780 850979 := bstep (se 1 (by rfl) ⟨638234, by rfl⟩ : syracuseStep 850979 = 1276469) B1276469
theorem B1014929 : Blo 447780 1014929 := bstep (se 2 (by rfl) ⟨380598, by rfl⟩ : syracuseStep 1014929 = 761197) B761197
theorem B720019 : Blo 447780 720019 := bstep (se 1 (by rfl) ⟨540014, by rfl⟩ : syracuseStep 720019 = 1080029) B1080029
theorem B1014947 : Blo 447780 1014947 := bstep (se 1 (by rfl) ⟨761210, by rfl⟩ : syracuseStep 1014947 = 1522421) B1522421
theorem B720065 : Blo 447780 720065 := bstep (se 2 (by rfl) ⟨270024, by rfl⟩ : syracuseStep 720065 = 540049) B540049
theorem B10386629 : Blo 447780 10386629 := bstep (se 4 (by rfl) ⟨973746, by rfl⟩ : syracuseStep 10386629 = 1947493) B1947493
theorem B1539299 : Blo 447780 1539299 := bstep (se 1 (by rfl) ⟨1154474, by rfl⟩ : syracuseStep 1539299 = 2308949) B2308949
theorem B1441165 : Blo 447780 1441165 := bstep (se 3 (by rfl) ⟨270218, by rfl⟩ : syracuseStep 1441165 = 540437) B540437
theorem B1015217 : Blo 447780 1015217 := bstep (se 2 (by rfl) ⟨380706, by rfl⟩ : syracuseStep 1015217 = 761413) B761413
theorem B1015235 : Blo 447780 1015235 := bstep (se 1 (by rfl) ⟨761426, by rfl⟩ : syracuseStep 1015235 = 1522853) B1522853
theorem B3407345 : Blo 447780 3407345 := bstep (se 2 (by rfl) ⟨1277754, by rfl⟩ : syracuseStep 3407345 = 2555509) B2555509
theorem B1703537 : Blo 447780 1703537 := bstep (se 2 (by rfl) ⟨638826, by rfl⟩ : syracuseStep 1703537 = 1277653) B1277653
theorem B1015505 : Blo 447780 1015505 := bstep (se 2 (by rfl) ⟨380814, by rfl⟩ : syracuseStep 1015505 = 761629) B761629
theorem B1015523 : Blo 447780 1015523 := bstep (se 1 (by rfl) ⟨761642, by rfl⟩ : syracuseStep 1015523 = 1523285) B1523285
theorem B1277869 : Blo 447780 1277869 := bstep (se 3 (by rfl) ⟨239600, by rfl⟩ : syracuseStep 1277869 = 479201) B479201
theorem B3702725 : Blo 447780 3702725 := bstep (se 4 (by rfl) ⟨347130, by rfl⟩ : syracuseStep 3702725 = 694261) B694261
theorem B1081297 : Blo 447780 1081297 := bstep (se 2 (by rfl) ⟨405486, by rfl⟩ : syracuseStep 1081297 = 810973) B810973
theorem B1015793 : Blo 447780 1015793 := bstep (se 2 (by rfl) ⟨380922, by rfl⟩ : syracuseStep 1015793 = 761845) B761845
theorem B1015883 : Blo 447780 1015883 := bstep (se 1 (by rfl) ⟨761912, by rfl⟩ : syracuseStep 1015883 = 1523825) B1523825
theorem B1015937 : Blo 447780 1015937 := bstep (se 2 (by rfl) ⟨380976, by rfl⟩ : syracuseStep 1015937 = 761953) B761953
theorem B2556035 : Blo 447780 2556035 := bstep (se 1 (by rfl) ⟨1917026, by rfl⟩ : syracuseStep 2556035 = 3834053) B3834053
theorem B3244211 : Blo 447780 3244211 := bstep (se 1 (by rfl) ⟨2433158, by rfl⟩ : syracuseStep 3244211 = 4866317) B4866317
theorem B2425049 : Blo 447780 2425049 := bstep (se 2 (by rfl) ⟨909393, by rfl⟩ : syracuseStep 2425049 = 1818787) B1818787
theorem B1016153 : Blo 447780 1016153 := bstep (se 2 (by rfl) ⟨381057, by rfl⟩ : syracuseStep 1016153 = 762115) B762115
theorem B852353 : Blo 447780 852353 := bstep (se 2 (by rfl) ⟨319632, by rfl⟩ : syracuseStep 852353 = 639265) B639265
theorem B1016243 : Blo 447780 1016243 := bstep (se 1 (by rfl) ⟨762182, by rfl⟩ : syracuseStep 1016243 = 1524365) B1524365
theorem B1016279 : Blo 447780 1016279 := bstep (se 1 (by rfl) ⟨762209, by rfl⟩ : syracuseStep 1016279 = 1524419) B1524419
theorem B1704523 : Blo 447780 1704523 := bstep (se 1 (by rfl) ⟨1278392, by rfl⟩ : syracuseStep 1704523 = 2556785) B2556785
theorem B8553053 : Blo 447780 8553053 := bstep (se 3 (by rfl) ⟨1603697, by rfl⟩ : syracuseStep 8553053 = 3207395) B3207395
theorem B852619 : Blo 447780 852619 := bstep (se 1 (by rfl) ⟨639464, by rfl⟩ : syracuseStep 852619 = 1278929) B1278929
theorem B1016459 : Blo 447780 1016459 := bstep (se 1 (by rfl) ⟨762344, by rfl⟩ : syracuseStep 1016459 = 1524689) B1524689
theorem B1704797 : Blo 447780 1704797 := bstep (se 3 (by rfl) ⟨319649, by rfl⟩ : syracuseStep 1704797 = 639299) B639299
theorem B853067 : Blo 447780 853067 := bstep (se 1 (by rfl) ⟨639800, by rfl⟩ : syracuseStep 853067 = 1279601) B1279601
theorem B853249 : Blo 447780 853249 := bstep (se 2 (by rfl) ⟨319968, by rfl⟩ : syracuseStep 853249 = 639937) B639937
theorem B5113205 : Blo 447780 5113205 := bstep (se 5 (by rfl) ⟨239681, by rfl⟩ : syracuseStep 5113205 = 479363) B479363
theorem B1541555 : Blo 447780 1541555 := bstep (se 1 (by rfl) ⟨1156166, by rfl⟩ : syracuseStep 1541555 = 2312333) B2312333
theorem B1705495 : Blo 447780 1705495 := bstep (se 1 (by rfl) ⟨1279121, by rfl⟩ : syracuseStep 1705495 = 2558243) B2558243
theorem B1050199 : Blo 447780 1050199 := bstep (se 1 (by rfl) ⟨787649, by rfl⟩ : syracuseStep 1050199 = 1575299) B1575299
theorem B853591 : Blo 447780 853591 := bstep (se 1 (by rfl) ⟨640193, by rfl⟩ : syracuseStep 853591 = 1280387) B1280387
theorem B1279577 : Blo 447780 1279577 := bstep (se 2 (by rfl) ⟨479841, by rfl⟩ : syracuseStep 1279577 = 959683) B959683
theorem B853811 : Blo 447780 853811 := bstep (se 1 (by rfl) ⟨640358, by rfl⟩ : syracuseStep 853811 = 1280717) B1280717
theorem B755723 : Blo 447780 755723 := bstep (se 1 (by rfl) ⟨566792, by rfl⟩ : syracuseStep 755723 = 1133585) B1133585
theorem B854039 : Blo 447780 854039 := bstep (se 1 (by rfl) ⟨640529, by rfl⟩ : syracuseStep 854039 = 1281059) B1281059
theorem B755851 : Blo 447780 755851 := bstep (se 1 (by rfl) ⟨566888, by rfl⟩ : syracuseStep 755851 = 1133777) B1133777
theorem B821441 : Blo 447780 821441 := bstep (se 2 (by rfl) ⟨308040, by rfl⟩ : syracuseStep 821441 = 616081) B616081
theorem B1018049 : Blo 447780 1018049 := bstep (se 2 (by rfl) ⟨381768, by rfl⟩ : syracuseStep 1018049 = 763537) B763537
theorem B755993 : Blo 447780 755993 := bstep (se 2 (by rfl) ⟨283497, by rfl⟩ : syracuseStep 755993 = 566995) B566995
theorem B854297 : Blo 447780 854297 := bstep (se 2 (by rfl) ⟨320361, by rfl⟩ : syracuseStep 854297 = 640723) B640723
theorem B1706285 : Blo 447780 1706285 := bstep (se 3 (by rfl) ⟨319928, by rfl⟩ : syracuseStep 1706285 = 639857) B639857
theorem B756121 : Blo 447780 756121 := bstep (se 2 (by rfl) ⟨283545, by rfl⟩ : syracuseStep 756121 = 567091) B567091
theorem B2558425 : Blo 447780 2558425 := bstep (se 2 (by rfl) ⟨959409, by rfl⟩ : syracuseStep 2558425 = 1918819) B1918819
theorem B723467 : Blo 447780 723467 := bstep (se 1 (by rfl) ⟨542600, by rfl⟩ : syracuseStep 723467 = 1085201) B1085201
theorem B854707 : Blo 447780 854707 := bstep (se 1 (by rfl) ⟨641030, by rfl⟩ : syracuseStep 854707 = 1282061) B1282061
theorem B1280843 : Blo 447780 1280843 := bstep (se 1 (by rfl) ⟨960632, by rfl⟩ : syracuseStep 1280843 = 1921265) B1921265
theorem B756695 : Blo 447780 756695 := bstep (se 1 (by rfl) ⟨567521, by rfl⟩ : syracuseStep 756695 = 1135043) B1135043
theorem B756823 : Blo 447780 756823 := bstep (se 1 (by rfl) ⟨567617, by rfl⟩ : syracuseStep 756823 = 1135235) B1135235
theorem B3247235 : Blo 447780 3247235 := bstep (se 1 (by rfl) ⟨2435426, by rfl⟩ : syracuseStep 3247235 = 4870853) B4870853
theorem B855193 : Blo 447780 855193 := bstep (se 2 (by rfl) ⟨320697, by rfl⟩ : syracuseStep 855193 = 641395) B641395
theorem B8326385 : Blo 447780 8326385 := bstep (se 2 (by rfl) ⟨3122394, by rfl⟩ : syracuseStep 8326385 = 6244789) B6244789
theorem B1215767 : Blo 447780 1215767 := bstep (se 1 (by rfl) ⟨911825, by rfl⟩ : syracuseStep 1215767 = 1823651) B1823651
theorem B2559383 : Blo 447780 2559383 := bstep (se 1 (by rfl) ⟨1919537, by rfl⟩ : syracuseStep 2559383 = 3839075) B3839075
theorem B1707713 : Blo 447780 1707713 := bstep (se 2 (by rfl) ⟨640392, by rfl⟩ : syracuseStep 1707713 = 1280785) B1280785
theorem B757451 : Blo 447780 757451 := bstep (se 1 (by rfl) ⟨568088, by rfl⟩ : syracuseStep 757451 = 1136177) B1136177
theorem B855755 : Blo 447780 855755 := bstep (se 1 (by rfl) ⟨641816, by rfl⟩ : syracuseStep 855755 = 1283633) B1283633
theorem B757579 : Blo 447780 757579 := bstep (se 1 (by rfl) ⟨568184, by rfl⟩ : syracuseStep 757579 = 1136369) B1136369
theorem B855937 : Blo 447780 855937 := bstep (se 2 (by rfl) ⟨320976, by rfl⟩ : syracuseStep 855937 = 641953) B641953
theorem B757721 : Blo 447780 757721 := bstep (se 2 (by rfl) ⟨284145, by rfl⟩ : syracuseStep 757721 = 568291) B568291
theorem B1511513 : Blo 447780 1511513 := bstep (se 2 (by rfl) ⟨566817, by rfl⟩ : syracuseStep 1511513 = 1133635) B1133635
theorem B757849 : Blo 447780 757849 := bstep (se 2 (by rfl) ⟨284193, by rfl⟩ : syracuseStep 757849 = 568387) B568387
theorem B1642841 : Blo 447780 1642841 := bstep (se 2 (by rfl) ⟨616065, by rfl⟩ : syracuseStep 1642841 = 1232131) B1232131
theorem B1151435 : Blo 447780 1151435 := bstep (se 1 (by rfl) ⟨863576, by rfl⟩ : syracuseStep 1151435 = 1727153) B1727153
theorem B856651 : Blo 447780 856651 := bstep (se 1 (by rfl) ⟨642488, by rfl⟩ : syracuseStep 856651 = 1284977) B1284977
theorem B758423 : Blo 447780 758423 := bstep (se 1 (by rfl) ⟨568817, by rfl⟩ : syracuseStep 758423 = 1137635) B1137635
theorem B856727 : Blo 447780 856727 := bstep (se 1 (by rfl) ⟨642545, by rfl⟩ : syracuseStep 856727 = 1285091) B1285091
theorem B1512215 : Blo 447780 1512215 := bstep (se 1 (by rfl) ⟨1134161, by rfl⟩ : syracuseStep 1512215 = 2268323) B2268323
theorem B758551 : Blo 447780 758551 := bstep (se 1 (by rfl) ⟨568913, by rfl⟩ : syracuseStep 758551 = 1137827) B1137827
theorem B4854593 : Blo 447780 4854593 := bstep (se 2 (by rfl) ⟨1820472, by rfl⟩ : syracuseStep 4854593 = 3640945) B3640945
theorem B1217369 : Blo 447780 1217369 := bstep (se 2 (by rfl) ⟨456513, by rfl⟩ : syracuseStep 1217369 = 913027) B913027
theorem B1709201 : Blo 447780 1709201 := bstep (se 2 (by rfl) ⟨640950, by rfl⟩ : syracuseStep 1709201 = 1281901) B1281901
theorem B4854935 : Blo 447780 4854935 := bstep (se 1 (by rfl) ⟨3641201, by rfl⟩ : syracuseStep 4854935 = 7282403) B7282403
theorem B1512755 : Blo 447780 1512755 := bstep (se 1 (by rfl) ⟨1134566, by rfl⟩ : syracuseStep 1512755 = 2269133) B2269133
theorem B857395 : Blo 447780 857395 := bstep (se 1 (by rfl) ⟨643046, by rfl⟩ : syracuseStep 857395 = 1286093) B1286093
theorem B759179 : Blo 447780 759179 := bstep (se 1 (by rfl) ⟨569384, by rfl⟩ : syracuseStep 759179 = 1138769) B1138769
theorem B759307 : Blo 447780 759307 := bstep (se 1 (by rfl) ⟨569480, by rfl⟩ : syracuseStep 759307 = 1138961) B1138961
theorem B1021463 : Blo 447780 1021463 := bstep (se 1 (by rfl) ⟨766097, by rfl⟩ : syracuseStep 1021463 = 1532195) B1532195
theorem B857623 : Blo 447780 857623 := bstep (se 1 (by rfl) ⟨643217, by rfl⟩ : syracuseStep 857623 = 1286435) B1286435
theorem B1513025 : Blo 447780 1513025 := bstep (se 2 (by rfl) ⟨567384, by rfl⟩ : syracuseStep 1513025 = 1134769) B1134769
theorem B1709657 : Blo 447780 1709657 := bstep (se 2 (by rfl) ⟨641121, by rfl⟩ : syracuseStep 1709657 = 1282243) B1282243
theorem B759449 : Blo 447780 759449 := bstep (se 2 (by rfl) ⟨284793, by rfl⟩ : syracuseStep 759449 = 569587) B569587
theorem B759577 : Blo 447780 759577 := bstep (se 2 (by rfl) ⟨284841, by rfl⟩ : syracuseStep 759577 = 569683) B569683
theorem B1709869 : Blo 447780 1709869 := bstep (se 3 (by rfl) ⟨320600, by rfl⟩ : syracuseStep 1709869 = 641201) B641201
theorem B2561867 : Blo 447780 2561867 := bstep (se 1 (by rfl) ⟨1921400, by rfl⟩ : syracuseStep 2561867 = 3842801) B3842801
theorem B2168707 : Blo 447780 2168707 := bstep (se 1 (by rfl) ⟨1626530, by rfl⟩ : syracuseStep 2168707 = 3253061) B3253061
theorem B3282893 : Blo 447780 3282893 := bstep (se 3 (by rfl) ⟨615542, by rfl⟩ : syracuseStep 3282893 = 1231085) B1231085
theorem B1939459 : Blo 447780 1939459 := bstep (se 1 (by rfl) ⟨1454594, by rfl⟩ : syracuseStep 1939459 = 2909189) B2909189
theorem B1513565 : Blo 447780 1513565 := bstep (se 3 (by rfl) ⟨283793, by rfl⟩ : syracuseStep 1513565 = 567587) B567587
theorem B1710173 : Blo 447780 1710173 := bstep (se 3 (by rfl) ⟨320657, by rfl⟩ : syracuseStep 1710173 = 641315) B641315
theorem B3545189 : Blo 447780 3545189 := bstep (se 4 (by rfl) ⟨332361, by rfl⟩ : syracuseStep 3545189 = 664723) B664723
theorem B760151 : Blo 447780 760151 := bstep (se 1 (by rfl) ⟨570113, by rfl⟩ : syracuseStep 760151 = 1140227) B1140227
theorem B4004275 : Blo 447780 4004275 := bstep (se 1 (by rfl) ⟨3003206, by rfl⟩ : syracuseStep 4004275 = 6006413) B6006413
theorem B760279 : Blo 447780 760279 := bstep (se 1 (by rfl) ⟨570209, by rfl⟩ : syracuseStep 760279 = 1140419) B1140419
theorem B760907 : Blo 447780 760907 := bstep (se 1 (by rfl) ⟨570680, by rfl⟩ : syracuseStep 760907 = 1141361) B1141361
theorem B1514699 : Blo 447780 1514699 := bstep (se 1 (by rfl) ⟨1136024, by rfl⟩ : syracuseStep 1514699 = 2272049) B2272049
theorem B761035 : Blo 447780 761035 := bstep (se 1 (by rfl) ⟨570776, by rfl⟩ : syracuseStep 761035 = 1141553) B1141553
theorem B957719 : Blo 447780 957719 := bstep (se 1 (by rfl) ⟨718289, by rfl⟩ : syracuseStep 957719 = 1436579) B1436579
theorem B761177 : Blo 447780 761177 := bstep (se 2 (by rfl) ⟨285441, by rfl⟩ : syracuseStep 761177 = 570883) B570883
theorem B1154483 : Blo 447780 1154483 := bstep (se 1 (by rfl) ⟨865862, by rfl⟩ : syracuseStep 1154483 = 1731725) B1731725
theorem B957899 : Blo 447780 957899 := bstep (se 1 (by rfl) ⟨718424, by rfl⟩ : syracuseStep 957899 = 1436849) B1436849
theorem B1514969 : Blo 447780 1514969 := bstep (se 2 (by rfl) ⟨568113, by rfl⟩ : syracuseStep 1514969 = 1136227) B1136227
theorem B761305 : Blo 447780 761305 := bstep (se 2 (by rfl) ⟨285489, by rfl⟩ : syracuseStep 761305 = 570979) B570979
theorem B2301571 : Blo 447780 2301571 := bstep (se 1 (by rfl) ⟨1726178, by rfl⟩ : syracuseStep 2301571 = 3452357) B3452357
theorem B5742515 : Blo 447780 5742515 := bstep (se 1 (by rfl) ⟨4306886, by rfl⟩ : syracuseStep 5742515 = 8613773) B8613773
theorem B761879 : Blo 447780 761879 := bstep (se 1 (by rfl) ⟨571409, by rfl⟩ : syracuseStep 761879 = 1142819) B1142819
theorem B1286219 : Blo 447780 1286219 := bstep (se 1 (by rfl) ⟨964664, by rfl⟩ : syracuseStep 1286219 = 1929329) B1929329
theorem B1515671 : Blo 447780 1515671 := bstep (se 1 (by rfl) ⟨1136753, by rfl⟩ : syracuseStep 1515671 = 2273507) B2273507
theorem B762007 : Blo 447780 762007 := bstep (se 1 (by rfl) ⟨571505, by rfl⟩ : syracuseStep 762007 = 1143011) B1143011
theorem B2269457 : Blo 447780 2269457 := bstep (se 2 (by rfl) ⟨851046, by rfl⟩ : syracuseStep 2269457 = 1702093) B1702093
theorem B2269619 : Blo 447780 2269619 := bstep (se 1 (by rfl) ⟨1702214, by rfl⟩ : syracuseStep 2269619 = 3404429) B3404429
theorem B2564531 : Blo 447780 2564531 := bstep (se 1 (by rfl) ⟨1923398, by rfl⟩ : syracuseStep 2564531 = 3846797) B3846797
theorem B1712771 : Blo 447780 1712771 := bstep (se 1 (by rfl) ⟨1284578, by rfl⟩ : syracuseStep 1712771 = 2569157) B2569157
theorem B1712785 : Blo 447780 1712785 := bstep (se 2 (by rfl) ⟨642294, by rfl⟩ : syracuseStep 1712785 = 1284589) B1284589
theorem B1516211 : Blo 447780 1516211 := bstep (se 1 (by rfl) ⟨1137158, by rfl⟩ : syracuseStep 1516211 = 2274317) B2274317
theorem B6497009 : Blo 447780 6497009 := bstep (se 2 (by rfl) ⟨2436378, by rfl⟩ : syracuseStep 6497009 = 4872757) B4872757
theorem B6169445 : Blo 447780 6169445 := bstep (se 4 (by rfl) ⟨578385, by rfl⟩ : syracuseStep 6169445 = 1156771) B1156771
theorem B1516481 : Blo 447780 1516481 := bstep (se 2 (by rfl) ⟨568680, by rfl⟩ : syracuseStep 1516481 = 1137361) B1137361
theorem B1713089 : Blo 447780 1713089 := bstep (se 2 (by rfl) ⟨642408, by rfl⟩ : syracuseStep 1713089 = 1284817) B1284817
theorem B959539 : Blo 447780 959539 := bstep (se 1 (by rfl) ⟨719654, by rfl⟩ : syracuseStep 959539 = 1439309) B1439309
theorem B1025111 : Blo 447780 1025111 := bstep (se 1 (by rfl) ⟨768833, by rfl⟩ : syracuseStep 1025111 = 1537667) B1537667
theorem B5776757 : Blo 447780 5776757 := bstep (se 5 (by rfl) ⟨270785, by rfl⟩ : syracuseStep 5776757 = 541571) B541571
theorem B2598323 : Blo 447780 2598323 := bstep (se 1 (by rfl) ⟨1948742, by rfl⟩ : syracuseStep 2598323 = 3897485) B3897485
theorem B1517021 : Blo 447780 1517021 := bstep (se 3 (by rfl) ⟨284441, by rfl⟩ : syracuseStep 1517021 = 568883) B568883
theorem B960025 : Blo 447780 960025 := bstep (se 2 (by rfl) ⟨360009, by rfl⟩ : syracuseStep 960025 = 720019) B720019
theorem B1713757 : Blo 447780 1713757 := bstep (se 3 (by rfl) ⟨321329, by rfl⟩ : syracuseStep 1713757 = 642659) B642659
theorem B927425 : Blo 447780 927425 := bstep (se 2 (by rfl) ⟨347784, by rfl⟩ : syracuseStep 927425 = 695569) B695569
theorem B2565989 : Blo 447780 2565989 := bstep (se 4 (by rfl) ⟨240561, by rfl⟩ : syracuseStep 2565989 = 481123) B481123
theorem B567319 : Blo 447780 567319 := bstep (se 1 (by rfl) ⟨425489, by rfl⟩ : syracuseStep 567319 = 850979) B850979
theorem B6924419 : Blo 447780 6924419 := bstep (se 1 (by rfl) ⟨5193314, by rfl⟩ : syracuseStep 6924419 = 10386629) B10386629
theorem B1026199 : Blo 447780 1026199 := bstep (se 1 (by rfl) ⟨769649, by rfl⟩ : syracuseStep 1026199 = 1539299) B1539299
theorem B2271563 : Blo 447780 2271563 := bstep (se 1 (by rfl) ⟨1703672, by rfl⟩ : syracuseStep 2271563 = 3407345) B3407345
theorem B2566673 : Blo 447780 2566673 := bstep (se 2 (by rfl) ⟨962502, by rfl⟩ : syracuseStep 2566673 = 1925005) B1925005
theorem B3254849 : Blo 447780 3254849 := bstep (se 2 (by rfl) ⟨1220568, by rfl⟩ : syracuseStep 3254849 = 2441137) B2441137
theorem B1518155 : Blo 447780 1518155 := bstep (se 1 (by rfl) ⟨1138616, by rfl⟩ : syracuseStep 1518155 = 2277233) B2277233
theorem B2468483 : Blo 447780 2468483 := bstep (se 1 (by rfl) ⟨1851362, by rfl⟩ : syracuseStep 2468483 = 3702725) B3702725
theorem B1518425 : Blo 447780 1518425 := bstep (se 2 (by rfl) ⟨569409, by rfl⟩ : syracuseStep 1518425 = 1138819) B1138819
theorem B1715033 : Blo 447780 1715033 := bstep (se 2 (by rfl) ⟨643137, by rfl⟩ : syracuseStep 1715033 = 1286275) B1286275
theorem B961409 : Blo 447780 961409 := bstep (se 2 (by rfl) ⟨360528, by rfl⟩ : syracuseStep 961409 = 721057) B721057
theorem B1616843 : Blo 447780 1616843 := bstep (se 1 (by rfl) ⟨1212632, by rfl⟩ : syracuseStep 1616843 = 2425265) B2425265
theorem B1027073 : Blo 447780 1027073 := bstep (se 2 (by rfl) ⟨385152, by rfl⟩ : syracuseStep 1027073 = 770305) B770305
theorem B961931 : Blo 447780 961931 := bstep (se 1 (by rfl) ⟨721448, by rfl⟩ : syracuseStep 961931 = 1442897) B1442897
theorem B1519127 : Blo 447780 1519127 := bstep (se 1 (by rfl) ⟨1139345, by rfl⟩ : syracuseStep 1519127 = 2278691) B2278691
theorem B2076353 : Blo 447780 2076353 := bstep (se 2 (by rfl) ⟨778632, by rfl⟩ : syracuseStep 2076353 = 1557265) B1557265
theorem B569035 : Blo 447780 569035 := bstep (se 1 (by rfl) ⟨426776, by rfl⟩ : syracuseStep 569035 = 853553) B853553
theorem B1093441 : Blo 447780 1093441 := bstep (se 2 (by rfl) ⟨410040, by rfl⟩ : syracuseStep 1093441 = 820081) B820081
theorem B503851 : Blo 447780 503851 := bstep (se 1 (by rfl) ⟨377888, by rfl⟩ : syracuseStep 503851 = 755777) B755777
theorem B1519667 : Blo 447780 1519667 := bstep (se 1 (by rfl) ⟨1139750, by rfl⟩ : syracuseStep 1519667 = 2279501) B2279501
theorem B2273345 : Blo 447780 2273345 := bstep (se 2 (by rfl) ⟨852504, by rfl⟩ : syracuseStep 2273345 = 1705009) B1705009
theorem B503959 : Blo 447780 503959 := bstep (se 1 (by rfl) ⟨377969, by rfl⟩ : syracuseStep 503959 = 755939) B755939
theorem B1519937 : Blo 447780 1519937 := bstep (se 2 (by rfl) ⟨569976, by rfl⟩ : syracuseStep 1519937 = 1139953) B1139953
theorem B504139 : Blo 447780 504139 := bstep (se 1 (by rfl) ⟨378104, by rfl⟩ : syracuseStep 504139 = 756209) B756209
theorem B2732363 : Blo 447780 2732363 := bstep (se 1 (by rfl) ⟨2049272, by rfl⟩ : syracuseStep 2732363 = 4098545) B4098545
theorem B504247 : Blo 447780 504247 := bstep (se 1 (by rfl) ⟨378185, by rfl⟩ : syracuseStep 504247 = 756371) B756371
theorem B963161 : Blo 447780 963161 := bstep (se 2 (by rfl) ⟨361185, by rfl⟩ : syracuseStep 963161 = 722371) B722371
theorem B504427 : Blo 447780 504427 := bstep (se 1 (by rfl) ⟨378320, by rfl⟩ : syracuseStep 504427 = 756641) B756641
theorem B1913489 : Blo 447780 1913489 := bstep (se 2 (by rfl) ⟨717558, by rfl⟩ : syracuseStep 1913489 = 1435117) B1435117
theorem B570007 : Blo 447780 570007 := bstep (se 1 (by rfl) ⟨427505, by rfl⟩ : syracuseStep 570007 = 855011) B855011
theorem B1028759 : Blo 447780 1028759 := bstep (se 1 (by rfl) ⟨771569, by rfl⟩ : syracuseStep 1028759 = 1543139) B1543139
theorem B504535 : Blo 447780 504535 := bstep (se 1 (by rfl) ⟨378401, by rfl⟩ : syracuseStep 504535 = 756803) B756803
theorem B5124869 : Blo 447780 5124869 := bstep (se 4 (by rfl) ⟨480456, by rfl⟩ : syracuseStep 5124869 = 960913) B960913
theorem B1520477 : Blo 447780 1520477 := bstep (se 3 (by rfl) ⟨285089, by rfl⟩ : syracuseStep 1520477 = 570179) B570179
theorem B504715 : Blo 447780 504715 := bstep (se 1 (by rfl) ⟨378536, by rfl⟩ : syracuseStep 504715 = 757073) B757073
theorem B2634713 : Blo 447780 2634713 := bstep (se 2 (by rfl) ⟨988017, by rfl⟩ : syracuseStep 2634713 = 1976035) B1976035
theorem B963571 : Blo 447780 963571 := bstep (se 1 (by rfl) ⟨722678, by rfl⟩ : syracuseStep 963571 = 1445357) B1445357
theorem B504823 : Blo 447780 504823 := bstep (se 1 (by rfl) ⟨378617, by rfl⟩ : syracuseStep 504823 = 757235) B757235
theorem B505003 : Blo 447780 505003 := bstep (se 1 (by rfl) ⟨378752, by rfl⟩ : syracuseStep 505003 = 757505) B757505
theorem B3650777 : Blo 447780 3650777 := bstep (se 2 (by rfl) ⟨1369041, by rfl⟩ : syracuseStep 3650777 = 2738083) B2738083
theorem B505111 : Blo 447780 505111 := bstep (se 1 (by rfl) ⟨378833, by rfl⟩ : syracuseStep 505111 = 757667) B757667
theorem B505291 : Blo 447780 505291 := bstep (se 1 (by rfl) ⟨378968, by rfl⟩ : syracuseStep 505291 = 757937) B757937
theorem B570827 : Blo 447780 570827 := bstep (se 1 (by rfl) ⟨428120, by rfl⟩ : syracuseStep 570827 = 856241) B856241
theorem B865753 : Blo 447780 865753 := bstep (se 2 (by rfl) ⟨324657, by rfl⟩ : syracuseStep 865753 = 649315) B649315
theorem B964057 : Blo 447780 964057 := bstep (se 2 (by rfl) ⟨361521, by rfl⟩ : syracuseStep 964057 = 723043) B723043
theorem B505399 : Blo 447780 505399 := bstep (se 1 (by rfl) ⟨379049, by rfl⟩ : syracuseStep 505399 = 758099) B758099
theorem B2569907 : Blo 447780 2569907 := bstep (se 1 (by rfl) ⟨1927430, by rfl⟩ : syracuseStep 2569907 = 3854861) B3854861
theorem B505579 : Blo 447780 505579 := bstep (se 1 (by rfl) ⟨379184, by rfl⟩ : syracuseStep 505579 = 758369) B758369
theorem B505687 : Blo 447780 505687 := bstep (se 1 (by rfl) ⟨379265, by rfl⟩ : syracuseStep 505687 = 758531) B758531
theorem B1816451 : Blo 447780 1816451 := bstep (se 1 (by rfl) ⟨1362338, by rfl⟩ : syracuseStep 1816451 = 2724677) B2724677
theorem B1521611 : Blo 447780 1521611 := bstep (se 1 (by rfl) ⟨1141208, by rfl⟩ : syracuseStep 1521611 = 2282417) B2282417
theorem B2275289 : Blo 447780 2275289 := bstep (se 2 (by rfl) ⟨853233, by rfl⟩ : syracuseStep 2275289 = 1706467) B1706467
theorem B505867 : Blo 447780 505867 := bstep (se 1 (by rfl) ⟨379400, by rfl⟩ : syracuseStep 505867 = 758801) B758801
theorem B505975 : Blo 447780 505975 := bstep (se 1 (by rfl) ⟨379481, by rfl⟩ : syracuseStep 505975 = 758963) B758963
theorem B571531 : Blo 447780 571531 := bstep (se 1 (by rfl) ⟨428648, by rfl⟩ : syracuseStep 571531 = 857297) B857297
theorem B964801 : Blo 447780 964801 := bstep (se 2 (by rfl) ⟨361800, by rfl⟩ : syracuseStep 964801 = 723601) B723601
theorem B1521881 : Blo 447780 1521881 := bstep (se 2 (by rfl) ⟨570705, by rfl⟩ : syracuseStep 1521881 = 1141411) B1141411
theorem B506155 : Blo 447780 506155 := bstep (se 1 (by rfl) ⟨379616, by rfl⟩ : syracuseStep 506155 = 759233) B759233
theorem B56342897 : Blo 447780 56342897 := bstep (se 2 (by rfl) ⟨21128586, by rfl⟩ : syracuseStep 56342897 = 42257173) B42257173
theorem B506263 : Blo 447780 506263 := bstep (se 1 (by rfl) ⟨379697, by rfl⟩ : syracuseStep 506263 = 759395) B759395
theorem B7485965 : Blo 447780 7485965 := bstep (se 3 (by rfl) ⟨1403618, by rfl⟩ : syracuseStep 7485965 = 2807237) B2807237
theorem B506443 : Blo 447780 506443 := bstep (se 1 (by rfl) ⟨379832, by rfl⟩ : syracuseStep 506443 = 759665) B759665
theorem B637579 : Blo 447780 637579 := bstep (se 1 (by rfl) ⟨478184, by rfl⟩ : syracuseStep 637579 = 956369) B956369
theorem B4340375 : Blo 447780 4340375 := bstep (se 1 (by rfl) ⟨3255281, by rfl⟩ : syracuseStep 4340375 = 6510563) B6510563
theorem B3422897 : Blo 447780 3422897 := bstep (se 2 (by rfl) ⟨1283586, by rfl⟩ : syracuseStep 3422897 = 2567173) B2567173
theorem B506551 : Blo 447780 506551 := bstep (se 1 (by rfl) ⟨379913, by rfl⟩ : syracuseStep 506551 = 759827) B759827
theorem B1391411 : Blo 447780 1391411 := bstep (se 1 (by rfl) ⟨1043558, by rfl⟩ : syracuseStep 1391411 = 2087117) B2087117
theorem B3652427 : Blo 447780 3652427 := bstep (se 1 (by rfl) ⟨2739320, by rfl⟩ : syracuseStep 3652427 = 5478641) B5478641
theorem B506731 : Blo 447780 506731 := bstep (se 1 (by rfl) ⟨380048, by rfl⟩ : syracuseStep 506731 = 760097) B760097
theorem B1522583 : Blo 447780 1522583 := bstep (se 1 (by rfl) ⟨1141937, by rfl⟩ : syracuseStep 1522583 = 2283875) B2283875
theorem B506839 : Blo 447780 506839 := bstep (se 1 (by rfl) ⟨380129, by rfl⟩ : syracuseStep 506839 = 760259) B760259
theorem B1915949 : Blo 447780 1915949 := bstep (se 3 (by rfl) ⟨359240, by rfl⟩ : syracuseStep 1915949 = 718481) B718481
theorem B2571365 : Blo 447780 2571365 := bstep (se 4 (by rfl) ⟨241065, by rfl⟩ : syracuseStep 2571365 = 482131) B482131
theorem B507019 : Blo 447780 507019 := bstep (se 1 (by rfl) ⟨380264, by rfl⟩ : syracuseStep 507019 = 760529) B760529
theorem B3423383 : Blo 447780 3423383 := bstep (se 1 (by rfl) ⟨2567537, by rfl⟩ : syracuseStep 3423383 = 5135075) B5135075
theorem B3456179 : Blo 447780 3456179 := bstep (se 1 (by rfl) ⟨2592134, by rfl⟩ : syracuseStep 3456179 = 5184269) B5184269
theorem B507127 : Blo 447780 507127 := bstep (se 1 (by rfl) ⟨380345, by rfl⟩ : syracuseStep 507127 = 760691) B760691
theorem B1916291 : Blo 447780 1916291 := bstep (se 1 (by rfl) ⟨1437218, by rfl⟩ : syracuseStep 1916291 = 2874437) B2874437
theorem B507307 : Blo 447780 507307 := bstep (se 1 (by rfl) ⟨380480, by rfl⟩ : syracuseStep 507307 = 760961) B760961
theorem B1523123 : Blo 447780 1523123 := bstep (se 1 (by rfl) ⟨1142342, by rfl⟩ : syracuseStep 1523123 = 2284685) B2284685
theorem B12271121 : Blo 447780 12271121 := bstep (se 2 (by rfl) ⟨4601670, by rfl⟩ : syracuseStep 12271121 = 9203341) B9203341
theorem B507415 : Blo 447780 507415 := bstep (se 1 (by rfl) ⟨380561, by rfl⟩ : syracuseStep 507415 = 761123) B761123
theorem B2276909 : Blo 447780 2276909 := bstep (se 3 (by rfl) ⟨426920, by rfl⟩ : syracuseStep 2276909 = 853841) B853841
theorem B2571821 : Blo 447780 2571821 := bstep (se 3 (by rfl) ⟨482216, by rfl⟩ : syracuseStep 2571821 = 964433) B964433
theorem B10927709 : Blo 447780 10927709 := bstep (se 3 (by rfl) ⟨2048945, by rfl⟩ : syracuseStep 10927709 = 4097891) B4097891
theorem B1523393 : Blo 447780 1523393 := bstep (se 2 (by rfl) ⟨571272, by rfl⟩ : syracuseStep 1523393 = 1142545) B1142545
theorem B507595 : Blo 447780 507595 := bstep (se 1 (by rfl) ⟨380696, by rfl⟩ : syracuseStep 507595 = 761393) B761393
theorem B20790989 : Blo 447780 20790989 := bstep (se 3 (by rfl) ⟨3898310, by rfl⟩ : syracuseStep 20790989 = 7796621) B7796621
theorem B507703 : Blo 447780 507703 := bstep (se 1 (by rfl) ⟨380777, by rfl⟩ : syracuseStep 507703 = 761555) B761555
theorem B638923 : Blo 447780 638923 := bstep (se 1 (by rfl) ⟨479192, by rfl⟩ : syracuseStep 638923 = 958385) B958385
theorem B671705 : Blo 447780 671705 := bstep (se 2 (by rfl) ⟨251889, by rfl⟩ : syracuseStep 671705 = 503779) B503779
theorem B507883 : Blo 447780 507883 := bstep (se 1 (by rfl) ⟨380912, by rfl⟩ : syracuseStep 507883 = 761825) B761825
theorem B671819 : Blo 447780 671819 := bstep (se 1 (by rfl) ⟨503864, by rfl⟩ : syracuseStep 671819 = 1007729) B1007729
theorem B671831 : Blo 447780 671831 := bstep (se 1 (by rfl) ⟨503873, by rfl⟩ : syracuseStep 671831 = 1007747) B1007747
theorem B507991 : Blo 447780 507991 := bstep (se 1 (by rfl) ⟨380993, by rfl⟩ : syracuseStep 507991 = 761987) B761987
theorem B671897 : Blo 447780 671897 := bstep (se 2 (by rfl) ⟨251961, by rfl⟩ : syracuseStep 671897 = 503923) B503923
theorem B639191 : Blo 447780 639191 := bstep (se 1 (by rfl) ⟨479393, by rfl⟩ : syracuseStep 639191 = 958787) B958787
theorem B2572505 : Blo 447780 2572505 := bstep (se 2 (by rfl) ⟨964689, by rfl⟩ : syracuseStep 2572505 = 1929379) B1929379
theorem B1523933 : Blo 447780 1523933 := bstep (se 3 (by rfl) ⟨285737, by rfl⟩ : syracuseStep 1523933 = 571475) B571475
theorem B672011 : Blo 447780 672011 := bstep (se 1 (by rfl) ⟨504008, by rfl⟩ : syracuseStep 672011 = 1008017) B1008017
theorem B508171 : Blo 447780 508171 := bstep (se 1 (by rfl) ⟨381128, by rfl⟩ : syracuseStep 508171 = 762257) B762257
theorem B3227921 : Blo 447780 3227921 := bstep (se 2 (by rfl) ⟨1210470, by rfl⟩ : syracuseStep 3227921 = 2420941) B2420941
theorem B672023 : Blo 447780 672023 := bstep (se 1 (by rfl) ⟨504017, by rfl⟩ : syracuseStep 672023 = 1008035) B1008035
theorem B672089 : Blo 447780 672089 := bstep (se 2 (by rfl) ⟨252033, by rfl⟩ : syracuseStep 672089 = 504067) B504067
theorem B672203 : Blo 447780 672203 := bstep (se 1 (by rfl) ⟨504152, by rfl⟩ : syracuseStep 672203 = 1008305) B1008305
theorem B672215 : Blo 447780 672215 := bstep (se 1 (by rfl) ⟨504161, by rfl⟩ : syracuseStep 672215 = 1008323) B1008323
theorem B672281 : Blo 447780 672281 := bstep (se 2 (by rfl) ⟨252105, by rfl⟩ : syracuseStep 672281 = 504211) B504211
theorem B672395 : Blo 447780 672395 := bstep (se 1 (by rfl) ⟨504296, by rfl⟩ : syracuseStep 672395 = 1008593) B1008593
theorem B672407 : Blo 447780 672407 := bstep (se 1 (by rfl) ⟨504305, by rfl⟩ : syracuseStep 672407 = 1008611) B1008611
theorem B6177485 : Blo 447780 6177485 := bstep (se 3 (by rfl) ⟨1158278, by rfl⟩ : syracuseStep 6177485 = 2316557) B2316557
theorem B672473 : Blo 447780 672473 := bstep (se 2 (by rfl) ⟨252177, by rfl⟩ : syracuseStep 672473 = 504355) B504355
theorem B672587 : Blo 447780 672587 := bstep (se 1 (by rfl) ⟨504440, by rfl⟩ : syracuseStep 672587 = 1008881) B1008881
theorem B672599 : Blo 447780 672599 := bstep (se 1 (by rfl) ⟨504449, by rfl⟩ : syracuseStep 672599 = 1008899) B1008899
theorem B1622915 : Blo 447780 1622915 := bstep (se 1 (by rfl) ⟨1217186, by rfl⟩ : syracuseStep 1622915 = 2434373) B2434373
theorem B672665 : Blo 447780 672665 := bstep (se 2 (by rfl) ⟨252249, by rfl⟩ : syracuseStep 672665 = 504499) B504499
theorem B672779 : Blo 447780 672779 := bstep (se 1 (by rfl) ⟨504584, by rfl⟩ : syracuseStep 672779 = 1009169) B1009169
theorem B672791 : Blo 447780 672791 := bstep (se 1 (by rfl) ⟨504593, by rfl⟩ : syracuseStep 672791 = 1009187) B1009187
theorem B6505541 : Blo 447780 6505541 := bstep (se 4 (by rfl) ⟨609894, by rfl⟩ : syracuseStep 6505541 = 1219789) B1219789
theorem B672857 : Blo 447780 672857 := bstep (se 2 (by rfl) ⟨252321, by rfl⟩ : syracuseStep 672857 = 504643) B504643
theorem B640153 : Blo 447780 640153 := bstep (se 2 (by rfl) ⟨240057, by rfl⟩ : syracuseStep 640153 = 480115) B480115
theorem B672971 : Blo 447780 672971 := bstep (se 1 (by rfl) ⟨504728, by rfl⟩ : syracuseStep 672971 = 1009457) B1009457
theorem B672983 : Blo 447780 672983 := bstep (se 1 (by rfl) ⟨504737, by rfl⟩ : syracuseStep 672983 = 1009475) B1009475
theorem B673049 : Blo 447780 673049 := bstep (se 2 (by rfl) ⟨252393, by rfl⟩ : syracuseStep 673049 = 504787) B504787
theorem B673163 : Blo 447780 673163 := bstep (se 1 (by rfl) ⟨504872, by rfl⟩ : syracuseStep 673163 = 1009745) B1009745
theorem B673175 : Blo 447780 673175 := bstep (se 1 (by rfl) ⟨504881, by rfl⟩ : syracuseStep 673175 = 1009763) B1009763
theorem B673241 : Blo 447780 673241 := bstep (se 2 (by rfl) ⟨252465, by rfl⟩ : syracuseStep 673241 = 504931) B504931
theorem B673355 : Blo 447780 673355 := bstep (se 1 (by rfl) ⟨505016, by rfl⟩ : syracuseStep 673355 = 1010033) B1010033
theorem B607819 : Blo 447780 607819 := bstep (se 1 (by rfl) ⟨455864, by rfl⟩ : syracuseStep 607819 = 911729) B911729
theorem B673367 : Blo 447780 673367 := bstep (se 1 (by rfl) ⟨505025, by rfl⟩ : syracuseStep 673367 = 1010051) B1010051
theorem B542359 : Blo 447780 542359 := bstep (se 1 (by rfl) ⟨406769, by rfl⟩ : syracuseStep 542359 = 813539) B813539
theorem B673433 : Blo 447780 673433 := bstep (se 2 (by rfl) ⟨252537, by rfl⟩ : syracuseStep 673433 = 505075) B505075
theorem B1918667 : Blo 447780 1918667 := bstep (se 1 (by rfl) ⟨1439000, by rfl⟩ : syracuseStep 1918667 = 2878001) B2878001
theorem B673547 : Blo 447780 673547 := bstep (se 1 (by rfl) ⟨505160, by rfl⟩ : syracuseStep 673547 = 1010321) B1010321
theorem B673559 : Blo 447780 673559 := bstep (se 1 (by rfl) ⟨505169, by rfl⟩ : syracuseStep 673559 = 1010339) B1010339
theorem B673625 : Blo 447780 673625 := bstep (se 2 (by rfl) ⟨252609, by rfl⟩ : syracuseStep 673625 = 505219) B505219
theorem B3229591 : Blo 447780 3229591 := bstep (se 1 (by rfl) ⟨2422193, by rfl⟩ : syracuseStep 3229591 = 4844387) B4844387
theorem B673739 : Blo 447780 673739 := bstep (se 1 (by rfl) ⟨505304, by rfl⟩ : syracuseStep 673739 = 1010609) B1010609
theorem B673751 : Blo 447780 673751 := bstep (se 1 (by rfl) ⟨505313, by rfl⟩ : syracuseStep 673751 = 1010627) B1010627
theorem B673817 : Blo 447780 673817 := bstep (se 2 (by rfl) ⟨252681, by rfl⟩ : syracuseStep 673817 = 505363) B505363
theorem B673931 : Blo 447780 673931 := bstep (se 1 (by rfl) ⟨505448, by rfl⟩ : syracuseStep 673931 = 1010897) B1010897
theorem B673943 : Blo 447780 673943 := bstep (se 1 (by rfl) ⟨505457, by rfl⟩ : syracuseStep 673943 = 1010915) B1010915
theorem B2869465 : Blo 447780 2869465 := bstep (se 2 (by rfl) ⟨1076049, by rfl⟩ : syracuseStep 2869465 = 2152099) B2152099
theorem B674009 : Blo 447780 674009 := bstep (se 2 (by rfl) ⟨252753, by rfl⟩ : syracuseStep 674009 = 505507) B505507
theorem B674123 : Blo 447780 674123 := bstep (se 1 (by rfl) ⟨505592, by rfl⟩ : syracuseStep 674123 = 1011185) B1011185
theorem B674135 : Blo 447780 674135 := bstep (se 1 (by rfl) ⟨505601, by rfl⟩ : syracuseStep 674135 = 1011203) B1011203
theorem B674201 : Blo 447780 674201 := bstep (se 2 (by rfl) ⟨252825, by rfl⟩ : syracuseStep 674201 = 505651) B505651
theorem B674315 : Blo 447780 674315 := bstep (se 1 (by rfl) ⟨505736, by rfl⟩ : syracuseStep 674315 = 1011473) B1011473
theorem B674327 : Blo 447780 674327 := bstep (se 1 (by rfl) ⟨505745, by rfl⟩ : syracuseStep 674327 = 1011491) B1011491
theorem B641611 : Blo 447780 641611 := bstep (se 1 (by rfl) ⟨481208, by rfl⟩ : syracuseStep 641611 = 962417) B962417
theorem B641623 : Blo 447780 641623 := bstep (se 1 (by rfl) ⟨481217, by rfl⟩ : syracuseStep 641623 = 962435) B962435
theorem B674393 : Blo 447780 674393 := bstep (se 2 (by rfl) ⟨252897, by rfl⟩ : syracuseStep 674393 = 505795) B505795
theorem B1919639 : Blo 447780 1919639 := bstep (se 1 (by rfl) ⟨1439729, by rfl⟩ : syracuseStep 1919639 = 2879459) B2879459
theorem B674507 : Blo 447780 674507 := bstep (se 1 (by rfl) ⟨505880, by rfl⟩ : syracuseStep 674507 = 1011761) B1011761
theorem B674519 : Blo 447780 674519 := bstep (se 1 (by rfl) ⟨505889, by rfl⟩ : syracuseStep 674519 = 1011779) B1011779
theorem B674585 : Blo 447780 674585 := bstep (se 2 (by rfl) ⟨252969, by rfl⟩ : syracuseStep 674585 = 505939) B505939
theorem B674699 : Blo 447780 674699 := bstep (se 1 (by rfl) ⟨506024, by rfl⟩ : syracuseStep 674699 = 1012049) B1012049
theorem B674711 : Blo 447780 674711 := bstep (se 1 (by rfl) ⟨506033, by rfl⟩ : syracuseStep 674711 = 1012067) B1012067
theorem B674777 : Blo 447780 674777 := bstep (se 2 (by rfl) ⟨253041, by rfl⟩ : syracuseStep 674777 = 506083) B506083
theorem B674891 : Blo 447780 674891 := bstep (se 1 (by rfl) ⟨506168, by rfl⟩ : syracuseStep 674891 = 1012337) B1012337
theorem B674903 : Blo 447780 674903 := bstep (se 1 (by rfl) ⟨506177, by rfl⟩ : syracuseStep 674903 = 1012355) B1012355
theorem B674969 : Blo 447780 674969 := bstep (se 2 (by rfl) ⟨253113, by rfl⟩ : syracuseStep 674969 = 506227) B506227
theorem B1133747 : Blo 447780 1133747 := bstep (se 1 (by rfl) ⟨850310, by rfl⟩ : syracuseStep 1133747 = 1700621) B1700621
theorem B675083 : Blo 447780 675083 := bstep (se 1 (by rfl) ⟨506312, by rfl⟩ : syracuseStep 675083 = 1012625) B1012625
theorem B675095 : Blo 447780 675095 := bstep (se 1 (by rfl) ⟨506321, by rfl⟩ : syracuseStep 675095 = 1012643) B1012643
theorem B1920307 : Blo 447780 1920307 := bstep (se 1 (by rfl) ⟨1440230, by rfl⟩ : syracuseStep 1920307 = 2880461) B2880461
theorem B675161 : Blo 447780 675161 := bstep (se 2 (by rfl) ⟨253185, by rfl⟩ : syracuseStep 675161 = 506371) B506371
theorem B2280797 : Blo 447780 2280797 := bstep (se 3 (by rfl) ⟨427649, by rfl⟩ : syracuseStep 2280797 = 855299) B855299
theorem B1723841 : Blo 447780 1723841 := bstep (se 2 (by rfl) ⟨646440, by rfl⟩ : syracuseStep 1723841 = 1292881) B1292881
theorem B675275 : Blo 447780 675275 := bstep (se 1 (by rfl) ⟨506456, by rfl⟩ : syracuseStep 675275 = 1012913) B1012913
theorem B675287 : Blo 447780 675287 := bstep (se 1 (by rfl) ⟨506465, by rfl⟩ : syracuseStep 675287 = 1012931) B1012931
theorem B675353 : Blo 447780 675353 := bstep (se 2 (by rfl) ⟨253257, by rfl⟩ : syracuseStep 675353 = 506515) B506515
theorem B675467 : Blo 447780 675467 := bstep (se 1 (by rfl) ⟨506600, by rfl⟩ : syracuseStep 675467 = 1013201) B1013201
theorem B675479 : Blo 447780 675479 := bstep (se 1 (by rfl) ⟨506609, by rfl⟩ : syracuseStep 675479 = 1013219) B1013219
theorem B1134283 : Blo 447780 1134283 := bstep (se 1 (by rfl) ⟨850712, by rfl⟩ : syracuseStep 1134283 = 1701425) B1701425
theorem B675545 : Blo 447780 675545 := bstep (se 2 (by rfl) ⟨253329, by rfl⟩ : syracuseStep 675545 = 506659) B506659
theorem B3067723 : Blo 447780 3067723 := bstep (se 1 (by rfl) ⟨2300792, by rfl⟩ : syracuseStep 3067723 = 4601585) B4601585
theorem B675659 : Blo 447780 675659 := bstep (se 1 (by rfl) ⟨506744, by rfl⟩ : syracuseStep 675659 = 1013489) B1013489
theorem B675671 : Blo 447780 675671 := bstep (se 1 (by rfl) ⟨506753, by rfl⟩ : syracuseStep 675671 = 1013507) B1013507
theorem B1134425 : Blo 447780 1134425 := bstep (se 2 (by rfl) ⟨425409, by rfl⟩ : syracuseStep 1134425 = 850819) B850819
theorem B675737 : Blo 447780 675737 := bstep (se 2 (by rfl) ⟨253401, by rfl⟩ : syracuseStep 675737 = 506803) B506803
theorem B675851 : Blo 447780 675851 := bstep (se 1 (by rfl) ⟨506888, by rfl⟩ : syracuseStep 675851 = 1013777) B1013777
theorem B675863 : Blo 447780 675863 := bstep (se 1 (by rfl) ⟨506897, by rfl⟩ : syracuseStep 675863 = 1013795) B1013795
theorem B610327 : Blo 447780 610327 := bstep (se 1 (by rfl) ⟨457745, by rfl⟩ : syracuseStep 610327 = 915491) B915491
theorem B970841 : Blo 447780 970841 := bstep (se 2 (by rfl) ⟨364065, by rfl⟩ : syracuseStep 970841 = 728131) B728131
theorem B675929 : Blo 447780 675929 := bstep (se 2 (by rfl) ⟨253473, by rfl⟩ : syracuseStep 675929 = 506947) B506947
theorem B1626257 : Blo 447780 1626257 := bstep (se 2 (by rfl) ⟨609846, by rfl⟩ : syracuseStep 1626257 = 1219693) B1219693
theorem B676043 : Blo 447780 676043 := bstep (se 1 (by rfl) ⟨507032, by rfl⟩ : syracuseStep 676043 = 1014065) B1014065
theorem B676055 : Blo 447780 676055 := bstep (se 1 (by rfl) ⟨507041, by rfl⟩ : syracuseStep 676055 = 1014083) B1014083
theorem B676121 : Blo 447780 676121 := bstep (se 2 (by rfl) ⟨253545, by rfl⟩ : syracuseStep 676121 = 507091) B507091
theorem B676235 : Blo 447780 676235 := bstep (se 1 (by rfl) ⟨507176, by rfl⟩ : syracuseStep 676235 = 1014353) B1014353
theorem B676247 : Blo 447780 676247 := bstep (se 1 (by rfl) ⟨507185, by rfl⟩ : syracuseStep 676247 = 1014371) B1014371
theorem B676313 : Blo 447780 676313 := bstep (se 2 (by rfl) ⟨253617, by rfl⟩ : syracuseStep 676313 = 507235) B507235
theorem B1921553 : Blo 447780 1921553 := bstep (se 2 (by rfl) ⟨720582, by rfl⟩ : syracuseStep 1921553 = 1441165) B1441165
theorem B807499 : Blo 447780 807499 := bstep (se 1 (by rfl) ⟨605624, by rfl⟩ : syracuseStep 807499 = 1211249) B1211249
theorem B676427 : Blo 447780 676427 := bstep (se 1 (by rfl) ⟨507320, by rfl⟩ : syracuseStep 676427 = 1014641) B1014641
theorem B676439 : Blo 447780 676439 := bstep (se 1 (by rfl) ⟨507329, by rfl⟩ : syracuseStep 676439 = 1014659) B1014659
theorem B1135255 : Blo 447780 1135255 := bstep (se 1 (by rfl) ⟨851441, by rfl⟩ : syracuseStep 1135255 = 1702883) B1702883
theorem B676505 : Blo 447780 676505 := bstep (se 2 (by rfl) ⟨253689, by rfl⟩ : syracuseStep 676505 = 507379) B507379
theorem B971531 : Blo 447780 971531 := bstep (se 1 (by rfl) ⟨728648, by rfl⟩ : syracuseStep 971531 = 1457297) B1457297
theorem B676619 : Blo 447780 676619 := bstep (se 1 (by rfl) ⟨507464, by rfl⟩ : syracuseStep 676619 = 1014929) B1014929
theorem B676631 : Blo 447780 676631 := bstep (se 1 (by rfl) ⟨507473, by rfl⟩ : syracuseStep 676631 = 1014947) B1014947
theorem B480043 : Blo 447780 480043 := bstep (se 1 (by rfl) ⟨360032, by rfl⟩ : syracuseStep 480043 = 720065) B720065
theorem B676697 : Blo 447780 676697 := bstep (se 2 (by rfl) ⟨253761, by rfl⟩ : syracuseStep 676697 = 507523) B507523
theorem B676811 : Blo 447780 676811 := bstep (se 1 (by rfl) ⟨507608, by rfl⟩ : syracuseStep 676811 = 1015217) B1015217
theorem B676823 : Blo 447780 676823 := bstep (se 1 (by rfl) ⟨507617, by rfl⟩ : syracuseStep 676823 = 1015235) B1015235
theorem B676889 : Blo 447780 676889 := bstep (se 2 (by rfl) ⟨253833, by rfl⟩ : syracuseStep 676889 = 507667) B507667
theorem B2774081 : Blo 447780 2774081 := bstep (se 2 (by rfl) ⟨1040280, by rfl⟩ : syracuseStep 2774081 = 2080561) B2080561
theorem B1135691 : Blo 447780 1135691 := bstep (se 1 (by rfl) ⟨851768, by rfl⟩ : syracuseStep 1135691 = 1703537) B1703537
theorem B677003 : Blo 447780 677003 := bstep (se 1 (by rfl) ⟨507752, by rfl⟩ : syracuseStep 677003 = 1015505) B1015505
theorem B677015 : Blo 447780 677015 := bstep (se 1 (by rfl) ⟨507761, by rfl⟩ : syracuseStep 677015 = 1015523) B1015523
theorem B677081 : Blo 447780 677081 := bstep (se 2 (by rfl) ⟨253905, by rfl⟩ : syracuseStep 677081 = 507811) B507811
theorem B447787 : Blo 447780 447787 := bstep (se 1 (by rfl) ⟨335840, by rfl⟩ : syracuseStep 447787 = 671681) B671681
theorem B447799 : Blo 447780 447799 := bstep (se 1 (by rfl) ⟨335849, by rfl⟩ : syracuseStep 447799 = 671699) B671699
theorem B447819 : Blo 447780 447819 := bstep (se 1 (by rfl) ⟨335864, by rfl⟩ : syracuseStep 447819 = 671729) B671729
theorem B677195 : Blo 447780 677195 := bstep (se 1 (by rfl) ⟨507896, by rfl⟩ : syracuseStep 677195 = 1015793) B1015793
theorem B447831 : Blo 447780 447831 := bstep (se 1 (by rfl) ⟨335873, by rfl⟩ : syracuseStep 447831 = 671747) B671747
theorem B677207 : Blo 447780 677207 := bstep (se 1 (by rfl) ⟨507905, by rfl⟩ : syracuseStep 677207 = 1015811) B1015811
theorem B447851 : Blo 447780 447851 := bstep (se 1 (by rfl) ⟨335888, by rfl⟩ : syracuseStep 447851 = 671777) B671777
theorem B447863 : Blo 447780 447863 := bstep (se 1 (by rfl) ⟨335897, by rfl⟩ : syracuseStep 447863 = 671795) B671795
theorem B808321 : Blo 447780 808321 := bstep (se 2 (by rfl) ⟨303120, by rfl⟩ : syracuseStep 808321 = 606241) B606241
theorem B447883 : Blo 447780 447883 := bstep (se 1 (by rfl) ⟨335912, by rfl⟩ : syracuseStep 447883 = 671825) B671825
theorem B447895 : Blo 447780 447895 := bstep (se 1 (by rfl) ⟨335921, by rfl⟩ : syracuseStep 447895 = 671843) B671843
theorem B2282903 : Blo 447780 2282903 := bstep (se 1 (by rfl) ⟨1712177, by rfl⟩ : syracuseStep 2282903 = 3424355) B3424355
theorem B677273 : Blo 447780 677273 := bstep (se 2 (by rfl) ⟨253977, by rfl⟩ : syracuseStep 677273 = 507955) B507955
theorem B447915 : Blo 447780 447915 := bstep (se 1 (by rfl) ⟨335936, by rfl⟩ : syracuseStep 447915 = 671873) B671873
theorem B5854643 : Blo 447780 5854643 := bstep (se 1 (by rfl) ⟨4390982, by rfl⟩ : syracuseStep 5854643 = 8781965) B8781965
theorem B447927 : Blo 447780 447927 := bstep (se 1 (by rfl) ⟨335945, by rfl⟩ : syracuseStep 447927 = 671891) B671891
theorem B1136065 : Blo 447780 1136065 := bstep (se 2 (by rfl) ⟨426024, by rfl⟩ : syracuseStep 1136065 = 852049) B852049
theorem B447947 : Blo 447780 447947 := bstep (se 1 (by rfl) ⟨335960, by rfl⟩ : syracuseStep 447947 = 671921) B671921
theorem B447959 : Blo 447780 447959 := bstep (se 1 (by rfl) ⟨335969, by rfl⟩ : syracuseStep 447959 = 671939) B671939
theorem B447979 : Blo 447780 447979 := bstep (se 1 (by rfl) ⟨335984, by rfl⟩ : syracuseStep 447979 = 671969) B671969
theorem B447991 : Blo 447780 447991 := bstep (se 1 (by rfl) ⟨335993, by rfl⟩ : syracuseStep 447991 = 671987) B671987
theorem B448011 : Blo 447780 448011 := bstep (se 1 (by rfl) ⟨336008, by rfl⟩ : syracuseStep 448011 = 672017) B672017
theorem B677387 : Blo 447780 677387 := bstep (se 1 (by rfl) ⟨508040, by rfl⟩ : syracuseStep 677387 = 1016081) B1016081
theorem B448023 : Blo 447780 448023 := bstep (se 1 (by rfl) ⟨336017, by rfl⟩ : syracuseStep 448023 = 672035) B672035
theorem B677399 : Blo 447780 677399 := bstep (se 1 (by rfl) ⟨508049, by rfl⟩ : syracuseStep 677399 = 1016099) B1016099
theorem B6477347 : Blo 447780 6477347 := bstep (se 1 (by rfl) ⟨4858010, by rfl⟩ : syracuseStep 6477347 = 9716021) B9716021
theorem B448043 : Blo 447780 448043 := bstep (se 1 (by rfl) ⟨336032, by rfl⟩ : syracuseStep 448043 = 672065) B672065
theorem B448055 : Blo 447780 448055 := bstep (se 1 (by rfl) ⟨336041, by rfl⟩ : syracuseStep 448055 = 672083) B672083
theorem B1955393 : Blo 447780 1955393 := bstep (se 2 (by rfl) ⟨733272, by rfl⟩ : syracuseStep 1955393 = 1466545) B1466545
theorem B448075 : Blo 447780 448075 := bstep (se 1 (by rfl) ⟨336056, by rfl⟩ : syracuseStep 448075 = 672113) B672113
theorem B448087 : Blo 447780 448087 := bstep (se 1 (by rfl) ⟨336065, by rfl⟩ : syracuseStep 448087 = 672131) B672131
theorem B808537 : Blo 447780 808537 := bstep (se 2 (by rfl) ⟨303201, by rfl⟩ : syracuseStep 808537 = 606403) B606403
theorem B677465 : Blo 447780 677465 := bstep (se 2 (by rfl) ⟨254049, by rfl⟩ : syracuseStep 677465 = 508099) B508099
theorem B448107 : Blo 447780 448107 := bstep (se 1 (by rfl) ⟨336080, by rfl⟩ : syracuseStep 448107 = 672161) B672161
theorem B448119 : Blo 447780 448119 := bstep (se 1 (by rfl) ⟨336089, by rfl⟩ : syracuseStep 448119 = 672179) B672179
theorem B448139 : Blo 447780 448139 := bstep (se 1 (by rfl) ⟨336104, by rfl⟩ : syracuseStep 448139 = 672209) B672209
theorem B448151 : Blo 447780 448151 := bstep (se 1 (by rfl) ⟨336113, by rfl⟩ : syracuseStep 448151 = 672227) B672227
theorem B448171 : Blo 447780 448171 := bstep (se 1 (by rfl) ⟨336128, by rfl⟩ : syracuseStep 448171 = 672257) B672257
theorem B448183 : Blo 447780 448183 := bstep (se 1 (by rfl) ⟨336137, by rfl⟩ : syracuseStep 448183 = 672275) B672275
theorem B448203 : Blo 447780 448203 := bstep (se 1 (by rfl) ⟨336152, by rfl⟩ : syracuseStep 448203 = 672305) B672305
theorem B677579 : Blo 447780 677579 := bstep (se 1 (by rfl) ⟨508184, by rfl⟩ : syracuseStep 677579 = 1016369) B1016369
theorem B448215 : Blo 447780 448215 := bstep (se 1 (by rfl) ⟨336161, by rfl⟩ : syracuseStep 448215 = 672323) B672323
theorem B677591 : Blo 447780 677591 := bstep (se 1 (by rfl) ⟨508193, by rfl⟩ : syracuseStep 677591 = 1016387) B1016387
theorem B448235 : Blo 447780 448235 := bstep (se 1 (by rfl) ⟨336176, by rfl⟩ : syracuseStep 448235 = 672353) B672353
theorem B448247 : Blo 447780 448247 := bstep (se 1 (by rfl) ⟨336185, by rfl⟩ : syracuseStep 448247 = 672371) B672371
theorem B448267 : Blo 447780 448267 := bstep (se 1 (by rfl) ⟨336200, by rfl⟩ : syracuseStep 448267 = 672401) B672401
theorem B448279 : Blo 447780 448279 := bstep (se 1 (by rfl) ⟨336209, by rfl⟩ : syracuseStep 448279 = 672419) B672419
theorem B677657 : Blo 447780 677657 := bstep (se 2 (by rfl) ⟨254121, by rfl⟩ : syracuseStep 677657 = 508243) B508243
theorem B448299 : Blo 447780 448299 := bstep (se 1 (by rfl) ⟨336224, by rfl⟩ : syracuseStep 448299 = 672449) B672449
theorem B448311 : Blo 447780 448311 := bstep (se 1 (by rfl) ⟨336233, by rfl⟩ : syracuseStep 448311 = 672467) B672467
theorem B448331 : Blo 447780 448331 := bstep (se 1 (by rfl) ⟨336248, by rfl⟩ : syracuseStep 448331 = 672497) B672497
theorem B448343 : Blo 447780 448343 := bstep (se 1 (by rfl) ⟨336257, by rfl⟩ : syracuseStep 448343 = 672515) B672515
theorem B448363 : Blo 447780 448363 := bstep (se 1 (by rfl) ⟨336272, by rfl⟩ : syracuseStep 448363 = 672545) B672545
theorem B448375 : Blo 447780 448375 := bstep (se 1 (by rfl) ⟨336281, by rfl⟩ : syracuseStep 448375 = 672563) B672563
theorem B448395 : Blo 447780 448395 := bstep (se 1 (by rfl) ⟨336296, by rfl⟩ : syracuseStep 448395 = 672593) B672593
theorem B448407 : Blo 447780 448407 := bstep (se 1 (by rfl) ⟨336305, by rfl⟩ : syracuseStep 448407 = 672611) B672611
theorem B448427 : Blo 447780 448427 := bstep (se 1 (by rfl) ⟨336320, by rfl⟩ : syracuseStep 448427 = 672641) B672641
theorem B808883 : Blo 447780 808883 := bstep (se 1 (by rfl) ⟨606662, by rfl⟩ : syracuseStep 808883 = 1213325) B1213325
theorem B448439 : Blo 447780 448439 := bstep (se 1 (by rfl) ⟨336329, by rfl⟩ : syracuseStep 448439 = 672659) B672659
theorem B448459 : Blo 447780 448459 := bstep (se 1 (by rfl) ⟨336344, by rfl⟩ : syracuseStep 448459 = 672689) B672689
theorem B448471 : Blo 447780 448471 := bstep (se 1 (by rfl) ⟨336353, by rfl⟩ : syracuseStep 448471 = 672707) B672707
theorem B448491 : Blo 447780 448491 := bstep (se 1 (by rfl) ⟨336368, by rfl⟩ : syracuseStep 448491 = 672737) B672737
theorem B448503 : Blo 447780 448503 := bstep (se 1 (by rfl) ⟨336377, by rfl⟩ : syracuseStep 448503 = 672755) B672755
theorem B448523 : Blo 447780 448523 := bstep (se 1 (by rfl) ⟨336392, by rfl⟩ : syracuseStep 448523 = 672785) B672785
theorem B448535 : Blo 447780 448535 := bstep (se 1 (by rfl) ⟨336401, by rfl⟩ : syracuseStep 448535 = 672803) B672803
theorem B1136663 : Blo 447780 1136663 := bstep (se 1 (by rfl) ⟨852497, by rfl⟩ : syracuseStep 1136663 = 1704995) B1704995
theorem B448555 : Blo 447780 448555 := bstep (se 1 (by rfl) ⟨336416, by rfl⟩ : syracuseStep 448555 = 672833) B672833
theorem B448567 : Blo 447780 448567 := bstep (se 1 (by rfl) ⟨336425, by rfl⟩ : syracuseStep 448567 = 672851) B672851
theorem B448587 : Blo 447780 448587 := bstep (se 1 (by rfl) ⟨336440, by rfl⟩ : syracuseStep 448587 = 672881) B672881
theorem B448599 : Blo 447780 448599 := bstep (se 1 (by rfl) ⟨336449, by rfl⟩ : syracuseStep 448599 = 672899) B672899
theorem B448619 : Blo 447780 448619 := bstep (se 1 (by rfl) ⟨336464, by rfl⟩ : syracuseStep 448619 = 672929) B672929
theorem B448631 : Blo 447780 448631 := bstep (se 1 (by rfl) ⟨336473, by rfl⟩ : syracuseStep 448631 = 672947) B672947
theorem B448651 : Blo 447780 448651 := bstep (se 1 (by rfl) ⟨336488, by rfl⟩ : syracuseStep 448651 = 672977) B672977
theorem B546955 : Blo 447780 546955 := bstep (se 1 (by rfl) ⟨410216, by rfl⟩ : syracuseStep 546955 = 820433) B820433
theorem B448663 : Blo 447780 448663 := bstep (se 1 (by rfl) ⟨336497, by rfl⟩ : syracuseStep 448663 = 672995) B672995
theorem B448683 : Blo 447780 448683 := bstep (se 1 (by rfl) ⟨336512, by rfl⟩ : syracuseStep 448683 = 673025) B673025
theorem B448695 : Blo 447780 448695 := bstep (se 1 (by rfl) ⟨336521, by rfl⟩ : syracuseStep 448695 = 673043) B673043
theorem B448715 : Blo 447780 448715 := bstep (se 1 (by rfl) ⟨336536, by rfl⟩ : syracuseStep 448715 = 673073) B673073
theorem B448727 : Blo 447780 448727 := bstep (se 1 (by rfl) ⟨336545, by rfl⟩ : syracuseStep 448727 = 673091) B673091
theorem B448747 : Blo 447780 448747 := bstep (se 1 (by rfl) ⟨336560, by rfl⟩ : syracuseStep 448747 = 673121) B673121
theorem B448759 : Blo 447780 448759 := bstep (se 1 (by rfl) ⟨336569, by rfl⟩ : syracuseStep 448759 = 673139) B673139
theorem B9230597 : Blo 447780 9230597 := bstep (se 4 (by rfl) ⟨865368, by rfl⟩ : syracuseStep 9230597 = 1730737) B1730737
theorem B448779 : Blo 447780 448779 := bstep (se 1 (by rfl) ⟨336584, by rfl⟩ : syracuseStep 448779 = 673169) B673169
theorem B3430673 : Blo 447780 3430673 := bstep (se 2 (by rfl) ⟨1286502, by rfl⟩ : syracuseStep 3430673 = 2573005) B2573005
theorem B448791 : Blo 447780 448791 := bstep (se 1 (by rfl) ⟨336593, by rfl⟩ : syracuseStep 448791 = 673187) B673187
theorem B448811 : Blo 447780 448811 := bstep (se 1 (by rfl) ⟨336608, by rfl⟩ : syracuseStep 448811 = 673217) B673217
theorem B448823 : Blo 447780 448823 := bstep (se 1 (by rfl) ⟨336617, by rfl⟩ : syracuseStep 448823 = 673235) B673235
theorem B448843 : Blo 447780 448843 := bstep (se 1 (by rfl) ⟨336632, by rfl⟩ : syracuseStep 448843 = 673265) B673265
theorem B842071 : Blo 447780 842071 := bstep (se 1 (by rfl) ⟨631553, by rfl⟩ : syracuseStep 842071 = 1263107) B1263107
theorem B448855 : Blo 447780 448855 := bstep (se 1 (by rfl) ⟨336641, by rfl⟩ : syracuseStep 448855 = 673283) B673283
theorem B448875 : Blo 447780 448875 := bstep (se 1 (by rfl) ⟨336656, by rfl⟩ : syracuseStep 448875 = 673313) B673313
theorem B448887 : Blo 447780 448887 := bstep (se 1 (by rfl) ⟨336665, by rfl⟩ : syracuseStep 448887 = 673331) B673331
theorem B809345 : Blo 447780 809345 := bstep (se 2 (by rfl) ⟨303504, by rfl⟩ : syracuseStep 809345 = 607009) B607009
theorem B448907 : Blo 447780 448907 := bstep (se 1 (by rfl) ⟨336680, by rfl⟩ : syracuseStep 448907 = 673361) B673361
theorem B448919 : Blo 447780 448919 := bstep (se 1 (by rfl) ⟨336689, by rfl⟩ : syracuseStep 448919 = 673379) B673379
theorem B448939 : Blo 447780 448939 := bstep (se 1 (by rfl) ⟨336704, by rfl⟩ : syracuseStep 448939 = 673409) B673409
theorem B448951 : Blo 447780 448951 := bstep (se 1 (by rfl) ⟨336713, by rfl⟩ : syracuseStep 448951 = 673427) B673427
theorem B448971 : Blo 447780 448971 := bstep (se 1 (by rfl) ⟨336728, by rfl⟩ : syracuseStep 448971 = 673457) B673457
theorem B448983 : Blo 447780 448983 := bstep (se 1 (by rfl) ⟨336737, by rfl⟩ : syracuseStep 448983 = 673475) B673475
theorem B449003 : Blo 447780 449003 := bstep (se 1 (by rfl) ⟨336752, by rfl⟩ : syracuseStep 449003 = 673505) B673505
theorem B449015 : Blo 447780 449015 := bstep (se 1 (by rfl) ⟨336761, by rfl⟩ : syracuseStep 449015 = 673523) B673523
theorem B449035 : Blo 447780 449035 := bstep (se 1 (by rfl) ⟨336776, by rfl⟩ : syracuseStep 449035 = 673553) B673553
theorem B449047 : Blo 447780 449047 := bstep (se 1 (by rfl) ⟨336785, by rfl⟩ : syracuseStep 449047 = 673571) B673571
theorem B449067 : Blo 447780 449067 := bstep (se 1 (by rfl) ⟨336800, by rfl⟩ : syracuseStep 449067 = 673601) B673601
theorem B449079 : Blo 447780 449079 := bstep (se 1 (by rfl) ⟨336809, by rfl⟩ : syracuseStep 449079 = 673619) B673619
theorem B449099 : Blo 447780 449099 := bstep (se 1 (by rfl) ⟨336824, by rfl⟩ : syracuseStep 449099 = 673649) B673649
theorem B449111 : Blo 447780 449111 := bstep (se 1 (by rfl) ⟨336833, by rfl⟩ : syracuseStep 449111 = 673667) B673667
theorem B449131 : Blo 447780 449131 := bstep (se 1 (by rfl) ⟨336848, by rfl⟩ : syracuseStep 449131 = 673697) B673697
theorem B449143 : Blo 447780 449143 := bstep (se 1 (by rfl) ⟨336857, by rfl⟩ : syracuseStep 449143 = 673715) B673715
theorem B449163 : Blo 447780 449163 := bstep (se 1 (by rfl) ⟨336872, by rfl⟩ : syracuseStep 449163 = 673745) B673745
theorem B449175 : Blo 447780 449175 := bstep (se 1 (by rfl) ⟨336881, by rfl⟩ : syracuseStep 449175 = 673763) B673763
theorem B449195 : Blo 447780 449195 := bstep (se 1 (by rfl) ⟨336896, by rfl⟩ : syracuseStep 449195 = 673793) B673793
theorem B449207 : Blo 447780 449207 := bstep (se 1 (by rfl) ⟨336905, by rfl⟩ : syracuseStep 449207 = 673811) B673811
theorem B449227 : Blo 447780 449227 := bstep (se 1 (by rfl) ⟨336920, by rfl⟩ : syracuseStep 449227 = 673841) B673841
theorem B449239 : Blo 447780 449239 := bstep (se 1 (by rfl) ⟨336929, by rfl⟩ : syracuseStep 449239 = 673859) B673859
theorem B449259 : Blo 447780 449259 := bstep (se 1 (by rfl) ⟨336944, by rfl⟩ : syracuseStep 449259 = 673889) B673889
theorem B449271 : Blo 447780 449271 := bstep (se 1 (by rfl) ⟨336953, by rfl⟩ : syracuseStep 449271 = 673907) B673907
theorem B449291 : Blo 447780 449291 := bstep (se 1 (by rfl) ⟨336968, by rfl⟩ : syracuseStep 449291 = 673937) B673937
theorem B482059 : Blo 447780 482059 := bstep (se 1 (by rfl) ⟨361544, by rfl⟩ : syracuseStep 482059 = 723089) B723089
theorem B449303 : Blo 447780 449303 := bstep (se 1 (by rfl) ⟨336977, by rfl⟩ : syracuseStep 449303 = 673955) B673955
theorem B449323 : Blo 447780 449323 := bstep (se 1 (by rfl) ⟨336992, by rfl⟩ : syracuseStep 449323 = 673985) B673985
theorem B449335 : Blo 447780 449335 := bstep (se 1 (by rfl) ⟨337001, by rfl⟩ : syracuseStep 449335 = 674003) B674003
theorem B1137473 : Blo 447780 1137473 := bstep (se 2 (by rfl) ⟨426552, by rfl⟩ : syracuseStep 1137473 = 853105) B853105
theorem B449355 : Blo 447780 449355 := bstep (se 1 (by rfl) ⟨337016, by rfl⟩ : syracuseStep 449355 = 674033) B674033
theorem B449367 : Blo 447780 449367 := bstep (se 1 (by rfl) ⟨337025, by rfl⟩ : syracuseStep 449367 = 674051) B674051
theorem B5561189 : Blo 447780 5561189 := bstep (se 4 (by rfl) ⟨521361, by rfl⟩ : syracuseStep 5561189 = 1042723) B1042723
theorem B449387 : Blo 447780 449387 := bstep (se 1 (by rfl) ⟨337040, by rfl⟩ : syracuseStep 449387 = 674081) B674081
theorem B449399 : Blo 447780 449399 := bstep (se 1 (by rfl) ⟨337049, by rfl⟩ : syracuseStep 449399 = 674099) B674099
theorem B449419 : Blo 447780 449419 := bstep (se 1 (by rfl) ⟨337064, by rfl⟩ : syracuseStep 449419 = 674129) B674129
theorem B449431 : Blo 447780 449431 := bstep (se 1 (by rfl) ⟨337073, by rfl⟩ : syracuseStep 449431 = 674147) B674147
theorem B449451 : Blo 447780 449451 := bstep (se 1 (by rfl) ⟨337088, by rfl⟩ : syracuseStep 449451 = 674177) B674177
theorem B1924013 : Blo 447780 1924013 := bstep (se 3 (by rfl) ⟨360752, by rfl⟩ : syracuseStep 1924013 = 721505) B721505
theorem B1727411 : Blo 447780 1727411 := bstep (se 1 (by rfl) ⟨1295558, by rfl⟩ : syracuseStep 1727411 = 2591117) B2591117
theorem B3431347 : Blo 447780 3431347 := bstep (se 1 (by rfl) ⟨2573510, by rfl⟩ : syracuseStep 3431347 = 5147021) B5147021
theorem B449463 : Blo 447780 449463 := bstep (se 1 (by rfl) ⟨337097, by rfl⟩ : syracuseStep 449463 = 674195) B674195
theorem B449483 : Blo 447780 449483 := bstep (se 1 (by rfl) ⟨337112, by rfl⟩ : syracuseStep 449483 = 674225) B674225
theorem B449495 : Blo 447780 449495 := bstep (se 1 (by rfl) ⟨337121, by rfl⟩ : syracuseStep 449495 = 674243) B674243
theorem B449515 : Blo 447780 449515 := bstep (se 1 (by rfl) ⟨337136, by rfl⟩ : syracuseStep 449515 = 674273) B674273
theorem B449527 : Blo 447780 449527 := bstep (se 1 (by rfl) ⟨337145, by rfl⟩ : syracuseStep 449527 = 674291) B674291
theorem B449547 : Blo 447780 449547 := bstep (se 1 (by rfl) ⟨337160, by rfl⟩ : syracuseStep 449547 = 674321) B674321
theorem B449559 : Blo 447780 449559 := bstep (se 1 (by rfl) ⟨337169, by rfl⟩ : syracuseStep 449559 = 674339) B674339
theorem B449579 : Blo 447780 449579 := bstep (se 1 (by rfl) ⟨337184, by rfl⟩ : syracuseStep 449579 = 674369) B674369
theorem B449591 : Blo 447780 449591 := bstep (se 1 (by rfl) ⟨337193, by rfl⟩ : syracuseStep 449591 = 674387) B674387
theorem B449611 : Blo 447780 449611 := bstep (se 1 (by rfl) ⟨337208, by rfl⟩ : syracuseStep 449611 = 674417) B674417
theorem B449623 : Blo 447780 449623 := bstep (se 1 (by rfl) ⟨337217, by rfl⟩ : syracuseStep 449623 = 674435) B674435
theorem B8313949 : Blo 447780 8313949 := bstep (se 3 (by rfl) ⟨1558865, by rfl⟩ : syracuseStep 8313949 = 3117731) B3117731
theorem B449643 : Blo 447780 449643 := bstep (se 1 (by rfl) ⟨337232, by rfl⟩ : syracuseStep 449643 = 674465) B674465
theorem B449655 : Blo 447780 449655 := bstep (se 1 (by rfl) ⟨337241, by rfl⟩ : syracuseStep 449655 = 674483) B674483
theorem B449675 : Blo 447780 449675 := bstep (se 1 (by rfl) ⟨337256, by rfl⟩ : syracuseStep 449675 = 674513) B674513
theorem B449687 : Blo 447780 449687 := bstep (se 1 (by rfl) ⟨337265, by rfl⟩ : syracuseStep 449687 = 674531) B674531
theorem B810137 : Blo 447780 810137 := bstep (se 2 (by rfl) ⟨303801, by rfl⟩ : syracuseStep 810137 = 607603) B607603
theorem B449707 : Blo 447780 449707 := bstep (se 1 (by rfl) ⟨337280, by rfl⟩ : syracuseStep 449707 = 674561) B674561
theorem B449719 : Blo 447780 449719 := bstep (se 1 (by rfl) ⟨337289, by rfl⟩ : syracuseStep 449719 = 674579) B674579
theorem B449739 : Blo 447780 449739 := bstep (se 1 (by rfl) ⟨337304, by rfl⟩ : syracuseStep 449739 = 674609) B674609
theorem B449751 : Blo 447780 449751 := bstep (se 1 (by rfl) ⟨337313, by rfl⟩ : syracuseStep 449751 = 674627) B674627
theorem B449771 : Blo 447780 449771 := bstep (se 1 (by rfl) ⟨337328, by rfl⟩ : syracuseStep 449771 = 674657) B674657
theorem B449783 : Blo 447780 449783 := bstep (se 1 (by rfl) ⟨337337, by rfl⟩ : syracuseStep 449783 = 674675) B674675
theorem B449803 : Blo 447780 449803 := bstep (se 1 (by rfl) ⟨337352, by rfl⟩ : syracuseStep 449803 = 674705) B674705
theorem B449815 : Blo 447780 449815 := bstep (se 1 (by rfl) ⟨337361, by rfl⟩ : syracuseStep 449815 = 674723) B674723
theorem B449835 : Blo 447780 449835 := bstep (se 1 (by rfl) ⟨337376, by rfl⟩ : syracuseStep 449835 = 674753) B674753
theorem B449847 : Blo 447780 449847 := bstep (se 1 (by rfl) ⟨337385, by rfl⟩ : syracuseStep 449847 = 674771) B674771
theorem B449867 : Blo 447780 449867 := bstep (se 1 (by rfl) ⟨337400, by rfl⟩ : syracuseStep 449867 = 674801) B674801
theorem B449879 : Blo 447780 449879 := bstep (se 1 (by rfl) ⟨337409, by rfl⟩ : syracuseStep 449879 = 674819) B674819
theorem B1138009 : Blo 447780 1138009 := bstep (se 2 (by rfl) ⟨426753, by rfl⟩ : syracuseStep 1138009 = 853507) B853507
theorem B449899 : Blo 447780 449899 := bstep (se 1 (by rfl) ⟨337424, by rfl⟩ : syracuseStep 449899 = 674849) B674849
theorem B449911 : Blo 447780 449911 := bstep (se 1 (by rfl) ⟨337433, by rfl⟩ : syracuseStep 449911 = 674867) B674867
theorem B449931 : Blo 447780 449931 := bstep (se 1 (by rfl) ⟨337448, by rfl⟩ : syracuseStep 449931 = 674897) B674897
theorem B449943 : Blo 447780 449943 := bstep (se 1 (by rfl) ⟨337457, by rfl⟩ : syracuseStep 449943 = 674915) B674915
theorem B449963 : Blo 447780 449963 := bstep (se 1 (by rfl) ⟨337472, by rfl⟩ : syracuseStep 449963 = 674945) B674945
theorem B449975 : Blo 447780 449975 := bstep (se 1 (by rfl) ⟨337481, by rfl⟩ : syracuseStep 449975 = 674963) B674963
theorem B449995 : Blo 447780 449995 := bstep (se 1 (by rfl) ⟨337496, by rfl⟩ : syracuseStep 449995 = 674993) B674993
theorem B548299 : Blo 447780 548299 := bstep (se 1 (by rfl) ⟨411224, by rfl⟩ : syracuseStep 548299 = 822449) B822449
theorem B450007 : Blo 447780 450007 := bstep (se 1 (by rfl) ⟨337505, by rfl⟩ : syracuseStep 450007 = 675011) B675011
theorem B2153945 : Blo 447780 2153945 := bstep (se 2 (by rfl) ⟨807729, by rfl⟩ : syracuseStep 2153945 = 1615459) B1615459
theorem B450027 : Blo 447780 450027 := bstep (se 1 (by rfl) ⟨337520, by rfl⟩ : syracuseStep 450027 = 675041) B675041
theorem B450039 : Blo 447780 450039 := bstep (se 1 (by rfl) ⟨337529, by rfl⟩ : syracuseStep 450039 = 675059) B675059
theorem B908801 : Blo 447780 908801 := bstep (se 2 (by rfl) ⟨340800, by rfl⟩ : syracuseStep 908801 = 681601) B681601
theorem B450059 : Blo 447780 450059 := bstep (se 1 (by rfl) ⟨337544, by rfl⟩ : syracuseStep 450059 = 675089) B675089
theorem B450071 : Blo 447780 450071 := bstep (se 1 (by rfl) ⟨337553, by rfl⟩ : syracuseStep 450071 = 675107) B675107
theorem B450091 : Blo 447780 450091 := bstep (se 1 (by rfl) ⟨337568, by rfl⟩ : syracuseStep 450091 = 675137) B675137
theorem B450103 : Blo 447780 450103 := bstep (se 1 (by rfl) ⟨337577, by rfl⟩ : syracuseStep 450103 = 675155) B675155
theorem B450123 : Blo 447780 450123 := bstep (se 1 (by rfl) ⟨337592, by rfl⟩ : syracuseStep 450123 = 675185) B675185
theorem B450135 : Blo 447780 450135 := bstep (se 1 (by rfl) ⟨337601, by rfl⟩ : syracuseStep 450135 = 675203) B675203
theorem B1924697 : Blo 447780 1924697 := bstep (se 2 (by rfl) ⟨721761, by rfl⟩ : syracuseStep 1924697 = 1443523) B1443523
theorem B450155 : Blo 447780 450155 := bstep (se 1 (by rfl) ⟨337616, by rfl⟩ : syracuseStep 450155 = 675233) B675233
theorem B450167 : Blo 447780 450167 := bstep (se 1 (by rfl) ⟨337625, by rfl⟩ : syracuseStep 450167 = 675251) B675251
theorem B450187 : Blo 447780 450187 := bstep (se 1 (by rfl) ⟨337640, by rfl⟩ : syracuseStep 450187 = 675281) B675281
theorem B450199 : Blo 447780 450199 := bstep (se 1 (by rfl) ⟨337649, by rfl⟩ : syracuseStep 450199 = 675299) B675299
theorem B450219 : Blo 447780 450219 := bstep (se 1 (by rfl) ⟨337664, by rfl⟩ : syracuseStep 450219 = 675329) B675329
theorem B450231 : Blo 447780 450231 := bstep (se 1 (by rfl) ⟨337673, by rfl⟩ : syracuseStep 450231 = 675347) B675347
theorem B450251 : Blo 447780 450251 := bstep (se 1 (by rfl) ⟨337688, by rfl⟩ : syracuseStep 450251 = 675377) B675377
theorem B1171147 : Blo 447780 1171147 := bstep (se 1 (by rfl) ⟨878360, by rfl⟩ : syracuseStep 1171147 = 1756721) B1756721
theorem B450263 : Blo 447780 450263 := bstep (se 1 (by rfl) ⟨337697, by rfl⟩ : syracuseStep 450263 = 675395) B675395
theorem B2055901 : Blo 447780 2055901 := bstep (se 3 (by rfl) ⟨385481, by rfl⟩ : syracuseStep 2055901 = 770963) B770963
theorem B450283 : Blo 447780 450283 := bstep (se 1 (by rfl) ⟨337712, by rfl⟩ : syracuseStep 450283 = 675425) B675425
theorem B450295 : Blo 447780 450295 := bstep (se 1 (by rfl) ⟨337721, by rfl⟩ : syracuseStep 450295 = 675443) B675443
theorem B450315 : Blo 447780 450315 := bstep (se 1 (by rfl) ⟨337736, by rfl⟩ : syracuseStep 450315 = 675473) B675473
theorem B450327 : Blo 447780 450327 := bstep (se 1 (by rfl) ⟨337745, by rfl⟩ : syracuseStep 450327 = 675491) B675491
theorem B450347 : Blo 447780 450347 := bstep (se 1 (by rfl) ⟨337760, by rfl⟩ : syracuseStep 450347 = 675521) B675521
theorem B450359 : Blo 447780 450359 := bstep (se 1 (by rfl) ⟨337769, by rfl⟩ : syracuseStep 450359 = 675539) B675539
theorem B450379 : Blo 447780 450379 := bstep (se 1 (by rfl) ⟨337784, by rfl⟩ : syracuseStep 450379 = 675569) B675569
theorem B450391 : Blo 447780 450391 := bstep (se 1 (by rfl) ⟨337793, by rfl⟩ : syracuseStep 450391 = 675587) B675587
theorem B450411 : Blo 447780 450411 := bstep (se 1 (by rfl) ⟨337808, by rfl⟩ : syracuseStep 450411 = 675617) B675617
theorem B450423 : Blo 447780 450423 := bstep (se 1 (by rfl) ⟨337817, by rfl⟩ : syracuseStep 450423 = 675635) B675635
theorem B450443 : Blo 447780 450443 := bstep (se 1 (by rfl) ⟨337832, by rfl⟩ : syracuseStep 450443 = 675665) B675665
theorem B450455 : Blo 447780 450455 := bstep (se 1 (by rfl) ⟨337841, by rfl⟩ : syracuseStep 450455 = 675683) B675683
theorem B1007513 : Blo 447780 1007513 := bstep (se 2 (by rfl) ⟨377817, by rfl⟩ : syracuseStep 1007513 = 755635) B755635
theorem B450475 : Blo 447780 450475 := bstep (se 1 (by rfl) ⟨337856, by rfl⟩ : syracuseStep 450475 = 675713) B675713
theorem B450487 : Blo 447780 450487 := bstep (se 1 (by rfl) ⟨337865, by rfl⟩ : syracuseStep 450487 = 675731) B675731
theorem B450507 : Blo 447780 450507 := bstep (se 1 (by rfl) ⟨337880, by rfl⟩ : syracuseStep 450507 = 675761) B675761
theorem B450519 : Blo 447780 450519 := bstep (se 1 (by rfl) ⟨337889, by rfl⟩ : syracuseStep 450519 = 675779) B675779
theorem B450539 : Blo 447780 450539 := bstep (se 1 (by rfl) ⟨337904, by rfl⟩ : syracuseStep 450539 = 675809) B675809
theorem B1007603 : Blo 447780 1007603 := bstep (se 1 (by rfl) ⟨755702, by rfl⟩ : syracuseStep 1007603 = 1511405) B1511405
theorem B450551 : Blo 447780 450551 := bstep (se 1 (by rfl) ⟨337913, by rfl⟩ : syracuseStep 450551 = 675827) B675827
theorem B1826819 : Blo 447780 1826819 := bstep (se 1 (by rfl) ⟨1370114, by rfl⟩ : syracuseStep 1826819 = 2740229) B2740229
theorem B450571 : Blo 447780 450571 := bstep (se 1 (by rfl) ⟨337928, by rfl⟩ : syracuseStep 450571 = 675857) B675857
theorem B1007639 : Blo 447780 1007639 := bstep (se 1 (by rfl) ⟨755729, by rfl⟩ : syracuseStep 1007639 = 1511459) B1511459
theorem B450583 : Blo 447780 450583 := bstep (se 1 (by rfl) ⟨337937, by rfl⟩ : syracuseStep 450583 = 675875) B675875
theorem B450603 : Blo 447780 450603 := bstep (se 1 (by rfl) ⟨337952, by rfl⟩ : syracuseStep 450603 = 675905) B675905
theorem B450615 : Blo 447780 450615 := bstep (se 1 (by rfl) ⟨337961, by rfl⟩ : syracuseStep 450615 = 675923) B675923
theorem B450635 : Blo 447780 450635 := bstep (se 1 (by rfl) ⟨337976, by rfl⟩ : syracuseStep 450635 = 675953) B675953
theorem B450647 : Blo 447780 450647 := bstep (se 1 (by rfl) ⟨337985, by rfl⟩ : syracuseStep 450647 = 675971) B675971
theorem B450667 : Blo 447780 450667 := bstep (se 1 (by rfl) ⟨338000, by rfl⟩ : syracuseStep 450667 = 676001) B676001
theorem B450679 : Blo 447780 450679 := bstep (se 1 (by rfl) ⟨338009, by rfl⟩ : syracuseStep 450679 = 676019) B676019
theorem B450699 : Blo 447780 450699 := bstep (se 1 (by rfl) ⟨338024, by rfl⟩ : syracuseStep 450699 = 676049) B676049
theorem B2056337 : Blo 447780 2056337 := bstep (se 2 (by rfl) ⟨771126, by rfl⟩ : syracuseStep 2056337 = 1542253) B1542253
theorem B450711 : Blo 447780 450711 := bstep (se 1 (by rfl) ⟨338033, by rfl⟩ : syracuseStep 450711 = 676067) B676067
theorem B450731 : Blo 447780 450731 := bstep (se 1 (by rfl) ⟨338048, by rfl⟩ : syracuseStep 450731 = 676097) B676097
theorem B450743 : Blo 447780 450743 := bstep (se 1 (by rfl) ⟨338057, by rfl⟩ : syracuseStep 450743 = 676115) B676115
theorem B1007819 : Blo 447780 1007819 := bstep (se 1 (by rfl) ⟨755864, by rfl⟩ : syracuseStep 1007819 = 1511729) B1511729
theorem B450763 : Blo 447780 450763 := bstep (se 1 (by rfl) ⟨338072, by rfl⟩ : syracuseStep 450763 = 676145) B676145
theorem B450775 : Blo 447780 450775 := bstep (se 1 (by rfl) ⟨338081, by rfl⟩ : syracuseStep 450775 = 676163) B676163
theorem B450795 : Blo 447780 450795 := bstep (se 1 (by rfl) ⟨338096, by rfl⟩ : syracuseStep 450795 = 676193) B676193
theorem B450807 : Blo 447780 450807 := bstep (se 1 (by rfl) ⟨338105, by rfl⟩ : syracuseStep 450807 = 676211) B676211
theorem B1007873 : Blo 447780 1007873 := bstep (se 2 (by rfl) ⟨377952, by rfl⟩ : syracuseStep 1007873 = 755905) B755905
theorem B450827 : Blo 447780 450827 := bstep (se 1 (by rfl) ⟨338120, by rfl⟩ : syracuseStep 450827 = 676241) B676241
theorem B450839 : Blo 447780 450839 := bstep (se 1 (by rfl) ⟨338129, by rfl⟩ : syracuseStep 450839 = 676259) B676259
theorem B450859 : Blo 447780 450859 := bstep (se 1 (by rfl) ⟨338144, by rfl⟩ : syracuseStep 450859 = 676289) B676289
theorem B450871 : Blo 447780 450871 := bstep (se 1 (by rfl) ⟨338153, by rfl⟩ : syracuseStep 450871 = 676307) B676307
theorem B450891 : Blo 447780 450891 := bstep (se 1 (by rfl) ⟨338168, by rfl⟩ : syracuseStep 450891 = 676337) B676337
theorem B450903 : Blo 447780 450903 := bstep (se 1 (by rfl) ⟨338177, by rfl⟩ : syracuseStep 450903 = 676355) B676355
theorem B450923 : Blo 447780 450923 := bstep (se 1 (by rfl) ⟨338192, by rfl⟩ : syracuseStep 450923 = 676385) B676385
theorem B450935 : Blo 447780 450935 := bstep (se 1 (by rfl) ⟨338201, by rfl⟩ : syracuseStep 450935 = 676403) B676403
theorem B450955 : Blo 447780 450955 := bstep (se 1 (by rfl) ⟨338216, by rfl⟩ : syracuseStep 450955 = 676433) B676433
theorem B450967 : Blo 447780 450967 := bstep (se 1 (by rfl) ⟨338225, by rfl⟩ : syracuseStep 450967 = 676451) B676451
theorem B450987 : Blo 447780 450987 := bstep (se 1 (by rfl) ⟨338240, by rfl⟩ : syracuseStep 450987 = 676481) B676481
theorem B1139123 : Blo 447780 1139123 := bstep (se 1 (by rfl) ⟨854342, by rfl⟩ : syracuseStep 1139123 = 1708685) B1708685
theorem B450999 : Blo 447780 450999 := bstep (se 1 (by rfl) ⟨338249, by rfl⟩ : syracuseStep 450999 = 676499) B676499
theorem B451019 : Blo 447780 451019 := bstep (se 1 (by rfl) ⟨338264, by rfl⟩ : syracuseStep 451019 = 676529) B676529
theorem B451031 : Blo 447780 451031 := bstep (se 1 (by rfl) ⟨338273, by rfl⟩ : syracuseStep 451031 = 676547) B676547
theorem B1008089 : Blo 447780 1008089 := bstep (se 2 (by rfl) ⟨378033, by rfl⟩ : syracuseStep 1008089 = 756067) B756067
theorem B451051 : Blo 447780 451051 := bstep (se 1 (by rfl) ⟨338288, by rfl⟩ : syracuseStep 451051 = 676577) B676577
theorem B451063 : Blo 447780 451063 := bstep (se 1 (by rfl) ⟨338297, by rfl⟩ : syracuseStep 451063 = 676595) B676595
theorem B451083 : Blo 447780 451083 := bstep (se 1 (by rfl) ⟨338312, by rfl⟩ : syracuseStep 451083 = 676625) B676625
theorem B6545933 : Blo 447780 6545933 := bstep (se 3 (by rfl) ⟨1227362, by rfl⟩ : syracuseStep 6545933 = 2454725) B2454725
theorem B3858961 : Blo 447780 3858961 := bstep (se 2 (by rfl) ⟨1447110, by rfl⟩ : syracuseStep 3858961 = 2894221) B2894221
theorem B451095 : Blo 447780 451095 := bstep (se 1 (by rfl) ⟨338321, by rfl⟩ : syracuseStep 451095 = 676643) B676643
theorem B4317731 : Blo 447780 4317731 := bstep (se 1 (by rfl) ⟨3238298, by rfl⟩ : syracuseStep 4317731 = 6476597) B6476597
theorem B451115 : Blo 447780 451115 := bstep (se 1 (by rfl) ⟨338336, by rfl⟩ : syracuseStep 451115 = 676673) B676673
theorem B1008179 : Blo 447780 1008179 := bstep (se 1 (by rfl) ⟨756134, by rfl⟩ : syracuseStep 1008179 = 1512269) B1512269
theorem B451127 : Blo 447780 451127 := bstep (se 1 (by rfl) ⟨338345, by rfl⟩ : syracuseStep 451127 = 676691) B676691
theorem B451147 : Blo 447780 451147 := bstep (se 1 (by rfl) ⟨338360, by rfl⟩ : syracuseStep 451147 = 676721) B676721
theorem B1008215 : Blo 447780 1008215 := bstep (se 1 (by rfl) ⟨756161, by rfl⟩ : syracuseStep 1008215 = 1512323) B1512323
theorem B451159 : Blo 447780 451159 := bstep (se 1 (by rfl) ⟨338369, by rfl⟩ : syracuseStep 451159 = 676739) B676739
theorem B451179 : Blo 447780 451179 := bstep (se 1 (by rfl) ⟨338384, by rfl⟩ : syracuseStep 451179 = 676769) B676769
theorem B451191 : Blo 447780 451191 := bstep (se 1 (by rfl) ⟨338393, by rfl⟩ : syracuseStep 451191 = 676787) B676787
theorem B451211 : Blo 447780 451211 := bstep (se 1 (by rfl) ⟨338408, by rfl⟩ : syracuseStep 451211 = 676817) B676817
theorem B451223 : Blo 447780 451223 := bstep (se 1 (by rfl) ⟨338417, by rfl⟩ : syracuseStep 451223 = 676835) B676835
theorem B451243 : Blo 447780 451243 := bstep (se 1 (by rfl) ⟨338432, by rfl⟩ : syracuseStep 451243 = 676865) B676865
theorem B451255 : Blo 447780 451255 := bstep (se 1 (by rfl) ⟨338441, by rfl⟩ : syracuseStep 451255 = 676883) B676883
theorem B451275 : Blo 447780 451275 := bstep (se 1 (by rfl) ⟨338456, by rfl⟩ : syracuseStep 451275 = 676913) B676913
theorem B451287 : Blo 447780 451287 := bstep (se 1 (by rfl) ⟨338465, by rfl⟩ : syracuseStep 451287 = 676931) B676931
theorem B1139417 : Blo 447780 1139417 := bstep (se 2 (by rfl) ⟨427281, by rfl⟩ : syracuseStep 1139417 = 854563) B854563
theorem B451307 : Blo 447780 451307 := bstep (se 1 (by rfl) ⟨338480, by rfl⟩ : syracuseStep 451307 = 676961) B676961
theorem B451319 : Blo 447780 451319 := bstep (se 1 (by rfl) ⟨338489, by rfl⟩ : syracuseStep 451319 = 676979) B676979
theorem B1008395 : Blo 447780 1008395 := bstep (se 1 (by rfl) ⟨756296, by rfl⟩ : syracuseStep 1008395 = 1512593) B1512593
theorem B451339 : Blo 447780 451339 := bstep (se 1 (by rfl) ⟨338504, by rfl⟩ : syracuseStep 451339 = 677009) B677009
theorem B451351 : Blo 447780 451351 := bstep (se 1 (by rfl) ⟨338513, by rfl⟩ : syracuseStep 451351 = 677027) B677027
theorem B3859235 : Blo 447780 3859235 := bstep (se 1 (by rfl) ⟨2894426, by rfl⟩ : syracuseStep 3859235 = 5788853) B5788853
theorem B451371 : Blo 447780 451371 := bstep (se 1 (by rfl) ⟨338528, by rfl⟩ : syracuseStep 451371 = 677057) B677057
theorem B451383 : Blo 447780 451383 := bstep (se 1 (by rfl) ⟨338537, by rfl⟩ : syracuseStep 451383 = 677075) B677075
theorem B1008449 : Blo 447780 1008449 := bstep (se 2 (by rfl) ⟨378168, by rfl⟩ : syracuseStep 1008449 = 756337) B756337
theorem B1925963 : Blo 447780 1925963 := bstep (se 1 (by rfl) ⟨1444472, by rfl⟩ : syracuseStep 1925963 = 2888945) B2888945
theorem B451403 : Blo 447780 451403 := bstep (se 1 (by rfl) ⟨338552, by rfl⟩ : syracuseStep 451403 = 677105) B677105
theorem B451415 : Blo 447780 451415 := bstep (se 1 (by rfl) ⟨338561, by rfl⟩ : syracuseStep 451415 = 677123) B677123
theorem B3400541 : Blo 447780 3400541 := bstep (se 3 (by rfl) ⟨637601, by rfl⟩ : syracuseStep 3400541 = 1275203) B1275203
theorem B451435 : Blo 447780 451435 := bstep (se 1 (by rfl) ⟨338576, by rfl⟩ : syracuseStep 451435 = 677153) B677153
theorem B451447 : Blo 447780 451447 := bstep (se 1 (by rfl) ⟨338585, by rfl⟩ : syracuseStep 451447 = 677171) B677171
theorem B2286467 : Blo 447780 2286467 := bstep (se 1 (by rfl) ⟨1714850, by rfl⟩ : syracuseStep 2286467 = 3429701) B3429701
theorem B451467 : Blo 447780 451467 := bstep (se 1 (by rfl) ⟨338600, by rfl⟩ : syracuseStep 451467 = 677201) B677201
theorem B451479 : Blo 447780 451479 := bstep (se 1 (by rfl) ⟨338609, by rfl⟩ : syracuseStep 451479 = 677219) B677219
theorem B451499 : Blo 447780 451499 := bstep (se 1 (by rfl) ⟨338624, by rfl⟩ : syracuseStep 451499 = 677249) B677249
theorem B451511 : Blo 447780 451511 := bstep (se 1 (by rfl) ⟨338633, by rfl⟩ : syracuseStep 451511 = 677267) B677267
theorem B451531 : Blo 447780 451531 := bstep (se 1 (by rfl) ⟨338648, by rfl⟩ : syracuseStep 451531 = 677297) B677297
theorem B451543 : Blo 447780 451543 := bstep (se 1 (by rfl) ⟨338657, by rfl⟩ : syracuseStep 451543 = 677315) B677315
theorem B451563 : Blo 447780 451563 := bstep (se 1 (by rfl) ⟨338672, by rfl⟩ : syracuseStep 451563 = 677345) B677345
theorem B451575 : Blo 447780 451575 := bstep (se 1 (by rfl) ⟨338681, by rfl⟩ : syracuseStep 451575 = 677363) B677363
theorem B451595 : Blo 447780 451595 := bstep (se 1 (by rfl) ⟨338696, by rfl⟩ : syracuseStep 451595 = 677393) B677393
theorem B451607 : Blo 447780 451607 := bstep (se 1 (by rfl) ⟨338705, by rfl⟩ : syracuseStep 451607 = 677411) B677411
theorem B1008665 : Blo 447780 1008665 := bstep (se 2 (by rfl) ⟨378249, by rfl⟩ : syracuseStep 1008665 = 756499) B756499
theorem B451627 : Blo 447780 451627 := bstep (se 1 (by rfl) ⟨338720, by rfl⟩ : syracuseStep 451627 = 677441) B677441
theorem B451639 : Blo 447780 451639 := bstep (se 1 (by rfl) ⟨338729, by rfl⟩ : syracuseStep 451639 = 677459) B677459
theorem B451659 : Blo 447780 451659 := bstep (se 1 (by rfl) ⟨338744, by rfl⟩ : syracuseStep 451659 = 677489) B677489
theorem B451671 : Blo 447780 451671 := bstep (se 1 (by rfl) ⟨338753, by rfl⟩ : syracuseStep 451671 = 677507) B677507
theorem B451691 : Blo 447780 451691 := bstep (se 1 (by rfl) ⟨338768, by rfl⟩ : syracuseStep 451691 = 677537) B677537
theorem B1008755 : Blo 447780 1008755 := bstep (se 1 (by rfl) ⟨756566, by rfl⟩ : syracuseStep 1008755 = 1513133) B1513133
theorem B451703 : Blo 447780 451703 := bstep (se 1 (by rfl) ⟨338777, by rfl⟩ : syracuseStep 451703 = 677555) B677555
theorem B451723 : Blo 447780 451723 := bstep (se 1 (by rfl) ⟨338792, by rfl⟩ : syracuseStep 451723 = 677585) B677585
theorem B1008791 : Blo 447780 1008791 := bstep (se 1 (by rfl) ⟨756593, by rfl⟩ : syracuseStep 1008791 = 1513187) B1513187
theorem B451735 : Blo 447780 451735 := bstep (se 1 (by rfl) ⟨338801, by rfl⟩ : syracuseStep 451735 = 677603) B677603
theorem B451755 : Blo 447780 451755 := bstep (se 1 (by rfl) ⟨338816, by rfl⟩ : syracuseStep 451755 = 677633) B677633
theorem B451767 : Blo 447780 451767 := bstep (se 1 (by rfl) ⟨338825, by rfl⟩ : syracuseStep 451767 = 677651) B677651
theorem B910529 : Blo 447780 910529 := bstep (se 2 (by rfl) ⟨341448, by rfl⟩ : syracuseStep 910529 = 682897) B682897
theorem B1926337 : Blo 447780 1926337 := bstep (se 2 (by rfl) ⟨722376, by rfl⟩ : syracuseStep 1926337 = 1444753) B1444753
theorem B1008971 : Blo 447780 1008971 := bstep (se 1 (by rfl) ⟨756728, by rfl⟩ : syracuseStep 1008971 = 1513457) B1513457
theorem B1009025 : Blo 447780 1009025 := bstep (se 2 (by rfl) ⟨378384, by rfl⟩ : syracuseStep 1009025 = 756769) B756769
theorem B3696023 : Blo 447780 3696023 := bstep (se 1 (by rfl) ⟨2772017, by rfl⟩ : syracuseStep 3696023 = 5544035) B5544035
theorem B1926679 : Blo 447780 1926679 := bstep (se 1 (by rfl) ⟨1445009, by rfl⟩ : syracuseStep 1926679 = 2890019) B2890019
theorem B1009241 : Blo 447780 1009241 := bstep (se 2 (by rfl) ⟨378465, by rfl⟩ : syracuseStep 1009241 = 756931) B756931
theorem B1009331 : Blo 447780 1009331 := bstep (se 1 (by rfl) ⟨756998, by rfl⟩ : syracuseStep 1009331 = 1513997) B1513997
theorem B1009367 : Blo 447780 1009367 := bstep (se 1 (by rfl) ⟨757025, by rfl⟩ : syracuseStep 1009367 = 1514051) B1514051
theorem B1009547 : Blo 447780 1009547 := bstep (se 1 (by rfl) ⟨757160, by rfl⟩ : syracuseStep 1009547 = 1514321) B1514321
theorem B1009601 : Blo 447780 1009601 := bstep (se 2 (by rfl) ⟨378600, by rfl⟩ : syracuseStep 1009601 = 757201) B757201
theorem B1828811 : Blo 447780 1828811 := bstep (se 1 (by rfl) ⟨1371608, by rfl⟩ : syracuseStep 1828811 = 2743217) B2743217
theorem B3500183 : Blo 447780 3500183 := bstep (se 1 (by rfl) ⟨2625137, by rfl⟩ : syracuseStep 3500183 = 5250275) B5250275
theorem B1009817 : Blo 447780 1009817 := bstep (se 2 (by rfl) ⟨378681, by rfl⟩ : syracuseStep 1009817 = 757363) B757363
theorem B1009907 : Blo 447780 1009907 := bstep (se 1 (by rfl) ⟨757430, by rfl⟩ : syracuseStep 1009907 = 1514861) B1514861
theorem B1009943 : Blo 447780 1009943 := bstep (se 1 (by rfl) ⟨757457, by rfl⟩ : syracuseStep 1009943 = 1514915) B1514915
theorem B682265 : Blo 447780 682265 := bstep (se 2 (by rfl) ⟨255849, by rfl⟩ : syracuseStep 682265 = 511699) B511699
theorem B1141067 : Blo 447780 1141067 := bstep (se 1 (by rfl) ⟨855800, by rfl⟩ : syracuseStep 1141067 = 1711601) B1711601
theorem B55568753 : Blo 447780 55568753 := bstep (se 2 (by rfl) ⟨20838282, by rfl⟩ : syracuseStep 55568753 = 41676565) B41676565
theorem B1010123 : Blo 447780 1010123 := bstep (se 1 (by rfl) ⟨757592, by rfl⟩ : syracuseStep 1010123 = 1515185) B1515185
theorem B2779609 : Blo 447780 2779609 := bstep (se 2 (by rfl) ⟨1042353, by rfl⟩ : syracuseStep 2779609 = 2084707) B2084707
theorem B1010177 : Blo 447780 1010177 := bstep (se 2 (by rfl) ⟨378816, by rfl⟩ : syracuseStep 1010177 = 757633) B757633
theorem B2058817 : Blo 447780 2058817 := bstep (se 2 (by rfl) ⟨772056, by rfl⟩ : syracuseStep 2058817 = 1544113) B1544113
theorem B1010393 : Blo 447780 1010393 := bstep (se 2 (by rfl) ⟨378897, by rfl⟩ : syracuseStep 1010393 = 757795) B757795
theorem B1010483 : Blo 447780 1010483 := bstep (se 1 (by rfl) ⟨757862, by rfl⟩ : syracuseStep 1010483 = 1515725) B1515725
theorem B1010519 : Blo 447780 1010519 := bstep (se 1 (by rfl) ⟨757889, by rfl⟩ : syracuseStep 1010519 = 1515779) B1515779
theorem B1010699 : Blo 447780 1010699 := bstep (se 1 (by rfl) ⟨758024, by rfl⟩ : syracuseStep 1010699 = 1516049) B1516049
theorem B1010753 : Blo 447780 1010753 := bstep (se 2 (by rfl) ⟨379032, by rfl⟩ : syracuseStep 1010753 = 758065) B758065
theorem B650315 : Blo 447780 650315 := bstep (se 1 (by rfl) ⟨487736, by rfl⟩ : syracuseStep 650315 = 975473) B975473
theorem B1142039 : Blo 447780 1142039 := bstep (se 1 (by rfl) ⟨856529, by rfl⟩ : syracuseStep 1142039 = 1713059) B1713059
theorem B1010969 : Blo 447780 1010969 := bstep (se 2 (by rfl) ⟨379113, by rfl⟩ : syracuseStep 1010969 = 758227) B758227
theorem B1371485 : Blo 447780 1371485 := bstep (se 3 (by rfl) ⟨257153, by rfl⟩ : syracuseStep 1371485 = 514307) B514307
theorem B1011059 : Blo 447780 1011059 := bstep (se 1 (by rfl) ⟨758294, by rfl⟩ : syracuseStep 1011059 = 1516589) B1516589
theorem B1011095 : Blo 447780 1011095 := bstep (se 1 (by rfl) ⟨758321, by rfl⟩ : syracuseStep 1011095 = 1516643) B1516643
theorem B3468835 : Blo 447780 3468835 := bstep (se 1 (by rfl) ⟨2601626, by rfl⟩ : syracuseStep 3468835 = 5203253) B5203253
theorem B1011275 : Blo 447780 1011275 := bstep (se 1 (by rfl) ⟨758456, by rfl⟩ : syracuseStep 1011275 = 1516913) B1516913
theorem B1011329 : Blo 447780 1011329 := bstep (se 2 (by rfl) ⟨379248, by rfl⟩ : syracuseStep 1011329 = 758497) B758497
theorem B1076915 : Blo 447780 1076915 := bstep (se 1 (by rfl) ⟨807686, by rfl⟩ : syracuseStep 1076915 = 1615373) B1615373
theorem B2191169 : Blo 447780 2191169 := bstep (se 2 (by rfl) ⟨821688, by rfl⟩ : syracuseStep 2191169 = 1643377) B1643377
theorem B1011545 : Blo 447780 1011545 := bstep (se 2 (by rfl) ⟨379329, by rfl⟩ : syracuseStep 1011545 = 758659) B758659
theorem B1011635 : Blo 447780 1011635 := bstep (se 1 (by rfl) ⟨758726, by rfl⟩ : syracuseStep 1011635 = 1517453) B1517453
theorem B1142707 : Blo 447780 1142707 := bstep (se 1 (by rfl) ⟨857030, by rfl⟩ : syracuseStep 1142707 = 1714061) B1714061
theorem B1011671 : Blo 447780 1011671 := bstep (se 1 (by rfl) ⟨758753, by rfl⟩ : syracuseStep 1011671 = 1517507) B1517507
theorem B1142849 : Blo 447780 1142849 := bstep (se 2 (by rfl) ⟨428568, by rfl⟩ : syracuseStep 1142849 = 857137) B857137
theorem B1077337 : Blo 447780 1077337 := bstep (se 2 (by rfl) ⟨404001, by rfl⟩ : syracuseStep 1077337 = 808003) B808003
theorem B1011851 : Blo 447780 1011851 := bstep (se 1 (by rfl) ⟨758888, by rfl⟩ : syracuseStep 1011851 = 1517777) B1517777
theorem B1011905 : Blo 447780 1011905 := bstep (se 2 (by rfl) ⟨379464, by rfl⟩ : syracuseStep 1011905 = 758929) B758929
theorem B684235 : Blo 447780 684235 := bstep (se 1 (by rfl) ⟨513176, by rfl⟩ : syracuseStep 684235 = 1026353) B1026353
theorem B913675 : Blo 447780 913675 := bstep (se 1 (by rfl) ⟨685256, by rfl⟩ : syracuseStep 913675 = 1370513) B1370513
theorem B1077569 : Blo 447780 1077569 := bstep (se 2 (by rfl) ⟨404088, by rfl⟩ : syracuseStep 1077569 = 808177) B808177
theorem B913739 : Blo 447780 913739 := bstep (se 1 (by rfl) ⟨685304, by rfl⟩ : syracuseStep 913739 = 1370609) B1370609
theorem B2158979 : Blo 447780 2158979 := bstep (se 1 (by rfl) ⟨1619234, by rfl⟩ : syracuseStep 2158979 = 3238469) B3238469
theorem B1012121 : Blo 447780 1012121 := bstep (se 2 (by rfl) ⟨379545, by rfl⟩ : syracuseStep 1012121 = 759091) B759091
theorem B1012211 : Blo 447780 1012211 := bstep (se 1 (by rfl) ⟨759158, by rfl⟩ : syracuseStep 1012211 = 1518317) B1518317
theorem B1012247 : Blo 447780 1012247 := bstep (se 1 (by rfl) ⟨759185, by rfl⟩ : syracuseStep 1012247 = 1518371) B1518371
theorem B1012427 : Blo 447780 1012427 := bstep (se 1 (by rfl) ⟨759320, by rfl⟩ : syracuseStep 1012427 = 1518641) B1518641
theorem B1012481 : Blo 447780 1012481 := bstep (se 2 (by rfl) ⟨379680, by rfl⟩ : syracuseStep 1012481 = 759361) B759361
theorem B2552593 : Blo 447780 2552593 := bstep (se 2 (by rfl) ⟨957222, by rfl⟩ : syracuseStep 2552593 = 1914445) B1914445
theorem B717655 : Blo 447780 717655 := bstep (se 1 (by rfl) ⟨538241, by rfl⟩ : syracuseStep 717655 = 1076483) B1076483
theorem B1012697 : Blo 447780 1012697 := bstep (se 2 (by rfl) ⟨379761, by rfl⟩ : syracuseStep 1012697 = 759523) B759523
theorem B1700909 : Blo 447780 1700909 := bstep (se 3 (by rfl) ⟨318920, by rfl⟩ : syracuseStep 1700909 = 637841) B637841
theorem B1012787 : Blo 447780 1012787 := bstep (se 1 (by rfl) ⟨759590, by rfl⟩ : syracuseStep 1012787 = 1519181) B1519181
theorem B1700939 : Blo 447780 1700939 := bstep (se 1 (by rfl) ⟨1275704, by rfl⟩ : syracuseStep 1700939 = 2551409) B2551409
theorem B1012823 : Blo 447780 1012823 := bstep (se 1 (by rfl) ⟨759617, by rfl⟩ : syracuseStep 1012823 = 1519235) B1519235
theorem B1013003 : Blo 447780 1013003 := bstep (se 1 (by rfl) ⟨759752, by rfl⟩ : syracuseStep 1013003 = 1519505) B1519505
theorem B1013057 : Blo 447780 1013057 := bstep (se 2 (by rfl) ⟨379896, by rfl⟩ : syracuseStep 1013057 = 759793) B759793
theorem B1734061 : Blo 447780 1734061 := bstep (se 3 (by rfl) ⟨325136, by rfl⟩ : syracuseStep 1734061 = 650273) B650273
theorem B2880947 : Blo 447780 2880947 := bstep (se 1 (by rfl) ⟨2160710, by rfl⟩ : syracuseStep 2880947 = 4321421) B4321421
theorem B1013273 : Blo 447780 1013273 := bstep (se 2 (by rfl) ⟨379977, by rfl⟩ : syracuseStep 1013273 = 759955) B759955
theorem B2881099 : Blo 447780 2881099 := bstep (se 1 (by rfl) ⟨2160824, by rfl⟩ : syracuseStep 2881099 = 4321649) B4321649
theorem B1013363 : Blo 447780 1013363 := bstep (se 1 (by rfl) ⟨760022, by rfl⟩ : syracuseStep 1013363 = 1520045) B1520045
theorem B718475 : Blo 447780 718475 := bstep (se 1 (by rfl) ⟨538856, by rfl⟩ : syracuseStep 718475 = 1077713) B1077713
theorem B1013399 : Blo 447780 1013399 := bstep (se 1 (by rfl) ⟨760049, by rfl⟩ : syracuseStep 1013399 = 1520099) B1520099
theorem B1701593 : Blo 447780 1701593 := bstep (se 2 (by rfl) ⟨638097, by rfl⟩ : syracuseStep 1701593 = 1276195) B1276195
theorem B1013579 : Blo 447780 1013579 := bstep (se 1 (by rfl) ⟨760184, by rfl⟩ : syracuseStep 1013579 = 1520369) B1520369
theorem B685913 : Blo 447780 685913 := bstep (se 2 (by rfl) ⟨257217, by rfl⟩ : syracuseStep 685913 = 514435) B514435
theorem B1013633 : Blo 447780 1013633 := bstep (se 2 (by rfl) ⟨380112, by rfl⟩ : syracuseStep 1013633 = 760225) B760225
theorem B1275841 : Blo 447780 1275841 := bstep (se 2 (by rfl) ⟨478440, by rfl⟩ : syracuseStep 1275841 = 956881) B956881
theorem B1701911 : Blo 447780 1701911 := bstep (se 1 (by rfl) ⟨1276433, by rfl⟩ : syracuseStep 1701911 = 2552867) B2552867
theorem B1013849 : Blo 447780 1013849 := bstep (se 2 (by rfl) ⟨380193, by rfl⟩ : syracuseStep 1013849 = 760387) B760387
theorem B1013939 : Blo 447780 1013939 := bstep (se 1 (by rfl) ⟨760454, by rfl⟩ : syracuseStep 1013939 = 1520909) B1520909
theorem B1013975 : Blo 447780 1013975 := bstep (se 1 (by rfl) ⟨760481, by rfl⟩ : syracuseStep 1013975 = 1520963) B1520963
theorem B1734929 : Blo 447780 1734929 := bstep (se 2 (by rfl) ⟨650598, by rfl⟩ : syracuseStep 1734929 = 1301197) B1301197
theorem B1440089 : Blo 447780 1440089 := bstep (se 2 (by rfl) ⟨540033, by rfl⟩ : syracuseStep 1440089 = 1080067) B1080067
theorem B1014155 : Blo 447780 1014155 := bstep (se 1 (by rfl) ⟨760616, by rfl⟩ : syracuseStep 1014155 = 1521233) B1521233
theorem B1014209 : Blo 447780 1014209 := bstep (se 2 (by rfl) ⟨380328, by rfl⟩ : syracuseStep 1014209 = 760657) B760657
theorem B5110289 : Blo 447780 5110289 := bstep (se 2 (by rfl) ⟨1916358, by rfl⟩ : syracuseStep 5110289 = 3832717) B3832717
theorem B1014425 : Blo 447780 1014425 := bstep (se 2 (by rfl) ⟨380409, by rfl⟩ : syracuseStep 1014425 = 760819) B760819
theorem B1702579 : Blo 447780 1702579 := bstep (se 1 (by rfl) ⟨1276934, by rfl⟩ : syracuseStep 1702579 = 2553869) B2553869
theorem B850675 : Blo 447780 850675 := bstep (se 1 (by rfl) ⟨638006, by rfl⟩ : syracuseStep 850675 = 1276013) B1276013
theorem B1014515 : Blo 447780 1014515 := bstep (se 1 (by rfl) ⟨760886, by rfl⟩ : syracuseStep 1014515 = 1521773) B1521773
theorem B457483 : Blo 447780 457483 := bstep (se 1 (by rfl) ⟨343112, by rfl⟩ : syracuseStep 457483 = 686225) B686225
theorem B1014551 : Blo 447780 1014551 := bstep (se 1 (by rfl) ⟨760913, by rfl⟩ : syracuseStep 1014551 = 1521827) B1521827
theorem B1014731 : Blo 447780 1014731 := bstep (se 1 (by rfl) ⟨761048, by rfl⟩ : syracuseStep 1014731 = 1522097) B1522097
theorem B1014785 : Blo 447780 1014785 := bstep (se 2 (by rfl) ⟨380544, by rfl⟩ : syracuseStep 1014785 = 761089) B761089
theorem B851123 : Blo 447780 851123 := bstep (se 1 (by rfl) ⟨638342, by rfl⟩ : syracuseStep 851123 = 1276685) B1276685
theorem B851161 : Blo 447780 851161 := bstep (se 2 (by rfl) ⟨319185, by rfl⟩ : syracuseStep 851161 = 638371) B638371
theorem B1015001 : Blo 447780 1015001 := bstep (se 2 (by rfl) ⟨380625, by rfl⟩ : syracuseStep 1015001 = 761251) B761251
theorem B1015091 : Blo 447780 1015091 := bstep (se 1 (by rfl) ⟨761318, by rfl⟩ : syracuseStep 1015091 = 1522637) B1522637
theorem B1015127 : Blo 447780 1015127 := bstep (se 1 (by rfl) ⟨761345, by rfl⟩ : syracuseStep 1015127 = 1522691) B1522691
theorem B1015307 : Blo 447780 1015307 := bstep (se 1 (by rfl) ⟨761480, by rfl⟩ : syracuseStep 1015307 = 1522961) B1522961
theorem B1015361 : Blo 447780 1015361 := bstep (se 2 (by rfl) ⟨380760, by rfl⟩ : syracuseStep 1015361 = 761521) B761521
theorem B851609 : Blo 447780 851609 := bstep (se 2 (by rfl) ⟨319353, by rfl⟩ : syracuseStep 851609 = 638707) B638707
theorem B1015577 : Blo 447780 1015577 := bstep (se 2 (by rfl) ⟨380841, by rfl⟩ : syracuseStep 1015577 = 761683) B761683
theorem B3833675 : Blo 447780 3833675 := bstep (se 1 (by rfl) ⟨2875256, by rfl⟩ : syracuseStep 3833675 = 5750513) B5750513
theorem B1015667 : Blo 447780 1015667 := bstep (se 1 (by rfl) ⟨761750, by rfl⟩ : syracuseStep 1015667 = 1523501) B1523501
theorem B1703825 : Blo 447780 1703825 := bstep (se 2 (by rfl) ⟨638934, by rfl⟩ : syracuseStep 1703825 = 1277869) B1277869
theorem B1015703 : Blo 447780 1015703 := bstep (se 1 (by rfl) ⟨761777, by rfl⟩ : syracuseStep 1015703 = 1523555) B1523555
theorem B1441729 : Blo 447780 1441729 := bstep (se 2 (by rfl) ⟨540648, by rfl⟩ : syracuseStep 1441729 = 1081297) B1081297
theorem B3112921 : Blo 447780 3112921 := bstep (se 2 (by rfl) ⟨1167345, by rfl⟩ : syracuseStep 3112921 = 2334691) B2334691
theorem B1704023 : Blo 447780 1704023 := bstep (se 1 (by rfl) ⟨1278017, by rfl⟩ : syracuseStep 1704023 = 2556035) B2556035
theorem B2162807 : Blo 447780 2162807 := bstep (se 1 (by rfl) ⟨1622105, by rfl⟩ : syracuseStep 2162807 = 3244211) B3244211
theorem B1015955 : Blo 447780 1015955 := bstep (se 1 (by rfl) ⟨761966, by rfl⟩ : syracuseStep 1015955 = 1523933) B1523933
theorem B1016009 : Blo 447780 1016009 := bstep (se 2 (by rfl) ⟨381003, by rfl⟩ : syracuseStep 1016009 = 762007) B762007
theorem B1704509 : Blo 447780 1704509 := bstep (se 3 (by rfl) ⟨319595, by rfl⟩ : syracuseStep 1704509 = 639191) B639191
theorem B1081943 : Blo 447780 1081943 := bstep (se 1 (by rfl) ⟨811457, by rfl⟩ : syracuseStep 1081943 = 1622915) B1622915
theorem B5145281 : Blo 447780 5145281 := bstep (se 2 (by rfl) ⟨1929480, by rfl⟩ : syracuseStep 5145281 = 3858961) B3858961
theorem B2917093 : Blo 447780 2917093 := bstep (se 4 (by rfl) ⟨273477, by rfl⟩ : syracuseStep 2917093 = 546955) B546955
theorem B3408803 : Blo 447780 3408803 := bstep (se 1 (by rfl) ⟨2556602, by rfl⟩ : syracuseStep 3408803 = 5113205) B5113205
theorem B37815349 : Blo 447780 37815349 := bstep (se 5 (by rfl) ⟨1772594, by rfl⟩ : syracuseStep 37815349 = 3545189) B3545189
theorem B1279111 : Blo 447780 1279111 := bstep (se 1 (by rfl) ⟨959333, by rfl⟩ : syracuseStep 1279111 = 1918667) B1918667
theorem B1279385 : Blo 447780 1279385 := bstep (se 2 (by rfl) ⟨479769, by rfl⟩ : syracuseStep 1279385 = 959539) B959539
theorem B22808141 : Blo 447780 22808141 := bstep (se 3 (by rfl) ⟨4276526, by rfl⟩ : syracuseStep 22808141 = 8553053) B8553053
theorem B853895 : Blo 447780 853895 := bstep (se 1 (by rfl) ⟨640421, by rfl⟩ : syracuseStep 853895 = 1280843) B1280843
theorem B1280033 : Blo 447780 1280033 := bstep (se 2 (by rfl) ⟨480012, by rfl⟩ : syracuseStep 1280033 = 960025) B960025
theorem B2164823 : Blo 447780 2164823 := bstep (se 1 (by rfl) ⟨1623617, by rfl⟩ : syracuseStep 2164823 = 3247235) B3247235
theorem B755831 : Blo 447780 755831 := bstep (se 1 (by rfl) ⟨566873, by rfl⟩ : syracuseStep 755831 = 1133747) B1133747
theorem B1706255 : Blo 447780 1706255 := bstep (se 1 (by rfl) ⟨1279691, by rfl⟩ : syracuseStep 1706255 = 2559383) B2559383
theorem B1149227 : Blo 447780 1149227 := bstep (se 1 (by rfl) ⟨861920, by rfl⟩ : syracuseStep 1149227 = 1723841) B1723841
theorem B756283 : Blo 447780 756283 := bstep (se 1 (by rfl) ⟨567212, by rfl⟩ : syracuseStep 756283 = 1134425) B1134425
theorem B756425 : Blo 447780 756425 := bstep (se 2 (by rfl) ⟨283659, by rfl⟩ : syracuseStep 756425 = 567319) B567319
theorem B1281035 : Blo 447780 1281035 := bstep (se 1 (by rfl) ⟨960776, by rfl⟩ : syracuseStep 1281035 = 1921553) B1921553
theorem B12946493 : Blo 447780 12946493 := bstep (se 3 (by rfl) ⟨2427467, by rfl⟩ : syracuseStep 12946493 = 4854935) B4854935
theorem B3411233 : Blo 447780 3411233 := bstep (se 2 (by rfl) ⟨1279212, by rfl⟩ : syracuseStep 3411233 = 2558425) B2558425
theorem B3706145 : Blo 447780 3706145 := bstep (se 2 (by rfl) ⟨1389804, by rfl⟩ : syracuseStep 3706145 = 2779609) B2779609
theorem B757127 : Blo 447780 757127 := bstep (se 1 (by rfl) ⟨567845, by rfl⟩ : syracuseStep 757127 = 1135691) B1135691
theorem B855497 : Blo 447780 855497 := bstep (se 2 (by rfl) ⟨320811, by rfl⟩ : syracuseStep 855497 = 641623) B641623
theorem B3903095 : Blo 447780 3903095 := bstep (se 1 (by rfl) ⟨2927321, by rfl⟩ : syracuseStep 3903095 = 5854643) B5854643
theorem B1707911 : Blo 447780 1707911 := bstep (se 1 (by rfl) ⟨1280933, by rfl⟩ : syracuseStep 1707911 = 2561867) B2561867
theorem B757775 : Blo 447780 757775 := bstep (se 1 (by rfl) ⟨568331, by rfl⟩ : syracuseStep 757775 = 1136663) B1136663
theorem B3412205 : Blo 447780 3412205 := bstep (se 3 (by rfl) ⟨639788, by rfl⟩ : syracuseStep 3412205 = 1279577) B1279577
theorem B2560409 : Blo 447780 2560409 := bstep (se 2 (by rfl) ⟨960153, by rfl⟩ : syracuseStep 2560409 = 1920307) B1920307
theorem B758315 : Blo 447780 758315 := bstep (se 1 (by rfl) ⟨568736, by rfl⟩ : syracuseStep 758315 = 1137473) B1137473
theorem B3707459 : Blo 447780 3707459 := bstep (se 1 (by rfl) ⟨2780594, by rfl⟩ : syracuseStep 3707459 = 5561189) B5561189
theorem B4625113 : Blo 447780 4625113 := bstep (se 2 (by rfl) ⟨1734417, by rfl⟩ : syracuseStep 4625113 = 3468835) B3468835
theorem B1512377 : Blo 447780 1512377 := bstep (se 2 (by rfl) ⟨567141, by rfl⟩ : syracuseStep 1512377 = 1134283) B1134283
theorem B758713 : Blo 447780 758713 := bstep (se 2 (by rfl) ⟨284517, by rfl⟩ : syracuseStep 758713 = 569035) B569035
theorem B1283131 : Blo 447780 1283131 := bstep (se 1 (by rfl) ⟨962348, by rfl⟩ : syracuseStep 1283131 = 1924697) B1924697
theorem B1217879 : Blo 447780 1217879 := bstep (se 1 (by rfl) ⟨913409, by rfl⟩ : syracuseStep 1217879 = 1826819) B1826819
theorem B857479 : Blo 447780 857479 := bstep (se 1 (by rfl) ⟨643109, by rfl⟩ : syracuseStep 857479 = 1286219) B1286219
theorem B1512971 : Blo 447780 1512971 := bstep (se 1 (by rfl) ⟨1134728, by rfl⟩ : syracuseStep 1512971 = 2269457) B2269457
theorem B1513079 : Blo 447780 1513079 := bstep (se 1 (by rfl) ⟨1134809, by rfl⟩ : syracuseStep 1513079 = 2269619) B2269619
theorem B759415 : Blo 447780 759415 := bstep (se 1 (by rfl) ⟨569561, by rfl⟩ : syracuseStep 759415 = 1139123) B1139123
theorem B1709687 : Blo 447780 1709687 := bstep (se 1 (by rfl) ⟨1282265, by rfl⟩ : syracuseStep 1709687 = 2564531) B2564531
theorem B4363955 : Blo 447780 4363955 := bstep (se 1 (by rfl) ⟨3272966, by rfl⟩ : syracuseStep 4363955 = 6545933) B6545933
theorem B1218233 : Blo 447780 1218233 := bstep (se 2 (by rfl) ⟨456837, by rfl⟩ : syracuseStep 1218233 = 913675) B913675
theorem B759611 : Blo 447780 759611 := bstep (se 1 (by rfl) ⟨569708, by rfl⟩ : syracuseStep 759611 = 1139417) B1139417
theorem B4331339 : Blo 447780 4331339 := bstep (se 1 (by rfl) ⟨3248504, by rfl⟩ : syracuseStep 4331339 = 6497009) B6497009
theorem B1283975 : Blo 447780 1283975 := bstep (se 1 (by rfl) ⟨962981, by rfl⟩ : syracuseStep 1283975 = 1925963) B1925963
theorem B2267027 : Blo 447780 2267027 := bstep (se 1 (by rfl) ⟨1700270, by rfl⟩ : syracuseStep 2267027 = 3400541) B3400541
theorem B3414149 : Blo 447780 3414149 := bstep (se 4 (by rfl) ⟨320076, by rfl⟩ : syracuseStep 3414149 = 640153) B640153
theorem B1513673 : Blo 447780 1513673 := bstep (se 2 (by rfl) ⟨567627, by rfl⟩ : syracuseStep 1513673 = 1135255) B1135255
theorem B760009 : Blo 447780 760009 := bstep (se 2 (by rfl) ⟨285003, by rfl⟩ : syracuseStep 760009 = 570007) B570007
theorem B2464015 : Blo 447780 2464015 := bstep (se 1 (by rfl) ⟨1848011, by rfl⟩ : syracuseStep 2464015 = 3696023) B3696023
theorem B956873 : Blo 447780 956873 := bstep (se 2 (by rfl) ⟨358827, by rfl⟩ : syracuseStep 956873 = 717655) B717655
theorem B1710659 : Blo 447780 1710659 := bstep (se 1 (by rfl) ⟨1282994, by rfl⟩ : syracuseStep 1710659 = 2565989) B2565989
theorem B1219207 : Blo 447780 1219207 := bstep (se 1 (by rfl) ⟨914405, by rfl⟩ : syracuseStep 1219207 = 1828811) B1828811
theorem B1284761 : Blo 447780 1284761 := bstep (se 2 (by rfl) ⟨481785, by rfl⟩ : syracuseStep 1284761 = 963571) B963571
theorem B2333455 : Blo 447780 2333455 := bstep (se 1 (by rfl) ⟨1750091, by rfl⟩ : syracuseStep 2333455 = 3500183) B3500183
theorem B1514375 : Blo 447780 1514375 := bstep (se 1 (by rfl) ⟨1135781, by rfl⟩ : syracuseStep 1514375 = 2271563) B2271563
theorem B760711 : Blo 447780 760711 := bstep (se 1 (by rfl) ⟨570533, by rfl⟩ : syracuseStep 760711 = 1141067) B1141067
theorem B1711115 : Blo 447780 1711115 := bstep (se 1 (by rfl) ⟨1283336, by rfl⟩ : syracuseStep 1711115 = 2566673) B2566673
theorem B2169899 : Blo 447780 2169899 := bstep (se 1 (by rfl) ⟨1627424, by rfl⟩ : syracuseStep 2169899 = 3254849) B3254849
theorem B5119037 : Blo 447780 5119037 := bstep (se 3 (by rfl) ⟨959819, by rfl⟩ : syracuseStep 5119037 = 1919639) B1919639
theorem B1645655 : Blo 447780 1645655 := bstep (se 1 (by rfl) ⟨1234241, by rfl⟩ : syracuseStep 1645655 = 2468483) B2468483
theorem B1514753 : Blo 447780 1514753 := bstep (se 2 (by rfl) ⟨568032, by rfl⟩ : syracuseStep 1514753 = 1136065) B1136065
theorem B1285409 : Blo 447780 1285409 := bstep (se 2 (by rfl) ⟨482028, by rfl⟩ : syracuseStep 1285409 = 964057) B964057
theorem B3841465 : Blo 447780 3841465 := bstep (se 2 (by rfl) ⟨1440549, by rfl⟩ : syracuseStep 3841465 = 2881099) B2881099
theorem B761359 : Blo 447780 761359 := bstep (se 1 (by rfl) ⟨571019, by rfl⟩ : syracuseStep 761359 = 1142039) B1142039
theorem B2563757 : Blo 447780 2563757 := bstep (se 3 (by rfl) ⟨480704, by rfl⟩ : syracuseStep 2563757 = 961409) B961409
theorem B2924261 : Blo 447780 2924261 := bstep (se 4 (by rfl) ⟨274149, by rfl⟩ : syracuseStep 2924261 = 548299) B548299
theorem B1384235 : Blo 447780 1384235 := bstep (se 1 (by rfl) ⟨1038176, by rfl⟩ : syracuseStep 1384235 = 2076353) B2076353
theorem B2891609 : Blo 447780 2891609 := bstep (se 2 (by rfl) ⟨1084353, by rfl⟩ : syracuseStep 2891609 = 2168707) B2168707
theorem B1515563 : Blo 447780 1515563 := bstep (se 1 (by rfl) ⟨1136672, by rfl⟩ : syracuseStep 1515563 = 2273345) B2273345
theorem B761899 : Blo 447780 761899 := bstep (se 1 (by rfl) ⟨571424, by rfl⟩ : syracuseStep 761899 = 1142849) B1142849
theorem B762041 : Blo 447780 762041 := bstep (se 2 (by rfl) ⟨285765, by rfl⟩ : syracuseStep 762041 = 571531) B571531
theorem B1286401 : Blo 447780 1286401 := bstep (se 2 (by rfl) ⟨482400, by rfl⟩ : syracuseStep 1286401 = 964801) B964801
theorem B1122761 : Blo 447780 1122761 := bstep (se 2 (by rfl) ⟨421035, by rfl⟩ : syracuseStep 1122761 = 842071) B842071
theorem B3416579 : Blo 447780 3416579 := bstep (se 1 (by rfl) ⟨2562434, by rfl⟩ : syracuseStep 3416579 = 5124869) B5124869
theorem B2892581 : Blo 447780 2892581 := bstep (se 4 (by rfl) ⟨271179, by rfl⟩ : syracuseStep 2892581 = 542359) B542359
theorem B2433851 : Blo 447780 2433851 := bstep (se 1 (by rfl) ⟨1825388, by rfl⟩ : syracuseStep 2433851 = 3650777) B3650777
theorem B2270105 : Blo 447780 2270105 := bstep (se 2 (by rfl) ⟨851289, by rfl⟩ : syracuseStep 2270105 = 1702579) B1702579
theorem B7316405 : Blo 447780 7316405 := bstep (se 5 (by rfl) ⟨342956, by rfl⟩ : syracuseStep 7316405 = 685913) B685913
theorem B1713271 : Blo 447780 1713271 := bstep (se 1 (by rfl) ⟨1284953, by rfl⟩ : syracuseStep 1713271 = 2569907) B2569907
theorem B1516859 : Blo 447780 1516859 := bstep (se 1 (by rfl) ⟨1137644, by rfl⟩ : syracuseStep 1516859 = 2275289) B2275289
theorem B11085265 : Blo 447780 11085265 := bstep (se 2 (by rfl) ⟨4156974, by rfl⟩ : syracuseStep 11085265 = 8313949) B8313949
theorem B1156619 : Blo 447780 1156619 := bstep (se 1 (by rfl) ⟨867464, by rfl⟩ : syracuseStep 1156619 = 1734929) B1734929
theorem B960059 : Blo 447780 960059 := bstep (se 1 (by rfl) ⟨720044, by rfl⟩ : syracuseStep 960059 = 1440089) B1440089
theorem B37561931 : Blo 447780 37561931 := bstep (se 1 (by rfl) ⟨28171448, by rfl⟩ : syracuseStep 37561931 = 56342897) B56342897
theorem B4990643 : Blo 447780 4990643 := bstep (se 1 (by rfl) ⟨3742982, by rfl⟩ : syracuseStep 4990643 = 7485965) B7485965
theorem B16361189 : Blo 447780 16361189 := bstep (se 4 (by rfl) ⟨1533861, by rfl⟩ : syracuseStep 16361189 = 3067723) B3067723
theorem B2893583 : Blo 447780 2893583 := bstep (se 1 (by rfl) ⟨2170187, by rfl⟩ : syracuseStep 2893583 = 4340375) B4340375
theorem B1517345 : Blo 447780 1517345 := bstep (se 2 (by rfl) ⟨569004, by rfl⟩ : syracuseStep 1517345 = 1138009) B1138009
theorem B18425717 : Blo 447780 18425717 := bstep (se 5 (by rfl) ⟨863705, by rfl⟩ : syracuseStep 18425717 = 1727411) B1727411
theorem B927607 : Blo 447780 927607 := bstep (se 1 (by rfl) ⟨695705, by rfl⟩ : syracuseStep 927607 = 1391411) B1391411
theorem B2434951 : Blo 447780 2434951 := bstep (se 1 (by rfl) ⟨1826213, by rfl⟩ : syracuseStep 2434951 = 3652427) B3652427
theorem B1714243 : Blo 447780 1714243 := bstep (se 1 (by rfl) ⟨1285682, by rfl⟩ : syracuseStep 1714243 = 2571365) B2571365
theorem B567415 : Blo 447780 567415 := bstep (se 1 (by rfl) ⟨425561, by rfl⟩ : syracuseStep 567415 = 851123) B851123
theorem B2304119 : Blo 447780 2304119 := bstep (se 1 (by rfl) ⟨1728089, by rfl⟩ : syracuseStep 2304119 = 3456179) B3456179
theorem B5843117 : Blo 447780 5843117 := bstep (se 3 (by rfl) ⟨1095584, by rfl⟩ : syracuseStep 5843117 = 2191169) B2191169
theorem B1517939 : Blo 447780 1517939 := bstep (se 1 (by rfl) ⟨1138454, by rfl⟩ : syracuseStep 1517939 = 2276909) B2276909
theorem B1714547 : Blo 447780 1714547 := bstep (se 1 (by rfl) ⟨1285910, by rfl⟩ : syracuseStep 1714547 = 2571821) B2571821
theorem B7285139 : Blo 447780 7285139 := bstep (se 1 (by rfl) ⟨5463854, by rfl⟩ : syracuseStep 7285139 = 10927709) B10927709
theorem B567739 : Blo 447780 567739 := bstep (se 1 (by rfl) ⟨425804, by rfl⟩ : syracuseStep 567739 = 851609) B851609
theorem B1616699 : Blo 447780 1616699 := bstep (se 1 (by rfl) ⟨1212524, by rfl⟩ : syracuseStep 1616699 = 2425049) B2425049
theorem B1715003 : Blo 447780 1715003 := bstep (se 1 (by rfl) ⟨1286252, by rfl⟩ : syracuseStep 1715003 = 2572505) B2572505
theorem B568235 : Blo 447780 568235 := bstep (se 1 (by rfl) ⟨426176, by rfl⟩ : syracuseStep 568235 = 852353) B852353
theorem B4336685 : Blo 447780 4336685 := bstep (se 3 (by rfl) ⟨813128, by rfl⟩ : syracuseStep 4336685 = 1626257) B1626257
theorem B4337027 : Blo 447780 4337027 := bstep (se 1 (by rfl) ⟨3252770, by rfl⟩ : syracuseStep 4337027 = 6505541) B6505541
theorem B568711 : Blo 447780 568711 := bstep (se 1 (by rfl) ⟨426533, by rfl⟩ : syracuseStep 568711 = 853067) B853067
theorem B2272697 : Blo 447780 2272697 := bstep (se 2 (by rfl) ⟨852261, by rfl⟩ : syracuseStep 2272697 = 1704523) B1704523
theorem B2436637 : Blo 447780 2436637 := bstep (se 3 (by rfl) ⟨456869, by rfl⟩ : syracuseStep 2436637 = 913739) B913739
theorem B1027703 : Blo 447780 1027703 := bstep (se 1 (by rfl) ⟨770777, by rfl⟩ : syracuseStep 1027703 = 1541555) B1541555
theorem B569207 : Blo 447780 569207 := bstep (se 1 (by rfl) ⟨426905, by rfl⟩ : syracuseStep 569207 = 853811) B853811
theorem B503815 : Blo 447780 503815 := bstep (se 1 (by rfl) ⟨377861, by rfl⟩ : syracuseStep 503815 = 755723) B755723
theorem B569359 : Blo 447780 569359 := bstep (se 1 (by rfl) ⟨427019, by rfl⟩ : syracuseStep 569359 = 854039) B854039
theorem B503995 : Blo 447780 503995 := bstep (se 1 (by rfl) ⟨377996, by rfl⟩ : syracuseStep 503995 = 755993) B755993
theorem B569531 : Blo 447780 569531 := bstep (se 1 (by rfl) ⟨427148, by rfl⟩ : syracuseStep 569531 = 854297) B854297
theorem B2568449 : Blo 447780 2568449 := bstep (se 2 (by rfl) ⟨963168, by rfl⟩ : syracuseStep 2568449 = 1926337) B1926337
theorem B504463 : Blo 447780 504463 := bstep (se 1 (by rfl) ⟨378347, by rfl⟩ : syracuseStep 504463 = 756695) B756695
theorem B2273993 : Blo 447780 2273993 := bstep (se 2 (by rfl) ⟨852747, by rfl⟩ : syracuseStep 2273993 = 1705495) B1705495
theorem B2568905 : Blo 447780 2568905 := bstep (se 2 (by rfl) ⟨963339, by rfl⟩ : syracuseStep 2568905 = 1926679) B1926679
theorem B5550923 : Blo 447780 5550923 := bstep (se 1 (by rfl) ⟨4163192, by rfl⟩ : syracuseStep 5550923 = 8326385) B8326385
theorem B1520531 : Blo 447780 1520531 := bstep (se 1 (by rfl) ⟨1140398, by rfl⟩ : syracuseStep 1520531 = 2280797) B2280797
theorem B504967 : Blo 447780 504967 := bstep (se 1 (by rfl) ⟨378725, by rfl⟩ : syracuseStep 504967 = 757451) B757451
theorem B570503 : Blo 447780 570503 := bstep (se 1 (by rfl) ⟨427877, by rfl⟩ : syracuseStep 570503 = 855755) B855755
theorem B4306121 : Blo 447780 4306121 := bstep (se 2 (by rfl) ⟨1614795, by rfl⟩ : syracuseStep 4306121 = 3229591) B3229591
theorem B505147 : Blo 447780 505147 := bstep (se 1 (by rfl) ⟨378860, by rfl⟩ : syracuseStep 505147 = 757721) B757721
theorem B1095227 : Blo 447780 1095227 := bstep (se 1 (by rfl) ⟨821420, by rfl⟩ : syracuseStep 1095227 = 1642841) B1642841
theorem B3421925 : Blo 447780 3421925 := bstep (se 4 (by rfl) ⟨320805, by rfl⟩ : syracuseStep 3421925 = 641611) B641611
theorem B505615 : Blo 447780 505615 := bstep (se 1 (by rfl) ⟨379211, by rfl⟩ : syracuseStep 505615 = 758423) B758423
theorem B571151 : Blo 447780 571151 := bstep (se 1 (by rfl) ⟨428363, by rfl⟩ : syracuseStep 571151 = 856727) B856727
theorem B1849387 : Blo 447780 1849387 := bstep (se 1 (by rfl) ⟨1387040, by rfl⟩ : syracuseStep 1849387 = 2774081) B2774081
theorem B506119 : Blo 447780 506119 := bstep (se 1 (by rfl) ⟨379589, by rfl⟩ : syracuseStep 506119 = 759179) B759179
theorem B1521935 : Blo 447780 1521935 := bstep (se 1 (by rfl) ⟨1141451, by rfl⟩ : syracuseStep 1521935 = 2282903) B2282903
theorem B506299 : Blo 447780 506299 := bstep (se 1 (by rfl) ⟨379724, by rfl⟩ : syracuseStep 506299 = 759449) B759449
theorem B6928861 : Blo 447780 6928861 := bstep (se 3 (by rfl) ⟨1299161, by rfl⟩ : syracuseStep 6928861 = 2598323) B2598323
theorem B1522205 : Blo 447780 1522205 := bstep (se 3 (by rfl) ⟨285413, by rfl⟩ : syracuseStep 1522205 = 570827) B570827
theorem B539255 : Blo 447780 539255 := bstep (se 1 (by rfl) ⟨404441, by rfl⟩ : syracuseStep 539255 = 808883) B808883
theorem B506767 : Blo 447780 506767 := bstep (se 1 (by rfl) ⟨380075, by rfl⟩ : syracuseStep 506767 = 760151) B760151
theorem B539563 : Blo 447780 539563 := bstep (se 1 (by rfl) ⟨404672, by rfl⟩ : syracuseStep 539563 = 809345) B809345
theorem B1915933 : Blo 447780 1915933 := bstep (se 3 (by rfl) ⟨359237, by rfl⟩ : syracuseStep 1915933 = 718475) B718475
theorem B507271 : Blo 447780 507271 := bstep (se 1 (by rfl) ⟨380453, by rfl⟩ : syracuseStep 507271 = 760907) B760907
theorem B540091 : Blo 447780 540091 := bstep (se 1 (by rfl) ⟨405068, by rfl⟩ : syracuseStep 540091 = 810137) B810137
theorem B638479 : Blo 447780 638479 := bstep (se 1 (by rfl) ⟨478859, by rfl⟩ : syracuseStep 638479 = 957719) B957719
theorem B507451 : Blo 447780 507451 := bstep (se 1 (by rfl) ⟨380588, by rfl⟩ : syracuseStep 507451 = 761177) B761177
theorem B769655 : Blo 447780 769655 := bstep (se 1 (by rfl) ⟨577241, by rfl⟩ : syracuseStep 769655 = 1154483) B1154483
theorem B638599 : Blo 447780 638599 := bstep (se 1 (by rfl) ⟨478949, by rfl⟩ : syracuseStep 638599 = 957899) B957899
theorem B1457921 : Blo 447780 1457921 := bstep (se 2 (by rfl) ⟨546720, by rfl⟩ : syracuseStep 1457921 = 1093441) B1093441
theorem B1523609 : Blo 447780 1523609 := bstep (se 2 (by rfl) ⟨571353, by rfl⟩ : syracuseStep 1523609 = 1142707) B1142707
theorem B671675 : Blo 447780 671675 := bstep (se 1 (by rfl) ⟨503756, by rfl⟩ : syracuseStep 671675 = 1007513) B1007513
theorem B671735 : Blo 447780 671735 := bstep (se 1 (by rfl) ⟨503801, by rfl⟩ : syracuseStep 671735 = 1007603) B1007603
theorem B671759 : Blo 447780 671759 := bstep (se 1 (by rfl) ⟨503819, by rfl⟩ : syracuseStep 671759 = 1007639) B1007639
theorem B507919 : Blo 447780 507919 := bstep (se 1 (by rfl) ⟨380939, by rfl⟩ : syracuseStep 507919 = 761879) B761879
theorem B671801 : Blo 447780 671801 := bstep (se 2 (by rfl) ⟨251925, by rfl⟩ : syracuseStep 671801 = 503851) B503851
theorem B671879 : Blo 447780 671879 := bstep (se 1 (by rfl) ⟨503909, by rfl⟩ : syracuseStep 671879 = 1007819) B1007819
theorem B671915 : Blo 447780 671915 := bstep (se 1 (by rfl) ⟨503936, by rfl⟩ : syracuseStep 671915 = 1007873) B1007873
theorem B671945 : Blo 447780 671945 := bstep (se 2 (by rfl) ⟨251979, by rfl⟩ : syracuseStep 671945 = 503959) B503959
theorem B672059 : Blo 447780 672059 := bstep (se 1 (by rfl) ⟨504044, by rfl⟩ : syracuseStep 672059 = 1008089) B1008089
theorem B672119 : Blo 447780 672119 := bstep (se 1 (by rfl) ⟨504089, by rfl⟩ : syracuseStep 672119 = 1008179) B1008179
theorem B672143 : Blo 447780 672143 := bstep (se 1 (by rfl) ⟨504107, by rfl⟩ : syracuseStep 672143 = 1008215) B1008215
theorem B672185 : Blo 447780 672185 := bstep (se 2 (by rfl) ⟨252069, by rfl⟩ : syracuseStep 672185 = 504139) B504139
theorem B672263 : Blo 447780 672263 := bstep (se 1 (by rfl) ⟨504197, by rfl⟩ : syracuseStep 672263 = 1008395) B1008395
theorem B2572823 : Blo 447780 2572823 := bstep (se 1 (by rfl) ⟨1929617, by rfl⟩ : syracuseStep 2572823 = 3859235) B3859235
theorem B672299 : Blo 447780 672299 := bstep (se 1 (by rfl) ⟨504224, by rfl⟩ : syracuseStep 672299 = 1008449) B1008449
theorem B4112963 : Blo 447780 4112963 := bstep (se 1 (by rfl) ⟨3084722, by rfl⟩ : syracuseStep 4112963 = 6169445) B6169445
theorem B672329 : Blo 447780 672329 := bstep (se 2 (by rfl) ⟨252123, by rfl⟩ : syracuseStep 672329 = 504247) B504247
theorem B1524311 : Blo 447780 1524311 := bstep (se 1 (by rfl) ⟨1143233, by rfl⟩ : syracuseStep 1524311 = 2286467) B2286467
theorem B672443 : Blo 447780 672443 := bstep (se 1 (by rfl) ⟨504332, by rfl⟩ : syracuseStep 672443 = 1008665) B1008665
theorem B672503 : Blo 447780 672503 := bstep (se 1 (by rfl) ⟨504377, by rfl⟩ : syracuseStep 672503 = 1008755) B1008755
theorem B672527 : Blo 447780 672527 := bstep (se 1 (by rfl) ⟨504395, by rfl⟩ : syracuseStep 672527 = 1008791) B1008791
theorem B607019 : Blo 447780 607019 := bstep (se 1 (by rfl) ⟨455264, by rfl⟩ : syracuseStep 607019 = 910529) B910529
theorem B672569 : Blo 447780 672569 := bstep (se 2 (by rfl) ⟨252213, by rfl⟩ : syracuseStep 672569 = 504427) B504427
theorem B672647 : Blo 447780 672647 := bstep (se 1 (by rfl) ⟨504485, by rfl⟩ : syracuseStep 672647 = 1008971) B1008971
theorem B3851171 : Blo 447780 3851171 := bstep (se 1 (by rfl) ⟨2888378, by rfl⟩ : syracuseStep 3851171 = 5776757) B5776757
theorem B672683 : Blo 447780 672683 := bstep (se 1 (by rfl) ⟨504512, by rfl⟩ : syracuseStep 672683 = 1009025) B1009025
theorem B672713 : Blo 447780 672713 := bstep (se 2 (by rfl) ⟨252267, by rfl⟩ : syracuseStep 672713 = 504535) B504535
theorem B640057 : Blo 447780 640057 := bstep (se 2 (by rfl) ⟨240021, by rfl⟩ : syracuseStep 640057 = 480043) B480043
theorem B672827 : Blo 447780 672827 := bstep (se 1 (by rfl) ⟨504620, by rfl⟩ : syracuseStep 672827 = 1009241) B1009241
theorem B672887 : Blo 447780 672887 := bstep (se 1 (by rfl) ⟨504665, by rfl⟩ : syracuseStep 672887 = 1009331) B1009331
theorem B672911 : Blo 447780 672911 := bstep (se 1 (by rfl) ⟨504683, by rfl⟩ : syracuseStep 672911 = 1009367) B1009367
theorem B672953 : Blo 447780 672953 := bstep (se 2 (by rfl) ⟨252357, by rfl⟩ : syracuseStep 672953 = 504715) B504715
theorem B673031 : Blo 447780 673031 := bstep (se 1 (by rfl) ⟨504773, by rfl⟩ : syracuseStep 673031 = 1009547) B1009547
theorem B673067 : Blo 447780 673067 := bstep (se 1 (by rfl) ⟨504800, by rfl⟩ : syracuseStep 673067 = 1009601) B1009601
theorem B673097 : Blo 447780 673097 := bstep (se 2 (by rfl) ⟨252411, by rfl⟩ : syracuseStep 673097 = 504823) B504823
theorem B673211 : Blo 447780 673211 := bstep (se 1 (by rfl) ⟨504908, by rfl⟩ : syracuseStep 673211 = 1009817) B1009817
theorem B673271 : Blo 447780 673271 := bstep (se 1 (by rfl) ⟨504953, by rfl⟩ : syracuseStep 673271 = 1009907) B1009907
theorem B673295 : Blo 447780 673295 := bstep (se 1 (by rfl) ⟨504971, by rfl⟩ : syracuseStep 673295 = 1009943) B1009943
theorem B673337 : Blo 447780 673337 := bstep (se 2 (by rfl) ⟨252501, by rfl⟩ : syracuseStep 673337 = 505003) B505003
theorem B37045835 : Blo 447780 37045835 := bstep (se 1 (by rfl) ⟨27784376, by rfl⟩ : syracuseStep 37045835 = 55568753) B55568753
theorem B673415 : Blo 447780 673415 := bstep (se 1 (by rfl) ⟨505061, by rfl⟩ : syracuseStep 673415 = 1010123) B1010123
theorem B673451 : Blo 447780 673451 := bstep (se 1 (by rfl) ⟨505088, by rfl⟩ : syracuseStep 673451 = 1010177) B1010177
theorem B673481 : Blo 447780 673481 := bstep (se 2 (by rfl) ⟨252555, by rfl⟩ : syracuseStep 673481 = 505111) B505111
theorem B673595 : Blo 447780 673595 := bstep (se 1 (by rfl) ⟨505196, by rfl⟩ : syracuseStep 673595 = 1010393) B1010393
theorem B673655 : Blo 447780 673655 := bstep (se 1 (by rfl) ⟨505241, by rfl⟩ : syracuseStep 673655 = 1010483) B1010483
theorem B673679 : Blo 447780 673679 := bstep (se 1 (by rfl) ⟨505259, by rfl⟩ : syracuseStep 673679 = 1010519) B1010519
theorem B2312081 : Blo 447780 2312081 := bstep (se 2 (by rfl) ⟨867030, by rfl⟩ : syracuseStep 2312081 = 1734061) B1734061
theorem B673721 : Blo 447780 673721 := bstep (se 2 (by rfl) ⟨252645, by rfl⟩ : syracuseStep 673721 = 505291) B505291
theorem B673799 : Blo 447780 673799 := bstep (se 1 (by rfl) ⟨505349, by rfl⟩ : syracuseStep 673799 = 1010699) B1010699
theorem B673835 : Blo 447780 673835 := bstep (se 1 (by rfl) ⟨505376, by rfl⟩ : syracuseStep 673835 = 1010753) B1010753
theorem B673865 : Blo 447780 673865 := bstep (se 2 (by rfl) ⟨252699, by rfl⟩ : syracuseStep 673865 = 505399) B505399
theorem B673979 : Blo 447780 673979 := bstep (se 1 (by rfl) ⟨505484, by rfl⟩ : syracuseStep 673979 = 1010969) B1010969
theorem B674039 : Blo 447780 674039 := bstep (se 1 (by rfl) ⟨505529, by rfl⟩ : syracuseStep 674039 = 1011059) B1011059
theorem B641287 : Blo 447780 641287 := bstep (se 1 (by rfl) ⟨480965, by rfl⟩ : syracuseStep 641287 = 961931) B961931
theorem B674063 : Blo 447780 674063 := bstep (se 1 (by rfl) ⟨505547, by rfl⟩ : syracuseStep 674063 = 1011095) B1011095
theorem B674105 : Blo 447780 674105 := bstep (se 2 (by rfl) ⟨252789, by rfl⟩ : syracuseStep 674105 = 505579) B505579
theorem B674183 : Blo 447780 674183 := bstep (se 1 (by rfl) ⟨505637, by rfl⟩ : syracuseStep 674183 = 1011275) B1011275
theorem B2279825 : Blo 447780 2279825 := bstep (se 2 (by rfl) ⟨854934, by rfl⟩ : syracuseStep 2279825 = 1709869) B1709869
theorem B674219 : Blo 447780 674219 := bstep (se 1 (by rfl) ⟨505664, by rfl⟩ : syracuseStep 674219 = 1011329) B1011329
theorem B674249 : Blo 447780 674249 := bstep (se 2 (by rfl) ⟨252843, by rfl⟩ : syracuseStep 674249 = 505687) B505687
theorem B5130701 : Blo 447780 5130701 := bstep (se 3 (by rfl) ⟨962006, by rfl⟩ : syracuseStep 5130701 = 1924013) B1924013
theorem B674363 : Blo 447780 674363 := bstep (se 1 (by rfl) ⟨505772, by rfl⟩ : syracuseStep 674363 = 1011545) B1011545
theorem B674423 : Blo 447780 674423 := bstep (se 1 (by rfl) ⟨505817, by rfl⟩ : syracuseStep 674423 = 1011635) B1011635
theorem B674447 : Blo 447780 674447 := bstep (se 1 (by rfl) ⟨505835, by rfl⟩ : syracuseStep 674447 = 1011671) B1011671
theorem B674489 : Blo 447780 674489 := bstep (se 2 (by rfl) ⟨252933, by rfl⟩ : syracuseStep 674489 = 505867) B505867
theorem B674567 : Blo 447780 674567 := bstep (se 1 (by rfl) ⟨505925, by rfl⟩ : syracuseStep 674567 = 1011851) B1011851
theorem B674603 : Blo 447780 674603 := bstep (se 1 (by rfl) ⟨505952, by rfl⟩ : syracuseStep 674603 = 1011905) B1011905
theorem B674633 : Blo 447780 674633 := bstep (se 2 (by rfl) ⟨252987, by rfl⟩ : syracuseStep 674633 = 505975) B505975
theorem B1821575 : Blo 447780 1821575 := bstep (se 1 (by rfl) ⟨1366181, by rfl⟩ : syracuseStep 1821575 = 2732363) B2732363
theorem B674747 : Blo 447780 674747 := bstep (se 1 (by rfl) ⟨506060, by rfl⟩ : syracuseStep 674747 = 1012121) B1012121
theorem B674807 : Blo 447780 674807 := bstep (se 1 (by rfl) ⟨506105, by rfl⟩ : syracuseStep 674807 = 1012211) B1012211
theorem B674831 : Blo 447780 674831 := bstep (se 1 (by rfl) ⟨506123, by rfl⟩ : syracuseStep 674831 = 1012247) B1012247
theorem B674873 : Blo 447780 674873 := bstep (se 2 (by rfl) ⟨253077, by rfl⟩ : syracuseStep 674873 = 506155) B506155
theorem B642107 : Blo 447780 642107 := bstep (se 1 (by rfl) ⟨481580, by rfl⟩ : syracuseStep 642107 = 963161) B963161
theorem B674951 : Blo 447780 674951 := bstep (se 1 (by rfl) ⟨506213, by rfl⟩ : syracuseStep 674951 = 1012427) B1012427
theorem B674987 : Blo 447780 674987 := bstep (se 1 (by rfl) ⟨506240, by rfl⟩ : syracuseStep 674987 = 1012481) B1012481
theorem B675017 : Blo 447780 675017 := bstep (se 2 (by rfl) ⟨253131, by rfl⟩ : syracuseStep 675017 = 506263) B506263
theorem B675131 : Blo 447780 675131 := bstep (se 1 (by rfl) ⟨506348, by rfl⟩ : syracuseStep 675131 = 1012697) B1012697
theorem B1756475 : Blo 447780 1756475 := bstep (se 1 (by rfl) ⟨1317356, by rfl⟩ : syracuseStep 1756475 = 2634713) B2634713
theorem B1133939 : Blo 447780 1133939 := bstep (se 1 (by rfl) ⟨850454, by rfl⟩ : syracuseStep 1133939 = 1700909) B1700909
theorem B675191 : Blo 447780 675191 := bstep (se 1 (by rfl) ⟨506393, by rfl⟩ : syracuseStep 675191 = 1012787) B1012787
theorem B1133959 : Blo 447780 1133959 := bstep (se 1 (by rfl) ⟨850469, by rfl⟩ : syracuseStep 1133959 = 1700939) B1700939
theorem B675215 : Blo 447780 675215 := bstep (se 1 (by rfl) ⟨506411, by rfl⟩ : syracuseStep 675215 = 1012823) B1012823
theorem B675257 : Blo 447780 675257 := bstep (se 2 (by rfl) ⟨253221, by rfl⟩ : syracuseStep 675257 = 506443) B506443
theorem B675335 : Blo 447780 675335 := bstep (se 1 (by rfl) ⟨506501, by rfl⟩ : syracuseStep 675335 = 1013003) B1013003
theorem B675371 : Blo 447780 675371 := bstep (se 1 (by rfl) ⟨506528, by rfl⟩ : syracuseStep 675371 = 1013057) B1013057
theorem B675401 : Blo 447780 675401 := bstep (se 2 (by rfl) ⟨253275, by rfl⟩ : syracuseStep 675401 = 506551) B506551
theorem B1920631 : Blo 447780 1920631 := bstep (se 1 (by rfl) ⟨1440473, by rfl⟩ : syracuseStep 1920631 = 2880947) B2880947
theorem B1134233 : Blo 447780 1134233 := bstep (se 2 (by rfl) ⟨425337, by rfl⟩ : syracuseStep 1134233 = 850675) B850675
theorem B609977 : Blo 447780 609977 := bstep (se 2 (by rfl) ⟨228741, by rfl⟩ : syracuseStep 609977 = 457483) B457483
theorem B642745 : Blo 447780 642745 := bstep (se 2 (by rfl) ⟨241029, by rfl⟩ : syracuseStep 642745 = 482059) B482059
theorem B675515 : Blo 447780 675515 := bstep (se 1 (by rfl) ⟨506636, by rfl⟩ : syracuseStep 675515 = 1013273) B1013273
theorem B675575 : Blo 447780 675575 := bstep (se 1 (by rfl) ⟨506681, by rfl⟩ : syracuseStep 675575 = 1013363) B1013363
theorem B675599 : Blo 447780 675599 := bstep (se 1 (by rfl) ⟨506699, by rfl⟩ : syracuseStep 675599 = 1013399) B1013399
theorem B675641 : Blo 447780 675641 := bstep (se 2 (by rfl) ⟨253365, by rfl⟩ : syracuseStep 675641 = 506731) B506731
theorem B1134395 : Blo 447780 1134395 := bstep (se 1 (by rfl) ⟨850796, by rfl⟩ : syracuseStep 1134395 = 1701593) B1701593
theorem B675719 : Blo 447780 675719 := bstep (se 1 (by rfl) ⟨506789, by rfl⟩ : syracuseStep 675719 = 1013579) B1013579
theorem B675755 : Blo 447780 675755 := bstep (se 1 (by rfl) ⟨506816, by rfl⟩ : syracuseStep 675755 = 1013633) B1013633
theorem B675785 : Blo 447780 675785 := bstep (se 2 (by rfl) ⟨253419, by rfl⟩ : syracuseStep 675785 = 506839) B506839
theorem B1134607 : Blo 447780 1134607 := bstep (se 1 (by rfl) ⟨850955, by rfl⟩ : syracuseStep 1134607 = 1701911) B1701911
theorem B675899 : Blo 447780 675899 := bstep (se 1 (by rfl) ⟨506924, by rfl⟩ : syracuseStep 675899 = 1013849) B1013849
theorem B675959 : Blo 447780 675959 := bstep (se 1 (by rfl) ⟨506969, by rfl⟩ : syracuseStep 675959 = 1013939) B1013939
theorem B675983 : Blo 447780 675983 := bstep (se 1 (by rfl) ⟨506987, by rfl⟩ : syracuseStep 675983 = 1013975) B1013975
theorem B676025 : Blo 447780 676025 := bstep (se 2 (by rfl) ⟨253509, by rfl⟩ : syracuseStep 676025 = 507019) B507019
theorem B676103 : Blo 447780 676103 := bstep (se 1 (by rfl) ⟨507077, by rfl⟩ : syracuseStep 676103 = 1014155) B1014155
theorem B1134881 : Blo 447780 1134881 := bstep (se 2 (by rfl) ⟨425580, by rfl⟩ : syracuseStep 1134881 = 851161) B851161
theorem B676139 : Blo 447780 676139 := bstep (se 1 (by rfl) ⟨507104, by rfl⟩ : syracuseStep 676139 = 1014209) B1014209
theorem B676169 : Blo 447780 676169 := bstep (se 2 (by rfl) ⟨253563, by rfl⟩ : syracuseStep 676169 = 507127) B507127
theorem B676283 : Blo 447780 676283 := bstep (se 1 (by rfl) ⟨507212, by rfl⟩ : syracuseStep 676283 = 1014425) B1014425
theorem B2281931 : Blo 447780 2281931 := bstep (se 1 (by rfl) ⟨1711448, by rfl⟩ : syracuseStep 2281931 = 3422897) B3422897
theorem B2871773 : Blo 447780 2871773 := bstep (se 3 (by rfl) ⟨538457, by rfl⟩ : syracuseStep 2871773 = 1076915) B1076915
theorem B676343 : Blo 447780 676343 := bstep (se 1 (by rfl) ⟨507257, by rfl⟩ : syracuseStep 676343 = 1014515) B1014515
theorem B676367 : Blo 447780 676367 := bstep (se 1 (by rfl) ⟨507275, by rfl⟩ : syracuseStep 676367 = 1014551) B1014551
theorem B18469397 : Blo 447780 18469397 := bstep (se 6 (by rfl) ⟨432876, by rfl⟩ : syracuseStep 18469397 = 865753) B865753
theorem B676409 : Blo 447780 676409 := bstep (se 2 (by rfl) ⟨253653, by rfl⟩ : syracuseStep 676409 = 507307) B507307
theorem B676487 : Blo 447780 676487 := bstep (se 1 (by rfl) ⟨507365, by rfl⟩ : syracuseStep 676487 = 1014731) B1014731
theorem B676523 : Blo 447780 676523 := bstep (se 1 (by rfl) ⟨507392, by rfl⟩ : syracuseStep 676523 = 1014785) B1014785
theorem B676553 : Blo 447780 676553 := bstep (se 2 (by rfl) ⟨253707, by rfl⟩ : syracuseStep 676553 = 507415) B507415
theorem B2282255 : Blo 447780 2282255 := bstep (se 1 (by rfl) ⟨1711691, by rfl⟩ : syracuseStep 2282255 = 3423383) B3423383
theorem B676667 : Blo 447780 676667 := bstep (se 1 (by rfl) ⟨507500, by rfl⟩ : syracuseStep 676667 = 1015001) B1015001
theorem B3068761 : Blo 447780 3068761 := bstep (se 2 (by rfl) ⟨1150785, by rfl⟩ : syracuseStep 3068761 = 2301571) B2301571
theorem B676727 : Blo 447780 676727 := bstep (se 1 (by rfl) ⟨507545, by rfl⟩ : syracuseStep 676727 = 1015091) B1015091
theorem B676751 : Blo 447780 676751 := bstep (se 1 (by rfl) ⟨507563, by rfl⟩ : syracuseStep 676751 = 1015127) B1015127
theorem B1561529 : Blo 447780 1561529 := bstep (se 2 (by rfl) ⟨585573, by rfl⟩ : syracuseStep 1561529 = 1171147) B1171147
theorem B676793 : Blo 447780 676793 := bstep (se 2 (by rfl) ⟨253797, by rfl⟩ : syracuseStep 676793 = 507595) B507595
theorem B2741201 : Blo 447780 2741201 := bstep (se 2 (by rfl) ⟨1027950, by rfl⟩ : syracuseStep 2741201 = 2055901) B2055901
theorem B676871 : Blo 447780 676871 := bstep (se 1 (by rfl) ⟨507653, by rfl⟩ : syracuseStep 676871 = 1015307) B1015307
theorem B8180747 : Blo 447780 8180747 := bstep (se 1 (by rfl) ⟨6135560, by rfl⟩ : syracuseStep 8180747 = 12271121) B12271121
theorem B676907 : Blo 447780 676907 := bstep (se 1 (by rfl) ⟨507680, by rfl⟩ : syracuseStep 676907 = 1015361) B1015361
theorem B676937 : Blo 447780 676937 := bstep (se 2 (by rfl) ⟨253851, by rfl⟩ : syracuseStep 676937 = 507703) B507703
theorem B677051 : Blo 447780 677051 := bstep (se 1 (by rfl) ⟨507788, by rfl⟩ : syracuseStep 677051 = 1015577) B1015577
theorem B677111 : Blo 447780 677111 := bstep (se 1 (by rfl) ⟨507833, by rfl⟩ : syracuseStep 677111 = 1015667) B1015667
theorem B1922305 : Blo 447780 1922305 := bstep (se 2 (by rfl) ⟨720864, by rfl⟩ : syracuseStep 1922305 = 1441729) B1441729
theorem B1135883 : Blo 447780 1135883 := bstep (se 1 (by rfl) ⟨851912, by rfl⟩ : syracuseStep 1135883 = 1703825) B1703825
theorem B677135 : Blo 447780 677135 := bstep (se 1 (by rfl) ⟨507851, by rfl⟩ : syracuseStep 677135 = 1015703) B1015703
theorem B4150561 : Blo 447780 4150561 := bstep (se 2 (by rfl) ⟨1556460, by rfl⟩ : syracuseStep 4150561 = 3112921) B3112921
theorem B677177 : Blo 447780 677177 := bstep (se 2 (by rfl) ⟨253941, by rfl⟩ : syracuseStep 677177 = 507883) B507883
theorem B447803 : Blo 447780 447803 := bstep (se 1 (by rfl) ⟨335852, by rfl⟩ : syracuseStep 447803 = 671705) B671705
theorem B447879 : Blo 447780 447879 := bstep (se 1 (by rfl) ⟨335909, by rfl⟩ : syracuseStep 447879 = 671819) B671819
theorem B677255 : Blo 447780 677255 := bstep (se 1 (by rfl) ⟨507941, by rfl⟩ : syracuseStep 677255 = 1015883) B1015883
theorem B447887 : Blo 447780 447887 := bstep (se 1 (by rfl) ⟨335915, by rfl⟩ : syracuseStep 447887 = 671831) B671831
theorem B677291 : Blo 447780 677291 := bstep (se 1 (by rfl) ⟨507968, by rfl⟩ : syracuseStep 677291 = 1015937) B1015937
theorem B447931 : Blo 447780 447931 := bstep (se 1 (by rfl) ⟨335948, by rfl⟩ : syracuseStep 447931 = 671897) B671897
theorem B677321 : Blo 447780 677321 := bstep (se 2 (by rfl) ⟨253995, by rfl⟩ : syracuseStep 677321 = 507991) B507991
theorem B448007 : Blo 447780 448007 := bstep (se 1 (by rfl) ⟨336005, by rfl⟩ : syracuseStep 448007 = 672011) B672011
theorem B2151947 : Blo 447780 2151947 := bstep (se 1 (by rfl) ⟨1613960, by rfl⟩ : syracuseStep 2151947 = 3227921) B3227921
theorem B448015 : Blo 447780 448015 := bstep (se 1 (by rfl) ⟨336011, by rfl⟩ : syracuseStep 448015 = 672023) B672023
theorem B448059 : Blo 447780 448059 := bstep (se 1 (by rfl) ⟨336044, by rfl⟩ : syracuseStep 448059 = 672089) B672089
theorem B677435 : Blo 447780 677435 := bstep (se 1 (by rfl) ⟨508076, by rfl⟩ : syracuseStep 677435 = 1016153) B1016153
theorem B677495 : Blo 447780 677495 := bstep (se 1 (by rfl) ⟨508121, by rfl⟩ : syracuseStep 677495 = 1016243) B1016243
theorem B448135 : Blo 447780 448135 := bstep (se 1 (by rfl) ⟨336101, by rfl⟩ : syracuseStep 448135 = 672203) B672203
theorem B448143 : Blo 447780 448143 := bstep (se 1 (by rfl) ⟨336107, by rfl⟩ : syracuseStep 448143 = 672215) B672215
theorem B677519 : Blo 447780 677519 := bstep (se 1 (by rfl) ⟨508139, by rfl⟩ : syracuseStep 677519 = 1016279) B1016279
theorem B677561 : Blo 447780 677561 := bstep (se 2 (by rfl) ⟨254085, by rfl⟩ : syracuseStep 677561 = 508171) B508171
theorem B448187 : Blo 447780 448187 := bstep (se 1 (by rfl) ⟨336140, by rfl⟩ : syracuseStep 448187 = 672281) B672281
theorem B448263 : Blo 447780 448263 := bstep (se 1 (by rfl) ⟨336197, by rfl⟩ : syracuseStep 448263 = 672395) B672395
theorem B677639 : Blo 447780 677639 := bstep (se 1 (by rfl) ⟨508229, by rfl⟩ : syracuseStep 677639 = 1016459) B1016459
theorem B448271 : Blo 447780 448271 := bstep (se 1 (by rfl) ⟨336203, by rfl⟩ : syracuseStep 448271 = 672407) B672407
theorem B4118323 : Blo 447780 4118323 := bstep (se 1 (by rfl) ⟨3088742, by rfl⟩ : syracuseStep 4118323 = 6177485) B6177485
theorem B448315 : Blo 447780 448315 := bstep (se 1 (by rfl) ⟨336236, by rfl⟩ : syracuseStep 448315 = 672473) B672473
theorem B448391 : Blo 447780 448391 := bstep (se 1 (by rfl) ⟨336293, by rfl⟩ : syracuseStep 448391 = 672587) B672587
theorem B448399 : Blo 447780 448399 := bstep (se 1 (by rfl) ⟨336299, by rfl⟩ : syracuseStep 448399 = 672599) B672599
theorem B1136531 : Blo 447780 1136531 := bstep (se 1 (by rfl) ⟨852398, by rfl⟩ : syracuseStep 1136531 = 1704797) B1704797
theorem B448443 : Blo 447780 448443 := bstep (se 1 (by rfl) ⟨336332, by rfl⟩ : syracuseStep 448443 = 672665) B672665
theorem B448519 : Blo 447780 448519 := bstep (se 1 (by rfl) ⟨336389, by rfl⟩ : syracuseStep 448519 = 672779) B672779
theorem B448527 : Blo 447780 448527 := bstep (se 1 (by rfl) ⟨336395, by rfl⟩ : syracuseStep 448527 = 672791) B672791
theorem B448571 : Blo 447780 448571 := bstep (se 1 (by rfl) ⟨336428, by rfl⟩ : syracuseStep 448571 = 672857) B672857
theorem B448647 : Blo 447780 448647 := bstep (se 1 (by rfl) ⟨336485, by rfl⟩ : syracuseStep 448647 = 672971) B672971
theorem B448655 : Blo 447780 448655 := bstep (se 1 (by rfl) ⟨336491, by rfl⟩ : syracuseStep 448655 = 672983) B672983
theorem B1136825 : Blo 447780 1136825 := bstep (se 2 (by rfl) ⟨426309, by rfl⟩ : syracuseStep 1136825 = 852619) B852619
theorem B448699 : Blo 447780 448699 := bstep (se 1 (by rfl) ⟨336524, by rfl⟩ : syracuseStep 448699 = 673049) B673049
theorem B2283713 : Blo 447780 2283713 := bstep (se 2 (by rfl) ⟨856392, by rfl⟩ : syracuseStep 2283713 = 1712785) B1712785
theorem B448775 : Blo 447780 448775 := bstep (se 1 (by rfl) ⟨336581, by rfl⟩ : syracuseStep 448775 = 673163) B673163
theorem B448783 : Blo 447780 448783 := bstep (se 1 (by rfl) ⟨336587, by rfl⟩ : syracuseStep 448783 = 673175) B673175
theorem B448827 : Blo 447780 448827 := bstep (se 1 (by rfl) ⟨336620, by rfl⟩ : syracuseStep 448827 = 673241) B673241
theorem B5757277 : Blo 447780 5757277 := bstep (se 3 (by rfl) ⟨1079489, by rfl⟩ : syracuseStep 5757277 = 2158979) B2158979
theorem B448903 : Blo 447780 448903 := bstep (se 1 (by rfl) ⟨336677, by rfl⟩ : syracuseStep 448903 = 673355) B673355
theorem B448911 : Blo 447780 448911 := bstep (se 1 (by rfl) ⟨336683, by rfl⟩ : syracuseStep 448911 = 673367) B673367
theorem B448955 : Blo 447780 448955 := bstep (se 1 (by rfl) ⟨336716, by rfl⟩ : syracuseStep 448955 = 673433) B673433
theorem B449031 : Blo 447780 449031 := bstep (se 1 (by rfl) ⟨336773, by rfl⟩ : syracuseStep 449031 = 673547) B673547
theorem B449039 : Blo 447780 449039 := bstep (se 1 (by rfl) ⟨336779, by rfl⟩ : syracuseStep 449039 = 673559) B673559
theorem B3070493 : Blo 447780 3070493 := bstep (se 3 (by rfl) ⟨575717, by rfl⟩ : syracuseStep 3070493 = 1151435) B1151435
theorem B449083 : Blo 447780 449083 := bstep (se 1 (by rfl) ⟨336812, by rfl⟩ : syracuseStep 449083 = 673625) B673625
theorem B449159 : Blo 447780 449159 := bstep (se 1 (by rfl) ⟨336869, by rfl⟩ : syracuseStep 449159 = 673739) B673739
theorem B449167 : Blo 447780 449167 := bstep (se 1 (by rfl) ⟨336875, by rfl⟩ : syracuseStep 449167 = 673751) B673751
theorem B449211 : Blo 447780 449211 := bstep (se 1 (by rfl) ⟨336908, by rfl⟩ : syracuseStep 449211 = 673817) B673817
theorem B449287 : Blo 447780 449287 := bstep (se 1 (by rfl) ⟨336965, by rfl⟩ : syracuseStep 449287 = 673931) B673931
theorem B449295 : Blo 447780 449295 := bstep (se 1 (by rfl) ⟨336971, by rfl⟩ : syracuseStep 449295 = 673943) B673943
theorem B449339 : Blo 447780 449339 := bstep (se 1 (by rfl) ⟨337004, by rfl⟩ : syracuseStep 449339 = 674009) B674009
theorem B1137523 : Blo 447780 1137523 := bstep (se 1 (by rfl) ⟨853142, by rfl⟩ : syracuseStep 1137523 = 1706285) B1706285
theorem B449415 : Blo 447780 449415 := bstep (se 1 (by rfl) ⟨337061, by rfl⟩ : syracuseStep 449415 = 674123) B674123
theorem B449423 : Blo 447780 449423 := bstep (se 1 (by rfl) ⟨337067, by rfl⟩ : syracuseStep 449423 = 674135) B674135
theorem B449467 : Blo 447780 449467 := bstep (se 1 (by rfl) ⟨337100, by rfl⟩ : syracuseStep 449467 = 674201) B674201
theorem B1137665 : Blo 447780 1137665 := bstep (se 2 (by rfl) ⟨426624, by rfl⟩ : syracuseStep 1137665 = 853249) B853249
theorem B449543 : Blo 447780 449543 := bstep (se 1 (by rfl) ⟨337157, by rfl⟩ : syracuseStep 449543 = 674315) B674315
theorem B482311 : Blo 447780 482311 := bstep (se 1 (by rfl) ⟨361733, by rfl⟩ : syracuseStep 482311 = 723467) B723467
theorem B449551 : Blo 447780 449551 := bstep (se 1 (by rfl) ⟨337163, by rfl⟩ : syracuseStep 449551 = 674327) B674327
theorem B449595 : Blo 447780 449595 := bstep (se 1 (by rfl) ⟨337196, by rfl⟩ : syracuseStep 449595 = 674393) B674393
theorem B2743357 : Blo 447780 2743357 := bstep (se 3 (by rfl) ⟨514379, by rfl⟩ : syracuseStep 2743357 = 1028759) B1028759
theorem B449671 : Blo 447780 449671 := bstep (se 1 (by rfl) ⟨337253, by rfl⟩ : syracuseStep 449671 = 674507) B674507
theorem B449679 : Blo 447780 449679 := bstep (se 1 (by rfl) ⟨337259, by rfl⟩ : syracuseStep 449679 = 674519) B674519
theorem B449723 : Blo 447780 449723 := bstep (se 1 (by rfl) ⟨337292, by rfl⟩ : syracuseStep 449723 = 674585) B674585
theorem B449799 : Blo 447780 449799 := bstep (se 1 (by rfl) ⟨337349, by rfl⟩ : syracuseStep 449799 = 674699) B674699
theorem B449807 : Blo 447780 449807 := bstep (se 1 (by rfl) ⟨337355, by rfl⟩ : syracuseStep 449807 = 674711) B674711
theorem B449851 : Blo 447780 449851 := bstep (se 1 (by rfl) ⟨337388, by rfl⟩ : syracuseStep 449851 = 674777) B674777
theorem B449927 : Blo 447780 449927 := bstep (se 1 (by rfl) ⟨337445, by rfl⟩ : syracuseStep 449927 = 674891) B674891
theorem B449935 : Blo 447780 449935 := bstep (se 1 (by rfl) ⟨337451, by rfl⟩ : syracuseStep 449935 = 674903) B674903
theorem B810425 : Blo 447780 810425 := bstep (se 2 (by rfl) ⟨303909, by rfl⟩ : syracuseStep 810425 = 607819) B607819
theorem B449979 : Blo 447780 449979 := bstep (se 1 (by rfl) ⟨337484, by rfl⟩ : syracuseStep 449979 = 674969) B674969
theorem B1138121 : Blo 447780 1138121 := bstep (se 2 (by rfl) ⟨426795, by rfl⟩ : syracuseStep 1138121 = 853591) B853591
theorem B2285009 : Blo 447780 2285009 := bstep (se 2 (by rfl) ⟨856878, by rfl⟩ : syracuseStep 2285009 = 1713757) B1713757
theorem B450055 : Blo 447780 450055 := bstep (se 1 (by rfl) ⟨337541, by rfl⟩ : syracuseStep 450055 = 675083) B675083
theorem B450063 : Blo 447780 450063 := bstep (se 1 (by rfl) ⟨337547, by rfl⟩ : syracuseStep 450063 = 675095) B675095
theorem B450107 : Blo 447780 450107 := bstep (se 1 (by rfl) ⟨337580, by rfl⟩ : syracuseStep 450107 = 675161) B675161
theorem B450183 : Blo 447780 450183 := bstep (se 1 (by rfl) ⟨337637, by rfl⟩ : syracuseStep 450183 = 675275) B675275
theorem B450191 : Blo 447780 450191 := bstep (se 1 (by rfl) ⟨337643, by rfl⟩ : syracuseStep 450191 = 675287) B675287
theorem B450235 : Blo 447780 450235 := bstep (se 1 (by rfl) ⟨337676, by rfl⟩ : syracuseStep 450235 = 675353) B675353
theorem B450311 : Blo 447780 450311 := bstep (se 1 (by rfl) ⟨337733, by rfl⟩ : syracuseStep 450311 = 675467) B675467
theorem B450319 : Blo 447780 450319 := bstep (se 1 (by rfl) ⟨337739, by rfl⟩ : syracuseStep 450319 = 675479) B675479
theorem B1138475 : Blo 447780 1138475 := bstep (se 1 (by rfl) ⟨853856, by rfl⟩ : syracuseStep 1138475 = 1707713) B1707713
theorem B450363 : Blo 447780 450363 := bstep (se 1 (by rfl) ⟨337772, by rfl⟩ : syracuseStep 450363 = 675545) B675545
theorem B450439 : Blo 447780 450439 := bstep (se 1 (by rfl) ⟨337829, by rfl⟩ : syracuseStep 450439 = 675659) B675659
theorem B450447 : Blo 447780 450447 := bstep (se 1 (by rfl) ⟨337835, by rfl⟩ : syracuseStep 450447 = 675671) B675671
theorem B450491 : Blo 447780 450491 := bstep (se 1 (by rfl) ⟨337868, by rfl⟩ : syracuseStep 450491 = 675737) B675737
theorem B450567 : Blo 447780 450567 := bstep (se 1 (by rfl) ⟨337925, by rfl⟩ : syracuseStep 450567 = 675851) B675851
theorem B450575 : Blo 447780 450575 := bstep (se 1 (by rfl) ⟨337931, by rfl⟩ : syracuseStep 450575 = 675863) B675863
theorem B1007675 : Blo 447780 1007675 := bstep (se 1 (by rfl) ⟨755756, by rfl⟩ : syracuseStep 1007675 = 1511513) B1511513
theorem B647227 : Blo 447780 647227 := bstep (se 1 (by rfl) ⟨485420, by rfl⟩ : syracuseStep 647227 = 970841) B970841
theorem B450619 : Blo 447780 450619 := bstep (se 1 (by rfl) ⟨337964, by rfl⟩ : syracuseStep 450619 = 675929) B675929
theorem B450695 : Blo 447780 450695 := bstep (se 1 (by rfl) ⟨338021, by rfl⟩ : syracuseStep 450695 = 676043) B676043
theorem B450703 : Blo 447780 450703 := bstep (se 1 (by rfl) ⟨338027, by rfl⟩ : syracuseStep 450703 = 676055) B676055
theorem B1007801 : Blo 447780 1007801 := bstep (se 2 (by rfl) ⟨377925, by rfl⟩ : syracuseStep 1007801 = 755851) B755851
theorem B450747 : Blo 447780 450747 := bstep (se 1 (by rfl) ⟨338060, by rfl⟩ : syracuseStep 450747 = 676121) B676121
theorem B1368265 : Blo 447780 1368265 := bstep (se 2 (by rfl) ⟨513099, by rfl⟩ : syracuseStep 1368265 = 1026199) B1026199
theorem B450823 : Blo 447780 450823 := bstep (se 1 (by rfl) ⟨338117, by rfl⟩ : syracuseStep 450823 = 676235) B676235
theorem B450831 : Blo 447780 450831 := bstep (se 1 (by rfl) ⟨338123, by rfl⟩ : syracuseStep 450831 = 676247) B676247
theorem B3825953 : Blo 447780 3825953 := bstep (se 2 (by rfl) ⟨1434732, by rfl⟩ : syracuseStep 3825953 = 2869465) B2869465
theorem B450875 : Blo 447780 450875 := bstep (se 1 (by rfl) ⟨338156, by rfl⟩ : syracuseStep 450875 = 676313) B676313
theorem B450951 : Blo 447780 450951 := bstep (se 1 (by rfl) ⟨338213, by rfl⟩ : syracuseStep 450951 = 676427) B676427
theorem B450959 : Blo 447780 450959 := bstep (se 1 (by rfl) ⟨338219, by rfl⟩ : syracuseStep 450959 = 676439) B676439
theorem B451003 : Blo 447780 451003 := bstep (se 1 (by rfl) ⟨338252, by rfl⟩ : syracuseStep 451003 = 676505) B676505
theorem B647687 : Blo 447780 647687 := bstep (se 1 (by rfl) ⟨485765, by rfl⟩ : syracuseStep 647687 = 971531) B971531
theorem B451079 : Blo 447780 451079 := bstep (se 1 (by rfl) ⟨338309, by rfl⟩ : syracuseStep 451079 = 676619) B676619
theorem B1008143 : Blo 447780 1008143 := bstep (se 1 (by rfl) ⟨756107, by rfl⟩ : syracuseStep 1008143 = 1512215) B1512215
theorem B451087 : Blo 447780 451087 := bstep (se 1 (by rfl) ⟨338315, by rfl⟩ : syracuseStep 451087 = 676631) B676631
theorem B1008161 : Blo 447780 1008161 := bstep (se 2 (by rfl) ⟨378060, by rfl⟩ : syracuseStep 1008161 = 756121) B756121
theorem B3236395 : Blo 447780 3236395 := bstep (se 1 (by rfl) ⟨2427296, by rfl⟩ : syracuseStep 3236395 = 4854593) B4854593
theorem B811579 : Blo 447780 811579 := bstep (se 1 (by rfl) ⟨608684, by rfl⟩ : syracuseStep 811579 = 1217369) B1217369
theorem B451131 : Blo 447780 451131 := bstep (se 1 (by rfl) ⟨338348, by rfl⟩ : syracuseStep 451131 = 676697) B676697
theorem B451207 : Blo 447780 451207 := bstep (se 1 (by rfl) ⟨338405, by rfl⟩ : syracuseStep 451207 = 676811) B676811
theorem B451215 : Blo 447780 451215 := bstep (se 1 (by rfl) ⟨338411, by rfl⟩ : syracuseStep 451215 = 676823) B676823
theorem B451259 : Blo 447780 451259 := bstep (se 1 (by rfl) ⟨338444, by rfl⟩ : syracuseStep 451259 = 676889) B676889
theorem B2745089 : Blo 447780 2745089 := bstep (se 2 (by rfl) ⟨1029408, by rfl⟩ : syracuseStep 2745089 = 2058817) B2058817
theorem B451335 : Blo 447780 451335 := bstep (se 1 (by rfl) ⟨338501, by rfl⟩ : syracuseStep 451335 = 677003) B677003
theorem B1139467 : Blo 447780 1139467 := bstep (se 1 (by rfl) ⟨854600, by rfl⟩ : syracuseStep 1139467 = 1709201) B1709201
theorem B451343 : Blo 447780 451343 := bstep (se 1 (by rfl) ⟨338507, by rfl⟩ : syracuseStep 451343 = 677015) B677015
theorem B451387 : Blo 447780 451387 := bstep (se 1 (by rfl) ⟨338540, by rfl⟩ : syracuseStep 451387 = 677081) B677081
theorem B1008503 : Blo 447780 1008503 := bstep (se 1 (by rfl) ⟨756377, by rfl⟩ : syracuseStep 1008503 = 1512755) B1512755
theorem B451463 : Blo 447780 451463 := bstep (se 1 (by rfl) ⟨338597, by rfl⟩ : syracuseStep 451463 = 677195) B677195
theorem B451471 : Blo 447780 451471 := bstep (se 1 (by rfl) ⟨338603, by rfl⟩ : syracuseStep 451471 = 677207) B677207
theorem B1139609 : Blo 447780 1139609 := bstep (se 2 (by rfl) ⟨427353, by rfl⟩ : syracuseStep 1139609 = 854707) B854707
theorem B451515 : Blo 447780 451515 := bstep (se 1 (by rfl) ⟨338636, by rfl⟩ : syracuseStep 451515 = 677273) B677273
theorem B451591 : Blo 447780 451591 := bstep (se 1 (by rfl) ⟨338693, by rfl⟩ : syracuseStep 451591 = 677387) B677387
theorem B680975 : Blo 447780 680975 := bstep (se 1 (by rfl) ⟨510731, by rfl⟩ : syracuseStep 680975 = 1021463) B1021463
theorem B451599 : Blo 447780 451599 := bstep (se 1 (by rfl) ⟨338699, by rfl⟩ : syracuseStep 451599 = 677399) B677399
theorem B4318231 : Blo 447780 4318231 := bstep (se 1 (by rfl) ⟨3238673, by rfl⟩ : syracuseStep 4318231 = 6477347) B6477347
theorem B1008683 : Blo 447780 1008683 := bstep (se 1 (by rfl) ⟨756512, by rfl⟩ : syracuseStep 1008683 = 1513025) B1513025
theorem B1303595 : Blo 447780 1303595 := bstep (se 1 (by rfl) ⟨977696, by rfl⟩ : syracuseStep 1303595 = 1955393) B1955393
theorem B1139771 : Blo 447780 1139771 := bstep (se 1 (by rfl) ⟨854828, by rfl⟩ : syracuseStep 1139771 = 1709657) B1709657
theorem B451643 : Blo 447780 451643 := bstep (se 1 (by rfl) ⟨338732, by rfl⟩ : syracuseStep 451643 = 677465) B677465
theorem B451719 : Blo 447780 451719 := bstep (se 1 (by rfl) ⟨338789, by rfl⟩ : syracuseStep 451719 = 677579) B677579
theorem B451727 : Blo 447780 451727 := bstep (se 1 (by rfl) ⟨338795, by rfl⟩ : syracuseStep 451727 = 677591) B677591
theorem B451771 : Blo 447780 451771 := bstep (se 1 (by rfl) ⟨338828, by rfl⟩ : syracuseStep 451771 = 677657) B677657
theorem B2188595 : Blo 447780 2188595 := bstep (se 1 (by rfl) ⟨1641446, by rfl⟩ : syracuseStep 2188595 = 3282893) B3282893
theorem B1009043 : Blo 447780 1009043 := bstep (se 1 (by rfl) ⟨756782, by rfl⟩ : syracuseStep 1009043 = 1513565) B1513565
theorem B1140115 : Blo 447780 1140115 := bstep (se 1 (by rfl) ⟨855086, by rfl⟩ : syracuseStep 1140115 = 1710173) B1710173
theorem B1009097 : Blo 447780 1009097 := bstep (se 2 (by rfl) ⟨378411, by rfl⟩ : syracuseStep 1009097 = 756823) B756823
theorem B6153731 : Blo 447780 6153731 := bstep (se 1 (by rfl) ⟨4615298, by rfl⟩ : syracuseStep 6153731 = 9230597) B9230597
theorem B2287115 : Blo 447780 2287115 := bstep (se 1 (by rfl) ⟨1715336, by rfl⟩ : syracuseStep 2287115 = 3430673) B3430673
theorem B1140257 : Blo 447780 1140257 := bstep (se 2 (by rfl) ⟨427596, by rfl⟩ : syracuseStep 1140257 = 855193) B855193
theorem B1009799 : Blo 447780 1009799 := bstep (se 1 (by rfl) ⟨757349, by rfl⟩ : syracuseStep 1009799 = 1514699) B1514699
theorem B1435963 : Blo 447780 1435963 := bstep (se 1 (by rfl) ⟨1076972, by rfl⟩ : syracuseStep 1435963 = 2153945) B2153945
theorem B1009979 : Blo 447780 1009979 := bstep (se 1 (by rfl) ⟨757484, by rfl⟩ : syracuseStep 1009979 = 1514969) B1514969
theorem B1010105 : Blo 447780 1010105 := bstep (se 2 (by rfl) ⟨378789, by rfl⟩ : syracuseStep 1010105 = 757579) B757579
theorem B1141249 : Blo 447780 1141249 := bstep (se 2 (by rfl) ⟨427968, by rfl⟩ : syracuseStep 1141249 = 855937) B855937
theorem B3828343 : Blo 447780 3828343 := bstep (se 1 (by rfl) ⟨2871257, by rfl⟩ : syracuseStep 3828343 = 5742515) B5742515
theorem B9693877 : Blo 447780 9693877 := bstep (se 5 (by rfl) ⟨454400, by rfl⟩ : syracuseStep 9693877 = 908801) B908801
theorem B813769 : Blo 447780 813769 := bstep (se 2 (by rfl) ⟨305163, by rfl⟩ : syracuseStep 813769 = 610327) B610327
theorem B1370891 : Blo 447780 1370891 := bstep (se 1 (by rfl) ⟨1028168, by rfl⟩ : syracuseStep 1370891 = 2056337) B2056337
theorem B1010447 : Blo 447780 1010447 := bstep (se 1 (by rfl) ⟨757835, by rfl⟩ : syracuseStep 1010447 = 1515671) B1515671
theorem B1436449 : Blo 447780 1436449 := bstep (se 2 (by rfl) ⟨538668, by rfl⟩ : syracuseStep 1436449 = 1077337) B1077337
theorem B1010465 : Blo 447780 1010465 := bstep (se 2 (by rfl) ⟨378924, by rfl⟩ : syracuseStep 1010465 = 757849) B757849
theorem B912313 : Blo 447780 912313 := bstep (se 2 (by rfl) ⟨342117, by rfl⟩ : syracuseStep 912313 = 684235) B684235
theorem B2878487 : Blo 447780 2878487 := bstep (se 1 (by rfl) ⟨2158865, by rfl⟩ : syracuseStep 2878487 = 4317731) B4317731
theorem B1141847 : Blo 447780 1141847 := bstep (se 1 (by rfl) ⟨856385, by rfl⟩ : syracuseStep 1141847 = 1712771) B1712771
theorem B1010807 : Blo 447780 1010807 := bstep (se 1 (by rfl) ⟨758105, by rfl⟩ : syracuseStep 1010807 = 1516211) B1516211
theorem B2190509 : Blo 447780 2190509 := bstep (se 3 (by rfl) ⟨410720, by rfl⟩ : syracuseStep 2190509 = 821441) B821441
theorem B2714797 : Blo 447780 2714797 := bstep (se 3 (by rfl) ⟨509024, by rfl⟩ : syracuseStep 2714797 = 1018049) B1018049
theorem B1010987 : Blo 447780 1010987 := bstep (se 1 (by rfl) ⟨758240, by rfl⟩ : syracuseStep 1010987 = 1516481) B1516481
theorem B1142059 : Blo 447780 1142059 := bstep (se 1 (by rfl) ⟨856544, by rfl⟩ : syracuseStep 1142059 = 1713089) B1713089
theorem B683407 : Blo 447780 683407 := bstep (se 1 (by rfl) ⟨512555, by rfl⟩ : syracuseStep 683407 = 1025111) B1025111
theorem B1076665 : Blo 447780 1076665 := bstep (se 2 (by rfl) ⟨403749, by rfl⟩ : syracuseStep 1076665 = 807499) B807499
theorem B1142201 : Blo 447780 1142201 := bstep (se 2 (by rfl) ⟨428325, by rfl⟩ : syracuseStep 1142201 = 856651) B856651
theorem B1011347 : Blo 447780 1011347 := bstep (se 1 (by rfl) ⟨758510, by rfl⟩ : syracuseStep 1011347 = 1517021) B1517021
theorem B3403457 : Blo 447780 3403457 := bstep (se 2 (by rfl) ⟨1276296, by rfl⟩ : syracuseStep 3403457 = 2552593) B2552593
theorem B1011401 : Blo 447780 1011401 := bstep (se 2 (by rfl) ⟨379275, by rfl⟩ : syracuseStep 1011401 = 758551) B758551
theorem B618283 : Blo 447780 618283 := bstep (se 1 (by rfl) ⟨463712, by rfl⟩ : syracuseStep 618283 = 927425) B927425
theorem B4616279 : Blo 447780 4616279 := bstep (se 1 (by rfl) ⟨3462209, by rfl⟩ : syracuseStep 4616279 = 6924419) B6924419
theorem B454843 : Blo 447780 454843 := bstep (se 1 (by rfl) ⟨341132, by rfl⟩ : syracuseStep 454843 = 682265) B682265
theorem B1012103 : Blo 447780 1012103 := bstep (se 1 (by rfl) ⟨759077, by rfl⟩ : syracuseStep 1012103 = 1518155) B1518155
theorem B1143193 : Blo 447780 1143193 := bstep (se 2 (by rfl) ⟨428697, by rfl⟩ : syracuseStep 1143193 = 857395) B857395
theorem B1077761 : Blo 447780 1077761 := bstep (se 2 (by rfl) ⟨404160, by rfl⟩ : syracuseStep 1077761 = 808321) B808321
theorem B1012283 : Blo 447780 1012283 := bstep (se 1 (by rfl) ⟨759212, by rfl⟩ : syracuseStep 1012283 = 1518425) B1518425
theorem B1143355 : Blo 447780 1143355 := bstep (se 1 (by rfl) ⟨857516, by rfl⟩ : syracuseStep 1143355 = 1715033) B1715033
theorem B1077895 : Blo 447780 1077895 := bstep (se 1 (by rfl) ⟨808421, by rfl⟩ : syracuseStep 1077895 = 1616843) B1616843
theorem B684715 : Blo 447780 684715 := bstep (se 1 (by rfl) ⟨513536, by rfl⟩ : syracuseStep 684715 = 1027073) B1027073
theorem B1012409 : Blo 447780 1012409 := bstep (se 2 (by rfl) ⟨379653, by rfl⟩ : syracuseStep 1012409 = 759307) B759307
theorem B1143497 : Blo 447780 1143497 := bstep (se 2 (by rfl) ⟨428811, by rfl⟩ : syracuseStep 1143497 = 857623) B857623
theorem B1078049 : Blo 447780 1078049 := bstep (se 2 (by rfl) ⟨404268, by rfl⟩ : syracuseStep 1078049 = 808537) B808537
theorem B914323 : Blo 447780 914323 := bstep (se 1 (by rfl) ⟨685742, by rfl⟩ : syracuseStep 914323 = 1371485) B1371485
theorem B1012751 : Blo 447780 1012751 := bstep (se 1 (by rfl) ⟨759563, by rfl⟩ : syracuseStep 1012751 = 1519127) B1519127
theorem B1012769 : Blo 447780 1012769 := bstep (se 2 (by rfl) ⟨379788, by rfl⟩ : syracuseStep 1012769 = 759577) B759577
theorem B1701121 : Blo 447780 1701121 := bstep (se 2 (by rfl) ⟨637920, by rfl⟩ : syracuseStep 1701121 = 1275841) B1275841
theorem B2585945 : Blo 447780 2585945 := bstep (se 2 (by rfl) ⟨969729, by rfl⟩ : syracuseStep 2585945 = 1939459) B1939459
theorem B1013111 : Blo 447780 1013111 := bstep (se 1 (by rfl) ⟨759833, by rfl⟩ : syracuseStep 1013111 = 1519667) B1519667
theorem B1734173 : Blo 447780 1734173 := bstep (se 3 (by rfl) ⟨325157, by rfl⟩ : syracuseStep 1734173 = 650315) B650315
theorem B718379 : Blo 447780 718379 := bstep (se 1 (by rfl) ⟨538784, by rfl⟩ : syracuseStep 718379 = 1077569) B1077569
theorem B1013291 : Blo 447780 1013291 := bstep (se 1 (by rfl) ⟨759968, by rfl⟩ : syracuseStep 1013291 = 1519937) B1519937
theorem B1275659 : Blo 447780 1275659 := bstep (se 1 (by rfl) ⟨956744, by rfl⟩ : syracuseStep 1275659 = 1913489) B1913489
theorem B5601061 : Blo 447780 5601061 := bstep (se 4 (by rfl) ⟨525099, by rfl⟩ : syracuseStep 5601061 = 1050199) B1050199
theorem B1013651 : Blo 447780 1013651 := bstep (se 1 (by rfl) ⟨760238, by rfl⟩ : syracuseStep 1013651 = 1520477) B1520477
theorem B5339033 : Blo 447780 5339033 := bstep (se 2 (by rfl) ⟨2002137, by rfl⟩ : syracuseStep 5339033 = 4004275) B4004275
theorem B1013705 : Blo 447780 1013705 := bstep (se 2 (by rfl) ⟨380139, by rfl⟩ : syracuseStep 1013705 = 760279) B760279
theorem B3242045 : Blo 447780 3242045 := bstep (se 3 (by rfl) ⟨607883, by rfl⟩ : syracuseStep 3242045 = 1215767) B1215767
theorem B850105 : Blo 447780 850105 := bstep (se 2 (by rfl) ⟨318789, by rfl⟩ : syracuseStep 850105 = 637579) B637579
theorem B73202069 : Blo 447780 73202069 := bstep (se 6 (by rfl) ⟨1715673, by rfl⟩ : syracuseStep 73202069 = 3431347) B3431347
theorem B1210967 : Blo 447780 1210967 := bstep (se 1 (by rfl) ⟨908225, by rfl⟩ : syracuseStep 1210967 = 1816451) B1816451
theorem B1014407 : Blo 447780 1014407 := bstep (se 1 (by rfl) ⟨760805, by rfl⟩ : syracuseStep 1014407 = 1521611) B1521611
theorem B1014587 : Blo 447780 1014587 := bstep (se 1 (by rfl) ⟨760940, by rfl⟩ : syracuseStep 1014587 = 1521881) B1521881
theorem B1014713 : Blo 447780 1014713 := bstep (se 2 (by rfl) ⟨380517, by rfl⟩ : syracuseStep 1014713 = 761035) B761035
theorem B3406859 : Blo 447780 3406859 := bstep (se 1 (by rfl) ⟨2555144, by rfl⟩ : syracuseStep 3406859 = 5110289) B5110289
theorem B1015055 : Blo 447780 1015055 := bstep (se 1 (by rfl) ⟨761291, by rfl⟩ : syracuseStep 1015055 = 1522583) B1522583
theorem B1015073 : Blo 447780 1015073 := bstep (se 2 (by rfl) ⟨380652, by rfl⟩ : syracuseStep 1015073 = 761305) B761305
theorem B1277299 : Blo 447780 1277299 := bstep (se 1 (by rfl) ⟨957974, by rfl⟩ : syracuseStep 1277299 = 1915949) B1915949
theorem B1277527 : Blo 447780 1277527 := bstep (se 1 (by rfl) ⟨958145, by rfl⟩ : syracuseStep 1277527 = 1916291) B1916291
theorem B1015415 : Blo 447780 1015415 := bstep (se 1 (by rfl) ⟨761561, by rfl⟩ : syracuseStep 1015415 = 1523123) B1523123
theorem B1015595 : Blo 447780 1015595 := bstep (se 1 (by rfl) ⟨761696, by rfl⟩ : syracuseStep 1015595 = 1523393) B1523393
theorem B13860659 : Blo 447780 13860659 := bstep (se 1 (by rfl) ⟨10395494, by rfl⟩ : syracuseStep 13860659 = 20790989) B20790989
theorem B2555783 : Blo 447780 2555783 := bstep (se 1 (by rfl) ⟨1916837, by rfl⟩ : syracuseStep 2555783 = 3833675) B3833675
theorem B851897 : Blo 447780 851897 := bstep (se 2 (by rfl) ⟨319461, by rfl⟩ : syracuseStep 851897 = 638923) B638923
theorem B1015865 : Blo 447780 1015865 := bstep (se 2 (by rfl) ⟨380949, by rfl⟩ : syracuseStep 1015865 = 761899) B761899
theorem B1441871 : Blo 447780 1441871 := bstep (se 1 (by rfl) ⟨1081403, by rfl⟩ : syracuseStep 1441871 = 2162807) B2162807
theorem B721295 : Blo 447780 721295 := bstep (se 1 (by rfl) ⟨540971, by rfl⟩ : syracuseStep 721295 = 1081943) B1081943
theorem B1016207 : Blo 447780 1016207 := bstep (se 1 (by rfl) ⟨762155, by rfl⟩ : syracuseStep 1016207 = 1524311) B1524311
theorem B1082105 : Blo 447780 1082105 := bstep (se 2 (by rfl) ⟨405789, by rfl⟩ : syracuseStep 1082105 = 811579) B811579
theorem B852923 : Blo 447780 852923 := bstep (se 1 (by rfl) ⟨639692, by rfl⟩ : syracuseStep 852923 = 1279385) B1279385
theorem B15205427 : Blo 447780 15205427 := bstep (se 1 (by rfl) ⟨11404070, by rfl⟩ : syracuseStep 15205427 = 22808141) B22808141
theorem B1541387 : Blo 447780 1541387 := bstep (se 1 (by rfl) ⟨1156040, by rfl⟩ : syracuseStep 1541387 = 2312081) B2312081
theorem B853355 : Blo 447780 853355 := bstep (se 1 (by rfl) ⟨640016, by rfl⟩ : syracuseStep 853355 = 1280033) B1280033
theorem B1443215 : Blo 447780 1443215 := bstep (se 1 (by rfl) ⟨1082411, by rfl⟩ : syracuseStep 1443215 = 2164823) B2164823
theorem B853409 : Blo 447780 853409 := bstep (se 2 (by rfl) ⟨320028, by rfl⟩ : syracuseStep 853409 = 640057) B640057
theorem B1705481 : Blo 447780 1705481 := bstep (se 2 (by rfl) ⟨639555, by rfl⟩ : syracuseStep 1705481 = 1279111) B1279111
theorem B755959 : Blo 447780 755959 := bstep (se 1 (by rfl) ⟨566969, by rfl⟩ : syracuseStep 755959 = 1133939) B1133939
theorem B756155 : Blo 447780 756155 := bstep (se 1 (by rfl) ⟨567116, by rfl⟩ : syracuseStep 756155 = 1134233) B1134233
theorem B4164077 : Blo 447780 4164077 := bstep (se 3 (by rfl) ⟨780764, by rfl⟩ : syracuseStep 4164077 = 1561529) B1561529
theorem B756263 : Blo 447780 756263 := bstep (se 1 (by rfl) ⟨567197, by rfl⟩ : syracuseStep 756263 = 1134395) B1134395
theorem B756553 : Blo 447780 756553 := bstep (se 2 (by rfl) ⟨283707, by rfl⟩ : syracuseStep 756553 = 567415) B567415
theorem B756587 : Blo 447780 756587 := bstep (se 1 (by rfl) ⟨567440, by rfl⟩ : syracuseStep 756587 = 1134881) B1134881
theorem B1706939 : Blo 447780 1706939 := bstep (se 1 (by rfl) ⟨1280204, by rfl⟩ : syracuseStep 1706939 = 2560409) B2560409
theorem B855049 : Blo 447780 855049 := bstep (se 2 (by rfl) ⟨320643, by rfl⟩ : syracuseStep 855049 = 641287) B641287
theorem B756985 : Blo 447780 756985 := bstep (se 2 (by rfl) ⟨283869, by rfl⟩ : syracuseStep 756985 = 567739) B567739
theorem B757255 : Blo 447780 757255 := bstep (se 1 (by rfl) ⟨567941, by rfl⟩ : syracuseStep 757255 = 1135883) B1135883
theorem B2887559 : Blo 447780 2887559 := bstep (se 1 (by rfl) ⟨2165669, by rfl⟩ : syracuseStep 2887559 = 4331339) B4331339
theorem B1216417 : Blo 447780 1216417 := bstep (se 2 (by rfl) ⟨456156, by rfl⟩ : syracuseStep 1216417 = 912313) B912313
theorem B855983 : Blo 447780 855983 := bstep (se 1 (by rfl) ⟨641987, by rfl⟩ : syracuseStep 855983 = 1283975) B1283975
theorem B1511351 : Blo 447780 1511351 := bstep (se 1 (by rfl) ⟨1133513, by rfl⟩ : syracuseStep 1511351 = 2267027) B2267027
theorem B757687 : Blo 447780 757687 := bstep (se 1 (by rfl) ⟨568265, by rfl⟩ : syracuseStep 757687 = 1136531) B1136531
theorem B757883 : Blo 447780 757883 := bstep (se 1 (by rfl) ⟨568412, by rfl⟩ : syracuseStep 757883 = 1136825) B1136825
theorem B2560157 : Blo 447780 2560157 := bstep (se 3 (by rfl) ⟨480029, by rfl⟩ : syracuseStep 2560157 = 960059) B960059
theorem B856507 : Blo 447780 856507 := bstep (se 1 (by rfl) ⟨642380, by rfl⟩ : syracuseStep 856507 = 1284761) B1284761
theorem B1511945 : Blo 447780 1511945 := bstep (se 2 (by rfl) ⟨566979, by rfl⟩ : syracuseStep 1511945 = 1133959) B1133959
theorem B758281 : Blo 447780 758281 := bstep (se 2 (by rfl) ⟨284355, by rfl⟩ : syracuseStep 758281 = 568711) B568711
theorem B758443 : Blo 447780 758443 := bstep (se 1 (by rfl) ⟨568832, by rfl⟩ : syracuseStep 758443 = 1137665) B1137665
theorem B1446599 : Blo 447780 1446599 := bstep (se 1 (by rfl) ⟨1084949, by rfl⟩ : syracuseStep 1446599 = 2169899) B2169899
theorem B3248849 : Blo 447780 3248849 := bstep (se 2 (by rfl) ⟨1218318, by rfl⟩ : syracuseStep 3248849 = 2436637) B2436637
theorem B3412691 : Blo 447780 3412691 := bstep (se 1 (by rfl) ⟨2559518, by rfl⟩ : syracuseStep 3412691 = 5119037) B5119037
theorem B2560841 : Blo 447780 2560841 := bstep (se 2 (by rfl) ⟨960315, by rfl⟩ : syracuseStep 2560841 = 1920631) B1920631
theorem B856993 : Blo 447780 856993 := bstep (se 2 (by rfl) ⟨321372, by rfl⟩ : syracuseStep 856993 = 642745) B642745
theorem B758747 : Blo 447780 758747 := bstep (se 1 (by rfl) ⟨569060, by rfl⟩ : syracuseStep 758747 = 1138121) B1138121
theorem B1709171 : Blo 447780 1709171 := bstep (se 1 (by rfl) ⟨1281878, by rfl⟩ : syracuseStep 1709171 = 2563757) B2563757
theorem B922823 : Blo 447780 922823 := bstep (se 1 (by rfl) ⟨692117, by rfl⟩ : syracuseStep 922823 = 1384235) B1384235
theorem B758983 : Blo 447780 758983 := bstep (se 1 (by rfl) ⟨569237, by rfl⟩ : syracuseStep 758983 = 1138475) B1138475
theorem B1512809 : Blo 447780 1512809 := bstep (se 2 (by rfl) ⟨567303, by rfl⟩ : syracuseStep 1512809 = 1134607) B1134607
theorem B759145 : Blo 447780 759145 := bstep (se 2 (by rfl) ⟨284679, by rfl⟩ : syracuseStep 759145 = 569359) B569359
theorem B1513403 : Blo 447780 1513403 := bstep (se 1 (by rfl) ⟨1135052, by rfl⟩ : syracuseStep 1513403 = 2270105) B2270105
theorem B759739 : Blo 447780 759739 := bstep (se 1 (by rfl) ⟨569804, by rfl⟩ : syracuseStep 759739 = 1139609) B1139609
theorem B759847 : Blo 447780 759847 := bstep (se 1 (by rfl) ⟨569885, by rfl⟩ : syracuseStep 759847 = 1139771) B1139771
theorem B6166817 : Blo 447780 6166817 := bstep (se 2 (by rfl) ⟨2312556, by rfl⟩ : syracuseStep 6166817 = 4625113) B4625113
theorem B4102487 : Blo 447780 4102487 := bstep (se 1 (by rfl) ⟨3076865, by rfl⟩ : syracuseStep 4102487 = 6153731) B6153731
theorem B760171 : Blo 447780 760171 := bstep (se 1 (by rfl) ⟨570128, by rfl⟩ : syracuseStep 760171 = 1140257) B1140257
theorem B25041287 : Blo 447780 25041287 := bstep (se 1 (by rfl) ⟨18780965, by rfl⟩ : syracuseStep 25041287 = 37561931) B37561931
theorem B1219097 : Blo 447780 1219097 := bstep (se 2 (by rfl) ⟨457161, by rfl⟩ : syracuseStep 1219097 = 914323) B914323
theorem B1710841 : Blo 447780 1710841 := bstep (se 2 (by rfl) ⟨641565, by rfl⟩ : syracuseStep 1710841 = 1283131) B1283131
theorem B4856759 : Blo 447780 4856759 := bstep (se 1 (by rfl) ⟨3642569, by rfl⟩ : syracuseStep 4856759 = 7285139) B7285139
theorem B2268161 : Blo 447780 2268161 := bstep (se 2 (by rfl) ⟨850560, by rfl⟩ : syracuseStep 2268161 = 1701121) B1701121
theorem B2563073 : Blo 447780 2563073 := bstep (se 2 (by rfl) ⟨961152, by rfl⟩ : syracuseStep 2563073 = 1922305) B1922305
theorem B2891123 : Blo 447780 2891123 := bstep (se 1 (by rfl) ⟨2168342, by rfl⟩ : syracuseStep 2891123 = 4336685) B4336685
theorem B761231 : Blo 447780 761231 := bstep (se 1 (by rfl) ⟨570923, by rfl⟩ : syracuseStep 761231 = 1141847) B1141847
theorem B3644837 : Blo 447780 3644837 := bstep (se 4 (by rfl) ⟨341703, by rfl⟩ : syracuseStep 3644837 = 683407) B683407
theorem B2891351 : Blo 447780 2891351 := bstep (se 1 (by rfl) ⟨2168513, by rfl⟩ : syracuseStep 2891351 = 4337027) B4337027
theorem B1515131 : Blo 447780 1515131 := bstep (se 1 (by rfl) ⟨1136348, by rfl⟩ : syracuseStep 1515131 = 2272697) B2272697
theorem B761467 : Blo 447780 761467 := bstep (se 1 (by rfl) ⟨571100, by rfl⟩ : syracuseStep 761467 = 1142201) B1142201
theorem B4857533 : Blo 447780 4857533 := bstep (se 3 (by rfl) ⟨910787, by rfl⟩ : syracuseStep 4857533 = 1821575) B1821575
theorem B59121413 : Blo 447780 59121413 := bstep (se 4 (by rfl) ⟨5542632, by rfl⟩ : syracuseStep 59121413 = 11085265) B11085265
theorem B1515293 : Blo 447780 1515293 := bstep (se 3 (by rfl) ⟨284117, by rfl⟩ : syracuseStep 1515293 = 568235) B568235
theorem B2268971 : Blo 447780 2268971 := bstep (se 1 (by rfl) ⟨1701728, by rfl⟩ : syracuseStep 2268971 = 3403457) B3403457
theorem B3416093 : Blo 447780 3416093 := bstep (se 3 (by rfl) ⟨640517, by rfl⟩ : syracuseStep 3416093 = 1281035) B1281035
theorem B2465849 : Blo 447780 2465849 := bstep (se 2 (by rfl) ⟨924693, by rfl⟩ : syracuseStep 2465849 = 1849387) B1849387
theorem B1712285 : Blo 447780 1712285 := bstep (se 3 (by rfl) ⟨321053, by rfl⟩ : syracuseStep 1712285 = 642107) B642107
theorem B1712299 : Blo 447780 1712299 := bstep (se 1 (by rfl) ⟨1284224, by rfl⟩ : syracuseStep 1712299 = 2568449) B2568449
theorem B3285353 : Blo 447780 3285353 := bstep (se 2 (by rfl) ⟨1232007, by rfl⟩ : syracuseStep 3285353 = 2464015) B2464015
theorem B7676369 : Blo 447780 7676369 := bstep (se 2 (by rfl) ⟨2878638, by rfl⟩ : syracuseStep 7676369 = 5757277) B5757277
theorem B1515995 : Blo 447780 1515995 := bstep (se 1 (by rfl) ⟨1136996, by rfl⟩ : syracuseStep 1515995 = 2273993) B2273993
theorem B1712603 : Blo 447780 1712603 := bstep (se 1 (by rfl) ⟨1284452, by rfl⟩ : syracuseStep 1712603 = 2568905) B2568905
theorem B762331 : Blo 447780 762331 := bstep (se 1 (by rfl) ⟨571748, by rfl⟩ : syracuseStep 762331 = 1143497) B1143497
theorem B1156115 : Blo 447780 1156115 := bstep (se 1 (by rfl) ⟨867086, by rfl⟩ : syracuseStep 1156115 = 1734173) B1734173
theorem B730151 : Blo 447780 730151 := bstep (se 1 (by rfl) ⟨547613, by rfl⟩ : syracuseStep 730151 = 1095227) B1095227
theorem B1516697 : Blo 447780 1516697 := bstep (se 2 (by rfl) ⟨568761, by rfl⟩ : syracuseStep 1516697 = 1137523) B1137523
theorem B48801379 : Blo 447780 48801379 := bstep (se 1 (by rfl) ⟨36601034, by rfl⟩ : syracuseStep 48801379 = 73202069) B73202069
theorem B5121953 : Blo 447780 5121953 := bstep (se 2 (by rfl) ⟨1920732, by rfl⟩ : syracuseStep 5121953 = 3841465) B3841465
theorem B2271239 : Blo 447780 2271239 := bstep (se 1 (by rfl) ⟨1703429, by rfl⟩ : syracuseStep 2271239 = 3406859) B3406859
theorem B12986405 : Blo 447780 12986405 := bstep (se 4 (by rfl) ⟨1217475, by rfl⟩ : syracuseStep 12986405 = 2434951) B2434951
theorem B1517885 : Blo 447780 1517885 := bstep (se 3 (by rfl) ⟨284603, by rfl⟩ : syracuseStep 1517885 = 569207) B569207
theorem B2271725 : Blo 447780 2271725 := bstep (se 3 (by rfl) ⟨425948, by rfl⟩ : syracuseStep 2271725 = 851897) B851897
theorem B862969 : Blo 447780 862969 := bstep (se 2 (by rfl) ⟨323613, by rfl⟩ : syracuseStep 862969 = 647227) B647227
theorem B1715201 : Blo 447780 1715201 := bstep (se 2 (by rfl) ⟨643200, by rfl⟩ : syracuseStep 1715201 = 1286401) B1286401
theorem B1715215 : Blo 447780 1715215 := bstep (se 1 (by rfl) ⟨1286411, by rfl⟩ : syracuseStep 1715215 = 2572823) B2572823
theorem B1518749 : Blo 447780 1518749 := bstep (se 3 (by rfl) ⟨284765, by rfl⟩ : syracuseStep 1518749 = 569531) B569531
theorem B2272535 : Blo 447780 2272535 := bstep (se 1 (by rfl) ⟨1704401, by rfl⟩ : syracuseStep 2272535 = 3408803) B3408803
theorem B2567447 : Blo 447780 2567447 := bstep (se 1 (by rfl) ⟨1925585, by rfl⟩ : syracuseStep 2567447 = 3851171) B3851171
theorem B1519289 : Blo 447780 1519289 := bstep (se 2 (by rfl) ⟨569733, by rfl⟩ : syracuseStep 1519289 = 1139467) B1139467
theorem B2994029 : Blo 447780 2994029 := bstep (se 3 (by rfl) ⟨561380, by rfl⟩ : syracuseStep 2994029 = 1122761) B1122761
theorem B569263 : Blo 447780 569263 := bstep (se 1 (by rfl) ⟨426947, by rfl⟩ : syracuseStep 569263 = 853895) B853895
theorem B503887 : Blo 447780 503887 := bstep (se 1 (by rfl) ⟨377915, by rfl⟩ : syracuseStep 503887 = 755831) B755831
theorem B766151 : Blo 447780 766151 := bstep (se 1 (by rfl) ⟨574613, by rfl⟩ : syracuseStep 766151 = 1149227) B1149227
theorem B1519883 : Blo 447780 1519883 := bstep (se 1 (by rfl) ⟨1139912, by rfl⟩ : syracuseStep 1519883 = 2279825) B2279825
theorem B3420467 : Blo 447780 3420467 := bstep (se 1 (by rfl) ⟨2565350, by rfl⟩ : syracuseStep 3420467 = 5130701) B5130701
theorem B504283 : Blo 447780 504283 := bstep (se 1 (by rfl) ⟨378212, by rfl⟩ : syracuseStep 504283 = 756425) B756425
theorem B1520153 : Blo 447780 1520153 := bstep (se 2 (by rfl) ⟨570057, by rfl⟩ : syracuseStep 1520153 = 1140115) B1140115
theorem B8630995 : Blo 447780 8630995 := bstep (se 1 (by rfl) ⟨6473246, by rfl⟩ : syracuseStep 8630995 = 12946493) B12946493
theorem B1618717 : Blo 447780 1618717 := bstep (se 3 (by rfl) ⟨303509, by rfl⟩ : syracuseStep 1618717 = 607019) B607019
theorem B2274155 : Blo 447780 2274155 := bstep (se 1 (by rfl) ⟨1705616, by rfl⟩ : syracuseStep 2274155 = 3411233) B3411233
theorem B2470763 : Blo 447780 2470763 := bstep (se 1 (by rfl) ⟨1853072, by rfl⟩ : syracuseStep 2470763 = 3706145) B3706145
theorem B504751 : Blo 447780 504751 := bstep (se 1 (by rfl) ⟨378563, by rfl⟩ : syracuseStep 504751 = 757127) B757127
theorem B570331 : Blo 447780 570331 := bstep (se 1 (by rfl) ⟨427748, by rfl⟩ : syracuseStep 570331 = 855497) B855497
theorem B2602063 : Blo 447780 2602063 := bstep (se 1 (by rfl) ⟨1951547, by rfl⟩ : syracuseStep 2602063 = 3903095) B3903095
theorem B505183 : Blo 447780 505183 := bstep (se 1 (by rfl) ⟨378887, by rfl⟩ : syracuseStep 505183 = 757775) B757775
theorem B2274803 : Blo 447780 2274803 := bstep (se 1 (by rfl) ⟨1706102, by rfl⟩ : syracuseStep 2274803 = 3412205) B3412205
theorem B1521287 : Blo 447780 1521287 := bstep (se 1 (by rfl) ⟨1140965, by rfl⟩ : syracuseStep 1521287 = 2281931) B2281931
theorem B1914515 : Blo 447780 1914515 := bstep (se 1 (by rfl) ⟨1435886, by rfl⟩ : syracuseStep 1914515 = 2871773) B2871773
theorem B1521341 : Blo 447780 1521341 := bstep (se 3 (by rfl) ⟨285251, by rfl⟩ : syracuseStep 1521341 = 570503) B570503
theorem B505543 : Blo 447780 505543 := bstep (se 1 (by rfl) ⟨379157, by rfl⟩ : syracuseStep 505543 = 758315) B758315
theorem B2471639 : Blo 447780 2471639 := bstep (se 1 (by rfl) ⟨1853729, by rfl⟩ : syracuseStep 2471639 = 3707459) B3707459
theorem B1914617 : Blo 447780 1914617 := bstep (se 2 (by rfl) ⟨717981, by rfl⟩ : syracuseStep 1914617 = 1435963) B1435963
theorem B1521503 : Blo 447780 1521503 := bstep (se 1 (by rfl) ⟨1141127, by rfl⟩ : syracuseStep 1521503 = 2282255) B2282255
theorem B1521665 : Blo 447780 1521665 := bstep (se 2 (by rfl) ⟨570624, by rfl⟩ : syracuseStep 1521665 = 1141249) B1141249
theorem B5453831 : Blo 447780 5453831 := bstep (se 1 (by rfl) ⟨4090373, by rfl⟩ : syracuseStep 5453831 = 8180747) B8180747
theorem B6895853 : Blo 447780 6895853 := bstep (se 3 (by rfl) ⟨1292972, by rfl⟩ : syracuseStep 6895853 = 2585945) B2585945
theorem B12925169 : Blo 447780 12925169 := bstep (se 2 (by rfl) ⟨4846938, by rfl⟩ : syracuseStep 12925169 = 9693877) B9693877
theorem B1915265 : Blo 447780 1915265 := bstep (se 2 (by rfl) ⟨718224, by rfl⟩ : syracuseStep 1915265 = 1436449) B1436449
theorem B506407 : Blo 447780 506407 := bstep (se 1 (by rfl) ⟨379805, by rfl⟩ : syracuseStep 506407 = 759611) B759611
theorem B2276099 : Blo 447780 2276099 := bstep (se 1 (by rfl) ⟨1707074, by rfl⟩ : syracuseStep 2276099 = 3414149) B3414149
theorem B1522475 : Blo 447780 1522475 := bstep (se 1 (by rfl) ⟨1141856, by rfl⟩ : syracuseStep 1522475 = 2283713) B2283713
theorem B3619729 : Blo 447780 3619729 := bstep (se 2 (by rfl) ⟨1357398, by rfl⟩ : syracuseStep 3619729 = 2714797) B2714797
theorem B2046995 : Blo 447780 2046995 := bstep (se 1 (by rfl) ⟨1535246, by rfl⟩ : syracuseStep 2046995 = 3070493) B3070493
theorem B1522745 : Blo 447780 1522745 := bstep (se 2 (by rfl) ⟨571029, by rfl⟩ : syracuseStep 1522745 = 1142059) B1142059
theorem B1523069 : Blo 447780 1523069 := bstep (se 3 (by rfl) ⟨285575, by rfl⟩ : syracuseStep 1523069 = 571151) B571151
theorem B1523339 : Blo 447780 1523339 := bstep (se 1 (by rfl) ⟨1142504, by rfl⟩ : syracuseStep 1523339 = 2285009) B2285009
theorem B1949507 : Blo 447780 1949507 := bstep (se 1 (by rfl) ⟨1462130, by rfl⟩ : syracuseStep 1949507 = 2924261) B2924261
theorem B671753 : Blo 447780 671753 := bstep (se 2 (by rfl) ⟨251907, by rfl⟩ : syracuseStep 671753 = 503815) B503815
theorem B671783 : Blo 447780 671783 := bstep (se 1 (by rfl) ⟨503837, by rfl⟩ : syracuseStep 671783 = 1007675) B1007675
theorem B671867 : Blo 447780 671867 := bstep (se 1 (by rfl) ⟨503900, by rfl⟩ : syracuseStep 671867 = 1007801) B1007801
theorem B508027 : Blo 447780 508027 := bstep (se 1 (by rfl) ⟨381020, by rfl⟩ : syracuseStep 508027 = 762041) B762041
theorem B671993 : Blo 447780 671993 := bstep (se 2 (by rfl) ⟨251997, by rfl⟩ : syracuseStep 671993 = 503995) B503995
theorem B606457 : Blo 447780 606457 := bstep (se 2 (by rfl) ⟨227421, by rfl⟩ : syracuseStep 606457 = 454843) B454843
theorem B2277719 : Blo 447780 2277719 := bstep (se 1 (by rfl) ⟨1708289, by rfl⟩ : syracuseStep 2277719 = 3416579) B3416579
theorem B672095 : Blo 447780 672095 := bstep (se 1 (by rfl) ⟨504071, by rfl⟩ : syracuseStep 672095 = 1008143) B1008143
theorem B672107 : Blo 447780 672107 := bstep (se 1 (by rfl) ⟨504080, by rfl⟩ : syracuseStep 672107 = 1008161) B1008161
theorem B1524257 : Blo 447780 1524257 := bstep (se 2 (by rfl) ⟨571596, by rfl⟩ : syracuseStep 1524257 = 1143193) B1143193
theorem B1622567 : Blo 447780 1622567 := bstep (se 1 (by rfl) ⟨1216925, by rfl⟩ : syracuseStep 1622567 = 2433851) B2433851
theorem B672335 : Blo 447780 672335 := bstep (se 1 (by rfl) ⟨504251, by rfl⟩ : syracuseStep 672335 = 1008503) B1008503
theorem B672455 : Blo 447780 672455 := bstep (se 1 (by rfl) ⟨504341, by rfl⟩ : syracuseStep 672455 = 1008683) B1008683
theorem B869063 : Blo 447780 869063 := bstep (se 1 (by rfl) ⟨651797, by rfl⟩ : syracuseStep 869063 = 1303595) B1303595
theorem B1524473 : Blo 447780 1524473 := bstep (se 2 (by rfl) ⟨571677, by rfl⟩ : syracuseStep 1524473 = 1143355) B1143355
theorem B672617 : Blo 447780 672617 := bstep (se 2 (by rfl) ⟨252231, by rfl⟩ : syracuseStep 672617 = 504463) B504463
theorem B1459063 : Blo 447780 1459063 := bstep (se 1 (by rfl) ⟨1094297, by rfl⟩ : syracuseStep 1459063 = 2188595) B2188595
theorem B672695 : Blo 447780 672695 := bstep (se 1 (by rfl) ⟨504521, by rfl⟩ : syracuseStep 672695 = 1009043) B1009043
theorem B672731 : Blo 447780 672731 := bstep (se 1 (by rfl) ⟨504548, by rfl⟩ : syracuseStep 672731 = 1009097) B1009097
theorem B771079 : Blo 447780 771079 := bstep (se 1 (by rfl) ⟨578309, by rfl⟩ : syracuseStep 771079 = 1156619) B1156619
theorem B1524743 : Blo 447780 1524743 := bstep (se 1 (by rfl) ⟨1143557, by rfl⟩ : syracuseStep 1524743 = 2287115) B2287115
theorem B3327095 : Blo 447780 3327095 := bstep (se 1 (by rfl) ⟨2495321, by rfl⟩ : syracuseStep 3327095 = 4990643) B4990643
theorem B673199 : Blo 447780 673199 := bstep (se 1 (by rfl) ⟨504899, by rfl⟩ : syracuseStep 673199 = 1009799) B1009799
theorem B673289 : Blo 447780 673289 := bstep (se 2 (by rfl) ⟨252483, by rfl⟩ : syracuseStep 673289 = 504967) B504967
theorem B673319 : Blo 447780 673319 := bstep (se 1 (by rfl) ⟨504989, by rfl⟩ : syracuseStep 673319 = 1009979) B1009979
theorem B673403 : Blo 447780 673403 := bstep (se 1 (by rfl) ⟨505052, by rfl⟩ : syracuseStep 673403 = 1010105) B1010105
theorem B673529 : Blo 447780 673529 := bstep (se 2 (by rfl) ⟨252573, by rfl⟩ : syracuseStep 673529 = 505147) B505147
theorem B673631 : Blo 447780 673631 := bstep (se 1 (by rfl) ⟨505223, by rfl⟩ : syracuseStep 673631 = 1010447) B1010447
theorem B673643 : Blo 447780 673643 := bstep (se 1 (by rfl) ⟨505232, by rfl⟩ : syracuseStep 673643 = 1010465) B1010465
theorem B1918991 : Blo 447780 1918991 := bstep (se 1 (by rfl) ⟨1439243, by rfl⟩ : syracuseStep 1918991 = 2878487) B2878487
theorem B673871 : Blo 447780 673871 := bstep (se 1 (by rfl) ⟨505403, by rfl⟩ : syracuseStep 673871 = 1010807) B1010807
theorem B1460339 : Blo 447780 1460339 := bstep (se 1 (by rfl) ⟨1095254, by rfl⟩ : syracuseStep 1460339 = 2190509) B2190509
theorem B673991 : Blo 447780 673991 := bstep (se 1 (by rfl) ⟨505493, by rfl⟩ : syracuseStep 673991 = 1010987) B1010987
theorem B674153 : Blo 447780 674153 := bstep (se 2 (by rfl) ⟨252807, by rfl⟩ : syracuseStep 674153 = 505615) B505615
theorem B5491097 : Blo 447780 5491097 := bstep (se 2 (by rfl) ⟨2059161, by rfl⟩ : syracuseStep 5491097 = 4118323) B4118323
theorem B674231 : Blo 447780 674231 := bstep (se 1 (by rfl) ⟨505673, by rfl⟩ : syracuseStep 674231 = 1011347) B1011347
theorem B674267 : Blo 447780 674267 := bstep (se 1 (by rfl) ⟨505700, by rfl⟩ : syracuseStep 674267 = 1011401) B1011401
theorem B1133473 : Blo 447780 1133473 := bstep (se 2 (by rfl) ⟨425052, by rfl⟩ : syracuseStep 1133473 = 850105) B850105
theorem B674735 : Blo 447780 674735 := bstep (se 1 (by rfl) ⟨506051, by rfl⟩ : syracuseStep 674735 = 1012103) B1012103
theorem B674825 : Blo 447780 674825 := bstep (se 2 (by rfl) ⟨253059, by rfl⟩ : syracuseStep 674825 = 506119) B506119
theorem B674855 : Blo 447780 674855 := bstep (se 1 (by rfl) ⟨506141, by rfl⟩ : syracuseStep 674855 = 1012283) B1012283
theorem B674939 : Blo 447780 674939 := bstep (se 1 (by rfl) ⟨506204, by rfl⟩ : syracuseStep 674939 = 1012409) B1012409
theorem B675065 : Blo 447780 675065 := bstep (se 2 (by rfl) ⟨253149, by rfl⟩ : syracuseStep 675065 = 506299) B506299
theorem B675167 : Blo 447780 675167 := bstep (se 1 (by rfl) ⟨506375, by rfl⟩ : syracuseStep 675167 = 1012751) B1012751
theorem B675179 : Blo 447780 675179 := bstep (se 1 (by rfl) ⟨506384, by rfl⟩ : syracuseStep 675179 = 1012769) B1012769
theorem B3427757 : Blo 447780 3427757 := bstep (se 3 (by rfl) ⟨642704, by rfl⟩ : syracuseStep 3427757 = 1285409) B1285409
theorem B2870747 : Blo 447780 2870747 := bstep (se 1 (by rfl) ⟨2153060, by rfl⟩ : syracuseStep 2870747 = 4306121) B4306121
theorem B1625609 : Blo 447780 1625609 := bstep (se 2 (by rfl) ⟨609603, by rfl⟩ : syracuseStep 1625609 = 1219207) B1219207
theorem B675407 : Blo 447780 675407 := bstep (se 1 (by rfl) ⟨506555, by rfl⟩ : syracuseStep 675407 = 1013111) B1013111
theorem B478919 : Blo 447780 478919 := bstep (se 1 (by rfl) ⟨359189, by rfl⟩ : syracuseStep 478919 = 718379) B718379
theorem B675527 : Blo 447780 675527 := bstep (se 1 (by rfl) ⟨506645, by rfl⟩ : syracuseStep 675527 = 1013291) B1013291
theorem B2281283 : Blo 447780 2281283 := bstep (se 1 (by rfl) ⟨1710962, by rfl⟩ : syracuseStep 2281283 = 3421925) B3421925
theorem B675689 : Blo 447780 675689 := bstep (se 2 (by rfl) ⟨253383, by rfl⟩ : syracuseStep 675689 = 506767) B506767
theorem B675767 : Blo 447780 675767 := bstep (se 1 (by rfl) ⟨506825, by rfl⟩ : syracuseStep 675767 = 1013651) B1013651
theorem B3559355 : Blo 447780 3559355 := bstep (se 1 (by rfl) ⟨2669516, by rfl⟩ : syracuseStep 3559355 = 5339033) B5339033
theorem B675803 : Blo 447780 675803 := bstep (se 1 (by rfl) ⟨506852, by rfl⟩ : syracuseStep 675803 = 1013705) B1013705
theorem B643081 : Blo 447780 643081 := bstep (se 2 (by rfl) ⟨241155, by rfl⟩ : syracuseStep 643081 = 482311) B482311
theorem B3657809 : Blo 447780 3657809 := bstep (se 2 (by rfl) ⟨1371678, by rfl⟩ : syracuseStep 3657809 = 2743357) B2743357
theorem B3297509 : Blo 447780 3297509 := bstep (se 4 (by rfl) ⟨309141, by rfl⟩ : syracuseStep 3297509 = 618283) B618283
theorem B807311 : Blo 447780 807311 := bstep (se 1 (by rfl) ⟨605483, by rfl⟩ : syracuseStep 807311 = 1210967) B1210967
theorem B676271 : Blo 447780 676271 := bstep (se 1 (by rfl) ⟨507203, by rfl⟩ : syracuseStep 676271 = 1014407) B1014407
theorem B1626605 : Blo 447780 1626605 := bstep (se 3 (by rfl) ⟨304988, by rfl⟩ : syracuseStep 1626605 = 609977) B609977
theorem B676361 : Blo 447780 676361 := bstep (se 2 (by rfl) ⟨253635, by rfl⟩ : syracuseStep 676361 = 507271) B507271
theorem B676391 : Blo 447780 676391 := bstep (se 1 (by rfl) ⟨507293, by rfl⟩ : syracuseStep 676391 = 1014587) B1014587
theorem B676475 : Blo 447780 676475 := bstep (se 1 (by rfl) ⟨507356, by rfl⟩ : syracuseStep 676475 = 1014713) B1014713
theorem B676601 : Blo 447780 676601 := bstep (se 2 (by rfl) ⟨253725, by rfl⟩ : syracuseStep 676601 = 507451) B507451
theorem B676703 : Blo 447780 676703 := bstep (se 1 (by rfl) ⟨507527, by rfl⟩ : syracuseStep 676703 = 1015055) B1015055
theorem B676715 : Blo 447780 676715 := bstep (se 1 (by rfl) ⟨507536, by rfl⟩ : syracuseStep 676715 = 1015073) B1015073
theorem B513103 : Blo 447780 513103 := bstep (se 1 (by rfl) ⟨384827, by rfl⟩ : syracuseStep 513103 = 769655) B769655
theorem B676943 : Blo 447780 676943 := bstep (se 1 (by rfl) ⟨507707, by rfl⟩ : syracuseStep 676943 = 1015415) B1015415
theorem B971947 : Blo 447780 971947 := bstep (se 1 (by rfl) ⟨728960, by rfl⟩ : syracuseStep 971947 = 1457921) B1457921
theorem B677063 : Blo 447780 677063 := bstep (se 1 (by rfl) ⟨507797, by rfl⟩ : syracuseStep 677063 = 1015595) B1015595
theorem B447783 : Blo 447780 447783 := bstep (se 1 (by rfl) ⟨335837, by rfl⟩ : syracuseStep 447783 = 671675) B671675
theorem B447823 : Blo 447780 447823 := bstep (se 1 (by rfl) ⟨335867, by rfl⟩ : syracuseStep 447823 = 671735) B671735
theorem B447839 : Blo 447780 447839 := bstep (se 1 (by rfl) ⟨335879, by rfl⟩ : syracuseStep 447839 = 671759) B671759
theorem B677225 : Blo 447780 677225 := bstep (se 2 (by rfl) ⟨253959, by rfl⟩ : syracuseStep 677225 = 507919) B507919
theorem B447867 : Blo 447780 447867 := bstep (se 1 (by rfl) ⟨335900, by rfl⟩ : syracuseStep 447867 = 671801) B671801
theorem B1136015 : Blo 447780 1136015 := bstep (se 1 (by rfl) ⟨852011, by rfl⟩ : syracuseStep 1136015 = 1704023) B1704023
theorem B447919 : Blo 447780 447919 := bstep (se 1 (by rfl) ⟨335939, by rfl⟩ : syracuseStep 447919 = 671879) B671879
theorem B677303 : Blo 447780 677303 := bstep (se 1 (by rfl) ⟨507977, by rfl⟩ : syracuseStep 677303 = 1015955) B1015955
theorem B447943 : Blo 447780 447943 := bstep (se 1 (by rfl) ⟨335957, by rfl⟩ : syracuseStep 447943 = 671915) B671915
theorem B447963 : Blo 447780 447963 := bstep (se 1 (by rfl) ⟨335972, by rfl⟩ : syracuseStep 447963 = 671945) B671945
theorem B677339 : Blo 447780 677339 := bstep (se 1 (by rfl) ⟨508004, by rfl⟩ : syracuseStep 677339 = 1016009) B1016009
theorem B448039 : Blo 447780 448039 := bstep (se 1 (by rfl) ⟨336029, by rfl⟩ : syracuseStep 448039 = 672059) B672059
theorem B448079 : Blo 447780 448079 := bstep (se 1 (by rfl) ⟨336059, by rfl⟩ : syracuseStep 448079 = 672119) B672119
theorem B448095 : Blo 447780 448095 := bstep (se 1 (by rfl) ⟨336071, by rfl⟩ : syracuseStep 448095 = 672143) B672143
theorem B1824353 : Blo 447780 1824353 := bstep (se 2 (by rfl) ⟨684132, by rfl⟩ : syracuseStep 1824353 = 1368265) B1368265
theorem B448123 : Blo 447780 448123 := bstep (se 1 (by rfl) ⟨336092, by rfl⟩ : syracuseStep 448123 = 672185) B672185
theorem B448175 : Blo 447780 448175 := bstep (se 1 (by rfl) ⟨336131, by rfl⟩ : syracuseStep 448175 = 672263) B672263
theorem B448199 : Blo 447780 448199 := bstep (se 1 (by rfl) ⟨336149, by rfl⟩ : syracuseStep 448199 = 672299) B672299
theorem B1136339 : Blo 447780 1136339 := bstep (se 1 (by rfl) ⟨852254, by rfl⟩ : syracuseStep 1136339 = 1704509) B1704509
theorem B2741975 : Blo 447780 2741975 := bstep (se 1 (by rfl) ⟨2056481, by rfl⟩ : syracuseStep 2741975 = 4112963) B4112963
theorem B448219 : Blo 447780 448219 := bstep (se 1 (by rfl) ⟨336164, by rfl⟩ : syracuseStep 448219 = 672329) B672329
theorem B448295 : Blo 447780 448295 := bstep (se 1 (by rfl) ⟨336221, by rfl⟩ : syracuseStep 448295 = 672443) B672443
theorem B3430187 : Blo 447780 3430187 := bstep (se 1 (by rfl) ⟨2572640, by rfl⟩ : syracuseStep 3430187 = 5145281) B5145281
theorem B448335 : Blo 447780 448335 := bstep (se 1 (by rfl) ⟨336251, by rfl⟩ : syracuseStep 448335 = 672503) B672503
theorem B448351 : Blo 447780 448351 := bstep (se 1 (by rfl) ⟨336263, by rfl⟩ : syracuseStep 448351 = 672527) B672527
theorem B448379 : Blo 447780 448379 := bstep (se 1 (by rfl) ⟨336284, by rfl⟩ : syracuseStep 448379 = 672569) B672569
theorem B448431 : Blo 447780 448431 := bstep (se 1 (by rfl) ⟨336323, by rfl⟩ : syracuseStep 448431 = 672647) B672647
theorem B448455 : Blo 447780 448455 := bstep (se 1 (by rfl) ⟨336341, by rfl⟩ : syracuseStep 448455 = 672683) B672683
theorem B448475 : Blo 447780 448475 := bstep (se 1 (by rfl) ⟨336356, by rfl⟩ : syracuseStep 448475 = 672713) B672713
theorem B448551 : Blo 447780 448551 := bstep (se 1 (by rfl) ⟨336413, by rfl⟩ : syracuseStep 448551 = 672827) B672827
theorem B4315193 : Blo 447780 4315193 := bstep (se 2 (by rfl) ⟨1618197, by rfl⟩ : syracuseStep 4315193 = 3236395) B3236395
theorem B448591 : Blo 447780 448591 := bstep (se 1 (by rfl) ⟨336443, by rfl⟩ : syracuseStep 448591 = 672887) B672887
theorem B448607 : Blo 447780 448607 := bstep (se 1 (by rfl) ⟨336455, by rfl⟩ : syracuseStep 448607 = 672911) B672911
theorem B448635 : Blo 447780 448635 := bstep (se 1 (by rfl) ⟨336476, by rfl⟩ : syracuseStep 448635 = 672953) B672953
theorem B448687 : Blo 447780 448687 := bstep (se 1 (by rfl) ⟨336515, by rfl⟩ : syracuseStep 448687 = 673031) B673031
theorem B448711 : Blo 447780 448711 := bstep (se 1 (by rfl) ⟨336533, by rfl⟩ : syracuseStep 448711 = 673067) B673067
theorem B448731 : Blo 447780 448731 := bstep (se 1 (by rfl) ⟨336548, by rfl⟩ : syracuseStep 448731 = 673097) B673097
theorem B448807 : Blo 447780 448807 := bstep (se 1 (by rfl) ⟨336605, by rfl⟩ : syracuseStep 448807 = 673211) B673211
theorem B3889457 : Blo 447780 3889457 := bstep (se 2 (by rfl) ⟨1458546, by rfl⟩ : syracuseStep 3889457 = 2917093) B2917093
theorem B448847 : Blo 447780 448847 := bstep (se 1 (by rfl) ⟨336635, by rfl⟩ : syracuseStep 448847 = 673271) B673271
theorem B448863 : Blo 447780 448863 := bstep (se 1 (by rfl) ⟨336647, by rfl⟩ : syracuseStep 448863 = 673295) B673295
theorem B448891 : Blo 447780 448891 := bstep (se 1 (by rfl) ⟨336668, by rfl⟩ : syracuseStep 448891 = 673337) B673337
theorem B24697223 : Blo 447780 24697223 := bstep (se 1 (by rfl) ⟨18522917, by rfl⟩ : syracuseStep 24697223 = 37045835) B37045835
theorem B448943 : Blo 447780 448943 := bstep (se 1 (by rfl) ⟨336707, by rfl⟩ : syracuseStep 448943 = 673415) B673415
theorem B448967 : Blo 447780 448967 := bstep (se 1 (by rfl) ⟨336725, by rfl⟩ : syracuseStep 448967 = 673451) B673451
theorem B448987 : Blo 447780 448987 := bstep (se 1 (by rfl) ⟨336740, by rfl⟩ : syracuseStep 448987 = 673481) B673481
theorem B449063 : Blo 447780 449063 := bstep (se 1 (by rfl) ⟨336797, by rfl⟩ : syracuseStep 449063 = 673595) B673595
theorem B449103 : Blo 447780 449103 := bstep (se 1 (by rfl) ⟨336827, by rfl⟩ : syracuseStep 449103 = 673655) B673655
theorem B449119 : Blo 447780 449119 := bstep (se 1 (by rfl) ⟨336839, by rfl⟩ : syracuseStep 449119 = 673679) B673679
theorem B449147 : Blo 447780 449147 := bstep (se 1 (by rfl) ⟨336860, by rfl⟩ : syracuseStep 449147 = 673721) B673721
theorem B449199 : Blo 447780 449199 := bstep (se 1 (by rfl) ⟨336899, by rfl⟩ : syracuseStep 449199 = 673799) B673799
theorem B1727165 : Blo 447780 1727165 := bstep (se 3 (by rfl) ⟨323843, by rfl⟩ : syracuseStep 1727165 = 647687) B647687
theorem B449223 : Blo 447780 449223 := bstep (se 1 (by rfl) ⟨336917, by rfl⟩ : syracuseStep 449223 = 673835) B673835
theorem B5757641 : Blo 447780 5757641 := bstep (se 2 (by rfl) ⟨2159115, by rfl⟩ : syracuseStep 5757641 = 4318231) B4318231
theorem B449243 : Blo 447780 449243 := bstep (se 1 (by rfl) ⟨336932, by rfl⟩ : syracuseStep 449243 = 673865) B673865
theorem B50420465 : Blo 447780 50420465 := bstep (se 2 (by rfl) ⟨18907674, by rfl⟩ : syracuseStep 50420465 = 37815349) B37815349
theorem B449319 : Blo 447780 449319 := bstep (se 1 (by rfl) ⟨336989, by rfl⟩ : syracuseStep 449319 = 673979) B673979
theorem B2284361 : Blo 447780 2284361 := bstep (se 2 (by rfl) ⟨856635, by rfl⟩ : syracuseStep 2284361 = 1713271) B1713271
theorem B449359 : Blo 447780 449359 := bstep (se 1 (by rfl) ⟨337019, by rfl⟩ : syracuseStep 449359 = 674039) B674039
theorem B449375 : Blo 447780 449375 := bstep (se 1 (by rfl) ⟨337031, by rfl⟩ : syracuseStep 449375 = 674063) B674063
theorem B1137503 : Blo 447780 1137503 := bstep (se 1 (by rfl) ⟨853127, by rfl⟩ : syracuseStep 1137503 = 1706255) B1706255
theorem B449403 : Blo 447780 449403 := bstep (se 1 (by rfl) ⟨337052, by rfl⟩ : syracuseStep 449403 = 674105) B674105
theorem B449455 : Blo 447780 449455 := bstep (se 1 (by rfl) ⟨337091, by rfl⟩ : syracuseStep 449455 = 674183) B674183
theorem B449479 : Blo 447780 449479 := bstep (se 1 (by rfl) ⟨337109, by rfl⟩ : syracuseStep 449479 = 674219) B674219
theorem B449499 : Blo 447780 449499 := bstep (se 1 (by rfl) ⟨337124, by rfl⟩ : syracuseStep 449499 = 674249) B674249
theorem B449575 : Blo 447780 449575 := bstep (se 1 (by rfl) ⟨337181, by rfl⟩ : syracuseStep 449575 = 674363) B674363
theorem B449615 : Blo 447780 449615 := bstep (se 1 (by rfl) ⟨337211, by rfl⟩ : syracuseStep 449615 = 674423) B674423
theorem B449631 : Blo 447780 449631 := bstep (se 1 (by rfl) ⟨337223, by rfl⟩ : syracuseStep 449631 = 674447) B674447
theorem B449659 : Blo 447780 449659 := bstep (se 1 (by rfl) ⟨337244, by rfl⟩ : syracuseStep 449659 = 674489) B674489
theorem B449711 : Blo 447780 449711 := bstep (se 1 (by rfl) ⟨337283, by rfl⟩ : syracuseStep 449711 = 674567) B674567
theorem B449735 : Blo 447780 449735 := bstep (se 1 (by rfl) ⟨337301, by rfl⟩ : syracuseStep 449735 = 674603) B674603
theorem B449755 : Blo 447780 449755 := bstep (se 1 (by rfl) ⟨337316, by rfl⟩ : syracuseStep 449755 = 674633) B674633
theorem B449831 : Blo 447780 449831 := bstep (se 1 (by rfl) ⟨337373, by rfl⟩ : syracuseStep 449831 = 674747) B674747
theorem B449871 : Blo 447780 449871 := bstep (se 1 (by rfl) ⟨337403, by rfl⟩ : syracuseStep 449871 = 674807) B674807
theorem B449887 : Blo 447780 449887 := bstep (se 1 (by rfl) ⟨337415, by rfl⟩ : syracuseStep 449887 = 674831) B674831
theorem B449915 : Blo 447780 449915 := bstep (se 1 (by rfl) ⟨337436, by rfl⟩ : syracuseStep 449915 = 674873) B674873
theorem B2874797 : Blo 447780 2874797 := bstep (se 3 (by rfl) ⟨539024, by rfl⟩ : syracuseStep 2874797 = 1078049) B1078049
theorem B449967 : Blo 447780 449967 := bstep (se 1 (by rfl) ⟨337475, by rfl⟩ : syracuseStep 449967 = 674951) B674951
theorem B449991 : Blo 447780 449991 := bstep (se 1 (by rfl) ⟨337493, by rfl⟩ : syracuseStep 449991 = 674987) B674987
theorem B450011 : Blo 447780 450011 := bstep (se 1 (by rfl) ⟨337508, by rfl⟩ : syracuseStep 450011 = 675017) B675017
theorem B450087 : Blo 447780 450087 := bstep (se 1 (by rfl) ⟨337565, by rfl⟩ : syracuseStep 450087 = 675131) B675131
theorem B1170983 : Blo 447780 1170983 := bstep (se 1 (by rfl) ⟨878237, by rfl⟩ : syracuseStep 1170983 = 1756475) B1756475
theorem B450127 : Blo 447780 450127 := bstep (se 1 (by rfl) ⟨337595, by rfl⟩ : syracuseStep 450127 = 675191) B675191
theorem B450143 : Blo 447780 450143 := bstep (se 1 (by rfl) ⟨337607, by rfl⟩ : syracuseStep 450143 = 675215) B675215
theorem B450171 : Blo 447780 450171 := bstep (se 1 (by rfl) ⟨337628, by rfl⟩ : syracuseStep 450171 = 675257) B675257
theorem B450223 : Blo 447780 450223 := bstep (se 1 (by rfl) ⟨337667, by rfl⟩ : syracuseStep 450223 = 675335) B675335
theorem B450247 : Blo 447780 450247 := bstep (se 1 (by rfl) ⟨337685, by rfl⟩ : syracuseStep 450247 = 675371) B675371
theorem B450267 : Blo 447780 450267 := bstep (se 1 (by rfl) ⟨337700, by rfl⟩ : syracuseStep 450267 = 675401) B675401
theorem B450343 : Blo 447780 450343 := bstep (se 1 (by rfl) ⟨337757, by rfl⟩ : syracuseStep 450343 = 675515) B675515
theorem B1236809 : Blo 447780 1236809 := bstep (se 2 (by rfl) ⟨463803, by rfl⟩ : syracuseStep 1236809 = 927607) B927607
theorem B450383 : Blo 447780 450383 := bstep (se 1 (by rfl) ⟨337787, by rfl⟩ : syracuseStep 450383 = 675575) B675575
theorem B450399 : Blo 447780 450399 := bstep (se 1 (by rfl) ⟨337799, by rfl⟩ : syracuseStep 450399 = 675599) B675599
theorem B450427 : Blo 447780 450427 := bstep (se 1 (by rfl) ⟨337820, by rfl⟩ : syracuseStep 450427 = 675641) B675641
theorem B1138607 : Blo 447780 1138607 := bstep (se 1 (by rfl) ⟨853955, by rfl⟩ : syracuseStep 1138607 = 1707911) B1707911
theorem B450479 : Blo 447780 450479 := bstep (se 1 (by rfl) ⟨337859, by rfl⟩ : syracuseStep 450479 = 675719) B675719
theorem B450503 : Blo 447780 450503 := bstep (se 1 (by rfl) ⟨337877, by rfl⟩ : syracuseStep 450503 = 675755) B675755
theorem B450523 : Blo 447780 450523 := bstep (se 1 (by rfl) ⟨337892, by rfl⟩ : syracuseStep 450523 = 675785) B675785
theorem B450599 : Blo 447780 450599 := bstep (se 1 (by rfl) ⟨337949, by rfl⟩ : syracuseStep 450599 = 675899) B675899
theorem B450639 : Blo 447780 450639 := bstep (se 1 (by rfl) ⟨337979, by rfl⟩ : syracuseStep 450639 = 675959) B675959
theorem B2285657 : Blo 447780 2285657 := bstep (se 2 (by rfl) ⟨857121, by rfl⟩ : syracuseStep 2285657 = 1714243) B1714243
theorem B450655 : Blo 447780 450655 := bstep (se 1 (by rfl) ⟨337991, by rfl⟩ : syracuseStep 450655 = 675983) B675983
theorem B450683 : Blo 447780 450683 := bstep (se 1 (by rfl) ⟨338012, by rfl⟩ : syracuseStep 450683 = 676025) B676025
theorem B450735 : Blo 447780 450735 := bstep (se 1 (by rfl) ⟨338051, by rfl⟩ : syracuseStep 450735 = 676103) B676103
theorem B450759 : Blo 447780 450759 := bstep (se 1 (by rfl) ⟨338069, by rfl⟩ : syracuseStep 450759 = 676139) B676139
theorem B450779 : Blo 447780 450779 := bstep (se 1 (by rfl) ⟨338084, by rfl⟩ : syracuseStep 450779 = 676169) B676169
theorem B450855 : Blo 447780 450855 := bstep (se 1 (by rfl) ⟨338141, by rfl⟩ : syracuseStep 450855 = 676283) B676283
theorem B450895 : Blo 447780 450895 := bstep (se 1 (by rfl) ⟨338171, by rfl⟩ : syracuseStep 450895 = 676343) B676343
theorem B450911 : Blo 447780 450911 := bstep (se 1 (by rfl) ⟨338183, by rfl⟩ : syracuseStep 450911 = 676367) B676367
theorem B12312931 : Blo 447780 12312931 := bstep (se 1 (by rfl) ⟨9234698, by rfl⟩ : syracuseStep 12312931 = 18469397) B18469397
theorem B450939 : Blo 447780 450939 := bstep (se 1 (by rfl) ⟨338204, by rfl⟩ : syracuseStep 450939 = 676409) B676409
theorem B450991 : Blo 447780 450991 := bstep (se 1 (by rfl) ⟨338243, by rfl⟩ : syracuseStep 450991 = 676487) B676487
theorem B451015 : Blo 447780 451015 := bstep (se 1 (by rfl) ⟨338261, by rfl⟩ : syracuseStep 451015 = 676523) B676523
theorem B451035 : Blo 447780 451035 := bstep (se 1 (by rfl) ⟨338276, by rfl⟩ : syracuseStep 451035 = 676553) B676553
theorem B451111 : Blo 447780 451111 := bstep (se 1 (by rfl) ⟨338333, by rfl⟩ : syracuseStep 451111 = 676667) B676667
theorem B451151 : Blo 447780 451151 := bstep (se 1 (by rfl) ⟨338363, by rfl⟩ : syracuseStep 451151 = 676727) B676727
theorem B451167 : Blo 447780 451167 := bstep (se 1 (by rfl) ⟨338375, by rfl⟩ : syracuseStep 451167 = 676751) B676751
theorem B1008251 : Blo 447780 1008251 := bstep (se 1 (by rfl) ⟨756188, by rfl⟩ : syracuseStep 1008251 = 1512377) B1512377
theorem B451195 : Blo 447780 451195 := bstep (se 1 (by rfl) ⟨338396, by rfl⟩ : syracuseStep 451195 = 676793) B676793
theorem B1827467 : Blo 447780 1827467 := bstep (se 1 (by rfl) ⟨1370600, by rfl⟩ : syracuseStep 1827467 = 2741201) B2741201
theorem B451247 : Blo 447780 451247 := bstep (se 1 (by rfl) ⟨338435, by rfl⟩ : syracuseStep 451247 = 676871) B676871
theorem B451271 : Blo 447780 451271 := bstep (se 1 (by rfl) ⟨338453, by rfl⟩ : syracuseStep 451271 = 676907) B676907
theorem B451291 : Blo 447780 451291 := bstep (se 1 (by rfl) ⟨338468, by rfl⟩ : syracuseStep 451291 = 676937) B676937
theorem B1008377 : Blo 447780 1008377 := bstep (se 2 (by rfl) ⟨378141, by rfl⟩ : syracuseStep 1008377 = 756283) B756283
theorem B451367 : Blo 447780 451367 := bstep (se 1 (by rfl) ⟨338525, by rfl⟩ : syracuseStep 451367 = 677051) B677051
theorem B5104457 : Blo 447780 5104457 := bstep (se 2 (by rfl) ⟨1914171, by rfl⟩ : syracuseStep 5104457 = 3828343) B3828343
theorem B451407 : Blo 447780 451407 := bstep (se 1 (by rfl) ⟨338555, by rfl⟩ : syracuseStep 451407 = 677111) B677111
theorem B451423 : Blo 447780 451423 := bstep (se 1 (by rfl) ⟨338567, by rfl⟩ : syracuseStep 451423 = 677135) B677135
theorem B451451 : Blo 447780 451451 := bstep (se 1 (by rfl) ⟨338588, by rfl⟩ : syracuseStep 451451 = 677177) B677177
theorem B811919 : Blo 447780 811919 := bstep (se 1 (by rfl) ⟨608939, by rfl⟩ : syracuseStep 811919 = 1217879) B1217879
theorem B451503 : Blo 447780 451503 := bstep (se 1 (by rfl) ⟨338627, by rfl⟩ : syracuseStep 451503 = 677255) B677255
theorem B451527 : Blo 447780 451527 := bstep (se 1 (by rfl) ⟨338645, by rfl⟩ : syracuseStep 451527 = 677291) B677291
theorem B451547 : Blo 447780 451547 := bstep (se 1 (by rfl) ⟨338660, by rfl⟩ : syracuseStep 451547 = 677321) B677321
theorem B1434631 : Blo 447780 1434631 := bstep (se 1 (by rfl) ⟨1075973, by rfl⟩ : syracuseStep 1434631 = 2151947) B2151947
theorem B1008647 : Blo 447780 1008647 := bstep (se 1 (by rfl) ⟨756485, by rfl⟩ : syracuseStep 1008647 = 1512971) B1512971
theorem B451623 : Blo 447780 451623 := bstep (se 1 (by rfl) ⟨338717, by rfl⟩ : syracuseStep 451623 = 677435) B677435
theorem B1008719 : Blo 447780 1008719 := bstep (se 1 (by rfl) ⟨756539, by rfl⟩ : syracuseStep 1008719 = 1513079) B1513079
theorem B1139791 : Blo 447780 1139791 := bstep (se 1 (by rfl) ⟨854843, by rfl⟩ : syracuseStep 1139791 = 1709687) B1709687
theorem B451663 : Blo 447780 451663 := bstep (se 1 (by rfl) ⟨338747, by rfl⟩ : syracuseStep 451663 = 677495) B677495
theorem B451679 : Blo 447780 451679 := bstep (se 1 (by rfl) ⟨338759, by rfl⟩ : syracuseStep 451679 = 677519) B677519
theorem B2909303 : Blo 447780 2909303 := bstep (se 1 (by rfl) ⟨2181977, by rfl⟩ : syracuseStep 2909303 = 4363955) B4363955
theorem B812155 : Blo 447780 812155 := bstep (se 1 (by rfl) ⟨609116, by rfl⟩ : syracuseStep 812155 = 1218233) B1218233
theorem B451707 : Blo 447780 451707 := bstep (se 1 (by rfl) ⟨338780, by rfl⟩ : syracuseStep 451707 = 677561) B677561
theorem B451759 : Blo 447780 451759 := bstep (se 1 (by rfl) ⟨338819, by rfl⟩ : syracuseStep 451759 = 677639) B677639
theorem B12445093 : Blo 447780 12445093 := bstep (se 4 (by rfl) ⟨1166727, by rfl⟩ : syracuseStep 12445093 = 2333455) B2333455
theorem B1009115 : Blo 447780 1009115 := bstep (se 1 (by rfl) ⟨756836, by rfl⟩ : syracuseStep 1009115 = 1513673) B1513673
theorem B17360405 : Blo 447780 17360405 := bstep (se 6 (by rfl) ⟨406884, by rfl⟩ : syracuseStep 17360405 = 813769) B813769
theorem B1140439 : Blo 447780 1140439 := bstep (se 1 (by rfl) ⟨855329, by rfl⟩ : syracuseStep 1140439 = 1710659) B1710659
theorem B1435553 : Blo 447780 1435553 := bstep (se 2 (by rfl) ⟨538332, by rfl⟩ : syracuseStep 1435553 = 1076665) B1076665
theorem B1009583 : Blo 447780 1009583 := bstep (se 1 (by rfl) ⟨757187, by rfl⟩ : syracuseStep 1009583 = 1514375) B1514375
theorem B1140743 : Blo 447780 1140743 := bstep (se 1 (by rfl) ⟨855557, by rfl⟩ : syracuseStep 1140743 = 1711115) B1711115
theorem B1009835 : Blo 447780 1009835 := bstep (se 1 (by rfl) ⟨757376, by rfl⟩ : syracuseStep 1009835 = 1514753) B1514753
theorem B1927739 : Blo 447780 1927739 := bstep (se 1 (by rfl) ⟨1445804, by rfl⟩ : syracuseStep 1927739 = 2891609) B2891609
theorem B1010375 : Blo 447780 1010375 := bstep (se 1 (by rfl) ⟨757781, by rfl⟩ : syracuseStep 1010375 = 1515563) B1515563
theorem B8645453 : Blo 447780 8645453 := bstep (se 3 (by rfl) ⟨1621022, by rfl⟩ : syracuseStep 8645453 = 3242045) B3242045
theorem B2550635 : Blo 447780 2550635 := bstep (se 1 (by rfl) ⟨1912976, by rfl⟩ : syracuseStep 2550635 = 3825953) B3825953
theorem B1830059 : Blo 447780 1830059 := bstep (se 1 (by rfl) ⟨1372544, by rfl⟩ : syracuseStep 1830059 = 2745089) B2745089
theorem B1928387 : Blo 447780 1928387 := bstep (se 1 (by rfl) ⟨1446290, by rfl⟩ : syracuseStep 1928387 = 2892581) B2892581
theorem B4877603 : Blo 447780 4877603 := bstep (se 1 (by rfl) ⟨3658202, by rfl⟩ : syracuseStep 4877603 = 7316405) B7316405
theorem B453983 : Blo 447780 453983 := bstep (se 1 (by rfl) ⟨340487, by rfl⟩ : syracuseStep 453983 = 680975) B680975
theorem B1437193 : Blo 447780 1437193 := bstep (se 2 (by rfl) ⟨538947, by rfl⟩ : syracuseStep 1437193 = 1077895) B1077895
theorem B1011239 : Blo 447780 1011239 := bstep (se 1 (by rfl) ⟨758429, by rfl⟩ : syracuseStep 1011239 = 1516859) B1516859
theorem B912953 : Blo 447780 912953 := bstep (se 2 (by rfl) ⟨342357, by rfl⟩ : syracuseStep 912953 = 684715) B684715
theorem B4091681 : Blo 447780 4091681 := bstep (se 2 (by rfl) ⟨1534380, by rfl⟩ : syracuseStep 4091681 = 3068761) B3068761
theorem B10907459 : Blo 447780 10907459 := bstep (se 1 (by rfl) ⟨8180594, by rfl⟩ : syracuseStep 10907459 = 16361189) B16361189
theorem B1929055 : Blo 447780 1929055 := bstep (se 1 (by rfl) ⟨1446791, by rfl⟩ : syracuseStep 1929055 = 2893583) B2893583
theorem B1011563 : Blo 447780 1011563 := bstep (se 1 (by rfl) ⟨758672, by rfl⟩ : syracuseStep 1011563 = 1517345) B1517345
theorem B2551661 : Blo 447780 2551661 := bstep (se 3 (by rfl) ⟨478436, by rfl⟩ : syracuseStep 2551661 = 956873) B956873
theorem B1011617 : Blo 447780 1011617 := bstep (se 2 (by rfl) ⟨379356, by rfl⟩ : syracuseStep 1011617 = 758713) B758713
theorem B12283811 : Blo 447780 12283811 := bstep (se 1 (by rfl) ⟨9212858, by rfl⟩ : syracuseStep 12283811 = 18425717) B18425717
theorem B1536079 : Blo 447780 1536079 := bstep (se 1 (by rfl) ⟨1152059, by rfl⟩ : syracuseStep 1536079 = 2304119) B2304119
theorem B3895411 : Blo 447780 3895411 := bstep (se 1 (by rfl) ⟨2921558, by rfl⟩ : syracuseStep 3895411 = 5843117) B5843117
theorem B1011959 : Blo 447780 1011959 := bstep (se 1 (by rfl) ⟨758969, by rfl⟩ : syracuseStep 1011959 = 1517939) B1517939
theorem B1143031 : Blo 447780 1143031 := bstep (se 1 (by rfl) ⟨857273, by rfl⟩ : syracuseStep 1143031 = 1714547) B1714547
theorem B1438013 : Blo 447780 1438013 := bstep (se 3 (by rfl) ⟨269627, by rfl⟩ : syracuseStep 1438013 = 539255) B539255
theorem B5534081 : Blo 447780 5534081 := bstep (se 2 (by rfl) ⟨2075280, by rfl⟩ : syracuseStep 5534081 = 4150561) B4150561
theorem B913927 : Blo 447780 913927 := bstep (se 1 (by rfl) ⟨685445, by rfl⟩ : syracuseStep 913927 = 1370891) B1370891
theorem B1143305 : Blo 447780 1143305 := bstep (se 2 (by rfl) ⟨428739, by rfl⟩ : syracuseStep 1143305 = 857479) B857479
theorem B1077799 : Blo 447780 1077799 := bstep (se 1 (by rfl) ⟨808349, by rfl⟩ : syracuseStep 1077799 = 1616699) B1616699
theorem B1143335 : Blo 447780 1143335 := bstep (se 1 (by rfl) ⟨857501, by rfl⟩ : syracuseStep 1143335 = 1715003) B1715003
theorem B1012553 : Blo 447780 1012553 := bstep (se 2 (by rfl) ⟨379707, by rfl⟩ : syracuseStep 1012553 = 759415) B759415
theorem B2880485 : Blo 447780 2880485 := bstep (se 4 (by rfl) ⟨270045, by rfl⟩ : syracuseStep 2880485 = 540091) B540091
theorem B7468081 : Blo 447780 7468081 := bstep (se 2 (by rfl) ⟨2800530, by rfl⟩ : syracuseStep 7468081 = 5601061) B5601061
theorem B685135 : Blo 447780 685135 := bstep (se 1 (by rfl) ⟨513851, by rfl⟩ : syracuseStep 685135 = 1027703) B1027703
theorem B3077519 : Blo 447780 3077519 := bstep (se 1 (by rfl) ⟨2308139, by rfl⟩ : syracuseStep 3077519 = 4616279) B4616279
theorem B4388413 : Blo 447780 4388413 := bstep (se 3 (by rfl) ⟨822827, by rfl⟩ : syracuseStep 4388413 = 1645655) B1645655
theorem B1013345 : Blo 447780 1013345 := bstep (se 2 (by rfl) ⟨380004, by rfl⟩ : syracuseStep 1013345 = 760009) B760009
theorem B718507 : Blo 447780 718507 := bstep (se 1 (by rfl) ⟨538880, by rfl⟩ : syracuseStep 718507 = 1077761) B1077761
theorem B3700615 : Blo 447780 3700615 := bstep (se 1 (by rfl) ⟨2775461, by rfl⟩ : syracuseStep 3700615 = 5550923) B5550923
theorem B1013687 : Blo 447780 1013687 := bstep (se 1 (by rfl) ⟨760265, by rfl⟩ : syracuseStep 1013687 = 1520531) B1520531
theorem B9238481 : Blo 447780 9238481 := bstep (se 2 (by rfl) ⟨3464430, by rfl⟩ : syracuseStep 9238481 = 6928861) B6928861
theorem B2161133 : Blo 447780 2161133 := bstep (se 3 (by rfl) ⟨405212, by rfl⟩ : syracuseStep 2161133 = 810425) B810425
theorem B850439 : Blo 447780 850439 := bstep (se 1 (by rfl) ⟨637829, by rfl⟩ : syracuseStep 850439 = 1275659) B1275659
theorem B1014281 : Blo 447780 1014281 := bstep (se 2 (by rfl) ⟨380355, by rfl⟩ : syracuseStep 1014281 = 760711) B760711
theorem B719417 : Blo 447780 719417 := bstep (se 2 (by rfl) ⟨269781, by rfl⟩ : syracuseStep 719417 = 539563) B539563
theorem B2554577 : Blo 447780 2554577 := bstep (se 2 (by rfl) ⟨957966, by rfl⟩ : syracuseStep 2554577 = 1915933) B1915933
theorem B1014623 : Blo 447780 1014623 := bstep (se 1 (by rfl) ⟨760967, by rfl⟩ : syracuseStep 1014623 = 1521935) B1521935
theorem B1014803 : Blo 447780 1014803 := bstep (se 1 (by rfl) ⟨761102, by rfl⟩ : syracuseStep 1014803 = 1522205) B1522205
theorem B1703065 : Blo 447780 1703065 := bstep (se 2 (by rfl) ⟨638649, by rfl⟩ : syracuseStep 1703065 = 1277299) B1277299
theorem B851305 : Blo 447780 851305 := bstep (se 2 (by rfl) ⟨319239, by rfl⟩ : syracuseStep 851305 = 638479) B638479
theorem B1015145 : Blo 447780 1015145 := bstep (se 2 (by rfl) ⟨380679, by rfl⟩ : syracuseStep 1015145 = 761359) B761359
theorem B1703369 : Blo 447780 1703369 := bstep (se 2 (by rfl) ⟨638763, by rfl⟩ : syracuseStep 1703369 = 1277527) B1277527
theorem B36961757 : Blo 447780 36961757 := bstep (se 3 (by rfl) ⟨6930329, by rfl⟩ : syracuseStep 36961757 = 13860659) B13860659
theorem B851465 : Blo 447780 851465 := bstep (se 2 (by rfl) ⟨319299, by rfl⟩ : syracuseStep 851465 = 638599) B638599
theorem B1703855 : Blo 447780 1703855 := bstep (se 1 (by rfl) ⟨1277891, by rfl⟩ : syracuseStep 1703855 = 2555783) B2555783
theorem B1015739 : Blo 447780 1015739 := bstep (se 1 (by rfl) ⟨761804, by rfl⟩ : syracuseStep 1015739 = 1523609) B1523609
theorem B1016171 : Blo 447780 1016171 := bstep (se 1 (by rfl) ⟨762128, by rfl⟩ : syracuseStep 1016171 = 1524257) B1524257
theorem B1081711 : Blo 447780 1081711 := bstep (se 1 (by rfl) ⟨811283, by rfl⟩ : syracuseStep 1081711 = 1622567) B1622567
theorem B16417241 : Blo 447780 16417241 := bstep (se 2 (by rfl) ⟨6156465, by rfl⟩ : syracuseStep 16417241 = 12312931) B12312931
theorem B721403 : Blo 447780 721403 := bstep (se 1 (by rfl) ⟨541052, by rfl⟩ : syracuseStep 721403 = 1082105) B1082105
theorem B1016315 : Blo 447780 1016315 := bstep (se 1 (by rfl) ⟨762236, by rfl⟩ : syracuseStep 1016315 = 1524473) B1524473
theorem B1016441 : Blo 447780 1016441 := bstep (se 2 (by rfl) ⟨381165, by rfl⟩ : syracuseStep 1016441 = 762331) B762331
theorem B1016495 : Blo 447780 1016495 := bstep (se 1 (by rfl) ⟨762371, by rfl⟩ : syracuseStep 1016495 = 1524743) B1524743
theorem B3834701 : Blo 447780 3834701 := bstep (se 3 (by rfl) ⟨719006, by rfl⟩ : syracuseStep 3834701 = 1438013) B1438013
theorem B1279327 : Blo 447780 1279327 := bstep (se 1 (by rfl) ⟨959495, by rfl⟩ : syracuseStep 1279327 = 1918991) B1918991
theorem B1082873 : Blo 447780 1082873 := bstep (se 2 (by rfl) ⟨406077, by rfl⟩ : syracuseStep 1082873 = 812155) B812155
theorem B1083739 : Blo 447780 1083739 := bstep (se 1 (by rfl) ⟨812804, by rfl⟩ : syracuseStep 1083739 = 1625609) B1625609
theorem B1706771 : Blo 447780 1706771 := bstep (se 1 (by rfl) ⟨1280078, by rfl⟩ : syracuseStep 1706771 = 2560157) B2560157
theorem B2198339 : Blo 447780 2198339 := bstep (se 1 (by rfl) ⟨1648754, by rfl⟩ : syracuseStep 2198339 = 3297509) B3297509
theorem B1084403 : Blo 447780 1084403 := bstep (se 1 (by rfl) ⟨813302, by rfl⟩ : syracuseStep 1084403 = 1626605) B1626605
theorem B1707227 : Blo 447780 1707227 := bstep (se 1 (by rfl) ⟨1280420, by rfl⟩ : syracuseStep 1707227 = 2560841) B2560841
theorem B757343 : Blo 447780 757343 := bstep (se 1 (by rfl) ⟨568007, by rfl⟩ : syracuseStep 757343 = 1136015) B1136015
theorem B1150625 : Blo 447780 1150625 := bstep (se 2 (by rfl) ⟨431484, by rfl⟩ : syracuseStep 1150625 = 862969) B862969
theorem B1216235 : Blo 447780 1216235 := bstep (se 1 (by rfl) ⟨912176, by rfl⟩ : syracuseStep 1216235 = 1824353) B1824353
theorem B757559 : Blo 447780 757559 := bstep (se 1 (by rfl) ⟨568169, by rfl⟩ : syracuseStep 757559 = 1136339) B1136339
theorem B1511297 : Blo 447780 1511297 := bstep (se 2 (by rfl) ⟨566736, by rfl⟩ : syracuseStep 1511297 = 1133473) B1133473
theorem B2592971 : Blo 447780 2592971 := bstep (se 1 (by rfl) ⟨1944728, by rfl⟩ : syracuseStep 2592971 = 3889457) B3889457
theorem B1151443 : Blo 447780 1151443 := bstep (se 1 (by rfl) ⟨863582, by rfl⟩ : syracuseStep 1151443 = 1727165) B1727165
theorem B3838427 : Blo 447780 3838427 := bstep (se 1 (by rfl) ⟨2878820, by rfl⟩ : syracuseStep 3838427 = 5757641) B5757641
theorem B758335 : Blo 447780 758335 := bstep (se 1 (by rfl) ⟨568751, by rfl⟩ : syracuseStep 758335 = 1137503) B1137503
theorem B1512107 : Blo 447780 1512107 := bstep (se 1 (by rfl) ⟨1134080, by rfl⟩ : syracuseStep 1512107 = 2268161) B2268161
theorem B1708715 : Blo 447780 1708715 := bstep (se 1 (by rfl) ⟨1281536, by rfl⟩ : syracuseStep 1708715 = 2563073) B2563073
theorem B2429891 : Blo 447780 2429891 := bstep (se 1 (by rfl) ⟨1822418, by rfl⟩ : syracuseStep 2429891 = 3644837) B3644837
theorem B1512647 : Blo 447780 1512647 := bstep (se 1 (by rfl) ⟨1134485, by rfl⟩ : syracuseStep 1512647 = 2268971) B2268971
theorem B759017 : Blo 447780 759017 := bstep (se 2 (by rfl) ⟨284631, by rfl⟩ : syracuseStep 759017 = 569263) B569263
theorem B759071 : Blo 447780 759071 := bstep (se 1 (by rfl) ⟨569303, by rfl⟩ : syracuseStep 759071 = 1138607) B1138607
theorem B857441 : Blo 447780 857441 := bstep (se 2 (by rfl) ⟨321540, by rfl⟩ : syracuseStep 857441 = 643081) B643081
theorem B1643899 : Blo 447780 1643899 := bstep (se 1 (by rfl) ⟨1232924, by rfl⟩ : syracuseStep 1643899 = 2465849) B2465849
theorem B5117579 : Blo 447780 5117579 := bstep (se 1 (by rfl) ⟨3838184, by rfl⟩ : syracuseStep 5117579 = 7676369) B7676369
theorem B1218311 : Blo 447780 1218311 := bstep (se 1 (by rfl) ⟨913733, by rfl⟩ : syracuseStep 1218311 = 1827467) B1827467
theorem B1218569 : Blo 447780 1218569 := bstep (se 2 (by rfl) ⟨456963, by rfl⟩ : syracuseStep 1218569 = 913927) B913927
theorem B1939535 : Blo 447780 1939535 := bstep (se 1 (by rfl) ⟨1454651, by rfl⟩ : syracuseStep 1939535 = 2909303) B2909303
theorem B11507993 : Blo 447780 11507993 := bstep (se 2 (by rfl) ⟨4315497, by rfl⟩ : syracuseStep 11507993 = 8630995) B8630995
theorem B11573603 : Blo 447780 11573603 := bstep (se 1 (by rfl) ⟨8680202, by rfl⟩ : syracuseStep 11573603 = 17360405) B17360405
theorem B957035 : Blo 447780 957035 := bstep (se 1 (by rfl) ⟨717776, by rfl⟩ : syracuseStep 957035 = 1435553) B1435553
theorem B3414635 : Blo 447780 3414635 := bstep (se 1 (by rfl) ⟨2560976, by rfl⟩ : syracuseStep 3414635 = 5121953) B5121953
theorem B760441 : Blo 447780 760441 := bstep (se 2 (by rfl) ⟨285165, by rfl⟩ : syracuseStep 760441 = 570331) B570331
theorem B1514159 : Blo 447780 1514159 := bstep (se 1 (by rfl) ⟨1135619, by rfl⟩ : syracuseStep 1514159 = 2271239) B2271239
theorem B760495 : Blo 447780 760495 := bstep (se 1 (by rfl) ⟨570371, by rfl⟩ : syracuseStep 760495 = 1140743) B1140743
theorem B2267837 : Blo 447780 2267837 := bstep (se 3 (by rfl) ⟨425219, by rfl⟩ : syracuseStep 2267837 = 850439) B850439
theorem B8657603 : Blo 447780 8657603 := bstep (se 1 (by rfl) ⟨6493202, by rfl⟩ : syracuseStep 8657603 = 12986405) B12986405
theorem B3250925 : Blo 447780 3250925 := bstep (se 3 (by rfl) ⟨609548, by rfl⟩ : syracuseStep 3250925 = 1219097) B1219097
theorem B1514483 : Blo 447780 1514483 := bstep (se 1 (by rfl) ⟨1135862, by rfl⟩ : syracuseStep 1514483 = 2271725) B2271725
theorem B1285159 : Blo 447780 1285159 := bstep (se 1 (by rfl) ⟨963869, by rfl⟩ : syracuseStep 1285159 = 1927739) B1927739
theorem B1220039 : Blo 447780 1220039 := bstep (se 1 (by rfl) ⟨915029, by rfl⟩ : syracuseStep 1220039 = 1830059) B1830059
theorem B1515023 : Blo 447780 1515023 := bstep (se 1 (by rfl) ⟨1136267, by rfl⟩ : syracuseStep 1515023 = 2272535) B2272535
theorem B1711631 : Blo 447780 1711631 := bstep (se 1 (by rfl) ⟨1283723, by rfl⟩ : syracuseStep 1711631 = 2567447) B2567447
theorem B3251735 : Blo 447780 3251735 := bstep (se 1 (by rfl) ⟨2438801, by rfl⟩ : syracuseStep 3251735 = 4877603) B4877603
theorem B958009 : Blo 447780 958009 := bstep (se 2 (by rfl) ⟨359253, by rfl⟩ : syracuseStep 958009 = 718507) B718507
theorem B762203 : Blo 447780 762203 := bstep (se 1 (by rfl) ⟨571652, by rfl⟩ : syracuseStep 762203 = 1143305) B1143305
theorem B762223 : Blo 447780 762223 := bstep (se 1 (by rfl) ⟨571667, by rfl⟩ : syracuseStep 762223 = 1143335) B1143335
theorem B1516103 : Blo 447780 1516103 := bstep (se 1 (by rfl) ⟨1137077, by rfl⟩ : syracuseStep 1516103 = 2274155) B2274155
theorem B1647175 : Blo 447780 1647175 := bstep (se 1 (by rfl) ⟨1235381, by rfl⟩ : syracuseStep 1647175 = 2470763) B2470763
theorem B1516535 : Blo 447780 1516535 := bstep (se 1 (by rfl) ⟨1137401, by rfl⟩ : syracuseStep 1516535 = 2274803) B2274803
theorem B4826305 : Blo 447780 4826305 := bstep (se 2 (by rfl) ⟨1809864, by rfl⟩ : syracuseStep 4826305 = 3619729) B3619729
theorem B3122621 : Blo 447780 3122621 := bstep (se 3 (by rfl) ⟨585491, by rfl⟩ : syracuseStep 3122621 = 1170983) B1170983
theorem B2434541 : Blo 447780 2434541 := bstep (se 3 (by rfl) ⟨456476, by rfl⟩ : syracuseStep 2434541 = 912953) B912953
theorem B4597235 : Blo 447780 4597235 := bstep (se 1 (by rfl) ⟨3447926, by rfl⟩ : syracuseStep 4597235 = 6895853) B6895853
theorem B2270753 : Blo 447780 2270753 := bstep (se 2 (by rfl) ⟨851532, by rfl⟩ : syracuseStep 2270753 = 1703065) B1703065
theorem B1517399 : Blo 447780 1517399 := bstep (se 1 (by rfl) ⟨1138049, by rfl⟩ : syracuseStep 1517399 = 2276099) B2276099
theorem B567643 : Blo 447780 567643 := bstep (se 1 (by rfl) ⟨425732, by rfl⟩ : syracuseStep 567643 = 851465) B851465
theorem B961247 : Blo 447780 961247 := bstep (se 1 (by rfl) ⟨720935, by rfl⟩ : syracuseStep 961247 = 1441871) B1441871
theorem B1518479 : Blo 447780 1518479 := bstep (se 1 (by rfl) ⟨1138859, by rfl⟩ : syracuseStep 1518479 = 2277719) B2277719
theorem B568615 : Blo 447780 568615 := bstep (se 1 (by rfl) ⟨426461, by rfl⟩ : syracuseStep 568615 = 852923) B852923
theorem B10136951 : Blo 447780 10136951 := bstep (se 1 (by rfl) ⟨7602713, by rfl⟩ : syracuseStep 10136951 = 15205427) B15205427
theorem B1027591 : Blo 447780 1027591 := bstep (se 1 (by rfl) ⟨770693, by rfl⟩ : syracuseStep 1027591 = 1541387) B1541387
theorem B568939 : Blo 447780 568939 := bstep (se 1 (by rfl) ⟨426704, by rfl⟩ : syracuseStep 568939 = 853409) B853409
theorem B1912841 : Blo 447780 1912841 := bstep (se 2 (by rfl) ⟨717315, by rfl⟩ : syracuseStep 1912841 = 1434631) B1434631
theorem B1028105 : Blo 447780 1028105 := bstep (se 2 (by rfl) ⟨385539, by rfl⟩ : syracuseStep 1028105 = 771079) B771079
theorem B1519721 : Blo 447780 1519721 := bstep (se 2 (by rfl) ⟨569895, by rfl⟩ : syracuseStep 1519721 = 1139791) B1139791
theorem B504103 : Blo 447780 504103 := bstep (se 1 (by rfl) ⟨378077, by rfl⟩ : syracuseStep 504103 = 756155) B756155
theorem B504175 : Blo 447780 504175 := bstep (se 1 (by rfl) ⟨378131, by rfl⟩ : syracuseStep 504175 = 756263) B756263
theorem B8663597 : Blo 447780 8663597 := bstep (se 3 (by rfl) ⟨1624424, by rfl⟩ : syracuseStep 8663597 = 3248849) B3248849
theorem B16593457 : Blo 447780 16593457 := bstep (se 2 (by rfl) ⟨6222546, by rfl⟩ : syracuseStep 16593457 = 12445093) B12445093
theorem B504391 : Blo 447780 504391 := bstep (se 1 (by rfl) ⟨378293, by rfl⟩ : syracuseStep 504391 = 756587) B756587
theorem B1520585 : Blo 447780 1520585 := bstep (se 2 (by rfl) ⟨570219, by rfl⟩ : syracuseStep 1520585 = 1140439) B1140439
theorem B1913831 : Blo 447780 1913831 := bstep (se 1 (by rfl) ⟨1435373, by rfl⟩ : syracuseStep 1913831 = 2870747) B2870747
theorem B1520855 : Blo 447780 1520855 := bstep (se 1 (by rfl) ⟨1140641, by rfl⟩ : syracuseStep 1520855 = 2281283) B2281283
theorem B570655 : Blo 447780 570655 := bstep (se 1 (by rfl) ⟨427991, by rfl⟩ : syracuseStep 570655 = 855983) B855983
theorem B2372903 : Blo 447780 2372903 := bstep (se 1 (by rfl) ⟨1779677, by rfl⟩ : syracuseStep 2372903 = 3559355) B3559355
theorem B505255 : Blo 447780 505255 := bstep (se 1 (by rfl) ⟨378941, by rfl⟩ : syracuseStep 505255 = 757883) B757883
theorem B538207 : Blo 447780 538207 := bstep (se 1 (by rfl) ⟨403655, by rfl⟩ : syracuseStep 538207 = 807311) B807311
theorem B964399 : Blo 447780 964399 := bstep (se 1 (by rfl) ⟨723299, by rfl⟩ : syracuseStep 964399 = 1446599) B1446599
theorem B2275127 : Blo 447780 2275127 := bstep (se 1 (by rfl) ⟨1706345, by rfl⟩ : syracuseStep 2275127 = 3412691) B3412691
theorem B505831 : Blo 447780 505831 := bstep (se 1 (by rfl) ⟨379373, by rfl⟩ : syracuseStep 505831 = 758747) B758747
theorem B2275613 : Blo 447780 2275613 := bstep (se 3 (by rfl) ⟨426677, by rfl⟩ : syracuseStep 2275613 = 853355) B853355
theorem B3848573 : Blo 447780 3848573 := bstep (se 3 (by rfl) ⟨721607, by rfl⟩ : syracuseStep 3848573 = 1443215) B1443215
theorem B4111211 : Blo 447780 4111211 := bstep (se 1 (by rfl) ⟨3083408, by rfl⟩ : syracuseStep 4111211 = 6166817) B6166817
theorem B2734991 : Blo 447780 2734991 := bstep (se 1 (by rfl) ⟨2051243, by rfl⟩ : syracuseStep 2734991 = 4102487) B4102487
theorem B16464815 : Blo 447780 16464815 := bstep (se 1 (by rfl) ⟨12348611, by rfl⟩ : syracuseStep 16464815 = 24697223) B24697223
theorem B16694191 : Blo 447780 16694191 := bstep (se 1 (by rfl) ⟨12520643, by rfl⟩ : syracuseStep 16694191 = 25041287) B25041287
theorem B1522907 : Blo 447780 1522907 := bstep (se 1 (by rfl) ⟨1142180, by rfl⟩ : syracuseStep 1522907 = 2284361) B2284361
theorem B7781669 : Blo 447780 7781669 := bstep (se 4 (by rfl) ⟨729531, by rfl⟩ : syracuseStep 7781669 = 1459063) B1459063
theorem B1916257 : Blo 447780 1916257 := bstep (se 2 (by rfl) ⟨718596, by rfl⟩ : syracuseStep 1916257 = 1437193) B1437193
theorem B507487 : Blo 447780 507487 := bstep (se 1 (by rfl) ⟨380615, by rfl⟩ : syracuseStep 507487 = 761231) B761231
theorem B1916531 : Blo 447780 1916531 := bstep (se 1 (by rfl) ⟨1437398, by rfl⟩ : syracuseStep 1916531 = 2874797) B2874797
theorem B2572073 : Blo 447780 2572073 := bstep (se 2 (by rfl) ⟨964527, by rfl⟩ : syracuseStep 2572073 = 1929055) B1929055
theorem B1621889 : Blo 447780 1621889 := bstep (se 2 (by rfl) ⟨608208, by rfl⟩ : syracuseStep 1621889 = 1216417) B1216417
theorem B2277395 : Blo 447780 2277395 := bstep (se 1 (by rfl) ⟨1708046, by rfl⟩ : syracuseStep 2277395 = 3416093) B3416093
theorem B1523771 : Blo 447780 1523771 := bstep (se 1 (by rfl) ⟨1142828, by rfl⟩ : syracuseStep 1523771 = 2285657) B2285657
theorem B671849 : Blo 447780 671849 := bstep (se 2 (by rfl) ⟨251943, by rfl⟩ : syracuseStep 671849 = 503887) B503887
theorem B2048105 : Blo 447780 2048105 := bstep (se 2 (by rfl) ⟨768039, by rfl⟩ : syracuseStep 2048105 = 1536079) B1536079
theorem B5193881 : Blo 447780 5193881 := bstep (se 2 (by rfl) ⟨1947705, by rfl⟩ : syracuseStep 5193881 = 3895411) B3895411
theorem B39829765 : Blo 447780 39829765 := bstep (se 4 (by rfl) ⟨3734040, by rfl⟩ : syracuseStep 39829765 = 7468081) B7468081
theorem B1524041 : Blo 447780 1524041 := bstep (se 2 (by rfl) ⟨571515, by rfl⟩ : syracuseStep 1524041 = 1143031) B1143031
theorem B13877669 : Blo 447780 13877669 := bstep (se 4 (by rfl) ⟨1301031, by rfl⟩ : syracuseStep 13877669 = 2602063) B2602063
theorem B672167 : Blo 447780 672167 := bstep (se 1 (by rfl) ⟨504125, by rfl⟩ : syracuseStep 672167 = 1008251) B1008251
theorem B672251 : Blo 447780 672251 := bstep (se 1 (by rfl) ⟨504188, by rfl⟩ : syracuseStep 672251 = 1008377) B1008377
theorem B541279 : Blo 447780 541279 := bstep (se 1 (by rfl) ⟨405959, by rfl⟩ : syracuseStep 541279 = 811919) B811919
theorem B672377 : Blo 447780 672377 := bstep (se 2 (by rfl) ⟨252141, by rfl⟩ : syracuseStep 672377 = 504283) B504283
theorem B672431 : Blo 447780 672431 := bstep (se 1 (by rfl) ⟨504323, by rfl⟩ : syracuseStep 672431 = 1008647) B1008647
theorem B770743 : Blo 447780 770743 := bstep (se 1 (by rfl) ⟨578057, by rfl⟩ : syracuseStep 770743 = 1156115) B1156115
theorem B672479 : Blo 447780 672479 := bstep (se 1 (by rfl) ⟨504359, by rfl⟩ : syracuseStep 672479 = 1008719) B1008719
theorem B672743 : Blo 447780 672743 := bstep (se 1 (by rfl) ⟨504557, by rfl⟩ : syracuseStep 672743 = 1009115) B1009115
theorem B673001 : Blo 447780 673001 := bstep (se 2 (by rfl) ⟨252375, by rfl⟩ : syracuseStep 673001 = 504751) B504751
theorem B673055 : Blo 447780 673055 := bstep (se 1 (by rfl) ⟨504791, by rfl⟩ : syracuseStep 673055 = 1009583) B1009583
theorem B673223 : Blo 447780 673223 := bstep (se 1 (by rfl) ⟨504917, by rfl⟩ : syracuseStep 673223 = 1009835) B1009835
theorem B1295929 : Blo 447780 1295929 := bstep (se 2 (by rfl) ⟨485973, by rfl⟩ : syracuseStep 1295929 = 971947) B971947
theorem B673577 : Blo 447780 673577 := bstep (se 2 (by rfl) ⟨252591, by rfl⟩ : syracuseStep 673577 = 505183) B505183
theorem B673583 : Blo 447780 673583 := bstep (se 1 (by rfl) ⟨505187, by rfl⟩ : syracuseStep 673583 = 1010375) B1010375
theorem B5851217 : Blo 447780 5851217 := bstep (se 2 (by rfl) ⟨2194206, by rfl⟩ : syracuseStep 5851217 = 4388413) B4388413
theorem B26364149 : Blo 447780 26364149 := bstep (se 5 (by rfl) ⟨1235819, by rfl⟩ : syracuseStep 26364149 = 2471639) B2471639
theorem B674057 : Blo 447780 674057 := bstep (se 2 (by rfl) ⟨252771, by rfl⟩ : syracuseStep 674057 = 505543) B505543
theorem B674159 : Blo 447780 674159 := bstep (se 1 (by rfl) ⟨505619, by rfl⟩ : syracuseStep 674159 = 1011239) B1011239
theorem B4934153 : Blo 447780 4934153 := bstep (se 2 (by rfl) ⟨1850307, by rfl⟩ : syracuseStep 4934153 = 3700615) B3700615
theorem B674375 : Blo 447780 674375 := bstep (se 1 (by rfl) ⟨505781, by rfl⟩ : syracuseStep 674375 = 1011563) B1011563
theorem B674411 : Blo 447780 674411 := bstep (se 1 (by rfl) ⟨505808, by rfl⟩ : syracuseStep 674411 = 1011617) B1011617
theorem B510767 : Blo 447780 510767 := bstep (se 1 (by rfl) ⟨383075, by rfl⟩ : syracuseStep 510767 = 766151) B766151
theorem B674639 : Blo 447780 674639 := bstep (se 1 (by rfl) ⟨505979, by rfl⟩ : syracuseStep 674639 = 1011959) B1011959
theorem B2280311 : Blo 447780 2280311 := bstep (se 1 (by rfl) ⟨1710233, by rfl⟩ : syracuseStep 2280311 = 3420467) B3420467
theorem B3689387 : Blo 447780 3689387 := bstep (se 1 (by rfl) ⟨2767040, by rfl⟩ : syracuseStep 3689387 = 5534081) B5534081
theorem B675035 : Blo 447780 675035 := bstep (se 1 (by rfl) ⟨506276, by rfl⟩ : syracuseStep 675035 = 1012553) B1012553
theorem B1920323 : Blo 447780 1920323 := bstep (se 1 (by rfl) ⟨1440242, by rfl⟩ : syracuseStep 1920323 = 2880485) B2880485
theorem B675209 : Blo 447780 675209 := bstep (se 2 (by rfl) ⟨253203, by rfl⟩ : syracuseStep 675209 = 506407) B506407
theorem B2281121 : Blo 447780 2281121 := bstep (se 2 (by rfl) ⟨855420, by rfl⟩ : syracuseStep 2281121 = 1710841) B1710841
theorem B675563 : Blo 447780 675563 := bstep (se 1 (by rfl) ⟨506672, by rfl⟩ : syracuseStep 675563 = 1013345) B1013345
theorem B675791 : Blo 447780 675791 := bstep (se 1 (by rfl) ⟨506843, by rfl⟩ : syracuseStep 675791 = 1013687) B1013687
theorem B676187 : Blo 447780 676187 := bstep (se 1 (by rfl) ⟨507140, by rfl⟩ : syracuseStep 676187 = 1014281) B1014281
theorem B479611 : Blo 447780 479611 := bstep (se 1 (by rfl) ⟨359708, by rfl⟩ : syracuseStep 479611 = 719417) B719417
theorem B1135073 : Blo 447780 1135073 := bstep (se 2 (by rfl) ⟨425652, by rfl⟩ : syracuseStep 1135073 = 851305) B851305
theorem B676415 : Blo 447780 676415 := bstep (se 1 (by rfl) ⟨507311, by rfl⟩ : syracuseStep 676415 = 1014623) B1014623
theorem B1364663 : Blo 447780 1364663 := bstep (se 1 (by rfl) ⟨1023497, by rfl⟩ : syracuseStep 1364663 = 2046995) B2046995
theorem B676535 : Blo 447780 676535 := bstep (se 1 (by rfl) ⟨507401, by rfl⟩ : syracuseStep 676535 = 1014803) B1014803
theorem B3298157 : Blo 447780 3298157 := bstep (se 3 (by rfl) ⟨618404, by rfl⟩ : syracuseStep 3298157 = 1236809) B1236809
theorem B676763 : Blo 447780 676763 := bstep (se 1 (by rfl) ⟨507572, by rfl⟩ : syracuseStep 676763 = 1015145) B1015145
theorem B1135579 : Blo 447780 1135579 := bstep (se 1 (by rfl) ⟨851684, by rfl⟩ : syracuseStep 1135579 = 1703369) B1703369
theorem B1299671 : Blo 447780 1299671 := bstep (se 1 (by rfl) ⟨974753, by rfl⟩ : syracuseStep 1299671 = 1949507) B1949507
theorem B1135903 : Blo 447780 1135903 := bstep (se 1 (by rfl) ⟨851927, by rfl⟩ : syracuseStep 1135903 = 1703855) B1703855
theorem B677159 : Blo 447780 677159 := bstep (se 1 (by rfl) ⟨507869, by rfl⟩ : syracuseStep 677159 = 1015739) B1015739
theorem B447835 : Blo 447780 447835 := bstep (se 1 (by rfl) ⟨335876, by rfl⟩ : syracuseStep 447835 = 671753) B671753
theorem B447855 : Blo 447780 447855 := bstep (se 1 (by rfl) ⟨335891, by rfl⟩ : syracuseStep 447855 = 671783) B671783
theorem B677243 : Blo 447780 677243 := bstep (se 1 (by rfl) ⟨507932, by rfl⟩ : syracuseStep 677243 = 1015865) B1015865
theorem B447911 : Blo 447780 447911 := bstep (se 1 (by rfl) ⟨335933, by rfl⟩ : syracuseStep 447911 = 671867) B671867
theorem B677369 : Blo 447780 677369 := bstep (se 2 (by rfl) ⟨254013, by rfl⟩ : syracuseStep 677369 = 508027) B508027
theorem B447995 : Blo 447780 447995 := bstep (se 1 (by rfl) ⟨335996, by rfl⟩ : syracuseStep 447995 = 671993) B671993
theorem B9754157 : Blo 447780 9754157 := bstep (se 3 (by rfl) ⟨1828904, by rfl⟩ : syracuseStep 9754157 = 3657809) B3657809
theorem B2283065 : Blo 447780 2283065 := bstep (se 2 (by rfl) ⟨856149, by rfl⟩ : syracuseStep 2283065 = 1712299) B1712299
theorem B448063 : Blo 447780 448063 := bstep (se 1 (by rfl) ⟨336047, by rfl⟩ : syracuseStep 448063 = 672095) B672095
theorem B448071 : Blo 447780 448071 := bstep (se 1 (by rfl) ⟨336053, by rfl⟩ : syracuseStep 448071 = 672107) B672107
theorem B480863 : Blo 447780 480863 := bstep (se 1 (by rfl) ⟨360647, by rfl⟩ : syracuseStep 480863 = 721295) B721295
theorem B677471 : Blo 447780 677471 := bstep (se 1 (by rfl) ⟨508103, by rfl⟩ : syracuseStep 677471 = 1016207) B1016207
theorem B448223 : Blo 447780 448223 := bstep (se 1 (by rfl) ⟨336167, by rfl⟩ : syracuseStep 448223 = 672335) B672335
theorem B448303 : Blo 447780 448303 := bstep (se 1 (by rfl) ⟨336227, by rfl⟩ : syracuseStep 448303 = 672455) B672455
theorem B448411 : Blo 447780 448411 := bstep (se 1 (by rfl) ⟨336308, by rfl⟩ : syracuseStep 448411 = 672617) B672617
theorem B448463 : Blo 447780 448463 := bstep (se 1 (by rfl) ⟨336347, by rfl⟩ : syracuseStep 448463 = 672695) B672695
theorem B448487 : Blo 447780 448487 := bstep (se 1 (by rfl) ⟨336365, by rfl⟩ : syracuseStep 448487 = 672731) B672731
theorem B2218063 : Blo 447780 2218063 := bstep (se 1 (by rfl) ⟨1663547, by rfl⟩ : syracuseStep 2218063 = 3327095) B3327095
theorem B448799 : Blo 447780 448799 := bstep (se 1 (by rfl) ⟨336599, by rfl⟩ : syracuseStep 448799 = 673199) B673199
theorem B448859 : Blo 447780 448859 := bstep (se 1 (by rfl) ⟨336644, by rfl⟩ : syracuseStep 448859 = 673289) B673289
theorem B1136987 : Blo 447780 1136987 := bstep (se 1 (by rfl) ⟨852740, by rfl⟩ : syracuseStep 1136987 = 1705481) B1705481
theorem B448879 : Blo 447780 448879 := bstep (se 1 (by rfl) ⟨336659, by rfl⟩ : syracuseStep 448879 = 673319) B673319
theorem B448935 : Blo 447780 448935 := bstep (se 1 (by rfl) ⟨336701, by rfl⟩ : syracuseStep 448935 = 673403) B673403
theorem B449019 : Blo 447780 449019 := bstep (se 1 (by rfl) ⟨336764, by rfl⟩ : syracuseStep 449019 = 673529) B673529
theorem B449087 : Blo 447780 449087 := bstep (se 1 (by rfl) ⟨336815, by rfl⟩ : syracuseStep 449087 = 673631) B673631
theorem B449095 : Blo 447780 449095 := bstep (se 1 (by rfl) ⟨336821, by rfl⟩ : syracuseStep 449095 = 673643) B673643
theorem B3234437 : Blo 447780 3234437 := bstep (se 4 (by rfl) ⟨303228, by rfl⟩ : syracuseStep 3234437 = 606457) B606457
theorem B449247 : Blo 447780 449247 := bstep (se 1 (by rfl) ⟨336935, by rfl⟩ : syracuseStep 449247 = 673871) B673871
theorem B973559 : Blo 447780 973559 := bstep (se 1 (by rfl) ⟨730169, by rfl⟩ : syracuseStep 973559 = 1460339) B1460339
theorem B449327 : Blo 447780 449327 := bstep (se 1 (by rfl) ⟨336995, by rfl⟩ : syracuseStep 449327 = 673991) B673991
theorem B449435 : Blo 447780 449435 := bstep (se 1 (by rfl) ⟨337076, by rfl⟩ : syracuseStep 449435 = 674153) B674153
theorem B3660731 : Blo 447780 3660731 := bstep (se 1 (by rfl) ⟨2745548, by rfl⟩ : syracuseStep 3660731 = 5491097) B5491097
theorem B449487 : Blo 447780 449487 := bstep (se 1 (by rfl) ⟨337115, by rfl⟩ : syracuseStep 449487 = 674231) B674231
theorem B449511 : Blo 447780 449511 := bstep (se 1 (by rfl) ⟨337133, by rfl⟩ : syracuseStep 449511 = 674267) B674267
theorem B2776051 : Blo 447780 2776051 := bstep (se 1 (by rfl) ⟨2082038, by rfl⟩ : syracuseStep 2776051 = 4164077) B4164077
theorem B2317501 : Blo 447780 2317501 := bstep (se 3 (by rfl) ⟨434531, by rfl⟩ : syracuseStep 2317501 = 869063) B869063
theorem B449823 : Blo 447780 449823 := bstep (se 1 (by rfl) ⟨337367, by rfl⟩ : syracuseStep 449823 = 674735) B674735
theorem B1137959 : Blo 447780 1137959 := bstep (se 1 (by rfl) ⟨853469, by rfl⟩ : syracuseStep 1137959 = 1706939) B1706939
theorem B449883 : Blo 447780 449883 := bstep (se 1 (by rfl) ⟨337412, by rfl⟩ : syracuseStep 449883 = 674825) B674825
theorem B449903 : Blo 447780 449903 := bstep (se 1 (by rfl) ⟨337427, by rfl⟩ : syracuseStep 449903 = 674855) B674855
theorem B449959 : Blo 447780 449959 := bstep (se 1 (by rfl) ⟨337469, by rfl⟩ : syracuseStep 449959 = 674939) B674939
theorem B65068505 : Blo 447780 65068505 := bstep (se 2 (by rfl) ⟨24400689, by rfl⟩ : syracuseStep 65068505 = 48801379) B48801379
theorem B450043 : Blo 447780 450043 := bstep (se 1 (by rfl) ⟨337532, by rfl⟩ : syracuseStep 450043 = 675065) B675065
theorem B450111 : Blo 447780 450111 := bstep (se 1 (by rfl) ⟨337583, by rfl⟩ : syracuseStep 450111 = 675167) B675167
theorem B450119 : Blo 447780 450119 := bstep (se 1 (by rfl) ⟨337589, by rfl⟩ : syracuseStep 450119 = 675179) B675179
theorem B2285171 : Blo 447780 2285171 := bstep (se 1 (by rfl) ⟨1713878, by rfl⟩ : syracuseStep 2285171 = 3427757) B3427757
theorem B450271 : Blo 447780 450271 := bstep (se 1 (by rfl) ⟨337703, by rfl⟩ : syracuseStep 450271 = 675407) B675407
theorem B450351 : Blo 447780 450351 := bstep (se 1 (by rfl) ⟨337763, by rfl⟩ : syracuseStep 450351 = 675527) B675527
theorem B450459 : Blo 447780 450459 := bstep (se 1 (by rfl) ⟨337844, by rfl⟩ : syracuseStep 450459 = 675689) B675689
theorem B1925039 : Blo 447780 1925039 := bstep (se 1 (by rfl) ⟨1443779, by rfl⟩ : syracuseStep 1925039 = 2887559) B2887559
theorem B1007567 : Blo 447780 1007567 := bstep (se 1 (by rfl) ⟨755675, by rfl⟩ : syracuseStep 1007567 = 1511351) B1511351
theorem B450511 : Blo 447780 450511 := bstep (se 1 (by rfl) ⟨337883, by rfl⟩ : syracuseStep 450511 = 675767) B675767
theorem B450535 : Blo 447780 450535 := bstep (se 1 (by rfl) ⟨337901, by rfl⟩ : syracuseStep 450535 = 675803) B675803
theorem B450847 : Blo 447780 450847 := bstep (se 1 (by rfl) ⟨338135, by rfl⟩ : syracuseStep 450847 = 676271) B676271
theorem B1007945 : Blo 447780 1007945 := bstep (se 2 (by rfl) ⟨377979, by rfl⟩ : syracuseStep 1007945 = 755959) B755959
theorem B1007963 : Blo 447780 1007963 := bstep (se 1 (by rfl) ⟨755972, by rfl⟩ : syracuseStep 1007963 = 1511945) B1511945
theorem B450907 : Blo 447780 450907 := bstep (se 1 (by rfl) ⟨338180, by rfl⟩ : syracuseStep 450907 = 676361) B676361
theorem B450927 : Blo 447780 450927 := bstep (se 1 (by rfl) ⟨338195, by rfl⟩ : syracuseStep 450927 = 676391) B676391
theorem B450983 : Blo 447780 450983 := bstep (se 1 (by rfl) ⟨338237, by rfl⟩ : syracuseStep 450983 = 676475) B676475
theorem B451067 : Blo 447780 451067 := bstep (se 1 (by rfl) ⟨338300, by rfl⟩ : syracuseStep 451067 = 676601) B676601
theorem B451135 : Blo 447780 451135 := bstep (se 1 (by rfl) ⟨338351, by rfl⟩ : syracuseStep 451135 = 676703) B676703
theorem B451143 : Blo 447780 451143 := bstep (se 1 (by rfl) ⟨338357, by rfl⟩ : syracuseStep 451143 = 676715) B676715
theorem B451295 : Blo 447780 451295 := bstep (se 1 (by rfl) ⟨338471, by rfl⟩ : syracuseStep 451295 = 676943) B676943
theorem B1139447 : Blo 447780 1139447 := bstep (se 1 (by rfl) ⟨854585, by rfl⟩ : syracuseStep 1139447 = 1709171) B1709171
theorem B615215 : Blo 447780 615215 := bstep (se 1 (by rfl) ⟨461411, by rfl⟩ : syracuseStep 615215 = 922823) B922823
theorem B451375 : Blo 447780 451375 := bstep (se 1 (by rfl) ⟨338531, by rfl⟩ : syracuseStep 451375 = 677063) B677063
theorem B1008539 : Blo 447780 1008539 := bstep (se 1 (by rfl) ⟨756404, by rfl⟩ : syracuseStep 1008539 = 1512809) B1512809
theorem B451483 : Blo 447780 451483 := bstep (se 1 (by rfl) ⟨338612, by rfl⟩ : syracuseStep 451483 = 677225) B677225
theorem B451535 : Blo 447780 451535 := bstep (se 1 (by rfl) ⟨338651, by rfl⟩ : syracuseStep 451535 = 677303) B677303
theorem B451559 : Blo 447780 451559 := bstep (se 1 (by rfl) ⟨338669, by rfl⟩ : syracuseStep 451559 = 677339) B677339
theorem B1008737 : Blo 447780 1008737 := bstep (se 2 (by rfl) ⟨378276, by rfl⟩ : syracuseStep 1008737 = 756553) B756553
theorem B1827983 : Blo 447780 1827983 := bstep (se 1 (by rfl) ⟨1370987, by rfl⟩ : syracuseStep 1827983 = 2741975) B2741975
theorem B2286791 : Blo 447780 2286791 := bstep (se 1 (by rfl) ⟨1715093, by rfl⟩ : syracuseStep 2286791 = 3430187) B3430187
theorem B1008935 : Blo 447780 1008935 := bstep (se 1 (by rfl) ⟨756701, by rfl⟩ : syracuseStep 1008935 = 1513403) B1513403
theorem B1140065 : Blo 447780 1140065 := bstep (se 2 (by rfl) ⟨427524, by rfl⟩ : syracuseStep 1140065 = 855049) B855049
theorem B2286953 : Blo 447780 2286953 := bstep (se 2 (by rfl) ⟨857607, by rfl⟩ : syracuseStep 2286953 = 1715215) B1715215
theorem B2876795 : Blo 447780 2876795 := bstep (se 1 (by rfl) ⟨2157596, by rfl⟩ : syracuseStep 2876795 = 4315193) B4315193
theorem B32826869 : Blo 447780 32826869 := bstep (se 5 (by rfl) ⟨1538759, by rfl⟩ : syracuseStep 32826869 = 3077519) B3077519
theorem B1009313 : Blo 447780 1009313 := bstep (se 2 (by rfl) ⟨378492, by rfl⟩ : syracuseStep 1009313 = 756985) B756985
theorem B33613643 : Blo 447780 33613643 := bstep (se 1 (by rfl) ⟨25210232, by rfl⟩ : syracuseStep 33613643 = 50420465) B50420465
theorem B3237839 : Blo 447780 3237839 := bstep (se 1 (by rfl) ⟨2428379, by rfl⟩ : syracuseStep 3237839 = 4856759) B4856759
theorem B1009673 : Blo 447780 1009673 := bstep (se 2 (by rfl) ⟨378627, by rfl⟩ : syracuseStep 1009673 = 757255) B757255
theorem B1927415 : Blo 447780 1927415 := bstep (se 1 (by rfl) ⟨1445561, by rfl⟩ : syracuseStep 1927415 = 2891123) B2891123
theorem B1927567 : Blo 447780 1927567 := bstep (se 1 (by rfl) ⟨1445675, by rfl⟩ : syracuseStep 1927567 = 2891351) B2891351
theorem B1010087 : Blo 447780 1010087 := bstep (se 1 (by rfl) ⟨757565, by rfl⟩ : syracuseStep 1010087 = 1515131) B1515131
theorem B3238355 : Blo 447780 3238355 := bstep (se 1 (by rfl) ⟨2428766, by rfl⟩ : syracuseStep 3238355 = 4857533) B4857533
theorem B39414275 : Blo 447780 39414275 := bstep (se 1 (by rfl) ⟨29560706, by rfl⟩ : syracuseStep 39414275 = 59121413) B59121413
theorem B1010195 : Blo 447780 1010195 := bstep (se 1 (by rfl) ⟨757646, by rfl⟩ : syracuseStep 1010195 = 1515293) B1515293
theorem B1010249 : Blo 447780 1010249 := bstep (se 2 (by rfl) ⟨378843, by rfl⟩ : syracuseStep 1010249 = 757687) B757687
theorem B1141523 : Blo 447780 1141523 := bstep (se 1 (by rfl) ⟨856142, by rfl⟩ : syracuseStep 1141523 = 1712285) B1712285
theorem B2190235 : Blo 447780 2190235 := bstep (se 1 (by rfl) ⟨1642676, by rfl⟩ : syracuseStep 2190235 = 3285353) B3285353
theorem B1010663 : Blo 447780 1010663 := bstep (se 1 (by rfl) ⟨757997, by rfl⟩ : syracuseStep 1010663 = 1515995) B1515995
theorem B1141735 : Blo 447780 1141735 := bstep (se 1 (by rfl) ⟨856301, by rfl⟩ : syracuseStep 1141735 = 1712603) B1712603
theorem B3402971 : Blo 447780 3402971 := bstep (se 1 (by rfl) ⟨2552228, by rfl⟩ : syracuseStep 3402971 = 5104457) B5104457
theorem B1142009 : Blo 447780 1142009 := bstep (se 2 (by rfl) ⟨428253, by rfl⟩ : syracuseStep 1142009 = 856507) B856507
theorem B1011041 : Blo 447780 1011041 := bstep (se 2 (by rfl) ⟨379140, by rfl⟩ : syracuseStep 1011041 = 758281) B758281
theorem B486767 : Blo 447780 486767 := bstep (se 1 (by rfl) ⟨365075, by rfl⟩ : syracuseStep 486767 = 730151) B730151
theorem B1437065 : Blo 447780 1437065 := bstep (se 2 (by rfl) ⟨538899, by rfl⟩ : syracuseStep 1437065 = 1077799) B1077799
theorem B1011131 : Blo 447780 1011131 := bstep (se 1 (by rfl) ⟨758348, by rfl⟩ : syracuseStep 1011131 = 1516697) B1516697
theorem B1011257 : Blo 447780 1011257 := bstep (se 2 (by rfl) ⟨379221, by rfl⟩ : syracuseStep 1011257 = 758443) B758443
theorem B5107373 : Blo 447780 5107373 := bstep (se 3 (by rfl) ⟨957632, by rfl⟩ : syracuseStep 5107373 = 1915265) B1915265
theorem B2158289 : Blo 447780 2158289 := bstep (se 2 (by rfl) ⟨809358, by rfl⟩ : syracuseStep 2158289 = 1618717) B1618717
theorem B1142657 : Blo 447780 1142657 := bstep (se 2 (by rfl) ⟨428496, by rfl⟩ : syracuseStep 1142657 = 856993) B856993
theorem B684137 : Blo 447780 684137 := bstep (se 2 (by rfl) ⟨256551, by rfl⟩ : syracuseStep 684137 = 513103) B513103
theorem B913513 : Blo 447780 913513 := bstep (se 2 (by rfl) ⟨342567, by rfl⟩ : syracuseStep 913513 = 685135) B685135
theorem B1011923 : Blo 447780 1011923 := bstep (se 1 (by rfl) ⟨758942, by rfl⟩ : syracuseStep 1011923 = 1517885) B1517885
theorem B1011977 : Blo 447780 1011977 := bstep (se 2 (by rfl) ⟨379491, by rfl⟩ : syracuseStep 1011977 = 758983) B758983
theorem B1012193 : Blo 447780 1012193 := bstep (se 2 (by rfl) ⟨379572, by rfl⟩ : syracuseStep 1012193 = 759145) B759145
theorem B5763635 : Blo 447780 5763635 := bstep (se 1 (by rfl) ⟨4322726, by rfl⟩ : syracuseStep 5763635 = 8645453) B8645453
theorem B1700423 : Blo 447780 1700423 := bstep (se 1 (by rfl) ⟨1275317, by rfl⟩ : syracuseStep 1700423 = 2550635) B2550635
theorem B1143467 : Blo 447780 1143467 := bstep (se 1 (by rfl) ⟨857600, by rfl⟩ : syracuseStep 1143467 = 1715201) B1715201
theorem B1012499 : Blo 447780 1012499 := bstep (se 1 (by rfl) ⟨759374, by rfl⟩ : syracuseStep 1012499 = 1518749) B1518749
theorem B1012859 : Blo 447780 1012859 := bstep (se 1 (by rfl) ⟨759644, by rfl⟩ : syracuseStep 1012859 = 1519289) B1519289
theorem B7271639 : Blo 447780 7271639 := bstep (se 1 (by rfl) ⟨5453729, by rfl⟩ : syracuseStep 7271639 = 10907459) B10907459
theorem B1701107 : Blo 447780 1701107 := bstep (se 1 (by rfl) ⟨1275830, by rfl⟩ : syracuseStep 1701107 = 2551661) B2551661
theorem B1996019 : Blo 447780 1996019 := bstep (se 1 (by rfl) ⟨1497014, by rfl⟩ : syracuseStep 1996019 = 2994029) B2994029
theorem B1012985 : Blo 447780 1012985 := bstep (se 2 (by rfl) ⟨379869, by rfl⟩ : syracuseStep 1012985 = 759739) B759739
theorem B8189207 : Blo 447780 8189207 := bstep (se 1 (by rfl) ⟨6141905, by rfl⟩ : syracuseStep 8189207 = 12283811) B12283811
theorem B1013129 : Blo 447780 1013129 := bstep (se 2 (by rfl) ⟨379923, by rfl⟩ : syracuseStep 1013129 = 759847) B759847
theorem B1013255 : Blo 447780 1013255 := bstep (se 1 (by rfl) ⟨759941, by rfl⟩ : syracuseStep 1013255 = 1519883) B1519883
theorem B1013435 : Blo 447780 1013435 := bstep (se 1 (by rfl) ⟨760076, by rfl⟩ : syracuseStep 1013435 = 1520153) B1520153
theorem B1013561 : Blo 447780 1013561 := bstep (se 2 (by rfl) ⟨380085, by rfl⟩ : syracuseStep 1013561 = 760171) B760171
theorem B5142365 : Blo 447780 5142365 := bstep (se 3 (by rfl) ⟨964193, by rfl⟩ : syracuseStep 5142365 = 1928387) B1928387
theorem B1210621 : Blo 447780 1210621 := bstep (se 3 (by rfl) ⟨226991, by rfl⟩ : syracuseStep 1210621 = 453983) B453983
theorem B1014191 : Blo 447780 1014191 := bstep (se 1 (by rfl) ⟨760643, by rfl⟩ : syracuseStep 1014191 = 1521287) B1521287
theorem B1276343 : Blo 447780 1276343 := bstep (se 1 (by rfl) ⟨957257, by rfl⟩ : syracuseStep 1276343 = 1914515) B1914515
theorem B1014227 : Blo 447780 1014227 := bstep (se 1 (by rfl) ⟨760670, by rfl⟩ : syracuseStep 1014227 = 1521341) B1521341
theorem B1276411 : Blo 447780 1276411 := bstep (se 1 (by rfl) ⟨957308, by rfl⟩ : syracuseStep 1276411 = 1914617) B1914617
theorem B1014335 : Blo 447780 1014335 := bstep (se 1 (by rfl) ⟨760751, by rfl⟩ : syracuseStep 1014335 = 1521503) B1521503
theorem B6158987 : Blo 447780 6158987 := bstep (se 1 (by rfl) ⟨4619240, by rfl⟩ : syracuseStep 6158987 = 9238481) B9238481
theorem B1014443 : Blo 447780 1014443 := bstep (se 1 (by rfl) ⟨760832, by rfl⟩ : syracuseStep 1014443 = 1521665) B1521665
theorem B3635887 : Blo 447780 3635887 := bstep (se 1 (by rfl) ⟨2726915, by rfl⟩ : syracuseStep 3635887 = 5453831) B5453831
theorem B8616779 : Blo 447780 8616779 := bstep (se 1 (by rfl) ⟨6462584, by rfl⟩ : syracuseStep 8616779 = 12925169) B12925169
theorem B1440755 : Blo 447780 1440755 := bstep (se 1 (by rfl) ⟨1080566, by rfl⟩ : syracuseStep 1440755 = 2161133) B2161133
theorem B1703051 : Blo 447780 1703051 := bstep (se 1 (by rfl) ⟨1277288, by rfl⟩ : syracuseStep 1703051 = 2554577) B2554577
theorem B1277117 : Blo 447780 1277117 := bstep (se 3 (by rfl) ⟨239459, by rfl⟩ : syracuseStep 1277117 = 478919) B478919
theorem B1014983 : Blo 447780 1014983 := bstep (se 1 (by rfl) ⟨761237, by rfl⟩ : syracuseStep 1014983 = 1522475) B1522475
theorem B1015163 : Blo 447780 1015163 := bstep (se 1 (by rfl) ⟨761372, by rfl⟩ : syracuseStep 1015163 = 1522745) B1522745
theorem B10911149 : Blo 447780 10911149 := bstep (se 3 (by rfl) ⟨2045840, by rfl⟩ : syracuseStep 10911149 = 4091681) B4091681
theorem B1015289 : Blo 447780 1015289 := bstep (se 2 (by rfl) ⟨380733, by rfl⟩ : syracuseStep 1015289 = 761467) B761467
theorem B1015379 : Blo 447780 1015379 := bstep (se 1 (by rfl) ⟨761534, by rfl⟩ : syracuseStep 1015379 = 1523069) B1523069
theorem B24641171 : Blo 447780 24641171 := bstep (se 1 (by rfl) ⟨18480878, by rfl⟩ : syracuseStep 24641171 = 36961757) B36961757
theorem B1015559 : Blo 447780 1015559 := bstep (se 1 (by rfl) ⟨761669, by rfl⟩ : syracuseStep 1015559 = 1523339) B1523339
theorem B1015847 : Blo 447780 1015847 := bstep (se 1 (by rfl) ⟨761885, by rfl⟩ : syracuseStep 1015847 = 1523771) B1523771
theorem B21921941 : Blo 447780 21921941 := bstep (se 6 (by rfl) ⟨513795, by rfl⟩ : syracuseStep 21921941 = 1027591) B1027591
theorem B1016027 : Blo 447780 1016027 := bstep (se 1 (by rfl) ⟨762020, by rfl⟩ : syracuseStep 1016027 = 1524041) B1524041
theorem B10944827 : Blo 447780 10944827 := bstep (se 1 (by rfl) ⟨8208620, by rfl⟩ : syracuseStep 10944827 = 16417241) B16417241
theorem B1442281 : Blo 447780 1442281 := bstep (se 2 (by rfl) ⟨540855, by rfl⟩ : syracuseStep 1442281 = 1081711) B1081711
theorem B1016297 : Blo 447780 1016297 := bstep (se 2 (by rfl) ⟨381111, by rfl⟩ : syracuseStep 1016297 = 762223) B762223
theorem B2556467 : Blo 447780 2556467 := bstep (se 1 (by rfl) ⟨1917350, by rfl⟩ : syracuseStep 2556467 = 3834701) B3834701
theorem B2196233 : Blo 447780 2196233 := bstep (se 2 (by rfl) ⟨823587, by rfl⟩ : syracuseStep 2196233 = 1647175) B1647175
theorem B721705 : Blo 447780 721705 := bstep (se 2 (by rfl) ⟨270639, by rfl⟩ : syracuseStep 721705 = 541279) B541279
theorem B721915 : Blo 447780 721915 := bstep (se 1 (by rfl) ⟨541436, by rfl⟩ : syracuseStep 721915 = 1082873) B1082873
theorem B3900811 : Blo 447780 3900811 := bstep (se 1 (by rfl) ⟨2925608, by rfl⟩ : syracuseStep 3900811 = 5851217) B5851217
theorem B1705769 : Blo 447780 1705769 := bstep (se 2 (by rfl) ⟨639663, by rfl⟩ : syracuseStep 1705769 = 1279327) B1279327
theorem B2459591 : Blo 447780 2459591 := bstep (se 1 (by rfl) ⟨1844693, by rfl⟩ : syracuseStep 2459591 = 3689387) B3689387
theorem B21792725 : Blo 447780 21792725 := bstep (se 7 (by rfl) ⟨255383, by rfl⟩ : syracuseStep 21792725 = 510767) B510767
theorem B2557925 : Blo 447780 2557925 := bstep (se 4 (by rfl) ⟨239805, by rfl⟩ : syracuseStep 2557925 = 479611) B479611
theorem B722935 : Blo 447780 722935 := bstep (se 1 (by rfl) ⟨542201, by rfl⟩ : syracuseStep 722935 = 1084403) B1084403
theorem B1640573 : Blo 447780 1640573 := bstep (se 3 (by rfl) ⟨307607, by rfl⟩ : syracuseStep 1640573 = 615215) B615215
theorem B1280215 : Blo 447780 1280215 := bstep (se 1 (by rfl) ⟨960161, by rfl⟩ : syracuseStep 1280215 = 1920323) B1920323
theorem B2558951 : Blo 447780 2558951 := bstep (se 1 (by rfl) ⟨1919213, by rfl⟩ : syracuseStep 2558951 = 3838427) B3838427
theorem B756715 : Blo 447780 756715 := bstep (se 1 (by rfl) ⟨567536, by rfl⟩ : syracuseStep 756715 = 1135073) B1135073
theorem B756857 : Blo 447780 756857 := bstep (se 2 (by rfl) ⟨283821, by rfl⟩ : syracuseStep 756857 = 567643) B567643
theorem B1444985 : Blo 447780 1444985 := bstep (se 2 (by rfl) ⟨541869, by rfl⟩ : syracuseStep 1444985 = 1083739) B1083739
theorem B2198771 : Blo 447780 2198771 := bstep (se 1 (by rfl) ⟨1649078, by rfl⟩ : syracuseStep 2198771 = 3298157) B3298157
theorem B3411719 : Blo 447780 3411719 := bstep (se 1 (by rfl) ⟨2558789, by rfl⟩ : syracuseStep 3411719 = 5117579) B5117579
theorem B2920313 : Blo 447780 2920313 := bstep (se 2 (by rfl) ⟨1095117, by rfl⟩ : syracuseStep 2920313 = 2190235) B2190235
theorem B6492109 : Blo 447780 6492109 := bstep (se 3 (by rfl) ⟨1217270, by rfl⟩ : syracuseStep 6492109 = 2434541) B2434541
theorem B7671995 : Blo 447780 7671995 := bstep (se 1 (by rfl) ⟨5753996, by rfl⟩ : syracuseStep 7671995 = 11507993) B11507993
theorem B757991 : Blo 447780 757991 := bstep (se 1 (by rfl) ⟨568493, by rfl⟩ : syracuseStep 757991 = 1136987) B1136987
theorem B1282301 : Blo 447780 1282301 := bstep (se 3 (by rfl) ⟨240431, by rfl⟩ : syracuseStep 1282301 = 480863) B480863
theorem B758153 : Blo 447780 758153 := bstep (se 2 (by rfl) ⟨284307, by rfl⟩ : syracuseStep 758153 = 568615) B568615
theorem B1511891 : Blo 447780 1511891 := bstep (se 1 (by rfl) ⟨1133918, by rfl⟩ : syracuseStep 1511891 = 2267837) B2267837
theorem B5771735 : Blo 447780 5771735 := bstep (se 1 (by rfl) ⟨4328801, by rfl⟩ : syracuseStep 5771735 = 8657603) B8657603
theorem B2167283 : Blo 447780 2167283 := bstep (se 1 (by rfl) ⟨1625462, by rfl⟩ : syracuseStep 2167283 = 3250925) B3250925
theorem B758585 : Blo 447780 758585 := bstep (se 2 (by rfl) ⟨284469, by rfl⟩ : syracuseStep 758585 = 568939) B568939
theorem B758639 : Blo 447780 758639 := bstep (se 1 (by rfl) ⟨568979, by rfl⟩ : syracuseStep 758639 = 1137959) B1137959
theorem B2167823 : Blo 447780 2167823 := bstep (se 1 (by rfl) ⟨1625867, by rfl⟩ : syracuseStep 2167823 = 3251735) B3251735
theorem B1283359 : Blo 447780 1283359 := bstep (se 1 (by rfl) ⟨962519, by rfl⟩ : syracuseStep 1283359 = 1925039) B1925039
theorem B3249517 : Blo 447780 3249517 := bstep (se 3 (by rfl) ⟨609284, by rfl⟩ : syracuseStep 3249517 = 1218569) B1218569
theorem B1218017 : Blo 447780 1218017 := bstep (se 2 (by rfl) ⟨456756, by rfl⟩ : syracuseStep 1218017 = 913513) B913513
theorem B759631 : Blo 447780 759631 := bstep (se 1 (by rfl) ⟨569723, by rfl⟩ : syracuseStep 759631 = 1139447) B1139447
theorem B22124609 : Blo 447780 22124609 := bstep (se 2 (by rfl) ⟨8296728, by rfl⟩ : syracuseStep 22124609 = 16593457) B16593457
theorem B1218655 : Blo 447780 1218655 := bstep (se 1 (by rfl) ⟨913991, by rfl⟩ : syracuseStep 1218655 = 1827983) B1827983
theorem B760043 : Blo 447780 760043 := bstep (se 1 (by rfl) ⟨570032, by rfl⟩ : syracuseStep 760043 = 1140065) B1140065
theorem B1513835 : Blo 447780 1513835 := bstep (se 1 (by rfl) ⟨1135376, by rfl⟩ : syracuseStep 1513835 = 2270753) B2270753
theorem B1514105 : Blo 447780 1514105 := bstep (se 2 (by rfl) ⟨567789, by rfl⟩ : syracuseStep 1514105 = 1135579) B1135579
theorem B1284943 : Blo 447780 1284943 := bstep (se 1 (by rfl) ⟨963707, by rfl⟩ : syracuseStep 1284943 = 1927415) B1927415
theorem B1514537 : Blo 447780 1514537 := bstep (se 2 (by rfl) ⟨567951, by rfl⟩ : syracuseStep 1514537 = 1135903) B1135903
theorem B760873 : Blo 447780 760873 := bstep (se 2 (by rfl) ⟨285327, by rfl⟩ : syracuseStep 760873 = 570655) B570655
theorem B761015 : Blo 447780 761015 := bstep (se 1 (by rfl) ⟨570761, by rfl⟩ : syracuseStep 761015 = 1141523) B1141523
theorem B2563325 : Blo 447780 2563325 := bstep (se 3 (by rfl) ⟨480623, by rfl⟩ : syracuseStep 2563325 = 961247) B961247
theorem B2268647 : Blo 447780 2268647 := bstep (se 1 (by rfl) ⟨1701485, by rfl⟩ : syracuseStep 2268647 = 3402971) B3402971
theorem B761339 : Blo 447780 761339 := bstep (se 1 (by rfl) ⟨571004, by rfl⟩ : syracuseStep 761339 = 1142009) B1142009
theorem B6757967 : Blo 447780 6757967 := bstep (se 1 (by rfl) ⟨5068475, by rfl⟩ : syracuseStep 6757967 = 10136951) B10136951
theorem B958043 : Blo 447780 958043 := bstep (se 1 (by rfl) ⟨718532, by rfl⟩ : syracuseStep 958043 = 1437065) B1437065
theorem B1285865 : Blo 447780 1285865 := bstep (se 2 (by rfl) ⟨482199, by rfl⟩ : syracuseStep 1285865 = 964399) B964399
theorem B761771 : Blo 447780 761771 := bstep (se 1 (by rfl) ⟨571328, by rfl⟩ : syracuseStep 761771 = 1142657) B1142657
theorem B2957417 : Blo 447780 2957417 := bstep (se 2 (by rfl) ⟨1109031, by rfl⟩ : syracuseStep 2957417 = 2218063) B2218063
theorem B1614161 : Blo 447780 1614161 := bstep (se 2 (by rfl) ⟨605310, by rfl⟩ : syracuseStep 1614161 = 1210621) B1210621
theorem B5775731 : Blo 447780 5775731 := bstep (se 1 (by rfl) ⟨4331798, by rfl⟩ : syracuseStep 5775731 = 8663597) B8663597
theorem B3842423 : Blo 447780 3842423 := bstep (se 1 (by rfl) ⟨2881817, by rfl⟩ : syracuseStep 3842423 = 5763635) B5763635
theorem B762311 : Blo 447780 762311 := bstep (se 1 (by rfl) ⟨571733, by rfl⟩ : syracuseStep 762311 = 1143467) B1143467
theorem B1581935 : Blo 447780 1581935 := bstep (se 1 (by rfl) ⟨1186451, by rfl⟩ : syracuseStep 1581935 = 2372903) B2372903
theorem B1516751 : Blo 447780 1516751 := bstep (se 1 (by rfl) ⟨1137563, by rfl⟩ : syracuseStep 1516751 = 2275127) B2275127
theorem B22258921 : Blo 447780 22258921 := bstep (se 2 (by rfl) ⟨8347095, by rfl⟩ : syracuseStep 22258921 = 16694191) B16694191
theorem B1713545 : Blo 447780 1713545 := bstep (se 2 (by rfl) ⟨642579, by rfl⟩ : syracuseStep 1713545 = 1285159) B1285159
theorem B1517075 : Blo 447780 1517075 := bstep (se 1 (by rfl) ⟨1137806, by rfl⟩ : syracuseStep 1517075 = 2275613) B2275613
theorem B3090001 : Blo 447780 3090001 := bstep (se 2 (by rfl) ⟨1158750, by rfl⟩ : syracuseStep 3090001 = 2317501) B2317501
theorem B2565715 : Blo 447780 2565715 := bstep (se 1 (by rfl) ⟨1924286, by rfl⟩ : syracuseStep 2565715 = 3848573) B3848573
theorem B4105991 : Blo 447780 4105991 := bstep (se 1 (by rfl) ⟨3079493, by rfl⟩ : syracuseStep 4105991 = 6158987) B6158987
theorem B5744519 : Blo 447780 5744519 := bstep (se 1 (by rfl) ⟨4308389, by rfl⟩ : syracuseStep 5744519 = 8616779) B8616779
theorem B960503 : Blo 447780 960503 := bstep (se 1 (by rfl) ⟨720377, by rfl⟩ : syracuseStep 960503 = 1440755) B1440755
theorem B5187779 : Blo 447780 5187779 := bstep (se 1 (by rfl) ⟨3890834, by rfl⟩ : syracuseStep 5187779 = 7781669) B7781669
theorem B16427447 : Blo 447780 16427447 := bstep (se 1 (by rfl) ⟨12320585, by rfl⟩ : syracuseStep 16427447 = 24641171) B24641171
theorem B1714715 : Blo 447780 1714715 := bstep (se 1 (by rfl) ⟨1286036, by rfl⟩ : syracuseStep 1714715 = 2572073) B2572073
theorem B1518263 : Blo 447780 1518263 := bstep (se 1 (by rfl) ⟨1138697, by rfl⟩ : syracuseStep 1518263 = 2277395) B2277395
theorem B1027657 : Blo 447780 1027657 := bstep (se 2 (by rfl) ⟨385371, by rfl⟩ : syracuseStep 1027657 = 770743) B770743
theorem B37007117 : Blo 447780 37007117 := bstep (se 3 (by rfl) ⟨6938834, by rfl⟩ : syracuseStep 37007117 = 13877669) B13877669
theorem B17576099 : Blo 447780 17576099 := bstep (se 1 (by rfl) ⟨13182074, by rfl⟩ : syracuseStep 17576099 = 26364149) B26364149
theorem B6435073 : Blo 447780 6435073 := bstep (se 2 (by rfl) ⟨2413152, by rfl⟩ : syracuseStep 6435073 = 4826305) B4826305
theorem B1520207 : Blo 447780 1520207 := bstep (se 1 (by rfl) ⟨1140155, by rfl⟩ : syracuseStep 1520207 = 2280311) B2280311
theorem B11481749 : Blo 447780 11481749 := bstep (se 6 (by rfl) ⟨269103, by rfl⟩ : syracuseStep 11481749 = 538207) B538207
theorem B504895 : Blo 447780 504895 := bstep (se 1 (by rfl) ⟨378671, by rfl⟩ : syracuseStep 504895 = 757343) B757343
theorem B767083 : Blo 447780 767083 := bstep (se 1 (by rfl) ⟨575312, by rfl⟩ : syracuseStep 767083 = 1150625) B1150625
theorem B1520747 : Blo 447780 1520747 := bstep (se 1 (by rfl) ⟨1140560, by rfl⟩ : syracuseStep 1520747 = 2281121) B2281121
theorem B505039 : Blo 447780 505039 := bstep (se 1 (by rfl) ⟨378779, by rfl⟩ : syracuseStep 505039 = 757559) B757559
theorem B2570089 : Blo 447780 2570089 := bstep (se 2 (by rfl) ⟨963783, by rfl⟩ : syracuseStep 2570089 = 1927567) B1927567
theorem B1619927 : Blo 447780 1619927 := bstep (se 1 (by rfl) ⟨1214945, by rfl⟩ : syracuseStep 1619927 = 2429891) B2429891
theorem B866447 : Blo 447780 866447 := bstep (se 1 (by rfl) ⟨649835, by rfl⟩ : syracuseStep 866447 = 1299671) B1299671
theorem B506011 : Blo 447780 506011 := bstep (se 1 (by rfl) ⟨379508, by rfl⟩ : syracuseStep 506011 = 759017) B759017
theorem B506047 : Blo 447780 506047 := bstep (se 1 (by rfl) ⟨379535, by rfl⟩ : syracuseStep 506047 = 759071) B759071
theorem B571627 : Blo 447780 571627 := bstep (se 1 (by rfl) ⟨428720, by rfl⟩ : syracuseStep 571627 = 857441) B857441
theorem B6502771 : Blo 447780 6502771 := bstep (se 1 (by rfl) ⟨4877078, by rfl⟩ : syracuseStep 6502771 = 9754157) B9754157
theorem B1522043 : Blo 447780 1522043 := bstep (se 1 (by rfl) ⟨1141532, by rfl⟩ : syracuseStep 1522043 = 2283065) B2283065
theorem B1522313 : Blo 447780 1522313 := bstep (se 2 (by rfl) ⟨570867, by rfl⟩ : syracuseStep 1522313 = 1141735) B1141735
theorem B1293023 : Blo 447780 1293023 := bstep (se 1 (by rfl) ⟨969767, by rfl⟩ : syracuseStep 1293023 = 1939535) B1939535
theorem B7715735 : Blo 447780 7715735 := bstep (se 1 (by rfl) ⟨5786801, by rfl⟩ : syracuseStep 7715735 = 11573603) B11573603
theorem B2276423 : Blo 447780 2276423 := bstep (se 1 (by rfl) ⟨1707317, by rfl⟩ : syracuseStep 2276423 = 3414635) B3414635
theorem B2440487 : Blo 447780 2440487 := bstep (se 1 (by rfl) ⟨1830365, by rfl⟩ : syracuseStep 2440487 = 3660731) B3660731
theorem B1523447 : Blo 447780 1523447 := bstep (se 1 (by rfl) ⟨1142585, by rfl⟩ : syracuseStep 1523447 = 2285171) B2285171
theorem B671711 : Blo 447780 671711 := bstep (se 1 (by rfl) ⟨503783, by rfl⟩ : syracuseStep 671711 = 1007567) B1007567
theorem B671963 : Blo 447780 671963 := bstep (se 1 (by rfl) ⟨503972, by rfl⟩ : syracuseStep 671963 = 1007945) B1007945
theorem B671975 : Blo 447780 671975 := bstep (se 1 (by rfl) ⟨503981, by rfl⟩ : syracuseStep 671975 = 1007963) B1007963
theorem B508135 : Blo 447780 508135 := bstep (se 1 (by rfl) ⟨381101, by rfl⟩ : syracuseStep 508135 = 762203) B762203
theorem B672137 : Blo 447780 672137 := bstep (se 2 (by rfl) ⟨252051, by rfl⟩ : syracuseStep 672137 = 504103) B504103
theorem B672233 : Blo 447780 672233 := bstep (se 2 (by rfl) ⟨252087, by rfl⟩ : syracuseStep 672233 = 504175) B504175
theorem B672359 : Blo 447780 672359 := bstep (se 1 (by rfl) ⟨504269, by rfl⟩ : syracuseStep 672359 = 1008539) B1008539
theorem B672491 : Blo 447780 672491 := bstep (se 1 (by rfl) ⟨504368, by rfl⟩ : syracuseStep 672491 = 1008737) B1008737
theorem B672521 : Blo 447780 672521 := bstep (se 2 (by rfl) ⟨252195, by rfl⟩ : syracuseStep 672521 = 504391) B504391
theorem B1524527 : Blo 447780 1524527 := bstep (se 1 (by rfl) ⟨1143395, by rfl⟩ : syracuseStep 1524527 = 2286791) B2286791
theorem B672623 : Blo 447780 672623 := bstep (se 1 (by rfl) ⟨504467, by rfl⟩ : syracuseStep 672623 = 1008935) B1008935
theorem B1524635 : Blo 447780 1524635 := bstep (se 1 (by rfl) ⟨1143476, by rfl⟩ : syracuseStep 1524635 = 2286953) B2286953
theorem B1917863 : Blo 447780 1917863 := bstep (se 1 (by rfl) ⟨1438397, by rfl⟩ : syracuseStep 1917863 = 2876795) B2876795
theorem B2081747 : Blo 447780 2081747 := bstep (se 1 (by rfl) ⟨1561310, by rfl⟩ : syracuseStep 2081747 = 3122621) B3122621
theorem B3064823 : Blo 447780 3064823 := bstep (se 1 (by rfl) ⟨2298617, by rfl⟩ : syracuseStep 3064823 = 4597235) B4597235
theorem B672875 : Blo 447780 672875 := bstep (se 1 (by rfl) ⟨504656, by rfl⟩ : syracuseStep 672875 = 1009313) B1009313
theorem B673115 : Blo 447780 673115 := bstep (se 1 (by rfl) ⟨504836, by rfl⟩ : syracuseStep 673115 = 1009673) B1009673
theorem B13157741 : Blo 447780 13157741 := bstep (se 3 (by rfl) ⟨2467076, by rfl⟩ : syracuseStep 13157741 = 4934153) B4934153
theorem B673391 : Blo 447780 673391 := bstep (se 1 (by rfl) ⟨505043, by rfl⟩ : syracuseStep 673391 = 1010087) B1010087
theorem B673463 : Blo 447780 673463 := bstep (se 1 (by rfl) ⟨505097, by rfl⟩ : syracuseStep 673463 = 1010195) B1010195
theorem B673499 : Blo 447780 673499 := bstep (se 1 (by rfl) ⟨505124, by rfl⟩ : syracuseStep 673499 = 1010249) B1010249
theorem B673673 : Blo 447780 673673 := bstep (se 2 (by rfl) ⟨252627, by rfl⟩ : syracuseStep 673673 = 505255) B505255
theorem B673775 : Blo 447780 673775 := bstep (se 1 (by rfl) ⟨505331, by rfl⟩ : syracuseStep 673775 = 1010663) B1010663
theorem B674027 : Blo 447780 674027 := bstep (se 1 (by rfl) ⟨505520, by rfl⟩ : syracuseStep 674027 = 1011041) B1011041
theorem B674087 : Blo 447780 674087 := bstep (se 1 (by rfl) ⟨505565, by rfl⟩ : syracuseStep 674087 = 1011131) B1011131
theorem B674171 : Blo 447780 674171 := bstep (se 1 (by rfl) ⟨505628, by rfl⟩ : syracuseStep 674171 = 1011257) B1011257
theorem B674441 : Blo 447780 674441 := bstep (se 2 (by rfl) ⟨252915, by rfl⟩ : syracuseStep 674441 = 505831) B505831
theorem B674615 : Blo 447780 674615 := bstep (se 1 (by rfl) ⟨505961, by rfl⟩ : syracuseStep 674615 = 1011923) B1011923
theorem B674651 : Blo 447780 674651 := bstep (se 1 (by rfl) ⟨505988, by rfl⟩ : syracuseStep 674651 = 1011977) B1011977
theorem B674795 : Blo 447780 674795 := bstep (se 1 (by rfl) ⟨506096, by rfl⟩ : syracuseStep 674795 = 1012193) B1012193
theorem B1133615 : Blo 447780 1133615 := bstep (se 1 (by rfl) ⟨850211, by rfl⟩ : syracuseStep 1133615 = 1700423) B1700423
theorem B674999 : Blo 447780 674999 := bstep (se 1 (by rfl) ⟨506249, by rfl⟩ : syracuseStep 674999 = 1012499) B1012499
theorem B675239 : Blo 447780 675239 := bstep (se 1 (by rfl) ⟨506429, by rfl⟩ : syracuseStep 675239 = 1012859) B1012859
theorem B1134071 : Blo 447780 1134071 := bstep (se 1 (by rfl) ⟨850553, by rfl⟩ : syracuseStep 1134071 = 1701107) B1701107
theorem B1330679 : Blo 447780 1330679 := bstep (se 1 (by rfl) ⟨998009, by rfl⟩ : syracuseStep 1330679 = 1996019) B1996019
theorem B675323 : Blo 447780 675323 := bstep (se 1 (by rfl) ⟨506492, by rfl⟩ : syracuseStep 675323 = 1012985) B1012985
theorem B5459471 : Blo 447780 5459471 := bstep (se 1 (by rfl) ⟨4094603, by rfl⟩ : syracuseStep 5459471 = 8189207) B8189207
theorem B675419 : Blo 447780 675419 := bstep (se 1 (by rfl) ⟨506564, by rfl⟩ : syracuseStep 675419 = 1013129) B1013129
theorem B1298045 : Blo 447780 1298045 := bstep (se 3 (by rfl) ⟨243383, by rfl⟩ : syracuseStep 1298045 = 486767) B486767
theorem B675503 : Blo 447780 675503 := bstep (se 1 (by rfl) ⟨506627, by rfl⟩ : syracuseStep 675503 = 1013255) B1013255
theorem B675623 : Blo 447780 675623 := bstep (se 1 (by rfl) ⟨506717, by rfl⟩ : syracuseStep 675623 = 1013435) B1013435
theorem B675707 : Blo 447780 675707 := bstep (se 1 (by rfl) ⟨506780, by rfl⟩ : syracuseStep 675707 = 1013561) B1013561
theorem B3428243 : Blo 447780 3428243 := bstep (se 1 (by rfl) ⟨2571182, by rfl⟩ : syracuseStep 3428243 = 5142365) B5142365
theorem B676127 : Blo 447780 676127 := bstep (se 1 (by rfl) ⟨507095, by rfl⟩ : syracuseStep 676127 = 1014191) B1014191
theorem B676151 : Blo 447780 676151 := bstep (se 1 (by rfl) ⟨507113, by rfl⟩ : syracuseStep 676151 = 1014227) B1014227
theorem B676223 : Blo 447780 676223 := bstep (se 1 (by rfl) ⟨507167, by rfl⟩ : syracuseStep 676223 = 1014335) B1014335
theorem B676295 : Blo 447780 676295 := bstep (se 1 (by rfl) ⟨507221, by rfl⟩ : syracuseStep 676295 = 1014443) B1014443
theorem B2740807 : Blo 447780 2740807 := bstep (se 1 (by rfl) ⟨2055605, by rfl⟩ : syracuseStep 2740807 = 4111211) B4111211
theorem B1823327 : Blo 447780 1823327 := bstep (se 1 (by rfl) ⟨1367495, by rfl⟩ : syracuseStep 1823327 = 2734991) B2734991
theorem B1135367 : Blo 447780 1135367 := bstep (se 1 (by rfl) ⟨851525, by rfl⟩ : syracuseStep 1135367 = 1703051) B1703051
theorem B676649 : Blo 447780 676649 := bstep (se 2 (by rfl) ⟨253743, by rfl⟩ : syracuseStep 676649 = 507487) B507487
theorem B676655 : Blo 447780 676655 := bstep (se 1 (by rfl) ⟨507491, by rfl⟩ : syracuseStep 676655 = 1014983) B1014983
theorem B676775 : Blo 447780 676775 := bstep (se 1 (by rfl) ⟨507581, by rfl⟩ : syracuseStep 676775 = 1015163) B1015163
theorem B676859 : Blo 447780 676859 := bstep (se 1 (by rfl) ⟨507644, by rfl⟩ : syracuseStep 676859 = 1015289) B1015289
theorem B676919 : Blo 447780 676919 := bstep (se 1 (by rfl) ⟨507689, by rfl⟩ : syracuseStep 676919 = 1015379) B1015379
theorem B677039 : Blo 447780 677039 := bstep (se 1 (by rfl) ⟨507779, by rfl⟩ : syracuseStep 677039 = 1015559) B1015559
theorem B447899 : Blo 447780 447899 := bstep (se 1 (by rfl) ⟨335924, by rfl⟩ : syracuseStep 447899 = 671849) B671849
theorem B3462587 : Blo 447780 3462587 := bstep (se 1 (by rfl) ⟨2596940, by rfl⟩ : syracuseStep 3462587 = 5193881) B5193881
theorem B677447 : Blo 447780 677447 := bstep (se 1 (by rfl) ⟨508085, by rfl⟩ : syracuseStep 677447 = 1016171) B1016171
theorem B5461613 : Blo 447780 5461613 := bstep (se 3 (by rfl) ⟨1024052, by rfl⟩ : syracuseStep 5461613 = 2048105) B2048105
theorem B1824365 : Blo 447780 1824365 := bstep (se 3 (by rfl) ⟨342068, by rfl⟩ : syracuseStep 1824365 = 684137) B684137
theorem B448111 : Blo 447780 448111 := bstep (se 1 (by rfl) ⟨336083, by rfl⟩ : syracuseStep 448111 = 672167) B672167
theorem B448167 : Blo 447780 448167 := bstep (se 1 (by rfl) ⟨336125, by rfl⟩ : syracuseStep 448167 = 672251) B672251
theorem B480935 : Blo 447780 480935 := bstep (se 1 (by rfl) ⟨360701, by rfl⟩ : syracuseStep 480935 = 721403) B721403
theorem B677543 : Blo 447780 677543 := bstep (se 1 (by rfl) ⟨508157, by rfl⟩ : syracuseStep 677543 = 1016315) B1016315
theorem B53106353 : Blo 447780 53106353 := bstep (se 2 (by rfl) ⟨19914882, by rfl⟩ : syracuseStep 53106353 = 39829765) B39829765
theorem B448251 : Blo 447780 448251 := bstep (se 1 (by rfl) ⟨336188, by rfl⟩ : syracuseStep 448251 = 672377) B672377
theorem B677627 : Blo 447780 677627 := bstep (se 1 (by rfl) ⟨508220, by rfl⟩ : syracuseStep 677627 = 1016441) B1016441
theorem B448287 : Blo 447780 448287 := bstep (se 1 (by rfl) ⟨336215, by rfl⟩ : syracuseStep 448287 = 672431) B672431
theorem B677663 : Blo 447780 677663 := bstep (se 1 (by rfl) ⟨508247, by rfl⟩ : syracuseStep 677663 = 1016495) B1016495
theorem B448319 : Blo 447780 448319 := bstep (se 1 (by rfl) ⟨336239, by rfl⟩ : syracuseStep 448319 = 672479) B672479
theorem B448495 : Blo 447780 448495 := bstep (se 1 (by rfl) ⟨336371, by rfl⟩ : syracuseStep 448495 = 672743) B672743
theorem B448667 : Blo 447780 448667 := bstep (se 1 (by rfl) ⟨336500, by rfl⟩ : syracuseStep 448667 = 673001) B673001
theorem B448703 : Blo 447780 448703 := bstep (se 1 (by rfl) ⟨336527, by rfl⟩ : syracuseStep 448703 = 673055) B673055
theorem B448815 : Blo 447780 448815 := bstep (se 1 (by rfl) ⟨336611, by rfl⟩ : syracuseStep 448815 = 673223) B673223
theorem B449051 : Blo 447780 449051 := bstep (se 1 (by rfl) ⟨336788, by rfl⟩ : syracuseStep 449051 = 673577) B673577
theorem B449055 : Blo 447780 449055 := bstep (se 1 (by rfl) ⟨336791, by rfl⟩ : syracuseStep 449055 = 673583) B673583
theorem B449371 : Blo 447780 449371 := bstep (se 1 (by rfl) ⟨337028, by rfl⟩ : syracuseStep 449371 = 674057) B674057
theorem B449439 : Blo 447780 449439 := bstep (se 1 (by rfl) ⟨337079, by rfl⟩ : syracuseStep 449439 = 674159) B674159
theorem B449583 : Blo 447780 449583 := bstep (se 1 (by rfl) ⟨337187, by rfl⟩ : syracuseStep 449583 = 674375) B674375
theorem B449607 : Blo 447780 449607 := bstep (se 1 (by rfl) ⟨337205, by rfl⟩ : syracuseStep 449607 = 674411) B674411
theorem B1137847 : Blo 447780 1137847 := bstep (se 1 (by rfl) ⟨853385, by rfl⟩ : syracuseStep 1137847 = 1706771) B1706771
theorem B1465559 : Blo 447780 1465559 := bstep (se 1 (by rfl) ⟨1099169, by rfl⟩ : syracuseStep 1465559 = 2198339) B2198339
theorem B449759 : Blo 447780 449759 := bstep (se 1 (by rfl) ⟨337319, by rfl⟩ : syracuseStep 449759 = 674639) B674639
theorem B1727905 : Blo 447780 1727905 := bstep (se 2 (by rfl) ⟨647964, by rfl⟩ : syracuseStep 1727905 = 1295929) B1295929
theorem B1138151 : Blo 447780 1138151 := bstep (se 1 (by rfl) ⟨853613, by rfl⟩ : syracuseStep 1138151 = 1707227) B1707227
theorem B450023 : Blo 447780 450023 := bstep (se 1 (by rfl) ⟨337517, by rfl⟩ : syracuseStep 450023 = 675035) B675035
theorem B450139 : Blo 447780 450139 := bstep (se 1 (by rfl) ⟨337604, by rfl⟩ : syracuseStep 450139 = 675209) B675209
theorem B810823 : Blo 447780 810823 := bstep (se 1 (by rfl) ⟨608117, by rfl⟩ : syracuseStep 810823 = 1216235) B1216235
theorem B450375 : Blo 447780 450375 := bstep (se 1 (by rfl) ⟨337781, by rfl⟩ : syracuseStep 450375 = 675563) B675563
theorem B1007531 : Blo 447780 1007531 := bstep (se 1 (by rfl) ⟨755648, by rfl⟩ : syracuseStep 1007531 = 1511297) B1511297
theorem B450527 : Blo 447780 450527 := bstep (se 1 (by rfl) ⟨337895, by rfl⟩ : syracuseStep 450527 = 675791) B675791
theorem B1728647 : Blo 447780 1728647 := bstep (se 1 (by rfl) ⟨1296485, by rfl⟩ : syracuseStep 1728647 = 2592971) B2592971
theorem B450791 : Blo 447780 450791 := bstep (se 1 (by rfl) ⟨338093, by rfl⟩ : syracuseStep 450791 = 676187) B676187
theorem B450943 : Blo 447780 450943 := bstep (se 1 (by rfl) ⟨338207, by rfl⟩ : syracuseStep 450943 = 676415) B676415
theorem B1008071 : Blo 447780 1008071 := bstep (se 1 (by rfl) ⟨756053, by rfl⟩ : syracuseStep 1008071 = 1512107) B1512107
theorem B1139143 : Blo 447780 1139143 := bstep (se 1 (by rfl) ⟨854357, by rfl⟩ : syracuseStep 1139143 = 1708715) B1708715
theorem B909775 : Blo 447780 909775 := bstep (se 1 (by rfl) ⟨682331, by rfl⟩ : syracuseStep 909775 = 1364663) B1364663
theorem B451023 : Blo 447780 451023 := bstep (se 1 (by rfl) ⟨338267, by rfl⟩ : syracuseStep 451023 = 676535) B676535
theorem B451175 : Blo 447780 451175 := bstep (se 1 (by rfl) ⟨338381, by rfl⟩ : syracuseStep 451175 = 676763) B676763
theorem B1008431 : Blo 447780 1008431 := bstep (se 1 (by rfl) ⟨756323, by rfl⟩ : syracuseStep 1008431 = 1512647) B1512647
theorem B451439 : Blo 447780 451439 := bstep (se 1 (by rfl) ⟨338579, by rfl⟩ : syracuseStep 451439 = 677159) B677159
theorem B451495 : Blo 447780 451495 := bstep (se 1 (by rfl) ⟨338621, by rfl⟩ : syracuseStep 451495 = 677243) B677243
theorem B451579 : Blo 447780 451579 := bstep (se 1 (by rfl) ⟨338684, by rfl⟩ : syracuseStep 451579 = 677369) B677369
theorem B451647 : Blo 447780 451647 := bstep (se 1 (by rfl) ⟨338735, by rfl⟩ : syracuseStep 451647 = 677471) B677471
theorem B812207 : Blo 447780 812207 := bstep (se 1 (by rfl) ⟨609155, by rfl⟩ : syracuseStep 812207 = 1218311) B1218311
theorem B2156291 : Blo 447780 2156291 := bstep (se 1 (by rfl) ⟨1617218, by rfl⟩ : syracuseStep 2156291 = 3234437) B3234437
theorem B1009439 : Blo 447780 1009439 := bstep (se 1 (by rfl) ⟨757079, by rfl⟩ : syracuseStep 1009439 = 1514159) B1514159
theorem B649039 : Blo 447780 649039 := bstep (se 1 (by rfl) ⟨486779, by rfl⟩ : syracuseStep 649039 = 973559) B973559
theorem B1009655 : Blo 447780 1009655 := bstep (se 1 (by rfl) ⟨757241, by rfl⟩ : syracuseStep 1009655 = 1514483) B1514483
theorem B813359 : Blo 447780 813359 := bstep (se 1 (by rfl) ⟨610019, by rfl⟩ : syracuseStep 813359 = 1220039) B1220039
theorem B43379003 : Blo 447780 43379003 := bstep (se 1 (by rfl) ⟨32534252, by rfl⟩ : syracuseStep 43379003 = 65068505) B65068505
theorem B1010015 : Blo 447780 1010015 := bstep (se 1 (by rfl) ⟨757511, by rfl⟩ : syracuseStep 1010015 = 1515023) B1515023
theorem B1141087 : Blo 447780 1141087 := bstep (se 1 (by rfl) ⟨855815, by rfl⟩ : syracuseStep 1141087 = 1711631) B1711631
theorem B14805605 : Blo 447780 14805605 := bstep (se 4 (by rfl) ⟨1388025, by rfl⟩ : syracuseStep 14805605 = 2776051) B2776051
theorem B1010735 : Blo 447780 1010735 := bstep (se 1 (by rfl) ⟨758051, by rfl⟩ : syracuseStep 1010735 = 1516103) B1516103
theorem B1535257 : Blo 447780 1535257 := bstep (se 2 (by rfl) ⟨575721, by rfl⟩ : syracuseStep 1535257 = 1151443) B1151443
theorem B1011023 : Blo 447780 1011023 := bstep (se 1 (by rfl) ⟨758267, by rfl⟩ : syracuseStep 1011023 = 1516535) B1516535
theorem B1011113 : Blo 447780 1011113 := bstep (se 2 (by rfl) ⟨379167, by rfl⟩ : syracuseStep 1011113 = 758335) B758335
theorem B21884579 : Blo 447780 21884579 := bstep (se 1 (by rfl) ⟨16413434, by rfl⟩ : syracuseStep 21884579 = 32826869) B32826869
theorem B22409095 : Blo 447780 22409095 := bstep (se 1 (by rfl) ⟨16806821, by rfl⟩ : syracuseStep 22409095 = 33613643) B33613643
theorem B1011599 : Blo 447780 1011599 := bstep (se 1 (by rfl) ⟨758699, by rfl⟩ : syracuseStep 1011599 = 1517399) B1517399
theorem B2158559 : Blo 447780 2158559 := bstep (se 1 (by rfl) ⟨1618919, by rfl⟩ : syracuseStep 2158559 = 3237839) B3237839
theorem B2552093 : Blo 447780 2552093 := bstep (se 3 (by rfl) ⟨478517, by rfl⟩ : syracuseStep 2552093 = 957035) B957035
theorem B2158903 : Blo 447780 2158903 := bstep (se 1 (by rfl) ⟨1619177, by rfl⟩ : syracuseStep 2158903 = 3238355) B3238355
theorem B26276183 : Blo 447780 26276183 := bstep (se 1 (by rfl) ⟨19707137, by rfl⟩ : syracuseStep 26276183 = 39414275) B39414275
theorem B2191865 : Blo 447780 2191865 := bstep (se 2 (by rfl) ⟨821949, by rfl⟩ : syracuseStep 2191865 = 1643899) B1643899
theorem B1012319 : Blo 447780 1012319 := bstep (se 1 (by rfl) ⟨759239, by rfl⟩ : syracuseStep 1012319 = 1518479) B1518479
theorem B3404915 : Blo 447780 3404915 := bstep (se 1 (by rfl) ⟨2553686, by rfl⟩ : syracuseStep 3404915 = 5107373) B5107373
theorem B1438859 : Blo 447780 1438859 := bstep (se 1 (by rfl) ⟨1079144, by rfl⟩ : syracuseStep 1438859 = 2158289) B2158289
theorem B1275227 : Blo 447780 1275227 := bstep (se 1 (by rfl) ⟨956420, by rfl⟩ : syracuseStep 1275227 = 1912841) B1912841
theorem B685403 : Blo 447780 685403 := bstep (se 1 (by rfl) ⟨514052, by rfl⟩ : syracuseStep 685403 = 1028105) B1028105
theorem B1013147 : Blo 447780 1013147 := bstep (se 1 (by rfl) ⟨759860, by rfl⟩ : syracuseStep 1013147 = 1519721) B1519721
theorem B1013723 : Blo 447780 1013723 := bstep (se 1 (by rfl) ⟨760292, by rfl⟩ : syracuseStep 1013723 = 1520585) B1520585
theorem B1275887 : Blo 447780 1275887 := bstep (se 1 (by rfl) ⟨956915, by rfl⟩ : syracuseStep 1275887 = 1913831) B1913831
theorem B1701881 : Blo 447780 1701881 := bstep (se 2 (by rfl) ⟨638205, by rfl⟩ : syracuseStep 1701881 = 1276411) B1276411
theorem B4847759 : Blo 447780 4847759 := bstep (se 1 (by rfl) ⟨3635819, by rfl⟩ : syracuseStep 4847759 = 7271639) B7271639
theorem B1013903 : Blo 447780 1013903 := bstep (se 1 (by rfl) ⟨760427, by rfl⟩ : syracuseStep 1013903 = 1520855) B1520855
theorem B1013921 : Blo 447780 1013921 := bstep (se 2 (by rfl) ⟨380220, by rfl⟩ : syracuseStep 1013921 = 760441) B760441
theorem B4847849 : Blo 447780 4847849 := bstep (se 2 (by rfl) ⟨1817943, by rfl⟩ : syracuseStep 4847849 = 3635887) B3635887
theorem B1013993 : Blo 447780 1013993 := bstep (se 2 (by rfl) ⟨380247, by rfl⟩ : syracuseStep 1013993 = 760495) B760495
theorem B850895 : Blo 447780 850895 := bstep (se 1 (by rfl) ⟨638171, by rfl⟩ : syracuseStep 850895 = 1276343) B1276343
theorem B2555009 : Blo 447780 2555009 := bstep (se 2 (by rfl) ⟨958128, by rfl⟩ : syracuseStep 2555009 = 1916257) B1916257
theorem B10976543 : Blo 447780 10976543 := bstep (se 1 (by rfl) ⟨8232407, by rfl⟩ : syracuseStep 10976543 = 16464815) B16464815
theorem B1277345 : Blo 447780 1277345 := bstep (se 2 (by rfl) ⟨479004, by rfl⟩ : syracuseStep 1277345 = 958009) B958009
theorem B851411 : Blo 447780 851411 := bstep (se 1 (by rfl) ⟨638558, by rfl⟩ : syracuseStep 851411 = 1277117) B1277117
theorem B1015271 : Blo 447780 1015271 := bstep (se 1 (by rfl) ⟨761453, by rfl⟩ : syracuseStep 1015271 = 1522907) B1522907
theorem B7274099 : Blo 447780 7274099 := bstep (se 1 (by rfl) ⟨5455574, by rfl⟩ : syracuseStep 7274099 = 10911149) B10911149
theorem B1277687 : Blo 447780 1277687 := bstep (se 1 (by rfl) ⟨958265, by rfl⟩ : syracuseStep 1277687 = 1916531) B1916531
theorem B1081259 : Blo 447780 1081259 := bstep (se 1 (by rfl) ⟨810944, by rfl⟩ : syracuseStep 1081259 = 1621889) B1621889
theorem B1704311 : Blo 447780 1704311 := bstep (se 1 (by rfl) ⟨1278233, by rfl⟩ : syracuseStep 1704311 = 2556467) B2556467
theorem B58458509 : Blo 447780 58458509 := bstep (se 3 (by rfl) ⟨10960970, by rfl⟩ : syracuseStep 58458509 = 21921941) B21921941
theorem B1016351 : Blo 447780 1016351 := bstep (se 1 (by rfl) ⟨762263, by rfl⟩ : syracuseStep 1016351 = 1524527) B1524527
theorem B1016423 : Blo 447780 1016423 := bstep (se 1 (by rfl) ⟨762317, by rfl⟩ : syracuseStep 1016423 = 1524635) B1524635
theorem B1278575 : Blo 447780 1278575 := bstep (se 1 (by rfl) ⟨958931, by rfl⟩ : syracuseStep 1278575 = 1917863) B1917863
theorem B1639727 : Blo 447780 1639727 := bstep (se 1 (by rfl) ⟨1229795, by rfl⟩ : syracuseStep 1639727 = 2459591) B2459591
theorem B1705283 : Blo 447780 1705283 := bstep (se 1 (by rfl) ⟨1278962, by rfl⟩ : syracuseStep 1705283 = 2557925) B2557925
theorem B1705967 : Blo 447780 1705967 := bstep (se 1 (by rfl) ⟨1279475, by rfl⟩ : syracuseStep 1705967 = 2558951) B2558951
theorem B755743 : Blo 447780 755743 := bstep (se 1 (by rfl) ⟨566807, by rfl⟩ : syracuseStep 755743 = 1133615) B1133615
theorem B756047 : Blo 447780 756047 := bstep (se 1 (by rfl) ⟨567035, by rfl⟩ : syracuseStep 756047 = 1134071) B1134071
theorem B887119 : Blo 447780 887119 := bstep (se 1 (by rfl) ⟨665339, by rfl⟩ : syracuseStep 887119 = 1330679) B1330679
theorem B3639647 : Blo 447780 3639647 := bstep (se 1 (by rfl) ⟨2729735, by rfl⟩ : syracuseStep 3639647 = 5459471) B5459471
theorem B4852133 : Blo 447780 4852133 := bstep (se 4 (by rfl) ⟨454887, by rfl⟩ : syracuseStep 4852133 = 909775) B909775
theorem B5114663 : Blo 447780 5114663 := bstep (se 1 (by rfl) ⟨3835997, by rfl⟩ : syracuseStep 5114663 = 7671995) B7671995
theorem B854867 : Blo 447780 854867 := bstep (se 1 (by rfl) ⟨641150, by rfl⟩ : syracuseStep 854867 = 1282301) B1282301
theorem B1706953 : Blo 447780 1706953 := bstep (se 2 (by rfl) ⟨640107, by rfl⟩ : syracuseStep 1706953 = 1280215) B1280215
theorem B1215551 : Blo 447780 1215551 := bstep (se 1 (by rfl) ⟨911663, by rfl⟩ : syracuseStep 1215551 = 1823327) B1823327
theorem B756911 : Blo 447780 756911 := bstep (se 1 (by rfl) ⟨567683, by rfl⟩ : syracuseStep 756911 = 1135367) B1135367
theorem B1445215 : Blo 447780 1445215 := bstep (se 1 (by rfl) ⟨1083911, by rfl⟩ : syracuseStep 1445215 = 2167823) B2167823
theorem B3641075 : Blo 447780 3641075 := bstep (se 1 (by rfl) ⟨2730806, by rfl⟩ : syracuseStep 3641075 = 5461613) B5461613
theorem B1216243 : Blo 447780 1216243 := bstep (se 1 (by rfl) ⟨912182, by rfl⟩ : syracuseStep 1216243 = 1824365) B1824365
theorem B3248045 : Blo 447780 3248045 := bstep (se 3 (by rfl) ⟨609008, by rfl⟩ : syracuseStep 3248045 = 1218017) B1218017
theorem B14749739 : Blo 447780 14749739 := bstep (se 1 (by rfl) ⟨11062304, by rfl⟩ : syracuseStep 14749739 = 22124609) B22124609
theorem B1282493 : Blo 447780 1282493 := bstep (se 3 (by rfl) ⟨240467, by rfl⟩ : syracuseStep 1282493 = 480935) B480935
theorem B1708883 : Blo 447780 1708883 := bstep (se 1 (by rfl) ⟨1281662, by rfl⟩ : syracuseStep 1708883 = 2563325) B2563325
theorem B1512431 : Blo 447780 1512431 := bstep (se 1 (by rfl) ⟨1134323, by rfl⟩ : syracuseStep 1512431 = 2268647) B2268647
theorem B758767 : Blo 447780 758767 := bstep (se 1 (by rfl) ⟨569075, by rfl⟩ : syracuseStep 758767 = 1138151) B1138151
theorem B857243 : Blo 447780 857243 := bstep (se 1 (by rfl) ⟨642932, by rfl⟩ : syracuseStep 857243 = 1285865) B1285865
theorem B8656145 : Blo 447780 8656145 := bstep (se 2 (by rfl) ⟨3246054, by rfl⟩ : syracuseStep 8656145 = 6492109) B6492109
theorem B2561341 : Blo 447780 2561341 := bstep (se 3 (by rfl) ⟨480251, by rfl⟩ : syracuseStep 2561341 = 960503) B960503
theorem B1971611 : Blo 447780 1971611 := bstep (se 1 (by rfl) ⟨1478708, by rfl⟩ : syracuseStep 1971611 = 2957417) B2957417
theorem B1152431 : Blo 447780 1152431 := bstep (se 1 (by rfl) ⟨864323, by rfl⟩ : syracuseStep 1152431 = 1728647) B1728647
theorem B2561615 : Blo 447780 2561615 := bstep (se 1 (by rfl) ⟨1921211, by rfl⟩ : syracuseStep 2561615 = 3842423) B3842423
theorem B2168957 : Blo 447780 2168957 := bstep (se 3 (by rfl) ⟨406679, by rfl⟩ : syracuseStep 2168957 = 813359) B813359
theorem B115677341 : Blo 447780 115677341 := bstep (se 3 (by rfl) ⟨21689501, by rfl⟩ : syracuseStep 115677341 = 43379003) B43379003
theorem B1022777 : Blo 447780 1022777 := bstep (se 2 (by rfl) ⟨383541, by rfl⟩ : syracuseStep 1022777 = 767083) B767083
theorem B10951631 : Blo 447780 10951631 := bstep (se 1 (by rfl) ⟨8213723, by rfl⟩ : syracuseStep 10951631 = 16427447) B16427447
theorem B1711145 : Blo 447780 1711145 := bstep (se 2 (by rfl) ⟨641679, by rfl⟩ : syracuseStep 1711145 = 1283359) B1283359
theorem B9870403 : Blo 447780 9870403 := bstep (se 1 (by rfl) ⟨7402802, by rfl⟩ : syracuseStep 9870403 = 14805605) B14805605
theorem B4332689 : Blo 447780 4332689 := bstep (se 2 (by rfl) ⟨1624758, by rfl⟩ : syracuseStep 4332689 = 3249517) B3249517
theorem B14589719 : Blo 447780 14589719 := bstep (se 1 (by rfl) ⟨10942289, by rfl⟩ : syracuseStep 14589719 = 21884579) B21884579
theorem B762169 : Blo 447780 762169 := bstep (se 2 (by rfl) ⟨285813, by rfl⟩ : syracuseStep 762169 = 571627) B571627
theorem B2269943 : Blo 447780 2269943 := bstep (se 1 (by rfl) ⟨1702457, by rfl⟩ : syracuseStep 2269943 = 3404915) B3404915
theorem B959239 : Blo 447780 959239 := bstep (se 1 (by rfl) ⟨719429, by rfl⟩ : syracuseStep 959239 = 1438859) B1438859
theorem B1713257 : Blo 447780 1713257 := bstep (se 2 (by rfl) ⟨642471, by rfl⟩ : syracuseStep 1713257 = 1284943) B1284943
theorem B2270429 : Blo 447780 2270429 := bstep (se 3 (by rfl) ⟨425705, by rfl⟩ : syracuseStep 2270429 = 851411) B851411
theorem B1517129 : Blo 447780 1517129 := bstep (se 2 (by rfl) ⟨568923, by rfl⟩ : syracuseStep 1517129 = 1137847) B1137847
theorem B862015 : Blo 447780 862015 := bstep (se 1 (by rfl) ⟨646511, by rfl⟩ : syracuseStep 862015 = 1293023) B1293023
theorem B2303873 : Blo 447780 2303873 := bstep (se 2 (by rfl) ⟨863952, by rfl⟩ : syracuseStep 2303873 = 1727905) B1727905
theorem B567263 : Blo 447780 567263 := bstep (se 1 (by rfl) ⟨425447, by rfl⟩ : syracuseStep 567263 = 850895) B850895
theorem B1517615 : Blo 447780 1517615 := bstep (se 1 (by rfl) ⟨1138211, by rfl⟩ : syracuseStep 1517615 = 2276423) B2276423
theorem B7317695 : Blo 447780 7317695 := bstep (se 1 (by rfl) ⟨5488271, by rfl⟩ : syracuseStep 7317695 = 10976543) B10976543
theorem B1518857 : Blo 447780 1518857 := bstep (se 2 (by rfl) ⟨569571, by rfl⟩ : syracuseStep 1518857 = 1139143) B1139143
theorem B2043215 : Blo 447780 2043215 := bstep (se 1 (by rfl) ⟨1532411, by rfl⟩ : syracuseStep 2043215 = 3064823) B3064823
theorem B962273 : Blo 447780 962273 := bstep (se 2 (by rfl) ⟨360852, by rfl⟩ : syracuseStep 962273 = 721705) B721705
theorem B5779421 : Blo 447780 5779421 := bstep (se 3 (by rfl) ⟨1083641, by rfl⟩ : syracuseStep 5779421 = 2167283) B2167283
theorem B14528483 : Blo 447780 14528483 := bstep (se 1 (by rfl) ⟨10896362, by rfl⟩ : syracuseStep 14528483 = 21792725) B21792725
theorem B5844973 : Blo 447780 5844973 := bstep (se 3 (by rfl) ⟨1095932, by rfl⟩ : syracuseStep 5844973 = 2191865) B2191865
theorem B1093715 : Blo 447780 1093715 := bstep (se 1 (by rfl) ⟨820286, by rfl⟩ : syracuseStep 1093715 = 1640573) B1640573
theorem B504571 : Blo 447780 504571 := bstep (se 1 (by rfl) ⟨378428, by rfl⟩ : syracuseStep 504571 = 756857) B756857
theorem B963323 : Blo 447780 963323 := bstep (se 1 (by rfl) ⟨722492, by rfl⟩ : syracuseStep 963323 = 1444985) B1444985
theorem B3420953 : Blo 447780 3420953 := bstep (se 2 (by rfl) ⟨1282857, by rfl⟩ : syracuseStep 3420953 = 2565715) B2565715
theorem B865385 : Blo 447780 865385 := bstep (se 2 (by rfl) ⟨324519, by rfl⟩ : syracuseStep 865385 = 649039) B649039
theorem B2274479 : Blo 447780 2274479 := bstep (se 1 (by rfl) ⟨1705859, by rfl⟩ : syracuseStep 2274479 = 3411719) B3411719
theorem B5551325 : Blo 447780 5551325 := bstep (se 3 (by rfl) ⟨1040873, by rfl⟩ : syracuseStep 5551325 = 2081747) B2081747
theorem B1946875 : Blo 447780 1946875 := bstep (se 1 (by rfl) ⟨1460156, by rfl⟩ : syracuseStep 1946875 = 2920313) B2920313
theorem B963913 : Blo 447780 963913 := bstep (se 2 (by rfl) ⟨361467, by rfl⟩ : syracuseStep 963913 = 722935) B722935
theorem B505327 : Blo 447780 505327 := bstep (se 1 (by rfl) ⟨378995, by rfl⟩ : syracuseStep 505327 = 757991) B757991
theorem B505435 : Blo 447780 505435 := bstep (se 1 (by rfl) ⟨379076, by rfl⟩ : syracuseStep 505435 = 758153) B758153
theorem B3847823 : Blo 447780 3847823 := bstep (se 1 (by rfl) ⟨2885867, by rfl⟩ : syracuseStep 3847823 = 5771735) B5771735
theorem B1521449 : Blo 447780 1521449 := bstep (se 2 (by rfl) ⟨570543, by rfl⟩ : syracuseStep 1521449 = 1141087) B1141087
theorem B505723 : Blo 447780 505723 := bstep (se 1 (by rfl) ⟨379292, by rfl⟩ : syracuseStep 505723 = 758585) B758585
theorem B505759 : Blo 447780 505759 := bstep (se 1 (by rfl) ⟨379319, by rfl⟩ : syracuseStep 505759 = 758639) B758639
theorem B2308391 : Blo 447780 2308391 := bstep (se 1 (by rfl) ⟨1731293, by rfl⟩ : syracuseStep 2308391 = 3462587) B3462587
theorem B35404235 : Blo 447780 35404235 := bstep (se 1 (by rfl) ⟨26553176, by rfl⟩ : syracuseStep 35404235 = 53106353) B53106353
theorem B506695 : Blo 447780 506695 := bstep (se 1 (by rfl) ⟨380021, by rfl⟩ : syracuseStep 506695 = 760043) B760043
theorem B507343 : Blo 447780 507343 := bstep (se 1 (by rfl) ⟨380507, by rfl⟩ : syracuseStep 507343 = 761015) B761015
theorem B507559 : Blo 447780 507559 := bstep (se 1 (by rfl) ⟨380669, by rfl⟩ : syracuseStep 507559 = 761339) B761339
theorem B4505311 : Blo 447780 4505311 := bstep (se 1 (by rfl) ⟨3378983, by rfl⟩ : syracuseStep 4505311 = 6757967) B6757967
theorem B638695 : Blo 447780 638695 := bstep (se 1 (by rfl) ⟨479021, by rfl⟩ : syracuseStep 638695 = 958043) B958043
theorem B671687 : Blo 447780 671687 := bstep (se 1 (by rfl) ⟨503765, by rfl⟩ : syracuseStep 671687 = 1007531) B1007531
theorem B507847 : Blo 447780 507847 := bstep (se 1 (by rfl) ⟨380885, by rfl⟩ : syracuseStep 507847 = 761771) B761771
theorem B3850213 : Blo 447780 3850213 := bstep (se 4 (by rfl) ⟨360957, by rfl⟩ : syracuseStep 3850213 = 721915) B721915
theorem B3850487 : Blo 447780 3850487 := bstep (se 1 (by rfl) ⟨2887865, by rfl⟩ : syracuseStep 3850487 = 5775731) B5775731
theorem B672047 : Blo 447780 672047 := bstep (se 1 (by rfl) ⟨504035, by rfl⟩ : syracuseStep 672047 = 1008071) B1008071
theorem B508207 : Blo 447780 508207 := bstep (se 1 (by rfl) ⟨381155, by rfl⟩ : syracuseStep 508207 = 762311) B762311
theorem B672287 : Blo 447780 672287 := bstep (se 1 (by rfl) ⟨504215, by rfl⟩ : syracuseStep 672287 = 1008431) B1008431
theorem B3654409 : Blo 447780 3654409 := bstep (se 2 (by rfl) ⟨1370403, by rfl⟩ : syracuseStep 3654409 = 2740807) B2740807
theorem B541471 : Blo 447780 541471 := bstep (se 1 (by rfl) ⟨406103, by rfl⟩ : syracuseStep 541471 = 812207) B812207
theorem B2737327 : Blo 447780 2737327 := bstep (se 1 (by rfl) ⟨2052995, by rfl⟩ : syracuseStep 2737327 = 4105991) B4105991
theorem B672959 : Blo 447780 672959 := bstep (se 1 (by rfl) ⟨504719, by rfl⟩ : syracuseStep 672959 = 1009439) B1009439
theorem B673103 : Blo 447780 673103 := bstep (se 1 (by rfl) ⟨504827, by rfl⟩ : syracuseStep 673103 = 1009655) B1009655
theorem B673193 : Blo 447780 673193 := bstep (se 2 (by rfl) ⟨252447, by rfl⟩ : syracuseStep 673193 = 504895) B504895
theorem B3458519 : Blo 447780 3458519 := bstep (se 1 (by rfl) ⟨2593889, by rfl⟩ : syracuseStep 3458519 = 5187779) B5187779
theorem B673343 : Blo 447780 673343 := bstep (se 1 (by rfl) ⟨505007, by rfl⟩ : syracuseStep 673343 = 1010015) B1010015
theorem B673385 : Blo 447780 673385 := bstep (se 2 (by rfl) ⟨252519, by rfl⟩ : syracuseStep 673385 = 505039) B505039
theorem B673823 : Blo 447780 673823 := bstep (se 1 (by rfl) ⟨505367, by rfl⟩ : syracuseStep 673823 = 1010735) B1010735
theorem B674015 : Blo 447780 674015 := bstep (se 1 (by rfl) ⟨505511, by rfl⟩ : syracuseStep 674015 = 1011023) B1011023
theorem B674075 : Blo 447780 674075 := bstep (se 1 (by rfl) ⟨505556, by rfl⟩ : syracuseStep 674075 = 1011113) B1011113
theorem B3426785 : Blo 447780 3426785 := bstep (se 2 (by rfl) ⟨1285044, by rfl⟩ : syracuseStep 3426785 = 2570089) B2570089
theorem B674399 : Blo 447780 674399 := bstep (se 1 (by rfl) ⟨505799, by rfl⟩ : syracuseStep 674399 = 1011599) B1011599
theorem B11717399 : Blo 447780 11717399 := bstep (se 1 (by rfl) ⟨8788049, by rfl⟩ : syracuseStep 11717399 = 17576099) B17576099
theorem B1624873 : Blo 447780 1624873 := bstep (se 2 (by rfl) ⟨609327, by rfl⟩ : syracuseStep 1624873 = 1218655) B1218655
theorem B674681 : Blo 447780 674681 := bstep (se 2 (by rfl) ⟨253005, by rfl⟩ : syracuseStep 674681 = 506011) B506011
theorem B17517455 : Blo 447780 17517455 := bstep (se 1 (by rfl) ⟨13138091, by rfl⟩ : syracuseStep 17517455 = 26276183) B26276183
theorem B674729 : Blo 447780 674729 := bstep (se 2 (by rfl) ⟨253023, by rfl⟩ : syracuseStep 674729 = 506047) B506047
theorem B674879 : Blo 447780 674879 := bstep (se 1 (by rfl) ⟨506159, by rfl⟩ : syracuseStep 674879 = 1012319) B1012319
theorem B7654499 : Blo 447780 7654499 := bstep (se 1 (by rfl) ⟨5740874, by rfl⟩ : syracuseStep 7654499 = 11481749) B11481749
theorem B8670361 : Blo 447780 8670361 := bstep (se 2 (by rfl) ⟨3251385, by rfl⟩ : syracuseStep 8670361 = 6502771) B6502771
theorem B6507965 : Blo 447780 6507965 := bstep (se 3 (by rfl) ⟨1220243, by rfl⟩ : syracuseStep 6507965 = 2440487) B2440487
theorem B675431 : Blo 447780 675431 := bstep (se 1 (by rfl) ⟨506573, by rfl⟩ : syracuseStep 675431 = 1013147) B1013147
theorem B675815 : Blo 447780 675815 := bstep (se 1 (by rfl) ⟨506861, by rfl⟩ : syracuseStep 675815 = 1013723) B1013723
theorem B1134587 : Blo 447780 1134587 := bstep (se 1 (by rfl) ⟨850940, by rfl⟩ : syracuseStep 1134587 = 1701881) B1701881
theorem B3231839 : Blo 447780 3231839 := bstep (se 1 (by rfl) ⟨2423879, by rfl⟩ : syracuseStep 3231839 = 4847759) B4847759
theorem B577631 : Blo 447780 577631 := bstep (se 1 (by rfl) ⟨433223, by rfl⟩ : syracuseStep 577631 = 866447) B866447
theorem B675935 : Blo 447780 675935 := bstep (se 1 (by rfl) ⟨506951, by rfl⟩ : syracuseStep 675935 = 1013903) B1013903
theorem B675947 : Blo 447780 675947 := bstep (se 1 (by rfl) ⟨506960, by rfl⟩ : syracuseStep 675947 = 1013921) B1013921
theorem B3231899 : Blo 447780 3231899 := bstep (se 1 (by rfl) ⟨2423924, by rfl⟩ : syracuseStep 3231899 = 4847849) B4847849
theorem B675995 : Blo 447780 675995 := bstep (se 1 (by rfl) ⟨506996, by rfl⟩ : syracuseStep 675995 = 1013993) B1013993
theorem B3461453 : Blo 447780 3461453 := bstep (se 3 (by rfl) ⟨649022, by rfl⟩ : syracuseStep 3461453 = 1298045) B1298045
theorem B676847 : Blo 447780 676847 := bstep (se 1 (by rfl) ⟨507635, by rfl⟩ : syracuseStep 676847 = 1015271) B1015271
theorem B447807 : Blo 447780 447807 := bstep (se 1 (by rfl) ⟨335855, by rfl⟩ : syracuseStep 447807 = 671711) B671711
theorem B677231 : Blo 447780 677231 := bstep (se 1 (by rfl) ⟨507923, by rfl⟩ : syracuseStep 677231 = 1015847) B1015847
theorem B447975 : Blo 447780 447975 := bstep (se 1 (by rfl) ⟨335981, by rfl⟩ : syracuseStep 447975 = 671963) B671963
theorem B677351 : Blo 447780 677351 := bstep (se 1 (by rfl) ⟨508013, by rfl⟩ : syracuseStep 677351 = 1016027) B1016027
theorem B447983 : Blo 447780 447983 := bstep (se 1 (by rfl) ⟨335987, by rfl⟩ : syracuseStep 447983 = 671975) B671975
theorem B7296551 : Blo 447780 7296551 := bstep (se 1 (by rfl) ⟨5472413, by rfl⟩ : syracuseStep 7296551 = 10944827) B10944827
theorem B448091 : Blo 447780 448091 := bstep (se 1 (by rfl) ⟨336068, by rfl⟩ : syracuseStep 448091 = 672137) B672137
theorem B677513 : Blo 447780 677513 := bstep (se 2 (by rfl) ⟨254067, by rfl⟩ : syracuseStep 677513 = 508135) B508135
theorem B448155 : Blo 447780 448155 := bstep (se 1 (by rfl) ⟨336116, by rfl⟩ : syracuseStep 448155 = 672233) B672233
theorem B677531 : Blo 447780 677531 := bstep (se 1 (by rfl) ⟨508148, by rfl⟩ : syracuseStep 677531 = 1016297) B1016297
theorem B448239 : Blo 447780 448239 := bstep (se 1 (by rfl) ⟨336179, by rfl⟩ : syracuseStep 448239 = 672359) B672359
theorem B448327 : Blo 447780 448327 := bstep (se 1 (by rfl) ⟨336245, by rfl⟩ : syracuseStep 448327 = 672491) B672491
theorem B448347 : Blo 447780 448347 := bstep (se 1 (by rfl) ⟨336260, by rfl⟩ : syracuseStep 448347 = 672521) B672521
theorem B1464155 : Blo 447780 1464155 := bstep (se 1 (by rfl) ⟨1098116, by rfl⟩ : syracuseStep 1464155 = 2196233) B2196233
theorem B448415 : Blo 447780 448415 := bstep (se 1 (by rfl) ⟨336311, by rfl⟩ : syracuseStep 448415 = 672623) B672623
theorem B1923041 : Blo 447780 1923041 := bstep (se 2 (by rfl) ⟨721140, by rfl⟩ : syracuseStep 1923041 = 1442281) B1442281
theorem B448583 : Blo 447780 448583 := bstep (se 1 (by rfl) ⟨336437, by rfl⟩ : syracuseStep 448583 = 672875) B672875
theorem B448743 : Blo 447780 448743 := bstep (se 1 (by rfl) ⟨336557, by rfl⟩ : syracuseStep 448743 = 673115) B673115
theorem B8771827 : Blo 447780 8771827 := bstep (se 1 (by rfl) ⟨6578870, by rfl⟩ : syracuseStep 8771827 = 13157741) B13157741
theorem B448927 : Blo 447780 448927 := bstep (se 1 (by rfl) ⟨336695, by rfl⟩ : syracuseStep 448927 = 673391) B673391
theorem B448975 : Blo 447780 448975 := bstep (se 1 (by rfl) ⟨336731, by rfl⟩ : syracuseStep 448975 = 673463) B673463
theorem B448999 : Blo 447780 448999 := bstep (se 1 (by rfl) ⟨336749, by rfl⟩ : syracuseStep 448999 = 673499) B673499
theorem B1137179 : Blo 447780 1137179 := bstep (se 1 (by rfl) ⟨852884, by rfl⟩ : syracuseStep 1137179 = 1705769) B1705769
theorem B449115 : Blo 447780 449115 := bstep (se 1 (by rfl) ⟨336836, by rfl⟩ : syracuseStep 449115 = 673673) B673673
theorem B449183 : Blo 447780 449183 := bstep (se 1 (by rfl) ⟨336887, by rfl⟩ : syracuseStep 449183 = 673775) B673775
theorem B449351 : Blo 447780 449351 := bstep (se 1 (by rfl) ⟨337013, by rfl⟩ : syracuseStep 449351 = 674027) B674027
theorem B449391 : Blo 447780 449391 := bstep (se 1 (by rfl) ⟨337043, by rfl⟩ : syracuseStep 449391 = 674087) B674087
theorem B449447 : Blo 447780 449447 := bstep (se 1 (by rfl) ⟨337085, by rfl⟩ : syracuseStep 449447 = 674171) B674171
theorem B29678561 : Blo 447780 29678561 := bstep (se 2 (by rfl) ⟨11129460, by rfl⟩ : syracuseStep 29678561 = 22258921) B22258921
theorem B449627 : Blo 447780 449627 := bstep (se 1 (by rfl) ⟨337220, by rfl⟩ : syracuseStep 449627 = 674441) B674441
theorem B5201081 : Blo 447780 5201081 := bstep (se 2 (by rfl) ⟨1950405, by rfl⟩ : syracuseStep 5201081 = 3900811) B3900811
theorem B449743 : Blo 447780 449743 := bstep (se 1 (by rfl) ⟨337307, by rfl⟩ : syracuseStep 449743 = 674615) B674615
theorem B449767 : Blo 447780 449767 := bstep (se 1 (by rfl) ⟨337325, by rfl⟩ : syracuseStep 449767 = 674651) B674651
theorem B449863 : Blo 447780 449863 := bstep (se 1 (by rfl) ⟨337397, by rfl⟩ : syracuseStep 449863 = 674795) B674795
theorem B4120001 : Blo 447780 4120001 := bstep (se 2 (by rfl) ⟨1545000, by rfl⟩ : syracuseStep 4120001 = 3090001) B3090001
theorem B449999 : Blo 447780 449999 := bstep (se 1 (by rfl) ⟨337499, by rfl⟩ : syracuseStep 449999 = 674999) B674999
theorem B1465847 : Blo 447780 1465847 := bstep (se 1 (by rfl) ⟨1099385, by rfl⟩ : syracuseStep 1465847 = 2198771) B2198771
theorem B450159 : Blo 447780 450159 := bstep (se 1 (by rfl) ⟨337619, by rfl⟩ : syracuseStep 450159 = 675239) B675239
theorem B4218493 : Blo 447780 4218493 := bstep (se 3 (by rfl) ⟨790967, by rfl⟩ : syracuseStep 4218493 = 1581935) B1581935
theorem B450215 : Blo 447780 450215 := bstep (se 1 (by rfl) ⟨337661, by rfl⟩ : syracuseStep 450215 = 675323) B675323
theorem B450279 : Blo 447780 450279 := bstep (se 1 (by rfl) ⟨337709, by rfl⟩ : syracuseStep 450279 = 675419) B675419
theorem B450335 : Blo 447780 450335 := bstep (se 1 (by rfl) ⟨337751, by rfl⟩ : syracuseStep 450335 = 675503) B675503
theorem B450415 : Blo 447780 450415 := bstep (se 1 (by rfl) ⟨337811, by rfl⟩ : syracuseStep 450415 = 675623) B675623
theorem B450471 : Blo 447780 450471 := bstep (se 1 (by rfl) ⟨337853, by rfl⟩ : syracuseStep 450471 = 675707) B675707
theorem B2285495 : Blo 447780 2285495 := bstep (se 1 (by rfl) ⟨1714121, by rfl⟩ : syracuseStep 2285495 = 3428243) B3428243
theorem B450751 : Blo 447780 450751 := bstep (se 1 (by rfl) ⟨338063, by rfl⟩ : syracuseStep 450751 = 676127) B676127
theorem B450767 : Blo 447780 450767 := bstep (se 1 (by rfl) ⟨338075, by rfl⟩ : syracuseStep 450767 = 676151) B676151
theorem B450815 : Blo 447780 450815 := bstep (se 1 (by rfl) ⟨338111, by rfl⟩ : syracuseStep 450815 = 676223) B676223
theorem B450863 : Blo 447780 450863 := bstep (se 1 (by rfl) ⟨338147, by rfl⟩ : syracuseStep 450863 = 676295) B676295
theorem B1007927 : Blo 447780 1007927 := bstep (se 1 (by rfl) ⟨755945, by rfl⟩ : syracuseStep 1007927 = 1511891) B1511891
theorem B451099 : Blo 447780 451099 := bstep (se 1 (by rfl) ⟨338324, by rfl⟩ : syracuseStep 451099 = 676649) B676649
theorem B451103 : Blo 447780 451103 := bstep (se 1 (by rfl) ⟨338327, by rfl⟩ : syracuseStep 451103 = 676655) B676655
theorem B451183 : Blo 447780 451183 := bstep (se 1 (by rfl) ⟨338387, by rfl⟩ : syracuseStep 451183 = 676775) B676775
theorem B451239 : Blo 447780 451239 := bstep (se 1 (by rfl) ⟨338429, by rfl⟩ : syracuseStep 451239 = 676859) B676859
theorem B451279 : Blo 447780 451279 := bstep (se 1 (by rfl) ⟨338459, by rfl⟩ : syracuseStep 451279 = 676919) B676919
theorem B451359 : Blo 447780 451359 := bstep (se 1 (by rfl) ⟨338519, by rfl⟩ : syracuseStep 451359 = 677039) B677039
theorem B451631 : Blo 447780 451631 := bstep (se 1 (by rfl) ⟨338723, by rfl⟩ : syracuseStep 451631 = 677447) B677447
theorem B451695 : Blo 447780 451695 := bstep (se 1 (by rfl) ⟨338771, by rfl⟩ : syracuseStep 451695 = 677543) B677543
theorem B451751 : Blo 447780 451751 := bstep (se 1 (by rfl) ⟨338813, by rfl⟩ : syracuseStep 451751 = 677627) B677627
theorem B451775 : Blo 447780 451775 := bstep (se 1 (by rfl) ⟨338831, by rfl⟩ : syracuseStep 451775 = 677663) B677663
theorem B1008953 : Blo 447780 1008953 := bstep (se 2 (by rfl) ⟨378357, by rfl⟩ : syracuseStep 1008953 = 756715) B756715
theorem B1009223 : Blo 447780 1009223 := bstep (se 1 (by rfl) ⟨756917, by rfl⟩ : syracuseStep 1009223 = 1513835) B1513835
theorem B1009403 : Blo 447780 1009403 := bstep (se 1 (by rfl) ⟨757052, by rfl⟩ : syracuseStep 1009403 = 1514105) B1514105
theorem B1009691 : Blo 447780 1009691 := bstep (se 1 (by rfl) ⟨757268, by rfl⟩ : syracuseStep 1009691 = 1514537) B1514537
theorem B1370209 : Blo 447780 1370209 := bstep (se 2 (by rfl) ⟨513828, by rfl⟩ : syracuseStep 1370209 = 1027657) B1027657
theorem B977039 : Blo 447780 977039 := bstep (se 1 (by rfl) ⟨732779, by rfl⟩ : syracuseStep 977039 = 1465559) B1465559
theorem B29878793 : Blo 447780 29878793 := bstep (se 2 (by rfl) ⟨11204547, by rfl⟩ : syracuseStep 29878793 = 22409095) B22409095
theorem B1076107 : Blo 447780 1076107 := bstep (se 1 (by rfl) ⟨807080, by rfl⟩ : syracuseStep 1076107 = 1614161) B1614161
theorem B8580097 : Blo 447780 8580097 := bstep (se 2 (by rfl) ⟨3217536, by rfl⟩ : syracuseStep 8580097 = 6435073) B6435073
theorem B2878537 : Blo 447780 2878537 := bstep (se 2 (by rfl) ⟨1079451, by rfl⟩ : syracuseStep 2878537 = 2158903) B2158903
theorem B1011167 : Blo 447780 1011167 := bstep (se 1 (by rfl) ⟨758375, by rfl⟩ : syracuseStep 1011167 = 1516751) B1516751
theorem B1142363 : Blo 447780 1142363 := bstep (se 1 (by rfl) ⟨856772, by rfl⟩ : syracuseStep 1142363 = 1713545) B1713545
theorem B1011383 : Blo 447780 1011383 := bstep (se 1 (by rfl) ⟨758537, by rfl⟩ : syracuseStep 1011383 = 1517075) B1517075
theorem B1437527 : Blo 447780 1437527 := bstep (se 1 (by rfl) ⟨1078145, by rfl⟩ : syracuseStep 1437527 = 2156291) B2156291
theorem B3829679 : Blo 447780 3829679 := bstep (se 1 (by rfl) ⟨2872259, by rfl⟩ : syracuseStep 3829679 = 5744519) B5744519
theorem B8188037 : Blo 447780 8188037 := bstep (se 4 (by rfl) ⟨767628, by rfl⟩ : syracuseStep 8188037 = 1535257) B1535257
theorem B1143143 : Blo 447780 1143143 := bstep (se 1 (by rfl) ⟨857357, by rfl⟩ : syracuseStep 1143143 = 1714715) B1714715
theorem B1012175 : Blo 447780 1012175 := bstep (se 1 (by rfl) ⟨759131, by rfl⟩ : syracuseStep 1012175 = 1518263) B1518263
theorem B1012841 : Blo 447780 1012841 := bstep (se 2 (by rfl) ⟨379815, by rfl⟩ : syracuseStep 1012841 = 759631) B759631
theorem B24671411 : Blo 447780 24671411 := bstep (se 1 (by rfl) ⟨18503558, by rfl⟩ : syracuseStep 24671411 = 37007117) B37007117
theorem B1439039 : Blo 447780 1439039 := bstep (se 1 (by rfl) ⟨1079279, by rfl⟩ : syracuseStep 1439039 = 2158559) B2158559
theorem B1701395 : Blo 447780 1701395 := bstep (se 1 (by rfl) ⟨1276046, by rfl⟩ : syracuseStep 1701395 = 2552093) B2552093
theorem B1013471 : Blo 447780 1013471 := bstep (se 1 (by rfl) ⟨760103, by rfl⟩ : syracuseStep 1013471 = 1520207) B1520207
theorem B1013831 : Blo 447780 1013831 := bstep (se 1 (by rfl) ⟨760373, by rfl⟩ : syracuseStep 1013831 = 1520747) B1520747
theorem B456935 : Blo 447780 456935 := bstep (se 1 (by rfl) ⟨342701, by rfl⟩ : syracuseStep 456935 = 685403) B685403
theorem B850151 : Blo 447780 850151 := bstep (se 1 (by rfl) ⟨637613, by rfl⟩ : syracuseStep 850151 = 1275227) B1275227
theorem B1079951 : Blo 447780 1079951 := bstep (se 1 (by rfl) ⟨809963, by rfl⟩ : syracuseStep 1079951 = 1619927) B1619927
theorem B850591 : Blo 447780 850591 := bstep (se 1 (by rfl) ⟨637943, by rfl⟩ : syracuseStep 850591 = 1275887) B1275887
theorem B1014497 : Blo 447780 1014497 := bstep (se 2 (by rfl) ⟨380436, by rfl⟩ : syracuseStep 1014497 = 760873) B760873
theorem B1014695 : Blo 447780 1014695 := bstep (se 1 (by rfl) ⟨761021, by rfl⟩ : syracuseStep 1014695 = 1522043) B1522043
theorem B1014875 : Blo 447780 1014875 := bstep (se 1 (by rfl) ⟨761156, by rfl⟩ : syracuseStep 1014875 = 1522313) B1522313
theorem B5143823 : Blo 447780 5143823 := bstep (se 1 (by rfl) ⟨3857867, by rfl⟩ : syracuseStep 5143823 = 7715735) B7715735
theorem B1703339 : Blo 447780 1703339 := bstep (se 1 (by rfl) ⟨1277504, by rfl⟩ : syracuseStep 1703339 = 2555009) B2555009
theorem B851563 : Blo 447780 851563 := bstep (se 1 (by rfl) ⟨638672, by rfl⟩ : syracuseStep 851563 = 1277345) B1277345
theorem B4849399 : Blo 447780 4849399 := bstep (se 1 (by rfl) ⟨3637049, by rfl⟩ : syracuseStep 4849399 = 7274099) B7274099
theorem B1081097 : Blo 447780 1081097 := bstep (se 2 (by rfl) ⟨405411, by rfl⟩ : syracuseStep 1081097 = 810823) B810823
theorem B851791 : Blo 447780 851791 := bstep (se 1 (by rfl) ⟨638843, by rfl⟩ : syracuseStep 851791 = 1277687) B1277687
theorem B1015631 : Blo 447780 1015631 := bstep (se 1 (by rfl) ⟨761723, by rfl⟩ : syracuseStep 1015631 = 1523447) B1523447
theorem B720839 : Blo 447780 720839 := bstep (se 1 (by rfl) ⟨540629, by rfl⟩ : syracuseStep 720839 = 1081259) B1081259
theorem B8618237 : Blo 447780 8618237 := bstep (se 3 (by rfl) ⟨1615919, by rfl⟩ : syracuseStep 8618237 = 3231839) B3231839
theorem B1540349 : Blo 447780 1540349 := bstep (se 3 (by rfl) ⟨288815, by rfl⟩ : syracuseStep 1540349 = 577631) B577631
theorem B852383 : Blo 447780 852383 := bstep (se 1 (by rfl) ⟨639287, by rfl⟩ : syracuseStep 852383 = 1278575) B1278575
theorem B1016225 : Blo 447780 1016225 := bstep (se 2 (by rfl) ⟨381084, by rfl⟩ : syracuseStep 1016225 = 762169) B762169
theorem B1278985 : Blo 447780 1278985 := bstep (se 2 (by rfl) ⟨479619, by rfl⟩ : syracuseStep 1278985 = 959239) B959239
theorem B721961 : Blo 447780 721961 := bstep (se 2 (by rfl) ⟨270735, by rfl⟩ : syracuseStep 721961 = 541471) B541471
theorem B2426431 : Blo 447780 2426431 := bstep (se 1 (by rfl) ⟨1819823, by rfl⟩ : syracuseStep 2426431 = 3639647) B3639647
theorem B3409775 : Blo 447780 3409775 := bstep (se 1 (by rfl) ⟨2557331, by rfl⟩ : syracuseStep 3409775 = 5114663) B5114663
theorem B1149353 : Blo 447780 1149353 := bstep (se 2 (by rfl) ⟨431007, by rfl⟩ : syracuseStep 1149353 = 862015) B862015
theorem B2427383 : Blo 447780 2427383 := bstep (se 1 (by rfl) ⟨1820537, by rfl⟩ : syracuseStep 2427383 = 3641075) B3641075
theorem B2165363 : Blo 447780 2165363 := bstep (se 1 (by rfl) ⟨1624022, by rfl⟩ : syracuseStep 2165363 = 3248045) B3248045
theorem B756391 : Blo 447780 756391 := bstep (se 1 (by rfl) ⟨567293, by rfl⟩ : syracuseStep 756391 = 1134587) B1134587
theorem B9833159 : Blo 447780 9833159 := bstep (se 1 (by rfl) ⟨7374869, by rfl⟩ : syracuseStep 9833159 = 14749739) B14749739
theorem B5770763 : Blo 447780 5770763 := bstep (se 1 (by rfl) ⟨4328072, by rfl⟩ : syracuseStep 5770763 = 8656145) B8656145
theorem B1314407 : Blo 447780 1314407 := bstep (se 1 (by rfl) ⟨985805, by rfl⟩ : syracuseStep 1314407 = 1971611) B1971611
theorem B1707743 : Blo 447780 1707743 := bstep (se 1 (by rfl) ⟨1280807, by rfl⟩ : syracuseStep 1707743 = 2561615) B2561615
theorem B2166497 : Blo 447780 2166497 := bstep (se 2 (by rfl) ⟨812436, by rfl⟩ : syracuseStep 2166497 = 1624873) B1624873
theorem B1282027 : Blo 447780 1282027 := bstep (se 1 (by rfl) ⟨961520, by rfl⟩ : syracuseStep 1282027 = 1923041) B1923041
theorem B11440129 : Blo 447780 11440129 := bstep (se 2 (by rfl) ⟨4290048, by rfl⟩ : syracuseStep 11440129 = 8580097) B8580097
theorem B3838049 : Blo 447780 3838049 := bstep (se 2 (by rfl) ⟨1439268, by rfl⟩ : syracuseStep 3838049 = 2878537) B2878537
theorem B758119 : Blo 447780 758119 := bstep (se 1 (by rfl) ⟨568589, by rfl⟩ : syracuseStep 758119 = 1137179) B1137179
theorem B2888459 : Blo 447780 2888459 := bstep (se 1 (by rfl) ⟨2166344, by rfl⟩ : syracuseStep 2888459 = 4332689) B4332689
theorem B1512701 : Blo 447780 1512701 := bstep (se 3 (by rfl) ⟨283631, by rfl⟩ : syracuseStep 1512701 = 567263) B567263
theorem B1513295 : Blo 447780 1513295 := bstep (se 1 (by rfl) ⟨1134971, by rfl⟩ : syracuseStep 1513295 = 2269943) B2269943
theorem B1218493 : Blo 447780 1218493 := bstep (se 3 (by rfl) ⟨228467, by rfl⟩ : syracuseStep 1218493 = 456935) B456935
theorem B1513619 : Blo 447780 1513619 := bstep (se 1 (by rfl) ⟨1135214, by rfl⟩ : syracuseStep 1513619 = 2270429) B2270429
theorem B2595833 : Blo 447780 2595833 := bstep (se 2 (by rfl) ⟨973437, by rfl⟩ : syracuseStep 2595833 = 1946875) B1946875
theorem B3415121 : Blo 447780 3415121 := bstep (se 2 (by rfl) ⟨1280670, by rfl⟩ : syracuseStep 3415121 = 2561341) B2561341
theorem B1285217 : Blo 447780 1285217 := bstep (se 2 (by rfl) ⟨481956, by rfl⟩ : syracuseStep 1285217 = 963913) B963913
theorem B761575 : Blo 447780 761575 := bstep (se 1 (by rfl) ⟨571181, by rfl⟩ : syracuseStep 761575 = 1142363) B1142363
theorem B958351 : Blo 447780 958351 := bstep (se 1 (by rfl) ⟨718763, by rfl⟩ : syracuseStep 958351 = 1437527) B1437527
theorem B729143 : Blo 447780 729143 := bstep (se 1 (by rfl) ⟨546857, by rfl⟩ : syracuseStep 729143 = 1093715) B1093715
theorem B762095 : Blo 447780 762095 := bstep (se 1 (by rfl) ⟨571571, by rfl⟩ : syracuseStep 762095 = 1143143) B1143143
theorem B1516319 : Blo 447780 1516319 := bstep (se 1 (by rfl) ⟨1137239, by rfl⟩ : syracuseStep 1516319 = 2274479) B2274479
theorem B959359 : Blo 447780 959359 := bstep (se 1 (by rfl) ⟨719519, by rfl⟩ : syracuseStep 959359 = 1439039) B1439039
theorem B2565215 : Blo 447780 2565215 := bstep (se 1 (by rfl) ⟨1923911, by rfl⟩ : syracuseStep 2565215 = 3847823) B3847823
theorem B25863461 : Blo 447780 25863461 := bstep (se 4 (by rfl) ⟨2424699, by rfl⟩ : syracuseStep 25863461 = 4849399) B4849399
theorem B566767 : Blo 447780 566767 := bstep (se 1 (by rfl) ⟨425075, by rfl⟩ : syracuseStep 566767 = 850151) B850151
theorem B23602823 : Blo 447780 23602823 := bstep (se 1 (by rfl) ⟨17702117, by rfl⟩ : syracuseStep 23602823 = 35404235) B35404235
theorem B6007081 : Blo 447780 6007081 := bstep (se 2 (by rfl) ⟨2252655, by rfl⟩ : syracuseStep 6007081 = 4505311) B4505311
theorem B2566991 : Blo 447780 2566991 := bstep (se 1 (by rfl) ⟨1925243, by rfl⟩ : syracuseStep 2566991 = 3850487) B3850487
theorem B38972339 : Blo 447780 38972339 := bstep (se 1 (by rfl) ⟨29229254, by rfl⟩ : syracuseStep 38972339 = 58458509) B58458509
theorem B1093151 : Blo 447780 1093151 := bstep (se 1 (by rfl) ⟨819863, by rfl⟩ : syracuseStep 1093151 = 1639727) B1639727
theorem B2305679 : Blo 447780 2305679 := bstep (se 1 (by rfl) ⟨1729259, by rfl⟩ : syracuseStep 2305679 = 3458519) B3458519
theorem B3419981 : Blo 447780 3419981 := bstep (se 3 (by rfl) ⟨641246, by rfl⟩ : syracuseStep 3419981 = 1282493) B1282493
theorem B504031 : Blo 447780 504031 := bstep (se 1 (by rfl) ⟨378023, by rfl⟩ : syracuseStep 504031 = 756047) B756047
theorem B3649769 : Blo 447780 3649769 := bstep (se 2 (by rfl) ⟨1368663, by rfl⟩ : syracuseStep 3649769 = 2737327) B2737327
theorem B4731301 : Blo 447780 4731301 := bstep (se 4 (by rfl) ⟨443559, by rfl⟩ : syracuseStep 4731301 = 887119) B887119
theorem B7811599 : Blo 447780 7811599 := bstep (se 1 (by rfl) ⟨5858699, by rfl⟩ : syracuseStep 7811599 = 11717399) B11717399
theorem B569911 : Blo 447780 569911 := bstep (se 1 (by rfl) ⟨427433, by rfl⟩ : syracuseStep 569911 = 854867) B854867
theorem B11678303 : Blo 447780 11678303 := bstep (se 1 (by rfl) ⟨8758727, by rfl⟩ : syracuseStep 11678303 = 17517455) B17517455
theorem B504607 : Blo 447780 504607 := bstep (se 1 (by rfl) ⟨378455, by rfl⟩ : syracuseStep 504607 = 756911) B756911
theorem B4338643 : Blo 447780 4338643 := bstep (se 1 (by rfl) ⟨3253982, by rfl⟩ : syracuseStep 4338643 = 6507965) B6507965
theorem B2307635 : Blo 447780 2307635 := bstep (se 1 (by rfl) ⟨1730726, by rfl⟩ : syracuseStep 2307635 = 3461453) B3461453
theorem B768287 : Blo 447780 768287 := bstep (se 1 (by rfl) ⟨576215, by rfl⟩ : syracuseStep 768287 = 1152431) B1152431
theorem B4864367 : Blo 447780 4864367 := bstep (se 1 (by rfl) ⟨3648275, by rfl⟩ : syracuseStep 4864367 = 7296551) B7296551
theorem B2275937 : Blo 447780 2275937 := bstep (se 2 (by rfl) ⟨853476, by rfl⟩ : syracuseStep 2275937 = 1706953) B1706953
theorem B77118227 : Blo 447780 77118227 := bstep (se 1 (by rfl) ⟨57838670, by rfl⟩ : syracuseStep 77118227 = 115677341) B115677341
theorem B1621657 : Blo 447780 1621657 := bstep (se 2 (by rfl) ⟨608121, by rfl⟩ : syracuseStep 1621657 = 1216243) B1216243
theorem B1523663 : Blo 447780 1523663 := bstep (se 1 (by rfl) ⟨1142747, by rfl⟩ : syracuseStep 1523663 = 2285495) B2285495
theorem B671951 : Blo 447780 671951 := bstep (se 1 (by rfl) ⟨503963, by rfl⟩ : syracuseStep 671951 = 1007927) B1007927
theorem B5783885 : Blo 447780 5783885 := bstep (se 3 (by rfl) ⟨1084478, by rfl⟩ : syracuseStep 5783885 = 2168957) B2168957
theorem B672635 : Blo 447780 672635 := bstep (se 1 (by rfl) ⟨504476, by rfl⟩ : syracuseStep 672635 = 1008953) B1008953
theorem B672761 : Blo 447780 672761 := bstep (se 2 (by rfl) ⟨252285, by rfl⟩ : syracuseStep 672761 = 504571) B504571
theorem B672815 : Blo 447780 672815 := bstep (se 1 (by rfl) ⟨504611, by rfl⟩ : syracuseStep 672815 = 1009223) B1009223
theorem B672935 : Blo 447780 672935 := bstep (se 1 (by rfl) ⟨504701, by rfl⟩ : syracuseStep 672935 = 1009403) B1009403
theorem B673127 : Blo 447780 673127 := bstep (se 1 (by rfl) ⟨504845, by rfl⟩ : syracuseStep 673127 = 1009691) B1009691
theorem B673769 : Blo 447780 673769 := bstep (se 2 (by rfl) ⟨252663, by rfl⟩ : syracuseStep 673769 = 505327) B505327
theorem B673913 : Blo 447780 673913 := bstep (se 2 (by rfl) ⟨252717, by rfl⟩ : syracuseStep 673913 = 505435) B505435
theorem B1362143 : Blo 447780 1362143 := bstep (se 1 (by rfl) ⟨1021607, by rfl⟩ : syracuseStep 1362143 = 2043215) B2043215
theorem B674111 : Blo 447780 674111 := bstep (se 1 (by rfl) ⟨505583, by rfl⟩ : syracuseStep 674111 = 1011167) B1011167
theorem B674255 : Blo 447780 674255 := bstep (se 1 (by rfl) ⟨505691, by rfl⟩ : syracuseStep 674255 = 1011383) B1011383
theorem B641515 : Blo 447780 641515 := bstep (se 1 (by rfl) ⟨481136, by rfl⟩ : syracuseStep 641515 = 962273) B962273
theorem B674297 : Blo 447780 674297 := bstep (se 2 (by rfl) ⟨252861, by rfl⟩ : syracuseStep 674297 = 505723) B505723
theorem B674345 : Blo 447780 674345 := bstep (se 2 (by rfl) ⟨252879, by rfl⟩ : syracuseStep 674345 = 505759) B505759
theorem B3852947 : Blo 447780 3852947 := bstep (se 1 (by rfl) ⟨2889710, by rfl⟩ : syracuseStep 3852947 = 5779421) B5779421
theorem B9685655 : Blo 447780 9685655 := bstep (se 1 (by rfl) ⟨7264241, by rfl⟩ : syracuseStep 9685655 = 14528483) B14528483
theorem B5458691 : Blo 447780 5458691 := bstep (se 1 (by rfl) ⟨4094018, by rfl⟩ : syracuseStep 5458691 = 8188037) B8188037
theorem B674783 : Blo 447780 674783 := bstep (se 1 (by rfl) ⟨506087, by rfl⟩ : syracuseStep 674783 = 1012175) B1012175
theorem B642215 : Blo 447780 642215 := bstep (se 1 (by rfl) ⟨481661, by rfl⟩ : syracuseStep 642215 = 963323) B963323
theorem B2280635 : Blo 447780 2280635 := bstep (se 1 (by rfl) ⟨1710476, by rfl⟩ : syracuseStep 2280635 = 3420953) B3420953
theorem B576923 : Blo 447780 576923 := bstep (se 1 (by rfl) ⟨432692, by rfl⟩ : syracuseStep 576923 = 865385) B865385
theorem B675227 : Blo 447780 675227 := bstep (se 1 (by rfl) ⟨506420, by rfl⟩ : syracuseStep 675227 = 1012841) B1012841
theorem B1134121 : Blo 447780 1134121 := bstep (se 2 (by rfl) ⟨425295, by rfl⟩ : syracuseStep 1134121 = 850591) B850591
theorem B1134263 : Blo 447780 1134263 := bstep (se 1 (by rfl) ⟨850697, by rfl⟩ : syracuseStep 1134263 = 1701395) B1701395
theorem B675593 : Blo 447780 675593 := bstep (se 2 (by rfl) ⟨253347, by rfl⟩ : syracuseStep 675593 = 506695) B506695
theorem B675647 : Blo 447780 675647 := bstep (se 1 (by rfl) ⟨506735, by rfl⟩ : syracuseStep 675647 = 1013471) B1013471
theorem B675887 : Blo 447780 675887 := bstep (se 1 (by rfl) ⟨506915, by rfl⟩ : syracuseStep 675887 = 1013831) B1013831
theorem B13160537 : Blo 447780 13160537 := bstep (se 2 (by rfl) ⟨4935201, by rfl⟩ : syracuseStep 13160537 = 9870403) B9870403
theorem B676331 : Blo 447780 676331 := bstep (se 1 (by rfl) ⟨507248, by rfl⟩ : syracuseStep 676331 = 1014497) B1014497
theorem B676457 : Blo 447780 676457 := bstep (se 2 (by rfl) ⟨253671, by rfl⟩ : syracuseStep 676457 = 507343) B507343
theorem B676463 : Blo 447780 676463 := bstep (se 1 (by rfl) ⟨507347, by rfl⟩ : syracuseStep 676463 = 1014695) B1014695
theorem B676583 : Blo 447780 676583 := bstep (se 1 (by rfl) ⟨507437, by rfl⟩ : syracuseStep 676583 = 1014875) B1014875
theorem B1135417 : Blo 447780 1135417 := bstep (se 2 (by rfl) ⟨425781, by rfl⟩ : syracuseStep 1135417 = 851563) B851563
theorem B5624657 : Blo 447780 5624657 := bstep (se 2 (by rfl) ⟨2109246, by rfl⟩ : syracuseStep 5624657 = 4218493) B4218493
theorem B3429215 : Blo 447780 3429215 := bstep (se 1 (by rfl) ⟨2571911, by rfl⟩ : syracuseStep 3429215 = 5143823) B5143823
theorem B676745 : Blo 447780 676745 := bstep (se 2 (by rfl) ⟨253779, by rfl⟩ : syracuseStep 676745 = 507559) B507559
theorem B1135559 : Blo 447780 1135559 := bstep (se 1 (by rfl) ⟨851669, by rfl⟩ : syracuseStep 1135559 = 1703339) B1703339
theorem B1135721 : Blo 447780 1135721 := bstep (se 2 (by rfl) ⟨425895, by rfl⟩ : syracuseStep 1135721 = 851791) B851791
theorem B1922237 : Blo 447780 1922237 := bstep (se 3 (by rfl) ⟨360419, by rfl⟩ : syracuseStep 1922237 = 720839) B720839
theorem B677087 : Blo 447780 677087 := bstep (se 1 (by rfl) ⟨507815, by rfl⟩ : syracuseStep 677087 = 1015631) B1015631
theorem B677129 : Blo 447780 677129 := bstep (se 2 (by rfl) ⟨253923, by rfl⟩ : syracuseStep 677129 = 507847) B507847
theorem B447791 : Blo 447780 447791 := bstep (se 1 (by rfl) ⟨335843, by rfl⟩ : syracuseStep 447791 = 671687) B671687
theorem B5133617 : Blo 447780 5133617 := bstep (se 2 (by rfl) ⟨1925106, by rfl⟩ : syracuseStep 5133617 = 3850213) B3850213
theorem B448031 : Blo 447780 448031 := bstep (se 1 (by rfl) ⟨336023, by rfl⟩ : syracuseStep 448031 = 672047) B672047
theorem B1136207 : Blo 447780 1136207 := bstep (se 1 (by rfl) ⟨852155, by rfl⟩ : syracuseStep 1136207 = 1704311) B1704311
theorem B448191 : Blo 447780 448191 := bstep (se 1 (by rfl) ⟨336143, by rfl⟩ : syracuseStep 448191 = 672287) B672287
theorem B677567 : Blo 447780 677567 := bstep (se 1 (by rfl) ⟨508175, by rfl⟩ : syracuseStep 677567 = 1016351) B1016351
theorem B677609 : Blo 447780 677609 := bstep (se 2 (by rfl) ⟨254103, by rfl⟩ : syracuseStep 677609 = 508207) B508207
theorem B677615 : Blo 447780 677615 := bstep (se 1 (by rfl) ⟨508211, by rfl⟩ : syracuseStep 677615 = 1016423) B1016423
theorem B448639 : Blo 447780 448639 := bstep (se 1 (by rfl) ⟨336479, by rfl⟩ : syracuseStep 448639 = 672959) B672959
theorem B1136855 : Blo 447780 1136855 := bstep (se 1 (by rfl) ⟨852641, by rfl⟩ : syracuseStep 1136855 = 1705283) B1705283
theorem B448735 : Blo 447780 448735 := bstep (se 1 (by rfl) ⟨336551, by rfl⟩ : syracuseStep 448735 = 673103) B673103
theorem B448795 : Blo 447780 448795 := bstep (se 1 (by rfl) ⟨336596, by rfl⟩ : syracuseStep 448795 = 673193) B673193
theorem B4872545 : Blo 447780 4872545 := bstep (se 2 (by rfl) ⟨1827204, by rfl⟩ : syracuseStep 4872545 = 3654409) B3654409
theorem B448895 : Blo 447780 448895 := bstep (se 1 (by rfl) ⟨336671, by rfl⟩ : syracuseStep 448895 = 673343) B673343
theorem B448923 : Blo 447780 448923 := bstep (se 1 (by rfl) ⟨336692, by rfl⟩ : syracuseStep 448923 = 673385) B673385
theorem B1137311 : Blo 447780 1137311 := bstep (se 1 (by rfl) ⟨852983, by rfl⟩ : syracuseStep 1137311 = 1705967) B1705967
theorem B449215 : Blo 447780 449215 := bstep (se 1 (by rfl) ⟨336911, by rfl⟩ : syracuseStep 449215 = 673823) B673823
theorem B449343 : Blo 447780 449343 := bstep (se 1 (by rfl) ⟨337007, by rfl⟩ : syracuseStep 449343 = 674015) B674015
theorem B449383 : Blo 447780 449383 := bstep (se 1 (by rfl) ⟨337037, by rfl⟩ : syracuseStep 449383 = 674075) B674075
theorem B3234755 : Blo 447780 3234755 := bstep (se 1 (by rfl) ⟨2426066, by rfl⟩ : syracuseStep 3234755 = 4852133) B4852133
theorem B2284523 : Blo 447780 2284523 := bstep (se 1 (by rfl) ⟨1713392, by rfl⟩ : syracuseStep 2284523 = 3426785) B3426785
theorem B449599 : Blo 447780 449599 := bstep (se 1 (by rfl) ⟨337199, by rfl⟩ : syracuseStep 449599 = 674399) B674399
theorem B449787 : Blo 447780 449787 := bstep (se 1 (by rfl) ⟨337340, by rfl⟩ : syracuseStep 449787 = 674681) B674681
theorem B449819 : Blo 447780 449819 := bstep (se 1 (by rfl) ⟨337364, by rfl⟩ : syracuseStep 449819 = 674729) B674729
theorem B810367 : Blo 447780 810367 := bstep (se 1 (by rfl) ⟨607775, by rfl⟩ : syracuseStep 810367 = 1215551) B1215551
theorem B449919 : Blo 447780 449919 := bstep (se 1 (by rfl) ⟨337439, by rfl⟩ : syracuseStep 449919 = 674879) B674879
theorem B5102999 : Blo 447780 5102999 := bstep (se 1 (by rfl) ⟨3827249, by rfl⟩ : syracuseStep 5102999 = 7654499) B7654499
theorem B450287 : Blo 447780 450287 := bstep (se 1 (by rfl) ⟨337715, by rfl⟩ : syracuseStep 450287 = 675431) B675431
theorem B450543 : Blo 447780 450543 := bstep (se 1 (by rfl) ⟨337907, by rfl⟩ : syracuseStep 450543 = 675815) B675815
theorem B1007657 : Blo 447780 1007657 := bstep (se 2 (by rfl) ⟨377871, by rfl⟩ : syracuseStep 1007657 = 755743) B755743
theorem B450623 : Blo 447780 450623 := bstep (se 1 (by rfl) ⟨337967, by rfl⟩ : syracuseStep 450623 = 675935) B675935
theorem B450631 : Blo 447780 450631 := bstep (se 1 (by rfl) ⟨337973, by rfl⟩ : syracuseStep 450631 = 675947) B675947
theorem B2154599 : Blo 447780 2154599 := bstep (se 1 (by rfl) ⟨1615949, by rfl⟩ : syracuseStep 2154599 = 3231899) B3231899
theorem B450663 : Blo 447780 450663 := bstep (se 1 (by rfl) ⟨337997, by rfl⟩ : syracuseStep 450663 = 675995) B675995
theorem B1826945 : Blo 447780 1826945 := bstep (se 2 (by rfl) ⟨685104, by rfl⟩ : syracuseStep 1826945 = 1370209) B1370209
theorem B2285981 : Blo 447780 2285981 := bstep (se 3 (by rfl) ⟨428621, by rfl⟩ : syracuseStep 2285981 = 857243) B857243
theorem B1139255 : Blo 447780 1139255 := bstep (se 1 (by rfl) ⟨854441, by rfl⟩ : syracuseStep 1139255 = 1708883) B1708883
theorem B1008287 : Blo 447780 1008287 := bstep (se 1 (by rfl) ⟨756215, by rfl⟩ : syracuseStep 1008287 = 1512431) B1512431
theorem B451231 : Blo 447780 451231 := bstep (se 1 (by rfl) ⟨338423, by rfl⟩ : syracuseStep 451231 = 676847) B676847
theorem B451487 : Blo 447780 451487 := bstep (se 1 (by rfl) ⟨338615, by rfl⟩ : syracuseStep 451487 = 677231) B677231
theorem B451567 : Blo 447780 451567 := bstep (se 1 (by rfl) ⟨338675, by rfl⟩ : syracuseStep 451567 = 677351) B677351
theorem B451675 : Blo 447780 451675 := bstep (se 1 (by rfl) ⟨338756, by rfl⟩ : syracuseStep 451675 = 677513) B677513
theorem B451687 : Blo 447780 451687 := bstep (se 1 (by rfl) ⟨338765, by rfl⟩ : syracuseStep 451687 = 677531) B677531
theorem B1434809 : Blo 447780 1434809 := bstep (se 2 (by rfl) ⟨538053, by rfl⟩ : syracuseStep 1434809 = 1076107) B1076107
theorem B976103 : Blo 447780 976103 := bstep (se 1 (by rfl) ⟨732077, by rfl⟩ : syracuseStep 976103 = 1464155) B1464155
theorem B11560481 : Blo 447780 11560481 := bstep (se 2 (by rfl) ⟨4335180, by rfl⟩ : syracuseStep 11560481 = 8670361) B8670361
theorem B1926953 : Blo 447780 1926953 := bstep (se 2 (by rfl) ⟨722607, by rfl⟩ : syracuseStep 1926953 = 1445215) B1445215
theorem B681851 : Blo 447780 681851 := bstep (se 1 (by rfl) ⟨511388, by rfl⟩ : syracuseStep 681851 = 1022777) B1022777
theorem B7301087 : Blo 447780 7301087 := bstep (se 1 (by rfl) ⟨5475815, by rfl⟩ : syracuseStep 7301087 = 10951631) B10951631
theorem B19785707 : Blo 447780 19785707 := bstep (se 1 (by rfl) ⟨14839280, by rfl⟩ : syracuseStep 19785707 = 29678561) B29678561
theorem B1140763 : Blo 447780 1140763 := bstep (se 1 (by rfl) ⟨855572, by rfl⟩ : syracuseStep 1140763 = 1711145) B1711145
theorem B3467387 : Blo 447780 3467387 := bstep (se 1 (by rfl) ⟨2600540, by rfl⟩ : syracuseStep 3467387 = 5201081) B5201081
theorem B2746667 : Blo 447780 2746667 := bstep (se 1 (by rfl) ⟨2060000, by rfl⟩ : syracuseStep 2746667 = 4120001) B4120001
theorem B977231 : Blo 447780 977231 := bstep (se 1 (by rfl) ⟨732923, by rfl⟩ : syracuseStep 977231 = 1465847) B1465847
theorem B9726479 : Blo 447780 9726479 := bstep (se 1 (by rfl) ⟨7294859, by rfl⟩ : syracuseStep 9726479 = 14589719) B14589719
theorem B7793297 : Blo 447780 7793297 := bstep (se 2 (by rfl) ⟨2922486, by rfl⟩ : syracuseStep 7793297 = 5844973) B5844973
theorem B1142171 : Blo 447780 1142171 := bstep (se 1 (by rfl) ⟨856628, by rfl⟩ : syracuseStep 1142171 = 1713257) B1713257
theorem B1011419 : Blo 447780 1011419 := bstep (se 1 (by rfl) ⟨758564, by rfl⟩ : syracuseStep 1011419 = 1517129) B1517129
theorem B1535915 : Blo 447780 1535915 := bstep (se 1 (by rfl) ⟨1151936, by rfl⟩ : syracuseStep 1535915 = 2303873) B2303873
theorem B1011689 : Blo 447780 1011689 := bstep (se 2 (by rfl) ⟨379383, by rfl⟩ : syracuseStep 1011689 = 758767) B758767
theorem B1011743 : Blo 447780 1011743 := bstep (se 1 (by rfl) ⟨758807, by rfl⟩ : syracuseStep 1011743 = 1517615) B1517615
theorem B651359 : Blo 447780 651359 := bstep (se 1 (by rfl) ⟨488519, by rfl⟩ : syracuseStep 651359 = 977039) B977039
theorem B4878463 : Blo 447780 4878463 := bstep (se 1 (by rfl) ⟨3658847, by rfl⟩ : syracuseStep 4878463 = 7317695) B7317695
theorem B19919195 : Blo 447780 19919195 := bstep (se 1 (by rfl) ⟨14939396, by rfl⟩ : syracuseStep 19919195 = 29878793) B29878793
theorem B2879869 : Blo 447780 2879869 := bstep (se 3 (by rfl) ⟨539975, by rfl⟩ : syracuseStep 2879869 = 1079951) B1079951
theorem B1012571 : Blo 447780 1012571 := bstep (se 1 (by rfl) ⟨759428, by rfl⟩ : syracuseStep 1012571 = 1518857) B1518857
theorem B2553119 : Blo 447780 2553119 := bstep (se 1 (by rfl) ⟨1914839, by rfl⟩ : syracuseStep 2553119 = 3829679) B3829679
theorem B11695769 : Blo 447780 11695769 := bstep (se 2 (by rfl) ⟨4385913, by rfl⟩ : syracuseStep 11695769 = 8771827) B8771827
theorem B16447607 : Blo 447780 16447607 := bstep (se 1 (by rfl) ⟨12335705, by rfl⟩ : syracuseStep 16447607 = 24671411) B24671411
theorem B3700883 : Blo 447780 3700883 := bstep (se 1 (by rfl) ⟨2775662, by rfl⟩ : syracuseStep 3700883 = 5551325) B5551325
theorem B1014299 : Blo 447780 1014299 := bstep (se 1 (by rfl) ⟨760724, by rfl⟩ : syracuseStep 1014299 = 1521449) B1521449
theorem B3406373 : Blo 447780 3406373 := bstep (se 4 (by rfl) ⟨319347, by rfl⟩ : syracuseStep 3406373 = 638695) B638695
theorem B1538927 : Blo 447780 1538927 := bstep (se 1 (by rfl) ⟨1154195, by rfl⟩ : syracuseStep 1538927 = 2308391) B2308391
theorem B720731 : Blo 447780 720731 := bstep (se 1 (by rfl) ⟨540548, by rfl⟩ : syracuseStep 720731 = 1081097) B1081097
theorem B1736957 : Blo 447780 1736957 := bstep (se 3 (by rfl) ⟨325679, by rfl⟩ : syracuseStep 1736957 = 651359) B651359
theorem B1279145 : Blo 447780 1279145 := bstep (se 2 (by rfl) ⟨479679, by rfl⟩ : syracuseStep 1279145 = 959359) B959359
theorem B1705313 : Blo 447780 1705313 := bstep (se 2 (by rfl) ⟨639492, by rfl⟩ : syracuseStep 1705313 = 1278985) B1278985
theorem B1443575 : Blo 447780 1443575 := bstep (se 1 (by rfl) ⟨1082681, by rfl⟩ : syracuseStep 1443575 = 2165363) B2165363
theorem B6457103 : Blo 447780 6457103 := bstep (se 1 (by rfl) ⟨4842827, by rfl⟩ : syracuseStep 6457103 = 9685655) B9685655
theorem B6555439 : Blo 447780 6555439 := bstep (se 1 (by rfl) ⟨4916579, by rfl⟩ : syracuseStep 6555439 = 9833159) B9833159
theorem B3639127 : Blo 447780 3639127 := bstep (se 1 (by rfl) ⟨2729345, by rfl⟩ : syracuseStep 3639127 = 5458691) B5458691
theorem B755689 : Blo 447780 755689 := bstep (se 2 (by rfl) ⟨283383, by rfl⟩ : syracuseStep 755689 = 566767) B566767
theorem B25233605 : Blo 447780 25233605 := bstep (se 4 (by rfl) ⟨2365650, by rfl⟩ : syracuseStep 25233605 = 4731301) B4731301
theorem B756175 : Blo 447780 756175 := bstep (se 1 (by rfl) ⟨567131, by rfl⟩ : syracuseStep 756175 = 1134263) B1134263
theorem B1444331 : Blo 447780 1444331 := bstep (se 1 (by rfl) ⟨1083248, by rfl⟩ : syracuseStep 1444331 = 2166497) B2166497
theorem B2558699 : Blo 447780 2558699 := bstep (se 1 (by rfl) ⟨1919024, by rfl⟩ : syracuseStep 2558699 = 3838049) B3838049
theorem B757039 : Blo 447780 757039 := bstep (se 1 (by rfl) ⟨567779, by rfl⟩ : syracuseStep 757039 = 1135559) B1135559
theorem B855353 : Blo 447780 855353 := bstep (se 2 (by rfl) ⟨320757, by rfl⟩ : syracuseStep 855353 = 641515) B641515
theorem B757147 : Blo 447780 757147 := bstep (se 1 (by rfl) ⟨567860, by rfl⟩ : syracuseStep 757147 = 1135721) B1135721
theorem B1281491 : Blo 447780 1281491 := bstep (se 1 (by rfl) ⟨961118, by rfl⟩ : syracuseStep 1281491 = 1922237) B1922237
theorem B757471 : Blo 447780 757471 := bstep (se 1 (by rfl) ⟨568103, by rfl⟩ : syracuseStep 757471 = 1136207) B1136207
theorem B757903 : Blo 447780 757903 := bstep (se 1 (by rfl) ⟨568427, by rfl⟩ : syracuseStep 757903 = 1136855) B1136855
theorem B3248363 : Blo 447780 3248363 := bstep (se 1 (by rfl) ⟨2436272, by rfl⟩ : syracuseStep 3248363 = 4872545) B4872545
theorem B758207 : Blo 447780 758207 := bstep (se 1 (by rfl) ⟨568655, by rfl⟩ : syracuseStep 758207 = 1137311) B1137311
theorem B1512161 : Blo 447780 1512161 := bstep (se 2 (by rfl) ⟨567060, by rfl⟩ : syracuseStep 1512161 = 1134121) B1134121
theorem B856811 : Blo 447780 856811 := bstep (se 1 (by rfl) ⟨642608, by rfl⟩ : syracuseStep 856811 = 1285217) B1285217
theorem B1709369 : Blo 447780 1709369 := bstep (se 2 (by rfl) ⟨641013, by rfl⟩ : syracuseStep 1709369 = 1282027) B1282027
theorem B1217963 : Blo 447780 1217963 := bstep (se 1 (by rfl) ⟨913472, by rfl⟩ : syracuseStep 1217963 = 1826945) B1826945
theorem B759503 : Blo 447780 759503 := bstep (se 1 (by rfl) ⟨569627, by rfl⟩ : syracuseStep 759503 = 1139255) B1139255
theorem B3839825 : Blo 447780 3839825 := bstep (se 2 (by rfl) ⟨1439934, by rfl⟩ : syracuseStep 3839825 = 2879869) B2879869
theorem B1710143 : Blo 447780 1710143 := bstep (se 1 (by rfl) ⟨1282607, by rfl⟩ : syracuseStep 1710143 = 2565215) B2565215
theorem B759881 : Blo 447780 759881 := bstep (se 2 (by rfl) ⟨284955, by rfl⟩ : syracuseStep 759881 = 569911) B569911
theorem B956539 : Blo 447780 956539 := bstep (se 1 (by rfl) ⟨717404, by rfl⟩ : syracuseStep 956539 = 1434809) B1434809
theorem B17242307 : Blo 447780 17242307 := bstep (se 1 (by rfl) ⟨12931730, by rfl⟩ : syracuseStep 17242307 = 25863461) B25863461
theorem B7706987 : Blo 447780 7706987 := bstep (se 1 (by rfl) ⟨5780240, by rfl⟩ : syracuseStep 7706987 = 11560481) B11560481
theorem B1513889 : Blo 447780 1513889 := bstep (se 2 (by rfl) ⟨567708, by rfl⟩ : syracuseStep 1513889 = 1135417) B1135417
theorem B15735215 : Blo 447780 15735215 := bstep (se 1 (by rfl) ⟨11801411, by rfl⟩ : syracuseStep 15735215 = 23602823) B23602823
theorem B1284635 : Blo 447780 1284635 := bstep (se 1 (by rfl) ⟨963476, by rfl⟩ : syracuseStep 1284635 = 1926953) B1926953
theorem B1711327 : Blo 447780 1711327 := bstep (se 1 (by rfl) ⟨1283495, by rfl⟩ : syracuseStep 1711327 = 2566991) B2566991
theorem B761447 : Blo 447780 761447 := bstep (se 1 (by rfl) ⟨571085, by rfl⟩ : syracuseStep 761447 = 1142171) B1142171
theorem B728767 : Blo 447780 728767 := bstep (se 1 (by rfl) ⟨546575, by rfl⟩ : syracuseStep 728767 = 1093151) B1093151
theorem B1023943 : Blo 447780 1023943 := bstep (se 1 (by rfl) ⟨767957, by rfl⟩ : syracuseStep 1023943 = 1535915) B1535915
theorem B2433179 : Blo 447780 2433179 := bstep (se 1 (by rfl) ⟨1824884, by rfl⟩ : syracuseStep 2433179 = 3649769) B3649769
theorem B13279463 : Blo 447780 13279463 := bstep (se 1 (by rfl) ⟨9959597, by rfl⟩ : syracuseStep 13279463 = 19919195) B19919195
theorem B1712573 : Blo 447780 1712573 := bstep (se 3 (by rfl) ⟨321107, by rfl⟩ : syracuseStep 1712573 = 642215) B642215
theorem B2467255 : Blo 447780 2467255 := bstep (se 1 (by rfl) ⟨1850441, by rfl⟩ : syracuseStep 2467255 = 3700883) B3700883
theorem B2270915 : Blo 447780 2270915 := bstep (se 1 (by rfl) ⟨1703186, by rfl⟩ : syracuseStep 2270915 = 3406373) B3406373
theorem B1517291 : Blo 447780 1517291 := bstep (se 1 (by rfl) ⟨1137968, by rfl⟩ : syracuseStep 1517291 = 2275937) B2275937
theorem B1025951 : Blo 447780 1025951 := bstep (se 1 (by rfl) ⟨769463, by rfl⟩ : syracuseStep 1025951 = 1538927) B1538927
theorem B5745491 : Blo 447780 5745491 := bstep (se 1 (by rfl) ⟨4309118, by rfl⟩ : syracuseStep 5745491 = 8618237) B8618237
theorem B1026899 : Blo 447780 1026899 := bstep (se 1 (by rfl) ⟨770174, by rfl⟩ : syracuseStep 1026899 = 1540349) B1540349
theorem B2273021 : Blo 447780 2273021 := bstep (se 3 (by rfl) ⟨426191, by rfl⟩ : syracuseStep 2273021 = 852383) B852383
theorem B2273183 : Blo 447780 2273183 := bstep (se 1 (by rfl) ⟨1704887, by rfl⟩ : syracuseStep 2273183 = 3409775) B3409775
theorem B31142141 : Blo 447780 31142141 := bstep (se 3 (by rfl) ⟨5839151, by rfl⟩ : syracuseStep 31142141 = 11678303) B11678303
theorem B766235 : Blo 447780 766235 := bstep (se 1 (by rfl) ⟨574676, by rfl⟩ : syracuseStep 766235 = 1149353) B1149353
theorem B1618255 : Blo 447780 1618255 := bstep (se 1 (by rfl) ⟨1213691, by rfl⟩ : syracuseStep 1618255 = 2427383) B2427383
theorem B2568631 : Blo 447780 2568631 := bstep (se 1 (by rfl) ⟨1926473, by rfl⟩ : syracuseStep 2568631 = 3852947) B3852947
theorem B1520423 : Blo 447780 1520423 := bstep (se 1 (by rfl) ⟨1140317, by rfl⟩ : syracuseStep 1520423 = 2280635) B2280635
theorem B3847175 : Blo 447780 3847175 := bstep (se 1 (by rfl) ⟨2885381, by rfl⟩ : syracuseStep 3847175 = 5770763) B5770763
theorem B1521017 : Blo 447780 1521017 := bstep (se 2 (by rfl) ⟨570381, by rfl⟩ : syracuseStep 1521017 = 1140763) B1140763
theorem B8009441 : Blo 447780 8009441 := bstep (se 2 (by rfl) ⟨3003540, by rfl⟩ : syracuseStep 8009441 = 6007081) B6007081
theorem B3749771 : Blo 447780 3749771 := bstep (se 1 (by rfl) ⟨2812328, by rfl⟩ : syracuseStep 3749771 = 5624657) B5624657
theorem B3422411 : Blo 447780 3422411 := bstep (se 1 (by rfl) ⟨2566808, by rfl⟩ : syracuseStep 3422411 = 5133617) B5133617
theorem B1523015 : Blo 447780 1523015 := bstep (se 1 (by rfl) ⟨1142261, by rfl⟩ : syracuseStep 1523015 = 2284523) B2284523
theorem B2276747 : Blo 447780 2276747 := bstep (se 1 (by rfl) ⟨1707560, by rfl⟩ : syracuseStep 2276747 = 3415121) B3415121
theorem B15253505 : Blo 447780 15253505 := bstep (se 2 (by rfl) ⟨5720064, by rfl⟩ : syracuseStep 15253505 = 11440129) B11440129
theorem B671771 : Blo 447780 671771 := bstep (se 1 (by rfl) ⟨503828, by rfl⟩ : syracuseStep 671771 = 1007657) B1007657
theorem B508063 : Blo 447780 508063 := bstep (se 1 (by rfl) ⟨381047, by rfl⟩ : syracuseStep 508063 = 762095) B762095
theorem B6504617 : Blo 447780 6504617 := bstep (se 2 (by rfl) ⟨2439231, by rfl⟩ : syracuseStep 6504617 = 4878463) B4878463
theorem B1523987 : Blo 447780 1523987 := bstep (se 1 (by rfl) ⟨1142990, by rfl⟩ : syracuseStep 1523987 = 2285981) B2285981
theorem B672041 : Blo 447780 672041 := bstep (se 2 (by rfl) ⟨252015, by rfl⟩ : syracuseStep 672041 = 504031) B504031
theorem B672191 : Blo 447780 672191 := bstep (se 1 (by rfl) ⟨504143, by rfl⟩ : syracuseStep 672191 = 1008287) B1008287
theorem B7324445 : Blo 447780 7324445 := bstep (se 3 (by rfl) ⟨1373333, by rfl⟩ : syracuseStep 7324445 = 2746667) B2746667
theorem B672809 : Blo 447780 672809 := bstep (se 2 (by rfl) ⟨252303, by rfl⟩ : syracuseStep 672809 = 504607) B504607
theorem B5784857 : Blo 447780 5784857 := bstep (se 2 (by rfl) ⟨2169321, by rfl⟩ : syracuseStep 5784857 = 4338643) B4338643
theorem B4867391 : Blo 447780 4867391 := bstep (se 1 (by rfl) ⟨3650543, by rfl⟩ : syracuseStep 4867391 = 7301087) B7301087
theorem B13190471 : Blo 447780 13190471 := bstep (se 1 (by rfl) ⟨9892853, by rfl⟩ : syracuseStep 13190471 = 19785707) B19785707
theorem B2311591 : Blo 447780 2311591 := bstep (se 1 (by rfl) ⟨1733693, by rfl⟩ : syracuseStep 2311591 = 3467387) B3467387
theorem B5195531 : Blo 447780 5195531 := bstep (se 1 (by rfl) ⟨3896648, by rfl⟩ : syracuseStep 5195531 = 7793297) B7793297
theorem B674279 : Blo 447780 674279 := bstep (se 1 (by rfl) ⟨505709, by rfl⟩ : syracuseStep 674279 = 1011419) B1011419
theorem B2279987 : Blo 447780 2279987 := bstep (se 1 (by rfl) ⟨1709990, by rfl⟩ : syracuseStep 2279987 = 3419981) B3419981
theorem B1624657 : Blo 447780 1624657 := bstep (se 2 (by rfl) ⟨609246, by rfl⟩ : syracuseStep 1624657 = 1218493) B1218493
theorem B674459 : Blo 447780 674459 := bstep (se 1 (by rfl) ⟨505844, by rfl⟩ : syracuseStep 674459 = 1011689) B1011689
theorem B674495 : Blo 447780 674495 := bstep (se 1 (by rfl) ⟨505871, by rfl⟩ : syracuseStep 674495 = 1011743) B1011743
theorem B675047 : Blo 447780 675047 := bstep (se 1 (by rfl) ⟨506285, by rfl⟩ : syracuseStep 675047 = 1012571) B1012571
theorem B10965071 : Blo 447780 10965071 := bstep (se 1 (by rfl) ⟨8223803, by rfl⟩ : syracuseStep 10965071 = 16447607) B16447607
theorem B512191 : Blo 447780 512191 := bstep (se 1 (by rfl) ⟨384143, by rfl⟩ : syracuseStep 512191 = 768287) B768287
theorem B676199 : Blo 447780 676199 := bstep (se 1 (by rfl) ⟨507149, by rfl⟩ : syracuseStep 676199 = 1014299) B1014299
theorem B6148477 : Blo 447780 6148477 := bstep (se 3 (by rfl) ⟨1152839, by rfl⟩ : syracuseStep 6148477 = 2305679) B2305679
theorem B480487 : Blo 447780 480487 := bstep (se 1 (by rfl) ⟨360365, by rfl⟩ : syracuseStep 480487 = 720731) B720731
theorem B447967 : Blo 447780 447967 := bstep (se 1 (by rfl) ⟨335975, by rfl⟩ : syracuseStep 447967 = 671951) B671951
theorem B3855923 : Blo 447780 3855923 := bstep (se 1 (by rfl) ⟨2891942, by rfl⟩ : syracuseStep 3855923 = 5783885) B5783885
theorem B677483 : Blo 447780 677483 := bstep (se 1 (by rfl) ⟨508112, by rfl⟩ : syracuseStep 677483 = 1016225) B1016225
theorem B448423 : Blo 447780 448423 := bstep (se 1 (by rfl) ⟨336317, by rfl⟩ : syracuseStep 448423 = 672635) B672635
theorem B448507 : Blo 447780 448507 := bstep (se 1 (by rfl) ⟨336380, by rfl⟩ : syracuseStep 448507 = 672761) B672761
theorem B481307 : Blo 447780 481307 := bstep (se 1 (by rfl) ⟨360980, by rfl⟩ : syracuseStep 481307 = 721961) B721961
theorem B448543 : Blo 447780 448543 := bstep (se 1 (by rfl) ⟨336407, by rfl⟩ : syracuseStep 448543 = 672815) B672815
theorem B448623 : Blo 447780 448623 := bstep (se 1 (by rfl) ⟨336467, by rfl⟩ : syracuseStep 448623 = 672935) B672935
theorem B448751 : Blo 447780 448751 := bstep (se 1 (by rfl) ⟨336563, by rfl⟩ : syracuseStep 448751 = 673127) B673127
theorem B449179 : Blo 447780 449179 := bstep (se 1 (by rfl) ⟨336884, by rfl⟩ : syracuseStep 449179 = 673769) B673769
theorem B449275 : Blo 447780 449275 := bstep (se 1 (by rfl) ⟨336956, by rfl⟩ : syracuseStep 449275 = 673913) B673913
theorem B908095 : Blo 447780 908095 := bstep (se 1 (by rfl) ⟨681071, by rfl⟩ : syracuseStep 908095 = 1362143) B1362143
theorem B449407 : Blo 447780 449407 := bstep (se 1 (by rfl) ⟨337055, by rfl⟩ : syracuseStep 449407 = 674111) B674111
theorem B449503 : Blo 447780 449503 := bstep (se 1 (by rfl) ⟨337127, by rfl⟩ : syracuseStep 449503 = 674255) B674255
theorem B449531 : Blo 447780 449531 := bstep (se 1 (by rfl) ⟨337148, by rfl⟩ : syracuseStep 449531 = 674297) B674297
theorem B449563 : Blo 447780 449563 := bstep (se 1 (by rfl) ⟨337172, by rfl⟩ : syracuseStep 449563 = 674345) B674345
theorem B449855 : Blo 447780 449855 := bstep (se 1 (by rfl) ⟨337391, by rfl⟩ : syracuseStep 449855 = 674783) B674783
theorem B3235241 : Blo 447780 3235241 := bstep (se 2 (by rfl) ⟨1213215, by rfl⟩ : syracuseStep 3235241 = 2426431) B2426431
theorem B450151 : Blo 447780 450151 := bstep (se 1 (by rfl) ⟨337613, by rfl⟩ : syracuseStep 450151 = 675227) B675227
theorem B876271 : Blo 447780 876271 := bstep (se 1 (by rfl) ⟨657203, by rfl⟩ : syracuseStep 876271 = 1314407) B1314407
theorem B1138495 : Blo 447780 1138495 := bstep (se 1 (by rfl) ⟨853871, by rfl⟩ : syracuseStep 1138495 = 1707743) B1707743
theorem B450395 : Blo 447780 450395 := bstep (se 1 (by rfl) ⟨337796, by rfl⟩ : syracuseStep 450395 = 675593) B675593
theorem B450431 : Blo 447780 450431 := bstep (se 1 (by rfl) ⟨337823, by rfl⟩ : syracuseStep 450431 = 675647) B675647
theorem B450591 : Blo 447780 450591 := bstep (se 1 (by rfl) ⟨337943, by rfl⟩ : syracuseStep 450591 = 675887) B675887
theorem B8773691 : Blo 447780 8773691 := bstep (se 1 (by rfl) ⟨6580268, by rfl⟩ : syracuseStep 8773691 = 13160537) B13160537
theorem B450887 : Blo 447780 450887 := bstep (se 1 (by rfl) ⟨338165, by rfl⟩ : syracuseStep 450887 = 676331) B676331
theorem B450971 : Blo 447780 450971 := bstep (se 1 (by rfl) ⟨338228, by rfl⟩ : syracuseStep 450971 = 676457) B676457
theorem B450975 : Blo 447780 450975 := bstep (se 1 (by rfl) ⟨338231, by rfl⟩ : syracuseStep 450975 = 676463) B676463
theorem B451055 : Blo 447780 451055 := bstep (se 1 (by rfl) ⟨338291, by rfl⟩ : syracuseStep 451055 = 676583) B676583
theorem B1925639 : Blo 447780 1925639 := bstep (se 1 (by rfl) ⟨1444229, by rfl⟩ : syracuseStep 1925639 = 2888459) B2888459
theorem B2286143 : Blo 447780 2286143 := bstep (se 1 (by rfl) ⟨1714607, by rfl⟩ : syracuseStep 2286143 = 3429215) B3429215
theorem B451163 : Blo 447780 451163 := bstep (se 1 (by rfl) ⟨338372, by rfl⟩ : syracuseStep 451163 = 676745) B676745
theorem B451391 : Blo 447780 451391 := bstep (se 1 (by rfl) ⟨338543, by rfl⟩ : syracuseStep 451391 = 677087) B677087
theorem B1008467 : Blo 447780 1008467 := bstep (se 1 (by rfl) ⟨756350, by rfl⟩ : syracuseStep 1008467 = 1512701) B1512701
theorem B451419 : Blo 447780 451419 := bstep (se 1 (by rfl) ⟨338564, by rfl⟩ : syracuseStep 451419 = 677129) B677129
theorem B1008521 : Blo 447780 1008521 := bstep (se 2 (by rfl) ⟨378195, by rfl⟩ : syracuseStep 1008521 = 756391) B756391
theorem B451711 : Blo 447780 451711 := bstep (se 1 (by rfl) ⟨338783, by rfl⟩ : syracuseStep 451711 = 677567) B677567
theorem B451739 : Blo 447780 451739 := bstep (se 1 (by rfl) ⟨338804, by rfl⟩ : syracuseStep 451739 = 677609) B677609
theorem B451743 : Blo 447780 451743 := bstep (se 1 (by rfl) ⟨338807, by rfl⟩ : syracuseStep 451743 = 677615) B677615
theorem B1008863 : Blo 447780 1008863 := bstep (se 1 (by rfl) ⟨756647, by rfl⟩ : syracuseStep 1008863 = 1513295) B1513295
theorem B1009079 : Blo 447780 1009079 := bstep (se 1 (by rfl) ⟨756809, by rfl⟩ : syracuseStep 1009079 = 1513619) B1513619
theorem B2156503 : Blo 447780 2156503 := bstep (se 1 (by rfl) ⟨1617377, by rfl⟩ : syracuseStep 2156503 = 3234755) B3234755
theorem B1730555 : Blo 447780 1730555 := bstep (se 1 (by rfl) ⟨1297916, by rfl⟩ : syracuseStep 1730555 = 2595833) B2595833
theorem B3401999 : Blo 447780 3401999 := bstep (se 1 (by rfl) ⟨2551499, by rfl⟩ : syracuseStep 3401999 = 5102999) B5102999
theorem B486095 : Blo 447780 486095 := bstep (se 1 (by rfl) ⟨364571, by rfl⟩ : syracuseStep 486095 = 729143) B729143
theorem B1436399 : Blo 447780 1436399 := bstep (se 1 (by rfl) ⟨1077299, by rfl⟩ : syracuseStep 1436399 = 2154599) B2154599
theorem B1010825 : Blo 447780 1010825 := bstep (se 2 (by rfl) ⟨379059, by rfl⟩ : syracuseStep 1010825 = 758119) B758119
theorem B1010879 : Blo 447780 1010879 := bstep (se 1 (by rfl) ⟨758159, by rfl⟩ : syracuseStep 1010879 = 1516319) B1516319
theorem B10415465 : Blo 447780 10415465 := bstep (se 2 (by rfl) ⟨3905799, by rfl⟩ : syracuseStep 10415465 = 7811599) B7811599
theorem B650735 : Blo 447780 650735 := bstep (se 1 (by rfl) ⟨488051, by rfl⟩ : syracuseStep 650735 = 976103) B976103
theorem B454567 : Blo 447780 454567 := bstep (se 1 (by rfl) ⟨340925, by rfl⟩ : syracuseStep 454567 = 681851) B681851
theorem B651487 : Blo 447780 651487 := bstep (se 1 (by rfl) ⟨488615, by rfl⟩ : syracuseStep 651487 = 977231) B977231
theorem B6484319 : Blo 447780 6484319 := bstep (se 1 (by rfl) ⟨4863239, by rfl⟩ : syracuseStep 6484319 = 9726479) B9726479
theorem B25981559 : Blo 447780 25981559 := bstep (se 1 (by rfl) ⟨19486169, by rfl⟩ : syracuseStep 25981559 = 38972339) B38972339
theorem B4321957 : Blo 447780 4321957 := bstep (se 4 (by rfl) ⟨405183, by rfl⟩ : syracuseStep 4321957 = 810367) B810367
theorem B1702079 : Blo 447780 1702079 := bstep (se 1 (by rfl) ⟨1276559, by rfl⟩ : syracuseStep 1702079 = 2553119) B2553119
theorem B1538423 : Blo 447780 1538423 := bstep (se 1 (by rfl) ⟨1153817, by rfl⟩ : syracuseStep 1538423 = 2307635) B2307635
theorem B1538461 : Blo 447780 1538461 := bstep (se 3 (by rfl) ⟨288461, by rfl⟩ : syracuseStep 1538461 = 576923) B576923
theorem B7797179 : Blo 447780 7797179 := bstep (se 1 (by rfl) ⟨5847884, by rfl⟩ : syracuseStep 7797179 = 11695769) B11695769
theorem B3242911 : Blo 447780 3242911 := bstep (se 1 (by rfl) ⟨2432183, by rfl⟩ : syracuseStep 3242911 = 4864367) B4864367
theorem B51412151 : Blo 447780 51412151 := bstep (se 1 (by rfl) ⟨38559113, by rfl⟩ : syracuseStep 51412151 = 77118227) B77118227
theorem B2162209 : Blo 447780 2162209 := bstep (se 2 (by rfl) ⟨810828, by rfl⟩ : syracuseStep 2162209 = 1621657) B1621657
theorem B1015433 : Blo 447780 1015433 := bstep (se 2 (by rfl) ⟨380787, by rfl⟩ : syracuseStep 1015433 = 761575) B761575
theorem B1277801 : Blo 447780 1277801 := bstep (se 2 (by rfl) ⟨479175, by rfl⟩ : syracuseStep 1277801 = 958351) B958351
theorem B1015775 : Blo 447780 1015775 := bstep (se 1 (by rfl) ⟨761831, by rfl⟩ : syracuseStep 1015775 = 1523663) B1523663
theorem B23396509 : Blo 447780 23396509 := bstep (se 3 (by rfl) ⟨4386845, by rfl⟩ : syracuseStep 23396509 = 8773691) B8773691
theorem B1015991 : Blo 447780 1015991 := bstep (se 1 (by rfl) ⟨761993, by rfl⟩ : syracuseStep 1015991 = 1523987) B1523987
theorem B4882963 : Blo 447780 4882963 := bstep (se 1 (by rfl) ⟨3662222, by rfl⟩ : syracuseStep 4882963 = 7324445) B7324445
theorem B852763 : Blo 447780 852763 := bstep (se 1 (by rfl) ⟨639572, by rfl⟩ : syracuseStep 852763 = 1279145) B1279145
theorem B1705799 : Blo 447780 1705799 := bstep (se 1 (by rfl) ⟨1279349, by rfl⟩ : syracuseStep 1705799 = 2558699) B2558699
theorem B3082121 : Blo 447780 3082121 := bstep (se 2 (by rfl) ⟨1155795, by rfl⟩ : syracuseStep 3082121 = 2311591) B2311591
theorem B854327 : Blo 447780 854327 := bstep (se 1 (by rfl) ⟨640745, by rfl⟩ : syracuseStep 854327 = 1281491) B1281491
theorem B4852169 : Blo 447780 4852169 := bstep (se 2 (by rfl) ⟨1819563, by rfl⟩ : syracuseStep 4852169 = 3639127) B3639127
theorem B7310047 : Blo 447780 7310047 := bstep (se 1 (by rfl) ⟨5482535, by rfl⟩ : syracuseStep 7310047 = 10965071) B10965071
theorem B2165575 : Blo 447780 2165575 := bstep (se 1 (by rfl) ⟨1624181, by rfl⟩ : syracuseStep 2165575 = 3248363) B3248363
theorem B2166209 : Blo 447780 2166209 := bstep (se 2 (by rfl) ⟨812328, by rfl⟩ : syracuseStep 2166209 = 1624657) B1624657
theorem B12979709 : Blo 447780 12979709 := bstep (se 3 (by rfl) ⟨2433695, by rfl⟩ : syracuseStep 12979709 = 4867391) B4867391
theorem B3247901 : Blo 447780 3247901 := bstep (se 3 (by rfl) ⟨608981, by rfl⟩ : syracuseStep 3247901 = 1217963) B1217963
theorem B2559883 : Blo 447780 2559883 := bstep (se 1 (by rfl) ⟨1919912, by rfl⟩ : syracuseStep 2559883 = 3839825) B3839825
theorem B10490143 : Blo 447780 10490143 := bstep (se 1 (by rfl) ⟨7867607, by rfl⟩ : syracuseStep 10490143 = 15735215) B15735215
theorem B856423 : Blo 447780 856423 := bstep (se 1 (by rfl) ⟨642317, by rfl⟩ : syracuseStep 856423 = 1284635) B1284635
theorem B9999389 : Blo 447780 9999389 := bstep (se 3 (by rfl) ⟨1874885, by rfl⟩ : syracuseStep 9999389 = 3749771) B3749771
theorem B1283485 : Blo 447780 1283485 := bstep (se 3 (by rfl) ⟨240653, by rfl⟩ : syracuseStep 1283485 = 481307) B481307
theorem B8852975 : Blo 447780 8852975 := bstep (se 1 (by rfl) ⟨6639731, by rfl⟩ : syracuseStep 8852975 = 13279463) B13279463
theorem B1283759 : Blo 447780 1283759 := bstep (se 1 (by rfl) ⟨962819, by rfl⟩ : syracuseStep 1283759 = 1925639) B1925639
theorem B8197969 : Blo 447780 8197969 := bstep (se 2 (by rfl) ⟨3074238, by rfl⟩ : syracuseStep 8197969 = 6148477) B6148477
theorem B1513943 : Blo 447780 1513943 := bstep (se 1 (by rfl) ⟨1135457, by rfl⟩ : syracuseStep 1513943 = 2270915) B2270915
theorem B1153703 : Blo 447780 1153703 := bstep (se 1 (by rfl) ⟨865277, by rfl⟩ : syracuseStep 1153703 = 1730555) B1730555
theorem B2267999 : Blo 447780 2267999 := bstep (se 1 (by rfl) ⟨1700999, by rfl⟩ : syracuseStep 2267999 = 3401999) B3401999
theorem B957599 : Blo 447780 957599 := bstep (se 1 (by rfl) ⟨718199, by rfl⟩ : syracuseStep 957599 = 1436399) B1436399
theorem B1515347 : Blo 447780 1515347 := bstep (se 1 (by rfl) ⟨1136510, by rfl⟩ : syracuseStep 1515347 = 2273021) B2273021
theorem B1515455 : Blo 447780 1515455 := bstep (se 1 (by rfl) ⟨1136591, by rfl⟩ : syracuseStep 1515455 = 2273183) B2273183
theorem B2564783 : Blo 447780 2564783 := bstep (se 1 (by rfl) ⟨1923587, by rfl⟩ : syracuseStep 2564783 = 3847175) B3847175
theorem B10953589 : Blo 447780 10953589 := bstep (se 5 (by rfl) ⟨513449, by rfl⟩ : syracuseStep 10953589 = 1026899) B1026899
theorem B1025615 : Blo 447780 1025615 := bstep (se 1 (by rfl) ⟨769211, by rfl⟩ : syracuseStep 1025615 = 1538423) B1538423
theorem B1517831 : Blo 447780 1517831 := bstep (se 1 (by rfl) ⟨1138373, by rfl⟩ : syracuseStep 1517831 = 2276747) B2276747
theorem B1517993 : Blo 447780 1517993 := bstep (se 2 (by rfl) ⟨569247, by rfl⟩ : syracuseStep 1517993 = 1138495) B1138495
theorem B10169003 : Blo 447780 10169003 := bstep (se 1 (by rfl) ⟨7626752, by rfl⟩ : syracuseStep 10169003 = 15253505) B15253505
theorem B4336411 : Blo 447780 4336411 := bstep (se 1 (by rfl) ⟨3252308, by rfl⟩ : syracuseStep 4336411 = 6504617) B6504617
theorem B1157971 : Blo 447780 1157971 := bstep (se 1 (by rfl) ⟨868478, by rfl⟩ : syracuseStep 1157971 = 1736957) B1736957
theorem B8793647 : Blo 447780 8793647 := bstep (se 1 (by rfl) ⟨6595235, by rfl⟩ : syracuseStep 8793647 = 13190471) B13190471
theorem B962383 : Blo 447780 962383 := bstep (se 1 (by rfl) ⟨721787, by rfl⟩ : syracuseStep 962383 = 1443575) B1443575
theorem B4304735 : Blo 447780 4304735 := bstep (se 1 (by rfl) ⟨3228551, by rfl⟩ : syracuseStep 4304735 = 6457103) B6457103
theorem B16822403 : Blo 447780 16822403 := bstep (se 1 (by rfl) ⟨12616802, by rfl⟩ : syracuseStep 16822403 = 25233605) B25233605
theorem B1519991 : Blo 447780 1519991 := bstep (se 1 (by rfl) ⟨1139993, by rfl⟩ : syracuseStep 1519991 = 2279987) B2279987
theorem B3289673 : Blo 447780 3289673 := bstep (se 2 (by rfl) ⟨1233627, by rfl⟩ : syracuseStep 3289673 = 2467255) B2467255
theorem B570235 : Blo 447780 570235 := bstep (se 1 (by rfl) ⟨427676, by rfl⟩ : syracuseStep 570235 = 855353) B855353
theorem B505471 : Blo 447780 505471 := bstep (se 1 (by rfl) ⟨379103, by rfl⟩ : syracuseStep 505471 = 758207) B758207
theorem B571207 : Blo 447780 571207 := bstep (se 1 (by rfl) ⟨428405, by rfl⟩ : syracuseStep 571207 = 856811) B856811
theorem B2570615 : Blo 447780 2570615 := bstep (se 1 (by rfl) ⟨1927961, by rfl⟩ : syracuseStep 2570615 = 3855923) B3855923
theorem B506335 : Blo 447780 506335 := bstep (se 1 (by rfl) ⟨379751, by rfl⟩ : syracuseStep 506335 = 759503) B759503
theorem B506587 : Blo 447780 506587 := bstep (se 1 (by rfl) ⟨379940, by rfl⟩ : syracuseStep 506587 = 759881) B759881
theorem B507631 : Blo 447780 507631 := bstep (se 1 (by rfl) ⟨380723, by rfl⟩ : syracuseStep 507631 = 761447) B761447
theorem B2735869 : Blo 447780 2735869 := bstep (se 3 (by rfl) ⟨512975, by rfl⟩ : syracuseStep 2735869 = 1025951) B1025951
theorem B606089 : Blo 447780 606089 := bstep (se 2 (by rfl) ⟨227283, by rfl⟩ : syracuseStep 606089 = 454567) B454567
theorem B1622119 : Blo 447780 1622119 := bstep (se 1 (by rfl) ⟨1216589, by rfl⟩ : syracuseStep 1622119 = 2433179) B2433179
theorem B868649 : Blo 447780 868649 := bstep (se 2 (by rfl) ⟨325743, by rfl⟩ : syracuseStep 868649 = 651487) B651487
theorem B1524095 : Blo 447780 1524095 := bstep (se 1 (by rfl) ⟨1143071, by rfl⟩ : syracuseStep 1524095 = 2286143) B2286143
theorem B672311 : Blo 447780 672311 := bstep (se 1 (by rfl) ⟨504233, by rfl⟩ : syracuseStep 672311 = 1008467) B1008467
theorem B3424841 : Blo 447780 3424841 := bstep (se 2 (by rfl) ⟨1284315, by rfl⟩ : syracuseStep 3424841 = 2568631) B2568631
theorem B672347 : Blo 447780 672347 := bstep (se 1 (by rfl) ⟨504260, by rfl⟩ : syracuseStep 672347 = 1008521) B1008521
theorem B672575 : Blo 447780 672575 := bstep (se 1 (by rfl) ⟨504431, by rfl⟩ : syracuseStep 672575 = 1008863) B1008863
theorem B672719 : Blo 447780 672719 := bstep (se 1 (by rfl) ⟨504539, by rfl⟩ : syracuseStep 672719 = 1009079) B1009079
theorem B20792477 : Blo 447780 20792477 := bstep (se 3 (by rfl) ⟨3898589, by rfl⟩ : syracuseStep 20792477 = 7797179) B7797179
theorem B3851549 : Blo 447780 3851549 := bstep (se 3 (by rfl) ⟨722165, by rfl⟩ : syracuseStep 3851549 = 1444331) B1444331
theorem B640649 : Blo 447780 640649 := bstep (se 2 (by rfl) ⟨240243, by rfl⟩ : syracuseStep 640649 = 480487) B480487
theorem B1296253 : Blo 447780 1296253 := bstep (se 3 (by rfl) ⟨243047, by rfl⟩ : syracuseStep 1296253 = 486095) B486095
theorem B673883 : Blo 447780 673883 := bstep (se 1 (by rfl) ⟨505412, by rfl⟩ : syracuseStep 673883 = 1010825) B1010825
theorem B673919 : Blo 447780 673919 := bstep (se 1 (by rfl) ⟨505439, by rfl⟩ : syracuseStep 673919 = 1010879) B1010879
theorem B20761427 : Blo 447780 20761427 := bstep (se 1 (by rfl) ⟨15571070, by rfl⟩ : syracuseStep 20761427 = 31142141) B31142141
theorem B510823 : Blo 447780 510823 := bstep (se 1 (by rfl) ⟨383117, by rfl⟩ : syracuseStep 510823 = 766235) B766235
theorem B17321039 : Blo 447780 17321039 := bstep (se 1 (by rfl) ⟨12990779, by rfl⟩ : syracuseStep 17321039 = 25981559) B25981559
theorem B2051281 : Blo 447780 2051281 := bstep (se 2 (by rfl) ⟨769230, by rfl⟩ : syracuseStep 2051281 = 1538461) B1538461
theorem B1134719 : Blo 447780 1134719 := bstep (se 1 (by rfl) ⟨851039, by rfl⟩ : syracuseStep 1134719 = 1702079) B1702079
theorem B2281607 : Blo 447780 2281607 := bstep (se 1 (by rfl) ⟨1711205, by rfl⟩ : syracuseStep 2281607 = 3422411) B3422411
theorem B2281769 : Blo 447780 2281769 := bstep (se 2 (by rfl) ⟨855663, by rfl⟩ : syracuseStep 2281769 = 1711327) B1711327
theorem B971689 : Blo 447780 971689 := bstep (se 2 (by rfl) ⟨364383, by rfl⟩ : syracuseStep 971689 = 728767) B728767
theorem B1168361 : Blo 447780 1168361 := bstep (se 2 (by rfl) ⟨438135, by rfl⟩ : syracuseStep 1168361 = 876271) B876271
theorem B676955 : Blo 447780 676955 := bstep (se 1 (by rfl) ⟨507716, by rfl⟩ : syracuseStep 676955 = 1015433) B1015433
theorem B1365257 : Blo 447780 1365257 := bstep (se 2 (by rfl) ⟨511971, by rfl⟩ : syracuseStep 1365257 = 1023943) B1023943
theorem B677183 : Blo 447780 677183 := bstep (se 1 (by rfl) ⟨507887, by rfl⟩ : syracuseStep 677183 = 1015775) B1015775
theorem B447847 : Blo 447780 447847 := bstep (se 1 (by rfl) ⟨335885, by rfl⟩ : syracuseStep 447847 = 671771) B671771
theorem B448027 : Blo 447780 448027 := bstep (se 1 (by rfl) ⟨336020, by rfl⟩ : syracuseStep 448027 = 672041) B672041
theorem B677417 : Blo 447780 677417 := bstep (se 2 (by rfl) ⟨254031, by rfl⟩ : syracuseStep 677417 = 508063) B508063
theorem B448127 : Blo 447780 448127 := bstep (se 1 (by rfl) ⟨336095, by rfl⟩ : syracuseStep 448127 = 672191) B672191
theorem B5101541 : Blo 447780 5101541 := bstep (se 4 (by rfl) ⟨478269, by rfl⟩ : syracuseStep 5101541 = 956539) B956539
theorem B448539 : Blo 447780 448539 := bstep (se 1 (by rfl) ⟨336404, by rfl⟩ : syracuseStep 448539 = 672809) B672809
theorem B3856571 : Blo 447780 3856571 := bstep (se 1 (by rfl) ⟨2892428, by rfl⟩ : syracuseStep 3856571 = 5784857) B5784857
theorem B1136875 : Blo 447780 1136875 := bstep (se 1 (by rfl) ⟨852656, by rfl⟩ : syracuseStep 1136875 = 1705313) B1705313
theorem B3463687 : Blo 447780 3463687 := bstep (se 1 (by rfl) ⟨2597765, by rfl⟩ : syracuseStep 3463687 = 5195531) B5195531
theorem B449519 : Blo 447780 449519 := bstep (se 1 (by rfl) ⟨337139, by rfl⟩ : syracuseStep 449519 = 674279) B674279
theorem B449639 : Blo 447780 449639 := bstep (se 1 (by rfl) ⟨337229, by rfl⟩ : syracuseStep 449639 = 674459) B674459
theorem B449663 : Blo 447780 449663 := bstep (se 1 (by rfl) ⟨337247, by rfl⟩ : syracuseStep 449663 = 674495) B674495
theorem B450031 : Blo 447780 450031 := bstep (se 1 (by rfl) ⟨337523, by rfl⟩ : syracuseStep 450031 = 675047) B675047
theorem B8740585 : Blo 447780 8740585 := bstep (se 2 (by rfl) ⟨3277719, by rfl⟩ : syracuseStep 8740585 = 6555439) B6555439
theorem B2875337 : Blo 447780 2875337 := bstep (se 2 (by rfl) ⟨1078251, by rfl⟩ : syracuseStep 2875337 = 2156503) B2156503
theorem B1007585 : Blo 447780 1007585 := bstep (se 2 (by rfl) ⟨377844, by rfl⟩ : syracuseStep 1007585 = 755689) B755689
theorem B450799 : Blo 447780 450799 := bstep (se 1 (by rfl) ⟨338099, by rfl⟩ : syracuseStep 450799 = 676199) B676199
theorem B1008107 : Blo 447780 1008107 := bstep (se 1 (by rfl) ⟨756080, by rfl⟩ : syracuseStep 1008107 = 1512161) B1512161
theorem B1008233 : Blo 447780 1008233 := bstep (se 2 (by rfl) ⟨378087, by rfl⟩ : syracuseStep 1008233 = 756175) B756175
theorem B1139579 : Blo 447780 1139579 := bstep (se 1 (by rfl) ⟨854684, by rfl⟩ : syracuseStep 1139579 = 1709369) B1709369
theorem B451655 : Blo 447780 451655 := bstep (se 1 (by rfl) ⟨338741, by rfl⟩ : syracuseStep 451655 = 677483) B677483
theorem B1140095 : Blo 447780 1140095 := bstep (se 1 (by rfl) ⟨855071, by rfl⟩ : syracuseStep 1140095 = 1710143) B1710143
theorem B11494871 : Blo 447780 11494871 := bstep (se 1 (by rfl) ⟨8621153, by rfl⟩ : syracuseStep 11494871 = 17242307) B17242307
theorem B5137991 : Blo 447780 5137991 := bstep (se 1 (by rfl) ⟨3853493, by rfl⟩ : syracuseStep 5137991 = 7706987) B7706987
theorem B1009259 : Blo 447780 1009259 := bstep (se 1 (by rfl) ⟨756944, by rfl⟩ : syracuseStep 1009259 = 1513889) B1513889
theorem B1009385 : Blo 447780 1009385 := bstep (se 2 (by rfl) ⟨378519, by rfl⟩ : syracuseStep 1009385 = 757039) B757039
theorem B1009529 : Blo 447780 1009529 := bstep (se 2 (by rfl) ⟨378573, by rfl⟩ : syracuseStep 1009529 = 757147) B757147
theorem B2156827 : Blo 447780 2156827 := bstep (se 1 (by rfl) ⟨1617620, by rfl⟩ : syracuseStep 2156827 = 3235241) B3235241
theorem B1009961 : Blo 447780 1009961 := bstep (se 2 (by rfl) ⟨378735, by rfl⟩ : syracuseStep 1009961 = 757471) B757471
theorem B6941173 : Blo 447780 6941173 := bstep (se 5 (by rfl) ⟨325367, by rfl⟩ : syracuseStep 6941173 = 650735) B650735
theorem B1010537 : Blo 447780 1010537 := bstep (se 2 (by rfl) ⟨378951, by rfl⟩ : syracuseStep 1010537 = 757903) B757903
theorem B682921 : Blo 447780 682921 := bstep (se 2 (by rfl) ⟨256095, by rfl⟩ : syracuseStep 682921 = 512191) B512191
theorem B1141715 : Blo 447780 1141715 := bstep (se 1 (by rfl) ⟨856286, by rfl⟩ : syracuseStep 1141715 = 1712573) B1712573
theorem B2157673 : Blo 447780 2157673 := bstep (se 2 (by rfl) ⟨809127, by rfl⟩ : syracuseStep 2157673 = 1618255) B1618255
theorem B5762609 : Blo 447780 5762609 := bstep (se 2 (by rfl) ⟨2160978, by rfl⟩ : syracuseStep 5762609 = 4321957) B4321957
theorem B1011527 : Blo 447780 1011527 := bstep (se 1 (by rfl) ⟨758645, by rfl⟩ : syracuseStep 1011527 = 1517291) B1517291
theorem B3830327 : Blo 447780 3830327 := bstep (se 1 (by rfl) ⟨2872745, by rfl⟩ : syracuseStep 3830327 = 5745491) B5745491
theorem B6943643 : Blo 447780 6943643 := bstep (se 1 (by rfl) ⟨5207732, by rfl⟩ : syracuseStep 6943643 = 10415465) B10415465
theorem B4322879 : Blo 447780 4322879 := bstep (se 1 (by rfl) ⟨3242159, by rfl⟩ : syracuseStep 4322879 = 6484319) B6484319
theorem B1013615 : Blo 447780 1013615 := bstep (se 1 (by rfl) ⟨760211, by rfl⟩ : syracuseStep 1013615 = 1520423) B1520423
theorem B1014011 : Blo 447780 1014011 := bstep (se 1 (by rfl) ⟨760508, by rfl⟩ : syracuseStep 1014011 = 1521017) B1521017
theorem B1210793 : Blo 447780 1210793 := bstep (se 2 (by rfl) ⟨454047, by rfl⟩ : syracuseStep 1210793 = 908095) B908095
theorem B5339627 : Blo 447780 5339627 := bstep (se 1 (by rfl) ⟨4004720, by rfl⟩ : syracuseStep 5339627 = 8009441) B8009441
theorem B4323881 : Blo 447780 4323881 := bstep (se 2 (by rfl) ⟨1621455, by rfl⟩ : syracuseStep 4323881 = 3242911) B3242911
theorem B2882945 : Blo 447780 2882945 := bstep (se 2 (by rfl) ⟨1081104, by rfl⟩ : syracuseStep 2882945 = 2162209) B2162209
theorem B34274767 : Blo 447780 34274767 := bstep (se 1 (by rfl) ⟨25706075, by rfl⟩ : syracuseStep 34274767 = 51412151) B51412151
theorem B1015343 : Blo 447780 1015343 := bstep (se 1 (by rfl) ⟨761507, by rfl⟩ : syracuseStep 1015343 = 1523015) B1523015
theorem B851867 : Blo 447780 851867 := bstep (se 1 (by rfl) ⟨638900, by rfl⟩ : syracuseStep 851867 = 1277801) B1277801
theorem B2162825 : Blo 447780 2162825 := bstep (se 2 (by rfl) ⟨811059, by rfl⟩ : syracuseStep 2162825 = 1622119) B1622119
theorem B1016063 : Blo 447780 1016063 := bstep (se 1 (by rfl) ⟨762047, by rfl⟩ : syracuseStep 1016063 = 1524095) B1524095
theorem B13861651 : Blo 447780 13861651 := bstep (se 1 (by rfl) ⟨10396238, by rfl⟩ : syracuseStep 13861651 = 20792477) B20792477
theorem B124781381 : Blo 447780 124781381 := bstep (se 4 (by rfl) ⟨11698254, by rfl⟩ : syracuseStep 124781381 = 23396509) B23396509
theorem B1444139 : Blo 447780 1444139 := bstep (se 1 (by rfl) ⟨1083104, by rfl⟩ : syracuseStep 1444139 = 2166209) B2166209
theorem B8653139 : Blo 447780 8653139 := bstep (se 1 (by rfl) ⟨6489854, by rfl⟩ : syracuseStep 8653139 = 12979709) B12979709
theorem B2165267 : Blo 447780 2165267 := bstep (se 1 (by rfl) ⟨1623950, by rfl⟩ : syracuseStep 2165267 = 3247901) B3247901
theorem B756479 : Blo 447780 756479 := bstep (se 1 (by rfl) ⟨567359, by rfl⟩ : syracuseStep 756479 = 1134719) B1134719
theorem B5901983 : Blo 447780 5901983 := bstep (se 1 (by rfl) ⟨4426487, by rfl⟩ : syracuseStep 5901983 = 8852975) B8852975
theorem B2887433 : Blo 447780 2887433 := bstep (se 2 (by rfl) ⟨1082787, by rfl⟩ : syracuseStep 2887433 = 2165575) B2165575
theorem B1543961 : Blo 447780 1543961 := bstep (se 2 (by rfl) ⟨578985, by rfl⟩ : syracuseStep 1543961 = 1157971) B1157971
theorem B855839 : Blo 447780 855839 := bstep (se 1 (by rfl) ⟨641879, by rfl⟩ : syracuseStep 855839 = 1283759) B1283759
theorem B1708397 : Blo 447780 1708397 := bstep (se 3 (by rfl) ⟨320324, by rfl⟩ : syracuseStep 1708397 = 640649) B640649
theorem B12915125 : Blo 447780 12915125 := bstep (se 5 (by rfl) ⟨605396, by rfl⟩ : syracuseStep 12915125 = 1210793) B1210793
theorem B1511999 : Blo 447780 1511999 := bstep (se 1 (by rfl) ⟨1133999, by rfl⟩ : syracuseStep 1511999 = 2267999) B2267999
theorem B1283177 : Blo 447780 1283177 := bstep (se 2 (by rfl) ⟨481191, by rfl⟩ : syracuseStep 1283177 = 962383) B962383
theorem B3413177 : Blo 447780 3413177 := bstep (se 2 (by rfl) ⟨1279941, by rfl⟩ : syracuseStep 3413177 = 2559883) B2559883
theorem B1709855 : Blo 447780 1709855 := bstep (se 1 (by rfl) ⟨1282391, by rfl⟩ : syracuseStep 1709855 = 2564783) B2564783
theorem B759719 : Blo 447780 759719 := bstep (se 1 (by rfl) ⟨569789, by rfl⟩ : syracuseStep 759719 = 1139579) B1139579
theorem B760063 : Blo 447780 760063 := bstep (se 1 (by rfl) ⟨570047, by rfl⟩ : syracuseStep 760063 = 1140095) B1140095
theorem B760313 : Blo 447780 760313 := bstep (se 2 (by rfl) ⟨285117, by rfl⟩ : syracuseStep 760313 = 570235) B570235
theorem B1711313 : Blo 447780 1711313 := bstep (se 2 (by rfl) ⟨641742, by rfl⟩ : syracuseStep 1711313 = 1283485) B1283485
theorem B761143 : Blo 447780 761143 := bstep (se 1 (by rfl) ⟨570857, by rfl⟩ : syracuseStep 761143 = 1141715) B1141715
theorem B3841739 : Blo 447780 3841739 := bstep (se 1 (by rfl) ⟨2881304, by rfl⟩ : syracuseStep 3841739 = 5762609) B5762609
theorem B761609 : Blo 447780 761609 := bstep (se 2 (by rfl) ⟨285603, by rfl⟩ : syracuseStep 761609 = 571207) B571207
theorem B11214935 : Blo 447780 11214935 := bstep (se 1 (by rfl) ⟨8411201, by rfl⟩ : syracuseStep 11214935 = 16822403) B16822403
theorem B1515833 : Blo 447780 1515833 := bstep (se 2 (by rfl) ⟨568437, by rfl⟩ : syracuseStep 1515833 = 1136875) B1136875
theorem B4629095 : Blo 447780 4629095 := bstep (se 1 (by rfl) ⟨3471821, by rfl⟩ : syracuseStep 4629095 = 6943643) B6943643
theorem B1713743 : Blo 447780 1713743 := bstep (se 1 (by rfl) ⟨1285307, by rfl⟩ : syracuseStep 1713743 = 2570615) B2570615
theorem B3647825 : Blo 447780 3647825 := bstep (se 2 (by rfl) ⟨1367934, by rfl⟩ : syracuseStep 3647825 = 2735869) B2735869
theorem B1616237 : Blo 447780 1616237 := bstep (se 3 (by rfl) ⟨303044, by rfl⟩ : syracuseStep 1616237 = 606089) B606089
theorem B567911 : Blo 447780 567911 := bstep (se 1 (by rfl) ⟨425933, by rfl⟩ : syracuseStep 567911 = 851867) B851867
theorem B2567699 : Blo 447780 2567699 := bstep (se 1 (by rfl) ⟨1925774, by rfl⟩ : syracuseStep 2567699 = 3851549) B3851549
theorem B13840951 : Blo 447780 13840951 := bstep (se 1 (by rfl) ⟨10380713, by rfl⟩ : syracuseStep 13840951 = 20761427) B20761427
theorem B11547359 : Blo 447780 11547359 := bstep (se 1 (by rfl) ⟨8660519, by rfl⟩ : syracuseStep 11547359 = 17321039) B17321039
theorem B1521071 : Blo 447780 1521071 := bstep (se 1 (by rfl) ⟨1140803, by rfl⟩ : syracuseStep 1521071 = 2281607) B2281607
theorem B1521179 : Blo 447780 1521179 := bstep (se 1 (by rfl) ⟨1140884, by rfl⟩ : syracuseStep 1521179 = 2281769) B2281769
theorem B9254897 : Blo 447780 9254897 := bstep (se 2 (by rfl) ⟨3470586, by rfl⟩ : syracuseStep 9254897 = 6941173) B6941173
theorem B6666259 : Blo 447780 6666259 := bstep (se 1 (by rfl) ⟨4999694, by rfl⟩ : syracuseStep 6666259 = 9999389) B9999389
theorem B9746729 : Blo 447780 9746729 := bstep (se 2 (by rfl) ⟨3655023, by rfl⟩ : syracuseStep 9746729 = 7310047) B7310047
theorem B5781881 : Blo 447780 5781881 := bstep (se 2 (by rfl) ⟨2168205, by rfl⟩ : syracuseStep 5781881 = 4336411) B4336411
theorem B2571047 : Blo 447780 2571047 := bstep (se 1 (by rfl) ⟨1928285, by rfl⟩ : syracuseStep 2571047 = 3856571) B3856571
theorem B2735041 : Blo 447780 2735041 := bstep (se 2 (by rfl) ⟨1025640, by rfl⟩ : syracuseStep 2735041 = 2051281) B2051281
theorem B638399 : Blo 447780 638399 := bstep (se 1 (by rfl) ⟨478799, by rfl⟩ : syracuseStep 638399 = 957599) B957599
theorem B1916891 : Blo 447780 1916891 := bstep (se 1 (by rfl) ⟨1437668, by rfl⟩ : syracuseStep 1916891 = 2875337) B2875337
theorem B671723 : Blo 447780 671723 := bstep (se 1 (by rfl) ⟨503792, by rfl⟩ : syracuseStep 671723 = 1007585) B1007585
theorem B672071 : Blo 447780 672071 := bstep (se 1 (by rfl) ⟨504053, by rfl⟩ : syracuseStep 672071 = 1008107) B1008107
theorem B672155 : Blo 447780 672155 := bstep (se 1 (by rfl) ⟨504116, by rfl⟩ : syracuseStep 672155 = 1008233) B1008233
theorem B2278205 : Blo 447780 2278205 := bstep (se 3 (by rfl) ⟨427163, by rfl⟩ : syracuseStep 2278205 = 854327) B854327
theorem B3425327 : Blo 447780 3425327 := bstep (se 1 (by rfl) ⟨2568995, by rfl⟩ : syracuseStep 3425327 = 5137991) B5137991
theorem B672839 : Blo 447780 672839 := bstep (se 1 (by rfl) ⟨504629, by rfl⟩ : syracuseStep 672839 = 1009259) B1009259
theorem B672923 : Blo 447780 672923 := bstep (se 1 (by rfl) ⟨504692, by rfl⟩ : syracuseStep 672923 = 1009385) B1009385
theorem B1295585 : Blo 447780 1295585 := bstep (se 2 (by rfl) ⟨485844, by rfl⟩ : syracuseStep 1295585 = 971689) B971689
theorem B673019 : Blo 447780 673019 := bstep (se 1 (by rfl) ⟨504764, by rfl⟩ : syracuseStep 673019 = 1009529) B1009529
theorem B673307 : Blo 447780 673307 := bstep (se 1 (by rfl) ⟨504980, by rfl⟩ : syracuseStep 673307 = 1009961) B1009961
theorem B673691 : Blo 447780 673691 := bstep (se 1 (by rfl) ⟨505268, by rfl⟩ : syracuseStep 673691 = 1010537) B1010537
theorem B673961 : Blo 447780 673961 := bstep (se 2 (by rfl) ⟨252735, by rfl⟩ : syracuseStep 673961 = 505471) B505471
theorem B10930625 : Blo 447780 10930625 := bstep (se 2 (by rfl) ⟨4098984, by rfl⟩ : syracuseStep 10930625 = 8197969) B8197969
theorem B674351 : Blo 447780 674351 := bstep (se 1 (by rfl) ⟨505763, by rfl⟩ : syracuseStep 674351 = 1011527) B1011527
theorem B2869823 : Blo 447780 2869823 := bstep (se 1 (by rfl) ⟨2152367, by rfl⟩ : syracuseStep 2869823 = 4304735) B4304735
theorem B675113 : Blo 447780 675113 := bstep (se 2 (by rfl) ⟨253167, by rfl⟩ : syracuseStep 675113 = 506335) B506335
theorem B675449 : Blo 447780 675449 := bstep (se 2 (by rfl) ⟨253293, by rfl⟩ : syracuseStep 675449 = 506587) B506587
theorem B675743 : Blo 447780 675743 := bstep (se 1 (by rfl) ⟨506807, by rfl⟩ : syracuseStep 675743 = 1013615) B1013615
theorem B676007 : Blo 447780 676007 := bstep (se 1 (by rfl) ⟨507005, by rfl⟩ : syracuseStep 676007 = 1014011) B1014011
theorem B3559751 : Blo 447780 3559751 := bstep (se 1 (by rfl) ⟨2669813, by rfl⟩ : syracuseStep 3559751 = 5339627) B5339627
theorem B45699689 : Blo 447780 45699689 := bstep (se 2 (by rfl) ⟨17137383, by rfl⟩ : syracuseStep 45699689 = 34274767) B34274767
theorem B1921963 : Blo 447780 1921963 := bstep (se 1 (by rfl) ⟨1441472, by rfl⟩ : syracuseStep 1921963 = 2882945) B2882945
theorem B11654113 : Blo 447780 11654113 := bstep (se 2 (by rfl) ⟨4370292, by rfl⟩ : syracuseStep 11654113 = 8740585) B8740585
theorem B676841 : Blo 447780 676841 := bstep (se 2 (by rfl) ⟨253815, by rfl⟩ : syracuseStep 676841 = 507631) B507631
theorem B676895 : Blo 447780 676895 := bstep (se 1 (by rfl) ⟨507671, by rfl⟩ : syracuseStep 676895 = 1015343) B1015343
theorem B677327 : Blo 447780 677327 := bstep (se 1 (by rfl) ⟨507995, by rfl⟩ : syracuseStep 677327 = 1015991) B1015991
theorem B448207 : Blo 447780 448207 := bstep (se 1 (by rfl) ⟨336155, by rfl⟩ : syracuseStep 448207 = 672311) B672311
theorem B2283227 : Blo 447780 2283227 := bstep (se 1 (by rfl) ⟨1712420, by rfl⟩ : syracuseStep 2283227 = 3424841) B3424841
theorem B448231 : Blo 447780 448231 := bstep (se 1 (by rfl) ⟨336173, by rfl⟩ : syracuseStep 448231 = 672347) B672347
theorem B448383 : Blo 447780 448383 := bstep (se 1 (by rfl) ⟨336287, by rfl⟩ : syracuseStep 448383 = 672575) B672575
theorem B448479 : Blo 447780 448479 := bstep (se 1 (by rfl) ⟨336359, by rfl⟩ : syracuseStep 448479 = 672719) B672719
theorem B6510617 : Blo 447780 6510617 := bstep (se 2 (by rfl) ⟨2441481, by rfl⟩ : syracuseStep 6510617 = 4882963) B4882963
theorem B1137017 : Blo 447780 1137017 := bstep (se 2 (by rfl) ⟨426381, by rfl⟩ : syracuseStep 1137017 = 852763) B852763
theorem B14604785 : Blo 447780 14604785 := bstep (se 2 (by rfl) ⟨5476794, by rfl⟩ : syracuseStep 14604785 = 10953589) B10953589
theorem B1137199 : Blo 447780 1137199 := bstep (se 1 (by rfl) ⟨852899, by rfl⟩ : syracuseStep 1137199 = 1705799) B1705799
theorem B2054747 : Blo 447780 2054747 := bstep (se 1 (by rfl) ⟨1541060, by rfl⟩ : syracuseStep 2054747 = 3082121) B3082121
theorem B449255 : Blo 447780 449255 := bstep (se 1 (by rfl) ⟨336941, by rfl⟩ : syracuseStep 449255 = 673883) B673883
theorem B449279 : Blo 447780 449279 := bstep (se 1 (by rfl) ⟨336959, by rfl⟩ : syracuseStep 449279 = 673919) B673919
theorem B3234779 : Blo 447780 3234779 := bstep (se 1 (by rfl) ⟨2426084, by rfl⟩ : syracuseStep 3234779 = 4852169) B4852169
theorem B18472997 : Blo 447780 18472997 := bstep (se 4 (by rfl) ⟨1731843, by rfl⟩ : syracuseStep 18472997 = 3463687) B3463687
theorem B2875769 : Blo 447780 2875769 := bstep (se 2 (by rfl) ⟨1078413, by rfl⟩ : syracuseStep 2875769 = 2156827) B2156827
theorem B9265589 : Blo 447780 9265589 := bstep (se 5 (by rfl) ⟨434324, by rfl⟩ : syracuseStep 9265589 = 868649) B868649
theorem B778907 : Blo 447780 778907 := bstep (se 1 (by rfl) ⟨584180, by rfl⟩ : syracuseStep 778907 = 1168361) B1168361
theorem B451303 : Blo 447780 451303 := bstep (se 1 (by rfl) ⟨338477, by rfl⟩ : syracuseStep 451303 = 676955) B676955
theorem B910171 : Blo 447780 910171 := bstep (se 1 (by rfl) ⟨682628, by rfl⟩ : syracuseStep 910171 = 1365257) B1365257
theorem B451455 : Blo 447780 451455 := bstep (se 1 (by rfl) ⟨338591, by rfl⟩ : syracuseStep 451455 = 677183) B677183
theorem B451611 : Blo 447780 451611 := bstep (se 1 (by rfl) ⟨338708, by rfl⟩ : syracuseStep 451611 = 677417) B677417
theorem B681097 : Blo 447780 681097 := bstep (se 2 (by rfl) ⟨255411, by rfl⟩ : syracuseStep 681097 = 510823) B510823
theorem B910561 : Blo 447780 910561 := bstep (se 2 (by rfl) ⟨341460, by rfl⟩ : syracuseStep 910561 = 682921) B682921
theorem B3401027 : Blo 447780 3401027 := bstep (se 1 (by rfl) ⟨2550770, by rfl⟩ : syracuseStep 3401027 = 5101541) B5101541
theorem B2876897 : Blo 447780 2876897 := bstep (se 2 (by rfl) ⟨1078836, by rfl⟩ : syracuseStep 2876897 = 2157673) B2157673
theorem B1009295 : Blo 447780 1009295 := bstep (se 1 (by rfl) ⟨756971, by rfl⟩ : syracuseStep 1009295 = 1513943) B1513943
theorem B1010231 : Blo 447780 1010231 := bstep (se 1 (by rfl) ⟨757673, by rfl⟩ : syracuseStep 1010231 = 1515347) B1515347
theorem B1010303 : Blo 447780 1010303 := bstep (se 1 (by rfl) ⟨757727, by rfl⟩ : syracuseStep 1010303 = 1515455) B1515455
theorem B13986857 : Blo 447780 13986857 := bstep (se 2 (by rfl) ⟨5245071, by rfl⟩ : syracuseStep 13986857 = 10490143) B10490143
theorem B1141897 : Blo 447780 1141897 := bstep (se 2 (by rfl) ⟨428211, by rfl⟩ : syracuseStep 1141897 = 856423) B856423
theorem B7663247 : Blo 447780 7663247 := bstep (se 1 (by rfl) ⟨5747435, by rfl⟩ : syracuseStep 7663247 = 11494871) B11494871
theorem B683743 : Blo 447780 683743 := bstep (se 1 (by rfl) ⟨512807, by rfl⟩ : syracuseStep 683743 = 1025615) B1025615
theorem B1011887 : Blo 447780 1011887 := bstep (se 1 (by rfl) ⟨758915, by rfl⟩ : syracuseStep 1011887 = 1517831) B1517831
theorem B1011995 : Blo 447780 1011995 := bstep (se 1 (by rfl) ⟨758996, by rfl⟩ : syracuseStep 1011995 = 1517993) B1517993
theorem B3076541 : Blo 447780 3076541 := bstep (se 3 (by rfl) ⟨576851, by rfl⟩ : syracuseStep 3076541 = 1153703) B1153703
theorem B6779335 : Blo 447780 6779335 := bstep (se 1 (by rfl) ⟨5084501, by rfl⟩ : syracuseStep 6779335 = 10169003) B10169003
theorem B5862431 : Blo 447780 5862431 := bstep (se 1 (by rfl) ⟨4396823, by rfl⟩ : syracuseStep 5862431 = 8793647) B8793647
theorem B1013327 : Blo 447780 1013327 := bstep (se 1 (by rfl) ⟨759995, by rfl⟩ : syracuseStep 1013327 = 1519991) B1519991
theorem B2553551 : Blo 447780 2553551 := bstep (se 1 (by rfl) ⟨1915163, by rfl⟩ : syracuseStep 2553551 = 3830327) B3830327
theorem B2193115 : Blo 447780 2193115 := bstep (se 1 (by rfl) ⟨1644836, by rfl⟩ : syracuseStep 2193115 = 3289673) B3289673
theorem B2881919 : Blo 447780 2881919 := bstep (se 1 (by rfl) ⟨2161439, by rfl⟩ : syracuseStep 2881919 = 4322879) B4322879
theorem B2882587 : Blo 447780 2882587 := bstep (se 1 (by rfl) ⟨2161940, by rfl⟩ : syracuseStep 2882587 = 4323881) B4323881
theorem B6913349 : Blo 447780 6913349 := bstep (se 4 (by rfl) ⟨648126, by rfl⟩ : syracuseStep 6913349 = 1296253) B1296253
theorem B1441883 : Blo 447780 1441883 := bstep (se 1 (by rfl) ⟨1081412, by rfl⟩ : syracuseStep 1441883 = 2162825) B2162825
theorem B18482201 : Blo 447780 18482201 := bstep (se 2 (by rfl) ⟨6930825, by rfl⟩ : syracuseStep 18482201 = 13861651) B13861651
theorem B1213561 : Blo 447780 1213561 := bstep (se 2 (by rfl) ⟨455085, by rfl⟩ : syracuseStep 1213561 = 910171) B910171
theorem B5768759 : Blo 447780 5768759 := bstep (se 1 (by rfl) ⟨4326569, by rfl⟩ : syracuseStep 5768759 = 8653139) B8653139
theorem B1214081 : Blo 447780 1214081 := bstep (se 2 (by rfl) ⟨455280, by rfl⟩ : syracuseStep 1214081 = 910561) B910561
theorem B1443511 : Blo 447780 1443511 := bstep (se 1 (by rfl) ⟨1082633, by rfl⟩ : syracuseStep 1443511 = 2165267) B2165267
theorem B3934655 : Blo 447780 3934655 := bstep (se 1 (by rfl) ⟨2950991, by rfl⟩ : syracuseStep 3934655 = 5901983) B5901983
theorem B855451 : Blo 447780 855451 := bstep (se 1 (by rfl) ⟨641588, by rfl⟩ : syracuseStep 855451 = 1283177) B1283177
theorem B758011 : Blo 447780 758011 := bstep (se 1 (by rfl) ⟨568508, by rfl⟩ : syracuseStep 758011 = 1137017) B1137017
theorem B9736523 : Blo 447780 9736523 := bstep (se 1 (by rfl) ⟨7302392, by rfl⟩ : syracuseStep 9736523 = 14604785) B14604785
theorem B2561159 : Blo 447780 2561159 := bstep (se 1 (by rfl) ⟨1920869, by rfl⟩ : syracuseStep 2561159 = 3841739) B3841739
theorem B7476623 : Blo 447780 7476623 := bstep (se 1 (by rfl) ⟨5607467, by rfl⟩ : syracuseStep 7476623 = 11214935) B11214935
theorem B3086063 : Blo 447780 3086063 := bstep (se 1 (by rfl) ⟨2314547, by rfl⟩ : syracuseStep 3086063 = 4629095) B4629095
theorem B18454601 : Blo 447780 18454601 := bstep (se 2 (by rfl) ⟨6920475, by rfl⟩ : syracuseStep 18454601 = 13840951) B13840951
theorem B2267351 : Blo 447780 2267351 := bstep (se 1 (by rfl) ⟨1700513, by rfl⟩ : syracuseStep 2267351 = 3401027) B3401027
theorem B2562617 : Blo 447780 2562617 := bstep (se 2 (by rfl) ⟨960981, by rfl⟩ : syracuseStep 2562617 = 1921963) B1921963
theorem B15538817 : Blo 447780 15538817 := bstep (se 2 (by rfl) ⟨5827056, by rfl⟩ : syracuseStep 15538817 = 11654113) B11654113
theorem B2431883 : Blo 447780 2431883 := bstep (se 1 (by rfl) ⟨1823912, by rfl⟩ : syracuseStep 2431883 = 3647825) B3647825
theorem B5479325 : Blo 447780 5479325 := bstep (se 3 (by rfl) ⟨1027373, by rfl⟩ : syracuseStep 5479325 = 2054747) B2054747
theorem B1514429 : Blo 447780 1514429 := bstep (se 3 (by rfl) ⟨283955, by rfl⟩ : syracuseStep 1514429 = 567911) B567911
theorem B2924153 : Blo 447780 2924153 := bstep (se 2 (by rfl) ⟨1096557, by rfl⟩ : syracuseStep 2924153 = 2193115) B2193115
theorem B1711799 : Blo 447780 1711799 := bstep (se 1 (by rfl) ⟨1283849, by rfl⟩ : syracuseStep 1711799 = 2567699) B2567699
theorem B8888345 : Blo 447780 8888345 := bstep (se 2 (by rfl) ⟨3333129, by rfl⟩ : syracuseStep 8888345 = 6666259) B6666259
theorem B3908287 : Blo 447780 3908287 := bstep (se 1 (by rfl) ⟨2931215, by rfl⟩ : syracuseStep 3908287 = 5862431) B5862431
theorem B1516265 : Blo 447780 1516265 := bstep (se 2 (by rfl) ⟨568599, by rfl⟩ : syracuseStep 1516265 = 1137199) B1137199
theorem B3646721 : Blo 447780 3646721 := bstep (se 2 (by rfl) ⟨1367520, by rfl⟩ : syracuseStep 3646721 = 2735041) B2735041
theorem B6169931 : Blo 447780 6169931 := bstep (se 1 (by rfl) ⟨4627448, by rfl⟩ : syracuseStep 6169931 = 9254897) B9254897
theorem B3843449 : Blo 447780 3843449 := bstep (se 2 (by rfl) ⟨1441293, by rfl⟩ : syracuseStep 3843449 = 2882587) B2882587
theorem B6497819 : Blo 447780 6497819 := bstep (se 1 (by rfl) ⟨4873364, by rfl⟩ : syracuseStep 6497819 = 9746729) B9746729
theorem B1714031 : Blo 447780 1714031 := bstep (se 1 (by rfl) ⟨1285523, by rfl⟩ : syracuseStep 1714031 = 2571047) B2571047
theorem B1518803 : Blo 447780 1518803 := bstep (se 1 (by rfl) ⟨1139102, by rfl⟩ : syracuseStep 1518803 = 2278205) B2278205
theorem B863723 : Blo 447780 863723 := bstep (se 1 (by rfl) ⟨647792, by rfl⟩ : syracuseStep 863723 = 1295585) B1295585
theorem B962759 : Blo 447780 962759 := bstep (se 1 (by rfl) ⟨722069, by rfl⟩ : syracuseStep 962759 = 1444139) B1444139
theorem B7287083 : Blo 447780 7287083 := bstep (se 1 (by rfl) ⟨5465312, by rfl⟩ : syracuseStep 7287083 = 10930625) B10930625
theorem B1913215 : Blo 447780 1913215 := bstep (se 1 (by rfl) ⟨1434911, by rfl⟩ : syracuseStep 1913215 = 2869823) B2869823
theorem B2077085 : Blo 447780 2077085 := bstep (se 3 (by rfl) ⟨389453, by rfl⟩ : syracuseStep 2077085 = 778907) B778907
theorem B504319 : Blo 447780 504319 := bstep (se 1 (by rfl) ⟨378239, by rfl⟩ : syracuseStep 504319 = 756479) B756479
theorem B570559 : Blo 447780 570559 := bstep (se 1 (by rfl) ⟨427919, by rfl⟩ : syracuseStep 570559 = 855839) B855839
theorem B2373167 : Blo 447780 2373167 := bstep (se 1 (by rfl) ⟨1779875, by rfl⟩ : syracuseStep 2373167 = 3559751) B3559751
theorem B2275451 : Blo 447780 2275451 := bstep (se 1 (by rfl) ⟨1706588, by rfl⟩ : syracuseStep 2275451 = 3413177) B3413177
theorem B1522151 : Blo 447780 1522151 := bstep (se 1 (by rfl) ⟨1141613, by rfl⟩ : syracuseStep 1522151 = 2283227) B2283227
theorem B506479 : Blo 447780 506479 := bstep (se 1 (by rfl) ⟨379859, by rfl⟩ : syracuseStep 506479 = 759719) B759719
theorem B4340411 : Blo 447780 4340411 := bstep (se 1 (by rfl) ⟨3255308, by rfl⟩ : syracuseStep 4340411 = 6510617) B6510617
theorem B1522529 : Blo 447780 1522529 := bstep (se 2 (by rfl) ⟨570948, by rfl⟩ : syracuseStep 1522529 = 1141897) B1141897
theorem B506875 : Blo 447780 506875 := bstep (se 1 (by rfl) ⟨380156, by rfl⟩ : syracuseStep 506875 = 760313) B760313
theorem B507739 : Blo 447780 507739 := bstep (se 1 (by rfl) ⟨380804, by rfl⟩ : syracuseStep 507739 = 761609) B761609
theorem B1917179 : Blo 447780 1917179 := bstep (se 1 (by rfl) ⟨1437884, by rfl⟩ : syracuseStep 1917179 = 2875769) B2875769
theorem B6177059 : Blo 447780 6177059 := bstep (se 1 (by rfl) ⟨4632794, by rfl⟩ : syracuseStep 6177059 = 9265589) B9265589
theorem B1917931 : Blo 447780 1917931 := bstep (se 1 (by rfl) ⟨1438448, by rfl⟩ : syracuseStep 1917931 = 2876897) B2876897
theorem B7685117 : Blo 447780 7685117 := bstep (se 3 (by rfl) ⟨1440959, by rfl⟩ : syracuseStep 7685117 = 2881919) B2881919
theorem B672863 : Blo 447780 672863 := bstep (se 1 (by rfl) ⟨504647, by rfl⟩ : syracuseStep 672863 = 1009295) B1009295
theorem B673487 : Blo 447780 673487 := bstep (se 1 (by rfl) ⟨505115, by rfl⟩ : syracuseStep 673487 = 1010231) B1010231
theorem B673535 : Blo 447780 673535 := bstep (se 1 (by rfl) ⟨505151, by rfl⟩ : syracuseStep 673535 = 1010303) B1010303
theorem B9324571 : Blo 447780 9324571 := bstep (se 1 (by rfl) ⟨6993428, by rfl⟩ : syracuseStep 9324571 = 13986857) B13986857
theorem B674591 : Blo 447780 674591 := bstep (se 1 (by rfl) ⟨505943, by rfl⟩ : syracuseStep 674591 = 1011887) B1011887
theorem B674663 : Blo 447780 674663 := bstep (se 1 (by rfl) ⟨505997, by rfl⟩ : syracuseStep 674663 = 1011995) B1011995
theorem B2051027 : Blo 447780 2051027 := bstep (se 1 (by rfl) ⟨1538270, by rfl⟩ : syracuseStep 2051027 = 3076541) B3076541
theorem B675551 : Blo 447780 675551 := bstep (se 1 (by rfl) ⟨506663, by rfl⟩ : syracuseStep 675551 = 1013327) B1013327
theorem B3854587 : Blo 447780 3854587 := bstep (se 1 (by rfl) ⟨2890940, by rfl⟩ : syracuseStep 3854587 = 5781881) B5781881
theorem B4117229 : Blo 447780 4117229 := bstep (se 3 (by rfl) ⟨771980, by rfl⟩ : syracuseStep 4117229 = 1543961) B1543961
theorem B4608899 : Blo 447780 4608899 := bstep (se 1 (by rfl) ⟨3456674, by rfl⟩ : syracuseStep 4608899 = 6913349) B6913349
theorem B447815 : Blo 447780 447815 := bstep (se 1 (by rfl) ⟨335861, by rfl⟩ : syracuseStep 447815 = 671723) B671723
theorem B677375 : Blo 447780 677375 := bstep (se 1 (by rfl) ⟨508031, by rfl⟩ : syracuseStep 677375 = 1016063) B1016063
theorem B448047 : Blo 447780 448047 := bstep (se 1 (by rfl) ⟨336035, by rfl⟩ : syracuseStep 448047 = 672071) B672071
theorem B448103 : Blo 447780 448103 := bstep (se 1 (by rfl) ⟨336077, by rfl⟩ : syracuseStep 448103 = 672155) B672155
theorem B83187587 : Blo 447780 83187587 := bstep (se 1 (by rfl) ⟨62390690, by rfl⟩ : syracuseStep 83187587 = 124781381) B124781381
theorem B2283551 : Blo 447780 2283551 := bstep (se 1 (by rfl) ⟨1712663, by rfl⟩ : syracuseStep 2283551 = 3425327) B3425327
theorem B448559 : Blo 447780 448559 := bstep (se 1 (by rfl) ⟨336419, by rfl⟩ : syracuseStep 448559 = 672839) B672839
theorem B448615 : Blo 447780 448615 := bstep (se 1 (by rfl) ⟨336461, by rfl⟩ : syracuseStep 448615 = 672923) B672923
theorem B448679 : Blo 447780 448679 := bstep (se 1 (by rfl) ⟨336509, by rfl⟩ : syracuseStep 448679 = 673019) B673019
theorem B448871 : Blo 447780 448871 := bstep (se 1 (by rfl) ⟨336653, by rfl⟩ : syracuseStep 448871 = 673307) B673307
theorem B449127 : Blo 447780 449127 := bstep (se 1 (by rfl) ⟨336845, by rfl⟩ : syracuseStep 449127 = 673691) B673691
theorem B449307 : Blo 447780 449307 := bstep (se 1 (by rfl) ⟨336980, by rfl⟩ : syracuseStep 449307 = 673961) B673961
theorem B908129 : Blo 447780 908129 := bstep (se 2 (by rfl) ⟨340548, by rfl⟩ : syracuseStep 908129 = 681097) B681097
theorem B449567 : Blo 447780 449567 := bstep (se 1 (by rfl) ⟨337175, by rfl⟩ : syracuseStep 449567 = 674351) B674351
theorem B450075 : Blo 447780 450075 := bstep (se 1 (by rfl) ⟨337556, by rfl⟩ : syracuseStep 450075 = 675113) B675113
theorem B450299 : Blo 447780 450299 := bstep (se 1 (by rfl) ⟨337724, by rfl⟩ : syracuseStep 450299 = 675449) B675449
theorem B1924955 : Blo 447780 1924955 := bstep (se 1 (by rfl) ⟨1443716, by rfl⟩ : syracuseStep 1924955 = 2887433) B2887433
theorem B450495 : Blo 447780 450495 := bstep (se 1 (by rfl) ⟨337871, by rfl⟩ : syracuseStep 450495 = 675743) B675743
theorem B450671 : Blo 447780 450671 := bstep (se 1 (by rfl) ⟨338003, by rfl⟩ : syracuseStep 450671 = 676007) B676007
theorem B1138931 : Blo 447780 1138931 := bstep (se 1 (by rfl) ⟨854198, by rfl⟩ : syracuseStep 1138931 = 1708397) B1708397
theorem B8610083 : Blo 447780 8610083 := bstep (se 1 (by rfl) ⟨6457562, by rfl⟩ : syracuseStep 8610083 = 12915125) B12915125
theorem B1007999 : Blo 447780 1007999 := bstep (se 1 (by rfl) ⟨755999, by rfl⟩ : syracuseStep 1007999 = 1511999) B1511999
theorem B30466459 : Blo 447780 30466459 := bstep (se 1 (by rfl) ⟨22849844, by rfl⟩ : syracuseStep 30466459 = 45699689) B45699689
theorem B451227 : Blo 447780 451227 := bstep (se 1 (by rfl) ⟨338420, by rfl⟩ : syracuseStep 451227 = 676841) B676841
theorem B451263 : Blo 447780 451263 := bstep (se 1 (by rfl) ⟨338447, by rfl⟩ : syracuseStep 451263 = 676895) B676895
theorem B451551 : Blo 447780 451551 := bstep (se 1 (by rfl) ⟨338663, by rfl⟩ : syracuseStep 451551 = 677327) B677327
theorem B1139903 : Blo 447780 1139903 := bstep (se 1 (by rfl) ⟨854927, by rfl⟩ : syracuseStep 1139903 = 1709855) B1709855
theorem B2156519 : Blo 447780 2156519 := bstep (se 1 (by rfl) ⟨1617389, by rfl⟩ : syracuseStep 2156519 = 3234779) B3234779
theorem B1140875 : Blo 447780 1140875 := bstep (se 1 (by rfl) ⟨855656, by rfl⟩ : syracuseStep 1140875 = 1711313) B1711313
theorem B911657 : Blo 447780 911657 := bstep (se 2 (by rfl) ⟨341871, by rfl⟩ : syracuseStep 911657 = 683743) B683743
theorem B12315331 : Blo 447780 12315331 := bstep (se 1 (by rfl) ⟨9236498, by rfl⟩ : syracuseStep 12315331 = 18472997) B18472997
theorem B1010555 : Blo 447780 1010555 := bstep (se 1 (by rfl) ⟨757916, by rfl⟩ : syracuseStep 1010555 = 1515833) B1515833
theorem B9039113 : Blo 447780 9039113 := bstep (se 2 (by rfl) ⟨3389667, by rfl⟩ : syracuseStep 9039113 = 6779335) B6779335
theorem B1142495 : Blo 447780 1142495 := bstep (se 1 (by rfl) ⟨856871, by rfl⟩ : syracuseStep 1142495 = 1713743) B1713743
theorem B1077491 : Blo 447780 1077491 := bstep (se 1 (by rfl) ⟨808118, by rfl⟩ : syracuseStep 1077491 = 1616237) B1616237
theorem B5108831 : Blo 447780 5108831 := bstep (se 1 (by rfl) ⟨3831623, by rfl⟩ : syracuseStep 5108831 = 7663247) B7663247
theorem B1013417 : Blo 447780 1013417 := bstep (se 2 (by rfl) ⟨380031, by rfl⟩ : syracuseStep 1013417 = 760063) B760063
theorem B7698239 : Blo 447780 7698239 := bstep (se 1 (by rfl) ⟨5773679, by rfl⟩ : syracuseStep 7698239 = 11547359) B11547359
theorem B1014047 : Blo 447780 1014047 := bstep (se 1 (by rfl) ⟨760535, by rfl⟩ : syracuseStep 1014047 = 1521071) B1521071
theorem B1014119 : Blo 447780 1014119 := bstep (se 1 (by rfl) ⟨760589, by rfl⟩ : syracuseStep 1014119 = 1521179) B1521179
theorem B1702367 : Blo 447780 1702367 := bstep (se 1 (by rfl) ⟨1276775, by rfl⟩ : syracuseStep 1702367 = 2553551) B2553551
theorem B1702397 : Blo 447780 1702397 := bstep (se 3 (by rfl) ⟨319199, by rfl⟩ : syracuseStep 1702397 = 638399) B638399
theorem B1014857 : Blo 447780 1014857 := bstep (se 2 (by rfl) ⟨380571, by rfl⟩ : syracuseStep 1014857 = 761143) B761143
theorem B1277927 : Blo 447780 1277927 := bstep (se 1 (by rfl) ⟨958445, by rfl⟩ : syracuseStep 1277927 = 1916891) B1916891
theorem B1278119 : Blo 447780 1278119 := bstep (se 1 (by rfl) ⟨958589, by rfl⟩ : syracuseStep 1278119 = 1917179) B1917179
theorem B12321467 : Blo 447780 12321467 := bstep (se 1 (by rfl) ⟨9241100, by rfl⟩ : syracuseStep 12321467 = 18482201) B18482201
theorem B5211049 : Blo 447780 5211049 := bstep (se 2 (by rfl) ⟨1954143, by rfl⟩ : syracuseStep 5211049 = 3908287) B3908287
theorem B5538893 : Blo 447780 5538893 := bstep (se 3 (by rfl) ⟨1038542, by rfl⟩ : syracuseStep 5538893 = 2077085) B2077085
theorem B2557241 : Blo 447780 2557241 := bstep (se 2 (by rfl) ⟨958965, by rfl⟩ : syracuseStep 2557241 = 1917931) B1917931
theorem B2623103 : Blo 447780 2623103 := bstep (se 1 (by rfl) ⟨1967327, by rfl⟩ : syracuseStep 2623103 = 3934655) B3934655
theorem B6491015 : Blo 447780 6491015 := bstep (se 1 (by rfl) ⟨4868261, by rfl⟩ : syracuseStep 6491015 = 9736523) B9736523
theorem B1707439 : Blo 447780 1707439 := bstep (se 1 (by rfl) ⟨1280579, by rfl⟩ : syracuseStep 1707439 = 2561159) B2561159
theorem B16420441 : Blo 447780 16420441 := bstep (se 2 (by rfl) ⟨6157665, by rfl⟩ : syracuseStep 16420441 = 12315331) B12315331
theorem B4984415 : Blo 447780 4984415 := bstep (se 1 (by rfl) ⟨3738311, by rfl⟩ : syracuseStep 4984415 = 7476623) B7476623
theorem B1511567 : Blo 447780 1511567 := bstep (se 1 (by rfl) ⟨1133675, by rfl⟩ : syracuseStep 1511567 = 2267351) B2267351
theorem B1708411 : Blo 447780 1708411 := bstep (se 1 (by rfl) ⟨1281308, by rfl⟩ : syracuseStep 1708411 = 2562617) B2562617
theorem B10359211 : Blo 447780 10359211 := bstep (se 1 (by rfl) ⟨7769408, by rfl⟩ : syracuseStep 10359211 = 15538817) B15538817
theorem B1283303 : Blo 447780 1283303 := bstep (se 1 (by rfl) ⟨962477, by rfl⟩ : syracuseStep 1283303 = 1924955) B1924955
theorem B759287 : Blo 447780 759287 := bstep (se 1 (by rfl) ⟨569465, by rfl⟩ : syracuseStep 759287 = 1138931) B1138931
theorem B5740055 : Blo 447780 5740055 := bstep (se 1 (by rfl) ⟨4305041, by rfl⟩ : syracuseStep 5740055 = 8610083) B8610083
theorem B759935 : Blo 447780 759935 := bstep (se 1 (by rfl) ⟨569951, by rfl⟩ : syracuseStep 759935 = 1139903) B1139903
theorem B2431147 : Blo 447780 2431147 := bstep (se 1 (by rfl) ⟨1823360, by rfl⟩ : syracuseStep 2431147 = 3646721) B3646721
theorem B2562299 : Blo 447780 2562299 := bstep (se 1 (by rfl) ⟨1921724, by rfl⟩ : syracuseStep 2562299 = 3843449) B3843449
theorem B4331879 : Blo 447780 4331879 := bstep (se 1 (by rfl) ⟨3248909, by rfl⟩ : syracuseStep 4331879 = 6497819) B6497819
theorem B760583 : Blo 447780 760583 := bstep (se 1 (by rfl) ⟨570437, by rfl⟩ : syracuseStep 760583 = 1140875) B1140875
theorem B760745 : Blo 447780 760745 := bstep (se 2 (by rfl) ⟨285279, by rfl⟩ : syracuseStep 760745 = 570559) B570559
theorem B761663 : Blo 447780 761663 := bstep (se 1 (by rfl) ⟨571247, by rfl⟩ : syracuseStep 761663 = 1142495) B1142495
theorem B4858055 : Blo 447780 4858055 := bstep (se 1 (by rfl) ⟨3643541, by rfl⟩ : syracuseStep 4858055 = 7287083) B7287083
theorem B1582111 : Blo 447780 1582111 := bstep (se 1 (by rfl) ⟨1186583, by rfl⟩ : syracuseStep 1582111 = 2373167) B2373167
theorem B1516967 : Blo 447780 1516967 := bstep (se 1 (by rfl) ⟨1137725, by rfl⟩ : syracuseStep 1516967 = 2275451) B2275451
theorem B2893607 : Blo 447780 2893607 := bstep (se 1 (by rfl) ⟨2170205, by rfl⟩ : syracuseStep 2893607 = 4340411) B4340411
theorem B961255 : Blo 447780 961255 := bstep (se 1 (by rfl) ⟨720941, by rfl⟩ : syracuseStep 961255 = 1441883) B1441883
theorem B5123411 : Blo 447780 5123411 := bstep (se 1 (by rfl) ⟨3842558, by rfl⟩ : syracuseStep 5123411 = 7685117) B7685117
theorem B3845839 : Blo 447780 3845839 := bstep (se 1 (by rfl) ⟨2884379, by rfl⟩ : syracuseStep 3845839 = 5768759) B5768759
theorem B12432761 : Blo 447780 12432761 := bstep (se 2 (by rfl) ⟨4662285, by rfl⟩ : syracuseStep 12432761 = 9324571) B9324571
theorem B55458391 : Blo 447780 55458391 := bstep (se 1 (by rfl) ⟨41593793, by rfl⟩ : syracuseStep 55458391 = 83187587) B83187587
theorem B1522367 : Blo 447780 1522367 := bstep (se 1 (by rfl) ⟨1141775, by rfl⟩ : syracuseStep 1522367 = 2283551) B2283551
theorem B1621255 : Blo 447780 1621255 := bstep (se 1 (by rfl) ⟨1215941, by rfl⟩ : syracuseStep 1621255 = 2431883) B2431883
theorem B3652883 : Blo 447780 3652883 := bstep (se 1 (by rfl) ⟨2739662, by rfl⟩ : syracuseStep 3652883 = 5479325) B5479325
theorem B1949435 : Blo 447780 1949435 := bstep (se 1 (by rfl) ⟨1462076, by rfl⟩ : syracuseStep 1949435 = 2924153) B2924153
theorem B671999 : Blo 447780 671999 := bstep (se 1 (by rfl) ⟨503999, by rfl⟩ : syracuseStep 671999 = 1007999) B1007999
theorem B6472325 : Blo 447780 6472325 := bstep (se 4 (by rfl) ⟨606780, by rfl⟩ : syracuseStep 6472325 = 1213561) B1213561
theorem B672425 : Blo 447780 672425 := bstep (se 2 (by rfl) ⟨252159, by rfl⟩ : syracuseStep 672425 = 504319) B504319
theorem B4113287 : Blo 447780 4113287 := bstep (se 1 (by rfl) ⟨3084965, by rfl⟩ : syracuseStep 4113287 = 6169931) B6169931
theorem B607771 : Blo 447780 607771 := bstep (se 1 (by rfl) ⟨455828, by rfl⟩ : syracuseStep 607771 = 911657) B911657
theorem B673703 : Blo 447780 673703 := bstep (se 1 (by rfl) ⟨505277, by rfl⟩ : syracuseStep 673703 = 1010555) B1010555
theorem B575815 : Blo 447780 575815 := bstep (se 1 (by rfl) ⟨431861, by rfl⟩ : syracuseStep 575815 = 863723) B863723
theorem B641839 : Blo 447780 641839 := bstep (se 1 (by rfl) ⟨481379, by rfl⟩ : syracuseStep 641839 = 962759) B962759
theorem B675305 : Blo 447780 675305 := bstep (se 2 (by rfl) ⟨253239, by rfl⟩ : syracuseStep 675305 = 506479) B506479
theorem B675611 : Blo 447780 675611 := bstep (se 1 (by rfl) ⟨506708, by rfl⟩ : syracuseStep 675611 = 1013417) B1013417
theorem B5132159 : Blo 447780 5132159 := bstep (se 1 (by rfl) ⟨3849119, by rfl⟩ : syracuseStep 5132159 = 7698239) B7698239
theorem B675833 : Blo 447780 675833 := bstep (se 2 (by rfl) ⟨253437, by rfl⟩ : syracuseStep 675833 = 506875) B506875
theorem B676031 : Blo 447780 676031 := bstep (se 1 (by rfl) ⟨507023, by rfl⟩ : syracuseStep 676031 = 1014047) B1014047
theorem B676079 : Blo 447780 676079 := bstep (se 1 (by rfl) ⟨507059, by rfl⟩ : syracuseStep 676079 = 1014119) B1014119
theorem B1134911 : Blo 447780 1134911 := bstep (se 1 (by rfl) ⟨851183, by rfl⟩ : syracuseStep 1134911 = 1702367) B1702367
theorem B1134931 : Blo 447780 1134931 := bstep (se 1 (by rfl) ⟨851198, by rfl⟩ : syracuseStep 1134931 = 1702397) B1702397
theorem B676571 : Blo 447780 676571 := bstep (se 1 (by rfl) ⟨507428, by rfl⟩ : syracuseStep 676571 = 1014857) B1014857
theorem B676985 : Blo 447780 676985 := bstep (se 2 (by rfl) ⟨253869, by rfl⟩ : syracuseStep 676985 = 507739) B507739
theorem B4118039 : Blo 447780 4118039 := bstep (se 1 (by rfl) ⟨3088529, by rfl⟩ : syracuseStep 4118039 = 6177059) B6177059
theorem B448575 : Blo 447780 448575 := bstep (se 1 (by rfl) ⟨336431, by rfl⟩ : syracuseStep 448575 = 672863) B672863
theorem B809387 : Blo 447780 809387 := bstep (se 1 (by rfl) ⟨607040, by rfl⟩ : syracuseStep 809387 = 1214081) B1214081
theorem B448991 : Blo 447780 448991 := bstep (se 1 (by rfl) ⟨336743, by rfl⟩ : syracuseStep 448991 = 673487) B673487
theorem B449023 : Blo 447780 449023 := bstep (se 1 (by rfl) ⟨336767, by rfl⟩ : syracuseStep 449023 = 673535) B673535
theorem B449727 : Blo 447780 449727 := bstep (se 1 (by rfl) ⟨337295, by rfl⟩ : syracuseStep 449727 = 674591) B674591
theorem B449775 : Blo 447780 449775 := bstep (se 1 (by rfl) ⟨337331, by rfl⟩ : syracuseStep 449775 = 674663) B674663
theorem B1367351 : Blo 447780 1367351 := bstep (se 1 (by rfl) ⟨1025513, by rfl⟩ : syracuseStep 1367351 = 2051027) B2051027
theorem B162487781 : Blo 447780 162487781 := bstep (se 4 (by rfl) ⟨15233229, by rfl⟩ : syracuseStep 162487781 = 30466459) B30466459
theorem B1924681 : Blo 447780 1924681 := bstep (se 2 (by rfl) ⟨721755, by rfl⟩ : syracuseStep 1924681 = 1443511) B1443511
theorem B450367 : Blo 447780 450367 := bstep (se 1 (by rfl) ⟨337775, by rfl⟩ : syracuseStep 450367 = 675551) B675551
theorem B2744819 : Blo 447780 2744819 := bstep (se 1 (by rfl) ⟨2058614, by rfl⟩ : syracuseStep 2744819 = 4117229) B4117229
theorem B3072599 : Blo 447780 3072599 := bstep (se 1 (by rfl) ⟨2304449, by rfl⟩ : syracuseStep 3072599 = 4608899) B4608899
theorem B451583 : Blo 447780 451583 := bstep (se 1 (by rfl) ⟨338687, by rfl⟩ : syracuseStep 451583 = 677375) B677375
theorem B2057375 : Blo 447780 2057375 := bstep (se 1 (by rfl) ⟨1543031, by rfl⟩ : syracuseStep 2057375 = 3086063) B3086063
theorem B1140601 : Blo 447780 1140601 := bstep (se 2 (by rfl) ⟨427725, by rfl⟩ : syracuseStep 1140601 = 855451) B855451
theorem B1009619 : Blo 447780 1009619 := bstep (se 1 (by rfl) ⟨757214, by rfl⟩ : syracuseStep 1009619 = 1514429) B1514429
theorem B1141199 : Blo 447780 1141199 := bstep (se 1 (by rfl) ⟨855899, by rfl⟩ : syracuseStep 1141199 = 1711799) B1711799
theorem B5925563 : Blo 447780 5925563 := bstep (se 1 (by rfl) ⟨4444172, by rfl⟩ : syracuseStep 5925563 = 8888345) B8888345
theorem B49212269 : Blo 447780 49212269 := bstep (se 3 (by rfl) ⟨9227300, by rfl⟩ : syracuseStep 49212269 = 18454601) B18454601
theorem B1010681 : Blo 447780 1010681 := bstep (se 2 (by rfl) ⟨379005, by rfl⟩ : syracuseStep 1010681 = 758011) B758011
theorem B5139449 : Blo 447780 5139449 := bstep (se 2 (by rfl) ⟨1927293, by rfl⟩ : syracuseStep 5139449 = 3854587) B3854587
theorem B1010843 : Blo 447780 1010843 := bstep (se 1 (by rfl) ⟨758132, by rfl⟩ : syracuseStep 1010843 = 1516265) B1516265
theorem B2550953 : Blo 447780 2550953 := bstep (se 2 (by rfl) ⟨956607, by rfl⟩ : syracuseStep 2550953 = 1913215) B1913215
theorem B1142687 : Blo 447780 1142687 := bstep (se 1 (by rfl) ⟨857015, by rfl⟩ : syracuseStep 1142687 = 1714031) B1714031
theorem B1437679 : Blo 447780 1437679 := bstep (se 1 (by rfl) ⟨1078259, by rfl⟩ : syracuseStep 1437679 = 2156519) B2156519
theorem B1012535 : Blo 447780 1012535 := bstep (se 1 (by rfl) ⟨759401, by rfl⟩ : syracuseStep 1012535 = 1518803) B1518803
theorem B6026075 : Blo 447780 6026075 := bstep (se 1 (by rfl) ⟨4519556, by rfl⟩ : syracuseStep 6026075 = 9039113) B9039113
theorem B2421677 : Blo 447780 2421677 := bstep (se 3 (by rfl) ⟨454064, by rfl⟩ : syracuseStep 2421677 = 908129) B908129
theorem B718327 : Blo 447780 718327 := bstep (se 1 (by rfl) ⟨538745, by rfl⟩ : syracuseStep 718327 = 1077491) B1077491
theorem B3405887 : Blo 447780 3405887 := bstep (se 1 (by rfl) ⟨2554415, by rfl⟩ : syracuseStep 3405887 = 5108831) B5108831
theorem B1014767 : Blo 447780 1014767 := bstep (se 1 (by rfl) ⟨761075, by rfl⟩ : syracuseStep 1014767 = 1522151) B1522151
theorem B1015019 : Blo 447780 1015019 := bstep (se 1 (by rfl) ⟨761264, by rfl⟩ : syracuseStep 1015019 = 1522529) B1522529
theorem B851951 : Blo 447780 851951 := bstep (se 1 (by rfl) ⟨638963, by rfl⟩ : syracuseStep 851951 = 1277927) B1277927
theorem B3408317 : Blo 447780 3408317 := bstep (se 3 (by rfl) ⟨639059, by rfl⟩ : syracuseStep 3408317 = 1278119) B1278119
theorem B59081525 : Blo 447780 59081525 := bstep (se 5 (by rfl) ⟨2769446, by rfl⟩ : syracuseStep 59081525 = 5538893) B5538893
theorem B1704827 : Blo 447780 1704827 := bstep (se 1 (by rfl) ⟨1278620, by rfl⟩ : syracuseStep 1704827 = 2557241) B2557241
theorem B6948065 : Blo 447780 6948065 := bstep (se 2 (by rfl) ⟨2605524, by rfl⟩ : syracuseStep 6948065 = 5211049) B5211049
theorem B4327343 : Blo 447780 4327343 := bstep (se 1 (by rfl) ⟨3245507, by rfl⟩ : syracuseStep 4327343 = 6491015) B6491015
theorem B756607 : Blo 447780 756607 := bstep (se 1 (by rfl) ⟨567455, by rfl⟩ : syracuseStep 756607 = 1134911) B1134911
theorem B855535 : Blo 447780 855535 := bstep (se 1 (by rfl) ⟨641651, by rfl⟩ : syracuseStep 855535 = 1283303) B1283303
theorem B1281673 : Blo 447780 1281673 := bstep (se 2 (by rfl) ⟨480627, by rfl⟩ : syracuseStep 1281673 = 961255) B961255
theorem B855785 : Blo 447780 855785 := bstep (se 2 (by rfl) ⟨320919, by rfl⟩ : syracuseStep 855785 = 641839) B641839
theorem B1708199 : Blo 447780 1708199 := bstep (se 1 (by rfl) ⟨1281149, by rfl⟩ : syracuseStep 1708199 = 2562299) B2562299
theorem B2887919 : Blo 447780 2887919 := bstep (se 1 (by rfl) ⟨2165939, by rfl⟩ : syracuseStep 2887919 = 4331879) B4331879
theorem B21893921 : Blo 447780 21893921 := bstep (se 2 (by rfl) ⟨8210220, by rfl⟩ : syracuseStep 21893921 = 16420441) B16420441
theorem B1513241 : Blo 447780 1513241 := bstep (se 2 (by rfl) ⟨567465, by rfl⟩ : syracuseStep 1513241 = 1134931) B1134931
theorem B760799 : Blo 447780 760799 := bstep (se 1 (by rfl) ⟨570599, by rfl⟩ : syracuseStep 760799 = 1141199) B1141199
theorem B32808179 : Blo 447780 32808179 := bstep (se 1 (by rfl) ⟨24606134, by rfl⟩ : syracuseStep 32808179 = 49212269) B49212269
theorem B3415607 : Blo 447780 3415607 := bstep (se 1 (by rfl) ⟨2561705, by rfl⟩ : syracuseStep 3415607 = 5123411) B5123411
theorem B761791 : Blo 447780 761791 := bstep (se 1 (by rfl) ⟨571343, by rfl⟩ : syracuseStep 761791 = 1142687) B1142687
theorem B1614451 : Blo 447780 1614451 := bstep (se 1 (by rfl) ⟨1210838, by rfl⟩ : syracuseStep 1614451 = 2421677) B2421677
theorem B2270591 : Blo 447780 2270591 := bstep (se 1 (by rfl) ⟨1702943, by rfl⟩ : syracuseStep 2270591 = 3405887) B3405887
theorem B2566241 : Blo 447780 2566241 := bstep (se 2 (by rfl) ⟨962340, by rfl⟩ : syracuseStep 2566241 = 1924681) B1924681
theorem B2435255 : Blo 447780 2435255 := bstep (se 1 (by rfl) ⟨1826441, by rfl⟩ : syracuseStep 2435255 = 3652883) B3652883
theorem B567967 : Blo 447780 567967 := bstep (se 1 (by rfl) ⟨425975, by rfl⟩ : syracuseStep 567967 = 851951) B851951
theorem B1748735 : Blo 447780 1748735 := bstep (se 1 (by rfl) ⟨1311551, by rfl⟩ : syracuseStep 1748735 = 2623103) B2623103
theorem B3322943 : Blo 447780 3322943 := bstep (se 1 (by rfl) ⟨2492207, by rfl⟩ : syracuseStep 3322943 = 4984415) B4984415
theorem B1520801 : Blo 447780 1520801 := bstep (se 2 (by rfl) ⟨570300, by rfl⟩ : syracuseStep 1520801 = 1140601) B1140601
theorem B3421439 : Blo 447780 3421439 := bstep (se 1 (by rfl) ⟨2566079, by rfl⟩ : syracuseStep 3421439 = 5132159) B5132159
theorem B767753 : Blo 447780 767753 := bstep (se 2 (by rfl) ⟨287907, by rfl⟩ : syracuseStep 767753 = 575815) B575815
theorem B506191 : Blo 447780 506191 := bstep (se 1 (by rfl) ⟨379643, by rfl⟩ : syracuseStep 506191 = 759287) B759287
theorem B506623 : Blo 447780 506623 := bstep (se 1 (by rfl) ⟨379967, by rfl⟩ : syracuseStep 506623 = 759935) B759935
theorem B539591 : Blo 447780 539591 := bstep (se 1 (by rfl) ⟨404693, by rfl⟩ : syracuseStep 539591 = 809387) B809387
theorem B507055 : Blo 447780 507055 := bstep (se 1 (by rfl) ⟨380291, by rfl⟩ : syracuseStep 507055 = 760583) B760583
theorem B2276585 : Blo 447780 2276585 := bstep (se 2 (by rfl) ⟨853719, by rfl⟩ : syracuseStep 2276585 = 1707439) B1707439
theorem B507163 : Blo 447780 507163 := bstep (se 1 (by rfl) ⟨380372, by rfl⟩ : syracuseStep 507163 = 760745) B760745
theorem B5127785 : Blo 447780 5127785 := bstep (se 2 (by rfl) ⟨1922919, by rfl⟩ : syracuseStep 5127785 = 3845839) B3845839
theorem B507775 : Blo 447780 507775 := bstep (se 1 (by rfl) ⟨380831, by rfl⟩ : syracuseStep 507775 = 761663) B761663
theorem B8437925 : Blo 447780 8437925 := bstep (se 4 (by rfl) ⟨791055, by rfl⟩ : syracuseStep 8437925 = 1582111) B1582111
theorem B2048399 : Blo 447780 2048399 := bstep (se 1 (by rfl) ⟨1536299, by rfl⟩ : syracuseStep 2048399 = 3072599) B3072599
theorem B2277881 : Blo 447780 2277881 := bstep (se 2 (by rfl) ⟨854205, by rfl⟩ : syracuseStep 2277881 = 1708411) B1708411
theorem B13812281 : Blo 447780 13812281 := bstep (se 2 (by rfl) ⟨5179605, by rfl⟩ : syracuseStep 13812281 = 10359211) B10359211
theorem B673079 : Blo 447780 673079 := bstep (se 1 (by rfl) ⟨504809, by rfl⟩ : syracuseStep 673079 = 1009619) B1009619
theorem B3950375 : Blo 447780 3950375 := bstep (se 1 (by rfl) ⟨2962781, by rfl⟩ : syracuseStep 3950375 = 5925563) B5925563
theorem B673787 : Blo 447780 673787 := bstep (se 1 (by rfl) ⟨505340, by rfl⟩ : syracuseStep 673787 = 1010681) B1010681
theorem B3426299 : Blo 447780 3426299 := bstep (se 1 (by rfl) ⟨2569724, by rfl⟩ : syracuseStep 3426299 = 5139449) B5139449
theorem B673895 : Blo 447780 673895 := bstep (se 1 (by rfl) ⟨505421, by rfl⟩ : syracuseStep 673895 = 1010843) B1010843
theorem B675023 : Blo 447780 675023 := bstep (se 1 (by rfl) ⟨506267, by rfl⟩ : syracuseStep 675023 = 1012535) B1012535
theorem B4017383 : Blo 447780 4017383 := bstep (se 1 (by rfl) ⟨3013037, by rfl⟩ : syracuseStep 4017383 = 6026075) B6026075
theorem B73944521 : Blo 447780 73944521 := bstep (se 2 (by rfl) ⟨27729195, by rfl⟩ : syracuseStep 73944521 = 55458391) B55458391
theorem B676511 : Blo 447780 676511 := bstep (se 1 (by rfl) ⟨507383, by rfl⟩ : syracuseStep 676511 = 1014767) B1014767
theorem B676679 : Blo 447780 676679 := bstep (se 1 (by rfl) ⟨507509, by rfl⟩ : syracuseStep 676679 = 1015019) B1015019
theorem B1299623 : Blo 447780 1299623 := bstep (se 1 (by rfl) ⟨974717, by rfl⟩ : syracuseStep 1299623 = 1949435) B1949435
theorem B447999 : Blo 447780 447999 := bstep (se 1 (by rfl) ⟨335999, by rfl⟩ : syracuseStep 447999 = 671999) B671999
theorem B4314883 : Blo 447780 4314883 := bstep (se 1 (by rfl) ⟨3236162, by rfl⟩ : syracuseStep 4314883 = 6472325) B6472325
theorem B448283 : Blo 447780 448283 := bstep (se 1 (by rfl) ⟨336212, by rfl⟩ : syracuseStep 448283 = 672425) B672425
theorem B8214311 : Blo 447780 8214311 := bstep (se 1 (by rfl) ⟨6160733, by rfl⟩ : syracuseStep 8214311 = 12321467) B12321467
theorem B2742191 : Blo 447780 2742191 := bstep (se 1 (by rfl) ⟨2056643, by rfl⟩ : syracuseStep 2742191 = 4113287) B4113287
theorem B449135 : Blo 447780 449135 := bstep (se 1 (by rfl) ⟨336851, by rfl⟩ : syracuseStep 449135 = 673703) B673703
theorem B810361 : Blo 447780 810361 := bstep (se 2 (by rfl) ⟨303885, by rfl⟩ : syracuseStep 810361 = 607771) B607771
theorem B450203 : Blo 447780 450203 := bstep (se 1 (by rfl) ⟨337652, by rfl⟩ : syracuseStep 450203 = 675305) B675305
theorem B450407 : Blo 447780 450407 := bstep (se 1 (by rfl) ⟨337805, by rfl⟩ : syracuseStep 450407 = 675611) B675611
theorem B450555 : Blo 447780 450555 := bstep (se 1 (by rfl) ⟨337916, by rfl⟩ : syracuseStep 450555 = 675833) B675833
theorem B1007711 : Blo 447780 1007711 := bstep (se 1 (by rfl) ⟨755783, by rfl⟩ : syracuseStep 1007711 = 1511567) B1511567
theorem B450687 : Blo 447780 450687 := bstep (se 1 (by rfl) ⟨338015, by rfl⟩ : syracuseStep 450687 = 676031) B676031
theorem B450719 : Blo 447780 450719 := bstep (se 1 (by rfl) ⟨338039, by rfl⟩ : syracuseStep 450719 = 676079) B676079
theorem B451047 : Blo 447780 451047 := bstep (se 1 (by rfl) ⟨338285, by rfl⟩ : syracuseStep 451047 = 676571) B676571
theorem B451323 : Blo 447780 451323 := bstep (se 1 (by rfl) ⟨338492, by rfl⟩ : syracuseStep 451323 = 676985) B676985
theorem B3826703 : Blo 447780 3826703 := bstep (se 1 (by rfl) ⟨2870027, by rfl⟩ : syracuseStep 3826703 = 5740055) B5740055
theorem B2745359 : Blo 447780 2745359 := bstep (se 1 (by rfl) ⟨2059019, by rfl⟩ : syracuseStep 2745359 = 4118039) B4118039
theorem B911567 : Blo 447780 911567 := bstep (se 1 (by rfl) ⟨683675, by rfl⟩ : syracuseStep 911567 = 1367351) B1367351
theorem B108325187 : Blo 447780 108325187 := bstep (se 1 (by rfl) ⟨81243890, by rfl⟩ : syracuseStep 108325187 = 162487781) B162487781
theorem B3238703 : Blo 447780 3238703 := bstep (se 1 (by rfl) ⟨2429027, by rfl⟩ : syracuseStep 3238703 = 4858055) B4858055
theorem B1829879 : Blo 447780 1829879 := bstep (se 1 (by rfl) ⟨1372409, by rfl⟩ : syracuseStep 1829879 = 2744819) B2744819
theorem B1371583 : Blo 447780 1371583 := bstep (se 1 (by rfl) ⟨1028687, by rfl⟩ : syracuseStep 1371583 = 2057375) B2057375
theorem B1011311 : Blo 447780 1011311 := bstep (se 1 (by rfl) ⟨758483, by rfl⟩ : syracuseStep 1011311 = 1516967) B1516967
theorem B1929071 : Blo 447780 1929071 := bstep (se 1 (by rfl) ⟨1446803, by rfl⟩ : syracuseStep 1929071 = 2893607) B2893607
theorem B1700635 : Blo 447780 1700635 := bstep (se 1 (by rfl) ⟨1275476, by rfl⟩ : syracuseStep 1700635 = 2550953) B2550953
theorem B3831077 : Blo 447780 3831077 := bstep (se 4 (by rfl) ⟨359163, by rfl⟩ : syracuseStep 3831077 = 718327) B718327
theorem B3241529 : Blo 447780 3241529 := bstep (se 2 (by rfl) ⟨1215573, by rfl⟩ : syracuseStep 3241529 = 2431147) B2431147
theorem B8288507 : Blo 447780 8288507 := bstep (se 1 (by rfl) ⟨6216380, by rfl⟩ : syracuseStep 8288507 = 12432761) B12432761
theorem B2161673 : Blo 447780 2161673 := bstep (se 2 (by rfl) ⟨810627, by rfl⟩ : syracuseStep 2161673 = 1621255) B1621255
theorem B1014911 : Blo 447780 1014911 := bstep (se 1 (by rfl) ⟨761183, by rfl⟩ : syracuseStep 1014911 = 1522367) B1522367
theorem B7667621 : Blo 447780 7667621 := bstep (se 4 (by rfl) ⟨718839, by rfl⟩ : syracuseStep 7667621 = 1437679) B1437679
theorem B9208187 : Blo 447780 9208187 := bstep (se 1 (by rfl) ⟨6906140, by rfl⟩ : syracuseStep 9208187 = 13812281) B13812281
theorem B39387683 : Blo 447780 39387683 := bstep (se 1 (by rfl) ⟨29540762, by rfl⟩ : syracuseStep 39387683 = 59081525) B59081525
theorem B2884895 : Blo 447780 2884895 := bstep (se 1 (by rfl) ⟨2163671, by rfl⟩ : syracuseStep 2884895 = 4327343) B4327343
theorem B757289 : Blo 447780 757289 := bstep (se 2 (by rfl) ⟨283983, by rfl⟩ : syracuseStep 757289 = 567967) B567967
theorem B5476207 : Blo 447780 5476207 := bstep (se 1 (by rfl) ⟨4107155, by rfl⟩ : syracuseStep 5476207 = 8214311) B8214311
theorem B1708897 : Blo 447780 1708897 := bstep (se 2 (by rfl) ⟨640836, by rfl⟩ : syracuseStep 1708897 = 1281673) B1281673
theorem B1513727 : Blo 447780 1513727 := bstep (se 1 (by rfl) ⟨1135295, by rfl⟩ : syracuseStep 1513727 = 2270591) B2270591
theorem B2267513 : Blo 447780 2267513 := bstep (se 2 (by rfl) ⟨850317, by rfl⟩ : syracuseStep 2267513 = 1700635) B1700635
theorem B1710827 : Blo 447780 1710827 := bstep (se 1 (by rfl) ⟨1283120, by rfl⟩ : syracuseStep 1710827 = 2566241) B2566241
theorem B1219919 : Blo 447780 1219919 := bstep (se 1 (by rfl) ⟨914939, by rfl⟩ : syracuseStep 1219919 = 1829879) B1829879
theorem B1286047 : Blo 447780 1286047 := bstep (se 1 (by rfl) ⟨964535, by rfl⟩ : syracuseStep 1286047 = 1929071) B1929071
theorem B1517723 : Blo 447780 1517723 := bstep (se 1 (by rfl) ⟨1138292, by rfl⟩ : syracuseStep 1517723 = 2276585) B2276585
theorem B3418523 : Blo 447780 3418523 := bstep (se 1 (by rfl) ⟨2563892, by rfl⟩ : syracuseStep 3418523 = 5127785) B5127785
theorem B2272211 : Blo 447780 2272211 := bstep (se 1 (by rfl) ⟨1704158, by rfl⟩ : syracuseStep 2272211 = 3408317) B3408317
theorem B1518587 : Blo 447780 1518587 := bstep (se 1 (by rfl) ⟨1138940, by rfl⟩ : syracuseStep 1518587 = 2277881) B2277881
theorem B49296347 : Blo 447780 49296347 := bstep (se 1 (by rfl) ⟨36972260, by rfl⟩ : syracuseStep 49296347 = 73944521) B73944521
theorem B14595947 : Blo 447780 14595947 := bstep (se 1 (by rfl) ⟨10946960, by rfl⟩ : syracuseStep 14595947 = 21893921) B21893921
theorem B18528173 : Blo 447780 18528173 := bstep (se 3 (by rfl) ⟨3474032, by rfl⟩ : syracuseStep 18528173 = 6948065) B6948065
theorem B507199 : Blo 447780 507199 := bstep (se 1 (by rfl) ⟨380399, by rfl⟩ : syracuseStep 507199 = 760799) B760799
theorem B21872119 : Blo 447780 21872119 := bstep (se 1 (by rfl) ⟨16404089, by rfl⟩ : syracuseStep 21872119 = 32808179) B32808179
theorem B2277071 : Blo 447780 2277071 := bstep (se 1 (by rfl) ⟨1707803, by rfl⟩ : syracuseStep 2277071 = 3415607) B3415607
theorem B671807 : Blo 447780 671807 := bstep (se 1 (by rfl) ⟨503855, by rfl⟩ : syracuseStep 671807 = 1007711) B1007711
theorem B1623503 : Blo 447780 1623503 := bstep (se 1 (by rfl) ⟨1217627, by rfl⟩ : syracuseStep 1623503 = 2435255) B2435255
theorem B607711 : Blo 447780 607711 := bstep (se 1 (by rfl) ⟨455783, by rfl⟩ : syracuseStep 607711 = 911567) B911567
theorem B5753177 : Blo 447780 5753177 := bstep (se 2 (by rfl) ⟨2157441, by rfl⟩ : syracuseStep 5753177 = 4314883) B4314883
theorem B674207 : Blo 447780 674207 := bstep (se 1 (by rfl) ⟨505655, by rfl⟩ : syracuseStep 674207 = 1011311) B1011311
theorem B1165823 : Blo 447780 1165823 := bstep (se 1 (by rfl) ⟨874367, by rfl⟩ : syracuseStep 1165823 = 1748735) B1748735
theorem B674921 : Blo 447780 674921 := bstep (se 2 (by rfl) ⟨253095, by rfl⟩ : syracuseStep 674921 = 506191) B506191
theorem B2215295 : Blo 447780 2215295 := bstep (se 1 (by rfl) ⟨1661471, by rfl⟩ : syracuseStep 2215295 = 3322943) B3322943
theorem B2280959 : Blo 447780 2280959 := bstep (se 1 (by rfl) ⟨1710719, by rfl⟩ : syracuseStep 2280959 = 3421439) B3421439
theorem B675497 : Blo 447780 675497 := bstep (se 2 (by rfl) ⟨253311, by rfl⟩ : syracuseStep 675497 = 506623) B506623
theorem B511835 : Blo 447780 511835 := bstep (se 1 (by rfl) ⟨383876, by rfl⟩ : syracuseStep 511835 = 767753) B767753
theorem B5525671 : Blo 447780 5525671 := bstep (se 1 (by rfl) ⟨4144253, by rfl⟩ : syracuseStep 5525671 = 8288507) B8288507
theorem B676073 : Blo 447780 676073 := bstep (se 2 (by rfl) ⟨253527, by rfl⟩ : syracuseStep 676073 = 507055) B507055
theorem B676217 : Blo 447780 676217 := bstep (se 2 (by rfl) ⟨253581, by rfl⟩ : syracuseStep 676217 = 507163) B507163
theorem B2282093 : Blo 447780 2282093 := bstep (se 3 (by rfl) ⟨427892, by rfl⟩ : syracuseStep 2282093 = 855785) B855785
theorem B5755637 : Blo 447780 5755637 := bstep (se 5 (by rfl) ⟨269795, by rfl⟩ : syracuseStep 5755637 = 539591) B539591
theorem B676607 : Blo 447780 676607 := bstep (se 1 (by rfl) ⟨507455, by rfl⟩ : syracuseStep 676607 = 1014911) B1014911
theorem B677033 : Blo 447780 677033 := bstep (se 2 (by rfl) ⟨253887, by rfl⟩ : syracuseStep 677033 = 507775) B507775
theorem B5625283 : Blo 447780 5625283 := bstep (se 1 (by rfl) ⟨4218962, by rfl⟩ : syracuseStep 5625283 = 8437925) B8437925
theorem B1365599 : Blo 447780 1365599 := bstep (se 1 (by rfl) ⟨1024199, by rfl⟩ : syracuseStep 1365599 = 2048399) B2048399
theorem B1136551 : Blo 447780 1136551 := bstep (se 1 (by rfl) ⟨852413, by rfl⟩ : syracuseStep 1136551 = 1704827) B1704827
theorem B2152601 : Blo 447780 2152601 := bstep (se 2 (by rfl) ⟨807225, by rfl⟩ : syracuseStep 2152601 = 1614451) B1614451
theorem B448719 : Blo 447780 448719 := bstep (se 1 (by rfl) ⟨336539, by rfl⟩ : syracuseStep 448719 = 673079) B673079
theorem B449191 : Blo 447780 449191 := bstep (se 1 (by rfl) ⟨336893, by rfl⟩ : syracuseStep 449191 = 673787) B673787
theorem B2284199 : Blo 447780 2284199 := bstep (se 1 (by rfl) ⟨1713149, by rfl⟩ : syracuseStep 2284199 = 3426299) B3426299
theorem B449263 : Blo 447780 449263 := bstep (se 1 (by rfl) ⟨336947, by rfl⟩ : syracuseStep 449263 = 673895) B673895
theorem B450015 : Blo 447780 450015 := bstep (se 1 (by rfl) ⟨337511, by rfl⟩ : syracuseStep 450015 = 675023) B675023
theorem B2678255 : Blo 447780 2678255 := bstep (se 1 (by rfl) ⟨2008691, by rfl⟩ : syracuseStep 2678255 = 4017383) B4017383
theorem B1138799 : Blo 447780 1138799 := bstep (se 1 (by rfl) ⟨854099, by rfl⟩ : syracuseStep 1138799 = 1708199) B1708199
theorem B1925279 : Blo 447780 1925279 := bstep (se 1 (by rfl) ⟨1443959, by rfl⟩ : syracuseStep 1925279 = 2887919) B2887919
theorem B3465661 : Blo 447780 3465661 := bstep (se 3 (by rfl) ⟨649811, by rfl⟩ : syracuseStep 3465661 = 1299623) B1299623
theorem B451007 : Blo 447780 451007 := bstep (se 1 (by rfl) ⟨338255, by rfl⟩ : syracuseStep 451007 = 676511) B676511
theorem B451119 : Blo 447780 451119 := bstep (se 1 (by rfl) ⟨338339, by rfl⟩ : syracuseStep 451119 = 676679) B676679
theorem B1008809 : Blo 447780 1008809 := bstep (se 2 (by rfl) ⟨378303, by rfl⟩ : syracuseStep 1008809 = 756607) B756607
theorem B1008827 : Blo 447780 1008827 := bstep (se 1 (by rfl) ⟨756620, by rfl⟩ : syracuseStep 1008827 = 1513241) B1513241
theorem B1828127 : Blo 447780 1828127 := bstep (se 1 (by rfl) ⟨1371095, by rfl⟩ : syracuseStep 1828127 = 2742191) B2742191
theorem B1828777 : Blo 447780 1828777 := bstep (se 2 (by rfl) ⟨685791, by rfl⟩ : syracuseStep 1828777 = 1371583) B1371583
theorem B1140713 : Blo 447780 1140713 := bstep (se 2 (by rfl) ⟨427767, by rfl⟩ : syracuseStep 1140713 = 855535) B855535
theorem B2551135 : Blo 447780 2551135 := bstep (se 1 (by rfl) ⟨1913351, by rfl⟩ : syracuseStep 2551135 = 3826703) B3826703
theorem B1830239 : Blo 447780 1830239 := bstep (se 1 (by rfl) ⟨1372679, by rfl⟩ : syracuseStep 1830239 = 2745359) B2745359
theorem B72216791 : Blo 447780 72216791 := bstep (se 1 (by rfl) ⟨54162593, by rfl⟩ : syracuseStep 72216791 = 108325187) B108325187
theorem B2159135 : Blo 447780 2159135 := bstep (se 1 (by rfl) ⟨1619351, by rfl⟩ : syracuseStep 2159135 = 3238703) B3238703
theorem B42137333 : Blo 447780 42137333 := bstep (se 5 (by rfl) ⟨1975187, by rfl⟩ : syracuseStep 42137333 = 3950375) B3950375
theorem B1013867 : Blo 447780 1013867 := bstep (se 1 (by rfl) ⟨760400, by rfl⟩ : syracuseStep 1013867 = 1520801) B1520801
theorem B2554051 : Blo 447780 2554051 := bstep (se 1 (by rfl) ⟨1915538, by rfl⟩ : syracuseStep 2554051 = 3831077) B3831077
theorem B2161019 : Blo 447780 2161019 := bstep (se 1 (by rfl) ⟨1620764, by rfl⟩ : syracuseStep 2161019 = 3241529) B3241529
theorem B1080481 : Blo 447780 1080481 := bstep (se 2 (by rfl) ⟨405180, by rfl⟩ : syracuseStep 1080481 = 810361) B810361
theorem B1441115 : Blo 447780 1441115 := bstep (se 1 (by rfl) ⟨1080836, by rfl⟩ : syracuseStep 1441115 = 2161673) B2161673
theorem B1015721 : Blo 447780 1015721 := bstep (se 2 (by rfl) ⟨380895, by rfl⟩ : syracuseStep 1015721 = 761791) B761791
theorem B5111747 : Blo 447780 5111747 := bstep (se 1 (by rfl) ⟨3833810, by rfl⟩ : syracuseStep 5111747 = 7667621) B7667621
theorem B4620881 : Blo 447780 4620881 := bstep (se 2 (by rfl) ⟨1732830, by rfl⟩ : syracuseStep 4620881 = 3465661) B3465661
theorem B1082335 : Blo 447780 1082335 := bstep (se 1 (by rfl) ⟨811751, by rfl⟩ : syracuseStep 1082335 = 1623503) B1623503
theorem B3835451 : Blo 447780 3835451 := bstep (se 1 (by rfl) ⟨2876588, by rfl⟩ : syracuseStep 3835451 = 5753177) B5753177
theorem B1476863 : Blo 447780 1476863 := bstep (se 1 (by rfl) ⟨1107647, by rfl⟩ : syracuseStep 1476863 = 2215295) B2215295
theorem B3837091 : Blo 447780 3837091 := bstep (se 1 (by rfl) ⟨2877818, by rfl⟩ : syracuseStep 3837091 = 5755637) B5755637
theorem B1511675 : Blo 447780 1511675 := bstep (se 1 (by rfl) ⟨1133756, by rfl⟩ : syracuseStep 1511675 = 2267513) B2267513
theorem B3641597 : Blo 447780 3641597 := bstep (se 3 (by rfl) ⟨682799, by rfl⟩ : syracuseStep 3641597 = 1365599) B1365599
theorem B759199 : Blo 447780 759199 := bstep (se 1 (by rfl) ⟨569399, by rfl⟩ : syracuseStep 759199 = 1138799) B1138799
theorem B1283519 : Blo 447780 1283519 := bstep (se 1 (by rfl) ⟨962639, by rfl⟩ : syracuseStep 1283519 = 1925279) B1925279
theorem B760475 : Blo 447780 760475 := bstep (se 1 (by rfl) ⟨570356, by rfl⟩ : syracuseStep 760475 = 1140713) B1140713
theorem B1514807 : Blo 447780 1514807 := bstep (se 1 (by rfl) ⟨1136105, by rfl⟩ : syracuseStep 1514807 = 2272211) B2272211
theorem B1220159 : Blo 447780 1220159 := bstep (se 1 (by rfl) ⟨915119, by rfl⟩ : syracuseStep 1220159 = 1830239) B1830239
theorem B1515401 : Blo 447780 1515401 := bstep (se 2 (by rfl) ⟨568275, by rfl⟩ : syracuseStep 1515401 = 1136551) B1136551
theorem B48144527 : Blo 447780 48144527 := bstep (se 1 (by rfl) ⟨36108395, by rfl⟩ : syracuseStep 48144527 = 72216791) B72216791
theorem B3253117 : Blo 447780 3253117 := bstep (se 3 (by rfl) ⟨609959, by rfl⟩ : syracuseStep 3253117 = 1219919) B1219919
theorem B28091555 : Blo 447780 28091555 := bstep (se 1 (by rfl) ⟨21068666, by rfl⟩ : syracuseStep 28091555 = 42137333) B42137333
theorem B960743 : Blo 447780 960743 := bstep (se 1 (by rfl) ⟨720557, by rfl⟩ : syracuseStep 960743 = 1441115) B1441115
theorem B1518047 : Blo 447780 1518047 := bstep (se 1 (by rfl) ⟨1138535, by rfl⟩ : syracuseStep 1518047 = 2277071) B2277071
theorem B1714729 : Blo 447780 1714729 := bstep (se 2 (by rfl) ⟨643023, by rfl⟩ : syracuseStep 1714729 = 1286047) B1286047
theorem B6138791 : Blo 447780 6138791 := bstep (se 1 (by rfl) ⟨4604093, by rfl⟩ : syracuseStep 6138791 = 9208187) B9208187
theorem B26258455 : Blo 447780 26258455 := bstep (se 1 (by rfl) ⟨19693841, by rfl⟩ : syracuseStep 26258455 = 39387683) B39387683
theorem B1520639 : Blo 447780 1520639 := bstep (se 1 (by rfl) ⟨1140479, by rfl⟩ : syracuseStep 1520639 = 2280959) B2280959
theorem B504859 : Blo 447780 504859 := bstep (se 1 (by rfl) ⟨378644, by rfl⟩ : syracuseStep 504859 = 757289) B757289
theorem B2438369 : Blo 447780 2438369 := bstep (se 2 (by rfl) ⟨914388, by rfl⟩ : syracuseStep 2438369 = 1828777) B1828777
theorem B1521395 : Blo 447780 1521395 := bstep (se 1 (by rfl) ⟨1141046, by rfl⟩ : syracuseStep 1521395 = 2282093) B2282093
theorem B1522799 : Blo 447780 1522799 := bstep (se 1 (by rfl) ⟨1142099, by rfl⟩ : syracuseStep 1522799 = 2284199) B2284199
theorem B1785503 : Blo 447780 1785503 := bstep (se 1 (by rfl) ⟨1339127, by rfl⟩ : syracuseStep 1785503 = 2678255) B2678255
theorem B672539 : Blo 447780 672539 := bstep (se 1 (by rfl) ⟨504404, by rfl⟩ : syracuseStep 672539 = 1008809) B1008809
theorem B672551 : Blo 447780 672551 := bstep (se 1 (by rfl) ⟨504413, by rfl⟩ : syracuseStep 672551 = 1008827) B1008827
theorem B2278529 : Blo 447780 2278529 := bstep (se 2 (by rfl) ⟨854448, by rfl⟩ : syracuseStep 2278529 = 1708897) B1708897
theorem B2279015 : Blo 447780 2279015 := bstep (se 1 (by rfl) ⟨1709261, by rfl⟩ : syracuseStep 2279015 = 3418523) B3418523
theorem B675911 : Blo 447780 675911 := bstep (se 1 (by rfl) ⟨506933, by rfl⟩ : syracuseStep 675911 = 1013867) B1013867
theorem B676265 : Blo 447780 676265 := bstep (se 2 (by rfl) ⟨253599, by rfl⟩ : syracuseStep 676265 = 507199) B507199
theorem B1364893 : Blo 447780 1364893 := bstep (se 3 (by rfl) ⟨255917, by rfl⟩ : syracuseStep 1364893 = 511835) B511835
theorem B677147 : Blo 447780 677147 := bstep (se 1 (by rfl) ⟨507860, by rfl⟩ : syracuseStep 677147 = 1015721) B1015721
theorem B447871 : Blo 447780 447871 := bstep (se 1 (by rfl) ⟨335903, by rfl⟩ : syracuseStep 447871 = 671807) B671807
theorem B1923263 : Blo 447780 1923263 := bstep (se 1 (by rfl) ⟨1442447, by rfl⟩ : syracuseStep 1923263 = 2884895) B2884895
theorem B449471 : Blo 447780 449471 := bstep (se 1 (by rfl) ⟨337103, by rfl⟩ : syracuseStep 449471 = 674207) B674207
theorem B777215 : Blo 447780 777215 := bstep (se 1 (by rfl) ⟨582911, by rfl⟩ : syracuseStep 777215 = 1165823) B1165823
theorem B810281 : Blo 447780 810281 := bstep (se 2 (by rfl) ⟨303855, by rfl⟩ : syracuseStep 810281 = 607711) B607711
theorem B449947 : Blo 447780 449947 := bstep (se 1 (by rfl) ⟨337460, by rfl⟩ : syracuseStep 449947 = 674921) B674921
theorem B450331 : Blo 447780 450331 := bstep (se 1 (by rfl) ⟨337748, by rfl⟩ : syracuseStep 450331 = 675497) B675497
theorem B450715 : Blo 447780 450715 := bstep (se 1 (by rfl) ⟨338036, by rfl⟩ : syracuseStep 450715 = 676073) B676073
theorem B450811 : Blo 447780 450811 := bstep (se 1 (by rfl) ⟨338108, by rfl⟩ : syracuseStep 450811 = 676217) B676217
theorem B451071 : Blo 447780 451071 := bstep (se 1 (by rfl) ⟨338303, by rfl⟩ : syracuseStep 451071 = 676607) B676607
theorem B4875005 : Blo 447780 4875005 := bstep (se 3 (by rfl) ⟨914063, by rfl⟩ : syracuseStep 4875005 = 1828127) B1828127
theorem B451355 : Blo 447780 451355 := bstep (se 1 (by rfl) ⟨338516, by rfl⟩ : syracuseStep 451355 = 677033) B677033
theorem B1435067 : Blo 447780 1435067 := bstep (se 1 (by rfl) ⟨1076300, by rfl⟩ : syracuseStep 1435067 = 2152601) B2152601
theorem B1009151 : Blo 447780 1009151 := bstep (se 1 (by rfl) ⟨756863, by rfl⟩ : syracuseStep 1009151 = 1513727) B1513727
theorem B3401513 : Blo 447780 3401513 := bstep (se 2 (by rfl) ⟨1275567, by rfl⟩ : syracuseStep 3401513 = 2551135) B2551135
theorem B1140551 : Blo 447780 1140551 := bstep (se 1 (by rfl) ⟨855413, by rfl⟩ : syracuseStep 1140551 = 1710827) B1710827
theorem B7301609 : Blo 447780 7301609 := bstep (se 2 (by rfl) ⟨2738103, by rfl⟩ : syracuseStep 7301609 = 5476207) B5476207
theorem B7367561 : Blo 447780 7367561 := bstep (se 2 (by rfl) ⟨2762835, by rfl⟩ : syracuseStep 7367561 = 5525671) B5525671
theorem B1011815 : Blo 447780 1011815 := bstep (se 1 (by rfl) ⟨758861, by rfl⟩ : syracuseStep 1011815 = 1517723) B1517723
theorem B7500377 : Blo 447780 7500377 := bstep (se 2 (by rfl) ⟨2812641, by rfl⟩ : syracuseStep 7500377 = 5625283) B5625283
theorem B1012391 : Blo 447780 1012391 := bstep (se 1 (by rfl) ⟨759293, by rfl⟩ : syracuseStep 1012391 = 1518587) B1518587
theorem B3405401 : Blo 447780 3405401 := bstep (se 2 (by rfl) ⟨1277025, by rfl⟩ : syracuseStep 3405401 = 2554051) B2554051
theorem B1439423 : Blo 447780 1439423 := bstep (se 1 (by rfl) ⟨1079567, by rfl⟩ : syracuseStep 1439423 = 2159135) B2159135
theorem B32864231 : Blo 447780 32864231 := bstep (se 1 (by rfl) ⟨24648173, by rfl⟩ : syracuseStep 32864231 = 49296347) B49296347
theorem B9730631 : Blo 447780 9730631 := bstep (se 1 (by rfl) ⟨7297973, by rfl⟩ : syracuseStep 9730631 = 14595947) B14595947
theorem B12352115 : Blo 447780 12352115 := bstep (se 1 (by rfl) ⟨9264086, by rfl⟩ : syracuseStep 12352115 = 18528173) B18528173
theorem B1440641 : Blo 447780 1440641 := bstep (se 2 (by rfl) ⟨540240, by rfl⟩ : syracuseStep 1440641 = 1080481) B1080481
theorem B1440679 : Blo 447780 1440679 := bstep (se 1 (by rfl) ⟨1080509, by rfl⟩ : syracuseStep 1440679 = 2161019) B2161019
theorem B29162825 : Blo 447780 29162825 := bstep (se 2 (by rfl) ⟨10936059, by rfl⟩ : syracuseStep 29162825 = 21872119) B21872119
theorem B3407831 : Blo 447780 3407831 := bstep (se 1 (by rfl) ⟨2555873, by rfl⟩ : syracuseStep 3407831 = 5111747) B5111747
theorem B3080587 : Blo 447780 3080587 := bstep (se 1 (by rfl) ⟨2310440, by rfl⟩ : syracuseStep 3080587 = 4620881) B4620881
theorem B2556967 : Blo 447780 2556967 := bstep (se 1 (by rfl) ⟨1917725, by rfl⟩ : syracuseStep 2556967 = 3835451) B3835451
theorem B1443113 : Blo 447780 1443113 := bstep (se 2 (by rfl) ⟨541167, by rfl⟩ : syracuseStep 1443113 = 1082335) B1082335
theorem B984575 : Blo 447780 984575 := bstep (se 1 (by rfl) ⟨738431, by rfl⟩ : syracuseStep 984575 = 1476863) B1476863
theorem B2427731 : Blo 447780 2427731 := bstep (se 1 (by rfl) ⟨1820798, by rfl⟩ : syracuseStep 2427731 = 3641597) B3641597
theorem B855679 : Blo 447780 855679 := bstep (se 1 (by rfl) ⟨641759, by rfl⟩ : syracuseStep 855679 = 1283519) B1283519
theorem B1282175 : Blo 447780 1282175 := bstep (se 1 (by rfl) ⟨961631, by rfl⟩ : syracuseStep 1282175 = 1923263) B1923263
theorem B5116121 : Blo 447780 5116121 := bstep (se 2 (by rfl) ⟨1918545, by rfl⟩ : syracuseStep 5116121 = 3837091) B3837091
theorem B7279429 : Blo 447780 7279429 := bstep (se 4 (by rfl) ⟨682446, by rfl⟩ : syracuseStep 7279429 = 1364893) B1364893
theorem B3250003 : Blo 447780 3250003 := bstep (se 1 (by rfl) ⟨2437502, by rfl⟩ : syracuseStep 3250003 = 4875005) B4875005
theorem B956711 : Blo 447780 956711 := bstep (se 1 (by rfl) ⟨717533, by rfl⟩ : syracuseStep 956711 = 1435067) B1435067
theorem B2267675 : Blo 447780 2267675 := bstep (se 1 (by rfl) ⟨1700756, by rfl⟩ : syracuseStep 2267675 = 3401513) B3401513
theorem B760367 : Blo 447780 760367 := bstep (se 1 (by rfl) ⟨570275, by rfl⟩ : syracuseStep 760367 = 1140551) B1140551
theorem B2072573 : Blo 447780 2072573 := bstep (se 3 (by rfl) ⟨388607, by rfl⟩ : syracuseStep 2072573 = 777215) B777215
theorem B2270267 : Blo 447780 2270267 := bstep (se 1 (by rfl) ⟨1702700, by rfl⟩ : syracuseStep 2270267 = 3405401) B3405401
theorem B959615 : Blo 447780 959615 := bstep (se 1 (by rfl) ⟨719711, by rfl⟩ : syracuseStep 959615 = 1439423) B1439423
theorem B8234743 : Blo 447780 8234743 := bstep (se 1 (by rfl) ⟨6176057, by rfl⟩ : syracuseStep 8234743 = 12352115) B12352115
theorem B4761341 : Blo 447780 4761341 := bstep (se 3 (by rfl) ⟨892751, by rfl⟩ : syracuseStep 4761341 = 1785503) B1785503
theorem B960427 : Blo 447780 960427 := bstep (se 1 (by rfl) ⟨720320, by rfl⟩ : syracuseStep 960427 = 1440641) B1440641
theorem B19441883 : Blo 447780 19441883 := bstep (se 1 (by rfl) ⟨14581412, by rfl⟩ : syracuseStep 19441883 = 29162825) B29162825
theorem B2271887 : Blo 447780 2271887 := bstep (se 1 (by rfl) ⟨1703915, by rfl⟩ : syracuseStep 2271887 = 3407831) B3407831
theorem B1519019 : Blo 447780 1519019 := bstep (se 1 (by rfl) ⟨1139264, by rfl⟩ : syracuseStep 1519019 = 2278529) B2278529
theorem B1519343 : Blo 447780 1519343 := bstep (se 1 (by rfl) ⟨1139507, by rfl⟩ : syracuseStep 1519343 = 2279015) B2279015
theorem B4337489 : Blo 447780 4337489 := bstep (se 2 (by rfl) ⟨1626558, by rfl⟩ : syracuseStep 4337489 = 3253117) B3253117
theorem B20001005 : Blo 447780 20001005 := bstep (se 3 (by rfl) ⟨3750188, by rfl⟩ : syracuseStep 20001005 = 7500377) B7500377
theorem B35011273 : Blo 447780 35011273 := bstep (se 2 (by rfl) ⟨13129227, by rfl⟩ : syracuseStep 35011273 = 26258455) B26258455
theorem B506983 : Blo 447780 506983 := bstep (se 1 (by rfl) ⟨380237, by rfl⟩ : syracuseStep 506983 = 760475) B760475
theorem B32096351 : Blo 447780 32096351 := bstep (se 1 (by rfl) ⟨24072263, by rfl⟩ : syracuseStep 32096351 = 48144527) B48144527
theorem B18727703 : Blo 447780 18727703 := bstep (se 1 (by rfl) ⟨14045777, by rfl⟩ : syracuseStep 18727703 = 28091555) B28091555
theorem B672767 : Blo 447780 672767 := bstep (se 1 (by rfl) ⟨504575, by rfl⟩ : syracuseStep 672767 = 1009151) B1009151
theorem B673145 : Blo 447780 673145 := bstep (se 2 (by rfl) ⟨252429, by rfl⟩ : syracuseStep 673145 = 504859) B504859
theorem B640495 : Blo 447780 640495 := bstep (se 1 (by rfl) ⟨480371, by rfl⟩ : syracuseStep 640495 = 960743) B960743
theorem B4867739 : Blo 447780 4867739 := bstep (se 1 (by rfl) ⟨3650804, by rfl⟩ : syracuseStep 4867739 = 7301609) B7301609
theorem B674543 : Blo 447780 674543 := bstep (se 1 (by rfl) ⟨505907, by rfl⟩ : syracuseStep 674543 = 1011815) B1011815
theorem B674927 : Blo 447780 674927 := bstep (se 1 (by rfl) ⟨506195, by rfl⟩ : syracuseStep 674927 = 1012391) B1012391
theorem B1625579 : Blo 447780 1625579 := bstep (se 1 (by rfl) ⟨1219184, by rfl⟩ : syracuseStep 1625579 = 2438369) B2438369
theorem B1920905 : Blo 447780 1920905 := bstep (se 2 (by rfl) ⟨720339, by rfl⟩ : syracuseStep 1920905 = 1440679) B1440679
theorem B21909487 : Blo 447780 21909487 := bstep (se 1 (by rfl) ⟨16432115, by rfl⟩ : syracuseStep 21909487 = 32864231) B32864231
theorem B448359 : Blo 447780 448359 := bstep (se 1 (by rfl) ⟨336269, by rfl⟩ : syracuseStep 448359 = 672539) B672539
theorem B448367 : Blo 447780 448367 := bstep (se 1 (by rfl) ⟨336275, by rfl⟩ : syracuseStep 448367 = 672551) B672551
theorem B450607 : Blo 447780 450607 := bstep (se 1 (by rfl) ⟨337955, by rfl⟩ : syracuseStep 450607 = 675911) B675911
theorem B1007783 : Blo 447780 1007783 := bstep (se 1 (by rfl) ⟨755837, by rfl⟩ : syracuseStep 1007783 = 1511675) B1511675
theorem B450843 : Blo 447780 450843 := bstep (se 1 (by rfl) ⟨338132, by rfl⟩ : syracuseStep 450843 = 676265) B676265
theorem B2286305 : Blo 447780 2286305 := bstep (se 2 (by rfl) ⟨857364, by rfl⟩ : syracuseStep 2286305 = 1714729) B1714729
theorem B451431 : Blo 447780 451431 := bstep (se 1 (by rfl) ⟨338573, by rfl⟩ : syracuseStep 451431 = 677147) B677147
theorem B1009871 : Blo 447780 1009871 := bstep (se 1 (by rfl) ⟨757403, by rfl⟩ : syracuseStep 1009871 = 1514807) B1514807
theorem B813439 : Blo 447780 813439 := bstep (se 1 (by rfl) ⟨610079, by rfl⟩ : syracuseStep 813439 = 1220159) B1220159
theorem B1010267 : Blo 447780 1010267 := bstep (se 1 (by rfl) ⟨757700, by rfl⟩ : syracuseStep 1010267 = 1515401) B1515401
theorem B1012031 : Blo 447780 1012031 := bstep (se 1 (by rfl) ⟨759023, by rfl⟩ : syracuseStep 1012031 = 1518047) B1518047
theorem B1012265 : Blo 447780 1012265 := bstep (se 2 (by rfl) ⟨379599, by rfl⟩ : syracuseStep 1012265 = 759199) B759199
theorem B4911707 : Blo 447780 4911707 := bstep (se 1 (by rfl) ⟨3683780, by rfl⟩ : syracuseStep 4911707 = 7367561) B7367561
theorem B4092527 : Blo 447780 4092527 := bstep (se 1 (by rfl) ⟨3069395, by rfl⟩ : syracuseStep 4092527 = 6138791) B6138791
theorem B1013759 : Blo 447780 1013759 := bstep (se 1 (by rfl) ⟨760319, by rfl⟩ : syracuseStep 1013759 = 1520639) B1520639
theorem B2160749 : Blo 447780 2160749 := bstep (se 3 (by rfl) ⟨405140, by rfl⟩ : syracuseStep 2160749 = 810281) B810281
theorem B1014263 : Blo 447780 1014263 := bstep (se 1 (by rfl) ⟨760697, by rfl⟩ : syracuseStep 1014263 = 1521395) B1521395
theorem B6487087 : Blo 447780 6487087 := bstep (se 1 (by rfl) ⟨4865315, by rfl⟩ : syracuseStep 6487087 = 9730631) B9730631
theorem B1015199 : Blo 447780 1015199 := bstep (se 1 (by rfl) ⟨761399, by rfl⟩ : syracuseStep 1015199 = 1522799) B1522799
theorem B21397567 : Blo 447780 21397567 := bstep (se 1 (by rfl) ⟨16048175, by rfl⟩ : syracuseStep 21397567 = 32096351) B32096351
theorem B12485135 : Blo 447780 12485135 := bstep (se 1 (by rfl) ⟨9363851, by rfl⟩ : syracuseStep 12485135 = 18727703) B18727703
theorem B3245159 : Blo 447780 3245159 := bstep (se 1 (by rfl) ⟨2433869, by rfl⟩ : syracuseStep 3245159 = 4867739) B4867739
theorem B3409289 : Blo 447780 3409289 := bstep (se 2 (by rfl) ⟨1278483, by rfl⟩ : syracuseStep 3409289 = 2556967) B2556967
theorem B853993 : Blo 447780 853993 := bstep (se 2 (by rfl) ⟨320247, by rfl⟩ : syracuseStep 853993 = 640495) B640495
theorem B1083719 : Blo 447780 1083719 := bstep (se 1 (by rfl) ⟨812789, by rfl⟩ : syracuseStep 1083719 = 1625579) B1625579
theorem B10979657 : Blo 447780 10979657 := bstep (se 2 (by rfl) ⟨4117371, by rfl⟩ : syracuseStep 10979657 = 8234743) B8234743
theorem B1280569 : Blo 447780 1280569 := bstep (se 2 (by rfl) ⟨480213, by rfl⟩ : syracuseStep 1280569 = 960427) B960427
theorem B1280603 : Blo 447780 1280603 := bstep (se 1 (by rfl) ⟨960452, by rfl⟩ : syracuseStep 1280603 = 1920905) B1920905
theorem B854783 : Blo 447780 854783 := bstep (se 1 (by rfl) ⟨641087, by rfl⟩ : syracuseStep 854783 = 1282175) B1282175
theorem B3410747 : Blo 447780 3410747 := bstep (se 1 (by rfl) ⟨2558060, by rfl⟩ : syracuseStep 3410747 = 5116121) B5116121
theorem B1084585 : Blo 447780 1084585 := bstep (se 2 (by rfl) ⟨406719, by rfl⟩ : syracuseStep 1084585 = 813439) B813439
theorem B2625533 : Blo 447780 2625533 := bstep (se 3 (by rfl) ⟨492287, by rfl⟩ : syracuseStep 2625533 = 984575) B984575
theorem B1511783 : Blo 447780 1511783 := bstep (se 1 (by rfl) ⟨1133837, by rfl⟩ : syracuseStep 1511783 = 2267675) B2267675
theorem B1381715 : Blo 447780 1381715 := bstep (se 1 (by rfl) ⟨1036286, by rfl⟩ : syracuseStep 1381715 = 2072573) B2072573
theorem B1513511 : Blo 447780 1513511 := bstep (se 1 (by rfl) ⟨1135133, by rfl⟩ : syracuseStep 1513511 = 2270267) B2270267
theorem B9705905 : Blo 447780 9705905 := bstep (se 2 (by rfl) ⟨3639714, by rfl⟩ : syracuseStep 9705905 = 7279429) B7279429
theorem B1514591 : Blo 447780 1514591 := bstep (se 1 (by rfl) ⟨1135943, by rfl⟩ : syracuseStep 1514591 = 2271887) B2271887
theorem B4333337 : Blo 447780 4333337 := bstep (se 2 (by rfl) ⟨1625001, by rfl⟩ : syracuseStep 4333337 = 3250003) B3250003
theorem B2891659 : Blo 447780 2891659 := bstep (se 1 (by rfl) ⟨2168744, by rfl⟩ : syracuseStep 2891659 = 4337489) B4337489
theorem B2728351 : Blo 447780 2728351 := bstep (se 1 (by rfl) ⟨2046263, by rfl⟩ : syracuseStep 2728351 = 4092527) B4092527
theorem B4107449 : Blo 447780 4107449 := bstep (se 2 (by rfl) ⟨1540293, by rfl⟩ : syracuseStep 4107449 = 3080587) B3080587
theorem B962075 : Blo 447780 962075 := bstep (se 1 (by rfl) ⟨721556, by rfl⟩ : syracuseStep 962075 = 1443113) B1443113
theorem B1618487 : Blo 447780 1618487 := bstep (se 1 (by rfl) ⟨1213865, by rfl⟩ : syracuseStep 1618487 = 2427731) B2427731
theorem B637807 : Blo 447780 637807 := bstep (se 1 (by rfl) ⟨478355, by rfl⟩ : syracuseStep 637807 = 956711) B956711
theorem B506911 : Blo 447780 506911 := bstep (se 1 (by rfl) ⟨380183, by rfl⟩ : syracuseStep 506911 = 760367) B760367
theorem B29212649 : Blo 447780 29212649 := bstep (se 2 (by rfl) ⟨10954743, by rfl⟩ : syracuseStep 29212649 = 21909487) B21909487
theorem B671855 : Blo 447780 671855 := bstep (se 1 (by rfl) ⟨503891, by rfl⟩ : syracuseStep 671855 = 1007783) B1007783
theorem B1524203 : Blo 447780 1524203 := bstep (se 1 (by rfl) ⟨1143152, by rfl⟩ : syracuseStep 1524203 = 2286305) B2286305
theorem B639743 : Blo 447780 639743 := bstep (se 1 (by rfl) ⟨479807, by rfl⟩ : syracuseStep 639743 = 959615) B959615
theorem B673247 : Blo 447780 673247 := bstep (se 1 (by rfl) ⟨504935, by rfl⟩ : syracuseStep 673247 = 1009871) B1009871
theorem B12961255 : Blo 447780 12961255 := bstep (se 1 (by rfl) ⟨9720941, by rfl⟩ : syracuseStep 12961255 = 19441883) B19441883
theorem B673511 : Blo 447780 673511 := bstep (se 1 (by rfl) ⟨505133, by rfl⟩ : syracuseStep 673511 = 1010267) B1010267
theorem B674687 : Blo 447780 674687 := bstep (se 1 (by rfl) ⟨506015, by rfl⟩ : syracuseStep 674687 = 1012031) B1012031
theorem B674843 : Blo 447780 674843 := bstep (se 1 (by rfl) ⟨506132, by rfl⟩ : syracuseStep 674843 = 1012265) B1012265
theorem B46681697 : Blo 447780 46681697 := bstep (se 2 (by rfl) ⟨17505636, by rfl⟩ : syracuseStep 46681697 = 35011273) B35011273
theorem B675839 : Blo 447780 675839 := bstep (se 1 (by rfl) ⟨506879, by rfl⟩ : syracuseStep 675839 = 1013759) B1013759
theorem B675977 : Blo 447780 675977 := bstep (se 2 (by rfl) ⟨253491, by rfl⟩ : syracuseStep 675977 = 506983) B506983
theorem B676175 : Blo 447780 676175 := bstep (se 1 (by rfl) ⟨507131, by rfl⟩ : syracuseStep 676175 = 1014263) B1014263
theorem B676799 : Blo 447780 676799 := bstep (se 1 (by rfl) ⟨507599, by rfl⟩ : syracuseStep 676799 = 1015199) B1015199
theorem B448511 : Blo 447780 448511 := bstep (se 1 (by rfl) ⟨336383, by rfl⟩ : syracuseStep 448511 = 672767) B672767
theorem B448763 : Blo 447780 448763 := bstep (se 1 (by rfl) ⟨336572, by rfl⟩ : syracuseStep 448763 = 673145) B673145
theorem B449695 : Blo 447780 449695 := bstep (se 1 (by rfl) ⟨337271, by rfl⟩ : syracuseStep 449695 = 674543) B674543
theorem B449951 : Blo 447780 449951 := bstep (se 1 (by rfl) ⟨337463, by rfl⟩ : syracuseStep 449951 = 674927) B674927
theorem B1140905 : Blo 447780 1140905 := bstep (se 2 (by rfl) ⟨427839, by rfl⟩ : syracuseStep 1140905 = 855679) B855679
theorem B3174227 : Blo 447780 3174227 := bstep (se 1 (by rfl) ⟨2380670, by rfl⟩ : syracuseStep 3174227 = 4761341) B4761341
theorem B1012679 : Blo 447780 1012679 := bstep (se 1 (by rfl) ⟨759509, by rfl⟩ : syracuseStep 1012679 = 1519019) B1519019
theorem B1012895 : Blo 447780 1012895 := bstep (se 1 (by rfl) ⟨759671, by rfl⟩ : syracuseStep 1012895 = 1519343) B1519343
theorem B13334003 : Blo 447780 13334003 := bstep (se 1 (by rfl) ⟨10000502, by rfl⟩ : syracuseStep 13334003 = 20001005) B20001005
theorem B3274471 : Blo 447780 3274471 := bstep (se 1 (by rfl) ⟨2455853, by rfl⟩ : syracuseStep 3274471 = 4911707) B4911707
theorem B8649449 : Blo 447780 8649449 := bstep (se 2 (by rfl) ⟨3243543, by rfl⟩ : syracuseStep 8649449 = 6487087) B6487087
theorem B1440499 : Blo 447780 1440499 := bstep (se 1 (by rfl) ⟨1080374, by rfl⟩ : syracuseStep 1440499 = 2160749) B2160749
theorem B1016135 : Blo 447780 1016135 := bstep (se 1 (by rfl) ⟨762101, by rfl⟩ : syracuseStep 1016135 = 1524203) B1524203
theorem B3637801 : Blo 447780 3637801 := bstep (se 2 (by rfl) ⟨1364175, by rfl⟩ : syracuseStep 3637801 = 2728351) B2728351
theorem B2163439 : Blo 447780 2163439 := bstep (se 1 (by rfl) ⟨1622579, by rfl⟩ : syracuseStep 2163439 = 3245159) B3245159
theorem B33293693 : Blo 447780 33293693 := bstep (se 3 (by rfl) ⟨6242567, by rfl⟩ : syracuseStep 33293693 = 12485135) B12485135
theorem B853735 : Blo 447780 853735 := bstep (se 1 (by rfl) ⟨640301, by rfl⟩ : syracuseStep 853735 = 1280603) B1280603
theorem B1705981 : Blo 447780 1705981 := bstep (se 3 (by rfl) ⟨319871, by rfl⟩ : syracuseStep 1705981 = 639743) B639743
theorem B1707425 : Blo 447780 1707425 := bstep (se 2 (by rfl) ⟨640284, by rfl⟩ : syracuseStep 1707425 = 1280569) B1280569
theorem B921143 : Blo 447780 921143 := bstep (se 1 (by rfl) ⟨690857, by rfl⟩ : syracuseStep 921143 = 1381715) B1381715
theorem B1446113 : Blo 447780 1446113 := bstep (se 2 (by rfl) ⟨542292, by rfl⟩ : syracuseStep 1446113 = 1084585) B1084585
theorem B2888891 : Blo 447780 2888891 := bstep (se 1 (by rfl) ⟨2166668, by rfl⟩ : syracuseStep 2888891 = 4333337) B4333337
theorem B2889917 : Blo 447780 2889917 := bstep (se 3 (by rfl) ⟨541859, by rfl⟩ : syracuseStep 2889917 = 1083719) B1083719
theorem B760603 : Blo 447780 760603 := bstep (se 1 (by rfl) ⟨570452, by rfl⟩ : syracuseStep 760603 = 1140905) B1140905
theorem B8889335 : Blo 447780 8889335 := bstep (se 1 (by rfl) ⟨6667001, by rfl⟩ : syracuseStep 8889335 = 13334003) B13334003
theorem B2565533 : Blo 447780 2565533 := bstep (se 3 (by rfl) ⟨481037, by rfl⟩ : syracuseStep 2565533 = 962075) B962075
theorem B19475099 : Blo 447780 19475099 := bstep (se 1 (by rfl) ⟨14606324, by rfl⟩ : syracuseStep 19475099 = 29212649) B29212649
theorem B2272859 : Blo 447780 2272859 := bstep (se 1 (by rfl) ⟨1704644, by rfl⟩ : syracuseStep 2272859 = 3409289) B3409289
theorem B7319771 : Blo 447780 7319771 := bstep (se 1 (by rfl) ⟨5489828, by rfl⟩ : syracuseStep 7319771 = 10979657) B10979657
theorem B569855 : Blo 447780 569855 := bstep (se 1 (by rfl) ⟨427391, by rfl⟩ : syracuseStep 569855 = 854783) B854783
theorem B2273831 : Blo 447780 2273831 := bstep (se 1 (by rfl) ⟨1705373, by rfl⟩ : syracuseStep 2273831 = 3410747) B3410747
theorem B17281673 : Blo 447780 17281673 := bstep (se 2 (by rfl) ⟨6480627, by rfl⟩ : syracuseStep 17281673 = 12961255) B12961255
theorem B1750355 : Blo 447780 1750355 := bstep (se 1 (by rfl) ⟨1312766, by rfl⟩ : syracuseStep 1750355 = 2625533) B2625533
theorem B6470603 : Blo 447780 6470603 := bstep (se 1 (by rfl) ⟨4852952, by rfl⟩ : syracuseStep 6470603 = 9705905) B9705905
theorem B2738299 : Blo 447780 2738299 := bstep (se 1 (by rfl) ⟨2053724, by rfl⟩ : syracuseStep 2738299 = 4107449) B4107449
theorem B2116151 : Blo 447780 2116151 := bstep (se 1 (by rfl) ⟨1587113, by rfl⟩ : syracuseStep 2116151 = 3174227) B3174227
theorem B675119 : Blo 447780 675119 := bstep (se 1 (by rfl) ⟨506339, by rfl⟩ : syracuseStep 675119 = 1012679) B1012679
theorem B675263 : Blo 447780 675263 := bstep (se 1 (by rfl) ⟨506447, by rfl⟩ : syracuseStep 675263 = 1012895) B1012895
theorem B1920665 : Blo 447780 1920665 := bstep (se 2 (by rfl) ⟨720249, by rfl⟩ : syracuseStep 1920665 = 1440499) B1440499
theorem B675881 : Blo 447780 675881 := bstep (se 2 (by rfl) ⟨253455, by rfl⟩ : syracuseStep 675881 = 506911) B506911
theorem B3855545 : Blo 447780 3855545 := bstep (se 2 (by rfl) ⟨1445829, by rfl⟩ : syracuseStep 3855545 = 2891659) B2891659
theorem B447903 : Blo 447780 447903 := bstep (se 1 (by rfl) ⟨335927, by rfl⟩ : syracuseStep 447903 = 671855) B671855
theorem B28530089 : Blo 447780 28530089 := bstep (se 2 (by rfl) ⟨10698783, by rfl⟩ : syracuseStep 28530089 = 21397567) B21397567
theorem B448831 : Blo 447780 448831 := bstep (se 1 (by rfl) ⟨336623, by rfl⟩ : syracuseStep 448831 = 673247) B673247
theorem B449007 : Blo 447780 449007 := bstep (se 1 (by rfl) ⟨336755, by rfl⟩ : syracuseStep 449007 = 673511) B673511
theorem B449791 : Blo 447780 449791 := bstep (se 1 (by rfl) ⟨337343, by rfl⟩ : syracuseStep 449791 = 674687) B674687
theorem B449895 : Blo 447780 449895 := bstep (se 1 (by rfl) ⟨337421, by rfl⟩ : syracuseStep 449895 = 674843) B674843
theorem B31121131 : Blo 447780 31121131 := bstep (se 1 (by rfl) ⟨23340848, by rfl⟩ : syracuseStep 31121131 = 46681697) B46681697
theorem B1138657 : Blo 447780 1138657 := bstep (se 2 (by rfl) ⟨426996, by rfl⟩ : syracuseStep 1138657 = 853993) B853993
theorem B450559 : Blo 447780 450559 := bstep (se 1 (by rfl) ⟨337919, by rfl⟩ : syracuseStep 450559 = 675839) B675839
theorem B450651 : Blo 447780 450651 := bstep (se 1 (by rfl) ⟨337988, by rfl⟩ : syracuseStep 450651 = 675977) B675977
theorem B450783 : Blo 447780 450783 := bstep (se 1 (by rfl) ⟨338087, by rfl⟩ : syracuseStep 450783 = 676175) B676175
theorem B1007855 : Blo 447780 1007855 := bstep (se 1 (by rfl) ⟨755891, by rfl⟩ : syracuseStep 1007855 = 1511783) B1511783
theorem B451199 : Blo 447780 451199 := bstep (se 1 (by rfl) ⟨338399, by rfl⟩ : syracuseStep 451199 = 676799) B676799
theorem B1009007 : Blo 447780 1009007 := bstep (se 1 (by rfl) ⟨756755, by rfl⟩ : syracuseStep 1009007 = 1513511) B1513511
theorem B1009727 : Blo 447780 1009727 := bstep (se 1 (by rfl) ⟨757295, by rfl⟩ : syracuseStep 1009727 = 1514591) B1514591
theorem B1078991 : Blo 447780 1078991 := bstep (se 1 (by rfl) ⟨809243, by rfl⟩ : syracuseStep 1078991 = 1618487) B1618487
theorem B850409 : Blo 447780 850409 := bstep (se 2 (by rfl) ⟨318903, by rfl⟩ : syracuseStep 850409 = 637807) B637807
theorem B17463845 : Blo 447780 17463845 := bstep (se 4 (by rfl) ⟨1637235, by rfl⟩ : syracuseStep 17463845 = 3274471) B3274471
theorem B5766299 : Blo 447780 5766299 := bstep (se 1 (by rfl) ⟨4324724, by rfl⟩ : syracuseStep 5766299 = 8649449) B8649449
theorem B4850401 : Blo 447780 4850401 := bstep (se 2 (by rfl) ⟨1818900, by rfl⟩ : syracuseStep 4850401 = 3637801) B3637801
theorem B2884585 : Blo 447780 2884585 := bstep (se 2 (by rfl) ⟨1081719, by rfl⟩ : syracuseStep 2884585 = 2163439) B2163439
theorem B1410767 : Blo 447780 1410767 := bstep (se 1 (by rfl) ⟨1058075, by rfl⟩ : syracuseStep 1410767 = 2116151) B2116151
theorem B1280443 : Blo 447780 1280443 := bstep (se 1 (by rfl) ⟨960332, by rfl⟩ : syracuseStep 1280443 = 1920665) B1920665
theorem B1710355 : Blo 447780 1710355 := bstep (se 1 (by rfl) ⟨1282766, by rfl⟩ : syracuseStep 1710355 = 2565533) B2565533
theorem B12983399 : Blo 447780 12983399 := bstep (se 1 (by rfl) ⟨9737549, by rfl⟩ : syracuseStep 12983399 = 19475099) B19475099
theorem B1515239 : Blo 447780 1515239 := bstep (se 1 (by rfl) ⟨1136429, by rfl⟩ : syracuseStep 1515239 = 2272859) B2272859
theorem B1515887 : Blo 447780 1515887 := bstep (se 1 (by rfl) ⟨1136915, by rfl⟩ : syracuseStep 1515887 = 2273831) B2273831
theorem B566939 : Blo 447780 566939 := bstep (se 1 (by rfl) ⟨425204, by rfl⟩ : syracuseStep 566939 = 850409) B850409
theorem B11642563 : Blo 447780 11642563 := bstep (se 1 (by rfl) ⟨8731922, by rfl⟩ : syracuseStep 11642563 = 17463845) B17463845
theorem B3844199 : Blo 447780 3844199 := bstep (se 1 (by rfl) ⟨2883149, by rfl⟩ : syracuseStep 3844199 = 5766299) B5766299
theorem B41494841 : Blo 447780 41494841 := bstep (se 2 (by rfl) ⟨15560565, by rfl⟩ : syracuseStep 41494841 = 31121131) B31121131
theorem B1518209 : Blo 447780 1518209 := bstep (se 2 (by rfl) ⟨569328, by rfl⟩ : syracuseStep 1518209 = 1138657) B1138657
theorem B22195795 : Blo 447780 22195795 := bstep (se 1 (by rfl) ⟨16646846, by rfl⟩ : syracuseStep 22195795 = 33293693) B33293693
theorem B1519613 : Blo 447780 1519613 := bstep (se 3 (by rfl) ⟨284927, by rfl⟩ : syracuseStep 1519613 = 569855) B569855
theorem B2274641 : Blo 447780 2274641 := bstep (se 2 (by rfl) ⟨852990, by rfl⟩ : syracuseStep 2274641 = 1705981) B1705981
theorem B964075 : Blo 447780 964075 := bstep (se 1 (by rfl) ⟨723056, by rfl⟩ : syracuseStep 964075 = 1446113) B1446113
theorem B3651065 : Blo 447780 3651065 := bstep (se 2 (by rfl) ⟨1369149, by rfl⟩ : syracuseStep 3651065 = 2738299) B2738299
theorem B2570363 : Blo 447780 2570363 := bstep (se 1 (by rfl) ⟨1927772, by rfl⟩ : syracuseStep 2570363 = 3855545) B3855545
theorem B19020059 : Blo 447780 19020059 := bstep (se 1 (by rfl) ⟨14265044, by rfl⟩ : syracuseStep 19020059 = 28530089) B28530089
theorem B671903 : Blo 447780 671903 := bstep (se 1 (by rfl) ⟨503927, by rfl⟩ : syracuseStep 671903 = 1007855) B1007855
theorem B672671 : Blo 447780 672671 := bstep (se 1 (by rfl) ⟨504503, by rfl⟩ : syracuseStep 672671 = 1009007) B1009007
theorem B673151 : Blo 447780 673151 := bstep (se 1 (by rfl) ⟨504863, by rfl⟩ : syracuseStep 673151 = 1009727) B1009727
theorem B11521115 : Blo 447780 11521115 := bstep (se 1 (by rfl) ⟨8640836, by rfl⟩ : syracuseStep 11521115 = 17281673) B17281673
theorem B1166903 : Blo 447780 1166903 := bstep (se 1 (by rfl) ⟨875177, by rfl⟩ : syracuseStep 1166903 = 1750355) B1750355
theorem B4313735 : Blo 447780 4313735 := bstep (se 1 (by rfl) ⟨3235301, by rfl⟩ : syracuseStep 4313735 = 6470603) B6470603
theorem B677423 : Blo 447780 677423 := bstep (se 1 (by rfl) ⟨508067, by rfl⟩ : syracuseStep 677423 = 1016135) B1016135
theorem B450079 : Blo 447780 450079 := bstep (se 1 (by rfl) ⟨337559, by rfl⟩ : syracuseStep 450079 = 675119) B675119
theorem B1138283 : Blo 447780 1138283 := bstep (se 1 (by rfl) ⟨853712, by rfl⟩ : syracuseStep 1138283 = 1707425) B1707425
theorem B450175 : Blo 447780 450175 := bstep (se 1 (by rfl) ⟨337631, by rfl⟩ : syracuseStep 450175 = 675263) B675263
theorem B1138313 : Blo 447780 1138313 := bstep (se 2 (by rfl) ⟨426867, by rfl⟩ : syracuseStep 1138313 = 853735) B853735
theorem B450587 : Blo 447780 450587 := bstep (se 1 (by rfl) ⟨337940, by rfl⟩ : syracuseStep 450587 = 675881) B675881
theorem B1925927 : Blo 447780 1925927 := bstep (se 1 (by rfl) ⟨1444445, by rfl⟩ : syracuseStep 1925927 = 2888891) B2888891
theorem B1926611 : Blo 447780 1926611 := bstep (se 1 (by rfl) ⟨1444958, by rfl⟩ : syracuseStep 1926611 = 2889917) B2889917
theorem B5926223 : Blo 447780 5926223 := bstep (se 1 (by rfl) ⟨4444667, by rfl⟩ : syracuseStep 5926223 = 8889335) B8889335
theorem B4879847 : Blo 447780 4879847 := bstep (se 1 (by rfl) ⟨3659885, by rfl⟩ : syracuseStep 4879847 = 7319771) B7319771
theorem B1014137 : Blo 447780 1014137 := bstep (se 2 (by rfl) ⟨380301, by rfl⟩ : syracuseStep 1014137 = 760603) B760603
theorem B719327 : Blo 447780 719327 := bstep (se 1 (by rfl) ⟨539495, by rfl⟩ : syracuseStep 719327 = 1078991) B1078991
theorem B2456381 : Blo 447780 2456381 := bstep (se 3 (by rfl) ⟨460571, by rfl⟩ : syracuseStep 2456381 = 921143) B921143
theorem B1707257 : Blo 447780 1707257 := bstep (se 2 (by rfl) ⟨640221, by rfl⟩ : syracuseStep 1707257 = 1280443) B1280443
theorem B1511837 : Blo 447780 1511837 := bstep (se 3 (by rfl) ⟨283469, by rfl⟩ : syracuseStep 1511837 = 566939) B566939
theorem B8655599 : Blo 447780 8655599 := bstep (se 1 (by rfl) ⟨6491699, by rfl⟩ : syracuseStep 8655599 = 12983399) B12983399
theorem B29594393 : Blo 447780 29594393 := bstep (se 2 (by rfl) ⟨11097897, by rfl⟩ : syracuseStep 29594393 = 22195795) B22195795
theorem B758855 : Blo 447780 758855 := bstep (se 1 (by rfl) ⟨569141, by rfl⟩ : syracuseStep 758855 = 1138283) B1138283
theorem B758875 : Blo 447780 758875 := bstep (se 1 (by rfl) ⟨569156, by rfl⟩ : syracuseStep 758875 = 1138313) B1138313
theorem B1283951 : Blo 447780 1283951 := bstep (se 1 (by rfl) ⟨962963, by rfl⟩ : syracuseStep 1283951 = 1925927) B1925927
theorem B1284407 : Blo 447780 1284407 := bstep (se 1 (by rfl) ⟨963305, by rfl⟩ : syracuseStep 1284407 = 1926611) B1926611
theorem B2562799 : Blo 447780 2562799 := bstep (se 1 (by rfl) ⟨1922099, by rfl⟩ : syracuseStep 2562799 = 3844199) B3844199
theorem B27663227 : Blo 447780 27663227 := bstep (se 1 (by rfl) ⟨20747420, by rfl⟩ : syracuseStep 27663227 = 41494841) B41494841
theorem B1285433 : Blo 447780 1285433 := bstep (se 2 (by rfl) ⟨482037, by rfl⟩ : syracuseStep 1285433 = 964075) B964075
theorem B1516427 : Blo 447780 1516427 := bstep (se 1 (by rfl) ⟨1137320, by rfl⟩ : syracuseStep 1516427 = 2274641) B2274641
theorem B3253231 : Blo 447780 3253231 := bstep (se 1 (by rfl) ⟨2439923, by rfl⟩ : syracuseStep 3253231 = 4879847) B4879847
theorem B2434043 : Blo 447780 2434043 := bstep (se 1 (by rfl) ⟨1825532, by rfl⟩ : syracuseStep 2434043 = 3651065) B3651065
theorem B1713575 : Blo 447780 1713575 := bstep (se 1 (by rfl) ⟨1285181, by rfl⟩ : syracuseStep 1713575 = 2570363) B2570363
theorem B6467201 : Blo 447780 6467201 := bstep (se 2 (by rfl) ⟨2425200, by rfl⟩ : syracuseStep 6467201 = 4850401) B4850401
theorem B3846113 : Blo 447780 3846113 := bstep (se 2 (by rfl) ⟨1442292, by rfl⟩ : syracuseStep 3846113 = 2884585) B2884585
theorem B7680743 : Blo 447780 7680743 := bstep (se 1 (by rfl) ⟨5760557, by rfl⟩ : syracuseStep 7680743 = 11521115) B11521115
theorem B1918205 : Blo 447780 1918205 := bstep (se 3 (by rfl) ⟨359663, by rfl⟩ : syracuseStep 1918205 = 719327) B719327
theorem B3950815 : Blo 447780 3950815 := bstep (se 1 (by rfl) ⟨2963111, by rfl⟩ : syracuseStep 3950815 = 5926223) B5926223
theorem B2280473 : Blo 447780 2280473 := bstep (se 2 (by rfl) ⟨855177, by rfl⟩ : syracuseStep 2280473 = 1710355) B1710355
theorem B676091 : Blo 447780 676091 := bstep (se 1 (by rfl) ⟨507068, by rfl⟩ : syracuseStep 676091 = 1014137) B1014137
theorem B447935 : Blo 447780 447935 := bstep (se 1 (by rfl) ⟨335951, by rfl⟩ : syracuseStep 447935 = 671903) B671903
theorem B448447 : Blo 447780 448447 := bstep (se 1 (by rfl) ⟨336335, by rfl⟩ : syracuseStep 448447 = 672671) B672671
theorem B448767 : Blo 447780 448767 := bstep (se 1 (by rfl) ⟨336575, by rfl⟩ : syracuseStep 448767 = 673151) B673151
theorem B940511 : Blo 447780 940511 := bstep (se 1 (by rfl) ⟨705383, by rfl⟩ : syracuseStep 940511 = 1410767) B1410767
theorem B15523417 : Blo 447780 15523417 := bstep (se 2 (by rfl) ⟨5821281, by rfl⟩ : syracuseStep 15523417 = 11642563) B11642563
theorem B777935 : Blo 447780 777935 := bstep (se 1 (by rfl) ⟨583451, by rfl⟩ : syracuseStep 777935 = 1166903) B1166903
theorem B2875823 : Blo 447780 2875823 := bstep (se 1 (by rfl) ⟨2156867, by rfl⟩ : syracuseStep 2875823 = 4313735) B4313735
theorem B451615 : Blo 447780 451615 := bstep (se 1 (by rfl) ⟨338711, by rfl⟩ : syracuseStep 451615 = 677423) B677423
theorem B1010159 : Blo 447780 1010159 := bstep (se 1 (by rfl) ⟨757619, by rfl⟩ : syracuseStep 1010159 = 1515239) B1515239
theorem B1010591 : Blo 447780 1010591 := bstep (se 1 (by rfl) ⟨757943, by rfl⟩ : syracuseStep 1010591 = 1515887) B1515887
theorem B1012139 : Blo 447780 1012139 := bstep (se 1 (by rfl) ⟨759104, by rfl⟩ : syracuseStep 1012139 = 1518209) B1518209
theorem B1013075 : Blo 447780 1013075 := bstep (se 1 (by rfl) ⟨759806, by rfl⟩ : syracuseStep 1013075 = 1519613) B1519613
theorem B12680039 : Blo 447780 12680039 := bstep (se 1 (by rfl) ⟨9510029, by rfl⟩ : syracuseStep 12680039 = 19020059) B19020059
theorem B1637587 : Blo 447780 1637587 := bstep (se 1 (by rfl) ⟨1228190, by rfl⟩ : syracuseStep 1637587 = 2456381) B2456381
theorem B1278803 : Blo 447780 1278803 := bstep (se 1 (by rfl) ⟨959102, by rfl⟩ : syracuseStep 1278803 = 1918205) B1918205
theorem B5770399 : Blo 447780 5770399 := bstep (se 1 (by rfl) ⟨4327799, by rfl⟩ : syracuseStep 5770399 = 8655599) B8655599
theorem B19729595 : Blo 447780 19729595 := bstep (se 1 (by rfl) ⟨14797196, by rfl⟩ : syracuseStep 19729595 = 29594393) B29594393
theorem B856271 : Blo 447780 856271 := bstep (se 1 (by rfl) ⟨642203, by rfl⟩ : syracuseStep 856271 = 1284407) B1284407
theorem B627007 : Blo 447780 627007 := bstep (se 1 (by rfl) ⟨470255, by rfl⟩ : syracuseStep 627007 = 940511) B940511
theorem B856955 : Blo 447780 856955 := bstep (se 1 (by rfl) ⟨642716, by rfl⟩ : syracuseStep 856955 = 1285433) B1285433
theorem B2564075 : Blo 447780 2564075 := bstep (se 1 (by rfl) ⟨1923056, by rfl⟩ : syracuseStep 2564075 = 3846113) B3846113
theorem B5120495 : Blo 447780 5120495 := bstep (se 1 (by rfl) ⟨3840371, by rfl⟩ : syracuseStep 5120495 = 7680743) B7680743
theorem B3417065 : Blo 447780 3417065 := bstep (se 2 (by rfl) ⟨1281399, by rfl⟩ : syracuseStep 3417065 = 2562799) B2562799
theorem B2074493 : Blo 447780 2074493 := bstep (se 3 (by rfl) ⟨388967, by rfl⟩ : syracuseStep 2074493 = 777935) B777935
theorem B4337641 : Blo 447780 4337641 := bstep (se 2 (by rfl) ⟨1626615, by rfl⟩ : syracuseStep 4337641 = 3253231) B3253231
theorem B1520315 : Blo 447780 1520315 := bstep (se 1 (by rfl) ⟨1140236, by rfl⟩ : syracuseStep 1520315 = 2280473) B2280473
theorem B505903 : Blo 447780 505903 := bstep (se 1 (by rfl) ⟨379427, by rfl⟩ : syracuseStep 505903 = 758855) B758855
theorem B3423869 : Blo 447780 3423869 := bstep (se 3 (by rfl) ⟨641975, by rfl⟩ : syracuseStep 3423869 = 1283951) B1283951
theorem B1917215 : Blo 447780 1917215 := bstep (se 1 (by rfl) ⟨1437911, by rfl⟩ : syracuseStep 1917215 = 2875823) B2875823
theorem B1622695 : Blo 447780 1622695 := bstep (se 1 (by rfl) ⟨1217021, by rfl⟩ : syracuseStep 1622695 = 2434043) B2434043
theorem B673439 : Blo 447780 673439 := bstep (se 1 (by rfl) ⟨505079, by rfl⟩ : syracuseStep 673439 = 1010159) B1010159
theorem B673727 : Blo 447780 673727 := bstep (se 1 (by rfl) ⟨505295, by rfl⟩ : syracuseStep 673727 = 1010591) B1010591
theorem B4311467 : Blo 447780 4311467 := bstep (se 1 (by rfl) ⟨3233600, by rfl⟩ : syracuseStep 4311467 = 6467201) B6467201
theorem B674759 : Blo 447780 674759 := bstep (se 1 (by rfl) ⟨506069, by rfl⟩ : syracuseStep 674759 = 1012139) B1012139
theorem B675383 : Blo 447780 675383 := bstep (se 1 (by rfl) ⟨506537, by rfl⟩ : syracuseStep 675383 = 1013075) B1013075
theorem B2183449 : Blo 447780 2183449 := bstep (se 2 (by rfl) ⟨818793, by rfl⟩ : syracuseStep 2183449 = 1637587) B1637587
theorem B20697889 : Blo 447780 20697889 := bstep (se 2 (by rfl) ⟨7761708, by rfl⟩ : syracuseStep 20697889 = 15523417) B15523417
theorem B1138171 : Blo 447780 1138171 := bstep (se 1 (by rfl) ⟨853628, by rfl⟩ : syracuseStep 1138171 = 1707257) B1707257
theorem B450727 : Blo 447780 450727 := bstep (se 1 (by rfl) ⟨338045, by rfl⟩ : syracuseStep 450727 = 676091) B676091
theorem B1007891 : Blo 447780 1007891 := bstep (se 1 (by rfl) ⟨755918, by rfl⟩ : syracuseStep 1007891 = 1511837) B1511837
theorem B5267753 : Blo 447780 5267753 := bstep (se 2 (by rfl) ⟨1975407, by rfl⟩ : syracuseStep 5267753 = 3950815) B3950815
theorem B18442151 : Blo 447780 18442151 := bstep (se 1 (by rfl) ⟨13831613, by rfl⟩ : syracuseStep 18442151 = 27663227) B27663227
theorem B1010951 : Blo 447780 1010951 := bstep (se 1 (by rfl) ⟨758213, by rfl⟩ : syracuseStep 1010951 = 1516427) B1516427
theorem B1142383 : Blo 447780 1142383 := bstep (se 1 (by rfl) ⟨856787, by rfl⟩ : syracuseStep 1142383 = 1713575) B1713575
theorem B1011833 : Blo 447780 1011833 := bstep (se 2 (by rfl) ⟨379437, by rfl⟩ : syracuseStep 1011833 = 758875) B758875
theorem B8453359 : Blo 447780 8453359 := bstep (se 1 (by rfl) ⟨6340019, by rfl⟩ : syracuseStep 8453359 = 12680039) B12680039
theorem B1278143 : Blo 447780 1278143 := bstep (se 1 (by rfl) ⟨958607, by rfl⟩ : syracuseStep 1278143 = 1917215) B1917215
theorem B852535 : Blo 447780 852535 := bstep (se 1 (by rfl) ⟨639401, by rfl⟩ : syracuseStep 852535 = 1278803) B1278803
theorem B2163593 : Blo 447780 2163593 := bstep (se 2 (by rfl) ⟨811347, by rfl⟩ : syracuseStep 2163593 = 1622695) B1622695
theorem B1709383 : Blo 447780 1709383 := bstep (se 1 (by rfl) ⟨1282037, by rfl⟩ : syracuseStep 1709383 = 2564075) B2564075
theorem B3511835 : Blo 447780 3511835 := bstep (se 1 (by rfl) ⟨2633876, by rfl⟩ : syracuseStep 3511835 = 5267753) B5267753
theorem B3413663 : Blo 447780 3413663 := bstep (se 1 (by rfl) ⟨2560247, by rfl⟩ : syracuseStep 3413663 = 5120495) B5120495
theorem B27597185 : Blo 447780 27597185 := bstep (se 2 (by rfl) ⟨10348944, by rfl⟩ : syracuseStep 27597185 = 20697889) B20697889
theorem B12294767 : Blo 447780 12294767 := bstep (se 1 (by rfl) ⟨9221075, by rfl⟩ : syracuseStep 12294767 = 18442151) B18442151
theorem B1517561 : Blo 447780 1517561 := bstep (se 2 (by rfl) ⟨569085, by rfl⟩ : syracuseStep 1517561 = 1138171) B1138171
theorem B13153063 : Blo 447780 13153063 := bstep (se 1 (by rfl) ⟨9864797, by rfl⟩ : syracuseStep 13153063 = 19729595) B19729595
theorem B571303 : Blo 447780 571303 := bstep (se 1 (by rfl) ⟨428477, by rfl⟩ : syracuseStep 571303 = 856955) B856955
theorem B1523177 : Blo 447780 1523177 := bstep (se 2 (by rfl) ⟨571191, by rfl⟩ : syracuseStep 1523177 = 1142383) B1142383
theorem B5783521 : Blo 447780 5783521 := bstep (se 2 (by rfl) ⟨2168820, by rfl⟩ : syracuseStep 5783521 = 4337641) B4337641
theorem B671927 : Blo 447780 671927 := bstep (se 1 (by rfl) ⟨503945, by rfl⟩ : syracuseStep 671927 = 1007891) B1007891
theorem B836009 : Blo 447780 836009 := bstep (se 2 (by rfl) ⟨313503, by rfl⟩ : syracuseStep 836009 = 627007) B627007
theorem B2278043 : Blo 447780 2278043 := bstep (se 1 (by rfl) ⟨1708532, by rfl⟩ : syracuseStep 2278043 = 3417065) B3417065
theorem B673967 : Blo 447780 673967 := bstep (se 1 (by rfl) ⟨505475, by rfl⟩ : syracuseStep 673967 = 1010951) B1010951
theorem B674537 : Blo 447780 674537 := bstep (se 2 (by rfl) ⟨252951, by rfl⟩ : syracuseStep 674537 = 505903) B505903
theorem B674555 : Blo 447780 674555 := bstep (se 1 (by rfl) ⟨505916, by rfl⟩ : syracuseStep 674555 = 1011833) B1011833
theorem B2282579 : Blo 447780 2282579 := bstep (se 1 (by rfl) ⟨1711934, by rfl⟩ : syracuseStep 2282579 = 3423869) B3423869
theorem B2283389 : Blo 447780 2283389 := bstep (se 3 (by rfl) ⟨428135, by rfl⟩ : syracuseStep 2283389 = 856271) B856271
theorem B448959 : Blo 447780 448959 := bstep (se 1 (by rfl) ⟨336719, by rfl⟩ : syracuseStep 448959 = 673439) B673439
theorem B449151 : Blo 447780 449151 := bstep (se 1 (by rfl) ⟨336863, by rfl⟩ : syracuseStep 449151 = 673727) B673727
theorem B2874311 : Blo 447780 2874311 := bstep (se 1 (by rfl) ⟨2155733, by rfl⟩ : syracuseStep 2874311 = 4311467) B4311467
theorem B449839 : Blo 447780 449839 := bstep (se 1 (by rfl) ⟨337379, by rfl⟩ : syracuseStep 449839 = 674759) B674759
theorem B450255 : Blo 447780 450255 := bstep (se 1 (by rfl) ⟨337691, by rfl⟩ : syracuseStep 450255 = 675383) B675383
theorem B7693865 : Blo 447780 7693865 := bstep (se 2 (by rfl) ⟨2885199, by rfl⟩ : syracuseStep 7693865 = 5770399) B5770399
theorem B5531981 : Blo 447780 5531981 := bstep (se 3 (by rfl) ⟨1037246, by rfl⟩ : syracuseStep 5531981 = 2074493) B2074493
theorem B2911265 : Blo 447780 2911265 := bstep (se 2 (by rfl) ⟨1091724, by rfl⟩ : syracuseStep 2911265 = 2183449) B2183449
theorem B1013543 : Blo 447780 1013543 := bstep (se 1 (by rfl) ⟨760157, by rfl⟩ : syracuseStep 1013543 = 1520315) B1520315
theorem B11271145 : Blo 447780 11271145 := bstep (se 2 (by rfl) ⟨4226679, by rfl⟩ : syracuseStep 11271145 = 8453359) B8453359
theorem B852095 : Blo 447780 852095 := bstep (se 1 (by rfl) ⟨639071, by rfl⟩ : syracuseStep 852095 = 1278143) B1278143
theorem B557339 : Blo 447780 557339 := bstep (se 1 (by rfl) ⟨418004, by rfl⟩ : syracuseStep 557339 = 836009) B836009
theorem B1442395 : Blo 447780 1442395 := bstep (se 1 (by rfl) ⟨1081796, by rfl⟩ : syracuseStep 1442395 = 2163593) B2163593
theorem B8196511 : Blo 447780 8196511 := bstep (se 1 (by rfl) ⟨6147383, by rfl⟩ : syracuseStep 8196511 = 12294767) B12294767
theorem B17537417 : Blo 447780 17537417 := bstep (se 2 (by rfl) ⟨6576531, by rfl⟩ : syracuseStep 17537417 = 13153063) B13153063
theorem B1940843 : Blo 447780 1940843 := bstep (se 1 (by rfl) ⟨1455632, by rfl⟩ : syracuseStep 1940843 = 2911265) B2911265
theorem B761737 : Blo 447780 761737 := bstep (se 2 (by rfl) ⟨285651, by rfl⟩ : syracuseStep 761737 = 571303) B571303
theorem B7711361 : Blo 447780 7711361 := bstep (se 2 (by rfl) ⟨2891760, by rfl⟩ : syracuseStep 7711361 = 5783521) B5783521
theorem B1518695 : Blo 447780 1518695 := bstep (se 1 (by rfl) ⟨1139021, by rfl⟩ : syracuseStep 1518695 = 2278043) B2278043
theorem B1521719 : Blo 447780 1521719 := bstep (se 1 (by rfl) ⟨1141289, by rfl⟩ : syracuseStep 1521719 = 2282579) B2282579
theorem B2341223 : Blo 447780 2341223 := bstep (se 1 (by rfl) ⟨1755917, by rfl⟩ : syracuseStep 2341223 = 3511835) B3511835
theorem B2275775 : Blo 447780 2275775 := bstep (se 1 (by rfl) ⟨1706831, by rfl⟩ : syracuseStep 2275775 = 3413663) B3413663
theorem B1522259 : Blo 447780 1522259 := bstep (se 1 (by rfl) ⟨1141694, by rfl⟩ : syracuseStep 1522259 = 2283389) B2283389
theorem B18398123 : Blo 447780 18398123 := bstep (se 1 (by rfl) ⟨13798592, by rfl⟩ : syracuseStep 18398123 = 27597185) B27597185
theorem B1916207 : Blo 447780 1916207 := bstep (se 1 (by rfl) ⟨1437155, by rfl⟩ : syracuseStep 1916207 = 2874311) B2874311
theorem B5129243 : Blo 447780 5129243 := bstep (se 1 (by rfl) ⟨3846932, by rfl⟩ : syracuseStep 5129243 = 7693865) B7693865
theorem B2279177 : Blo 447780 2279177 := bstep (se 2 (by rfl) ⟨854691, by rfl⟩ : syracuseStep 2279177 = 1709383) B1709383
theorem B675695 : Blo 447780 675695 := bstep (se 1 (by rfl) ⟨506771, by rfl⟩ : syracuseStep 675695 = 1013543) B1013543
theorem B15028193 : Blo 447780 15028193 := bstep (se 2 (by rfl) ⟨5635572, by rfl⟩ : syracuseStep 15028193 = 11271145) B11271145
theorem B447951 : Blo 447780 447951 := bstep (se 1 (by rfl) ⟨335963, by rfl⟩ : syracuseStep 447951 = 671927) B671927
theorem B1136713 : Blo 447780 1136713 := bstep (se 2 (by rfl) ⟨426267, by rfl⟩ : syracuseStep 1136713 = 852535) B852535
theorem B449311 : Blo 447780 449311 := bstep (se 1 (by rfl) ⟨336983, by rfl⟩ : syracuseStep 449311 = 673967) B673967
theorem B449691 : Blo 447780 449691 := bstep (se 1 (by rfl) ⟨337268, by rfl⟩ : syracuseStep 449691 = 674537) B674537
theorem B449703 : Blo 447780 449703 := bstep (se 1 (by rfl) ⟨337277, by rfl⟩ : syracuseStep 449703 = 674555) B674555
theorem B59007797 : Blo 447780 59007797 := bstep (se 5 (by rfl) ⟨2765990, by rfl⟩ : syracuseStep 59007797 = 5531981) B5531981
theorem B1011707 : Blo 447780 1011707 := bstep (se 1 (by rfl) ⟨758780, by rfl⟩ : syracuseStep 1011707 = 1517561) B1517561
theorem B1015451 : Blo 447780 1015451 := bstep (se 1 (by rfl) ⟨761588, by rfl⟩ : syracuseStep 1015451 = 1523177) B1523177
theorem B1515617 : Blo 447780 1515617 := bstep (se 2 (by rfl) ⟨568356, by rfl⟩ : syracuseStep 1515617 = 1136713) B1136713
theorem B1517183 : Blo 447780 1517183 := bstep (se 1 (by rfl) ⟨1137887, by rfl⟩ : syracuseStep 1517183 = 2275775) B2275775
theorem B12265415 : Blo 447780 12265415 := bstep (se 1 (by rfl) ⟨9199061, by rfl⟩ : syracuseStep 12265415 = 18398123) B18398123
theorem B568063 : Blo 447780 568063 := bstep (se 1 (by rfl) ⟨426047, by rfl⟩ : syracuseStep 568063 = 852095) B852095
theorem B3419495 : Blo 447780 3419495 := bstep (se 1 (by rfl) ⟨2564621, by rfl⟩ : syracuseStep 3419495 = 5129243) B5129243
theorem B1486237 : Blo 447780 1486237 := bstep (se 3 (by rfl) ⟨278669, by rfl⟩ : syracuseStep 1486237 = 557339) B557339
theorem B1519451 : Blo 447780 1519451 := bstep (se 1 (by rfl) ⟨1139588, by rfl⟩ : syracuseStep 1519451 = 2279177) B2279177
theorem B1293895 : Blo 447780 1293895 := bstep (se 1 (by rfl) ⟨970421, by rfl⟩ : syracuseStep 1293895 = 1940843) B1940843
theorem B39338531 : Blo 447780 39338531 := bstep (se 1 (by rfl) ⟨29503898, by rfl⟩ : syracuseStep 39338531 = 59007797) B59007797
theorem B10928681 : Blo 447780 10928681 := bstep (se 2 (by rfl) ⟨4098255, by rfl⟩ : syracuseStep 10928681 = 8196511) B8196511
theorem B674471 : Blo 447780 674471 := bstep (se 1 (by rfl) ⟨505853, by rfl⟩ : syracuseStep 674471 = 1011707) B1011707
theorem B1560815 : Blo 447780 1560815 := bstep (se 1 (by rfl) ⟨1170611, by rfl⟩ : syracuseStep 1560815 = 2341223) B2341223
theorem B676967 : Blo 447780 676967 := bstep (se 1 (by rfl) ⟨507725, by rfl⟩ : syracuseStep 676967 = 1015451) B1015451
theorem B1923193 : Blo 447780 1923193 := bstep (se 2 (by rfl) ⟨721197, by rfl⟩ : syracuseStep 1923193 = 1442395) B1442395
theorem B450463 : Blo 447780 450463 := bstep (se 1 (by rfl) ⟨337847, by rfl⟩ : syracuseStep 450463 = 675695) B675695
theorem B11691611 : Blo 447780 11691611 := bstep (se 1 (by rfl) ⟨8768708, by rfl⟩ : syracuseStep 11691611 = 17537417) B17537417
theorem B5140907 : Blo 447780 5140907 := bstep (se 1 (by rfl) ⟨3855680, by rfl⟩ : syracuseStep 5140907 = 7711361) B7711361
theorem B1012463 : Blo 447780 1012463 := bstep (se 1 (by rfl) ⟨759347, by rfl⟩ : syracuseStep 1012463 = 1518695) B1518695
theorem B1014479 : Blo 447780 1014479 := bstep (se 1 (by rfl) ⟨760859, by rfl⟩ : syracuseStep 1014479 = 1521719) B1521719
theorem B1014839 : Blo 447780 1014839 := bstep (se 1 (by rfl) ⟨761129, by rfl⟩ : syracuseStep 1014839 = 1522259) B1522259
theorem B1277471 : Blo 447780 1277471 := bstep (se 1 (by rfl) ⟨958103, by rfl⟩ : syracuseStep 1277471 = 1916207) B1916207
theorem B1015649 : Blo 447780 1015649 := bstep (se 2 (by rfl) ⟨380868, by rfl⟩ : syracuseStep 1015649 = 761737) B761737
theorem B40075181 : Blo 447780 40075181 := bstep (se 3 (by rfl) ⟨7514096, by rfl⟩ : syracuseStep 40075181 = 15028193) B15028193
theorem B757417 : Blo 447780 757417 := bstep (se 2 (by rfl) ⟨284031, by rfl⟩ : syracuseStep 757417 = 568063) B568063
theorem B2564257 : Blo 447780 2564257 := bstep (se 2 (by rfl) ⟨961596, by rfl⟩ : syracuseStep 2564257 = 1923193) B1923193
theorem B26716787 : Blo 447780 26716787 := bstep (se 1 (by rfl) ⟨20037590, by rfl⟩ : syracuseStep 26716787 = 40075181) B40075181
theorem B26225687 : Blo 447780 26225687 := bstep (se 1 (by rfl) ⟨19669265, by rfl⟩ : syracuseStep 26225687 = 39338531) B39338531
theorem B7285787 : Blo 447780 7285787 := bstep (se 1 (by rfl) ⟨5464340, by rfl⟩ : syracuseStep 7285787 = 10928681) B10928681
theorem B1981649 : Blo 447780 1981649 := bstep (se 2 (by rfl) ⟨743118, by rfl⟩ : syracuseStep 1981649 = 1486237) B1486237
theorem B8176943 : Blo 447780 8176943 := bstep (se 1 (by rfl) ⟨6132707, by rfl⟩ : syracuseStep 8176943 = 12265415) B12265415
theorem B2279663 : Blo 447780 2279663 := bstep (se 1 (by rfl) ⟨1709747, by rfl⟩ : syracuseStep 2279663 = 3419495) B3419495
theorem B3427271 : Blo 447780 3427271 := bstep (se 1 (by rfl) ⟨2570453, by rfl⟩ : syracuseStep 3427271 = 5140907) B5140907
theorem B674975 : Blo 447780 674975 := bstep (se 1 (by rfl) ⟨506231, by rfl⟩ : syracuseStep 674975 = 1012463) B1012463
theorem B676319 : Blo 447780 676319 := bstep (se 1 (by rfl) ⟨507239, by rfl⟩ : syracuseStep 676319 = 1014479) B1014479
theorem B676559 : Blo 447780 676559 := bstep (se 1 (by rfl) ⟨507419, by rfl⟩ : syracuseStep 676559 = 1014839) B1014839
theorem B1725193 : Blo 447780 1725193 := bstep (se 2 (by rfl) ⟨646947, by rfl⟩ : syracuseStep 1725193 = 1293895) B1293895
theorem B677099 : Blo 447780 677099 := bstep (se 1 (by rfl) ⟨507824, by rfl⟩ : syracuseStep 677099 = 1015649) B1015649
theorem B449647 : Blo 447780 449647 := bstep (se 1 (by rfl) ⟨337235, by rfl⟩ : syracuseStep 449647 = 674471) B674471
theorem B1040543 : Blo 447780 1040543 := bstep (se 1 (by rfl) ⟨780407, by rfl⟩ : syracuseStep 1040543 = 1560815) B1560815
theorem B451311 : Blo 447780 451311 := bstep (se 1 (by rfl) ⟨338483, by rfl⟩ : syracuseStep 451311 = 676967) B676967
theorem B1010411 : Blo 447780 1010411 := bstep (se 1 (by rfl) ⟨757808, by rfl⟩ : syracuseStep 1010411 = 1515617) B1515617
theorem B7794407 : Blo 447780 7794407 := bstep (se 1 (by rfl) ⟨5845805, by rfl⟩ : syracuseStep 7794407 = 11691611) B11691611
theorem B1011455 : Blo 447780 1011455 := bstep (se 1 (by rfl) ⟨758591, by rfl⟩ : syracuseStep 1011455 = 1517183) B1517183
theorem B1012967 : Blo 447780 1012967 := bstep (se 1 (by rfl) ⟨759725, by rfl⟩ : syracuseStep 1012967 = 1519451) B1519451
theorem B851647 : Blo 447780 851647 := bstep (se 1 (by rfl) ⟨638735, by rfl⟩ : syracuseStep 851647 = 1277471) B1277471
theorem B693695 : Blo 447780 693695 := bstep (se 1 (by rfl) ⟨520271, by rfl⟩ : syracuseStep 693695 = 1040543) B1040543
theorem B2300257 : Blo 447780 2300257 := bstep (se 2 (by rfl) ⟨862596, by rfl⟩ : syracuseStep 2300257 = 1725193) B1725193
theorem B4857191 : Blo 447780 4857191 := bstep (se 1 (by rfl) ⟨3642893, by rfl⟩ : syracuseStep 4857191 = 7285787) B7285787
theorem B1321099 : Blo 447780 1321099 := bstep (se 1 (by rfl) ⟨990824, by rfl⟩ : syracuseStep 1321099 = 1981649) B1981649
theorem B3419009 : Blo 447780 3419009 := bstep (se 2 (by rfl) ⟨1282128, by rfl⟩ : syracuseStep 3419009 = 2564257) B2564257
theorem B5451295 : Blo 447780 5451295 := bstep (se 1 (by rfl) ⟨4088471, by rfl⟩ : syracuseStep 5451295 = 8176943) B8176943
theorem B1519775 : Blo 447780 1519775 := bstep (se 1 (by rfl) ⟨1139831, by rfl⟩ : syracuseStep 1519775 = 2279663) B2279663
theorem B17811191 : Blo 447780 17811191 := bstep (se 1 (by rfl) ⟨13358393, by rfl⟩ : syracuseStep 17811191 = 26716787) B26716787
theorem B673607 : Blo 447780 673607 := bstep (se 1 (by rfl) ⟨505205, by rfl⟩ : syracuseStep 673607 = 1010411) B1010411
theorem B17483791 : Blo 447780 17483791 := bstep (se 1 (by rfl) ⟨13112843, by rfl⟩ : syracuseStep 17483791 = 26225687) B26225687
theorem B5196271 : Blo 447780 5196271 := bstep (se 1 (by rfl) ⟨3897203, by rfl⟩ : syracuseStep 5196271 = 7794407) B7794407
theorem B674303 : Blo 447780 674303 := bstep (se 1 (by rfl) ⟨505727, by rfl⟩ : syracuseStep 674303 = 1011455) B1011455
theorem B675311 : Blo 447780 675311 := bstep (se 1 (by rfl) ⟨506483, by rfl⟩ : syracuseStep 675311 = 1012967) B1012967
theorem B1135529 : Blo 447780 1135529 := bstep (se 2 (by rfl) ⟨425823, by rfl⟩ : syracuseStep 1135529 = 851647) B851647
theorem B2284847 : Blo 447780 2284847 := bstep (se 1 (by rfl) ⟨1713635, by rfl⟩ : syracuseStep 2284847 = 3427271) B3427271
theorem B449983 : Blo 447780 449983 := bstep (se 1 (by rfl) ⟨337487, by rfl⟩ : syracuseStep 449983 = 674975) B674975
theorem B450879 : Blo 447780 450879 := bstep (se 1 (by rfl) ⟨338159, by rfl⟩ : syracuseStep 450879 = 676319) B676319
theorem B451039 : Blo 447780 451039 := bstep (se 1 (by rfl) ⟨338279, by rfl⟩ : syracuseStep 451039 = 676559) B676559
theorem B451399 : Blo 447780 451399 := bstep (se 1 (by rfl) ⟨338549, by rfl⟩ : syracuseStep 451399 = 677099) B677099
theorem B1009889 : Blo 447780 1009889 := bstep (se 2 (by rfl) ⟨378708, by rfl⟩ : syracuseStep 1009889 = 757417) B757417
theorem B7045861 : Blo 447780 7045861 := bstep (se 4 (by rfl) ⟨660549, by rfl⟩ : syracuseStep 7045861 = 1321099) B1321099
theorem B757019 : Blo 447780 757019 := bstep (se 1 (by rfl) ⟨567764, by rfl⟩ : syracuseStep 757019 = 1135529) B1135529
theorem B11874127 : Blo 447780 11874127 := bstep (se 1 (by rfl) ⟨8905595, by rfl⟩ : syracuseStep 11874127 = 17811191) B17811191
theorem B12268037 : Blo 447780 12268037 := bstep (se 4 (by rfl) ⟨1150128, by rfl⟩ : syracuseStep 12268037 = 2300257) B2300257
theorem B23311721 : Blo 447780 23311721 := bstep (se 2 (by rfl) ⟨8741895, by rfl⟩ : syracuseStep 23311721 = 17483791) B17483791
theorem B6928361 : Blo 447780 6928361 := bstep (se 2 (by rfl) ⟨2598135, by rfl⟩ : syracuseStep 6928361 = 5196271) B5196271
theorem B1849853 : Blo 447780 1849853 := bstep (se 3 (by rfl) ⟨346847, by rfl⟩ : syracuseStep 1849853 = 693695) B693695
theorem B1523231 : Blo 447780 1523231 := bstep (se 1 (by rfl) ⟨1142423, by rfl⟩ : syracuseStep 1523231 = 2284847) B2284847
theorem B673259 : Blo 447780 673259 := bstep (se 1 (by rfl) ⟨504944, by rfl⟩ : syracuseStep 673259 = 1009889) B1009889
theorem B2279339 : Blo 447780 2279339 := bstep (se 1 (by rfl) ⟨1709504, by rfl⟩ : syracuseStep 2279339 = 3419009) B3419009
theorem B449071 : Blo 447780 449071 := bstep (se 1 (by rfl) ⟨336803, by rfl⟩ : syracuseStep 449071 = 673607) B673607
theorem B449535 : Blo 447780 449535 := bstep (se 1 (by rfl) ⟨337151, by rfl⟩ : syracuseStep 449535 = 674303) B674303
theorem B450207 : Blo 447780 450207 := bstep (se 1 (by rfl) ⟨337655, by rfl⟩ : syracuseStep 450207 = 675311) B675311
theorem B7268393 : Blo 447780 7268393 := bstep (se 2 (by rfl) ⟨2725647, by rfl⟩ : syracuseStep 7268393 = 5451295) B5451295
theorem B3238127 : Blo 447780 3238127 := bstep (se 1 (by rfl) ⟨2428595, by rfl⟩ : syracuseStep 3238127 = 4857191) B4857191
theorem B1013183 : Blo 447780 1013183 := bstep (se 1 (by rfl) ⟨759887, by rfl⟩ : syracuseStep 1013183 = 1519775) B1519775
theorem B15832169 : Blo 447780 15832169 := bstep (se 2 (by rfl) ⟨5937063, by rfl⟩ : syracuseStep 15832169 = 11874127) B11874127
theorem B15541147 : Blo 447780 15541147 := bstep (se 1 (by rfl) ⟨11655860, by rfl⟩ : syracuseStep 15541147 = 23311721) B23311721
theorem B1519559 : Blo 447780 1519559 := bstep (se 1 (by rfl) ⟨1139669, by rfl⟩ : syracuseStep 1519559 = 2279339) B2279339
theorem B32714765 : Blo 447780 32714765 := bstep (se 3 (by rfl) ⟨6134018, by rfl⟩ : syracuseStep 32714765 = 12268037) B12268037
theorem B504679 : Blo 447780 504679 := bstep (se 1 (by rfl) ⟨378509, by rfl⟩ : syracuseStep 504679 = 757019) B757019
theorem B675455 : Blo 447780 675455 := bstep (se 1 (by rfl) ⟨506591, by rfl⟩ : syracuseStep 675455 = 1013183) B1013183
theorem B1233235 : Blo 447780 1233235 := bstep (se 1 (by rfl) ⟨924926, by rfl⟩ : syracuseStep 1233235 = 1849853) B1849853
theorem B9394481 : Blo 447780 9394481 := bstep (se 2 (by rfl) ⟨3522930, by rfl⟩ : syracuseStep 9394481 = 7045861) B7045861
theorem B448839 : Blo 447780 448839 := bstep (se 1 (by rfl) ⟨336629, by rfl⟩ : syracuseStep 448839 = 673259) B673259
theorem B4845595 : Blo 447780 4845595 := bstep (se 1 (by rfl) ⟨3634196, by rfl⟩ : syracuseStep 4845595 = 7268393) B7268393
theorem B2158751 : Blo 447780 2158751 := bstep (se 1 (by rfl) ⟨1619063, by rfl⟩ : syracuseStep 2158751 = 3238127) B3238127
theorem B4618907 : Blo 447780 4618907 := bstep (se 1 (by rfl) ⟨3464180, by rfl⟩ : syracuseStep 4618907 = 6928361) B6928361
theorem B1015487 : Blo 447780 1015487 := bstep (se 1 (by rfl) ⟨761615, by rfl⟩ : syracuseStep 1015487 = 1523231) B1523231
theorem B10554779 : Blo 447780 10554779 := bstep (se 1 (by rfl) ⟨7916084, by rfl⟩ : syracuseStep 10554779 = 15832169) B15832169
theorem B6460793 : Blo 447780 6460793 := bstep (se 2 (by rfl) ⟨2422797, by rfl⟩ : syracuseStep 6460793 = 4845595) B4845595
theorem B1644313 : Blo 447780 1644313 := bstep (se 2 (by rfl) ⟨616617, by rfl⟩ : syracuseStep 1644313 = 1233235) B1233235
theorem B20721529 : Blo 447780 20721529 := bstep (se 2 (by rfl) ⟨7770573, by rfl⟩ : syracuseStep 20721529 = 15541147) B15541147
theorem B25051949 : Blo 447780 25051949 := bstep (se 3 (by rfl) ⟨4697240, by rfl⟩ : syracuseStep 25051949 = 9394481) B9394481
theorem B672905 : Blo 447780 672905 := bstep (se 2 (by rfl) ⟨252339, by rfl⟩ : syracuseStep 672905 = 504679) B504679
theorem B21809843 : Blo 447780 21809843 := bstep (se 1 (by rfl) ⟨16357382, by rfl⟩ : syracuseStep 21809843 = 32714765) B32714765
theorem B676991 : Blo 447780 676991 := bstep (se 1 (by rfl) ⟨507743, by rfl⟩ : syracuseStep 676991 = 1015487) B1015487
theorem B450303 : Blo 447780 450303 := bstep (se 1 (by rfl) ⟨337727, by rfl⟩ : syracuseStep 450303 = 675455) B675455
theorem B1013039 : Blo 447780 1013039 := bstep (se 1 (by rfl) ⟨759779, by rfl⟩ : syracuseStep 1013039 = 1519559) B1519559
theorem B1439167 : Blo 447780 1439167 := bstep (se 1 (by rfl) ⟨1079375, by rfl⟩ : syracuseStep 1439167 = 2158751) B2158751
theorem B3079271 : Blo 447780 3079271 := bstep (se 1 (by rfl) ⟨2309453, by rfl⟩ : syracuseStep 3079271 = 4618907) B4618907
theorem B27628705 : Blo 447780 27628705 := bstep (se 2 (by rfl) ⟨10360764, by rfl⟩ : syracuseStep 27628705 = 20721529) B20721529
theorem B4307195 : Blo 447780 4307195 := bstep (se 1 (by rfl) ⟨3230396, by rfl⟩ : syracuseStep 4307195 = 6460793) B6460793
theorem B1918889 : Blo 447780 1918889 := bstep (se 2 (by rfl) ⟨719583, by rfl⟩ : syracuseStep 1918889 = 1439167) B1439167
theorem B675359 : Blo 447780 675359 := bstep (se 1 (by rfl) ⟨506519, by rfl⟩ : syracuseStep 675359 = 1013039) B1013039
theorem B2052847 : Blo 447780 2052847 := bstep (se 1 (by rfl) ⟨1539635, by rfl⟩ : syracuseStep 2052847 = 3079271) B3079271
theorem B16701299 : Blo 447780 16701299 := bstep (se 1 (by rfl) ⟨12525974, by rfl⟩ : syracuseStep 16701299 = 25051949) B25051949
theorem B448603 : Blo 447780 448603 := bstep (se 1 (by rfl) ⟨336452, by rfl⟩ : syracuseStep 448603 = 672905) B672905
theorem B14539895 : Blo 447780 14539895 := bstep (se 1 (by rfl) ⟨10904921, by rfl⟩ : syracuseStep 14539895 = 21809843) B21809843
theorem B7036519 : Blo 447780 7036519 := bstep (se 1 (by rfl) ⟨5277389, by rfl⟩ : syracuseStep 7036519 = 10554779) B10554779
theorem B451327 : Blo 447780 451327 := bstep (se 1 (by rfl) ⟨338495, by rfl⟩ : syracuseStep 451327 = 676991) B676991
theorem B2192417 : Blo 447780 2192417 := bstep (se 2 (by rfl) ⟨822156, by rfl⟩ : syracuseStep 2192417 = 1644313) B1644313
theorem B1279259 : Blo 447780 1279259 := bstep (se 1 (by rfl) ⟨959444, by rfl⟩ : syracuseStep 1279259 = 1918889) B1918889
theorem B10948517 : Blo 447780 10948517 := bstep (se 4 (by rfl) ⟨1026423, by rfl⟩ : syracuseStep 10948517 = 2052847) B2052847
theorem B36838273 : Blo 447780 36838273 := bstep (se 2 (by rfl) ⟨13814352, by rfl⟩ : syracuseStep 36838273 = 27628705) B27628705
theorem B9382025 : Blo 447780 9382025 := bstep (se 2 (by rfl) ⟨3518259, by rfl⟩ : syracuseStep 9382025 = 7036519) B7036519
theorem B1461611 : Blo 447780 1461611 := bstep (se 1 (by rfl) ⟨1096208, by rfl⟩ : syracuseStep 1461611 = 2192417) B2192417
theorem B2871463 : Blo 447780 2871463 := bstep (se 1 (by rfl) ⟨2153597, by rfl⟩ : syracuseStep 2871463 = 4307195) B4307195
theorem B450239 : Blo 447780 450239 := bstep (se 1 (by rfl) ⟨337679, by rfl⟩ : syracuseStep 450239 = 675359) B675359
theorem B11134199 : Blo 447780 11134199 := bstep (se 1 (by rfl) ⟨8350649, by rfl⟩ : syracuseStep 11134199 = 16701299) B16701299
theorem B9693263 : Blo 447780 9693263 := bstep (se 1 (by rfl) ⟨7269947, by rfl⟩ : syracuseStep 9693263 = 14539895) B14539895
theorem B852839 : Blo 447780 852839 := bstep (se 1 (by rfl) ⟨639629, by rfl⟩ : syracuseStep 852839 = 1279259) B1279259
theorem B6462175 : Blo 447780 6462175 := bstep (se 1 (by rfl) ⟨4846631, by rfl⟩ : syracuseStep 6462175 = 9693263) B9693263
theorem B25018733 : Blo 447780 25018733 := bstep (se 3 (by rfl) ⟨4691012, by rfl⟩ : syracuseStep 25018733 = 9382025) B9382025
theorem B7422799 : Blo 447780 7422799 := bstep (se 1 (by rfl) ⟨5567099, by rfl⟩ : syracuseStep 7422799 = 11134199) B11134199
theorem B7299011 : Blo 447780 7299011 := bstep (se 1 (by rfl) ⟨5474258, by rfl⟩ : syracuseStep 7299011 = 10948517) B10948517
theorem B3828617 : Blo 447780 3828617 := bstep (se 2 (by rfl) ⟨1435731, by rfl⟩ : syracuseStep 3828617 = 2871463) B2871463
theorem B3897629 : Blo 447780 3897629 := bstep (se 3 (by rfl) ⟨730805, by rfl⟩ : syracuseStep 3897629 = 1461611) B1461611
theorem B49117697 : Blo 447780 49117697 := bstep (se 2 (by rfl) ⟨18419136, by rfl⟩ : syracuseStep 49117697 = 36838273) B36838273
theorem B16679155 : Blo 447780 16679155 := bstep (se 1 (by rfl) ⟨12509366, by rfl⟩ : syracuseStep 16679155 = 25018733) B25018733
theorem B9897065 : Blo 447780 9897065 := bstep (se 2 (by rfl) ⟨3711399, by rfl⟩ : syracuseStep 9897065 = 7422799) B7422799
theorem B2598419 : Blo 447780 2598419 := bstep (se 1 (by rfl) ⟨1948814, by rfl⟩ : syracuseStep 2598419 = 3897629) B3897629
theorem B32745131 : Blo 447780 32745131 := bstep (se 1 (by rfl) ⟨24558848, by rfl⟩ : syracuseStep 32745131 = 49117697) B49117697
theorem B568559 : Blo 447780 568559 := bstep (se 1 (by rfl) ⟨426419, by rfl⟩ : syracuseStep 568559 = 852839) B852839
theorem B4866007 : Blo 447780 4866007 := bstep (se 1 (by rfl) ⟨3649505, by rfl⟩ : syracuseStep 4866007 = 7299011) B7299011
theorem B2552411 : Blo 447780 2552411 := bstep (se 1 (by rfl) ⟨1914308, by rfl⟩ : syracuseStep 2552411 = 3828617) B3828617
theorem B8616233 : Blo 447780 8616233 := bstep (se 2 (by rfl) ⟨3231087, by rfl⟩ : syracuseStep 8616233 = 6462175) B6462175
theorem B21830087 : Blo 447780 21830087 := bstep (se 1 (by rfl) ⟨16372565, by rfl⟩ : syracuseStep 21830087 = 32745131) B32745131
theorem B1516157 : Blo 447780 1516157 := bstep (se 3 (by rfl) ⟨284279, by rfl⟩ : syracuseStep 1516157 = 568559) B568559
theorem B5744155 : Blo 447780 5744155 := bstep (se 1 (by rfl) ⟨4308116, by rfl⟩ : syracuseStep 5744155 = 8616233) B8616233
theorem B6598043 : Blo 447780 6598043 := bstep (se 1 (by rfl) ⟨4948532, by rfl⟩ : syracuseStep 6598043 = 9897065) B9897065
theorem B22238873 : Blo 447780 22238873 := bstep (se 2 (by rfl) ⟨8339577, by rfl⟩ : syracuseStep 22238873 = 16679155) B16679155
theorem B1732279 : Blo 447780 1732279 := bstep (se 1 (by rfl) ⟨1299209, by rfl⟩ : syracuseStep 1732279 = 2598419) B2598419
theorem B1701607 : Blo 447780 1701607 := bstep (se 1 (by rfl) ⟨1276205, by rfl⟩ : syracuseStep 1701607 = 2552411) B2552411
theorem B6488009 : Blo 447780 6488009 := bstep (se 2 (by rfl) ⟨2433003, by rfl⟩ : syracuseStep 6488009 = 4866007) B4866007
theorem B14553391 : Blo 447780 14553391 := bstep (se 1 (by rfl) ⟨10915043, by rfl⟩ : syracuseStep 14553391 = 21830087) B21830087
theorem B4398695 : Blo 447780 4398695 := bstep (se 1 (by rfl) ⟨3299021, by rfl⟩ : syracuseStep 4398695 = 6598043) B6598043
theorem B2268809 : Blo 447780 2268809 := bstep (se 2 (by rfl) ⟨850803, by rfl⟩ : syracuseStep 2268809 = 1701607) B1701607
theorem B14825915 : Blo 447780 14825915 := bstep (se 1 (by rfl) ⟨11119436, by rfl⟩ : syracuseStep 14825915 = 22238873) B22238873
theorem B2309705 : Blo 447780 2309705 := bstep (se 2 (by rfl) ⟨866139, by rfl⟩ : syracuseStep 2309705 = 1732279) B1732279
theorem B7658873 : Blo 447780 7658873 := bstep (se 2 (by rfl) ⟨2872077, by rfl⟩ : syracuseStep 7658873 = 5744155) B5744155
theorem B1010771 : Blo 447780 1010771 := bstep (se 1 (by rfl) ⟨758078, by rfl⟩ : syracuseStep 1010771 = 1516157) B1516157
theorem B4325339 : Blo 447780 4325339 := bstep (se 1 (by rfl) ⟨3244004, by rfl⟩ : syracuseStep 4325339 = 6488009) B6488009
theorem B1512539 : Blo 447780 1512539 := bstep (se 1 (by rfl) ⟨1134404, by rfl⟩ : syracuseStep 1512539 = 2268809) B2268809
theorem B19404521 : Blo 447780 19404521 := bstep (se 2 (by rfl) ⟨7276695, by rfl⟩ : syracuseStep 19404521 = 14553391) B14553391
theorem B2932463 : Blo 447780 2932463 := bstep (se 1 (by rfl) ⟨2199347, by rfl⟩ : syracuseStep 2932463 = 4398695) B4398695
theorem B673847 : Blo 447780 673847 := bstep (se 1 (by rfl) ⟨505385, by rfl⟩ : syracuseStep 673847 = 1010771) B1010771
theorem B9883943 : Blo 447780 9883943 := bstep (se 1 (by rfl) ⟨7412957, by rfl⟩ : syracuseStep 9883943 = 14825915) B14825915
theorem B5105915 : Blo 447780 5105915 := bstep (se 1 (by rfl) ⟨3829436, by rfl⟩ : syracuseStep 5105915 = 7658873) B7658873
theorem B1539803 : Blo 447780 1539803 := bstep (se 1 (by rfl) ⟨1154852, by rfl⟩ : syracuseStep 1539803 = 2309705) B2309705
theorem B11534237 : Blo 447780 11534237 := bstep (se 3 (by rfl) ⟨2162669, by rfl⟩ : syracuseStep 11534237 = 4325339) B4325339
theorem B6589295 : Blo 447780 6589295 := bstep (se 1 (by rfl) ⟨4941971, by rfl⟩ : syracuseStep 6589295 = 9883943) B9883943
theorem B1026535 : Blo 447780 1026535 := bstep (se 1 (by rfl) ⟨769901, by rfl⟩ : syracuseStep 1026535 = 1539803) B1539803
theorem B7819901 : Blo 447780 7819901 := bstep (se 3 (by rfl) ⟨1466231, by rfl⟩ : syracuseStep 7819901 = 2932463) B2932463
theorem B7689491 : Blo 447780 7689491 := bstep (se 1 (by rfl) ⟨5767118, by rfl⟩ : syracuseStep 7689491 = 11534237) B11534237
theorem B449231 : Blo 447780 449231 := bstep (se 1 (by rfl) ⟨336923, by rfl⟩ : syracuseStep 449231 = 673847) B673847
theorem B1008359 : Blo 447780 1008359 := bstep (se 1 (by rfl) ⟨756269, by rfl⟩ : syracuseStep 1008359 = 1512539) B1512539
theorem B12936347 : Blo 447780 12936347 := bstep (se 1 (by rfl) ⟨9702260, by rfl⟩ : syracuseStep 12936347 = 19404521) B19404521
theorem B3403943 : Blo 447780 3403943 := bstep (se 1 (by rfl) ⟨2552957, by rfl⟩ : syracuseStep 3403943 = 5105915) B5105915
theorem B4392863 : Blo 447780 4392863 := bstep (se 1 (by rfl) ⟨3294647, by rfl⟩ : syracuseStep 4392863 = 6589295) B6589295
theorem B5213267 : Blo 447780 5213267 := bstep (se 1 (by rfl) ⟨3909950, by rfl⟩ : syracuseStep 5213267 = 7819901) B7819901
theorem B8624231 : Blo 447780 8624231 := bstep (se 1 (by rfl) ⟨6468173, by rfl⟩ : syracuseStep 8624231 = 12936347) B12936347
theorem B2269295 : Blo 447780 2269295 := bstep (se 1 (by rfl) ⟨1701971, by rfl⟩ : syracuseStep 2269295 = 3403943) B3403943
theorem B5126327 : Blo 447780 5126327 := bstep (se 1 (by rfl) ⟨3844745, by rfl⟩ : syracuseStep 5126327 = 7689491) B7689491
theorem B672239 : Blo 447780 672239 := bstep (se 1 (by rfl) ⟨504179, by rfl⟩ : syracuseStep 672239 = 1008359) B1008359
theorem B1368713 : Blo 447780 1368713 := bstep (se 2 (by rfl) ⟨513267, by rfl⟩ : syracuseStep 1368713 = 1026535) B1026535
theorem B3475511 : Blo 447780 3475511 := bstep (se 1 (by rfl) ⟨2606633, by rfl⟩ : syracuseStep 3475511 = 5213267) B5213267
theorem B1512863 : Blo 447780 1512863 := bstep (se 1 (by rfl) ⟨1134647, by rfl⟩ : syracuseStep 1512863 = 2269295) B2269295
theorem B3417551 : Blo 447780 3417551 := bstep (se 1 (by rfl) ⟨2563163, by rfl⟩ : syracuseStep 3417551 = 5126327) B5126327
theorem B2928575 : Blo 447780 2928575 := bstep (se 1 (by rfl) ⟨2196431, by rfl⟩ : syracuseStep 2928575 = 4392863) B4392863
theorem B5749487 : Blo 447780 5749487 := bstep (se 1 (by rfl) ⟨4312115, by rfl⟩ : syracuseStep 5749487 = 8624231) B8624231
theorem B448159 : Blo 447780 448159 := bstep (se 1 (by rfl) ⟨336119, by rfl⟩ : syracuseStep 448159 = 672239) B672239
theorem B912475 : Blo 447780 912475 := bstep (se 1 (by rfl) ⟨684356, by rfl⟩ : syracuseStep 912475 = 1368713) B1368713
theorem B1216633 : Blo 447780 1216633 := bstep (se 2 (by rfl) ⟨456237, by rfl⟩ : syracuseStep 1216633 = 912475) B912475
theorem B2278367 : Blo 447780 2278367 := bstep (se 1 (by rfl) ⟨1708775, by rfl⟩ : syracuseStep 2278367 = 3417551) B3417551
theorem B1952383 : Blo 447780 1952383 := bstep (se 1 (by rfl) ⟨1464287, by rfl⟩ : syracuseStep 1952383 = 2928575) B2928575
theorem B2317007 : Blo 447780 2317007 := bstep (se 1 (by rfl) ⟨1737755, by rfl⟩ : syracuseStep 2317007 = 3475511) B3475511
theorem B1008575 : Blo 447780 1008575 := bstep (se 1 (by rfl) ⟨756431, by rfl⟩ : syracuseStep 1008575 = 1512863) B1512863
theorem B3832991 : Blo 447780 3832991 := bstep (se 1 (by rfl) ⟨2874743, by rfl⟩ : syracuseStep 3832991 = 5749487) B5749487
theorem B1518911 : Blo 447780 1518911 := bstep (se 1 (by rfl) ⟨1139183, by rfl⟩ : syracuseStep 1518911 = 2278367) B2278367
theorem B2603177 : Blo 447780 2603177 := bstep (se 2 (by rfl) ⟨976191, by rfl⟩ : syracuseStep 2603177 = 1952383) B1952383
theorem B1622177 : Blo 447780 1622177 := bstep (se 2 (by rfl) ⟨608316, by rfl⟩ : syracuseStep 1622177 = 1216633) B1216633
theorem B672383 : Blo 447780 672383 := bstep (se 1 (by rfl) ⟨504287, by rfl⟩ : syracuseStep 672383 = 1008575) B1008575
theorem B6178685 : Blo 447780 6178685 := bstep (se 3 (by rfl) ⟨1158503, by rfl⟩ : syracuseStep 6178685 = 2317007) B2317007
theorem B2555327 : Blo 447780 2555327 := bstep (se 1 (by rfl) ⟨1916495, by rfl⟩ : syracuseStep 2555327 = 3832991) B3832991
theorem B1081451 : Blo 447780 1081451 := bstep (se 1 (by rfl) ⟨811088, by rfl⟩ : syracuseStep 1081451 = 1622177) B1622177
theorem B448255 : Blo 447780 448255 := bstep (se 1 (by rfl) ⟨336191, by rfl⟩ : syracuseStep 448255 = 672383) B672383
theorem B16476493 : Blo 447780 16476493 := bstep (se 3 (by rfl) ⟨3089342, by rfl⟩ : syracuseStep 16476493 = 6178685) B6178685
theorem B1012607 : Blo 447780 1012607 := bstep (se 1 (by rfl) ⟨759455, by rfl⟩ : syracuseStep 1012607 = 1518911) B1518911
theorem B1735451 : Blo 447780 1735451 := bstep (se 1 (by rfl) ⟨1301588, by rfl⟩ : syracuseStep 1735451 = 2603177) B2603177
theorem B1703551 : Blo 447780 1703551 := bstep (se 1 (by rfl) ⟨1277663, by rfl⟩ : syracuseStep 1703551 = 2555327) B2555327
theorem B2883869 : Blo 447780 2883869 := bstep (se 3 (by rfl) ⟨540725, by rfl⟩ : syracuseStep 2883869 = 1081451) B1081451
theorem B1156967 : Blo 447780 1156967 := bstep (se 1 (by rfl) ⟨867725, by rfl⟩ : syracuseStep 1156967 = 1735451) B1735451
theorem B2271401 : Blo 447780 2271401 := bstep (se 2 (by rfl) ⟨851775, by rfl⟩ : syracuseStep 2271401 = 1703551) B1703551
theorem B21968657 : Blo 447780 21968657 := bstep (se 2 (by rfl) ⟨8238246, by rfl⟩ : syracuseStep 21968657 = 16476493) B16476493
theorem B675071 : Blo 447780 675071 := bstep (se 1 (by rfl) ⟨506303, by rfl⟩ : syracuseStep 675071 = 1012607) B1012607
theorem B1514267 : Blo 447780 1514267 := bstep (se 1 (by rfl) ⟨1135700, by rfl⟩ : syracuseStep 1514267 = 2271401) B2271401
theorem B771311 : Blo 447780 771311 := bstep (se 1 (by rfl) ⟨578483, by rfl⟩ : syracuseStep 771311 = 1156967) B1156967
theorem B1922579 : Blo 447780 1922579 := bstep (se 1 (by rfl) ⟨1441934, by rfl⟩ : syracuseStep 1922579 = 2883869) B2883869
theorem B450047 : Blo 447780 450047 := bstep (se 1 (by rfl) ⟨337535, by rfl⟩ : syracuseStep 450047 = 675071) B675071
theorem B14645771 : Blo 447780 14645771 := bstep (se 1 (by rfl) ⟨10984328, by rfl⟩ : syracuseStep 14645771 = 21968657) B21968657
theorem B1281719 : Blo 447780 1281719 := bstep (se 1 (by rfl) ⟨961289, by rfl⟩ : syracuseStep 1281719 = 1922579) B1922579
theorem B514207 : Blo 447780 514207 := bstep (se 1 (by rfl) ⟨385655, by rfl⟩ : syracuseStep 514207 = 771311) B771311
theorem B1009511 : Blo 447780 1009511 := bstep (se 1 (by rfl) ⟨757133, by rfl⟩ : syracuseStep 1009511 = 1514267) B1514267
theorem B9763847 : Blo 447780 9763847 := bstep (se 1 (by rfl) ⟨7322885, by rfl⟩ : syracuseStep 9763847 = 14645771) B14645771
theorem B854479 : Blo 447780 854479 := bstep (se 1 (by rfl) ⟨640859, by rfl⟩ : syracuseStep 854479 = 1281719) B1281719
theorem B673007 : Blo 447780 673007 := bstep (se 1 (by rfl) ⟨504755, by rfl⟩ : syracuseStep 673007 = 1009511) B1009511
theorem B6509231 : Blo 447780 6509231 := bstep (se 1 (by rfl) ⟨4881923, by rfl⟩ : syracuseStep 6509231 = 9763847) B9763847
theorem B2742437 : Blo 447780 2742437 := bstep (se 4 (by rfl) ⟨257103, by rfl⟩ : syracuseStep 2742437 = 514207) B514207
theorem B4339487 : Blo 447780 4339487 := bstep (se 1 (by rfl) ⟨3254615, by rfl⟩ : syracuseStep 4339487 = 6509231) B6509231
theorem B448671 : Blo 447780 448671 := bstep (se 1 (by rfl) ⟨336503, by rfl⟩ : syracuseStep 448671 = 673007) B673007
theorem B1139305 : Blo 447780 1139305 := bstep (se 2 (by rfl) ⟨427239, by rfl⟩ : syracuseStep 1139305 = 854479) B854479
theorem B1828291 : Blo 447780 1828291 := bstep (se 1 (by rfl) ⟨1371218, by rfl⟩ : syracuseStep 1828291 = 2742437) B2742437
theorem B2892991 : Blo 447780 2892991 := bstep (se 1 (by rfl) ⟨2169743, by rfl⟩ : syracuseStep 2892991 = 4339487) B4339487
theorem B1519073 : Blo 447780 1519073 := bstep (se 2 (by rfl) ⟨569652, by rfl⟩ : syracuseStep 1519073 = 1139305) B1139305
theorem B2437721 : Blo 447780 2437721 := bstep (se 2 (by rfl) ⟨914145, by rfl⟩ : syracuseStep 2437721 = 1828291) B1828291
theorem B1625147 : Blo 447780 1625147 := bstep (se 1 (by rfl) ⟨1218860, by rfl⟩ : syracuseStep 1625147 = 2437721) B2437721
theorem B3857321 : Blo 447780 3857321 := bstep (se 2 (by rfl) ⟨1446495, by rfl⟩ : syracuseStep 3857321 = 2892991) B2892991
theorem B1012715 : Blo 447780 1012715 := bstep (se 1 (by rfl) ⟨759536, by rfl⟩ : syracuseStep 1012715 = 1519073) B1519073
theorem B1083431 : Blo 447780 1083431 := bstep (se 1 (by rfl) ⟨812573, by rfl⟩ : syracuseStep 1083431 = 1625147) B1625147
theorem B2571547 : Blo 447780 2571547 := bstep (se 1 (by rfl) ⟨1928660, by rfl⟩ : syracuseStep 2571547 = 3857321) B3857321
theorem B675143 : Blo 447780 675143 := bstep (se 1 (by rfl) ⟨506357, by rfl⟩ : syracuseStep 675143 = 1012715) B1012715
theorem B722287 : Blo 447780 722287 := bstep (se 1 (by rfl) ⟨541715, by rfl⟩ : syracuseStep 722287 = 1083431) B1083431
theorem B3428729 : Blo 447780 3428729 := bstep (se 2 (by rfl) ⟨1285773, by rfl⟩ : syracuseStep 3428729 = 2571547) B2571547
theorem B450095 : Blo 447780 450095 := bstep (se 1 (by rfl) ⟨337571, by rfl⟩ : syracuseStep 450095 = 675143) B675143
theorem B3852197 : Blo 447780 3852197 := bstep (se 4 (by rfl) ⟨361143, by rfl⟩ : syracuseStep 3852197 = 722287) B722287
theorem B2285819 : Blo 447780 2285819 := bstep (se 1 (by rfl) ⟨1714364, by rfl⟩ : syracuseStep 2285819 = 3428729) B3428729
theorem B2568131 : Blo 447780 2568131 := bstep (se 1 (by rfl) ⟨1926098, by rfl⟩ : syracuseStep 2568131 = 3852197) B3852197
theorem B1523879 : Blo 447780 1523879 := bstep (se 1 (by rfl) ⟨1142909, by rfl⟩ : syracuseStep 1523879 = 2285819) B2285819
theorem B1015919 : Blo 447780 1015919 := bstep (se 1 (by rfl) ⟨761939, by rfl⟩ : syracuseStep 1015919 = 1523879) B1523879
theorem B1712087 : Blo 447780 1712087 := bstep (se 1 (by rfl) ⟨1284065, by rfl⟩ : syracuseStep 1712087 = 2568131) B2568131
theorem B677279 : Blo 447780 677279 := bstep (se 1 (by rfl) ⟨507959, by rfl⟩ : syracuseStep 677279 = 1015919) B1015919
theorem B1141391 : Blo 447780 1141391 := bstep (se 1 (by rfl) ⟨856043, by rfl⟩ : syracuseStep 1141391 = 1712087) B1712087
theorem B760927 : Blo 447780 760927 := bstep (se 1 (by rfl) ⟨570695, by rfl⟩ : syracuseStep 760927 = 1141391) B1141391
theorem B451519 : Blo 447780 451519 := bstep (se 1 (by rfl) ⟨338639, by rfl⟩ : syracuseStep 451519 = 677279) B677279
theorem B1014569 : Blo 447780 1014569 := bstep (se 2 (by rfl) ⟨380463, by rfl⟩ : syracuseStep 1014569 = 760927) B760927
theorem B676379 : Blo 447780 676379 := bstep (se 1 (by rfl) ⟨507284, by rfl⟩ : syracuseStep 676379 = 1014569) B1014569
theorem B450919 : Blo 447780 450919 := bstep (se 1 (by rfl) ⟨338189, by rfl⟩ : syracuseStep 450919 = 676379) B676379

theorem C0 (j : ℕ) (h1 : 111945 ≤ j) (h2 : j ≤ 112644) : Blo 447780 (4 * j + 3) := by
  interval_cases j
  · exact B447783
  · exact B447787
  · exact B447791
  · exact B447795
  · exact B447799
  · exact B447803
  · exact B447807
  · exact B447811
  · exact B447815
  · exact B447819
  · exact B447823
  · exact B447827
  · exact B447831
  · exact B447835
  · exact B447839
  · exact B447843
  · exact B447847
  · exact B447851
  · exact B447855
  · exact B447859
  · exact B447863
  · exact B447867
  · exact B447871
  · exact B447875
  · exact B447879
  · exact B447883
  · exact B447887
  · exact B447891
  · exact B447895
  · exact B447899
  · exact B447903
  · exact B447907
  · exact B447911
  · exact B447915
  · exact B447919
  · exact B447923
  · exact B447927
  · exact B447931
  · exact B447935
  · exact B447939
  · exact B447943
  · exact B447947
  · exact B447951
  · exact B447955
  · exact B447959
  · exact B447963
  · exact B447967
  · exact B447971
  · exact B447975
  · exact B447979
  · exact B447983
  · exact B447987
  · exact B447991
  · exact B447995
  · exact B447999
  · exact B448003
  · exact B448007
  · exact B448011
  · exact B448015
  · exact B448019
  · exact B448023
  · exact B448027
  · exact B448031
  · exact B448035
  · exact B448039
  · exact B448043
  · exact B448047
  · exact B448051
  · exact B448055
  · exact B448059
  · exact B448063
  · exact B448067
  · exact B448071
  · exact B448075
  · exact B448079
  · exact B448083
  · exact B448087
  · exact B448091
  · exact B448095
  · exact B448099
  · exact B448103
  · exact B448107
  · exact B448111
  · exact B448115
  · exact B448119
  · exact B448123
  · exact B448127
  · exact B448131
  · exact B448135
  · exact B448139
  · exact B448143
  · exact B448147
  · exact B448151
  · exact B448155
  · exact B448159
  · exact B448163
  · exact B448167
  · exact B448171
  · exact B448175
  · exact B448179
  · exact B448183
  · exact B448187
  · exact B448191
  · exact B448195
  · exact B448199
  · exact B448203
  · exact B448207
  · exact B448211
  · exact B448215
  · exact B448219
  · exact B448223
  · exact B448227
  · exact B448231
  · exact B448235
  · exact B448239
  · exact B448243
  · exact B448247
  · exact B448251
  · exact B448255
  · exact B448259
  · exact B448263
  · exact B448267
  · exact B448271
  · exact B448275
  · exact B448279
  · exact B448283
  · exact B448287
  · exact B448291
  · exact B448295
  · exact B448299
  · exact B448303
  · exact B448307
  · exact B448311
  · exact B448315
  · exact B448319
  · exact B448323
  · exact B448327
  · exact B448331
  · exact B448335
  · exact B448339
  · exact B448343
  · exact B448347
  · exact B448351
  · exact B448355
  · exact B448359
  · exact B448363
  · exact B448367
  · exact B448371
  · exact B448375
  · exact B448379
  · exact B448383
  · exact B448387
  · exact B448391
  · exact B448395
  · exact B448399
  · exact B448403
  · exact B448407
  · exact B448411
  · exact B448415
  · exact B448419
  · exact B448423
  · exact B448427
  · exact B448431
  · exact B448435
  · exact B448439
  · exact B448443
  · exact B448447
  · exact B448451
  · exact B448455
  · exact B448459
  · exact B448463
  · exact B448467
  · exact B448471
  · exact B448475
  · exact B448479
  · exact B448483
  · exact B448487
  · exact B448491
  · exact B448495
  · exact B448499
  · exact B448503
  · exact B448507
  · exact B448511
  · exact B448515
  · exact B448519
  · exact B448523
  · exact B448527
  · exact B448531
  · exact B448535
  · exact B448539
  · exact B448543
  · exact B448547
  · exact B448551
  · exact B448555
  · exact B448559
  · exact B448563
  · exact B448567
  · exact B448571
  · exact B448575
  · exact B448579
  · exact B448583
  · exact B448587
  · exact B448591
  · exact B448595
  · exact B448599
  · exact B448603
  · exact B448607
  · exact B448611
  · exact B448615
  · exact B448619
  · exact B448623
  · exact B448627
  · exact B448631
  · exact B448635
  · exact B448639
  · exact B448643
  · exact B448647
  · exact B448651
  · exact B448655
  · exact B448659
  · exact B448663
  · exact B448667
  · exact B448671
  · exact B448675
  · exact B448679
  · exact B448683
  · exact B448687
  · exact B448691
  · exact B448695
  · exact B448699
  · exact B448703
  · exact B448707
  · exact B448711
  · exact B448715
  · exact B448719
  · exact B448723
  · exact B448727
  · exact B448731
  · exact B448735
  · exact B448739
  · exact B448743
  · exact B448747
  · exact B448751
  · exact B448755
  · exact B448759
  · exact B448763
  · exact B448767
  · exact B448771
  · exact B448775
  · exact B448779
  · exact B448783
  · exact B448787
  · exact B448791
  · exact B448795
  · exact B448799
  · exact B448803
  · exact B448807
  · exact B448811
  · exact B448815
  · exact B448819
  · exact B448823
  · exact B448827
  · exact B448831
  · exact B448835
  · exact B448839
  · exact B448843
  · exact B448847
  · exact B448851
  · exact B448855
  · exact B448859
  · exact B448863
  · exact B448867
  · exact B448871
  · exact B448875
  · exact B448879
  · exact B448883
  · exact B448887
  · exact B448891
  · exact B448895
  · exact B448899
  · exact B448903
  · exact B448907
  · exact B448911
  · exact B448915
  · exact B448919
  · exact B448923
  · exact B448927
  · exact B448931
  · exact B448935
  · exact B448939
  · exact B448943
  · exact B448947
  · exact B448951
  · exact B448955
  · exact B448959
  · exact B448963
  · exact B448967
  · exact B448971
  · exact B448975
  · exact B448979
  · exact B448983
  · exact B448987
  · exact B448991
  · exact B448995
  · exact B448999
  · exact B449003
  · exact B449007
  · exact B449011
  · exact B449015
  · exact B449019
  · exact B449023
  · exact B449027
  · exact B449031
  · exact B449035
  · exact B449039
  · exact B449043
  · exact B449047
  · exact B449051
  · exact B449055
  · exact B449059
  · exact B449063
  · exact B449067
  · exact B449071
  · exact B449075
  · exact B449079
  · exact B449083
  · exact B449087
  · exact B449091
  · exact B449095
  · exact B449099
  · exact B449103
  · exact B449107
  · exact B449111
  · exact B449115
  · exact B449119
  · exact B449123
  · exact B449127
  · exact B449131
  · exact B449135
  · exact B449139
  · exact B449143
  · exact B449147
  · exact B449151
  · exact B449155
  · exact B449159
  · exact B449163
  · exact B449167
  · exact B449171
  · exact B449175
  · exact B449179
  · exact B449183
  · exact B449187
  · exact B449191
  · exact B449195
  · exact B449199
  · exact B449203
  · exact B449207
  · exact B449211
  · exact B449215
  · exact B449219
  · exact B449223
  · exact B449227
  · exact B449231
  · exact B449235
  · exact B449239
  · exact B449243
  · exact B449247
  · exact B449251
  · exact B449255
  · exact B449259
  · exact B449263
  · exact B449267
  · exact B449271
  · exact B449275
  · exact B449279
  · exact B449283
  · exact B449287
  · exact B449291
  · exact B449295
  · exact B449299
  · exact B449303
  · exact B449307
  · exact B449311
  · exact B449315
  · exact B449319
  · exact B449323
  · exact B449327
  · exact B449331
  · exact B449335
  · exact B449339
  · exact B449343
  · exact B449347
  · exact B449351
  · exact B449355
  · exact B449359
  · exact B449363
  · exact B449367
  · exact B449371
  · exact B449375
  · exact B449379
  · exact B449383
  · exact B449387
  · exact B449391
  · exact B449395
  · exact B449399
  · exact B449403
  · exact B449407
  · exact B449411
  · exact B449415
  · exact B449419
  · exact B449423
  · exact B449427
  · exact B449431
  · exact B449435
  · exact B449439
  · exact B449443
  · exact B449447
  · exact B449451
  · exact B449455
  · exact B449459
  · exact B449463
  · exact B449467
  · exact B449471
  · exact B449475
  · exact B449479
  · exact B449483
  · exact B449487
  · exact B449491
  · exact B449495
  · exact B449499
  · exact B449503
  · exact B449507
  · exact B449511
  · exact B449515
  · exact B449519
  · exact B449523
  · exact B449527
  · exact B449531
  · exact B449535
  · exact B449539
  · exact B449543
  · exact B449547
  · exact B449551
  · exact B449555
  · exact B449559
  · exact B449563
  · exact B449567
  · exact B449571
  · exact B449575
  · exact B449579
  · exact B449583
  · exact B449587
  · exact B449591
  · exact B449595
  · exact B449599
  · exact B449603
  · exact B449607
  · exact B449611
  · exact B449615
  · exact B449619
  · exact B449623
  · exact B449627
  · exact B449631
  · exact B449635
  · exact B449639
  · exact B449643
  · exact B449647
  · exact B449651
  · exact B449655
  · exact B449659
  · exact B449663
  · exact B449667
  · exact B449671
  · exact B449675
  · exact B449679
  · exact B449683
  · exact B449687
  · exact B449691
  · exact B449695
  · exact B449699
  · exact B449703
  · exact B449707
  · exact B449711
  · exact B449715
  · exact B449719
  · exact B449723
  · exact B449727
  · exact B449731
  · exact B449735
  · exact B449739
  · exact B449743
  · exact B449747
  · exact B449751
  · exact B449755
  · exact B449759
  · exact B449763
  · exact B449767
  · exact B449771
  · exact B449775
  · exact B449779
  · exact B449783
  · exact B449787
  · exact B449791
  · exact B449795
  · exact B449799
  · exact B449803
  · exact B449807
  · exact B449811
  · exact B449815
  · exact B449819
  · exact B449823
  · exact B449827
  · exact B449831
  · exact B449835
  · exact B449839
  · exact B449843
  · exact B449847
  · exact B449851
  · exact B449855
  · exact B449859
  · exact B449863
  · exact B449867
  · exact B449871
  · exact B449875
  · exact B449879
  · exact B449883
  · exact B449887
  · exact B449891
  · exact B449895
  · exact B449899
  · exact B449903
  · exact B449907
  · exact B449911
  · exact B449915
  · exact B449919
  · exact B449923
  · exact B449927
  · exact B449931
  · exact B449935
  · exact B449939
  · exact B449943
  · exact B449947
  · exact B449951
  · exact B449955
  · exact B449959
  · exact B449963
  · exact B449967
  · exact B449971
  · exact B449975
  · exact B449979
  · exact B449983
  · exact B449987
  · exact B449991
  · exact B449995
  · exact B449999
  · exact B450003
  · exact B450007
  · exact B450011
  · exact B450015
  · exact B450019
  · exact B450023
  · exact B450027
  · exact B450031
  · exact B450035
  · exact B450039
  · exact B450043
  · exact B450047
  · exact B450051
  · exact B450055
  · exact B450059
  · exact B450063
  · exact B450067
  · exact B450071
  · exact B450075
  · exact B450079
  · exact B450083
  · exact B450087
  · exact B450091
  · exact B450095
  · exact B450099
  · exact B450103
  · exact B450107
  · exact B450111
  · exact B450115
  · exact B450119
  · exact B450123
  · exact B450127
  · exact B450131
  · exact B450135
  · exact B450139
  · exact B450143
  · exact B450147
  · exact B450151
  · exact B450155
  · exact B450159
  · exact B450163
  · exact B450167
  · exact B450171
  · exact B450175
  · exact B450179
  · exact B450183
  · exact B450187
  · exact B450191
  · exact B450195
  · exact B450199
  · exact B450203
  · exact B450207
  · exact B450211
  · exact B450215
  · exact B450219
  · exact B450223
  · exact B450227
  · exact B450231
  · exact B450235
  · exact B450239
  · exact B450243
  · exact B450247
  · exact B450251
  · exact B450255
  · exact B450259
  · exact B450263
  · exact B450267
  · exact B450271
  · exact B450275
  · exact B450279
  · exact B450283
  · exact B450287
  · exact B450291
  · exact B450295
  · exact B450299
  · exact B450303
  · exact B450307
  · exact B450311
  · exact B450315
  · exact B450319
  · exact B450323
  · exact B450327
  · exact B450331
  · exact B450335
  · exact B450339
  · exact B450343
  · exact B450347
  · exact B450351
  · exact B450355
  · exact B450359
  · exact B450363
  · exact B450367
  · exact B450371
  · exact B450375
  · exact B450379
  · exact B450383
  · exact B450387
  · exact B450391
  · exact B450395
  · exact B450399
  · exact B450403
  · exact B450407
  · exact B450411
  · exact B450415
  · exact B450419
  · exact B450423
  · exact B450427
  · exact B450431
  · exact B450435
  · exact B450439
  · exact B450443
  · exact B450447
  · exact B450451
  · exact B450455
  · exact B450459
  · exact B450463
  · exact B450467
  · exact B450471
  · exact B450475
  · exact B450479
  · exact B450483
  · exact B450487
  · exact B450491
  · exact B450495
  · exact B450499
  · exact B450503
  · exact B450507
  · exact B450511
  · exact B450515
  · exact B450519
  · exact B450523
  · exact B450527
  · exact B450531
  · exact B450535
  · exact B450539
  · exact B450543
  · exact B450547
  · exact B450551
  · exact B450555
  · exact B450559
  · exact B450563
  · exact B450567
  · exact B450571
  · exact B450575
  · exact B450579

theorem C1 (j : ℕ) (h1 : 112645 ≤ j) (h2 : j ≤ 112944) : Blo 447780 (4 * j + 3) := by
  interval_cases j
  · exact B450583
  · exact B450587
  · exact B450591
  · exact B450595
  · exact B450599
  · exact B450603
  · exact B450607
  · exact B450611
  · exact B450615
  · exact B450619
  · exact B450623
  · exact B450627
  · exact B450631
  · exact B450635
  · exact B450639
  · exact B450643
  · exact B450647
  · exact B450651
  · exact B450655
  · exact B450659
  · exact B450663
  · exact B450667
  · exact B450671
  · exact B450675
  · exact B450679
  · exact B450683
  · exact B450687
  · exact B450691
  · exact B450695
  · exact B450699
  · exact B450703
  · exact B450707
  · exact B450711
  · exact B450715
  · exact B450719
  · exact B450723
  · exact B450727
  · exact B450731
  · exact B450735
  · exact B450739
  · exact B450743
  · exact B450747
  · exact B450751
  · exact B450755
  · exact B450759
  · exact B450763
  · exact B450767
  · exact B450771
  · exact B450775
  · exact B450779
  · exact B450783
  · exact B450787
  · exact B450791
  · exact B450795
  · exact B450799
  · exact B450803
  · exact B450807
  · exact B450811
  · exact B450815
  · exact B450819
  · exact B450823
  · exact B450827
  · exact B450831
  · exact B450835
  · exact B450839
  · exact B450843
  · exact B450847
  · exact B450851
  · exact B450855
  · exact B450859
  · exact B450863
  · exact B450867
  · exact B450871
  · exact B450875
  · exact B450879
  · exact B450883
  · exact B450887
  · exact B450891
  · exact B450895
  · exact B450899
  · exact B450903
  · exact B450907
  · exact B450911
  · exact B450915
  · exact B450919
  · exact B450923
  · exact B450927
  · exact B450931
  · exact B450935
  · exact B450939
  · exact B450943
  · exact B450947
  · exact B450951
  · exact B450955
  · exact B450959
  · exact B450963
  · exact B450967
  · exact B450971
  · exact B450975
  · exact B450979
  · exact B450983
  · exact B450987
  · exact B450991
  · exact B450995
  · exact B450999
  · exact B451003
  · exact B451007
  · exact B451011
  · exact B451015
  · exact B451019
  · exact B451023
  · exact B451027
  · exact B451031
  · exact B451035
  · exact B451039
  · exact B451043
  · exact B451047
  · exact B451051
  · exact B451055
  · exact B451059
  · exact B451063
  · exact B451067
  · exact B451071
  · exact B451075
  · exact B451079
  · exact B451083
  · exact B451087
  · exact B451091
  · exact B451095
  · exact B451099
  · exact B451103
  · exact B451107
  · exact B451111
  · exact B451115
  · exact B451119
  · exact B451123
  · exact B451127
  · exact B451131
  · exact B451135
  · exact B451139
  · exact B451143
  · exact B451147
  · exact B451151
  · exact B451155
  · exact B451159
  · exact B451163
  · exact B451167
  · exact B451171
  · exact B451175
  · exact B451179
  · exact B451183
  · exact B451187
  · exact B451191
  · exact B451195
  · exact B451199
  · exact B451203
  · exact B451207
  · exact B451211
  · exact B451215
  · exact B451219
  · exact B451223
  · exact B451227
  · exact B451231
  · exact B451235
  · exact B451239
  · exact B451243
  · exact B451247
  · exact B451251
  · exact B451255
  · exact B451259
  · exact B451263
  · exact B451267
  · exact B451271
  · exact B451275
  · exact B451279
  · exact B451283
  · exact B451287
  · exact B451291
  · exact B451295
  · exact B451299
  · exact B451303
  · exact B451307
  · exact B451311
  · exact B451315
  · exact B451319
  · exact B451323
  · exact B451327
  · exact B451331
  · exact B451335
  · exact B451339
  · exact B451343
  · exact B451347
  · exact B451351
  · exact B451355
  · exact B451359
  · exact B451363
  · exact B451367
  · exact B451371
  · exact B451375
  · exact B451379
  · exact B451383
  · exact B451387
  · exact B451391
  · exact B451395
  · exact B451399
  · exact B451403
  · exact B451407
  · exact B451411
  · exact B451415
  · exact B451419
  · exact B451423
  · exact B451427
  · exact B451431
  · exact B451435
  · exact B451439
  · exact B451443
  · exact B451447
  · exact B451451
  · exact B451455
  · exact B451459
  · exact B451463
  · exact B451467
  · exact B451471
  · exact B451475
  · exact B451479
  · exact B451483
  · exact B451487
  · exact B451491
  · exact B451495
  · exact B451499
  · exact B451503
  · exact B451507
  · exact B451511
  · exact B451515
  · exact B451519
  · exact B451523
  · exact B451527
  · exact B451531
  · exact B451535
  · exact B451539
  · exact B451543
  · exact B451547
  · exact B451551
  · exact B451555
  · exact B451559
  · exact B451563
  · exact B451567
  · exact B451571
  · exact B451575
  · exact B451579
  · exact B451583
  · exact B451587
  · exact B451591
  · exact B451595
  · exact B451599
  · exact B451603
  · exact B451607
  · exact B451611
  · exact B451615
  · exact B451619
  · exact B451623
  · exact B451627
  · exact B451631
  · exact B451635
  · exact B451639
  · exact B451643
  · exact B451647
  · exact B451651
  · exact B451655
  · exact B451659
  · exact B451663
  · exact B451667
  · exact B451671
  · exact B451675
  · exact B451679
  · exact B451683
  · exact B451687
  · exact B451691
  · exact B451695
  · exact B451699
  · exact B451703
  · exact B451707
  · exact B451711
  · exact B451715
  · exact B451719
  · exact B451723
  · exact B451727
  · exact B451731
  · exact B451735
  · exact B451739
  · exact B451743
  · exact B451747
  · exact B451751
  · exact B451755
  · exact B451759
  · exact B451763
  · exact B451767
  · exact B451771
  · exact B451775
  · exact B451779

theorem solution (m : ℕ) (hlo : 447780 ≤ m) (hhi : m ≤ 451780) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 111945 ≤ j := by omega
    have hj2 : j ≤ 112944 := by omega
    have hb : Blo 447780 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 112645 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
