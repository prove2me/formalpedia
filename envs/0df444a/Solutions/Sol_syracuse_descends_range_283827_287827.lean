-- Prove2me | solution 1 for syracuse_descends_range_283827_287827
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:44:13.581537+00:00
-- url     : https://prove2.me/submissions/e0612f02-8ebc-4dca-91c6-4d6eaef46ac6

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


theorem B426005 : Blo 283827 426005 := bbase (se 6 (by rfl) ⟨9984, by rfl⟩ : syracuseStep 426005 = 19969) (by norm_num)
theorem B589853 : Blo 283827 589853 := bbase (se 3 (by rfl) ⟨110597, by rfl⟩ : syracuseStep 589853 = 221195) (by norm_num)
theorem B426029 : Blo 283827 426029 := bbase (se 3 (by rfl) ⟨79880, by rfl⟩ : syracuseStep 426029 = 159761) (by norm_num)
theorem B426053 : Blo 283827 426053 := bbase (se 4 (by rfl) ⟨39942, by rfl⟩ : syracuseStep 426053 = 79885) (by norm_num)
theorem B426077 : Blo 283827 426077 := bbase (se 3 (by rfl) ⟨79889, by rfl⟩ : syracuseStep 426077 = 159779) (by norm_num)
theorem B360541 : Blo 283827 360541 := bbase (se 3 (by rfl) ⟨67601, by rfl⟩ : syracuseStep 360541 = 135203) (by norm_num)
theorem B426101 : Blo 283827 426101 := bbase (se 5 (by rfl) ⟨19973, by rfl⟩ : syracuseStep 426101 = 39947) (by norm_num)
theorem B721021 : Blo 283827 721021 := bbase (se 3 (by rfl) ⟨135191, by rfl⟩ : syracuseStep 721021 = 270383) (by norm_num)
theorem B426125 : Blo 283827 426125 := bbase (se 3 (by rfl) ⟨79898, by rfl⟩ : syracuseStep 426125 = 159797) (by norm_num)
theorem B426149 : Blo 283827 426149 := bbase (se 4 (by rfl) ⟨39951, by rfl⟩ : syracuseStep 426149 = 79903) (by norm_num)
theorem B917669 : Blo 283827 917669 := bbase (se 4 (by rfl) ⟨86031, by rfl⟩ : syracuseStep 917669 = 172063) (by norm_num)
theorem B295093 : Blo 283827 295093 := bbase (se 5 (by rfl) ⟨13832, by rfl⟩ : syracuseStep 295093 = 27665) (by norm_num)
theorem B426173 : Blo 283827 426173 := bbase (se 3 (by rfl) ⟨79907, by rfl⟩ : syracuseStep 426173 = 159815) (by norm_num)
theorem B524485 : Blo 283827 524485 := bbase (se 4 (by rfl) ⟨49170, by rfl⟩ : syracuseStep 524485 = 98341) (by norm_num)
theorem B1474757 : Blo 283827 1474757 := bbase (se 4 (by rfl) ⟨138258, by rfl⟩ : syracuseStep 1474757 = 276517) (by norm_num)
theorem B426197 : Blo 283827 426197 := bbase (se 7 (by rfl) ⟨4994, by rfl⟩ : syracuseStep 426197 = 9989) (by norm_num)
theorem B426221 : Blo 283827 426221 := bbase (se 3 (by rfl) ⟨79916, by rfl⟩ : syracuseStep 426221 = 159833) (by norm_num)
theorem B721133 : Blo 283827 721133 := bbase (se 3 (by rfl) ⟨135212, by rfl⟩ : syracuseStep 721133 = 270425) (by norm_num)
theorem B1212677 : Blo 283827 1212677 := bbase (se 4 (by rfl) ⟨113688, by rfl⟩ : syracuseStep 1212677 = 227377) (by norm_num)
theorem B426245 : Blo 283827 426245 := bbase (se 4 (by rfl) ⟨39960, by rfl⟩ : syracuseStep 426245 = 79921) (by norm_num)
theorem B360713 : Blo 283827 360713 := bbase (se 2 (by rfl) ⟨135267, by rfl⟩ : syracuseStep 360713 = 270535) (by norm_num)
theorem B426269 : Blo 283827 426269 := bbase (se 3 (by rfl) ⟨79925, by rfl⟩ : syracuseStep 426269 = 159851) (by norm_num)
theorem B426293 : Blo 283827 426293 := bbase (se 5 (by rfl) ⟨19982, by rfl⟩ : syracuseStep 426293 = 39965) (by norm_num)
theorem B688445 : Blo 283827 688445 := bbase (se 3 (by rfl) ⟨129083, by rfl⟩ : syracuseStep 688445 = 258167) (by norm_num)
theorem B360769 : Blo 283827 360769 := bbase (se 2 (by rfl) ⟨135288, by rfl⟩ : syracuseStep 360769 = 270577) (by norm_num)
theorem B426317 : Blo 283827 426317 := bbase (se 3 (by rfl) ⟨79934, by rfl⟩ : syracuseStep 426317 = 159869) (by norm_num)
theorem B426341 : Blo 283827 426341 := bbase (se 4 (by rfl) ⟨39969, by rfl⟩ : syracuseStep 426341 = 79939) (by norm_num)
theorem B426365 : Blo 283827 426365 := bbase (se 3 (by rfl) ⟨79943, by rfl⟩ : syracuseStep 426365 = 159887) (by norm_num)
theorem B426389 : Blo 283827 426389 := bbase (se 6 (by rfl) ⟨9993, by rfl⟩ : syracuseStep 426389 = 19987) (by norm_num)
theorem B360865 : Blo 283827 360865 := bbase (se 2 (by rfl) ⟨135324, by rfl⟩ : syracuseStep 360865 = 270649) (by norm_num)
theorem B426413 : Blo 283827 426413 := bbase (se 3 (by rfl) ⟨79952, by rfl⟩ : syracuseStep 426413 = 159905) (by norm_num)
theorem B721325 : Blo 283827 721325 := bbase (se 3 (by rfl) ⟨135248, by rfl⟩ : syracuseStep 721325 = 270497) (by norm_num)
theorem B426437 : Blo 283827 426437 := bbase (se 4 (by rfl) ⟨39978, by rfl⟩ : syracuseStep 426437 = 79957) (by norm_num)
theorem B426461 : Blo 283827 426461 := bbase (se 3 (by rfl) ⟨79961, by rfl⟩ : syracuseStep 426461 = 159923) (by norm_num)
theorem B459245 : Blo 283827 459245 := bbase (se 3 (by rfl) ⟨86108, by rfl⟩ : syracuseStep 459245 = 172217) (by norm_num)
theorem B426485 : Blo 283827 426485 := bbase (se 5 (by rfl) ⟨19991, by rfl⟩ : syracuseStep 426485 = 39983) (by norm_num)
theorem B426509 : Blo 283827 426509 := bbase (se 3 (by rfl) ⟨79970, by rfl⟩ : syracuseStep 426509 = 159941) (by norm_num)
theorem B1212965 : Blo 283827 1212965 := bbase (se 4 (by rfl) ⟨113715, by rfl⟩ : syracuseStep 1212965 = 227431) (by norm_num)
theorem B426533 : Blo 283827 426533 := bbase (se 4 (by rfl) ⟨39987, by rfl⟩ : syracuseStep 426533 = 79975) (by norm_num)
theorem B426557 : Blo 283827 426557 := bbase (se 3 (by rfl) ⟨79979, by rfl⟩ : syracuseStep 426557 = 159959) (by norm_num)
theorem B361037 : Blo 283827 361037 := bbase (se 3 (by rfl) ⟨67694, by rfl⟩ : syracuseStep 361037 = 135389) (by norm_num)
theorem B426581 : Blo 283827 426581 := bbase (se 8 (by rfl) ⟨2499, by rfl⟩ : syracuseStep 426581 = 4999) (by norm_num)
theorem B1081957 : Blo 283827 1081957 := bbase (se 4 (by rfl) ⟨101433, by rfl⟩ : syracuseStep 1081957 = 202867) (by norm_num)
theorem B426605 : Blo 283827 426605 := bbase (se 3 (by rfl) ⟨79988, by rfl⟩ : syracuseStep 426605 = 159977) (by norm_num)
theorem B459373 : Blo 283827 459373 := bbase (se 3 (by rfl) ⟨86132, by rfl⟩ : syracuseStep 459373 = 172265) (by norm_num)
theorem B426629 : Blo 283827 426629 := bbase (se 4 (by rfl) ⟨39996, by rfl⟩ : syracuseStep 426629 = 79993) (by norm_num)
theorem B361093 : Blo 283827 361093 := bbase (se 4 (by rfl) ⟨33852, by rfl⟩ : syracuseStep 361093 = 67705) (by norm_num)
theorem B426653 : Blo 283827 426653 := bbase (se 3 (by rfl) ⟨79997, by rfl⟩ : syracuseStep 426653 = 159995) (by norm_num)
theorem B459437 : Blo 283827 459437 := bbase (se 3 (by rfl) ⟨86144, by rfl⟩ : syracuseStep 459437 = 172289) (by norm_num)
theorem B426677 : Blo 283827 426677 := bbase (se 5 (by rfl) ⟨20000, by rfl⟩ : syracuseStep 426677 = 40001) (by norm_num)
theorem B426701 : Blo 283827 426701 := bbase (se 3 (by rfl) ⟨80006, by rfl⟩ : syracuseStep 426701 = 160013) (by norm_num)
theorem B426725 : Blo 283827 426725 := bbase (se 4 (by rfl) ⟨40005, by rfl⟩ : syracuseStep 426725 = 80011) (by norm_num)
theorem B361189 : Blo 283827 361189 := bbase (se 4 (by rfl) ⟨33861, by rfl⟩ : syracuseStep 361189 = 67723) (by norm_num)
theorem B426749 : Blo 283827 426749 := bbase (se 3 (by rfl) ⟨80015, by rfl⟩ : syracuseStep 426749 = 160031) (by norm_num)
theorem B721669 : Blo 283827 721669 := bbase (se 4 (by rfl) ⟨67656, by rfl⟩ : syracuseStep 721669 = 135313) (by norm_num)
theorem B426773 : Blo 283827 426773 := bbase (se 6 (by rfl) ⟨10002, by rfl⟩ : syracuseStep 426773 = 20005) (by norm_num)
theorem B426797 : Blo 283827 426797 := bbase (se 3 (by rfl) ⟨80024, by rfl⟩ : syracuseStep 426797 = 160049) (by norm_num)
theorem B426821 : Blo 283827 426821 := bbase (se 4 (by rfl) ⟨40014, by rfl⟩ : syracuseStep 426821 = 80029) (by norm_num)
theorem B525133 : Blo 283827 525133 := bbase (se 3 (by rfl) ⟨98462, by rfl⟩ : syracuseStep 525133 = 196925) (by norm_num)
theorem B17662805 : Blo 283827 17662805 := bbase (se 9 (by rfl) ⟨51746, by rfl⟩ : syracuseStep 17662805 = 103493) (by norm_num)
theorem B426845 : Blo 283827 426845 := bbase (se 3 (by rfl) ⟨80033, by rfl⟩ : syracuseStep 426845 = 160067) (by norm_num)
theorem B426869 : Blo 283827 426869 := bbase (se 5 (by rfl) ⟨20009, by rfl⟩ : syracuseStep 426869 = 40019) (by norm_num)
theorem B721781 : Blo 283827 721781 := bbase (se 5 (by rfl) ⟨33833, by rfl⟩ : syracuseStep 721781 = 67667) (by norm_num)
theorem B426893 : Blo 283827 426893 := bbase (se 3 (by rfl) ⟨80042, by rfl⟩ : syracuseStep 426893 = 160085) (by norm_num)
theorem B361361 : Blo 283827 361361 := bbase (se 2 (by rfl) ⟨135510, by rfl⟩ : syracuseStep 361361 = 271021) (by norm_num)
theorem B1082261 : Blo 283827 1082261 := bbase (se 6 (by rfl) ⟨25365, by rfl⟩ : syracuseStep 1082261 = 50731) (by norm_num)
theorem B426917 : Blo 283827 426917 := bbase (se 4 (by rfl) ⟨40023, by rfl⟩ : syracuseStep 426917 = 80047) (by norm_num)
theorem B426941 : Blo 283827 426941 := bbase (se 3 (by rfl) ⟨80051, by rfl⟩ : syracuseStep 426941 = 160103) (by norm_num)
theorem B361417 : Blo 283827 361417 := bbase (se 2 (by rfl) ⟨135531, by rfl⟩ : syracuseStep 361417 = 271063) (by norm_num)
theorem B426965 : Blo 283827 426965 := bbase (se 7 (by rfl) ⟨5003, by rfl⟩ : syracuseStep 426965 = 10007) (by norm_num)
theorem B426989 : Blo 283827 426989 := bbase (se 3 (by rfl) ⟨80060, by rfl⟩ : syracuseStep 426989 = 160121) (by norm_num)
theorem B427013 : Blo 283827 427013 := bbase (se 4 (by rfl) ⟨40032, by rfl⟩ : syracuseStep 427013 = 80065) (by norm_num)
theorem B427037 : Blo 283827 427037 := bbase (se 3 (by rfl) ⟨80069, by rfl⟩ : syracuseStep 427037 = 160139) (by norm_num)
theorem B361513 : Blo 283827 361513 := bbase (se 2 (by rfl) ⟨135567, by rfl⟩ : syracuseStep 361513 = 271135) (by norm_num)
theorem B427061 : Blo 283827 427061 := bbase (se 5 (by rfl) ⟨20018, by rfl⟩ : syracuseStep 427061 = 40037) (by norm_num)
theorem B721973 : Blo 283827 721973 := bbase (se 5 (by rfl) ⟨33842, by rfl⟩ : syracuseStep 721973 = 67685) (by norm_num)
theorem B689213 : Blo 283827 689213 := bbase (se 3 (by rfl) ⟨129227, by rfl⟩ : syracuseStep 689213 = 258455) (by norm_num)
theorem B427085 : Blo 283827 427085 := bbase (se 3 (by rfl) ⟨80078, by rfl⟩ : syracuseStep 427085 = 160157) (by norm_num)
theorem B427109 : Blo 283827 427109 := bbase (se 4 (by rfl) ⟨40041, by rfl⟩ : syracuseStep 427109 = 80083) (by norm_num)
theorem B1442933 : Blo 283827 1442933 := bbase (se 5 (by rfl) ⟨67637, by rfl⟩ : syracuseStep 1442933 = 135275) (by norm_num)
theorem B427133 : Blo 283827 427133 := bbase (se 3 (by rfl) ⟨80087, by rfl⟩ : syracuseStep 427133 = 160175) (by norm_num)
theorem B427157 : Blo 283827 427157 := bbase (se 6 (by rfl) ⟨10011, by rfl⟩ : syracuseStep 427157 = 20023) (by norm_num)
theorem B427181 : Blo 283827 427181 := bbase (se 3 (by rfl) ⟨80096, by rfl⟩ : syracuseStep 427181 = 160193) (by norm_num)
theorem B427205 : Blo 283827 427205 := bbase (se 4 (by rfl) ⟨40050, by rfl⟩ : syracuseStep 427205 = 80101) (by norm_num)
theorem B361685 : Blo 283827 361685 := bbase (se 7 (by rfl) ⟨4238, by rfl⟩ : syracuseStep 361685 = 8477) (by norm_num)
theorem B427229 : Blo 283827 427229 := bbase (se 3 (by rfl) ⟨80105, by rfl⟩ : syracuseStep 427229 = 160211) (by norm_num)
theorem B427253 : Blo 283827 427253 := bbase (se 5 (by rfl) ⟨20027, by rfl⟩ : syracuseStep 427253 = 40055) (by norm_num)
theorem B918773 : Blo 283827 918773 := bbase (se 5 (by rfl) ⟨43067, by rfl⟩ : syracuseStep 918773 = 86135) (by norm_num)
theorem B427277 : Blo 283827 427277 := bbase (se 3 (by rfl) ⟨80114, by rfl⟩ : syracuseStep 427277 = 160229) (by norm_num)
theorem B361741 : Blo 283827 361741 := bbase (se 3 (by rfl) ⟨67826, by rfl⟩ : syracuseStep 361741 = 135653) (by norm_num)
theorem B1213717 : Blo 283827 1213717 := bbase (se 6 (by rfl) ⟨28446, by rfl⟩ : syracuseStep 1213717 = 56893) (by norm_num)
theorem B427301 : Blo 283827 427301 := bbase (se 4 (by rfl) ⟨40059, by rfl⟩ : syracuseStep 427301 = 80119) (by norm_num)
theorem B427325 : Blo 283827 427325 := bbase (se 3 (by rfl) ⟨80123, by rfl⟩ : syracuseStep 427325 = 160247) (by norm_num)
theorem B427349 : Blo 283827 427349 := bbase (se 12 (by rfl) ⟨156, by rfl⟩ : syracuseStep 427349 = 313) (by norm_num)
theorem B427373 : Blo 283827 427373 := bbase (se 3 (by rfl) ⟨80132, by rfl⟩ : syracuseStep 427373 = 160265) (by norm_num)
theorem B361837 : Blo 283827 361837 := bbase (se 3 (by rfl) ⟨67844, by rfl⟩ : syracuseStep 361837 = 135689) (by norm_num)
theorem B427397 : Blo 283827 427397 := bbase (se 4 (by rfl) ⟨40068, by rfl⟩ : syracuseStep 427397 = 80137) (by norm_num)
theorem B722317 : Blo 283827 722317 := bbase (se 3 (by rfl) ⟨135434, by rfl⟩ : syracuseStep 722317 = 270869) (by norm_num)
theorem B427421 : Blo 283827 427421 := bbase (se 3 (by rfl) ⟨80141, by rfl⟩ : syracuseStep 427421 = 160283) (by norm_num)
theorem B427445 : Blo 283827 427445 := bbase (se 5 (by rfl) ⟨20036, by rfl⟩ : syracuseStep 427445 = 40073) (by norm_num)
theorem B427469 : Blo 283827 427469 := bbase (se 3 (by rfl) ⟨80150, by rfl⟩ : syracuseStep 427469 = 160301) (by norm_num)
theorem B427493 : Blo 283827 427493 := bbase (se 4 (by rfl) ⟨40077, by rfl⟩ : syracuseStep 427493 = 80155) (by norm_num)
theorem B427517 : Blo 283827 427517 := bbase (se 3 (by rfl) ⟨80159, by rfl⟩ : syracuseStep 427517 = 160319) (by norm_num)
theorem B722429 : Blo 283827 722429 := bbase (se 3 (by rfl) ⟨135455, by rfl⟩ : syracuseStep 722429 = 270911) (by norm_num)
theorem B427541 : Blo 283827 427541 := bbase (se 6 (by rfl) ⟨10020, by rfl⟩ : syracuseStep 427541 = 20041) (by norm_num)
theorem B362009 : Blo 283827 362009 := bbase (se 2 (by rfl) ⟨135753, by rfl⟩ : syracuseStep 362009 = 271507) (by norm_num)
theorem B427565 : Blo 283827 427565 := bbase (se 3 (by rfl) ⟨80168, by rfl⟩ : syracuseStep 427565 = 160337) (by norm_num)
theorem B427589 : Blo 283827 427589 := bbase (se 4 (by rfl) ⟨40086, by rfl⟩ : syracuseStep 427589 = 80173) (by norm_num)
theorem B362065 : Blo 283827 362065 := bbase (se 2 (by rfl) ⟨135774, by rfl⟩ : syracuseStep 362065 = 271549) (by norm_num)
theorem B427613 : Blo 283827 427613 := bbase (se 3 (by rfl) ⟨80177, by rfl⟩ : syracuseStep 427613 = 160355) (by norm_num)
theorem B427637 : Blo 283827 427637 := bbase (se 5 (by rfl) ⟨20045, by rfl⟩ : syracuseStep 427637 = 40091) (by norm_num)
theorem B427661 : Blo 283827 427661 := bbase (se 3 (by rfl) ⟨80186, by rfl⟩ : syracuseStep 427661 = 160373) (by norm_num)
theorem B427685 : Blo 283827 427685 := bbase (se 4 (by rfl) ⟨40095, by rfl⟩ : syracuseStep 427685 = 80191) (by norm_num)
theorem B362161 : Blo 283827 362161 := bbase (se 2 (by rfl) ⟨135810, by rfl⟩ : syracuseStep 362161 = 271621) (by norm_num)
theorem B427709 : Blo 283827 427709 := bbase (se 3 (by rfl) ⟨80195, by rfl⟩ : syracuseStep 427709 = 160391) (by norm_num)
theorem B722621 : Blo 283827 722621 := bbase (se 3 (by rfl) ⟨135491, by rfl⟩ : syracuseStep 722621 = 270983) (by norm_num)
theorem B427733 : Blo 283827 427733 := bbase (se 7 (by rfl) ⟨5012, by rfl⟩ : syracuseStep 427733 = 10025) (by norm_num)
theorem B427757 : Blo 283827 427757 := bbase (se 3 (by rfl) ⟨80204, by rfl⟩ : syracuseStep 427757 = 160409) (by norm_num)
theorem B427781 : Blo 283827 427781 := bbase (se 4 (by rfl) ⟨40104, by rfl⟩ : syracuseStep 427781 = 80209) (by norm_num)
theorem B5605141 : Blo 283827 5605141 := bbase (se 6 (by rfl) ⟨131370, by rfl⟩ : syracuseStep 5605141 = 262741) (by norm_num)
theorem B427805 : Blo 283827 427805 := bbase (se 3 (by rfl) ⟨80213, by rfl⟩ : syracuseStep 427805 = 160427) (by norm_num)
theorem B427829 : Blo 283827 427829 := bbase (se 5 (by rfl) ⟨20054, by rfl⟩ : syracuseStep 427829 = 40109) (by norm_num)
theorem B427853 : Blo 283827 427853 := bbase (se 3 (by rfl) ⟨80222, by rfl⟩ : syracuseStep 427853 = 160445) (by norm_num)
theorem B362333 : Blo 283827 362333 := bbase (se 3 (by rfl) ⟨67937, by rfl⟩ : syracuseStep 362333 = 135875) (by norm_num)
theorem B427877 : Blo 283827 427877 := bbase (se 4 (by rfl) ⟨40113, by rfl⟩ : syracuseStep 427877 = 80227) (by norm_num)
theorem B427901 : Blo 283827 427901 := bbase (se 3 (by rfl) ⟨80231, by rfl⟩ : syracuseStep 427901 = 160463) (by norm_num)
theorem B427925 : Blo 283827 427925 := bbase (se 6 (by rfl) ⟨10029, by rfl⟩ : syracuseStep 427925 = 20059) (by norm_num)
theorem B362389 : Blo 283827 362389 := bbase (se 6 (by rfl) ⟨8493, by rfl⟩ : syracuseStep 362389 = 16987) (by norm_num)
theorem B427949 : Blo 283827 427949 := bbase (se 3 (by rfl) ⟨80240, by rfl⟩ : syracuseStep 427949 = 160481) (by norm_num)
theorem B427973 : Blo 283827 427973 := bbase (se 4 (by rfl) ⟨40122, by rfl⟩ : syracuseStep 427973 = 80245) (by norm_num)
theorem B460757 : Blo 283827 460757 := bbase (se 7 (by rfl) ⟨5399, by rfl⟩ : syracuseStep 460757 = 10799) (by norm_num)
theorem B427997 : Blo 283827 427997 := bbase (se 3 (by rfl) ⟨80249, by rfl⟩ : syracuseStep 427997 = 160499) (by norm_num)
theorem B1214453 : Blo 283827 1214453 := bbase (se 5 (by rfl) ⟨56927, by rfl⟩ : syracuseStep 1214453 = 113855) (by norm_num)
theorem B428021 : Blo 283827 428021 := bbase (se 5 (by rfl) ⟨20063, by rfl⟩ : syracuseStep 428021 = 40127) (by norm_num)
theorem B362485 : Blo 283827 362485 := bbase (se 5 (by rfl) ⟨16991, by rfl⟩ : syracuseStep 362485 = 33983) (by norm_num)
theorem B428045 : Blo 283827 428045 := bbase (se 3 (by rfl) ⟨80258, by rfl⟩ : syracuseStep 428045 = 160517) (by norm_num)
theorem B722965 : Blo 283827 722965 := bbase (se 6 (by rfl) ⟨16944, by rfl⟩ : syracuseStep 722965 = 33889) (by norm_num)
theorem B428069 : Blo 283827 428069 := bbase (se 4 (by rfl) ⟨40131, by rfl⟩ : syracuseStep 428069 = 80263) (by norm_num)
theorem B428093 : Blo 283827 428093 := bbase (se 3 (by rfl) ⟨80267, by rfl⟩ : syracuseStep 428093 = 160535) (by norm_num)
theorem B428117 : Blo 283827 428117 := bbase (se 8 (by rfl) ⟨2508, by rfl⟩ : syracuseStep 428117 = 5017) (by norm_num)
theorem B460885 : Blo 283827 460885 := bbase (se 8 (by rfl) ⟨2700, by rfl⟩ : syracuseStep 460885 = 5401) (by norm_num)
theorem B428141 : Blo 283827 428141 := bbase (se 3 (by rfl) ⟨80276, by rfl⟩ : syracuseStep 428141 = 160553) (by norm_num)
theorem B1476725 : Blo 283827 1476725 := bbase (se 5 (by rfl) ⟨69221, by rfl⟩ : syracuseStep 1476725 = 138443) (by norm_num)
theorem B428165 : Blo 283827 428165 := bbase (se 4 (by rfl) ⟨40140, by rfl⟩ : syracuseStep 428165 = 80281) (by norm_num)
theorem B723077 : Blo 283827 723077 := bbase (se 4 (by rfl) ⟨67788, by rfl⟩ : syracuseStep 723077 = 135577) (by norm_num)
theorem B428189 : Blo 283827 428189 := bbase (se 3 (by rfl) ⟨80285, by rfl⟩ : syracuseStep 428189 = 160571) (by norm_num)
theorem B362657 : Blo 283827 362657 := bbase (se 2 (by rfl) ⟨135996, by rfl⟩ : syracuseStep 362657 = 271993) (by norm_num)
theorem B428213 : Blo 283827 428213 := bbase (se 5 (by rfl) ⟨20072, by rfl⟩ : syracuseStep 428213 = 40145) (by norm_num)
theorem B428237 : Blo 283827 428237 := bbase (se 3 (by rfl) ⟨80294, by rfl⟩ : syracuseStep 428237 = 160589) (by norm_num)
theorem B362713 : Blo 283827 362713 := bbase (se 2 (by rfl) ⟨136017, by rfl⟩ : syracuseStep 362713 = 272035) (by norm_num)
theorem B428261 : Blo 283827 428261 := bbase (se 4 (by rfl) ⟨40149, by rfl⟩ : syracuseStep 428261 = 80299) (by norm_num)
theorem B428285 : Blo 283827 428285 := bbase (se 3 (by rfl) ⟨80303, by rfl⟩ : syracuseStep 428285 = 160607) (by norm_num)
theorem B428309 : Blo 283827 428309 := bbase (se 6 (by rfl) ⟨10038, by rfl⟩ : syracuseStep 428309 = 20077) (by norm_num)
theorem B428333 : Blo 283827 428333 := bbase (se 3 (by rfl) ⟨80312, by rfl⟩ : syracuseStep 428333 = 160625) (by norm_num)
theorem B362809 : Blo 283827 362809 := bbase (se 2 (by rfl) ⟨136053, by rfl⟩ : syracuseStep 362809 = 272107) (by norm_num)
theorem B428357 : Blo 283827 428357 := bbase (se 4 (by rfl) ⟨40158, by rfl⟩ : syracuseStep 428357 = 80317) (by norm_num)
theorem B723269 : Blo 283827 723269 := bbase (se 4 (by rfl) ⟨67806, by rfl⟩ : syracuseStep 723269 = 135613) (by norm_num)
theorem B428381 : Blo 283827 428381 := bbase (se 3 (by rfl) ⟨80321, by rfl⟩ : syracuseStep 428381 = 160643) (by norm_num)
theorem B428405 : Blo 283827 428405 := bbase (se 5 (by rfl) ⟨20081, by rfl⟩ : syracuseStep 428405 = 40163) (by norm_num)
theorem B1444229 : Blo 283827 1444229 := bbase (se 4 (by rfl) ⟨135396, by rfl⟩ : syracuseStep 1444229 = 270793) (by norm_num)
theorem B428429 : Blo 283827 428429 := bbase (se 3 (by rfl) ⟨80330, by rfl⟩ : syracuseStep 428429 = 160661) (by norm_num)
theorem B428453 : Blo 283827 428453 := bbase (se 4 (by rfl) ⟨40167, by rfl⟩ : syracuseStep 428453 = 80335) (by norm_num)
theorem B428477 : Blo 283827 428477 := bbase (se 3 (by rfl) ⟨80339, by rfl⟩ : syracuseStep 428477 = 160679) (by norm_num)
theorem B428501 : Blo 283827 428501 := bbase (se 7 (by rfl) ⟨5021, by rfl⟩ : syracuseStep 428501 = 10043) (by norm_num)
theorem B362981 : Blo 283827 362981 := bbase (se 4 (by rfl) ⟨34029, by rfl⟩ : syracuseStep 362981 = 68059) (by norm_num)
theorem B428525 : Blo 283827 428525 := bbase (se 3 (by rfl) ⟨80348, by rfl⟩ : syracuseStep 428525 = 160697) (by norm_num)
theorem B428549 : Blo 283827 428549 := bbase (se 4 (by rfl) ⟨40176, by rfl⟩ : syracuseStep 428549 = 80353) (by norm_num)
theorem B428573 : Blo 283827 428573 := bbase (se 3 (by rfl) ⟨80357, by rfl⟩ : syracuseStep 428573 = 160715) (by norm_num)
theorem B363037 : Blo 283827 363037 := bbase (se 3 (by rfl) ⟨68069, by rfl⟩ : syracuseStep 363037 = 136139) (by norm_num)
theorem B428597 : Blo 283827 428597 := bbase (se 5 (by rfl) ⟨20090, by rfl⟩ : syracuseStep 428597 = 40181) (by norm_num)
theorem B428621 : Blo 283827 428621 := bbase (se 3 (by rfl) ⟨80366, by rfl⟩ : syracuseStep 428621 = 160733) (by norm_num)
theorem B428645 : Blo 283827 428645 := bbase (se 4 (by rfl) ⟨40185, by rfl⟩ : syracuseStep 428645 = 80371) (by norm_num)
theorem B428669 : Blo 283827 428669 := bbase (se 3 (by rfl) ⟨80375, by rfl⟩ : syracuseStep 428669 = 160751) (by norm_num)
theorem B363133 : Blo 283827 363133 := bbase (se 3 (by rfl) ⟨68087, by rfl⟩ : syracuseStep 363133 = 136175) (by norm_num)
theorem B428693 : Blo 283827 428693 := bbase (se 6 (by rfl) ⟨10047, by rfl⟩ : syracuseStep 428693 = 20095) (by norm_num)
theorem B723613 : Blo 283827 723613 := bbase (se 3 (by rfl) ⟨135677, by rfl⟩ : syracuseStep 723613 = 271355) (by norm_num)
theorem B428717 : Blo 283827 428717 := bbase (se 3 (by rfl) ⟨80384, by rfl⟩ : syracuseStep 428717 = 160769) (by norm_num)
theorem B428741 : Blo 283827 428741 := bbase (se 4 (by rfl) ⟨40194, by rfl⟩ : syracuseStep 428741 = 80389) (by norm_num)
theorem B428765 : Blo 283827 428765 := bbase (se 3 (by rfl) ⟨80393, by rfl⟩ : syracuseStep 428765 = 160787) (by norm_num)
theorem B690925 : Blo 283827 690925 := bbase (se 3 (by rfl) ⟨129548, by rfl⟩ : syracuseStep 690925 = 259097) (by norm_num)
theorem B428789 : Blo 283827 428789 := bbase (se 5 (by rfl) ⟨20099, by rfl⟩ : syracuseStep 428789 = 40199) (by norm_num)
theorem B428813 : Blo 283827 428813 := bbase (se 3 (by rfl) ⟨80402, by rfl⟩ : syracuseStep 428813 = 160805) (by norm_num)
theorem B723725 : Blo 283827 723725 := bbase (se 3 (by rfl) ⟨135698, by rfl⟩ : syracuseStep 723725 = 271397) (by norm_num)
theorem B428837 : Blo 283827 428837 := bbase (se 4 (by rfl) ⟨40203, by rfl⟩ : syracuseStep 428837 = 80407) (by norm_num)
theorem B363305 : Blo 283827 363305 := bbase (se 2 (by rfl) ⟨136239, by rfl⟩ : syracuseStep 363305 = 272479) (by norm_num)
theorem B428861 : Blo 283827 428861 := bbase (se 3 (by rfl) ⟨80411, by rfl⟩ : syracuseStep 428861 = 160823) (by norm_num)
theorem B428885 : Blo 283827 428885 := bbase (se 9 (by rfl) ⟨1256, by rfl⟩ : syracuseStep 428885 = 2513) (by norm_num)
theorem B363361 : Blo 283827 363361 := bbase (se 2 (by rfl) ⟨136260, by rfl⟩ : syracuseStep 363361 = 272521) (by norm_num)
theorem B428909 : Blo 283827 428909 := bbase (se 3 (by rfl) ⟨80420, by rfl⟩ : syracuseStep 428909 = 160841) (by norm_num)
theorem B428933 : Blo 283827 428933 := bbase (se 4 (by rfl) ⟨40212, by rfl⟩ : syracuseStep 428933 = 80425) (by norm_num)
theorem B428957 : Blo 283827 428957 := bbase (se 3 (by rfl) ⟨80429, by rfl⟩ : syracuseStep 428957 = 160859) (by norm_num)
theorem B428981 : Blo 283827 428981 := bbase (se 5 (by rfl) ⟨20108, by rfl⟩ : syracuseStep 428981 = 40217) (by norm_num)
theorem B363457 : Blo 283827 363457 := bbase (se 2 (by rfl) ⟨136296, by rfl⟩ : syracuseStep 363457 = 272593) (by norm_num)
theorem B723917 : Blo 283827 723917 := bbase (se 3 (by rfl) ⟨135734, by rfl⟩ : syracuseStep 723917 = 271469) (by norm_num)
theorem B429005 : Blo 283827 429005 := bbase (se 3 (by rfl) ⟨80438, by rfl⟩ : syracuseStep 429005 = 160877) (by norm_num)
theorem B1084373 : Blo 283827 1084373 := bbase (se 7 (by rfl) ⟨12707, by rfl⟩ : syracuseStep 1084373 = 25415) (by norm_num)
theorem B429029 : Blo 283827 429029 := bbase (se 4 (by rfl) ⟨40221, by rfl⟩ : syracuseStep 429029 = 80443) (by norm_num)
theorem B429053 : Blo 283827 429053 := bbase (se 3 (by rfl) ⟨80447, by rfl⟩ : syracuseStep 429053 = 160895) (by norm_num)
theorem B429077 : Blo 283827 429077 := bbase (se 6 (by rfl) ⟨10056, by rfl⟩ : syracuseStep 429077 = 20113) (by norm_num)
theorem B429101 : Blo 283827 429101 := bbase (se 3 (by rfl) ⟨80456, by rfl⟩ : syracuseStep 429101 = 160913) (by norm_num)
theorem B429125 : Blo 283827 429125 := bbase (se 4 (by rfl) ⟨40230, by rfl⟩ : syracuseStep 429125 = 80461) (by norm_num)
theorem B429149 : Blo 283827 429149 := bbase (se 3 (by rfl) ⟨80465, by rfl⟩ : syracuseStep 429149 = 160931) (by norm_num)
theorem B363629 : Blo 283827 363629 := bbase (se 3 (by rfl) ⟨68180, by rfl⟩ : syracuseStep 363629 = 136361) (by norm_num)
theorem B429173 : Blo 283827 429173 := bbase (se 5 (by rfl) ⟨20117, by rfl⟩ : syracuseStep 429173 = 40235) (by norm_num)
theorem B920693 : Blo 283827 920693 := bbase (se 5 (by rfl) ⟨43157, by rfl⟩ : syracuseStep 920693 = 86315) (by norm_num)
theorem B429197 : Blo 283827 429197 := bbase (se 3 (by rfl) ⟨80474, by rfl⟩ : syracuseStep 429197 = 160949) (by norm_num)
theorem B429221 : Blo 283827 429221 := bbase (se 4 (by rfl) ⟨40239, by rfl⟩ : syracuseStep 429221 = 80479) (by norm_num)
theorem B363685 : Blo 283827 363685 := bbase (se 4 (by rfl) ⟨34095, by rfl⟩ : syracuseStep 363685 = 68191) (by norm_num)
theorem B429245 : Blo 283827 429245 := bbase (se 3 (by rfl) ⟨80483, by rfl⟩ : syracuseStep 429245 = 160967) (by norm_num)
theorem B429269 : Blo 283827 429269 := bbase (se 7 (by rfl) ⟨5030, by rfl⟩ : syracuseStep 429269 = 10061) (by norm_num)
theorem B429293 : Blo 283827 429293 := bbase (se 3 (by rfl) ⟨80492, by rfl⟩ : syracuseStep 429293 = 160985) (by norm_num)
theorem B1084661 : Blo 283827 1084661 := bbase (se 5 (by rfl) ⟨50843, by rfl⟩ : syracuseStep 1084661 = 101687) (by norm_num)
theorem B429317 : Blo 283827 429317 := bbase (se 4 (by rfl) ⟨40248, by rfl⟩ : syracuseStep 429317 = 80497) (by norm_num)
theorem B363781 : Blo 283827 363781 := bbase (se 4 (by rfl) ⟨34104, by rfl⟩ : syracuseStep 363781 = 68209) (by norm_num)
theorem B429341 : Blo 283827 429341 := bbase (se 3 (by rfl) ⟨80501, by rfl⟩ : syracuseStep 429341 = 161003) (by norm_num)
theorem B724261 : Blo 283827 724261 := bbase (se 4 (by rfl) ⟨67899, by rfl⟩ : syracuseStep 724261 = 135799) (by norm_num)
theorem B429365 : Blo 283827 429365 := bbase (se 5 (by rfl) ⟨20126, by rfl⟩ : syracuseStep 429365 = 40253) (by norm_num)
theorem B691517 : Blo 283827 691517 := bbase (se 3 (by rfl) ⟨129659, by rfl⟩ : syracuseStep 691517 = 259319) (by norm_num)
theorem B429389 : Blo 283827 429389 := bbase (se 3 (by rfl) ⟨80510, by rfl⟩ : syracuseStep 429389 = 161021) (by norm_num)
theorem B2166101 : Blo 283827 2166101 := bbase (se 11 (by rfl) ⟨1586, by rfl⟩ : syracuseStep 2166101 = 3173) (by norm_num)
theorem B691541 : Blo 283827 691541 := bbase (se 11 (by rfl) ⟨506, by rfl⟩ : syracuseStep 691541 = 1013) (by norm_num)
theorem B429413 : Blo 283827 429413 := bbase (se 4 (by rfl) ⟨40257, by rfl⟩ : syracuseStep 429413 = 80515) (by norm_num)
theorem B429437 : Blo 283827 429437 := bbase (se 3 (by rfl) ⟨80519, by rfl⟩ : syracuseStep 429437 = 161039) (by norm_num)
theorem B724373 : Blo 283827 724373 := bbase (se 6 (by rfl) ⟨16977, by rfl⟩ : syracuseStep 724373 = 33955) (by norm_num)
theorem B429461 : Blo 283827 429461 := bbase (se 6 (by rfl) ⟨10065, by rfl⟩ : syracuseStep 429461 = 20131) (by norm_num)
theorem B429485 : Blo 283827 429485 := bbase (se 3 (by rfl) ⟨80528, by rfl⟩ : syracuseStep 429485 = 161057) (by norm_num)
theorem B363953 : Blo 283827 363953 := bbase (se 2 (by rfl) ⟨136482, by rfl⟩ : syracuseStep 363953 = 272965) (by norm_num)
theorem B429509 : Blo 283827 429509 := bbase (se 4 (by rfl) ⟨40266, by rfl⟩ : syracuseStep 429509 = 80533) (by norm_num)
theorem B7769557 : Blo 283827 7769557 := bbase (se 7 (by rfl) ⟨91049, by rfl⟩ : syracuseStep 7769557 = 182099) (by norm_num)
theorem B1641941 : Blo 283827 1641941 := bbase (se 7 (by rfl) ⟨19241, by rfl⟩ : syracuseStep 1641941 = 38483) (by norm_num)
theorem B429533 : Blo 283827 429533 := bbase (se 3 (by rfl) ⟨80537, by rfl⟩ : syracuseStep 429533 = 161075) (by norm_num)
theorem B364009 : Blo 283827 364009 := bbase (se 2 (by rfl) ⟨136503, by rfl⟩ : syracuseStep 364009 = 273007) (by norm_num)
theorem B429557 : Blo 283827 429557 := bbase (se 5 (by rfl) ⟨20135, by rfl⟩ : syracuseStep 429557 = 40271) (by norm_num)
theorem B429581 : Blo 283827 429581 := bbase (se 3 (by rfl) ⟨80546, by rfl⟩ : syracuseStep 429581 = 161093) (by norm_num)
theorem B429605 : Blo 283827 429605 := bbase (se 4 (by rfl) ⟨40275, by rfl⟩ : syracuseStep 429605 = 80551) (by norm_num)
theorem B429629 : Blo 283827 429629 := bbase (se 3 (by rfl) ⟨80555, by rfl⟩ : syracuseStep 429629 = 161111) (by norm_num)
theorem B364105 : Blo 283827 364105 := bbase (se 2 (by rfl) ⟨136539, by rfl⟩ : syracuseStep 364105 = 273079) (by norm_num)
theorem B724565 : Blo 283827 724565 := bbase (se 8 (by rfl) ⟨4245, by rfl⟩ : syracuseStep 724565 = 8491) (by norm_num)
theorem B429653 : Blo 283827 429653 := bbase (se 8 (by rfl) ⟨2517, by rfl⟩ : syracuseStep 429653 = 5035) (by norm_num)
theorem B429677 : Blo 283827 429677 := bbase (se 3 (by rfl) ⟨80564, by rfl⟩ : syracuseStep 429677 = 161129) (by norm_num)
theorem B429701 : Blo 283827 429701 := bbase (se 4 (by rfl) ⟨40284, by rfl⟩ : syracuseStep 429701 = 80569) (by norm_num)
theorem B1445525 : Blo 283827 1445525 := bbase (se 6 (by rfl) ⟨33879, by rfl⟩ : syracuseStep 1445525 = 67759) (by norm_num)
theorem B429725 : Blo 283827 429725 := bbase (se 3 (by rfl) ⟨80573, by rfl⟩ : syracuseStep 429725 = 161147) (by norm_num)
theorem B429749 : Blo 283827 429749 := bbase (se 5 (by rfl) ⟨20144, by rfl⟩ : syracuseStep 429749 = 40289) (by norm_num)
theorem B429773 : Blo 283827 429773 := bbase (se 3 (by rfl) ⟨80582, by rfl⟩ : syracuseStep 429773 = 161165) (by norm_num)
theorem B429797 : Blo 283827 429797 := bbase (se 4 (by rfl) ⟨40293, by rfl⟩ : syracuseStep 429797 = 80587) (by norm_num)
theorem B364277 : Blo 283827 364277 := bbase (se 5 (by rfl) ⟨17075, by rfl⟩ : syracuseStep 364277 = 34151) (by norm_num)
theorem B429821 : Blo 283827 429821 := bbase (se 3 (by rfl) ⟨80591, by rfl⟩ : syracuseStep 429821 = 161183) (by norm_num)
theorem B429845 : Blo 283827 429845 := bbase (se 6 (by rfl) ⟨10074, by rfl⟩ : syracuseStep 429845 = 20149) (by norm_num)
theorem B429869 : Blo 283827 429869 := bbase (se 3 (by rfl) ⟨80600, by rfl⟩ : syracuseStep 429869 = 161201) (by norm_num)
theorem B429893 : Blo 283827 429893 := bbase (se 4 (by rfl) ⟨40302, by rfl⟩ : syracuseStep 429893 = 80605) (by norm_num)
theorem B429917 : Blo 283827 429917 := bbase (se 3 (by rfl) ⟨80609, by rfl⟩ : syracuseStep 429917 = 161219) (by norm_num)
theorem B429941 : Blo 283827 429941 := bbase (se 5 (by rfl) ⟨20153, by rfl⟩ : syracuseStep 429941 = 40307) (by norm_num)
theorem B397181 : Blo 283827 397181 := bbase (se 3 (by rfl) ⟨74471, by rfl⟩ : syracuseStep 397181 = 148943) (by norm_num)
theorem B429965 : Blo 283827 429965 := bbase (se 3 (by rfl) ⟨80618, by rfl⟩ : syracuseStep 429965 = 161237) (by norm_num)
theorem B429989 : Blo 283827 429989 := bbase (se 4 (by rfl) ⟨40311, by rfl⟩ : syracuseStep 429989 = 80623) (by norm_num)
theorem B724909 : Blo 283827 724909 := bbase (se 3 (by rfl) ⟨135920, by rfl⟩ : syracuseStep 724909 = 271841) (by norm_num)
theorem B364465 : Blo 283827 364465 := bbase (se 2 (by rfl) ⟨136674, by rfl⟩ : syracuseStep 364465 = 273349) (by norm_num)
theorem B430013 : Blo 283827 430013 := bbase (se 3 (by rfl) ⟨80627, by rfl⟩ : syracuseStep 430013 = 161255) (by norm_num)
theorem B430037 : Blo 283827 430037 := bbase (se 7 (by rfl) ⟨5039, by rfl⟩ : syracuseStep 430037 = 10079) (by norm_num)
theorem B430061 : Blo 283827 430061 := bbase (se 3 (by rfl) ⟨80636, by rfl⟩ : syracuseStep 430061 = 161273) (by norm_num)
theorem B430085 : Blo 283827 430085 := bbase (se 4 (by rfl) ⟨40320, by rfl⟩ : syracuseStep 430085 = 80641) (by norm_num)
theorem B725021 : Blo 283827 725021 := bbase (se 3 (by rfl) ⟨135941, by rfl⟩ : syracuseStep 725021 = 271883) (by norm_num)
theorem B430109 : Blo 283827 430109 := bbase (se 3 (by rfl) ⟨80645, by rfl⟩ : syracuseStep 430109 = 161291) (by norm_num)
theorem B430133 : Blo 283827 430133 := bbase (se 5 (by rfl) ⟨20162, by rfl⟩ : syracuseStep 430133 = 40325) (by norm_num)
theorem B430157 : Blo 283827 430157 := bbase (se 3 (by rfl) ⟨80654, by rfl⟩ : syracuseStep 430157 = 161309) (by norm_num)
theorem B430181 : Blo 283827 430181 := bbase (se 4 (by rfl) ⟨40329, by rfl⟩ : syracuseStep 430181 = 80659) (by norm_num)
theorem B430205 : Blo 283827 430205 := bbase (se 3 (by rfl) ⟨80663, by rfl⟩ : syracuseStep 430205 = 161327) (by norm_num)
theorem B430229 : Blo 283827 430229 := bbase (se 6 (by rfl) ⟨10083, by rfl⟩ : syracuseStep 430229 = 20167) (by norm_num)
theorem B430253 : Blo 283827 430253 := bbase (se 3 (by rfl) ⟨80672, by rfl⟩ : syracuseStep 430253 = 161345) (by norm_num)
theorem B430277 : Blo 283827 430277 := bbase (se 4 (by rfl) ⟨40338, by rfl⟩ : syracuseStep 430277 = 80677) (by norm_num)
theorem B364753 : Blo 283827 364753 := bbase (se 2 (by rfl) ⟨136782, by rfl⟩ : syracuseStep 364753 = 273565) (by norm_num)
theorem B725213 : Blo 283827 725213 := bbase (se 3 (by rfl) ⟨135977, by rfl⟩ : syracuseStep 725213 = 271955) (by norm_num)
theorem B430301 : Blo 283827 430301 := bbase (se 3 (by rfl) ⟨80681, by rfl⟩ : syracuseStep 430301 = 161363) (by norm_num)
theorem B430325 : Blo 283827 430325 := bbase (se 5 (by rfl) ⟨20171, by rfl⟩ : syracuseStep 430325 = 40343) (by norm_num)
theorem B430349 : Blo 283827 430349 := bbase (se 3 (by rfl) ⟨80690, by rfl⟩ : syracuseStep 430349 = 161381) (by norm_num)
theorem B430373 : Blo 283827 430373 := bbase (se 4 (by rfl) ⟨40347, by rfl⟩ : syracuseStep 430373 = 80695) (by norm_num)
theorem B430397 : Blo 283827 430397 := bbase (se 3 (by rfl) ⟨80699, by rfl⟩ : syracuseStep 430397 = 161399) (by norm_num)
theorem B430421 : Blo 283827 430421 := bbase (se 10 (by rfl) ⟨630, by rfl⟩ : syracuseStep 430421 = 1261) (by norm_num)
theorem B430445 : Blo 283827 430445 := bbase (se 3 (by rfl) ⟨80708, by rfl⟩ : syracuseStep 430445 = 161417) (by norm_num)
theorem B430469 : Blo 283827 430469 := bbase (se 4 (by rfl) ⟨40356, by rfl⟩ : syracuseStep 430469 = 80713) (by norm_num)
theorem B1085845 : Blo 283827 1085845 := bbase (se 6 (by rfl) ⟨25449, by rfl⟩ : syracuseStep 1085845 = 50899) (by norm_num)
theorem B430493 : Blo 283827 430493 := bbase (se 3 (by rfl) ⟨80717, by rfl⟩ : syracuseStep 430493 = 161435) (by norm_num)
theorem B430517 : Blo 283827 430517 := bbase (se 5 (by rfl) ⟨20180, by rfl⟩ : syracuseStep 430517 = 40361) (by norm_num)
theorem B430541 : Blo 283827 430541 := bbase (se 3 (by rfl) ⟨80726, by rfl⟩ : syracuseStep 430541 = 161453) (by norm_num)
theorem B430565 : Blo 283827 430565 := bbase (se 4 (by rfl) ⟨40365, by rfl⟩ : syracuseStep 430565 = 80731) (by norm_num)
theorem B430589 : Blo 283827 430589 := bbase (se 3 (by rfl) ⟨80735, by rfl⟩ : syracuseStep 430589 = 161471) (by norm_num)
theorem B430613 : Blo 283827 430613 := bbase (se 6 (by rfl) ⟨10092, by rfl⟩ : syracuseStep 430613 = 20185) (by norm_num)
theorem B430637 : Blo 283827 430637 := bbase (se 3 (by rfl) ⟨80744, by rfl⟩ : syracuseStep 430637 = 161489) (by norm_num)
theorem B725557 : Blo 283827 725557 := bbase (se 5 (by rfl) ⟨34010, by rfl⟩ : syracuseStep 725557 = 68021) (by norm_num)
theorem B430661 : Blo 283827 430661 := bbase (se 4 (by rfl) ⟨40374, by rfl⟩ : syracuseStep 430661 = 80749) (by norm_num)
theorem B430685 : Blo 283827 430685 := bbase (se 3 (by rfl) ⟨80753, by rfl⟩ : syracuseStep 430685 = 161507) (by norm_num)
theorem B430709 : Blo 283827 430709 := bbase (se 5 (by rfl) ⟨20189, by rfl⟩ : syracuseStep 430709 = 40379) (by norm_num)
theorem B430733 : Blo 283827 430733 := bbase (se 3 (by rfl) ⟨80762, by rfl⟩ : syracuseStep 430733 = 161525) (by norm_num)
theorem B725669 : Blo 283827 725669 := bbase (se 4 (by rfl) ⟨68031, by rfl⟩ : syracuseStep 725669 = 136063) (by norm_num)
theorem B430757 : Blo 283827 430757 := bbase (se 4 (by rfl) ⟨40383, by rfl⟩ : syracuseStep 430757 = 80767) (by norm_num)
theorem B2429621 : Blo 283827 2429621 := bbase (se 5 (by rfl) ⟨113888, by rfl⟩ : syracuseStep 2429621 = 227777) (by norm_num)
theorem B430781 : Blo 283827 430781 := bbase (se 3 (by rfl) ⟨80771, by rfl⟩ : syracuseStep 430781 = 161543) (by norm_num)
theorem B1086149 : Blo 283827 1086149 := bbase (se 4 (by rfl) ⟨101826, by rfl⟩ : syracuseStep 1086149 = 203653) (by norm_num)
theorem B430805 : Blo 283827 430805 := bbase (se 7 (by rfl) ⟨5048, by rfl⟩ : syracuseStep 430805 = 10097) (by norm_num)
theorem B430829 : Blo 283827 430829 := bbase (se 3 (by rfl) ⟨80780, by rfl⟩ : syracuseStep 430829 = 161561) (by norm_num)
theorem B430853 : Blo 283827 430853 := bbase (se 4 (by rfl) ⟨40392, by rfl⟩ : syracuseStep 430853 = 80785) (by norm_num)
theorem B430877 : Blo 283827 430877 := bbase (se 3 (by rfl) ⟨80789, by rfl⟩ : syracuseStep 430877 = 161579) (by norm_num)
theorem B430901 : Blo 283827 430901 := bbase (se 5 (by rfl) ⟨20198, by rfl⟩ : syracuseStep 430901 = 40397) (by norm_num)
theorem B430925 : Blo 283827 430925 := bbase (se 3 (by rfl) ⟨80798, by rfl⟩ : syracuseStep 430925 = 161597) (by norm_num)
theorem B8262485 : Blo 283827 8262485 := bbase (se 9 (by rfl) ⟨24206, by rfl⟩ : syracuseStep 8262485 = 48413) (by norm_num)
theorem B725861 : Blo 283827 725861 := bbase (se 4 (by rfl) ⟨68049, by rfl⟩ : syracuseStep 725861 = 136099) (by norm_num)
theorem B430949 : Blo 283827 430949 := bbase (se 4 (by rfl) ⟨40401, by rfl⟩ : syracuseStep 430949 = 80803) (by norm_num)
theorem B430973 : Blo 283827 430973 := bbase (se 3 (by rfl) ⟨80807, by rfl⟩ : syracuseStep 430973 = 161615) (by norm_num)
theorem B430997 : Blo 283827 430997 := bbase (se 6 (by rfl) ⟨10101, by rfl⟩ : syracuseStep 430997 = 20203) (by norm_num)
theorem B1446821 : Blo 283827 1446821 := bbase (se 4 (by rfl) ⟨135639, by rfl⟩ : syracuseStep 1446821 = 271279) (by norm_num)
theorem B431021 : Blo 283827 431021 := bbase (se 3 (by rfl) ⟨80816, by rfl⟩ : syracuseStep 431021 = 161633) (by norm_num)
theorem B431045 : Blo 283827 431045 := bbase (se 4 (by rfl) ⟨40410, by rfl⟩ : syracuseStep 431045 = 80821) (by norm_num)
theorem B1151957 : Blo 283827 1151957 := bbase (se 7 (by rfl) ⟨13499, by rfl⟩ : syracuseStep 1151957 = 26999) (by norm_num)
theorem B431069 : Blo 283827 431069 := bbase (se 3 (by rfl) ⟨80825, by rfl⟩ : syracuseStep 431069 = 161651) (by norm_num)
theorem B431093 : Blo 283827 431093 := bbase (se 5 (by rfl) ⟨20207, by rfl⟩ : syracuseStep 431093 = 40415) (by norm_num)
theorem B431117 : Blo 283827 431117 := bbase (se 3 (by rfl) ⟨80834, by rfl⟩ : syracuseStep 431117 = 161669) (by norm_num)
theorem B431141 : Blo 283827 431141 := bbase (se 4 (by rfl) ⟨40419, by rfl⟩ : syracuseStep 431141 = 80839) (by norm_num)
theorem B431165 : Blo 283827 431165 := bbase (se 3 (by rfl) ⟨80843, by rfl⟩ : syracuseStep 431165 = 161687) (by norm_num)
theorem B693317 : Blo 283827 693317 := bbase (se 4 (by rfl) ⟨64998, by rfl⟩ : syracuseStep 693317 = 129997) (by norm_num)
theorem B431189 : Blo 283827 431189 := bbase (se 8 (by rfl) ⟨2526, by rfl⟩ : syracuseStep 431189 = 5053) (by norm_num)
theorem B431213 : Blo 283827 431213 := bbase (se 3 (by rfl) ⟨80852, by rfl⟩ : syracuseStep 431213 = 161705) (by norm_num)
theorem B431237 : Blo 283827 431237 := bbase (se 4 (by rfl) ⟨40428, by rfl⟩ : syracuseStep 431237 = 80857) (by norm_num)
theorem B431261 : Blo 283827 431261 := bbase (se 3 (by rfl) ⟨80861, by rfl⟩ : syracuseStep 431261 = 161723) (by norm_num)
theorem B431285 : Blo 283827 431285 := bbase (se 5 (by rfl) ⟨20216, by rfl⟩ : syracuseStep 431285 = 40433) (by norm_num)
theorem B726205 : Blo 283827 726205 := bbase (se 3 (by rfl) ⟨136163, by rfl⟩ : syracuseStep 726205 = 272327) (by norm_num)
theorem B431309 : Blo 283827 431309 := bbase (se 3 (by rfl) ⟨80870, by rfl⟩ : syracuseStep 431309 = 161741) (by norm_num)
theorem B1217749 : Blo 283827 1217749 := bbase (se 7 (by rfl) ⟨14270, by rfl⟩ : syracuseStep 1217749 = 28541) (by norm_num)
theorem B431333 : Blo 283827 431333 := bbase (se 4 (by rfl) ⟨40437, by rfl⟩ : syracuseStep 431333 = 80875) (by norm_num)
theorem B431357 : Blo 283827 431357 := bbase (se 3 (by rfl) ⟨80879, by rfl⟩ : syracuseStep 431357 = 161759) (by norm_num)
theorem B1381637 : Blo 283827 1381637 := bbase (se 4 (by rfl) ⟨129528, by rfl⟩ : syracuseStep 1381637 = 259057) (by norm_num)
theorem B431381 : Blo 283827 431381 := bbase (se 6 (by rfl) ⟨10110, by rfl⟩ : syracuseStep 431381 = 20221) (by norm_num)
theorem B726317 : Blo 283827 726317 := bbase (se 3 (by rfl) ⟨136184, by rfl⟩ : syracuseStep 726317 = 272369) (by norm_num)
theorem B431405 : Blo 283827 431405 := bbase (se 3 (by rfl) ⟨80888, by rfl⟩ : syracuseStep 431405 = 161777) (by norm_num)
theorem B431429 : Blo 283827 431429 := bbase (se 4 (by rfl) ⟨40446, by rfl⟩ : syracuseStep 431429 = 80893) (by norm_num)
theorem B431453 : Blo 283827 431453 := bbase (se 3 (by rfl) ⟨80897, by rfl⟩ : syracuseStep 431453 = 161795) (by norm_num)
theorem B431477 : Blo 283827 431477 := bbase (se 5 (by rfl) ⟨20225, by rfl⟩ : syracuseStep 431477 = 40451) (by norm_num)
theorem B431501 : Blo 283827 431501 := bbase (se 3 (by rfl) ⟨80906, by rfl⟩ : syracuseStep 431501 = 161813) (by norm_num)
theorem B431525 : Blo 283827 431525 := bbase (se 4 (by rfl) ⟨40455, by rfl⟩ : syracuseStep 431525 = 80911) (by norm_num)
theorem B431549 : Blo 283827 431549 := bbase (se 3 (by rfl) ⟨80915, by rfl⟩ : syracuseStep 431549 = 161831) (by norm_num)
theorem B431573 : Blo 283827 431573 := bbase (se 7 (by rfl) ⟨5057, by rfl⟩ : syracuseStep 431573 = 10115) (by norm_num)
theorem B726509 : Blo 283827 726509 := bbase (se 3 (by rfl) ⟨136220, by rfl⟩ : syracuseStep 726509 = 272441) (by norm_num)
theorem B431597 : Blo 283827 431597 := bbase (se 3 (by rfl) ⟨80924, by rfl⟩ : syracuseStep 431597 = 161849) (by norm_num)
theorem B431621 : Blo 283827 431621 := bbase (se 4 (by rfl) ⟨40464, by rfl⟩ : syracuseStep 431621 = 80929) (by norm_num)
theorem B431645 : Blo 283827 431645 := bbase (se 3 (by rfl) ⟨80933, by rfl⟩ : syracuseStep 431645 = 161867) (by norm_num)
theorem B431669 : Blo 283827 431669 := bbase (se 5 (by rfl) ⟨20234, by rfl⟩ : syracuseStep 431669 = 40469) (by norm_num)
theorem B661069 : Blo 283827 661069 := bbase (se 3 (by rfl) ⟨123950, by rfl⟩ : syracuseStep 661069 = 247901) (by norm_num)
theorem B431693 : Blo 283827 431693 := bbase (se 3 (by rfl) ⟨80942, by rfl⟩ : syracuseStep 431693 = 161885) (by norm_num)
theorem B431717 : Blo 283827 431717 := bbase (se 4 (by rfl) ⟨40473, by rfl⟩ : syracuseStep 431717 = 80947) (by norm_num)
theorem B431741 : Blo 283827 431741 := bbase (se 3 (by rfl) ⟨80951, by rfl⟩ : syracuseStep 431741 = 161903) (by norm_num)
theorem B726853 : Blo 283827 726853 := bbase (se 4 (by rfl) ⟨68142, by rfl⟩ : syracuseStep 726853 = 136285) (by norm_num)
theorem B726965 : Blo 283827 726965 := bbase (se 5 (by rfl) ⟨34076, by rfl⟩ : syracuseStep 726965 = 68153) (by norm_num)
theorem B2922581 : Blo 283827 2922581 := bbase (se 8 (by rfl) ⟨17124, by rfl⟩ : syracuseStep 2922581 = 34249) (by norm_num)
theorem B727157 : Blo 283827 727157 := bbase (se 5 (by rfl) ⟨34085, by rfl⟩ : syracuseStep 727157 = 68171) (by norm_num)
theorem B1448117 : Blo 283827 1448117 := bbase (se 5 (by rfl) ⟨67880, by rfl⟩ : syracuseStep 1448117 = 135761) (by norm_num)
theorem B432373 : Blo 283827 432373 := bbase (se 5 (by rfl) ⟨20267, by rfl⟩ : syracuseStep 432373 = 40535) (by norm_num)
theorem B989525 : Blo 283827 989525 := bbase (se 10 (by rfl) ⟨1449, by rfl⟩ : syracuseStep 989525 = 2899) (by norm_num)
theorem B727501 : Blo 283827 727501 := bbase (se 3 (by rfl) ⟨136406, by rfl⟩ : syracuseStep 727501 = 272813) (by norm_num)
theorem B727613 : Blo 283827 727613 := bbase (se 3 (by rfl) ⟨136427, by rfl⟩ : syracuseStep 727613 = 272855) (by norm_num)
theorem B367237 : Blo 283827 367237 := bbase (se 4 (by rfl) ⟨34428, by rfl⟩ : syracuseStep 367237 = 68857) (by norm_num)
theorem B531173 : Blo 283827 531173 := bbase (se 4 (by rfl) ⟨49797, by rfl⟩ : syracuseStep 531173 = 99595) (by norm_num)
theorem B727805 : Blo 283827 727805 := bbase (se 3 (by rfl) ⟨136463, by rfl⟩ : syracuseStep 727805 = 272927) (by norm_num)
theorem B1088261 : Blo 283827 1088261 := bbase (se 4 (by rfl) ⟨102024, by rfl⟩ : syracuseStep 1088261 = 204049) (by norm_num)
theorem B1088549 : Blo 283827 1088549 := bbase (se 4 (by rfl) ⟨102051, by rfl⟩ : syracuseStep 1088549 = 204103) (by norm_num)
theorem B367669 : Blo 283827 367669 := bbase (se 5 (by rfl) ⟨17234, by rfl⟩ : syracuseStep 367669 = 34469) (by norm_num)
theorem B728149 : Blo 283827 728149 := bbase (se 8 (by rfl) ⟨4266, by rfl⟩ : syracuseStep 728149 = 8533) (by norm_num)
theorem B1154213 : Blo 283827 1154213 := bbase (se 4 (by rfl) ⟨108207, by rfl⟩ : syracuseStep 1154213 = 216415) (by norm_num)
theorem B2202805 : Blo 283827 2202805 := bbase (se 5 (by rfl) ⟨103256, by rfl⟩ : syracuseStep 2202805 = 206513) (by norm_num)
theorem B728261 : Blo 283827 728261 := bbase (se 4 (by rfl) ⟨68274, by rfl⟩ : syracuseStep 728261 = 136549) (by norm_num)
theorem B1154357 : Blo 283827 1154357 := bbase (se 5 (by rfl) ⟨54110, by rfl⟩ : syracuseStep 1154357 = 108221) (by norm_num)
theorem B728453 : Blo 283827 728453 := bbase (se 4 (by rfl) ⟨68292, by rfl⟩ : syracuseStep 728453 = 136585) (by norm_num)
theorem B1449413 : Blo 283827 1449413 := bbase (se 4 (by rfl) ⟨135882, by rfl⟩ : syracuseStep 1449413 = 271765) (by norm_num)
theorem B499469 : Blo 283827 499469 := bbase (se 3 (by rfl) ⟨93650, by rfl⟩ : syracuseStep 499469 = 187301) (by norm_num)
theorem B958229 : Blo 283827 958229 := bbase (se 6 (by rfl) ⟨22458, by rfl⟩ : syracuseStep 958229 = 44917) (by norm_num)
theorem B368653 : Blo 283827 368653 := bbase (se 3 (by rfl) ⟨69122, by rfl⟩ : syracuseStep 368653 = 138245) (by norm_num)
theorem B434197 : Blo 283827 434197 := bbase (se 6 (by rfl) ⟨10176, by rfl⟩ : syracuseStep 434197 = 20353) (by norm_num)
theorem B696397 : Blo 283827 696397 := bbase (se 3 (by rfl) ⟨130574, by rfl⟩ : syracuseStep 696397 = 261149) (by norm_num)
theorem B1220741 : Blo 283827 1220741 := bbase (se 4 (by rfl) ⟨114444, by rfl⟩ : syracuseStep 1220741 = 228889) (by norm_num)
theorem B958661 : Blo 283827 958661 := bbase (se 4 (by rfl) ⟨89874, by rfl⟩ : syracuseStep 958661 = 179749) (by norm_num)
theorem B1089733 : Blo 283827 1089733 := bbase (se 4 (by rfl) ⟨102162, by rfl⟩ : syracuseStep 1089733 = 204325) (by norm_num)
theorem B4923605 : Blo 283827 4923605 := bbase (se 7 (by rfl) ⟨57698, by rfl⟩ : syracuseStep 4923605 = 115397) (by norm_num)
theorem B303421 : Blo 283827 303421 := bbase (se 3 (by rfl) ⟨56891, by rfl⟩ : syracuseStep 303421 = 113783) (by norm_num)
theorem B303545 : Blo 283827 303545 := bbase (se 2 (by rfl) ⟨113829, by rfl⟩ : syracuseStep 303545 = 227659) (by norm_num)
theorem B1090037 : Blo 283827 1090037 := bbase (se 5 (by rfl) ⟨51095, by rfl⟩ : syracuseStep 1090037 = 102191) (by norm_num)
theorem B959093 : Blo 283827 959093 := bbase (se 5 (by rfl) ⟨44957, by rfl⟩ : syracuseStep 959093 = 89915) (by norm_num)
theorem B303797 : Blo 283827 303797 := bbase (se 5 (by rfl) ⟨14240, by rfl⟩ : syracuseStep 303797 = 28481) (by norm_num)
theorem B1450709 : Blo 283827 1450709 := bbase (se 7 (by rfl) ⟨17000, by rfl⟩ : syracuseStep 1450709 = 34001) (by norm_num)
theorem B959525 : Blo 283827 959525 := bbase (se 4 (by rfl) ⟨89955, by rfl⟩ : syracuseStep 959525 = 179911) (by norm_num)
theorem B5022805 : Blo 283827 5022805 := bbase (se 8 (by rfl) ⟨29430, by rfl⟩ : syracuseStep 5022805 = 58861) (by norm_num)
theorem B304241 : Blo 283827 304241 := bbase (se 2 (by rfl) ⟨114090, by rfl⟩ : syracuseStep 304241 = 228181) (by norm_num)
theorem B1221749 : Blo 283827 1221749 := bbase (se 5 (by rfl) ⟨57269, by rfl⟩ : syracuseStep 1221749 = 114539) (by norm_num)
theorem B435413 : Blo 283827 435413 := bbase (se 7 (by rfl) ⟨5102, by rfl⟩ : syracuseStep 435413 = 10205) (by norm_num)
theorem B304489 : Blo 283827 304489 := bbase (se 2 (by rfl) ⟨114183, by rfl⟩ : syracuseStep 304489 = 228367) (by norm_num)
theorem B959957 : Blo 283827 959957 := bbase (se 7 (by rfl) ⟨11249, by rfl⟩ : syracuseStep 959957 = 22499) (by norm_num)
theorem B435701 : Blo 283827 435701 := bbase (se 5 (by rfl) ⟨20423, by rfl⟩ : syracuseStep 435701 = 40847) (by norm_num)
theorem B1746517 : Blo 283827 1746517 := bbase (se 8 (by rfl) ⟨10233, by rfl⟩ : syracuseStep 1746517 = 20467) (by norm_num)
theorem B370273 : Blo 283827 370273 := bbase (se 2 (by rfl) ⟨138852, by rfl⟩ : syracuseStep 370273 = 277705) (by norm_num)
theorem B304933 : Blo 283827 304933 := bbase (se 4 (by rfl) ⟨28587, by rfl⟩ : syracuseStep 304933 = 57175) (by norm_num)
theorem B304993 : Blo 283827 304993 := bbase (se 2 (by rfl) ⟨114372, by rfl⟩ : syracuseStep 304993 = 228745) (by norm_num)
theorem B960389 : Blo 283827 960389 := bbase (se 4 (by rfl) ⟨90036, by rfl⟩ : syracuseStep 960389 = 180073) (by norm_num)
theorem B1452005 : Blo 283827 1452005 := bbase (se 4 (by rfl) ⟨136125, by rfl⟩ : syracuseStep 1452005 = 272251) (by norm_num)
theorem B305309 : Blo 283827 305309 := bbase (se 3 (by rfl) ⟨57245, by rfl⟩ : syracuseStep 305309 = 114491) (by norm_num)
theorem B960821 : Blo 283827 960821 := bbase (se 5 (by rfl) ⟨45038, by rfl⟩ : syracuseStep 960821 = 90077) (by norm_num)
theorem B1092149 : Blo 283827 1092149 := bbase (se 5 (by rfl) ⟨51194, by rfl⟩ : syracuseStep 1092149 = 102389) (by norm_num)
theorem B305753 : Blo 283827 305753 := bbase (se 2 (by rfl) ⟨114657, by rfl⟩ : syracuseStep 305753 = 229315) (by norm_num)
theorem B305813 : Blo 283827 305813 := bbase (se 6 (by rfl) ⟨7167, by rfl⟩ : syracuseStep 305813 = 14335) (by norm_num)
theorem B961253 : Blo 283827 961253 := bbase (se 4 (by rfl) ⟨90117, by rfl⟩ : syracuseStep 961253 = 180235) (by norm_num)
theorem B305941 : Blo 283827 305941 := bbase (se 6 (by rfl) ⟨7170, by rfl⟩ : syracuseStep 305941 = 14341) (by norm_num)
theorem B1092437 : Blo 283827 1092437 := bbase (se 9 (by rfl) ⟨3200, by rfl⟩ : syracuseStep 1092437 = 6401) (by norm_num)
theorem B1223525 : Blo 283827 1223525 := bbase (se 4 (by rfl) ⟨114705, by rfl⟩ : syracuseStep 1223525 = 229411) (by norm_num)
theorem B2173877 : Blo 283827 2173877 := bbase (se 5 (by rfl) ⟨101900, by rfl⟩ : syracuseStep 2173877 = 203801) (by norm_num)
theorem B666557 : Blo 283827 666557 := bbase (se 3 (by rfl) ⟨124979, by rfl⟩ : syracuseStep 666557 = 249959) (by norm_num)
theorem B404453 : Blo 283827 404453 := bbase (se 4 (by rfl) ⟨37917, by rfl⟩ : syracuseStep 404453 = 75835) (by norm_num)
theorem B928741 : Blo 283827 928741 := bbase (se 4 (by rfl) ⟨87069, by rfl⟩ : syracuseStep 928741 = 174139) (by norm_num)
theorem B961685 : Blo 283827 961685 := bbase (se 6 (by rfl) ⟨22539, by rfl⟩ : syracuseStep 961685 = 45079) (by norm_num)
theorem B306385 : Blo 283827 306385 := bbase (se 2 (by rfl) ⟨114894, by rfl⟩ : syracuseStep 306385 = 229789) (by norm_num)
theorem B1453301 : Blo 283827 1453301 := bbase (se 5 (by rfl) ⟨68123, by rfl⟩ : syracuseStep 1453301 = 136247) (by norm_num)
theorem B306505 : Blo 283827 306505 := bbase (se 2 (by rfl) ⟨114939, by rfl⟩ : syracuseStep 306505 = 229879) (by norm_num)
theorem B699781 : Blo 283827 699781 := bbase (se 4 (by rfl) ⟨65604, by rfl⟩ : syracuseStep 699781 = 131209) (by norm_num)
theorem B405005 : Blo 283827 405005 := bbase (se 3 (by rfl) ⟨75938, by rfl⟩ : syracuseStep 405005 = 151877) (by norm_num)
theorem B962117 : Blo 283827 962117 := bbase (se 4 (by rfl) ⟨90198, by rfl⟩ : syracuseStep 962117 = 180397) (by norm_num)
theorem B306757 : Blo 283827 306757 := bbase (se 4 (by rfl) ⟨28758, by rfl⟩ : syracuseStep 306757 = 57517) (by norm_num)
theorem B306761 : Blo 283827 306761 := bbase (se 2 (by rfl) ⟨115035, by rfl⟩ : syracuseStep 306761 = 230071) (by norm_num)
theorem B1027765 : Blo 283827 1027765 := bbase (se 5 (by rfl) ⟨48176, by rfl⟩ : syracuseStep 1027765 = 96353) (by norm_num)
theorem B962549 : Blo 283827 962549 := bbase (se 5 (by rfl) ⟨45119, by rfl⟩ : syracuseStep 962549 = 90239) (by norm_num)
theorem B307325 : Blo 283827 307325 := bbase (se 3 (by rfl) ⟨57623, by rfl⟩ : syracuseStep 307325 = 115247) (by norm_num)
theorem B405757 : Blo 283827 405757 := bbase (se 3 (by rfl) ⟨76079, by rfl⟩ : syracuseStep 405757 = 152159) (by norm_num)
theorem B962981 : Blo 283827 962981 := bbase (se 4 (by rfl) ⟨90279, by rfl⟩ : syracuseStep 962981 = 180559) (by norm_num)
theorem B1454597 : Blo 283827 1454597 := bbase (se 4 (by rfl) ⟨136368, by rfl⟩ : syracuseStep 1454597 = 272737) (by norm_num)
theorem B2437685 : Blo 283827 2437685 := bbase (se 5 (by rfl) ⟨114266, by rfl⟩ : syracuseStep 2437685 = 228533) (by norm_num)
theorem B963413 : Blo 283827 963413 := bbase (se 9 (by rfl) ⟨2822, by rfl⟩ : syracuseStep 963413 = 5645) (by norm_num)
theorem B425981 : Blo 283827 425981 := bbase (se 3 (by rfl) ⟨79871, by rfl⟩ : syracuseStep 425981 = 159743) (by norm_num)
theorem B832501 : Blo 283827 832501 := bbase (se 5 (by rfl) ⟨39023, by rfl⟩ : syracuseStep 832501 = 78047) (by norm_num)
theorem B340993 : Blo 283827 340993 := bbase (se 2 (by rfl) ⟨127872, by rfl⟩ : syracuseStep 340993 = 255745) (by norm_num)
theorem B406549 : Blo 283827 406549 := bbase (se 6 (by rfl) ⟨9528, by rfl⟩ : syracuseStep 406549 = 19057) (by norm_num)
theorem B963845 : Blo 283827 963845 := bbase (se 4 (by rfl) ⟨90360, by rfl⟩ : syracuseStep 963845 = 180721) (by norm_num)
theorem B865637 : Blo 283827 865637 := bbase (se 4 (by rfl) ⟨81153, by rfl⟩ : syracuseStep 865637 = 162307) (by norm_num)
theorem B406885 : Blo 283827 406885 := bbase (se 4 (by rfl) ⟨38145, by rfl⟩ : syracuseStep 406885 = 76291) (by norm_num)
theorem B1095029 : Blo 283827 1095029 := bbase (se 5 (by rfl) ⟨51329, by rfl⟩ : syracuseStep 1095029 = 102659) (by norm_num)
theorem B341377 : Blo 283827 341377 := bbase (se 2 (by rfl) ⟨128016, by rfl⟩ : syracuseStep 341377 = 256033) (by norm_num)
theorem B407101 : Blo 283827 407101 := bbase (se 3 (by rfl) ⟨76331, by rfl⟩ : syracuseStep 407101 = 152663) (by norm_num)
theorem B964277 : Blo 283827 964277 := bbase (se 5 (by rfl) ⟨45200, by rfl⟩ : syracuseStep 964277 = 90401) (by norm_num)
theorem B1455893 : Blo 283827 1455893 := bbase (se 6 (by rfl) ⟨34122, by rfl⟩ : syracuseStep 1455893 = 68245) (by norm_num)
theorem B407477 : Blo 283827 407477 := bbase (se 5 (by rfl) ⟨19100, by rfl⟩ : syracuseStep 407477 = 38201) (by norm_num)
theorem B964709 : Blo 283827 964709 := bbase (se 4 (by rfl) ⟨90441, by rfl⟩ : syracuseStep 964709 = 180883) (by norm_num)
theorem B1161605 : Blo 283827 1161605 := bbase (se 4 (by rfl) ⟨108900, by rfl⟩ : syracuseStep 1161605 = 217801) (by norm_num)
theorem B342425 : Blo 283827 342425 := bbase (se 2 (by rfl) ⟨128409, by rfl⟩ : syracuseStep 342425 = 256819) (by norm_num)
theorem B539149 : Blo 283827 539149 := bbase (se 3 (by rfl) ⟨101090, by rfl⟩ : syracuseStep 539149 = 202181) (by norm_num)
theorem B965141 : Blo 283827 965141 := bbase (se 6 (by rfl) ⟨22620, by rfl⟩ : syracuseStep 965141 = 45241) (by norm_num)
theorem B539293 : Blo 283827 539293 := bbase (se 3 (by rfl) ⟨101117, by rfl⟩ : syracuseStep 539293 = 202235) (by norm_num)
theorem B342733 : Blo 283827 342733 := bbase (se 3 (by rfl) ⟨64262, by rfl⟩ : syracuseStep 342733 = 128525) (by norm_num)
theorem B342761 : Blo 283827 342761 := bbase (se 2 (by rfl) ⟨128535, by rfl⟩ : syracuseStep 342761 = 257071) (by norm_num)
theorem B539453 : Blo 283827 539453 := bbase (se 3 (by rfl) ⟨101147, by rfl⟩ : syracuseStep 539453 = 202295) (by norm_num)
theorem B1096597 : Blo 283827 1096597 := bbase (se 6 (by rfl) ⟨25701, by rfl⟩ : syracuseStep 1096597 = 51403) (by norm_num)
theorem B965573 : Blo 283827 965573 := bbase (se 4 (by rfl) ⟨90522, by rfl⟩ : syracuseStep 965573 = 181045) (by norm_num)
theorem B539597 : Blo 283827 539597 := bbase (se 3 (by rfl) ⟨101174, by rfl⟩ : syracuseStep 539597 = 202349) (by norm_num)
theorem B1653749 : Blo 283827 1653749 := bbase (se 5 (by rfl) ⟨77519, by rfl⟩ : syracuseStep 1653749 = 155039) (by norm_num)
theorem B1227797 : Blo 283827 1227797 := bbase (se 6 (by rfl) ⟨28776, by rfl⟩ : syracuseStep 1227797 = 57553) (by norm_num)
theorem B1621205 : Blo 283827 1621205 := bbase (se 7 (by rfl) ⟨18998, by rfl⟩ : syracuseStep 1621205 = 37997) (by norm_num)
theorem B343261 : Blo 283827 343261 := bbase (se 3 (by rfl) ⟨64361, by rfl⟩ : syracuseStep 343261 = 128723) (by norm_num)
theorem B539885 : Blo 283827 539885 := bbase (se 3 (by rfl) ⟨101228, by rfl⟩ : syracuseStep 539885 = 202457) (by norm_num)
theorem B408901 : Blo 283827 408901 := bbase (se 4 (by rfl) ⟨38334, by rfl⟩ : syracuseStep 408901 = 76669) (by norm_num)
theorem B736589 : Blo 283827 736589 := bbase (se 3 (by rfl) ⟨138110, by rfl⟩ : syracuseStep 736589 = 276221) (by norm_num)
theorem B966005 : Blo 283827 966005 := bbase (se 5 (by rfl) ⟨45281, by rfl⟩ : syracuseStep 966005 = 90563) (by norm_num)
theorem B540037 : Blo 283827 540037 := bbase (se 4 (by rfl) ⟨50628, by rfl⟩ : syracuseStep 540037 = 101257) (by norm_num)
theorem B638621 : Blo 283827 638621 := bbase (se 3 (by rfl) ⟨119741, by rfl⟩ : syracuseStep 638621 = 239483) (by norm_num)
theorem B540341 : Blo 283827 540341 := bbase (se 5 (by rfl) ⟨25328, by rfl⟩ : syracuseStep 540341 = 50657) (by norm_num)
theorem B638693 : Blo 283827 638693 := bbase (se 4 (by rfl) ⟨59877, by rfl⟩ : syracuseStep 638693 = 119755) (by norm_num)
theorem B769765 : Blo 283827 769765 := bbase (se 4 (by rfl) ⟨72165, by rfl⟩ : syracuseStep 769765 = 144331) (by norm_num)
theorem B966437 : Blo 283827 966437 := bbase (se 4 (by rfl) ⟨90603, by rfl⟩ : syracuseStep 966437 = 181207) (by norm_num)
theorem B638765 : Blo 283827 638765 := bbase (se 3 (by rfl) ⟨119768, by rfl⟩ : syracuseStep 638765 = 239537) (by norm_num)
theorem B638837 : Blo 283827 638837 := bbase (se 5 (by rfl) ⟨29945, by rfl⟩ : syracuseStep 638837 = 59891) (by norm_num)
theorem B409493 : Blo 283827 409493 := bbase (se 6 (by rfl) ⟨9597, by rfl⟩ : syracuseStep 409493 = 19195) (by norm_num)
theorem B638909 : Blo 283827 638909 := bbase (se 3 (by rfl) ⟨119795, by rfl⟩ : syracuseStep 638909 = 239591) (by norm_num)
theorem B409573 : Blo 283827 409573 := bbase (se 4 (by rfl) ⟨38397, by rfl⟩ : syracuseStep 409573 = 76795) (by norm_num)
theorem B638981 : Blo 283827 638981 := bbase (se 4 (by rfl) ⟨59904, by rfl⟩ : syracuseStep 638981 = 119809) (by norm_num)
theorem B639053 : Blo 283827 639053 := bbase (se 3 (by rfl) ⟨119822, by rfl⟩ : syracuseStep 639053 = 239645) (by norm_num)
theorem B409693 : Blo 283827 409693 := bbase (se 3 (by rfl) ⟨76817, by rfl⟩ : syracuseStep 409693 = 153635) (by norm_num)
theorem B639125 : Blo 283827 639125 := bbase (se 6 (by rfl) ⟨14979, by rfl⟩ : syracuseStep 639125 = 29959) (by norm_num)
theorem B409789 : Blo 283827 409789 := bbase (se 3 (by rfl) ⟨76835, by rfl⟩ : syracuseStep 409789 = 153671) (by norm_num)
theorem B966869 : Blo 283827 966869 := bbase (se 7 (by rfl) ⟨11330, by rfl⟩ : syracuseStep 966869 = 22661) (by norm_num)
theorem B639197 : Blo 283827 639197 := bbase (se 3 (by rfl) ⟨119849, by rfl⟩ : syracuseStep 639197 = 239699) (by norm_num)
theorem B639269 : Blo 283827 639269 := bbase (se 4 (by rfl) ⟨59931, by rfl⟩ : syracuseStep 639269 = 119863) (by norm_num)
theorem B639341 : Blo 283827 639341 := bbase (se 3 (by rfl) ⟨119876, by rfl⟩ : syracuseStep 639341 = 239753) (by norm_num)
theorem B1622389 : Blo 283827 1622389 := bbase (se 5 (by rfl) ⟨76049, by rfl⟩ : syracuseStep 1622389 = 152099) (by norm_num)
theorem B344449 : Blo 283827 344449 := bbase (se 2 (by rfl) ⟨129168, by rfl⟩ : syracuseStep 344449 = 258337) (by norm_num)
theorem B541093 : Blo 283827 541093 := bbase (se 4 (by rfl) ⟨50727, by rfl⟩ : syracuseStep 541093 = 101455) (by norm_num)
theorem B639413 : Blo 283827 639413 := bbase (se 5 (by rfl) ⟨29972, by rfl⟩ : syracuseStep 639413 = 59945) (by norm_num)
theorem B639485 : Blo 283827 639485 := bbase (se 3 (by rfl) ⟨119903, by rfl⟩ : syracuseStep 639485 = 239807) (by norm_num)
theorem B541237 : Blo 283827 541237 := bbase (se 5 (by rfl) ⟨25370, by rfl⟩ : syracuseStep 541237 = 50741) (by norm_num)
theorem B344641 : Blo 283827 344641 := bbase (se 2 (by rfl) ⟨129240, by rfl⟩ : syracuseStep 344641 = 258481) (by norm_num)
theorem B639557 : Blo 283827 639557 := bbase (se 4 (by rfl) ⟨59958, by rfl⟩ : syracuseStep 639557 = 119917) (by norm_num)
theorem B1163861 : Blo 283827 1163861 := bbase (se 8 (by rfl) ⟨6819, by rfl⟩ : syracuseStep 1163861 = 13639) (by norm_num)
theorem B967301 : Blo 283827 967301 := bbase (se 4 (by rfl) ⟨90684, by rfl⟩ : syracuseStep 967301 = 181369) (by norm_num)
theorem B639629 : Blo 283827 639629 := bbase (se 3 (by rfl) ⟨119930, by rfl⟩ : syracuseStep 639629 = 239861) (by norm_num)
theorem B344741 : Blo 283827 344741 := bbase (se 4 (by rfl) ⟨32319, by rfl⟩ : syracuseStep 344741 = 64639) (by norm_num)
theorem B639701 : Blo 283827 639701 := bbase (se 7 (by rfl) ⟨7496, by rfl⟩ : syracuseStep 639701 = 14993) (by norm_num)
theorem B541397 : Blo 283827 541397 := bbase (se 7 (by rfl) ⟨6344, by rfl⟩ : syracuseStep 541397 = 12689) (by norm_num)
theorem B639773 : Blo 283827 639773 := bbase (se 3 (by rfl) ⟨119957, by rfl⟩ : syracuseStep 639773 = 239915) (by norm_num)
theorem B1033013 : Blo 283827 1033013 := bbase (se 5 (by rfl) ⟨48422, by rfl⟩ : syracuseStep 1033013 = 96845) (by norm_num)
theorem B4146005 : Blo 283827 4146005 := bbase (se 9 (by rfl) ⟨12146, by rfl⟩ : syracuseStep 4146005 = 24293) (by norm_num)
theorem B639845 : Blo 283827 639845 := bbase (se 4 (by rfl) ⟨59985, by rfl⟩ : syracuseStep 639845 = 119971) (by norm_num)
theorem B541541 : Blo 283827 541541 := bbase (se 4 (by rfl) ⟨50769, by rfl⟩ : syracuseStep 541541 = 101539) (by norm_num)
theorem B639917 : Blo 283827 639917 := bbase (se 3 (by rfl) ⟨119984, by rfl⟩ : syracuseStep 639917 = 239969) (by norm_num)
theorem B1098677 : Blo 283827 1098677 := bbase (se 5 (by rfl) ⟨51500, by rfl⟩ : syracuseStep 1098677 = 103001) (by norm_num)
theorem B639989 : Blo 283827 639989 := bbase (se 5 (by rfl) ⟨29999, by rfl⟩ : syracuseStep 639989 = 59999) (by norm_num)
theorem B967733 : Blo 283827 967733 := bbase (se 5 (by rfl) ⟨45362, by rfl⟩ : syracuseStep 967733 = 90725) (by norm_num)
theorem B640061 : Blo 283827 640061 := bbase (se 3 (by rfl) ⟨120011, by rfl⟩ : syracuseStep 640061 = 240023) (by norm_num)
theorem B640133 : Blo 283827 640133 := bbase (se 4 (by rfl) ⟨60012, by rfl⟩ : syracuseStep 640133 = 120025) (by norm_num)
theorem B541829 : Blo 283827 541829 := bbase (se 4 (by rfl) ⟨50796, by rfl⟩ : syracuseStep 541829 = 101593) (by norm_num)
theorem B640205 : Blo 283827 640205 := bbase (se 3 (by rfl) ⟨120038, by rfl⟩ : syracuseStep 640205 = 240077) (by norm_num)
theorem B640277 : Blo 283827 640277 := bbase (se 6 (by rfl) ⟨15006, by rfl⟩ : syracuseStep 640277 = 30013) (by norm_num)
theorem B541981 : Blo 283827 541981 := bbase (se 3 (by rfl) ⟨101621, by rfl⟩ : syracuseStep 541981 = 203243) (by norm_num)
theorem B640349 : Blo 283827 640349 := bbase (se 3 (by rfl) ⟨120065, by rfl⟩ : syracuseStep 640349 = 240131) (by norm_num)
theorem B607637 : Blo 283827 607637 := bbase (se 6 (by rfl) ⟨14241, by rfl⟩ : syracuseStep 607637 = 28483) (by norm_num)
theorem B640421 : Blo 283827 640421 := bbase (se 4 (by rfl) ⟨60039, by rfl⟩ : syracuseStep 640421 = 120079) (by norm_num)
theorem B345529 : Blo 283827 345529 := bbase (se 2 (by rfl) ⟨129573, by rfl⟩ : syracuseStep 345529 = 259147) (by norm_num)
theorem B1394117 : Blo 283827 1394117 := bbase (se 4 (by rfl) ⟨130698, by rfl⟩ : syracuseStep 1394117 = 261397) (by norm_num)
theorem B968165 : Blo 283827 968165 := bbase (se 4 (by rfl) ⟨90765, by rfl⟩ : syracuseStep 968165 = 181531) (by norm_num)
theorem B640493 : Blo 283827 640493 := bbase (se 3 (by rfl) ⟨120092, by rfl⟩ : syracuseStep 640493 = 240185) (by norm_num)
theorem B607781 : Blo 283827 607781 := bbase (se 4 (by rfl) ⟨56979, by rfl⟩ : syracuseStep 607781 = 113959) (by norm_num)
theorem B640565 : Blo 283827 640565 := bbase (se 5 (by rfl) ⟨30026, by rfl⟩ : syracuseStep 640565 = 60053) (by norm_num)
theorem B542285 : Blo 283827 542285 := bbase (se 3 (by rfl) ⟨101678, by rfl⟩ : syracuseStep 542285 = 203357) (by norm_num)
theorem B640637 : Blo 283827 640637 := bbase (se 3 (by rfl) ⟨120119, by rfl⟩ : syracuseStep 640637 = 240239) (by norm_num)
theorem B640709 : Blo 283827 640709 := bbase (se 4 (by rfl) ⟨60066, by rfl⟩ : syracuseStep 640709 = 120133) (by norm_num)
theorem B640781 : Blo 283827 640781 := bbase (se 3 (by rfl) ⟨120146, by rfl⟩ : syracuseStep 640781 = 240293) (by norm_num)
theorem B640853 : Blo 283827 640853 := bbase (se 9 (by rfl) ⟨1877, by rfl⟩ : syracuseStep 640853 = 3755) (by norm_num)
theorem B608141 : Blo 283827 608141 := bbase (se 3 (by rfl) ⟨114026, by rfl⟩ : syracuseStep 608141 = 228053) (by norm_num)
theorem B968597 : Blo 283827 968597 := bbase (se 6 (by rfl) ⟨22701, by rfl⟩ : syracuseStep 968597 = 45403) (by norm_num)
theorem B640925 : Blo 283827 640925 := bbase (se 3 (by rfl) ⟨120173, by rfl⟩ : syracuseStep 640925 = 240347) (by norm_num)
theorem B640997 : Blo 283827 640997 := bbase (se 4 (by rfl) ⟨60093, by rfl⟩ : syracuseStep 640997 = 120187) (by norm_num)
theorem B4769813 : Blo 283827 4769813 := bbase (se 6 (by rfl) ⟨111792, by rfl⟩ : syracuseStep 4769813 = 223585) (by norm_num)
theorem B641069 : Blo 283827 641069 := bbase (se 3 (by rfl) ⟨120200, by rfl⟩ : syracuseStep 641069 = 240401) (by norm_num)
theorem B313453 : Blo 283827 313453 := bbase (se 3 (by rfl) ⟨58772, by rfl⟩ : syracuseStep 313453 = 117545) (by norm_num)
theorem B641141 : Blo 283827 641141 := bbase (se 5 (by rfl) ⟨30053, by rfl⟩ : syracuseStep 641141 = 60107) (by norm_num)
theorem B641213 : Blo 283827 641213 := bbase (se 3 (by rfl) ⟨120227, by rfl⟩ : syracuseStep 641213 = 240455) (by norm_num)
theorem B641285 : Blo 283827 641285 := bbase (se 4 (by rfl) ⟨60120, by rfl⟩ : syracuseStep 641285 = 120241) (by norm_num)
theorem B1624373 : Blo 283827 1624373 := bbase (se 5 (by rfl) ⟨76142, by rfl⟩ : syracuseStep 1624373 = 152285) (by norm_num)
theorem B543037 : Blo 283827 543037 := bbase (se 3 (by rfl) ⟨101819, by rfl⟩ : syracuseStep 543037 = 203639) (by norm_num)
theorem B969029 : Blo 283827 969029 := bbase (se 4 (by rfl) ⟨90846, by rfl⟩ : syracuseStep 969029 = 181693) (by norm_num)
theorem B641357 : Blo 283827 641357 := bbase (se 3 (by rfl) ⟨120254, by rfl⟩ : syracuseStep 641357 = 240509) (by norm_num)
theorem B641429 : Blo 283827 641429 := bbase (se 6 (by rfl) ⟨15033, by rfl⟩ : syracuseStep 641429 = 30067) (by norm_num)
theorem B543181 : Blo 283827 543181 := bbase (se 3 (by rfl) ⟨101846, by rfl⟩ : syracuseStep 543181 = 203693) (by norm_num)
theorem B641501 : Blo 283827 641501 := bbase (se 3 (by rfl) ⟨120281, by rfl⟩ : syracuseStep 641501 = 240563) (by norm_num)
theorem B2181653 : Blo 283827 2181653 := bbase (se 6 (by rfl) ⟨51132, by rfl⟩ : syracuseStep 2181653 = 102265) (by norm_num)
theorem B641573 : Blo 283827 641573 := bbase (se 4 (by rfl) ⟨60147, by rfl⟩ : syracuseStep 641573 = 120295) (by norm_num)
theorem B11061845 : Blo 283827 11061845 := bbase (se 8 (by rfl) ⟨64815, by rfl⟩ : syracuseStep 11061845 = 129631) (by norm_num)
theorem B641645 : Blo 283827 641645 := bbase (se 3 (by rfl) ⟨120308, by rfl⟩ : syracuseStep 641645 = 240617) (by norm_num)
theorem B543341 : Blo 283827 543341 := bbase (se 3 (by rfl) ⟨101876, by rfl⟩ : syracuseStep 543341 = 203753) (by norm_num)
theorem B641717 : Blo 283827 641717 := bbase (se 5 (by rfl) ⟨30080, by rfl⟩ : syracuseStep 641717 = 60161) (by norm_num)
theorem B1166021 : Blo 283827 1166021 := bbase (se 4 (by rfl) ⟨109314, by rfl⟩ : syracuseStep 1166021 = 218629) (by norm_num)
theorem B969461 : Blo 283827 969461 := bbase (se 5 (by rfl) ⟨45443, by rfl⟩ : syracuseStep 969461 = 90887) (by norm_num)
theorem B641789 : Blo 283827 641789 := bbase (se 3 (by rfl) ⟨120335, by rfl⟩ : syracuseStep 641789 = 240671) (by norm_num)
theorem B543485 : Blo 283827 543485 := bbase (se 3 (by rfl) ⟨101903, by rfl⟩ : syracuseStep 543485 = 203807) (by norm_num)
theorem B609029 : Blo 283827 609029 := bbase (se 4 (by rfl) ⟨57096, by rfl⟩ : syracuseStep 609029 = 114193) (by norm_num)
theorem B641861 : Blo 283827 641861 := bbase (se 4 (by rfl) ⟨60174, by rfl⟩ : syracuseStep 641861 = 120349) (by norm_num)
theorem B641933 : Blo 283827 641933 := bbase (se 3 (by rfl) ⟨120362, by rfl⟩ : syracuseStep 641933 = 240725) (by norm_num)
theorem B642005 : Blo 283827 642005 := bbase (se 7 (by rfl) ⟨7523, by rfl⟩ : syracuseStep 642005 = 15047) (by norm_num)
theorem B2870261 : Blo 283827 2870261 := bbase (se 5 (by rfl) ⟨134543, by rfl⟩ : syracuseStep 2870261 = 269087) (by norm_num)
theorem B609277 : Blo 283827 609277 := bbase (se 3 (by rfl) ⟨114239, by rfl⟩ : syracuseStep 609277 = 228479) (by norm_num)
theorem B642077 : Blo 283827 642077 := bbase (se 3 (by rfl) ⟨120389, by rfl⟩ : syracuseStep 642077 = 240779) (by norm_num)
theorem B543773 : Blo 283827 543773 := bbase (se 3 (by rfl) ⟨101957, by rfl⟩ : syracuseStep 543773 = 203915) (by norm_num)
theorem B642149 : Blo 283827 642149 := bbase (se 4 (by rfl) ⟨60201, by rfl⟩ : syracuseStep 642149 = 120403) (by norm_num)
theorem B969893 : Blo 283827 969893 := bbase (se 4 (by rfl) ⟨90927, by rfl⟩ : syracuseStep 969893 = 181855) (by norm_num)
theorem B642221 : Blo 283827 642221 := bbase (se 3 (by rfl) ⟨120416, by rfl⟩ : syracuseStep 642221 = 240833) (by norm_num)
theorem B543925 : Blo 283827 543925 := bbase (se 5 (by rfl) ⟨25496, by rfl⟩ : syracuseStep 543925 = 50993) (by norm_num)
theorem B642293 : Blo 283827 642293 := bbase (se 5 (by rfl) ⟨30107, by rfl⟩ : syracuseStep 642293 = 60215) (by norm_num)
theorem B642325 : Blo 283827 642325 := bbase (se 6 (by rfl) ⟨15054, by rfl⟩ : syracuseStep 642325 = 30109) (by norm_num)
theorem B642365 : Blo 283827 642365 := bbase (se 3 (by rfl) ⟨120443, by rfl⟩ : syracuseStep 642365 = 240887) (by norm_num)
theorem B642437 : Blo 283827 642437 := bbase (se 4 (by rfl) ⟨60228, by rfl⟩ : syracuseStep 642437 = 120457) (by norm_num)
theorem B347537 : Blo 283827 347537 := bbase (se 2 (by rfl) ⟨130326, by rfl⟩ : syracuseStep 347537 = 260653) (by norm_num)
theorem B642509 : Blo 283827 642509 := bbase (se 3 (by rfl) ⟨120470, by rfl⟩ : syracuseStep 642509 = 240941) (by norm_num)
theorem B544229 : Blo 283827 544229 := bbase (se 4 (by rfl) ⟨51021, by rfl⟩ : syracuseStep 544229 = 102043) (by norm_num)
theorem B609781 : Blo 283827 609781 := bbase (se 5 (by rfl) ⟨28583, by rfl⟩ : syracuseStep 609781 = 57167) (by norm_num)
theorem B642581 : Blo 283827 642581 := bbase (se 6 (by rfl) ⟨15060, by rfl⟩ : syracuseStep 642581 = 30121) (by norm_num)
theorem B970325 : Blo 283827 970325 := bbase (se 8 (by rfl) ⟨5685, by rfl⟩ : syracuseStep 970325 = 11371) (by norm_num)
theorem B642653 : Blo 283827 642653 := bbase (se 3 (by rfl) ⟨120497, by rfl⟩ : syracuseStep 642653 = 240995) (by norm_num)
theorem B642725 : Blo 283827 642725 := bbase (se 4 (by rfl) ⟨60255, by rfl⟩ : syracuseStep 642725 = 120511) (by norm_num)
theorem B642797 : Blo 283827 642797 := bbase (se 3 (by rfl) ⟨120524, by rfl⟩ : syracuseStep 642797 = 241049) (by norm_num)
theorem B478973 : Blo 283827 478973 := bbase (se 3 (by rfl) ⟨89807, by rfl⟩ : syracuseStep 478973 = 179615) (by norm_num)
theorem B1298213 : Blo 283827 1298213 := bbase (se 4 (by rfl) ⟨121707, by rfl⟩ : syracuseStep 1298213 = 243415) (by norm_num)
theorem B642869 : Blo 283827 642869 := bbase (se 5 (by rfl) ⟨30134, by rfl⟩ : syracuseStep 642869 = 60269) (by norm_num)
theorem B479101 : Blo 283827 479101 := bbase (se 3 (by rfl) ⟨89831, by rfl⟩ : syracuseStep 479101 = 179663) (by norm_num)
theorem B642941 : Blo 283827 642941 := bbase (se 3 (by rfl) ⟨120551, by rfl⟩ : syracuseStep 642941 = 241103) (by norm_num)
theorem B643013 : Blo 283827 643013 := bbase (se 4 (by rfl) ⟨60282, by rfl⟩ : syracuseStep 643013 = 120565) (by norm_num)
theorem B479189 : Blo 283827 479189 := bbase (se 7 (by rfl) ⟨5615, by rfl⟩ : syracuseStep 479189 = 11231) (by norm_num)
theorem B970757 : Blo 283827 970757 := bbase (se 4 (by rfl) ⟨91008, by rfl⟩ : syracuseStep 970757 = 182017) (by norm_num)
theorem B643085 : Blo 283827 643085 := bbase (se 3 (by rfl) ⟨120578, by rfl⟩ : syracuseStep 643085 = 241157) (by norm_num)
theorem B315433 : Blo 283827 315433 := bbase (se 2 (by rfl) ⟨118287, by rfl⟩ : syracuseStep 315433 = 236575) (by norm_num)
theorem B479317 : Blo 283827 479317 := bbase (se 8 (by rfl) ⟨2808, by rfl⟩ : syracuseStep 479317 = 5617) (by norm_num)
theorem B643157 : Blo 283827 643157 := bbase (se 8 (by rfl) ⟨3768, by rfl⟩ : syracuseStep 643157 = 7537) (by norm_num)
theorem B643229 : Blo 283827 643229 := bbase (se 3 (by rfl) ⟨120605, by rfl⟩ : syracuseStep 643229 = 241211) (by norm_num)
theorem B479405 : Blo 283827 479405 := bbase (se 3 (by rfl) ⟨89888, by rfl⟩ : syracuseStep 479405 = 179777) (by norm_num)
theorem B1364165 : Blo 283827 1364165 := bbase (se 4 (by rfl) ⟨127890, by rfl⟩ : syracuseStep 1364165 = 255781) (by norm_num)
theorem B544981 : Blo 283827 544981 := bbase (se 7 (by rfl) ⟨6386, by rfl⟩ : syracuseStep 544981 = 12773) (by norm_num)
theorem B643301 : Blo 283827 643301 := bbase (se 4 (by rfl) ⟨60309, by rfl⟩ : syracuseStep 643301 = 120619) (by norm_num)
theorem B479533 : Blo 283827 479533 := bbase (se 3 (by rfl) ⟨89912, by rfl⟩ : syracuseStep 479533 = 179825) (by norm_num)
theorem B643373 : Blo 283827 643373 := bbase (se 3 (by rfl) ⟨120632, by rfl⟩ : syracuseStep 643373 = 241265) (by norm_num)
theorem B4903253 : Blo 283827 4903253 := bbase (se 10 (by rfl) ⟨7182, by rfl⟩ : syracuseStep 4903253 = 14365) (by norm_num)
theorem B545125 : Blo 283827 545125 := bbase (se 4 (by rfl) ⟨51105, by rfl⟩ : syracuseStep 545125 = 102211) (by norm_num)
theorem B610669 : Blo 283827 610669 := bbase (se 3 (by rfl) ⟨114500, by rfl⟩ : syracuseStep 610669 = 229001) (by norm_num)
theorem B643445 : Blo 283827 643445 := bbase (se 5 (by rfl) ⟨30161, by rfl⟩ : syracuseStep 643445 = 60323) (by norm_num)
theorem B479621 : Blo 283827 479621 := bbase (se 4 (by rfl) ⟨44964, by rfl⟩ : syracuseStep 479621 = 89929) (by norm_num)
theorem B971189 : Blo 283827 971189 := bbase (se 5 (by rfl) ⟨45524, by rfl⟩ : syracuseStep 971189 = 91049) (by norm_num)
theorem B643517 : Blo 283827 643517 := bbase (se 3 (by rfl) ⟨120659, by rfl⟩ : syracuseStep 643517 = 241319) (by norm_num)
theorem B1626581 : Blo 283827 1626581 := bbase (se 7 (by rfl) ⟨19061, by rfl⟩ : syracuseStep 1626581 = 38123) (by norm_num)
theorem B1102325 : Blo 283827 1102325 := bbase (se 5 (by rfl) ⟨51671, by rfl⟩ : syracuseStep 1102325 = 103343) (by norm_num)
theorem B479749 : Blo 283827 479749 := bbase (se 4 (by rfl) ⟨44976, by rfl⟩ : syracuseStep 479749 = 89953) (by norm_num)
theorem B643589 : Blo 283827 643589 := bbase (se 4 (by rfl) ⟨60336, by rfl⟩ : syracuseStep 643589 = 120673) (by norm_num)
theorem B545285 : Blo 283827 545285 := bbase (se 4 (by rfl) ⟨51120, by rfl⟩ : syracuseStep 545285 = 102241) (by norm_num)
theorem B643661 : Blo 283827 643661 := bbase (se 3 (by rfl) ⟨120686, by rfl⟩ : syracuseStep 643661 = 241373) (by norm_num)
theorem B479837 : Blo 283827 479837 := bbase (se 3 (by rfl) ⟨89969, by rfl⟩ : syracuseStep 479837 = 179939) (by norm_num)
theorem B971365 : Blo 283827 971365 := bbase (se 4 (by rfl) ⟨91065, by rfl⟩ : syracuseStep 971365 = 182131) (by norm_num)
theorem B643733 : Blo 283827 643733 := bbase (se 6 (by rfl) ⟨15087, by rfl⟩ : syracuseStep 643733 = 30175) (by norm_num)
theorem B545429 : Blo 283827 545429 := bbase (se 6 (by rfl) ⟨12783, by rfl⟩ : syracuseStep 545429 = 25567) (by norm_num)
theorem B479965 : Blo 283827 479965 := bbase (se 3 (by rfl) ⟨89993, by rfl⟩ : syracuseStep 479965 = 179987) (by norm_num)
theorem B643805 : Blo 283827 643805 := bbase (se 3 (by rfl) ⟨120713, by rfl⟩ : syracuseStep 643805 = 241427) (by norm_num)
theorem B643877 : Blo 283827 643877 := bbase (se 4 (by rfl) ⟨60363, by rfl⟩ : syracuseStep 643877 = 120727) (by norm_num)
theorem B480053 : Blo 283827 480053 := bbase (se 5 (by rfl) ⟨22502, by rfl⟩ : syracuseStep 480053 = 45005) (by norm_num)
theorem B611165 : Blo 283827 611165 := bbase (se 3 (by rfl) ⟨114593, by rfl⟩ : syracuseStep 611165 = 229187) (by norm_num)
theorem B643949 : Blo 283827 643949 := bbase (se 3 (by rfl) ⟨120740, by rfl⟩ : syracuseStep 643949 = 241481) (by norm_num)
theorem B480181 : Blo 283827 480181 := bbase (se 5 (by rfl) ⟨22508, by rfl⟩ : syracuseStep 480181 = 45017) (by norm_num)
theorem B644021 : Blo 283827 644021 := bbase (se 5 (by rfl) ⟨30188, by rfl⟩ : syracuseStep 644021 = 60377) (by norm_num)
theorem B545717 : Blo 283827 545717 := bbase (se 5 (by rfl) ⟨25580, by rfl⟩ : syracuseStep 545717 = 51161) (by norm_num)
theorem B644093 : Blo 283827 644093 := bbase (se 3 (by rfl) ⟨120767, by rfl⟩ : syracuseStep 644093 = 241535) (by norm_num)
theorem B480269 : Blo 283827 480269 := bbase (se 3 (by rfl) ⟨90050, by rfl⟩ : syracuseStep 480269 = 180101) (by norm_num)
theorem B578621 : Blo 283827 578621 := bbase (se 3 (by rfl) ⟨108491, by rfl⟩ : syracuseStep 578621 = 216983) (by norm_num)
theorem B644165 : Blo 283827 644165 := bbase (se 4 (by rfl) ⟨60390, by rfl⟩ : syracuseStep 644165 = 120781) (by norm_num)
theorem B545869 : Blo 283827 545869 := bbase (se 3 (by rfl) ⟨102350, by rfl⟩ : syracuseStep 545869 = 204701) (by norm_num)
theorem B578669 : Blo 283827 578669 := bbase (se 3 (by rfl) ⟨108500, by rfl⟩ : syracuseStep 578669 = 217001) (by norm_num)
theorem B480397 : Blo 283827 480397 := bbase (se 3 (by rfl) ⟨90074, by rfl⟩ : syracuseStep 480397 = 180149) (by norm_num)
theorem B644237 : Blo 283827 644237 := bbase (se 3 (by rfl) ⟨120794, by rfl⟩ : syracuseStep 644237 = 241589) (by norm_num)
theorem B644309 : Blo 283827 644309 := bbase (se 7 (by rfl) ⟨7550, by rfl⟩ : syracuseStep 644309 = 15101) (by norm_num)
theorem B480485 : Blo 283827 480485 := bbase (se 4 (by rfl) ⟨45045, by rfl⟩ : syracuseStep 480485 = 90091) (by norm_num)
theorem B644381 : Blo 283827 644381 := bbase (se 3 (by rfl) ⟨120821, by rfl⟩ : syracuseStep 644381 = 241643) (by norm_num)
theorem B3659093 : Blo 283827 3659093 := bbase (se 15 (by rfl) ⟨167, by rfl⟩ : syracuseStep 3659093 = 335) (by norm_num)
theorem B480613 : Blo 283827 480613 := bbase (se 4 (by rfl) ⟨45057, by rfl⟩ : syracuseStep 480613 = 90115) (by norm_num)
theorem B644453 : Blo 283827 644453 := bbase (se 4 (by rfl) ⟨60417, by rfl⟩ : syracuseStep 644453 = 120835) (by norm_num)
theorem B546173 : Blo 283827 546173 := bbase (se 3 (by rfl) ⟨102407, by rfl⟩ : syracuseStep 546173 = 204815) (by norm_num)
theorem B808325 : Blo 283827 808325 := bbase (se 4 (by rfl) ⟨75780, by rfl⟩ : syracuseStep 808325 = 151561) (by norm_num)
theorem B513421 : Blo 283827 513421 := bbase (se 3 (by rfl) ⟨96266, by rfl⟩ : syracuseStep 513421 = 192533) (by norm_num)
theorem B644525 : Blo 283827 644525 := bbase (se 3 (by rfl) ⟨120848, by rfl⟩ : syracuseStep 644525 = 241697) (by norm_num)
theorem B480701 : Blo 283827 480701 := bbase (se 3 (by rfl) ⟨90131, by rfl⟩ : syracuseStep 480701 = 180263) (by norm_num)
theorem B644597 : Blo 283827 644597 := bbase (se 5 (by rfl) ⟨30215, by rfl⟩ : syracuseStep 644597 = 60431) (by norm_num)
theorem B579125 : Blo 283827 579125 := bbase (se 5 (by rfl) ⟨27146, by rfl⟩ : syracuseStep 579125 = 54293) (by norm_num)
theorem B874037 : Blo 283827 874037 := bbase (se 5 (by rfl) ⟨40970, by rfl⟩ : syracuseStep 874037 = 81941) (by norm_num)
theorem B480829 : Blo 283827 480829 := bbase (se 3 (by rfl) ⟨90155, by rfl⟩ : syracuseStep 480829 = 180311) (by norm_num)
theorem B644669 : Blo 283827 644669 := bbase (se 3 (by rfl) ⟨120875, by rfl⟩ : syracuseStep 644669 = 241751) (by norm_num)
theorem B644741 : Blo 283827 644741 := bbase (se 4 (by rfl) ⟨60444, by rfl⟩ : syracuseStep 644741 = 120889) (by norm_num)
theorem B480917 : Blo 283827 480917 := bbase (se 6 (by rfl) ⟨11271, by rfl⟩ : syracuseStep 480917 = 22543) (by norm_num)
theorem B644813 : Blo 283827 644813 := bbase (se 3 (by rfl) ⟨120902, by rfl⟩ : syracuseStep 644813 = 241805) (by norm_num)
theorem B612053 : Blo 283827 612053 := bbase (se 7 (by rfl) ⟨7172, by rfl⟩ : syracuseStep 612053 = 14345) (by norm_num)
theorem B481045 : Blo 283827 481045 := bbase (se 6 (by rfl) ⟨11274, by rfl⟩ : syracuseStep 481045 = 22549) (by norm_num)
theorem B644885 : Blo 283827 644885 := bbase (se 6 (by rfl) ⟨15114, by rfl⟩ : syracuseStep 644885 = 30229) (by norm_num)
theorem B612173 : Blo 283827 612173 := bbase (se 3 (by rfl) ⟨114782, by rfl⟩ : syracuseStep 612173 = 229565) (by norm_num)
theorem B644957 : Blo 283827 644957 := bbase (se 3 (by rfl) ⟨120929, by rfl⟩ : syracuseStep 644957 = 241859) (by norm_num)
theorem B481133 : Blo 283827 481133 := bbase (se 3 (by rfl) ⟨90212, by rfl⟩ : syracuseStep 481133 = 180425) (by norm_num)
theorem B645029 : Blo 283827 645029 := bbase (se 4 (by rfl) ⟨60471, by rfl⟩ : syracuseStep 645029 = 120943) (by norm_num)
theorem B481261 : Blo 283827 481261 := bbase (se 3 (by rfl) ⟨90236, by rfl⟩ : syracuseStep 481261 = 180473) (by norm_num)
theorem B645101 : Blo 283827 645101 := bbase (se 3 (by rfl) ⟨120956, by rfl⟩ : syracuseStep 645101 = 241913) (by norm_num)
theorem B645173 : Blo 283827 645173 := bbase (se 5 (by rfl) ⟨30242, by rfl⟩ : syracuseStep 645173 = 60485) (by norm_num)
theorem B481349 : Blo 283827 481349 := bbase (se 4 (by rfl) ⟨45126, by rfl⟩ : syracuseStep 481349 = 90253) (by norm_num)
theorem B2054261 : Blo 283827 2054261 := bbase (se 5 (by rfl) ⟨96293, by rfl⟩ : syracuseStep 2054261 = 192587) (by norm_num)
theorem B645245 : Blo 283827 645245 := bbase (se 3 (by rfl) ⟨120983, by rfl⟩ : syracuseStep 645245 = 241967) (by norm_num)
theorem B481477 : Blo 283827 481477 := bbase (se 4 (by rfl) ⟨45138, by rfl⟩ : syracuseStep 481477 = 90277) (by norm_num)
theorem B645317 : Blo 283827 645317 := bbase (se 4 (by rfl) ⟨60498, by rfl⟩ : syracuseStep 645317 = 120997) (by norm_num)
theorem B1300693 : Blo 283827 1300693 := bbase (se 7 (by rfl) ⟨15242, by rfl⟩ : syracuseStep 1300693 = 30485) (by norm_num)
theorem B645389 : Blo 283827 645389 := bbase (se 3 (by rfl) ⟨121010, by rfl⟩ : syracuseStep 645389 = 242021) (by norm_num)
theorem B481565 : Blo 283827 481565 := bbase (se 3 (by rfl) ⟨90293, by rfl⟩ : syracuseStep 481565 = 180587) (by norm_num)
theorem B645461 : Blo 283827 645461 := bbase (se 10 (by rfl) ⟨945, by rfl⟩ : syracuseStep 645461 = 1891) (by norm_num)
theorem B481693 : Blo 283827 481693 := bbase (se 3 (by rfl) ⟨90317, by rfl⟩ : syracuseStep 481693 = 180635) (by norm_num)
theorem B645533 : Blo 283827 645533 := bbase (se 3 (by rfl) ⟨121037, by rfl⟩ : syracuseStep 645533 = 242075) (by norm_num)
theorem B612805 : Blo 283827 612805 := bbase (se 4 (by rfl) ⟨57450, by rfl⟩ : syracuseStep 612805 = 114901) (by norm_num)
theorem B645605 : Blo 283827 645605 := bbase (se 4 (by rfl) ⟨60525, by rfl⟩ : syracuseStep 645605 = 121051) (by norm_num)
theorem B481781 : Blo 283827 481781 := bbase (se 5 (by rfl) ⟨22583, by rfl⟩ : syracuseStep 481781 = 45167) (by norm_num)
theorem B809509 : Blo 283827 809509 := bbase (se 4 (by rfl) ⟨75891, by rfl⟩ : syracuseStep 809509 = 151783) (by norm_num)
theorem B645677 : Blo 283827 645677 := bbase (se 3 (by rfl) ⟨121064, by rfl⟩ : syracuseStep 645677 = 242129) (by norm_num)
theorem B481909 : Blo 283827 481909 := bbase (se 5 (by rfl) ⟨22589, by rfl⟩ : syracuseStep 481909 = 45179) (by norm_num)
theorem B645749 : Blo 283827 645749 := bbase (se 5 (by rfl) ⟨30269, by rfl⟩ : syracuseStep 645749 = 60539) (by norm_num)
theorem B645821 : Blo 283827 645821 := bbase (se 3 (by rfl) ⟨121091, by rfl⟩ : syracuseStep 645821 = 242183) (by norm_num)
theorem B809669 : Blo 283827 809669 := bbase (se 4 (by rfl) ⟨75906, by rfl⟩ : syracuseStep 809669 = 151813) (by norm_num)
theorem B481997 : Blo 283827 481997 := bbase (se 3 (by rfl) ⟨90374, by rfl⟩ : syracuseStep 481997 = 180749) (by norm_num)
theorem B645893 : Blo 283827 645893 := bbase (se 4 (by rfl) ⟨60552, by rfl⟩ : syracuseStep 645893 = 121105) (by norm_num)
theorem B514829 : Blo 283827 514829 := bbase (se 3 (by rfl) ⟨96530, by rfl⟩ : syracuseStep 514829 = 193061) (by norm_num)
theorem B514885 : Blo 283827 514885 := bbase (se 4 (by rfl) ⟨48270, by rfl⟩ : syracuseStep 514885 = 96541) (by norm_num)
theorem B482125 : Blo 283827 482125 := bbase (se 3 (by rfl) ⟨90398, by rfl⟩ : syracuseStep 482125 = 180797) (by norm_num)
theorem B645965 : Blo 283827 645965 := bbase (se 3 (by rfl) ⟨121118, by rfl⟩ : syracuseStep 645965 = 242237) (by norm_num)
theorem B646037 : Blo 283827 646037 := bbase (se 6 (by rfl) ⟨15141, by rfl⟩ : syracuseStep 646037 = 30283) (by norm_num)
theorem B482213 : Blo 283827 482213 := bbase (se 4 (by rfl) ⟨45207, by rfl⟩ : syracuseStep 482213 = 90415) (by norm_num)
theorem B809909 : Blo 283827 809909 := bbase (se 5 (by rfl) ⟨37964, by rfl⟩ : syracuseStep 809909 = 75929) (by norm_num)
theorem B646109 : Blo 283827 646109 := bbase (se 3 (by rfl) ⟨121145, by rfl⟩ : syracuseStep 646109 = 242291) (by norm_num)
theorem B482341 : Blo 283827 482341 := bbase (se 4 (by rfl) ⟨45219, by rfl⟩ : syracuseStep 482341 = 90439) (by norm_num)
theorem B646181 : Blo 283827 646181 := bbase (se 4 (by rfl) ⟨60579, by rfl⟩ : syracuseStep 646181 = 121159) (by norm_num)
theorem B777269 : Blo 283827 777269 := bbase (se 5 (by rfl) ⟨36434, by rfl⟩ : syracuseStep 777269 = 72869) (by norm_num)
theorem B646253 : Blo 283827 646253 := bbase (se 3 (by rfl) ⟨121172, by rfl⟩ : syracuseStep 646253 = 242345) (by norm_num)
theorem B810101 : Blo 283827 810101 := bbase (se 5 (by rfl) ⟨37973, by rfl⟩ : syracuseStep 810101 = 75947) (by norm_num)
theorem B482429 : Blo 283827 482429 := bbase (se 3 (by rfl) ⟨90455, by rfl⟩ : syracuseStep 482429 = 180911) (by norm_num)
theorem B646325 : Blo 283827 646325 := bbase (se 5 (by rfl) ⟨30296, by rfl⟩ : syracuseStep 646325 = 60593) (by norm_num)
theorem B482557 : Blo 283827 482557 := bbase (se 3 (by rfl) ⟨90479, by rfl⟩ : syracuseStep 482557 = 180959) (by norm_num)
theorem B646397 : Blo 283827 646397 := bbase (se 3 (by rfl) ⟨121199, by rfl⟩ : syracuseStep 646397 = 242399) (by norm_num)
theorem B613693 : Blo 283827 613693 := bbase (se 3 (by rfl) ⟨115067, by rfl⟩ : syracuseStep 613693 = 230135) (by norm_num)
theorem B646469 : Blo 283827 646469 := bbase (se 4 (by rfl) ⟨60606, by rfl⟩ : syracuseStep 646469 = 121213) (by norm_num)
theorem B482645 : Blo 283827 482645 := bbase (se 11 (by rfl) ⟨353, by rfl⟩ : syracuseStep 482645 = 707) (by norm_num)
theorem B646541 : Blo 283827 646541 := bbase (se 3 (by rfl) ⟨121226, by rfl⟩ : syracuseStep 646541 = 242453) (by norm_num)
theorem B1564085 : Blo 283827 1564085 := bbase (se 5 (by rfl) ⟨73316, by rfl⟩ : syracuseStep 1564085 = 146633) (by norm_num)
theorem B613813 : Blo 283827 613813 := bbase (se 5 (by rfl) ⟨28772, by rfl⟩ : syracuseStep 613813 = 57545) (by norm_num)
theorem B482773 : Blo 283827 482773 := bbase (se 7 (by rfl) ⟨5657, by rfl⟩ : syracuseStep 482773 = 11315) (by norm_num)
theorem B646613 : Blo 283827 646613 := bbase (se 7 (by rfl) ⟨7577, by rfl⟩ : syracuseStep 646613 = 15155) (by norm_num)
theorem B777701 : Blo 283827 777701 := bbase (se 4 (by rfl) ⟨72909, by rfl⟩ : syracuseStep 777701 = 145819) (by norm_num)
theorem B646685 : Blo 283827 646685 := bbase (se 3 (by rfl) ⟨121253, by rfl⟩ : syracuseStep 646685 = 242507) (by norm_num)
theorem B482861 : Blo 283827 482861 := bbase (se 3 (by rfl) ⟨90536, by rfl⟩ : syracuseStep 482861 = 181073) (by norm_num)
theorem B646757 : Blo 283827 646757 := bbase (se 4 (by rfl) ⟨60633, by rfl⟩ : syracuseStep 646757 = 121267) (by norm_num)
theorem B482989 : Blo 283827 482989 := bbase (se 3 (by rfl) ⟨90560, by rfl⟩ : syracuseStep 482989 = 181121) (by norm_num)
theorem B646829 : Blo 283827 646829 := bbase (se 3 (by rfl) ⟨121280, by rfl⟩ : syracuseStep 646829 = 242561) (by norm_num)
theorem B614069 : Blo 283827 614069 := bbase (se 5 (by rfl) ⟨28784, by rfl⟩ : syracuseStep 614069 = 57569) (by norm_num)
theorem B646901 : Blo 283827 646901 := bbase (se 5 (by rfl) ⟨30323, by rfl⟩ : syracuseStep 646901 = 60647) (by norm_num)
theorem B483077 : Blo 283827 483077 := bbase (se 4 (by rfl) ⟨45288, by rfl⟩ : syracuseStep 483077 = 90577) (by norm_num)
theorem B548669 : Blo 283827 548669 := bbase (se 3 (by rfl) ⟨102875, by rfl⟩ : syracuseStep 548669 = 205751) (by norm_num)
theorem B646973 : Blo 283827 646973 := bbase (se 3 (by rfl) ⟨121307, by rfl⟩ : syracuseStep 646973 = 242615) (by norm_num)
theorem B319333 : Blo 283827 319333 := bbase (se 4 (by rfl) ⟨29937, by rfl⟩ : syracuseStep 319333 = 59875) (by norm_num)
theorem B483205 : Blo 283827 483205 := bbase (se 4 (by rfl) ⟨45300, by rfl⟩ : syracuseStep 483205 = 90601) (by norm_num)
theorem B647045 : Blo 283827 647045 := bbase (se 4 (by rfl) ⟨60660, by rfl⟩ : syracuseStep 647045 = 121321) (by norm_num)
theorem B319369 : Blo 283827 319369 := bbase (se 2 (by rfl) ⟨119763, by rfl⟩ : syracuseStep 319369 = 239527) (by norm_num)
theorem B319405 : Blo 283827 319405 := bbase (se 3 (by rfl) ⟨59888, by rfl⟩ : syracuseStep 319405 = 119777) (by norm_num)
theorem B647117 : Blo 283827 647117 := bbase (se 3 (by rfl) ⟨121334, by rfl⟩ : syracuseStep 647117 = 242669) (by norm_num)
theorem B319441 : Blo 283827 319441 := bbase (se 2 (by rfl) ⟨119790, by rfl⟩ : syracuseStep 319441 = 239581) (by norm_num)
theorem B483293 : Blo 283827 483293 := bbase (se 3 (by rfl) ⟨90617, by rfl⟩ : syracuseStep 483293 = 181235) (by norm_num)
theorem B319477 : Blo 283827 319477 := bbase (se 5 (by rfl) ⟨14975, by rfl⟩ : syracuseStep 319477 = 29951) (by norm_num)
theorem B647189 : Blo 283827 647189 := bbase (se 6 (by rfl) ⟨15168, by rfl⟩ : syracuseStep 647189 = 30337) (by norm_num)
theorem B319513 : Blo 283827 319513 := bbase (se 2 (by rfl) ⟨119817, by rfl⟩ : syracuseStep 319513 = 239635) (by norm_num)
theorem B319549 : Blo 283827 319549 := bbase (se 3 (by rfl) ⟨59915, by rfl⟩ : syracuseStep 319549 = 119831) (by norm_num)
theorem B811093 : Blo 283827 811093 := bbase (se 8 (by rfl) ⟨4752, by rfl⟩ : syracuseStep 811093 = 9505) (by norm_num)
theorem B483421 : Blo 283827 483421 := bbase (se 3 (by rfl) ⟨90641, by rfl⟩ : syracuseStep 483421 = 181283) (by norm_num)
theorem B647261 : Blo 283827 647261 := bbase (se 3 (by rfl) ⟨121361, by rfl⟩ : syracuseStep 647261 = 242723) (by norm_num)
theorem B319585 : Blo 283827 319585 := bbase (se 2 (by rfl) ⟨119844, by rfl⟩ : syracuseStep 319585 = 239689) (by norm_num)
theorem B319621 : Blo 283827 319621 := bbase (se 4 (by rfl) ⟨29964, by rfl⟩ : syracuseStep 319621 = 59929) (by norm_num)
theorem B647333 : Blo 283827 647333 := bbase (se 4 (by rfl) ⟨60687, by rfl⟩ : syracuseStep 647333 = 121375) (by norm_num)
theorem B319657 : Blo 283827 319657 := bbase (se 2 (by rfl) ⟨119871, by rfl⟩ : syracuseStep 319657 = 239743) (by norm_num)
theorem B483509 : Blo 283827 483509 := bbase (se 5 (by rfl) ⟨22664, by rfl⟩ : syracuseStep 483509 = 45329) (by norm_num)
theorem B319693 : Blo 283827 319693 := bbase (se 3 (by rfl) ⟨59942, by rfl⟩ : syracuseStep 319693 = 119885) (by norm_num)
theorem B614621 : Blo 283827 614621 := bbase (se 3 (by rfl) ⟨115241, by rfl⟩ : syracuseStep 614621 = 230483) (by norm_num)
theorem B647405 : Blo 283827 647405 := bbase (se 3 (by rfl) ⟨121388, by rfl⟩ : syracuseStep 647405 = 242777) (by norm_num)
theorem B319729 : Blo 283827 319729 := bbase (se 2 (by rfl) ⟨119898, by rfl⟩ : syracuseStep 319729 = 239797) (by norm_num)
theorem B319765 : Blo 283827 319765 := bbase (se 6 (by rfl) ⟨7494, by rfl⟩ : syracuseStep 319765 = 14989) (by norm_num)
theorem B483637 : Blo 283827 483637 := bbase (se 5 (by rfl) ⟨22670, by rfl⟩ : syracuseStep 483637 = 45341) (by norm_num)
theorem B647477 : Blo 283827 647477 := bbase (se 5 (by rfl) ⟨30350, by rfl⟩ : syracuseStep 647477 = 60701) (by norm_num)
theorem B319801 : Blo 283827 319801 := bbase (se 2 (by rfl) ⟨119925, by rfl⟩ : syracuseStep 319801 = 239851) (by norm_num)
theorem B319837 : Blo 283827 319837 := bbase (se 3 (by rfl) ⟨59969, by rfl⟩ : syracuseStep 319837 = 119939) (by norm_num)
theorem B647549 : Blo 283827 647549 := bbase (se 3 (by rfl) ⟨121415, by rfl⟩ : syracuseStep 647549 = 242831) (by norm_num)
theorem B319873 : Blo 283827 319873 := bbase (se 2 (by rfl) ⟨119952, by rfl⟩ : syracuseStep 319873 = 239905) (by norm_num)
theorem B483725 : Blo 283827 483725 := bbase (se 3 (by rfl) ⟨90698, by rfl⟩ : syracuseStep 483725 = 181397) (by norm_num)
theorem B319909 : Blo 283827 319909 := bbase (se 4 (by rfl) ⟨29991, by rfl⟩ : syracuseStep 319909 = 59983) (by norm_num)
theorem B319945 : Blo 283827 319945 := bbase (se 2 (by rfl) ⟨119979, by rfl⟩ : syracuseStep 319945 = 239959) (by norm_num)
theorem B1106389 : Blo 283827 1106389 := bbase (se 7 (by rfl) ⟨12965, by rfl⟩ : syracuseStep 1106389 = 25931) (by norm_num)
theorem B319981 : Blo 283827 319981 := bbase (se 3 (by rfl) ⟨59996, by rfl⟩ : syracuseStep 319981 = 119993) (by norm_num)
theorem B483853 : Blo 283827 483853 := bbase (se 3 (by rfl) ⟨90722, by rfl⟩ : syracuseStep 483853 = 181445) (by norm_num)
theorem B320017 : Blo 283827 320017 := bbase (se 2 (by rfl) ⟨120006, by rfl⟩ : syracuseStep 320017 = 240013) (by norm_num)
theorem B320053 : Blo 283827 320053 := bbase (se 5 (by rfl) ⟨15002, by rfl⟩ : syracuseStep 320053 = 30005) (by norm_num)
theorem B320089 : Blo 283827 320089 := bbase (se 2 (by rfl) ⟨120033, by rfl⟩ : syracuseStep 320089 = 240067) (by norm_num)
theorem B483941 : Blo 283827 483941 := bbase (se 4 (by rfl) ⟨45369, by rfl⟩ : syracuseStep 483941 = 90739) (by norm_num)
theorem B385645 : Blo 283827 385645 := bbase (se 3 (by rfl) ⟨72308, by rfl⟩ : syracuseStep 385645 = 144617) (by norm_num)
theorem B320125 : Blo 283827 320125 := bbase (se 3 (by rfl) ⟨60023, by rfl⟩ : syracuseStep 320125 = 120047) (by norm_num)
theorem B320161 : Blo 283827 320161 := bbase (se 2 (by rfl) ⟨120060, by rfl⟩ : syracuseStep 320161 = 240121) (by norm_num)
theorem B320197 : Blo 283827 320197 := bbase (se 4 (by rfl) ⟨30018, by rfl⟩ : syracuseStep 320197 = 60037) (by norm_num)
theorem B484069 : Blo 283827 484069 := bbase (se 4 (by rfl) ⟨45381, by rfl⟩ : syracuseStep 484069 = 90763) (by norm_num)
theorem B320233 : Blo 283827 320233 := bbase (se 2 (by rfl) ⟨120087, by rfl⟩ : syracuseStep 320233 = 240175) (by norm_num)
theorem B320269 : Blo 283827 320269 := bbase (se 3 (by rfl) ⟨60050, by rfl⟩ : syracuseStep 320269 = 120101) (by norm_num)
theorem B320305 : Blo 283827 320305 := bbase (se 2 (by rfl) ⟨120114, by rfl⟩ : syracuseStep 320305 = 240229) (by norm_num)
theorem B484157 : Blo 283827 484157 := bbase (se 3 (by rfl) ⟨90779, by rfl⟩ : syracuseStep 484157 = 181559) (by norm_num)
theorem B648013 : Blo 283827 648013 := bbase (se 3 (by rfl) ⟨121502, by rfl⟩ : syracuseStep 648013 = 243005) (by norm_num)
theorem B320341 : Blo 283827 320341 := bbase (se 9 (by rfl) ⟨938, by rfl⟩ : syracuseStep 320341 = 1877) (by norm_num)
theorem B320377 : Blo 283827 320377 := bbase (se 2 (by rfl) ⟨120141, by rfl⟩ : syracuseStep 320377 = 240283) (by norm_num)
theorem B3072917 : Blo 283827 3072917 := bbase (se 6 (by rfl) ⟨72021, by rfl⟩ : syracuseStep 3072917 = 144043) (by norm_num)
theorem B320413 : Blo 283827 320413 := bbase (se 3 (by rfl) ⟨60077, by rfl⟩ : syracuseStep 320413 = 120155) (by norm_num)
theorem B975797 : Blo 283827 975797 := bbase (se 5 (by rfl) ⟨45740, by rfl⟩ : syracuseStep 975797 = 91481) (by norm_num)
theorem B484285 : Blo 283827 484285 := bbase (se 3 (by rfl) ⟨90803, by rfl⟩ : syracuseStep 484285 = 181607) (by norm_num)
theorem B320449 : Blo 283827 320449 := bbase (se 2 (by rfl) ⟨120168, by rfl⟩ : syracuseStep 320449 = 240337) (by norm_num)
theorem B320485 : Blo 283827 320485 := bbase (se 4 (by rfl) ⟨30045, by rfl⟩ : syracuseStep 320485 = 60091) (by norm_num)
theorem B320521 : Blo 283827 320521 := bbase (se 2 (by rfl) ⟨120195, by rfl⟩ : syracuseStep 320521 = 240391) (by norm_num)
theorem B484373 : Blo 283827 484373 := bbase (se 6 (by rfl) ⟨11352, by rfl⟩ : syracuseStep 484373 = 22705) (by norm_num)
theorem B320557 : Blo 283827 320557 := bbase (se 3 (by rfl) ⟨60104, by rfl⟩ : syracuseStep 320557 = 120209) (by norm_num)
theorem B320593 : Blo 283827 320593 := bbase (se 2 (by rfl) ⟨120222, by rfl⟩ : syracuseStep 320593 = 240445) (by norm_num)
theorem B320629 : Blo 283827 320629 := bbase (se 5 (by rfl) ⟨15029, by rfl⟩ : syracuseStep 320629 = 30059) (by norm_num)
theorem B582773 : Blo 283827 582773 := bbase (se 5 (by rfl) ⟨27317, by rfl⟩ : syracuseStep 582773 = 54635) (by norm_num)
theorem B484501 : Blo 283827 484501 := bbase (se 6 (by rfl) ⟨11355, by rfl⟩ : syracuseStep 484501 = 22711) (by norm_num)
theorem B320665 : Blo 283827 320665 := bbase (se 2 (by rfl) ⟨120249, by rfl⟩ : syracuseStep 320665 = 240499) (by norm_num)
theorem B812197 : Blo 283827 812197 := bbase (se 4 (by rfl) ⟨76143, by rfl⟩ : syracuseStep 812197 = 152287) (by norm_num)
theorem B320701 : Blo 283827 320701 := bbase (se 3 (by rfl) ⟨60131, by rfl⟩ : syracuseStep 320701 = 120263) (by norm_num)
theorem B320737 : Blo 283827 320737 := bbase (se 2 (by rfl) ⟨120276, by rfl⟩ : syracuseStep 320737 = 240553) (by norm_num)
theorem B484589 : Blo 283827 484589 := bbase (se 3 (by rfl) ⟨90860, by rfl⟩ : syracuseStep 484589 = 181721) (by norm_num)
theorem B320773 : Blo 283827 320773 := bbase (se 4 (by rfl) ⟨30072, by rfl⟩ : syracuseStep 320773 = 60145) (by norm_num)
theorem B320809 : Blo 283827 320809 := bbase (se 2 (by rfl) ⟨120303, by rfl⟩ : syracuseStep 320809 = 240607) (by norm_num)
theorem B517429 : Blo 283827 517429 := bbase (se 5 (by rfl) ⟨24254, by rfl⟩ : syracuseStep 517429 = 48509) (by norm_num)
theorem B320845 : Blo 283827 320845 := bbase (se 3 (by rfl) ⟨60158, by rfl⟩ : syracuseStep 320845 = 120317) (by norm_num)
theorem B3106133 : Blo 283827 3106133 := bbase (se 12 (by rfl) ⟨1137, by rfl⟩ : syracuseStep 3106133 = 2275) (by norm_num)
theorem B484717 : Blo 283827 484717 := bbase (se 3 (by rfl) ⟨90884, by rfl⟩ : syracuseStep 484717 = 181769) (by norm_num)
theorem B320881 : Blo 283827 320881 := bbase (se 2 (by rfl) ⟨120330, by rfl⟩ : syracuseStep 320881 = 240661) (by norm_num)
theorem B5203349 : Blo 283827 5203349 := bbase (se 6 (by rfl) ⟨121953, by rfl⟩ : syracuseStep 5203349 = 243907) (by norm_num)
theorem B320917 : Blo 283827 320917 := bbase (se 6 (by rfl) ⟨7521, by rfl⟩ : syracuseStep 320917 = 15043) (by norm_num)
theorem B320953 : Blo 283827 320953 := bbase (se 2 (by rfl) ⟨120357, by rfl⟩ : syracuseStep 320953 = 240715) (by norm_num)
theorem B517573 : Blo 283827 517573 := bbase (se 4 (by rfl) ⟨48522, by rfl⟩ : syracuseStep 517573 = 97045) (by norm_num)
theorem B484805 : Blo 283827 484805 := bbase (se 4 (by rfl) ⟨45450, by rfl⟩ : syracuseStep 484805 = 90901) (by norm_num)
theorem B320989 : Blo 283827 320989 := bbase (se 3 (by rfl) ⟨60185, by rfl⟩ : syracuseStep 320989 = 120371) (by norm_num)
theorem B321025 : Blo 283827 321025 := bbase (se 2 (by rfl) ⟨120384, by rfl⟩ : syracuseStep 321025 = 240769) (by norm_num)
theorem B321061 : Blo 283827 321061 := bbase (se 4 (by rfl) ⟨30099, by rfl⟩ : syracuseStep 321061 = 60199) (by norm_num)
theorem B484933 : Blo 283827 484933 := bbase (se 4 (by rfl) ⟨45462, by rfl⟩ : syracuseStep 484933 = 90925) (by norm_num)
theorem B321097 : Blo 283827 321097 := bbase (se 2 (by rfl) ⟨120411, by rfl⟩ : syracuseStep 321097 = 240823) (by norm_num)
theorem B321133 : Blo 283827 321133 := bbase (se 3 (by rfl) ⟨60212, by rfl⟩ : syracuseStep 321133 = 120425) (by norm_num)
theorem B1828469 : Blo 283827 1828469 := bbase (se 5 (by rfl) ⟨85709, by rfl⟩ : syracuseStep 1828469 = 171419) (by norm_num)
theorem B321169 : Blo 283827 321169 := bbase (se 2 (by rfl) ⟨120438, by rfl⟩ : syracuseStep 321169 = 240877) (by norm_num)
theorem B3270293 : Blo 283827 3270293 := bbase (se 6 (by rfl) ⟨76647, by rfl⟩ : syracuseStep 3270293 = 153295) (by norm_num)
theorem B485021 : Blo 283827 485021 := bbase (se 3 (by rfl) ⟨90941, by rfl⟩ : syracuseStep 485021 = 181883) (by norm_num)
theorem B321205 : Blo 283827 321205 := bbase (se 5 (by rfl) ⟨15056, by rfl⟩ : syracuseStep 321205 = 30113) (by norm_num)
theorem B321241 : Blo 283827 321241 := bbase (se 2 (by rfl) ⟨120465, by rfl⟩ : syracuseStep 321241 = 240931) (by norm_num)
theorem B583405 : Blo 283827 583405 := bbase (se 3 (by rfl) ⟨109388, by rfl⟩ : syracuseStep 583405 = 218777) (by norm_num)
theorem B321277 : Blo 283827 321277 := bbase (se 3 (by rfl) ⟨60239, by rfl⟩ : syracuseStep 321277 = 120479) (by norm_num)
theorem B485149 : Blo 283827 485149 := bbase (se 3 (by rfl) ⟨90965, by rfl⟩ : syracuseStep 485149 = 181931) (by norm_num)
theorem B321313 : Blo 283827 321313 := bbase (se 2 (by rfl) ⟨120492, by rfl⟩ : syracuseStep 321313 = 240985) (by norm_num)
theorem B386861 : Blo 283827 386861 := bbase (se 3 (by rfl) ⟨72536, by rfl⟩ : syracuseStep 386861 = 145073) (by norm_num)
theorem B321349 : Blo 283827 321349 := bbase (se 4 (by rfl) ⟨30126, by rfl⟩ : syracuseStep 321349 = 60253) (by norm_num)
theorem B321385 : Blo 283827 321385 := bbase (se 2 (by rfl) ⟨120519, by rfl⟩ : syracuseStep 321385 = 241039) (by norm_num)
theorem B485237 : Blo 283827 485237 := bbase (se 5 (by rfl) ⟨22745, by rfl⟩ : syracuseStep 485237 = 45491) (by norm_num)
theorem B321421 : Blo 283827 321421 := bbase (se 3 (by rfl) ⟨60266, by rfl⟩ : syracuseStep 321421 = 120533) (by norm_num)
theorem B321457 : Blo 283827 321457 := bbase (se 2 (by rfl) ⟨120546, by rfl⟩ : syracuseStep 321457 = 241093) (by norm_num)
theorem B321493 : Blo 283827 321493 := bbase (se 7 (by rfl) ⟨3767, by rfl⟩ : syracuseStep 321493 = 7535) (by norm_num)
theorem B387029 : Blo 283827 387029 := bbase (se 7 (by rfl) ⟨4535, by rfl⟩ : syracuseStep 387029 = 9071) (by norm_num)
theorem B485365 : Blo 283827 485365 := bbase (se 5 (by rfl) ⟨22751, by rfl⟩ : syracuseStep 485365 = 45503) (by norm_num)
theorem B321529 : Blo 283827 321529 := bbase (se 2 (by rfl) ⟨120573, by rfl⟩ : syracuseStep 321529 = 241147) (by norm_num)
theorem B780293 : Blo 283827 780293 := bbase (se 4 (by rfl) ⟨73152, by rfl⟩ : syracuseStep 780293 = 146305) (by norm_num)
theorem B387077 : Blo 283827 387077 := bbase (se 4 (by rfl) ⟨36288, by rfl⟩ : syracuseStep 387077 = 72577) (by norm_num)
theorem B321565 : Blo 283827 321565 := bbase (se 3 (by rfl) ⟨60293, by rfl⟩ : syracuseStep 321565 = 120587) (by norm_num)
theorem B321601 : Blo 283827 321601 := bbase (se 2 (by rfl) ⟨120600, by rfl⟩ : syracuseStep 321601 = 241201) (by norm_num)
theorem B485453 : Blo 283827 485453 := bbase (se 3 (by rfl) ⟨91022, by rfl⟩ : syracuseStep 485453 = 182045) (by norm_num)
theorem B321637 : Blo 283827 321637 := bbase (se 4 (by rfl) ⟨30153, by rfl⟩ : syracuseStep 321637 = 60307) (by norm_num)
theorem B288889 : Blo 283827 288889 := bbase (se 2 (by rfl) ⟨108333, by rfl⟩ : syracuseStep 288889 = 216667) (by norm_num)
theorem B321673 : Blo 283827 321673 := bbase (se 2 (by rfl) ⟨120627, by rfl⟩ : syracuseStep 321673 = 241255) (by norm_num)
theorem B321709 : Blo 283827 321709 := bbase (se 3 (by rfl) ⟨60320, by rfl⟩ : syracuseStep 321709 = 120641) (by norm_num)
theorem B485581 : Blo 283827 485581 := bbase (se 3 (by rfl) ⟨91046, by rfl⟩ : syracuseStep 485581 = 182093) (by norm_num)
theorem B321745 : Blo 283827 321745 := bbase (se 2 (by rfl) ⟨120654, by rfl⟩ : syracuseStep 321745 = 241309) (by norm_num)
theorem B321781 : Blo 283827 321781 := bbase (se 5 (by rfl) ⟨15083, by rfl⟩ : syracuseStep 321781 = 30167) (by norm_num)
theorem B321817 : Blo 283827 321817 := bbase (se 2 (by rfl) ⟨120681, by rfl⟩ : syracuseStep 321817 = 241363) (by norm_num)
theorem B485669 : Blo 283827 485669 := bbase (se 4 (by rfl) ⟨45531, by rfl⟩ : syracuseStep 485669 = 91063) (by norm_num)
theorem B321853 : Blo 283827 321853 := bbase (se 3 (by rfl) ⟨60347, by rfl⟩ : syracuseStep 321853 = 120695) (by norm_num)
theorem B321889 : Blo 283827 321889 := bbase (se 2 (by rfl) ⟨120708, by rfl⟩ : syracuseStep 321889 = 241417) (by norm_num)
theorem B616829 : Blo 283827 616829 := bbase (se 3 (by rfl) ⟨115655, by rfl⟩ : syracuseStep 616829 = 231311) (by norm_num)
theorem B321925 : Blo 283827 321925 := bbase (se 4 (by rfl) ⟨30180, by rfl⟩ : syracuseStep 321925 = 60361) (by norm_num)
theorem B289189 : Blo 283827 289189 := bbase (se 4 (by rfl) ⟨27111, by rfl⟩ : syracuseStep 289189 = 54223) (by norm_num)
theorem B321961 : Blo 283827 321961 := bbase (se 2 (by rfl) ⟨120735, by rfl⟩ : syracuseStep 321961 = 241471) (by norm_num)
theorem B321997 : Blo 283827 321997 := bbase (se 3 (by rfl) ⟨60374, by rfl⟩ : syracuseStep 321997 = 120749) (by norm_num)
theorem B322033 : Blo 283827 322033 := bbase (se 2 (by rfl) ⟨120762, by rfl⟩ : syracuseStep 322033 = 241525) (by norm_num)
theorem B322069 : Blo 283827 322069 := bbase (se 6 (by rfl) ⟨7548, by rfl⟩ : syracuseStep 322069 = 15097) (by norm_num)
theorem B322105 : Blo 283827 322105 := bbase (se 2 (by rfl) ⟨120789, by rfl⟩ : syracuseStep 322105 = 241579) (by norm_num)
theorem B322141 : Blo 283827 322141 := bbase (se 3 (by rfl) ⟨60401, by rfl⟩ : syracuseStep 322141 = 120803) (by norm_num)
theorem B322177 : Blo 283827 322177 := bbase (se 2 (by rfl) ⟨120816, by rfl⟩ : syracuseStep 322177 = 241633) (by norm_num)
theorem B813701 : Blo 283827 813701 := bbase (se 4 (by rfl) ⟨76284, by rfl⟩ : syracuseStep 813701 = 152569) (by norm_num)
theorem B1174181 : Blo 283827 1174181 := bbase (se 4 (by rfl) ⟨110079, by rfl⟩ : syracuseStep 1174181 = 220159) (by norm_num)
theorem B322213 : Blo 283827 322213 := bbase (se 4 (by rfl) ⟨30207, by rfl⟩ : syracuseStep 322213 = 60415) (by norm_num)
theorem B322249 : Blo 283827 322249 := bbase (se 2 (by rfl) ⟨120843, by rfl⟩ : syracuseStep 322249 = 241687) (by norm_num)
theorem B322285 : Blo 283827 322285 := bbase (se 3 (by rfl) ⟨60428, by rfl⟩ : syracuseStep 322285 = 120857) (by norm_num)
theorem B322321 : Blo 283827 322321 := bbase (se 2 (by rfl) ⟨120870, by rfl⟩ : syracuseStep 322321 = 241741) (by norm_num)
theorem B322357 : Blo 283827 322357 := bbase (se 5 (by rfl) ⟨15110, by rfl⟩ : syracuseStep 322357 = 30221) (by norm_num)
theorem B322393 : Blo 283827 322393 := bbase (se 2 (by rfl) ⟨120897, by rfl⟩ : syracuseStep 322393 = 241795) (by norm_num)
theorem B322429 : Blo 283827 322429 := bbase (se 3 (by rfl) ⟨60455, by rfl⟩ : syracuseStep 322429 = 120911) (by norm_num)
theorem B322465 : Blo 283827 322465 := bbase (se 2 (by rfl) ⟨120924, by rfl⟩ : syracuseStep 322465 = 241849) (by norm_num)
theorem B2747317 : Blo 283827 2747317 := bbase (se 5 (by rfl) ⟨128780, by rfl⟩ : syracuseStep 2747317 = 257561) (by norm_num)
theorem B322501 : Blo 283827 322501 := bbase (se 4 (by rfl) ⟨30234, by rfl⟩ : syracuseStep 322501 = 60469) (by norm_num)
theorem B3959765 : Blo 283827 3959765 := bbase (se 7 (by rfl) ⟨46403, by rfl⟩ : syracuseStep 3959765 = 92807) (by norm_num)
theorem B289765 : Blo 283827 289765 := bbase (se 4 (by rfl) ⟨27165, by rfl⟩ : syracuseStep 289765 = 54331) (by norm_num)
theorem B322537 : Blo 283827 322537 := bbase (se 2 (by rfl) ⟨120951, by rfl⟩ : syracuseStep 322537 = 241903) (by norm_num)
theorem B683005 : Blo 283827 683005 := bbase (se 3 (by rfl) ⟨128063, by rfl⟩ : syracuseStep 683005 = 256127) (by norm_num)
theorem B912389 : Blo 283827 912389 := bbase (se 4 (by rfl) ⟨85536, by rfl⟩ : syracuseStep 912389 = 171073) (by norm_num)
theorem B322573 : Blo 283827 322573 := bbase (se 3 (by rfl) ⟨60482, by rfl⟩ : syracuseStep 322573 = 120965) (by norm_num)
theorem B322609 : Blo 283827 322609 := bbase (se 2 (by rfl) ⟨120978, by rfl⟩ : syracuseStep 322609 = 241957) (by norm_num)
theorem B486461 : Blo 283827 486461 := bbase (se 3 (by rfl) ⟨91211, by rfl⟩ : syracuseStep 486461 = 182423) (by norm_num)
theorem B322645 : Blo 283827 322645 := bbase (se 8 (by rfl) ⟨1890, by rfl⟩ : syracuseStep 322645 = 3781) (by norm_num)
theorem B322681 : Blo 283827 322681 := bbase (se 2 (by rfl) ⟨121005, by rfl⟩ : syracuseStep 322681 = 242011) (by norm_num)
theorem B322717 : Blo 283827 322717 := bbase (se 3 (by rfl) ⟨60509, by rfl⟩ : syracuseStep 322717 = 121019) (by norm_num)
theorem B322753 : Blo 283827 322753 := bbase (se 2 (by rfl) ⟨121032, by rfl⟩ : syracuseStep 322753 = 242065) (by norm_num)
theorem B2616533 : Blo 283827 2616533 := bbase (se 7 (by rfl) ⟨30662, by rfl⟩ : syracuseStep 2616533 = 61325) (by norm_num)
theorem B322789 : Blo 283827 322789 := bbase (se 4 (by rfl) ⟨30261, by rfl⟩ : syracuseStep 322789 = 60523) (by norm_num)
theorem B322825 : Blo 283827 322825 := bbase (se 2 (by rfl) ⟨121059, by rfl⟩ : syracuseStep 322825 = 242119) (by norm_num)
theorem B322861 : Blo 283827 322861 := bbase (se 3 (by rfl) ⟨60536, by rfl⟩ : syracuseStep 322861 = 121073) (by norm_num)
theorem B322897 : Blo 283827 322897 := bbase (se 2 (by rfl) ⟨121086, by rfl⟩ : syracuseStep 322897 = 242173) (by norm_num)
theorem B322933 : Blo 283827 322933 := bbase (se 5 (by rfl) ⟨15137, by rfl⟩ : syracuseStep 322933 = 30275) (by norm_num)
theorem B1305989 : Blo 283827 1305989 := bbase (se 4 (by rfl) ⟨122436, by rfl⟩ : syracuseStep 1305989 = 244873) (by norm_num)
theorem B322969 : Blo 283827 322969 := bbase (se 2 (by rfl) ⟨121113, by rfl⟩ : syracuseStep 322969 = 242227) (by norm_num)
theorem B323005 : Blo 283827 323005 := bbase (se 3 (by rfl) ⟨60563, by rfl⟩ : syracuseStep 323005 = 121127) (by norm_num)
theorem B323041 : Blo 283827 323041 := bbase (se 2 (by rfl) ⟨121140, by rfl⟩ : syracuseStep 323041 = 242281) (by norm_num)
theorem B323077 : Blo 283827 323077 := bbase (se 4 (by rfl) ⟨30288, by rfl⟩ : syracuseStep 323077 = 60577) (by norm_num)
theorem B2321941 : Blo 283827 2321941 := bbase (se 6 (by rfl) ⟨54420, by rfl⟩ : syracuseStep 2321941 = 108841) (by norm_num)
theorem B323113 : Blo 283827 323113 := bbase (se 2 (by rfl) ⟨121167, by rfl⟩ : syracuseStep 323113 = 242335) (by norm_num)
theorem B2780725 : Blo 283827 2780725 := bbase (se 5 (by rfl) ⟨130346, by rfl⟩ : syracuseStep 2780725 = 260693) (by norm_num)
theorem B323149 : Blo 283827 323149 := bbase (se 3 (by rfl) ⟨60590, by rfl⟩ : syracuseStep 323149 = 121181) (by norm_num)
theorem B323185 : Blo 283827 323185 := bbase (se 2 (by rfl) ⟨121194, by rfl⟩ : syracuseStep 323185 = 242389) (by norm_num)
theorem B323221 : Blo 283827 323221 := bbase (se 6 (by rfl) ⟨7575, by rfl⟩ : syracuseStep 323221 = 15151) (by norm_num)
theorem B683677 : Blo 283827 683677 := bbase (se 3 (by rfl) ⟨128189, by rfl⟩ : syracuseStep 683677 = 256379) (by norm_num)
theorem B323257 : Blo 283827 323257 := bbase (se 2 (by rfl) ⟨121221, by rfl⟩ : syracuseStep 323257 = 242443) (by norm_num)
theorem B1732309 : Blo 283827 1732309 := bbase (se 7 (by rfl) ⟨20300, by rfl⟩ : syracuseStep 1732309 = 40601) (by norm_num)
theorem B323293 : Blo 283827 323293 := bbase (se 3 (by rfl) ⟨60617, by rfl⟩ : syracuseStep 323293 = 121235) (by norm_num)
theorem B2158325 : Blo 283827 2158325 := bbase (se 5 (by rfl) ⟨101171, by rfl⟩ : syracuseStep 2158325 = 202343) (by norm_num)
theorem B323329 : Blo 283827 323329 := bbase (se 2 (by rfl) ⟨121248, by rfl⟩ : syracuseStep 323329 = 242497) (by norm_num)
theorem B323365 : Blo 283827 323365 := bbase (se 4 (by rfl) ⟨30315, by rfl⟩ : syracuseStep 323365 = 60631) (by norm_num)
theorem B323401 : Blo 283827 323401 := bbase (se 2 (by rfl) ⟨121275, by rfl⟩ : syracuseStep 323401 = 242551) (by norm_num)
theorem B290665 : Blo 283827 290665 := bbase (se 2 (by rfl) ⟨108999, by rfl⟩ : syracuseStep 290665 = 217999) (by norm_num)
theorem B323437 : Blo 283827 323437 := bbase (se 3 (by rfl) ⟨60644, by rfl⟩ : syracuseStep 323437 = 121289) (by norm_num)
theorem B683909 : Blo 283827 683909 := bbase (se 4 (by rfl) ⟨64116, by rfl⟩ : syracuseStep 683909 = 128233) (by norm_num)
theorem B323473 : Blo 283827 323473 := bbase (se 2 (by rfl) ⟨121302, by rfl⟩ : syracuseStep 323473 = 242605) (by norm_num)
theorem B913301 : Blo 283827 913301 := bbase (se 6 (by rfl) ⟨21405, by rfl⟩ : syracuseStep 913301 = 42811) (by norm_num)
theorem B323509 : Blo 283827 323509 := bbase (se 5 (by rfl) ⟨15164, by rfl⟩ : syracuseStep 323509 = 30329) (by norm_num)
theorem B3502037 : Blo 283827 3502037 := bbase (se 7 (by rfl) ⟨41039, by rfl⟩ : syracuseStep 3502037 = 82079) (by norm_num)
theorem B323545 : Blo 283827 323545 := bbase (se 2 (by rfl) ⟨121329, by rfl⟩ : syracuseStep 323545 = 242659) (by norm_num)
theorem B323581 : Blo 283827 323581 := bbase (se 3 (by rfl) ⟨60671, by rfl⟩ : syracuseStep 323581 = 121343) (by norm_num)
theorem B684053 : Blo 283827 684053 := bbase (se 6 (by rfl) ⟨16032, by rfl⟩ : syracuseStep 684053 = 32065) (by norm_num)
theorem B323617 : Blo 283827 323617 := bbase (se 2 (by rfl) ⟨121356, by rfl⟩ : syracuseStep 323617 = 242713) (by norm_num)
theorem B454709 : Blo 283827 454709 := bbase (se 5 (by rfl) ⟨21314, by rfl⟩ : syracuseStep 454709 = 42629) (by norm_num)
theorem B1437749 : Blo 283827 1437749 := bbase (se 5 (by rfl) ⟨67394, by rfl⟩ : syracuseStep 1437749 = 134789) (by norm_num)
theorem B684101 : Blo 283827 684101 := bbase (se 4 (by rfl) ⟨64134, by rfl⟩ : syracuseStep 684101 = 128269) (by norm_num)
theorem B323653 : Blo 283827 323653 := bbase (se 4 (by rfl) ⟨30342, by rfl⟩ : syracuseStep 323653 = 60685) (by norm_num)
theorem B323689 : Blo 283827 323689 := bbase (se 2 (by rfl) ⟨121383, by rfl⟩ : syracuseStep 323689 = 242767) (by norm_num)
theorem B323725 : Blo 283827 323725 := bbase (se 3 (by rfl) ⟨60698, by rfl⟩ : syracuseStep 323725 = 121397) (by norm_num)
theorem B323761 : Blo 283827 323761 := bbase (se 2 (by rfl) ⟨121410, by rfl⟩ : syracuseStep 323761 = 242821) (by norm_num)
theorem B454837 : Blo 283827 454837 := bbase (se 5 (by rfl) ⟨21320, by rfl⟩ : syracuseStep 454837 = 42641) (by norm_num)
theorem B815285 : Blo 283827 815285 := bbase (se 5 (by rfl) ⟨38216, by rfl⟩ : syracuseStep 815285 = 76433) (by norm_num)
theorem B323797 : Blo 283827 323797 := bbase (se 7 (by rfl) ⟨3794, by rfl⟩ : syracuseStep 323797 = 7589) (by norm_num)
theorem B618725 : Blo 283827 618725 := bbase (se 4 (by rfl) ⟨58005, by rfl⟩ : syracuseStep 618725 = 116011) (by norm_num)
theorem B323833 : Blo 283827 323833 := bbase (se 2 (by rfl) ⟨121437, by rfl⟩ : syracuseStep 323833 = 242875) (by norm_num)
theorem B323869 : Blo 283827 323869 := bbase (se 3 (by rfl) ⟨60725, by rfl⟩ : syracuseStep 323869 = 121451) (by norm_num)
theorem B684389 : Blo 283827 684389 := bbase (se 4 (by rfl) ⟨64161, by rfl⟩ : syracuseStep 684389 = 128323) (by norm_num)
theorem B1470997 : Blo 283827 1470997 := bbase (se 6 (by rfl) ⟨34476, by rfl⟩ : syracuseStep 1470997 = 68953) (by norm_num)
theorem B455221 : Blo 283827 455221 := bbase (se 5 (by rfl) ⟨21338, by rfl⟩ : syracuseStep 455221 = 42677) (by norm_num)
theorem B1078069 : Blo 283827 1078069 := bbase (se 5 (by rfl) ⟨50534, by rfl⟩ : syracuseStep 1078069 = 101069) (by norm_num)
theorem B455477 : Blo 283827 455477 := bbase (se 5 (by rfl) ⟨21350, by rfl⟩ : syracuseStep 455477 = 42701) (by norm_num)
theorem B815957 : Blo 283827 815957 := bbase (se 9 (by rfl) ⟨2390, by rfl⟩ : syracuseStep 815957 = 4781) (by norm_num)
theorem B1078373 : Blo 283827 1078373 := bbase (se 4 (by rfl) ⟨101097, by rfl⟩ : syracuseStep 1078373 = 202195) (by norm_num)
theorem B914645 : Blo 283827 914645 := bbase (se 7 (by rfl) ⟨10718, by rfl⟩ : syracuseStep 914645 = 21437) (by norm_num)
theorem B1373429 : Blo 283827 1373429 := bbase (se 5 (by rfl) ⟨64379, by rfl⟩ : syracuseStep 1373429 = 128759) (by norm_num)
theorem B816389 : Blo 283827 816389 := bbase (se 4 (by rfl) ⟨76536, by rfl⟩ : syracuseStep 816389 = 153073) (by norm_num)
theorem B1439045 : Blo 283827 1439045 := bbase (se 4 (by rfl) ⟨134910, by rfl⟩ : syracuseStep 1439045 = 269821) (by norm_num)
theorem B1832341 : Blo 283827 1832341 := bbase (se 6 (by rfl) ⟨42945, by rfl⟩ : syracuseStep 1832341 = 85891) (by norm_num)
theorem B292405 : Blo 283827 292405 := bbase (se 5 (by rfl) ⟨13706, by rfl⟩ : syracuseStep 292405 = 27413) (by norm_num)
theorem B1373813 : Blo 283827 1373813 := bbase (se 5 (by rfl) ⟨64397, by rfl⟩ : syracuseStep 1373813 = 128795) (by norm_num)
theorem B456349 : Blo 283827 456349 := bbase (se 3 (by rfl) ⟨85565, by rfl⟩ : syracuseStep 456349 = 171131) (by norm_num)
theorem B2291381 : Blo 283827 2291381 := bbase (se 5 (by rfl) ⟨107408, by rfl⟩ : syracuseStep 2291381 = 214817) (by norm_num)
theorem B718541 : Blo 283827 718541 := bbase (se 3 (by rfl) ⟨134726, by rfl⟩ : syracuseStep 718541 = 269453) (by norm_num)
theorem B456445 : Blo 283827 456445 := bbase (se 3 (by rfl) ⟨85583, by rfl⟩ : syracuseStep 456445 = 171167) (by norm_num)
theorem B718733 : Blo 283827 718733 := bbase (se 3 (by rfl) ⟨134762, by rfl⟩ : syracuseStep 718733 = 269525) (by norm_num)
theorem B456605 : Blo 283827 456605 := bbase (se 3 (by rfl) ⟨85613, by rfl⟩ : syracuseStep 456605 = 171227) (by norm_num)
theorem B817141 : Blo 283827 817141 := bbase (se 5 (by rfl) ⟨38303, by rfl⟩ : syracuseStep 817141 = 76607) (by norm_num)
theorem B325721 : Blo 283827 325721 := bbase (se 2 (by rfl) ⟨122145, by rfl⟩ : syracuseStep 325721 = 244291) (by norm_num)
theorem B1636469 : Blo 283827 1636469 := bbase (se 5 (by rfl) ⟨76709, by rfl⟩ : syracuseStep 1636469 = 153419) (by norm_num)
theorem B1308869 : Blo 283827 1308869 := bbase (se 4 (by rfl) ⟨122706, by rfl⟩ : syracuseStep 1308869 = 245413) (by norm_num)
theorem B719077 : Blo 283827 719077 := bbase (se 4 (by rfl) ⟨67413, by rfl⟩ : syracuseStep 719077 = 134827) (by norm_num)
theorem B522517 : Blo 283827 522517 := bbase (se 6 (by rfl) ⟨12246, by rfl⟩ : syracuseStep 522517 = 24493) (by norm_num)
theorem B620821 : Blo 283827 620821 := bbase (se 6 (by rfl) ⟨14550, by rfl⟩ : syracuseStep 620821 = 29101) (by norm_num)
theorem B1308997 : Blo 283827 1308997 := bbase (se 4 (by rfl) ⟨122718, by rfl⟩ : syracuseStep 1308997 = 245437) (by norm_num)
theorem B719189 : Blo 283827 719189 := bbase (se 10 (by rfl) ⟨1053, by rfl⟩ : syracuseStep 719189 = 2107) (by norm_num)
theorem B522677 : Blo 283827 522677 := bbase (se 5 (by rfl) ⟨24500, by rfl⟩ : syracuseStep 522677 = 49001) (by norm_num)
theorem B719381 : Blo 283827 719381 := bbase (se 6 (by rfl) ⟨16860, by rfl⟩ : syracuseStep 719381 = 33721) (by norm_num)
theorem B1440341 : Blo 283827 1440341 := bbase (se 8 (by rfl) ⟨8439, by rfl⟩ : syracuseStep 1440341 = 16879) (by norm_num)
theorem B916069 : Blo 283827 916069 := bbase (se 4 (by rfl) ⟨85881, by rfl⟩ : syracuseStep 916069 = 171763) (by norm_num)
theorem B686821 : Blo 283827 686821 := bbase (se 4 (by rfl) ⟨64389, by rfl⟩ : syracuseStep 686821 = 128779) (by norm_num)
theorem B1178389 : Blo 283827 1178389 := bbase (se 6 (by rfl) ⟨27618, by rfl⟩ : syracuseStep 1178389 = 55237) (by norm_num)
theorem B359245 : Blo 283827 359245 := bbase (se 3 (by rfl) ⟨67358, by rfl⟩ : syracuseStep 359245 = 134717) (by norm_num)
theorem B719725 : Blo 283827 719725 := bbase (se 3 (by rfl) ⟨134948, by rfl⟩ : syracuseStep 719725 = 269897) (by norm_num)
theorem B719837 : Blo 283827 719837 := bbase (se 3 (by rfl) ⟨134969, by rfl⟩ : syracuseStep 719837 = 269939) (by norm_num)
theorem B359417 : Blo 283827 359417 := bbase (se 2 (by rfl) ⟨134781, by rfl⟩ : syracuseStep 359417 = 269563) (by norm_num)
theorem B457733 : Blo 283827 457733 := bbase (se 4 (by rfl) ⟨42912, by rfl⟩ : syracuseStep 457733 = 85825) (by norm_num)
theorem B326669 : Blo 283827 326669 := bbase (se 3 (by rfl) ⟨61250, by rfl⟩ : syracuseStep 326669 = 122501) (by norm_num)
theorem B359473 : Blo 283827 359473 := bbase (se 2 (by rfl) ⟨134802, by rfl⟩ : syracuseStep 359473 = 269605) (by norm_num)
theorem B359569 : Blo 283827 359569 := bbase (se 2 (by rfl) ⟨134838, by rfl⟩ : syracuseStep 359569 = 269677) (by norm_num)
theorem B720029 : Blo 283827 720029 := bbase (se 3 (by rfl) ⟨135005, by rfl⟩ : syracuseStep 720029 = 270011) (by norm_num)
theorem B1080485 : Blo 283827 1080485 := bbase (se 4 (by rfl) ⟨101295, by rfl⟩ : syracuseStep 1080485 = 202591) (by norm_num)
theorem B1965269 : Blo 283827 1965269 := bbase (se 7 (by rfl) ⟨23030, by rfl⟩ : syracuseStep 1965269 = 46061) (by norm_num)
theorem B359741 : Blo 283827 359741 := bbase (se 3 (by rfl) ⟨67451, by rfl⟩ : syracuseStep 359741 = 134903) (by norm_num)
theorem B687437 : Blo 283827 687437 := bbase (se 3 (by rfl) ⟨128894, by rfl⟩ : syracuseStep 687437 = 257789) (by norm_num)
theorem B359797 : Blo 283827 359797 := bbase (se 5 (by rfl) ⟨16865, by rfl⟩ : syracuseStep 359797 = 33731) (by norm_num)
theorem B1080773 : Blo 283827 1080773 := bbase (se 4 (by rfl) ⟨101322, by rfl⟩ : syracuseStep 1080773 = 202645) (by norm_num)
theorem B359893 : Blo 283827 359893 := bbase (se 7 (by rfl) ⟨4217, by rfl⟩ : syracuseStep 359893 = 8435) (by norm_num)
theorem B720373 : Blo 283827 720373 := bbase (se 5 (by rfl) ⟨33767, by rfl⟩ : syracuseStep 720373 = 67535) (by norm_num)
theorem B458245 : Blo 283827 458245 := bbase (se 4 (by rfl) ⟨42960, by rfl⟩ : syracuseStep 458245 = 85921) (by norm_num)
theorem B687637 : Blo 283827 687637 := bbase (se 6 (by rfl) ⟨16116, by rfl⟩ : syracuseStep 687637 = 32233) (by norm_num)
theorem B720485 : Blo 283827 720485 := bbase (se 4 (by rfl) ⟨67545, by rfl⟩ : syracuseStep 720485 = 135091) (by norm_num)
theorem B1638005 : Blo 283827 1638005 := bbase (se 5 (by rfl) ⟨76781, by rfl⟩ : syracuseStep 1638005 = 153563) (by norm_num)
theorem B360065 : Blo 283827 360065 := bbase (se 2 (by rfl) ⟨135024, by rfl⟩ : syracuseStep 360065 = 270049) (by norm_num)
theorem B360121 : Blo 283827 360121 := bbase (se 2 (by rfl) ⟨135045, by rfl⟩ : syracuseStep 360121 = 270091) (by norm_num)
theorem B425741 : Blo 283827 425741 := bbase (se 3 (by rfl) ⟨79826, by rfl⟩ : syracuseStep 425741 = 159653) (by norm_num)
theorem B360217 : Blo 283827 360217 := bbase (se 2 (by rfl) ⟨135081, by rfl⟩ : syracuseStep 360217 = 270163) (by norm_num)
theorem B425765 : Blo 283827 425765 := bbase (se 4 (by rfl) ⟨39915, by rfl⟩ : syracuseStep 425765 = 79831) (by norm_num)
theorem B720677 : Blo 283827 720677 := bbase (se 4 (by rfl) ⟨67563, by rfl⟩ : syracuseStep 720677 = 135127) (by norm_num)
theorem B425789 : Blo 283827 425789 := bbase (se 3 (by rfl) ⟨79835, by rfl⟩ : syracuseStep 425789 = 159671) (by norm_num)
theorem B425813 : Blo 283827 425813 := bbase (se 9 (by rfl) ⟨1247, by rfl⟩ : syracuseStep 425813 = 2495) (by norm_num)
theorem B1441637 : Blo 283827 1441637 := bbase (se 4 (by rfl) ⟨135153, by rfl⟩ : syracuseStep 1441637 = 270307) (by norm_num)
theorem B425837 : Blo 283827 425837 := bbase (se 3 (by rfl) ⟨79844, by rfl⟩ : syracuseStep 425837 = 159689) (by norm_num)
theorem B425861 : Blo 283827 425861 := bbase (se 4 (by rfl) ⟨39924, by rfl⟩ : syracuseStep 425861 = 79849) (by norm_num)
theorem B2326421 : Blo 283827 2326421 := bbase (se 6 (by rfl) ⟨54525, by rfl⟩ : syracuseStep 2326421 = 109051) (by norm_num)
theorem B425885 : Blo 283827 425885 := bbase (se 3 (by rfl) ⟨79853, by rfl⟩ : syracuseStep 425885 = 159707) (by norm_num)
theorem B425909 : Blo 283827 425909 := bbase (se 5 (by rfl) ⟨19964, by rfl⟩ : syracuseStep 425909 = 39929) (by norm_num)
theorem B360389 : Blo 283827 360389 := bbase (se 4 (by rfl) ⟨33786, by rfl⟩ : syracuseStep 360389 = 67573) (by norm_num)
theorem B425933 : Blo 283827 425933 := bbase (se 3 (by rfl) ⟨79862, by rfl⟩ : syracuseStep 425933 = 159725) (by norm_num)
theorem B425957 : Blo 283827 425957 := bbase (se 4 (by rfl) ⟨39933, by rfl⟩ : syracuseStep 425957 = 79867) (by norm_num)
theorem B360445 : Blo 283827 360445 := bbase (se 3 (by rfl) ⟨67583, by rfl⟩ : syracuseStep 360445 = 135167) (by norm_num)
theorem B425987 : Blo 283827 425987 := bstep (se 1 (by rfl) ⟨319490, by rfl⟩ : syracuseStep 425987 = 638981) B638981
theorem B491537 : Blo 283827 491537 := bstep (se 2 (by rfl) ⟨184326, by rfl⟩ : syracuseStep 491537 = 368653) B368653
theorem B426017 : Blo 283827 426017 := bstep (se 2 (by rfl) ⟨159756, by rfl⟩ : syracuseStep 426017 = 319513) B319513
theorem B426035 : Blo 283827 426035 := bstep (se 1 (by rfl) ⟨319526, by rfl⟩ : syracuseStep 426035 = 639053) B639053
theorem B1572941 : Blo 283827 1572941 := bstep (se 3 (by rfl) ⟨294926, by rfl⟩ : syracuseStep 1572941 = 589853) B589853
theorem B426065 : Blo 283827 426065 := bstep (se 2 (by rfl) ⟨159774, by rfl⟩ : syracuseStep 426065 = 319549) B319549
theorem B426083 : Blo 283827 426083 := bstep (se 1 (by rfl) ⟨319562, by rfl⟩ : syracuseStep 426083 = 639125) B639125
theorem B1081457 : Blo 283827 1081457 := bstep (se 2 (by rfl) ⟨405546, by rfl⟩ : syracuseStep 1081457 = 811093) B811093
theorem B426113 : Blo 283827 426113 := bstep (se 2 (by rfl) ⟨159792, by rfl⟩ : syracuseStep 426113 = 319585) B319585
theorem B983171 : Blo 283827 983171 := bstep (se 1 (by rfl) ⟨737378, by rfl⟩ : syracuseStep 983171 = 1474757) B1474757
theorem B426131 : Blo 283827 426131 := bstep (se 1 (by rfl) ⟨319598, by rfl⟩ : syracuseStep 426131 = 639197) B639197
theorem B426161 : Blo 283827 426161 := bstep (se 2 (by rfl) ⟨159810, by rfl⟩ : syracuseStep 426161 = 319621) B319621
theorem B426179 : Blo 283827 426179 := bstep (se 1 (by rfl) ⟨319634, by rfl⟩ : syracuseStep 426179 = 639269) B639269
theorem B458963 : Blo 283827 458963 := bstep (se 1 (by rfl) ⟨344222, by rfl⟩ : syracuseStep 458963 = 688445) B688445
theorem B426209 : Blo 283827 426209 := bstep (se 2 (by rfl) ⟨159828, by rfl⟩ : syracuseStep 426209 = 319657) B319657
theorem B426227 : Blo 283827 426227 := bstep (se 1 (by rfl) ⟨319670, by rfl⟩ : syracuseStep 426227 = 639341) B639341
theorem B426257 : Blo 283827 426257 := bstep (se 2 (by rfl) ⟨159846, by rfl⟩ : syracuseStep 426257 = 319693) B319693
theorem B426275 : Blo 283827 426275 := bstep (se 1 (by rfl) ⟨319706, by rfl⟩ : syracuseStep 426275 = 639413) B639413
theorem B426305 : Blo 283827 426305 := bstep (se 2 (by rfl) ⟨159864, by rfl⟩ : syracuseStep 426305 = 319729) B319729
theorem B819533 : Blo 283827 819533 := bstep (se 3 (by rfl) ⟨153662, by rfl⟩ : syracuseStep 819533 = 307325) B307325
theorem B426323 : Blo 283827 426323 := bstep (se 1 (by rfl) ⟨319742, by rfl⟩ : syracuseStep 426323 = 639485) B639485
theorem B426353 : Blo 283827 426353 := bstep (se 2 (by rfl) ⟨159882, by rfl⟩ : syracuseStep 426353 = 319765) B319765
theorem B426371 : Blo 283827 426371 := bstep (se 1 (by rfl) ⟨319778, by rfl⟩ : syracuseStep 426371 = 639557) B639557
theorem B426401 : Blo 283827 426401 := bstep (se 2 (by rfl) ⟨159900, by rfl⟩ : syracuseStep 426401 = 319801) B319801
theorem B426419 : Blo 283827 426419 := bstep (se 1 (by rfl) ⟨319814, by rfl⟩ : syracuseStep 426419 = 639629) B639629
theorem B426449 : Blo 283827 426449 := bstep (se 2 (by rfl) ⟨159918, by rfl⟩ : syracuseStep 426449 = 319837) B319837
theorem B426467 : Blo 283827 426467 := bstep (se 1 (by rfl) ⟨319850, by rfl⟩ : syracuseStep 426467 = 639701) B639701
theorem B360931 : Blo 283827 360931 := bstep (se 1 (by rfl) ⟨270698, by rfl⟩ : syracuseStep 360931 = 541397) B541397
theorem B2163185 : Blo 283827 2163185 := bstep (se 2 (by rfl) ⟨811194, by rfl⟩ : syracuseStep 2163185 = 1622389) B1622389
theorem B426497 : Blo 283827 426497 := bstep (se 2 (by rfl) ⟨159936, by rfl⟩ : syracuseStep 426497 = 319873) B319873
theorem B459265 : Blo 283827 459265 := bstep (se 2 (by rfl) ⟨172224, by rfl⟩ : syracuseStep 459265 = 344449) B344449
theorem B426515 : Blo 283827 426515 := bstep (se 1 (by rfl) ⟨319886, by rfl⟩ : syracuseStep 426515 = 639773) B639773
theorem B688675 : Blo 283827 688675 := bstep (se 1 (by rfl) ⟨516506, by rfl⟩ : syracuseStep 688675 = 1033013) B1033013
theorem B426545 : Blo 283827 426545 := bstep (se 2 (by rfl) ⟨159954, by rfl⟩ : syracuseStep 426545 = 319909) B319909
theorem B721457 : Blo 283827 721457 := bstep (se 2 (by rfl) ⟨270546, by rfl⟩ : syracuseStep 721457 = 541093) B541093
theorem B426563 : Blo 283827 426563 := bstep (se 1 (by rfl) ⟨319922, by rfl⟩ : syracuseStep 426563 = 639845) B639845
theorem B361027 : Blo 283827 361027 := bstep (se 1 (by rfl) ⟨270770, by rfl⟩ : syracuseStep 361027 = 541541) B541541
theorem B1671749 : Blo 283827 1671749 := bstep (se 4 (by rfl) ⟨156726, by rfl⟩ : syracuseStep 1671749 = 313453) B313453
theorem B426593 : Blo 283827 426593 := bstep (se 2 (by rfl) ⟨159972, by rfl⟩ : syracuseStep 426593 = 319945) B319945
theorem B721507 : Blo 283827 721507 := bstep (se 1 (by rfl) ⟨541130, by rfl⟩ : syracuseStep 721507 = 1082261) B1082261
theorem B1475185 : Blo 283827 1475185 := bstep (se 2 (by rfl) ⟨553194, by rfl⟩ : syracuseStep 1475185 = 1106389) B1106389
theorem B426611 : Blo 283827 426611 := bstep (se 1 (by rfl) ⟨319958, by rfl⟩ : syracuseStep 426611 = 639917) B639917
theorem B426641 : Blo 283827 426641 := bstep (se 2 (by rfl) ⟨159990, by rfl⟩ : syracuseStep 426641 = 319981) B319981
theorem B426659 : Blo 283827 426659 := bstep (se 1 (by rfl) ⟨319994, by rfl⟩ : syracuseStep 426659 = 639989) B639989
theorem B426689 : Blo 283827 426689 := bstep (se 2 (by rfl) ⟨160008, by rfl⟩ : syracuseStep 426689 = 320017) B320017
theorem B426707 : Blo 283827 426707 := bstep (se 1 (by rfl) ⟨320030, by rfl⟩ : syracuseStep 426707 = 640061) B640061
theorem B459475 : Blo 283827 459475 := bstep (se 1 (by rfl) ⟨344606, by rfl⟩ : syracuseStep 459475 = 689213) B689213
theorem B426737 : Blo 283827 426737 := bstep (se 2 (by rfl) ⟨160026, by rfl⟩ : syracuseStep 426737 = 320053) B320053
theorem B721649 : Blo 283827 721649 := bstep (se 2 (by rfl) ⟨270618, by rfl⟩ : syracuseStep 721649 = 541237) B541237
theorem B459521 : Blo 283827 459521 := bstep (se 2 (by rfl) ⟨172320, by rfl⟩ : syracuseStep 459521 = 344641) B344641
theorem B426755 : Blo 283827 426755 := bstep (se 1 (by rfl) ⟨320066, by rfl⟩ : syracuseStep 426755 = 640133) B640133
theorem B426785 : Blo 283827 426785 := bstep (se 2 (by rfl) ⟨160044, by rfl⟩ : syracuseStep 426785 = 320089) B320089
theorem B1442609 : Blo 283827 1442609 := bstep (se 2 (by rfl) ⟨540978, by rfl⟩ : syracuseStep 1442609 = 1081957) B1081957
theorem B426803 : Blo 283827 426803 := bstep (se 1 (by rfl) ⟨320102, by rfl⟩ : syracuseStep 426803 = 640205) B640205
theorem B426833 : Blo 283827 426833 := bstep (se 2 (by rfl) ⟨160062, by rfl⟩ : syracuseStep 426833 = 320125) B320125
theorem B426851 : Blo 283827 426851 := bstep (se 1 (by rfl) ⟨320138, by rfl⟩ : syracuseStep 426851 = 640277) B640277
theorem B426881 : Blo 283827 426881 := bstep (se 2 (by rfl) ⟨160080, by rfl⟩ : syracuseStep 426881 = 320161) B320161
theorem B426899 : Blo 283827 426899 := bstep (se 1 (by rfl) ⟨320174, by rfl⟩ : syracuseStep 426899 = 640349) B640349
theorem B426929 : Blo 283827 426929 := bstep (se 2 (by rfl) ⟨160098, by rfl⟩ : syracuseStep 426929 = 320197) B320197
theorem B426947 : Blo 283827 426947 := bstep (se 1 (by rfl) ⟨320210, by rfl⟩ : syracuseStep 426947 = 640421) B640421
theorem B1573829 : Blo 283827 1573829 := bstep (se 4 (by rfl) ⟨147546, by rfl⟩ : syracuseStep 1573829 = 295093) B295093
theorem B426977 : Blo 283827 426977 := bstep (se 2 (by rfl) ⟨160116, by rfl⟩ : syracuseStep 426977 = 320233) B320233
theorem B426995 : Blo 283827 426995 := bstep (se 1 (by rfl) ⟨320246, by rfl⟩ : syracuseStep 426995 = 640493) B640493
theorem B427025 : Blo 283827 427025 := bstep (se 2 (by rfl) ⟨160134, by rfl⟩ : syracuseStep 427025 = 320269) B320269
theorem B427043 : Blo 283827 427043 := bstep (se 1 (by rfl) ⟨320282, by rfl⟩ : syracuseStep 427043 = 640565) B640565
theorem B361523 : Blo 283827 361523 := bstep (se 1 (by rfl) ⟨271142, by rfl⟩ : syracuseStep 361523 = 542285) B542285
theorem B427073 : Blo 283827 427073 := bstep (se 2 (by rfl) ⟨160152, by rfl⟩ : syracuseStep 427073 = 320305) B320305
theorem B427091 : Blo 283827 427091 := bstep (se 1 (by rfl) ⟨320318, by rfl⟩ : syracuseStep 427091 = 640637) B640637
theorem B427121 : Blo 283827 427121 := bstep (se 2 (by rfl) ⟨160170, by rfl⟩ : syracuseStep 427121 = 320341) B320341
theorem B427139 : Blo 283827 427139 := bstep (se 1 (by rfl) ⟨320354, by rfl⟩ : syracuseStep 427139 = 640709) B640709
theorem B427169 : Blo 283827 427169 := bstep (se 2 (by rfl) ⟨160188, by rfl⟩ : syracuseStep 427169 = 320377) B320377
theorem B427187 : Blo 283827 427187 := bstep (se 1 (by rfl) ⟨320390, by rfl⟩ : syracuseStep 427187 = 640781) B640781
theorem B427217 : Blo 283827 427217 := bstep (se 2 (by rfl) ⟨160206, by rfl⟩ : syracuseStep 427217 = 320413) B320413
theorem B427235 : Blo 283827 427235 := bstep (se 1 (by rfl) ⟨320426, by rfl⟩ : syracuseStep 427235 = 640853) B640853
theorem B427265 : Blo 283827 427265 := bstep (se 2 (by rfl) ⟨160224, by rfl⟩ : syracuseStep 427265 = 320449) B320449
theorem B427283 : Blo 283827 427283 := bstep (se 1 (by rfl) ⟨320462, by rfl⟩ : syracuseStep 427283 = 640925) B640925
theorem B427313 : Blo 283827 427313 := bstep (se 2 (by rfl) ⟨160242, by rfl⟩ : syracuseStep 427313 = 320485) B320485
theorem B427331 : Blo 283827 427331 := bstep (se 1 (by rfl) ⟨320498, by rfl⟩ : syracuseStep 427331 = 640997) B640997
theorem B427361 : Blo 283827 427361 := bstep (se 2 (by rfl) ⟨160260, by rfl⟩ : syracuseStep 427361 = 320521) B320521
theorem B427379 : Blo 283827 427379 := bstep (se 1 (by rfl) ⟨320534, by rfl⟩ : syracuseStep 427379 = 641069) B641069
theorem B427409 : Blo 283827 427409 := bstep (se 2 (by rfl) ⟨160278, by rfl⟩ : syracuseStep 427409 = 320557) B320557
theorem B427427 : Blo 283827 427427 := bstep (se 1 (by rfl) ⟨320570, by rfl⟩ : syracuseStep 427427 = 641141) B641141
theorem B427457 : Blo 283827 427457 := bstep (se 2 (by rfl) ⟨160296, by rfl⟩ : syracuseStep 427457 = 320593) B320593
theorem B427475 : Blo 283827 427475 := bstep (se 1 (by rfl) ⟨320606, by rfl⟩ : syracuseStep 427475 = 641213) B641213
theorem B427505 : Blo 283827 427505 := bstep (se 2 (by rfl) ⟨160314, by rfl⟩ : syracuseStep 427505 = 320629) B320629
theorem B427523 : Blo 283827 427523 := bstep (se 1 (by rfl) ⟨320642, by rfl⟩ : syracuseStep 427523 = 641285) B641285
theorem B427553 : Blo 283827 427553 := bstep (se 2 (by rfl) ⟨160332, by rfl⟩ : syracuseStep 427553 = 320665) B320665
theorem B1082915 : Blo 283827 1082915 := bstep (se 1 (by rfl) ⟨812186, by rfl⟩ : syracuseStep 1082915 = 1624373) B1624373
theorem B1082929 : Blo 283827 1082929 := bstep (se 2 (by rfl) ⟨406098, by rfl⟩ : syracuseStep 1082929 = 812197) B812197
theorem B427571 : Blo 283827 427571 := bstep (se 1 (by rfl) ⟨320678, by rfl⟩ : syracuseStep 427571 = 641357) B641357
theorem B427601 : Blo 283827 427601 := bstep (se 2 (by rfl) ⟨160350, by rfl⟩ : syracuseStep 427601 = 320701) B320701
theorem B427619 : Blo 283827 427619 := bstep (se 1 (by rfl) ⟨320714, by rfl⟩ : syracuseStep 427619 = 641429) B641429
theorem B427649 : Blo 283827 427649 := bstep (se 2 (by rfl) ⟨160368, by rfl⟩ : syracuseStep 427649 = 320737) B320737
theorem B427667 : Blo 283827 427667 := bstep (se 1 (by rfl) ⟨320750, by rfl⟩ : syracuseStep 427667 = 641501) B641501
theorem B427697 : Blo 283827 427697 := bstep (se 2 (by rfl) ⟨160386, by rfl⟩ : syracuseStep 427697 = 320773) B320773
theorem B427715 : Blo 283827 427715 := bstep (se 1 (by rfl) ⟨320786, by rfl⟩ : syracuseStep 427715 = 641573) B641573
theorem B722641 : Blo 283827 722641 := bstep (se 2 (by rfl) ⟨270990, by rfl⟩ : syracuseStep 722641 = 541981) B541981
theorem B427745 : Blo 283827 427745 := bstep (se 2 (by rfl) ⟨160404, by rfl⟩ : syracuseStep 427745 = 320809) B320809
theorem B7374563 : Blo 283827 7374563 := bstep (se 1 (by rfl) ⟨5530922, by rfl⟩ : syracuseStep 7374563 = 11061845) B11061845
theorem B689905 : Blo 283827 689905 := bstep (se 2 (by rfl) ⟨258714, by rfl⟩ : syracuseStep 689905 = 517429) B517429
theorem B427763 : Blo 283827 427763 := bstep (se 1 (by rfl) ⟨320822, by rfl⟩ : syracuseStep 427763 = 641645) B641645
theorem B362227 : Blo 283827 362227 := bstep (se 1 (by rfl) ⟨271670, by rfl⟩ : syracuseStep 362227 = 543341) B543341
theorem B427793 : Blo 283827 427793 := bstep (se 2 (by rfl) ⟨160422, by rfl⟩ : syracuseStep 427793 = 320845) B320845
theorem B427811 : Blo 283827 427811 := bstep (se 1 (by rfl) ⟨320858, by rfl⟩ : syracuseStep 427811 = 641717) B641717
theorem B427841 : Blo 283827 427841 := bstep (se 2 (by rfl) ⟨160440, by rfl⟩ : syracuseStep 427841 = 320881) B320881
theorem B427859 : Blo 283827 427859 := bstep (se 1 (by rfl) ⟨320894, by rfl⟩ : syracuseStep 427859 = 641789) B641789
theorem B362323 : Blo 283827 362323 := bstep (se 1 (by rfl) ⟨271742, by rfl⟩ : syracuseStep 362323 = 543485) B543485
theorem B427889 : Blo 283827 427889 := bstep (se 2 (by rfl) ⟨160458, by rfl⟩ : syracuseStep 427889 = 320917) B320917
theorem B427907 : Blo 283827 427907 := bstep (se 1 (by rfl) ⟨320930, by rfl⟩ : syracuseStep 427907 = 641861) B641861
theorem B427937 : Blo 283827 427937 := bstep (se 2 (by rfl) ⟨160476, by rfl⟩ : syracuseStep 427937 = 320953) B320953
theorem B427955 : Blo 283827 427955 := bstep (se 1 (by rfl) ⟨320966, by rfl⟩ : syracuseStep 427955 = 641933) B641933
theorem B427985 : Blo 283827 427985 := bstep (se 2 (by rfl) ⟨160494, by rfl⟩ : syracuseStep 427985 = 320989) B320989
theorem B428003 : Blo 283827 428003 := bstep (se 1 (by rfl) ⟨321002, by rfl⟩ : syracuseStep 428003 = 642005) B642005
theorem B722915 : Blo 283827 722915 := bstep (se 1 (by rfl) ⟨542186, by rfl⟩ : syracuseStep 722915 = 1084373) B1084373
theorem B428033 : Blo 283827 428033 := bstep (se 2 (by rfl) ⟨160512, by rfl⟩ : syracuseStep 428033 = 321025) B321025
theorem B428051 : Blo 283827 428051 := bstep (se 1 (by rfl) ⟨321038, by rfl⟩ : syracuseStep 428051 = 642077) B642077
theorem B428081 : Blo 283827 428081 := bstep (se 2 (by rfl) ⟨160530, by rfl⟩ : syracuseStep 428081 = 321061) B321061
theorem B428099 : Blo 283827 428099 := bstep (se 1 (by rfl) ⟨321074, by rfl⟩ : syracuseStep 428099 = 642149) B642149
theorem B428129 : Blo 283827 428129 := bstep (se 2 (by rfl) ⟨160548, by rfl⟩ : syracuseStep 428129 = 321097) B321097
theorem B2328689 : Blo 283827 2328689 := bstep (se 2 (by rfl) ⟨873258, by rfl⟩ : syracuseStep 2328689 = 1746517) B1746517
theorem B428147 : Blo 283827 428147 := bstep (se 1 (by rfl) ⟨321110, by rfl⟩ : syracuseStep 428147 = 642221) B642221
theorem B493697 : Blo 283827 493697 := bstep (se 2 (by rfl) ⟨185136, by rfl⟩ : syracuseStep 493697 = 370273) B370273
theorem B1214605 : Blo 283827 1214605 := bstep (se 3 (by rfl) ⟨227738, by rfl⟩ : syracuseStep 1214605 = 455477) B455477
theorem B428177 : Blo 283827 428177 := bstep (se 2 (by rfl) ⟨160566, by rfl⟩ : syracuseStep 428177 = 321133) B321133
theorem B428195 : Blo 283827 428195 := bstep (se 1 (by rfl) ⟨321146, by rfl⟩ : syracuseStep 428195 = 642293) B642293
theorem B723107 : Blo 283827 723107 := bstep (se 1 (by rfl) ⟨542330, by rfl⟩ : syracuseStep 723107 = 1084661) B1084661
theorem B428225 : Blo 283827 428225 := bstep (se 2 (by rfl) ⟨160584, by rfl⟩ : syracuseStep 428225 = 321169) B321169
theorem B1542341 : Blo 283827 1542341 := bstep (se 4 (by rfl) ⟨144594, by rfl⟩ : syracuseStep 1542341 = 289189) B289189
theorem B428243 : Blo 283827 428243 := bstep (se 1 (by rfl) ⟨321182, by rfl⟩ : syracuseStep 428243 = 642365) B642365
theorem B1444067 : Blo 283827 1444067 := bstep (se 1 (by rfl) ⟨1083050, by rfl⟩ : syracuseStep 1444067 = 2166101) B2166101
theorem B461027 : Blo 283827 461027 := bstep (se 1 (by rfl) ⟨345770, by rfl⟩ : syracuseStep 461027 = 691541) B691541
theorem B428273 : Blo 283827 428273 := bstep (se 2 (by rfl) ⟨160602, by rfl⟩ : syracuseStep 428273 = 321205) B321205
theorem B428291 : Blo 283827 428291 := bstep (se 1 (by rfl) ⟨321218, by rfl⟩ : syracuseStep 428291 = 642437) B642437
theorem B428321 : Blo 283827 428321 := bstep (se 2 (by rfl) ⟨160620, by rfl⟩ : syracuseStep 428321 = 321241) B321241
theorem B428339 : Blo 283827 428339 := bstep (se 1 (by rfl) ⟨321254, by rfl⟩ : syracuseStep 428339 = 642509) B642509
theorem B362819 : Blo 283827 362819 := bstep (se 1 (by rfl) ⟨272114, by rfl⟩ : syracuseStep 362819 = 544229) B544229
theorem B428369 : Blo 283827 428369 := bstep (se 2 (by rfl) ⟨160638, by rfl⟩ : syracuseStep 428369 = 321277) B321277
theorem B428387 : Blo 283827 428387 := bstep (se 1 (by rfl) ⟨321290, by rfl⟩ : syracuseStep 428387 = 642581) B642581
theorem B7473521 : Blo 283827 7473521 := bstep (se 2 (by rfl) ⟨2802570, by rfl⟩ : syracuseStep 7473521 = 5605141) B5605141
theorem B428417 : Blo 283827 428417 := bstep (se 2 (by rfl) ⟨160656, by rfl⟩ : syracuseStep 428417 = 321313) B321313
theorem B428435 : Blo 283827 428435 := bstep (se 1 (by rfl) ⟨321326, by rfl⟩ : syracuseStep 428435 = 642653) B642653
theorem B428465 : Blo 283827 428465 := bstep (se 2 (by rfl) ⟨160674, by rfl⟩ : syracuseStep 428465 = 321349) B321349
theorem B428483 : Blo 283827 428483 := bstep (se 1 (by rfl) ⟨321362, by rfl⟩ : syracuseStep 428483 = 642725) B642725
theorem B428513 : Blo 283827 428513 := bstep (se 2 (by rfl) ⟨160692, by rfl⟩ : syracuseStep 428513 = 321385) B321385
theorem B428531 : Blo 283827 428531 := bstep (se 1 (by rfl) ⟨321398, by rfl⟩ : syracuseStep 428531 = 642797) B642797
theorem B428561 : Blo 283827 428561 := bstep (se 2 (by rfl) ⟨160710, by rfl⟩ : syracuseStep 428561 = 321421) B321421
theorem B6162965 : Blo 283827 6162965 := bstep (se 6 (by rfl) ⟨144444, by rfl⟩ : syracuseStep 6162965 = 288889) B288889
theorem B428579 : Blo 283827 428579 := bstep (se 1 (by rfl) ⟨321434, by rfl⟩ : syracuseStep 428579 = 642869) B642869
theorem B428609 : Blo 283827 428609 := bstep (se 2 (by rfl) ⟨160728, by rfl⟩ : syracuseStep 428609 = 321457) B321457
theorem B428627 : Blo 283827 428627 := bstep (se 1 (by rfl) ⟨321470, by rfl⟩ : syracuseStep 428627 = 642941) B642941
theorem B428657 : Blo 283827 428657 := bstep (se 2 (by rfl) ⟨160746, by rfl⟩ : syracuseStep 428657 = 321493) B321493
theorem B428675 : Blo 283827 428675 := bstep (se 1 (by rfl) ⟨321506, by rfl⟩ : syracuseStep 428675 = 643013) B643013
theorem B428705 : Blo 283827 428705 := bstep (se 2 (by rfl) ⟨160764, by rfl⟩ : syracuseStep 428705 = 321529) B321529
theorem B428723 : Blo 283827 428723 := bstep (se 1 (by rfl) ⟨321542, by rfl⟩ : syracuseStep 428723 = 643085) B643085
theorem B428753 : Blo 283827 428753 := bstep (se 2 (by rfl) ⟨160782, by rfl⟩ : syracuseStep 428753 = 321565) B321565
theorem B428771 : Blo 283827 428771 := bstep (se 1 (by rfl) ⟨321578, by rfl⟩ : syracuseStep 428771 = 643157) B643157
theorem B428801 : Blo 283827 428801 := bstep (se 2 (by rfl) ⟨160800, by rfl⟩ : syracuseStep 428801 = 321601) B321601
theorem B428819 : Blo 283827 428819 := bstep (se 1 (by rfl) ⟨321614, by rfl⟩ : syracuseStep 428819 = 643229) B643229
theorem B428849 : Blo 283827 428849 := bstep (se 2 (by rfl) ⟨160818, by rfl⟩ : syracuseStep 428849 = 321637) B321637
theorem B428867 : Blo 283827 428867 := bstep (se 1 (by rfl) ⟨321650, by rfl⟩ : syracuseStep 428867 = 643301) B643301
theorem B1542989 : Blo 283827 1542989 := bstep (se 3 (by rfl) ⟨289310, by rfl⟩ : syracuseStep 1542989 = 578621) B578621
theorem B428897 : Blo 283827 428897 := bstep (se 2 (by rfl) ⟨160836, by rfl⟩ : syracuseStep 428897 = 321673) B321673
theorem B428915 : Blo 283827 428915 := bstep (se 1 (by rfl) ⟨321686, by rfl⟩ : syracuseStep 428915 = 643373) B643373
theorem B428945 : Blo 283827 428945 := bstep (se 2 (by rfl) ⟨160854, by rfl⟩ : syracuseStep 428945 = 321709) B321709
theorem B428963 : Blo 283827 428963 := bstep (se 1 (by rfl) ⟨321722, by rfl⟩ : syracuseStep 428963 = 643445) B643445
theorem B428993 : Blo 283827 428993 := bstep (se 2 (by rfl) ⟨160872, by rfl⟩ : syracuseStep 428993 = 321745) B321745
theorem B1543117 : Blo 283827 1543117 := bstep (se 3 (by rfl) ⟨289334, by rfl⟩ : syracuseStep 1543117 = 578669) B578669
theorem B429011 : Blo 283827 429011 := bstep (se 1 (by rfl) ⟨321758, by rfl⟩ : syracuseStep 429011 = 643517) B643517
theorem B1084387 : Blo 283827 1084387 := bstep (se 1 (by rfl) ⟨813290, by rfl⟩ : syracuseStep 1084387 = 1626581) B1626581
theorem B429041 : Blo 283827 429041 := bstep (se 2 (by rfl) ⟨160890, by rfl⟩ : syracuseStep 429041 = 321781) B321781
theorem B429059 : Blo 283827 429059 := bstep (se 1 (by rfl) ⟨321794, by rfl⟩ : syracuseStep 429059 = 643589) B643589
theorem B363523 : Blo 283827 363523 := bstep (se 1 (by rfl) ⟨272642, by rfl⟩ : syracuseStep 363523 = 545285) B545285
theorem B1444877 : Blo 283827 1444877 := bstep (se 3 (by rfl) ⟨270914, by rfl⟩ : syracuseStep 1444877 = 541829) B541829
theorem B429089 : Blo 283827 429089 := bstep (se 2 (by rfl) ⟨160908, by rfl⟩ : syracuseStep 429089 = 321817) B321817
theorem B429107 : Blo 283827 429107 := bstep (se 1 (by rfl) ⟨321830, by rfl⟩ : syracuseStep 429107 = 643661) B643661
theorem B724049 : Blo 283827 724049 := bstep (se 2 (by rfl) ⟨271518, by rfl⟩ : syracuseStep 724049 = 543037) B543037
theorem B429137 : Blo 283827 429137 := bstep (se 2 (by rfl) ⟨160926, by rfl⟩ : syracuseStep 429137 = 321853) B321853
theorem B429155 : Blo 283827 429155 := bstep (se 1 (by rfl) ⟨321866, by rfl⟩ : syracuseStep 429155 = 643733) B643733
theorem B363619 : Blo 283827 363619 := bstep (se 1 (by rfl) ⟨272714, by rfl⟩ : syracuseStep 363619 = 545429) B545429
theorem B429185 : Blo 283827 429185 := bstep (se 2 (by rfl) ⟨160944, by rfl⟩ : syracuseStep 429185 = 321889) B321889
theorem B724099 : Blo 283827 724099 := bstep (se 1 (by rfl) ⟨543074, by rfl⟩ : syracuseStep 724099 = 1086149) B1086149
theorem B429203 : Blo 283827 429203 := bstep (se 1 (by rfl) ⟨321902, by rfl⟩ : syracuseStep 429203 = 643805) B643805
theorem B429233 : Blo 283827 429233 := bstep (se 2 (by rfl) ⟨160962, by rfl⟩ : syracuseStep 429233 = 321925) B321925
theorem B429251 : Blo 283827 429251 := bstep (se 1 (by rfl) ⟨321938, by rfl⟩ : syracuseStep 429251 = 643877) B643877
theorem B429281 : Blo 283827 429281 := bstep (se 2 (by rfl) ⟨160980, by rfl⟩ : syracuseStep 429281 = 321961) B321961
theorem B5508323 : Blo 283827 5508323 := bstep (se 1 (by rfl) ⟨4131242, by rfl⟩ : syracuseStep 5508323 = 8262485) B8262485
theorem B429299 : Blo 283827 429299 := bstep (se 1 (by rfl) ⟨321974, by rfl⟩ : syracuseStep 429299 = 643949) B643949
theorem B724241 : Blo 283827 724241 := bstep (se 2 (by rfl) ⟨271590, by rfl⟩ : syracuseStep 724241 = 543181) B543181
theorem B429329 : Blo 283827 429329 := bstep (se 2 (by rfl) ⟨160998, by rfl⟩ : syracuseStep 429329 = 321997) B321997
theorem B429347 : Blo 283827 429347 := bstep (se 1 (by rfl) ⟨322010, by rfl⟩ : syracuseStep 429347 = 644021) B644021
theorem B429377 : Blo 283827 429377 := bstep (se 2 (by rfl) ⟨161016, by rfl⟩ : syracuseStep 429377 = 322033) B322033
theorem B429395 : Blo 283827 429395 := bstep (se 1 (by rfl) ⟨322046, by rfl⟩ : syracuseStep 429395 = 644093) B644093
theorem B429425 : Blo 283827 429425 := bstep (se 2 (by rfl) ⟨161034, by rfl⟩ : syracuseStep 429425 = 322069) B322069
theorem B429443 : Blo 283827 429443 := bstep (se 1 (by rfl) ⟨322082, by rfl⟩ : syracuseStep 429443 = 644165) B644165
theorem B429473 : Blo 283827 429473 := bstep (se 2 (by rfl) ⟨161052, by rfl⟩ : syracuseStep 429473 = 322105) B322105
theorem B429491 : Blo 283827 429491 := bstep (se 1 (by rfl) ⟨322118, by rfl⟩ : syracuseStep 429491 = 644237) B644237
theorem B429521 : Blo 283827 429521 := bstep (se 2 (by rfl) ⟨161070, by rfl⟩ : syracuseStep 429521 = 322141) B322141
theorem B429539 : Blo 283827 429539 := bstep (se 1 (by rfl) ⟨322154, by rfl⟩ : syracuseStep 429539 = 644309) B644309
theorem B429569 : Blo 283827 429569 := bstep (se 2 (by rfl) ⟨161088, by rfl⟩ : syracuseStep 429569 = 322177) B322177
theorem B429587 : Blo 283827 429587 := bstep (se 1 (by rfl) ⟨322190, by rfl⟩ : syracuseStep 429587 = 644381) B644381
theorem B429617 : Blo 283827 429617 := bstep (se 2 (by rfl) ⟨161106, by rfl⟩ : syracuseStep 429617 = 322213) B322213
theorem B429635 : Blo 283827 429635 := bstep (se 1 (by rfl) ⟨322226, by rfl⟩ : syracuseStep 429635 = 644453) B644453
theorem B364115 : Blo 283827 364115 := bstep (se 1 (by rfl) ⟨273086, by rfl⟩ : syracuseStep 364115 = 546173) B546173
theorem B429665 : Blo 283827 429665 := bstep (se 2 (by rfl) ⟨161124, by rfl⟩ : syracuseStep 429665 = 322249) B322249
theorem B429683 : Blo 283827 429683 := bstep (se 1 (by rfl) ⟨322262, by rfl⟩ : syracuseStep 429683 = 644525) B644525
theorem B429713 : Blo 283827 429713 := bstep (se 2 (by rfl) ⟨161142, by rfl⟩ : syracuseStep 429713 = 322285) B322285
theorem B921233 : Blo 283827 921233 := bstep (se 2 (by rfl) ⟨345462, by rfl⟩ : syracuseStep 921233 = 690925) B690925
theorem B429731 : Blo 283827 429731 := bstep (se 1 (by rfl) ⟨322298, by rfl⟩ : syracuseStep 429731 = 644597) B644597
theorem B429761 : Blo 283827 429761 := bstep (se 2 (by rfl) ⟨161160, by rfl⟩ : syracuseStep 429761 = 322321) B322321
theorem B429779 : Blo 283827 429779 := bstep (se 1 (by rfl) ⟨322334, by rfl⟩ : syracuseStep 429779 = 644669) B644669
theorem B429809 : Blo 283827 429809 := bstep (se 2 (by rfl) ⟨161178, by rfl⟩ : syracuseStep 429809 = 322357) B322357
theorem B429827 : Blo 283827 429827 := bstep (se 1 (by rfl) ⟨322370, by rfl⟩ : syracuseStep 429827 = 644741) B644741
theorem B429857 : Blo 283827 429857 := bstep (se 2 (by rfl) ⟨161196, by rfl⟩ : syracuseStep 429857 = 322393) B322393
theorem B429875 : Blo 283827 429875 := bstep (se 1 (by rfl) ⟨322406, by rfl⟩ : syracuseStep 429875 = 644813) B644813
theorem B429905 : Blo 283827 429905 := bstep (se 2 (by rfl) ⟨161214, by rfl⟩ : syracuseStep 429905 = 322429) B322429
theorem B429923 : Blo 283827 429923 := bstep (se 1 (by rfl) ⟨322442, by rfl⟩ : syracuseStep 429923 = 644885) B644885
theorem B429953 : Blo 283827 429953 := bstep (se 2 (by rfl) ⟨161232, by rfl⟩ : syracuseStep 429953 = 322465) B322465
theorem B429971 : Blo 283827 429971 := bstep (se 1 (by rfl) ⟨322478, by rfl⟩ : syracuseStep 429971 = 644957) B644957
theorem B430001 : Blo 283827 430001 := bstep (se 2 (by rfl) ⟨161250, by rfl⟩ : syracuseStep 430001 = 322501) B322501
theorem B430019 : Blo 283827 430019 := bstep (se 1 (by rfl) ⟨322514, by rfl⟩ : syracuseStep 430019 = 645029) B645029
theorem B430049 : Blo 283827 430049 := bstep (se 2 (by rfl) ⟨161268, by rfl⟩ : syracuseStep 430049 = 322537) B322537
theorem B430067 : Blo 283827 430067 := bstep (se 1 (by rfl) ⟨322550, by rfl⟩ : syracuseStep 430067 = 645101) B645101
theorem B430097 : Blo 283827 430097 := bstep (se 2 (by rfl) ⟨161286, by rfl⟩ : syracuseStep 430097 = 322573) B322573
theorem B430115 : Blo 283827 430115 := bstep (se 1 (by rfl) ⟨322586, by rfl⟩ : syracuseStep 430115 = 645173) B645173
theorem B430145 : Blo 283827 430145 := bstep (se 2 (by rfl) ⟨161304, by rfl⟩ : syracuseStep 430145 = 322609) B322609
theorem B430163 : Blo 283827 430163 := bstep (se 1 (by rfl) ⟨322622, by rfl⟩ : syracuseStep 430163 = 645245) B645245
theorem B430193 : Blo 283827 430193 := bstep (se 2 (by rfl) ⟨161322, by rfl⟩ : syracuseStep 430193 = 322645) B322645
theorem B430211 : Blo 283827 430211 := bstep (se 1 (by rfl) ⟨322658, by rfl⟩ : syracuseStep 430211 = 645317) B645317
theorem B2330765 : Blo 283827 2330765 := bstep (se 3 (by rfl) ⟨437018, by rfl⟩ : syracuseStep 2330765 = 874037) B874037
theorem B430241 : Blo 283827 430241 := bstep (se 2 (by rfl) ⟨161340, by rfl⟩ : syracuseStep 430241 = 322681) B322681
theorem B430259 : Blo 283827 430259 := bstep (se 1 (by rfl) ⟨322694, by rfl⟩ : syracuseStep 430259 = 645389) B645389
theorem B430289 : Blo 283827 430289 := bstep (se 2 (by rfl) ⟨161358, by rfl⟩ : syracuseStep 430289 = 322717) B322717
theorem B659683 : Blo 283827 659683 := bstep (se 1 (by rfl) ⟨494762, by rfl⟩ : syracuseStep 659683 = 989525) B989525
theorem B430307 : Blo 283827 430307 := bstep (se 1 (by rfl) ⟨322730, by rfl⟩ : syracuseStep 430307 = 645461) B645461
theorem B725233 : Blo 283827 725233 := bstep (se 2 (by rfl) ⟨271962, by rfl⟩ : syracuseStep 725233 = 543925) B543925
theorem B430337 : Blo 283827 430337 := bstep (se 2 (by rfl) ⟨161376, by rfl⟩ : syracuseStep 430337 = 322753) B322753
theorem B430355 : Blo 283827 430355 := bstep (se 1 (by rfl) ⟨322766, by rfl⟩ : syracuseStep 430355 = 645533) B645533
theorem B430385 : Blo 283827 430385 := bstep (se 2 (by rfl) ⟨161394, by rfl⟩ : syracuseStep 430385 = 322789) B322789
theorem B430403 : Blo 283827 430403 := bstep (se 1 (by rfl) ⟨322802, by rfl⟩ : syracuseStep 430403 = 645605) B645605
theorem B430433 : Blo 283827 430433 := bstep (se 2 (by rfl) ⟨161412, by rfl⟩ : syracuseStep 430433 = 322825) B322825
theorem B856433 : Blo 283827 856433 := bstep (se 2 (by rfl) ⟨321162, by rfl⟩ : syracuseStep 856433 = 642325) B642325
theorem B430451 : Blo 283827 430451 := bstep (se 1 (by rfl) ⟨322838, by rfl⟩ : syracuseStep 430451 = 645677) B645677
theorem B430481 : Blo 283827 430481 := bstep (se 2 (by rfl) ⟨161430, by rfl⟩ : syracuseStep 430481 = 322861) B322861
theorem B430499 : Blo 283827 430499 := bstep (se 1 (by rfl) ⟨322874, by rfl⟩ : syracuseStep 430499 = 645749) B645749
theorem B430529 : Blo 283827 430529 := bstep (se 2 (by rfl) ⟨161448, by rfl⟩ : syracuseStep 430529 = 322897) B322897
theorem B430547 : Blo 283827 430547 := bstep (se 1 (by rfl) ⟨322910, by rfl⟩ : syracuseStep 430547 = 645821) B645821
theorem B430577 : Blo 283827 430577 := bstep (se 2 (by rfl) ⟨161466, by rfl⟩ : syracuseStep 430577 = 322933) B322933
theorem B725507 : Blo 283827 725507 := bstep (se 1 (by rfl) ⟨544130, by rfl⟩ : syracuseStep 725507 = 1088261) B1088261
theorem B430595 : Blo 283827 430595 := bstep (se 1 (by rfl) ⟨322946, by rfl⟩ : syracuseStep 430595 = 645893) B645893
theorem B430625 : Blo 283827 430625 := bstep (se 2 (by rfl) ⟨161484, by rfl⟩ : syracuseStep 430625 = 322969) B322969
theorem B430643 : Blo 283827 430643 := bstep (se 1 (by rfl) ⟨322982, by rfl⟩ : syracuseStep 430643 = 645965) B645965
theorem B430673 : Blo 283827 430673 := bstep (se 2 (by rfl) ⟨161502, by rfl⟩ : syracuseStep 430673 = 323005) B323005
theorem B430691 : Blo 283827 430691 := bstep (se 1 (by rfl) ⟨323018, by rfl⟩ : syracuseStep 430691 = 646037) B646037
theorem B10359409 : Blo 283827 10359409 := bstep (se 2 (by rfl) ⟨3884778, by rfl⟩ : syracuseStep 10359409 = 7769557) B7769557
theorem B430721 : Blo 283827 430721 := bstep (se 2 (by rfl) ⟨161520, by rfl⟩ : syracuseStep 430721 = 323041) B323041
theorem B430739 : Blo 283827 430739 := bstep (se 1 (by rfl) ⟨323054, by rfl⟩ : syracuseStep 430739 = 646109) B646109
theorem B430769 : Blo 283827 430769 := bstep (se 2 (by rfl) ⟨161538, by rfl⟩ : syracuseStep 430769 = 323077) B323077
theorem B725699 : Blo 283827 725699 := bstep (se 1 (by rfl) ⟨544274, by rfl⟩ : syracuseStep 725699 = 1088549) B1088549
theorem B430787 : Blo 283827 430787 := bstep (se 1 (by rfl) ⟨323090, by rfl⟩ : syracuseStep 430787 = 646181) B646181
theorem B430817 : Blo 283827 430817 := bstep (se 2 (by rfl) ⟨161556, by rfl⟩ : syracuseStep 430817 = 323113) B323113
theorem B3707633 : Blo 283827 3707633 := bstep (se 2 (by rfl) ⟨1390362, by rfl⟩ : syracuseStep 3707633 = 2780725) B2780725
theorem B430835 : Blo 283827 430835 := bstep (se 1 (by rfl) ⟨323126, by rfl⟩ : syracuseStep 430835 = 646253) B646253
theorem B430865 : Blo 283827 430865 := bstep (se 2 (by rfl) ⟨161574, by rfl⟩ : syracuseStep 430865 = 323149) B323149
theorem B430883 : Blo 283827 430883 := bstep (se 1 (by rfl) ⟨323162, by rfl⟩ : syracuseStep 430883 = 646325) B646325
theorem B430913 : Blo 283827 430913 := bstep (se 2 (by rfl) ⟨161592, by rfl⟩ : syracuseStep 430913 = 323185) B323185
theorem B430931 : Blo 283827 430931 := bstep (se 1 (by rfl) ⟨323198, by rfl⟩ : syracuseStep 430931 = 646397) B646397
theorem B430961 : Blo 283827 430961 := bstep (se 2 (by rfl) ⟨161610, by rfl⟩ : syracuseStep 430961 = 323221) B323221
theorem B430979 : Blo 283827 430979 := bstep (se 1 (by rfl) ⟨323234, by rfl⟩ : syracuseStep 430979 = 646469) B646469
theorem B431009 : Blo 283827 431009 := bstep (se 2 (by rfl) ⟨161628, by rfl⟩ : syracuseStep 431009 = 323257) B323257
theorem B431027 : Blo 283827 431027 := bstep (se 1 (by rfl) ⟨323270, by rfl⟩ : syracuseStep 431027 = 646541) B646541
theorem B431057 : Blo 283827 431057 := bstep (se 2 (by rfl) ⟨161646, by rfl⟩ : syracuseStep 431057 = 323293) B323293
theorem B431075 : Blo 283827 431075 := bstep (se 1 (by rfl) ⟨323306, by rfl⟩ : syracuseStep 431075 = 646613) B646613
theorem B431105 : Blo 283827 431105 := bstep (se 2 (by rfl) ⟨161664, by rfl⟩ : syracuseStep 431105 = 323329) B323329
theorem B431123 : Blo 283827 431123 := bstep (se 1 (by rfl) ⟨323342, by rfl⟩ : syracuseStep 431123 = 646685) B646685
theorem B431153 : Blo 283827 431153 := bstep (se 2 (by rfl) ⟨161682, by rfl⟩ : syracuseStep 431153 = 323365) B323365
theorem B431171 : Blo 283827 431171 := bstep (se 1 (by rfl) ⟨323378, by rfl⟩ : syracuseStep 431171 = 646757) B646757
theorem B431201 : Blo 283827 431201 := bstep (se 2 (by rfl) ⟨161700, by rfl⟩ : syracuseStep 431201 = 323401) B323401
theorem B431219 : Blo 283827 431219 := bstep (se 1 (by rfl) ⟨323414, by rfl⟩ : syracuseStep 431219 = 646829) B646829
theorem B1086605 : Blo 283827 1086605 := bstep (se 3 (by rfl) ⟨203738, by rfl⟩ : syracuseStep 1086605 = 407477) B407477
theorem B431249 : Blo 283827 431249 := bstep (se 2 (by rfl) ⟨161718, by rfl⟩ : syracuseStep 431249 = 323437) B323437
theorem B431267 : Blo 283827 431267 := bstep (se 1 (by rfl) ⟨323450, by rfl⟩ : syracuseStep 431267 = 646901) B646901
theorem B431297 : Blo 283827 431297 := bstep (se 2 (by rfl) ⟨161736, by rfl⟩ : syracuseStep 431297 = 323473) B323473
theorem B365779 : Blo 283827 365779 := bstep (se 1 (by rfl) ⟨274334, by rfl⟩ : syracuseStep 365779 = 548669) B548669
theorem B431315 : Blo 283827 431315 := bstep (se 1 (by rfl) ⟨323486, by rfl⟩ : syracuseStep 431315 = 646973) B646973
theorem B431345 : Blo 283827 431345 := bstep (se 2 (by rfl) ⟨161754, by rfl⟩ : syracuseStep 431345 = 323509) B323509
theorem B431363 : Blo 283827 431363 := bstep (se 1 (by rfl) ⟨323522, by rfl⟩ : syracuseStep 431363 = 647045) B647045
theorem B431393 : Blo 283827 431393 := bstep (se 2 (by rfl) ⟨161772, by rfl⟩ : syracuseStep 431393 = 323545) B323545
theorem B431411 : Blo 283827 431411 := bstep (se 1 (by rfl) ⟨323558, by rfl⟩ : syracuseStep 431411 = 647117) B647117
theorem B431441 : Blo 283827 431441 := bstep (se 2 (by rfl) ⟨161790, by rfl⟩ : syracuseStep 431441 = 323581) B323581
theorem B431459 : Blo 283827 431459 := bstep (se 1 (by rfl) ⟨323594, by rfl⟩ : syracuseStep 431459 = 647189) B647189
theorem B431489 : Blo 283827 431489 := bstep (se 2 (by rfl) ⟨161808, by rfl⟩ : syracuseStep 431489 = 323617) B323617
theorem B12719501 : Blo 283827 12719501 := bstep (se 3 (by rfl) ⟨2384906, by rfl⟩ : syracuseStep 12719501 = 4769813) B4769813
theorem B431507 : Blo 283827 431507 := bstep (se 1 (by rfl) ⟨323630, by rfl⟩ : syracuseStep 431507 = 647261) B647261
theorem B431537 : Blo 283827 431537 := bstep (se 2 (by rfl) ⟨161826, by rfl⟩ : syracuseStep 431537 = 323653) B323653
theorem B431555 : Blo 283827 431555 := bstep (se 1 (by rfl) ⟨323666, by rfl⟩ : syracuseStep 431555 = 647333) B647333
theorem B431585 : Blo 283827 431585 := bstep (se 2 (by rfl) ⟨161844, by rfl⟩ : syracuseStep 431585 = 323689) B323689
theorem B3282403 : Blo 283827 3282403 := bstep (se 1 (by rfl) ⟨2461802, by rfl⟩ : syracuseStep 3282403 = 4923605) B4923605
theorem B431603 : Blo 283827 431603 := bstep (se 1 (by rfl) ⟨323702, by rfl⟩ : syracuseStep 431603 = 647405) B647405
theorem B431633 : Blo 283827 431633 := bstep (se 2 (by rfl) ⟨161862, by rfl⟩ : syracuseStep 431633 = 323725) B323725
theorem B431651 : Blo 283827 431651 := bstep (se 1 (by rfl) ⟨323738, by rfl⟩ : syracuseStep 431651 = 647477) B647477
theorem B431681 : Blo 283827 431681 := bstep (se 2 (by rfl) ⟨161880, by rfl⟩ : syracuseStep 431681 = 323761) B323761
theorem B431699 : Blo 283827 431699 := bstep (se 1 (by rfl) ⟨323774, by rfl⟩ : syracuseStep 431699 = 647549) B647549
theorem B726641 : Blo 283827 726641 := bstep (se 2 (by rfl) ⟨272490, by rfl⟩ : syracuseStep 726641 = 544981) B544981
theorem B431729 : Blo 283827 431729 := bstep (se 2 (by rfl) ⟨161898, by rfl⟩ : syracuseStep 431729 = 323797) B323797
theorem B3937933 : Blo 283827 3937933 := bstep (se 3 (by rfl) ⟨738362, by rfl⟩ : syracuseStep 3937933 = 1476725) B1476725
theorem B431777 : Blo 283827 431777 := bstep (se 2 (by rfl) ⟨161916, by rfl⟩ : syracuseStep 431777 = 323833) B323833
theorem B726691 : Blo 283827 726691 := bstep (se 1 (by rfl) ⟨545018, by rfl⟩ : syracuseStep 726691 = 1090037) B1090037
theorem B431825 : Blo 283827 431825 := bstep (se 2 (by rfl) ⟨161934, by rfl⟩ : syracuseStep 431825 = 323869) B323869
theorem B726833 : Blo 283827 726833 := bstep (se 2 (by rfl) ⟨272562, by rfl⟩ : syracuseStep 726833 = 545125) B545125
theorem B1447793 : Blo 283827 1447793 := bstep (se 2 (by rfl) ⟨542922, by rfl⟩ : syracuseStep 1447793 = 1085845) B1085845
theorem B2070755 : Blo 283827 2070755 := bstep (se 1 (by rfl) ⟨1553066, by rfl⟩ : syracuseStep 2070755 = 3106133) B3106133
theorem B1644877 : Blo 283827 1644877 := bstep (se 3 (by rfl) ⟨308414, by rfl⟩ : syracuseStep 1644877 = 616829) B616829
theorem B1218979 : Blo 283827 1218979 := bstep (se 1 (by rfl) ⟨914234, by rfl⟩ : syracuseStep 1218979 = 1828469) B1828469
theorem B727825 : Blo 283827 727825 := bstep (se 2 (by rfl) ⟨272934, by rfl⟩ : syracuseStep 727825 = 545869) B545869
theorem B728099 : Blo 283827 728099 := bstep (se 1 (by rfl) ⟨546074, by rfl⟩ : syracuseStep 728099 = 1092149) B1092149
theorem B3677237 : Blo 283827 3677237 := bstep (se 5 (by rfl) ⟨172370, by rfl⟩ : syracuseStep 3677237 = 344741) B344741
theorem B728291 : Blo 283827 728291 := bstep (se 1 (by rfl) ⟨546218, by rfl⟩ : syracuseStep 728291 = 1092437) B1092437
theorem B1449251 : Blo 283827 1449251 := bstep (se 1 (by rfl) ⟨1086938, by rfl⟩ : syracuseStep 1449251 = 2173877) B2173877
theorem B1744355 : Blo 283827 1744355 := bstep (se 1 (by rfl) ⟨1308266, by rfl⟩ : syracuseStep 1744355 = 2616533) B2616533
theorem B1842821 : Blo 283827 1842821 := bstep (se 4 (by rfl) ⟨172764, by rfl⟩ : syracuseStep 1842821 = 345529) B345529
theorem B2760389 : Blo 283827 2760389 := bstep (se 4 (by rfl) ⟨258786, by rfl⟩ : syracuseStep 2760389 = 517573) B517573
theorem B2334691 : Blo 283827 2334691 := bstep (se 1 (by rfl) ⟨1751018, by rfl⟩ : syracuseStep 2334691 = 3502037) B3502037
theorem B958445 : Blo 283827 958445 := bstep (se 3 (by rfl) ⟨179708, by rfl⟩ : syracuseStep 958445 = 359417) B359417
theorem B1089521 : Blo 283827 1089521 := bstep (se 2 (by rfl) ⟨408570, by rfl⟩ : syracuseStep 1089521 = 817141) B817141
theorem B2433037 : Blo 283827 2433037 := bstep (se 3 (by rfl) ⟨456194, by rfl⟩ : syracuseStep 2433037 = 912389) B912389
theorem B7282709 : Blo 283827 7282709 := bstep (se 6 (by rfl) ⟨170688, by rfl⟩ : syracuseStep 7282709 = 341377) B341377
theorem B303139 : Blo 283827 303139 := bstep (se 1 (by rfl) ⟨227354, by rfl⟩ : syracuseStep 303139 = 454709) B454709
theorem B958499 : Blo 283827 958499 := bstep (se 1 (by rfl) ⟨718874, by rfl⟩ : syracuseStep 958499 = 1437749) B1437749
theorem B1450061 : Blo 283827 1450061 := bstep (se 3 (by rfl) ⟨271886, by rfl⟩ : syracuseStep 1450061 = 543773) B543773
theorem B958769 : Blo 283827 958769 := bstep (se 2 (by rfl) ⟨359538, by rfl⟩ : syracuseStep 958769 = 719077) B719077
theorem B696689 : Blo 283827 696689 := bstep (se 2 (by rfl) ⟨261258, by rfl⟩ : syracuseStep 696689 = 522517) B522517
theorem B827761 : Blo 283827 827761 := bstep (se 2 (by rfl) ⟨310410, by rfl⟩ : syracuseStep 827761 = 620821) B620821
theorem B1745329 : Blo 283827 1745329 := bstep (se 2 (by rfl) ⟨654498, by rfl⟩ : syracuseStep 1745329 = 1308997) B1308997
theorem B1221425 : Blo 283827 1221425 := bstep (se 2 (by rfl) ⟨458034, by rfl⟩ : syracuseStep 1221425 = 916069) B916069
theorem B1844045 : Blo 283827 1844045 := bstep (se 3 (by rfl) ⟨345758, by rfl⟩ : syracuseStep 1844045 = 691517) B691517
theorem B959309 : Blo 283827 959309 := bstep (se 3 (by rfl) ⟨179870, by rfl⟩ : syracuseStep 959309 = 359741) B359741
theorem B959363 : Blo 283827 959363 := bstep (se 1 (by rfl) ⟨719522, by rfl⟩ : syracuseStep 959363 = 1439045) B1439045
theorem B730019 : Blo 283827 730019 := bstep (se 1 (by rfl) ⟨547514, by rfl⟩ : syracuseStep 730019 = 1095029) B1095029
theorem B926765 : Blo 283827 926765 := bstep (se 3 (by rfl) ⟨173768, by rfl⟩ : syracuseStep 926765 = 347537) B347537
theorem B959633 : Blo 283827 959633 := bstep (se 2 (by rfl) ⟨359862, by rfl⟩ : syracuseStep 959633 = 719725) B719725
theorem B2073869 : Blo 283827 2073869 := bstep (se 3 (by rfl) ⟨388850, by rfl⟩ : syracuseStep 2073869 = 777701) B777701
theorem B304403 : Blo 283827 304403 := bstep (se 1 (by rfl) ⟨228302, by rfl⟩ : syracuseStep 304403 = 456605) B456605
theorem B2434373 : Blo 283827 2434373 := bstep (se 4 (by rfl) ⟨228222, by rfl⟩ : syracuseStep 2434373 = 456445) B456445
theorem B1090979 : Blo 283827 1090979 := bstep (se 1 (by rfl) ⟨818234, by rfl⟩ : syracuseStep 1090979 = 1636469) B1636469
theorem B4368013 : Blo 283827 4368013 := bstep (se 3 (by rfl) ⟨819002, by rfl⟩ : syracuseStep 4368013 = 1638005) B1638005
theorem B960173 : Blo 283827 960173 := bstep (se 3 (by rfl) ⟨180032, by rfl⟩ : syracuseStep 960173 = 360065) B360065
theorem B960227 : Blo 283827 960227 := bstep (se 1 (by rfl) ⟨720170, by rfl⟩ : syracuseStep 960227 = 1440341) B1440341
theorem B960497 : Blo 283827 960497 := bstep (se 2 (by rfl) ⟨360186, by rfl⟩ : syracuseStep 960497 = 720373) B720373
theorem B305155 : Blo 283827 305155 := bstep (se 1 (by rfl) ⟨228866, by rfl⟩ : syracuseStep 305155 = 457733) B457733
theorem B1943813 : Blo 283827 1943813 := bstep (se 4 (by rfl) ⟨182232, by rfl⟩ : syracuseStep 1943813 = 364465) B364465
theorem B1026353 : Blo 283827 1026353 := bstep (se 2 (by rfl) ⟨384882, by rfl⟩ : syracuseStep 1026353 = 769765) B769765
theorem B1059149 : Blo 283827 1059149 := bstep (se 3 (by rfl) ⟨198590, by rfl⟩ : syracuseStep 1059149 = 397181) B397181
theorem B6203789 : Blo 283827 6203789 := bstep (se 3 (by rfl) ⟨1163210, by rfl⟩ : syracuseStep 6203789 = 2326421) B2326421
theorem B1091981 : Blo 283827 1091981 := bstep (se 3 (by rfl) ⟨204746, by rfl⟩ : syracuseStep 1091981 = 409493) B409493
theorem B961037 : Blo 283827 961037 := bstep (se 3 (by rfl) ⟨180194, by rfl⟩ : syracuseStep 961037 = 360389) B360389
theorem B961091 : Blo 283827 961091 := bstep (se 1 (by rfl) ⟨720818, by rfl⟩ : syracuseStep 961091 = 1441637) B1441637
theorem B928529 : Blo 283827 928529 := bstep (se 2 (by rfl) ⟨348198, by rfl⟩ : syracuseStep 928529 = 696397) B696397
theorem B961361 : Blo 283827 961361 := bstep (se 2 (by rfl) ⟨360510, by rfl⟩ : syracuseStep 961361 = 721021) B721021
theorem B1682309 : Blo 283827 1682309 := bstep (se 4 (by rfl) ⟨157716, by rfl⟩ : syracuseStep 1682309 = 315433) B315433
theorem B1452977 : Blo 283827 1452977 := bstep (se 2 (by rfl) ⟨544866, by rfl⟩ : syracuseStep 1452977 = 1089733) B1089733
theorem B699313 : Blo 283827 699313 := bstep (se 2 (by rfl) ⟨262242, by rfl⟩ : syracuseStep 699313 = 524485) B524485
theorem B306163 : Blo 283827 306163 := bstep (se 1 (by rfl) ⟨229622, by rfl⟩ : syracuseStep 306163 = 459245) B459245
theorem B404561 : Blo 283827 404561 := bstep (se 2 (by rfl) ⟨151710, by rfl⟩ : syracuseStep 404561 = 303421) B303421
theorem B11775203 : Blo 283827 11775203 := bstep (se 1 (by rfl) ⟨8831402, by rfl⟩ : syracuseStep 11775203 = 17662805) B17662805
theorem B2764003 : Blo 283827 2764003 := bstep (se 1 (by rfl) ⟨2073002, by rfl⟩ : syracuseStep 2764003 = 4146005) B4146005
theorem B1649933 : Blo 283827 1649933 := bstep (se 3 (by rfl) ⟨309362, by rfl⟩ : syracuseStep 1649933 = 618725) B618725
theorem B732451 : Blo 283827 732451 := bstep (se 1 (by rfl) ⟨549338, by rfl⟩ : syracuseStep 732451 = 1098677) B1098677
theorem B961901 : Blo 283827 961901 := bstep (se 3 (by rfl) ⟨180356, by rfl⟩ : syracuseStep 961901 = 360713) B360713
theorem B961955 : Blo 283827 961955 := bstep (se 1 (by rfl) ⟨721466, by rfl⟩ : syracuseStep 961955 = 1442933) B1442933
theorem B405091 : Blo 283827 405091 := bstep (se 1 (by rfl) ⟨303818, by rfl⟩ : syracuseStep 405091 = 607637) B607637
theorem B929411 : Blo 283827 929411 := bstep (se 1 (by rfl) ⟨697058, by rfl⟩ : syracuseStep 929411 = 1394117) B1394117
theorem B962225 : Blo 283827 962225 := bstep (se 2 (by rfl) ⟨360834, by rfl⟩ : syracuseStep 962225 = 721669) B721669
theorem B864017 : Blo 283827 864017 := bstep (se 2 (by rfl) ⟨324006, by rfl⟩ : syracuseStep 864017 = 648013) B648013
theorem B700177 : Blo 283827 700177 := bstep (se 2 (by rfl) ⟨262566, by rfl⟩ : syracuseStep 700177 = 525133) B525133
theorem B405427 : Blo 283827 405427 := bstep (se 1 (by rfl) ⟨304070, by rfl⟩ : syracuseStep 405427 = 608141) B608141
theorem B307171 : Blo 283827 307171 := bstep (se 1 (by rfl) ⟨230378, by rfl⟩ : syracuseStep 307171 = 460757) B460757
theorem B6697073 : Blo 283827 6697073 := bstep (se 2 (by rfl) ⟨2511402, by rfl⟩ : syracuseStep 6697073 = 5022805) B5022805
theorem B962765 : Blo 283827 962765 := bstep (se 3 (by rfl) ⟨180518, by rfl⟩ : syracuseStep 962765 = 361037) B361037
theorem B962819 : Blo 283827 962819 := bstep (se 1 (by rfl) ⟨722114, by rfl⟩ : syracuseStep 962819 = 1444229) B1444229
theorem B1454435 : Blo 283827 1454435 := bstep (se 1 (by rfl) ⟨1090826, by rfl⟩ : syracuseStep 1454435 = 2181653) B2181653
theorem B1618289 : Blo 283827 1618289 := bstep (se 2 (by rfl) ⟨606858, by rfl⟩ : syracuseStep 1618289 = 1213717) B1213717
theorem B1225165 : Blo 283827 1225165 := bstep (se 3 (by rfl) ⟨229718, by rfl⟩ : syracuseStep 1225165 = 459437) B459437
theorem B405985 : Blo 283827 405985 := bstep (se 2 (by rfl) ⟨152244, by rfl⟩ : syracuseStep 405985 = 304489) B304489
theorem B406019 : Blo 283827 406019 := bstep (se 1 (by rfl) ⟨304514, by rfl⟩ : syracuseStep 406019 = 609029) B609029
theorem B963089 : Blo 283827 963089 := bstep (se 2 (by rfl) ⟨361158, by rfl⟩ : syracuseStep 963089 = 722317) B722317
theorem B1913507 : Blo 283827 1913507 := bstep (se 1 (by rfl) ⟨1435130, by rfl⟩ : syracuseStep 1913507 = 2870261) B2870261
theorem B1094627 : Blo 283827 1094627 := bstep (se 1 (by rfl) ⟨820970, by rfl⟩ : syracuseStep 1094627 = 1641941) B1641941
theorem B963629 : Blo 283827 963629 := bstep (se 3 (by rfl) ⟨180680, by rfl⟩ : syracuseStep 963629 = 361361) B361361
theorem B406577 : Blo 283827 406577 := bstep (se 2 (by rfl) ⟨152466, by rfl⟩ : syracuseStep 406577 = 304933) B304933
theorem B963683 : Blo 283827 963683 := bstep (se 1 (by rfl) ⟨722762, by rfl⟩ : syracuseStep 963683 = 1445525) B1445525
theorem B406657 : Blo 283827 406657 := bstep (se 2 (by rfl) ⟨152496, by rfl⟩ : syracuseStep 406657 = 304993) B304993
theorem B1455245 : Blo 283827 1455245 := bstep (se 3 (by rfl) ⟨272858, by rfl⟩ : syracuseStep 1455245 = 545717) B545717
theorem B865475 : Blo 283827 865475 := bstep (se 1 (by rfl) ⟨649106, by rfl⟩ : syracuseStep 865475 = 1298213) B1298213
theorem B963953 : Blo 283827 963953 := bstep (se 2 (by rfl) ⟨361482, by rfl⟩ : syracuseStep 963953 = 722965) B722965
theorem B1848845 : Blo 283827 1848845 := bstep (se 3 (by rfl) ⟨346658, by rfl⟩ : syracuseStep 1848845 = 693317) B693317
theorem B1554061 : Blo 283827 1554061 := bstep (se 3 (by rfl) ⟨291386, by rfl⟩ : syracuseStep 1554061 = 582773) B582773
theorem B1619747 : Blo 283827 1619747 := bstep (se 1 (by rfl) ⟨1214810, by rfl⟩ : syracuseStep 1619747 = 2429621) B2429621
theorem B964493 : Blo 283827 964493 := bstep (se 3 (by rfl) ⟨180842, by rfl⟩ : syracuseStep 964493 = 361685) B361685
theorem B1161101 : Blo 283827 1161101 := bstep (se 3 (by rfl) ⟨217706, by rfl⟩ : syracuseStep 1161101 = 435413) B435413
theorem B407443 : Blo 283827 407443 := bstep (se 1 (by rfl) ⟨305582, by rfl⟩ : syracuseStep 407443 = 611165) B611165
theorem B964547 : Blo 283827 964547 := bstep (se 1 (by rfl) ⟨723410, by rfl⟩ : syracuseStep 964547 = 1446821) B1446821
theorem B767971 : Blo 283827 767971 := bstep (se 1 (by rfl) ⟨575978, by rfl⟩ : syracuseStep 767971 = 1151957) B1151957
theorem B3684365 : Blo 283827 3684365 := bstep (se 3 (by rfl) ⟨690818, by rfl⟩ : syracuseStep 3684365 = 1381637) B1381637
theorem B964817 : Blo 283827 964817 := bstep (se 2 (by rfl) ⟨361806, by rfl⟩ : syracuseStep 964817 = 723613) B723613
theorem B2439395 : Blo 283827 2439395 := bstep (se 1 (by rfl) ⟨1829546, by rfl⟩ : syracuseStep 2439395 = 3659093) B3659093
theorem B538883 : Blo 283827 538883 := bstep (se 1 (by rfl) ⟨404162, by rfl⟩ : syracuseStep 538883 = 808325) B808325
theorem B407921 : Blo 283827 407921 := bstep (se 2 (by rfl) ⟨152970, by rfl⟩ : syracuseStep 407921 = 305941) B305941
theorem B408035 : Blo 283827 408035 := bstep (se 1 (by rfl) ⟨306026, by rfl⟩ : syracuseStep 408035 = 612053) B612053
theorem B408115 : Blo 283827 408115 := bstep (se 1 (by rfl) ⟨306086, by rfl⟩ : syracuseStep 408115 = 612173) B612173
theorem B1948387 : Blo 283827 1948387 := bstep (se 1 (by rfl) ⟨1461290, by rfl⟩ : syracuseStep 1948387 = 2922581) B2922581
theorem B965357 : Blo 283827 965357 := bstep (se 3 (by rfl) ⟨181004, by rfl⟩ : syracuseStep 965357 = 362009) B362009
theorem B1620749 : Blo 283827 1620749 := bstep (se 3 (by rfl) ⟨303890, by rfl⟩ : syracuseStep 1620749 = 607781) B607781
theorem B965411 : Blo 283827 965411 := bstep (se 1 (by rfl) ⟨724058, by rfl⟩ : syracuseStep 965411 = 1448117) B1448117
theorem B965681 : Blo 283827 965681 := bstep (se 2 (by rfl) ⟨362130, by rfl⟩ : syracuseStep 965681 = 724261) B724261
theorem B408673 : Blo 283827 408673 := bstep (se 2 (by rfl) ⟨153252, by rfl⟩ : syracuseStep 408673 = 306505) B306505
theorem B539779 : Blo 283827 539779 := bstep (se 1 (by rfl) ⟨404834, by rfl⟩ : syracuseStep 539779 = 809669) B809669
theorem B933041 : Blo 283827 933041 := bstep (se 2 (by rfl) ⟨349890, by rfl⟩ : syracuseStep 933041 = 699781) B699781
theorem B343219 : Blo 283827 343219 := bstep (se 1 (by rfl) ⟨257414, by rfl⟩ : syracuseStep 343219 = 514829) B514829
theorem B539939 : Blo 283827 539939 := bstep (se 1 (by rfl) ⟨404954, by rfl⟩ : syracuseStep 539939 = 809909) B809909
theorem B3095921 : Blo 283827 3095921 := bstep (se 2 (by rfl) ⟨1160970, by rfl⟩ : syracuseStep 3095921 = 2321941) B2321941
theorem B769475 : Blo 283827 769475 := bstep (se 1 (by rfl) ⟨577106, by rfl⟩ : syracuseStep 769475 = 1154213) B1154213
theorem B5848517 : Blo 283827 5848517 := bstep (se 4 (by rfl) ⟨548298, by rfl⟩ : syracuseStep 5848517 = 1096597) B1096597
theorem B1031629 : Blo 283827 1031629 := bstep (se 3 (by rfl) ⟨193430, by rfl⟩ : syracuseStep 1031629 = 386861) B386861
theorem B769571 : Blo 283827 769571 := bstep (se 1 (by rfl) ⟨577178, by rfl⟩ : syracuseStep 769571 = 1154357) B1154357
theorem B966221 : Blo 283827 966221 := bstep (se 3 (by rfl) ⟨181166, by rfl⟩ : syracuseStep 966221 = 362333) B362333
theorem B966275 : Blo 283827 966275 := bstep (se 1 (by rfl) ⟨724706, by rfl⟩ : syracuseStep 966275 = 1449413) B1449413
theorem B409379 : Blo 283827 409379 := bstep (se 1 (by rfl) ⟨307034, by rfl⟩ : syracuseStep 409379 = 614069) B614069
theorem B638801 : Blo 283827 638801 := bstep (se 2 (by rfl) ⟨239550, by rfl⟩ : syracuseStep 638801 = 479101) B479101
theorem B638819 : Blo 283827 638819 := bstep (se 1 (by rfl) ⟨479114, by rfl⟩ : syracuseStep 638819 = 958229) B958229
theorem B1032077 : Blo 283827 1032077 := bstep (se 3 (by rfl) ⟨193514, by rfl⟩ : syracuseStep 1032077 = 387029) B387029
theorem B966545 : Blo 283827 966545 := bstep (se 2 (by rfl) ⟨362454, by rfl⟩ : syracuseStep 966545 = 724909) B724909
theorem B4440005 : Blo 283827 4440005 := bstep (se 4 (by rfl) ⟨416250, by rfl⟩ : syracuseStep 4440005 = 832501) B832501
theorem B1032205 : Blo 283827 1032205 := bstep (se 3 (by rfl) ⟨193538, by rfl⟩ : syracuseStep 1032205 = 387077) B387077
theorem B639089 : Blo 283827 639089 := bstep (se 2 (by rfl) ⟨239658, by rfl⟩ : syracuseStep 639089 = 479317) B479317
theorem B639107 : Blo 283827 639107 := bstep (se 1 (by rfl) ⟨479330, by rfl⟩ : syracuseStep 639107 = 958661) B958661
theorem B409747 : Blo 283827 409747 := bstep (se 1 (by rfl) ⟨307310, by rfl⟩ : syracuseStep 409747 = 614621) B614621
theorem B868589 : Blo 283827 868589 := bstep (se 3 (by rfl) ⟨162860, by rfl⟩ : syracuseStep 868589 = 325721) B325721
theorem B606449 : Blo 283827 606449 := bstep (se 2 (by rfl) ⟨227418, by rfl⟩ : syracuseStep 606449 = 454837) B454837
theorem B541009 : Blo 283827 541009 := bstep (se 2 (by rfl) ⟨202878, by rfl⟩ : syracuseStep 541009 = 405757) B405757
theorem B639377 : Blo 283827 639377 := bstep (se 2 (by rfl) ⟨239766, by rfl⟩ : syracuseStep 639377 = 479533) B479533
theorem B639395 : Blo 283827 639395 := bstep (se 1 (by rfl) ⟨479546, by rfl⟩ : syracuseStep 639395 = 959093) B959093
theorem B967085 : Blo 283827 967085 := bstep (se 3 (by rfl) ⟨181328, by rfl⟩ : syracuseStep 967085 = 362657) B362657
theorem B967139 : Blo 283827 967139 := bstep (se 1 (by rfl) ⟨725354, by rfl⟩ : syracuseStep 967139 = 1450709) B1450709
theorem B2048611 : Blo 283827 2048611 := bstep (se 1 (by rfl) ⟨1536458, by rfl⟩ : syracuseStep 2048611 = 3072917) B3072917
theorem B639665 : Blo 283827 639665 := bstep (se 2 (by rfl) ⟨239874, by rfl⟩ : syracuseStep 639665 = 479749) B479749
theorem B639683 : Blo 283827 639683 := bstep (se 1 (by rfl) ⟨479762, by rfl⟩ : syracuseStep 639683 = 959525) B959525
theorem B606961 : Blo 283827 606961 := bstep (se 2 (by rfl) ⟨227610, by rfl⟩ : syracuseStep 606961 = 455221) B455221
theorem B967409 : Blo 283827 967409 := bstep (se 2 (by rfl) ⟨362778, by rfl⟩ : syracuseStep 967409 = 725557) B725557
theorem B1295153 : Blo 283827 1295153 := bstep (se 2 (by rfl) ⟨485682, by rfl⟩ : syracuseStep 1295153 = 971365) B971365
theorem B639953 : Blo 283827 639953 := bstep (se 2 (by rfl) ⟨239982, by rfl⟩ : syracuseStep 639953 = 479965) B479965
theorem B639971 : Blo 283827 639971 := bstep (se 1 (by rfl) ⟨479978, by rfl⟩ : syracuseStep 639971 = 959957) B959957
theorem B2180195 : Blo 283827 2180195 := bstep (se 1 (by rfl) ⟨1635146, by rfl⟩ : syracuseStep 2180195 = 3270293) B3270293
theorem B640241 : Blo 283827 640241 := bstep (se 2 (by rfl) ⟨240090, by rfl⟩ : syracuseStep 640241 = 480181) B480181
theorem B640259 : Blo 283827 640259 := bstep (se 1 (by rfl) ⟨480194, by rfl⟩ : syracuseStep 640259 = 960389) B960389
theorem B967949 : Blo 283827 967949 := bstep (se 3 (by rfl) ⟨181490, by rfl⟩ : syracuseStep 967949 = 362981) B362981
theorem B968003 : Blo 283827 968003 := bstep (se 1 (by rfl) ⟨726002, by rfl⟩ : syracuseStep 968003 = 1452005) B1452005
theorem B542065 : Blo 283827 542065 := bstep (se 2 (by rfl) ⟨203274, by rfl⟩ : syracuseStep 542065 = 406549) B406549
theorem B640529 : Blo 283827 640529 := bstep (se 2 (by rfl) ⟨240198, by rfl⟩ : syracuseStep 640529 = 480397) B480397
theorem B640547 : Blo 283827 640547 := bstep (se 1 (by rfl) ⟨480410, by rfl⟩ : syracuseStep 640547 = 960821) B960821
theorem B968273 : Blo 283827 968273 := bstep (se 2 (by rfl) ⟨363102, by rfl⟩ : syracuseStep 968273 = 726205) B726205
theorem B1623665 : Blo 283827 1623665 := bstep (se 2 (by rfl) ⟨608874, by rfl⟩ : syracuseStep 1623665 = 1217749) B1217749
theorem B542467 : Blo 283827 542467 := bstep (se 1 (by rfl) ⟨406850, by rfl⟩ : syracuseStep 542467 = 813701) B813701
theorem B3131149 : Blo 283827 3131149 := bstep (se 3 (by rfl) ⟨587090, by rfl⟩ : syracuseStep 3131149 = 1174181) B1174181
theorem B640817 : Blo 283827 640817 := bstep (se 2 (by rfl) ⟨240306, by rfl⟩ : syracuseStep 640817 = 480613) B480613
theorem B542513 : Blo 283827 542513 := bstep (se 2 (by rfl) ⟨203442, by rfl⟩ : syracuseStep 542513 = 406885) B406885
theorem B640835 : Blo 283827 640835 := bstep (se 1 (by rfl) ⟨480626, by rfl⟩ : syracuseStep 640835 = 961253) B961253
theorem B2443121 : Blo 283827 2443121 := bstep (se 2 (by rfl) ⟨916170, by rfl⟩ : syracuseStep 2443121 = 1832341) B1832341
theorem B444371 : Blo 283827 444371 := bstep (se 1 (by rfl) ⟨333278, by rfl⟩ : syracuseStep 444371 = 666557) B666557
theorem B2639843 : Blo 283827 2639843 := bstep (se 1 (by rfl) ⟨1979882, by rfl⟩ : syracuseStep 2639843 = 3959765) B3959765
theorem B2738245 : Blo 283827 2738245 := bstep (se 4 (by rfl) ⟨256710, by rfl⟩ : syracuseStep 2738245 = 513421) B513421
theorem B641105 : Blo 283827 641105 := bstep (se 2 (by rfl) ⟨240414, by rfl⟩ : syracuseStep 641105 = 480829) B480829
theorem B542801 : Blo 283827 542801 := bstep (se 2 (by rfl) ⟨203550, by rfl⟩ : syracuseStep 542801 = 407101) B407101
theorem B641123 : Blo 283827 641123 := bstep (se 1 (by rfl) ⟨480842, by rfl⟩ : syracuseStep 641123 = 961685) B961685
theorem B968813 : Blo 283827 968813 := bstep (se 3 (by rfl) ⟨181652, by rfl⟩ : syracuseStep 968813 = 363305) B363305
theorem B968867 : Blo 283827 968867 := bstep (se 1 (by rfl) ⟨726650, by rfl⟩ : syracuseStep 968867 = 1453301) B1453301
theorem B608465 : Blo 283827 608465 := bstep (se 2 (by rfl) ⟨228174, by rfl⟩ : syracuseStep 608465 = 456349) B456349
theorem B870659 : Blo 283827 870659 := bstep (se 1 (by rfl) ⟨652994, by rfl⟩ : syracuseStep 870659 = 1305989) B1305989
theorem B641393 : Blo 283827 641393 := bstep (se 2 (by rfl) ⟨240522, by rfl⟩ : syracuseStep 641393 = 481045) B481045
theorem B641411 : Blo 283827 641411 := bstep (se 1 (by rfl) ⟨481058, by rfl⟩ : syracuseStep 641411 = 962117) B962117
theorem B969137 : Blo 283827 969137 := bstep (se 2 (by rfl) ⟨363426, by rfl⟩ : syracuseStep 969137 = 726853) B726853
theorem B3656117 : Blo 283827 3656117 := bstep (se 5 (by rfl) ⟨171380, by rfl⟩ : syracuseStep 3656117 = 342761) B342761
theorem B608867 : Blo 283827 608867 := bstep (se 1 (by rfl) ⟨456650, by rfl⟩ : syracuseStep 608867 = 913301) B913301
theorem B641681 : Blo 283827 641681 := bstep (se 2 (by rfl) ⟨240630, by rfl⟩ : syracuseStep 641681 = 481261) B481261
theorem B641699 : Blo 283827 641699 := bstep (se 1 (by rfl) ⟨481274, by rfl⟩ : syracuseStep 641699 = 962549) B962549
theorem B871117 : Blo 283827 871117 := bstep (se 3 (by rfl) ⟨163334, by rfl⟩ : syracuseStep 871117 = 326669) B326669
theorem B543523 : Blo 283827 543523 := bstep (se 1 (by rfl) ⟨407642, by rfl⟩ : syracuseStep 543523 = 815285) B815285
theorem B5327669 : Blo 283827 5327669 := bstep (se 5 (by rfl) ⟨249734, by rfl⟩ : syracuseStep 5327669 = 499469) B499469
theorem B641969 : Blo 283827 641969 := bstep (se 2 (by rfl) ⟨240738, by rfl⟩ : syracuseStep 641969 = 481477) B481477
theorem B641987 : Blo 283827 641987 := bstep (se 1 (by rfl) ⟨481490, by rfl⟩ : syracuseStep 641987 = 962981) B962981
theorem B969677 : Blo 283827 969677 := bstep (se 3 (by rfl) ⟨181814, by rfl⟩ : syracuseStep 969677 = 363629) B363629
theorem B576497 : Blo 283827 576497 := bstep (se 2 (by rfl) ⟨216186, by rfl⟩ : syracuseStep 576497 = 432373) B432373
theorem B969731 : Blo 283827 969731 := bstep (se 1 (by rfl) ⟨727298, by rfl⟩ : syracuseStep 969731 = 1454597) B1454597
theorem B1625123 : Blo 283827 1625123 := bstep (se 1 (by rfl) ⟨1218842, by rfl⟩ : syracuseStep 1625123 = 2437685) B2437685
theorem B642257 : Blo 283827 642257 := bstep (se 2 (by rfl) ⟨240846, by rfl⟩ : syracuseStep 642257 = 481693) B481693
theorem B642275 : Blo 283827 642275 := bstep (se 1 (by rfl) ⟨481706, by rfl⟩ : syracuseStep 642275 = 963413) B963413
theorem B543971 : Blo 283827 543971 := bstep (se 1 (by rfl) ⟨407978, by rfl⟩ : syracuseStep 543971 = 815957) B815957
theorem B970001 : Blo 283827 970001 := bstep (se 2 (by rfl) ⟨363750, by rfl⟩ : syracuseStep 970001 = 727501) B727501
theorem B609763 : Blo 283827 609763 := bstep (se 1 (by rfl) ⟨457322, by rfl⟩ : syracuseStep 609763 = 914645) B914645
theorem B642545 : Blo 283827 642545 := bstep (se 2 (by rfl) ⟨240954, by rfl⟩ : syracuseStep 642545 = 481909) B481909
theorem B642563 : Blo 283827 642563 := bstep (se 1 (by rfl) ⟨481922, by rfl⟩ : syracuseStep 642563 = 963845) B963845
theorem B544259 : Blo 283827 544259 := bstep (se 1 (by rfl) ⟨408194, by rfl⟩ : syracuseStep 544259 = 816389) B816389
theorem B577091 : Blo 283827 577091 := bstep (se 1 (by rfl) ⟨432818, by rfl⟩ : syracuseStep 577091 = 865637) B865637
theorem B478993 : Blo 283827 478993 := bstep (se 2 (by rfl) ⟨179622, by rfl⟩ : syracuseStep 478993 = 359245) B359245
theorem B642833 : Blo 283827 642833 := bstep (se 2 (by rfl) ⟨241062, by rfl⟩ : syracuseStep 642833 = 482125) B482125
theorem B642851 : Blo 283827 642851 := bstep (se 1 (by rfl) ⟨482138, by rfl⟩ : syracuseStep 642851 = 964277) B964277
theorem B1527587 : Blo 283827 1527587 := bstep (se 1 (by rfl) ⟨1145690, by rfl⟩ : syracuseStep 1527587 = 2291381) B2291381
theorem B970541 : Blo 283827 970541 := bstep (se 3 (by rfl) ⟨181976, by rfl⟩ : syracuseStep 970541 = 363953) B363953
theorem B479027 : Blo 283827 479027 := bstep (se 1 (by rfl) ⟨359270, by rfl⟩ : syracuseStep 479027 = 718541) B718541
theorem B970595 : Blo 283827 970595 := bstep (se 1 (by rfl) ⟨727946, by rfl⟩ : syracuseStep 970595 = 1455893) B1455893
theorem B479155 : Blo 283827 479155 := bstep (se 1 (by rfl) ⟨359366, by rfl⟩ : syracuseStep 479155 = 718733) B718733
theorem B643121 : Blo 283827 643121 := bstep (se 2 (by rfl) ⟨241170, by rfl⟩ : syracuseStep 643121 = 482341) B482341
theorem B479297 : Blo 283827 479297 := bstep (se 2 (by rfl) ⟨179736, by rfl⟩ : syracuseStep 479297 = 359473) B359473
theorem B643139 : Blo 283827 643139 := bstep (se 1 (by rfl) ⟨482354, by rfl⟩ : syracuseStep 643139 = 964709) B964709
theorem B970865 : Blo 283827 970865 := bstep (se 2 (by rfl) ⟨364074, by rfl⟩ : syracuseStep 970865 = 728149) B728149
theorem B872579 : Blo 283827 872579 := bstep (se 1 (by rfl) ⟨654434, by rfl⟩ : syracuseStep 872579 = 1308869) B1308869
theorem B479425 : Blo 283827 479425 := bstep (se 2 (by rfl) ⟨179784, by rfl⟩ : syracuseStep 479425 = 359569) B359569
theorem B479459 : Blo 283827 479459 := bstep (se 1 (by rfl) ⟨359594, by rfl⟩ : syracuseStep 479459 = 719189) B719189
theorem B2937073 : Blo 283827 2937073 := bstep (se 2 (by rfl) ⟨1101402, by rfl⟩ : syracuseStep 2937073 = 2202805) B2202805
theorem B774403 : Blo 283827 774403 := bstep (se 1 (by rfl) ⟨580802, by rfl⟩ : syracuseStep 774403 = 1161605) B1161605
theorem B348451 : Blo 283827 348451 := bstep (se 1 (by rfl) ⟨261338, by rfl⟩ : syracuseStep 348451 = 522677) B522677
theorem B643409 : Blo 283827 643409 := bstep (se 2 (by rfl) ⟨241278, by rfl⟩ : syracuseStep 643409 = 482557) B482557
theorem B479587 : Blo 283827 479587 := bstep (se 1 (by rfl) ⟨359690, by rfl⟩ : syracuseStep 479587 = 719381) B719381
theorem B643427 : Blo 283827 643427 := bstep (se 1 (by rfl) ⟨482570, by rfl⟩ : syracuseStep 643427 = 965141) B965141
theorem B545201 : Blo 283827 545201 := bstep (se 2 (by rfl) ⟨204450, by rfl⟩ : syracuseStep 545201 = 408901) B408901
theorem B479729 : Blo 283827 479729 := bstep (se 2 (by rfl) ⟨179898, by rfl⟩ : syracuseStep 479729 = 359797) B359797
theorem B479857 : Blo 283827 479857 := bstep (se 2 (by rfl) ⟨179946, by rfl⟩ : syracuseStep 479857 = 359893) B359893
theorem B643697 : Blo 283827 643697 := bstep (se 2 (by rfl) ⟨241386, by rfl⟩ : syracuseStep 643697 = 482773) B482773
theorem B643715 : Blo 283827 643715 := bstep (se 1 (by rfl) ⟨482786, by rfl⟩ : syracuseStep 643715 = 965573) B965573
theorem B971405 : Blo 283827 971405 := bstep (se 3 (by rfl) ⟨182138, by rfl⟩ : syracuseStep 971405 = 364277) B364277
theorem B479891 : Blo 283827 479891 := bstep (se 1 (by rfl) ⟨359918, by rfl⟩ : syracuseStep 479891 = 719837) B719837
theorem B1102499 : Blo 283827 1102499 := bstep (se 1 (by rfl) ⟨826874, by rfl⟩ : syracuseStep 1102499 = 1653749) B1653749
theorem B610993 : Blo 283827 610993 := bstep (se 2 (by rfl) ⟨229122, by rfl⟩ : syracuseStep 610993 = 458245) B458245
theorem B480019 : Blo 283827 480019 := bstep (se 1 (by rfl) ⟨360014, by rfl⟩ : syracuseStep 480019 = 720029) B720029
theorem B643985 : Blo 283827 643985 := bstep (se 2 (by rfl) ⟨241494, by rfl⟩ : syracuseStep 643985 = 482989) B482989
theorem B480161 : Blo 283827 480161 := bstep (se 2 (by rfl) ⟨180060, by rfl⟩ : syracuseStep 480161 = 360121) B360121
theorem B644003 : Blo 283827 644003 := bstep (se 1 (by rfl) ⟨483002, by rfl⟩ : syracuseStep 644003 = 966005) B966005
theorem B480289 : Blo 283827 480289 := bstep (se 2 (by rfl) ⟨180108, by rfl⟩ : syracuseStep 480289 = 360217) B360217
theorem B480323 : Blo 283827 480323 := bstep (se 1 (by rfl) ⟨360242, by rfl⟩ : syracuseStep 480323 = 720485) B720485
theorem B644273 : Blo 283827 644273 := bstep (se 2 (by rfl) ⟨241602, by rfl⟩ : syracuseStep 644273 = 483205) B483205
theorem B283827 : Blo 283827 283827 := bstep (se 1 (by rfl) ⟨212870, by rfl⟩ : syracuseStep 283827 = 425741) B425741
theorem B283843 : Blo 283827 283843 := bstep (se 1 (by rfl) ⟨212882, by rfl⟩ : syracuseStep 283843 = 425765) B425765
theorem B480451 : Blo 283827 480451 := bstep (se 1 (by rfl) ⟨360338, by rfl⟩ : syracuseStep 480451 = 720677) B720677
theorem B644291 : Blo 283827 644291 := bstep (se 1 (by rfl) ⟨483218, by rfl⟩ : syracuseStep 644291 = 966437) B966437
theorem B283859 : Blo 283827 283859 := bstep (se 1 (by rfl) ⟨212894, by rfl⟩ : syracuseStep 283859 = 425789) B425789
theorem B283875 : Blo 283827 283875 := bstep (se 1 (by rfl) ⟨212906, by rfl⟩ : syracuseStep 283875 = 425813) B425813
theorem B283891 : Blo 283827 283891 := bstep (se 1 (by rfl) ⟨212918, by rfl⟩ : syracuseStep 283891 = 425837) B425837
theorem B283907 : Blo 283827 283907 := bstep (se 1 (by rfl) ⟨212930, by rfl⟩ : syracuseStep 283907 = 425861) B425861
theorem B283923 : Blo 283827 283923 := bstep (se 1 (by rfl) ⟨212942, by rfl⟩ : syracuseStep 283923 = 425885) B425885
theorem B283939 : Blo 283827 283939 := bstep (se 1 (by rfl) ⟨212954, by rfl⟩ : syracuseStep 283939 = 425909) B425909
theorem B546097 : Blo 283827 546097 := bstep (se 2 (by rfl) ⟨204786, by rfl⟩ : syracuseStep 546097 = 409573) B409573
theorem B283955 : Blo 283827 283955 := bstep (se 1 (by rfl) ⟨212966, by rfl⟩ : syracuseStep 283955 = 425933) B425933
theorem B283971 : Blo 283827 283971 := bstep (se 1 (by rfl) ⟨212978, by rfl⟩ : syracuseStep 283971 = 425957) B425957
theorem B480593 : Blo 283827 480593 := bstep (se 2 (by rfl) ⟨180222, by rfl⟩ : syracuseStep 480593 = 360445) B360445
theorem B283987 : Blo 283827 283987 := bstep (se 1 (by rfl) ⟨212990, by rfl⟩ : syracuseStep 283987 = 425981) B425981
theorem B284003 : Blo 283827 284003 := bstep (se 1 (by rfl) ⟨213002, by rfl⟩ : syracuseStep 284003 = 426005) B426005
theorem B578929 : Blo 283827 578929 := bstep (se 2 (by rfl) ⟨217098, by rfl⟩ : syracuseStep 578929 = 434197) B434197
theorem B284019 : Blo 283827 284019 := bstep (se 1 (by rfl) ⟨213014, by rfl⟩ : syracuseStep 284019 = 426029) B426029
theorem B284035 : Blo 283827 284035 := bstep (se 1 (by rfl) ⟨213026, by rfl⟩ : syracuseStep 284035 = 426053) B426053
theorem B284051 : Blo 283827 284051 := bstep (se 1 (by rfl) ⟨213038, by rfl⟩ : syracuseStep 284051 = 426077) B426077
theorem B284067 : Blo 283827 284067 := bstep (se 1 (by rfl) ⟨213050, by rfl⟩ : syracuseStep 284067 = 426101) B426101
theorem B284083 : Blo 283827 284083 := bstep (se 1 (by rfl) ⟨213062, by rfl⟩ : syracuseStep 284083 = 426125) B426125
theorem B284099 : Blo 283827 284099 := bstep (se 1 (by rfl) ⟨213074, by rfl⟩ : syracuseStep 284099 = 426149) B426149
theorem B480721 : Blo 283827 480721 := bstep (se 2 (by rfl) ⟨180270, by rfl⟩ : syracuseStep 480721 = 360541) B360541
theorem B644561 : Blo 283827 644561 := bstep (se 2 (by rfl) ⟨241710, by rfl⟩ : syracuseStep 644561 = 483421) B483421
theorem B284115 : Blo 283827 284115 := bstep (se 1 (by rfl) ⟨213086, by rfl⟩ : syracuseStep 284115 = 426173) B426173
theorem B546257 : Blo 283827 546257 := bstep (se 2 (by rfl) ⟨204846, by rfl⟩ : syracuseStep 546257 = 409693) B409693
theorem B284131 : Blo 283827 284131 := bstep (se 1 (by rfl) ⟨213098, by rfl⟩ : syracuseStep 284131 = 426197) B426197
theorem B644579 : Blo 283827 644579 := bstep (se 1 (by rfl) ⟨483434, by rfl⟩ : syracuseStep 644579 = 966869) B966869
theorem B284147 : Blo 283827 284147 := bstep (se 1 (by rfl) ⟨213110, by rfl⟩ : syracuseStep 284147 = 426221) B426221
theorem B480755 : Blo 283827 480755 := bstep (se 1 (by rfl) ⟨360566, by rfl⟩ : syracuseStep 480755 = 721133) B721133
theorem B808451 : Blo 283827 808451 := bstep (se 1 (by rfl) ⟨606338, by rfl⟩ : syracuseStep 808451 = 1212677) B1212677
theorem B284163 : Blo 283827 284163 := bstep (se 1 (by rfl) ⟨213122, by rfl⟩ : syracuseStep 284163 = 426245) B426245
theorem B284179 : Blo 283827 284179 := bstep (se 1 (by rfl) ⟨213134, by rfl⟩ : syracuseStep 284179 = 426269) B426269
theorem B284195 : Blo 283827 284195 := bstep (se 1 (by rfl) ⟨213146, by rfl⟩ : syracuseStep 284195 = 426293) B426293
theorem B284211 : Blo 283827 284211 := bstep (se 1 (by rfl) ⟨213158, by rfl⟩ : syracuseStep 284211 = 426317) B426317
theorem B284227 : Blo 283827 284227 := bstep (se 1 (by rfl) ⟨213170, by rfl⟩ : syracuseStep 284227 = 426341) B426341
theorem B284243 : Blo 283827 284243 := bstep (se 1 (by rfl) ⟨213182, by rfl⟩ : syracuseStep 284243 = 426365) B426365
theorem B284259 : Blo 283827 284259 := bstep (se 1 (by rfl) ⟨213194, by rfl⟩ : syracuseStep 284259 = 426389) B426389
theorem B284275 : Blo 283827 284275 := bstep (se 1 (by rfl) ⟨213206, by rfl⟩ : syracuseStep 284275 = 426413) B426413
theorem B480883 : Blo 283827 480883 := bstep (se 1 (by rfl) ⟨360662, by rfl⟩ : syracuseStep 480883 = 721325) B721325
theorem B284291 : Blo 283827 284291 := bstep (se 1 (by rfl) ⟨213218, by rfl⟩ : syracuseStep 284291 = 426437) B426437
theorem B284307 : Blo 283827 284307 := bstep (se 1 (by rfl) ⟨213230, by rfl⟩ : syracuseStep 284307 = 426461) B426461
theorem B284323 : Blo 283827 284323 := bstep (se 1 (by rfl) ⟨213242, by rfl⟩ : syracuseStep 284323 = 426485) B426485
theorem B284339 : Blo 283827 284339 := bstep (se 1 (by rfl) ⟨213254, by rfl⟩ : syracuseStep 284339 = 426509) B426509
theorem B808643 : Blo 283827 808643 := bstep (se 1 (by rfl) ⟨606482, by rfl⟩ : syracuseStep 808643 = 1212965) B1212965
theorem B284355 : Blo 283827 284355 := bstep (se 1 (by rfl) ⟨213266, by rfl⟩ : syracuseStep 284355 = 426533) B426533
theorem B284371 : Blo 283827 284371 := bstep (se 1 (by rfl) ⟨213278, by rfl⟩ : syracuseStep 284371 = 426557) B426557
theorem B284387 : Blo 283827 284387 := bstep (se 1 (by rfl) ⟨213290, by rfl⟩ : syracuseStep 284387 = 426581) B426581
theorem B775907 : Blo 283827 775907 := bstep (se 1 (by rfl) ⟨581930, by rfl⟩ : syracuseStep 775907 = 1163861) B1163861
theorem B644849 : Blo 283827 644849 := bstep (se 2 (by rfl) ⟨241818, by rfl⟩ : syracuseStep 644849 = 483637) B483637
theorem B284403 : Blo 283827 284403 := bstep (se 1 (by rfl) ⟨213302, by rfl⟩ : syracuseStep 284403 = 426605) B426605
theorem B481025 : Blo 283827 481025 := bstep (se 2 (by rfl) ⟨180384, by rfl⟩ : syracuseStep 481025 = 360769) B360769
theorem B284419 : Blo 283827 284419 := bstep (se 1 (by rfl) ⟨213314, by rfl⟩ : syracuseStep 284419 = 426629) B426629
theorem B644867 : Blo 283827 644867 := bstep (se 1 (by rfl) ⟨483650, by rfl⟩ : syracuseStep 644867 = 967301) B967301
theorem B2447117 : Blo 283827 2447117 := bstep (se 3 (by rfl) ⟨458834, by rfl⟩ : syracuseStep 2447117 = 917669) B917669
theorem B284435 : Blo 283827 284435 := bstep (se 1 (by rfl) ⟨213326, by rfl⟩ : syracuseStep 284435 = 426653) B426653
theorem B284451 : Blo 283827 284451 := bstep (se 1 (by rfl) ⟨213338, by rfl⟩ : syracuseStep 284451 = 426677) B426677
theorem B284467 : Blo 283827 284467 := bstep (se 1 (by rfl) ⟨213350, by rfl⟩ : syracuseStep 284467 = 426701) B426701
theorem B284483 : Blo 283827 284483 := bstep (se 1 (by rfl) ⟨213362, by rfl⟩ : syracuseStep 284483 = 426725) B426725
theorem B284499 : Blo 283827 284499 := bstep (se 1 (by rfl) ⟨213374, by rfl⟩ : syracuseStep 284499 = 426749) B426749
theorem B284515 : Blo 283827 284515 := bstep (se 1 (by rfl) ⟨213386, by rfl⟩ : syracuseStep 284515 = 426773) B426773
theorem B284531 : Blo 283827 284531 := bstep (se 1 (by rfl) ⟨213398, by rfl⟩ : syracuseStep 284531 = 426797) B426797
theorem B481153 : Blo 283827 481153 := bstep (se 2 (by rfl) ⟨180432, by rfl⟩ : syracuseStep 481153 = 360865) B360865
theorem B284547 : Blo 283827 284547 := bstep (se 1 (by rfl) ⟨213410, by rfl⟩ : syracuseStep 284547 = 426821) B426821
theorem B284563 : Blo 283827 284563 := bstep (se 1 (by rfl) ⟨213422, by rfl⟩ : syracuseStep 284563 = 426845) B426845
theorem B284579 : Blo 283827 284579 := bstep (se 1 (by rfl) ⟨213434, by rfl⟩ : syracuseStep 284579 = 426869) B426869
theorem B481187 : Blo 283827 481187 := bstep (se 1 (by rfl) ⟨360890, by rfl⟩ : syracuseStep 481187 = 721781) B721781
theorem B284595 : Blo 283827 284595 := bstep (se 1 (by rfl) ⟨213446, by rfl⟩ : syracuseStep 284595 = 426893) B426893
theorem B284611 : Blo 283827 284611 := bstep (se 1 (by rfl) ⟨213458, by rfl⟩ : syracuseStep 284611 = 426917) B426917
theorem B284627 : Blo 283827 284627 := bstep (se 1 (by rfl) ⟨213470, by rfl⟩ : syracuseStep 284627 = 426941) B426941
theorem B284643 : Blo 283827 284643 := bstep (se 1 (by rfl) ⟨213482, by rfl⟩ : syracuseStep 284643 = 426965) B426965
theorem B284659 : Blo 283827 284659 := bstep (se 1 (by rfl) ⟨213494, by rfl⟩ : syracuseStep 284659 = 426989) B426989
theorem B284675 : Blo 283827 284675 := bstep (se 1 (by rfl) ⟨213506, by rfl⟩ : syracuseStep 284675 = 427013) B427013
theorem B645137 : Blo 283827 645137 := bstep (se 2 (by rfl) ⟨241926, by rfl⟩ : syracuseStep 645137 = 483853) B483853
theorem B284691 : Blo 283827 284691 := bstep (se 1 (by rfl) ⟨213518, by rfl⟩ : syracuseStep 284691 = 427037) B427037
theorem B284707 : Blo 283827 284707 := bstep (se 1 (by rfl) ⟨213530, by rfl⟩ : syracuseStep 284707 = 427061) B427061
theorem B481315 : Blo 283827 481315 := bstep (se 1 (by rfl) ⟨360986, by rfl⟩ : syracuseStep 481315 = 721973) B721973
theorem B645155 : Blo 283827 645155 := bstep (se 1 (by rfl) ⟨483866, by rfl⟩ : syracuseStep 645155 = 967733) B967733
theorem B284723 : Blo 283827 284723 := bstep (se 1 (by rfl) ⟨213542, by rfl⟩ : syracuseStep 284723 = 427085) B427085
theorem B284739 : Blo 283827 284739 := bstep (se 1 (by rfl) ⟨213554, by rfl⟩ : syracuseStep 284739 = 427109) B427109
theorem B284755 : Blo 283827 284755 := bstep (se 1 (by rfl) ⟨213566, by rfl⟩ : syracuseStep 284755 = 427133) B427133
theorem B284771 : Blo 283827 284771 := bstep (se 1 (by rfl) ⟨213578, by rfl⟩ : syracuseStep 284771 = 427157) B427157
theorem B284787 : Blo 283827 284787 := bstep (se 1 (by rfl) ⟨213590, by rfl⟩ : syracuseStep 284787 = 427181) B427181
theorem B284803 : Blo 283827 284803 := bstep (se 1 (by rfl) ⟨213602, by rfl⟩ : syracuseStep 284803 = 427205) B427205
theorem B514193 : Blo 283827 514193 := bstep (se 2 (by rfl) ⟨192822, by rfl⟩ : syracuseStep 514193 = 385645) B385645
theorem B284819 : Blo 283827 284819 := bstep (se 1 (by rfl) ⟨213614, by rfl⟩ : syracuseStep 284819 = 427229) B427229
theorem B612497 : Blo 283827 612497 := bstep (se 2 (by rfl) ⟨229686, by rfl⟩ : syracuseStep 612497 = 459373) B459373
theorem B284835 : Blo 283827 284835 := bstep (se 1 (by rfl) ⟨213626, by rfl⟩ : syracuseStep 284835 = 427253) B427253
theorem B612515 : Blo 283827 612515 := bstep (se 1 (by rfl) ⟨459386, by rfl⟩ : syracuseStep 612515 = 918773) B918773
theorem B481457 : Blo 283827 481457 := bstep (se 2 (by rfl) ⟨180546, by rfl⟩ : syracuseStep 481457 = 361093) B361093
theorem B284851 : Blo 283827 284851 := bstep (se 1 (by rfl) ⟨213638, by rfl⟩ : syracuseStep 284851 = 427277) B427277
theorem B284867 : Blo 283827 284867 := bstep (se 1 (by rfl) ⟨213650, by rfl⟩ : syracuseStep 284867 = 427301) B427301
theorem B284883 : Blo 283827 284883 := bstep (se 1 (by rfl) ⟨213662, by rfl⟩ : syracuseStep 284883 = 427325) B427325
theorem B284899 : Blo 283827 284899 := bstep (se 1 (by rfl) ⟨213674, by rfl⟩ : syracuseStep 284899 = 427349) B427349
theorem B284915 : Blo 283827 284915 := bstep (se 1 (by rfl) ⟨213686, by rfl⟩ : syracuseStep 284915 = 427373) B427373
theorem B284931 : Blo 283827 284931 := bstep (se 1 (by rfl) ⟨213698, by rfl⟩ : syracuseStep 284931 = 427397) B427397
theorem B1825037 : Blo 283827 1825037 := bstep (se 3 (by rfl) ⟨342194, by rfl⟩ : syracuseStep 1825037 = 684389) B684389
theorem B284947 : Blo 283827 284947 := bstep (se 1 (by rfl) ⟨213710, by rfl⟩ : syracuseStep 284947 = 427421) B427421
theorem B284963 : Blo 283827 284963 := bstep (se 1 (by rfl) ⟨213722, by rfl⟩ : syracuseStep 284963 = 427445) B427445
theorem B481585 : Blo 283827 481585 := bstep (se 2 (by rfl) ⟨180594, by rfl⟩ : syracuseStep 481585 = 361189) B361189
theorem B645425 : Blo 283827 645425 := bstep (se 2 (by rfl) ⟨242034, by rfl⟩ : syracuseStep 645425 = 484069) B484069
theorem B284979 : Blo 283827 284979 := bstep (se 1 (by rfl) ⟨213734, by rfl⟩ : syracuseStep 284979 = 427469) B427469
theorem B284995 : Blo 283827 284995 := bstep (se 1 (by rfl) ⟨213746, by rfl⟩ : syracuseStep 284995 = 427493) B427493
theorem B645443 : Blo 283827 645443 := bstep (se 1 (by rfl) ⟨484082, by rfl⟩ : syracuseStep 645443 = 968165) B968165
theorem B2185541 : Blo 283827 2185541 := bstep (se 4 (by rfl) ⟨204894, by rfl⟩ : syracuseStep 2185541 = 409789) B409789
theorem B285011 : Blo 283827 285011 := bstep (se 1 (by rfl) ⟨213758, by rfl⟩ : syracuseStep 285011 = 427517) B427517
theorem B481619 : Blo 283827 481619 := bstep (se 1 (by rfl) ⟨361214, by rfl⟩ : syracuseStep 481619 = 722429) B722429
theorem B285027 : Blo 283827 285027 := bstep (se 1 (by rfl) ⟨213770, by rfl⟩ : syracuseStep 285027 = 427541) B427541
theorem B285043 : Blo 283827 285043 := bstep (se 1 (by rfl) ⟨213782, by rfl⟩ : syracuseStep 285043 = 427565) B427565
theorem B285059 : Blo 283827 285059 := bstep (se 1 (by rfl) ⟨213794, by rfl⟩ : syracuseStep 285059 = 427589) B427589
theorem B285075 : Blo 283827 285075 := bstep (se 1 (by rfl) ⟨213806, by rfl⟩ : syracuseStep 285075 = 427613) B427613
theorem B285091 : Blo 283827 285091 := bstep (se 1 (by rfl) ⟨213818, by rfl⟩ : syracuseStep 285091 = 427637) B427637
theorem B285107 : Blo 283827 285107 := bstep (se 1 (by rfl) ⟨213830, by rfl⟩ : syracuseStep 285107 = 427661) B427661
theorem B285123 : Blo 283827 285123 := bstep (se 1 (by rfl) ⟨213842, by rfl⟩ : syracuseStep 285123 = 427685) B427685
theorem B285139 : Blo 283827 285139 := bstep (se 1 (by rfl) ⟨213854, by rfl⟩ : syracuseStep 285139 = 427709) B427709
theorem B481747 : Blo 283827 481747 := bstep (se 1 (by rfl) ⟨361310, by rfl⟩ : syracuseStep 481747 = 722621) B722621
theorem B285155 : Blo 283827 285155 := bstep (se 1 (by rfl) ⟨213866, by rfl⟩ : syracuseStep 285155 = 427733) B427733
theorem B809453 : Blo 283827 809453 := bstep (se 3 (by rfl) ⟨151772, by rfl⟩ : syracuseStep 809453 = 303545) B303545
theorem B285171 : Blo 283827 285171 := bstep (se 1 (by rfl) ⟨213878, by rfl⟩ : syracuseStep 285171 = 427757) B427757
theorem B285187 : Blo 283827 285187 := bstep (se 1 (by rfl) ⟨213890, by rfl⟩ : syracuseStep 285187 = 427781) B427781
theorem B285203 : Blo 283827 285203 := bstep (se 1 (by rfl) ⟨213902, by rfl⟩ : syracuseStep 285203 = 427805) B427805
theorem B285219 : Blo 283827 285219 := bstep (se 1 (by rfl) ⟨213914, by rfl⟩ : syracuseStep 285219 = 427829) B427829
theorem B285235 : Blo 283827 285235 := bstep (se 1 (by rfl) ⟨213926, by rfl⟩ : syracuseStep 285235 = 427853) B427853
theorem B285251 : Blo 283827 285251 := bstep (se 1 (by rfl) ⟨213938, by rfl⟩ : syracuseStep 285251 = 427877) B427877
theorem B645713 : Blo 283827 645713 := bstep (se 2 (by rfl) ⟨242142, by rfl⟩ : syracuseStep 645713 = 484285) B484285
theorem B285267 : Blo 283827 285267 := bstep (se 1 (by rfl) ⟨213950, by rfl⟩ : syracuseStep 285267 = 427901) B427901
theorem B481889 : Blo 283827 481889 := bstep (se 2 (by rfl) ⟨180708, by rfl⟩ : syracuseStep 481889 = 361417) B361417
theorem B285283 : Blo 283827 285283 := bstep (se 1 (by rfl) ⟨213962, by rfl⟩ : syracuseStep 285283 = 427925) B427925
theorem B645731 : Blo 283827 645731 := bstep (se 1 (by rfl) ⟨484298, by rfl⟩ : syracuseStep 645731 = 968597) B968597
theorem B285299 : Blo 283827 285299 := bstep (se 1 (by rfl) ⟨213974, by rfl⟩ : syracuseStep 285299 = 427949) B427949
theorem B285315 : Blo 283827 285315 := bstep (se 1 (by rfl) ⟨213986, by rfl⟩ : syracuseStep 285315 = 427973) B427973
theorem B2939533 : Blo 283827 2939533 := bstep (se 3 (by rfl) ⟨551162, by rfl⟩ : syracuseStep 2939533 = 1102325) B1102325
theorem B285331 : Blo 283827 285331 := bstep (se 1 (by rfl) ⟨213998, by rfl⟩ : syracuseStep 285331 = 427997) B427997
theorem B809635 : Blo 283827 809635 := bstep (se 1 (by rfl) ⟨607226, by rfl⟩ : syracuseStep 809635 = 1214453) B1214453
theorem B285347 : Blo 283827 285347 := bstep (se 1 (by rfl) ⟨214010, by rfl⟩ : syracuseStep 285347 = 428021) B428021
theorem B285363 : Blo 283827 285363 := bstep (se 1 (by rfl) ⟨214022, by rfl⟩ : syracuseStep 285363 = 428045) B428045
theorem B285379 : Blo 283827 285379 := bstep (se 1 (by rfl) ⟨214034, by rfl⟩ : syracuseStep 285379 = 428069) B428069
theorem B285395 : Blo 283827 285395 := bstep (se 1 (by rfl) ⟨214046, by rfl⟩ : syracuseStep 285395 = 428093) B428093
theorem B482017 : Blo 283827 482017 := bstep (se 2 (by rfl) ⟨180756, by rfl⟩ : syracuseStep 482017 = 361513) B361513
theorem B285411 : Blo 283827 285411 := bstep (se 1 (by rfl) ⟨214058, by rfl⟩ : syracuseStep 285411 = 428117) B428117
theorem B285427 : Blo 283827 285427 := bstep (se 1 (by rfl) ⟨214070, by rfl⟩ : syracuseStep 285427 = 428141) B428141
theorem B285443 : Blo 283827 285443 := bstep (se 1 (by rfl) ⟨214082, by rfl⟩ : syracuseStep 285443 = 428165) B428165
theorem B482051 : Blo 283827 482051 := bstep (se 1 (by rfl) ⟨361538, by rfl⟩ : syracuseStep 482051 = 723077) B723077
theorem B285459 : Blo 283827 285459 := bstep (se 1 (by rfl) ⟨214094, by rfl⟩ : syracuseStep 285459 = 428189) B428189
theorem B285475 : Blo 283827 285475 := bstep (se 1 (by rfl) ⟨214106, by rfl⟩ : syracuseStep 285475 = 428213) B428213
theorem B285491 : Blo 283827 285491 := bstep (se 1 (by rfl) ⟨214118, by rfl⟩ : syracuseStep 285491 = 428237) B428237
theorem B285507 : Blo 283827 285507 := bstep (se 1 (by rfl) ⟨214130, by rfl⟩ : syracuseStep 285507 = 428261) B428261
theorem B285523 : Blo 283827 285523 := bstep (se 1 (by rfl) ⟨214142, by rfl⟩ : syracuseStep 285523 = 428285) B428285
theorem B285539 : Blo 283827 285539 := bstep (se 1 (by rfl) ⟨214154, by rfl⟩ : syracuseStep 285539 = 428309) B428309
theorem B646001 : Blo 283827 646001 := bstep (se 2 (by rfl) ⟨242250, by rfl⟩ : syracuseStep 646001 = 484501) B484501
theorem B285555 : Blo 283827 285555 := bstep (se 1 (by rfl) ⟨214166, by rfl⟩ : syracuseStep 285555 = 428333) B428333
theorem B285571 : Blo 283827 285571 := bstep (se 1 (by rfl) ⟨214178, by rfl⟩ : syracuseStep 285571 = 428357) B428357
theorem B482179 : Blo 283827 482179 := bstep (se 1 (by rfl) ⟨361634, by rfl⟩ : syracuseStep 482179 = 723269) B723269
theorem B646019 : Blo 283827 646019 := bstep (se 1 (by rfl) ⟨484514, by rfl⟩ : syracuseStep 646019 = 969029) B969029
theorem B285587 : Blo 283827 285587 := bstep (se 1 (by rfl) ⟨214190, by rfl⟩ : syracuseStep 285587 = 428381) B428381
theorem B285603 : Blo 283827 285603 := bstep (se 1 (by rfl) ⟨214202, by rfl⟩ : syracuseStep 285603 = 428405) B428405
theorem B285619 : Blo 283827 285619 := bstep (se 1 (by rfl) ⟨214214, by rfl⟩ : syracuseStep 285619 = 428429) B428429
theorem B285635 : Blo 283827 285635 := bstep (se 1 (by rfl) ⟨214226, by rfl⟩ : syracuseStep 285635 = 428453) B428453
theorem B285651 : Blo 283827 285651 := bstep (se 1 (by rfl) ⟨214238, by rfl⟩ : syracuseStep 285651 = 428477) B428477
theorem B285667 : Blo 283827 285667 := bstep (se 1 (by rfl) ⟨214250, by rfl⟩ : syracuseStep 285667 = 428501) B428501
theorem B285683 : Blo 283827 285683 := bstep (se 1 (by rfl) ⟨214262, by rfl⟩ : syracuseStep 285683 = 428525) B428525
theorem B285699 : Blo 283827 285699 := bstep (se 1 (by rfl) ⟨214274, by rfl⟩ : syracuseStep 285699 = 428549) B428549
theorem B482321 : Blo 283827 482321 := bstep (se 2 (by rfl) ⟨180870, by rfl⟩ : syracuseStep 482321 = 361741) B361741
theorem B285715 : Blo 283827 285715 := bstep (se 1 (by rfl) ⟨214286, by rfl⟩ : syracuseStep 285715 = 428573) B428573
theorem B285731 : Blo 283827 285731 := bstep (se 1 (by rfl) ⟨214298, by rfl⟩ : syracuseStep 285731 = 428597) B428597
theorem B285747 : Blo 283827 285747 := bstep (se 1 (by rfl) ⟨214310, by rfl⟩ : syracuseStep 285747 = 428621) B428621
theorem B285763 : Blo 283827 285763 := bstep (se 1 (by rfl) ⟨214322, by rfl⟩ : syracuseStep 285763 = 428645) B428645
theorem B285779 : Blo 283827 285779 := bstep (se 1 (by rfl) ⟨214334, by rfl⟩ : syracuseStep 285779 = 428669) B428669
theorem B285795 : Blo 283827 285795 := bstep (se 1 (by rfl) ⟨214346, by rfl⟩ : syracuseStep 285795 = 428693) B428693
theorem B285811 : Blo 283827 285811 := bstep (se 1 (by rfl) ⟨214358, by rfl⟩ : syracuseStep 285811 = 428717) B428717
theorem B285827 : Blo 283827 285827 := bstep (se 1 (by rfl) ⟨214370, by rfl⟩ : syracuseStep 285827 = 428741) B428741
theorem B777347 : Blo 283827 777347 := bstep (se 1 (by rfl) ⟨583010, by rfl⟩ : syracuseStep 777347 = 1166021) B1166021
theorem B810125 : Blo 283827 810125 := bstep (se 3 (by rfl) ⟨151898, by rfl⟩ : syracuseStep 810125 = 303797) B303797
theorem B482449 : Blo 283827 482449 := bstep (se 2 (by rfl) ⟨180918, by rfl⟩ : syracuseStep 482449 = 361837) B361837
theorem B646289 : Blo 283827 646289 := bstep (se 2 (by rfl) ⟨242358, by rfl⟩ : syracuseStep 646289 = 484717) B484717
theorem B285843 : Blo 283827 285843 := bstep (se 1 (by rfl) ⟨214382, by rfl⟩ : syracuseStep 285843 = 428765) B428765
theorem B285859 : Blo 283827 285859 := bstep (se 1 (by rfl) ⟨214394, by rfl⟩ : syracuseStep 285859 = 428789) B428789
theorem B646307 : Blo 283827 646307 := bstep (se 1 (by rfl) ⟨484730, by rfl⟩ : syracuseStep 646307 = 969461) B969461
theorem B285875 : Blo 283827 285875 := bstep (se 1 (by rfl) ⟨214406, by rfl⟩ : syracuseStep 285875 = 428813) B428813
theorem B482483 : Blo 283827 482483 := bstep (se 1 (by rfl) ⟨361862, by rfl⟩ : syracuseStep 482483 = 723725) B723725
theorem B285891 : Blo 283827 285891 := bstep (se 1 (by rfl) ⟨214418, by rfl⟩ : syracuseStep 285891 = 428837) B428837
theorem B285907 : Blo 283827 285907 := bstep (se 1 (by rfl) ⟨214430, by rfl⟩ : syracuseStep 285907 = 428861) B428861
theorem B285923 : Blo 283827 285923 := bstep (se 1 (by rfl) ⟨214442, by rfl⟩ : syracuseStep 285923 = 428885) B428885
theorem B285939 : Blo 283827 285939 := bstep (se 1 (by rfl) ⟨214454, by rfl⟩ : syracuseStep 285939 = 428909) B428909
theorem B285955 : Blo 283827 285955 := bstep (se 1 (by rfl) ⟨214466, by rfl⟩ : syracuseStep 285955 = 428933) B428933
theorem B285971 : Blo 283827 285971 := bstep (se 1 (by rfl) ⟨214478, by rfl⟩ : syracuseStep 285971 = 428957) B428957
theorem B285987 : Blo 283827 285987 := bstep (se 1 (by rfl) ⟨214490, by rfl⟩ : syracuseStep 285987 = 428981) B428981
theorem B482611 : Blo 283827 482611 := bstep (se 1 (by rfl) ⟨361958, by rfl⟩ : syracuseStep 482611 = 723917) B723917
theorem B286003 : Blo 283827 286003 := bstep (se 1 (by rfl) ⟨214502, by rfl⟩ : syracuseStep 286003 = 429005) B429005
theorem B286019 : Blo 283827 286019 := bstep (se 1 (by rfl) ⟨214514, by rfl⟩ : syracuseStep 286019 = 429029) B429029
theorem B286035 : Blo 283827 286035 := bstep (se 1 (by rfl) ⟨214526, by rfl⟩ : syracuseStep 286035 = 429053) B429053
theorem B286051 : Blo 283827 286051 := bstep (se 1 (by rfl) ⟨214538, by rfl⟩ : syracuseStep 286051 = 429077) B429077
theorem B286067 : Blo 283827 286067 := bstep (se 1 (by rfl) ⟨214550, by rfl⟩ : syracuseStep 286067 = 429101) B429101
theorem B286083 : Blo 283827 286083 := bstep (se 1 (by rfl) ⟨214562, by rfl⟩ : syracuseStep 286083 = 429125) B429125
theorem B286099 : Blo 283827 286099 := bstep (se 1 (by rfl) ⟨214574, by rfl⟩ : syracuseStep 286099 = 429149) B429149
theorem B286115 : Blo 283827 286115 := bstep (se 1 (by rfl) ⟨214586, by rfl⟩ : syracuseStep 286115 = 429173) B429173
theorem B646577 : Blo 283827 646577 := bstep (se 2 (by rfl) ⟨242466, by rfl⟩ : syracuseStep 646577 = 484933) B484933
theorem B286131 : Blo 283827 286131 := bstep (se 1 (by rfl) ⟨214598, by rfl⟩ : syracuseStep 286131 = 429197) B429197
theorem B482753 : Blo 283827 482753 := bstep (se 2 (by rfl) ⟨181032, by rfl⟩ : syracuseStep 482753 = 362065) B362065
theorem B286147 : Blo 283827 286147 := bstep (se 1 (by rfl) ⟨214610, by rfl⟩ : syracuseStep 286147 = 429221) B429221
theorem B646595 : Blo 283827 646595 := bstep (se 1 (by rfl) ⟨484946, by rfl⟩ : syracuseStep 646595 = 969893) B969893
theorem B286163 : Blo 283827 286163 := bstep (se 1 (by rfl) ⟨214622, by rfl⟩ : syracuseStep 286163 = 429245) B429245
theorem B286179 : Blo 283827 286179 := bstep (se 1 (by rfl) ⟨214634, by rfl⟩ : syracuseStep 286179 = 429269) B429269
theorem B286195 : Blo 283827 286195 := bstep (se 1 (by rfl) ⟨214646, by rfl⟩ : syracuseStep 286195 = 429293) B429293
theorem B286211 : Blo 283827 286211 := bstep (se 1 (by rfl) ⟨214658, by rfl⟩ : syracuseStep 286211 = 429317) B429317
theorem B286227 : Blo 283827 286227 := bstep (se 1 (by rfl) ⟨214670, by rfl⟩ : syracuseStep 286227 = 429341) B429341
theorem B286243 : Blo 283827 286243 := bstep (se 1 (by rfl) ⟨214682, by rfl⟩ : syracuseStep 286243 = 429365) B429365
theorem B286259 : Blo 283827 286259 := bstep (se 1 (by rfl) ⟨214694, by rfl⟩ : syracuseStep 286259 = 429389) B429389
theorem B482881 : Blo 283827 482881 := bstep (se 2 (by rfl) ⟨181080, by rfl⟩ : syracuseStep 482881 = 362161) B362161
theorem B286275 : Blo 283827 286275 := bstep (se 1 (by rfl) ⟨214706, by rfl⟩ : syracuseStep 286275 = 429413) B429413
theorem B286291 : Blo 283827 286291 := bstep (se 1 (by rfl) ⟨214718, by rfl⟩ : syracuseStep 286291 = 429437) B429437
theorem B482915 : Blo 283827 482915 := bstep (se 1 (by rfl) ⟨362186, by rfl⟩ : syracuseStep 482915 = 724373) B724373
theorem B286307 : Blo 283827 286307 := bstep (se 1 (by rfl) ⟨214730, by rfl⟩ : syracuseStep 286307 = 429461) B429461
theorem B286323 : Blo 283827 286323 := bstep (se 1 (by rfl) ⟨214742, by rfl⟩ : syracuseStep 286323 = 429485) B429485
theorem B286339 : Blo 283827 286339 := bstep (se 1 (by rfl) ⟨214754, by rfl⟩ : syracuseStep 286339 = 429509) B429509
theorem B286355 : Blo 283827 286355 := bstep (se 1 (by rfl) ⟨214766, by rfl⟩ : syracuseStep 286355 = 429533) B429533
theorem B286371 : Blo 283827 286371 := bstep (se 1 (by rfl) ⟨214778, by rfl⟩ : syracuseStep 286371 = 429557) B429557
theorem B286387 : Blo 283827 286387 := bstep (se 1 (by rfl) ⟨214790, by rfl⟩ : syracuseStep 286387 = 429581) B429581
theorem B286403 : Blo 283827 286403 := bstep (se 1 (by rfl) ⟨214802, by rfl⟩ : syracuseStep 286403 = 429605) B429605
theorem B646865 : Blo 283827 646865 := bstep (se 2 (by rfl) ⟨242574, by rfl⟩ : syracuseStep 646865 = 485149) B485149
theorem B286419 : Blo 283827 286419 := bstep (se 1 (by rfl) ⟨214814, by rfl⟩ : syracuseStep 286419 = 429629) B429629
theorem B483043 : Blo 283827 483043 := bstep (se 1 (by rfl) ⟨362282, by rfl⟩ : syracuseStep 483043 = 724565) B724565
theorem B286435 : Blo 283827 286435 := bstep (se 1 (by rfl) ⟨214826, by rfl⟩ : syracuseStep 286435 = 429653) B429653
theorem B646883 : Blo 283827 646883 := bstep (se 1 (by rfl) ⟨485162, by rfl⟩ : syracuseStep 646883 = 970325) B970325
theorem B286451 : Blo 283827 286451 := bstep (se 1 (by rfl) ⟨214838, by rfl⟩ : syracuseStep 286451 = 429677) B429677
theorem B286467 : Blo 283827 286467 := bstep (se 1 (by rfl) ⟨214850, by rfl⟩ : syracuseStep 286467 = 429701) B429701
theorem B286483 : Blo 283827 286483 := bstep (se 1 (by rfl) ⟨214862, by rfl⟩ : syracuseStep 286483 = 429725) B429725
theorem B286499 : Blo 283827 286499 := bstep (se 1 (by rfl) ⟨214874, by rfl⟩ : syracuseStep 286499 = 429749) B429749
theorem B286515 : Blo 283827 286515 := bstep (se 1 (by rfl) ⟨214886, by rfl⟩ : syracuseStep 286515 = 429773) B429773
theorem B286531 : Blo 283827 286531 := bstep (se 1 (by rfl) ⟨214898, by rfl⟩ : syracuseStep 286531 = 429797) B429797
theorem B319315 : Blo 283827 319315 := bstep (se 1 (by rfl) ⟨239486, by rfl⟩ : syracuseStep 319315 = 478973) B478973
theorem B286547 : Blo 283827 286547 := bstep (se 1 (by rfl) ⟨214910, by rfl⟩ : syracuseStep 286547 = 429821) B429821
theorem B286563 : Blo 283827 286563 := bstep (se 1 (by rfl) ⟨214922, by rfl⟩ : syracuseStep 286563 = 429845) B429845
theorem B483185 : Blo 283827 483185 := bstep (se 2 (by rfl) ⟨181194, by rfl⟩ : syracuseStep 483185 = 362389) B362389
theorem B286579 : Blo 283827 286579 := bstep (se 1 (by rfl) ⟨214934, by rfl⟩ : syracuseStep 286579 = 429869) B429869
theorem B286595 : Blo 283827 286595 := bstep (se 1 (by rfl) ⟨214946, by rfl⟩ : syracuseStep 286595 = 429893) B429893
theorem B286611 : Blo 283827 286611 := bstep (se 1 (by rfl) ⟨214958, by rfl⟩ : syracuseStep 286611 = 429917) B429917
theorem B286627 : Blo 283827 286627 := bstep (se 1 (by rfl) ⟨214970, by rfl⟩ : syracuseStep 286627 = 429941) B429941
theorem B286643 : Blo 283827 286643 := bstep (se 1 (by rfl) ⟨214982, by rfl⟩ : syracuseStep 286643 = 429965) B429965
theorem B286659 : Blo 283827 286659 := bstep (se 1 (by rfl) ⟨214994, by rfl⟩ : syracuseStep 286659 = 429989) B429989
theorem B286675 : Blo 283827 286675 := bstep (se 1 (by rfl) ⟨215006, by rfl⟩ : syracuseStep 286675 = 430013) B430013
theorem B319459 : Blo 283827 319459 := bstep (se 1 (by rfl) ⟨239594, by rfl⟩ : syracuseStep 319459 = 479189) B479189
theorem B286691 : Blo 283827 286691 := bstep (se 1 (by rfl) ⟨215018, by rfl⟩ : syracuseStep 286691 = 430037) B430037
theorem B483313 : Blo 283827 483313 := bstep (se 2 (by rfl) ⟨181242, by rfl⟩ : syracuseStep 483313 = 362485) B362485
theorem B647153 : Blo 283827 647153 := bstep (se 2 (by rfl) ⟨242682, by rfl⟩ : syracuseStep 647153 = 485365) B485365
theorem B286707 : Blo 283827 286707 := bstep (se 1 (by rfl) ⟨215030, by rfl⟩ : syracuseStep 286707 = 430061) B430061
theorem B286723 : Blo 283827 286723 := bstep (se 1 (by rfl) ⟨215042, by rfl⟩ : syracuseStep 286723 = 430085) B430085
theorem B647171 : Blo 283827 647171 := bstep (se 1 (by rfl) ⟨485378, by rfl⟩ : syracuseStep 647171 = 970757) B970757
theorem B483347 : Blo 283827 483347 := bstep (se 1 (by rfl) ⟨362510, by rfl⟩ : syracuseStep 483347 = 725021) B725021
theorem B286739 : Blo 283827 286739 := bstep (se 1 (by rfl) ⟨215054, by rfl⟩ : syracuseStep 286739 = 430109) B430109
theorem B286755 : Blo 283827 286755 := bstep (se 1 (by rfl) ⟨215066, by rfl⟩ : syracuseStep 286755 = 430133) B430133
theorem B286771 : Blo 283827 286771 := bstep (se 1 (by rfl) ⟨215078, by rfl⟩ : syracuseStep 286771 = 430157) B430157
theorem B286787 : Blo 283827 286787 := bstep (se 1 (by rfl) ⟨215090, by rfl⟩ : syracuseStep 286787 = 430181) B430181
theorem B286803 : Blo 283827 286803 := bstep (se 1 (by rfl) ⟨215102, by rfl⟩ : syracuseStep 286803 = 430205) B430205
theorem B286819 : Blo 283827 286819 := bstep (se 1 (by rfl) ⟨215114, by rfl⟩ : syracuseStep 286819 = 430229) B430229
theorem B614513 : Blo 283827 614513 := bstep (se 2 (by rfl) ⟨230442, by rfl⟩ : syracuseStep 614513 = 460885) B460885
theorem B319603 : Blo 283827 319603 := bstep (se 1 (by rfl) ⟨239702, by rfl⟩ : syracuseStep 319603 = 479405) B479405
theorem B286835 : Blo 283827 286835 := bstep (se 1 (by rfl) ⟨215126, by rfl⟩ : syracuseStep 286835 = 430253) B430253
theorem B909443 : Blo 283827 909443 := bstep (se 1 (by rfl) ⟨682082, by rfl⟩ : syracuseStep 909443 = 1364165) B1364165
theorem B286851 : Blo 283827 286851 := bstep (se 1 (by rfl) ⟨215138, by rfl⟩ : syracuseStep 286851 = 430277) B430277
theorem B483475 : Blo 283827 483475 := bstep (se 1 (by rfl) ⟨362606, by rfl⟩ : syracuseStep 483475 = 725213) B725213
theorem B286867 : Blo 283827 286867 := bstep (se 1 (by rfl) ⟨215150, by rfl⟩ : syracuseStep 286867 = 430301) B430301
theorem B286883 : Blo 283827 286883 := bstep (se 1 (by rfl) ⟨215162, by rfl⟩ : syracuseStep 286883 = 430325) B430325
theorem B286899 : Blo 283827 286899 := bstep (se 1 (by rfl) ⟨215174, by rfl⟩ : syracuseStep 286899 = 430349) B430349
theorem B286915 : Blo 283827 286915 := bstep (se 1 (by rfl) ⟨215186, by rfl⟩ : syracuseStep 286915 = 430373) B430373
theorem B286931 : Blo 283827 286931 := bstep (se 1 (by rfl) ⟨215198, by rfl⟩ : syracuseStep 286931 = 430397) B430397
theorem B286947 : Blo 283827 286947 := bstep (se 1 (by rfl) ⟨215210, by rfl⟩ : syracuseStep 286947 = 430421) B430421
theorem B3268835 : Blo 283827 3268835 := bstep (se 1 (by rfl) ⟨2451626, by rfl⟩ : syracuseStep 3268835 = 4903253) B4903253
theorem B286963 : Blo 283827 286963 := bstep (se 1 (by rfl) ⟨215222, by rfl⟩ : syracuseStep 286963 = 430445) B430445
theorem B319747 : Blo 283827 319747 := bstep (se 1 (by rfl) ⟨239810, by rfl⟩ : syracuseStep 319747 = 479621) B479621
theorem B286979 : Blo 283827 286979 := bstep (se 1 (by rfl) ⟨215234, by rfl⟩ : syracuseStep 286979 = 430469) B430469
theorem B647441 : Blo 283827 647441 := bstep (se 2 (by rfl) ⟨242790, by rfl⟩ : syracuseStep 647441 = 485581) B485581
theorem B286995 : Blo 283827 286995 := bstep (se 1 (by rfl) ⟨215246, by rfl⟩ : syracuseStep 286995 = 430493) B430493
theorem B483617 : Blo 283827 483617 := bstep (se 2 (by rfl) ⟨181356, by rfl⟩ : syracuseStep 483617 = 362713) B362713
theorem B287011 : Blo 283827 287011 := bstep (se 1 (by rfl) ⟨215258, by rfl⟩ : syracuseStep 287011 = 430517) B430517
theorem B647459 : Blo 283827 647459 := bstep (se 1 (by rfl) ⟨485594, by rfl⟩ : syracuseStep 647459 = 971189) B971189
theorem B811309 : Blo 283827 811309 := bstep (se 3 (by rfl) ⟨152120, by rfl⟩ : syracuseStep 811309 = 304241) B304241
theorem B287027 : Blo 283827 287027 := bstep (se 1 (by rfl) ⟨215270, by rfl⟩ : syracuseStep 287027 = 430541) B430541
theorem B287043 : Blo 283827 287043 := bstep (se 1 (by rfl) ⟨215282, by rfl⟩ : syracuseStep 287043 = 430565) B430565
theorem B287059 : Blo 283827 287059 := bstep (se 1 (by rfl) ⟨215294, by rfl⟩ : syracuseStep 287059 = 430589) B430589
theorem B287075 : Blo 283827 287075 := bstep (se 1 (by rfl) ⟨215306, by rfl⟩ : syracuseStep 287075 = 430613) B430613
theorem B287091 : Blo 283827 287091 := bstep (se 1 (by rfl) ⟨215318, by rfl⟩ : syracuseStep 287091 = 430637) B430637
theorem B287107 : Blo 283827 287107 := bstep (se 1 (by rfl) ⟨215330, by rfl⟩ : syracuseStep 287107 = 430661) B430661
theorem B319891 : Blo 283827 319891 := bstep (se 1 (by rfl) ⟨239918, by rfl⟩ : syracuseStep 319891 = 479837) B479837
theorem B287123 : Blo 283827 287123 := bstep (se 1 (by rfl) ⟨215342, by rfl⟩ : syracuseStep 287123 = 430685) B430685
theorem B483745 : Blo 283827 483745 := bstep (se 2 (by rfl) ⟨181404, by rfl⟩ : syracuseStep 483745 = 362809) B362809
theorem B287139 : Blo 283827 287139 := bstep (se 1 (by rfl) ⟨215354, by rfl⟩ : syracuseStep 287139 = 430709) B430709
theorem B287155 : Blo 283827 287155 := bstep (se 1 (by rfl) ⟨215366, by rfl⟩ : syracuseStep 287155 = 430733) B430733
theorem B483779 : Blo 283827 483779 := bstep (se 1 (by rfl) ⟨362834, by rfl⟩ : syracuseStep 483779 = 725669) B725669
theorem B287171 : Blo 283827 287171 := bstep (se 1 (by rfl) ⟨215378, by rfl⟩ : syracuseStep 287171 = 430757) B430757
theorem B287187 : Blo 283827 287187 := bstep (se 1 (by rfl) ⟨215390, by rfl⟩ : syracuseStep 287187 = 430781) B430781
theorem B287203 : Blo 283827 287203 := bstep (se 1 (by rfl) ⟨215402, by rfl⟩ : syracuseStep 287203 = 430805) B430805
theorem B287219 : Blo 283827 287219 := bstep (se 1 (by rfl) ⟨215414, by rfl⟩ : syracuseStep 287219 = 430829) B430829
theorem B287235 : Blo 283827 287235 := bstep (se 1 (by rfl) ⟨215426, by rfl⟩ : syracuseStep 287235 = 430853) B430853
theorem B287251 : Blo 283827 287251 := bstep (se 1 (by rfl) ⟨215438, by rfl⟩ : syracuseStep 287251 = 430877) B430877
theorem B320035 : Blo 283827 320035 := bstep (se 1 (by rfl) ⟨240026, by rfl⟩ : syracuseStep 320035 = 480053) B480053
theorem B287267 : Blo 283827 287267 := bstep (se 1 (by rfl) ⟨215450, by rfl⟩ : syracuseStep 287267 = 430901) B430901
theorem B287283 : Blo 283827 287283 := bstep (se 1 (by rfl) ⟨215462, by rfl⟩ : syracuseStep 287283 = 430925) B430925
theorem B483907 : Blo 283827 483907 := bstep (se 1 (by rfl) ⟨362930, by rfl⟩ : syracuseStep 483907 = 725861) B725861
theorem B287299 : Blo 283827 287299 := bstep (se 1 (by rfl) ⟨215474, by rfl⟩ : syracuseStep 287299 = 430949) B430949
theorem B287315 : Blo 283827 287315 := bstep (se 1 (by rfl) ⟨215486, by rfl⟩ : syracuseStep 287315 = 430973) B430973
theorem B287331 : Blo 283827 287331 := bstep (se 1 (by rfl) ⟨215498, by rfl⟩ : syracuseStep 287331 = 430997) B430997
theorem B287347 : Blo 283827 287347 := bstep (se 1 (by rfl) ⟨215510, by rfl⟩ : syracuseStep 287347 = 431021) B431021
theorem B287363 : Blo 283827 287363 := bstep (se 1 (by rfl) ⟨215522, by rfl⟩ : syracuseStep 287363 = 431045) B431045
theorem B287379 : Blo 283827 287379 := bstep (se 1 (by rfl) ⟨215534, by rfl⟩ : syracuseStep 287379 = 431069) B431069
theorem B287395 : Blo 283827 287395 := bstep (se 1 (by rfl) ⟨215546, by rfl⟩ : syracuseStep 287395 = 431093) B431093
theorem B320179 : Blo 283827 320179 := bstep (se 1 (by rfl) ⟨240134, by rfl⟩ : syracuseStep 320179 = 480269) B480269
theorem B287411 : Blo 283827 287411 := bstep (se 1 (by rfl) ⟨215558, by rfl⟩ : syracuseStep 287411 = 431117) B431117
theorem B287427 : Blo 283827 287427 := bstep (se 1 (by rfl) ⟨215570, by rfl⟩ : syracuseStep 287427 = 431141) B431141
theorem B484049 : Blo 283827 484049 := bstep (se 2 (by rfl) ⟨181518, by rfl⟩ : syracuseStep 484049 = 363037) B363037
theorem B287443 : Blo 283827 287443 := bstep (se 1 (by rfl) ⟨215582, by rfl⟩ : syracuseStep 287443 = 431165) B431165
theorem B287459 : Blo 283827 287459 := bstep (se 1 (by rfl) ⟨215594, by rfl⟩ : syracuseStep 287459 = 431189) B431189
theorem B287475 : Blo 283827 287475 := bstep (se 1 (by rfl) ⟨215606, by rfl⟩ : syracuseStep 287475 = 431213) B431213
theorem B287491 : Blo 283827 287491 := bstep (se 1 (by rfl) ⟨215618, by rfl⟩ : syracuseStep 287491 = 431237) B431237
theorem B287507 : Blo 283827 287507 := bstep (se 1 (by rfl) ⟨215630, by rfl⟩ : syracuseStep 287507 = 431261) B431261
theorem B287523 : Blo 283827 287523 := bstep (se 1 (by rfl) ⟨215642, by rfl⟩ : syracuseStep 287523 = 431285) B431285
theorem B287539 : Blo 283827 287539 := bstep (se 1 (by rfl) ⟨215654, by rfl⟩ : syracuseStep 287539 = 431309) B431309
theorem B320323 : Blo 283827 320323 := bstep (se 1 (by rfl) ⟨240242, by rfl⟩ : syracuseStep 320323 = 480485) B480485
theorem B287555 : Blo 283827 287555 := bstep (se 1 (by rfl) ⟨215666, by rfl⟩ : syracuseStep 287555 = 431333) B431333
theorem B484177 : Blo 283827 484177 := bstep (se 2 (by rfl) ⟨181566, by rfl⟩ : syracuseStep 484177 = 363133) B363133
theorem B287571 : Blo 283827 287571 := bstep (se 1 (by rfl) ⟨215678, by rfl⟩ : syracuseStep 287571 = 431357) B431357
theorem B287587 : Blo 283827 287587 := bstep (se 1 (by rfl) ⟨215690, by rfl⟩ : syracuseStep 287587 = 431381) B431381
theorem B484211 : Blo 283827 484211 := bstep (se 1 (by rfl) ⟨363158, by rfl⟩ : syracuseStep 484211 = 726317) B726317
theorem B287603 : Blo 283827 287603 := bstep (se 1 (by rfl) ⟨215702, by rfl⟩ : syracuseStep 287603 = 431405) B431405
theorem B287619 : Blo 283827 287619 := bstep (se 1 (by rfl) ⟨215714, by rfl⟩ : syracuseStep 287619 = 431429) B431429
theorem B287635 : Blo 283827 287635 := bstep (se 1 (by rfl) ⟨215726, by rfl⟩ : syracuseStep 287635 = 431453) B431453
theorem B287651 : Blo 283827 287651 := bstep (se 1 (by rfl) ⟨215738, by rfl⟩ : syracuseStep 287651 = 431477) B431477
theorem B287667 : Blo 283827 287667 := bstep (se 1 (by rfl) ⟨215750, by rfl⟩ : syracuseStep 287667 = 431501) B431501
theorem B287683 : Blo 283827 287683 := bstep (se 1 (by rfl) ⟨215762, by rfl⟩ : syracuseStep 287683 = 431525) B431525
theorem B320467 : Blo 283827 320467 := bstep (se 1 (by rfl) ⟨240350, by rfl⟩ : syracuseStep 320467 = 480701) B480701
theorem B287699 : Blo 283827 287699 := bstep (se 1 (by rfl) ⟨215774, by rfl⟩ : syracuseStep 287699 = 431549) B431549
theorem B287715 : Blo 283827 287715 := bstep (se 1 (by rfl) ⟨215786, by rfl⟩ : syracuseStep 287715 = 431573) B431573
theorem B484339 : Blo 283827 484339 := bstep (se 1 (by rfl) ⟨363254, by rfl⟩ : syracuseStep 484339 = 726509) B726509
theorem B287731 : Blo 283827 287731 := bstep (se 1 (by rfl) ⟨215798, by rfl⟩ : syracuseStep 287731 = 431597) B431597
theorem B287747 : Blo 283827 287747 := bstep (se 1 (by rfl) ⟨215810, by rfl⟩ : syracuseStep 287747 = 431621) B431621
theorem B287763 : Blo 283827 287763 := bstep (se 1 (by rfl) ⟨215822, by rfl⟩ : syracuseStep 287763 = 431645) B431645
theorem B386083 : Blo 283827 386083 := bstep (se 1 (by rfl) ⟨289562, by rfl⟩ : syracuseStep 386083 = 579125) B579125
theorem B287779 : Blo 283827 287779 := bstep (se 1 (by rfl) ⟨215834, by rfl⟩ : syracuseStep 287779 = 431669) B431669
theorem B287795 : Blo 283827 287795 := bstep (se 1 (by rfl) ⟨215846, by rfl⟩ : syracuseStep 287795 = 431693) B431693
theorem B287811 : Blo 283827 287811 := bstep (se 1 (by rfl) ⟨215858, by rfl⟩ : syracuseStep 287811 = 431717) B431717
theorem B287827 : Blo 283827 287827 := bstep (se 1 (by rfl) ⟨215870, by rfl⟩ : syracuseStep 287827 = 431741) B431741
theorem B320611 : Blo 283827 320611 := bstep (se 1 (by rfl) ⟨240458, by rfl⟩ : syracuseStep 320611 = 480917) B480917
theorem B484481 : Blo 283827 484481 := bstep (se 2 (by rfl) ⟨181680, by rfl⟩ : syracuseStep 484481 = 363361) B363361
theorem B3663089 : Blo 283827 3663089 := bstep (se 2 (by rfl) ⟨1373658, by rfl⟩ : syracuseStep 3663089 = 2747317) B2747317
theorem B320755 : Blo 283827 320755 := bstep (se 1 (by rfl) ⟨240566, by rfl⟩ : syracuseStep 320755 = 481133) B481133
theorem B484609 : Blo 283827 484609 := bstep (se 2 (by rfl) ⟨181728, by rfl⟩ : syracuseStep 484609 = 363457) B363457
theorem B484643 : Blo 283827 484643 := bstep (se 1 (by rfl) ⟨363482, by rfl⟩ : syracuseStep 484643 = 726965) B726965
theorem B386353 : Blo 283827 386353 := bstep (se 2 (by rfl) ⟨144882, by rfl⟩ : syracuseStep 386353 = 289765) B289765
theorem B1238321 : Blo 283827 1238321 := bstep (se 2 (by rfl) ⟨464370, by rfl⟩ : syracuseStep 1238321 = 928741) B928741
theorem B910673 : Blo 283827 910673 := bstep (se 2 (by rfl) ⟨341502, by rfl⟩ : syracuseStep 910673 = 683005) B683005
theorem B812369 : Blo 283827 812369 := bstep (se 2 (by rfl) ⟨304638, by rfl⟩ : syracuseStep 812369 = 609277) B609277
theorem B320899 : Blo 283827 320899 := bstep (se 1 (by rfl) ⟨240674, by rfl⟩ : syracuseStep 320899 = 481349) B481349
theorem B1369507 : Blo 283827 1369507 := bstep (se 1 (by rfl) ⟨1027130, by rfl⟩ : syracuseStep 1369507 = 2054261) B2054261
theorem B484771 : Blo 283827 484771 := bstep (se 1 (by rfl) ⟨363578, by rfl⟩ : syracuseStep 484771 = 727157) B727157
theorem B321043 : Blo 283827 321043 := bstep (se 1 (by rfl) ⟨240782, by rfl⟩ : syracuseStep 321043 = 481565) B481565
theorem B484913 : Blo 283827 484913 := bstep (se 2 (by rfl) ⟨181842, by rfl⟩ : syracuseStep 484913 = 363685) B363685
theorem B321187 : Blo 283827 321187 := bstep (se 1 (by rfl) ⟨240890, by rfl⟩ : syracuseStep 321187 = 481781) B481781
theorem B485041 : Blo 283827 485041 := bstep (se 2 (by rfl) ⟨181890, by rfl⟩ : syracuseStep 485041 = 363781) B363781
theorem B485075 : Blo 283827 485075 := bstep (se 1 (by rfl) ⟨363806, by rfl⟩ : syracuseStep 485075 = 727613) B727613
theorem B321331 : Blo 283827 321331 := bstep (se 1 (by rfl) ⟨240998, by rfl⟩ : syracuseStep 321331 = 481997) B481997
theorem B354115 : Blo 283827 354115 := bstep (se 1 (by rfl) ⟨265586, by rfl⟩ : syracuseStep 354115 = 531173) B531173
theorem B485203 : Blo 283827 485203 := bstep (se 1 (by rfl) ⟨363902, by rfl⟩ : syracuseStep 485203 = 727805) B727805
theorem B321475 : Blo 283827 321475 := bstep (se 1 (by rfl) ⟨241106, by rfl⟩ : syracuseStep 321475 = 482213) B482213
theorem B485345 : Blo 283827 485345 := bstep (se 2 (by rfl) ⟨182004, by rfl⟩ : syracuseStep 485345 = 364009) B364009
theorem B813041 : Blo 283827 813041 := bstep (se 2 (by rfl) ⟨304890, by rfl⟩ : syracuseStep 813041 = 609781) B609781
theorem B518179 : Blo 283827 518179 := bstep (se 1 (by rfl) ⟨388634, by rfl⟩ : syracuseStep 518179 = 777269) B777269
theorem B321619 : Blo 283827 321619 := bstep (se 1 (by rfl) ⟨241214, by rfl⟩ : syracuseStep 321619 = 482429) B482429
theorem B485473 : Blo 283827 485473 := bstep (se 2 (by rfl) ⟨182052, by rfl⟩ : syracuseStep 485473 = 364105) B364105
theorem B485507 : Blo 283827 485507 := bstep (se 1 (by rfl) ⟨364130, by rfl⟩ : syracuseStep 485507 = 728261) B728261
theorem B911569 : Blo 283827 911569 := bstep (se 2 (by rfl) ⟨341838, by rfl⟩ : syracuseStep 911569 = 683677) B683677
theorem B321763 : Blo 283827 321763 := bstep (se 1 (by rfl) ⟨241322, by rfl⟩ : syracuseStep 321763 = 482645) B482645
theorem B1370353 : Blo 283827 1370353 := bstep (se 2 (by rfl) ⟨513882, by rfl⟩ : syracuseStep 1370353 = 1027765) B1027765
theorem B485635 : Blo 283827 485635 := bstep (se 1 (by rfl) ⟨364226, by rfl⟩ : syracuseStep 485635 = 728453) B728453
theorem B1042723 : Blo 283827 1042723 := bstep (se 1 (by rfl) ⟨782042, by rfl⟩ : syracuseStep 1042723 = 1564085) B1564085
theorem B321907 : Blo 283827 321907 := bstep (se 1 (by rfl) ⟨241430, by rfl⟩ : syracuseStep 321907 = 482861) B482861
theorem B387553 : Blo 283827 387553 := bstep (se 2 (by rfl) ⟨145332, by rfl⟩ : syracuseStep 387553 = 290665) B290665
theorem B322051 : Blo 283827 322051 := bstep (se 1 (by rfl) ⟨241538, by rfl⟩ : syracuseStep 322051 = 483077) B483077
theorem B322195 : Blo 283827 322195 := bstep (se 1 (by rfl) ⟨241646, by rfl⟩ : syracuseStep 322195 = 483293) B483293
theorem B813827 : Blo 283827 813827 := bstep (se 1 (by rfl) ⟨610370, by rfl⟩ : syracuseStep 813827 = 1220741) B1220741
theorem B322339 : Blo 283827 322339 := bstep (se 1 (by rfl) ⟨241754, by rfl⟩ : syracuseStep 322339 = 483509) B483509
theorem B322483 : Blo 283827 322483 := bstep (se 1 (by rfl) ⟨241862, by rfl⟩ : syracuseStep 322483 = 483725) B483725
theorem B486337 : Blo 283827 486337 := bstep (se 2 (by rfl) ⟨182376, by rfl⟩ : syracuseStep 486337 = 364753) B364753
theorem B322627 : Blo 283827 322627 := bstep (se 1 (by rfl) ⟨241970, by rfl⟩ : syracuseStep 322627 = 483941) B483941
theorem B814157 : Blo 283827 814157 := bstep (se 3 (by rfl) ⟨152654, by rfl⟩ : syracuseStep 814157 = 305309) B305309
theorem B814225 : Blo 283827 814225 := bstep (se 2 (by rfl) ⟨305334, by rfl⟩ : syracuseStep 814225 = 610669) B610669
theorem B322771 : Blo 283827 322771 := bstep (se 1 (by rfl) ⟨242078, by rfl⟩ : syracuseStep 322771 = 484157) B484157
theorem B650531 : Blo 283827 650531 := bstep (se 1 (by rfl) ⟨487898, by rfl⟩ : syracuseStep 650531 = 975797) B975797
theorem B322915 : Blo 283827 322915 := bstep (se 1 (by rfl) ⟨242186, by rfl⟩ : syracuseStep 322915 = 484373) B484373
theorem B1961329 : Blo 283827 1961329 := bstep (se 2 (by rfl) ⟨735498, by rfl⟩ : syracuseStep 1961329 = 1470997) B1470997
theorem B814499 : Blo 283827 814499 := bstep (se 1 (by rfl) ⟨610874, by rfl⟩ : syracuseStep 814499 = 1221749) B1221749
theorem B323059 : Blo 283827 323059 := bstep (se 1 (by rfl) ⟨242294, by rfl⟩ : syracuseStep 323059 = 484589) B484589
theorem B3468899 : Blo 283827 3468899 := bstep (se 1 (by rfl) ⟨2601674, by rfl⟩ : syracuseStep 3468899 = 5203349) B5203349
theorem B323203 : Blo 283827 323203 := bstep (se 1 (by rfl) ⟨242402, by rfl⟩ : syracuseStep 323203 = 484805) B484805
theorem B290467 : Blo 283827 290467 := bstep (se 1 (by rfl) ⟨217850, by rfl⟩ : syracuseStep 290467 = 435701) B435701
theorem B913133 : Blo 283827 913133 := bstep (se 3 (by rfl) ⟨171212, by rfl⟩ : syracuseStep 913133 = 342425) B342425
theorem B1437425 : Blo 283827 1437425 := bstep (se 2 (by rfl) ⟨539034, by rfl⟩ : syracuseStep 1437425 = 1078069) B1078069
theorem B1634053 : Blo 283827 1634053 := bstep (se 4 (by rfl) ⟨153192, by rfl⟩ : syracuseStep 1634053 = 306385) B306385
theorem B323347 : Blo 283827 323347 := bstep (se 1 (by rfl) ⟨242510, by rfl⟩ : syracuseStep 323347 = 485021) B485021
theorem B1830725 : Blo 283827 1830725 := bstep (se 4 (by rfl) ⟨171630, by rfl⟩ : syracuseStep 1830725 = 343261) B343261
theorem B323491 : Blo 283827 323491 := bstep (se 1 (by rfl) ⟨242618, by rfl⟩ : syracuseStep 323491 = 485237) B485237
theorem B454657 : Blo 283827 454657 := bstep (se 2 (by rfl) ⟨170496, by rfl⟩ : syracuseStep 454657 = 340993) B340993
theorem B520195 : Blo 283827 520195 := bstep (se 1 (by rfl) ⟨390146, by rfl⟩ : syracuseStep 520195 = 780293) B780293
theorem B323635 : Blo 283827 323635 := bstep (se 1 (by rfl) ⟨242726, by rfl⟩ : syracuseStep 323635 = 485453) B485453
theorem B323779 : Blo 283827 323779 := bstep (se 1 (by rfl) ⟨242834, by rfl⟩ : syracuseStep 323779 = 485669) B485669
theorem B815341 : Blo 283827 815341 := bstep (se 3 (by rfl) ⟨152876, by rfl⟩ : syracuseStep 815341 = 305753) B305753
theorem B815501 : Blo 283827 815501 := bstep (se 3 (by rfl) ⟨152906, by rfl⟩ : syracuseStep 815501 = 305813) B305813
theorem B815683 : Blo 283827 815683 := bstep (se 1 (by rfl) ⟨611762, by rfl⟩ : syracuseStep 815683 = 1223525) B1223525
theorem B324307 : Blo 283827 324307 := bstep (se 1 (by rfl) ⟨243230, by rfl⟩ : syracuseStep 324307 = 486461) B486461
theorem B389873 : Blo 283827 389873 := bstep (se 2 (by rfl) ⟨146202, by rfl⟩ : syracuseStep 389873 = 292405) B292405
theorem B881425 : Blo 283827 881425 := bstep (se 2 (by rfl) ⟨330534, by rfl⟩ : syracuseStep 881425 = 661069) B661069
theorem B1438883 : Blo 283827 1438883 := bstep (se 1 (by rfl) ⟨1079162, by rfl⟩ : syracuseStep 1438883 = 2158325) B2158325
theorem B455939 : Blo 283827 455939 := bstep (se 1 (by rfl) ⟨341954, by rfl⟩ : syracuseStep 455939 = 683909) B683909
theorem B1078541 : Blo 283827 1078541 := bstep (se 3 (by rfl) ⟨202226, by rfl⟩ : syracuseStep 1078541 = 404453) B404453
theorem B456035 : Blo 283827 456035 := bstep (se 1 (by rfl) ⟨342026, by rfl⟩ : syracuseStep 456035 = 684053) B684053
theorem B456067 : Blo 283827 456067 := bstep (se 1 (by rfl) ⟨342050, by rfl⟩ : syracuseStep 456067 = 684101) B684101
theorem B1734257 : Blo 283827 1734257 := bstep (se 2 (by rfl) ⟨650346, by rfl⟩ : syracuseStep 1734257 = 1300693) B1300693
theorem B2160269 : Blo 283827 2160269 := bstep (se 3 (by rfl) ⟨405050, by rfl⟩ : syracuseStep 2160269 = 810101) B810101
theorem B2455181 : Blo 283827 2455181 := bstep (se 3 (by rfl) ⟨460346, by rfl⟩ : syracuseStep 2455181 = 920693) B920693
theorem B1636037 : Blo 283827 1636037 := bstep (se 4 (by rfl) ⟨153378, by rfl⟩ : syracuseStep 1636037 = 306757) B306757
theorem B817073 : Blo 283827 817073 := bstep (se 2 (by rfl) ⟨306402, by rfl⟩ : syracuseStep 817073 = 612805) B612805
theorem B1439693 : Blo 283827 1439693 := bstep (se 3 (by rfl) ⟨269942, by rfl⟩ : syracuseStep 1439693 = 539885) B539885
theorem B718865 : Blo 283827 718865 := bstep (se 2 (by rfl) ⟨269574, by rfl⟩ : syracuseStep 718865 = 539149) B539149
theorem B1079345 : Blo 283827 1079345 := bstep (se 2 (by rfl) ⟨404754, by rfl⟩ : syracuseStep 1079345 = 809509) B809509
theorem B718915 : Blo 283827 718915 := bstep (se 1 (by rfl) ⟨539186, by rfl⟩ : syracuseStep 718915 = 1078373) B1078373
theorem B915619 : Blo 283827 915619 := bstep (se 1 (by rfl) ⟨686714, by rfl⟩ : syracuseStep 915619 = 1373429) B1373429
theorem B489649 : Blo 283827 489649 := bstep (se 2 (by rfl) ⟨183618, by rfl⟩ : syracuseStep 489649 = 367237) B367237
theorem B719057 : Blo 283827 719057 := bstep (se 2 (by rfl) ⟨269646, by rfl⟩ : syracuseStep 719057 = 539293) B539293
theorem B456977 : Blo 283827 456977 := bstep (se 2 (by rfl) ⟨171366, by rfl⟩ : syracuseStep 456977 = 342733) B342733
theorem B915761 : Blo 283827 915761 := bstep (se 2 (by rfl) ⟨343410, by rfl⟩ : syracuseStep 915761 = 686821) B686821
theorem B1571185 : Blo 283827 1571185 := bstep (se 2 (by rfl) ⟨589194, by rfl⟩ : syracuseStep 1571185 = 1178389) B1178389
theorem B915875 : Blo 283827 915875 := bstep (se 1 (by rfl) ⟨686906, by rfl⟩ : syracuseStep 915875 = 1373813) B1373813
theorem B686513 : Blo 283827 686513 := bstep (se 2 (by rfl) ⟨257442, by rfl⟩ : syracuseStep 686513 = 514885) B514885
theorem B9238981 : Blo 283827 9238981 := bstep (se 4 (by rfl) ⟨866154, by rfl⟩ : syracuseStep 9238981 = 1732309) B1732309
theorem B3111493 : Blo 283827 3111493 := bstep (se 4 (by rfl) ⟨291702, by rfl⟩ : syracuseStep 3111493 = 583405) B583405
theorem B1080013 : Blo 283827 1080013 := bstep (se 3 (by rfl) ⟨202502, by rfl⟩ : syracuseStep 1080013 = 405005) B405005
theorem B490225 : Blo 283827 490225 := bstep (se 2 (by rfl) ⟨183834, by rfl⟩ : syracuseStep 490225 = 367669) B367669
theorem B818029 : Blo 283827 818029 := bstep (se 3 (by rfl) ⟨153380, by rfl⟩ : syracuseStep 818029 = 306761) B306761
theorem B818257 : Blo 283827 818257 := bstep (se 2 (by rfl) ⟨306846, by rfl⟩ : syracuseStep 818257 = 613693) B613693
theorem B720049 : Blo 283827 720049 := bstep (se 2 (by rfl) ⟨270018, by rfl⟩ : syracuseStep 720049 = 540037) B540037
theorem B359635 : Blo 283827 359635 := bstep (se 1 (by rfl) ⟨269726, by rfl⟩ : syracuseStep 359635 = 539453) B539453
theorem B818417 : Blo 283827 818417 := bstep (se 2 (by rfl) ⟨306906, by rfl⟩ : syracuseStep 818417 = 613813) B613813
theorem B359731 : Blo 283827 359731 := bstep (se 1 (by rfl) ⟨269798, by rfl⟩ : syracuseStep 359731 = 539597) B539597
theorem B818531 : Blo 283827 818531 := bstep (se 1 (by rfl) ⟨613898, by rfl⟩ : syracuseStep 818531 = 1227797) B1227797
theorem B916849 : Blo 283827 916849 := bstep (se 2 (by rfl) ⟨343818, by rfl⟩ : syracuseStep 916849 = 687637) B687637
theorem B720323 : Blo 283827 720323 := bstep (se 1 (by rfl) ⟨540242, by rfl⟩ : syracuseStep 720323 = 1080485) B1080485
theorem B1080803 : Blo 283827 1080803 := bstep (se 1 (by rfl) ⟨810602, by rfl⟩ : syracuseStep 1080803 = 1621205) B1621205
theorem B1310179 : Blo 283827 1310179 := bstep (se 1 (by rfl) ⟨982634, by rfl⟩ : syracuseStep 1310179 = 1965269) B1965269
theorem B458291 : Blo 283827 458291 := bstep (se 1 (by rfl) ⟨343718, by rfl⟩ : syracuseStep 458291 = 687437) B687437
theorem B491059 : Blo 283827 491059 := bstep (se 1 (by rfl) ⟨368294, by rfl⟩ : syracuseStep 491059 = 736589) B736589
theorem B720515 : Blo 283827 720515 := bstep (se 1 (by rfl) ⟨540386, by rfl⟩ : syracuseStep 720515 = 1080773) B1080773
theorem B425747 : Blo 283827 425747 := bstep (se 1 (by rfl) ⟨319310, by rfl⟩ : syracuseStep 425747 = 638621) B638621
theorem B360227 : Blo 283827 360227 := bstep (se 1 (by rfl) ⟨270170, by rfl⟩ : syracuseStep 360227 = 540341) B540341
theorem B425777 : Blo 283827 425777 := bstep (se 2 (by rfl) ⟨159666, by rfl⟩ : syracuseStep 425777 = 319333) B319333
theorem B425795 : Blo 283827 425795 := bstep (se 1 (by rfl) ⟨319346, by rfl⟩ : syracuseStep 425795 = 638693) B638693
theorem B425825 : Blo 283827 425825 := bstep (se 2 (by rfl) ⟨159684, by rfl⟩ : syracuseStep 425825 = 319369) B319369
theorem B425843 : Blo 283827 425843 := bstep (se 1 (by rfl) ⟨319382, by rfl⟩ : syracuseStep 425843 = 638765) B638765
theorem B425873 : Blo 283827 425873 := bstep (se 2 (by rfl) ⟨159702, by rfl⟩ : syracuseStep 425873 = 319405) B319405
theorem B425891 : Blo 283827 425891 := bstep (se 1 (by rfl) ⟨319418, by rfl⟩ : syracuseStep 425891 = 638837) B638837
theorem B425921 : Blo 283827 425921 := bstep (se 2 (by rfl) ⟨159720, by rfl⟩ : syracuseStep 425921 = 319441) B319441
theorem B425939 : Blo 283827 425939 := bstep (se 1 (by rfl) ⟨319454, by rfl⟩ : syracuseStep 425939 = 638909) B638909
theorem B425969 : Blo 283827 425969 := bstep (se 2 (by rfl) ⟨159738, by rfl⟩ : syracuseStep 425969 = 319477) B319477
theorem B327691 : Blo 283827 327691 := bstep (se 1 (by rfl) ⟨245768, by rfl⟩ : syracuseStep 327691 = 491537) B491537
theorem B3244049 : Blo 283827 3244049 := bstep (se 2 (by rfl) ⟨1216518, by rfl⟩ : syracuseStep 3244049 = 2433037) B2433037
theorem B1376273 : Blo 283827 1376273 := bstep (se 2 (by rfl) ⟨516102, by rfl⟩ : syracuseStep 1376273 = 1032205) B1032205
theorem B1048627 : Blo 283827 1048627 := bstep (se 1 (by rfl) ⟨786470, by rfl⟩ : syracuseStep 1048627 = 1572941) B1572941
theorem B426059 : Blo 283827 426059 := bstep (se 1 (by rfl) ⟨319544, by rfl⟩ : syracuseStep 426059 = 639089) B639089
theorem B720971 : Blo 283827 720971 := bstep (se 1 (by rfl) ⟨540728, by rfl⟩ : syracuseStep 720971 = 1081457) B1081457
theorem B426071 : Blo 283827 426071 := bstep (se 1 (by rfl) ⟨319553, by rfl⟩ : syracuseStep 426071 = 639107) B639107
theorem B655447 : Blo 283827 655447 := bstep (se 1 (by rfl) ⟨491585, by rfl⟩ : syracuseStep 655447 = 983171) B983171
theorem B426137 : Blo 283827 426137 := bstep (se 2 (by rfl) ⟨159801, by rfl⟩ : syracuseStep 426137 = 319603) B319603
theorem B426251 : Blo 283827 426251 := bstep (se 1 (by rfl) ⟨319688, by rfl⟩ : syracuseStep 426251 = 639377) B639377
theorem B426263 : Blo 283827 426263 := bstep (se 1 (by rfl) ⟨319697, by rfl⟩ : syracuseStep 426263 = 639395) B639395
theorem B1638701 : Blo 283827 1638701 := bstep (se 3 (by rfl) ⟨307256, by rfl⟩ : syracuseStep 1638701 = 614513) B614513
theorem B1442123 : Blo 283827 1442123 := bstep (se 1 (by rfl) ⟨1081592, by rfl⟩ : syracuseStep 1442123 = 2163185) B2163185
theorem B426329 : Blo 283827 426329 := bstep (se 2 (by rfl) ⟨159873, by rfl⟩ : syracuseStep 426329 = 319747) B319747
theorem B2326877 : Blo 283827 2326877 := bstep (se 3 (by rfl) ⟨436289, by rfl⟩ : syracuseStep 2326877 = 872579) B872579
theorem B1114499 : Blo 283827 1114499 := bstep (se 1 (by rfl) ⟨835874, by rfl⟩ : syracuseStep 1114499 = 1671749) B1671749
theorem B1081745 : Blo 283827 1081745 := bstep (se 2 (by rfl) ⟨405654, by rfl⟩ : syracuseStep 1081745 = 811309) B811309
theorem B721345 : Blo 283827 721345 := bstep (se 2 (by rfl) ⟨270504, by rfl⟩ : syracuseStep 721345 = 541009) B541009
theorem B426443 : Blo 283827 426443 := bstep (se 1 (by rfl) ⟨319832, by rfl⟩ : syracuseStep 426443 = 639665) B639665
theorem B426455 : Blo 283827 426455 := bstep (se 1 (by rfl) ⟨319841, by rfl⟩ : syracuseStep 426455 = 639683) B639683
theorem B426521 : Blo 283827 426521 := bstep (se 2 (by rfl) ⟨159945, by rfl⟩ : syracuseStep 426521 = 319891) B319891
theorem B2327105 : Blo 283827 2327105 := bstep (se 2 (by rfl) ⟨872664, by rfl⟩ : syracuseStep 2327105 = 1745329) B1745329
theorem B1049219 : Blo 283827 1049219 := bstep (se 1 (by rfl) ⟨786914, by rfl⟩ : syracuseStep 1049219 = 1573829) B1573829
theorem B426635 : Blo 283827 426635 := bstep (se 1 (by rfl) ⟨319976, by rfl⟩ : syracuseStep 426635 = 639953) B639953
theorem B426647 : Blo 283827 426647 := bstep (se 1 (by rfl) ⟨319985, by rfl⟩ : syracuseStep 426647 = 639971) B639971
theorem B426713 : Blo 283827 426713 := bstep (se 2 (by rfl) ⟨160017, by rfl⟩ : syracuseStep 426713 = 320035) B320035
theorem B918233 : Blo 283827 918233 := bstep (se 2 (by rfl) ⟨344337, by rfl⟩ : syracuseStep 918233 = 688675) B688675
theorem B1966913 : Blo 283827 1966913 := bstep (se 2 (by rfl) ⟨737592, by rfl⟩ : syracuseStep 1966913 = 1475185) B1475185
theorem B426827 : Blo 283827 426827 := bstep (se 1 (by rfl) ⟨320120, by rfl⟩ : syracuseStep 426827 = 640241) B640241
theorem B426839 : Blo 283827 426839 := bstep (se 1 (by rfl) ⟨320129, by rfl⟩ : syracuseStep 426839 = 640259) B640259
theorem B426905 : Blo 283827 426905 := bstep (se 2 (by rfl) ⟨160089, by rfl⟩ : syracuseStep 426905 = 320179) B320179
theorem B427019 : Blo 283827 427019 := bstep (se 1 (by rfl) ⟨320264, by rfl⟩ : syracuseStep 427019 = 640529) B640529
theorem B427031 : Blo 283827 427031 := bstep (se 1 (by rfl) ⟨320273, by rfl⟩ : syracuseStep 427031 = 640547) B640547
theorem B721943 : Blo 283827 721943 := bstep (se 1 (by rfl) ⟨541457, by rfl⟩ : syracuseStep 721943 = 1082915) B1082915
theorem B1082443 : Blo 283827 1082443 := bstep (se 1 (by rfl) ⟨811832, by rfl⟩ : syracuseStep 1082443 = 1623665) B1623665
theorem B427097 : Blo 283827 427097 := bstep (se 2 (by rfl) ⟨160161, by rfl⟩ : syracuseStep 427097 = 320323) B320323
theorem B4916375 : Blo 283827 4916375 := bstep (se 1 (by rfl) ⟨3687281, by rfl⟩ : syracuseStep 4916375 = 7374563) B7374563
theorem B427211 : Blo 283827 427211 := bstep (se 1 (by rfl) ⟨320408, by rfl⟩ : syracuseStep 427211 = 640817) B640817
theorem B361675 : Blo 283827 361675 := bstep (se 1 (by rfl) ⟨271256, by rfl⟩ : syracuseStep 361675 = 542513) B542513
theorem B427223 : Blo 283827 427223 := bstep (se 1 (by rfl) ⟨320417, by rfl⟩ : syracuseStep 427223 = 640835) B640835
theorem B427289 : Blo 283827 427289 := bstep (se 2 (by rfl) ⟨160233, by rfl⟩ : syracuseStep 427289 = 320467) B320467
theorem B1082717 : Blo 283827 1082717 := bstep (se 3 (by rfl) ⟨203009, by rfl⟩ : syracuseStep 1082717 = 406019) B406019
theorem B4130149 : Blo 283827 4130149 := bstep (se 4 (by rfl) ⟨387201, by rfl⟩ : syracuseStep 4130149 = 774403) B774403
theorem B427403 : Blo 283827 427403 := bstep (se 1 (by rfl) ⟨320552, by rfl⟩ : syracuseStep 427403 = 641105) B641105
theorem B427415 : Blo 283827 427415 := bstep (se 1 (by rfl) ⟨320561, by rfl⟩ : syracuseStep 427415 = 641123) B641123
theorem B329131 : Blo 283827 329131 := bstep (se 1 (by rfl) ⟨246848, by rfl⟩ : syracuseStep 329131 = 493697) B493697
theorem B427481 : Blo 283827 427481 := bstep (se 2 (by rfl) ⟨160305, by rfl⟩ : syracuseStep 427481 = 320611) B320611
theorem B427595 : Blo 283827 427595 := bstep (se 1 (by rfl) ⟨320696, by rfl⟩ : syracuseStep 427595 = 641393) B641393
theorem B4982347 : Blo 283827 4982347 := bstep (se 1 (by rfl) ⟨3736760, by rfl⟩ : syracuseStep 4982347 = 7473521) B7473521
theorem B427607 : Blo 283827 427607 := bstep (se 1 (by rfl) ⟨320705, by rfl⟩ : syracuseStep 427607 = 641411) B641411
theorem B427673 : Blo 283827 427673 := bstep (se 2 (by rfl) ⟨160377, by rfl⟩ : syracuseStep 427673 = 320755) B320755
theorem B427787 : Blo 283827 427787 := bstep (se 1 (by rfl) ⟨320840, by rfl⟩ : syracuseStep 427787 = 641681) B641681
theorem B427799 : Blo 283827 427799 := bstep (se 1 (by rfl) ⟨320849, by rfl⟩ : syracuseStep 427799 = 641699) B641699
theorem B722753 : Blo 283827 722753 := bstep (se 2 (by rfl) ⟨271032, by rfl⟩ : syracuseStep 722753 = 542065) B542065
theorem B427865 : Blo 283827 427865 := bstep (se 2 (by rfl) ⟨160449, by rfl⟩ : syracuseStep 427865 = 320899) B320899
theorem B427979 : Blo 283827 427979 := bstep (se 1 (by rfl) ⟨320984, by rfl⟩ : syracuseStep 427979 = 641969) B641969
theorem B427991 : Blo 283827 427991 := bstep (se 1 (by rfl) ⟨320993, by rfl⟩ : syracuseStep 427991 = 641987) B641987
theorem B1083415 : Blo 283827 1083415 := bstep (se 1 (by rfl) ⟨812561, by rfl⟩ : syracuseStep 1083415 = 1625123) B1625123
theorem B428057 : Blo 283827 428057 := bstep (se 2 (by rfl) ⟨160521, by rfl⟩ : syracuseStep 428057 = 321043) B321043
theorem B1443905 : Blo 283827 1443905 := bstep (se 2 (by rfl) ⟨541464, by rfl⟩ : syracuseStep 1443905 = 1082929) B1082929
theorem B428171 : Blo 283827 428171 := bstep (se 1 (by rfl) ⟨321128, by rfl⟩ : syracuseStep 428171 = 642257) B642257
theorem B428183 : Blo 283827 428183 := bstep (se 1 (by rfl) ⟨321137, by rfl⟩ : syracuseStep 428183 = 642275) B642275
theorem B362647 : Blo 283827 362647 := bstep (se 1 (by rfl) ⟨271985, by rfl⟩ : syracuseStep 362647 = 543971) B543971
theorem B3672215 : Blo 283827 3672215 := bstep (se 1 (by rfl) ⟨2754161, by rfl⟩ : syracuseStep 3672215 = 5508323) B5508323
theorem B428249 : Blo 283827 428249 := bstep (se 2 (by rfl) ⟨160593, by rfl⟩ : syracuseStep 428249 = 321187) B321187
theorem B919873 : Blo 283827 919873 := bstep (se 2 (by rfl) ⟨344952, by rfl⟩ : syracuseStep 919873 = 689905) B689905
theorem B428363 : Blo 283827 428363 := bstep (se 1 (by rfl) ⟨321272, by rfl⟩ : syracuseStep 428363 = 642545) B642545
theorem B428375 : Blo 283827 428375 := bstep (se 1 (by rfl) ⟨321281, by rfl⟩ : syracuseStep 428375 = 642563) B642563
theorem B723289 : Blo 283827 723289 := bstep (se 2 (by rfl) ⟨271233, by rfl⟩ : syracuseStep 723289 = 542467) B542467
theorem B428441 : Blo 283827 428441 := bstep (se 2 (by rfl) ⟨160665, by rfl⟩ : syracuseStep 428441 = 321331) B321331
theorem B428555 : Blo 283827 428555 := bstep (se 1 (by rfl) ⟨321416, by rfl⟩ : syracuseStep 428555 = 642833) B642833
theorem B428567 : Blo 283827 428567 := bstep (se 1 (by rfl) ⟨321425, by rfl⟩ : syracuseStep 428567 = 642851) B642851
theorem B1018391 : Blo 283827 1018391 := bstep (se 1 (by rfl) ⟨763793, by rfl⟩ : syracuseStep 1018391 = 1527587) B1527587
theorem B428633 : Blo 283827 428633 := bstep (se 2 (by rfl) ⟨160737, by rfl⟩ : syracuseStep 428633 = 321475) B321475
theorem B428747 : Blo 283827 428747 := bstep (se 1 (by rfl) ⟨321560, by rfl⟩ : syracuseStep 428747 = 643121) B643121
theorem B428759 : Blo 283827 428759 := bstep (se 1 (by rfl) ⟨321569, by rfl⟩ : syracuseStep 428759 = 643139) B643139
theorem B690905 : Blo 283827 690905 := bstep (se 2 (by rfl) ⟨259089, by rfl⟩ : syracuseStep 690905 = 518179) B518179
theorem B428825 : Blo 283827 428825 := bstep (se 2 (by rfl) ⟨160809, by rfl⟩ : syracuseStep 428825 = 321619) B321619
theorem B1084205 : Blo 283827 1084205 := bstep (se 3 (by rfl) ⟨203288, by rfl⟩ : syracuseStep 1084205 = 406577) B406577
theorem B3246965 : Blo 283827 3246965 := bstep (se 5 (by rfl) ⟨152201, by rfl⟩ : syracuseStep 3246965 = 304403) B304403
theorem B428939 : Blo 283827 428939 := bstep (se 1 (by rfl) ⟨321704, by rfl⟩ : syracuseStep 428939 = 643409) B643409
theorem B428951 : Blo 283827 428951 := bstep (se 1 (by rfl) ⟨321713, by rfl⟩ : syracuseStep 428951 = 643427) B643427
theorem B1215425 : Blo 283827 1215425 := bstep (se 2 (by rfl) ⟨455784, by rfl⟩ : syracuseStep 1215425 = 911569) B911569
theorem B363467 : Blo 283827 363467 := bstep (se 1 (by rfl) ⟨272600, by rfl⟩ : syracuseStep 363467 = 545201) B545201
theorem B429017 : Blo 283827 429017 := bstep (se 2 (by rfl) ⟨160881, by rfl⟩ : syracuseStep 429017 = 321763) B321763
theorem B429131 : Blo 283827 429131 := bstep (se 1 (by rfl) ⟨321848, by rfl⟩ : syracuseStep 429131 = 643697) B643697
theorem B429143 : Blo 283827 429143 := bstep (se 1 (by rfl) ⟨321857, by rfl⟩ : syracuseStep 429143 = 643715) B643715
theorem B429209 : Blo 283827 429209 := bstep (se 2 (by rfl) ⟨160953, by rfl⟩ : syracuseStep 429209 = 321907) B321907
theorem B429323 : Blo 283827 429323 := bstep (se 1 (by rfl) ⟨321992, by rfl⟩ : syracuseStep 429323 = 643985) B643985
theorem B429335 : Blo 283827 429335 := bstep (se 1 (by rfl) ⟨322001, by rfl⟩ : syracuseStep 429335 = 644003) B644003
theorem B429401 : Blo 283827 429401 := bstep (se 2 (by rfl) ⟨161025, by rfl⟩ : syracuseStep 429401 = 322051) B322051
theorem B724403 : Blo 283827 724403 := bstep (se 1 (by rfl) ⟨543302, by rfl⟩ : syracuseStep 724403 = 1086605) B1086605
theorem B429515 : Blo 283827 429515 := bstep (se 1 (by rfl) ⟨322136, by rfl⟩ : syracuseStep 429515 = 644273) B644273
theorem B429527 : Blo 283827 429527 := bstep (se 1 (by rfl) ⟨322145, by rfl⟩ : syracuseStep 429527 = 644291) B644291
theorem B429593 : Blo 283827 429593 := bstep (se 2 (by rfl) ⟨161097, by rfl⟩ : syracuseStep 429593 = 322195) B322195
theorem B1216093 : Blo 283827 1216093 := bstep (se 3 (by rfl) ⟨228017, by rfl⟩ : syracuseStep 1216093 = 456035) B456035
theorem B429707 : Blo 283827 429707 := bstep (se 1 (by rfl) ⟨322280, by rfl⟩ : syracuseStep 429707 = 644561) B644561
theorem B364171 : Blo 283827 364171 := bstep (se 1 (by rfl) ⟨273128, by rfl⟩ : syracuseStep 364171 = 546257) B546257
theorem B429719 : Blo 283827 429719 := bstep (se 1 (by rfl) ⟨322289, by rfl⟩ : syracuseStep 429719 = 644579) B644579
theorem B724697 : Blo 283827 724697 := bstep (se 2 (by rfl) ⟨271761, by rfl⟩ : syracuseStep 724697 = 543523) B543523
theorem B429785 : Blo 283827 429785 := bstep (se 2 (by rfl) ⟨161169, by rfl⟩ : syracuseStep 429785 = 322339) B322339
theorem B429899 : Blo 283827 429899 := bstep (se 1 (by rfl) ⟨322424, by rfl⟩ : syracuseStep 429899 = 644849) B644849
theorem B429911 : Blo 283827 429911 := bstep (se 1 (by rfl) ⟨322433, by rfl⟩ : syracuseStep 429911 = 644867) B644867
theorem B429977 : Blo 283827 429977 := bstep (se 2 (by rfl) ⟨161241, by rfl⟩ : syracuseStep 429977 = 322483) B322483
theorem B1445849 : Blo 283827 1445849 := bstep (se 2 (by rfl) ⟨542193, by rfl⟩ : syracuseStep 1445849 = 1084387) B1084387
theorem B430091 : Blo 283827 430091 := bstep (se 1 (by rfl) ⟨322568, by rfl⟩ : syracuseStep 430091 = 645137) B645137
theorem B430103 : Blo 283827 430103 := bstep (se 1 (by rfl) ⟨322577, by rfl⟩ : syracuseStep 430103 = 645155) B645155
theorem B430169 : Blo 283827 430169 := bstep (se 2 (by rfl) ⟨161313, by rfl⟩ : syracuseStep 430169 = 322627) B322627
theorem B1380503 : Blo 283827 1380503 := bstep (se 1 (by rfl) ⟨1035377, by rfl⟩ : syracuseStep 1380503 = 2070755) B2070755
theorem B1216691 : Blo 283827 1216691 := bstep (se 1 (by rfl) ⟨912518, by rfl⟩ : syracuseStep 1216691 = 1825037) B1825037
theorem B1085633 : Blo 283827 1085633 := bstep (se 2 (by rfl) ⟨407112, by rfl⟩ : syracuseStep 1085633 = 814225) B814225
theorem B430283 : Blo 283827 430283 := bstep (se 1 (by rfl) ⟨322712, by rfl⟩ : syracuseStep 430283 = 645425) B645425
theorem B430295 : Blo 283827 430295 := bstep (se 1 (by rfl) ⟨322721, by rfl⟩ : syracuseStep 430295 = 645443) B645443
theorem B18583829 : Blo 283827 18583829 := bstep (se 6 (by rfl) ⟨435558, by rfl⟩ : syracuseStep 18583829 = 871117) B871117
theorem B430361 : Blo 283827 430361 := bstep (se 2 (by rfl) ⟨161385, by rfl⟩ : syracuseStep 430361 = 322771) B322771
theorem B4624685 : Blo 283827 4624685 := bstep (se 3 (by rfl) ⟨867128, by rfl⟩ : syracuseStep 4624685 = 1734257) B1734257
theorem B430475 : Blo 283827 430475 := bstep (se 1 (by rfl) ⟨322856, by rfl⟩ : syracuseStep 430475 = 645713) B645713
theorem B430487 : Blo 283827 430487 := bstep (se 1 (by rfl) ⟨322865, by rfl⟩ : syracuseStep 430487 = 645731) B645731
theorem B1151405 : Blo 283827 1151405 := bstep (se 3 (by rfl) ⟨215888, by rfl⟩ : syracuseStep 1151405 = 431777) B431777
theorem B430553 : Blo 283827 430553 := bstep (se 2 (by rfl) ⟨161457, by rfl⟩ : syracuseStep 430553 = 322915) B322915
theorem B1151533 : Blo 283827 1151533 := bstep (se 3 (by rfl) ⟨215912, by rfl⟩ : syracuseStep 1151533 = 431825) B431825
theorem B430667 : Blo 283827 430667 := bstep (se 1 (by rfl) ⟨323000, by rfl⟩ : syracuseStep 430667 = 646001) B646001
theorem B430679 : Blo 283827 430679 := bstep (se 1 (by rfl) ⟨323009, by rfl⟩ : syracuseStep 430679 = 646019) B646019
theorem B430745 : Blo 283827 430745 := bstep (se 2 (by rfl) ⟨161529, by rfl⟩ : syracuseStep 430745 = 323059) B323059
theorem B430859 : Blo 283827 430859 := bstep (se 1 (by rfl) ⟨323144, by rfl⟩ : syracuseStep 430859 = 646289) B646289
theorem B430871 : Blo 283827 430871 := bstep (se 1 (by rfl) ⟨323153, by rfl⟩ : syracuseStep 430871 = 646307) B646307
theorem B430937 : Blo 283827 430937 := bstep (se 2 (by rfl) ⟨161601, by rfl⟩ : syracuseStep 430937 = 323203) B323203
theorem B431051 : Blo 283827 431051 := bstep (se 1 (by rfl) ⟨323288, by rfl⟩ : syracuseStep 431051 = 646577) B646577
theorem B431063 : Blo 283827 431063 := bstep (se 1 (by rfl) ⟨323297, by rfl⟩ : syracuseStep 431063 = 646595) B646595
theorem B431129 : Blo 283827 431129 := bstep (se 2 (by rfl) ⟨161673, by rfl⟩ : syracuseStep 431129 = 323347) B323347
theorem B1840259 : Blo 283827 1840259 := bstep (se 1 (by rfl) ⟨1380194, by rfl⟩ : syracuseStep 1840259 = 2760389) B2760389
theorem B431243 : Blo 283827 431243 := bstep (se 1 (by rfl) ⟨323432, by rfl⟩ : syracuseStep 431243 = 646865) B646865
theorem B431255 : Blo 283827 431255 := bstep (se 1 (by rfl) ⟨323441, by rfl⟩ : syracuseStep 431255 = 646883) B646883
theorem B431321 : Blo 283827 431321 := bstep (se 2 (by rfl) ⟨161745, by rfl⟩ : syracuseStep 431321 = 323491) B323491
theorem B726347 : Blo 283827 726347 := bstep (se 1 (by rfl) ⟨544760, by rfl⟩ : syracuseStep 726347 = 1089521) B1089521
theorem B431435 : Blo 283827 431435 := bstep (se 1 (by rfl) ⟨323576, by rfl⟩ : syracuseStep 431435 = 647153) B647153
theorem B431447 : Blo 283827 431447 := bstep (se 1 (by rfl) ⟨323585, by rfl⟩ : syracuseStep 431447 = 647171) B647171
theorem B693593 : Blo 283827 693593 := bstep (se 2 (by rfl) ⟨260097, by rfl⟩ : syracuseStep 693593 = 520195) B520195
theorem B4855139 : Blo 283827 4855139 := bstep (se 1 (by rfl) ⟨3641354, by rfl⟩ : syracuseStep 4855139 = 7282709) B7282709
theorem B431513 : Blo 283827 431513 := bstep (se 2 (by rfl) ⟨161817, by rfl⟩ : syracuseStep 431513 = 323635) B323635
theorem B431627 : Blo 283827 431627 := bstep (se 1 (by rfl) ⟨323720, by rfl⟩ : syracuseStep 431627 = 647441) B647441
theorem B431639 : Blo 283827 431639 := bstep (se 1 (by rfl) ⟨323729, by rfl⟩ : syracuseStep 431639 = 647459) B647459
theorem B1447469 : Blo 283827 1447469 := bstep (se 3 (by rfl) ⟨271400, by rfl⟩ : syracuseStep 1447469 = 542801) B542801
theorem B464459 : Blo 283827 464459 := bstep (se 1 (by rfl) ⟨348344, by rfl⟩ : syracuseStep 464459 = 696689) B696689
theorem B431705 : Blo 283827 431705 := bstep (se 2 (by rfl) ⟨161889, by rfl⟩ : syracuseStep 431705 = 323779) B323779
theorem B1087121 : Blo 283827 1087121 := bstep (se 2 (by rfl) ⟨407670, by rfl⟩ : syracuseStep 1087121 = 815341) B815341
theorem B1087577 : Blo 283827 1087577 := bstep (se 2 (by rfl) ⟨407841, by rfl⟩ : syracuseStep 1087577 = 815683) B815683
theorem B1382579 : Blo 283827 1382579 := bstep (se 1 (by rfl) ⟨1036934, by rfl⟩ : syracuseStep 1382579 = 2073869) B2073869
theorem B825547 : Blo 283827 825547 := bstep (se 1 (by rfl) ⟨619160, by rfl⟩ : syracuseStep 825547 = 1238321) B1238321
theorem B727319 : Blo 283827 727319 := bstep (se 1 (by rfl) ⟨545489, by rfl⟩ : syracuseStep 727319 = 1090979) B1090979
theorem B1087789 : Blo 283827 1087789 := bstep (se 3 (by rfl) ⟨203960, by rfl⟩ : syracuseStep 1087789 = 407921) B407921
theorem B1088093 : Blo 283827 1088093 := bstep (se 3 (by rfl) ⟨204017, by rfl⟩ : syracuseStep 1088093 = 408035) B408035
theorem B4135859 : Blo 283827 4135859 := bstep (se 1 (by rfl) ⟨3101894, by rfl⟩ : syracuseStep 4135859 = 6203789) B6203789
theorem B727987 : Blo 283827 727987 := bstep (se 1 (by rfl) ⟨545990, by rfl⟩ : syracuseStep 727987 = 1091981) B1091981
theorem B728129 : Blo 283827 728129 := bstep (se 2 (by rfl) ⟨273048, by rfl⟩ : syracuseStep 728129 = 546097) B546097
theorem B1121539 : Blo 283827 1121539 := bstep (se 1 (by rfl) ⟨841154, by rfl⟩ : syracuseStep 1121539 = 1682309) B1682309
theorem B2072081 : Blo 283827 2072081 := bstep (se 2 (by rfl) ⟨777030, by rfl⟩ : syracuseStep 2072081 = 1554061) B1554061
theorem B5250577 : Blo 283827 5250577 := bstep (se 2 (by rfl) ⟨1968966, by rfl⟩ : syracuseStep 5250577 = 3937933) B3937933
theorem B433687 : Blo 283827 433687 := bstep (se 1 (by rfl) ⟨325265, by rfl⟩ : syracuseStep 433687 = 650531) B650531
theorem B958283 : Blo 283827 958283 := bstep (se 1 (by rfl) ⟨718712, by rfl⟩ : syracuseStep 958283 = 1437425) B1437425
theorem B1220483 : Blo 283827 1220483 := bstep (se 1 (by rfl) ⟨915362, by rfl⟩ : syracuseStep 1220483 = 1830725) B1830725
theorem B1023961 : Blo 283827 1023961 := bstep (se 2 (by rfl) ⟨383985, by rfl⟩ : syracuseStep 1023961 = 767971) B767971
theorem B4464715 : Blo 283827 4464715 := bstep (se 1 (by rfl) ⟨3348536, by rfl⟩ : syracuseStep 4464715 = 6697073) B6697073
theorem B958553 : Blo 283827 958553 := bstep (se 2 (by rfl) ⟨359457, by rfl⟩ : syracuseStep 958553 = 718915) B718915
theorem B1220825 : Blo 283827 1220825 := bstep (se 2 (by rfl) ⟨457809, by rfl⟩ : syracuseStep 1220825 = 915619) B915619
theorem B729751 : Blo 283827 729751 := bstep (se 1 (by rfl) ⟨547313, by rfl⟩ : syracuseStep 729751 = 1094627) B1094627
theorem B959255 : Blo 283827 959255 := bstep (se 1 (by rfl) ⟨719441, by rfl⟩ : syracuseStep 959255 = 1438883) B1438883
theorem B303959 : Blo 283827 303959 := bstep (se 1 (by rfl) ⟨227969, by rfl⟩ : syracuseStep 303959 = 455939) B455939
theorem B2597849 : Blo 283827 2597849 := bstep (se 2 (by rfl) ⟨974193, by rfl⟩ : syracuseStep 2597849 = 1948387) B1948387
theorem B1090691 : Blo 283827 1090691 := bstep (se 1 (by rfl) ⟨818018, by rfl⟩ : syracuseStep 1090691 = 1636037) B1636037
theorem B1090705 : Blo 283827 1090705 := bstep (se 2 (by rfl) ⟨409014, by rfl⟩ : syracuseStep 1090705 = 818029) B818029
theorem B959795 : Blo 283827 959795 := bstep (se 1 (by rfl) ⟨719846, by rfl⟩ : syracuseStep 959795 = 1439693) B1439693
theorem B1451357 : Blo 283827 1451357 := bstep (se 3 (by rfl) ⟨272129, by rfl⟩ : syracuseStep 1451357 = 544259) B544259
theorem B1091009 : Blo 283827 1091009 := bstep (se 2 (by rfl) ⟨409128, by rfl⟩ : syracuseStep 1091009 = 818257) B818257
theorem B304651 : Blo 283827 304651 := bstep (se 1 (by rfl) ⟨228488, by rfl⟩ : syracuseStep 304651 = 456977) B456977
theorem B960065 : Blo 283827 960065 := bstep (se 2 (by rfl) ⟨360024, by rfl⟩ : syracuseStep 960065 = 720049) B720049
theorem B1222465 : Blo 283827 1222465 := bstep (se 2 (by rfl) ⟨458424, by rfl⟩ : syracuseStep 1222465 = 916849) B916849
theorem B2435021 : Blo 283827 2435021 := bstep (se 3 (by rfl) ⟨456566, by rfl⟩ : syracuseStep 2435021 = 913133) B913133
theorem B1746905 : Blo 283827 1746905 := bstep (se 2 (by rfl) ⟨655089, by rfl⟩ : syracuseStep 1746905 = 1310179) B1310179
theorem B960605 : Blo 283827 960605 := bstep (se 3 (by rfl) ⟨180113, by rfl⟩ : syracuseStep 960605 = 360227) B360227
theorem B1091677 : Blo 283827 1091677 := bstep (se 3 (by rfl) ⟨204689, by rfl⟩ : syracuseStep 1091677 = 409379) B409379
theorem B305527 : Blo 283827 305527 := bstep (se 1 (by rfl) ⟨229145, by rfl⟩ : syracuseStep 305527 = 458291) B458291
theorem B2960003 : Blo 283827 2960003 := bstep (se 1 (by rfl) ⟨2220002, by rfl⟩ : syracuseStep 2960003 = 4440005) B4440005
theorem B404185 : Blo 283827 404185 := bstep (se 2 (by rfl) ⟨151569, by rfl⟩ : syracuseStep 404185 = 303139) B303139
theorem B305975 : Blo 283827 305975 := bstep (se 1 (by rfl) ⟨229481, by rfl⟩ : syracuseStep 305975 = 458963) B458963
theorem B404299 : Blo 283827 404299 := bstep (se 1 (by rfl) ⟨303224, by rfl⟩ : syracuseStep 404299 = 606449) B606449
theorem B306347 : Blo 283827 306347 := bstep (se 1 (by rfl) ⟨229760, by rfl⟩ : syracuseStep 306347 = 459521) B459521
theorem B961739 : Blo 283827 961739 := bstep (se 1 (by rfl) ⟨721304, by rfl⟩ : syracuseStep 961739 = 1442609) B1442609
theorem B863435 : Blo 283827 863435 := bstep (se 1 (by rfl) ⟨647576, by rfl⟩ : syracuseStep 863435 = 1295153) B1295153
theorem B1453463 : Blo 283827 1453463 := bstep (se 1 (by rfl) ⟨1090097, by rfl⟩ : syracuseStep 1453463 = 2180195) B2180195
theorem B2731481 : Blo 283827 2731481 := bstep (se 2 (by rfl) ⟨1024305, by rfl⟩ : syracuseStep 2731481 = 2048611) B2048611
theorem B962009 : Blo 283827 962009 := bstep (se 2 (by rfl) ⟨360753, by rfl⟩ : syracuseStep 962009 = 721507) B721507
theorem B3518309 : Blo 283827 3518309 := bstep (se 4 (by rfl) ⟨329841, by rfl⟩ : syracuseStep 3518309 = 659683) B659683
theorem B1552459 : Blo 283827 1552459 := bstep (se 1 (by rfl) ⟨1164344, by rfl⟩ : syracuseStep 1552459 = 2328689) B2328689
theorem B1028227 : Blo 283827 1028227 := bstep (se 1 (by rfl) ⟨771170, by rfl⟩ : syracuseStep 1028227 = 1542341) B1542341
theorem B405643 : Blo 283827 405643 := bstep (se 1 (by rfl) ⟨304232, by rfl⟩ : syracuseStep 405643 = 608465) B608465
theorem B962711 : Blo 283827 962711 := bstep (se 1 (by rfl) ⟨722033, by rfl⟩ : syracuseStep 962711 = 1444067) B1444067
theorem B307351 : Blo 283827 307351 := bstep (se 1 (by rfl) ⟨230513, by rfl⟩ : syracuseStep 307351 = 461027) B461027
theorem B2437411 : Blo 283827 2437411 := bstep (se 1 (by rfl) ⟨1828058, by rfl⟩ : syracuseStep 2437411 = 3656117) B3656117
theorem B4108643 : Blo 283827 4108643 := bstep (se 1 (by rfl) ⟨3081482, by rfl⟩ : syracuseStep 4108643 = 6162965) B6162965
theorem B405911 : Blo 283827 405911 := bstep (se 1 (by rfl) ⟨304433, by rfl⟩ : syracuseStep 405911 = 608867) B608867
theorem B3551779 : Blo 283827 3551779 := bstep (se 1 (by rfl) ⟨2663834, by rfl⟩ : syracuseStep 3551779 = 5327669) B5327669
theorem B963251 : Blo 283827 963251 := bstep (se 1 (by rfl) ⟨722438, by rfl⟩ : syracuseStep 963251 = 1444877) B1444877
theorem B963521 : Blo 283827 963521 := bstep (se 2 (by rfl) ⟨361320, by rfl⟩ : syracuseStep 963521 = 722641) B722641
theorem B4174865 : Blo 283827 4174865 := bstep (se 2 (by rfl) ⟨1565574, by rfl⟩ : syracuseStep 4174865 = 3131149) B3131149
theorem B472153 : Blo 283827 472153 := bstep (se 2 (by rfl) ⟨177057, by rfl⟩ : syracuseStep 472153 = 354115) B354115
theorem B406873 : Blo 283827 406873 := bstep (se 2 (by rfl) ⟨152577, by rfl⟩ : syracuseStep 406873 = 305155) B305155
theorem B3650993 : Blo 283827 3650993 := bstep (se 2 (by rfl) ⟨1369122, by rfl⟩ : syracuseStep 3650993 = 2738245) B2738245
theorem B1553843 : Blo 283827 1553843 := bstep (se 1 (by rfl) ⟨1165382, by rfl⟩ : syracuseStep 1553843 = 2330765) B2330765
theorem B964061 : Blo 283827 964061 := bstep (se 3 (by rfl) ⟨180761, by rfl⟩ : syracuseStep 964061 = 361523) B361523
theorem B1619473 : Blo 283827 1619473 := bstep (se 2 (by rfl) ⟨607302, by rfl⟩ : syracuseStep 1619473 = 1214605) B1214605
theorem B734999 : Blo 283827 734999 := bstep (se 1 (by rfl) ⟨551249, by rfl⟩ : syracuseStep 734999 = 1102499) B1102499
theorem B2471755 : Blo 283827 2471755 := bstep (se 1 (by rfl) ⟨1853816, by rfl⟩ : syracuseStep 2471755 = 3707633) B3707633
theorem B15677509 : Blo 283827 15677509 := bstep (se 4 (by rfl) ⟨1469766, by rfl⟩ : syracuseStep 15677509 = 2939533) B2939533
theorem B3258629 : Blo 283827 3258629 := bstep (se 4 (by rfl) ⟨305496, by rfl⟩ : syracuseStep 3258629 = 610993) B610993
theorem B538967 : Blo 283827 538967 := bstep (se 1 (by rfl) ⟨404225, by rfl⟩ : syracuseStep 538967 = 808451) B808451
theorem B932417 : Blo 283827 932417 := bstep (se 2 (by rfl) ⟨349656, by rfl⟩ : syracuseStep 932417 = 699313) B699313
theorem B965195 : Blo 283827 965195 := bstep (se 1 (by rfl) ⟨723896, by rfl⟩ : syracuseStep 965195 = 1447793) B1447793
theorem B408331 : Blo 283827 408331 := bstep (se 1 (by rfl) ⟨306248, by rfl⟩ : syracuseStep 408331 = 612497) B612497
theorem B408343 : Blo 283827 408343 := bstep (se 1 (by rfl) ⟨306257, by rfl⟩ : syracuseStep 408343 = 612515) B612515
theorem B965465 : Blo 283827 965465 := bstep (se 2 (by rfl) ⟨362049, by rfl⟩ : syracuseStep 965465 = 724099) B724099
theorem B1457027 : Blo 283827 1457027 := bstep (se 1 (by rfl) ⟨1092770, by rfl⟩ : syracuseStep 1457027 = 2185541) B2185541
theorem B3685337 : Blo 283827 3685337 := bstep (se 2 (by rfl) ⟨1382001, by rfl⟩ : syracuseStep 3685337 = 2764003) B2764003
theorem B539635 : Blo 283827 539635 := bstep (se 1 (by rfl) ⟨404726, by rfl⟩ : syracuseStep 539635 = 809453) B809453
theorem B540083 : Blo 283827 540083 := bstep (se 1 (by rfl) ⟨405062, by rfl⟩ : syracuseStep 540083 = 810125) B810125
theorem B540121 : Blo 283827 540121 := bstep (se 2 (by rfl) ⟨202545, by rfl⟩ : syracuseStep 540121 = 405091) B405091
theorem B966167 : Blo 283827 966167 := bstep (se 1 (by rfl) ⟨724625, by rfl⟩ : syracuseStep 966167 = 1449251) B1449251
theorem B2178737 : Blo 283827 2178737 := bstep (se 2 (by rfl) ⟨817026, by rfl⟩ : syracuseStep 2178737 = 1634053) B1634053
theorem B638657 : Blo 283827 638657 := bstep (se 2 (by rfl) ⟨239496, by rfl⟩ : syracuseStep 638657 = 478993) B478993
theorem B933569 : Blo 283827 933569 := bstep (se 2 (by rfl) ⟨350088, by rfl⟩ : syracuseStep 933569 = 700177) B700177
theorem B3096269 : Blo 283827 3096269 := bstep (se 3 (by rfl) ⟨580550, by rfl⟩ : syracuseStep 3096269 = 1161101) B1161101
theorem B1228547 : Blo 283827 1228547 := bstep (se 1 (by rfl) ⟨921410, by rfl⟩ : syracuseStep 1228547 = 1842821) B1842821
theorem B638873 : Blo 283827 638873 := bstep (se 2 (by rfl) ⟨239577, by rfl⟩ : syracuseStep 638873 = 479155) B479155
theorem B540569 : Blo 283827 540569 := bstep (se 2 (by rfl) ⟨202713, by rfl⟩ : syracuseStep 540569 = 405427) B405427
theorem B638963 : Blo 283827 638963 := bstep (se 1 (by rfl) ⟨479222, by rfl⟩ : syracuseStep 638963 = 958445) B958445
theorem B606209 : Blo 283827 606209 := bstep (se 2 (by rfl) ⟨227328, by rfl⟩ : syracuseStep 606209 = 454657) B454657
theorem B638999 : Blo 283827 638999 := bstep (se 1 (by rfl) ⟨479249, by rfl⟩ : syracuseStep 638999 = 958499) B958499
theorem B966707 : Blo 283827 966707 := bstep (se 1 (by rfl) ⟨725030, by rfl⟩ : syracuseStep 966707 = 1450061) B1450061
theorem B606295 : Blo 283827 606295 := bstep (se 1 (by rfl) ⟨454721, by rfl⟩ : syracuseStep 606295 = 909443) B909443
theorem B2179223 : Blo 283827 2179223 := bstep (se 1 (by rfl) ⟨1634417, by rfl⟩ : syracuseStep 2179223 = 3268835) B3268835
theorem B639179 : Blo 283827 639179 := bstep (se 1 (by rfl) ⟨479384, by rfl⟩ : syracuseStep 639179 = 958769) B958769
theorem B639233 : Blo 283827 639233 := bstep (se 2 (by rfl) ⟨239712, by rfl⟩ : syracuseStep 639233 = 479425) B479425
theorem B3916097 : Blo 283827 3916097 := bstep (se 2 (by rfl) ⟨1468536, by rfl⟩ : syracuseStep 3916097 = 2937073) B2937073
theorem B966977 : Blo 283827 966977 := bstep (se 2 (by rfl) ⟨362616, by rfl⟩ : syracuseStep 966977 = 725233) B725233
theorem B639449 : Blo 283827 639449 := bstep (se 2 (by rfl) ⟨239793, by rfl⟩ : syracuseStep 639449 = 479587) B479587
theorem B1229363 : Blo 283827 1229363 := bstep (se 1 (by rfl) ⟨922022, by rfl⟩ : syracuseStep 1229363 = 1844045) B1844045
theorem B639539 : Blo 283827 639539 := bstep (se 1 (by rfl) ⟨479654, by rfl⟩ : syracuseStep 639539 = 959309) B959309
theorem B639575 : Blo 283827 639575 := bstep (se 1 (by rfl) ⟨479681, by rfl⟩ : syracuseStep 639575 = 959363) B959363
theorem B541313 : Blo 283827 541313 := bstep (se 2 (by rfl) ⟨202992, by rfl⟩ : syracuseStep 541313 = 405985) B405985
theorem B639755 : Blo 283827 639755 := bstep (se 1 (by rfl) ⟨479816, by rfl⟩ : syracuseStep 639755 = 959633) B959633
theorem B13812545 : Blo 283827 13812545 := bstep (se 2 (by rfl) ⟨5179704, by rfl⟩ : syracuseStep 13812545 = 10359409) B10359409
theorem B639809 : Blo 283827 639809 := bstep (se 2 (by rfl) ⟨239928, by rfl⟩ : syracuseStep 639809 = 479857) B479857
theorem B2442059 : Blo 283827 2442059 := bstep (se 1 (by rfl) ⟨1831544, by rfl⟩ : syracuseStep 2442059 = 3663089) B3663089
theorem B967517 : Blo 283827 967517 := bstep (se 3 (by rfl) ⟨181409, by rfl⟩ : syracuseStep 967517 = 362819) B362819
theorem B1622915 : Blo 283827 1622915 := bstep (se 1 (by rfl) ⟨1217186, by rfl⟩ : syracuseStep 1622915 = 2434373) B2434373
theorem B607115 : Blo 283827 607115 := bstep (se 1 (by rfl) ⟨455336, by rfl⟩ : syracuseStep 607115 = 910673) B910673
theorem B541579 : Blo 283827 541579 := bstep (se 1 (by rfl) ⟨406184, by rfl⟩ : syracuseStep 541579 = 812369) B812369
theorem B640025 : Blo 283827 640025 := bstep (se 2 (by rfl) ⟨240009, by rfl⟩ : syracuseStep 640025 = 480019) B480019
theorem B640115 : Blo 283827 640115 := bstep (se 1 (by rfl) ⟨480086, by rfl⟩ : syracuseStep 640115 = 960173) B960173
theorem B640151 : Blo 283827 640151 := bstep (se 1 (by rfl) ⟨480113, by rfl⟩ : syracuseStep 640151 = 960227) B960227
theorem B640331 : Blo 283827 640331 := bstep (se 1 (by rfl) ⟨480248, by rfl⟩ : syracuseStep 640331 = 960497) B960497
theorem B542027 : Blo 283827 542027 := bstep (se 1 (by rfl) ⟨406520, by rfl⟩ : syracuseStep 542027 = 813041) B813041
theorem B640385 : Blo 283827 640385 := bstep (se 2 (by rfl) ⟨240144, by rfl⟩ : syracuseStep 640385 = 480289) B480289
theorem B542209 : Blo 283827 542209 := bstep (se 2 (by rfl) ⟨203328, by rfl⟩ : syracuseStep 542209 = 406657) B406657
theorem B1295875 : Blo 283827 1295875 := bstep (se 1 (by rfl) ⟨971906, by rfl⟩ : syracuseStep 1295875 = 1943813) B1943813
theorem B706099 : Blo 283827 706099 := bstep (se 1 (by rfl) ⟨529574, by rfl⟩ : syracuseStep 706099 = 1059149) B1059149
theorem B640601 : Blo 283827 640601 := bstep (se 2 (by rfl) ⟨240225, by rfl⟩ : syracuseStep 640601 = 480451) B480451
theorem B640691 : Blo 283827 640691 := bstep (se 1 (by rfl) ⟨480518, by rfl⟩ : syracuseStep 640691 = 961037) B961037
theorem B640727 : Blo 283827 640727 := bstep (se 1 (by rfl) ⟨480545, by rfl⟩ : syracuseStep 640727 = 961091) B961091
theorem B771905 : Blo 283827 771905 := bstep (se 2 (by rfl) ⟨289464, by rfl⟩ : syracuseStep 771905 = 578929) B578929
theorem B542551 : Blo 283827 542551 := bstep (se 1 (by rfl) ⟨406913, by rfl⟩ : syracuseStep 542551 = 813827) B813827
theorem B608089 : Blo 283827 608089 := bstep (se 2 (by rfl) ⟨228033, by rfl⟩ : syracuseStep 608089 = 456067) B456067
theorem B640907 : Blo 283827 640907 := bstep (se 1 (by rfl) ⟨480680, by rfl⟩ : syracuseStep 640907 = 961361) B961361
theorem B640961 : Blo 283827 640961 := bstep (se 2 (by rfl) ⟨240360, by rfl⟩ : syracuseStep 640961 = 480721) B480721
theorem B968651 : Blo 283827 968651 := bstep (se 1 (by rfl) ⟨726488, by rfl⟩ : syracuseStep 968651 = 1452977) B1452977
theorem B4376537 : Blo 283827 4376537 := bstep (se 2 (by rfl) ⟨1641201, by rfl⟩ : syracuseStep 4376537 = 3282403) B3282403
theorem B542771 : Blo 283827 542771 := bstep (se 1 (by rfl) ⟨407078, by rfl⟩ : syracuseStep 542771 = 814157) B814157
theorem B7850135 : Blo 283827 7850135 := bstep (se 1 (by rfl) ⟨5887601, by rfl⟩ : syracuseStep 7850135 = 11775203) B11775203
theorem B641177 : Blo 283827 641177 := bstep (se 2 (by rfl) ⟨240441, by rfl⟩ : syracuseStep 641177 = 480883) B480883
theorem B1099955 : Blo 283827 1099955 := bstep (se 1 (by rfl) ⟨824966, by rfl⟩ : syracuseStep 1099955 = 1649933) B1649933
theorem B4114637 : Blo 283827 4114637 := bstep (se 3 (by rfl) ⟨771494, by rfl⟩ : syracuseStep 4114637 = 1542989) B1542989
theorem B968921 : Blo 283827 968921 := bstep (se 2 (by rfl) ⟨363345, by rfl⟩ : syracuseStep 968921 = 726691) B726691
theorem B641267 : Blo 283827 641267 := bstep (se 1 (by rfl) ⟨480950, by rfl⟩ : syracuseStep 641267 = 961901) B961901
theorem B641303 : Blo 283827 641303 := bstep (se 1 (by rfl) ⟨480977, by rfl⟩ : syracuseStep 641303 = 961955) B961955
theorem B542999 : Blo 283827 542999 := bstep (se 1 (by rfl) ⟨407249, by rfl⟩ : syracuseStep 542999 = 814499) B814499
theorem B2312599 : Blo 283827 2312599 := bstep (se 1 (by rfl) ⟨1734449, by rfl⟩ : syracuseStep 2312599 = 3468899) B3468899
theorem B641483 : Blo 283827 641483 := bstep (se 1 (by rfl) ⟨481112, by rfl⟩ : syracuseStep 641483 = 962225) B962225
theorem B641537 : Blo 283827 641537 := bstep (se 2 (by rfl) ⟨240576, by rfl⟩ : syracuseStep 641537 = 481153) B481153
theorem B576011 : Blo 283827 576011 := bstep (se 1 (by rfl) ⟨432008, by rfl⟩ : syracuseStep 576011 = 864017) B864017
theorem B543257 : Blo 283827 543257 := bstep (se 2 (by rfl) ⟨203721, by rfl⟩ : syracuseStep 543257 = 407443) B407443
theorem B641753 : Blo 283827 641753 := bstep (se 2 (by rfl) ⟨240657, by rfl⟩ : syracuseStep 641753 = 481315) B481315
theorem B641843 : Blo 283827 641843 := bstep (se 1 (by rfl) ⟨481382, by rfl⟩ : syracuseStep 641843 = 962765) B962765
theorem B641879 : Blo 283827 641879 := bstep (se 1 (by rfl) ⟨481409, by rfl⟩ : syracuseStep 641879 = 962819) B962819
theorem B969623 : Blo 283827 969623 := bstep (se 1 (by rfl) ⟨727217, by rfl⟩ : syracuseStep 969623 = 1454435) B1454435
theorem B543667 : Blo 283827 543667 := bstep (se 1 (by rfl) ⟨407750, by rfl⟩ : syracuseStep 543667 = 815501) B815501
theorem B642059 : Blo 283827 642059 := bstep (se 1 (by rfl) ⟨481544, by rfl⟩ : syracuseStep 642059 = 963089) B963089
theorem B642113 : Blo 283827 642113 := bstep (se 2 (by rfl) ⟨240792, by rfl⟩ : syracuseStep 642113 = 481585) B481585
theorem B1625305 : Blo 283827 1625305 := bstep (se 2 (by rfl) ⟨609489, by rfl⟩ : syracuseStep 1625305 = 1218979) B1218979
theorem B642329 : Blo 283827 642329 := bstep (se 2 (by rfl) ⟨240873, by rfl⟩ : syracuseStep 642329 = 481747) B481747
theorem B642419 : Blo 283827 642419 := bstep (se 1 (by rfl) ⟨481814, by rfl⟩ : syracuseStep 642419 = 963629) B963629
theorem B642455 : Blo 283827 642455 := bstep (se 1 (by rfl) ⟨481841, by rfl⟩ : syracuseStep 642455 = 963683) B963683
theorem B544153 : Blo 283827 544153 := bstep (se 2 (by rfl) ⟨204057, by rfl⟩ : syracuseStep 544153 = 408115) B408115
theorem B4148657 : Blo 283827 4148657 := bstep (se 2 (by rfl) ⟨1555746, by rfl⟩ : syracuseStep 4148657 = 3111493) B3111493
theorem B970163 : Blo 283827 970163 := bstep (se 1 (by rfl) ⟨727622, by rfl⟩ : syracuseStep 970163 = 1455245) B1455245
theorem B576983 : Blo 283827 576983 := bstep (se 1 (by rfl) ⟨432737, by rfl⟩ : syracuseStep 576983 = 865475) B865475
theorem B642635 : Blo 283827 642635 := bstep (se 1 (by rfl) ⟨481976, by rfl⟩ : syracuseStep 642635 = 963953) B963953
theorem B642689 : Blo 283827 642689 := bstep (se 2 (by rfl) ⟨241008, by rfl⟩ : syracuseStep 642689 = 482017) B482017
theorem B1232563 : Blo 283827 1232563 := bstep (se 1 (by rfl) ⟨924422, by rfl⟩ : syracuseStep 1232563 = 1848845) B1848845
theorem B970433 : Blo 283827 970433 := bstep (se 2 (by rfl) ⟨363912, by rfl⟩ : syracuseStep 970433 = 727825) B727825
theorem B642905 : Blo 283827 642905 := bstep (se 2 (by rfl) ⟨241089, by rfl⟩ : syracuseStep 642905 = 482179) B482179
theorem B642995 : Blo 283827 642995 := bstep (se 1 (by rfl) ⟨482246, by rfl⟩ : syracuseStep 642995 = 964493) B964493
theorem B544715 : Blo 283827 544715 := bstep (se 1 (by rfl) ⟨408536, by rfl⟩ : syracuseStep 544715 = 817073) B817073
theorem B643031 : Blo 283827 643031 := bstep (se 1 (by rfl) ⟨482273, by rfl⟩ : syracuseStep 643031 = 964547) B964547
theorem B479243 : Blo 283827 479243 := bstep (se 1 (by rfl) ⟨359432, by rfl⟩ : syracuseStep 479243 = 718865) B718865
theorem B544897 : Blo 283827 544897 := bstep (se 2 (by rfl) ⟨204336, by rfl⟩ : syracuseStep 544897 = 408673) B408673
theorem B479371 : Blo 283827 479371 := bstep (se 1 (by rfl) ⟨359528, by rfl⟩ : syracuseStep 479371 = 719057) B719057
theorem B643211 : Blo 283827 643211 := bstep (se 1 (by rfl) ⟨482408, by rfl⟩ : syracuseStep 643211 = 964817) B964817
theorem B1626263 : Blo 283827 1626263 := bstep (se 1 (by rfl) ⟨1219697, by rfl⟩ : syracuseStep 1626263 = 2439395) B2439395
theorem B643265 : Blo 283827 643265 := bstep (se 2 (by rfl) ⟨241224, by rfl⟩ : syracuseStep 643265 = 482449) B482449
theorem B610507 : Blo 283827 610507 := bstep (se 1 (by rfl) ⟨457880, by rfl⟩ : syracuseStep 610507 = 915761) B915761
theorem B970973 : Blo 283827 970973 := bstep (se 3 (by rfl) ⟨182057, by rfl⟩ : syracuseStep 970973 = 364115) B364115
theorem B610583 : Blo 283827 610583 := bstep (se 1 (by rfl) ⟨457937, by rfl⟩ : syracuseStep 610583 = 915875) B915875
theorem B479513 : Blo 283827 479513 := bstep (se 2 (by rfl) ⟨179817, by rfl⟩ : syracuseStep 479513 = 359635) B359635
theorem B479641 : Blo 283827 479641 := bstep (se 2 (by rfl) ⟨179865, by rfl⟩ : syracuseStep 479641 = 359731) B359731
theorem B643481 : Blo 283827 643481 := bstep (se 2 (by rfl) ⟨241305, by rfl⟩ : syracuseStep 643481 = 482611) B482611
theorem B643571 : Blo 283827 643571 := bstep (se 1 (by rfl) ⟨482678, by rfl⟩ : syracuseStep 643571 = 965357) B965357
theorem B643607 : Blo 283827 643607 := bstep (se 1 (by rfl) ⟨482705, by rfl⟩ : syracuseStep 643607 = 965411) B965411
theorem B643787 : Blo 283827 643787 := bstep (se 1 (by rfl) ⟨482840, by rfl⟩ : syracuseStep 643787 = 965681) B965681
theorem B643841 : Blo 283827 643841 := bstep (se 2 (by rfl) ⟨241440, by rfl⟩ : syracuseStep 643841 = 482881) B482881
theorem B545611 : Blo 283827 545611 := bstep (se 1 (by rfl) ⟨409208, by rfl⟩ : syracuseStep 545611 = 818417) B818417
theorem B4739957 : Blo 283827 4739957 := bstep (se 5 (by rfl) ⟨222185, by rfl⟩ : syracuseStep 4739957 = 444371) B444371
theorem B545687 : Blo 283827 545687 := bstep (se 1 (by rfl) ⟨409265, by rfl⟩ : syracuseStep 545687 = 818531) B818531
theorem B480215 : Blo 283827 480215 := bstep (se 1 (by rfl) ⟨360161, by rfl⟩ : syracuseStep 480215 = 720323) B720323
theorem B512983 : Blo 283827 512983 := bstep (se 1 (by rfl) ⟨384737, by rfl⟩ : syracuseStep 512983 = 769475) B769475
theorem B644057 : Blo 283827 644057 := bstep (se 2 (by rfl) ⟨241521, by rfl⟩ : syracuseStep 644057 = 483043) B483043
theorem B513047 : Blo 283827 513047 := bstep (se 1 (by rfl) ⟨384785, by rfl⟩ : syracuseStep 513047 = 769571) B769571
theorem B644147 : Blo 283827 644147 := bstep (se 1 (by rfl) ⟨483110, by rfl⟩ : syracuseStep 644147 = 966221) B966221
theorem B480343 : Blo 283827 480343 := bstep (se 1 (by rfl) ⟨360257, by rfl⟩ : syracuseStep 480343 = 720515) B720515
theorem B644183 : Blo 283827 644183 := bstep (se 1 (by rfl) ⟨483137, by rfl⟩ : syracuseStep 644183 = 966275) B966275
theorem B283831 : Blo 283827 283831 := bstep (se 1 (by rfl) ⟨212873, by rfl⟩ : syracuseStep 283831 = 425747) B425747
theorem B283851 : Blo 283827 283851 := bstep (se 1 (by rfl) ⟨212888, by rfl⟩ : syracuseStep 283851 = 425777) B425777
theorem B283863 : Blo 283827 283863 := bstep (se 1 (by rfl) ⟨212897, by rfl⟩ : syracuseStep 283863 = 425795) B425795
theorem B283883 : Blo 283827 283883 := bstep (se 1 (by rfl) ⟨212912, by rfl⟩ : syracuseStep 283883 = 425825) B425825
theorem B283895 : Blo 283827 283895 := bstep (se 1 (by rfl) ⟨212921, by rfl⟩ : syracuseStep 283895 = 425843) B425843
theorem B283915 : Blo 283827 283915 := bstep (se 1 (by rfl) ⟨212936, by rfl⟩ : syracuseStep 283915 = 425873) B425873
theorem B644363 : Blo 283827 644363 := bstep (se 1 (by rfl) ⟨483272, by rfl⟩ : syracuseStep 644363 = 966545) B966545
theorem B283927 : Blo 283827 283927 := bstep (se 1 (by rfl) ⟨212945, by rfl⟩ : syracuseStep 283927 = 425891) B425891
theorem B283947 : Blo 283827 283947 := bstep (se 1 (by rfl) ⟨212960, by rfl⟩ : syracuseStep 283947 = 425921) B425921
theorem B283959 : Blo 283827 283959 := bstep (se 1 (by rfl) ⟨212969, by rfl⟩ : syracuseStep 283959 = 425939) B425939
theorem B644417 : Blo 283827 644417 := bstep (se 2 (by rfl) ⟨241656, by rfl⟩ : syracuseStep 644417 = 483313) B483313
theorem B283979 : Blo 283827 283979 := bstep (se 1 (by rfl) ⟨212984, by rfl⟩ : syracuseStep 283979 = 425969) B425969
theorem B283991 : Blo 283827 283991 := bstep (se 1 (by rfl) ⟨212993, by rfl⟩ : syracuseStep 283991 = 425987) B425987
theorem B284011 : Blo 283827 284011 := bstep (se 1 (by rfl) ⟨213008, by rfl⟩ : syracuseStep 284011 = 426017) B426017
theorem B284023 : Blo 283827 284023 := bstep (se 1 (by rfl) ⟨213017, by rfl⟩ : syracuseStep 284023 = 426035) B426035
theorem B284043 : Blo 283827 284043 := bstep (se 1 (by rfl) ⟨213032, by rfl⟩ : syracuseStep 284043 = 426065) B426065
theorem B284055 : Blo 283827 284055 := bstep (se 1 (by rfl) ⟨213041, by rfl⟩ : syracuseStep 284055 = 426083) B426083
theorem B284075 : Blo 283827 284075 := bstep (se 1 (by rfl) ⟨213056, by rfl⟩ : syracuseStep 284075 = 426113) B426113
theorem B284087 : Blo 283827 284087 := bstep (se 1 (by rfl) ⟨213065, by rfl⟩ : syracuseStep 284087 = 426131) B426131
theorem B284107 : Blo 283827 284107 := bstep (se 1 (by rfl) ⟨213080, by rfl⟩ : syracuseStep 284107 = 426161) B426161
theorem B284119 : Blo 283827 284119 := bstep (se 1 (by rfl) ⟨213089, by rfl⟩ : syracuseStep 284119 = 426179) B426179
theorem B284139 : Blo 283827 284139 := bstep (se 1 (by rfl) ⟨213104, by rfl⟩ : syracuseStep 284139 = 426209) B426209
theorem B579059 : Blo 283827 579059 := bstep (se 1 (by rfl) ⟨434294, by rfl⟩ : syracuseStep 579059 = 868589) B868589
theorem B284151 : Blo 283827 284151 := bstep (se 1 (by rfl) ⟨213113, by rfl⟩ : syracuseStep 284151 = 426227) B426227
theorem B284171 : Blo 283827 284171 := bstep (se 1 (by rfl) ⟨213128, by rfl⟩ : syracuseStep 284171 = 426257) B426257
theorem B284183 : Blo 283827 284183 := bstep (se 1 (by rfl) ⟨213137, by rfl⟩ : syracuseStep 284183 = 426275) B426275
theorem B546329 : Blo 283827 546329 := bstep (se 2 (by rfl) ⟨204873, by rfl⟩ : syracuseStep 546329 = 409747) B409747
theorem B644633 : Blo 283827 644633 := bstep (se 2 (by rfl) ⟨241737, by rfl⟩ : syracuseStep 644633 = 483475) B483475
theorem B284203 : Blo 283827 284203 := bstep (se 1 (by rfl) ⟨213152, by rfl⟩ : syracuseStep 284203 = 426305) B426305
theorem B546355 : Blo 283827 546355 := bstep (se 1 (by rfl) ⟨409766, by rfl⟩ : syracuseStep 546355 = 819533) B819533
theorem B284215 : Blo 283827 284215 := bstep (se 1 (by rfl) ⟨213161, by rfl⟩ : syracuseStep 284215 = 426323) B426323
theorem B284235 : Blo 283827 284235 := bstep (se 1 (by rfl) ⟨213176, by rfl⟩ : syracuseStep 284235 = 426353) B426353
theorem B284247 : Blo 283827 284247 := bstep (se 1 (by rfl) ⟨213185, by rfl⟩ : syracuseStep 284247 = 426371) B426371
theorem B284267 : Blo 283827 284267 := bstep (se 1 (by rfl) ⟨213200, by rfl⟩ : syracuseStep 284267 = 426401) B426401
theorem B644723 : Blo 283827 644723 := bstep (se 1 (by rfl) ⟨483542, by rfl⟩ : syracuseStep 644723 = 967085) B967085
theorem B284279 : Blo 283827 284279 := bstep (se 1 (by rfl) ⟨213209, by rfl⟩ : syracuseStep 284279 = 426419) B426419
theorem B284299 : Blo 283827 284299 := bstep (se 1 (by rfl) ⟨213224, by rfl⟩ : syracuseStep 284299 = 426449) B426449
theorem B284311 : Blo 283827 284311 := bstep (se 1 (by rfl) ⟨213233, by rfl⟩ : syracuseStep 284311 = 426467) B426467
theorem B644759 : Blo 283827 644759 := bstep (se 1 (by rfl) ⟨483569, by rfl⟩ : syracuseStep 644759 = 967139) B967139
theorem B284331 : Blo 283827 284331 := bstep (se 1 (by rfl) ⟨213248, by rfl⟩ : syracuseStep 284331 = 426497) B426497
theorem B284343 : Blo 283827 284343 := bstep (se 1 (by rfl) ⟨213257, by rfl⟩ : syracuseStep 284343 = 426515) B426515
theorem B284363 : Blo 283827 284363 := bstep (se 1 (by rfl) ⟨213272, by rfl⟩ : syracuseStep 284363 = 426545) B426545
theorem B480971 : Blo 283827 480971 := bstep (se 1 (by rfl) ⟨360728, by rfl⟩ : syracuseStep 480971 = 721457) B721457
theorem B284375 : Blo 283827 284375 := bstep (se 1 (by rfl) ⟨213281, by rfl⟩ : syracuseStep 284375 = 426563) B426563
theorem B284395 : Blo 283827 284395 := bstep (se 1 (by rfl) ⟨213296, by rfl⟩ : syracuseStep 284395 = 426593) B426593
theorem B284407 : Blo 283827 284407 := bstep (se 1 (by rfl) ⟨213305, by rfl⟩ : syracuseStep 284407 = 426611) B426611
theorem B284427 : Blo 283827 284427 := bstep (se 1 (by rfl) ⟨213320, by rfl⟩ : syracuseStep 284427 = 426641) B426641
theorem B284439 : Blo 283827 284439 := bstep (se 1 (by rfl) ⟨213329, by rfl⟩ : syracuseStep 284439 = 426659) B426659
theorem B284459 : Blo 283827 284459 := bstep (se 1 (by rfl) ⟨213344, by rfl⟩ : syracuseStep 284459 = 426689) B426689
theorem B284471 : Blo 283827 284471 := bstep (se 1 (by rfl) ⟨213353, by rfl⟩ : syracuseStep 284471 = 426707) B426707
theorem B1103681 : Blo 283827 1103681 := bstep (se 2 (by rfl) ⟨413880, by rfl⟩ : syracuseStep 1103681 = 827761) B827761
theorem B284491 : Blo 283827 284491 := bstep (se 1 (by rfl) ⟨213368, by rfl⟩ : syracuseStep 284491 = 426737) B426737
theorem B481099 : Blo 283827 481099 := bstep (se 1 (by rfl) ⟨360824, by rfl⟩ : syracuseStep 481099 = 721649) B721649
theorem B644939 : Blo 283827 644939 := bstep (se 1 (by rfl) ⟨483704, by rfl⟩ : syracuseStep 644939 = 967409) B967409
theorem B284503 : Blo 283827 284503 := bstep (se 1 (by rfl) ⟨213377, by rfl⟩ : syracuseStep 284503 = 426755) B426755
theorem B284523 : Blo 283827 284523 := bstep (se 1 (by rfl) ⟨213392, by rfl⟩ : syracuseStep 284523 = 426785) B426785
theorem B284535 : Blo 283827 284535 := bstep (se 1 (by rfl) ⟨213401, by rfl⟩ : syracuseStep 284535 = 426803) B426803
theorem B644993 : Blo 283827 644993 := bstep (se 2 (by rfl) ⟨241872, by rfl⟩ : syracuseStep 644993 = 483745) B483745
theorem B284555 : Blo 283827 284555 := bstep (se 1 (by rfl) ⟨213416, by rfl⟩ : syracuseStep 284555 = 426833) B426833
theorem B284567 : Blo 283827 284567 := bstep (se 1 (by rfl) ⟨213425, by rfl⟩ : syracuseStep 284567 = 426851) B426851
theorem B284587 : Blo 283827 284587 := bstep (se 1 (by rfl) ⟨213440, by rfl⟩ : syracuseStep 284587 = 426881) B426881
theorem B284599 : Blo 283827 284599 := bstep (se 1 (by rfl) ⟨213449, by rfl⟩ : syracuseStep 284599 = 426899) B426899
theorem B284619 : Blo 283827 284619 := bstep (se 1 (by rfl) ⟨213464, by rfl⟩ : syracuseStep 284619 = 426929) B426929
theorem B284631 : Blo 283827 284631 := bstep (se 1 (by rfl) ⟨213473, by rfl⟩ : syracuseStep 284631 = 426947) B426947
theorem B481241 : Blo 283827 481241 := bstep (se 2 (by rfl) ⟨180465, by rfl⟩ : syracuseStep 481241 = 360931) B360931
theorem B284651 : Blo 283827 284651 := bstep (se 1 (by rfl) ⟨213488, by rfl⟩ : syracuseStep 284651 = 426977) B426977
theorem B284663 : Blo 283827 284663 := bstep (se 1 (by rfl) ⟨213497, by rfl⟩ : syracuseStep 284663 = 426995) B426995
theorem B612353 : Blo 283827 612353 := bstep (se 2 (by rfl) ⟨229632, by rfl⟩ : syracuseStep 612353 = 459265) B459265
theorem B284683 : Blo 283827 284683 := bstep (se 1 (by rfl) ⟨213512, by rfl⟩ : syracuseStep 284683 = 427025) B427025
theorem B284695 : Blo 283827 284695 := bstep (se 1 (by rfl) ⟨213521, by rfl⟩ : syracuseStep 284695 = 427043) B427043
theorem B284715 : Blo 283827 284715 := bstep (se 1 (by rfl) ⟨213536, by rfl⟩ : syracuseStep 284715 = 427073) B427073
theorem B284727 : Blo 283827 284727 := bstep (se 1 (by rfl) ⟨213545, by rfl⟩ : syracuseStep 284727 = 427091) B427091
theorem B284747 : Blo 283827 284747 := bstep (se 1 (by rfl) ⟨213560, by rfl⟩ : syracuseStep 284747 = 427121) B427121
theorem B284759 : Blo 283827 284759 := bstep (se 1 (by rfl) ⟨213569, by rfl⟩ : syracuseStep 284759 = 427139) B427139
theorem B481369 : Blo 283827 481369 := bstep (se 2 (by rfl) ⟨180513, by rfl⟩ : syracuseStep 481369 = 361027) B361027
theorem B645209 : Blo 283827 645209 := bstep (se 2 (by rfl) ⟨241953, by rfl⟩ : syracuseStep 645209 = 483907) B483907
theorem B284779 : Blo 283827 284779 := bstep (se 1 (by rfl) ⟨213584, by rfl⟩ : syracuseStep 284779 = 427169) B427169
theorem B284791 : Blo 283827 284791 := bstep (se 1 (by rfl) ⟨213593, by rfl⟩ : syracuseStep 284791 = 427187) B427187
theorem B284811 : Blo 283827 284811 := bstep (se 1 (by rfl) ⟨213608, by rfl⟩ : syracuseStep 284811 = 427217) B427217
theorem B284823 : Blo 283827 284823 := bstep (se 1 (by rfl) ⟨213617, by rfl⟩ : syracuseStep 284823 = 427235) B427235
theorem B284843 : Blo 283827 284843 := bstep (se 1 (by rfl) ⟨213632, by rfl⟩ : syracuseStep 284843 = 427265) B427265
theorem B645299 : Blo 283827 645299 := bstep (se 1 (by rfl) ⟨483974, by rfl⟩ : syracuseStep 645299 = 967949) B967949
theorem B284855 : Blo 283827 284855 := bstep (se 1 (by rfl) ⟨213641, by rfl⟩ : syracuseStep 284855 = 427283) B427283
theorem B284875 : Blo 283827 284875 := bstep (se 1 (by rfl) ⟨213656, by rfl⟩ : syracuseStep 284875 = 427313) B427313
theorem B284887 : Blo 283827 284887 := bstep (se 1 (by rfl) ⟨213665, by rfl⟩ : syracuseStep 284887 = 427331) B427331
theorem B645335 : Blo 283827 645335 := bstep (se 1 (by rfl) ⟨484001, by rfl⟩ : syracuseStep 645335 = 968003) B968003
theorem B284907 : Blo 283827 284907 := bstep (se 1 (by rfl) ⟨213680, by rfl⟩ : syracuseStep 284907 = 427361) B427361
theorem B284919 : Blo 283827 284919 := bstep (se 1 (by rfl) ⟨213689, by rfl⟩ : syracuseStep 284919 = 427379) B427379
theorem B284939 : Blo 283827 284939 := bstep (se 1 (by rfl) ⟨213704, by rfl⟩ : syracuseStep 284939 = 427409) B427409
theorem B284951 : Blo 283827 284951 := bstep (se 1 (by rfl) ⟨213713, by rfl⟩ : syracuseStep 284951 = 427427) B427427
theorem B284971 : Blo 283827 284971 := bstep (se 1 (by rfl) ⟨213728, by rfl⟩ : syracuseStep 284971 = 427457) B427457
theorem B2283821 : Blo 283827 2283821 := bstep (se 3 (by rfl) ⟨428216, by rfl⟩ : syracuseStep 2283821 = 856433) B856433
theorem B284983 : Blo 283827 284983 := bstep (se 1 (by rfl) ⟨213737, by rfl⟩ : syracuseStep 284983 = 427475) B427475
theorem B809281 : Blo 283827 809281 := bstep (se 2 (by rfl) ⟨303480, by rfl⟩ : syracuseStep 809281 = 606961) B606961
theorem B285003 : Blo 283827 285003 := bstep (se 1 (by rfl) ⟨213752, by rfl⟩ : syracuseStep 285003 = 427505) B427505
theorem B285015 : Blo 283827 285015 := bstep (se 1 (by rfl) ⟨213761, by rfl⟩ : syracuseStep 285015 = 427523) B427523
theorem B285035 : Blo 283827 285035 := bstep (se 1 (by rfl) ⟨213776, by rfl⟩ : syracuseStep 285035 = 427553) B427553
theorem B285047 : Blo 283827 285047 := bstep (se 1 (by rfl) ⟨213785, by rfl⟩ : syracuseStep 285047 = 427571) B427571
theorem B285067 : Blo 283827 285067 := bstep (se 1 (by rfl) ⟨213800, by rfl⟩ : syracuseStep 285067 = 427601) B427601
theorem B645515 : Blo 283827 645515 := bstep (se 1 (by rfl) ⟨484136, by rfl⟩ : syracuseStep 645515 = 968273) B968273
theorem B285079 : Blo 283827 285079 := bstep (se 1 (by rfl) ⟨213809, by rfl⟩ : syracuseStep 285079 = 427619) B427619
theorem B285099 : Blo 283827 285099 := bstep (se 1 (by rfl) ⟨213824, by rfl⟩ : syracuseStep 285099 = 427649) B427649
theorem B285111 : Blo 283827 285111 := bstep (se 1 (by rfl) ⟨213833, by rfl⟩ : syracuseStep 285111 = 427667) B427667
theorem B645569 : Blo 283827 645569 := bstep (se 2 (by rfl) ⟨242088, by rfl⟩ : syracuseStep 645569 = 484177) B484177
theorem B285131 : Blo 283827 285131 := bstep (se 1 (by rfl) ⟨213848, by rfl⟩ : syracuseStep 285131 = 427697) B427697
theorem B285143 : Blo 283827 285143 := bstep (se 1 (by rfl) ⟨213857, by rfl⟩ : syracuseStep 285143 = 427715) B427715
theorem B285163 : Blo 283827 285163 := bstep (se 1 (by rfl) ⟨213872, by rfl⟩ : syracuseStep 285163 = 427745) B427745
theorem B285175 : Blo 283827 285175 := bstep (se 1 (by rfl) ⟨213881, by rfl⟩ : syracuseStep 285175 = 427763) B427763
theorem B285195 : Blo 283827 285195 := bstep (se 1 (by rfl) ⟨213896, by rfl⟩ : syracuseStep 285195 = 427793) B427793
theorem B285207 : Blo 283827 285207 := bstep (se 1 (by rfl) ⟨213905, by rfl⟩ : syracuseStep 285207 = 427811) B427811
theorem B285227 : Blo 283827 285227 := bstep (se 1 (by rfl) ⟨213920, by rfl⟩ : syracuseStep 285227 = 427841) B427841
theorem B285239 : Blo 283827 285239 := bstep (se 1 (by rfl) ⟨213929, by rfl⟩ : syracuseStep 285239 = 427859) B427859
theorem B285259 : Blo 283827 285259 := bstep (se 1 (by rfl) ⟨213944, by rfl⟩ : syracuseStep 285259 = 427889) B427889
theorem B1628747 : Blo 283827 1628747 := bstep (se 1 (by rfl) ⟨1221560, by rfl⟩ : syracuseStep 1628747 = 2443121) B2443121
theorem B285271 : Blo 283827 285271 := bstep (se 1 (by rfl) ⟨213953, by rfl⟩ : syracuseStep 285271 = 427907) B427907
theorem B285291 : Blo 283827 285291 := bstep (se 1 (by rfl) ⟨213968, by rfl⟩ : syracuseStep 285291 = 427937) B427937
theorem B285303 : Blo 283827 285303 := bstep (se 1 (by rfl) ⟨213977, by rfl⟩ : syracuseStep 285303 = 427955) B427955
theorem B285323 : Blo 283827 285323 := bstep (se 1 (by rfl) ⟨213992, by rfl⟩ : syracuseStep 285323 = 427985) B427985
theorem B285335 : Blo 283827 285335 := bstep (se 1 (by rfl) ⟨214001, by rfl⟩ : syracuseStep 285335 = 428003) B428003
theorem B1759895 : Blo 283827 1759895 := bstep (se 1 (by rfl) ⟨1319921, by rfl⟩ : syracuseStep 1759895 = 2639843) B2639843
theorem B481943 : Blo 283827 481943 := bstep (se 1 (by rfl) ⟨361457, by rfl⟩ : syracuseStep 481943 = 722915) B722915
theorem B645785 : Blo 283827 645785 := bstep (se 2 (by rfl) ⟨242169, by rfl⟩ : syracuseStep 645785 = 484339) B484339
theorem B285355 : Blo 283827 285355 := bstep (se 1 (by rfl) ⟨214016, by rfl⟩ : syracuseStep 285355 = 428033) B428033
theorem B285367 : Blo 283827 285367 := bstep (se 1 (by rfl) ⟨214025, by rfl⟩ : syracuseStep 285367 = 428051) B428051
theorem B285387 : Blo 283827 285387 := bstep (se 1 (by rfl) ⟨214040, by rfl⟩ : syracuseStep 285387 = 428081) B428081
theorem B285399 : Blo 283827 285399 := bstep (se 1 (by rfl) ⟨214049, by rfl⟩ : syracuseStep 285399 = 428099) B428099
theorem B514777 : Blo 283827 514777 := bstep (se 2 (by rfl) ⟨193041, by rfl⟩ : syracuseStep 514777 = 386083) B386083
theorem B285419 : Blo 283827 285419 := bstep (se 1 (by rfl) ⟨214064, by rfl⟩ : syracuseStep 285419 = 428129) B428129
theorem B645875 : Blo 283827 645875 := bstep (se 1 (by rfl) ⟨484406, by rfl⟩ : syracuseStep 645875 = 968813) B968813
theorem B285431 : Blo 283827 285431 := bstep (se 1 (by rfl) ⟨214073, by rfl⟩ : syracuseStep 285431 = 428147) B428147
theorem B285451 : Blo 283827 285451 := bstep (se 1 (by rfl) ⟨214088, by rfl⟩ : syracuseStep 285451 = 428177) B428177
theorem B285463 : Blo 283827 285463 := bstep (se 1 (by rfl) ⟨214097, by rfl⟩ : syracuseStep 285463 = 428195) B428195
theorem B482071 : Blo 283827 482071 := bstep (se 1 (by rfl) ⟨361553, by rfl⟩ : syracuseStep 482071 = 723107) B723107
theorem B645911 : Blo 283827 645911 := bstep (se 1 (by rfl) ⟨484433, by rfl⟩ : syracuseStep 645911 = 968867) B968867
theorem B285483 : Blo 283827 285483 := bstep (se 1 (by rfl) ⟨214112, by rfl⟩ : syracuseStep 285483 = 428225) B428225
theorem B285495 : Blo 283827 285495 := bstep (se 1 (by rfl) ⟨214121, by rfl⟩ : syracuseStep 285495 = 428243) B428243
theorem B285515 : Blo 283827 285515 := bstep (se 1 (by rfl) ⟨214136, by rfl⟩ : syracuseStep 285515 = 428273) B428273
theorem B285527 : Blo 283827 285527 := bstep (se 1 (by rfl) ⟨214145, by rfl⟩ : syracuseStep 285527 = 428291) B428291
theorem B580439 : Blo 283827 580439 := bstep (se 1 (by rfl) ⟨435329, by rfl⟩ : syracuseStep 580439 = 870659) B870659
theorem B5561189 : Blo 283827 5561189 := bstep (se 4 (by rfl) ⟨521361, by rfl⟩ : syracuseStep 5561189 = 1042723) B1042723
theorem B1858405 : Blo 283827 1858405 := bstep (se 4 (by rfl) ⟨174225, by rfl⟩ : syracuseStep 1858405 = 348451) B348451
theorem B285547 : Blo 283827 285547 := bstep (se 1 (by rfl) ⟨214160, by rfl⟩ : syracuseStep 285547 = 428321) B428321
theorem B285559 : Blo 283827 285559 := bstep (se 1 (by rfl) ⟨214169, by rfl⟩ : syracuseStep 285559 = 428339) B428339
theorem B285579 : Blo 283827 285579 := bstep (se 1 (by rfl) ⟨214184, by rfl⟩ : syracuseStep 285579 = 428369) B428369
theorem B285591 : Blo 283827 285591 := bstep (se 1 (by rfl) ⟨214193, by rfl⟩ : syracuseStep 285591 = 428387) B428387
theorem B285611 : Blo 283827 285611 := bstep (se 1 (by rfl) ⟨214208, by rfl⟩ : syracuseStep 285611 = 428417) B428417
theorem B285623 : Blo 283827 285623 := bstep (se 1 (by rfl) ⟨214217, by rfl⟩ : syracuseStep 285623 = 428435) B428435
theorem B285643 : Blo 283827 285643 := bstep (se 1 (by rfl) ⟨214232, by rfl⟩ : syracuseStep 285643 = 428465) B428465
theorem B646091 : Blo 283827 646091 := bstep (se 1 (by rfl) ⟨484568, by rfl⟩ : syracuseStep 646091 = 969137) B969137
theorem B285655 : Blo 283827 285655 := bstep (se 1 (by rfl) ⟨214241, by rfl⟩ : syracuseStep 285655 = 428483) B428483
theorem B285675 : Blo 283827 285675 := bstep (se 1 (by rfl) ⟨214256, by rfl⟩ : syracuseStep 285675 = 428513) B428513
theorem B285687 : Blo 283827 285687 := bstep (se 1 (by rfl) ⟨214265, by rfl⟩ : syracuseStep 285687 = 428531) B428531
theorem B646145 : Blo 283827 646145 := bstep (se 2 (by rfl) ⟨242304, by rfl⟩ : syracuseStep 646145 = 484609) B484609
theorem B285707 : Blo 283827 285707 := bstep (se 1 (by rfl) ⟨214280, by rfl⟩ : syracuseStep 285707 = 428561) B428561
theorem B285719 : Blo 283827 285719 := bstep (se 1 (by rfl) ⟨214289, by rfl⟩ : syracuseStep 285719 = 428579) B428579
theorem B285739 : Blo 283827 285739 := bstep (se 1 (by rfl) ⟨214304, by rfl⟩ : syracuseStep 285739 = 428609) B428609
theorem B285751 : Blo 283827 285751 := bstep (se 1 (by rfl) ⟨214313, by rfl⟩ : syracuseStep 285751 = 428627) B428627
theorem B285771 : Blo 283827 285771 := bstep (se 1 (by rfl) ⟨214328, by rfl⟩ : syracuseStep 285771 = 428657) B428657
theorem B285783 : Blo 283827 285783 := bstep (se 1 (by rfl) ⟨214337, by rfl⟩ : syracuseStep 285783 = 428675) B428675
theorem B285803 : Blo 283827 285803 := bstep (se 1 (by rfl) ⟨214352, by rfl⟩ : syracuseStep 285803 = 428705) B428705
theorem B285815 : Blo 283827 285815 := bstep (se 1 (by rfl) ⟨214361, by rfl⟩ : syracuseStep 285815 = 428723) B428723
theorem B285835 : Blo 283827 285835 := bstep (se 1 (by rfl) ⟨214376, by rfl⟩ : syracuseStep 285835 = 428753) B428753
theorem B285847 : Blo 283827 285847 := bstep (se 1 (by rfl) ⟨214385, by rfl⟩ : syracuseStep 285847 = 428771) B428771
theorem B285867 : Blo 283827 285867 := bstep (se 1 (by rfl) ⟨214400, by rfl⟩ : syracuseStep 285867 = 428801) B428801
theorem B285879 : Blo 283827 285879 := bstep (se 1 (by rfl) ⟨214409, by rfl⟩ : syracuseStep 285879 = 428819) B428819
theorem B285899 : Blo 283827 285899 := bstep (se 1 (by rfl) ⟨214424, by rfl⟩ : syracuseStep 285899 = 428849) B428849
theorem B285911 : Blo 283827 285911 := bstep (se 1 (by rfl) ⟨214433, by rfl⟩ : syracuseStep 285911 = 428867) B428867
theorem B1826009 : Blo 283827 1826009 := bstep (se 2 (by rfl) ⟨684753, by rfl⟩ : syracuseStep 1826009 = 1369507) B1369507
theorem B646361 : Blo 283827 646361 := bstep (se 2 (by rfl) ⟨242385, by rfl⟩ : syracuseStep 646361 = 484771) B484771
theorem B285931 : Blo 283827 285931 := bstep (se 1 (by rfl) ⟨214448, by rfl⟩ : syracuseStep 285931 = 428897) B428897
theorem B285943 : Blo 283827 285943 := bstep (se 1 (by rfl) ⟨214457, by rfl⟩ : syracuseStep 285943 = 428915) B428915
theorem B285963 : Blo 283827 285963 := bstep (se 1 (by rfl) ⟨214472, by rfl⟩ : syracuseStep 285963 = 428945) B428945
theorem B285975 : Blo 283827 285975 := bstep (se 1 (by rfl) ⟨214481, by rfl⟩ : syracuseStep 285975 = 428963) B428963
theorem B285995 : Blo 283827 285995 := bstep (se 1 (by rfl) ⟨214496, by rfl⟩ : syracuseStep 285995 = 428993) B428993
theorem B1039661 : Blo 283827 1039661 := bstep (se 3 (by rfl) ⟨194936, by rfl⟩ : syracuseStep 1039661 = 389873) B389873
theorem B646451 : Blo 283827 646451 := bstep (se 1 (by rfl) ⟨484838, by rfl⟩ : syracuseStep 646451 = 969677) B969677
theorem B286007 : Blo 283827 286007 := bstep (se 1 (by rfl) ⟨214505, by rfl⟩ : syracuseStep 286007 = 429011) B429011
theorem B286027 : Blo 283827 286027 := bstep (se 1 (by rfl) ⟨214520, by rfl⟩ : syracuseStep 286027 = 429041) B429041
theorem B286039 : Blo 283827 286039 := bstep (se 1 (by rfl) ⟨214529, by rfl⟩ : syracuseStep 286039 = 429059) B429059
theorem B646487 : Blo 283827 646487 := bstep (se 1 (by rfl) ⟨484865, by rfl⟩ : syracuseStep 646487 = 969731) B969731
theorem B286059 : Blo 283827 286059 := bstep (se 1 (by rfl) ⟨214544, by rfl⟩ : syracuseStep 286059 = 429089) B429089
theorem B286071 : Blo 283827 286071 := bstep (se 1 (by rfl) ⟨214553, by rfl⟩ : syracuseStep 286071 = 429107) B429107
theorem B482699 : Blo 283827 482699 := bstep (se 1 (by rfl) ⟨362024, by rfl⟩ : syracuseStep 482699 = 724049) B724049
theorem B286091 : Blo 283827 286091 := bstep (se 1 (by rfl) ⟨214568, by rfl⟩ : syracuseStep 286091 = 429137) B429137
theorem B286103 : Blo 283827 286103 := bstep (se 1 (by rfl) ⟨214577, by rfl⟩ : syracuseStep 286103 = 429155) B429155
theorem B286123 : Blo 283827 286123 := bstep (se 1 (by rfl) ⟨214592, by rfl⟩ : syracuseStep 286123 = 429185) B429185
theorem B286135 : Blo 283827 286135 := bstep (se 1 (by rfl) ⟨214601, by rfl⟩ : syracuseStep 286135 = 429203) B429203
theorem B286155 : Blo 283827 286155 := bstep (se 1 (by rfl) ⟨214616, by rfl⟩ : syracuseStep 286155 = 429233) B429233
theorem B286167 : Blo 283827 286167 := bstep (se 1 (by rfl) ⟨214625, by rfl⟩ : syracuseStep 286167 = 429251) B429251
theorem B286187 : Blo 283827 286187 := bstep (se 1 (by rfl) ⟨214640, by rfl⟩ : syracuseStep 286187 = 429281) B429281
theorem B286199 : Blo 283827 286199 := bstep (se 1 (by rfl) ⟨214649, by rfl⟩ : syracuseStep 286199 = 429299) B429299
theorem B482827 : Blo 283827 482827 := bstep (se 1 (by rfl) ⟨362120, by rfl⟩ : syracuseStep 482827 = 724241) B724241
theorem B286219 : Blo 283827 286219 := bstep (se 1 (by rfl) ⟨214664, by rfl⟩ : syracuseStep 286219 = 429329) B429329
theorem B646667 : Blo 283827 646667 := bstep (se 1 (by rfl) ⟨485000, by rfl⟩ : syracuseStep 646667 = 970001) B970001
theorem B286231 : Blo 283827 286231 := bstep (se 1 (by rfl) ⟨214673, by rfl⟩ : syracuseStep 286231 = 429347) B429347
theorem B286251 : Blo 283827 286251 := bstep (se 1 (by rfl) ⟨214688, by rfl⟩ : syracuseStep 286251 = 429377) B429377
theorem B286263 : Blo 283827 286263 := bstep (se 1 (by rfl) ⟨214697, by rfl⟩ : syracuseStep 286263 = 429395) B429395
theorem B646721 : Blo 283827 646721 := bstep (se 2 (by rfl) ⟨242520, by rfl⟩ : syracuseStep 646721 = 485041) B485041
theorem B286283 : Blo 283827 286283 := bstep (se 1 (by rfl) ⟨214712, by rfl⟩ : syracuseStep 286283 = 429425) B429425
theorem B286295 : Blo 283827 286295 := bstep (se 1 (by rfl) ⟨214721, by rfl⟩ : syracuseStep 286295 = 429443) B429443
theorem B286315 : Blo 283827 286315 := bstep (se 1 (by rfl) ⟨214736, by rfl⟩ : syracuseStep 286315 = 429473) B429473
theorem B286327 : Blo 283827 286327 := bstep (se 1 (by rfl) ⟨214745, by rfl⟩ : syracuseStep 286327 = 429491) B429491
theorem B286347 : Blo 283827 286347 := bstep (se 1 (by rfl) ⟨214760, by rfl⟩ : syracuseStep 286347 = 429521) B429521
theorem B286359 : Blo 283827 286359 := bstep (se 1 (by rfl) ⟨214769, by rfl⟩ : syracuseStep 286359 = 429539) B429539
theorem B482969 : Blo 283827 482969 := bstep (se 2 (by rfl) ⟨181113, by rfl⟩ : syracuseStep 482969 = 362227) B362227
theorem B286379 : Blo 283827 286379 := bstep (se 1 (by rfl) ⟨214784, by rfl⟩ : syracuseStep 286379 = 429569) B429569
theorem B286391 : Blo 283827 286391 := bstep (se 1 (by rfl) ⟨214793, by rfl⟩ : syracuseStep 286391 = 429587) B429587
theorem B286411 : Blo 283827 286411 := bstep (se 1 (by rfl) ⟨214808, by rfl⟩ : syracuseStep 286411 = 429617) B429617
theorem B286423 : Blo 283827 286423 := bstep (se 1 (by rfl) ⟨214817, by rfl⟩ : syracuseStep 286423 = 429635) B429635
theorem B286443 : Blo 283827 286443 := bstep (se 1 (by rfl) ⟨214832, by rfl⟩ : syracuseStep 286443 = 429665) B429665
theorem B286455 : Blo 283827 286455 := bstep (se 1 (by rfl) ⟨214841, by rfl⟩ : syracuseStep 286455 = 429683) B429683
theorem B286475 : Blo 283827 286475 := bstep (se 1 (by rfl) ⟨214856, by rfl⟩ : syracuseStep 286475 = 429713) B429713
theorem B614155 : Blo 283827 614155 := bstep (se 1 (by rfl) ⟨460616, by rfl⟩ : syracuseStep 614155 = 921233) B921233
theorem B286487 : Blo 283827 286487 := bstep (se 1 (by rfl) ⟨214865, by rfl⟩ : syracuseStep 286487 = 429731) B429731
theorem B483097 : Blo 283827 483097 := bstep (se 2 (by rfl) ⟨181161, by rfl⟩ : syracuseStep 483097 = 362323) B362323
theorem B646937 : Blo 283827 646937 := bstep (se 2 (by rfl) ⟨242601, by rfl⟩ : syracuseStep 646937 = 485203) B485203
theorem B286507 : Blo 283827 286507 := bstep (se 1 (by rfl) ⟨214880, by rfl⟩ : syracuseStep 286507 = 429761) B429761
theorem B286519 : Blo 283827 286519 := bstep (se 1 (by rfl) ⟨214889, by rfl⟩ : syracuseStep 286519 = 429779) B429779
theorem B286539 : Blo 283827 286539 := bstep (se 1 (by rfl) ⟨214904, by rfl⟩ : syracuseStep 286539 = 429809) B429809
theorem B286551 : Blo 283827 286551 := bstep (se 1 (by rfl) ⟨214913, by rfl⟩ : syracuseStep 286551 = 429827) B429827
theorem B286571 : Blo 283827 286571 := bstep (se 1 (by rfl) ⟨214928, by rfl⟩ : syracuseStep 286571 = 429857) B429857
theorem B647027 : Blo 283827 647027 := bstep (se 1 (by rfl) ⟨485270, by rfl⟩ : syracuseStep 647027 = 970541) B970541
theorem B319351 : Blo 283827 319351 := bstep (se 1 (by rfl) ⟨239513, by rfl⟩ : syracuseStep 319351 = 479027) B479027
theorem B286583 : Blo 283827 286583 := bstep (se 1 (by rfl) ⟨214937, by rfl⟩ : syracuseStep 286583 = 429875) B429875
theorem B286603 : Blo 283827 286603 := bstep (se 1 (by rfl) ⟨214952, by rfl⟩ : syracuseStep 286603 = 429905) B429905
theorem B286615 : Blo 283827 286615 := bstep (se 1 (by rfl) ⟨214961, by rfl⟩ : syracuseStep 286615 = 429923) B429923
theorem B647063 : Blo 283827 647063 := bstep (se 1 (by rfl) ⟨485297, by rfl⟩ : syracuseStep 647063 = 970595) B970595
theorem B286635 : Blo 283827 286635 := bstep (se 1 (by rfl) ⟨214976, by rfl⟩ : syracuseStep 286635 = 429953) B429953
theorem B286647 : Blo 283827 286647 := bstep (se 1 (by rfl) ⟨214985, by rfl⟩ : syracuseStep 286647 = 429971) B429971
theorem B286667 : Blo 283827 286667 := bstep (se 1 (by rfl) ⟨215000, by rfl⟩ : syracuseStep 286667 = 430001) B430001
theorem B286679 : Blo 283827 286679 := bstep (se 1 (by rfl) ⟨215009, by rfl⟩ : syracuseStep 286679 = 430019) B430019
theorem B286699 : Blo 283827 286699 := bstep (se 1 (by rfl) ⟨215024, by rfl⟩ : syracuseStep 286699 = 430049) B430049
theorem B286711 : Blo 283827 286711 := bstep (se 1 (by rfl) ⟨215033, by rfl⟩ : syracuseStep 286711 = 430067) B430067
theorem B286731 : Blo 283827 286731 := bstep (se 1 (by rfl) ⟨215048, by rfl⟩ : syracuseStep 286731 = 430097) B430097
theorem B286743 : Blo 283827 286743 := bstep (se 1 (by rfl) ⟨215057, by rfl⟩ : syracuseStep 286743 = 430115) B430115
theorem B319531 : Blo 283827 319531 := bstep (se 1 (by rfl) ⟨239648, by rfl⟩ : syracuseStep 319531 = 479297) B479297
theorem B286763 : Blo 283827 286763 := bstep (se 1 (by rfl) ⟨215072, by rfl⟩ : syracuseStep 286763 = 430145) B430145
theorem B286775 : Blo 283827 286775 := bstep (se 1 (by rfl) ⟨215081, by rfl⟩ : syracuseStep 286775 = 430163) B430163
theorem B286795 : Blo 283827 286795 := bstep (se 1 (by rfl) ⟨215096, by rfl⟩ : syracuseStep 286795 = 430193) B430193
theorem B647243 : Blo 283827 647243 := bstep (se 1 (by rfl) ⟨485432, by rfl⟩ : syracuseStep 647243 = 970865) B970865
theorem B286807 : Blo 283827 286807 := bstep (se 1 (by rfl) ⟨215105, by rfl⟩ : syracuseStep 286807 = 430211) B430211
theorem B286827 : Blo 283827 286827 := bstep (se 1 (by rfl) ⟨215120, by rfl⟩ : syracuseStep 286827 = 430241) B430241
theorem B286839 : Blo 283827 286839 := bstep (se 1 (by rfl) ⟨215129, by rfl⟩ : syracuseStep 286839 = 430259) B430259
theorem B647297 : Blo 283827 647297 := bstep (se 2 (by rfl) ⟨242736, by rfl⟩ : syracuseStep 647297 = 485473) B485473
theorem B286859 : Blo 283827 286859 := bstep (se 1 (by rfl) ⟨215144, by rfl⟩ : syracuseStep 286859 = 430289) B430289
theorem B319639 : Blo 283827 319639 := bstep (se 1 (by rfl) ⟨239729, by rfl⟩ : syracuseStep 319639 = 479459) B479459
theorem B286871 : Blo 283827 286871 := bstep (se 1 (by rfl) ⟨215153, by rfl⟩ : syracuseStep 286871 = 430307) B430307
theorem B286891 : Blo 283827 286891 := bstep (se 1 (by rfl) ⟨215168, by rfl⟩ : syracuseStep 286891 = 430337) B430337
theorem B286903 : Blo 283827 286903 := bstep (se 1 (by rfl) ⟨215177, by rfl⟩ : syracuseStep 286903 = 430355) B430355
theorem B286923 : Blo 283827 286923 := bstep (se 1 (by rfl) ⟨215192, by rfl⟩ : syracuseStep 286923 = 430385) B430385
theorem B286935 : Blo 283827 286935 := bstep (se 1 (by rfl) ⟨215201, by rfl⟩ : syracuseStep 286935 = 430403) B430403
theorem B286955 : Blo 283827 286955 := bstep (se 1 (by rfl) ⟨215216, by rfl⟩ : syracuseStep 286955 = 430433) B430433
theorem B286967 : Blo 283827 286967 := bstep (se 1 (by rfl) ⟨215225, by rfl⟩ : syracuseStep 286967 = 430451) B430451
theorem B286987 : Blo 283827 286987 := bstep (se 1 (by rfl) ⟨215240, by rfl⟩ : syracuseStep 286987 = 430481) B430481
theorem B93184277 : Blo 283827 93184277 := bstep (se 6 (by rfl) ⟨2184006, by rfl⟩ : syracuseStep 93184277 = 4368013) B4368013
theorem B286999 : Blo 283827 286999 := bstep (se 1 (by rfl) ⟨215249, by rfl⟩ : syracuseStep 286999 = 430499) B430499
theorem B287019 : Blo 283827 287019 := bstep (se 1 (by rfl) ⟨215264, by rfl⟩ : syracuseStep 287019 = 430529) B430529
theorem B287031 : Blo 283827 287031 := bstep (se 1 (by rfl) ⟨215273, by rfl⟩ : syracuseStep 287031 = 430547) B430547
theorem B1827137 : Blo 283827 1827137 := bstep (se 2 (by rfl) ⟨685176, by rfl⟩ : syracuseStep 1827137 = 1370353) B1370353
theorem B319819 : Blo 283827 319819 := bstep (se 1 (by rfl) ⟨239864, by rfl⟩ : syracuseStep 319819 = 479729) B479729
theorem B287051 : Blo 283827 287051 := bstep (se 1 (by rfl) ⟨215288, by rfl⟩ : syracuseStep 287051 = 430577) B430577
theorem B483671 : Blo 283827 483671 := bstep (se 1 (by rfl) ⟨362753, by rfl⟩ : syracuseStep 483671 = 725507) B725507
theorem B287063 : Blo 283827 287063 := bstep (se 1 (by rfl) ⟨215297, by rfl⟩ : syracuseStep 287063 = 430595) B430595
theorem B647513 : Blo 283827 647513 := bstep (se 2 (by rfl) ⟨242817, by rfl⟩ : syracuseStep 647513 = 485635) B485635
theorem B287083 : Blo 283827 287083 := bstep (se 1 (by rfl) ⟨215312, by rfl⟩ : syracuseStep 287083 = 430625) B430625
theorem B287095 : Blo 283827 287095 := bstep (se 1 (by rfl) ⟨215321, by rfl⟩ : syracuseStep 287095 = 430643) B430643
theorem B287115 : Blo 283827 287115 := bstep (se 1 (by rfl) ⟨215336, by rfl⟩ : syracuseStep 287115 = 430673) B430673
theorem B287127 : Blo 283827 287127 := bstep (se 1 (by rfl) ⟨215345, by rfl⟩ : syracuseStep 287127 = 430691) B430691
theorem B287147 : Blo 283827 287147 := bstep (se 1 (by rfl) ⟨215360, by rfl⟩ : syracuseStep 287147 = 430721) B430721
theorem B647603 : Blo 283827 647603 := bstep (se 1 (by rfl) ⟨485702, by rfl⟩ : syracuseStep 647603 = 971405) B971405
theorem B319927 : Blo 283827 319927 := bstep (se 1 (by rfl) ⟨239945, by rfl⟩ : syracuseStep 319927 = 479891) B479891
theorem B287159 : Blo 283827 287159 := bstep (se 1 (by rfl) ⟨215369, by rfl⟩ : syracuseStep 287159 = 430739) B430739
theorem B287179 : Blo 283827 287179 := bstep (se 1 (by rfl) ⟨215384, by rfl⟩ : syracuseStep 287179 = 430769) B430769
theorem B483799 : Blo 283827 483799 := bstep (se 1 (by rfl) ⟨362849, by rfl⟩ : syracuseStep 483799 = 725699) B725699
theorem B287191 : Blo 283827 287191 := bstep (se 1 (by rfl) ⟨215393, by rfl⟩ : syracuseStep 287191 = 430787) B430787
theorem B287211 : Blo 283827 287211 := bstep (se 1 (by rfl) ⟨215408, by rfl⟩ : syracuseStep 287211 = 430817) B430817
theorem B287223 : Blo 283827 287223 := bstep (se 1 (by rfl) ⟨215417, by rfl⟩ : syracuseStep 287223 = 430835) B430835
theorem B287243 : Blo 283827 287243 := bstep (se 1 (by rfl) ⟨215432, by rfl⟩ : syracuseStep 287243 = 430865) B430865
theorem B287255 : Blo 283827 287255 := bstep (se 1 (by rfl) ⟨215441, by rfl⟩ : syracuseStep 287255 = 430883) B430883
theorem B287275 : Blo 283827 287275 := bstep (se 1 (by rfl) ⟨215456, by rfl⟩ : syracuseStep 287275 = 430913) B430913
theorem B287287 : Blo 283827 287287 := bstep (se 1 (by rfl) ⟨215465, by rfl⟩ : syracuseStep 287287 = 430931) B430931
theorem B287307 : Blo 283827 287307 := bstep (se 1 (by rfl) ⟨215480, by rfl⟩ : syracuseStep 287307 = 430961) B430961
theorem B287319 : Blo 283827 287319 := bstep (se 1 (by rfl) ⟨215489, by rfl⟩ : syracuseStep 287319 = 430979) B430979
theorem B320107 : Blo 283827 320107 := bstep (se 1 (by rfl) ⟨240080, by rfl⟩ : syracuseStep 320107 = 480161) B480161
theorem B287339 : Blo 283827 287339 := bstep (se 1 (by rfl) ⟨215504, by rfl⟩ : syracuseStep 287339 = 431009) B431009
theorem B287351 : Blo 283827 287351 := bstep (se 1 (by rfl) ⟨215513, by rfl⟩ : syracuseStep 287351 = 431027) B431027
theorem B516737 : Blo 283827 516737 := bstep (se 2 (by rfl) ⟨193776, by rfl⟩ : syracuseStep 516737 = 387553) B387553
theorem B287371 : Blo 283827 287371 := bstep (se 1 (by rfl) ⟨215528, by rfl⟩ : syracuseStep 287371 = 431057) B431057
theorem B287383 : Blo 283827 287383 := bstep (se 1 (by rfl) ⟨215537, by rfl⟩ : syracuseStep 287383 = 431075) B431075
theorem B287403 : Blo 283827 287403 := bstep (se 1 (by rfl) ⟨215552, by rfl⟩ : syracuseStep 287403 = 431105) B431105
theorem B287415 : Blo 283827 287415 := bstep (se 1 (by rfl) ⟨215561, by rfl⟩ : syracuseStep 287415 = 431123) B431123
theorem B287435 : Blo 283827 287435 := bstep (se 1 (by rfl) ⟨215576, by rfl⟩ : syracuseStep 287435 = 431153) B431153
theorem B320215 : Blo 283827 320215 := bstep (se 1 (by rfl) ⟨240161, by rfl⟩ : syracuseStep 320215 = 480323) B480323
theorem B287447 : Blo 283827 287447 := bstep (se 1 (by rfl) ⟨215585, by rfl⟩ : syracuseStep 287447 = 431171) B431171
theorem B287467 : Blo 283827 287467 := bstep (se 1 (by rfl) ⟨215600, by rfl⟩ : syracuseStep 287467 = 431201) B431201
theorem B287479 : Blo 283827 287479 := bstep (se 1 (by rfl) ⟨215609, by rfl⟩ : syracuseStep 287479 = 431219) B431219
theorem B287499 : Blo 283827 287499 := bstep (se 1 (by rfl) ⟨215624, by rfl⟩ : syracuseStep 287499 = 431249) B431249
theorem B287511 : Blo 283827 287511 := bstep (se 1 (by rfl) ⟨215633, by rfl⟩ : syracuseStep 287511 = 431267) B431267
theorem B287531 : Blo 283827 287531 := bstep (se 1 (by rfl) ⟨215648, by rfl⟩ : syracuseStep 287531 = 431297) B431297
theorem B287543 : Blo 283827 287543 := bstep (se 1 (by rfl) ⟨215657, by rfl⟩ : syracuseStep 287543 = 431315) B431315
theorem B287563 : Blo 283827 287563 := bstep (se 1 (by rfl) ⟨215672, by rfl⟩ : syracuseStep 287563 = 431345) B431345
theorem B287575 : Blo 283827 287575 := bstep (se 1 (by rfl) ⟨215681, by rfl⟩ : syracuseStep 287575 = 431363) B431363
theorem B287595 : Blo 283827 287595 := bstep (se 1 (by rfl) ⟨215696, by rfl⟩ : syracuseStep 287595 = 431393) B431393
theorem B287607 : Blo 283827 287607 := bstep (se 1 (by rfl) ⟨215705, by rfl⟩ : syracuseStep 287607 = 431411) B431411
theorem B320395 : Blo 283827 320395 := bstep (se 1 (by rfl) ⟨240296, by rfl⟩ : syracuseStep 320395 = 480593) B480593
theorem B287627 : Blo 283827 287627 := bstep (se 1 (by rfl) ⟨215720, by rfl⟩ : syracuseStep 287627 = 431441) B431441
theorem B287639 : Blo 283827 287639 := bstep (se 1 (by rfl) ⟨215729, by rfl⟩ : syracuseStep 287639 = 431459) B431459
theorem B287659 : Blo 283827 287659 := bstep (se 1 (by rfl) ⟨215744, by rfl⟩ : syracuseStep 287659 = 431489) B431489
theorem B8479667 : Blo 283827 8479667 := bstep (se 1 (by rfl) ⟨6359750, by rfl⟩ : syracuseStep 8479667 = 12719501) B12719501
theorem B287671 : Blo 283827 287671 := bstep (se 1 (by rfl) ⟨215753, by rfl⟩ : syracuseStep 287671 = 431507) B431507
theorem B287691 : Blo 283827 287691 := bstep (se 1 (by rfl) ⟨215768, by rfl⟩ : syracuseStep 287691 = 431537) B431537
theorem B287703 : Blo 283827 287703 := bstep (se 1 (by rfl) ⟨215777, by rfl⟩ : syracuseStep 287703 = 431555) B431555
theorem B287723 : Blo 283827 287723 := bstep (se 1 (by rfl) ⟨215792, by rfl⟩ : syracuseStep 287723 = 431585) B431585
theorem B320503 : Blo 283827 320503 := bstep (se 1 (by rfl) ⟨240377, by rfl⟩ : syracuseStep 320503 = 480755) B480755
theorem B287735 : Blo 283827 287735 := bstep (se 1 (by rfl) ⟨215801, by rfl⟩ : syracuseStep 287735 = 431603) B431603
theorem B287755 : Blo 283827 287755 := bstep (se 1 (by rfl) ⟨215816, by rfl⟩ : syracuseStep 287755 = 431633) B431633
theorem B287767 : Blo 283827 287767 := bstep (se 1 (by rfl) ⟨215825, by rfl⟩ : syracuseStep 287767 = 431651) B431651
theorem B287787 : Blo 283827 287787 := bstep (se 1 (by rfl) ⟨215840, by rfl⟩ : syracuseStep 287787 = 431681) B431681
theorem B287799 : Blo 283827 287799 := bstep (se 1 (by rfl) ⟨215849, by rfl⟩ : syracuseStep 287799 = 431699) B431699
theorem B484427 : Blo 283827 484427 := bstep (se 1 (by rfl) ⟨363320, by rfl⟩ : syracuseStep 484427 = 726641) B726641
theorem B287819 : Blo 283827 287819 := bstep (se 1 (by rfl) ⟨215864, by rfl⟩ : syracuseStep 287819 = 431729) B431729
theorem B2450533 : Blo 283827 2450533 := bstep (se 4 (by rfl) ⟨229737, by rfl⟩ : syracuseStep 2450533 = 459475) B459475
theorem B1729637 : Blo 283827 1729637 := bstep (se 4 (by rfl) ⟨162153, by rfl⟩ : syracuseStep 1729637 = 324307) B324307
theorem B517271 : Blo 283827 517271 := bstep (se 1 (by rfl) ⟨387953, by rfl⟩ : syracuseStep 517271 = 775907) B775907
theorem B320683 : Blo 283827 320683 := bstep (se 1 (by rfl) ⟨240512, by rfl⟩ : syracuseStep 320683 = 481025) B481025
theorem B1631411 : Blo 283827 1631411 := bstep (se 1 (by rfl) ⟨1223558, by rfl⟩ : syracuseStep 1631411 = 2447117) B2447117
theorem B484555 : Blo 283827 484555 := bstep (se 1 (by rfl) ⟨363416, by rfl⟩ : syracuseStep 484555 = 726833) B726833
theorem B648449 : Blo 283827 648449 := bstep (se 2 (by rfl) ⟨243168, by rfl⟩ : syracuseStep 648449 = 486337) B486337
theorem B2057489 : Blo 283827 2057489 := bstep (se 2 (by rfl) ⟨771558, by rfl⟩ : syracuseStep 2057489 = 1543117) B1543117
theorem B320791 : Blo 283827 320791 := bstep (se 1 (by rfl) ⟨240593, by rfl⟩ : syracuseStep 320791 = 481187) B481187
theorem B484697 : Blo 283827 484697 := bstep (se 2 (by rfl) ⟨181761, by rfl⟩ : syracuseStep 484697 = 363523) B363523
theorem B320971 : Blo 283827 320971 := bstep (se 1 (by rfl) ⟨240728, by rfl⟩ : syracuseStep 320971 = 481457) B481457
theorem B484825 : Blo 283827 484825 := bstep (se 2 (by rfl) ⟨181809, by rfl⟩ : syracuseStep 484825 = 363619) B363619
theorem B321079 : Blo 283827 321079 := bstep (se 1 (by rfl) ⟨240809, by rfl⟩ : syracuseStep 321079 = 481619) B481619
theorem B976601 : Blo 283827 976601 := bstep (se 2 (by rfl) ⟨366225, by rfl⟩ : syracuseStep 976601 = 732451) B732451
theorem B321259 : Blo 283827 321259 := bstep (se 1 (by rfl) ⟨240944, by rfl⟩ : syracuseStep 321259 = 481889) B481889
theorem B2615105 : Blo 283827 2615105 := bstep (se 2 (by rfl) ⟨980664, by rfl⟩ : syracuseStep 2615105 = 1961329) B1961329
theorem B321367 : Blo 283827 321367 := bstep (se 1 (by rfl) ⟨241025, by rfl⟩ : syracuseStep 321367 = 482051) B482051
theorem B2156381 : Blo 283827 2156381 := bstep (se 3 (by rfl) ⟨404321, by rfl⟩ : syracuseStep 2156381 = 808643) B808643
theorem B813017 : Blo 283827 813017 := bstep (se 2 (by rfl) ⟨304881, by rfl⟩ : syracuseStep 813017 = 609763) B609763
theorem B321547 : Blo 283827 321547 := bstep (se 1 (by rfl) ⟨241160, by rfl⟩ : syracuseStep 321547 = 482321) B482321
theorem B485399 : Blo 283827 485399 := bstep (se 1 (by rfl) ⟨364049, by rfl⟩ : syracuseStep 485399 = 728099) B728099
theorem B2451491 : Blo 283827 2451491 := bstep (se 1 (by rfl) ⟨1838618, by rfl⟩ : syracuseStep 2451491 = 3677237) B3677237
theorem B518231 : Blo 283827 518231 := bstep (se 1 (by rfl) ⟨388673, by rfl⟩ : syracuseStep 518231 = 777347) B777347
theorem B321655 : Blo 283827 321655 := bstep (se 1 (by rfl) ⟨241241, by rfl⟩ : syracuseStep 321655 = 482483) B482483
theorem B485527 : Blo 283827 485527 := bstep (se 1 (by rfl) ⟨364145, by rfl⟩ : syracuseStep 485527 = 728291) B728291
theorem B387289 : Blo 283827 387289 := bstep (se 2 (by rfl) ⟨145233, by rfl⟩ : syracuseStep 387289 = 290467) B290467
theorem B321835 : Blo 283827 321835 := bstep (se 1 (by rfl) ⟨241376, by rfl⟩ : syracuseStep 321835 = 482753) B482753
theorem B321943 : Blo 283827 321943 := bstep (se 1 (by rfl) ⟨241457, by rfl⟩ : syracuseStep 321943 = 482915) B482915
theorem B322123 : Blo 283827 322123 := bstep (se 1 (by rfl) ⟨241592, by rfl⟩ : syracuseStep 322123 = 483185) B483185
theorem B1632869 : Blo 283827 1632869 := bstep (se 4 (by rfl) ⟨153081, by rfl⟩ : syracuseStep 1632869 = 306163) B306163
theorem B322231 : Blo 283827 322231 := bstep (se 1 (by rfl) ⟨241673, by rfl⟩ : syracuseStep 322231 = 483347) B483347
theorem B322411 : Blo 283827 322411 := bstep (se 1 (by rfl) ⟨241808, by rfl⟩ : syracuseStep 322411 = 483617) B483617
theorem B322519 : Blo 283827 322519 := bstep (se 1 (by rfl) ⟨241889, by rfl⟩ : syracuseStep 322519 = 483779) B483779
theorem B1371181 : Blo 283827 1371181 := bstep (se 3 (by rfl) ⟨257096, by rfl⟩ : syracuseStep 1371181 = 514193) B514193
theorem B322699 : Blo 283827 322699 := bstep (se 1 (by rfl) ⟨242024, by rfl⟩ : syracuseStep 322699 = 484049) B484049
theorem B814283 : Blo 283827 814283 := bstep (se 1 (by rfl) ⟨610712, by rfl⟩ : syracuseStep 814283 = 1221425) B1221425
theorem B322807 : Blo 283827 322807 := bstep (se 1 (by rfl) ⟨242105, by rfl⟩ : syracuseStep 322807 = 484211) B484211
theorem B1633553 : Blo 283827 1633553 := bstep (se 2 (by rfl) ⟨612582, by rfl⟩ : syracuseStep 1633553 = 1225165) B1225165
theorem B486679 : Blo 283827 486679 := bstep (se 1 (by rfl) ⟨365009, by rfl⟩ : syracuseStep 486679 = 730019) B730019
theorem B617843 : Blo 283827 617843 := bstep (se 1 (by rfl) ⟨463382, by rfl⟩ : syracuseStep 617843 = 926765) B926765
theorem B322987 : Blo 283827 322987 := bstep (se 1 (by rfl) ⟨242240, by rfl⟩ : syracuseStep 322987 = 484481) B484481
theorem B323095 : Blo 283827 323095 := bstep (se 1 (by rfl) ⟨242321, by rfl⟩ : syracuseStep 323095 = 484643) B484643
theorem B1175233 : Blo 283827 1175233 := bstep (se 2 (by rfl) ⟨440712, by rfl⟩ : syracuseStep 1175233 = 881425) B881425
theorem B323275 : Blo 283827 323275 := bstep (se 1 (by rfl) ⟨242456, by rfl⟩ : syracuseStep 323275 = 484913) B484913
theorem B1830701 : Blo 283827 1830701 := bstep (se 3 (by rfl) ⟨343256, by rfl⟩ : syracuseStep 1830701 = 686513) B686513
theorem B323383 : Blo 283827 323383 := bstep (se 1 (by rfl) ⟨242537, by rfl⟩ : syracuseStep 323383 = 485075) B485075
theorem B323563 : Blo 283827 323563 := bstep (se 1 (by rfl) ⟨242672, by rfl⟩ : syracuseStep 323563 = 485345) B485345
theorem B323671 : Blo 283827 323671 := bstep (se 1 (by rfl) ⟨242753, by rfl⟩ : syracuseStep 323671 = 485507) B485507
theorem B684235 : Blo 283827 684235 := bstep (se 1 (by rfl) ⟨513176, by rfl⟩ : syracuseStep 684235 = 1026353) B1026353
theorem B2060549 : Blo 283827 2060549 := bstep (se 4 (by rfl) ⟨193176, by rfl⟩ : syracuseStep 2060549 = 386353) B386353
theorem B487705 : Blo 283827 487705 := bstep (se 2 (by rfl) ⟨182889, by rfl⟩ : syracuseStep 487705 = 365779) B365779
theorem B619019 : Blo 283827 619019 := bstep (se 1 (by rfl) ⟨464264, by rfl⟩ : syracuseStep 619019 = 928529) B928529
theorem B619607 : Blo 283827 619607 := bstep (se 1 (by rfl) ⟨464705, by rfl⟩ : syracuseStep 619607 = 929411) B929411
theorem B1537325 : Blo 283827 1537325 := bstep (se 3 (by rfl) ⟨288248, by rfl⟩ : syracuseStep 1537325 = 576497) B576497
theorem B1078829 : Blo 283827 1078829 := bstep (se 3 (by rfl) ⟨202280, by rfl⟩ : syracuseStep 1078829 = 404561) B404561
theorem B652865 : Blo 283827 652865 := bstep (se 2 (by rfl) ⟨244824, by rfl⟩ : syracuseStep 652865 = 489649) B489649
theorem B1078859 : Blo 283827 1078859 := bstep (se 1 (by rfl) ⟨809144, by rfl⟩ : syracuseStep 1078859 = 1618289) B1618289
theorem B2193169 : Blo 283827 2193169 := bstep (se 2 (by rfl) ⟨822438, by rfl⟩ : syracuseStep 2193169 = 1644877) B1644877
theorem B1275671 : Blo 283827 1275671 := bstep (se 1 (by rfl) ⟨956753, by rfl⟩ : syracuseStep 1275671 = 1913507) B1913507
theorem B2094913 : Blo 283827 2094913 := bstep (se 2 (by rfl) ⟨785592, by rfl⟩ : syracuseStep 2094913 = 1571185) B1571185
theorem B12318641 : Blo 283827 12318641 := bstep (se 2 (by rfl) ⟨4619490, by rfl⟩ : syracuseStep 12318641 = 9238981) B9238981
theorem B719027 : Blo 283827 719027 := bstep (se 1 (by rfl) ⟨539270, by rfl⟩ : syracuseStep 719027 = 1078541) B1078541
theorem B1079513 : Blo 283827 1079513 := bstep (se 2 (by rfl) ⟨404817, by rfl⟩ : syracuseStep 1079513 = 809635) B809635
theorem B1440017 : Blo 283827 1440017 := bstep (se 2 (by rfl) ⟨540006, by rfl⟩ : syracuseStep 1440017 = 1080013) B1080013
theorem B8255789 : Blo 283827 8255789 := bstep (se 3 (by rfl) ⟨1547960, by rfl⟩ : syracuseStep 8255789 = 3095921) B3095921
theorem B653633 : Blo 283827 653633 := bstep (se 2 (by rfl) ⟨245112, by rfl⟩ : syracuseStep 653633 = 490225) B490225
theorem B1440179 : Blo 283827 1440179 := bstep (se 1 (by rfl) ⟨1080134, by rfl⟩ : syracuseStep 1440179 = 2160269) B2160269
theorem B1636787 : Blo 283827 1636787 := bstep (se 1 (by rfl) ⟨1227590, by rfl⟩ : syracuseStep 1636787 = 2455181) B2455181
theorem B1079831 : Blo 283827 1079831 := bstep (se 1 (by rfl) ⟨809873, by rfl⟩ : syracuseStep 1079831 = 1619747) B1619747
theorem B4651613 : Blo 283827 4651613 := bstep (se 3 (by rfl) ⟨872177, by rfl⟩ : syracuseStep 4651613 = 1744355) B1744355
theorem B2456243 : Blo 283827 2456243 := bstep (se 1 (by rfl) ⟨1842182, by rfl⟩ : syracuseStep 2456243 = 3684365) B3684365
theorem B719563 : Blo 283827 719563 := bstep (se 1 (by rfl) ⟨539672, by rfl⟩ : syracuseStep 719563 = 1079345) B1079345
theorem B359255 : Blo 283827 359255 := bstep (se 1 (by rfl) ⟨269441, by rfl⟩ : syracuseStep 359255 = 538883) B538883
theorem B719705 : Blo 283827 719705 := bstep (se 2 (by rfl) ⟨269889, by rfl⟩ : syracuseStep 719705 = 539779) B539779
theorem B1538909 : Blo 283827 1538909 := bstep (se 3 (by rfl) ⟨288545, by rfl⟩ : syracuseStep 1538909 = 577091) B577091
theorem B457625 : Blo 283827 457625 := bstep (se 2 (by rfl) ⟨171609, by rfl⟩ : syracuseStep 457625 = 343219) B343219
theorem B1080499 : Blo 283827 1080499 := bstep (se 1 (by rfl) ⟨810374, by rfl⟩ : syracuseStep 1080499 = 1620749) B1620749
theorem B1375505 : Blo 283827 1375505 := bstep (se 2 (by rfl) ⟨515814, by rfl⟩ : syracuseStep 1375505 = 1031629) B1031629
theorem B654745 : Blo 283827 654745 := bstep (se 2 (by rfl) ⟨245529, by rfl⟩ : syracuseStep 654745 = 491059) B491059
theorem B622027 : Blo 283827 622027 := bstep (se 1 (by rfl) ⟨466520, by rfl⟩ : syracuseStep 622027 = 933041) B933041
theorem B359959 : Blo 283827 359959 := bstep (se 1 (by rfl) ⟨269969, by rfl⟩ : syracuseStep 359959 = 539939) B539939
theorem B3899011 : Blo 283827 3899011 := bstep (se 1 (by rfl) ⟨2924258, by rfl⟩ : syracuseStep 3899011 = 5848517) B5848517
theorem B720535 : Blo 283827 720535 := bstep (se 1 (by rfl) ⟨540401, by rfl⟩ : syracuseStep 720535 = 1080803) B1080803
theorem B425753 : Blo 283827 425753 := bstep (se 2 (by rfl) ⟨159657, by rfl⟩ : syracuseStep 425753 = 319315) B319315
theorem B1638245 : Blo 283827 1638245 := bstep (se 4 (by rfl) ⟨153585, by rfl⟩ : syracuseStep 1638245 = 307171) B307171
theorem B425867 : Blo 283827 425867 := bstep (se 1 (by rfl) ⟨319400, by rfl⟩ : syracuseStep 425867 = 638801) B638801
theorem B425879 : Blo 283827 425879 := bstep (se 1 (by rfl) ⟨319409, by rfl⟩ : syracuseStep 425879 = 638819) B638819
theorem B688051 : Blo 283827 688051 := bstep (se 1 (by rfl) ⟨516038, by rfl⟩ : syracuseStep 688051 = 1032077) B1032077
theorem B425945 : Blo 283827 425945 := bstep (se 2 (by rfl) ⟨159729, by rfl⟩ : syracuseStep 425945 = 319459) B319459
theorem B3112921 : Blo 283827 3112921 := bstep (se 2 (by rfl) ⟨1167345, by rfl⟩ : syracuseStep 3112921 = 2334691) B2334691
theorem B2162699 : Blo 283827 2162699 := bstep (se 1 (by rfl) ⟨1622024, by rfl⟩ : syracuseStep 2162699 = 3244049) B3244049
theorem B917515 : Blo 283827 917515 := bstep (se 1 (by rfl) ⟨688136, by rfl⟩ : syracuseStep 917515 = 1376273) B1376273
theorem B425999 : Blo 283827 425999 := bstep (se 1 (by rfl) ⟨319499, by rfl⟩ : syracuseStep 425999 = 638999) B638999
theorem B426041 : Blo 283827 426041 := bstep (se 2 (by rfl) ⟨159765, by rfl⟩ : syracuseStep 426041 = 319531) B319531
theorem B426119 : Blo 283827 426119 := bstep (se 1 (by rfl) ⟨319589, by rfl⟩ : syracuseStep 426119 = 639179) B639179
theorem B426155 : Blo 283827 426155 := bstep (se 1 (by rfl) ⟨319616, by rfl⟩ : syracuseStep 426155 = 639233) B639233
theorem B426185 : Blo 283827 426185 := bstep (se 2 (by rfl) ⟨159819, by rfl⟩ : syracuseStep 426185 = 319639) B319639
theorem B721163 : Blo 283827 721163 := bstep (se 1 (by rfl) ⟨540872, by rfl⟩ : syracuseStep 721163 = 1081745) B1081745
theorem B426299 : Blo 283827 426299 := bstep (se 1 (by rfl) ⟨319724, by rfl⟩ : syracuseStep 426299 = 639449) B639449
theorem B819575 : Blo 283827 819575 := bstep (se 1 (by rfl) ⟨614681, by rfl⟩ : syracuseStep 819575 = 1229363) B1229363
theorem B426359 : Blo 283827 426359 := bstep (se 1 (by rfl) ⟨319769, by rfl⟩ : syracuseStep 426359 = 639539) B639539
theorem B426383 : Blo 283827 426383 := bstep (se 1 (by rfl) ⟨319787, by rfl⟩ : syracuseStep 426383 = 639575) B639575
theorem B360875 : Blo 283827 360875 := bstep (se 1 (by rfl) ⟨270656, by rfl⟩ : syracuseStep 360875 = 541313) B541313
theorem B426425 : Blo 283827 426425 := bstep (se 2 (by rfl) ⟨159909, by rfl⟩ : syracuseStep 426425 = 319819) B319819
theorem B426503 : Blo 283827 426503 := bstep (se 1 (by rfl) ⟨319877, by rfl⟩ : syracuseStep 426503 = 639755) B639755
theorem B9208363 : Blo 283827 9208363 := bstep (se 1 (by rfl) ⟨6906272, by rfl⟩ : syracuseStep 9208363 = 13812545) B13812545
theorem B426539 : Blo 283827 426539 := bstep (se 1 (by rfl) ⟨319904, by rfl⟩ : syracuseStep 426539 = 639809) B639809
theorem B1311275 : Blo 283827 1311275 := bstep (se 1 (by rfl) ⟨983456, by rfl⟩ : syracuseStep 1311275 = 1966913) B1966913
theorem B426569 : Blo 283827 426569 := bstep (se 2 (by rfl) ⟨159963, by rfl⟩ : syracuseStep 426569 = 319927) B319927
theorem B1081943 : Blo 283827 1081943 := bstep (se 1 (by rfl) ⟨811457, by rfl⟩ : syracuseStep 1081943 = 1622915) B1622915
theorem B426683 : Blo 283827 426683 := bstep (se 1 (by rfl) ⟨320012, by rfl⟩ : syracuseStep 426683 = 640025) B640025
theorem B426743 : Blo 283827 426743 := bstep (se 1 (by rfl) ⟨320057, by rfl⟩ : syracuseStep 426743 = 640115) B640115
theorem B426767 : Blo 283827 426767 := bstep (se 1 (by rfl) ⟨320075, by rfl⟩ : syracuseStep 426767 = 640151) B640151
theorem B3277583 : Blo 283827 3277583 := bstep (se 1 (by rfl) ⟨2458187, by rfl⟩ : syracuseStep 3277583 = 4916375) B4916375
theorem B426809 : Blo 283827 426809 := bstep (se 2 (by rfl) ⟨160053, by rfl⟩ : syracuseStep 426809 = 320107) B320107
theorem B426887 : Blo 283827 426887 := bstep (se 1 (by rfl) ⟨320165, by rfl⟩ : syracuseStep 426887 = 640331) B640331
theorem B361351 : Blo 283827 361351 := bstep (se 1 (by rfl) ⟨271013, by rfl⟩ : syracuseStep 361351 = 542027) B542027
theorem B721811 : Blo 283827 721811 := bstep (se 1 (by rfl) ⟨541358, by rfl⟩ : syracuseStep 721811 = 1082717) B1082717
theorem B426923 : Blo 283827 426923 := bstep (se 1 (by rfl) ⟨320192, by rfl⟩ : syracuseStep 426923 = 640385) B640385
theorem B426953 : Blo 283827 426953 := bstep (se 2 (by rfl) ⟨160107, by rfl⟩ : syracuseStep 426953 = 320215) B320215
theorem B427067 : Blo 283827 427067 := bstep (se 1 (by rfl) ⟨320300, by rfl⟩ : syracuseStep 427067 = 640601) B640601
theorem B1082429 : Blo 283827 1082429 := bstep (se 3 (by rfl) ⟨202955, by rfl⟩ : syracuseStep 1082429 = 405911) B405911
theorem B427127 : Blo 283827 427127 := bstep (se 1 (by rfl) ⟨320345, by rfl⟩ : syracuseStep 427127 = 640691) B640691
theorem B427151 : Blo 283827 427151 := bstep (se 1 (by rfl) ⟨320363, by rfl⟩ : syracuseStep 427151 = 640727) B640727
theorem B427193 : Blo 283827 427193 := bstep (se 2 (by rfl) ⟨160197, by rfl⟩ : syracuseStep 427193 = 320395) B320395
theorem B722105 : Blo 283827 722105 := bstep (se 2 (by rfl) ⟨270789, by rfl⟩ : syracuseStep 722105 = 541579) B541579
theorem B427271 : Blo 283827 427271 := bstep (se 1 (by rfl) ⟨320453, by rfl⟩ : syracuseStep 427271 = 640907) B640907
theorem B427307 : Blo 283827 427307 := bstep (se 1 (by rfl) ⟨320480, by rfl⟩ : syracuseStep 427307 = 640961) B640961
theorem B2917691 : Blo 283827 2917691 := bstep (se 1 (by rfl) ⟨2188268, by rfl⟩ : syracuseStep 2917691 = 4376537) B4376537
theorem B427337 : Blo 283827 427337 := bstep (se 2 (by rfl) ⟨160251, by rfl⟩ : syracuseStep 427337 = 320503) B320503
theorem B361847 : Blo 283827 361847 := bstep (se 1 (by rfl) ⟨271385, by rfl⟩ : syracuseStep 361847 = 542771) B542771
theorem B1443257 : Blo 283827 1443257 := bstep (se 2 (by rfl) ⟨541221, by rfl⟩ : syracuseStep 1443257 = 1082443) B1082443
theorem B427451 : Blo 283827 427451 := bstep (se 1 (by rfl) ⟨320588, by rfl⟩ : syracuseStep 427451 = 641177) B641177
theorem B427511 : Blo 283827 427511 := bstep (se 1 (by rfl) ⟨320633, by rfl⟩ : syracuseStep 427511 = 641267) B641267
theorem B427535 : Blo 283827 427535 := bstep (se 1 (by rfl) ⟨320651, by rfl⟩ : syracuseStep 427535 = 641303) B641303
theorem B361999 : Blo 283827 361999 := bstep (se 1 (by rfl) ⟨271499, by rfl⟩ : syracuseStep 361999 = 542999) B542999
theorem B427577 : Blo 283827 427577 := bstep (se 2 (by rfl) ⟨160341, by rfl⟩ : syracuseStep 427577 = 320683) B320683
theorem B427655 : Blo 283827 427655 := bstep (se 1 (by rfl) ⟨320741, by rfl⟩ : syracuseStep 427655 = 641483) B641483
theorem B427691 : Blo 283827 427691 := bstep (se 1 (by rfl) ⟨320768, by rfl⟩ : syracuseStep 427691 = 641537) B641537
theorem B1377965 : Blo 283827 1377965 := bstep (se 3 (by rfl) ⟨258368, by rfl⟩ : syracuseStep 1377965 = 516737) B516737
theorem B362171 : Blo 283827 362171 := bstep (se 1 (by rfl) ⟨271628, by rfl⟩ : syracuseStep 362171 = 543257) B543257
theorem B427721 : Blo 283827 427721 := bstep (se 2 (by rfl) ⟨160395, by rfl⟩ : syracuseStep 427721 = 320791) B320791
theorem B5506865 : Blo 283827 5506865 := bstep (se 2 (by rfl) ⟨2065074, by rfl⟩ : syracuseStep 5506865 = 4130149) B4130149
theorem B427835 : Blo 283827 427835 := bstep (se 1 (by rfl) ⟨320876, by rfl⟩ : syracuseStep 427835 = 641753) B641753
theorem B460603 : Blo 283827 460603 := bstep (se 1 (by rfl) ⟨345452, by rfl⟩ : syracuseStep 460603 = 690905) B690905
theorem B722803 : Blo 283827 722803 := bstep (se 1 (by rfl) ⟨542102, by rfl⟩ : syracuseStep 722803 = 1084205) B1084205
theorem B427895 : Blo 283827 427895 := bstep (se 1 (by rfl) ⟨320921, by rfl⟩ : syracuseStep 427895 = 641843) B641843
theorem B427919 : Blo 283827 427919 := bstep (se 1 (by rfl) ⟨320939, by rfl⟩ : syracuseStep 427919 = 641879) B641879
theorem B2164643 : Blo 283827 2164643 := bstep (se 1 (by rfl) ⟨1623482, by rfl⟩ : syracuseStep 2164643 = 3246965) B3246965
theorem B427961 : Blo 283827 427961 := bstep (se 2 (by rfl) ⟨160485, by rfl⟩ : syracuseStep 427961 = 320971) B320971
theorem B722945 : Blo 283827 722945 := bstep (se 2 (by rfl) ⟨271104, by rfl⟩ : syracuseStep 722945 = 542209) B542209
theorem B428039 : Blo 283827 428039 := bstep (se 1 (by rfl) ⟨321029, by rfl⟩ : syracuseStep 428039 = 642059) B642059
theorem B428075 : Blo 283827 428075 := bstep (se 1 (by rfl) ⟨321056, by rfl⟩ : syracuseStep 428075 = 642113) B642113
theorem B428105 : Blo 283827 428105 := bstep (se 2 (by rfl) ⟨160539, by rfl⟩ : syracuseStep 428105 = 321079) B321079
theorem B428219 : Blo 283827 428219 := bstep (se 1 (by rfl) ⟨321164, by rfl⟩ : syracuseStep 428219 = 642329) B642329
theorem B428279 : Blo 283827 428279 := bstep (se 1 (by rfl) ⟨321209, by rfl⟩ : syracuseStep 428279 = 642419) B642419
theorem B428303 : Blo 283827 428303 := bstep (se 1 (by rfl) ⟨321227, by rfl⟩ : syracuseStep 428303 = 642455) B642455
theorem B428345 : Blo 283827 428345 := bstep (se 2 (by rfl) ⟨160629, by rfl⟩ : syracuseStep 428345 = 321259) B321259
theorem B428423 : Blo 283827 428423 := bstep (se 1 (by rfl) ⟨321317, by rfl⟩ : syracuseStep 428423 = 642635) B642635
theorem B428459 : Blo 283827 428459 := bstep (se 1 (by rfl) ⟨321344, by rfl⟩ : syracuseStep 428459 = 642689) B642689
theorem B428489 : Blo 283827 428489 := bstep (se 2 (by rfl) ⟨160683, by rfl⟩ : syracuseStep 428489 = 321367) B321367
theorem B723401 : Blo 283827 723401 := bstep (se 2 (by rfl) ⟨271275, by rfl⟩ : syracuseStep 723401 = 542551) B542551
theorem B428603 : Blo 283827 428603 := bstep (se 1 (by rfl) ⟨321452, by rfl⟩ : syracuseStep 428603 = 642905) B642905
theorem B428663 : Blo 283827 428663 := bstep (se 1 (by rfl) ⟨321497, by rfl⟩ : syracuseStep 428663 = 642995) B642995
theorem B363143 : Blo 283827 363143 := bstep (se 1 (by rfl) ⟨272357, by rfl⟩ : syracuseStep 363143 = 544715) B544715
theorem B428687 : Blo 283827 428687 := bstep (se 1 (by rfl) ⟨321515, by rfl⟩ : syracuseStep 428687 = 643031) B643031
theorem B428729 : Blo 283827 428729 := bstep (se 2 (by rfl) ⟨160773, by rfl⟩ : syracuseStep 428729 = 321547) B321547
theorem B1444553 : Blo 283827 1444553 := bstep (se 2 (by rfl) ⟨541707, by rfl⟩ : syracuseStep 1444553 = 1083415) B1083415
theorem B428807 : Blo 283827 428807 := bstep (se 1 (by rfl) ⟨321605, by rfl⟩ : syracuseStep 428807 = 643211) B643211
theorem B1084175 : Blo 283827 1084175 := bstep (se 1 (by rfl) ⟨813131, by rfl⟩ : syracuseStep 1084175 = 1626263) B1626263
theorem B920335 : Blo 283827 920335 := bstep (se 1 (by rfl) ⟨690251, by rfl⟩ : syracuseStep 920335 = 1380503) B1380503
theorem B428843 : Blo 283827 428843 := bstep (se 1 (by rfl) ⟨321632, by rfl⟩ : syracuseStep 428843 = 643265) B643265
theorem B723755 : Blo 283827 723755 := bstep (se 1 (by rfl) ⟨542816, by rfl⟩ : syracuseStep 723755 = 1085633) B1085633
theorem B428873 : Blo 283827 428873 := bstep (se 2 (by rfl) ⟨160827, by rfl⟩ : syracuseStep 428873 = 321655) B321655
theorem B12389219 : Blo 283827 12389219 := bstep (se 1 (by rfl) ⟨9291914, by rfl⟩ : syracuseStep 12389219 = 18583829) B18583829
theorem B3083123 : Blo 283827 3083123 := bstep (se 1 (by rfl) ⟨2312342, by rfl⟩ : syracuseStep 3083123 = 4624685) B4624685
theorem B428987 : Blo 283827 428987 := bstep (se 1 (by rfl) ⟨321740, by rfl⟩ : syracuseStep 428987 = 643481) B643481
theorem B429047 : Blo 283827 429047 := bstep (se 1 (by rfl) ⟨321785, by rfl⟩ : syracuseStep 429047 = 643571) B643571
theorem B429071 : Blo 283827 429071 := bstep (se 1 (by rfl) ⟨321803, by rfl⟩ : syracuseStep 429071 = 643607) B643607
theorem B429113 : Blo 283827 429113 := bstep (se 2 (by rfl) ⟨160917, by rfl⟩ : syracuseStep 429113 = 321835) B321835
theorem B1379389 : Blo 283827 1379389 := bstep (se 3 (by rfl) ⟨258635, by rfl⟩ : syracuseStep 1379389 = 517271) B517271
theorem B429191 : Blo 283827 429191 := bstep (se 1 (by rfl) ⟨321893, by rfl⟩ : syracuseStep 429191 = 643787) B643787
theorem B429227 : Blo 283827 429227 := bstep (se 1 (by rfl) ⟨321920, by rfl⟩ : syracuseStep 429227 = 643841) B643841
theorem B3083465 : Blo 283827 3083465 := bstep (se 2 (by rfl) ⟨1156299, by rfl⟩ : syracuseStep 3083465 = 2312599) B2312599
theorem B429257 : Blo 283827 429257 := bstep (se 2 (by rfl) ⟨160971, by rfl⟩ : syracuseStep 429257 = 321943) B321943
theorem B363791 : Blo 283827 363791 := bstep (se 1 (by rfl) ⟨272843, by rfl⟩ : syracuseStep 363791 = 545687) B545687
theorem B429371 : Blo 283827 429371 := bstep (se 1 (by rfl) ⟨322028, by rfl⟩ : syracuseStep 429371 = 644057) B644057
theorem B429431 : Blo 283827 429431 := bstep (se 1 (by rfl) ⟨322073, by rfl⟩ : syracuseStep 429431 = 644147) B644147
theorem B429455 : Blo 283827 429455 := bstep (se 1 (by rfl) ⟨322091, by rfl⟩ : syracuseStep 429455 = 644183) B644183
theorem B429497 : Blo 283827 429497 := bstep (se 2 (by rfl) ⟨161061, by rfl⟩ : syracuseStep 429497 = 322123) B322123
theorem B429575 : Blo 283827 429575 := bstep (se 1 (by rfl) ⟨322181, by rfl⟩ : syracuseStep 429575 = 644363) B644363
theorem B429611 : Blo 283827 429611 := bstep (se 1 (by rfl) ⟨322208, by rfl⟩ : syracuseStep 429611 = 644417) B644417
theorem B462395 : Blo 283827 462395 := bstep (se 1 (by rfl) ⟨346796, by rfl⟩ : syracuseStep 462395 = 693593) B693593
theorem B429641 : Blo 283827 429641 := bstep (se 2 (by rfl) ⟨161115, by rfl⟩ : syracuseStep 429641 = 322231) B322231
theorem B364219 : Blo 283827 364219 := bstep (se 1 (by rfl) ⟨273164, by rfl⟩ : syracuseStep 364219 = 546329) B546329
theorem B429755 : Blo 283827 429755 := bstep (se 1 (by rfl) ⟨322316, by rfl⟩ : syracuseStep 429755 = 644633) B644633
theorem B429815 : Blo 283827 429815 := bstep (se 1 (by rfl) ⟨322361, by rfl⟩ : syracuseStep 429815 = 644723) B644723
theorem B724747 : Blo 283827 724747 := bstep (se 1 (by rfl) ⟨543560, by rfl⟩ : syracuseStep 724747 = 1087121) B1087121
theorem B429839 : Blo 283827 429839 := bstep (se 1 (by rfl) ⟨322379, by rfl⟩ : syracuseStep 429839 = 644759) B644759
theorem B429881 : Blo 283827 429881 := bstep (se 2 (by rfl) ⟨161205, by rfl⟩ : syracuseStep 429881 = 322411) B322411
theorem B429959 : Blo 283827 429959 := bstep (se 1 (by rfl) ⟨322469, by rfl⟩ : syracuseStep 429959 = 644939) B644939
theorem B724889 : Blo 283827 724889 := bstep (se 2 (by rfl) ⟨271833, by rfl⟩ : syracuseStep 724889 = 543667) B543667
theorem B429995 : Blo 283827 429995 := bstep (se 1 (by rfl) ⟨322496, by rfl⟩ : syracuseStep 429995 = 644993) B644993
theorem B430025 : Blo 283827 430025 := bstep (se 2 (by rfl) ⟨161259, by rfl⟩ : syracuseStep 430025 = 322519) B322519
theorem B725051 : Blo 283827 725051 := bstep (se 1 (by rfl) ⟨543788, by rfl⟩ : syracuseStep 725051 = 1087577) B1087577
theorem B430139 : Blo 283827 430139 := bstep (se 1 (by rfl) ⟨322604, by rfl⟩ : syracuseStep 430139 = 645209) B645209
theorem B430199 : Blo 283827 430199 := bstep (se 1 (by rfl) ⟨322649, by rfl⟩ : syracuseStep 430199 = 645299) B645299
theorem B921719 : Blo 283827 921719 := bstep (se 1 (by rfl) ⟨691289, by rfl⟩ : syracuseStep 921719 = 1382579) B1382579
theorem B430223 : Blo 283827 430223 := bstep (se 1 (by rfl) ⟨322667, by rfl⟩ : syracuseStep 430223 = 645335) B645335
theorem B1740973 : Blo 283827 1740973 := bstep (se 3 (by rfl) ⟨326432, by rfl⟩ : syracuseStep 1740973 = 652865) B652865
theorem B430265 : Blo 283827 430265 := bstep (se 2 (by rfl) ⟨161349, by rfl⟩ : syracuseStep 430265 = 322699) B322699
theorem B430343 : Blo 283827 430343 := bstep (se 1 (by rfl) ⟨322757, by rfl⟩ : syracuseStep 430343 = 645515) B645515
theorem B2167073 : Blo 283827 2167073 := bstep (se 2 (by rfl) ⟨812652, by rfl⟩ : syracuseStep 2167073 = 1625305) B1625305
theorem B430379 : Blo 283827 430379 := bstep (se 1 (by rfl) ⟨322784, by rfl⟩ : syracuseStep 430379 = 645569) B645569
theorem B430409 : Blo 283827 430409 := bstep (se 2 (by rfl) ⟨161403, by rfl⟩ : syracuseStep 430409 = 322807) B322807
theorem B1085831 : Blo 283827 1085831 := bstep (se 1 (by rfl) ⟨814373, by rfl⟩ : syracuseStep 1085831 = 1628747) B1628747
theorem B725395 : Blo 283827 725395 := bstep (se 1 (by rfl) ⟨544046, by rfl⟩ : syracuseStep 725395 = 1088093) B1088093
theorem B430523 : Blo 283827 430523 := bstep (se 1 (by rfl) ⟨322892, by rfl⟩ : syracuseStep 430523 = 645785) B645785
theorem B430583 : Blo 283827 430583 := bstep (se 1 (by rfl) ⟨322937, by rfl⟩ : syracuseStep 430583 = 645875) B645875
theorem B430607 : Blo 283827 430607 := bstep (se 1 (by rfl) ⟨322955, by rfl⟩ : syracuseStep 430607 = 645911) B645911
theorem B725537 : Blo 283827 725537 := bstep (se 2 (by rfl) ⟨272076, by rfl⟩ : syracuseStep 725537 = 544153) B544153
theorem B430649 : Blo 283827 430649 := bstep (se 2 (by rfl) ⟨161493, by rfl⟩ : syracuseStep 430649 = 322987) B322987
theorem B3707459 : Blo 283827 3707459 := bstep (se 1 (by rfl) ⟨2780594, by rfl⟩ : syracuseStep 3707459 = 5561189) B5561189
theorem B2757239 : Blo 283827 2757239 := bstep (se 1 (by rfl) ⟨2067929, by rfl⟩ : syracuseStep 2757239 = 4135859) B4135859
theorem B430727 : Blo 283827 430727 := bstep (se 1 (by rfl) ⟨323045, by rfl⟩ : syracuseStep 430727 = 646091) B646091
theorem B430763 : Blo 283827 430763 := bstep (se 1 (by rfl) ⟨323072, by rfl⟩ : syracuseStep 430763 = 646145) B646145
theorem B430793 : Blo 283827 430793 := bstep (se 2 (by rfl) ⟨161547, by rfl⟩ : syracuseStep 430793 = 323095) B323095
theorem B1217339 : Blo 283827 1217339 := bstep (se 1 (by rfl) ⟨913004, by rfl⟩ : syracuseStep 1217339 = 1826009) B1826009
theorem B430907 : Blo 283827 430907 := bstep (se 1 (by rfl) ⟨323180, by rfl⟩ : syracuseStep 430907 = 646361) B646361
theorem B693107 : Blo 283827 693107 := bstep (se 1 (by rfl) ⟨519830, by rfl⟩ : syracuseStep 693107 = 1039661) B1039661
theorem B430967 : Blo 283827 430967 := bstep (se 1 (by rfl) ⟨323225, by rfl⟩ : syracuseStep 430967 = 646451) B646451
theorem B430991 : Blo 283827 430991 := bstep (se 1 (by rfl) ⟨323243, by rfl⟩ : syracuseStep 430991 = 646487) B646487
theorem B1643417 : Blo 283827 1643417 := bstep (se 2 (by rfl) ⟨616281, by rfl⟩ : syracuseStep 1643417 = 1232563) B1232563
theorem B431033 : Blo 283827 431033 := bstep (se 2 (by rfl) ⟨161637, by rfl⟩ : syracuseStep 431033 = 323275) B323275
theorem B431111 : Blo 283827 431111 := bstep (se 1 (by rfl) ⟨323333, by rfl⟩ : syracuseStep 431111 = 646667) B646667
theorem B1381387 : Blo 283827 1381387 := bstep (se 1 (by rfl) ⟨1036040, by rfl⟩ : syracuseStep 1381387 = 2072081) B2072081
theorem B431147 : Blo 283827 431147 := bstep (se 1 (by rfl) ⟨323360, by rfl⟩ : syracuseStep 431147 = 646721) B646721
theorem B431177 : Blo 283827 431177 := bstep (se 2 (by rfl) ⟨161691, by rfl⟩ : syracuseStep 431177 = 323383) B323383
theorem B431291 : Blo 283827 431291 := bstep (se 1 (by rfl) ⟨323468, by rfl⟩ : syracuseStep 431291 = 646937) B646937
theorem B2168045 : Blo 283827 2168045 := bstep (se 3 (by rfl) ⟨406508, by rfl⟩ : syracuseStep 2168045 = 813017) B813017
theorem B4658413 : Blo 283827 4658413 := bstep (se 3 (by rfl) ⟨873452, by rfl⟩ : syracuseStep 4658413 = 1746905) B1746905
theorem B431351 : Blo 283827 431351 := bstep (se 1 (by rfl) ⟨323513, by rfl⟩ : syracuseStep 431351 = 647027) B647027
theorem B431375 : Blo 283827 431375 := bstep (se 1 (by rfl) ⟨323531, by rfl⟩ : syracuseStep 431375 = 647063) B647063
theorem B431417 : Blo 283827 431417 := bstep (se 2 (by rfl) ⟨161781, by rfl⟩ : syracuseStep 431417 = 323563) B323563
theorem B431495 : Blo 283827 431495 := bstep (se 1 (by rfl) ⟨323621, by rfl⟩ : syracuseStep 431495 = 647243) B647243
theorem B431531 : Blo 283827 431531 := bstep (se 1 (by rfl) ⟨323648, by rfl⟩ : syracuseStep 431531 = 647297) B647297
theorem B2069945 : Blo 283827 2069945 := bstep (se 2 (by rfl) ⟨776229, by rfl⟩ : syracuseStep 2069945 = 1552459) B1552459
theorem B431561 : Blo 283827 431561 := bstep (se 2 (by rfl) ⟨161835, by rfl⟩ : syracuseStep 431561 = 323671) B323671
theorem B726529 : Blo 283827 726529 := bstep (se 2 (by rfl) ⟨272448, by rfl⟩ : syracuseStep 726529 = 544897) B544897
theorem B1218091 : Blo 283827 1218091 := bstep (se 1 (by rfl) ⟨913568, by rfl⟩ : syracuseStep 1218091 = 1827137) B1827137
theorem B431675 : Blo 283827 431675 := bstep (se 1 (by rfl) ⟨323756, by rfl⟩ : syracuseStep 431675 = 647513) B647513
theorem B431735 : Blo 283827 431735 := bstep (se 1 (by rfl) ⟨323801, by rfl⟩ : syracuseStep 431735 = 647603) B647603
theorem B3249881 : Blo 283827 3249881 := bstep (se 2 (by rfl) ⟨1218705, by rfl⟩ : syracuseStep 3249881 = 2437411) B2437411
theorem B1153091 : Blo 283827 1153091 := bstep (se 1 (by rfl) ⟨864818, by rfl⟩ : syracuseStep 1153091 = 1729637) B1729637
theorem B727127 : Blo 283827 727127 := bstep (se 1 (by rfl) ⟨545345, by rfl⟩ : syracuseStep 727127 = 1090691) B1090691
theorem B4954229 : Blo 283827 4954229 := bstep (se 5 (by rfl) ⟨232229, by rfl⟩ : syracuseStep 4954229 = 464459) B464459
theorem B1087607 : Blo 283827 1087607 := bstep (se 1 (by rfl) ⟨815705, by rfl⟩ : syracuseStep 1087607 = 1631411) B1631411
theorem B432299 : Blo 283827 432299 := bstep (se 1 (by rfl) ⟨324224, by rfl⟩ : syracuseStep 432299 = 648449) B648449
theorem B727339 : Blo 283827 727339 := bstep (se 1 (by rfl) ⟨545504, by rfl⟩ : syracuseStep 727339 = 1091009) B1091009
theorem B727481 : Blo 283827 727481 := bstep (se 2 (by rfl) ⟨272805, by rfl⟩ : syracuseStep 727481 = 545611) B545611
theorem B629537 : Blo 283827 629537 := bstep (se 2 (by rfl) ⟨236076, by rfl⟩ : syracuseStep 629537 = 472153) B472153
theorem B1088579 : Blo 283827 1088579 := bstep (se 1 (by rfl) ⟨816434, by rfl⟩ : syracuseStep 1088579 = 1632869) B1632869
theorem B1973335 : Blo 283827 1973335 := bstep (se 1 (by rfl) ⟨1480001, by rfl⟩ : syracuseStep 1973335 = 2960003) B2960003
theorem B2169989 : Blo 283827 2169989 := bstep (se 4 (by rfl) ⟨203436, by rfl⟩ : syracuseStep 2169989 = 406873) B406873
theorem B728473 : Blo 283827 728473 := bstep (se 2 (by rfl) ⟨273177, by rfl⟩ : syracuseStep 728473 = 546355) B546355
theorem B1089035 : Blo 283827 1089035 := bstep (se 1 (by rfl) ⟨816776, by rfl⟩ : syracuseStep 1089035 = 1633553) B1633553
theorem B958013 : Blo 283827 958013 := bstep (se 3 (by rfl) ⟨179627, by rfl⟩ : syracuseStep 958013 = 359255) B359255
theorem B2924225 : Blo 283827 2924225 := bstep (se 2 (by rfl) ⟨1096584, by rfl⟩ : syracuseStep 2924225 = 2193169) B2193169
theorem B2793217 : Blo 283827 2793217 := bstep (se 2 (by rfl) ⟨1047456, by rfl⟩ : syracuseStep 2793217 = 2094913) B2094913
theorem B1220467 : Blo 283827 1220467 := bstep (se 1 (by rfl) ⟨915350, by rfl⟩ : syracuseStep 1220467 = 1830701) B1830701
theorem B1450385 : Blo 283827 1450385 := bstep (se 2 (by rfl) ⟨543894, by rfl⟩ : syracuseStep 1450385 = 1087789) B1087789
theorem B1024883 : Blo 283827 1024883 := bstep (se 1 (by rfl) ⟨768662, by rfl⟩ : syracuseStep 1024883 = 1537325) B1537325
theorem B959417 : Blo 283827 959417 := bstep (se 2 (by rfl) ⟨359781, by rfl⟩ : syracuseStep 959417 = 719563) B719563
theorem B2433995 : Blo 283827 2433995 := bstep (se 1 (by rfl) ⟨1825496, by rfl⟩ : syracuseStep 2433995 = 3650993) B3650993
theorem B2172419 : Blo 283827 2172419 := bstep (se 1 (by rfl) ⟨1629314, by rfl⟩ : syracuseStep 2172419 = 3258629) B3258629
theorem B960011 : Blo 283827 960011 := bstep (se 1 (by rfl) ⟨720008, by rfl⟩ : syracuseStep 960011 = 1440017) B1440017
theorem B435755 : Blo 283827 435755 := bstep (se 1 (by rfl) ⟨326816, by rfl⟩ : syracuseStep 435755 = 653633) B653633
theorem B960119 : Blo 283827 960119 := bstep (se 1 (by rfl) ⟨720089, by rfl⟩ : syracuseStep 960119 = 1440179) B1440179
theorem B1091191 : Blo 283827 1091191 := bstep (se 1 (by rfl) ⟨818393, by rfl⟩ : syracuseStep 1091191 = 1636787) B1636787
theorem B1025939 : Blo 283827 1025939 := bstep (se 1 (by rfl) ⟨769454, by rfl⟩ : syracuseStep 1025939 = 1538909) B1538909
theorem B829369 : Blo 283827 829369 := bstep (se 2 (by rfl) ⟨311013, by rfl⟩ : syracuseStep 829369 = 622027) B622027
theorem B305083 : Blo 283827 305083 := bstep (se 1 (by rfl) ⟨228812, by rfl⟩ : syracuseStep 305083 = 457625) B457625
theorem B960713 : Blo 283827 960713 := bstep (se 2 (by rfl) ⟨360267, by rfl⟩ : syracuseStep 960713 = 720535) B720535
theorem B1452491 : Blo 283827 1452491 := bstep (se 1 (by rfl) ⟨1089368, by rfl⟩ : syracuseStep 1452491 = 2178737) B2178737
theorem B1092163 : Blo 283827 1092163 := bstep (se 1 (by rfl) ⟨819122, by rfl⟩ : syracuseStep 1092163 = 1638245) B1638245
theorem B1616557 : Blo 283827 1616557 := bstep (se 3 (by rfl) ⟨303104, by rfl⟩ : syracuseStep 1616557 = 606209) B606209
theorem B436921 : Blo 283827 436921 := bstep (se 2 (by rfl) ⟨163845, by rfl⟩ : syracuseStep 436921 = 327691) B327691
theorem B1452815 : Blo 283827 1452815 := bstep (se 1 (by rfl) ⟨1089611, by rfl⟩ : syracuseStep 1452815 = 2179223) B2179223
theorem B1092467 : Blo 283827 1092467 := bstep (se 1 (by rfl) ⟨819350, by rfl⟩ : syracuseStep 1092467 = 1638701) B1638701
theorem B961415 : Blo 283827 961415 := bstep (se 1 (by rfl) ⟨721061, by rfl⟩ : syracuseStep 961415 = 1442123) B1442123
theorem B1551251 : Blo 283827 1551251 := bstep (se 1 (by rfl) ⟨1163438, by rfl⟩ : syracuseStep 1551251 = 2326877) B2326877
theorem B1551403 : Blo 283827 1551403 := bstep (se 1 (by rfl) ⟨1163552, by rfl⟩ : syracuseStep 1551403 = 2327105) B2327105
theorem B699479 : Blo 283827 699479 := bstep (se 1 (by rfl) ⟨524609, by rfl⟩ : syracuseStep 699479 = 1049219) B1049219
theorem B961793 : Blo 283827 961793 := bstep (se 2 (by rfl) ⟨360672, by rfl⟩ : syracuseStep 961793 = 721345) B721345
theorem B248491405 : Blo 283827 248491405 := bstep (se 3 (by rfl) ⟨46592138, by rfl⟩ : syracuseStep 248491405 = 93184277) B93184277
theorem B962603 : Blo 283827 962603 := bstep (se 1 (by rfl) ⟨721952, by rfl⟩ : syracuseStep 962603 = 1443905) B1443905
theorem B733303 : Blo 283827 733303 := bstep (se 1 (by rfl) ⟨549977, by rfl⟩ : syracuseStep 733303 = 1099955) B1099955
theorem B1454273 : Blo 283827 1454273 := bstep (se 2 (by rfl) ⟨545352, by rfl⟩ : syracuseStep 1454273 = 1090705) B1090705
theorem B438841 : Blo 283827 438841 := bstep (se 2 (by rfl) ⟨164565, by rfl⟩ : syracuseStep 438841 = 329131) B329131
theorem B2765771 : Blo 283827 2765771 := bstep (se 1 (by rfl) ⟨2074328, by rfl⟩ : syracuseStep 2765771 = 4148657) B4148657
theorem B1618973 : Blo 283827 1618973 := bstep (se 3 (by rfl) ⟨303557, by rfl⟩ : syracuseStep 1618973 = 607115) B607115
theorem B963899 : Blo 283827 963899 := bstep (se 1 (by rfl) ⟨722924, by rfl⟩ : syracuseStep 963899 = 1445849) B1445849
theorem B1455569 : Blo 283827 1455569 := bstep (se 2 (by rfl) ⟨545838, by rfl⟩ : syracuseStep 1455569 = 1091677) B1091677
theorem B1652285 : Blo 283827 1652285 := bstep (se 3 (by rfl) ⟨309803, by rfl⟩ : syracuseStep 1652285 = 619607) B619607
theorem B767603 : Blo 283827 767603 := bstep (se 1 (by rfl) ⟨575702, by rfl⟩ : syracuseStep 767603 = 1151405) B1151405
theorem B1226497 : Blo 283827 1226497 := bstep (se 2 (by rfl) ⟨459936, by rfl⟩ : syracuseStep 1226497 = 919873) B919873
theorem B964385 : Blo 283827 964385 := bstep (se 2 (by rfl) ⟨361644, by rfl⟩ : syracuseStep 964385 = 723289) B723289
theorem B407369 : Blo 283827 407369 := bstep (se 2 (by rfl) ⟨152763, by rfl⟩ : syracuseStep 407369 = 305527) B305527
theorem B3159971 : Blo 283827 3159971 := bstep (se 1 (by rfl) ⟨2369978, by rfl⟩ : syracuseStep 3159971 = 4739957) B4739957
theorem B342031 : Blo 283827 342031 := bstep (se 1 (by rfl) ⟨256523, by rfl⟩ : syracuseStep 342031 = 513047) B513047
theorem B1226839 : Blo 283827 1226839 := bstep (se 1 (by rfl) ⟨920129, by rfl⟩ : syracuseStep 1226839 = 1840259) B1840259
theorem B538913 : Blo 283827 538913 := bstep (se 2 (by rfl) ⟨202092, by rfl⟩ : syracuseStep 538913 = 404185) B404185
theorem B964979 : Blo 283827 964979 := bstep (se 1 (by rfl) ⟨723734, by rfl⟩ : syracuseStep 964979 = 1447469) B1447469
theorem B539065 : Blo 283827 539065 := bstep (se 2 (by rfl) ⟨202149, by rfl⟩ : syracuseStep 539065 = 404299) B404299
theorem B4143581 : Blo 283827 4143581 := bstep (se 3 (by rfl) ⟨776921, by rfl⟩ : syracuseStep 4143581 = 1553843) B1553843
theorem B735787 : Blo 283827 735787 := bstep (se 1 (by rfl) ⟨551840, by rfl⟩ : syracuseStep 735787 = 1103681) B1103681
theorem B408235 : Blo 283827 408235 := bstep (se 1 (by rfl) ⟨306176, by rfl⟩ : syracuseStep 408235 = 612353) B612353
theorem B2177765 : Blo 283827 2177765 := bstep (se 4 (by rfl) ⟨204165, by rfl⟩ : syracuseStep 2177765 = 408331) B408331
theorem B1522547 : Blo 283827 1522547 := bstep (se 1 (by rfl) ⟨1141910, by rfl⟩ : syracuseStep 1522547 = 2283821) B2283821
theorem B2604269 : Blo 283827 2604269 := bstep (se 3 (by rfl) ⟨488300, by rfl⟩ : syracuseStep 2604269 = 976601) B976601
theorem B1621457 : Blo 283827 1621457 := bstep (se 2 (by rfl) ⟨608046, by rfl⟩ : syracuseStep 1621457 = 1216093) B1216093
theorem B638855 : Blo 283827 638855 := bstep (se 1 (by rfl) ⟨479141, by rfl⟩ : syracuseStep 638855 = 958283) B958283
theorem B639035 : Blo 283827 639035 := bstep (se 1 (by rfl) ⟨479276, by rfl⟩ : syracuseStep 639035 = 958553) B958553
theorem B639161 : Blo 283827 639161 := bstep (se 2 (by rfl) ⟨239685, by rfl⟩ : syracuseStep 639161 = 479371) B479371
theorem B540857 : Blo 283827 540857 := bstep (se 2 (by rfl) ⟨202821, by rfl⟩ : syracuseStep 540857 = 405643) B405643
theorem B409801 : Blo 283827 409801 := bstep (se 2 (by rfl) ⟨153675, by rfl⟩ : syracuseStep 409801 = 307351) B307351
theorem B639503 : Blo 283827 639503 := bstep (se 1 (by rfl) ⟨479627, by rfl⟩ : syracuseStep 639503 = 959255) B959255
theorem B639521 : Blo 283827 639521 := bstep (se 2 (by rfl) ⟨239820, by rfl⟩ : syracuseStep 639521 = 479641) B479641
theorem B5653111 : Blo 283827 5653111 := bstep (se 1 (by rfl) ⟨4239833, by rfl⟩ : syracuseStep 5653111 = 8479667) B8479667
theorem B4735705 : Blo 283827 4735705 := bstep (se 2 (by rfl) ⟨1775889, by rfl⟩ : syracuseStep 4735705 = 3551779) B3551779
theorem B639863 : Blo 283827 639863 := bstep (se 1 (by rfl) ⟨479897, by rfl⟩ : syracuseStep 639863 = 959795) B959795
theorem B967571 : Blo 283827 967571 := bstep (se 1 (by rfl) ⟨725678, by rfl⟩ : syracuseStep 967571 = 1451357) B1451357
theorem B640043 : Blo 283827 640043 := bstep (se 1 (by rfl) ⟨480032, by rfl⟩ : syracuseStep 640043 = 960065) B960065
theorem B1623347 : Blo 283827 1623347 := bstep (se 1 (by rfl) ⟨1217510, by rfl⟩ : syracuseStep 1623347 = 2435021) B2435021
theorem B345487 : Blo 283827 345487 := bstep (se 1 (by rfl) ⟨259115, by rfl⟩ : syracuseStep 345487 = 518231) B518231
theorem B640403 : Blo 283827 640403 := bstep (se 1 (by rfl) ⟨480302, by rfl⟩ : syracuseStep 640403 = 960605) B960605
theorem B640457 : Blo 283827 640457 := bstep (se 2 (by rfl) ⟨240171, by rfl⟩ : syracuseStep 640457 = 480343) B480343
theorem B641159 : Blo 283827 641159 := bstep (se 1 (by rfl) ⟨480869, by rfl⟩ : syracuseStep 641159 = 961739) B961739
theorem B542855 : Blo 283827 542855 := bstep (se 1 (by rfl) ⟨407141, by rfl⟩ : syracuseStep 542855 = 814283) B814283
theorem B575623 : Blo 283827 575623 := bstep (se 1 (by rfl) ⟨431717, by rfl⟩ : syracuseStep 575623 = 863435) B863435
theorem B411895 : Blo 283827 411895 := bstep (se 1 (by rfl) ⟨308921, by rfl⟩ : syracuseStep 411895 = 617843) B617843
theorem B968975 : Blo 283827 968975 := bstep (se 1 (by rfl) ⟨726731, by rfl⟩ : syracuseStep 968975 = 1453463) B1453463
theorem B1820987 : Blo 283827 1820987 := bstep (se 1 (by rfl) ⟨1365740, by rfl⟩ : syracuseStep 1820987 = 2731481) B2731481
theorem B641339 : Blo 283827 641339 := bstep (se 1 (by rfl) ⟨481004, by rfl⟩ : syracuseStep 641339 = 962009) B962009
theorem B641465 : Blo 283827 641465 := bstep (se 2 (by rfl) ⟨240549, by rfl⟩ : syracuseStep 641465 = 481099) B481099
theorem B3295673 : Blo 283827 3295673 := bstep (se 2 (by rfl) ⟨1235877, by rfl⟩ : syracuseStep 3295673 = 2471755) B2471755
theorem B969245 : Blo 283827 969245 := bstep (se 3 (by rfl) ⟨181733, by rfl⟩ : syracuseStep 969245 = 363467) B363467
theorem B2345539 : Blo 283827 2345539 := bstep (se 1 (by rfl) ⟨1759154, by rfl⟩ : syracuseStep 2345539 = 3518309) B3518309
theorem B1624805 : Blo 283827 1624805 := bstep (se 4 (by rfl) ⟨152325, by rfl⟩ : syracuseStep 1624805 = 304651) B304651
theorem B641807 : Blo 283827 641807 := bstep (se 1 (by rfl) ⟨481355, by rfl⟩ : syracuseStep 641807 = 962711) B962711
theorem B641825 : Blo 283827 641825 := bstep (se 2 (by rfl) ⟨240684, by rfl⟩ : syracuseStep 641825 = 481369) B481369
theorem B2739095 : Blo 283827 2739095 := bstep (se 1 (by rfl) ⟨2054321, by rfl⟩ : syracuseStep 2739095 = 4108643) B4108643
theorem B1100729 : Blo 283827 1100729 := bstep (se 2 (by rfl) ⟨412773, by rfl⟩ : syracuseStep 1100729 = 825547) B825547
theorem B412679 : Blo 283827 412679 := bstep (se 1 (by rfl) ⟨309509, by rfl⟩ : syracuseStep 412679 = 619019) B619019
theorem B642167 : Blo 283827 642167 := bstep (se 1 (by rfl) ⟨481625, by rfl⟩ : syracuseStep 642167 = 963251) B963251
theorem B642347 : Blo 283827 642347 := bstep (se 1 (by rfl) ⟨481760, by rfl⟩ : syracuseStep 642347 = 963521) B963521
theorem B642707 : Blo 283827 642707 := bstep (se 1 (by rfl) ⟨482030, by rfl⟩ : syracuseStep 642707 = 964061) B964061
theorem B642761 : Blo 283827 642761 := bstep (se 2 (by rfl) ⟨241035, by rfl⟩ : syracuseStep 642761 = 482071) B482071
theorem B544457 : Blo 283827 544457 := bstep (se 2 (by rfl) ⟨204171, by rfl⟩ : syracuseStep 544457 = 408343) B408343
theorem B2477873 : Blo 283827 2477873 := bstep (se 2 (by rfl) ⟨929202, by rfl⟩ : syracuseStep 2477873 = 1858405) B1858405
theorem B970649 : Blo 283827 970649 := bstep (se 2 (by rfl) ⟨363993, by rfl⟩ : syracuseStep 970649 = 727987) B727987
theorem B8212427 : Blo 283827 8212427 := bstep (se 1 (by rfl) ⟨6159320, by rfl⟩ : syracuseStep 8212427 = 12318641) B12318641
theorem B479351 : Blo 283827 479351 := bstep (se 1 (by rfl) ⟨359513, by rfl⟩ : syracuseStep 479351 = 719027) B719027
theorem B1495385 : Blo 283827 1495385 := bstep (se 2 (by rfl) ⟨560769, by rfl⟩ : syracuseStep 1495385 = 1121539) B1121539
theorem B643463 : Blo 283827 643463 := bstep (se 1 (by rfl) ⟨482597, by rfl⟩ : syracuseStep 643463 = 965195) B965195
theorem B3101075 : Blo 283827 3101075 := bstep (se 1 (by rfl) ⟨2325806, by rfl⟩ : syracuseStep 3101075 = 4651613) B4651613
theorem B872993 : Blo 283827 872993 := bstep (se 2 (by rfl) ⟨327372, by rfl⟩ : syracuseStep 872993 = 654745) B654745
theorem B479803 : Blo 283827 479803 := bstep (se 1 (by rfl) ⟨359852, by rfl⟩ : syracuseStep 479803 = 719705) B719705
theorem B643643 : Blo 283827 643643 := bstep (se 1 (by rfl) ⟨482732, by rfl⟩ : syracuseStep 643643 = 965465) B965465
theorem B971351 : Blo 283827 971351 := bstep (se 1 (by rfl) ⟨728513, by rfl⟩ : syracuseStep 971351 = 1457027) B1457027
theorem B643769 : Blo 283827 643769 := bstep (se 2 (by rfl) ⟨241413, by rfl⟩ : syracuseStep 643769 = 482827) B482827
theorem B7000769 : Blo 283827 7000769 := bstep (se 2 (by rfl) ⟨2625288, by rfl⟩ : syracuseStep 7000769 = 5250577) B5250577
theorem B479945 : Blo 283827 479945 := bstep (se 2 (by rfl) ⟨179979, by rfl⟩ : syracuseStep 479945 = 359959) B359959
theorem B578249 : Blo 283827 578249 := bstep (se 2 (by rfl) ⟨216843, by rfl⟩ : syracuseStep 578249 = 433687) B433687
theorem B5198681 : Blo 283827 5198681 := bstep (se 2 (by rfl) ⟨1949505, by rfl⟩ : syracuseStep 5198681 = 3899011) B3899011
theorem B644111 : Blo 283827 644111 := bstep (se 1 (by rfl) ⟨483083, by rfl⟩ : syracuseStep 644111 = 966167) B966167
theorem B644129 : Blo 283827 644129 := bstep (se 2 (by rfl) ⟨241548, by rfl⟩ : syracuseStep 644129 = 483097) B483097
theorem B283835 : Blo 283827 283835 := bstep (se 1 (by rfl) ⟨212876, by rfl⟩ : syracuseStep 283835 = 425753) B425753
theorem B283911 : Blo 283827 283911 := bstep (se 1 (by rfl) ⟨212933, by rfl⟩ : syracuseStep 283911 = 425867) B425867
theorem B283919 : Blo 283827 283919 := bstep (se 1 (by rfl) ⟨212939, by rfl⟩ : syracuseStep 283919 = 425879) B425879
theorem B4150561 : Blo 283827 4150561 := bstep (se 2 (by rfl) ⟨1556460, by rfl⟩ : syracuseStep 4150561 = 3112921) B3112921
theorem B1365281 : Blo 283827 1365281 := bstep (se 2 (by rfl) ⟨511980, by rfl⟩ : syracuseStep 1365281 = 1023961) B1023961
theorem B283963 : Blo 283827 283963 := bstep (se 1 (by rfl) ⟨212972, by rfl⟩ : syracuseStep 283963 = 425945) B425945
theorem B644471 : Blo 283827 644471 := bstep (se 1 (by rfl) ⟨483353, by rfl⟩ : syracuseStep 644471 = 966707) B966707
theorem B284039 : Blo 283827 284039 := bstep (se 1 (by rfl) ⟨213029, by rfl⟩ : syracuseStep 284039 = 426059) B426059
theorem B480647 : Blo 283827 480647 := bstep (se 1 (by rfl) ⟨360485, by rfl⟩ : syracuseStep 480647 = 720971) B720971
theorem B284047 : Blo 283827 284047 := bstep (se 1 (by rfl) ⟨213035, by rfl⟩ : syracuseStep 284047 = 426071) B426071
theorem B1398169 : Blo 283827 1398169 := bstep (se 2 (by rfl) ⟨524313, by rfl⟩ : syracuseStep 1398169 = 1048627) B1048627
theorem B5952953 : Blo 283827 5952953 := bstep (se 2 (by rfl) ⟨2232357, by rfl⟩ : syracuseStep 5952953 = 4464715) B4464715
theorem B284091 : Blo 283827 284091 := bstep (se 1 (by rfl) ⟨213068, by rfl⟩ : syracuseStep 284091 = 426137) B426137
theorem B808393 : Blo 283827 808393 := bstep (se 2 (by rfl) ⟨303147, by rfl⟩ : syracuseStep 808393 = 606295) B606295
theorem B873929 : Blo 283827 873929 := bstep (se 2 (by rfl) ⟨327723, by rfl⟩ : syracuseStep 873929 = 655447) B655447
theorem B284167 : Blo 283827 284167 := bstep (se 1 (by rfl) ⟨213125, by rfl⟩ : syracuseStep 284167 = 426251) B426251
theorem B284175 : Blo 283827 284175 := bstep (se 1 (by rfl) ⟨213131, by rfl⟩ : syracuseStep 284175 = 426263) B426263
theorem B2610731 : Blo 283827 2610731 := bstep (se 1 (by rfl) ⟨1958048, by rfl⟩ : syracuseStep 2610731 = 3916097) B3916097
theorem B644651 : Blo 283827 644651 := bstep (se 1 (by rfl) ⟨483488, by rfl⟩ : syracuseStep 644651 = 966977) B966977
theorem B284219 : Blo 283827 284219 := bstep (se 1 (by rfl) ⟨213164, by rfl⟩ : syracuseStep 284219 = 426329) B426329
theorem B284295 : Blo 283827 284295 := bstep (se 1 (by rfl) ⟨213221, by rfl⟩ : syracuseStep 284295 = 426443) B426443
theorem B284303 : Blo 283827 284303 := bstep (se 1 (by rfl) ⟨213227, by rfl⟩ : syracuseStep 284303 = 426455) B426455
theorem B284347 : Blo 283827 284347 := bstep (se 1 (by rfl) ⟨213260, by rfl⟩ : syracuseStep 284347 = 426521) B426521
theorem B284423 : Blo 283827 284423 := bstep (se 1 (by rfl) ⟨213317, by rfl⟩ : syracuseStep 284423 = 426635) B426635
theorem B284431 : Blo 283827 284431 := bstep (se 1 (by rfl) ⟨213323, by rfl⟩ : syracuseStep 284431 = 426647) B426647
theorem B284475 : Blo 283827 284475 := bstep (se 1 (by rfl) ⟨213356, by rfl⟩ : syracuseStep 284475 = 426713) B426713
theorem B612155 : Blo 283827 612155 := bstep (se 1 (by rfl) ⟨459116, by rfl⟩ : syracuseStep 612155 = 918233) B918233
theorem B284551 : Blo 283827 284551 := bstep (se 1 (by rfl) ⟨213413, by rfl⟩ : syracuseStep 284551 = 426827) B426827
theorem B1628039 : Blo 283827 1628039 := bstep (se 1 (by rfl) ⟨1221029, by rfl⟩ : syracuseStep 1628039 = 2442059) B2442059
theorem B284559 : Blo 283827 284559 := bstep (se 1 (by rfl) ⟨213419, by rfl⟩ : syracuseStep 284559 = 426839) B426839
theorem B645011 : Blo 283827 645011 := bstep (se 1 (by rfl) ⟨483758, by rfl⟩ : syracuseStep 645011 = 967517) B967517
theorem B284603 : Blo 283827 284603 := bstep (se 1 (by rfl) ⟨213452, by rfl⟩ : syracuseStep 284603 = 426905) B426905
theorem B645065 : Blo 283827 645065 := bstep (se 2 (by rfl) ⟨241899, by rfl⟩ : syracuseStep 645065 = 483799) B483799
theorem B284679 : Blo 283827 284679 := bstep (se 1 (by rfl) ⟨213509, by rfl⟩ : syracuseStep 284679 = 427019) B427019
theorem B284687 : Blo 283827 284687 := bstep (se 1 (by rfl) ⟨213515, by rfl⟩ : syracuseStep 284687 = 427031) B427031
theorem B481295 : Blo 283827 481295 := bstep (se 1 (by rfl) ⟨360971, by rfl⟩ : syracuseStep 481295 = 721943) B721943
theorem B284731 : Blo 283827 284731 := bstep (se 1 (by rfl) ⟨213548, by rfl⟩ : syracuseStep 284731 = 427097) B427097
theorem B1628221 : Blo 283827 1628221 := bstep (se 3 (by rfl) ⟨305291, by rfl⟩ : syracuseStep 1628221 = 610583) B610583
theorem B284807 : Blo 283827 284807 := bstep (se 1 (by rfl) ⟨213605, by rfl⟩ : syracuseStep 284807 = 427211) B427211
theorem B284815 : Blo 283827 284815 := bstep (se 1 (by rfl) ⟨213611, by rfl⟩ : syracuseStep 284815 = 427223) B427223
theorem B284859 : Blo 283827 284859 := bstep (se 1 (by rfl) ⟨213644, by rfl⟩ : syracuseStep 284859 = 427289) B427289
theorem B973001 : Blo 283827 973001 := bstep (se 2 (by rfl) ⟨364875, by rfl⟩ : syracuseStep 973001 = 729751) B729751
theorem B284935 : Blo 283827 284935 := bstep (se 1 (by rfl) ⟨213701, by rfl⟩ : syracuseStep 284935 = 427403) B427403
theorem B284943 : Blo 283827 284943 := bstep (se 1 (by rfl) ⟨213707, by rfl⟩ : syracuseStep 284943 = 427415) B427415
theorem B284987 : Blo 283827 284987 := bstep (se 1 (by rfl) ⟨213740, by rfl⟩ : syracuseStep 284987 = 427481) B427481
theorem B2971997 : Blo 283827 2971997 := bstep (se 3 (by rfl) ⟨557249, by rfl⟩ : syracuseStep 2971997 = 1114499) B1114499
theorem B285063 : Blo 283827 285063 := bstep (se 1 (by rfl) ⟨213797, by rfl⟩ : syracuseStep 285063 = 427595) B427595
theorem B285071 : Blo 283827 285071 := bstep (se 1 (by rfl) ⟨213803, by rfl⟩ : syracuseStep 285071 = 427607) B427607
theorem B285115 : Blo 283827 285115 := bstep (se 1 (by rfl) ⟨213836, by rfl⟩ : syracuseStep 285115 = 427673) B427673
theorem B285191 : Blo 283827 285191 := bstep (se 1 (by rfl) ⟨213893, by rfl⟩ : syracuseStep 285191 = 427787) B427787
theorem B285199 : Blo 283827 285199 := bstep (se 1 (by rfl) ⟨213899, by rfl⟩ : syracuseStep 285199 = 427799) B427799
theorem B481835 : Blo 283827 481835 := bstep (se 1 (by rfl) ⟨361376, by rfl⟩ : syracuseStep 481835 = 722753) B722753
theorem B514603 : Blo 283827 514603 := bstep (se 1 (by rfl) ⟨385952, by rfl⟩ : syracuseStep 514603 = 771905) B771905
theorem B285243 : Blo 283827 285243 := bstep (se 1 (by rfl) ⟨213932, by rfl⟩ : syracuseStep 285243 = 427865) B427865
theorem B285319 : Blo 283827 285319 := bstep (se 1 (by rfl) ⟨213989, by rfl⟩ : syracuseStep 285319 = 427979) B427979
theorem B645767 : Blo 283827 645767 := bstep (se 1 (by rfl) ⟨484325, by rfl⟩ : syracuseStep 645767 = 968651) B968651
theorem B285327 : Blo 283827 285327 := bstep (se 1 (by rfl) ⟨213995, by rfl⟩ : syracuseStep 285327 = 427991) B427991
theorem B285371 : Blo 283827 285371 := bstep (se 1 (by rfl) ⟨214028, by rfl⟩ : syracuseStep 285371 = 428057) B428057
theorem B285447 : Blo 283827 285447 := bstep (se 1 (by rfl) ⟨214085, by rfl⟩ : syracuseStep 285447 = 428171) B428171
theorem B285455 : Blo 283827 285455 := bstep (se 1 (by rfl) ⟨214091, by rfl⟩ : syracuseStep 285455 = 428183) B428183
theorem B2448143 : Blo 283827 2448143 := bstep (se 1 (by rfl) ⟨1836107, by rfl⟩ : syracuseStep 2448143 = 3672215) B3672215
theorem B5233423 : Blo 283827 5233423 := bstep (se 1 (by rfl) ⟨3925067, by rfl⟩ : syracuseStep 5233423 = 7850135) B7850135
theorem B3267377 : Blo 283827 3267377 := bstep (se 2 (by rfl) ⟨1225266, by rfl⟩ : syracuseStep 3267377 = 2450533) B2450533
theorem B2743091 : Blo 283827 2743091 := bstep (se 1 (by rfl) ⟨2057318, by rfl⟩ : syracuseStep 2743091 = 4114637) B4114637
theorem B285499 : Blo 283827 285499 := bstep (se 1 (by rfl) ⟨214124, by rfl⟩ : syracuseStep 285499 = 428249) B428249
theorem B645947 : Blo 283827 645947 := bstep (se 1 (by rfl) ⟨484460, by rfl⟩ : syracuseStep 645947 = 968921) B968921
theorem B285575 : Blo 283827 285575 := bstep (se 1 (by rfl) ⟨214181, by rfl⟩ : syracuseStep 285575 = 428363) B428363
theorem B285583 : Blo 283827 285583 := bstep (se 1 (by rfl) ⟨214187, by rfl⟩ : syracuseStep 285583 = 428375) B428375
theorem B482233 : Blo 283827 482233 := bstep (se 2 (by rfl) ⟨180837, by rfl⟩ : syracuseStep 482233 = 361675) B361675
theorem B646073 : Blo 283827 646073 := bstep (se 2 (by rfl) ⟨242277, by rfl⟩ : syracuseStep 646073 = 484555) B484555
theorem B285627 : Blo 283827 285627 := bstep (se 1 (by rfl) ⟨214220, by rfl⟩ : syracuseStep 285627 = 428441) B428441
theorem B384007 : Blo 283827 384007 := bstep (se 1 (by rfl) ⟨288005, by rfl⟩ : syracuseStep 384007 = 576011) B576011
theorem B285703 : Blo 283827 285703 := bstep (se 1 (by rfl) ⟨214277, by rfl⟩ : syracuseStep 285703 = 428555) B428555
theorem B285711 : Blo 283827 285711 := bstep (se 1 (by rfl) ⟨214283, by rfl⟩ : syracuseStep 285711 = 428567) B428567
theorem B285755 : Blo 283827 285755 := bstep (se 1 (by rfl) ⟨214316, by rfl⟩ : syracuseStep 285755 = 428633) B428633
theorem B285831 : Blo 283827 285831 := bstep (se 1 (by rfl) ⟨214373, by rfl⟩ : syracuseStep 285831 = 428747) B428747
theorem B285839 : Blo 283827 285839 := bstep (se 1 (by rfl) ⟨214379, by rfl⟩ : syracuseStep 285839 = 428759) B428759
theorem B285883 : Blo 283827 285883 := bstep (se 1 (by rfl) ⟨214412, by rfl⟩ : syracuseStep 285883 = 428825) B428825
theorem B285959 : Blo 283827 285959 := bstep (se 1 (by rfl) ⟨214469, by rfl⟩ : syracuseStep 285959 = 428939) B428939
theorem B285967 : Blo 283827 285967 := bstep (se 1 (by rfl) ⟨214475, by rfl⟩ : syracuseStep 285967 = 428951) B428951
theorem B646415 : Blo 283827 646415 := bstep (se 1 (by rfl) ⟨484811, by rfl⟩ : syracuseStep 646415 = 969623) B969623
theorem B646433 : Blo 283827 646433 := bstep (se 2 (by rfl) ⟨242412, by rfl⟩ : syracuseStep 646433 = 484825) B484825
theorem B286011 : Blo 283827 286011 := bstep (se 1 (by rfl) ⟨214508, by rfl⟩ : syracuseStep 286011 = 429017) B429017
theorem B1727833 : Blo 283827 1727833 := bstep (se 2 (by rfl) ⟨647937, by rfl⟩ : syracuseStep 1727833 = 1295875) B1295875
theorem B286087 : Blo 283827 286087 := bstep (se 1 (by rfl) ⟨214565, by rfl⟩ : syracuseStep 286087 = 429131) B429131
theorem B286095 : Blo 283827 286095 := bstep (se 1 (by rfl) ⟨214571, by rfl⟩ : syracuseStep 286095 = 429143) B429143
theorem B941465 : Blo 283827 941465 := bstep (se 2 (by rfl) ⟨353049, by rfl⟩ : syracuseStep 941465 = 706099) B706099
theorem B6643129 : Blo 283827 6643129 := bstep (se 2 (by rfl) ⟨2491173, by rfl⟩ : syracuseStep 6643129 = 4982347) B4982347
theorem B286139 : Blo 283827 286139 := bstep (se 1 (by rfl) ⟨214604, by rfl⟩ : syracuseStep 286139 = 429209) B429209
theorem B286215 : Blo 283827 286215 := bstep (se 1 (by rfl) ⟨214661, by rfl⟩ : syracuseStep 286215 = 429323) B429323
theorem B286223 : Blo 283827 286223 := bstep (se 1 (by rfl) ⟨214667, by rfl⟩ : syracuseStep 286223 = 429335) B429335
theorem B286267 : Blo 283827 286267 := bstep (se 1 (by rfl) ⟨214700, by rfl⟩ : syracuseStep 286267 = 429401) B429401
theorem B810557 : Blo 283827 810557 := bstep (se 3 (by rfl) ⟨151979, by rfl⟩ : syracuseStep 810557 = 303959) B303959
theorem B482935 : Blo 283827 482935 := bstep (se 1 (by rfl) ⟨362201, by rfl⟩ : syracuseStep 482935 = 724403) B724403
theorem B646775 : Blo 283827 646775 := bstep (se 1 (by rfl) ⟨485081, by rfl⟩ : syracuseStep 646775 = 970163) B970163
theorem B286343 : Blo 283827 286343 := bstep (se 1 (by rfl) ⟨214757, by rfl⟩ : syracuseStep 286343 = 429515) B429515
theorem B286351 : Blo 283827 286351 := bstep (se 1 (by rfl) ⟨214763, by rfl⟩ : syracuseStep 286351 = 429527) B429527
theorem B286395 : Blo 283827 286395 := bstep (se 1 (by rfl) ⟨214796, by rfl⟩ : syracuseStep 286395 = 429593) B429593
theorem B1629953 : Blo 283827 1629953 := bstep (se 2 (by rfl) ⟨611232, by rfl⟩ : syracuseStep 1629953 = 1222465) B1222465
theorem B286471 : Blo 283827 286471 := bstep (se 1 (by rfl) ⟨214853, by rfl⟩ : syracuseStep 286471 = 429707) B429707
theorem B286479 : Blo 283827 286479 := bstep (se 1 (by rfl) ⟨214859, by rfl⟩ : syracuseStep 286479 = 429719) B429719
theorem B810785 : Blo 283827 810785 := bstep (se 2 (by rfl) ⟨304044, by rfl⟩ : syracuseStep 810785 = 608089) B608089
theorem B646955 : Blo 283827 646955 := bstep (se 1 (by rfl) ⟨485216, by rfl⟩ : syracuseStep 646955 = 970433) B970433
theorem B483131 : Blo 283827 483131 := bstep (se 1 (by rfl) ⟨362348, by rfl⟩ : syracuseStep 483131 = 724697) B724697
theorem B286523 : Blo 283827 286523 := bstep (se 1 (by rfl) ⟨214892, by rfl⟩ : syracuseStep 286523 = 429785) B429785
theorem B286599 : Blo 283827 286599 := bstep (se 1 (by rfl) ⟨214949, by rfl⟩ : syracuseStep 286599 = 429899) B429899
theorem B286607 : Blo 283827 286607 := bstep (se 1 (by rfl) ⟨214955, by rfl⟩ : syracuseStep 286607 = 429911) B429911
theorem B286651 : Blo 283827 286651 := bstep (se 1 (by rfl) ⟨214988, by rfl⟩ : syracuseStep 286651 = 429977) B429977
theorem B319495 : Blo 283827 319495 := bstep (se 1 (by rfl) ⟨239621, by rfl⟩ : syracuseStep 319495 = 479243) B479243
theorem B286727 : Blo 283827 286727 := bstep (se 1 (by rfl) ⟨215045, by rfl⟩ : syracuseStep 286727 = 430091) B430091
theorem B286735 : Blo 283827 286735 := bstep (se 1 (by rfl) ⟨215051, by rfl⟩ : syracuseStep 286735 = 430103) B430103
theorem B286779 : Blo 283827 286779 := bstep (se 1 (by rfl) ⟨215084, by rfl⟩ : syracuseStep 286779 = 430169) B430169
theorem B811127 : Blo 283827 811127 := bstep (se 1 (by rfl) ⟨608345, by rfl⟩ : syracuseStep 811127 = 1216691) B1216691
theorem B286855 : Blo 283827 286855 := bstep (se 1 (by rfl) ⟨215141, by rfl⟩ : syracuseStep 286855 = 430283) B430283
theorem B286863 : Blo 283827 286863 := bstep (se 1 (by rfl) ⟨215147, by rfl⟩ : syracuseStep 286863 = 430295) B430295
theorem B647315 : Blo 283827 647315 := bstep (se 1 (by rfl) ⟨485486, by rfl⟩ : syracuseStep 647315 = 970973) B970973
theorem B319675 : Blo 283827 319675 := bstep (se 1 (by rfl) ⟨239756, by rfl⟩ : syracuseStep 319675 = 479513) B479513
theorem B286907 : Blo 283827 286907 := bstep (se 1 (by rfl) ⟨215180, by rfl⟩ : syracuseStep 286907 = 430361) B430361
theorem B483529 : Blo 283827 483529 := bstep (se 2 (by rfl) ⟨181323, by rfl⟩ : syracuseStep 483529 = 362647) B362647
theorem B647369 : Blo 283827 647369 := bstep (se 2 (by rfl) ⟨242763, by rfl⟩ : syracuseStep 647369 = 485527) B485527
theorem B286983 : Blo 283827 286983 := bstep (se 1 (by rfl) ⟨215237, by rfl⟩ : syracuseStep 286983 = 430475) B430475
theorem B286991 : Blo 283827 286991 := bstep (se 1 (by rfl) ⟨215243, by rfl⟩ : syracuseStep 286991 = 430487) B430487
theorem B516385 : Blo 283827 516385 := bstep (se 2 (by rfl) ⟨193644, by rfl⟩ : syracuseStep 516385 = 387289) B387289
theorem B287035 : Blo 283827 287035 := bstep (se 1 (by rfl) ⟨215276, by rfl⟩ : syracuseStep 287035 = 430553) B430553
theorem B287111 : Blo 283827 287111 := bstep (se 1 (by rfl) ⟨215333, by rfl⟩ : syracuseStep 287111 = 430667) B430667
theorem B287119 : Blo 283827 287119 := bstep (se 1 (by rfl) ⟨215339, by rfl⟩ : syracuseStep 287119 = 430679) B430679
theorem B287163 : Blo 283827 287163 := bstep (se 1 (by rfl) ⟨215372, by rfl⟩ : syracuseStep 287163 = 430745) B430745
theorem B287239 : Blo 283827 287239 := bstep (se 1 (by rfl) ⟨215429, by rfl⟩ : syracuseStep 287239 = 430859) B430859
theorem B287247 : Blo 283827 287247 := bstep (se 1 (by rfl) ⟨215435, by rfl⟩ : syracuseStep 287247 = 430871) B430871
theorem B287291 : Blo 283827 287291 := bstep (se 1 (by rfl) ⟨215468, by rfl⟩ : syracuseStep 287291 = 430937) B430937
theorem B287367 : Blo 283827 287367 := bstep (se 1 (by rfl) ⟨215525, by rfl⟩ : syracuseStep 287367 = 431051) B431051
theorem B320143 : Blo 283827 320143 := bstep (se 1 (by rfl) ⟨240107, by rfl⟩ : syracuseStep 320143 = 480215) B480215
theorem B287375 : Blo 283827 287375 := bstep (se 1 (by rfl) ⟨215531, by rfl⟩ : syracuseStep 287375 = 431063) B431063
theorem B287419 : Blo 283827 287419 := bstep (se 1 (by rfl) ⟨215564, by rfl⟩ : syracuseStep 287419 = 431129) B431129
theorem B287495 : Blo 283827 287495 := bstep (se 1 (by rfl) ⟨215621, by rfl⟩ : syracuseStep 287495 = 431243) B431243
theorem B287503 : Blo 283827 287503 := bstep (se 1 (by rfl) ⟨215627, by rfl⟩ : syracuseStep 287503 = 431255) B431255
theorem B287547 : Blo 283827 287547 := bstep (se 1 (by rfl) ⟨215660, by rfl⟩ : syracuseStep 287547 = 431321) B431321
theorem B484231 : Blo 283827 484231 := bstep (se 1 (by rfl) ⟨363173, by rfl⟩ : syracuseStep 484231 = 726347) B726347
theorem B287623 : Blo 283827 287623 := bstep (se 1 (by rfl) ⟨215717, by rfl⟩ : syracuseStep 287623 = 431435) B431435
theorem B287631 : Blo 283827 287631 := bstep (se 1 (by rfl) ⟨215723, by rfl⟩ : syracuseStep 287631 = 431447) B431447
theorem B3236759 : Blo 283827 3236759 := bstep (se 1 (by rfl) ⟨2427569, by rfl⟩ : syracuseStep 3236759 = 4855139) B4855139
theorem B287675 : Blo 283827 287675 := bstep (se 1 (by rfl) ⟨215756, by rfl⟩ : syracuseStep 287675 = 431513) B431513
theorem B386039 : Blo 283827 386039 := bstep (se 1 (by rfl) ⟨289529, by rfl⟩ : syracuseStep 386039 = 579059) B579059
theorem B287751 : Blo 283827 287751 := bstep (se 1 (by rfl) ⟨215813, by rfl⟩ : syracuseStep 287751 = 431627) B431627
theorem B287759 : Blo 283827 287759 := bstep (se 1 (by rfl) ⟨215819, by rfl⟩ : syracuseStep 287759 = 431639) B431639
theorem B287803 : Blo 283827 287803 := bstep (se 1 (by rfl) ⟨215852, by rfl⟩ : syracuseStep 287803 = 431705) B431705
theorem B320647 : Blo 283827 320647 := bstep (se 1 (by rfl) ⟨240485, by rfl⟩ : syracuseStep 320647 = 480971) B480971
theorem B320827 : Blo 283827 320827 := bstep (se 1 (by rfl) ⟨240620, by rfl⟩ : syracuseStep 320827 = 481241) B481241
theorem B1828241 : Blo 283827 1828241 := bstep (se 2 (by rfl) ⟨685590, by rfl⟩ : syracuseStep 1828241 = 1371181) B1371181
theorem B484879 : Blo 283827 484879 := bstep (se 1 (by rfl) ⟨363659, by rfl⟩ : syracuseStep 484879 = 727319) B727319
theorem B648905 : Blo 283827 648905 := bstep (se 2 (by rfl) ⟨243339, by rfl⟩ : syracuseStep 648905 = 486679) B486679
theorem B1173263 : Blo 283827 1173263 := bstep (se 1 (by rfl) ⟨879947, by rfl⟩ : syracuseStep 1173263 = 1759895) B1759895
theorem B321295 : Blo 283827 321295 := bstep (se 1 (by rfl) ⟨240971, by rfl⟩ : syracuseStep 321295 = 481943) B481943
theorem B386959 : Blo 283827 386959 := bstep (se 1 (by rfl) ⟨290219, by rfl⟩ : syracuseStep 386959 = 580439) B580439
theorem B485419 : Blo 283827 485419 := bstep (se 1 (by rfl) ⟨364064, by rfl⟩ : syracuseStep 485419 = 728129) B728129
theorem B1959997 : Blo 283827 1959997 := bstep (se 3 (by rfl) ⟨367499, by rfl⟩ : syracuseStep 1959997 = 734999) B734999
theorem B6973613 : Blo 283827 6973613 := bstep (se 3 (by rfl) ⟨1307552, by rfl⟩ : syracuseStep 6973613 = 2615105) B2615105
theorem B485561 : Blo 283827 485561 := bstep (se 2 (by rfl) ⟨182085, by rfl⟩ : syracuseStep 485561 = 364171) B364171
theorem B1566977 : Blo 283827 1566977 := bstep (se 2 (by rfl) ⟨587616, by rfl⟩ : syracuseStep 1566977 = 1175233) B1175233
theorem B321799 : Blo 283827 321799 := bstep (se 1 (by rfl) ⟨241349, by rfl⟩ : syracuseStep 321799 = 482699) B482699
theorem B321979 : Blo 283827 321979 := bstep (se 1 (by rfl) ⟨241484, by rfl⟩ : syracuseStep 321979 = 482969) B482969
theorem B813655 : Blo 283827 813655 := bstep (se 1 (by rfl) ⟨610241, by rfl⟩ : syracuseStep 813655 = 1220483) B1220483
theorem B813883 : Blo 283827 813883 := bstep (se 1 (by rfl) ⟨610412, by rfl⟩ : syracuseStep 813883 = 1220825) B1220825
theorem B1370969 : Blo 283827 1370969 := bstep (se 2 (by rfl) ⟨514113, by rfl⟩ : syracuseStep 1370969 = 1028227) B1028227
theorem B322447 : Blo 283827 322447 := bstep (se 1 (by rfl) ⟨241835, by rfl⟩ : syracuseStep 322447 = 483671) B483671
theorem B912313 : Blo 283827 912313 := bstep (se 2 (by rfl) ⟨342117, by rfl⟩ : syracuseStep 912313 = 684235) B684235
theorem B814009 : Blo 283827 814009 := bstep (se 2 (by rfl) ⟨305253, by rfl⟩ : syracuseStep 814009 = 610507) B610507
theorem B650273 : Blo 283827 650273 := bstep (se 2 (by rfl) ⟨243852, by rfl⟩ : syracuseStep 650273 = 487705) B487705
theorem B1731899 : Blo 283827 1731899 := bstep (se 1 (by rfl) ⟨1298924, by rfl⟩ : syracuseStep 1731899 = 2597849) B2597849
theorem B322951 : Blo 283827 322951 := bstep (se 1 (by rfl) ⟨242213, by rfl⟩ : syracuseStep 322951 = 484427) B484427
theorem B1535377 : Blo 283827 1535377 := bstep (se 2 (by rfl) ⟨575766, by rfl⟩ : syracuseStep 1535377 = 1151533) B1151533
theorem B1371659 : Blo 283827 1371659 := bstep (se 1 (by rfl) ⟨1028744, by rfl⟩ : syracuseStep 1371659 = 2057489) B2057489
theorem B323131 : Blo 283827 323131 := bstep (se 1 (by rfl) ⟨242348, by rfl⟩ : syracuseStep 323131 = 484697) B484697
theorem B1437587 : Blo 283827 1437587 := bstep (se 1 (by rfl) ⟨1078190, by rfl⟩ : syracuseStep 1437587 = 2156381) B2156381
theorem B683977 : Blo 283827 683977 := bstep (se 2 (by rfl) ⟨256491, by rfl⟩ : syracuseStep 683977 = 512983) B512983
theorem B323599 : Blo 283827 323599 := bstep (se 1 (by rfl) ⟨242699, by rfl⟩ : syracuseStep 323599 = 485399) B485399
theorem B1634327 : Blo 283827 1634327 := bstep (se 1 (by rfl) ⟨1225745, by rfl⟩ : syracuseStep 1634327 = 2451491) B2451491
theorem B2715709 : Blo 283827 2715709 := bstep (se 3 (by rfl) ⟨509195, by rfl⟩ : syracuseStep 2715709 = 1018391) B1018391
theorem B2159297 : Blo 283827 2159297 := bstep (se 2 (by rfl) ⟨809736, by rfl⟩ : syracuseStep 2159297 = 1619473) B1619473
theorem B815933 : Blo 283827 815933 := bstep (se 3 (by rfl) ⟨152987, by rfl⟩ : syracuseStep 815933 = 305975) B305975
theorem B3241133 : Blo 283827 3241133 := bstep (se 3 (by rfl) ⟨607712, by rfl⟩ : syracuseStep 3241133 = 1215425) B1215425
theorem B20903345 : Blo 283827 20903345 := bstep (se 2 (by rfl) ⟨7838754, by rfl⟩ : syracuseStep 20903345 = 15677509) B15677509
theorem B1373699 : Blo 283827 1373699 := bstep (se 1 (by rfl) ⟨1030274, by rfl⟩ : syracuseStep 1373699 = 2060549) B2060549
theorem B1079041 : Blo 283827 1079041 := bstep (se 2 (by rfl) ⟨404640, by rfl⟩ : syracuseStep 1079041 = 809281) B809281
theorem B816925 : Blo 283827 816925 := bstep (se 3 (by rfl) ⟨153173, by rfl⟩ : syracuseStep 816925 = 306347) B306347
theorem B2783243 : Blo 283827 2783243 := bstep (se 1 (by rfl) ⟨2087432, by rfl⟩ : syracuseStep 2783243 = 4174865) B4174865
theorem B686369 : Blo 283827 686369 := bstep (se 2 (by rfl) ⟨257388, by rfl⟩ : syracuseStep 686369 = 514777) B514777
theorem B719219 : Blo 283827 719219 := bstep (se 1 (by rfl) ⟨539414, by rfl⟩ : syracuseStep 719219 = 1078829) B1078829
theorem B719239 : Blo 283827 719239 := bstep (se 1 (by rfl) ⟨539429, by rfl⟩ : syracuseStep 719239 = 1078859) B1078859
theorem B850447 : Blo 283827 850447 := bstep (se 1 (by rfl) ⟨637835, by rfl⟩ : syracuseStep 850447 = 1275671) B1275671
theorem B1538621 : Blo 283827 1538621 := bstep (se 3 (by rfl) ⟨288491, by rfl⟩ : syracuseStep 1538621 = 576983) B576983
theorem B719513 : Blo 283827 719513 := bstep (se 2 (by rfl) ⟨269817, by rfl⟩ : syracuseStep 719513 = 539635) B539635
theorem B719675 : Blo 283827 719675 := bstep (se 1 (by rfl) ⟨539756, by rfl⟩ : syracuseStep 719675 = 1079513) B1079513
theorem B5503859 : Blo 283827 5503859 := bstep (se 1 (by rfl) ⟨4127894, by rfl⟩ : syracuseStep 5503859 = 8255789) B8255789
theorem B359311 : Blo 283827 359311 := bstep (se 1 (by rfl) ⟨269483, by rfl⟩ : syracuseStep 359311 = 538967) B538967
theorem B1440665 : Blo 283827 1440665 := bstep (se 2 (by rfl) ⟨540249, by rfl⟩ : syracuseStep 1440665 = 1080499) B1080499
theorem B719887 : Blo 283827 719887 := bstep (se 1 (by rfl) ⟨539915, by rfl⟩ : syracuseStep 719887 = 1079831) B1079831
theorem B621611 : Blo 283827 621611 := bstep (se 1 (by rfl) ⟨466208, by rfl⟩ : syracuseStep 621611 = 932417) B932417
theorem B1637495 : Blo 283827 1637495 := bstep (se 1 (by rfl) ⟨1228121, by rfl⟩ : syracuseStep 1637495 = 2456243) B2456243
theorem B720161 : Blo 283827 720161 := bstep (se 2 (by rfl) ⟨270060, by rfl⟩ : syracuseStep 720161 = 540121) B540121
theorem B2456891 : Blo 283827 2456891 := bstep (se 1 (by rfl) ⟨1842668, by rfl⟩ : syracuseStep 2456891 = 3685337) B3685337
theorem B3276125 : Blo 283827 3276125 := bstep (se 3 (by rfl) ⟨614273, by rfl⟩ : syracuseStep 3276125 = 1228547) B1228547
theorem B917003 : Blo 283827 917003 := bstep (se 1 (by rfl) ⟨687752, by rfl⟩ : syracuseStep 917003 = 1375505) B1375505
theorem B360055 : Blo 283827 360055 := bstep (se 1 (by rfl) ⟨270041, by rfl⟩ : syracuseStep 360055 = 540083) B540083
theorem B818873 : Blo 283827 818873 := bstep (se 2 (by rfl) ⟨307077, by rfl⟩ : syracuseStep 818873 = 614155) B614155
theorem B425771 : Blo 283827 425771 := bstep (se 1 (by rfl) ⟨319328, by rfl⟩ : syracuseStep 425771 = 638657) B638657
theorem B622379 : Blo 283827 622379 := bstep (se 1 (by rfl) ⟨466784, by rfl⟩ : syracuseStep 622379 = 933569) B933569
theorem B2064179 : Blo 283827 2064179 := bstep (se 1 (by rfl) ⟨1548134, by rfl⟩ : syracuseStep 2064179 = 3096269) B3096269
theorem B425801 : Blo 283827 425801 := bstep (se 2 (by rfl) ⟨159675, by rfl⟩ : syracuseStep 425801 = 319351) B319351
theorem B917401 : Blo 283827 917401 := bstep (se 2 (by rfl) ⟨344025, by rfl⟩ : syracuseStep 917401 = 688051) B688051
theorem B425915 : Blo 283827 425915 := bstep (se 1 (by rfl) ⟨319436, by rfl⟩ : syracuseStep 425915 = 638873) B638873
theorem B360379 : Blo 283827 360379 := bstep (se 1 (by rfl) ⟨270284, by rfl⟩ : syracuseStep 360379 = 540569) B540569
theorem B425975 : Blo 283827 425975 := bstep (se 1 (by rfl) ⟨319481, by rfl⟩ : syracuseStep 425975 = 638963) B638963
theorem B1441799 : Blo 283827 1441799 := bstep (se 1 (by rfl) ⟨1081349, by rfl⟩ : syracuseStep 1441799 = 2162699) B2162699
theorem B425993 : Blo 283827 425993 := bstep (se 2 (by rfl) ⟨159747, by rfl⟩ : syracuseStep 425993 = 319495) B319495
theorem B426023 : Blo 283827 426023 := bstep (se 1 (by rfl) ⟨319517, by rfl⟩ : syracuseStep 426023 = 639035) B639035
theorem B426107 : Blo 283827 426107 := bstep (se 1 (by rfl) ⟨319580, by rfl⟩ : syracuseStep 426107 = 639161) B639161
theorem B426233 : Blo 283827 426233 := bstep (se 2 (by rfl) ⟨159837, by rfl⟩ : syracuseStep 426233 = 319675) B319675
theorem B426335 : Blo 283827 426335 := bstep (se 1 (by rfl) ⟨319751, by rfl⟩ : syracuseStep 426335 = 639503) B639503
theorem B426347 : Blo 283827 426347 := bstep (se 1 (by rfl) ⟨319760, by rfl⟩ : syracuseStep 426347 = 639521) B639521
theorem B688513 : Blo 283827 688513 := bstep (se 2 (by rfl) ⟨258192, by rfl⟩ : syracuseStep 688513 = 516385) B516385
theorem B721295 : Blo 283827 721295 := bstep (se 1 (by rfl) ⟨540971, by rfl⟩ : syracuseStep 721295 = 1081943) B1081943
theorem B1442285 : Blo 283827 1442285 := bstep (se 3 (by rfl) ⟨270428, by rfl⟩ : syracuseStep 1442285 = 540857) B540857
theorem B426575 : Blo 283827 426575 := bstep (se 1 (by rfl) ⟨319931, by rfl⟩ : syracuseStep 426575 = 639863) B639863
theorem B426695 : Blo 283827 426695 := bstep (se 1 (by rfl) ⟨320021, by rfl⟩ : syracuseStep 426695 = 640043) B640043
theorem B721619 : Blo 283827 721619 := bstep (se 1 (by rfl) ⟨541214, by rfl⟩ : syracuseStep 721619 = 1082429) B1082429
theorem B7537481 : Blo 283827 7537481 := bstep (se 2 (by rfl) ⟨2826555, by rfl⟩ : syracuseStep 7537481 = 5653111) B5653111
theorem B426857 : Blo 283827 426857 := bstep (se 2 (by rfl) ⟨160071, by rfl⟩ : syracuseStep 426857 = 320143) B320143
theorem B1082231 : Blo 283827 1082231 := bstep (se 1 (by rfl) ⟨811673, by rfl⟩ : syracuseStep 1082231 = 1623347) B1623347
theorem B426935 : Blo 283827 426935 := bstep (se 1 (by rfl) ⟨320201, by rfl⟩ : syracuseStep 426935 = 640403) B640403
theorem B426971 : Blo 283827 426971 := bstep (se 1 (by rfl) ⟨320228, by rfl⟩ : syracuseStep 426971 = 640457) B640457
theorem B918643 : Blo 283827 918643 := bstep (se 1 (by rfl) ⟨688982, by rfl⟩ : syracuseStep 918643 = 1377965) B1377965
theorem B3671243 : Blo 283827 3671243 := bstep (se 1 (by rfl) ⟨2753432, by rfl⟩ : syracuseStep 3671243 = 5506865) B5506865
theorem B1443095 : Blo 283827 1443095 := bstep (se 1 (by rfl) ⟨1082321, by rfl⟩ : syracuseStep 1443095 = 2164643) B2164643
theorem B427439 : Blo 283827 427439 := bstep (se 1 (by rfl) ⟨320579, by rfl⟩ : syracuseStep 427439 = 641159) B641159
theorem B361903 : Blo 283827 361903 := bstep (se 1 (by rfl) ⟨271427, by rfl⟩ : syracuseStep 361903 = 542855) B542855
theorem B427529 : Blo 283827 427529 := bstep (se 2 (by rfl) ⟨160323, by rfl⟩ : syracuseStep 427529 = 320647) B320647
theorem B1213991 : Blo 283827 1213991 := bstep (se 1 (by rfl) ⟨910493, by rfl⟩ : syracuseStep 1213991 = 1820987) B1820987
theorem B427559 : Blo 283827 427559 := bstep (se 1 (by rfl) ⟨320669, by rfl⟩ : syracuseStep 427559 = 641339) B641339
theorem B427643 : Blo 283827 427643 := bstep (se 1 (by rfl) ⟨320732, by rfl⟩ : syracuseStep 427643 = 641465) B641465
theorem B2197115 : Blo 283827 2197115 := bstep (se 1 (by rfl) ⟨1647836, by rfl⟩ : syracuseStep 2197115 = 3295673) B3295673
theorem B427769 : Blo 283827 427769 := bstep (se 2 (by rfl) ⟨160413, by rfl⟩ : syracuseStep 427769 = 320827) B320827
theorem B1083203 : Blo 283827 1083203 := bstep (se 1 (by rfl) ⟨812402, by rfl⟩ : syracuseStep 1083203 = 1624805) B1624805
theorem B427871 : Blo 283827 427871 := bstep (se 1 (by rfl) ⟨320903, by rfl⟩ : syracuseStep 427871 = 641807) B641807
theorem B722783 : Blo 283827 722783 := bstep (se 1 (by rfl) ⟨542087, by rfl⟩ : syracuseStep 722783 = 1084175) B1084175
theorem B460649 : Blo 283827 460649 := bstep (se 2 (by rfl) ⟨172743, by rfl⟩ : syracuseStep 460649 = 345487) B345487
theorem B427883 : Blo 283827 427883 := bstep (se 1 (by rfl) ⟨320912, by rfl⟩ : syracuseStep 427883 = 641825) B641825
theorem B8259479 : Blo 283827 8259479 := bstep (se 1 (by rfl) ⟨6194609, by rfl⟩ : syracuseStep 8259479 = 12389219) B12389219
theorem B428111 : Blo 283827 428111 := bstep (se 1 (by rfl) ⟨321083, by rfl⟩ : syracuseStep 428111 = 642167) B642167
theorem B428231 : Blo 283827 428231 := bstep (se 1 (by rfl) ⟨321173, by rfl⟩ : syracuseStep 428231 = 642347) B642347
theorem B428393 : Blo 283827 428393 := bstep (se 2 (by rfl) ⟨160647, by rfl⟩ : syracuseStep 428393 = 321295) B321295
theorem B428471 : Blo 283827 428471 := bstep (se 1 (by rfl) ⟨321353, by rfl⟩ : syracuseStep 428471 = 642707) B642707
theorem B428507 : Blo 283827 428507 := bstep (se 1 (by rfl) ⟨321380, by rfl⟩ : syracuseStep 428507 = 642761) B642761
theorem B362971 : Blo 283827 362971 := bstep (se 1 (by rfl) ⟨272228, by rfl⟩ : syracuseStep 362971 = 544457) B544457
theorem B5474951 : Blo 283827 5474951 := bstep (se 1 (by rfl) ⟨4106213, by rfl⟩ : syracuseStep 5474951 = 8212427) B8212427
theorem B16714421 : Blo 283827 16714421 := bstep (se 5 (by rfl) ⟨783488, by rfl⟩ : syracuseStep 16714421 = 1566977) B1566977
theorem B1444715 : Blo 283827 1444715 := bstep (se 1 (by rfl) ⟨1083536, by rfl⟩ : syracuseStep 1444715 = 2167073) B2167073
theorem B723887 : Blo 283827 723887 := bstep (se 1 (by rfl) ⟨542915, by rfl⟩ : syracuseStep 723887 = 1085831) B1085831
theorem B428975 : Blo 283827 428975 := bstep (se 1 (by rfl) ⟨321731, by rfl⟩ : syracuseStep 428975 = 643463) B643463
theorem B2067383 : Blo 283827 2067383 := bstep (se 1 (by rfl) ⟨1550537, by rfl⟩ : syracuseStep 2067383 = 3101075) B3101075
theorem B429065 : Blo 283827 429065 := bstep (se 2 (by rfl) ⟨160899, by rfl⟩ : syracuseStep 429065 = 321799) B321799
theorem B429095 : Blo 283827 429095 := bstep (se 1 (by rfl) ⟨321821, by rfl⟩ : syracuseStep 429095 = 643643) B643643
theorem B1838159 : Blo 283827 1838159 := bstep (se 1 (by rfl) ⟨1378619, by rfl⟩ : syracuseStep 1838159 = 2757239) B2757239
theorem B429179 : Blo 283827 429179 := bstep (se 1 (by rfl) ⟨321884, by rfl⟩ : syracuseStep 429179 = 643769) B643769
theorem B462071 : Blo 283827 462071 := bstep (se 1 (by rfl) ⟨346553, by rfl⟩ : syracuseStep 462071 = 693107) B693107
theorem B429305 : Blo 283827 429305 := bstep (se 2 (by rfl) ⟨160989, by rfl⟩ : syracuseStep 429305 = 321979) B321979
theorem B429407 : Blo 283827 429407 := bstep (se 1 (by rfl) ⟨322055, by rfl⟩ : syracuseStep 429407 = 644111) B644111
theorem B429419 : Blo 283827 429419 := bstep (se 1 (by rfl) ⟨322064, by rfl⟩ : syracuseStep 429419 = 644129) B644129
theorem B1084873 : Blo 283827 1084873 := bstep (se 2 (by rfl) ⟨406827, by rfl⟩ : syracuseStep 1084873 = 813655) B813655
theorem B1445363 : Blo 283827 1445363 := bstep (se 1 (by rfl) ⟨1084022, by rfl⟩ : syracuseStep 1445363 = 2168045) B2168045
theorem B429647 : Blo 283827 429647 := bstep (se 1 (by rfl) ⟨322235, by rfl⟩ : syracuseStep 429647 = 644471) B644471
theorem B3968635 : Blo 283827 3968635 := bstep (se 1 (by rfl) ⟨2976476, by rfl⟩ : syracuseStep 3968635 = 5952953) B5952953
theorem B1379963 : Blo 283827 1379963 := bstep (se 1 (by rfl) ⟨1034972, by rfl⟩ : syracuseStep 1379963 = 2069945) B2069945
theorem B2330245 : Blo 283827 2330245 := bstep (se 4 (by rfl) ⟨218460, by rfl⟩ : syracuseStep 2330245 = 436921) B436921
theorem B1740487 : Blo 283827 1740487 := bstep (se 1 (by rfl) ⟨1305365, by rfl⟩ : syracuseStep 1740487 = 2610731) B2610731
theorem B429767 : Blo 283827 429767 := bstep (se 1 (by rfl) ⟨322325, by rfl⟩ : syracuseStep 429767 = 644651) B644651
theorem B1085177 : Blo 283827 1085177 := bstep (se 2 (by rfl) ⟨406941, by rfl⟩ : syracuseStep 1085177 = 813883) B813883
theorem B2166587 : Blo 283827 2166587 := bstep (se 1 (by rfl) ⟨1624940, by rfl⟩ : syracuseStep 2166587 = 3249881) B3249881
theorem B429929 : Blo 283827 429929 := bstep (se 2 (by rfl) ⟨161223, by rfl⟩ : syracuseStep 429929 = 322447) B322447
theorem B2330477 : Blo 283827 2330477 := bstep (se 3 (by rfl) ⟨436964, by rfl⟩ : syracuseStep 2330477 = 873929) B873929
theorem B1216417 : Blo 283827 1216417 := bstep (se 2 (by rfl) ⟨456156, by rfl⟩ : syracuseStep 1216417 = 912313) B912313
theorem B1085345 : Blo 283827 1085345 := bstep (se 2 (by rfl) ⟨407004, by rfl⟩ : syracuseStep 1085345 = 814009) B814009
theorem B1085359 : Blo 283827 1085359 := bstep (se 1 (by rfl) ⟨814019, by rfl⟩ : syracuseStep 1085359 = 1628039) B1628039
theorem B430007 : Blo 283827 430007 := bstep (se 1 (by rfl) ⟨322505, by rfl⟩ : syracuseStep 430007 = 645011) B645011
theorem B430043 : Blo 283827 430043 := bstep (se 1 (by rfl) ⟨322532, by rfl⟩ : syracuseStep 430043 = 645065) B645065
theorem B2068537 : Blo 283827 2068537 := bstep (se 2 (by rfl) ⟨775701, by rfl⟩ : syracuseStep 2068537 = 1551403) B1551403
theorem B725071 : Blo 283827 725071 := bstep (se 1 (by rfl) ⟨543803, by rfl⟩ : syracuseStep 725071 = 1087607) B1087607
theorem B1839185 : Blo 283827 1839185 := bstep (se 2 (by rfl) ⟨689694, by rfl⟩ : syracuseStep 1839185 = 1379389) B1379389
theorem B430511 : Blo 283827 430511 := bstep (se 1 (by rfl) ⟨322883, by rfl⟩ : syracuseStep 430511 = 645767) B645767
theorem B430601 : Blo 283827 430601 := bstep (se 2 (by rfl) ⟨161475, by rfl⟩ : syracuseStep 430601 = 322951) B322951
theorem B331321873 : Blo 283827 331321873 := bstep (se 2 (by rfl) ⟨124245702, by rfl⟩ : syracuseStep 331321873 = 248491405) B248491405
theorem B430631 : Blo 283827 430631 := bstep (se 1 (by rfl) ⟨322973, by rfl⟩ : syracuseStep 430631 = 645947) B645947
theorem B430715 : Blo 283827 430715 := bstep (se 1 (by rfl) ⟨323036, by rfl⟩ : syracuseStep 430715 = 646073) B646073
theorem B725719 : Blo 283827 725719 := bstep (se 1 (by rfl) ⟨544289, by rfl⟩ : syracuseStep 725719 = 1088579) B1088579
theorem B430841 : Blo 283827 430841 := bstep (se 2 (by rfl) ⟨161565, by rfl⟩ : syracuseStep 430841 = 323131) B323131
theorem B1446659 : Blo 283827 1446659 := bstep (se 1 (by rfl) ⟨1084994, by rfl⟩ : syracuseStep 1446659 = 2169989) B2169989
theorem B430943 : Blo 283827 430943 := bstep (se 1 (by rfl) ⟨323207, by rfl⟩ : syracuseStep 430943 = 646415) B646415
theorem B430955 : Blo 283827 430955 := bstep (se 1 (by rfl) ⟨323216, by rfl⟩ : syracuseStep 430955 = 646433) B646433
theorem B1086317 : Blo 283827 1086317 := bstep (se 3 (by rfl) ⟨203684, by rfl⟩ : syracuseStep 1086317 = 407369) B407369
theorem B627643 : Blo 283827 627643 := bstep (se 1 (by rfl) ⟨470732, by rfl⟩ : syracuseStep 627643 = 941465) B941465
theorem B726023 : Blo 283827 726023 := bstep (se 1 (by rfl) ⟨544517, by rfl⟩ : syracuseStep 726023 = 1089035) B1089035
theorem B431183 : Blo 283827 431183 := bstep (se 1 (by rfl) ⟨323387, by rfl⟩ : syracuseStep 431183 = 646775) B646775
theorem B1086635 : Blo 283827 1086635 := bstep (se 1 (by rfl) ⟨814976, by rfl⟩ : syracuseStep 1086635 = 1629953) B1629953
theorem B431303 : Blo 283827 431303 := bstep (se 1 (by rfl) ⟨323477, by rfl⟩ : syracuseStep 431303 = 646955) B646955
theorem B431465 : Blo 283827 431465 := bstep (se 2 (by rfl) ⟨161799, by rfl⟩ : syracuseStep 431465 = 323599) B323599
theorem B431543 : Blo 283827 431543 := bstep (se 1 (by rfl) ⟨323657, by rfl⟩ : syracuseStep 431543 = 647315) B647315
theorem B431579 : Blo 283827 431579 := bstep (se 1 (by rfl) ⟨323684, by rfl⟩ : syracuseStep 431579 = 647369) B647369
theorem B1152797 : Blo 283827 1152797 := bstep (se 3 (by rfl) ⟨216149, by rfl⟩ : syracuseStep 1152797 = 432299) B432299
theorem B1218827 : Blo 283827 1218827 := bstep (se 1 (by rfl) ⟨914120, by rfl⟩ : syracuseStep 1218827 = 1828241) B1828241
theorem B1448279 : Blo 283827 1448279 := bstep (se 1 (by rfl) ⟨1086209, by rfl⟩ : syracuseStep 1448279 = 2172419) B2172419
theorem B1841849 : Blo 283827 1841849 := bstep (se 2 (by rfl) ⟨690693, by rfl⟩ : syracuseStep 1841849 = 1381387) B1381387
theorem B728311 : Blo 283827 728311 := bstep (se 1 (by rfl) ⟨546233, by rfl⟩ : syracuseStep 728311 = 1092467) B1092467
theorem B466319 : Blo 283827 466319 := bstep (se 1 (by rfl) ⟨349739, by rfl⟩ : syracuseStep 466319 = 699479) B699479
theorem B1089233 : Blo 283827 1089233 := bstep (se 2 (by rfl) ⟨408462, by rfl⟩ : syracuseStep 1089233 = 816925) B816925
theorem B958391 : Blo 283827 958391 := bstep (se 1 (by rfl) ⟨718793, by rfl⟩ : syracuseStep 958391 = 1437587) B1437587
theorem B1089551 : Blo 283827 1089551 := bstep (se 1 (by rfl) ⟨817163, by rfl⟩ : syracuseStep 1089551 = 1634327) B1634327
theorem B2170961 : Blo 283827 2170961 := bstep (se 2 (by rfl) ⟨814110, by rfl⟩ : syracuseStep 2170961 = 1628221) B1628221
theorem B958985 : Blo 283827 958985 := bstep (se 2 (by rfl) ⟨359619, by rfl⟩ : syracuseStep 958985 = 719239) B719239
theorem B1843847 : Blo 283827 1843847 := bstep (se 1 (by rfl) ⟨1382885, by rfl⟩ : syracuseStep 1843847 = 2765771) B2765771
theorem B13935563 : Blo 283827 13935563 := bstep (se 1 (by rfl) ⟨10451672, by rfl⟩ : syracuseStep 13935563 = 20903345) B20903345
theorem B1942501 : Blo 283827 1942501 := bstep (se 4 (by rfl) ⟨182109, by rfl⟩ : syracuseStep 1942501 = 364219) B364219
theorem B2106647 : Blo 283827 2106647 := bstep (se 1 (by rfl) ⟨1579985, by rfl⟩ : syracuseStep 2106647 = 3159971) B3159971
theorem B959849 : Blo 283827 959849 := bstep (se 2 (by rfl) ⟨359943, by rfl⟩ : syracuseStep 959849 = 719887) B719887
theorem B2631113 : Blo 283827 2631113 := bstep (se 2 (by rfl) ⟨986667, by rfl⟩ : syracuseStep 2631113 = 1973335) B1973335
theorem B2762387 : Blo 283827 2762387 := bstep (se 1 (by rfl) ⟨2071790, by rfl⟩ : syracuseStep 2762387 = 4143581) B4143581
theorem B1025747 : Blo 283827 1025747 := bstep (se 1 (by rfl) ⟨769310, by rfl⟩ : syracuseStep 1025747 = 1538621) B1538621
theorem B2303777 : Blo 283827 2303777 := bstep (se 2 (by rfl) ⟨863916, by rfl⟩ : syracuseStep 2303777 = 1727833) B1727833
theorem B1451843 : Blo 283827 1451843 := bstep (se 1 (by rfl) ⟨1088882, by rfl⟩ : syracuseStep 1451843 = 2177765) B2177765
theorem B8857505 : Blo 283827 8857505 := bstep (se 2 (by rfl) ⟨3321564, by rfl⟩ : syracuseStep 8857505 = 6643129) B6643129
theorem B960443 : Blo 283827 960443 := bstep (se 1 (by rfl) ⟨720332, by rfl⟩ : syracuseStep 960443 = 1440665) B1440665
theorem B1091663 : Blo 283827 1091663 := bstep (se 1 (by rfl) ⟨818747, by rfl⟩ : syracuseStep 1091663 = 1637495) B1637495
theorem B1223201 : Blo 283827 1223201 := bstep (se 2 (by rfl) ⟨458700, by rfl⟩ : syracuseStep 1223201 = 917401) B917401
theorem B1223353 : Blo 283827 1223353 := bstep (se 2 (by rfl) ⟨458757, by rfl⟩ : syracuseStep 1223353 = 917515) B917515
theorem B3910949 : Blo 283827 3910949 := bstep (se 4 (by rfl) ⟨366651, by rfl⟩ : syracuseStep 3910949 = 733303) B733303
theorem B1945127 : Blo 283827 1945127 := bstep (se 1 (by rfl) ⟨1458845, by rfl⟩ : syracuseStep 1945127 = 2917691) B2917691
theorem B962171 : Blo 283827 962171 := bstep (se 1 (by rfl) ⟨721628, by rfl⟩ : syracuseStep 962171 = 1443257) B1443257
theorem B962333 : Blo 283827 962333 := bstep (se 3 (by rfl) ⟨180437, by rfl⟩ : syracuseStep 962333 = 360875) B360875
theorem B963035 : Blo 283827 963035 := bstep (se 1 (by rfl) ⟨722276, by rfl⟩ : syracuseStep 963035 = 1444553) B1444553
theorem B733819 : Blo 283827 733819 := bstep (se 1 (by rfl) ⟨550364, by rfl⟩ : syracuseStep 733819 = 1100729) B1100729
theorem B1454921 : Blo 283827 1454921 := bstep (se 2 (by rfl) ⟨545595, by rfl⟩ : syracuseStep 1454921 = 1091191) B1091191
theorem B2175821 : Blo 283827 2175821 := bstep (se 3 (by rfl) ⟨407966, by rfl⟩ : syracuseStep 2175821 = 815933) B815933
theorem B963737 : Blo 283827 963737 := bstep (se 2 (by rfl) ⟨361401, by rfl⟩ : syracuseStep 963737 = 722803) B722803
theorem B1651915 : Blo 283827 1651915 := bstep (se 1 (by rfl) ⟨1238936, by rfl⟩ : syracuseStep 1651915 = 2477873) B2477873
theorem B406777 : Blo 283827 406777 := bstep (se 2 (by rfl) ⟨152541, by rfl⟩ : syracuseStep 406777 = 305083) B305083
theorem B1029437 : Blo 283827 1029437 := bstep (se 3 (by rfl) ⟨193019, by rfl⟩ : syracuseStep 1029437 = 386039) B386039
theorem B767497 : Blo 283827 767497 := bstep (se 2 (by rfl) ⟨287811, by rfl⟩ : syracuseStep 767497 = 575623) B575623
theorem B996923 : Blo 283827 996923 := bstep (se 1 (by rfl) ⟨747692, by rfl⟩ : syracuseStep 996923 = 1495385) B1495385
theorem B2340485 : Blo 283827 2340485 := bstep (se 4 (by rfl) ⟨219420, by rfl⟩ : syracuseStep 2340485 = 438841) B438841
theorem B2471639 : Blo 283827 2471639 := bstep (se 1 (by rfl) ⟨1853729, by rfl⟩ : syracuseStep 2471639 = 3707459) B3707459
theorem B4667179 : Blo 283827 4667179 := bstep (se 1 (by rfl) ⟨3500384, by rfl⟩ : syracuseStep 4667179 = 7000769) B7000769
theorem B1095611 : Blo 283827 1095611 := bstep (se 1 (by rfl) ⟨821708, by rfl⟩ : syracuseStep 1095611 = 1643417) B1643417
theorem B3127385 : Blo 283827 3127385 := bstep (se 2 (by rfl) ⟨1172769, by rfl⟩ : syracuseStep 3127385 = 2345539) B2345539
theorem B1456217 : Blo 283827 1456217 := bstep (se 2 (by rfl) ⟨546081, by rfl⟩ : syracuseStep 1456217 = 1092163) B1092163
theorem B964925 : Blo 283827 964925 := bstep (se 3 (by rfl) ⟨180923, by rfl⟩ : syracuseStep 964925 = 361847) B361847
theorem B1227113 : Blo 283827 1227113 := bstep (se 2 (by rfl) ⟨460167, by rfl⟩ : syracuseStep 1227113 = 920335) B920335
theorem B768727 : Blo 283827 768727 := bstep (se 1 (by rfl) ⟨576545, by rfl⟩ : syracuseStep 768727 = 1153091) B1153091
theorem B1981331 : Blo 283827 1981331 := bstep (se 1 (by rfl) ⟨1485998, by rfl⟩ : syracuseStep 1981331 = 2971997) B2971997
theorem B2046941 : Blo 283827 2046941 := bstep (se 3 (by rfl) ⟨383801, by rfl⟩ : syracuseStep 2046941 = 767603) B767603
theorem B965789 : Blo 283827 965789 := bstep (se 3 (by rfl) ⟨181085, by rfl⟩ : syracuseStep 965789 = 362171) B362171
theorem B2047169 : Blo 283827 2047169 := bstep (se 2 (by rfl) ⟨767688, by rfl⟩ : syracuseStep 2047169 = 1535377) B1535377
theorem B2178251 : Blo 283827 2178251 := bstep (se 1 (by rfl) ⟨1633688, by rfl⟩ : syracuseStep 2178251 = 3267377) B3267377
theorem B3128701 : Blo 283827 3128701 := bstep (se 3 (by rfl) ⟨586631, by rfl⟩ : syracuseStep 3128701 = 1173263) B1173263
theorem B966329 : Blo 283827 966329 := bstep (se 2 (by rfl) ⟨362373, by rfl⟩ : syracuseStep 966329 = 724747) B724747
theorem B638675 : Blo 283827 638675 := bstep (se 1 (by rfl) ⟨479006, by rfl⟩ : syracuseStep 638675 = 958013) B958013
theorem B540371 : Blo 283827 540371 := bstep (se 1 (by rfl) ⟨405278, by rfl⟩ : syracuseStep 540371 = 810557) B810557
theorem B1949483 : Blo 283827 1949483 := bstep (se 1 (by rfl) ⟨1462112, by rfl⟩ : syracuseStep 1949483 = 2924225) B2924225
theorem B540523 : Blo 283827 540523 := bstep (se 1 (by rfl) ⟨405392, by rfl⟩ : syracuseStep 540523 = 810785) B810785
theorem B540751 : Blo 283827 540751 := bstep (se 1 (by rfl) ⟨405563, by rfl⟩ : syracuseStep 540751 = 811127) B811127
theorem B3620945 : Blo 283827 3620945 := bstep (se 2 (by rfl) ⟨1357854, by rfl⟩ : syracuseStep 3620945 = 2715709) B2715709
theorem B966923 : Blo 283827 966923 := bstep (se 1 (by rfl) ⟨725192, by rfl⟩ : syracuseStep 966923 = 1450385) B1450385
theorem B967193 : Blo 283827 967193 := bstep (se 2 (by rfl) ⟨362697, by rfl⟩ : syracuseStep 967193 = 725395) B725395
theorem B639611 : Blo 283827 639611 := bstep (se 1 (by rfl) ⟨479708, by rfl⟩ : syracuseStep 639611 = 959417) B959417
theorem B1622663 : Blo 283827 1622663 := bstep (se 1 (by rfl) ⟨1216997, by rfl⟩ : syracuseStep 1622663 = 2433995) B2433995
theorem B639737 : Blo 283827 639737 := bstep (se 2 (by rfl) ⟨239901, by rfl⟩ : syracuseStep 639737 = 479803) B479803
theorem B640007 : Blo 283827 640007 := bstep (se 1 (by rfl) ⟨480005, by rfl⟩ : syracuseStep 640007 = 960011) B960011
theorem B640079 : Blo 283827 640079 := bstep (se 1 (by rfl) ⟨480059, by rfl⟩ : syracuseStep 640079 = 960119) B960119
theorem B640475 : Blo 283827 640475 := bstep (se 1 (by rfl) ⟨480356, by rfl⟩ : syracuseStep 640475 = 960713) B960713
theorem B968327 : Blo 283827 968327 := bstep (se 1 (by rfl) ⟨726245, by rfl⟩ : syracuseStep 968327 = 1452491) B1452491
theorem B6211217 : Blo 283827 6211217 := bstep (se 2 (by rfl) ⟨2329206, by rfl⟩ : syracuseStep 6211217 = 4658413) B4658413
theorem B968381 : Blo 283827 968381 := bstep (se 3 (by rfl) ⟨181571, by rfl⟩ : syracuseStep 968381 = 363143) B363143
theorem B968543 : Blo 283827 968543 := bstep (se 1 (by rfl) ⟨726407, by rfl⟩ : syracuseStep 968543 = 1452815) B1452815
theorem B640943 : Blo 283827 640943 := bstep (se 1 (by rfl) ⟨480707, by rfl⟩ : syracuseStep 640943 = 961415) B961415
theorem B1034167 : Blo 283827 1034167 := bstep (se 1 (by rfl) ⟨775625, by rfl⟩ : syracuseStep 1034167 = 1551251) B1551251
theorem B968705 : Blo 283827 968705 := bstep (se 2 (by rfl) ⟨363264, by rfl⟩ : syracuseStep 968705 = 726529) B726529
theorem B1624121 : Blo 283827 1624121 := bstep (se 2 (by rfl) ⟨609045, by rfl⟩ : syracuseStep 1624121 = 1218091) B1218091
theorem B641195 : Blo 283827 641195 := bstep (se 1 (by rfl) ⟨480896, by rfl⟩ : syracuseStep 641195 = 961793) B961793
theorem B1100477 : Blo 283827 1100477 := bstep (se 3 (by rfl) ⟨206339, by rfl⟩ : syracuseStep 1100477 = 412679) B412679
theorem B641735 : Blo 283827 641735 := bstep (se 1 (by rfl) ⟨481301, by rfl⟩ : syracuseStep 641735 = 962603) B962603
theorem B969515 : Blo 283827 969515 := bstep (se 1 (by rfl) ⟨727136, by rfl⟩ : syracuseStep 969515 = 1454273) B1454273
theorem B969785 : Blo 283827 969785 := bstep (se 2 (by rfl) ⟨363669, by rfl⟩ : syracuseStep 969785 = 727339) B727339
theorem B1133929 : Blo 283827 1133929 := bstep (se 2 (by rfl) ⟨425223, by rfl⟩ : syracuseStep 1133929 = 850447) B850447
theorem B970109 : Blo 283827 970109 := bstep (se 3 (by rfl) ⟨181895, by rfl⟩ : syracuseStep 970109 = 363791) B363791
theorem B642599 : Blo 283827 642599 := bstep (se 1 (by rfl) ⟨481949, by rfl⟩ : syracuseStep 642599 = 963899) B963899
theorem B544313 : Blo 283827 544313 := bstep (se 2 (by rfl) ⟨204117, by rfl⟩ : syracuseStep 544313 = 408235) B408235
theorem B970379 : Blo 283827 970379 := bstep (se 1 (by rfl) ⟨727784, by rfl⟩ : syracuseStep 970379 = 1455569) B1455569
theorem B1101523 : Blo 283827 1101523 := bstep (se 1 (by rfl) ⟨826142, by rfl⟩ : syracuseStep 1101523 = 1652285) B1652285
theorem B479081 : Blo 283827 479081 := bstep (se 2 (by rfl) ⟨179655, by rfl⟩ : syracuseStep 479081 = 359311) B359311
theorem B642923 : Blo 283827 642923 := bstep (se 1 (by rfl) ⟨482192, by rfl⟩ : syracuseStep 642923 = 964385) B964385
theorem B642977 : Blo 283827 642977 := bstep (se 2 (by rfl) ⟨241116, by rfl⟩ : syracuseStep 642977 = 482233) B482233
theorem B1855495 : Blo 283827 1855495 := bstep (se 1 (by rfl) ⟨1391621, by rfl⟩ : syracuseStep 1855495 = 2783243) B2783243
theorem B512009 : Blo 283827 512009 := bstep (se 2 (by rfl) ⟨192003, by rfl⟩ : syracuseStep 512009 = 384007) B384007
theorem B3657757 : Blo 283827 3657757 := bstep (se 3 (by rfl) ⟨685829, by rfl⟩ : syracuseStep 3657757 = 1371659) B1371659
theorem B1233053 : Blo 283827 1233053 := bstep (se 3 (by rfl) ⟨231197, by rfl⟩ : syracuseStep 1233053 = 462395) B462395
theorem B479479 : Blo 283827 479479 := bstep (se 1 (by rfl) ⟨359609, by rfl⟩ : syracuseStep 479479 = 719219) B719219
theorem B643319 : Blo 283827 643319 := bstep (se 1 (by rfl) ⟨482489, by rfl⟩ : syracuseStep 643319 = 964979) B964979
theorem B479675 : Blo 283827 479675 := bstep (se 1 (by rfl) ⟨359756, by rfl⟩ : syracuseStep 479675 = 719513) B719513
theorem B971297 : Blo 283827 971297 := bstep (se 2 (by rfl) ⟨364236, by rfl⟩ : syracuseStep 971297 = 728473) B728473
theorem B479783 : Blo 283827 479783 := bstep (se 1 (by rfl) ⟨359837, by rfl⟩ : syracuseStep 479783 = 719675) B719675
theorem B414407 : Blo 283827 414407 := bstep (se 1 (by rfl) ⟨310805, by rfl⟩ : syracuseStep 414407 = 621611) B621611
theorem B480073 : Blo 283827 480073 := bstep (se 2 (by rfl) ⟨180027, by rfl⟩ : syracuseStep 480073 = 360055) B360055
theorem B643913 : Blo 283827 643913 := bstep (se 2 (by rfl) ⟨241467, by rfl⟩ : syracuseStep 643913 = 482935) B482935
theorem B480107 : Blo 283827 480107 := bstep (se 1 (by rfl) ⟨360080, by rfl⟩ : syracuseStep 480107 = 720161) B720161
theorem B2184083 : Blo 283827 2184083 := bstep (se 1 (by rfl) ⟨1638062, by rfl⟩ : syracuseStep 2184083 = 3276125) B3276125
theorem B3724289 : Blo 283827 3724289 := bstep (se 2 (by rfl) ⟨1396608, by rfl⟩ : syracuseStep 3724289 = 2793217) B2793217
theorem B611335 : Blo 283827 611335 := bstep (se 1 (by rfl) ⟨458501, by rfl⟩ : syracuseStep 611335 = 917003) B917003
theorem B545915 : Blo 283827 545915 := bstep (se 1 (by rfl) ⟨409436, by rfl⟩ : syracuseStep 545915 = 818873) B818873
theorem B1627289 : Blo 283827 1627289 := bstep (se 2 (by rfl) ⟨610233, by rfl⟩ : syracuseStep 1627289 = 1220467) B1220467
theorem B283847 : Blo 283827 283847 := bstep (se 1 (by rfl) ⟨212885, by rfl⟩ : syracuseStep 283847 = 425771) B425771
theorem B414919 : Blo 283827 414919 := bstep (se 1 (by rfl) ⟨311189, by rfl⟩ : syracuseStep 414919 = 622379) B622379
theorem B283867 : Blo 283827 283867 := bstep (se 1 (by rfl) ⟨212900, by rfl⟩ : syracuseStep 283867 = 425801) B425801
theorem B480505 : Blo 283827 480505 := bstep (se 2 (by rfl) ⟨180189, by rfl⟩ : syracuseStep 480505 = 360379) B360379
theorem B283943 : Blo 283827 283943 := bstep (se 1 (by rfl) ⟨212957, by rfl⟩ : syracuseStep 283943 = 425915) B425915
theorem B283983 : Blo 283827 283983 := bstep (se 1 (by rfl) ⟨212987, by rfl⟩ : syracuseStep 283983 = 425975) B425975
theorem B283999 : Blo 283827 283999 := bstep (se 1 (by rfl) ⟨212999, by rfl⟩ : syracuseStep 283999 = 425999) B425999
theorem B284027 : Blo 283827 284027 := bstep (se 1 (by rfl) ⟨213020, by rfl⟩ : syracuseStep 284027 = 426041) B426041
theorem B284079 : Blo 283827 284079 := bstep (se 1 (by rfl) ⟨213059, by rfl⟩ : syracuseStep 284079 = 426119) B426119
theorem B284103 : Blo 283827 284103 := bstep (se 1 (by rfl) ⟨213077, by rfl⟩ : syracuseStep 284103 = 426155) B426155
theorem B284123 : Blo 283827 284123 := bstep (se 1 (by rfl) ⟨213092, by rfl⟩ : syracuseStep 284123 = 426185) B426185
theorem B480775 : Blo 283827 480775 := bstep (se 1 (by rfl) ⟨360581, by rfl⟩ : syracuseStep 480775 = 721163) B721163
theorem B284199 : Blo 283827 284199 := bstep (se 1 (by rfl) ⟨213149, by rfl⟩ : syracuseStep 284199 = 426299) B426299
theorem B546383 : Blo 283827 546383 := bstep (se 1 (by rfl) ⟨409787, by rfl⟩ : syracuseStep 546383 = 819575) B819575
theorem B284239 : Blo 283827 284239 := bstep (se 1 (by rfl) ⟨213179, by rfl⟩ : syracuseStep 284239 = 426359) B426359
theorem B284255 : Blo 283827 284255 := bstep (se 1 (by rfl) ⟨213191, by rfl⟩ : syracuseStep 284255 = 426383) B426383
theorem B644705 : Blo 283827 644705 := bstep (se 2 (by rfl) ⟨241764, by rfl⟩ : syracuseStep 644705 = 483529) B483529
theorem B546401 : Blo 283827 546401 := bstep (se 2 (by rfl) ⟨204900, by rfl⟩ : syracuseStep 546401 = 409801) B409801
theorem B284283 : Blo 283827 284283 := bstep (se 1 (by rfl) ⟨213212, by rfl⟩ : syracuseStep 284283 = 426425) B426425
theorem B284335 : Blo 283827 284335 := bstep (se 1 (by rfl) ⟨213251, by rfl⟩ : syracuseStep 284335 = 426503) B426503
theorem B284359 : Blo 283827 284359 := bstep (se 1 (by rfl) ⟨213269, by rfl⟩ : syracuseStep 284359 = 426539) B426539
theorem B284379 : Blo 283827 284379 := bstep (se 1 (by rfl) ⟨213284, by rfl⟩ : syracuseStep 284379 = 426569) B426569
theorem B284455 : Blo 283827 284455 := bstep (se 1 (by rfl) ⟨213341, by rfl⟩ : syracuseStep 284455 = 426683) B426683
theorem B284495 : Blo 283827 284495 := bstep (se 1 (by rfl) ⟨213371, by rfl⟩ : syracuseStep 284495 = 426743) B426743
theorem B284511 : Blo 283827 284511 := bstep (se 1 (by rfl) ⟨213383, by rfl⟩ : syracuseStep 284511 = 426767) B426767
theorem B2185055 : Blo 283827 2185055 := bstep (se 1 (by rfl) ⟨1638791, by rfl⟩ : syracuseStep 2185055 = 3277583) B3277583
theorem B284539 : Blo 283827 284539 := bstep (se 1 (by rfl) ⟨213404, by rfl⟩ : syracuseStep 284539 = 426809) B426809
theorem B284591 : Blo 283827 284591 := bstep (se 1 (by rfl) ⟨213443, by rfl⟩ : syracuseStep 284591 = 426887) B426887
theorem B481207 : Blo 283827 481207 := bstep (se 1 (by rfl) ⟨360905, by rfl⟩ : syracuseStep 481207 = 721811) B721811
theorem B645047 : Blo 283827 645047 := bstep (se 1 (by rfl) ⟨483785, by rfl⟩ : syracuseStep 645047 = 967571) B967571
theorem B284615 : Blo 283827 284615 := bstep (se 1 (by rfl) ⟨213461, by rfl⟩ : syracuseStep 284615 = 426923) B426923
theorem B284635 : Blo 283827 284635 := bstep (se 1 (by rfl) ⟨213476, by rfl⟩ : syracuseStep 284635 = 426953) B426953
theorem B284711 : Blo 283827 284711 := bstep (se 1 (by rfl) ⟨213533, by rfl⟩ : syracuseStep 284711 = 427067) B427067
theorem B12277817 : Blo 283827 12277817 := bstep (se 2 (by rfl) ⟨4604181, by rfl⟩ : syracuseStep 12277817 = 9208363) B9208363
theorem B284751 : Blo 283827 284751 := bstep (se 1 (by rfl) ⟨213563, by rfl⟩ : syracuseStep 284751 = 427127) B427127
theorem B284767 : Blo 283827 284767 := bstep (se 1 (by rfl) ⟨213575, by rfl⟩ : syracuseStep 284767 = 427151) B427151
theorem B284795 : Blo 283827 284795 := bstep (se 1 (by rfl) ⟨213596, by rfl⟩ : syracuseStep 284795 = 427193) B427193
theorem B481403 : Blo 283827 481403 := bstep (se 1 (by rfl) ⟨361052, by rfl⟩ : syracuseStep 481403 = 722105) B722105
theorem B284847 : Blo 283827 284847 := bstep (se 1 (by rfl) ⟨213635, by rfl⟩ : syracuseStep 284847 = 427271) B427271
theorem B284871 : Blo 283827 284871 := bstep (se 1 (by rfl) ⟨213653, by rfl⟩ : syracuseStep 284871 = 427307) B427307
theorem B284891 : Blo 283827 284891 := bstep (se 1 (by rfl) ⟨213668, by rfl⟩ : syracuseStep 284891 = 427337) B427337
theorem B6314273 : Blo 283827 6314273 := bstep (se 2 (by rfl) ⟨2367852, by rfl⟩ : syracuseStep 6314273 = 4735705) B4735705
theorem B284967 : Blo 283827 284967 := bstep (se 1 (by rfl) ⟨213725, by rfl⟩ : syracuseStep 284967 = 427451) B427451
theorem B285007 : Blo 283827 285007 := bstep (se 1 (by rfl) ⟨213755, by rfl⟩ : syracuseStep 285007 = 427511) B427511
theorem B285023 : Blo 283827 285023 := bstep (se 1 (by rfl) ⟨213767, by rfl⟩ : syracuseStep 285023 = 427535) B427535
theorem B285051 : Blo 283827 285051 := bstep (se 1 (by rfl) ⟨213788, by rfl⟩ : syracuseStep 285051 = 427577) B427577
theorem B285103 : Blo 283827 285103 := bstep (se 1 (by rfl) ⟨213827, by rfl⟩ : syracuseStep 285103 = 427655) B427655
theorem B285127 : Blo 283827 285127 := bstep (se 1 (by rfl) ⟨213845, by rfl⟩ : syracuseStep 285127 = 427691) B427691
theorem B285147 : Blo 283827 285147 := bstep (se 1 (by rfl) ⟨213860, by rfl⟩ : syracuseStep 285147 = 427721) B427721
theorem B481801 : Blo 283827 481801 := bstep (se 2 (by rfl) ⟨180675, by rfl⟩ : syracuseStep 481801 = 361351) B361351
theorem B645641 : Blo 283827 645641 := bstep (se 2 (by rfl) ⟨242115, by rfl⟩ : syracuseStep 645641 = 484231) B484231
theorem B285223 : Blo 283827 285223 := bstep (se 1 (by rfl) ⟨213917, by rfl⟩ : syracuseStep 285223 = 427835) B427835
theorem B285263 : Blo 283827 285263 := bstep (se 1 (by rfl) ⟨213947, by rfl⟩ : syracuseStep 285263 = 427895) B427895
theorem B285279 : Blo 283827 285279 := bstep (se 1 (by rfl) ⟨213959, by rfl⟩ : syracuseStep 285279 = 427919) B427919
theorem B285307 : Blo 283827 285307 := bstep (se 1 (by rfl) ⟨213980, by rfl⟩ : syracuseStep 285307 = 427961) B427961
theorem B481963 : Blo 283827 481963 := bstep (se 1 (by rfl) ⟨361472, by rfl⟩ : syracuseStep 481963 = 722945) B722945
theorem B285359 : Blo 283827 285359 := bstep (se 1 (by rfl) ⟨214019, by rfl⟩ : syracuseStep 285359 = 428039) B428039
theorem B285383 : Blo 283827 285383 := bstep (se 1 (by rfl) ⟨214037, by rfl⟩ : syracuseStep 285383 = 428075) B428075
theorem B285403 : Blo 283827 285403 := bstep (se 1 (by rfl) ⟨214052, by rfl⟩ : syracuseStep 285403 = 428105) B428105
theorem B3496733 : Blo 283827 3496733 := bstep (se 3 (by rfl) ⟨655637, by rfl⟩ : syracuseStep 3496733 = 1311275) B1311275
theorem B285479 : Blo 283827 285479 := bstep (se 1 (by rfl) ⟨214109, by rfl⟩ : syracuseStep 285479 = 428219) B428219
theorem B285519 : Blo 283827 285519 := bstep (se 1 (by rfl) ⟨214139, by rfl⟩ : syracuseStep 285519 = 428279) B428279
theorem B285535 : Blo 283827 285535 := bstep (se 1 (by rfl) ⟨214151, by rfl⟩ : syracuseStep 285535 = 428303) B428303
theorem B645983 : Blo 283827 645983 := bstep (se 1 (by rfl) ⟨484487, by rfl⟩ : syracuseStep 645983 = 968975) B968975
theorem B285563 : Blo 283827 285563 := bstep (se 1 (by rfl) ⟨214172, by rfl⟩ : syracuseStep 285563 = 428345) B428345
theorem B285615 : Blo 283827 285615 := bstep (se 1 (by rfl) ⟨214211, by rfl⟩ : syracuseStep 285615 = 428423) B428423
theorem B285639 : Blo 283827 285639 := bstep (se 1 (by rfl) ⟨214229, by rfl⟩ : syracuseStep 285639 = 428459) B428459
theorem B285659 : Blo 283827 285659 := bstep (se 1 (by rfl) ⟨214244, by rfl⟩ : syracuseStep 285659 = 428489) B428489
theorem B482267 : Blo 283827 482267 := bstep (se 1 (by rfl) ⟨361700, by rfl⟩ : syracuseStep 482267 = 723401) B723401
theorem B646163 : Blo 283827 646163 := bstep (se 1 (by rfl) ⟨484622, by rfl⟩ : syracuseStep 646163 = 969245) B969245
theorem B285735 : Blo 283827 285735 := bstep (se 1 (by rfl) ⟨214301, by rfl⟩ : syracuseStep 285735 = 428603) B428603
theorem B285775 : Blo 283827 285775 := bstep (se 1 (by rfl) ⟨214331, by rfl⟩ : syracuseStep 285775 = 428663) B428663
theorem B285791 : Blo 283827 285791 := bstep (se 1 (by rfl) ⟨214343, by rfl⟩ : syracuseStep 285791 = 428687) B428687
theorem B285819 : Blo 283827 285819 := bstep (se 1 (by rfl) ⟨214364, by rfl⟩ : syracuseStep 285819 = 428729) B428729
theorem B285871 : Blo 283827 285871 := bstep (se 1 (by rfl) ⟨214403, by rfl⟩ : syracuseStep 285871 = 428807) B428807
theorem B285895 : Blo 283827 285895 := bstep (se 1 (by rfl) ⟨214421, by rfl⟩ : syracuseStep 285895 = 428843) B428843
theorem B482503 : Blo 283827 482503 := bstep (se 1 (by rfl) ⟨361877, by rfl⟩ : syracuseStep 482503 = 723755) B723755
theorem B285915 : Blo 283827 285915 := bstep (se 1 (by rfl) ⟨214436, by rfl⟩ : syracuseStep 285915 = 428873) B428873
theorem B2055415 : Blo 283827 2055415 := bstep (se 1 (by rfl) ⟨1541561, by rfl⟩ : syracuseStep 2055415 = 3083123) B3083123
theorem B1826063 : Blo 283827 1826063 := bstep (se 1 (by rfl) ⟨1369547, by rfl⟩ : syracuseStep 1826063 = 2739095) B2739095
theorem B285991 : Blo 283827 285991 := bstep (se 1 (by rfl) ⟨214493, by rfl⟩ : syracuseStep 285991 = 428987) B428987
theorem B286031 : Blo 283827 286031 := bstep (se 1 (by rfl) ⟨214523, by rfl⟩ : syracuseStep 286031 = 429047) B429047
theorem B286047 : Blo 283827 286047 := bstep (se 1 (by rfl) ⟨214535, by rfl⟩ : syracuseStep 286047 = 429071) B429071
theorem B482665 : Blo 283827 482665 := bstep (se 2 (by rfl) ⟨180999, by rfl⟩ : syracuseStep 482665 = 361999) B361999
theorem B646505 : Blo 283827 646505 := bstep (se 2 (by rfl) ⟨242439, by rfl⟩ : syracuseStep 646505 = 484879) B484879
theorem B286075 : Blo 283827 286075 := bstep (se 1 (by rfl) ⟨214556, by rfl⟩ : syracuseStep 286075 = 429113) B429113
theorem B286127 : Blo 283827 286127 := bstep (se 1 (by rfl) ⟨214595, by rfl⟩ : syracuseStep 286127 = 429191) B429191
theorem B286151 : Blo 283827 286151 := bstep (se 1 (by rfl) ⟨214613, by rfl⟩ : syracuseStep 286151 = 429227) B429227
theorem B286171 : Blo 283827 286171 := bstep (se 1 (by rfl) ⟨214628, by rfl⟩ : syracuseStep 286171 = 429257) B429257
theorem B286247 : Blo 283827 286247 := bstep (se 1 (by rfl) ⟨214685, by rfl⟩ : syracuseStep 286247 = 429371) B429371
theorem B286287 : Blo 283827 286287 := bstep (se 1 (by rfl) ⟨214715, by rfl⟩ : syracuseStep 286287 = 429431) B429431
theorem B286303 : Blo 283827 286303 := bstep (se 1 (by rfl) ⟨214727, by rfl⟩ : syracuseStep 286303 = 429455) B429455
theorem B286331 : Blo 283827 286331 := bstep (se 1 (by rfl) ⟨214748, by rfl⟩ : syracuseStep 286331 = 429497) B429497
theorem B286383 : Blo 283827 286383 := bstep (se 1 (by rfl) ⟨214787, by rfl⟩ : syracuseStep 286383 = 429575) B429575
theorem B286407 : Blo 283827 286407 := bstep (se 1 (by rfl) ⟨214805, by rfl⟩ : syracuseStep 286407 = 429611) B429611
theorem B286427 : Blo 283827 286427 := bstep (se 1 (by rfl) ⟨214820, by rfl⟩ : syracuseStep 286427 = 429641) B429641
theorem B614137 : Blo 283827 614137 := bstep (se 2 (by rfl) ⟨230301, by rfl⟩ : syracuseStep 614137 = 460603) B460603
theorem B286503 : Blo 283827 286503 := bstep (se 1 (by rfl) ⟨214877, by rfl⟩ : syracuseStep 286503 = 429755) B429755
theorem B286543 : Blo 283827 286543 := bstep (se 1 (by rfl) ⟨214907, by rfl⟩ : syracuseStep 286543 = 429815) B429815
theorem B286559 : Blo 283827 286559 := bstep (se 1 (by rfl) ⟨214919, by rfl⟩ : syracuseStep 286559 = 429839) B429839
theorem B515945 : Blo 283827 515945 := bstep (se 2 (by rfl) ⟨193479, by rfl⟩ : syracuseStep 515945 = 386959) B386959
theorem B286587 : Blo 283827 286587 := bstep (se 1 (by rfl) ⟨214940, by rfl⟩ : syracuseStep 286587 = 429881) B429881
theorem B1105825 : Blo 283827 1105825 := bstep (se 2 (by rfl) ⟨414684, by rfl⟩ : syracuseStep 1105825 = 829369) B829369
theorem B286639 : Blo 283827 286639 := bstep (se 1 (by rfl) ⟨214979, by rfl⟩ : syracuseStep 286639 = 429959) B429959
theorem B483259 : Blo 283827 483259 := bstep (se 1 (by rfl) ⟨362444, by rfl⟩ : syracuseStep 483259 = 724889) B724889
theorem B647099 : Blo 283827 647099 := bstep (se 1 (by rfl) ⟨485324, by rfl⟩ : syracuseStep 647099 = 970649) B970649
theorem B286663 : Blo 283827 286663 := bstep (se 1 (by rfl) ⟨214997, by rfl⟩ : syracuseStep 286663 = 429995) B429995
theorem B286683 : Blo 283827 286683 := bstep (se 1 (by rfl) ⟨215012, by rfl⟩ : syracuseStep 286683 = 430025) B430025
theorem B483367 : Blo 283827 483367 := bstep (se 1 (by rfl) ⟨362525, by rfl⟩ : syracuseStep 483367 = 725051) B725051
theorem B286759 : Blo 283827 286759 := bstep (se 1 (by rfl) ⟨215069, by rfl⟩ : syracuseStep 286759 = 430139) B430139
theorem B647225 : Blo 283827 647225 := bstep (se 2 (by rfl) ⟨242709, by rfl⟩ : syracuseStep 647225 = 485419) B485419
theorem B319567 : Blo 283827 319567 := bstep (se 1 (by rfl) ⟨239675, by rfl⟩ : syracuseStep 319567 = 479351) B479351
theorem B286799 : Blo 283827 286799 := bstep (se 1 (by rfl) ⟨215099, by rfl⟩ : syracuseStep 286799 = 430199) B430199
theorem B2613329 : Blo 283827 2613329 := bstep (se 2 (by rfl) ⟨979998, by rfl⟩ : syracuseStep 2613329 = 1959997) B1959997
theorem B614479 : Blo 283827 614479 := bstep (se 1 (by rfl) ⟨460859, by rfl⟩ : syracuseStep 614479 = 921719) B921719
theorem B286815 : Blo 283827 286815 := bstep (se 1 (by rfl) ⟨215111, by rfl⟩ : syracuseStep 286815 = 430223) B430223
theorem B286843 : Blo 283827 286843 := bstep (se 1 (by rfl) ⟨215132, by rfl⟩ : syracuseStep 286843 = 430265) B430265
theorem B286895 : Blo 283827 286895 := bstep (se 1 (by rfl) ⟨215171, by rfl⟩ : syracuseStep 286895 = 430343) B430343
theorem B286919 : Blo 283827 286919 := bstep (se 1 (by rfl) ⟨215189, by rfl⟩ : syracuseStep 286919 = 430379) B430379
theorem B286939 : Blo 283827 286939 := bstep (se 1 (by rfl) ⟨215204, by rfl⟩ : syracuseStep 286939 = 430409) B430409
theorem B2744549 : Blo 283827 2744549 := bstep (se 4 (by rfl) ⟨257301, by rfl⟩ : syracuseStep 2744549 = 514603) B514603
theorem B3924197 : Blo 283827 3924197 := bstep (se 4 (by rfl) ⟨367893, by rfl⟩ : syracuseStep 3924197 = 735787) B735787
theorem B287015 : Blo 283827 287015 := bstep (se 1 (by rfl) ⟨215261, by rfl⟩ : syracuseStep 287015 = 430523) B430523
theorem B549193 : Blo 283827 549193 := bstep (se 2 (by rfl) ⟨205947, by rfl⟩ : syracuseStep 549193 = 411895) B411895
theorem B287055 : Blo 283827 287055 := bstep (se 1 (by rfl) ⟨215291, by rfl⟩ : syracuseStep 287055 = 430583) B430583
theorem B287071 : Blo 283827 287071 := bstep (se 1 (by rfl) ⟨215303, by rfl⟩ : syracuseStep 287071 = 430607) B430607
theorem B483691 : Blo 283827 483691 := bstep (se 1 (by rfl) ⟨362768, by rfl⟩ : syracuseStep 483691 = 725537) B725537
theorem B581995 : Blo 283827 581995 := bstep (se 1 (by rfl) ⟨436496, by rfl⟩ : syracuseStep 581995 = 872993) B872993
theorem B287099 : Blo 283827 287099 := bstep (se 1 (by rfl) ⟨215324, by rfl⟩ : syracuseStep 287099 = 430649) B430649
theorem B647567 : Blo 283827 647567 := bstep (se 1 (by rfl) ⟨485675, by rfl⟩ : syracuseStep 647567 = 971351) B971351
theorem B287151 : Blo 283827 287151 := bstep (se 1 (by rfl) ⟨215363, by rfl⟩ : syracuseStep 287151 = 430727) B430727
theorem B287175 : Blo 283827 287175 := bstep (se 1 (by rfl) ⟨215381, by rfl⟩ : syracuseStep 287175 = 430763) B430763
theorem B319963 : Blo 283827 319963 := bstep (se 1 (by rfl) ⟨239972, by rfl⟩ : syracuseStep 319963 = 479945) B479945
theorem B385499 : Blo 283827 385499 := bstep (se 1 (by rfl) ⟨289124, by rfl⟩ : syracuseStep 385499 = 578249) B578249
theorem B287195 : Blo 283827 287195 := bstep (se 1 (by rfl) ⟨215396, by rfl⟩ : syracuseStep 287195 = 430793) B430793
theorem B811559 : Blo 283827 811559 := bstep (se 1 (by rfl) ⟨608669, by rfl⟩ : syracuseStep 811559 = 1217339) B1217339
theorem B287271 : Blo 283827 287271 := bstep (se 1 (by rfl) ⟨215453, by rfl⟩ : syracuseStep 287271 = 430907) B430907
theorem B3465787 : Blo 283827 3465787 := bstep (se 1 (by rfl) ⟨2599340, by rfl⟩ : syracuseStep 3465787 = 5198681) B5198681
theorem B287311 : Blo 283827 287311 := bstep (se 1 (by rfl) ⟨215483, by rfl⟩ : syracuseStep 287311 = 430967) B430967
theorem B287327 : Blo 283827 287327 := bstep (se 1 (by rfl) ⟨215495, by rfl⟩ : syracuseStep 287327 = 430991) B430991
theorem B287355 : Blo 283827 287355 := bstep (se 1 (by rfl) ⟨215516, by rfl⟩ : syracuseStep 287355 = 431033) B431033
theorem B287407 : Blo 283827 287407 := bstep (se 1 (by rfl) ⟨215555, by rfl⟩ : syracuseStep 287407 = 431111) B431111
theorem B287431 : Blo 283827 287431 := bstep (se 1 (by rfl) ⟨215573, by rfl⟩ : syracuseStep 287431 = 431147) B431147
theorem B287451 : Blo 283827 287451 := bstep (se 1 (by rfl) ⟨215588, by rfl⟩ : syracuseStep 287451 = 431177) B431177
theorem B287527 : Blo 283827 287527 := bstep (se 1 (by rfl) ⟨215645, by rfl⟩ : syracuseStep 287527 = 431291) B431291
theorem B287567 : Blo 283827 287567 := bstep (se 1 (by rfl) ⟨215675, by rfl⟩ : syracuseStep 287567 = 431351) B431351
theorem B287583 : Blo 283827 287583 := bstep (se 1 (by rfl) ⟨215687, by rfl⟩ : syracuseStep 287583 = 431375) B431375
theorem B910187 : Blo 283827 910187 := bstep (se 1 (by rfl) ⟨682640, by rfl⟩ : syracuseStep 910187 = 1365281) B1365281
theorem B287611 : Blo 283827 287611 := bstep (se 1 (by rfl) ⟨215708, by rfl⟩ : syracuseStep 287611 = 431417) B431417
theorem B2155409 : Blo 283827 2155409 := bstep (se 2 (by rfl) ⟨808278, by rfl⟩ : syracuseStep 2155409 = 1616557) B1616557
theorem B320431 : Blo 283827 320431 := bstep (se 1 (by rfl) ⟨240323, by rfl⟩ : syracuseStep 320431 = 480647) B480647
theorem B287663 : Blo 283827 287663 := bstep (se 1 (by rfl) ⟨215747, by rfl⟩ : syracuseStep 287663 = 431495) B431495
theorem B287687 : Blo 283827 287687 := bstep (se 1 (by rfl) ⟨215765, by rfl⟩ : syracuseStep 287687 = 431531) B431531
theorem B287707 : Blo 283827 287707 := bstep (se 1 (by rfl) ⟨215780, by rfl⟩ : syracuseStep 287707 = 431561) B431561
theorem B287783 : Blo 283827 287783 := bstep (se 1 (by rfl) ⟨215837, by rfl⟩ : syracuseStep 287783 = 431675) B431675
theorem B287823 : Blo 283827 287823 := bstep (se 1 (by rfl) ⟨215867, by rfl⟩ : syracuseStep 287823 = 431735) B431735
theorem B320863 : Blo 283827 320863 := bstep (se 1 (by rfl) ⟨240647, by rfl⟩ : syracuseStep 320863 = 481295) B481295
theorem B484751 : Blo 283827 484751 := bstep (se 1 (by rfl) ⟨363563, by rfl⟩ : syracuseStep 484751 = 727127) B727127
theorem B3302819 : Blo 283827 3302819 := bstep (se 1 (by rfl) ⟨2477114, by rfl⟩ : syracuseStep 3302819 = 4954229) B4954229
theorem B648667 : Blo 283827 648667 := bstep (se 1 (by rfl) ⟨486500, by rfl⟩ : syracuseStep 648667 = 973001) B973001
theorem B484987 : Blo 283827 484987 := bstep (se 1 (by rfl) ⟨363740, by rfl⟩ : syracuseStep 484987 = 727481) B727481
theorem B321223 : Blo 283827 321223 := bstep (se 1 (by rfl) ⟨240917, by rfl⟩ : syracuseStep 321223 = 481835) B481835
theorem B1632095 : Blo 283827 1632095 := bstep (se 1 (by rfl) ⟨1224071, by rfl⟩ : syracuseStep 1632095 = 2448143) B2448143
theorem B1730413 : Blo 283827 1730413 := bstep (se 3 (by rfl) ⟨324452, by rfl⟩ : syracuseStep 1730413 = 648905) B648905
theorem B1828727 : Blo 283827 1828727 := bstep (se 1 (by rfl) ⟨1371545, by rfl⟩ : syracuseStep 1828727 = 2743091) B2743091
theorem B1632413 : Blo 283827 1632413 := bstep (se 3 (by rfl) ⟨306077, by rfl⟩ : syracuseStep 1632413 = 612155) B612155
theorem B322087 : Blo 283827 322087 := bstep (se 1 (by rfl) ⟨241565, by rfl⟩ : syracuseStep 322087 = 483131) B483131
theorem B911969 : Blo 283827 911969 := bstep (se 2 (by rfl) ⟨341988, by rfl⟩ : syracuseStep 911969 = 683977) B683977
theorem B2321297 : Blo 283827 2321297 := bstep (se 2 (by rfl) ⟨870486, by rfl⟩ : syracuseStep 2321297 = 1740973) B1740973
theorem B683255 : Blo 283827 683255 := bstep (se 1 (by rfl) ⟨512441, by rfl⟩ : syracuseStep 683255 = 1024883) B1024883
theorem B2157839 : Blo 283827 2157839 := bstep (se 1 (by rfl) ⟨1618379, by rfl⟩ : syracuseStep 2157839 = 3236759) B3236759
theorem B1437101 : Blo 283827 1437101 := bstep (se 3 (by rfl) ⟨269456, by rfl⟩ : syracuseStep 1437101 = 538913) B538913
theorem B290503 : Blo 283827 290503 := bstep (se 1 (by rfl) ⟨217877, by rfl⟩ : syracuseStep 290503 = 435755) B435755
theorem B683959 : Blo 283827 683959 := bstep (se 1 (by rfl) ⟨512969, by rfl⟩ : syracuseStep 683959 = 1025939) B1025939
theorem B4649075 : Blo 283827 4649075 := bstep (se 1 (by rfl) ⟨3486806, by rfl⟩ : syracuseStep 4649075 = 6973613) B6973613
theorem B323707 : Blo 283827 323707 := bstep (se 1 (by rfl) ⟨242780, by rfl⟩ : syracuseStep 323707 = 485561) B485561
theorem B5534081 : Blo 283827 5534081 := bstep (se 2 (by rfl) ⟨2075280, by rfl⟩ : syracuseStep 5534081 = 4150561) B4150561
theorem B1864225 : Blo 283827 1864225 := bstep (se 2 (by rfl) ⟨699084, by rfl⟩ : syracuseStep 1864225 = 1398169) B1398169
theorem B913979 : Blo 283827 913979 := bstep (se 1 (by rfl) ⟨685484, by rfl⟩ : syracuseStep 913979 = 1370969) B1370969
theorem B1077857 : Blo 283827 1077857 := bstep (se 2 (by rfl) ⟨404196, by rfl⟩ : syracuseStep 1077857 = 808393) B808393
theorem B1438721 : Blo 283827 1438721 := bstep (se 2 (by rfl) ⟨539520, by rfl⟩ : syracuseStep 1438721 = 1079041) B1079041
theorem B1635329 : Blo 283827 1635329 := bstep (se 2 (by rfl) ⟨613248, by rfl⟩ : syracuseStep 1635329 = 1226497) B1226497
theorem B456041 : Blo 283827 456041 := bstep (se 2 (by rfl) ⟨171015, by rfl⟩ : syracuseStep 456041 = 342031) B342031
theorem B1734061 : Blo 283827 1734061 := bstep (se 3 (by rfl) ⟨325136, by rfl⟩ : syracuseStep 1734061 = 650273) B650273
theorem B1635785 : Blo 283827 1635785 := bstep (se 2 (by rfl) ⟨613419, by rfl⟩ : syracuseStep 1635785 = 1226839) B1226839
theorem B6715061 : Blo 283827 6715061 := bstep (se 5 (by rfl) ⟨314768, by rfl⟩ : syracuseStep 6715061 = 629537) B629537
theorem B1439531 : Blo 283827 1439531 := bstep (se 1 (by rfl) ⟨1079648, by rfl⟩ : syracuseStep 1439531 = 2159297) B2159297
theorem B8222573 : Blo 283827 8222573 := bstep (se 3 (by rfl) ⟨1541732, by rfl⟩ : syracuseStep 8222573 = 3083465) B3083465
theorem B718753 : Blo 283827 718753 := bstep (se 2 (by rfl) ⟨269532, by rfl⟩ : syracuseStep 718753 = 539065) B539065
theorem B6944717 : Blo 283827 6944717 := bstep (se 3 (by rfl) ⟨1302134, by rfl⟩ : syracuseStep 6944717 = 2604269) B2604269
theorem B1079315 : Blo 283827 1079315 := bstep (se 1 (by rfl) ⟨809486, by rfl⟩ : syracuseStep 1079315 = 1618973) B1618973
theorem B2160755 : Blo 283827 2160755 := bstep (se 1 (by rfl) ⟨1620566, by rfl⟩ : syracuseStep 2160755 = 3241133) B3241133
theorem B4618397 : Blo 283827 4618397 := bstep (se 3 (by rfl) ⟨865949, by rfl⟩ : syracuseStep 4618397 = 1731899) B1731899
theorem B915799 : Blo 283827 915799 := bstep (se 1 (by rfl) ⟨686849, by rfl⟩ : syracuseStep 915799 = 1373699) B1373699
theorem B6977897 : Blo 283827 6977897 := bstep (se 2 (by rfl) ⟨2616711, by rfl⟩ : syracuseStep 6977897 = 5233423) B5233423
theorem B457579 : Blo 283827 457579 := bstep (se 1 (by rfl) ⟨343184, by rfl⟩ : syracuseStep 457579 = 686369) B686369
theorem B1015031 : Blo 283827 1015031 := bstep (se 1 (by rfl) ⟨761273, by rfl⟩ : syracuseStep 1015031 = 1522547) B1522547
theorem B3669239 : Blo 283827 3669239 := bstep (se 1 (by rfl) ⟨2751929, by rfl⟩ : syracuseStep 3669239 = 5503859) B5503859
theorem B1637927 : Blo 283827 1637927 := bstep (se 1 (by rfl) ⟨1228445, by rfl⟩ : syracuseStep 1637927 = 2456891) B2456891
theorem B1080971 : Blo 283827 1080971 := bstep (se 1 (by rfl) ⟨810728, by rfl⟩ : syracuseStep 1080971 = 1621457) B1621457
theorem B1376119 : Blo 283827 1376119 := bstep (se 1 (by rfl) ⟨1032089, by rfl⟩ : syracuseStep 1376119 = 2064179) B2064179
theorem B425903 : Blo 283827 425903 := bstep (se 1 (by rfl) ⟨319427, by rfl⟩ : syracuseStep 425903 = 638855) B638855
theorem B426089 : Blo 283827 426089 := bstep (se 2 (by rfl) ⟨159783, by rfl⟩ : syracuseStep 426089 = 319567) B319567
theorem B721001 : Blo 283827 721001 := bstep (se 2 (by rfl) ⟨270375, by rfl⟩ : syracuseStep 721001 = 540751) B540751
theorem B819305 : Blo 283827 819305 := bstep (se 2 (by rfl) ⟨307239, by rfl⟩ : syracuseStep 819305 = 614479) B614479
theorem B426407 : Blo 283827 426407 := bstep (se 1 (by rfl) ⟨319805, by rfl⟩ : syracuseStep 426407 = 639611) B639611
theorem B1081775 : Blo 283827 1081775 := bstep (se 1 (by rfl) ⟨811331, by rfl⟩ : syracuseStep 1081775 = 1622663) B1622663
theorem B426491 : Blo 283827 426491 := bstep (se 1 (by rfl) ⟨319868, by rfl⟩ : syracuseStep 426491 = 639737) B639737
theorem B918017 : Blo 283827 918017 := bstep (se 2 (by rfl) ⟨344256, by rfl⟩ : syracuseStep 918017 = 688513) B688513
theorem B721487 : Blo 283827 721487 := bstep (se 1 (by rfl) ⟨541115, by rfl⟩ : syracuseStep 721487 = 1082231) B1082231
theorem B426617 : Blo 283827 426617 := bstep (se 2 (by rfl) ⟨159981, by rfl⟩ : syracuseStep 426617 = 319963) B319963
theorem B426671 : Blo 283827 426671 := bstep (se 1 (by rfl) ⟨320003, by rfl⟩ : syracuseStep 426671 = 640007) B640007
theorem B426719 : Blo 283827 426719 := bstep (se 1 (by rfl) ⟨320039, by rfl⟩ : syracuseStep 426719 = 640079) B640079
theorem B4621049 : Blo 283827 4621049 := bstep (se 2 (by rfl) ⟨1732893, by rfl⟩ : syracuseStep 4621049 = 3465787) B3465787
theorem B426983 : Blo 283827 426983 := bstep (se 1 (by rfl) ⟨320237, by rfl⟩ : syracuseStep 426983 = 640475) B640475
theorem B722135 : Blo 283827 722135 := bstep (se 1 (by rfl) ⟨541601, by rfl⟩ : syracuseStep 722135 = 1083203) B1083203
theorem B427241 : Blo 283827 427241 := bstep (se 2 (by rfl) ⟨160215, by rfl⟩ : syracuseStep 427241 = 320431) B320431
theorem B5506319 : Blo 283827 5506319 := bstep (se 1 (by rfl) ⟨4129739, by rfl⟩ : syracuseStep 5506319 = 8259479) B8259479
theorem B427295 : Blo 283827 427295 := bstep (se 1 (by rfl) ⟨320471, by rfl⟩ : syracuseStep 427295 = 640943) B640943
theorem B2590001 : Blo 283827 2590001 := bstep (se 2 (by rfl) ⟨971250, by rfl⟩ : syracuseStep 2590001 = 1942501) B1942501
theorem B1082747 : Blo 283827 1082747 := bstep (se 1 (by rfl) ⟨812060, by rfl⟩ : syracuseStep 1082747 = 1624121) B1624121
theorem B2164157 : Blo 283827 2164157 := bstep (se 3 (by rfl) ⟨405779, by rfl⟩ : syracuseStep 2164157 = 811559) B811559
theorem B427463 : Blo 283827 427463 := bstep (se 1 (by rfl) ⟨320597, by rfl⟩ : syracuseStep 427463 = 641195) B641195
theorem B11142947 : Blo 283827 11142947 := bstep (se 1 (by rfl) ⟨8357210, by rfl⟩ : syracuseStep 11142947 = 16714421) B16714421
theorem B427817 : Blo 283827 427817 := bstep (se 2 (by rfl) ⟨160431, by rfl⟩ : syracuseStep 427817 = 320863) B320863
theorem B427823 : Blo 283827 427823 := bstep (se 1 (by rfl) ⟨320867, by rfl⟩ : syracuseStep 427823 = 641735) B641735
theorem B1378255 : Blo 283827 1378255 := bstep (se 1 (by rfl) ⟨1033691, by rfl⟩ : syracuseStep 1378255 = 2067383) B2067383
theorem B428297 : Blo 283827 428297 := bstep (se 2 (by rfl) ⟨160611, by rfl⟩ : syracuseStep 428297 = 321223) B321223
theorem B428399 : Blo 283827 428399 := bstep (se 1 (by rfl) ⟨321299, by rfl⟩ : syracuseStep 428399 = 642599) B642599
theorem B362875 : Blo 283827 362875 := bstep (se 1 (by rfl) ⟨272156, by rfl⟩ : syracuseStep 362875 = 544313) B544313
theorem B723451 : Blo 283827 723451 := bstep (se 1 (by rfl) ⟨542588, by rfl⟩ : syracuseStep 723451 = 1085177) B1085177
theorem B1444391 : Blo 283827 1444391 := bstep (se 1 (by rfl) ⟨1083293, by rfl⟩ : syracuseStep 1444391 = 2166587) B2166587
theorem B428615 : Blo 283827 428615 := bstep (se 1 (by rfl) ⟨321461, by rfl⟩ : syracuseStep 428615 = 642923) B642923
theorem B1378889 : Blo 283827 1378889 := bstep (se 2 (by rfl) ⟨517083, by rfl⟩ : syracuseStep 1378889 = 1034167) B1034167
theorem B428651 : Blo 283827 428651 := bstep (se 1 (by rfl) ⟨321488, by rfl⟩ : syracuseStep 428651 = 642977) B642977
theorem B723563 : Blo 283827 723563 := bstep (se 1 (by rfl) ⟨542672, by rfl⟩ : syracuseStep 723563 = 1085345) B1085345
theorem B822035 : Blo 283827 822035 := bstep (se 1 (by rfl) ⟨616526, by rfl⟩ : syracuseStep 822035 = 1233053) B1233053
theorem B428879 : Blo 283827 428879 := bstep (se 1 (by rfl) ⟨321659, by rfl⟩ : syracuseStep 428879 = 643319) B643319
theorem B429275 : Blo 283827 429275 := bstep (se 1 (by rfl) ⟨321956, by rfl⟩ : syracuseStep 429275 = 643913) B643913
theorem B724211 : Blo 283827 724211 := bstep (se 1 (by rfl) ⟨543158, by rfl⟩ : syracuseStep 724211 = 1086317) B1086317
theorem B429449 : Blo 283827 429449 := bstep (se 2 (by rfl) ⟨161043, by rfl⟩ : syracuseStep 429449 = 322087) B322087
theorem B363943 : Blo 283827 363943 := bstep (se 1 (by rfl) ⟨272957, by rfl⟩ : syracuseStep 363943 = 545915) B545915
theorem B1084859 : Blo 283827 1084859 := bstep (se 1 (by rfl) ⟨813644, by rfl⟩ : syracuseStep 1084859 = 1627289) B1627289
theorem B724423 : Blo 283827 724423 := bstep (se 1 (by rfl) ⟨543317, by rfl⟩ : syracuseStep 724423 = 1086635) B1086635
theorem B1216109 : Blo 283827 1216109 := bstep (se 3 (by rfl) ⟨228020, by rfl⟩ : syracuseStep 1216109 = 456041) B456041
theorem B429803 : Blo 283827 429803 := bstep (se 1 (by rfl) ⟨322352, by rfl⟩ : syracuseStep 429803 = 644705) B644705
theorem B364267 : Blo 283827 364267 := bstep (se 1 (by rfl) ⟨273200, by rfl⟩ : syracuseStep 364267 = 546401) B546401
theorem B430031 : Blo 283827 430031 := bstep (se 1 (by rfl) ⟨322523, by rfl⟩ : syracuseStep 430031 = 645047) B645047
theorem B430427 : Blo 283827 430427 := bstep (se 1 (by rfl) ⟨322820, by rfl⟩ : syracuseStep 430427 = 645641) B645641
theorem B1511905 : Blo 283827 1511905 := bstep (se 2 (by rfl) ⟨566964, by rfl⟩ : syracuseStep 1511905 = 1133929) B1133929
theorem B2331155 : Blo 283827 2331155 := bstep (se 1 (by rfl) ⟨1748366, by rfl⟩ : syracuseStep 2331155 = 3496733) B3496733
theorem B430655 : Blo 283827 430655 := bstep (se 1 (by rfl) ⟨322991, by rfl⟩ : syracuseStep 430655 = 645983) B645983
theorem B1446497 : Blo 283827 1446497 := bstep (se 2 (by rfl) ⟨542436, by rfl⟩ : syracuseStep 1446497 = 1084873) B1084873
theorem B430775 : Blo 283827 430775 := bstep (se 1 (by rfl) ⟨323081, by rfl⟩ : syracuseStep 430775 = 646163) B646163
theorem B1217375 : Blo 283827 1217375 := bstep (se 1 (by rfl) ⟨913031, by rfl⟩ : syracuseStep 1217375 = 1826063) B1826063
theorem B431003 : Blo 283827 431003 := bstep (se 1 (by rfl) ⟨323252, by rfl⟩ : syracuseStep 431003 = 646505) B646505
theorem B726155 : Blo 283827 726155 := bstep (se 1 (by rfl) ⟨544616, by rfl⟩ : syracuseStep 726155 = 1089233) B1089233
theorem B1447145 : Blo 283827 1447145 := bstep (se 2 (by rfl) ⟨542679, by rfl⟩ : syracuseStep 1447145 = 1085359) B1085359
theorem B431399 : Blo 283827 431399 := bstep (se 1 (by rfl) ⟨323549, by rfl⟩ : syracuseStep 431399 = 647099) B647099
theorem B726367 : Blo 283827 726367 := bstep (se 1 (by rfl) ⟨544775, by rfl⟩ : syracuseStep 726367 = 1089551) B1089551
theorem B431483 : Blo 283827 431483 := bstep (se 1 (by rfl) ⟨323612, by rfl⟩ : syracuseStep 431483 = 647225) B647225
theorem B1447307 : Blo 283827 1447307 := bstep (se 1 (by rfl) ⟨1085480, by rfl⟩ : syracuseStep 1447307 = 2170961) B2170961
theorem B1742219 : Blo 283827 1742219 := bstep (se 1 (by rfl) ⟨1306664, by rfl⟩ : syracuseStep 1742219 = 2613329) B2613329
theorem B2758049 : Blo 283827 2758049 := bstep (se 2 (by rfl) ⟨1034268, by rfl⟩ : syracuseStep 2758049 = 2068537) B2068537
theorem B431609 : Blo 283827 431609 := bstep (se 2 (by rfl) ⟨161853, by rfl⟩ : syracuseStep 431609 = 323707) B323707
theorem B431711 : Blo 283827 431711 := bstep (se 1 (by rfl) ⟨323783, by rfl⟩ : syracuseStep 431711 = 647567) B647567
theorem B2201879 : Blo 283827 2201879 := bstep (se 1 (by rfl) ⟨1651409, by rfl⟩ : syracuseStep 2201879 = 3302819) B3302819
theorem B1841591 : Blo 283827 1841591 := bstep (se 1 (by rfl) ⟨1381193, by rfl⟩ : syracuseStep 1841591 = 2762387) B2762387
theorem B1088063 : Blo 283827 1088063 := bstep (se 1 (by rfl) ⟨816047, by rfl⟩ : syracuseStep 1088063 = 1632095) B1632095
theorem B1219151 : Blo 283827 1219151 := bstep (se 1 (by rfl) ⟨914363, by rfl⟩ : syracuseStep 1219151 = 1828727) B1828727
theorem B5905003 : Blo 283827 5905003 := bstep (se 1 (by rfl) ⟨4428752, by rfl⟩ : syracuseStep 5905003 = 8857505) B8857505
theorem B727775 : Blo 283827 727775 := bstep (se 1 (by rfl) ⟨545831, by rfl⟩ : syracuseStep 727775 = 1091663) B1091663
theorem B1088275 : Blo 283827 1088275 := bstep (se 1 (by rfl) ⟨816206, by rfl⟩ : syracuseStep 1088275 = 1632413) B1632413
theorem B2202553 : Blo 283827 2202553 := bstep (se 2 (by rfl) ⟨825957, by rfl⟩ : syracuseStep 2202553 = 1651915) B1651915
theorem B1547531 : Blo 283827 1547531 := bstep (se 1 (by rfl) ⟨1160648, by rfl⟩ : syracuseStep 1547531 = 2321297) B2321297
theorem B1023329 : Blo 283827 1023329 := bstep (se 2 (by rfl) ⟨383748, by rfl⟩ : syracuseStep 1023329 = 767497) B767497
theorem B958067 : Blo 283827 958067 := bstep (se 1 (by rfl) ⟨718550, by rfl⟩ : syracuseStep 958067 = 1437101) B1437101
theorem B958337 : Blo 283827 958337 := bstep (se 2 (by rfl) ⟨359376, by rfl⟩ : syracuseStep 958337 = 718753) B718753
theorem B1221065 : Blo 283827 1221065 := bstep (se 2 (by rfl) ⟨457899, by rfl⟩ : syracuseStep 1221065 = 915799) B915799
theorem B1450547 : Blo 283827 1450547 := bstep (se 1 (by rfl) ⟨1087910, by rfl⟩ : syracuseStep 1450547 = 2175821) B2175821
theorem B959147 : Blo 283827 959147 := bstep (se 1 (by rfl) ⟨719360, by rfl⟩ : syracuseStep 959147 = 1438721) B1438721
theorem B1090219 : Blo 283827 1090219 := bstep (se 1 (by rfl) ⟨817664, by rfl⟩ : syracuseStep 1090219 = 1635329) B1635329
theorem B1024969 : Blo 283827 1024969 := bstep (se 2 (by rfl) ⟨384363, by rfl⟩ : syracuseStep 1024969 = 768727) B768727
theorem B1090523 : Blo 283827 1090523 := bstep (se 1 (by rfl) ⟨817892, by rfl⟩ : syracuseStep 1090523 = 1635785) B1635785
theorem B664615 : Blo 283827 664615 := bstep (se 1 (by rfl) ⟨498461, by rfl⟩ : syracuseStep 664615 = 996923) B996923
theorem B959687 : Blo 283827 959687 := bstep (se 1 (by rfl) ⟨719765, by rfl⟩ : syracuseStep 959687 = 1439531) B1439531
theorem B5481715 : Blo 283827 5481715 := bstep (se 1 (by rfl) ⟨4111286, by rfl⟩ : syracuseStep 5481715 = 8222573) B8222573
theorem B4629811 : Blo 283827 4629811 := bstep (se 1 (by rfl) ⟨3472358, by rfl⟩ : syracuseStep 4629811 = 6944717) B6944717
theorem B3679901 : Blo 283827 3679901 := bstep (se 3 (by rfl) ⟨689981, by rfl⟩ : syracuseStep 3679901 = 1379963) B1379963
theorem B4171601 : Blo 283827 4171601 := bstep (se 2 (by rfl) ⟨1564350, by rfl⟩ : syracuseStep 4171601 = 3128701) B3128701
theorem B1320887 : Blo 283827 1320887 := bstep (se 1 (by rfl) ⟨990665, by rfl⟩ : syracuseStep 1320887 = 1981331) B1981331
theorem B1452167 : Blo 283827 1452167 := bstep (se 1 (by rfl) ⟨1089125, by rfl⟩ : syracuseStep 1452167 = 2178251) B2178251
theorem B1091951 : Blo 283827 1091951 := bstep (se 1 (by rfl) ⟨818963, by rfl⟩ : syracuseStep 1091951 = 1637927) B1637927
theorem B961199 : Blo 283827 961199 := bstep (se 1 (by rfl) ⟨720899, by rfl⟩ : syracuseStep 961199 = 1441799) B1441799
theorem B961523 : Blo 283827 961523 := bstep (se 1 (by rfl) ⟨721142, by rfl⟩ : syracuseStep 961523 = 1442285) B1442285
theorem B732257 : Blo 283827 732257 := bstep (se 2 (by rfl) ⟨274596, by rfl⟩ : syracuseStep 732257 = 549193) B549193
theorem B5024987 : Blo 283827 5024987 := bstep (se 1 (by rfl) ⟨3768740, by rfl⟩ : syracuseStep 5024987 = 7537481) B7537481
theorem B962063 : Blo 283827 962063 := bstep (se 1 (by rfl) ⟨721547, by rfl⟩ : syracuseStep 962063 = 1443095) B1443095
theorem B4140811 : Blo 283827 4140811 := bstep (se 1 (by rfl) ⟨3105608, by rfl⟩ : syracuseStep 4140811 = 6211217) B6211217
theorem B307099 : Blo 283827 307099 := bstep (se 1 (by rfl) ⟨230324, by rfl⟩ : syracuseStep 307099 = 460649) B460649
theorem B1027997 : Blo 283827 1027997 := bstep (se 3 (by rfl) ⟨192749, by rfl⟩ : syracuseStep 1027997 = 385499) B385499
theorem B1224857 : Blo 283827 1224857 := bstep (se 2 (by rfl) ⟨459321, by rfl⟩ : syracuseStep 1224857 = 918643) B918643
theorem B3649967 : Blo 283827 3649967 := bstep (se 1 (by rfl) ⟨2737475, by rfl⟩ : syracuseStep 3649967 = 5474951) B5474951
theorem B963143 : Blo 283827 963143 := bstep (se 1 (by rfl) ⟨722357, by rfl⟩ : syracuseStep 963143 = 1444715) B1444715
theorem B1225439 : Blo 283827 1225439 := bstep (se 1 (by rfl) ⟨919079, by rfl⟩ : syracuseStep 1225439 = 1838159) B1838159
theorem B308047 : Blo 283827 308047 := bstep (se 1 (by rfl) ⟨231035, by rfl⟩ : syracuseStep 308047 = 462071) B462071
theorem B963575 : Blo 283827 963575 := bstep (se 1 (by rfl) ⟨722681, by rfl⟩ : syracuseStep 963575 = 1445363) B1445363
theorem B2307217 : Blo 283827 2307217 := bstep (se 2 (by rfl) ⟨865206, by rfl⟩ : syracuseStep 2307217 = 1730413) B1730413
theorem B1553651 : Blo 283827 1553651 := bstep (se 1 (by rfl) ⟨1165238, by rfl⟩ : syracuseStep 1553651 = 2330477) B2330477
theorem B341339 : Blo 283827 341339 := bstep (se 1 (by rfl) ⟨256004, by rfl⟩ : syracuseStep 341339 = 512009) B512009
theorem B1226123 : Blo 283827 1226123 := bstep (se 1 (by rfl) ⟨919592, by rfl⟩ : syracuseStep 1226123 = 1839185) B1839185
theorem B964439 : Blo 283827 964439 := bstep (se 1 (by rfl) ⟨723329, by rfl⟩ : syracuseStep 964439 = 1446659) B1446659
theorem B1456055 : Blo 283827 1456055 := bstep (se 1 (by rfl) ⟨1092041, by rfl⟩ : syracuseStep 1456055 = 2184083) B2184083
theorem B1456703 : Blo 283827 1456703 := bstep (se 1 (by rfl) ⟨1092527, by rfl⟩ : syracuseStep 1456703 = 2185055) B2185055
theorem B4209515 : Blo 283827 4209515 := bstep (se 1 (by rfl) ⟨3157136, by rfl⟩ : syracuseStep 4209515 = 6314273) B6314273
theorem B1457021 : Blo 283827 1457021 := bstep (se 3 (by rfl) ⟨273191, by rfl⟩ : syracuseStep 1457021 = 546383) B546383
theorem B965519 : Blo 283827 965519 := bstep (se 1 (by rfl) ⟨724139, by rfl⟩ : syracuseStep 965519 = 1448279) B1448279
theorem B1227899 : Blo 283827 1227899 := bstep (se 1 (by rfl) ⟨920924, by rfl⟩ : syracuseStep 1227899 = 1841849) B1841849
theorem B5291513 : Blo 283827 5291513 := bstep (se 2 (by rfl) ⟨1984317, by rfl⟩ : syracuseStep 5291513 = 3968635) B3968635
theorem B310879 : Blo 283827 310879 := bstep (se 1 (by rfl) ⟨233159, by rfl⟩ : syracuseStep 310879 = 466319) B466319
theorem B1621889 : Blo 283827 1621889 := bstep (se 2 (by rfl) ⟨608208, by rfl⟩ : syracuseStep 1621889 = 1216417) B1216417
theorem B343963 : Blo 283827 343963 := bstep (se 1 (by rfl) ⟨257972, by rfl⟩ : syracuseStep 343963 = 515945) B515945
theorem B638927 : Blo 283827 638927 := bstep (se 1 (by rfl) ⟨479195, by rfl⟩ : syracuseStep 638927 = 958391) B958391
theorem B2473993 : Blo 283827 2473993 := bstep (se 2 (by rfl) ⟨927747, by rfl⟩ : syracuseStep 2473993 = 1855495) B1855495
theorem B966761 : Blo 283827 966761 := bstep (se 2 (by rfl) ⟨362535, by rfl⟩ : syracuseStep 966761 = 725071) B725071
theorem B639305 : Blo 283827 639305 := bstep (se 2 (by rfl) ⟨239739, by rfl⟩ : syracuseStep 639305 = 479479) B479479
theorem B639323 : Blo 283827 639323 := bstep (se 1 (by rfl) ⟨479492, by rfl⟩ : syracuseStep 639323 = 958985) B958985
theorem B1229231 : Blo 283827 1229231 := bstep (se 1 (by rfl) ⟨921923, by rfl⟩ : syracuseStep 1229231 = 1843847) B1843847
theorem B606791 : Blo 283827 606791 := bstep (se 1 (by rfl) ⟨455093, by rfl⟩ : syracuseStep 606791 = 910187) B910187
theorem B9290375 : Blo 283827 9290375 := bstep (se 1 (by rfl) ⟨6967781, by rfl⟩ : syracuseStep 9290375 = 13935563) B13935563
theorem B441762497 : Blo 283827 441762497 := bstep (se 2 (by rfl) ⟨165660936, by rfl⟩ : syracuseStep 441762497 = 331321873) B331321873
theorem B639899 : Blo 283827 639899 := bstep (se 1 (by rfl) ⟨479924, by rfl⟩ : syracuseStep 639899 = 959849) B959849
theorem B967625 : Blo 283827 967625 := bstep (se 2 (by rfl) ⟨362859, by rfl⟩ : syracuseStep 967625 = 725719) B725719
theorem B1754075 : Blo 283827 1754075 := bstep (se 1 (by rfl) ⟨1315556, by rfl⟩ : syracuseStep 1754075 = 2631113) B2631113
theorem B640097 : Blo 283827 640097 := bstep (se 2 (by rfl) ⟨240036, by rfl⟩ : syracuseStep 640097 = 480073) B480073
theorem B967895 : Blo 283827 967895 := bstep (se 1 (by rfl) ⟨725921, by rfl⟩ : syracuseStep 967895 = 1451843) B1451843
theorem B836857 : Blo 283827 836857 := bstep (se 2 (by rfl) ⟨313821, by rfl⟩ : syracuseStep 836857 = 627643) B627643
theorem B640295 : Blo 283827 640295 := bstep (se 1 (by rfl) ⟨480221, by rfl⟩ : syracuseStep 640295 = 960443) B960443
theorem B640673 : Blo 283827 640673 := bstep (se 2 (by rfl) ⟨240252, by rfl⟩ : syracuseStep 640673 = 480505) B480505
theorem B542369 : Blo 283827 542369 := bstep (se 2 (by rfl) ⟨203388, by rfl⟩ : syracuseStep 542369 = 406777) B406777
theorem B607979 : Blo 283827 607979 := bstep (se 1 (by rfl) ⟨455984, by rfl⟩ : syracuseStep 607979 = 911969) B911969
theorem B2934605 : Blo 283827 2934605 := bstep (se 3 (by rfl) ⟨550238, by rfl⟩ : syracuseStep 2934605 = 1100477) B1100477
theorem B2312081 : Blo 283827 2312081 := bstep (se 2 (by rfl) ⟨867030, by rfl⟩ : syracuseStep 2312081 = 1734061) B1734061
theorem B641033 : Blo 283827 641033 := bstep (se 2 (by rfl) ⟨240387, by rfl⟩ : syracuseStep 641033 = 480775) B480775
theorem B2607299 : Blo 283827 2607299 := bstep (se 1 (by rfl) ⟨1955474, by rfl⟩ : syracuseStep 2607299 = 3910949) B3910949
theorem B26364149 : Blo 283827 26364149 := bstep (se 5 (by rfl) ⟨1235819, by rfl⟩ : syracuseStep 26364149 = 2471639) B2471639
theorem B1296751 : Blo 283827 1296751 := bstep (se 1 (by rfl) ⟨972563, by rfl⟩ : syracuseStep 1296751 = 1945127) B1945127
theorem B641447 : Blo 283827 641447 := bstep (se 1 (by rfl) ⟨481085, by rfl⟩ : syracuseStep 641447 = 962171) B962171
theorem B3459557 : Blo 283827 3459557 := bstep (se 4 (by rfl) ⟨324333, by rfl⟩ : syracuseStep 3459557 = 648667) B648667
theorem B641555 : Blo 283827 641555 := bstep (se 1 (by rfl) ⟨481166, by rfl⟩ : syracuseStep 641555 = 962333) B962333
theorem B641609 : Blo 283827 641609 := bstep (se 2 (by rfl) ⟨240603, by rfl⟩ : syracuseStep 641609 = 481207) B481207
theorem B3099383 : Blo 283827 3099383 := bstep (se 1 (by rfl) ⟨2324537, by rfl⟩ : syracuseStep 3099383 = 4649075) B4649075
theorem B3689387 : Blo 283827 3689387 := bstep (se 1 (by rfl) ⟨2767040, by rfl⟩ : syracuseStep 3689387 = 5534081) B5534081
theorem B642023 : Blo 283827 642023 := bstep (se 1 (by rfl) ⟨481517, by rfl⟩ : syracuseStep 642023 = 963035) B963035
theorem B609319 : Blo 283827 609319 := bstep (se 1 (by rfl) ⟨456989, by rfl⟩ : syracuseStep 609319 = 913979) B913979
theorem B969947 : Blo 283827 969947 := bstep (se 1 (by rfl) ⟨727460, by rfl⟩ : syracuseStep 969947 = 1454921) B1454921
theorem B1822013 : Blo 283827 1822013 := bstep (se 3 (by rfl) ⟨341627, by rfl⟩ : syracuseStep 1822013 = 683255) B683255
theorem B642401 : Blo 283827 642401 := bstep (se 2 (by rfl) ⟨240900, by rfl⟩ : syracuseStep 642401 = 481801) B481801
theorem B642491 : Blo 283827 642491 := bstep (se 1 (by rfl) ⟨481868, by rfl⟩ : syracuseStep 642491 = 963737) B963737
theorem B642617 : Blo 283827 642617 := bstep (se 2 (by rfl) ⟨240981, by rfl⟩ : syracuseStep 642617 = 481963) B481963
theorem B1560323 : Blo 283827 1560323 := bstep (se 1 (by rfl) ⟨1170242, by rfl⟩ : syracuseStep 1560323 = 2340485) B2340485
theorem B4476707 : Blo 283827 4476707 := bstep (se 1 (by rfl) ⟨3357530, by rfl⟩ : syracuseStep 4476707 = 6715061) B6715061
theorem B610105 : Blo 283827 610105 := bstep (se 2 (by rfl) ⟨228789, by rfl⟩ : syracuseStep 610105 = 457579) B457579
theorem B2084923 : Blo 283827 2084923 := bstep (se 1 (by rfl) ⟨1563692, by rfl⟩ : syracuseStep 2084923 = 3127385) B3127385
theorem B970811 : Blo 283827 970811 := bstep (se 1 (by rfl) ⟨728108, by rfl⟩ : syracuseStep 970811 = 1456217) B1456217
theorem B643283 : Blo 283827 643283 := bstep (se 1 (by rfl) ⟨482462, by rfl⟩ : syracuseStep 643283 = 964925) B964925
theorem B643337 : Blo 283827 643337 := bstep (se 2 (by rfl) ⟨241251, by rfl⟩ : syracuseStep 643337 = 482503) B482503
theorem B2740553 : Blo 283827 2740553 := bstep (se 2 (by rfl) ⟨1027707, by rfl⟩ : syracuseStep 2740553 = 2055415) B2055415
theorem B971081 : Blo 283827 971081 := bstep (se 2 (by rfl) ⟨364155, by rfl⟩ : syracuseStep 971081 = 728311) B728311
theorem B643553 : Blo 283827 643553 := bstep (se 2 (by rfl) ⟨241332, by rfl⟩ : syracuseStep 643553 = 482665) B482665
theorem B11686517 : Blo 283827 11686517 := bstep (se 5 (by rfl) ⟨547805, by rfl⟩ : syracuseStep 11686517 = 1095611) B1095611
theorem B1364627 : Blo 283827 1364627 := bstep (se 1 (by rfl) ⟨1023470, by rfl⟩ : syracuseStep 1364627 = 2046941) B2046941
theorem B643859 : Blo 283827 643859 := bstep (se 1 (by rfl) ⟨482894, by rfl⟩ : syracuseStep 643859 = 965789) B965789
theorem B1364779 : Blo 283827 1364779 := bstep (se 1 (by rfl) ⟨1023584, by rfl⟩ : syracuseStep 1364779 = 2047169) B2047169
theorem B676687 : Blo 283827 676687 := bstep (se 1 (by rfl) ⟨507515, by rfl⟩ : syracuseStep 676687 = 1015031) B1015031
theorem B2446159 : Blo 283827 2446159 := bstep (se 1 (by rfl) ⟨1834619, by rfl⟩ : syracuseStep 2446159 = 3669239) B3669239
theorem B644219 : Blo 283827 644219 := bstep (se 1 (by rfl) ⟨483164, by rfl⟩ : syracuseStep 644219 = 966329) B966329
theorem B1299655 : Blo 283827 1299655 := bstep (se 1 (by rfl) ⟨974741, by rfl⟩ : syracuseStep 1299655 = 1949483) B1949483
theorem B644345 : Blo 283827 644345 := bstep (se 2 (by rfl) ⟨241629, by rfl⟩ : syracuseStep 644345 = 483259) B483259
theorem B283935 : Blo 283827 283935 := bstep (se 1 (by rfl) ⟨212951, by rfl⟩ : syracuseStep 283935 = 425903) B425903
theorem B283995 : Blo 283827 283995 := bstep (se 1 (by rfl) ⟨212996, by rfl⟩ : syracuseStep 283995 = 425993) B425993
theorem B284015 : Blo 283827 284015 := bstep (se 1 (by rfl) ⟨213011, by rfl⟩ : syracuseStep 284015 = 426023) B426023
theorem B644489 : Blo 283827 644489 := bstep (se 2 (by rfl) ⟨241683, by rfl⟩ : syracuseStep 644489 = 483367) B483367
theorem B284071 : Blo 283827 284071 := bstep (se 1 (by rfl) ⟨213053, by rfl⟩ : syracuseStep 284071 = 426107) B426107
theorem B284155 : Blo 283827 284155 := bstep (se 1 (by rfl) ⟨213116, by rfl⟩ : syracuseStep 284155 = 426233) B426233
theorem B644615 : Blo 283827 644615 := bstep (se 1 (by rfl) ⟨483461, by rfl⟩ : syracuseStep 644615 = 966923) B966923
theorem B9655853 : Blo 283827 9655853 := bstep (se 3 (by rfl) ⟨1810472, by rfl⟩ : syracuseStep 9655853 = 3620945) B3620945
theorem B284223 : Blo 283827 284223 := bstep (se 1 (by rfl) ⟨213167, by rfl⟩ : syracuseStep 284223 = 426335) B426335
theorem B284231 : Blo 283827 284231 := bstep (se 1 (by rfl) ⟨213173, by rfl⟩ : syracuseStep 284231 = 426347) B426347
theorem B480863 : Blo 283827 480863 := bstep (se 1 (by rfl) ⟨360647, by rfl⟩ : syracuseStep 480863 = 721295) B721295
theorem B644795 : Blo 283827 644795 := bstep (se 1 (by rfl) ⟨483596, by rfl⟩ : syracuseStep 644795 = 967193) B967193
theorem B284383 : Blo 283827 284383 := bstep (se 1 (by rfl) ⟨213287, by rfl⟩ : syracuseStep 284383 = 426575) B426575
theorem B284463 : Blo 283827 284463 := bstep (se 1 (by rfl) ⟨213347, by rfl⟩ : syracuseStep 284463 = 426695) B426695
theorem B481079 : Blo 283827 481079 := bstep (se 1 (by rfl) ⟨360809, by rfl⟩ : syracuseStep 481079 = 721619) B721619
theorem B644921 : Blo 283827 644921 := bstep (se 2 (by rfl) ⟨241845, by rfl⟩ : syracuseStep 644921 = 483691) B483691
theorem B775993 : Blo 283827 775993 := bstep (se 2 (by rfl) ⟨290997, by rfl⟩ : syracuseStep 775993 = 581995) B581995
theorem B284571 : Blo 283827 284571 := bstep (se 1 (by rfl) ⟨213428, by rfl⟩ : syracuseStep 284571 = 426857) B426857
theorem B284623 : Blo 283827 284623 := bstep (se 1 (by rfl) ⟨213467, by rfl⟩ : syracuseStep 284623 = 426935) B426935
theorem B284647 : Blo 283827 284647 := bstep (se 1 (by rfl) ⟨213485, by rfl⟩ : syracuseStep 284647 = 426971) B426971
theorem B2447495 : Blo 283827 2447495 := bstep (se 1 (by rfl) ⟨1835621, by rfl⟩ : syracuseStep 2447495 = 3671243) B3671243
theorem B284959 : Blo 283827 284959 := bstep (se 1 (by rfl) ⟨213719, by rfl⟩ : syracuseStep 284959 = 427439) B427439
theorem B285019 : Blo 283827 285019 := bstep (se 1 (by rfl) ⟨213764, by rfl⟩ : syracuseStep 285019 = 427529) B427529
theorem B809327 : Blo 283827 809327 := bstep (se 1 (by rfl) ⟨606995, by rfl⟩ : syracuseStep 809327 = 1213991) B1213991
theorem B285039 : Blo 283827 285039 := bstep (se 1 (by rfl) ⟨213779, by rfl⟩ : syracuseStep 285039 = 427559) B427559
theorem B285095 : Blo 283827 285095 := bstep (se 1 (by rfl) ⟨213821, by rfl⟩ : syracuseStep 285095 = 427643) B427643
theorem B1464743 : Blo 283827 1464743 := bstep (se 1 (by rfl) ⟨1098557, by rfl⟩ : syracuseStep 1464743 = 2197115) B2197115
theorem B645551 : Blo 283827 645551 := bstep (se 1 (by rfl) ⟨484163, by rfl⟩ : syracuseStep 645551 = 968327) B968327
theorem B645587 : Blo 283827 645587 := bstep (se 1 (by rfl) ⟨484190, by rfl⟩ : syracuseStep 645587 = 968381) B968381
theorem B285179 : Blo 283827 285179 := bstep (se 1 (by rfl) ⟨213884, by rfl⟩ : syracuseStep 285179 = 427769) B427769
theorem B285247 : Blo 283827 285247 := bstep (se 1 (by rfl) ⟨213935, by rfl⟩ : syracuseStep 285247 = 427871) B427871
theorem B481855 : Blo 283827 481855 := bstep (se 1 (by rfl) ⟨361391, by rfl⟩ : syracuseStep 481855 = 722783) B722783
theorem B645695 : Blo 283827 645695 := bstep (se 1 (by rfl) ⟨484271, by rfl⟩ : syracuseStep 645695 = 968543) B968543
theorem B285255 : Blo 283827 285255 := bstep (se 1 (by rfl) ⟨213941, by rfl⟩ : syracuseStep 285255 = 427883) B427883
theorem B645803 : Blo 283827 645803 := bstep (se 1 (by rfl) ⟨484352, by rfl⟩ : syracuseStep 645803 = 968705) B968705
theorem B285407 : Blo 283827 285407 := bstep (se 1 (by rfl) ⟨214055, by rfl⟩ : syracuseStep 285407 = 428111) B428111
theorem B285487 : Blo 283827 285487 := bstep (se 1 (by rfl) ⟨214115, by rfl⟩ : syracuseStep 285487 = 428231) B428231
theorem B285595 : Blo 283827 285595 := bstep (se 1 (by rfl) ⟨214196, by rfl⟩ : syracuseStep 285595 = 428393) B428393
theorem B285647 : Blo 283827 285647 := bstep (se 1 (by rfl) ⟨214235, by rfl⟩ : syracuseStep 285647 = 428471) B428471
theorem B285671 : Blo 283827 285671 := bstep (se 1 (by rfl) ⟨214253, by rfl⟩ : syracuseStep 285671 = 428507) B428507
theorem B1105085 : Blo 283827 1105085 := bstep (se 3 (by rfl) ⟨207203, by rfl⟩ : syracuseStep 1105085 = 414407) B414407
theorem B646343 : Blo 283827 646343 := bstep (se 1 (by rfl) ⟨484757, by rfl⟩ : syracuseStep 646343 = 969515) B969515
theorem B482537 : Blo 283827 482537 := bstep (se 2 (by rfl) ⟨180951, by rfl⟩ : syracuseStep 482537 = 361903) B361903
theorem B482591 : Blo 283827 482591 := bstep (se 1 (by rfl) ⟨361943, by rfl⟩ : syracuseStep 482591 = 723887) B723887
theorem B285983 : Blo 283827 285983 := bstep (se 1 (by rfl) ⟨214487, by rfl⟩ : syracuseStep 285983 = 428975) B428975
theorem B286043 : Blo 283827 286043 := bstep (se 1 (by rfl) ⟨214532, by rfl⟩ : syracuseStep 286043 = 429065) B429065
theorem B286063 : Blo 283827 286063 := bstep (se 1 (by rfl) ⟨214547, by rfl⟩ : syracuseStep 286063 = 429095) B429095
theorem B646523 : Blo 283827 646523 := bstep (se 1 (by rfl) ⟨484892, by rfl⟩ : syracuseStep 646523 = 969785) B969785
theorem B286119 : Blo 283827 286119 := bstep (se 1 (by rfl) ⟨214589, by rfl⟩ : syracuseStep 286119 = 429179) B429179
theorem B646649 : Blo 283827 646649 := bstep (se 2 (by rfl) ⟨242493, by rfl⟩ : syracuseStep 646649 = 484987) B484987
theorem B286203 : Blo 283827 286203 := bstep (se 1 (by rfl) ⟨214652, by rfl⟩ : syracuseStep 286203 = 429305) B429305
theorem B286271 : Blo 283827 286271 := bstep (se 1 (by rfl) ⟨214703, by rfl⟩ : syracuseStep 286271 = 429407) B429407
theorem B286279 : Blo 283827 286279 := bstep (se 1 (by rfl) ⟨214709, by rfl⟩ : syracuseStep 286279 = 429419) B429419
theorem B646739 : Blo 283827 646739 := bstep (se 1 (by rfl) ⟨485054, by rfl⟩ : syracuseStep 646739 = 970109) B970109
theorem B286431 : Blo 283827 286431 := bstep (se 1 (by rfl) ⟨214823, by rfl⟩ : syracuseStep 286431 = 429647) B429647
theorem B646919 : Blo 283827 646919 := bstep (se 1 (by rfl) ⟨485189, by rfl⟩ : syracuseStep 646919 = 970379) B970379
theorem B286511 : Blo 283827 286511 := bstep (se 1 (by rfl) ⟨214883, by rfl⟩ : syracuseStep 286511 = 429767) B429767
theorem B319387 : Blo 283827 319387 := bstep (se 1 (by rfl) ⟨239540, by rfl⟩ : syracuseStep 319387 = 479081) B479081
theorem B286619 : Blo 283827 286619 := bstep (se 1 (by rfl) ⟨214964, by rfl⟩ : syracuseStep 286619 = 429929) B429929
theorem B286671 : Blo 283827 286671 := bstep (se 1 (by rfl) ⟨215003, by rfl⟩ : syracuseStep 286671 = 430007) B430007
theorem B286695 : Blo 283827 286695 := bstep (se 1 (by rfl) ⟨215021, by rfl⟩ : syracuseStep 286695 = 430043) B430043
theorem B287007 : Blo 283827 287007 := bstep (se 1 (by rfl) ⟨215255, by rfl⟩ : syracuseStep 287007 = 430511) B430511
theorem B319783 : Blo 283827 319783 := bstep (se 1 (by rfl) ⟨239837, by rfl⟩ : syracuseStep 319783 = 479675) B479675
theorem B287067 : Blo 283827 287067 := bstep (se 1 (by rfl) ⟨215300, by rfl⟩ : syracuseStep 287067 = 430601) B430601
theorem B319855 : Blo 283827 319855 := bstep (se 1 (by rfl) ⟨239891, by rfl⟩ : syracuseStep 319855 = 479783) B479783
theorem B287087 : Blo 283827 287087 := bstep (se 1 (by rfl) ⟨215315, by rfl⟩ : syracuseStep 287087 = 430631) B430631
theorem B647531 : Blo 283827 647531 := bstep (se 1 (by rfl) ⟨485648, by rfl⟩ : syracuseStep 647531 = 971297) B971297
theorem B287143 : Blo 283827 287143 := bstep (se 1 (by rfl) ⟨215357, by rfl⟩ : syracuseStep 287143 = 430715) B430715
theorem B287227 : Blo 283827 287227 := bstep (se 1 (by rfl) ⟨215420, by rfl⟩ : syracuseStep 287227 = 430841) B430841
theorem B287295 : Blo 283827 287295 := bstep (se 1 (by rfl) ⟨215471, by rfl⟩ : syracuseStep 287295 = 430943) B430943
theorem B320071 : Blo 283827 320071 := bstep (se 1 (by rfl) ⟨240053, by rfl⟩ : syracuseStep 320071 = 480107) B480107
theorem B287303 : Blo 283827 287303 := bstep (se 1 (by rfl) ⟨215477, by rfl⟩ : syracuseStep 287303 = 430955) B430955
theorem B483961 : Blo 283827 483961 := bstep (se 2 (by rfl) ⟨181485, by rfl⟩ : syracuseStep 483961 = 362971) B362971
theorem B2482859 : Blo 283827 2482859 := bstep (se 1 (by rfl) ⟨1862144, by rfl⟩ : syracuseStep 2482859 = 3724289) B3724289
theorem B484015 : Blo 283827 484015 := bstep (se 1 (by rfl) ⟨363011, by rfl⟩ : syracuseStep 484015 = 726023) B726023
theorem B287455 : Blo 283827 287455 := bstep (se 1 (by rfl) ⟨215591, by rfl⟩ : syracuseStep 287455 = 431183) B431183
theorem B287535 : Blo 283827 287535 := bstep (se 1 (by rfl) ⟨215651, by rfl⟩ : syracuseStep 287535 = 431303) B431303
theorem B287643 : Blo 283827 287643 := bstep (se 1 (by rfl) ⟨215732, by rfl⟩ : syracuseStep 287643 = 431465) B431465
theorem B1631137 : Blo 283827 1631137 := bstep (se 2 (by rfl) ⟨611676, by rfl⟩ : syracuseStep 1631137 = 1223353) B1223353
theorem B287695 : Blo 283827 287695 := bstep (se 1 (by rfl) ⟨215771, by rfl⟩ : syracuseStep 287695 = 431543) B431543
theorem B287719 : Blo 283827 287719 := bstep (se 1 (by rfl) ⟨215789, by rfl⟩ : syracuseStep 287719 = 431579) B431579
theorem B8185211 : Blo 283827 8185211 := bstep (se 1 (by rfl) ⟨6138908, by rfl⟩ : syracuseStep 8185211 = 12277817) B12277817
theorem B320935 : Blo 283827 320935 := bstep (se 1 (by rfl) ⟨240701, by rfl⟩ : syracuseStep 320935 = 481403) B481403
theorem B812551 : Blo 283827 812551 := bstep (se 1 (by rfl) ⟨609413, by rfl⟩ : syracuseStep 812551 = 1218827) B1218827
theorem B321511 : Blo 283827 321511 := bstep (se 1 (by rfl) ⟨241133, by rfl⟩ : syracuseStep 321511 = 482267) B482267
theorem B3074125 : Blo 283827 3074125 := bstep (se 3 (by rfl) ⟨576398, by rfl⟩ : syracuseStep 3074125 = 1152797) B1152797
theorem B3106993 : Blo 283827 3106993 := bstep (se 2 (by rfl) ⟨1165122, by rfl⟩ : syracuseStep 3106993 = 2330245) B2330245
theorem B2320649 : Blo 283827 2320649 := bstep (se 2 (by rfl) ⟨870243, by rfl⟩ : syracuseStep 2320649 = 1740487) B1740487
theorem B387337 : Blo 283827 387337 := bstep (se 2 (by rfl) ⟨145251, by rfl⟩ : syracuseStep 387337 = 290503) B290503
theorem B1468697 : Blo 283827 1468697 := bstep (se 2 (by rfl) ⟨550761, by rfl⟩ : syracuseStep 1468697 = 1101523) B1101523
theorem B911945 : Blo 283827 911945 := bstep (se 2 (by rfl) ⟨341979, by rfl⟩ : syracuseStep 911945 = 683959) B683959
theorem B4877009 : Blo 283827 4877009 := bstep (se 2 (by rfl) ⟨1828878, by rfl⟩ : syracuseStep 4877009 = 3657757) B3657757
theorem B1829699 : Blo 283827 1829699 := bstep (se 1 (by rfl) ⟨1372274, by rfl⟩ : syracuseStep 1829699 = 2744549) B2744549
theorem B2616131 : Blo 283827 2616131 := bstep (se 1 (by rfl) ⟨1962098, by rfl⟩ : syracuseStep 2616131 = 3924197) B3924197
theorem B1436939 : Blo 283827 1436939 := bstep (se 1 (by rfl) ⟨1077704, by rfl⟩ : syracuseStep 1436939 = 2155409) B2155409
theorem B2485633 : Blo 283827 2485633 := bstep (se 2 (by rfl) ⟨932112, by rfl⟩ : syracuseStep 2485633 = 1864225) B1864225
theorem B978425 : Blo 283827 978425 := bstep (se 2 (by rfl) ⟨366909, by rfl⟩ : syracuseStep 978425 = 733819) B733819
theorem B1404431 : Blo 283827 1404431 := bstep (se 1 (by rfl) ⟨1053323, by rfl⟩ : syracuseStep 1404431 = 2106647) B2106647
theorem B323167 : Blo 283827 323167 := bstep (se 1 (by rfl) ⟨242375, by rfl⟩ : syracuseStep 323167 = 484751) B484751
theorem B683831 : Blo 283827 683831 := bstep (se 1 (by rfl) ⟨512873, by rfl⟩ : syracuseStep 683831 = 1025747) B1025747
theorem B1535851 : Blo 283827 1535851 := bstep (se 1 (by rfl) ⟨1151888, by rfl⟩ : syracuseStep 1535851 = 2303777) B2303777
theorem B815113 : Blo 283827 815113 := bstep (se 2 (by rfl) ⟨305667, by rfl⟩ : syracuseStep 815113 = 611335) B611335
theorem B553225 : Blo 283827 553225 := bstep (se 2 (by rfl) ⟨207459, by rfl⟩ : syracuseStep 553225 = 414919) B414919
theorem B815467 : Blo 283827 815467 := bstep (se 1 (by rfl) ⟨611600, by rfl⟩ : syracuseStep 815467 = 1223201) B1223201
theorem B1438559 : Blo 283827 1438559 := bstep (se 1 (by rfl) ⟨1078919, by rfl⟩ : syracuseStep 1438559 = 2157839) B2157839
theorem B6222905 : Blo 283827 6222905 := bstep (se 2 (by rfl) ⟨2333589, by rfl⟩ : syracuseStep 6222905 = 4667179) B4667179
theorem B718571 : Blo 283827 718571 := bstep (se 1 (by rfl) ⟨538928, by rfl⟩ : syracuseStep 718571 = 1077857) B1077857
theorem B686291 : Blo 283827 686291 := bstep (se 1 (by rfl) ⟨514718, by rfl⟩ : syracuseStep 686291 = 1029437) B1029437
theorem B719543 : Blo 283827 719543 := bstep (se 1 (by rfl) ⟨539657, by rfl⟩ : syracuseStep 719543 = 1079315) B1079315
theorem B1440503 : Blo 283827 1440503 := bstep (se 1 (by rfl) ⟨1080377, by rfl⟩ : syracuseStep 1440503 = 2160755) B2160755
theorem B3078931 : Blo 283827 3078931 := bstep (se 1 (by rfl) ⟨2309198, by rfl⟩ : syracuseStep 3078931 = 4618397) B4618397
theorem B4651931 : Blo 283827 4651931 := bstep (se 1 (by rfl) ⟨3488948, by rfl⟩ : syracuseStep 4651931 = 6977897) B6977897
theorem B818075 : Blo 283827 818075 := bstep (se 1 (by rfl) ⟨613556, by rfl⟩ : syracuseStep 818075 = 1227113) B1227113
theorem B1440989 : Blo 283827 1440989 := bstep (se 3 (by rfl) ⟨270185, by rfl⟩ : syracuseStep 1440989 = 540371) B540371
theorem B818849 : Blo 283827 818849 := bstep (se 2 (by rfl) ⟨307068, by rfl⟩ : syracuseStep 818849 = 614137) B614137
theorem B720647 : Blo 283827 720647 := bstep (se 1 (by rfl) ⟨540485, by rfl⟩ : syracuseStep 720647 = 1080971) B1080971
theorem B425783 : Blo 283827 425783 := bstep (se 1 (by rfl) ⟨319337, by rfl⟩ : syracuseStep 425783 = 638675) B638675
theorem B720697 : Blo 283827 720697 := bstep (se 2 (by rfl) ⟨270261, by rfl⟩ : syracuseStep 720697 = 540523) B540523
theorem B1834825 : Blo 283827 1834825 := bstep (se 2 (by rfl) ⟨688059, by rfl⟩ : syracuseStep 1834825 = 1376119) B1376119
theorem B1474433 : Blo 283827 1474433 := bstep (se 2 (by rfl) ⟨552912, by rfl⟩ : syracuseStep 1474433 = 1105825) B1105825
theorem B426203 : Blo 283827 426203 := bstep (se 1 (by rfl) ⟨319652, by rfl⟩ : syracuseStep 426203 = 639305) B639305
theorem B426215 : Blo 283827 426215 := bstep (se 1 (by rfl) ⟨319661, by rfl⟩ : syracuseStep 426215 = 639323) B639323
theorem B721183 : Blo 283827 721183 := bstep (se 1 (by rfl) ⟨540887, by rfl⟩ : syracuseStep 721183 = 1081775) B1081775
theorem B819487 : Blo 283827 819487 := bstep (se 1 (by rfl) ⟨614615, by rfl⟩ : syracuseStep 819487 = 1229231) B1229231
theorem B426377 : Blo 283827 426377 := bstep (se 2 (by rfl) ⟨159891, by rfl⟩ : syracuseStep 426377 = 319783) B319783
theorem B6193583 : Blo 283827 6193583 := bstep (se 1 (by rfl) ⟨4645187, by rfl⟩ : syracuseStep 6193583 = 9290375) B9290375
theorem B426473 : Blo 283827 426473 := bstep (se 2 (by rfl) ⟨159927, by rfl⟩ : syracuseStep 426473 = 319855) B319855
theorem B3080699 : Blo 283827 3080699 := bstep (se 1 (by rfl) ⟨2310524, by rfl⟩ : syracuseStep 3080699 = 4621049) B4621049
theorem B426599 : Blo 283827 426599 := bstep (se 1 (by rfl) ⟨319949, by rfl⟩ : syracuseStep 426599 = 639899) B639899
theorem B426731 : Blo 283827 426731 := bstep (se 1 (by rfl) ⟨320048, by rfl⟩ : syracuseStep 426731 = 640097) B640097
theorem B426761 : Blo 283827 426761 := bstep (se 2 (by rfl) ⟨160035, by rfl⟩ : syracuseStep 426761 = 320071) B320071
theorem B3670879 : Blo 283827 3670879 := bstep (se 1 (by rfl) ⟨2753159, by rfl⟩ : syracuseStep 3670879 = 5506319) B5506319
theorem B426863 : Blo 283827 426863 := bstep (se 1 (by rfl) ⟨320147, by rfl⟩ : syracuseStep 426863 = 640295) B640295
theorem B721831 : Blo 283827 721831 := bstep (se 1 (by rfl) ⟨541373, by rfl⟩ : syracuseStep 721831 = 1082747) B1082747
theorem B1442771 : Blo 283827 1442771 := bstep (se 1 (by rfl) ⟨1082078, by rfl⟩ : syracuseStep 1442771 = 2164157) B2164157
theorem B427115 : Blo 283827 427115 := bstep (se 1 (by rfl) ⟨320336, by rfl⟩ : syracuseStep 427115 = 640673) B640673
theorem B361579 : Blo 283827 361579 := bstep (se 1 (by rfl) ⟨271184, by rfl⟩ : syracuseStep 361579 = 542369) B542369
theorem B1541387 : Blo 283827 1541387 := bstep (se 1 (by rfl) ⟨1156040, by rfl⟩ : syracuseStep 1541387 = 2312081) B2312081
theorem B427355 : Blo 283827 427355 := bstep (se 1 (by rfl) ⟨320516, by rfl⟩ : syracuseStep 427355 = 641033) B641033
theorem B886153 : Blo 283827 886153 := bstep (se 2 (by rfl) ⟨332307, by rfl⟩ : syracuseStep 886153 = 664615) B664615
theorem B1738199 : Blo 283827 1738199 := bstep (se 1 (by rfl) ⟨1303649, by rfl⟩ : syracuseStep 1738199 = 2607299) B2607299
theorem B427631 : Blo 283827 427631 := bstep (se 1 (by rfl) ⟨320723, by rfl⟩ : syracuseStep 427631 = 641447) B641447
theorem B7308953 : Blo 283827 7308953 := bstep (se 2 (by rfl) ⟨2740857, by rfl⟩ : syracuseStep 7308953 = 5481715) B5481715
theorem B427703 : Blo 283827 427703 := bstep (se 1 (by rfl) ⟨320777, by rfl⟩ : syracuseStep 427703 = 641555) B641555
theorem B427739 : Blo 283827 427739 := bstep (se 1 (by rfl) ⟨320804, by rfl⟩ : syracuseStep 427739 = 641609) B641609
theorem B919259 : Blo 283827 919259 := bstep (se 1 (by rfl) ⟨689444, by rfl⟩ : syracuseStep 919259 = 1378889) B1378889
theorem B6620957 : Blo 283827 6620957 := bstep (se 3 (by rfl) ⟨1241429, by rfl⟩ : syracuseStep 6620957 = 2482859) B2482859
theorem B2066255 : Blo 283827 2066255 := bstep (se 1 (by rfl) ⟨1549691, by rfl⟩ : syracuseStep 2066255 = 3099383) B3099383
theorem B427913 : Blo 283827 427913 := bstep (se 2 (by rfl) ⟨160467, by rfl⟩ : syracuseStep 427913 = 320935) B320935
theorem B2459591 : Blo 283827 2459591 := bstep (se 1 (by rfl) ⟨1844693, by rfl⟩ : syracuseStep 2459591 = 3689387) B3689387
theorem B428015 : Blo 283827 428015 := bstep (se 1 (by rfl) ⟨321011, by rfl⟩ : syracuseStep 428015 = 642023) B642023
theorem B1083401 : Blo 283827 1083401 := bstep (se 2 (by rfl) ⟨406275, by rfl⟩ : syracuseStep 1083401 = 812551) B812551
theorem B1214675 : Blo 283827 1214675 := bstep (se 1 (by rfl) ⟨911006, by rfl⟩ : syracuseStep 1214675 = 1822013) B1822013
theorem B428267 : Blo 283827 428267 := bstep (se 1 (by rfl) ⟨321200, by rfl⟩ : syracuseStep 428267 = 642401) B642401
theorem B428327 : Blo 283827 428327 := bstep (se 1 (by rfl) ⟨321245, by rfl⟩ : syracuseStep 428327 = 642491) B642491
theorem B723239 : Blo 283827 723239 := bstep (se 1 (by rfl) ⟨542429, by rfl⟩ : syracuseStep 723239 = 1084859) B1084859
theorem B428411 : Blo 283827 428411 := bstep (se 1 (by rfl) ⟨321308, by rfl⟩ : syracuseStep 428411 = 642617) B642617
theorem B2984471 : Blo 283827 2984471 := bstep (se 1 (by rfl) ⟨2238353, by rfl⟩ : syracuseStep 2984471 = 4476707) B4476707
theorem B1837673 : Blo 283827 1837673 := bstep (se 2 (by rfl) ⟨689127, by rfl⟩ : syracuseStep 1837673 = 1378255) B1378255
theorem B428681 : Blo 283827 428681 := bstep (se 2 (by rfl) ⟨160755, by rfl⟩ : syracuseStep 428681 = 321511) B321511
theorem B4098833 : Blo 283827 4098833 := bstep (se 2 (by rfl) ⟨1537062, by rfl⟩ : syracuseStep 4098833 = 3074125) B3074125
theorem B428855 : Blo 283827 428855 := bstep (se 1 (by rfl) ⟨321641, by rfl⟩ : syracuseStep 428855 = 643283) B643283
theorem B428891 : Blo 283827 428891 := bstep (se 1 (by rfl) ⟨321668, by rfl⟩ : syracuseStep 428891 = 643337) B643337
theorem B429035 : Blo 283827 429035 := bstep (se 1 (by rfl) ⟨321776, by rfl⟩ : syracuseStep 429035 = 643553) B643553
theorem B429239 : Blo 283827 429239 := bstep (se 1 (by rfl) ⟨321929, by rfl⟩ : syracuseStep 429239 = 643859) B643859
theorem B429479 : Blo 283827 429479 := bstep (se 1 (by rfl) ⟨322109, by rfl⟩ : syracuseStep 429479 = 644219) B644219
theorem B429563 : Blo 283827 429563 := bstep (se 1 (by rfl) ⟨322172, by rfl⟩ : syracuseStep 429563 = 644345) B644345
theorem B429659 : Blo 283827 429659 := bstep (se 1 (by rfl) ⟨322244, by rfl⟩ : syracuseStep 429659 = 644489) B644489
theorem B1838699 : Blo 283827 1838699 := bstep (se 1 (by rfl) ⟨1379024, by rfl⟩ : syracuseStep 1838699 = 2758049) B2758049
theorem B429743 : Blo 283827 429743 := bstep (se 1 (by rfl) ⟨322307, by rfl⟩ : syracuseStep 429743 = 644615) B644615
theorem B429863 : Blo 283827 429863 := bstep (se 1 (by rfl) ⟨322397, by rfl⟩ : syracuseStep 429863 = 644795) B644795
theorem B429947 : Blo 283827 429947 := bstep (se 1 (by rfl) ⟨322460, by rfl⟩ : syracuseStep 429947 = 644921) B644921
theorem B430367 : Blo 283827 430367 := bstep (se 1 (by rfl) ⟨322775, by rfl⟩ : syracuseStep 430367 = 645551) B645551
theorem B430391 : Blo 283827 430391 := bstep (se 1 (by rfl) ⟨322793, by rfl⟩ : syracuseStep 430391 = 645587) B645587
theorem B725375 : Blo 283827 725375 := bstep (se 1 (by rfl) ⟨544031, by rfl⟩ : syracuseStep 725375 = 1088063) B1088063
theorem B430463 : Blo 283827 430463 := bstep (se 1 (by rfl) ⟨322847, by rfl⟩ : syracuseStep 430463 = 645695) B645695
theorem B430535 : Blo 283827 430535 := bstep (se 1 (by rfl) ⟨322901, by rfl⟩ : syracuseStep 430535 = 645803) B645803
theorem B3314177 : Blo 283827 3314177 := bstep (se 2 (by rfl) ⟨1242816, by rfl⟩ : syracuseStep 3314177 = 2485633) B2485633
theorem B430889 : Blo 283827 430889 := bstep (se 2 (by rfl) ⟨161583, by rfl⟩ : syracuseStep 430889 = 323167) B323167
theorem B430895 : Blo 283827 430895 := bstep (se 1 (by rfl) ⟨323171, by rfl⟩ : syracuseStep 430895 = 646343) B646343
theorem B431015 : Blo 283827 431015 := bstep (se 1 (by rfl) ⟨323261, by rfl⟩ : syracuseStep 431015 = 646523) B646523
theorem B431099 : Blo 283827 431099 := bstep (se 1 (by rfl) ⟨323324, by rfl⟩ : syracuseStep 431099 = 646649) B646649
theorem B431159 : Blo 283827 431159 := bstep (se 1 (by rfl) ⟨323369, by rfl⟩ : syracuseStep 431159 = 646739) B646739
theorem B431279 : Blo 283827 431279 := bstep (se 1 (by rfl) ⟨323459, by rfl⟩ : syracuseStep 431279 = 646919) B646919
theorem B1086817 : Blo 283827 1086817 := bstep (se 2 (by rfl) ⟨407556, by rfl⟩ : syracuseStep 1086817 = 815113) B815113
theorem B431687 : Blo 283827 431687 := bstep (se 1 (by rfl) ⟨323765, by rfl⟩ : syracuseStep 431687 = 647531) B647531
theorem B1087289 : Blo 283827 1087289 := bstep (se 2 (by rfl) ⟨407733, by rfl⟩ : syracuseStep 1087289 = 815467) B815467
theorem B727015 : Blo 283827 727015 := bstep (se 1 (by rfl) ⟨545261, by rfl⟩ : syracuseStep 727015 = 1090523) B1090523
theorem B3905981 : Blo 283827 3905981 := bstep (se 3 (by rfl) ⟨732371, by rfl⟩ : syracuseStep 3905981 = 1464743) B1464743
theorem B4463237 : Blo 283827 4463237 := bstep (se 4 (by rfl) ⟨418428, by rfl⟩ : syracuseStep 4463237 = 836857) B836857
theorem B1547099 : Blo 283827 1547099 := bstep (se 1 (by rfl) ⟨1160324, by rfl⟩ : syracuseStep 1547099 = 2320649) B2320649
theorem B2431853 : Blo 283827 2431853 := bstep (se 3 (by rfl) ⟨455972, by rfl⟩ : syracuseStep 2431853 = 911945) B911945
theorem B727967 : Blo 283827 727967 := bstep (se 1 (by rfl) ⟨545975, by rfl⟩ : syracuseStep 727967 = 1091951) B1091951
theorem B3251339 : Blo 283827 3251339 := bstep (se 1 (by rfl) ⟨2438504, by rfl⟩ : syracuseStep 3251339 = 4877009) B4877009
theorem B1219799 : Blo 283827 1219799 := bstep (se 1 (by rfl) ⟨914849, by rfl⟩ : syracuseStep 1219799 = 1829699) B1829699
theorem B1744087 : Blo 283827 1744087 := bstep (se 1 (by rfl) ⟨1308065, by rfl⟩ : syracuseStep 1744087 = 2616131) B2616131
theorem B3349991 : Blo 283827 3349991 := bstep (se 1 (by rfl) ⟨2512493, by rfl⟩ : syracuseStep 3349991 = 5024987) B5024987
theorem B957959 : Blo 283827 957959 := bstep (se 1 (by rfl) ⟨718469, by rfl⟩ : syracuseStep 957959 = 1436939) B1436939
theorem B2433311 : Blo 283827 2433311 := bstep (se 1 (by rfl) ⟨1824983, by rfl⟩ : syracuseStep 2433311 = 3649967) B3649967
theorem B959039 : Blo 283827 959039 := bstep (se 1 (by rfl) ⟨719279, by rfl⟩ : syracuseStep 959039 = 1438559) B1438559
theorem B7873337 : Blo 283827 7873337 := bstep (se 2 (by rfl) ⟨2952501, by rfl⟩ : syracuseStep 7873337 = 5905003) B5905003
theorem B4105241 : Blo 283827 4105241 := bstep (se 2 (by rfl) ⟨1539465, by rfl⟩ : syracuseStep 4105241 = 3078931) B3078931
theorem B1451033 : Blo 283827 1451033 := bstep (se 2 (by rfl) ⟨544137, by rfl⟩ : syracuseStep 1451033 = 1088275) B1088275
theorem B960335 : Blo 283827 960335 := bstep (se 1 (by rfl) ⟨720251, by rfl⟩ : syracuseStep 960335 = 1440503) B1440503
theorem B960659 : Blo 283827 960659 := bstep (se 1 (by rfl) ⟨720494, by rfl⟩ : syracuseStep 960659 = 1440989) B1440989
theorem B960929 : Blo 283827 960929 := bstep (se 2 (by rfl) ⟨360348, by rfl⟩ : syracuseStep 960929 = 720697) B720697
theorem B11119589 : Blo 283827 11119589 := bstep (se 4 (by rfl) ⟨1042461, by rfl⟩ : syracuseStep 11119589 = 2084923) B2084923
theorem B404527 : Blo 283827 404527 := bstep (se 1 (by rfl) ⟨303395, by rfl⟩ : syracuseStep 404527 = 606791) B606791
theorem B1453625 : Blo 283827 1453625 := bstep (se 2 (by rfl) ⟨545109, by rfl⟩ : syracuseStep 1453625 = 1090219) B1090219
theorem B405319 : Blo 283827 405319 := bstep (se 1 (by rfl) ⟨303989, by rfl⟩ : syracuseStep 405319 = 607979) B607979
theorem B2174849 : Blo 283827 2174849 := bstep (se 2 (by rfl) ⟨815568, by rfl⟩ : syracuseStep 2174849 = 1631137) B1631137
theorem B17576099 : Blo 283827 17576099 := bstep (se 1 (by rfl) ⟨13182074, by rfl⟩ : syracuseStep 17576099 = 26364149) B26364149
theorem B962927 : Blo 283827 962927 := bstep (se 1 (by rfl) ⟨722195, by rfl⟩ : syracuseStep 962927 = 1444391) B1444391
theorem B6173081 : Blo 283827 6173081 := bstep (se 2 (by rfl) ⟨2314905, by rfl⟩ : syracuseStep 6173081 = 4629811) B4629811
theorem B4142657 : Blo 283827 4142657 := bstep (se 2 (by rfl) ⟨1553496, by rfl⟩ : syracuseStep 4142657 = 3106993) B3106993
theorem B1554103 : Blo 283827 1554103 := bstep (se 1 (by rfl) ⟨1165577, by rfl⟩ : syracuseStep 1554103 = 2331155) B2331155
theorem B964331 : Blo 283827 964331 := bstep (se 1 (by rfl) ⟨723248, by rfl⟩ : syracuseStep 964331 = 1446497) B1446497
theorem B964601 : Blo 283827 964601 := bstep (se 2 (by rfl) ⟨361725, by rfl⟩ : syracuseStep 964601 = 723451) B723451
theorem B964763 : Blo 283827 964763 := bstep (se 1 (by rfl) ⟨723572, by rfl⟩ : syracuseStep 964763 = 1447145) B1447145
theorem B964871 : Blo 283827 964871 := bstep (se 1 (by rfl) ⟨723653, by rfl⟩ : syracuseStep 964871 = 1447307) B1447307
theorem B1161479 : Blo 283827 1161479 := bstep (se 1 (by rfl) ⟨871109, by rfl⟩ : syracuseStep 1161479 = 1742219) B1742219
theorem B539551 : Blo 283827 539551 := bstep (se 1 (by rfl) ⟨404663, by rfl⟩ : syracuseStep 539551 = 809327) B809327
theorem B1227727 : Blo 283827 1227727 := bstep (se 1 (by rfl) ⟨920795, by rfl⟩ : syracuseStep 1227727 = 1841591) B1841591
theorem B965897 : Blo 283827 965897 := bstep (se 2 (by rfl) ⟨362211, by rfl⟩ : syracuseStep 965897 = 724423) B724423
theorem B736723 : Blo 283827 736723 := bstep (se 1 (by rfl) ⟨552542, by rfl⟩ : syracuseStep 736723 = 1105085) B1105085
theorem B1031687 : Blo 283827 1031687 := bstep (se 1 (by rfl) ⟨773765, by rfl⟩ : syracuseStep 1031687 = 1547531) B1547531
theorem B5521081 : Blo 283827 5521081 := bstep (se 2 (by rfl) ⟨2070405, by rfl⟩ : syracuseStep 5521081 = 4140811) B4140811
theorem B638711 : Blo 283827 638711 := bstep (se 1 (by rfl) ⟨479033, by rfl⟩ : syracuseStep 638711 = 958067) B958067
theorem B409465 : Blo 283827 409465 := bstep (se 2 (by rfl) ⟨153549, by rfl⟩ : syracuseStep 409465 = 307099) B307099
theorem B638891 : Blo 283827 638891 := bstep (se 1 (by rfl) ⟨479168, by rfl⟩ : syracuseStep 638891 = 958337) B958337
theorem B737633 : Blo 283827 737633 := bstep (se 2 (by rfl) ⟨276612, by rfl⟩ : syracuseStep 737633 = 553225) B553225
theorem B967031 : Blo 283827 967031 := bstep (se 1 (by rfl) ⟨725273, by rfl⟩ : syracuseStep 967031 = 1450547) B1450547
theorem B639431 : Blo 283827 639431 := bstep (se 1 (by rfl) ⟨479573, by rfl⟩ : syracuseStep 639431 = 959147) B959147
theorem B2015873 : Blo 283827 2015873 := bstep (se 2 (by rfl) ⟨755952, by rfl⟩ : syracuseStep 2015873 = 1511905) B1511905
theorem B3916525 : Blo 283827 3916525 := bstep (se 3 (by rfl) ⟨734348, by rfl⟩ : syracuseStep 3916525 = 1468697) B1468697
theorem B639791 : Blo 283827 639791 := bstep (se 1 (by rfl) ⟨479843, by rfl⟩ : syracuseStep 639791 = 959687) B959687
theorem B5456807 : Blo 283827 5456807 := bstep (se 1 (by rfl) ⟨4092605, by rfl⟩ : syracuseStep 5456807 = 8185211) B8185211
theorem B6931493 : Blo 283827 6931493 := bstep (se 4 (by rfl) ⟨649827, by rfl⟩ : syracuseStep 6931493 = 1299655) B1299655
theorem B1819705 : Blo 283827 1819705 := bstep (se 2 (by rfl) ⟨682389, by rfl⟩ : syracuseStep 1819705 = 1364779) B1364779
theorem B410729 : Blo 283827 410729 := bstep (se 2 (by rfl) ⟨154023, by rfl⟩ : syracuseStep 410729 = 308047) B308047
theorem B902249 : Blo 283827 902249 := bstep (se 2 (by rfl) ⟨338343, by rfl⟩ : syracuseStep 902249 = 676687) B676687
theorem B3261545 : Blo 283827 3261545 := bstep (se 2 (by rfl) ⟨1223079, by rfl⟩ : syracuseStep 3261545 = 2446159) B2446159
theorem B9225485 : Blo 283827 9225485 := bstep (se 3 (by rfl) ⟨1729778, by rfl⟩ : syracuseStep 9225485 = 3459557) B3459557
theorem B968111 : Blo 283827 968111 := bstep (se 1 (by rfl) ⟨726083, by rfl⟩ : syracuseStep 968111 = 1452167) B1452167
theorem B640799 : Blo 283827 640799 := bstep (se 1 (by rfl) ⟨480599, by rfl⟩ : syracuseStep 640799 = 961199) B961199
theorem B968489 : Blo 283827 968489 := bstep (se 2 (by rfl) ⟨363183, by rfl⟩ : syracuseStep 968489 = 726367) B726367
theorem B641015 : Blo 283827 641015 := bstep (se 1 (by rfl) ⟨480761, by rfl⟩ : syracuseStep 641015 = 961523) B961523
theorem B936287 : Blo 283827 936287 := bstep (se 1 (by rfl) ⟨702215, by rfl⟩ : syracuseStep 936287 = 1404431) B1404431
theorem B641375 : Blo 283827 641375 := bstep (se 1 (by rfl) ⟨481031, by rfl⟩ : syracuseStep 641375 = 962063) B962063
theorem B1034657 : Blo 283827 1034657 := bstep (se 2 (by rfl) ⟨387996, by rfl⟩ : syracuseStep 1034657 = 775993) B775993
theorem B642095 : Blo 283827 642095 := bstep (se 1 (by rfl) ⟨481571, by rfl⟩ : syracuseStep 642095 = 963143) B963143
theorem B642383 : Blo 283827 642383 := bstep (se 1 (by rfl) ⟨481787, by rfl⟩ : syracuseStep 642383 = 963575) B963575
theorem B4148603 : Blo 283827 4148603 := bstep (se 1 (by rfl) ⟨3111452, by rfl⟩ : syracuseStep 4148603 = 6222905) B6222905
theorem B642473 : Blo 283827 642473 := bstep (se 2 (by rfl) ⟨240927, by rfl⟩ : syracuseStep 642473 = 481855) B481855
theorem B1035767 : Blo 283827 1035767 := bstep (se 1 (by rfl) ⟨776825, by rfl⟩ : syracuseStep 1035767 = 1553651) B1553651
theorem B479047 : Blo 283827 479047 := bstep (se 1 (by rfl) ⟨359285, by rfl⟩ : syracuseStep 479047 = 718571) B718571
theorem B642959 : Blo 283827 642959 := bstep (se 1 (by rfl) ⟨482219, by rfl⟩ : syracuseStep 642959 = 964439) B964439
theorem B2936737 : Blo 283827 2936737 := bstep (se 2 (by rfl) ⟨1101276, by rfl⟩ : syracuseStep 2936737 = 2202553) B2202553
theorem B970703 : Blo 283827 970703 := bstep (se 1 (by rfl) ⟨728027, by rfl⟩ : syracuseStep 970703 = 1456055) B1456055
theorem B971135 : Blo 283827 971135 := bstep (se 1 (by rfl) ⟨728351, by rfl⟩ : syracuseStep 971135 = 1456703) B1456703
theorem B2183597 : Blo 283827 2183597 := bstep (se 3 (by rfl) ⟨409424, by rfl⟩ : syracuseStep 2183597 = 818849) B818849
theorem B479695 : Blo 283827 479695 := bstep (se 1 (by rfl) ⟨359771, by rfl⟩ : syracuseStep 479695 = 719543) B719543
theorem B2806343 : Blo 283827 2806343 := bstep (se 1 (by rfl) ⟨2104757, by rfl⟩ : syracuseStep 2806343 = 4209515) B4209515
theorem B971347 : Blo 283827 971347 := bstep (se 1 (by rfl) ⟨728510, by rfl⟩ : syracuseStep 971347 = 1457021) B1457021
theorem B643679 : Blo 283827 643679 := bstep (se 1 (by rfl) ⟨482759, by rfl⟩ : syracuseStep 643679 = 965519) B965519
theorem B3101287 : Blo 283827 3101287 := bstep (se 1 (by rfl) ⟨2325965, by rfl⟩ : syracuseStep 3101287 = 4651931) B4651931
theorem B545383 : Blo 283827 545383 := bstep (se 1 (by rfl) ⟨409037, by rfl⟩ : syracuseStep 545383 = 818075) B818075
theorem B414505 : Blo 283827 414505 := bstep (se 2 (by rfl) ⟨155439, by rfl⟩ : syracuseStep 414505 = 310879) B310879
theorem B3527675 : Blo 283827 3527675 := bstep (se 1 (by rfl) ⟨2645756, by rfl⟩ : syracuseStep 3527675 = 5291513) B5291513
theorem B2446433 : Blo 283827 2446433 := bstep (se 2 (by rfl) ⟨917412, by rfl⟩ : syracuseStep 2446433 = 1834825) B1834825
theorem B480431 : Blo 283827 480431 := bstep (se 1 (by rfl) ⟨360323, by rfl⟩ : syracuseStep 480431 = 720647) B720647
theorem B283855 : Blo 283827 283855 := bstep (se 1 (by rfl) ⟨212891, by rfl⟩ : syracuseStep 283855 = 425783) B425783
theorem B3298657 : Blo 283827 3298657 := bstep (se 2 (by rfl) ⟨1236996, by rfl⟩ : syracuseStep 3298657 = 2473993) B2473993
theorem B284059 : Blo 283827 284059 := bstep (se 1 (by rfl) ⟨213044, by rfl⟩ : syracuseStep 284059 = 426089) B426089
theorem B480667 : Blo 283827 480667 := bstep (se 1 (by rfl) ⟨360500, by rfl⟩ : syracuseStep 480667 = 721001) B721001
theorem B644507 : Blo 283827 644507 := bstep (se 1 (by rfl) ⟨483380, by rfl⟩ : syracuseStep 644507 = 966761) B966761
theorem B546203 : Blo 283827 546203 := bstep (se 1 (by rfl) ⟨409652, by rfl⟩ : syracuseStep 546203 = 819305) B819305
theorem B284271 : Blo 283827 284271 := bstep (se 1 (by rfl) ⟨213203, by rfl⟩ : syracuseStep 284271 = 426407) B426407
theorem B284327 : Blo 283827 284327 := bstep (se 1 (by rfl) ⟨213245, by rfl⟩ : syracuseStep 284327 = 426491) B426491
theorem B612011 : Blo 283827 612011 := bstep (se 1 (by rfl) ⟨459008, by rfl⟩ : syracuseStep 612011 = 918017) B918017
theorem B480991 : Blo 283827 480991 := bstep (se 1 (by rfl) ⟨360743, by rfl⟩ : syracuseStep 480991 = 721487) B721487
theorem B284411 : Blo 283827 284411 := bstep (se 1 (by rfl) ⟨213308, by rfl⟩ : syracuseStep 284411 = 426617) B426617
theorem B284447 : Blo 283827 284447 := bstep (se 1 (by rfl) ⟨213335, by rfl⟩ : syracuseStep 284447 = 426671) B426671
theorem B294508331 : Blo 283827 294508331 := bstep (se 1 (by rfl) ⟨220881248, by rfl⟩ : syracuseStep 294508331 = 441762497) B441762497
theorem B284479 : Blo 283827 284479 := bstep (se 1 (by rfl) ⟨213359, by rfl⟩ : syracuseStep 284479 = 426719) B426719
theorem B645083 : Blo 283827 645083 := bstep (se 1 (by rfl) ⟨483812, by rfl⟩ : syracuseStep 645083 = 967625) B967625
theorem B1169383 : Blo 283827 1169383 := bstep (se 1 (by rfl) ⟨877037, by rfl⟩ : syracuseStep 1169383 = 1754075) B1754075
theorem B284655 : Blo 283827 284655 := bstep (se 1 (by rfl) ⟨213491, by rfl⟩ : syracuseStep 284655 = 426983) B426983
theorem B481423 : Blo 283827 481423 := bstep (se 1 (by rfl) ⟨361067, by rfl⟩ : syracuseStep 481423 = 722135) B722135
theorem B645263 : Blo 283827 645263 := bstep (se 1 (by rfl) ⟨483947, by rfl⟩ : syracuseStep 645263 = 967895) B967895
theorem B284827 : Blo 283827 284827 := bstep (se 1 (by rfl) ⟨213620, by rfl⟩ : syracuseStep 284827 = 427241) B427241
theorem B645281 : Blo 283827 645281 := bstep (se 2 (by rfl) ⟨241980, by rfl⟩ : syracuseStep 645281 = 483961) B483961
theorem B284863 : Blo 283827 284863 := bstep (se 1 (by rfl) ⟨213647, by rfl⟩ : syracuseStep 284863 = 427295) B427295
theorem B1726667 : Blo 283827 1726667 := bstep (se 1 (by rfl) ⟨1295000, by rfl⟩ : syracuseStep 1726667 = 2590001) B2590001
theorem B645353 : Blo 283827 645353 := bstep (se 2 (by rfl) ⟨242007, by rfl⟩ : syracuseStep 645353 = 484015) B484015
theorem B284975 : Blo 283827 284975 := bstep (se 1 (by rfl) ⟨213731, by rfl⟩ : syracuseStep 284975 = 427463) B427463
theorem B7428631 : Blo 283827 7428631 := bstep (se 1 (by rfl) ⟨5571473, by rfl⟩ : syracuseStep 7428631 = 11142947) B11142947
theorem B285211 : Blo 283827 285211 := bstep (se 1 (by rfl) ⟨213908, by rfl⟩ : syracuseStep 285211 = 427817) B427817
theorem B285215 : Blo 283827 285215 := bstep (se 1 (by rfl) ⟨213911, by rfl⟩ : syracuseStep 285215 = 427823) B427823
theorem B1956403 : Blo 283827 1956403 := bstep (se 1 (by rfl) ⟨1467302, by rfl⟩ : syracuseStep 1956403 = 2934605) B2934605
theorem B1366625 : Blo 283827 1366625 := bstep (se 2 (by rfl) ⟨512484, by rfl⟩ : syracuseStep 1366625 = 1024969) B1024969
theorem B285531 : Blo 283827 285531 := bstep (se 1 (by rfl) ⟨214148, by rfl⟩ : syracuseStep 285531 = 428297) B428297
theorem B285599 : Blo 283827 285599 := bstep (se 1 (by rfl) ⟨214199, by rfl⟩ : syracuseStep 285599 = 428399) B428399
theorem B285743 : Blo 283827 285743 := bstep (se 1 (by rfl) ⟨214307, by rfl⟩ : syracuseStep 285743 = 428615) B428615
theorem B285767 : Blo 283827 285767 := bstep (se 1 (by rfl) ⟨214325, by rfl⟩ : syracuseStep 285767 = 428651) B428651
theorem B482375 : Blo 283827 482375 := bstep (se 1 (by rfl) ⟨361781, by rfl⟩ : syracuseStep 482375 = 723563) B723563
theorem B285919 : Blo 283827 285919 := bstep (se 1 (by rfl) ⟨214439, by rfl⟩ : syracuseStep 285919 = 428879) B428879
theorem B286183 : Blo 283827 286183 := bstep (se 1 (by rfl) ⟨214637, by rfl⟩ : syracuseStep 286183 = 429275) B429275
theorem B646631 : Blo 283827 646631 := bstep (se 1 (by rfl) ⟨484973, by rfl⟩ : syracuseStep 646631 = 969947) B969947
theorem B482807 : Blo 283827 482807 := bstep (se 1 (by rfl) ⟨362105, by rfl⟩ : syracuseStep 482807 = 724211) B724211
theorem B286299 : Blo 283827 286299 := bstep (se 1 (by rfl) ⟨214724, by rfl⟩ : syracuseStep 286299 = 429449) B429449
theorem B810739 : Blo 283827 810739 := bstep (se 1 (by rfl) ⟨608054, by rfl⟩ : syracuseStep 810739 = 1216109) B1216109
theorem B286535 : Blo 283827 286535 := bstep (se 1 (by rfl) ⟨214901, by rfl⟩ : syracuseStep 286535 = 429803) B429803
theorem B1040215 : Blo 283827 1040215 := bstep (se 1 (by rfl) ⟨780161, by rfl⟩ : syracuseStep 1040215 = 1560323) B1560323
theorem B286687 : Blo 283827 286687 := bstep (se 1 (by rfl) ⟨215015, by rfl⟩ : syracuseStep 286687 = 430031) B430031
theorem B647207 : Blo 283827 647207 := bstep (se 1 (by rfl) ⟨485405, by rfl⟩ : syracuseStep 647207 = 970811) B970811
theorem B1827035 : Blo 283827 1827035 := bstep (se 1 (by rfl) ⟨1370276, by rfl⟩ : syracuseStep 1827035 = 2740553) B2740553
theorem B647387 : Blo 283827 647387 := bstep (se 1 (by rfl) ⟨485540, by rfl⟩ : syracuseStep 647387 = 971081) B971081
theorem B286951 : Blo 283827 286951 := bstep (se 1 (by rfl) ⟨215213, by rfl⟩ : syracuseStep 286951 = 430427) B430427
theorem B516449 : Blo 283827 516449 := bstep (se 2 (by rfl) ⟨193668, by rfl⟩ : syracuseStep 516449 = 387337) B387337
theorem B287103 : Blo 283827 287103 := bstep (se 1 (by rfl) ⟨215327, by rfl⟩ : syracuseStep 287103 = 430655) B430655
theorem B7791011 : Blo 283827 7791011 := bstep (se 1 (by rfl) ⟨5843258, by rfl⟩ : syracuseStep 7791011 = 11686517) B11686517
theorem B909751 : Blo 283827 909751 := bstep (se 1 (by rfl) ⟨682313, by rfl⟩ : syracuseStep 909751 = 1364627) B1364627
theorem B287183 : Blo 283827 287183 := bstep (se 1 (by rfl) ⟨215387, by rfl⟩ : syracuseStep 287183 = 430775) B430775
theorem B1729001 : Blo 283827 1729001 := bstep (se 2 (by rfl) ⟨648375, by rfl⟩ : syracuseStep 1729001 = 1296751) B1296751
theorem B483833 : Blo 283827 483833 := bstep (se 2 (by rfl) ⟨181437, by rfl⟩ : syracuseStep 483833 = 362875) B362875
theorem B811583 : Blo 283827 811583 := bstep (se 1 (by rfl) ⟨608687, by rfl⟩ : syracuseStep 811583 = 1217375) B1217375
theorem B287335 : Blo 283827 287335 := bstep (se 1 (by rfl) ⟨215501, by rfl⟩ : syracuseStep 287335 = 431003) B431003
theorem B484103 : Blo 283827 484103 := bstep (se 1 (by rfl) ⟨363077, by rfl⟩ : syracuseStep 484103 = 726155) B726155
theorem B287599 : Blo 283827 287599 := bstep (se 1 (by rfl) ⟨215699, by rfl⟩ : syracuseStep 287599 = 431399) B431399
theorem B910237 : Blo 283827 910237 := bstep (se 3 (by rfl) ⟨170669, by rfl⟩ : syracuseStep 910237 = 341339) B341339
theorem B287655 : Blo 283827 287655 := bstep (se 1 (by rfl) ⟨215741, by rfl⟩ : syracuseStep 287655 = 431483) B431483
theorem B287739 : Blo 283827 287739 := bstep (se 1 (by rfl) ⟨215804, by rfl⟩ : syracuseStep 287739 = 431609) B431609
theorem B320575 : Blo 283827 320575 := bstep (se 1 (by rfl) ⟨240431, by rfl⟩ : syracuseStep 320575 = 480863) B480863
theorem B287807 : Blo 283827 287807 := bstep (se 1 (by rfl) ⟨215855, by rfl⟩ : syracuseStep 287807 = 431711) B431711
theorem B320719 : Blo 283827 320719 := bstep (se 1 (by rfl) ⟨240539, by rfl⟩ : syracuseStep 320719 = 481079) B481079
theorem B812425 : Blo 283827 812425 := bstep (se 2 (by rfl) ⟨304659, by rfl⟩ : syracuseStep 812425 = 609319) B609319
theorem B1631663 : Blo 283827 1631663 := bstep (se 1 (by rfl) ⟨1223747, by rfl⟩ : syracuseStep 1631663 = 2447495) B2447495
theorem B25748941 : Blo 283827 25748941 := bstep (se 3 (by rfl) ⟨4827926, by rfl⟩ : syracuseStep 25748941 = 9655853) B9655853
theorem B1467919 : Blo 283827 1467919 := bstep (se 1 (by rfl) ⟨1100939, by rfl⟩ : syracuseStep 1467919 = 2201879) B2201879
theorem B812767 : Blo 283827 812767 := bstep (se 1 (by rfl) ⟨609575, by rfl⟩ : syracuseStep 812767 = 1219151) B1219151
theorem B485183 : Blo 283827 485183 := bstep (se 1 (by rfl) ⟨363887, by rfl⟩ : syracuseStep 485183 = 727775) B727775
theorem B485257 : Blo 283827 485257 := bstep (se 2 (by rfl) ⟨181971, by rfl⟩ : syracuseStep 485257 = 363943) B363943
theorem B321691 : Blo 283827 321691 := bstep (se 1 (by rfl) ⟨241268, by rfl⟩ : syracuseStep 321691 = 482537) B482537
theorem B321727 : Blo 283827 321727 := bstep (se 1 (by rfl) ⟨241295, by rfl⟩ : syracuseStep 321727 = 482591) B482591
theorem B682219 : Blo 283827 682219 := bstep (se 1 (by rfl) ⟨511664, by rfl⟩ : syracuseStep 682219 = 1023329) B1023329
theorem B485689 : Blo 283827 485689 := bstep (se 2 (by rfl) ⟨182133, by rfl⟩ : syracuseStep 485689 = 364267) B364267
theorem B813473 : Blo 283827 813473 := bstep (se 2 (by rfl) ⟨305052, by rfl⟩ : syracuseStep 813473 = 610105) B610105
theorem B814043 : Blo 283827 814043 := bstep (se 1 (by rfl) ⟨610532, by rfl⟩ : syracuseStep 814043 = 1221065) B1221065
theorem B1830109 : Blo 283827 1830109 := bstep (se 3 (by rfl) ⟨343145, by rfl⟩ : syracuseStep 1830109 = 686291) B686291
theorem B2453267 : Blo 283827 2453267 := bstep (se 1 (by rfl) ⟨1839950, by rfl⟩ : syracuseStep 2453267 = 3679901) B3679901
theorem B2781067 : Blo 283827 2781067 := bstep (se 1 (by rfl) ⟨2085800, by rfl⟩ : syracuseStep 2781067 = 4171601) B4171601
theorem B880591 : Blo 283827 880591 := bstep (se 1 (by rfl) ⟨660443, by rfl⟩ : syracuseStep 880591 = 1320887) B1320887
theorem B3076289 : Blo 283827 3076289 := bstep (se 2 (by rfl) ⟨1153608, by rfl⟩ : syracuseStep 3076289 = 2307217) B2307217
theorem B2192093 : Blo 283827 2192093 := bstep (se 3 (by rfl) ⟨411017, by rfl⟩ : syracuseStep 2192093 = 822035) B822035
theorem B488171 : Blo 283827 488171 := bstep (se 1 (by rfl) ⟨366128, by rfl⟩ : syracuseStep 488171 = 732257) B732257
theorem B652283 : Blo 283827 652283 := bstep (se 1 (by rfl) ⟨489212, by rfl⟩ : syracuseStep 652283 = 978425) B978425
theorem B455887 : Blo 283827 455887 := bstep (se 1 (by rfl) ⟨341915, by rfl⟩ : syracuseStep 455887 = 683831) B683831
theorem B685331 : Blo 283827 685331 := bstep (se 1 (by rfl) ⟨513998, by rfl⟩ : syracuseStep 685331 = 1027997) B1027997
theorem B816571 : Blo 283827 816571 := bstep (se 1 (by rfl) ⟨612428, by rfl⟩ : syracuseStep 816571 = 1224857) B1224857
theorem B816959 : Blo 283827 816959 := bstep (se 1 (by rfl) ⟨612719, by rfl⟩ : syracuseStep 816959 = 1225439) B1225439
theorem B817415 : Blo 283827 817415 := bstep (se 1 (by rfl) ⟨613061, by rfl⟩ : syracuseStep 817415 = 1226123) B1226123
theorem B8191205 : Blo 283827 8191205 := bstep (se 4 (by rfl) ⟨767925, by rfl⟩ : syracuseStep 8191205 = 1535851) B1535851
theorem B818599 : Blo 283827 818599 := bstep (se 1 (by rfl) ⟨613949, by rfl⟩ : syracuseStep 818599 = 1227899) B1227899
theorem B425849 : Blo 283827 425849 := bstep (se 2 (by rfl) ⟨159693, by rfl⟩ : syracuseStep 425849 = 319387) B319387
theorem B458617 : Blo 283827 458617 := bstep (se 2 (by rfl) ⟨171981, by rfl⟩ : syracuseStep 458617 = 343963) B343963
theorem B1081259 : Blo 283827 1081259 := bstep (se 1 (by rfl) ⟨810944, by rfl⟩ : syracuseStep 1081259 = 1621889) B1621889
theorem B982955 : Blo 283827 982955 := bstep (se 1 (by rfl) ⟨737216, by rfl⟩ : syracuseStep 982955 = 1474433) B1474433
theorem B425951 : Blo 283827 425951 := bstep (se 1 (by rfl) ⟨319463, by rfl⟩ : syracuseStep 425951 = 638927) B638927
theorem B4129055 : Blo 283827 4129055 := bstep (se 1 (by rfl) ⟨3096791, by rfl⟩ : syracuseStep 4129055 = 6193583) B6193583
theorem B426287 : Blo 283827 426287 := bstep (se 1 (by rfl) ⟨319715, by rfl⟩ : syracuseStep 426287 = 639431) B639431
theorem B1343915 : Blo 283827 1343915 := bstep (se 1 (by rfl) ⟨1007936, by rfl⟩ : syracuseStep 1343915 = 2015873) B2015873
theorem B426527 : Blo 283827 426527 := bstep (se 1 (by rfl) ⟨319895, by rfl⟩ : syracuseStep 426527 = 639791) B639791
theorem B1213001 : Blo 283827 1213001 := bstep (se 2 (by rfl) ⟨454875, by rfl⟩ : syracuseStep 1213001 = 909751) B909751
theorem B3637871 : Blo 283827 3637871 := bstep (se 1 (by rfl) ⟨2728403, by rfl⟩ : syracuseStep 3637871 = 5456807) B5456807
theorem B4620995 : Blo 283827 4620995 := bstep (se 1 (by rfl) ⟨3465746, by rfl⟩ : syracuseStep 4620995 = 6931493) B6931493
theorem B1967021 : Blo 283827 1967021 := bstep (se 3 (by rfl) ⟨368816, by rfl⟩ : syracuseStep 1967021 = 737633) B737633
theorem B427199 : Blo 283827 427199 := bstep (se 1 (by rfl) ⟨320399, by rfl⟩ : syracuseStep 427199 = 640799) B640799
theorem B1213649 : Blo 283827 1213649 := bstep (se 2 (by rfl) ⟨455118, by rfl⟩ : syracuseStep 1213649 = 910237) B910237
theorem B1377503 : Blo 283827 1377503 := bstep (se 1 (by rfl) ⟨1033127, by rfl⟩ : syracuseStep 1377503 = 2066255) B2066255
theorem B1639727 : Blo 283827 1639727 := bstep (se 1 (by rfl) ⟨1229795, by rfl⟩ : syracuseStep 1639727 = 2459591) B2459591
theorem B427343 : Blo 283827 427343 := bstep (se 1 (by rfl) ⟨320507, by rfl⟩ : syracuseStep 427343 = 641015) B641015
theorem B722267 : Blo 283827 722267 := bstep (se 1 (by rfl) ⟨541700, by rfl⟩ : syracuseStep 722267 = 1083401) B1083401
theorem B2426273 : Blo 283827 2426273 := bstep (se 2 (by rfl) ⟨909852, by rfl⟩ : syracuseStep 2426273 = 1819705) B1819705
theorem B427433 : Blo 283827 427433 := bstep (se 2 (by rfl) ⟨160287, by rfl⟩ : syracuseStep 427433 = 320575) B320575
theorem B624191 : Blo 283827 624191 := bstep (se 1 (by rfl) ⟨468143, by rfl⟩ : syracuseStep 624191 = 936287) B936287
theorem B427583 : Blo 283827 427583 := bstep (se 1 (by rfl) ⟨320687, by rfl⟩ : syracuseStep 427583 = 641375) B641375
theorem B427625 : Blo 283827 427625 := bstep (se 2 (by rfl) ⟨160359, by rfl⟩ : syracuseStep 427625 = 320719) B320719
theorem B689771 : Blo 283827 689771 := bstep (se 1 (by rfl) ⟨517328, by rfl⟩ : syracuseStep 689771 = 1034657) B1034657
theorem B1083233 : Blo 283827 1083233 := bstep (se 2 (by rfl) ⟨406212, by rfl⟩ : syracuseStep 1083233 = 812425) B812425
theorem B1181537 : Blo 283827 1181537 := bstep (se 2 (by rfl) ⟨443076, by rfl⟩ : syracuseStep 1181537 = 886153) B886153
theorem B428063 : Blo 283827 428063 := bstep (se 1 (by rfl) ⟨321047, by rfl⟩ : syracuseStep 428063 = 642095) B642095
theorem B428255 : Blo 283827 428255 := bstep (se 1 (by rfl) ⟨321191, by rfl⟩ : syracuseStep 428255 = 642383) B642383
theorem B428315 : Blo 283827 428315 := bstep (se 1 (by rfl) ⟨321236, by rfl⟩ : syracuseStep 428315 = 642473) B642473
theorem B1083689 : Blo 283827 1083689 := bstep (se 2 (by rfl) ⟨406383, by rfl⟩ : syracuseStep 1083689 = 812767) B812767
theorem B428639 : Blo 283827 428639 := bstep (se 1 (by rfl) ⟨321479, by rfl⟩ : syracuseStep 428639 = 642959) B642959
theorem B428921 : Blo 283827 428921 := bstep (se 2 (by rfl) ⟨160845, by rfl⟩ : syracuseStep 428921 = 321691) B321691
theorem B428969 : Blo 283827 428969 := bstep (se 2 (by rfl) ⟨160863, by rfl⟩ : syracuseStep 428969 = 321727) B321727
theorem B1870895 : Blo 283827 1870895 := bstep (se 1 (by rfl) ⟨1403171, by rfl⟩ : syracuseStep 1870895 = 2806343) B2806343
theorem B429119 : Blo 283827 429119 := bstep (se 1 (by rfl) ⟨321839, by rfl⟩ : syracuseStep 429119 = 643679) B643679
theorem B429671 : Blo 283827 429671 := bstep (se 1 (by rfl) ⟨322253, by rfl⟩ : syracuseStep 429671 = 644507) B644507
theorem B724859 : Blo 283827 724859 := bstep (se 1 (by rfl) ⟨543644, by rfl⟩ : syracuseStep 724859 = 1087289) B1087289
theorem B430055 : Blo 283827 430055 := bstep (se 1 (by rfl) ⟨322541, by rfl⟩ : syracuseStep 430055 = 645083) B645083
theorem B430175 : Blo 283827 430175 := bstep (se 1 (by rfl) ⟨322631, by rfl⟩ : syracuseStep 430175 = 645263) B645263
theorem B430187 : Blo 283827 430187 := bstep (se 1 (by rfl) ⟨322640, by rfl⟩ : syracuseStep 430187 = 645281) B645281
theorem B1151111 : Blo 283827 1151111 := bstep (se 1 (by rfl) ⟨863333, by rfl⟩ : syracuseStep 1151111 = 1726667) B1726667
theorem B430235 : Blo 283827 430235 := bstep (se 1 (by rfl) ⟨322676, by rfl⟩ : syracuseStep 430235 = 645353) B645353
theorem B2167559 : Blo 283827 2167559 := bstep (se 1 (by rfl) ⟨1625669, by rfl⟩ : syracuseStep 2167559 = 3251339) B3251339
theorem B2233327 : Blo 283827 2233327 := bstep (se 1 (by rfl) ⟨1674995, by rfl⟩ : syracuseStep 2233327 = 3349991) B3349991
theorem B431087 : Blo 283827 431087 := bstep (se 1 (by rfl) ⟨323315, by rfl⟩ : syracuseStep 431087 = 646631) B646631
theorem B3708089 : Blo 283827 3708089 := bstep (se 2 (by rfl) ⟨1390533, by rfl⟩ : syracuseStep 3708089 = 2781067) B2781067
theorem B431471 : Blo 283827 431471 := bstep (se 1 (by rfl) ⟨323603, by rfl⟩ : syracuseStep 431471 = 647207) B647207
theorem B1218023 : Blo 283827 1218023 := bstep (se 1 (by rfl) ⟨913517, by rfl⟩ : syracuseStep 1218023 = 1827035) B1827035
theorem B431591 : Blo 283827 431591 := bstep (se 1 (by rfl) ⟨323693, by rfl⟩ : syracuseStep 431591 = 647387) B647387
theorem B1152667 : Blo 283827 1152667 := bstep (se 1 (by rfl) ⟨864500, by rfl⟩ : syracuseStep 1152667 = 1729001) B1729001
theorem B5248891 : Blo 283827 5248891 := bstep (se 1 (by rfl) ⟨3936668, by rfl⟩ : syracuseStep 5248891 = 7873337) B7873337
theorem B4135049 : Blo 283827 4135049 := bstep (se 2 (by rfl) ⟨1550643, by rfl⟩ : syracuseStep 4135049 = 3101287) B3101287
theorem B727177 : Blo 283827 727177 := bstep (se 2 (by rfl) ⟨272691, by rfl⟩ : syracuseStep 727177 = 545383) B545383
theorem B1087775 : Blo 283827 1087775 := bstep (se 1 (by rfl) ⟨815831, by rfl⟩ : syracuseStep 1087775 = 1631663) B1631663
theorem B2431397 : Blo 283827 2431397 := bstep (se 4 (by rfl) ⟨227943, by rfl⟩ : syracuseStep 2431397 = 455887) B455887
theorem B4398209 : Blo 283827 4398209 := bstep (se 2 (by rfl) ⟨1649328, by rfl⟩ : syracuseStep 4398209 = 3298657) B3298657
theorem B1449089 : Blo 283827 1449089 := bstep (se 2 (by rfl) ⟨543408, by rfl⟩ : syracuseStep 1449089 = 1086817) B1086817
theorem B1088761 : Blo 283827 1088761 := bstep (se 2 (by rfl) ⟨408285, by rfl⟩ : syracuseStep 1088761 = 816571) B816571
theorem B7413059 : Blo 283827 7413059 := bstep (se 1 (by rfl) ⟨5559794, by rfl⟩ : syracuseStep 7413059 = 11119589) B11119589
theorem B2072137 : Blo 283827 2072137 := bstep (se 2 (by rfl) ⟨777051, by rfl⟩ : syracuseStep 2072137 = 1554103) B1554103
theorem B1449899 : Blo 283827 1449899 := bstep (se 1 (by rfl) ⟨1087424, by rfl⟩ : syracuseStep 1449899 = 2174849) B2174849
theorem B3252797 : Blo 283827 3252797 := bstep (se 3 (by rfl) ⟨609899, by rfl⟩ : syracuseStep 3252797 = 1219799) B1219799
theorem B434855 : Blo 283827 434855 := bstep (se 1 (by rfl) ⟨326141, by rfl⟩ : syracuseStep 434855 = 652283) B652283
theorem B9904841 : Blo 283827 9904841 := bstep (se 2 (by rfl) ⟨3714315, by rfl⟩ : syracuseStep 9904841 = 7428631) B7428631
theorem B2761771 : Blo 283827 2761771 := bstep (se 1 (by rfl) ⟨2071328, by rfl⟩ : syracuseStep 2761771 = 4142657) B4142657
theorem B2762045 : Blo 283827 2762045 := bstep (se 3 (by rfl) ⟨517883, by rfl⟩ : syracuseStep 2762045 = 1035767) B1035767
theorem B1091465 : Blo 283827 1091465 := bstep (se 2 (by rfl) ⟨409299, by rfl⟩ : syracuseStep 1091465 = 818599) B818599
theorem B1386953 : Blo 283827 1386953 := bstep (se 2 (by rfl) ⟨520107, by rfl⟩ : syracuseStep 1386953 = 1040215) B1040215
theorem B961577 : Blo 283827 961577 := bstep (se 2 (by rfl) ⟨360591, by rfl⟩ : syracuseStep 961577 = 721183) B721183
theorem B1092649 : Blo 283827 1092649 := bstep (se 2 (by rfl) ⟨409743, by rfl⟩ : syracuseStep 1092649 = 819487) B819487
theorem B961847 : Blo 283827 961847 := bstep (se 1 (by rfl) ⟨721385, by rfl⟩ : syracuseStep 961847 = 1442771) B1442771
theorem B601499 : Blo 283827 601499 := bstep (se 1 (by rfl) ⟨451124, by rfl⟩ : syracuseStep 601499 = 902249) B902249
theorem B2174363 : Blo 283827 2174363 := bstep (se 1 (by rfl) ⟨1630772, by rfl⟩ : syracuseStep 2174363 = 3261545) B3261545
theorem B1158799 : Blo 283827 1158799 := bstep (se 1 (by rfl) ⟨869099, by rfl⟩ : syracuseStep 1158799 = 1738199) B1738199
theorem B5222033 : Blo 283827 5222033 := bstep (se 2 (by rfl) ⟨1958262, by rfl⟩ : syracuseStep 5222033 = 3916525) B3916525
theorem B4894505 : Blo 283827 4894505 := bstep (se 2 (by rfl) ⟨1835439, by rfl⟩ : syracuseStep 4894505 = 3670879) B3670879
theorem B962441 : Blo 283827 962441 := bstep (se 2 (by rfl) ⟨360915, by rfl⟩ : syracuseStep 962441 = 721831) B721831
theorem B1225115 : Blo 283827 1225115 := bstep (se 1 (by rfl) ⟨918836, by rfl⟩ : syracuseStep 1225115 = 1837673) B1837673
theorem B2732555 : Blo 283827 2732555 := bstep (se 1 (by rfl) ⟨2049416, by rfl⟩ : syracuseStep 2732555 = 4098833) B4098833
theorem B2765735 : Blo 283827 2765735 := bstep (se 1 (by rfl) ⟨2074301, by rfl⟩ : syracuseStep 2765735 = 4148603) B4148603
theorem B1225799 : Blo 283827 1225799 := bstep (se 1 (by rfl) ⟨919349, by rfl⟩ : syracuseStep 1225799 = 1838699) B1838699
theorem B1095277 : Blo 283827 1095277 := bstep (se 3 (by rfl) ⟨205364, by rfl⟩ : syracuseStep 1095277 = 410729) B410729
theorem B1455731 : Blo 283827 1455731 := bstep (se 1 (by rfl) ⟨1091798, by rfl⟩ : syracuseStep 1455731 = 2183597) B2183597
theorem B2209451 : Blo 283827 2209451 := bstep (se 1 (by rfl) ⟨1657088, by rfl⟩ : syracuseStep 2209451 = 3314177) B3314177
theorem B4110365 : Blo 283827 4110365 := bstep (se 3 (by rfl) ⟨770693, by rfl⟩ : syracuseStep 4110365 = 1541387) B1541387
theorem B1456541 : Blo 283827 1456541 := bstep (se 3 (by rfl) ⟨273101, by rfl⟩ : syracuseStep 1456541 = 546203) B546203
theorem B408007 : Blo 283827 408007 := bstep (se 1 (by rfl) ⟨306005, by rfl⟩ : syracuseStep 408007 = 612011) B612011
theorem B539369 : Blo 283827 539369 := bstep (se 2 (by rfl) ⟨202263, by rfl⟩ : syracuseStep 539369 = 404527) B404527
theorem B2440145 : Blo 283827 2440145 := bstep (se 2 (by rfl) ⟨915054, by rfl⟩ : syracuseStep 2440145 = 1830109) B1830109
theorem B2603987 : Blo 283827 2603987 := bstep (se 1 (by rfl) ⟨1952990, by rfl⟩ : syracuseStep 2603987 = 3905981) B3905981
theorem B1031399 : Blo 283827 1031399 := bstep (se 1 (by rfl) ⟨773549, by rfl⟩ : syracuseStep 1031399 = 1547099) B1547099
theorem B1621235 : Blo 283827 1621235 := bstep (se 1 (by rfl) ⟨1215926, by rfl⟩ : syracuseStep 1621235 = 2431853) B2431853
theorem B638639 : Blo 283827 638639 := bstep (se 1 (by rfl) ⟨478979, by rfl⟩ : syracuseStep 638639 = 957959) B957959
theorem B638729 : Blo 283827 638729 := bstep (se 2 (by rfl) ⟨239523, by rfl⟩ : syracuseStep 638729 = 479047) B479047
theorem B540425 : Blo 283827 540425 := bstep (se 2 (by rfl) ⟨202659, by rfl⟩ : syracuseStep 540425 = 405319) B405319
theorem B3915649 : Blo 283827 3915649 := bstep (se 2 (by rfl) ⟨1468368, by rfl⟩ : syracuseStep 3915649 = 2936737) B2936737
theorem B1622207 : Blo 283827 1622207 := bstep (se 1 (by rfl) ⟨1216655, by rfl⟩ : syracuseStep 1622207 = 2433311) B2433311
theorem B344299 : Blo 283827 344299 := bstep (se 1 (by rfl) ⟨258224, by rfl⟩ : syracuseStep 344299 = 516449) B516449
theorem B5194007 : Blo 283827 5194007 := bstep (se 1 (by rfl) ⟨3895505, by rfl⟩ : syracuseStep 5194007 = 7791011) B7791011
theorem B639359 : Blo 283827 639359 := bstep (se 1 (by rfl) ⟨479519, by rfl⟩ : syracuseStep 639359 = 959039) B959039
theorem B541055 : Blo 283827 541055 := bstep (se 1 (by rfl) ⟨405791, by rfl⟩ : syracuseStep 541055 = 811583) B811583
theorem B639593 : Blo 283827 639593 := bstep (se 2 (by rfl) ⟨239847, by rfl⟩ : syracuseStep 639593 = 479695) B479695
theorem B2736827 : Blo 283827 2736827 := bstep (se 1 (by rfl) ⟨2052620, by rfl⟩ : syracuseStep 2736827 = 4105241) B4105241
theorem B967355 : Blo 283827 967355 := bstep (se 1 (by rfl) ⟨725516, by rfl⟩ : syracuseStep 967355 = 1451033) B1451033
theorem B1295129 : Blo 283827 1295129 := bstep (se 2 (by rfl) ⟨485673, by rfl⟩ : syracuseStep 1295129 = 971347) B971347
theorem B640223 : Blo 283827 640223 := bstep (se 1 (by rfl) ⟨480167, by rfl⟩ : syracuseStep 640223 = 960335) B960335
theorem B640439 : Blo 283827 640439 := bstep (se 1 (by rfl) ⟨480329, by rfl⟩ : syracuseStep 640439 = 960659) B960659
theorem B640619 : Blo 283827 640619 := bstep (se 1 (by rfl) ⟨480464, by rfl⟩ : syracuseStep 640619 = 960929) B960929
theorem B542315 : Blo 283827 542315 := bstep (se 1 (by rfl) ⟨406736, by rfl⟩ : syracuseStep 542315 = 813473) B813473
theorem B640889 : Blo 283827 640889 := bstep (se 2 (by rfl) ⟨240333, by rfl⟩ : syracuseStep 640889 = 480667) B480667
theorem B542695 : Blo 283827 542695 := bstep (se 1 (by rfl) ⟨407021, by rfl⟩ : syracuseStep 542695 = 814043) B814043
theorem B641321 : Blo 283827 641321 := bstep (se 2 (by rfl) ⟨240495, by rfl⟩ : syracuseStep 641321 = 480991) B480991
theorem B969083 : Blo 283827 969083 := bstep (se 1 (by rfl) ⟨726812, by rfl⟩ : syracuseStep 969083 = 1453625) B1453625
theorem B1559177 : Blo 283827 1559177 := bstep (se 2 (by rfl) ⟨584691, by rfl⟩ : syracuseStep 1559177 = 1169383) B1169383
theorem B969353 : Blo 283827 969353 := bstep (se 2 (by rfl) ⟨363507, by rfl⟩ : syracuseStep 969353 = 727015) B727015
theorem B11717399 : Blo 283827 11717399 := bstep (se 1 (by rfl) ⟨8788049, by rfl⟩ : syracuseStep 11717399 = 17576099) B17576099
theorem B2050859 : Blo 283827 2050859 := bstep (se 1 (by rfl) ⟨1538144, by rfl⟩ : syracuseStep 2050859 = 3076289) B3076289
theorem B641897 : Blo 283827 641897 := bstep (se 2 (by rfl) ⟨240711, by rfl⟩ : syracuseStep 641897 = 481423) B481423
theorem B641951 : Blo 283827 641951 := bstep (se 1 (by rfl) ⟨481463, by rfl⟩ : syracuseStep 641951 = 962927) B962927
theorem B4115387 : Blo 283827 4115387 := bstep (se 1 (by rfl) ⟨3086540, by rfl⟩ : syracuseStep 4115387 = 6173081) B6173081
theorem B1461395 : Blo 283827 1461395 := bstep (se 1 (by rfl) ⟨1096046, by rfl⟩ : syracuseStep 1461395 = 2192093) B2192093
theorem B2608537 : Blo 283827 2608537 := bstep (se 2 (by rfl) ⟨978201, by rfl⟩ : syracuseStep 2608537 = 1956403) B1956403
theorem B642887 : Blo 283827 642887 := bstep (se 1 (by rfl) ⟨482165, by rfl⟩ : syracuseStep 642887 = 964331) B964331
theorem B544639 : Blo 283827 544639 := bstep (se 1 (by rfl) ⟨408479, by rfl⟩ : syracuseStep 544639 = 816959) B816959
theorem B643067 : Blo 283827 643067 := bstep (se 1 (by rfl) ⟨482300, by rfl⟩ : syracuseStep 643067 = 964601) B964601
theorem B643175 : Blo 283827 643175 := bstep (se 1 (by rfl) ⟨482381, by rfl⟩ : syracuseStep 643175 = 964763) B964763
theorem B643247 : Blo 283827 643247 := bstep (se 1 (by rfl) ⟨482435, by rfl⟩ : syracuseStep 643247 = 964871) B964871
theorem B774319 : Blo 283827 774319 := bstep (se 1 (by rfl) ⟨580739, by rfl⟩ : syracuseStep 774319 = 1161479) B1161479
theorem B544943 : Blo 283827 544943 := bstep (se 1 (by rfl) ⟨408707, by rfl⟩ : syracuseStep 544943 = 817415) B817415
theorem B5460803 : Blo 283827 5460803 := bstep (se 1 (by rfl) ⟨4095602, by rfl⟩ : syracuseStep 5460803 = 8191205) B8191205
theorem B643931 : Blo 283827 643931 := bstep (se 1 (by rfl) ⟨482948, by rfl⟩ : syracuseStep 643931 = 965897) B965897
theorem B7361441 : Blo 283827 7361441 := bstep (se 2 (by rfl) ⟨2760540, by rfl⟩ : syracuseStep 7361441 = 5521081) B5521081
theorem B611489 : Blo 283827 611489 := bstep (se 2 (by rfl) ⟨229308, by rfl⟩ : syracuseStep 611489 = 458617) B458617
theorem B545953 : Blo 283827 545953 := bstep (se 2 (by rfl) ⟨204732, by rfl⟩ : syracuseStep 545953 = 409465) B409465
theorem B283899 : Blo 283827 283899 := bstep (se 1 (by rfl) ⟨212924, by rfl⟩ : syracuseStep 283899 = 425849) B425849
theorem B283967 : Blo 283827 283967 := bstep (se 1 (by rfl) ⟨212975, by rfl⟩ : syracuseStep 283967 = 425951) B425951
theorem B284135 : Blo 283827 284135 := bstep (se 1 (by rfl) ⟨213101, by rfl⟩ : syracuseStep 284135 = 426203) B426203
theorem B284143 : Blo 283827 284143 := bstep (se 1 (by rfl) ⟨213107, by rfl⟩ : syracuseStep 284143 = 426215) B426215
theorem B644687 : Blo 283827 644687 := bstep (se 1 (by rfl) ⟨483515, by rfl⟩ : syracuseStep 644687 = 967031) B967031
theorem B284251 : Blo 283827 284251 := bstep (se 1 (by rfl) ⟨213188, by rfl⟩ : syracuseStep 284251 = 426377) B426377
theorem B284315 : Blo 283827 284315 := bstep (se 1 (by rfl) ⟨213236, by rfl⟩ : syracuseStep 284315 = 426473) B426473
theorem B2053799 : Blo 283827 2053799 := bstep (se 1 (by rfl) ⟨1540349, by rfl⟩ : syracuseStep 2053799 = 3080699) B3080699
theorem B284399 : Blo 283827 284399 := bstep (se 1 (by rfl) ⟨213299, by rfl⟩ : syracuseStep 284399 = 426599) B426599
theorem B284487 : Blo 283827 284487 := bstep (se 1 (by rfl) ⟨213365, by rfl⟩ : syracuseStep 284487 = 426731) B426731
theorem B284507 : Blo 283827 284507 := bstep (se 1 (by rfl) ⟨213380, by rfl⟩ : syracuseStep 284507 = 426761) B426761
theorem B284575 : Blo 283827 284575 := bstep (se 1 (by rfl) ⟨213431, by rfl⟩ : syracuseStep 284575 = 426863) B426863
theorem B284743 : Blo 283827 284743 := bstep (se 1 (by rfl) ⟨213557, by rfl⟩ : syracuseStep 284743 = 427115) B427115
theorem B6150323 : Blo 283827 6150323 := bstep (se 1 (by rfl) ⟨4612742, by rfl⟩ : syracuseStep 6150323 = 9225485) B9225485
theorem B284903 : Blo 283827 284903 := bstep (se 1 (by rfl) ⟨213677, by rfl⟩ : syracuseStep 284903 = 427355) B427355
theorem B645407 : Blo 283827 645407 := bstep (se 1 (by rfl) ⟨484055, by rfl⟩ : syracuseStep 645407 = 968111) B968111
theorem B285087 : Blo 283827 285087 := bstep (se 1 (by rfl) ⟨213815, by rfl⟩ : syracuseStep 285087 = 427631) B427631
theorem B4872635 : Blo 283827 4872635 := bstep (se 1 (by rfl) ⟨3654476, by rfl⟩ : syracuseStep 4872635 = 7308953) B7308953
theorem B285135 : Blo 283827 285135 := bstep (se 1 (by rfl) ⟨213851, by rfl⟩ : syracuseStep 285135 = 427703) B427703
theorem B285159 : Blo 283827 285159 := bstep (se 1 (by rfl) ⟨213869, by rfl⟩ : syracuseStep 285159 = 427739) B427739
theorem B612839 : Blo 283827 612839 := bstep (se 1 (by rfl) ⟨459629, by rfl⟩ : syracuseStep 612839 = 919259) B919259
theorem B4413971 : Blo 283827 4413971 := bstep (se 1 (by rfl) ⟨3310478, by rfl⟩ : syracuseStep 4413971 = 6620957) B6620957
theorem B645659 : Blo 283827 645659 := bstep (se 1 (by rfl) ⟨484244, by rfl⟩ : syracuseStep 645659 = 968489) B968489
theorem B285275 : Blo 283827 285275 := bstep (se 1 (by rfl) ⟨213956, by rfl⟩ : syracuseStep 285275 = 427913) B427913
theorem B285343 : Blo 283827 285343 := bstep (se 1 (by rfl) ⟨214007, by rfl⟩ : syracuseStep 285343 = 428015) B428015
theorem B809783 : Blo 283827 809783 := bstep (se 1 (by rfl) ⟨607337, by rfl⟩ : syracuseStep 809783 = 1214675) B1214675
theorem B482105 : Blo 283827 482105 := bstep (se 2 (by rfl) ⟨180789, by rfl⟩ : syracuseStep 482105 = 361579) B361579
theorem B285511 : Blo 283827 285511 := bstep (se 1 (by rfl) ⟨214133, by rfl⟩ : syracuseStep 285511 = 428267) B428267
theorem B285551 : Blo 283827 285551 := bstep (se 1 (by rfl) ⟨214163, by rfl⟩ : syracuseStep 285551 = 428327) B428327
theorem B482159 : Blo 283827 482159 := bstep (se 1 (by rfl) ⟨361619, by rfl⟩ : syracuseStep 482159 = 723239) B723239
theorem B285607 : Blo 283827 285607 := bstep (se 1 (by rfl) ⟨214205, by rfl⟩ : syracuseStep 285607 = 428411) B428411
theorem B1989647 : Blo 283827 1989647 := bstep (se 1 (by rfl) ⟨1492235, by rfl⟩ : syracuseStep 1989647 = 2984471) B2984471
theorem B285787 : Blo 283827 285787 := bstep (se 1 (by rfl) ⟨214340, by rfl⟩ : syracuseStep 285787 = 428681) B428681
theorem B285903 : Blo 283827 285903 := bstep (se 1 (by rfl) ⟨214427, by rfl⟩ : syracuseStep 285903 = 428855) B428855
theorem B285927 : Blo 283827 285927 := bstep (se 1 (by rfl) ⟨214445, by rfl⟩ : syracuseStep 285927 = 428891) B428891
theorem B34331921 : Blo 283827 34331921 := bstep (se 2 (by rfl) ⟨12874470, by rfl⟩ : syracuseStep 34331921 = 25748941) B25748941
theorem B1301789 : Blo 283827 1301789 := bstep (se 3 (by rfl) ⟨244085, by rfl⟩ : syracuseStep 1301789 = 488171) B488171
theorem B286023 : Blo 283827 286023 := bstep (se 1 (by rfl) ⟨214517, by rfl⟩ : syracuseStep 286023 = 429035) B429035
theorem B1957225 : Blo 283827 1957225 := bstep (se 2 (by rfl) ⟨733959, by rfl⟩ : syracuseStep 1957225 = 1467919) B1467919
theorem B286159 : Blo 283827 286159 := bstep (se 1 (by rfl) ⟨214619, by rfl⟩ : syracuseStep 286159 = 429239) B429239
theorem B286319 : Blo 283827 286319 := bstep (se 1 (by rfl) ⟨214739, by rfl⟩ : syracuseStep 286319 = 429479) B429479
theorem B286375 : Blo 283827 286375 := bstep (se 1 (by rfl) ⟨214781, by rfl⟩ : syracuseStep 286375 = 429563) B429563
theorem B286439 : Blo 283827 286439 := bstep (se 1 (by rfl) ⟨214829, by rfl⟩ : syracuseStep 286439 = 429659) B429659
theorem B286495 : Blo 283827 286495 := bstep (se 1 (by rfl) ⟨214871, by rfl⟩ : syracuseStep 286495 = 429743) B429743
theorem B647009 : Blo 283827 647009 := bstep (se 2 (by rfl) ⟨242628, by rfl⟩ : syracuseStep 647009 = 485257) B485257
theorem B286575 : Blo 283827 286575 := bstep (se 1 (by rfl) ⟨214931, by rfl⟩ : syracuseStep 286575 = 429863) B429863
theorem B286631 : Blo 283827 286631 := bstep (se 1 (by rfl) ⟨214973, by rfl⟩ : syracuseStep 286631 = 429947) B429947
theorem B647135 : Blo 283827 647135 := bstep (se 1 (by rfl) ⟨485351, by rfl⟩ : syracuseStep 647135 = 970703) B970703
theorem B286911 : Blo 283827 286911 := bstep (se 1 (by rfl) ⟨215183, by rfl⟩ : syracuseStep 286911 = 430367) B430367
theorem B286927 : Blo 283827 286927 := bstep (se 1 (by rfl) ⟨215195, by rfl⟩ : syracuseStep 286927 = 430391) B430391
theorem B483583 : Blo 283827 483583 := bstep (se 1 (by rfl) ⟨362687, by rfl⟩ : syracuseStep 483583 = 725375) B725375
theorem B286975 : Blo 283827 286975 := bstep (se 1 (by rfl) ⟨215231, by rfl⟩ : syracuseStep 286975 = 430463) B430463
theorem B647423 : Blo 283827 647423 := bstep (se 1 (by rfl) ⟨485567, by rfl⟩ : syracuseStep 647423 = 971135) B971135
theorem B287023 : Blo 283827 287023 := bstep (se 1 (by rfl) ⟨215267, by rfl⟩ : syracuseStep 287023 = 430535) B430535
theorem B909625 : Blo 283827 909625 := bstep (se 2 (by rfl) ⟨341109, by rfl⟩ : syracuseStep 909625 = 682219) B682219
theorem B647585 : Blo 283827 647585 := bstep (se 2 (by rfl) ⟨242844, by rfl⟩ : syracuseStep 647585 = 485689) B485689
theorem B287259 : Blo 283827 287259 := bstep (se 1 (by rfl) ⟨215444, by rfl⟩ : syracuseStep 287259 = 430889) B430889
theorem B287263 : Blo 283827 287263 := bstep (se 1 (by rfl) ⟨215447, by rfl⟩ : syracuseStep 287263 = 430895) B430895
theorem B287343 : Blo 283827 287343 := bstep (se 1 (by rfl) ⟨215507, by rfl⟩ : syracuseStep 287343 = 431015) B431015
theorem B2351783 : Blo 283827 2351783 := bstep (se 1 (by rfl) ⟨1763837, by rfl⟩ : syracuseStep 2351783 = 3527675) B3527675
theorem B287399 : Blo 283827 287399 := bstep (se 1 (by rfl) ⟨215549, by rfl⟩ : syracuseStep 287399 = 431099) B431099
theorem B287439 : Blo 283827 287439 := bstep (se 1 (by rfl) ⟨215579, by rfl⟩ : syracuseStep 287439 = 431159) B431159
theorem B1630955 : Blo 283827 1630955 := bstep (se 1 (by rfl) ⟨1223216, by rfl⟩ : syracuseStep 1630955 = 2446433) B2446433
theorem B320287 : Blo 283827 320287 := bstep (se 1 (by rfl) ⟨240215, by rfl⟩ : syracuseStep 320287 = 480431) B480431
theorem B287519 : Blo 283827 287519 := bstep (se 1 (by rfl) ⟨215639, by rfl⟩ : syracuseStep 287519 = 431279) B431279
theorem B287791 : Blo 283827 287791 := bstep (se 1 (by rfl) ⟨215843, by rfl⟩ : syracuseStep 287791 = 431687) B431687
theorem B196338887 : Blo 283827 196338887 := bstep (se 1 (by rfl) ⟨147254165, by rfl⟩ : syracuseStep 196338887 = 294508331) B294508331
theorem B911083 : Blo 283827 911083 := bstep (se 1 (by rfl) ⟨683312, by rfl⟩ : syracuseStep 911083 = 1366625) B1366625
theorem B2975491 : Blo 283827 2975491 := bstep (se 1 (by rfl) ⟨2231618, by rfl⟩ : syracuseStep 2975491 = 4463237) B4463237
theorem B485311 : Blo 283827 485311 := bstep (se 1 (by rfl) ⟨363983, by rfl⟩ : syracuseStep 485311 = 727967) B727967
theorem B321583 : Blo 283827 321583 := bstep (se 1 (by rfl) ⟨241187, by rfl⟩ : syracuseStep 321583 = 482375) B482375
theorem B321871 : Blo 283827 321871 := bstep (se 1 (by rfl) ⟨241403, by rfl⟩ : syracuseStep 321871 = 482807) B482807
theorem B1174121 : Blo 283827 1174121 := bstep (se 2 (by rfl) ⟨440295, by rfl⟩ : syracuseStep 1174121 = 880591) B880591
theorem B322555 : Blo 283827 322555 := bstep (se 1 (by rfl) ⟨241916, by rfl⟩ : syracuseStep 322555 = 483833) B483833
theorem B322735 : Blo 283827 322735 := bstep (se 1 (by rfl) ⟨242051, by rfl⟩ : syracuseStep 322735 = 484103) B484103
theorem B552673 : Blo 283827 552673 := bstep (se 2 (by rfl) ⟨207252, by rfl⟩ : syracuseStep 552673 = 414505) B414505
theorem B323455 : Blo 283827 323455 := bstep (se 1 (by rfl) ⟨242591, by rfl⟩ : syracuseStep 323455 = 485183) B485183
theorem B1635511 : Blo 283827 1635511 := bstep (se 1 (by rfl) ⟨1226633, by rfl⟩ : syracuseStep 1635511 = 2453267) B2453267
theorem B456887 : Blo 283827 456887 := bstep (se 1 (by rfl) ⟨342665, by rfl⟩ : syracuseStep 456887 = 685331) B685331
theorem B719401 : Blo 283827 719401 := bstep (se 2 (by rfl) ⟨269775, by rfl⟩ : syracuseStep 719401 = 539551) B539551
theorem B1636969 : Blo 283827 1636969 := bstep (se 2 (by rfl) ⟨613863, by rfl⟩ : syracuseStep 1636969 = 1227727) B1227727
theorem B2325449 : Blo 283827 2325449 := bstep (se 2 (by rfl) ⟨872043, by rfl⟩ : syracuseStep 2325449 = 1744087) B1744087
theorem B982297 : Blo 283827 982297 := bstep (se 2 (by rfl) ⟨368361, by rfl⟩ : syracuseStep 982297 = 736723) B736723
theorem B1080985 : Blo 283827 1080985 := bstep (se 2 (by rfl) ⟨405369, by rfl⟩ : syracuseStep 1080985 = 810739) B810739
theorem B687791 : Blo 283827 687791 := bstep (se 1 (by rfl) ⟨515843, by rfl⟩ : syracuseStep 687791 = 1031687) B1031687
theorem B425807 : Blo 283827 425807 := bstep (se 1 (by rfl) ⟨319355, by rfl⟩ : syracuseStep 425807 = 638711) B638711
theorem B425927 : Blo 283827 425927 := bstep (se 1 (by rfl) ⟨319445, by rfl⟩ : syracuseStep 425927 = 638891) B638891
theorem B720839 : Blo 283827 720839 := bstep (se 1 (by rfl) ⟨540629, by rfl⟩ : syracuseStep 720839 = 1081259) B1081259
theorem B655303 : Blo 283827 655303 := bstep (se 1 (by rfl) ⟨491477, by rfl⟩ : syracuseStep 655303 = 982955) B982955
theorem B1081471 : Blo 283827 1081471 := bstep (se 1 (by rfl) ⟨811103, by rfl⟩ : syracuseStep 1081471 = 1622207) B1622207
theorem B2752703 : Blo 283827 2752703 := bstep (se 1 (by rfl) ⟨2064527, by rfl⟩ : syracuseStep 2752703 = 4129055) B4129055
theorem B426239 : Blo 283827 426239 := bstep (se 1 (by rfl) ⟨319679, by rfl⟩ : syracuseStep 426239 = 639359) B639359
theorem B360703 : Blo 283827 360703 := bstep (se 1 (by rfl) ⟨270527, by rfl⟩ : syracuseStep 360703 = 541055) B541055
theorem B459065 : Blo 283827 459065 := bstep (se 2 (by rfl) ⟨172149, by rfl⟩ : syracuseStep 459065 = 344299) B344299
theorem B426395 : Blo 283827 426395 := bstep (se 1 (by rfl) ⟨319796, by rfl⟩ : syracuseStep 426395 = 639593) B639593
theorem B2425247 : Blo 283827 2425247 := bstep (se 1 (by rfl) ⟨1818935, by rfl⟩ : syracuseStep 2425247 = 3637871) B3637871
theorem B1212833 : Blo 283827 1212833 := bstep (se 2 (by rfl) ⟨454812, by rfl⟩ : syracuseStep 1212833 = 909625) B909625
theorem B3080663 : Blo 283827 3080663 := bstep (se 1 (by rfl) ⟨2310497, by rfl⟩ : syracuseStep 3080663 = 4620995) B4620995
theorem B1311347 : Blo 283827 1311347 := bstep (se 1 (by rfl) ⟨983510, by rfl⟩ : syracuseStep 1311347 = 1967021) B1967021
theorem B426815 : Blo 283827 426815 := bstep (se 1 (by rfl) ⟨320111, by rfl⟩ : syracuseStep 426815 = 640223) B640223
theorem B918335 : Blo 283827 918335 := bstep (se 1 (by rfl) ⟨688751, by rfl⟩ : syracuseStep 918335 = 1377503) B1377503
theorem B426959 : Blo 283827 426959 := bstep (se 1 (by rfl) ⟨320219, by rfl⟩ : syracuseStep 426959 = 640439) B640439
theorem B427049 : Blo 283827 427049 := bstep (se 2 (by rfl) ⟨160143, by rfl⟩ : syracuseStep 427049 = 320287) B320287
theorem B427079 : Blo 283827 427079 := bstep (se 1 (by rfl) ⟨320309, by rfl⟩ : syracuseStep 427079 = 640619) B640619
theorem B459847 : Blo 283827 459847 := bstep (se 1 (by rfl) ⟨344885, by rfl⟩ : syracuseStep 459847 = 689771) B689771
theorem B722155 : Blo 283827 722155 := bstep (se 1 (by rfl) ⟨541616, by rfl⟩ : syracuseStep 722155 = 1083233) B1083233
theorem B787691 : Blo 283827 787691 := bstep (se 1 (by rfl) ⟨590768, by rfl⟩ : syracuseStep 787691 = 1181537) B1181537
theorem B427259 : Blo 283827 427259 := bstep (se 1 (by rfl) ⟨320444, by rfl⟩ : syracuseStep 427259 = 640889) B640889
theorem B427547 : Blo 283827 427547 := bstep (se 1 (by rfl) ⟨320660, by rfl⟩ : syracuseStep 427547 = 641321) B641321
theorem B722459 : Blo 283827 722459 := bstep (se 1 (by rfl) ⟨541844, by rfl⟩ : syracuseStep 722459 = 1083689) B1083689
theorem B427931 : Blo 283827 427931 := bstep (se 1 (by rfl) ⟨320948, by rfl⟩ : syracuseStep 427931 = 641897) B641897
theorem B427967 : Blo 283827 427967 := bstep (se 1 (by rfl) ⟨320975, by rfl⟩ : syracuseStep 427967 = 641951) B641951
theorem B1214777 : Blo 283827 1214777 := bstep (se 2 (by rfl) ⟨455541, by rfl⟩ : syracuseStep 1214777 = 911083) B911083
theorem B3967321 : Blo 283827 3967321 := bstep (se 2 (by rfl) ⟨1487745, by rfl⟩ : syracuseStep 3967321 = 2975491) B2975491
theorem B428591 : Blo 283827 428591 := bstep (se 1 (by rfl) ⟨321443, by rfl⟩ : syracuseStep 428591 = 642887) B642887
theorem B723593 : Blo 283827 723593 := bstep (se 2 (by rfl) ⟨271347, by rfl⟩ : syracuseStep 723593 = 542695) B542695
theorem B428711 : Blo 283827 428711 := bstep (se 1 (by rfl) ⟨321533, by rfl⟩ : syracuseStep 428711 = 643067) B643067
theorem B428777 : Blo 283827 428777 := bstep (se 2 (by rfl) ⟨160791, by rfl⟩ : syracuseStep 428777 = 321583) B321583
theorem B428783 : Blo 283827 428783 := bstep (se 1 (by rfl) ⟨321587, by rfl⟩ : syracuseStep 428783 = 643175) B643175
theorem B428831 : Blo 283827 428831 := bstep (se 1 (by rfl) ⟨321623, by rfl⟩ : syracuseStep 428831 = 643247) B643247
theorem B363295 : Blo 283827 363295 := bstep (se 1 (by rfl) ⟨272471, by rfl⟩ : syracuseStep 363295 = 544943) B544943
theorem B429161 : Blo 283827 429161 := bstep (se 2 (by rfl) ⟨160935, by rfl⟩ : syracuseStep 429161 = 321871) B321871
theorem B1445039 : Blo 283827 1445039 := bstep (se 1 (by rfl) ⟨1083779, by rfl⟩ : syracuseStep 1445039 = 2167559) B2167559
theorem B3640535 : Blo 283827 3640535 := bstep (se 1 (by rfl) ⟨2730401, by rfl⟩ : syracuseStep 3640535 = 5460803) B5460803
theorem B429287 : Blo 283827 429287 := bstep (se 1 (by rfl) ⟨321965, by rfl⟩ : syracuseStep 429287 = 643931) B643931
theorem B429791 : Blo 283827 429791 := bstep (se 1 (by rfl) ⟨322343, by rfl⟩ : syracuseStep 429791 = 644687) B644687
theorem B430073 : Blo 283827 430073 := bstep (se 2 (by rfl) ⟨161277, by rfl⟩ : syracuseStep 430073 = 322555) B322555
theorem B2756699 : Blo 283827 2756699 := bstep (se 1 (by rfl) ⟨2067524, by rfl⟩ : syracuseStep 2756699 = 4135049) B4135049
theorem B4100215 : Blo 283827 4100215 := bstep (se 1 (by rfl) ⟨3075161, by rfl⟩ : syracuseStep 4100215 = 6150323) B6150323
theorem B725183 : Blo 283827 725183 := bstep (se 1 (by rfl) ⟨543887, by rfl⟩ : syracuseStep 725183 = 1087775) B1087775
theorem B430271 : Blo 283827 430271 := bstep (se 1 (by rfl) ⟨322703, by rfl⟩ : syracuseStep 430271 = 645407) B645407
theorem B430313 : Blo 283827 430313 := bstep (se 2 (by rfl) ⟨161367, by rfl⟩ : syracuseStep 430313 = 322735) B322735
theorem B1446173 : Blo 283827 1446173 := bstep (se 3 (by rfl) ⟨271157, by rfl⟩ : syracuseStep 1446173 = 542315) B542315
theorem B3248423 : Blo 283827 3248423 := bstep (se 1 (by rfl) ⟨2436317, by rfl⟩ : syracuseStep 3248423 = 4872635) B4872635
theorem B430439 : Blo 283827 430439 := bstep (se 1 (by rfl) ⟨322829, by rfl⟩ : syracuseStep 430439 = 645659) B645659
theorem B3478049 : Blo 283827 3478049 := bstep (se 2 (by rfl) ⟨1304268, by rfl⟩ : syracuseStep 3478049 = 2608537) B2608537
theorem B1545065 : Blo 283827 1545065 := bstep (se 2 (by rfl) ⟨579399, by rfl⟩ : syracuseStep 1545065 = 1158799) B1158799
theorem B726185 : Blo 283827 726185 := bstep (se 2 (by rfl) ⟨272319, by rfl⟩ : syracuseStep 726185 = 544639) B544639
theorem B431273 : Blo 283827 431273 := bstep (se 2 (by rfl) ⟨161727, by rfl⟩ : syracuseStep 431273 = 323455) B323455
theorem B431339 : Blo 283827 431339 := bstep (se 1 (by rfl) ⟨323504, by rfl⟩ : syracuseStep 431339 = 647009) B647009
theorem B431423 : Blo 283827 431423 := bstep (se 1 (by rfl) ⟨323567, by rfl⟩ : syracuseStep 431423 = 647135) B647135
theorem B431615 : Blo 283827 431615 := bstep (se 1 (by rfl) ⟨323711, by rfl⟩ : syracuseStep 431615 = 647423) B647423
theorem B431723 : Blo 283827 431723 := bstep (se 1 (by rfl) ⟨323792, by rfl⟩ : syracuseStep 431723 = 647585) B647585
theorem B2168531 : Blo 283827 2168531 := bstep (se 1 (by rfl) ⟨1626398, by rfl⟩ : syracuseStep 2168531 = 3252797) B3252797
theorem B1218365 : Blo 283827 1218365 := bstep (se 3 (by rfl) ⟨228443, by rfl⟩ : syracuseStep 1218365 = 456887) B456887
theorem B1087303 : Blo 283827 1087303 := bstep (se 1 (by rfl) ⟨815477, by rfl⟩ : syracuseStep 1087303 = 1630955) B1630955
theorem B1841363 : Blo 283827 1841363 := bstep (se 1 (by rfl) ⟨1381022, by rfl⟩ : syracuseStep 1841363 = 2762045) B2762045
theorem B727643 : Blo 283827 727643 := bstep (se 1 (by rfl) ⟨545732, by rfl⟩ : syracuseStep 727643 = 1091465) B1091465
theorem B11770589 : Blo 283827 11770589 := bstep (se 3 (by rfl) ⟨2206985, by rfl⟩ : syracuseStep 11770589 = 4413971) B4413971
theorem B727937 : Blo 283827 727937 := bstep (se 2 (by rfl) ⟨272976, by rfl⟩ : syracuseStep 727937 = 545953) B545953
theorem B924635 : Blo 283827 924635 := bstep (se 1 (by rfl) ⟨693476, by rfl⟩ : syracuseStep 924635 = 1386953) B1386953
theorem B1449575 : Blo 283827 1449575 := bstep (se 1 (by rfl) ⟨1087181, by rfl⟩ : syracuseStep 1449575 = 2174363) B2174363
theorem B3481355 : Blo 283827 3481355 := bstep (se 1 (by rfl) ⟨2611016, by rfl⟩ : syracuseStep 3481355 = 5222033) B5222033
theorem B4989053 : Blo 283827 4989053 := bstep (se 3 (by rfl) ⟨935447, by rfl⟩ : syracuseStep 4989053 = 1870895) B1870895
theorem B1843823 : Blo 283827 1843823 := bstep (se 1 (by rfl) ⟨1382867, by rfl⟩ : syracuseStep 1843823 = 2765735) B2765735
theorem B959201 : Blo 283827 959201 := bstep (se 2 (by rfl) ⟨359700, by rfl⟩ : syracuseStep 959201 = 719401) B719401
theorem B19768157 : Blo 283827 19768157 := bstep (se 3 (by rfl) ⟨3706529, by rfl⟩ : syracuseStep 19768157 = 7413059) B7413059
theorem B1451681 : Blo 283827 1451681 := bstep (se 2 (by rfl) ⟨544380, by rfl⟩ : syracuseStep 1451681 = 1088761) B1088761
theorem B1550299 : Blo 283827 1550299 := bstep (se 1 (by rfl) ⟨1162724, by rfl⟩ : syracuseStep 1550299 = 2325449) B2325449
theorem B2762849 : Blo 283827 2762849 := bstep (se 2 (by rfl) ⟨1036068, by rfl⟩ : syracuseStep 2762849 = 2072137) B2072137
theorem B5220865 : Blo 283827 5220865 := bstep (se 2 (by rfl) ⟨1957824, by rfl⟩ : syracuseStep 5220865 = 3915649) B3915649
theorem B895943 : Blo 283827 895943 := bstep (se 1 (by rfl) ⟨671957, by rfl⟩ : syracuseStep 895943 = 1343915) B1343915
theorem B1093151 : Blo 283827 1093151 := bstep (se 1 (by rfl) ⟨819863, by rfl⟩ : syracuseStep 1093151 = 1639727) B1639727
theorem B1617515 : Blo 283827 1617515 := bstep (se 1 (by rfl) ⟨1213136, by rfl⟩ : syracuseStep 1617515 = 2426273) B2426273
theorem B3682361 : Blo 283827 3682361 := bstep (se 2 (by rfl) ⟨1380885, by rfl⟩ : syracuseStep 3682361 = 2761771) B2761771
theorem B7811599 : Blo 283827 7811599 := bstep (se 1 (by rfl) ⟨5858699, by rfl⟩ : syracuseStep 7811599 = 11717399) B11717399
theorem B3453677 : Blo 283827 3453677 := bstep (se 3 (by rfl) ⟨647564, by rfl⟩ : syracuseStep 3453677 = 1295129) B1295129
theorem B767407 : Blo 283827 767407 := bstep (se 1 (by rfl) ⟨575555, by rfl⟩ : syracuseStep 767407 = 1151111) B1151111
theorem B2472059 : Blo 283827 2472059 := bstep (se 1 (by rfl) ⟨1854044, by rfl⟩ : syracuseStep 2472059 = 3708089) B3708089
theorem B1456865 : Blo 283827 1456865 := bstep (se 2 (by rfl) ⟨546324, by rfl⟩ : syracuseStep 1456865 = 1092649) B1092649
theorem B1620931 : Blo 283827 1620931 := bstep (se 1 (by rfl) ⟨1215698, by rfl⟩ : syracuseStep 1620931 = 2431397) B2431397
theorem B408559 : Blo 283827 408559 := bstep (se 1 (by rfl) ⟨306419, by rfl⟩ : syracuseStep 408559 = 612839) B612839
theorem B539855 : Blo 283827 539855 := bstep (se 1 (by rfl) ⟨404891, by rfl⟩ : syracuseStep 539855 = 809783) B809783
theorem B1326431 : Blo 283827 1326431 := bstep (se 1 (by rfl) ⟨994823, by rfl⟩ : syracuseStep 1326431 = 1989647) B1989647
theorem B2932139 : Blo 283827 2932139 := bstep (se 1 (by rfl) ⟨2199104, by rfl⟩ : syracuseStep 2932139 = 4398209) B4398209
theorem B966059 : Blo 283827 966059 := bstep (se 1 (by rfl) ⟨724544, by rfl⟩ : syracuseStep 966059 = 1449089) B1449089
theorem B22887947 : Blo 283827 22887947 := bstep (se 1 (by rfl) ⟨17165960, by rfl⟩ : syracuseStep 22887947 = 34331921) B34331921
theorem B736897 : Blo 283827 736897 := bstep (se 2 (by rfl) ⟨276336, by rfl⟩ : syracuseStep 736897 = 552673) B552673
theorem B966599 : Blo 283827 966599 := bstep (se 1 (by rfl) ⟨724949, by rfl⟩ : syracuseStep 966599 = 1449899) B1449899
theorem B1032425 : Blo 283827 1032425 := bstep (se 2 (by rfl) ⟨387159, by rfl⟩ : syracuseStep 1032425 = 774319) B774319
theorem B6603227 : Blo 283827 6603227 := bstep (se 1 (by rfl) ⟨4952420, by rfl⟩ : syracuseStep 6603227 = 9904841) B9904841
theorem B130892591 : Blo 283827 130892591 := bstep (se 1 (by rfl) ⟨98169443, by rfl⟩ : syracuseStep 130892591 = 196338887) B196338887
theorem B2180681 : Blo 283827 2180681 := bstep (se 2 (by rfl) ⟨817755, by rfl⟩ : syracuseStep 2180681 = 1635511) B1635511
theorem B641051 : Blo 283827 641051 := bstep (se 1 (by rfl) ⟨480788, by rfl⟩ : syracuseStep 641051 = 961577) B961577
theorem B1460369 : Blo 283827 1460369 := bstep (se 2 (by rfl) ⟨547638, by rfl⟩ : syracuseStep 1460369 = 1095277) B1095277
theorem B641231 : Blo 283827 641231 := bstep (se 1 (by rfl) ⟨480923, by rfl⟩ : syracuseStep 641231 = 961847) B961847
theorem B6998521 : Blo 283827 6998521 := bstep (se 2 (by rfl) ⟨2624445, by rfl⟩ : syracuseStep 6998521 = 5248891) B5248891
theorem B3263003 : Blo 283827 3263003 := bstep (se 1 (by rfl) ⟨2447252, by rfl⟩ : syracuseStep 3263003 = 4894505) B4894505
theorem B641627 : Blo 283827 641627 := bstep (se 1 (by rfl) ⟨481220, by rfl⟩ : syracuseStep 641627 = 962441) B962441
theorem B969569 : Blo 283827 969569 := bstep (se 2 (by rfl) ⟨363588, by rfl⟩ : syracuseStep 969569 = 727177) B727177
theorem B1821703 : Blo 283827 1821703 := bstep (se 1 (by rfl) ⟨1366277, by rfl⟩ : syracuseStep 1821703 = 2732555) B2732555
theorem B544009 : Blo 283827 544009 := bstep (se 2 (by rfl) ⟨204003, by rfl⟩ : syracuseStep 544009 = 408007) B408007
theorem B2182625 : Blo 283827 2182625 := bstep (se 2 (by rfl) ⟨818484, by rfl⟩ : syracuseStep 2182625 = 1636969) B1636969
theorem B970487 : Blo 283827 970487 := bstep (se 1 (by rfl) ⟨727865, by rfl⟩ : syracuseStep 970487 = 1455731) B1455731
theorem B2740243 : Blo 283827 2740243 := bstep (se 1 (by rfl) ⟨2055182, by rfl⟩ : syracuseStep 2740243 = 4110365) B4110365
theorem B971027 : Blo 283827 971027 := bstep (se 1 (by rfl) ⟨728270, by rfl⟩ : syracuseStep 971027 = 1456541) B1456541
theorem B2609633 : Blo 283827 2609633 := bstep (se 2 (by rfl) ⟨978612, by rfl⟩ : syracuseStep 2609633 = 1957225) B1957225
theorem B1626763 : Blo 283827 1626763 := bstep (se 1 (by rfl) ⟨1220072, by rfl⟩ : syracuseStep 1626763 = 2440145) B2440145
theorem B283871 : Blo 283827 283871 := bstep (se 1 (by rfl) ⟨212903, by rfl⟩ : syracuseStep 283871 = 425807) B425807
theorem B873737 : Blo 283827 873737 := bstep (se 2 (by rfl) ⟨327651, by rfl⟩ : syracuseStep 873737 = 655303) B655303
theorem B283951 : Blo 283827 283951 := bstep (se 1 (by rfl) ⟨212963, by rfl⟩ : syracuseStep 283951 = 425927) B425927
theorem B480559 : Blo 283827 480559 := bstep (se 1 (by rfl) ⟨360419, by rfl⟩ : syracuseStep 480559 = 720839) B720839
theorem B3462671 : Blo 283827 3462671 := bstep (se 1 (by rfl) ⟨2597003, by rfl⟩ : syracuseStep 3462671 = 5194007) B5194007
theorem B284191 : Blo 283827 284191 := bstep (se 1 (by rfl) ⟨213143, by rfl⟩ : syracuseStep 284191 = 426287) B426287
theorem B644777 : Blo 283827 644777 := bstep (se 2 (by rfl) ⟨241791, by rfl⟩ : syracuseStep 644777 = 483583) B483583
theorem B284351 : Blo 283827 284351 := bstep (se 1 (by rfl) ⟨213263, by rfl⟩ : syracuseStep 284351 = 426527) B426527
theorem B808667 : Blo 283827 808667 := bstep (se 1 (by rfl) ⟨606500, by rfl⟩ : syracuseStep 808667 = 1213001) B1213001
theorem B1824551 : Blo 283827 1824551 := bstep (se 1 (by rfl) ⟨1368413, by rfl⟩ : syracuseStep 1824551 = 2736827) B2736827
theorem B644903 : Blo 283827 644903 := bstep (se 1 (by rfl) ⟨483677, by rfl⟩ : syracuseStep 644903 = 967355) B967355
theorem B284799 : Blo 283827 284799 := bstep (se 1 (by rfl) ⟨213599, by rfl⟩ : syracuseStep 284799 = 427199) B427199
theorem B809099 : Blo 283827 809099 := bstep (se 1 (by rfl) ⟨606824, by rfl⟩ : syracuseStep 809099 = 1213649) B1213649
theorem B284895 : Blo 283827 284895 := bstep (se 1 (by rfl) ⟨213671, by rfl⟩ : syracuseStep 284895 = 427343) B427343
theorem B481511 : Blo 283827 481511 := bstep (se 1 (by rfl) ⟨361133, by rfl⟩ : syracuseStep 481511 = 722267) B722267
theorem B284955 : Blo 283827 284955 := bstep (se 1 (by rfl) ⟨213716, by rfl⟩ : syracuseStep 284955 = 427433) B427433
theorem B285055 : Blo 283827 285055 := bstep (se 1 (by rfl) ⟨213791, by rfl⟩ : syracuseStep 285055 = 427583) B427583
theorem B285083 : Blo 283827 285083 := bstep (se 1 (by rfl) ⟨213812, by rfl⟩ : syracuseStep 285083 = 427625) B427625
theorem B285375 : Blo 283827 285375 := bstep (se 1 (by rfl) ⟨214031, by rfl⟩ : syracuseStep 285375 = 428063) B428063
theorem B285503 : Blo 283827 285503 := bstep (se 1 (by rfl) ⟨214127, by rfl⟩ : syracuseStep 285503 = 428255) B428255
theorem B285543 : Blo 283827 285543 := bstep (se 1 (by rfl) ⟨214157, by rfl⟩ : syracuseStep 285543 = 428315) B428315
theorem B646055 : Blo 283827 646055 := bstep (se 1 (by rfl) ⟨484541, by rfl⟩ : syracuseStep 646055 = 969083) B969083
theorem B285759 : Blo 283827 285759 := bstep (se 1 (by rfl) ⟨214319, by rfl⟩ : syracuseStep 285759 = 428639) B428639
theorem B1039451 : Blo 283827 1039451 := bstep (se 1 (by rfl) ⟨779588, by rfl⟩ : syracuseStep 1039451 = 1559177) B1559177
theorem B646235 : Blo 283827 646235 := bstep (se 1 (by rfl) ⟨484676, by rfl⟩ : syracuseStep 646235 = 969353) B969353
theorem B285947 : Blo 283827 285947 := bstep (se 1 (by rfl) ⟨214460, by rfl⟩ : syracuseStep 285947 = 428921) B428921
theorem B285979 : Blo 283827 285979 := bstep (se 1 (by rfl) ⟨214484, by rfl⟩ : syracuseStep 285979 = 428969) B428969
theorem B2743591 : Blo 283827 2743591 := bstep (se 1 (by rfl) ⟨2057693, by rfl⟩ : syracuseStep 2743591 = 4115387) B4115387
theorem B286079 : Blo 283827 286079 := bstep (se 1 (by rfl) ⟨214559, by rfl⟩ : syracuseStep 286079 = 429119) B429119
theorem B974263 : Blo 283827 974263 := bstep (se 1 (by rfl) ⟨730697, by rfl⟩ : syracuseStep 974263 = 1461395) B1461395
theorem B286447 : Blo 283827 286447 := bstep (se 1 (by rfl) ⟨214835, by rfl⟩ : syracuseStep 286447 = 429671) B429671
theorem B483239 : Blo 283827 483239 := bstep (se 1 (by rfl) ⟨362429, by rfl⟩ : syracuseStep 483239 = 724859) B724859
theorem B647081 : Blo 283827 647081 := bstep (se 2 (by rfl) ⟨242655, by rfl⟩ : syracuseStep 647081 = 485311) B485311
theorem B286703 : Blo 283827 286703 := bstep (se 1 (by rfl) ⟨215027, by rfl⟩ : syracuseStep 286703 = 430055) B430055
theorem B286783 : Blo 283827 286783 := bstep (se 1 (by rfl) ⟨215087, by rfl⟩ : syracuseStep 286783 = 430175) B430175
theorem B286791 : Blo 283827 286791 := bstep (se 1 (by rfl) ⟨215093, by rfl⟩ : syracuseStep 286791 = 430187) B430187
theorem B286823 : Blo 283827 286823 := bstep (se 1 (by rfl) ⟨215117, by rfl⟩ : syracuseStep 286823 = 430235) B430235
theorem B1630637 : Blo 283827 1630637 := bstep (se 3 (by rfl) ⟨305744, by rfl⟩ : syracuseStep 1630637 = 611489) B611489
theorem B4907627 : Blo 283827 4907627 := bstep (se 1 (by rfl) ⟨3680720, by rfl⟩ : syracuseStep 4907627 = 7361441) B7361441
theorem B287391 : Blo 283827 287391 := bstep (se 1 (by rfl) ⟨215543, by rfl⟩ : syracuseStep 287391 = 431087) B431087
theorem B287647 : Blo 283827 287647 := bstep (se 1 (by rfl) ⟨215735, by rfl⟩ : syracuseStep 287647 = 431471) B431471
theorem B812015 : Blo 283827 812015 := bstep (se 1 (by rfl) ⟨609011, by rfl⟩ : syracuseStep 812015 = 1218023) B1218023
theorem B287727 : Blo 283827 287727 := bstep (se 1 (by rfl) ⟨215795, by rfl⟩ : syracuseStep 287727 = 431591) B431591
theorem B1369199 : Blo 283827 1369199 := bstep (se 1 (by rfl) ⟨1026899, by rfl⟩ : syracuseStep 1369199 = 2053799) B2053799
theorem B1664509 : Blo 283827 1664509 := bstep (se 3 (by rfl) ⟨312095, by rfl⟩ : syracuseStep 1664509 = 624191) B624191
theorem B5891869 : Blo 283827 5891869 := bstep (se 3 (by rfl) ⟨1104725, by rfl⟩ : syracuseStep 5891869 = 2209451) B2209451
theorem B321403 : Blo 283827 321403 := bstep (se 1 (by rfl) ⟨241052, by rfl⟩ : syracuseStep 321403 = 482105) B482105
theorem B321439 : Blo 283827 321439 := bstep (se 1 (by rfl) ⟨241079, by rfl⟩ : syracuseStep 321439 = 482159) B482159
theorem B289903 : Blo 283827 289903 := bstep (se 1 (by rfl) ⟨217427, by rfl⟩ : syracuseStep 289903 = 434855) B434855
theorem B1567855 : Blo 283827 1567855 := bstep (se 1 (by rfl) ⟨1175891, by rfl⟩ : syracuseStep 1567855 = 2351783) B2351783
theorem B2977769 : Blo 283827 2977769 := bstep (se 2 (by rfl) ⟨1116663, by rfl⟩ : syracuseStep 2977769 = 2233327) B2233327
theorem B782747 : Blo 283827 782747 := bstep (se 1 (by rfl) ⟨587060, by rfl⟩ : syracuseStep 782747 = 1174121) B1174121
theorem B5468957 : Blo 283827 5468957 := bstep (se 3 (by rfl) ⟨1025429, by rfl⟩ : syracuseStep 5468957 = 2050859) B2050859
theorem B1536889 : Blo 283827 1536889 := bstep (se 2 (by rfl) ⟨576333, by rfl⟩ : syracuseStep 1536889 = 1152667) B1152667
theorem B816743 : Blo 283827 816743 := bstep (se 1 (by rfl) ⟨612557, by rfl⟩ : syracuseStep 816743 = 1225115) B1225115
theorem B817199 : Blo 283827 817199 := bstep (se 1 (by rfl) ⟨612899, by rfl⟩ : syracuseStep 817199 = 1225799) B1225799
theorem B3471437 : Blo 283827 3471437 := bstep (se 3 (by rfl) ⟨650894, by rfl⟩ : syracuseStep 3471437 = 1301789) B1301789
theorem B1603997 : Blo 283827 1603997 := bstep (se 3 (by rfl) ⟨300749, by rfl⟩ : syracuseStep 1603997 = 601499) B601499
theorem B1309729 : Blo 283827 1309729 := bstep (se 2 (by rfl) ⟨491148, by rfl⟩ : syracuseStep 1309729 = 982297) B982297
theorem B1834109 : Blo 283827 1834109 := bstep (se 3 (by rfl) ⟨343895, by rfl⟩ : syracuseStep 1834109 = 687791) B687791
theorem B359579 : Blo 283827 359579 := bstep (se 1 (by rfl) ⟨269684, by rfl⟩ : syracuseStep 359579 = 539369) B539369
theorem B1735991 : Blo 283827 1735991 := bstep (se 1 (by rfl) ⟨1301993, by rfl⟩ : syracuseStep 1735991 = 2603987) B2603987
theorem B687599 : Blo 283827 687599 := bstep (se 1 (by rfl) ⟨515699, by rfl⟩ : syracuseStep 687599 = 1031399) B1031399
theorem B1080823 : Blo 283827 1080823 := bstep (se 1 (by rfl) ⟨810617, by rfl⟩ : syracuseStep 1080823 = 1621235) B1621235
theorem B1441313 : Blo 283827 1441313 := bstep (se 2 (by rfl) ⟨540492, by rfl⟩ : syracuseStep 1441313 = 1080985) B1080985
theorem B425759 : Blo 283827 425759 := bstep (se 1 (by rfl) ⟨319319, by rfl⟩ : syracuseStep 425759 = 638639) B638639
theorem B425819 : Blo 283827 425819 := bstep (se 1 (by rfl) ⟨319364, by rfl⟩ : syracuseStep 425819 = 638729) B638729
theorem B360283 : Blo 283827 360283 := bstep (se 1 (by rfl) ⟨270212, by rfl⟩ : syracuseStep 360283 = 540425) B540425
theorem B1835135 : Blo 283827 1835135 := bstep (se 1 (by rfl) ⟨1376351, by rfl⟩ : syracuseStep 1835135 = 2752703) B2752703
theorem B688283 : Blo 283827 688283 := bstep (se 1 (by rfl) ⟨516212, by rfl⟩ : syracuseStep 688283 = 1032425) B1032425
theorem B1441961 : Blo 283827 1441961 := bstep (se 2 (by rfl) ⟨540735, by rfl⟩ : syracuseStep 1441961 = 1081471) B1081471
theorem B525127 : Blo 283827 525127 := bstep (se 1 (by rfl) ⟨393845, by rfl⟩ : syracuseStep 525127 = 787691) B787691
theorem B427367 : Blo 283827 427367 := bstep (se 1 (by rfl) ⟨320525, by rfl⟩ : syracuseStep 427367 = 641051) B641051
theorem B427487 : Blo 283827 427487 := bstep (se 1 (by rfl) ⟨320615, by rfl⟩ : syracuseStep 427487 = 641231) B641231
theorem B427751 : Blo 283827 427751 := bstep (se 1 (by rfl) ⟨320813, by rfl⟩ : syracuseStep 427751 = 641627) B641627
theorem B349046909 : Blo 283827 349046909 := bstep (se 3 (by rfl) ⟨65446295, by rfl⟩ : syracuseStep 349046909 = 130892591) B130892591
theorem B2427023 : Blo 283827 2427023 := bstep (se 1 (by rfl) ⟨1820267, by rfl⟩ : syracuseStep 2427023 = 3640535) B3640535
theorem B428537 : Blo 283827 428537 := bstep (se 2 (by rfl) ⟨160701, by rfl⟩ : syracuseStep 428537 = 321403) B321403
theorem B428585 : Blo 283827 428585 := bstep (se 2 (by rfl) ⟨160719, by rfl⟩ : syracuseStep 428585 = 321439) B321439
theorem B2067065 : Blo 283827 2067065 := bstep (se 2 (by rfl) ⟨775149, by rfl⟩ : syracuseStep 2067065 = 1550299) B1550299
theorem B1837799 : Blo 283827 1837799 := bstep (se 1 (by rfl) ⟨1378349, by rfl⟩ : syracuseStep 1837799 = 2756699) B2756699
theorem B2165615 : Blo 283827 2165615 := bstep (se 1 (by rfl) ⟨1624211, by rfl⟩ : syracuseStep 2165615 = 3248423) B3248423
theorem B1739755 : Blo 283827 1739755 := bstep (se 1 (by rfl) ⟨1304816, by rfl⟩ : syracuseStep 1739755 = 2609633) B2609633
theorem B429851 : Blo 283827 429851 := bstep (se 1 (by rfl) ⟨322388, by rfl⟩ : syracuseStep 429851 = 644777) B644777
theorem B1445687 : Blo 283827 1445687 := bstep (se 1 (by rfl) ⟨1084265, by rfl⟩ : syracuseStep 1445687 = 2168531) B2168531
theorem B1216367 : Blo 283827 1216367 := bstep (se 1 (by rfl) ⟨912275, by rfl⟩ : syracuseStep 1216367 = 1824551) B1824551
theorem B429935 : Blo 283827 429935 := bstep (se 1 (by rfl) ⟨322451, by rfl⟩ : syracuseStep 429935 = 644903) B644903
theorem B2428937 : Blo 283827 2428937 := bstep (se 2 (by rfl) ⟨910851, by rfl⟩ : syracuseStep 2428937 = 1821703) B1821703
theorem B725345 : Blo 283827 725345 := bstep (se 2 (by rfl) ⟨272004, by rfl⟩ : syracuseStep 725345 = 544009) B544009
theorem B430703 : Blo 283827 430703 := bstep (se 1 (by rfl) ⟨323027, by rfl⟩ : syracuseStep 430703 = 646055) B646055
theorem B430823 : Blo 283827 430823 := bstep (se 1 (by rfl) ⟨323117, by rfl⟩ : syracuseStep 430823 = 646235) B646235
theorem B431387 : Blo 283827 431387 := bstep (se 1 (by rfl) ⟨323540, by rfl⟩ : syracuseStep 431387 = 647081) B647081
theorem B1087091 : Blo 283827 1087091 := bstep (se 1 (by rfl) ⟨815318, by rfl⟩ : syracuseStep 1087091 = 1630637) B1630637
theorem B13178771 : Blo 283827 13178771 := bstep (se 1 (by rfl) ⟨9884078, by rfl⟩ : syracuseStep 13178771 = 19768157) B19768157
theorem B2169017 : Blo 283827 2169017 := bstep (se 2 (by rfl) ⟨813381, by rfl⟩ : syracuseStep 2169017 = 1626763) B1626763
theorem B1841899 : Blo 283827 1841899 := bstep (se 1 (by rfl) ⟨1381424, by rfl⟩ : syracuseStep 1841899 = 2762849) B2762849
theorem B1023209 : Blo 283827 1023209 := bstep (se 2 (by rfl) ⟨383703, by rfl⟩ : syracuseStep 1023209 = 767407) B767407
theorem B597295 : Blo 283827 597295 := bstep (se 1 (by rfl) ⟨447971, by rfl⟩ : syracuseStep 597295 = 895943) B895943
theorem B728767 : Blo 283827 728767 := bstep (se 1 (by rfl) ⟨546575, by rfl⟩ : syracuseStep 728767 = 1093151) B1093151
theorem B1449737 : Blo 283827 1449737 := bstep (se 2 (by rfl) ⟨543651, by rfl⟩ : syracuseStep 1449737 = 1087303) B1087303
theorem B958877 : Blo 283827 958877 := bstep (se 3 (by rfl) ⟨179789, by rfl⟩ : syracuseStep 958877 = 359579) B359579
theorem B2302451 : Blo 283827 2302451 := bstep (se 1 (by rfl) ⟨1726838, by rfl⟩ : syracuseStep 2302451 = 3453677) B3453677
theorem B3645971 : Blo 283827 3645971 := bstep (se 1 (by rfl) ⟨2734478, by rfl⟩ : syracuseStep 3645971 = 5468957) B5468957
theorem B1746305 : Blo 283827 1746305 := bstep (se 2 (by rfl) ⟨654864, by rfl⟩ : syracuseStep 1746305 = 1309729) B1309729
theorem B1648039 : Blo 283827 1648039 := bstep (se 1 (by rfl) ⟨1236029, by rfl⟩ : syracuseStep 1648039 = 2472059) B2472059
theorem B1222739 : Blo 283827 1222739 := bstep (se 1 (by rfl) ⟨917054, by rfl⟩ : syracuseStep 1222739 = 1834109) B1834109
theorem B1157327 : Blo 283827 1157327 := bstep (se 1 (by rfl) ⟨867995, by rfl⟩ : syracuseStep 1157327 = 1735991) B1735991
theorem B960875 : Blo 283827 960875 := bstep (se 1 (by rfl) ⟨720656, by rfl⟩ : syracuseStep 960875 = 1441313) B1441313
theorem B7940717 : Blo 283827 7940717 := bstep (se 3 (by rfl) ⟨1488884, by rfl⟩ : syracuseStep 7940717 = 2977769) B2977769
theorem B1616831 : Blo 283827 1616831 := bstep (se 1 (by rfl) ⟨1212623, by rfl⟩ : syracuseStep 1616831 = 2425247) B2425247
theorem B4402151 : Blo 283827 4402151 := bstep (se 1 (by rfl) ⟨3301613, by rfl⟩ : syracuseStep 4402151 = 6603227) B6603227
theorem B1224173 : Blo 283827 1224173 := bstep (se 3 (by rfl) ⟨229532, by rfl⟩ : syracuseStep 1224173 = 459065) B459065
theorem B1453787 : Blo 283827 1453787 := bstep (se 1 (by rfl) ⟨1090340, by rfl⟩ : syracuseStep 1453787 = 2180681) B2180681
theorem B962873 : Blo 283827 962873 := bstep (se 2 (by rfl) ⟨361077, by rfl⟩ : syracuseStep 962873 = 722155) B722155
theorem B2175335 : Blo 283827 2175335 := bstep (se 1 (by rfl) ⟨1631501, by rfl⟩ : syracuseStep 2175335 = 3263003) B3263003
theorem B963359 : Blo 283827 963359 := bstep (se 1 (by rfl) ⟨722519, by rfl⟩ : syracuseStep 963359 = 1445039) B1445039
theorem B1455083 : Blo 283827 1455083 := bstep (se 1 (by rfl) ⟨1091312, by rfl⟩ : syracuseStep 1455083 = 2182625) B2182625
theorem B964115 : Blo 283827 964115 := bstep (se 1 (by rfl) ⟨723086, by rfl⟩ : syracuseStep 964115 = 1446173) B1446173
theorem B5289761 : Blo 283827 5289761 := bstep (se 2 (by rfl) ⟨1983660, by rfl⟩ : syracuseStep 5289761 = 3967321) B3967321
theorem B1030043 : Blo 283827 1030043 := bstep (se 1 (by rfl) ⟨772532, by rfl⟩ : syracuseStep 1030043 = 1545065) B1545065
theorem B6961153 : Blo 283827 6961153 := bstep (se 2 (by rfl) ⟨2610432, by rfl⟩ : syracuseStep 6961153 = 5220865) B5220865
theorem B2308447 : Blo 283827 2308447 := bstep (se 1 (by rfl) ⟨1731335, by rfl⟩ : syracuseStep 2308447 = 3462671) B3462671
theorem B539111 : Blo 283827 539111 := bstep (se 1 (by rfl) ⟨404333, by rfl⟩ : syracuseStep 539111 = 808667) B808667
theorem B539399 : Blo 283827 539399 := bstep (se 1 (by rfl) ⟨404549, by rfl⟩ : syracuseStep 539399 = 809099) B809099
theorem B1227575 : Blo 283827 1227575 := bstep (se 1 (by rfl) ⟨920681, by rfl⟩ : syracuseStep 1227575 = 1841363) B1841363
theorem B7847059 : Blo 283827 7847059 := bstep (se 1 (by rfl) ⟨5885294, by rfl⟩ : syracuseStep 7847059 = 11770589) B11770589
theorem B966383 : Blo 283827 966383 := bstep (se 1 (by rfl) ⟨724787, by rfl⟩ : syracuseStep 966383 = 1449575) B1449575
theorem B3653657 : Blo 283827 3653657 := bstep (se 2 (by rfl) ⟨1370121, by rfl⟩ : syracuseStep 3653657 = 2740243) B2740243
theorem B3326035 : Blo 283827 3326035 := bstep (se 1 (by rfl) ⟨2494526, by rfl⟩ : syracuseStep 3326035 = 4989053) B4989053
theorem B1229215 : Blo 283827 1229215 := bstep (se 1 (by rfl) ⟨921911, by rfl⟩ : syracuseStep 1229215 = 1843823) B1843823
theorem B639467 : Blo 283827 639467 := bstep (se 1 (by rfl) ⟨479600, by rfl⟩ : syracuseStep 639467 = 959201) B959201
theorem B541343 : Blo 283827 541343 := bstep (se 1 (by rfl) ⟨406007, by rfl⟩ : syracuseStep 541343 = 812015) B812015
theorem B967787 : Blo 283827 967787 := bstep (se 1 (by rfl) ⟨725840, by rfl⟩ : syracuseStep 967787 = 1451681) B1451681
theorem B2049185 : Blo 283827 2049185 := bstep (se 2 (by rfl) ⟨768444, by rfl⟩ : syracuseStep 2049185 = 1536889) B1536889
theorem B640745 : Blo 283827 640745 := bstep (se 2 (by rfl) ⟨240279, by rfl⟩ : syracuseStep 640745 = 480559) B480559
theorem B2771869 : Blo 283827 2771869 := bstep (se 3 (by rfl) ⟨519725, by rfl⟩ : syracuseStep 2771869 = 1039451) B1039451
theorem B544495 : Blo 283827 544495 := bstep (se 1 (by rfl) ⟨408371, by rfl⟩ : syracuseStep 544495 = 816743) B816743
theorem B544745 : Blo 283827 544745 := bstep (se 2 (by rfl) ⟨204279, by rfl⟩ : syracuseStep 544745 = 408559) B408559
theorem B544799 : Blo 283827 544799 := bstep (se 1 (by rfl) ⟨408599, by rfl⟩ : syracuseStep 544799 = 817199) B817199
theorem B2314291 : Blo 283827 2314291 := bstep (se 1 (by rfl) ⟨1735718, by rfl⟩ : syracuseStep 2314291 = 3471437) B3471437
theorem B1069331 : Blo 283827 1069331 := bstep (se 1 (by rfl) ⟨801998, by rfl⟩ : syracuseStep 1069331 = 1603997) B1603997
theorem B3658121 : Blo 283827 3658121 := bstep (se 2 (by rfl) ⟨1371795, by rfl⟩ : syracuseStep 3658121 = 2743591) B2743591
theorem B971243 : Blo 283827 971243 := bstep (se 1 (by rfl) ⟨728432, by rfl⟩ : syracuseStep 971243 = 1456865) B1456865
theorem B1299017 : Blo 283827 1299017 := bstep (se 2 (by rfl) ⟨487131, by rfl⟩ : syracuseStep 1299017 = 974263) B974263
theorem B1954759 : Blo 283827 1954759 := bstep (se 1 (by rfl) ⟨1466069, by rfl⟩ : syracuseStep 1954759 = 2932139) B2932139
theorem B644039 : Blo 283827 644039 := bstep (se 1 (by rfl) ⟨483029, by rfl⟩ : syracuseStep 644039 = 966059) B966059
theorem B15258631 : Blo 283827 15258631 := bstep (se 1 (by rfl) ⟨11443973, by rfl⟩ : syracuseStep 15258631 = 22887947) B22887947
theorem B480377 : Blo 283827 480377 := bstep (se 2 (by rfl) ⟨180141, by rfl⟩ : syracuseStep 480377 = 360283) B360283
theorem B283839 : Blo 283827 283839 := bstep (se 1 (by rfl) ⟨212879, by rfl⟩ : syracuseStep 283839 = 425759) B425759
theorem B283879 : Blo 283827 283879 := bstep (se 1 (by rfl) ⟨212909, by rfl⟩ : syracuseStep 283879 = 425819) B425819
theorem B644399 : Blo 283827 644399 := bstep (se 1 (by rfl) ⟨483299, by rfl⟩ : syracuseStep 644399 = 966599) B966599
theorem B284159 : Blo 283827 284159 := bstep (se 1 (by rfl) ⟨213119, by rfl⟩ : syracuseStep 284159 = 426239) B426239
theorem B284263 : Blo 283827 284263 := bstep (se 1 (by rfl) ⟨213197, by rfl⟩ : syracuseStep 284263 = 426395) B426395
theorem B808555 : Blo 283827 808555 := bstep (se 1 (by rfl) ⟨606416, by rfl⟩ : syracuseStep 808555 = 1212833) B1212833
theorem B2053775 : Blo 283827 2053775 := bstep (se 1 (by rfl) ⟨1540331, by rfl⟩ : syracuseStep 2053775 = 3080663) B3080663
theorem B480937 : Blo 283827 480937 := bstep (se 2 (by rfl) ⟨180351, by rfl⟩ : syracuseStep 480937 = 360703) B360703
theorem B284543 : Blo 283827 284543 := bstep (se 1 (by rfl) ⟨213407, by rfl⟩ : syracuseStep 284543 = 426815) B426815
theorem B284639 : Blo 283827 284639 := bstep (se 1 (by rfl) ⟨213479, by rfl⟩ : syracuseStep 284639 = 426959) B426959
theorem B284699 : Blo 283827 284699 := bstep (se 1 (by rfl) ⟨213524, by rfl⟩ : syracuseStep 284699 = 427049) B427049
theorem B284719 : Blo 283827 284719 := bstep (se 1 (by rfl) ⟨213539, by rfl⟩ : syracuseStep 284719 = 427079) B427079
theorem B284839 : Blo 283827 284839 := bstep (se 1 (by rfl) ⟨213629, by rfl⟩ : syracuseStep 284839 = 427259) B427259
theorem B285031 : Blo 283827 285031 := bstep (se 1 (by rfl) ⟨213773, by rfl⟩ : syracuseStep 285031 = 427547) B427547
theorem B481639 : Blo 283827 481639 := bstep (se 1 (by rfl) ⟨361229, by rfl⟩ : syracuseStep 481639 = 722459) B722459
theorem B285287 : Blo 283827 285287 := bstep (se 1 (by rfl) ⟨213965, by rfl⟩ : syracuseStep 285287 = 427931) B427931
theorem B285311 : Blo 283827 285311 := bstep (se 1 (by rfl) ⟨213983, by rfl⟩ : syracuseStep 285311 = 427967) B427967
theorem B809851 : Blo 283827 809851 := bstep (se 1 (by rfl) ⟨607388, by rfl⟩ : syracuseStep 809851 = 1214777) B1214777
theorem B3496925 : Blo 283827 3496925 := bstep (se 3 (by rfl) ⟨655673, by rfl⟩ : syracuseStep 3496925 = 1311347) B1311347
theorem B285727 : Blo 283827 285727 := bstep (se 1 (by rfl) ⟨214295, by rfl⟩ : syracuseStep 285727 = 428591) B428591
theorem B482395 : Blo 283827 482395 := bstep (se 1 (by rfl) ⟨361796, by rfl⟩ : syracuseStep 482395 = 723593) B723593
theorem B285807 : Blo 283827 285807 := bstep (se 1 (by rfl) ⟨214355, by rfl⟩ : syracuseStep 285807 = 428711) B428711
theorem B285851 : Blo 283827 285851 := bstep (se 1 (by rfl) ⟨214388, by rfl⟩ : syracuseStep 285851 = 428777) B428777
theorem B285855 : Blo 283827 285855 := bstep (se 1 (by rfl) ⟨214391, by rfl⟩ : syracuseStep 285855 = 428783) B428783
theorem B285887 : Blo 283827 285887 := bstep (se 1 (by rfl) ⟨214415, by rfl⟩ : syracuseStep 285887 = 428831) B428831
theorem B646379 : Blo 283827 646379 := bstep (se 1 (by rfl) ⟨484784, by rfl⟩ : syracuseStep 646379 = 969569) B969569
theorem B2219345 : Blo 283827 2219345 := bstep (se 2 (by rfl) ⟨832254, by rfl⟩ : syracuseStep 2219345 = 1664509) B1664509
theorem B286107 : Blo 283827 286107 := bstep (se 1 (by rfl) ⟨214580, by rfl⟩ : syracuseStep 286107 = 429161) B429161
theorem B286191 : Blo 283827 286191 := bstep (se 1 (by rfl) ⟨214643, by rfl⟩ : syracuseStep 286191 = 429287) B429287
theorem B2448893 : Blo 283827 2448893 := bstep (se 3 (by rfl) ⟨459167, by rfl⟩ : syracuseStep 2448893 = 918335) B918335
theorem B7855825 : Blo 283827 7855825 := bstep (se 2 (by rfl) ⟨2945934, by rfl⟩ : syracuseStep 7855825 = 5891869) B5891869
theorem B286527 : Blo 283827 286527 := bstep (se 1 (by rfl) ⟨214895, by rfl⟩ : syracuseStep 286527 = 429791) B429791
theorem B646991 : Blo 283827 646991 := bstep (se 1 (by rfl) ⟨485243, by rfl⟩ : syracuseStep 646991 = 970487) B970487
theorem B286715 : Blo 283827 286715 := bstep (se 1 (by rfl) ⟨215036, by rfl⟩ : syracuseStep 286715 = 430073) B430073
theorem B483455 : Blo 283827 483455 := bstep (se 1 (by rfl) ⟨362591, by rfl⟩ : syracuseStep 483455 = 725183) B725183
theorem B286847 : Blo 283827 286847 := bstep (se 1 (by rfl) ⟨215135, by rfl⟩ : syracuseStep 286847 = 430271) B430271
theorem B286875 : Blo 283827 286875 := bstep (se 1 (by rfl) ⟨215156, by rfl⟩ : syracuseStep 286875 = 430313) B430313
theorem B647351 : Blo 283827 647351 := bstep (se 1 (by rfl) ⟨485513, by rfl⟩ : syracuseStep 647351 = 971027) B971027
theorem B286959 : Blo 283827 286959 := bstep (se 1 (by rfl) ⟨215219, by rfl⟩ : syracuseStep 286959 = 430439) B430439
theorem B2318699 : Blo 283827 2318699 := bstep (se 1 (by rfl) ⟨1739024, by rfl⟩ : syracuseStep 2318699 = 3478049) B3478049
theorem B9331361 : Blo 283827 9331361 := bstep (se 2 (by rfl) ⟨3499260, by rfl⟩ : syracuseStep 9331361 = 6998521) B6998521
theorem B484123 : Blo 283827 484123 := bstep (se 1 (by rfl) ⟨363092, by rfl⟩ : syracuseStep 484123 = 726185) B726185
theorem B287515 : Blo 283827 287515 := bstep (se 1 (by rfl) ⟨215636, by rfl⟩ : syracuseStep 287515 = 431273) B431273
theorem B287559 : Blo 283827 287559 := bstep (se 1 (by rfl) ⟨215669, by rfl⟩ : syracuseStep 287559 = 431339) B431339
theorem B582491 : Blo 283827 582491 := bstep (se 1 (by rfl) ⟨436868, by rfl⟩ : syracuseStep 582491 = 873737) B873737
theorem B287615 : Blo 283827 287615 := bstep (se 1 (by rfl) ⟨215711, by rfl⟩ : syracuseStep 287615 = 431423) B431423
theorem B287743 : Blo 283827 287743 := bstep (se 1 (by rfl) ⟨215807, by rfl⟩ : syracuseStep 287743 = 431615) B431615
theorem B484393 : Blo 283827 484393 := bstep (se 2 (by rfl) ⟨181647, by rfl⟩ : syracuseStep 484393 = 363295) B363295
theorem B287815 : Blo 283827 287815 := bstep (se 1 (by rfl) ⟨215861, by rfl⟩ : syracuseStep 287815 = 431723) B431723
theorem B812243 : Blo 283827 812243 := bstep (se 1 (by rfl) ⟨609182, by rfl⟩ : syracuseStep 812243 = 1218365) B1218365
theorem B386537 : Blo 283827 386537 := bstep (se 2 (by rfl) ⟨144951, by rfl⟩ : syracuseStep 386537 = 289903) B289903
theorem B2090473 : Blo 283827 2090473 := bstep (se 2 (by rfl) ⟨783927, by rfl⟩ : syracuseStep 2090473 = 1567855) B1567855
theorem B321007 : Blo 283827 321007 := bstep (se 1 (by rfl) ⟨240755, by rfl⟩ : syracuseStep 321007 = 481511) B481511
theorem B485095 : Blo 283827 485095 := bstep (se 1 (by rfl) ⟨363821, by rfl⟩ : syracuseStep 485095 = 727643) B727643
theorem B485291 : Blo 283827 485291 := bstep (se 1 (by rfl) ⟨363968, by rfl⟩ : syracuseStep 485291 = 727937) B727937
theorem B616423 : Blo 283827 616423 := bstep (se 1 (by rfl) ⟨462317, by rfl⟩ : syracuseStep 616423 = 924635) B924635
theorem B2320903 : Blo 283827 2320903 := bstep (se 1 (by rfl) ⟨1740677, by rfl⟩ : syracuseStep 2320903 = 3481355) B3481355
theorem B322159 : Blo 283827 322159 := bstep (se 1 (by rfl) ⟨241619, by rfl⟩ : syracuseStep 322159 = 483239) B483239
theorem B5466953 : Blo 283827 5466953 := bstep (se 2 (by rfl) ⟨2050107, by rfl⟩ : syracuseStep 5466953 = 4100215) B4100215
theorem B2452517 : Blo 283827 2452517 := bstep (se 4 (by rfl) ⟨229923, by rfl⟩ : syracuseStep 2452517 = 459847) B459847
theorem B3894317 : Blo 283827 3894317 := bstep (se 3 (by rfl) ⟨730184, by rfl⟩ : syracuseStep 3894317 = 1460369) B1460369
theorem B3271751 : Blo 283827 3271751 := bstep (se 1 (by rfl) ⟨2453813, by rfl⟩ : syracuseStep 3271751 = 4907627) B4907627
theorem B10415465 : Blo 283827 10415465 := bstep (se 2 (by rfl) ⟨3905799, by rfl⟩ : syracuseStep 10415465 = 7811599) B7811599
theorem B912799 : Blo 283827 912799 := bstep (se 1 (by rfl) ⟨684599, by rfl⟩ : syracuseStep 912799 = 1369199) B1369199
theorem B1078343 : Blo 283827 1078343 := bstep (se 1 (by rfl) ⟨808757, by rfl⟩ : syracuseStep 1078343 = 1617515) B1617515
theorem B2454907 : Blo 283827 2454907 := bstep (se 1 (by rfl) ⟨1841180, by rfl⟩ : syracuseStep 2454907 = 3682361) B3682361
theorem B521831 : Blo 283827 521831 := bstep (se 1 (by rfl) ⟨391373, by rfl⟩ : syracuseStep 521831 = 782747) B782747
theorem B2161241 : Blo 283827 2161241 := bstep (se 2 (by rfl) ⟨810465, by rfl⟩ : syracuseStep 2161241 = 1620931) B1620931
theorem B1441097 : Blo 283827 1441097 := bstep (se 2 (by rfl) ⟨540411, by rfl⟩ : syracuseStep 1441097 = 1080823) B1080823
theorem B359903 : Blo 283827 359903 := bstep (se 1 (by rfl) ⟨269927, by rfl⟩ : syracuseStep 359903 = 539855) B539855
theorem B982529 : Blo 283827 982529 := bstep (se 2 (by rfl) ⟨368448, by rfl⟩ : syracuseStep 982529 = 736897) B736897
theorem B884287 : Blo 283827 884287 := bstep (se 1 (by rfl) ⟨663215, by rfl⟩ : syracuseStep 884287 = 1326431) B1326431
theorem B458399 : Blo 283827 458399 := bstep (se 1 (by rfl) ⟨343799, by rfl⟩ : syracuseStep 458399 = 687599) B687599
theorem B458855 : Blo 283827 458855 := bstep (se 1 (by rfl) ⟨344141, by rfl⟩ : syracuseStep 458855 = 688283) B688283
theorem B426311 : Blo 283827 426311 := bstep (se 1 (by rfl) ⟨319733, by rfl⟩ : syracuseStep 426311 = 639467) B639467
theorem B1638953 : Blo 283827 1638953 := bstep (se 2 (by rfl) ⟨614607, by rfl⟩ : syracuseStep 1638953 = 1229215) B1229215
theorem B2851549 : Blo 283827 2851549 := bstep (se 3 (by rfl) ⟨534665, by rfl⟩ : syracuseStep 2851549 = 1069331) B1069331
theorem B427163 : Blo 283827 427163 := bstep (se 1 (by rfl) ⟨320372, by rfl⟩ : syracuseStep 427163 = 640745) B640745
theorem B1378043 : Blo 283827 1378043 := bstep (se 1 (by rfl) ⟨1033532, by rfl⟩ : syracuseStep 1378043 = 2067065) B2067065
theorem B1443581 : Blo 283827 1443581 := bstep (se 3 (by rfl) ⟨270671, by rfl⟩ : syracuseStep 1443581 = 541343) B541343
theorem B2197385 : Blo 283827 2197385 := bstep (se 2 (by rfl) ⟨824019, by rfl⟩ : syracuseStep 2197385 = 1648039) B1648039
theorem B1443743 : Blo 283827 1443743 := bstep (se 1 (by rfl) ⟨1082807, by rfl⟩ : syracuseStep 1443743 = 2165615) B2165615
theorem B428009 : Blo 283827 428009 := bstep (se 2 (by rfl) ⟨160503, by rfl⟩ : syracuseStep 428009 = 321007) B321007
theorem B821897 : Blo 283827 821897 := bstep (se 2 (by rfl) ⟨308211, by rfl⟩ : syracuseStep 821897 = 616423) B616423
theorem B363199 : Blo 283827 363199 := bstep (se 1 (by rfl) ⟨272399, by rfl⟩ : syracuseStep 363199 = 544799) B544799
theorem B429359 : Blo 283827 429359 := bstep (se 1 (by rfl) ⟨322019, by rfl⟩ : syracuseStep 429359 = 644039) B644039
theorem B429545 : Blo 283827 429545 := bstep (se 2 (by rfl) ⟨161079, by rfl⟩ : syracuseStep 429545 = 322159) B322159
theorem B429599 : Blo 283827 429599 := bstep (se 1 (by rfl) ⟨322199, by rfl⟩ : syracuseStep 429599 = 644399) B644399
theorem B724727 : Blo 283827 724727 := bstep (se 1 (by rfl) ⟨543545, by rfl⟩ : syracuseStep 724727 = 1087091) B1087091
theorem B8785847 : Blo 283827 8785847 := bstep (se 1 (by rfl) ⟨6589385, by rfl⟩ : syracuseStep 8785847 = 13178771) B13178771
theorem B1446011 : Blo 283827 1446011 := bstep (se 1 (by rfl) ⟨1084508, by rfl⟩ : syracuseStep 1446011 = 2169017) B2169017
theorem B2331283 : Blo 283827 2331283 := bstep (se 1 (by rfl) ⟨1748462, by rfl⟩ : syracuseStep 2331283 = 3496925) B3496925
theorem B430919 : Blo 283827 430919 := bstep (se 1 (by rfl) ⟨323189, by rfl⟩ : syracuseStep 430919 = 646379) B646379
theorem B1479563 : Blo 283827 1479563 := bstep (se 1 (by rfl) ⟨1109672, by rfl⟩ : syracuseStep 1479563 = 2219345) B2219345
theorem B725993 : Blo 283827 725993 := bstep (se 2 (by rfl) ⟨272247, by rfl⟩ : syracuseStep 725993 = 544495) B544495
theorem B431327 : Blo 283827 431327 := bstep (se 1 (by rfl) ⟨323495, by rfl⟩ : syracuseStep 431327 = 646991) B646991
theorem B3085721 : Blo 283827 3085721 := bstep (se 2 (by rfl) ⟨1157145, by rfl⟩ : syracuseStep 3085721 = 2314291) B2314291
theorem B431567 : Blo 283827 431567 := bstep (se 1 (by rfl) ⟨323675, by rfl⟩ : syracuseStep 431567 = 647351) B647351
theorem B1545799 : Blo 283827 1545799 := bstep (se 1 (by rfl) ⟨1159349, by rfl⟩ : syracuseStep 1545799 = 2318699) B2318699
theorem B2430647 : Blo 283827 2430647 := bstep (se 1 (by rfl) ⟨1822985, by rfl⟩ : syracuseStep 2430647 = 3645971) B3645971
theorem B3644635 : Blo 283827 3644635 := bstep (se 1 (by rfl) ⟨2733476, by rfl⟩ : syracuseStep 3644635 = 5466953) B5466953
theorem B2596211 : Blo 283827 2596211 := bstep (se 1 (by rfl) ⟨1947158, by rfl⟩ : syracuseStep 2596211 = 3894317) B3894317
theorem B9281537 : Blo 283827 9281537 := bstep (se 2 (by rfl) ⟨3480576, by rfl⟩ : syracuseStep 9281537 = 6961153) B6961153
theorem B1450223 : Blo 283827 1450223 := bstep (se 1 (by rfl) ⟨1087667, by rfl⟩ : syracuseStep 1450223 = 2175335) B2175335
theorem B959741 : Blo 283827 959741 := bstep (se 3 (by rfl) ⟨179951, by rfl⟩ : syracuseStep 959741 = 359903) B359903
theorem B10462745 : Blo 283827 10462745 := bstep (se 2 (by rfl) ⟨3923529, by rfl⟩ : syracuseStep 10462745 = 7847059) B7847059
theorem B796393 : Blo 283827 796393 := bstep (se 2 (by rfl) ⟨298647, by rfl⟩ : syracuseStep 796393 = 597295) B597295
theorem B1222397 : Blo 283827 1222397 := bstep (se 3 (by rfl) ⟨229199, by rfl⟩ : syracuseStep 1222397 = 458399) B458399
theorem B960731 : Blo 283827 960731 := bstep (se 1 (by rfl) ⟨720548, by rfl⟩ : syracuseStep 960731 = 1441097) B1441097
theorem B1452653 : Blo 283827 1452653 := bstep (se 3 (by rfl) ⟨272372, by rfl⟩ : syracuseStep 1452653 = 544745) B544745
theorem B2435771 : Blo 283827 2435771 := bstep (se 1 (by rfl) ⟨1826828, by rfl⟩ : syracuseStep 2435771 = 3653657) B3653657
theorem B1223423 : Blo 283827 1223423 := bstep (se 1 (by rfl) ⟨917567, by rfl⟩ : syracuseStep 1223423 = 1835135) B1835135
theorem B4434713 : Blo 283827 4434713 := bstep (se 2 (by rfl) ⟨1663017, by rfl⟩ : syracuseStep 4434713 = 3326035) B3326035
theorem B961307 : Blo 283827 961307 := bstep (se 1 (by rfl) ⟨720980, by rfl⟩ : syracuseStep 961307 = 1441961) B1441961
theorem B700169 : Blo 283827 700169 := bstep (se 2 (by rfl) ⟨262563, by rfl⟩ : syracuseStep 700169 = 525127) B525127
theorem B232697939 : Blo 283827 232697939 := bstep (se 1 (by rfl) ⟨174523454, by rfl⟩ : syracuseStep 232697939 = 349046909) B349046909
theorem B1618015 : Blo 283827 1618015 := bstep (se 1 (by rfl) ⟨1213511, by rfl⟩ : syracuseStep 1618015 = 2427023) B2427023
theorem B1225199 : Blo 283827 1225199 := bstep (se 1 (by rfl) ⟨918899, by rfl⟩ : syracuseStep 1225199 = 1837799) B1837799
theorem B963791 : Blo 283827 963791 := bstep (se 1 (by rfl) ⟨722843, by rfl⟩ : syracuseStep 963791 = 1445687) B1445687
theorem B1619291 : Blo 283827 1619291 := bstep (se 1 (by rfl) ⟨1214468, by rfl⟩ : syracuseStep 1619291 = 2428937) B2428937
theorem B2438747 : Blo 283827 2438747 := bstep (se 1 (by rfl) ⟨1829060, by rfl⟩ : syracuseStep 2438747 = 3658121) B3658121
theorem B866011 : Blo 283827 866011 := bstep (se 1 (by rfl) ⟨649508, by rfl⟩ : syracuseStep 866011 = 1299017) B1299017
theorem B3094537 : Blo 283827 3094537 := bstep (se 2 (by rfl) ⟨1160451, by rfl⟩ : syracuseStep 3094537 = 2320903) B2320903
theorem B1030765 : Blo 283827 1030765 := bstep (se 3 (by rfl) ⟨193268, by rfl⟩ : syracuseStep 1030765 = 386537) B386537
theorem B966491 : Blo 283827 966491 := bstep (se 1 (by rfl) ⟨724868, by rfl⟩ : syracuseStep 966491 = 1449737) B1449737
theorem B639251 : Blo 283827 639251 := bstep (se 1 (by rfl) ⟨479438, by rfl⟩ : syracuseStep 639251 = 958877) B958877
theorem B541495 : Blo 283827 541495 := bstep (se 1 (by rfl) ⟨406121, by rfl⟩ : syracuseStep 541495 = 812243) B812243
theorem B1164203 : Blo 283827 1164203 := bstep (se 1 (by rfl) ⟨873152, by rfl⟩ : syracuseStep 1164203 = 1746305) B1746305
theorem B2606345 : Blo 283827 2606345 := bstep (se 2 (by rfl) ⟨977379, by rfl⟩ : syracuseStep 2606345 = 1954759) B1954759
theorem B771551 : Blo 283827 771551 := bstep (se 1 (by rfl) ⟨578663, by rfl⟩ : syracuseStep 771551 = 1157327) B1157327
theorem B640583 : Blo 283827 640583 := bstep (se 1 (by rfl) ⟨480437, by rfl⟩ : syracuseStep 640583 = 960875) B960875
theorem B5293811 : Blo 283827 5293811 := bstep (se 1 (by rfl) ⟨3970358, by rfl⟩ : syracuseStep 5293811 = 7940717) B7940717
theorem B2934767 : Blo 283827 2934767 := bstep (se 1 (by rfl) ⟨2201075, by rfl⟩ : syracuseStep 2934767 = 4402151) B4402151
theorem B2181167 : Blo 283827 2181167 := bstep (se 1 (by rfl) ⟨1635875, by rfl⟩ : syracuseStep 2181167 = 3271751) B3271751
theorem B4868261 : Blo 283827 4868261 := bstep (se 4 (by rfl) ⟨456399, by rfl⟩ : syracuseStep 4868261 = 912799) B912799
theorem B641249 : Blo 283827 641249 := bstep (se 2 (by rfl) ⟨240468, by rfl⟩ : syracuseStep 641249 = 480937) B480937
theorem B969191 : Blo 283827 969191 := bstep (se 1 (by rfl) ⟨726893, by rfl⟩ : syracuseStep 969191 = 1453787) B1453787
theorem B641915 : Blo 283827 641915 := bstep (se 1 (by rfl) ⟨481436, by rfl⟩ : syracuseStep 641915 = 962873) B962873
theorem B642185 : Blo 283827 642185 := bstep (se 2 (by rfl) ⟨240819, by rfl⟩ : syracuseStep 642185 = 481639) B481639
theorem B642239 : Blo 283827 642239 := bstep (se 1 (by rfl) ⟨481679, by rfl⟩ : syracuseStep 642239 = 963359) B963359
theorem B970055 : Blo 283827 970055 := bstep (se 1 (by rfl) ⟨727541, by rfl⟩ : syracuseStep 970055 = 1455083) B1455083
theorem B642743 : Blo 283827 642743 := bstep (se 1 (by rfl) ⟨482057, by rfl⟩ : syracuseStep 642743 = 964115) B964115
theorem B347887 : Blo 283827 347887 := bstep (se 1 (by rfl) ⟨260915, by rfl⟩ : syracuseStep 347887 = 521831) B521831
theorem B3526507 : Blo 283827 3526507 := bstep (se 1 (by rfl) ⟨2644880, by rfl⟩ : syracuseStep 3526507 = 5289761) B5289761
theorem B3264461 : Blo 283827 3264461 := bstep (se 3 (by rfl) ⟨612086, by rfl⟩ : syracuseStep 3264461 = 1224173) B1224173
theorem B643193 : Blo 283827 643193 := bstep (se 2 (by rfl) ⟨241197, by rfl⟩ : syracuseStep 643193 = 482395) B482395
theorem B971689 : Blo 283827 971689 := bstep (se 2 (by rfl) ⟨364383, by rfl⟩ : syracuseStep 971689 = 728767) B728767
theorem B10474433 : Blo 283827 10474433 := bstep (se 2 (by rfl) ⟨3927912, by rfl⟩ : syracuseStep 10474433 = 7855825) B7855825
theorem B644255 : Blo 283827 644255 := bstep (se 1 (by rfl) ⟨483191, by rfl⟩ : syracuseStep 644255 = 966383) B966383
theorem B645191 : Blo 283827 645191 := bstep (se 1 (by rfl) ⟨483893, by rfl⟩ : syracuseStep 645191 = 967787) B967787
theorem B284911 : Blo 283827 284911 := bstep (se 1 (by rfl) ⟨213683, by rfl⟩ : syracuseStep 284911 = 427367) B427367
theorem B284991 : Blo 283827 284991 := bstep (se 1 (by rfl) ⟨213743, by rfl⟩ : syracuseStep 284991 = 427487) B427487
theorem B645497 : Blo 283827 645497 := bstep (se 2 (by rfl) ⟨242061, by rfl⟩ : syracuseStep 645497 = 484123) B484123
theorem B285167 : Blo 283827 285167 := bstep (se 1 (by rfl) ⟨213875, by rfl⟩ : syracuseStep 285167 = 427751) B427751
theorem B645857 : Blo 283827 645857 := bstep (se 2 (by rfl) ⟨242196, by rfl⟩ : syracuseStep 645857 = 484393) B484393
theorem B285691 : Blo 283827 285691 := bstep (se 1 (by rfl) ⟨214268, by rfl⟩ : syracuseStep 285691 = 428537) B428537
theorem B285723 : Blo 283827 285723 := bstep (se 1 (by rfl) ⟨214292, by rfl⟩ : syracuseStep 285723 = 428585) B428585
theorem B646793 : Blo 283827 646793 := bstep (se 2 (by rfl) ⟨242547, by rfl⟩ : syracuseStep 646793 = 485095) B485095
theorem B286567 : Blo 283827 286567 := bstep (se 1 (by rfl) ⟨214925, by rfl⟩ : syracuseStep 286567 = 429851) B429851
theorem B810911 : Blo 283827 810911 := bstep (se 1 (by rfl) ⟨608183, by rfl⟩ : syracuseStep 810911 = 1216367) B1216367
theorem B286623 : Blo 283827 286623 := bstep (se 1 (by rfl) ⟨214967, by rfl⟩ : syracuseStep 286623 = 429935) B429935
theorem B483563 : Blo 283827 483563 := bstep (se 1 (by rfl) ⟨362672, by rfl⟩ : syracuseStep 483563 = 725345) B725345
theorem B647495 : Blo 283827 647495 := bstep (se 1 (by rfl) ⟨485621, by rfl⟩ : syracuseStep 647495 = 971243) B971243
theorem B287135 : Blo 283827 287135 := bstep (se 1 (by rfl) ⟨215351, by rfl⟩ : syracuseStep 287135 = 430703) B430703
theorem B5464493 : Blo 283827 5464493 := bstep (se 3 (by rfl) ⟨1024592, by rfl⟩ : syracuseStep 5464493 = 2049185) B2049185
theorem B287215 : Blo 283827 287215 := bstep (se 1 (by rfl) ⟨215411, by rfl⟩ : syracuseStep 287215 = 430823) B430823
theorem B320251 : Blo 283827 320251 := bstep (se 1 (by rfl) ⟨240188, by rfl⟩ : syracuseStep 320251 = 480377) B480377
theorem B287591 : Blo 283827 287591 := bstep (se 1 (by rfl) ⟨215693, by rfl⟩ : syracuseStep 287591 = 431387) B431387
theorem B1369183 : Blo 283827 1369183 := bstep (se 1 (by rfl) ⟨1026887, by rfl⟩ : syracuseStep 1369183 = 2053775) B2053775
theorem B3695825 : Blo 283827 3695825 := bstep (se 2 (by rfl) ⟨1385934, by rfl⟩ : syracuseStep 3695825 = 2771869) B2771869
theorem B2319673 : Blo 283827 2319673 := bstep (se 2 (by rfl) ⟨869877, by rfl⟩ : syracuseStep 2319673 = 1739755) B1739755
theorem B682139 : Blo 283827 682139 := bstep (se 1 (by rfl) ⟨511604, by rfl⟩ : syracuseStep 682139 = 1023209) B1023209
theorem B1632595 : Blo 283827 1632595 := bstep (se 1 (by rfl) ⟨1224446, by rfl⟩ : syracuseStep 1632595 = 2448893) B2448893
theorem B2746781 : Blo 283827 2746781 := bstep (se 3 (by rfl) ⟨515021, by rfl⟩ : syracuseStep 2746781 = 1030043) B1030043
theorem B322303 : Blo 283827 322303 := bstep (se 1 (by rfl) ⟨241727, by rfl⟩ : syracuseStep 322303 = 483455) B483455
theorem B1534967 : Blo 283827 1534967 := bstep (se 1 (by rfl) ⟨1151225, by rfl⟩ : syracuseStep 1534967 = 2302451) B2302451
theorem B6220907 : Blo 283827 6220907 := bstep (se 1 (by rfl) ⟨4665680, by rfl⟩ : syracuseStep 6220907 = 9331361) B9331361
theorem B388327 : Blo 283827 388327 := bstep (se 1 (by rfl) ⟨291245, by rfl⟩ : syracuseStep 388327 = 582491) B582491
theorem B323527 : Blo 283827 323527 := bstep (se 1 (by rfl) ⟨242645, by rfl⟩ : syracuseStep 323527 = 485291) B485291
theorem B20344841 : Blo 283827 20344841 := bstep (se 2 (by rfl) ⟨7629315, by rfl⟩ : syracuseStep 20344841 = 15258631) B15258631
theorem B815159 : Blo 283827 815159 := bstep (se 1 (by rfl) ⟨611369, by rfl⟩ : syracuseStep 815159 = 1222739) B1222739
theorem B3273209 : Blo 283827 3273209 := bstep (se 2 (by rfl) ⟨1227453, by rfl⟩ : syracuseStep 3273209 = 2454907) B2454907
theorem B1077887 : Blo 283827 1077887 := bstep (se 1 (by rfl) ⟨808415, by rfl⟩ : syracuseStep 1077887 = 1616831) B1616831
theorem B1438397 : Blo 283827 1438397 := bstep (se 3 (by rfl) ⟨269699, by rfl⟩ : syracuseStep 1438397 = 539399) B539399
theorem B1635011 : Blo 283827 1635011 := bstep (se 1 (by rfl) ⟨1226258, by rfl⟩ : syracuseStep 1635011 = 2452517) B2452517
theorem B1078073 : Blo 283827 1078073 := bstep (se 2 (by rfl) ⟨404277, by rfl⟩ : syracuseStep 1078073 = 808555) B808555
theorem B6943643 : Blo 283827 6943643 := bstep (se 1 (by rfl) ⟨5207732, by rfl⟩ : syracuseStep 6943643 = 10415465) B10415465
theorem B3077929 : Blo 283827 3077929 := bstep (se 2 (by rfl) ⟨1154223, by rfl⟩ : syracuseStep 3077929 = 2308447) B2308447
theorem B718895 : Blo 283827 718895 := bstep (se 1 (by rfl) ⟨539171, by rfl⟩ : syracuseStep 718895 = 1078343) B1078343
theorem B2455865 : Blo 283827 2455865 := bstep (se 2 (by rfl) ⟨920949, by rfl⟩ : syracuseStep 2455865 = 1841899) B1841899
theorem B1079801 : Blo 283827 1079801 := bstep (se 2 (by rfl) ⟨404925, by rfl⟩ : syracuseStep 1079801 = 809851) B809851
theorem B359407 : Blo 283827 359407 := bstep (se 1 (by rfl) ⟨269555, by rfl⟩ : syracuseStep 359407 = 539111) B539111
theorem B1440827 : Blo 283827 1440827 := bstep (se 1 (by rfl) ⟨1080620, by rfl⟩ : syracuseStep 1440827 = 2161241) B2161241
theorem B818383 : Blo 283827 818383 := bstep (se 1 (by rfl) ⟨613787, by rfl⟩ : syracuseStep 818383 = 1227575) B1227575
theorem B1179049 : Blo 283827 1179049 := bstep (se 2 (by rfl) ⟨442143, by rfl⟩ : syracuseStep 1179049 = 884287) B884287
theorem B44596757 : Blo 283827 44596757 := bstep (se 6 (by rfl) ⟨1045236, by rfl⟩ : syracuseStep 44596757 = 2090473) B2090473
theorem B655019 : Blo 283827 655019 := bstep (se 1 (by rfl) ⟨491264, by rfl⟩ : syracuseStep 655019 = 982529) B982529
theorem B426167 : Blo 283827 426167 := bstep (se 1 (by rfl) ⟨319625, by rfl⟩ : syracuseStep 426167 = 639251) B639251
theorem B620527837 : Blo 283827 620527837 := bstep (se 3 (by rfl) ⟨116348969, by rfl⟩ : syracuseStep 620527837 = 232697939) B232697939
theorem B1737563 : Blo 283827 1737563 := bstep (se 1 (by rfl) ⟨1303172, by rfl⟩ : syracuseStep 1737563 = 2606345) B2606345
theorem B427001 : Blo 283827 427001 := bstep (se 2 (by rfl) ⟨160125, by rfl⟩ : syracuseStep 427001 = 320251) B320251
theorem B427055 : Blo 283827 427055 := bstep (se 1 (by rfl) ⟨320291, by rfl⟩ : syracuseStep 427055 = 640583) B640583
theorem B721993 : Blo 283827 721993 := bstep (se 2 (by rfl) ⟨270747, by rfl⟩ : syracuseStep 721993 = 541495) B541495
theorem B918695 : Blo 283827 918695 := bstep (se 1 (by rfl) ⟨689021, by rfl⟩ : syracuseStep 918695 = 1378043) B1378043
theorem B3245507 : Blo 283827 3245507 := bstep (se 1 (by rfl) ⟨2434130, by rfl⟩ : syracuseStep 3245507 = 4868261) B4868261
theorem B427499 : Blo 283827 427499 := bstep (se 1 (by rfl) ⟨320624, by rfl⟩ : syracuseStep 427499 = 641249) B641249
theorem B427943 : Blo 283827 427943 := bstep (se 1 (by rfl) ⟨320957, by rfl⟩ : syracuseStep 427943 = 641915) B641915
theorem B428123 : Blo 283827 428123 := bstep (se 1 (by rfl) ⟨321092, by rfl⟩ : syracuseStep 428123 = 642185) B642185
theorem B428159 : Blo 283827 428159 := bstep (se 1 (by rfl) ⟨321119, by rfl⟩ : syracuseStep 428159 = 642239) B642239
theorem B428495 : Blo 283827 428495 := bstep (se 1 (by rfl) ⟨321371, by rfl⟩ : syracuseStep 428495 = 642743) B642743
theorem B428795 : Blo 283827 428795 := bstep (se 1 (by rfl) ⟨321596, by rfl⟩ : syracuseStep 428795 = 643193) B643193
theorem B986375 : Blo 283827 986375 := bstep (se 1 (by rfl) ⟨739781, by rfl⟩ : syracuseStep 986375 = 1479563) B1479563
theorem B6982955 : Blo 283827 6982955 := bstep (se 1 (by rfl) ⟨5237216, by rfl⟩ : syracuseStep 6982955 = 10474433) B10474433
theorem B429503 : Blo 283827 429503 := bstep (se 1 (by rfl) ⟨322127, by rfl⟩ : syracuseStep 429503 = 644255) B644255
theorem B429737 : Blo 283827 429737 := bstep (se 2 (by rfl) ⟨161151, by rfl⟩ : syracuseStep 429737 = 322303) B322303
theorem B430127 : Blo 283827 430127 := bstep (se 1 (by rfl) ⟨322595, by rfl⟩ : syracuseStep 430127 = 645191) B645191
theorem B430331 : Blo 283827 430331 := bstep (se 1 (by rfl) ⟨322748, by rfl⟩ : syracuseStep 430331 = 645497) B645497
theorem B430571 : Blo 283827 430571 := bstep (se 1 (by rfl) ⟨322928, by rfl⟩ : syracuseStep 430571 = 645857) B645857
theorem B463849 : Blo 283827 463849 := bstep (se 2 (by rfl) ⟨173943, by rfl⟩ : syracuseStep 463849 = 347887) B347887
theorem B431195 : Blo 283827 431195 := bstep (se 1 (by rfl) ⟨323396, by rfl⟩ : syracuseStep 431195 = 646793) B646793
theorem B431369 : Blo 283827 431369 := bstep (se 2 (by rfl) ⟨161763, by rfl⟩ : syracuseStep 431369 = 323527) B323527
theorem B431663 : Blo 283827 431663 := bstep (se 1 (by rfl) ⟨323747, by rfl⟩ : syracuseStep 431663 = 647495) B647495
theorem B3642995 : Blo 283827 3642995 := bstep (se 1 (by rfl) ⟨2732246, by rfl⟩ : syracuseStep 3642995 = 5464493) B5464493
theorem B2956475 : Blo 283827 2956475 := bstep (se 1 (by rfl) ⟨2217356, by rfl⟩ : syracuseStep 2956475 = 4434713) B4434713
theorem B1023311 : Blo 283827 1023311 := bstep (se 1 (by rfl) ⟨767483, by rfl⟩ : syracuseStep 1023311 = 1534967) B1534967
theorem B1154681 : Blo 283827 1154681 := bstep (se 2 (by rfl) ⟨433005, by rfl⟩ : syracuseStep 1154681 = 866011) B866011
theorem B958931 : Blo 283827 958931 := bstep (se 1 (by rfl) ⟨719198, by rfl⟩ : syracuseStep 958931 = 1438397) B1438397
theorem B1090007 : Blo 283827 1090007 := bstep (se 1 (by rfl) ⟨817505, by rfl⟩ : syracuseStep 1090007 = 1635011) B1635011
theorem B4629095 : Blo 283827 4629095 := bstep (se 1 (by rfl) ⟨3471821, by rfl⟩ : syracuseStep 4629095 = 6943643) B6943643
theorem B1091177 : Blo 283827 1091177 := bstep (se 2 (by rfl) ⟨409191, by rfl⟩ : syracuseStep 1091177 = 818383) B818383
theorem B4859513 : Blo 283827 4859513 := bstep (se 2 (by rfl) ⟨1822317, by rfl⟩ : syracuseStep 4859513 = 3644635) B3644635
theorem B960551 : Blo 283827 960551 := bstep (se 1 (by rfl) ⟨720413, by rfl⟩ : syracuseStep 960551 = 1440827) B1440827
theorem B29731171 : Blo 283827 29731171 := bstep (se 1 (by rfl) ⟨22298378, by rfl⟩ : syracuseStep 29731171 = 44596757) B44596757
theorem B436679 : Blo 283827 436679 := bstep (se 1 (by rfl) ⟨327509, by rfl⟩ : syracuseStep 436679 = 655019) B655019
theorem B305903 : Blo 283827 305903 := bstep (se 1 (by rfl) ⟨229427, by rfl⟩ : syracuseStep 305903 = 458855) B458855
theorem B1092635 : Blo 283827 1092635 := bstep (se 1 (by rfl) ⟨819476, by rfl⟩ : syracuseStep 1092635 = 1638953) B1638953
theorem B962387 : Blo 283827 962387 := bstep (se 1 (by rfl) ⟨721790, by rfl⟩ : syracuseStep 962387 = 1443581) B1443581
theorem B962495 : Blo 283827 962495 := bstep (se 1 (by rfl) ⟨721871, by rfl⟩ : syracuseStep 962495 = 1443743) B1443743
theorem B1454111 : Blo 283827 1454111 := bstep (se 1 (by rfl) ⟨1090583, by rfl⟩ : syracuseStep 1454111 = 2181167) B2181167
theorem B3092897 : Blo 283827 3092897 := bstep (se 2 (by rfl) ⟨1159836, by rfl⟩ : syracuseStep 3092897 = 2319673) B2319673
theorem B1061857 : Blo 283827 1061857 := bstep (se 2 (by rfl) ⟨398196, by rfl⟩ : syracuseStep 1061857 = 796393) B796393
theorem B2176307 : Blo 283827 2176307 := bstep (se 1 (by rfl) ⟨1632230, by rfl⟩ : syracuseStep 2176307 = 3264461) B3264461
theorem B964007 : Blo 283827 964007 := bstep (se 1 (by rfl) ⟨723005, by rfl⟩ : syracuseStep 964007 = 1446011) B1446011
theorem B2176793 : Blo 283827 2176793 := bstep (se 2 (by rfl) ⟨816297, by rfl⟩ : syracuseStep 2176793 = 1632595) B1632595
theorem B1620431 : Blo 283827 1620431 := bstep (se 1 (by rfl) ⟨1215323, by rfl⟩ : syracuseStep 1620431 = 2430647) B2430647
theorem B60833045 : Blo 283827 60833045 := bstep (se 6 (by rfl) ⟨1425774, by rfl⟩ : syracuseStep 60833045 = 2851549) B2851549
theorem B4702009 : Blo 283827 4702009 := bstep (se 2 (by rfl) ⟨1763253, by rfl⟩ : syracuseStep 4702009 = 3526507) B3526507
theorem B540607 : Blo 283827 540607 := bstep (se 1 (by rfl) ⟨405455, by rfl⟩ : syracuseStep 540607 = 810911) B810911
theorem B966815 : Blo 283827 966815 := bstep (se 1 (by rfl) ⟨725111, by rfl⟩ : syracuseStep 966815 = 1450223) B1450223
theorem B1819037 : Blo 283827 1819037 := bstep (se 3 (by rfl) ⟨341069, by rfl⟩ : syracuseStep 1819037 = 682139) B682139
theorem B639827 : Blo 283827 639827 := bstep (se 1 (by rfl) ⟨479870, by rfl⟩ : syracuseStep 639827 = 959741) B959741
theorem B1295585 : Blo 283827 1295585 := bstep (se 2 (by rfl) ⟨485844, by rfl⟩ : syracuseStep 1295585 = 971689) B971689
theorem B640487 : Blo 283827 640487 := bstep (se 1 (by rfl) ⟨480365, by rfl⟩ : syracuseStep 640487 = 960731) B960731
theorem B968435 : Blo 283827 968435 := bstep (se 1 (by rfl) ⟨726326, by rfl⟩ : syracuseStep 968435 = 1452653) B1452653
theorem B1623847 : Blo 283827 1623847 := bstep (se 1 (by rfl) ⟨1217885, by rfl⟩ : syracuseStep 1623847 = 2435771) B2435771
theorem B640871 : Blo 283827 640871 := bstep (se 1 (by rfl) ⟨480653, by rfl⟩ : syracuseStep 640871 = 961307) B961307
theorem B4147271 : Blo 283827 4147271 := bstep (se 1 (by rfl) ⟨3110453, by rfl⟩ : syracuseStep 4147271 = 6220907) B6220907
theorem B543439 : Blo 283827 543439 := bstep (se 1 (by rfl) ⟨407579, by rfl⟩ : syracuseStep 543439 = 815159) B815159
theorem B2182139 : Blo 283827 2182139 := bstep (se 1 (by rfl) ⟨1636604, by rfl⟩ : syracuseStep 2182139 = 3273209) B3273209
theorem B642527 : Blo 283827 642527 := bstep (se 1 (by rfl) ⟨481895, by rfl⟩ : syracuseStep 642527 = 963791) B963791
theorem B1625831 : Blo 283827 1625831 := bstep (se 1 (by rfl) ⟨1219373, by rfl⟩ : syracuseStep 1625831 = 2438747) B2438747
theorem B479209 : Blo 283827 479209 := bstep (se 2 (by rfl) ⟨179703, by rfl⟩ : syracuseStep 479209 = 359407) B359407
theorem B479263 : Blo 283827 479263 := bstep (se 1 (by rfl) ⟨359447, by rfl⟩ : syracuseStep 479263 = 718895) B718895
theorem B644327 : Blo 283827 644327 := bstep (se 1 (by rfl) ⟨483245, by rfl⟩ : syracuseStep 644327 = 966491) B966491
theorem B284207 : Blo 283827 284207 := bstep (se 1 (by rfl) ⟨213155, by rfl⟩ : syracuseStep 284207 = 426311) B426311
theorem B776135 : Blo 283827 776135 := bstep (se 1 (by rfl) ⟨582101, by rfl⟩ : syracuseStep 776135 = 1164203) B1164203
theorem B284775 : Blo 283827 284775 := bstep (se 1 (by rfl) ⟨213581, by rfl⟩ : syracuseStep 284775 = 427163) B427163
theorem B514367 : Blo 283827 514367 := bstep (se 1 (by rfl) ⟨385775, by rfl⟩ : syracuseStep 514367 = 771551) B771551
theorem B3529207 : Blo 283827 3529207 := bstep (se 1 (by rfl) ⟨2646905, by rfl⟩ : syracuseStep 3529207 = 5293811) B5293811
theorem B1464923 : Blo 283827 1464923 := bstep (se 1 (by rfl) ⟨1098692, by rfl⟩ : syracuseStep 1464923 = 2197385) B2197385
theorem B285339 : Blo 283827 285339 := bstep (se 1 (by rfl) ⟨214004, by rfl⟩ : syracuseStep 285339 = 428009) B428009
theorem B1956511 : Blo 283827 1956511 := bstep (se 1 (by rfl) ⟨1467383, by rfl⟩ : syracuseStep 1956511 = 2934767) B2934767
theorem B1825577 : Blo 283827 1825577 := bstep (se 2 (by rfl) ⟨684591, by rfl⟩ : syracuseStep 1825577 = 1369183) B1369183
theorem B646127 : Blo 283827 646127 := bstep (se 1 (by rfl) ⟨484595, by rfl⟩ : syracuseStep 646127 = 969191) B969191
theorem B547931 : Blo 283827 547931 := bstep (se 1 (by rfl) ⟨410948, by rfl⟩ : syracuseStep 547931 = 821897) B821897
theorem B286239 : Blo 283827 286239 := bstep (se 1 (by rfl) ⟨214679, by rfl⟩ : syracuseStep 286239 = 429359) B429359
theorem B646703 : Blo 283827 646703 := bstep (se 1 (by rfl) ⟨485027, by rfl⟩ : syracuseStep 646703 = 970055) B970055
theorem B286363 : Blo 283827 286363 := bstep (se 1 (by rfl) ⟨214772, by rfl⟩ : syracuseStep 286363 = 429545) B429545
theorem B286399 : Blo 283827 286399 := bstep (se 1 (by rfl) ⟨214799, by rfl⟩ : syracuseStep 286399 = 429599) B429599
theorem B483151 : Blo 283827 483151 := bstep (se 1 (by rfl) ⟨362363, by rfl⟩ : syracuseStep 483151 = 724727) B724727
theorem B5857231 : Blo 283827 5857231 := bstep (se 1 (by rfl) ⟨4392923, by rfl⟩ : syracuseStep 5857231 = 8785847) B8785847
theorem B9855533 : Blo 283827 9855533 := bstep (se 3 (by rfl) ⟨1847912, by rfl⟩ : syracuseStep 9855533 = 3695825) B3695825
theorem B287279 : Blo 283827 287279 := bstep (se 1 (by rfl) ⟨215459, by rfl⟩ : syracuseStep 287279 = 430919) B430919
theorem B483995 : Blo 283827 483995 := bstep (se 1 (by rfl) ⟨362996, by rfl⟩ : syracuseStep 483995 = 725993) B725993
theorem B287551 : Blo 283827 287551 := bstep (se 1 (by rfl) ⟨215663, by rfl⟩ : syracuseStep 287551 = 431327) B431327
theorem B484265 : Blo 283827 484265 := bstep (se 2 (by rfl) ⟨181599, by rfl⟩ : syracuseStep 484265 = 363199) B363199
theorem B2057147 : Blo 283827 2057147 := bstep (se 1 (by rfl) ⟨1542860, by rfl⟩ : syracuseStep 2057147 = 3085721) B3085721
theorem B287711 : Blo 283827 287711 := bstep (se 1 (by rfl) ⟨215783, by rfl⟩ : syracuseStep 287711 = 431567) B431567
theorem B517769 : Blo 283827 517769 := bstep (se 2 (by rfl) ⟨194163, by rfl⟩ : syracuseStep 517769 = 388327) B388327
theorem B1730807 : Blo 283827 1730807 := bstep (se 1 (by rfl) ⟨1298105, by rfl⟩ : syracuseStep 1730807 = 2596211) B2596211
theorem B6187691 : Blo 283827 6187691 := bstep (se 1 (by rfl) ⟨4640768, by rfl⟩ : syracuseStep 6187691 = 9281537) B9281537
theorem B2157353 : Blo 283827 2157353 := bstep (se 2 (by rfl) ⟨809007, by rfl⟩ : syracuseStep 2157353 = 1618015) B1618015
theorem B322375 : Blo 283827 322375 := bstep (se 1 (by rfl) ⟨241781, by rfl⟩ : syracuseStep 322375 = 483563) B483563
theorem B3108377 : Blo 283827 3108377 := bstep (se 2 (by rfl) ⟨1165641, by rfl⟩ : syracuseStep 3108377 = 2331283) B2331283
theorem B6975163 : Blo 283827 6975163 := bstep (se 1 (by rfl) ⟨5231372, by rfl⟩ : syracuseStep 6975163 = 10462745) B10462745
theorem B814931 : Blo 283827 814931 := bstep (se 1 (by rfl) ⟨611198, by rfl⟩ : syracuseStep 814931 = 1222397) B1222397
theorem B1831187 : Blo 283827 1831187 := bstep (se 1 (by rfl) ⟨1373390, by rfl⟩ : syracuseStep 1831187 = 2746781) B2746781
theorem B815615 : Blo 283827 815615 := bstep (se 1 (by rfl) ⟨611711, by rfl⟩ : syracuseStep 815615 = 1223423) B1223423
theorem B2061065 : Blo 283827 2061065 := bstep (se 2 (by rfl) ⟨772899, by rfl⟩ : syracuseStep 2061065 = 1545799) B1545799
theorem B13563227 : Blo 283827 13563227 := bstep (se 1 (by rfl) ⟨10172420, by rfl⟩ : syracuseStep 13563227 = 20344841) B20344841
theorem B4126049 : Blo 283827 4126049 := bstep (se 2 (by rfl) ⟨1547268, by rfl⟩ : syracuseStep 4126049 = 3094537) B3094537
theorem B7468469 : Blo 283827 7468469 := bstep (se 5 (by rfl) ⟨350084, by rfl⟩ : syracuseStep 7468469 = 700169) B700169
theorem B816799 : Blo 283827 816799 := bstep (se 1 (by rfl) ⟨612599, by rfl⟩ : syracuseStep 816799 = 1225199) B1225199
theorem B718591 : Blo 283827 718591 := bstep (se 1 (by rfl) ⟨538943, by rfl⟩ : syracuseStep 718591 = 1077887) B1077887
theorem B718715 : Blo 283827 718715 := bstep (se 1 (by rfl) ⟨539036, by rfl⟩ : syracuseStep 718715 = 1078073) B1078073
theorem B1374353 : Blo 283827 1374353 := bstep (se 2 (by rfl) ⟨515382, by rfl⟩ : syracuseStep 1374353 = 1030765) B1030765
theorem B1079527 : Blo 283827 1079527 := bstep (se 1 (by rfl) ⟨809645, by rfl⟩ : syracuseStep 1079527 = 1619291) B1619291
theorem B1637243 : Blo 283827 1637243 := bstep (se 1 (by rfl) ⟨1227932, by rfl⟩ : syracuseStep 1637243 = 2455865) B2455865
theorem B16415621 : Blo 283827 16415621 := bstep (se 4 (by rfl) ⟨1538964, by rfl⟩ : syracuseStep 16415621 = 3077929) B3077929
theorem B719867 : Blo 283827 719867 := bstep (se 1 (by rfl) ⟨539900, by rfl⟩ : syracuseStep 719867 = 1079801) B1079801
theorem B1572065 : Blo 283827 1572065 := bstep (se 2 (by rfl) ⟨589524, by rfl⟩ : syracuseStep 1572065 = 1179049) B1179049
theorem B426551 : Blo 283827 426551 := bstep (se 1 (by rfl) ⟨319913, by rfl⟩ : syracuseStep 426551 = 639827) B639827
theorem B2163671 : Blo 283827 2163671 := bstep (se 1 (by rfl) ⟨1622753, by rfl⟩ : syracuseStep 2163671 = 3245507) B3245507
theorem B4850765 : Blo 283827 4850765 := bstep (se 3 (by rfl) ⟨909518, by rfl⟩ : syracuseStep 4850765 = 1819037) B1819037
theorem B427247 : Blo 283827 427247 := bstep (se 1 (by rfl) ⟨320435, by rfl⟩ : syracuseStep 427247 = 640871) B640871
theorem B26281421 : Blo 283827 26281421 := bstep (se 3 (by rfl) ⟨4927766, by rfl⟩ : syracuseStep 26281421 = 9855533) B9855533
theorem B4655303 : Blo 283827 4655303 := bstep (se 1 (by rfl) ⟨3491477, by rfl⟩ : syracuseStep 4655303 = 6982955) B6982955
theorem B428351 : Blo 283827 428351 := bstep (se 1 (by rfl) ⟨321263, by rfl⟩ : syracuseStep 428351 = 642527) B642527
theorem B2165129 : Blo 283827 2165129 := bstep (se 2 (by rfl) ⟨811923, by rfl⟩ : syracuseStep 2165129 = 1623847) B1623847
theorem B1083887 : Blo 283827 1083887 := bstep (se 1 (by rfl) ⟨812915, by rfl⟩ : syracuseStep 1083887 = 1625831) B1625831
theorem B429551 : Blo 283827 429551 := bstep (se 1 (by rfl) ⟨322163, by rfl⟩ : syracuseStep 429551 = 644327) B644327
theorem B724585 : Blo 283827 724585 := bstep (se 2 (by rfl) ⟨271719, by rfl⟩ : syracuseStep 724585 = 543439) B543439
theorem B2428663 : Blo 283827 2428663 := bstep (se 1 (by rfl) ⟨1821497, by rfl⟩ : syracuseStep 2428663 = 3642995) B3642995
theorem B429833 : Blo 283827 429833 := bstep (se 2 (by rfl) ⟨161187, by rfl⟩ : syracuseStep 429833 = 322375) B322375
theorem B1707965 : Blo 283827 1707965 := bstep (se 3 (by rfl) ⟨320243, by rfl⟩ : syracuseStep 1707965 = 640487) B640487
theorem B1217051 : Blo 283827 1217051 := bstep (se 1 (by rfl) ⟨912788, by rfl⟩ : syracuseStep 1217051 = 1825577) B1825577
theorem B430751 : Blo 283827 430751 := bstep (se 1 (by rfl) ⟨323063, by rfl⟩ : syracuseStep 430751 = 646127) B646127
theorem B1970983 : Blo 283827 1970983 := bstep (se 1 (by rfl) ⟨1478237, by rfl⟩ : syracuseStep 1970983 = 2956475) B2956475
theorem B431135 : Blo 283827 431135 := bstep (se 1 (by rfl) ⟨323351, by rfl⟩ : syracuseStep 431135 = 646703) B646703
theorem B726671 : Blo 283827 726671 := bstep (se 1 (by rfl) ⟨545003, by rfl⟩ : syracuseStep 726671 = 1090007) B1090007
theorem B3086063 : Blo 283827 3086063 := bstep (se 1 (by rfl) ⟨2314547, by rfl⟩ : syracuseStep 3086063 = 4629095) B4629095
theorem B727451 : Blo 283827 727451 := bstep (se 1 (by rfl) ⟨545588, by rfl⟩ : syracuseStep 727451 = 1091177) B1091177
theorem B1415809 : Blo 283827 1415809 := bstep (se 2 (by rfl) ⟨530928, by rfl⟩ : syracuseStep 1415809 = 1061857) B1061857
theorem B1153871 : Blo 283827 1153871 := bstep (se 1 (by rfl) ⟨865403, by rfl⟩ : syracuseStep 1153871 = 1730807) B1730807
theorem B3906461 : Blo 283827 3906461 := bstep (se 3 (by rfl) ⟨732461, by rfl⟩ : syracuseStep 3906461 = 1464923) B1464923
theorem B728423 : Blo 283827 728423 := bstep (se 1 (by rfl) ⟨546317, by rfl⟩ : syracuseStep 728423 = 1092635) B1092635
theorem B1089065 : Blo 283827 1089065 := bstep (se 2 (by rfl) ⟨408399, by rfl⟩ : syracuseStep 1089065 = 816799) B816799
theorem B958121 : Blo 283827 958121 := bstep (se 2 (by rfl) ⟨359295, by rfl⟩ : syracuseStep 958121 = 718591) B718591
theorem B2072251 : Blo 283827 2072251 := bstep (se 1 (by rfl) ⟨1554188, by rfl⟩ : syracuseStep 2072251 = 3108377) B3108377
theorem B1220791 : Blo 283827 1220791 := bstep (se 1 (by rfl) ⟨915593, by rfl⟩ : syracuseStep 1220791 = 1831187) B1831187
theorem B2630333 : Blo 283827 2630333 := bstep (se 3 (by rfl) ⟨493187, by rfl⟩ : syracuseStep 2630333 = 986375) B986375
theorem B1450871 : Blo 283827 1450871 := bstep (se 1 (by rfl) ⟨1088153, by rfl⟩ : syracuseStep 1450871 = 2176307) B2176307
theorem B2728829 : Blo 283827 2728829 := bstep (se 3 (by rfl) ⟨511655, by rfl⟩ : syracuseStep 2728829 = 1023311) B1023311
theorem B37200869 : Blo 283827 37200869 := bstep (se 4 (by rfl) ⟨3487581, by rfl⟩ : syracuseStep 37200869 = 6975163) B6975163
theorem B1451195 : Blo 283827 1451195 := bstep (se 1 (by rfl) ⟨1088396, by rfl⟩ : syracuseStep 1451195 = 2176793) B2176793
theorem B1091495 : Blo 283827 1091495 := bstep (se 1 (by rfl) ⟨818621, by rfl⟩ : syracuseStep 1091495 = 1637243) B1637243
theorem B6269345 : Blo 283827 6269345 := bstep (se 2 (by rfl) ⟨2351004, by rfl⟩ : syracuseStep 6269345 = 4702009) B4702009
theorem B7809641 : Blo 283827 7809641 := bstep (se 2 (by rfl) ⟨2928615, by rfl⟩ : syracuseStep 7809641 = 5857231) B5857231
theorem B827370449 : Blo 283827 827370449 := bstep (se 2 (by rfl) ⟨310263918, by rfl⟩ : syracuseStep 827370449 = 620527837) B620527837
theorem B863723 : Blo 283827 863723 := bstep (se 1 (by rfl) ⟨647792, by rfl⟩ : syracuseStep 863723 = 1295585) B1295585
theorem B2764847 : Blo 283827 2764847 := bstep (se 1 (by rfl) ⟨2073635, by rfl⟩ : syracuseStep 2764847 = 4147271) B4147271
theorem B962657 : Blo 283827 962657 := bstep (se 2 (by rfl) ⟨360996, by rfl⟩ : syracuseStep 962657 = 721993) B721993
theorem B1454759 : Blo 283827 1454759 := bstep (se 1 (by rfl) ⟨1091069, by rfl⟩ : syracuseStep 1454759 = 2182139) B2182139
theorem B342911 : Blo 283827 342911 := bstep (se 1 (by rfl) ⟨257183, by rfl⟩ : syracuseStep 342911 = 514367) B514367
theorem B769787 : Blo 283827 769787 := bstep (se 1 (by rfl) ⟨577340, by rfl⟩ : syracuseStep 769787 = 1154681) B1154681
theorem B638945 : Blo 283827 638945 := bstep (se 2 (by rfl) ⟨239604, by rfl⟩ : syracuseStep 638945 = 479209) B479209
theorem B639017 : Blo 283827 639017 := bstep (se 2 (by rfl) ⟨239631, by rfl⟩ : syracuseStep 639017 = 479263) B479263
theorem B639287 : Blo 283827 639287 := bstep (se 1 (by rfl) ⟨479465, by rfl⟩ : syracuseStep 639287 = 958931) B958931
theorem B345179 : Blo 283827 345179 := bstep (se 1 (by rfl) ⟨258884, by rfl⟩ : syracuseStep 345179 = 517769) B517769
theorem B640367 : Blo 283827 640367 := bstep (se 1 (by rfl) ⟨480275, by rfl⟩ : syracuseStep 640367 = 960551) B960551
theorem B641591 : Blo 283827 641591 := bstep (se 1 (by rfl) ⟨481193, by rfl⟩ : syracuseStep 641591 = 962387) B962387
theorem B543287 : Blo 283827 543287 := bstep (se 1 (by rfl) ⟨407465, by rfl⟩ : syracuseStep 543287 = 814931) B814931
theorem B641663 : Blo 283827 641663 := bstep (se 1 (by rfl) ⟨481247, by rfl⟩ : syracuseStep 641663 = 962495) B962495
theorem B969407 : Blo 283827 969407 := bstep (se 1 (by rfl) ⟨727055, by rfl⟩ : syracuseStep 969407 = 1454111) B1454111
theorem B1461149 : Blo 283827 1461149 := bstep (se 3 (by rfl) ⟨273965, by rfl⟩ : syracuseStep 1461149 = 547931) B547931
theorem B543743 : Blo 283827 543743 := bstep (se 1 (by rfl) ⟨407807, by rfl⟩ : syracuseStep 543743 = 815615) B815615
theorem B4705609 : Blo 283827 4705609 := bstep (se 2 (by rfl) ⟨1764603, by rfl⟩ : syracuseStep 4705609 = 3529207) B3529207
theorem B2608681 : Blo 283827 2608681 := bstep (se 2 (by rfl) ⟨978255, by rfl⟩ : syracuseStep 2608681 = 1956511) B1956511
theorem B642671 : Blo 283827 642671 := bstep (se 1 (by rfl) ⟨482003, by rfl⟩ : syracuseStep 642671 = 964007) B964007
theorem B18534005 : Blo 283827 18534005 := bstep (se 5 (by rfl) ⟨868781, by rfl⟩ : syracuseStep 18534005 = 1737563) B1737563
theorem B479143 : Blo 283827 479143 := bstep (se 1 (by rfl) ⟨359357, by rfl⟩ : syracuseStep 479143 = 718715) B718715
theorem B479911 : Blo 283827 479911 := bstep (se 1 (by rfl) ⟨359933, by rfl⟩ : syracuseStep 479911 = 719867) B719867
theorem B40555363 : Blo 283827 40555363 := bstep (se 1 (by rfl) ⟨30416522, by rfl⟩ : syracuseStep 40555363 = 60833045) B60833045
theorem B644201 : Blo 283827 644201 := bstep (se 2 (by rfl) ⟨241575, by rfl⟩ : syracuseStep 644201 = 483151) B483151
theorem B644543 : Blo 283827 644543 := bstep (se 1 (by rfl) ⟨483407, by rfl⟩ : syracuseStep 644543 = 966815) B966815
theorem B284111 : Blo 283827 284111 := bstep (se 1 (by rfl) ⟨213083, by rfl⟩ : syracuseStep 284111 = 426167) B426167
theorem B284667 : Blo 283827 284667 := bstep (se 1 (by rfl) ⟨213500, by rfl⟩ : syracuseStep 284667 = 427001) B427001
theorem B284703 : Blo 283827 284703 := bstep (se 1 (by rfl) ⟨213527, by rfl⟩ : syracuseStep 284703 = 427055) B427055
theorem B612463 : Blo 283827 612463 := bstep (se 1 (by rfl) ⟨459347, by rfl⟩ : syracuseStep 612463 = 918695) B918695
theorem B284999 : Blo 283827 284999 := bstep (se 1 (by rfl) ⟨213749, by rfl⟩ : syracuseStep 284999 = 427499) B427499
theorem B645623 : Blo 283827 645623 := bstep (se 1 (by rfl) ⟨484217, by rfl⟩ : syracuseStep 645623 = 968435) B968435
theorem B285295 : Blo 283827 285295 := bstep (se 1 (by rfl) ⟨213971, by rfl⟩ : syracuseStep 285295 = 427943) B427943
theorem B285415 : Blo 283827 285415 := bstep (se 1 (by rfl) ⟨214061, by rfl⟩ : syracuseStep 285415 = 428123) B428123
theorem B285439 : Blo 283827 285439 := bstep (se 1 (by rfl) ⟨214079, by rfl⟩ : syracuseStep 285439 = 428159) B428159
theorem B285663 : Blo 283827 285663 := bstep (se 1 (by rfl) ⟨214247, by rfl⟩ : syracuseStep 285663 = 428495) B428495
theorem B285863 : Blo 283827 285863 := bstep (se 1 (by rfl) ⟨214397, by rfl⟩ : syracuseStep 285863 = 428795) B428795
theorem B5496173 : Blo 283827 5496173 := bstep (se 3 (by rfl) ⟨1030532, by rfl⟩ : syracuseStep 5496173 = 2061065) B2061065
theorem B286335 : Blo 283827 286335 := bstep (se 1 (by rfl) ⟨214751, by rfl⟩ : syracuseStep 286335 = 429503) B429503
theorem B286491 : Blo 283827 286491 := bstep (se 1 (by rfl) ⟨214868, by rfl⟩ : syracuseStep 286491 = 429737) B429737
theorem B286751 : Blo 283827 286751 := bstep (se 1 (by rfl) ⟨215063, by rfl⟩ : syracuseStep 286751 = 430127) B430127
theorem B286887 : Blo 283827 286887 := bstep (se 1 (by rfl) ⟨215165, by rfl⟩ : syracuseStep 286887 = 430331) B430331
theorem B287047 : Blo 283827 287047 := bstep (se 1 (by rfl) ⟨215285, by rfl⟩ : syracuseStep 287047 = 430571) B430571
theorem B39641561 : Blo 283827 39641561 := bstep (se 2 (by rfl) ⟨14865585, by rfl⟩ : syracuseStep 39641561 = 29731171) B29731171
theorem B287463 : Blo 283827 287463 := bstep (se 1 (by rfl) ⟨215597, by rfl⟩ : syracuseStep 287463 = 431195) B431195
theorem B287579 : Blo 283827 287579 := bstep (se 1 (by rfl) ⟨215684, by rfl⟩ : syracuseStep 287579 = 431369) B431369
theorem B287775 : Blo 283827 287775 := bstep (se 1 (by rfl) ⟨215831, by rfl⟩ : syracuseStep 287775 = 431663) B431663
theorem B517423 : Blo 283827 517423 := bstep (se 1 (by rfl) ⟨388067, by rfl⟩ : syracuseStep 517423 = 776135) B776135
theorem B322663 : Blo 283827 322663 := bstep (se 1 (by rfl) ⟨241997, by rfl⟩ : syracuseStep 322663 = 483995) B483995
theorem B322843 : Blo 283827 322843 := bstep (se 1 (by rfl) ⟨242132, by rfl⟩ : syracuseStep 322843 = 484265) B484265
theorem B1371431 : Blo 283827 1371431 := bstep (se 1 (by rfl) ⟨1028573, by rfl⟩ : syracuseStep 1371431 = 2057147) B2057147
theorem B3239675 : Blo 283827 3239675 := bstep (se 1 (by rfl) ⟨2429756, by rfl⟩ : syracuseStep 3239675 = 4859513) B4859513
theorem B291119 : Blo 283827 291119 := bstep (se 1 (by rfl) ⟨218339, by rfl⟩ : syracuseStep 291119 = 436679) B436679
theorem B4125127 : Blo 283827 4125127 := bstep (se 1 (by rfl) ⟨3093845, by rfl⟩ : syracuseStep 4125127 = 6187691) B6187691
theorem B1438235 : Blo 283827 1438235 := bstep (se 1 (by rfl) ⟨1078676, by rfl⟩ : syracuseStep 1438235 = 2157353) B2157353
theorem B815741 : Blo 283827 815741 := bstep (se 3 (by rfl) ⟨152951, by rfl⟩ : syracuseStep 815741 = 305903) B305903
theorem B2061931 : Blo 283827 2061931 := bstep (se 1 (by rfl) ⟨1546448, by rfl⟩ : syracuseStep 2061931 = 3092897) B3092897
theorem B1439369 : Blo 283827 1439369 := bstep (se 2 (by rfl) ⟨539763, by rfl⟩ : syracuseStep 1439369 = 1079527) B1079527
theorem B9042151 : Blo 283827 9042151 := bstep (se 1 (by rfl) ⟨6781613, by rfl⟩ : syracuseStep 9042151 = 13563227) B13563227
theorem B2750699 : Blo 283827 2750699 := bstep (se 1 (by rfl) ⟨2063024, by rfl⟩ : syracuseStep 2750699 = 4126049) B4126049
theorem B4978979 : Blo 283827 4978979 := bstep (se 1 (by rfl) ⟨3734234, by rfl⟩ : syracuseStep 4978979 = 7468469) B7468469
theorem B916235 : Blo 283827 916235 := bstep (se 1 (by rfl) ⟨687176, by rfl⟩ : syracuseStep 916235 = 1374353) B1374353
theorem B1080287 : Blo 283827 1080287 := bstep (se 1 (by rfl) ⟨810215, by rfl⟩ : syracuseStep 1080287 = 1620431) B1620431
theorem B10943747 : Blo 283827 10943747 := bstep (se 1 (by rfl) ⟨8207810, by rfl⟩ : syracuseStep 10943747 = 16415621) B16415621
theorem B1048043 : Blo 283827 1048043 := bstep (se 1 (by rfl) ⟨786032, by rfl⟩ : syracuseStep 1048043 = 1572065) B1572065
theorem B9895445 : Blo 283827 9895445 := bstep (se 6 (by rfl) ⟨231924, by rfl⟩ : syracuseStep 9895445 = 463849) B463849
theorem B720809 : Blo 283827 720809 := bstep (se 2 (by rfl) ⟨270303, by rfl⟩ : syracuseStep 720809 = 540607) B540607
theorem B426011 : Blo 283827 426011 := bstep (se 1 (by rfl) ⟨319508, by rfl⟩ : syracuseStep 426011 = 639017) B639017
theorem B426191 : Blo 283827 426191 := bstep (se 1 (by rfl) ⟨319643, by rfl⟩ : syracuseStep 426191 = 639287) B639287
theorem B1442447 : Blo 283827 1442447 := bstep (se 1 (by rfl) ⟨1081835, by rfl⟩ : syracuseStep 1442447 = 2163671) B2163671
theorem B426911 : Blo 283827 426911 := bstep (se 1 (by rfl) ⟨320183, by rfl⟩ : syracuseStep 426911 = 640367) B640367
theorem B1443419 : Blo 283827 1443419 := bstep (se 1 (by rfl) ⟨1082564, by rfl⟩ : syracuseStep 1443419 = 2165129) B2165129
theorem B722591 : Blo 283827 722591 := bstep (se 1 (by rfl) ⟨541943, by rfl⟩ : syracuseStep 722591 = 1083887) B1083887
theorem B427727 : Blo 283827 427727 := bstep (se 1 (by rfl) ⟨320795, by rfl⟩ : syracuseStep 427727 = 641591) B641591
theorem B689897 : Blo 283827 689897 := bstep (se 2 (by rfl) ⟨258711, by rfl⟩ : syracuseStep 689897 = 517423) B517423
theorem B427775 : Blo 283827 427775 := bstep (se 1 (by rfl) ⟨320831, by rfl⟩ : syracuseStep 427775 = 641663) B641663
theorem B362495 : Blo 283827 362495 := bstep (se 1 (by rfl) ⟨271871, by rfl⟩ : syracuseStep 362495 = 543743) B543743
theorem B428447 : Blo 283827 428447 := bstep (se 1 (by rfl) ⟨321335, by rfl⟩ : syracuseStep 428447 = 642671) B642671
theorem B12356003 : Blo 283827 12356003 := bstep (se 1 (by rfl) ⟨9267002, by rfl⟩ : syracuseStep 12356003 = 18534005) B18534005
theorem B920477 : Blo 283827 920477 := bstep (se 3 (by rfl) ⟨172589, by rfl⟩ : syracuseStep 920477 = 345179) B345179
theorem B429467 : Blo 283827 429467 := bstep (se 1 (by rfl) ⟨322100, by rfl⟩ : syracuseStep 429467 = 644201) B644201
theorem B429695 : Blo 283827 429695 := bstep (se 1 (by rfl) ⟨322271, by rfl⟩ : syracuseStep 429695 = 644543) B644543
theorem B430217 : Blo 283827 430217 := bstep (se 2 (by rfl) ⟨161331, by rfl⟩ : syracuseStep 430217 = 322663) B322663
theorem B430415 : Blo 283827 430415 := bstep (se 1 (by rfl) ⟨322811, by rfl⟩ : syracuseStep 430415 = 645623) B645623
theorem B430457 : Blo 283827 430457 := bstep (se 2 (by rfl) ⟨161421, by rfl⟩ : syracuseStep 430457 = 322843) B322843
theorem B3478241 : Blo 283827 3478241 := bstep (se 2 (by rfl) ⟨1304340, by rfl⟩ : syracuseStep 3478241 = 2608681) B2608681
theorem B726043 : Blo 283827 726043 := bstep (se 1 (by rfl) ⟨544532, by rfl⟩ : syracuseStep 726043 = 1089065) B1089065
theorem B2627977 : Blo 283827 2627977 := bstep (se 2 (by rfl) ⟨985491, by rfl⟩ : syracuseStep 2627977 = 1970983) B1970983
theorem B54073817 : Blo 283827 54073817 := bstep (se 2 (by rfl) ⟨20277681, by rfl⟩ : syracuseStep 54073817 = 40555363) B40555363
theorem B727663 : Blo 283827 727663 := bstep (se 1 (by rfl) ⟨545747, by rfl⟩ : syracuseStep 727663 = 1091495) B1091495
theorem B1448765 : Blo 283827 1448765 := bstep (se 3 (by rfl) ⟨271643, by rfl⟩ : syracuseStep 1448765 = 543287) B543287
theorem B1843231 : Blo 283827 1843231 := bstep (se 1 (by rfl) ⟨1382423, by rfl⟩ : syracuseStep 1843231 = 2764847) B2764847
theorem B958823 : Blo 283827 958823 := bstep (se 1 (by rfl) ⟨719117, by rfl⟩ : syracuseStep 958823 = 1438235) B1438235
theorem B959579 : Blo 283827 959579 := bstep (se 1 (by rfl) ⟨719684, by rfl⟩ : syracuseStep 959579 = 1439369) B1439369
theorem B2303261 : Blo 283827 2303261 := bstep (se 3 (by rfl) ⟨431861, by rfl⟩ : syracuseStep 2303261 = 863723) B863723
theorem B2794781 : Blo 283827 2794781 := bstep (se 3 (by rfl) ⟨524021, by rfl⟩ : syracuseStep 2794781 = 1048043) B1048043
theorem B3319319 : Blo 283827 3319319 := bstep (se 1 (by rfl) ⟨2489489, by rfl⟩ : syracuseStep 3319319 = 4978979) B4978979
theorem B2763001 : Blo 283827 2763001 := bstep (se 2 (by rfl) ⟨1036125, by rfl⟩ : syracuseStep 2763001 = 2072251) B2072251
theorem B6596963 : Blo 283827 6596963 := bstep (se 1 (by rfl) ⟨4947722, by rfl⟩ : syracuseStep 6596963 = 9895445) B9895445
theorem B6274145 : Blo 283827 6274145 := bstep (se 2 (by rfl) ⟨2352804, by rfl⟩ : syracuseStep 6274145 = 4705609) B4705609
theorem B769247 : Blo 283827 769247 := bstep (se 1 (by rfl) ⟨576935, by rfl⟩ : syracuseStep 769247 = 1153871) B1153871
theorem B2604307 : Blo 283827 2604307 := bstep (se 1 (by rfl) ⟨1953230, by rfl⟩ : syracuseStep 2604307 = 3906461) B3906461
theorem B966113 : Blo 283827 966113 := bstep (se 2 (by rfl) ⟨362292, by rfl⟩ : syracuseStep 966113 = 724585) B724585
theorem B638747 : Blo 283827 638747 := bstep (se 1 (by rfl) ⟨479060, by rfl⟩ : syracuseStep 638747 = 958121) B958121
theorem B638857 : Blo 283827 638857 := bstep (se 2 (by rfl) ⟨239571, by rfl⟩ : syracuseStep 638857 = 479143) B479143
theorem B26427707 : Blo 283827 26427707 := bstep (se 1 (by rfl) ⟨19820780, by rfl⟩ : syracuseStep 26427707 = 39641561) B39641561
theorem B1753555 : Blo 283827 1753555 := bstep (se 1 (by rfl) ⟨1315166, by rfl⟩ : syracuseStep 1753555 = 2630333) B2630333
theorem B967247 : Blo 283827 967247 := bstep (se 1 (by rfl) ⟨725435, by rfl⟩ : syracuseStep 967247 = 1450871) B1450871
theorem B1819219 : Blo 283827 1819219 := bstep (se 1 (by rfl) ⟨1364414, by rfl⟩ : syracuseStep 1819219 = 2728829) B2728829
theorem B967463 : Blo 283827 967463 := bstep (se 1 (by rfl) ⟨725597, by rfl⟩ : syracuseStep 967463 = 1451195) B1451195
theorem B639881 : Blo 283827 639881 := bstep (se 2 (by rfl) ⟨239955, by rfl⟩ : syracuseStep 639881 = 479911) B479911
theorem B4179563 : Blo 283827 4179563 := bstep (se 1 (by rfl) ⟨3134672, by rfl⟩ : syracuseStep 4179563 = 6269345) B6269345
theorem B641771 : Blo 283827 641771 := bstep (se 1 (by rfl) ⟨481328, by rfl⟩ : syracuseStep 641771 = 962657) B962657
theorem B543827 : Blo 283827 543827 := bstep (se 1 (by rfl) ⟨407870, by rfl⟩ : syracuseStep 543827 = 815741) B815741
theorem B969839 : Blo 283827 969839 := bstep (se 1 (by rfl) ⟨727379, by rfl⟩ : syracuseStep 969839 = 1454759) B1454759
theorem B1887745 : Blo 283827 1887745 := bstep (se 2 (by rfl) ⟨707904, by rfl⟩ : syracuseStep 1887745 = 1415809) B1415809
theorem B610823 : Blo 283827 610823 := bstep (se 1 (by rfl) ⟨458117, by rfl⟩ : syracuseStep 610823 = 916235) B916235
theorem B7295831 : Blo 283827 7295831 := bstep (se 1 (by rfl) ⟨5471873, by rfl⟩ : syracuseStep 7295831 = 10943747) B10943747
theorem B513191 : Blo 283827 513191 := bstep (se 1 (by rfl) ⟨384893, by rfl⟩ : syracuseStep 513191 = 769787) B769787
theorem B480539 : Blo 283827 480539 := bstep (se 1 (by rfl) ⟨360404, by rfl⟩ : syracuseStep 480539 = 720809) B720809
theorem B1627721 : Blo 283827 1627721 := bstep (se 2 (by rfl) ⟨610395, by rfl⟩ : syracuseStep 1627721 = 1220791) B1220791
theorem B284367 : Blo 283827 284367 := bstep (se 1 (by rfl) ⟨213275, by rfl⟩ : syracuseStep 284367 = 426551) B426551
theorem B3233843 : Blo 283827 3233843 := bstep (se 1 (by rfl) ⟨2425382, by rfl⟩ : syracuseStep 3233843 = 4850765) B4850765
theorem B776317 : Blo 283827 776317 := bstep (se 3 (by rfl) ⟨145559, by rfl⟩ : syracuseStep 776317 = 291119) B291119
theorem B284831 : Blo 283827 284831 := bstep (se 1 (by rfl) ⟨213623, by rfl⟩ : syracuseStep 284831 = 427247) B427247
theorem B17520947 : Blo 283827 17520947 := bstep (se 1 (by rfl) ⟨13140710, by rfl⟩ : syracuseStep 17520947 = 26281421) B26281421
theorem B3103535 : Blo 283827 3103535 := bstep (se 1 (by rfl) ⟨2327651, by rfl⟩ : syracuseStep 3103535 = 4655303) B4655303
theorem B285567 : Blo 283827 285567 := bstep (se 1 (by rfl) ⟨214175, by rfl⟩ : syracuseStep 285567 = 428351) B428351
theorem B646271 : Blo 283827 646271 := bstep (se 1 (by rfl) ⟨484703, by rfl⟩ : syracuseStep 646271 = 969407) B969407
theorem B974099 : Blo 283827 974099 := bstep (se 1 (by rfl) ⟨730574, by rfl⟩ : syracuseStep 974099 = 1461149) B1461149
theorem B286367 : Blo 283827 286367 := bstep (se 1 (by rfl) ⟨214775, by rfl⟩ : syracuseStep 286367 = 429551) B429551
theorem B286555 : Blo 283827 286555 := bstep (se 1 (by rfl) ⟨214916, by rfl⟩ : syracuseStep 286555 = 429833) B429833
theorem B1138643 : Blo 283827 1138643 := bstep (se 1 (by rfl) ⟨853982, by rfl⟩ : syracuseStep 1138643 = 1707965) B1707965
theorem B811367 : Blo 283827 811367 := bstep (se 1 (by rfl) ⟨608525, by rfl⟩ : syracuseStep 811367 = 1217051) B1217051
theorem B287167 : Blo 283827 287167 := bstep (se 1 (by rfl) ⟨215375, by rfl⟩ : syracuseStep 287167 = 430751) B430751
theorem B287423 : Blo 283827 287423 := bstep (se 1 (by rfl) ⟨215567, by rfl⟩ : syracuseStep 287423 = 431135) B431135
theorem B484447 : Blo 283827 484447 := bstep (se 1 (by rfl) ⟨363335, by rfl⟩ : syracuseStep 484447 = 726671) B726671
theorem B2057375 : Blo 283827 2057375 := bstep (se 1 (by rfl) ⟨1543031, by rfl⟩ : syracuseStep 2057375 = 3086063) B3086063
theorem B484967 : Blo 283827 484967 := bstep (se 1 (by rfl) ⟨363725, by rfl⟩ : syracuseStep 484967 = 727451) B727451
theorem B485615 : Blo 283827 485615 := bstep (se 1 (by rfl) ⟨364211, by rfl⟩ : syracuseStep 485615 = 728423) B728423
theorem B3664115 : Blo 283827 3664115 := bstep (se 1 (by rfl) ⟨2748086, by rfl⟩ : syracuseStep 3664115 = 5496173) B5496173
theorem B3238217 : Blo 283827 3238217 := bstep (se 2 (by rfl) ⟨1214331, by rfl⟩ : syracuseStep 3238217 = 2428663) B2428663
theorem B5500169 : Blo 283827 5500169 := bstep (se 2 (by rfl) ⟨2062563, by rfl⟩ : syracuseStep 5500169 = 4125127) B4125127
theorem B7335197 : Blo 283827 7335197 := bstep (se 3 (by rfl) ⟨1375349, by rfl⟩ : syracuseStep 7335197 = 2750699) B2750699
theorem B24800579 : Blo 283827 24800579 := bstep (se 1 (by rfl) ⟨18600434, by rfl⟩ : syracuseStep 24800579 = 37200869) B37200869
theorem B5206427 : Blo 283827 5206427 := bstep (se 1 (by rfl) ⟨3904820, by rfl⟩ : syracuseStep 5206427 = 7809641) B7809641
theorem B551580299 : Blo 283827 551580299 := bstep (se 1 (by rfl) ⟨413685224, by rfl⟩ : syracuseStep 551580299 = 827370449) B827370449
theorem B2749241 : Blo 283827 2749241 := bstep (se 2 (by rfl) ⟨1030965, by rfl⟩ : syracuseStep 2749241 = 2061931) B2061931
theorem B914287 : Blo 283827 914287 := bstep (se 1 (by rfl) ⟨685715, by rfl⟩ : syracuseStep 914287 = 1371431) B1371431
theorem B914429 : Blo 283827 914429 := bstep (se 3 (by rfl) ⟨171455, by rfl⟩ : syracuseStep 914429 = 342911) B342911
theorem B2159783 : Blo 283827 2159783 := bstep (se 1 (by rfl) ⟨1619837, by rfl⟩ : syracuseStep 2159783 = 3239675) B3239675
theorem B816617 : Blo 283827 816617 := bstep (se 2 (by rfl) ⟨306231, by rfl⟩ : syracuseStep 816617 = 612463) B612463
theorem B12056201 : Blo 283827 12056201 := bstep (se 2 (by rfl) ⟨4521075, by rfl⟩ : syracuseStep 12056201 = 9042151) B9042151
theorem B720191 : Blo 283827 720191 := bstep (se 1 (by rfl) ⟨540143, by rfl⟩ : syracuseStep 720191 = 1080287) B1080287
theorem B425963 : Blo 283827 425963 := bstep (se 1 (by rfl) ⟨319472, by rfl⟩ : syracuseStep 425963 = 638945) B638945
theorem B2457641 : Blo 283827 2457641 := bstep (se 2 (by rfl) ⟨921615, by rfl⟩ : syracuseStep 2457641 = 1843231) B1843231
theorem B426587 : Blo 283827 426587 := bstep (se 1 (by rfl) ⟨319940, by rfl⟩ : syracuseStep 426587 = 639881) B639881
theorem B2425625 : Blo 283827 2425625 := bstep (se 2 (by rfl) ⟨909609, by rfl⟩ : syracuseStep 2425625 = 1819219) B1819219
theorem B2786375 : Blo 283827 2786375 := bstep (se 1 (by rfl) ⟨2089781, by rfl⟩ : syracuseStep 2786375 = 4179563) B4179563
theorem B459931 : Blo 283827 459931 := bstep (se 1 (by rfl) ⟨344948, by rfl⟩ : syracuseStep 459931 = 689897) B689897
theorem B427847 : Blo 283827 427847 := bstep (se 1 (by rfl) ⟨320885, by rfl⟩ : syracuseStep 427847 = 641771) B641771
theorem B9275309 : Blo 283827 9275309 := bstep (se 3 (by rfl) ⟨1739120, by rfl⟩ : syracuseStep 9275309 = 3478241) B3478241
theorem B362551 : Blo 283827 362551 := bstep (se 1 (by rfl) ⟨271913, by rfl⟩ : syracuseStep 362551 = 543827) B543827
theorem B1085147 : Blo 283827 1085147 := bstep (se 1 (by rfl) ⟨813860, by rfl⟩ : syracuseStep 1085147 = 1627721) B1627721
theorem B36049211 : Blo 283827 36049211 := bstep (se 1 (by rfl) ⟨27036908, by rfl⟩ : syracuseStep 36049211 = 54073817) B54073817
theorem B2069023 : Blo 283827 2069023 := bstep (se 1 (by rfl) ⟨1551767, by rfl⟩ : syracuseStep 2069023 = 3103535) B3103535
theorem B430847 : Blo 283827 430847 := bstep (se 1 (by rfl) ⟨323135, by rfl⟩ : syracuseStep 430847 = 646271) B646271
theorem B759095 : Blo 283827 759095 := bstep (se 1 (by rfl) ⟨569321, by rfl⟩ : syracuseStep 759095 = 1138643) B1138643
theorem B1219049 : Blo 283827 1219049 := bstep (se 2 (by rfl) ⟨457143, by rfl⟩ : syracuseStep 1219049 = 914287) B914287
theorem B4397975 : Blo 283827 4397975 := bstep (se 1 (by rfl) ⟨3298481, by rfl⟩ : syracuseStep 4397975 = 6596963) B6596963
theorem B4890131 : Blo 283827 4890131 := bstep (se 1 (by rfl) ⟨3667598, by rfl⟩ : syracuseStep 4890131 = 7335197) B7335197
theorem B8037467 : Blo 283827 8037467 := bstep (se 1 (by rfl) ⟨6028100, by rfl⟩ : syracuseStep 8037467 = 12056201) B12056201
theorem B961631 : Blo 283827 961631 := bstep (se 1 (by rfl) ⟨721223, by rfl⟩ : syracuseStep 961631 = 1442447) B1442447
theorem B2338073 : Blo 283827 2338073 := bstep (se 2 (by rfl) ⟨876777, by rfl⟩ : syracuseStep 2338073 = 1753555) B1753555
theorem B962279 : Blo 283827 962279 := bstep (se 1 (by rfl) ⟨721709, by rfl⟩ : syracuseStep 962279 = 1443419) B1443419
theorem B8237335 : Blo 283827 8237335 := bstep (se 1 (by rfl) ⟨6178001, by rfl⟩ : syracuseStep 8237335 = 12356003) B12356003
theorem B3684001 : Blo 283827 3684001 := bstep (se 2 (by rfl) ⟨1381500, by rfl⟩ : syracuseStep 3684001 = 2763001) B2763001
theorem B407215 : Blo 283827 407215 := bstep (se 1 (by rfl) ⟨305411, by rfl⟩ : syracuseStep 407215 = 610823) B610823
theorem B4863887 : Blo 283827 4863887 := bstep (se 1 (by rfl) ⟨3647915, by rfl⟩ : syracuseStep 4863887 = 7295831) B7295831
theorem B7452749 : Blo 283827 7452749 := bstep (se 3 (by rfl) ⟨1397390, by rfl⟩ : syracuseStep 7452749 = 2794781) B2794781
theorem B342127 : Blo 283827 342127 := bstep (se 1 (by rfl) ⟨256595, by rfl⟩ : syracuseStep 342127 = 513191) B513191
theorem B11680631 : Blo 283827 11680631 := bstep (se 1 (by rfl) ⟨8760473, by rfl⟩ : syracuseStep 11680631 = 17520947) B17520947
theorem B965843 : Blo 283827 965843 := bstep (se 1 (by rfl) ⟨724382, by rfl⟩ : syracuseStep 965843 = 1448765) B1448765
theorem B966653 : Blo 283827 966653 := bstep (se 3 (by rfl) ⟨181247, by rfl⟩ : syracuseStep 966653 = 362495) B362495
theorem B639215 : Blo 283827 639215 := bstep (se 1 (by rfl) ⟨479411, by rfl⟩ : syracuseStep 639215 = 958823) B958823
theorem B540911 : Blo 283827 540911 := bstep (se 1 (by rfl) ⟨405683, by rfl⟩ : syracuseStep 540911 = 811367) B811367
theorem B639719 : Blo 283827 639719 := bstep (se 1 (by rfl) ⟨479789, by rfl⟩ : syracuseStep 639719 = 959579) B959579
theorem B2212879 : Blo 283827 2212879 := bstep (se 1 (by rfl) ⟨1659659, by rfl⟩ : syracuseStep 2212879 = 3319319) B3319319
theorem B968057 : Blo 283827 968057 := bstep (se 2 (by rfl) ⟨363021, by rfl⟩ : syracuseStep 968057 = 726043) B726043
theorem B2442743 : Blo 283827 2442743 := bstep (se 1 (by rfl) ⟨1832057, by rfl⟩ : syracuseStep 2442743 = 3664115) B3664115
theorem B16533719 : Blo 283827 16533719 := bstep (se 1 (by rfl) ⟨12400289, by rfl⟩ : syracuseStep 16533719 = 24800579) B24800579
theorem B1035089 : Blo 283827 1035089 := bstep (se 2 (by rfl) ⟨388158, by rfl⟩ : syracuseStep 1035089 = 776317) B776317
theorem B609619 : Blo 283827 609619 := bstep (se 1 (by rfl) ⟨457214, by rfl⟩ : syracuseStep 609619 = 914429) B914429
theorem B970217 : Blo 283827 970217 := bstep (se 2 (by rfl) ⟨363831, by rfl⟩ : syracuseStep 970217 = 727663) B727663
theorem B544411 : Blo 283827 544411 := bstep (se 1 (by rfl) ⟨408308, by rfl⟩ : syracuseStep 544411 = 816617) B816617
theorem B4182763 : Blo 283827 4182763 := bstep (se 1 (by rfl) ⟨3137072, by rfl⟩ : syracuseStep 4182763 = 6274145) B6274145
theorem B512831 : Blo 283827 512831 := bstep (se 1 (by rfl) ⟨384623, by rfl⟩ : syracuseStep 512831 = 769247) B769247
theorem B480127 : Blo 283827 480127 := bstep (se 1 (by rfl) ⟨360095, by rfl⟩ : syracuseStep 480127 = 720191) B720191
theorem B644075 : Blo 283827 644075 := bstep (se 1 (by rfl) ⟨483056, by rfl⟩ : syracuseStep 644075 = 966113) B966113
theorem B283975 : Blo 283827 283975 := bstep (se 1 (by rfl) ⟨212981, by rfl⟩ : syracuseStep 283975 = 425963) B425963
theorem B284007 : Blo 283827 284007 := bstep (se 1 (by rfl) ⟨213005, by rfl⟩ : syracuseStep 284007 = 426011) B426011
theorem B284127 : Blo 283827 284127 := bstep (se 1 (by rfl) ⟨213095, by rfl⟩ : syracuseStep 284127 = 426191) B426191
theorem B17618471 : Blo 283827 17618471 := bstep (se 1 (by rfl) ⟨13213853, by rfl⟩ : syracuseStep 17618471 = 26427707) B26427707
theorem B644831 : Blo 283827 644831 := bstep (se 1 (by rfl) ⟨483623, by rfl⟩ : syracuseStep 644831 = 967247) B967247
theorem B644975 : Blo 283827 644975 := bstep (se 1 (by rfl) ⟨483731, by rfl⟩ : syracuseStep 644975 = 967463) B967463
theorem B284607 : Blo 283827 284607 := bstep (se 1 (by rfl) ⟨213455, by rfl⟩ : syracuseStep 284607 = 426911) B426911
theorem B481727 : Blo 283827 481727 := bstep (se 1 (by rfl) ⟨361295, by rfl⟩ : syracuseStep 481727 = 722591) B722591
theorem B285151 : Blo 283827 285151 := bstep (se 1 (by rfl) ⟨213863, by rfl⟩ : syracuseStep 285151 = 427727) B427727
theorem B285183 : Blo 283827 285183 := bstep (se 1 (by rfl) ⟨213887, by rfl⟩ : syracuseStep 285183 = 427775) B427775
theorem B645929 : Blo 283827 645929 := bstep (se 2 (by rfl) ⟨242223, by rfl⟩ : syracuseStep 645929 = 484447) B484447
theorem B285631 : Blo 283827 285631 := bstep (se 1 (by rfl) ⟨214223, by rfl⟩ : syracuseStep 285631 = 428447) B428447
theorem B613651 : Blo 283827 613651 := bstep (se 1 (by rfl) ⟨460238, by rfl⟩ : syracuseStep 613651 = 920477) B920477
theorem B646559 : Blo 283827 646559 := bstep (se 1 (by rfl) ⟨484919, by rfl⟩ : syracuseStep 646559 = 969839) B969839
theorem B286311 : Blo 283827 286311 := bstep (se 1 (by rfl) ⟨214733, by rfl⟩ : syracuseStep 286311 = 429467) B429467
theorem B286463 : Blo 283827 286463 := bstep (se 1 (by rfl) ⟨214847, by rfl⟩ : syracuseStep 286463 = 429695) B429695
theorem B286811 : Blo 283827 286811 := bstep (se 1 (by rfl) ⟨215108, by rfl⟩ : syracuseStep 286811 = 430217) B430217
theorem B286943 : Blo 283827 286943 := bstep (se 1 (by rfl) ⟨215207, by rfl⟩ : syracuseStep 286943 = 430415) B430415
theorem B286971 : Blo 283827 286971 := bstep (se 1 (by rfl) ⟨215228, by rfl⟩ : syracuseStep 286971 = 430457) B430457
theorem B320359 : Blo 283827 320359 := bstep (se 1 (by rfl) ⟨240269, by rfl⟩ : syracuseStep 320359 = 480539) B480539
theorem B2155895 : Blo 283827 2155895 := bstep (se 1 (by rfl) ⟨1616921, by rfl⟩ : syracuseStep 2155895 = 3233843) B3233843
theorem B2516993 : Blo 283827 2516993 := bstep (se 2 (by rfl) ⟨943872, by rfl⟩ : syracuseStep 2516993 = 1887745) B1887745
theorem B649399 : Blo 283827 649399 := bstep (se 1 (by rfl) ⟨487049, by rfl⟩ : syracuseStep 649399 = 974099) B974099
theorem B1371583 : Blo 283827 1371583 := bstep (se 1 (by rfl) ⟨1028687, by rfl⟩ : syracuseStep 1371583 = 2057375) B2057375
theorem B1535507 : Blo 283827 1535507 := bstep (se 1 (by rfl) ⟨1151630, by rfl⟩ : syracuseStep 1535507 = 2303261) B2303261
theorem B323311 : Blo 283827 323311 := bstep (se 1 (by rfl) ⟨242483, by rfl⟩ : syracuseStep 323311 = 484967) B484967
theorem B323743 : Blo 283827 323743 := bstep (se 1 (by rfl) ⟨242807, by rfl⟩ : syracuseStep 323743 = 485615) B485615
theorem B2158811 : Blo 283827 2158811 := bstep (se 1 (by rfl) ⟨1619108, by rfl⟩ : syracuseStep 2158811 = 3238217) B3238217
theorem B3666779 : Blo 283827 3666779 := bstep (se 1 (by rfl) ⟨2750084, by rfl⟩ : syracuseStep 3666779 = 5500169) B5500169
theorem B3470951 : Blo 283827 3470951 := bstep (se 1 (by rfl) ⟨2603213, by rfl⟩ : syracuseStep 3470951 = 5206427) B5206427
theorem B367720199 : Blo 283827 367720199 := bstep (se 1 (by rfl) ⟨275790149, by rfl⟩ : syracuseStep 367720199 = 551580299) B551580299
theorem B3503969 : Blo 283827 3503969 := bstep (se 2 (by rfl) ⟨1313988, by rfl⟩ : syracuseStep 3503969 = 2627977) B2627977
theorem B1832827 : Blo 283827 1832827 := bstep (se 1 (by rfl) ⟨1374620, by rfl⟩ : syracuseStep 1832827 = 2749241) B2749241
theorem B1439855 : Blo 283827 1439855 := bstep (se 1 (by rfl) ⟨1079891, by rfl⟩ : syracuseStep 1439855 = 2159783) B2159783
theorem B3472409 : Blo 283827 3472409 := bstep (se 2 (by rfl) ⟨1302153, by rfl⟩ : syracuseStep 3472409 = 2604307) B2604307
theorem B851809 : Blo 283827 851809 := bstep (se 2 (by rfl) ⟨319428, by rfl⟩ : syracuseStep 851809 = 638857) B638857
theorem B425831 : Blo 283827 425831 := bstep (se 1 (by rfl) ⟨319373, by rfl⟩ : syracuseStep 425831 = 638747) B638747
theorem B1638427 : Blo 283827 1638427 := bstep (se 1 (by rfl) ⟨1228820, by rfl⟩ : syracuseStep 1638427 = 2457641) B2457641
theorem B426143 : Blo 283827 426143 := bstep (se 1 (by rfl) ⟨319607, by rfl⟩ : syracuseStep 426143 = 639215) B639215
theorem B360607 : Blo 283827 360607 := bstep (se 1 (by rfl) ⟨270455, by rfl⟩ : syracuseStep 360607 = 540911) B540911
theorem B426479 : Blo 283827 426479 := bstep (se 1 (by rfl) ⟨319859, by rfl⟩ : syracuseStep 426479 = 639719) B639719
theorem B427145 : Blo 283827 427145 := bstep (se 2 (by rfl) ⟨160179, by rfl⟩ : syracuseStep 427145 = 320359) B320359
theorem B2950505 : Blo 283827 2950505 := bstep (se 2 (by rfl) ⟨1106439, by rfl⟩ : syracuseStep 2950505 = 2212879) B2212879
theorem B690059 : Blo 283827 690059 := bstep (se 1 (by rfl) ⟨517544, by rfl⟩ : syracuseStep 690059 = 1035089) B1035089
theorem B723431 : Blo 283827 723431 := bstep (se 1 (by rfl) ⟨542573, by rfl⟩ : syracuseStep 723431 = 1085147) B1085147
theorem B429383 : Blo 283827 429383 := bstep (se 1 (by rfl) ⟨322037, by rfl⟩ : syracuseStep 429383 = 644075) B644075
theorem B429887 : Blo 283827 429887 := bstep (se 1 (by rfl) ⟨322415, by rfl⟩ : syracuseStep 429887 = 644831) B644831
theorem B429983 : Blo 283827 429983 := bstep (se 1 (by rfl) ⟨322487, by rfl⟩ : syracuseStep 429983 = 644975) B644975
theorem B430619 : Blo 283827 430619 := bstep (se 1 (by rfl) ⟨322964, by rfl⟩ : syracuseStep 430619 = 645929) B645929
theorem B725881 : Blo 283827 725881 := bstep (se 2 (by rfl) ⟨272205, by rfl⟩ : syracuseStep 725881 = 544411) B544411
theorem B431039 : Blo 283827 431039 := bstep (se 1 (by rfl) ⟨323279, by rfl⟩ : syracuseStep 431039 = 646559) B646559
theorem B431081 : Blo 283827 431081 := bstep (se 2 (by rfl) ⟨161655, by rfl⟩ : syracuseStep 431081 = 323311) B323311
theorem B431657 : Blo 283827 431657 := bstep (se 2 (by rfl) ⟨161871, by rfl⟩ : syracuseStep 431657 = 323743) B323743
theorem B10983113 : Blo 283827 10983113 := bstep (se 2 (by rfl) ⟨4118667, by rfl⟩ : syracuseStep 10983113 = 8237335) B8237335
theorem B2758697 : Blo 283827 2758697 := bstep (se 2 (by rfl) ⟨1034511, by rfl⟩ : syracuseStep 2758697 = 2069023) B2069023
theorem B5577017 : Blo 283827 5577017 := bstep (se 2 (by rfl) ⟨2091381, by rfl⟩ : syracuseStep 5577017 = 4182763) B4182763
theorem B1677995 : Blo 283827 1677995 := bstep (se 1 (by rfl) ⟨1258496, by rfl⟩ : syracuseStep 1677995 = 2516993) B2516993
theorem B1023671 : Blo 283827 1023671 := bstep (se 1 (by rfl) ⟨767753, by rfl⟩ : syracuseStep 1023671 = 1535507) B1535507
theorem B245146799 : Blo 283827 245146799 := bstep (se 1 (by rfl) ⟨183860099, by rfl⟩ : syracuseStep 245146799 = 367720199) B367720199
theorem B2335979 : Blo 283827 2335979 := bstep (se 1 (by rfl) ⟨1751984, by rfl⟩ : syracuseStep 2335979 = 3503969) B3503969
theorem B959903 : Blo 283827 959903 := bstep (se 1 (by rfl) ⟨719927, by rfl⟩ : syracuseStep 959903 = 1439855) B1439855
theorem B1617083 : Blo 283827 1617083 := bstep (se 1 (by rfl) ⟨1212812, by rfl⟩ : syracuseStep 1617083 = 2425625) B2425625
theorem B11022479 : Blo 283827 11022479 := bstep (se 1 (by rfl) ⟨8266859, by rfl⟩ : syracuseStep 11022479 = 16533719) B16533719
theorem B24032807 : Blo 283827 24032807 := bstep (se 1 (by rfl) ⟨18024605, by rfl⟩ : syracuseStep 24032807 = 36049211) B36049211
theorem B865865 : Blo 283827 865865 := bstep (se 2 (by rfl) ⟨324699, by rfl⟩ : syracuseStep 865865 = 649399) B649399
theorem B506063 : Blo 283827 506063 := bstep (se 1 (by rfl) ⟨379547, by rfl⟩ : syracuseStep 506063 = 759095) B759095
theorem B11745647 : Blo 283827 11745647 := bstep (se 1 (by rfl) ⟨8809235, by rfl⟩ : syracuseStep 11745647 = 17618471) B17618471
theorem B2931983 : Blo 283827 2931983 := bstep (se 1 (by rfl) ⟨2198987, by rfl⟩ : syracuseStep 2931983 = 4397975) B4397975
theorem B3260087 : Blo 283827 3260087 := bstep (se 1 (by rfl) ⟨2445065, by rfl⟩ : syracuseStep 3260087 = 4890131) B4890131
theorem B5358311 : Blo 283827 5358311 := bstep (se 1 (by rfl) ⟨4018733, by rfl⟩ : syracuseStep 5358311 = 8037467) B8037467
theorem B640169 : Blo 283827 640169 := bstep (se 2 (by rfl) ⟨240063, by rfl⟩ : syracuseStep 640169 = 480127) B480127
theorem B641087 : Blo 283827 641087 := bstep (se 1 (by rfl) ⟨480815, by rfl⟩ : syracuseStep 641087 = 961631) B961631
theorem B1558715 : Blo 283827 1558715 := bstep (se 1 (by rfl) ⟨1169036, by rfl⟩ : syracuseStep 1558715 = 2338073) B2338073
theorem B542953 : Blo 283827 542953 := bstep (se 2 (by rfl) ⟨203607, by rfl⟩ : syracuseStep 542953 = 407215) B407215
theorem B641519 : Blo 283827 641519 := bstep (se 1 (by rfl) ⟨481139, by rfl⟩ : syracuseStep 641519 = 962279) B962279
theorem B2443769 : Blo 283827 2443769 := bstep (se 2 (by rfl) ⟨916413, by rfl⟩ : syracuseStep 2443769 = 1832827) B1832827
theorem B2444519 : Blo 283827 2444519 := bstep (se 1 (by rfl) ⟨1833389, by rfl⟩ : syracuseStep 2444519 = 3666779) B3666779
theorem B2313967 : Blo 283827 2313967 := bstep (se 1 (by rfl) ⟨1735475, by rfl⟩ : syracuseStep 2313967 = 3470951) B3470951
theorem B4968499 : Blo 283827 4968499 := bstep (se 1 (by rfl) ⟨3726374, by rfl⟩ : syracuseStep 4968499 = 7452749) B7452749
theorem B7787087 : Blo 283827 7787087 := bstep (se 1 (by rfl) ⟨5840315, by rfl⟩ : syracuseStep 7787087 = 11680631) B11680631
theorem B2314939 : Blo 283827 2314939 := bstep (se 1 (by rfl) ⟨1736204, by rfl⟩ : syracuseStep 2314939 = 3472409) B3472409
theorem B643895 : Blo 283827 643895 := bstep (se 1 (by rfl) ⟨482921, by rfl⟩ : syracuseStep 643895 = 965843) B965843
theorem B1135745 : Blo 283827 1135745 := bstep (se 2 (by rfl) ⟨425904, by rfl⟩ : syracuseStep 1135745 = 851809) B851809
theorem B283887 : Blo 283827 283887 := bstep (se 1 (by rfl) ⟨212915, by rfl⟩ : syracuseStep 283887 = 425831) B425831
theorem B644435 : Blo 283827 644435 := bstep (se 1 (by rfl) ⟨483326, by rfl⟩ : syracuseStep 644435 = 966653) B966653
theorem B284391 : Blo 283827 284391 := bstep (se 1 (by rfl) ⟨213293, by rfl⟩ : syracuseStep 284391 = 426587) B426587
theorem B1824677 : Blo 283827 1824677 := bstep (se 4 (by rfl) ⟨171063, by rfl⟩ : syracuseStep 1824677 = 342127) B342127
theorem B1857583 : Blo 283827 1857583 := bstep (se 1 (by rfl) ⟨1393187, by rfl⟩ : syracuseStep 1857583 = 2786375) B2786375
theorem B645371 : Blo 283827 645371 := bstep (se 1 (by rfl) ⟨484028, by rfl⟩ : syracuseStep 645371 = 968057) B968057
theorem B1628495 : Blo 283827 1628495 := bstep (se 1 (by rfl) ⟨1221371, by rfl⟩ : syracuseStep 1628495 = 2442743) B2442743
theorem B285231 : Blo 283827 285231 := bstep (se 1 (by rfl) ⟨213923, by rfl⟩ : syracuseStep 285231 = 427847) B427847
theorem B6183539 : Blo 283827 6183539 := bstep (se 1 (by rfl) ⟨4637654, by rfl⟩ : syracuseStep 6183539 = 9275309) B9275309
theorem B613241 : Blo 283827 613241 := bstep (se 2 (by rfl) ⟨229965, by rfl⟩ : syracuseStep 613241 = 459931) B459931
theorem B1367549 : Blo 283827 1367549 := bstep (se 3 (by rfl) ⟨256415, by rfl⟩ : syracuseStep 1367549 = 512831) B512831
theorem B646811 : Blo 283827 646811 := bstep (se 1 (by rfl) ⟨485108, by rfl⟩ : syracuseStep 646811 = 970217) B970217
theorem B483401 : Blo 283827 483401 := bstep (se 2 (by rfl) ⟨181275, by rfl⟩ : syracuseStep 483401 = 362551) B362551
theorem B287231 : Blo 283827 287231 := bstep (se 1 (by rfl) ⟨215423, by rfl⟩ : syracuseStep 287231 = 430847) B430847
theorem B321151 : Blo 283827 321151 := bstep (se 1 (by rfl) ⟨240863, by rfl⟩ : syracuseStep 321151 = 481727) B481727
theorem B812699 : Blo 283827 812699 := bstep (se 1 (by rfl) ⟨609524, by rfl⟩ : syracuseStep 812699 = 1219049) B1219049
theorem B812825 : Blo 283827 812825 := bstep (se 2 (by rfl) ⟨304809, by rfl⟩ : syracuseStep 812825 = 609619) B609619
theorem B1828777 : Blo 283827 1828777 := bstep (se 2 (by rfl) ⟨685791, by rfl⟩ : syracuseStep 1828777 = 1371583) B1371583
theorem B1437263 : Blo 283827 1437263 := bstep (se 1 (by rfl) ⟨1077947, by rfl⟩ : syracuseStep 1437263 = 2155895) B2155895
theorem B4912001 : Blo 283827 4912001 := bstep (se 2 (by rfl) ⟨1842000, by rfl⟩ : syracuseStep 4912001 = 3684001) B3684001
theorem B1439207 : Blo 283827 1439207 := bstep (se 1 (by rfl) ⟨1079405, by rfl⟩ : syracuseStep 1439207 = 2158811) B2158811
theorem B3242591 : Blo 283827 3242591 := bstep (se 1 (by rfl) ⟨2431943, by rfl⟩ : syracuseStep 3242591 = 4863887) B4863887
theorem B818201 : Blo 283827 818201 := bstep (se 2 (by rfl) ⟨306825, by rfl⟩ : syracuseStep 818201 = 613651) B613651
theorem B3572207 : Blo 283827 3572207 := bstep (se 1 (by rfl) ⟨2679155, by rfl⟩ : syracuseStep 3572207 = 5358311) B5358311
theorem B426779 : Blo 283827 426779 := bstep (se 1 (by rfl) ⟨320084, by rfl⟩ : syracuseStep 426779 = 640169) B640169
theorem B1967003 : Blo 283827 1967003 := bstep (se 1 (by rfl) ⟨1475252, by rfl⟩ : syracuseStep 1967003 = 2950505) B2950505
theorem B427391 : Blo 283827 427391 := bstep (se 1 (by rfl) ⟨320543, by rfl⟩ : syracuseStep 427391 = 641087) B641087
theorem B427679 : Blo 283827 427679 := bstep (se 1 (by rfl) ⟨320759, by rfl⟩ : syracuseStep 427679 = 641519) B641519
theorem B428201 : Blo 283827 428201 := bstep (se 2 (by rfl) ⟨160575, by rfl⟩ : syracuseStep 428201 = 321151) B321151
theorem B723937 : Blo 283827 723937 := bstep (se 2 (by rfl) ⟨271476, by rfl⟩ : syracuseStep 723937 = 542953) B542953
theorem B429263 : Blo 283827 429263 := bstep (se 1 (by rfl) ⟨321947, by rfl⟩ : syracuseStep 429263 = 643895) B643895
theorem B429623 : Blo 283827 429623 := bstep (se 1 (by rfl) ⟨322217, by rfl⟩ : syracuseStep 429623 = 644435) B644435
theorem B1216451 : Blo 283827 1216451 := bstep (se 1 (by rfl) ⟨912338, by rfl⟩ : syracuseStep 1216451 = 1824677) B1824677
theorem B1839131 : Blo 283827 1839131 := bstep (se 1 (by rfl) ⟨1379348, by rfl⟩ : syracuseStep 1839131 = 2758697) B2758697
theorem B430247 : Blo 283827 430247 := bstep (se 1 (by rfl) ⟨322685, by rfl⟩ : syracuseStep 430247 = 645371) B645371
theorem B1085663 : Blo 283827 1085663 := bstep (se 1 (by rfl) ⟨814247, by rfl⟩ : syracuseStep 1085663 = 1628495) B1628495
theorem B1118663 : Blo 283827 1118663 := bstep (se 1 (by rfl) ⟨838997, by rfl⟩ : syracuseStep 1118663 = 1677995) B1677995
theorem B3085289 : Blo 283827 3085289 := bstep (se 2 (by rfl) ⟨1156983, by rfl⟩ : syracuseStep 3085289 = 2313967) B2313967
theorem B1840157 : Blo 283827 1840157 := bstep (se 3 (by rfl) ⟨345029, by rfl⟩ : syracuseStep 1840157 = 690059) B690059
theorem B431207 : Blo 283827 431207 := bstep (se 1 (by rfl) ⟨323405, by rfl⟩ : syracuseStep 431207 = 646811) B646811
theorem B6624665 : Blo 283827 6624665 := bstep (se 2 (by rfl) ⟨2484249, by rfl⟩ : syracuseStep 6624665 = 4968499) B4968499
theorem B3086585 : Blo 283827 3086585 := bstep (se 2 (by rfl) ⟨1157469, by rfl⟩ : syracuseStep 3086585 = 2314939) B2314939
theorem B958175 : Blo 283827 958175 := bstep (se 1 (by rfl) ⟨718631, by rfl⟩ : syracuseStep 958175 = 1437263) B1437263
theorem B7348319 : Blo 283827 7348319 := bstep (se 1 (by rfl) ⟨5511239, by rfl⟩ : syracuseStep 7348319 = 11022479) B11022479
theorem B959471 : Blo 283827 959471 := bstep (se 1 (by rfl) ⟨719603, by rfl⟩ : syracuseStep 959471 = 1439207) B1439207
theorem B337375 : Blo 283827 337375 := bstep (se 1 (by rfl) ⟨253031, by rfl⟩ : syracuseStep 337375 = 506063) B506063
theorem B2173391 : Blo 283827 2173391 := bstep (se 1 (by rfl) ⟨1630043, by rfl⟩ : syracuseStep 2173391 = 3260087) B3260087
theorem B16626293 : Blo 283827 16626293 := bstep (se 5 (by rfl) ⟨779357, by rfl⟩ : syracuseStep 16626293 = 1558715) B1558715
theorem B2438369 : Blo 283827 2438369 := bstep (se 2 (by rfl) ⟨914388, by rfl⟩ : syracuseStep 2438369 = 1828777) B1828777
theorem B5191391 : Blo 283827 5191391 := bstep (se 1 (by rfl) ⟨3893543, by rfl⟩ : syracuseStep 5191391 = 7787087) B7787087
theorem B7322075 : Blo 283827 7322075 := bstep (se 1 (by rfl) ⟨5491556, by rfl⟩ : syracuseStep 7322075 = 10983113) B10983113
theorem B408827 : Blo 283827 408827 := bstep (se 1 (by rfl) ⟨306620, by rfl⟩ : syracuseStep 408827 = 613241) B613241
theorem B163431199 : Blo 283827 163431199 := bstep (se 1 (by rfl) ⟨122573399, by rfl⟩ : syracuseStep 163431199 = 245146799) B245146799
theorem B1557319 : Blo 283827 1557319 := bstep (se 1 (by rfl) ⟨1167989, by rfl⟩ : syracuseStep 1557319 = 2335979) B2335979
theorem B639935 : Blo 283827 639935 := bstep (se 1 (by rfl) ⟨479951, by rfl⟩ : syracuseStep 639935 = 959903) B959903
theorem B541799 : Blo 283827 541799 := bstep (se 1 (by rfl) ⟨406349, by rfl⟩ : syracuseStep 541799 = 812699) B812699
theorem B967841 : Blo 283827 967841 := bstep (se 2 (by rfl) ⟨362940, by rfl⟩ : syracuseStep 967841 = 725881) B725881
theorem B541883 : Blo 283827 541883 := bstep (se 1 (by rfl) ⟨406412, by rfl⟩ : syracuseStep 541883 = 812825) B812825
theorem B2476777 : Blo 283827 2476777 := bstep (se 2 (by rfl) ⟨928791, by rfl⟩ : syracuseStep 2476777 = 1857583) B1857583
theorem B577243 : Blo 283827 577243 := bstep (se 1 (by rfl) ⟨432932, by rfl⟩ : syracuseStep 577243 = 865865) B865865
theorem B545467 : Blo 283827 545467 := bstep (se 1 (by rfl) ⟨409100, by rfl⟩ : syracuseStep 545467 = 818201) B818201
theorem B1954655 : Blo 283827 1954655 := bstep (se 1 (by rfl) ⟨1465991, by rfl⟩ : syracuseStep 1954655 = 2931983) B2931983
theorem B2184569 : Blo 283827 2184569 := bstep (se 2 (by rfl) ⟨819213, by rfl⟩ : syracuseStep 2184569 = 1638427) B1638427
theorem B284095 : Blo 283827 284095 := bstep (se 1 (by rfl) ⟨213071, by rfl⟩ : syracuseStep 284095 = 426143) B426143
theorem B480809 : Blo 283827 480809 := bstep (se 2 (by rfl) ⟨180303, by rfl⟩ : syracuseStep 480809 = 360607) B360607
theorem B284319 : Blo 283827 284319 := bstep (se 1 (by rfl) ⟨213239, by rfl⟩ : syracuseStep 284319 = 426479) B426479
theorem B284763 : Blo 283827 284763 := bstep (se 1 (by rfl) ⟨213572, by rfl⟩ : syracuseStep 284763 = 427145) B427145
theorem B12114613 : Blo 283827 12114613 := bstep (se 5 (by rfl) ⟨567872, by rfl⟩ : syracuseStep 12114613 = 1135745) B1135745
theorem B482287 : Blo 283827 482287 := bstep (se 1 (by rfl) ⟨361715, by rfl⟩ : syracuseStep 482287 = 723431) B723431
theorem B1629179 : Blo 283827 1629179 := bstep (se 1 (by rfl) ⟨1221884, by rfl⟩ : syracuseStep 1629179 = 2443769) B2443769
theorem B1629679 : Blo 283827 1629679 := bstep (se 1 (by rfl) ⟨1222259, by rfl⟩ : syracuseStep 1629679 = 2444519) B2444519
theorem B286255 : Blo 283827 286255 := bstep (se 1 (by rfl) ⟨214691, by rfl⟩ : syracuseStep 286255 = 429383) B429383
theorem B286591 : Blo 283827 286591 := bstep (se 1 (by rfl) ⟨214943, by rfl⟩ : syracuseStep 286591 = 429887) B429887
theorem B286655 : Blo 283827 286655 := bstep (se 1 (by rfl) ⟨214991, by rfl⟩ : syracuseStep 286655 = 429983) B429983
theorem B287079 : Blo 283827 287079 := bstep (se 1 (by rfl) ⟨215309, by rfl⟩ : syracuseStep 287079 = 430619) B430619
theorem B287359 : Blo 283827 287359 := bstep (se 1 (by rfl) ⟨215519, by rfl⟩ : syracuseStep 287359 = 431039) B431039
theorem B287387 : Blo 283827 287387 := bstep (se 1 (by rfl) ⟨215540, by rfl⟩ : syracuseStep 287387 = 431081) B431081
theorem B287771 : Blo 283827 287771 := bstep (se 1 (by rfl) ⟨215828, by rfl⟩ : syracuseStep 287771 = 431657) B431657
theorem B4122359 : Blo 283827 4122359 := bstep (se 1 (by rfl) ⟨3091769, by rfl⟩ : syracuseStep 4122359 = 6183539) B6183539
theorem B911699 : Blo 283827 911699 := bstep (se 1 (by rfl) ⟨683774, by rfl⟩ : syracuseStep 911699 = 1367549) B1367549
theorem B682447 : Blo 283827 682447 := bstep (se 1 (by rfl) ⟨511835, by rfl⟩ : syracuseStep 682447 = 1023671) B1023671
theorem B322267 : Blo 283827 322267 := bstep (se 1 (by rfl) ⟨241700, by rfl⟩ : syracuseStep 322267 = 483401) B483401
theorem B14872045 : Blo 283827 14872045 := bstep (se 3 (by rfl) ⟨2788508, by rfl⟩ : syracuseStep 14872045 = 5577017) B5577017
theorem B1078055 : Blo 283827 1078055 := bstep (se 1 (by rfl) ⟨808541, by rfl⟩ : syracuseStep 1078055 = 1617083) B1617083
theorem B3274667 : Blo 283827 3274667 := bstep (se 1 (by rfl) ⟨2456000, by rfl⟩ : syracuseStep 3274667 = 4912001) B4912001
theorem B16021871 : Blo 283827 16021871 := bstep (se 1 (by rfl) ⟨12016403, by rfl⟩ : syracuseStep 16021871 = 24032807) B24032807
theorem B7830431 : Blo 283827 7830431 := bstep (se 1 (by rfl) ⟨5872823, by rfl⟩ : syracuseStep 7830431 = 11745647) B11745647
theorem B2161727 : Blo 283827 2161727 := bstep (se 1 (by rfl) ⟨1621295, by rfl⟩ : syracuseStep 2161727 = 3242591) B3242591
theorem B1311335 : Blo 283827 1311335 := bstep (se 1 (by rfl) ⟨983501, by rfl⟩ : syracuseStep 1311335 = 1967003) B1967003
theorem B426623 : Blo 283827 426623 := bstep (se 1 (by rfl) ⟨319967, by rfl⟩ : syracuseStep 426623 = 639935) B639935
theorem B361199 : Blo 283827 361199 := bstep (se 1 (by rfl) ⟨270899, by rfl⟩ : syracuseStep 361199 = 541799) B541799
theorem B361255 : Blo 283827 361255 := bstep (se 1 (by rfl) ⟨270941, by rfl⟩ : syracuseStep 361255 = 541883) B541883
theorem B217908265 : Blo 283827 217908265 := bstep (se 2 (by rfl) ⟨81715599, by rfl⟩ : syracuseStep 217908265 = 163431199) B163431199
theorem B723775 : Blo 283827 723775 := bstep (se 1 (by rfl) ⟨542831, by rfl⟩ : syracuseStep 723775 = 1085663) B1085663
theorem B429689 : Blo 283827 429689 := bstep (se 2 (by rfl) ⟨161133, by rfl⟩ : syracuseStep 429689 = 322267) B322267
theorem B19829393 : Blo 283827 19829393 := bstep (se 2 (by rfl) ⟨7436022, by rfl⟩ : syracuseStep 19829393 = 14872045) B14872045
theorem B1086119 : Blo 283827 1086119 := bstep (se 1 (by rfl) ⟨814589, by rfl⟩ : syracuseStep 1086119 = 1629179) B1629179
theorem B727289 : Blo 283827 727289 := bstep (se 2 (by rfl) ⟨272733, by rfl⟩ : syracuseStep 727289 = 545467) B545467
theorem B1448927 : Blo 283827 1448927 := bstep (se 1 (by rfl) ⟨1086695, by rfl⟩ : syracuseStep 1448927 = 2173391) B2173391
theorem B11084195 : Blo 283827 11084195 := bstep (se 1 (by rfl) ⟨8313146, by rfl⟩ : syracuseStep 11084195 = 16626293) B16626293
theorem B1090205 : Blo 283827 1090205 := bstep (se 3 (by rfl) ⟨204413, by rfl⟩ : syracuseStep 1090205 = 408827) B408827
theorem B5220287 : Blo 283827 5220287 := bstep (se 1 (by rfl) ⟨3915215, by rfl⟩ : syracuseStep 5220287 = 7830431) B7830431
theorem B2172905 : Blo 283827 2172905 := bstep (se 2 (by rfl) ⟨814839, by rfl⟩ : syracuseStep 2172905 = 1629679) B1629679
theorem B2076425 : Blo 283827 2076425 := bstep (se 2 (by rfl) ⟨778659, by rfl⟩ : syracuseStep 2076425 = 1557319) B1557319
theorem B1226087 : Blo 283827 1226087 := bstep (se 1 (by rfl) ⟨919565, by rfl⟩ : syracuseStep 1226087 = 1839131) B1839131
theorem B1226771 : Blo 283827 1226771 := bstep (se 1 (by rfl) ⟨920078, by rfl⟩ : syracuseStep 1226771 = 1840157) B1840157
theorem B1456379 : Blo 283827 1456379 := bstep (se 1 (by rfl) ⟨1092284, by rfl⟩ : syracuseStep 1456379 = 2184569) B2184569
theorem B965249 : Blo 283827 965249 := bstep (se 2 (by rfl) ⟨361968, by rfl⟩ : syracuseStep 965249 = 723937) B723937
theorem B769657 : Blo 283827 769657 := bstep (se 2 (by rfl) ⟨288621, by rfl⟩ : syracuseStep 769657 = 577243) B577243
theorem B638783 : Blo 283827 638783 := bstep (se 1 (by rfl) ⟨479087, by rfl⟩ : syracuseStep 638783 = 958175) B958175
theorem B4898879 : Blo 283827 4898879 := bstep (se 1 (by rfl) ⟨3674159, by rfl⟩ : syracuseStep 4898879 = 7348319) B7348319
theorem B639647 : Blo 283827 639647 := bstep (se 1 (by rfl) ⟨479735, by rfl⟩ : syracuseStep 639647 = 959471) B959471
theorem B607799 : Blo 283827 607799 := bstep (se 1 (by rfl) ⟨455849, by rfl⟩ : syracuseStep 607799 = 911699) B911699
theorem B1625579 : Blo 283827 1625579 := bstep (se 1 (by rfl) ⟨1219184, by rfl⟩ : syracuseStep 1625579 = 2438369) B2438369
theorem B3460927 : Blo 283827 3460927 := bstep (se 1 (by rfl) ⟨2595695, by rfl⟩ : syracuseStep 3460927 = 5191391) B5191391
theorem B2183111 : Blo 283827 2183111 := bstep (se 1 (by rfl) ⟨1637333, by rfl⟩ : syracuseStep 2183111 = 3274667) B3274667
theorem B643049 : Blo 283827 643049 := bstep (se 2 (by rfl) ⟨241143, by rfl⟩ : syracuseStep 643049 = 482287) B482287
theorem B2381471 : Blo 283827 2381471 := bstep (se 1 (by rfl) ⟨1786103, by rfl⟩ : syracuseStep 2381471 = 3572207) B3572207
theorem B284519 : Blo 283827 284519 := bstep (se 1 (by rfl) ⟨213389, by rfl⟩ : syracuseStep 284519 = 426779) B426779
theorem B645227 : Blo 283827 645227 := bstep (se 1 (by rfl) ⟨483920, by rfl⟩ : syracuseStep 645227 = 967841) B967841
theorem B284927 : Blo 283827 284927 := bstep (se 1 (by rfl) ⟨213695, by rfl⟩ : syracuseStep 284927 = 427391) B427391
theorem B285119 : Blo 283827 285119 := bstep (se 1 (by rfl) ⟨213839, by rfl⟩ : syracuseStep 285119 = 427679) B427679
theorem B285467 : Blo 283827 285467 := bstep (se 1 (by rfl) ⟨214100, by rfl⟩ : syracuseStep 285467 = 428201) B428201
theorem B286175 : Blo 283827 286175 := bstep (se 1 (by rfl) ⟨214631, by rfl⟩ : syracuseStep 286175 = 429263) B429263
theorem B286415 : Blo 283827 286415 := bstep (se 1 (by rfl) ⟨214811, by rfl⟩ : syracuseStep 286415 = 429623) B429623
theorem B810967 : Blo 283827 810967 := bstep (se 1 (by rfl) ⟨608225, by rfl⟩ : syracuseStep 810967 = 1216451) B1216451
theorem B286831 : Blo 283827 286831 := bstep (se 1 (by rfl) ⟨215123, by rfl⟩ : syracuseStep 286831 = 430247) B430247
theorem B745775 : Blo 283827 745775 := bstep (se 1 (by rfl) ⟨559331, by rfl⟩ : syracuseStep 745775 = 1118663) B1118663
theorem B1303103 : Blo 283827 1303103 := bstep (se 1 (by rfl) ⟨977327, by rfl⟩ : syracuseStep 1303103 = 1954655) B1954655
theorem B909929 : Blo 283827 909929 := bstep (se 2 (by rfl) ⟨341223, by rfl⟩ : syracuseStep 909929 = 682447) B682447
theorem B2056859 : Blo 283827 2056859 := bstep (se 1 (by rfl) ⟨1542644, by rfl⟩ : syracuseStep 2056859 = 3085289) B3085289
theorem B287471 : Blo 283827 287471 := bstep (se 1 (by rfl) ⟨215603, by rfl⟩ : syracuseStep 287471 = 431207) B431207
theorem B4416443 : Blo 283827 4416443 := bstep (se 1 (by rfl) ⟨3312332, by rfl⟩ : syracuseStep 4416443 = 6624665) B6624665
theorem B3302369 : Blo 283827 3302369 := bstep (se 2 (by rfl) ⟨1238388, by rfl⟩ : syracuseStep 3302369 = 2476777) B2476777
theorem B320539 : Blo 283827 320539 := bstep (se 1 (by rfl) ⟨240404, by rfl⟩ : syracuseStep 320539 = 480809) B480809
theorem B2057723 : Blo 283827 2057723 := bstep (se 1 (by rfl) ⟨1543292, by rfl⟩ : syracuseStep 2057723 = 3086585) B3086585
theorem B2748239 : Blo 283827 2748239 := bstep (se 1 (by rfl) ⟨2061179, by rfl⟩ : syracuseStep 2748239 = 4122359) B4122359
theorem B1799333 : Blo 283827 1799333 := bstep (se 4 (by rfl) ⟨168687, by rfl⟩ : syracuseStep 1799333 = 337375) B337375
theorem B718703 : Blo 283827 718703 := bstep (se 1 (by rfl) ⟨539027, by rfl⟩ : syracuseStep 718703 = 1078055) B1078055
theorem B16152817 : Blo 283827 16152817 := bstep (se 2 (by rfl) ⟨6057306, by rfl⟩ : syracuseStep 16152817 = 12114613) B12114613
theorem B10681247 : Blo 283827 10681247 := bstep (se 1 (by rfl) ⟨8010935, by rfl⟩ : syracuseStep 10681247 = 16021871) B16021871
theorem B4881383 : Blo 283827 4881383 := bstep (se 1 (by rfl) ⟨3661037, by rfl⟩ : syracuseStep 4881383 = 7322075) B7322075
theorem B1441151 : Blo 283827 1441151 := bstep (se 1 (by rfl) ⟨1080863, by rfl⟩ : syracuseStep 1441151 = 2161727) B2161727
theorem B426431 : Blo 283827 426431 := bstep (se 1 (by rfl) ⟨319823, by rfl⟩ : syracuseStep 426431 = 639647) B639647
theorem B427385 : Blo 283827 427385 := bstep (se 2 (by rfl) ⟨160269, by rfl⟩ : syracuseStep 427385 = 320539) B320539
theorem B1083719 : Blo 283827 1083719 := bstep (se 1 (by rfl) ⟨812789, by rfl⟩ : syracuseStep 1083719 = 1625579) B1625579
theorem B428699 : Blo 283827 428699 := bstep (se 1 (by rfl) ⟨321524, by rfl⟩ : syracuseStep 428699 = 643049) B643049
theorem B724079 : Blo 283827 724079 := bstep (se 1 (by rfl) ⟨543059, by rfl⟩ : syracuseStep 724079 = 1086119) B1086119
theorem B430151 : Blo 283827 430151 := bstep (se 1 (by rfl) ⟨322613, by rfl⟩ : syracuseStep 430151 = 645227) B645227
theorem B497183 : Blo 283827 497183 := bstep (se 1 (by rfl) ⟨372887, by rfl⟩ : syracuseStep 497183 = 745775) B745775
theorem B726803 : Blo 283827 726803 := bstep (se 1 (by rfl) ⟨545102, by rfl⟩ : syracuseStep 726803 = 1090205) B1090205
theorem B2201579 : Blo 283827 2201579 := bstep (se 1 (by rfl) ⟨1651184, by rfl⟩ : syracuseStep 2201579 = 3302369) B3302369
theorem B3480191 : Blo 283827 3480191 := bstep (se 1 (by rfl) ⟨2610143, by rfl⟩ : syracuseStep 3480191 = 5220287) B5220287
theorem B1448603 : Blo 283827 1448603 := bstep (se 1 (by rfl) ⟨1086452, by rfl⟩ : syracuseStep 1448603 = 2172905) B2172905
theorem B1384283 : Blo 283827 1384283 := bstep (se 1 (by rfl) ⟨1038212, by rfl⟩ : syracuseStep 1384283 = 2076425) B2076425
theorem B21537089 : Blo 283827 21537089 := bstep (se 2 (by rfl) ⟨8076408, by rfl⟩ : syracuseStep 21537089 = 16152817) B16152817
theorem B7120831 : Blo 283827 7120831 := bstep (se 1 (by rfl) ⟨5340623, by rfl⟩ : syracuseStep 7120831 = 10681247) B10681247
theorem B3254255 : Blo 283827 3254255 := bstep (se 1 (by rfl) ⟨2440691, by rfl⟩ : syracuseStep 3254255 = 4881383) B4881383
theorem B1026209 : Blo 283827 1026209 := bstep (se 2 (by rfl) ⟨384828, by rfl⟩ : syracuseStep 1026209 = 769657) B769657
theorem B960767 : Blo 283827 960767 := bstep (se 1 (by rfl) ⟨720575, by rfl⟩ : syracuseStep 960767 = 1441151) B1441151
theorem B405199 : Blo 283827 405199 := bstep (se 1 (by rfl) ⟨303899, by rfl⟩ : syracuseStep 405199 = 607799) B607799
theorem B963197 : Blo 283827 963197 := bstep (se 3 (by rfl) ⟨180599, by rfl⟩ : syracuseStep 963197 = 361199) B361199
theorem B1455407 : Blo 283827 1455407 := bstep (se 1 (by rfl) ⟨1091555, by rfl⟩ : syracuseStep 1455407 = 2183111) B2183111
theorem B13219595 : Blo 283827 13219595 := bstep (se 1 (by rfl) ⟨9914696, by rfl⟩ : syracuseStep 13219595 = 19829393) B19829393
theorem B965033 : Blo 283827 965033 := bstep (se 2 (by rfl) ⟨361887, by rfl⟩ : syracuseStep 965033 = 723775) B723775
theorem B1587647 : Blo 283827 1587647 := bstep (se 1 (by rfl) ⟨1190735, by rfl⟩ : syracuseStep 1587647 = 2381471) B2381471
theorem B965951 : Blo 283827 965951 := bstep (se 1 (by rfl) ⟨724463, by rfl⟩ : syracuseStep 965951 = 1448927) B1448927
theorem B7389463 : Blo 283827 7389463 := bstep (se 1 (by rfl) ⟨5542097, by rfl⟩ : syracuseStep 7389463 = 11084195) B11084195
theorem B868735 : Blo 283827 868735 := bstep (se 1 (by rfl) ⟨651551, by rfl⟩ : syracuseStep 868735 = 1303103) B1303103
theorem B606619 : Blo 283827 606619 := bstep (se 1 (by rfl) ⟨454964, by rfl⟩ : syracuseStep 606619 = 909929) B909929
theorem B1199555 : Blo 283827 1199555 := bstep (se 1 (by rfl) ⟨899666, by rfl⟩ : syracuseStep 1199555 = 1799333) B1799333
theorem B479135 : Blo 283827 479135 := bstep (se 1 (by rfl) ⟨359351, by rfl⟩ : syracuseStep 479135 = 718703) B718703
theorem B970919 : Blo 283827 970919 := bstep (se 1 (by rfl) ⟨728189, by rfl⟩ : syracuseStep 970919 = 1456379) B1456379
theorem B643499 : Blo 283827 643499 := bstep (se 1 (by rfl) ⟨482624, by rfl⟩ : syracuseStep 643499 = 965249) B965249
theorem B3265919 : Blo 283827 3265919 := bstep (se 1 (by rfl) ⟨2449439, by rfl⟩ : syracuseStep 3265919 = 4898879) B4898879
theorem B874223 : Blo 283827 874223 := bstep (se 1 (by rfl) ⟨655667, by rfl⟩ : syracuseStep 874223 = 1311335) B1311335
theorem B284415 : Blo 283827 284415 := bstep (se 1 (by rfl) ⟨213311, by rfl⟩ : syracuseStep 284415 = 426623) B426623
theorem B481673 : Blo 283827 481673 := bstep (se 2 (by rfl) ⟨180627, by rfl⟩ : syracuseStep 481673 = 361255) B361255
theorem B290544353 : Blo 283827 290544353 := bstep (se 2 (by rfl) ⟨108954132, by rfl⟩ : syracuseStep 290544353 = 217908265) B217908265
theorem B286459 : Blo 283827 286459 := bstep (se 1 (by rfl) ⟨214844, by rfl⟩ : syracuseStep 286459 = 429689) B429689
theorem B484859 : Blo 283827 484859 := bstep (se 1 (by rfl) ⟨363644, by rfl⟩ : syracuseStep 484859 = 727289) B727289
theorem B4614569 : Blo 283827 4614569 := bstep (se 2 (by rfl) ⟨1730463, by rfl⟩ : syracuseStep 4614569 = 3460927) B3460927
theorem B1371239 : Blo 283827 1371239 := bstep (se 1 (by rfl) ⟨1028429, by rfl⟩ : syracuseStep 1371239 = 2056859) B2056859
theorem B2944295 : Blo 283827 2944295 := bstep (se 1 (by rfl) ⟨2208221, by rfl⟩ : syracuseStep 2944295 = 4416443) B4416443
theorem B1371815 : Blo 283827 1371815 := bstep (se 1 (by rfl) ⟨1028861, by rfl⟩ : syracuseStep 1371815 = 2057723) B2057723
theorem B1832159 : Blo 283827 1832159 := bstep (se 1 (by rfl) ⟨1374119, by rfl⟩ : syracuseStep 1832159 = 2748239) B2748239
theorem B817391 : Blo 283827 817391 := bstep (se 1 (by rfl) ⟨613043, by rfl⟩ : syracuseStep 817391 = 1226087) B1226087
theorem B817847 : Blo 283827 817847 := bstep (se 1 (by rfl) ⟨613385, by rfl⟩ : syracuseStep 817847 = 1226771) B1226771
theorem B425855 : Blo 283827 425855 := bstep (se 1 (by rfl) ⟨319391, by rfl⟩ : syracuseStep 425855 = 638783) B638783
theorem B1081289 : Blo 283827 1081289 := bstep (se 2 (by rfl) ⟨405483, by rfl⟩ : syracuseStep 1081289 = 810967) B810967
theorem B722479 : Blo 283827 722479 := bstep (se 1 (by rfl) ⟨541859, by rfl⟩ : syracuseStep 722479 = 1083719) B1083719
theorem B428999 : Blo 283827 428999 := bstep (se 1 (by rfl) ⟨321749, by rfl⟩ : syracuseStep 428999 = 643499) B643499
theorem B4885757 : Blo 283827 4885757 := bstep (se 3 (by rfl) ⟨916079, by rfl⟩ : syracuseStep 4885757 = 1832159) B1832159
theorem B193696235 : Blo 283827 193696235 := bstep (se 1 (by rfl) ⟨145272176, by rfl⟩ : syracuseStep 193696235 = 290544353) B290544353
theorem B922855 : Blo 283827 922855 := bstep (se 1 (by rfl) ⟨692141, by rfl⟩ : syracuseStep 922855 = 1384283) B1384283
theorem B14358059 : Blo 283827 14358059 := bstep (se 1 (by rfl) ⟨10768544, by rfl⟩ : syracuseStep 14358059 = 21537089) B21537089
theorem B4233725 : Blo 283827 4233725 := bstep (se 3 (by rfl) ⟨793823, by rfl⟩ : syracuseStep 4233725 = 1587647) B1587647
theorem B2169503 : Blo 283827 2169503 := bstep (se 1 (by rfl) ⟨1627127, by rfl⟩ : syracuseStep 2169503 = 3254255) B3254255
theorem B1158313 : Blo 283827 1158313 := bstep (se 2 (by rfl) ⟨434367, by rfl⟩ : syracuseStep 1158313 = 868735) B868735
theorem B799703 : Blo 283827 799703 := bstep (se 1 (by rfl) ⟨599777, by rfl⟩ : syracuseStep 799703 = 1199555) B1199555
theorem B2177279 : Blo 283827 2177279 := bstep (se 1 (by rfl) ⟨1632959, by rfl⟩ : syracuseStep 2177279 = 3265919) B3265919
theorem B1325821 : Blo 283827 1325821 := bstep (se 3 (by rfl) ⟨248591, by rfl⟩ : syracuseStep 1325821 = 497183) B497183
theorem B965735 : Blo 283827 965735 := bstep (se 1 (by rfl) ⟨724301, by rfl⟩ : syracuseStep 965735 = 1448603) B1448603
theorem B540265 : Blo 283827 540265 := bstep (se 2 (by rfl) ⟨202599, by rfl⟩ : syracuseStep 540265 = 405199) B405199
theorem B2179709 : Blo 283827 2179709 := bstep (se 3 (by rfl) ⟨408695, by rfl⟩ : syracuseStep 2179709 = 817391) B817391
theorem B640511 : Blo 283827 640511 := bstep (se 1 (by rfl) ⟨480383, by rfl⟩ : syracuseStep 640511 = 960767) B960767
theorem B642131 : Blo 283827 642131 := bstep (se 1 (by rfl) ⟨481598, by rfl⟩ : syracuseStep 642131 = 963197) B963197
theorem B970271 : Blo 283827 970271 := bstep (se 1 (by rfl) ⟨727703, by rfl⟩ : syracuseStep 970271 = 1455407) B1455407
theorem B643355 : Blo 283827 643355 := bstep (se 1 (by rfl) ⟨482516, by rfl⟩ : syracuseStep 643355 = 965033) B965033
theorem B545231 : Blo 283827 545231 := bstep (se 1 (by rfl) ⟨408923, by rfl⟩ : syracuseStep 545231 = 817847) B817847
theorem B643967 : Blo 283827 643967 := bstep (se 1 (by rfl) ⟨482975, by rfl⟩ : syracuseStep 643967 = 965951) B965951
theorem B283903 : Blo 283827 283903 := bstep (se 1 (by rfl) ⟨212927, by rfl⟩ : syracuseStep 283903 = 425855) B425855
theorem B284287 : Blo 283827 284287 := bstep (se 1 (by rfl) ⟨213215, by rfl⟩ : syracuseStep 284287 = 426431) B426431
theorem B9852617 : Blo 283827 9852617 := bstep (se 2 (by rfl) ⟨3694731, by rfl⟩ : syracuseStep 9852617 = 7389463) B7389463
theorem B284923 : Blo 283827 284923 := bstep (se 1 (by rfl) ⟨213692, by rfl⟩ : syracuseStep 284923 = 427385) B427385
theorem B285799 : Blo 283827 285799 := bstep (se 1 (by rfl) ⟨214349, by rfl⟩ : syracuseStep 285799 = 428699) B428699
theorem B482719 : Blo 283827 482719 := bstep (se 1 (by rfl) ⟨362039, by rfl⟩ : syracuseStep 482719 = 724079) B724079
theorem B3235301 : Blo 283827 3235301 := bstep (se 4 (by rfl) ⟨303309, by rfl⟩ : syracuseStep 3235301 = 606619) B606619
theorem B9494441 : Blo 283827 9494441 := bstep (se 2 (by rfl) ⟨3560415, by rfl⟩ : syracuseStep 9494441 = 7120831) B7120831
theorem B319423 : Blo 283827 319423 := bstep (se 1 (by rfl) ⟨239567, by rfl⟩ : syracuseStep 319423 = 479135) B479135
theorem B286767 : Blo 283827 286767 := bstep (se 1 (by rfl) ⟨215075, by rfl⟩ : syracuseStep 286767 = 430151) B430151
theorem B647279 : Blo 283827 647279 := bstep (se 1 (by rfl) ⟨485459, by rfl⟩ : syracuseStep 647279 = 970919) B970919
theorem B582815 : Blo 283827 582815 := bstep (se 1 (by rfl) ⟨437111, by rfl⟩ : syracuseStep 582815 = 874223) B874223
theorem B484535 : Blo 283827 484535 := bstep (se 1 (by rfl) ⟨363401, by rfl⟩ : syracuseStep 484535 = 726803) B726803
theorem B1467719 : Blo 283827 1467719 := bstep (se 1 (by rfl) ⟨1100789, by rfl⟩ : syracuseStep 1467719 = 2201579) B2201579
theorem B321115 : Blo 283827 321115 := bstep (se 1 (by rfl) ⟨240836, by rfl⟩ : syracuseStep 321115 = 481673) B481673
theorem B2320127 : Blo 283827 2320127 := bstep (se 1 (by rfl) ⟨1740095, by rfl⟩ : syracuseStep 2320127 = 3480191) B3480191
theorem B323239 : Blo 283827 323239 := bstep (se 1 (by rfl) ⟨242429, by rfl⟩ : syracuseStep 323239 = 484859) B484859
theorem B684139 : Blo 283827 684139 := bstep (se 1 (by rfl) ⟨513104, by rfl⟩ : syracuseStep 684139 = 1026209) B1026209
theorem B3076379 : Blo 283827 3076379 := bstep (se 1 (by rfl) ⟨2307284, by rfl⟩ : syracuseStep 3076379 = 4614569) B4614569
theorem B914159 : Blo 283827 914159 := bstep (se 1 (by rfl) ⟨685619, by rfl⟩ : syracuseStep 914159 = 1371239) B1371239
theorem B1962863 : Blo 283827 1962863 := bstep (se 1 (by rfl) ⟨1472147, by rfl⟩ : syracuseStep 1962863 = 2944295) B2944295
theorem B914543 : Blo 283827 914543 := bstep (se 1 (by rfl) ⟨685907, by rfl⟩ : syracuseStep 914543 = 1371815) B1371815
theorem B8813063 : Blo 283827 8813063 := bstep (se 1 (by rfl) ⟨6609797, by rfl⟩ : syracuseStep 8813063 = 13219595) B13219595
theorem B720859 : Blo 283827 720859 := bstep (se 1 (by rfl) ⟨540644, by rfl⟩ : syracuseStep 720859 = 1081289) B1081289
theorem B427007 : Blo 283827 427007 := bstep (se 1 (by rfl) ⟨320255, by rfl⟩ : syracuseStep 427007 = 640511) B640511
theorem B428087 : Blo 283827 428087 := bstep (se 1 (by rfl) ⟨321065, by rfl⟩ : syracuseStep 428087 = 642131) B642131
theorem B428153 : Blo 283827 428153 := bstep (se 2 (by rfl) ⟨160557, by rfl⟩ : syracuseStep 428153 = 321115) B321115
theorem B428903 : Blo 283827 428903 := bstep (se 1 (by rfl) ⟨321677, by rfl⟩ : syracuseStep 428903 = 643355) B643355
theorem B429311 : Blo 283827 429311 := bstep (se 1 (by rfl) ⟨321983, by rfl⟩ : syracuseStep 429311 = 643967) B643967
theorem B9572039 : Blo 283827 9572039 := bstep (se 1 (by rfl) ⟨7179029, by rfl⟩ : syracuseStep 9572039 = 14358059) B14358059
theorem B1544417 : Blo 283827 1544417 := bstep (se 2 (by rfl) ⟨579156, by rfl⟩ : syracuseStep 1544417 = 1158313) B1158313
theorem B2822483 : Blo 283827 2822483 := bstep (se 1 (by rfl) ⟨2116862, by rfl⟩ : syracuseStep 2822483 = 4233725) B4233725
theorem B1446335 : Blo 283827 1446335 := bstep (se 1 (by rfl) ⟨1084751, by rfl⟩ : syracuseStep 1446335 = 2169503) B2169503
theorem B430985 : Blo 283827 430985 := bstep (se 2 (by rfl) ⟨161619, by rfl⟩ : syracuseStep 430985 = 323239) B323239
theorem B6329627 : Blo 283827 6329627 := bstep (se 1 (by rfl) ⟨4747220, by rfl⟩ : syracuseStep 6329627 = 9494441) B9494441
theorem B431519 : Blo 283827 431519 := bstep (se 1 (by rfl) ⟨323639, by rfl⟩ : syracuseStep 431519 = 647279) B647279
theorem B1546751 : Blo 283827 1546751 := bstep (se 1 (by rfl) ⟨1160063, by rfl⟩ : syracuseStep 1546751 = 2320127) B2320127
theorem B23501501 : Blo 283827 23501501 := bstep (se 3 (by rfl) ⟨4406531, by rfl⟩ : syracuseStep 23501501 = 8813063) B8813063
theorem B533135 : Blo 283827 533135 := bstep (se 1 (by rfl) ⟨399851, by rfl⟩ : syracuseStep 533135 = 799703) B799703
theorem B1451519 : Blo 283827 1451519 := bstep (se 1 (by rfl) ⟨1088639, by rfl⟩ : syracuseStep 1451519 = 2177279) B2177279
theorem B961145 : Blo 283827 961145 := bstep (se 2 (by rfl) ⟨360429, by rfl⟩ : syracuseStep 961145 = 720859) B720859
theorem B1453139 : Blo 283827 1453139 := bstep (se 1 (by rfl) ⟨1089854, by rfl⟩ : syracuseStep 1453139 = 2179709) B2179709
theorem B1453949 : Blo 283827 1453949 := bstep (se 3 (by rfl) ⟨272615, by rfl⟩ : syracuseStep 1453949 = 545231) B545231
theorem B963305 : Blo 283827 963305 := bstep (se 2 (by rfl) ⟨361239, by rfl⟩ : syracuseStep 963305 = 722479) B722479
theorem B3257171 : Blo 283827 3257171 := bstep (se 1 (by rfl) ⟨2442878, by rfl⟩ : syracuseStep 3257171 = 4885757) B4885757
theorem B1554173 : Blo 283827 1554173 := bstep (se 3 (by rfl) ⟨291407, by rfl⟩ : syracuseStep 1554173 = 582815) B582815
theorem B6568411 : Blo 283827 6568411 := bstep (se 1 (by rfl) ⟨4926308, by rfl⟩ : syracuseStep 6568411 = 9852617) B9852617
theorem B1230473 : Blo 283827 1230473 := bstep (se 2 (by rfl) ⟨461427, by rfl⟩ : syracuseStep 1230473 = 922855) B922855
theorem B2050919 : Blo 283827 2050919 := bstep (se 1 (by rfl) ⟨1538189, by rfl⟩ : syracuseStep 2050919 = 3076379) B3076379
theorem B609439 : Blo 283827 609439 := bstep (se 1 (by rfl) ⟨457079, by rfl⟩ : syracuseStep 609439 = 914159) B914159
theorem B609695 : Blo 283827 609695 := bstep (se 1 (by rfl) ⟨457271, by rfl⟩ : syracuseStep 609695 = 914543) B914543
theorem B643625 : Blo 283827 643625 := bstep (se 2 (by rfl) ⟨241359, by rfl⟩ : syracuseStep 643625 = 482719) B482719
theorem B643823 : Blo 283827 643823 := bstep (se 1 (by rfl) ⟨482867, by rfl⟩ : syracuseStep 643823 = 965735) B965735
theorem B285999 : Blo 283827 285999 := bstep (se 1 (by rfl) ⟨214499, by rfl⟩ : syracuseStep 285999 = 428999) B428999
theorem B646847 : Blo 283827 646847 := bstep (se 1 (by rfl) ⟨485135, by rfl⟩ : syracuseStep 646847 = 970271) B970271
theorem B129130823 : Blo 283827 129130823 := bstep (se 1 (by rfl) ⟨96848117, by rfl⟩ : syracuseStep 129130823 = 193696235) B193696235
theorem B2156867 : Blo 283827 2156867 := bstep (se 1 (by rfl) ⟨1617650, by rfl⟩ : syracuseStep 2156867 = 3235301) B3235301
theorem B912185 : Blo 283827 912185 := bstep (se 2 (by rfl) ⟨342069, by rfl⟩ : syracuseStep 912185 = 684139) B684139
theorem B323023 : Blo 283827 323023 := bstep (se 1 (by rfl) ⟨242267, by rfl⟩ : syracuseStep 323023 = 484535) B484535
theorem B978479 : Blo 283827 978479 := bstep (se 1 (by rfl) ⟨733859, by rfl⟩ : syracuseStep 978479 = 1467719) B1467719
theorem B1308575 : Blo 283827 1308575 := bstep (se 1 (by rfl) ⟨981431, by rfl⟩ : syracuseStep 1308575 = 1962863) B1962863
theorem B1767761 : Blo 283827 1767761 := bstep (se 2 (by rfl) ⟨662910, by rfl⟩ : syracuseStep 1767761 = 1325821) B1325821
theorem B720353 : Blo 283827 720353 := bstep (se 2 (by rfl) ⟨270132, by rfl⟩ : syracuseStep 720353 = 540265) B540265
theorem B425897 : Blo 283827 425897 := bstep (se 2 (by rfl) ⟨159711, by rfl⟩ : syracuseStep 425897 = 319423) B319423
theorem B820315 : Blo 283827 820315 := bstep (se 1 (by rfl) ⟨615236, by rfl⟩ : syracuseStep 820315 = 1230473) B1230473
theorem B429083 : Blo 283827 429083 := bstep (se 1 (by rfl) ⟨321812, by rfl⟩ : syracuseStep 429083 = 643625) B643625
theorem B429215 : Blo 283827 429215 := bstep (se 1 (by rfl) ⟨321911, by rfl⟩ : syracuseStep 429215 = 643823) B643823
theorem B15667667 : Blo 283827 15667667 := bstep (se 1 (by rfl) ⟨11750750, by rfl⟩ : syracuseStep 15667667 = 23501501) B23501501
theorem B430697 : Blo 283827 430697 := bstep (se 2 (by rfl) ⟨161511, by rfl⟩ : syracuseStep 430697 = 323023) B323023
theorem B431231 : Blo 283827 431231 := bstep (se 1 (by rfl) ⟨323423, by rfl⟩ : syracuseStep 431231 = 646847) B646847
theorem B86087215 : Blo 283827 86087215 := bstep (se 1 (by rfl) ⟨64565411, by rfl⟩ : syracuseStep 86087215 = 129130823) B129130823
theorem B2171447 : Blo 283827 2171447 := bstep (se 1 (by rfl) ⟨1628585, by rfl⟩ : syracuseStep 2171447 = 3257171) B3257171
theorem B8757881 : Blo 283827 8757881 := bstep (se 2 (by rfl) ⟨3284205, by rfl⟩ : syracuseStep 8757881 = 6568411) B6568411
theorem B406463 : Blo 283827 406463 := bstep (se 1 (by rfl) ⟨304847, by rfl⟩ : syracuseStep 406463 = 609695) B609695
theorem B1029611 : Blo 283827 1029611 := bstep (se 1 (by rfl) ⟨772208, by rfl⟩ : syracuseStep 1029611 = 1544417) B1544417
theorem B964223 : Blo 283827 964223 := bstep (se 1 (by rfl) ⟨723167, by rfl⟩ : syracuseStep 964223 = 1446335) B1446335
theorem B1031167 : Blo 283827 1031167 := bstep (se 1 (by rfl) ⟨773375, by rfl⟩ : syracuseStep 1031167 = 1546751) B1546751
theorem B967679 : Blo 283827 967679 := bstep (se 1 (by rfl) ⟨725759, by rfl⟩ : syracuseStep 967679 = 1451519) B1451519
theorem B640763 : Blo 283827 640763 := bstep (se 1 (by rfl) ⟨480572, by rfl⟩ : syracuseStep 640763 = 961145) B961145
theorem B608123 : Blo 283827 608123 := bstep (se 1 (by rfl) ⟨456092, by rfl⟩ : syracuseStep 608123 = 912185) B912185
theorem B968759 : Blo 283827 968759 := bstep (se 1 (by rfl) ⟨726569, by rfl⟩ : syracuseStep 968759 = 1453139) B1453139
theorem B969299 : Blo 283827 969299 := bstep (se 1 (by rfl) ⟨726974, by rfl⟩ : syracuseStep 969299 = 1453949) B1453949
theorem B642203 : Blo 283827 642203 := bstep (se 1 (by rfl) ⟨481652, by rfl⟩ : syracuseStep 642203 = 963305) B963305
theorem B1036115 : Blo 283827 1036115 := bstep (se 1 (by rfl) ⟨777086, by rfl⟩ : syracuseStep 1036115 = 1554173) B1554173
theorem B872383 : Blo 283827 872383 := bstep (se 1 (by rfl) ⟨654287, by rfl⟩ : syracuseStep 872383 = 1308575) B1308575
theorem B480235 : Blo 283827 480235 := bstep (se 1 (by rfl) ⟨360176, by rfl⟩ : syracuseStep 480235 = 720353) B720353
theorem B283931 : Blo 283827 283931 := bstep (se 1 (by rfl) ⟨212948, by rfl⟩ : syracuseStep 283931 = 425897) B425897
theorem B284671 : Blo 283827 284671 := bstep (se 1 (by rfl) ⟨213503, by rfl⟩ : syracuseStep 284671 = 427007) B427007
theorem B7526621 : Blo 283827 7526621 := bstep (se 3 (by rfl) ⟨1411241, by rfl⟩ : syracuseStep 7526621 = 2822483) B2822483
theorem B285391 : Blo 283827 285391 := bstep (se 1 (by rfl) ⟨214043, by rfl⟩ : syracuseStep 285391 = 428087) B428087
theorem B285435 : Blo 283827 285435 := bstep (se 1 (by rfl) ⟨214076, by rfl⟩ : syracuseStep 285435 = 428153) B428153
theorem B1367279 : Blo 283827 1367279 := bstep (se 1 (by rfl) ⟨1025459, by rfl⟩ : syracuseStep 1367279 = 2050919) B2050919
theorem B285935 : Blo 283827 285935 := bstep (se 1 (by rfl) ⟨214451, by rfl⟩ : syracuseStep 285935 = 428903) B428903
theorem B286207 : Blo 283827 286207 := bstep (se 1 (by rfl) ⟨214655, by rfl⟩ : syracuseStep 286207 = 429311) B429311
theorem B6381359 : Blo 283827 6381359 := bstep (se 1 (by rfl) ⟨4786019, by rfl⟩ : syracuseStep 6381359 = 9572039) B9572039
theorem B287323 : Blo 283827 287323 := bstep (se 1 (by rfl) ⟨215492, by rfl⟩ : syracuseStep 287323 = 430985) B430985
theorem B4219751 : Blo 283827 4219751 := bstep (se 1 (by rfl) ⟨3164813, by rfl⟩ : syracuseStep 4219751 = 6329627) B6329627
theorem B287679 : Blo 283827 287679 := bstep (se 1 (by rfl) ⟨215759, by rfl⟩ : syracuseStep 287679 = 431519) B431519
theorem B812585 : Blo 283827 812585 := bstep (se 2 (by rfl) ⟨304719, by rfl⟩ : syracuseStep 812585 = 609439) B609439
theorem B355423 : Blo 283827 355423 := bstep (se 1 (by rfl) ⟨266567, by rfl⟩ : syracuseStep 355423 = 533135) B533135
theorem B1437911 : Blo 283827 1437911 := bstep (se 1 (by rfl) ⟨1078433, by rfl⟩ : syracuseStep 1437911 = 2156867) B2156867
theorem B652319 : Blo 283827 652319 := bstep (se 1 (by rfl) ⟨489239, by rfl⟩ : syracuseStep 652319 = 978479) B978479
theorem B1178507 : Blo 283827 1178507 := bstep (se 1 (by rfl) ⟨883880, by rfl⟩ : syracuseStep 1178507 = 1767761) B1767761
theorem B427175 : Blo 283827 427175 := bstep (se 1 (by rfl) ⟨320381, by rfl⟩ : syracuseStep 427175 = 640763) B640763
theorem B428135 : Blo 283827 428135 := bstep (se 1 (by rfl) ⟨321101, by rfl⟩ : syracuseStep 428135 = 642203) B642203
theorem B1083901 : Blo 283827 1083901 := bstep (se 3 (by rfl) ⟨203231, by rfl⟩ : syracuseStep 1083901 = 406463) B406463
theorem B690743 : Blo 283827 690743 := bstep (se 1 (by rfl) ⟨518057, by rfl⟩ : syracuseStep 690743 = 1036115) B1036115
theorem B1447631 : Blo 283827 1447631 := bstep (se 1 (by rfl) ⟨1085723, by rfl⟩ : syracuseStep 1447631 = 2171447) B2171447
theorem B5838587 : Blo 283827 5838587 := bstep (se 1 (by rfl) ⟨4378940, by rfl⟩ : syracuseStep 5838587 = 8757881) B8757881
theorem B958607 : Blo 283827 958607 := bstep (se 1 (by rfl) ⟨718955, by rfl⟩ : syracuseStep 958607 = 1437911) B1437911
theorem B434879 : Blo 283827 434879 := bstep (se 1 (by rfl) ⟨326159, by rfl⟩ : syracuseStep 434879 = 652319) B652319
theorem B405415 : Blo 283827 405415 := bstep (se 1 (by rfl) ⟨304061, by rfl⟩ : syracuseStep 405415 = 608123) B608123
theorem B1093753 : Blo 283827 1093753 := bstep (se 2 (by rfl) ⟨410157, by rfl⟩ : syracuseStep 1093753 = 820315) B820315
theorem B473897 : Blo 283827 473897 := bstep (se 2 (by rfl) ⟨177711, by rfl⟩ : syracuseStep 473897 = 355423) B355423
theorem B180042709 : Blo 283827 180042709 := bstep (se 7 (by rfl) ⟨2109875, by rfl⟩ : syracuseStep 180042709 = 4219751) B4219751
theorem B1163177 : Blo 283827 1163177 := bstep (se 2 (by rfl) ⟨436191, by rfl⟩ : syracuseStep 1163177 = 872383) B872383
theorem B20070989 : Blo 283827 20070989 := bstep (se 3 (by rfl) ⟨3763310, by rfl⟩ : syracuseStep 20070989 = 7526621) B7526621
theorem B541723 : Blo 283827 541723 := bstep (se 1 (by rfl) ⟨406292, by rfl⟩ : syracuseStep 541723 = 812585) B812585
theorem B640313 : Blo 283827 640313 := bstep (se 2 (by rfl) ⟨240117, by rfl⟩ : syracuseStep 640313 = 480235) B480235
theorem B642815 : Blo 283827 642815 := bstep (se 1 (by rfl) ⟨482111, by rfl⟩ : syracuseStep 642815 = 964223) B964223
theorem B645119 : Blo 283827 645119 := bstep (se 1 (by rfl) ⟨483839, by rfl⟩ : syracuseStep 645119 = 967679) B967679
theorem B645839 : Blo 283827 645839 := bstep (se 1 (by rfl) ⟨484379, by rfl⟩ : syracuseStep 645839 = 968759) B968759
theorem B646199 : Blo 283827 646199 := bstep (se 1 (by rfl) ⟨484649, by rfl⟩ : syracuseStep 646199 = 969299) B969299
theorem B286055 : Blo 283827 286055 := bstep (se 1 (by rfl) ⟨214541, by rfl⟩ : syracuseStep 286055 = 429083) B429083
theorem B286143 : Blo 283827 286143 := bstep (se 1 (by rfl) ⟨214607, by rfl⟩ : syracuseStep 286143 = 429215) B429215
theorem B10445111 : Blo 283827 10445111 := bstep (se 1 (by rfl) ⟨7833833, by rfl⟩ : syracuseStep 10445111 = 15667667) B15667667
theorem B287131 : Blo 283827 287131 := bstep (se 1 (by rfl) ⟨215348, by rfl⟩ : syracuseStep 287131 = 430697) B430697
theorem B287487 : Blo 283827 287487 := bstep (se 1 (by rfl) ⟨215615, by rfl⟩ : syracuseStep 287487 = 431231) B431231
theorem B911519 : Blo 283827 911519 := bstep (se 1 (by rfl) ⟨683639, by rfl⟩ : syracuseStep 911519 = 1367279) B1367279
theorem B4254239 : Blo 283827 4254239 := bstep (se 1 (by rfl) ⟨3190679, by rfl⟩ : syracuseStep 4254239 = 6381359) B6381359
theorem B114782953 : Blo 283827 114782953 := bstep (se 2 (by rfl) ⟨43043607, by rfl⟩ : syracuseStep 114782953 = 86087215) B86087215
theorem B3142685 : Blo 283827 3142685 := bstep (se 3 (by rfl) ⟨589253, by rfl⟩ : syracuseStep 3142685 = 1178507) B1178507
theorem B686407 : Blo 283827 686407 := bstep (se 1 (by rfl) ⟨514805, by rfl⟩ : syracuseStep 686407 = 1029611) B1029611
theorem B1374889 : Blo 283827 1374889 := bstep (se 2 (by rfl) ⟨515583, by rfl⟩ : syracuseStep 1374889 = 1031167) B1031167
theorem B426875 : Blo 283827 426875 := bstep (se 1 (by rfl) ⟨320156, by rfl⟩ : syracuseStep 426875 = 640313) B640313
theorem B722297 : Blo 283827 722297 := bstep (se 2 (by rfl) ⟨270861, by rfl⟩ : syracuseStep 722297 = 541723) B541723
theorem B460495 : Blo 283827 460495 := bstep (se 1 (by rfl) ⟨345371, by rfl⟩ : syracuseStep 460495 = 690743) B690743
theorem B428543 : Blo 283827 428543 := bstep (se 1 (by rfl) ⟨321407, by rfl⟩ : syracuseStep 428543 = 642815) B642815
theorem B1445201 : Blo 283827 1445201 := bstep (se 2 (by rfl) ⟨541950, by rfl⟩ : syracuseStep 1445201 = 1083901) B1083901
theorem B430079 : Blo 283827 430079 := bstep (se 1 (by rfl) ⟨322559, by rfl⟩ : syracuseStep 430079 = 645119) B645119
theorem B430559 : Blo 283827 430559 := bstep (se 1 (by rfl) ⟨322919, by rfl⟩ : syracuseStep 430559 = 645839) B645839
theorem B430799 : Blo 283827 430799 := bstep (se 1 (by rfl) ⟨323099, by rfl⟩ : syracuseStep 430799 = 646199) B646199
theorem B11344637 : Blo 283827 11344637 := bstep (se 3 (by rfl) ⟨2127119, by rfl⟩ : syracuseStep 11344637 = 4254239) B4254239
theorem B13380659 : Blo 283827 13380659 := bstep (se 1 (by rfl) ⟨10035494, by rfl⟩ : syracuseStep 13380659 = 20070989) B20070989
theorem B965087 : Blo 283827 965087 := bstep (se 1 (by rfl) ⟨723815, by rfl⟩ : syracuseStep 965087 = 1447631) B1447631
theorem B639071 : Blo 283827 639071 := bstep (se 1 (by rfl) ⟨479303, by rfl⟩ : syracuseStep 639071 = 958607) B958607
theorem B1458337 : Blo 283827 1458337 := bstep (se 2 (by rfl) ⟨546876, by rfl⟩ : syracuseStep 1458337 = 1093753) B1093753
theorem B6963407 : Blo 283827 6963407 := bstep (se 1 (by rfl) ⟨5222555, by rfl⟩ : syracuseStep 6963407 = 10445111) B10445111
theorem B153043937 : Blo 283827 153043937 := bstep (se 2 (by rfl) ⟨57391476, by rfl⟩ : syracuseStep 153043937 = 114782953) B114782953
theorem B607679 : Blo 283827 607679 := bstep (se 1 (by rfl) ⟨455759, by rfl⟩ : syracuseStep 607679 = 911519) B911519
theorem B1263725 : Blo 283827 1263725 := bstep (se 3 (by rfl) ⟨236948, by rfl⟩ : syracuseStep 1263725 = 473897) B473897
theorem B775451 : Blo 283827 775451 := bstep (se 1 (by rfl) ⟨581588, by rfl⟩ : syracuseStep 775451 = 1163177) B1163177
theorem B284783 : Blo 283827 284783 := bstep (se 1 (by rfl) ⟨213587, by rfl⟩ : syracuseStep 284783 = 427175) B427175
theorem B285423 : Blo 283827 285423 := bstep (se 1 (by rfl) ⟨214067, by rfl⟩ : syracuseStep 285423 = 428135) B428135
theorem B8380493 : Blo 283827 8380493 := bstep (se 3 (by rfl) ⟨1571342, by rfl⟩ : syracuseStep 8380493 = 3142685) B3142685
theorem B3892391 : Blo 283827 3892391 := bstep (se 1 (by rfl) ⟨2919293, by rfl⟩ : syracuseStep 3892391 = 5838587) B5838587
theorem B289919 : Blo 283827 289919 := bstep (se 1 (by rfl) ⟨217439, by rfl⟩ : syracuseStep 289919 = 434879) B434879
theorem B915209 : Blo 283827 915209 := bstep (se 2 (by rfl) ⟨343203, by rfl⟩ : syracuseStep 915209 = 686407) B686407
theorem B1833185 : Blo 283827 1833185 := bstep (se 2 (by rfl) ⟨687444, by rfl⟩ : syracuseStep 1833185 = 1374889) B1374889
theorem B240056945 : Blo 283827 240056945 := bstep (se 2 (by rfl) ⟨90021354, by rfl⟩ : syracuseStep 240056945 = 180042709) B180042709
theorem B2162213 : Blo 283827 2162213 := bstep (se 4 (by rfl) ⟨202707, by rfl⟩ : syracuseStep 2162213 = 405415) B405415
theorem B426047 : Blo 283827 426047 := bstep (se 1 (by rfl) ⟨319535, by rfl⟩ : syracuseStep 426047 = 639071) B639071
theorem B2067869 : Blo 283827 2067869 := bstep (se 3 (by rfl) ⟨387725, by rfl⟩ : syracuseStep 2067869 = 775451) B775451
theorem B2594927 : Blo 283827 2594927 := bstep (se 1 (by rfl) ⟨1946195, by rfl⟩ : syracuseStep 2594927 = 3892391) B3892391
theorem B8920439 : Blo 283827 8920439 := bstep (se 1 (by rfl) ⟨6690329, by rfl⟩ : syracuseStep 8920439 = 13380659) B13380659
theorem B1222123 : Blo 283827 1222123 := bstep (se 1 (by rfl) ⟨916592, by rfl⟩ : syracuseStep 1222123 = 1833185) B1833185
theorem B1944449 : Blo 283827 1944449 := bstep (se 2 (by rfl) ⟨729168, by rfl⟩ : syracuseStep 1944449 = 1458337) B1458337
theorem B405119 : Blo 283827 405119 := bstep (se 1 (by rfl) ⟨303839, by rfl⟩ : syracuseStep 405119 = 607679) B607679
theorem B963467 : Blo 283827 963467 := bstep (se 1 (by rfl) ⟨722600, by rfl⟩ : syracuseStep 963467 = 1445201) B1445201
theorem B5586995 : Blo 283827 5586995 := bstep (se 1 (by rfl) ⟨4190246, by rfl⟩ : syracuseStep 5586995 = 8380493) B8380493
theorem B773117 : Blo 283827 773117 := bstep (se 3 (by rfl) ⟨144959, by rfl⟩ : syracuseStep 773117 = 289919) B289919
theorem B610139 : Blo 283827 610139 := bstep (se 1 (by rfl) ⟨457604, by rfl⟩ : syracuseStep 610139 = 915209) B915209
theorem B643391 : Blo 283827 643391 := bstep (se 1 (by rfl) ⟨482543, by rfl⟩ : syracuseStep 643391 = 965087) B965087
theorem B4642271 : Blo 283827 4642271 := bstep (se 1 (by rfl) ⟨3481703, by rfl⟩ : syracuseStep 4642271 = 6963407) B6963407
theorem B284583 : Blo 283827 284583 := bstep (se 1 (by rfl) ⟨213437, by rfl⟩ : syracuseStep 284583 = 426875) B426875
theorem B102029291 : Blo 283827 102029291 := bstep (se 1 (by rfl) ⟨76521968, by rfl⟩ : syracuseStep 102029291 = 153043937) B153043937
theorem B481531 : Blo 283827 481531 := bstep (se 1 (by rfl) ⟨361148, by rfl⟩ : syracuseStep 481531 = 722297) B722297
theorem B842483 : Blo 283827 842483 := bstep (se 1 (by rfl) ⟨631862, by rfl⟩ : syracuseStep 842483 = 1263725) B1263725
theorem B285695 : Blo 283827 285695 := bstep (se 1 (by rfl) ⟨214271, by rfl⟩ : syracuseStep 285695 = 428543) B428543
theorem B613993 : Blo 283827 613993 := bstep (se 2 (by rfl) ⟨230247, by rfl⟩ : syracuseStep 613993 = 460495) B460495
theorem B286719 : Blo 283827 286719 := bstep (se 1 (by rfl) ⟨215039, by rfl⟩ : syracuseStep 286719 = 430079) B430079
theorem B287039 : Blo 283827 287039 := bstep (se 1 (by rfl) ⟨215279, by rfl⟩ : syracuseStep 287039 = 430559) B430559
theorem B287199 : Blo 283827 287199 := bstep (se 1 (by rfl) ⟨215399, by rfl⟩ : syracuseStep 287199 = 430799) B430799
theorem B7563091 : Blo 283827 7563091 := bstep (se 1 (by rfl) ⟨5672318, by rfl⟩ : syracuseStep 7563091 = 11344637) B11344637
theorem B160037963 : Blo 283827 160037963 := bstep (se 1 (by rfl) ⟨120028472, by rfl⟩ : syracuseStep 160037963 = 240056945) B240056945
theorem B1441475 : Blo 283827 1441475 := bstep (se 1 (by rfl) ⟨1081106, by rfl⟩ : syracuseStep 1441475 = 2162213) B2162213
theorem B428927 : Blo 283827 428927 := bstep (se 1 (by rfl) ⟨321695, by rfl⟩ : syracuseStep 428927 = 643391) B643391
theorem B561655 : Blo 283827 561655 := bstep (se 1 (by rfl) ⟨421241, by rfl⟩ : syracuseStep 561655 = 842483) B842483
theorem B6919805 : Blo 283827 6919805 := bstep (se 3 (by rfl) ⟨1297463, by rfl⟩ : syracuseStep 6919805 = 2594927) B2594927
theorem B5514317 : Blo 283827 5514317 := bstep (se 3 (by rfl) ⟨1033934, by rfl⟩ : syracuseStep 5514317 = 2067869) B2067869
theorem B960983 : Blo 283827 960983 := bstep (se 1 (by rfl) ⟨720737, by rfl⟩ : syracuseStep 960983 = 1441475) B1441475
theorem B3094847 : Blo 283827 3094847 := bstep (se 1 (by rfl) ⟨2321135, by rfl⟩ : syracuseStep 3094847 = 4642271) B4642271
theorem B5946959 : Blo 283827 5946959 := bstep (se 1 (by rfl) ⟨4460219, by rfl⟩ : syracuseStep 5946959 = 8920439) B8920439
theorem B1296299 : Blo 283827 1296299 := bstep (se 1 (by rfl) ⟨972224, by rfl⟩ : syracuseStep 1296299 = 1944449) B1944449
theorem B642041 : Blo 283827 642041 := bstep (se 2 (by rfl) ⟨240765, by rfl⟩ : syracuseStep 642041 = 481531) B481531
theorem B642311 : Blo 283827 642311 := bstep (se 1 (by rfl) ⟨481733, by rfl⟩ : syracuseStep 642311 = 963467) B963467
theorem B1627037 : Blo 283827 1627037 := bstep (se 3 (by rfl) ⟨305069, by rfl⟩ : syracuseStep 1627037 = 610139) B610139
theorem B3724663 : Blo 283827 3724663 := bstep (se 1 (by rfl) ⟨2793497, by rfl⟩ : syracuseStep 3724663 = 5586995) B5586995
theorem B284031 : Blo 283827 284031 := bstep (se 1 (by rfl) ⟨213023, by rfl⟩ : syracuseStep 284031 = 426047) B426047
theorem B1629497 : Blo 283827 1629497 := bstep (se 2 (by rfl) ⟨611061, by rfl⟩ : syracuseStep 1629497 = 1222123) B1222123
theorem B515411 : Blo 283827 515411 := bstep (se 1 (by rfl) ⟨386558, by rfl⟩ : syracuseStep 515411 = 773117) B773117
theorem B10084121 : Blo 283827 10084121 := bstep (se 2 (by rfl) ⟨3781545, by rfl⟩ : syracuseStep 10084121 = 7563091) B7563091
theorem B68019527 : Blo 283827 68019527 := bstep (se 1 (by rfl) ⟨51014645, by rfl⟩ : syracuseStep 68019527 = 102029291) B102029291
theorem B1080317 : Blo 283827 1080317 := bstep (se 3 (by rfl) ⟨202559, by rfl⟩ : syracuseStep 1080317 = 405119) B405119
theorem B106691975 : Blo 283827 106691975 := bstep (se 1 (by rfl) ⟨80018981, by rfl⟩ : syracuseStep 106691975 = 160037963) B160037963
theorem B818657 : Blo 283827 818657 := bstep (se 2 (by rfl) ⟨306996, by rfl⟩ : syracuseStep 818657 = 613993) B613993
theorem B428027 : Blo 283827 428027 := bstep (se 1 (by rfl) ⟨321020, by rfl⟩ : syracuseStep 428027 = 642041) B642041
theorem B428207 : Blo 283827 428207 := bstep (se 1 (by rfl) ⟨321155, by rfl⟩ : syracuseStep 428207 = 642311) B642311
theorem B1084691 : Blo 283827 1084691 := bstep (se 1 (by rfl) ⟨813518, by rfl⟩ : syracuseStep 1084691 = 1627037) B1627037
theorem B1086331 : Blo 283827 1086331 := bstep (se 1 (by rfl) ⟨814748, by rfl⟩ : syracuseStep 1086331 = 1629497) B1629497
theorem B6722747 : Blo 283827 6722747 := bstep (se 1 (by rfl) ⟨5042060, by rfl⟩ : syracuseStep 6722747 = 10084121) B10084121
theorem B3676211 : Blo 283827 3676211 := bstep (se 1 (by rfl) ⟨2757158, by rfl⟩ : syracuseStep 3676211 = 5514317) B5514317
theorem B864199 : Blo 283827 864199 := bstep (se 1 (by rfl) ⟨648149, by rfl⟩ : syracuseStep 864199 = 1296299) B1296299
theorem B343607 : Blo 283827 343607 := bstep (se 1 (by rfl) ⟨257705, by rfl⟩ : syracuseStep 343607 = 515411) B515411
theorem B640655 : Blo 283827 640655 := bstep (se 1 (by rfl) ⟨480491, by rfl⟩ : syracuseStep 640655 = 960983) B960983
theorem B4966217 : Blo 283827 4966217 := bstep (se 2 (by rfl) ⟨1862331, by rfl⟩ : syracuseStep 4966217 = 3724663) B3724663
theorem B71127983 : Blo 283827 71127983 := bstep (se 1 (by rfl) ⟨53345987, by rfl⟩ : syracuseStep 71127983 = 106691975) B106691975
theorem B545771 : Blo 283827 545771 := bstep (se 1 (by rfl) ⟨409328, by rfl⟩ : syracuseStep 545771 = 818657) B818657
theorem B285951 : Blo 283827 285951 := bstep (se 1 (by rfl) ⟨214463, by rfl⟩ : syracuseStep 285951 = 428927) B428927
theorem B4613203 : Blo 283827 4613203 := bstep (se 1 (by rfl) ⟨3459902, by rfl⟩ : syracuseStep 4613203 = 6919805) B6919805
theorem B748873 : Blo 283827 748873 := bstep (se 2 (by rfl) ⟨280827, by rfl⟩ : syracuseStep 748873 = 561655) B561655
theorem B45346351 : Blo 283827 45346351 := bstep (se 1 (by rfl) ⟨34009763, by rfl⟩ : syracuseStep 45346351 = 68019527) B68019527
theorem B2063231 : Blo 283827 2063231 := bstep (se 1 (by rfl) ⟨1547423, by rfl⟩ : syracuseStep 2063231 = 3094847) B3094847
theorem B720211 : Blo 283827 720211 := bstep (se 1 (by rfl) ⟨540158, by rfl⟩ : syracuseStep 720211 = 1080317) B1080317
theorem B3964639 : Blo 283827 3964639 := bstep (se 1 (by rfl) ⟨2973479, by rfl⟩ : syracuseStep 3964639 = 5946959) B5946959
theorem B427103 : Blo 283827 427103 := bstep (se 1 (by rfl) ⟨320327, by rfl⟩ : syracuseStep 427103 = 640655) B640655
theorem B3310811 : Blo 283827 3310811 := bstep (se 1 (by rfl) ⟨2483108, by rfl⟩ : syracuseStep 3310811 = 4966217) B4966217
theorem B723127 : Blo 283827 723127 := bstep (se 1 (by rfl) ⟨542345, by rfl⟩ : syracuseStep 723127 = 1084691) B1084691
theorem B47418655 : Blo 283827 47418655 := bstep (se 1 (by rfl) ⟨35563991, by rfl⟩ : syracuseStep 47418655 = 71127983) B71127983
theorem B363847 : Blo 283827 363847 := bstep (se 1 (by rfl) ⟨272885, by rfl⟩ : syracuseStep 363847 = 545771) B545771
theorem B60461801 : Blo 283827 60461801 := bstep (se 2 (by rfl) ⟨22673175, by rfl⟩ : syracuseStep 60461801 = 45346351) B45346351
theorem B1152265 : Blo 283827 1152265 := bstep (se 2 (by rfl) ⟨432099, by rfl⟩ : syracuseStep 1152265 = 864199) B864199
theorem B1448441 : Blo 283827 1448441 := bstep (se 2 (by rfl) ⟨543165, by rfl⟩ : syracuseStep 1448441 = 1086331) B1086331
theorem B960281 : Blo 283827 960281 := bstep (se 2 (by rfl) ⟨360105, by rfl⟩ : syracuseStep 960281 = 720211) B720211
theorem B5286185 : Blo 283827 5286185 := bstep (se 2 (by rfl) ⟨1982319, by rfl⟩ : syracuseStep 5286185 = 3964639) B3964639
theorem B998497 : Blo 283827 998497 := bstep (se 2 (by rfl) ⟨374436, by rfl⟩ : syracuseStep 998497 = 748873) B748873
theorem B285351 : Blo 283827 285351 := bstep (se 1 (by rfl) ⟨214013, by rfl⟩ : syracuseStep 285351 = 428027) B428027
theorem B6150937 : Blo 283827 6150937 := bstep (se 2 (by rfl) ⟨2306601, by rfl⟩ : syracuseStep 6150937 = 4613203) B4613203
theorem B285471 : Blo 283827 285471 := bstep (se 1 (by rfl) ⟨214103, by rfl⟩ : syracuseStep 285471 = 428207) B428207
theorem B4481831 : Blo 283827 4481831 := bstep (se 1 (by rfl) ⟨3361373, by rfl⟩ : syracuseStep 4481831 = 6722747) B6722747
theorem B2450807 : Blo 283827 2450807 := bstep (se 1 (by rfl) ⟨1838105, by rfl⟩ : syracuseStep 2450807 = 3676211) B3676211
theorem B916285 : Blo 283827 916285 := bstep (se 3 (by rfl) ⟨171803, by rfl⟩ : syracuseStep 916285 = 343607) B343607
theorem B1375487 : Blo 283827 1375487 := bstep (se 1 (by rfl) ⟨1031615, by rfl⟩ : syracuseStep 1375487 = 2063231) B2063231
theorem B40307867 : Blo 283827 40307867 := bstep (se 1 (by rfl) ⟨30230900, by rfl⟩ : syracuseStep 40307867 = 60461801) B60461801
theorem B2987887 : Blo 283827 2987887 := bstep (se 1 (by rfl) ⟨2240915, by rfl⟩ : syracuseStep 2987887 = 4481831) B4481831
theorem B8201249 : Blo 283827 8201249 := bstep (se 2 (by rfl) ⟨3075468, by rfl⟩ : syracuseStep 8201249 = 6150937) B6150937
theorem B1221713 : Blo 283827 1221713 := bstep (se 2 (by rfl) ⟨458142, by rfl⟩ : syracuseStep 1221713 = 916285) B916285
theorem B2207207 : Blo 283827 2207207 := bstep (se 1 (by rfl) ⟨1655405, by rfl⟩ : syracuseStep 2207207 = 3310811) B3310811
theorem B964169 : Blo 283827 964169 := bstep (se 2 (by rfl) ⟨361563, by rfl⟩ : syracuseStep 964169 = 723127) B723127
theorem B965627 : Blo 283827 965627 := bstep (se 1 (by rfl) ⟨724220, by rfl⟩ : syracuseStep 965627 = 1448441) B1448441
theorem B63224873 : Blo 283827 63224873 := bstep (se 2 (by rfl) ⟨23709327, by rfl⟩ : syracuseStep 63224873 = 47418655) B47418655
theorem B640187 : Blo 283827 640187 := bstep (se 1 (by rfl) ⟨480140, by rfl⟩ : syracuseStep 640187 = 960281) B960281
theorem B3524123 : Blo 283827 3524123 := bstep (se 1 (by rfl) ⟨2643092, by rfl⟩ : syracuseStep 3524123 = 5286185) B5286185
theorem B1331329 : Blo 283827 1331329 := bstep (se 2 (by rfl) ⟨499248, by rfl⟩ : syracuseStep 1331329 = 998497) B998497
theorem B284735 : Blo 283827 284735 := bstep (se 1 (by rfl) ⟨213551, by rfl⟩ : syracuseStep 284735 = 427103) B427103
theorem B485129 : Blo 283827 485129 := bstep (se 2 (by rfl) ⟨181923, by rfl⟩ : syracuseStep 485129 = 363847) B363847
theorem B1633871 : Blo 283827 1633871 := bstep (se 1 (by rfl) ⟨1225403, by rfl⟩ : syracuseStep 1633871 = 2450807) B2450807
theorem B1536353 : Blo 283827 1536353 := bstep (se 2 (by rfl) ⟨576132, by rfl⟩ : syracuseStep 1536353 = 1152265) B1152265
theorem B916991 : Blo 283827 916991 := bstep (se 1 (by rfl) ⟨687743, by rfl⟩ : syracuseStep 916991 = 1375487) B1375487
theorem B426791 : Blo 283827 426791 := bstep (se 1 (by rfl) ⟨320093, by rfl⟩ : syracuseStep 426791 = 640187) B640187
theorem B26871911 : Blo 283827 26871911 := bstep (se 1 (by rfl) ⟨20153933, by rfl⟩ : syracuseStep 26871911 = 40307867) B40307867
theorem B1775105 : Blo 283827 1775105 := bstep (se 2 (by rfl) ⟨665664, by rfl⟩ : syracuseStep 1775105 = 1331329) B1331329
theorem B1089247 : Blo 283827 1089247 := bstep (se 1 (by rfl) ⟨816935, by rfl⟩ : syracuseStep 1089247 = 1633871) B1633871
theorem B1024235 : Blo 283827 1024235 := bstep (se 1 (by rfl) ⟨768176, by rfl⟩ : syracuseStep 1024235 = 1536353) B1536353
theorem B42149915 : Blo 283827 42149915 := bstep (se 1 (by rfl) ⟨31612436, by rfl⟩ : syracuseStep 42149915 = 63224873) B63224873
theorem B3983849 : Blo 283827 3983849 := bstep (se 2 (by rfl) ⟨1493943, by rfl⟩ : syracuseStep 3983849 = 2987887) B2987887
theorem B642779 : Blo 283827 642779 := bstep (se 1 (by rfl) ⟨482084, by rfl⟩ : syracuseStep 642779 = 964169) B964169
theorem B5885885 : Blo 283827 5885885 := bstep (se 3 (by rfl) ⟨1103603, by rfl⟩ : syracuseStep 5885885 = 2207207) B2207207
theorem B643751 : Blo 283827 643751 := bstep (se 1 (by rfl) ⟨482813, by rfl⟩ : syracuseStep 643751 = 965627) B965627
theorem B611327 : Blo 283827 611327 := bstep (se 1 (by rfl) ⟨458495, by rfl⟩ : syracuseStep 611327 = 916991) B916991
theorem B2349415 : Blo 283827 2349415 := bstep (se 1 (by rfl) ⟨1762061, by rfl⟩ : syracuseStep 2349415 = 3524123) B3524123
theorem B5467499 : Blo 283827 5467499 := bstep (se 1 (by rfl) ⟨4100624, by rfl⟩ : syracuseStep 5467499 = 8201249) B8201249
theorem B814475 : Blo 283827 814475 := bstep (se 1 (by rfl) ⟨610856, by rfl⟩ : syracuseStep 814475 = 1221713) B1221713
theorem B323419 : Blo 283827 323419 := bstep (se 1 (by rfl) ⟨242564, by rfl⟩ : syracuseStep 323419 = 485129) B485129
theorem B2655899 : Blo 283827 2655899 := bstep (se 1 (by rfl) ⟨1991924, by rfl⟩ : syracuseStep 2655899 = 3983849) B3983849
theorem B428519 : Blo 283827 428519 := bstep (se 1 (by rfl) ⟨321389, by rfl⟩ : syracuseStep 428519 = 642779) B642779
theorem B429167 : Blo 283827 429167 := bstep (se 1 (by rfl) ⟨321875, by rfl⟩ : syracuseStep 429167 = 643751) B643751
theorem B1183403 : Blo 283827 1183403 := bstep (se 1 (by rfl) ⟨887552, by rfl⟩ : syracuseStep 1183403 = 1775105) B1775105
theorem B431225 : Blo 283827 431225 := bstep (se 2 (by rfl) ⟨161709, by rfl⟩ : syracuseStep 431225 = 323419) B323419
theorem B3644999 : Blo 283827 3644999 := bstep (se 1 (by rfl) ⟨2733749, by rfl⟩ : syracuseStep 3644999 = 5467499) B5467499
theorem B2171933 : Blo 283827 2171933 := bstep (se 3 (by rfl) ⟨407237, by rfl⟩ : syracuseStep 2171933 = 814475) B814475
theorem B1452329 : Blo 283827 1452329 := bstep (se 2 (by rfl) ⟨544623, by rfl⟩ : syracuseStep 1452329 = 1089247) B1089247
theorem B12530213 : Blo 283827 12530213 := bstep (se 4 (by rfl) ⟨1174707, by rfl⟩ : syracuseStep 12530213 = 2349415) B2349415
theorem B28099943 : Blo 283827 28099943 := bstep (se 1 (by rfl) ⟨21074957, by rfl⟩ : syracuseStep 28099943 = 42149915) B42149915
theorem B284527 : Blo 283827 284527 := bstep (se 1 (by rfl) ⟨213395, by rfl⟩ : syracuseStep 284527 = 426791) B426791
theorem B17914607 : Blo 283827 17914607 := bstep (se 1 (by rfl) ⟨13435955, by rfl⟩ : syracuseStep 17914607 = 26871911) B26871911
theorem B3923923 : Blo 283827 3923923 := bstep (se 1 (by rfl) ⟨2942942, by rfl⟩ : syracuseStep 3923923 = 5885885) B5885885
theorem B1630205 : Blo 283827 1630205 := bstep (se 3 (by rfl) ⟨305663, by rfl⟩ : syracuseStep 1630205 = 611327) B611327
theorem B682823 : Blo 283827 682823 := bstep (se 1 (by rfl) ⟨512117, by rfl⟩ : syracuseStep 682823 = 1024235) B1024235
theorem B1770599 : Blo 283827 1770599 := bstep (se 1 (by rfl) ⟨1327949, by rfl⟩ : syracuseStep 1770599 = 2655899) B2655899
theorem B788935 : Blo 283827 788935 := bstep (se 1 (by rfl) ⟨591701, by rfl⟩ : syracuseStep 788935 = 1183403) B1183403
theorem B2429999 : Blo 283827 2429999 := bstep (se 1 (by rfl) ⟨1822499, by rfl⟩ : syracuseStep 2429999 = 3644999) B3644999
theorem B1086803 : Blo 283827 1086803 := bstep (se 1 (by rfl) ⟨815102, by rfl⟩ : syracuseStep 1086803 = 1630205) B1630205
theorem B1447955 : Blo 283827 1447955 := bstep (se 1 (by rfl) ⟨1085966, by rfl⟩ : syracuseStep 1447955 = 2171933) B2171933
theorem B11943071 : Blo 283827 11943071 := bstep (se 1 (by rfl) ⟨8957303, by rfl⟩ : syracuseStep 11943071 = 17914607) B17914607
theorem B968219 : Blo 283827 968219 := bstep (se 1 (by rfl) ⟨726164, by rfl⟩ : syracuseStep 968219 = 1452329) B1452329
theorem B5231897 : Blo 283827 5231897 := bstep (se 2 (by rfl) ⟨1961961, by rfl⟩ : syracuseStep 5231897 = 3923923) B3923923
theorem B18733295 : Blo 283827 18733295 := bstep (se 1 (by rfl) ⟨14049971, by rfl⟩ : syracuseStep 18733295 = 28099943) B28099943
theorem B285679 : Blo 283827 285679 := bstep (se 1 (by rfl) ⟨214259, by rfl⟩ : syracuseStep 285679 = 428519) B428519
theorem B286111 : Blo 283827 286111 := bstep (se 1 (by rfl) ⟨214583, by rfl⟩ : syracuseStep 286111 = 429167) B429167
theorem B287483 : Blo 283827 287483 := bstep (se 1 (by rfl) ⟨215612, by rfl⟩ : syracuseStep 287483 = 431225) B431225
theorem B455215 : Blo 283827 455215 := bstep (se 1 (by rfl) ⟨341411, by rfl⟩ : syracuseStep 455215 = 682823) B682823
theorem B8353475 : Blo 283827 8353475 := bstep (se 1 (by rfl) ⟨6265106, by rfl⟩ : syracuseStep 8353475 = 12530213) B12530213
theorem B4721597 : Blo 283827 4721597 := bstep (se 3 (by rfl) ⟨885299, by rfl⟩ : syracuseStep 4721597 = 1770599) B1770599
theorem B1051913 : Blo 283827 1051913 := bstep (se 2 (by rfl) ⟨394467, by rfl⟩ : syracuseStep 1051913 = 788935) B788935
theorem B724535 : Blo 283827 724535 := bstep (se 1 (by rfl) ⟨543401, by rfl⟩ : syracuseStep 724535 = 1086803) B1086803
theorem B1619999 : Blo 283827 1619999 := bstep (se 1 (by rfl) ⟨1214999, by rfl⟩ : syracuseStep 1619999 = 2429999) B2429999
theorem B3487931 : Blo 283827 3487931 := bstep (se 1 (by rfl) ⟨2615948, by rfl⟩ : syracuseStep 3487931 = 5231897) B5231897
theorem B965303 : Blo 283827 965303 := bstep (se 1 (by rfl) ⟨723977, by rfl⟩ : syracuseStep 965303 = 1447955) B1447955
theorem B49955453 : Blo 283827 49955453 := bstep (se 3 (by rfl) ⟨9366647, by rfl⟩ : syracuseStep 49955453 = 18733295) B18733295
theorem B606953 : Blo 283827 606953 := bstep (se 2 (by rfl) ⟨227607, by rfl⟩ : syracuseStep 606953 = 455215) B455215
theorem B645479 : Blo 283827 645479 := bstep (se 1 (by rfl) ⟨484109, by rfl⟩ : syracuseStep 645479 = 968219) B968219
theorem B5568983 : Blo 283827 5568983 := bstep (se 1 (by rfl) ⟨4176737, by rfl⟩ : syracuseStep 5568983 = 8353475) B8353475
theorem B7962047 : Blo 283827 7962047 := bstep (se 1 (by rfl) ⟨5971535, by rfl⟩ : syracuseStep 7962047 = 11943071) B11943071
theorem B3147731 : Blo 283827 3147731 := bstep (se 1 (by rfl) ⟨2360798, by rfl⟩ : syracuseStep 3147731 = 4721597) B4721597
theorem B430319 : Blo 283827 430319 := bstep (se 1 (by rfl) ⟨322739, by rfl⟩ : syracuseStep 430319 = 645479) B645479
theorem B3712655 : Blo 283827 3712655 := bstep (se 1 (by rfl) ⟨2784491, by rfl⟩ : syracuseStep 3712655 = 5568983) B5568983
theorem B33303635 : Blo 283827 33303635 := bstep (se 1 (by rfl) ⟨24977726, by rfl⟩ : syracuseStep 33303635 = 49955453) B49955453
theorem B1618541 : Blo 283827 1618541 := bstep (se 3 (by rfl) ⟨303476, by rfl⟩ : syracuseStep 1618541 = 606953) B606953
theorem B2805101 : Blo 283827 2805101 := bstep (se 3 (by rfl) ⟨525956, by rfl⟩ : syracuseStep 2805101 = 1051913) B1051913
theorem B643535 : Blo 283827 643535 := bstep (se 1 (by rfl) ⟨482651, by rfl⟩ : syracuseStep 643535 = 965303) B965303
theorem B483023 : Blo 283827 483023 := bstep (se 1 (by rfl) ⟨362267, by rfl⟩ : syracuseStep 483023 = 724535) B724535
theorem B1079999 : Blo 283827 1079999 := bstep (se 1 (by rfl) ⟨809999, by rfl⟩ : syracuseStep 1079999 = 1619999) B1619999
theorem B2325287 : Blo 283827 2325287 := bstep (se 1 (by rfl) ⟨1743965, by rfl⟩ : syracuseStep 2325287 = 3487931) B3487931
theorem B5308031 : Blo 283827 5308031 := bstep (se 1 (by rfl) ⟨3981023, by rfl⟩ : syracuseStep 5308031 = 7962047) B7962047
theorem B2098487 : Blo 283827 2098487 := bstep (se 1 (by rfl) ⟨1573865, by rfl⟩ : syracuseStep 2098487 = 3147731) B3147731
theorem B1870067 : Blo 283827 1870067 := bstep (se 1 (by rfl) ⟨1402550, by rfl⟩ : syracuseStep 1870067 = 2805101) B2805101
theorem B429023 : Blo 283827 429023 := bstep (se 1 (by rfl) ⟨321767, by rfl⟩ : syracuseStep 429023 = 643535) B643535
theorem B9900413 : Blo 283827 9900413 := bstep (se 3 (by rfl) ⟨1856327, by rfl⟩ : syracuseStep 9900413 = 3712655) B3712655
theorem B1550191 : Blo 283827 1550191 := bstep (se 1 (by rfl) ⟨1162643, by rfl⟩ : syracuseStep 1550191 = 2325287) B2325287
theorem B22202423 : Blo 283827 22202423 := bstep (se 1 (by rfl) ⟨16651817, by rfl⟩ : syracuseStep 22202423 = 33303635) B33303635
theorem B286879 : Blo 283827 286879 := bstep (se 1 (by rfl) ⟨215159, by rfl⟩ : syracuseStep 286879 = 430319) B430319
theorem B322015 : Blo 283827 322015 := bstep (se 1 (by rfl) ⟨241511, by rfl⟩ : syracuseStep 322015 = 483023) B483023
theorem B1079027 : Blo 283827 1079027 := bstep (se 1 (by rfl) ⟨809270, by rfl⟩ : syracuseStep 1079027 = 1618541) B1618541
theorem B719999 : Blo 283827 719999 := bstep (se 1 (by rfl) ⟨539999, by rfl⟩ : syracuseStep 719999 = 1079999) B1079999
theorem B3538687 : Blo 283827 3538687 := bstep (se 1 (by rfl) ⟨2654015, by rfl⟩ : syracuseStep 3538687 = 5308031) B5308031
theorem B2066921 : Blo 283827 2066921 := bstep (se 2 (by rfl) ⟨775095, by rfl⟩ : syracuseStep 2066921 = 1550191) B1550191
theorem B429353 : Blo 283827 429353 := bstep (se 2 (by rfl) ⟨161007, by rfl⟩ : syracuseStep 429353 = 322015) B322015
theorem B4986845 : Blo 283827 4986845 := bstep (se 3 (by rfl) ⟨935033, by rfl⟩ : syracuseStep 4986845 = 1870067) B1870067
theorem B6600275 : Blo 283827 6600275 := bstep (se 1 (by rfl) ⟨4950206, by rfl⟩ : syracuseStep 6600275 = 9900413) B9900413
theorem B479999 : Blo 283827 479999 := bstep (se 1 (by rfl) ⟨359999, by rfl⟩ : syracuseStep 479999 = 719999) B719999
theorem B14801615 : Blo 283827 14801615 := bstep (se 1 (by rfl) ⟨11101211, by rfl⟩ : syracuseStep 14801615 = 22202423) B22202423
theorem B286015 : Blo 283827 286015 := bstep (se 1 (by rfl) ⟨214511, by rfl⟩ : syracuseStep 286015 = 429023) B429023
theorem B5595965 : Blo 283827 5595965 := bstep (se 3 (by rfl) ⟨1049243, by rfl⟩ : syracuseStep 5595965 = 2098487) B2098487
theorem B719351 : Blo 283827 719351 := bstep (se 1 (by rfl) ⟨539513, by rfl⟩ : syracuseStep 719351 = 1079027) B1079027
theorem B4718249 : Blo 283827 4718249 := bstep (se 2 (by rfl) ⟨1769343, by rfl⟩ : syracuseStep 4718249 = 3538687) B3538687
theorem B1377947 : Blo 283827 1377947 := bstep (se 1 (by rfl) ⟨1033460, by rfl⟩ : syracuseStep 1377947 = 2066921) B2066921
theorem B9867743 : Blo 283827 9867743 := bstep (se 1 (by rfl) ⟨7400807, by rfl⟩ : syracuseStep 9867743 = 14801615) B14801615
theorem B4400183 : Blo 283827 4400183 := bstep (se 1 (by rfl) ⟨3300137, by rfl⟩ : syracuseStep 4400183 = 6600275) B6600275
theorem B3324563 : Blo 283827 3324563 := bstep (se 1 (by rfl) ⟨2493422, by rfl⟩ : syracuseStep 3324563 = 4986845) B4986845
theorem B479567 : Blo 283827 479567 := bstep (se 1 (by rfl) ⟨359675, by rfl⟩ : syracuseStep 479567 = 719351) B719351
theorem B286235 : Blo 283827 286235 := bstep (se 1 (by rfl) ⟨214676, by rfl⟩ : syracuseStep 286235 = 429353) B429353
theorem B319999 : Blo 283827 319999 := bstep (se 1 (by rfl) ⟨239999, by rfl⟩ : syracuseStep 319999 = 479999) B479999
theorem B3730643 : Blo 283827 3730643 := bstep (se 1 (by rfl) ⟨2797982, by rfl⟩ : syracuseStep 3730643 = 5595965) B5595965
theorem B3145499 : Blo 283827 3145499 := bstep (se 1 (by rfl) ⟨2359124, by rfl⟩ : syracuseStep 3145499 = 4718249) B4718249
theorem B426665 : Blo 283827 426665 := bstep (se 2 (by rfl) ⟨159999, by rfl⟩ : syracuseStep 426665 = 319999) B319999
theorem B918631 : Blo 283827 918631 := bstep (se 1 (by rfl) ⟨688973, by rfl⟩ : syracuseStep 918631 = 1377947) B1377947
theorem B2933455 : Blo 283827 2933455 := bstep (se 1 (by rfl) ⟨2200091, by rfl⟩ : syracuseStep 2933455 = 4400183) B4400183
theorem B2216375 : Blo 283827 2216375 := bstep (se 1 (by rfl) ⟨1662281, by rfl⟩ : syracuseStep 2216375 = 3324563) B3324563
theorem B319711 : Blo 283827 319711 := bstep (se 1 (by rfl) ⟨239783, by rfl⟩ : syracuseStep 319711 = 479567) B479567
theorem B6578495 : Blo 283827 6578495 := bstep (se 1 (by rfl) ⟨4933871, by rfl⟩ : syracuseStep 6578495 = 9867743) B9867743
theorem B2487095 : Blo 283827 2487095 := bstep (se 1 (by rfl) ⟨1865321, by rfl⟩ : syracuseStep 2487095 = 3730643) B3730643
theorem B2096999 : Blo 283827 2096999 := bstep (se 1 (by rfl) ⟨1572749, by rfl⟩ : syracuseStep 2096999 = 3145499) B3145499
theorem B426281 : Blo 283827 426281 := bstep (se 2 (by rfl) ⟨159855, by rfl⟩ : syracuseStep 426281 = 319711) B319711
theorem B3911273 : Blo 283827 3911273 := bstep (se 2 (by rfl) ⟨1466727, by rfl⟩ : syracuseStep 3911273 = 2933455) B2933455
theorem B1224841 : Blo 283827 1224841 := bstep (se 2 (by rfl) ⟨459315, by rfl⟩ : syracuseStep 1224841 = 918631) B918631
theorem B1658063 : Blo 283827 1658063 := bstep (se 1 (by rfl) ⟨1243547, by rfl⟩ : syracuseStep 1658063 = 2487095) B2487095
theorem B1397999 : Blo 283827 1397999 := bstep (se 1 (by rfl) ⟨1048499, by rfl⟩ : syracuseStep 1397999 = 2096999) B2096999
theorem B284443 : Blo 283827 284443 := bstep (se 1 (by rfl) ⟨213332, by rfl⟩ : syracuseStep 284443 = 426665) B426665
theorem B4385663 : Blo 283827 4385663 := bstep (se 1 (by rfl) ⟨3289247, by rfl⟩ : syracuseStep 4385663 = 6578495) B6578495
theorem B94565333 : Blo 283827 94565333 := bstep (se 7 (by rfl) ⟨1108187, by rfl⟩ : syracuseStep 94565333 = 2216375) B2216375
theorem B2923775 : Blo 283827 2923775 := bstep (se 1 (by rfl) ⟨2192831, by rfl⟩ : syracuseStep 2923775 = 4385663) B4385663
theorem B931999 : Blo 283827 931999 := bstep (se 1 (by rfl) ⟨698999, by rfl⟩ : syracuseStep 931999 = 1397999) B1397999
theorem B2607515 : Blo 283827 2607515 := bstep (se 1 (by rfl) ⟨1955636, by rfl⟩ : syracuseStep 2607515 = 3911273) B3911273
theorem B284187 : Blo 283827 284187 := bstep (se 1 (by rfl) ⟨213140, by rfl⟩ : syracuseStep 284187 = 426281) B426281
theorem B1105375 : Blo 283827 1105375 := bstep (se 1 (by rfl) ⟨829031, by rfl⟩ : syracuseStep 1105375 = 1658063) B1658063
theorem B252174221 : Blo 283827 252174221 := bstep (se 3 (by rfl) ⟨47282666, by rfl⟩ : syracuseStep 252174221 = 94565333) B94565333
theorem B1633121 : Blo 283827 1633121 := bstep (se 2 (by rfl) ⟨612420, by rfl⟩ : syracuseStep 1633121 = 1224841) B1224841
theorem B1738343 : Blo 283827 1738343 := bstep (se 1 (by rfl) ⟨1303757, by rfl⟩ : syracuseStep 1738343 = 2607515) B2607515
theorem B1088747 : Blo 283827 1088747 := bstep (se 1 (by rfl) ⟨816560, by rfl⟩ : syracuseStep 1088747 = 1633121) B1633121
theorem B1949183 : Blo 283827 1949183 := bstep (se 1 (by rfl) ⟨1461887, by rfl⟩ : syracuseStep 1949183 = 2923775) B2923775
theorem B168116147 : Blo 283827 168116147 := bstep (se 1 (by rfl) ⟨126087110, by rfl⟩ : syracuseStep 168116147 = 252174221) B252174221
theorem B1242665 : Blo 283827 1242665 := bstep (se 2 (by rfl) ⟨465999, by rfl⟩ : syracuseStep 1242665 = 931999) B931999
theorem B1473833 : Blo 283827 1473833 := bstep (se 2 (by rfl) ⟨552687, by rfl⟩ : syracuseStep 1473833 = 1105375) B1105375
theorem B725831 : Blo 283827 725831 := bstep (se 1 (by rfl) ⟨544373, by rfl⟩ : syracuseStep 725831 = 1088747) B1088747
theorem B828443 : Blo 283827 828443 := bstep (se 1 (by rfl) ⟨621332, by rfl⟩ : syracuseStep 828443 = 1242665) B1242665
theorem B112077431 : Blo 283827 112077431 := bstep (se 1 (by rfl) ⟨84058073, by rfl⟩ : syracuseStep 112077431 = 168116147) B168116147
theorem B1158895 : Blo 283827 1158895 := bstep (se 1 (by rfl) ⟨869171, by rfl⟩ : syracuseStep 1158895 = 1738343) B1738343
theorem B1299455 : Blo 283827 1299455 := bstep (se 1 (by rfl) ⟨974591, by rfl⟩ : syracuseStep 1299455 = 1949183) B1949183
theorem B3930221 : Blo 283827 3930221 := bstep (se 3 (by rfl) ⟨736916, by rfl⟩ : syracuseStep 3930221 = 1473833) B1473833
theorem B1545193 : Blo 283827 1545193 := bstep (se 2 (by rfl) ⟨579447, by rfl⟩ : syracuseStep 1545193 = 1158895) B1158895
theorem B74718287 : Blo 283827 74718287 := bstep (se 1 (by rfl) ⟨56038715, by rfl⟩ : syracuseStep 74718287 = 112077431) B112077431
theorem B866303 : Blo 283827 866303 := bstep (se 1 (by rfl) ⟨649727, by rfl⟩ : syracuseStep 866303 = 1299455) B1299455
theorem B483887 : Blo 283827 483887 := bstep (se 1 (by rfl) ⟨362915, by rfl⟩ : syracuseStep 483887 = 725831) B725831
theorem B552295 : Blo 283827 552295 := bstep (se 1 (by rfl) ⟨414221, by rfl⟩ : syracuseStep 552295 = 828443) B828443
theorem B2620147 : Blo 283827 2620147 := bstep (se 1 (by rfl) ⟨1965110, by rfl⟩ : syracuseStep 2620147 = 3930221) B3930221
theorem B49812191 : Blo 283827 49812191 := bstep (se 1 (by rfl) ⟨37359143, by rfl⟩ : syracuseStep 49812191 = 74718287) B74718287
theorem B736393 : Blo 283827 736393 := bstep (se 2 (by rfl) ⟨276147, by rfl⟩ : syracuseStep 736393 = 552295) B552295
theorem B3493529 : Blo 283827 3493529 := bstep (se 2 (by rfl) ⟨1310073, by rfl⟩ : syracuseStep 3493529 = 2620147) B2620147
theorem B577535 : Blo 283827 577535 := bstep (se 1 (by rfl) ⟨433151, by rfl⟩ : syracuseStep 577535 = 866303) B866303
theorem B322591 : Blo 283827 322591 := bstep (se 1 (by rfl) ⟨241943, by rfl⟩ : syracuseStep 322591 = 483887) B483887
theorem B2060257 : Blo 283827 2060257 := bstep (se 2 (by rfl) ⟨772596, by rfl⟩ : syracuseStep 2060257 = 1545193) B1545193
theorem B2329019 : Blo 283827 2329019 := bstep (se 1 (by rfl) ⟨1746764, by rfl⟩ : syracuseStep 2329019 = 3493529) B3493529
theorem B430121 : Blo 283827 430121 := bstep (se 2 (by rfl) ⟨161295, by rfl⟩ : syracuseStep 430121 = 322591) B322591
theorem B33208127 : Blo 283827 33208127 := bstep (se 1 (by rfl) ⟨24906095, by rfl⟩ : syracuseStep 33208127 = 49812191) B49812191
theorem B1540093 : Blo 283827 1540093 := bstep (se 3 (by rfl) ⟨288767, by rfl⟩ : syracuseStep 1540093 = 577535) B577535
theorem B2747009 : Blo 283827 2747009 := bstep (se 2 (by rfl) ⟨1030128, by rfl⟩ : syracuseStep 2747009 = 2060257) B2060257
theorem B981857 : Blo 283827 981857 := bstep (se 2 (by rfl) ⟨368196, by rfl⟩ : syracuseStep 981857 = 736393) B736393
theorem B1552679 : Blo 283827 1552679 := bstep (se 1 (by rfl) ⟨1164509, by rfl⟩ : syracuseStep 1552679 = 2329019) B2329019
theorem B22138751 : Blo 283827 22138751 := bstep (se 1 (by rfl) ⟨16604063, by rfl⟩ : syracuseStep 22138751 = 33208127) B33208127
theorem B2053457 : Blo 283827 2053457 := bstep (se 2 (by rfl) ⟨770046, by rfl⟩ : syracuseStep 2053457 = 1540093) B1540093
theorem B286747 : Blo 283827 286747 := bstep (se 1 (by rfl) ⟨215060, by rfl⟩ : syracuseStep 286747 = 430121) B430121
theorem B1831339 : Blo 283827 1831339 := bstep (se 1 (by rfl) ⟨1373504, by rfl⟩ : syracuseStep 1831339 = 2747009) B2747009
theorem B654571 : Blo 283827 654571 := bstep (se 1 (by rfl) ⟨490928, by rfl⟩ : syracuseStep 654571 = 981857) B981857
theorem B14759167 : Blo 283827 14759167 := bstep (se 1 (by rfl) ⟨11069375, by rfl⟩ : syracuseStep 14759167 = 22138751) B22138751
theorem B2441785 : Blo 283827 2441785 := bstep (se 2 (by rfl) ⟨915669, by rfl⟩ : syracuseStep 2441785 = 1831339) B1831339
theorem B3491045 : Blo 283827 3491045 := bstep (se 4 (by rfl) ⟨327285, by rfl⟩ : syracuseStep 3491045 = 654571) B654571
theorem B1035119 : Blo 283827 1035119 := bstep (se 1 (by rfl) ⟨776339, by rfl⟩ : syracuseStep 1035119 = 1552679) B1552679
theorem B1368971 : Blo 283827 1368971 := bstep (se 1 (by rfl) ⟨1026728, by rfl⟩ : syracuseStep 1368971 = 2053457) B2053457
theorem B2327363 : Blo 283827 2327363 := bstep (se 1 (by rfl) ⟨1745522, by rfl⟩ : syracuseStep 2327363 = 3491045) B3491045
theorem B690079 : Blo 283827 690079 := bstep (se 1 (by rfl) ⟨517559, by rfl⟩ : syracuseStep 690079 = 1035119) B1035119
theorem B3255713 : Blo 283827 3255713 := bstep (se 2 (by rfl) ⟨1220892, by rfl⟩ : syracuseStep 3255713 = 2441785) B2441785
theorem B19678889 : Blo 283827 19678889 := bstep (se 2 (by rfl) ⟨7379583, by rfl⟩ : syracuseStep 19678889 = 14759167) B14759167
theorem B912647 : Blo 283827 912647 := bstep (se 1 (by rfl) ⟨684485, by rfl⟩ : syracuseStep 912647 = 1368971) B1368971
theorem B920105 : Blo 283827 920105 := bstep (se 2 (by rfl) ⟨345039, by rfl⟩ : syracuseStep 920105 = 690079) B690079
theorem B2170475 : Blo 283827 2170475 := bstep (se 1 (by rfl) ⟨1627856, by rfl⟩ : syracuseStep 2170475 = 3255713) B3255713
theorem B1551575 : Blo 283827 1551575 := bstep (se 1 (by rfl) ⟨1163681, by rfl⟩ : syracuseStep 1551575 = 2327363) B2327363
theorem B13119259 : Blo 283827 13119259 := bstep (se 1 (by rfl) ⟨9839444, by rfl⟩ : syracuseStep 13119259 = 19678889) B19678889
theorem B608431 : Blo 283827 608431 := bstep (se 1 (by rfl) ⟨456323, by rfl⟩ : syracuseStep 608431 = 912647) B912647
theorem B1446983 : Blo 283827 1446983 := bstep (se 1 (by rfl) ⟨1085237, by rfl⟩ : syracuseStep 1446983 = 2170475) B2170475
theorem B1034383 : Blo 283827 1034383 := bstep (se 1 (by rfl) ⟨775787, by rfl⟩ : syracuseStep 1034383 = 1551575) B1551575
theorem B613403 : Blo 283827 613403 := bstep (se 1 (by rfl) ⟨460052, by rfl⟩ : syracuseStep 613403 = 920105) B920105
theorem B811241 : Blo 283827 811241 := bstep (se 2 (by rfl) ⟨304215, by rfl⟩ : syracuseStep 811241 = 608431) B608431
theorem B17492345 : Blo 283827 17492345 := bstep (se 2 (by rfl) ⟨6559629, by rfl⟩ : syracuseStep 17492345 = 13119259) B13119259
theorem B1379177 : Blo 283827 1379177 := bstep (se 2 (by rfl) ⟨517191, by rfl⟩ : syracuseStep 1379177 = 1034383) B1034383
theorem B964655 : Blo 283827 964655 := bstep (se 1 (by rfl) ⟨723491, by rfl⟩ : syracuseStep 964655 = 1446983) B1446983
theorem B408935 : Blo 283827 408935 := bstep (se 1 (by rfl) ⟨306701, by rfl⟩ : syracuseStep 408935 = 613403) B613403
theorem B540827 : Blo 283827 540827 := bstep (se 1 (by rfl) ⟨405620, by rfl⟩ : syracuseStep 540827 = 811241) B811241
theorem B11661563 : Blo 283827 11661563 := bstep (se 1 (by rfl) ⟨8746172, by rfl⟩ : syracuseStep 11661563 = 17492345) B17492345
theorem B360551 : Blo 283827 360551 := bstep (se 1 (by rfl) ⟨270413, by rfl⟩ : syracuseStep 360551 = 540827) B540827
theorem B919451 : Blo 283827 919451 := bstep (se 1 (by rfl) ⟨689588, by rfl⟩ : syracuseStep 919451 = 1379177) B1379177
theorem B7774375 : Blo 283827 7774375 := bstep (se 1 (by rfl) ⟨5830781, by rfl⟩ : syracuseStep 7774375 = 11661563) B11661563
theorem B1090493 : Blo 283827 1090493 := bstep (se 3 (by rfl) ⟨204467, by rfl⟩ : syracuseStep 1090493 = 408935) B408935
theorem B643103 : Blo 283827 643103 := bstep (se 1 (by rfl) ⟨482327, by rfl⟩ : syracuseStep 643103 = 964655) B964655
theorem B428735 : Blo 283827 428735 := bstep (se 1 (by rfl) ⟨321551, by rfl⟩ : syracuseStep 428735 = 643103) B643103
theorem B726995 : Blo 283827 726995 := bstep (se 1 (by rfl) ⟨545246, by rfl⟩ : syracuseStep 726995 = 1090493) B1090493
theorem B10365833 : Blo 283827 10365833 := bstep (se 2 (by rfl) ⟨3887187, by rfl⟩ : syracuseStep 10365833 = 7774375) B7774375
theorem B961469 : Blo 283827 961469 := bstep (se 3 (by rfl) ⟨180275, by rfl⟩ : syracuseStep 961469 = 360551) B360551
theorem B2451869 : Blo 283827 2451869 := bstep (se 3 (by rfl) ⟨459725, by rfl⟩ : syracuseStep 2451869 = 919451) B919451
theorem B640979 : Blo 283827 640979 := bstep (se 1 (by rfl) ⟨480734, by rfl⟩ : syracuseStep 640979 = 961469) B961469
theorem B285823 : Blo 283827 285823 := bstep (se 1 (by rfl) ⟨214367, by rfl⟩ : syracuseStep 285823 = 428735) B428735
theorem B484663 : Blo 283827 484663 := bstep (se 1 (by rfl) ⟨363497, by rfl⟩ : syracuseStep 484663 = 726995) B726995
theorem B1634579 : Blo 283827 1634579 := bstep (se 1 (by rfl) ⟨1225934, by rfl⟩ : syracuseStep 1634579 = 2451869) B2451869
theorem B6910555 : Blo 283827 6910555 := bstep (se 1 (by rfl) ⟨5182916, by rfl⟩ : syracuseStep 6910555 = 10365833) B10365833
theorem B427319 : Blo 283827 427319 := bstep (se 1 (by rfl) ⟨320489, by rfl⟩ : syracuseStep 427319 = 640979) B640979
theorem B9214073 : Blo 283827 9214073 := bstep (se 2 (by rfl) ⟨3455277, by rfl⟩ : syracuseStep 9214073 = 6910555) B6910555
theorem B1089719 : Blo 283827 1089719 := bstep (se 1 (by rfl) ⟨817289, by rfl⟩ : syracuseStep 1089719 = 1634579) B1634579
theorem B646217 : Blo 283827 646217 := bstep (se 2 (by rfl) ⟨242331, by rfl⟩ : syracuseStep 646217 = 484663) B484663
theorem B430811 : Blo 283827 430811 := bstep (se 1 (by rfl) ⟨323108, by rfl⟩ : syracuseStep 430811 = 646217) B646217
theorem B726479 : Blo 283827 726479 := bstep (se 1 (by rfl) ⟨544859, by rfl⟩ : syracuseStep 726479 = 1089719) B1089719
theorem B6142715 : Blo 283827 6142715 := bstep (se 1 (by rfl) ⟨4607036, by rfl⟩ : syracuseStep 6142715 = 9214073) B9214073
theorem B284879 : Blo 283827 284879 := bstep (se 1 (by rfl) ⟨213659, by rfl⟩ : syracuseStep 284879 = 427319) B427319
theorem B287207 : Blo 283827 287207 := bstep (se 1 (by rfl) ⟨215405, by rfl⟩ : syracuseStep 287207 = 430811) B430811
theorem B484319 : Blo 283827 484319 := bstep (se 1 (by rfl) ⟨363239, by rfl⟩ : syracuseStep 484319 = 726479) B726479
theorem B4095143 : Blo 283827 4095143 := bstep (se 1 (by rfl) ⟨3071357, by rfl⟩ : syracuseStep 4095143 = 6142715) B6142715
theorem B2730095 : Blo 283827 2730095 := bstep (se 1 (by rfl) ⟨2047571, by rfl⟩ : syracuseStep 2730095 = 4095143) B4095143
theorem B322879 : Blo 283827 322879 := bstep (se 1 (by rfl) ⟨242159, by rfl⟩ : syracuseStep 322879 = 484319) B484319
theorem B430505 : Blo 283827 430505 := bstep (se 2 (by rfl) ⟨161439, by rfl⟩ : syracuseStep 430505 = 322879) B322879
theorem B1820063 : Blo 283827 1820063 := bstep (se 1 (by rfl) ⟨1365047, by rfl⟩ : syracuseStep 1820063 = 2730095) B2730095
theorem B1213375 : Blo 283827 1213375 := bstep (se 1 (by rfl) ⟨910031, by rfl⟩ : syracuseStep 1213375 = 1820063) B1820063
theorem B287003 : Blo 283827 287003 := bstep (se 1 (by rfl) ⟨215252, by rfl⟩ : syracuseStep 287003 = 430505) B430505
theorem B1617833 : Blo 283827 1617833 := bstep (se 2 (by rfl) ⟨606687, by rfl⟩ : syracuseStep 1617833 = 1213375) B1213375
theorem B1078555 : Blo 283827 1078555 := bstep (se 1 (by rfl) ⟨808916, by rfl⟩ : syracuseStep 1078555 = 1617833) B1617833
theorem B1438073 : Blo 283827 1438073 := bstep (se 2 (by rfl) ⟨539277, by rfl⟩ : syracuseStep 1438073 = 1078555) B1078555
theorem B958715 : Blo 283827 958715 := bstep (se 1 (by rfl) ⟨719036, by rfl⟩ : syracuseStep 958715 = 1438073) B1438073
theorem B639143 : Blo 283827 639143 := bstep (se 1 (by rfl) ⟨479357, by rfl⟩ : syracuseStep 639143 = 958715) B958715
theorem B426095 : Blo 283827 426095 := bstep (se 1 (by rfl) ⟨319571, by rfl⟩ : syracuseStep 426095 = 639143) B639143
theorem B284063 : Blo 283827 284063 := bstep (se 1 (by rfl) ⟨213047, by rfl⟩ : syracuseStep 284063 = 426095) B426095

theorem C0 (j : ℕ) (h1 : 70956 ≤ j) (h2 : j ≤ 71655) : Blo 283827 (4 * j + 3) := by
  interval_cases j
  · exact B283827
  · exact B283831
  · exact B283835
  · exact B283839
  · exact B283843
  · exact B283847
  · exact B283851
  · exact B283855
  · exact B283859
  · exact B283863
  · exact B283867
  · exact B283871
  · exact B283875
  · exact B283879
  · exact B283883
  · exact B283887
  · exact B283891
  · exact B283895
  · exact B283899
  · exact B283903
  · exact B283907
  · exact B283911
  · exact B283915
  · exact B283919
  · exact B283923
  · exact B283927
  · exact B283931
  · exact B283935
  · exact B283939
  · exact B283943
  · exact B283947
  · exact B283951
  · exact B283955
  · exact B283959
  · exact B283963
  · exact B283967
  · exact B283971
  · exact B283975
  · exact B283979
  · exact B283983
  · exact B283987
  · exact B283991
  · exact B283995
  · exact B283999
  · exact B284003
  · exact B284007
  · exact B284011
  · exact B284015
  · exact B284019
  · exact B284023
  · exact B284027
  · exact B284031
  · exact B284035
  · exact B284039
  · exact B284043
  · exact B284047
  · exact B284051
  · exact B284055
  · exact B284059
  · exact B284063
  · exact B284067
  · exact B284071
  · exact B284075
  · exact B284079
  · exact B284083
  · exact B284087
  · exact B284091
  · exact B284095
  · exact B284099
  · exact B284103
  · exact B284107
  · exact B284111
  · exact B284115
  · exact B284119
  · exact B284123
  · exact B284127
  · exact B284131
  · exact B284135
  · exact B284139
  · exact B284143
  · exact B284147
  · exact B284151
  · exact B284155
  · exact B284159
  · exact B284163
  · exact B284167
  · exact B284171
  · exact B284175
  · exact B284179
  · exact B284183
  · exact B284187
  · exact B284191
  · exact B284195
  · exact B284199
  · exact B284203
  · exact B284207
  · exact B284211
  · exact B284215
  · exact B284219
  · exact B284223
  · exact B284227
  · exact B284231
  · exact B284235
  · exact B284239
  · exact B284243
  · exact B284247
  · exact B284251
  · exact B284255
  · exact B284259
  · exact B284263
  · exact B284267
  · exact B284271
  · exact B284275
  · exact B284279
  · exact B284283
  · exact B284287
  · exact B284291
  · exact B284295
  · exact B284299
  · exact B284303
  · exact B284307
  · exact B284311
  · exact B284315
  · exact B284319
  · exact B284323
  · exact B284327
  · exact B284331
  · exact B284335
  · exact B284339
  · exact B284343
  · exact B284347
  · exact B284351
  · exact B284355
  · exact B284359
  · exact B284363
  · exact B284367
  · exact B284371
  · exact B284375
  · exact B284379
  · exact B284383
  · exact B284387
  · exact B284391
  · exact B284395
  · exact B284399
  · exact B284403
  · exact B284407
  · exact B284411
  · exact B284415
  · exact B284419
  · exact B284423
  · exact B284427
  · exact B284431
  · exact B284435
  · exact B284439
  · exact B284443
  · exact B284447
  · exact B284451
  · exact B284455
  · exact B284459
  · exact B284463
  · exact B284467
  · exact B284471
  · exact B284475
  · exact B284479
  · exact B284483
  · exact B284487
  · exact B284491
  · exact B284495
  · exact B284499
  · exact B284503
  · exact B284507
  · exact B284511
  · exact B284515
  · exact B284519
  · exact B284523
  · exact B284527
  · exact B284531
  · exact B284535
  · exact B284539
  · exact B284543
  · exact B284547
  · exact B284551
  · exact B284555
  · exact B284559
  · exact B284563
  · exact B284567
  · exact B284571
  · exact B284575
  · exact B284579
  · exact B284583
  · exact B284587
  · exact B284591
  · exact B284595
  · exact B284599
  · exact B284603
  · exact B284607
  · exact B284611
  · exact B284615
  · exact B284619
  · exact B284623
  · exact B284627
  · exact B284631
  · exact B284635
  · exact B284639
  · exact B284643
  · exact B284647
  · exact B284651
  · exact B284655
  · exact B284659
  · exact B284663
  · exact B284667
  · exact B284671
  · exact B284675
  · exact B284679
  · exact B284683
  · exact B284687
  · exact B284691
  · exact B284695
  · exact B284699
  · exact B284703
  · exact B284707
  · exact B284711
  · exact B284715
  · exact B284719
  · exact B284723
  · exact B284727
  · exact B284731
  · exact B284735
  · exact B284739
  · exact B284743
  · exact B284747
  · exact B284751
  · exact B284755
  · exact B284759
  · exact B284763
  · exact B284767
  · exact B284771
  · exact B284775
  · exact B284779
  · exact B284783
  · exact B284787
  · exact B284791
  · exact B284795
  · exact B284799
  · exact B284803
  · exact B284807
  · exact B284811
  · exact B284815
  · exact B284819
  · exact B284823
  · exact B284827
  · exact B284831
  · exact B284835
  · exact B284839
  · exact B284843
  · exact B284847
  · exact B284851
  · exact B284855
  · exact B284859
  · exact B284863
  · exact B284867
  · exact B284871
  · exact B284875
  · exact B284879
  · exact B284883
  · exact B284887
  · exact B284891
  · exact B284895
  · exact B284899
  · exact B284903
  · exact B284907
  · exact B284911
  · exact B284915
  · exact B284919
  · exact B284923
  · exact B284927
  · exact B284931
  · exact B284935
  · exact B284939
  · exact B284943
  · exact B284947
  · exact B284951
  · exact B284955
  · exact B284959
  · exact B284963
  · exact B284967
  · exact B284971
  · exact B284975
  · exact B284979
  · exact B284983
  · exact B284987
  · exact B284991
  · exact B284995
  · exact B284999
  · exact B285003
  · exact B285007
  · exact B285011
  · exact B285015
  · exact B285019
  · exact B285023
  · exact B285027
  · exact B285031
  · exact B285035
  · exact B285039
  · exact B285043
  · exact B285047
  · exact B285051
  · exact B285055
  · exact B285059
  · exact B285063
  · exact B285067
  · exact B285071
  · exact B285075
  · exact B285079
  · exact B285083
  · exact B285087
  · exact B285091
  · exact B285095
  · exact B285099
  · exact B285103
  · exact B285107
  · exact B285111
  · exact B285115
  · exact B285119
  · exact B285123
  · exact B285127
  · exact B285131
  · exact B285135
  · exact B285139
  · exact B285143
  · exact B285147
  · exact B285151
  · exact B285155
  · exact B285159
  · exact B285163
  · exact B285167
  · exact B285171
  · exact B285175
  · exact B285179
  · exact B285183
  · exact B285187
  · exact B285191
  · exact B285195
  · exact B285199
  · exact B285203
  · exact B285207
  · exact B285211
  · exact B285215
  · exact B285219
  · exact B285223
  · exact B285227
  · exact B285231
  · exact B285235
  · exact B285239
  · exact B285243
  · exact B285247
  · exact B285251
  · exact B285255
  · exact B285259
  · exact B285263
  · exact B285267
  · exact B285271
  · exact B285275
  · exact B285279
  · exact B285283
  · exact B285287
  · exact B285291
  · exact B285295
  · exact B285299
  · exact B285303
  · exact B285307
  · exact B285311
  · exact B285315
  · exact B285319
  · exact B285323
  · exact B285327
  · exact B285331
  · exact B285335
  · exact B285339
  · exact B285343
  · exact B285347
  · exact B285351
  · exact B285355
  · exact B285359
  · exact B285363
  · exact B285367
  · exact B285371
  · exact B285375
  · exact B285379
  · exact B285383
  · exact B285387
  · exact B285391
  · exact B285395
  · exact B285399
  · exact B285403
  · exact B285407
  · exact B285411
  · exact B285415
  · exact B285419
  · exact B285423
  · exact B285427
  · exact B285431
  · exact B285435
  · exact B285439
  · exact B285443
  · exact B285447
  · exact B285451
  · exact B285455
  · exact B285459
  · exact B285463
  · exact B285467
  · exact B285471
  · exact B285475
  · exact B285479
  · exact B285483
  · exact B285487
  · exact B285491
  · exact B285495
  · exact B285499
  · exact B285503
  · exact B285507
  · exact B285511
  · exact B285515
  · exact B285519
  · exact B285523
  · exact B285527
  · exact B285531
  · exact B285535
  · exact B285539
  · exact B285543
  · exact B285547
  · exact B285551
  · exact B285555
  · exact B285559
  · exact B285563
  · exact B285567
  · exact B285571
  · exact B285575
  · exact B285579
  · exact B285583
  · exact B285587
  · exact B285591
  · exact B285595
  · exact B285599
  · exact B285603
  · exact B285607
  · exact B285611
  · exact B285615
  · exact B285619
  · exact B285623
  · exact B285627
  · exact B285631
  · exact B285635
  · exact B285639
  · exact B285643
  · exact B285647
  · exact B285651
  · exact B285655
  · exact B285659
  · exact B285663
  · exact B285667
  · exact B285671
  · exact B285675
  · exact B285679
  · exact B285683
  · exact B285687
  · exact B285691
  · exact B285695
  · exact B285699
  · exact B285703
  · exact B285707
  · exact B285711
  · exact B285715
  · exact B285719
  · exact B285723
  · exact B285727
  · exact B285731
  · exact B285735
  · exact B285739
  · exact B285743
  · exact B285747
  · exact B285751
  · exact B285755
  · exact B285759
  · exact B285763
  · exact B285767
  · exact B285771
  · exact B285775
  · exact B285779
  · exact B285783
  · exact B285787
  · exact B285791
  · exact B285795
  · exact B285799
  · exact B285803
  · exact B285807
  · exact B285811
  · exact B285815
  · exact B285819
  · exact B285823
  · exact B285827
  · exact B285831
  · exact B285835
  · exact B285839
  · exact B285843
  · exact B285847
  · exact B285851
  · exact B285855
  · exact B285859
  · exact B285863
  · exact B285867
  · exact B285871
  · exact B285875
  · exact B285879
  · exact B285883
  · exact B285887
  · exact B285891
  · exact B285895
  · exact B285899
  · exact B285903
  · exact B285907
  · exact B285911
  · exact B285915
  · exact B285919
  · exact B285923
  · exact B285927
  · exact B285931
  · exact B285935
  · exact B285939
  · exact B285943
  · exact B285947
  · exact B285951
  · exact B285955
  · exact B285959
  · exact B285963
  · exact B285967
  · exact B285971
  · exact B285975
  · exact B285979
  · exact B285983
  · exact B285987
  · exact B285991
  · exact B285995
  · exact B285999
  · exact B286003
  · exact B286007
  · exact B286011
  · exact B286015
  · exact B286019
  · exact B286023
  · exact B286027
  · exact B286031
  · exact B286035
  · exact B286039
  · exact B286043
  · exact B286047
  · exact B286051
  · exact B286055
  · exact B286059
  · exact B286063
  · exact B286067
  · exact B286071
  · exact B286075
  · exact B286079
  · exact B286083
  · exact B286087
  · exact B286091
  · exact B286095
  · exact B286099
  · exact B286103
  · exact B286107
  · exact B286111
  · exact B286115
  · exact B286119
  · exact B286123
  · exact B286127
  · exact B286131
  · exact B286135
  · exact B286139
  · exact B286143
  · exact B286147
  · exact B286151
  · exact B286155
  · exact B286159
  · exact B286163
  · exact B286167
  · exact B286171
  · exact B286175
  · exact B286179
  · exact B286183
  · exact B286187
  · exact B286191
  · exact B286195
  · exact B286199
  · exact B286203
  · exact B286207
  · exact B286211
  · exact B286215
  · exact B286219
  · exact B286223
  · exact B286227
  · exact B286231
  · exact B286235
  · exact B286239
  · exact B286243
  · exact B286247
  · exact B286251
  · exact B286255
  · exact B286259
  · exact B286263
  · exact B286267
  · exact B286271
  · exact B286275
  · exact B286279
  · exact B286283
  · exact B286287
  · exact B286291
  · exact B286295
  · exact B286299
  · exact B286303
  · exact B286307
  · exact B286311
  · exact B286315
  · exact B286319
  · exact B286323
  · exact B286327
  · exact B286331
  · exact B286335
  · exact B286339
  · exact B286343
  · exact B286347
  · exact B286351
  · exact B286355
  · exact B286359
  · exact B286363
  · exact B286367
  · exact B286371
  · exact B286375
  · exact B286379
  · exact B286383
  · exact B286387
  · exact B286391
  · exact B286395
  · exact B286399
  · exact B286403
  · exact B286407
  · exact B286411
  · exact B286415
  · exact B286419
  · exact B286423
  · exact B286427
  · exact B286431
  · exact B286435
  · exact B286439
  · exact B286443
  · exact B286447
  · exact B286451
  · exact B286455
  · exact B286459
  · exact B286463
  · exact B286467
  · exact B286471
  · exact B286475
  · exact B286479
  · exact B286483
  · exact B286487
  · exact B286491
  · exact B286495
  · exact B286499
  · exact B286503
  · exact B286507
  · exact B286511
  · exact B286515
  · exact B286519
  · exact B286523
  · exact B286527
  · exact B286531
  · exact B286535
  · exact B286539
  · exact B286543
  · exact B286547
  · exact B286551
  · exact B286555
  · exact B286559
  · exact B286563
  · exact B286567
  · exact B286571
  · exact B286575
  · exact B286579
  · exact B286583
  · exact B286587
  · exact B286591
  · exact B286595
  · exact B286599
  · exact B286603
  · exact B286607
  · exact B286611
  · exact B286615
  · exact B286619
  · exact B286623

theorem C1 (j : ℕ) (h1 : 71656 ≤ j) (h2 : j ≤ 71956) : Blo 283827 (4 * j + 3) := by
  interval_cases j
  · exact B286627
  · exact B286631
  · exact B286635
  · exact B286639
  · exact B286643
  · exact B286647
  · exact B286651
  · exact B286655
  · exact B286659
  · exact B286663
  · exact B286667
  · exact B286671
  · exact B286675
  · exact B286679
  · exact B286683
  · exact B286687
  · exact B286691
  · exact B286695
  · exact B286699
  · exact B286703
  · exact B286707
  · exact B286711
  · exact B286715
  · exact B286719
  · exact B286723
  · exact B286727
  · exact B286731
  · exact B286735
  · exact B286739
  · exact B286743
  · exact B286747
  · exact B286751
  · exact B286755
  · exact B286759
  · exact B286763
  · exact B286767
  · exact B286771
  · exact B286775
  · exact B286779
  · exact B286783
  · exact B286787
  · exact B286791
  · exact B286795
  · exact B286799
  · exact B286803
  · exact B286807
  · exact B286811
  · exact B286815
  · exact B286819
  · exact B286823
  · exact B286827
  · exact B286831
  · exact B286835
  · exact B286839
  · exact B286843
  · exact B286847
  · exact B286851
  · exact B286855
  · exact B286859
  · exact B286863
  · exact B286867
  · exact B286871
  · exact B286875
  · exact B286879
  · exact B286883
  · exact B286887
  · exact B286891
  · exact B286895
  · exact B286899
  · exact B286903
  · exact B286907
  · exact B286911
  · exact B286915
  · exact B286919
  · exact B286923
  · exact B286927
  · exact B286931
  · exact B286935
  · exact B286939
  · exact B286943
  · exact B286947
  · exact B286951
  · exact B286955
  · exact B286959
  · exact B286963
  · exact B286967
  · exact B286971
  · exact B286975
  · exact B286979
  · exact B286983
  · exact B286987
  · exact B286991
  · exact B286995
  · exact B286999
  · exact B287003
  · exact B287007
  · exact B287011
  · exact B287015
  · exact B287019
  · exact B287023
  · exact B287027
  · exact B287031
  · exact B287035
  · exact B287039
  · exact B287043
  · exact B287047
  · exact B287051
  · exact B287055
  · exact B287059
  · exact B287063
  · exact B287067
  · exact B287071
  · exact B287075
  · exact B287079
  · exact B287083
  · exact B287087
  · exact B287091
  · exact B287095
  · exact B287099
  · exact B287103
  · exact B287107
  · exact B287111
  · exact B287115
  · exact B287119
  · exact B287123
  · exact B287127
  · exact B287131
  · exact B287135
  · exact B287139
  · exact B287143
  · exact B287147
  · exact B287151
  · exact B287155
  · exact B287159
  · exact B287163
  · exact B287167
  · exact B287171
  · exact B287175
  · exact B287179
  · exact B287183
  · exact B287187
  · exact B287191
  · exact B287195
  · exact B287199
  · exact B287203
  · exact B287207
  · exact B287211
  · exact B287215
  · exact B287219
  · exact B287223
  · exact B287227
  · exact B287231
  · exact B287235
  · exact B287239
  · exact B287243
  · exact B287247
  · exact B287251
  · exact B287255
  · exact B287259
  · exact B287263
  · exact B287267
  · exact B287271
  · exact B287275
  · exact B287279
  · exact B287283
  · exact B287287
  · exact B287291
  · exact B287295
  · exact B287299
  · exact B287303
  · exact B287307
  · exact B287311
  · exact B287315
  · exact B287319
  · exact B287323
  · exact B287327
  · exact B287331
  · exact B287335
  · exact B287339
  · exact B287343
  · exact B287347
  · exact B287351
  · exact B287355
  · exact B287359
  · exact B287363
  · exact B287367
  · exact B287371
  · exact B287375
  · exact B287379
  · exact B287383
  · exact B287387
  · exact B287391
  · exact B287395
  · exact B287399
  · exact B287403
  · exact B287407
  · exact B287411
  · exact B287415
  · exact B287419
  · exact B287423
  · exact B287427
  · exact B287431
  · exact B287435
  · exact B287439
  · exact B287443
  · exact B287447
  · exact B287451
  · exact B287455
  · exact B287459
  · exact B287463
  · exact B287467
  · exact B287471
  · exact B287475
  · exact B287479
  · exact B287483
  · exact B287487
  · exact B287491
  · exact B287495
  · exact B287499
  · exact B287503
  · exact B287507
  · exact B287511
  · exact B287515
  · exact B287519
  · exact B287523
  · exact B287527
  · exact B287531
  · exact B287535
  · exact B287539
  · exact B287543
  · exact B287547
  · exact B287551
  · exact B287555
  · exact B287559
  · exact B287563
  · exact B287567
  · exact B287571
  · exact B287575
  · exact B287579
  · exact B287583
  · exact B287587
  · exact B287591
  · exact B287595
  · exact B287599
  · exact B287603
  · exact B287607
  · exact B287611
  · exact B287615
  · exact B287619
  · exact B287623
  · exact B287627
  · exact B287631
  · exact B287635
  · exact B287639
  · exact B287643
  · exact B287647
  · exact B287651
  · exact B287655
  · exact B287659
  · exact B287663
  · exact B287667
  · exact B287671
  · exact B287675
  · exact B287679
  · exact B287683
  · exact B287687
  · exact B287691
  · exact B287695
  · exact B287699
  · exact B287703
  · exact B287707
  · exact B287711
  · exact B287715
  · exact B287719
  · exact B287723
  · exact B287727
  · exact B287731
  · exact B287735
  · exact B287739
  · exact B287743
  · exact B287747
  · exact B287751
  · exact B287755
  · exact B287759
  · exact B287763
  · exact B287767
  · exact B287771
  · exact B287775
  · exact B287779
  · exact B287783
  · exact B287787
  · exact B287791
  · exact B287795
  · exact B287799
  · exact B287803
  · exact B287807
  · exact B287811
  · exact B287815
  · exact B287819
  · exact B287823
  · exact B287827

theorem solution (m : ℕ) (hlo : 283827 ≤ m) (hhi : m ≤ 287827) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 70956 ≤ j := by omega
    have hj2 : j ≤ 71956 := by omega
    have hb : Blo 283827 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 71656 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
