-- Prove2me | solution 1 for syracuse_descends_range_1336987_1338987
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:12:43.666753+00:00
-- url     : https://prove2.me/submissions/3722dae6-c264-4867-a8ee-eb205c0cb275

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


theorem B2539525 : Blo 1336987 2539525 := bbase (se 4 (by rfl) ⟨238080, by rfl⟩ : syracuseStep 2539525 = 476161) (by norm_num)
theorem B2007053 : Blo 1336987 2007053 := bbase (se 3 (by rfl) ⟨376322, by rfl⟩ : syracuseStep 2007053 = 752645) (by norm_num)
theorem B2007077 : Blo 1336987 2007077 := bbase (se 4 (by rfl) ⟨188163, by rfl⟩ : syracuseStep 2007077 = 376327) (by norm_num)
theorem B2007101 : Blo 1336987 2007101 := bbase (se 3 (by rfl) ⟨376331, by rfl⟩ : syracuseStep 2007101 = 752663) (by norm_num)
theorem B5079125 : Blo 1336987 5079125 := bbase (se 8 (by rfl) ⟨29760, by rfl⟩ : syracuseStep 5079125 = 59521) (by norm_num)
theorem B2007125 : Blo 1336987 2007125 := bbase (se 8 (by rfl) ⟨11760, by rfl⟩ : syracuseStep 2007125 = 23521) (by norm_num)
theorem B4178021 : Blo 1336987 4178021 := bbase (se 4 (by rfl) ⟨391689, by rfl⟩ : syracuseStep 4178021 = 783379) (by norm_num)
theorem B2007149 : Blo 1336987 2007149 := bbase (se 3 (by rfl) ⟨376340, by rfl⟩ : syracuseStep 2007149 = 752681) (by norm_num)
theorem B2007173 : Blo 1336987 2007173 := bbase (se 4 (by rfl) ⟨188172, by rfl⟩ : syracuseStep 2007173 = 376345) (by norm_num)
theorem B2711693 : Blo 1336987 2711693 := bbase (se 3 (by rfl) ⟨508442, by rfl⟩ : syracuseStep 2711693 = 1016885) (by norm_num)
theorem B2539669 : Blo 1336987 2539669 := bbase (se 6 (by rfl) ⟨59523, by rfl⟩ : syracuseStep 2539669 = 119047) (by norm_num)
theorem B2007197 : Blo 1336987 2007197 := bbase (se 3 (by rfl) ⟨376349, by rfl⟩ : syracuseStep 2007197 = 752699) (by norm_num)
theorem B2007221 : Blo 1336987 2007221 := bbase (se 5 (by rfl) ⟨94088, by rfl⟩ : syracuseStep 2007221 = 188177) (by norm_num)
theorem B2007245 : Blo 1336987 2007245 := bbase (se 3 (by rfl) ⟨376358, by rfl⟩ : syracuseStep 2007245 = 752717) (by norm_num)
theorem B2859229 : Blo 1336987 2859229 := bbase (se 3 (by rfl) ⟨536105, by rfl⟩ : syracuseStep 2859229 = 1072211) (by norm_num)
theorem B4514021 : Blo 1336987 4514021 := bbase (se 4 (by rfl) ⟨423189, by rfl⟩ : syracuseStep 4514021 = 846379) (by norm_num)
theorem B5423333 : Blo 1336987 5423333 := bbase (se 4 (by rfl) ⟨508437, by rfl⟩ : syracuseStep 5423333 = 1016875) (by norm_num)
theorem B2007269 : Blo 1336987 2007269 := bbase (se 4 (by rfl) ⟨188181, by rfl⟩ : syracuseStep 2007269 = 376363) (by norm_num)
theorem B2007293 : Blo 1336987 2007293 := bbase (se 3 (by rfl) ⟨376367, by rfl⟩ : syracuseStep 2007293 = 752735) (by norm_num)
theorem B2007317 : Blo 1336987 2007317 := bbase (se 6 (by rfl) ⟨47046, by rfl⟩ : syracuseStep 2007317 = 94093) (by norm_num)
theorem B2007341 : Blo 1336987 2007341 := bbase (se 3 (by rfl) ⟨376376, by rfl⟩ : syracuseStep 2007341 = 752753) (by norm_num)
theorem B2539829 : Blo 1336987 2539829 := bbase (se 5 (by rfl) ⟨119054, by rfl⟩ : syracuseStep 2539829 = 238109) (by norm_num)
theorem B2007365 : Blo 1336987 2007365 := bbase (se 4 (by rfl) ⟨188190, by rfl⟩ : syracuseStep 2007365 = 376381) (by norm_num)
theorem B2007389 : Blo 1336987 2007389 := bbase (se 3 (by rfl) ⟨376385, by rfl⟩ : syracuseStep 2007389 = 752771) (by norm_num)
theorem B2007413 : Blo 1336987 2007413 := bbase (se 5 (by rfl) ⟨94097, by rfl⟩ : syracuseStep 2007413 = 188195) (by norm_num)
theorem B2007437 : Blo 1336987 2007437 := bbase (se 3 (by rfl) ⟨376394, by rfl⟩ : syracuseStep 2007437 = 752789) (by norm_num)
theorem B2007461 : Blo 1336987 2007461 := bbase (se 4 (by rfl) ⟨188199, by rfl⟩ : syracuseStep 2007461 = 376399) (by norm_num)
theorem B2007485 : Blo 1336987 2007485 := bbase (se 3 (by rfl) ⟨376403, by rfl⟩ : syracuseStep 2007485 = 752807) (by norm_num)
theorem B2539973 : Blo 1336987 2539973 := bbase (se 4 (by rfl) ⟨238122, by rfl⟩ : syracuseStep 2539973 = 476245) (by norm_num)
theorem B2007509 : Blo 1336987 2007509 := bbase (se 7 (by rfl) ⟨23525, by rfl⟩ : syracuseStep 2007509 = 47051) (by norm_num)
theorem B2007533 : Blo 1336987 2007533 := bbase (se 3 (by rfl) ⟨376412, by rfl⟩ : syracuseStep 2007533 = 752825) (by norm_num)
theorem B2007557 : Blo 1336987 2007557 := bbase (se 4 (by rfl) ⟨188208, by rfl⟩ : syracuseStep 2007557 = 376417) (by norm_num)
theorem B2007581 : Blo 1336987 2007581 := bbase (se 3 (by rfl) ⟨376421, by rfl⟩ : syracuseStep 2007581 = 752843) (by norm_num)
theorem B3809845 : Blo 1336987 3809845 := bbase (se 5 (by rfl) ⟨178586, by rfl⟩ : syracuseStep 3809845 = 357173) (by norm_num)
theorem B2007605 : Blo 1336987 2007605 := bbase (se 5 (by rfl) ⟨94106, by rfl⟩ : syracuseStep 2007605 = 188213) (by norm_num)
theorem B2007629 : Blo 1336987 2007629 := bbase (se 3 (by rfl) ⟨376430, by rfl⟩ : syracuseStep 2007629 = 752861) (by norm_num)
theorem B2007653 : Blo 1336987 2007653 := bbase (se 4 (by rfl) ⟨188217, by rfl⟩ : syracuseStep 2007653 = 376435) (by norm_num)
theorem B2007677 : Blo 1336987 2007677 := bbase (se 3 (by rfl) ⟨376439, by rfl⟩ : syracuseStep 2007677 = 752879) (by norm_num)
theorem B1606289 : Blo 1336987 1606289 := bbase (se 2 (by rfl) ⟨602358, by rfl⟩ : syracuseStep 1606289 = 1204717) (by norm_num)
theorem B4514453 : Blo 1336987 4514453 := bbase (se 6 (by rfl) ⟨105807, by rfl⟩ : syracuseStep 4514453 = 211615) (by norm_num)
theorem B2007701 : Blo 1336987 2007701 := bbase (se 6 (by rfl) ⟨47055, by rfl⟩ : syracuseStep 2007701 = 94111) (by norm_num)
theorem B2007725 : Blo 1336987 2007725 := bbase (se 3 (by rfl) ⟨376448, by rfl⟩ : syracuseStep 2007725 = 752897) (by norm_num)
theorem B7332533 : Blo 1336987 7332533 := bbase (se 5 (by rfl) ⟨343712, by rfl⟩ : syracuseStep 7332533 = 687425) (by norm_num)
theorem B2007749 : Blo 1336987 2007749 := bbase (se 4 (by rfl) ⟨188226, by rfl⟩ : syracuseStep 2007749 = 376453) (by norm_num)
theorem B2859725 : Blo 1336987 2859725 := bbase (se 3 (by rfl) ⟨536198, by rfl⟩ : syracuseStep 2859725 = 1072397) (by norm_num)
theorem B2007773 : Blo 1336987 2007773 := bbase (se 3 (by rfl) ⟨376457, by rfl⟩ : syracuseStep 2007773 = 752915) (by norm_num)
theorem B2540261 : Blo 1336987 2540261 := bbase (se 4 (by rfl) ⟨238149, by rfl⟩ : syracuseStep 2540261 = 476299) (by norm_num)
theorem B2007797 : Blo 1336987 2007797 := bbase (se 5 (by rfl) ⟨94115, by rfl⟩ : syracuseStep 2007797 = 188231) (by norm_num)
theorem B1606405 : Blo 1336987 1606405 := bbase (se 4 (by rfl) ⟨150600, by rfl⟩ : syracuseStep 1606405 = 301201) (by norm_num)
theorem B2171653 : Blo 1336987 2171653 := bbase (se 4 (by rfl) ⟨203592, by rfl⟩ : syracuseStep 2171653 = 407185) (by norm_num)
theorem B2007821 : Blo 1336987 2007821 := bbase (se 3 (by rfl) ⟨376466, by rfl⟩ : syracuseStep 2007821 = 752933) (by norm_num)
theorem B1606429 : Blo 1336987 1606429 := bbase (se 3 (by rfl) ⟨301205, by rfl⟩ : syracuseStep 1606429 = 602411) (by norm_num)
theorem B2007845 : Blo 1336987 2007845 := bbase (se 4 (by rfl) ⟨188235, by rfl⟩ : syracuseStep 2007845 = 376471) (by norm_num)
theorem B2007869 : Blo 1336987 2007869 := bbase (se 3 (by rfl) ⟨376475, by rfl⟩ : syracuseStep 2007869 = 752951) (by norm_num)
theorem B6431557 : Blo 1336987 6431557 := bbase (se 4 (by rfl) ⟨602958, by rfl⟩ : syracuseStep 6431557 = 1205917) (by norm_num)
theorem B2007893 : Blo 1336987 2007893 := bbase (se 9 (by rfl) ⟨5882, by rfl⟩ : syracuseStep 2007893 = 11765) (by norm_num)
theorem B5718869 : Blo 1336987 5718869 := bbase (se 9 (by rfl) ⟨16754, by rfl⟩ : syracuseStep 5718869 = 33509) (by norm_num)
theorem B2007917 : Blo 1336987 2007917 := bbase (se 3 (by rfl) ⟨376484, by rfl⟩ : syracuseStep 2007917 = 752969) (by norm_num)
theorem B2540413 : Blo 1336987 2540413 := bbase (se 3 (by rfl) ⟨476327, by rfl⟩ : syracuseStep 2540413 = 952655) (by norm_num)
theorem B2007941 : Blo 1336987 2007941 := bbase (se 4 (by rfl) ⟨188244, by rfl⟩ : syracuseStep 2007941 = 376489) (by norm_num)
theorem B2007965 : Blo 1336987 2007965 := bbase (se 3 (by rfl) ⟨376493, by rfl⟩ : syracuseStep 2007965 = 752987) (by norm_num)
theorem B2007989 : Blo 1336987 2007989 := bbase (se 5 (by rfl) ⟨94124, by rfl⟩ : syracuseStep 2007989 = 188249) (by norm_num)
theorem B2008013 : Blo 1336987 2008013 := bbase (se 3 (by rfl) ⟨376502, by rfl⟩ : syracuseStep 2008013 = 753005) (by norm_num)
theorem B2008037 : Blo 1336987 2008037 := bbase (se 4 (by rfl) ⟨188253, by rfl⟩ : syracuseStep 2008037 = 376507) (by norm_num)
theorem B3384301 : Blo 1336987 3384301 := bbase (se 3 (by rfl) ⟨634556, by rfl⟩ : syracuseStep 3384301 = 1269113) (by norm_num)
theorem B2008061 : Blo 1336987 2008061 := bbase (se 3 (by rfl) ⟨376511, by rfl⟩ : syracuseStep 2008061 = 753023) (by norm_num)
theorem B2008085 : Blo 1336987 2008085 := bbase (se 6 (by rfl) ⟨47064, by rfl⟩ : syracuseStep 2008085 = 94129) (by norm_num)
theorem B2008109 : Blo 1336987 2008109 := bbase (se 3 (by rfl) ⟨376520, by rfl⟩ : syracuseStep 2008109 = 753041) (by norm_num)
theorem B4514885 : Blo 1336987 4514885 := bbase (se 4 (by rfl) ⟨423270, by rfl⟩ : syracuseStep 4514885 = 846541) (by norm_num)
theorem B2008133 : Blo 1336987 2008133 := bbase (se 4 (by rfl) ⟨188262, by rfl⟩ : syracuseStep 2008133 = 376525) (by norm_num)
theorem B7619669 : Blo 1336987 7619669 := bbase (se 8 (by rfl) ⟨44646, by rfl⟩ : syracuseStep 7619669 = 89293) (by norm_num)
theorem B3384413 : Blo 1336987 3384413 := bbase (se 3 (by rfl) ⟨634577, by rfl⟩ : syracuseStep 3384413 = 1269155) (by norm_num)
theorem B2008157 : Blo 1336987 2008157 := bbase (se 3 (by rfl) ⟨376529, by rfl⟩ : syracuseStep 2008157 = 753059) (by norm_num)
theorem B2008181 : Blo 1336987 2008181 := bbase (se 5 (by rfl) ⟨94133, by rfl⟩ : syracuseStep 2008181 = 188267) (by norm_num)
theorem B2008205 : Blo 1336987 2008205 := bbase (se 3 (by rfl) ⟨376538, by rfl⟩ : syracuseStep 2008205 = 753077) (by norm_num)
theorem B3433637 : Blo 1336987 3433637 := bbase (se 4 (by rfl) ⟨321903, by rfl⟩ : syracuseStep 3433637 = 643807) (by norm_num)
theorem B6775973 : Blo 1336987 6775973 := bbase (se 4 (by rfl) ⟨635247, by rfl⟩ : syracuseStep 6775973 = 1270495) (by norm_num)
theorem B2008229 : Blo 1336987 2008229 := bbase (se 4 (by rfl) ⟨188271, by rfl⟩ : syracuseStep 2008229 = 376543) (by norm_num)
theorem B2540717 : Blo 1336987 2540717 := bbase (se 3 (by rfl) ⟨476384, by rfl⟩ : syracuseStep 2540717 = 952769) (by norm_num)
theorem B2008253 : Blo 1336987 2008253 := bbase (se 3 (by rfl) ⟨376547, by rfl⟩ : syracuseStep 2008253 = 753095) (by norm_num)
theorem B2008277 : Blo 1336987 2008277 := bbase (se 7 (by rfl) ⟨23534, by rfl⟩ : syracuseStep 2008277 = 47069) (by norm_num)
theorem B5711077 : Blo 1336987 5711077 := bbase (se 4 (by rfl) ⟨535413, by rfl⟩ : syracuseStep 5711077 = 1070827) (by norm_num)
theorem B2008301 : Blo 1336987 2008301 := bbase (se 3 (by rfl) ⟨376556, by rfl⟩ : syracuseStep 2008301 = 753113) (by norm_num)
theorem B2172149 : Blo 1336987 2172149 := bbase (se 5 (by rfl) ⟨101819, by rfl⟩ : syracuseStep 2172149 = 203639) (by norm_num)
theorem B2008325 : Blo 1336987 2008325 := bbase (se 4 (by rfl) ⟨188280, by rfl⟩ : syracuseStep 2008325 = 376561) (by norm_num)
theorem B3384605 : Blo 1336987 3384605 := bbase (se 3 (by rfl) ⟨634613, by rfl⟩ : syracuseStep 3384605 = 1269227) (by norm_num)
theorem B2008349 : Blo 1336987 2008349 := bbase (se 3 (by rfl) ⟨376565, by rfl⟩ : syracuseStep 2008349 = 753131) (by norm_num)
theorem B3212597 : Blo 1336987 3212597 := bbase (se 5 (by rfl) ⟨150590, by rfl⟩ : syracuseStep 3212597 = 301181) (by norm_num)
theorem B2008373 : Blo 1336987 2008373 := bbase (se 5 (by rfl) ⟨94142, by rfl⟩ : syracuseStep 2008373 = 188285) (by norm_num)
theorem B10167605 : Blo 1336987 10167605 := bbase (se 5 (by rfl) ⟨476606, by rfl⟩ : syracuseStep 10167605 = 953213) (by norm_num)
theorem B2008397 : Blo 1336987 2008397 := bbase (se 3 (by rfl) ⟨376574, by rfl⟩ : syracuseStep 2008397 = 753149) (by norm_num)
theorem B2008421 : Blo 1336987 2008421 := bbase (se 4 (by rfl) ⟨188289, by rfl⟩ : syracuseStep 2008421 = 376579) (by norm_num)
theorem B2008445 : Blo 1336987 2008445 := bbase (se 3 (by rfl) ⟨376583, by rfl⟩ : syracuseStep 2008445 = 753167) (by norm_num)
theorem B2008469 : Blo 1336987 2008469 := bbase (se 6 (by rfl) ⟨47073, by rfl⟩ : syracuseStep 2008469 = 94147) (by norm_num)
theorem B1607125 : Blo 1336987 1607125 := bbase (se 7 (by rfl) ⟨18833, by rfl⟩ : syracuseStep 1607125 = 37667) (by norm_num)
theorem B4515317 : Blo 1336987 4515317 := bbase (se 5 (by rfl) ⟨211655, by rfl⟩ : syracuseStep 4515317 = 423311) (by norm_num)
theorem B1525277 : Blo 1336987 1525277 := bbase (se 3 (by rfl) ⟨285989, by rfl⟩ : syracuseStep 1525277 = 571979) (by norm_num)
theorem B1607221 : Blo 1336987 1607221 := bbase (se 5 (by rfl) ⟨75338, by rfl⟩ : syracuseStep 1607221 = 150677) (by norm_num)
theorem B2410069 : Blo 1336987 2410069 := bbase (se 8 (by rfl) ⟨14121, by rfl⟩ : syracuseStep 2410069 = 28243) (by norm_num)
theorem B3384949 : Blo 1336987 3384949 := bbase (se 5 (by rfl) ⟨158669, by rfl⟩ : syracuseStep 3384949 = 317339) (by norm_num)
theorem B10159829 : Blo 1336987 10159829 := bbase (se 7 (by rfl) ⟨119060, by rfl⟩ : syracuseStep 10159829 = 238121) (by norm_num)
theorem B3385061 : Blo 1336987 3385061 := bbase (se 4 (by rfl) ⟨317349, by rfl⟩ : syracuseStep 3385061 = 634699) (by norm_num)
theorem B3008285 : Blo 1336987 3008285 := bbase (se 3 (by rfl) ⟨564053, by rfl⟩ : syracuseStep 3008285 = 1128107) (by norm_num)
theorem B3434293 : Blo 1336987 3434293 := bbase (se 5 (by rfl) ⟨160982, by rfl⟩ : syracuseStep 3434293 = 321965) (by norm_num)
theorem B3008357 : Blo 1336987 3008357 := bbase (se 4 (by rfl) ⟨282033, by rfl⟩ : syracuseStep 3008357 = 564067) (by norm_num)
theorem B2410357 : Blo 1336987 2410357 := bbase (se 5 (by rfl) ⟨112985, by rfl⟩ : syracuseStep 2410357 = 225971) (by norm_num)
theorem B2574197 : Blo 1336987 2574197 := bbase (se 5 (by rfl) ⟨120665, by rfl⟩ : syracuseStep 2574197 = 241331) (by norm_num)
theorem B5146517 : Blo 1336987 5146517 := bbase (se 6 (by rfl) ⟨120621, by rfl⟩ : syracuseStep 5146517 = 241243) (by norm_num)
theorem B2541469 : Blo 1336987 2541469 := bbase (se 3 (by rfl) ⟨476525, by rfl⟩ : syracuseStep 2541469 = 953051) (by norm_num)
theorem B3385253 : Blo 1336987 3385253 := bbase (se 4 (by rfl) ⟨317367, by rfl⟩ : syracuseStep 3385253 = 634735) (by norm_num)
theorem B4515749 : Blo 1336987 4515749 := bbase (se 4 (by rfl) ⟨423351, by rfl⟩ : syracuseStep 4515749 = 846703) (by norm_num)
theorem B3008429 : Blo 1336987 3008429 := bbase (se 3 (by rfl) ⟨564080, by rfl⟩ : syracuseStep 3008429 = 1128161) (by norm_num)
theorem B3008501 : Blo 1336987 3008501 := bbase (se 5 (by rfl) ⟨141023, by rfl⟩ : syracuseStep 3008501 = 282047) (by norm_num)
theorem B3811349 : Blo 1336987 3811349 := bbase (se 6 (by rfl) ⟨89328, by rfl⟩ : syracuseStep 3811349 = 178657) (by norm_num)
theorem B2541613 : Blo 1336987 2541613 := bbase (se 3 (by rfl) ⟨476552, by rfl⟩ : syracuseStep 2541613 = 953105) (by norm_num)
theorem B2287669 : Blo 1336987 2287669 := bbase (se 5 (by rfl) ⟨107234, by rfl⟩ : syracuseStep 2287669 = 214469) (by norm_num)
theorem B3008573 : Blo 1336987 3008573 := bbase (se 3 (by rfl) ⟨564107, by rfl⟩ : syracuseStep 3008573 = 1128215) (by norm_num)
theorem B6514805 : Blo 1336987 6514805 := bbase (se 5 (by rfl) ⟨305381, by rfl⟩ : syracuseStep 6514805 = 610763) (by norm_num)
theorem B3008645 : Blo 1336987 3008645 := bbase (se 4 (by rfl) ⟨282060, by rfl⟩ : syracuseStep 3008645 = 564121) (by norm_num)
theorem B5081237 : Blo 1336987 5081237 := bbase (se 6 (by rfl) ⟨119091, by rfl⟩ : syracuseStep 5081237 = 238183) (by norm_num)
theorem B3008717 : Blo 1336987 3008717 := bbase (se 3 (by rfl) ⟨564134, by rfl⟩ : syracuseStep 3008717 = 1128269) (by norm_num)
theorem B2541773 : Blo 1336987 2541773 := bbase (se 3 (by rfl) ⟨476582, by rfl⟩ : syracuseStep 2541773 = 953165) (by norm_num)
theorem B2033885 : Blo 1336987 2033885 := bbase (se 3 (by rfl) ⟨381353, by rfl⟩ : syracuseStep 2033885 = 762707) (by norm_num)
theorem B3385597 : Blo 1336987 3385597 := bbase (se 3 (by rfl) ⟨634799, by rfl⟩ : syracuseStep 3385597 = 1269599) (by norm_num)
theorem B3008789 : Blo 1336987 3008789 := bbase (se 6 (by rfl) ⟨70518, by rfl⟩ : syracuseStep 3008789 = 141037) (by norm_num)
theorem B4516181 : Blo 1336987 4516181 := bbase (se 10 (by rfl) ⟨6615, by rfl⟩ : syracuseStep 4516181 = 13231) (by norm_num)
theorem B3008861 : Blo 1336987 3008861 := bbase (se 3 (by rfl) ⟨564161, by rfl⟩ : syracuseStep 3008861 = 1128323) (by norm_num)
theorem B2034013 : Blo 1336987 2034013 := bbase (se 3 (by rfl) ⟨381377, by rfl⟩ : syracuseStep 2034013 = 762755) (by norm_num)
theorem B2541917 : Blo 1336987 2541917 := bbase (se 3 (by rfl) ⟨476609, by rfl⟩ : syracuseStep 2541917 = 953219) (by norm_num)
theorem B3385709 : Blo 1336987 3385709 := bbase (se 3 (by rfl) ⟨634820, by rfl⟩ : syracuseStep 3385709 = 1269641) (by norm_num)
theorem B3008933 : Blo 1336987 3008933 := bbase (se 4 (by rfl) ⟨282087, by rfl⟩ : syracuseStep 3008933 = 564175) (by norm_num)
theorem B5425589 : Blo 1336987 5425589 := bbase (se 5 (by rfl) ⟨254324, by rfl⟩ : syracuseStep 5425589 = 508649) (by norm_num)
theorem B5081525 : Blo 1336987 5081525 := bbase (se 5 (by rfl) ⟨238196, by rfl⟩ : syracuseStep 5081525 = 476393) (by norm_num)
theorem B6777269 : Blo 1336987 6777269 := bbase (se 5 (by rfl) ⟨317684, by rfl⟩ : syracuseStep 6777269 = 635369) (by norm_num)
theorem B36628949 : Blo 1336987 36628949 := bbase (se 7 (by rfl) ⟨429245, by rfl⟩ : syracuseStep 36628949 = 858491) (by norm_num)
theorem B3009005 : Blo 1336987 3009005 := bbase (se 3 (by rfl) ⟨564188, by rfl⟩ : syracuseStep 3009005 = 1128377) (by norm_num)
theorem B1608221 : Blo 1336987 1608221 := bbase (se 3 (by rfl) ⟨301541, by rfl⟩ : syracuseStep 1608221 = 603083) (by norm_num)
theorem B3385901 : Blo 1336987 3385901 := bbase (se 3 (by rfl) ⟨634856, by rfl⟩ : syracuseStep 3385901 = 1269713) (by norm_num)
theorem B3009077 : Blo 1336987 3009077 := bbase (se 5 (by rfl) ⟨141050, by rfl⟩ : syracuseStep 3009077 = 282101) (by norm_num)
theorem B1428077 : Blo 1336987 1428077 := bbase (se 3 (by rfl) ⟨267764, by rfl⟩ : syracuseStep 1428077 = 535529) (by norm_num)
theorem B3009149 : Blo 1336987 3009149 := bbase (se 3 (by rfl) ⟨564215, by rfl⟩ : syracuseStep 3009149 = 1128431) (by norm_num)
theorem B2411149 : Blo 1336987 2411149 := bbase (se 3 (by rfl) ⟨452090, by rfl⟩ : syracuseStep 2411149 = 904181) (by norm_num)
theorem B5712565 : Blo 1336987 5712565 := bbase (se 5 (by rfl) ⟨267776, by rfl⟩ : syracuseStep 5712565 = 535553) (by norm_num)
theorem B5712581 : Blo 1336987 5712581 := bbase (se 4 (by rfl) ⟨535554, by rfl⟩ : syracuseStep 5712581 = 1071109) (by norm_num)
theorem B3009221 : Blo 1336987 3009221 := bbase (se 4 (by rfl) ⟨282114, by rfl⟩ : syracuseStep 3009221 = 564229) (by norm_num)
theorem B25701077 : Blo 1336987 25701077 := bbase (se 7 (by rfl) ⟨301184, by rfl⟩ : syracuseStep 25701077 = 602369) (by norm_num)
theorem B4516613 : Blo 1336987 4516613 := bbase (se 4 (by rfl) ⟨423432, by rfl⟩ : syracuseStep 4516613 = 846865) (by norm_num)
theorem B3009293 : Blo 1336987 3009293 := bbase (se 3 (by rfl) ⟨564242, by rfl⟩ : syracuseStep 3009293 = 1128485) (by norm_num)
theorem B2411293 : Blo 1336987 2411293 := bbase (se 3 (by rfl) ⟨452117, by rfl⟩ : syracuseStep 2411293 = 904235) (by norm_num)
theorem B1608509 : Blo 1336987 1608509 := bbase (se 3 (by rfl) ⟨301595, by rfl⟩ : syracuseStep 1608509 = 603191) (by norm_num)
theorem B6769493 : Blo 1336987 6769493 := bbase (se 9 (by rfl) ⟨19832, by rfl⟩ : syracuseStep 6769493 = 39665) (by norm_num)
theorem B3009365 : Blo 1336987 3009365 := bbase (se 9 (by rfl) ⟨8816, by rfl⟩ : syracuseStep 3009365 = 17633) (by norm_num)
theorem B3386245 : Blo 1336987 3386245 := bbase (se 4 (by rfl) ⟨317460, by rfl⟩ : syracuseStep 3386245 = 634921) (by norm_num)
theorem B3009437 : Blo 1336987 3009437 := bbase (se 3 (by rfl) ⟨564269, by rfl⟩ : syracuseStep 3009437 = 1128539) (by norm_num)
theorem B2411453 : Blo 1336987 2411453 := bbase (se 3 (by rfl) ⟨452147, by rfl⟩ : syracuseStep 2411453 = 904295) (by norm_num)
theorem B1526737 : Blo 1336987 1526737 := bbase (se 2 (by rfl) ⟨572526, by rfl⟩ : syracuseStep 1526737 = 1145053) (by norm_num)
theorem B3009509 : Blo 1336987 3009509 := bbase (se 4 (by rfl) ⟨282141, by rfl⟩ : syracuseStep 3009509 = 564283) (by norm_num)
theorem B3386357 : Blo 1336987 3386357 := bbase (se 5 (by rfl) ⟨158735, by rfl⟩ : syracuseStep 3386357 = 317471) (by norm_num)
theorem B2411525 : Blo 1336987 2411525 := bbase (se 4 (by rfl) ⟨226080, by rfl⟩ : syracuseStep 2411525 = 452161) (by norm_num)
theorem B1428521 : Blo 1336987 1428521 := bbase (se 2 (by rfl) ⟨535695, by rfl⟩ : syracuseStep 1428521 = 1071391) (by norm_num)
theorem B3009581 : Blo 1336987 3009581 := bbase (se 3 (by rfl) ⟨564296, by rfl⟩ : syracuseStep 3009581 = 1128593) (by norm_num)
theorem B3009653 : Blo 1336987 3009653 := bbase (se 5 (by rfl) ⟨141077, by rfl⟩ : syracuseStep 3009653 = 282155) (by norm_num)
theorem B25734293 : Blo 1336987 25734293 := bbase (se 6 (by rfl) ⟨603147, by rfl⟩ : syracuseStep 25734293 = 1206295) (by norm_num)
theorem B1715377 : Blo 1336987 1715377 := bbase (se 2 (by rfl) ⟨643266, by rfl⟩ : syracuseStep 1715377 = 1286533) (by norm_num)
theorem B3386549 : Blo 1336987 3386549 := bbase (se 5 (by rfl) ⟨158744, by rfl⟩ : syracuseStep 3386549 = 317489) (by norm_num)
theorem B4517045 : Blo 1336987 4517045 := bbase (se 5 (by rfl) ⟨211736, by rfl⟩ : syracuseStep 4517045 = 423473) (by norm_num)
theorem B3009725 : Blo 1336987 3009725 := bbase (se 3 (by rfl) ⟨564323, by rfl⟩ : syracuseStep 3009725 = 1128647) (by norm_num)
theorem B1903829 : Blo 1336987 1903829 := bbase (se 7 (by rfl) ⟨22310, by rfl⟩ : syracuseStep 1903829 = 44621) (by norm_num)
theorem B7621877 : Blo 1336987 7621877 := bbase (se 5 (by rfl) ⟨357275, by rfl⟩ : syracuseStep 7621877 = 714551) (by norm_num)
theorem B3009797 : Blo 1336987 3009797 := bbase (se 4 (by rfl) ⟨282168, by rfl⟩ : syracuseStep 3009797 = 564337) (by norm_num)
theorem B2444573 : Blo 1336987 2444573 := bbase (se 3 (by rfl) ⟨458357, by rfl⟩ : syracuseStep 2444573 = 916715) (by norm_num)
theorem B1428769 : Blo 1336987 1428769 := bbase (se 2 (by rfl) ⟨535788, by rfl⟩ : syracuseStep 1428769 = 1071577) (by norm_num)
theorem B3009869 : Blo 1336987 3009869 := bbase (se 3 (by rfl) ⟨564350, by rfl⟩ : syracuseStep 3009869 = 1128701) (by norm_num)
theorem B2256221 : Blo 1336987 2256221 := bbase (se 3 (by rfl) ⟨423041, by rfl⟩ : syracuseStep 2256221 = 846083) (by norm_num)
theorem B3009941 : Blo 1336987 3009941 := bbase (se 6 (by rfl) ⟨70545, by rfl⟩ : syracuseStep 3009941 = 141091) (by norm_num)
theorem B2141597 : Blo 1336987 2141597 := bbase (se 3 (by rfl) ⟨401549, by rfl⟩ : syracuseStep 2141597 = 803099) (by norm_num)
theorem B2936237 : Blo 1336987 2936237 := bbase (se 3 (by rfl) ⟨550544, by rfl⟩ : syracuseStep 2936237 = 1101089) (by norm_num)
theorem B4345285 : Blo 1336987 4345285 := bbase (se 4 (by rfl) ⟨407370, by rfl⟩ : syracuseStep 4345285 = 814741) (by norm_num)
theorem B2256349 : Blo 1336987 2256349 := bbase (se 3 (by rfl) ⟨423065, by rfl⟩ : syracuseStep 2256349 = 846131) (by norm_num)
theorem B3091933 : Blo 1336987 3091933 := bbase (se 3 (by rfl) ⟨579737, by rfl⟩ : syracuseStep 3091933 = 1159475) (by norm_num)
theorem B3010013 : Blo 1336987 3010013 := bbase (se 3 (by rfl) ⟨564377, by rfl⟩ : syracuseStep 3010013 = 1128755) (by norm_num)
theorem B4287973 : Blo 1336987 4287973 := bbase (se 4 (by rfl) ⟨401997, by rfl⟩ : syracuseStep 4287973 = 803995) (by norm_num)
theorem B2035181 : Blo 1336987 2035181 := bbase (se 3 (by rfl) ⟨381596, by rfl⟩ : syracuseStep 2035181 = 763193) (by norm_num)
theorem B3386893 : Blo 1336987 3386893 := bbase (se 3 (by rfl) ⟨635042, by rfl⟩ : syracuseStep 3386893 = 1270085) (by norm_num)
theorem B19295765 : Blo 1336987 19295765 := bbase (se 6 (by rfl) ⟨452244, by rfl⟩ : syracuseStep 19295765 = 904489) (by norm_num)
theorem B3010085 : Blo 1336987 3010085 := bbase (se 4 (by rfl) ⟨282195, by rfl⟩ : syracuseStep 3010085 = 564391) (by norm_num)
theorem B3214885 : Blo 1336987 3214885 := bbase (se 4 (by rfl) ⟨301395, by rfl⟩ : syracuseStep 3214885 = 602791) (by norm_num)
theorem B2256437 : Blo 1336987 2256437 := bbase (se 5 (by rfl) ⟨105770, by rfl⟩ : syracuseStep 2256437 = 211541) (by norm_num)
theorem B3812933 : Blo 1336987 3812933 := bbase (se 4 (by rfl) ⟨357462, by rfl⟩ : syracuseStep 3812933 = 714925) (by norm_num)
theorem B5082709 : Blo 1336987 5082709 := bbase (se 8 (by rfl) ⟨29781, by rfl⟩ : syracuseStep 5082709 = 59563) (by norm_num)
theorem B4517477 : Blo 1336987 4517477 := bbase (se 4 (by rfl) ⟨423513, by rfl⟩ : syracuseStep 4517477 = 847027) (by norm_num)
theorem B3010157 : Blo 1336987 3010157 := bbase (se 3 (by rfl) ⟨564404, by rfl⟩ : syracuseStep 3010157 = 1128809) (by norm_num)
theorem B10849909 : Blo 1336987 10849909 := bbase (se 5 (by rfl) ⟨508589, by rfl⟩ : syracuseStep 10849909 = 1017179) (by norm_num)
theorem B3387005 : Blo 1336987 3387005 := bbase (se 3 (by rfl) ⟨635063, by rfl⟩ : syracuseStep 3387005 = 1270127) (by norm_num)
theorem B3214981 : Blo 1336987 3214981 := bbase (se 4 (by rfl) ⟨301404, by rfl⟩ : syracuseStep 3214981 = 602809) (by norm_num)
theorem B3051173 : Blo 1336987 3051173 := bbase (se 4 (by rfl) ⟨286047, by rfl⟩ : syracuseStep 3051173 = 572095) (by norm_num)
theorem B2256565 : Blo 1336987 2256565 := bbase (se 5 (by rfl) ⟨105776, by rfl⟩ : syracuseStep 2256565 = 211553) (by norm_num)
theorem B3010229 : Blo 1336987 3010229 := bbase (se 5 (by rfl) ⟨141104, by rfl⟩ : syracuseStep 3010229 = 282209) (by norm_num)
theorem B9645749 : Blo 1336987 9645749 := bbase (se 5 (by rfl) ⟨452144, by rfl⟩ : syracuseStep 9645749 = 904289) (by norm_num)
theorem B6778565 : Blo 1336987 6778565 := bbase (se 4 (by rfl) ⟨635490, by rfl⟩ : syracuseStep 6778565 = 1270981) (by norm_num)
theorem B1429201 : Blo 1336987 1429201 := bbase (se 2 (by rfl) ⟨535950, by rfl⟩ : syracuseStep 1429201 = 1071901) (by norm_num)
theorem B4288229 : Blo 1336987 4288229 := bbase (se 4 (by rfl) ⟨402021, by rfl⟩ : syracuseStep 4288229 = 804043) (by norm_num)
theorem B3010301 : Blo 1336987 3010301 := bbase (se 3 (by rfl) ⟨564431, by rfl⟩ : syracuseStep 3010301 = 1128863) (by norm_num)
theorem B2256653 : Blo 1336987 2256653 := bbase (se 3 (by rfl) ⟨423122, by rfl⟩ : syracuseStep 2256653 = 846245) (by norm_num)
theorem B12865301 : Blo 1336987 12865301 := bbase (se 6 (by rfl) ⟨301530, by rfl⟩ : syracuseStep 12865301 = 603061) (by norm_num)
theorem B1429273 : Blo 1336987 1429273 := bbase (se 2 (by rfl) ⟨535977, by rfl⟩ : syracuseStep 1429273 = 1071955) (by norm_num)
theorem B2142013 : Blo 1336987 2142013 := bbase (se 3 (by rfl) ⟨401627, by rfl⟩ : syracuseStep 2142013 = 803255) (by norm_num)
theorem B3387197 : Blo 1336987 3387197 := bbase (se 3 (by rfl) ⟨635099, by rfl⟩ : syracuseStep 3387197 = 1270199) (by norm_num)
theorem B3010373 : Blo 1336987 3010373 := bbase (se 4 (by rfl) ⟨282222, by rfl⟩ : syracuseStep 3010373 = 564445) (by norm_num)
theorem B3215173 : Blo 1336987 3215173 := bbase (se 4 (by rfl) ⟨301422, by rfl⟩ : syracuseStep 3215173 = 602845) (by norm_num)
theorem B1740629 : Blo 1336987 1740629 := bbase (se 9 (by rfl) ⟨5099, by rfl⟩ : syracuseStep 1740629 = 10199) (by norm_num)
theorem B6426485 : Blo 1336987 6426485 := bbase (se 5 (by rfl) ⟨301241, by rfl⟩ : syracuseStep 6426485 = 602483) (by norm_num)
theorem B5083013 : Blo 1336987 5083013 := bbase (se 4 (by rfl) ⟨476532, by rfl⟩ : syracuseStep 5083013 = 953065) (by norm_num)
theorem B2256781 : Blo 1336987 2256781 := bbase (se 3 (by rfl) ⟨423146, by rfl⟩ : syracuseStep 2256781 = 846293) (by norm_num)
theorem B3010445 : Blo 1336987 3010445 := bbase (se 3 (by rfl) ⟨564458, by rfl⟩ : syracuseStep 3010445 = 1128917) (by norm_num)
theorem B1904581 : Blo 1336987 1904581 := bbase (se 4 (by rfl) ⟨178554, by rfl⟩ : syracuseStep 1904581 = 357109) (by norm_num)
theorem B3010517 : Blo 1336987 3010517 := bbase (se 7 (by rfl) ⟨35279, by rfl⟩ : syracuseStep 3010517 = 70559) (by norm_num)
theorem B9646037 : Blo 1336987 9646037 := bbase (se 7 (by rfl) ⟨113039, by rfl⟩ : syracuseStep 9646037 = 226079) (by norm_num)
theorem B2256869 : Blo 1336987 2256869 := bbase (se 4 (by rfl) ⟨211581, by rfl⟩ : syracuseStep 2256869 = 423163) (by norm_num)
theorem B1355761 : Blo 1336987 1355761 := bbase (se 2 (by rfl) ⟨508410, by rfl⟩ : syracuseStep 1355761 = 1016821) (by norm_num)
theorem B2412533 : Blo 1336987 2412533 := bbase (se 5 (by rfl) ⟨113087, by rfl⟩ : syracuseStep 2412533 = 226175) (by norm_num)
theorem B8572949 : Blo 1336987 8572949 := bbase (se 6 (by rfl) ⟨200928, by rfl⟩ : syracuseStep 8572949 = 401857) (by norm_num)
theorem B4517909 : Blo 1336987 4517909 := bbase (se 6 (by rfl) ⟨105888, by rfl⟩ : syracuseStep 4517909 = 211777) (by norm_num)
theorem B3010589 : Blo 1336987 3010589 := bbase (se 3 (by rfl) ⟨564485, by rfl⟩ : syracuseStep 3010589 = 1128971) (by norm_num)
theorem B4821029 : Blo 1336987 4821029 := bbase (se 4 (by rfl) ⟨451971, by rfl⟩ : syracuseStep 4821029 = 903943) (by norm_num)
theorem B2576461 : Blo 1336987 2576461 := bbase (se 3 (by rfl) ⟨483086, by rfl⟩ : syracuseStep 2576461 = 966173) (by norm_num)
theorem B7721045 : Blo 1336987 7721045 := bbase (se 8 (by rfl) ⟨45240, by rfl⟩ : syracuseStep 7721045 = 90481) (by norm_num)
theorem B6770789 : Blo 1336987 6770789 := bbase (se 4 (by rfl) ⟨634761, by rfl⟩ : syracuseStep 6770789 = 1269523) (by norm_num)
theorem B2256997 : Blo 1336987 2256997 := bbase (se 4 (by rfl) ⟨211593, by rfl⟩ : syracuseStep 2256997 = 423187) (by norm_num)
theorem B3010661 : Blo 1336987 3010661 := bbase (se 4 (by rfl) ⟨282249, by rfl⟩ : syracuseStep 3010661 = 564499) (by norm_num)
theorem B2289797 : Blo 1336987 2289797 := bbase (se 4 (by rfl) ⟨214668, by rfl⟩ : syracuseStep 2289797 = 429337) (by norm_num)
theorem B2412677 : Blo 1336987 2412677 := bbase (se 4 (by rfl) ⟨226188, by rfl⟩ : syracuseStep 2412677 = 452377) (by norm_num)
theorem B3215501 : Blo 1336987 3215501 := bbase (se 3 (by rfl) ⟨602906, by rfl⟩ : syracuseStep 3215501 = 1205813) (by norm_num)
theorem B1429645 : Blo 1336987 1429645 := bbase (se 3 (by rfl) ⟨268058, by rfl⟩ : syracuseStep 1429645 = 536117) (by norm_num)
theorem B3387541 : Blo 1336987 3387541 := bbase (se 6 (by rfl) ⟨79395, by rfl⟩ : syracuseStep 3387541 = 158791) (by norm_num)
theorem B3010733 : Blo 1336987 3010733 := bbase (se 3 (by rfl) ⟨564512, by rfl⟩ : syracuseStep 3010733 = 1129025) (by norm_num)
theorem B2257085 : Blo 1336987 2257085 := bbase (se 3 (by rfl) ⟨423203, by rfl⟩ : syracuseStep 2257085 = 846407) (by norm_num)
theorem B2412757 : Blo 1336987 2412757 := bbase (se 7 (by rfl) ⟨28274, by rfl⟩ : syracuseStep 2412757 = 56549) (by norm_num)
theorem B1716445 : Blo 1336987 1716445 := bbase (se 3 (by rfl) ⟨321833, by rfl⟩ : syracuseStep 1716445 = 643667) (by norm_num)
theorem B3010805 : Blo 1336987 3010805 := bbase (se 5 (by rfl) ⟨141131, by rfl⟩ : syracuseStep 3010805 = 282263) (by norm_num)
theorem B3387653 : Blo 1336987 3387653 := bbase (se 4 (by rfl) ⟨317592, by rfl⟩ : syracuseStep 3387653 = 635185) (by norm_num)
theorem B2257213 : Blo 1336987 2257213 := bbase (se 3 (by rfl) ⟨423227, by rfl⟩ : syracuseStep 2257213 = 846455) (by norm_num)
theorem B3010877 : Blo 1336987 3010877 := bbase (se 3 (by rfl) ⟨564539, by rfl⟩ : syracuseStep 3010877 = 1129079) (by norm_num)
theorem B3010949 : Blo 1336987 3010949 := bbase (se 4 (by rfl) ⟨282276, by rfl⟩ : syracuseStep 3010949 = 564553) (by norm_num)
theorem B2257301 : Blo 1336987 2257301 := bbase (se 6 (by rfl) ⟨52905, by rfl⟩ : syracuseStep 2257301 = 105811) (by norm_num)
theorem B3387845 : Blo 1336987 3387845 := bbase (se 4 (by rfl) ⟨317610, by rfl⟩ : syracuseStep 3387845 = 635221) (by norm_num)
theorem B4518341 : Blo 1336987 4518341 := bbase (se 4 (by rfl) ⟨423594, by rfl⟩ : syracuseStep 4518341 = 847189) (by norm_num)
theorem B3011021 : Blo 1336987 3011021 := bbase (se 3 (by rfl) ⟨564566, by rfl⟩ : syracuseStep 3011021 = 1129133) (by norm_num)
theorem B1692181 : Blo 1336987 1692181 := bbase (se 6 (by rfl) ⟨39660, by rfl⟩ : syracuseStep 1692181 = 79321) (by norm_num)
theorem B2257429 : Blo 1336987 2257429 := bbase (se 6 (by rfl) ⟨52908, by rfl⟩ : syracuseStep 2257429 = 105817) (by norm_num)
theorem B3011093 : Blo 1336987 3011093 := bbase (se 6 (by rfl) ⟨70572, by rfl⟩ : syracuseStep 3011093 = 141145) (by norm_num)
theorem B3215933 : Blo 1336987 3215933 := bbase (se 3 (by rfl) ⟨602987, by rfl⟩ : syracuseStep 3215933 = 1205975) (by norm_num)
theorem B11424341 : Blo 1336987 11424341 := bbase (se 8 (by rfl) ⟨66939, by rfl⟩ : syracuseStep 11424341 = 133879) (by norm_num)
theorem B3011165 : Blo 1336987 3011165 := bbase (se 3 (by rfl) ⟨564593, by rfl⟩ : syracuseStep 3011165 = 1129187) (by norm_num)
theorem B2257517 : Blo 1336987 2257517 := bbase (se 3 (by rfl) ⟨423284, by rfl⟩ : syracuseStep 2257517 = 846569) (by norm_num)
theorem B3011237 : Blo 1336987 3011237 := bbase (se 4 (by rfl) ⟨282303, by rfl⟩ : syracuseStep 3011237 = 564607) (by norm_num)
theorem B1692353 : Blo 1336987 1692353 := bbase (se 2 (by rfl) ⟨634632, by rfl⟩ : syracuseStep 1692353 = 1269265) (by norm_num)
theorem B1905373 : Blo 1336987 1905373 := bbase (se 3 (by rfl) ⟨357257, by rfl⟩ : syracuseStep 1905373 = 714515) (by norm_num)
theorem B2142949 : Blo 1336987 2142949 := bbase (se 4 (by rfl) ⟨200901, by rfl⟩ : syracuseStep 2142949 = 401803) (by norm_num)
theorem B2257645 : Blo 1336987 2257645 := bbase (se 3 (by rfl) ⟨423308, by rfl⟩ : syracuseStep 2257645 = 846617) (by norm_num)
theorem B3011309 : Blo 1336987 3011309 := bbase (se 3 (by rfl) ⟨564620, by rfl⟩ : syracuseStep 3011309 = 1129241) (by norm_num)
theorem B1692409 : Blo 1336987 1692409 := bbase (se 2 (by rfl) ⟨634653, by rfl⟩ : syracuseStep 1692409 = 1269307) (by norm_num)
theorem B3388189 : Blo 1336987 3388189 := bbase (se 3 (by rfl) ⟨635285, by rfl⟩ : syracuseStep 3388189 = 1270571) (by norm_num)
theorem B3011381 : Blo 1336987 3011381 := bbase (se 5 (by rfl) ⟨141158, by rfl⟩ : syracuseStep 3011381 = 282317) (by norm_num)
theorem B2257733 : Blo 1336987 2257733 := bbase (se 4 (by rfl) ⟨211662, by rfl⟩ : syracuseStep 2257733 = 423325) (by norm_num)
theorem B1692505 : Blo 1336987 1692505 := bbase (se 2 (by rfl) ⟨634689, by rfl⟩ : syracuseStep 1692505 = 1269379) (by norm_num)
theorem B4518773 : Blo 1336987 4518773 := bbase (se 5 (by rfl) ⟨211817, by rfl⟩ : syracuseStep 4518773 = 423635) (by norm_num)
theorem B3011453 : Blo 1336987 3011453 := bbase (se 3 (by rfl) ⟨564647, by rfl⟩ : syracuseStep 3011453 = 1129295) (by norm_num)
theorem B1504129 : Blo 1336987 1504129 := bbase (se 2 (by rfl) ⟨564048, by rfl⟩ : syracuseStep 1504129 = 1128097) (by norm_num)
theorem B3388301 : Blo 1336987 3388301 := bbase (se 3 (by rfl) ⟨635306, by rfl⟩ : syracuseStep 3388301 = 1270613) (by norm_num)
theorem B3216269 : Blo 1336987 3216269 := bbase (se 3 (by rfl) ⟨603050, by rfl⟩ : syracuseStep 3216269 = 1206101) (by norm_num)
theorem B5714837 : Blo 1336987 5714837 := bbase (se 6 (by rfl) ⟨133941, by rfl⟩ : syracuseStep 5714837 = 267883) (by norm_num)
theorem B1504165 : Blo 1336987 1504165 := bbase (se 4 (by rfl) ⟨141015, by rfl⟩ : syracuseStep 1504165 = 282031) (by norm_num)
theorem B3478445 : Blo 1336987 3478445 := bbase (se 3 (by rfl) ⟨652208, by rfl⟩ : syracuseStep 3478445 = 1304417) (by norm_num)
theorem B2257861 : Blo 1336987 2257861 := bbase (se 4 (by rfl) ⟨211674, by rfl⟩ : syracuseStep 2257861 = 423349) (by norm_num)
theorem B3011525 : Blo 1336987 3011525 := bbase (se 4 (by rfl) ⟨282330, by rfl⟩ : syracuseStep 3011525 = 564661) (by norm_num)
theorem B1504201 : Blo 1336987 1504201 := bbase (se 2 (by rfl) ⟨564075, by rfl⟩ : syracuseStep 1504201 = 1128151) (by norm_num)
theorem B3093461 : Blo 1336987 3093461 := bbase (se 7 (by rfl) ⟨36251, by rfl⟩ : syracuseStep 3093461 = 72503) (by norm_num)
theorem B1504237 : Blo 1336987 1504237 := bbase (se 3 (by rfl) ⟨282044, by rfl⟩ : syracuseStep 1504237 = 564089) (by norm_num)
theorem B1692677 : Blo 1336987 1692677 := bbase (se 4 (by rfl) ⟨158688, by rfl⟩ : syracuseStep 1692677 = 317377) (by norm_num)
theorem B3011597 : Blo 1336987 3011597 := bbase (se 3 (by rfl) ⟨564674, by rfl⟩ : syracuseStep 3011597 = 1129349) (by norm_num)
theorem B1504273 : Blo 1336987 1504273 := bbase (se 2 (by rfl) ⟨564102, by rfl⟩ : syracuseStep 1504273 = 1128205) (by norm_num)
theorem B2257949 : Blo 1336987 2257949 := bbase (se 3 (by rfl) ⟨423365, by rfl⟩ : syracuseStep 2257949 = 846731) (by norm_num)
theorem B1905709 : Blo 1336987 1905709 := bbase (se 3 (by rfl) ⟨357320, by rfl⟩ : syracuseStep 1905709 = 714641) (by norm_num)
theorem B1504309 : Blo 1336987 1504309 := bbase (se 5 (by rfl) ⟨70514, by rfl⟩ : syracuseStep 1504309 = 141029) (by norm_num)
theorem B1692733 : Blo 1336987 1692733 := bbase (se 3 (by rfl) ⟨317387, by rfl⟩ : syracuseStep 1692733 = 634775) (by norm_num)
theorem B3388493 : Blo 1336987 3388493 := bbase (se 3 (by rfl) ⟨635342, by rfl⟩ : syracuseStep 3388493 = 1270685) (by norm_num)
theorem B3011669 : Blo 1336987 3011669 := bbase (se 8 (by rfl) ⟨17646, by rfl⟩ : syracuseStep 3011669 = 35293) (by norm_num)
theorem B1504345 : Blo 1336987 1504345 := bbase (se 2 (by rfl) ⟨564129, by rfl⟩ : syracuseStep 1504345 = 1128259) (by norm_num)
theorem B6861941 : Blo 1336987 6861941 := bbase (se 5 (by rfl) ⟨321653, by rfl⟩ : syracuseStep 6861941 = 643307) (by norm_num)
theorem B1504381 : Blo 1336987 1504381 := bbase (se 3 (by rfl) ⟨282071, by rfl⟩ : syracuseStep 1504381 = 564143) (by norm_num)
theorem B1717393 : Blo 1336987 1717393 := bbase (se 2 (by rfl) ⟨644022, by rfl⟩ : syracuseStep 1717393 = 1288045) (by norm_num)
theorem B1692829 : Blo 1336987 1692829 := bbase (se 3 (by rfl) ⟨317405, by rfl⟩ : syracuseStep 1692829 = 634811) (by norm_num)
theorem B2258077 : Blo 1336987 2258077 := bbase (se 3 (by rfl) ⟨423389, by rfl⟩ : syracuseStep 2258077 = 846779) (by norm_num)
theorem B3011741 : Blo 1336987 3011741 := bbase (se 3 (by rfl) ⟨564701, by rfl⟩ : syracuseStep 3011741 = 1129403) (by norm_num)
theorem B1504417 : Blo 1336987 1504417 := bbase (se 2 (by rfl) ⟨564156, by rfl⟩ : syracuseStep 1504417 = 1128313) (by norm_num)
theorem B1504453 : Blo 1336987 1504453 := bbase (se 4 (by rfl) ⟨141042, by rfl⟩ : syracuseStep 1504453 = 282085) (by norm_num)
theorem B3011813 : Blo 1336987 3011813 := bbase (se 4 (by rfl) ⟨282357, by rfl⟩ : syracuseStep 3011813 = 564715) (by norm_num)
theorem B1504489 : Blo 1336987 1504489 := bbase (se 2 (by rfl) ⟨564183, by rfl⟩ : syracuseStep 1504489 = 1128367) (by norm_num)
theorem B2258165 : Blo 1336987 2258165 := bbase (se 5 (by rfl) ⟨105851, by rfl⟩ : syracuseStep 2258165 = 211703) (by norm_num)
theorem B1905925 : Blo 1336987 1905925 := bbase (se 4 (by rfl) ⟨178680, by rfl⟩ : syracuseStep 1905925 = 357361) (by norm_num)
theorem B1504525 : Blo 1336987 1504525 := bbase (se 3 (by rfl) ⟨282098, by rfl⟩ : syracuseStep 1504525 = 564197) (by norm_num)
theorem B3011885 : Blo 1336987 3011885 := bbase (se 3 (by rfl) ⟨564728, by rfl⟩ : syracuseStep 3011885 = 1129457) (by norm_num)
theorem B1504561 : Blo 1336987 1504561 := bbase (se 2 (by rfl) ⟨564210, by rfl⟩ : syracuseStep 1504561 = 1128421) (by norm_num)
theorem B1693001 : Blo 1336987 1693001 := bbase (se 2 (by rfl) ⟨634875, by rfl⟩ : syracuseStep 1693001 = 1269751) (by norm_num)
theorem B1504597 : Blo 1336987 1504597 := bbase (se 13 (by rfl) ⟨275, by rfl⟩ : syracuseStep 1504597 = 551) (by norm_num)
theorem B6772085 : Blo 1336987 6772085 := bbase (se 5 (by rfl) ⟨317441, by rfl⟩ : syracuseStep 6772085 = 634883) (by norm_num)
theorem B2258293 : Blo 1336987 2258293 := bbase (se 5 (by rfl) ⟨105857, by rfl⟩ : syracuseStep 2258293 = 211715) (by norm_num)
theorem B3011957 : Blo 1336987 3011957 := bbase (se 5 (by rfl) ⟨141185, by rfl⟩ : syracuseStep 3011957 = 282371) (by norm_num)
theorem B1504633 : Blo 1336987 1504633 := bbase (se 2 (by rfl) ⟨564237, by rfl⟩ : syracuseStep 1504633 = 1128475) (by norm_num)
theorem B1693057 : Blo 1336987 1693057 := bbase (se 2 (by rfl) ⟨634896, by rfl⟩ : syracuseStep 1693057 = 1269793) (by norm_num)
theorem B2856325 : Blo 1336987 2856325 := bbase (se 4 (by rfl) ⟨267780, by rfl⟩ : syracuseStep 2856325 = 535561) (by norm_num)
theorem B1504669 : Blo 1336987 1504669 := bbase (se 3 (by rfl) ⟨282125, by rfl⟩ : syracuseStep 1504669 = 564251) (by norm_num)
theorem B3388837 : Blo 1336987 3388837 := bbase (se 4 (by rfl) ⟨317703, by rfl⟩ : syracuseStep 3388837 = 635407) (by norm_num)
theorem B3012029 : Blo 1336987 3012029 := bbase (se 3 (by rfl) ⟨564755, by rfl⟩ : syracuseStep 3012029 = 1129511) (by norm_num)
theorem B1504705 : Blo 1336987 1504705 := bbase (se 2 (by rfl) ⟨564264, by rfl⟩ : syracuseStep 1504705 = 1128529) (by norm_num)
theorem B2258381 : Blo 1336987 2258381 := bbase (se 3 (by rfl) ⟨423446, by rfl⟩ : syracuseStep 2258381 = 846893) (by norm_num)
theorem B14464469 : Blo 1336987 14464469 := bbase (se 7 (by rfl) ⟨169505, by rfl⟩ : syracuseStep 14464469 = 339011) (by norm_num)
theorem B1693153 : Blo 1336987 1693153 := bbase (se 2 (by rfl) ⟨634932, by rfl⟩ : syracuseStep 1693153 = 1269865) (by norm_num)
theorem B1504741 : Blo 1336987 1504741 := bbase (se 4 (by rfl) ⟨141069, by rfl⟩ : syracuseStep 1504741 = 282139) (by norm_num)
theorem B3012101 : Blo 1336987 3012101 := bbase (se 4 (by rfl) ⟨282384, by rfl⟩ : syracuseStep 3012101 = 564769) (by norm_num)
theorem B1504777 : Blo 1336987 1504777 := bbase (se 2 (by rfl) ⟨564291, by rfl⟩ : syracuseStep 1504777 = 1128583) (by norm_num)
theorem B3388949 : Blo 1336987 3388949 := bbase (se 6 (by rfl) ⟨79428, by rfl⟩ : syracuseStep 3388949 = 158857) (by norm_num)
theorem B1504813 : Blo 1336987 1504813 := bbase (se 3 (by rfl) ⟨282152, by rfl⟩ : syracuseStep 1504813 = 564305) (by norm_num)
theorem B2258509 : Blo 1336987 2258509 := bbase (se 3 (by rfl) ⟨423470, by rfl⟩ : syracuseStep 2258509 = 846941) (by norm_num)
theorem B3012173 : Blo 1336987 3012173 := bbase (se 3 (by rfl) ⟨564782, by rfl⟩ : syracuseStep 3012173 = 1129565) (by norm_num)
theorem B1504849 : Blo 1336987 1504849 := bbase (se 2 (by rfl) ⟨564318, by rfl⟩ : syracuseStep 1504849 = 1128637) (by norm_num)
theorem B1504885 : Blo 1336987 1504885 := bbase (se 5 (by rfl) ⟨70541, by rfl⟩ : syracuseStep 1504885 = 141083) (by norm_num)
theorem B1906301 : Blo 1336987 1906301 := bbase (se 3 (by rfl) ⟨357431, by rfl⟩ : syracuseStep 1906301 = 714863) (by norm_num)
theorem B1693325 : Blo 1336987 1693325 := bbase (se 3 (by rfl) ⟨317498, by rfl⟩ : syracuseStep 1693325 = 634997) (by norm_num)
theorem B3012245 : Blo 1336987 3012245 := bbase (se 6 (by rfl) ⟨70599, by rfl⟩ : syracuseStep 3012245 = 141199) (by norm_num)
theorem B1504921 : Blo 1336987 1504921 := bbase (se 2 (by rfl) ⟨564345, by rfl⟩ : syracuseStep 1504921 = 1128691) (by norm_num)
theorem B2258597 : Blo 1336987 2258597 := bbase (se 4 (by rfl) ⟨211743, by rfl⟩ : syracuseStep 2258597 = 423487) (by norm_num)
theorem B1504957 : Blo 1336987 1504957 := bbase (se 3 (by rfl) ⟨282179, by rfl⟩ : syracuseStep 1504957 = 564359) (by norm_num)
theorem B1693381 : Blo 1336987 1693381 := bbase (se 4 (by rfl) ⟨158754, by rfl⟩ : syracuseStep 1693381 = 317509) (by norm_num)
theorem B3389141 : Blo 1336987 3389141 := bbase (se 7 (by rfl) ⟨39716, by rfl⟩ : syracuseStep 3389141 = 79433) (by norm_num)
theorem B3012317 : Blo 1336987 3012317 := bbase (se 3 (by rfl) ⟨564809, by rfl⟩ : syracuseStep 3012317 = 1129619) (by norm_num)
theorem B1504993 : Blo 1336987 1504993 := bbase (se 2 (by rfl) ⟨564372, by rfl⟩ : syracuseStep 1504993 = 1128745) (by norm_num)
theorem B2856701 : Blo 1336987 2856701 := bbase (se 3 (by rfl) ⟨535631, by rfl⟩ : syracuseStep 2856701 = 1071263) (by norm_num)
theorem B1505029 : Blo 1336987 1505029 := bbase (se 4 (by rfl) ⟨141096, by rfl⟩ : syracuseStep 1505029 = 282193) (by norm_num)
theorem B1693477 : Blo 1336987 1693477 := bbase (se 4 (by rfl) ⟨158763, by rfl⟩ : syracuseStep 1693477 = 317527) (by norm_num)
theorem B2258725 : Blo 1336987 2258725 := bbase (se 4 (by rfl) ⟨211755, by rfl⟩ : syracuseStep 2258725 = 423511) (by norm_num)
theorem B3012389 : Blo 1336987 3012389 := bbase (se 4 (by rfl) ⟨282411, by rfl⟩ : syracuseStep 3012389 = 564823) (by norm_num)
theorem B1505065 : Blo 1336987 1505065 := bbase (se 2 (by rfl) ⟨564399, by rfl⟩ : syracuseStep 1505065 = 1128799) (by norm_num)
theorem B1505101 : Blo 1336987 1505101 := bbase (se 3 (by rfl) ⟨282206, by rfl⟩ : syracuseStep 1505101 = 564413) (by norm_num)
theorem B3012461 : Blo 1336987 3012461 := bbase (se 3 (by rfl) ⟨564836, by rfl⟩ : syracuseStep 3012461 = 1129673) (by norm_num)
theorem B1505137 : Blo 1336987 1505137 := bbase (se 2 (by rfl) ⟨564426, by rfl⟩ : syracuseStep 1505137 = 1128853) (by norm_num)
theorem B2258813 : Blo 1336987 2258813 := bbase (se 3 (by rfl) ⟨423527, by rfl⟩ : syracuseStep 2258813 = 847055) (by norm_num)
theorem B5420933 : Blo 1336987 5420933 := bbase (se 4 (by rfl) ⟨508212, by rfl⟩ : syracuseStep 5420933 = 1016425) (by norm_num)
theorem B1374085 : Blo 1336987 1374085 := bbase (se 4 (by rfl) ⟨128820, by rfl⟩ : syracuseStep 1374085 = 257641) (by norm_num)
theorem B2144141 : Blo 1336987 2144141 := bbase (se 3 (by rfl) ⟨402026, by rfl⟩ : syracuseStep 2144141 = 804053) (by norm_num)
theorem B1505173 : Blo 1336987 1505173 := bbase (se 6 (by rfl) ⟨35277, by rfl⟩ : syracuseStep 1505173 = 70555) (by norm_num)
theorem B5576597 : Blo 1336987 5576597 := bbase (se 6 (by rfl) ⟨130701, by rfl⟩ : syracuseStep 5576597 = 261403) (by norm_num)
theorem B3094429 : Blo 1336987 3094429 := bbase (se 3 (by rfl) ⟨580205, by rfl⟩ : syracuseStep 3094429 = 1160411) (by norm_num)
theorem B3012533 : Blo 1336987 3012533 := bbase (se 5 (by rfl) ⟨141212, by rfl⟩ : syracuseStep 3012533 = 282425) (by norm_num)
theorem B1505209 : Blo 1336987 1505209 := bbase (se 2 (by rfl) ⟨564453, by rfl⟩ : syracuseStep 1505209 = 1128907) (by norm_num)
theorem B1693649 : Blo 1336987 1693649 := bbase (se 2 (by rfl) ⟨635118, by rfl⟩ : syracuseStep 1693649 = 1270237) (by norm_num)
theorem B1505245 : Blo 1336987 1505245 := bbase (se 3 (by rfl) ⟨282233, by rfl⟩ : syracuseStep 1505245 = 564467) (by norm_num)
theorem B7616501 : Blo 1336987 7616501 := bbase (se 5 (by rfl) ⟨357023, by rfl⟩ : syracuseStep 7616501 = 714047) (by norm_num)
theorem B2258941 : Blo 1336987 2258941 := bbase (se 3 (by rfl) ⟨423551, by rfl⟩ : syracuseStep 2258941 = 847103) (by norm_num)
theorem B3012605 : Blo 1336987 3012605 := bbase (se 3 (by rfl) ⟨564863, by rfl⟩ : syracuseStep 3012605 = 1129727) (by norm_num)
theorem B1505281 : Blo 1336987 1505281 := bbase (se 2 (by rfl) ⟨564480, by rfl⟩ : syracuseStep 1505281 = 1128961) (by norm_num)
theorem B1693705 : Blo 1336987 1693705 := bbase (se 2 (by rfl) ⟨635139, by rfl⟩ : syracuseStep 1693705 = 1270279) (by norm_num)
theorem B1505317 : Blo 1336987 1505317 := bbase (se 4 (by rfl) ⟨141123, by rfl⟩ : syracuseStep 1505317 = 282247) (by norm_num)
theorem B3012677 : Blo 1336987 3012677 := bbase (se 4 (by rfl) ⟨282438, by rfl⟩ : syracuseStep 3012677 = 564877) (by norm_num)
theorem B1505353 : Blo 1336987 1505353 := bbase (se 2 (by rfl) ⟨564507, by rfl⟩ : syracuseStep 1505353 = 1129015) (by norm_num)
theorem B2144333 : Blo 1336987 2144333 := bbase (se 3 (by rfl) ⟨402062, by rfl⟩ : syracuseStep 2144333 = 804125) (by norm_num)
theorem B3807317 : Blo 1336987 3807317 := bbase (se 8 (by rfl) ⟨22308, by rfl⟩ : syracuseStep 3807317 = 44617) (by norm_num)
theorem B2259029 : Blo 1336987 2259029 := bbase (se 8 (by rfl) ⟨13236, by rfl⟩ : syracuseStep 2259029 = 26473) (by norm_num)
theorem B1693801 : Blo 1336987 1693801 := bbase (se 2 (by rfl) ⟨635175, by rfl⟩ : syracuseStep 1693801 = 1270351) (by norm_num)
theorem B1505389 : Blo 1336987 1505389 := bbase (se 3 (by rfl) ⟨282260, by rfl⟩ : syracuseStep 1505389 = 564521) (by norm_num)
theorem B1505425 : Blo 1336987 1505425 := bbase (se 2 (by rfl) ⟨564534, by rfl⟩ : syracuseStep 1505425 = 1129069) (by norm_num)
theorem B1505461 : Blo 1336987 1505461 := bbase (se 5 (by rfl) ⟨70568, by rfl⟩ : syracuseStep 1505461 = 141137) (by norm_num)
theorem B2259157 : Blo 1336987 2259157 := bbase (se 7 (by rfl) ⟨26474, by rfl⟩ : syracuseStep 2259157 = 52949) (by norm_num)
theorem B1505497 : Blo 1336987 1505497 := bbase (se 2 (by rfl) ⟨564561, by rfl⟩ : syracuseStep 1505497 = 1129123) (by norm_num)
theorem B3258613 : Blo 1336987 3258613 := bbase (se 5 (by rfl) ⟨152747, by rfl⟩ : syracuseStep 3258613 = 305495) (by norm_num)
theorem B1505533 : Blo 1336987 1505533 := bbase (se 3 (by rfl) ⟨282287, by rfl⟩ : syracuseStep 1505533 = 564575) (by norm_num)
theorem B2201861 : Blo 1336987 2201861 := bbase (se 4 (by rfl) ⟨206424, by rfl⟩ : syracuseStep 2201861 = 412849) (by norm_num)
theorem B1693973 : Blo 1336987 1693973 := bbase (se 6 (by rfl) ⟨39702, by rfl⟩ : syracuseStep 1693973 = 79405) (by norm_num)
theorem B1505569 : Blo 1336987 1505569 := bbase (se 2 (by rfl) ⟨564588, by rfl⟩ : syracuseStep 1505569 = 1129177) (by norm_num)
theorem B2259245 : Blo 1336987 2259245 := bbase (se 3 (by rfl) ⟨423608, by rfl⟩ : syracuseStep 2259245 = 847217) (by norm_num)
theorem B3807557 : Blo 1336987 3807557 := bbase (se 4 (by rfl) ⟨356958, by rfl⟩ : syracuseStep 3807557 = 713917) (by norm_num)
theorem B1505605 : Blo 1336987 1505605 := bbase (se 4 (by rfl) ⟨141150, by rfl⟩ : syracuseStep 1505605 = 282301) (by norm_num)
theorem B1694029 : Blo 1336987 1694029 := bbase (se 3 (by rfl) ⟨317630, by rfl⟩ : syracuseStep 1694029 = 635261) (by norm_num)
theorem B5077349 : Blo 1336987 5077349 := bbase (se 4 (by rfl) ⟨476001, by rfl⟩ : syracuseStep 5077349 = 952003) (by norm_num)
theorem B1505641 : Blo 1336987 1505641 := bbase (se 2 (by rfl) ⟨564615, by rfl⟩ : syracuseStep 1505641 = 1129231) (by norm_num)
theorem B3619189 : Blo 1336987 3619189 := bbase (se 5 (by rfl) ⟨169649, by rfl⟩ : syracuseStep 3619189 = 339299) (by norm_num)
theorem B1505677 : Blo 1336987 1505677 := bbase (se 3 (by rfl) ⟨282314, by rfl⟩ : syracuseStep 1505677 = 564629) (by norm_num)
theorem B2062757 : Blo 1336987 2062757 := bbase (se 4 (by rfl) ⟨193383, by rfl⟩ : syracuseStep 2062757 = 386767) (by norm_num)
theorem B1694125 : Blo 1336987 1694125 := bbase (se 3 (by rfl) ⟨317648, by rfl⟩ : syracuseStep 1694125 = 635297) (by norm_num)
theorem B2259373 : Blo 1336987 2259373 := bbase (se 3 (by rfl) ⟨423632, by rfl⟩ : syracuseStep 2259373 = 847265) (by norm_num)
theorem B1505713 : Blo 1336987 1505713 := bbase (se 2 (by rfl) ⟨564642, by rfl⟩ : syracuseStep 1505713 = 1129285) (by norm_num)
theorem B4823509 : Blo 1336987 4823509 := bbase (se 7 (by rfl) ⟨56525, by rfl⟩ : syracuseStep 4823509 = 113051) (by norm_num)
theorem B1505749 : Blo 1336987 1505749 := bbase (se 7 (by rfl) ⟨17645, by rfl⟩ : syracuseStep 1505749 = 35291) (by norm_num)
theorem B2005493 : Blo 1336987 2005493 := bbase (se 5 (by rfl) ⟨94007, by rfl⟩ : syracuseStep 2005493 = 188015) (by norm_num)
theorem B1505785 : Blo 1336987 1505785 := bbase (se 2 (by rfl) ⟨564669, by rfl⟩ : syracuseStep 1505785 = 1129339) (by norm_num)
theorem B3807749 : Blo 1336987 3807749 := bbase (se 4 (by rfl) ⟨356976, by rfl⟩ : syracuseStep 3807749 = 713953) (by norm_num)
theorem B2259461 : Blo 1336987 2259461 := bbase (se 4 (by rfl) ⟨211824, by rfl⟩ : syracuseStep 2259461 = 423649) (by norm_num)
theorem B2005517 : Blo 1336987 2005517 := bbase (se 3 (by rfl) ⟨376034, by rfl⟩ : syracuseStep 2005517 = 752069) (by norm_num)
theorem B1505821 : Blo 1336987 1505821 := bbase (se 3 (by rfl) ⟨282341, by rfl⟩ : syracuseStep 1505821 = 564683) (by norm_num)
theorem B2005541 : Blo 1336987 2005541 := bbase (se 4 (by rfl) ⟨188019, by rfl⟩ : syracuseStep 2005541 = 376039) (by norm_num)
theorem B2005565 : Blo 1336987 2005565 := bbase (se 3 (by rfl) ⟨376043, by rfl⟩ : syracuseStep 2005565 = 752087) (by norm_num)
theorem B1505857 : Blo 1336987 1505857 := bbase (se 2 (by rfl) ⟨564696, by rfl⟩ : syracuseStep 1505857 = 1129393) (by norm_num)
theorem B2005589 : Blo 1336987 2005589 := bbase (se 8 (by rfl) ⟨11751, by rfl⟩ : syracuseStep 2005589 = 23503) (by norm_num)
theorem B1694297 : Blo 1336987 1694297 := bbase (se 2 (by rfl) ⟨635361, by rfl⟩ : syracuseStep 1694297 = 1270723) (by norm_num)
theorem B1505893 : Blo 1336987 1505893 := bbase (se 4 (by rfl) ⟨141177, by rfl⟩ : syracuseStep 1505893 = 282355) (by norm_num)
theorem B2005613 : Blo 1336987 2005613 := bbase (se 3 (by rfl) ⟨376052, by rfl⟩ : syracuseStep 2005613 = 752105) (by norm_num)
theorem B2005637 : Blo 1336987 2005637 := bbase (se 4 (by rfl) ⟨188028, by rfl⟩ : syracuseStep 2005637 = 376057) (by norm_num)
theorem B5077637 : Blo 1336987 5077637 := bbase (se 4 (by rfl) ⟨476028, by rfl⟩ : syracuseStep 5077637 = 952057) (by norm_num)
theorem B6773381 : Blo 1336987 6773381 := bbase (se 4 (by rfl) ⟨635004, by rfl⟩ : syracuseStep 6773381 = 1270009) (by norm_num)
theorem B1505929 : Blo 1336987 1505929 := bbase (se 2 (by rfl) ⟨564723, by rfl⟩ : syracuseStep 1505929 = 1129447) (by norm_num)
theorem B1694353 : Blo 1336987 1694353 := bbase (se 2 (by rfl) ⟨635382, by rfl⟩ : syracuseStep 1694353 = 1270765) (by norm_num)
theorem B2005661 : Blo 1336987 2005661 := bbase (se 3 (by rfl) ⟨376061, by rfl⟩ : syracuseStep 2005661 = 752123) (by norm_num)
theorem B1505965 : Blo 1336987 1505965 := bbase (se 3 (by rfl) ⟨282368, by rfl⟩ : syracuseStep 1505965 = 564737) (by norm_num)
theorem B2005685 : Blo 1336987 2005685 := bbase (se 5 (by rfl) ⟨94016, by rfl⟩ : syracuseStep 2005685 = 188033) (by norm_num)
theorem B6273733 : Blo 1336987 6273733 := bbase (se 4 (by rfl) ⟨588162, by rfl⟩ : syracuseStep 6273733 = 1176325) (by norm_num)
theorem B2005709 : Blo 1336987 2005709 := bbase (se 3 (by rfl) ⟨376070, by rfl⟩ : syracuseStep 2005709 = 752141) (by norm_num)
theorem B1506001 : Blo 1336987 1506001 := bbase (se 2 (by rfl) ⟨564750, by rfl⟩ : syracuseStep 1506001 = 1129501) (by norm_num)
theorem B2005733 : Blo 1336987 2005733 := bbase (se 4 (by rfl) ⟨188037, by rfl⟩ : syracuseStep 2005733 = 376075) (by norm_num)
theorem B1694449 : Blo 1336987 1694449 := bbase (se 2 (by rfl) ⟨635418, by rfl⟩ : syracuseStep 1694449 = 1270837) (by norm_num)
theorem B1506037 : Blo 1336987 1506037 := bbase (se 5 (by rfl) ⟨70595, by rfl⟩ : syracuseStep 1506037 = 141191) (by norm_num)
theorem B2005757 : Blo 1336987 2005757 := bbase (se 3 (by rfl) ⟨376079, by rfl⟩ : syracuseStep 2005757 = 752159) (by norm_num)
theorem B2005781 : Blo 1336987 2005781 := bbase (se 6 (by rfl) ⟨47010, by rfl⟩ : syracuseStep 2005781 = 94021) (by norm_num)
theorem B1506073 : Blo 1336987 1506073 := bbase (se 2 (by rfl) ⟨564777, by rfl⟩ : syracuseStep 1506073 = 1129555) (by norm_num)
theorem B2005805 : Blo 1336987 2005805 := bbase (se 3 (by rfl) ⟨376088, by rfl⟩ : syracuseStep 2005805 = 752177) (by norm_num)
theorem B1506109 : Blo 1336987 1506109 := bbase (se 3 (by rfl) ⟨282395, by rfl⟩ : syracuseStep 1506109 = 564791) (by norm_num)
theorem B2005829 : Blo 1336987 2005829 := bbase (se 4 (by rfl) ⟨188046, by rfl⟩ : syracuseStep 2005829 = 376093) (by norm_num)
theorem B2538317 : Blo 1336987 2538317 := bbase (se 3 (by rfl) ⟨475934, by rfl⟩ : syracuseStep 2538317 = 951869) (by norm_num)
theorem B2005853 : Blo 1336987 2005853 := bbase (se 3 (by rfl) ⟨376097, by rfl⟩ : syracuseStep 2005853 = 752195) (by norm_num)
theorem B1506145 : Blo 1336987 1506145 := bbase (se 2 (by rfl) ⟨564804, by rfl⟩ : syracuseStep 1506145 = 1129609) (by norm_num)
theorem B2005877 : Blo 1336987 2005877 := bbase (se 5 (by rfl) ⟨94025, by rfl⟩ : syracuseStep 2005877 = 188051) (by norm_num)
theorem B1506181 : Blo 1336987 1506181 := bbase (se 4 (by rfl) ⟨141204, by rfl⟩ : syracuseStep 1506181 = 282409) (by norm_num)
theorem B2005901 : Blo 1336987 2005901 := bbase (se 3 (by rfl) ⟨376106, by rfl⟩ : syracuseStep 2005901 = 752213) (by norm_num)
theorem B2063261 : Blo 1336987 2063261 := bbase (se 3 (by rfl) ⟨386861, by rfl⟩ : syracuseStep 2063261 = 773723) (by norm_num)
theorem B1694621 : Blo 1336987 1694621 := bbase (se 3 (by rfl) ⟨317741, by rfl⟩ : syracuseStep 1694621 = 635483) (by norm_num)
theorem B2005925 : Blo 1336987 2005925 := bbase (se 4 (by rfl) ⟨188055, by rfl⟩ : syracuseStep 2005925 = 376111) (by norm_num)
theorem B1506217 : Blo 1336987 1506217 := bbase (se 2 (by rfl) ⟨564831, by rfl⟩ : syracuseStep 1506217 = 1129663) (by norm_num)
theorem B2005949 : Blo 1336987 2005949 := bbase (se 3 (by rfl) ⟨376115, by rfl⟩ : syracuseStep 2005949 = 752231) (by norm_num)
theorem B1506253 : Blo 1336987 1506253 := bbase (se 3 (by rfl) ⟨282422, by rfl⟩ : syracuseStep 1506253 = 564845) (by norm_num)
theorem B4512725 : Blo 1336987 4512725 := bbase (se 7 (by rfl) ⟨52883, by rfl⟩ : syracuseStep 4512725 = 105767) (by norm_num)
theorem B2005973 : Blo 1336987 2005973 := bbase (se 7 (by rfl) ⟨23507, by rfl⟩ : syracuseStep 2005973 = 47015) (by norm_num)
theorem B2538469 : Blo 1336987 2538469 := bbase (se 4 (by rfl) ⟨237981, by rfl⟩ : syracuseStep 2538469 = 475963) (by norm_num)
theorem B2005997 : Blo 1336987 2005997 := bbase (se 3 (by rfl) ⟨376124, by rfl⟩ : syracuseStep 2005997 = 752249) (by norm_num)
theorem B1506289 : Blo 1336987 1506289 := bbase (se 2 (by rfl) ⟨564858, by rfl⟩ : syracuseStep 1506289 = 1129717) (by norm_num)
theorem B2006021 : Blo 1336987 2006021 := bbase (se 4 (by rfl) ⟨188064, by rfl⟩ : syracuseStep 2006021 = 376129) (by norm_num)
theorem B1506325 : Blo 1336987 1506325 := bbase (se 6 (by rfl) ⟨35304, by rfl⟩ : syracuseStep 1506325 = 70609) (by norm_num)
theorem B2006045 : Blo 1336987 2006045 := bbase (se 3 (by rfl) ⟨376133, by rfl⟩ : syracuseStep 2006045 = 752267) (by norm_num)
theorem B2710565 : Blo 1336987 2710565 := bbase (se 4 (by rfl) ⟨254115, by rfl⟩ : syracuseStep 2710565 = 508231) (by norm_num)
theorem B2006069 : Blo 1336987 2006069 := bbase (se 5 (by rfl) ⟨94034, by rfl⟩ : syracuseStep 2006069 = 188069) (by norm_num)
theorem B1506361 : Blo 1336987 1506361 := bbase (se 2 (by rfl) ⟨564885, by rfl⟩ : syracuseStep 1506361 = 1129771) (by norm_num)
theorem B2006093 : Blo 1336987 2006093 := bbase (se 3 (by rfl) ⟨376142, by rfl⟩ : syracuseStep 2006093 = 752285) (by norm_num)
theorem B2006117 : Blo 1336987 2006117 := bbase (se 4 (by rfl) ⟨188073, by rfl⟩ : syracuseStep 2006117 = 376147) (by norm_num)
theorem B2006141 : Blo 1336987 2006141 := bbase (se 3 (by rfl) ⟨376151, by rfl⟩ : syracuseStep 2006141 = 752303) (by norm_num)
theorem B2006165 : Blo 1336987 2006165 := bbase (se 6 (by rfl) ⟨47019, by rfl⟩ : syracuseStep 2006165 = 94039) (by norm_num)
theorem B7617685 : Blo 1336987 7617685 := bbase (se 6 (by rfl) ⟨178539, by rfl⟩ : syracuseStep 7617685 = 357079) (by norm_num)
theorem B2006189 : Blo 1336987 2006189 := bbase (se 3 (by rfl) ⟨376160, by rfl⟩ : syracuseStep 2006189 = 752321) (by norm_num)
theorem B2006213 : Blo 1336987 2006213 := bbase (se 4 (by rfl) ⟨188082, by rfl⟩ : syracuseStep 2006213 = 376165) (by norm_num)
theorem B2006237 : Blo 1336987 2006237 := bbase (se 3 (by rfl) ⟨376169, by rfl⟩ : syracuseStep 2006237 = 752339) (by norm_num)
theorem B2006261 : Blo 1336987 2006261 := bbase (se 5 (by rfl) ⟨94043, by rfl⟩ : syracuseStep 2006261 = 188087) (by norm_num)
theorem B2006285 : Blo 1336987 2006285 := bbase (se 3 (by rfl) ⟨376178, by rfl⟩ : syracuseStep 2006285 = 752357) (by norm_num)
theorem B2538773 : Blo 1336987 2538773 := bbase (se 6 (by rfl) ⟨59502, by rfl⟩ : syracuseStep 2538773 = 119005) (by norm_num)
theorem B2006309 : Blo 1336987 2006309 := bbase (se 4 (by rfl) ⟨188091, by rfl⟩ : syracuseStep 2006309 = 376183) (by norm_num)
theorem B2006333 : Blo 1336987 2006333 := bbase (se 3 (by rfl) ⟨376187, by rfl⟩ : syracuseStep 2006333 = 752375) (by norm_num)
theorem B2006357 : Blo 1336987 2006357 := bbase (se 11 (by rfl) ⟨1469, by rfl⟩ : syracuseStep 2006357 = 2939) (by norm_num)
theorem B2858341 : Blo 1336987 2858341 := bbase (se 4 (by rfl) ⟨267969, by rfl⟩ : syracuseStep 2858341 = 535939) (by norm_num)
theorem B2006381 : Blo 1336987 2006381 := bbase (se 3 (by rfl) ⟨376196, by rfl⟩ : syracuseStep 2006381 = 752393) (by norm_num)
theorem B4513157 : Blo 1336987 4513157 := bbase (se 4 (by rfl) ⟨423108, by rfl⟩ : syracuseStep 4513157 = 846217) (by norm_num)
theorem B2006405 : Blo 1336987 2006405 := bbase (se 4 (by rfl) ⟨188100, by rfl⟩ : syracuseStep 2006405 = 376201) (by norm_num)
theorem B2006429 : Blo 1336987 2006429 := bbase (se 3 (by rfl) ⟨376205, by rfl⟩ : syracuseStep 2006429 = 752411) (by norm_num)
theorem B2006453 : Blo 1336987 2006453 := bbase (se 5 (by rfl) ⟨94052, by rfl⟩ : syracuseStep 2006453 = 188105) (by norm_num)
theorem B2006477 : Blo 1336987 2006477 := bbase (se 3 (by rfl) ⟨376214, by rfl⟩ : syracuseStep 2006477 = 752429) (by norm_num)
theorem B3808741 : Blo 1336987 3808741 := bbase (se 4 (by rfl) ⟨357069, by rfl⟩ : syracuseStep 3808741 = 714139) (by norm_num)
theorem B2006501 : Blo 1336987 2006501 := bbase (se 4 (by rfl) ⟨188109, by rfl⟩ : syracuseStep 2006501 = 376219) (by norm_num)
theorem B11427317 : Blo 1336987 11427317 := bbase (se 5 (by rfl) ⟨535655, by rfl⟩ : syracuseStep 11427317 = 1071311) (by norm_num)
theorem B2006525 : Blo 1336987 2006525 := bbase (se 3 (by rfl) ⟨376223, by rfl⟩ : syracuseStep 2006525 = 752447) (by norm_num)
theorem B2006549 : Blo 1336987 2006549 := bbase (se 6 (by rfl) ⟨47028, by rfl⟩ : syracuseStep 2006549 = 94057) (by norm_num)
theorem B2006573 : Blo 1336987 2006573 := bbase (se 3 (by rfl) ⟨376232, by rfl⟩ : syracuseStep 2006573 = 752465) (by norm_num)
theorem B2006597 : Blo 1336987 2006597 := bbase (se 4 (by rfl) ⟨188118, by rfl⟩ : syracuseStep 2006597 = 376237) (by norm_num)
theorem B2006621 : Blo 1336987 2006621 := bbase (se 3 (by rfl) ⟨376241, by rfl⟩ : syracuseStep 2006621 = 752483) (by norm_num)
theorem B2006645 : Blo 1336987 2006645 := bbase (se 5 (by rfl) ⟨94061, by rfl⟩ : syracuseStep 2006645 = 188123) (by norm_num)
theorem B2006669 : Blo 1336987 2006669 := bbase (se 3 (by rfl) ⟨376250, by rfl⟩ : syracuseStep 2006669 = 752501) (by norm_num)
theorem B4284053 : Blo 1336987 4284053 := bbase (se 6 (by rfl) ⟨100407, by rfl⟩ : syracuseStep 4284053 = 200815) (by norm_num)
theorem B2006693 : Blo 1336987 2006693 := bbase (se 4 (by rfl) ⟨188127, by rfl⟩ : syracuseStep 2006693 = 376255) (by norm_num)
theorem B2006717 : Blo 1336987 2006717 := bbase (se 3 (by rfl) ⟨376259, by rfl⟩ : syracuseStep 2006717 = 752519) (by norm_num)
theorem B2006741 : Blo 1336987 2006741 := bbase (se 7 (by rfl) ⟨23516, by rfl⟩ : syracuseStep 2006741 = 47033) (by norm_num)
theorem B2006765 : Blo 1336987 2006765 := bbase (se 3 (by rfl) ⟨376268, by rfl⟩ : syracuseStep 2006765 = 752537) (by norm_num)
theorem B5791493 : Blo 1336987 5791493 := bbase (se 4 (by rfl) ⟨542952, by rfl⟩ : syracuseStep 5791493 = 1085905) (by norm_num)
theorem B2006789 : Blo 1336987 2006789 := bbase (se 4 (by rfl) ⟨188136, by rfl⟩ : syracuseStep 2006789 = 376273) (by norm_num)
theorem B2006813 : Blo 1336987 2006813 := bbase (se 3 (by rfl) ⟨376277, by rfl⟩ : syracuseStep 2006813 = 752555) (by norm_num)
theorem B5078821 : Blo 1336987 5078821 := bbase (se 4 (by rfl) ⟨476139, by rfl⟩ : syracuseStep 5078821 = 952279) (by norm_num)
theorem B4513589 : Blo 1336987 4513589 := bbase (se 5 (by rfl) ⟨211574, by rfl⟩ : syracuseStep 4513589 = 423149) (by norm_num)
theorem B2006837 : Blo 1336987 2006837 := bbase (se 5 (by rfl) ⟨94070, by rfl⟩ : syracuseStep 2006837 = 188141) (by norm_num)
theorem B2006861 : Blo 1336987 2006861 := bbase (se 3 (by rfl) ⟨376286, by rfl⟩ : syracuseStep 2006861 = 752573) (by norm_num)
theorem B2006885 : Blo 1336987 2006885 := bbase (se 4 (by rfl) ⟨188145, by rfl⟩ : syracuseStep 2006885 = 376291) (by norm_num)
theorem B2006909 : Blo 1336987 2006909 := bbase (se 3 (by rfl) ⟨376295, by rfl⟩ : syracuseStep 2006909 = 752591) (by norm_num)
theorem B2006933 : Blo 1336987 2006933 := bbase (se 6 (by rfl) ⟨47037, by rfl⟩ : syracuseStep 2006933 = 94075) (by norm_num)
theorem B6774677 : Blo 1336987 6774677 := bbase (se 6 (by rfl) ⟨158781, by rfl⟩ : syracuseStep 6774677 = 317563) (by norm_num)
theorem B2006957 : Blo 1336987 2006957 := bbase (se 3 (by rfl) ⟨376304, by rfl⟩ : syracuseStep 2006957 = 752609) (by norm_num)
theorem B2006981 : Blo 1336987 2006981 := bbase (se 4 (by rfl) ⟨188154, by rfl⟩ : syracuseStep 2006981 = 376309) (by norm_num)
theorem B2007005 : Blo 1336987 2007005 := bbase (se 3 (by rfl) ⟨376313, by rfl⟩ : syracuseStep 2007005 = 752627) (by norm_num)
theorem B2007029 : Blo 1336987 2007029 := bbase (se 5 (by rfl) ⟨94079, by rfl⟩ : syracuseStep 2007029 = 188159) (by norm_num)
theorem B2007041 : Blo 1336987 2007041 := bstep (se 2 (by rfl) ⟨752640, by rfl⟩ : syracuseStep 2007041 = 1505281) B1505281
theorem B4513805 : Blo 1336987 4513805 := bstep (se 3 (by rfl) ⟨846338, by rfl⟩ : syracuseStep 4513805 = 1692677) B1692677
theorem B2007059 : Blo 1336987 2007059 := bstep (se 1 (by rfl) ⟨1505294, by rfl⟩ : syracuseStep 2007059 = 3010589) B3010589
theorem B2007089 : Blo 1336987 2007089 := bstep (se 2 (by rfl) ⟨752658, by rfl⟩ : syracuseStep 2007089 = 1505317) B1505317
theorem B4513859 : Blo 1336987 4513859 := bstep (se 1 (by rfl) ⟨3385394, by rfl⟩ : syracuseStep 4513859 = 6770789) B6770789
theorem B2007107 : Blo 1336987 2007107 := bstep (se 1 (by rfl) ⟨1505330, by rfl⟩ : syracuseStep 2007107 = 3010661) B3010661
theorem B2007137 : Blo 1336987 2007137 := bstep (se 2 (by rfl) ⟨752676, by rfl⟩ : syracuseStep 2007137 = 1505353) B1505353
theorem B2007155 : Blo 1336987 2007155 := bstep (se 1 (by rfl) ⟨1505366, by rfl⟩ : syracuseStep 2007155 = 3010733) B3010733
theorem B2007185 : Blo 1336987 2007185 := bstep (se 2 (by rfl) ⟨752694, by rfl⟩ : syracuseStep 2007185 = 1505389) B1505389
theorem B2007203 : Blo 1336987 2007203 := bstep (se 1 (by rfl) ⟨1505402, by rfl⟩ : syracuseStep 2007203 = 3010805) B3010805
theorem B2007233 : Blo 1336987 2007233 := bstep (se 2 (by rfl) ⟨752712, by rfl⟩ : syracuseStep 2007233 = 1505425) B1505425
theorem B5718221 : Blo 1336987 5718221 := bstep (se 3 (by rfl) ⟨1072166, by rfl⟩ : syracuseStep 5718221 = 2144333) B2144333
theorem B2007251 : Blo 1336987 2007251 := bstep (se 1 (by rfl) ⟨1505438, by rfl⟩ : syracuseStep 2007251 = 3010877) B3010877
theorem B2007281 : Blo 1336987 2007281 := bstep (se 2 (by rfl) ⟨752730, by rfl⟩ : syracuseStep 2007281 = 1505461) B1505461
theorem B2007299 : Blo 1336987 2007299 := bstep (se 1 (by rfl) ⟨1505474, by rfl⟩ : syracuseStep 2007299 = 3010949) B3010949
theorem B11141389 : Blo 1336987 11141389 := bstep (se 3 (by rfl) ⟨2089010, by rfl⟩ : syracuseStep 11141389 = 4178021) B4178021
theorem B2007329 : Blo 1336987 2007329 := bstep (se 2 (by rfl) ⟨752748, by rfl⟩ : syracuseStep 2007329 = 1505497) B1505497
theorem B2007347 : Blo 1336987 2007347 := bstep (se 1 (by rfl) ⟨1505510, by rfl⟩ : syracuseStep 2007347 = 3011021) B3011021
theorem B4514129 : Blo 1336987 4514129 := bstep (se 2 (by rfl) ⟨1692798, by rfl⟩ : syracuseStep 4514129 = 3385597) B3385597
theorem B2007377 : Blo 1336987 2007377 := bstep (se 2 (by rfl) ⟨752766, by rfl⟩ : syracuseStep 2007377 = 1505533) B1505533
theorem B2007395 : Blo 1336987 2007395 := bstep (se 1 (by rfl) ⟨1505546, by rfl⟩ : syracuseStep 2007395 = 3011093) B3011093
theorem B2007425 : Blo 1336987 2007425 := bstep (se 2 (by rfl) ⟨752784, by rfl⟩ : syracuseStep 2007425 = 1505569) B1505569
theorem B2007443 : Blo 1336987 2007443 := bstep (se 1 (by rfl) ⟨1505582, by rfl⟩ : syracuseStep 2007443 = 3011165) B3011165
theorem B2007473 : Blo 1336987 2007473 := bstep (se 2 (by rfl) ⟨752802, by rfl⟩ : syracuseStep 2007473 = 1505605) B1505605
theorem B15237557 : Blo 1336987 15237557 := bstep (se 5 (by rfl) ⟨714260, by rfl⟩ : syracuseStep 15237557 = 1428521) B1428521
theorem B2007491 : Blo 1336987 2007491 := bstep (se 1 (by rfl) ⟨1505618, by rfl⟩ : syracuseStep 2007491 = 3011237) B3011237
theorem B2712017 : Blo 1336987 2712017 := bstep (se 2 (by rfl) ⟨1017006, by rfl⟩ : syracuseStep 2712017 = 2034013) B2034013
theorem B2007521 : Blo 1336987 2007521 := bstep (se 2 (by rfl) ⟨752820, by rfl⟩ : syracuseStep 2007521 = 1505641) B1505641
theorem B4825585 : Blo 1336987 4825585 := bstep (se 2 (by rfl) ⟨1809594, by rfl⟩ : syracuseStep 4825585 = 3619189) B3619189
theorem B2007539 : Blo 1336987 2007539 := bstep (se 1 (by rfl) ⟨1505654, by rfl⟩ : syracuseStep 2007539 = 3011309) B3011309
theorem B2007569 : Blo 1336987 2007569 := bstep (se 2 (by rfl) ⟨752838, by rfl⟩ : syracuseStep 2007569 = 1505677) B1505677
theorem B2007587 : Blo 1336987 2007587 := bstep (se 1 (by rfl) ⟨1505690, by rfl⟩ : syracuseStep 2007587 = 3011381) B3011381
theorem B2007617 : Blo 1336987 2007617 := bstep (se 2 (by rfl) ⟨752856, by rfl⟩ : syracuseStep 2007617 = 1505713) B1505713
theorem B2007635 : Blo 1336987 2007635 := bstep (se 1 (by rfl) ⟨1505726, by rfl⟩ : syracuseStep 2007635 = 3011453) B3011453
theorem B3809891 : Blo 1336987 3809891 := bstep (se 1 (by rfl) ⟨2857418, by rfl⟩ : syracuseStep 3809891 = 5714837) B5714837
theorem B6431345 : Blo 1336987 6431345 := bstep (se 2 (by rfl) ⟨2411754, by rfl⟩ : syracuseStep 6431345 = 4823509) B4823509
theorem B2007665 : Blo 1336987 2007665 := bstep (se 2 (by rfl) ⟨752874, by rfl⟩ : syracuseStep 2007665 = 1505749) B1505749
theorem B2318963 : Blo 1336987 2318963 := bstep (se 1 (by rfl) ⟨1739222, by rfl⟩ : syracuseStep 2318963 = 3478445) B3478445
theorem B2007683 : Blo 1336987 2007683 := bstep (se 1 (by rfl) ⟨1505762, by rfl⟩ : syracuseStep 2007683 = 3011525) B3011525
theorem B2007713 : Blo 1336987 2007713 := bstep (se 2 (by rfl) ⟨752892, by rfl⟩ : syracuseStep 2007713 = 1505785) B1505785
theorem B2007731 : Blo 1336987 2007731 := bstep (se 1 (by rfl) ⟨1505798, by rfl⟩ : syracuseStep 2007731 = 3011597) B3011597
theorem B2007761 : Blo 1336987 2007761 := bstep (se 2 (by rfl) ⟨752910, by rfl⟩ : syracuseStep 2007761 = 1505821) B1505821
theorem B5079779 : Blo 1336987 5079779 := bstep (se 1 (by rfl) ⟨3809834, by rfl⟩ : syracuseStep 5079779 = 7619669) B7619669
theorem B2007779 : Blo 1336987 2007779 := bstep (se 1 (by rfl) ⟨1505834, by rfl⟩ : syracuseStep 2007779 = 3011669) B3011669
theorem B5079793 : Blo 1336987 5079793 := bstep (se 2 (by rfl) ⟨1904922, by rfl⟩ : syracuseStep 5079793 = 3809845) B3809845
theorem B2007809 : Blo 1336987 2007809 := bstep (se 2 (by rfl) ⟨752928, by rfl⟩ : syracuseStep 2007809 = 1505857) B1505857
theorem B2007827 : Blo 1336987 2007827 := bstep (se 1 (by rfl) ⟨1505870, by rfl⟩ : syracuseStep 2007827 = 3011741) B3011741
theorem B2007857 : Blo 1336987 2007857 := bstep (se 2 (by rfl) ⟨752946, by rfl⟩ : syracuseStep 2007857 = 1505893) B1505893
theorem B2007875 : Blo 1336987 2007875 := bstep (se 1 (by rfl) ⟨1505906, by rfl⟩ : syracuseStep 2007875 = 3011813) B3011813
theorem B2007905 : Blo 1336987 2007905 := bstep (se 2 (by rfl) ⟨752964, by rfl⟩ : syracuseStep 2007905 = 1505929) B1505929
theorem B4514669 : Blo 1336987 4514669 := bstep (se 3 (by rfl) ⟨846500, by rfl⟩ : syracuseStep 4514669 = 1693001) B1693001
theorem B2007923 : Blo 1336987 2007923 := bstep (se 1 (by rfl) ⟨1505942, by rfl⟩ : syracuseStep 2007923 = 3011885) B3011885
theorem B2007953 : Blo 1336987 2007953 := bstep (se 2 (by rfl) ⟨752982, by rfl⟩ : syracuseStep 2007953 = 1505965) B1505965
theorem B4514723 : Blo 1336987 4514723 := bstep (se 1 (by rfl) ⟨3386042, by rfl⟩ : syracuseStep 4514723 = 6772085) B6772085
theorem B2007971 : Blo 1336987 2007971 := bstep (se 1 (by rfl) ⟨1505978, by rfl⟩ : syracuseStep 2007971 = 3011957) B3011957
theorem B8364977 : Blo 1336987 8364977 := bstep (se 2 (by rfl) ⟨3136866, by rfl⟩ : syracuseStep 8364977 = 6273733) B6273733
theorem B2008001 : Blo 1336987 2008001 := bstep (se 2 (by rfl) ⟨753000, by rfl⟩ : syracuseStep 2008001 = 1506001) B1506001
theorem B2540497 : Blo 1336987 2540497 := bstep (se 2 (by rfl) ⟨952686, by rfl⟩ : syracuseStep 2540497 = 1905373) B1905373
theorem B2008019 : Blo 1336987 2008019 := bstep (se 1 (by rfl) ⟨1506014, by rfl⟩ : syracuseStep 2008019 = 3012029) B3012029
theorem B9642979 : Blo 1336987 9642979 := bstep (se 1 (by rfl) ⟨7232234, by rfl⟩ : syracuseStep 9642979 = 14464469) B14464469
theorem B2008049 : Blo 1336987 2008049 := bstep (se 2 (by rfl) ⟨753018, by rfl⟩ : syracuseStep 2008049 = 1506037) B1506037
theorem B2008067 : Blo 1336987 2008067 := bstep (se 1 (by rfl) ⟨1506050, by rfl⟩ : syracuseStep 2008067 = 3012101) B3012101
theorem B2008097 : Blo 1336987 2008097 := bstep (se 2 (by rfl) ⟨753036, by rfl⟩ : syracuseStep 2008097 = 1506073) B1506073
theorem B2008115 : Blo 1336987 2008115 := bstep (se 1 (by rfl) ⟨1506086, by rfl⟩ : syracuseStep 2008115 = 3012173) B3012173
theorem B5710925 : Blo 1336987 5710925 := bstep (se 3 (by rfl) ⟨1070798, by rfl⟩ : syracuseStep 5710925 = 2141597) B2141597
theorem B2008145 : Blo 1336987 2008145 := bstep (se 2 (by rfl) ⟨753054, by rfl⟩ : syracuseStep 2008145 = 1506109) B1506109
theorem B2008163 : Blo 1336987 2008163 := bstep (se 1 (by rfl) ⟨1506122, by rfl⟩ : syracuseStep 2008163 = 3012245) B3012245
theorem B2008193 : Blo 1336987 2008193 := bstep (se 2 (by rfl) ⟨753072, by rfl⟩ : syracuseStep 2008193 = 1506145) B1506145
theorem B2008211 : Blo 1336987 2008211 := bstep (se 1 (by rfl) ⟨1506158, by rfl⟩ : syracuseStep 2008211 = 3012317) B3012317
theorem B4514993 : Blo 1336987 4514993 := bstep (se 2 (by rfl) ⟨1693122, by rfl⟩ : syracuseStep 4514993 = 3386245) B3386245
theorem B2008241 : Blo 1336987 2008241 := bstep (se 2 (by rfl) ⟨753090, by rfl⟩ : syracuseStep 2008241 = 1506181) B1506181
theorem B2008259 : Blo 1336987 2008259 := bstep (se 1 (by rfl) ⟨1506194, by rfl⟩ : syracuseStep 2008259 = 3012389) B3012389
theorem B2008289 : Blo 1336987 2008289 := bstep (se 2 (by rfl) ⟨753108, by rfl⟩ : syracuseStep 2008289 = 1506217) B1506217
theorem B2008307 : Blo 1336987 2008307 := bstep (se 1 (by rfl) ⟨1506230, by rfl⟩ : syracuseStep 2008307 = 3012461) B3012461
theorem B3613955 : Blo 1336987 3613955 := bstep (se 1 (by rfl) ⟨2710466, by rfl⟩ : syracuseStep 3613955 = 5420933) B5420933
theorem B2008337 : Blo 1336987 2008337 := bstep (se 2 (by rfl) ⟨753126, by rfl⟩ : syracuseStep 2008337 = 1506253) B1506253
theorem B2008355 : Blo 1336987 2008355 := bstep (se 1 (by rfl) ⟨1506266, by rfl⟩ : syracuseStep 2008355 = 3012533) B3012533
theorem B3384625 : Blo 1336987 3384625 := bstep (se 2 (by rfl) ⟨1269234, by rfl⟩ : syracuseStep 3384625 = 2538469) B2538469
theorem B2008385 : Blo 1336987 2008385 := bstep (se 2 (by rfl) ⟨753144, by rfl⟩ : syracuseStep 2008385 = 1506289) B1506289
theorem B2008403 : Blo 1336987 2008403 := bstep (se 1 (by rfl) ⟨1506302, by rfl⟩ : syracuseStep 2008403 = 3012605) B3012605
theorem B2540899 : Blo 1336987 2540899 := bstep (se 1 (by rfl) ⟨1905674, by rfl⟩ : syracuseStep 2540899 = 3811349) B3811349
theorem B2008433 : Blo 1336987 2008433 := bstep (se 2 (by rfl) ⟨753162, by rfl⟩ : syracuseStep 2008433 = 1506325) B1506325
theorem B2008451 : Blo 1336987 2008451 := bstep (se 1 (by rfl) ⟨1506338, by rfl⟩ : syracuseStep 2008451 = 3012677) B3012677
theorem B2540945 : Blo 1336987 2540945 := bstep (se 2 (by rfl) ⟨952854, by rfl⟩ : syracuseStep 2540945 = 1905709) B1905709
theorem B2008481 : Blo 1336987 2008481 := bstep (se 2 (by rfl) ⟨753180, by rfl⟩ : syracuseStep 2008481 = 1506361) B1506361
theorem B4343203 : Blo 1336987 4343203 := bstep (se 1 (by rfl) ⟨3257402, by rfl⟩ : syracuseStep 4343203 = 6514805) B6514805
theorem B1467907 : Blo 1336987 1467907 := bstep (se 1 (by rfl) ⟨1100930, by rfl⟩ : syracuseStep 1467907 = 2201861) B2201861
theorem B7620101 : Blo 1336987 7620101 := bstep (se 4 (by rfl) ⟨714384, by rfl⟩ : syracuseStep 7620101 = 1428769) B1428769
theorem B2287169 : Blo 1336987 2287169 := bstep (se 2 (by rfl) ⟨857688, by rfl⟩ : syracuseStep 2287169 = 1715377) B1715377
theorem B3384899 : Blo 1336987 3384899 := bstep (se 1 (by rfl) ⟨2538674, by rfl⟩ : syracuseStep 3384899 = 5077349) B5077349
theorem B1336995 : Blo 1336987 1336995 := bstep (se 1 (by rfl) ⟨1002746, by rfl⟩ : syracuseStep 1336995 = 2005493) B2005493
theorem B2541233 : Blo 1336987 2541233 := bstep (se 2 (by rfl) ⟨952962, by rfl⟩ : syracuseStep 2541233 = 1905925) B1905925
theorem B1337011 : Blo 1336987 1337011 := bstep (se 1 (by rfl) ⟨1002758, by rfl⟩ : syracuseStep 1337011 = 2005517) B2005517
theorem B1337027 : Blo 1336987 1337027 := bstep (se 1 (by rfl) ⟨1002770, by rfl⟩ : syracuseStep 1337027 = 2005541) B2005541
theorem B4515533 : Blo 1336987 4515533 := bstep (se 3 (by rfl) ⟨846662, by rfl⟩ : syracuseStep 4515533 = 1693325) B1693325
theorem B1337043 : Blo 1336987 1337043 := bstep (se 1 (by rfl) ⟨1002782, by rfl⟩ : syracuseStep 1337043 = 2005565) B2005565
theorem B1337059 : Blo 1336987 1337059 := bstep (se 1 (by rfl) ⟨1002794, by rfl⟩ : syracuseStep 1337059 = 2005589) B2005589
theorem B1337075 : Blo 1336987 1337075 := bstep (se 1 (by rfl) ⟨1002806, by rfl⟩ : syracuseStep 1337075 = 2005613) B2005613
theorem B1337091 : Blo 1336987 1337091 := bstep (se 1 (by rfl) ⟨1002818, by rfl⟩ : syracuseStep 1337091 = 2005637) B2005637
theorem B3385091 : Blo 1336987 3385091 := bstep (se 1 (by rfl) ⟨2538818, by rfl⟩ : syracuseStep 3385091 = 5077637) B5077637
theorem B4515587 : Blo 1336987 4515587 := bstep (se 1 (by rfl) ⟨3386690, by rfl⟩ : syracuseStep 4515587 = 6773381) B6773381
theorem B1337107 : Blo 1336987 1337107 := bstep (se 1 (by rfl) ⟨1002830, by rfl⟩ : syracuseStep 1337107 = 2005661) B2005661
theorem B1337123 : Blo 1336987 1337123 := bstep (se 1 (by rfl) ⟨1002842, by rfl⟩ : syracuseStep 1337123 = 2005685) B2005685
theorem B3811121 : Blo 1336987 3811121 := bstep (se 2 (by rfl) ⟨1429170, by rfl⟩ : syracuseStep 3811121 = 2858341) B2858341
theorem B1337139 : Blo 1336987 1337139 := bstep (se 1 (by rfl) ⟨1002854, by rfl⟩ : syracuseStep 1337139 = 2005709) B2005709
theorem B1337155 : Blo 1336987 1337155 := bstep (se 1 (by rfl) ⟨1002866, by rfl⟩ : syracuseStep 1337155 = 2005733) B2005733
theorem B1337171 : Blo 1336987 1337171 := bstep (se 1 (by rfl) ⟨1002878, by rfl⟩ : syracuseStep 1337171 = 2005757) B2005757
theorem B1337187 : Blo 1336987 1337187 := bstep (se 1 (by rfl) ⟨1002890, by rfl⟩ : syracuseStep 1337187 = 2005781) B2005781
theorem B1337203 : Blo 1336987 1337203 := bstep (se 1 (by rfl) ⟨1002902, by rfl⟩ : syracuseStep 1337203 = 2005805) B2005805
theorem B1337219 : Blo 1336987 1337219 := bstep (se 1 (by rfl) ⟨1002914, by rfl⟩ : syracuseStep 1337219 = 2005829) B2005829
theorem B1337235 : Blo 1336987 1337235 := bstep (se 1 (by rfl) ⟨1002926, by rfl⟩ : syracuseStep 1337235 = 2005853) B2005853
theorem B1337251 : Blo 1336987 1337251 := bstep (se 1 (by rfl) ⟨1002938, by rfl⟩ : syracuseStep 1337251 = 2005877) B2005877
theorem B5793713 : Blo 1336987 5793713 := bstep (se 2 (by rfl) ⟨2172642, by rfl⟩ : syracuseStep 5793713 = 4345285) B4345285
theorem B1337267 : Blo 1336987 1337267 := bstep (se 1 (by rfl) ⟨1002950, by rfl⟩ : syracuseStep 1337267 = 2005901) B2005901
theorem B1337283 : Blo 1336987 1337283 := bstep (se 1 (by rfl) ⟨1002962, by rfl⟩ : syracuseStep 1337283 = 2005925) B2005925
theorem B3008465 : Blo 1336987 3008465 := bstep (se 2 (by rfl) ⟨1128174, by rfl⟩ : syracuseStep 3008465 = 2256349) B2256349
theorem B4122577 : Blo 1336987 4122577 := bstep (se 2 (by rfl) ⟨1545966, by rfl⟩ : syracuseStep 4122577 = 3091933) B3091933
theorem B1337299 : Blo 1336987 1337299 := bstep (se 1 (by rfl) ⟨1002974, by rfl⟩ : syracuseStep 1337299 = 2005949) B2005949
theorem B1607635 : Blo 1336987 1607635 := bstep (se 1 (by rfl) ⟨1205726, by rfl⟩ : syracuseStep 1607635 = 2411453) B2411453
theorem B3008483 : Blo 1336987 3008483 := bstep (se 1 (by rfl) ⟨2256362, by rfl⟩ : syracuseStep 3008483 = 4512725) B4512725
theorem B1337315 : Blo 1336987 1337315 := bstep (se 1 (by rfl) ⟨1002986, by rfl⟩ : syracuseStep 1337315 = 2005973) B2005973
theorem B1337331 : Blo 1336987 1337331 := bstep (se 1 (by rfl) ⟨1002998, by rfl⟩ : syracuseStep 1337331 = 2005997) B2005997
theorem B1337347 : Blo 1336987 1337347 := bstep (se 1 (by rfl) ⟨1003010, by rfl⟩ : syracuseStep 1337347 = 2006021) B2006021
theorem B1607683 : Blo 1336987 1607683 := bstep (se 1 (by rfl) ⟨1205762, by rfl⟩ : syracuseStep 1607683 = 2411525) B2411525
theorem B4515857 : Blo 1336987 4515857 := bstep (se 2 (by rfl) ⟨1693446, by rfl⟩ : syracuseStep 4515857 = 3386893) B3386893
theorem B1337363 : Blo 1336987 1337363 := bstep (se 1 (by rfl) ⟨1003022, by rfl⟩ : syracuseStep 1337363 = 2006045) B2006045
theorem B1337379 : Blo 1336987 1337379 := bstep (se 1 (by rfl) ⟨1003034, by rfl⟩ : syracuseStep 1337379 = 2006069) B2006069
theorem B4286513 : Blo 1336987 4286513 := bstep (se 2 (by rfl) ⟨1607442, by rfl⟩ : syracuseStep 4286513 = 3214885) B3214885
theorem B1337395 : Blo 1336987 1337395 := bstep (se 1 (by rfl) ⟨1003046, by rfl⟩ : syracuseStep 1337395 = 2006093) B2006093
theorem B1337411 : Blo 1336987 1337411 := bstep (se 1 (by rfl) ⟨1003058, by rfl⟩ : syracuseStep 1337411 = 2006117) B2006117
theorem B1337427 : Blo 1336987 1337427 := bstep (se 1 (by rfl) ⟨1003070, by rfl⟩ : syracuseStep 1337427 = 2006141) B2006141
theorem B1337443 : Blo 1336987 1337443 := bstep (se 1 (by rfl) ⟨1003082, by rfl⟩ : syracuseStep 1337443 = 2006165) B2006165
theorem B17156195 : Blo 1336987 17156195 := bstep (se 1 (by rfl) ⟨12867146, by rfl⟩ : syracuseStep 17156195 = 25734293) B25734293
theorem B3213425 : Blo 1336987 3213425 := bstep (se 2 (by rfl) ⟨1205034, by rfl⟩ : syracuseStep 3213425 = 2410069) B2410069
theorem B6776945 : Blo 1336987 6776945 := bstep (se 2 (by rfl) ⟨2541354, by rfl⟩ : syracuseStep 6776945 = 5082709) B5082709
theorem B1337459 : Blo 1336987 1337459 := bstep (se 1 (by rfl) ⟨1003094, by rfl⟩ : syracuseStep 1337459 = 2006189) B2006189
theorem B1337475 : Blo 1336987 1337475 := bstep (se 1 (by rfl) ⟨1003106, by rfl⟩ : syracuseStep 1337475 = 2006213) B2006213
theorem B1337491 : Blo 1336987 1337491 := bstep (se 1 (by rfl) ⟨1003118, by rfl⟩ : syracuseStep 1337491 = 2006237) B2006237
theorem B1337507 : Blo 1336987 1337507 := bstep (se 1 (by rfl) ⟨1003130, by rfl⟩ : syracuseStep 1337507 = 2006261) B2006261
theorem B5081251 : Blo 1336987 5081251 := bstep (se 1 (by rfl) ⟨3810938, by rfl⟩ : syracuseStep 5081251 = 7621877) B7621877
theorem B4286641 : Blo 1336987 4286641 := bstep (se 2 (by rfl) ⟨1607490, by rfl⟩ : syracuseStep 4286641 = 3214981) B3214981
theorem B1337523 : Blo 1336987 1337523 := bstep (se 1 (by rfl) ⟨1003142, by rfl⟩ : syracuseStep 1337523 = 2006285) B2006285
theorem B1337539 : Blo 1336987 1337539 := bstep (se 1 (by rfl) ⟨1003154, by rfl⟩ : syracuseStep 1337539 = 2006309) B2006309
theorem B6768845 : Blo 1336987 6768845 := bstep (se 3 (by rfl) ⟨1269158, by rfl⟩ : syracuseStep 6768845 = 2538317) B2538317
theorem B1337555 : Blo 1336987 1337555 := bstep (se 1 (by rfl) ⟨1003166, by rfl⟩ : syracuseStep 1337555 = 2006333) B2006333
theorem B1337571 : Blo 1336987 1337571 := bstep (se 1 (by rfl) ⟨1003178, by rfl⟩ : syracuseStep 1337571 = 2006357) B2006357
theorem B3008753 : Blo 1336987 3008753 := bstep (se 2 (by rfl) ⟨1128282, by rfl⟩ : syracuseStep 3008753 = 2256565) B2256565
theorem B1337587 : Blo 1336987 1337587 := bstep (se 1 (by rfl) ⟨1003190, by rfl⟩ : syracuseStep 1337587 = 2006381) B2006381
theorem B3008771 : Blo 1336987 3008771 := bstep (se 1 (by rfl) ⟨2256578, by rfl⟩ : syracuseStep 3008771 = 4513157) B4513157
theorem B1337603 : Blo 1336987 1337603 := bstep (se 1 (by rfl) ⟨1003202, by rfl⟩ : syracuseStep 1337603 = 2006405) B2006405
theorem B1337619 : Blo 1336987 1337619 := bstep (se 1 (by rfl) ⟨1003214, by rfl⟩ : syracuseStep 1337619 = 2006429) B2006429
theorem B1337635 : Blo 1336987 1337635 := bstep (se 1 (by rfl) ⟨1003226, by rfl⟩ : syracuseStep 1337635 = 2006453) B2006453
theorem B1337651 : Blo 1336987 1337651 := bstep (se 1 (by rfl) ⟨1003238, by rfl⟩ : syracuseStep 1337651 = 2006477) B2006477
theorem B1337667 : Blo 1336987 1337667 := bstep (se 1 (by rfl) ⟨1003250, by rfl⟩ : syracuseStep 1337667 = 2006501) B2006501
theorem B1337683 : Blo 1336987 1337683 := bstep (se 1 (by rfl) ⟨1003262, by rfl⟩ : syracuseStep 1337683 = 2006525) B2006525
theorem B1337699 : Blo 1336987 1337699 := bstep (se 1 (by rfl) ⟨1003274, by rfl⟩ : syracuseStep 1337699 = 2006549) B2006549
theorem B12863843 : Blo 1336987 12863843 := bstep (se 1 (by rfl) ⟨9647882, by rfl⟩ : syracuseStep 12863843 = 19295765) B19295765
theorem B1337715 : Blo 1336987 1337715 := bstep (se 1 (by rfl) ⟨1003286, by rfl⟩ : syracuseStep 1337715 = 2006573) B2006573
theorem B1337731 : Blo 1336987 1337731 := bstep (se 1 (by rfl) ⟨1003298, by rfl⟩ : syracuseStep 1337731 = 2006597) B2006597
theorem B2541955 : Blo 1336987 2541955 := bstep (se 1 (by rfl) ⟨1906466, by rfl⟩ : syracuseStep 2541955 = 3812933) B3812933
theorem B1337747 : Blo 1336987 1337747 := bstep (se 1 (by rfl) ⟨1003310, by rfl⟩ : syracuseStep 1337747 = 2006621) B2006621
theorem B1337763 : Blo 1336987 1337763 := bstep (se 1 (by rfl) ⟨1003322, by rfl⟩ : syracuseStep 1337763 = 2006645) B2006645
theorem B4286897 : Blo 1336987 4286897 := bstep (se 2 (by rfl) ⟨1607586, by rfl⟩ : syracuseStep 4286897 = 3215173) B3215173
theorem B1337779 : Blo 1336987 1337779 := bstep (se 1 (by rfl) ⟨1003334, by rfl⟩ : syracuseStep 1337779 = 2006669) B2006669
theorem B1337795 : Blo 1336987 1337795 := bstep (se 1 (by rfl) ⟨1003346, by rfl⟩ : syracuseStep 1337795 = 2006693) B2006693
theorem B2034115 : Blo 1336987 2034115 := bstep (se 1 (by rfl) ⟨1525586, by rfl⟩ : syracuseStep 2034115 = 3051173) B3051173
theorem B1337811 : Blo 1336987 1337811 := bstep (se 1 (by rfl) ⟨1003358, by rfl⟩ : syracuseStep 1337811 = 2006717) B2006717
theorem B1337827 : Blo 1336987 1337827 := bstep (se 1 (by rfl) ⟨1003370, by rfl⟩ : syracuseStep 1337827 = 2006741) B2006741
theorem B3213809 : Blo 1336987 3213809 := bstep (se 2 (by rfl) ⟨1205178, by rfl⟩ : syracuseStep 3213809 = 2410357) B2410357
theorem B1337843 : Blo 1336987 1337843 := bstep (se 1 (by rfl) ⟨1003382, by rfl⟩ : syracuseStep 1337843 = 2006765) B2006765
theorem B3860995 : Blo 1336987 3860995 := bstep (se 1 (by rfl) ⟨2895746, by rfl⟩ : syracuseStep 3860995 = 5791493) B5791493
theorem B1337859 : Blo 1336987 1337859 := bstep (se 1 (by rfl) ⟨1003394, by rfl⟩ : syracuseStep 1337859 = 2006789) B2006789
theorem B3009041 : Blo 1336987 3009041 := bstep (se 2 (by rfl) ⟨1128390, by rfl⟩ : syracuseStep 3009041 = 2256781) B2256781
theorem B1337875 : Blo 1336987 1337875 := bstep (se 1 (by rfl) ⟨1003406, by rfl⟩ : syracuseStep 1337875 = 2006813) B2006813
theorem B3009059 : Blo 1336987 3009059 := bstep (se 1 (by rfl) ⟨2256794, by rfl⟩ : syracuseStep 3009059 = 4513589) B4513589
theorem B1337891 : Blo 1336987 1337891 := bstep (se 1 (by rfl) ⟨1003418, by rfl⟩ : syracuseStep 1337891 = 2006837) B2006837
theorem B4516397 : Blo 1336987 4516397 := bstep (se 3 (by rfl) ⟨846824, by rfl⟩ : syracuseStep 4516397 = 1693649) B1693649
theorem B1337907 : Blo 1336987 1337907 := bstep (se 1 (by rfl) ⟨1003430, by rfl⟩ : syracuseStep 1337907 = 2006861) B2006861
theorem B1337923 : Blo 1336987 1337923 := bstep (se 1 (by rfl) ⟨1003442, by rfl⟩ : syracuseStep 1337923 = 2006885) B2006885
theorem B1337939 : Blo 1336987 1337939 := bstep (se 1 (by rfl) ⟨1003454, by rfl⟩ : syracuseStep 1337939 = 2006909) B2006909
theorem B1337955 : Blo 1336987 1337955 := bstep (se 1 (by rfl) ⟨1003466, by rfl⟩ : syracuseStep 1337955 = 2006933) B2006933
theorem B4516451 : Blo 1336987 4516451 := bstep (se 1 (by rfl) ⟨3387338, by rfl⟩ : syracuseStep 4516451 = 6774677) B6774677
theorem B1337971 : Blo 1336987 1337971 := bstep (se 1 (by rfl) ⟨1003478, by rfl⟩ : syracuseStep 1337971 = 2006957) B2006957
theorem B1337987 : Blo 1336987 1337987 := bstep (se 1 (by rfl) ⟨1003490, by rfl⟩ : syracuseStep 1337987 = 2006981) B2006981
theorem B1338003 : Blo 1336987 1338003 := bstep (se 1 (by rfl) ⟨1003502, by rfl⟩ : syracuseStep 1338003 = 2007005) B2007005
theorem B1338019 : Blo 1336987 1338019 := bstep (se 1 (by rfl) ⟨1003514, by rfl⟩ : syracuseStep 1338019 = 2007029) B2007029
theorem B1608355 : Blo 1336987 1608355 := bstep (se 1 (by rfl) ⟨1206266, by rfl⟩ : syracuseStep 1608355 = 2412533) B2412533
theorem B3386033 : Blo 1336987 3386033 := bstep (se 2 (by rfl) ⟨1269762, by rfl⟩ : syracuseStep 3386033 = 2539525) B2539525
theorem B1338035 : Blo 1336987 1338035 := bstep (se 1 (by rfl) ⟨1003526, by rfl⟩ : syracuseStep 1338035 = 2007053) B2007053
theorem B3214019 : Blo 1336987 3214019 := bstep (se 1 (by rfl) ⟨2410514, by rfl⟩ : syracuseStep 3214019 = 4821029) B4821029
theorem B1338051 : Blo 1336987 1338051 := bstep (se 1 (by rfl) ⟨1003538, by rfl⟩ : syracuseStep 1338051 = 2007077) B2007077
theorem B1338067 : Blo 1336987 1338067 := bstep (se 1 (by rfl) ⟨1003550, by rfl⟩ : syracuseStep 1338067 = 2007101) B2007101
theorem B5147363 : Blo 1336987 5147363 := bstep (se 1 (by rfl) ⟨3860522, by rfl⟩ : syracuseStep 5147363 = 7721045) B7721045
theorem B3386083 : Blo 1336987 3386083 := bstep (se 1 (by rfl) ⟨2539562, by rfl⟩ : syracuseStep 3386083 = 5079125) B5079125
theorem B1338083 : Blo 1336987 1338083 := bstep (se 1 (by rfl) ⟨1003562, by rfl⟩ : syracuseStep 1338083 = 2007125) B2007125
theorem B3050225 : Blo 1336987 3050225 := bstep (se 2 (by rfl) ⟨1143834, by rfl⟩ : syracuseStep 3050225 = 2287669) B2287669
theorem B1338099 : Blo 1336987 1338099 := bstep (se 1 (by rfl) ⟨1003574, by rfl⟩ : syracuseStep 1338099 = 2007149) B2007149
theorem B1338115 : Blo 1336987 1338115 := bstep (se 1 (by rfl) ⟨1003586, by rfl⟩ : syracuseStep 1338115 = 2007173) B2007173
theorem B1526531 : Blo 1336987 1526531 := bstep (se 1 (by rfl) ⟨1144898, by rfl⟩ : syracuseStep 1526531 = 2289797) B2289797
theorem B3435281 : Blo 1336987 3435281 := bstep (se 2 (by rfl) ⟨1288230, by rfl⟩ : syracuseStep 3435281 = 2576461) B2576461
theorem B1338131 : Blo 1336987 1338131 := bstep (se 1 (by rfl) ⟨1003598, by rfl⟩ : syracuseStep 1338131 = 2007197) B2007197
theorem B46328597 : Blo 1336987 46328597 := bstep (se 6 (by rfl) ⟨1085826, by rfl⟩ : syracuseStep 46328597 = 2171653) B2171653
theorem B1338147 : Blo 1336987 1338147 := bstep (se 1 (by rfl) ⟨1003610, by rfl⟩ : syracuseStep 1338147 = 2007221) B2007221
theorem B3009329 : Blo 1336987 3009329 := bstep (se 2 (by rfl) ⟨1128498, by rfl⟩ : syracuseStep 3009329 = 2256997) B2256997
theorem B1338163 : Blo 1336987 1338163 := bstep (se 1 (by rfl) ⟨1003622, by rfl⟩ : syracuseStep 1338163 = 2007245) B2007245
theorem B3009347 : Blo 1336987 3009347 := bstep (se 1 (by rfl) ⟨2257010, by rfl⟩ : syracuseStep 3009347 = 4514021) B4514021
theorem B1338179 : Blo 1336987 1338179 := bstep (se 1 (by rfl) ⟨1003634, by rfl⟩ : syracuseStep 1338179 = 2007269) B2007269
theorem B1338195 : Blo 1336987 1338195 := bstep (se 1 (by rfl) ⟨1003646, by rfl⟩ : syracuseStep 1338195 = 2007293) B2007293
theorem B1338211 : Blo 1336987 1338211 := bstep (se 1 (by rfl) ⟨1003658, by rfl⟩ : syracuseStep 1338211 = 2007317) B2007317
theorem B3386225 : Blo 1336987 3386225 := bstep (se 2 (by rfl) ⟨1269834, by rfl⟩ : syracuseStep 3386225 = 2539669) B2539669
theorem B4516721 : Blo 1336987 4516721 := bstep (se 2 (by rfl) ⟨1693770, by rfl⟩ : syracuseStep 4516721 = 3387541) B3387541
theorem B1338227 : Blo 1336987 1338227 := bstep (se 1 (by rfl) ⟨1003670, by rfl⟩ : syracuseStep 1338227 = 2007341) B2007341
theorem B1338243 : Blo 1336987 1338243 := bstep (se 1 (by rfl) ⟨1003682, by rfl⟩ : syracuseStep 1338243 = 2007365) B2007365
theorem B1338259 : Blo 1336987 1338259 := bstep (se 1 (by rfl) ⟨1003694, by rfl⟩ : syracuseStep 1338259 = 2007389) B2007389
theorem B1338275 : Blo 1336987 1338275 := bstep (se 1 (by rfl) ⟨1003706, by rfl⟩ : syracuseStep 1338275 = 2007413) B2007413
theorem B1338291 : Blo 1336987 1338291 := bstep (se 1 (by rfl) ⟨1003718, by rfl⟩ : syracuseStep 1338291 = 2007437) B2007437
theorem B1338307 : Blo 1336987 1338307 := bstep (se 1 (by rfl) ⟨1003730, by rfl⟩ : syracuseStep 1338307 = 2007461) B2007461
theorem B8571845 : Blo 1336987 8571845 := bstep (se 4 (by rfl) ⟨803610, by rfl⟩ : syracuseStep 8571845 = 1607221) B1607221
theorem B2288593 : Blo 1336987 2288593 := bstep (se 2 (by rfl) ⟨858222, by rfl⟩ : syracuseStep 2288593 = 1716445) B1716445
theorem B1338323 : Blo 1336987 1338323 := bstep (se 1 (by rfl) ⟨1003742, by rfl⟩ : syracuseStep 1338323 = 2007485) B2007485
theorem B1338339 : Blo 1336987 1338339 := bstep (se 1 (by rfl) ⟨1003754, by rfl⟩ : syracuseStep 1338339 = 2007509) B2007509
theorem B1338355 : Blo 1336987 1338355 := bstep (se 1 (by rfl) ⟨1003766, by rfl⟩ : syracuseStep 1338355 = 2007533) B2007533
theorem B1338371 : Blo 1336987 1338371 := bstep (se 1 (by rfl) ⟨1003778, by rfl⟩ : syracuseStep 1338371 = 2007557) B2007557
theorem B6433805 : Blo 1336987 6433805 := bstep (se 3 (by rfl) ⟨1206338, by rfl⟩ : syracuseStep 6433805 = 2412677) B2412677
theorem B1338387 : Blo 1336987 1338387 := bstep (se 1 (by rfl) ⟨1003790, by rfl⟩ : syracuseStep 1338387 = 2007581) B2007581
theorem B36637717 : Blo 1336987 36637717 := bstep (se 6 (by rfl) ⟨858696, by rfl⟩ : syracuseStep 36637717 = 1717393) B1717393
theorem B1338403 : Blo 1336987 1338403 := bstep (se 1 (by rfl) ⟨1003802, by rfl⟩ : syracuseStep 1338403 = 2007605) B2007605
theorem B1338419 : Blo 1336987 1338419 := bstep (se 1 (by rfl) ⟨1003814, by rfl⟩ : syracuseStep 1338419 = 2007629) B2007629
theorem B1338435 : Blo 1336987 1338435 := bstep (se 1 (by rfl) ⟨1003826, by rfl⟩ : syracuseStep 1338435 = 2007653) B2007653
theorem B3009617 : Blo 1336987 3009617 := bstep (se 2 (by rfl) ⟨1128606, by rfl⟩ : syracuseStep 3009617 = 2257213) B2257213
theorem B1338451 : Blo 1336987 1338451 := bstep (se 1 (by rfl) ⟨1003838, by rfl⟩ : syracuseStep 1338451 = 2007677) B2007677
theorem B3009635 : Blo 1336987 3009635 := bstep (se 1 (by rfl) ⟨2257226, by rfl⟩ : syracuseStep 3009635 = 4514453) B4514453
theorem B1338467 : Blo 1336987 1338467 := bstep (se 1 (by rfl) ⟨1003850, by rfl⟩ : syracuseStep 1338467 = 2007701) B2007701
theorem B1338483 : Blo 1336987 1338483 := bstep (se 1 (by rfl) ⟨1003862, by rfl⟩ : syracuseStep 1338483 = 2007725) B2007725
theorem B1338499 : Blo 1336987 1338499 := bstep (se 1 (by rfl) ⟨1003874, by rfl⟩ : syracuseStep 1338499 = 2007749) B2007749
theorem B1338515 : Blo 1336987 1338515 := bstep (se 1 (by rfl) ⟨1003886, by rfl⟩ : syracuseStep 1338515 = 2007773) B2007773
theorem B1338531 : Blo 1336987 1338531 := bstep (se 1 (by rfl) ⟨1003898, by rfl⟩ : syracuseStep 1338531 = 2007797) B2007797
theorem B1338547 : Blo 1336987 1338547 := bstep (se 1 (by rfl) ⟨1003910, by rfl⟩ : syracuseStep 1338547 = 2007821) B2007821
theorem B1338563 : Blo 1336987 1338563 := bstep (se 1 (by rfl) ⟨1003922, by rfl⟩ : syracuseStep 1338563 = 2007845) B2007845
theorem B1338579 : Blo 1336987 1338579 := bstep (se 1 (by rfl) ⟨1003934, by rfl⟩ : syracuseStep 1338579 = 2007869) B2007869
theorem B1338595 : Blo 1336987 1338595 := bstep (se 1 (by rfl) ⟨1003946, by rfl⟩ : syracuseStep 1338595 = 2007893) B2007893
theorem B3812579 : Blo 1336987 3812579 := bstep (se 1 (by rfl) ⟨2859434, by rfl⟩ : syracuseStep 3812579 = 5718869) B5718869
theorem B1338611 : Blo 1336987 1338611 := bstep (se 1 (by rfl) ⟨1003958, by rfl⟩ : syracuseStep 1338611 = 2007917) B2007917
theorem B1338627 : Blo 1336987 1338627 := bstep (se 1 (by rfl) ⟨1003970, by rfl⟩ : syracuseStep 1338627 = 2007941) B2007941
theorem B14462221 : Blo 1336987 14462221 := bstep (se 3 (by rfl) ⟨2711666, by rfl⟩ : syracuseStep 14462221 = 5423333) B5423333
theorem B1338643 : Blo 1336987 1338643 := bstep (se 1 (by rfl) ⟨1003982, by rfl⟩ : syracuseStep 1338643 = 2007965) B2007965
theorem B1338659 : Blo 1336987 1338659 := bstep (se 1 (by rfl) ⟨1003994, by rfl⟩ : syracuseStep 1338659 = 2007989) B2007989
theorem B1338675 : Blo 1336987 1338675 := bstep (se 1 (by rfl) ⟨1004006, by rfl⟩ : syracuseStep 1338675 = 2008013) B2008013
theorem B1338691 : Blo 1336987 1338691 := bstep (se 1 (by rfl) ⟨1004018, by rfl⟩ : syracuseStep 1338691 = 2008037) B2008037
theorem B1338707 : Blo 1336987 1338707 := bstep (se 1 (by rfl) ⟨1004030, by rfl⟩ : syracuseStep 1338707 = 2008061) B2008061
theorem B1338723 : Blo 1336987 1338723 := bstep (se 1 (by rfl) ⟨1004042, by rfl⟩ : syracuseStep 1338723 = 2008085) B2008085
theorem B2256241 : Blo 1336987 2256241 := bstep (se 2 (by rfl) ⟨846090, by rfl⟩ : syracuseStep 2256241 = 1692181) B1692181
theorem B3009905 : Blo 1336987 3009905 := bstep (se 2 (by rfl) ⟨1128714, by rfl⟩ : syracuseStep 3009905 = 2257429) B2257429
theorem B1338739 : Blo 1336987 1338739 := bstep (se 1 (by rfl) ⟨1004054, by rfl⟩ : syracuseStep 1338739 = 2008109) B2008109
theorem B3009923 : Blo 1336987 3009923 := bstep (se 1 (by rfl) ⟨2257442, by rfl⟩ : syracuseStep 3009923 = 4514885) B4514885
theorem B1338755 : Blo 1336987 1338755 := bstep (se 1 (by rfl) ⟨1004066, by rfl⟩ : syracuseStep 1338755 = 2008133) B2008133
theorem B4517261 : Blo 1336987 4517261 := bstep (se 3 (by rfl) ⟨846986, by rfl⟩ : syracuseStep 4517261 = 1693973) B1693973
theorem B2256275 : Blo 1336987 2256275 := bstep (se 1 (by rfl) ⟨1692206, by rfl⟩ : syracuseStep 2256275 = 3384413) B3384413
theorem B1338771 : Blo 1336987 1338771 := bstep (se 1 (by rfl) ⟨1004078, by rfl⟩ : syracuseStep 1338771 = 2008157) B2008157
theorem B4574627 : Blo 1336987 4574627 := bstep (se 1 (by rfl) ⟨3430970, by rfl⟩ : syracuseStep 4574627 = 6861941) B6861941
theorem B1338787 : Blo 1336987 1338787 := bstep (se 1 (by rfl) ⟨1004090, by rfl⟩ : syracuseStep 1338787 = 2008181) B2008181
theorem B1338803 : Blo 1336987 1338803 := bstep (se 1 (by rfl) ⟨1004102, by rfl⟩ : syracuseStep 1338803 = 2008205) B2008205
theorem B2289091 : Blo 1336987 2289091 := bstep (se 1 (by rfl) ⟨1716818, by rfl⟩ : syracuseStep 2289091 = 3433637) B3433637
theorem B4517315 : Blo 1336987 4517315 := bstep (se 1 (by rfl) ⟨3387986, by rfl⟩ : syracuseStep 4517315 = 6775973) B6775973
theorem B1338819 : Blo 1336987 1338819 := bstep (se 1 (by rfl) ⟨1004114, by rfl⟩ : syracuseStep 1338819 = 2008229) B2008229
theorem B1338835 : Blo 1336987 1338835 := bstep (se 1 (by rfl) ⟨1004126, by rfl⟩ : syracuseStep 1338835 = 2008253) B2008253
theorem B1338851 : Blo 1336987 1338851 := bstep (se 1 (by rfl) ⟨1004138, by rfl⟩ : syracuseStep 1338851 = 2008277) B2008277
theorem B1338867 : Blo 1336987 1338867 := bstep (se 1 (by rfl) ⟨1004150, by rfl⟩ : syracuseStep 1338867 = 2008301) B2008301
theorem B1338883 : Blo 1336987 1338883 := bstep (se 1 (by rfl) ⟨1004162, by rfl⟩ : syracuseStep 1338883 = 2008325) B2008325
theorem B3214865 : Blo 1336987 3214865 := bstep (se 2 (by rfl) ⟨1205574, by rfl⟩ : syracuseStep 3214865 = 2411149) B2411149
theorem B2256403 : Blo 1336987 2256403 := bstep (se 1 (by rfl) ⟨1692302, by rfl⟩ : syracuseStep 2256403 = 3384605) B3384605
theorem B1338899 : Blo 1336987 1338899 := bstep (se 1 (by rfl) ⟨1004174, by rfl⟩ : syracuseStep 1338899 = 2008349) B2008349
theorem B2141731 : Blo 1336987 2141731 := bstep (se 1 (by rfl) ⟨1606298, by rfl⟩ : syracuseStep 2141731 = 3212597) B3212597
theorem B1338915 : Blo 1336987 1338915 := bstep (se 1 (by rfl) ⟨1004186, by rfl⟩ : syracuseStep 1338915 = 2008373) B2008373
theorem B6778403 : Blo 1336987 6778403 := bstep (se 1 (by rfl) ⟨5083802, by rfl⟩ : syracuseStep 6778403 = 10167605) B10167605
theorem B1338931 : Blo 1336987 1338931 := bstep (se 1 (by rfl) ⟨1004198, by rfl⟩ : syracuseStep 1338931 = 2008397) B2008397
theorem B1338947 : Blo 1336987 1338947 := bstep (se 1 (by rfl) ⟨1004210, by rfl⟩ : syracuseStep 1338947 = 2008421) B2008421
theorem B1338963 : Blo 1336987 1338963 := bstep (se 1 (by rfl) ⟨1004222, by rfl⟩ : syracuseStep 1338963 = 2008445) B2008445
theorem B1338979 : Blo 1336987 1338979 := bstep (se 1 (by rfl) ⟨1004234, by rfl⟩ : syracuseStep 1338979 = 2008469) B2008469
theorem B3010193 : Blo 1336987 3010193 := bstep (se 2 (by rfl) ⟨1128822, by rfl⟩ : syracuseStep 3010193 = 2257645) B2257645
theorem B2256545 : Blo 1336987 2256545 := bstep (se 2 (by rfl) ⟨846204, by rfl⟩ : syracuseStep 2256545 = 1692409) B1692409
theorem B3010211 : Blo 1336987 3010211 := bstep (se 1 (by rfl) ⟨2257658, by rfl⟩ : syracuseStep 3010211 = 4515317) B4515317
theorem B2141873 : Blo 1336987 2141873 := bstep (se 2 (by rfl) ⟨803202, by rfl⟩ : syracuseStep 2141873 = 1606405) B1606405
theorem B2141905 : Blo 1336987 2141905 := bstep (se 2 (by rfl) ⟨803214, by rfl⟩ : syracuseStep 2141905 = 1606429) B1606429
theorem B3215057 : Blo 1336987 3215057 := bstep (se 2 (by rfl) ⟨1205646, by rfl⟩ : syracuseStep 3215057 = 2411293) B2411293
theorem B4517585 : Blo 1336987 4517585 := bstep (se 2 (by rfl) ⟨1694094, by rfl⟩ : syracuseStep 4517585 = 3388189) B3388189
theorem B5500685 : Blo 1336987 5500685 := bstep (se 3 (by rfl) ⟨1031378, by rfl⟩ : syracuseStep 5500685 = 2062757) B2062757
theorem B2256673 : Blo 1336987 2256673 := bstep (se 2 (by rfl) ⟨846252, by rfl⟩ : syracuseStep 2256673 = 1692505) B1692505
theorem B2256707 : Blo 1336987 2256707 := bstep (se 1 (by rfl) ⟨1692530, by rfl⟩ : syracuseStep 2256707 = 3385061) B3385061
theorem B15249221 : Blo 1336987 15249221 := bstep (se 4 (by rfl) ⟨1429614, by rfl⟩ : syracuseStep 15249221 = 2859229) B2859229
theorem B3387217 : Blo 1336987 3387217 := bstep (se 2 (by rfl) ⟨1270206, by rfl⟩ : syracuseStep 3387217 = 2540413) B2540413
theorem B1904467 : Blo 1336987 1904467 := bstep (se 1 (by rfl) ⟨1428350, by rfl⟩ : syracuseStep 1904467 = 2856701) B2856701
theorem B97677197 : Blo 1336987 97677197 := bstep (se 3 (by rfl) ⟨18314474, by rfl⟩ : syracuseStep 97677197 = 36628949) B36628949
theorem B1716131 : Blo 1336987 1716131 := bstep (se 1 (by rfl) ⟨1287098, by rfl⟩ : syracuseStep 1716131 = 2574197) B2574197
theorem B3010481 : Blo 1336987 3010481 := bstep (se 2 (by rfl) ⟨1128930, by rfl⟩ : syracuseStep 3010481 = 2257861) B2257861
theorem B1429427 : Blo 1336987 1429427 := bstep (se 1 (by rfl) ⟨1072070, by rfl⟩ : syracuseStep 1429427 = 2144141) B2144141
theorem B2035649 : Blo 1336987 2035649 := bstep (se 2 (by rfl) ⟨763368, by rfl⟩ : syracuseStep 2035649 = 1526737) B1526737
theorem B2256835 : Blo 1336987 2256835 := bstep (se 1 (by rfl) ⟨1692626, by rfl⟩ : syracuseStep 2256835 = 3385253) B3385253
theorem B17379269 : Blo 1336987 17379269 := bstep (se 4 (by rfl) ⟨1629306, by rfl⟩ : syracuseStep 17379269 = 3258613) B3258613
theorem B3010499 : Blo 1336987 3010499 := bstep (se 1 (by rfl) ⟨2257874, by rfl⟩ : syracuseStep 3010499 = 4515749) B4515749
theorem B10153997 : Blo 1336987 10153997 := bstep (se 3 (by rfl) ⟨1903874, by rfl⟩ : syracuseStep 10153997 = 3807749) B3807749
theorem B4067405 : Blo 1336987 4067405 := bstep (se 3 (by rfl) ⟨762638, by rfl⟩ : syracuseStep 4067405 = 1525277) B1525277
theorem B4288589 : Blo 1336987 4288589 := bstep (se 3 (by rfl) ⟨804110, by rfl⟩ : syracuseStep 4288589 = 1608221) B1608221
theorem B2256977 : Blo 1336987 2256977 := bstep (se 2 (by rfl) ⟨846366, by rfl⟩ : syracuseStep 2256977 = 1692733) B1692733
theorem B3387491 : Blo 1336987 3387491 := bstep (se 1 (by rfl) ⟨2540618, by rfl⟩ : syracuseStep 3387491 = 5081237) B5081237
theorem B1355923 : Blo 1336987 1355923 := bstep (se 1 (by rfl) ⟨1016942, by rfl⟩ : syracuseStep 1355923 = 2033885) B2033885
theorem B2257105 : Blo 1336987 2257105 := bstep (se 2 (by rfl) ⟨846414, by rfl⟩ : syracuseStep 2257105 = 1692829) B1692829
theorem B3010769 : Blo 1336987 3010769 := bstep (se 2 (by rfl) ⟨1129038, by rfl⟩ : syracuseStep 3010769 = 2258077) B2258077
theorem B3010787 : Blo 1336987 3010787 := bstep (se 1 (by rfl) ⟨2258090, by rfl⟩ : syracuseStep 3010787 = 4516181) B4516181
theorem B4518125 : Blo 1336987 4518125 := bstep (se 3 (by rfl) ⟨847148, by rfl⟩ : syracuseStep 4518125 = 1694297) B1694297
theorem B2257139 : Blo 1336987 2257139 := bstep (se 1 (by rfl) ⟨1692854, by rfl⟩ : syracuseStep 2257139 = 3385709) B3385709
theorem B3617059 : Blo 1336987 3617059 := bstep (se 1 (by rfl) ⟨2712794, by rfl⟩ : syracuseStep 3617059 = 5425589) B5425589
theorem B3387683 : Blo 1336987 3387683 := bstep (se 1 (by rfl) ⟨2540762, by rfl⟩ : syracuseStep 3387683 = 5081525) B5081525
theorem B4518179 : Blo 1336987 4518179 := bstep (se 1 (by rfl) ⟨3388634, by rfl⟩ : syracuseStep 4518179 = 6777269) B6777269
theorem B7614769 : Blo 1336987 7614769 := bstep (se 2 (by rfl) ⟨2855538, by rfl⟩ : syracuseStep 7614769 = 5711077) B5711077
theorem B5083469 : Blo 1336987 5083469 := bstep (se 3 (by rfl) ⟨953150, by rfl⟩ : syracuseStep 5083469 = 1906301) B1906301
theorem B2257267 : Blo 1336987 2257267 := bstep (se 1 (by rfl) ⟨1692950, by rfl⟩ : syracuseStep 2257267 = 3385901) B3385901
theorem B17134051 : Blo 1336987 17134051 := bstep (se 1 (by rfl) ⟨12850538, by rfl⟩ : syracuseStep 17134051 = 25701077) B25701077
theorem B3011057 : Blo 1336987 3011057 := bstep (se 2 (by rfl) ⟨1129146, by rfl⟩ : syracuseStep 3011057 = 2258293) B2258293
theorem B2257409 : Blo 1336987 2257409 := bstep (se 2 (by rfl) ⟨846528, by rfl⟩ : syracuseStep 2257409 = 1693057) B1693057
theorem B3011075 : Blo 1336987 3011075 := bstep (se 1 (by rfl) ⟨2258306, by rfl⟩ : syracuseStep 3011075 = 4516613) B4516613
theorem B4518449 : Blo 1336987 4518449 := bstep (se 2 (by rfl) ⟨1694418, by rfl⟩ : syracuseStep 4518449 = 3388837) B3388837
theorem B2142833 : Blo 1336987 2142833 := bstep (se 2 (by rfl) ⟨803562, by rfl⟩ : syracuseStep 2142833 = 1607125) B1607125
theorem B2257537 : Blo 1336987 2257537 := bstep (se 2 (by rfl) ⟨846576, by rfl⟩ : syracuseStep 2257537 = 1693153) B1693153
theorem B2257571 : Blo 1336987 2257571 := bstep (se 1 (by rfl) ⟨1693178, by rfl⟩ : syracuseStep 2257571 = 3386357) B3386357
theorem B1807043 : Blo 1336987 1807043 := bstep (se 1 (by rfl) ⟨1355282, by rfl⟩ : syracuseStep 1807043 = 2710565) B2710565
theorem B3011345 : Blo 1336987 3011345 := bstep (se 2 (by rfl) ⟨1129254, by rfl⟩ : syracuseStep 3011345 = 2258509) B2258509
theorem B2257699 : Blo 1336987 2257699 := bstep (se 1 (by rfl) ⟨1693274, by rfl⟩ : syracuseStep 2257699 = 3386549) B3386549
theorem B3011363 : Blo 1336987 3011363 := bstep (se 1 (by rfl) ⟨2258522, by rfl⟩ : syracuseStep 3011363 = 4517045) B4517045
theorem B4289357 : Blo 1336987 4289357 := bstep (se 3 (by rfl) ⟨804254, by rfl⟩ : syracuseStep 4289357 = 1608509) B1608509
theorem B1692515 : Blo 1336987 1692515 := bstep (se 1 (by rfl) ⟨1269386, by rfl⟩ : syracuseStep 1692515 = 2538773) B2538773
theorem B4641677 : Blo 1336987 4641677 := bstep (se 3 (by rfl) ⟨870314, by rfl⟩ : syracuseStep 4641677 = 1740629) B1740629
theorem B1504147 : Blo 1336987 1504147 := bstep (se 1 (by rfl) ⟨1128110, by rfl⟩ : syracuseStep 1504147 = 2256221) B2256221
theorem B2257841 : Blo 1336987 2257841 := bstep (se 2 (by rfl) ⟨846690, by rfl⟩ : syracuseStep 2257841 = 1693381) B1693381
theorem B1905601 : Blo 1336987 1905601 := bstep (se 2 (by rfl) ⟨714600, by rfl⟩ : syracuseStep 1905601 = 1429201) B1429201
theorem B1356787 : Blo 1336987 1356787 := bstep (se 1 (by rfl) ⟨1017590, by rfl⟩ : syracuseStep 1356787 = 2035181) B2035181
theorem B1905697 : Blo 1336987 1905697 := bstep (se 2 (by rfl) ⟨714636, by rfl⟩ : syracuseStep 1905697 = 1429273) B1429273
theorem B1504291 : Blo 1336987 1504291 := bstep (se 1 (by rfl) ⟨1128218, by rfl⟩ : syracuseStep 1504291 = 2256437) B2256437
theorem B6771761 : Blo 1336987 6771761 := bstep (se 2 (by rfl) ⟨2539410, by rfl⟩ : syracuseStep 6771761 = 5078821) B5078821
theorem B2257969 : Blo 1336987 2257969 := bstep (se 2 (by rfl) ⟨846738, by rfl⟩ : syracuseStep 2257969 = 1693477) B1693477
theorem B3011633 : Blo 1336987 3011633 := bstep (se 2 (by rfl) ⟨1129362, by rfl⟩ : syracuseStep 3011633 = 2258725) B2258725
theorem B3011651 : Blo 1336987 3011651 := bstep (se 1 (by rfl) ⟨2258738, by rfl⟩ : syracuseStep 3011651 = 4517477) B4517477
theorem B4518989 : Blo 1336987 4518989 := bstep (se 3 (by rfl) ⟨847310, by rfl⟩ : syracuseStep 4518989 = 1694621) B1694621
theorem B2856017 : Blo 1336987 2856017 := bstep (se 2 (by rfl) ⟨1071006, by rfl⟩ : syracuseStep 2856017 = 2142013) B2142013
theorem B2258003 : Blo 1336987 2258003 := bstep (se 1 (by rfl) ⟨1693502, by rfl⟩ : syracuseStep 2258003 = 3387005) B3387005
theorem B2856035 : Blo 1336987 2856035 := bstep (se 1 (by rfl) ⟨2142026, by rfl⟩ : syracuseStep 2856035 = 4284053) B4284053
theorem B4519043 : Blo 1336987 4519043 := bstep (se 1 (by rfl) ⟨3389282, by rfl⟩ : syracuseStep 4519043 = 6778565) B6778565
theorem B1832113 : Blo 1336987 1832113 := bstep (se 2 (by rfl) ⟨687042, by rfl⟩ : syracuseStep 1832113 = 1374085) B1374085
theorem B1504435 : Blo 1336987 1504435 := bstep (se 1 (by rfl) ⟨1128326, by rfl⟩ : syracuseStep 1504435 = 2256653) B2256653
theorem B4125905 : Blo 1336987 4125905 := bstep (se 2 (by rfl) ⟨1547214, by rfl⟩ : syracuseStep 4125905 = 3094429) B3094429
theorem B3388625 : Blo 1336987 3388625 := bstep (se 2 (by rfl) ⟨1270734, by rfl⟩ : syracuseStep 3388625 = 2541469) B2541469
theorem B2258131 : Blo 1336987 2258131 := bstep (se 1 (by rfl) ⟨1693598, by rfl⟩ : syracuseStep 2258131 = 3387197) B3387197
theorem B3388675 : Blo 1336987 3388675 := bstep (se 1 (by rfl) ⟨2541506, by rfl⟩ : syracuseStep 3388675 = 5083013) B5083013
theorem B1807681 : Blo 1336987 1807681 := bstep (se 2 (by rfl) ⟨677880, by rfl⟩ : syracuseStep 1807681 = 1355761) B1355761
theorem B1504579 : Blo 1336987 1504579 := bstep (se 1 (by rfl) ⟨1128434, by rfl⟩ : syracuseStep 1504579 = 2256869) B2256869
theorem B3011921 : Blo 1336987 3011921 := bstep (se 2 (by rfl) ⟨1129470, by rfl⟩ : syracuseStep 3011921 = 2258941) B2258941
theorem B2258273 : Blo 1336987 2258273 := bstep (se 2 (by rfl) ⟨846852, by rfl⟩ : syracuseStep 2258273 = 1693705) B1693705
theorem B5715299 : Blo 1336987 5715299 := bstep (se 1 (by rfl) ⟨4286474, by rfl⟩ : syracuseStep 5715299 = 8572949) B8572949
theorem B3011939 : Blo 1336987 3011939 := bstep (se 1 (by rfl) ⟨2258954, by rfl⟩ : syracuseStep 3011939 = 4517909) B4517909
theorem B3388817 : Blo 1336987 3388817 := bstep (se 2 (by rfl) ⟨1270806, by rfl⟩ : syracuseStep 3388817 = 2541613) B2541613
theorem B1807795 : Blo 1336987 1807795 := bstep (se 1 (by rfl) ⟨1355846, by rfl⟩ : syracuseStep 1807795 = 2711693) B2711693
theorem B2143667 : Blo 1336987 2143667 := bstep (se 1 (by rfl) ⟨1607750, by rfl⟩ : syracuseStep 2143667 = 3215501) B3215501
theorem B1504723 : Blo 1336987 1504723 := bstep (se 1 (by rfl) ⟨1128542, by rfl⟩ : syracuseStep 1504723 = 2257085) B2257085
theorem B2258401 : Blo 1336987 2258401 := bstep (se 2 (by rfl) ⟨846900, by rfl⟩ : syracuseStep 2258401 = 1693801) B1693801
theorem B2258435 : Blo 1336987 2258435 := bstep (se 1 (by rfl) ⟨1693826, by rfl⟩ : syracuseStep 2258435 = 3387653) B3387653
theorem B1906193 : Blo 1336987 1906193 := bstep (se 2 (by rfl) ⟨714822, by rfl⟩ : syracuseStep 1906193 = 1429645) B1429645
theorem B1693219 : Blo 1336987 1693219 := bstep (se 1 (by rfl) ⟨1269914, by rfl⟩ : syracuseStep 1693219 = 2539829) B2539829
theorem B1504867 : Blo 1336987 1504867 := bstep (se 1 (by rfl) ⟨1128650, by rfl⟩ : syracuseStep 1504867 = 2257301) B2257301
theorem B3012209 : Blo 1336987 3012209 := bstep (se 2 (by rfl) ⟨1129578, by rfl⟩ : syracuseStep 3012209 = 2259157) B2259157
theorem B3217009 : Blo 1336987 3217009 := bstep (se 2 (by rfl) ⟨1206378, by rfl⟩ : syracuseStep 3217009 = 2412757) B2412757
theorem B1693315 : Blo 1336987 1693315 := bstep (se 1 (by rfl) ⟨1269986, by rfl⟩ : syracuseStep 1693315 = 2539973) B2539973
theorem B2258563 : Blo 1336987 2258563 := bstep (se 1 (by rfl) ⟨1693922, by rfl⟩ : syracuseStep 2258563 = 3387845) B3387845
theorem B3012227 : Blo 1336987 3012227 := bstep (se 1 (by rfl) ⟨2259170, by rfl⟩ : syracuseStep 3012227 = 4518341) B4518341
theorem B2143955 : Blo 1336987 2143955 := bstep (se 1 (by rfl) ⟨1607966, by rfl⟩ : syracuseStep 2143955 = 3215933) B3215933
theorem B7616227 : Blo 1336987 7616227 := bstep (se 1 (by rfl) ⟨5712170, by rfl⟩ : syracuseStep 7616227 = 11424341) B11424341
theorem B1505011 : Blo 1336987 1505011 := bstep (se 1 (by rfl) ⟨1128758, by rfl⟩ : syracuseStep 1505011 = 2257517) B2257517
theorem B2258705 : Blo 1336987 2258705 := bstep (se 2 (by rfl) ⟨847014, by rfl⟩ : syracuseStep 2258705 = 1694029) B1694029
theorem B4888355 : Blo 1336987 4888355 := bstep (se 1 (by rfl) ⟨3666266, by rfl⟩ : syracuseStep 4888355 = 7332533) B7332533
theorem B1505155 : Blo 1336987 1505155 := bstep (se 1 (by rfl) ⟨1128866, by rfl⟩ : syracuseStep 1505155 = 2257733) B2257733
theorem B5076877 : Blo 1336987 5076877 := bstep (se 3 (by rfl) ⟨951914, by rfl⟩ : syracuseStep 5076877 = 1903829) B1903829
theorem B2258833 : Blo 1336987 2258833 := bstep (se 2 (by rfl) ⟨847062, by rfl⟩ : syracuseStep 2258833 = 1694125) B1694125
theorem B3012497 : Blo 1336987 3012497 := bstep (se 2 (by rfl) ⟨1129686, by rfl⟩ : syracuseStep 3012497 = 2259373) B2259373
theorem B3012515 : Blo 1336987 3012515 := bstep (se 1 (by rfl) ⟨2259386, by rfl⟩ : syracuseStep 3012515 = 4518773) B4518773
theorem B2258867 : Blo 1336987 2258867 := bstep (se 1 (by rfl) ⟨1694150, by rfl⟩ : syracuseStep 2258867 = 3388301) B3388301
theorem B2144179 : Blo 1336987 2144179 := bstep (se 1 (by rfl) ⟨1608134, by rfl⟩ : syracuseStep 2144179 = 3216269) B3216269
theorem B2062307 : Blo 1336987 2062307 := bstep (se 1 (by rfl) ⟨1546730, by rfl⟩ : syracuseStep 2062307 = 3093461) B3093461
theorem B1505299 : Blo 1336987 1505299 := bstep (se 1 (by rfl) ⟨1128974, by rfl⟩ : syracuseStep 1505299 = 2257949) B2257949
theorem B2258995 : Blo 1336987 2258995 := bstep (se 1 (by rfl) ⟨1694246, by rfl⟩ : syracuseStep 2258995 = 3388493) B3388493
theorem B1693811 : Blo 1336987 1693811 := bstep (se 1 (by rfl) ⟨1270358, by rfl⟩ : syracuseStep 1693811 = 2540717) B2540717
theorem B1448099 : Blo 1336987 1448099 := bstep (se 1 (by rfl) ⟨1086074, by rfl⟩ : syracuseStep 1448099 = 2172149) B2172149
theorem B1505443 : Blo 1336987 1505443 := bstep (se 1 (by rfl) ⟨1129082, by rfl⟩ : syracuseStep 1505443 = 2258165) B2258165
theorem B2259137 : Blo 1336987 2259137 := bstep (se 2 (by rfl) ⟨847176, by rfl⟩ : syracuseStep 2259137 = 1694353) B1694353
theorem B7616753 : Blo 1336987 7616753 := bstep (se 2 (by rfl) ⟨2856282, by rfl⟩ : syracuseStep 7616753 = 5712565) B5712565
theorem B2857265 : Blo 1336987 2857265 := bstep (se 2 (by rfl) ⟨1071474, by rfl⟩ : syracuseStep 2857265 = 2142949) B2142949
theorem B1505587 : Blo 1336987 1505587 := bstep (se 1 (by rfl) ⟨1129190, by rfl⟩ : syracuseStep 1505587 = 2258381) B2258381
theorem B2259265 : Blo 1336987 2259265 := bstep (se 2 (by rfl) ⟨847224, by rfl⟩ : syracuseStep 2259265 = 1694449) B1694449
theorem B2259299 : Blo 1336987 2259299 := bstep (se 1 (by rfl) ⟨1694474, by rfl⟩ : syracuseStep 2259299 = 3388949) B3388949
theorem B8575409 : Blo 1336987 8575409 := bstep (se 2 (by rfl) ⟨3215778, by rfl⟩ : syracuseStep 8575409 = 6431557) B6431557
theorem B1505731 : Blo 1336987 1505731 := bstep (se 1 (by rfl) ⟨1129298, by rfl⟩ : syracuseStep 1505731 = 2258597) B2258597
theorem B7829965 : Blo 1336987 7829965 := bstep (se 3 (by rfl) ⟨1468118, by rfl⟩ : syracuseStep 7829965 = 2936237) B2936237
theorem B6773219 : Blo 1336987 6773219 := bstep (se 1 (by rfl) ⟨5079914, by rfl⟩ : syracuseStep 6773219 = 10159829) B10159829
theorem B2259427 : Blo 1336987 2259427 := bstep (se 1 (by rfl) ⟨1694570, by rfl⟩ : syracuseStep 2259427 = 3389141) B3389141
theorem B2005505 : Blo 1336987 2005505 := bstep (se 2 (by rfl) ⟨752064, by rfl⟩ : syracuseStep 2005505 = 1504129) B1504129
theorem B2005523 : Blo 1336987 2005523 := bstep (se 1 (by rfl) ⟨1504142, by rfl⟩ : syracuseStep 2005523 = 3008285) B3008285
theorem B2005553 : Blo 1336987 2005553 := bstep (se 2 (by rfl) ⟨752082, by rfl⟩ : syracuseStep 2005553 = 1504165) B1504165
theorem B2005571 : Blo 1336987 2005571 := bstep (se 1 (by rfl) ⟨1504178, by rfl⟩ : syracuseStep 2005571 = 3008357) B3008357
theorem B1505875 : Blo 1336987 1505875 := bstep (se 1 (by rfl) ⟨1129406, by rfl⟩ : syracuseStep 1505875 = 2258813) B2258813
theorem B2005601 : Blo 1336987 2005601 := bstep (se 2 (by rfl) ⟨752100, by rfl⟩ : syracuseStep 2005601 = 1504201) B1504201
theorem B3431011 : Blo 1336987 3431011 := bstep (se 1 (by rfl) ⟨2573258, by rfl⟩ : syracuseStep 3431011 = 5146517) B5146517
theorem B3717731 : Blo 1336987 3717731 := bstep (se 1 (by rfl) ⟨2788298, by rfl⟩ : syracuseStep 3717731 = 5576597) B5576597
theorem B2005619 : Blo 1336987 2005619 := bstep (se 1 (by rfl) ⟨1504214, by rfl⟩ : syracuseStep 2005619 = 3008429) B3008429
theorem B4512401 : Blo 1336987 4512401 := bstep (se 2 (by rfl) ⟨1692150, by rfl⟩ : syracuseStep 4512401 = 3384301) B3384301
theorem B2005649 : Blo 1336987 2005649 := bstep (se 2 (by rfl) ⟨752118, by rfl⟩ : syracuseStep 2005649 = 1504237) B1504237
theorem B2005667 : Blo 1336987 2005667 := bstep (se 1 (by rfl) ⟨1504250, by rfl⟩ : syracuseStep 2005667 = 3008501) B3008501
theorem B5077667 : Blo 1336987 5077667 := bstep (se 1 (by rfl) ⟨3808250, by rfl⟩ : syracuseStep 5077667 = 7616501) B7616501
theorem B2005697 : Blo 1336987 2005697 := bstep (se 2 (by rfl) ⟨752136, by rfl⟩ : syracuseStep 2005697 = 1504273) B1504273
theorem B2005715 : Blo 1336987 2005715 := bstep (se 1 (by rfl) ⟨1504286, by rfl⟩ : syracuseStep 2005715 = 3008573) B3008573
theorem B2538211 : Blo 1336987 2538211 := bstep (se 1 (by rfl) ⟨1903658, by rfl⟩ : syracuseStep 2538211 = 3807317) B3807317
theorem B1506019 : Blo 1336987 1506019 := bstep (se 1 (by rfl) ⟨1129514, by rfl⟩ : syracuseStep 1506019 = 2259029) B2259029
theorem B2005745 : Blo 1336987 2005745 := bstep (se 2 (by rfl) ⟨752154, by rfl⟩ : syracuseStep 2005745 = 1504309) B1504309
theorem B2005763 : Blo 1336987 2005763 := bstep (se 1 (by rfl) ⟨1504322, by rfl⟩ : syracuseStep 2005763 = 3008645) B3008645
theorem B2005793 : Blo 1336987 2005793 := bstep (se 2 (by rfl) ⟨752172, by rfl⟩ : syracuseStep 2005793 = 1504345) B1504345
theorem B2005811 : Blo 1336987 2005811 := bstep (se 1 (by rfl) ⟨1504358, by rfl⟩ : syracuseStep 2005811 = 3008717) B3008717
theorem B1694515 : Blo 1336987 1694515 := bstep (se 1 (by rfl) ⟨1270886, by rfl⟩ : syracuseStep 1694515 = 2541773) B2541773
theorem B2005841 : Blo 1336987 2005841 := bstep (se 2 (by rfl) ⟨752190, by rfl⟩ : syracuseStep 2005841 = 1504381) B1504381
theorem B2005859 : Blo 1336987 2005859 := bstep (se 1 (by rfl) ⟨1504394, by rfl⟩ : syracuseStep 2005859 = 3008789) B3008789
theorem B10156913 : Blo 1336987 10156913 := bstep (se 2 (by rfl) ⟨3808842, by rfl⟩ : syracuseStep 10156913 = 7617685) B7617685
theorem B1506163 : Blo 1336987 1506163 := bstep (se 1 (by rfl) ⟨1129622, by rfl⟩ : syracuseStep 1506163 = 2259245) B2259245
theorem B2005889 : Blo 1336987 2005889 := bstep (se 2 (by rfl) ⟨752208, by rfl⟩ : syracuseStep 2005889 = 1504417) B1504417
theorem B2538371 : Blo 1336987 2538371 := bstep (se 1 (by rfl) ⟨1903778, by rfl⟩ : syracuseStep 2538371 = 3807557) B3807557
theorem B2005907 : Blo 1336987 2005907 := bstep (se 1 (by rfl) ⟨1504430, by rfl⟩ : syracuseStep 2005907 = 3008861) B3008861
theorem B1694611 : Blo 1336987 1694611 := bstep (se 1 (by rfl) ⟨1270958, by rfl⟩ : syracuseStep 1694611 = 2541917) B2541917
theorem B2005937 : Blo 1336987 2005937 := bstep (se 2 (by rfl) ⟨752226, by rfl⟩ : syracuseStep 2005937 = 1504453) B1504453
theorem B2005955 : Blo 1336987 2005955 := bstep (se 1 (by rfl) ⟨1504466, by rfl⟩ : syracuseStep 2005955 = 3008933) B3008933
theorem B3808205 : Blo 1336987 3808205 := bstep (se 3 (by rfl) ⟨714038, by rfl⟩ : syracuseStep 3808205 = 1428077) B1428077
theorem B2005985 : Blo 1336987 2005985 := bstep (se 2 (by rfl) ⟨752244, by rfl⟩ : syracuseStep 2005985 = 1504489) B1504489
theorem B2006003 : Blo 1336987 2006003 := bstep (se 1 (by rfl) ⟨1504502, by rfl⟩ : syracuseStep 2006003 = 3009005) B3009005
theorem B1506307 : Blo 1336987 1506307 := bstep (se 1 (by rfl) ⟨1129730, by rfl⟩ : syracuseStep 1506307 = 2259461) B2259461
theorem B2006033 : Blo 1336987 2006033 := bstep (se 2 (by rfl) ⟨752262, by rfl⟩ : syracuseStep 2006033 = 1504525) B1504525
theorem B2006051 : Blo 1336987 2006051 := bstep (se 1 (by rfl) ⟨1504538, by rfl⟩ : syracuseStep 2006051 = 3009077) B3009077
theorem B4283437 : Blo 1336987 4283437 := bstep (se 3 (by rfl) ⟨803144, by rfl⟩ : syracuseStep 4283437 = 1606289) B1606289
theorem B2006081 : Blo 1336987 2006081 := bstep (se 2 (by rfl) ⟨752280, by rfl⟩ : syracuseStep 2006081 = 1504561) B1504561
theorem B2006099 : Blo 1336987 2006099 := bstep (se 1 (by rfl) ⟨1504574, by rfl⟩ : syracuseStep 2006099 = 3009149) B3009149
theorem B2006129 : Blo 1336987 2006129 := bstep (se 2 (by rfl) ⟨752298, by rfl⟩ : syracuseStep 2006129 = 1504597) B1504597
theorem B3808387 : Blo 1336987 3808387 := bstep (se 1 (by rfl) ⟨2856290, by rfl⟩ : syracuseStep 3808387 = 5712581) B5712581
theorem B2006147 : Blo 1336987 2006147 := bstep (se 1 (by rfl) ⟨1504610, by rfl⟩ : syracuseStep 2006147 = 3009221) B3009221
theorem B2006177 : Blo 1336987 2006177 := bstep (se 2 (by rfl) ⟨752316, by rfl⟩ : syracuseStep 2006177 = 1504633) B1504633
theorem B4512941 : Blo 1336987 4512941 := bstep (se 3 (by rfl) ⟨846176, by rfl⟩ : syracuseStep 4512941 = 1692353) B1692353
theorem B3808433 : Blo 1336987 3808433 := bstep (se 2 (by rfl) ⟨1428162, by rfl⟩ : syracuseStep 3808433 = 2856325) B2856325
theorem B2006195 : Blo 1336987 2006195 := bstep (se 1 (by rfl) ⟨1504646, by rfl⟩ : syracuseStep 2006195 = 3009293) B3009293
theorem B7625933 : Blo 1336987 7625933 := bstep (se 3 (by rfl) ⟨1429862, by rfl⟩ : syracuseStep 7625933 = 2859725) B2859725
theorem B2006225 : Blo 1336987 2006225 := bstep (se 2 (by rfl) ⟨752334, by rfl⟩ : syracuseStep 2006225 = 1504669) B1504669
theorem B4512995 : Blo 1336987 4512995 := bstep (se 1 (by rfl) ⟨3384746, by rfl⟩ : syracuseStep 4512995 = 6769493) B6769493
theorem B2006243 : Blo 1336987 2006243 := bstep (se 1 (by rfl) ⟨1504682, by rfl⟩ : syracuseStep 2006243 = 3009365) B3009365
theorem B2006273 : Blo 1336987 2006273 := bstep (se 2 (by rfl) ⟨752352, by rfl⟩ : syracuseStep 2006273 = 1504705) B1504705
theorem B6774029 : Blo 1336987 6774029 := bstep (se 3 (by rfl) ⟨1270130, by rfl⟩ : syracuseStep 6774029 = 2540261) B2540261
theorem B2006291 : Blo 1336987 2006291 := bstep (se 1 (by rfl) ⟨1504718, by rfl⟩ : syracuseStep 2006291 = 3009437) B3009437
theorem B1375507 : Blo 1336987 1375507 := bstep (se 1 (by rfl) ⟨1031630, by rfl⟩ : syracuseStep 1375507 = 2063261) B2063261
theorem B5078321 : Blo 1336987 5078321 := bstep (se 2 (by rfl) ⟨1904370, by rfl⟩ : syracuseStep 5078321 = 3808741) B3808741
theorem B2006321 : Blo 1336987 2006321 := bstep (se 2 (by rfl) ⟨752370, by rfl⟩ : syracuseStep 2006321 = 1504741) B1504741
theorem B5717297 : Blo 1336987 5717297 := bstep (se 2 (by rfl) ⟨2143986, by rfl⟩ : syracuseStep 5717297 = 4287973) B4287973
theorem B2006339 : Blo 1336987 2006339 := bstep (se 1 (by rfl) ⟨1504754, by rfl⟩ : syracuseStep 2006339 = 3009509) B3009509
theorem B2006369 : Blo 1336987 2006369 := bstep (se 2 (by rfl) ⟨752388, by rfl⟩ : syracuseStep 2006369 = 1504777) B1504777
theorem B2006387 : Blo 1336987 2006387 := bstep (se 1 (by rfl) ⟨1504790, by rfl⟩ : syracuseStep 2006387 = 3009581) B3009581
theorem B2006417 : Blo 1336987 2006417 := bstep (se 2 (by rfl) ⟨752406, by rfl⟩ : syracuseStep 2006417 = 1504813) B1504813
theorem B2006435 : Blo 1336987 2006435 := bstep (se 1 (by rfl) ⟨1504826, by rfl⟩ : syracuseStep 2006435 = 3009653) B3009653
theorem B2006465 : Blo 1336987 2006465 := bstep (se 2 (by rfl) ⟨752424, by rfl⟩ : syracuseStep 2006465 = 1504849) B1504849
theorem B2006483 : Blo 1336987 2006483 := bstep (se 1 (by rfl) ⟨1504862, by rfl⟩ : syracuseStep 2006483 = 3009725) B3009725
theorem B4513265 : Blo 1336987 4513265 := bstep (se 2 (by rfl) ⟨1692474, by rfl⟩ : syracuseStep 4513265 = 3384949) B3384949
theorem B2006513 : Blo 1336987 2006513 := bstep (se 2 (by rfl) ⟨752442, by rfl⟩ : syracuseStep 2006513 = 1504885) B1504885
theorem B14466545 : Blo 1336987 14466545 := bstep (se 2 (by rfl) ⟨5424954, by rfl⟩ : syracuseStep 14466545 = 10849909) B10849909
theorem B2006531 : Blo 1336987 2006531 := bstep (se 1 (by rfl) ⟨1504898, by rfl⟩ : syracuseStep 2006531 = 3009797) B3009797
theorem B1629715 : Blo 1336987 1629715 := bstep (se 1 (by rfl) ⟨1222286, by rfl⟩ : syracuseStep 1629715 = 2444573) B2444573
theorem B2006561 : Blo 1336987 2006561 := bstep (se 2 (by rfl) ⟨752460, by rfl⟩ : syracuseStep 2006561 = 1504921) B1504921
theorem B2006579 : Blo 1336987 2006579 := bstep (se 1 (by rfl) ⟨1504934, by rfl⟩ : syracuseStep 2006579 = 3009869) B3009869
theorem B2006609 : Blo 1336987 2006609 := bstep (se 2 (by rfl) ⟨752478, by rfl⟩ : syracuseStep 2006609 = 1504957) B1504957
theorem B2006627 : Blo 1336987 2006627 := bstep (se 1 (by rfl) ⟨1504970, by rfl⟩ : syracuseStep 2006627 = 3009941) B3009941
theorem B2006657 : Blo 1336987 2006657 := bstep (se 2 (by rfl) ⟨752496, by rfl⟩ : syracuseStep 2006657 = 1504993) B1504993
theorem B2006675 : Blo 1336987 2006675 := bstep (se 1 (by rfl) ⟨1505006, by rfl⟩ : syracuseStep 2006675 = 3010013) B3010013
theorem B7618211 : Blo 1336987 7618211 := bstep (se 1 (by rfl) ⟨5713658, by rfl⟩ : syracuseStep 7618211 = 11427317) B11427317
theorem B2006705 : Blo 1336987 2006705 := bstep (se 2 (by rfl) ⟨752514, by rfl⟩ : syracuseStep 2006705 = 1505029) B1505029
theorem B2006723 : Blo 1336987 2006723 := bstep (se 1 (by rfl) ⟨1505042, by rfl⟩ : syracuseStep 2006723 = 3010085) B3010085
theorem B2006753 : Blo 1336987 2006753 := bstep (se 2 (by rfl) ⟨752532, by rfl⟩ : syracuseStep 2006753 = 1505065) B1505065
theorem B4579057 : Blo 1336987 4579057 := bstep (se 2 (by rfl) ⟨1717146, by rfl⟩ : syracuseStep 4579057 = 3434293) B3434293
theorem B2006771 : Blo 1336987 2006771 := bstep (se 1 (by rfl) ⟨1505078, by rfl⟩ : syracuseStep 2006771 = 3010157) B3010157
theorem B2006801 : Blo 1336987 2006801 := bstep (se 2 (by rfl) ⟨752550, by rfl⟩ : syracuseStep 2006801 = 1505101) B1505101
theorem B2006819 : Blo 1336987 2006819 := bstep (se 1 (by rfl) ⟨1505114, by rfl⟩ : syracuseStep 2006819 = 3010229) B3010229
theorem B6430499 : Blo 1336987 6430499 := bstep (se 1 (by rfl) ⟨4822874, by rfl⟩ : syracuseStep 6430499 = 9645749) B9645749
theorem B2006849 : Blo 1336987 2006849 := bstep (se 2 (by rfl) ⟨752568, by rfl⟩ : syracuseStep 2006849 = 1505137) B1505137
theorem B2858819 : Blo 1336987 2858819 := bstep (se 1 (by rfl) ⟨2144114, by rfl⟩ : syracuseStep 2858819 = 4288229) B4288229
theorem B2006867 : Blo 1336987 2006867 := bstep (se 1 (by rfl) ⟨1505150, by rfl⟩ : syracuseStep 2006867 = 3010301) B3010301
theorem B8576867 : Blo 1336987 8576867 := bstep (se 1 (by rfl) ⟨6432650, by rfl⟩ : syracuseStep 8576867 = 12865301) B12865301
theorem B2006897 : Blo 1336987 2006897 := bstep (se 2 (by rfl) ⟨752586, by rfl⟩ : syracuseStep 2006897 = 1505173) B1505173
theorem B2006915 : Blo 1336987 2006915 := bstep (se 1 (by rfl) ⟨1505186, by rfl⟩ : syracuseStep 2006915 = 3010373) B3010373
theorem B2006945 : Blo 1336987 2006945 := bstep (se 2 (by rfl) ⟨752604, by rfl⟩ : syracuseStep 2006945 = 1505209) B1505209
theorem B4284323 : Blo 1336987 4284323 := bstep (se 1 (by rfl) ⟨3213242, by rfl⟩ : syracuseStep 4284323 = 6426485) B6426485
theorem B2539441 : Blo 1336987 2539441 := bstep (se 2 (by rfl) ⟨952290, by rfl⟩ : syracuseStep 2539441 = 1904581) B1904581
theorem B2006963 : Blo 1336987 2006963 := bstep (se 1 (by rfl) ⟨1505222, by rfl⟩ : syracuseStep 2006963 = 3010445) B3010445
theorem B2006993 : Blo 1336987 2006993 := bstep (se 2 (by rfl) ⟨752622, by rfl⟩ : syracuseStep 2006993 = 1505245) B1505245
theorem B2007011 : Blo 1336987 2007011 := bstep (se 1 (by rfl) ⟨1505258, by rfl⟩ : syracuseStep 2007011 = 3010517) B3010517
theorem B6430691 : Blo 1336987 6430691 := bstep (se 1 (by rfl) ⟨4823018, by rfl⟩ : syracuseStep 6430691 = 9646037) B9646037
theorem B2007065 : Blo 1336987 2007065 := bstep (se 2 (by rfl) ⟨752649, by rfl⟩ : syracuseStep 2007065 = 1505299) B1505299
theorem B2711603 : Blo 1336987 2711603 := bstep (se 1 (by rfl) ⟨2033702, by rfl⟩ : syracuseStep 2711603 = 4067405) B4067405
theorem B2859059 : Blo 1336987 2859059 := bstep (se 1 (by rfl) ⟨2144294, by rfl⟩ : syracuseStep 2859059 = 4288589) B4288589
theorem B2007179 : Blo 1336987 2007179 := bstep (se 1 (by rfl) ⟨1505384, by rfl⟩ : syracuseStep 2007179 = 3010769) B3010769
theorem B2007191 : Blo 1336987 2007191 := bstep (se 1 (by rfl) ⟨1505393, by rfl⟩ : syracuseStep 2007191 = 3010787) B3010787
theorem B2007257 : Blo 1336987 2007257 := bstep (se 2 (by rfl) ⟨752721, by rfl⟩ : syracuseStep 2007257 = 1505443) B1505443
theorem B6775001 : Blo 1336987 6775001 := bstep (se 2 (by rfl) ⟨2540625, by rfl⟩ : syracuseStep 6775001 = 5081251) B5081251
theorem B10158371 : Blo 1336987 10158371 := bstep (se 1 (by rfl) ⟨7618778, by rfl⟩ : syracuseStep 10158371 = 15237557) B15237557
theorem B2007371 : Blo 1336987 2007371 := bstep (se 1 (by rfl) ⟨1505528, by rfl⟩ : syracuseStep 2007371 = 3011057) B3011057
theorem B2007383 : Blo 1336987 2007383 := bstep (se 1 (by rfl) ⟨1505537, by rfl⟩ : syracuseStep 2007383 = 3011075) B3011075
theorem B52142453 : Blo 1336987 52142453 := bstep (se 5 (by rfl) ⟨2444177, by rfl⟩ : syracuseStep 52142453 = 4888355) B4888355
theorem B2539927 : Blo 1336987 2539927 := bstep (se 1 (by rfl) ⟨1904945, by rfl⟩ : syracuseStep 2539927 = 3809891) B3809891
theorem B2007449 : Blo 1336987 2007449 := bstep (se 2 (by rfl) ⟨752793, by rfl⟩ : syracuseStep 2007449 = 1505587) B1505587
theorem B2007563 : Blo 1336987 2007563 := bstep (se 1 (by rfl) ⟨1505672, by rfl⟩ : syracuseStep 2007563 = 3011345) B3011345
theorem B2007575 : Blo 1336987 2007575 := bstep (se 1 (by rfl) ⟨1505681, by rfl⟩ : syracuseStep 2007575 = 3011363) B3011363
theorem B2859571 : Blo 1336987 2859571 := bstep (se 1 (by rfl) ⟨2144678, by rfl⟩ : syracuseStep 2859571 = 4289357) B4289357
theorem B2007641 : Blo 1336987 2007641 := bstep (se 2 (by rfl) ⟨752865, by rfl⟩ : syracuseStep 2007641 = 1505731) B1505731
theorem B4514507 : Blo 1336987 4514507 := bstep (se 1 (by rfl) ⟨3385880, by rfl⟩ : syracuseStep 4514507 = 6771761) B6771761
theorem B2007755 : Blo 1336987 2007755 := bstep (se 1 (by rfl) ⟨1505816, by rfl⟩ : syracuseStep 2007755 = 3011633) B3011633
theorem B2007767 : Blo 1336987 2007767 := bstep (se 1 (by rfl) ⟨1505825, by rfl⟩ : syracuseStep 2007767 = 3011651) B3011651
theorem B2007833 : Blo 1336987 2007833 := bstep (se 2 (by rfl) ⟨752937, by rfl⟩ : syracuseStep 2007833 = 1505875) B1505875
theorem B8577893 : Blo 1336987 8577893 := bstep (se 4 (by rfl) ⟨804177, by rfl⟩ : syracuseStep 8577893 = 1608355) B1608355
theorem B2007947 : Blo 1336987 2007947 := bstep (se 1 (by rfl) ⟨1505960, by rfl⟩ : syracuseStep 2007947 = 3011921) B3011921
theorem B3810199 : Blo 1336987 3810199 := bstep (se 1 (by rfl) ⟨2857649, by rfl⟩ : syracuseStep 3810199 = 5715299) B5715299
theorem B2007959 : Blo 1336987 2007959 := bstep (se 1 (by rfl) ⟨1505969, by rfl⟩ : syracuseStep 2007959 = 3011939) B3011939
theorem B3384281 : Blo 1336987 3384281 := bstep (se 2 (by rfl) ⟨1269105, by rfl⟩ : syracuseStep 3384281 = 2538211) B2538211
theorem B4514777 : Blo 1336987 4514777 := bstep (se 2 (by rfl) ⟨1693041, by rfl⟩ : syracuseStep 4514777 = 3386083) B3386083
theorem B2008025 : Blo 1336987 2008025 := bstep (se 2 (by rfl) ⟨753009, by rfl⟩ : syracuseStep 2008025 = 1506019) B1506019
theorem B5080067 : Blo 1336987 5080067 := bstep (se 1 (by rfl) ⟨3810050, by rfl⟩ : syracuseStep 5080067 = 7620101) B7620101
theorem B1524779 : Blo 1336987 1524779 := bstep (se 1 (by rfl) ⟨1143584, by rfl⟩ : syracuseStep 1524779 = 2287169) B2287169
theorem B2008139 : Blo 1336987 2008139 := bstep (se 1 (by rfl) ⟨1506104, by rfl⟩ : syracuseStep 2008139 = 3012209) B3012209
theorem B2008151 : Blo 1336987 2008151 := bstep (se 1 (by rfl) ⟨1506113, by rfl⟩ : syracuseStep 2008151 = 3012227) B3012227
theorem B2008217 : Blo 1336987 2008217 := bstep (se 2 (by rfl) ⟨753081, by rfl⟩ : syracuseStep 2008217 = 1506163) B1506163
theorem B2540747 : Blo 1336987 2540747 := bstep (se 1 (by rfl) ⟨1905560, by rfl⟩ : syracuseStep 2540747 = 3811121) B3811121
theorem B2540801 : Blo 1336987 2540801 := bstep (se 2 (by rfl) ⟨952800, by rfl⟩ : syracuseStep 2540801 = 1905601) B1905601
theorem B24421637 : Blo 1336987 24421637 := bstep (se 4 (by rfl) ⟨2289528, by rfl⟩ : syracuseStep 24421637 = 4579057) B4579057
theorem B2008331 : Blo 1336987 2008331 := bstep (se 1 (by rfl) ⟨1506248, by rfl⟩ : syracuseStep 2008331 = 3012497) B3012497
theorem B2008343 : Blo 1336987 2008343 := bstep (se 1 (by rfl) ⟨1506257, by rfl⟩ : syracuseStep 2008343 = 3012515) B3012515
theorem B2008409 : Blo 1336987 2008409 := bstep (se 2 (by rfl) ⟨753153, by rfl⟩ : syracuseStep 2008409 = 1506307) B1506307
theorem B48850289 : Blo 1336987 48850289 := bstep (se 2 (by rfl) ⟨18318858, by rfl⟩ : syracuseStep 48850289 = 36637717) B36637717
theorem B5711249 : Blo 1336987 5711249 := bstep (se 2 (by rfl) ⟨2141718, by rfl⟩ : syracuseStep 5711249 = 4283437) B4283437
theorem B43394453 : Blo 1336987 43394453 := bstep (se 6 (by rfl) ⟨1017057, by rfl⟩ : syracuseStep 43394453 = 2034115) B2034115
theorem B11437463 : Blo 1336987 11437463 := bstep (se 1 (by rfl) ⟨8578097, by rfl⟩ : syracuseStep 11437463 = 17156195) B17156195
theorem B2442817 : Blo 1336987 2442817 := bstep (se 2 (by rfl) ⟨916056, by rfl⟩ : syracuseStep 2442817 = 1832113) B1832113
theorem B4515479 : Blo 1336987 4515479 := bstep (se 1 (by rfl) ⟨3386609, by rfl⟩ : syracuseStep 4515479 = 6773219) B6773219
theorem B1337003 : Blo 1336987 1337003 := bstep (se 1 (by rfl) ⟨1002752, by rfl⟩ : syracuseStep 1337003 = 2005505) B2005505
theorem B1337015 : Blo 1336987 1337015 := bstep (se 1 (by rfl) ⟨1002761, by rfl⟩ : syracuseStep 1337015 = 2005523) B2005523
theorem B1337035 : Blo 1336987 1337035 := bstep (se 1 (by rfl) ⟨1002776, by rfl⟩ : syracuseStep 1337035 = 2005553) B2005553
theorem B1337047 : Blo 1336987 1337047 := bstep (se 1 (by rfl) ⟨1002785, by rfl⟩ : syracuseStep 1337047 = 2005571) B2005571
theorem B1337067 : Blo 1336987 1337067 := bstep (se 1 (by rfl) ⟨1002800, by rfl⟩ : syracuseStep 1337067 = 2005601) B2005601
theorem B1337079 : Blo 1336987 1337079 := bstep (se 1 (by rfl) ⟨1002809, by rfl⟩ : syracuseStep 1337079 = 2005619) B2005619
theorem B2410241 : Blo 1336987 2410241 := bstep (se 2 (by rfl) ⟨903840, by rfl⟩ : syracuseStep 2410241 = 1807681) B1807681
theorem B3008267 : Blo 1336987 3008267 := bstep (se 1 (by rfl) ⟨2256200, by rfl⟩ : syracuseStep 3008267 = 4512401) B4512401
theorem B1337099 : Blo 1336987 1337099 := bstep (se 1 (by rfl) ⟨1002824, by rfl⟩ : syracuseStep 1337099 = 2005649) B2005649
theorem B1337111 : Blo 1336987 1337111 := bstep (se 1 (by rfl) ⟨1002833, by rfl⟩ : syracuseStep 1337111 = 2005667) B2005667
theorem B3385111 : Blo 1336987 3385111 := bstep (se 1 (by rfl) ⟨2538833, by rfl⟩ : syracuseStep 3385111 = 5077667) B5077667
theorem B1337131 : Blo 1336987 1337131 := bstep (se 1 (by rfl) ⟨1002848, by rfl⟩ : syracuseStep 1337131 = 2005697) B2005697
theorem B6776621 : Blo 1336987 6776621 := bstep (se 3 (by rfl) ⟨1270616, by rfl⟩ : syracuseStep 6776621 = 2541233) B2541233
theorem B1337143 : Blo 1336987 1337143 := bstep (se 1 (by rfl) ⟨1002857, by rfl⟩ : syracuseStep 1337143 = 2005715) B2005715
theorem B3008321 : Blo 1336987 3008321 := bstep (se 2 (by rfl) ⟨1128120, by rfl⟩ : syracuseStep 3008321 = 2256241) B2256241
theorem B1337163 : Blo 1336987 1337163 := bstep (se 1 (by rfl) ⟨1002872, by rfl⟩ : syracuseStep 1337163 = 2005745) B2005745
theorem B2033483 : Blo 1336987 2033483 := bstep (se 1 (by rfl) ⟨1525112, by rfl⟩ : syracuseStep 2033483 = 3050225) B3050225
theorem B1337175 : Blo 1336987 1337175 := bstep (se 1 (by rfl) ⟨1002881, by rfl⟩ : syracuseStep 1337175 = 2005763) B2005763
theorem B4818781 : Blo 1336987 4818781 := bstep (se 3 (by rfl) ⟨903521, by rfl⟩ : syracuseStep 4818781 = 1807043) B1807043
theorem B8570717 : Blo 1336987 8570717 := bstep (se 3 (by rfl) ⟨1607009, by rfl⟩ : syracuseStep 8570717 = 3214019) B3214019
theorem B30885731 : Blo 1336987 30885731 := bstep (se 1 (by rfl) ⟨23164298, by rfl⟩ : syracuseStep 30885731 = 46328597) B46328597
theorem B1337195 : Blo 1336987 1337195 := bstep (se 1 (by rfl) ⟨1002896, by rfl⟩ : syracuseStep 1337195 = 2005793) B2005793
theorem B1337207 : Blo 1336987 1337207 := bstep (se 1 (by rfl) ⟨1002905, by rfl⟩ : syracuseStep 1337207 = 2005811) B2005811
theorem B1337227 : Blo 1336987 1337227 := bstep (se 1 (by rfl) ⟨1002920, by rfl⟩ : syracuseStep 1337227 = 2005841) B2005841
theorem B1337239 : Blo 1336987 1337239 := bstep (se 1 (by rfl) ⟨1002929, by rfl⟩ : syracuseStep 1337239 = 2005859) B2005859
theorem B2410393 : Blo 1336987 2410393 := bstep (se 2 (by rfl) ⟨903897, by rfl⟩ : syracuseStep 2410393 = 1807795) B1807795
theorem B1337259 : Blo 1336987 1337259 := bstep (se 1 (by rfl) ⟨1002944, by rfl⟩ : syracuseStep 1337259 = 2005889) B2005889
theorem B1337271 : Blo 1336987 1337271 := bstep (se 1 (by rfl) ⟨1002953, by rfl⟩ : syracuseStep 1337271 = 2005907) B2005907
theorem B1337291 : Blo 1336987 1337291 := bstep (se 1 (by rfl) ⟨1002968, by rfl⟩ : syracuseStep 1337291 = 2005937) B2005937
theorem B1337303 : Blo 1336987 1337303 := bstep (se 1 (by rfl) ⟨1002977, by rfl⟩ : syracuseStep 1337303 = 2005955) B2005955
theorem B1337323 : Blo 1336987 1337323 := bstep (se 1 (by rfl) ⟨1002992, by rfl⟩ : syracuseStep 1337323 = 2005985) B2005985
theorem B1337335 : Blo 1336987 1337335 := bstep (se 1 (by rfl) ⟨1003001, by rfl⟩ : syracuseStep 1337335 = 2006003) B2006003
theorem B1337355 : Blo 1336987 1337355 := bstep (se 1 (by rfl) ⟨1003016, by rfl⟩ : syracuseStep 1337355 = 2006033) B2006033
theorem B1337367 : Blo 1336987 1337367 := bstep (se 1 (by rfl) ⟨1003025, by rfl⟩ : syracuseStep 1337367 = 2006051) B2006051
theorem B3008537 : Blo 1336987 3008537 := bstep (se 2 (by rfl) ⟨1128201, by rfl⟩ : syracuseStep 3008537 = 2256403) B2256403
theorem B2172953 : Blo 1336987 2172953 := bstep (se 2 (by rfl) ⟨814857, by rfl⟩ : syracuseStep 2172953 = 1629715) B1629715
theorem B1337387 : Blo 1336987 1337387 := bstep (se 1 (by rfl) ⟨1003040, by rfl⟩ : syracuseStep 1337387 = 2006081) B2006081
theorem B1337399 : Blo 1336987 1337399 := bstep (se 1 (by rfl) ⟨1003049, by rfl⟩ : syracuseStep 1337399 = 2006099) B2006099
theorem B1337419 : Blo 1336987 1337419 := bstep (se 1 (by rfl) ⟨1003064, by rfl⟩ : syracuseStep 1337419 = 2006129) B2006129
theorem B1337431 : Blo 1336987 1337431 := bstep (se 1 (by rfl) ⟨1003073, by rfl⟩ : syracuseStep 1337431 = 2006147) B2006147
theorem B1337451 : Blo 1336987 1337451 := bstep (se 1 (by rfl) ⟨1003088, by rfl⟩ : syracuseStep 1337451 = 2006177) B2006177
theorem B3008627 : Blo 1336987 3008627 := bstep (se 1 (by rfl) ⟨2256470, by rfl⟩ : syracuseStep 3008627 = 4512941) B4512941
theorem B1337463 : Blo 1336987 1337463 := bstep (se 1 (by rfl) ⟨1003097, by rfl⟩ : syracuseStep 1337463 = 2006195) B2006195
theorem B1337483 : Blo 1336987 1337483 := bstep (se 1 (by rfl) ⟨1003112, by rfl⟩ : syracuseStep 1337483 = 2006225) B2006225
theorem B3008663 : Blo 1336987 3008663 := bstep (se 1 (by rfl) ⟨2256497, by rfl⟩ : syracuseStep 3008663 = 4512995) B4512995
theorem B1337495 : Blo 1336987 1337495 := bstep (se 1 (by rfl) ⟨1003121, by rfl⟩ : syracuseStep 1337495 = 2006243) B2006243
theorem B2541719 : Blo 1336987 2541719 := bstep (se 1 (by rfl) ⟨1906289, by rfl⟩ : syracuseStep 2541719 = 3812579) B3812579
theorem B1337515 : Blo 1336987 1337515 := bstep (se 1 (by rfl) ⟨1003136, by rfl⟩ : syracuseStep 1337515 = 2006273) B2006273
theorem B4516019 : Blo 1336987 4516019 := bstep (se 1 (by rfl) ⟨3387014, by rfl⟩ : syracuseStep 4516019 = 6774029) B6774029
theorem B1337527 : Blo 1336987 1337527 := bstep (se 1 (by rfl) ⟨1003145, by rfl⟩ : syracuseStep 1337527 = 2006291) B2006291
theorem B3385547 : Blo 1336987 3385547 := bstep (se 1 (by rfl) ⟨2539160, by rfl⟩ : syracuseStep 3385547 = 5078321) B5078321
theorem B1337547 : Blo 1336987 1337547 := bstep (se 1 (by rfl) ⟨1003160, by rfl⟩ : syracuseStep 1337547 = 2006321) B2006321
theorem B3811531 : Blo 1336987 3811531 := bstep (se 1 (by rfl) ⟨2858648, by rfl⟩ : syracuseStep 3811531 = 5717297) B5717297
theorem B1337559 : Blo 1336987 1337559 := bstep (se 1 (by rfl) ⟨1003169, by rfl⟩ : syracuseStep 1337559 = 2006339) B2006339
theorem B1337579 : Blo 1336987 1337579 := bstep (se 1 (by rfl) ⟨1003184, by rfl⟩ : syracuseStep 1337579 = 2006369) B2006369
theorem B1337591 : Blo 1336987 1337591 := bstep (se 1 (by rfl) ⟨1003193, by rfl⟩ : syracuseStep 1337591 = 2006387) B2006387
theorem B1337611 : Blo 1336987 1337611 := bstep (se 1 (by rfl) ⟨1003208, by rfl⟩ : syracuseStep 1337611 = 2006417) B2006417
theorem B3049751 : Blo 1336987 3049751 := bstep (se 1 (by rfl) ⟨2287313, by rfl⟩ : syracuseStep 3049751 = 4574627) B4574627
theorem B1337623 : Blo 1336987 1337623 := bstep (se 1 (by rfl) ⟨1003217, by rfl⟩ : syracuseStep 1337623 = 2006435) B2006435
theorem B1337643 : Blo 1336987 1337643 := bstep (se 1 (by rfl) ⟨1003232, by rfl⟩ : syracuseStep 1337643 = 2006465) B2006465
theorem B1337655 : Blo 1336987 1337655 := bstep (se 1 (by rfl) ⟨1003241, by rfl⟩ : syracuseStep 1337655 = 2006483) B2006483
theorem B3008843 : Blo 1336987 3008843 := bstep (se 1 (by rfl) ⟨2256632, by rfl⟩ : syracuseStep 3008843 = 4513265) B4513265
theorem B1337675 : Blo 1336987 1337675 := bstep (se 1 (by rfl) ⟨1003256, by rfl⟩ : syracuseStep 1337675 = 2006513) B2006513
theorem B9644363 : Blo 1336987 9644363 := bstep (se 1 (by rfl) ⟨7233272, by rfl⟩ : syracuseStep 9644363 = 14466545) B14466545
theorem B1337687 : Blo 1336987 1337687 := bstep (se 1 (by rfl) ⟨1003265, by rfl⟩ : syracuseStep 1337687 = 2006531) B2006531
theorem B1337707 : Blo 1336987 1337707 := bstep (se 1 (by rfl) ⟨1003280, by rfl⟩ : syracuseStep 1337707 = 2006561) B2006561
theorem B1337719 : Blo 1336987 1337719 := bstep (se 1 (by rfl) ⟨1003289, by rfl⟩ : syracuseStep 1337719 = 2006579) B2006579
theorem B3008897 : Blo 1336987 3008897 := bstep (se 2 (by rfl) ⟨1128336, by rfl⟩ : syracuseStep 3008897 = 2256673) B2256673
theorem B1337739 : Blo 1336987 1337739 := bstep (se 1 (by rfl) ⟨1003304, by rfl⟩ : syracuseStep 1337739 = 2006609) B2006609
theorem B1337751 : Blo 1336987 1337751 := bstep (se 1 (by rfl) ⟨1003313, by rfl⟩ : syracuseStep 1337751 = 2006627) B2006627
theorem B1337771 : Blo 1336987 1337771 := bstep (se 1 (by rfl) ⟨1003328, by rfl⟩ : syracuseStep 1337771 = 2006657) B2006657
theorem B1337783 : Blo 1336987 1337783 := bstep (se 1 (by rfl) ⟨1003337, by rfl⟩ : syracuseStep 1337783 = 2006675) B2006675
theorem B4516289 : Blo 1336987 4516289 := bstep (se 2 (by rfl) ⟨1693608, by rfl⟩ : syracuseStep 4516289 = 3387217) B3387217
theorem B1427915 : Blo 1336987 1427915 := bstep (se 1 (by rfl) ⟨1070936, by rfl⟩ : syracuseStep 1427915 = 2141873) B2141873
theorem B1337803 : Blo 1336987 1337803 := bstep (se 1 (by rfl) ⟨1003352, by rfl⟩ : syracuseStep 1337803 = 2006705) B2006705
theorem B1337815 : Blo 1336987 1337815 := bstep (se 1 (by rfl) ⟨1003361, by rfl⟩ : syracuseStep 1337815 = 2006723) B2006723
theorem B3811805 : Blo 1336987 3811805 := bstep (se 3 (by rfl) ⟨714713, by rfl⟩ : syracuseStep 3811805 = 1429427) B1429427
theorem B1337835 : Blo 1336987 1337835 := bstep (se 1 (by rfl) ⟨1003376, by rfl⟩ : syracuseStep 1337835 = 2006753) B2006753
theorem B1337847 : Blo 1336987 1337847 := bstep (se 1 (by rfl) ⟨1003385, by rfl⟩ : syracuseStep 1337847 = 2006771) B2006771
theorem B1337867 : Blo 1336987 1337867 := bstep (se 1 (by rfl) ⟨1003400, by rfl⟩ : syracuseStep 1337867 = 2006801) B2006801
theorem B6769169 : Blo 1336987 6769169 := bstep (se 2 (by rfl) ⟨2538438, by rfl⟩ : syracuseStep 6769169 = 5076877) B5076877
theorem B1337879 : Blo 1336987 1337879 := bstep (se 1 (by rfl) ⟨1003409, by rfl⟩ : syracuseStep 1337879 = 2006819) B2006819
theorem B4286999 : Blo 1336987 4286999 := bstep (se 1 (by rfl) ⟨3215249, by rfl⟩ : syracuseStep 4286999 = 6430499) B6430499
theorem B1337899 : Blo 1336987 1337899 := bstep (se 1 (by rfl) ⟨1003424, by rfl⟩ : syracuseStep 1337899 = 2006849) B2006849
theorem B1337911 : Blo 1336987 1337911 := bstep (se 1 (by rfl) ⟨1003433, by rfl⟩ : syracuseStep 1337911 = 2006867) B2006867
theorem B3385921 : Blo 1336987 3385921 := bstep (se 2 (by rfl) ⟨1269720, by rfl⟩ : syracuseStep 3385921 = 2539441) B2539441
theorem B1337931 : Blo 1336987 1337931 := bstep (se 1 (by rfl) ⟨1003448, by rfl⟩ : syracuseStep 1337931 = 2006897) B2006897
theorem B1337943 : Blo 1336987 1337943 := bstep (se 1 (by rfl) ⟨1003457, by rfl⟩ : syracuseStep 1337943 = 2006915) B2006915
theorem B3009113 : Blo 1336987 3009113 := bstep (se 2 (by rfl) ⟨1128417, by rfl⟩ : syracuseStep 3009113 = 2256835) B2256835
theorem B17148509 : Blo 1336987 17148509 := bstep (se 3 (by rfl) ⟨3215345, by rfl⟩ : syracuseStep 17148509 = 6430691) B6430691
theorem B1337963 : Blo 1336987 1337963 := bstep (se 1 (by rfl) ⟨1003472, by rfl⟩ : syracuseStep 1337963 = 2006945) B2006945
theorem B1337975 : Blo 1336987 1337975 := bstep (se 1 (by rfl) ⟨1003481, by rfl⟩ : syracuseStep 1337975 = 2006963) B2006963
theorem B11586179 : Blo 1336987 11586179 := bstep (se 1 (by rfl) ⟨8689634, by rfl⟩ : syracuseStep 11586179 = 17379269) B17379269
theorem B1337995 : Blo 1336987 1337995 := bstep (se 1 (by rfl) ⟨1003496, by rfl⟩ : syracuseStep 1337995 = 2006993) B2006993
theorem B1338007 : Blo 1336987 1338007 := bstep (se 1 (by rfl) ⟨1003505, by rfl⟩ : syracuseStep 1338007 = 2007011) B2007011
theorem B1338027 : Blo 1336987 1338027 := bstep (se 1 (by rfl) ⟨1003520, by rfl⟩ : syracuseStep 1338027 = 2007041) B2007041
theorem B6769331 : Blo 1336987 6769331 := bstep (se 1 (by rfl) ⟨5076998, by rfl⟩ : syracuseStep 6769331 = 10153997) B10153997
theorem B3009203 : Blo 1336987 3009203 := bstep (se 1 (by rfl) ⟨2256902, by rfl⟩ : syracuseStep 3009203 = 4513805) B4513805
theorem B1338039 : Blo 1336987 1338039 := bstep (se 1 (by rfl) ⟨1003529, by rfl⟩ : syracuseStep 1338039 = 2007059) B2007059
theorem B1338059 : Blo 1336987 1338059 := bstep (se 1 (by rfl) ⟨1003544, by rfl⟩ : syracuseStep 1338059 = 2007089) B2007089
theorem B3009239 : Blo 1336987 3009239 := bstep (se 1 (by rfl) ⟨2256929, by rfl⟩ : syracuseStep 3009239 = 4513859) B4513859
theorem B1338071 : Blo 1336987 1338071 := bstep (se 1 (by rfl) ⟨1003553, by rfl⟩ : syracuseStep 1338071 = 2007107) B2007107
theorem B1338091 : Blo 1336987 1338091 := bstep (se 1 (by rfl) ⟨1003568, by rfl⟩ : syracuseStep 1338091 = 2007137) B2007137
theorem B1338103 : Blo 1336987 1338103 := bstep (se 1 (by rfl) ⟨1003577, by rfl⟩ : syracuseStep 1338103 = 2007155) B2007155
theorem B1338123 : Blo 1336987 1338123 := bstep (se 1 (by rfl) ⟨1003592, by rfl⟩ : syracuseStep 1338123 = 2007185) B2007185
theorem B1338135 : Blo 1336987 1338135 := bstep (se 1 (by rfl) ⟨1003601, by rfl⟩ : syracuseStep 1338135 = 2007203) B2007203
theorem B1338155 : Blo 1336987 1338155 := bstep (se 1 (by rfl) ⟨1003616, by rfl⟩ : syracuseStep 1338155 = 2007233) B2007233
theorem B3812147 : Blo 1336987 3812147 := bstep (se 1 (by rfl) ⟨2859110, by rfl⟩ : syracuseStep 3812147 = 5718221) B5718221
theorem B1338167 : Blo 1336987 1338167 := bstep (se 1 (by rfl) ⟨1003625, by rfl⟩ : syracuseStep 1338167 = 2007251) B2007251
theorem B1338187 : Blo 1336987 1338187 := bstep (se 1 (by rfl) ⟨1003640, by rfl⟩ : syracuseStep 1338187 = 2007281) B2007281
theorem B1338199 : Blo 1336987 1338199 := bstep (se 1 (by rfl) ⟨1003649, by rfl⟩ : syracuseStep 1338199 = 2007299) B2007299
theorem B11422565 : Blo 1336987 11422565 := bstep (se 4 (by rfl) ⟨1070865, by rfl⟩ : syracuseStep 11422565 = 2141731) B2141731
theorem B1338219 : Blo 1336987 1338219 := bstep (se 1 (by rfl) ⟨1003664, by rfl⟩ : syracuseStep 1338219 = 2007329) B2007329
theorem B1338231 : Blo 1336987 1338231 := bstep (se 1 (by rfl) ⟨1003673, by rfl⟩ : syracuseStep 1338231 = 2007347) B2007347
theorem B3009419 : Blo 1336987 3009419 := bstep (se 1 (by rfl) ⟨2257064, by rfl⟩ : syracuseStep 3009419 = 4514129) B4514129
theorem B1338251 : Blo 1336987 1338251 := bstep (se 1 (by rfl) ⟨1003688, by rfl⟩ : syracuseStep 1338251 = 2007377) B2007377
theorem B1338263 : Blo 1336987 1338263 := bstep (se 1 (by rfl) ⟨1003697, by rfl⟩ : syracuseStep 1338263 = 2007395) B2007395
theorem B1338283 : Blo 1336987 1338283 := bstep (se 1 (by rfl) ⟨1003712, by rfl⟩ : syracuseStep 1338283 = 2007425) B2007425
theorem B1338295 : Blo 1336987 1338295 := bstep (se 1 (by rfl) ⟨1003721, by rfl⟩ : syracuseStep 1338295 = 2007443) B2007443
theorem B3009473 : Blo 1336987 3009473 := bstep (se 2 (by rfl) ⟨1128552, by rfl⟩ : syracuseStep 3009473 = 2257105) B2257105
theorem B1338315 : Blo 1336987 1338315 := bstep (se 1 (by rfl) ⟨1003736, by rfl⟩ : syracuseStep 1338315 = 2007473) B2007473
theorem B1338327 : Blo 1336987 1338327 := bstep (se 1 (by rfl) ⟨1003745, by rfl⟩ : syracuseStep 1338327 = 2007491) B2007491
theorem B4516829 : Blo 1336987 4516829 := bstep (se 3 (by rfl) ⟨846905, by rfl⟩ : syracuseStep 4516829 = 1693811) B1693811
theorem B1338347 : Blo 1336987 1338347 := bstep (se 1 (by rfl) ⟨1003760, by rfl⟩ : syracuseStep 1338347 = 2007521) B2007521
theorem B1338359 : Blo 1336987 1338359 := bstep (se 1 (by rfl) ⟨1003769, by rfl⟩ : syracuseStep 1338359 = 2007539) B2007539
theorem B1338379 : Blo 1336987 1338379 := bstep (se 1 (by rfl) ⟨1003784, by rfl⟩ : syracuseStep 1338379 = 2007569) B2007569
theorem B14855185 : Blo 1336987 14855185 := bstep (se 2 (by rfl) ⟨5570694, by rfl⟩ : syracuseStep 14855185 = 11141389) B11141389
theorem B1338391 : Blo 1336987 1338391 := bstep (se 1 (by rfl) ⟨1003793, by rfl⟩ : syracuseStep 1338391 = 2007587) B2007587
theorem B1338411 : Blo 1336987 1338411 := bstep (se 1 (by rfl) ⟨1003808, by rfl⟩ : syracuseStep 1338411 = 2007617) B2007617
theorem B1338423 : Blo 1336987 1338423 := bstep (se 1 (by rfl) ⟨1003817, by rfl⟩ : syracuseStep 1338423 = 2007635) B2007635
theorem B10153025 : Blo 1336987 10153025 := bstep (se 2 (by rfl) ⟨3807384, by rfl⟩ : syracuseStep 10153025 = 7614769) B7614769
theorem B4287563 : Blo 1336987 4287563 := bstep (se 1 (by rfl) ⟨3215672, by rfl⟩ : syracuseStep 4287563 = 6431345) B6431345
theorem B1338443 : Blo 1336987 1338443 := bstep (se 1 (by rfl) ⟨1003832, by rfl⟩ : syracuseStep 1338443 = 2007665) B2007665
theorem B1338455 : Blo 1336987 1338455 := bstep (se 1 (by rfl) ⟨1003841, by rfl⟩ : syracuseStep 1338455 = 2007683) B2007683
theorem B1338475 : Blo 1336987 1338475 := bstep (se 1 (by rfl) ⟨1003856, by rfl⟩ : syracuseStep 1338475 = 2007713) B2007713
theorem B1338487 : Blo 1336987 1338487 := bstep (se 1 (by rfl) ⟨1003865, by rfl⟩ : syracuseStep 1338487 = 2007731) B2007731
theorem B1338507 : Blo 1336987 1338507 := bstep (se 1 (by rfl) ⟨1003880, by rfl⟩ : syracuseStep 1338507 = 2007761) B2007761
theorem B3386519 : Blo 1336987 3386519 := bstep (se 1 (by rfl) ⟨2539889, by rfl⟩ : syracuseStep 3386519 = 5079779) B5079779
theorem B1338519 : Blo 1336987 1338519 := bstep (se 1 (by rfl) ⟨1003889, by rfl⟩ : syracuseStep 1338519 = 2007779) B2007779
theorem B3009689 : Blo 1336987 3009689 := bstep (se 2 (by rfl) ⟨1128633, by rfl⟩ : syracuseStep 3009689 = 2257267) B2257267
theorem B1338539 : Blo 1336987 1338539 := bstep (se 1 (by rfl) ⟨1003904, by rfl⟩ : syracuseStep 1338539 = 2007809) B2007809
theorem B1338551 : Blo 1336987 1338551 := bstep (se 1 (by rfl) ⟨1003913, by rfl⟩ : syracuseStep 1338551 = 2007827) B2007827
theorem B1338571 : Blo 1336987 1338571 := bstep (se 1 (by rfl) ⟨1003928, by rfl⟩ : syracuseStep 1338571 = 2007857) B2007857
theorem B1338583 : Blo 1336987 1338583 := bstep (se 1 (by rfl) ⟨1003937, by rfl⟩ : syracuseStep 1338583 = 2007875) B2007875
theorem B1338603 : Blo 1336987 1338603 := bstep (se 1 (by rfl) ⟨1003952, by rfl⟩ : syracuseStep 1338603 = 2007905) B2007905
theorem B3009779 : Blo 1336987 3009779 := bstep (se 1 (by rfl) ⟨2257334, by rfl⟩ : syracuseStep 3009779 = 4514669) B4514669
theorem B1338615 : Blo 1336987 1338615 := bstep (se 1 (by rfl) ⟨1003961, by rfl⟩ : syracuseStep 1338615 = 2007923) B2007923
theorem B1338635 : Blo 1336987 1338635 := bstep (se 1 (by rfl) ⟨1003976, by rfl⟩ : syracuseStep 1338635 = 2007953) B2007953
theorem B3009815 : Blo 1336987 3009815 := bstep (se 1 (by rfl) ⟨2257361, by rfl⟩ : syracuseStep 3009815 = 4514723) B4514723
theorem B1338647 : Blo 1336987 1338647 := bstep (se 1 (by rfl) ⟨1003985, by rfl⟩ : syracuseStep 1338647 = 2007971) B2007971
theorem B1338667 : Blo 1336987 1338667 := bstep (se 1 (by rfl) ⟨1004000, by rfl⟩ : syracuseStep 1338667 = 2008001) B2008001
theorem B1338679 : Blo 1336987 1338679 := bstep (se 1 (by rfl) ⟨1004009, by rfl⟩ : syracuseStep 1338679 = 2008019) B2008019
theorem B6434113 : Blo 1336987 6434113 := bstep (se 2 (by rfl) ⟨2412792, by rfl⟩ : syracuseStep 6434113 = 4825585) B4825585
theorem B1338699 : Blo 1336987 1338699 := bstep (se 1 (by rfl) ⟨1004024, by rfl⟩ : syracuseStep 1338699 = 2008049) B2008049
theorem B5147993 : Blo 1336987 5147993 := bstep (se 2 (by rfl) ⟨1930497, by rfl⟩ : syracuseStep 5147993 = 3860995) B3860995
theorem B1338711 : Blo 1336987 1338711 := bstep (se 1 (by rfl) ⟨1004033, by rfl⟩ : syracuseStep 1338711 = 2008067) B2008067
theorem B9637213 : Blo 1336987 9637213 := bstep (se 3 (by rfl) ⟨1806977, by rfl⟩ : syracuseStep 9637213 = 3613955) B3613955
theorem B1338731 : Blo 1336987 1338731 := bstep (se 1 (by rfl) ⟨1004048, by rfl⟩ : syracuseStep 1338731 = 2008097) B2008097
theorem B1338743 : Blo 1336987 1338743 := bstep (se 1 (by rfl) ⟨1004057, by rfl⟩ : syracuseStep 1338743 = 2008115) B2008115
theorem B1338763 : Blo 1336987 1338763 := bstep (se 1 (by rfl) ⟨1004072, by rfl⟩ : syracuseStep 1338763 = 2008145) B2008145
theorem B1904023 : Blo 1336987 1904023 := bstep (se 1 (by rfl) ⟨1428017, by rfl⟩ : syracuseStep 1904023 = 2856035) B2856035
theorem B1338775 : Blo 1336987 1338775 := bstep (se 1 (by rfl) ⟨1004081, by rfl⟩ : syracuseStep 1338775 = 2008163) B2008163
theorem B1338795 : Blo 1336987 1338795 := bstep (se 1 (by rfl) ⟨1004096, by rfl⟩ : syracuseStep 1338795 = 2008193) B2008193
theorem B1338807 : Blo 1336987 1338807 := bstep (se 1 (by rfl) ⟨1004105, by rfl⟩ : syracuseStep 1338807 = 2008211) B2008211
theorem B3009995 : Blo 1336987 3009995 := bstep (se 1 (by rfl) ⟨2257496, by rfl⟩ : syracuseStep 3009995 = 4514993) B4514993
theorem B1338827 : Blo 1336987 1338827 := bstep (se 1 (by rfl) ⟨1004120, by rfl⟩ : syracuseStep 1338827 = 2008241) B2008241
theorem B1338839 : Blo 1336987 1338839 := bstep (se 1 (by rfl) ⟨1004129, by rfl⟩ : syracuseStep 1338839 = 2008259) B2008259
theorem B4574681 : Blo 1336987 4574681 := bstep (se 2 (by rfl) ⟨1715505, by rfl⟩ : syracuseStep 4574681 = 3431011) B3431011
theorem B1338859 : Blo 1336987 1338859 := bstep (se 1 (by rfl) ⟨1004144, by rfl⟩ : syracuseStep 1338859 = 2008289) B2008289
theorem B1338871 : Blo 1336987 1338871 := bstep (se 1 (by rfl) ⟨1004153, by rfl⟩ : syracuseStep 1338871 = 2008307) B2008307
theorem B3010049 : Blo 1336987 3010049 := bstep (se 2 (by rfl) ⟨1128768, by rfl⟩ : syracuseStep 3010049 = 2257537) B2257537
theorem B1338891 : Blo 1336987 1338891 := bstep (se 1 (by rfl) ⟨1004168, by rfl⟩ : syracuseStep 1338891 = 2008337) B2008337
theorem B1338903 : Blo 1336987 1338903 := bstep (se 1 (by rfl) ⟨1004177, by rfl⟩ : syracuseStep 1338903 = 2008355) B2008355
theorem B1338923 : Blo 1336987 1338923 := bstep (se 1 (by rfl) ⟨1004192, by rfl⟩ : syracuseStep 1338923 = 2008385) B2008385
theorem B1338935 : Blo 1336987 1338935 := bstep (se 1 (by rfl) ⟨1004201, by rfl⟩ : syracuseStep 1338935 = 2008403) B2008403
theorem B1338955 : Blo 1336987 1338955 := bstep (se 1 (by rfl) ⟨1004216, by rfl⟩ : syracuseStep 1338955 = 2008433) B2008433
theorem B1338967 : Blo 1336987 1338967 := bstep (se 1 (by rfl) ⟨1004225, by rfl⟩ : syracuseStep 1338967 = 2008451) B2008451
theorem B1338987 : Blo 1336987 1338987 := bstep (se 1 (by rfl) ⟨1004240, by rfl⟩ : syracuseStep 1338987 = 2008481) B2008481
theorem B1429111 : Blo 1336987 1429111 := bstep (se 1 (by rfl) ⟨1071833, by rfl⟩ : syracuseStep 1429111 = 2143667) B2143667
theorem B2256599 : Blo 1336987 2256599 := bstep (se 1 (by rfl) ⟨1692449, by rfl⟩ : syracuseStep 2256599 = 3384899) B3384899
theorem B3010265 : Blo 1336987 3010265 := bstep (se 2 (by rfl) ⟨1128849, by rfl⟩ : syracuseStep 3010265 = 2257699) B2257699
theorem B3010355 : Blo 1336987 3010355 := bstep (se 1 (by rfl) ⟨2257766, by rfl⟩ : syracuseStep 3010355 = 4515533) B4515533
theorem B2256727 : Blo 1336987 2256727 := bstep (se 1 (by rfl) ⟨1692545, by rfl⟩ : syracuseStep 2256727 = 3385091) B3385091
theorem B3010391 : Blo 1336987 3010391 := bstep (se 1 (by rfl) ⟨2257793, by rfl⟩ : syracuseStep 3010391 = 4515587) B4515587
theorem B3387329 : Blo 1336987 3387329 := bstep (se 2 (by rfl) ⟨1270248, by rfl⟩ : syracuseStep 3387329 = 2540497) B2540497
theorem B3862475 : Blo 1336987 3862475 := bstep (se 1 (by rfl) ⟨2896856, by rfl⟩ : syracuseStep 3862475 = 5793713) B5793713
theorem B12857305 : Blo 1336987 12857305 := bstep (se 2 (by rfl) ⟨4821489, by rfl⟩ : syracuseStep 12857305 = 9642979) B9642979
theorem B3010571 : Blo 1336987 3010571 := bstep (se 1 (by rfl) ⟨2257928, by rfl⟩ : syracuseStep 3010571 = 4515857) B4515857
theorem B5083181 : Blo 1336987 5083181 := bstep (se 3 (by rfl) ⟨953096, by rfl⟩ : syracuseStep 5083181 = 1906193) B1906193
theorem B3010625 : Blo 1336987 3010625 := bstep (se 2 (by rfl) ⟨1128984, by rfl⟩ : syracuseStep 3010625 = 2257969) B2257969
theorem B2142283 : Blo 1336987 2142283 := bstep (se 1 (by rfl) ⟨1606712, by rfl⟩ : syracuseStep 2142283 = 3213425) B3213425
theorem B4517963 : Blo 1336987 4517963 := bstep (se 1 (by rfl) ⟨3388472, by rfl⟩ : syracuseStep 4517963 = 6776945) B6776945
theorem B7336037 : Blo 1336987 7336037 := bstep (se 4 (by rfl) ⟨687753, by rfl⟩ : syracuseStep 7336037 = 1375507) B1375507
theorem B1904843 : Blo 1336987 1904843 := bstep (se 1 (by rfl) ⟨1428632, by rfl⟩ : syracuseStep 1904843 = 2857265) B2857265
theorem B3010841 : Blo 1336987 3010841 := bstep (se 2 (by rfl) ⟨1129065, by rfl⟩ : syracuseStep 3010841 = 2258131) B2258131
theorem B5714221 : Blo 1336987 5714221 := bstep (se 3 (by rfl) ⟨1071416, by rfl⟩ : syracuseStep 5714221 = 2142833) B2142833
theorem B2142539 : Blo 1336987 2142539 := bstep (se 1 (by rfl) ⟨1606904, by rfl⟩ : syracuseStep 2142539 = 3213809) B3213809
theorem B4518233 : Blo 1336987 4518233 := bstep (se 2 (by rfl) ⟨1694337, by rfl⟩ : syracuseStep 4518233 = 3388675) B3388675
theorem B3010931 : Blo 1336987 3010931 := bstep (se 1 (by rfl) ⟨2258198, by rfl⟩ : syracuseStep 3010931 = 4516397) B4516397
theorem B15446389 : Blo 1336987 15446389 := bstep (se 5 (by rfl) ⟨724049, by rfl⟩ : syracuseStep 15446389 = 1448099) B1448099
theorem B3010967 : Blo 1336987 3010967 := bstep (se 1 (by rfl) ⟨2258225, by rfl⟩ : syracuseStep 3010967 = 4516451) B4516451
theorem B2478487 : Blo 1336987 2478487 := bstep (se 1 (by rfl) ⟨1858865, by rfl⟩ : syracuseStep 2478487 = 3717731) B3717731
theorem B2257355 : Blo 1336987 2257355 := bstep (se 1 (by rfl) ⟨1693016, by rfl⟩ : syracuseStep 2257355 = 3386033) B3386033
theorem B3387865 : Blo 1336987 3387865 := bstep (se 2 (by rfl) ⟨1270449, by rfl⟩ : syracuseStep 3387865 = 2540899) B2540899
theorem B2290187 : Blo 1336987 2290187 := bstep (se 1 (by rfl) ⟨1717640, by rfl⟩ : syracuseStep 2290187 = 3435281) B3435281
theorem B8573485 : Blo 1336987 8573485 := bstep (se 3 (by rfl) ⟨1607528, by rfl⟩ : syracuseStep 8573485 = 3215057) B3215057
theorem B6771275 : Blo 1336987 6771275 := bstep (se 1 (by rfl) ⟨5078456, by rfl⟩ : syracuseStep 6771275 = 10156913) B10156913
theorem B2257483 : Blo 1336987 2257483 := bstep (se 1 (by rfl) ⟨1693112, by rfl⟩ : syracuseStep 2257483 = 3386225) B3386225
theorem B3011147 : Blo 1336987 3011147 := bstep (se 1 (by rfl) ⟨2258360, by rfl⟩ : syracuseStep 3011147 = 4516721) B4516721
theorem B1692247 : Blo 1336987 1692247 := bstep (se 1 (by rfl) ⟨1269185, by rfl⟩ : syracuseStep 1692247 = 2538371) B2538371
theorem B3052121 : Blo 1336987 3052121 := bstep (se 2 (by rfl) ⟨1144545, by rfl⟩ : syracuseStep 3052121 = 2289091) B2289091
theorem B3011201 : Blo 1336987 3011201 := bstep (se 2 (by rfl) ⟨1129200, by rfl⟩ : syracuseStep 3011201 = 2258401) B2258401
theorem B5714563 : Blo 1336987 5714563 := bstep (se 1 (by rfl) ⟨4285922, by rfl⟩ : syracuseStep 5714563 = 8571845) B8571845
theorem B4289203 : Blo 1336987 4289203 := bstep (se 1 (by rfl) ⟨3216902, by rfl⟩ : syracuseStep 4289203 = 6433805) B6433805
theorem B2257625 : Blo 1336987 2257625 := bstep (se 2 (by rfl) ⟨846609, by rfl⟩ : syracuseStep 2257625 = 1693219) B1693219
theorem B5083955 : Blo 1336987 5083955 := bstep (se 1 (by rfl) ⟨3812966, by rfl⟩ : syracuseStep 5083955 = 7625933) B7625933
theorem B4289345 : Blo 1336987 4289345 := bstep (se 2 (by rfl) ⟨1608504, by rfl⟩ : syracuseStep 4289345 = 3217009) B3217009
theorem B2257753 : Blo 1336987 2257753 := bstep (se 2 (by rfl) ⟨846657, by rfl⟩ : syracuseStep 2257753 = 1693315) B1693315
theorem B3011417 : Blo 1336987 3011417 := bstep (se 2 (by rfl) ⟨1129281, by rfl⟩ : syracuseStep 3011417 = 2258563) B2258563
theorem B7623517 : Blo 1336987 7623517 := bstep (se 3 (by rfl) ⟨1429409, by rfl⟩ : syracuseStep 7623517 = 2858819) B2858819
theorem B3011507 : Blo 1336987 3011507 := bstep (se 1 (by rfl) ⟨2258630, by rfl⟩ : syracuseStep 3011507 = 4517261) B4517261
theorem B1504183 : Blo 1336987 1504183 := bstep (se 1 (by rfl) ⟨1128137, by rfl⟩ : syracuseStep 1504183 = 2256275) B2256275
theorem B2855873 : Blo 1336987 2855873 := bstep (se 2 (by rfl) ⟨1070952, by rfl⟩ : syracuseStep 2855873 = 2141905) B2141905
theorem B3011543 : Blo 1336987 3011543 := bstep (se 1 (by rfl) ⟨2258657, by rfl⟩ : syracuseStep 3011543 = 4517315) B4517315
theorem B10154969 : Blo 1336987 10154969 := bstep (se 2 (by rfl) ⟨3808113, by rfl⟩ : syracuseStep 10154969 = 7616227) B7616227
theorem B2143243 : Blo 1336987 2143243 := bstep (se 1 (by rfl) ⟨1607432, by rfl⟩ : syracuseStep 2143243 = 3214865) B3214865
theorem B4518935 : Blo 1336987 4518935 := bstep (se 1 (by rfl) ⟨3389201, by rfl⟩ : syracuseStep 4518935 = 6778403) B6778403
theorem B41759813 : Blo 1336987 41759813 := bstep (se 4 (by rfl) ⟨3914982, by rfl⟩ : syracuseStep 41759813 = 7829965) B7829965
theorem B4576349 : Blo 1336987 4576349 := bstep (se 3 (by rfl) ⟨858065, by rfl⟩ : syracuseStep 4576349 = 1716131) B1716131
theorem B1504363 : Blo 1336987 1504363 := bstep (se 1 (by rfl) ⟨1128272, by rfl⟩ : syracuseStep 1504363 = 2256545) B2256545
theorem B3011723 : Blo 1336987 3011723 := bstep (se 1 (by rfl) ⟨2258792, by rfl⟩ : syracuseStep 3011723 = 4517585) B4517585
theorem B5428397 : Blo 1336987 5428397 := bstep (se 3 (by rfl) ⟨1017824, by rfl⟩ : syracuseStep 5428397 = 2035649) B2035649
theorem B3667123 : Blo 1336987 3667123 := bstep (se 1 (by rfl) ⟨2750342, by rfl⟩ : syracuseStep 3667123 = 5500685) B5500685
theorem B3011777 : Blo 1336987 3011777 := bstep (se 2 (by rfl) ⟨1129416, by rfl⟩ : syracuseStep 3011777 = 2258833) B2258833
theorem B1504471 : Blo 1336987 1504471 := bstep (se 1 (by rfl) ⟨1128353, by rfl⟩ : syracuseStep 1504471 = 2256707) B2256707
theorem B2856215 : Blo 1336987 2856215 := bstep (se 1 (by rfl) ⟨2142161, by rfl⟩ : syracuseStep 2856215 = 4284323) B4284323
theorem B2143513 : Blo 1336987 2143513 := bstep (se 2 (by rfl) ⟨803817, by rfl⟩ : syracuseStep 2143513 = 1607635) B1607635
theorem B2143577 : Blo 1336987 2143577 := bstep (se 2 (by rfl) ⟨803841, by rfl⟩ : syracuseStep 2143577 = 1607683) B1607683
theorem B1504651 : Blo 1336987 1504651 := bstep (se 1 (by rfl) ⟨1128488, by rfl⟩ : syracuseStep 1504651 = 2256977) B2256977
theorem B31315349 : Blo 1336987 31315349 := bstep (se 6 (by rfl) ⟨733953, by rfl⟩ : syracuseStep 31315349 = 1467907) B1467907
theorem B2258327 : Blo 1336987 2258327 := bstep (se 1 (by rfl) ⟨1693745, by rfl⟩ : syracuseStep 2258327 = 3387491) B3387491
theorem B3011993 : Blo 1336987 3011993 := bstep (se 2 (by rfl) ⟨1129497, by rfl⟩ : syracuseStep 3011993 = 2258995) B2258995
theorem B3012083 : Blo 1336987 3012083 := bstep (se 1 (by rfl) ⟨2259062, by rfl⟩ : syracuseStep 3012083 = 4518125) B4518125
theorem B1504759 : Blo 1336987 1504759 := bstep (se 1 (by rfl) ⟨1128569, by rfl⟩ : syracuseStep 1504759 = 2257139) B2257139
theorem B10163717 : Blo 1336987 10163717 := bstep (se 4 (by rfl) ⟨952848, by rfl⟩ : syracuseStep 10163717 = 1905697) B1905697
theorem B2258455 : Blo 1336987 2258455 := bstep (se 1 (by rfl) ⟨1693841, by rfl⟩ : syracuseStep 2258455 = 3387683) B3387683
theorem B3012119 : Blo 1336987 3012119 := bstep (se 1 (by rfl) ⟨2259089, by rfl⟩ : syracuseStep 3012119 = 4518179) B4518179
theorem B7616045 : Blo 1336987 7616045 := bstep (se 3 (by rfl) ⟨1428008, by rfl⟩ : syracuseStep 7616045 = 2856017) B2856017
theorem B3388979 : Blo 1336987 3388979 := bstep (se 1 (by rfl) ⟨2541734, by rfl⟩ : syracuseStep 3388979 = 5083469) B5083469
theorem B5715521 : Blo 1336987 5715521 := bstep (se 2 (by rfl) ⟨2143320, by rfl⟩ : syracuseStep 5715521 = 4286641) B4286641
theorem B1808011 : Blo 1336987 1808011 := bstep (se 1 (by rfl) ⟨1356008, by rfl⟩ : syracuseStep 1808011 = 2712017) B2712017
theorem B1504939 : Blo 1336987 1504939 := bstep (se 1 (by rfl) ⟨1128704, by rfl⟩ : syracuseStep 1504939 = 2257409) B2257409
theorem B3012299 : Blo 1336987 3012299 := bstep (se 1 (by rfl) ⟨2259224, by rfl⟩ : syracuseStep 3012299 = 4518449) B4518449
theorem B4822745 : Blo 1336987 4822745 := bstep (se 2 (by rfl) ⟨1808529, by rfl⟩ : syracuseStep 4822745 = 3617059) B3617059
theorem B3012353 : Blo 1336987 3012353 := bstep (se 2 (by rfl) ⟨1129632, by rfl⟩ : syracuseStep 3012353 = 2259265) B2259265
theorem B1505047 : Blo 1336987 1505047 := bstep (se 1 (by rfl) ⟨1128785, by rfl⟩ : syracuseStep 1505047 = 2257571) B2257571
theorem B3389273 : Blo 1336987 3389273 := bstep (se 2 (by rfl) ⟨1270977, by rfl⟩ : syracuseStep 3389273 = 2541955) B2541955
theorem B3094451 : Blo 1336987 3094451 := bstep (se 1 (by rfl) ⟨2320838, by rfl⟩ : syracuseStep 3094451 = 4641677) B4641677
theorem B1505227 : Blo 1336987 1505227 := bstep (se 1 (by rfl) ⟨1128920, by rfl⟩ : syracuseStep 1505227 = 2257841) B2257841
theorem B5576651 : Blo 1336987 5576651 := bstep (se 1 (by rfl) ⟨4182488, by rfl⟩ : syracuseStep 5576651 = 8364977) B8364977
theorem B22845401 : Blo 1336987 22845401 := bstep (se 2 (by rfl) ⟨8567025, by rfl⟩ : syracuseStep 22845401 = 17134051) B17134051
theorem B3012569 : Blo 1336987 3012569 := bstep (se 2 (by rfl) ⟨1129713, by rfl⟩ : syracuseStep 3012569 = 2259427) B2259427
theorem B3807283 : Blo 1336987 3807283 := bstep (se 1 (by rfl) ⟨2855462, by rfl⟩ : syracuseStep 3807283 = 5710925) B5710925
theorem B3012659 : Blo 1336987 3012659 := bstep (se 1 (by rfl) ⟨2259494, by rfl⟩ : syracuseStep 3012659 = 4518989) B4518989
theorem B1505335 : Blo 1336987 1505335 := bstep (se 1 (by rfl) ⟨1129001, by rfl⟩ : syracuseStep 1505335 = 2258003) B2258003
theorem B3012695 : Blo 1336987 3012695 := bstep (se 1 (by rfl) ⟨2259521, by rfl⟩ : syracuseStep 3012695 = 4519043) B4519043
theorem B7231589 : Blo 1336987 7231589 := bstep (se 4 (by rfl) ⟨677961, by rfl⟩ : syracuseStep 7231589 = 1355923) B1355923
theorem B2750603 : Blo 1336987 2750603 := bstep (se 1 (by rfl) ⟨2062952, by rfl⟩ : syracuseStep 2750603 = 4125905) B4125905
theorem B2259083 : Blo 1336987 2259083 := bstep (se 1 (by rfl) ⟨1694312, by rfl⟩ : syracuseStep 2259083 = 3388625) B3388625
theorem B1505515 : Blo 1336987 1505515 := bstep (se 1 (by rfl) ⟨1129136, by rfl⟩ : syracuseStep 1505515 = 2258273) B2258273
theorem B1693963 : Blo 1336987 1693963 := bstep (se 1 (by rfl) ⟨1270472, by rfl⟩ : syracuseStep 1693963 = 2540945) B2540945
theorem B2259211 : Blo 1336987 2259211 := bstep (se 1 (by rfl) ⟨1694408, by rfl⟩ : syracuseStep 2259211 = 3388817) B3388817
theorem B6773057 : Blo 1336987 6773057 := bstep (se 2 (by rfl) ⟨2539896, by rfl⟩ : syracuseStep 6773057 = 5079793) B5079793
theorem B1505623 : Blo 1336987 1505623 := bstep (se 1 (by rfl) ⟨1129217, by rfl⟩ : syracuseStep 1505623 = 2258435) B2258435
theorem B2259353 : Blo 1336987 2259353 := bstep (se 2 (by rfl) ⟨847257, by rfl⟩ : syracuseStep 2259353 = 1694515) B1694515
theorem B1505803 : Blo 1336987 1505803 := bstep (se 1 (by rfl) ⟨1129352, by rfl⟩ : syracuseStep 1505803 = 2258705) B2258705
theorem B2005529 : Blo 1336987 2005529 := bstep (se 2 (by rfl) ⟨752073, by rfl⟩ : syracuseStep 2005529 = 1504147) B1504147
theorem B2259481 : Blo 1336987 2259481 := bstep (se 2 (by rfl) ⟨847305, by rfl⟩ : syracuseStep 2259481 = 1694611) B1694611
theorem B1505911 : Blo 1336987 1505911 := bstep (se 1 (by rfl) ⟨1129433, by rfl⟩ : syracuseStep 1505911 = 2258867) B2258867
theorem B2005643 : Blo 1336987 2005643 := bstep (se 1 (by rfl) ⟨1504232, by rfl⟩ : syracuseStep 2005643 = 3008465) B3008465
theorem B2005655 : Blo 1336987 2005655 := bstep (se 1 (by rfl) ⟨1504241, by rfl⟩ : syracuseStep 2005655 = 3008483) B3008483
theorem B1374871 : Blo 1336987 1374871 := bstep (se 1 (by rfl) ⟨1031153, by rfl⟩ : syracuseStep 1374871 = 2062307) B2062307
theorem B1809049 : Blo 1336987 1809049 := bstep (se 2 (by rfl) ⟨678393, by rfl⟩ : syracuseStep 1809049 = 1356787) B1356787
theorem B2857675 : Blo 1336987 2857675 := bstep (se 1 (by rfl) ⟨2143256, by rfl⟩ : syracuseStep 2857675 = 4286513) B4286513
theorem B2005721 : Blo 1336987 2005721 := bstep (se 2 (by rfl) ⟨752145, by rfl⟩ : syracuseStep 2005721 = 1504291) B1504291
theorem B1506091 : Blo 1336987 1506091 := bstep (se 1 (by rfl) ⟨1129568, by rfl⟩ : syracuseStep 1506091 = 2259137) B2259137
theorem B4512563 : Blo 1336987 4512563 := bstep (se 1 (by rfl) ⟨3384422, by rfl⟩ : syracuseStep 4512563 = 6768845) B6768845
theorem B2005835 : Blo 1336987 2005835 := bstep (se 1 (by rfl) ⟨1504376, by rfl⟩ : syracuseStep 2005835 = 3008753) B3008753
theorem B5077835 : Blo 1336987 5077835 := bstep (se 1 (by rfl) ⟨3808376, by rfl⟩ : syracuseStep 5077835 = 7616753) B7616753
theorem B2005847 : Blo 1336987 2005847 := bstep (se 1 (by rfl) ⟨1504385, by rfl⟩ : syracuseStep 2005847 = 3008771) B3008771
theorem B5077849 : Blo 1336987 5077849 := bstep (se 2 (by rfl) ⟨1904193, by rfl⟩ : syracuseStep 5077849 = 3808387) B3808387
theorem B8575895 : Blo 1336987 8575895 := bstep (se 1 (by rfl) ⟨6431921, by rfl⟩ : syracuseStep 8575895 = 12863843) B12863843
theorem B1506199 : Blo 1336987 1506199 := bstep (se 1 (by rfl) ⟨1129649, by rfl⟩ : syracuseStep 1506199 = 2259299) B2259299
theorem B2005913 : Blo 1336987 2005913 := bstep (se 2 (by rfl) ⟨752217, by rfl⟩ : syracuseStep 2005913 = 1504435) B1504435
theorem B2857931 : Blo 1336987 2857931 := bstep (se 1 (by rfl) ⟨2143448, by rfl⟩ : syracuseStep 2857931 = 4286897) B4286897
theorem B5716939 : Blo 1336987 5716939 := bstep (se 1 (by rfl) ⟨4287704, by rfl⟩ : syracuseStep 5716939 = 8575409) B8575409
theorem B6183901 : Blo 1336987 6183901 := bstep (se 3 (by rfl) ⟨1159481, by rfl⟩ : syracuseStep 6183901 = 2318963) B2318963
theorem B2006027 : Blo 1336987 2006027 := bstep (se 1 (by rfl) ⟨1504520, by rfl⟩ : syracuseStep 2006027 = 3009041) B3009041
theorem B19282961 : Blo 1336987 19282961 := bstep (se 2 (by rfl) ⟨7231110, by rfl⟩ : syracuseStep 19282961 = 14462221) B14462221
theorem B2006039 : Blo 1336987 2006039 := bstep (se 1 (by rfl) ⟨1504529, by rfl⟩ : syracuseStep 2006039 = 3009059) B3009059
theorem B4512833 : Blo 1336987 4512833 := bstep (se 2 (by rfl) ⟨1692312, by rfl⟩ : syracuseStep 4512833 = 3384625) B3384625
theorem B2006105 : Blo 1336987 2006105 := bstep (se 2 (by rfl) ⟨752289, by rfl⟩ : syracuseStep 2006105 = 1504579) B1504579
theorem B3431575 : Blo 1336987 3431575 := bstep (se 1 (by rfl) ⟨2573681, by rfl⟩ : syracuseStep 3431575 = 5147363) B5147363
theorem B2006219 : Blo 1336987 2006219 := bstep (se 1 (by rfl) ⟨1504664, by rfl⟩ : syracuseStep 2006219 = 3009329) B3009329
theorem B2006231 : Blo 1336987 2006231 := bstep (se 1 (by rfl) ⟨1504673, by rfl⟩ : syracuseStep 2006231 = 3009347) B3009347
theorem B5790937 : Blo 1336987 5790937 := bstep (se 2 (by rfl) ⟨2171601, by rfl⟩ : syracuseStep 5790937 = 4343203) B4343203
theorem B5717213 : Blo 1336987 5717213 := bstep (se 3 (by rfl) ⟨1071977, by rfl⟩ : syracuseStep 5717213 = 2143955) B2143955
theorem B2006297 : Blo 1336987 2006297 := bstep (se 2 (by rfl) ⟨752361, by rfl⟩ : syracuseStep 2006297 = 1504723) B1504723
theorem B2538803 : Blo 1336987 2538803 := bstep (se 1 (by rfl) ⟨1904102, by rfl⟩ : syracuseStep 2538803 = 3808205) B3808205
theorem B4070749 : Blo 1336987 4070749 := bstep (se 3 (by rfl) ⟨763265, by rfl⟩ : syracuseStep 4070749 = 1526531) B1526531
theorem B2006411 : Blo 1336987 2006411 := bstep (se 1 (by rfl) ⟨1504808, by rfl⟩ : syracuseStep 2006411 = 3009617) B3009617
theorem B2006423 : Blo 1336987 2006423 := bstep (se 1 (by rfl) ⟨1504817, by rfl⟩ : syracuseStep 2006423 = 3009635) B3009635
theorem B2538955 : Blo 1336987 2538955 := bstep (se 1 (by rfl) ⟨1904216, by rfl⟩ : syracuseStep 2538955 = 3808433) B3808433
theorem B2006489 : Blo 1336987 2006489 := bstep (se 2 (by rfl) ⟨752433, by rfl⟩ : syracuseStep 2006489 = 1504867) B1504867
theorem B2006603 : Blo 1336987 2006603 := bstep (se 1 (by rfl) ⟨1504952, by rfl⟩ : syracuseStep 2006603 = 3009905) B3009905
theorem B2006615 : Blo 1336987 2006615 := bstep (se 1 (by rfl) ⟨1504961, by rfl⟩ : syracuseStep 2006615 = 3009923) B3009923
theorem B4513373 : Blo 1336987 4513373 := bstep (se 3 (by rfl) ⟨846257, by rfl⟩ : syracuseStep 4513373 = 1692515) B1692515
theorem B22871645 : Blo 1336987 22871645 := bstep (se 3 (by rfl) ⟨4288433, by rfl⟩ : syracuseStep 22871645 = 8576867) B8576867
theorem B2006681 : Blo 1336987 2006681 := bstep (se 2 (by rfl) ⟨752505, by rfl⟩ : syracuseStep 2006681 = 1505011) B1505011
theorem B12205829 : Blo 1336987 12205829 := bstep (se 4 (by rfl) ⟨1144296, by rfl⟩ : syracuseStep 12205829 = 2288593) B2288593
theorem B2006795 : Blo 1336987 2006795 := bstep (se 1 (by rfl) ⟨1505096, by rfl⟩ : syracuseStep 2006795 = 3010193) B3010193
theorem B5078807 : Blo 1336987 5078807 := bstep (se 1 (by rfl) ⟨3809105, by rfl⟩ : syracuseStep 5078807 = 7618211) B7618211
theorem B2006807 : Blo 1336987 2006807 := bstep (se 1 (by rfl) ⟨1505105, by rfl⟩ : syracuseStep 2006807 = 3010211) B3010211
theorem B2539289 : Blo 1336987 2539289 := bstep (se 2 (by rfl) ⟨952233, by rfl⟩ : syracuseStep 2539289 = 1904467) B1904467
theorem B2006873 : Blo 1336987 2006873 := bstep (se 2 (by rfl) ⟨752577, by rfl⟩ : syracuseStep 2006873 = 1505155) B1505155
theorem B10166147 : Blo 1336987 10166147 := bstep (se 1 (by rfl) ⟨7624610, by rfl⟩ : syracuseStep 10166147 = 15249221) B15249221
theorem B2858905 : Blo 1336987 2858905 := bstep (se 2 (by rfl) ⟨1072089, by rfl⟩ : syracuseStep 2858905 = 2144179) B2144179
theorem B65118131 : Blo 1336987 65118131 := bstep (se 1 (by rfl) ⟨48838598, by rfl⟩ : syracuseStep 65118131 = 97677197) B97677197
theorem B5496769 : Blo 1336987 5496769 := bstep (se 2 (by rfl) ⟨2061288, by rfl⟩ : syracuseStep 5496769 = 4122577) B4122577
theorem B2006987 : Blo 1336987 2006987 := bstep (se 1 (by rfl) ⟨1505240, by rfl⟩ : syracuseStep 2006987 = 3010481) B3010481
theorem B2006999 : Blo 1336987 2006999 := bstep (se 1 (by rfl) ⟨1505249, by rfl⟩ : syracuseStep 2006999 = 3010499) B3010499
theorem B2007047 : Blo 1336987 2007047 := bstep (se 1 (by rfl) ⟨1505285, by rfl⟩ : syracuseStep 2007047 = 3010571) B3010571
theorem B2007083 : Blo 1336987 2007083 := bstep (se 1 (by rfl) ⟨1505312, by rfl⟩ : syracuseStep 2007083 = 3010625) B3010625
theorem B4890691 : Blo 1336987 4890691 := bstep (se 1 (by rfl) ⟨3668018, by rfl⟩ : syracuseStep 4890691 = 7336037) B7336037
theorem B2007113 : Blo 1336987 2007113 := bstep (se 2 (by rfl) ⟨752667, by rfl⟩ : syracuseStep 2007113 = 1505335) B1505335
theorem B2007227 : Blo 1336987 2007227 := bstep (se 1 (by rfl) ⟨1505420, by rfl⟩ : syracuseStep 2007227 = 3010841) B3010841
theorem B2007287 : Blo 1336987 2007287 := bstep (se 1 (by rfl) ⟨1505465, by rfl⟩ : syracuseStep 2007287 = 3010931) B3010931
theorem B2007311 : Blo 1336987 2007311 := bstep (se 1 (by rfl) ⟨1505483, by rfl⟩ : syracuseStep 2007311 = 3010967) B3010967
theorem B2007353 : Blo 1336987 2007353 := bstep (se 2 (by rfl) ⟨752757, by rfl⟩ : syracuseStep 2007353 = 1505515) B1505515
theorem B4514183 : Blo 1336987 4514183 := bstep (se 1 (by rfl) ⟨3385637, by rfl⟩ : syracuseStep 4514183 = 6771275) B6771275
theorem B2007431 : Blo 1336987 2007431 := bstep (se 1 (by rfl) ⟨1505573, by rfl⟩ : syracuseStep 2007431 = 3011147) B3011147
theorem B7618961 : Blo 1336987 7618961 := bstep (se 2 (by rfl) ⟨2857110, by rfl⟩ : syracuseStep 7618961 = 5714221) B5714221
theorem B2007467 : Blo 1336987 2007467 := bstep (se 1 (by rfl) ⟨1505600, by rfl⟩ : syracuseStep 2007467 = 3011201) B3011201
theorem B2007497 : Blo 1336987 2007497 := bstep (se 2 (by rfl) ⟨752811, by rfl⟩ : syracuseStep 2007497 = 1505623) B1505623
theorem B20595185 : Blo 1336987 20595185 := bstep (se 2 (by rfl) ⟨7723194, by rfl⟩ : syracuseStep 20595185 = 15446389) B15446389
theorem B5079581 : Blo 1336987 5079581 := bstep (se 3 (by rfl) ⟨952421, by rfl⟩ : syracuseStep 5079581 = 1904843) B1904843
theorem B6775325 : Blo 1336987 6775325 := bstep (se 3 (by rfl) ⟨1270373, by rfl⟩ : syracuseStep 6775325 = 2540747) B2540747
theorem B2859563 : Blo 1336987 2859563 := bstep (se 1 (by rfl) ⟨2144672, by rfl⟩ : syracuseStep 2859563 = 4289345) B4289345
theorem B2007611 : Blo 1336987 2007611 := bstep (se 1 (by rfl) ⟨1505708, by rfl⟩ : syracuseStep 2007611 = 3011417) B3011417
theorem B5718595 : Blo 1336987 5718595 := bstep (se 1 (by rfl) ⟨4288946, by rfl⟩ : syracuseStep 5718595 = 8577893) B8577893
theorem B2007671 : Blo 1336987 2007671 := bstep (se 1 (by rfl) ⟨1505753, by rfl⟩ : syracuseStep 2007671 = 3011507) B3011507
theorem B2007695 : Blo 1336987 2007695 := bstep (se 1 (by rfl) ⟨1505771, by rfl⟩ : syracuseStep 2007695 = 3011543) B3011543
theorem B2007737 : Blo 1336987 2007737 := bstep (se 2 (by rfl) ⟨752901, by rfl⟩ : syracuseStep 2007737 = 1505803) B1505803
theorem B9642725 : Blo 1336987 9642725 := bstep (se 4 (by rfl) ⟨904005, by rfl⟩ : syracuseStep 9642725 = 1808011) B1808011
theorem B4514561 : Blo 1336987 4514561 := bstep (se 2 (by rfl) ⟨1692960, by rfl⟩ : syracuseStep 4514561 = 3385921) B3385921
theorem B2007815 : Blo 1336987 2007815 := bstep (se 1 (by rfl) ⟨1505861, by rfl⟩ : syracuseStep 2007815 = 3011723) B3011723
theorem B18301733 : Blo 1336987 18301733 := bstep (se 4 (by rfl) ⟨1715787, by rfl⟩ : syracuseStep 18301733 = 3431575) B3431575
theorem B2007851 : Blo 1336987 2007851 := bstep (se 1 (by rfl) ⟨1505888, by rfl⟩ : syracuseStep 2007851 = 3011777) B3011777
theorem B2007881 : Blo 1336987 2007881 := bstep (se 2 (by rfl) ⟨752955, by rfl⟩ : syracuseStep 2007881 = 1505911) B1505911
theorem B7619417 : Blo 1336987 7619417 := bstep (se 2 (by rfl) ⟨2857281, by rfl⟩ : syracuseStep 7619417 = 5714563) B5714563
theorem B5718937 : Blo 1336987 5718937 := bstep (se 2 (by rfl) ⟨2144601, by rfl⟩ : syracuseStep 5718937 = 4289203) B4289203
theorem B3810233 : Blo 1336987 3810233 := bstep (se 2 (by rfl) ⟨1428837, by rfl⟩ : syracuseStep 3810233 = 2857675) B2857675
theorem B2007995 : Blo 1336987 2007995 := bstep (se 1 (by rfl) ⟨1505996, by rfl⟩ : syracuseStep 2007995 = 3011993) B3011993
theorem B2008055 : Blo 1336987 2008055 := bstep (se 1 (by rfl) ⟨1506041, by rfl⟩ : syracuseStep 2008055 = 3012083) B3012083
theorem B6775811 : Blo 1336987 6775811 := bstep (se 1 (by rfl) ⟨5081858, by rfl⟩ : syracuseStep 6775811 = 10163717) B10163717
theorem B2008079 : Blo 1336987 2008079 := bstep (se 1 (by rfl) ⟨1506059, by rfl⟩ : syracuseStep 2008079 = 3012119) B3012119
theorem B3810347 : Blo 1336987 3810347 := bstep (se 1 (by rfl) ⟨2857760, by rfl⟩ : syracuseStep 3810347 = 5715521) B5715521
theorem B2008121 : Blo 1336987 2008121 := bstep (se 2 (by rfl) ⟨753045, by rfl⟩ : syracuseStep 2008121 = 1506091) B1506091
theorem B2008199 : Blo 1336987 2008199 := bstep (se 1 (by rfl) ⟨1506149, by rfl⟩ : syracuseStep 2008199 = 3012299) B3012299
theorem B2008235 : Blo 1336987 2008235 := bstep (se 1 (by rfl) ⟨1506176, by rfl⟩ : syracuseStep 2008235 = 3012353) B3012353
theorem B5080265 : Blo 1336987 5080265 := bstep (se 2 (by rfl) ⟨1905099, by rfl⟩ : syracuseStep 5080265 = 3810199) B3810199
theorem B2008265 : Blo 1336987 2008265 := bstep (se 2 (by rfl) ⟨753099, by rfl⟩ : syracuseStep 2008265 = 1506199) B1506199
theorem B15230267 : Blo 1336987 15230267 := bstep (se 1 (by rfl) ⟨11422700, by rfl⟩ : syracuseStep 15230267 = 22845401) B22845401
theorem B2008379 : Blo 1336987 2008379 := bstep (se 1 (by rfl) ⟨1506284, by rfl⟩ : syracuseStep 2008379 = 3012569) B3012569
theorem B2008439 : Blo 1336987 2008439 := bstep (se 1 (by rfl) ⟨1506329, by rfl⟩ : syracuseStep 2008439 = 3012659) B3012659
theorem B2008463 : Blo 1336987 2008463 := bstep (se 1 (by rfl) ⟨1506347, by rfl⟩ : syracuseStep 2008463 = 3012695) B3012695
theorem B4515371 : Blo 1336987 4515371 := bstep (se 1 (by rfl) ⟨3386528, by rfl⟩ : syracuseStep 4515371 = 6773057) B6773057
theorem B2541203 : Blo 1336987 2541203 := bstep (se 1 (by rfl) ⟨1905902, by rfl⟩ : syracuseStep 2541203 = 3811805) B3811805
theorem B1337019 : Blo 1336987 1337019 := bstep (se 1 (by rfl) ⟨1002764, by rfl⟩ : syracuseStep 1337019 = 2005529) B2005529
theorem B8578817 : Blo 1336987 8578817 := bstep (se 2 (by rfl) ⟨3217056, by rfl⟩ : syracuseStep 8578817 = 6434113) B6434113
theorem B1337095 : Blo 1336987 1337095 := bstep (se 1 (by rfl) ⟨1002821, by rfl⟩ : syracuseStep 1337095 = 2005643) B2005643
theorem B1337103 : Blo 1336987 1337103 := bstep (se 1 (by rfl) ⟨1002827, by rfl⟩ : syracuseStep 1337103 = 2005655) B2005655
theorem B1337147 : Blo 1336987 1337147 := bstep (se 1 (by rfl) ⟨1002860, by rfl⟩ : syracuseStep 1337147 = 2005721) B2005721
theorem B3008375 : Blo 1336987 3008375 := bstep (se 1 (by rfl) ⟨2256281, by rfl⟩ : syracuseStep 3008375 = 4512563) B4512563
theorem B2541431 : Blo 1336987 2541431 := bstep (se 1 (by rfl) ⟨1906073, by rfl⟩ : syracuseStep 2541431 = 3812147) B3812147
theorem B1337223 : Blo 1336987 1337223 := bstep (se 1 (by rfl) ⟨1002917, by rfl⟩ : syracuseStep 1337223 = 2005835) B2005835
theorem B3385223 : Blo 1336987 3385223 := bstep (se 1 (by rfl) ⟨2538917, by rfl⟩ : syracuseStep 3385223 = 5077835) B5077835
theorem B1337231 : Blo 1336987 1337231 := bstep (se 1 (by rfl) ⟨1002923, by rfl⟩ : syracuseStep 1337231 = 2005847) B2005847
theorem B3385273 : Blo 1336987 3385273 := bstep (se 2 (by rfl) ⟨1269477, by rfl⟩ : syracuseStep 3385273 = 2538955) B2538955
theorem B1337275 : Blo 1336987 1337275 := bstep (se 1 (by rfl) ⟨1002956, by rfl⟩ : syracuseStep 1337275 = 2005913) B2005913
theorem B1337351 : Blo 1336987 1337351 := bstep (se 1 (by rfl) ⟨1003013, by rfl⟩ : syracuseStep 1337351 = 2006027) B2006027
theorem B12855307 : Blo 1336987 12855307 := bstep (se 1 (by rfl) ⟨9641480, by rfl⟩ : syracuseStep 12855307 = 19282961) B19282961
theorem B1337359 : Blo 1336987 1337359 := bstep (se 1 (by rfl) ⟨1003019, by rfl⟩ : syracuseStep 1337359 = 2006039) B2006039
theorem B6768683 : Blo 1336987 6768683 := bstep (se 1 (by rfl) ⟨5076512, by rfl⟩ : syracuseStep 6768683 = 10153025) B10153025
theorem B3008555 : Blo 1336987 3008555 := bstep (se 1 (by rfl) ⟨2256416, by rfl⟩ : syracuseStep 3008555 = 4512833) B4512833
theorem B1337403 : Blo 1336987 1337403 := bstep (se 1 (by rfl) ⟨1003052, by rfl⟩ : syracuseStep 1337403 = 2006105) B2006105
theorem B1337479 : Blo 1336987 1337479 := bstep (se 1 (by rfl) ⟨1003109, by rfl⟩ : syracuseStep 1337479 = 2006219) B2006219
theorem B1337487 : Blo 1336987 1337487 := bstep (se 1 (by rfl) ⟨1003115, by rfl⟩ : syracuseStep 1337487 = 2006231) B2006231
theorem B3811475 : Blo 1336987 3811475 := bstep (se 1 (by rfl) ⟨2858606, by rfl⟩ : syracuseStep 3811475 = 5717213) B5717213
theorem B1337531 : Blo 1336987 1337531 := bstep (se 1 (by rfl) ⟨1003148, by rfl⟩ : syracuseStep 1337531 = 2006297) B2006297
theorem B1337607 : Blo 1336987 1337607 := bstep (se 1 (by rfl) ⟨1003205, by rfl⟩ : syracuseStep 1337607 = 2006411) B2006411
theorem B1337615 : Blo 1336987 1337615 := bstep (se 1 (by rfl) ⟨1003211, by rfl⟩ : syracuseStep 1337615 = 2006423) B2006423
theorem B3049787 : Blo 1336987 3049787 := bstep (se 1 (by rfl) ⟨2287340, by rfl⟩ : syracuseStep 3049787 = 4574681) B4574681
theorem B1337659 : Blo 1336987 1337659 := bstep (se 1 (by rfl) ⟨1003244, by rfl⟩ : syracuseStep 1337659 = 2006489) B2006489
theorem B1337735 : Blo 1336987 1337735 := bstep (se 1 (by rfl) ⟨1003301, by rfl⟩ : syracuseStep 1337735 = 2006603) B2006603
theorem B1337743 : Blo 1336987 1337743 := bstep (se 1 (by rfl) ⟨1003307, by rfl⟩ : syracuseStep 1337743 = 2006615) B2006615
theorem B3008915 : Blo 1336987 3008915 := bstep (se 1 (by rfl) ⟨2256686, by rfl⟩ : syracuseStep 3008915 = 4513373) B4513373
theorem B15247763 : Blo 1336987 15247763 := bstep (se 1 (by rfl) ⟨11435822, by rfl⟩ : syracuseStep 15247763 = 22871645) B22871645
theorem B1337787 : Blo 1336987 1337787 := bstep (se 1 (by rfl) ⟨1003340, by rfl⟩ : syracuseStep 1337787 = 2006681) B2006681
theorem B3008969 : Blo 1336987 3008969 := bstep (se 2 (by rfl) ⟨1128363, by rfl⟩ : syracuseStep 3008969 = 2256727) B2256727
theorem B6425041 : Blo 1336987 6425041 := bstep (se 2 (by rfl) ⟨2409390, by rfl⟩ : syracuseStep 6425041 = 4818781) B4818781
theorem B8137219 : Blo 1336987 8137219 := bstep (se 1 (by rfl) ⟨6102914, by rfl⟩ : syracuseStep 8137219 = 12205829) B12205829
theorem B1337863 : Blo 1336987 1337863 := bstep (se 1 (by rfl) ⟨1003397, by rfl⟩ : syracuseStep 1337863 = 2006795) B2006795
theorem B3385871 : Blo 1336987 3385871 := bstep (se 1 (by rfl) ⟨2539403, by rfl⟩ : syracuseStep 3385871 = 5078807) B5078807
theorem B1337871 : Blo 1336987 1337871 := bstep (se 1 (by rfl) ⟨1003403, by rfl⟩ : syracuseStep 1337871 = 2006807) B2006807
theorem B3213857 : Blo 1336987 3213857 := bstep (se 2 (by rfl) ⟨1205196, by rfl⟩ : syracuseStep 3213857 = 2410393) B2410393
theorem B3811873 : Blo 1336987 3811873 := bstep (se 2 (by rfl) ⟨1429452, by rfl⟩ : syracuseStep 3811873 = 2858905) B2858905
theorem B1337915 : Blo 1336987 1337915 := bstep (se 1 (by rfl) ⟨1003436, by rfl⟩ : syracuseStep 1337915 = 2006873) B2006873
theorem B6777431 : Blo 1336987 6777431 := bstep (se 1 (by rfl) ⟨5083073, by rfl⟩ : syracuseStep 6777431 = 10166147) B10166147
theorem B43412087 : Blo 1336987 43412087 := bstep (se 1 (by rfl) ⟨32559065, by rfl⟩ : syracuseStep 43412087 = 65118131) B65118131
theorem B1337991 : Blo 1336987 1337991 := bstep (se 1 (by rfl) ⟨1003493, by rfl⟩ : syracuseStep 1337991 = 2006987) B2006987
theorem B2574983 : Blo 1336987 2574983 := bstep (se 1 (by rfl) ⟨1931237, by rfl⟩ : syracuseStep 2574983 = 3862475) B3862475
theorem B1337999 : Blo 1336987 1337999 := bstep (se 1 (by rfl) ⟨1003499, by rfl⟩ : syracuseStep 1337999 = 2006999) B2006999
theorem B1338043 : Blo 1336987 1338043 := bstep (se 1 (by rfl) ⟨1003532, by rfl⟩ : syracuseStep 1338043 = 2007065) B2007065
theorem B11430629 : Blo 1336987 11430629 := bstep (se 4 (by rfl) ⟨1071621, by rfl⟩ : syracuseStep 11430629 = 2143243) B2143243
theorem B5794541 : Blo 1336987 5794541 := bstep (se 3 (by rfl) ⟨1086476, by rfl⟩ : syracuseStep 5794541 = 2172953) B2172953
theorem B1338119 : Blo 1336987 1338119 := bstep (se 1 (by rfl) ⟨1003589, by rfl⟩ : syracuseStep 1338119 = 2007179) B2007179
theorem B1338127 : Blo 1336987 1338127 := bstep (se 1 (by rfl) ⟨1003595, by rfl⟩ : syracuseStep 1338127 = 2007191) B2007191
theorem B1338171 : Blo 1336987 1338171 := bstep (se 1 (by rfl) ⟨1003628, by rfl⟩ : syracuseStep 1338171 = 2007257) B2007257
theorem B4516667 : Blo 1336987 4516667 := bstep (se 1 (by rfl) ⟨3387500, by rfl⟩ : syracuseStep 4516667 = 6775001) B6775001
theorem B1428359 : Blo 1336987 1428359 := bstep (se 1 (by rfl) ⟨1071269, by rfl⟩ : syracuseStep 1428359 = 2142539) B2142539
theorem B1338247 : Blo 1336987 1338247 := bstep (se 1 (by rfl) ⟨1003685, by rfl⟩ : syracuseStep 1338247 = 2007371) B2007371
theorem B1338255 : Blo 1336987 1338255 := bstep (se 1 (by rfl) ⟨1003691, by rfl⟩ : syracuseStep 1338255 = 2007383) B2007383
theorem B34761635 : Blo 1336987 34761635 := bstep (se 1 (by rfl) ⟨26071226, by rfl⟩ : syracuseStep 34761635 = 52142453) B52142453
theorem B5082041 : Blo 1336987 5082041 := bstep (se 2 (by rfl) ⟨1905765, by rfl⟩ : syracuseStep 5082041 = 3811531) B3811531
theorem B1338299 : Blo 1336987 1338299 := bstep (se 1 (by rfl) ⟨1003724, by rfl⟩ : syracuseStep 1338299 = 2007449) B2007449
theorem B13028357 : Blo 1336987 13028357 := bstep (se 4 (by rfl) ⟨1221408, by rfl⟩ : syracuseStep 13028357 = 2442817) B2442817
theorem B1338375 : Blo 1336987 1338375 := bstep (se 1 (by rfl) ⟨1003781, by rfl⟩ : syracuseStep 1338375 = 2007563) B2007563
theorem B1526791 : Blo 1336987 1526791 := bstep (se 1 (by rfl) ⟨1145093, by rfl⟩ : syracuseStep 1526791 = 2290187) B2290187
theorem B1338383 : Blo 1336987 1338383 := bstep (se 1 (by rfl) ⟨1003787, by rfl⟩ : syracuseStep 1338383 = 2007575) B2007575
theorem B7334941 : Blo 1336987 7334941 := bstep (se 3 (by rfl) ⟨1375301, by rfl⟩ : syracuseStep 7334941 = 2750603) B2750603
theorem B1338427 : Blo 1336987 1338427 := bstep (se 1 (by rfl) ⟨1003820, by rfl⟩ : syracuseStep 1338427 = 2007641) B2007641
theorem B6777917 : Blo 1336987 6777917 := bstep (se 3 (by rfl) ⟨1270859, by rfl⟩ : syracuseStep 6777917 = 2541719) B2541719
theorem B16264309 : Blo 1336987 16264309 := bstep (se 5 (by rfl) ⟨762389, by rfl⟩ : syracuseStep 16264309 = 1524779) B1524779
theorem B3009671 : Blo 1336987 3009671 := bstep (se 1 (by rfl) ⟨2257253, by rfl⟩ : syracuseStep 3009671 = 4514507) B4514507
theorem B1338503 : Blo 1336987 1338503 := bstep (se 1 (by rfl) ⟨1003877, by rfl⟩ : syracuseStep 1338503 = 2007755) B2007755
theorem B1338511 : Blo 1336987 1338511 := bstep (se 1 (by rfl) ⟨1003883, by rfl⟩ : syracuseStep 1338511 = 2007767) B2007767
theorem B1338555 : Blo 1336987 1338555 := bstep (se 1 (by rfl) ⟨1003916, by rfl⟩ : syracuseStep 1338555 = 2007833) B2007833
theorem B3386569 : Blo 1336987 3386569 := bstep (se 2 (by rfl) ⟨1269963, by rfl⟩ : syracuseStep 3386569 = 2539927) B2539927
theorem B3304649 : Blo 1336987 3304649 := bstep (se 2 (by rfl) ⟨1239243, by rfl⟩ : syracuseStep 3304649 = 2478487) B2478487
theorem B1338631 : Blo 1336987 1338631 := bstep (se 1 (by rfl) ⟨1003973, by rfl⟩ : syracuseStep 1338631 = 2007947) B2007947
theorem B1338639 : Blo 1336987 1338639 := bstep (se 1 (by rfl) ⟨1003979, by rfl⟩ : syracuseStep 1338639 = 2007959) B2007959
theorem B4517153 : Blo 1336987 4517153 := bstep (se 2 (by rfl) ⟨1693932, by rfl⟩ : syracuseStep 4517153 = 3387865) B3387865
theorem B1903915 : Blo 1336987 1903915 := bstep (se 1 (by rfl) ⟨1427936, by rfl⟩ : syracuseStep 1903915 = 2855873) B2855873
theorem B2256187 : Blo 1336987 2256187 := bstep (se 1 (by rfl) ⟨1692140, by rfl⟩ : syracuseStep 2256187 = 3384281) B3384281
theorem B6769979 : Blo 1336987 6769979 := bstep (se 1 (by rfl) ⟨5077484, by rfl⟩ : syracuseStep 6769979 = 10154969) B10154969
theorem B3009851 : Blo 1336987 3009851 := bstep (se 1 (by rfl) ⟨2257388, by rfl⟩ : syracuseStep 3009851 = 4514777) B4514777
theorem B1338683 : Blo 1336987 1338683 := bstep (se 1 (by rfl) ⟨1004012, by rfl⟩ : syracuseStep 1338683 = 2008025) B2008025
theorem B3386711 : Blo 1336987 3386711 := bstep (se 1 (by rfl) ⟨2540033, by rfl⟩ : syracuseStep 3386711 = 5080067) B5080067
theorem B27839875 : Blo 1336987 27839875 := bstep (se 1 (by rfl) ⟨20879906, by rfl⟩ : syracuseStep 27839875 = 41759813) B41759813
theorem B1338759 : Blo 1336987 1338759 := bstep (se 1 (by rfl) ⟨1004069, by rfl⟩ : syracuseStep 1338759 = 2008139) B2008139
theorem B1338767 : Blo 1336987 1338767 := bstep (se 1 (by rfl) ⟨1004075, by rfl⟩ : syracuseStep 1338767 = 2008151) B2008151
theorem B11431313 : Blo 1336987 11431313 := bstep (se 2 (by rfl) ⟨4286742, by rfl⟩ : syracuseStep 11431313 = 8573485) B8573485
theorem B3812761 : Blo 1336987 3812761 := bstep (se 2 (by rfl) ⟨1429785, by rfl⟩ : syracuseStep 3812761 = 2859571) B2859571
theorem B3009977 : Blo 1336987 3009977 := bstep (se 2 (by rfl) ⟨1128741, by rfl⟩ : syracuseStep 3009977 = 2257483) B2257483
theorem B1338811 : Blo 1336987 1338811 := bstep (se 1 (by rfl) ⟨1004108, by rfl⟩ : syracuseStep 1338811 = 2008217) B2008217
theorem B2256329 : Blo 1336987 2256329 := bstep (se 2 (by rfl) ⟨846123, by rfl⟩ : syracuseStep 2256329 = 1692247) B1692247
theorem B6770141 : Blo 1336987 6770141 := bstep (se 3 (by rfl) ⟨1269401, by rfl⟩ : syracuseStep 6770141 = 2538803) B2538803
theorem B16281091 : Blo 1336987 16281091 := bstep (se 1 (by rfl) ⟨12210818, by rfl⟩ : syracuseStep 16281091 = 24421637) B24421637
theorem B1338887 : Blo 1336987 1338887 := bstep (se 1 (by rfl) ⟨1004165, by rfl⟩ : syracuseStep 1338887 = 2008331) B2008331
theorem B1904143 : Blo 1336987 1904143 := bstep (se 1 (by rfl) ⟨1428107, by rfl⟩ : syracuseStep 1904143 = 2856215) B2856215
theorem B1338895 : Blo 1336987 1338895 := bstep (se 1 (by rfl) ⟨1004171, by rfl⟩ : syracuseStep 1338895 = 2008343) B2008343
theorem B2412065 : Blo 1336987 2412065 := bstep (se 2 (by rfl) ⟨904524, by rfl⟩ : syracuseStep 2412065 = 1809049) B1809049
theorem B1429051 : Blo 1336987 1429051 := bstep (se 1 (by rfl) ⟨1071788, by rfl⟩ : syracuseStep 1429051 = 2143577) B2143577
theorem B1338939 : Blo 1336987 1338939 := bstep (se 1 (by rfl) ⟨1004204, by rfl⟩ : syracuseStep 1338939 = 2008409) B2008409
theorem B32566859 : Blo 1336987 32566859 := bstep (se 1 (by rfl) ⟨24425144, by rfl⟩ : syracuseStep 32566859 = 48850289) B48850289
theorem B28929635 : Blo 1336987 28929635 := bstep (se 1 (by rfl) ⟨21697226, by rfl⟩ : syracuseStep 28929635 = 43394453) B43394453
theorem B3010319 : Blo 1336987 3010319 := bstep (se 1 (by rfl) ⟨2257739, by rfl⟩ : syracuseStep 3010319 = 4515479) B4515479
theorem B6770465 : Blo 1336987 6770465 := bstep (se 2 (by rfl) ⟨2538924, by rfl⟩ : syracuseStep 6770465 = 5077849) B5077849
theorem B3010337 : Blo 1336987 3010337 := bstep (se 2 (by rfl) ⟨1128876, by rfl⟩ : syracuseStep 3010337 = 2257753) B2257753
theorem B4517747 : Blo 1336987 4517747 := bstep (se 1 (by rfl) ⟨3388310, by rfl⟩ : syracuseStep 4517747 = 6776621) B6776621
theorem B5713811 : Blo 1336987 5713811 := bstep (se 1 (by rfl) ⟨4285358, by rfl⟩ : syracuseStep 5713811 = 8570717) B8570717
theorem B20590487 : Blo 1336987 20590487 := bstep (se 1 (by rfl) ⟨15442865, by rfl⟩ : syracuseStep 20590487 = 30885731) B30885731
theorem B7622585 : Blo 1336987 7622585 := bstep (se 2 (by rfl) ⟨2858469, by rfl⟩ : syracuseStep 7622585 = 5716939) B5716939
theorem B8245201 : Blo 1336987 8245201 := bstep (se 2 (by rfl) ⟨3091950, by rfl⟩ : syracuseStep 8245201 = 6183901) B6183901
theorem B4821059 : Blo 1336987 4821059 := bstep (se 1 (by rfl) ⟨3615794, by rfl⟩ : syracuseStep 4821059 = 7231589) B7231589
theorem B3010679 : Blo 1336987 3010679 := bstep (se 1 (by rfl) ⟨2258009, by rfl⟩ : syracuseStep 3010679 = 4516019) B4516019
theorem B2257031 : Blo 1336987 2257031 := bstep (se 1 (by rfl) ⟨1692773, by rfl⟩ : syracuseStep 2257031 = 3385547) B3385547
theorem B8138989 : Blo 1336987 8138989 := bstep (se 3 (by rfl) ⟨1526060, by rfl⟩ : syracuseStep 8138989 = 3052121) B3052121
theorem B7721249 : Blo 1336987 7721249 := bstep (se 2 (by rfl) ⟨2895468, by rfl⟩ : syracuseStep 7721249 = 5790937) B5790937
theorem B3010859 : Blo 1336987 3010859 := bstep (se 1 (by rfl) ⟨2258144, by rfl⟩ : syracuseStep 3010859 = 4516289) B4516289
theorem B11432339 : Blo 1336987 11432339 := bstep (se 1 (by rfl) ⟨8574254, by rfl⟩ : syracuseStep 11432339 = 17148509) B17148509
theorem B12849617 : Blo 1336987 12849617 := bstep (se 2 (by rfl) ⟨4818606, by rfl⟩ : syracuseStep 12849617 = 9637213) B9637213
theorem B5427665 : Blo 1336987 5427665 := bstep (se 2 (by rfl) ⟨2035374, by rfl⟩ : syracuseStep 5427665 = 4070749) B4070749
theorem B7615043 : Blo 1336987 7615043 := bstep (se 1 (by rfl) ⟨5711282, by rfl⟩ : syracuseStep 7615043 = 11422565) B11422565
theorem B1905287 : Blo 1336987 1905287 := bstep (se 1 (by rfl) ⟨1428965, by rfl⟩ : syracuseStep 1905287 = 2857931) B2857931
theorem B3011219 : Blo 1336987 3011219 := bstep (se 1 (by rfl) ⟨2258414, by rfl⟩ : syracuseStep 3011219 = 4516829) B4516829
theorem B6427309 : Blo 1336987 6427309 := bstep (se 3 (by rfl) ⟨1205120, by rfl⟩ : syracuseStep 6427309 = 2410241) B2410241
theorem B3011273 : Blo 1336987 3011273 := bstep (se 2 (by rfl) ⟨1129227, by rfl⟩ : syracuseStep 3011273 = 2258455) B2258455
theorem B6771437 : Blo 1336987 6771437 := bstep (se 3 (by rfl) ⟨1269644, by rfl⟩ : syracuseStep 6771437 = 2539289) B2539289
theorem B2257679 : Blo 1336987 2257679 := bstep (se 1 (by rfl) ⟨1693259, by rfl⟩ : syracuseStep 2257679 = 3386519) B3386519
theorem B1905481 : Blo 1336987 1905481 := bstep (se 2 (by rfl) ⟨714555, by rfl⟩ : syracuseStep 1905481 = 1429111) B1429111
theorem B1504399 : Blo 1336987 1504399 := bstep (se 1 (by rfl) ⟨1128299, by rfl⟩ : syracuseStep 1504399 = 2256599) B2256599
theorem B7329025 : Blo 1336987 7329025 := bstep (se 2 (by rfl) ⟨2748384, by rfl⟩ : syracuseStep 7329025 = 5496769) B5496769
theorem B17143073 : Blo 1336987 17143073 := bstep (se 2 (by rfl) ⟨6428652, by rfl⟩ : syracuseStep 17143073 = 12857305) B12857305
theorem B2258219 : Blo 1336987 2258219 := bstep (se 1 (by rfl) ⟨1693664, by rfl⟩ : syracuseStep 2258219 = 3387329) B3387329
theorem B3388787 : Blo 1336987 3388787 := bstep (se 1 (by rfl) ⟨2541590, by rfl⟩ : syracuseStep 3388787 = 5083181) B5083181
theorem B1906039 : Blo 1336987 1906039 := bstep (se 1 (by rfl) ⟨1429529, by rfl⟩ : syracuseStep 1906039 = 2859059) B2859059
theorem B3011975 : Blo 1336987 3011975 := bstep (se 1 (by rfl) ⟨2258981, by rfl⟩ : syracuseStep 3011975 = 4517963) B4517963
theorem B5076377 : Blo 1336987 5076377 := bstep (se 2 (by rfl) ⟨1903641, by rfl⟩ : syracuseStep 5076377 = 3807283) B3807283
theorem B2856377 : Blo 1336987 2856377 := bstep (se 2 (by rfl) ⟨1071141, by rfl⟩ : syracuseStep 2856377 = 2142283) B2142283
theorem B7230941 : Blo 1336987 7230941 := bstep (se 3 (by rfl) ⟨1355801, by rfl⟩ : syracuseStep 7230941 = 2711603) B2711603
theorem B6772247 : Blo 1336987 6772247 := bstep (se 1 (by rfl) ⟨5079185, by rfl⟩ : syracuseStep 6772247 = 10158371) B10158371
theorem B3012155 : Blo 1336987 3012155 := bstep (se 1 (by rfl) ⟨2259116, by rfl⟩ : syracuseStep 3012155 = 4518233) B4518233
theorem B12203597 : Blo 1336987 12203597 := bstep (se 3 (by rfl) ⟨2288174, by rfl⟩ : syracuseStep 12203597 = 4576349) B4576349
theorem B1504903 : Blo 1336987 1504903 := bstep (se 1 (by rfl) ⟨1128677, by rfl⟩ : syracuseStep 1504903 = 2257355) B2257355
theorem B2258617 : Blo 1336987 2258617 := bstep (se 2 (by rfl) ⟨846981, by rfl⟩ : syracuseStep 2258617 = 1693963) B1693963
theorem B3012281 : Blo 1336987 3012281 := bstep (se 2 (by rfl) ⟨1129605, by rfl⟩ : syracuseStep 3012281 = 2259211) B2259211
theorem B1505083 : Blo 1336987 1505083 := bstep (se 1 (by rfl) ⟨1128812, by rfl⟩ : syracuseStep 1505083 = 2257625) B2257625
theorem B3389303 : Blo 1336987 3389303 := bstep (se 1 (by rfl) ⟨2541977, by rfl⟩ : syracuseStep 3389303 = 5083955) B5083955
theorem B3012623 : Blo 1336987 3012623 := bstep (se 1 (by rfl) ⟨2259467, by rfl⟩ : syracuseStep 3012623 = 4518935) B4518935
theorem B3012641 : Blo 1336987 3012641 := bstep (se 2 (by rfl) ⟨1129740, by rfl⟩ : syracuseStep 3012641 = 2259481) B2259481
theorem B8132669 : Blo 1336987 8132669 := bstep (se 3 (by rfl) ⟨1524875, by rfl⟩ : syracuseStep 8132669 = 3049751) B3049751
theorem B3618931 : Blo 1336987 3618931 := bstep (se 1 (by rfl) ⟨2714198, by rfl⟩ : syracuseStep 3618931 = 5428397) B5428397
theorem B1693867 : Blo 1336987 1693867 := bstep (se 1 (by rfl) ⟨1270400, by rfl⟩ : syracuseStep 1693867 = 2540801) B2540801
theorem B1833161 : Blo 1336987 1833161 := bstep (se 2 (by rfl) ⟨687435, by rfl⟩ : syracuseStep 1833161 = 1374871) B1374871
theorem B13727981 : Blo 1336987 13727981 := bstep (se 3 (by rfl) ⟨2573996, by rfl⟩ : syracuseStep 13727981 = 5147993) B5147993
theorem B3807499 : Blo 1336987 3807499 := bstep (se 1 (by rfl) ⟨2855624, by rfl⟩ : syracuseStep 3807499 = 5711249) B5711249
theorem B1505551 : Blo 1336987 1505551 := bstep (se 1 (by rfl) ⟨1129163, by rfl⟩ : syracuseStep 1505551 = 2258327) B2258327
theorem B7624975 : Blo 1336987 7624975 := bstep (se 1 (by rfl) ⟨5718731, by rfl⟩ : syracuseStep 7624975 = 11437463) B11437463
theorem B5077363 : Blo 1336987 5077363 := bstep (se 1 (by rfl) ⟨3808022, by rfl⟩ : syracuseStep 5077363 = 7616045) B7616045
theorem B2259319 : Blo 1336987 2259319 := bstep (se 1 (by rfl) ⟨1694489, by rfl⟩ : syracuseStep 2259319 = 3388979) B3388979
theorem B83507597 : Blo 1336987 83507597 := bstep (se 3 (by rfl) ⟨15657674, by rfl⟩ : syracuseStep 83507597 = 31315349) B31315349
theorem B10164689 : Blo 1336987 10164689 := bstep (se 2 (by rfl) ⟨3811758, by rfl⟩ : syracuseStep 10164689 = 7623517) B7623517
theorem B2005511 : Blo 1336987 2005511 := bstep (se 1 (by rfl) ⟨1504133, by rfl⟩ : syracuseStep 2005511 = 3008267) B3008267
theorem B3807773 : Blo 1336987 3807773 := bstep (se 3 (by rfl) ⟨713957, by rfl⟩ : syracuseStep 3807773 = 1427915) B1427915
theorem B2005547 : Blo 1336987 2005547 := bstep (se 1 (by rfl) ⟨1504160, by rfl⟩ : syracuseStep 2005547 = 3008321) B3008321
theorem B2259515 : Blo 1336987 2259515 := bstep (se 1 (by rfl) ⟨1694636, by rfl⟩ : syracuseStep 2259515 = 3389273) B3389273
theorem B2005577 : Blo 1336987 2005577 := bstep (se 2 (by rfl) ⟨752091, by rfl⟩ : syracuseStep 2005577 = 1504183) B1504183
theorem B2062967 : Blo 1336987 2062967 := bstep (se 1 (by rfl) ⟨1547225, by rfl⟩ : syracuseStep 2062967 = 3094451) B3094451
theorem B3717767 : Blo 1336987 3717767 := bstep (se 1 (by rfl) ⟨2788325, by rfl⟩ : syracuseStep 3717767 = 5576651) B5576651
theorem B2005691 : Blo 1336987 2005691 := bstep (se 1 (by rfl) ⟨1504268, by rfl⟩ : syracuseStep 2005691 = 3008537) B3008537
theorem B19806913 : Blo 1336987 19806913 := bstep (se 2 (by rfl) ⟨7427592, by rfl⟩ : syracuseStep 19806913 = 14855185) B14855185
theorem B2005751 : Blo 1336987 2005751 := bstep (se 1 (by rfl) ⟨1504313, by rfl⟩ : syracuseStep 2005751 = 3008627) B3008627
theorem B1506055 : Blo 1336987 1506055 := bstep (se 1 (by rfl) ⟨1129541, by rfl⟩ : syracuseStep 1506055 = 2259083) B2259083
theorem B2005775 : Blo 1336987 2005775 := bstep (se 1 (by rfl) ⟨1504331, by rfl⟩ : syracuseStep 2005775 = 3008663) B3008663
theorem B2005817 : Blo 1336987 2005817 := bstep (se 2 (by rfl) ⟨752181, by rfl⟩ : syracuseStep 2005817 = 1504363) B1504363
theorem B2005895 : Blo 1336987 2005895 := bstep (se 1 (by rfl) ⟨1504421, by rfl⟩ : syracuseStep 2005895 = 3008843) B3008843
theorem B6429575 : Blo 1336987 6429575 := bstep (se 1 (by rfl) ⟨4822181, by rfl⟩ : syracuseStep 6429575 = 9644363) B9644363
theorem B4889497 : Blo 1336987 4889497 := bstep (se 2 (by rfl) ⟨1833561, by rfl⟩ : syracuseStep 4889497 = 3667123) B3667123
theorem B2005931 : Blo 1336987 2005931 := bstep (se 1 (by rfl) ⟨1504448, by rfl⟩ : syracuseStep 2005931 = 3008897) B3008897
theorem B1506235 : Blo 1336987 1506235 := bstep (se 1 (by rfl) ⟨1129676, by rfl⟩ : syracuseStep 1506235 = 2259353) B2259353
theorem B2005961 : Blo 1336987 2005961 := bstep (se 2 (by rfl) ⟨752235, by rfl⟩ : syracuseStep 2005961 = 1504471) B1504471
theorem B4512779 : Blo 1336987 4512779 := bstep (se 1 (by rfl) ⟨3384584, by rfl⟩ : syracuseStep 4512779 = 6769169) B6769169
theorem B2857999 : Blo 1336987 2857999 := bstep (se 1 (by rfl) ⟨2143499, by rfl⟩ : syracuseStep 2857999 = 4286999) B4286999
theorem B2858017 : Blo 1336987 2858017 := bstep (se 2 (by rfl) ⟨1071756, by rfl⟩ : syracuseStep 2858017 = 2143513) B2143513
theorem B2006075 : Blo 1336987 2006075 := bstep (se 1 (by rfl) ⟨1504556, by rfl⟩ : syracuseStep 2006075 = 3009113) B3009113
theorem B7724119 : Blo 1336987 7724119 := bstep (se 1 (by rfl) ⟨5793089, by rfl⟩ : syracuseStep 7724119 = 11586179) B11586179
theorem B4512887 : Blo 1336987 4512887 := bstep (se 1 (by rfl) ⟨3384665, by rfl⟩ : syracuseStep 4512887 = 6769331) B6769331
theorem B2006135 : Blo 1336987 2006135 := bstep (se 1 (by rfl) ⟨1504601, by rfl⟩ : syracuseStep 2006135 = 3009203) B3009203
theorem B2006159 : Blo 1336987 2006159 := bstep (se 1 (by rfl) ⟨1504619, by rfl⟩ : syracuseStep 2006159 = 3009239) B3009239
theorem B2006201 : Blo 1336987 2006201 := bstep (se 2 (by rfl) ⟨752325, by rfl⟩ : syracuseStep 2006201 = 1504651) B1504651
theorem B2538697 : Blo 1336987 2538697 := bstep (se 2 (by rfl) ⟨952011, by rfl⟩ : syracuseStep 2538697 = 1904023) B1904023
theorem B12860653 : Blo 1336987 12860653 := bstep (se 3 (by rfl) ⟨2411372, by rfl⟩ : syracuseStep 12860653 = 4822745) B4822745
theorem B2006279 : Blo 1336987 2006279 := bstep (se 1 (by rfl) ⟨1504709, by rfl⟩ : syracuseStep 2006279 = 3009419) B3009419
theorem B5717263 : Blo 1336987 5717263 := bstep (se 1 (by rfl) ⟨4287947, by rfl⟩ : syracuseStep 5717263 = 8575895) B8575895
theorem B2006315 : Blo 1336987 2006315 := bstep (se 1 (by rfl) ⟨1504736, by rfl⟩ : syracuseStep 2006315 = 3009473) B3009473
theorem B2006345 : Blo 1336987 2006345 := bstep (se 2 (by rfl) ⟨752379, by rfl⟩ : syracuseStep 2006345 = 1504759) B1504759
theorem B2858375 : Blo 1336987 2858375 := bstep (se 1 (by rfl) ⟨2143781, by rfl⟩ : syracuseStep 2858375 = 4287563) B4287563
theorem B2006459 : Blo 1336987 2006459 := bstep (se 1 (by rfl) ⟨1504844, by rfl⟩ : syracuseStep 2006459 = 3009689) B3009689
theorem B2006519 : Blo 1336987 2006519 := bstep (se 1 (by rfl) ⟨1504889, by rfl⟩ : syracuseStep 2006519 = 3009779) B3009779
theorem B2006543 : Blo 1336987 2006543 := bstep (se 1 (by rfl) ⟨1504907, by rfl⟩ : syracuseStep 2006543 = 3009815) B3009815
theorem B5422621 : Blo 1336987 5422621 := bstep (se 3 (by rfl) ⟨1016741, by rfl⟩ : syracuseStep 5422621 = 2033483) B2033483
theorem B2006585 : Blo 1336987 2006585 := bstep (se 2 (by rfl) ⟨752469, by rfl⟩ : syracuseStep 2006585 = 1504939) B1504939
theorem B2006663 : Blo 1336987 2006663 := bstep (se 1 (by rfl) ⟨1504997, by rfl⟩ : syracuseStep 2006663 = 3009995) B3009995
theorem B2006699 : Blo 1336987 2006699 := bstep (se 1 (by rfl) ⟨1505024, by rfl⟩ : syracuseStep 2006699 = 3010049) B3010049
theorem B4513481 : Blo 1336987 4513481 := bstep (se 2 (by rfl) ⟨1692555, by rfl⟩ : syracuseStep 4513481 = 3385111) B3385111
theorem B2006729 : Blo 1336987 2006729 := bstep (se 2 (by rfl) ⟨752523, by rfl⟩ : syracuseStep 2006729 = 1505047) B1505047
theorem B2006843 : Blo 1336987 2006843 := bstep (se 1 (by rfl) ⟨1505132, by rfl⟩ : syracuseStep 2006843 = 3010265) B3010265
theorem B2006903 : Blo 1336987 2006903 := bstep (se 1 (by rfl) ⟨1505177, by rfl⟩ : syracuseStep 2006903 = 3010355) B3010355
theorem B2006927 : Blo 1336987 2006927 := bstep (se 1 (by rfl) ⟨1505195, by rfl⟩ : syracuseStep 2006927 = 3010391) B3010391
theorem B2006969 : Blo 1336987 2006969 := bstep (se 2 (by rfl) ⟨752613, by rfl⟩ : syracuseStep 2006969 = 1505227) B1505227
theorem B2007119 : Blo 1336987 2007119 := bstep (se 1 (by rfl) ⟨1505339, by rfl⟩ : syracuseStep 2007119 = 3010679) B3010679
theorem B4825241 : Blo 1336987 4825241 := bstep (se 2 (by rfl) ⟨1809465, by rfl⟩ : syracuseStep 4825241 = 3618931) B3618931
theorem B2007239 : Blo 1336987 2007239 := bstep (se 1 (by rfl) ⟨1505429, by rfl⟩ : syracuseStep 2007239 = 3010859) B3010859
theorem B5079307 : Blo 1336987 5079307 := bstep (se 1 (by rfl) ⟨3809480, by rfl⟩ : syracuseStep 5079307 = 7618961) B7618961
theorem B13730123 : Blo 1336987 13730123 := bstep (se 1 (by rfl) ⟨10297592, by rfl⟩ : syracuseStep 13730123 = 20595185) B20595185
theorem B26083685 : Blo 1336987 26083685 := bstep (se 4 (by rfl) ⟨2445345, by rfl⟩ : syracuseStep 26083685 = 4890691) B4890691
theorem B2007401 : Blo 1336987 2007401 := bstep (se 2 (by rfl) ⟨752775, by rfl⟩ : syracuseStep 2007401 = 1505551) B1505551
theorem B10166633 : Blo 1336987 10166633 := bstep (se 2 (by rfl) ⟨3812487, by rfl⟩ : syracuseStep 10166633 = 7624975) B7624975
theorem B2007479 : Blo 1336987 2007479 := bstep (se 1 (by rfl) ⟨1505609, by rfl⟩ : syracuseStep 2007479 = 3011219) B3011219
theorem B2007515 : Blo 1336987 2007515 := bstep (se 1 (by rfl) ⟨1505636, by rfl⟩ : syracuseStep 2007515 = 3011273) B3011273
theorem B4514291 : Blo 1336987 4514291 := bstep (se 1 (by rfl) ⟨3385718, by rfl⟩ : syracuseStep 4514291 = 6771437) B6771437
theorem B5079611 : Blo 1336987 5079611 := bstep (se 1 (by rfl) ⟨3809708, by rfl⟩ : syracuseStep 5079611 = 7619417) B7619417
theorem B2540155 : Blo 1336987 2540155 := bstep (se 1 (by rfl) ⟨1905116, by rfl⟩ : syracuseStep 2540155 = 3810233) B3810233
theorem B2540231 : Blo 1336987 2540231 := bstep (se 1 (by rfl) ⟨1905173, by rfl⟩ : syracuseStep 2540231 = 3810347) B3810347
theorem B11428715 : Blo 1336987 11428715 := bstep (se 1 (by rfl) ⟨8571536, by rfl⟩ : syracuseStep 11428715 = 17143073) B17143073
theorem B8569745 : Blo 1336987 8569745 := bstep (se 2 (by rfl) ⟨3213654, by rfl⟩ : syracuseStep 8569745 = 6427309) B6427309
theorem B2007983 : Blo 1336987 2007983 := bstep (se 1 (by rfl) ⟨1505987, by rfl⟩ : syracuseStep 2007983 = 3011975) B3011975
theorem B3384251 : Blo 1336987 3384251 := bstep (se 1 (by rfl) ⟨2538188, by rfl⟩ : syracuseStep 3384251 = 5076377) B5076377
theorem B105636869 : Blo 1336987 105636869 := bstep (se 4 (by rfl) ⟨9903456, by rfl⟩ : syracuseStep 105636869 = 19806913) B19806913
theorem B2008073 : Blo 1336987 2008073 := bstep (se 2 (by rfl) ⟨753027, by rfl⟩ : syracuseStep 2008073 = 1506055) B1506055
theorem B4514831 : Blo 1336987 4514831 := bstep (se 1 (by rfl) ⟨3386123, by rfl⟩ : syracuseStep 4514831 = 6772247) B6772247
theorem B2008103 : Blo 1336987 2008103 := bstep (se 1 (by rfl) ⟨1506077, by rfl⟩ : syracuseStep 2008103 = 3012155) B3012155
theorem B8135731 : Blo 1336987 8135731 := bstep (se 1 (by rfl) ⟨6101798, by rfl⟩ : syracuseStep 8135731 = 12203597) B12203597
theorem B2540641 : Blo 1336987 2540641 := bstep (se 2 (by rfl) ⟨952740, by rfl⟩ : syracuseStep 2540641 = 1905481) B1905481
theorem B2008187 : Blo 1336987 2008187 := bstep (se 1 (by rfl) ⟨1506140, by rfl⟩ : syracuseStep 2008187 = 3012281) B3012281
theorem B5719211 : Blo 1336987 5719211 := bstep (se 1 (by rfl) ⟨4289408, by rfl⟩ : syracuseStep 5719211 = 8578817) B8578817
theorem B2008313 : Blo 1336987 2008313 := bstep (se 2 (by rfl) ⟨753117, by rfl⟩ : syracuseStep 2008313 = 1506235) B1506235
theorem B2008415 : Blo 1336987 2008415 := bstep (se 1 (by rfl) ⟨1506311, by rfl⟩ : syracuseStep 2008415 = 3012623) B3012623
theorem B3810665 : Blo 1336987 3810665 := bstep (se 2 (by rfl) ⟨1428999, by rfl⟩ : syracuseStep 3810665 = 2857999) B2857999
theorem B2008427 : Blo 1336987 2008427 := bstep (se 1 (by rfl) ⟨1506320, by rfl⟩ : syracuseStep 2008427 = 3012641) B3012641
theorem B3810689 : Blo 1336987 3810689 := bstep (se 2 (by rfl) ⟨1429008, by rfl⟩ : syracuseStep 3810689 = 2858017) B2858017
theorem B8570285 : Blo 1336987 8570285 := bstep (se 3 (by rfl) ⟨1606928, by rfl⟩ : syracuseStep 8570285 = 3213857) B3213857
theorem B6432173 : Blo 1336987 6432173 := bstep (se 3 (by rfl) ⟨1206032, by rfl⟩ : syracuseStep 6432173 = 2412065) B2412065
theorem B2540983 : Blo 1336987 2540983 := bstep (se 1 (by rfl) ⟨1905737, by rfl⟩ : syracuseStep 2540983 = 3811475) B3811475
theorem B10298825 : Blo 1336987 10298825 := bstep (se 2 (by rfl) ⟨3862059, by rfl⟩ : syracuseStep 10298825 = 7724119) B7724119
theorem B21685745 : Blo 1336987 21685745 := bstep (se 2 (by rfl) ⟨8132154, by rfl⟩ : syracuseStep 21685745 = 16264309) B16264309
theorem B9151987 : Blo 1336987 9151987 := bstep (se 1 (by rfl) ⟨6863990, by rfl⟩ : syracuseStep 9151987 = 13727981) B13727981
theorem B2033191 : Blo 1336987 2033191 := bstep (se 1 (by rfl) ⟨1524893, by rfl⟩ : syracuseStep 2033191 = 3049787) B3049787
theorem B3384929 : Blo 1336987 3384929 := bstep (se 2 (by rfl) ⟨1269348, by rfl⟩ : syracuseStep 3384929 = 2538697) B2538697
theorem B4515425 : Blo 1336987 4515425 := bstep (se 2 (by rfl) ⟨1693284, by rfl⟩ : syracuseStep 4515425 = 3386569) B3386569
theorem B6776459 : Blo 1336987 6776459 := bstep (se 1 (by rfl) ⟨5082344, by rfl⟩ : syracuseStep 6776459 = 10164689) B10164689
theorem B17147537 : Blo 1336987 17147537 := bstep (se 2 (by rfl) ⟨6430326, by rfl⟩ : syracuseStep 17147537 = 12860653) B12860653
theorem B1337007 : Blo 1336987 1337007 := bstep (se 1 (by rfl) ⟨1002755, by rfl⟩ : syracuseStep 1337007 = 2005511) B2005511
theorem B5080765 : Blo 1336987 5080765 := bstep (se 3 (by rfl) ⟨952643, by rfl⟩ : syracuseStep 5080765 = 1905287) B1905287
theorem B1337031 : Blo 1336987 1337031 := bstep (se 1 (by rfl) ⟨1002773, by rfl⟩ : syracuseStep 1337031 = 2005547) B2005547
theorem B1337051 : Blo 1336987 1337051 := bstep (se 1 (by rfl) ⟨1002788, by rfl⟩ : syracuseStep 1337051 = 2005577) B2005577
theorem B3008249 : Blo 1336987 3008249 := bstep (se 2 (by rfl) ⟨1128093, by rfl⟩ : syracuseStep 3008249 = 2256187) B2256187
theorem B1337127 : Blo 1336987 1337127 := bstep (se 1 (by rfl) ⟨1002845, by rfl⟩ : syracuseStep 1337127 = 2005691) B2005691
theorem B7620419 : Blo 1336987 7620419 := bstep (se 1 (by rfl) ⟨5715314, by rfl⟩ : syracuseStep 7620419 = 11430629) B11430629
theorem B2541385 : Blo 1336987 2541385 := bstep (se 2 (by rfl) ⟨953019, by rfl⟩ : syracuseStep 2541385 = 1906039) B1906039
theorem B1337167 : Blo 1336987 1337167 := bstep (se 1 (by rfl) ⟨1002875, by rfl⟩ : syracuseStep 1337167 = 2005751) B2005751
theorem B37119833 : Blo 1336987 37119833 := bstep (se 2 (by rfl) ⟨13919937, by rfl⟩ : syracuseStep 37119833 = 27839875) B27839875
theorem B1337183 : Blo 1336987 1337183 := bstep (se 1 (by rfl) ⟨1002887, by rfl⟩ : syracuseStep 1337183 = 2005775) B2005775
theorem B1337211 : Blo 1336987 1337211 := bstep (se 1 (by rfl) ⟨1002908, by rfl⟩ : syracuseStep 1337211 = 2005817) B2005817
theorem B1337263 : Blo 1336987 1337263 := bstep (se 1 (by rfl) ⟨1002947, by rfl⟩ : syracuseStep 1337263 = 2005895) B2005895
theorem B1337287 : Blo 1336987 1337287 := bstep (se 1 (by rfl) ⟨1002965, by rfl⟩ : syracuseStep 1337287 = 2005931) B2005931
theorem B1337307 : Blo 1336987 1337307 := bstep (se 1 (by rfl) ⟨1002980, by rfl⟩ : syracuseStep 1337307 = 2005961) B2005961
theorem B8685571 : Blo 1336987 8685571 := bstep (se 1 (by rfl) ⟨6514178, by rfl⟩ : syracuseStep 8685571 = 13028357) B13028357
theorem B3008519 : Blo 1336987 3008519 := bstep (se 1 (by rfl) ⟨2256389, by rfl⟩ : syracuseStep 3008519 = 4512779) B4512779
theorem B1337383 : Blo 1336987 1337383 := bstep (se 1 (by rfl) ⟨1003037, by rfl⟩ : syracuseStep 1337383 = 2006075) B2006075
theorem B3008591 : Blo 1336987 3008591 := bstep (se 1 (by rfl) ⟨2256443, by rfl⟩ : syracuseStep 3008591 = 4512887) B4512887
theorem B1337423 : Blo 1336987 1337423 := bstep (se 1 (by rfl) ⟨1003067, by rfl⟩ : syracuseStep 1337423 = 2006135) B2006135
theorem B1337439 : Blo 1336987 1337439 := bstep (se 1 (by rfl) ⟨1003079, by rfl⟩ : syracuseStep 1337439 = 2006159) B2006159
theorem B1337467 : Blo 1336987 1337467 := bstep (se 1 (by rfl) ⟨1003100, by rfl⟩ : syracuseStep 1337467 = 2006201) B2006201
theorem B1337519 : Blo 1336987 1337519 := bstep (se 1 (by rfl) ⟨1003139, by rfl⟩ : syracuseStep 1337519 = 2006279) B2006279
theorem B1337543 : Blo 1336987 1337543 := bstep (se 1 (by rfl) ⟨1003157, by rfl⟩ : syracuseStep 1337543 = 2006315) B2006315
theorem B1337563 : Blo 1336987 1337563 := bstep (se 1 (by rfl) ⟨1003172, by rfl⟩ : syracuseStep 1337563 = 2006345) B2006345
theorem B7620875 : Blo 1336987 7620875 := bstep (se 1 (by rfl) ⟨5715656, by rfl⟩ : syracuseStep 7620875 = 11431313) B11431313
theorem B1337639 : Blo 1336987 1337639 := bstep (se 1 (by rfl) ⟨1003229, by rfl⟩ : syracuseStep 1337639 = 2006459) B2006459
theorem B1337679 : Blo 1336987 1337679 := bstep (se 1 (by rfl) ⟨1003259, by rfl⟩ : syracuseStep 1337679 = 2006519) B2006519
theorem B1337695 : Blo 1336987 1337695 := bstep (se 1 (by rfl) ⟨1003271, by rfl⟩ : syracuseStep 1337695 = 2006543) B2006543
theorem B1337723 : Blo 1336987 1337723 := bstep (se 1 (by rfl) ⟨1003292, by rfl⟩ : syracuseStep 1337723 = 2006585) B2006585
theorem B21711239 : Blo 1336987 21711239 := bstep (se 1 (by rfl) ⟨16283429, by rfl⟩ : syracuseStep 21711239 = 32566859) B32566859
theorem B19286423 : Blo 1336987 19286423 := bstep (se 1 (by rfl) ⟨14464817, by rfl⟩ : syracuseStep 19286423 = 28929635) B28929635
theorem B1337775 : Blo 1336987 1337775 := bstep (se 1 (by rfl) ⟨1003331, by rfl⟩ : syracuseStep 1337775 = 2006663) B2006663
theorem B1337799 : Blo 1336987 1337799 := bstep (se 1 (by rfl) ⟨1003349, by rfl⟩ : syracuseStep 1337799 = 2006699) B2006699
theorem B3008987 : Blo 1336987 3008987 := bstep (se 1 (by rfl) ⟨2256740, by rfl⟩ : syracuseStep 3008987 = 4513481) B4513481
theorem B1337819 : Blo 1336987 1337819 := bstep (se 1 (by rfl) ⟨1003364, by rfl⟩ : syracuseStep 1337819 = 2006729) B2006729
theorem B1337895 : Blo 1336987 1337895 := bstep (se 1 (by rfl) ⟨1003421, by rfl⟩ : syracuseStep 1337895 = 2006843) B2006843
theorem B1337935 : Blo 1336987 1337935 := bstep (se 1 (by rfl) ⟨1003451, by rfl⟩ : syracuseStep 1337935 = 2006903) B2006903
theorem B1337951 : Blo 1336987 1337951 := bstep (se 1 (by rfl) ⟨1003463, by rfl⟩ : syracuseStep 1337951 = 2006927) B2006927
theorem B1337979 : Blo 1336987 1337979 := bstep (se 1 (by rfl) ⟨1003484, by rfl⟩ : syracuseStep 1337979 = 2006969) B2006969
theorem B5081723 : Blo 1336987 5081723 := bstep (se 1 (by rfl) ⟨3811292, by rfl⟩ : syracuseStep 5081723 = 7622585) B7622585
theorem B1338031 : Blo 1336987 1338031 := bstep (se 1 (by rfl) ⟨1003523, by rfl⟩ : syracuseStep 1338031 = 2007047) B2007047
theorem B17140409 : Blo 1336987 17140409 := bstep (se 2 (by rfl) ⟨6427653, by rfl⟩ : syracuseStep 17140409 = 12855307) B12855307
theorem B1338055 : Blo 1336987 1338055 := bstep (se 1 (by rfl) ⟨1003541, by rfl⟩ : syracuseStep 1338055 = 2007083) B2007083
theorem B1338075 : Blo 1336987 1338075 := bstep (se 1 (by rfl) ⟨1003556, by rfl⟩ : syracuseStep 1338075 = 2007113) B2007113
theorem B1338151 : Blo 1336987 1338151 := bstep (se 1 (by rfl) ⟨1003613, by rfl⟩ : syracuseStep 1338151 = 2007227) B2007227
theorem B1338191 : Blo 1336987 1338191 := bstep (se 1 (by rfl) ⟨1003643, by rfl⟩ : syracuseStep 1338191 = 2007287) B2007287
theorem B12856157 : Blo 1336987 12856157 := bstep (se 3 (by rfl) ⟨2410529, by rfl⟩ : syracuseStep 12856157 = 4821059) B4821059
theorem B1338207 : Blo 1336987 1338207 := bstep (se 1 (by rfl) ⟨1003655, by rfl⟩ : syracuseStep 1338207 = 2007311) B2007311
theorem B1338235 : Blo 1336987 1338235 := bstep (se 1 (by rfl) ⟨1003676, by rfl⟩ : syracuseStep 1338235 = 2007353) B2007353
theorem B3009455 : Blo 1336987 3009455 := bstep (se 1 (by rfl) ⟨2257091, by rfl⟩ : syracuseStep 3009455 = 4514183) B4514183
theorem B1338287 : Blo 1336987 1338287 := bstep (se 1 (by rfl) ⟨1003715, by rfl⟩ : syracuseStep 1338287 = 2007431) B2007431
theorem B7621559 : Blo 1336987 7621559 := bstep (se 1 (by rfl) ⟨5716169, by rfl⟩ : syracuseStep 7621559 = 11432339) B11432339
theorem B1338311 : Blo 1336987 1338311 := bstep (se 1 (by rfl) ⟨1003733, by rfl⟩ : syracuseStep 1338311 = 2007467) B2007467
theorem B1338331 : Blo 1336987 1338331 := bstep (se 1 (by rfl) ⟨1003748, by rfl⟩ : syracuseStep 1338331 = 2007497) B2007497
theorem B3386387 : Blo 1336987 3386387 := bstep (se 1 (by rfl) ⟨2539790, by rfl⟩ : syracuseStep 3386387 = 5079581) B5079581
theorem B4516883 : Blo 1336987 4516883 := bstep (se 1 (by rfl) ⟨3387662, by rfl⟩ : syracuseStep 4516883 = 6775325) B6775325
theorem B1338407 : Blo 1336987 1338407 := bstep (se 1 (by rfl) ⟨1003805, by rfl⟩ : syracuseStep 1338407 = 2007611) B2007611
theorem B1338447 : Blo 1336987 1338447 := bstep (se 1 (by rfl) ⟨1003835, by rfl⟩ : syracuseStep 1338447 = 2007671) B2007671
theorem B1338463 : Blo 1336987 1338463 := bstep (se 1 (by rfl) ⟨1003847, by rfl⟩ : syracuseStep 1338463 = 2007695) B2007695
theorem B1338491 : Blo 1336987 1338491 := bstep (se 1 (by rfl) ⟨1003868, by rfl⟩ : syracuseStep 1338491 = 2007737) B2007737
theorem B6769817 : Blo 1336987 6769817 := bstep (se 2 (by rfl) ⟨2538681, by rfl⟩ : syracuseStep 6769817 = 5077363) B5077363
theorem B3009707 : Blo 1336987 3009707 := bstep (se 1 (by rfl) ⟨2257280, by rfl⟩ : syracuseStep 3009707 = 4514561) B4514561
theorem B1338543 : Blo 1336987 1338543 := bstep (se 1 (by rfl) ⟨1003907, by rfl⟩ : syracuseStep 1338543 = 2007815) B2007815
theorem B12201155 : Blo 1336987 12201155 := bstep (se 1 (by rfl) ⟨9150866, by rfl⟩ : syracuseStep 12201155 = 18301733) B18301733
theorem B1338567 : Blo 1336987 1338567 := bstep (se 1 (by rfl) ⟨1003925, by rfl⟩ : syracuseStep 1338567 = 2007851) B2007851
theorem B1338587 : Blo 1336987 1338587 := bstep (se 1 (by rfl) ⟨1003940, by rfl⟩ : syracuseStep 1338587 = 2007881) B2007881
theorem B1338663 : Blo 1336987 1338663 := bstep (se 1 (by rfl) ⟨1003997, by rfl⟩ : syracuseStep 1338663 = 2007995) B2007995
theorem B1338703 : Blo 1336987 1338703 := bstep (se 1 (by rfl) ⟨1004027, by rfl⟩ : syracuseStep 1338703 = 2008055) B2008055
theorem B4517207 : Blo 1336987 4517207 := bstep (se 1 (by rfl) ⟨3387905, by rfl⟩ : syracuseStep 4517207 = 6775811) B6775811
theorem B10849625 : Blo 1336987 10849625 := bstep (se 2 (by rfl) ⟨4068609, by rfl⟩ : syracuseStep 10849625 = 8137219) B8137219
theorem B1338719 : Blo 1336987 1338719 := bstep (se 1 (by rfl) ⟨1004039, by rfl⟩ : syracuseStep 1338719 = 2008079) B2008079
theorem B1338747 : Blo 1336987 1338747 := bstep (se 1 (by rfl) ⟨1004060, by rfl⟩ : syracuseStep 1338747 = 2008121) B2008121
theorem B5082497 : Blo 1336987 5082497 := bstep (se 2 (by rfl) ⟨1905936, by rfl⟩ : syracuseStep 5082497 = 3811873) B3811873
theorem B20589997 : Blo 1336987 20589997 := bstep (se 3 (by rfl) ⟨3860624, by rfl⟩ : syracuseStep 20589997 = 7721249) B7721249
theorem B1338799 : Blo 1336987 1338799 := bstep (se 1 (by rfl) ⟨1004099, by rfl⟩ : syracuseStep 1338799 = 2008199) B2008199
theorem B1338823 : Blo 1336987 1338823 := bstep (se 1 (by rfl) ⟨1004117, by rfl⟩ : syracuseStep 1338823 = 2008235) B2008235
theorem B3386843 : Blo 1336987 3386843 := bstep (se 1 (by rfl) ⟨2540132, by rfl⟩ : syracuseStep 3386843 = 5080265) B5080265
theorem B1338843 : Blo 1336987 1338843 := bstep (se 1 (by rfl) ⟨1004132, by rfl⟩ : syracuseStep 1338843 = 2008265) B2008265
theorem B10153511 : Blo 1336987 10153511 := bstep (se 1 (by rfl) ⟨7615133, by rfl⟩ : syracuseStep 10153511 = 15230267) B15230267
theorem B1338919 : Blo 1336987 1338919 := bstep (se 1 (by rfl) ⟨1004189, by rfl⟩ : syracuseStep 1338919 = 2008379) B2008379
theorem B1338959 : Blo 1336987 1338959 := bstep (se 1 (by rfl) ⟨1004219, by rfl⟩ : syracuseStep 1338959 = 2008439) B2008439
theorem B1338975 : Blo 1336987 1338975 := bstep (se 1 (by rfl) ⟨1004231, by rfl⟩ : syracuseStep 1338975 = 2008463) B2008463
theorem B1904251 : Blo 1336987 1904251 := bstep (se 1 (by rfl) ⟨1428188, by rfl⟩ : syracuseStep 1904251 = 2856377) B2856377
theorem B4820627 : Blo 1336987 4820627 := bstep (se 1 (by rfl) ⟨3615470, by rfl⟩ : syracuseStep 4820627 = 7230941) B7230941
theorem B7622333 : Blo 1336987 7622333 := bstep (se 3 (by rfl) ⟨1429187, by rfl⟩ : syracuseStep 7622333 = 2858375) B2858375
theorem B3010247 : Blo 1336987 3010247 := bstep (se 1 (by rfl) ⟨2257685, by rfl⟩ : syracuseStep 3010247 = 4515371) B4515371
theorem B2256815 : Blo 1336987 2256815 := bstep (se 1 (by rfl) ⟨1692611, by rfl⟩ : syracuseStep 2256815 = 3385223) B3385223
theorem B39088133 : Blo 1336987 39088133 := bstep (se 4 (by rfl) ⟨3664512, by rfl⟩ : syracuseStep 39088133 = 7329025) B7329025
theorem B2035721 : Blo 1336987 2035721 := bstep (se 2 (by rfl) ⟨763395, by rfl⟩ : syracuseStep 2035721 = 1526791) B1526791
theorem B5501245 : Blo 1336987 5501245 := bstep (se 3 (by rfl) ⟨1031483, by rfl⟩ : syracuseStep 5501245 = 2062967) B2062967
theorem B2257247 : Blo 1336987 2257247 := bstep (se 1 (by rfl) ⟨1692935, by rfl⟩ : syracuseStep 2257247 = 3385871) B3385871
theorem B7623017 : Blo 1336987 7623017 := bstep (se 2 (by rfl) ⟨2858631, by rfl⟩ : syracuseStep 7623017 = 5717263) B5717263
theorem B4518287 : Blo 1336987 4518287 := bstep (se 1 (by rfl) ⟨3388715, by rfl⟩ : syracuseStep 4518287 = 6777431) B6777431
theorem B1716655 : Blo 1336987 1716655 := bstep (se 1 (by rfl) ⟨1287491, by rfl⟩ : syracuseStep 1716655 = 2574983) B2574983
theorem B2478511 : Blo 1336987 2478511 := bstep (se 1 (by rfl) ⟨1858883, by rfl⟩ : syracuseStep 2478511 = 3717767) B3717767
theorem B3863027 : Blo 1336987 3863027 := bstep (se 1 (by rfl) ⟨2897270, by rfl⟩ : syracuseStep 3863027 = 5794541) B5794541
theorem B5083681 : Blo 1336987 5083681 := bstep (se 2 (by rfl) ⟨1906380, by rfl⟩ : syracuseStep 5083681 = 3812761) B3812761
theorem B3011111 : Blo 1336987 3011111 := bstep (se 1 (by rfl) ⟨2258333, by rfl⟩ : syracuseStep 3011111 = 4516667) B4516667
theorem B3388027 : Blo 1336987 3388027 := bstep (se 1 (by rfl) ⟨2541020, by rfl⟩ : syracuseStep 3388027 = 5082041) B5082041
theorem B7230161 : Blo 1336987 7230161 := bstep (se 2 (by rfl) ⟨2711310, by rfl⟩ : syracuseStep 7230161 = 5422621) B5422621
theorem B4518611 : Blo 1336987 4518611 := bstep (se 1 (by rfl) ⟨3388958, by rfl⟩ : syracuseStep 4518611 = 6777917) B6777917
theorem B1905401 : Blo 1336987 1905401 := bstep (se 2 (by rfl) ⟨714525, by rfl⟩ : syracuseStep 1905401 = 1429051) B1429051
theorem B3011435 : Blo 1336987 3011435 := bstep (se 1 (by rfl) ⟨2258576, by rfl⟩ : syracuseStep 3011435 = 4517153) B4517153
theorem B2257807 : Blo 1336987 2257807 := bstep (se 1 (by rfl) ⟨1693355, by rfl⟩ : syracuseStep 2257807 = 3386711) B3386711
theorem B3011489 : Blo 1336987 3011489 := bstep (se 2 (by rfl) ⟨1129308, by rfl⟩ : syracuseStep 3011489 = 2258617) B2258617
theorem B1504219 : Blo 1336987 1504219 := bstep (se 1 (by rfl) ⟨1128164, by rfl⟩ : syracuseStep 1504219 = 2256329) B2256329
theorem B3011831 : Blo 1336987 3011831 := bstep (se 1 (by rfl) ⟨2258873, by rfl⟩ : syracuseStep 3011831 = 4517747) B4517747
theorem B13726991 : Blo 1336987 13726991 := bstep (se 1 (by rfl) ⟨10295243, by rfl⟩ : syracuseStep 13726991 = 20590487) B20590487
theorem B1504687 : Blo 1336987 1504687 := bstep (se 1 (by rfl) ⟨1128515, by rfl⟩ : syracuseStep 1504687 = 2257031) B2257031
theorem B2258489 : Blo 1336987 2258489 := bstep (se 2 (by rfl) ⟨846933, by rfl⟩ : syracuseStep 2258489 = 1693867) B1693867
theorem B8566411 : Blo 1336987 8566411 := bstep (se 1 (by rfl) ⟨6424808, by rfl⟩ : syracuseStep 8566411 = 12849617) B12849617
theorem B3618443 : Blo 1336987 3618443 := bstep (se 1 (by rfl) ⟨2713832, by rfl⟩ : syracuseStep 3618443 = 5427665) B5427665
theorem B10851985 : Blo 1336987 10851985 := bstep (se 2 (by rfl) ⟨4069494, by rfl⟩ : syracuseStep 10851985 = 8138989) B8138989
theorem B5076665 : Blo 1336987 5076665 := bstep (se 2 (by rfl) ⟨1903749, by rfl⟩ : syracuseStep 5076665 = 3807499) B3807499
theorem B5076695 : Blo 1336987 5076695 := bstep (se 1 (by rfl) ⟨3807521, by rfl⟩ : syracuseStep 5076695 = 7615043) B7615043
theorem B6428483 : Blo 1336987 6428483 := bstep (se 1 (by rfl) ⟨4821362, by rfl⟩ : syracuseStep 6428483 = 9642725) B9642725
theorem B3012425 : Blo 1336987 3012425 := bstep (se 2 (by rfl) ⟨1129659, by rfl⟩ : syracuseStep 3012425 = 2259319) B2259319
theorem B1505119 : Blo 1336987 1505119 := bstep (se 1 (by rfl) ⟨1128839, by rfl⟩ : syracuseStep 1505119 = 2257679) B2257679
theorem B8812397 : Blo 1336987 8812397 := bstep (se 3 (by rfl) ⟨1652324, by rfl⟩ : syracuseStep 8812397 = 3304649) B3304649
theorem B8566721 : Blo 1336987 8566721 := bstep (se 2 (by rfl) ⟨3212520, by rfl⟩ : syracuseStep 8566721 = 6425041) B6425041
theorem B7624793 : Blo 1336987 7624793 := bstep (se 2 (by rfl) ⟨2859297, by rfl⟩ : syracuseStep 7624793 = 5718595) B5718595
theorem B1505479 : Blo 1336987 1505479 := bstep (se 1 (by rfl) ⟨1129109, by rfl⟩ : syracuseStep 1505479 = 2258219) B2258219
theorem B2259191 : Blo 1336987 2259191 := bstep (se 1 (by rfl) ⟨1694393, by rfl⟩ : syracuseStep 2259191 = 3388787) B3388787
theorem B1694135 : Blo 1336987 1694135 := bstep (se 1 (by rfl) ⟨1270601, by rfl⟩ : syracuseStep 1694135 = 2541203) B2541203
theorem B6519329 : Blo 1336987 6519329 := bstep (se 2 (by rfl) ⟨2444748, by rfl⟩ : syracuseStep 6519329 = 4889497) B4889497
theorem B7625249 : Blo 1336987 7625249 := bstep (se 2 (by rfl) ⟨2859468, by rfl⟩ : syracuseStep 7625249 = 5718937) B5718937
theorem B2005583 : Blo 1336987 2005583 := bstep (se 1 (by rfl) ⟨1504187, by rfl⟩ : syracuseStep 2005583 = 3008375) B3008375
theorem B1694287 : Blo 1336987 1694287 := bstep (se 1 (by rfl) ⟨1270715, by rfl⟩ : syracuseStep 1694287 = 2541431) B2541431
theorem B2259535 : Blo 1336987 2259535 := bstep (se 1 (by rfl) ⟨1694651, by rfl⟩ : syracuseStep 2259535 = 3389303) B3389303
theorem B4512455 : Blo 1336987 4512455 := bstep (se 1 (by rfl) ⟨3384341, by rfl⟩ : syracuseStep 4512455 = 6768683) B6768683
theorem B2005703 : Blo 1336987 2005703 := bstep (se 1 (by rfl) ⟨1504277, by rfl⟩ : syracuseStep 2005703 = 3008555) B3008555
theorem B9779921 : Blo 1336987 9779921 := bstep (se 2 (by rfl) ⟨3667470, by rfl⟩ : syracuseStep 9779921 = 7334941) B7334941
theorem B5421779 : Blo 1336987 5421779 := bstep (se 1 (by rfl) ⟨4066334, by rfl⟩ : syracuseStep 5421779 = 8132669) B8132669
theorem B7625501 : Blo 1336987 7625501 := bstep (se 3 (by rfl) ⟨1429781, by rfl⟩ : syracuseStep 7625501 = 2859563) B2859563
theorem B2005865 : Blo 1336987 2005865 := bstep (se 2 (by rfl) ⟨752199, by rfl⟩ : syracuseStep 2005865 = 1504399) B1504399
theorem B55671731 : Blo 1336987 55671731 := bstep (se 1 (by rfl) ⟨41753798, by rfl⟩ : syracuseStep 55671731 = 83507597) B83507597
theorem B2005943 : Blo 1336987 2005943 := bstep (se 1 (by rfl) ⟨1504457, by rfl⟩ : syracuseStep 2005943 = 3008915) B3008915
theorem B10165175 : Blo 1336987 10165175 := bstep (se 1 (by rfl) ⟨7623881, by rfl⟩ : syracuseStep 10165175 = 15247763) B15247763
theorem B2005979 : Blo 1336987 2005979 := bstep (se 1 (by rfl) ⟨1504484, by rfl⟩ : syracuseStep 2005979 = 3008969) B3008969
theorem B2538515 : Blo 1336987 2538515 := bstep (se 1 (by rfl) ⟨1903886, by rfl⟩ : syracuseStep 2538515 = 3807773) B3807773
theorem B1506343 : Blo 1336987 1506343 := bstep (se 1 (by rfl) ⟨1129757, by rfl⟩ : syracuseStep 1506343 = 2259515) B2259515
theorem B2538553 : Blo 1336987 2538553 := bstep (se 2 (by rfl) ⟨951957, by rfl⟩ : syracuseStep 2538553 = 1903915) B1903915
theorem B28941391 : Blo 1336987 28941391 := bstep (se 1 (by rfl) ⟨21706043, by rfl⟩ : syracuseStep 28941391 = 43412087) B43412087
theorem B23174423 : Blo 1336987 23174423 := bstep (se 1 (by rfl) ⟨17380817, by rfl⟩ : syracuseStep 23174423 = 34761635) B34761635
theorem B21708121 : Blo 1336987 21708121 := bstep (se 2 (by rfl) ⟨8140545, by rfl⟩ : syracuseStep 21708121 = 16281091) B16281091
theorem B2538857 : Blo 1336987 2538857 := bstep (se 2 (by rfl) ⟨952071, by rfl⟩ : syracuseStep 2538857 = 1904143) B1904143
theorem B2006447 : Blo 1336987 2006447 := bstep (se 1 (by rfl) ⟨1504835, by rfl⟩ : syracuseStep 2006447 = 3009671) B3009671
theorem B19553717 : Blo 1336987 19553717 := bstep (se 5 (by rfl) ⟨916580, by rfl⟩ : syracuseStep 19553717 = 1833161) B1833161
theorem B2006537 : Blo 1336987 2006537 := bstep (se 2 (by rfl) ⟨752451, by rfl⟩ : syracuseStep 2006537 = 1504903) B1504903
theorem B4513319 : Blo 1336987 4513319 := bstep (se 1 (by rfl) ⟨3384989, by rfl⟩ : syracuseStep 4513319 = 6769979) B6769979
theorem B2006567 : Blo 1336987 2006567 := bstep (se 1 (by rfl) ⟨1504925, by rfl⟩ : syracuseStep 2006567 = 3009851) B3009851
theorem B2006651 : Blo 1336987 2006651 := bstep (se 1 (by rfl) ⟨1504988, by rfl⟩ : syracuseStep 2006651 = 3009977) B3009977
theorem B4513427 : Blo 1336987 4513427 := bstep (se 1 (by rfl) ⟨3385070, by rfl⟩ : syracuseStep 4513427 = 6770141) B6770141
theorem B3808957 : Blo 1336987 3808957 := bstep (se 3 (by rfl) ⟨714179, by rfl⟩ : syracuseStep 3808957 = 1428359) B1428359
theorem B17145533 : Blo 1336987 17145533 := bstep (se 3 (by rfl) ⟨3214787, by rfl⟩ : syracuseStep 17145533 = 6429575) B6429575
theorem B2006777 : Blo 1336987 2006777 := bstep (se 2 (by rfl) ⟨752541, by rfl⟩ : syracuseStep 2006777 = 1505083) B1505083
theorem B2006879 : Blo 1336987 2006879 := bstep (se 1 (by rfl) ⟨1505159, by rfl⟩ : syracuseStep 2006879 = 3010319) B3010319
theorem B4513643 : Blo 1336987 4513643 := bstep (se 1 (by rfl) ⟨3385232, by rfl⟩ : syracuseStep 4513643 = 6770465) B6770465
theorem B2006891 : Blo 1336987 2006891 := bstep (se 1 (by rfl) ⟨1505168, by rfl⟩ : syracuseStep 2006891 = 3010337) B3010337
theorem B4513697 : Blo 1336987 4513697 := bstep (se 2 (by rfl) ⟨1692636, by rfl⟩ : syracuseStep 4513697 = 3385273) B3385273
theorem B3809207 : Blo 1336987 3809207 := bstep (se 1 (by rfl) ⟨2856905, by rfl⟩ : syracuseStep 3809207 = 5713811) B5713811
theorem B10993601 : Blo 1336987 10993601 := bstep (se 2 (by rfl) ⟨4122600, by rfl⟩ : syracuseStep 10993601 = 8245201) B8245201
theorem B26058755 : Blo 1336987 26058755 := bstep (se 1 (by rfl) ⟨19544066, by rfl⟩ : syracuseStep 26058755 = 39088133) B39088133
theorem B2007305 : Blo 1336987 2007305 := bstep (se 2 (by rfl) ⟨752739, by rfl⟩ : syracuseStep 2007305 = 1505479) B1505479
theorem B2007407 : Blo 1336987 2007407 := bstep (se 1 (by rfl) ⟨1505555, by rfl⟩ : syracuseStep 2007407 = 3011111) B3011111
theorem B7619143 : Blo 1336987 7619143 := bstep (se 1 (by rfl) ⟨5714357, by rfl⟩ : syracuseStep 7619143 = 11428715) B11428715
theorem B2007623 : Blo 1336987 2007623 := bstep (se 1 (by rfl) ⟨1505717, by rfl⟩ : syracuseStep 2007623 = 3011435) B3011435
theorem B2007659 : Blo 1336987 2007659 := bstep (se 1 (by rfl) ⟨1505744, by rfl⟩ : syracuseStep 2007659 = 3011489) B3011489
theorem B2007887 : Blo 1336987 2007887 := bstep (se 1 (by rfl) ⟨1505915, by rfl⟩ : syracuseStep 2007887 = 3011831) B3011831
theorem B9151327 : Blo 1336987 9151327 := bstep (se 1 (by rfl) ⟨6863495, by rfl⟩ : syracuseStep 9151327 = 13726991) B13726991
theorem B2540459 : Blo 1336987 2540459 := bstep (se 1 (by rfl) ⟨1905344, by rfl⟩ : syracuseStep 2540459 = 3810689) B3810689
theorem B6865883 : Blo 1336987 6865883 := bstep (se 1 (by rfl) ⟨5149412, by rfl⟩ : syracuseStep 6865883 = 10298825) B10298825
theorem B3384443 : Blo 1336987 3384443 := bstep (se 1 (by rfl) ⟨2538332, by rfl⟩ : syracuseStep 3384443 = 5076665) B5076665
theorem B3384463 : Blo 1336987 3384463 := bstep (se 1 (by rfl) ⟨2538347, by rfl⟩ : syracuseStep 3384463 = 5076695) B5076695
theorem B4285655 : Blo 1336987 4285655 := bstep (se 1 (by rfl) ⟨3214241, by rfl⟩ : syracuseStep 4285655 = 6428483) B6428483
theorem B5080279 : Blo 1336987 5080279 := bstep (se 1 (by rfl) ⟨3810209, by rfl⟩ : syracuseStep 5080279 = 7620419) B7620419
theorem B2008283 : Blo 1336987 2008283 := bstep (se 1 (by rfl) ⟨1506212, by rfl⟩ : syracuseStep 2008283 = 3012425) B3012425
theorem B5874931 : Blo 1336987 5874931 := bstep (se 1 (by rfl) ⟨4406198, by rfl⟩ : syracuseStep 5874931 = 8812397) B8812397
theorem B5711147 : Blo 1336987 5711147 := bstep (se 1 (by rfl) ⟨4283360, by rfl⟩ : syracuseStep 5711147 = 8566721) B8566721
theorem B57828653 : Blo 1336987 57828653 := bstep (se 3 (by rfl) ⟨10842872, by rfl⟩ : syracuseStep 57828653 = 21685745) B21685745
theorem B2008457 : Blo 1336987 2008457 := bstep (se 2 (by rfl) ⟨753171, by rfl⟩ : syracuseStep 2008457 = 1506343) B1506343
theorem B10847641 : Blo 1336987 10847641 := bstep (se 2 (by rfl) ⟨4067865, by rfl⟩ : syracuseStep 10847641 = 8135731) B8135731
theorem B3384737 : Blo 1336987 3384737 := bstep (se 2 (by rfl) ⟨1269276, by rfl⟩ : syracuseStep 3384737 = 2538553) B2538553
theorem B5080583 : Blo 1336987 5080583 := bstep (se 1 (by rfl) ⟨3810437, by rfl⟩ : syracuseStep 5080583 = 7620875) B7620875
theorem B1337055 : Blo 1336987 1337055 := bstep (se 1 (by rfl) ⟨1002791, by rfl⟩ : syracuseStep 1337055 = 2005583) B2005583
theorem B28944161 : Blo 1336987 28944161 := bstep (se 2 (by rfl) ⟨10854060, by rfl⟩ : syracuseStep 28944161 = 21708121) B21708121
theorem B3008303 : Blo 1336987 3008303 := bstep (se 1 (by rfl) ⟨2256227, by rfl⟩ : syracuseStep 3008303 = 4512455) B4512455
theorem B1337135 : Blo 1336987 1337135 := bstep (se 1 (by rfl) ⟨1002851, by rfl⟩ : syracuseStep 1337135 = 2005703) B2005703
theorem B3614519 : Blo 1336987 3614519 := bstep (se 1 (by rfl) ⟨2710889, by rfl⟩ : syracuseStep 3614519 = 5421779) B5421779
theorem B27453329 : Blo 1336987 27453329 := bstep (se 2 (by rfl) ⟨10294998, by rfl⟩ : syracuseStep 27453329 = 20589997) B20589997
theorem B8570771 : Blo 1336987 8570771 := bstep (se 1 (by rfl) ⟨6428078, by rfl⟩ : syracuseStep 8570771 = 12856157) B12856157
theorem B1337243 : Blo 1336987 1337243 := bstep (se 1 (by rfl) ⟨1002932, by rfl⟩ : syracuseStep 1337243 = 2005865) B2005865
theorem B1337295 : Blo 1336987 1337295 := bstep (se 1 (by rfl) ⟨1002971, by rfl⟩ : syracuseStep 1337295 = 2005943) B2005943
theorem B5081039 : Blo 1336987 5081039 := bstep (se 1 (by rfl) ⟨3810779, by rfl⟩ : syracuseStep 5081039 = 7621559) B7621559
theorem B6776783 : Blo 1336987 6776783 := bstep (se 1 (by rfl) ⟨5082587, by rfl⟩ : syracuseStep 6776783 = 10165175) B10165175
theorem B1337319 : Blo 1336987 1337319 := bstep (se 1 (by rfl) ⟨1002989, by rfl⟩ : syracuseStep 1337319 = 2005979) B2005979
theorem B5081069 : Blo 1336987 5081069 := bstep (se 3 (by rfl) ⟨952700, by rfl⟩ : syracuseStep 5081069 = 1905401) B1905401
theorem B11421881 : Blo 1336987 11421881 := bstep (se 2 (by rfl) ⟨4283205, by rfl⟩ : syracuseStep 11421881 = 8566411) B8566411
theorem B14469313 : Blo 1336987 14469313 := bstep (se 2 (by rfl) ⟨5425992, by rfl⟩ : syracuseStep 14469313 = 10851985) B10851985
theorem B1337631 : Blo 1336987 1337631 := bstep (se 1 (by rfl) ⟨1003223, by rfl⟩ : syracuseStep 1337631 = 2006447) B2006447
theorem B13035811 : Blo 1336987 13035811 := bstep (se 1 (by rfl) ⟨9776858, by rfl⟩ : syracuseStep 13035811 = 19553717) B19553717
theorem B1337691 : Blo 1336987 1337691 := bstep (se 1 (by rfl) ⟨1003268, by rfl⟩ : syracuseStep 1337691 = 2006537) B2006537
theorem B6769007 : Blo 1336987 6769007 := bstep (se 1 (by rfl) ⟨5076755, by rfl⟩ : syracuseStep 6769007 = 10153511) B10153511
theorem B3008879 : Blo 1336987 3008879 := bstep (se 1 (by rfl) ⟨2256659, by rfl⟩ : syracuseStep 3008879 = 4513319) B4513319
theorem B1337711 : Blo 1336987 1337711 := bstep (se 1 (by rfl) ⟨1003283, by rfl⟩ : syracuseStep 1337711 = 2006567) B2006567
theorem B1337767 : Blo 1336987 1337767 := bstep (se 1 (by rfl) ⟨1003325, by rfl⟩ : syracuseStep 1337767 = 2006651) B2006651
theorem B3008951 : Blo 1336987 3008951 := bstep (se 1 (by rfl) ⟨2256713, by rfl⟩ : syracuseStep 3008951 = 4513427) B4513427
theorem B3213751 : Blo 1336987 3213751 := bstep (se 1 (by rfl) ⟨2410313, by rfl⟩ : syracuseStep 3213751 = 4820627) B4820627
theorem B11430355 : Blo 1336987 11430355 := bstep (se 1 (by rfl) ⟨8572766, by rfl⟩ : syracuseStep 11430355 = 17145533) B17145533
theorem B5081555 : Blo 1336987 5081555 := bstep (se 1 (by rfl) ⟨3811166, by rfl⟩ : syracuseStep 5081555 = 7622333) B7622333
theorem B1337851 : Blo 1336987 1337851 := bstep (se 1 (by rfl) ⟨1003388, by rfl⟩ : syracuseStep 1337851 = 2006777) B2006777
theorem B1337919 : Blo 1336987 1337919 := bstep (se 1 (by rfl) ⟨1003439, by rfl⟩ : syracuseStep 1337919 = 2006879) B2006879
theorem B3009095 : Blo 1336987 3009095 := bstep (se 1 (by rfl) ⟨2256821, by rfl⟩ : syracuseStep 3009095 = 4513643) B4513643
theorem B1337927 : Blo 1336987 1337927 := bstep (se 1 (by rfl) ⟨1003445, by rfl⟩ : syracuseStep 1337927 = 2006891) B2006891
theorem B3009131 : Blo 1336987 3009131 := bstep (se 1 (by rfl) ⟨2256848, by rfl⟩ : syracuseStep 3009131 = 4513697) B4513697
theorem B1338079 : Blo 1336987 1338079 := bstep (se 1 (by rfl) ⟨1003559, by rfl⟩ : syracuseStep 1338079 = 2007119) B2007119
theorem B1338159 : Blo 1336987 1338159 := bstep (se 1 (by rfl) ⟨1003619, by rfl⟩ : syracuseStep 1338159 = 2007239) B2007239
theorem B9153415 : Blo 1336987 9153415 := bstep (se 1 (by rfl) ⟨6865061, by rfl⟩ : syracuseStep 9153415 = 13730123) B13730123
theorem B1338267 : Blo 1336987 1338267 := bstep (se 1 (by rfl) ⟨1003700, by rfl⟩ : syracuseStep 1338267 = 2007401) B2007401
theorem B5082011 : Blo 1336987 5082011 := bstep (se 1 (by rfl) ⟨3811508, by rfl⟩ : syracuseStep 5082011 = 7623017) B7623017
theorem B6777755 : Blo 1336987 6777755 := bstep (se 1 (by rfl) ⟨5083316, by rfl⟩ : syracuseStep 6777755 = 10166633) B10166633
theorem B1338319 : Blo 1336987 1338319 := bstep (se 1 (by rfl) ⟨1003739, by rfl⟩ : syracuseStep 1338319 = 2007479) B2007479
theorem B1338343 : Blo 1336987 1338343 := bstep (se 1 (by rfl) ⟨1003757, by rfl⟩ : syracuseStep 1338343 = 2007515) B2007515
theorem B3009527 : Blo 1336987 3009527 := bstep (se 1 (by rfl) ⟨2257145, by rfl⟩ : syracuseStep 3009527 = 4514291) B4514291
theorem B2575351 : Blo 1336987 2575351 := bstep (se 1 (by rfl) ⟨1931513, by rfl⟩ : syracuseStep 2575351 = 3863027) B3863027
theorem B3386407 : Blo 1336987 3386407 := bstep (se 1 (by rfl) ⟨2539805, by rfl⟩ : syracuseStep 3386407 = 5079611) B5079611
theorem B7334993 : Blo 1336987 7334993 := bstep (se 2 (by rfl) ⟨2750622, by rfl⟩ : syracuseStep 7334993 = 5501245) B5501245
theorem B4820107 : Blo 1336987 4820107 := bstep (se 1 (by rfl) ⟨3615080, by rfl⟩ : syracuseStep 4820107 = 7230161) B7230161
theorem B2288873 : Blo 1336987 2288873 := bstep (se 2 (by rfl) ⟨858327, by rfl⟩ : syracuseStep 2288873 = 1716655) B1716655
theorem B3304681 : Blo 1336987 3304681 := bstep (se 2 (by rfl) ⟨1239255, by rfl⟩ : syracuseStep 3304681 = 2478511) B2478511
theorem B5713163 : Blo 1336987 5713163 := bstep (se 1 (by rfl) ⟨4284872, by rfl⟩ : syracuseStep 5713163 = 8569745) B8569745
theorem B1338655 : Blo 1336987 1338655 := bstep (se 1 (by rfl) ⟨1003991, by rfl⟩ : syracuseStep 1338655 = 2007983) B2007983
theorem B2256167 : Blo 1336987 2256167 := bstep (se 1 (by rfl) ⟨1692125, by rfl⟩ : syracuseStep 2256167 = 3384251) B3384251
theorem B1338715 : Blo 1336987 1338715 := bstep (se 1 (by rfl) ⟨1004036, by rfl⟩ : syracuseStep 1338715 = 2008073) B2008073
theorem B3009887 : Blo 1336987 3009887 := bstep (se 1 (by rfl) ⟨2257415, by rfl⟩ : syracuseStep 3009887 = 4514831) B4514831
theorem B1338735 : Blo 1336987 1338735 := bstep (se 1 (by rfl) ⟨1004051, by rfl⟩ : syracuseStep 1338735 = 2008103) B2008103
theorem B6778241 : Blo 1336987 6778241 := bstep (se 2 (by rfl) ⟨2541840, by rfl⟩ : syracuseStep 6778241 = 5083681) B5083681
theorem B1338791 : Blo 1336987 1338791 := bstep (se 1 (by rfl) ⟨1004093, by rfl⟩ : syracuseStep 1338791 = 2008187) B2008187
theorem B3812807 : Blo 1336987 3812807 := bstep (se 1 (by rfl) ⟨2859605, by rfl⟩ : syracuseStep 3812807 = 5719211) B5719211
theorem B3386873 : Blo 1336987 3386873 := bstep (se 2 (by rfl) ⟨1270077, by rfl⟩ : syracuseStep 3386873 = 2540155) B2540155
theorem B4517369 : Blo 1336987 4517369 := bstep (se 2 (by rfl) ⟨1694013, by rfl⟩ : syracuseStep 4517369 = 3388027) B3388027
theorem B1338875 : Blo 1336987 1338875 := bstep (se 1 (by rfl) ⟨1004156, by rfl⟩ : syracuseStep 1338875 = 2008313) B2008313
theorem B1338943 : Blo 1336987 1338943 := bstep (se 1 (by rfl) ⟨1004207, by rfl⟩ : syracuseStep 1338943 = 2008415) B2008415
theorem B1338951 : Blo 1336987 1338951 := bstep (se 1 (by rfl) ⟨1004213, by rfl⟩ : syracuseStep 1338951 = 2008427) B2008427
theorem B10161773 : Blo 1336987 10161773 := bstep (se 3 (by rfl) ⟨1905332, by rfl⟩ : syracuseStep 10161773 = 3810665) B3810665
theorem B5713523 : Blo 1336987 5713523 := bstep (se 1 (by rfl) ⟨4285142, by rfl⟩ : syracuseStep 5713523 = 8570285) B8570285
theorem B4288115 : Blo 1336987 4288115 := bstep (se 1 (by rfl) ⟨3216086, by rfl⟩ : syracuseStep 4288115 = 6432173) B6432173
theorem B2256619 : Blo 1336987 2256619 := bstep (se 1 (by rfl) ⟨1692464, by rfl⟩ : syracuseStep 2256619 = 3384929) B3384929
theorem B3010283 : Blo 1336987 3010283 := bstep (se 1 (by rfl) ⟨2257712, by rfl⟩ : syracuseStep 3010283 = 4515425) B4515425
theorem B4517639 : Blo 1336987 4517639 := bstep (se 1 (by rfl) ⟨3388229, by rfl⟩ : syracuseStep 4517639 = 6776459) B6776459
theorem B11431691 : Blo 1336987 11431691 := bstep (se 1 (by rfl) ⟨8573768, by rfl⟩ : syracuseStep 11431691 = 17147537) B17147537
theorem B4517693 : Blo 1336987 4517693 := bstep (se 3 (by rfl) ⟨847067, by rfl⟩ : syracuseStep 4517693 = 1694135) B1694135
theorem B3010409 : Blo 1336987 3010409 := bstep (se 2 (by rfl) ⟨1128903, by rfl⟩ : syracuseStep 3010409 = 2257807) B2257807
theorem B5083195 : Blo 1336987 5083195 := bstep (se 1 (by rfl) ⟨3812396, by rfl⟩ : syracuseStep 5083195 = 7624793) B7624793
theorem B38588521 : Blo 1336987 38588521 := bstep (se 2 (by rfl) ⟨14470695, by rfl⟩ : syracuseStep 38588521 = 28941391) B28941391
theorem B3387521 : Blo 1336987 3387521 := bstep (se 2 (by rfl) ⟨1270320, by rfl⟩ : syracuseStep 3387521 = 2540641) B2540641
theorem B12857615 : Blo 1336987 12857615 := bstep (se 1 (by rfl) ⟨9643211, by rfl⟩ : syracuseStep 12857615 = 19286423) B19286423
theorem B4346219 : Blo 1336987 4346219 := bstep (se 1 (by rfl) ⟨3259664, by rfl⟩ : syracuseStep 4346219 = 6519329) B6519329
theorem B5083499 : Blo 1336987 5083499 := bstep (se 1 (by rfl) ⟨3812624, by rfl⟩ : syracuseStep 5083499 = 7625249) B7625249
theorem B3387815 : Blo 1336987 3387815 := bstep (se 1 (by rfl) ⟨2540861, by rfl⟩ : syracuseStep 3387815 = 5081723) B5081723
theorem B5083667 : Blo 1336987 5083667 := bstep (se 1 (by rfl) ⟨3812750, by rfl⟩ : syracuseStep 5083667 = 7625501) B7625501
theorem B3387977 : Blo 1336987 3387977 := bstep (se 2 (by rfl) ⟨1270491, by rfl⟩ : syracuseStep 3387977 = 2540983) B2540983
theorem B37114487 : Blo 1336987 37114487 := bstep (se 1 (by rfl) ⟨27835865, by rfl⟩ : syracuseStep 37114487 = 55671731) B55671731
theorem B12202649 : Blo 1336987 12202649 := bstep (se 2 (by rfl) ⟨4575993, by rfl⟩ : syracuseStep 12202649 = 9151987) B9151987
theorem B1692343 : Blo 1336987 1692343 := bstep (se 1 (by rfl) ⟨1269257, by rfl⟩ : syracuseStep 1692343 = 2538515) B2538515
theorem B2257591 : Blo 1336987 2257591 := bstep (se 1 (by rfl) ⟨1693193, by rfl⟩ : syracuseStep 2257591 = 3386387) B3386387
theorem B3011255 : Blo 1336987 3011255 := bstep (se 1 (by rfl) ⟨2258441, by rfl⟩ : syracuseStep 3011255 = 4516883) B4516883
theorem B3011471 : Blo 1336987 3011471 := bstep (se 1 (by rfl) ⟨2258603, by rfl⟩ : syracuseStep 3011471 = 4517207) B4517207
theorem B1692571 : Blo 1336987 1692571 := bstep (se 1 (by rfl) ⟨1269428, by rfl⟩ : syracuseStep 1692571 = 2538857) B2538857
theorem B3388331 : Blo 1336987 3388331 := bstep (se 1 (by rfl) ⟨2541248, by rfl⟩ : syracuseStep 3388331 = 5082497) B5082497
theorem B2257895 : Blo 1336987 2257895 := bstep (se 1 (by rfl) ⟨1693421, by rfl⟩ : syracuseStep 2257895 = 3386843) B3386843
theorem B3388513 : Blo 1336987 3388513 := bstep (se 2 (by rfl) ⟨1270692, by rfl⟩ : syracuseStep 3388513 = 2541385) B2541385
theorem B29316269 : Blo 1336987 29316269 := bstep (se 3 (by rfl) ⟨5496800, by rfl⟩ : syracuseStep 29316269 = 10993601) B10993601
theorem B1504543 : Blo 1336987 1504543 := bstep (se 1 (by rfl) ⟨1128407, by rfl⟩ : syracuseStep 1504543 = 2256815) B2256815
theorem B11580761 : Blo 1336987 11580761 := bstep (se 2 (by rfl) ⟨4342785, by rfl⟩ : syracuseStep 11580761 = 8685571) B8685571
theorem B1357147 : Blo 1336987 1357147 := bstep (se 1 (by rfl) ⟨1017860, by rfl⟩ : syracuseStep 1357147 = 2035721) B2035721
theorem B3216827 : Blo 1336987 3216827 := bstep (se 1 (by rfl) ⟨2412620, by rfl⟩ : syracuseStep 3216827 = 4825241) B4825241
theorem B1504831 : Blo 1336987 1504831 := bstep (se 1 (by rfl) ⟨1128623, by rfl⟩ : syracuseStep 1504831 = 2257247) B2257247
theorem B3012191 : Blo 1336987 3012191 := bstep (se 1 (by rfl) ⟨2259143, by rfl⟩ : syracuseStep 3012191 = 4518287) B4518287
theorem B6772409 : Blo 1336987 6772409 := bstep (se 2 (by rfl) ⟨2539653, by rfl⟩ : syracuseStep 6772409 = 5079307) B5079307
theorem B1693487 : Blo 1336987 1693487 := bstep (se 1 (by rfl) ⟨1270115, by rfl⟩ : syracuseStep 1693487 = 2540231) B2540231
theorem B3012407 : Blo 1336987 3012407 := bstep (se 1 (by rfl) ⟨2259305, by rfl⟩ : syracuseStep 3012407 = 4518611) B4518611
theorem B70424579 : Blo 1336987 70424579 := bstep (se 1 (by rfl) ⟨52818434, by rfl⟩ : syracuseStep 70424579 = 105636869) B105636869
theorem B2259049 : Blo 1336987 2259049 := bstep (se 2 (by rfl) ⟨847143, by rfl⟩ : syracuseStep 2259049 = 1694287) B1694287
theorem B3012713 : Blo 1336987 3012713 := bstep (se 2 (by rfl) ⟨1129767, by rfl⟩ : syracuseStep 3012713 = 2259535) B2259535
theorem B69556493 : Blo 1336987 69556493 := bstep (se 3 (by rfl) ⟨13041842, by rfl⟩ : syracuseStep 69556493 = 26083685) B26083685
theorem B1505659 : Blo 1336987 1505659 := bstep (se 1 (by rfl) ⟨1129244, by rfl⟩ : syracuseStep 1505659 = 2258489) B2258489
theorem B2005499 : Blo 1336987 2005499 := bstep (se 1 (by rfl) ⟨1504124, by rfl⟩ : syracuseStep 2005499 = 3008249) B3008249
theorem B24746555 : Blo 1336987 24746555 := bstep (se 1 (by rfl) ⟨18559916, by rfl⟩ : syracuseStep 24746555 = 37119833) B37119833
theorem B2005625 : Blo 1336987 2005625 := bstep (se 2 (by rfl) ⟨752109, by rfl⟩ : syracuseStep 2005625 = 1504219) B1504219
theorem B2005679 : Blo 1336987 2005679 := bstep (se 1 (by rfl) ⟨1504259, by rfl⟩ : syracuseStep 2005679 = 3008519) B3008519
theorem B2005727 : Blo 1336987 2005727 := bstep (se 1 (by rfl) ⟨1504295, by rfl⟩ : syracuseStep 2005727 = 3008591) B3008591
theorem B1506127 : Blo 1336987 1506127 := bstep (se 1 (by rfl) ⟨1129595, by rfl⟩ : syracuseStep 1506127 = 2259191) B2259191
theorem B14474159 : Blo 1336987 14474159 := bstep (se 1 (by rfl) ⟨10855619, by rfl⟩ : syracuseStep 14474159 = 21711239) B21711239
theorem B2005991 : Blo 1336987 2005991 := bstep (se 1 (by rfl) ⟨1504493, by rfl⟩ : syracuseStep 2005991 = 3008987) B3008987
theorem B9649181 : Blo 1336987 9649181 := bstep (se 3 (by rfl) ⟨1809221, by rfl⟩ : syracuseStep 9649181 = 3618443) B3618443
theorem B11426939 : Blo 1336987 11426939 := bstep (se 1 (by rfl) ⟨8570204, by rfl⟩ : syracuseStep 11426939 = 17140409) B17140409
theorem B6519947 : Blo 1336987 6519947 := bstep (se 1 (by rfl) ⟨4889960, by rfl⟩ : syracuseStep 6519947 = 9779921) B9779921
theorem B2006249 : Blo 1336987 2006249 := bstep (se 2 (by rfl) ⟨752343, by rfl⟩ : syracuseStep 2006249 = 1504687) B1504687
theorem B2006303 : Blo 1336987 2006303 := bstep (se 1 (by rfl) ⟨1504727, by rfl⟩ : syracuseStep 2006303 = 3009455) B3009455
theorem B2710921 : Blo 1336987 2710921 := bstep (se 2 (by rfl) ⟨1016595, by rfl⟩ : syracuseStep 2710921 = 2033191) B2033191
theorem B4513211 : Blo 1336987 4513211 := bstep (se 1 (by rfl) ⟨3384908, by rfl⟩ : syracuseStep 4513211 = 6769817) B6769817
theorem B2006471 : Blo 1336987 2006471 := bstep (se 1 (by rfl) ⟨1504853, by rfl⟩ : syracuseStep 2006471 = 3009707) B3009707
theorem B8134103 : Blo 1336987 8134103 := bstep (se 1 (by rfl) ⟨6100577, by rfl⟩ : syracuseStep 8134103 = 12201155) B12201155
theorem B2539001 : Blo 1336987 2539001 := bstep (se 2 (by rfl) ⟨952125, by rfl⟩ : syracuseStep 2539001 = 1904251) B1904251
theorem B15449615 : Blo 1336987 15449615 := bstep (se 1 (by rfl) ⟨11587211, by rfl⟩ : syracuseStep 15449615 = 23174423) B23174423
theorem B7233083 : Blo 1336987 7233083 := bstep (se 1 (by rfl) ⟨5424812, by rfl⟩ : syracuseStep 7233083 = 10849625) B10849625
theorem B5078609 : Blo 1336987 5078609 := bstep (se 2 (by rfl) ⟨1904478, by rfl⟩ : syracuseStep 5078609 = 3808957) B3808957
theorem B6774353 : Blo 1336987 6774353 := bstep (se 2 (by rfl) ⟨2540382, by rfl⟩ : syracuseStep 6774353 = 5080765) B5080765
theorem B2006825 : Blo 1336987 2006825 := bstep (se 2 (by rfl) ⟨752559, by rfl⟩ : syracuseStep 2006825 = 1505119) B1505119
theorem B2006831 : Blo 1336987 2006831 := bstep (se 1 (by rfl) ⟨1505123, by rfl⟩ : syracuseStep 2006831 = 3010247) B3010247
theorem B10157885 : Blo 1336987 10157885 := bstep (se 3 (by rfl) ⟨1904603, by rfl⟩ : syracuseStep 10157885 = 3809207) B3809207
theorem B19292417 : Blo 1336987 19292417 := bstep (se 2 (by rfl) ⟨7234656, by rfl⟩ : syracuseStep 19292417 = 14469313) B14469313
theorem B8135099 : Blo 1336987 8135099 := bstep (se 1 (by rfl) ⟨6101324, by rfl⟩ : syracuseStep 8135099 = 12202649) B12202649
theorem B2007503 : Blo 1336987 2007503 := bstep (se 1 (by rfl) ⟨1505627, by rfl⟩ : syracuseStep 2007503 = 3011255) B3011255
theorem B2007545 : Blo 1336987 2007545 := bstep (se 2 (by rfl) ⟨752829, by rfl⟩ : syracuseStep 2007545 = 1505659) B1505659
theorem B4285001 : Blo 1336987 4285001 := bstep (se 2 (by rfl) ⟨1606875, by rfl⟩ : syracuseStep 4285001 = 3213751) B3213751
theorem B2007647 : Blo 1336987 2007647 := bstep (se 1 (by rfl) ⟨1505735, by rfl⟩ : syracuseStep 2007647 = 3011471) B3011471
theorem B185483981 : Blo 1336987 185483981 := bstep (se 3 (by rfl) ⟨34778246, by rfl⟩ : syracuseStep 185483981 = 69556493) B69556493
theorem B10158857 : Blo 1336987 10158857 := bstep (se 2 (by rfl) ⟨3809571, by rfl⟩ : syracuseStep 10158857 = 7619143) B7619143
theorem B38552435 : Blo 1336987 38552435 := bstep (se 1 (by rfl) ⟨28914326, by rfl⟩ : syracuseStep 38552435 = 57828653) B57828653
theorem B2008127 : Blo 1336987 2008127 := bstep (se 1 (by rfl) ⟨1506095, by rfl⟩ : syracuseStep 2008127 = 3012191) B3012191
theorem B2008169 : Blo 1336987 2008169 := bstep (se 2 (by rfl) ⟨753063, by rfl⟩ : syracuseStep 2008169 = 1506127) B1506127
theorem B4514939 : Blo 1336987 4514939 := bstep (se 1 (by rfl) ⟨3386204, by rfl⟩ : syracuseStep 4514939 = 6772409) B6772409
theorem B2409679 : Blo 1336987 2409679 := bstep (se 1 (by rfl) ⟨1807259, by rfl⟩ : syracuseStep 2409679 = 3614519) B3614519
theorem B2008271 : Blo 1336987 2008271 := bstep (se 1 (by rfl) ⟨1506203, by rfl⟩ : syracuseStep 2008271 = 3012407) B3012407
theorem B18302219 : Blo 1336987 18302219 := bstep (se 1 (by rfl) ⟨13726664, by rfl⟩ : syracuseStep 18302219 = 27453329) B27453329
theorem B3433801 : Blo 1336987 3433801 := bstep (se 2 (by rfl) ⟨1287675, by rfl⟩ : syracuseStep 3433801 = 2575351) B2575351
theorem B46949719 : Blo 1336987 46949719 := bstep (se 1 (by rfl) ⟨35212289, by rfl⟩ : syracuseStep 46949719 = 70424579) B70424579
theorem B4515209 : Blo 1336987 4515209 := bstep (se 2 (by rfl) ⟨1693203, by rfl⟩ : syracuseStep 4515209 = 3386407) B3386407
theorem B2008475 : Blo 1336987 2008475 := bstep (se 1 (by rfl) ⟨1506356, by rfl⟩ : syracuseStep 2008475 = 3012713) B3012713
theorem B7833241 : Blo 1336987 7833241 := bstep (se 2 (by rfl) ⟨2937465, by rfl⟩ : syracuseStep 7833241 = 5874931) B5874931
theorem B1336999 : Blo 1336987 1336999 := bstep (se 1 (by rfl) ⟨1002749, by rfl⟩ : syracuseStep 1336999 = 2005499) B2005499
theorem B1337083 : Blo 1336987 1337083 := bstep (se 1 (by rfl) ⟨1002812, by rfl⟩ : syracuseStep 1337083 = 2005625) B2005625
theorem B1337119 : Blo 1336987 1337119 := bstep (se 1 (by rfl) ⟨1002839, by rfl⟩ : syracuseStep 1337119 = 2005679) B2005679
theorem B1337151 : Blo 1336987 1337151 := bstep (se 1 (by rfl) ⟨1002863, by rfl⟩ : syracuseStep 1337151 = 2005727) B2005727
theorem B3614561 : Blo 1336987 3614561 := bstep (se 2 (by rfl) ⟨1355460, by rfl⟩ : syracuseStep 3614561 = 2710921) B2710921
theorem B1337327 : Blo 1336987 1337327 := bstep (se 1 (by rfl) ⟨1002995, by rfl⟩ : syracuseStep 1337327 = 2005991) B2005991
theorem B6432787 : Blo 1336987 6432787 := bstep (se 1 (by rfl) ⟨4824590, by rfl⟩ : syracuseStep 6432787 = 9649181) B9649181
theorem B4515965 : Blo 1336987 4515965 := bstep (se 3 (by rfl) ⟨846743, by rfl⟩ : syracuseStep 4515965 = 1693487) B1693487
theorem B1337499 : Blo 1336987 1337499 := bstep (se 1 (by rfl) ⟨1003124, by rfl⟩ : syracuseStep 1337499 = 2006249) B2006249
theorem B1525915 : Blo 1336987 1525915 := bstep (se 1 (by rfl) ⟨1144436, by rfl⟩ : syracuseStep 1525915 = 2288873) B2288873
theorem B1337535 : Blo 1336987 1337535 := bstep (se 1 (by rfl) ⟨1003151, by rfl⟩ : syracuseStep 1337535 = 2006303) B2006303
theorem B3008807 : Blo 1336987 3008807 := bstep (se 1 (by rfl) ⟨2256605, by rfl⟩ : syracuseStep 3008807 = 4513211) B4513211
theorem B1337647 : Blo 1336987 1337647 := bstep (se 1 (by rfl) ⟨1003235, by rfl⟩ : syracuseStep 1337647 = 2006471) B2006471
theorem B2541871 : Blo 1336987 2541871 := bstep (se 1 (by rfl) ⟨1906403, by rfl⟩ : syracuseStep 2541871 = 3812807) B3812807
theorem B3008825 : Blo 1336987 3008825 := bstep (se 2 (by rfl) ⟨1128309, by rfl⟩ : syracuseStep 3008825 = 2256619) B2256619
theorem B10299743 : Blo 1336987 10299743 := bstep (se 1 (by rfl) ⟨7724807, by rfl⟩ : syracuseStep 10299743 = 15449615) B15449615
theorem B3385739 : Blo 1336987 3385739 := bstep (se 1 (by rfl) ⟨2539304, by rfl⟩ : syracuseStep 3385739 = 5078609) B5078609
theorem B4516235 : Blo 1336987 4516235 := bstep (se 1 (by rfl) ⟨3387176, by rfl⟩ : syracuseStep 4516235 = 6774353) B6774353
theorem B7621127 : Blo 1336987 7621127 := bstep (se 1 (by rfl) ⟨5715845, by rfl⟩ : syracuseStep 7621127 = 11431691) B11431691
theorem B1337883 : Blo 1336987 1337883 := bstep (se 1 (by rfl) ⟨1003412, by rfl⟩ : syracuseStep 1337883 = 2006825) B2006825
theorem B1337887 : Blo 1336987 1337887 := bstep (se 1 (by rfl) ⟨1003415, by rfl⟩ : syracuseStep 1337887 = 2006831) B2006831
theorem B6777593 : Blo 1336987 6777593 := bstep (se 2 (by rfl) ⟨2541597, by rfl⟩ : syracuseStep 6777593 = 5083195) B5083195
theorem B1338203 : Blo 1336987 1338203 := bstep (se 1 (by rfl) ⟨1003652, by rfl⟩ : syracuseStep 1338203 = 2007305) B2007305
theorem B8571743 : Blo 1336987 8571743 := bstep (se 1 (by rfl) ⟨6428807, by rfl⟩ : syracuseStep 8571743 = 12857615) B12857615
theorem B1338271 : Blo 1336987 1338271 := bstep (se 1 (by rfl) ⟨1003703, by rfl⟩ : syracuseStep 1338271 = 2007407) B2007407
theorem B17386525 : Blo 1336987 17386525 := bstep (se 3 (by rfl) ⟨3259973, by rfl⟩ : syracuseStep 17386525 = 6519947) B6519947
theorem B1338415 : Blo 1336987 1338415 := bstep (se 1 (by rfl) ⟨1003811, by rfl⟩ : syracuseStep 1338415 = 2007623) B2007623
theorem B1338439 : Blo 1336987 1338439 := bstep (se 1 (by rfl) ⟨1003829, by rfl⟩ : syracuseStep 1338439 = 2007659) B2007659
theorem B24742991 : Blo 1336987 24742991 := bstep (se 1 (by rfl) ⟨18557243, by rfl⟩ : syracuseStep 24742991 = 37114487) B37114487
theorem B1338591 : Blo 1336987 1338591 := bstep (se 1 (by rfl) ⟨1003943, by rfl⟩ : syracuseStep 1338591 = 2007887) B2007887
theorem B15240473 : Blo 1336987 15240473 := bstep (se 2 (by rfl) ⟨5715177, by rfl⟩ : syracuseStep 15240473 = 11430355) B11430355
theorem B2256295 : Blo 1336987 2256295 := bstep (se 1 (by rfl) ⟨1692221, by rfl⟩ : syracuseStep 2256295 = 3384443) B3384443
theorem B1338855 : Blo 1336987 1338855 := bstep (se 1 (by rfl) ⟨1004141, by rfl⟩ : syracuseStep 1338855 = 2008283) B2008283
theorem B2256457 : Blo 1336987 2256457 := bstep (se 2 (by rfl) ⟨846171, by rfl⟩ : syracuseStep 2256457 = 1692343) B1692343
theorem B3010121 : Blo 1336987 3010121 := bstep (se 2 (by rfl) ⟨1128795, by rfl⟩ : syracuseStep 3010121 = 2257591) B2257591
theorem B1338971 : Blo 1336987 1338971 := bstep (se 1 (by rfl) ⟨1004228, by rfl⟩ : syracuseStep 1338971 = 2008457) B2008457
theorem B2256491 : Blo 1336987 2256491 := bstep (se 1 (by rfl) ⟨1692368, by rfl⟩ : syracuseStep 2256491 = 3384737) B3384737
theorem B3387055 : Blo 1336987 3387055 := bstep (se 1 (by rfl) ⟨2540291, by rfl⟩ : syracuseStep 3387055 = 5080583) B5080583
theorem B12201769 : Blo 1336987 12201769 := bstep (se 2 (by rfl) ⟨4575663, by rfl⟩ : syracuseStep 12201769 = 9151327) B9151327
theorem B19296107 : Blo 1336987 19296107 := bstep (se 1 (by rfl) ⟨14472080, by rfl⟩ : syracuseStep 19296107 = 28944161) B28944161
theorem B2256761 : Blo 1336987 2256761 := bstep (se 2 (by rfl) ⟨846285, by rfl⟩ : syracuseStep 2256761 = 1692571) B1692571
theorem B17624965 : Blo 1336987 17624965 := bstep (se 4 (by rfl) ⟨1652340, by rfl⟩ : syracuseStep 17624965 = 3304681) B3304681
theorem B5713847 : Blo 1336987 5713847 := bstep (se 1 (by rfl) ⟨4285385, by rfl⟩ : syracuseStep 5713847 = 8570771) B8570771
theorem B3387359 : Blo 1336987 3387359 := bstep (se 1 (by rfl) ⟨2540519, by rfl⟩ : syracuseStep 3387359 = 5081039) B5081039
theorem B4517855 : Blo 1336987 4517855 := bstep (se 1 (by rfl) ⟨3388391, by rfl⟩ : syracuseStep 4517855 = 6776783) B6776783
theorem B3387379 : Blo 1336987 3387379 := bstep (se 1 (by rfl) ⟨2540534, by rfl⟩ : syracuseStep 3387379 = 5081069) B5081069
theorem B7614587 : Blo 1336987 7614587 := bstep (se 1 (by rfl) ⟨5710940, by rfl⟩ : syracuseStep 7614587 = 11421881) B11421881
theorem B4518017 : Blo 1336987 4518017 := bstep (se 2 (by rfl) ⟨1694256, by rfl⟩ : syracuseStep 4518017 = 3388513) B3388513
theorem B6426809 : Blo 1336987 6426809 := bstep (se 2 (by rfl) ⟨2410053, by rfl⟩ : syracuseStep 6426809 = 4820107) B4820107
theorem B3387703 : Blo 1336987 3387703 := bstep (se 1 (by rfl) ⟨2540777, by rfl⟩ : syracuseStep 3387703 = 5081555) B5081555
theorem B14463521 : Blo 1336987 14463521 := bstep (se 2 (by rfl) ⟨5423820, by rfl⟩ : syracuseStep 14463521 = 10847641) B10847641
theorem B3388007 : Blo 1336987 3388007 := bstep (se 1 (by rfl) ⟨2541005, by rfl⟩ : syracuseStep 3388007 = 5082011) B5082011
theorem B4518503 : Blo 1336987 4518503 := bstep (se 1 (by rfl) ⟨3388877, by rfl⟩ : syracuseStep 4518503 = 6777755) B6777755
theorem B1504111 : Blo 1336987 1504111 := bstep (se 1 (by rfl) ⟨1128083, by rfl⟩ : syracuseStep 1504111 = 2256167) B2256167
theorem B4518827 : Blo 1336987 4518827 := bstep (se 1 (by rfl) ⟨3389120, by rfl⟩ : syracuseStep 4518827 = 6778241) B6778241
theorem B1692667 : Blo 1336987 1692667 := bstep (se 1 (by rfl) ⟨1269500, by rfl⟩ : syracuseStep 1692667 = 2539001) B2539001
theorem B2257915 : Blo 1336987 2257915 := bstep (se 1 (by rfl) ⟨1693436, by rfl⟩ : syracuseStep 2257915 = 3386873) B3386873
theorem B3011579 : Blo 1336987 3011579 := bstep (se 1 (by rfl) ⟨2258684, by rfl⟩ : syracuseStep 3011579 = 4517369) B4517369
theorem B4822055 : Blo 1336987 4822055 := bstep (se 1 (by rfl) ⟨3616541, by rfl⟩ : syracuseStep 4822055 = 7233083) B7233083
theorem B3011759 : Blo 1336987 3011759 := bstep (se 1 (by rfl) ⟨2258819, by rfl⟩ : syracuseStep 3011759 = 4517639) B4517639
theorem B6771923 : Blo 1336987 6771923 := bstep (se 1 (by rfl) ⟨5078942, by rfl⟩ : syracuseStep 6771923 = 10157885) B10157885
theorem B3011795 : Blo 1336987 3011795 := bstep (se 1 (by rfl) ⟨2258846, by rfl⟩ : syracuseStep 3011795 = 4517693) B4517693
theorem B17372503 : Blo 1336987 17372503 := bstep (se 1 (by rfl) ⟨13029377, by rfl⟩ : syracuseStep 17372503 = 26058755) B26058755
theorem B2258347 : Blo 1336987 2258347 := bstep (se 1 (by rfl) ⟨1693760, by rfl⟩ : syracuseStep 2258347 = 3387521) B3387521
theorem B51451361 : Blo 1336987 51451361 := bstep (se 2 (by rfl) ⟨19294260, by rfl⟩ : syracuseStep 51451361 = 38588521) B38588521
theorem B3012065 : Blo 1336987 3012065 := bstep (se 2 (by rfl) ⟨1129524, by rfl⟩ : syracuseStep 3012065 = 2259049) B2259049
theorem B19559981 : Blo 1336987 19559981 := bstep (se 3 (by rfl) ⟨3667496, by rfl⟩ : syracuseStep 19559981 = 7334993) B7334993
theorem B2897479 : Blo 1336987 2897479 := bstep (se 1 (by rfl) ⟨2173109, by rfl⟩ : syracuseStep 2897479 = 4346219) B4346219
theorem B3388999 : Blo 1336987 3388999 := bstep (se 1 (by rfl) ⟨2541749, by rfl⟩ : syracuseStep 3388999 = 5083499) B5083499
theorem B2258543 : Blo 1336987 2258543 := bstep (se 1 (by rfl) ⟨1693907, by rfl⟩ : syracuseStep 2258543 = 3387815) B3387815
theorem B3389111 : Blo 1336987 3389111 := bstep (se 1 (by rfl) ⟨2541833, by rfl⟩ : syracuseStep 3389111 = 5083667) B5083667
theorem B17381081 : Blo 1336987 17381081 := bstep (se 2 (by rfl) ⟨6517905, by rfl⟩ : syracuseStep 17381081 = 13035811) B13035811
theorem B2258651 : Blo 1336987 2258651 := bstep (se 1 (by rfl) ⟨1693988, by rfl⟩ : syracuseStep 2258651 = 3387977) B3387977
theorem B1693639 : Blo 1336987 1693639 := bstep (se 1 (by rfl) ⟨1270229, by rfl⟩ : syracuseStep 1693639 = 2540459) B2540459
theorem B2258887 : Blo 1336987 2258887 := bstep (se 1 (by rfl) ⟨1694165, by rfl⟩ : syracuseStep 2258887 = 3388331) B3388331
theorem B4577255 : Blo 1336987 4577255 := bstep (se 1 (by rfl) ⟨3432941, by rfl⟩ : syracuseStep 4577255 = 6865883) B6865883
theorem B1505263 : Blo 1336987 1505263 := bstep (se 1 (by rfl) ⟨1128947, by rfl⟩ : syracuseStep 1505263 = 2257895) B2257895
theorem B19544179 : Blo 1336987 19544179 := bstep (se 1 (by rfl) ⟨14658134, by rfl⟩ : syracuseStep 19544179 = 29316269) B29316269
theorem B2857103 : Blo 1336987 2857103 := bstep (se 1 (by rfl) ⟨2142827, by rfl⟩ : syracuseStep 2857103 = 4285655) B4285655
theorem B3807431 : Blo 1336987 3807431 := bstep (se 1 (by rfl) ⟨2855573, by rfl⟩ : syracuseStep 3807431 = 5711147) B5711147
theorem B30882029 : Blo 1336987 30882029 := bstep (se 3 (by rfl) ⟨5790380, by rfl⟩ : syracuseStep 30882029 = 11580761) B11580761
theorem B2144551 : Blo 1336987 2144551 := bstep (se 1 (by rfl) ⟨1608413, by rfl⟩ : syracuseStep 2144551 = 3216827) B3216827
theorem B12204553 : Blo 1336987 12204553 := bstep (se 2 (by rfl) ⟨4576707, by rfl⟩ : syracuseStep 12204553 = 9153415) B9153415
theorem B2005535 : Blo 1336987 2005535 := bstep (se 1 (by rfl) ⟨1504151, by rfl⟩ : syracuseStep 2005535 = 3008303) B3008303
theorem B4512617 : Blo 1336987 4512617 := bstep (se 2 (by rfl) ⟨1692231, by rfl⟩ : syracuseStep 4512617 = 3384463) B3384463
theorem B4512671 : Blo 1336987 4512671 := bstep (se 1 (by rfl) ⟨3384503, by rfl⟩ : syracuseStep 4512671 = 6769007) B6769007
theorem B2005919 : Blo 1336987 2005919 := bstep (se 1 (by rfl) ⟨1504439, by rfl⟩ : syracuseStep 2005919 = 3008879) B3008879
theorem B6773705 : Blo 1336987 6773705 := bstep (se 2 (by rfl) ⟨2540139, by rfl⟩ : syracuseStep 6773705 = 5080279) B5080279
theorem B2005967 : Blo 1336987 2005967 := bstep (se 1 (by rfl) ⟨1504475, by rfl⟩ : syracuseStep 2005967 = 3008951) B3008951
theorem B16497703 : Blo 1336987 16497703 := bstep (se 1 (by rfl) ⟨12373277, by rfl⟩ : syracuseStep 16497703 = 24746555) B24746555
theorem B2006057 : Blo 1336987 2006057 := bstep (se 2 (by rfl) ⟨752271, by rfl⟩ : syracuseStep 2006057 = 1504543) B1504543
theorem B2006063 : Blo 1336987 2006063 := bstep (se 1 (by rfl) ⟨1504547, by rfl⟩ : syracuseStep 2006063 = 3009095) B3009095
theorem B2006087 : Blo 1336987 2006087 := bstep (se 1 (by rfl) ⟨1504565, by rfl⟩ : syracuseStep 2006087 = 3009131) B3009131
theorem B1809529 : Blo 1336987 1809529 := bstep (se 2 (by rfl) ⟨678573, by rfl⟩ : syracuseStep 1809529 = 1357147) B1357147
theorem B9649439 : Blo 1336987 9649439 := bstep (se 1 (by rfl) ⟨7237079, by rfl⟩ : syracuseStep 9649439 = 14474159) B14474159
theorem B2006351 : Blo 1336987 2006351 := bstep (se 1 (by rfl) ⟨1504763, by rfl⟩ : syracuseStep 2006351 = 3009527) B3009527
theorem B7617959 : Blo 1336987 7617959 := bstep (se 1 (by rfl) ⟨5713469, by rfl⟩ : syracuseStep 7617959 = 11426939) B11426939
theorem B2006441 : Blo 1336987 2006441 := bstep (se 2 (by rfl) ⟨752415, by rfl⟩ : syracuseStep 2006441 = 1504831) B1504831
theorem B3808775 : Blo 1336987 3808775 := bstep (se 1 (by rfl) ⟨2856581, by rfl⟩ : syracuseStep 3808775 = 5713163) B5713163
theorem B2006591 : Blo 1336987 2006591 := bstep (se 1 (by rfl) ⟨1504943, by rfl⟩ : syracuseStep 2006591 = 3009887) B3009887
theorem B5422735 : Blo 1336987 5422735 := bstep (se 1 (by rfl) ⟨4067051, by rfl⟩ : syracuseStep 5422735 = 8134103) B8134103
theorem B6774515 : Blo 1336987 6774515 := bstep (se 1 (by rfl) ⟨5080886, by rfl⟩ : syracuseStep 6774515 = 10161773) B10161773
theorem B3809015 : Blo 1336987 3809015 := bstep (se 1 (by rfl) ⟨2856761, by rfl⟩ : syracuseStep 3809015 = 5713523) B5713523
theorem B2858743 : Blo 1336987 2858743 := bstep (se 1 (by rfl) ⟨2144057, by rfl⟩ : syracuseStep 2858743 = 4288115) B4288115
theorem B2006855 : Blo 1336987 2006855 := bstep (se 1 (by rfl) ⟨1505141, by rfl⟩ : syracuseStep 2006855 = 3010283) B3010283
theorem B2006939 : Blo 1336987 2006939 := bstep (se 1 (by rfl) ⟨1505204, by rfl⟩ : syracuseStep 2006939 = 3010409) B3010409
theorem B8577049 : Blo 1336987 8577049 := bstep (se 2 (by rfl) ⟨3216393, by rfl⟩ : syracuseStep 8577049 = 6432787) B6432787
theorem B4284539 : Blo 1336987 4284539 := bstep (se 1 (by rfl) ⟨3213404, by rfl⟩ : syracuseStep 4284539 = 6426809) B6426809
theorem B26058905 : Blo 1336987 26058905 := bstep (se 2 (by rfl) ⟨9772089, by rfl⟩ : syracuseStep 26058905 = 19544179) B19544179
theorem B12861611 : Blo 1336987 12861611 := bstep (se 1 (by rfl) ⟨9646208, by rfl⟩ : syracuseStep 12861611 = 19292417) B19292417
theorem B5423399 : Blo 1336987 5423399 := bstep (se 1 (by rfl) ⟨4067549, by rfl⟩ : syracuseStep 5423399 = 8135099) B8135099
theorem B9642347 : Blo 1336987 9642347 := bstep (se 1 (by rfl) ⟨7231760, by rfl⟩ : syracuseStep 9642347 = 14463521) B14463521
theorem B2859401 : Blo 1336987 2859401 := bstep (se 2 (by rfl) ⟨1072275, by rfl⟩ : syracuseStep 2859401 = 2144551) B2144551
theorem B9650821 : Blo 1336987 9650821 := bstep (se 4 (by rfl) ⟨904764, by rfl⟩ : syracuseStep 9650821 = 1809529) B1809529
theorem B2007719 : Blo 1336987 2007719 := bstep (se 1 (by rfl) ⟨1505789, by rfl⟩ : syracuseStep 2007719 = 3011579) B3011579
theorem B2007839 : Blo 1336987 2007839 := bstep (se 1 (by rfl) ⟨1505879, by rfl⟩ : syracuseStep 2007839 = 3011759) B3011759
theorem B4514615 : Blo 1336987 4514615 := bstep (se 1 (by rfl) ⟨3385961, by rfl⟩ : syracuseStep 4514615 = 6771923) B6771923
theorem B2007863 : Blo 1336987 2007863 := bstep (se 1 (by rfl) ⟨1505897, by rfl⟩ : syracuseStep 2007863 = 3011795) B3011795
theorem B34300907 : Blo 1336987 34300907 := bstep (se 1 (by rfl) ⟨25725680, by rfl⟩ : syracuseStep 34300907 = 51451361) B51451361
theorem B2008043 : Blo 1336987 2008043 := bstep (se 1 (by rfl) ⟨1506032, by rfl⟩ : syracuseStep 2008043 = 3012065) B3012065
theorem B2409707 : Blo 1336987 2409707 := bstep (se 1 (by rfl) ⟨1807280, by rfl⟩ : syracuseStep 2409707 = 3614561) B3614561
theorem B21996937 : Blo 1336987 21996937 := bstep (se 2 (by rfl) ⟨8248851, by rfl⟩ : syracuseStep 21996937 = 16497703) B16497703
theorem B52159949 : Blo 1336987 52159949 := bstep (se 3 (by rfl) ⟨9779990, by rfl⟩ : syracuseStep 52159949 = 19559981) B19559981
theorem B6866495 : Blo 1336987 6866495 := bstep (se 1 (by rfl) ⟨5149871, by rfl⟩ : syracuseStep 6866495 = 10299743) B10299743
theorem B3212905 : Blo 1336987 3212905 := bstep (se 2 (by rfl) ⟨1204839, by rfl⟩ : syracuseStep 3212905 = 2409679) B2409679
theorem B5080751 : Blo 1336987 5080751 := bstep (se 1 (by rfl) ⟨3810563, by rfl⟩ : syracuseStep 5080751 = 7621127) B7621127
theorem B1337023 : Blo 1336987 1337023 := bstep (se 1 (by rfl) ⟨1002767, by rfl⟩ : syracuseStep 1337023 = 2005535) B2005535
theorem B3008393 : Blo 1336987 3008393 := bstep (se 2 (by rfl) ⟨1128147, by rfl⟩ : syracuseStep 3008393 = 2256295) B2256295
theorem B3008411 : Blo 1336987 3008411 := bstep (se 1 (by rfl) ⟨2256308, by rfl⟩ : syracuseStep 3008411 = 4512617) B4512617
theorem B3008447 : Blo 1336987 3008447 := bstep (se 1 (by rfl) ⟨2256335, by rfl⟩ : syracuseStep 3008447 = 4512671) B4512671
theorem B1337279 : Blo 1336987 1337279 := bstep (se 1 (by rfl) ⟨1002959, by rfl⟩ : syracuseStep 1337279 = 2005919) B2005919
theorem B4515803 : Blo 1336987 4515803 := bstep (se 1 (by rfl) ⟨3386852, by rfl⟩ : syracuseStep 4515803 = 6773705) B6773705
theorem B1337311 : Blo 1336987 1337311 := bstep (se 1 (by rfl) ⟨1002983, by rfl⟩ : syracuseStep 1337311 = 2005967) B2005967
theorem B1337371 : Blo 1336987 1337371 := bstep (se 1 (by rfl) ⟨1003028, by rfl⟩ : syracuseStep 1337371 = 2006057) B2006057
theorem B1337375 : Blo 1336987 1337375 := bstep (se 1 (by rfl) ⟨1003031, by rfl⟩ : syracuseStep 1337375 = 2006063) B2006063
theorem B1337391 : Blo 1336987 1337391 := bstep (se 1 (by rfl) ⟨1003043, by rfl⟩ : syracuseStep 1337391 = 2006087) B2006087
theorem B3008609 : Blo 1336987 3008609 := bstep (se 2 (by rfl) ⟨1128228, by rfl⟩ : syracuseStep 3008609 = 2256457) B2256457
theorem B10160315 : Blo 1336987 10160315 := bstep (se 1 (by rfl) ⟨7620236, by rfl⟩ : syracuseStep 10160315 = 15240473) B15240473
theorem B6432959 : Blo 1336987 6432959 := bstep (se 1 (by rfl) ⟨4824719, by rfl⟩ : syracuseStep 6432959 = 9649439) B9649439
theorem B1337567 : Blo 1336987 1337567 := bstep (se 1 (by rfl) ⟨1003175, by rfl⟩ : syracuseStep 1337567 = 2006351) B2006351
theorem B4516073 : Blo 1336987 4516073 := bstep (se 2 (by rfl) ⟨1693527, by rfl⟩ : syracuseStep 4516073 = 3387055) B3387055
theorem B1337627 : Blo 1336987 1337627 := bstep (se 1 (by rfl) ⟨1003220, by rfl⟩ : syracuseStep 1337627 = 2006441) B2006441
theorem B3811657 : Blo 1336987 3811657 := bstep (se 2 (by rfl) ⟨1429371, by rfl⟩ : syracuseStep 3811657 = 2858743) B2858743
theorem B1337727 : Blo 1336987 1337727 := bstep (se 1 (by rfl) ⟨1003295, by rfl⟩ : syracuseStep 1337727 = 2006591) B2006591
theorem B4516343 : Blo 1336987 4516343 := bstep (se 1 (by rfl) ⟨3387257, by rfl⟩ : syracuseStep 4516343 = 6774515) B6774515
theorem B1337903 : Blo 1336987 1337903 := bstep (se 1 (by rfl) ⟨1003427, by rfl⟩ : syracuseStep 1337903 = 2006855) B2006855
theorem B12864071 : Blo 1336987 12864071 := bstep (se 1 (by rfl) ⟨9648053, by rfl⟩ : syracuseStep 12864071 = 19296107) B19296107
theorem B1337959 : Blo 1336987 1337959 := bstep (se 1 (by rfl) ⟨1003469, by rfl⟩ : syracuseStep 1337959 = 2006939) B2006939
theorem B4516505 : Blo 1336987 4516505 := bstep (se 2 (by rfl) ⟨1693689, by rfl⟩ : syracuseStep 4516505 = 3387379) B3387379
theorem B2034553 : Blo 1336987 2034553 := bstep (se 2 (by rfl) ⟨762957, by rfl⟩ : syracuseStep 2034553 = 1525915) B1525915
theorem B1338335 : Blo 1336987 1338335 := bstep (se 1 (by rfl) ⟨1003751, by rfl⟩ : syracuseStep 1338335 = 2007503) B2007503
theorem B1338363 : Blo 1336987 1338363 := bstep (se 1 (by rfl) ⟨1003772, by rfl⟩ : syracuseStep 1338363 = 2007545) B2007545
theorem B1338431 : Blo 1336987 1338431 := bstep (se 1 (by rfl) ⟨1003823, by rfl⟩ : syracuseStep 1338431 = 2007647) B2007647
theorem B4516937 : Blo 1336987 4516937 := bstep (se 2 (by rfl) ⟨1693851, by rfl⟩ : syracuseStep 4516937 = 3387703) B3387703
theorem B25701623 : Blo 1336987 25701623 := bstep (se 1 (by rfl) ⟨19276217, by rfl⟩ : syracuseStep 25701623 = 38552435) B38552435
theorem B16272737 : Blo 1336987 16272737 := bstep (se 2 (by rfl) ⟨6102276, by rfl⟩ : syracuseStep 16272737 = 12204553) B12204553
theorem B3214703 : Blo 1336987 3214703 := bstep (se 1 (by rfl) ⟨2411027, by rfl⟩ : syracuseStep 3214703 = 4822055) B4822055
theorem B1338751 : Blo 1336987 1338751 := bstep (se 1 (by rfl) ⟨1004063, by rfl⟩ : syracuseStep 1338751 = 2008127) B2008127
theorem B1338779 : Blo 1336987 1338779 := bstep (se 1 (by rfl) ⟨1004084, by rfl⟩ : syracuseStep 1338779 = 2008169) B2008169
theorem B3009959 : Blo 1336987 3009959 := bstep (se 1 (by rfl) ⟨2257469, by rfl⟩ : syracuseStep 3009959 = 4514939) B4514939
theorem B1338847 : Blo 1336987 1338847 := bstep (se 1 (by rfl) ⟨1004135, by rfl⟩ : syracuseStep 1338847 = 2008271) B2008271
theorem B12201479 : Blo 1336987 12201479 := bstep (se 1 (by rfl) ⟨9151109, by rfl⟩ : syracuseStep 12201479 = 18302219) B18302219
theorem B3010139 : Blo 1336987 3010139 := bstep (se 1 (by rfl) ⟨2257604, by rfl⟩ : syracuseStep 3010139 = 4515209) B4515209
theorem B1338983 : Blo 1336987 1338983 := bstep (se 1 (by rfl) ⟨1004237, by rfl⟩ : syracuseStep 1338983 = 2008475) B2008475
theorem B11587387 : Blo 1336987 11587387 := bstep (se 1 (by rfl) ⟨8690540, by rfl⟩ : syracuseStep 11587387 = 17381081) B17381081
theorem B3051503 : Blo 1336987 3051503 := bstep (se 1 (by rfl) ⟨2288627, by rfl⟩ : syracuseStep 3051503 = 4577255) B4577255
theorem B2256889 : Blo 1336987 2256889 := bstep (se 2 (by rfl) ⟨846333, by rfl⟩ : syracuseStep 2256889 = 1692667) B1692667
theorem B3010553 : Blo 1336987 3010553 := bstep (se 2 (by rfl) ⟨1128957, by rfl⟩ : syracuseStep 3010553 = 2257915) B2257915
theorem B3010643 : Blo 1336987 3010643 := bstep (se 1 (by rfl) ⟨2257982, by rfl⟩ : syracuseStep 3010643 = 4515965) B4515965
theorem B1904735 : Blo 1336987 1904735 := bstep (se 1 (by rfl) ⟨1428551, by rfl⟩ : syracuseStep 1904735 = 2857103) B2857103
theorem B2257159 : Blo 1336987 2257159 := bstep (se 1 (by rfl) ⟨1692869, by rfl⟩ : syracuseStep 2257159 = 3385739) B3385739
theorem B3010823 : Blo 1336987 3010823 := bstep (se 1 (by rfl) ⟨2258117, by rfl⟩ : syracuseStep 3010823 = 4516235) B4516235
theorem B62599625 : Blo 1336987 62599625 := bstep (se 2 (by rfl) ⟨23474859, by rfl⟩ : syracuseStep 62599625 = 46949719) B46949719
theorem B23163337 : Blo 1336987 23163337 := bstep (se 2 (by rfl) ⟨8686251, by rfl⟩ : syracuseStep 23163337 = 17372503) B17372503
theorem B4518395 : Blo 1336987 4518395 := bstep (se 1 (by rfl) ⟨3388796, by rfl⟩ : syracuseStep 4518395 = 6777593) B6777593
theorem B3011129 : Blo 1336987 3011129 := bstep (se 2 (by rfl) ⟨1129173, by rfl⟩ : syracuseStep 3011129 = 2258347) B2258347
theorem B5714495 : Blo 1336987 5714495 := bstep (se 1 (by rfl) ⟨4285871, by rfl⟩ : syracuseStep 5714495 = 8571743) B8571743
theorem B16495327 : Blo 1336987 16495327 := bstep (se 1 (by rfl) ⟨12371495, by rfl⟩ : syracuseStep 16495327 = 24742991) B24742991
theorem B3863305 : Blo 1336987 3863305 := bstep (se 2 (by rfl) ⟨1448739, by rfl⟩ : syracuseStep 3863305 = 2897479) B2897479
theorem B4518665 : Blo 1336987 4518665 := bstep (se 2 (by rfl) ⟨1694499, by rfl⟩ : syracuseStep 4518665 = 3388999) B3388999
theorem B7230313 : Blo 1336987 7230313 := bstep (se 2 (by rfl) ⟨2711367, by rfl⟩ : syracuseStep 7230313 = 5422735) B5422735
theorem B1504327 : Blo 1336987 1504327 := bstep (se 1 (by rfl) ⟨1128245, by rfl⟩ : syracuseStep 1504327 = 2256491) B2256491
theorem B23499953 : Blo 1336987 23499953 := bstep (se 2 (by rfl) ⟨8812482, by rfl⟩ : syracuseStep 23499953 = 17624965) B17624965
theorem B1504507 : Blo 1336987 1504507 := bstep (se 1 (by rfl) ⟨1128380, by rfl⟩ : syracuseStep 1504507 = 2256761) B2256761
theorem B2258185 : Blo 1336987 2258185 := bstep (se 2 (by rfl) ⟨846819, by rfl⟩ : syracuseStep 2258185 = 1693639) B1693639
theorem B3011849 : Blo 1336987 3011849 := bstep (se 2 (by rfl) ⟨1129443, by rfl⟩ : syracuseStep 3011849 = 2258887) B2258887
theorem B2258239 : Blo 1336987 2258239 := bstep (se 1 (by rfl) ⟨1693679, by rfl⟩ : syracuseStep 2258239 = 3387359) B3387359
theorem B3011903 : Blo 1336987 3011903 := bstep (se 1 (by rfl) ⟨2258927, by rfl⟩ : syracuseStep 3011903 = 4517855) B4517855
theorem B5076391 : Blo 1336987 5076391 := bstep (se 1 (by rfl) ⟨3807293, by rfl⟩ : syracuseStep 5076391 = 7614587) B7614587
theorem B3012011 : Blo 1336987 3012011 := bstep (se 1 (by rfl) ⟨2259008, by rfl⟩ : syracuseStep 3012011 = 4518017) B4518017
theorem B2856667 : Blo 1336987 2856667 := bstep (se 1 (by rfl) ⟨2142500, by rfl⟩ : syracuseStep 2856667 = 4285001) B4285001
theorem B3389161 : Blo 1336987 3389161 := bstep (se 2 (by rfl) ⟨1270935, by rfl⟩ : syracuseStep 3389161 = 2541871) B2541871
theorem B2258671 : Blo 1336987 2258671 := bstep (se 1 (by rfl) ⟨1694003, by rfl⟩ : syracuseStep 2258671 = 3388007) B3388007
theorem B3012335 : Blo 1336987 3012335 := bstep (se 1 (by rfl) ⟨2259251, by rfl⟩ : syracuseStep 3012335 = 4518503) B4518503
theorem B123655987 : Blo 1336987 123655987 := bstep (se 1 (by rfl) ⟨92741990, by rfl⟩ : syracuseStep 123655987 = 185483981) B185483981
theorem B6772571 : Blo 1336987 6772571 := bstep (se 1 (by rfl) ⟨5079428, by rfl⟩ : syracuseStep 6772571 = 10158857) B10158857
theorem B3012551 : Blo 1336987 3012551 := bstep (se 1 (by rfl) ⟨2259413, by rfl⟩ : syracuseStep 3012551 = 4518827) B4518827
theorem B1505695 : Blo 1336987 1505695 := bstep (se 1 (by rfl) ⟨1129271, by rfl⟩ : syracuseStep 1505695 = 2258543) B2258543
theorem B2259407 : Blo 1336987 2259407 := bstep (se 1 (by rfl) ⟨1694555, by rfl⟩ : syracuseStep 2259407 = 3389111) B3389111
theorem B1505767 : Blo 1336987 1505767 := bstep (se 1 (by rfl) ⟨1129325, by rfl⟩ : syracuseStep 1505767 = 2258651) B2258651
theorem B2005481 : Blo 1336987 2005481 := bstep (se 2 (by rfl) ⟨752055, by rfl⟩ : syracuseStep 2005481 = 1504111) B1504111
theorem B23182033 : Blo 1336987 23182033 := bstep (se 2 (by rfl) ⟨8693262, by rfl⟩ : syracuseStep 23182033 = 17386525) B17386525
theorem B2538287 : Blo 1336987 2538287 := bstep (se 1 (by rfl) ⟨1903715, by rfl⟩ : syracuseStep 2538287 = 3807431) B3807431
theorem B2005871 : Blo 1336987 2005871 := bstep (se 1 (by rfl) ⟨1504403, by rfl⟩ : syracuseStep 2005871 = 3008807) B3008807
theorem B2005883 : Blo 1336987 2005883 := bstep (se 1 (by rfl) ⟨1504412, by rfl⟩ : syracuseStep 2005883 = 3008825) B3008825
theorem B4578401 : Blo 1336987 4578401 := bstep (se 2 (by rfl) ⟨1716900, by rfl⟩ : syracuseStep 4578401 = 3433801) B3433801
theorem B10444321 : Blo 1336987 10444321 := bstep (se 2 (by rfl) ⟨3916620, by rfl⟩ : syracuseStep 10444321 = 7833241) B7833241
theorem B5078639 : Blo 1336987 5078639 := bstep (se 1 (by rfl) ⟨3808979, by rfl⟩ : syracuseStep 5078639 = 7617959) B7617959
theorem B2539183 : Blo 1336987 2539183 := bstep (se 1 (by rfl) ⟨1904387, by rfl⟩ : syracuseStep 2539183 = 3808775) B3808775
theorem B2006747 : Blo 1336987 2006747 := bstep (se 1 (by rfl) ⟨1505060, by rfl⟩ : syracuseStep 2006747 = 3010121) B3010121
theorem B16269025 : Blo 1336987 16269025 := bstep (se 2 (by rfl) ⟨6100884, by rfl⟩ : syracuseStep 16269025 = 12201769) B12201769
theorem B329408309 : Blo 1336987 329408309 := bstep (se 5 (by rfl) ⟨15441014, by rfl⟩ : syracuseStep 329408309 = 30882029) B30882029
theorem B2539343 : Blo 1336987 2539343 := bstep (se 1 (by rfl) ⟨1904507, by rfl⟩ : syracuseStep 2539343 = 3809015) B3809015
theorem B3809231 : Blo 1336987 3809231 := bstep (se 1 (by rfl) ⟨2856923, by rfl⟩ : syracuseStep 3809231 = 5713847) B5713847
theorem B2007017 : Blo 1336987 2007017 := bstep (se 2 (by rfl) ⟨752631, by rfl⟩ : syracuseStep 2007017 = 1505263) B1505263
theorem B11436065 : Blo 1336987 11436065 := bstep (se 2 (by rfl) ⟨4288524, by rfl⟩ : syracuseStep 11436065 = 8577049) B8577049
theorem B2007095 : Blo 1336987 2007095 := bstep (se 1 (by rfl) ⟨1505321, by rfl⟩ : syracuseStep 2007095 = 3010643) B3010643
theorem B2007215 : Blo 1336987 2007215 := bstep (se 1 (by rfl) ⟨1505411, by rfl⟩ : syracuseStep 2007215 = 3010823) B3010823
theorem B5079293 : Blo 1336987 5079293 := bstep (se 3 (by rfl) ⟨952367, by rfl⟩ : syracuseStep 5079293 = 1904735) B1904735
theorem B2007419 : Blo 1336987 2007419 := bstep (se 1 (by rfl) ⟨1505564, by rfl⟩ : syracuseStep 2007419 = 3011129) B3011129
theorem B3809663 : Blo 1336987 3809663 := bstep (se 1 (by rfl) ⟨2857247, by rfl⟩ : syracuseStep 3809663 = 5714495) B5714495
theorem B2007593 : Blo 1336987 2007593 := bstep (se 2 (by rfl) ⟨752847, by rfl⟩ : syracuseStep 2007593 = 1505695) B1505695
theorem B30884449 : Blo 1336987 30884449 := bstep (se 2 (by rfl) ⟨11581668, by rfl⟩ : syracuseStep 30884449 = 23163337) B23163337
theorem B2007689 : Blo 1336987 2007689 := bstep (se 2 (by rfl) ⟨752883, by rfl⟩ : syracuseStep 2007689 = 1505767) B1505767
theorem B2007899 : Blo 1336987 2007899 := bstep (se 1 (by rfl) ⟨1505924, by rfl⟩ : syracuseStep 2007899 = 3011849) B3011849
theorem B2007935 : Blo 1336987 2007935 := bstep (se 1 (by rfl) ⟨1505951, by rfl⟩ : syracuseStep 2007935 = 3011903) B3011903
theorem B30909377 : Blo 1336987 30909377 := bstep (se 2 (by rfl) ⟨11591016, by rfl⟩ : syracuseStep 30909377 = 23182033) B23182033
theorem B2008007 : Blo 1336987 2008007 := bstep (se 1 (by rfl) ⟨1506005, by rfl⟩ : syracuseStep 2008007 = 3012011) B3012011
theorem B2008223 : Blo 1336987 2008223 := bstep (se 1 (by rfl) ⟨1506167, by rfl⟩ : syracuseStep 2008223 = 3012335) B3012335
theorem B2712737 : Blo 1336987 2712737 := bstep (se 2 (by rfl) ⟨1017276, by rfl⟩ : syracuseStep 2712737 = 2034553) B2034553
theorem B4515047 : Blo 1336987 4515047 := bstep (se 1 (by rfl) ⟨3386285, by rfl⟩ : syracuseStep 4515047 = 6772571) B6772571
theorem B2008367 : Blo 1336987 2008367 := bstep (se 1 (by rfl) ⟨1506275, by rfl⟩ : syracuseStep 2008367 = 3012551) B3012551
theorem B1336987 : Blo 1336987 1336987 := bstep (se 1 (by rfl) ⟨1002740, by rfl⟩ : syracuseStep 1336987 = 2005481) B2005481
theorem B29329249 : Blo 1336987 29329249 := bstep (se 2 (by rfl) ⟨10998468, by rfl⟩ : syracuseStep 29329249 = 21996937) B21996937
theorem B6768521 : Blo 1336987 6768521 := bstep (se 2 (by rfl) ⟨2538195, by rfl⟩ : syracuseStep 6768521 = 5076391) B5076391
theorem B1337247 : Blo 1336987 1337247 := bstep (se 1 (by rfl) ⟨1002935, by rfl⟩ : syracuseStep 1337247 = 2005871) B2005871
theorem B1337255 : Blo 1336987 1337255 := bstep (se 1 (by rfl) ⟨1002941, by rfl⟩ : syracuseStep 1337255 = 2005883) B2005883
theorem B3385577 : Blo 1336987 3385577 := bstep (se 2 (by rfl) ⟨1269591, by rfl⟩ : syracuseStep 3385577 = 2539183) B2539183
theorem B10848491 : Blo 1336987 10848491 := bstep (se 1 (by rfl) ⟨8136368, by rfl⟩ : syracuseStep 10848491 = 16272737) B16272737
theorem B164874649 : Blo 1336987 164874649 := bstep (se 2 (by rfl) ⟨61827993, by rfl⟩ : syracuseStep 164874649 = 123655987) B123655987
theorem B3385759 : Blo 1336987 3385759 := bstep (se 1 (by rfl) ⟨2539319, by rfl⟩ : syracuseStep 3385759 = 5078639) B5078639
theorem B1337831 : Blo 1336987 1337831 := bstep (se 1 (by rfl) ⟨1003373, by rfl⟩ : syracuseStep 1337831 = 2006747) B2006747
theorem B219605539 : Blo 1336987 219605539 := bstep (se 1 (by rfl) ⟨164704154, by rfl⟩ : syracuseStep 219605539 = 329408309) B329408309
theorem B1338011 : Blo 1336987 1338011 := bstep (se 1 (by rfl) ⟨1003508, by rfl⟩ : syracuseStep 1338011 = 2007017) B2007017
theorem B2034335 : Blo 1336987 2034335 := bstep (se 1 (by rfl) ⟨1525751, by rfl⟩ : syracuseStep 2034335 = 3051503) B3051503
theorem B3009185 : Blo 1336987 3009185 := bstep (se 2 (by rfl) ⟨1128444, by rfl⟩ : syracuseStep 3009185 = 2256889) B2256889
theorem B3615599 : Blo 1336987 3615599 := bstep (se 1 (by rfl) ⟨2711699, by rfl⟩ : syracuseStep 3615599 = 5423399) B5423399
theorem B12209069 : Blo 1336987 12209069 := bstep (se 3 (by rfl) ⟨2289200, by rfl⟩ : syracuseStep 12209069 = 4578401) B4578401
theorem B41733083 : Blo 1336987 41733083 := bstep (se 1 (by rfl) ⟨31299812, by rfl⟩ : syracuseStep 41733083 = 62599625) B62599625
theorem B3009545 : Blo 1336987 3009545 := bstep (se 2 (by rfl) ⟨1128579, by rfl⟩ : syracuseStep 3009545 = 2257159) B2257159
theorem B5082209 : Blo 1336987 5082209 := bstep (se 2 (by rfl) ⟨1905828, by rfl⟩ : syracuseStep 5082209 = 3811657) B3811657
theorem B1338479 : Blo 1336987 1338479 := bstep (se 1 (by rfl) ⟨1003859, by rfl⟩ : syracuseStep 1338479 = 2007719) B2007719
theorem B1338559 : Blo 1336987 1338559 := bstep (se 1 (by rfl) ⟨1003919, by rfl⟩ : syracuseStep 1338559 = 2007839) B2007839
theorem B3009743 : Blo 1336987 3009743 := bstep (se 1 (by rfl) ⟨2257307, by rfl⟩ : syracuseStep 3009743 = 4514615) B4514615
theorem B1338575 : Blo 1336987 1338575 := bstep (se 1 (by rfl) ⟨1003931, by rfl⟩ : syracuseStep 1338575 = 2007863) B2007863
theorem B6425885 : Blo 1336987 6425885 := bstep (se 3 (by rfl) ⟨1204853, by rfl⟩ : syracuseStep 6425885 = 2409707) B2409707
theorem B22867271 : Blo 1336987 22867271 := bstep (se 1 (by rfl) ⟨17150453, by rfl⟩ : syracuseStep 22867271 = 34300907) B34300907
theorem B1338695 : Blo 1336987 1338695 := bstep (se 1 (by rfl) ⟨1004021, by rfl⟩ : syracuseStep 1338695 = 2008043) B2008043
theorem B15666635 : Blo 1336987 15666635 := bstep (se 1 (by rfl) ⟨11749976, by rfl⟩ : syracuseStep 15666635 = 23499953) B23499953
theorem B3387167 : Blo 1336987 3387167 := bstep (se 1 (by rfl) ⟨2540375, by rfl⟩ : syracuseStep 3387167 = 5080751) B5080751
theorem B3010535 : Blo 1336987 3010535 := bstep (se 1 (by rfl) ⟨2257901, by rfl⟩ : syracuseStep 3010535 = 4515803) B4515803
theorem B4288639 : Blo 1336987 4288639 := bstep (se 1 (by rfl) ⟨3216479, by rfl⟩ : syracuseStep 4288639 = 6432959) B6432959
theorem B3010715 : Blo 1336987 3010715 := bstep (se 1 (by rfl) ⟨2258036, by rfl⟩ : syracuseStep 3010715 = 4516073) B4516073
theorem B3010895 : Blo 1336987 3010895 := bstep (se 1 (by rfl) ⟨2258171, by rfl⟩ : syracuseStep 3010895 = 4516343) B4516343
theorem B3010913 : Blo 1336987 3010913 := bstep (se 2 (by rfl) ⟨1129092, by rfl⟩ : syracuseStep 3010913 = 2258185) B2258185
theorem B3010985 : Blo 1336987 3010985 := bstep (se 2 (by rfl) ⟨1129119, by rfl⟩ : syracuseStep 3010985 = 2258239) B2258239
theorem B3011003 : Blo 1336987 3011003 := bstep (se 1 (by rfl) ⟨2258252, by rfl⟩ : syracuseStep 3011003 = 4516505) B4516505
theorem B1692191 : Blo 1336987 1692191 := bstep (se 1 (by rfl) ⟨1269143, by rfl⟩ : syracuseStep 1692191 = 2538287) B2538287
theorem B3011291 : Blo 1336987 3011291 := bstep (se 1 (by rfl) ⟨2258468, by rfl⟩ : syracuseStep 3011291 = 4516937) B4516937
theorem B17134415 : Blo 1336987 17134415 := bstep (se 1 (by rfl) ⟨12850811, by rfl⟩ : syracuseStep 17134415 = 25701623) B25701623
theorem B2143135 : Blo 1336987 2143135 := bstep (se 1 (by rfl) ⟨1607351, by rfl⟩ : syracuseStep 2143135 = 3214703) B3214703
theorem B4518881 : Blo 1336987 4518881 := bstep (se 2 (by rfl) ⟨1694580, by rfl⟩ : syracuseStep 4518881 = 3389161) B3389161
theorem B3011561 : Blo 1336987 3011561 := bstep (se 2 (by rfl) ⟨1129335, by rfl⟩ : syracuseStep 3011561 = 2258671) B2258671
theorem B1692895 : Blo 1336987 1692895 := bstep (se 1 (by rfl) ⟨1269671, by rfl⟩ : syracuseStep 1692895 = 2539343) B2539343
theorem B2856359 : Blo 1336987 2856359 := bstep (se 1 (by rfl) ⟨2142269, by rfl⟩ : syracuseStep 2856359 = 4284539) B4284539
theorem B17372603 : Blo 1336987 17372603 := bstep (se 1 (by rfl) ⟨13029452, by rfl⟩ : syracuseStep 17372603 = 26058905) B26058905
theorem B8574407 : Blo 1336987 8574407 := bstep (se 1 (by rfl) ⟨6430805, by rfl⟩ : syracuseStep 8574407 = 12861611) B12861611
theorem B55703045 : Blo 1336987 55703045 := bstep (se 4 (by rfl) ⟨5222160, by rfl⟩ : syracuseStep 55703045 = 10444321) B10444321
theorem B6428231 : Blo 1336987 6428231 := bstep (se 1 (by rfl) ⟨4821173, by rfl⟩ : syracuseStep 6428231 = 9642347) B9642347
theorem B1906267 : Blo 1336987 1906267 := bstep (se 1 (by rfl) ⟨1429700, by rfl⟩ : syracuseStep 1906267 = 2859401) B2859401
theorem B3012263 : Blo 1336987 3012263 := bstep (se 1 (by rfl) ⟨2259197, by rfl⟩ : syracuseStep 3012263 = 4518395) B4518395
theorem B3012443 : Blo 1336987 3012443 := bstep (se 1 (by rfl) ⟨2259332, by rfl⟩ : syracuseStep 3012443 = 4518665) B4518665
theorem B12867761 : Blo 1336987 12867761 := bstep (se 2 (by rfl) ⟨4825410, by rfl⟩ : syracuseStep 12867761 = 9650821) B9650821
theorem B21993769 : Blo 1336987 21993769 := bstep (se 2 (by rfl) ⟨8247663, by rfl⟩ : syracuseStep 21993769 = 16495327) B16495327
theorem B34773299 : Blo 1336987 34773299 := bstep (se 1 (by rfl) ⟨26079974, by rfl⟩ : syracuseStep 34773299 = 52159949) B52159949
theorem B5151073 : Blo 1336987 5151073 := bstep (se 2 (by rfl) ⟨1931652, by rfl⟩ : syracuseStep 5151073 = 3863305) B3863305
theorem B4577663 : Blo 1336987 4577663 := bstep (se 1 (by rfl) ⟨3433247, by rfl⟩ : syracuseStep 4577663 = 6866495) B6866495
theorem B9640417 : Blo 1336987 9640417 := bstep (se 2 (by rfl) ⟨3615156, by rfl⟩ : syracuseStep 9640417 = 7230313) B7230313
theorem B2005595 : Blo 1336987 2005595 := bstep (se 1 (by rfl) ⟨1504196, by rfl⟩ : syracuseStep 2005595 = 3008393) B3008393
theorem B2005607 : Blo 1336987 2005607 := bstep (se 1 (by rfl) ⟨1504205, by rfl⟩ : syracuseStep 2005607 = 3008411) B3008411
theorem B2005631 : Blo 1336987 2005631 := bstep (se 1 (by rfl) ⟨1504223, by rfl⟩ : syracuseStep 2005631 = 3008447) B3008447
theorem B2005739 : Blo 1336987 2005739 := bstep (se 1 (by rfl) ⟨1504304, by rfl⟩ : syracuseStep 2005739 = 3008609) B3008609
theorem B2005769 : Blo 1336987 2005769 := bstep (se 2 (by rfl) ⟨752163, by rfl⟩ : syracuseStep 2005769 = 1504327) B1504327
theorem B6773543 : Blo 1336987 6773543 := bstep (se 1 (by rfl) ⟨5080157, by rfl⟩ : syracuseStep 6773543 = 10160315) B10160315
theorem B1506271 : Blo 1336987 1506271 := bstep (se 1 (by rfl) ⟨1129703, by rfl⟩ : syracuseStep 1506271 = 2259407) B2259407
theorem B2006009 : Blo 1336987 2006009 := bstep (se 2 (by rfl) ⟨752253, by rfl⟩ : syracuseStep 2006009 = 1504507) B1504507
theorem B8576047 : Blo 1336987 8576047 := bstep (se 1 (by rfl) ⟨6432035, by rfl⟩ : syracuseStep 8576047 = 12864071) B12864071
theorem B4283873 : Blo 1336987 4283873 := bstep (se 2 (by rfl) ⟨1606452, by rfl⟩ : syracuseStep 4283873 = 3212905) B3212905
theorem B2006639 : Blo 1336987 2006639 := bstep (se 1 (by rfl) ⟨1504979, by rfl⟩ : syracuseStep 2006639 = 3009959) B3009959
theorem B3808889 : Blo 1336987 3808889 := bstep (se 2 (by rfl) ⟨1428333, by rfl⟩ : syracuseStep 3808889 = 2856667) B2856667
theorem B21692033 : Blo 1336987 21692033 := bstep (se 2 (by rfl) ⟨8134512, by rfl⟩ : syracuseStep 21692033 = 16269025) B16269025
theorem B8134319 : Blo 1336987 8134319 := bstep (se 1 (by rfl) ⟨6100739, by rfl⟩ : syracuseStep 8134319 = 12201479) B12201479
theorem B2006759 : Blo 1336987 2006759 := bstep (se 1 (by rfl) ⟨1505069, by rfl⟩ : syracuseStep 2006759 = 3010139) B3010139
theorem B15449849 : Blo 1336987 15449849 := bstep (se 2 (by rfl) ⟨5793693, by rfl⟩ : syracuseStep 15449849 = 11587387) B11587387
theorem B2539487 : Blo 1336987 2539487 := bstep (se 1 (by rfl) ⟨1904615, by rfl⟩ : syracuseStep 2539487 = 3809231) B3809231
theorem B2007035 : Blo 1336987 2007035 := bstep (se 1 (by rfl) ⟨1505276, by rfl⟩ : syracuseStep 2007035 = 3010553) B3010553
theorem B2007143 : Blo 1336987 2007143 := bstep (se 1 (by rfl) ⟨1505357, by rfl⟩ : syracuseStep 2007143 = 3010715) B3010715
theorem B5718185 : Blo 1336987 5718185 := bstep (se 2 (by rfl) ⟨2144319, by rfl⟩ : syracuseStep 5718185 = 4288639) B4288639
theorem B2007263 : Blo 1336987 2007263 := bstep (se 1 (by rfl) ⟨1505447, by rfl⟩ : syracuseStep 2007263 = 3010895) B3010895
theorem B2007275 : Blo 1336987 2007275 := bstep (se 1 (by rfl) ⟨1505456, by rfl⟩ : syracuseStep 2007275 = 3010913) B3010913
theorem B2539775 : Blo 1336987 2539775 := bstep (se 1 (by rfl) ⟨1904831, by rfl⟩ : syracuseStep 2539775 = 3809663) B3809663
theorem B2007323 : Blo 1336987 2007323 := bstep (se 1 (by rfl) ⟨1505492, by rfl⟩ : syracuseStep 2007323 = 3010985) B3010985
theorem B2007335 : Blo 1336987 2007335 := bstep (se 1 (by rfl) ⟨1505501, by rfl⟩ : syracuseStep 2007335 = 3011003) B3011003
theorem B7233965 : Blo 1336987 7233965 := bstep (se 3 (by rfl) ⟨1356368, by rfl⟩ : syracuseStep 7233965 = 2712737) B2712737
theorem B2007527 : Blo 1336987 2007527 := bstep (se 1 (by rfl) ⟨1505645, by rfl⟩ : syracuseStep 2007527 = 3011291) B3011291
theorem B219832865 : Blo 1336987 219832865 := bstep (se 2 (by rfl) ⟨82437324, by rfl⟩ : syracuseStep 219832865 = 164874649) B164874649
theorem B4514345 : Blo 1336987 4514345 := bstep (se 2 (by rfl) ⟨1692879, by rfl⟩ : syracuseStep 4514345 = 3385759) B3385759
theorem B12853889 : Blo 1336987 12853889 := bstep (se 2 (by rfl) ⟨4820208, by rfl⟩ : syracuseStep 12853889 = 9640417) B9640417
theorem B2007707 : Blo 1336987 2007707 := bstep (se 1 (by rfl) ⟨1505780, by rfl⟩ : syracuseStep 2007707 = 3011561) B3011561
theorem B292807385 : Blo 1336987 292807385 := bstep (se 2 (by rfl) ⟨109802769, by rfl⟩ : syracuseStep 292807385 = 219605539) B219605539
theorem B37135363 : Blo 1336987 37135363 := bstep (se 1 (by rfl) ⟨27851522, by rfl⟩ : syracuseStep 37135363 = 55703045) B55703045
theorem B4285487 : Blo 1336987 4285487 := bstep (se 1 (by rfl) ⟨3214115, by rfl⟩ : syracuseStep 4285487 = 6428231) B6428231
theorem B2008175 : Blo 1336987 2008175 := bstep (se 1 (by rfl) ⟨1506131, by rfl⟩ : syracuseStep 2008175 = 3012263) B3012263
theorem B46326941 : Blo 1336987 46326941 := bstep (se 3 (by rfl) ⟨8686301, by rfl⟩ : syracuseStep 46326941 = 17372603) B17372603
theorem B2008295 : Blo 1336987 2008295 := bstep (se 1 (by rfl) ⟨1506221, by rfl⟩ : syracuseStep 2008295 = 3012443) B3012443
theorem B2008361 : Blo 1336987 2008361 := bstep (se 2 (by rfl) ⟨753135, by rfl⟩ : syracuseStep 2008361 = 1506271) B1506271
theorem B1337063 : Blo 1336987 1337063 := bstep (se 1 (by rfl) ⟨1002797, by rfl⟩ : syracuseStep 1337063 = 2005595) B2005595
theorem B1337071 : Blo 1336987 1337071 := bstep (se 1 (by rfl) ⟨1002803, by rfl⟩ : syracuseStep 1337071 = 2005607) B2005607
theorem B5424893 : Blo 1336987 5424893 := bstep (se 3 (by rfl) ⟨1017167, by rfl⟩ : syracuseStep 5424893 = 2034335) B2034335
theorem B1337087 : Blo 1336987 1337087 := bstep (se 1 (by rfl) ⟨1002815, by rfl⟩ : syracuseStep 1337087 = 2005631) B2005631
theorem B1337159 : Blo 1336987 1337159 := bstep (se 1 (by rfl) ⟨1002869, by rfl⟩ : syracuseStep 1337159 = 2005739) B2005739
theorem B1337179 : Blo 1336987 1337179 := bstep (se 1 (by rfl) ⟨1002884, by rfl⟩ : syracuseStep 1337179 = 2005769) B2005769
theorem B4515695 : Blo 1336987 4515695 := bstep (se 1 (by rfl) ⟨3386771, by rfl⟩ : syracuseStep 4515695 = 6773543) B6773543
theorem B2410399 : Blo 1336987 2410399 := bstep (se 1 (by rfl) ⟨1807799, by rfl⟩ : syracuseStep 2410399 = 3615599) B3615599
theorem B27822055 : Blo 1336987 27822055 := bstep (se 1 (by rfl) ⟨20866541, by rfl⟩ : syracuseStep 27822055 = 41733083) B41733083
theorem B1337339 : Blo 1336987 1337339 := bstep (se 1 (by rfl) ⟨1003004, by rfl⟩ : syracuseStep 1337339 = 2006009) B2006009
theorem B2541689 : Blo 1336987 2541689 := bstep (se 2 (by rfl) ⟨953133, by rfl⟩ : syracuseStep 2541689 = 1906267) B1906267
theorem B1337759 : Blo 1336987 1337759 := bstep (se 1 (by rfl) ⟨1003319, by rfl⟩ : syracuseStep 1337759 = 2006639) B2006639
theorem B14461355 : Blo 1336987 14461355 := bstep (se 1 (by rfl) ⟨10846016, by rfl⟩ : syracuseStep 14461355 = 21692033) B21692033
theorem B1337839 : Blo 1336987 1337839 := bstep (se 1 (by rfl) ⟨1003379, by rfl⟩ : syracuseStep 1337839 = 2006759) B2006759
theorem B10299899 : Blo 1336987 10299899 := bstep (se 1 (by rfl) ⟨7724924, by rfl⟩ : syracuseStep 10299899 = 15449849) B15449849
theorem B1338023 : Blo 1336987 1338023 := bstep (se 1 (by rfl) ⟨1003517, by rfl⟩ : syracuseStep 1338023 = 2007035) B2007035
theorem B1338063 : Blo 1336987 1338063 := bstep (se 1 (by rfl) ⟨1003547, by rfl⟩ : syracuseStep 1338063 = 2007095) B2007095
theorem B1338143 : Blo 1336987 1338143 := bstep (se 1 (by rfl) ⟨1003607, by rfl⟩ : syracuseStep 1338143 = 2007215) B2007215
theorem B3386195 : Blo 1336987 3386195 := bstep (se 1 (by rfl) ⟨2539646, by rfl⟩ : syracuseStep 3386195 = 5079293) B5079293
theorem B1338279 : Blo 1336987 1338279 := bstep (se 1 (by rfl) ⟨1003709, by rfl⟩ : syracuseStep 1338279 = 2007419) B2007419
theorem B1338395 : Blo 1336987 1338395 := bstep (se 1 (by rfl) ⟨1003796, by rfl⟩ : syracuseStep 1338395 = 2007593) B2007593
theorem B1338459 : Blo 1336987 1338459 := bstep (se 1 (by rfl) ⟨1003844, by rfl⟩ : syracuseStep 1338459 = 2007689) B2007689
theorem B6868097 : Blo 1336987 6868097 := bstep (se 2 (by rfl) ⟨2575536, by rfl⟩ : syracuseStep 6868097 = 5151073) B5151073
theorem B11422943 : Blo 1336987 11422943 := bstep (se 1 (by rfl) ⟨8567207, by rfl⟩ : syracuseStep 11422943 = 17134415) B17134415
theorem B1338599 : Blo 1336987 1338599 := bstep (se 1 (by rfl) ⟨1003949, by rfl⟩ : syracuseStep 1338599 = 2007899) B2007899
theorem B1338623 : Blo 1336987 1338623 := bstep (se 1 (by rfl) ⟨1003967, by rfl⟩ : syracuseStep 1338623 = 2007935) B2007935
theorem B20606251 : Blo 1336987 20606251 := bstep (se 1 (by rfl) ⟨15454688, by rfl⟩ : syracuseStep 20606251 = 30909377) B30909377
theorem B1338671 : Blo 1336987 1338671 := bstep (se 1 (by rfl) ⟨1004003, by rfl⟩ : syracuseStep 1338671 = 2008007) B2008007
theorem B1338815 : Blo 1336987 1338815 := bstep (se 1 (by rfl) ⟨1004111, by rfl⟩ : syracuseStep 1338815 = 2008223) B2008223
theorem B3010031 : Blo 1336987 3010031 := bstep (se 1 (by rfl) ⟨2257523, by rfl⟩ : syracuseStep 3010031 = 4515047) B4515047
theorem B1338911 : Blo 1336987 1338911 := bstep (se 1 (by rfl) ⟨1004183, by rfl⟩ : syracuseStep 1338911 = 2008367) B2008367
theorem B1904239 : Blo 1336987 1904239 := bstep (se 1 (by rfl) ⟨1428179, by rfl⟩ : syracuseStep 1904239 = 2856359) B2856359
theorem B2257051 : Blo 1336987 2257051 := bstep (se 1 (by rfl) ⟨1692788, by rfl⟩ : syracuseStep 2257051 = 3385577) B3385577
theorem B3051775 : Blo 1336987 3051775 := bstep (se 1 (by rfl) ⟨2288831, by rfl⟩ : syracuseStep 3051775 = 4577663) B4577663
theorem B2257193 : Blo 1336987 2257193 := bstep (se 2 (by rfl) ⟨846447, by rfl⟩ : syracuseStep 2257193 = 1692895) B1692895
theorem B8139379 : Blo 1336987 8139379 := bstep (se 1 (by rfl) ⟨6104534, by rfl⟩ : syracuseStep 8139379 = 12209069) B12209069
theorem B3388139 : Blo 1336987 3388139 := bstep (se 1 (by rfl) ⟨2541104, by rfl⟩ : syracuseStep 3388139 = 5082209) B5082209
theorem B2855915 : Blo 1336987 2855915 := bstep (se 1 (by rfl) ⟨2141936, by rfl⟩ : syracuseStep 2855915 = 4283873) B4283873
theorem B39105665 : Blo 1336987 39105665 := bstep (se 2 (by rfl) ⟨14664624, by rfl⟩ : syracuseStep 39105665 = 29329249) B29329249
theorem B2258111 : Blo 1336987 2258111 := bstep (se 1 (by rfl) ⟨1693583, by rfl⟩ : syracuseStep 2258111 = 3387167) B3387167
theorem B1692991 : Blo 1336987 1692991 := bstep (se 1 (by rfl) ⟨1269743, by rfl⟩ : syracuseStep 1692991 = 2539487) B2539487
theorem B7624043 : Blo 1336987 7624043 := bstep (se 1 (by rfl) ⟨5718032, by rfl⟩ : syracuseStep 7624043 = 11436065) B11436065
theorem B29325025 : Blo 1336987 29325025 := bstep (se 2 (by rfl) ⟨10996884, by rfl⟩ : syracuseStep 29325025 = 21993769) B21993769
theorem B34314029 : Blo 1336987 34314029 := bstep (se 3 (by rfl) ⟨6433880, by rfl⟩ : syracuseStep 34314029 = 12867761) B12867761
theorem B3012587 : Blo 1336987 3012587 := bstep (se 1 (by rfl) ⟨2259440, by rfl⟩ : syracuseStep 3012587 = 4518881) B4518881
theorem B41179265 : Blo 1336987 41179265 := bstep (se 2 (by rfl) ⟨15442224, by rfl⟩ : syracuseStep 41179265 = 30884449) B30884449
theorem B5716271 : Blo 1336987 5716271 := bstep (se 1 (by rfl) ⟨4287203, by rfl⟩ : syracuseStep 5716271 = 8574407) B8574407
theorem B41777693 : Blo 1336987 41777693 := bstep (se 3 (by rfl) ⟨7833317, by rfl⟩ : syracuseStep 41777693 = 15666635) B15666635
theorem B2857513 : Blo 1336987 2857513 := bstep (se 2 (by rfl) ⟨1071567, by rfl⟩ : syracuseStep 2857513 = 2143135) B2143135
theorem B4512347 : Blo 1336987 4512347 := bstep (se 1 (by rfl) ⟨3384260, by rfl⟩ : syracuseStep 4512347 = 6768521) B6768521
theorem B11434729 : Blo 1336987 11434729 := bstep (se 2 (by rfl) ⟨4288023, by rfl⟩ : syracuseStep 11434729 = 8576047) B8576047
theorem B4512509 : Blo 1336987 4512509 := bstep (se 3 (by rfl) ⟨846095, by rfl⟩ : syracuseStep 4512509 = 1692191) B1692191
theorem B7232327 : Blo 1336987 7232327 := bstep (se 1 (by rfl) ⟨5424245, by rfl⟩ : syracuseStep 7232327 = 10848491) B10848491
theorem B23182199 : Blo 1336987 23182199 := bstep (se 1 (by rfl) ⟨17386649, by rfl⟩ : syracuseStep 23182199 = 34773299) B34773299
theorem B2006123 : Blo 1336987 2006123 := bstep (se 1 (by rfl) ⟨1504592, by rfl⟩ : syracuseStep 2006123 = 3009185) B3009185
theorem B2006363 : Blo 1336987 2006363 := bstep (se 1 (by rfl) ⟨1504772, by rfl⟩ : syracuseStep 2006363 = 3009545) B3009545
theorem B2006495 : Blo 1336987 2006495 := bstep (se 1 (by rfl) ⟨1504871, by rfl⟩ : syracuseStep 2006495 = 3009743) B3009743
theorem B4283923 : Blo 1336987 4283923 := bstep (se 1 (by rfl) ⟨3212942, by rfl⟩ : syracuseStep 4283923 = 6425885) B6425885
theorem B15244847 : Blo 1336987 15244847 := bstep (se 1 (by rfl) ⟨11433635, by rfl⟩ : syracuseStep 15244847 = 22867271) B22867271
theorem B2539259 : Blo 1336987 2539259 := bstep (se 1 (by rfl) ⟨1904444, by rfl⟩ : syracuseStep 2539259 = 3808889) B3808889
theorem B5422879 : Blo 1336987 5422879 := bstep (se 1 (by rfl) ⟨4067159, by rfl⟩ : syracuseStep 5422879 = 8134319) B8134319
theorem B2007023 : Blo 1336987 2007023 := bstep (se 1 (by rfl) ⟨1505267, by rfl⟩ : syracuseStep 2007023 = 3010535) B3010535
theorem B11427965 : Blo 1336987 11427965 := bstep (se 3 (by rfl) ⟨2142743, by rfl⟩ : syracuseStep 11427965 = 4285487) B4285487
theorem B146555243 : Blo 1336987 146555243 := bstep (se 1 (by rfl) ⟨109916432, by rfl⟩ : syracuseStep 146555243 = 219832865) B219832865
theorem B8569259 : Blo 1336987 8569259 := bstep (se 1 (by rfl) ⟨6426944, by rfl⟩ : syracuseStep 8569259 = 12853889) B12853889
theorem B3810017 : Blo 1336987 3810017 := bstep (se 2 (by rfl) ⟨1428756, by rfl⟩ : syracuseStep 3810017 = 2857513) B2857513
theorem B30884627 : Blo 1336987 30884627 := bstep (se 1 (by rfl) ⟨23163470, by rfl⟩ : syracuseStep 30884627 = 46326941) B46326941
theorem B15246305 : Blo 1336987 15246305 := bstep (se 2 (by rfl) ⟨5717364, by rfl⟩ : syracuseStep 15246305 = 11434729) B11434729
theorem B2008391 : Blo 1336987 2008391 := bstep (se 1 (by rfl) ⟨1506293, by rfl⟩ : syracuseStep 2008391 = 3012587) B3012587
theorem B49513817 : Blo 1336987 49513817 := bstep (se 2 (by rfl) ⟨18567681, by rfl⟩ : syracuseStep 49513817 = 37135363) B37135363
theorem B27452843 : Blo 1336987 27452843 := bstep (se 1 (by rfl) ⟨20589632, by rfl⟩ : syracuseStep 27452843 = 41179265) B41179265
theorem B3008231 : Blo 1336987 3008231 := bstep (se 1 (by rfl) ⟨2256173, by rfl⟩ : syracuseStep 3008231 = 4512347) B4512347
theorem B3008339 : Blo 1336987 3008339 := bstep (se 1 (by rfl) ⟨2256254, by rfl⟩ : syracuseStep 3008339 = 4512509) B4512509
theorem B5711897 : Blo 1336987 5711897 := bstep (se 2 (by rfl) ⟨2141961, by rfl⟩ : syracuseStep 5711897 = 4283923) B4283923
theorem B1337415 : Blo 1336987 1337415 := bstep (se 1 (by rfl) ⟨1003061, by rfl⟩ : syracuseStep 1337415 = 2006123) B2006123
theorem B1337575 : Blo 1336987 1337575 := bstep (se 1 (by rfl) ⟨1003181, by rfl⟩ : syracuseStep 1337575 = 2006363) B2006363
theorem B1337663 : Blo 1336987 1337663 := bstep (se 1 (by rfl) ⟨1003247, by rfl⟩ : syracuseStep 1337663 = 2006495) B2006495
theorem B3213865 : Blo 1336987 3213865 := bstep (se 2 (by rfl) ⟨1205199, by rfl⟩ : syracuseStep 3213865 = 2410399) B2410399
theorem B37096073 : Blo 1336987 37096073 := bstep (se 2 (by rfl) ⟨13911027, by rfl⟩ : syracuseStep 37096073 = 27822055) B27822055
theorem B1338015 : Blo 1336987 1338015 := bstep (se 1 (by rfl) ⟨1003511, by rfl⟩ : syracuseStep 1338015 = 2007023) B2007023
theorem B1338095 : Blo 1336987 1338095 := bstep (se 1 (by rfl) ⟨1003571, by rfl⟩ : syracuseStep 1338095 = 2007143) B2007143
theorem B3812123 : Blo 1336987 3812123 := bstep (se 1 (by rfl) ⟨2859092, by rfl⟩ : syracuseStep 3812123 = 5718185) B5718185
theorem B1338175 : Blo 1336987 1338175 := bstep (se 1 (by rfl) ⟨1003631, by rfl⟩ : syracuseStep 1338175 = 2007263) B2007263
theorem B1338183 : Blo 1336987 1338183 := bstep (se 1 (by rfl) ⟨1003637, by rfl⟩ : syracuseStep 1338183 = 2007275) B2007275
theorem B1338215 : Blo 1336987 1338215 := bstep (se 1 (by rfl) ⟨1003661, by rfl⟩ : syracuseStep 1338215 = 2007323) B2007323
theorem B1338223 : Blo 1336987 1338223 := bstep (se 1 (by rfl) ⟨1003667, by rfl⟩ : syracuseStep 1338223 = 2007335) B2007335
theorem B3009401 : Blo 1336987 3009401 := bstep (se 2 (by rfl) ⟨1128525, by rfl⟩ : syracuseStep 3009401 = 2257051) B2257051
theorem B1338351 : Blo 1336987 1338351 := bstep (se 1 (by rfl) ⟨1003763, by rfl⟩ : syracuseStep 1338351 = 2007527) B2007527
theorem B3009563 : Blo 1336987 3009563 := bstep (se 1 (by rfl) ⟨2257172, by rfl⟩ : syracuseStep 3009563 = 4514345) B4514345
theorem B1338471 : Blo 1336987 1338471 := bstep (se 1 (by rfl) ⟨1003853, by rfl⟩ : syracuseStep 1338471 = 2007707) B2007707
theorem B1903943 : Blo 1336987 1903943 := bstep (se 1 (by rfl) ⟨1427957, by rfl⟩ : syracuseStep 1903943 = 2855915) B2855915
theorem B1338783 : Blo 1336987 1338783 := bstep (se 1 (by rfl) ⟨1004087, by rfl⟩ : syracuseStep 1338783 = 2008175) B2008175
theorem B26070443 : Blo 1336987 26070443 := bstep (se 1 (by rfl) ⟨19552832, by rfl⟩ : syracuseStep 26070443 = 39105665) B39105665
theorem B1338863 : Blo 1336987 1338863 := bstep (se 1 (by rfl) ⟨1004147, by rfl⟩ : syracuseStep 1338863 = 2008295) B2008295
theorem B1338907 : Blo 1336987 1338907 := bstep (se 1 (by rfl) ⟨1004180, by rfl⟩ : syracuseStep 1338907 = 2008361) B2008361
theorem B5082695 : Blo 1336987 5082695 := bstep (se 1 (by rfl) ⟨3812021, by rfl⟩ : syracuseStep 5082695 = 7624043) B7624043
theorem B38563613 : Blo 1336987 38563613 := bstep (se 3 (by rfl) ⟨7230677, by rfl⟩ : syracuseStep 38563613 = 14461355) B14461355
theorem B3616595 : Blo 1336987 3616595 := bstep (se 1 (by rfl) ⟨2712446, by rfl⟩ : syracuseStep 3616595 = 5424893) B5424893
theorem B22876019 : Blo 1336987 22876019 := bstep (se 1 (by rfl) ⟨17157014, by rfl⟩ : syracuseStep 22876019 = 34314029) B34314029
theorem B3010463 : Blo 1336987 3010463 := bstep (se 1 (by rfl) ⟨2257847, by rfl⟩ : syracuseStep 3010463 = 4515695) B4515695
theorem B2257321 : Blo 1336987 2257321 := bstep (se 2 (by rfl) ⟨846495, by rfl⟩ : syracuseStep 2257321 = 1692991) B1692991
theorem B4821551 : Blo 1336987 4821551 := bstep (se 1 (by rfl) ⟨3616163, by rfl⟩ : syracuseStep 4821551 = 7232327) B7232327
theorem B2257463 : Blo 1336987 2257463 := bstep (se 1 (by rfl) ⟨1693097, by rfl⟩ : syracuseStep 2257463 = 3386195) B3386195
theorem B15454799 : Blo 1336987 15454799 := bstep (se 1 (by rfl) ⟨11591099, by rfl⟩ : syracuseStep 15454799 = 23182199) B23182199
theorem B7615295 : Blo 1336987 7615295 := bstep (se 1 (by rfl) ⟨5711471, by rfl⟩ : syracuseStep 7615295 = 11422943) B11422943
theorem B10163231 : Blo 1336987 10163231 := bstep (se 1 (by rfl) ⟨7622423, by rfl⟩ : syracuseStep 10163231 = 15244847) B15244847
theorem B7230505 : Blo 1336987 7230505 := bstep (se 2 (by rfl) ⟨2711439, by rfl⟩ : syracuseStep 7230505 = 5422879) B5422879
theorem B1692839 : Blo 1336987 1692839 := bstep (se 1 (by rfl) ⟨1269629, by rfl⟩ : syracuseStep 1692839 = 2539259) B2539259
theorem B1504795 : Blo 1336987 1504795 := bstep (se 1 (by rfl) ⟨1128596, by rfl⟩ : syracuseStep 1504795 = 2257193) B2257193
theorem B4822643 : Blo 1336987 4822643 := bstep (se 1 (by rfl) ⟨3616982, by rfl⟩ : syracuseStep 4822643 = 7233965) B7233965
theorem B195204923 : Blo 1336987 195204923 := bstep (se 1 (by rfl) ⟨146403692, by rfl⟩ : syracuseStep 195204923 = 292807385) B292807385
theorem B2258759 : Blo 1336987 2258759 := bstep (se 1 (by rfl) ⟨1694069, by rfl⟩ : syracuseStep 2258759 = 3388139) B3388139
theorem B10155941 : Blo 1336987 10155941 := bstep (se 4 (by rfl) ⟨952119, by rfl⟩ : syracuseStep 10155941 = 1904239) B1904239
theorem B6772733 : Blo 1336987 6772733 := bstep (se 3 (by rfl) ⟨1269887, by rfl⟩ : syracuseStep 6772733 = 2539775) B2539775
theorem B15243389 : Blo 1336987 15243389 := bstep (se 3 (by rfl) ⟨2858135, by rfl⟩ : syracuseStep 15243389 = 5716271) B5716271
theorem B1505407 : Blo 1336987 1505407 := bstep (se 1 (by rfl) ⟨1129055, by rfl⟩ : syracuseStep 1505407 = 2258111) B2258111
theorem B10852505 : Blo 1336987 10852505 := bstep (se 2 (by rfl) ⟨4069689, by rfl⟩ : syracuseStep 10852505 = 8139379) B8139379
theorem B27466397 : Blo 1336987 27466397 := bstep (se 3 (by rfl) ⟨5149949, by rfl⟩ : syracuseStep 27466397 = 10299899) B10299899
theorem B16276133 : Blo 1336987 16276133 := bstep (se 4 (by rfl) ⟨1525887, by rfl⟩ : syracuseStep 16276133 = 3051775) B3051775
theorem B1694459 : Blo 1336987 1694459 := bstep (se 1 (by rfl) ⟨1270844, by rfl⟩ : syracuseStep 1694459 = 2541689) B2541689
theorem B27851795 : Blo 1336987 27851795 := bstep (se 1 (by rfl) ⟨20888846, by rfl⟩ : syracuseStep 27851795 = 41777693) B41777693
theorem B27475001 : Blo 1336987 27475001 := bstep (se 2 (by rfl) ⟨10303125, by rfl⟩ : syracuseStep 27475001 = 20606251) B20606251
theorem B4578731 : Blo 1336987 4578731 := bstep (se 1 (by rfl) ⟨3434048, by rfl⟩ : syracuseStep 4578731 = 6868097) B6868097
theorem B39100033 : Blo 1336987 39100033 := bstep (se 2 (by rfl) ⟨14662512, by rfl⟩ : syracuseStep 39100033 = 29325025) B29325025
theorem B2006687 : Blo 1336987 2006687 := bstep (se 1 (by rfl) ⟨1505015, by rfl⟩ : syracuseStep 2006687 = 3010031) B3010031
theorem B7618643 : Blo 1336987 7618643 := bstep (se 1 (by rfl) ⟨5713982, by rfl⟩ : syracuseStep 7618643 = 11427965) B11427965
theorem B2007209 : Blo 1336987 2007209 := bstep (se 2 (by rfl) ⟨752703, by rfl⟩ : syracuseStep 2007209 = 1505407) B1505407
theorem B4514237 : Blo 1336987 4514237 := bstep (se 3 (by rfl) ⟨846419, by rfl⟩ : syracuseStep 4514237 = 1692839) B1692839
theorem B2540011 : Blo 1336987 2540011 := bstep (se 1 (by rfl) ⟨1905008, by rfl⟩ : syracuseStep 2540011 = 3810017) B3810017
theorem B6775487 : Blo 1336987 6775487 := bstep (se 1 (by rfl) ⟨5081615, by rfl⟩ : syracuseStep 6775487 = 10163231) B10163231
theorem B4285153 : Blo 1336987 4285153 := bstep (se 2 (by rfl) ⟨1606932, by rfl⟩ : syracuseStep 4285153 = 3213865) B3213865
theorem B18301895 : Blo 1336987 18301895 := bstep (se 1 (by rfl) ⟨13726421, by rfl⟩ : syracuseStep 18301895 = 27452843) B27452843
theorem B4515155 : Blo 1336987 4515155 := bstep (se 1 (by rfl) ⟨3386366, by rfl⟩ : syracuseStep 4515155 = 6772733) B6772733
theorem B7235003 : Blo 1336987 7235003 := bstep (se 1 (by rfl) ⟨5426252, by rfl⟩ : syracuseStep 7235003 = 10852505) B10852505
theorem B18310931 : Blo 1336987 18310931 := bstep (se 1 (by rfl) ⟨13733198, by rfl⟩ : syracuseStep 18310931 = 27466397) B27466397
theorem B1337791 : Blo 1336987 1337791 := bstep (se 1 (by rfl) ⟨1003343, by rfl⟩ : syracuseStep 1337791 = 2006687) B2006687
theorem B25709075 : Blo 1336987 25709075 := bstep (se 1 (by rfl) ⟨19281806, by rfl⟩ : syracuseStep 25709075 = 38563613) B38563613
theorem B2411063 : Blo 1336987 2411063 := bstep (se 1 (by rfl) ⟨1808297, by rfl⟩ : syracuseStep 2411063 = 3616595) B3616595
theorem B15231725 : Blo 1336987 15231725 := bstep (se 3 (by rfl) ⟨2855948, by rfl⟩ : syracuseStep 15231725 = 5711897) B5711897
theorem B5712839 : Blo 1336987 5712839 := bstep (se 1 (by rfl) ⟨4284629, by rfl⟩ : syracuseStep 5712839 = 8569259) B8569259
theorem B3214367 : Blo 1336987 3214367 := bstep (se 1 (by rfl) ⟨2410775, by rfl⟩ : syracuseStep 3214367 = 4821551) B4821551
theorem B20589751 : Blo 1336987 20589751 := bstep (se 1 (by rfl) ⟨15442313, by rfl⟩ : syracuseStep 20589751 = 30884627) B30884627
theorem B3009761 : Blo 1336987 3009761 := bstep (se 2 (by rfl) ⟨1128660, by rfl⟩ : syracuseStep 3009761 = 2257321) B2257321
theorem B1338927 : Blo 1336987 1338927 := bstep (se 1 (by rfl) ⟨1004195, by rfl⟩ : syracuseStep 1338927 = 2008391) B2008391
theorem B33009211 : Blo 1336987 33009211 := bstep (se 1 (by rfl) ⟨24756908, by rfl⟩ : syracuseStep 33009211 = 49513817) B49513817
theorem B3215095 : Blo 1336987 3215095 := bstep (se 1 (by rfl) ⟨2411321, by rfl⟩ : syracuseStep 3215095 = 4822643) B4822643
theorem B6770627 : Blo 1336987 6770627 := bstep (se 1 (by rfl) ⟨5077970, by rfl⟩ : syracuseStep 6770627 = 10155941) B10155941
theorem B10162259 : Blo 1336987 10162259 := bstep (se 1 (by rfl) ⟨7621694, by rfl⟩ : syracuseStep 10162259 = 15243389) B15243389
theorem B10850755 : Blo 1336987 10850755 := bstep (se 1 (by rfl) ⟨8138066, by rfl⟩ : syracuseStep 10850755 = 16276133) B16276133
theorem B4518557 : Blo 1336987 4518557 := bstep (se 3 (by rfl) ⟨847229, by rfl⟩ : syracuseStep 4518557 = 1694459) B1694459
theorem B18567863 : Blo 1336987 18567863 := bstep (se 1 (by rfl) ⟨13925897, by rfl⟩ : syracuseStep 18567863 = 27851795) B27851795
theorem B17380295 : Blo 1336987 17380295 := bstep (se 1 (by rfl) ⟨13035221, by rfl⟩ : syracuseStep 17380295 = 26070443) B26070443
theorem B3052487 : Blo 1336987 3052487 := bstep (se 1 (by rfl) ⟨2289365, by rfl⟩ : syracuseStep 3052487 = 4578731) B4578731
theorem B3388463 : Blo 1336987 3388463 := bstep (se 1 (by rfl) ⟨2541347, by rfl⟩ : syracuseStep 3388463 = 5082695) B5082695
theorem B15250679 : Blo 1336987 15250679 := bstep (se 1 (by rfl) ⟨11438009, by rfl⟩ : syracuseStep 15250679 = 22876019) B22876019
theorem B97703495 : Blo 1336987 97703495 := bstep (se 1 (by rfl) ⟨73277621, by rfl⟩ : syracuseStep 97703495 = 146555243) B146555243
theorem B1504975 : Blo 1336987 1504975 := bstep (se 1 (by rfl) ⟨1128731, by rfl⟩ : syracuseStep 1504975 = 2257463) B2257463
theorem B10303199 : Blo 1336987 10303199 := bstep (se 1 (by rfl) ⟨7727399, by rfl⟩ : syracuseStep 10303199 = 15454799) B15454799
theorem B5076863 : Blo 1336987 5076863 := bstep (se 1 (by rfl) ⟨3807647, by rfl⟩ : syracuseStep 5076863 = 7615295) B7615295
theorem B10164203 : Blo 1336987 10164203 := bstep (se 1 (by rfl) ⟨7623152, by rfl⟩ : syracuseStep 10164203 = 15246305) B15246305
theorem B5077181 : Blo 1336987 5077181 := bstep (se 3 (by rfl) ⟨951971, by rfl⟩ : syracuseStep 5077181 = 1903943) B1903943
theorem B2005487 : Blo 1336987 2005487 := bstep (se 1 (by rfl) ⟨1504115, by rfl⟩ : syracuseStep 2005487 = 3008231) B3008231
theorem B130136615 : Blo 1336987 130136615 := bstep (se 1 (by rfl) ⟨97602461, by rfl⟩ : syracuseStep 130136615 = 195204923) B195204923
theorem B1505839 : Blo 1336987 1505839 := bstep (se 1 (by rfl) ⟨1129379, by rfl⟩ : syracuseStep 1505839 = 2258759) B2258759
theorem B2005559 : Blo 1336987 2005559 := bstep (se 1 (by rfl) ⟨1504169, by rfl⟩ : syracuseStep 2005559 = 3008339) B3008339
theorem B9640673 : Blo 1336987 9640673 := bstep (se 2 (by rfl) ⟨3615252, by rfl⟩ : syracuseStep 9640673 = 7230505) B7230505
theorem B24730715 : Blo 1336987 24730715 := bstep (se 1 (by rfl) ⟨18548036, by rfl⟩ : syracuseStep 24730715 = 37096073) B37096073
theorem B2006267 : Blo 1336987 2006267 := bstep (se 1 (by rfl) ⟨1504700, by rfl⟩ : syracuseStep 2006267 = 3009401) B3009401
theorem B2006375 : Blo 1336987 2006375 := bstep (se 1 (by rfl) ⟨1504781, by rfl⟩ : syracuseStep 2006375 = 3009563) B3009563
theorem B2006393 : Blo 1336987 2006393 := bstep (se 2 (by rfl) ⟨752397, by rfl⟩ : syracuseStep 2006393 = 1504795) B1504795
theorem B18316667 : Blo 1336987 18316667 := bstep (se 1 (by rfl) ⟨13737500, by rfl⟩ : syracuseStep 18316667 = 27475001) B27475001
theorem B10165661 : Blo 1336987 10165661 := bstep (se 3 (by rfl) ⟨1906061, by rfl⟩ : syracuseStep 10165661 = 3812123) B3812123
theorem B52133377 : Blo 1336987 52133377 := bstep (se 2 (by rfl) ⟨19550016, by rfl⟩ : syracuseStep 52133377 = 39100033) B39100033
theorem B2006975 : Blo 1336987 2006975 := bstep (se 1 (by rfl) ⟨1505231, by rfl⟩ : syracuseStep 2006975 = 3010463) B3010463
theorem B5079095 : Blo 1336987 5079095 := bstep (se 1 (by rfl) ⟨3809321, by rfl⟩ : syracuseStep 5079095 = 7618643) B7618643
theorem B6774839 : Blo 1336987 6774839 := bstep (se 1 (by rfl) ⟨5081129, by rfl⟩ : syracuseStep 6774839 = 10162259) B10162259
theorem B12378575 : Blo 1336987 12378575 := bstep (se 1 (by rfl) ⟨9283931, by rfl⟩ : syracuseStep 12378575 = 18567863) B18567863
theorem B14467673 : Blo 1336987 14467673 := bstep (se 2 (by rfl) ⟨5425377, by rfl⟩ : syracuseStep 14467673 = 10850755) B10850755
theorem B2007785 : Blo 1336987 2007785 := bstep (se 2 (by rfl) ⟨752919, by rfl⟩ : syracuseStep 2007785 = 1505839) B1505839
theorem B10167119 : Blo 1336987 10167119 := bstep (se 1 (by rfl) ⟨7625339, by rfl⟩ : syracuseStep 10167119 = 15250679) B15250679
theorem B65135663 : Blo 1336987 65135663 := bstep (se 1 (by rfl) ⟨48851747, by rfl⟩ : syracuseStep 65135663 = 97703495) B97703495
theorem B12207287 : Blo 1336987 12207287 := bstep (se 1 (by rfl) ⟨9155465, by rfl⟩ : syracuseStep 12207287 = 18310931) B18310931
theorem B3384575 : Blo 1336987 3384575 := bstep (se 1 (by rfl) ⟨2538431, by rfl⟩ : syracuseStep 3384575 = 5076863) B5076863
theorem B17147173 : Blo 1336987 17147173 := bstep (se 4 (by rfl) ⟨1607547, by rfl⟩ : syracuseStep 17147173 = 3215095) B3215095
theorem B6776135 : Blo 1336987 6776135 := bstep (se 1 (by rfl) ⟨5082101, by rfl⟩ : syracuseStep 6776135 = 10164203) B10164203
theorem B3384787 : Blo 1336987 3384787 := bstep (se 1 (by rfl) ⟨2538590, by rfl⟩ : syracuseStep 3384787 = 5077181) B5077181
theorem B27453001 : Blo 1336987 27453001 := bstep (se 2 (by rfl) ⟨10294875, by rfl⟩ : syracuseStep 27453001 = 20589751) B20589751
theorem B1336991 : Blo 1336987 1336991 := bstep (se 1 (by rfl) ⟨1002743, by rfl⟩ : syracuseStep 1336991 = 2005487) B2005487
theorem B17139383 : Blo 1336987 17139383 := bstep (se 1 (by rfl) ⟨12854537, by rfl⟩ : syracuseStep 17139383 = 25709075) B25709075
theorem B1337039 : Blo 1336987 1337039 := bstep (se 1 (by rfl) ⟨1002779, by rfl⟩ : syracuseStep 1337039 = 2005559) B2005559
theorem B1607375 : Blo 1336987 1607375 := bstep (se 1 (by rfl) ⟨1205531, by rfl⟩ : syracuseStep 1607375 = 2411063) B2411063
theorem B69511169 : Blo 1336987 69511169 := bstep (se 2 (by rfl) ⟨26066688, by rfl⟩ : syracuseStep 69511169 = 52133377) B52133377
theorem B1337511 : Blo 1336987 1337511 := bstep (se 1 (by rfl) ⟨1003133, by rfl⟩ : syracuseStep 1337511 = 2006267) B2006267
theorem B1337583 : Blo 1336987 1337583 := bstep (se 1 (by rfl) ⟨1003187, by rfl⟩ : syracuseStep 1337583 = 2006375) B2006375
theorem B1337595 : Blo 1336987 1337595 := bstep (se 1 (by rfl) ⟨1003196, by rfl⟩ : syracuseStep 1337595 = 2006393) B2006393
theorem B6777107 : Blo 1336987 6777107 := bstep (se 1 (by rfl) ⟨5082830, by rfl⟩ : syracuseStep 6777107 = 10165661) B10165661
theorem B1337983 : Blo 1336987 1337983 := bstep (se 1 (by rfl) ⟨1003487, by rfl⟩ : syracuseStep 1337983 = 2006975) B2006975
theorem B1338139 : Blo 1336987 1338139 := bstep (se 1 (by rfl) ⟨1003604, by rfl⟩ : syracuseStep 1338139 = 2007209) B2007209
theorem B65948573 : Blo 1336987 65948573 := bstep (se 3 (by rfl) ⟨12365357, by rfl⟩ : syracuseStep 65948573 = 24730715) B24730715
theorem B3009491 : Blo 1336987 3009491 := bstep (se 1 (by rfl) ⟨2257118, by rfl⟩ : syracuseStep 3009491 = 4514237) B4514237
theorem B4516991 : Blo 1336987 4516991 := bstep (se 1 (by rfl) ⟨3387743, by rfl⟩ : syracuseStep 4516991 = 6775487) B6775487
theorem B12201263 : Blo 1336987 12201263 := bstep (se 1 (by rfl) ⟨9150947, by rfl⟩ : syracuseStep 12201263 = 18301895) B18301895
theorem B11586863 : Blo 1336987 11586863 := bstep (se 1 (by rfl) ⟨8690147, by rfl⟩ : syracuseStep 11586863 = 17380295) B17380295
theorem B2034991 : Blo 1336987 2034991 := bstep (se 1 (by rfl) ⟨1526243, by rfl⟩ : syracuseStep 2034991 = 3052487) B3052487
theorem B3386681 : Blo 1336987 3386681 := bstep (se 2 (by rfl) ⟨1270005, by rfl⟩ : syracuseStep 3386681 = 2540011) B2540011
theorem B3010103 : Blo 1336987 3010103 := bstep (se 1 (by rfl) ⟨2257577, by rfl⟩ : syracuseStep 3010103 = 4515155) B4515155
theorem B6868799 : Blo 1336987 6868799 := bstep (se 1 (by rfl) ⟨5151599, by rfl⟩ : syracuseStep 6868799 = 10303199) B10303199
theorem B86757743 : Blo 1336987 86757743 := bstep (se 1 (by rfl) ⟨65068307, by rfl⟩ : syracuseStep 86757743 = 130136615) B130136615
theorem B6427115 : Blo 1336987 6427115 := bstep (se 1 (by rfl) ⟨4820336, by rfl⟩ : syracuseStep 6427115 = 9640673) B9640673
theorem B10154483 : Blo 1336987 10154483 := bstep (se 1 (by rfl) ⟨7615862, by rfl⟩ : syracuseStep 10154483 = 15231725) B15231725
theorem B2142911 : Blo 1336987 2142911 := bstep (se 1 (by rfl) ⟨1607183, by rfl⟩ : syracuseStep 2142911 = 3214367) B3214367
theorem B44012281 : Blo 1336987 44012281 := bstep (se 2 (by rfl) ⟨16504605, by rfl⟩ : syracuseStep 44012281 = 33009211) B33009211
theorem B12211111 : Blo 1336987 12211111 := bstep (se 1 (by rfl) ⟨9158333, by rfl⟩ : syracuseStep 12211111 = 18316667) B18316667
theorem B3012371 : Blo 1336987 3012371 := bstep (se 1 (by rfl) ⟨2259278, by rfl⟩ : syracuseStep 3012371 = 4518557) B4518557
theorem B2258975 : Blo 1336987 2258975 := bstep (se 1 (by rfl) ⟨1694231, by rfl⟩ : syracuseStep 2258975 = 3388463) B3388463
theorem B4823335 : Blo 1336987 4823335 := bstep (se 1 (by rfl) ⟨3617501, by rfl⟩ : syracuseStep 4823335 = 7235003) B7235003
theorem B22854149 : Blo 1336987 22854149 := bstep (se 4 (by rfl) ⟨2142576, by rfl⟩ : syracuseStep 22854149 = 4285153) B4285153
theorem B3808559 : Blo 1336987 3808559 := bstep (se 1 (by rfl) ⟨2856419, by rfl⟩ : syracuseStep 3808559 = 5712839) B5712839
theorem B2006507 : Blo 1336987 2006507 := bstep (se 1 (by rfl) ⟨1504880, by rfl⟩ : syracuseStep 2006507 = 3009761) B3009761
theorem B2006633 : Blo 1336987 2006633 := bstep (se 2 (by rfl) ⟨752487, by rfl⟩ : syracuseStep 2006633 = 1504975) B1504975
theorem B4513751 : Blo 1336987 4513751 := bstep (se 1 (by rfl) ⟨3385313, by rfl⟩ : syracuseStep 4513751 = 6770627) B6770627
theorem B4284743 : Blo 1336987 4284743 := bstep (se 1 (by rfl) ⟨3213557, by rfl⟩ : syracuseStep 4284743 = 6427115) B6427115
theorem B6431113 : Blo 1336987 6431113 := bstep (se 2 (by rfl) ⟨2411667, by rfl⟩ : syracuseStep 6431113 = 4823335) B4823335
theorem B2008247 : Blo 1336987 2008247 := bstep (se 1 (by rfl) ⟨1506185, by rfl⟩ : syracuseStep 2008247 = 3012371) B3012371
theorem B2713321 : Blo 1336987 2713321 := bstep (se 2 (by rfl) ⟨1017495, by rfl⟩ : syracuseStep 2713321 = 2034991) B2034991
theorem B4286333 : Blo 1336987 4286333 := bstep (se 3 (by rfl) ⟨803687, by rfl⟩ : syracuseStep 4286333 = 1607375) B1607375
theorem B36604001 : Blo 1336987 36604001 := bstep (se 2 (by rfl) ⟨13726500, by rfl⟩ : syracuseStep 36604001 = 27453001) B27453001
theorem B1337671 : Blo 1336987 1337671 := bstep (se 1 (by rfl) ⟨1003253, by rfl⟩ : syracuseStep 1337671 = 2006507) B2006507
theorem B1337755 : Blo 1336987 1337755 := bstep (se 1 (by rfl) ⟨1003316, by rfl⟩ : syracuseStep 1337755 = 2006633) B2006633
theorem B3009167 : Blo 1336987 3009167 := bstep (se 1 (by rfl) ⟨2256875, by rfl⟩ : syracuseStep 3009167 = 4513751) B4513751
theorem B3386063 : Blo 1336987 3386063 := bstep (se 1 (by rfl) ⟨2539547, by rfl⟩ : syracuseStep 3386063 = 5079095) B5079095
theorem B4516559 : Blo 1336987 4516559 := bstep (se 1 (by rfl) ⟨3387419, by rfl⟩ : syracuseStep 4516559 = 6774839) B6774839
theorem B57838495 : Blo 1336987 57838495 := bstep (se 1 (by rfl) ⟨43378871, by rfl⟩ : syracuseStep 57838495 = 86757743) B86757743
theorem B8252383 : Blo 1336987 8252383 := bstep (se 1 (by rfl) ⟨6189287, by rfl⟩ : syracuseStep 8252383 = 12378575) B12378575
theorem B6769655 : Blo 1336987 6769655 := bstep (se 1 (by rfl) ⟨5077241, by rfl⟩ : syracuseStep 6769655 = 10154483) B10154483
theorem B9645115 : Blo 1336987 9645115 := bstep (se 1 (by rfl) ⟨7233836, by rfl⟩ : syracuseStep 9645115 = 14467673) B14467673
theorem B1428607 : Blo 1336987 1428607 := bstep (se 1 (by rfl) ⟨1071455, by rfl⟩ : syracuseStep 1428607 = 2142911) B2142911
theorem B1338523 : Blo 1336987 1338523 := bstep (se 1 (by rfl) ⟨1003892, by rfl⟩ : syracuseStep 1338523 = 2007785) B2007785
theorem B6778079 : Blo 1336987 6778079 := bstep (se 1 (by rfl) ⟨5083559, by rfl⟩ : syracuseStep 6778079 = 10167119) B10167119
theorem B2256383 : Blo 1336987 2256383 := bstep (se 1 (by rfl) ⟨1692287, by rfl⟩ : syracuseStep 2256383 = 3384575) B3384575
theorem B4517423 : Blo 1336987 4517423 := bstep (se 1 (by rfl) ⟨3388067, by rfl⟩ : syracuseStep 4517423 = 6776135) B6776135
theorem B58683041 : Blo 1336987 58683041 := bstep (se 2 (by rfl) ⟨22006140, by rfl⟩ : syracuseStep 58683041 = 44012281) B44012281
theorem B16281481 : Blo 1336987 16281481 := bstep (se 2 (by rfl) ⟨6105555, by rfl⟩ : syracuseStep 16281481 = 12211111) B12211111
theorem B4518071 : Blo 1336987 4518071 := bstep (se 1 (by rfl) ⟨3388553, by rfl⟩ : syracuseStep 4518071 = 6777107) B6777107
theorem B3011327 : Blo 1336987 3011327 := bstep (se 1 (by rfl) ⟨2258495, by rfl⟩ : syracuseStep 3011327 = 4516991) B4516991
theorem B2257787 : Blo 1336987 2257787 := bstep (se 1 (by rfl) ⟨1693340, by rfl⟩ : syracuseStep 2257787 = 3386681) B3386681
theorem B32552765 : Blo 1336987 32552765 := bstep (se 3 (by rfl) ⟨6103643, by rfl⟩ : syracuseStep 32552765 = 12207287) B12207287
theorem B43423775 : Blo 1336987 43423775 := bstep (se 1 (by rfl) ⟨32567831, by rfl⟩ : syracuseStep 43423775 = 65135663) B65135663
theorem B11426255 : Blo 1336987 11426255 := bstep (se 1 (by rfl) ⟨8569691, by rfl⟩ : syracuseStep 11426255 = 17139383) B17139383
theorem B46340779 : Blo 1336987 46340779 := bstep (se 1 (by rfl) ⟨34755584, by rfl⟩ : syracuseStep 46340779 = 69511169) B69511169
theorem B1505983 : Blo 1336987 1505983 := bstep (se 1 (by rfl) ⟨1129487, by rfl⟩ : syracuseStep 1505983 = 2258975) B2258975
theorem B15236099 : Blo 1336987 15236099 := bstep (se 1 (by rfl) ⟨11427074, by rfl⟩ : syracuseStep 15236099 = 22854149) B22854149
theorem B22862897 : Blo 1336987 22862897 := bstep (se 2 (by rfl) ⟨8573586, by rfl⟩ : syracuseStep 22862897 = 17147173) B17147173
theorem B43965715 : Blo 1336987 43965715 := bstep (se 1 (by rfl) ⟨32974286, by rfl⟩ : syracuseStep 43965715 = 65948573) B65948573
theorem B4513049 : Blo 1336987 4513049 := bstep (se 2 (by rfl) ⟨1692393, by rfl⟩ : syracuseStep 4513049 = 3384787) B3384787
theorem B2006327 : Blo 1336987 2006327 := bstep (se 1 (by rfl) ⟨1504745, by rfl⟩ : syracuseStep 2006327 = 3009491) B3009491
theorem B2539039 : Blo 1336987 2539039 := bstep (se 1 (by rfl) ⟨1904279, by rfl⟩ : syracuseStep 2539039 = 3808559) B3808559
theorem B8134175 : Blo 1336987 8134175 := bstep (se 1 (by rfl) ⟨6100631, by rfl⟩ : syracuseStep 8134175 = 12201263) B12201263
theorem B7724575 : Blo 1336987 7724575 := bstep (se 1 (by rfl) ⟨5793431, by rfl⟩ : syracuseStep 7724575 = 11586863) B11586863
theorem B2006735 : Blo 1336987 2006735 := bstep (se 1 (by rfl) ⟨1505051, by rfl⟩ : syracuseStep 2006735 = 3010103) B3010103
theorem B4579199 : Blo 1336987 4579199 := bstep (se 1 (by rfl) ⟨3434399, by rfl⟩ : syracuseStep 4579199 = 6868799) B6868799
theorem B2007551 : Blo 1336987 2007551 := bstep (se 1 (by rfl) ⟨1505663, by rfl⟩ : syracuseStep 2007551 = 3011327) B3011327
theorem B2007977 : Blo 1336987 2007977 := bstep (se 2 (by rfl) ⟨752991, by rfl⟩ : syracuseStep 2007977 = 1505983) B1505983
theorem B21701843 : Blo 1336987 21701843 := bstep (se 1 (by rfl) ⟨16276382, by rfl⟩ : syracuseStep 21701843 = 32552765) B32552765
theorem B11003177 : Blo 1336987 11003177 := bstep (se 2 (by rfl) ⟨4126191, by rfl⟩ : syracuseStep 11003177 = 8252383) B8252383
theorem B3385385 : Blo 1336987 3385385 := bstep (se 2 (by rfl) ⟨1269519, by rfl⟩ : syracuseStep 3385385 = 2539039) B2539039
theorem B10299433 : Blo 1336987 10299433 := bstep (se 2 (by rfl) ⟨3862287, by rfl⟩ : syracuseStep 10299433 = 7724575) B7724575
theorem B3008699 : Blo 1336987 3008699 := bstep (se 1 (by rfl) ⟨2256524, by rfl⟩ : syracuseStep 3008699 = 4513049) B4513049
theorem B1337551 : Blo 1336987 1337551 := bstep (se 1 (by rfl) ⟨1003163, by rfl⟩ : syracuseStep 1337551 = 2006327) B2006327
theorem B1337823 : Blo 1336987 1337823 := bstep (se 1 (by rfl) ⟨1003367, by rfl⟩ : syracuseStep 1337823 = 2006735) B2006735
theorem B1338831 : Blo 1336987 1338831 := bstep (se 1 (by rfl) ⟨1004123, by rfl⟩ : syracuseStep 1338831 = 2008247) B2008247
theorem B61787705 : Blo 1336987 61787705 := bstep (se 2 (by rfl) ⟨23170389, by rfl⟩ : syracuseStep 61787705 = 46340779) B46340779
theorem B14471045 : Blo 1336987 14471045 := bstep (se 4 (by rfl) ⟨1356660, by rfl⟩ : syracuseStep 14471045 = 2713321) B2713321
theorem B1904809 : Blo 1336987 1904809 := bstep (se 2 (by rfl) ⟨714303, by rfl⟩ : syracuseStep 1904809 = 1428607) B1428607
theorem B2257375 : Blo 1336987 2257375 := bstep (se 1 (by rfl) ⟨1693031, by rfl⟩ : syracuseStep 2257375 = 3386063) B3386063
theorem B3011039 : Blo 1336987 3011039 := bstep (se 1 (by rfl) ⟨2258279, by rfl⟩ : syracuseStep 3011039 = 4516559) B4516559
theorem B15241931 : Blo 1336987 15241931 := bstep (se 1 (by rfl) ⟨11431448, by rfl⟩ : syracuseStep 15241931 = 22862897) B22862897
theorem B4518719 : Blo 1336987 4518719 := bstep (se 1 (by rfl) ⟨3389039, by rfl⟩ : syracuseStep 4518719 = 6778079) B6778079
theorem B1504255 : Blo 1336987 1504255 := bstep (se 1 (by rfl) ⟨1128191, by rfl⟩ : syracuseStep 1504255 = 2256383) B2256383
theorem B3011615 : Blo 1336987 3011615 := bstep (se 1 (by rfl) ⟨2258711, by rfl⟩ : syracuseStep 3011615 = 4517423) B4517423
theorem B39122027 : Blo 1336987 39122027 := bstep (se 1 (by rfl) ⟨29341520, by rfl⟩ : syracuseStep 39122027 = 58683041) B58683041
theorem B3052799 : Blo 1336987 3052799 := bstep (se 1 (by rfl) ⟨2289599, by rfl⟩ : syracuseStep 3052799 = 4579199) B4579199
theorem B3012047 : Blo 1336987 3012047 := bstep (se 1 (by rfl) ⟨2259035, by rfl⟩ : syracuseStep 3012047 = 4518071) B4518071
theorem B8574817 : Blo 1336987 8574817 := bstep (se 2 (by rfl) ⟨3215556, by rfl⟩ : syracuseStep 8574817 = 6431113) B6431113
theorem B1505191 : Blo 1336987 1505191 := bstep (se 1 (by rfl) ⟨1128893, by rfl⟩ : syracuseStep 1505191 = 2257787) B2257787
theorem B11425981 : Blo 1336987 11425981 := bstep (se 3 (by rfl) ⟨2142371, by rfl⟩ : syracuseStep 11425981 = 4284743) B4284743
theorem B77117993 : Blo 1336987 77117993 := bstep (se 2 (by rfl) ⟨28919247, by rfl⟩ : syracuseStep 77117993 = 57838495) B57838495
theorem B2857555 : Blo 1336987 2857555 := bstep (se 1 (by rfl) ⟨2143166, by rfl⟩ : syracuseStep 2857555 = 4286333) B4286333
theorem B28949183 : Blo 1336987 28949183 := bstep (se 1 (by rfl) ⟨21711887, by rfl⟩ : syracuseStep 28949183 = 43423775) B43423775
theorem B24402667 : Blo 1336987 24402667 := bstep (se 1 (by rfl) ⟨18302000, by rfl⟩ : syracuseStep 24402667 = 36604001) B36604001
theorem B12860153 : Blo 1336987 12860153 := bstep (se 2 (by rfl) ⟨4822557, by rfl⟩ : syracuseStep 12860153 = 9645115) B9645115
theorem B7617503 : Blo 1336987 7617503 := bstep (se 1 (by rfl) ⟨5713127, by rfl⟩ : syracuseStep 7617503 = 11426255) B11426255
theorem B58620953 : Blo 1336987 58620953 := bstep (se 2 (by rfl) ⟨21982857, by rfl⟩ : syracuseStep 58620953 = 43965715) B43965715
theorem B2006111 : Blo 1336987 2006111 := bstep (se 1 (by rfl) ⟨1504583, by rfl⟩ : syracuseStep 2006111 = 3009167) B3009167
theorem B4513103 : Blo 1336987 4513103 := bstep (se 1 (by rfl) ⟨3384827, by rfl⟩ : syracuseStep 4513103 = 6769655) B6769655
theorem B10157399 : Blo 1336987 10157399 := bstep (se 1 (by rfl) ⟨7618049, by rfl⟩ : syracuseStep 10157399 = 15236099) B15236099
theorem B5422783 : Blo 1336987 5422783 := bstep (se 1 (by rfl) ⟨4067087, by rfl⟩ : syracuseStep 5422783 = 8134175) B8134175
theorem B21708641 : Blo 1336987 21708641 := bstep (se 2 (by rfl) ⟨8140740, by rfl⟩ : syracuseStep 21708641 = 16281481) B16281481
theorem B2539745 : Blo 1336987 2539745 := bstep (se 2 (by rfl) ⟨952404, by rfl⟩ : syracuseStep 2539745 = 1904809) B1904809
theorem B2007359 : Blo 1336987 2007359 := bstep (se 1 (by rfl) ⟨1505519, by rfl⟩ : syracuseStep 2007359 = 3011039) B3011039
theorem B2007743 : Blo 1336987 2007743 := bstep (se 1 (by rfl) ⟨1505807, by rfl⟩ : syracuseStep 2007743 = 3011615) B3011615
theorem B3810073 : Blo 1336987 3810073 := bstep (se 2 (by rfl) ⟨1428777, by rfl⟩ : syracuseStep 3810073 = 2857555) B2857555
theorem B14467895 : Blo 1336987 14467895 := bstep (se 1 (by rfl) ⟨10850921, by rfl⟩ : syracuseStep 14467895 = 21701843) B21701843
theorem B2008031 : Blo 1336987 2008031 := bstep (se 1 (by rfl) ⟨1506023, by rfl⟩ : syracuseStep 2008031 = 3012047) B3012047
theorem B164767213 : Blo 1336987 164767213 := bstep (se 3 (by rfl) ⟨30893852, by rfl⟩ : syracuseStep 164767213 = 61787705) B61787705
theorem B1337407 : Blo 1336987 1337407 := bstep (se 1 (by rfl) ⟨1003055, by rfl⟩ : syracuseStep 1337407 = 2006111) B2006111
theorem B3008735 : Blo 1336987 3008735 := bstep (se 1 (by rfl) ⟨2256551, by rfl⟩ : syracuseStep 3008735 = 4513103) B4513103
theorem B13732577 : Blo 1336987 13732577 := bstep (se 2 (by rfl) ⟨5149716, by rfl⟩ : syracuseStep 13732577 = 10299433) B10299433
theorem B156322541 : Blo 1336987 156322541 := bstep (se 3 (by rfl) ⟨29310476, by rfl⟩ : syracuseStep 156322541 = 58620953) B58620953
theorem B1338367 : Blo 1336987 1338367 := bstep (se 1 (by rfl) ⟨1003775, by rfl⟩ : syracuseStep 1338367 = 2007551) B2007551
theorem B10161287 : Blo 1336987 10161287 := bstep (se 1 (by rfl) ⟨7620965, by rfl⟩ : syracuseStep 10161287 = 15241931) B15241931
theorem B1338651 : Blo 1336987 1338651 := bstep (se 1 (by rfl) ⟨1003988, by rfl⟩ : syracuseStep 1338651 = 2007977) B2007977
theorem B3009833 : Blo 1336987 3009833 := bstep (se 2 (by rfl) ⟨1128687, by rfl⟩ : syracuseStep 3009833 = 2257375) B2257375
theorem B2035199 : Blo 1336987 2035199 := bstep (se 1 (by rfl) ⟨1526399, by rfl⟩ : syracuseStep 2035199 = 3052799) B3052799
theorem B7335451 : Blo 1336987 7335451 := bstep (se 1 (by rfl) ⟨5501588, by rfl⟩ : syracuseStep 7335451 = 11003177) B11003177
theorem B2256923 : Blo 1336987 2256923 := bstep (se 1 (by rfl) ⟨1692692, by rfl⟩ : syracuseStep 2256923 = 3385385) B3385385
theorem B8573435 : Blo 1336987 8573435 := bstep (se 1 (by rfl) ⟨6430076, by rfl⟩ : syracuseStep 8573435 = 12860153) B12860153
theorem B6771599 : Blo 1336987 6771599 := bstep (se 1 (by rfl) ⟨5078699, by rfl⟩ : syracuseStep 6771599 = 10157399) B10157399
theorem B7230377 : Blo 1336987 7230377 := bstep (se 2 (by rfl) ⟨2711391, by rfl⟩ : syracuseStep 7230377 = 5422783) B5422783
theorem B11433089 : Blo 1336987 11433089 := bstep (se 2 (by rfl) ⟨4287408, by rfl⟩ : syracuseStep 11433089 = 8574817) B8574817
theorem B14472427 : Blo 1336987 14472427 := bstep (se 1 (by rfl) ⟨10854320, by rfl⟩ : syracuseStep 14472427 = 21708641) B21708641
theorem B9647363 : Blo 1336987 9647363 := bstep (se 1 (by rfl) ⟨7235522, by rfl⟩ : syracuseStep 9647363 = 14471045) B14471045
theorem B15234641 : Blo 1336987 15234641 := bstep (se 2 (by rfl) ⟨5712990, by rfl⟩ : syracuseStep 15234641 = 11425981) B11425981
theorem B3012479 : Blo 1336987 3012479 := bstep (se 1 (by rfl) ⟨2259359, by rfl⟩ : syracuseStep 3012479 = 4518719) B4518719
theorem B26081351 : Blo 1336987 26081351 := bstep (se 1 (by rfl) ⟨19561013, by rfl⟩ : syracuseStep 26081351 = 39122027) B39122027
theorem B32536889 : Blo 1336987 32536889 := bstep (se 2 (by rfl) ⟨12201333, by rfl⟩ : syracuseStep 32536889 = 24402667) B24402667
theorem B2005673 : Blo 1336987 2005673 := bstep (se 2 (by rfl) ⟨752127, by rfl⟩ : syracuseStep 2005673 = 1504255) B1504255
theorem B2005799 : Blo 1336987 2005799 := bstep (se 1 (by rfl) ⟨1504349, by rfl⟩ : syracuseStep 2005799 = 3008699) B3008699
theorem B51411995 : Blo 1336987 51411995 := bstep (se 1 (by rfl) ⟨38558996, by rfl⟩ : syracuseStep 51411995 = 77117993) B77117993
theorem B19299455 : Blo 1336987 19299455 := bstep (se 1 (by rfl) ⟨14474591, by rfl⟩ : syracuseStep 19299455 = 28949183) B28949183
theorem B5078335 : Blo 1336987 5078335 := bstep (se 1 (by rfl) ⟨3808751, by rfl⟩ : syracuseStep 5078335 = 7617503) B7617503
theorem B2006921 : Blo 1336987 2006921 := bstep (se 2 (by rfl) ⟨752595, by rfl⟩ : syracuseStep 2006921 = 1505191) B1505191
theorem B4514399 : Blo 1336987 4514399 := bstep (se 1 (by rfl) ⟨3385799, by rfl⟩ : syracuseStep 4514399 = 6771599) B6771599
theorem B6431575 : Blo 1336987 6431575 := bstep (se 1 (by rfl) ⟨4823681, by rfl⟩ : syracuseStep 6431575 = 9647363) B9647363
theorem B5080097 : Blo 1336987 5080097 := bstep (se 2 (by rfl) ⟨1905036, by rfl⟩ : syracuseStep 5080097 = 3810073) B3810073
theorem B2008319 : Blo 1336987 2008319 := bstep (se 1 (by rfl) ⟨1506239, by rfl⟩ : syracuseStep 2008319 = 3012479) B3012479
theorem B1337115 : Blo 1336987 1337115 := bstep (se 1 (by rfl) ⟨1002836, by rfl⟩ : syracuseStep 1337115 = 2005673) B2005673
theorem B1337199 : Blo 1336987 1337199 := bstep (se 1 (by rfl) ⟨1002899, by rfl⟩ : syracuseStep 1337199 = 2005799) B2005799
theorem B1337947 : Blo 1336987 1337947 := bstep (se 1 (by rfl) ⟨1003460, by rfl⟩ : syracuseStep 1337947 = 2006921) B2006921
theorem B1338239 : Blo 1336987 1338239 := bstep (se 1 (by rfl) ⟨1003679, by rfl⟩ : syracuseStep 1338239 = 2007359) B2007359
theorem B1338495 : Blo 1336987 1338495 := bstep (se 1 (by rfl) ⟨1003871, by rfl⟩ : syracuseStep 1338495 = 2007743) B2007743
theorem B9645263 : Blo 1336987 9645263 := bstep (se 1 (by rfl) ⟨7233947, by rfl⟩ : syracuseStep 9645263 = 14467895) B14467895
theorem B4820251 : Blo 1336987 4820251 := bstep (se 1 (by rfl) ⟨3615188, by rfl⟩ : syracuseStep 4820251 = 7230377) B7230377
theorem B1338687 : Blo 1336987 1338687 := bstep (se 1 (by rfl) ⟨1004015, by rfl⟩ : syracuseStep 1338687 = 2008031) B2008031
theorem B7622059 : Blo 1336987 7622059 := bstep (se 1 (by rfl) ⟨5716544, by rfl⟩ : syracuseStep 7622059 = 11433089) B11433089
theorem B17387567 : Blo 1336987 17387567 := bstep (se 1 (by rfl) ⟨13040675, by rfl⟩ : syracuseStep 17387567 = 26081351) B26081351
theorem B19296569 : Blo 1336987 19296569 := bstep (se 2 (by rfl) ⟨7236213, by rfl⟩ : syracuseStep 19296569 = 14472427) B14472427
theorem B6771113 : Blo 1336987 6771113 := bstep (se 2 (by rfl) ⟨2539167, by rfl⟩ : syracuseStep 6771113 = 5078335) B5078335
theorem B9155051 : Blo 1336987 9155051 := bstep (se 1 (by rfl) ⟨6866288, by rfl⟩ : syracuseStep 9155051 = 13732577) B13732577
theorem B104215027 : Blo 1336987 104215027 := bstep (se 1 (by rfl) ⟨78161270, by rfl⟩ : syracuseStep 104215027 = 156322541) B156322541
theorem B219689617 : Blo 1336987 219689617 := bstep (se 2 (by rfl) ⟨82383606, by rfl⟩ : syracuseStep 219689617 = 164767213) B164767213
theorem B12866303 : Blo 1336987 12866303 := bstep (se 1 (by rfl) ⟨9649727, by rfl⟩ : syracuseStep 12866303 = 19299455) B19299455
theorem B1356799 : Blo 1336987 1356799 := bstep (se 1 (by rfl) ⟨1017599, by rfl⟩ : syracuseStep 1356799 = 2035199) B2035199
theorem B1504615 : Blo 1336987 1504615 := bstep (se 1 (by rfl) ⟨1128461, by rfl⟩ : syracuseStep 1504615 = 2256923) B2256923
theorem B1693163 : Blo 1336987 1693163 := bstep (se 1 (by rfl) ⟨1269872, by rfl⟩ : syracuseStep 1693163 = 2539745) B2539745
theorem B5715623 : Blo 1336987 5715623 := bstep (se 1 (by rfl) ⟨4286717, by rfl⟩ : syracuseStep 5715623 = 8573435) B8573435
theorem B10156427 : Blo 1336987 10156427 := bstep (se 1 (by rfl) ⟨7617320, by rfl⟩ : syracuseStep 10156427 = 15234641) B15234641
theorem B2005823 : Blo 1336987 2005823 := bstep (se 1 (by rfl) ⟨1504367, by rfl⟩ : syracuseStep 2005823 = 3008735) B3008735
theorem B21691259 : Blo 1336987 21691259 := bstep (se 1 (by rfl) ⟨16268444, by rfl⟩ : syracuseStep 21691259 = 32536889) B32536889
theorem B34274663 : Blo 1336987 34274663 := bstep (se 1 (by rfl) ⟨25705997, by rfl⟩ : syracuseStep 34274663 = 51411995) B51411995
theorem B9780601 : Blo 1336987 9780601 := bstep (se 2 (by rfl) ⟨3667725, by rfl⟩ : syracuseStep 9780601 = 7335451) B7335451
theorem B6774191 : Blo 1336987 6774191 := bstep (se 1 (by rfl) ⟨5080643, by rfl⟩ : syracuseStep 6774191 = 10161287) B10161287
theorem B2006555 : Blo 1336987 2006555 := bstep (se 1 (by rfl) ⟨1504916, by rfl⟩ : syracuseStep 2006555 = 3009833) B3009833
theorem B11591711 : Blo 1336987 11591711 := bstep (se 1 (by rfl) ⟨8693783, by rfl⟩ : syracuseStep 11591711 = 17387567) B17387567
theorem B4514075 : Blo 1336987 4514075 := bstep (se 1 (by rfl) ⟨3385556, by rfl⟩ : syracuseStep 4514075 = 6771113) B6771113
theorem B6103367 : Blo 1336987 6103367 := bstep (se 1 (by rfl) ⟨4577525, by rfl⟩ : syracuseStep 6103367 = 9155051) B9155051
theorem B8577535 : Blo 1336987 8577535 := bstep (se 1 (by rfl) ⟨6433151, by rfl⟩ : syracuseStep 8577535 = 12866303) B12866303
theorem B138953369 : Blo 1336987 138953369 := bstep (se 2 (by rfl) ⟨52107513, by rfl⟩ : syracuseStep 138953369 = 104215027) B104215027
theorem B3810415 : Blo 1336987 3810415 := bstep (se 1 (by rfl) ⟨2857811, by rfl⟩ : syracuseStep 3810415 = 5715623) B5715623
theorem B4515101 : Blo 1336987 4515101 := bstep (se 3 (by rfl) ⟨846581, by rfl⟩ : syracuseStep 4515101 = 1693163) B1693163
theorem B1337215 : Blo 1336987 1337215 := bstep (se 1 (by rfl) ⟨1002911, by rfl⟩ : syracuseStep 1337215 = 2005823) B2005823
theorem B14460839 : Blo 1336987 14460839 := bstep (se 1 (by rfl) ⟨10845629, by rfl⟩ : syracuseStep 14460839 = 21691259) B21691259
theorem B22849775 : Blo 1336987 22849775 := bstep (se 1 (by rfl) ⟨17137331, by rfl⟩ : syracuseStep 22849775 = 34274663) B34274663
theorem B4516127 : Blo 1336987 4516127 := bstep (se 1 (by rfl) ⟨3387095, by rfl⟩ : syracuseStep 4516127 = 6774191) B6774191
theorem B1337703 : Blo 1336987 1337703 := bstep (se 1 (by rfl) ⟨1003277, by rfl⟩ : syracuseStep 1337703 = 2006555) B2006555
theorem B12864379 : Blo 1336987 12864379 := bstep (se 1 (by rfl) ⟨9648284, by rfl⟩ : syracuseStep 12864379 = 19296569) B19296569
theorem B3009599 : Blo 1336987 3009599 := bstep (se 1 (by rfl) ⟨2257199, by rfl⟩ : syracuseStep 3009599 = 4514399) B4514399
theorem B3386731 : Blo 1336987 3386731 := bstep (se 1 (by rfl) ⟨2540048, by rfl⟩ : syracuseStep 3386731 = 5080097) B5080097
theorem B1338879 : Blo 1336987 1338879 := bstep (se 1 (by rfl) ⟨1004159, by rfl⟩ : syracuseStep 1338879 = 2008319) B2008319
theorem B6770951 : Blo 1336987 6770951 := bstep (se 1 (by rfl) ⟨5078213, by rfl⟩ : syracuseStep 6770951 = 10156427) B10156427
theorem B6427001 : Blo 1336987 6427001 := bstep (se 2 (by rfl) ⟨2410125, by rfl⟩ : syracuseStep 6427001 = 4820251) B4820251
theorem B10162745 : Blo 1336987 10162745 := bstep (se 2 (by rfl) ⟨3811029, by rfl⟩ : syracuseStep 10162745 = 7622059) B7622059
theorem B292919489 : Blo 1336987 292919489 := bstep (se 2 (by rfl) ⟨109844808, by rfl⟩ : syracuseStep 292919489 = 219689617) B219689617
theorem B8575433 : Blo 1336987 8575433 := bstep (se 2 (by rfl) ⟨3215787, by rfl⟩ : syracuseStep 8575433 = 6431575) B6431575
theorem B1809065 : Blo 1336987 1809065 := bstep (se 2 (by rfl) ⟨678399, by rfl⟩ : syracuseStep 1809065 = 1356799) B1356799
theorem B2006153 : Blo 1336987 2006153 := bstep (se 2 (by rfl) ⟨752307, by rfl⟩ : syracuseStep 2006153 = 1504615) B1504615
theorem B13040801 : Blo 1336987 13040801 := bstep (se 2 (by rfl) ⟨4890300, by rfl⟩ : syracuseStep 13040801 = 9780601) B9780601
theorem B6430175 : Blo 1336987 6430175 := bstep (se 1 (by rfl) ⟨4822631, by rfl⟩ : syracuseStep 6430175 = 9645263) B9645263
theorem B4513967 : Blo 1336987 4513967 := bstep (se 1 (by rfl) ⟨3385475, by rfl⟩ : syracuseStep 4513967 = 6770951) B6770951
theorem B4284667 : Blo 1336987 4284667 := bstep (se 1 (by rfl) ⟨3213500, by rfl⟩ : syracuseStep 4284667 = 6427001) B6427001
theorem B6775163 : Blo 1336987 6775163 := bstep (se 1 (by rfl) ⟨5081372, by rfl⟩ : syracuseStep 6775163 = 10162745) B10162745
theorem B92635579 : Blo 1336987 92635579 := bstep (se 1 (by rfl) ⟨69476684, by rfl⟩ : syracuseStep 92635579 = 138953369) B138953369
theorem B11436713 : Blo 1336987 11436713 := bstep (se 2 (by rfl) ⟨4288767, by rfl⟩ : syracuseStep 11436713 = 8577535) B8577535
theorem B5080553 : Blo 1336987 5080553 := bstep (se 2 (by rfl) ⟨1905207, by rfl⟩ : syracuseStep 5080553 = 3810415) B3810415
theorem B4515641 : Blo 1336987 4515641 := bstep (se 2 (by rfl) ⟨1693365, by rfl⟩ : syracuseStep 4515641 = 3386731) B3386731
theorem B1337435 : Blo 1336987 1337435 := bstep (se 1 (by rfl) ⟨1003076, by rfl⟩ : syracuseStep 1337435 = 2006153) B2006153
theorem B8693867 : Blo 1336987 8693867 := bstep (se 1 (by rfl) ⟨6520400, by rfl⟩ : syracuseStep 8693867 = 13040801) B13040801
theorem B4286783 : Blo 1336987 4286783 := bstep (se 1 (by rfl) ⟨3215087, by rfl⟩ : syracuseStep 4286783 = 6430175) B6430175
theorem B7727807 : Blo 1336987 7727807 := bstep (se 1 (by rfl) ⟨5795855, by rfl⟩ : syracuseStep 7727807 = 11591711) B11591711
theorem B3009383 : Blo 1336987 3009383 := bstep (se 1 (by rfl) ⟨2257037, by rfl⟩ : syracuseStep 3009383 = 4514075) B4514075
theorem B3010067 : Blo 1336987 3010067 := bstep (se 1 (by rfl) ⟨2257550, by rfl⟩ : syracuseStep 3010067 = 4515101) B4515101
theorem B15233183 : Blo 1336987 15233183 := bstep (se 1 (by rfl) ⟨11424887, by rfl⟩ : syracuseStep 15233183 = 22849775) B22849775
theorem B3010751 : Blo 1336987 3010751 := bstep (se 1 (by rfl) ⟨2258063, by rfl⟩ : syracuseStep 3010751 = 4516127) B4516127
theorem B4068911 : Blo 1336987 4068911 := bstep (se 1 (by rfl) ⟨3051683, by rfl⟩ : syracuseStep 4068911 = 6103367) B6103367
theorem B17152505 : Blo 1336987 17152505 := bstep (se 2 (by rfl) ⟨6432189, by rfl⟩ : syracuseStep 17152505 = 12864379) B12864379
theorem B9640559 : Blo 1336987 9640559 := bstep (se 1 (by rfl) ⟨7230419, by rfl⟩ : syracuseStep 9640559 = 14460839) B14460839
theorem B195279659 : Blo 1336987 195279659 := bstep (se 1 (by rfl) ⟨146459744, by rfl⟩ : syracuseStep 195279659 = 292919489) B292919489
theorem B5716955 : Blo 1336987 5716955 := bstep (se 1 (by rfl) ⟨4287716, by rfl⟩ : syracuseStep 5716955 = 8575433) B8575433
theorem B4824173 : Blo 1336987 4824173 := bstep (se 3 (by rfl) ⟨904532, by rfl⟩ : syracuseStep 4824173 = 1809065) B1809065
theorem B2006399 : Blo 1336987 2006399 := bstep (se 1 (by rfl) ⟨1504799, by rfl⟩ : syracuseStep 2006399 = 3009599) B3009599
theorem B2007167 : Blo 1336987 2007167 := bstep (se 1 (by rfl) ⟨1505375, by rfl⟩ : syracuseStep 2007167 = 3010751) B3010751
theorem B3811303 : Blo 1336987 3811303 := bstep (se 1 (by rfl) ⟨2858477, by rfl⟩ : syracuseStep 3811303 = 5716955) B5716955
theorem B1337599 : Blo 1336987 1337599 := bstep (se 1 (by rfl) ⟨1003199, by rfl⟩ : syracuseStep 1337599 = 2006399) B2006399
theorem B3009311 : Blo 1336987 3009311 := bstep (se 1 (by rfl) ⟨2256983, by rfl⟩ : syracuseStep 3009311 = 4513967) B4513967
theorem B4516775 : Blo 1336987 4516775 := bstep (se 1 (by rfl) ⟨3387581, by rfl⟩ : syracuseStep 4516775 = 6775163) B6775163
theorem B5712889 : Blo 1336987 5712889 := bstep (se 2 (by rfl) ⟨2142333, by rfl⟩ : syracuseStep 5712889 = 4284667) B4284667
theorem B3387035 : Blo 1336987 3387035 := bstep (se 1 (by rfl) ⟨2540276, by rfl⟩ : syracuseStep 3387035 = 5080553) B5080553
theorem B3010427 : Blo 1336987 3010427 := bstep (se 1 (by rfl) ⟨2257820, by rfl⟩ : syracuseStep 3010427 = 4515641) B4515641
theorem B5795911 : Blo 1336987 5795911 := bstep (se 1 (by rfl) ⟨4346933, by rfl⟩ : syracuseStep 5795911 = 8693867) B8693867
theorem B10850429 : Blo 1336987 10850429 := bstep (se 3 (by rfl) ⟨2034455, by rfl⟩ : syracuseStep 10850429 = 4068911) B4068911
theorem B6427039 : Blo 1336987 6427039 := bstep (se 1 (by rfl) ⟨4820279, by rfl⟩ : syracuseStep 6427039 = 9640559) B9640559
theorem B3216115 : Blo 1336987 3216115 := bstep (se 1 (by rfl) ⟨2412086, by rfl⟩ : syracuseStep 3216115 = 4824173) B4824173
theorem B494056421 : Blo 1336987 494056421 := bstep (se 4 (by rfl) ⟨46317789, by rfl⟩ : syracuseStep 494056421 = 92635579) B92635579
theorem B10155455 : Blo 1336987 10155455 := bstep (se 1 (by rfl) ⟨7616591, by rfl⟩ : syracuseStep 10155455 = 15233183) B15233183
theorem B7624475 : Blo 1336987 7624475 := bstep (se 1 (by rfl) ⟨5718356, by rfl⟩ : syracuseStep 7624475 = 11436713) B11436713
theorem B2857855 : Blo 1336987 2857855 := bstep (se 1 (by rfl) ⟨2143391, by rfl⟩ : syracuseStep 2857855 = 4286783) B4286783
theorem B11435003 : Blo 1336987 11435003 := bstep (se 1 (by rfl) ⟨8576252, by rfl⟩ : syracuseStep 11435003 = 17152505) B17152505
theorem B5151871 : Blo 1336987 5151871 := bstep (se 1 (by rfl) ⟨3863903, by rfl⟩ : syracuseStep 5151871 = 7727807) B7727807
theorem B130186439 : Blo 1336987 130186439 := bstep (se 1 (by rfl) ⟨97639829, by rfl⟩ : syracuseStep 130186439 = 195279659) B195279659
theorem B2006255 : Blo 1336987 2006255 := bstep (se 1 (by rfl) ⟨1504691, by rfl⟩ : syracuseStep 2006255 = 3009383) B3009383
theorem B2006711 : Blo 1336987 2006711 := bstep (se 1 (by rfl) ⟨1505033, by rfl⟩ : syracuseStep 2006711 = 3010067) B3010067
theorem B7233619 : Blo 1336987 7233619 := bstep (se 1 (by rfl) ⟨5425214, by rfl⟩ : syracuseStep 7233619 = 10850429) B10850429
theorem B8569385 : Blo 1336987 8569385 := bstep (se 2 (by rfl) ⟨3213519, by rfl⟩ : syracuseStep 8569385 = 6427039) B6427039
theorem B3810473 : Blo 1336987 3810473 := bstep (se 2 (by rfl) ⟨1428927, by rfl⟩ : syracuseStep 3810473 = 2857855) B2857855
theorem B1337503 : Blo 1336987 1337503 := bstep (se 1 (by rfl) ⟨1003127, by rfl⟩ : syracuseStep 1337503 = 2006255) B2006255
theorem B1337807 : Blo 1336987 1337807 := bstep (se 1 (by rfl) ⟨1003355, by rfl⟩ : syracuseStep 1337807 = 2006711) B2006711
theorem B5081737 : Blo 1336987 5081737 := bstep (se 2 (by rfl) ⟨1905651, by rfl⟩ : syracuseStep 5081737 = 3811303) B3811303
theorem B1338111 : Blo 1336987 1338111 := bstep (se 1 (by rfl) ⟨1003583, by rfl⟩ : syracuseStep 1338111 = 2007167) B2007167
theorem B7727881 : Blo 1336987 7727881 := bstep (se 2 (by rfl) ⟨2897955, by rfl⟩ : syracuseStep 7727881 = 5795911) B5795911
theorem B329370947 : Blo 1336987 329370947 := bstep (se 1 (by rfl) ⟨247028210, by rfl⟩ : syracuseStep 329370947 = 494056421) B494056421
theorem B6770303 : Blo 1336987 6770303 := bstep (se 1 (by rfl) ⟨5077727, by rfl⟩ : syracuseStep 6770303 = 10155455) B10155455
theorem B4288153 : Blo 1336987 4288153 := bstep (se 2 (by rfl) ⟨1608057, by rfl⟩ : syracuseStep 4288153 = 3216115) B3216115
theorem B5082983 : Blo 1336987 5082983 := bstep (se 1 (by rfl) ⟨3812237, by rfl⟩ : syracuseStep 5082983 = 7624475) B7624475
theorem B6869161 : Blo 1336987 6869161 := bstep (se 2 (by rfl) ⟨2575935, by rfl⟩ : syracuseStep 6869161 = 5151871) B5151871
theorem B3011183 : Blo 1336987 3011183 := bstep (se 1 (by rfl) ⟨2258387, by rfl⟩ : syracuseStep 3011183 = 4516775) B4516775
theorem B7623335 : Blo 1336987 7623335 := bstep (se 1 (by rfl) ⟨5717501, by rfl⟩ : syracuseStep 7623335 = 11435003) B11435003
theorem B86790959 : Blo 1336987 86790959 := bstep (se 1 (by rfl) ⟨65093219, by rfl⟩ : syracuseStep 86790959 = 130186439) B130186439
theorem B2258023 : Blo 1336987 2258023 := bstep (se 1 (by rfl) ⟨1693517, by rfl⟩ : syracuseStep 2258023 = 3387035) B3387035
theorem B7617185 : Blo 1336987 7617185 := bstep (se 2 (by rfl) ⟨2856444, by rfl⟩ : syracuseStep 7617185 = 5712889) B5712889
theorem B2006207 : Blo 1336987 2006207 := bstep (se 1 (by rfl) ⟨1504655, by rfl⟩ : syracuseStep 2006207 = 3009311) B3009311
theorem B2006951 : Blo 1336987 2006951 := bstep (se 1 (by rfl) ⟨1505213, by rfl⟩ : syracuseStep 2006951 = 3010427) B3010427
theorem B9158881 : Blo 1336987 9158881 := bstep (se 2 (by rfl) ⟨3434580, by rfl⟩ : syracuseStep 9158881 = 6869161) B6869161
theorem B2007455 : Blo 1336987 2007455 := bstep (se 1 (by rfl) ⟨1505591, by rfl⟩ : syracuseStep 2007455 = 3011183) B3011183
theorem B57860639 : Blo 1336987 57860639 := bstep (se 1 (by rfl) ⟨43395479, by rfl⟩ : syracuseStep 57860639 = 86790959) B86790959
theorem B2540315 : Blo 1336987 2540315 := bstep (se 1 (by rfl) ⟨1905236, by rfl⟩ : syracuseStep 2540315 = 3810473) B3810473
theorem B6775649 : Blo 1336987 6775649 := bstep (se 2 (by rfl) ⟨2540868, by rfl⟩ : syracuseStep 6775649 = 5081737) B5081737
theorem B1337471 : Blo 1336987 1337471 := bstep (se 1 (by rfl) ⟨1003103, by rfl⟩ : syracuseStep 1337471 = 2006207) B2006207
theorem B219580631 : Blo 1336987 219580631 := bstep (se 1 (by rfl) ⟨164685473, by rfl⟩ : syracuseStep 219580631 = 329370947) B329370947
theorem B1337967 : Blo 1336987 1337967 := bstep (se 1 (by rfl) ⟨1003475, by rfl⟩ : syracuseStep 1337967 = 2006951) B2006951
theorem B9644825 : Blo 1336987 9644825 := bstep (se 2 (by rfl) ⟨3616809, by rfl⟩ : syracuseStep 9644825 = 7233619) B7233619
theorem B5712923 : Blo 1336987 5712923 := bstep (se 1 (by rfl) ⟨4284692, by rfl⟩ : syracuseStep 5712923 = 8569385) B8569385
theorem B5082223 : Blo 1336987 5082223 := bstep (se 1 (by rfl) ⟨3811667, by rfl⟩ : syracuseStep 5082223 = 7623335) B7623335
theorem B3010697 : Blo 1336987 3010697 := bstep (se 2 (by rfl) ⟨1129011, by rfl⟩ : syracuseStep 3010697 = 2258023) B2258023
theorem B3388655 : Blo 1336987 3388655 := bstep (se 1 (by rfl) ⟨2541491, by rfl⟩ : syracuseStep 3388655 = 5082983) B5082983
theorem B10303841 : Blo 1336987 10303841 := bstep (se 2 (by rfl) ⟨3863940, by rfl⟩ : syracuseStep 10303841 = 7727881) B7727881
theorem B5078123 : Blo 1336987 5078123 := bstep (se 1 (by rfl) ⟨3808592, by rfl⟩ : syracuseStep 5078123 = 7617185) B7617185
theorem B5717537 : Blo 1336987 5717537 := bstep (se 2 (by rfl) ⟨2144076, by rfl⟩ : syracuseStep 5717537 = 4288153) B4288153
theorem B4513535 : Blo 1336987 4513535 := bstep (se 1 (by rfl) ⟨3385151, by rfl⟩ : syracuseStep 4513535 = 6770303) B6770303
theorem B2007131 : Blo 1336987 2007131 := bstep (se 1 (by rfl) ⟨1505348, by rfl⟩ : syracuseStep 2007131 = 3010697) B3010697
theorem B6776297 : Blo 1336987 6776297 := bstep (se 2 (by rfl) ⟨2541111, by rfl⟩ : syracuseStep 6776297 = 5082223) B5082223
theorem B3385415 : Blo 1336987 3385415 := bstep (se 1 (by rfl) ⟨2539061, by rfl⟩ : syracuseStep 3385415 = 5078123) B5078123
theorem B3811691 : Blo 1336987 3811691 := bstep (se 1 (by rfl) ⟨2858768, by rfl⟩ : syracuseStep 3811691 = 5717537) B5717537
theorem B3009023 : Blo 1336987 3009023 := bstep (se 1 (by rfl) ⟨2256767, by rfl⟩ : syracuseStep 3009023 = 4513535) B4513535
theorem B1338303 : Blo 1336987 1338303 := bstep (se 1 (by rfl) ⟨1003727, by rfl⟩ : syracuseStep 1338303 = 2007455) B2007455
theorem B4517099 : Blo 1336987 4517099 := bstep (se 1 (by rfl) ⟨3387824, by rfl⟩ : syracuseStep 4517099 = 6775649) B6775649
theorem B146387087 : Blo 1336987 146387087 := bstep (se 1 (by rfl) ⟨109790315, by rfl⟩ : syracuseStep 146387087 = 219580631) B219580631
theorem B6869227 : Blo 1336987 6869227 := bstep (se 1 (by rfl) ⟨5151920, by rfl⟩ : syracuseStep 6869227 = 10303841) B10303841
theorem B12211841 : Blo 1336987 12211841 := bstep (se 2 (by rfl) ⟨4579440, by rfl⟩ : syracuseStep 12211841 = 9158881) B9158881
theorem B38573759 : Blo 1336987 38573759 := bstep (se 1 (by rfl) ⟨28930319, by rfl⟩ : syracuseStep 38573759 = 57860639) B57860639
theorem B1693543 : Blo 1336987 1693543 := bstep (se 1 (by rfl) ⟨1270157, by rfl⟩ : syracuseStep 1693543 = 2540315) B2540315
theorem B2259103 : Blo 1336987 2259103 := bstep (se 1 (by rfl) ⟨1694327, by rfl⟩ : syracuseStep 2259103 = 3388655) B3388655
theorem B6429883 : Blo 1336987 6429883 := bstep (se 1 (by rfl) ⟨4822412, by rfl⟩ : syracuseStep 6429883 = 9644825) B9644825
theorem B3808615 : Blo 1336987 3808615 := bstep (se 1 (by rfl) ⟨2856461, by rfl⟩ : syracuseStep 3808615 = 5712923) B5712923
theorem B97591391 : Blo 1336987 97591391 := bstep (se 1 (by rfl) ⟨73193543, by rfl⟩ : syracuseStep 97591391 = 146387087) B146387087
theorem B9158969 : Blo 1336987 9158969 := bstep (se 2 (by rfl) ⟨3434613, by rfl⟩ : syracuseStep 9158969 = 6869227) B6869227
theorem B25715839 : Blo 1336987 25715839 := bstep (se 1 (by rfl) ⟨19286879, by rfl⟩ : syracuseStep 25715839 = 38573759) B38573759
theorem B2541127 : Blo 1336987 2541127 := bstep (se 1 (by rfl) ⟨1905845, by rfl⟩ : syracuseStep 2541127 = 3811691) B3811691
theorem B32564909 : Blo 1336987 32564909 := bstep (se 3 (by rfl) ⟨6105920, by rfl⟩ : syracuseStep 32564909 = 12211841) B12211841
theorem B1338087 : Blo 1336987 1338087 := bstep (se 1 (by rfl) ⟨1003565, by rfl⟩ : syracuseStep 1338087 = 2007131) B2007131
theorem B4517531 : Blo 1336987 4517531 := bstep (se 1 (by rfl) ⟨3388148, by rfl⟩ : syracuseStep 4517531 = 6776297) B6776297
theorem B2256943 : Blo 1336987 2256943 := bstep (se 1 (by rfl) ⟨1692707, by rfl⟩ : syracuseStep 2256943 = 3385415) B3385415
theorem B8573177 : Blo 1336987 8573177 := bstep (se 2 (by rfl) ⟨3214941, by rfl⟩ : syracuseStep 8573177 = 6429883) B6429883
theorem B3011399 : Blo 1336987 3011399 := bstep (se 1 (by rfl) ⟨2258549, by rfl⟩ : syracuseStep 3011399 = 4517099) B4517099
theorem B2258057 : Blo 1336987 2258057 := bstep (se 2 (by rfl) ⟨846771, by rfl⟩ : syracuseStep 2258057 = 1693543) B1693543
theorem B3012137 : Blo 1336987 3012137 := bstep (se 2 (by rfl) ⟨1129551, by rfl⟩ : syracuseStep 3012137 = 2259103) B2259103
theorem B2006015 : Blo 1336987 2006015 := bstep (se 1 (by rfl) ⟨1504511, by rfl⟩ : syracuseStep 2006015 = 3009023) B3009023
theorem B5078153 : Blo 1336987 5078153 := bstep (se 2 (by rfl) ⟨1904307, by rfl⟩ : syracuseStep 5078153 = 3808615) B3808615
theorem B65060927 : Blo 1336987 65060927 := bstep (se 1 (by rfl) ⟨48795695, by rfl⟩ : syracuseStep 65060927 = 97591391) B97591391
theorem B2007599 : Blo 1336987 2007599 := bstep (se 1 (by rfl) ⟨1505699, by rfl⟩ : syracuseStep 2007599 = 3011399) B3011399
theorem B2008091 : Blo 1336987 2008091 := bstep (se 1 (by rfl) ⟨1506068, by rfl⟩ : syracuseStep 2008091 = 3012137) B3012137
theorem B21709939 : Blo 1336987 21709939 := bstep (se 1 (by rfl) ⟨16282454, by rfl⟩ : syracuseStep 21709939 = 32564909) B32564909
theorem B1337343 : Blo 1336987 1337343 := bstep (se 1 (by rfl) ⟨1003007, by rfl⟩ : syracuseStep 1337343 = 2006015) B2006015
theorem B3385435 : Blo 1336987 3385435 := bstep (se 1 (by rfl) ⟨2539076, by rfl⟩ : syracuseStep 3385435 = 5078153) B5078153
theorem B3009257 : Blo 1336987 3009257 := bstep (se 2 (by rfl) ⟨1128471, by rfl⟩ : syracuseStep 3009257 = 2256943) B2256943
theorem B6105979 : Blo 1336987 6105979 := bstep (se 1 (by rfl) ⟨4579484, by rfl⟩ : syracuseStep 6105979 = 9158969) B9158969
theorem B34287785 : Blo 1336987 34287785 := bstep (se 2 (by rfl) ⟨12857919, by rfl⟩ : syracuseStep 34287785 = 25715839) B25715839
theorem B3388169 : Blo 1336987 3388169 := bstep (se 2 (by rfl) ⟨1270563, by rfl⟩ : syracuseStep 3388169 = 2541127) B2541127
theorem B3011687 : Blo 1336987 3011687 := bstep (se 1 (by rfl) ⟨2258765, by rfl⟩ : syracuseStep 3011687 = 4517531) B4517531
theorem B5715451 : Blo 1336987 5715451 := bstep (se 1 (by rfl) ⟨4286588, by rfl⟩ : syracuseStep 5715451 = 8573177) B8573177
theorem B1505371 : Blo 1336987 1505371 := bstep (se 1 (by rfl) ⟨1129028, by rfl⟩ : syracuseStep 1505371 = 2258057) B2258057
theorem B4513913 : Blo 1336987 4513913 := bstep (se 2 (by rfl) ⟨1692717, by rfl⟩ : syracuseStep 4513913 = 3385435) B3385435
theorem B2007161 : Blo 1336987 2007161 := bstep (se 2 (by rfl) ⟨752685, by rfl⟩ : syracuseStep 2007161 = 1505371) B1505371
theorem B2007791 : Blo 1336987 2007791 := bstep (se 1 (by rfl) ⟨1505843, by rfl⟩ : syracuseStep 2007791 = 3011687) B3011687
theorem B7620601 : Blo 1336987 7620601 := bstep (se 2 (by rfl) ⟨2857725, by rfl⟩ : syracuseStep 7620601 = 5715451) B5715451
theorem B22858523 : Blo 1336987 22858523 := bstep (se 1 (by rfl) ⟨17143892, by rfl⟩ : syracuseStep 22858523 = 34287785) B34287785
theorem B1338399 : Blo 1336987 1338399 := bstep (se 1 (by rfl) ⟨1003799, by rfl⟩ : syracuseStep 1338399 = 2007599) B2007599
theorem B1338727 : Blo 1336987 1338727 := bstep (se 1 (by rfl) ⟨1004045, by rfl⟩ : syracuseStep 1338727 = 2008091) B2008091
theorem B28946585 : Blo 1336987 28946585 := bstep (se 2 (by rfl) ⟨10854969, by rfl⟩ : syracuseStep 28946585 = 21709939) B21709939
theorem B43373951 : Blo 1336987 43373951 := bstep (se 1 (by rfl) ⟨32530463, by rfl⟩ : syracuseStep 43373951 = 65060927) B65060927
theorem B2258779 : Blo 1336987 2258779 := bstep (se 1 (by rfl) ⟨1694084, by rfl⟩ : syracuseStep 2258779 = 3388169) B3388169
theorem B8141305 : Blo 1336987 8141305 := bstep (se 2 (by rfl) ⟨3052989, by rfl⟩ : syracuseStep 8141305 = 6105979) B6105979
theorem B2006171 : Blo 1336987 2006171 := bstep (se 1 (by rfl) ⟨1504628, by rfl⟩ : syracuseStep 2006171 = 3009257) B3009257
theorem B10855073 : Blo 1336987 10855073 := bstep (se 2 (by rfl) ⟨4070652, by rfl⟩ : syracuseStep 10855073 = 8141305) B8141305
theorem B15239015 : Blo 1336987 15239015 := bstep (se 1 (by rfl) ⟨11429261, by rfl⟩ : syracuseStep 15239015 = 22858523) B22858523
theorem B1337447 : Blo 1336987 1337447 := bstep (se 1 (by rfl) ⟨1003085, by rfl⟩ : syracuseStep 1337447 = 2006171) B2006171
theorem B10160801 : Blo 1336987 10160801 := bstep (se 2 (by rfl) ⟨3810300, by rfl⟩ : syracuseStep 10160801 = 7620601) B7620601
theorem B3009275 : Blo 1336987 3009275 := bstep (se 1 (by rfl) ⟨2256956, by rfl⟩ : syracuseStep 3009275 = 4513913) B4513913
theorem B1338107 : Blo 1336987 1338107 := bstep (se 1 (by rfl) ⟨1003580, by rfl⟩ : syracuseStep 1338107 = 2007161) B2007161
theorem B1338527 : Blo 1336987 1338527 := bstep (se 1 (by rfl) ⟨1003895, by rfl⟩ : syracuseStep 1338527 = 2007791) B2007791
theorem B3011705 : Blo 1336987 3011705 := bstep (se 2 (by rfl) ⟨1129389, by rfl⟩ : syracuseStep 3011705 = 2258779) B2258779
theorem B19297723 : Blo 1336987 19297723 := bstep (se 1 (by rfl) ⟨14473292, by rfl⟩ : syracuseStep 19297723 = 28946585) B28946585
theorem B28915967 : Blo 1336987 28915967 := bstep (se 1 (by rfl) ⟨21686975, by rfl⟩ : syracuseStep 28915967 = 43373951) B43373951
theorem B2007803 : Blo 1336987 2007803 := bstep (se 1 (by rfl) ⟨1505852, by rfl⟩ : syracuseStep 2007803 = 3011705) B3011705
theorem B10159343 : Blo 1336987 10159343 := bstep (se 1 (by rfl) ⟨7619507, by rfl⟩ : syracuseStep 10159343 = 15239015) B15239015
theorem B19277311 : Blo 1336987 19277311 := bstep (se 1 (by rfl) ⟨14457983, by rfl⟩ : syracuseStep 19277311 = 28915967) B28915967
theorem B7236715 : Blo 1336987 7236715 := bstep (se 1 (by rfl) ⟨5427536, by rfl⟩ : syracuseStep 7236715 = 10855073) B10855073
theorem B6773867 : Blo 1336987 6773867 := bstep (se 1 (by rfl) ⟨5080400, by rfl⟩ : syracuseStep 6773867 = 10160801) B10160801
theorem B2006183 : Blo 1336987 2006183 := bstep (se 1 (by rfl) ⟨1504637, by rfl⟩ : syracuseStep 2006183 = 3009275) B3009275
theorem B25730297 : Blo 1336987 25730297 := bstep (se 2 (by rfl) ⟨9648861, by rfl⟩ : syracuseStep 25730297 = 19297723) B19297723
theorem B4515911 : Blo 1336987 4515911 := bstep (se 1 (by rfl) ⟨3386933, by rfl⟩ : syracuseStep 4515911 = 6773867) B6773867
theorem B1337455 : Blo 1336987 1337455 := bstep (se 1 (by rfl) ⟨1003091, by rfl⟩ : syracuseStep 1337455 = 2006183) B2006183
theorem B1338535 : Blo 1336987 1338535 := bstep (se 1 (by rfl) ⟨1003901, by rfl⟩ : syracuseStep 1338535 = 2007803) B2007803
theorem B25703081 : Blo 1336987 25703081 := bstep (se 2 (by rfl) ⟨9638655, by rfl⟩ : syracuseStep 25703081 = 19277311) B19277311
theorem B6772895 : Blo 1336987 6772895 := bstep (se 1 (by rfl) ⟨5079671, by rfl⟩ : syracuseStep 6772895 = 10159343) B10159343
theorem B9648953 : Blo 1336987 9648953 := bstep (se 2 (by rfl) ⟨3618357, by rfl⟩ : syracuseStep 9648953 = 7236715) B7236715
theorem B17153531 : Blo 1336987 17153531 := bstep (se 1 (by rfl) ⟨12865148, by rfl⟩ : syracuseStep 17153531 = 25730297) B25730297
theorem B4515263 : Blo 1336987 4515263 := bstep (se 1 (by rfl) ⟨3386447, by rfl⟩ : syracuseStep 4515263 = 6772895) B6772895
theorem B6432635 : Blo 1336987 6432635 := bstep (se 1 (by rfl) ⟨4824476, by rfl⟩ : syracuseStep 6432635 = 9648953) B9648953
theorem B3010607 : Blo 1336987 3010607 := bstep (se 1 (by rfl) ⟨2257955, by rfl⟩ : syracuseStep 3010607 = 4515911) B4515911
theorem B17135387 : Blo 1336987 17135387 := bstep (se 1 (by rfl) ⟨12851540, by rfl⟩ : syracuseStep 17135387 = 25703081) B25703081
theorem B11435687 : Blo 1336987 11435687 := bstep (se 1 (by rfl) ⟨8576765, by rfl⟩ : syracuseStep 11435687 = 17153531) B17153531
theorem B2007071 : Blo 1336987 2007071 := bstep (se 1 (by rfl) ⟨1505303, by rfl⟩ : syracuseStep 2007071 = 3010607) B3010607
theorem B3010175 : Blo 1336987 3010175 := bstep (se 1 (by rfl) ⟨2257631, by rfl⟩ : syracuseStep 3010175 = 4515263) B4515263
theorem B11423591 : Blo 1336987 11423591 := bstep (se 1 (by rfl) ⟨8567693, by rfl⟩ : syracuseStep 11423591 = 17135387) B17135387
theorem B4288423 : Blo 1336987 4288423 := bstep (se 1 (by rfl) ⟨3216317, by rfl⟩ : syracuseStep 4288423 = 6432635) B6432635
theorem B7623791 : Blo 1336987 7623791 := bstep (se 1 (by rfl) ⟨5717843, by rfl⟩ : syracuseStep 7623791 = 11435687) B11435687
theorem B1338047 : Blo 1336987 1338047 := bstep (se 1 (by rfl) ⟨1003535, by rfl⟩ : syracuseStep 1338047 = 2007071) B2007071
theorem B5082527 : Blo 1336987 5082527 := bstep (se 1 (by rfl) ⟨3811895, by rfl⟩ : syracuseStep 5082527 = 7623791) B7623791
theorem B7615727 : Blo 1336987 7615727 := bstep (se 1 (by rfl) ⟨5711795, by rfl⟩ : syracuseStep 7615727 = 11423591) B11423591
theorem B2006783 : Blo 1336987 2006783 := bstep (se 1 (by rfl) ⟨1505087, by rfl⟩ : syracuseStep 2006783 = 3010175) B3010175
theorem B5717897 : Blo 1336987 5717897 := bstep (se 2 (by rfl) ⟨2144211, by rfl⟩ : syracuseStep 5717897 = 4288423) B4288423
theorem B1337855 : Blo 1336987 1337855 := bstep (se 1 (by rfl) ⟨1003391, by rfl⟩ : syracuseStep 1337855 = 2006783) B2006783
theorem B3811931 : Blo 1336987 3811931 := bstep (se 1 (by rfl) ⟨2858948, by rfl⟩ : syracuseStep 3811931 = 5717897) B5717897
theorem B3388351 : Blo 1336987 3388351 := bstep (se 1 (by rfl) ⟨2541263, by rfl⟩ : syracuseStep 3388351 = 5082527) B5082527
theorem B5077151 : Blo 1336987 5077151 := bstep (se 1 (by rfl) ⟨3807863, by rfl⟩ : syracuseStep 5077151 = 7615727) B7615727
theorem B3384767 : Blo 1336987 3384767 := bstep (se 1 (by rfl) ⟨2538575, by rfl⟩ : syracuseStep 3384767 = 5077151) B5077151
theorem B2541287 : Blo 1336987 2541287 := bstep (se 1 (by rfl) ⟨1905965, by rfl⟩ : syracuseStep 2541287 = 3811931) B3811931
theorem B4517801 : Blo 1336987 4517801 := bstep (se 2 (by rfl) ⟨1694175, by rfl⟩ : syracuseStep 4517801 = 3388351) B3388351
theorem B2256511 : Blo 1336987 2256511 := bstep (se 1 (by rfl) ⟨1692383, by rfl⟩ : syracuseStep 2256511 = 3384767) B3384767
theorem B3011867 : Blo 1336987 3011867 := bstep (se 1 (by rfl) ⟨2258900, by rfl⟩ : syracuseStep 3011867 = 4517801) B4517801
theorem B1694191 : Blo 1336987 1694191 := bstep (se 1 (by rfl) ⟨1270643, by rfl⟩ : syracuseStep 1694191 = 2541287) B2541287
theorem B2007911 : Blo 1336987 2007911 := bstep (se 1 (by rfl) ⟨1505933, by rfl⟩ : syracuseStep 2007911 = 3011867) B3011867
theorem B3008681 : Blo 1336987 3008681 := bstep (se 2 (by rfl) ⟨1128255, by rfl⟩ : syracuseStep 3008681 = 2256511) B2256511
theorem B2258921 : Blo 1336987 2258921 := bstep (se 2 (by rfl) ⟨847095, by rfl⟩ : syracuseStep 2258921 = 1694191) B1694191
theorem B1338607 : Blo 1336987 1338607 := bstep (se 1 (by rfl) ⟨1003955, by rfl⟩ : syracuseStep 1338607 = 2007911) B2007911
theorem B1505947 : Blo 1336987 1505947 := bstep (se 1 (by rfl) ⟨1129460, by rfl⟩ : syracuseStep 1505947 = 2258921) B2258921
theorem B2005787 : Blo 1336987 2005787 := bstep (se 1 (by rfl) ⟨1504340, by rfl⟩ : syracuseStep 2005787 = 3008681) B3008681
theorem B2007929 : Blo 1336987 2007929 := bstep (se 2 (by rfl) ⟨752973, by rfl⟩ : syracuseStep 2007929 = 1505947) B1505947
theorem B1337191 : Blo 1336987 1337191 := bstep (se 1 (by rfl) ⟨1002893, by rfl⟩ : syracuseStep 1337191 = 2005787) B2005787
theorem B1338619 : Blo 1336987 1338619 := bstep (se 1 (by rfl) ⟨1003964, by rfl⟩ : syracuseStep 1338619 = 2007929) B2007929

theorem C0 (j : ℕ) (h1 : 334246 ≤ j) (h2 : j ≤ 334746) : Blo 1336987 (4 * j + 3) := by
  interval_cases j
  · exact B1336987
  · exact B1336991
  · exact B1336995
  · exact B1336999
  · exact B1337003
  · exact B1337007
  · exact B1337011
  · exact B1337015
  · exact B1337019
  · exact B1337023
  · exact B1337027
  · exact B1337031
  · exact B1337035
  · exact B1337039
  · exact B1337043
  · exact B1337047
  · exact B1337051
  · exact B1337055
  · exact B1337059
  · exact B1337063
  · exact B1337067
  · exact B1337071
  · exact B1337075
  · exact B1337079
  · exact B1337083
  · exact B1337087
  · exact B1337091
  · exact B1337095
  · exact B1337099
  · exact B1337103
  · exact B1337107
  · exact B1337111
  · exact B1337115
  · exact B1337119
  · exact B1337123
  · exact B1337127
  · exact B1337131
  · exact B1337135
  · exact B1337139
  · exact B1337143
  · exact B1337147
  · exact B1337151
  · exact B1337155
  · exact B1337159
  · exact B1337163
  · exact B1337167
  · exact B1337171
  · exact B1337175
  · exact B1337179
  · exact B1337183
  · exact B1337187
  · exact B1337191
  · exact B1337195
  · exact B1337199
  · exact B1337203
  · exact B1337207
  · exact B1337211
  · exact B1337215
  · exact B1337219
  · exact B1337223
  · exact B1337227
  · exact B1337231
  · exact B1337235
  · exact B1337239
  · exact B1337243
  · exact B1337247
  · exact B1337251
  · exact B1337255
  · exact B1337259
  · exact B1337263
  · exact B1337267
  · exact B1337271
  · exact B1337275
  · exact B1337279
  · exact B1337283
  · exact B1337287
  · exact B1337291
  · exact B1337295
  · exact B1337299
  · exact B1337303
  · exact B1337307
  · exact B1337311
  · exact B1337315
  · exact B1337319
  · exact B1337323
  · exact B1337327
  · exact B1337331
  · exact B1337335
  · exact B1337339
  · exact B1337343
  · exact B1337347
  · exact B1337351
  · exact B1337355
  · exact B1337359
  · exact B1337363
  · exact B1337367
  · exact B1337371
  · exact B1337375
  · exact B1337379
  · exact B1337383
  · exact B1337387
  · exact B1337391
  · exact B1337395
  · exact B1337399
  · exact B1337403
  · exact B1337407
  · exact B1337411
  · exact B1337415
  · exact B1337419
  · exact B1337423
  · exact B1337427
  · exact B1337431
  · exact B1337435
  · exact B1337439
  · exact B1337443
  · exact B1337447
  · exact B1337451
  · exact B1337455
  · exact B1337459
  · exact B1337463
  · exact B1337467
  · exact B1337471
  · exact B1337475
  · exact B1337479
  · exact B1337483
  · exact B1337487
  · exact B1337491
  · exact B1337495
  · exact B1337499
  · exact B1337503
  · exact B1337507
  · exact B1337511
  · exact B1337515
  · exact B1337519
  · exact B1337523
  · exact B1337527
  · exact B1337531
  · exact B1337535
  · exact B1337539
  · exact B1337543
  · exact B1337547
  · exact B1337551
  · exact B1337555
  · exact B1337559
  · exact B1337563
  · exact B1337567
  · exact B1337571
  · exact B1337575
  · exact B1337579
  · exact B1337583
  · exact B1337587
  · exact B1337591
  · exact B1337595
  · exact B1337599
  · exact B1337603
  · exact B1337607
  · exact B1337611
  · exact B1337615
  · exact B1337619
  · exact B1337623
  · exact B1337627
  · exact B1337631
  · exact B1337635
  · exact B1337639
  · exact B1337643
  · exact B1337647
  · exact B1337651
  · exact B1337655
  · exact B1337659
  · exact B1337663
  · exact B1337667
  · exact B1337671
  · exact B1337675
  · exact B1337679
  · exact B1337683
  · exact B1337687
  · exact B1337691
  · exact B1337695
  · exact B1337699
  · exact B1337703
  · exact B1337707
  · exact B1337711
  · exact B1337715
  · exact B1337719
  · exact B1337723
  · exact B1337727
  · exact B1337731
  · exact B1337735
  · exact B1337739
  · exact B1337743
  · exact B1337747
  · exact B1337751
  · exact B1337755
  · exact B1337759
  · exact B1337763
  · exact B1337767
  · exact B1337771
  · exact B1337775
  · exact B1337779
  · exact B1337783
  · exact B1337787
  · exact B1337791
  · exact B1337795
  · exact B1337799
  · exact B1337803
  · exact B1337807
  · exact B1337811
  · exact B1337815
  · exact B1337819
  · exact B1337823
  · exact B1337827
  · exact B1337831
  · exact B1337835
  · exact B1337839
  · exact B1337843
  · exact B1337847
  · exact B1337851
  · exact B1337855
  · exact B1337859
  · exact B1337863
  · exact B1337867
  · exact B1337871
  · exact B1337875
  · exact B1337879
  · exact B1337883
  · exact B1337887
  · exact B1337891
  · exact B1337895
  · exact B1337899
  · exact B1337903
  · exact B1337907
  · exact B1337911
  · exact B1337915
  · exact B1337919
  · exact B1337923
  · exact B1337927
  · exact B1337931
  · exact B1337935
  · exact B1337939
  · exact B1337943
  · exact B1337947
  · exact B1337951
  · exact B1337955
  · exact B1337959
  · exact B1337963
  · exact B1337967
  · exact B1337971
  · exact B1337975
  · exact B1337979
  · exact B1337983
  · exact B1337987
  · exact B1337991
  · exact B1337995
  · exact B1337999
  · exact B1338003
  · exact B1338007
  · exact B1338011
  · exact B1338015
  · exact B1338019
  · exact B1338023
  · exact B1338027
  · exact B1338031
  · exact B1338035
  · exact B1338039
  · exact B1338043
  · exact B1338047
  · exact B1338051
  · exact B1338055
  · exact B1338059
  · exact B1338063
  · exact B1338067
  · exact B1338071
  · exact B1338075
  · exact B1338079
  · exact B1338083
  · exact B1338087
  · exact B1338091
  · exact B1338095
  · exact B1338099
  · exact B1338103
  · exact B1338107
  · exact B1338111
  · exact B1338115
  · exact B1338119
  · exact B1338123
  · exact B1338127
  · exact B1338131
  · exact B1338135
  · exact B1338139
  · exact B1338143
  · exact B1338147
  · exact B1338151
  · exact B1338155
  · exact B1338159
  · exact B1338163
  · exact B1338167
  · exact B1338171
  · exact B1338175
  · exact B1338179
  · exact B1338183
  · exact B1338187
  · exact B1338191
  · exact B1338195
  · exact B1338199
  · exact B1338203
  · exact B1338207
  · exact B1338211
  · exact B1338215
  · exact B1338219
  · exact B1338223
  · exact B1338227
  · exact B1338231
  · exact B1338235
  · exact B1338239
  · exact B1338243
  · exact B1338247
  · exact B1338251
  · exact B1338255
  · exact B1338259
  · exact B1338263
  · exact B1338267
  · exact B1338271
  · exact B1338275
  · exact B1338279
  · exact B1338283
  · exact B1338287
  · exact B1338291
  · exact B1338295
  · exact B1338299
  · exact B1338303
  · exact B1338307
  · exact B1338311
  · exact B1338315
  · exact B1338319
  · exact B1338323
  · exact B1338327
  · exact B1338331
  · exact B1338335
  · exact B1338339
  · exact B1338343
  · exact B1338347
  · exact B1338351
  · exact B1338355
  · exact B1338359
  · exact B1338363
  · exact B1338367
  · exact B1338371
  · exact B1338375
  · exact B1338379
  · exact B1338383
  · exact B1338387
  · exact B1338391
  · exact B1338395
  · exact B1338399
  · exact B1338403
  · exact B1338407
  · exact B1338411
  · exact B1338415
  · exact B1338419
  · exact B1338423
  · exact B1338427
  · exact B1338431
  · exact B1338435
  · exact B1338439
  · exact B1338443
  · exact B1338447
  · exact B1338451
  · exact B1338455
  · exact B1338459
  · exact B1338463
  · exact B1338467
  · exact B1338471
  · exact B1338475
  · exact B1338479
  · exact B1338483
  · exact B1338487
  · exact B1338491
  · exact B1338495
  · exact B1338499
  · exact B1338503
  · exact B1338507
  · exact B1338511
  · exact B1338515
  · exact B1338519
  · exact B1338523
  · exact B1338527
  · exact B1338531
  · exact B1338535
  · exact B1338539
  · exact B1338543
  · exact B1338547
  · exact B1338551
  · exact B1338555
  · exact B1338559
  · exact B1338563
  · exact B1338567
  · exact B1338571
  · exact B1338575
  · exact B1338579
  · exact B1338583
  · exact B1338587
  · exact B1338591
  · exact B1338595
  · exact B1338599
  · exact B1338603
  · exact B1338607
  · exact B1338611
  · exact B1338615
  · exact B1338619
  · exact B1338623
  · exact B1338627
  · exact B1338631
  · exact B1338635
  · exact B1338639
  · exact B1338643
  · exact B1338647
  · exact B1338651
  · exact B1338655
  · exact B1338659
  · exact B1338663
  · exact B1338667
  · exact B1338671
  · exact B1338675
  · exact B1338679
  · exact B1338683
  · exact B1338687
  · exact B1338691
  · exact B1338695
  · exact B1338699
  · exact B1338703
  · exact B1338707
  · exact B1338711
  · exact B1338715
  · exact B1338719
  · exact B1338723
  · exact B1338727
  · exact B1338731
  · exact B1338735
  · exact B1338739
  · exact B1338743
  · exact B1338747
  · exact B1338751
  · exact B1338755
  · exact B1338759
  · exact B1338763
  · exact B1338767
  · exact B1338771
  · exact B1338775
  · exact B1338779
  · exact B1338783
  · exact B1338787
  · exact B1338791
  · exact B1338795
  · exact B1338799
  · exact B1338803
  · exact B1338807
  · exact B1338811
  · exact B1338815
  · exact B1338819
  · exact B1338823
  · exact B1338827
  · exact B1338831
  · exact B1338835
  · exact B1338839
  · exact B1338843
  · exact B1338847
  · exact B1338851
  · exact B1338855
  · exact B1338859
  · exact B1338863
  · exact B1338867
  · exact B1338871
  · exact B1338875
  · exact B1338879
  · exact B1338883
  · exact B1338887
  · exact B1338891
  · exact B1338895
  · exact B1338899
  · exact B1338903
  · exact B1338907
  · exact B1338911
  · exact B1338915
  · exact B1338919
  · exact B1338923
  · exact B1338927
  · exact B1338931
  · exact B1338935
  · exact B1338939
  · exact B1338943
  · exact B1338947
  · exact B1338951
  · exact B1338955
  · exact B1338959
  · exact B1338963
  · exact B1338967
  · exact B1338971
  · exact B1338975
  · exact B1338979
  · exact B1338983
  · exact B1338987

theorem solution (m : ℕ) (hlo : 1336987 ≤ m) (hhi : m ≤ 1338987) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 334246 ≤ j := by omega
    have hj2 : j ≤ 334746 := by omega
    have hb : Blo 1336987 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
