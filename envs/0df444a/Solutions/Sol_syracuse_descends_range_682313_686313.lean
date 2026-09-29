-- Prove2me | solution 1 for syracuse_descends_range_682313_686313
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:04:55.61986+00:00
-- url     : https://prove2.me/submissions/611cf3a8-e5ef-48bc-8108-f27ca2c3a658

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


theorem B1540133 : Blo 682313 1540133 := bbase (se 4 (by rfl) ⟨144387, by rfl⟩ : syracuseStep 1540133 = 288775) (by norm_num)
theorem B1736741 : Blo 682313 1736741 := bbase (se 4 (by rfl) ⟨162819, by rfl⟩ : syracuseStep 1736741 = 325639) (by norm_num)
theorem B1540205 : Blo 682313 1540205 := bbase (se 3 (by rfl) ⟨288788, by rfl⟩ : syracuseStep 1540205 = 577577) (by norm_num)
theorem B1540277 : Blo 682313 1540277 := bbase (se 5 (by rfl) ⟨72200, by rfl⟩ : syracuseStep 1540277 = 144401) (by norm_num)
theorem B1540349 : Blo 682313 1540349 := bbase (se 3 (by rfl) ⟨288815, by rfl⟩ : syracuseStep 1540349 = 577631) (by norm_num)
theorem B1540421 : Blo 682313 1540421 := bbase (se 4 (by rfl) ⟨144414, by rfl⟩ : syracuseStep 1540421 = 288829) (by norm_num)
theorem B3473765 : Blo 682313 3473765 := bbase (se 4 (by rfl) ⟨325665, by rfl⟩ : syracuseStep 3473765 = 651331) (by norm_num)
theorem B1737085 : Blo 682313 1737085 := bbase (se 3 (by rfl) ⟨325703, by rfl⟩ : syracuseStep 1737085 = 651407) (by norm_num)
theorem B1540493 : Blo 682313 1540493 := bbase (se 3 (by rfl) ⟨288842, by rfl⟩ : syracuseStep 1540493 = 577685) (by norm_num)
theorem B4456885 : Blo 682313 4456885 := bbase (se 5 (by rfl) ⟨208916, by rfl⟩ : syracuseStep 4456885 = 417833) (by norm_num)
theorem B1540565 : Blo 682313 1540565 := bbase (se 7 (by rfl) ⟨18053, by rfl⟩ : syracuseStep 1540565 = 36107) (by norm_num)
theorem B1737197 : Blo 682313 1737197 := bbase (se 3 (by rfl) ⟨325724, by rfl⟩ : syracuseStep 1737197 = 651449) (by norm_num)
theorem B1540637 : Blo 682313 1540637 := bbase (se 3 (by rfl) ⟨288869, by rfl⟩ : syracuseStep 1540637 = 577739) (by norm_num)
theorem B819805 : Blo 682313 819805 := bbase (se 3 (by rfl) ⟨153713, by rfl⟩ : syracuseStep 819805 = 307427) (by norm_num)
theorem B1540709 : Blo 682313 1540709 := bbase (se 4 (by rfl) ⟨144441, by rfl⟩ : syracuseStep 1540709 = 288883) (by norm_num)
theorem B1540781 : Blo 682313 1540781 := bbase (se 3 (by rfl) ⟨288896, by rfl⟩ : syracuseStep 1540781 = 577793) (by norm_num)
theorem B819901 : Blo 682313 819901 := bbase (se 3 (by rfl) ⟨153731, by rfl⟩ : syracuseStep 819901 = 307463) (by norm_num)
theorem B1540853 : Blo 682313 1540853 := bbase (se 5 (by rfl) ⟨72227, by rfl⟩ : syracuseStep 1540853 = 144455) (by norm_num)
theorem B1540925 : Blo 682313 1540925 := bbase (se 3 (by rfl) ⟨288923, by rfl⟩ : syracuseStep 1540925 = 577847) (by norm_num)
theorem B1540997 : Blo 682313 1540997 := bbase (se 4 (by rfl) ⟨144468, by rfl⟩ : syracuseStep 1540997 = 288937) (by norm_num)
theorem B1541069 : Blo 682313 1541069 := bbase (se 3 (by rfl) ⟨288950, by rfl⟩ : syracuseStep 1541069 = 577901) (by norm_num)
theorem B1541141 : Blo 682313 1541141 := bbase (se 6 (by rfl) ⟨36120, by rfl⟩ : syracuseStep 1541141 = 72241) (by norm_num)
theorem B1541213 : Blo 682313 1541213 := bbase (se 3 (by rfl) ⟨288977, by rfl⟩ : syracuseStep 1541213 = 577955) (by norm_num)
theorem B5276821 : Blo 682313 5276821 := bbase (se 6 (by rfl) ⟨123675, by rfl⟩ : syracuseStep 5276821 = 247351) (by norm_num)
theorem B2196629 : Blo 682313 2196629 := bbase (se 6 (by rfl) ⟨51483, by rfl⟩ : syracuseStep 2196629 = 102967) (by norm_num)
theorem B1541285 : Blo 682313 1541285 := bbase (se 4 (by rfl) ⟨144495, by rfl⟩ : syracuseStep 1541285 = 288991) (by norm_num)
theorem B1541357 : Blo 682313 1541357 := bbase (se 3 (by rfl) ⟨289004, by rfl⟩ : syracuseStep 1541357 = 578009) (by norm_num)
theorem B1541429 : Blo 682313 1541429 := bbase (se 5 (by rfl) ⟨72254, by rfl⟩ : syracuseStep 1541429 = 144509) (by norm_num)
theorem B1541501 : Blo 682313 1541501 := bbase (se 3 (by rfl) ⟨289031, by rfl⟩ : syracuseStep 1541501 = 578063) (by norm_num)
theorem B1541573 : Blo 682313 1541573 := bbase (se 4 (by rfl) ⟨144522, by rfl⟩ : syracuseStep 1541573 = 289045) (by norm_num)
theorem B1541645 : Blo 682313 1541645 := bbase (se 3 (by rfl) ⟨289058, by rfl⟩ : syracuseStep 1541645 = 578117) (by norm_num)
theorem B11240981 : Blo 682313 11240981 := bbase (se 6 (by rfl) ⟨263460, by rfl⟩ : syracuseStep 11240981 = 526921) (by norm_num)
theorem B3507781 : Blo 682313 3507781 := bbase (se 4 (by rfl) ⟨328854, by rfl⟩ : syracuseStep 3507781 = 657709) (by norm_num)
theorem B1541717 : Blo 682313 1541717 := bbase (se 8 (by rfl) ⟨9033, by rfl⟩ : syracuseStep 1541717 = 18067) (by norm_num)
theorem B1541789 : Blo 682313 1541789 := bbase (se 3 (by rfl) ⟨289085, by rfl⟩ : syracuseStep 1541789 = 578171) (by norm_num)
theorem B820901 : Blo 682313 820901 := bbase (se 4 (by rfl) ⟨76959, by rfl⟩ : syracuseStep 820901 = 153919) (by norm_num)
theorem B1541861 : Blo 682313 1541861 := bbase (se 4 (by rfl) ⟨144549, by rfl⟩ : syracuseStep 1541861 = 289099) (by norm_num)
theorem B1541933 : Blo 682313 1541933 := bbase (se 3 (by rfl) ⟨289112, by rfl⟩ : syracuseStep 1541933 = 578225) (by norm_num)
theorem B1640245 : Blo 682313 1640245 := bbase (se 5 (by rfl) ⟨76886, by rfl⟩ : syracuseStep 1640245 = 153773) (by norm_num)
theorem B1542005 : Blo 682313 1542005 := bbase (se 5 (by rfl) ⟨72281, by rfl⟩ : syracuseStep 1542005 = 144563) (by norm_num)
theorem B1640341 : Blo 682313 1640341 := bbase (se 6 (by rfl) ⟨38445, by rfl⟩ : syracuseStep 1640341 = 76891) (by norm_num)
theorem B1542077 : Blo 682313 1542077 := bbase (se 3 (by rfl) ⟨289139, by rfl⟩ : syracuseStep 1542077 = 578279) (by norm_num)
theorem B821189 : Blo 682313 821189 := bbase (se 4 (by rfl) ⟨76986, by rfl⟩ : syracuseStep 821189 = 153973) (by norm_num)
theorem B1542149 : Blo 682313 1542149 := bbase (se 4 (by rfl) ⟨144576, by rfl⟩ : syracuseStep 1542149 = 289153) (by norm_num)
theorem B2197525 : Blo 682313 2197525 := bbase (se 6 (by rfl) ⟨51504, by rfl⟩ : syracuseStep 2197525 = 103009) (by norm_num)
theorem B2820149 : Blo 682313 2820149 := bbase (se 5 (by rfl) ⟨132194, by rfl⟩ : syracuseStep 2820149 = 264389) (by norm_num)
theorem B1542221 : Blo 682313 1542221 := bbase (se 3 (by rfl) ⟨289166, by rfl⟩ : syracuseStep 1542221 = 578333) (by norm_num)
theorem B2590805 : Blo 682313 2590805 := bbase (se 8 (by rfl) ⟨15180, by rfl⟩ : syracuseStep 2590805 = 30361) (by norm_num)
theorem B1640533 : Blo 682313 1640533 := bbase (se 8 (by rfl) ⟨9612, by rfl⟩ : syracuseStep 1640533 = 19225) (by norm_num)
theorem B821353 : Blo 682313 821353 := bbase (se 2 (by rfl) ⟨308007, by rfl⟩ : syracuseStep 821353 = 616015) (by norm_num)
theorem B821381 : Blo 682313 821381 := bbase (se 4 (by rfl) ⟨77004, by rfl⟩ : syracuseStep 821381 = 154009) (by norm_num)
theorem B1542293 : Blo 682313 1542293 := bbase (se 6 (by rfl) ⟨36147, by rfl⟩ : syracuseStep 1542293 = 72295) (by norm_num)
theorem B1542365 : Blo 682313 1542365 := bbase (se 3 (by rfl) ⟨289193, by rfl⟩ : syracuseStep 1542365 = 578387) (by norm_num)
theorem B821497 : Blo 682313 821497 := bbase (se 2 (by rfl) ⟨308061, by rfl⟩ : syracuseStep 821497 = 616123) (by norm_num)
theorem B1542437 : Blo 682313 1542437 := bbase (se 4 (by rfl) ⟨144603, by rfl⟩ : syracuseStep 1542437 = 289207) (by norm_num)
theorem B821593 : Blo 682313 821593 := bbase (se 2 (by rfl) ⟨308097, by rfl⟩ : syracuseStep 821593 = 616195) (by norm_num)
theorem B1542509 : Blo 682313 1542509 := bbase (se 3 (by rfl) ⟨289220, by rfl⟩ : syracuseStep 1542509 = 578441) (by norm_num)
theorem B1640861 : Blo 682313 1640861 := bbase (se 3 (by rfl) ⟨307661, by rfl⟩ : syracuseStep 1640861 = 615323) (by norm_num)
theorem B2197925 : Blo 682313 2197925 := bbase (se 4 (by rfl) ⟨206055, by rfl⟩ : syracuseStep 2197925 = 412111) (by norm_num)
theorem B1542581 : Blo 682313 1542581 := bbase (se 5 (by rfl) ⟨72308, by rfl⟩ : syracuseStep 1542581 = 144617) (by norm_num)
theorem B1542653 : Blo 682313 1542653 := bbase (se 3 (by rfl) ⟨289247, by rfl⟩ : syracuseStep 1542653 = 578495) (by norm_num)
theorem B1542725 : Blo 682313 1542725 := bbase (se 4 (by rfl) ⟨144630, by rfl⟩ : syracuseStep 1542725 = 289261) (by norm_num)
theorem B1542797 : Blo 682313 1542797 := bbase (se 3 (by rfl) ⟨289274, by rfl⟩ : syracuseStep 1542797 = 578549) (by norm_num)
theorem B1542869 : Blo 682313 1542869 := bbase (se 7 (by rfl) ⟨18080, by rfl⟩ : syracuseStep 1542869 = 36161) (by norm_num)
theorem B1542941 : Blo 682313 1542941 := bbase (se 3 (by rfl) ⟨289301, by rfl⟩ : syracuseStep 1542941 = 578603) (by norm_num)
theorem B822073 : Blo 682313 822073 := bbase (se 2 (by rfl) ⟨308277, by rfl⟩ : syracuseStep 822073 = 616555) (by norm_num)
theorem B1641293 : Blo 682313 1641293 := bbase (se 3 (by rfl) ⟨307742, by rfl⟩ : syracuseStep 1641293 = 615485) (by norm_num)
theorem B1543013 : Blo 682313 1543013 := bbase (se 4 (by rfl) ⟨144657, by rfl⟩ : syracuseStep 1543013 = 289315) (by norm_num)
theorem B1543085 : Blo 682313 1543085 := bbase (se 3 (by rfl) ⟨289328, by rfl⟩ : syracuseStep 1543085 = 578657) (by norm_num)
theorem B1543157 : Blo 682313 1543157 := bbase (se 5 (by rfl) ⟨72335, by rfl⟩ : syracuseStep 1543157 = 144671) (by norm_num)
theorem B1543229 : Blo 682313 1543229 := bbase (se 3 (by rfl) ⟨289355, by rfl⟩ : syracuseStep 1543229 = 578711) (by norm_num)
theorem B2919509 : Blo 682313 2919509 := bbase (se 8 (by rfl) ⟨17106, by rfl⟩ : syracuseStep 2919509 = 34213) (by norm_num)
theorem B1543301 : Blo 682313 1543301 := bbase (se 4 (by rfl) ⟨144684, by rfl⟩ : syracuseStep 1543301 = 289369) (by norm_num)
theorem B1641629 : Blo 682313 1641629 := bbase (se 3 (by rfl) ⟨307805, by rfl⟩ : syracuseStep 1641629 = 615611) (by norm_num)
theorem B1543373 : Blo 682313 1543373 := bbase (se 3 (by rfl) ⟨289382, by rfl⟩ : syracuseStep 1543373 = 578765) (by norm_num)
theorem B1543445 : Blo 682313 1543445 := bbase (se 6 (by rfl) ⟨36174, by rfl⟩ : syracuseStep 1543445 = 72349) (by norm_num)
theorem B1543517 : Blo 682313 1543517 := bbase (se 3 (by rfl) ⟨289409, by rfl⟩ : syracuseStep 1543517 = 578819) (by norm_num)
theorem B1478045 : Blo 682313 1478045 := bbase (se 3 (by rfl) ⟨277133, by rfl⟩ : syracuseStep 1478045 = 554267) (by norm_num)
theorem B3509669 : Blo 682313 3509669 := bbase (se 4 (by rfl) ⟨329031, by rfl⟩ : syracuseStep 3509669 = 658063) (by norm_num)
theorem B1543589 : Blo 682313 1543589 := bbase (se 4 (by rfl) ⟨144711, by rfl⟩ : syracuseStep 1543589 = 289423) (by norm_num)
theorem B1543661 : Blo 682313 1543661 := bbase (se 3 (by rfl) ⟨289436, by rfl⟩ : syracuseStep 1543661 = 578873) (by norm_num)
theorem B4918805 : Blo 682313 4918805 := bbase (se 6 (by rfl) ⟨115284, by rfl⟩ : syracuseStep 4918805 = 230569) (by norm_num)
theorem B1543733 : Blo 682313 1543733 := bbase (se 5 (by rfl) ⟨72362, by rfl⟩ : syracuseStep 1543733 = 144725) (by norm_num)
theorem B1543805 : Blo 682313 1543805 := bbase (se 3 (by rfl) ⟨289463, by rfl⟩ : syracuseStep 1543805 = 578927) (by norm_num)
theorem B1543877 : Blo 682313 1543877 := bbase (se 4 (by rfl) ⟨144738, by rfl⟩ : syracuseStep 1543877 = 289477) (by norm_num)
theorem B1543949 : Blo 682313 1543949 := bbase (se 3 (by rfl) ⟨289490, by rfl⟩ : syracuseStep 1543949 = 578981) (by norm_num)
theorem B1544021 : Blo 682313 1544021 := bbase (se 9 (by rfl) ⟨4523, by rfl⟩ : syracuseStep 1544021 = 9047) (by norm_num)
theorem B2527109 : Blo 682313 2527109 := bbase (se 4 (by rfl) ⟨236916, by rfl⟩ : syracuseStep 2527109 = 473833) (by norm_num)
theorem B1544093 : Blo 682313 1544093 := bbase (se 3 (by rfl) ⟨289517, by rfl⟩ : syracuseStep 1544093 = 579035) (by norm_num)
theorem B692173 : Blo 682313 692173 := bbase (se 3 (by rfl) ⟨129782, by rfl⟩ : syracuseStep 692173 = 259565) (by norm_num)
theorem B1544165 : Blo 682313 1544165 := bbase (se 4 (by rfl) ⟨144765, by rfl⟩ : syracuseStep 1544165 = 289531) (by norm_num)
theorem B2592917 : Blo 682313 2592917 := bbase (se 6 (by rfl) ⟨60771, by rfl⟩ : syracuseStep 2592917 = 121543) (by norm_num)
theorem B823457 : Blo 682313 823457 := bbase (se 2 (by rfl) ⟨308796, by rfl⟩ : syracuseStep 823457 = 617593) (by norm_num)
theorem B1642685 : Blo 682313 1642685 := bbase (se 3 (by rfl) ⟨308003, by rfl⟩ : syracuseStep 1642685 = 616007) (by norm_num)
theorem B823645 : Blo 682313 823645 := bbase (se 3 (by rfl) ⟨154433, by rfl⟩ : syracuseStep 823645 = 308867) (by norm_num)
theorem B3379589 : Blo 682313 3379589 := bbase (se 4 (by rfl) ⟨316836, by rfl⟩ : syracuseStep 3379589 = 633673) (by norm_num)
theorem B2593205 : Blo 682313 2593205 := bbase (se 5 (by rfl) ⟨121556, by rfl⟩ : syracuseStep 2593205 = 243113) (by norm_num)
theorem B2462213 : Blo 682313 2462213 := bbase (se 4 (by rfl) ⟨230832, by rfl⟩ : syracuseStep 2462213 = 461665) (by norm_num)
theorem B692749 : Blo 682313 692749 := bbase (se 3 (by rfl) ⟨129890, by rfl⟩ : syracuseStep 692749 = 259781) (by norm_num)
theorem B1151509 : Blo 682313 1151509 := bbase (se 6 (by rfl) ⟨26988, by rfl⟩ : syracuseStep 1151509 = 53977) (by norm_num)
theorem B823861 : Blo 682313 823861 := bbase (se 5 (by rfl) ⟨38618, by rfl⟩ : syracuseStep 823861 = 77237) (by norm_num)
theorem B1151597 : Blo 682313 1151597 := bbase (se 3 (by rfl) ⟨215924, by rfl⟩ : syracuseStep 1151597 = 431849) (by norm_num)
theorem B1151725 : Blo 682313 1151725 := bbase (se 3 (by rfl) ⟨215948, by rfl⟩ : syracuseStep 1151725 = 431897) (by norm_num)
theorem B1151813 : Blo 682313 1151813 := bbase (se 4 (by rfl) ⟨107982, by rfl⟩ : syracuseStep 1151813 = 215965) (by norm_num)
theorem B2921285 : Blo 682313 2921285 := bbase (se 4 (by rfl) ⟨273870, by rfl⟩ : syracuseStep 2921285 = 547741) (by norm_num)
theorem B824149 : Blo 682313 824149 := bbase (se 9 (by rfl) ⟨2414, by rfl⟩ : syracuseStep 824149 = 4829) (by norm_num)
theorem B1151941 : Blo 682313 1151941 := bbase (se 4 (by rfl) ⟨107994, by rfl⟩ : syracuseStep 1151941 = 215989) (by norm_num)
theorem B988157 : Blo 682313 988157 := bbase (se 3 (by rfl) ⟨185279, by rfl⟩ : syracuseStep 988157 = 370559) (by norm_num)
theorem B1152029 : Blo 682313 1152029 := bbase (se 3 (by rfl) ⟨216005, by rfl⟩ : syracuseStep 1152029 = 432011) (by norm_num)
theorem B1152157 : Blo 682313 1152157 := bbase (se 3 (by rfl) ⟨216029, by rfl⟩ : syracuseStep 1152157 = 432059) (by norm_num)
theorem B1152245 : Blo 682313 1152245 := bbase (se 5 (by rfl) ⟨54011, by rfl⟩ : syracuseStep 1152245 = 108023) (by norm_num)
theorem B922909 : Blo 682313 922909 := bbase (se 3 (by rfl) ⟨173045, by rfl⟩ : syracuseStep 922909 = 346091) (by norm_num)
theorem B3282277 : Blo 682313 3282277 := bbase (se 4 (by rfl) ⟨307713, by rfl⟩ : syracuseStep 3282277 = 615427) (by norm_num)
theorem B1152373 : Blo 682313 1152373 := bbase (se 5 (by rfl) ⟨54017, by rfl⟩ : syracuseStep 1152373 = 108035) (by norm_num)
theorem B1152461 : Blo 682313 1152461 := bbase (se 3 (by rfl) ⟨216086, by rfl⟩ : syracuseStep 1152461 = 432173) (by norm_num)
theorem B1054237 : Blo 682313 1054237 := bbase (se 3 (by rfl) ⟨197669, by rfl⟩ : syracuseStep 1054237 = 395339) (by norm_num)
theorem B1250869 : Blo 682313 1250869 := bbase (se 5 (by rfl) ⟨58634, by rfl⟩ : syracuseStep 1250869 = 117269) (by norm_num)
theorem B1152589 : Blo 682313 1152589 := bbase (se 3 (by rfl) ⟨216110, by rfl⟩ : syracuseStep 1152589 = 432221) (by norm_num)
theorem B2594389 : Blo 682313 2594389 := bbase (se 8 (by rfl) ⟨15201, by rfl⟩ : syracuseStep 2594389 = 30403) (by norm_num)
theorem B1152677 : Blo 682313 1152677 := bbase (se 4 (by rfl) ⟨108063, by rfl⟩ : syracuseStep 1152677 = 216127) (by norm_num)
theorem B5183189 : Blo 682313 5183189 := bbase (se 7 (by rfl) ⟨60740, by rfl⟩ : syracuseStep 5183189 = 121481) (by norm_num)
theorem B1152805 : Blo 682313 1152805 := bbase (se 4 (by rfl) ⟨108075, by rfl⟩ : syracuseStep 1152805 = 216151) (by norm_num)
theorem B2922277 : Blo 682313 2922277 := bbase (se 4 (by rfl) ⟨273963, by rfl⟩ : syracuseStep 2922277 = 547927) (by norm_num)
theorem B1152893 : Blo 682313 1152893 := bbase (se 3 (by rfl) ⟨216167, by rfl⟩ : syracuseStep 1152893 = 432335) (by norm_num)
theorem B2594693 : Blo 682313 2594693 := bbase (se 4 (by rfl) ⟨243252, by rfl⟩ : syracuseStep 2594693 = 486505) (by norm_num)
theorem B4396949 : Blo 682313 4396949 := bbase (se 6 (by rfl) ⟨103053, by rfl⟩ : syracuseStep 4396949 = 206107) (by norm_num)
theorem B694217 : Blo 682313 694217 := bbase (se 2 (by rfl) ⟨260331, by rfl⟩ : syracuseStep 694217 = 520663) (by norm_num)
theorem B1153021 : Blo 682313 1153021 := bbase (se 3 (by rfl) ⟨216191, by rfl⟩ : syracuseStep 1153021 = 432383) (by norm_num)
theorem B1153109 : Blo 682313 1153109 := bbase (se 8 (by rfl) ⟨6756, by rfl⟩ : syracuseStep 1153109 = 13513) (by norm_num)
theorem B923773 : Blo 682313 923773 := bbase (se 3 (by rfl) ⟨173207, by rfl⟩ : syracuseStep 923773 = 346415) (by norm_num)
theorem B792749 : Blo 682313 792749 := bbase (se 3 (by rfl) ⟨148640, by rfl⟩ : syracuseStep 792749 = 297281) (by norm_num)
theorem B1153237 : Blo 682313 1153237 := bbase (se 7 (by rfl) ⟨13514, by rfl⟩ : syracuseStep 1153237 = 27029) (by norm_num)
theorem B1153325 : Blo 682313 1153325 := bbase (se 3 (by rfl) ⟨216248, by rfl⟩ : syracuseStep 1153325 = 432497) (by norm_num)
theorem B1644877 : Blo 682313 1644877 := bbase (se 3 (by rfl) ⟨308414, by rfl⟩ : syracuseStep 1644877 = 616829) (by norm_num)
theorem B1153453 : Blo 682313 1153453 := bbase (se 3 (by rfl) ⟨216272, by rfl⟩ : syracuseStep 1153453 = 432545) (by norm_num)
theorem B1153541 : Blo 682313 1153541 := bbase (se 4 (by rfl) ⟨108144, by rfl⟩ : syracuseStep 1153541 = 216289) (by norm_num)
theorem B1153669 : Blo 682313 1153669 := bbase (se 4 (by rfl) ⟨108156, by rfl⟩ : syracuseStep 1153669 = 216313) (by norm_num)
theorem B1153757 : Blo 682313 1153757 := bbase (se 3 (by rfl) ⟨216329, by rfl⟩ : syracuseStep 1153757 = 432659) (by norm_num)
theorem B1481509 : Blo 682313 1481509 := bbase (se 4 (by rfl) ⟨138891, by rfl⟩ : syracuseStep 1481509 = 277783) (by norm_num)
theorem B1153885 : Blo 682313 1153885 := bbase (se 3 (by rfl) ⟨216353, by rfl⟩ : syracuseStep 1153885 = 432707) (by norm_num)
theorem B1153973 : Blo 682313 1153973 := bbase (se 5 (by rfl) ⟨54092, by rfl⟩ : syracuseStep 1153973 = 108185) (by norm_num)
theorem B3513365 : Blo 682313 3513365 := bbase (se 6 (by rfl) ⟨82344, by rfl⟩ : syracuseStep 3513365 = 164689) (by norm_num)
theorem B1154101 : Blo 682313 1154101 := bbase (se 5 (by rfl) ⟨54098, by rfl⟩ : syracuseStep 1154101 = 108197) (by norm_num)
theorem B1875077 : Blo 682313 1875077 := bbase (se 4 (by rfl) ⟨175788, by rfl⟩ : syracuseStep 1875077 = 351577) (by norm_num)
theorem B1154189 : Blo 682313 1154189 := bbase (se 3 (by rfl) ⟨216410, by rfl⟩ : syracuseStep 1154189 = 432821) (by norm_num)
theorem B1252565 : Blo 682313 1252565 := bbase (se 7 (by rfl) ⟨14678, by rfl⟩ : syracuseStep 1252565 = 29357) (by norm_num)
theorem B1154317 : Blo 682313 1154317 := bbase (se 3 (by rfl) ⟨216434, by rfl⟩ : syracuseStep 1154317 = 432869) (by norm_num)
theorem B1154405 : Blo 682313 1154405 := bbase (se 4 (by rfl) ⟨108225, by rfl⟩ : syracuseStep 1154405 = 216451) (by norm_num)
theorem B2956709 : Blo 682313 2956709 := bbase (se 4 (by rfl) ⟨277191, by rfl⟩ : syracuseStep 2956709 = 554383) (by norm_num)
theorem B3120565 : Blo 682313 3120565 := bbase (se 5 (by rfl) ⟨146276, by rfl⟩ : syracuseStep 3120565 = 292553) (by norm_num)
theorem B1154533 : Blo 682313 1154533 := bbase (se 4 (by rfl) ⟨108237, by rfl⟩ : syracuseStep 1154533 = 216475) (by norm_num)
theorem B1023485 : Blo 682313 1023485 := bbase (se 3 (by rfl) ⟨191903, by rfl⟩ : syracuseStep 1023485 = 383807) (by norm_num)
theorem B1383941 : Blo 682313 1383941 := bbase (se 4 (by rfl) ⟨129744, by rfl⟩ : syracuseStep 1383941 = 259489) (by norm_num)
theorem B1023509 : Blo 682313 1023509 := bbase (se 6 (by rfl) ⟨23988, by rfl⟩ : syracuseStep 1023509 = 47977) (by norm_num)
theorem B1023533 : Blo 682313 1023533 := bbase (se 3 (by rfl) ⟨191912, by rfl⟩ : syracuseStep 1023533 = 383825) (by norm_num)
theorem B1154621 : Blo 682313 1154621 := bbase (se 3 (by rfl) ⟨216491, by rfl⟩ : syracuseStep 1154621 = 432983) (by norm_num)
theorem B1023557 : Blo 682313 1023557 := bbase (se 4 (by rfl) ⟨95958, by rfl⟩ : syracuseStep 1023557 = 191917) (by norm_num)
theorem B1023581 : Blo 682313 1023581 := bbase (se 3 (by rfl) ⟨191921, by rfl⟩ : syracuseStep 1023581 = 383843) (by norm_num)
theorem B728681 : Blo 682313 728681 := bbase (se 2 (by rfl) ⟨273255, by rfl⟩ : syracuseStep 728681 = 546511) (by norm_num)
theorem B1023605 : Blo 682313 1023605 := bbase (se 5 (by rfl) ⟨47981, by rfl⟩ : syracuseStep 1023605 = 95963) (by norm_num)
theorem B1023629 : Blo 682313 1023629 := bbase (se 3 (by rfl) ⟨191930, by rfl⟩ : syracuseStep 1023629 = 383861) (by norm_num)
theorem B1023653 : Blo 682313 1023653 := bbase (se 4 (by rfl) ⟨95967, by rfl⟩ : syracuseStep 1023653 = 191935) (by norm_num)
theorem B1646261 : Blo 682313 1646261 := bbase (se 5 (by rfl) ⟨77168, by rfl⟩ : syracuseStep 1646261 = 154337) (by norm_num)
theorem B1318589 : Blo 682313 1318589 := bbase (se 3 (by rfl) ⟨247235, by rfl⟩ : syracuseStep 1318589 = 494471) (by norm_num)
theorem B1023677 : Blo 682313 1023677 := bbase (se 3 (by rfl) ⟨191939, by rfl⟩ : syracuseStep 1023677 = 383879) (by norm_num)
theorem B1154749 : Blo 682313 1154749 := bbase (se 3 (by rfl) ⟨216515, by rfl⟩ : syracuseStep 1154749 = 433031) (by norm_num)
theorem B1023701 : Blo 682313 1023701 := bbase (se 7 (by rfl) ⟨11996, by rfl⟩ : syracuseStep 1023701 = 23993) (by norm_num)
theorem B1023725 : Blo 682313 1023725 := bbase (se 3 (by rfl) ⟨191948, by rfl⟩ : syracuseStep 1023725 = 383897) (by norm_num)
theorem B1023749 : Blo 682313 1023749 := bbase (se 4 (by rfl) ⟨95976, by rfl⟩ : syracuseStep 1023749 = 191953) (by norm_num)
theorem B1154837 : Blo 682313 1154837 := bbase (se 6 (by rfl) ⟨27066, by rfl⟩ : syracuseStep 1154837 = 54133) (by norm_num)
theorem B3907349 : Blo 682313 3907349 := bbase (se 6 (by rfl) ⟨91578, by rfl⟩ : syracuseStep 3907349 = 183157) (by norm_num)
theorem B1023773 : Blo 682313 1023773 := bbase (se 3 (by rfl) ⟨191957, by rfl⟩ : syracuseStep 1023773 = 383915) (by norm_num)
theorem B1023797 : Blo 682313 1023797 := bbase (se 5 (by rfl) ⟨47990, by rfl⟩ : syracuseStep 1023797 = 95981) (by norm_num)
theorem B1023821 : Blo 682313 1023821 := bbase (se 3 (by rfl) ⟨191966, by rfl⟩ : syracuseStep 1023821 = 383933) (by norm_num)
theorem B728929 : Blo 682313 728929 := bbase (se 2 (by rfl) ⟨273348, by rfl⟩ : syracuseStep 728929 = 546697) (by norm_num)
theorem B1023845 : Blo 682313 1023845 := bbase (se 4 (by rfl) ⟨95985, by rfl⟩ : syracuseStep 1023845 = 191971) (by norm_num)
theorem B1646453 : Blo 682313 1646453 := bbase (se 5 (by rfl) ⟨77177, by rfl⟩ : syracuseStep 1646453 = 154355) (by norm_num)
theorem B1023869 : Blo 682313 1023869 := bbase (se 3 (by rfl) ⟨191975, by rfl⟩ : syracuseStep 1023869 = 383951) (by norm_num)
theorem B1023893 : Blo 682313 1023893 := bbase (se 6 (by rfl) ⟨23997, by rfl⟩ : syracuseStep 1023893 = 47995) (by norm_num)
theorem B1154965 : Blo 682313 1154965 := bbase (se 6 (by rfl) ⟨27069, by rfl⟩ : syracuseStep 1154965 = 54139) (by norm_num)
theorem B1023917 : Blo 682313 1023917 := bbase (se 3 (by rfl) ⟨191984, by rfl⟩ : syracuseStep 1023917 = 383969) (by norm_num)
theorem B1023941 : Blo 682313 1023941 := bbase (se 4 (by rfl) ⟨95994, by rfl⟩ : syracuseStep 1023941 = 191989) (by norm_num)
theorem B2596805 : Blo 682313 2596805 := bbase (se 4 (by rfl) ⟨243450, by rfl⟩ : syracuseStep 2596805 = 486901) (by norm_num)
theorem B1023965 : Blo 682313 1023965 := bbase (se 3 (by rfl) ⟨191993, by rfl⟩ : syracuseStep 1023965 = 383987) (by norm_num)
theorem B1155053 : Blo 682313 1155053 := bbase (se 3 (by rfl) ⟨216572, by rfl⟩ : syracuseStep 1155053 = 433145) (by norm_num)
theorem B1023989 : Blo 682313 1023989 := bbase (se 5 (by rfl) ⟨47999, by rfl⟩ : syracuseStep 1023989 = 95999) (by norm_num)
theorem B1024013 : Blo 682313 1024013 := bbase (se 3 (by rfl) ⟨192002, by rfl⟩ : syracuseStep 1024013 = 384005) (by norm_num)
theorem B1024037 : Blo 682313 1024037 := bbase (se 4 (by rfl) ⟨96003, by rfl⟩ : syracuseStep 1024037 = 192007) (by norm_num)
theorem B1024061 : Blo 682313 1024061 := bbase (se 3 (by rfl) ⟨192011, by rfl⟩ : syracuseStep 1024061 = 384023) (by norm_num)
theorem B1024085 : Blo 682313 1024085 := bbase (se 8 (by rfl) ⟨6000, by rfl⟩ : syracuseStep 1024085 = 12001) (by norm_num)
theorem B7610453 : Blo 682313 7610453 := bbase (se 8 (by rfl) ⟨44592, by rfl⟩ : syracuseStep 7610453 = 89185) (by norm_num)
theorem B1024109 : Blo 682313 1024109 := bbase (se 3 (by rfl) ⟨192020, by rfl⟩ : syracuseStep 1024109 = 384041) (by norm_num)
theorem B1155181 : Blo 682313 1155181 := bbase (se 3 (by rfl) ⟨216596, by rfl⟩ : syracuseStep 1155181 = 433193) (by norm_num)
theorem B1024133 : Blo 682313 1024133 := bbase (se 4 (by rfl) ⟨96012, by rfl⟩ : syracuseStep 1024133 = 192025) (by norm_num)
theorem B1024157 : Blo 682313 1024157 := bbase (se 3 (by rfl) ⟨192029, by rfl⟩ : syracuseStep 1024157 = 384059) (by norm_num)
theorem B1024181 : Blo 682313 1024181 := bbase (se 5 (by rfl) ⟨48008, by rfl⟩ : syracuseStep 1024181 = 96017) (by norm_num)
theorem B1155269 : Blo 682313 1155269 := bbase (se 4 (by rfl) ⟨108306, by rfl⟩ : syracuseStep 1155269 = 216613) (by norm_num)
theorem B1024205 : Blo 682313 1024205 := bbase (se 3 (by rfl) ⟨192038, by rfl⟩ : syracuseStep 1024205 = 384077) (by norm_num)
theorem B1024229 : Blo 682313 1024229 := bbase (se 4 (by rfl) ⟨96021, by rfl⟩ : syracuseStep 1024229 = 192043) (by norm_num)
theorem B2597093 : Blo 682313 2597093 := bbase (se 4 (by rfl) ⟨243477, by rfl⟩ : syracuseStep 2597093 = 486955) (by norm_num)
theorem B1024253 : Blo 682313 1024253 := bbase (se 3 (by rfl) ⟨192047, by rfl⟩ : syracuseStep 1024253 = 384095) (by norm_num)
theorem B729361 : Blo 682313 729361 := bbase (se 2 (by rfl) ⟨273510, by rfl⟩ : syracuseStep 729361 = 547021) (by norm_num)
theorem B1024277 : Blo 682313 1024277 := bbase (se 6 (by rfl) ⟨24006, by rfl⟩ : syracuseStep 1024277 = 48013) (by norm_num)
theorem B1024301 : Blo 682313 1024301 := bbase (se 3 (by rfl) ⟨192056, by rfl⟩ : syracuseStep 1024301 = 384113) (by norm_num)
theorem B1024325 : Blo 682313 1024325 := bbase (se 4 (by rfl) ⟨96030, by rfl⟩ : syracuseStep 1024325 = 192061) (by norm_num)
theorem B1155397 : Blo 682313 1155397 := bbase (se 4 (by rfl) ⟨108318, by rfl⟩ : syracuseStep 1155397 = 216637) (by norm_num)
theorem B729433 : Blo 682313 729433 := bbase (se 2 (by rfl) ⟨273537, by rfl⟩ : syracuseStep 729433 = 547075) (by norm_num)
theorem B1024349 : Blo 682313 1024349 := bbase (se 3 (by rfl) ⟨192065, by rfl⟩ : syracuseStep 1024349 = 384131) (by norm_num)
theorem B1024373 : Blo 682313 1024373 := bbase (se 5 (by rfl) ⟨48017, by rfl⟩ : syracuseStep 1024373 = 96035) (by norm_num)
theorem B3514757 : Blo 682313 3514757 := bbase (se 4 (by rfl) ⟨329508, by rfl⟩ : syracuseStep 3514757 = 659017) (by norm_num)
theorem B1024397 : Blo 682313 1024397 := bbase (se 3 (by rfl) ⟨192074, by rfl⟩ : syracuseStep 1024397 = 384149) (by norm_num)
theorem B1155485 : Blo 682313 1155485 := bbase (se 3 (by rfl) ⟨216653, by rfl⟩ : syracuseStep 1155485 = 433307) (by norm_num)
theorem B1024421 : Blo 682313 1024421 := bbase (se 4 (by rfl) ⟨96039, by rfl⟩ : syracuseStep 1024421 = 192079) (by norm_num)
theorem B1024445 : Blo 682313 1024445 := bbase (se 3 (by rfl) ⟨192083, by rfl⟩ : syracuseStep 1024445 = 384167) (by norm_num)
theorem B1024469 : Blo 682313 1024469 := bbase (se 7 (by rfl) ⟨12005, by rfl⟩ : syracuseStep 1024469 = 24011) (by norm_num)
theorem B1024493 : Blo 682313 1024493 := bbase (se 3 (by rfl) ⟨192092, by rfl⟩ : syracuseStep 1024493 = 384185) (by norm_num)
theorem B1024517 : Blo 682313 1024517 := bbase (se 4 (by rfl) ⟨96048, by rfl⟩ : syracuseStep 1024517 = 192097) (by norm_num)
theorem B2433557 : Blo 682313 2433557 := bbase (se 6 (by rfl) ⟨57036, by rfl⟩ : syracuseStep 2433557 = 114073) (by norm_num)
theorem B1024541 : Blo 682313 1024541 := bbase (se 3 (by rfl) ⟨192101, by rfl⟩ : syracuseStep 1024541 = 384203) (by norm_num)
theorem B1155613 : Blo 682313 1155613 := bbase (se 3 (by rfl) ⟨216677, by rfl⟩ : syracuseStep 1155613 = 433355) (by norm_num)
theorem B1024565 : Blo 682313 1024565 := bbase (se 5 (by rfl) ⟨48026, by rfl⟩ : syracuseStep 1024565 = 96053) (by norm_num)
theorem B1024589 : Blo 682313 1024589 := bbase (se 3 (by rfl) ⟨192110, by rfl⟩ : syracuseStep 1024589 = 384221) (by norm_num)
theorem B1024613 : Blo 682313 1024613 := bbase (se 4 (by rfl) ⟨96057, by rfl⟩ : syracuseStep 1024613 = 192115) (by norm_num)
theorem B1155701 : Blo 682313 1155701 := bbase (se 5 (by rfl) ⟨54173, by rfl⟩ : syracuseStep 1155701 = 108347) (by norm_num)
theorem B1647221 : Blo 682313 1647221 := bbase (se 5 (by rfl) ⟨77213, by rfl⟩ : syracuseStep 1647221 = 154427) (by norm_num)
theorem B1024637 : Blo 682313 1024637 := bbase (se 3 (by rfl) ⟨192119, by rfl⟩ : syracuseStep 1024637 = 384239) (by norm_num)
theorem B1024661 : Blo 682313 1024661 := bbase (se 6 (by rfl) ⟨24015, by rfl⟩ : syracuseStep 1024661 = 48031) (by norm_num)
theorem B926357 : Blo 682313 926357 := bbase (se 6 (by rfl) ⟨21711, by rfl⟩ : syracuseStep 926357 = 43423) (by norm_num)
theorem B1024685 : Blo 682313 1024685 := bbase (se 3 (by rfl) ⟨192128, by rfl⟩ : syracuseStep 1024685 = 384257) (by norm_num)
theorem B5415605 : Blo 682313 5415605 := bbase (se 5 (by rfl) ⟨253856, by rfl⟩ : syracuseStep 5415605 = 507713) (by norm_num)
theorem B1024709 : Blo 682313 1024709 := bbase (se 4 (by rfl) ⟨96066, by rfl⟩ : syracuseStep 1024709 = 192133) (by norm_num)
theorem B729805 : Blo 682313 729805 := bbase (se 3 (by rfl) ⟨136838, by rfl⟩ : syracuseStep 729805 = 273677) (by norm_num)
theorem B1024733 : Blo 682313 1024733 := bbase (se 3 (by rfl) ⟨192137, by rfl⟩ : syracuseStep 1024733 = 384275) (by norm_num)
theorem B1024757 : Blo 682313 1024757 := bbase (se 5 (by rfl) ⟨48035, by rfl⟩ : syracuseStep 1024757 = 96071) (by norm_num)
theorem B1155829 : Blo 682313 1155829 := bbase (se 5 (by rfl) ⟨54179, by rfl⟩ : syracuseStep 1155829 = 108359) (by norm_num)
theorem B1024781 : Blo 682313 1024781 := bbase (se 3 (by rfl) ⟨192146, by rfl⟩ : syracuseStep 1024781 = 384293) (by norm_num)
theorem B1024805 : Blo 682313 1024805 := bbase (se 4 (by rfl) ⟨96075, by rfl⟩ : syracuseStep 1024805 = 192151) (by norm_num)
theorem B1024829 : Blo 682313 1024829 := bbase (se 3 (by rfl) ⟨192155, by rfl⟩ : syracuseStep 1024829 = 384311) (by norm_num)
theorem B1155917 : Blo 682313 1155917 := bbase (se 3 (by rfl) ⟨216734, by rfl⟩ : syracuseStep 1155917 = 433469) (by norm_num)
theorem B1024853 : Blo 682313 1024853 := bbase (se 9 (by rfl) ⟨3002, by rfl⟩ : syracuseStep 1024853 = 6005) (by norm_num)
theorem B1024877 : Blo 682313 1024877 := bbase (se 3 (by rfl) ⟨192164, by rfl⟩ : syracuseStep 1024877 = 384329) (by norm_num)
theorem B1024901 : Blo 682313 1024901 := bbase (se 4 (by rfl) ⟨96084, by rfl⟩ : syracuseStep 1024901 = 192169) (by norm_num)
theorem B1024925 : Blo 682313 1024925 := bbase (se 3 (by rfl) ⟨192173, by rfl⟩ : syracuseStep 1024925 = 384347) (by norm_num)
theorem B1024949 : Blo 682313 1024949 := bbase (se 5 (by rfl) ⟨48044, by rfl⟩ : syracuseStep 1024949 = 96089) (by norm_num)
theorem B3908533 : Blo 682313 3908533 := bbase (se 5 (by rfl) ⟨183212, by rfl⟩ : syracuseStep 3908533 = 366425) (by norm_num)
theorem B1024973 : Blo 682313 1024973 := bbase (se 3 (by rfl) ⟨192182, by rfl⟩ : syracuseStep 1024973 = 384365) (by norm_num)
theorem B1156045 : Blo 682313 1156045 := bbase (se 3 (by rfl) ⟨216758, by rfl⟩ : syracuseStep 1156045 = 433517) (by norm_num)
theorem B1024997 : Blo 682313 1024997 := bbase (se 4 (by rfl) ⟨96093, by rfl⟩ : syracuseStep 1024997 = 192187) (by norm_num)
theorem B1025021 : Blo 682313 1025021 := bbase (se 3 (by rfl) ⟨192191, by rfl⟩ : syracuseStep 1025021 = 384383) (by norm_num)
theorem B1025045 : Blo 682313 1025045 := bbase (se 6 (by rfl) ⟨24024, by rfl⟩ : syracuseStep 1025045 = 48049) (by norm_num)
theorem B1156133 : Blo 682313 1156133 := bbase (se 4 (by rfl) ⟨108387, by rfl⟩ : syracuseStep 1156133 = 216775) (by norm_num)
theorem B1025069 : Blo 682313 1025069 := bbase (se 3 (by rfl) ⟨192200, by rfl⟩ : syracuseStep 1025069 = 384401) (by norm_num)
theorem B2303045 : Blo 682313 2303045 := bbase (se 4 (by rfl) ⟨215910, by rfl⟩ : syracuseStep 2303045 = 431821) (by norm_num)
theorem B1025093 : Blo 682313 1025093 := bbase (se 4 (by rfl) ⟨96102, by rfl⟩ : syracuseStep 1025093 = 192205) (by norm_num)
theorem B730181 : Blo 682313 730181 := bbase (se 4 (by rfl) ⟨68454, by rfl⟩ : syracuseStep 730181 = 136909) (by norm_num)
theorem B1025117 : Blo 682313 1025117 := bbase (se 3 (by rfl) ⟨192209, by rfl⟩ : syracuseStep 1025117 = 384419) (by norm_num)
theorem B1025141 : Blo 682313 1025141 := bbase (se 5 (by rfl) ⟨48053, by rfl⟩ : syracuseStep 1025141 = 96107) (by norm_num)
theorem B1025165 : Blo 682313 1025165 := bbase (se 3 (by rfl) ⟨192218, by rfl⟩ : syracuseStep 1025165 = 384437) (by norm_num)
theorem B730253 : Blo 682313 730253 := bbase (se 3 (by rfl) ⟨136922, by rfl⟩ : syracuseStep 730253 = 273845) (by norm_num)
theorem B1025189 : Blo 682313 1025189 := bbase (se 4 (by rfl) ⟨96111, by rfl⟩ : syracuseStep 1025189 = 192223) (by norm_num)
theorem B1156261 : Blo 682313 1156261 := bbase (se 4 (by rfl) ⟨108399, by rfl⟩ : syracuseStep 1156261 = 216799) (by norm_num)
theorem B1025213 : Blo 682313 1025213 := bbase (se 3 (by rfl) ⟨192227, by rfl⟩ : syracuseStep 1025213 = 384455) (by norm_num)
theorem B1025237 : Blo 682313 1025237 := bbase (se 7 (by rfl) ⟨12014, by rfl⟩ : syracuseStep 1025237 = 24029) (by norm_num)
theorem B3122405 : Blo 682313 3122405 := bbase (se 4 (by rfl) ⟨292725, by rfl⟩ : syracuseStep 3122405 = 585451) (by norm_num)
theorem B1025261 : Blo 682313 1025261 := bbase (se 3 (by rfl) ⟨192236, by rfl⟩ : syracuseStep 1025261 = 384473) (by norm_num)
theorem B1156349 : Blo 682313 1156349 := bbase (se 3 (by rfl) ⟨216815, by rfl⟩ : syracuseStep 1156349 = 433631) (by norm_num)
theorem B1025285 : Blo 682313 1025285 := bbase (se 4 (by rfl) ⟨96120, by rfl⟩ : syracuseStep 1025285 = 192241) (by norm_num)
theorem B3286277 : Blo 682313 3286277 := bbase (se 4 (by rfl) ⟨308088, by rfl⟩ : syracuseStep 3286277 = 616177) (by norm_num)
theorem B4433173 : Blo 682313 4433173 := bbase (se 6 (by rfl) ⟨103902, by rfl⟩ : syracuseStep 4433173 = 207805) (by norm_num)
theorem B1025309 : Blo 682313 1025309 := bbase (se 3 (by rfl) ⟨192245, by rfl⟩ : syracuseStep 1025309 = 384491) (by norm_num)
theorem B1025333 : Blo 682313 1025333 := bbase (se 5 (by rfl) ⟨48062, by rfl⟩ : syracuseStep 1025333 = 96125) (by norm_num)
theorem B2467141 : Blo 682313 2467141 := bbase (se 4 (by rfl) ⟨231294, by rfl⟩ : syracuseStep 2467141 = 462589) (by norm_num)
theorem B730441 : Blo 682313 730441 := bbase (se 2 (by rfl) ⟨273915, by rfl⟩ : syracuseStep 730441 = 547831) (by norm_num)
theorem B1025357 : Blo 682313 1025357 := bbase (se 3 (by rfl) ⟨192254, by rfl⟩ : syracuseStep 1025357 = 384509) (by norm_num)
theorem B1025381 : Blo 682313 1025381 := bbase (se 4 (by rfl) ⟨96129, by rfl⟩ : syracuseStep 1025381 = 192259) (by norm_num)
theorem B1025405 : Blo 682313 1025405 := bbase (se 3 (by rfl) ⟨192263, by rfl⟩ : syracuseStep 1025405 = 384527) (by norm_num)
theorem B1156477 : Blo 682313 1156477 := bbase (se 3 (by rfl) ⟨216839, by rfl⟩ : syracuseStep 1156477 = 433679) (by norm_num)
theorem B2598277 : Blo 682313 2598277 := bbase (se 4 (by rfl) ⟨243588, by rfl⟩ : syracuseStep 2598277 = 487177) (by norm_num)
theorem B1025429 : Blo 682313 1025429 := bbase (se 6 (by rfl) ⟨24033, by rfl⟩ : syracuseStep 1025429 = 48067) (by norm_num)
theorem B1025453 : Blo 682313 1025453 := bbase (se 3 (by rfl) ⟨192272, by rfl⟩ : syracuseStep 1025453 = 384545) (by norm_num)
theorem B1025477 : Blo 682313 1025477 := bbase (se 4 (by rfl) ⟨96138, by rfl⟩ : syracuseStep 1025477 = 192277) (by norm_num)
theorem B1156565 : Blo 682313 1156565 := bbase (se 7 (by rfl) ⟨13553, by rfl⟩ : syracuseStep 1156565 = 27107) (by norm_num)
theorem B1025501 : Blo 682313 1025501 := bbase (se 3 (by rfl) ⟨192281, by rfl⟩ : syracuseStep 1025501 = 384563) (by norm_num)
theorem B2303477 : Blo 682313 2303477 := bbase (se 5 (by rfl) ⟨107975, by rfl⟩ : syracuseStep 2303477 = 215951) (by norm_num)
theorem B1025525 : Blo 682313 1025525 := bbase (se 5 (by rfl) ⟨48071, by rfl⟩ : syracuseStep 1025525 = 96143) (by norm_num)
theorem B730625 : Blo 682313 730625 := bbase (se 2 (by rfl) ⟨273984, by rfl⟩ : syracuseStep 730625 = 547969) (by norm_num)
theorem B1025549 : Blo 682313 1025549 := bbase (se 3 (by rfl) ⟨192290, by rfl⟩ : syracuseStep 1025549 = 384581) (by norm_num)
theorem B1025573 : Blo 682313 1025573 := bbase (se 4 (by rfl) ⟨96147, by rfl⟩ : syracuseStep 1025573 = 192295) (by norm_num)
theorem B1025597 : Blo 682313 1025597 := bbase (se 3 (by rfl) ⟨192299, by rfl⟩ : syracuseStep 1025597 = 384599) (by norm_num)
theorem B1025621 : Blo 682313 1025621 := bbase (se 8 (by rfl) ⟨6009, by rfl⟩ : syracuseStep 1025621 = 12019) (by norm_num)
theorem B1156693 : Blo 682313 1156693 := bbase (se 8 (by rfl) ⟨6777, by rfl⟩ : syracuseStep 1156693 = 13555) (by norm_num)
theorem B1025645 : Blo 682313 1025645 := bbase (se 3 (by rfl) ⟨192308, by rfl⟩ : syracuseStep 1025645 = 384617) (by norm_num)
theorem B1025669 : Blo 682313 1025669 := bbase (se 4 (by rfl) ⟨96156, by rfl⟩ : syracuseStep 1025669 = 192313) (by norm_num)
theorem B1025693 : Blo 682313 1025693 := bbase (se 3 (by rfl) ⟨192317, by rfl⟩ : syracuseStep 1025693 = 384635) (by norm_num)
theorem B1156781 : Blo 682313 1156781 := bbase (se 3 (by rfl) ⟨216896, by rfl⟩ : syracuseStep 1156781 = 433793) (by norm_num)
theorem B1025717 : Blo 682313 1025717 := bbase (se 5 (by rfl) ⟨48080, by rfl⟩ : syracuseStep 1025717 = 96161) (by norm_num)
theorem B2598581 : Blo 682313 2598581 := bbase (se 5 (by rfl) ⟨121808, by rfl⟩ : syracuseStep 2598581 = 243617) (by norm_num)
theorem B1025741 : Blo 682313 1025741 := bbase (se 3 (by rfl) ⟨192326, by rfl⟩ : syracuseStep 1025741 = 384653) (by norm_num)
theorem B1025765 : Blo 682313 1025765 := bbase (se 4 (by rfl) ⟨96165, by rfl⟩ : syracuseStep 1025765 = 192331) (by norm_num)
theorem B1025789 : Blo 682313 1025789 := bbase (se 3 (by rfl) ⟨192335, by rfl⟩ : syracuseStep 1025789 = 384671) (by norm_num)
theorem B1025813 : Blo 682313 1025813 := bbase (se 6 (by rfl) ⟨24042, by rfl⟩ : syracuseStep 1025813 = 48085) (by norm_num)
theorem B1025837 : Blo 682313 1025837 := bbase (se 3 (by rfl) ⟨192344, by rfl⟩ : syracuseStep 1025837 = 384689) (by norm_num)
theorem B1156909 : Blo 682313 1156909 := bbase (se 3 (by rfl) ⟨216920, by rfl⟩ : syracuseStep 1156909 = 433841) (by norm_num)
theorem B1025861 : Blo 682313 1025861 := bbase (se 4 (by rfl) ⟨96174, by rfl⟩ : syracuseStep 1025861 = 192349) (by norm_num)
theorem B1025885 : Blo 682313 1025885 := bbase (se 3 (by rfl) ⟨192353, by rfl⟩ : syracuseStep 1025885 = 384707) (by norm_num)
theorem B1025909 : Blo 682313 1025909 := bbase (se 5 (by rfl) ⟨48089, by rfl⟩ : syracuseStep 1025909 = 96179) (by norm_num)
theorem B1845125 : Blo 682313 1845125 := bbase (se 4 (by rfl) ⟨172980, by rfl⟩ : syracuseStep 1845125 = 345961) (by norm_num)
theorem B1156997 : Blo 682313 1156997 := bbase (se 4 (by rfl) ⟨108468, by rfl⟩ : syracuseStep 1156997 = 216937) (by norm_num)
theorem B1025933 : Blo 682313 1025933 := bbase (se 3 (by rfl) ⟨192362, by rfl⟩ : syracuseStep 1025933 = 384725) (by norm_num)
theorem B2303909 : Blo 682313 2303909 := bbase (se 4 (by rfl) ⟨215991, by rfl⟩ : syracuseStep 2303909 = 431983) (by norm_num)
theorem B1025957 : Blo 682313 1025957 := bbase (se 4 (by rfl) ⟨96183, by rfl⟩ : syracuseStep 1025957 = 192367) (by norm_num)
theorem B1025981 : Blo 682313 1025981 := bbase (se 3 (by rfl) ⟨192371, by rfl⟩ : syracuseStep 1025981 = 384743) (by norm_num)
theorem B1026005 : Blo 682313 1026005 := bbase (se 7 (by rfl) ⟨12023, by rfl⟩ : syracuseStep 1026005 = 24047) (by norm_num)
theorem B1026029 : Blo 682313 1026029 := bbase (se 3 (by rfl) ⟨192380, by rfl⟩ : syracuseStep 1026029 = 384761) (by norm_num)
theorem B1026053 : Blo 682313 1026053 := bbase (se 4 (by rfl) ⟨96192, by rfl⟩ : syracuseStep 1026053 = 192385) (by norm_num)
theorem B1157125 : Blo 682313 1157125 := bbase (se 4 (by rfl) ⟨108480, by rfl⟩ : syracuseStep 1157125 = 216961) (by norm_num)
theorem B1026077 : Blo 682313 1026077 := bbase (se 3 (by rfl) ⟨192389, by rfl⟩ : syracuseStep 1026077 = 384779) (by norm_num)
theorem B1943605 : Blo 682313 1943605 := bbase (se 5 (by rfl) ⟨91106, by rfl⟩ : syracuseStep 1943605 = 182213) (by norm_num)
theorem B1026101 : Blo 682313 1026101 := bbase (se 5 (by rfl) ⟨48098, by rfl⟩ : syracuseStep 1026101 = 96197) (by norm_num)
theorem B1026125 : Blo 682313 1026125 := bbase (se 3 (by rfl) ⟨192398, by rfl⟩ : syracuseStep 1026125 = 384797) (by norm_num)
theorem B1157213 : Blo 682313 1157213 := bbase (se 3 (by rfl) ⟨216977, by rfl⟩ : syracuseStep 1157213 = 433955) (by norm_num)
theorem B1026149 : Blo 682313 1026149 := bbase (se 4 (by rfl) ⟨96201, by rfl⟩ : syracuseStep 1026149 = 192403) (by norm_num)
theorem B1026173 : Blo 682313 1026173 := bbase (se 3 (by rfl) ⟨192407, by rfl⟩ : syracuseStep 1026173 = 384815) (by norm_num)
theorem B1026197 : Blo 682313 1026197 := bbase (se 6 (by rfl) ⟨24051, by rfl⟩ : syracuseStep 1026197 = 48103) (by norm_num)
theorem B1026221 : Blo 682313 1026221 := bbase (se 3 (by rfl) ⟨192416, by rfl⟩ : syracuseStep 1026221 = 384833) (by norm_num)
theorem B1026245 : Blo 682313 1026245 := bbase (se 4 (by rfl) ⟨96210, by rfl⟩ : syracuseStep 1026245 = 192421) (by norm_num)
theorem B1026269 : Blo 682313 1026269 := bbase (se 3 (by rfl) ⟨192425, by rfl⟩ : syracuseStep 1026269 = 384851) (by norm_num)
theorem B1157341 : Blo 682313 1157341 := bbase (se 3 (by rfl) ⟨217001, by rfl⟩ : syracuseStep 1157341 = 434003) (by norm_num)
theorem B731377 : Blo 682313 731377 := bbase (se 2 (by rfl) ⟨274266, by rfl⟩ : syracuseStep 731377 = 548533) (by norm_num)
theorem B1026293 : Blo 682313 1026293 := bbase (se 5 (by rfl) ⟨48107, by rfl⟩ : syracuseStep 1026293 = 96215) (by norm_num)
theorem B1026317 : Blo 682313 1026317 := bbase (se 3 (by rfl) ⟨192434, by rfl⟩ : syracuseStep 1026317 = 384869) (by norm_num)
theorem B1026341 : Blo 682313 1026341 := bbase (se 4 (by rfl) ⟨96219, by rfl⟩ : syracuseStep 1026341 = 192439) (by norm_num)
theorem B1157429 : Blo 682313 1157429 := bbase (se 5 (by rfl) ⟨54254, by rfl⟩ : syracuseStep 1157429 = 108509) (by norm_num)
theorem B731449 : Blo 682313 731449 := bbase (se 2 (by rfl) ⟨274293, by rfl⟩ : syracuseStep 731449 = 548587) (by norm_num)
theorem B1026365 : Blo 682313 1026365 := bbase (se 3 (by rfl) ⟨192443, by rfl⟩ : syracuseStep 1026365 = 384887) (by norm_num)
theorem B2304341 : Blo 682313 2304341 := bbase (se 10 (by rfl) ⟨3375, by rfl⟩ : syracuseStep 2304341 = 6751) (by norm_num)
theorem B1845589 : Blo 682313 1845589 := bbase (se 10 (by rfl) ⟨2703, by rfl⟩ : syracuseStep 1845589 = 5407) (by norm_num)
theorem B1026389 : Blo 682313 1026389 := bbase (se 10 (by rfl) ⟨1503, by rfl⟩ : syracuseStep 1026389 = 3007) (by norm_num)
theorem B1026413 : Blo 682313 1026413 := bbase (se 3 (by rfl) ⟨192452, by rfl⟩ : syracuseStep 1026413 = 384905) (by norm_num)
theorem B1386877 : Blo 682313 1386877 := bbase (se 3 (by rfl) ⟨260039, by rfl⟩ : syracuseStep 1386877 = 520079) (by norm_num)
theorem B1026437 : Blo 682313 1026437 := bbase (se 4 (by rfl) ⟨96228, by rfl⟩ : syracuseStep 1026437 = 192457) (by norm_num)
theorem B1026461 : Blo 682313 1026461 := bbase (se 3 (by rfl) ⟨192461, by rfl⟩ : syracuseStep 1026461 = 384923) (by norm_num)
theorem B1026485 : Blo 682313 1026485 := bbase (se 5 (by rfl) ⟨48116, by rfl⟩ : syracuseStep 1026485 = 96233) (by norm_num)
theorem B1157557 : Blo 682313 1157557 := bbase (se 5 (by rfl) ⟨54260, by rfl⟩ : syracuseStep 1157557 = 108521) (by norm_num)
theorem B1026509 : Blo 682313 1026509 := bbase (se 3 (by rfl) ⟨192470, by rfl⟩ : syracuseStep 1026509 = 384941) (by norm_num)
theorem B1026533 : Blo 682313 1026533 := bbase (se 4 (by rfl) ⟨96237, by rfl⟩ : syracuseStep 1026533 = 192475) (by norm_num)
theorem B731629 : Blo 682313 731629 := bbase (se 3 (by rfl) ⟨137180, by rfl⟩ : syracuseStep 731629 = 274361) (by norm_num)
theorem B1026557 : Blo 682313 1026557 := bbase (se 3 (by rfl) ⟨192479, by rfl⟩ : syracuseStep 1026557 = 384959) (by norm_num)
theorem B1157645 : Blo 682313 1157645 := bbase (se 3 (by rfl) ⟨217058, by rfl⟩ : syracuseStep 1157645 = 434117) (by norm_num)
theorem B1026581 : Blo 682313 1026581 := bbase (se 6 (by rfl) ⟨24060, by rfl⟩ : syracuseStep 1026581 = 48121) (by norm_num)
theorem B1026605 : Blo 682313 1026605 := bbase (se 3 (by rfl) ⟨192488, by rfl⟩ : syracuseStep 1026605 = 384977) (by norm_num)
theorem B1026629 : Blo 682313 1026629 := bbase (se 4 (by rfl) ⟨96246, by rfl⟩ : syracuseStep 1026629 = 192493) (by norm_num)
theorem B1026653 : Blo 682313 1026653 := bbase (se 3 (by rfl) ⟨192497, by rfl⟩ : syracuseStep 1026653 = 384995) (by norm_num)
theorem B2108005 : Blo 682313 2108005 := bbase (se 4 (by rfl) ⟨197625, by rfl⟩ : syracuseStep 2108005 = 395251) (by norm_num)
theorem B1026677 : Blo 682313 1026677 := bbase (se 5 (by rfl) ⟨48125, by rfl⟩ : syracuseStep 1026677 = 96251) (by norm_num)
theorem B1026701 : Blo 682313 1026701 := bbase (se 3 (by rfl) ⟨192506, by rfl⟩ : syracuseStep 1026701 = 385013) (by norm_num)
theorem B1157773 : Blo 682313 1157773 := bbase (se 3 (by rfl) ⟨217082, by rfl⟩ : syracuseStep 1157773 = 434165) (by norm_num)
theorem B1026725 : Blo 682313 1026725 := bbase (se 4 (by rfl) ⟨96255, by rfl⟩ : syracuseStep 1026725 = 192511) (by norm_num)
theorem B2927285 : Blo 682313 2927285 := bbase (se 5 (by rfl) ⟨137216, by rfl⟩ : syracuseStep 2927285 = 274433) (by norm_num)
theorem B1026749 : Blo 682313 1026749 := bbase (se 3 (by rfl) ⟨192515, by rfl⟩ : syracuseStep 1026749 = 385031) (by norm_num)
theorem B1026773 : Blo 682313 1026773 := bbase (se 7 (by rfl) ⟨12032, by rfl⟩ : syracuseStep 1026773 = 24065) (by norm_num)
theorem B1780445 : Blo 682313 1780445 := bbase (se 3 (by rfl) ⟨333833, by rfl⟩ : syracuseStep 1780445 = 667667) (by norm_num)
theorem B1157861 : Blo 682313 1157861 := bbase (se 4 (by rfl) ⟨108549, by rfl⟩ : syracuseStep 1157861 = 217099) (by norm_num)
theorem B1026797 : Blo 682313 1026797 := bbase (se 3 (by rfl) ⟨192524, by rfl⟩ : syracuseStep 1026797 = 385049) (by norm_num)
theorem B2304773 : Blo 682313 2304773 := bbase (se 4 (by rfl) ⟨216072, by rfl⟩ : syracuseStep 2304773 = 432145) (by norm_num)
theorem B1026821 : Blo 682313 1026821 := bbase (se 4 (by rfl) ⟨96264, by rfl⟩ : syracuseStep 1026821 = 192529) (by norm_num)
theorem B1026845 : Blo 682313 1026845 := bbase (se 3 (by rfl) ⟨192533, by rfl⟩ : syracuseStep 1026845 = 385067) (by norm_num)
theorem B1026869 : Blo 682313 1026869 := bbase (se 5 (by rfl) ⟨48134, by rfl⟩ : syracuseStep 1026869 = 96269) (by norm_num)
theorem B1026893 : Blo 682313 1026893 := bbase (se 3 (by rfl) ⟨192542, by rfl⟩ : syracuseStep 1026893 = 385085) (by norm_num)
theorem B1026917 : Blo 682313 1026917 := bbase (se 4 (by rfl) ⟨96273, by rfl⟩ : syracuseStep 1026917 = 192547) (by norm_num)
theorem B1157989 : Blo 682313 1157989 := bbase (se 4 (by rfl) ⟨108561, by rfl⟩ : syracuseStep 1157989 = 217123) (by norm_num)
theorem B1026941 : Blo 682313 1026941 := bbase (se 3 (by rfl) ⟨192551, by rfl⟩ : syracuseStep 1026941 = 385103) (by norm_num)
theorem B1026965 : Blo 682313 1026965 := bbase (se 6 (by rfl) ⟨24069, by rfl⟩ : syracuseStep 1026965 = 48139) (by norm_num)
theorem B732073 : Blo 682313 732073 := bbase (se 2 (by rfl) ⟨274527, by rfl⟩ : syracuseStep 732073 = 549055) (by norm_num)
theorem B1026989 : Blo 682313 1026989 := bbase (se 3 (by rfl) ⟨192560, by rfl⟩ : syracuseStep 1026989 = 385121) (by norm_num)
theorem B1158077 : Blo 682313 1158077 := bbase (se 3 (by rfl) ⟨217139, by rfl⟩ : syracuseStep 1158077 = 434279) (by norm_num)
theorem B1027013 : Blo 682313 1027013 := bbase (se 4 (by rfl) ⟨96282, by rfl⟩ : syracuseStep 1027013 = 192565) (by norm_num)
theorem B2927573 : Blo 682313 2927573 := bbase (se 7 (by rfl) ⟨34307, by rfl⟩ : syracuseStep 2927573 = 68615) (by norm_num)
theorem B1027037 : Blo 682313 1027037 := bbase (se 3 (by rfl) ⟨192569, by rfl⟩ : syracuseStep 1027037 = 385139) (by norm_num)
theorem B1027061 : Blo 682313 1027061 := bbase (se 5 (by rfl) ⟨48143, by rfl⟩ : syracuseStep 1027061 = 96287) (by norm_num)
theorem B1027085 : Blo 682313 1027085 := bbase (se 3 (by rfl) ⟨192578, by rfl⟩ : syracuseStep 1027085 = 385157) (by norm_num)
theorem B1027109 : Blo 682313 1027109 := bbase (se 4 (by rfl) ⟨96291, by rfl⟩ : syracuseStep 1027109 = 192583) (by norm_num)
theorem B732197 : Blo 682313 732197 := bbase (se 4 (by rfl) ⟨68643, by rfl⟩ : syracuseStep 732197 = 137287) (by norm_num)
theorem B1027133 : Blo 682313 1027133 := bbase (se 3 (by rfl) ⟨192587, by rfl⟩ : syracuseStep 1027133 = 385175) (by norm_num)
theorem B1027157 : Blo 682313 1027157 := bbase (se 8 (by rfl) ⟨6018, by rfl⟩ : syracuseStep 1027157 = 12037) (by norm_num)
theorem B1027181 : Blo 682313 1027181 := bbase (se 3 (by rfl) ⟨192596, by rfl⟩ : syracuseStep 1027181 = 385193) (by norm_num)
theorem B1027205 : Blo 682313 1027205 := bbase (se 4 (by rfl) ⟨96300, by rfl⟩ : syracuseStep 1027205 = 192601) (by norm_num)
theorem B1027229 : Blo 682313 1027229 := bbase (se 3 (by rfl) ⟨192605, by rfl⟩ : syracuseStep 1027229 = 385211) (by norm_num)
theorem B2305205 : Blo 682313 2305205 := bbase (se 5 (by rfl) ⟨108056, by rfl⟩ : syracuseStep 2305205 = 216113) (by norm_num)
theorem B1027253 : Blo 682313 1027253 := bbase (se 5 (by rfl) ⟨48152, by rfl⟩ : syracuseStep 1027253 = 96305) (by norm_num)
theorem B1027277 : Blo 682313 1027277 := bbase (se 3 (by rfl) ⟨192614, by rfl⟩ : syracuseStep 1027277 = 385229) (by norm_num)
theorem B1027301 : Blo 682313 1027301 := bbase (se 4 (by rfl) ⟨96309, by rfl⟩ : syracuseStep 1027301 = 192619) (by norm_num)
theorem B1027325 : Blo 682313 1027325 := bbase (se 3 (by rfl) ⟨192623, by rfl⟩ : syracuseStep 1027325 = 385247) (by norm_num)
theorem B1027349 : Blo 682313 1027349 := bbase (se 6 (by rfl) ⟨24078, by rfl⟩ : syracuseStep 1027349 = 48157) (by norm_num)
theorem B732449 : Blo 682313 732449 := bbase (se 2 (by rfl) ⟨274668, by rfl⟩ : syracuseStep 732449 = 549337) (by norm_num)
theorem B1027373 : Blo 682313 1027373 := bbase (se 3 (by rfl) ⟨192632, by rfl⟩ : syracuseStep 1027373 = 385265) (by norm_num)
theorem B1027397 : Blo 682313 1027397 := bbase (se 4 (by rfl) ⟨96318, by rfl⟩ : syracuseStep 1027397 = 192637) (by norm_num)
theorem B863561 : Blo 682313 863561 := bbase (se 2 (by rfl) ⟨323835, by rfl⟩ : syracuseStep 863561 = 647671) (by norm_num)
theorem B1027421 : Blo 682313 1027421 := bbase (se 3 (by rfl) ⟨192641, by rfl⟩ : syracuseStep 1027421 = 385283) (by norm_num)
theorem B1027445 : Blo 682313 1027445 := bbase (se 5 (by rfl) ⟨48161, by rfl⟩ : syracuseStep 1027445 = 96323) (by norm_num)
theorem B863617 : Blo 682313 863617 := bbase (se 2 (by rfl) ⟨323856, by rfl⟩ : syracuseStep 863617 = 647713) (by norm_num)
theorem B1027469 : Blo 682313 1027469 := bbase (se 3 (by rfl) ⟨192650, by rfl⟩ : syracuseStep 1027469 = 385301) (by norm_num)
theorem B1027493 : Blo 682313 1027493 := bbase (se 4 (by rfl) ⟨96327, by rfl⟩ : syracuseStep 1027493 = 192655) (by norm_num)
theorem B4926901 : Blo 682313 4926901 := bbase (se 5 (by rfl) ⟨230948, by rfl⟩ : syracuseStep 4926901 = 461897) (by norm_num)
theorem B1027517 : Blo 682313 1027517 := bbase (se 3 (by rfl) ⟨192659, by rfl⟩ : syracuseStep 1027517 = 385319) (by norm_num)
theorem B1027541 : Blo 682313 1027541 := bbase (se 7 (by rfl) ⟨12041, by rfl⟩ : syracuseStep 1027541 = 24083) (by norm_num)
theorem B863713 : Blo 682313 863713 := bbase (se 2 (by rfl) ⟨323892, by rfl⟩ : syracuseStep 863713 = 647785) (by norm_num)
theorem B1027565 : Blo 682313 1027565 := bbase (se 3 (by rfl) ⟨192668, by rfl⟩ : syracuseStep 1027565 = 385337) (by norm_num)
theorem B1027589 : Blo 682313 1027589 := bbase (se 4 (by rfl) ⟨96336, by rfl⟩ : syracuseStep 1027589 = 192673) (by norm_num)
theorem B1945109 : Blo 682313 1945109 := bbase (se 6 (by rfl) ⟨45588, by rfl⟩ : syracuseStep 1945109 = 91177) (by norm_num)
theorem B1027613 : Blo 682313 1027613 := bbase (se 3 (by rfl) ⟨192677, by rfl⟩ : syracuseStep 1027613 = 385355) (by norm_num)
theorem B1027637 : Blo 682313 1027637 := bbase (se 5 (by rfl) ⟨48170, by rfl⟩ : syracuseStep 1027637 = 96341) (by norm_num)
theorem B1093189 : Blo 682313 1093189 := bbase (se 4 (by rfl) ⟨102486, by rfl⟩ : syracuseStep 1093189 = 204973) (by norm_num)
theorem B1027661 : Blo 682313 1027661 := bbase (se 3 (by rfl) ⟨192686, by rfl⟩ : syracuseStep 1027661 = 385373) (by norm_num)
theorem B2305637 : Blo 682313 2305637 := bbase (se 4 (by rfl) ⟨216153, by rfl⟩ : syracuseStep 2305637 = 432307) (by norm_num)
theorem B1027685 : Blo 682313 1027685 := bbase (se 4 (by rfl) ⟨96345, by rfl⟩ : syracuseStep 1027685 = 192691) (by norm_num)
theorem B1027709 : Blo 682313 1027709 := bbase (se 3 (by rfl) ⟨192695, by rfl⟩ : syracuseStep 1027709 = 385391) (by norm_num)
theorem B863885 : Blo 682313 863885 := bbase (se 3 (by rfl) ⟨161978, by rfl⟩ : syracuseStep 863885 = 323957) (by norm_num)
theorem B1027733 : Blo 682313 1027733 := bbase (se 6 (by rfl) ⟨24087, by rfl⟩ : syracuseStep 1027733 = 48175) (by norm_num)
theorem B1027757 : Blo 682313 1027757 := bbase (se 3 (by rfl) ⟨192704, by rfl⟩ : syracuseStep 1027757 = 385409) (by norm_num)
theorem B863941 : Blo 682313 863941 := bbase (se 4 (by rfl) ⟨80994, by rfl⟩ : syracuseStep 863941 = 161989) (by norm_num)
theorem B1027781 : Blo 682313 1027781 := bbase (se 4 (by rfl) ⟨96354, by rfl⟩ : syracuseStep 1027781 = 192709) (by norm_num)
theorem B2928325 : Blo 682313 2928325 := bbase (se 4 (by rfl) ⟨274530, by rfl⟩ : syracuseStep 2928325 = 549061) (by norm_num)
theorem B1027805 : Blo 682313 1027805 := bbase (se 3 (by rfl) ⟨192713, by rfl⟩ : syracuseStep 1027805 = 385427) (by norm_num)
theorem B732893 : Blo 682313 732893 := bbase (se 3 (by rfl) ⟨137417, by rfl⟩ : syracuseStep 732893 = 274835) (by norm_num)
theorem B2600693 : Blo 682313 2600693 := bbase (se 5 (by rfl) ⟨121907, by rfl⟩ : syracuseStep 2600693 = 243815) (by norm_num)
theorem B1027829 : Blo 682313 1027829 := bbase (se 5 (by rfl) ⟨48179, by rfl⟩ : syracuseStep 1027829 = 96359) (by norm_num)
theorem B1027853 : Blo 682313 1027853 := bbase (se 3 (by rfl) ⟨192722, by rfl⟩ : syracuseStep 1027853 = 385445) (by norm_num)
theorem B5844757 : Blo 682313 5844757 := bbase (se 6 (by rfl) ⟨136986, by rfl⟩ : syracuseStep 5844757 = 273973) (by norm_num)
theorem B864037 : Blo 682313 864037 := bbase (se 4 (by rfl) ⟨81003, by rfl⟩ : syracuseStep 864037 = 162007) (by norm_num)
theorem B1027877 : Blo 682313 1027877 := bbase (se 4 (by rfl) ⟨96363, by rfl⟩ : syracuseStep 1027877 = 192727) (by norm_num)
theorem B1027901 : Blo 682313 1027901 := bbase (se 3 (by rfl) ⟨192731, by rfl⟩ : syracuseStep 1027901 = 385463) (by norm_num)
theorem B1027925 : Blo 682313 1027925 := bbase (se 9 (by rfl) ⟨3011, by rfl⟩ : syracuseStep 1027925 = 6023) (by norm_num)
theorem B1027949 : Blo 682313 1027949 := bbase (se 3 (by rfl) ⟨192740, by rfl⟩ : syracuseStep 1027949 = 385481) (by norm_num)
theorem B1027973 : Blo 682313 1027973 := bbase (se 4 (by rfl) ⟨96372, by rfl⟩ : syracuseStep 1027973 = 192745) (by norm_num)
theorem B1027997 : Blo 682313 1027997 := bbase (se 3 (by rfl) ⟨192749, by rfl⟩ : syracuseStep 1027997 = 385499) (by norm_num)
theorem B2469797 : Blo 682313 2469797 := bbase (se 4 (by rfl) ⟨231543, by rfl⟩ : syracuseStep 2469797 = 463087) (by norm_num)
theorem B1028021 : Blo 682313 1028021 := bbase (se 5 (by rfl) ⟨48188, by rfl⟩ : syracuseStep 1028021 = 96377) (by norm_num)
theorem B1028045 : Blo 682313 1028045 := bbase (se 3 (by rfl) ⟨192758, by rfl⟩ : syracuseStep 1028045 = 385517) (by norm_num)
theorem B864209 : Blo 682313 864209 := bbase (se 2 (by rfl) ⟨324078, by rfl⟩ : syracuseStep 864209 = 648157) (by norm_num)
theorem B3289061 : Blo 682313 3289061 := bbase (se 4 (by rfl) ⟨308349, by rfl⟩ : syracuseStep 3289061 = 616699) (by norm_num)
theorem B1028069 : Blo 682313 1028069 := bbase (se 4 (by rfl) ⟨96381, by rfl⟩ : syracuseStep 1028069 = 192763) (by norm_num)
theorem B1028093 : Blo 682313 1028093 := bbase (se 3 (by rfl) ⟨192767, by rfl⟩ : syracuseStep 1028093 = 385535) (by norm_num)
theorem B864265 : Blo 682313 864265 := bbase (se 2 (by rfl) ⟨324099, by rfl⟩ : syracuseStep 864265 = 648199) (by norm_num)
theorem B2306069 : Blo 682313 2306069 := bbase (se 6 (by rfl) ⟨54048, by rfl⟩ : syracuseStep 2306069 = 108097) (by norm_num)
theorem B2600981 : Blo 682313 2600981 := bbase (se 6 (by rfl) ⟨60960, by rfl⟩ : syracuseStep 2600981 = 121921) (by norm_num)
theorem B1028117 : Blo 682313 1028117 := bbase (se 6 (by rfl) ⟨24096, by rfl⟩ : syracuseStep 1028117 = 48193) (by norm_num)
theorem B1028141 : Blo 682313 1028141 := bbase (se 3 (by rfl) ⟨192776, by rfl⟩ : syracuseStep 1028141 = 385553) (by norm_num)
theorem B1028165 : Blo 682313 1028165 := bbase (se 4 (by rfl) ⟨96390, by rfl⟩ : syracuseStep 1028165 = 192781) (by norm_num)
theorem B1028189 : Blo 682313 1028189 := bbase (se 3 (by rfl) ⟨192785, by rfl⟩ : syracuseStep 1028189 = 385571) (by norm_num)
theorem B864361 : Blo 682313 864361 := bbase (se 2 (by rfl) ⟨324135, by rfl⟩ : syracuseStep 864361 = 648271) (by norm_num)
theorem B1028213 : Blo 682313 1028213 := bbase (se 5 (by rfl) ⟨48197, by rfl⟩ : syracuseStep 1028213 = 96395) (by norm_num)
theorem B1028237 : Blo 682313 1028237 := bbase (se 3 (by rfl) ⟨192794, by rfl⟩ : syracuseStep 1028237 = 385589) (by norm_num)
theorem B1847461 : Blo 682313 1847461 := bbase (se 4 (by rfl) ⟨173199, by rfl⟩ : syracuseStep 1847461 = 346399) (by norm_num)
theorem B1028261 : Blo 682313 1028261 := bbase (se 4 (by rfl) ⟨96399, by rfl⟩ : syracuseStep 1028261 = 192799) (by norm_num)
theorem B1028285 : Blo 682313 1028285 := bbase (se 3 (by rfl) ⟨192803, by rfl⟩ : syracuseStep 1028285 = 385607) (by norm_num)
theorem B2470085 : Blo 682313 2470085 := bbase (se 4 (by rfl) ⟨231570, by rfl⟩ : syracuseStep 2470085 = 463141) (by norm_num)
theorem B1028309 : Blo 682313 1028309 := bbase (se 7 (by rfl) ⟨12050, by rfl⟩ : syracuseStep 1028309 = 24101) (by norm_num)
theorem B1028333 : Blo 682313 1028333 := bbase (se 3 (by rfl) ⟨192812, by rfl⟩ : syracuseStep 1028333 = 385625) (by norm_num)
theorem B1028357 : Blo 682313 1028357 := bbase (se 4 (by rfl) ⟨96408, by rfl⟩ : syracuseStep 1028357 = 192817) (by norm_num)
theorem B864533 : Blo 682313 864533 := bbase (se 6 (by rfl) ⟨20262, by rfl⟩ : syracuseStep 864533 = 40525) (by norm_num)
theorem B1028381 : Blo 682313 1028381 := bbase (se 3 (by rfl) ⟨192821, by rfl⟩ : syracuseStep 1028381 = 385643) (by norm_num)
theorem B1028405 : Blo 682313 1028405 := bbase (se 5 (by rfl) ⟨48206, by rfl⟩ : syracuseStep 1028405 = 96413) (by norm_num)
theorem B864589 : Blo 682313 864589 := bbase (se 3 (by rfl) ⟨162110, by rfl⟩ : syracuseStep 864589 = 324221) (by norm_num)
theorem B1028429 : Blo 682313 1028429 := bbase (se 3 (by rfl) ⟨192830, by rfl⟩ : syracuseStep 1028429 = 385661) (by norm_num)
theorem B1028453 : Blo 682313 1028453 := bbase (se 4 (by rfl) ⟨96417, by rfl⟩ : syracuseStep 1028453 = 192835) (by norm_num)
theorem B1028477 : Blo 682313 1028477 := bbase (se 3 (by rfl) ⟨192839, by rfl⟩ : syracuseStep 1028477 = 385679) (by norm_num)
theorem B1028501 : Blo 682313 1028501 := bbase (se 6 (by rfl) ⟨24105, by rfl⟩ : syracuseStep 1028501 = 48211) (by norm_num)
theorem B2929061 : Blo 682313 2929061 := bbase (se 4 (by rfl) ⟨274599, by rfl⟩ : syracuseStep 2929061 = 549199) (by norm_num)
theorem B864685 : Blo 682313 864685 := bbase (se 3 (by rfl) ⟨162128, by rfl⟩ : syracuseStep 864685 = 324257) (by norm_num)
theorem B1028525 : Blo 682313 1028525 := bbase (se 3 (by rfl) ⟨192848, by rfl⟩ : syracuseStep 1028525 = 385697) (by norm_num)
theorem B2306501 : Blo 682313 2306501 := bbase (se 4 (by rfl) ⟨216234, by rfl⟩ : syracuseStep 2306501 = 432469) (by norm_num)
theorem B1028549 : Blo 682313 1028549 := bbase (se 4 (by rfl) ⟨96426, by rfl⟩ : syracuseStep 1028549 = 192853) (by norm_num)
theorem B1028573 : Blo 682313 1028573 := bbase (se 3 (by rfl) ⟨192857, by rfl⟩ : syracuseStep 1028573 = 385715) (by norm_num)
theorem B1028597 : Blo 682313 1028597 := bbase (se 5 (by rfl) ⟨48215, by rfl⟩ : syracuseStep 1028597 = 96431) (by norm_num)
theorem B1028621 : Blo 682313 1028621 := bbase (se 3 (by rfl) ⟨192866, by rfl⟩ : syracuseStep 1028621 = 385733) (by norm_num)
theorem B1028645 : Blo 682313 1028645 := bbase (se 4 (by rfl) ⟨96435, by rfl⟩ : syracuseStep 1028645 = 192871) (by norm_num)
theorem B1028669 : Blo 682313 1028669 := bbase (se 3 (by rfl) ⟨192875, by rfl⟩ : syracuseStep 1028669 = 385751) (by norm_num)
theorem B1847893 : Blo 682313 1847893 := bbase (se 8 (by rfl) ⟨10827, by rfl⟩ : syracuseStep 1847893 = 21655) (by norm_num)
theorem B1028693 : Blo 682313 1028693 := bbase (se 8 (by rfl) ⟨6027, by rfl⟩ : syracuseStep 1028693 = 12055) (by norm_num)
theorem B864857 : Blo 682313 864857 := bbase (se 2 (by rfl) ⟨324321, by rfl⟩ : syracuseStep 864857 = 648643) (by norm_num)
theorem B1028717 : Blo 682313 1028717 := bbase (se 3 (by rfl) ⟨192884, by rfl⟩ : syracuseStep 1028717 = 385769) (by norm_num)
theorem B1028741 : Blo 682313 1028741 := bbase (se 4 (by rfl) ⟨96444, by rfl⟩ : syracuseStep 1028741 = 192889) (by norm_num)
theorem B864913 : Blo 682313 864913 := bbase (se 2 (by rfl) ⟨324342, by rfl⟩ : syracuseStep 864913 = 648685) (by norm_num)
theorem B1028765 : Blo 682313 1028765 := bbase (se 3 (by rfl) ⟨192893, by rfl⟩ : syracuseStep 1028765 = 385787) (by norm_num)
theorem B1028789 : Blo 682313 1028789 := bbase (se 5 (by rfl) ⟨48224, by rfl⟩ : syracuseStep 1028789 = 96449) (by norm_num)
theorem B1028813 : Blo 682313 1028813 := bbase (se 3 (by rfl) ⟨192902, by rfl⟩ : syracuseStep 1028813 = 385805) (by norm_num)
theorem B1028837 : Blo 682313 1028837 := bbase (se 4 (by rfl) ⟨96453, by rfl⟩ : syracuseStep 1028837 = 192907) (by norm_num)
theorem B1094381 : Blo 682313 1094381 := bbase (se 3 (by rfl) ⟨205196, by rfl⟩ : syracuseStep 1094381 = 410393) (by norm_num)
theorem B865009 : Blo 682313 865009 := bbase (se 2 (by rfl) ⟨324378, by rfl⟩ : syracuseStep 865009 = 648757) (by norm_num)
theorem B1028861 : Blo 682313 1028861 := bbase (se 3 (by rfl) ⟨192911, by rfl⟩ : syracuseStep 1028861 = 385823) (by norm_num)
theorem B1389325 : Blo 682313 1389325 := bbase (se 3 (by rfl) ⟨260498, by rfl⟩ : syracuseStep 1389325 = 520997) (by norm_num)
theorem B1028885 : Blo 682313 1028885 := bbase (se 6 (by rfl) ⟨24114, by rfl⟩ : syracuseStep 1028885 = 48229) (by norm_num)
theorem B1028909 : Blo 682313 1028909 := bbase (se 3 (by rfl) ⟨192920, by rfl⟩ : syracuseStep 1028909 = 385841) (by norm_num)
theorem B1028933 : Blo 682313 1028933 := bbase (se 4 (by rfl) ⟨96462, by rfl⟩ : syracuseStep 1028933 = 192925) (by norm_num)
theorem B6566741 : Blo 682313 6566741 := bbase (se 9 (by rfl) ⟨19238, by rfl⟩ : syracuseStep 6566741 = 38477) (by norm_num)
theorem B1028957 : Blo 682313 1028957 := bbase (se 3 (by rfl) ⟨192929, by rfl⟩ : syracuseStep 1028957 = 385859) (by norm_num)
theorem B2306933 : Blo 682313 2306933 := bbase (se 5 (by rfl) ⟨108137, by rfl⟩ : syracuseStep 2306933 = 216275) (by norm_num)
theorem B1028981 : Blo 682313 1028981 := bbase (se 5 (by rfl) ⟨48233, by rfl⟩ : syracuseStep 1028981 = 96467) (by norm_num)
theorem B1029005 : Blo 682313 1029005 := bbase (se 3 (by rfl) ⟨192938, by rfl⟩ : syracuseStep 1029005 = 385877) (by norm_num)
theorem B865181 : Blo 682313 865181 := bbase (se 3 (by rfl) ⟨162221, by rfl⟩ : syracuseStep 865181 = 324443) (by norm_num)
theorem B1029029 : Blo 682313 1029029 := bbase (se 4 (by rfl) ⟨96471, by rfl⟩ : syracuseStep 1029029 = 192943) (by norm_num)
theorem B1094573 : Blo 682313 1094573 := bbase (se 3 (by rfl) ⟨205232, by rfl⟩ : syracuseStep 1094573 = 410465) (by norm_num)
theorem B1029053 : Blo 682313 1029053 := bbase (se 3 (by rfl) ⟨192947, by rfl⟩ : syracuseStep 1029053 = 385895) (by norm_num)
theorem B865237 : Blo 682313 865237 := bbase (se 7 (by rfl) ⟨10139, by rfl⟩ : syracuseStep 865237 = 20279) (by norm_num)
theorem B1029077 : Blo 682313 1029077 := bbase (se 7 (by rfl) ⟨12059, by rfl⟩ : syracuseStep 1029077 = 24119) (by norm_num)
theorem B1029101 : Blo 682313 1029101 := bbase (se 3 (by rfl) ⟨192956, by rfl⟩ : syracuseStep 1029101 = 385913) (by norm_num)
theorem B1782773 : Blo 682313 1782773 := bbase (se 5 (by rfl) ⟨83567, by rfl⟩ : syracuseStep 1782773 = 167135) (by norm_num)
theorem B1029125 : Blo 682313 1029125 := bbase (se 4 (by rfl) ⟨96480, by rfl⟩ : syracuseStep 1029125 = 192961) (by norm_num)
theorem B1029149 : Blo 682313 1029149 := bbase (se 3 (by rfl) ⟨192965, by rfl⟩ : syracuseStep 1029149 = 385931) (by norm_num)
theorem B2470949 : Blo 682313 2470949 := bbase (se 4 (by rfl) ⟨231651, by rfl⟩ : syracuseStep 2470949 = 463303) (by norm_num)
theorem B865333 : Blo 682313 865333 := bbase (se 5 (by rfl) ⟨40562, by rfl⟩ : syracuseStep 865333 = 81125) (by norm_num)
theorem B1029173 : Blo 682313 1029173 := bbase (se 5 (by rfl) ⟨48242, by rfl⟩ : syracuseStep 1029173 = 96485) (by norm_num)
theorem B1946693 : Blo 682313 1946693 := bbase (se 4 (by rfl) ⟨182502, by rfl⟩ : syracuseStep 1946693 = 365005) (by norm_num)
theorem B1782853 : Blo 682313 1782853 := bbase (se 4 (by rfl) ⟨167142, by rfl⟩ : syracuseStep 1782853 = 334285) (by norm_num)
theorem B1029197 : Blo 682313 1029197 := bbase (se 3 (by rfl) ⟨192974, by rfl⟩ : syracuseStep 1029197 = 385949) (by norm_num)
theorem B1029221 : Blo 682313 1029221 := bbase (se 4 (by rfl) ⟨96489, by rfl⟩ : syracuseStep 1029221 = 192979) (by norm_num)
theorem B1029245 : Blo 682313 1029245 := bbase (se 3 (by rfl) ⟨192983, by rfl⟩ : syracuseStep 1029245 = 385967) (by norm_num)
theorem B1029269 : Blo 682313 1029269 := bbase (se 6 (by rfl) ⟨24123, by rfl⟩ : syracuseStep 1029269 = 48247) (by norm_num)
theorem B1029293 : Blo 682313 1029293 := bbase (se 3 (by rfl) ⟨192992, by rfl⟩ : syracuseStep 1029293 = 385985) (by norm_num)
theorem B2602165 : Blo 682313 2602165 := bbase (se 5 (by rfl) ⟨121976, by rfl⟩ : syracuseStep 2602165 = 243953) (by norm_num)
theorem B1029317 : Blo 682313 1029317 := bbase (se 4 (by rfl) ⟨96498, by rfl⟩ : syracuseStep 1029317 = 192997) (by norm_num)
theorem B1029341 : Blo 682313 1029341 := bbase (se 3 (by rfl) ⟨193001, by rfl⟩ : syracuseStep 1029341 = 386003) (by norm_num)
theorem B865505 : Blo 682313 865505 := bbase (se 2 (by rfl) ⟨324564, by rfl⟩ : syracuseStep 865505 = 649129) (by norm_num)
theorem B1029365 : Blo 682313 1029365 := bbase (se 5 (by rfl) ⟨48251, by rfl⟩ : syracuseStep 1029365 = 96503) (by norm_num)
theorem B1029389 : Blo 682313 1029389 := bbase (se 3 (by rfl) ⟨193010, by rfl⟩ : syracuseStep 1029389 = 386021) (by norm_num)
theorem B865561 : Blo 682313 865561 := bbase (se 2 (by rfl) ⟨324585, by rfl⟩ : syracuseStep 865561 = 649171) (by norm_num)
theorem B2307365 : Blo 682313 2307365 := bbase (se 4 (by rfl) ⟨216315, by rfl⟩ : syracuseStep 2307365 = 432631) (by norm_num)
theorem B1029413 : Blo 682313 1029413 := bbase (se 4 (by rfl) ⟨96507, by rfl⟩ : syracuseStep 1029413 = 193015) (by norm_num)
theorem B5190965 : Blo 682313 5190965 := bbase (se 5 (by rfl) ⟨243326, by rfl⟩ : syracuseStep 5190965 = 486653) (by norm_num)
theorem B1029437 : Blo 682313 1029437 := bbase (se 3 (by rfl) ⟨193019, by rfl⟩ : syracuseStep 1029437 = 386039) (by norm_num)
theorem B1029461 : Blo 682313 1029461 := bbase (se 13 (by rfl) ⟨188, by rfl⟩ : syracuseStep 1029461 = 377) (by norm_num)
theorem B3454325 : Blo 682313 3454325 := bbase (se 5 (by rfl) ⟨161921, by rfl⟩ : syracuseStep 3454325 = 323843) (by norm_num)
theorem B865657 : Blo 682313 865657 := bbase (se 2 (by rfl) ⟨324621, by rfl⟩ : syracuseStep 865657 = 649243) (by norm_num)
theorem B2602469 : Blo 682313 2602469 := bbase (se 4 (by rfl) ⟨243981, by rfl⟩ : syracuseStep 2602469 = 487963) (by norm_num)
theorem B865829 : Blo 682313 865829 := bbase (se 4 (by rfl) ⟨81171, by rfl⟩ : syracuseStep 865829 = 162343) (by norm_num)
theorem B865885 : Blo 682313 865885 := bbase (se 3 (by rfl) ⟨162353, by rfl⟩ : syracuseStep 865885 = 324707) (by norm_num)
theorem B2471525 : Blo 682313 2471525 := bbase (se 4 (by rfl) ⟨231705, by rfl⟩ : syracuseStep 2471525 = 463411) (by norm_num)
theorem B767605 : Blo 682313 767605 := bbase (se 5 (by rfl) ⟨35981, by rfl⟩ : syracuseStep 767605 = 71963) (by norm_num)
theorem B5060245 : Blo 682313 5060245 := bbase (se 6 (by rfl) ⟨118599, by rfl⟩ : syracuseStep 5060245 = 237199) (by norm_num)
theorem B767641 : Blo 682313 767641 := bbase (se 2 (by rfl) ⟨287865, by rfl⟩ : syracuseStep 767641 = 575731) (by norm_num)
theorem B767677 : Blo 682313 767677 := bbase (se 3 (by rfl) ⟨143939, by rfl⟩ : syracuseStep 767677 = 287879) (by norm_num)
theorem B865981 : Blo 682313 865981 := bbase (se 3 (by rfl) ⟨162371, by rfl⟩ : syracuseStep 865981 = 324743) (by norm_num)
theorem B2307797 : Blo 682313 2307797 := bbase (se 7 (by rfl) ⟨27044, by rfl⟩ : syracuseStep 2307797 = 54089) (by norm_num)
theorem B5846741 : Blo 682313 5846741 := bbase (se 7 (by rfl) ⟨68516, by rfl⟩ : syracuseStep 5846741 = 137033) (by norm_num)
theorem B767713 : Blo 682313 767713 := bbase (se 2 (by rfl) ⟨287892, by rfl⟩ : syracuseStep 767713 = 575785) (by norm_num)
theorem B1947365 : Blo 682313 1947365 := bbase (se 4 (by rfl) ⟨182565, by rfl⟩ : syracuseStep 1947365 = 365131) (by norm_num)
theorem B767749 : Blo 682313 767749 := bbase (se 4 (by rfl) ⟨71976, by rfl⟩ : syracuseStep 767749 = 143953) (by norm_num)
theorem B767785 : Blo 682313 767785 := bbase (se 2 (by rfl) ⟨287919, by rfl⟩ : syracuseStep 767785 = 575839) (by norm_num)
theorem B767821 : Blo 682313 767821 := bbase (se 3 (by rfl) ⟨143966, by rfl⟩ : syracuseStep 767821 = 287933) (by norm_num)
theorem B866153 : Blo 682313 866153 := bbase (se 2 (by rfl) ⟨324807, by rfl⟩ : syracuseStep 866153 = 649615) (by norm_num)
theorem B767857 : Blo 682313 767857 := bbase (se 2 (by rfl) ⟨287946, by rfl⟩ : syracuseStep 767857 = 575893) (by norm_num)
theorem B767893 : Blo 682313 767893 := bbase (se 6 (by rfl) ⟨17997, by rfl⟩ : syracuseStep 767893 = 35995) (by norm_num)
theorem B866209 : Blo 682313 866209 := bbase (se 2 (by rfl) ⟨324828, by rfl⟩ : syracuseStep 866209 = 649657) (by norm_num)
theorem B767929 : Blo 682313 767929 := bbase (se 2 (by rfl) ⟨287973, by rfl⟩ : syracuseStep 767929 = 575947) (by norm_num)
theorem B767965 : Blo 682313 767965 := bbase (se 3 (by rfl) ⟨143993, by rfl⟩ : syracuseStep 767965 = 287987) (by norm_num)
theorem B768001 : Blo 682313 768001 := bbase (se 2 (by rfl) ⟨288000, by rfl⟩ : syracuseStep 768001 = 576001) (by norm_num)
theorem B866305 : Blo 682313 866305 := bbase (se 2 (by rfl) ⟨324864, by rfl⟩ : syracuseStep 866305 = 649729) (by norm_num)
theorem B768037 : Blo 682313 768037 := bbase (se 4 (by rfl) ⟨72003, by rfl⟩ : syracuseStep 768037 = 144007) (by norm_num)
theorem B768073 : Blo 682313 768073 := bbase (se 2 (by rfl) ⟨288027, by rfl⟩ : syracuseStep 768073 = 576055) (by norm_num)
theorem B768109 : Blo 682313 768109 := bbase (se 3 (by rfl) ⟨144020, by rfl⟩ : syracuseStep 768109 = 288041) (by norm_num)
theorem B2308229 : Blo 682313 2308229 := bbase (se 4 (by rfl) ⟨216396, by rfl⟩ : syracuseStep 2308229 = 432793) (by norm_num)
theorem B768145 : Blo 682313 768145 := bbase (se 2 (by rfl) ⟨288054, by rfl⟩ : syracuseStep 768145 = 576109) (by norm_num)
theorem B1947797 : Blo 682313 1947797 := bbase (se 6 (by rfl) ⟨45651, by rfl⟩ : syracuseStep 1947797 = 91303) (by norm_num)
theorem B1849493 : Blo 682313 1849493 := bbase (se 6 (by rfl) ⟨43347, by rfl⟩ : syracuseStep 1849493 = 86695) (by norm_num)
theorem B866477 : Blo 682313 866477 := bbase (se 3 (by rfl) ⟨162464, by rfl⟩ : syracuseStep 866477 = 324929) (by norm_num)
theorem B768181 : Blo 682313 768181 := bbase (se 5 (by rfl) ⟨36008, by rfl⟩ : syracuseStep 768181 = 72017) (by norm_num)
theorem B768217 : Blo 682313 768217 := bbase (se 2 (by rfl) ⟨288081, by rfl⟩ : syracuseStep 768217 = 576163) (by norm_num)
theorem B866533 : Blo 682313 866533 := bbase (se 4 (by rfl) ⟨81237, by rfl⟩ : syracuseStep 866533 = 162475) (by norm_num)
theorem B768253 : Blo 682313 768253 := bbase (se 3 (by rfl) ⟨144047, by rfl⟩ : syracuseStep 768253 = 288095) (by norm_num)
theorem B1128701 : Blo 682313 1128701 := bbase (se 3 (by rfl) ⟨211631, by rfl⟩ : syracuseStep 1128701 = 423263) (by norm_num)
theorem B768289 : Blo 682313 768289 := bbase (se 2 (by rfl) ⟨288108, by rfl⟩ : syracuseStep 768289 = 576217) (by norm_num)
theorem B768325 : Blo 682313 768325 := bbase (se 4 (by rfl) ⟨72030, by rfl⟩ : syracuseStep 768325 = 144061) (by norm_num)
theorem B866629 : Blo 682313 866629 := bbase (se 4 (by rfl) ⟨81246, by rfl⟩ : syracuseStep 866629 = 162493) (by norm_num)
theorem B1096021 : Blo 682313 1096021 := bbase (se 10 (by rfl) ⟨1605, by rfl⟩ : syracuseStep 1096021 = 3211) (by norm_num)
theorem B833893 : Blo 682313 833893 := bbase (se 4 (by rfl) ⟨78177, by rfl⟩ : syracuseStep 833893 = 156355) (by norm_num)
theorem B768361 : Blo 682313 768361 := bbase (se 2 (by rfl) ⟨288135, by rfl⟩ : syracuseStep 768361 = 576271) (by norm_num)
theorem B768397 : Blo 682313 768397 := bbase (se 3 (by rfl) ⟨144074, by rfl⟩ : syracuseStep 768397 = 288149) (by norm_num)
theorem B768433 : Blo 682313 768433 := bbase (se 2 (by rfl) ⟨288162, by rfl⟩ : syracuseStep 768433 = 576325) (by norm_num)
theorem B3127733 : Blo 682313 3127733 := bbase (se 5 (by rfl) ⟨146612, by rfl⟩ : syracuseStep 3127733 = 293225) (by norm_num)
theorem B768469 : Blo 682313 768469 := bbase (se 7 (by rfl) ⟨9005, by rfl⟩ : syracuseStep 768469 = 18011) (by norm_num)
theorem B866801 : Blo 682313 866801 := bbase (se 2 (by rfl) ⟨325050, by rfl⟩ : syracuseStep 866801 = 650101) (by norm_num)
theorem B768505 : Blo 682313 768505 := bbase (se 2 (by rfl) ⟨288189, by rfl⟩ : syracuseStep 768505 = 576379) (by norm_num)
theorem B768541 : Blo 682313 768541 := bbase (se 3 (by rfl) ⟨144101, by rfl⟩ : syracuseStep 768541 = 288203) (by norm_num)
theorem B1391141 : Blo 682313 1391141 := bbase (se 4 (by rfl) ⟨130419, by rfl⟩ : syracuseStep 1391141 = 260839) (by norm_num)
theorem B866857 : Blo 682313 866857 := bbase (se 2 (by rfl) ⟨325071, by rfl⟩ : syracuseStep 866857 = 650143) (by norm_num)
theorem B2308661 : Blo 682313 2308661 := bbase (se 5 (by rfl) ⟨108218, by rfl⟩ : syracuseStep 2308661 = 216437) (by norm_num)
theorem B768577 : Blo 682313 768577 := bbase (se 2 (by rfl) ⟨288216, by rfl⟩ : syracuseStep 768577 = 576433) (by norm_num)
theorem B768613 : Blo 682313 768613 := bbase (se 4 (by rfl) ⟨72057, by rfl⟩ : syracuseStep 768613 = 144115) (by norm_num)
theorem B3455621 : Blo 682313 3455621 := bbase (se 4 (by rfl) ⟨323964, by rfl⟩ : syracuseStep 3455621 = 647929) (by norm_num)
theorem B768649 : Blo 682313 768649 := bbase (se 2 (by rfl) ⟨288243, by rfl⟩ : syracuseStep 768649 = 576487) (by norm_num)
theorem B866953 : Blo 682313 866953 := bbase (se 2 (by rfl) ⟨325107, by rfl⟩ : syracuseStep 866953 = 650215) (by norm_num)
theorem B768685 : Blo 682313 768685 := bbase (se 3 (by rfl) ⟨144128, by rfl⟩ : syracuseStep 768685 = 288257) (by norm_num)
theorem B768721 : Blo 682313 768721 := bbase (se 2 (by rfl) ⟨288270, by rfl⟩ : syracuseStep 768721 = 576541) (by norm_num)
theorem B768757 : Blo 682313 768757 := bbase (se 5 (by rfl) ⟨36035, by rfl⟩ : syracuseStep 768757 = 72071) (by norm_num)
theorem B768793 : Blo 682313 768793 := bbase (se 2 (by rfl) ⟨288297, by rfl⟩ : syracuseStep 768793 = 576595) (by norm_num)
theorem B867125 : Blo 682313 867125 := bbase (se 5 (by rfl) ⟨40646, by rfl⟩ : syracuseStep 867125 = 81293) (by norm_num)
theorem B768829 : Blo 682313 768829 := bbase (se 3 (by rfl) ⟨144155, by rfl⟩ : syracuseStep 768829 = 288311) (by norm_num)
theorem B768865 : Blo 682313 768865 := bbase (se 2 (by rfl) ⟨288324, by rfl⟩ : syracuseStep 768865 = 576649) (by norm_num)
theorem B867181 : Blo 682313 867181 := bbase (se 3 (by rfl) ⟨162596, by rfl⟩ : syracuseStep 867181 = 325193) (by norm_num)
theorem B768901 : Blo 682313 768901 := bbase (se 4 (by rfl) ⟨72084, by rfl⟩ : syracuseStep 768901 = 144169) (by norm_num)
theorem B1948549 : Blo 682313 1948549 := bbase (se 4 (by rfl) ⟨182676, by rfl⟩ : syracuseStep 1948549 = 365353) (by norm_num)
theorem B768937 : Blo 682313 768937 := bbase (se 2 (by rfl) ⟨288351, by rfl⟩ : syracuseStep 768937 = 576703) (by norm_num)
theorem B1850293 : Blo 682313 1850293 := bbase (se 5 (by rfl) ⟨86732, by rfl⟩ : syracuseStep 1850293 = 173465) (by norm_num)
theorem B768973 : Blo 682313 768973 := bbase (se 3 (by rfl) ⟨144182, by rfl⟩ : syracuseStep 768973 = 288365) (by norm_num)
theorem B867277 : Blo 682313 867277 := bbase (se 3 (by rfl) ⟨162614, by rfl⟩ : syracuseStep 867277 = 325229) (by norm_num)
theorem B2309093 : Blo 682313 2309093 := bbase (se 4 (by rfl) ⟨216477, by rfl⟩ : syracuseStep 2309093 = 432955) (by norm_num)
theorem B769009 : Blo 682313 769009 := bbase (se 2 (by rfl) ⟨288378, by rfl⟩ : syracuseStep 769009 = 576757) (by norm_num)
theorem B769045 : Blo 682313 769045 := bbase (se 6 (by rfl) ⟨18024, by rfl⟩ : syracuseStep 769045 = 36049) (by norm_num)
theorem B769081 : Blo 682313 769081 := bbase (se 2 (by rfl) ⟨288405, by rfl⟩ : syracuseStep 769081 = 576811) (by norm_num)
theorem B834625 : Blo 682313 834625 := bbase (se 2 (by rfl) ⟨312984, by rfl⟩ : syracuseStep 834625 = 625969) (by norm_num)
theorem B769117 : Blo 682313 769117 := bbase (se 3 (by rfl) ⟨144209, by rfl⟩ : syracuseStep 769117 = 288419) (by norm_num)
theorem B867449 : Blo 682313 867449 := bbase (se 2 (by rfl) ⟨325293, by rfl⟩ : syracuseStep 867449 = 650587) (by norm_num)
theorem B769153 : Blo 682313 769153 := bbase (se 2 (by rfl) ⟨288432, by rfl⟩ : syracuseStep 769153 = 576865) (by norm_num)
theorem B769189 : Blo 682313 769189 := bbase (se 4 (by rfl) ⟨72111, by rfl⟩ : syracuseStep 769189 = 144223) (by norm_num)
theorem B867505 : Blo 682313 867505 := bbase (se 2 (by rfl) ⟨325314, by rfl⟩ : syracuseStep 867505 = 650629) (by norm_num)
theorem B769225 : Blo 682313 769225 := bbase (se 2 (by rfl) ⟨288459, by rfl⟩ : syracuseStep 769225 = 576919) (by norm_num)
theorem B769261 : Blo 682313 769261 := bbase (se 3 (by rfl) ⟨144236, by rfl⟩ : syracuseStep 769261 = 288473) (by norm_num)
theorem B769297 : Blo 682313 769297 := bbase (se 2 (by rfl) ⟨288486, by rfl⟩ : syracuseStep 769297 = 576973) (by norm_num)
theorem B867601 : Blo 682313 867601 := bbase (se 2 (by rfl) ⟨325350, by rfl⟩ : syracuseStep 867601 = 650701) (by norm_num)
theorem B769333 : Blo 682313 769333 := bbase (se 5 (by rfl) ⟨36062, by rfl⟩ : syracuseStep 769333 = 72125) (by norm_num)
theorem B769369 : Blo 682313 769369 := bbase (se 2 (by rfl) ⟨288513, by rfl⟩ : syracuseStep 769369 = 577027) (by norm_num)
theorem B5913973 : Blo 682313 5913973 := bbase (se 5 (by rfl) ⟨277217, by rfl⟩ : syracuseStep 5913973 = 554435) (by norm_num)
theorem B769405 : Blo 682313 769405 := bbase (se 3 (by rfl) ⟨144263, by rfl⟩ : syracuseStep 769405 = 288527) (by norm_num)
theorem B4373909 : Blo 682313 4373909 := bbase (se 6 (by rfl) ⟨102513, by rfl⟩ : syracuseStep 4373909 = 205027) (by norm_num)
theorem B2309525 : Blo 682313 2309525 := bbase (se 6 (by rfl) ⟨54129, by rfl⟩ : syracuseStep 2309525 = 108259) (by norm_num)
theorem B769441 : Blo 682313 769441 := bbase (se 2 (by rfl) ⟨288540, by rfl⟩ : syracuseStep 769441 = 577081) (by norm_num)
theorem B1850789 : Blo 682313 1850789 := bbase (se 4 (by rfl) ⟨173511, by rfl⟩ : syracuseStep 1850789 = 347023) (by norm_num)
theorem B2080181 : Blo 682313 2080181 := bbase (se 5 (by rfl) ⟨97508, by rfl⟩ : syracuseStep 2080181 = 195017) (by norm_num)
theorem B3292597 : Blo 682313 3292597 := bbase (se 5 (by rfl) ⟨154340, by rfl⟩ : syracuseStep 3292597 = 308681) (by norm_num)
theorem B867773 : Blo 682313 867773 := bbase (se 3 (by rfl) ⟨162707, by rfl⟩ : syracuseStep 867773 = 325415) (by norm_num)
theorem B769477 : Blo 682313 769477 := bbase (se 4 (by rfl) ⟨72138, by rfl⟩ : syracuseStep 769477 = 144277) (by norm_num)
theorem B2473429 : Blo 682313 2473429 := bbase (se 7 (by rfl) ⟨28985, by rfl⟩ : syracuseStep 2473429 = 57971) (by norm_num)
theorem B769513 : Blo 682313 769513 := bbase (se 2 (by rfl) ⟨288567, by rfl⟩ : syracuseStep 769513 = 577135) (by norm_num)
theorem B867829 : Blo 682313 867829 := bbase (se 5 (by rfl) ⟨40679, by rfl⟩ : syracuseStep 867829 = 81359) (by norm_num)
theorem B769549 : Blo 682313 769549 := bbase (se 3 (by rfl) ⟨144290, by rfl⟩ : syracuseStep 769549 = 288581) (by norm_num)
theorem B2604581 : Blo 682313 2604581 := bbase (se 4 (by rfl) ⟨244179, by rfl⟩ : syracuseStep 2604581 = 488359) (by norm_num)
theorem B769585 : Blo 682313 769585 := bbase (se 2 (by rfl) ⟨288594, by rfl⟩ : syracuseStep 769585 = 577189) (by norm_num)
theorem B769621 : Blo 682313 769621 := bbase (se 8 (by rfl) ⟨4509, by rfl⟩ : syracuseStep 769621 = 9019) (by norm_num)
theorem B867925 : Blo 682313 867925 := bbase (se 8 (by rfl) ⟨5085, by rfl⟩ : syracuseStep 867925 = 10171) (by norm_num)
theorem B769657 : Blo 682313 769657 := bbase (se 2 (by rfl) ⟨288621, by rfl⟩ : syracuseStep 769657 = 577243) (by norm_num)
theorem B769693 : Blo 682313 769693 := bbase (se 3 (by rfl) ⟨144317, by rfl⟩ : syracuseStep 769693 = 288635) (by norm_num)
theorem B1097405 : Blo 682313 1097405 := bbase (se 3 (by rfl) ⟨205763, by rfl⟩ : syracuseStep 1097405 = 411527) (by norm_num)
theorem B769729 : Blo 682313 769729 := bbase (se 2 (by rfl) ⟨288648, by rfl⟩ : syracuseStep 769729 = 577297) (by norm_num)
theorem B1752781 : Blo 682313 1752781 := bbase (se 3 (by rfl) ⟨328646, by rfl⟩ : syracuseStep 1752781 = 657293) (by norm_num)
theorem B769765 : Blo 682313 769765 := bbase (se 4 (by rfl) ⟨72165, by rfl⟩ : syracuseStep 769765 = 144331) (by norm_num)
theorem B868097 : Blo 682313 868097 := bbase (se 2 (by rfl) ⟨325536, by rfl⟩ : syracuseStep 868097 = 651073) (by norm_num)
theorem B769801 : Blo 682313 769801 := bbase (se 2 (by rfl) ⟨288675, by rfl⟩ : syracuseStep 769801 = 577351) (by norm_num)
theorem B769837 : Blo 682313 769837 := bbase (se 3 (by rfl) ⟨144344, by rfl⟩ : syracuseStep 769837 = 288689) (by norm_num)
theorem B868153 : Blo 682313 868153 := bbase (se 2 (by rfl) ⟨325557, by rfl⟩ : syracuseStep 868153 = 651115) (by norm_num)
theorem B2309957 : Blo 682313 2309957 := bbase (se 4 (by rfl) ⟨216558, by rfl⟩ : syracuseStep 2309957 = 433117) (by norm_num)
theorem B2604869 : Blo 682313 2604869 := bbase (se 4 (by rfl) ⟨244206, by rfl⟩ : syracuseStep 2604869 = 488413) (by norm_num)
theorem B769873 : Blo 682313 769873 := bbase (se 2 (by rfl) ⟨288702, by rfl⟩ : syracuseStep 769873 = 577405) (by norm_num)
theorem B769909 : Blo 682313 769909 := bbase (se 5 (by rfl) ⟨36089, by rfl⟩ : syracuseStep 769909 = 72179) (by norm_num)
theorem B1097597 : Blo 682313 1097597 := bbase (se 3 (by rfl) ⟨205799, by rfl⟩ : syracuseStep 1097597 = 411599) (by norm_num)
theorem B3456917 : Blo 682313 3456917 := bbase (se 6 (by rfl) ⟨81021, by rfl⟩ : syracuseStep 3456917 = 162043) (by norm_num)
theorem B769945 : Blo 682313 769945 := bbase (se 2 (by rfl) ⟨288729, by rfl⟩ : syracuseStep 769945 = 577459) (by norm_num)
theorem B868249 : Blo 682313 868249 := bbase (se 2 (by rfl) ⟨325593, by rfl⟩ : syracuseStep 868249 = 651187) (by norm_num)
theorem B769981 : Blo 682313 769981 := bbase (se 3 (by rfl) ⟨144371, by rfl⟩ : syracuseStep 769981 = 288743) (by norm_num)
theorem B770017 : Blo 682313 770017 := bbase (se 2 (by rfl) ⟨288756, by rfl⟩ : syracuseStep 770017 = 577513) (by norm_num)
theorem B770053 : Blo 682313 770053 := bbase (se 4 (by rfl) ⟨72192, by rfl⟩ : syracuseStep 770053 = 144385) (by norm_num)
theorem B770089 : Blo 682313 770089 := bbase (se 2 (by rfl) ⟨288783, by rfl⟩ : syracuseStep 770089 = 577567) (by norm_num)
theorem B868421 : Blo 682313 868421 := bbase (se 4 (by rfl) ⟨81414, by rfl⟩ : syracuseStep 868421 = 162829) (by norm_num)
theorem B770125 : Blo 682313 770125 := bbase (se 3 (by rfl) ⟨144398, by rfl⟩ : syracuseStep 770125 = 288797) (by norm_num)
theorem B770161 : Blo 682313 770161 := bbase (se 2 (by rfl) ⟨288810, by rfl⟩ : syracuseStep 770161 = 577621) (by norm_num)
theorem B868477 : Blo 682313 868477 := bbase (se 3 (by rfl) ⟨162839, by rfl⟩ : syracuseStep 868477 = 325679) (by norm_num)
theorem B770197 : Blo 682313 770197 := bbase (se 6 (by rfl) ⟨18051, by rfl⟩ : syracuseStep 770197 = 36103) (by norm_num)
theorem B770233 : Blo 682313 770233 := bbase (se 2 (by rfl) ⟨288837, by rfl⟩ : syracuseStep 770233 = 577675) (by norm_num)
theorem B770269 : Blo 682313 770269 := bbase (se 3 (by rfl) ⟨144425, by rfl⟩ : syracuseStep 770269 = 288851) (by norm_num)
theorem B868573 : Blo 682313 868573 := bbase (se 3 (by rfl) ⟨162857, by rfl⟩ : syracuseStep 868573 = 325715) (by norm_num)
theorem B2310389 : Blo 682313 2310389 := bbase (se 5 (by rfl) ⟨108299, by rfl⟩ : syracuseStep 2310389 = 216599) (by norm_num)
theorem B770305 : Blo 682313 770305 := bbase (se 2 (by rfl) ⟨288864, by rfl⟩ : syracuseStep 770305 = 577729) (by norm_num)
theorem B770341 : Blo 682313 770341 := bbase (se 4 (by rfl) ⟨72219, by rfl⟩ : syracuseStep 770341 = 144439) (by norm_num)
theorem B770377 : Blo 682313 770377 := bbase (se 2 (by rfl) ⟨288891, by rfl⟩ : syracuseStep 770377 = 577783) (by norm_num)
theorem B770413 : Blo 682313 770413 := bbase (se 3 (by rfl) ⟨144452, by rfl⟩ : syracuseStep 770413 = 288905) (by norm_num)
theorem B770449 : Blo 682313 770449 := bbase (se 2 (by rfl) ⟨288918, by rfl⟩ : syracuseStep 770449 = 577837) (by norm_num)
theorem B770485 : Blo 682313 770485 := bbase (se 5 (by rfl) ⟨36116, by rfl⟩ : syracuseStep 770485 = 72233) (by norm_num)
theorem B770521 : Blo 682313 770521 := bbase (se 2 (by rfl) ⟨288945, by rfl⟩ : syracuseStep 770521 = 577891) (by norm_num)
theorem B1458661 : Blo 682313 1458661 := bbase (se 4 (by rfl) ⟨136749, by rfl⟩ : syracuseStep 1458661 = 273499) (by norm_num)
theorem B770557 : Blo 682313 770557 := bbase (se 3 (by rfl) ⟨144479, by rfl⟩ : syracuseStep 770557 = 288959) (by norm_num)
theorem B7029269 : Blo 682313 7029269 := bbase (se 6 (by rfl) ⟨164748, by rfl⟩ : syracuseStep 7029269 = 329497) (by norm_num)
theorem B770593 : Blo 682313 770593 := bbase (se 2 (by rfl) ⟨288972, by rfl⟩ : syracuseStep 770593 = 577945) (by norm_num)
theorem B770629 : Blo 682313 770629 := bbase (se 4 (by rfl) ⟨72246, by rfl⟩ : syracuseStep 770629 = 144493) (by norm_num)
theorem B770665 : Blo 682313 770665 := bbase (se 2 (by rfl) ⟨288999, by rfl⟩ : syracuseStep 770665 = 577999) (by norm_num)
theorem B770701 : Blo 682313 770701 := bbase (se 3 (by rfl) ⟨144506, by rfl⟩ : syracuseStep 770701 = 289013) (by norm_num)
theorem B2310821 : Blo 682313 2310821 := bbase (se 4 (by rfl) ⟨216639, by rfl⟩ : syracuseStep 2310821 = 433279) (by norm_num)
theorem B770737 : Blo 682313 770737 := bbase (se 2 (by rfl) ⟨289026, by rfl⟩ : syracuseStep 770737 = 578053) (by norm_num)
theorem B770773 : Blo 682313 770773 := bbase (se 7 (by rfl) ⟨9032, by rfl⟩ : syracuseStep 770773 = 18065) (by norm_num)
theorem B770809 : Blo 682313 770809 := bbase (se 2 (by rfl) ⟨289053, by rfl⟩ : syracuseStep 770809 = 578107) (by norm_num)
theorem B770845 : Blo 682313 770845 := bbase (se 3 (by rfl) ⟨144533, by rfl⟩ : syracuseStep 770845 = 289067) (by norm_num)
theorem B770881 : Blo 682313 770881 := bbase (se 2 (by rfl) ⟨289080, by rfl⟩ : syracuseStep 770881 = 578161) (by norm_num)
theorem B770917 : Blo 682313 770917 := bbase (se 4 (by rfl) ⟨72273, by rfl⟩ : syracuseStep 770917 = 144547) (by norm_num)
theorem B770953 : Blo 682313 770953 := bbase (se 2 (by rfl) ⟨289107, by rfl⟩ : syracuseStep 770953 = 578215) (by norm_num)
theorem B770989 : Blo 682313 770989 := bbase (se 3 (by rfl) ⟨144560, by rfl⟩ : syracuseStep 770989 = 289121) (by norm_num)
theorem B771025 : Blo 682313 771025 := bbase (se 2 (by rfl) ⟨289134, by rfl⟩ : syracuseStep 771025 = 578269) (by norm_num)
theorem B771061 : Blo 682313 771061 := bbase (se 5 (by rfl) ⟨36143, by rfl⟩ : syracuseStep 771061 = 72287) (by norm_num)
theorem B1295365 : Blo 682313 1295365 := bbase (se 4 (by rfl) ⟨121440, by rfl⟩ : syracuseStep 1295365 = 242881) (by norm_num)
theorem B771097 : Blo 682313 771097 := bbase (se 2 (by rfl) ⟨289161, by rfl⟩ : syracuseStep 771097 = 578323) (by norm_num)
theorem B771133 : Blo 682313 771133 := bbase (se 3 (by rfl) ⟨144587, by rfl⟩ : syracuseStep 771133 = 289175) (by norm_num)
theorem B2311253 : Blo 682313 2311253 := bbase (se 8 (by rfl) ⟨13542, by rfl⟩ : syracuseStep 2311253 = 27085) (by norm_num)
theorem B771169 : Blo 682313 771169 := bbase (se 2 (by rfl) ⟨289188, by rfl⟩ : syracuseStep 771169 = 578377) (by norm_num)
theorem B771205 : Blo 682313 771205 := bbase (se 4 (by rfl) ⟨72300, by rfl⟩ : syracuseStep 771205 = 144601) (by norm_num)
theorem B1295509 : Blo 682313 1295509 := bbase (se 6 (by rfl) ⟨30363, by rfl⟩ : syracuseStep 1295509 = 60727) (by norm_num)
theorem B3458213 : Blo 682313 3458213 := bbase (se 4 (by rfl) ⟨324207, by rfl⟩ : syracuseStep 3458213 = 648415) (by norm_num)
theorem B1098917 : Blo 682313 1098917 := bbase (se 4 (by rfl) ⟨103023, by rfl⟩ : syracuseStep 1098917 = 206047) (by norm_num)
theorem B771241 : Blo 682313 771241 := bbase (se 2 (by rfl) ⟨289215, by rfl⟩ : syracuseStep 771241 = 578431) (by norm_num)
theorem B1557701 : Blo 682313 1557701 := bbase (se 4 (by rfl) ⟨146034, by rfl⟩ : syracuseStep 1557701 = 292069) (by norm_num)
theorem B771277 : Blo 682313 771277 := bbase (se 3 (by rfl) ⟨144614, by rfl⟩ : syracuseStep 771277 = 289229) (by norm_num)
theorem B771313 : Blo 682313 771313 := bbase (se 2 (by rfl) ⟨289242, by rfl⟩ : syracuseStep 771313 = 578485) (by norm_num)
theorem B1099013 : Blo 682313 1099013 := bbase (se 4 (by rfl) ⟨103032, by rfl⟩ : syracuseStep 1099013 = 206065) (by norm_num)
theorem B771349 : Blo 682313 771349 := bbase (se 6 (by rfl) ⟨18078, by rfl⟩ : syracuseStep 771349 = 36157) (by norm_num)
theorem B1099045 : Blo 682313 1099045 := bbase (se 4 (by rfl) ⟨103035, by rfl⟩ : syracuseStep 1099045 = 206071) (by norm_num)
theorem B1295669 : Blo 682313 1295669 := bbase (se 5 (by rfl) ⟨60734, by rfl⟩ : syracuseStep 1295669 = 121469) (by norm_num)
theorem B771385 : Blo 682313 771385 := bbase (se 2 (by rfl) ⟨289269, by rfl⟩ : syracuseStep 771385 = 578539) (by norm_num)
theorem B1459549 : Blo 682313 1459549 := bbase (se 3 (by rfl) ⟨273665, by rfl⟩ : syracuseStep 1459549 = 547331) (by norm_num)
theorem B771421 : Blo 682313 771421 := bbase (se 3 (by rfl) ⟨144641, by rfl⟩ : syracuseStep 771421 = 289283) (by norm_num)
theorem B771457 : Blo 682313 771457 := bbase (se 2 (by rfl) ⟨289296, by rfl⟩ : syracuseStep 771457 = 578593) (by norm_num)
theorem B771493 : Blo 682313 771493 := bbase (se 4 (by rfl) ⟨72327, by rfl⟩ : syracuseStep 771493 = 144655) (by norm_num)
theorem B1295813 : Blo 682313 1295813 := bbase (se 4 (by rfl) ⟨121482, by rfl⟩ : syracuseStep 1295813 = 242965) (by norm_num)
theorem B771529 : Blo 682313 771529 := bbase (se 2 (by rfl) ⟨289323, by rfl⟩ : syracuseStep 771529 = 578647) (by norm_num)
theorem B2344405 : Blo 682313 2344405 := bbase (se 7 (by rfl) ⟨27473, by rfl⟩ : syracuseStep 2344405 = 54947) (by norm_num)
theorem B771565 : Blo 682313 771565 := bbase (se 3 (by rfl) ⟨144668, by rfl⟩ : syracuseStep 771565 = 289337) (by norm_num)
theorem B2311685 : Blo 682313 2311685 := bbase (se 4 (by rfl) ⟨216720, by rfl⟩ : syracuseStep 2311685 = 433441) (by norm_num)
theorem B771601 : Blo 682313 771601 := bbase (se 2 (by rfl) ⟨289350, by rfl⟩ : syracuseStep 771601 = 578701) (by norm_num)
theorem B771637 : Blo 682313 771637 := bbase (se 5 (by rfl) ⟨36170, by rfl⟩ : syracuseStep 771637 = 72341) (by norm_num)
theorem B771673 : Blo 682313 771673 := bbase (se 2 (by rfl) ⟨289377, by rfl⟩ : syracuseStep 771673 = 578755) (by norm_num)
theorem B771709 : Blo 682313 771709 := bbase (se 3 (by rfl) ⟨144695, by rfl⟩ : syracuseStep 771709 = 289391) (by norm_num)
theorem B771745 : Blo 682313 771745 := bbase (se 2 (by rfl) ⟨289404, by rfl⟩ : syracuseStep 771745 = 578809) (by norm_num)
theorem B1951397 : Blo 682313 1951397 := bbase (se 4 (by rfl) ⟨182943, by rfl⟩ : syracuseStep 1951397 = 365887) (by norm_num)
theorem B771781 : Blo 682313 771781 := bbase (se 4 (by rfl) ⟨72354, by rfl⟩ : syracuseStep 771781 = 144709) (by norm_num)
theorem B1296101 : Blo 682313 1296101 := bbase (se 4 (by rfl) ⟨121509, by rfl⟩ : syracuseStep 1296101 = 243019) (by norm_num)
theorem B771817 : Blo 682313 771817 := bbase (se 2 (by rfl) ⟨289431, by rfl⟩ : syracuseStep 771817 = 578863) (by norm_num)
theorem B771853 : Blo 682313 771853 := bbase (se 3 (by rfl) ⟨144722, by rfl⟩ : syracuseStep 771853 = 289445) (by norm_num)
theorem B771889 : Blo 682313 771889 := bbase (se 2 (by rfl) ⟨289458, by rfl⟩ : syracuseStep 771889 = 578917) (by norm_num)
theorem B1460045 : Blo 682313 1460045 := bbase (se 3 (by rfl) ⟨273758, by rfl⟩ : syracuseStep 1460045 = 547517) (by norm_num)
theorem B771925 : Blo 682313 771925 := bbase (se 9 (by rfl) ⟨2261, by rfl⟩ : syracuseStep 771925 = 4523) (by norm_num)
theorem B771961 : Blo 682313 771961 := bbase (se 2 (by rfl) ⟨289485, by rfl⟩ : syracuseStep 771961 = 578971) (by norm_num)
theorem B1296253 : Blo 682313 1296253 := bbase (se 3 (by rfl) ⟨243047, by rfl⟩ : syracuseStep 1296253 = 486095) (by norm_num)
theorem B771997 : Blo 682313 771997 := bbase (se 3 (by rfl) ⟨144749, by rfl⟩ : syracuseStep 771997 = 289499) (by norm_num)
theorem B2312117 : Blo 682313 2312117 := bbase (se 5 (by rfl) ⟨108380, by rfl⟩ : syracuseStep 2312117 = 216761) (by norm_num)
theorem B772033 : Blo 682313 772033 := bbase (se 2 (by rfl) ⟨289512, by rfl⟩ : syracuseStep 772033 = 579025) (by norm_num)
theorem B772069 : Blo 682313 772069 := bbase (se 4 (by rfl) ⟨72381, by rfl⟩ : syracuseStep 772069 = 144763) (by norm_num)
theorem B2672645 : Blo 682313 2672645 := bbase (se 4 (by rfl) ⟨250560, by rfl⟩ : syracuseStep 2672645 = 501121) (by norm_num)
theorem B1296557 : Blo 682313 1296557 := bbase (se 3 (by rfl) ⟨243104, by rfl⟩ : syracuseStep 1296557 = 486209) (by norm_num)
theorem B1231085 : Blo 682313 1231085 := bbase (se 3 (by rfl) ⟨230828, by rfl⟩ : syracuseStep 1231085 = 461657) (by norm_num)
theorem B2312549 : Blo 682313 2312549 := bbase (se 4 (by rfl) ⟨216801, by rfl⟩ : syracuseStep 2312549 = 433603) (by norm_num)
theorem B3459509 : Blo 682313 3459509 := bbase (se 5 (by rfl) ⟨162164, by rfl⟩ : syracuseStep 3459509 = 324329) (by norm_num)
theorem B1460909 : Blo 682313 1460909 := bbase (se 3 (by rfl) ⟨273920, by rfl⟩ : syracuseStep 1460909 = 547841) (by norm_num)
theorem B2312981 : Blo 682313 2312981 := bbase (se 6 (by rfl) ⟨54210, by rfl⟩ : syracuseStep 2312981 = 108421) (by norm_num)
theorem B5327669 : Blo 682313 5327669 := bbase (se 5 (by rfl) ⟨249734, by rfl⟩ : syracuseStep 5327669 = 499469) (by norm_num)
theorem B1461053 : Blo 682313 1461053 := bbase (se 3 (by rfl) ⟨273947, by rfl⟩ : syracuseStep 1461053 = 547895) (by norm_num)
theorem B772933 : Blo 682313 772933 := bbase (se 4 (by rfl) ⟨72462, by rfl⟩ : syracuseStep 772933 = 144925) (by norm_num)
theorem B1952581 : Blo 682313 1952581 := bbase (se 4 (by rfl) ⟨183054, by rfl⟩ : syracuseStep 1952581 = 366109) (by norm_num)
theorem B1297309 : Blo 682313 1297309 := bbase (se 3 (by rfl) ⟨243245, by rfl⟩ : syracuseStep 1297309 = 486491) (by norm_num)
theorem B3296213 : Blo 682313 3296213 := bbase (se 7 (by rfl) ⟨38627, by rfl⟩ : syracuseStep 3296213 = 77255) (by norm_num)
theorem B1952741 : Blo 682313 1952741 := bbase (se 4 (by rfl) ⟨183069, by rfl⟩ : syracuseStep 1952741 = 366139) (by norm_num)
theorem B1297453 : Blo 682313 1297453 := bbase (se 3 (by rfl) ⟨243272, by rfl⟩ : syracuseStep 1297453 = 486545) (by norm_num)
theorem B2313413 : Blo 682313 2313413 := bbase (se 4 (by rfl) ⟨216882, by rfl⟩ : syracuseStep 2313413 = 433765) (by norm_num)
theorem B1297613 : Blo 682313 1297613 := bbase (se 3 (by rfl) ⟨243302, by rfl⟩ : syracuseStep 1297613 = 486605) (by norm_num)
theorem B1952981 : Blo 682313 1952981 := bbase (se 7 (by rfl) ⟨22886, by rfl⟩ : syracuseStep 1952981 = 45773) (by norm_num)
theorem B1232101 : Blo 682313 1232101 := bbase (se 4 (by rfl) ⟨115509, by rfl⟩ : syracuseStep 1232101 = 231019) (by norm_num)
theorem B1297757 : Blo 682313 1297757 := bbase (se 3 (by rfl) ⟨243329, by rfl⟩ : syracuseStep 1297757 = 486659) (by norm_num)
theorem B1953173 : Blo 682313 1953173 := bbase (se 6 (by rfl) ⟨45777, by rfl⟩ : syracuseStep 1953173 = 91555) (by norm_num)
theorem B1461797 : Blo 682313 1461797 := bbase (se 4 (by rfl) ⟨137043, by rfl⟩ : syracuseStep 1461797 = 274087) (by norm_num)
theorem B740945 : Blo 682313 740945 := bbase (se 2 (by rfl) ⟨277854, by rfl⟩ : syracuseStep 740945 = 555709) (by norm_num)
theorem B2313845 : Blo 682313 2313845 := bbase (se 5 (by rfl) ⟨108461, by rfl⟩ : syracuseStep 2313845 = 216923) (by norm_num)
theorem B1298045 : Blo 682313 1298045 := bbase (se 3 (by rfl) ⟨243383, by rfl⟩ : syracuseStep 1298045 = 486767) (by norm_num)
theorem B1232533 : Blo 682313 1232533 := bbase (se 6 (by rfl) ⟨28887, by rfl⟩ : syracuseStep 1232533 = 57775) (by norm_num)
theorem B1756829 : Blo 682313 1756829 := bbase (se 3 (by rfl) ⟨329405, by rfl⟩ : syracuseStep 1756829 = 658811) (by norm_num)
theorem B3460805 : Blo 682313 3460805 := bbase (se 4 (by rfl) ⟨324450, by rfl⟩ : syracuseStep 3460805 = 648901) (by norm_num)
theorem B1298197 : Blo 682313 1298197 := bbase (se 6 (by rfl) ⟨30426, by rfl⟩ : syracuseStep 1298197 = 60853) (by norm_num)
theorem B2314277 : Blo 682313 2314277 := bbase (se 4 (by rfl) ⟨216963, by rfl⟩ : syracuseStep 2314277 = 433927) (by norm_num)
theorem B1298501 : Blo 682313 1298501 := bbase (se 4 (by rfl) ⟨121734, by rfl⟩ : syracuseStep 1298501 = 243469) (by norm_num)
theorem B3887189 : Blo 682313 3887189 := bbase (se 8 (by rfl) ⟨22776, by rfl⟩ : syracuseStep 3887189 = 45553) (by norm_num)
theorem B1233053 : Blo 682313 1233053 := bbase (se 3 (by rfl) ⟨231197, by rfl⟩ : syracuseStep 1233053 = 462395) (by norm_num)
theorem B1462549 : Blo 682313 1462549 := bbase (se 6 (by rfl) ⟨34278, by rfl⟩ : syracuseStep 1462549 = 68557) (by norm_num)
theorem B1331525 : Blo 682313 1331525 := bbase (se 4 (by rfl) ⟨124830, by rfl⟩ : syracuseStep 1331525 = 249661) (by norm_num)
theorem B1954165 : Blo 682313 1954165 := bbase (se 5 (by rfl) ⟨91601, by rfl⟩ : syracuseStep 1954165 = 183203) (by norm_num)
theorem B1462693 : Blo 682313 1462693 := bbase (se 4 (by rfl) ⟨137127, by rfl⟩ : syracuseStep 1462693 = 274255) (by norm_num)
theorem B2347429 : Blo 682313 2347429 := bbase (se 4 (by rfl) ⟨220071, by rfl⟩ : syracuseStep 2347429 = 440143) (by norm_num)
theorem B2314709 : Blo 682313 2314709 := bbase (se 7 (by rfl) ⟨27125, by rfl⟩ : syracuseStep 2314709 = 54251) (by norm_num)
theorem B938461 : Blo 682313 938461 := bbase (se 3 (by rfl) ⟨175961, by rfl⟩ : syracuseStep 938461 = 351923) (by norm_num)
theorem B1463069 : Blo 682313 1463069 := bbase (se 3 (by rfl) ⟨274325, by rfl⟩ : syracuseStep 1463069 = 548651) (by norm_num)
theorem B1299253 : Blo 682313 1299253 := bbase (se 5 (by rfl) ⟨60902, by rfl⟩ : syracuseStep 1299253 = 121805) (by norm_num)
theorem B2315141 : Blo 682313 2315141 := bbase (se 4 (by rfl) ⟨217044, by rfl⟩ : syracuseStep 2315141 = 434089) (by norm_num)
theorem B5198741 : Blo 682313 5198741 := bbase (se 6 (by rfl) ⟨121845, by rfl⟩ : syracuseStep 5198741 = 243691) (by norm_num)
theorem B1299397 : Blo 682313 1299397 := bbase (se 4 (by rfl) ⟨121818, by rfl⟩ : syracuseStep 1299397 = 243637) (by norm_num)
theorem B3462101 : Blo 682313 3462101 := bbase (se 7 (by rfl) ⟨40571, by rfl⟩ : syracuseStep 3462101 = 81143) (by norm_num)
theorem B1168357 : Blo 682313 1168357 := bbase (se 4 (by rfl) ⟨109533, by rfl⟩ : syracuseStep 1168357 = 219067) (by norm_num)
theorem B21353557 : Blo 682313 21353557 := bbase (se 8 (by rfl) ⟨125118, by rfl⟩ : syracuseStep 21353557 = 250237) (by norm_num)
theorem B1299557 : Blo 682313 1299557 := bbase (se 4 (by rfl) ⟨121833, by rfl⟩ : syracuseStep 1299557 = 243667) (by norm_num)
theorem B1463437 : Blo 682313 1463437 := bbase (se 3 (by rfl) ⟨274394, by rfl⟩ : syracuseStep 1463437 = 548789) (by norm_num)
theorem B1758437 : Blo 682313 1758437 := bbase (se 4 (by rfl) ⟨164853, by rfl⟩ : syracuseStep 1758437 = 329707) (by norm_num)
theorem B1299701 : Blo 682313 1299701 := bbase (se 5 (by rfl) ⟨60923, by rfl⟩ : syracuseStep 1299701 = 121847) (by norm_num)
theorem B2315573 : Blo 682313 2315573 := bbase (se 5 (by rfl) ⟨108542, by rfl⟩ : syracuseStep 2315573 = 217085) (by norm_num)
theorem B1168789 : Blo 682313 1168789 := bbase (se 6 (by rfl) ⟨27393, by rfl⟩ : syracuseStep 1168789 = 54787) (by norm_num)
theorem B972253 : Blo 682313 972253 := bbase (se 3 (by rfl) ⟨182297, by rfl⟩ : syracuseStep 972253 = 364595) (by norm_num)
theorem B1299989 : Blo 682313 1299989 := bbase (se 6 (by rfl) ⟨30468, by rfl⟩ : syracuseStep 1299989 = 60937) (by norm_num)
theorem B1300141 : Blo 682313 1300141 := bbase (se 3 (by rfl) ⟨243776, by rfl⟩ : syracuseStep 1300141 = 487553) (by norm_num)
theorem B7100117 : Blo 682313 7100117 := bbase (se 7 (by rfl) ⟨83204, by rfl⟩ : syracuseStep 7100117 = 166409) (by norm_num)
theorem B2316005 : Blo 682313 2316005 := bbase (se 4 (by rfl) ⟨217125, by rfl⟩ : syracuseStep 2316005 = 434251) (by norm_num)
theorem B1038101 : Blo 682313 1038101 := bbase (se 6 (by rfl) ⟨24330, by rfl⟩ : syracuseStep 1038101 = 48661) (by norm_num)
theorem B972589 : Blo 682313 972589 := bbase (se 3 (by rfl) ⟨182360, by rfl⟩ : syracuseStep 972589 = 364721) (by norm_num)
theorem B1300445 : Blo 682313 1300445 := bbase (se 3 (by rfl) ⟨243833, by rfl⟩ : syracuseStep 1300445 = 487667) (by norm_num)
theorem B972805 : Blo 682313 972805 := bbase (se 4 (by rfl) ⟨91200, by rfl⟩ : syracuseStep 972805 = 182401) (by norm_num)
theorem B1562645 : Blo 682313 1562645 := bbase (se 6 (by rfl) ⟨36624, by rfl⟩ : syracuseStep 1562645 = 73249) (by norm_num)
theorem B3463397 : Blo 682313 3463397 := bbase (se 4 (by rfl) ⟨324693, by rfl⟩ : syracuseStep 3463397 = 649387) (by norm_num)
theorem B3889397 : Blo 682313 3889397 := bbase (se 5 (by rfl) ⟨182315, by rfl⟩ : syracuseStep 3889397 = 364631) (by norm_num)
theorem B973181 : Blo 682313 973181 := bbase (se 3 (by rfl) ⟨182471, by rfl⟩ : syracuseStep 973181 = 364943) (by norm_num)
theorem B2775653 : Blo 682313 2775653 := bbase (se 4 (by rfl) ⟨260217, by rfl⟩ : syracuseStep 2775653 = 520435) (by norm_num)
theorem B1464941 : Blo 682313 1464941 := bbase (se 3 (by rfl) ⟨274676, by rfl⟩ : syracuseStep 1464941 = 549353) (by norm_num)
theorem B1301197 : Blo 682313 1301197 := bbase (se 3 (by rfl) ⟨243974, by rfl⟩ : syracuseStep 1301197 = 487949) (by norm_num)
theorem B1465085 : Blo 682313 1465085 := bbase (se 3 (by rfl) ⟨274703, by rfl⟩ : syracuseStep 1465085 = 549407) (by norm_num)
theorem B1170245 : Blo 682313 1170245 := bbase (se 4 (by rfl) ⟨109710, by rfl⟩ : syracuseStep 1170245 = 219421) (by norm_num)
theorem B1301341 : Blo 682313 1301341 := bbase (se 3 (by rfl) ⟨244001, by rfl⟩ : syracuseStep 1301341 = 488003) (by norm_num)
theorem B1727365 : Blo 682313 1727365 := bbase (se 4 (by rfl) ⟨161940, by rfl⟩ : syracuseStep 1727365 = 323881) (by norm_num)
theorem B1727477 : Blo 682313 1727477 := bbase (se 5 (by rfl) ⟨80975, by rfl⟩ : syracuseStep 1727477 = 161951) (by norm_num)
theorem B1301501 : Blo 682313 1301501 := bbase (se 3 (by rfl) ⟨244031, by rfl⟩ : syracuseStep 1301501 = 488063) (by norm_num)
theorem B1170485 : Blo 682313 1170485 := bbase (se 5 (by rfl) ⟨54866, by rfl⟩ : syracuseStep 1170485 = 109733) (by norm_num)
theorem B1465445 : Blo 682313 1465445 := bbase (se 4 (by rfl) ⟨137385, by rfl⟩ : syracuseStep 1465445 = 274771) (by norm_num)
theorem B1170541 : Blo 682313 1170541 := bbase (se 3 (by rfl) ⟨219476, by rfl⟩ : syracuseStep 1170541 = 438953) (by norm_num)
theorem B1301645 : Blo 682313 1301645 := bbase (se 3 (by rfl) ⟨244058, by rfl⟩ : syracuseStep 1301645 = 488117) (by norm_num)
theorem B1727669 : Blo 682313 1727669 := bbase (se 5 (by rfl) ⟨80984, by rfl⟩ : syracuseStep 1727669 = 161969) (by norm_num)
theorem B1760501 : Blo 682313 1760501 := bbase (se 5 (by rfl) ⟨82523, by rfl⟩ : syracuseStep 1760501 = 165047) (by norm_num)
theorem B1301933 : Blo 682313 1301933 := bbase (se 3 (by rfl) ⟨244112, by rfl⟩ : syracuseStep 1301933 = 488225) (by norm_num)
theorem B1236397 : Blo 682313 1236397 := bbase (se 3 (by rfl) ⟨231824, by rfl⟩ : syracuseStep 1236397 = 463649) (by norm_num)
theorem B875981 : Blo 682313 875981 := bbase (se 3 (by rfl) ⟨164246, by rfl⟩ : syracuseStep 875981 = 328493) (by norm_num)
theorem B3464693 : Blo 682313 3464693 := bbase (se 5 (by rfl) ⟨162407, by rfl⟩ : syracuseStep 3464693 = 324815) (by norm_num)
theorem B1728013 : Blo 682313 1728013 := bbase (se 3 (by rfl) ⟨324002, by rfl⟩ : syracuseStep 1728013 = 648005) (by norm_num)
theorem B1236541 : Blo 682313 1236541 := bbase (se 3 (by rfl) ⟨231851, by rfl⟩ : syracuseStep 1236541 = 463703) (by norm_num)
theorem B1302085 : Blo 682313 1302085 := bbase (se 4 (by rfl) ⟨122070, by rfl⟩ : syracuseStep 1302085 = 244141) (by norm_num)
theorem B1728125 : Blo 682313 1728125 := bbase (se 3 (by rfl) ⟨324023, by rfl⟩ : syracuseStep 1728125 = 648047) (by norm_num)
theorem B1564397 : Blo 682313 1564397 := bbase (se 3 (by rfl) ⟨293324, by rfl⟩ : syracuseStep 1564397 = 586649) (by norm_num)
theorem B974605 : Blo 682313 974605 := bbase (se 3 (by rfl) ⟨182738, by rfl⟩ : syracuseStep 974605 = 365477) (by norm_num)
theorem B1662781 : Blo 682313 1662781 := bbase (se 3 (by rfl) ⟨311771, by rfl⟩ : syracuseStep 1662781 = 623543) (by norm_num)
theorem B1728317 : Blo 682313 1728317 := bbase (se 3 (by rfl) ⟨324059, by rfl⟩ : syracuseStep 1728317 = 648119) (by norm_num)
theorem B876361 : Blo 682313 876361 := bbase (se 2 (by rfl) ⟨328635, by rfl⟩ : syracuseStep 876361 = 657271) (by norm_num)
theorem B1302389 : Blo 682313 1302389 := bbase (se 5 (by rfl) ⟨61049, by rfl⟩ : syracuseStep 1302389 = 122099) (by norm_num)
theorem B1564741 : Blo 682313 1564741 := bbase (se 4 (by rfl) ⟨146694, by rfl⟩ : syracuseStep 1564741 = 293389) (by norm_num)
theorem B876637 : Blo 682313 876637 := bbase (se 3 (by rfl) ⟨164369, by rfl⟩ : syracuseStep 876637 = 328739) (by norm_num)
theorem B843869 : Blo 682313 843869 := bbase (se 3 (by rfl) ⟨158225, by rfl⟩ : syracuseStep 843869 = 316451) (by norm_num)
theorem B1728661 : Blo 682313 1728661 := bbase (se 6 (by rfl) ⟨40515, by rfl⟩ : syracuseStep 1728661 = 81031) (by norm_num)
theorem B1728773 : Blo 682313 1728773 := bbase (se 4 (by rfl) ⟨162072, by rfl⟩ : syracuseStep 1728773 = 324145) (by norm_num)
theorem B18702677 : Blo 682313 18702677 := bbase (se 10 (by rfl) ⟨27396, by rfl⟩ : syracuseStep 18702677 = 54793) (by norm_num)
theorem B975197 : Blo 682313 975197 := bbase (se 3 (by rfl) ⟨182849, by rfl⟩ : syracuseStep 975197 = 365699) (by norm_num)
theorem B975277 : Blo 682313 975277 := bbase (se 3 (by rfl) ⟨182864, by rfl⟩ : syracuseStep 975277 = 365729) (by norm_num)
theorem B1728965 : Blo 682313 1728965 := bbase (se 4 (by rfl) ⟨162090, by rfl⟩ : syracuseStep 1728965 = 324181) (by norm_num)
theorem B975397 : Blo 682313 975397 := bbase (se 4 (by rfl) ⟨91443, by rfl⟩ : syracuseStep 975397 = 182887) (by norm_num)
theorem B975493 : Blo 682313 975493 := bbase (se 4 (by rfl) ⟨91452, by rfl⟩ : syracuseStep 975493 = 182905) (by norm_num)
theorem B3465989 : Blo 682313 3465989 := bbase (se 4 (by rfl) ⟨324936, by rfl⟩ : syracuseStep 3465989 = 649873) (by norm_num)
theorem B1729309 : Blo 682313 1729309 := bbase (se 3 (by rfl) ⟨324245, by rfl⟩ : syracuseStep 1729309 = 648491) (by norm_num)
theorem B877429 : Blo 682313 877429 := bbase (se 5 (by rfl) ⟨41129, by rfl⟩ : syracuseStep 877429 = 82259) (by norm_num)
theorem B1729421 : Blo 682313 1729421 := bbase (se 3 (by rfl) ⟨324266, by rfl⟩ : syracuseStep 1729421 = 648533) (by norm_num)
theorem B1664077 : Blo 682313 1664077 := bbase (se 3 (by rfl) ⟨312014, by rfl⟩ : syracuseStep 1664077 = 624029) (by norm_num)
theorem B1729613 : Blo 682313 1729613 := bbase (se 3 (by rfl) ⟨324302, by rfl⟩ : syracuseStep 1729613 = 648605) (by norm_num)
theorem B7398485 : Blo 682313 7398485 := bbase (se 8 (by rfl) ⟨43350, by rfl⟩ : syracuseStep 7398485 = 86701) (by norm_num)
theorem B975989 : Blo 682313 975989 := bbase (se 5 (by rfl) ⟨45749, by rfl⟩ : syracuseStep 975989 = 91499) (by norm_num)
theorem B8316053 : Blo 682313 8316053 := bbase (se 6 (by rfl) ⟨194907, by rfl⟩ : syracuseStep 8316053 = 389815) (by norm_num)
theorem B2188453 : Blo 682313 2188453 := bbase (se 4 (by rfl) ⟨205167, by rfl⟩ : syracuseStep 2188453 = 410335) (by norm_num)
theorem B779485 : Blo 682313 779485 := bbase (se 3 (by rfl) ⟨146153, by rfl⟩ : syracuseStep 779485 = 292307) (by norm_num)
theorem B1041653 : Blo 682313 1041653 := bbase (se 5 (by rfl) ⟨48827, by rfl⟩ : syracuseStep 1041653 = 97655) (by norm_num)
theorem B1402181 : Blo 682313 1402181 := bbase (se 4 (by rfl) ⟨131454, by rfl⟩ : syracuseStep 1402181 = 262909) (by norm_num)
theorem B2188709 : Blo 682313 2188709 := bbase (se 4 (by rfl) ⟨205191, by rfl⟩ : syracuseStep 2188709 = 410383) (by norm_num)
theorem B1729957 : Blo 682313 1729957 := bbase (se 4 (by rfl) ⟨162183, by rfl⟩ : syracuseStep 1729957 = 324367) (by norm_num)
theorem B779717 : Blo 682313 779717 := bbase (se 4 (by rfl) ⟨73098, by rfl⟩ : syracuseStep 779717 = 146197) (by norm_num)
theorem B1730069 : Blo 682313 1730069 := bbase (se 6 (by rfl) ⟨40548, by rfl⟩ : syracuseStep 1730069 = 81097) (by norm_num)
theorem B5858837 : Blo 682313 5858837 := bbase (se 6 (by rfl) ⟨137316, by rfl⟩ : syracuseStep 5858837 = 274633) (by norm_num)
theorem B4154933 : Blo 682313 4154933 := bbase (se 5 (by rfl) ⟨194762, by rfl⟩ : syracuseStep 4154933 = 389525) (by norm_num)
theorem B1402429 : Blo 682313 1402429 := bbase (se 3 (by rfl) ⟨262955, by rfl⟩ : syracuseStep 1402429 = 525911) (by norm_num)
theorem B976541 : Blo 682313 976541 := bbase (se 3 (by rfl) ⟨183101, by rfl⟩ : syracuseStep 976541 = 366203) (by norm_num)
theorem B1730261 : Blo 682313 1730261 := bbase (se 7 (by rfl) ⟨20276, by rfl⟩ : syracuseStep 1730261 = 40553) (by norm_num)
theorem B8775701 : Blo 682313 8775701 := bbase (se 6 (by rfl) ⟨205680, by rfl⟩ : syracuseStep 8775701 = 411361) (by norm_num)
theorem B3467285 : Blo 682313 3467285 := bbase (se 6 (by rfl) ⟨81264, by rfl⟩ : syracuseStep 3467285 = 162529) (by norm_num)
theorem B1730605 : Blo 682313 1730605 := bbase (se 3 (by rfl) ⟨324488, by rfl⟩ : syracuseStep 1730605 = 648977) (by norm_num)
theorem B4384853 : Blo 682313 4384853 := bbase (se 8 (by rfl) ⟨25692, by rfl⟩ : syracuseStep 4384853 = 51385) (by norm_num)
theorem B1730717 : Blo 682313 1730717 := bbase (se 3 (by rfl) ⟨324509, by rfl⟩ : syracuseStep 1730717 = 649019) (by norm_num)
theorem B1665293 : Blo 682313 1665293 := bbase (se 3 (by rfl) ⟨312242, by rfl⟩ : syracuseStep 1665293 = 624485) (by norm_num)
theorem B1730909 : Blo 682313 1730909 := bbase (se 3 (by rfl) ⟨324545, by rfl⟩ : syracuseStep 1730909 = 649091) (by norm_num)
theorem B1599925 : Blo 682313 1599925 := bbase (se 5 (by rfl) ⟨74996, by rfl⟩ : syracuseStep 1599925 = 149993) (by norm_num)
theorem B1173941 : Blo 682313 1173941 := bbase (se 5 (by rfl) ⟨55028, by rfl⟩ : syracuseStep 1173941 = 110057) (by norm_num)
theorem B780949 : Blo 682313 780949 := bbase (se 6 (by rfl) ⟨18303, by rfl⟩ : syracuseStep 780949 = 36607) (by norm_num)
theorem B1731253 : Blo 682313 1731253 := bbase (se 5 (by rfl) ⟨81152, by rfl⟩ : syracuseStep 1731253 = 162305) (by norm_num)
theorem B1731365 : Blo 682313 1731365 := bbase (se 4 (by rfl) ⟨162315, by rfl⟩ : syracuseStep 1731365 = 324631) (by norm_num)
theorem B3206101 : Blo 682313 3206101 := bbase (se 7 (by rfl) ⟨37571, by rfl⟩ : syracuseStep 3206101 = 75143) (by norm_num)
theorem B1731557 : Blo 682313 1731557 := bbase (se 4 (by rfl) ⟨162333, by rfl⟩ : syracuseStep 1731557 = 324667) (by norm_num)
theorem B781309 : Blo 682313 781309 := bbase (se 3 (by rfl) ⟨146495, by rfl⟩ : syracuseStep 781309 = 292991) (by norm_num)
theorem B3599509 : Blo 682313 3599509 := bbase (se 6 (by rfl) ⟨84363, by rfl⟩ : syracuseStep 3599509 = 168727) (by norm_num)
theorem B1535237 : Blo 682313 1535237 := bbase (se 4 (by rfl) ⟨143928, by rfl⟩ : syracuseStep 1535237 = 287857) (by norm_num)
theorem B3468581 : Blo 682313 3468581 := bbase (se 4 (by rfl) ⟨325179, by rfl⟩ : syracuseStep 3468581 = 650359) (by norm_num)
theorem B1731901 : Blo 682313 1731901 := bbase (se 3 (by rfl) ⟨324731, by rfl⟩ : syracuseStep 1731901 = 649463) (by norm_num)
theorem B1535309 : Blo 682313 1535309 := bbase (se 3 (by rfl) ⟨287870, by rfl⟩ : syracuseStep 1535309 = 575741) (by norm_num)
theorem B2223445 : Blo 682313 2223445 := bbase (se 11 (by rfl) ⟨1628, by rfl⟩ : syracuseStep 2223445 = 3257) (by norm_num)
theorem B1535381 : Blo 682313 1535381 := bbase (se 6 (by rfl) ⟨35985, by rfl⟩ : syracuseStep 1535381 = 71971) (by norm_num)
theorem B781733 : Blo 682313 781733 := bbase (se 4 (by rfl) ⟨73287, by rfl⟩ : syracuseStep 781733 = 146575) (by norm_num)
theorem B1732013 : Blo 682313 1732013 := bbase (se 3 (by rfl) ⟨324752, by rfl⟩ : syracuseStep 1732013 = 649505) (by norm_num)
theorem B1535453 : Blo 682313 1535453 := bbase (se 3 (by rfl) ⟨287897, by rfl⟩ : syracuseStep 1535453 = 575795) (by norm_num)
theorem B1535525 : Blo 682313 1535525 := bbase (se 4 (by rfl) ⟨143955, by rfl⟩ : syracuseStep 1535525 = 287911) (by norm_num)
theorem B1535597 : Blo 682313 1535597 := bbase (se 3 (by rfl) ⟨287924, by rfl⟩ : syracuseStep 1535597 = 575849) (by norm_num)
theorem B1732205 : Blo 682313 1732205 := bbase (se 3 (by rfl) ⟨324788, by rfl⟩ : syracuseStep 1732205 = 649577) (by norm_num)
theorem B1535669 : Blo 682313 1535669 := bbase (se 5 (by rfl) ⟨71984, by rfl⟩ : syracuseStep 1535669 = 143969) (by norm_num)
theorem B1044149 : Blo 682313 1044149 := bbase (se 5 (by rfl) ⟨48944, by rfl⟩ : syracuseStep 1044149 = 97889) (by norm_num)
theorem B1535741 : Blo 682313 1535741 := bbase (se 3 (by rfl) ⟨287951, by rfl⟩ : syracuseStep 1535741 = 575903) (by norm_num)
theorem B1535813 : Blo 682313 1535813 := bbase (se 4 (by rfl) ⟨143982, by rfl⟩ : syracuseStep 1535813 = 287965) (by norm_num)
theorem B1535885 : Blo 682313 1535885 := bbase (se 3 (by rfl) ⟨287978, by rfl⟩ : syracuseStep 1535885 = 575957) (by norm_num)
theorem B1732549 : Blo 682313 1732549 := bbase (se 4 (by rfl) ⟨162426, by rfl⟩ : syracuseStep 1732549 = 324853) (by norm_num)
theorem B3502037 : Blo 682313 3502037 := bbase (se 7 (by rfl) ⟨41039, by rfl⟩ : syracuseStep 3502037 = 82079) (by norm_num)
theorem B1535957 : Blo 682313 1535957 := bbase (se 7 (by rfl) ⟨17999, by rfl⟩ : syracuseStep 1535957 = 35999) (by norm_num)
theorem B1536029 : Blo 682313 1536029 := bbase (se 3 (by rfl) ⟨288005, by rfl⟩ : syracuseStep 1536029 = 576011) (by norm_num)
theorem B1732661 : Blo 682313 1732661 := bbase (se 5 (by rfl) ⟨81218, by rfl⟩ : syracuseStep 1732661 = 162437) (by norm_num)
theorem B1536101 : Blo 682313 1536101 := bbase (se 4 (by rfl) ⟨144009, by rfl⟩ : syracuseStep 1536101 = 288019) (by norm_num)
theorem B2191477 : Blo 682313 2191477 := bbase (se 5 (by rfl) ⟨102725, by rfl⟩ : syracuseStep 2191477 = 205451) (by norm_num)
theorem B1536173 : Blo 682313 1536173 := bbase (se 3 (by rfl) ⟨288032, by rfl⟩ : syracuseStep 1536173 = 576065) (by norm_num)
theorem B1536245 : Blo 682313 1536245 := bbase (se 5 (by rfl) ⟨72011, by rfl⟩ : syracuseStep 1536245 = 144023) (by norm_num)
theorem B1732853 : Blo 682313 1732853 := bbase (se 5 (by rfl) ⟨81227, by rfl⟩ : syracuseStep 1732853 = 162455) (by norm_num)
theorem B1536317 : Blo 682313 1536317 := bbase (se 3 (by rfl) ⟨288059, by rfl⟩ : syracuseStep 1536317 = 576119) (by norm_num)
theorem B1667429 : Blo 682313 1667429 := bbase (se 4 (by rfl) ⟨156321, by rfl⟩ : syracuseStep 1667429 = 312643) (by norm_num)
theorem B1536389 : Blo 682313 1536389 := bbase (se 4 (by rfl) ⟨144036, by rfl⟩ : syracuseStep 1536389 = 288073) (by norm_num)
theorem B1536461 : Blo 682313 1536461 := bbase (se 3 (by rfl) ⟨288086, by rfl⟩ : syracuseStep 1536461 = 576173) (by norm_num)
theorem B5206517 : Blo 682313 5206517 := bbase (se 5 (by rfl) ⟨244055, by rfl⟩ : syracuseStep 5206517 = 488111) (by norm_num)
theorem B1536533 : Blo 682313 1536533 := bbase (se 6 (by rfl) ⟨36012, by rfl⟩ : syracuseStep 1536533 = 72025) (by norm_num)
theorem B3469877 : Blo 682313 3469877 := bbase (se 5 (by rfl) ⟨162650, by rfl⟩ : syracuseStep 3469877 = 325301) (by norm_num)
theorem B1733197 : Blo 682313 1733197 := bbase (se 3 (by rfl) ⟨324974, by rfl⟩ : syracuseStep 1733197 = 649949) (by norm_num)
theorem B1536605 : Blo 682313 1536605 := bbase (se 3 (by rfl) ⟨288113, by rfl⟩ : syracuseStep 1536605 = 576227) (by norm_num)
theorem B1536677 : Blo 682313 1536677 := bbase (se 4 (by rfl) ⟨144063, by rfl⟩ : syracuseStep 1536677 = 288127) (by norm_num)
theorem B2257573 : Blo 682313 2257573 := bbase (se 4 (by rfl) ⟨211647, by rfl⟩ : syracuseStep 2257573 = 423295) (by norm_num)
theorem B1733309 : Blo 682313 1733309 := bbase (se 3 (by rfl) ⟨324995, by rfl⟩ : syracuseStep 1733309 = 649991) (by norm_num)
theorem B750277 : Blo 682313 750277 := bbase (se 4 (by rfl) ⟨70338, by rfl⟩ : syracuseStep 750277 = 140677) (by norm_num)
theorem B1536749 : Blo 682313 1536749 := bbase (se 3 (by rfl) ⟨288140, by rfl⟩ : syracuseStep 1536749 = 576281) (by norm_num)
theorem B1536821 : Blo 682313 1536821 := bbase (se 5 (by rfl) ⟨72038, by rfl⟩ : syracuseStep 1536821 = 144077) (by norm_num)
theorem B4944725 : Blo 682313 4944725 := bbase (se 9 (by rfl) ⟨14486, by rfl⟩ : syracuseStep 4944725 = 28973) (by norm_num)
theorem B1536893 : Blo 682313 1536893 := bbase (se 3 (by rfl) ⟨288167, by rfl⟩ : syracuseStep 1536893 = 576335) (by norm_num)
theorem B1733501 : Blo 682313 1733501 := bbase (se 3 (by rfl) ⟨325031, by rfl⟩ : syracuseStep 1733501 = 650063) (by norm_num)
theorem B1536965 : Blo 682313 1536965 := bbase (se 4 (by rfl) ⟨144090, by rfl⟩ : syracuseStep 1536965 = 288181) (by norm_num)
theorem B1537037 : Blo 682313 1537037 := bbase (se 3 (by rfl) ⟨288194, by rfl⟩ : syracuseStep 1537037 = 576389) (by norm_num)
theorem B6583349 : Blo 682313 6583349 := bbase (se 5 (by rfl) ⟨308594, by rfl⟩ : syracuseStep 6583349 = 617189) (by norm_num)
theorem B1537109 : Blo 682313 1537109 := bbase (se 8 (by rfl) ⟨9006, by rfl⟩ : syracuseStep 1537109 = 18013) (by norm_num)
theorem B1537181 : Blo 682313 1537181 := bbase (se 3 (by rfl) ⟨288221, by rfl⟩ : syracuseStep 1537181 = 576443) (by norm_num)
theorem B7795925 : Blo 682313 7795925 := bbase (se 7 (by rfl) ⟨91358, by rfl⟩ : syracuseStep 7795925 = 182717) (by norm_num)
theorem B1733845 : Blo 682313 1733845 := bbase (se 7 (by rfl) ⟨20318, by rfl⟩ : syracuseStep 1733845 = 40637) (by norm_num)
theorem B1537253 : Blo 682313 1537253 := bbase (se 4 (by rfl) ⟨144117, by rfl⟩ : syracuseStep 1537253 = 288235) (by norm_num)
theorem B13137173 : Blo 682313 13137173 := bbase (se 6 (by rfl) ⟨307902, by rfl⟩ : syracuseStep 13137173 = 615805) (by norm_num)
theorem B1537325 : Blo 682313 1537325 := bbase (se 3 (by rfl) ⟨288248, by rfl⟩ : syracuseStep 1537325 = 576497) (by norm_num)
theorem B1733957 : Blo 682313 1733957 := bbase (se 4 (by rfl) ⟨162558, by rfl⟩ : syracuseStep 1733957 = 325117) (by norm_num)
theorem B1537397 : Blo 682313 1537397 := bbase (se 5 (by rfl) ⟨72065, by rfl⟩ : syracuseStep 1537397 = 144131) (by norm_num)
theorem B1537469 : Blo 682313 1537469 := bbase (se 3 (by rfl) ⟨288275, by rfl⟩ : syracuseStep 1537469 = 576551) (by norm_num)
theorem B1537541 : Blo 682313 1537541 := bbase (se 4 (by rfl) ⟨144144, by rfl⟩ : syracuseStep 1537541 = 288289) (by norm_num)
theorem B1734149 : Blo 682313 1734149 := bbase (se 4 (by rfl) ⟨162576, by rfl⟩ : syracuseStep 1734149 = 325153) (by norm_num)
theorem B1537613 : Blo 682313 1537613 := bbase (se 3 (by rfl) ⟨288302, by rfl⟩ : syracuseStep 1537613 = 576605) (by norm_num)
theorem B1537685 : Blo 682313 1537685 := bbase (se 6 (by rfl) ⟨36039, by rfl⟩ : syracuseStep 1537685 = 72079) (by norm_num)
theorem B1537757 : Blo 682313 1537757 := bbase (se 3 (by rfl) ⟨288329, by rfl⟩ : syracuseStep 1537757 = 576659) (by norm_num)
theorem B1111781 : Blo 682313 1111781 := bbase (se 4 (by rfl) ⟨104229, by rfl⟩ : syracuseStep 1111781 = 208459) (by norm_num)
theorem B1603309 : Blo 682313 1603309 := bbase (se 3 (by rfl) ⟨300620, by rfl⟩ : syracuseStep 1603309 = 601241) (by norm_num)
theorem B1537829 : Blo 682313 1537829 := bbase (se 4 (by rfl) ⟨144171, by rfl⟩ : syracuseStep 1537829 = 288343) (by norm_num)
theorem B3471173 : Blo 682313 3471173 := bbase (se 4 (by rfl) ⟨325422, by rfl⟩ : syracuseStep 3471173 = 650845) (by norm_num)
theorem B1734493 : Blo 682313 1734493 := bbase (se 3 (by rfl) ⟨325217, by rfl⟩ : syracuseStep 1734493 = 650435) (by norm_num)
theorem B1537901 : Blo 682313 1537901 := bbase (se 3 (by rfl) ⟨288356, by rfl⟩ : syracuseStep 1537901 = 576713) (by norm_num)
theorem B1537973 : Blo 682313 1537973 := bbase (se 5 (by rfl) ⟨72092, by rfl⟩ : syracuseStep 1537973 = 144185) (by norm_num)
theorem B1734605 : Blo 682313 1734605 := bbase (se 3 (by rfl) ⟨325238, by rfl⟩ : syracuseStep 1734605 = 650477) (by norm_num)
theorem B1538045 : Blo 682313 1538045 := bbase (se 3 (by rfl) ⟨288383, by rfl⟩ : syracuseStep 1538045 = 576767) (by norm_num)
theorem B1538117 : Blo 682313 1538117 := bbase (se 4 (by rfl) ⟨144198, by rfl⟩ : syracuseStep 1538117 = 288397) (by norm_num)
theorem B1538189 : Blo 682313 1538189 := bbase (se 3 (by rfl) ⟨288410, by rfl⟩ : syracuseStep 1538189 = 576821) (by norm_num)
theorem B1734797 : Blo 682313 1734797 := bbase (se 3 (by rfl) ⟨325274, by rfl⟩ : syracuseStep 1734797 = 650549) (by norm_num)
theorem B1407181 : Blo 682313 1407181 := bbase (se 3 (by rfl) ⟨263846, by rfl⟩ : syracuseStep 1407181 = 527693) (by norm_num)
theorem B1538261 : Blo 682313 1538261 := bbase (se 7 (by rfl) ⟨18026, by rfl⟩ : syracuseStep 1538261 = 36053) (by norm_num)
theorem B1538333 : Blo 682313 1538333 := bbase (se 3 (by rfl) ⟨288437, by rfl⟩ : syracuseStep 1538333 = 576875) (by norm_num)
theorem B1538405 : Blo 682313 1538405 := bbase (se 4 (by rfl) ⟨144225, by rfl⟩ : syracuseStep 1538405 = 288451) (by norm_num)
theorem B1538477 : Blo 682313 1538477 := bbase (se 3 (by rfl) ⟨288464, by rfl⟩ : syracuseStep 1538477 = 576929) (by norm_num)
theorem B1735141 : Blo 682313 1735141 := bbase (se 4 (by rfl) ⟨162669, by rfl⟩ : syracuseStep 1735141 = 325339) (by norm_num)
theorem B1538549 : Blo 682313 1538549 := bbase (se 5 (by rfl) ⟨72119, by rfl⟩ : syracuseStep 1538549 = 144239) (by norm_num)
theorem B1538621 : Blo 682313 1538621 := bbase (se 3 (by rfl) ⟨288491, by rfl⟩ : syracuseStep 1538621 = 576983) (by norm_num)
theorem B1735253 : Blo 682313 1735253 := bbase (se 8 (by rfl) ⟨10167, by rfl⟩ : syracuseStep 1735253 = 20335) (by norm_num)
theorem B1538693 : Blo 682313 1538693 := bbase (se 4 (by rfl) ⟨144252, by rfl⟩ : syracuseStep 1538693 = 288505) (by norm_num)
theorem B1538765 : Blo 682313 1538765 := bbase (se 3 (by rfl) ⟨288518, by rfl⟩ : syracuseStep 1538765 = 577037) (by norm_num)
theorem B1538837 : Blo 682313 1538837 := bbase (se 6 (by rfl) ⟨36066, by rfl⟩ : syracuseStep 1538837 = 72133) (by norm_num)
theorem B1735445 : Blo 682313 1735445 := bbase (se 6 (by rfl) ⟨40674, by rfl⟩ : syracuseStep 1735445 = 81349) (by norm_num)
theorem B1538909 : Blo 682313 1538909 := bbase (se 3 (by rfl) ⟨288545, by rfl⟩ : syracuseStep 1538909 = 577091) (by norm_num)
theorem B1538981 : Blo 682313 1538981 := bbase (se 4 (by rfl) ⟨144279, by rfl⟩ : syracuseStep 1538981 = 288559) (by norm_num)
theorem B1539053 : Blo 682313 1539053 := bbase (se 3 (by rfl) ⟨288572, by rfl⟩ : syracuseStep 1539053 = 577145) (by norm_num)
theorem B1539125 : Blo 682313 1539125 := bbase (se 5 (by rfl) ⟨72146, by rfl⟩ : syracuseStep 1539125 = 144293) (by norm_num)
theorem B3472469 : Blo 682313 3472469 := bbase (se 8 (by rfl) ⟨20346, by rfl⟩ : syracuseStep 3472469 = 40693) (by norm_num)
theorem B1735789 : Blo 682313 1735789 := bbase (se 3 (by rfl) ⟨325460, by rfl⟩ : syracuseStep 1735789 = 650921) (by norm_num)
theorem B1539197 : Blo 682313 1539197 := bbase (se 3 (by rfl) ⟨288599, by rfl⟩ : syracuseStep 1539197 = 577199) (by norm_num)
theorem B2915477 : Blo 682313 2915477 := bbase (se 6 (by rfl) ⟨68331, by rfl⟩ : syracuseStep 2915477 = 136663) (by norm_num)
theorem B1539269 : Blo 682313 1539269 := bbase (se 4 (by rfl) ⟨144306, by rfl⟩ : syracuseStep 1539269 = 288613) (by norm_num)
theorem B1735901 : Blo 682313 1735901 := bbase (se 3 (by rfl) ⟨325481, by rfl⟩ : syracuseStep 1735901 = 650963) (by norm_num)
theorem B1539341 : Blo 682313 1539341 := bbase (se 3 (by rfl) ⟨288626, by rfl⟩ : syracuseStep 1539341 = 577253) (by norm_num)
theorem B1539413 : Blo 682313 1539413 := bbase (se 11 (by rfl) ⟨1127, by rfl⟩ : syracuseStep 1539413 = 2255) (by norm_num)
theorem B1539485 : Blo 682313 1539485 := bbase (se 3 (by rfl) ⟨288653, by rfl⟩ : syracuseStep 1539485 = 577307) (by norm_num)
theorem B1736093 : Blo 682313 1736093 := bbase (se 3 (by rfl) ⟨325517, by rfl⟩ : syracuseStep 1736093 = 651035) (by norm_num)
theorem B1539557 : Blo 682313 1539557 := bbase (se 4 (by rfl) ⟨144333, by rfl⟩ : syracuseStep 1539557 = 288667) (by norm_num)
theorem B1539629 : Blo 682313 1539629 := bbase (se 3 (by rfl) ⟨288680, by rfl⟩ : syracuseStep 1539629 = 577361) (by norm_num)
theorem B1539701 : Blo 682313 1539701 := bbase (se 5 (by rfl) ⟨72173, by rfl⟩ : syracuseStep 1539701 = 144347) (by norm_num)
theorem B1539773 : Blo 682313 1539773 := bbase (se 3 (by rfl) ⟨288707, by rfl⟩ : syracuseStep 1539773 = 577415) (by norm_num)
theorem B1736437 : Blo 682313 1736437 := bbase (se 5 (by rfl) ⟨81395, by rfl⟩ : syracuseStep 1736437 = 162791) (by norm_num)
theorem B1539845 : Blo 682313 1539845 := bbase (se 4 (by rfl) ⟨144360, by rfl⟩ : syracuseStep 1539845 = 288721) (by norm_num)
theorem B1539917 : Blo 682313 1539917 := bbase (se 3 (by rfl) ⟨288734, by rfl⟩ : syracuseStep 1539917 = 577469) (by norm_num)
theorem B1736549 : Blo 682313 1736549 := bbase (se 4 (by rfl) ⟨162801, by rfl⟩ : syracuseStep 1736549 = 325603) (by norm_num)
theorem B1539989 : Blo 682313 1539989 := bbase (se 6 (by rfl) ⟨36093, by rfl⟩ : syracuseStep 1539989 = 72187) (by norm_num)
theorem B3899285 : Blo 682313 3899285 := bbase (se 6 (by rfl) ⟨91389, by rfl⟩ : syracuseStep 3899285 = 182779) (by norm_num)
theorem B1540061 : Blo 682313 1540061 := bbase (se 3 (by rfl) ⟨288761, by rfl⟩ : syracuseStep 1540061 = 577523) (by norm_num)
theorem B28508213 : Blo 682313 28508213 := bstep (se 5 (by rfl) ⟨1336322, by rfl⟩ : syracuseStep 28508213 = 2672645) B2672645
theorem B1540241 : Blo 682313 1540241 := bstep (se 2 (by rfl) ⟨577590, by rfl⟩ : syracuseStep 1540241 = 1155181) B1155181
theorem B1540259 : Blo 682313 1540259 := bstep (se 1 (by rfl) ⟨1155194, by rfl⟩ : syracuseStep 1540259 = 2310389) B2310389
theorem B4686179 : Blo 682313 4686179 := bstep (se 1 (by rfl) ⟨3514634, by rfl⟩ : syracuseStep 4686179 = 7029269) B7029269
theorem B2195885 : Blo 682313 2195885 := bstep (se 3 (by rfl) ⟨411728, by rfl⟩ : syracuseStep 2195885 = 823457) B823457
theorem B1540529 : Blo 682313 1540529 := bstep (se 2 (by rfl) ⟨577698, by rfl⟩ : syracuseStep 1540529 = 1155397) B1155397
theorem B1540547 : Blo 682313 1540547 := bstep (se 1 (by rfl) ⟨1155410, by rfl⟩ : syracuseStep 1540547 = 2310821) B2310821
theorem B12485173 : Blo 682313 12485173 := bstep (se 5 (by rfl) ⟨585242, by rfl⟩ : syracuseStep 12485173 = 1170485) B1170485
theorem B1540817 : Blo 682313 1540817 := bstep (se 2 (by rfl) ⟨577806, by rfl⟩ : syracuseStep 1540817 = 1155613) B1155613
theorem B1540835 : Blo 682313 1540835 := bstep (se 1 (by rfl) ⟨1155626, by rfl⟩ : syracuseStep 1540835 = 2311253) B2311253
theorem B49873805 : Blo 682313 49873805 := bstep (se 3 (by rfl) ⟨9351338, by rfl⟩ : syracuseStep 49873805 = 18702677) B18702677
theorem B1541105 : Blo 682313 1541105 := bstep (se 2 (by rfl) ⟨577914, by rfl⟩ : syracuseStep 1541105 = 1155829) B1155829
theorem B1541123 : Blo 682313 1541123 := bstep (se 1 (by rfl) ⟨1155842, by rfl⟩ : syracuseStep 1541123 = 2311685) B2311685
theorem B9372685 : Blo 682313 9372685 := bstep (se 3 (by rfl) ⟨1757378, by rfl⟩ : syracuseStep 9372685 = 3514757) B3514757
theorem B5211377 : Blo 682313 5211377 := bstep (se 2 (by rfl) ⟨1954266, by rfl⟩ : syracuseStep 5211377 = 3908533) B3908533
theorem B1541393 : Blo 682313 1541393 := bstep (se 2 (by rfl) ⟨578022, by rfl⟩ : syracuseStep 1541393 = 1156045) B1156045
theorem B1541411 : Blo 682313 1541411 := bstep (se 1 (by rfl) ⟨1156058, by rfl⟩ : syracuseStep 1541411 = 2312117) B2312117
theorem B2917937 : Blo 682313 2917937 := bstep (se 2 (by rfl) ⟨1094226, by rfl⟩ : syracuseStep 2917937 = 2188453) B2188453
theorem B1541681 : Blo 682313 1541681 := bstep (se 2 (by rfl) ⟨578130, by rfl⟩ : syracuseStep 1541681 = 1156261) B1156261
theorem B1541699 : Blo 682313 1541699 := bstep (se 1 (by rfl) ⟨1156274, by rfl⟩ : syracuseStep 1541699 = 2312549) B2312549
theorem B3901061 : Blo 682313 3901061 := bstep (se 4 (by rfl) ⟨365724, by rfl⟩ : syracuseStep 3901061 = 731449) B731449
theorem B1541969 : Blo 682313 1541969 := bstep (se 2 (by rfl) ⟨578238, by rfl⟩ : syracuseStep 1541969 = 1156477) B1156477
theorem B1541987 : Blo 682313 1541987 := bstep (se 1 (by rfl) ⟨1156490, by rfl⟩ : syracuseStep 1541987 = 2312981) B2312981
theorem B2197475 : Blo 682313 2197475 := bstep (se 1 (by rfl) ⟨1648106, by rfl⟩ : syracuseStep 2197475 = 3296213) B3296213
theorem B3901517 : Blo 682313 3901517 := bstep (se 3 (by rfl) ⟨731534, by rfl⟩ : syracuseStep 3901517 = 1463069) B1463069
theorem B1869905 : Blo 682313 1869905 := bstep (se 2 (by rfl) ⟨701214, by rfl⟩ : syracuseStep 1869905 = 1402429) B1402429
theorem B1542257 : Blo 682313 1542257 := bstep (se 2 (by rfl) ⟨578346, by rfl⟩ : syracuseStep 1542257 = 1156693) B1156693
theorem B1542275 : Blo 682313 1542275 := bstep (se 1 (by rfl) ⟨1156706, by rfl⟩ : syracuseStep 1542275 = 2313413) B2313413
theorem B3279203 : Blo 682313 3279203 := bstep (se 1 (by rfl) ⟨2459402, by rfl⟩ : syracuseStep 3279203 = 4918805) B4918805
theorem B1542545 : Blo 682313 1542545 := bstep (se 2 (by rfl) ⟨578454, by rfl⟩ : syracuseStep 1542545 = 1156909) B1156909
theorem B1542563 : Blo 682313 1542563 := bstep (se 1 (by rfl) ⟨1156922, by rfl⟩ : syracuseStep 1542563 = 2313845) B2313845
theorem B2918861 : Blo 682313 2918861 := bstep (se 3 (by rfl) ⟨547286, by rfl⟩ : syracuseStep 2918861 = 1094573) B1094573
theorem B1542833 : Blo 682313 1542833 := bstep (se 2 (by rfl) ⟨578562, by rfl⟩ : syracuseStep 1542833 = 1157125) B1157125
theorem B1542851 : Blo 682313 1542851 := bstep (se 1 (by rfl) ⟨1157138, by rfl⟩ : syracuseStep 1542851 = 2314277) B2314277
theorem B2591459 : Blo 682313 2591459 := bstep (se 1 (by rfl) ⟨1943594, by rfl⟩ : syracuseStep 2591459 = 3887189) B3887189
theorem B2591473 : Blo 682313 2591473 := bstep (se 2 (by rfl) ⟨971802, by rfl⟩ : syracuseStep 2591473 = 1943605) B1943605
theorem B822035 : Blo 682313 822035 := bstep (se 1 (by rfl) ⟨616526, by rfl⟩ : syracuseStep 822035 = 1233053) B1233053
theorem B887683 : Blo 682313 887683 := bstep (se 1 (by rfl) ⟨665762, by rfl⟩ : syracuseStep 887683 = 1331525) B1331525
theorem B4393925 : Blo 682313 4393925 := bstep (se 4 (by rfl) ⟨411930, by rfl⟩ : syracuseStep 4393925 = 823861) B823861
theorem B1543121 : Blo 682313 1543121 := bstep (se 2 (by rfl) ⟨578670, by rfl⟩ : syracuseStep 1543121 = 1157341) B1157341
theorem B1543139 : Blo 682313 1543139 := bstep (se 1 (by rfl) ⟨1157354, by rfl⟩ : syracuseStep 1543139 = 2314709) B2314709
theorem B1641475 : Blo 682313 1641475 := bstep (se 1 (by rfl) ⟨1231106, by rfl⟩ : syracuseStep 1641475 = 2462213) B2462213
theorem B2460785 : Blo 682313 2460785 := bstep (se 2 (by rfl) ⟨922794, by rfl⟩ : syracuseStep 2460785 = 1845589) B1845589
theorem B2133233 : Blo 682313 2133233 := bstep (se 2 (by rfl) ⟨799962, by rfl⟩ : syracuseStep 2133233 = 1599925) B1599925
theorem B1543409 : Blo 682313 1543409 := bstep (se 2 (by rfl) ⟨578778, by rfl⟩ : syracuseStep 1543409 = 1157557) B1157557
theorem B1543427 : Blo 682313 1543427 := bstep (se 1 (by rfl) ⟨1157570, by rfl⟩ : syracuseStep 1543427 = 2315141) B2315141
theorem B1543697 : Blo 682313 1543697 := bstep (se 2 (by rfl) ⟨578886, by rfl⟩ : syracuseStep 1543697 = 1157773) B1157773
theorem B1543715 : Blo 682313 1543715 := bstep (se 1 (by rfl) ⟨1157786, by rfl⟩ : syracuseStep 1543715 = 2315573) B2315573
theorem B1543985 : Blo 682313 1543985 := bstep (se 2 (by rfl) ⟨578994, by rfl⟩ : syracuseStep 1543985 = 1157989) B1157989
theorem B1544003 : Blo 682313 1544003 := bstep (se 1 (by rfl) ⟨1158002, by rfl⟩ : syracuseStep 1544003 = 2316005) B2316005
theorem B11079821 : Blo 682313 11079821 := bstep (se 3 (by rfl) ⟨2077466, by rfl⟩ : syracuseStep 11079821 = 4154933) B4154933
theorem B2592931 : Blo 682313 2592931 := bstep (se 1 (by rfl) ⟨1944698, by rfl⟩ : syracuseStep 2592931 = 3889397) B3889397
theorem B7901381 : Blo 682313 7901381 := bstep (se 4 (by rfl) ⟨740754, by rfl⟩ : syracuseStep 7901381 = 1481509) B1481509
theorem B1151489 : Blo 682313 1151489 := bstep (se 2 (by rfl) ⟨431808, by rfl⟩ : syracuseStep 1151489 = 863617) B863617
theorem B1151617 : Blo 682313 1151617 := bstep (se 2 (by rfl) ⟨431856, by rfl⟩ : syracuseStep 1151617 = 863713) B863713
theorem B1151651 : Blo 682313 1151651 := bstep (se 1 (by rfl) ⟨863738, by rfl⟩ : syracuseStep 1151651 = 1727477) B1727477
theorem B1250051 : Blo 682313 1250051 := bstep (se 1 (by rfl) ⟨937538, by rfl⟩ : syracuseStep 1250051 = 1875077) B1875077
theorem B1151779 : Blo 682313 1151779 := bstep (se 1 (by rfl) ⟨863834, by rfl⟩ : syracuseStep 1151779 = 1727669) B1727669
theorem B1643377 : Blo 682313 1643377 := bstep (se 2 (by rfl) ⟨616266, by rfl⟩ : syracuseStep 1643377 = 1232533) B1232533
theorem B1151921 : Blo 682313 1151921 := bstep (se 2 (by rfl) ⟨431970, by rfl⟩ : syracuseStep 1151921 = 863941) B863941
theorem B3904433 : Blo 682313 3904433 := bstep (se 2 (by rfl) ⟨1464162, by rfl⟩ : syracuseStep 3904433 = 2928325) B2928325
theorem B922627 : Blo 682313 922627 := bstep (se 1 (by rfl) ⟨691970, by rfl⟩ : syracuseStep 922627 = 1383941) B1383941
theorem B1152049 : Blo 682313 1152049 := bstep (se 2 (by rfl) ⟨432018, by rfl⟩ : syracuseStep 1152049 = 864037) B864037
theorem B1152083 : Blo 682313 1152083 := bstep (se 1 (by rfl) ⟨864062, by rfl⟩ : syracuseStep 1152083 = 1728125) B1728125
theorem B1152211 : Blo 682313 1152211 := bstep (se 1 (by rfl) ⟨864158, by rfl⟩ : syracuseStep 1152211 = 1728317) B1728317
theorem B922897 : Blo 682313 922897 := bstep (se 2 (by rfl) ⟨346086, by rfl⟩ : syracuseStep 922897 = 692173) B692173
theorem B1152353 : Blo 682313 1152353 := bstep (se 2 (by rfl) ⟨432132, by rfl⟩ : syracuseStep 1152353 = 864265) B864265
theorem B1152481 : Blo 682313 1152481 := bstep (se 2 (by rfl) ⟨432180, by rfl⟩ : syracuseStep 1152481 = 864361) B864361
theorem B2921969 : Blo 682313 2921969 := bstep (se 2 (by rfl) ⟨1095738, by rfl⟩ : syracuseStep 2921969 = 2191477) B2191477
theorem B1152515 : Blo 682313 1152515 := bstep (se 1 (by rfl) ⟨864386, by rfl⟩ : syracuseStep 1152515 = 1728773) B1728773
theorem B2463281 : Blo 682313 2463281 := bstep (se 2 (by rfl) ⟨923730, by rfl⟩ : syracuseStep 2463281 = 1847461) B1847461
theorem B1152643 : Blo 682313 1152643 := bstep (se 1 (by rfl) ⟨864482, by rfl⟩ : syracuseStep 1152643 = 1728965) B1728965
theorem B9508549 : Blo 682313 9508549 := bstep (se 4 (by rfl) ⟨891426, by rfl⟩ : syracuseStep 9508549 = 1782853) B1782853
theorem B1152785 : Blo 682313 1152785 := bstep (se 2 (by rfl) ⟨432294, by rfl⟩ : syracuseStep 1152785 = 864589) B864589
theorem B3610403 : Blo 682313 3610403 := bstep (se 1 (by rfl) ⟨2707802, by rfl⟩ : syracuseStep 3610403 = 5415605) B5415605
theorem B1152913 : Blo 682313 1152913 := bstep (se 2 (by rfl) ⟨432342, by rfl⟩ : syracuseStep 1152913 = 864685) B864685
theorem B1152947 : Blo 682313 1152947 := bstep (se 1 (by rfl) ⟨864710, by rfl⟩ : syracuseStep 1152947 = 1729421) B1729421
theorem B3282893 : Blo 682313 3282893 := bstep (se 3 (by rfl) ⟨615542, by rfl⟩ : syracuseStep 3282893 = 1231085) B1231085
theorem B1251281 : Blo 682313 1251281 := bstep (se 2 (by rfl) ⟨469230, by rfl⟩ : syracuseStep 1251281 = 938461) B938461
theorem B923665 : Blo 682313 923665 := bstep (se 2 (by rfl) ⟨346374, by rfl⟩ : syracuseStep 923665 = 692749) B692749
theorem B1153075 : Blo 682313 1153075 := bstep (se 1 (by rfl) ⟨864806, by rfl⟩ : syracuseStep 1153075 = 1729613) B1729613
theorem B5544035 : Blo 682313 5544035 := bstep (se 1 (by rfl) ⟨4158026, by rfl⟩ : syracuseStep 5544035 = 8316053) B8316053
theorem B2463857 : Blo 682313 2463857 := bstep (se 2 (by rfl) ⟨923946, by rfl⟩ : syracuseStep 2463857 = 1847893) B1847893
theorem B1153217 : Blo 682313 1153217 := bstep (se 2 (by rfl) ⟨432456, by rfl⟩ : syracuseStep 1153217 = 864913) B864913
theorem B1153345 : Blo 682313 1153345 := bstep (se 2 (by rfl) ⟨432504, by rfl⟩ : syracuseStep 1153345 = 865009) B865009
theorem B2595149 : Blo 682313 2595149 := bstep (se 3 (by rfl) ⟨486590, by rfl⟩ : syracuseStep 2595149 = 973181) B973181
theorem B1153379 : Blo 682313 1153379 := bstep (se 1 (by rfl) ⟨865034, by rfl⟩ : syracuseStep 1153379 = 1730069) B1730069
theorem B3905891 : Blo 682313 3905891 := bstep (se 1 (by rfl) ⟨2929418, by rfl⟩ : syracuseStep 3905891 = 5858837) B5858837
theorem B7772597 : Blo 682313 7772597 := bstep (se 5 (by rfl) ⟨364340, by rfl⟩ : syracuseStep 7772597 = 728681) B728681
theorem B1153507 : Blo 682313 1153507 := bstep (se 1 (by rfl) ⟨865130, by rfl⟩ : syracuseStep 1153507 = 1730261) B1730261
theorem B17570357 : Blo 682313 17570357 := bstep (se 5 (by rfl) ⟨823610, by rfl⟩ : syracuseStep 17570357 = 1647221) B1647221
theorem B1153649 : Blo 682313 1153649 := bstep (se 2 (by rfl) ⟨432618, by rfl⟩ : syracuseStep 1153649 = 865237) B865237
theorem B2923235 : Blo 682313 2923235 := bstep (se 1 (by rfl) ⟨2192426, by rfl⟩ : syracuseStep 2923235 = 4384853) B4384853
theorem B1153777 : Blo 682313 1153777 := bstep (se 2 (by rfl) ⟨432666, by rfl⟩ : syracuseStep 1153777 = 865333) B865333
theorem B3709709 : Blo 682313 3709709 := bstep (se 3 (by rfl) ⟨695570, by rfl⟩ : syracuseStep 3709709 = 1391141) B1391141
theorem B1153811 : Blo 682313 1153811 := bstep (se 1 (by rfl) ⟨865358, by rfl⟩ : syracuseStep 1153811 = 1730717) B1730717
theorem B1153939 : Blo 682313 1153939 := bstep (se 1 (by rfl) ⟨865454, by rfl⟩ : syracuseStep 1153939 = 1730909) B1730909
theorem B1154081 : Blo 682313 1154081 := bstep (se 2 (by rfl) ⟨432780, by rfl⟩ : syracuseStep 1154081 = 865561) B865561
theorem B1186963 : Blo 682313 1186963 := bstep (se 1 (by rfl) ⟨890222, by rfl⟩ : syracuseStep 1186963 = 1780445) B1780445
theorem B1154209 : Blo 682313 1154209 := bstep (se 2 (by rfl) ⟨432828, by rfl⟩ : syracuseStep 1154209 = 865657) B865657
theorem B1154243 : Blo 682313 1154243 := bstep (se 1 (by rfl) ⟨865682, by rfl⟩ : syracuseStep 1154243 = 1731365) B1731365
theorem B1154371 : Blo 682313 1154371 := bstep (se 1 (by rfl) ⟨865778, by rfl⟩ : syracuseStep 1154371 = 1731557) B1731557
theorem B3906893 : Blo 682313 3906893 := bstep (se 3 (by rfl) ⟨732542, by rfl⟩ : syracuseStep 3906893 = 1465085) B1465085
theorem B1154513 : Blo 682313 1154513 := bstep (se 2 (by rfl) ⟨432942, by rfl⟩ : syracuseStep 1154513 = 865885) B865885
theorem B1023473 : Blo 682313 1023473 := bstep (se 2 (by rfl) ⟨383802, by rfl⟩ : syracuseStep 1023473 = 767605) B767605
theorem B1023491 : Blo 682313 1023491 := bstep (se 1 (by rfl) ⟨767618, by rfl⟩ : syracuseStep 1023491 = 1535237) B1535237
theorem B3120653 : Blo 682313 3120653 := bstep (se 3 (by rfl) ⟨585122, by rfl⟩ : syracuseStep 3120653 = 1170245) B1170245
theorem B1023521 : Blo 682313 1023521 := bstep (se 2 (by rfl) ⟨383820, by rfl⟩ : syracuseStep 1023521 = 767641) B767641
theorem B1023539 : Blo 682313 1023539 := bstep (se 1 (by rfl) ⟨767654, by rfl⟩ : syracuseStep 1023539 = 1535309) B1535309
theorem B1023569 : Blo 682313 1023569 := bstep (se 2 (by rfl) ⟨383838, by rfl⟩ : syracuseStep 1023569 = 767677) B767677
theorem B1154641 : Blo 682313 1154641 := bstep (se 2 (by rfl) ⟨432990, by rfl⟩ : syracuseStep 1154641 = 865981) B865981
theorem B1023587 : Blo 682313 1023587 := bstep (se 1 (by rfl) ⟨767690, by rfl⟩ : syracuseStep 1023587 = 1535381) B1535381
theorem B1154675 : Blo 682313 1154675 := bstep (se 1 (by rfl) ⟨866006, by rfl⟩ : syracuseStep 1154675 = 1732013) B1732013
theorem B1023617 : Blo 682313 1023617 := bstep (se 2 (by rfl) ⟨383856, by rfl⟩ : syracuseStep 1023617 = 767713) B767713
theorem B2137745 : Blo 682313 2137745 := bstep (se 2 (by rfl) ⟨801654, by rfl⟩ : syracuseStep 2137745 = 1603309) B1603309
theorem B1023635 : Blo 682313 1023635 := bstep (se 1 (by rfl) ⟨767726, by rfl⟩ : syracuseStep 1023635 = 1535453) B1535453
theorem B1023665 : Blo 682313 1023665 := bstep (se 2 (by rfl) ⟨383874, by rfl⟩ : syracuseStep 1023665 = 767749) B767749
theorem B1023683 : Blo 682313 1023683 := bstep (se 1 (by rfl) ⟨767762, by rfl⟩ : syracuseStep 1023683 = 1535525) B1535525
theorem B1023713 : Blo 682313 1023713 := bstep (se 2 (by rfl) ⟨383892, by rfl⟩ : syracuseStep 1023713 = 767785) B767785
theorem B1023731 : Blo 682313 1023731 := bstep (se 1 (by rfl) ⟨767798, by rfl⟩ : syracuseStep 1023731 = 1535597) B1535597
theorem B1154803 : Blo 682313 1154803 := bstep (se 1 (by rfl) ⟨866102, by rfl⟩ : syracuseStep 1154803 = 1732205) B1732205
theorem B1023761 : Blo 682313 1023761 := bstep (se 2 (by rfl) ⟨383910, by rfl⟩ : syracuseStep 1023761 = 767821) B767821
theorem B1023779 : Blo 682313 1023779 := bstep (se 1 (by rfl) ⟨767834, by rfl⟩ : syracuseStep 1023779 = 1535669) B1535669
theorem B1023809 : Blo 682313 1023809 := bstep (se 2 (by rfl) ⟨383928, by rfl⟩ : syracuseStep 1023809 = 767857) B767857
theorem B1023827 : Blo 682313 1023827 := bstep (se 1 (by rfl) ⟨767870, by rfl⟩ : syracuseStep 1023827 = 1535741) B1535741
theorem B1023857 : Blo 682313 1023857 := bstep (se 2 (by rfl) ⟨383946, by rfl⟩ : syracuseStep 1023857 = 767893) B767893
theorem B1154945 : Blo 682313 1154945 := bstep (se 2 (by rfl) ⟨433104, by rfl⟩ : syracuseStep 1154945 = 866209) B866209
theorem B1023875 : Blo 682313 1023875 := bstep (se 1 (by rfl) ⟨767906, by rfl⟩ : syracuseStep 1023875 = 1535813) B1535813
theorem B1023905 : Blo 682313 1023905 := bstep (se 2 (by rfl) ⟨383964, by rfl⟩ : syracuseStep 1023905 = 767929) B767929
theorem B1023923 : Blo 682313 1023923 := bstep (se 1 (by rfl) ⟨767942, by rfl⟩ : syracuseStep 1023923 = 1535885) B1535885
theorem B1646531 : Blo 682313 1646531 := bstep (se 1 (by rfl) ⟨1234898, by rfl⟩ : syracuseStep 1646531 = 2469797) B2469797
theorem B1023953 : Blo 682313 1023953 := bstep (se 2 (by rfl) ⟨383982, by rfl⟩ : syracuseStep 1023953 = 767965) B767965
theorem B2334691 : Blo 682313 2334691 := bstep (se 1 (by rfl) ⟨1751018, by rfl⟩ : syracuseStep 2334691 = 3502037) B3502037
theorem B1023971 : Blo 682313 1023971 := bstep (se 1 (by rfl) ⟨767978, by rfl⟩ : syracuseStep 1023971 = 1535957) B1535957
theorem B1024001 : Blo 682313 1024001 := bstep (se 2 (by rfl) ⟨384000, by rfl⟩ : syracuseStep 1024001 = 768001) B768001
theorem B1155073 : Blo 682313 1155073 := bstep (se 2 (by rfl) ⟨433152, by rfl⟩ : syracuseStep 1155073 = 866305) B866305
theorem B1024019 : Blo 682313 1024019 := bstep (se 1 (by rfl) ⟨768014, by rfl⟩ : syracuseStep 1024019 = 1536029) B1536029
theorem B1155107 : Blo 682313 1155107 := bstep (se 1 (by rfl) ⟨866330, by rfl⟩ : syracuseStep 1155107 = 1732661) B1732661
theorem B1024049 : Blo 682313 1024049 := bstep (se 2 (by rfl) ⟨384018, by rfl⟩ : syracuseStep 1024049 = 768037) B768037
theorem B1024067 : Blo 682313 1024067 := bstep (se 1 (by rfl) ⟨768050, by rfl⟩ : syracuseStep 1024067 = 1536101) B1536101
theorem B1024097 : Blo 682313 1024097 := bstep (se 2 (by rfl) ⟨384036, by rfl⟩ : syracuseStep 1024097 = 768073) B768073
theorem B1024115 : Blo 682313 1024115 := bstep (se 1 (by rfl) ⟨768086, by rfl⟩ : syracuseStep 1024115 = 1536173) B1536173
theorem B1646723 : Blo 682313 1646723 := bstep (se 1 (by rfl) ⟨1235042, by rfl⟩ : syracuseStep 1646723 = 2470085) B2470085
theorem B1024145 : Blo 682313 1024145 := bstep (se 2 (by rfl) ⟨384054, by rfl⟩ : syracuseStep 1024145 = 768109) B768109
theorem B1024163 : Blo 682313 1024163 := bstep (se 1 (by rfl) ⟨768122, by rfl⟩ : syracuseStep 1024163 = 1536245) B1536245
theorem B1155235 : Blo 682313 1155235 := bstep (se 1 (by rfl) ⟨866426, by rfl⟩ : syracuseStep 1155235 = 1732853) B1732853
theorem B1024193 : Blo 682313 1024193 := bstep (se 2 (by rfl) ⟨384072, by rfl⟩ : syracuseStep 1024193 = 768145) B768145
theorem B1024211 : Blo 682313 1024211 := bstep (se 1 (by rfl) ⟨768158, by rfl⟩ : syracuseStep 1024211 = 1536317) B1536317
theorem B1024241 : Blo 682313 1024241 := bstep (se 2 (by rfl) ⟨384090, by rfl⟩ : syracuseStep 1024241 = 768181) B768181
theorem B1024259 : Blo 682313 1024259 := bstep (se 1 (by rfl) ⟨768194, by rfl⟩ : syracuseStep 1024259 = 1536389) B1536389
theorem B1876241 : Blo 682313 1876241 := bstep (se 2 (by rfl) ⟨703590, by rfl⟩ : syracuseStep 1876241 = 1407181) B1407181
theorem B1024289 : Blo 682313 1024289 := bstep (se 2 (by rfl) ⟨384108, by rfl⟩ : syracuseStep 1024289 = 768217) B768217
theorem B1155377 : Blo 682313 1155377 := bstep (se 2 (by rfl) ⟨433266, by rfl⟩ : syracuseStep 1155377 = 866533) B866533
theorem B1024307 : Blo 682313 1024307 := bstep (se 1 (by rfl) ⟨768230, by rfl⟩ : syracuseStep 1024307 = 1536461) B1536461
theorem B1024337 : Blo 682313 1024337 := bstep (se 2 (by rfl) ⟨384126, by rfl⟩ : syracuseStep 1024337 = 768253) B768253
theorem B1024355 : Blo 682313 1024355 := bstep (se 1 (by rfl) ⟨768266, by rfl⟩ : syracuseStep 1024355 = 1536533) B1536533
theorem B1024385 : Blo 682313 1024385 := bstep (se 2 (by rfl) ⟨384144, by rfl⟩ : syracuseStep 1024385 = 768289) B768289
theorem B1024403 : Blo 682313 1024403 := bstep (se 1 (by rfl) ⟨768302, by rfl⟩ : syracuseStep 1024403 = 1536605) B1536605
theorem B1024433 : Blo 682313 1024433 := bstep (se 2 (by rfl) ⟨384162, by rfl⟩ : syracuseStep 1024433 = 768325) B768325
theorem B1155505 : Blo 682313 1155505 := bstep (se 2 (by rfl) ⟨433314, by rfl⟩ : syracuseStep 1155505 = 866629) B866629
theorem B1024451 : Blo 682313 1024451 := bstep (se 1 (by rfl) ⟨768338, by rfl⟩ : syracuseStep 1024451 = 1536677) B1536677
theorem B1155539 : Blo 682313 1155539 := bstep (se 1 (by rfl) ⟨866654, by rfl⟩ : syracuseStep 1155539 = 1733309) B1733309
theorem B1024481 : Blo 682313 1024481 := bstep (se 2 (by rfl) ⟨384180, by rfl⟩ : syracuseStep 1024481 = 768361) B768361
theorem B1024499 : Blo 682313 1024499 := bstep (se 1 (by rfl) ⟨768374, by rfl⟩ : syracuseStep 1024499 = 1536749) B1536749
theorem B729587 : Blo 682313 729587 := bstep (se 1 (by rfl) ⟨547190, by rfl⟩ : syracuseStep 729587 = 1094381) B1094381
theorem B1024529 : Blo 682313 1024529 := bstep (se 2 (by rfl) ⟨384198, by rfl⟩ : syracuseStep 1024529 = 768397) B768397
theorem B1024547 : Blo 682313 1024547 := bstep (se 1 (by rfl) ⟨768410, by rfl⟩ : syracuseStep 1024547 = 1536821) B1536821
theorem B1024577 : Blo 682313 1024577 := bstep (se 2 (by rfl) ⟨384216, by rfl⟩ : syracuseStep 1024577 = 768433) B768433
theorem B1024595 : Blo 682313 1024595 := bstep (se 1 (by rfl) ⟨768446, by rfl⟩ : syracuseStep 1024595 = 1536893) B1536893
theorem B1155667 : Blo 682313 1155667 := bstep (se 1 (by rfl) ⟨866750, by rfl⟩ : syracuseStep 1155667 = 1733501) B1733501
theorem B1024625 : Blo 682313 1024625 := bstep (se 2 (by rfl) ⟨384234, by rfl⟩ : syracuseStep 1024625 = 768469) B768469
theorem B1024643 : Blo 682313 1024643 := bstep (se 1 (by rfl) ⟨768482, by rfl⟩ : syracuseStep 1024643 = 1536965) B1536965
theorem B4694669 : Blo 682313 4694669 := bstep (se 3 (by rfl) ⟨880250, by rfl⟩ : syracuseStep 4694669 = 1760501) B1760501
theorem B1024673 : Blo 682313 1024673 := bstep (se 2 (by rfl) ⟨384252, by rfl⟩ : syracuseStep 1024673 = 768505) B768505
theorem B1188515 : Blo 682313 1188515 := bstep (se 1 (by rfl) ⟨891386, by rfl⟩ : syracuseStep 1188515 = 1782773) B1782773
theorem B1024691 : Blo 682313 1024691 := bstep (se 1 (by rfl) ⟨768518, by rfl⟩ : syracuseStep 1024691 = 1537037) B1537037
theorem B1647299 : Blo 682313 1647299 := bstep (se 1 (by rfl) ⟨1235474, by rfl⟩ : syracuseStep 1647299 = 2470949) B2470949
theorem B1024721 : Blo 682313 1024721 := bstep (se 2 (by rfl) ⟨384270, by rfl⟩ : syracuseStep 1024721 = 768541) B768541
theorem B1155809 : Blo 682313 1155809 := bstep (se 2 (by rfl) ⟨433428, by rfl⟩ : syracuseStep 1155809 = 866857) B866857
theorem B1024739 : Blo 682313 1024739 := bstep (se 1 (by rfl) ⟨768554, by rfl⟩ : syracuseStep 1024739 = 1537109) B1537109
theorem B1024769 : Blo 682313 1024769 := bstep (se 2 (by rfl) ⟨384288, by rfl⟩ : syracuseStep 1024769 = 768577) B768577
theorem B1024787 : Blo 682313 1024787 := bstep (se 1 (by rfl) ⟨768590, by rfl⟩ : syracuseStep 1024787 = 1537181) B1537181
theorem B1024817 : Blo 682313 1024817 := bstep (se 2 (by rfl) ⟨384306, by rfl⟩ : syracuseStep 1024817 = 768613) B768613
theorem B1024835 : Blo 682313 1024835 := bstep (se 1 (by rfl) ⟨768626, by rfl⟩ : syracuseStep 1024835 = 1537253) B1537253
theorem B1024865 : Blo 682313 1024865 := bstep (se 2 (by rfl) ⟨384324, by rfl⟩ : syracuseStep 1024865 = 768649) B768649
theorem B1155937 : Blo 682313 1155937 := bstep (se 2 (by rfl) ⟨433476, by rfl⟩ : syracuseStep 1155937 = 866953) B866953
theorem B8758115 : Blo 682313 8758115 := bstep (se 1 (by rfl) ⟨6568586, by rfl⟩ : syracuseStep 8758115 = 13137173) B13137173
theorem B2302829 : Blo 682313 2302829 := bstep (se 3 (by rfl) ⟨431780, by rfl⟩ : syracuseStep 2302829 = 863561) B863561
theorem B1024883 : Blo 682313 1024883 := bstep (se 1 (by rfl) ⟨768662, by rfl⟩ : syracuseStep 1024883 = 1537325) B1537325
theorem B1155971 : Blo 682313 1155971 := bstep (se 1 (by rfl) ⟨866978, by rfl⟩ : syracuseStep 1155971 = 1733957) B1733957
theorem B1024913 : Blo 682313 1024913 := bstep (se 2 (by rfl) ⟨384342, by rfl⟩ : syracuseStep 1024913 = 768685) B768685
theorem B2302883 : Blo 682313 2302883 := bstep (se 1 (by rfl) ⟨1727162, by rfl⟩ : syracuseStep 2302883 = 3454325) B3454325
theorem B1024931 : Blo 682313 1024931 := bstep (se 1 (by rfl) ⟨768698, by rfl⟩ : syracuseStep 1024931 = 1537397) B1537397
theorem B1024961 : Blo 682313 1024961 := bstep (se 2 (by rfl) ⟨384360, by rfl⟩ : syracuseStep 1024961 = 768721) B768721
theorem B1024979 : Blo 682313 1024979 := bstep (se 1 (by rfl) ⟨768734, by rfl⟩ : syracuseStep 1024979 = 1537469) B1537469
theorem B1025009 : Blo 682313 1025009 := bstep (se 2 (by rfl) ⟨384378, by rfl⟩ : syracuseStep 1025009 = 768757) B768757
theorem B1025027 : Blo 682313 1025027 := bstep (se 1 (by rfl) ⟨768770, by rfl⟩ : syracuseStep 1025027 = 1537541) B1537541
theorem B1156099 : Blo 682313 1156099 := bstep (se 1 (by rfl) ⟨867074, by rfl⟩ : syracuseStep 1156099 = 1734149) B1734149
theorem B1025057 : Blo 682313 1025057 := bstep (se 2 (by rfl) ⟨384396, by rfl⟩ : syracuseStep 1025057 = 768793) B768793
theorem B1025075 : Blo 682313 1025075 := bstep (se 1 (by rfl) ⟨768806, by rfl⟩ : syracuseStep 1025075 = 1537613) B1537613
theorem B1647683 : Blo 682313 1647683 := bstep (se 1 (by rfl) ⟨1235762, by rfl⟩ : syracuseStep 1647683 = 2471525) B2471525
theorem B3941453 : Blo 682313 3941453 := bstep (se 3 (by rfl) ⟨739022, by rfl⟩ : syracuseStep 3941453 = 1478045) B1478045
theorem B1025105 : Blo 682313 1025105 := bstep (se 2 (by rfl) ⟨384414, by rfl⟩ : syracuseStep 1025105 = 768829) B768829
theorem B1025123 : Blo 682313 1025123 := bstep (se 1 (by rfl) ⟨768842, by rfl⟩ : syracuseStep 1025123 = 1537685) B1537685
theorem B1025153 : Blo 682313 1025153 := bstep (se 2 (by rfl) ⟨384432, by rfl⟩ : syracuseStep 1025153 = 768865) B768865
theorem B5547149 : Blo 682313 5547149 := bstep (se 3 (by rfl) ⟨1040090, by rfl⟩ : syracuseStep 5547149 = 2080181) B2080181
theorem B1156241 : Blo 682313 1156241 := bstep (se 2 (by rfl) ⟨433590, by rfl⟩ : syracuseStep 1156241 = 867181) B867181
theorem B1025171 : Blo 682313 1025171 := bstep (se 1 (by rfl) ⟨768878, by rfl⟩ : syracuseStep 1025171 = 1537757) B1537757
theorem B2303153 : Blo 682313 2303153 := bstep (se 2 (by rfl) ⟨863682, by rfl⟩ : syracuseStep 2303153 = 1727365) B1727365
theorem B1025201 : Blo 682313 1025201 := bstep (se 2 (by rfl) ⟨384450, by rfl⟩ : syracuseStep 1025201 = 768901) B768901
theorem B2598065 : Blo 682313 2598065 := bstep (se 2 (by rfl) ⟨974274, by rfl⟩ : syracuseStep 2598065 = 1948549) B1948549
theorem B1025219 : Blo 682313 1025219 := bstep (se 1 (by rfl) ⟨768914, by rfl⟩ : syracuseStep 1025219 = 1537829) B1537829
theorem B2335949 : Blo 682313 2335949 := bstep (se 3 (by rfl) ⟨437990, by rfl⟩ : syracuseStep 2335949 = 875981) B875981
theorem B1025249 : Blo 682313 1025249 := bstep (se 2 (by rfl) ⟨384468, by rfl⟩ : syracuseStep 1025249 = 768937) B768937
theorem B2467057 : Blo 682313 2467057 := bstep (se 2 (by rfl) ⟨925146, by rfl⟩ : syracuseStep 2467057 = 1850293) B1850293
theorem B1025267 : Blo 682313 1025267 := bstep (se 1 (by rfl) ⟨768950, by rfl⟩ : syracuseStep 1025267 = 1537901) B1537901
theorem B1025297 : Blo 682313 1025297 := bstep (se 2 (by rfl) ⟨384486, by rfl⟩ : syracuseStep 1025297 = 768973) B768973
theorem B1156369 : Blo 682313 1156369 := bstep (se 2 (by rfl) ⟨433638, by rfl⟩ : syracuseStep 1156369 = 867277) B867277
theorem B1025315 : Blo 682313 1025315 := bstep (se 1 (by rfl) ⟨768986, by rfl⟩ : syracuseStep 1025315 = 1537973) B1537973
theorem B1156403 : Blo 682313 1156403 := bstep (se 1 (by rfl) ⟨867302, by rfl⟩ : syracuseStep 1156403 = 1734605) B1734605
theorem B1025345 : Blo 682313 1025345 := bstep (se 2 (by rfl) ⟨384504, by rfl⟩ : syracuseStep 1025345 = 769009) B769009
theorem B1025363 : Blo 682313 1025363 := bstep (se 1 (by rfl) ⟨769022, by rfl⟩ : syracuseStep 1025363 = 1538045) B1538045
theorem B1025393 : Blo 682313 1025393 := bstep (se 2 (by rfl) ⟨384522, by rfl⟩ : syracuseStep 1025393 = 769045) B769045
theorem B1025411 : Blo 682313 1025411 := bstep (se 1 (by rfl) ⟨769058, by rfl⟩ : syracuseStep 1025411 = 1538117) B1538117
theorem B1025441 : Blo 682313 1025441 := bstep (se 2 (by rfl) ⟨384540, by rfl⟩ : syracuseStep 1025441 = 769081) B769081
theorem B1025459 : Blo 682313 1025459 := bstep (se 1 (by rfl) ⟨769094, by rfl⟩ : syracuseStep 1025459 = 1538189) B1538189
theorem B1156531 : Blo 682313 1156531 := bstep (se 1 (by rfl) ⟨867398, by rfl⟩ : syracuseStep 1156531 = 1734797) B1734797
theorem B1025489 : Blo 682313 1025489 := bstep (se 2 (by rfl) ⟨384558, by rfl⟩ : syracuseStep 1025489 = 769117) B769117
theorem B1025507 : Blo 682313 1025507 := bstep (se 1 (by rfl) ⟨769130, by rfl⟩ : syracuseStep 1025507 = 1538261) B1538261
theorem B1025537 : Blo 682313 1025537 := bstep (se 2 (by rfl) ⟨384576, by rfl⟩ : syracuseStep 1025537 = 769153) B769153
theorem B1025555 : Blo 682313 1025555 := bstep (se 1 (by rfl) ⟨769166, by rfl⟩ : syracuseStep 1025555 = 1538333) B1538333
theorem B1975853 : Blo 682313 1975853 := bstep (se 3 (by rfl) ⟨370472, by rfl⟩ : syracuseStep 1975853 = 740945) B740945
theorem B1025585 : Blo 682313 1025585 := bstep (se 2 (by rfl) ⟨384594, by rfl⟩ : syracuseStep 1025585 = 769189) B769189
theorem B1156673 : Blo 682313 1156673 := bstep (se 2 (by rfl) ⟨433752, by rfl⟩ : syracuseStep 1156673 = 867505) B867505
theorem B1025603 : Blo 682313 1025603 := bstep (se 1 (by rfl) ⟨769202, by rfl⟩ : syracuseStep 1025603 = 1538405) B1538405
theorem B1025633 : Blo 682313 1025633 := bstep (se 2 (by rfl) ⟨384612, by rfl⟩ : syracuseStep 1025633 = 769225) B769225
theorem B1025651 : Blo 682313 1025651 := bstep (se 1 (by rfl) ⟨769238, by rfl⟩ : syracuseStep 1025651 = 1538477) B1538477
theorem B1025681 : Blo 682313 1025681 := bstep (se 2 (by rfl) ⟨384630, by rfl⟩ : syracuseStep 1025681 = 769261) B769261
theorem B1025699 : Blo 682313 1025699 := bstep (se 1 (by rfl) ⟨769274, by rfl⟩ : syracuseStep 1025699 = 1538549) B1538549
theorem B1025729 : Blo 682313 1025729 := bstep (se 2 (by rfl) ⟨384648, by rfl⟩ : syracuseStep 1025729 = 769297) B769297
theorem B1156801 : Blo 682313 1156801 := bstep (se 2 (by rfl) ⟨433800, by rfl⟩ : syracuseStep 1156801 = 867601) B867601
theorem B2303693 : Blo 682313 2303693 := bstep (se 3 (by rfl) ⟨431942, by rfl⟩ : syracuseStep 2303693 = 863885) B863885
theorem B1025747 : Blo 682313 1025747 := bstep (se 1 (by rfl) ⟨769310, by rfl⟩ : syracuseStep 1025747 = 1538621) B1538621
theorem B1156835 : Blo 682313 1156835 := bstep (se 1 (by rfl) ⟨867626, by rfl⟩ : syracuseStep 1156835 = 1735253) B1735253
theorem B1025777 : Blo 682313 1025777 := bstep (se 2 (by rfl) ⟨384666, by rfl⟩ : syracuseStep 1025777 = 769333) B769333
theorem B2303747 : Blo 682313 2303747 := bstep (se 1 (by rfl) ⟨1727810, by rfl⟩ : syracuseStep 2303747 = 3455621) B3455621
theorem B1025795 : Blo 682313 1025795 := bstep (se 1 (by rfl) ⟨769346, by rfl⟩ : syracuseStep 1025795 = 1538693) B1538693
theorem B1025825 : Blo 682313 1025825 := bstep (se 2 (by rfl) ⟨384684, by rfl⟩ : syracuseStep 1025825 = 769369) B769369
theorem B1025843 : Blo 682313 1025843 := bstep (se 1 (by rfl) ⟨769382, by rfl⟩ : syracuseStep 1025843 = 1538765) B1538765
theorem B1025873 : Blo 682313 1025873 := bstep (se 2 (by rfl) ⟨384702, by rfl⟩ : syracuseStep 1025873 = 769405) B769405
theorem B1025891 : Blo 682313 1025891 := bstep (se 1 (by rfl) ⟨769418, by rfl⟩ : syracuseStep 1025891 = 1538837) B1538837
theorem B1156963 : Blo 682313 1156963 := bstep (se 1 (by rfl) ⟨867722, by rfl⟩ : syracuseStep 1156963 = 1735445) B1735445
theorem B1025921 : Blo 682313 1025921 := bstep (se 2 (by rfl) ⟨384720, by rfl⟩ : syracuseStep 1025921 = 769441) B769441
theorem B1648529 : Blo 682313 1648529 := bstep (se 2 (by rfl) ⟨618198, by rfl⟩ : syracuseStep 1648529 = 1236397) B1236397
theorem B1025939 : Blo 682313 1025939 := bstep (se 1 (by rfl) ⟨769454, by rfl⟩ : syracuseStep 1025939 = 1538909) B1538909
theorem B1025969 : Blo 682313 1025969 := bstep (se 2 (by rfl) ⟨384738, by rfl⟩ : syracuseStep 1025969 = 769477) B769477
theorem B1025987 : Blo 682313 1025987 := bstep (se 1 (by rfl) ⟨769490, by rfl⟩ : syracuseStep 1025987 = 1538981) B1538981
theorem B1026017 : Blo 682313 1026017 := bstep (se 2 (by rfl) ⟨384756, by rfl⟩ : syracuseStep 1026017 = 769513) B769513
theorem B1157105 : Blo 682313 1157105 := bstep (se 2 (by rfl) ⟨433914, by rfl⟩ : syracuseStep 1157105 = 867829) B867829
theorem B1026035 : Blo 682313 1026035 := bstep (se 1 (by rfl) ⟨769526, by rfl⟩ : syracuseStep 1026035 = 1539053) B1539053
theorem B2304017 : Blo 682313 2304017 := bstep (se 2 (by rfl) ⟨864006, by rfl⟩ : syracuseStep 2304017 = 1728013) B1728013
theorem B1026065 : Blo 682313 1026065 := bstep (se 2 (by rfl) ⟨384774, by rfl⟩ : syracuseStep 1026065 = 769549) B769549
theorem B1026083 : Blo 682313 1026083 := bstep (se 1 (by rfl) ⟨769562, by rfl⟩ : syracuseStep 1026083 = 1539125) B1539125
theorem B1026113 : Blo 682313 1026113 := bstep (se 2 (by rfl) ⟨384792, by rfl⟩ : syracuseStep 1026113 = 769585) B769585
theorem B1648721 : Blo 682313 1648721 := bstep (se 2 (by rfl) ⟨618270, by rfl⟩ : syracuseStep 1648721 = 1236541) B1236541
theorem B1026131 : Blo 682313 1026131 := bstep (se 1 (by rfl) ⟨769598, by rfl⟩ : syracuseStep 1026131 = 1539197) B1539197
theorem B1943651 : Blo 682313 1943651 := bstep (se 1 (by rfl) ⟨1457738, by rfl⟩ : syracuseStep 1943651 = 2915477) B2915477
theorem B1026161 : Blo 682313 1026161 := bstep (se 2 (by rfl) ⟨384810, by rfl⟩ : syracuseStep 1026161 = 769621) B769621
theorem B1157233 : Blo 682313 1157233 := bstep (se 2 (by rfl) ⟨433962, by rfl⟩ : syracuseStep 1157233 = 867925) B867925
theorem B1026179 : Blo 682313 1026179 := bstep (se 1 (by rfl) ⟨769634, by rfl⟩ : syracuseStep 1026179 = 1539269) B1539269
theorem B1157267 : Blo 682313 1157267 := bstep (se 1 (by rfl) ⟨867950, by rfl⟩ : syracuseStep 1157267 = 1735901) B1735901
theorem B1026209 : Blo 682313 1026209 := bstep (se 2 (by rfl) ⟨384828, by rfl⟩ : syracuseStep 1026209 = 769657) B769657
theorem B1026227 : Blo 682313 1026227 := bstep (se 1 (by rfl) ⟨769670, by rfl⟩ : syracuseStep 1026227 = 1539341) B1539341
theorem B1026257 : Blo 682313 1026257 := bstep (se 2 (by rfl) ⟨384846, by rfl⟩ : syracuseStep 1026257 = 769693) B769693
theorem B1026275 : Blo 682313 1026275 := bstep (se 1 (by rfl) ⟨769706, by rfl⟩ : syracuseStep 1026275 = 1539413) B1539413
theorem B1026305 : Blo 682313 1026305 := bstep (se 2 (by rfl) ⟨384864, by rfl⟩ : syracuseStep 1026305 = 769729) B769729
theorem B2337041 : Blo 682313 2337041 := bstep (se 2 (by rfl) ⟨876390, by rfl⟩ : syracuseStep 2337041 = 1752781) B1752781
theorem B1026323 : Blo 682313 1026323 := bstep (se 1 (by rfl) ⟨769742, by rfl⟩ : syracuseStep 1026323 = 1539485) B1539485
theorem B1157395 : Blo 682313 1157395 := bstep (se 1 (by rfl) ⟨868046, by rfl⟩ : syracuseStep 1157395 = 1736093) B1736093
theorem B1026353 : Blo 682313 1026353 := bstep (se 2 (by rfl) ⟨384882, by rfl⟩ : syracuseStep 1026353 = 769765) B769765
theorem B1026371 : Blo 682313 1026371 := bstep (se 1 (by rfl) ⟨769778, by rfl⟩ : syracuseStep 1026371 = 1539557) B1539557
theorem B2926925 : Blo 682313 2926925 := bstep (se 3 (by rfl) ⟨548798, by rfl⟩ : syracuseStep 2926925 = 1097597) B1097597
theorem B1026401 : Blo 682313 1026401 := bstep (se 2 (by rfl) ⟨384900, by rfl⟩ : syracuseStep 1026401 = 769801) B769801
theorem B1026419 : Blo 682313 1026419 := bstep (se 1 (by rfl) ⟨769814, by rfl⟩ : syracuseStep 1026419 = 1539629) B1539629
theorem B1026449 : Blo 682313 1026449 := bstep (se 2 (by rfl) ⟨384918, by rfl⟩ : syracuseStep 1026449 = 769837) B769837
theorem B1157537 : Blo 682313 1157537 := bstep (se 2 (by rfl) ⟨434076, by rfl⟩ : syracuseStep 1157537 = 868153) B868153
theorem B1026467 : Blo 682313 1026467 := bstep (se 1 (by rfl) ⟨769850, by rfl⟩ : syracuseStep 1026467 = 1539701) B1539701
theorem B1026497 : Blo 682313 1026497 := bstep (se 2 (by rfl) ⟨384936, by rfl⟩ : syracuseStep 1026497 = 769873) B769873
theorem B1026515 : Blo 682313 1026515 := bstep (se 1 (by rfl) ⟨769886, by rfl⟩ : syracuseStep 1026515 = 1539773) B1539773
theorem B731603 : Blo 682313 731603 := bstep (se 1 (by rfl) ⟨548702, by rfl⟩ : syracuseStep 731603 = 1097405) B1097405
theorem B1026545 : Blo 682313 1026545 := bstep (se 2 (by rfl) ⟨384954, by rfl⟩ : syracuseStep 1026545 = 769909) B769909
theorem B1026563 : Blo 682313 1026563 := bstep (se 1 (by rfl) ⟨769922, by rfl⟩ : syracuseStep 1026563 = 1539845) B1539845
theorem B1026593 : Blo 682313 1026593 := bstep (se 2 (by rfl) ⟨384972, by rfl⟩ : syracuseStep 1026593 = 769945) B769945
theorem B1157665 : Blo 682313 1157665 := bstep (se 2 (by rfl) ⟨434124, by rfl⟩ : syracuseStep 1157665 = 868249) B868249
theorem B2304557 : Blo 682313 2304557 := bstep (se 3 (by rfl) ⟨432104, by rfl⟩ : syracuseStep 2304557 = 864209) B864209
theorem B1026611 : Blo 682313 1026611 := bstep (se 1 (by rfl) ⟨769958, by rfl⟩ : syracuseStep 1026611 = 1539917) B1539917
theorem B1157699 : Blo 682313 1157699 := bstep (se 1 (by rfl) ⟨868274, by rfl⟩ : syracuseStep 1157699 = 1736549) B1736549
theorem B1026641 : Blo 682313 1026641 := bstep (se 2 (by rfl) ⟨384990, by rfl⟩ : syracuseStep 1026641 = 769981) B769981
theorem B2304611 : Blo 682313 2304611 := bstep (se 1 (by rfl) ⟨1728458, by rfl⟩ : syracuseStep 2304611 = 3456917) B3456917
theorem B1026659 : Blo 682313 1026659 := bstep (se 1 (by rfl) ⟨769994, by rfl⟩ : syracuseStep 1026659 = 1539989) B1539989
theorem B2599523 : Blo 682313 2599523 := bstep (se 1 (by rfl) ⟨1949642, by rfl⟩ : syracuseStep 2599523 = 3899285) B3899285
theorem B1026689 : Blo 682313 1026689 := bstep (se 2 (by rfl) ⟨385008, by rfl⟩ : syracuseStep 1026689 = 770017) B770017
theorem B1026707 : Blo 682313 1026707 := bstep (se 1 (by rfl) ⟨770030, by rfl⟩ : syracuseStep 1026707 = 1540061) B1540061
theorem B1026737 : Blo 682313 1026737 := bstep (se 2 (by rfl) ⟨385026, by rfl⟩ : syracuseStep 1026737 = 770053) B770053
theorem B1026755 : Blo 682313 1026755 := bstep (se 1 (by rfl) ⟨770066, by rfl⟩ : syracuseStep 1026755 = 1540133) B1540133
theorem B1157827 : Blo 682313 1157827 := bstep (se 1 (by rfl) ⟨868370, by rfl⟩ : syracuseStep 1157827 = 1736741) B1736741
theorem B1026785 : Blo 682313 1026785 := bstep (se 2 (by rfl) ⟨385044, by rfl⟩ : syracuseStep 1026785 = 770089) B770089
theorem B1026803 : Blo 682313 1026803 := bstep (se 1 (by rfl) ⟨770102, by rfl⟩ : syracuseStep 1026803 = 1540205) B1540205
theorem B1026833 : Blo 682313 1026833 := bstep (se 2 (by rfl) ⟨385062, by rfl⟩ : syracuseStep 1026833 = 770125) B770125
theorem B1026851 : Blo 682313 1026851 := bstep (se 1 (by rfl) ⟨770138, by rfl⟩ : syracuseStep 1026851 = 1540277) B1540277
theorem B1026881 : Blo 682313 1026881 := bstep (se 2 (by rfl) ⟨385080, by rfl⟩ : syracuseStep 1026881 = 770161) B770161
theorem B1157969 : Blo 682313 1157969 := bstep (se 2 (by rfl) ⟨434238, by rfl⟩ : syracuseStep 1157969 = 868477) B868477
theorem B1026899 : Blo 682313 1026899 := bstep (se 1 (by rfl) ⟨770174, by rfl⟩ : syracuseStep 1026899 = 1540349) B1540349
theorem B2304881 : Blo 682313 2304881 := bstep (se 2 (by rfl) ⟨864330, by rfl⟩ : syracuseStep 2304881 = 1728661) B1728661
theorem B1026929 : Blo 682313 1026929 := bstep (se 2 (by rfl) ⟨385098, by rfl⟩ : syracuseStep 1026929 = 770197) B770197
theorem B1026947 : Blo 682313 1026947 := bstep (se 1 (by rfl) ⟨770210, by rfl⟩ : syracuseStep 1026947 = 1540421) B1540421
theorem B1026977 : Blo 682313 1026977 := bstep (se 2 (by rfl) ⟨385116, by rfl⟩ : syracuseStep 1026977 = 770233) B770233
theorem B1026995 : Blo 682313 1026995 := bstep (se 1 (by rfl) ⟨770246, by rfl⟩ : syracuseStep 1026995 = 1540493) B1540493
theorem B1027025 : Blo 682313 1027025 := bstep (se 2 (by rfl) ⟨385134, by rfl⟩ : syracuseStep 1027025 = 770269) B770269
theorem B1158097 : Blo 682313 1158097 := bstep (se 2 (by rfl) ⟨434286, by rfl⟩ : syracuseStep 1158097 = 868573) B868573
theorem B1027043 : Blo 682313 1027043 := bstep (se 1 (by rfl) ⟨770282, by rfl⟩ : syracuseStep 1027043 = 1540565) B1540565
theorem B1158131 : Blo 682313 1158131 := bstep (se 1 (by rfl) ⟨868598, by rfl⟩ : syracuseStep 1158131 = 1737197) B1737197
theorem B1027073 : Blo 682313 1027073 := bstep (se 2 (by rfl) ⟨385152, by rfl⟩ : syracuseStep 1027073 = 770305) B770305
theorem B1027091 : Blo 682313 1027091 := bstep (se 1 (by rfl) ⟨770318, by rfl⟩ : syracuseStep 1027091 = 1540637) B1540637
theorem B1027121 : Blo 682313 1027121 := bstep (se 2 (by rfl) ⟨385170, by rfl⟩ : syracuseStep 1027121 = 770341) B770341
theorem B1027139 : Blo 682313 1027139 := bstep (se 1 (by rfl) ⟨770354, by rfl⟩ : syracuseStep 1027139 = 1540709) B1540709
theorem B1027169 : Blo 682313 1027169 := bstep (se 2 (by rfl) ⟨385188, by rfl⟩ : syracuseStep 1027169 = 770377) B770377
theorem B1027187 : Blo 682313 1027187 := bstep (se 1 (by rfl) ⟨770390, by rfl⟩ : syracuseStep 1027187 = 1540781) B1540781
theorem B1027217 : Blo 682313 1027217 := bstep (se 2 (by rfl) ⟨385206, by rfl⟩ : syracuseStep 1027217 = 770413) B770413
theorem B1027235 : Blo 682313 1027235 := bstep (se 1 (by rfl) ⟨770426, by rfl⟩ : syracuseStep 1027235 = 1540853) B1540853
theorem B1027265 : Blo 682313 1027265 := bstep (se 2 (by rfl) ⟨385224, by rfl⟩ : syracuseStep 1027265 = 770449) B770449
theorem B1027283 : Blo 682313 1027283 := bstep (se 1 (by rfl) ⟨770462, by rfl⟩ : syracuseStep 1027283 = 1540925) B1540925
theorem B1027313 : Blo 682313 1027313 := bstep (se 2 (by rfl) ⟨385242, by rfl⟩ : syracuseStep 1027313 = 770485) B770485
theorem B5942513 : Blo 682313 5942513 := bstep (se 2 (by rfl) ⟨2228442, by rfl⟩ : syracuseStep 5942513 = 4456885) B4456885
theorem B1027331 : Blo 682313 1027331 := bstep (se 1 (by rfl) ⟨770498, by rfl⟩ : syracuseStep 1027331 = 1540997) B1540997
theorem B1027361 : Blo 682313 1027361 := bstep (se 2 (by rfl) ⟨385260, by rfl⟩ : syracuseStep 1027361 = 770521) B770521
theorem B1944881 : Blo 682313 1944881 := bstep (se 2 (by rfl) ⟨729330, by rfl⟩ : syracuseStep 1944881 = 1458661) B1458661
theorem B1027379 : Blo 682313 1027379 := bstep (se 1 (by rfl) ⟨770534, by rfl⟩ : syracuseStep 1027379 = 1541069) B1541069
theorem B1027409 : Blo 682313 1027409 := bstep (se 2 (by rfl) ⟨385278, by rfl⟩ : syracuseStep 1027409 = 770557) B770557
theorem B1027427 : Blo 682313 1027427 := bstep (se 1 (by rfl) ⟨770570, by rfl⟩ : syracuseStep 1027427 = 1541141) B1541141
theorem B1027457 : Blo 682313 1027457 := bstep (se 2 (by rfl) ⟨385296, by rfl⟩ : syracuseStep 1027457 = 770593) B770593
theorem B2305421 : Blo 682313 2305421 := bstep (se 3 (by rfl) ⟨432266, by rfl⟩ : syracuseStep 2305421 = 864533) B864533
theorem B1027475 : Blo 682313 1027475 := bstep (se 1 (by rfl) ⟨770606, by rfl⟩ : syracuseStep 1027475 = 1541213) B1541213
theorem B1027505 : Blo 682313 1027505 := bstep (se 2 (by rfl) ⟨385314, by rfl⟩ : syracuseStep 1027505 = 770629) B770629
theorem B2305475 : Blo 682313 2305475 := bstep (se 1 (by rfl) ⟨1729106, by rfl⟩ : syracuseStep 2305475 = 3458213) B3458213
theorem B1027523 : Blo 682313 1027523 := bstep (se 1 (by rfl) ⟨770642, by rfl⟩ : syracuseStep 1027523 = 1541285) B1541285
theorem B732611 : Blo 682313 732611 := bstep (se 1 (by rfl) ⟨549458, by rfl⟩ : syracuseStep 732611 = 1098917) B1098917
theorem B1093073 : Blo 682313 1093073 := bstep (se 2 (by rfl) ⟨409902, by rfl⟩ : syracuseStep 1093073 = 819805) B819805
theorem B1027553 : Blo 682313 1027553 := bstep (se 2 (by rfl) ⟨385332, by rfl⟩ : syracuseStep 1027553 = 770665) B770665
theorem B1027571 : Blo 682313 1027571 := bstep (se 1 (by rfl) ⟨770678, by rfl⟩ : syracuseStep 1027571 = 1541357) B1541357
theorem B1027601 : Blo 682313 1027601 := bstep (se 2 (by rfl) ⟨385350, by rfl⟩ : syracuseStep 1027601 = 770701) B770701
theorem B863779 : Blo 682313 863779 := bstep (se 1 (by rfl) ⟨647834, by rfl⟩ : syracuseStep 863779 = 1295669) B1295669
theorem B1027619 : Blo 682313 1027619 := bstep (se 1 (by rfl) ⟨770714, by rfl⟩ : syracuseStep 1027619 = 1541429) B1541429
theorem B1027649 : Blo 682313 1027649 := bstep (se 2 (by rfl) ⟨385368, by rfl⟩ : syracuseStep 1027649 = 770737) B770737
theorem B2600525 : Blo 682313 2600525 := bstep (se 3 (by rfl) ⟨487598, by rfl⟩ : syracuseStep 2600525 = 975197) B975197
theorem B1027667 : Blo 682313 1027667 := bstep (se 1 (by rfl) ⟨770750, by rfl⟩ : syracuseStep 1027667 = 1541501) B1541501
theorem B1027697 : Blo 682313 1027697 := bstep (se 2 (by rfl) ⟨385386, by rfl⟩ : syracuseStep 1027697 = 770773) B770773
theorem B863875 : Blo 682313 863875 := bstep (se 1 (by rfl) ⟨647906, by rfl⟩ : syracuseStep 863875 = 1295813) B1295813
theorem B1027715 : Blo 682313 1027715 := bstep (se 1 (by rfl) ⟨770786, by rfl⟩ : syracuseStep 1027715 = 1541573) B1541573
theorem B1027745 : Blo 682313 1027745 := bstep (se 2 (by rfl) ⟨385404, by rfl⟩ : syracuseStep 1027745 = 770809) B770809
theorem B1027763 : Blo 682313 1027763 := bstep (se 1 (by rfl) ⟨770822, by rfl⟩ : syracuseStep 1027763 = 1541645) B1541645
theorem B2305745 : Blo 682313 2305745 := bstep (se 2 (by rfl) ⟨864654, by rfl⟩ : syracuseStep 2305745 = 1729309) B1729309
theorem B1027793 : Blo 682313 1027793 := bstep (se 2 (by rfl) ⟨385422, by rfl⟩ : syracuseStep 1027793 = 770845) B770845
theorem B1027811 : Blo 682313 1027811 := bstep (se 1 (by rfl) ⟨770858, by rfl⟩ : syracuseStep 1027811 = 1541717) B1541717
theorem B1027841 : Blo 682313 1027841 := bstep (se 2 (by rfl) ⟨385440, by rfl⟩ : syracuseStep 1027841 = 770881) B770881
theorem B1027859 : Blo 682313 1027859 := bstep (se 1 (by rfl) ⟨770894, by rfl⟩ : syracuseStep 1027859 = 1541789) B1541789
theorem B1027889 : Blo 682313 1027889 := bstep (se 2 (by rfl) ⟨385458, by rfl⟩ : syracuseStep 1027889 = 770917) B770917
theorem B1027907 : Blo 682313 1027907 := bstep (se 1 (by rfl) ⟨770930, by rfl⟩ : syracuseStep 1027907 = 1541861) B1541861
theorem B1027937 : Blo 682313 1027937 := bstep (se 2 (by rfl) ⟨385476, by rfl⟩ : syracuseStep 1027937 = 770953) B770953
theorem B1027955 : Blo 682313 1027955 := bstep (se 1 (by rfl) ⟨770966, by rfl⟩ : syracuseStep 1027955 = 1541933) B1541933
theorem B1027985 : Blo 682313 1027985 := bstep (se 2 (by rfl) ⟨385494, by rfl⟩ : syracuseStep 1027985 = 770989) B770989
theorem B1028003 : Blo 682313 1028003 := bstep (se 1 (by rfl) ⟨771002, by rfl⟩ : syracuseStep 1028003 = 1542005) B1542005
theorem B1028033 : Blo 682313 1028033 := bstep (se 2 (by rfl) ⟨385512, by rfl⟩ : syracuseStep 1028033 = 771025) B771025
theorem B1028051 : Blo 682313 1028051 := bstep (se 1 (by rfl) ⟨771038, by rfl⟩ : syracuseStep 1028051 = 1542077) B1542077
theorem B1028081 : Blo 682313 1028081 := bstep (se 2 (by rfl) ⟨385530, by rfl⟩ : syracuseStep 1028081 = 771061) B771061
theorem B1028099 : Blo 682313 1028099 := bstep (se 1 (by rfl) ⟨771074, by rfl⟩ : syracuseStep 1028099 = 1542149) B1542149
theorem B1028129 : Blo 682313 1028129 := bstep (se 2 (by rfl) ⟨385548, by rfl⟩ : syracuseStep 1028129 = 771097) B771097
theorem B1880099 : Blo 682313 1880099 := bstep (se 1 (by rfl) ⟨1410074, by rfl⟩ : syracuseStep 1880099 = 2820149) B2820149
theorem B1028147 : Blo 682313 1028147 := bstep (se 1 (by rfl) ⟨771110, by rfl⟩ : syracuseStep 1028147 = 1542221) B1542221
theorem B1028177 : Blo 682313 1028177 := bstep (se 2 (by rfl) ⟨385566, by rfl⟩ : syracuseStep 1028177 = 771133) B771133
theorem B1028195 : Blo 682313 1028195 := bstep (se 1 (by rfl) ⟨771146, by rfl⟩ : syracuseStep 1028195 = 1542293) B1542293
theorem B864371 : Blo 682313 864371 := bstep (se 1 (by rfl) ⟨648278, by rfl⟩ : syracuseStep 864371 = 1296557) B1296557
theorem B1028225 : Blo 682313 1028225 := bstep (se 2 (by rfl) ⟨385584, by rfl⟩ : syracuseStep 1028225 = 771169) B771169
theorem B1028243 : Blo 682313 1028243 := bstep (se 1 (by rfl) ⟨771182, by rfl⟩ : syracuseStep 1028243 = 1542365) B1542365
theorem B1028273 : Blo 682313 1028273 := bstep (se 2 (by rfl) ⟨385602, by rfl⟩ : syracuseStep 1028273 = 771205) B771205
theorem B1028291 : Blo 682313 1028291 := bstep (se 1 (by rfl) ⟨771218, by rfl⟩ : syracuseStep 1028291 = 1542437) B1542437
theorem B1028321 : Blo 682313 1028321 := bstep (se 2 (by rfl) ⟨385620, by rfl⟩ : syracuseStep 1028321 = 771241) B771241
theorem B2306285 : Blo 682313 2306285 := bstep (se 3 (by rfl) ⟨432428, by rfl⟩ : syracuseStep 2306285 = 864857) B864857
theorem B1028339 : Blo 682313 1028339 := bstep (se 1 (by rfl) ⟨771254, by rfl⟩ : syracuseStep 1028339 = 1542509) B1542509
theorem B1028369 : Blo 682313 1028369 := bstep (se 2 (by rfl) ⟨385638, by rfl⟩ : syracuseStep 1028369 = 771277) B771277
theorem B1093907 : Blo 682313 1093907 := bstep (se 1 (by rfl) ⟨820430, by rfl⟩ : syracuseStep 1093907 = 1640861) B1640861
theorem B2306339 : Blo 682313 2306339 := bstep (se 1 (by rfl) ⟨1729754, by rfl⟩ : syracuseStep 2306339 = 3459509) B3459509
theorem B1028387 : Blo 682313 1028387 := bstep (se 1 (by rfl) ⟨771290, by rfl⟩ : syracuseStep 1028387 = 1542581) B1542581
theorem B1028417 : Blo 682313 1028417 := bstep (se 2 (by rfl) ⟨385656, by rfl⟩ : syracuseStep 1028417 = 771313) B771313
theorem B1028435 : Blo 682313 1028435 := bstep (se 1 (by rfl) ⟨771326, by rfl⟩ : syracuseStep 1028435 = 1542653) B1542653
theorem B1028465 : Blo 682313 1028465 := bstep (se 2 (by rfl) ⟨385674, by rfl⟩ : syracuseStep 1028465 = 771349) B771349
theorem B1028483 : Blo 682313 1028483 := bstep (se 1 (by rfl) ⟨771362, by rfl⟩ : syracuseStep 1028483 = 1542725) B1542725
theorem B2470285 : Blo 682313 2470285 := bstep (se 3 (by rfl) ⟨463178, by rfl⟩ : syracuseStep 2470285 = 926357) B926357
theorem B1028513 : Blo 682313 1028513 := bstep (se 2 (by rfl) ⟨385692, by rfl⟩ : syracuseStep 1028513 = 771385) B771385
theorem B1028531 : Blo 682313 1028531 := bstep (se 1 (by rfl) ⟨771398, by rfl⟩ : syracuseStep 1028531 = 1542797) B1542797
theorem B1028561 : Blo 682313 1028561 := bstep (se 2 (by rfl) ⟨385710, by rfl⟩ : syracuseStep 1028561 = 771421) B771421
theorem B1028579 : Blo 682313 1028579 := bstep (se 1 (by rfl) ⟨771434, by rfl⟩ : syracuseStep 1028579 = 1542869) B1542869
theorem B1028609 : Blo 682313 1028609 := bstep (se 2 (by rfl) ⟨385728, by rfl⟩ : syracuseStep 1028609 = 771457) B771457
theorem B1028627 : Blo 682313 1028627 := bstep (se 1 (by rfl) ⟨771470, by rfl⟩ : syracuseStep 1028627 = 1542941) B1542941
theorem B3551779 : Blo 682313 3551779 := bstep (se 1 (by rfl) ⟨2663834, by rfl⟩ : syracuseStep 3551779 = 5327669) B5327669
theorem B2306609 : Blo 682313 2306609 := bstep (se 2 (by rfl) ⟨864978, by rfl⟩ : syracuseStep 2306609 = 1729957) B1729957
theorem B1028657 : Blo 682313 1028657 := bstep (se 2 (by rfl) ⟨385746, by rfl⟩ : syracuseStep 1028657 = 771493) B771493
theorem B1094195 : Blo 682313 1094195 := bstep (se 1 (by rfl) ⟨820646, by rfl⟩ : syracuseStep 1094195 = 1641293) B1641293
theorem B1028675 : Blo 682313 1028675 := bstep (se 1 (by rfl) ⟨771506, by rfl⟩ : syracuseStep 1028675 = 1543013) B1543013
theorem B1028705 : Blo 682313 1028705 := bstep (se 2 (by rfl) ⟨385764, by rfl⟩ : syracuseStep 1028705 = 771529) B771529
theorem B3125873 : Blo 682313 3125873 := bstep (se 2 (by rfl) ⟨1172202, by rfl⟩ : syracuseStep 3125873 = 2344405) B2344405
theorem B1028723 : Blo 682313 1028723 := bstep (se 1 (by rfl) ⟨771542, by rfl⟩ : syracuseStep 1028723 = 1543085) B1543085
theorem B1028753 : Blo 682313 1028753 := bstep (se 2 (by rfl) ⟨385782, by rfl⟩ : syracuseStep 1028753 = 771565) B771565
theorem B1028771 : Blo 682313 1028771 := bstep (se 1 (by rfl) ⟨771578, by rfl⟩ : syracuseStep 1028771 = 1543157) B1543157
theorem B1028801 : Blo 682313 1028801 := bstep (se 2 (by rfl) ⟨385800, by rfl⟩ : syracuseStep 1028801 = 771601) B771601
theorem B1028819 : Blo 682313 1028819 := bstep (se 1 (by rfl) ⟨771614, by rfl⟩ : syracuseStep 1028819 = 1543229) B1543229
theorem B1946339 : Blo 682313 1946339 := bstep (se 1 (by rfl) ⟨1459754, by rfl⟩ : syracuseStep 1946339 = 2919509) B2919509
theorem B1028849 : Blo 682313 1028849 := bstep (se 2 (by rfl) ⟨385818, by rfl⟩ : syracuseStep 1028849 = 771637) B771637
theorem B1028867 : Blo 682313 1028867 := bstep (se 1 (by rfl) ⟨771650, by rfl⟩ : syracuseStep 1028867 = 1543301) B1543301
theorem B1094419 : Blo 682313 1094419 := bstep (se 1 (by rfl) ⟨820814, by rfl⟩ : syracuseStep 1094419 = 1641629) B1641629
theorem B44970773 : Blo 682313 44970773 := bstep (se 6 (by rfl) ⟨1054002, by rfl⟩ : syracuseStep 44970773 = 2108005) B2108005
theorem B1028897 : Blo 682313 1028897 := bstep (se 2 (by rfl) ⟨385836, by rfl⟩ : syracuseStep 1028897 = 771673) B771673
theorem B865075 : Blo 682313 865075 := bstep (se 1 (by rfl) ⟨648806, by rfl⟩ : syracuseStep 865075 = 1297613) B1297613
theorem B1028915 : Blo 682313 1028915 := bstep (se 1 (by rfl) ⟨771686, by rfl⟩ : syracuseStep 1028915 = 1543373) B1543373
theorem B1028945 : Blo 682313 1028945 := bstep (se 2 (by rfl) ⟨385854, by rfl⟩ : syracuseStep 1028945 = 771709) B771709
theorem B1028963 : Blo 682313 1028963 := bstep (se 1 (by rfl) ⟨771722, by rfl⟩ : syracuseStep 1028963 = 1543445) B1543445
theorem B1028993 : Blo 682313 1028993 := bstep (se 2 (by rfl) ⟨385872, by rfl⟩ : syracuseStep 1028993 = 771745) B771745
theorem B865171 : Blo 682313 865171 := bstep (se 1 (by rfl) ⟨648878, by rfl⟩ : syracuseStep 865171 = 1297757) B1297757
theorem B1029011 : Blo 682313 1029011 := bstep (se 1 (by rfl) ⟨771758, by rfl⟩ : syracuseStep 1029011 = 1543517) B1543517
theorem B1029041 : Blo 682313 1029041 := bstep (se 2 (by rfl) ⟨385890, by rfl⟩ : syracuseStep 1029041 = 771781) B771781
theorem B2339779 : Blo 682313 2339779 := bstep (se 1 (by rfl) ⟨1754834, by rfl⟩ : syracuseStep 2339779 = 3509669) B3509669
theorem B1029059 : Blo 682313 1029059 := bstep (se 1 (by rfl) ⟨771794, by rfl⟩ : syracuseStep 1029059 = 1543589) B1543589
theorem B1029089 : Blo 682313 1029089 := bstep (se 2 (by rfl) ⟨385908, by rfl⟩ : syracuseStep 1029089 = 771817) B771817
theorem B1029107 : Blo 682313 1029107 := bstep (se 1 (by rfl) ⟨771830, by rfl⟩ : syracuseStep 1029107 = 1543661) B1543661
theorem B1029137 : Blo 682313 1029137 := bstep (se 2 (by rfl) ⟨385926, by rfl⟩ : syracuseStep 1029137 = 771853) B771853
theorem B1029155 : Blo 682313 1029155 := bstep (se 1 (by rfl) ⟨771866, by rfl⟩ : syracuseStep 1029155 = 1543733) B1543733
theorem B1029185 : Blo 682313 1029185 := bstep (se 2 (by rfl) ⟨385944, by rfl⟩ : syracuseStep 1029185 = 771889) B771889
theorem B2307149 : Blo 682313 2307149 := bstep (se 3 (by rfl) ⟨432590, by rfl⟩ : syracuseStep 2307149 = 865181) B865181
theorem B1029203 : Blo 682313 1029203 := bstep (se 1 (by rfl) ⟨771902, by rfl⟩ : syracuseStep 1029203 = 1543805) B1543805
theorem B1029233 : Blo 682313 1029233 := bstep (se 2 (by rfl) ⟨385962, by rfl⟩ : syracuseStep 1029233 = 771925) B771925
theorem B2307203 : Blo 682313 2307203 := bstep (se 1 (by rfl) ⟨1730402, by rfl⟩ : syracuseStep 2307203 = 3460805) B3460805
theorem B1029251 : Blo 682313 1029251 := bstep (se 1 (by rfl) ⟨771938, by rfl⟩ : syracuseStep 1029251 = 1543877) B1543877
theorem B1029281 : Blo 682313 1029281 := bstep (se 2 (by rfl) ⟨385980, by rfl⟩ : syracuseStep 1029281 = 771961) B771961
theorem B1029299 : Blo 682313 1029299 := bstep (se 1 (by rfl) ⟨771974, by rfl⟩ : syracuseStep 1029299 = 1543949) B1543949
theorem B1029329 : Blo 682313 1029329 := bstep (se 2 (by rfl) ⟨385998, by rfl⟩ : syracuseStep 1029329 = 771997) B771997
theorem B1029347 : Blo 682313 1029347 := bstep (se 1 (by rfl) ⟨772010, by rfl⟩ : syracuseStep 1029347 = 1544021) B1544021
theorem B1029377 : Blo 682313 1029377 := bstep (se 2 (by rfl) ⟨386016, by rfl⟩ : syracuseStep 1029377 = 772033) B772033
theorem B1684739 : Blo 682313 1684739 := bstep (se 1 (by rfl) ⟨1263554, by rfl⟩ : syracuseStep 1684739 = 2527109) B2527109
theorem B1029395 : Blo 682313 1029395 := bstep (se 1 (by rfl) ⟨772046, by rfl⟩ : syracuseStep 1029395 = 1544093) B1544093
theorem B1029425 : Blo 682313 1029425 := bstep (se 2 (by rfl) ⟨386034, by rfl⟩ : syracuseStep 1029425 = 772069) B772069
theorem B1029443 : Blo 682313 1029443 := bstep (se 1 (by rfl) ⟨772082, by rfl⟩ : syracuseStep 1029443 = 1544165) B1544165
theorem B2635085 : Blo 682313 2635085 := bstep (se 3 (by rfl) ⟨494078, by rfl⟩ : syracuseStep 2635085 = 988157) B988157
theorem B2930033 : Blo 682313 2930033 := bstep (se 2 (by rfl) ⟨1098762, by rfl⟩ : syracuseStep 2930033 = 2197525) B2197525
theorem B865667 : Blo 682313 865667 := bstep (se 1 (by rfl) ⟨649250, by rfl⟩ : syracuseStep 865667 = 1298501) B1298501
theorem B2307473 : Blo 682313 2307473 := bstep (se 2 (by rfl) ⟨865302, by rfl⟩ : syracuseStep 2307473 = 1730605) B1730605
theorem B1095137 : Blo 682313 1095137 := bstep (se 2 (by rfl) ⟨410676, by rfl⟩ : syracuseStep 1095137 = 821353) B821353
theorem B1947149 : Blo 682313 1947149 := bstep (se 3 (by rfl) ⟨365090, by rfl⟩ : syracuseStep 1947149 = 730181) B730181
theorem B2602637 : Blo 682313 2602637 := bstep (se 3 (by rfl) ⟨487994, by rfl⟩ : syracuseStep 2602637 = 975989) B975989
theorem B1095329 : Blo 682313 1095329 := bstep (se 2 (by rfl) ⟨410748, by rfl⟩ : syracuseStep 1095329 = 821497) B821497
theorem B1947341 : Blo 682313 1947341 := bstep (se 3 (by rfl) ⟨365126, by rfl⟩ : syracuseStep 1947341 = 730253) B730253
theorem B767731 : Blo 682313 767731 := bstep (se 1 (by rfl) ⟨575798, by rfl⟩ : syracuseStep 767731 = 1151597) B1151597
theorem B1095457 : Blo 682313 1095457 := bstep (se 2 (by rfl) ⟨410796, by rfl⟩ : syracuseStep 1095457 = 821593) B821593
theorem B1849169 : Blo 682313 1849169 := bstep (se 2 (by rfl) ⟨693438, by rfl⟩ : syracuseStep 1849169 = 1386877) B1386877
theorem B767875 : Blo 682313 767875 := bstep (se 1 (by rfl) ⟨575906, by rfl⟩ : syracuseStep 767875 = 1151813) B1151813
theorem B2308013 : Blo 682313 2308013 := bstep (se 3 (by rfl) ⟨432752, by rfl⟩ : syracuseStep 2308013 = 865505) B865505
theorem B2308067 : Blo 682313 2308067 := bstep (se 1 (by rfl) ⟨1731050, by rfl⟩ : syracuseStep 2308067 = 3462101) B3462101
theorem B2930701 : Blo 682313 2930701 := bstep (se 3 (by rfl) ⟨549506, by rfl⟩ : syracuseStep 2930701 = 1099013) B1099013
theorem B768019 : Blo 682313 768019 := bstep (se 1 (by rfl) ⟨576014, by rfl⟩ : syracuseStep 768019 = 1152029) B1152029
theorem B14956597 : Blo 682313 14956597 := bstep (se 5 (by rfl) ⟨701090, by rfl⟩ : syracuseStep 14956597 = 1402181) B1402181
theorem B866371 : Blo 682313 866371 := bstep (se 1 (by rfl) ⟨649778, by rfl⟩ : syracuseStep 866371 = 1299557) B1299557
theorem B768163 : Blo 682313 768163 := bstep (se 1 (by rfl) ⟨576122, by rfl⟩ : syracuseStep 768163 = 1152245) B1152245
theorem B866467 : Blo 682313 866467 := bstep (se 1 (by rfl) ⟨649850, by rfl⟩ : syracuseStep 866467 = 1299701) B1299701
theorem B2308337 : Blo 682313 2308337 := bstep (se 2 (by rfl) ⟨865626, by rfl⟩ : syracuseStep 2308337 = 1731253) B1731253
theorem B768307 : Blo 682313 768307 := bstep (se 1 (by rfl) ⟨576230, by rfl⟩ : syracuseStep 768307 = 1152461) B1152461
theorem B4372805 : Blo 682313 4372805 := bstep (se 4 (by rfl) ⟨409950, by rfl⟩ : syracuseStep 4372805 = 819901) B819901
theorem B1096097 : Blo 682313 1096097 := bstep (se 2 (by rfl) ⟨411036, by rfl⟩ : syracuseStep 1096097 = 822073) B822073
theorem B1030577 : Blo 682313 1030577 := bstep (se 2 (by rfl) ⟨386466, by rfl⟩ : syracuseStep 1030577 = 772933) B772933
theorem B2603441 : Blo 682313 2603441 := bstep (se 2 (by rfl) ⟨976290, by rfl⟩ : syracuseStep 2603441 = 1952581) B1952581
theorem B768451 : Blo 682313 768451 := bstep (se 1 (by rfl) ⟨576338, by rfl⟩ : syracuseStep 768451 = 1152677) B1152677
theorem B4733411 : Blo 682313 4733411 := bstep (se 1 (by rfl) ⟨3550058, by rfl⟩ : syracuseStep 4733411 = 7100117) B7100117
theorem B3455459 : Blo 682313 3455459 := bstep (se 1 (by rfl) ⟨2591594, by rfl⟩ : syracuseStep 3455459 = 5183189) B5183189
theorem B2079245 : Blo 682313 2079245 := bstep (se 3 (by rfl) ⟨389858, by rfl⟩ : syracuseStep 2079245 = 779717) B779717
theorem B768595 : Blo 682313 768595 := bstep (se 1 (by rfl) ⟨576446, by rfl⟩ : syracuseStep 768595 = 1152893) B1152893
theorem B2931299 : Blo 682313 2931299 := bstep (se 1 (by rfl) ⟨2198474, by rfl⟩ : syracuseStep 2931299 = 4396949) B4396949
theorem B4274801 : Blo 682313 4274801 := bstep (se 2 (by rfl) ⟨1603050, by rfl⟩ : syracuseStep 4274801 = 3206101) B3206101
theorem B866963 : Blo 682313 866963 := bstep (se 1 (by rfl) ⟨650222, by rfl⟩ : syracuseStep 866963 = 1300445) B1300445
theorem B1948333 : Blo 682313 1948333 := bstep (se 3 (by rfl) ⟨365312, by rfl⟩ : syracuseStep 1948333 = 730625) B730625
theorem B768739 : Blo 682313 768739 := bstep (se 1 (by rfl) ⟨576554, by rfl⟩ : syracuseStep 768739 = 1153109) B1153109
theorem B2308877 : Blo 682313 2308877 := bstep (se 3 (by rfl) ⟨432914, by rfl⟩ : syracuseStep 2308877 = 865829) B865829
theorem B2308931 : Blo 682313 2308931 := bstep (se 1 (by rfl) ⟨1731698, by rfl⟩ : syracuseStep 2308931 = 3463397) B3463397
theorem B4799345 : Blo 682313 4799345 := bstep (se 2 (by rfl) ⟨1799754, by rfl⟩ : syracuseStep 4799345 = 3599509) B3599509
theorem B768883 : Blo 682313 768883 := bstep (se 1 (by rfl) ⟨576662, by rfl⟩ : syracuseStep 768883 = 1153325) B1153325
theorem B769027 : Blo 682313 769027 := bstep (se 1 (by rfl) ⟨576770, by rfl⟩ : syracuseStep 769027 = 1153541) B1153541
theorem B1850435 : Blo 682313 1850435 := bstep (se 1 (by rfl) ⟨1387826, by rfl⟩ : syracuseStep 1850435 = 2775653) B2775653
theorem B2604109 : Blo 682313 2604109 := bstep (se 3 (by rfl) ⟨488270, by rfl⟩ : syracuseStep 2604109 = 976541) B976541
theorem B2309201 : Blo 682313 2309201 := bstep (se 2 (by rfl) ⟨865950, by rfl⟩ : syracuseStep 2309201 = 1731901) B1731901
theorem B2964593 : Blo 682313 2964593 := bstep (se 2 (by rfl) ⟨1111722, by rfl⟩ : syracuseStep 2964593 = 2223445) B2223445
theorem B769171 : Blo 682313 769171 := bstep (se 1 (by rfl) ⟨576878, by rfl⟩ : syracuseStep 769171 = 1153757) B1153757
theorem B6569201 : Blo 682313 6569201 := bstep (se 2 (by rfl) ⟨2463450, by rfl⟩ : syracuseStep 6569201 = 4926901) B4926901
theorem B3456269 : Blo 682313 3456269 := bstep (se 3 (by rfl) ⟨648050, by rfl⟩ : syracuseStep 3456269 = 1296101) B1296101
theorem B769315 : Blo 682313 769315 := bstep (se 1 (by rfl) ⟨576986, by rfl⟩ : syracuseStep 769315 = 1153973) B1153973
theorem B867667 : Blo 682313 867667 := bstep (se 1 (by rfl) ⟨650750, by rfl⟩ : syracuseStep 867667 = 1301501) B1301501
theorem B2342243 : Blo 682313 2342243 := bstep (se 1 (by rfl) ⟨1756682, by rfl⟩ : syracuseStep 2342243 = 3513365) B3513365
theorem B2768269 : Blo 682313 2768269 := bstep (se 3 (by rfl) ⟨519050, by rfl⟩ : syracuseStep 2768269 = 1038101) B1038101
theorem B1457585 : Blo 682313 1457585 := bstep (se 2 (by rfl) ⟨546594, by rfl⟩ : syracuseStep 1457585 = 1093189) B1093189
theorem B769459 : Blo 682313 769459 := bstep (se 1 (by rfl) ⟨577094, by rfl⟩ : syracuseStep 769459 = 1154189) B1154189
theorem B867763 : Blo 682313 867763 := bstep (se 1 (by rfl) ⟨650822, by rfl⟩ : syracuseStep 867763 = 1301645) B1301645
theorem B835043 : Blo 682313 835043 := bstep (se 1 (by rfl) ⟨626282, by rfl⟩ : syracuseStep 835043 = 1252565) B1252565
theorem B769603 : Blo 682313 769603 := bstep (se 1 (by rfl) ⟨577202, by rfl⟩ : syracuseStep 769603 = 1154405) B1154405
theorem B2309741 : Blo 682313 2309741 := bstep (se 3 (by rfl) ⟨433076, by rfl⟩ : syracuseStep 2309741 = 866153) B866153
theorem B2309795 : Blo 682313 2309795 := bstep (se 1 (by rfl) ⟨1732346, by rfl⟩ : syracuseStep 2309795 = 3464693) B3464693
theorem B769747 : Blo 682313 769747 := bstep (se 1 (by rfl) ⟨577310, by rfl⟩ : syracuseStep 769747 = 1154621) B1154621
theorem B1097507 : Blo 682313 1097507 := bstep (se 1 (by rfl) ⟨823130, by rfl⟩ : syracuseStep 1097507 = 1646261) B1646261
theorem B769891 : Blo 682313 769891 := bstep (se 1 (by rfl) ⟨577418, by rfl⟩ : syracuseStep 769891 = 1154837) B1154837
theorem B2604899 : Blo 682313 2604899 := bstep (se 1 (by rfl) ⟨1953674, by rfl⟩ : syracuseStep 2604899 = 3907349) B3907349
theorem B1851245 : Blo 682313 1851245 := bstep (se 3 (by rfl) ⟨347108, by rfl⟩ : syracuseStep 1851245 = 694217) B694217
theorem B1097635 : Blo 682313 1097635 := bstep (se 1 (by rfl) ⟨823226, by rfl⟩ : syracuseStep 1097635 = 1646453) B1646453
theorem B868259 : Blo 682313 868259 := bstep (se 1 (by rfl) ⟨651194, by rfl⟩ : syracuseStep 868259 = 1302389) B1302389
theorem B2310065 : Blo 682313 2310065 := bstep (se 2 (by rfl) ⟨866274, by rfl⟩ : syracuseStep 2310065 = 1732549) B1732549
theorem B770035 : Blo 682313 770035 := bstep (se 1 (by rfl) ⟨577526, by rfl⟩ : syracuseStep 770035 = 1155053) B1155053
theorem B770179 : Blo 682313 770179 := bstep (se 1 (by rfl) ⟨577634, by rfl⟩ : syracuseStep 770179 = 1155269) B1155269
theorem B770323 : Blo 682313 770323 := bstep (se 1 (by rfl) ⟨577742, by rfl⟩ : syracuseStep 770323 = 1155485) B1155485
theorem B1622371 : Blo 682313 1622371 := bstep (se 1 (by rfl) ⟨1216778, by rfl⟩ : syracuseStep 1622371 = 2433557) B2433557
theorem B1950065 : Blo 682313 1950065 := bstep (se 2 (by rfl) ⟨731274, by rfl⟩ : syracuseStep 1950065 = 1462549) B1462549
theorem B770467 : Blo 682313 770467 := bstep (se 1 (by rfl) ⟨577850, by rfl⟩ : syracuseStep 770467 = 1155701) B1155701
theorem B2310605 : Blo 682313 2310605 := bstep (se 3 (by rfl) ⟨433238, by rfl⟩ : syracuseStep 2310605 = 866477) B866477
theorem B2113997 : Blo 682313 2113997 := bstep (se 3 (by rfl) ⟨396374, by rfl⟩ : syracuseStep 2113997 = 792749) B792749
theorem B1098193 : Blo 682313 1098193 := bstep (se 2 (by rfl) ⟨411822, by rfl⟩ : syracuseStep 1098193 = 823645) B823645
theorem B2605553 : Blo 682313 2605553 := bstep (se 2 (by rfl) ⟨977082, by rfl⟩ : syracuseStep 2605553 = 1954165) B1954165
theorem B2310659 : Blo 682313 2310659 := bstep (se 1 (by rfl) ⟨1732994, by rfl⟩ : syracuseStep 2310659 = 3465989) B3465989
theorem B1950257 : Blo 682313 1950257 := bstep (se 2 (by rfl) ⟨731346, by rfl⟩ : syracuseStep 1950257 = 1462693) B1462693
theorem B3129905 : Blo 682313 3129905 := bstep (se 2 (by rfl) ⟨1173714, by rfl⟩ : syracuseStep 3129905 = 2347429) B2347429
theorem B770611 : Blo 682313 770611 := bstep (se 1 (by rfl) ⟨577958, by rfl⟩ : syracuseStep 770611 = 1155917) B1155917
theorem B770755 : Blo 682313 770755 := bstep (se 1 (by rfl) ⟨578066, by rfl⟩ : syracuseStep 770755 = 1156133) B1156133
theorem B4440781 : Blo 682313 4440781 := bstep (se 3 (by rfl) ⟨832646, by rfl⟩ : syracuseStep 4440781 = 1665293) B1665293
theorem B4932323 : Blo 682313 4932323 := bstep (se 1 (by rfl) ⟨3699242, by rfl⟩ : syracuseStep 4932323 = 7398485) B7398485
theorem B2310929 : Blo 682313 2310929 := bstep (se 2 (by rfl) ⟨866598, by rfl⟩ : syracuseStep 2310929 = 1733197) B1733197
theorem B2081603 : Blo 682313 2081603 := bstep (se 1 (by rfl) ⟨1561202, by rfl⟩ : syracuseStep 2081603 = 3122405) B3122405
theorem B770899 : Blo 682313 770899 := bstep (se 1 (by rfl) ⟨578174, by rfl⟩ : syracuseStep 770899 = 1156349) B1156349
theorem B1000369 : Blo 682313 1000369 := bstep (se 2 (by rfl) ⟨375138, by rfl⟩ : syracuseStep 1000369 = 750277) B750277
theorem B1459139 : Blo 682313 1459139 := bstep (se 1 (by rfl) ⟨1094354, by rfl⟩ : syracuseStep 1459139 = 2188709) B2188709
theorem B771043 : Blo 682313 771043 := bstep (se 1 (by rfl) ⟨578282, by rfl⟩ : syracuseStep 771043 = 1156565) B1156565
theorem B1852433 : Blo 682313 1852433 := bstep (se 2 (by rfl) ⟨694662, by rfl⟩ : syracuseStep 1852433 = 1389325) B1389325
theorem B1098865 : Blo 682313 1098865 := bstep (se 2 (by rfl) ⟨412074, by rfl⟩ : syracuseStep 1098865 = 824149) B824149
theorem B771187 : Blo 682313 771187 := bstep (se 1 (by rfl) ⟨578390, by rfl⟩ : syracuseStep 771187 = 1156781) B1156781
theorem B6571205 : Blo 682313 6571205 := bstep (se 4 (by rfl) ⟨616050, by rfl⟩ : syracuseStep 6571205 = 1232101) B1232101
theorem B1230083 : Blo 682313 1230083 := bstep (se 1 (by rfl) ⟨922562, by rfl⟩ : syracuseStep 1230083 = 1845125) B1845125
theorem B771331 : Blo 682313 771331 := bstep (se 1 (by rfl) ⟨578498, by rfl⟩ : syracuseStep 771331 = 1156997) B1156997
theorem B2311469 : Blo 682313 2311469 := bstep (se 3 (by rfl) ⟨433400, by rfl⟩ : syracuseStep 2311469 = 866801) B866801
theorem B1557809 : Blo 682313 1557809 := bstep (se 2 (by rfl) ⟨584178, by rfl⟩ : syracuseStep 1557809 = 1168357) B1168357
theorem B5850467 : Blo 682313 5850467 := bstep (se 1 (by rfl) ⟨4387850, by rfl⟩ : syracuseStep 5850467 = 8775701) B8775701
theorem B2311523 : Blo 682313 2311523 := bstep (se 1 (by rfl) ⟨1733642, by rfl⟩ : syracuseStep 2311523 = 3467285) B3467285
theorem B771475 : Blo 682313 771475 := bstep (se 1 (by rfl) ⟨578606, by rfl⟩ : syracuseStep 771475 = 1157213) B1157213
theorem B23643589 : Blo 682313 23643589 := bstep (se 4 (by rfl) ⟨2216586, by rfl⟩ : syracuseStep 23643589 = 4433173) B4433173
theorem B1951249 : Blo 682313 1951249 := bstep (se 2 (by rfl) ⟨731718, by rfl⟩ : syracuseStep 1951249 = 1463437) B1463437
theorem B771619 : Blo 682313 771619 := bstep (se 1 (by rfl) ⟨578714, by rfl⟩ : syracuseStep 771619 = 1157429) B1157429
theorem B2311793 : Blo 682313 2311793 := bstep (se 2 (by rfl) ⟨866922, by rfl⟩ : syracuseStep 2311793 = 1733845) B1733845
theorem B771763 : Blo 682313 771763 := bstep (se 1 (by rfl) ⟨578822, by rfl⟩ : syracuseStep 771763 = 1157645) B1157645
theorem B13158085 : Blo 682313 13158085 := bstep (se 4 (by rfl) ⟨1233570, by rfl⟩ : syracuseStep 13158085 = 2467141) B2467141
theorem B1230545 : Blo 682313 1230545 := bstep (se 2 (by rfl) ⟨461454, by rfl⟩ : syracuseStep 1230545 = 922909) B922909
theorem B1951523 : Blo 682313 1951523 := bstep (se 1 (by rfl) ⟨1463642, by rfl⟩ : syracuseStep 1951523 = 2927285) B2927285
theorem B4376369 : Blo 682313 4376369 := bstep (se 2 (by rfl) ⟨1641138, by rfl⟩ : syracuseStep 4376369 = 3282277) B3282277
theorem B7784261 : Blo 682313 7784261 := bstep (se 4 (by rfl) ⟨729774, by rfl⟩ : syracuseStep 7784261 = 1459549) B1459549
theorem B771907 : Blo 682313 771907 := bstep (se 1 (by rfl) ⟨578930, by rfl⟩ : syracuseStep 771907 = 1157861) B1157861
theorem B1558385 : Blo 682313 1558385 := bstep (se 2 (by rfl) ⟨584394, by rfl⟩ : syracuseStep 1558385 = 1168789) B1168789
theorem B1296337 : Blo 682313 1296337 := bstep (se 2 (by rfl) ⟨486126, by rfl⟩ : syracuseStep 1296337 = 972253) B972253
theorem B772051 : Blo 682313 772051 := bstep (se 1 (by rfl) ⟨579038, by rfl⟩ : syracuseStep 772051 = 1158077) B1158077
theorem B1951715 : Blo 682313 1951715 := bstep (se 1 (by rfl) ⟨1463786, by rfl⟩ : syracuseStep 1951715 = 2927573) B2927573
theorem B3459185 : Blo 682313 3459185 := bstep (se 2 (by rfl) ⟨1297194, by rfl⟩ : syracuseStep 3459185 = 2594389) B2594389
theorem B2312333 : Blo 682313 2312333 := bstep (se 3 (by rfl) ⟨433562, by rfl⟩ : syracuseStep 2312333 = 867125) B867125
theorem B2312387 : Blo 682313 2312387 := bstep (se 1 (by rfl) ⟨1734290, by rfl⟩ : syracuseStep 2312387 = 3468581) B3468581
theorem B1296739 : Blo 682313 1296739 := bstep (se 1 (by rfl) ⟨972554, by rfl⟩ : syracuseStep 1296739 = 1945109) B1945109
theorem B1296785 : Blo 682313 1296785 := bstep (se 2 (by rfl) ⟨486294, by rfl⟩ : syracuseStep 1296785 = 972589) B972589
theorem B2312657 : Blo 682313 2312657 := bstep (se 2 (by rfl) ⟨867246, by rfl⟩ : syracuseStep 2312657 = 1734493) B1734493
theorem B1297073 : Blo 682313 1297073 := bstep (se 2 (by rfl) ⟨486402, by rfl⟩ : syracuseStep 1297073 = 972805) B972805
theorem B1952525 : Blo 682313 1952525 := bstep (se 3 (by rfl) ⟨366098, by rfl⟩ : syracuseStep 1952525 = 732197) B732197
theorem B1231697 : Blo 682313 1231697 := bstep (se 2 (by rfl) ⟨461886, by rfl⟩ : syracuseStep 1231697 = 923773) B923773
theorem B1952707 : Blo 682313 1952707 := bstep (se 1 (by rfl) ⟨1464530, by rfl⟩ : syracuseStep 1952707 = 2929061) B2929061
theorem B2313197 : Blo 682313 2313197 := bstep (se 3 (by rfl) ⟨433724, by rfl⟩ : syracuseStep 2313197 = 867449) B867449
theorem B2313251 : Blo 682313 2313251 := bstep (se 1 (by rfl) ⟨1734938, by rfl⟩ : syracuseStep 2313251 = 3469877) B3469877
theorem B1461361 : Blo 682313 1461361 := bstep (se 2 (by rfl) ⟨548010, by rfl⟩ : syracuseStep 1461361 = 1096021) B1096021
theorem B4377827 : Blo 682313 4377827 := bstep (se 1 (by rfl) ⟨3283370, by rfl⟩ : syracuseStep 4377827 = 6566741) B6566741
theorem B3296483 : Blo 682313 3296483 := bstep (se 1 (by rfl) ⟨2472362, by rfl⟩ : syracuseStep 3296483 = 4944725) B4944725
theorem B2313521 : Blo 682313 2313521 := bstep (se 2 (by rfl) ⟨867570, by rfl⟩ : syracuseStep 2313521 = 1735141) B1735141
theorem B1297795 : Blo 682313 1297795 := bstep (se 1 (by rfl) ⟨973346, by rfl⟩ : syracuseStep 1297795 = 1946693) B1946693
theorem B1953197 : Blo 682313 1953197 := bstep (se 3 (by rfl) ⟨366224, by rfl⟩ : syracuseStep 1953197 = 732449) B732449
theorem B5197283 : Blo 682313 5197283 := bstep (se 1 (by rfl) ⟨3897962, by rfl⟩ : syracuseStep 5197283 = 7795925) B7795925
theorem B3460643 : Blo 682313 3460643 := bstep (se 1 (by rfl) ⟨2595482, by rfl⟩ : syracuseStep 3460643 = 5190965) B5190965
theorem B7884557 : Blo 682313 7884557 := bstep (se 3 (by rfl) ⟨1478354, by rfl⟩ : syracuseStep 7884557 = 2956709) B2956709
theorem B4935437 : Blo 682313 4935437 := bstep (se 3 (by rfl) ⟨925394, by rfl⟩ : syracuseStep 4935437 = 1850789) B1850789
theorem B2084621 : Blo 682313 2084621 := bstep (se 3 (by rfl) ⟨390866, by rfl⟩ : syracuseStep 2084621 = 781733) B781733
theorem B1298243 : Blo 682313 1298243 := bstep (se 1 (by rfl) ⟨973682, by rfl⟩ : syracuseStep 1298243 = 1947365) B1947365
theorem B741187 : Blo 682313 741187 := bstep (se 1 (by rfl) ⟨555890, by rfl⟩ : syracuseStep 741187 = 1111781) B1111781
theorem B2314061 : Blo 682313 2314061 := bstep (se 3 (by rfl) ⟨433886, by rfl⟩ : syracuseStep 2314061 = 867773) B867773
theorem B2314115 : Blo 682313 2314115 := bstep (se 1 (by rfl) ⟨1735586, by rfl⟩ : syracuseStep 2314115 = 3471173) B3471173
theorem B1298531 : Blo 682313 1298531 := bstep (se 1 (by rfl) ⟨973898, by rfl⟩ : syracuseStep 1298531 = 1947797) B1947797
theorem B1232995 : Blo 682313 1232995 := bstep (se 1 (by rfl) ⟨924746, by rfl⟩ : syracuseStep 1232995 = 1849493) B1849493
theorem B1560721 : Blo 682313 1560721 := bstep (se 2 (by rfl) ⟨585270, by rfl⟩ : syracuseStep 1560721 = 1170541) B1170541
theorem B2314385 : Blo 682313 2314385 := bstep (se 2 (by rfl) ⟨867894, by rfl⟩ : syracuseStep 2314385 = 1735789) B1735789
theorem B2085155 : Blo 682313 2085155 := bstep (se 1 (by rfl) ⟨1563866, by rfl⟩ : syracuseStep 2085155 = 3127733) B3127733
theorem B3461453 : Blo 682313 3461453 := bstep (se 3 (by rfl) ⟨649022, by rfl⟩ : syracuseStep 3461453 = 1298045) B1298045
theorem B7885297 : Blo 682313 7885297 := bstep (se 2 (by rfl) ⟨2956986, by rfl⟩ : syracuseStep 7885297 = 5913973) B5913973
theorem B3887621 : Blo 682313 3887621 := bstep (se 4 (by rfl) ⟨364464, by rfl⟩ : syracuseStep 3887621 = 728929) B728929
theorem B1954381 : Blo 682313 1954381 := bstep (se 3 (by rfl) ⟨366446, by rfl⟩ : syracuseStep 1954381 = 732893) B732893
theorem B3297905 : Blo 682313 3297905 := bstep (se 2 (by rfl) ⟨1236714, by rfl⟩ : syracuseStep 3297905 = 2473429) B2473429
theorem B2314925 : Blo 682313 2314925 := bstep (se 3 (by rfl) ⟨434048, by rfl⟩ : syracuseStep 2314925 = 868097) B868097
theorem B2314979 : Blo 682313 2314979 := bstep (se 1 (by rfl) ⟨1736234, by rfl⟩ : syracuseStep 2314979 = 3472469) B3472469
theorem B2315249 : Blo 682313 2315249 := bstep (se 2 (by rfl) ⟨868218, by rfl⟩ : syracuseStep 2315249 = 1736437) B1736437
theorem B1299473 : Blo 682313 1299473 := bstep (se 2 (by rfl) ⟨487302, by rfl⟩ : syracuseStep 1299473 = 974605) B974605
theorem B2217041 : Blo 682313 2217041 := bstep (se 2 (by rfl) ⟨831390, by rfl⟩ : syracuseStep 2217041 = 1662781) B1662781
theorem B1168481 : Blo 682313 1168481 := bstep (se 2 (by rfl) ⟨438180, by rfl⟩ : syracuseStep 1168481 = 876361) B876361
theorem B1168849 : Blo 682313 1168849 := bstep (se 2 (by rfl) ⟨438318, by rfl⟩ : syracuseStep 1168849 = 876637) B876637
theorem B2315789 : Blo 682313 2315789 := bstep (se 3 (by rfl) ⟨434210, by rfl⟩ : syracuseStep 2315789 = 868421) B868421
theorem B2315843 : Blo 682313 2315843 := bstep (se 1 (by rfl) ⟨1736882, by rfl⟩ : syracuseStep 2315843 = 3473765) B3473765
theorem B2250317 : Blo 682313 2250317 := bstep (se 3 (by rfl) ⟨421934, by rfl⟩ : syracuseStep 2250317 = 843869) B843869
theorem B972481 : Blo 682313 972481 := bstep (se 2 (by rfl) ⟨364680, by rfl⟩ : syracuseStep 972481 = 729361) B729361
theorem B8345285 : Blo 682313 8345285 := bstep (se 4 (by rfl) ⟨782370, by rfl⟩ : syracuseStep 8345285 = 1564741) B1564741
theorem B972577 : Blo 682313 972577 := bstep (se 2 (by rfl) ⟨364716, by rfl⟩ : syracuseStep 972577 = 729433) B729433
theorem B4380493 : Blo 682313 4380493 := bstep (se 3 (by rfl) ⟨821342, by rfl⟩ : syracuseStep 4380493 = 1642685) B1642685
theorem B2316113 : Blo 682313 2316113 := bstep (se 2 (by rfl) ⟨868542, by rfl⟩ : syracuseStep 2316113 = 1737085) B1737085
theorem B1300369 : Blo 682313 1300369 := bstep (se 2 (by rfl) ⟨487638, by rfl⟩ : syracuseStep 1300369 = 975277) B975277
theorem B1300529 : Blo 682313 1300529 := bstep (se 2 (by rfl) ⟨487698, by rfl⟩ : syracuseStep 1300529 = 975397) B975397
theorem B1464419 : Blo 682313 1464419 := bstep (se 1 (by rfl) ⟨1098314, by rfl⟩ : syracuseStep 1464419 = 2196629) B2196629
theorem B1038467 : Blo 682313 1038467 := bstep (se 1 (by rfl) ⟨778850, by rfl⟩ : syracuseStep 1038467 = 1557701) B1557701
theorem B973073 : Blo 682313 973073 := bstep (se 2 (by rfl) ⟨364902, by rfl⟩ : syracuseStep 973073 = 729805) B729805
theorem B7493987 : Blo 682313 7493987 := bstep (se 1 (by rfl) ⟨5620490, by rfl⟩ : syracuseStep 7493987 = 11240981) B11240981
theorem B1300931 : Blo 682313 1300931 := bstep (se 1 (by rfl) ⟨975698, by rfl⟩ : syracuseStep 1300931 = 1951397) B1951397
theorem B1169905 : Blo 682313 1169905 := bstep (se 2 (by rfl) ⟨438714, by rfl⟩ : syracuseStep 1169905 = 877429) B877429
theorem B1727153 : Blo 682313 1727153 := bstep (se 2 (by rfl) ⟨647682, by rfl⟩ : syracuseStep 1727153 = 1295365) B1295365
theorem B1727203 : Blo 682313 1727203 := bstep (se 1 (by rfl) ⟨1295402, by rfl⟩ : syracuseStep 1727203 = 2590805) B2590805
theorem B2218769 : Blo 682313 2218769 := bstep (se 2 (by rfl) ⟨832038, by rfl⟩ : syracuseStep 2218769 = 1664077) B1664077
theorem B1727345 : Blo 682313 1727345 := bstep (se 2 (by rfl) ⟨647754, by rfl⟩ : syracuseStep 1727345 = 1295509) B1295509
theorem B7035761 : Blo 682313 7035761 := bstep (se 2 (by rfl) ⟨2638410, by rfl⟩ : syracuseStep 7035761 = 5276821) B5276821
theorem B1465283 : Blo 682313 1465283 := bstep (se 1 (by rfl) ⟨1098962, by rfl⟩ : syracuseStep 1465283 = 2197925) B2197925
theorem B1039313 : Blo 682313 1039313 := bstep (se 2 (by rfl) ⟨389742, by rfl⟩ : syracuseStep 1039313 = 779485) B779485
theorem B1465393 : Blo 682313 1465393 := bstep (se 2 (by rfl) ⟨549522, by rfl⟩ : syracuseStep 1465393 = 1099045) B1099045
theorem B973939 : Blo 682313 973939 := bstep (se 1 (by rfl) ⟨730454, by rfl⟩ : syracuseStep 973939 = 1460909) B1460909
theorem B3464369 : Blo 682313 3464369 := bstep (se 2 (by rfl) ⟨1299138, by rfl⟩ : syracuseStep 3464369 = 2598277) B2598277
theorem B4447429 : Blo 682313 4447429 := bstep (se 4 (by rfl) ⟨416946, by rfl⟩ : syracuseStep 4447429 = 833893) B833893
theorem B974035 : Blo 682313 974035 := bstep (se 1 (by rfl) ⟨730526, by rfl⟩ : syracuseStep 974035 = 1461053) B1461053
theorem B1301827 : Blo 682313 1301827 := bstep (se 1 (by rfl) ⟨976370, by rfl⟩ : syracuseStep 1301827 = 1952741) B1952741
theorem B4677041 : Blo 682313 4677041 := bstep (se 2 (by rfl) ⟨1753890, by rfl⟩ : syracuseStep 4677041 = 3507781) B3507781
theorem B1301987 : Blo 682313 1301987 := bstep (se 1 (by rfl) ⟨976490, by rfl⟩ : syracuseStep 1301987 = 1952981) B1952981
theorem B7790093 : Blo 682313 7790093 := bstep (se 3 (by rfl) ⟨1460642, by rfl⟩ : syracuseStep 7790093 = 2921285) B2921285
theorem B974531 : Blo 682313 974531 := bstep (se 1 (by rfl) ⟨730898, by rfl⟩ : syracuseStep 974531 = 1461797) B1461797
theorem B2186993 : Blo 682313 2186993 := bstep (se 2 (by rfl) ⟨820122, by rfl⟩ : syracuseStep 2186993 = 1640245) B1640245
theorem B1171219 : Blo 682313 1171219 := bstep (se 1 (by rfl) ⟨878414, by rfl⟩ : syracuseStep 1171219 = 1756829) B1756829
theorem B1728337 : Blo 682313 1728337 := bstep (se 2 (by rfl) ⟨648126, by rfl⟩ : syracuseStep 1728337 = 1296253) B1296253
theorem B2187121 : Blo 682313 2187121 := bstep (se 2 (by rfl) ⟨820170, by rfl⟩ : syracuseStep 2187121 = 1640341) B1640341
theorem B1728611 : Blo 682313 1728611 := bstep (se 1 (by rfl) ⟨1296458, by rfl⟩ : syracuseStep 1728611 = 2592917) B2592917
theorem B2187377 : Blo 682313 2187377 := bstep (se 2 (by rfl) ⟨820266, by rfl⟩ : syracuseStep 2187377 = 1640533) B1640533
theorem B2253059 : Blo 682313 2253059 := bstep (se 1 (by rfl) ⟨1689794, by rfl⟩ : syracuseStep 2253059 = 3379589) B3379589
theorem B1728803 : Blo 682313 1728803 := bstep (se 1 (by rfl) ⟨1296602, by rfl⟩ : syracuseStep 1728803 = 2593205) B2593205
theorem B975169 : Blo 682313 975169 := bstep (se 2 (by rfl) ⟨365688, by rfl⟩ : syracuseStep 975169 = 731377) B731377
theorem B3465827 : Blo 682313 3465827 := bstep (se 1 (by rfl) ⟨2599370, by rfl⟩ : syracuseStep 3465827 = 5198741) B5198741
theorem B2777741 : Blo 682313 2777741 := bstep (se 3 (by rfl) ⟨520826, by rfl⟩ : syracuseStep 2777741 = 1041653) B1041653
theorem B975505 : Blo 682313 975505 := bstep (se 2 (by rfl) ⟨365814, by rfl⟩ : syracuseStep 975505 = 731629) B731629
theorem B5202629 : Blo 682313 5202629 := bstep (se 4 (by rfl) ⟨487746, by rfl⟩ : syracuseStep 5202629 = 975493) B975493
theorem B1172291 : Blo 682313 1172291 := bstep (se 1 (by rfl) ⟨879218, by rfl⟩ : syracuseStep 1172291 = 1758437) B1758437
theorem B1041265 : Blo 682313 1041265 := bstep (se 2 (by rfl) ⟨390474, by rfl⟩ : syracuseStep 1041265 = 780949) B780949
theorem B1729745 : Blo 682313 1729745 := bstep (se 2 (by rfl) ⟨648654, by rfl⟩ : syracuseStep 1729745 = 1297309) B1297309
theorem B976097 : Blo 682313 976097 := bstep (se 2 (by rfl) ⟨366036, by rfl⟩ : syracuseStep 976097 = 732073) B732073
theorem B1729795 : Blo 682313 1729795 := bstep (se 1 (by rfl) ⟨1297346, by rfl⟩ : syracuseStep 1729795 = 2594693) B2594693
theorem B1041745 : Blo 682313 1041745 := bstep (se 2 (by rfl) ⟨390654, by rfl⟩ : syracuseStep 1041745 = 781309) B781309
theorem B1041763 : Blo 682313 1041763 := bstep (se 1 (by rfl) ⟨781322, by rfl⟩ : syracuseStep 1041763 = 1562645) B1562645
theorem B3466637 : Blo 682313 3466637 := bstep (se 3 (by rfl) ⟨649994, by rfl⟩ : syracuseStep 3466637 = 1299989) B1299989
theorem B1729937 : Blo 682313 1729937 := bstep (se 2 (by rfl) ⟨648726, by rfl⟩ : syracuseStep 1729937 = 1297453) B1297453
theorem B976627 : Blo 682313 976627 := bstep (se 1 (by rfl) ⟨732470, by rfl⟩ : syracuseStep 976627 = 1464941) B1464941
theorem B2189069 : Blo 682313 2189069 := bstep (se 3 (by rfl) ⟨410450, by rfl⟩ : syracuseStep 2189069 = 820901) B820901
theorem B976963 : Blo 682313 976963 := bstep (se 1 (by rfl) ⟨732722, by rfl⟩ : syracuseStep 976963 = 1465445) B1465445
theorem B3893453 : Blo 682313 3893453 := bstep (se 3 (by rfl) ⟨730022, by rfl⟩ : syracuseStep 3893453 = 1460045) B1460045
theorem B682323 : Blo 682313 682323 := bstep (se 1 (by rfl) ⟨511742, by rfl⟩ : syracuseStep 682323 = 1023485) B1023485
theorem B682339 : Blo 682313 682339 := bstep (se 1 (by rfl) ⟨511754, by rfl⟩ : syracuseStep 682339 = 1023509) B1023509
theorem B1730929 : Blo 682313 1730929 := bstep (se 2 (by rfl) ⟨649098, by rfl⟩ : syracuseStep 1730929 = 1298197) B1298197
theorem B7793009 : Blo 682313 7793009 := bstep (se 2 (by rfl) ⟨2922378, by rfl⟩ : syracuseStep 7793009 = 5844757) B5844757
theorem B682355 : Blo 682313 682355 := bstep (se 1 (by rfl) ⟨511766, by rfl⟩ : syracuseStep 682355 = 1023533) B1023533
theorem B682371 : Blo 682313 682371 := bstep (se 1 (by rfl) ⟨511778, by rfl⟩ : syracuseStep 682371 = 1023557) B1023557
theorem B682387 : Blo 682313 682387 := bstep (se 1 (by rfl) ⟨511790, by rfl⟩ : syracuseStep 682387 = 1023581) B1023581
theorem B682403 : Blo 682313 682403 := bstep (se 1 (by rfl) ⟨511802, by rfl⟩ : syracuseStep 682403 = 1023605) B1023605
theorem B682419 : Blo 682313 682419 := bstep (se 1 (by rfl) ⟨511814, by rfl⟩ : syracuseStep 682419 = 1023629) B1023629
theorem B682435 : Blo 682313 682435 := bstep (se 1 (by rfl) ⟨511826, by rfl⟩ : syracuseStep 682435 = 1023653) B1023653
theorem B682451 : Blo 682313 682451 := bstep (se 1 (by rfl) ⟨511838, by rfl⟩ : syracuseStep 682451 = 1023677) B1023677
theorem B879059 : Blo 682313 879059 := bstep (se 1 (by rfl) ⟨659294, by rfl⟩ : syracuseStep 879059 = 1318589) B1318589
theorem B682467 : Blo 682313 682467 := bstep (se 1 (by rfl) ⟨511850, by rfl⟩ : syracuseStep 682467 = 1023701) B1023701
theorem B682483 : Blo 682313 682483 := bstep (se 1 (by rfl) ⟨511862, by rfl⟩ : syracuseStep 682483 = 1023725) B1023725
theorem B1042931 : Blo 682313 1042931 := bstep (se 1 (by rfl) ⟨782198, by rfl⟩ : syracuseStep 1042931 = 1564397) B1564397
theorem B682499 : Blo 682313 682499 := bstep (se 1 (by rfl) ⟨511874, by rfl⟩ : syracuseStep 682499 = 1023749) B1023749
theorem B2189837 : Blo 682313 2189837 := bstep (se 3 (by rfl) ⟨410594, by rfl⟩ : syracuseStep 2189837 = 821189) B821189
theorem B682515 : Blo 682313 682515 := bstep (se 1 (by rfl) ⟨511886, by rfl⟩ : syracuseStep 682515 = 1023773) B1023773
theorem B682531 : Blo 682313 682531 := bstep (se 1 (by rfl) ⟨511898, by rfl⟩ : syracuseStep 682531 = 1023797) B1023797
theorem B682547 : Blo 682313 682547 := bstep (se 1 (by rfl) ⟨511910, by rfl⟩ : syracuseStep 682547 = 1023821) B1023821
theorem B682563 : Blo 682313 682563 := bstep (se 1 (by rfl) ⟨511922, by rfl⟩ : syracuseStep 682563 = 1023845) B1023845
theorem B682579 : Blo 682313 682579 := bstep (se 1 (by rfl) ⟨511934, by rfl⟩ : syracuseStep 682579 = 1023869) B1023869
theorem B682595 : Blo 682313 682595 := bstep (se 1 (by rfl) ⟨511946, by rfl⟩ : syracuseStep 682595 = 1023893) B1023893
theorem B682611 : Blo 682313 682611 := bstep (se 1 (by rfl) ⟨511958, by rfl⟩ : syracuseStep 682611 = 1023917) B1023917
theorem B682627 : Blo 682313 682627 := bstep (se 1 (by rfl) ⟨511970, by rfl⟩ : syracuseStep 682627 = 1023941) B1023941
theorem B1731203 : Blo 682313 1731203 := bstep (se 1 (by rfl) ⟨1298402, by rfl⟩ : syracuseStep 1731203 = 2596805) B2596805
theorem B682643 : Blo 682313 682643 := bstep (se 1 (by rfl) ⟨511982, by rfl⟩ : syracuseStep 682643 = 1023965) B1023965
theorem B682659 : Blo 682313 682659 := bstep (se 1 (by rfl) ⟨511994, by rfl⟩ : syracuseStep 682659 = 1023989) B1023989
theorem B682675 : Blo 682313 682675 := bstep (se 1 (by rfl) ⟨512006, by rfl⟩ : syracuseStep 682675 = 1024013) B1024013
theorem B682691 : Blo 682313 682691 := bstep (se 1 (by rfl) ⟨512018, by rfl⟩ : syracuseStep 682691 = 1024037) B1024037
theorem B682707 : Blo 682313 682707 := bstep (se 1 (by rfl) ⟨512030, by rfl⟩ : syracuseStep 682707 = 1024061) B1024061
theorem B682723 : Blo 682313 682723 := bstep (se 1 (by rfl) ⟨512042, by rfl⟩ : syracuseStep 682723 = 1024085) B1024085
theorem B5073635 : Blo 682313 5073635 := bstep (se 1 (by rfl) ⟨3805226, by rfl⟩ : syracuseStep 5073635 = 7610453) B7610453
theorem B682739 : Blo 682313 682739 := bstep (se 1 (by rfl) ⟨512054, by rfl⟩ : syracuseStep 682739 = 1024109) B1024109
theorem B682755 : Blo 682313 682755 := bstep (se 1 (by rfl) ⟨512066, by rfl⟩ : syracuseStep 682755 = 1024133) B1024133
theorem B682771 : Blo 682313 682771 := bstep (se 1 (by rfl) ⟨512078, by rfl⟩ : syracuseStep 682771 = 1024157) B1024157
theorem B682787 : Blo 682313 682787 := bstep (se 1 (by rfl) ⟨512090, by rfl⟩ : syracuseStep 682787 = 1024181) B1024181
theorem B682803 : Blo 682313 682803 := bstep (se 1 (by rfl) ⟨512102, by rfl⟩ : syracuseStep 682803 = 1024205) B1024205
theorem B682819 : Blo 682313 682819 := bstep (se 1 (by rfl) ⟨512114, by rfl⟩ : syracuseStep 682819 = 1024229) B1024229
theorem B1731395 : Blo 682313 1731395 := bstep (se 1 (by rfl) ⟨1298546, by rfl⟩ : syracuseStep 1731395 = 2597093) B2597093
theorem B682835 : Blo 682313 682835 := bstep (se 1 (by rfl) ⟨512126, by rfl⟩ : syracuseStep 682835 = 1024253) B1024253
theorem B682851 : Blo 682313 682851 := bstep (se 1 (by rfl) ⟨512138, by rfl⟩ : syracuseStep 682851 = 1024277) B1024277
theorem B682867 : Blo 682313 682867 := bstep (se 1 (by rfl) ⟨512150, by rfl⟩ : syracuseStep 682867 = 1024301) B1024301
theorem B682883 : Blo 682313 682883 := bstep (se 1 (by rfl) ⟨512162, by rfl⟩ : syracuseStep 682883 = 1024325) B1024325
theorem B682899 : Blo 682313 682899 := bstep (se 1 (by rfl) ⟨512174, by rfl⟩ : syracuseStep 682899 = 1024349) B1024349
theorem B682915 : Blo 682313 682915 := bstep (se 1 (by rfl) ⟨512186, by rfl⟩ : syracuseStep 682915 = 1024373) B1024373
theorem B682931 : Blo 682313 682931 := bstep (se 1 (by rfl) ⟨512198, by rfl⟩ : syracuseStep 682931 = 1024397) B1024397
theorem B682947 : Blo 682313 682947 := bstep (se 1 (by rfl) ⟨512210, by rfl⟩ : syracuseStep 682947 = 1024421) B1024421
theorem B682963 : Blo 682313 682963 := bstep (se 1 (by rfl) ⟨512222, by rfl⟩ : syracuseStep 682963 = 1024445) B1024445
theorem B682979 : Blo 682313 682979 := bstep (se 1 (by rfl) ⟨512234, by rfl⟩ : syracuseStep 682979 = 1024469) B1024469
theorem B682995 : Blo 682313 682995 := bstep (se 1 (by rfl) ⟨512246, by rfl⟩ : syracuseStep 682995 = 1024493) B1024493
theorem B683011 : Blo 682313 683011 := bstep (se 1 (by rfl) ⟨512258, by rfl⟩ : syracuseStep 683011 = 1024517) B1024517
theorem B2190349 : Blo 682313 2190349 := bstep (se 3 (by rfl) ⟨410690, by rfl⟩ : syracuseStep 2190349 = 821381) B821381
theorem B683027 : Blo 682313 683027 := bstep (se 1 (by rfl) ⟨512270, by rfl⟩ : syracuseStep 683027 = 1024541) B1024541
theorem B683043 : Blo 682313 683043 := bstep (se 1 (by rfl) ⟨512282, by rfl⟩ : syracuseStep 683043 = 1024565) B1024565
theorem B683059 : Blo 682313 683059 := bstep (se 1 (by rfl) ⟨512294, by rfl⟩ : syracuseStep 683059 = 1024589) B1024589
theorem B683075 : Blo 682313 683075 := bstep (se 1 (by rfl) ⟨512306, by rfl⟩ : syracuseStep 683075 = 1024613) B1024613
theorem B683091 : Blo 682313 683091 := bstep (se 1 (by rfl) ⟨512318, by rfl⟩ : syracuseStep 683091 = 1024637) B1024637
theorem B683107 : Blo 682313 683107 := bstep (se 1 (by rfl) ⟨512330, by rfl⟩ : syracuseStep 683107 = 1024661) B1024661
theorem B683123 : Blo 682313 683123 := bstep (se 1 (by rfl) ⟨512342, by rfl⟩ : syracuseStep 683123 = 1024685) B1024685
theorem B683139 : Blo 682313 683139 := bstep (se 1 (by rfl) ⟨512354, by rfl⟩ : syracuseStep 683139 = 1024709) B1024709
theorem B683155 : Blo 682313 683155 := bstep (se 1 (by rfl) ⟨512366, by rfl⟩ : syracuseStep 683155 = 1024733) B1024733
theorem B683171 : Blo 682313 683171 := bstep (se 1 (by rfl) ⟨512378, by rfl⟩ : syracuseStep 683171 = 1024757) B1024757
theorem B683187 : Blo 682313 683187 := bstep (se 1 (by rfl) ⟨512390, by rfl⟩ : syracuseStep 683187 = 1024781) B1024781
theorem B683203 : Blo 682313 683203 := bstep (se 1 (by rfl) ⟨512402, by rfl⟩ : syracuseStep 683203 = 1024805) B1024805
theorem B683219 : Blo 682313 683219 := bstep (se 1 (by rfl) ⟨512414, by rfl⟩ : syracuseStep 683219 = 1024829) B1024829
theorem B683235 : Blo 682313 683235 := bstep (se 1 (by rfl) ⟨512426, by rfl⟩ : syracuseStep 683235 = 1024853) B1024853
theorem B683251 : Blo 682313 683251 := bstep (se 1 (by rfl) ⟨512438, by rfl⟩ : syracuseStep 683251 = 1024877) B1024877
theorem B683267 : Blo 682313 683267 := bstep (se 1 (by rfl) ⟨512450, by rfl⟩ : syracuseStep 683267 = 1024901) B1024901
theorem B683283 : Blo 682313 683283 := bstep (se 1 (by rfl) ⟨512462, by rfl⟩ : syracuseStep 683283 = 1024925) B1024925
theorem B683299 : Blo 682313 683299 := bstep (se 1 (by rfl) ⟨512474, by rfl⟩ : syracuseStep 683299 = 1024949) B1024949
theorem B683315 : Blo 682313 683315 := bstep (se 1 (by rfl) ⟨512486, by rfl⟩ : syracuseStep 683315 = 1024973) B1024973
theorem B683331 : Blo 682313 683331 := bstep (se 1 (by rfl) ⟨512498, by rfl⟩ : syracuseStep 683331 = 1024997) B1024997
theorem B3009869 : Blo 682313 3009869 := bstep (se 3 (by rfl) ⟨564350, by rfl⟩ : syracuseStep 3009869 = 1128701) B1128701
theorem B683347 : Blo 682313 683347 := bstep (se 1 (by rfl) ⟨512510, by rfl⟩ : syracuseStep 683347 = 1025021) B1025021
theorem B683363 : Blo 682313 683363 := bstep (se 1 (by rfl) ⟨512522, by rfl⟩ : syracuseStep 683363 = 1025045) B1025045
theorem B1535345 : Blo 682313 1535345 := bstep (se 2 (by rfl) ⟨575754, by rfl⟩ : syracuseStep 1535345 = 1151509) B1151509
theorem B683379 : Blo 682313 683379 := bstep (se 1 (by rfl) ⟨512534, by rfl⟩ : syracuseStep 683379 = 1025069) B1025069
theorem B1535363 : Blo 682313 1535363 := bstep (se 1 (by rfl) ⟨1151522, by rfl⟩ : syracuseStep 1535363 = 2303045) B2303045
theorem B683395 : Blo 682313 683395 := bstep (se 1 (by rfl) ⟨512546, by rfl⟩ : syracuseStep 683395 = 1025093) B1025093
theorem B683411 : Blo 682313 683411 := bstep (se 1 (by rfl) ⟨512558, by rfl⟩ : syracuseStep 683411 = 1025117) B1025117
theorem B683427 : Blo 682313 683427 := bstep (se 1 (by rfl) ⟨512570, by rfl⟩ : syracuseStep 683427 = 1025141) B1025141
theorem B683443 : Blo 682313 683443 := bstep (se 1 (by rfl) ⟨512582, by rfl⟩ : syracuseStep 683443 = 1025165) B1025165
theorem B683459 : Blo 682313 683459 := bstep (se 1 (by rfl) ⟨512594, by rfl⟩ : syracuseStep 683459 = 1025189) B1025189
theorem B683475 : Blo 682313 683475 := bstep (se 1 (by rfl) ⟨512606, by rfl⟩ : syracuseStep 683475 = 1025213) B1025213
theorem B683491 : Blo 682313 683491 := bstep (se 1 (by rfl) ⟨512618, by rfl⟩ : syracuseStep 683491 = 1025237) B1025237
theorem B683507 : Blo 682313 683507 := bstep (se 1 (by rfl) ⟨512630, by rfl⟩ : syracuseStep 683507 = 1025261) B1025261
theorem B683523 : Blo 682313 683523 := bstep (se 1 (by rfl) ⟨512642, by rfl⟩ : syracuseStep 683523 = 1025285) B1025285
theorem B2190851 : Blo 682313 2190851 := bstep (se 1 (by rfl) ⟨1643138, by rfl⟩ : syracuseStep 2190851 = 3286277) B3286277
theorem B683539 : Blo 682313 683539 := bstep (se 1 (by rfl) ⟨512654, by rfl⟩ : syracuseStep 683539 = 1025309) B1025309
theorem B683555 : Blo 682313 683555 := bstep (se 1 (by rfl) ⟨512666, by rfl⟩ : syracuseStep 683555 = 1025333) B1025333
theorem B3010097 : Blo 682313 3010097 := bstep (se 2 (by rfl) ⟨1128786, by rfl⟩ : syracuseStep 3010097 = 2257573) B2257573
theorem B683571 : Blo 682313 683571 := bstep (se 1 (by rfl) ⟨512678, by rfl⟩ : syracuseStep 683571 = 1025357) B1025357
theorem B683587 : Blo 682313 683587 := bstep (se 1 (by rfl) ⟨512690, by rfl⟩ : syracuseStep 683587 = 1025381) B1025381
theorem B683603 : Blo 682313 683603 := bstep (se 1 (by rfl) ⟨512702, by rfl⟩ : syracuseStep 683603 = 1025405) B1025405
theorem B683619 : Blo 682313 683619 := bstep (se 1 (by rfl) ⟨512714, by rfl⟩ : syracuseStep 683619 = 1025429) B1025429
theorem B683635 : Blo 682313 683635 := bstep (se 1 (by rfl) ⟨512726, by rfl⟩ : syracuseStep 683635 = 1025453) B1025453
theorem B683651 : Blo 682313 683651 := bstep (se 1 (by rfl) ⟨512738, by rfl⟩ : syracuseStep 683651 = 1025477) B1025477
theorem B1535633 : Blo 682313 1535633 := bstep (se 2 (by rfl) ⟨575862, by rfl⟩ : syracuseStep 1535633 = 1151725) B1151725
theorem B683667 : Blo 682313 683667 := bstep (se 1 (by rfl) ⟨512750, by rfl⟩ : syracuseStep 683667 = 1025501) B1025501
theorem B1535651 : Blo 682313 1535651 := bstep (se 1 (by rfl) ⟨1151738, by rfl⟩ : syracuseStep 1535651 = 2303477) B2303477
theorem B683683 : Blo 682313 683683 := bstep (se 1 (by rfl) ⟨512762, by rfl⟩ : syracuseStep 683683 = 1025525) B1025525
theorem B683699 : Blo 682313 683699 := bstep (se 1 (by rfl) ⟨512774, by rfl⟩ : syracuseStep 683699 = 1025549) B1025549
theorem B683715 : Blo 682313 683715 := bstep (se 1 (by rfl) ⟨512786, by rfl⟩ : syracuseStep 683715 = 1025573) B1025573
theorem B683731 : Blo 682313 683731 := bstep (se 1 (by rfl) ⟨512798, by rfl⟩ : syracuseStep 683731 = 1025597) B1025597
theorem B683747 : Blo 682313 683747 := bstep (se 1 (by rfl) ⟨512810, by rfl⟩ : syracuseStep 683747 = 1025621) B1025621
theorem B1732337 : Blo 682313 1732337 := bstep (se 2 (by rfl) ⟨649626, by rfl⟩ : syracuseStep 1732337 = 1299253) B1299253
theorem B683763 : Blo 682313 683763 := bstep (se 1 (by rfl) ⟨512822, by rfl⟩ : syracuseStep 683763 = 1025645) B1025645
theorem B683779 : Blo 682313 683779 := bstep (se 1 (by rfl) ⟨512834, by rfl⟩ : syracuseStep 683779 = 1025669) B1025669
theorem B683795 : Blo 682313 683795 := bstep (se 1 (by rfl) ⟨512846, by rfl⟩ : syracuseStep 683795 = 1025693) B1025693
theorem B683811 : Blo 682313 683811 := bstep (se 1 (by rfl) ⟨512858, by rfl⟩ : syracuseStep 683811 = 1025717) B1025717
theorem B1732387 : Blo 682313 1732387 := bstep (se 1 (by rfl) ⟨1299290, by rfl⟩ : syracuseStep 1732387 = 2598581) B2598581
theorem B683827 : Blo 682313 683827 := bstep (se 1 (by rfl) ⟨512870, by rfl⟩ : syracuseStep 683827 = 1025741) B1025741
theorem B683843 : Blo 682313 683843 := bstep (se 1 (by rfl) ⟨512882, by rfl⟩ : syracuseStep 683843 = 1025765) B1025765
theorem B683859 : Blo 682313 683859 := bstep (se 1 (by rfl) ⟨512894, by rfl⟩ : syracuseStep 683859 = 1025789) B1025789
theorem B683875 : Blo 682313 683875 := bstep (se 1 (by rfl) ⟨512906, by rfl⟩ : syracuseStep 683875 = 1025813) B1025813
theorem B683891 : Blo 682313 683891 := bstep (se 1 (by rfl) ⟨512918, by rfl⟩ : syracuseStep 683891 = 1025837) B1025837
theorem B683907 : Blo 682313 683907 := bstep (se 1 (by rfl) ⟨512930, by rfl⟩ : syracuseStep 683907 = 1025861) B1025861
theorem B683923 : Blo 682313 683923 := bstep (se 1 (by rfl) ⟨512942, by rfl⟩ : syracuseStep 683923 = 1025885) B1025885
theorem B683939 : Blo 682313 683939 := bstep (se 1 (by rfl) ⟨512954, by rfl⟩ : syracuseStep 683939 = 1025909) B1025909
theorem B1535921 : Blo 682313 1535921 := bstep (se 2 (by rfl) ⟨575970, by rfl⟩ : syracuseStep 1535921 = 1151941) B1151941
theorem B1732529 : Blo 682313 1732529 := bstep (se 2 (by rfl) ⟨649698, by rfl⟩ : syracuseStep 1732529 = 1299397) B1299397
theorem B683955 : Blo 682313 683955 := bstep (se 1 (by rfl) ⟨512966, by rfl⟩ : syracuseStep 683955 = 1025933) B1025933
theorem B1535939 : Blo 682313 1535939 := bstep (se 1 (by rfl) ⟨1151954, by rfl⟩ : syracuseStep 1535939 = 2303909) B2303909
theorem B683971 : Blo 682313 683971 := bstep (se 1 (by rfl) ⟨512978, by rfl⟩ : syracuseStep 683971 = 1025957) B1025957
theorem B683987 : Blo 682313 683987 := bstep (se 1 (by rfl) ⟨512990, by rfl⟩ : syracuseStep 683987 = 1025981) B1025981
theorem B684003 : Blo 682313 684003 := bstep (se 1 (by rfl) ⟨513002, by rfl⟩ : syracuseStep 684003 = 1026005) B1026005
theorem B684019 : Blo 682313 684019 := bstep (se 1 (by rfl) ⟨513014, by rfl⟩ : syracuseStep 684019 = 1026029) B1026029
theorem B684035 : Blo 682313 684035 := bstep (se 1 (by rfl) ⟨513026, by rfl⟩ : syracuseStep 684035 = 1026053) B1026053
theorem B684051 : Blo 682313 684051 := bstep (se 1 (by rfl) ⟨513038, by rfl⟩ : syracuseStep 684051 = 1026077) B1026077
theorem B684067 : Blo 682313 684067 := bstep (se 1 (by rfl) ⟨513050, by rfl⟩ : syracuseStep 684067 = 1026101) B1026101
theorem B684083 : Blo 682313 684083 := bstep (se 1 (by rfl) ⟨513062, by rfl⟩ : syracuseStep 684083 = 1026125) B1026125
theorem B684099 : Blo 682313 684099 := bstep (se 1 (by rfl) ⟨513074, by rfl⟩ : syracuseStep 684099 = 1026149) B1026149
theorem B684115 : Blo 682313 684115 := bstep (se 1 (by rfl) ⟨513086, by rfl⟩ : syracuseStep 684115 = 1026173) B1026173
theorem B684131 : Blo 682313 684131 := bstep (se 1 (by rfl) ⟨513098, by rfl⟩ : syracuseStep 684131 = 1026197) B1026197
theorem B28471409 : Blo 682313 28471409 := bstep (se 2 (by rfl) ⟨10676778, by rfl⟩ : syracuseStep 28471409 = 21353557) B21353557
theorem B684147 : Blo 682313 684147 := bstep (se 1 (by rfl) ⟨513110, by rfl⟩ : syracuseStep 684147 = 1026221) B1026221
theorem B684163 : Blo 682313 684163 := bstep (se 1 (by rfl) ⟨513122, by rfl⟩ : syracuseStep 684163 = 1026245) B1026245
theorem B684179 : Blo 682313 684179 := bstep (se 1 (by rfl) ⟨513134, by rfl⟩ : syracuseStep 684179 = 1026269) B1026269
theorem B684195 : Blo 682313 684195 := bstep (se 1 (by rfl) ⟨513146, by rfl⟩ : syracuseStep 684195 = 1026293) B1026293
theorem B684211 : Blo 682313 684211 := bstep (se 1 (by rfl) ⟨513158, by rfl⟩ : syracuseStep 684211 = 1026317) B1026317
theorem B684227 : Blo 682313 684227 := bstep (se 1 (by rfl) ⟨513170, by rfl⟩ : syracuseStep 684227 = 1026341) B1026341
theorem B1536209 : Blo 682313 1536209 := bstep (se 2 (by rfl) ⟨576078, by rfl⟩ : syracuseStep 1536209 = 1152157) B1152157
theorem B684243 : Blo 682313 684243 := bstep (se 1 (by rfl) ⟨513182, by rfl⟩ : syracuseStep 684243 = 1026365) B1026365
theorem B1536227 : Blo 682313 1536227 := bstep (se 1 (by rfl) ⟨1152170, by rfl⟩ : syracuseStep 1536227 = 2304341) B2304341
theorem B684259 : Blo 682313 684259 := bstep (se 1 (by rfl) ⟨513194, by rfl⟩ : syracuseStep 684259 = 1026389) B1026389
theorem B3469553 : Blo 682313 3469553 := bstep (se 2 (by rfl) ⟨1301082, by rfl⟩ : syracuseStep 3469553 = 2602165) B2602165
theorem B684275 : Blo 682313 684275 := bstep (se 1 (by rfl) ⟨513206, by rfl⟩ : syracuseStep 684275 = 1026413) B1026413
theorem B684291 : Blo 682313 684291 := bstep (se 1 (by rfl) ⟨513218, by rfl⟩ : syracuseStep 684291 = 1026437) B1026437
theorem B684307 : Blo 682313 684307 := bstep (se 1 (by rfl) ⟨513230, by rfl⟩ : syracuseStep 684307 = 1026461) B1026461
theorem B684323 : Blo 682313 684323 := bstep (se 1 (by rfl) ⟨513242, by rfl⟩ : syracuseStep 684323 = 1026485) B1026485
theorem B782627 : Blo 682313 782627 := bstep (se 1 (by rfl) ⟨586970, by rfl⟩ : syracuseStep 782627 = 1173941) B1173941
theorem B684339 : Blo 682313 684339 := bstep (se 1 (by rfl) ⟨513254, by rfl⟩ : syracuseStep 684339 = 1026509) B1026509
theorem B684355 : Blo 682313 684355 := bstep (se 1 (by rfl) ⟨513266, by rfl⟩ : syracuseStep 684355 = 1026533) B1026533
theorem B684371 : Blo 682313 684371 := bstep (se 1 (by rfl) ⟨513278, by rfl⟩ : syracuseStep 684371 = 1026557) B1026557
theorem B684387 : Blo 682313 684387 := bstep (se 1 (by rfl) ⟨513290, by rfl⟩ : syracuseStep 684387 = 1026581) B1026581
theorem B684403 : Blo 682313 684403 := bstep (se 1 (by rfl) ⟨513302, by rfl⟩ : syracuseStep 684403 = 1026605) B1026605
theorem B684419 : Blo 682313 684419 := bstep (se 1 (by rfl) ⟨513314, by rfl⟩ : syracuseStep 684419 = 1026629) B1026629
theorem B3895685 : Blo 682313 3895685 := bstep (se 4 (by rfl) ⟨365220, by rfl⟩ : syracuseStep 3895685 = 730441) B730441
theorem B684435 : Blo 682313 684435 := bstep (se 1 (by rfl) ⟨513326, by rfl⟩ : syracuseStep 684435 = 1026653) B1026653
theorem B684451 : Blo 682313 684451 := bstep (se 1 (by rfl) ⟨513338, by rfl⟩ : syracuseStep 684451 = 1026677) B1026677
theorem B684467 : Blo 682313 684467 := bstep (se 1 (by rfl) ⟨513350, by rfl⟩ : syracuseStep 684467 = 1026701) B1026701
theorem B684483 : Blo 682313 684483 := bstep (se 1 (by rfl) ⟨513362, by rfl⟩ : syracuseStep 684483 = 1026725) B1026725
theorem B684499 : Blo 682313 684499 := bstep (se 1 (by rfl) ⟨513374, by rfl⟩ : syracuseStep 684499 = 1026749) B1026749
theorem B684515 : Blo 682313 684515 := bstep (se 1 (by rfl) ⟨513386, by rfl⟩ : syracuseStep 684515 = 1026773) B1026773
theorem B1536497 : Blo 682313 1536497 := bstep (se 2 (by rfl) ⟨576186, by rfl⟩ : syracuseStep 1536497 = 1152373) B1152373
theorem B684531 : Blo 682313 684531 := bstep (se 1 (by rfl) ⟨513398, by rfl⟩ : syracuseStep 684531 = 1026797) B1026797
theorem B1536515 : Blo 682313 1536515 := bstep (se 1 (by rfl) ⟨1152386, by rfl⟩ : syracuseStep 1536515 = 2304773) B2304773
theorem B684547 : Blo 682313 684547 := bstep (se 1 (by rfl) ⟨513410, by rfl⟩ : syracuseStep 684547 = 1026821) B1026821
theorem B684563 : Blo 682313 684563 := bstep (se 1 (by rfl) ⟨513422, by rfl⟩ : syracuseStep 684563 = 1026845) B1026845
theorem B684579 : Blo 682313 684579 := bstep (se 1 (by rfl) ⟨513434, by rfl⟩ : syracuseStep 684579 = 1026869) B1026869
theorem B684595 : Blo 682313 684595 := bstep (se 1 (by rfl) ⟨513446, by rfl⟩ : syracuseStep 684595 = 1026893) B1026893
theorem B684611 : Blo 682313 684611 := bstep (se 1 (by rfl) ⟨513458, by rfl⟩ : syracuseStep 684611 = 1026917) B1026917
theorem B684627 : Blo 682313 684627 := bstep (se 1 (by rfl) ⟨513470, by rfl⟩ : syracuseStep 684627 = 1026941) B1026941
theorem B684643 : Blo 682313 684643 := bstep (se 1 (by rfl) ⟨513482, by rfl⟩ : syracuseStep 684643 = 1026965) B1026965
theorem B684659 : Blo 682313 684659 := bstep (se 1 (by rfl) ⟨513494, by rfl⟩ : syracuseStep 684659 = 1026989) B1026989
theorem B684675 : Blo 682313 684675 := bstep (se 1 (by rfl) ⟨513506, by rfl⟩ : syracuseStep 684675 = 1027013) B1027013
theorem B684691 : Blo 682313 684691 := bstep (se 1 (by rfl) ⟨513518, by rfl⟩ : syracuseStep 684691 = 1027037) B1027037
theorem B684707 : Blo 682313 684707 := bstep (se 1 (by rfl) ⟨513530, by rfl⟩ : syracuseStep 684707 = 1027061) B1027061
theorem B684723 : Blo 682313 684723 := bstep (se 1 (by rfl) ⟨513542, by rfl⟩ : syracuseStep 684723 = 1027085) B1027085
theorem B684739 : Blo 682313 684739 := bstep (se 1 (by rfl) ⟨513554, by rfl⟩ : syracuseStep 684739 = 1027109) B1027109
theorem B1405649 : Blo 682313 1405649 := bstep (se 2 (by rfl) ⟨527118, by rfl⟩ : syracuseStep 1405649 = 1054237) B1054237
theorem B684755 : Blo 682313 684755 := bstep (se 1 (by rfl) ⟨513566, by rfl⟩ : syracuseStep 684755 = 1027133) B1027133
theorem B684771 : Blo 682313 684771 := bstep (se 1 (by rfl) ⟨513578, by rfl⟩ : syracuseStep 684771 = 1027157) B1027157
theorem B1667825 : Blo 682313 1667825 := bstep (se 2 (by rfl) ⟨625434, by rfl⟩ : syracuseStep 1667825 = 1250869) B1250869
theorem B684787 : Blo 682313 684787 := bstep (se 1 (by rfl) ⟨513590, by rfl⟩ : syracuseStep 684787 = 1027181) B1027181
theorem B684803 : Blo 682313 684803 := bstep (se 1 (by rfl) ⟨513602, by rfl⟩ : syracuseStep 684803 = 1027205) B1027205
theorem B1536785 : Blo 682313 1536785 := bstep (se 2 (by rfl) ⟨576294, by rfl⟩ : syracuseStep 1536785 = 1152589) B1152589
theorem B684819 : Blo 682313 684819 := bstep (se 1 (by rfl) ⟨513614, by rfl⟩ : syracuseStep 684819 = 1027229) B1027229
theorem B1536803 : Blo 682313 1536803 := bstep (se 1 (by rfl) ⟨1152602, by rfl⟩ : syracuseStep 1536803 = 2305205) B2305205
theorem B684835 : Blo 682313 684835 := bstep (se 1 (by rfl) ⟨513626, by rfl⟩ : syracuseStep 684835 = 1027253) B1027253
theorem B684851 : Blo 682313 684851 := bstep (se 1 (by rfl) ⟨513638, by rfl⟩ : syracuseStep 684851 = 1027277) B1027277
theorem B684867 : Blo 682313 684867 := bstep (se 1 (by rfl) ⟨513650, by rfl⟩ : syracuseStep 684867 = 1027301) B1027301
theorem B684883 : Blo 682313 684883 := bstep (se 1 (by rfl) ⟨513662, by rfl⟩ : syracuseStep 684883 = 1027325) B1027325
theorem B684899 : Blo 682313 684899 := bstep (se 1 (by rfl) ⟨513674, by rfl⟩ : syracuseStep 684899 = 1027349) B1027349
theorem B6746993 : Blo 682313 6746993 := bstep (se 2 (by rfl) ⟨2530122, by rfl⟩ : syracuseStep 6746993 = 5060245) B5060245
theorem B684915 : Blo 682313 684915 := bstep (se 1 (by rfl) ⟨513686, by rfl⟩ : syracuseStep 684915 = 1027373) B1027373
theorem B684931 : Blo 682313 684931 := bstep (se 1 (by rfl) ⟨513698, by rfl⟩ : syracuseStep 684931 = 1027397) B1027397
theorem B1733521 : Blo 682313 1733521 := bstep (se 2 (by rfl) ⟨650070, by rfl⟩ : syracuseStep 1733521 = 1300141) B1300141
theorem B684947 : Blo 682313 684947 := bstep (se 1 (by rfl) ⟨513710, by rfl⟩ : syracuseStep 684947 = 1027421) B1027421
theorem B684963 : Blo 682313 684963 := bstep (se 1 (by rfl) ⟨513722, by rfl⟩ : syracuseStep 684963 = 1027445) B1027445
theorem B684979 : Blo 682313 684979 := bstep (se 1 (by rfl) ⟨513734, by rfl⟩ : syracuseStep 684979 = 1027469) B1027469
theorem B684995 : Blo 682313 684995 := bstep (se 1 (by rfl) ⟨513746, by rfl⟩ : syracuseStep 684995 = 1027493) B1027493
theorem B685011 : Blo 682313 685011 := bstep (se 1 (by rfl) ⟨513758, by rfl⟩ : syracuseStep 685011 = 1027517) B1027517
theorem B685027 : Blo 682313 685027 := bstep (se 1 (by rfl) ⟨513770, by rfl⟩ : syracuseStep 685027 = 1027541) B1027541
theorem B685043 : Blo 682313 685043 := bstep (se 1 (by rfl) ⟨513782, by rfl⟩ : syracuseStep 685043 = 1027565) B1027565
theorem B685059 : Blo 682313 685059 := bstep (se 1 (by rfl) ⟨513794, by rfl⟩ : syracuseStep 685059 = 1027589) B1027589
theorem B685075 : Blo 682313 685075 := bstep (se 1 (by rfl) ⟨513806, by rfl⟩ : syracuseStep 685075 = 1027613) B1027613
theorem B685091 : Blo 682313 685091 := bstep (se 1 (by rfl) ⟨513818, by rfl⟩ : syracuseStep 685091 = 1027637) B1027637
theorem B1537073 : Blo 682313 1537073 := bstep (se 2 (by rfl) ⟨576402, by rfl⟩ : syracuseStep 1537073 = 1152805) B1152805
theorem B3896369 : Blo 682313 3896369 := bstep (se 2 (by rfl) ⟨1461138, by rfl⟩ : syracuseStep 3896369 = 2922277) B2922277
theorem B685107 : Blo 682313 685107 := bstep (se 1 (by rfl) ⟨513830, by rfl⟩ : syracuseStep 685107 = 1027661) B1027661
theorem B1537091 : Blo 682313 1537091 := bstep (se 1 (by rfl) ⟨1152818, by rfl⟩ : syracuseStep 1537091 = 2305637) B2305637
theorem B685123 : Blo 682313 685123 := bstep (se 1 (by rfl) ⟨513842, by rfl⟩ : syracuseStep 685123 = 1027685) B1027685
theorem B685139 : Blo 682313 685139 := bstep (se 1 (by rfl) ⟨513854, by rfl⟩ : syracuseStep 685139 = 1027709) B1027709
theorem B685155 : Blo 682313 685155 := bstep (se 1 (by rfl) ⟨513866, by rfl⟩ : syracuseStep 685155 = 1027733) B1027733
theorem B685171 : Blo 682313 685171 := bstep (se 1 (by rfl) ⟨513878, by rfl⟩ : syracuseStep 685171 = 1027757) B1027757
theorem B685187 : Blo 682313 685187 := bstep (se 1 (by rfl) ⟨513890, by rfl⟩ : syracuseStep 685187 = 1027781) B1027781
theorem B685203 : Blo 682313 685203 := bstep (se 1 (by rfl) ⟨513902, by rfl⟩ : syracuseStep 685203 = 1027805) B1027805
theorem B1733795 : Blo 682313 1733795 := bstep (se 1 (by rfl) ⟨1300346, by rfl⟩ : syracuseStep 1733795 = 2600693) B2600693
theorem B685219 : Blo 682313 685219 := bstep (se 1 (by rfl) ⟨513914, by rfl⟩ : syracuseStep 685219 = 1027829) B1027829
theorem B685235 : Blo 682313 685235 := bstep (se 1 (by rfl) ⟨513926, by rfl⟩ : syracuseStep 685235 = 1027853) B1027853
theorem B685251 : Blo 682313 685251 := bstep (se 1 (by rfl) ⟨513938, by rfl⟩ : syracuseStep 685251 = 1027877) B1027877
theorem B685267 : Blo 682313 685267 := bstep (se 1 (by rfl) ⟨513950, by rfl⟩ : syracuseStep 685267 = 1027901) B1027901
theorem B685283 : Blo 682313 685283 := bstep (se 1 (by rfl) ⟨513962, by rfl⟩ : syracuseStep 685283 = 1027925) B1027925
theorem B685299 : Blo 682313 685299 := bstep (se 1 (by rfl) ⟨513974, by rfl⟩ : syracuseStep 685299 = 1027949) B1027949
theorem B685315 : Blo 682313 685315 := bstep (se 1 (by rfl) ⟨513986, by rfl⟩ : syracuseStep 685315 = 1027973) B1027973
theorem B685331 : Blo 682313 685331 := bstep (se 1 (by rfl) ⟨513998, by rfl⟩ : syracuseStep 685331 = 1027997) B1027997
theorem B685347 : Blo 682313 685347 := bstep (se 1 (by rfl) ⟨514010, by rfl⟩ : syracuseStep 685347 = 1028021) B1028021
theorem B685363 : Blo 682313 685363 := bstep (se 1 (by rfl) ⟨514022, by rfl⟩ : syracuseStep 685363 = 1028045) B1028045
theorem B2192707 : Blo 682313 2192707 := bstep (se 1 (by rfl) ⟨1644530, by rfl⟩ : syracuseStep 2192707 = 3289061) B3289061
theorem B685379 : Blo 682313 685379 := bstep (se 1 (by rfl) ⟨514034, by rfl⟩ : syracuseStep 685379 = 1028069) B1028069
theorem B1537361 : Blo 682313 1537361 := bstep (se 2 (by rfl) ⟨576510, by rfl⟩ : syracuseStep 1537361 = 1153021) B1153021
theorem B685395 : Blo 682313 685395 := bstep (se 1 (by rfl) ⟨514046, by rfl⟩ : syracuseStep 685395 = 1028093) B1028093
theorem B1537379 : Blo 682313 1537379 := bstep (se 1 (by rfl) ⟨1153034, by rfl⟩ : syracuseStep 1537379 = 2306069) B2306069
theorem B1733987 : Blo 682313 1733987 := bstep (se 1 (by rfl) ⟨1300490, by rfl⟩ : syracuseStep 1733987 = 2600981) B2600981
theorem B685411 : Blo 682313 685411 := bstep (se 1 (by rfl) ⟨514058, by rfl⟩ : syracuseStep 685411 = 1028117) B1028117
theorem B685427 : Blo 682313 685427 := bstep (se 1 (by rfl) ⟨514070, by rfl⟩ : syracuseStep 685427 = 1028141) B1028141
theorem B685443 : Blo 682313 685443 := bstep (se 1 (by rfl) ⟨514082, by rfl⟩ : syracuseStep 685443 = 1028165) B1028165
theorem B685459 : Blo 682313 685459 := bstep (se 1 (by rfl) ⟨514094, by rfl⟩ : syracuseStep 685459 = 1028189) B1028189
theorem B685475 : Blo 682313 685475 := bstep (se 1 (by rfl) ⟨514106, by rfl⟩ : syracuseStep 685475 = 1028213) B1028213
theorem B685491 : Blo 682313 685491 := bstep (se 1 (by rfl) ⟨514118, by rfl⟩ : syracuseStep 685491 = 1028237) B1028237
theorem B685507 : Blo 682313 685507 := bstep (se 1 (by rfl) ⟨514130, by rfl⟩ : syracuseStep 685507 = 1028261) B1028261
theorem B685523 : Blo 682313 685523 := bstep (se 1 (by rfl) ⟨514142, by rfl⟩ : syracuseStep 685523 = 1028285) B1028285
theorem B685539 : Blo 682313 685539 := bstep (se 1 (by rfl) ⟨514154, by rfl⟩ : syracuseStep 685539 = 1028309) B1028309
theorem B685555 : Blo 682313 685555 := bstep (se 1 (by rfl) ⟨514166, by rfl⟩ : syracuseStep 685555 = 1028333) B1028333
theorem B685571 : Blo 682313 685571 := bstep (se 1 (by rfl) ⟨514178, by rfl⟩ : syracuseStep 685571 = 1028357) B1028357
theorem B685587 : Blo 682313 685587 := bstep (se 1 (by rfl) ⟨514190, by rfl⟩ : syracuseStep 685587 = 1028381) B1028381
theorem B685603 : Blo 682313 685603 := bstep (se 1 (by rfl) ⟨514202, by rfl⟩ : syracuseStep 685603 = 1028405) B1028405
theorem B685619 : Blo 682313 685619 := bstep (se 1 (by rfl) ⟨514214, by rfl⟩ : syracuseStep 685619 = 1028429) B1028429
theorem B1111619 : Blo 682313 1111619 := bstep (se 1 (by rfl) ⟨833714, by rfl⟩ : syracuseStep 1111619 = 1667429) B1667429
theorem B685635 : Blo 682313 685635 := bstep (se 1 (by rfl) ⟨514226, by rfl⟩ : syracuseStep 685635 = 1028453) B1028453
theorem B685651 : Blo 682313 685651 := bstep (se 1 (by rfl) ⟨514238, by rfl⟩ : syracuseStep 685651 = 1028477) B1028477
theorem B685667 : Blo 682313 685667 := bstep (se 1 (by rfl) ⟨514250, by rfl⟩ : syracuseStep 685667 = 1028501) B1028501
theorem B1537649 : Blo 682313 1537649 := bstep (se 2 (by rfl) ⟨576618, by rfl⟩ : syracuseStep 1537649 = 1153237) B1153237
theorem B685683 : Blo 682313 685683 := bstep (se 1 (by rfl) ⟨514262, by rfl⟩ : syracuseStep 685683 = 1028525) B1028525
theorem B1537667 : Blo 682313 1537667 := bstep (se 1 (by rfl) ⟨1153250, by rfl⟩ : syracuseStep 1537667 = 2306501) B2306501
theorem B685699 : Blo 682313 685699 := bstep (se 1 (by rfl) ⟨514274, by rfl⟩ : syracuseStep 685699 = 1028549) B1028549
theorem B685715 : Blo 682313 685715 := bstep (se 1 (by rfl) ⟨514286, by rfl⟩ : syracuseStep 685715 = 1028573) B1028573
theorem B3471011 : Blo 682313 3471011 := bstep (se 1 (by rfl) ⟨2603258, by rfl⟩ : syracuseStep 3471011 = 5206517) B5206517
theorem B685731 : Blo 682313 685731 := bstep (se 1 (by rfl) ⟨514298, by rfl⟩ : syracuseStep 685731 = 1028597) B1028597
theorem B685747 : Blo 682313 685747 := bstep (se 1 (by rfl) ⟨514310, by rfl⟩ : syracuseStep 685747 = 1028621) B1028621
theorem B685763 : Blo 682313 685763 := bstep (se 1 (by rfl) ⟨514322, by rfl⟩ : syracuseStep 685763 = 1028645) B1028645
theorem B685779 : Blo 682313 685779 := bstep (se 1 (by rfl) ⟨514334, by rfl⟩ : syracuseStep 685779 = 1028669) B1028669
theorem B685795 : Blo 682313 685795 := bstep (se 1 (by rfl) ⟨514346, by rfl⟩ : syracuseStep 685795 = 1028693) B1028693
theorem B685811 : Blo 682313 685811 := bstep (se 1 (by rfl) ⟨514358, by rfl⟩ : syracuseStep 685811 = 1028717) B1028717
theorem B685827 : Blo 682313 685827 := bstep (se 1 (by rfl) ⟨514370, by rfl⟩ : syracuseStep 685827 = 1028741) B1028741
theorem B2193169 : Blo 682313 2193169 := bstep (se 2 (by rfl) ⟨822438, by rfl⟩ : syracuseStep 2193169 = 1644877) B1644877
theorem B685843 : Blo 682313 685843 := bstep (se 1 (by rfl) ⟨514382, by rfl⟩ : syracuseStep 685843 = 1028765) B1028765
theorem B685859 : Blo 682313 685859 := bstep (se 1 (by rfl) ⟨514394, by rfl⟩ : syracuseStep 685859 = 1028789) B1028789
theorem B685875 : Blo 682313 685875 := bstep (se 1 (by rfl) ⟨514406, by rfl⟩ : syracuseStep 685875 = 1028813) B1028813
theorem B685891 : Blo 682313 685891 := bstep (se 1 (by rfl) ⟨514418, by rfl⟩ : syracuseStep 685891 = 1028837) B1028837
theorem B685907 : Blo 682313 685907 := bstep (se 1 (by rfl) ⟨514430, by rfl⟩ : syracuseStep 685907 = 1028861) B1028861
theorem B685923 : Blo 682313 685923 := bstep (se 1 (by rfl) ⟨514442, by rfl⟩ : syracuseStep 685923 = 1028885) B1028885
theorem B685939 : Blo 682313 685939 := bstep (se 1 (by rfl) ⟨514454, by rfl⟩ : syracuseStep 685939 = 1028909) B1028909
theorem B685955 : Blo 682313 685955 := bstep (se 1 (by rfl) ⟨514466, by rfl⟩ : syracuseStep 685955 = 1028933) B1028933
theorem B1537937 : Blo 682313 1537937 := bstep (se 2 (by rfl) ⟨576726, by rfl⟩ : syracuseStep 1537937 = 1153453) B1153453
theorem B685971 : Blo 682313 685971 := bstep (se 1 (by rfl) ⟨514478, by rfl⟩ : syracuseStep 685971 = 1028957) B1028957
theorem B1537955 : Blo 682313 1537955 := bstep (se 1 (by rfl) ⟨1153466, by rfl⟩ : syracuseStep 1537955 = 2306933) B2306933
theorem B685987 : Blo 682313 685987 := bstep (se 1 (by rfl) ⟨514490, by rfl⟩ : syracuseStep 685987 = 1028981) B1028981
theorem B686003 : Blo 682313 686003 := bstep (se 1 (by rfl) ⟨514502, by rfl⟩ : syracuseStep 686003 = 1029005) B1029005
theorem B686019 : Blo 682313 686019 := bstep (se 1 (by rfl) ⟨514514, by rfl⟩ : syracuseStep 686019 = 1029029) B1029029
theorem B686035 : Blo 682313 686035 := bstep (se 1 (by rfl) ⟨514526, by rfl⟩ : syracuseStep 686035 = 1029053) B1029053
theorem B686051 : Blo 682313 686051 := bstep (se 1 (by rfl) ⟨514538, by rfl⟩ : syracuseStep 686051 = 1029077) B1029077
theorem B686067 : Blo 682313 686067 := bstep (se 1 (by rfl) ⟨514550, by rfl⟩ : syracuseStep 686067 = 1029101) B1029101
theorem B686083 : Blo 682313 686083 := bstep (se 1 (by rfl) ⟨514562, by rfl⟩ : syracuseStep 686083 = 1029125) B1029125
theorem B686099 : Blo 682313 686099 := bstep (se 1 (by rfl) ⟨514574, by rfl⟩ : syracuseStep 686099 = 1029149) B1029149
theorem B4388899 : Blo 682313 4388899 := bstep (se 1 (by rfl) ⟨3291674, by rfl⟩ : syracuseStep 4388899 = 6583349) B6583349
theorem B686115 : Blo 682313 686115 := bstep (se 1 (by rfl) ⟨514586, by rfl⟩ : syracuseStep 686115 = 1029173) B1029173
theorem B686131 : Blo 682313 686131 := bstep (se 1 (by rfl) ⟨514598, by rfl⟩ : syracuseStep 686131 = 1029197) B1029197
theorem B686147 : Blo 682313 686147 := bstep (se 1 (by rfl) ⟨514610, by rfl⟩ : syracuseStep 686147 = 1029221) B1029221
theorem B686163 : Blo 682313 686163 := bstep (se 1 (by rfl) ⟨514622, by rfl⟩ : syracuseStep 686163 = 1029245) B1029245
theorem B686179 : Blo 682313 686179 := bstep (se 1 (by rfl) ⟨514634, by rfl⟩ : syracuseStep 686179 = 1029269) B1029269
theorem B686195 : Blo 682313 686195 := bstep (se 1 (by rfl) ⟨514646, by rfl⟩ : syracuseStep 686195 = 1029293) B1029293
theorem B686211 : Blo 682313 686211 := bstep (se 1 (by rfl) ⟨514658, by rfl⟩ : syracuseStep 686211 = 1029317) B1029317
theorem B686227 : Blo 682313 686227 := bstep (se 1 (by rfl) ⟨514670, by rfl⟩ : syracuseStep 686227 = 1029341) B1029341
theorem B686243 : Blo 682313 686243 := bstep (se 1 (by rfl) ⟨514682, by rfl⟩ : syracuseStep 686243 = 1029365) B1029365
theorem B1538225 : Blo 682313 1538225 := bstep (se 2 (by rfl) ⟨576834, by rfl⟩ : syracuseStep 1538225 = 1153669) B1153669
theorem B686259 : Blo 682313 686259 := bstep (se 1 (by rfl) ⟨514694, by rfl⟩ : syracuseStep 686259 = 1029389) B1029389
theorem B1538243 : Blo 682313 1538243 := bstep (se 1 (by rfl) ⟨1153682, by rfl⟩ : syracuseStep 1538243 = 2307365) B2307365
theorem B686275 : Blo 682313 686275 := bstep (se 1 (by rfl) ⟨514706, by rfl⟩ : syracuseStep 686275 = 1029413) B1029413
theorem B686291 : Blo 682313 686291 := bstep (se 1 (by rfl) ⟨514718, by rfl⟩ : syracuseStep 686291 = 1029437) B1029437
theorem B686307 : Blo 682313 686307 := bstep (se 1 (by rfl) ⟨514730, by rfl⟩ : syracuseStep 686307 = 1029461) B1029461
theorem B1734929 : Blo 682313 1734929 := bstep (se 2 (by rfl) ⟨650598, by rfl⟩ : syracuseStep 1734929 = 1301197) B1301197
theorem B1734979 : Blo 682313 1734979 := bstep (se 1 (by rfl) ⟨1301234, by rfl⟩ : syracuseStep 1734979 = 2602469) B2602469
theorem B5208461 : Blo 682313 5208461 := bstep (se 3 (by rfl) ⟨976586, by rfl⟩ : syracuseStep 5208461 = 1953173) B1953173
theorem B3471821 : Blo 682313 3471821 := bstep (se 3 (by rfl) ⟨650966, by rfl⟩ : syracuseStep 3471821 = 1301933) B1301933
theorem B1538513 : Blo 682313 1538513 := bstep (se 2 (by rfl) ⟨576942, by rfl⟩ : syracuseStep 1538513 = 1153885) B1153885
theorem B1735121 : Blo 682313 1735121 := bstep (se 2 (by rfl) ⟨650670, by rfl⟩ : syracuseStep 1735121 = 1301341) B1301341
theorem B1538531 : Blo 682313 1538531 := bstep (se 1 (by rfl) ⟨1153898, by rfl⟩ : syracuseStep 1538531 = 2307797) B2307797
theorem B3897827 : Blo 682313 3897827 := bstep (se 1 (by rfl) ⟨2923370, by rfl⟩ : syracuseStep 3897827 = 5846741) B5846741
theorem B1538801 : Blo 682313 1538801 := bstep (se 2 (by rfl) ⟨577050, by rfl⟩ : syracuseStep 1538801 = 1154101) B1154101
theorem B1112833 : Blo 682313 1112833 := bstep (se 2 (by rfl) ⟨417312, by rfl⟩ : syracuseStep 1112833 = 834625) B834625
theorem B1538819 : Blo 682313 1538819 := bstep (se 1 (by rfl) ⟨1154114, by rfl⟩ : syracuseStep 1538819 = 2308229) B2308229
theorem B1539089 : Blo 682313 1539089 := bstep (se 2 (by rfl) ⟨577158, by rfl⟩ : syracuseStep 1539089 = 1154317) B1154317
theorem B1539107 : Blo 682313 1539107 := bstep (se 1 (by rfl) ⟨1154330, by rfl⟩ : syracuseStep 1539107 = 2308661) B2308661
theorem B2784397 : Blo 682313 2784397 := bstep (se 3 (by rfl) ⟨522074, by rfl⟩ : syracuseStep 2784397 = 1044149) B1044149
theorem B4160753 : Blo 682313 4160753 := bstep (se 2 (by rfl) ⟨1560282, by rfl⟩ : syracuseStep 4160753 = 3120565) B3120565
theorem B4390129 : Blo 682313 4390129 := bstep (se 2 (by rfl) ⟨1646298, by rfl⟩ : syracuseStep 4390129 = 3292597) B3292597
theorem B1539377 : Blo 682313 1539377 := bstep (se 2 (by rfl) ⟨577266, by rfl⟩ : syracuseStep 1539377 = 1154533) B1154533
theorem B1539395 : Blo 682313 1539395 := bstep (se 1 (by rfl) ⟨1154546, by rfl⟩ : syracuseStep 1539395 = 2309093) B2309093
theorem B1736113 : Blo 682313 1736113 := bstep (se 2 (by rfl) ⟨651042, by rfl⟩ : syracuseStep 1736113 = 1302085) B1302085
theorem B1539665 : Blo 682313 1539665 := bstep (se 2 (by rfl) ⟨577374, by rfl⟩ : syracuseStep 1539665 = 1154749) B1154749
theorem B2915939 : Blo 682313 2915939 := bstep (se 1 (by rfl) ⟨2186954, by rfl⟩ : syracuseStep 2915939 = 4373909) B4373909
theorem B1539683 : Blo 682313 1539683 := bstep (se 1 (by rfl) ⟨1154762, by rfl⟩ : syracuseStep 1539683 = 2309525) B2309525
theorem B1736387 : Blo 682313 1736387 := bstep (se 1 (by rfl) ⟨1302290, by rfl⟩ : syracuseStep 1736387 = 2604581) B2604581
theorem B1539953 : Blo 682313 1539953 := bstep (se 2 (by rfl) ⟨577482, by rfl⟩ : syracuseStep 1539953 = 1154965) B1154965
theorem B1539971 : Blo 682313 1539971 := bstep (se 1 (by rfl) ⟨1154978, by rfl⟩ : syracuseStep 1539971 = 2309957) B2309957
theorem B1736579 : Blo 682313 1736579 := bstep (se 1 (by rfl) ⟨1302434, by rfl⟩ : syracuseStep 1736579 = 2604869) B2604869
theorem B1540097 : Blo 682313 1540097 := bstep (se 2 (by rfl) ⟨577536, by rfl⟩ : syracuseStep 1540097 = 1155073) B1155073
theorem B19005475 : Blo 682313 19005475 := bstep (se 1 (by rfl) ⟨14254106, by rfl⟩ : syracuseStep 19005475 = 28508213) B28508213
theorem B1540313 : Blo 682313 1540313 := bstep (se 2 (by rfl) ⟨577617, by rfl⟩ : syracuseStep 1540313 = 1155235) B1155235
theorem B1540403 : Blo 682313 1540403 := bstep (se 1 (by rfl) ⟨1155302, by rfl⟩ : syracuseStep 1540403 = 2310605) B2310605
theorem B1737035 : Blo 682313 1737035 := bstep (se 1 (by rfl) ⟨1302776, by rfl⟩ : syracuseStep 1737035 = 2605553) B2605553
theorem B1540439 : Blo 682313 1540439 := bstep (se 1 (by rfl) ⟨1155329, by rfl⟩ : syracuseStep 1540439 = 2310659) B2310659
theorem B2163161 : Blo 682313 2163161 := bstep (se 2 (by rfl) ⟨811185, by rfl⟩ : syracuseStep 2163161 = 1622371) B1622371
theorem B1540619 : Blo 682313 1540619 := bstep (se 1 (by rfl) ⟨1155464, by rfl⟩ : syracuseStep 1540619 = 2310929) B2310929
theorem B1540673 : Blo 682313 1540673 := bstep (se 2 (by rfl) ⟨577752, by rfl⟩ : syracuseStep 1540673 = 1155505) B1155505
theorem B16646897 : Blo 682313 16646897 := bstep (se 2 (by rfl) ⟨6242586, by rfl⟩ : syracuseStep 16646897 = 12485173) B12485173
theorem B1540889 : Blo 682313 1540889 := bstep (se 2 (by rfl) ⟨577833, by rfl⟩ : syracuseStep 1540889 = 1155667) B1155667
theorem B3474251 : Blo 682313 3474251 := bstep (se 1 (by rfl) ⟨2605688, by rfl⟩ : syracuseStep 3474251 = 5211377) B5211377
theorem B820055 : Blo 682313 820055 := bstep (se 1 (by rfl) ⟨615041, by rfl⟩ : syracuseStep 820055 = 1230083) B1230083
theorem B1540979 : Blo 682313 1540979 := bstep (se 1 (by rfl) ⟨1155734, by rfl⟩ : syracuseStep 1540979 = 2311469) B2311469
theorem B3900311 : Blo 682313 3900311 := bstep (se 1 (by rfl) ⟨2925233, by rfl⟩ : syracuseStep 3900311 = 5850467) B5850467
theorem B1541015 : Blo 682313 1541015 := bstep (se 1 (by rfl) ⟨1155761, by rfl⟩ : syracuseStep 1541015 = 2311523) B2311523
theorem B1541195 : Blo 682313 1541195 := bstep (se 1 (by rfl) ⟨1155896, by rfl⟩ : syracuseStep 1541195 = 2311793) B2311793
theorem B1541249 : Blo 682313 1541249 := bstep (se 2 (by rfl) ⟨577968, by rfl⟩ : syracuseStep 1541249 = 1155937) B1155937
theorem B820363 : Blo 682313 820363 := bstep (se 1 (by rfl) ⟨615272, by rfl⟩ : syracuseStep 820363 = 1230545) B1230545
theorem B2917579 : Blo 682313 2917579 := bstep (se 1 (by rfl) ⟨2188184, by rfl⟩ : syracuseStep 2917579 = 4376369) B4376369
theorem B5637325 : Blo 682313 5637325 := bstep (se 3 (by rfl) ⟨1056998, by rfl⟩ : syracuseStep 5637325 = 2113997) B2113997
theorem B1541465 : Blo 682313 1541465 := bstep (se 2 (by rfl) ⟨578049, by rfl⟩ : syracuseStep 1541465 = 1156099) B1156099
theorem B1246603 : Blo 682313 1246603 := bstep (se 1 (by rfl) ⟨934952, by rfl⟩ : syracuseStep 1246603 = 1869905) B1869905
theorem B1541555 : Blo 682313 1541555 := bstep (se 1 (by rfl) ⟨1156166, by rfl⟩ : syracuseStep 1541555 = 2312333) B2312333
theorem B1541591 : Blo 682313 1541591 := bstep (se 1 (by rfl) ⟨1156193, by rfl⟩ : syracuseStep 1541591 = 2312387) B2312387
theorem B2917853 : Blo 682313 2917853 := bstep (se 3 (by rfl) ⟨547097, by rfl⟩ : syracuseStep 2917853 = 1094195) B1094195
theorem B1541771 : Blo 682313 1541771 := bstep (se 1 (by rfl) ⟨1156328, by rfl⟩ : syracuseStep 1541771 = 2312657) B2312657
theorem B1541825 : Blo 682313 1541825 := bstep (se 2 (by rfl) ⟨578184, by rfl⟩ : syracuseStep 1541825 = 1156369) B1156369
theorem B1542041 : Blo 682313 1542041 := bstep (se 2 (by rfl) ⟨578265, by rfl⟩ : syracuseStep 1542041 = 1156531) B1156531
theorem B31524785 : Blo 682313 31524785 := bstep (se 2 (by rfl) ⟨11821794, by rfl⟩ : syracuseStep 31524785 = 23643589) B23643589
theorem B1542131 : Blo 682313 1542131 := bstep (se 1 (by rfl) ⟨1156598, by rfl⟩ : syracuseStep 1542131 = 2313197) B2313197
theorem B1542167 : Blo 682313 1542167 := bstep (se 1 (by rfl) ⟨1156625, by rfl⟩ : syracuseStep 1542167 = 2313251) B2313251
theorem B2197655 : Blo 682313 2197655 := bstep (se 1 (by rfl) ⟨1648241, by rfl⟩ : syracuseStep 2197655 = 3296483) B3296483
theorem B1542347 : Blo 682313 1542347 := bstep (se 1 (by rfl) ⟨1156760, by rfl⟩ : syracuseStep 1542347 = 2313521) B2313521
theorem B1542401 : Blo 682313 1542401 := bstep (se 2 (by rfl) ⟨578400, by rfl⟩ : syracuseStep 1542401 = 1156801) B1156801
theorem B1542617 : Blo 682313 1542617 := bstep (se 2 (by rfl) ⟨578481, by rfl⟩ : syracuseStep 1542617 = 1156963) B1156963
theorem B1542707 : Blo 682313 1542707 := bstep (se 1 (by rfl) ⟨1157030, by rfl⟩ : syracuseStep 1542707 = 2314061) B2314061
theorem B1542743 : Blo 682313 1542743 := bstep (se 1 (by rfl) ⟨1157057, by rfl⟩ : syracuseStep 1542743 = 2314115) B2314115
theorem B1542923 : Blo 682313 1542923 := bstep (se 1 (by rfl) ⟨1157192, by rfl⟩ : syracuseStep 1542923 = 2314385) B2314385
theorem B1542977 : Blo 682313 1542977 := bstep (se 2 (by rfl) ⟨578616, by rfl⟩ : syracuseStep 1542977 = 1157233) B1157233
theorem B2591747 : Blo 682313 2591747 := bstep (se 1 (by rfl) ⟨1943810, by rfl⟩ : syracuseStep 2591747 = 3887621) B3887621
theorem B1543193 : Blo 682313 1543193 := bstep (se 2 (by rfl) ⟨578697, by rfl⟩ : syracuseStep 1543193 = 1157395) B1157395
theorem B2198603 : Blo 682313 2198603 := bstep (se 1 (by rfl) ⟨1648952, by rfl⟩ : syracuseStep 2198603 = 3297905) B3297905
theorem B1543283 : Blo 682313 1543283 := bstep (se 1 (by rfl) ⟨1157462, by rfl⟩ : syracuseStep 1543283 = 2314925) B2314925
theorem B1543319 : Blo 682313 1543319 := bstep (se 1 (by rfl) ⟨1157489, by rfl⟩ : syracuseStep 1543319 = 2314979) B2314979
theorem B1543499 : Blo 682313 1543499 := bstep (se 1 (by rfl) ⟨1157624, by rfl⟩ : syracuseStep 1543499 = 2315249) B2315249
theorem B1543553 : Blo 682313 1543553 := bstep (se 2 (by rfl) ⟨578832, by rfl⟩ : syracuseStep 1543553 = 1157665) B1157665
theorem B1478027 : Blo 682313 1478027 := bstep (se 1 (by rfl) ⟨1108520, by rfl⟩ : syracuseStep 1478027 = 2217041) B2217041
theorem B1543769 : Blo 682313 1543769 := bstep (se 2 (by rfl) ⟨578913, by rfl⟩ : syracuseStep 1543769 = 1157827) B1157827
theorem B1543859 : Blo 682313 1543859 := bstep (se 1 (by rfl) ⟨1157894, by rfl⟩ : syracuseStep 1543859 = 2315789) B2315789
theorem B1642187 : Blo 682313 1642187 := bstep (se 1 (by rfl) ⟨1231640, by rfl⟩ : syracuseStep 1642187 = 2463281) B2463281
theorem B1543895 : Blo 682313 1543895 := bstep (se 1 (by rfl) ⟨1157921, by rfl⟩ : syracuseStep 1543895 = 2315843) B2315843
theorem B1183577 : Blo 682313 1183577 := bstep (se 2 (by rfl) ⟨443841, by rfl⟩ : syracuseStep 1183577 = 887683) B887683
theorem B1544075 : Blo 682313 1544075 := bstep (se 1 (by rfl) ⟨1158056, by rfl⟩ : syracuseStep 1544075 = 2316113) B2316113
theorem B1544129 : Blo 682313 1544129 := bstep (se 2 (by rfl) ⟨579048, by rfl⟩ : syracuseStep 1544129 = 1158097) B1158097
theorem B2920465 : Blo 682313 2920465 := bstep (se 2 (by rfl) ⟨1095174, by rfl⟩ : syracuseStep 2920465 = 2190349) B2190349
theorem B1642571 : Blo 682313 1642571 := bstep (se 1 (by rfl) ⟨1231928, by rfl⟩ : syracuseStep 1642571 = 2463857) B2463857
theorem B692311 : Blo 682313 692311 := bstep (se 1 (by rfl) ⟨519233, by rfl⟩ : syracuseStep 692311 = 1038467) B1038467
theorem B5181731 : Blo 682313 5181731 := bstep (se 1 (by rfl) ⟨3886298, by rfl⟩ : syracuseStep 5181731 = 7772597) B7772597
theorem B1151435 : Blo 682313 1151435 := bstep (se 1 (by rfl) ⟨863576, by rfl⟩ : syracuseStep 1151435 = 1727153) B1727153
theorem B1479179 : Blo 682313 1479179 := bstep (se 1 (by rfl) ⟨1109384, by rfl⟩ : syracuseStep 1479179 = 2218769) B2218769
theorem B1151563 : Blo 682313 1151563 := bstep (se 1 (by rfl) ⟨863672, by rfl⟩ : syracuseStep 1151563 = 1727345) B1727345
theorem B4690507 : Blo 682313 4690507 := bstep (se 1 (by rfl) ⟨3517880, by rfl⟩ : syracuseStep 4690507 = 7035761) B7035761
theorem B692875 : Blo 682313 692875 := bstep (se 1 (by rfl) ⟨519656, by rfl⟩ : syracuseStep 692875 = 1039313) B1039313
theorem B1151705 : Blo 682313 1151705 := bstep (se 2 (by rfl) ⟨431889, by rfl⟩ : syracuseStep 1151705 = 863779) B863779
theorem B1151833 : Blo 682313 1151833 := bstep (se 2 (by rfl) ⟨431937, by rfl⟩ : syracuseStep 1151833 = 863875) B863875
theorem B3118027 : Blo 682313 3118027 := bstep (se 1 (by rfl) ⟨2338520, by rfl⟩ : syracuseStep 3118027 = 4677041) B4677041
theorem B988249 : Blo 682313 988249 := bstep (se 2 (by rfl) ⟨370593, by rfl⟩ : syracuseStep 988249 = 741187) B741187
theorem B1152407 : Blo 682313 1152407 := bstep (se 1 (by rfl) ⟨864305, by rfl⟩ : syracuseStep 1152407 = 1728611) B1728611
theorem B1643993 : Blo 682313 1643993 := bstep (se 2 (by rfl) ⟨616497, by rfl⟩ : syracuseStep 1643993 = 1232995) B1232995
theorem B1152535 : Blo 682313 1152535 := bstep (se 1 (by rfl) ⟨864401, by rfl⟩ : syracuseStep 1152535 = 1728803) B1728803
theorem B4396589 : Blo 682313 4396589 := bstep (se 3 (by rfl) ⟨824360, by rfl⟩ : syracuseStep 4396589 = 1648721) B1648721
theorem B3905117 : Blo 682313 3905117 := bstep (se 3 (by rfl) ⟨732209, by rfl⟩ : syracuseStep 3905117 = 1464419) B1464419
theorem B5838743 : Blo 682313 5838743 := bstep (se 1 (by rfl) ⟨4379057, by rfl⟩ : syracuseStep 5838743 = 8758115) B8758115
theorem B2594861 : Blo 682313 2594861 := bstep (se 3 (by rfl) ⟨486536, by rfl⟩ : syracuseStep 2594861 = 973073) B973073
theorem B2627635 : Blo 682313 2627635 := bstep (se 1 (by rfl) ⟨1970726, by rfl⟩ : syracuseStep 2627635 = 3941453) B3941453
theorem B6330469 : Blo 682313 6330469 := bstep (se 4 (by rfl) ⟨593481, by rfl⟩ : syracuseStep 6330469 = 1186963) B1186963
theorem B1153163 : Blo 682313 1153163 := bstep (se 1 (by rfl) ⟨864872, by rfl⟩ : syracuseStep 1153163 = 1729745) B1729745
theorem B1153291 : Blo 682313 1153291 := bstep (se 1 (by rfl) ⟨864968, by rfl⟩ : syracuseStep 1153291 = 1729937) B1729937
theorem B1317235 : Blo 682313 1317235 := bstep (se 1 (by rfl) ⟨987926, by rfl⟩ : syracuseStep 1317235 = 1975853) B1975853
theorem B1153433 : Blo 682313 1153433 := bstep (se 2 (by rfl) ⟨432537, by rfl⟩ : syracuseStep 1153433 = 865075) B865075
theorem B1153561 : Blo 682313 1153561 := bstep (se 2 (by rfl) ⟨432585, by rfl⟩ : syracuseStep 1153561 = 865171) B865171
theorem B3119705 : Blo 682313 3119705 := bstep (se 2 (by rfl) ⟨1169889, by rfl⟩ : syracuseStep 3119705 = 2339779) B2339779
theorem B12622429 : Blo 682313 12622429 := bstep (se 3 (by rfl) ⟨2366705, by rfl⟩ : syracuseStep 12622429 = 4733411) B4733411
theorem B4922117 : Blo 682313 4922117 := bstep (se 4 (by rfl) ⟨461448, by rfl⟩ : syracuseStep 4922117 = 922897) B922897
theorem B2595635 : Blo 682313 2595635 := bstep (se 1 (by rfl) ⟨1946726, by rfl⟩ : syracuseStep 2595635 = 3893453) B3893453
theorem B695287 : Blo 682313 695287 := bstep (se 1 (by rfl) ⟨521465, by rfl⟩ : syracuseStep 695287 = 1042931) B1042931
theorem B1154135 : Blo 682313 1154135 := bstep (se 1 (by rfl) ⟨865601, by rfl⟩ : syracuseStep 1154135 = 1731203) B1731203
theorem B2923609 : Blo 682313 2923609 := bstep (se 2 (by rfl) ⟨1096353, by rfl⟩ : syracuseStep 2923609 = 2192707) B2192707
theorem B1154263 : Blo 682313 1154263 := bstep (se 1 (by rfl) ⟨865697, by rfl⟩ : syracuseStep 1154263 = 1731395) B1731395
theorem B3284525 : Blo 682313 3284525 := bstep (se 3 (by rfl) ⟨615848, by rfl⟩ : syracuseStep 3284525 = 1231697) B1231697
theorem B2006579 : Blo 682313 2006579 := bstep (se 1 (by rfl) ⟨1504934, by rfl⟩ : syracuseStep 2006579 = 3009869) B3009869
theorem B1023563 : Blo 682313 1023563 := bstep (se 1 (by rfl) ⟨767672, by rfl⟩ : syracuseStep 1023563 = 1535345) B1535345
theorem B1023575 : Blo 682313 1023575 := bstep (se 1 (by rfl) ⟨767681, by rfl⟩ : syracuseStep 1023575 = 1535363) B1535363
theorem B1023641 : Blo 682313 1023641 := bstep (se 2 (by rfl) ⟨383865, by rfl⟩ : syracuseStep 1023641 = 767731) B767731
theorem B2924225 : Blo 682313 2924225 := bstep (se 2 (by rfl) ⟨1096584, by rfl⟩ : syracuseStep 2924225 = 2193169) B2193169
theorem B2006731 : Blo 682313 2006731 := bstep (se 1 (by rfl) ⟨1505048, by rfl⟩ : syracuseStep 2006731 = 3010097) B3010097
theorem B6233861 : Blo 682313 6233861 := bstep (se 4 (by rfl) ⟨584424, by rfl⟩ : syracuseStep 6233861 = 1168849) B1168849
theorem B1023755 : Blo 682313 1023755 := bstep (se 1 (by rfl) ⟨767816, by rfl⟩ : syracuseStep 1023755 = 1535633) B1535633
theorem B5840657 : Blo 682313 5840657 := bstep (se 2 (by rfl) ⟨2190246, by rfl⟩ : syracuseStep 5840657 = 4380493) B4380493
theorem B1023767 : Blo 682313 1023767 := bstep (se 1 (by rfl) ⟨767825, by rfl⟩ : syracuseStep 1023767 = 1535651) B1535651
theorem B1154891 : Blo 682313 1154891 := bstep (se 1 (by rfl) ⟨866168, by rfl⟩ : syracuseStep 1154891 = 1732337) B1732337
theorem B1023833 : Blo 682313 1023833 := bstep (se 2 (by rfl) ⟨383937, by rfl⟩ : syracuseStep 1023833 = 767875) B767875
theorem B1023947 : Blo 682313 1023947 := bstep (se 1 (by rfl) ⟨767960, by rfl⟩ : syracuseStep 1023947 = 1535921) B1535921
theorem B1155019 : Blo 682313 1155019 := bstep (se 1 (by rfl) ⟨866264, by rfl⟩ : syracuseStep 1155019 = 1732529) B1732529
theorem B1023959 : Blo 682313 1023959 := bstep (se 1 (by rfl) ⟨767969, by rfl⟩ : syracuseStep 1023959 = 1535939) B1535939
theorem B3907601 : Blo 682313 3907601 := bstep (se 2 (by rfl) ⟨1465350, by rfl⟩ : syracuseStep 3907601 = 2930701) B2930701
theorem B1253399 : Blo 682313 1253399 := bstep (se 1 (by rfl) ⟨940049, by rfl⟩ : syracuseStep 1253399 = 1880099) B1880099
theorem B1024025 : Blo 682313 1024025 := bstep (se 2 (by rfl) ⟨384009, by rfl⟩ : syracuseStep 1024025 = 768019) B768019
theorem B18980939 : Blo 682313 18980939 := bstep (se 1 (by rfl) ⟨14235704, by rfl⟩ : syracuseStep 18980939 = 28471409) B28471409
theorem B1155161 : Blo 682313 1155161 := bstep (se 2 (by rfl) ⟨433185, by rfl⟩ : syracuseStep 1155161 = 866371) B866371
theorem B1024139 : Blo 682313 1024139 := bstep (se 1 (by rfl) ⟨768104, by rfl⟩ : syracuseStep 1024139 = 1536209) B1536209
theorem B1024151 : Blo 682313 1024151 := bstep (se 1 (by rfl) ⟨768113, by rfl⟩ : syracuseStep 1024151 = 1536227) B1536227
theorem B729271 : Blo 682313 729271 := bstep (se 1 (by rfl) ⟨546953, by rfl⟩ : syracuseStep 729271 = 1093907) B1093907
theorem B1024217 : Blo 682313 1024217 := bstep (se 2 (by rfl) ⟨384081, by rfl⟩ : syracuseStep 1024217 = 768163) B768163
theorem B1155289 : Blo 682313 1155289 := bstep (se 2 (by rfl) ⟨433233, by rfl⟩ : syracuseStep 1155289 = 866467) B866467
theorem B2597123 : Blo 682313 2597123 := bstep (se 1 (by rfl) ⟨1947842, by rfl⟩ : syracuseStep 2597123 = 3895685) B3895685
theorem B6562093 : Blo 682313 6562093 := bstep (se 3 (by rfl) ⟨1230392, by rfl⟩ : syracuseStep 6562093 = 2460785) B2460785
theorem B1024331 : Blo 682313 1024331 := bstep (se 1 (by rfl) ⟨768248, by rfl⟩ : syracuseStep 1024331 = 1536497) B1536497
theorem B1024343 : Blo 682313 1024343 := bstep (se 1 (by rfl) ⟨768257, by rfl⟩ : syracuseStep 1024343 = 1536515) B1536515
theorem B1024409 : Blo 682313 1024409 := bstep (se 2 (by rfl) ⟨384153, by rfl⟩ : syracuseStep 1024409 = 768307) B768307
theorem B1024523 : Blo 682313 1024523 := bstep (se 1 (by rfl) ⟨768392, by rfl⟩ : syracuseStep 1024523 = 1536785) B1536785
theorem B1024535 : Blo 682313 1024535 := bstep (se 1 (by rfl) ⟨768401, by rfl⟩ : syracuseStep 1024535 = 1536803) B1536803
theorem B4497995 : Blo 682313 4497995 := bstep (se 1 (by rfl) ⟨3373496, by rfl⟩ : syracuseStep 4497995 = 6746993) B6746993
theorem B1024601 : Blo 682313 1024601 := bstep (se 2 (by rfl) ⟨384225, by rfl⟩ : syracuseStep 1024601 = 768451) B768451
theorem B11674205 : Blo 682313 11674205 := bstep (se 3 (by rfl) ⟨2188913, by rfl⟩ : syracuseStep 11674205 = 4377827) B4377827
theorem B1024715 : Blo 682313 1024715 := bstep (se 1 (by rfl) ⟨768536, by rfl⟩ : syracuseStep 1024715 = 1537073) B1537073
theorem B2597579 : Blo 682313 2597579 := bstep (se 1 (by rfl) ⟨1948184, by rfl⟩ : syracuseStep 2597579 = 3896369) B3896369
theorem B1024727 : Blo 682313 1024727 := bstep (se 1 (by rfl) ⟨768545, by rfl⟩ : syracuseStep 1024727 = 1537091) B1537091
theorem B1155863 : Blo 682313 1155863 := bstep (se 1 (by rfl) ⟨866897, by rfl⟩ : syracuseStep 1155863 = 1733795) B1733795
theorem B1024793 : Blo 682313 1024793 := bstep (se 2 (by rfl) ⟨384297, by rfl⟩ : syracuseStep 1024793 = 768595) B768595
theorem B1123159 : Blo 682313 1123159 := bstep (se 1 (by rfl) ⟨842369, by rfl⟩ : syracuseStep 1123159 = 1684739) B1684739
theorem B1024907 : Blo 682313 1024907 := bstep (se 1 (by rfl) ⟨768680, by rfl⟩ : syracuseStep 1024907 = 1537361) B1537361
theorem B2597777 : Blo 682313 2597777 := bstep (se 2 (by rfl) ⟨974166, by rfl⟩ : syracuseStep 2597777 = 1948333) B1948333
theorem B1024919 : Blo 682313 1024919 := bstep (se 1 (by rfl) ⟨768689, by rfl⟩ : syracuseStep 1024919 = 1537379) B1537379
theorem B1155991 : Blo 682313 1155991 := bstep (se 1 (by rfl) ⟨866993, by rfl⟩ : syracuseStep 1155991 = 1733987) B1733987
theorem B2302937 : Blo 682313 2302937 := bstep (se 2 (by rfl) ⟨863601, by rfl⟩ : syracuseStep 2302937 = 1727203) B1727203
theorem B1024985 : Blo 682313 1024985 := bstep (se 2 (by rfl) ⟨384369, by rfl⟩ : syracuseStep 1024985 = 768739) B768739
theorem B730091 : Blo 682313 730091 := bstep (se 1 (by rfl) ⟨547568, by rfl⟩ : syracuseStep 730091 = 1095137) B1095137
theorem B1483777 : Blo 682313 1483777 := bstep (se 2 (by rfl) ⟨556416, by rfl⟩ : syracuseStep 1483777 = 1112833) B1112833
theorem B1025099 : Blo 682313 1025099 := bstep (se 1 (by rfl) ⟨768824, by rfl⟩ : syracuseStep 1025099 = 1537649) B1537649
theorem B1025111 : Blo 682313 1025111 := bstep (se 1 (by rfl) ⟨768833, by rfl⟩ : syracuseStep 1025111 = 1537667) B1537667
theorem B730219 : Blo 682313 730219 := bstep (se 1 (by rfl) ⟨547664, by rfl⟩ : syracuseStep 730219 = 1095329) B1095329
theorem B1025177 : Blo 682313 1025177 := bstep (se 2 (by rfl) ⟨384441, by rfl⟩ : syracuseStep 1025177 = 768883) B768883
theorem B1025291 : Blo 682313 1025291 := bstep (se 1 (by rfl) ⟨768968, by rfl⟩ : syracuseStep 1025291 = 1537937) B1537937
theorem B1025303 : Blo 682313 1025303 := bstep (se 1 (by rfl) ⟨768977, by rfl⟩ : syracuseStep 1025303 = 1537955) B1537955
theorem B1025369 : Blo 682313 1025369 := bstep (se 2 (by rfl) ⟨384513, by rfl⟩ : syracuseStep 1025369 = 769027) B769027
theorem B1025483 : Blo 682313 1025483 := bstep (se 1 (by rfl) ⟨769112, by rfl⟩ : syracuseStep 1025483 = 1538225) B1538225
theorem B1025495 : Blo 682313 1025495 := bstep (se 1 (by rfl) ⟨769121, by rfl⟩ : syracuseStep 1025495 = 1538243) B1538243
theorem B5187077 : Blo 682313 5187077 := bstep (se 4 (by rfl) ⟨486288, by rfl⟩ : syracuseStep 5187077 = 972577) B972577
theorem B1156619 : Blo 682313 1156619 := bstep (se 1 (by rfl) ⟨867464, by rfl⟩ : syracuseStep 1156619 = 1734929) B1734929
theorem B3712529 : Blo 682313 3712529 := bstep (se 2 (by rfl) ⟨1392198, by rfl⟩ : syracuseStep 3712529 = 2784397) B2784397
theorem B1025561 : Blo 682313 1025561 := bstep (se 2 (by rfl) ⟨384585, by rfl⟩ : syracuseStep 1025561 = 769171) B769171
theorem B1025675 : Blo 682313 1025675 := bstep (se 1 (by rfl) ⟨769256, by rfl⟩ : syracuseStep 1025675 = 1538513) B1538513
theorem B1156747 : Blo 682313 1156747 := bstep (se 1 (by rfl) ⟨867560, by rfl⟩ : syracuseStep 1156747 = 1735121) B1735121
theorem B2303639 : Blo 682313 2303639 := bstep (se 1 (by rfl) ⟨1727729, by rfl⟩ : syracuseStep 2303639 = 3455459) B3455459
theorem B1025687 : Blo 682313 1025687 := bstep (se 1 (by rfl) ⟨769265, by rfl⟩ : syracuseStep 1025687 = 1538531) B1538531
theorem B2598551 : Blo 682313 2598551 := bstep (se 1 (by rfl) ⟨1948913, by rfl⟩ : syracuseStep 2598551 = 3897827) B3897827
theorem B1386163 : Blo 682313 1386163 := bstep (se 1 (by rfl) ⟨1039622, by rfl⟩ : syracuseStep 1386163 = 2079245) B2079245
theorem B1025753 : Blo 682313 1025753 := bstep (se 2 (by rfl) ⟨384657, by rfl⟩ : syracuseStep 1025753 = 769315) B769315
theorem B1156889 : Blo 682313 1156889 := bstep (se 2 (by rfl) ⟨433833, by rfl⟩ : syracuseStep 1156889 = 867667) B867667
theorem B1025867 : Blo 682313 1025867 := bstep (se 1 (by rfl) ⟨769400, by rfl⟩ : syracuseStep 1025867 = 1538801) B1538801
theorem B1025879 : Blo 682313 1025879 := bstep (se 1 (by rfl) ⟨769409, by rfl⟩ : syracuseStep 1025879 = 1538819) B1538819
theorem B2598749 : Blo 682313 2598749 := bstep (se 3 (by rfl) ⟨487265, by rfl⟩ : syracuseStep 2598749 = 974531) B974531
theorem B1025945 : Blo 682313 1025945 := bstep (se 2 (by rfl) ⟨384729, by rfl⟩ : syracuseStep 1025945 = 769459) B769459
theorem B1157017 : Blo 682313 1157017 := bstep (se 2 (by rfl) ⟨433881, by rfl⟩ : syracuseStep 1157017 = 867763) B867763
theorem B1026059 : Blo 682313 1026059 := bstep (se 1 (by rfl) ⟨769544, by rfl⟩ : syracuseStep 1026059 = 1539089) B1539089
theorem B1026071 : Blo 682313 1026071 := bstep (se 1 (by rfl) ⟨769553, by rfl⟩ : syracuseStep 1026071 = 1539107) B1539107
theorem B1976395 : Blo 682313 1976395 := bstep (se 1 (by rfl) ⟨1482296, by rfl⟩ : syracuseStep 1976395 = 2964593) B2964593
theorem B1026137 : Blo 682313 1026137 := bstep (se 2 (by rfl) ⟨384801, by rfl⟩ : syracuseStep 1026137 = 769603) B769603
theorem B2926685 : Blo 682313 2926685 := bstep (se 3 (by rfl) ⟨548753, by rfl⟩ : syracuseStep 2926685 = 1097507) B1097507
theorem B2304179 : Blo 682313 2304179 := bstep (se 1 (by rfl) ⟨1728134, by rfl⟩ : syracuseStep 2304179 = 3456269) B3456269
theorem B1026251 : Blo 682313 1026251 := bstep (se 1 (by rfl) ⟨769688, by rfl⟩ : syracuseStep 1026251 = 1539377) B1539377
theorem B1026263 : Blo 682313 1026263 := bstep (se 1 (by rfl) ⟨769697, by rfl⟩ : syracuseStep 1026263 = 1539395) B1539395
theorem B1026329 : Blo 682313 1026329 := bstep (se 2 (by rfl) ⟨384873, by rfl⟩ : syracuseStep 1026329 = 769747) B769747
theorem B1026443 : Blo 682313 1026443 := bstep (se 1 (by rfl) ⟨769832, by rfl⟩ : syracuseStep 1026443 = 1539665) B1539665
theorem B1943959 : Blo 682313 1943959 := bstep (se 1 (by rfl) ⟨1457969, by rfl⟩ : syracuseStep 1943959 = 2915939) B2915939
theorem B1026455 : Blo 682313 1026455 := bstep (se 1 (by rfl) ⟨769841, by rfl⟩ : syracuseStep 1026455 = 1539683) B1539683
theorem B2304449 : Blo 682313 2304449 := bstep (se 2 (by rfl) ⟨864168, by rfl⟩ : syracuseStep 2304449 = 1728337) B1728337
theorem B1157591 : Blo 682313 1157591 := bstep (se 1 (by rfl) ⟨868193, by rfl⟩ : syracuseStep 1157591 = 1736387) B1736387
theorem B1026521 : Blo 682313 1026521 := bstep (se 2 (by rfl) ⟨384945, by rfl⟩ : syracuseStep 1026521 = 769891) B769891
theorem B1026635 : Blo 682313 1026635 := bstep (se 1 (by rfl) ⟨769976, by rfl⟩ : syracuseStep 1026635 = 1539953) B1539953
theorem B1026647 : Blo 682313 1026647 := bstep (se 1 (by rfl) ⟨769985, by rfl⟩ : syracuseStep 1026647 = 1539971) B1539971
theorem B1157719 : Blo 682313 1157719 := bstep (se 1 (by rfl) ⟨868289, by rfl⟩ : syracuseStep 1157719 = 1736579) B1736579
theorem B1026713 : Blo 682313 1026713 := bstep (se 2 (by rfl) ⟨385017, by rfl⟩ : syracuseStep 1026713 = 770035) B770035
theorem B1026827 : Blo 682313 1026827 := bstep (se 1 (by rfl) ⟨770120, by rfl⟩ : syracuseStep 1026827 = 1540241) B1540241
theorem B1026839 : Blo 682313 1026839 := bstep (se 1 (by rfl) ⟨770129, by rfl⟩ : syracuseStep 1026839 = 1540259) B1540259
theorem B1026905 : Blo 682313 1026905 := bstep (se 2 (by rfl) ⟨385089, by rfl⟩ : syracuseStep 1026905 = 770179) B770179
theorem B1027019 : Blo 682313 1027019 := bstep (se 1 (by rfl) ⟨770264, by rfl⟩ : syracuseStep 1027019 = 1540529) B1540529
theorem B1027031 : Blo 682313 1027031 := bstep (se 1 (by rfl) ⟨770273, by rfl⟩ : syracuseStep 1027031 = 1540547) B1540547
theorem B2304989 : Blo 682313 2304989 := bstep (se 3 (by rfl) ⟨432185, by rfl⟩ : syracuseStep 2304989 = 864371) B864371
theorem B1027097 : Blo 682313 1027097 := bstep (se 2 (by rfl) ⟨385161, by rfl⟩ : syracuseStep 1027097 = 770323) B770323
theorem B1027211 : Blo 682313 1027211 := bstep (se 1 (by rfl) ⟨770408, by rfl⟩ : syracuseStep 1027211 = 1540817) B1540817
theorem B3288215 : Blo 682313 3288215 := bstep (se 1 (by rfl) ⟨2466161, by rfl⟩ : syracuseStep 3288215 = 4932323) B4932323
theorem B1027223 : Blo 682313 1027223 := bstep (se 1 (by rfl) ⟨770417, by rfl⟩ : syracuseStep 1027223 = 1540835) B1540835
theorem B1387735 : Blo 682313 1387735 := bstep (se 1 (by rfl) ⟨1040801, by rfl⟩ : syracuseStep 1387735 = 2081603) B2081603
theorem B1027289 : Blo 682313 1027289 := bstep (se 2 (by rfl) ⟨385233, by rfl⟩ : syracuseStep 1027289 = 770467) B770467
theorem B1027403 : Blo 682313 1027403 := bstep (se 1 (by rfl) ⟨770552, by rfl⟩ : syracuseStep 1027403 = 1541105) B1541105
theorem B1027415 : Blo 682313 1027415 := bstep (se 1 (by rfl) ⟨770561, by rfl⟩ : syracuseStep 1027415 = 1541123) B1541123
theorem B1027481 : Blo 682313 1027481 := bstep (se 2 (by rfl) ⟨385305, by rfl⟩ : syracuseStep 1027481 = 770611) B770611
theorem B1027595 : Blo 682313 1027595 := bstep (se 1 (by rfl) ⟨770696, by rfl⟩ : syracuseStep 1027595 = 1541393) B1541393
theorem B1027607 : Blo 682313 1027607 := bstep (se 1 (by rfl) ⟨770705, by rfl⟩ : syracuseStep 1027607 = 1541411) B1541411
theorem B1027673 : Blo 682313 1027673 := bstep (se 2 (by rfl) ⟨385377, by rfl⟩ : syracuseStep 1027673 = 770755) B770755
theorem B12496477 : Blo 682313 12496477 := bstep (se 3 (by rfl) ⟨2343089, by rfl⟩ : syracuseStep 12496477 = 4686179) B4686179
theorem B1945291 : Blo 682313 1945291 := bstep (se 1 (by rfl) ⟨1458968, by rfl⟩ : syracuseStep 1945291 = 2917937) B2917937
theorem B1027787 : Blo 682313 1027787 := bstep (se 1 (by rfl) ⟨770840, by rfl⟩ : syracuseStep 1027787 = 1541681) B1541681
theorem B1027799 : Blo 682313 1027799 := bstep (se 1 (by rfl) ⟨770849, by rfl⟩ : syracuseStep 1027799 = 1541699) B1541699
theorem B2600707 : Blo 682313 2600707 := bstep (se 1 (by rfl) ⟨1950530, by rfl⟩ : syracuseStep 2600707 = 3901061) B3901061
theorem B1027865 : Blo 682313 1027865 := bstep (se 2 (by rfl) ⟨385449, by rfl⟩ : syracuseStep 1027865 = 770899) B770899
theorem B1388353 : Blo 682313 1388353 := bstep (se 2 (by rfl) ⟨520632, by rfl⟩ : syracuseStep 1388353 = 1041265) B1041265
theorem B5189507 : Blo 682313 5189507 := bstep (se 1 (by rfl) ⟨3892130, by rfl⟩ : syracuseStep 5189507 = 7784261) B7784261
theorem B1027979 : Blo 682313 1027979 := bstep (se 1 (by rfl) ⟨770984, by rfl⟩ : syracuseStep 1027979 = 1541969) B1541969
theorem B1027991 : Blo 682313 1027991 := bstep (se 1 (by rfl) ⟨770993, by rfl⟩ : syracuseStep 1027991 = 1541987) B1541987
theorem B1028057 : Blo 682313 1028057 := bstep (se 2 (by rfl) ⟨385521, by rfl⟩ : syracuseStep 1028057 = 771043) B771043
theorem B1945565 : Blo 682313 1945565 := bstep (se 3 (by rfl) ⟨364793, by rfl⟩ : syracuseStep 1945565 = 729587) B729587
theorem B12496913 : Blo 682313 12496913 := bstep (se 2 (by rfl) ⟨4686342, by rfl⟩ : syracuseStep 12496913 = 9372685) B9372685
theorem B2601011 : Blo 682313 2601011 := bstep (se 1 (by rfl) ⟨1950758, by rfl⟩ : syracuseStep 2601011 = 3901517) B3901517
theorem B2306123 : Blo 682313 2306123 := bstep (se 1 (by rfl) ⟨1729592, by rfl⟩ : syracuseStep 2306123 = 3459185) B3459185
theorem B1028171 : Blo 682313 1028171 := bstep (se 1 (by rfl) ⟨771128, by rfl⟩ : syracuseStep 1028171 = 1542257) B1542257
theorem B1028183 : Blo 682313 1028183 := bstep (se 1 (by rfl) ⟨771137, by rfl⟩ : syracuseStep 1028183 = 1542275) B1542275
theorem B1028249 : Blo 682313 1028249 := bstep (se 2 (by rfl) ⟨385593, by rfl⟩ : syracuseStep 1028249 = 771187) B771187
theorem B864523 : Blo 682313 864523 := bstep (se 1 (by rfl) ⟨648392, by rfl⟩ : syracuseStep 864523 = 1296785) B1296785
theorem B1028363 : Blo 682313 1028363 := bstep (se 1 (by rfl) ⟨771272, by rfl⟩ : syracuseStep 1028363 = 1542545) B1542545
theorem B1028375 : Blo 682313 1028375 := bstep (se 1 (by rfl) ⟨771281, by rfl⟩ : syracuseStep 1028375 = 1542563) B1542563
theorem B1945907 : Blo 682313 1945907 := bstep (se 1 (by rfl) ⟨1459430, by rfl⟩ : syracuseStep 1945907 = 2918861) B2918861
theorem B3289409 : Blo 682313 3289409 := bstep (se 2 (by rfl) ⟨1233528, by rfl⟩ : syracuseStep 3289409 = 2467057) B2467057
theorem B2306393 : Blo 682313 2306393 := bstep (se 2 (by rfl) ⟨864897, by rfl⟩ : syracuseStep 2306393 = 1729795) B1729795
theorem B1028441 : Blo 682313 1028441 := bstep (se 2 (by rfl) ⟨385665, by rfl⟩ : syracuseStep 1028441 = 771331) B771331
theorem B1388993 : Blo 682313 1388993 := bstep (se 2 (by rfl) ⟨520872, by rfl⟩ : syracuseStep 1388993 = 1041745) B1041745
theorem B1028555 : Blo 682313 1028555 := bstep (se 1 (by rfl) ⟨771416, by rfl⟩ : syracuseStep 1028555 = 1542833) B1542833
theorem B1028567 : Blo 682313 1028567 := bstep (se 1 (by rfl) ⟨771425, by rfl⟩ : syracuseStep 1028567 = 1542851) B1542851
theorem B1389017 : Blo 682313 1389017 := bstep (se 2 (by rfl) ⟨520881, by rfl⟩ : syracuseStep 1389017 = 1041763) B1041763
theorem B1028633 : Blo 682313 1028633 := bstep (se 2 (by rfl) ⟨385737, by rfl⟩ : syracuseStep 1028633 = 771475) B771475
theorem B2929283 : Blo 682313 2929283 := bstep (se 1 (by rfl) ⟨2196962, by rfl⟩ : syracuseStep 2929283 = 4393925) B4393925
theorem B1028747 : Blo 682313 1028747 := bstep (se 1 (by rfl) ⟨771560, by rfl⟩ : syracuseStep 1028747 = 1543121) B1543121
theorem B1028759 : Blo 682313 1028759 := bstep (se 1 (by rfl) ⟨771569, by rfl⟩ : syracuseStep 1028759 = 1543139) B1543139
theorem B2601665 : Blo 682313 2601665 := bstep (se 2 (by rfl) ⟨975624, by rfl⟩ : syracuseStep 2601665 = 1951249) B1951249
theorem B1028825 : Blo 682313 1028825 := bstep (se 2 (by rfl) ⟨385809, by rfl⟩ : syracuseStep 1028825 = 771619) B771619
theorem B1422155 : Blo 682313 1422155 := bstep (se 1 (by rfl) ⟨1066616, by rfl⟩ : syracuseStep 1422155 = 2133233) B2133233
theorem B1028939 : Blo 682313 1028939 := bstep (se 1 (by rfl) ⟨771704, by rfl⟩ : syracuseStep 1028939 = 1543409) B1543409
theorem B1028951 : Blo 682313 1028951 := bstep (se 1 (by rfl) ⟨771713, by rfl⟩ : syracuseStep 1028951 = 1543427) B1543427
theorem B3126109 : Blo 682313 3126109 := bstep (se 3 (by rfl) ⟨586145, by rfl⟩ : syracuseStep 3126109 = 1172291) B1172291
theorem B1029017 : Blo 682313 1029017 := bstep (se 2 (by rfl) ⟨385881, by rfl⟩ : syracuseStep 1029017 = 771763) B771763
theorem B17544113 : Blo 682313 17544113 := bstep (se 2 (by rfl) ⟨6579042, by rfl⟩ : syracuseStep 17544113 = 13158085) B13158085
theorem B1029131 : Blo 682313 1029131 := bstep (se 1 (by rfl) ⟨771848, by rfl⟩ : syracuseStep 1029131 = 1543697) B1543697
theorem B2307095 : Blo 682313 2307095 := bstep (se 1 (by rfl) ⟨1730321, by rfl⟩ : syracuseStep 2307095 = 3460643) B3460643
theorem B1029143 : Blo 682313 1029143 := bstep (se 1 (by rfl) ⟨771857, by rfl⟩ : syracuseStep 1029143 = 1543715) B1543715
theorem B1029209 : Blo 682313 1029209 := bstep (se 2 (by rfl) ⟨385953, by rfl⟩ : syracuseStep 1029209 = 771907) B771907
theorem B5256371 : Blo 682313 5256371 := bstep (se 1 (by rfl) ⟨3942278, by rfl⟩ : syracuseStep 5256371 = 7884557) B7884557
theorem B3290291 : Blo 682313 3290291 := bstep (se 1 (by rfl) ⟨2467718, by rfl⟩ : syracuseStep 3290291 = 4935437) B4935437
theorem B1029323 : Blo 682313 1029323 := bstep (se 1 (by rfl) ⟨771992, by rfl⟩ : syracuseStep 1029323 = 1543985) B1543985
theorem B865495 : Blo 682313 865495 := bstep (se 1 (by rfl) ⟨649121, by rfl⟩ : syracuseStep 865495 = 1298243) B1298243
theorem B1029335 : Blo 682313 1029335 := bstep (se 1 (by rfl) ⟨772001, by rfl⟩ : syracuseStep 1029335 = 1544003) B1544003
theorem B1029401 : Blo 682313 1029401 := bstep (se 2 (by rfl) ⟨386025, by rfl⟩ : syracuseStep 1029401 = 772051) B772051
theorem B7386547 : Blo 682313 7386547 := bstep (se 1 (by rfl) ⟨5539910, by rfl⟩ : syracuseStep 7386547 = 11079821) B11079821
theorem B1390103 : Blo 682313 1390103 := bstep (se 1 (by rfl) ⟨1042577, by rfl⟩ : syracuseStep 1390103 = 2085155) B2085155
theorem B2307635 : Blo 682313 2307635 := bstep (se 1 (by rfl) ⟨1730726, by rfl⟩ : syracuseStep 2307635 = 3461453) B3461453
theorem B767659 : Blo 682313 767659 := bstep (se 1 (by rfl) ⟨575744, by rfl⟩ : syracuseStep 767659 = 1151489) B1151489
theorem B767767 : Blo 682313 767767 := bstep (se 1 (by rfl) ⟨575825, by rfl⟩ : syracuseStep 767767 = 1151651) B1151651
theorem B2307905 : Blo 682313 2307905 := bstep (se 2 (by rfl) ⟨865464, by rfl⟩ : syracuseStep 2307905 = 1730929) B1730929
theorem B2602925 : Blo 682313 2602925 := bstep (se 3 (by rfl) ⟨488048, by rfl⟩ : syracuseStep 2602925 = 976097) B976097
theorem B767947 : Blo 682313 767947 := bstep (se 1 (by rfl) ⟨575960, by rfl⟩ : syracuseStep 767947 = 1151921) B1151921
theorem B2602955 : Blo 682313 2602955 := bstep (se 1 (by rfl) ⟨1952216, by rfl⟩ : syracuseStep 2602955 = 3904433) B3904433
theorem B866315 : Blo 682313 866315 := bstep (se 1 (by rfl) ⟨649736, by rfl⟩ : syracuseStep 866315 = 1299473) B1299473
theorem B768055 : Blo 682313 768055 := bstep (se 1 (by rfl) ⟨576041, by rfl⟩ : syracuseStep 768055 = 1152083) B1152083
theorem B768235 : Blo 682313 768235 := bstep (se 1 (by rfl) ⟨576176, by rfl⟩ : syracuseStep 768235 = 1152353) B1152353
theorem B7813421 : Blo 682313 7813421 := bstep (se 3 (by rfl) ⟨1465016, by rfl⟩ : syracuseStep 7813421 = 2930033) B2930033
theorem B3455297 : Blo 682313 3455297 := bstep (se 2 (by rfl) ⟨1295736, by rfl⟩ : syracuseStep 3455297 = 2591473) B2591473
theorem B1947979 : Blo 682313 1947979 := bstep (se 1 (by rfl) ⟨1460984, by rfl⟩ : syracuseStep 1947979 = 2921969) B2921969
theorem B768343 : Blo 682313 768343 := bstep (se 1 (by rfl) ⟨576257, by rfl⟩ : syracuseStep 768343 = 1152515) B1152515
theorem B2308445 : Blo 682313 2308445 := bstep (se 3 (by rfl) ⟨432833, by rfl⟩ : syracuseStep 2308445 = 865667) B865667
theorem B768523 : Blo 682313 768523 := bstep (se 1 (by rfl) ⟨576392, by rfl⟩ : syracuseStep 768523 = 1152785) B1152785
theorem B2406935 : Blo 682313 2406935 := bstep (se 1 (by rfl) ⟨1805201, by rfl⟩ : syracuseStep 2406935 = 3610403) B3610403
theorem B2603609 : Blo 682313 2603609 := bstep (se 2 (by rfl) ⟨976353, by rfl⟩ : syracuseStep 2603609 = 1952707) B1952707
theorem B768631 : Blo 682313 768631 := bstep (se 1 (by rfl) ⟨576473, by rfl⟩ : syracuseStep 768631 = 1152947) B1152947
theorem B834187 : Blo 682313 834187 := bstep (se 1 (by rfl) ⟨625640, by rfl⟩ : syracuseStep 834187 = 1251281) B1251281
theorem B867019 : Blo 682313 867019 := bstep (se 1 (by rfl) ⟨650264, by rfl⟩ : syracuseStep 867019 = 1300529) B1300529
theorem B94878485 : Blo 682313 94878485 := bstep (se 6 (by rfl) ⟨2223714, by rfl⟩ : syracuseStep 94878485 = 4447429) B4447429
theorem B768811 : Blo 682313 768811 := bstep (se 1 (by rfl) ⟨576608, by rfl⟩ : syracuseStep 768811 = 1153217) B1153217
theorem B1948481 : Blo 682313 1948481 := bstep (se 2 (by rfl) ⟨730680, by rfl⟩ : syracuseStep 1948481 = 1461361) B1461361
theorem B768919 : Blo 682313 768919 := bstep (se 1 (by rfl) ⟨576689, by rfl⟩ : syracuseStep 768919 = 1153379) B1153379
theorem B4995991 : Blo 682313 4995991 := bstep (se 1 (by rfl) ⟨3746993, by rfl⟩ : syracuseStep 4995991 = 7493987) B7493987
theorem B2603927 : Blo 682313 2603927 := bstep (se 1 (by rfl) ⟨1952945, by rfl⟩ : syracuseStep 2603927 = 3905891) B3905891
theorem B867287 : Blo 682313 867287 := bstep (se 1 (by rfl) ⟨650465, by rfl⟩ : syracuseStep 867287 = 1300931) B1300931
theorem B11713571 : Blo 682313 11713571 := bstep (se 1 (by rfl) ⟨8785178, by rfl⟩ : syracuseStep 11713571 = 17570357) B17570357
theorem B769099 : Blo 682313 769099 := bstep (se 1 (by rfl) ⟨576824, by rfl⟩ : syracuseStep 769099 = 1153649) B1153649
theorem B1948823 : Blo 682313 1948823 := bstep (se 1 (by rfl) ⟨1461617, by rfl⟩ : syracuseStep 1948823 = 2923235) B2923235
theorem B2473139 : Blo 682313 2473139 := bstep (se 1 (by rfl) ⟨1854854, by rfl⟩ : syracuseStep 2473139 = 3709709) B3709709
theorem B769207 : Blo 682313 769207 := bstep (se 1 (by rfl) ⟨576905, by rfl⟩ : syracuseStep 769207 = 1153811) B1153811
theorem B5192909 : Blo 682313 5192909 := bstep (se 3 (by rfl) ⟨973670, by rfl⟩ : syracuseStep 5192909 = 1947341) B1947341
theorem B769387 : Blo 682313 769387 := bstep (se 1 (by rfl) ⟨577040, by rfl⟩ : syracuseStep 769387 = 1154081) B1154081
theorem B2309579 : Blo 682313 2309579 := bstep (se 1 (by rfl) ⟨1732184, by rfl⟩ : syracuseStep 2309579 = 3464369) B3464369
theorem B769495 : Blo 682313 769495 := bstep (se 1 (by rfl) ⟨577121, by rfl⟩ : syracuseStep 769495 = 1154243) B1154243
theorem B4931117 : Blo 682313 4931117 := bstep (se 3 (by rfl) ⟨924584, by rfl⟩ : syracuseStep 4931117 = 1849169) B1849169
theorem B2604595 : Blo 682313 2604595 := bstep (se 1 (by rfl) ⟨1953446, by rfl⟩ : syracuseStep 2604595 = 3906893) B3906893
theorem B769675 : Blo 682313 769675 := bstep (se 1 (by rfl) ⟨577256, by rfl⟩ : syracuseStep 769675 = 1154513) B1154513
theorem B867991 : Blo 682313 867991 := bstep (se 1 (by rfl) ⟨650993, by rfl⟩ : syracuseStep 867991 = 1301987) B1301987
theorem B5193395 : Blo 682313 5193395 := bstep (se 1 (by rfl) ⟨3895046, by rfl⟩ : syracuseStep 5193395 = 7790093) B7790093
theorem B2309849 : Blo 682313 2309849 := bstep (se 2 (by rfl) ⟨866193, by rfl⟩ : syracuseStep 2309849 = 1732387) B1732387
theorem B769783 : Blo 682313 769783 := bstep (se 1 (by rfl) ⟨577337, by rfl⟩ : syracuseStep 769783 = 1154675) B1154675
theorem B1425163 : Blo 682313 1425163 := bstep (se 1 (by rfl) ⟨1068872, by rfl⟩ : syracuseStep 1425163 = 2137745) B2137745
theorem B1457995 : Blo 682313 1457995 := bstep (se 1 (by rfl) ⟨1093496, by rfl⟩ : syracuseStep 1457995 = 2186993) B2186993
theorem B769963 : Blo 682313 769963 := bstep (se 1 (by rfl) ⟨577472, by rfl⟩ : syracuseStep 769963 = 1154945) B1154945
theorem B1097687 : Blo 682313 1097687 := bstep (se 1 (by rfl) ⟨823265, by rfl⟩ : syracuseStep 1097687 = 1646531) B1646531
theorem B770071 : Blo 682313 770071 := bstep (se 1 (by rfl) ⟨577553, by rfl⟩ : syracuseStep 770071 = 1155107) B1155107
theorem B1458251 : Blo 682313 1458251 := bstep (se 1 (by rfl) ⟨1093688, by rfl⟩ : syracuseStep 1458251 = 2187377) B2187377
theorem B1097815 : Blo 682313 1097815 := bstep (se 1 (by rfl) ⟨823361, by rfl⟩ : syracuseStep 1097815 = 1646723) B1646723
theorem B2080961 : Blo 682313 2080961 := bstep (se 2 (by rfl) ⟨780360, by rfl⟩ : syracuseStep 2080961 = 1560721) B1560721
theorem B770251 : Blo 682313 770251 := bstep (se 1 (by rfl) ⟨577688, by rfl⟩ : syracuseStep 770251 = 1155377) B1155377
theorem B3457241 : Blo 682313 3457241 := bstep (se 2 (by rfl) ⟨1296465, by rfl⟩ : syracuseStep 3457241 = 2592931) B2592931
theorem B770359 : Blo 682313 770359 := bstep (se 1 (by rfl) ⟨577769, by rfl⟩ : syracuseStep 770359 = 1155539) B1155539
theorem B2310551 : Blo 682313 2310551 := bstep (se 1 (by rfl) ⟨1732913, by rfl⟩ : syracuseStep 2310551 = 3465827) B3465827
theorem B1851827 : Blo 682313 1851827 := bstep (se 1 (by rfl) ⟨1388870, by rfl⟩ : syracuseStep 1851827 = 2777741) B2777741
theorem B3129779 : Blo 682313 3129779 := bstep (se 1 (by rfl) ⟨2347334, by rfl⟩ : syracuseStep 3129779 = 4694669) B4694669
theorem B1098199 : Blo 682313 1098199 := bstep (se 1 (by rfl) ⟨823649, by rfl⟩ : syracuseStep 1098199 = 1647299) B1647299
theorem B770539 : Blo 682313 770539 := bstep (se 1 (by rfl) ⟨577904, by rfl⟩ : syracuseStep 770539 = 1155809) B1155809
theorem B3293713 : Blo 682313 3293713 := bstep (se 2 (by rfl) ⟨1235142, by rfl⟩ : syracuseStep 3293713 = 2470285) B2470285
theorem B770647 : Blo 682313 770647 := bstep (se 1 (by rfl) ⟨577985, by rfl⟩ : syracuseStep 770647 = 1155971) B1155971
theorem B1098455 : Blo 682313 1098455 := bstep (se 1 (by rfl) ⟨823841, by rfl⟩ : syracuseStep 1098455 = 1647683) B1647683
theorem B4735705 : Blo 682313 4735705 := bstep (se 2 (by rfl) ⟨1775889, by rfl⟩ : syracuseStep 4735705 = 3551779) B3551779
theorem B770827 : Blo 682313 770827 := bstep (se 1 (by rfl) ⟨578120, by rfl⟩ : syracuseStep 770827 = 1156241) B1156241
theorem B2605841 : Blo 682313 2605841 := bstep (se 2 (by rfl) ⟨977190, by rfl⟩ : syracuseStep 2605841 = 1954381) B1954381
theorem B1557299 : Blo 682313 1557299 := bstep (se 1 (by rfl) ⟨1167974, by rfl⟩ : syracuseStep 1557299 = 2335949) B2335949
theorem B770935 : Blo 682313 770935 := bstep (se 1 (by rfl) ⟨578201, by rfl⟩ : syracuseStep 770935 = 1156403) B1156403
theorem B2311091 : Blo 682313 2311091 := bstep (se 1 (by rfl) ⟨1733318, by rfl⟩ : syracuseStep 2311091 = 3466637) B3466637
theorem B1459225 : Blo 682313 1459225 := bstep (se 2 (by rfl) ⟨547209, by rfl⟩ : syracuseStep 1459225 = 1094419) B1094419
theorem B771115 : Blo 682313 771115 := bstep (se 1 (by rfl) ⟨578336, by rfl⟩ : syracuseStep 771115 = 1156673) B1156673
theorem B5194853 : Blo 682313 5194853 := bstep (se 4 (by rfl) ⟨487017, by rfl⟩ : syracuseStep 5194853 = 974035) B974035
theorem B771223 : Blo 682313 771223 := bstep (se 1 (by rfl) ⟨578417, by rfl⟩ : syracuseStep 771223 = 1156835) B1156835
theorem B1459379 : Blo 682313 1459379 := bstep (se 1 (by rfl) ⟨1094534, by rfl⟩ : syracuseStep 1459379 = 2189069) B2189069
theorem B2311361 : Blo 682313 2311361 := bstep (se 2 (by rfl) ⟨866760, by rfl⟩ : syracuseStep 2311361 = 1733521) B1733521
theorem B1950941 : Blo 682313 1950941 := bstep (se 3 (by rfl) ⟨365801, by rfl⟩ : syracuseStep 1950941 = 731603) B731603
theorem B2344157 : Blo 682313 2344157 := bstep (se 3 (by rfl) ⟨439529, by rfl⟩ : syracuseStep 2344157 = 879059) B879059
theorem B1099019 : Blo 682313 1099019 := bstep (se 1 (by rfl) ⟨824264, by rfl⟩ : syracuseStep 1099019 = 1648529) B1648529
theorem B771403 : Blo 682313 771403 := bstep (se 1 (by rfl) ⟨578552, by rfl⟩ : syracuseStep 771403 = 1157105) B1157105
theorem B1230169 : Blo 682313 1230169 := bstep (se 2 (by rfl) ⟨461313, by rfl⟩ : syracuseStep 1230169 = 922627) B922627
theorem B1295767 : Blo 682313 1295767 := bstep (se 1 (by rfl) ⟨971825, by rfl⟩ : syracuseStep 1295767 = 1943651) B1943651
theorem B771511 : Blo 682313 771511 := bstep (se 1 (by rfl) ⟨578633, by rfl⟩ : syracuseStep 771511 = 1157267) B1157267
theorem B1558027 : Blo 682313 1558027 := bstep (se 1 (by rfl) ⟨1168520, by rfl⟩ : syracuseStep 1558027 = 2337041) B2337041
theorem B1951283 : Blo 682313 1951283 := bstep (se 1 (by rfl) ⟨1463462, by rfl⟩ : syracuseStep 1951283 = 2926925) B2926925
theorem B5195339 : Blo 682313 5195339 := bstep (se 1 (by rfl) ⟨3896504, by rfl⟩ : syracuseStep 5195339 = 7793009) B7793009
theorem B771691 : Blo 682313 771691 := bstep (se 1 (by rfl) ⟨578768, by rfl⟩ : syracuseStep 771691 = 1157537) B1157537
theorem B1459891 : Blo 682313 1459891 := bstep (se 1 (by rfl) ⟨1094918, by rfl⟩ : syracuseStep 1459891 = 2189837) B2189837
theorem B771799 : Blo 682313 771799 := bstep (se 1 (by rfl) ⟨578849, by rfl⟩ : syracuseStep 771799 = 1157699) B1157699
theorem B2311901 : Blo 682313 2311901 := bstep (se 3 (by rfl) ⟨433481, by rfl⟩ : syracuseStep 2311901 = 866963) B866963
theorem B3458861 : Blo 682313 3458861 := bstep (se 3 (by rfl) ⟨648536, by rfl⟩ : syracuseStep 3458861 = 1297073) B1297073
theorem B771979 : Blo 682313 771979 := bstep (se 1 (by rfl) ⟨578984, by rfl⟩ : syracuseStep 771979 = 1157969) B1157969
theorem B772087 : Blo 682313 772087 := bstep (se 1 (by rfl) ⟨579065, by rfl⟩ : syracuseStep 772087 = 1158131) B1158131
theorem B1296587 : Blo 682313 1296587 := bstep (se 1 (by rfl) ⟨972440, by rfl⟩ : syracuseStep 1296587 = 1944881) B1944881
theorem B1296641 : Blo 682313 1296641 := bstep (se 2 (by rfl) ⟨486240, by rfl⟩ : syracuseStep 1296641 = 972481) B972481
theorem B12798253 : Blo 682313 12798253 := bstep (se 3 (by rfl) ⟨2399672, by rfl⟩ : syracuseStep 12798253 = 4799345) B4799345
theorem B1460567 : Blo 682313 1460567 := bstep (se 1 (by rfl) ⟨1095425, by rfl⟩ : syracuseStep 1460567 = 2190851) B2190851
theorem B1460609 : Blo 682313 1460609 := bstep (se 2 (by rfl) ⟨547728, by rfl⟩ : syracuseStep 1460609 = 1095457) B1095457
theorem B1231553 : Blo 682313 1231553 := bstep (se 2 (by rfl) ⟨461832, by rfl⟩ : syracuseStep 1231553 = 923665) B923665
theorem B5851865 : Blo 682313 5851865 := bstep (se 2 (by rfl) ⟨2194449, by rfl⟩ : syracuseStep 5851865 = 4388899) B4388899
theorem B19942129 : Blo 682313 19942129 := bstep (se 2 (by rfl) ⟨7478298, by rfl⟩ : syracuseStep 19942129 = 14956597) B14956597
theorem B2313035 : Blo 682313 2313035 := bstep (se 1 (by rfl) ⟨1734776, by rfl⟩ : syracuseStep 2313035 = 3469553) B3469553
theorem B2083915 : Blo 682313 2083915 := bstep (se 1 (by rfl) ⟨1562936, by rfl⟩ : syracuseStep 2083915 = 3125873) B3125873
theorem B2313305 : Blo 682313 2313305 := bstep (se 2 (by rfl) ⟨867489, by rfl⟩ : syracuseStep 2313305 = 1734979) B1734979
theorem B937099 : Blo 682313 937099 := bstep (se 1 (by rfl) ⟨702824, by rfl⟩ : syracuseStep 937099 = 1405649) B1405649
theorem B1297559 : Blo 682313 1297559 := bstep (se 1 (by rfl) ⟨973169, by rfl⟩ : syracuseStep 1297559 = 1946339) B1946339
theorem B17517869 : Blo 682313 17517869 := bstep (se 3 (by rfl) ⟨3284600, by rfl⟩ : syracuseStep 17517869 = 6569201) B6569201
theorem B1559873 : Blo 682313 1559873 := bstep (se 2 (by rfl) ⟨584952, by rfl⟩ : syracuseStep 1559873 = 1169905) B1169905
theorem B1756723 : Blo 682313 1756723 := bstep (se 1 (by rfl) ⟨1317542, by rfl⟩ : syracuseStep 1756723 = 2635085) B2635085
theorem B6245981 : Blo 682313 6245981 := bstep (se 3 (by rfl) ⟨1171121, by rfl⟩ : syracuseStep 6245981 = 2342243) B2342243
theorem B1298099 : Blo 682313 1298099 := bstep (se 1 (by rfl) ⟨973574, by rfl⟩ : syracuseStep 1298099 = 1947149) B1947149
theorem B741079 : Blo 682313 741079 := bstep (se 1 (by rfl) ⟨555809, by rfl⟩ : syracuseStep 741079 = 1111619) B1111619
theorem B2314007 : Blo 682313 2314007 := bstep (se 1 (by rfl) ⟨1735505, by rfl⟩ : syracuseStep 2314007 = 3471011) B3471011
theorem B1953629 : Blo 682313 1953629 := bstep (se 3 (by rfl) ⟨366305, by rfl⟩ : syracuseStep 1953629 = 732611) B732611
theorem B1953857 : Blo 682313 1953857 := bstep (se 2 (by rfl) ⟨732696, by rfl⟩ : syracuseStep 1953857 = 1465393) B1465393
theorem B1298585 : Blo 682313 1298585 := bstep (se 2 (by rfl) ⟨486969, by rfl⟩ : syracuseStep 1298585 = 973939) B973939
theorem B2314547 : Blo 682313 2314547 := bstep (se 1 (by rfl) ⟨1735910, by rfl⟩ : syracuseStep 2314547 = 3471821) B3471821
theorem B5853505 : Blo 682313 5853505 := bstep (se 2 (by rfl) ⟨2195064, by rfl⟩ : syracuseStep 5853505 = 4390129) B4390129
theorem B1954199 : Blo 682313 1954199 := bstep (se 1 (by rfl) ⟨1465649, by rfl⟩ : syracuseStep 1954199 = 2931299) B2931299
theorem B3691025 : Blo 682313 3691025 := bstep (se 2 (by rfl) ⟨1384134, by rfl⟩ : syracuseStep 3691025 = 2768269) B2768269
theorem B2314817 : Blo 682313 2314817 := bstep (se 2 (by rfl) ⟨868056, by rfl⟩ : syracuseStep 2314817 = 1736113) B1736113
theorem B5558989 : Blo 682313 5558989 := bstep (se 3 (by rfl) ⟨1042310, by rfl⟩ : syracuseStep 5558989 = 2084621) B2084621
theorem B1233623 : Blo 682313 1233623 := bstep (se 1 (by rfl) ⟨925217, by rfl⟩ : syracuseStep 1233623 = 1850435) B1850435
theorem B2773835 : Blo 682313 2773835 := bstep (se 1 (by rfl) ⟨2080376, by rfl⟩ : syracuseStep 2773835 = 4160753) B4160753
theorem B971723 : Blo 682313 971723 := bstep (se 1 (by rfl) ⟨728792, by rfl⟩ : syracuseStep 971723 = 1457585) B1457585
theorem B1561625 : Blo 682313 1561625 := bstep (se 2 (by rfl) ⟨585609, by rfl⟩ : syracuseStep 1561625 = 1171219) B1171219
theorem B2315357 : Blo 682313 2315357 := bstep (se 3 (by rfl) ⟨434129, by rfl⟩ : syracuseStep 2315357 = 868259) B868259
theorem B1463513 : Blo 682313 1463513 := bstep (se 2 (by rfl) ⟨548817, by rfl⟩ : syracuseStep 1463513 = 1097635) B1097635
theorem B1234163 : Blo 682313 1234163 := bstep (se 1 (by rfl) ⟨925622, by rfl⟩ : syracuseStep 1234163 = 1851245) B1851245
theorem B1300043 : Blo 682313 1300043 := bstep (se 1 (by rfl) ⟨975032, by rfl⟩ : syracuseStep 1300043 = 1950065) B1950065
theorem B3462749 : Blo 682313 3462749 := bstep (se 3 (by rfl) ⟨649265, by rfl⟩ : syracuseStep 3462749 = 1298531) B1298531
theorem B1463923 : Blo 682313 1463923 := bstep (se 1 (by rfl) ⟨1097942, by rfl⟩ : syracuseStep 1463923 = 2195885) B2195885
theorem B2086603 : Blo 682313 2086603 := bstep (se 1 (by rfl) ⟨1564952, by rfl⟩ : syracuseStep 2086603 = 3129905) B3129905
theorem B1300225 : Blo 682313 1300225 := bstep (se 2 (by rfl) ⟨487584, by rfl⟩ : syracuseStep 1300225 = 975169) B975169
theorem B33249203 : Blo 682313 33249203 := bstep (se 1 (by rfl) ⟨24936902, by rfl⟩ : syracuseStep 33249203 = 49873805) B49873805
theorem B1464257 : Blo 682313 1464257 := bstep (se 2 (by rfl) ⟨549096, by rfl⟩ : syracuseStep 1464257 = 1098193) B1098193
theorem B1234955 : Blo 682313 1234955 := bstep (se 1 (by rfl) ⟨926216, by rfl⟩ : syracuseStep 1234955 = 1852433) B1852433
theorem B5003309 : Blo 682313 5003309 := bstep (se 3 (by rfl) ⟨938120, by rfl⟩ : syracuseStep 5003309 = 1876241) B1876241
theorem B4380803 : Blo 682313 4380803 := bstep (se 1 (by rfl) ⟨3285602, by rfl⟩ : syracuseStep 4380803 = 6571205) B6571205
theorem B1300673 : Blo 682313 1300673 := bstep (se 2 (by rfl) ⟨487752, by rfl⟩ : syracuseStep 1300673 = 975505) B975505
theorem B1038539 : Blo 682313 1038539 := bstep (se 1 (by rfl) ⟨778904, by rfl⟩ : syracuseStep 1038539 = 1557809) B1557809
theorem B5921041 : Blo 682313 5921041 := bstep (se 2 (by rfl) ⟨2220390, by rfl⟩ : syracuseStep 5921041 = 4440781) B4440781
theorem B1301015 : Blo 682313 1301015 := bstep (se 1 (by rfl) ⟨975761, by rfl⟩ : syracuseStep 1301015 = 1951523) B1951523
theorem B1038923 : Blo 682313 1038923 := bstep (se 1 (by rfl) ⟨779192, by rfl⟩ : syracuseStep 1038923 = 1558385) B1558385
theorem B1464983 : Blo 682313 1464983 := bstep (se 1 (by rfl) ⟨1098737, by rfl⟩ : syracuseStep 1464983 = 2197475) B2197475
theorem B5200685 : Blo 682313 5200685 := bstep (se 3 (by rfl) ⟨975128, by rfl⟩ : syracuseStep 5200685 = 1950257) B1950257
theorem B2186135 : Blo 682313 2186135 := bstep (se 1 (by rfl) ⟨1639601, by rfl⟩ : syracuseStep 2186135 = 3279203) B3279203
theorem B3169373 : Blo 682313 3169373 := bstep (se 3 (by rfl) ⟨594257, by rfl⟩ : syracuseStep 3169373 = 1188515) B1188515
theorem B1727639 : Blo 682313 1727639 := bstep (se 1 (by rfl) ⟨1295729, by rfl⟩ : syracuseStep 1727639 = 2591459) B2591459
theorem B1301683 : Blo 682313 1301683 := bstep (se 1 (by rfl) ⟨976262, by rfl⟩ : syracuseStep 1301683 = 1952525) B1952525
theorem B3333469 : Blo 682313 3333469 := bstep (se 3 (by rfl) ⟨625025, by rfl⟩ : syracuseStep 3333469 = 1250051) B1250051
theorem B119922061 : Blo 682313 119922061 := bstep (se 3 (by rfl) ⟨22485386, by rfl⟩ : syracuseStep 119922061 = 44970773) B44970773
theorem B1302131 : Blo 682313 1302131 := bstep (se 1 (by rfl) ⟨976598, by rfl⟩ : syracuseStep 1302131 = 1953197) B1953197
theorem B3464855 : Blo 682313 3464855 := bstep (se 1 (by rfl) ⟨2598641, by rfl⟩ : syracuseStep 3464855 = 5197283) B5197283
theorem B1302169 : Blo 682313 1302169 := bstep (se 2 (by rfl) ⟨488313, by rfl⟩ : syracuseStep 1302169 = 976627) B976627
theorem B3891037 : Blo 682313 3891037 := bstep (se 3 (by rfl) ⟨729569, by rfl⟩ : syracuseStep 3891037 = 1459139) B1459139
theorem B1728449 : Blo 682313 1728449 := bstep (se 2 (by rfl) ⟨648168, by rfl⟩ : syracuseStep 1728449 = 1296337) B1296337
theorem B1302617 : Blo 682313 1302617 := bstep (se 2 (by rfl) ⟨488481, by rfl⟩ : syracuseStep 1302617 = 976963) B976963
theorem B5267587 : Blo 682313 5267587 := bstep (se 1 (by rfl) ⟨3950690, by rfl⟩ : syracuseStep 5267587 = 7901381) B7901381
theorem B8348021 : Blo 682313 8348021 := bstep (se 5 (by rfl) ⟨391313, by rfl⟩ : syracuseStep 8348021 = 782627) B782627
theorem B1728985 : Blo 682313 1728985 := bstep (se 2 (by rfl) ⟨648369, by rfl⟩ : syracuseStep 1728985 = 1296739) B1296739
theorem B778987 : Blo 682313 778987 := bstep (se 1 (by rfl) ⟨584240, by rfl⟩ : syracuseStep 778987 = 1168481) B1168481
theorem B1500211 : Blo 682313 1500211 := bstep (se 1 (by rfl) ⟨1125158, by rfl⟩ : syracuseStep 1500211 = 2250317) B2250317
theorem B5563523 : Blo 682313 5563523 := bstep (se 1 (by rfl) ⟨4172642, by rfl⟩ : syracuseStep 5563523 = 8345285) B8345285
theorem B2188595 : Blo 682313 2188595 := bstep (se 1 (by rfl) ⟨1641446, by rfl⟩ : syracuseStep 2188595 = 3282893) B3282893
theorem B2188633 : Blo 682313 2188633 := bstep (se 2 (by rfl) ⟨820737, by rfl⟩ : syracuseStep 2188633 = 1641475) B1641475
theorem B3696023 : Blo 682313 3696023 := bstep (se 1 (by rfl) ⟨2772017, by rfl⟩ : syracuseStep 3696023 = 5544035) B5544035
theorem B1730099 : Blo 682313 1730099 := bstep (se 1 (by rfl) ⟨1297574, by rfl⟩ : syracuseStep 1730099 = 2595149) B2595149
theorem B11691701 : Blo 682313 11691701 := bstep (se 5 (by rfl) ⟨548048, by rfl⟩ : syracuseStep 11691701 = 1096097) B1096097
theorem B1730393 : Blo 682313 1730393 := bstep (se 2 (by rfl) ⟨648897, by rfl⟩ : syracuseStep 1730393 = 1297795) B1297795
theorem B976855 : Blo 682313 976855 := bstep (se 1 (by rfl) ⟨732641, by rfl⟩ : syracuseStep 976855 = 1465283) B1465283
theorem B5335301 : Blo 682313 5335301 := bstep (se 4 (by rfl) ⟨500184, by rfl⟩ : syracuseStep 5335301 = 1000369) B1000369
theorem B682315 : Blo 682313 682315 := bstep (se 1 (by rfl) ⟨511736, by rfl⟩ : syracuseStep 682315 = 1023473) B1023473
theorem B682327 : Blo 682313 682327 := bstep (se 1 (by rfl) ⟨511745, by rfl⟩ : syracuseStep 682327 = 1023491) B1023491
theorem B682347 : Blo 682313 682347 := bstep (se 1 (by rfl) ⟨511760, by rfl⟩ : syracuseStep 682347 = 1023521) B1023521
theorem B682359 : Blo 682313 682359 := bstep (se 1 (by rfl) ⟨511769, by rfl⟩ : syracuseStep 682359 = 1023539) B1023539
theorem B682379 : Blo 682313 682379 := bstep (se 1 (by rfl) ⟨511784, by rfl⟩ : syracuseStep 682379 = 1023569) B1023569
theorem B682391 : Blo 682313 682391 := bstep (se 1 (by rfl) ⟨511793, by rfl⟩ : syracuseStep 682391 = 1023587) B1023587
theorem B682411 : Blo 682313 682411 := bstep (se 1 (by rfl) ⟨511808, by rfl⟩ : syracuseStep 682411 = 1023617) B1023617
theorem B682423 : Blo 682313 682423 := bstep (se 1 (by rfl) ⟨511817, by rfl⟩ : syracuseStep 682423 = 1023635) B1023635
theorem B682443 : Blo 682313 682443 := bstep (se 1 (by rfl) ⟨511832, by rfl⟩ : syracuseStep 682443 = 1023665) B1023665
theorem B682455 : Blo 682313 682455 := bstep (se 1 (by rfl) ⟨511841, by rfl⟩ : syracuseStep 682455 = 1023683) B1023683
theorem B682475 : Blo 682313 682475 := bstep (se 1 (by rfl) ⟨511856, by rfl⟩ : syracuseStep 682475 = 1023713) B1023713
theorem B682487 : Blo 682313 682487 := bstep (se 1 (by rfl) ⟨511865, by rfl⟩ : syracuseStep 682487 = 1023731) B1023731
theorem B682507 : Blo 682313 682507 := bstep (se 1 (by rfl) ⟨511880, by rfl⟩ : syracuseStep 682507 = 1023761) B1023761
theorem B682519 : Blo 682313 682519 := bstep (se 1 (by rfl) ⟨511889, by rfl⟩ : syracuseStep 682519 = 1023779) B1023779
theorem B682539 : Blo 682313 682539 := bstep (se 1 (by rfl) ⟨511904, by rfl⟩ : syracuseStep 682539 = 1023809) B1023809
theorem B682551 : Blo 682313 682551 := bstep (se 1 (by rfl) ⟨511913, by rfl⟩ : syracuseStep 682551 = 1023827) B1023827
theorem B682571 : Blo 682313 682571 := bstep (se 1 (by rfl) ⟨511928, by rfl⟩ : syracuseStep 682571 = 1023857) B1023857
theorem B682583 : Blo 682313 682583 := bstep (se 1 (by rfl) ⟨511937, by rfl⟩ : syracuseStep 682583 = 1023875) B1023875
theorem B5204573 : Blo 682313 5204573 := bstep (se 3 (by rfl) ⟨975857, by rfl⟩ : syracuseStep 5204573 = 1951715) B1951715
theorem B682603 : Blo 682313 682603 := bstep (se 1 (by rfl) ⟨511952, by rfl⟩ : syracuseStep 682603 = 1023905) B1023905
theorem B682615 : Blo 682313 682615 := bstep (se 1 (by rfl) ⟨511961, by rfl⟩ : syracuseStep 682615 = 1023923) B1023923
theorem B682635 : Blo 682313 682635 := bstep (se 1 (by rfl) ⟨511976, by rfl⟩ : syracuseStep 682635 = 1023953) B1023953
theorem B682647 : Blo 682313 682647 := bstep (se 1 (by rfl) ⟨511985, by rfl⟩ : syracuseStep 682647 = 1023971) B1023971
theorem B682667 : Blo 682313 682667 := bstep (se 1 (by rfl) ⟨512000, by rfl⟩ : syracuseStep 682667 = 1024001) B1024001
theorem B682679 : Blo 682313 682679 := bstep (se 1 (by rfl) ⟨512009, by rfl⟩ : syracuseStep 682679 = 1024019) B1024019
theorem B682699 : Blo 682313 682699 := bstep (se 1 (by rfl) ⟨512024, by rfl⟩ : syracuseStep 682699 = 1024049) B1024049
theorem B682711 : Blo 682313 682711 := bstep (se 1 (by rfl) ⟨512033, by rfl⟩ : syracuseStep 682711 = 1024067) B1024067
theorem B682731 : Blo 682313 682731 := bstep (se 1 (by rfl) ⟨512048, by rfl⟩ : syracuseStep 682731 = 1024097) B1024097
theorem B682743 : Blo 682313 682743 := bstep (se 1 (by rfl) ⟨512057, by rfl⟩ : syracuseStep 682743 = 1024115) B1024115
theorem B682763 : Blo 682313 682763 := bstep (se 1 (by rfl) ⟨512072, by rfl⟩ : syracuseStep 682763 = 1024145) B1024145
theorem B682775 : Blo 682313 682775 := bstep (se 1 (by rfl) ⟨512081, by rfl⟩ : syracuseStep 682775 = 1024163) B1024163
theorem B682795 : Blo 682313 682795 := bstep (se 1 (by rfl) ⟨512096, by rfl⟩ : syracuseStep 682795 = 1024193) B1024193
theorem B682807 : Blo 682313 682807 := bstep (se 1 (by rfl) ⟨512105, by rfl⟩ : syracuseStep 682807 = 1024211) B1024211
theorem B682827 : Blo 682313 682827 := bstep (se 1 (by rfl) ⟨512120, by rfl⟩ : syracuseStep 682827 = 1024241) B1024241
theorem B682839 : Blo 682313 682839 := bstep (se 1 (by rfl) ⟨512129, by rfl⟩ : syracuseStep 682839 = 1024259) B1024259
theorem B1502039 : Blo 682313 1502039 := bstep (se 1 (by rfl) ⟨1126529, by rfl⟩ : syracuseStep 1502039 = 2253059) B2253059
theorem B682859 : Blo 682313 682859 := bstep (se 1 (by rfl) ⟨512144, by rfl⟩ : syracuseStep 682859 = 1024289) B1024289
theorem B682871 : Blo 682313 682871 := bstep (se 1 (by rfl) ⟨512153, by rfl⟩ : syracuseStep 682871 = 1024307) B1024307
theorem B682891 : Blo 682313 682891 := bstep (se 1 (by rfl) ⟨512168, by rfl⟩ : syracuseStep 682891 = 1024337) B1024337
theorem B682903 : Blo 682313 682903 := bstep (se 1 (by rfl) ⟨512177, by rfl⟩ : syracuseStep 682903 = 1024355) B1024355
theorem B682923 : Blo 682313 682923 := bstep (se 1 (by rfl) ⟨512192, by rfl⟩ : syracuseStep 682923 = 1024385) B1024385
theorem B682935 : Blo 682313 682935 := bstep (se 1 (by rfl) ⟨512201, by rfl⟩ : syracuseStep 682935 = 1024403) B1024403
theorem B682955 : Blo 682313 682955 := bstep (se 1 (by rfl) ⟨512216, by rfl⟩ : syracuseStep 682955 = 1024433) B1024433
theorem B682967 : Blo 682313 682967 := bstep (se 1 (by rfl) ⟨512225, by rfl⟩ : syracuseStep 682967 = 1024451) B1024451
theorem B682987 : Blo 682313 682987 := bstep (se 1 (by rfl) ⟨512240, by rfl⟩ : syracuseStep 682987 = 1024481) B1024481
theorem B682999 : Blo 682313 682999 := bstep (se 1 (by rfl) ⟨512249, by rfl⟩ : syracuseStep 682999 = 1024499) B1024499
theorem B683019 : Blo 682313 683019 := bstep (se 1 (by rfl) ⟨512264, by rfl⟩ : syracuseStep 683019 = 1024529) B1024529
theorem B683031 : Blo 682313 683031 := bstep (se 1 (by rfl) ⟨512273, by rfl⟩ : syracuseStep 683031 = 1024547) B1024547
theorem B683051 : Blo 682313 683051 := bstep (se 1 (by rfl) ⟨512288, by rfl⟩ : syracuseStep 683051 = 1024577) B1024577
theorem B683063 : Blo 682313 683063 := bstep (se 1 (by rfl) ⟨512297, by rfl⟩ : syracuseStep 683063 = 1024595) B1024595
theorem B683083 : Blo 682313 683083 := bstep (se 1 (by rfl) ⟨512312, by rfl⟩ : syracuseStep 683083 = 1024625) B1024625
theorem B683095 : Blo 682313 683095 := bstep (se 1 (by rfl) ⟨512321, by rfl⟩ : syracuseStep 683095 = 1024643) B1024643
theorem B683115 : Blo 682313 683115 := bstep (se 1 (by rfl) ⟨512336, by rfl⟩ : syracuseStep 683115 = 1024673) B1024673
theorem B683127 : Blo 682313 683127 := bstep (se 1 (by rfl) ⟨512345, by rfl⟩ : syracuseStep 683127 = 1024691) B1024691
theorem B3468419 : Blo 682313 3468419 := bstep (se 1 (by rfl) ⟨2601314, by rfl⟩ : syracuseStep 3468419 = 5202629) B5202629
theorem B683147 : Blo 682313 683147 := bstep (se 1 (by rfl) ⟨512360, by rfl⟩ : syracuseStep 683147 = 1024721) B1024721
theorem B683159 : Blo 682313 683159 := bstep (se 1 (by rfl) ⟨512369, by rfl⟩ : syracuseStep 683159 = 1024739) B1024739
theorem B683179 : Blo 682313 683179 := bstep (se 1 (by rfl) ⟨512384, by rfl⟩ : syracuseStep 683179 = 1024769) B1024769
theorem B683191 : Blo 682313 683191 := bstep (se 1 (by rfl) ⟨512393, by rfl⟩ : syracuseStep 683191 = 1024787) B1024787
theorem B683211 : Blo 682313 683211 := bstep (se 1 (by rfl) ⟨512408, by rfl⟩ : syracuseStep 683211 = 1024817) B1024817
theorem B683223 : Blo 682313 683223 := bstep (se 1 (by rfl) ⟨512417, by rfl⟩ : syracuseStep 683223 = 1024835) B1024835
theorem B683243 : Blo 682313 683243 := bstep (se 1 (by rfl) ⟨512432, by rfl⟩ : syracuseStep 683243 = 1024865) B1024865
theorem B1535219 : Blo 682313 1535219 := bstep (se 1 (by rfl) ⟨1151414, by rfl⟩ : syracuseStep 1535219 = 2302829) B2302829
theorem B683255 : Blo 682313 683255 := bstep (se 1 (by rfl) ⟨512441, by rfl⟩ : syracuseStep 683255 = 1024883) B1024883
theorem B5860613 : Blo 682313 5860613 := bstep (se 4 (by rfl) ⟨549432, by rfl⟩ : syracuseStep 5860613 = 1098865) B1098865
theorem B683275 : Blo 682313 683275 := bstep (se 1 (by rfl) ⟨512456, by rfl⟩ : syracuseStep 683275 = 1024913) B1024913
theorem B1535255 : Blo 682313 1535255 := bstep (se 1 (by rfl) ⟨1151441, by rfl⟩ : syracuseStep 1535255 = 2302883) B2302883
theorem B683287 : Blo 682313 683287 := bstep (se 1 (by rfl) ⟨512465, by rfl⟩ : syracuseStep 683287 = 1024931) B1024931
theorem B683307 : Blo 682313 683307 := bstep (se 1 (by rfl) ⟨512480, by rfl⟩ : syracuseStep 683307 = 1024961) B1024961
theorem B683319 : Blo 682313 683319 := bstep (se 1 (by rfl) ⟨512489, by rfl⟩ : syracuseStep 683319 = 1024979) B1024979
theorem B10513729 : Blo 682313 10513729 := bstep (se 2 (by rfl) ⟨3942648, by rfl⟩ : syracuseStep 10513729 = 7885297) B7885297
theorem B683339 : Blo 682313 683339 := bstep (se 1 (by rfl) ⟨512504, by rfl⟩ : syracuseStep 683339 = 1025009) B1025009
theorem B683351 : Blo 682313 683351 := bstep (se 1 (by rfl) ⟨512513, by rfl⟩ : syracuseStep 683351 = 1025027) B1025027
theorem B683371 : Blo 682313 683371 := bstep (se 1 (by rfl) ⟨512528, by rfl⟩ : syracuseStep 683371 = 1025057) B1025057
theorem B683383 : Blo 682313 683383 := bstep (se 1 (by rfl) ⟨512537, by rfl⟩ : syracuseStep 683383 = 1025075) B1025075
theorem B683403 : Blo 682313 683403 := bstep (se 1 (by rfl) ⟨512552, by rfl⟩ : syracuseStep 683403 = 1025105) B1025105
theorem B683415 : Blo 682313 683415 := bstep (se 1 (by rfl) ⟨512561, by rfl⟩ : syracuseStep 683415 = 1025123) B1025123
theorem B683435 : Blo 682313 683435 := bstep (se 1 (by rfl) ⟨512576, by rfl⟩ : syracuseStep 683435 = 1025153) B1025153
theorem B3698099 : Blo 682313 3698099 := bstep (se 1 (by rfl) ⟨2773574, by rfl⟩ : syracuseStep 3698099 = 5547149) B5547149
theorem B683447 : Blo 682313 683447 := bstep (se 1 (by rfl) ⟨512585, by rfl⟩ : syracuseStep 683447 = 1025171) B1025171
theorem B1535435 : Blo 682313 1535435 := bstep (se 1 (by rfl) ⟨1151576, by rfl⟩ : syracuseStep 1535435 = 2303153) B2303153
theorem B683467 : Blo 682313 683467 := bstep (se 1 (by rfl) ⟨512600, by rfl⟩ : syracuseStep 683467 = 1025201) B1025201
theorem B1732043 : Blo 682313 1732043 := bstep (se 1 (by rfl) ⟨1299032, by rfl⟩ : syracuseStep 1732043 = 2598065) B2598065
theorem B683479 : Blo 682313 683479 := bstep (se 1 (by rfl) ⟨512609, by rfl⟩ : syracuseStep 683479 = 1025219) B1025219
theorem B683499 : Blo 682313 683499 := bstep (se 1 (by rfl) ⟨512624, by rfl⟩ : syracuseStep 683499 = 1025249) B1025249
theorem B683511 : Blo 682313 683511 := bstep (se 1 (by rfl) ⟨512633, by rfl⟩ : syracuseStep 683511 = 1025267) B1025267
theorem B1535489 : Blo 682313 1535489 := bstep (se 2 (by rfl) ⟨575808, by rfl⟩ : syracuseStep 1535489 = 1151617) B1151617
theorem B683531 : Blo 682313 683531 := bstep (se 1 (by rfl) ⟨512648, by rfl⟩ : syracuseStep 683531 = 1025297) B1025297
theorem B683543 : Blo 682313 683543 := bstep (se 1 (by rfl) ⟨512657, by rfl⟩ : syracuseStep 683543 = 1025315) B1025315
theorem B683563 : Blo 682313 683563 := bstep (se 1 (by rfl) ⟨512672, by rfl⟩ : syracuseStep 683563 = 1025345) B1025345
theorem B683575 : Blo 682313 683575 := bstep (se 1 (by rfl) ⟨512681, by rfl⟩ : syracuseStep 683575 = 1025363) B1025363
theorem B683595 : Blo 682313 683595 := bstep (se 1 (by rfl) ⟨512696, by rfl⟩ : syracuseStep 683595 = 1025393) B1025393
theorem B683607 : Blo 682313 683607 := bstep (se 1 (by rfl) ⟨512705, by rfl⟩ : syracuseStep 683607 = 1025411) B1025411
theorem B683627 : Blo 682313 683627 := bstep (se 1 (by rfl) ⟨512720, by rfl⟩ : syracuseStep 683627 = 1025441) B1025441
theorem B683639 : Blo 682313 683639 := bstep (se 1 (by rfl) ⟨512729, by rfl⟩ : syracuseStep 683639 = 1025459) B1025459
theorem B683659 : Blo 682313 683659 := bstep (se 1 (by rfl) ⟨512744, by rfl⟩ : syracuseStep 683659 = 1025489) B1025489
theorem B683671 : Blo 682313 683671 := bstep (se 1 (by rfl) ⟨512753, by rfl⟩ : syracuseStep 683671 = 1025507) B1025507
theorem B683691 : Blo 682313 683691 := bstep (se 1 (by rfl) ⟨512768, by rfl⟩ : syracuseStep 683691 = 1025537) B1025537
theorem B683703 : Blo 682313 683703 := bstep (se 1 (by rfl) ⟨512777, by rfl⟩ : syracuseStep 683703 = 1025555) B1025555
theorem B683723 : Blo 682313 683723 := bstep (se 1 (by rfl) ⟨512792, by rfl⟩ : syracuseStep 683723 = 1025585) B1025585
theorem B683735 : Blo 682313 683735 := bstep (se 1 (by rfl) ⟨512801, by rfl⟩ : syracuseStep 683735 = 1025603) B1025603
theorem B1535705 : Blo 682313 1535705 := bstep (se 2 (by rfl) ⟨575889, by rfl⟩ : syracuseStep 1535705 = 1151779) B1151779
theorem B683755 : Blo 682313 683755 := bstep (se 1 (by rfl) ⟨512816, by rfl⟩ : syracuseStep 683755 = 1025633) B1025633
theorem B683767 : Blo 682313 683767 := bstep (se 1 (by rfl) ⟨512825, by rfl⟩ : syracuseStep 683767 = 1025651) B1025651
theorem B683787 : Blo 682313 683787 := bstep (se 1 (by rfl) ⟨512840, by rfl⟩ : syracuseStep 683787 = 1025681) B1025681
theorem B683799 : Blo 682313 683799 := bstep (se 1 (by rfl) ⟨512849, by rfl⟩ : syracuseStep 683799 = 1025699) B1025699
theorem B683819 : Blo 682313 683819 := bstep (se 1 (by rfl) ⟨512864, by rfl⟩ : syracuseStep 683819 = 1025729) B1025729
theorem B2748205 : Blo 682313 2748205 := bstep (se 3 (by rfl) ⟨515288, by rfl⟩ : syracuseStep 2748205 = 1030577) B1030577
theorem B1535795 : Blo 682313 1535795 := bstep (se 1 (by rfl) ⟨1151846, by rfl⟩ : syracuseStep 1535795 = 2303693) B2303693
theorem B683831 : Blo 682313 683831 := bstep (se 1 (by rfl) ⟨512873, by rfl⟩ : syracuseStep 683831 = 1025747) B1025747
theorem B2191169 : Blo 682313 2191169 := bstep (se 2 (by rfl) ⟨821688, by rfl⟩ : syracuseStep 2191169 = 1643377) B1643377
theorem B683851 : Blo 682313 683851 := bstep (se 1 (by rfl) ⟨512888, by rfl⟩ : syracuseStep 683851 = 1025777) B1025777
theorem B1535831 : Blo 682313 1535831 := bstep (se 1 (by rfl) ⟨1151873, by rfl⟩ : syracuseStep 1535831 = 2303747) B2303747
theorem B683863 : Blo 682313 683863 := bstep (se 1 (by rfl) ⟨512897, by rfl⟩ : syracuseStep 683863 = 1025795) B1025795
theorem B683883 : Blo 682313 683883 := bstep (se 1 (by rfl) ⟨512912, by rfl⟩ : syracuseStep 683883 = 1025825) B1025825
theorem B683895 : Blo 682313 683895 := bstep (se 1 (by rfl) ⟨512921, by rfl⟩ : syracuseStep 683895 = 1025843) B1025843
theorem B683915 : Blo 682313 683915 := bstep (se 1 (by rfl) ⟨512936, by rfl⟩ : syracuseStep 683915 = 1025873) B1025873
theorem B683927 : Blo 682313 683927 := bstep (se 1 (by rfl) ⟨512945, by rfl⟩ : syracuseStep 683927 = 1025891) B1025891
theorem B683947 : Blo 682313 683947 := bstep (se 1 (by rfl) ⟨512960, by rfl⟩ : syracuseStep 683947 = 1025921) B1025921
theorem B683959 : Blo 682313 683959 := bstep (se 1 (by rfl) ⟨512969, by rfl⟩ : syracuseStep 683959 = 1025939) B1025939
theorem B683979 : Blo 682313 683979 := bstep (se 1 (by rfl) ⟨512984, by rfl⟩ : syracuseStep 683979 = 1025969) B1025969
theorem B683991 : Blo 682313 683991 := bstep (se 1 (by rfl) ⟨512993, by rfl⟩ : syracuseStep 683991 = 1025987) B1025987
theorem B684011 : Blo 682313 684011 := bstep (se 1 (by rfl) ⟨513008, by rfl⟩ : syracuseStep 684011 = 1026017) B1026017
theorem B684023 : Blo 682313 684023 := bstep (se 1 (by rfl) ⟨513017, by rfl⟩ : syracuseStep 684023 = 1026035) B1026035
theorem B1536011 : Blo 682313 1536011 := bstep (se 1 (by rfl) ⟨1152008, by rfl⟩ : syracuseStep 1536011 = 2304017) B2304017
theorem B684043 : Blo 682313 684043 := bstep (se 1 (by rfl) ⟨513032, by rfl⟩ : syracuseStep 684043 = 1026065) B1026065
theorem B684055 : Blo 682313 684055 := bstep (se 1 (by rfl) ⟨513041, by rfl⟩ : syracuseStep 684055 = 1026083) B1026083
theorem B684075 : Blo 682313 684075 := bstep (se 1 (by rfl) ⟨513056, by rfl⟩ : syracuseStep 684075 = 1026113) B1026113
theorem B684087 : Blo 682313 684087 := bstep (se 1 (by rfl) ⟨513065, by rfl⟩ : syracuseStep 684087 = 1026131) B1026131
theorem B1536065 : Blo 682313 1536065 := bstep (se 2 (by rfl) ⟨576024, by rfl⟩ : syracuseStep 1536065 = 1152049) B1152049
theorem B684107 : Blo 682313 684107 := bstep (se 1 (by rfl) ⟨513080, by rfl⟩ : syracuseStep 684107 = 1026161) B1026161
theorem B684119 : Blo 682313 684119 := bstep (se 1 (by rfl) ⟨513089, by rfl⟩ : syracuseStep 684119 = 1026179) B1026179
theorem B684139 : Blo 682313 684139 := bstep (se 1 (by rfl) ⟨513104, by rfl⟩ : syracuseStep 684139 = 1026209) B1026209
theorem B684151 : Blo 682313 684151 := bstep (se 1 (by rfl) ⟨513113, by rfl⟩ : syracuseStep 684151 = 1026227) B1026227
theorem B684171 : Blo 682313 684171 := bstep (se 1 (by rfl) ⟨513128, by rfl⟩ : syracuseStep 684171 = 1026257) B1026257
theorem B684183 : Blo 682313 684183 := bstep (se 1 (by rfl) ⟨513137, by rfl⟩ : syracuseStep 684183 = 1026275) B1026275
theorem B684203 : Blo 682313 684203 := bstep (se 1 (by rfl) ⟨513152, by rfl⟩ : syracuseStep 684203 = 1026305) B1026305
theorem B684215 : Blo 682313 684215 := bstep (se 1 (by rfl) ⟨513161, by rfl⟩ : syracuseStep 684215 = 1026323) B1026323
theorem B684235 : Blo 682313 684235 := bstep (se 1 (by rfl) ⟨513176, by rfl⟩ : syracuseStep 684235 = 1026353) B1026353
theorem B684247 : Blo 682313 684247 := bstep (se 1 (by rfl) ⟨513185, by rfl⟩ : syracuseStep 684247 = 1026371) B1026371
theorem B684267 : Blo 682313 684267 := bstep (se 1 (by rfl) ⟨513200, by rfl⟩ : syracuseStep 684267 = 1026401) B1026401
theorem B684279 : Blo 682313 684279 := bstep (se 1 (by rfl) ⟨513209, by rfl⟩ : syracuseStep 684279 = 1026419) B1026419
theorem B684299 : Blo 682313 684299 := bstep (se 1 (by rfl) ⟨513224, by rfl⟩ : syracuseStep 684299 = 1026449) B1026449
theorem B684311 : Blo 682313 684311 := bstep (se 1 (by rfl) ⟨513233, by rfl⟩ : syracuseStep 684311 = 1026467) B1026467
theorem B1536281 : Blo 682313 1536281 := bstep (se 2 (by rfl) ⟨576105, by rfl⟩ : syracuseStep 1536281 = 1152211) B1152211
theorem B684331 : Blo 682313 684331 := bstep (se 1 (by rfl) ⟨513248, by rfl⟩ : syracuseStep 684331 = 1026497) B1026497
theorem B684343 : Blo 682313 684343 := bstep (se 1 (by rfl) ⟨513257, by rfl⟩ : syracuseStep 684343 = 1026515) B1026515
theorem B684363 : Blo 682313 684363 := bstep (se 1 (by rfl) ⟨513272, by rfl⟩ : syracuseStep 684363 = 1026545) B1026545
theorem B684375 : Blo 682313 684375 := bstep (se 1 (by rfl) ⟨513281, by rfl⟩ : syracuseStep 684375 = 1026563) B1026563
theorem B684395 : Blo 682313 684395 := bstep (se 1 (by rfl) ⟨513296, by rfl⟩ : syracuseStep 684395 = 1026593) B1026593
theorem B1536371 : Blo 682313 1536371 := bstep (se 1 (by rfl) ⟨1152278, by rfl⟩ : syracuseStep 1536371 = 2304557) B2304557
theorem B684407 : Blo 682313 684407 := bstep (se 1 (by rfl) ⟨513305, by rfl⟩ : syracuseStep 684407 = 1026611) B1026611
theorem B684427 : Blo 682313 684427 := bstep (se 1 (by rfl) ⟨513320, by rfl⟩ : syracuseStep 684427 = 1026641) B1026641
theorem B1536407 : Blo 682313 1536407 := bstep (se 1 (by rfl) ⟨1152305, by rfl⟩ : syracuseStep 1536407 = 2304611) B2304611
theorem B684439 : Blo 682313 684439 := bstep (se 1 (by rfl) ⟨513329, by rfl⟩ : syracuseStep 684439 = 1026659) B1026659
theorem B1733015 : Blo 682313 1733015 := bstep (se 1 (by rfl) ⟨1299761, by rfl⟩ : syracuseStep 1733015 = 2599523) B2599523
theorem B684459 : Blo 682313 684459 := bstep (se 1 (by rfl) ⟨513344, by rfl⟩ : syracuseStep 684459 = 1026689) B1026689
theorem B684471 : Blo 682313 684471 := bstep (se 1 (by rfl) ⟨513353, by rfl⟩ : syracuseStep 684471 = 1026707) B1026707
theorem B684491 : Blo 682313 684491 := bstep (se 1 (by rfl) ⟨513368, by rfl⟩ : syracuseStep 684491 = 1026737) B1026737
theorem B684503 : Blo 682313 684503 := bstep (se 1 (by rfl) ⟨513377, by rfl⟩ : syracuseStep 684503 = 1026755) B1026755
theorem B684523 : Blo 682313 684523 := bstep (se 1 (by rfl) ⟨513392, by rfl⟩ : syracuseStep 684523 = 1026785) B1026785
theorem B684535 : Blo 682313 684535 := bstep (se 1 (by rfl) ⟨513401, by rfl⟩ : syracuseStep 684535 = 1026803) B1026803
theorem B684555 : Blo 682313 684555 := bstep (se 1 (by rfl) ⟨513416, by rfl⟩ : syracuseStep 684555 = 1026833) B1026833
theorem B684567 : Blo 682313 684567 := bstep (se 1 (by rfl) ⟨513425, by rfl⟩ : syracuseStep 684567 = 1026851) B1026851
theorem B684587 : Blo 682313 684587 := bstep (se 1 (by rfl) ⟨513440, by rfl⟩ : syracuseStep 684587 = 1026881) B1026881
theorem B684599 : Blo 682313 684599 := bstep (se 1 (by rfl) ⟨513449, by rfl⟩ : syracuseStep 684599 = 1026899) B1026899
theorem B1536587 : Blo 682313 1536587 := bstep (se 1 (by rfl) ⟨1152440, by rfl⟩ : syracuseStep 1536587 = 2304881) B2304881
theorem B684619 : Blo 682313 684619 := bstep (se 1 (by rfl) ⟨513464, by rfl⟩ : syracuseStep 684619 = 1026929) B1026929
theorem B684631 : Blo 682313 684631 := bstep (se 1 (by rfl) ⟨513473, by rfl⟩ : syracuseStep 684631 = 1026947) B1026947
theorem B13529693 : Blo 682313 13529693 := bstep (se 3 (by rfl) ⟨2536817, by rfl⟩ : syracuseStep 13529693 = 5073635) B5073635
theorem B684651 : Blo 682313 684651 := bstep (se 1 (by rfl) ⟨513488, by rfl⟩ : syracuseStep 684651 = 1026977) B1026977
theorem B684663 : Blo 682313 684663 := bstep (se 1 (by rfl) ⟨513497, by rfl⟩ : syracuseStep 684663 = 1026995) B1026995
theorem B1536641 : Blo 682313 1536641 := bstep (se 2 (by rfl) ⟨576240, by rfl⟩ : syracuseStep 1536641 = 1152481) B1152481
theorem B684683 : Blo 682313 684683 := bstep (se 1 (by rfl) ⟨513512, by rfl⟩ : syracuseStep 684683 = 1027025) B1027025
theorem B684695 : Blo 682313 684695 := bstep (se 1 (by rfl) ⟨513521, by rfl⟩ : syracuseStep 684695 = 1027043) B1027043
theorem B684715 : Blo 682313 684715 := bstep (se 1 (by rfl) ⟨513536, by rfl⟩ : syracuseStep 684715 = 1027073) B1027073
theorem B684727 : Blo 682313 684727 := bstep (se 1 (by rfl) ⟨513545, by rfl⟩ : syracuseStep 684727 = 1027091) B1027091
theorem B684747 : Blo 682313 684747 := bstep (se 1 (by rfl) ⟨513560, by rfl⟩ : syracuseStep 684747 = 1027121) B1027121
theorem B684759 : Blo 682313 684759 := bstep (se 1 (by rfl) ⟨513569, by rfl⟩ : syracuseStep 684759 = 1027139) B1027139
theorem B2192093 : Blo 682313 2192093 := bstep (se 3 (by rfl) ⟨411017, by rfl⟩ : syracuseStep 2192093 = 822035) B822035
theorem B684779 : Blo 682313 684779 := bstep (se 1 (by rfl) ⟨513584, by rfl⟩ : syracuseStep 684779 = 1027169) B1027169
theorem B684791 : Blo 682313 684791 := bstep (se 1 (by rfl) ⟨513593, by rfl⟩ : syracuseStep 684791 = 1027187) B1027187
theorem B684811 : Blo 682313 684811 := bstep (se 1 (by rfl) ⟨513608, by rfl⟩ : syracuseStep 684811 = 1027217) B1027217
theorem B684823 : Blo 682313 684823 := bstep (se 1 (by rfl) ⟨513617, by rfl⟩ : syracuseStep 684823 = 1027235) B1027235
theorem B684843 : Blo 682313 684843 := bstep (se 1 (by rfl) ⟨513632, by rfl⟩ : syracuseStep 684843 = 1027265) B1027265
theorem B684855 : Blo 682313 684855 := bstep (se 1 (by rfl) ⟨513641, by rfl⟩ : syracuseStep 684855 = 1027283) B1027283
theorem B684875 : Blo 682313 684875 := bstep (se 1 (by rfl) ⟨513656, by rfl⟩ : syracuseStep 684875 = 1027313) B1027313
theorem B3961675 : Blo 682313 3961675 := bstep (se 1 (by rfl) ⟨2971256, by rfl⟩ : syracuseStep 3961675 = 5942513) B5942513
theorem B684887 : Blo 682313 684887 := bstep (se 1 (by rfl) ⟨513665, by rfl⟩ : syracuseStep 684887 = 1027331) B1027331
theorem B1536857 : Blo 682313 1536857 := bstep (se 2 (by rfl) ⟨576321, by rfl⟩ : syracuseStep 1536857 = 1152643) B1152643
theorem B684907 : Blo 682313 684907 := bstep (se 1 (by rfl) ⟨513680, by rfl⟩ : syracuseStep 684907 = 1027361) B1027361
theorem B684919 : Blo 682313 684919 := bstep (se 1 (by rfl) ⟨513689, by rfl⟩ : syracuseStep 684919 = 1027379) B1027379
theorem B684939 : Blo 682313 684939 := bstep (se 1 (by rfl) ⟨513704, by rfl⟩ : syracuseStep 684939 = 1027409) B1027409
theorem B684951 : Blo 682313 684951 := bstep (se 1 (by rfl) ⟨513713, by rfl⟩ : syracuseStep 684951 = 1027427) B1027427
theorem B684971 : Blo 682313 684971 := bstep (se 1 (by rfl) ⟨513728, by rfl⟩ : syracuseStep 684971 = 1027457) B1027457
theorem B12678065 : Blo 682313 12678065 := bstep (se 2 (by rfl) ⟨4754274, by rfl⟩ : syracuseStep 12678065 = 9508549) B9508549
theorem B1536947 : Blo 682313 1536947 := bstep (se 1 (by rfl) ⟨1152710, by rfl⟩ : syracuseStep 1536947 = 2305421) B2305421
theorem B684983 : Blo 682313 684983 := bstep (se 1 (by rfl) ⟨513737, by rfl⟩ : syracuseStep 684983 = 1027475) B1027475
theorem B685003 : Blo 682313 685003 := bstep (se 1 (by rfl) ⟨513752, by rfl⟩ : syracuseStep 685003 = 1027505) B1027505
theorem B1536983 : Blo 682313 1536983 := bstep (se 1 (by rfl) ⟨1152737, by rfl⟩ : syracuseStep 1536983 = 2305475) B2305475
theorem B685015 : Blo 682313 685015 := bstep (se 1 (by rfl) ⟨513761, by rfl⟩ : syracuseStep 685015 = 1027523) B1027523
theorem B685035 : Blo 682313 685035 := bstep (se 1 (by rfl) ⟨513776, by rfl⟩ : syracuseStep 685035 = 1027553) B1027553
theorem B685047 : Blo 682313 685047 := bstep (se 1 (by rfl) ⟨513785, by rfl⟩ : syracuseStep 685047 = 1027571) B1027571
theorem B685067 : Blo 682313 685067 := bstep (se 1 (by rfl) ⟨513800, by rfl⟩ : syracuseStep 685067 = 1027601) B1027601
theorem B685079 : Blo 682313 685079 := bstep (se 1 (by rfl) ⟨513809, by rfl⟩ : syracuseStep 685079 = 1027619) B1027619
theorem B685099 : Blo 682313 685099 := bstep (se 1 (by rfl) ⟨513824, by rfl⟩ : syracuseStep 685099 = 1027649) B1027649
theorem B1733683 : Blo 682313 1733683 := bstep (se 1 (by rfl) ⟨1300262, by rfl⟩ : syracuseStep 1733683 = 2600525) B2600525
theorem B685111 : Blo 682313 685111 := bstep (se 1 (by rfl) ⟨513833, by rfl⟩ : syracuseStep 685111 = 1027667) B1027667
theorem B685131 : Blo 682313 685131 := bstep (se 1 (by rfl) ⟨513848, by rfl⟩ : syracuseStep 685131 = 1027697) B1027697
theorem B685143 : Blo 682313 685143 := bstep (se 1 (by rfl) ⟨513857, by rfl⟩ : syracuseStep 685143 = 1027715) B1027715
theorem B685163 : Blo 682313 685163 := bstep (se 1 (by rfl) ⟨513872, by rfl⟩ : syracuseStep 685163 = 1027745) B1027745
theorem B685175 : Blo 682313 685175 := bstep (se 1 (by rfl) ⟨513881, by rfl⟩ : syracuseStep 685175 = 1027763) B1027763
theorem B1537163 : Blo 682313 1537163 := bstep (se 1 (by rfl) ⟨1152872, by rfl⟩ : syracuseStep 1537163 = 2305745) B2305745
theorem B685195 : Blo 682313 685195 := bstep (se 1 (by rfl) ⟨513896, by rfl⟩ : syracuseStep 685195 = 1027793) B1027793
theorem B685207 : Blo 682313 685207 := bstep (se 1 (by rfl) ⟨513905, by rfl⟩ : syracuseStep 685207 = 1027811) B1027811
theorem B685227 : Blo 682313 685227 := bstep (se 1 (by rfl) ⟨513920, by rfl⟩ : syracuseStep 685227 = 1027841) B1027841
theorem B685239 : Blo 682313 685239 := bstep (se 1 (by rfl) ⟨513929, by rfl⟩ : syracuseStep 685239 = 1027859) B1027859
theorem B1537217 : Blo 682313 1537217 := bstep (se 2 (by rfl) ⟨576456, by rfl⟩ : syracuseStep 1537217 = 1152913) B1152913
theorem B1733825 : Blo 682313 1733825 := bstep (se 2 (by rfl) ⟨650184, by rfl⟩ : syracuseStep 1733825 = 1300369) B1300369
theorem B685259 : Blo 682313 685259 := bstep (se 1 (by rfl) ⟨513944, by rfl⟩ : syracuseStep 685259 = 1027889) B1027889
theorem B685271 : Blo 682313 685271 := bstep (se 1 (by rfl) ⟨513953, by rfl⟩ : syracuseStep 685271 = 1027907) B1027907
theorem B685291 : Blo 682313 685291 := bstep (se 1 (by rfl) ⟨513968, by rfl⟩ : syracuseStep 685291 = 1027937) B1027937
theorem B685303 : Blo 682313 685303 := bstep (se 1 (by rfl) ⟨513977, by rfl⟩ : syracuseStep 685303 = 1027955) B1027955
theorem B685323 : Blo 682313 685323 := bstep (se 1 (by rfl) ⟨513992, by rfl⟩ : syracuseStep 685323 = 1027985) B1027985
theorem B685335 : Blo 682313 685335 := bstep (se 1 (by rfl) ⟨514001, by rfl⟩ : syracuseStep 685335 = 1028003) B1028003
theorem B685355 : Blo 682313 685355 := bstep (se 1 (by rfl) ⟨514016, by rfl⟩ : syracuseStep 685355 = 1028033) B1028033
theorem B685367 : Blo 682313 685367 := bstep (se 1 (by rfl) ⟨514025, by rfl⟩ : syracuseStep 685367 = 1028051) B1028051
theorem B685387 : Blo 682313 685387 := bstep (se 1 (by rfl) ⟨514040, by rfl⟩ : syracuseStep 685387 = 1028081) B1028081
theorem B685399 : Blo 682313 685399 := bstep (se 1 (by rfl) ⟨514049, by rfl⟩ : syracuseStep 685399 = 1028099) B1028099
theorem B685419 : Blo 682313 685419 := bstep (se 1 (by rfl) ⟨514064, by rfl⟩ : syracuseStep 685419 = 1028129) B1028129
theorem B685431 : Blo 682313 685431 := bstep (se 1 (by rfl) ⟨514073, by rfl⟩ : syracuseStep 685431 = 1028147) B1028147
theorem B685451 : Blo 682313 685451 := bstep (se 1 (by rfl) ⟨514088, by rfl⟩ : syracuseStep 685451 = 1028177) B1028177
theorem B685463 : Blo 682313 685463 := bstep (se 1 (by rfl) ⟨514097, by rfl⟩ : syracuseStep 685463 = 1028195) B1028195
theorem B1537433 : Blo 682313 1537433 := bstep (se 2 (by rfl) ⟨576537, by rfl⟩ : syracuseStep 1537433 = 1153075) B1153075
theorem B685483 : Blo 682313 685483 := bstep (se 1 (by rfl) ⟨514112, by rfl⟩ : syracuseStep 685483 = 1028225) B1028225
theorem B685495 : Blo 682313 685495 := bstep (se 1 (by rfl) ⟨514121, by rfl⟩ : syracuseStep 685495 = 1028243) B1028243
theorem B685515 : Blo 682313 685515 := bstep (se 1 (by rfl) ⟨514136, by rfl⟩ : syracuseStep 685515 = 1028273) B1028273
theorem B685527 : Blo 682313 685527 := bstep (se 1 (by rfl) ⟨514145, by rfl⟩ : syracuseStep 685527 = 1028291) B1028291
theorem B685547 : Blo 682313 685547 := bstep (se 1 (by rfl) ⟨514160, by rfl⟩ : syracuseStep 685547 = 1028321) B1028321
theorem B1537523 : Blo 682313 1537523 := bstep (se 1 (by rfl) ⟨1153142, by rfl⟩ : syracuseStep 1537523 = 2306285) B2306285
theorem B685559 : Blo 682313 685559 := bstep (se 1 (by rfl) ⟨514169, by rfl⟩ : syracuseStep 685559 = 1028339) B1028339
theorem B685579 : Blo 682313 685579 := bstep (se 1 (by rfl) ⟨514184, by rfl⟩ : syracuseStep 685579 = 1028369) B1028369
theorem B1537559 : Blo 682313 1537559 := bstep (se 1 (by rfl) ⟨1153169, by rfl⟩ : syracuseStep 1537559 = 2306339) B2306339
theorem B685591 : Blo 682313 685591 := bstep (se 1 (by rfl) ⟨514193, by rfl⟩ : syracuseStep 685591 = 1028387) B1028387
theorem B685611 : Blo 682313 685611 := bstep (se 1 (by rfl) ⟨514208, by rfl⟩ : syracuseStep 685611 = 1028417) B1028417
theorem B685623 : Blo 682313 685623 := bstep (se 1 (by rfl) ⟨514217, by rfl⟩ : syracuseStep 685623 = 1028435) B1028435
theorem B685643 : Blo 682313 685643 := bstep (se 1 (by rfl) ⟨514232, by rfl⟩ : syracuseStep 685643 = 1028465) B1028465
theorem B685655 : Blo 682313 685655 := bstep (se 1 (by rfl) ⟨514241, by rfl⟩ : syracuseStep 685655 = 1028483) B1028483
theorem B685675 : Blo 682313 685675 := bstep (se 1 (by rfl) ⟨514256, by rfl⟩ : syracuseStep 685675 = 1028513) B1028513
theorem B685687 : Blo 682313 685687 := bstep (se 1 (by rfl) ⟨514265, by rfl⟩ : syracuseStep 685687 = 1028531) B1028531
theorem B685707 : Blo 682313 685707 := bstep (se 1 (by rfl) ⟨514280, by rfl⟩ : syracuseStep 685707 = 1028561) B1028561
theorem B685719 : Blo 682313 685719 := bstep (se 1 (by rfl) ⟨514289, by rfl⟩ : syracuseStep 685719 = 1028579) B1028579
theorem B685739 : Blo 682313 685739 := bstep (se 1 (by rfl) ⟨514304, by rfl⟩ : syracuseStep 685739 = 1028609) B1028609
theorem B685751 : Blo 682313 685751 := bstep (se 1 (by rfl) ⟨514313, by rfl⟩ : syracuseStep 685751 = 1028627) B1028627
theorem B1537739 : Blo 682313 1537739 := bstep (se 1 (by rfl) ⟨1153304, by rfl⟩ : syracuseStep 1537739 = 2306609) B2306609
theorem B685771 : Blo 682313 685771 := bstep (se 1 (by rfl) ⟨514328, by rfl⟩ : syracuseStep 685771 = 1028657) B1028657
theorem B685783 : Blo 682313 685783 := bstep (se 1 (by rfl) ⟨514337, by rfl⟩ : syracuseStep 685783 = 1028675) B1028675
theorem B685803 : Blo 682313 685803 := bstep (se 1 (by rfl) ⟨514352, by rfl⟩ : syracuseStep 685803 = 1028705) B1028705
theorem B685815 : Blo 682313 685815 := bstep (se 1 (by rfl) ⟨514361, by rfl⟩ : syracuseStep 685815 = 1028723) B1028723
theorem B1537793 : Blo 682313 1537793 := bstep (se 2 (by rfl) ⟨576672, by rfl⟩ : syracuseStep 1537793 = 1153345) B1153345
theorem B685835 : Blo 682313 685835 := bstep (se 1 (by rfl) ⟨514376, by rfl⟩ : syracuseStep 685835 = 1028753) B1028753
theorem B685847 : Blo 682313 685847 := bstep (se 1 (by rfl) ⟨514385, by rfl⟩ : syracuseStep 685847 = 1028771) B1028771
theorem B685867 : Blo 682313 685867 := bstep (se 1 (by rfl) ⟨514400, by rfl⟩ : syracuseStep 685867 = 1028801) B1028801
theorem B685879 : Blo 682313 685879 := bstep (se 1 (by rfl) ⟨514409, by rfl⟩ : syracuseStep 685879 = 1028819) B1028819
theorem B1111883 : Blo 682313 1111883 := bstep (se 1 (by rfl) ⟨833912, by rfl⟩ : syracuseStep 1111883 = 1667825) B1667825
theorem B685899 : Blo 682313 685899 := bstep (se 1 (by rfl) ⟨514424, by rfl⟩ : syracuseStep 685899 = 1028849) B1028849
theorem B685911 : Blo 682313 685911 := bstep (se 1 (by rfl) ⟨514433, by rfl⟩ : syracuseStep 685911 = 1028867) B1028867
theorem B685931 : Blo 682313 685931 := bstep (se 1 (by rfl) ⟨514448, by rfl⟩ : syracuseStep 685931 = 1028897) B1028897
theorem B685943 : Blo 682313 685943 := bstep (se 1 (by rfl) ⟨514457, by rfl⟩ : syracuseStep 685943 = 1028915) B1028915
theorem B685963 : Blo 682313 685963 := bstep (se 1 (by rfl) ⟨514472, by rfl⟩ : syracuseStep 685963 = 1028945) B1028945
theorem B685975 : Blo 682313 685975 := bstep (se 1 (by rfl) ⟨514481, by rfl⟩ : syracuseStep 685975 = 1028963) B1028963
theorem B685995 : Blo 682313 685995 := bstep (se 1 (by rfl) ⟨514496, by rfl⟩ : syracuseStep 685995 = 1028993) B1028993
theorem B686007 : Blo 682313 686007 := bstep (se 1 (by rfl) ⟨514505, by rfl⟩ : syracuseStep 686007 = 1029011) B1029011
theorem B686027 : Blo 682313 686027 := bstep (se 1 (by rfl) ⟨514520, by rfl⟩ : syracuseStep 686027 = 1029041) B1029041
theorem B686039 : Blo 682313 686039 := bstep (se 1 (by rfl) ⟨514529, by rfl⟩ : syracuseStep 686039 = 1029059) B1029059
theorem B1538009 : Blo 682313 1538009 := bstep (se 2 (by rfl) ⟨576753, by rfl⟩ : syracuseStep 1538009 = 1153507) B1153507
theorem B686059 : Blo 682313 686059 := bstep (se 1 (by rfl) ⟨514544, by rfl⟩ : syracuseStep 686059 = 1029089) B1029089
theorem B686071 : Blo 682313 686071 := bstep (se 1 (by rfl) ⟨514553, by rfl⟩ : syracuseStep 686071 = 1029107) B1029107
theorem B686091 : Blo 682313 686091 := bstep (se 1 (by rfl) ⟨514568, by rfl⟩ : syracuseStep 686091 = 1029137) B1029137
theorem B686103 : Blo 682313 686103 := bstep (se 1 (by rfl) ⟨514577, by rfl⟩ : syracuseStep 686103 = 1029155) B1029155
theorem B686123 : Blo 682313 686123 := bstep (se 1 (by rfl) ⟨514592, by rfl⟩ : syracuseStep 686123 = 1029185) B1029185
theorem B1538099 : Blo 682313 1538099 := bstep (se 1 (by rfl) ⟨1153574, by rfl⟩ : syracuseStep 1538099 = 2307149) B2307149
theorem B686135 : Blo 682313 686135 := bstep (se 1 (by rfl) ⟨514601, by rfl⟩ : syracuseStep 686135 = 1029203) B1029203
theorem B686155 : Blo 682313 686155 := bstep (se 1 (by rfl) ⟨514616, by rfl⟩ : syracuseStep 686155 = 1029233) B1029233
theorem B1538135 : Blo 682313 1538135 := bstep (se 1 (by rfl) ⟨1153601, by rfl⟩ : syracuseStep 1538135 = 2307203) B2307203
theorem B686167 : Blo 682313 686167 := bstep (se 1 (by rfl) ⟨514625, by rfl⟩ : syracuseStep 686167 = 1029251) B1029251
theorem B686187 : Blo 682313 686187 := bstep (se 1 (by rfl) ⟨514640, by rfl⟩ : syracuseStep 686187 = 1029281) B1029281
theorem B686199 : Blo 682313 686199 := bstep (se 1 (by rfl) ⟨514649, by rfl⟩ : syracuseStep 686199 = 1029299) B1029299
theorem B686219 : Blo 682313 686219 := bstep (se 1 (by rfl) ⟨514664, by rfl⟩ : syracuseStep 686219 = 1029329) B1029329
theorem B686231 : Blo 682313 686231 := bstep (se 1 (by rfl) ⟨514673, by rfl⟩ : syracuseStep 686231 = 1029347) B1029347
theorem B686251 : Blo 682313 686251 := bstep (se 1 (by rfl) ⟨514688, by rfl⟩ : syracuseStep 686251 = 1029377) B1029377
theorem B686263 : Blo 682313 686263 := bstep (se 1 (by rfl) ⟨514697, by rfl⟩ : syracuseStep 686263 = 1029395) B1029395
theorem B686283 : Blo 682313 686283 := bstep (se 1 (by rfl) ⟨514712, by rfl⟩ : syracuseStep 686283 = 1029425) B1029425
theorem B686295 : Blo 682313 686295 := bstep (se 1 (by rfl) ⟨514721, by rfl⟩ : syracuseStep 686295 = 1029443) B1029443
theorem B1538315 : Blo 682313 1538315 := bstep (se 1 (by rfl) ⟨1153736, by rfl⟩ : syracuseStep 1538315 = 2307473) B2307473
theorem B1538369 : Blo 682313 1538369 := bstep (se 2 (by rfl) ⟨576888, by rfl⟩ : syracuseStep 1538369 = 1153777) B1153777
theorem B1735091 : Blo 682313 1735091 := bstep (se 1 (by rfl) ⟨1301318, by rfl⟩ : syracuseStep 1735091 = 2602637) B2602637
theorem B1538585 : Blo 682313 1538585 := bstep (se 2 (by rfl) ⟨576969, by rfl⟩ : syracuseStep 1538585 = 1153939) B1153939
theorem B2914861 : Blo 682313 2914861 := bstep (se 3 (by rfl) ⟨546536, by rfl⟩ : syracuseStep 2914861 = 1093073) B1093073
theorem B2226781 : Blo 682313 2226781 := bstep (se 3 (by rfl) ⟨417521, by rfl⟩ : syracuseStep 2226781 = 835043) B835043
theorem B1538675 : Blo 682313 1538675 := bstep (se 1 (by rfl) ⟨1154006, by rfl⟩ : syracuseStep 1538675 = 2308013) B2308013
theorem B1538711 : Blo 682313 1538711 := bstep (se 1 (by rfl) ⟨1154033, by rfl⟩ : syracuseStep 1538711 = 2308067) B2308067
theorem B8321741 : Blo 682313 8321741 := bstep (se 3 (by rfl) ⟨1560326, by rfl⟩ : syracuseStep 8321741 = 3120653) B3120653
theorem B3472145 : Blo 682313 3472145 := bstep (se 2 (by rfl) ⟨1302054, by rfl⟩ : syracuseStep 3472145 = 2604109) B2604109
theorem B1538891 : Blo 682313 1538891 := bstep (se 1 (by rfl) ⟨1154168, by rfl⟩ : syracuseStep 1538891 = 2308337) B2308337
theorem B1538945 : Blo 682313 1538945 := bstep (se 2 (by rfl) ⟨577104, by rfl⟩ : syracuseStep 1538945 = 1154209) B1154209
theorem B2915203 : Blo 682313 2915203 := bstep (se 1 (by rfl) ⟨2186402, by rfl⟩ : syracuseStep 2915203 = 4372805) B4372805
theorem B3472307 : Blo 682313 3472307 := bstep (se 1 (by rfl) ⟨2604230, by rfl⟩ : syracuseStep 3472307 = 5208461) B5208461
theorem B1735627 : Blo 682313 1735627 := bstep (se 1 (by rfl) ⟨1301720, by rfl⟩ : syracuseStep 1735627 = 2603441) B2603441
theorem B2849867 : Blo 682313 2849867 := bstep (se 1 (by rfl) ⟨2137400, by rfl⟩ : syracuseStep 2849867 = 4274801) B4274801
theorem B1539161 : Blo 682313 1539161 := bstep (se 2 (by rfl) ⟨577185, by rfl⟩ : syracuseStep 1539161 = 1154371) B1154371
theorem B1735769 : Blo 682313 1735769 := bstep (se 2 (by rfl) ⟨650913, by rfl⟩ : syracuseStep 1735769 = 1301827) B1301827
theorem B1539251 : Blo 682313 1539251 := bstep (se 1 (by rfl) ⟨1154438, by rfl⟩ : syracuseStep 1539251 = 2308877) B2308877
theorem B1539287 : Blo 682313 1539287 := bstep (se 1 (by rfl) ⟨1154465, by rfl⟩ : syracuseStep 1539287 = 2308931) B2308931
theorem B1539467 : Blo 682313 1539467 := bstep (se 1 (by rfl) ⟨1154600, by rfl⟩ : syracuseStep 1539467 = 2309201) B2309201
theorem B1539521 : Blo 682313 1539521 := bstep (se 2 (by rfl) ⟨577320, by rfl⟩ : syracuseStep 1539521 = 1154641) B1154641
theorem B1539737 : Blo 682313 1539737 := bstep (se 2 (by rfl) ⟨577401, by rfl⟩ : syracuseStep 1539737 = 1154803) B1154803
theorem B1539827 : Blo 682313 1539827 := bstep (se 1 (by rfl) ⟨1154870, by rfl⟩ : syracuseStep 1539827 = 2309741) B2309741
theorem B1539863 : Blo 682313 1539863 := bstep (se 1 (by rfl) ⟨1154897, by rfl⟩ : syracuseStep 1539863 = 2309795) B2309795
theorem B2916161 : Blo 682313 2916161 := bstep (se 2 (by rfl) ⟨1093560, by rfl⟩ : syracuseStep 2916161 = 2187121) B2187121
theorem B1736599 : Blo 682313 1736599 := bstep (se 1 (by rfl) ⟨1302449, by rfl⟩ : syracuseStep 1736599 = 2604899) B2604899
theorem B1540043 : Blo 682313 1540043 := bstep (se 1 (by rfl) ⟨1155032, by rfl⟩ : syracuseStep 1540043 = 2310065) B2310065
theorem B3112921 : Blo 682313 3112921 := bstep (se 2 (by rfl) ⟨1167345, by rfl⟩ : syracuseStep 3112921 = 2334691) B2334691
theorem B3342397 : Blo 682313 3342397 := bstep (se 3 (by rfl) ⟨626699, by rfl⟩ : syracuseStep 3342397 = 1253399) B1253399
theorem B1540367 : Blo 682313 1540367 := bstep (se 1 (by rfl) ⟨1155275, by rfl⟩ : syracuseStep 1540367 = 2310551) B2310551
theorem B1540385 : Blo 682313 1540385 := bstep (se 2 (by rfl) ⟨577644, by rfl⟩ : syracuseStep 1540385 = 1155289) B1155289
theorem B1442107 : Blo 682313 1442107 := bstep (se 1 (by rfl) ⟨1081580, by rfl⟩ : syracuseStep 1442107 = 2163161) B2163161
theorem B8749457 : Blo 682313 8749457 := bstep (se 2 (by rfl) ⟨3281046, by rfl⟩ : syracuseStep 8749457 = 6562093) B6562093
theorem B1737227 : Blo 682313 1737227 := bstep (se 1 (by rfl) ⟨1302920, by rfl⟩ : syracuseStep 1737227 = 2605841) B2605841
theorem B1540727 : Blo 682313 1540727 := bstep (se 1 (by rfl) ⟨1155545, by rfl⟩ : syracuseStep 1540727 = 2311091) B2311091
theorem B4391617 : Blo 682313 4391617 := bstep (se 2 (by rfl) ⟨1646856, by rfl⟩ : syracuseStep 4391617 = 3293713) B3293713
theorem B1540907 : Blo 682313 1540907 := bstep (se 1 (by rfl) ⟨1155680, by rfl⟩ : syracuseStep 1540907 = 2311361) B2311361
theorem B1541267 : Blo 682313 1541267 := bstep (se 1 (by rfl) ⟨1155950, by rfl⟩ : syracuseStep 1541267 = 2311901) B2311901
theorem B3703981 : Blo 682313 3703981 := bstep (se 3 (by rfl) ⟨694496, by rfl⟩ : syracuseStep 3703981 = 1388993) B1388993
theorem B1541321 : Blo 682313 1541321 := bstep (se 2 (by rfl) ⟨577995, by rfl⟩ : syracuseStep 1541321 = 1155991) B1155991
theorem B68257349 : Blo 682313 68257349 := bstep (se 4 (by rfl) ⟨6399126, by rfl⟩ : syracuseStep 68257349 = 12798253) B12798253
theorem B36079181 : Blo 682313 36079181 := bstep (se 3 (by rfl) ⟨6764846, by rfl⟩ : syracuseStep 36079181 = 13529693) B13529693
theorem B1640225 : Blo 682313 1640225 := bstep (se 2 (by rfl) ⟨615084, by rfl⟩ : syracuseStep 1640225 = 1230169) B1230169
theorem B2918177 : Blo 682313 2918177 := bstep (se 2 (by rfl) ⟨1094316, by rfl⟩ : syracuseStep 2918177 = 2188633) B2188633
theorem B821035 : Blo 682313 821035 := bstep (se 1 (by rfl) ⟨615776, by rfl⟩ : syracuseStep 821035 = 1231553) B1231553
theorem B3901243 : Blo 682313 3901243 := bstep (se 1 (by rfl) ⟨2925932, by rfl⟩ : syracuseStep 3901243 = 5851865) B5851865
theorem B1542023 : Blo 682313 1542023 := bstep (se 1 (by rfl) ⟨1156517, by rfl⟩ : syracuseStep 1542023 = 2313035) B2313035
theorem B1542203 : Blo 682313 1542203 := bstep (se 1 (by rfl) ⟨1156652, by rfl⟩ : syracuseStep 1542203 = 2313305) B2313305
theorem B1542329 : Blo 682313 1542329 := bstep (se 2 (by rfl) ⟨578373, by rfl⟩ : syracuseStep 1542329 = 1156747) B1156747
theorem B4163987 : Blo 682313 4163987 := bstep (se 1 (by rfl) ⟨3122990, by rfl⟩ : syracuseStep 4163987 = 6245981) B6245981
theorem B1542671 : Blo 682313 1542671 := bstep (se 1 (by rfl) ⟨1157003, by rfl⟩ : syracuseStep 1542671 = 2314007) B2314007
theorem B2591261 : Blo 682313 2591261 := bstep (se 3 (by rfl) ⟨485861, by rfl⟩ : syracuseStep 2591261 = 971723) B971723
theorem B1542689 : Blo 682313 1542689 := bstep (se 2 (by rfl) ⟨578508, by rfl⟩ : syracuseStep 1542689 = 1157017) B1157017
theorem B1543031 : Blo 682313 1543031 := bstep (se 1 (by rfl) ⟨1157273, by rfl⟩ : syracuseStep 1543031 = 2314547) B2314547
theorem B2460683 : Blo 682313 2460683 := bstep (se 1 (by rfl) ⟨1845512, by rfl⟩ : syracuseStep 2460683 = 3691025) B3691025
theorem B1543211 : Blo 682313 1543211 := bstep (se 1 (by rfl) ⟨1157408, by rfl⟩ : syracuseStep 1543211 = 2314817) B2314817
theorem B822415 : Blo 682313 822415 := bstep (se 1 (by rfl) ⟨616811, by rfl⟩ : syracuseStep 822415 = 1233623) B1233623
theorem B2591945 : Blo 682313 2591945 := bstep (se 2 (by rfl) ⟨971979, by rfl⟩ : syracuseStep 2591945 = 1943959) B1943959
theorem B3902701 : Blo 682313 3902701 := bstep (se 3 (by rfl) ⟨731756, by rfl⟩ : syracuseStep 3902701 = 1463513) B1463513
theorem B1543571 : Blo 682313 1543571 := bstep (se 1 (by rfl) ⟨1157678, by rfl⟩ : syracuseStep 1543571 = 2315357) B2315357
theorem B1543625 : Blo 682313 1543625 := bstep (se 2 (by rfl) ⟨578859, by rfl⟩ : syracuseStep 1543625 = 1157719) B1157719
theorem B823303 : Blo 682313 823303 := bstep (se 1 (by rfl) ⟨617477, by rfl⟩ : syracuseStep 823303 = 1234955) B1234955
theorem B2920535 : Blo 682313 2920535 := bstep (se 1 (by rfl) ⟨2190401, by rfl⟩ : syracuseStep 2920535 = 4380803) B4380803
theorem B692615 : Blo 682313 692615 := bstep (se 1 (by rfl) ⟨519461, by rfl⟩ : syracuseStep 692615 = 1038923) B1038923
theorem B3281411 : Blo 682313 3281411 := bstep (se 1 (by rfl) ⟨2461058, by rfl⟩ : syracuseStep 3281411 = 4922117) B4922117
theorem B1151759 : Blo 682313 1151759 := bstep (se 1 (by rfl) ⟨863819, by rfl⟩ : syracuseStep 1151759 = 1727639) B1727639
theorem B26645285 : Blo 682313 26645285 := bstep (se 4 (by rfl) ⟨2497995, by rfl⟩ : syracuseStep 26645285 = 4995991) B4995991
theorem B2593721 : Blo 682313 2593721 := bstep (se 2 (by rfl) ⟨972645, by rfl⟩ : syracuseStep 2593721 = 1945291) B1945291
theorem B3904685 : Blo 682313 3904685 := bstep (se 3 (by rfl) ⟨732128, by rfl⟩ : syracuseStep 3904685 = 1464257) B1464257
theorem B1152299 : Blo 682313 1152299 := bstep (se 1 (by rfl) ⟨864224, by rfl⟩ : syracuseStep 1152299 = 1728449) B1728449
theorem B923081 : Blo 682313 923081 := bstep (se 2 (by rfl) ⟨346155, by rfl⟩ : syracuseStep 923081 = 692311) B692311
theorem B13342157 : Blo 682313 13342157 := bstep (se 3 (by rfl) ⟨2501654, by rfl⟩ : syracuseStep 13342157 = 5003309) B5003309
theorem B8001125 : Blo 682313 8001125 := bstep (se 4 (by rfl) ⟨750105, by rfl⟩ : syracuseStep 8001125 = 1500211) B1500211
theorem B1152697 : Blo 682313 1152697 := bstep (se 2 (by rfl) ⟨432261, by rfl⟩ : syracuseStep 1152697 = 864523) B864523
theorem B7804673 : Blo 682313 7804673 := bstep (se 2 (by rfl) ⟨2926752, by rfl⟩ : syracuseStep 7804673 = 5853505) B5853505
theorem B923833 : Blo 682313 923833 := bstep (se 2 (by rfl) ⟨346437, by rfl⟩ : syracuseStep 923833 = 692875) B692875
theorem B2464015 : Blo 682313 2464015 := bstep (se 1 (by rfl) ⟨1848011, by rfl⟩ : syracuseStep 2464015 = 3696023) B3696023
theorem B7411985 : Blo 682313 7411985 := bstep (se 2 (by rfl) ⟨2779494, by rfl⟩ : syracuseStep 7411985 = 5558989) B5558989
theorem B1153399 : Blo 682313 1153399 := bstep (se 1 (by rfl) ⟨865049, by rfl⟩ : syracuseStep 1153399 = 1730099) B1730099
theorem B5282233 : Blo 682313 5282233 := bstep (se 2 (by rfl) ⟨1980837, by rfl⟩ : syracuseStep 5282233 = 3961675) B3961675
theorem B4168145 : Blo 682313 4168145 := bstep (se 2 (by rfl) ⟨1563054, by rfl⟩ : syracuseStep 4168145 = 3126109) B3126109
theorem B1153595 : Blo 682313 1153595 := bstep (se 1 (by rfl) ⟨865196, by rfl⟩ : syracuseStep 1153595 = 1730393) B1730393
theorem B1317665 : Blo 682313 1317665 := bstep (se 2 (by rfl) ⟨494124, by rfl⟩ : syracuseStep 1317665 = 988249) B988249
theorem B1153993 : Blo 682313 1153993 := bstep (se 2 (by rfl) ⟨432747, by rfl⟩ : syracuseStep 1153993 = 865495) B865495
theorem B1023479 : Blo 682313 1023479 := bstep (se 1 (by rfl) ⟨767609, by rfl⟩ : syracuseStep 1023479 = 1535219) B1535219
theorem B3907075 : Blo 682313 3907075 := bstep (se 1 (by rfl) ⟨2930306, by rfl⟩ : syracuseStep 3907075 = 5860613) B5860613
theorem B1023503 : Blo 682313 1023503 := bstep (se 1 (by rfl) ⟨767627, by rfl⟩ : syracuseStep 1023503 = 1535255) B1535255
theorem B1023545 : Blo 682313 1023545 := bstep (se 2 (by rfl) ⟨383829, by rfl⟩ : syracuseStep 1023545 = 767659) B767659
theorem B2465399 : Blo 682313 2465399 := bstep (se 1 (by rfl) ⟨1849049, by rfl⟩ : syracuseStep 2465399 = 3698099) B3698099
theorem B1023623 : Blo 682313 1023623 := bstep (se 1 (by rfl) ⟨767717, by rfl⟩ : syracuseStep 1023623 = 1535435) B1535435
theorem B1154695 : Blo 682313 1154695 := bstep (se 1 (by rfl) ⟨866021, by rfl⟩ : syracuseStep 1154695 = 1732043) B1732043
theorem B1023659 : Blo 682313 1023659 := bstep (se 1 (by rfl) ⟨767744, by rfl⟩ : syracuseStep 1023659 = 1535489) B1535489
theorem B1023689 : Blo 682313 1023689 := bstep (se 2 (by rfl) ⟨383883, by rfl⟩ : syracuseStep 1023689 = 767767) B767767
theorem B1023803 : Blo 682313 1023803 := bstep (se 1 (by rfl) ⟨767852, by rfl⟩ : syracuseStep 1023803 = 1535705) B1535705
theorem B1023863 : Blo 682313 1023863 := bstep (se 1 (by rfl) ⟨767897, by rfl⟩ : syracuseStep 1023863 = 1535795) B1535795
theorem B1023887 : Blo 682313 1023887 := bstep (se 1 (by rfl) ⟨767915, by rfl⟩ : syracuseStep 1023887 = 1535831) B1535831
theorem B1023929 : Blo 682313 1023929 := bstep (se 2 (by rfl) ⟨383973, by rfl⟩ : syracuseStep 1023929 = 767947) B767947
theorem B1024007 : Blo 682313 1024007 := bstep (se 1 (by rfl) ⟨768005, by rfl⟩ : syracuseStep 1024007 = 1536011) B1536011
theorem B8331275 : Blo 682313 8331275 := bstep (se 1 (by rfl) ⟨6248456, by rfl⟩ : syracuseStep 8331275 = 12496913) B12496913
theorem B1024043 : Blo 682313 1024043 := bstep (se 1 (by rfl) ⟨768032, by rfl⟩ : syracuseStep 1024043 = 1536065) B1536065
theorem B1024073 : Blo 682313 1024073 := bstep (se 2 (by rfl) ⟨384027, by rfl⟩ : syracuseStep 1024073 = 768055) B768055
theorem B1024187 : Blo 682313 1024187 := bstep (se 1 (by rfl) ⟨768140, by rfl⟩ : syracuseStep 1024187 = 1536281) B1536281
theorem B1024247 : Blo 682313 1024247 := bstep (se 1 (by rfl) ⟨768185, by rfl⟩ : syracuseStep 1024247 = 1536371) B1536371
theorem B1024271 : Blo 682313 1024271 := bstep (se 1 (by rfl) ⟨768203, by rfl⟩ : syracuseStep 1024271 = 1536407) B1536407
theorem B1155343 : Blo 682313 1155343 := bstep (se 1 (by rfl) ⟨866507, by rfl⟩ : syracuseStep 1155343 = 1733015) B1733015
theorem B1024313 : Blo 682313 1024313 := bstep (se 2 (by rfl) ⟨384117, by rfl⟩ : syracuseStep 1024313 = 768235) B768235
theorem B926011 : Blo 682313 926011 := bstep (se 1 (by rfl) ⟨694508, by rfl⟩ : syracuseStep 926011 = 1389017) B1389017
theorem B1024391 : Blo 682313 1024391 := bstep (se 1 (by rfl) ⟨768293, by rfl⟩ : syracuseStep 1024391 = 1536587) B1536587
theorem B1024427 : Blo 682313 1024427 := bstep (se 1 (by rfl) ⟨768320, by rfl⟩ : syracuseStep 1024427 = 1536641) B1536641
theorem B2597305 : Blo 682313 2597305 := bstep (se 2 (by rfl) ⟨973989, by rfl⟩ : syracuseStep 2597305 = 1947979) B1947979
theorem B1024457 : Blo 682313 1024457 := bstep (se 2 (by rfl) ⟨384171, by rfl⟩ : syracuseStep 1024457 = 768343) B768343
theorem B1024571 : Blo 682313 1024571 := bstep (se 1 (by rfl) ⟨768428, by rfl⟩ : syracuseStep 1024571 = 1536857) B1536857
theorem B7807589 : Blo 682313 7807589 := bstep (se 4 (by rfl) ⟨731961, by rfl⟩ : syracuseStep 7807589 = 1463923) B1463923
theorem B1024631 : Blo 682313 1024631 := bstep (se 1 (by rfl) ⟨768473, by rfl⟩ : syracuseStep 1024631 = 1536947) B1536947
theorem B1024655 : Blo 682313 1024655 := bstep (se 1 (by rfl) ⟨768491, by rfl⟩ : syracuseStep 1024655 = 1536983) B1536983
theorem B1024697 : Blo 682313 1024697 := bstep (se 2 (by rfl) ⟨384261, by rfl⟩ : syracuseStep 1024697 = 768523) B768523
theorem B1024775 : Blo 682313 1024775 := bstep (se 1 (by rfl) ⟨768581, by rfl⟩ : syracuseStep 1024775 = 1537163) B1537163
theorem B1024811 : Blo 682313 1024811 := bstep (se 1 (by rfl) ⟨768608, by rfl⟩ : syracuseStep 1024811 = 1537217) B1537217
theorem B1155883 : Blo 682313 1155883 := bstep (se 1 (by rfl) ⟨866912, by rfl⟩ : syracuseStep 1155883 = 1733825) B1733825
theorem B1024841 : Blo 682313 1024841 := bstep (se 2 (by rfl) ⟨384315, by rfl⟩ : syracuseStep 1024841 = 768631) B768631
theorem B12624821 : Blo 682313 12624821 := bstep (se 5 (by rfl) ⟨591788, by rfl⟩ : syracuseStep 12624821 = 1183577) B1183577
theorem B1156025 : Blo 682313 1156025 := bstep (se 2 (by rfl) ⟨433509, by rfl⟩ : syracuseStep 1156025 = 867019) B867019
theorem B1024955 : Blo 682313 1024955 := bstep (se 1 (by rfl) ⟨768716, by rfl⟩ : syracuseStep 1024955 = 1537433) B1537433
theorem B1025015 : Blo 682313 1025015 := bstep (se 1 (by rfl) ⟨768761, by rfl⟩ : syracuseStep 1025015 = 1537523) B1537523
theorem B1025039 : Blo 682313 1025039 := bstep (se 1 (by rfl) ⟨768779, by rfl⟩ : syracuseStep 1025039 = 1537559) B1537559
theorem B926735 : Blo 682313 926735 := bstep (se 1 (by rfl) ⟨695051, by rfl⟩ : syracuseStep 926735 = 1390103) B1390103
theorem B3941405 : Blo 682313 3941405 := bstep (se 3 (by rfl) ⟨739013, by rfl⟩ : syracuseStep 3941405 = 1478027) B1478027
theorem B1025081 : Blo 682313 1025081 := bstep (se 2 (by rfl) ⟨384405, by rfl⟩ : syracuseStep 1025081 = 768811) B768811
theorem B1025159 : Blo 682313 1025159 := bstep (se 1 (by rfl) ⟨768869, by rfl⟩ : syracuseStep 1025159 = 1537739) B1537739
theorem B1025195 : Blo 682313 1025195 := bstep (se 1 (by rfl) ⟨768896, by rfl⟩ : syracuseStep 1025195 = 1537793) B1537793
theorem B1025225 : Blo 682313 1025225 := bstep (se 2 (by rfl) ⟨384459, by rfl⟩ : syracuseStep 1025225 = 768919) B768919
theorem B1025339 : Blo 682313 1025339 := bstep (se 1 (by rfl) ⟨769004, by rfl⟩ : syracuseStep 1025339 = 1538009) B1538009
theorem B927049 : Blo 682313 927049 := bstep (se 2 (by rfl) ⟨347643, by rfl⟩ : syracuseStep 927049 = 695287) B695287
theorem B1025399 : Blo 682313 1025399 := bstep (se 1 (by rfl) ⟨769049, by rfl⟩ : syracuseStep 1025399 = 1538099) B1538099
theorem B1025423 : Blo 682313 1025423 := bstep (se 1 (by rfl) ⟨769067, by rfl⟩ : syracuseStep 1025423 = 1538135) B1538135
theorem B1025465 : Blo 682313 1025465 := bstep (se 2 (by rfl) ⟨384549, by rfl⟩ : syracuseStep 1025465 = 769099) B769099
theorem B1025543 : Blo 682313 1025543 := bstep (se 1 (by rfl) ⟨769157, by rfl⟩ : syracuseStep 1025543 = 1538315) B1538315
theorem B2303531 : Blo 682313 2303531 := bstep (se 1 (by rfl) ⟨1727648, by rfl⟩ : syracuseStep 2303531 = 3455297) B3455297
theorem B1025579 : Blo 682313 1025579 := bstep (se 1 (by rfl) ⟨769184, by rfl⟩ : syracuseStep 1025579 = 1538369) B1538369
theorem B1025609 : Blo 682313 1025609 := bstep (se 2 (by rfl) ⟨384603, by rfl⟩ : syracuseStep 1025609 = 769207) B769207
theorem B1156727 : Blo 682313 1156727 := bstep (se 1 (by rfl) ⟨867545, by rfl⟩ : syracuseStep 1156727 = 1735091) B1735091
theorem B1025723 : Blo 682313 1025723 := bstep (se 1 (by rfl) ⟨769292, by rfl⟩ : syracuseStep 1025723 = 1538585) B1538585
theorem B1025783 : Blo 682313 1025783 := bstep (se 1 (by rfl) ⟨769337, by rfl⟩ : syracuseStep 1025783 = 1538675) B1538675
theorem B1025807 : Blo 682313 1025807 := bstep (se 1 (by rfl) ⟨769355, by rfl⟩ : syracuseStep 1025807 = 1538711) B1538711
theorem B5547827 : Blo 682313 5547827 := bstep (se 1 (by rfl) ⟨4160870, by rfl⟩ : syracuseStep 5547827 = 8321741) B8321741
theorem B1025849 : Blo 682313 1025849 := bstep (se 2 (by rfl) ⟨384693, by rfl⟩ : syracuseStep 1025849 = 769387) B769387
theorem B63252323 : Blo 682313 63252323 := bstep (se 1 (by rfl) ⟨47439242, by rfl⟩ : syracuseStep 63252323 = 94878485) B94878485
theorem B1025927 : Blo 682313 1025927 := bstep (se 1 (by rfl) ⟨769445, by rfl⟩ : syracuseStep 1025927 = 1538891) B1538891
theorem B1025963 : Blo 682313 1025963 := bstep (se 1 (by rfl) ⟨769472, by rfl⟩ : syracuseStep 1025963 = 1538945) B1538945
theorem B1025993 : Blo 682313 1025993 := bstep (se 2 (by rfl) ⟨384747, by rfl⟩ : syracuseStep 1025993 = 769495) B769495
theorem B16623629 : Blo 682313 16623629 := bstep (se 3 (by rfl) ⟨3116930, by rfl⟩ : syracuseStep 16623629 = 6233861) B6233861
theorem B7809047 : Blo 682313 7809047 := bstep (se 1 (by rfl) ⟨5856785, by rfl⟩ : syracuseStep 7809047 = 11713571) B11713571
theorem B1026107 : Blo 682313 1026107 := bstep (se 1 (by rfl) ⟨769580, by rfl⟩ : syracuseStep 1026107 = 1539161) B1539161
theorem B1157179 : Blo 682313 1157179 := bstep (se 1 (by rfl) ⟨867884, by rfl⟩ : syracuseStep 1157179 = 1735769) B1735769
theorem B1026167 : Blo 682313 1026167 := bstep (se 1 (by rfl) ⟨769625, by rfl⟩ : syracuseStep 1026167 = 1539251) B1539251
theorem B1648759 : Blo 682313 1648759 := bstep (se 1 (by rfl) ⟨1236569, by rfl⟩ : syracuseStep 1648759 = 2473139) B2473139
theorem B1026191 : Blo 682313 1026191 := bstep (se 1 (by rfl) ⟨769643, by rfl⟩ : syracuseStep 1026191 = 1539287) B1539287
theorem B5843117 : Blo 682313 5843117 := bstep (se 3 (by rfl) ⟨1095584, by rfl⟩ : syracuseStep 5843117 = 2191169) B2191169
theorem B1026233 : Blo 682313 1026233 := bstep (se 2 (by rfl) ⟨384837, by rfl⟩ : syracuseStep 1026233 = 769675) B769675
theorem B1157321 : Blo 682313 1157321 := bstep (se 2 (by rfl) ⟨433995, by rfl⟩ : syracuseStep 1157321 = 867991) B867991
theorem B1026311 : Blo 682313 1026311 := bstep (se 1 (by rfl) ⟨769733, by rfl⟩ : syracuseStep 1026311 = 1539467) B1539467
theorem B1026347 : Blo 682313 1026347 := bstep (se 1 (by rfl) ⟨769760, by rfl⟩ : syracuseStep 1026347 = 1539521) B1539521
theorem B1026377 : Blo 682313 1026377 := bstep (se 2 (by rfl) ⟨384891, by rfl⟩ : syracuseStep 1026377 = 769783) B769783
theorem B3287411 : Blo 682313 3287411 := bstep (se 1 (by rfl) ⟨2465558, by rfl⟩ : syracuseStep 3287411 = 4931117) B4931117
theorem B1943993 : Blo 682313 1943993 := bstep (se 2 (by rfl) ⟨728997, by rfl⟩ : syracuseStep 1943993 = 1457995) B1457995
theorem B1026491 : Blo 682313 1026491 := bstep (se 1 (by rfl) ⟨769868, by rfl⟩ : syracuseStep 1026491 = 1539737) B1539737
theorem B5188049 : Blo 682313 5188049 := bstep (se 2 (by rfl) ⟨1945518, by rfl⟩ : syracuseStep 5188049 = 3891037) B3891037
theorem B1026551 : Blo 682313 1026551 := bstep (se 1 (by rfl) ⟨769913, by rfl⟩ : syracuseStep 1026551 = 1539827) B1539827
theorem B1026575 : Blo 682313 1026575 := bstep (se 1 (by rfl) ⟨769931, by rfl⟩ : syracuseStep 1026575 = 1539863) B1539863
theorem B1944107 : Blo 682313 1944107 := bstep (se 1 (by rfl) ⟨1458080, by rfl⟩ : syracuseStep 1944107 = 2916161) B2916161
theorem B1026617 : Blo 682313 1026617 := bstep (se 2 (by rfl) ⟨384981, by rfl⟩ : syracuseStep 1026617 = 769963) B769963
theorem B1026695 : Blo 682313 1026695 := bstep (se 1 (by rfl) ⟨770021, by rfl⟩ : syracuseStep 1026695 = 1540043) B1540043
theorem B731791 : Blo 682313 731791 := bstep (se 1 (by rfl) ⟨548843, by rfl⟩ : syracuseStep 731791 = 1097687) B1097687
theorem B1026731 : Blo 682313 1026731 := bstep (se 1 (by rfl) ⟨770048, by rfl⟩ : syracuseStep 1026731 = 1540097) B1540097
theorem B1026761 : Blo 682313 1026761 := bstep (se 2 (by rfl) ⟨385035, by rfl⟩ : syracuseStep 1026761 = 770071) B770071
theorem B25340633 : Blo 682313 25340633 := bstep (se 2 (by rfl) ⟨9502737, by rfl⟩ : syracuseStep 25340633 = 19005475) B19005475
theorem B1387307 : Blo 682313 1387307 := bstep (se 1 (by rfl) ⟨1040480, by rfl⟩ : syracuseStep 1387307 = 2080961) B2080961
theorem B2304827 : Blo 682313 2304827 := bstep (se 1 (by rfl) ⟨1728620, by rfl⟩ : syracuseStep 2304827 = 3457241) B3457241
theorem B1026875 : Blo 682313 1026875 := bstep (se 1 (by rfl) ⟨770156, by rfl⟩ : syracuseStep 1026875 = 1540313) B1540313
theorem B7023449 : Blo 682313 7023449 := bstep (se 2 (by rfl) ⟨2633793, by rfl⟩ : syracuseStep 7023449 = 5267587) B5267587
theorem B1026935 : Blo 682313 1026935 := bstep (se 1 (by rfl) ⟨770201, by rfl⟩ : syracuseStep 1026935 = 1540403) B1540403
theorem B1158023 : Blo 682313 1158023 := bstep (se 1 (by rfl) ⟨868517, by rfl⟩ : syracuseStep 1158023 = 1737035) B1737035
theorem B1026959 : Blo 682313 1026959 := bstep (se 1 (by rfl) ⟨770219, by rfl⟩ : syracuseStep 1026959 = 1540439) B1540439
theorem B1027001 : Blo 682313 1027001 := bstep (se 2 (by rfl) ⟨385125, by rfl⟩ : syracuseStep 1027001 = 770251) B770251
theorem B1027079 : Blo 682313 1027079 := bstep (se 1 (by rfl) ⟨770309, by rfl⟩ : syracuseStep 1027079 = 1540619) B1540619
theorem B1027115 : Blo 682313 1027115 := bstep (se 1 (by rfl) ⟨770336, by rfl⟩ : syracuseStep 1027115 = 1540673) B1540673
theorem B1027145 : Blo 682313 1027145 := bstep (se 2 (by rfl) ⟨385179, by rfl⟩ : syracuseStep 1027145 = 770359) B770359
theorem B1027259 : Blo 682313 1027259 := bstep (se 1 (by rfl) ⟨770444, by rfl⟩ : syracuseStep 1027259 = 1540889) B1540889
theorem B1027319 : Blo 682313 1027319 := bstep (se 1 (by rfl) ⟨770489, by rfl⟩ : syracuseStep 1027319 = 1540979) B1540979
theorem B2600207 : Blo 682313 2600207 := bstep (se 1 (by rfl) ⟨1950155, by rfl⟩ : syracuseStep 2600207 = 3900311) B3900311
theorem B1027343 : Blo 682313 1027343 := bstep (se 1 (by rfl) ⟨770507, by rfl⟩ : syracuseStep 1027343 = 1541015) B1541015
theorem B2305313 : Blo 682313 2305313 := bstep (se 2 (by rfl) ⟨864492, by rfl⟩ : syracuseStep 2305313 = 1728985) B1728985
theorem B1027385 : Blo 682313 1027385 := bstep (se 2 (by rfl) ⟨385269, by rfl⟩ : syracuseStep 1027385 = 770539) B770539
theorem B1027463 : Blo 682313 1027463 := bstep (se 1 (by rfl) ⟨770597, by rfl⟩ : syracuseStep 1027463 = 1541195) B1541195
theorem B1027499 : Blo 682313 1027499 := bstep (se 1 (by rfl) ⟨770624, by rfl⟩ : syracuseStep 1027499 = 1541249) B1541249
theorem B1027529 : Blo 682313 1027529 := bstep (se 2 (by rfl) ⟨385323, by rfl⟩ : syracuseStep 1027529 = 770647) B770647
theorem B1027643 : Blo 682313 1027643 := bstep (se 1 (by rfl) ⟨770732, by rfl⟩ : syracuseStep 1027643 = 1541465) B1541465
theorem B1027703 : Blo 682313 1027703 := bstep (se 1 (by rfl) ⟨770777, by rfl⟩ : syracuseStep 1027703 = 1541555) B1541555
theorem B1027727 : Blo 682313 1027727 := bstep (se 1 (by rfl) ⟨770795, by rfl⟩ : syracuseStep 1027727 = 1541591) B1541591
theorem B1945235 : Blo 682313 1945235 := bstep (se 1 (by rfl) ⟨1458926, by rfl⟩ : syracuseStep 1945235 = 2917853) B2917853
theorem B1027769 : Blo 682313 1027769 := bstep (se 2 (by rfl) ⟨385413, by rfl⟩ : syracuseStep 1027769 = 770827) B770827
theorem B1027847 : Blo 682313 1027847 := bstep (se 1 (by rfl) ⟨770885, by rfl⟩ : syracuseStep 1027847 = 1541771) B1541771
theorem B1027883 : Blo 682313 1027883 := bstep (se 1 (by rfl) ⟨770912, by rfl⟩ : syracuseStep 1027883 = 1541825) B1541825
theorem B1027913 : Blo 682313 1027913 := bstep (se 2 (by rfl) ⟨385467, by rfl⟩ : syracuseStep 1027913 = 770935) B770935
theorem B2305907 : Blo 682313 2305907 := bstep (se 1 (by rfl) ⟨1729430, by rfl⟩ : syracuseStep 2305907 = 3458861) B3458861
theorem B1028027 : Blo 682313 1028027 := bstep (se 1 (by rfl) ⟨771020, by rfl⟩ : syracuseStep 1028027 = 1542041) B1542041
theorem B21016523 : Blo 682313 21016523 := bstep (se 1 (by rfl) ⟨15762392, by rfl⟩ : syracuseStep 21016523 = 31524785) B31524785
theorem B1028087 : Blo 682313 1028087 := bstep (se 1 (by rfl) ⟨771065, by rfl⟩ : syracuseStep 1028087 = 1542131) B1542131
theorem B1028111 : Blo 682313 1028111 := bstep (se 1 (by rfl) ⟨771083, by rfl⟩ : syracuseStep 1028111 = 1542167) B1542167
theorem B3944477 : Blo 682313 3944477 := bstep (se 3 (by rfl) ⟨739589, by rfl⟩ : syracuseStep 3944477 = 1479179) B1479179
theorem B1945633 : Blo 682313 1945633 := bstep (se 2 (by rfl) ⟨729612, by rfl⟩ : syracuseStep 1945633 = 1459225) B1459225
theorem B1028153 : Blo 682313 1028153 := bstep (se 2 (by rfl) ⟨385557, by rfl⟩ : syracuseStep 1028153 = 771115) B771115
theorem B1028231 : Blo 682313 1028231 := bstep (se 1 (by rfl) ⟨771173, by rfl⟩ : syracuseStep 1028231 = 1542347) B1542347
theorem B864427 : Blo 682313 864427 := bstep (se 1 (by rfl) ⟨648320, by rfl⟩ : syracuseStep 864427 = 1296641) B1296641
theorem B1028267 : Blo 682313 1028267 := bstep (se 1 (by rfl) ⟨771200, by rfl⟩ : syracuseStep 1028267 = 1542401) B1542401
theorem B1093817 : Blo 682313 1093817 := bstep (se 2 (by rfl) ⟨410181, by rfl⟩ : syracuseStep 1093817 = 820363) B820363
theorem B1028297 : Blo 682313 1028297 := bstep (se 2 (by rfl) ⟨385611, by rfl⟩ : syracuseStep 1028297 = 771223) B771223
theorem B7516433 : Blo 682313 7516433 := bstep (se 2 (by rfl) ⟨2818662, by rfl⟩ : syracuseStep 7516433 = 5637325) B5637325
theorem B1028411 : Blo 682313 1028411 := bstep (se 1 (by rfl) ⟨771308, by rfl⟩ : syracuseStep 1028411 = 1542617) B1542617
theorem B1028471 : Blo 682313 1028471 := bstep (se 1 (by rfl) ⟨771353, by rfl⟩ : syracuseStep 1028471 = 1542707) B1542707
theorem B1028495 : Blo 682313 1028495 := bstep (se 1 (by rfl) ⟨771371, by rfl⟩ : syracuseStep 1028495 = 1542743) B1542743
theorem B1028537 : Blo 682313 1028537 := bstep (se 2 (by rfl) ⟨385701, by rfl⟩ : syracuseStep 1028537 = 771403) B771403
theorem B1028615 : Blo 682313 1028615 := bstep (se 1 (by rfl) ⟨771461, by rfl⟩ : syracuseStep 1028615 = 1542923) B1542923
theorem B1028651 : Blo 682313 1028651 := bstep (se 1 (by rfl) ⟨771488, by rfl⟩ : syracuseStep 1028651 = 1542977) B1542977
theorem B2929213 : Blo 682313 2929213 := bstep (se 3 (by rfl) ⟨549227, by rfl⟩ : syracuseStep 2929213 = 1098455) B1098455
theorem B1028681 : Blo 682313 1028681 := bstep (se 2 (by rfl) ⟨385755, by rfl⟩ : syracuseStep 1028681 = 771511) B771511
theorem B2077369 : Blo 682313 2077369 := bstep (se 2 (by rfl) ⟨779013, by rfl⟩ : syracuseStep 2077369 = 1558027) B1558027
theorem B1028795 : Blo 682313 1028795 := bstep (se 1 (by rfl) ⟨771596, by rfl⟩ : syracuseStep 1028795 = 1543193) B1543193
theorem B1028855 : Blo 682313 1028855 := bstep (se 1 (by rfl) ⟨771641, by rfl⟩ : syracuseStep 1028855 = 1543283) B1543283
theorem B1028879 : Blo 682313 1028879 := bstep (se 1 (by rfl) ⟨771659, by rfl⟩ : syracuseStep 1028879 = 1543319) B1543319
theorem B1028921 : Blo 682313 1028921 := bstep (se 2 (by rfl) ⟨385845, by rfl⟩ : syracuseStep 1028921 = 771691) B771691
theorem B11678579 : Blo 682313 11678579 := bstep (se 1 (by rfl) ⟨8758934, by rfl⟩ : syracuseStep 11678579 = 17517869) B17517869
theorem B1028999 : Blo 682313 1028999 := bstep (se 1 (by rfl) ⟨771749, by rfl⟩ : syracuseStep 1028999 = 1543499) B1543499
theorem B1946521 : Blo 682313 1946521 := bstep (se 2 (by rfl) ⟨729945, by rfl⟩ : syracuseStep 1946521 = 1459891) B1459891
theorem B1848217 : Blo 682313 1848217 := bstep (se 2 (by rfl) ⟨693081, by rfl⟩ : syracuseStep 1848217 = 1386163) B1386163
theorem B1029035 : Blo 682313 1029035 := bstep (se 1 (by rfl) ⟨771776, by rfl⟩ : syracuseStep 1029035 = 1543553) B1543553
theorem B1029065 : Blo 682313 1029065 := bstep (se 2 (by rfl) ⟨385899, by rfl⟩ : syracuseStep 1029065 = 771799) B771799
theorem B1029179 : Blo 682313 1029179 := bstep (se 1 (by rfl) ⟨771884, by rfl⟩ : syracuseStep 1029179 = 1543769) B1543769
theorem B865399 : Blo 682313 865399 := bstep (se 1 (by rfl) ⟨649049, by rfl⟩ : syracuseStep 865399 = 1298099) B1298099
theorem B1029239 : Blo 682313 1029239 := bstep (se 1 (by rfl) ⟨771929, by rfl⟩ : syracuseStep 1029239 = 1543859) B1543859
theorem B1094791 : Blo 682313 1094791 := bstep (se 1 (by rfl) ⟨821093, by rfl⟩ : syracuseStep 1094791 = 1642187) B1642187
theorem B1029263 : Blo 682313 1029263 := bstep (se 1 (by rfl) ⟨771947, by rfl⟩ : syracuseStep 1029263 = 1543895) B1543895
theorem B1029305 : Blo 682313 1029305 := bstep (se 2 (by rfl) ⟨385989, by rfl⟩ : syracuseStep 1029305 = 771979) B771979
theorem B1029383 : Blo 682313 1029383 := bstep (se 1 (by rfl) ⟨772037, by rfl⟩ : syracuseStep 1029383 = 1544075) B1544075
theorem B1946909 : Blo 682313 1946909 := bstep (se 3 (by rfl) ⟨365045, by rfl⟩ : syracuseStep 1946909 = 730091) B730091
theorem B1029419 : Blo 682313 1029419 := bstep (se 1 (by rfl) ⟨772064, by rfl⟩ : syracuseStep 1029419 = 1544129) B1544129
theorem B1029449 : Blo 682313 1029449 := bstep (se 2 (by rfl) ⟨386043, by rfl⟩ : syracuseStep 1029449 = 772087) B772087
theorem B1095047 : Blo 682313 1095047 := bstep (se 1 (by rfl) ⟨821285, by rfl⟩ : syracuseStep 1095047 = 1642571) B1642571
theorem B2635193 : Blo 682313 2635193 := bstep (se 2 (by rfl) ⟨988197, by rfl⟩ : syracuseStep 2635193 = 1976395) B1976395
theorem B865723 : Blo 682313 865723 := bstep (se 1 (by rfl) ⟨649292, by rfl⟩ : syracuseStep 865723 = 1298585) B1298585
theorem B3454487 : Blo 682313 3454487 := bstep (se 1 (by rfl) ⟨2590865, by rfl⟩ : syracuseStep 3454487 = 5181731) B5181731
theorem B767623 : Blo 682313 767623 := bstep (se 1 (by rfl) ⟨575717, by rfl⟩ : syracuseStep 767623 = 1151435) B1151435
theorem B767803 : Blo 682313 767803 := bstep (se 1 (by rfl) ⟨575852, by rfl⟩ : syracuseStep 767803 = 1151705) B1151705
theorem B1849223 : Blo 682313 1849223 := bstep (se 1 (by rfl) ⟨1386917, by rfl⟩ : syracuseStep 1849223 = 2773835) B2773835
theorem B3291101 : Blo 682313 3291101 := bstep (se 3 (by rfl) ⟨617081, by rfl⟩ : syracuseStep 3291101 = 1234163) B1234163
theorem B2930717 : Blo 682313 2930717 := bstep (se 3 (by rfl) ⟨549509, by rfl⟩ : syracuseStep 2930717 = 1099019) B1099019
theorem B768271 : Blo 682313 768271 := bstep (se 1 (by rfl) ⟨576203, by rfl⟩ : syracuseStep 768271 = 1152407) B1152407
theorem B1095995 : Blo 682313 1095995 := bstep (se 1 (by rfl) ⟨821996, by rfl⟩ : syracuseStep 1095995 = 1643993) B1643993
theorem B26589505 : Blo 682313 26589505 := bstep (se 2 (by rfl) ⟨9971064, by rfl⟩ : syracuseStep 26589505 = 19942129) B19942129
theorem B2931059 : Blo 682313 2931059 := bstep (se 1 (by rfl) ⟨2198294, by rfl⟩ : syracuseStep 2931059 = 4396589) B4396589
theorem B866695 : Blo 682313 866695 := bstep (se 1 (by rfl) ⟨650021, by rfl⟩ : syracuseStep 866695 = 1300043) B1300043
theorem B2308499 : Blo 682313 2308499 := bstep (se 1 (by rfl) ⟨1731374, by rfl⟩ : syracuseStep 2308499 = 3462749) B3462749
theorem B2603411 : Blo 682313 2603411 := bstep (se 1 (by rfl) ⟨1952558, by rfl⟩ : syracuseStep 2603411 = 3905117) B3905117
theorem B22166135 : Blo 682313 22166135 := bstep (se 1 (by rfl) ⟨16624601, by rfl⟩ : syracuseStep 22166135 = 33249203) B33249203
theorem B768775 : Blo 682313 768775 := bstep (se 1 (by rfl) ⟨576581, by rfl⟩ : syracuseStep 768775 = 1153163) B1153163
theorem B867115 : Blo 682313 867115 := bstep (se 1 (by rfl) ⟨650336, by rfl⟩ : syracuseStep 867115 = 1300673) B1300673
theorem B768955 : Blo 682313 768955 := bstep (se 1 (by rfl) ⟨576716, by rfl⟩ : syracuseStep 768955 = 1153433) B1153433
theorem B867343 : Blo 682313 867343 := bstep (se 1 (by rfl) ⟨650507, by rfl⟩ : syracuseStep 867343 = 1301015) B1301015
theorem B2079803 : Blo 682313 2079803 := bstep (se 1 (by rfl) ⟨1559852, by rfl⟩ : syracuseStep 2079803 = 3119705) B3119705
theorem B1457423 : Blo 682313 1457423 := bstep (se 1 (by rfl) ⟨1093067, by rfl⟩ : syracuseStep 1457423 = 2186135) B2186135
theorem B769423 : Blo 682313 769423 := bstep (se 1 (by rfl) ⟨577067, by rfl⟩ : syracuseStep 769423 = 1154135) B1154135
theorem B2342297 : Blo 682313 2342297 := bstep (se 2 (by rfl) ⟨878361, by rfl⟩ : syracuseStep 2342297 = 1756723) B1756723
theorem B16661969 : Blo 682313 16661969 := bstep (se 2 (by rfl) ⟨6248238, by rfl⟩ : syracuseStep 16661969 = 12496477) B12496477
theorem B2965021 : Blo 682313 2965021 := bstep (se 3 (by rfl) ⟨555941, by rfl⟩ : syracuseStep 2965021 = 1111883) B1111883
theorem B868087 : Blo 682313 868087 := bstep (se 1 (by rfl) ⟨651065, by rfl⟩ : syracuseStep 868087 = 1302131) B1302131
theorem B1851137 : Blo 682313 1851137 := bstep (se 2 (by rfl) ⟨694176, by rfl⟩ : syracuseStep 1851137 = 1388353) B1388353
theorem B2309903 : Blo 682313 2309903 := bstep (se 1 (by rfl) ⟨1732427, by rfl⟩ : syracuseStep 2309903 = 3464855) B3464855
theorem B1949483 : Blo 682313 1949483 := bstep (se 1 (by rfl) ⟨1462112, by rfl⟩ : syracuseStep 1949483 = 2924225) B2924225
theorem B769927 : Blo 682313 769927 := bstep (se 1 (by rfl) ⟨577445, by rfl⟩ : syracuseStep 769927 = 1154891) B1154891
theorem B7913477 : Blo 682313 7913477 := bstep (se 4 (by rfl) ⟨741888, by rfl⟩ : syracuseStep 7913477 = 1483777) B1483777
theorem B2605067 : Blo 682313 2605067 := bstep (se 1 (by rfl) ⟨1953800, by rfl⟩ : syracuseStep 2605067 = 3907601) B3907601
theorem B2310173 : Blo 682313 2310173 := bstep (se 3 (by rfl) ⟨433157, by rfl⟩ : syracuseStep 2310173 = 866315) B866315
theorem B770107 : Blo 682313 770107 := bstep (se 1 (by rfl) ⟨577580, by rfl⟩ : syracuseStep 770107 = 1155161) B1155161
theorem B868411 : Blo 682313 868411 := bstep (se 1 (by rfl) ⟨651308, by rfl⟩ : syracuseStep 868411 = 1302617) B1302617
theorem B2998663 : Blo 682313 2998663 := bstep (se 1 (by rfl) ⟨2248997, by rfl⟩ : syracuseStep 2998663 = 4497995) B4497995
theorem B7782803 : Blo 682313 7782803 := bstep (se 1 (by rfl) ⟨5837102, by rfl⟩ : syracuseStep 7782803 = 11674205) B11674205
theorem B770575 : Blo 682313 770575 := bstep (se 1 (by rfl) ⟨577931, by rfl⟩ : syracuseStep 770575 = 1155863) B1155863
theorem B3457565 : Blo 682313 3457565 := bstep (se 3 (by rfl) ⟨648293, by rfl⟩ : syracuseStep 3457565 = 1296587) B1296587
theorem B2769437 : Blo 682313 2769437 := bstep (se 3 (by rfl) ⟨519269, by rfl⟩ : syracuseStep 2769437 = 1038539) B1038539
theorem B4997861 : Blo 682313 4997861 := bstep (se 4 (by rfl) ⟨468549, by rfl⟩ : syracuseStep 4997861 = 937099) B937099
theorem B1459063 : Blo 682313 1459063 := bstep (se 1 (by rfl) ⟨1094297, by rfl⟩ : syracuseStep 1459063 = 2188595) B2188595
theorem B3458051 : Blo 682313 3458051 := bstep (se 1 (by rfl) ⟨2593538, by rfl⟩ : syracuseStep 3458051 = 5187077) B5187077
theorem B771079 : Blo 682313 771079 := bstep (se 1 (by rfl) ⟨578309, by rfl⟩ : syracuseStep 771079 = 1156619) B1156619
theorem B2475019 : Blo 682313 2475019 := bstep (se 1 (by rfl) ⟨1856264, by rfl⟩ : syracuseStep 2475019 = 3712529) B3712529
theorem B771259 : Blo 682313 771259 := bstep (se 1 (by rfl) ⟨578444, by rfl⟩ : syracuseStep 771259 = 1156889) B1156889
theorem B1951123 : Blo 682313 1951123 := bstep (se 1 (by rfl) ⟨1463342, by rfl⟩ : syracuseStep 1951123 = 2926685) B2926685
theorem B2311577 : Blo 682313 2311577 := bstep (se 2 (by rfl) ⟨866841, by rfl⟩ : syracuseStep 2311577 = 1733683) B1733683
theorem B3556867 : Blo 682313 3556867 := bstep (se 1 (by rfl) ⟨2667650, by rfl⟩ : syracuseStep 3556867 = 5335301) B5335301
theorem B771727 : Blo 682313 771727 := bstep (se 1 (by rfl) ⟨578795, by rfl⟩ : syracuseStep 771727 = 1157591) B1157591
theorem B1001359 : Blo 682313 1001359 := bstep (se 1 (by rfl) ⟨751019, by rfl⟩ : syracuseStep 1001359 = 1502039) B1502039
theorem B9848729 : Blo 682313 9848729 := bstep (se 2 (by rfl) ⟨3693273, by rfl⟩ : syracuseStep 9848729 = 7386547) B7386547
theorem B2312279 : Blo 682313 2312279 := bstep (se 1 (by rfl) ⟨1734209, by rfl⟩ : syracuseStep 2312279 = 3468419) B3468419
theorem B2312765 : Blo 682313 2312765 := bstep (se 3 (by rfl) ⟨433643, by rfl⟩ : syracuseStep 2312765 = 867287) B867287
theorem B3459671 : Blo 682313 3459671 := bstep (se 1 (by rfl) ⟨2594753, by rfl⟩ : syracuseStep 3459671 = 5189507) B5189507
theorem B1297043 : Blo 682313 1297043 := bstep (se 1 (by rfl) ⟨972782, by rfl⟩ : syracuseStep 1297043 = 1945565) B1945565
theorem B8440625 : Blo 682313 8440625 := bstep (se 2 (by rfl) ⟨3165234, by rfl⟩ : syracuseStep 8440625 = 6330469) B6330469
theorem B1297271 : Blo 682313 1297271 := bstep (se 1 (by rfl) ⟨972953, by rfl⟩ : syracuseStep 1297271 = 1945907) B1945907
theorem B3460157 : Blo 682313 3460157 := bstep (se 3 (by rfl) ⟨648779, by rfl⟩ : syracuseStep 3460157 = 1297559) B1297559
theorem B8768573 : Blo 682313 8768573 := bstep (se 3 (by rfl) ⟨1644107, by rfl⟩ : syracuseStep 8768573 = 3288215) B3288215
theorem B1952855 : Blo 682313 1952855 := bstep (se 1 (by rfl) ⟨1464641, by rfl⟩ : syracuseStep 1952855 = 2929283) B2929283
theorem B1461395 : Blo 682313 1461395 := bstep (se 1 (by rfl) ⟨1096046, by rfl⟩ : syracuseStep 1461395 = 2192093) B2192093
theorem B1756313 : Blo 682313 1756313 := bstep (se 2 (by rfl) ⟨658617, by rfl⟩ : syracuseStep 1756313 = 1317235) B1317235
theorem B3886481 : Blo 682313 3886481 := bstep (se 2 (by rfl) ⟨1457430, by rfl⟩ : syracuseStep 3886481 = 2914861) B2914861
theorem B16829905 : Blo 682313 16829905 := bstep (se 2 (by rfl) ⟨6311214, by rfl⟩ : syracuseStep 16829905 = 12622429) B12622429
theorem B2969041 : Blo 682313 2969041 := bstep (se 2 (by rfl) ⟨1113390, by rfl⟩ : syracuseStep 2969041 = 2226781) B2226781
theorem B11128549 : Blo 682313 11128549 := bstep (se 4 (by rfl) ⟨1043301, by rfl⟩ : syracuseStep 11128549 = 2086603) B2086603
theorem B3952421 : Blo 682313 3952421 := bstep (se 4 (by rfl) ⟨370539, by rfl⟩ : syracuseStep 3952421 = 741079) B741079
theorem B3886937 : Blo 682313 3886937 := bstep (se 2 (by rfl) ⟨1457601, by rfl⟩ : syracuseStep 3886937 = 2915203) B2915203
theorem B2314169 : Blo 682313 2314169 := bstep (se 2 (by rfl) ⟨867813, by rfl⟩ : syracuseStep 2314169 = 1735627) B1735627
theorem B4444625 : Blo 682313 4444625 := bstep (se 2 (by rfl) ⟨1666734, by rfl⟩ : syracuseStep 4444625 = 3333469) B3333469
theorem B2314763 : Blo 682313 2314763 := bstep (se 1 (by rfl) ⟨1736072, by rfl⟩ : syracuseStep 2314763 = 3472145) B3472145
theorem B159896081 : Blo 682313 159896081 := bstep (se 2 (by rfl) ⟨59961030, by rfl⟩ : syracuseStep 159896081 = 119922061) B119922061
theorem B1298987 : Blo 682313 1298987 := bstep (se 1 (by rfl) ⟨974240, by rfl⟩ : syracuseStep 1298987 = 1948481) B1948481
theorem B2314871 : Blo 682313 2314871 := bstep (se 1 (by rfl) ⟨1736153, by rfl⟩ : syracuseStep 2314871 = 3472307) B3472307
theorem B1299215 : Blo 682313 1299215 := bstep (se 1 (by rfl) ⟨974411, by rfl⟩ : syracuseStep 1299215 = 1948823) B1948823
theorem B3461939 : Blo 682313 3461939 := bstep (se 1 (by rfl) ⟨2596454, by rfl⟩ : syracuseStep 3461939 = 5192909) B5192909
theorem B2675641 : Blo 682313 2675641 := bstep (se 2 (by rfl) ⟨1003365, by rfl⟩ : syracuseStep 2675641 = 2006731) B2006731
theorem B3462263 : Blo 682313 3462263 := bstep (se 1 (by rfl) ⟨2596697, by rfl⟩ : syracuseStep 3462263 = 5193395) B5193395
theorem B2315465 : Blo 682313 2315465 := bstep (se 2 (by rfl) ⟨868299, by rfl⟩ : syracuseStep 2315465 = 1736599) B1736599
theorem B4150561 : Blo 682313 4150561 := bstep (se 2 (by rfl) ⟨1556460, by rfl⟩ : syracuseStep 4150561 = 3112921) B3112921
theorem B972167 : Blo 682313 972167 := bstep (se 1 (by rfl) ⟨729125, by rfl⟩ : syracuseStep 972167 = 1458251) B1458251
theorem B1463753 : Blo 682313 1463753 := bstep (se 2 (by rfl) ⟨548907, by rfl⟩ : syracuseStep 1463753 = 1097815) B1097815
theorem B50615837 : Blo 682313 50615837 := bstep (se 3 (by rfl) ⟨9490469, by rfl⟩ : syracuseStep 50615837 = 18980939) B18980939
theorem B972361 : Blo 682313 972361 := bstep (se 2 (by rfl) ⟨364635, by rfl⟩ : syracuseStep 972361 = 729271) B729271
theorem B2086519 : Blo 682313 2086519 := bstep (se 1 (by rfl) ⟨1564889, by rfl⟩ : syracuseStep 2086519 = 3129779) B3129779
theorem B11097931 : Blo 682313 11097931 := bstep (se 1 (by rfl) ⟨8323448, by rfl⟩ : syracuseStep 11097931 = 16646897) B16646897
theorem B1038199 : Blo 682313 1038199 := bstep (se 1 (by rfl) ⟨778649, by rfl⟩ : syracuseStep 1038199 = 1557299) B1557299
theorem B2316167 : Blo 682313 2316167 := bstep (se 1 (by rfl) ⟨1737125, by rfl⟩ : syracuseStep 2316167 = 3474251) B3474251
theorem B1464265 : Blo 682313 1464265 := bstep (se 2 (by rfl) ⟨549099, by rfl⟩ : syracuseStep 1464265 = 1098199) B1098199
theorem B3463235 : Blo 682313 3463235 := bstep (se 1 (by rfl) ⟨2597426, by rfl⟩ : syracuseStep 3463235 = 5194853) B5194853
theorem B972919 : Blo 682313 972919 := bstep (se 1 (by rfl) ⟨729689, by rfl⟩ : syracuseStep 972919 = 1459379) B1459379
theorem B1300627 : Blo 682313 1300627 := bstep (se 1 (by rfl) ⟨975470, by rfl⟩ : syracuseStep 1300627 = 1950941) B1950941
theorem B1562771 : Blo 682313 1562771 := bstep (se 1 (by rfl) ⟨1172078, by rfl⟩ : syracuseStep 1562771 = 2344157) B2344157
theorem B6314273 : Blo 682313 6314273 := bstep (se 2 (by rfl) ⟨2367852, by rfl⟩ : syracuseStep 6314273 = 4735705) B4735705
theorem B1038649 : Blo 682313 1038649 := bstep (se 2 (by rfl) ⟨389493, by rfl⟩ : syracuseStep 1038649 = 778987) B778987
theorem B1300855 : Blo 682313 1300855 := bstep (se 1 (by rfl) ⟨975641, by rfl⟩ : syracuseStep 1300855 = 1951283) B1951283
theorem B3463559 : Blo 682313 3463559 := bstep (se 1 (by rfl) ⟨2597669, by rfl⟩ : syracuseStep 3463559 = 5195339) B5195339
theorem B1497545 : Blo 682313 1497545 := bstep (se 2 (by rfl) ⟨561579, by rfl⟩ : syracuseStep 1497545 = 1123159) B1123159
theorem B4938205 : Blo 682313 4938205 := bstep (se 3 (by rfl) ⟨925913, by rfl⟩ : syracuseStep 4938205 = 1851827) B1851827
theorem B1465103 : Blo 682313 1465103 := bstep (se 1 (by rfl) ⟨1098827, by rfl⟩ : syracuseStep 1465103 = 2197655) B2197655
theorem B973625 : Blo 682313 973625 := bstep (se 2 (by rfl) ⟨365109, by rfl⟩ : syracuseStep 973625 = 730219) B730219
theorem B973711 : Blo 682313 973711 := bstep (se 1 (by rfl) ⟨730283, by rfl⟩ : syracuseStep 973711 = 1460567) B1460567
theorem B973739 : Blo 682313 973739 := bstep (se 1 (by rfl) ⟨730304, by rfl⟩ : syracuseStep 973739 = 1460609) B1460609
theorem B3890105 : Blo 682313 3890105 := bstep (se 2 (by rfl) ⟨1458789, by rfl⟩ : syracuseStep 3890105 = 2917579) B2917579
theorem B1662137 : Blo 682313 1662137 := bstep (se 2 (by rfl) ⟨623301, by rfl⟩ : syracuseStep 1662137 = 1246603) B1246603
theorem B1727689 : Blo 682313 1727689 := bstep (se 2 (by rfl) ⟨647883, by rfl⟩ : syracuseStep 1727689 = 1295767) B1295767
theorem B1727831 : Blo 682313 1727831 := bstep (se 1 (by rfl) ⟨1295873, by rfl⟩ : syracuseStep 1727831 = 2591747) B2591747
theorem B1465735 : Blo 682313 1465735 := bstep (se 1 (by rfl) ⟨1099301, by rfl⟩ : syracuseStep 1465735 = 2198603) B2198603
theorem B3792413 : Blo 682313 3792413 := bstep (se 3 (by rfl) ⟨711077, by rfl⟩ : syracuseStep 3792413 = 1422155) B1422155
theorem B1039915 : Blo 682313 1039915 := bstep (se 1 (by rfl) ⟨779936, by rfl⟩ : syracuseStep 1039915 = 1559873) B1559873
theorem B2186813 : Blo 682313 2186813 := bstep (se 3 (by rfl) ⟨410027, by rfl⟩ : syracuseStep 2186813 = 820055) B820055
theorem B1302419 : Blo 682313 1302419 := bstep (se 1 (by rfl) ⟨976814, by rfl⟩ : syracuseStep 1302419 = 1953629) B1953629
theorem B1302473 : Blo 682313 1302473 := bstep (se 2 (by rfl) ⟨488427, by rfl⟩ : syracuseStep 1302473 = 976855) B976855
theorem B1302571 : Blo 682313 1302571 := bstep (se 1 (by rfl) ⟨976928, by rfl⟩ : syracuseStep 1302571 = 1953857) B1953857
theorem B1302799 : Blo 682313 1302799 := bstep (se 1 (by rfl) ⟨977099, by rfl⟩ : syracuseStep 1302799 = 1954199) B1954199
theorem B14836061 : Blo 682313 14836061 := bstep (se 3 (by rfl) ⟨2781761, by rfl⟩ : syracuseStep 14836061 = 5563523) B5563523
theorem B14016989 : Blo 682313 14016989 := bstep (se 3 (by rfl) ⟨2628185, by rfl⟩ : syracuseStep 14016989 = 5256371) B5256371
theorem B1041083 : Blo 682313 1041083 := bstep (se 1 (by rfl) ⟨780812, by rfl⟩ : syracuseStep 1041083 = 1561625) B1561625
theorem B3892495 : Blo 682313 3892495 := bstep (se 1 (by rfl) ⟨2919371, by rfl⟩ : syracuseStep 3892495 = 5838743) B5838743
theorem B1729907 : Blo 682313 1729907 := bstep (se 1 (by rfl) ⟨1297430, by rfl⟩ : syracuseStep 1729907 = 2594861) B2594861
theorem B2778553 : Blo 682313 2778553 := bstep (se 2 (by rfl) ⟨1041957, by rfl⟩ : syracuseStep 2778553 = 2083915) B2083915
theorem B14018305 : Blo 682313 14018305 := bstep (se 2 (by rfl) ⟨5256864, by rfl⟩ : syracuseStep 14018305 = 10513729) B10513729
theorem B976655 : Blo 682313 976655 := bstep (se 1 (by rfl) ⟨732491, by rfl⟩ : syracuseStep 976655 = 1464983) B1464983
theorem B3467123 : Blo 682313 3467123 := bstep (se 1 (by rfl) ⟨2600342, by rfl⟩ : syracuseStep 3467123 = 5200685) B5200685
theorem B1730423 : Blo 682313 1730423 := bstep (se 1 (by rfl) ⟨1297817, by rfl⟩ : syracuseStep 1730423 = 2595635) B2595635
theorem B3467609 : Blo 682313 3467609 := bstep (se 2 (by rfl) ⟨1300353, by rfl⟩ : syracuseStep 3467609 = 2600707) B2600707
theorem B2189683 : Blo 682313 2189683 := bstep (se 1 (by rfl) ⟨1642262, by rfl⟩ : syracuseStep 2189683 = 3284525) B3284525
theorem B1337719 : Blo 682313 1337719 := bstep (se 1 (by rfl) ⟨1003289, by rfl⟩ : syracuseStep 1337719 = 2006579) B2006579
theorem B682375 : Blo 682313 682375 := bstep (se 1 (by rfl) ⟨511781, by rfl⟩ : syracuseStep 682375 = 1023563) B1023563
theorem B682383 : Blo 682313 682383 := bstep (se 1 (by rfl) ⟨511787, by rfl⟩ : syracuseStep 682383 = 1023575) B1023575
theorem B3664273 : Blo 682313 3664273 := bstep (se 2 (by rfl) ⟨1374102, by rfl⟩ : syracuseStep 3664273 = 2748205) B2748205
theorem B682427 : Blo 682313 682427 := bstep (se 1 (by rfl) ⟨511820, by rfl⟩ : syracuseStep 682427 = 1023641) B1023641
theorem B682503 : Blo 682313 682503 := bstep (se 1 (by rfl) ⟨511877, by rfl⟩ : syracuseStep 682503 = 1023755) B1023755
theorem B3893771 : Blo 682313 3893771 := bstep (se 1 (by rfl) ⟨2920328, by rfl⟩ : syracuseStep 3893771 = 5840657) B5840657
theorem B682511 : Blo 682313 682511 := bstep (se 1 (by rfl) ⟨511883, by rfl⟩ : syracuseStep 682511 = 1023767) B1023767
theorem B682555 : Blo 682313 682555 := bstep (se 1 (by rfl) ⟨511916, by rfl⟩ : syracuseStep 682555 = 1023833) B1023833
theorem B682631 : Blo 682313 682631 := bstep (se 1 (by rfl) ⟨511973, by rfl⟩ : syracuseStep 682631 = 1023947) B1023947
theorem B682639 : Blo 682313 682639 := bstep (se 1 (by rfl) ⟨511979, by rfl⟩ : syracuseStep 682639 = 1023959) B1023959
theorem B682683 : Blo 682313 682683 := bstep (se 1 (by rfl) ⟨512012, by rfl⟩ : syracuseStep 682683 = 1024025) B1024025
theorem B3893953 : Blo 682313 3893953 := bstep (se 2 (by rfl) ⟨1460232, by rfl⟩ : syracuseStep 3893953 = 2920465) B2920465
theorem B682759 : Blo 682313 682759 := bstep (se 1 (by rfl) ⟨512069, by rfl⟩ : syracuseStep 682759 = 1024139) B1024139
theorem B682767 : Blo 682313 682767 := bstep (se 1 (by rfl) ⟨512075, by rfl⟩ : syracuseStep 682767 = 1024151) B1024151
theorem B682811 : Blo 682313 682811 := bstep (se 1 (by rfl) ⟨512108, by rfl⟩ : syracuseStep 682811 = 1024217) B1024217
theorem B1731415 : Blo 682313 1731415 := bstep (se 1 (by rfl) ⟨1298561, by rfl⟩ : syracuseStep 1731415 = 2597123) B2597123
theorem B682887 : Blo 682313 682887 := bstep (se 1 (by rfl) ⟨512165, by rfl⟩ : syracuseStep 682887 = 1024331) B1024331
theorem B682895 : Blo 682313 682895 := bstep (se 1 (by rfl) ⟨512171, by rfl⟩ : syracuseStep 682895 = 1024343) B1024343
theorem B5565347 : Blo 682313 5565347 := bstep (se 1 (by rfl) ⟨4174010, by rfl⟩ : syracuseStep 5565347 = 8348021) B8348021
theorem B682939 : Blo 682313 682939 := bstep (se 1 (by rfl) ⟨512204, by rfl⟩ : syracuseStep 682939 = 1024409) B1024409
theorem B683015 : Blo 682313 683015 := bstep (se 1 (by rfl) ⟨512261, by rfl⟩ : syracuseStep 683015 = 1024523) B1024523
theorem B683023 : Blo 682313 683023 := bstep (se 1 (by rfl) ⟨512267, by rfl⟩ : syracuseStep 683023 = 1024535) B1024535
theorem B683067 : Blo 682313 683067 := bstep (se 1 (by rfl) ⟨512300, by rfl⟩ : syracuseStep 683067 = 1024601) B1024601
theorem B683143 : Blo 682313 683143 := bstep (se 1 (by rfl) ⟨512357, by rfl⟩ : syracuseStep 683143 = 1024715) B1024715
theorem B1731719 : Blo 682313 1731719 := bstep (se 1 (by rfl) ⟨1298789, by rfl⟩ : syracuseStep 1731719 = 2597579) B2597579
theorem B683151 : Blo 682313 683151 := bstep (se 1 (by rfl) ⟨512363, by rfl⟩ : syracuseStep 683151 = 1024727) B1024727
theorem B683195 : Blo 682313 683195 := bstep (se 1 (by rfl) ⟨512396, by rfl⟩ : syracuseStep 683195 = 1024793) B1024793
theorem B683271 : Blo 682313 683271 := bstep (se 1 (by rfl) ⟨512453, by rfl⟩ : syracuseStep 683271 = 1024907) B1024907
theorem B1731851 : Blo 682313 1731851 := bstep (se 1 (by rfl) ⟨1298888, by rfl⟩ : syracuseStep 1731851 = 2597777) B2597777
theorem B683279 : Blo 682313 683279 := bstep (se 1 (by rfl) ⟨512459, by rfl⟩ : syracuseStep 683279 = 1024919) B1024919
theorem B1535291 : Blo 682313 1535291 := bstep (se 1 (by rfl) ⟨1151468, by rfl⟩ : syracuseStep 1535291 = 2302937) B2302937
theorem B683323 : Blo 682313 683323 := bstep (se 1 (by rfl) ⟨512492, by rfl⟩ : syracuseStep 683323 = 1024985) B1024985
theorem B683399 : Blo 682313 683399 := bstep (se 1 (by rfl) ⟨512549, by rfl⟩ : syracuseStep 683399 = 1025099) B1025099
theorem B683407 : Blo 682313 683407 := bstep (se 1 (by rfl) ⟨512555, by rfl⟩ : syracuseStep 683407 = 1025111) B1025111
theorem B1535417 : Blo 682313 1535417 := bstep (se 2 (by rfl) ⟨575781, by rfl⟩ : syracuseStep 1535417 = 1151563) B1151563
theorem B6254009 : Blo 682313 6254009 := bstep (se 2 (by rfl) ⟨2345253, by rfl⟩ : syracuseStep 6254009 = 4690507) B4690507
theorem B683451 : Blo 682313 683451 := bstep (se 1 (by rfl) ⟨512588, by rfl⟩ : syracuseStep 683451 = 1025177) B1025177
theorem B683527 : Blo 682313 683527 := bstep (se 1 (by rfl) ⟨512645, by rfl⟩ : syracuseStep 683527 = 1025291) B1025291
theorem B683535 : Blo 682313 683535 := bstep (se 1 (by rfl) ⟨512651, by rfl⟩ : syracuseStep 683535 = 1025303) B1025303
theorem B683579 : Blo 682313 683579 := bstep (se 1 (by rfl) ⟨512684, by rfl⟩ : syracuseStep 683579 = 1025369) B1025369
theorem B683655 : Blo 682313 683655 := bstep (se 1 (by rfl) ⟨512741, by rfl⟩ : syracuseStep 683655 = 1025483) B1025483
theorem B683663 : Blo 682313 683663 := bstep (se 1 (by rfl) ⟨512747, by rfl⟩ : syracuseStep 683663 = 1025495) B1025495
theorem B683707 : Blo 682313 683707 := bstep (se 1 (by rfl) ⟨512780, by rfl⟩ : syracuseStep 683707 = 1025561) B1025561
theorem B683783 : Blo 682313 683783 := bstep (se 1 (by rfl) ⟨512837, by rfl⟩ : syracuseStep 683783 = 1025675) B1025675
theorem B1535759 : Blo 682313 1535759 := bstep (se 1 (by rfl) ⟨1151819, by rfl⟩ : syracuseStep 1535759 = 2303639) B2303639
theorem B683791 : Blo 682313 683791 := bstep (se 1 (by rfl) ⟨512843, by rfl⟩ : syracuseStep 683791 = 1025687) B1025687
theorem B1732367 : Blo 682313 1732367 := bstep (se 1 (by rfl) ⟨1299275, by rfl⟩ : syracuseStep 1732367 = 2598551) B2598551
theorem B1535777 : Blo 682313 1535777 := bstep (se 2 (by rfl) ⟨575916, by rfl⟩ : syracuseStep 1535777 = 1151833) B1151833
theorem B7794467 : Blo 682313 7794467 := bstep (se 1 (by rfl) ⟨5845850, by rfl⟩ : syracuseStep 7794467 = 11691701) B11691701
theorem B7401253 : Blo 682313 7401253 := bstep (se 4 (by rfl) ⟨693867, by rfl⟩ : syracuseStep 7401253 = 1387735) B1387735
theorem B683835 : Blo 682313 683835 := bstep (se 1 (by rfl) ⟨512876, by rfl⟩ : syracuseStep 683835 = 1025753) B1025753
theorem B683911 : Blo 682313 683911 := bstep (se 1 (by rfl) ⟨512933, by rfl⟩ : syracuseStep 683911 = 1025867) B1025867
theorem B683919 : Blo 682313 683919 := bstep (se 1 (by rfl) ⟨512939, by rfl⟩ : syracuseStep 683919 = 1025879) B1025879
theorem B1732499 : Blo 682313 1732499 := bstep (se 1 (by rfl) ⟨1299374, by rfl⟩ : syracuseStep 1732499 = 2598749) B2598749
theorem B4157369 : Blo 682313 4157369 := bstep (se 2 (by rfl) ⟨1559013, by rfl⟩ : syracuseStep 4157369 = 3118027) B3118027
theorem B683963 : Blo 682313 683963 := bstep (se 1 (by rfl) ⟨512972, by rfl⟩ : syracuseStep 683963 = 1025945) B1025945
theorem B684039 : Blo 682313 684039 := bstep (se 1 (by rfl) ⟨513029, by rfl⟩ : syracuseStep 684039 = 1026059) B1026059
theorem B684047 : Blo 682313 684047 := bstep (se 1 (by rfl) ⟨513035, by rfl⟩ : syracuseStep 684047 = 1026071) B1026071
theorem B684091 : Blo 682313 684091 := bstep (se 1 (by rfl) ⟨513068, by rfl⟩ : syracuseStep 684091 = 1026137) B1026137
theorem B1536119 : Blo 682313 1536119 := bstep (se 1 (by rfl) ⟨1152089, by rfl⟩ : syracuseStep 1536119 = 2304179) B2304179
theorem B684167 : Blo 682313 684167 := bstep (se 1 (by rfl) ⟨513125, by rfl⟩ : syracuseStep 684167 = 1026251) B1026251
theorem B684175 : Blo 682313 684175 := bstep (se 1 (by rfl) ⟨513131, by rfl⟩ : syracuseStep 684175 = 1026263) B1026263
theorem B684219 : Blo 682313 684219 := bstep (se 1 (by rfl) ⟨513164, by rfl⟩ : syracuseStep 684219 = 1026329) B1026329
theorem B684295 : Blo 682313 684295 := bstep (se 1 (by rfl) ⟨513221, by rfl⟩ : syracuseStep 684295 = 1026443) B1026443
theorem B684303 : Blo 682313 684303 := bstep (se 1 (by rfl) ⟨513227, by rfl⟩ : syracuseStep 684303 = 1026455) B1026455
theorem B1536299 : Blo 682313 1536299 := bstep (se 1 (by rfl) ⟨1152224, by rfl⟩ : syracuseStep 1536299 = 2304449) B2304449
theorem B684347 : Blo 682313 684347 := bstep (se 1 (by rfl) ⟨513260, by rfl⟩ : syracuseStep 684347 = 1026521) B1026521
theorem B684423 : Blo 682313 684423 := bstep (se 1 (by rfl) ⟨513317, by rfl⟩ : syracuseStep 684423 = 1026635) B1026635
theorem B684431 : Blo 682313 684431 := bstep (se 1 (by rfl) ⟨513323, by rfl⟩ : syracuseStep 684431 = 1026647) B1026647
theorem B3469715 : Blo 682313 3469715 := bstep (se 1 (by rfl) ⟨2602286, by rfl⟩ : syracuseStep 3469715 = 5204573) B5204573
theorem B684475 : Blo 682313 684475 := bstep (se 1 (by rfl) ⟨513356, by rfl⟩ : syracuseStep 684475 = 1026713) B1026713
theorem B684551 : Blo 682313 684551 := bstep (se 1 (by rfl) ⟨513413, by rfl⟩ : syracuseStep 684551 = 1026827) B1026827
theorem B684559 : Blo 682313 684559 := bstep (se 1 (by rfl) ⟨513419, by rfl⟩ : syracuseStep 684559 = 1026839) B1026839
theorem B684603 : Blo 682313 684603 := bstep (se 1 (by rfl) ⟨513452, by rfl⟩ : syracuseStep 684603 = 1026905) B1026905
theorem B684679 : Blo 682313 684679 := bstep (se 1 (by rfl) ⟨513509, by rfl⟩ : syracuseStep 684679 = 1027019) B1027019
theorem B684687 : Blo 682313 684687 := bstep (se 1 (by rfl) ⟨513515, by rfl⟩ : syracuseStep 684687 = 1027031) B1027031
theorem B1536659 : Blo 682313 1536659 := bstep (se 1 (by rfl) ⟨1152494, by rfl⟩ : syracuseStep 1536659 = 2304989) B2304989
theorem B684731 : Blo 682313 684731 := bstep (se 1 (by rfl) ⟨513548, by rfl⟩ : syracuseStep 684731 = 1027097) B1027097
theorem B1536713 : Blo 682313 1536713 := bstep (se 2 (by rfl) ⟨576267, by rfl⟩ : syracuseStep 1536713 = 1152535) B1152535
theorem B684807 : Blo 682313 684807 := bstep (se 1 (by rfl) ⟨513605, by rfl⟩ : syracuseStep 684807 = 1027211) B1027211
theorem B684815 : Blo 682313 684815 := bstep (se 1 (by rfl) ⟨513611, by rfl⟩ : syracuseStep 684815 = 1027223) B1027223
theorem B684859 : Blo 682313 684859 := bstep (se 1 (by rfl) ⟨513644, by rfl⟩ : syracuseStep 684859 = 1027289) B1027289
theorem B684935 : Blo 682313 684935 := bstep (se 1 (by rfl) ⟨513701, by rfl⟩ : syracuseStep 684935 = 1027403) B1027403
theorem B684943 : Blo 682313 684943 := bstep (se 1 (by rfl) ⟨513707, by rfl⟩ : syracuseStep 684943 = 1027415) B1027415
theorem B684987 : Blo 682313 684987 := bstep (se 1 (by rfl) ⟨513740, by rfl⟩ : syracuseStep 684987 = 1027481) B1027481
theorem B1733633 : Blo 682313 1733633 := bstep (se 2 (by rfl) ⟨650112, by rfl⟩ : syracuseStep 1733633 = 1300225) B1300225
theorem B685063 : Blo 682313 685063 := bstep (se 1 (by rfl) ⟨513797, by rfl⟩ : syracuseStep 685063 = 1027595) B1027595
theorem B685071 : Blo 682313 685071 := bstep (se 1 (by rfl) ⟨513803, by rfl⟩ : syracuseStep 685071 = 1027607) B1027607
theorem B685115 : Blo 682313 685115 := bstep (se 1 (by rfl) ⟨513836, by rfl⟩ : syracuseStep 685115 = 1027673) B1027673
theorem B685191 : Blo 682313 685191 := bstep (se 1 (by rfl) ⟨513893, by rfl⟩ : syracuseStep 685191 = 1027787) B1027787
theorem B685199 : Blo 682313 685199 := bstep (se 1 (by rfl) ⟨513899, by rfl⟩ : syracuseStep 685199 = 1027799) B1027799
theorem B685243 : Blo 682313 685243 := bstep (se 1 (by rfl) ⟨513932, by rfl⟩ : syracuseStep 685243 = 1027865) B1027865
theorem B685319 : Blo 682313 685319 := bstep (se 1 (by rfl) ⟨513989, by rfl⟩ : syracuseStep 685319 = 1027979) B1027979
theorem B685327 : Blo 682313 685327 := bstep (se 1 (by rfl) ⟨513995, by rfl⟩ : syracuseStep 685327 = 1027991) B1027991
theorem B685371 : Blo 682313 685371 := bstep (se 1 (by rfl) ⟨514028, by rfl⟩ : syracuseStep 685371 = 1028057) B1028057
theorem B1734007 : Blo 682313 1734007 := bstep (se 1 (by rfl) ⟨1300505, by rfl⟩ : syracuseStep 1734007 = 2601011) B2601011
theorem B1537415 : Blo 682313 1537415 := bstep (se 1 (by rfl) ⟨1153061, by rfl⟩ : syracuseStep 1537415 = 2306123) B2306123
theorem B685447 : Blo 682313 685447 := bstep (se 1 (by rfl) ⟨514085, by rfl⟩ : syracuseStep 685447 = 1028171) B1028171
theorem B685455 : Blo 682313 685455 := bstep (se 1 (by rfl) ⟨514091, by rfl⟩ : syracuseStep 685455 = 1028183) B1028183
theorem B3503513 : Blo 682313 3503513 := bstep (se 2 (by rfl) ⟨1313817, by rfl⟩ : syracuseStep 3503513 = 2627635) B2627635
theorem B685499 : Blo 682313 685499 := bstep (se 1 (by rfl) ⟨514124, by rfl⟩ : syracuseStep 685499 = 1028249) B1028249
theorem B685575 : Blo 682313 685575 := bstep (se 1 (by rfl) ⟨514181, by rfl⟩ : syracuseStep 685575 = 1028363) B1028363
theorem B685583 : Blo 682313 685583 := bstep (se 1 (by rfl) ⟨514187, by rfl⟩ : syracuseStep 685583 = 1028375) B1028375
theorem B2192939 : Blo 682313 2192939 := bstep (se 1 (by rfl) ⟨1644704, by rfl⟩ : syracuseStep 2192939 = 3289409) B3289409
theorem B1537595 : Blo 682313 1537595 := bstep (se 1 (by rfl) ⟨1153196, by rfl⟩ : syracuseStep 1537595 = 2306393) B2306393
theorem B685627 : Blo 682313 685627 := bstep (se 1 (by rfl) ⟨514220, by rfl⟩ : syracuseStep 685627 = 1028441) B1028441
theorem B8451661 : Blo 682313 8451661 := bstep (se 3 (by rfl) ⟨1584686, by rfl⟩ : syracuseStep 8451661 = 3169373) B3169373
theorem B685703 : Blo 682313 685703 := bstep (se 1 (by rfl) ⟨514277, by rfl⟩ : syracuseStep 685703 = 1028555) B1028555
theorem B685711 : Blo 682313 685711 := bstep (se 1 (by rfl) ⟨514283, by rfl⟩ : syracuseStep 685711 = 1028567) B1028567
theorem B1537721 : Blo 682313 1537721 := bstep (se 2 (by rfl) ⟨576645, by rfl⟩ : syracuseStep 1537721 = 1153291) B1153291
theorem B685755 : Blo 682313 685755 := bstep (se 1 (by rfl) ⟨514316, by rfl⟩ : syracuseStep 685755 = 1028633) B1028633
theorem B7894721 : Blo 682313 7894721 := bstep (se 2 (by rfl) ⟨2960520, by rfl⟩ : syracuseStep 7894721 = 5921041) B5921041
theorem B685831 : Blo 682313 685831 := bstep (se 1 (by rfl) ⟨514373, by rfl⟩ : syracuseStep 685831 = 1028747) B1028747
theorem B685839 : Blo 682313 685839 := bstep (se 1 (by rfl) ⟨514379, by rfl⟩ : syracuseStep 685839 = 1028759) B1028759
theorem B1734443 : Blo 682313 1734443 := bstep (se 1 (by rfl) ⟨1300832, by rfl⟩ : syracuseStep 1734443 = 2601665) B2601665
theorem B685883 : Blo 682313 685883 := bstep (se 1 (by rfl) ⟨514412, by rfl⟩ : syracuseStep 685883 = 1028825) B1028825
theorem B685959 : Blo 682313 685959 := bstep (se 1 (by rfl) ⟨514469, by rfl⟩ : syracuseStep 685959 = 1028939) B1028939
theorem B685967 : Blo 682313 685967 := bstep (se 1 (by rfl) ⟨514475, by rfl⟩ : syracuseStep 685967 = 1028951) B1028951
theorem B686011 : Blo 682313 686011 := bstep (se 1 (by rfl) ⟨514508, by rfl⟩ : syracuseStep 686011 = 1029017) B1029017
theorem B11696075 : Blo 682313 11696075 := bstep (se 1 (by rfl) ⟨8772056, by rfl⟩ : syracuseStep 11696075 = 17544113) B17544113
theorem B8452043 : Blo 682313 8452043 := bstep (se 1 (by rfl) ⟨6339032, by rfl⟩ : syracuseStep 8452043 = 12678065) B12678065
theorem B686087 : Blo 682313 686087 := bstep (se 1 (by rfl) ⟨514565, by rfl⟩ : syracuseStep 686087 = 1029131) B1029131
theorem B1538063 : Blo 682313 1538063 := bstep (se 1 (by rfl) ⟨1153547, by rfl⟩ : syracuseStep 1538063 = 2307095) B2307095
theorem B686095 : Blo 682313 686095 := bstep (se 1 (by rfl) ⟨514571, by rfl⟩ : syracuseStep 686095 = 1029143) B1029143
theorem B1538081 : Blo 682313 1538081 := bstep (se 2 (by rfl) ⟨576780, by rfl⟩ : syracuseStep 1538081 = 1153561) B1153561
theorem B686139 : Blo 682313 686139 := bstep (se 1 (by rfl) ⟨514604, by rfl⟩ : syracuseStep 686139 = 1029209) B1029209
theorem B2193527 : Blo 682313 2193527 := bstep (se 1 (by rfl) ⟨1645145, by rfl⟩ : syracuseStep 2193527 = 3290291) B3290291
theorem B686215 : Blo 682313 686215 := bstep (se 1 (by rfl) ⟨514661, by rfl⟩ : syracuseStep 686215 = 1029323) B1029323
theorem B686223 : Blo 682313 686223 := bstep (se 1 (by rfl) ⟨514667, by rfl⟩ : syracuseStep 686223 = 1029335) B1029335
theorem B1112249 : Blo 682313 1112249 := bstep (se 2 (by rfl) ⟨417093, by rfl⟩ : syracuseStep 1112249 = 834187) B834187
theorem B686267 : Blo 682313 686267 := bstep (se 1 (by rfl) ⟨514700, by rfl⟩ : syracuseStep 686267 = 1029401) B1029401
theorem B1538423 : Blo 682313 1538423 := bstep (se 1 (by rfl) ⟨1153817, by rfl⟩ : syracuseStep 1538423 = 2307635) B2307635
theorem B1538603 : Blo 682313 1538603 := bstep (se 1 (by rfl) ⟨1153952, by rfl⟩ : syracuseStep 1538603 = 2307905) B2307905
theorem B1735283 : Blo 682313 1735283 := bstep (se 1 (by rfl) ⟨1301462, by rfl⟩ : syracuseStep 1735283 = 2602925) B2602925
theorem B1735303 : Blo 682313 1735303 := bstep (se 1 (by rfl) ⟨1301477, by rfl⟩ : syracuseStep 1735303 = 2602955) B2602955
theorem B3898145 : Blo 682313 3898145 := bstep (se 2 (by rfl) ⟨1461804, by rfl⟩ : syracuseStep 3898145 = 2923609) B2923609
theorem B5208947 : Blo 682313 5208947 := bstep (se 1 (by rfl) ⟨3906710, by rfl⟩ : syracuseStep 5208947 = 7813421) B7813421
theorem B1538963 : Blo 682313 1538963 := bstep (se 1 (by rfl) ⟨1154222, by rfl⟩ : syracuseStep 1538963 = 2308445) B2308445
theorem B1735577 : Blo 682313 1735577 := bstep (se 2 (by rfl) ⟨650841, by rfl⟩ : syracuseStep 1735577 = 1301683) B1301683
theorem B1539017 : Blo 682313 1539017 := bstep (se 2 (by rfl) ⟨577131, by rfl⟩ : syracuseStep 1539017 = 1154263) B1154263
theorem B1604623 : Blo 682313 1604623 := bstep (se 1 (by rfl) ⟨1203467, by rfl⟩ : syracuseStep 1604623 = 2406935) B2406935
theorem B1735739 : Blo 682313 1735739 := bstep (se 1 (by rfl) ⟨1301804, by rfl⟩ : syracuseStep 1735739 = 2603609) B2603609
theorem B1735951 : Blo 682313 1735951 := bstep (se 1 (by rfl) ⟨1301963, by rfl⟩ : syracuseStep 1735951 = 2603927) B2603927
theorem B1899911 : Blo 682313 1899911 := bstep (se 1 (by rfl) ⟨1424933, by rfl⟩ : syracuseStep 1899911 = 2849867) B2849867
theorem B3472793 : Blo 682313 3472793 := bstep (se 2 (by rfl) ⟨1302297, by rfl⟩ : syracuseStep 3472793 = 2604595) B2604595
theorem B1736225 : Blo 682313 1736225 := bstep (se 2 (by rfl) ⟨651084, by rfl⟩ : syracuseStep 1736225 = 1302169) B1302169
theorem B1539719 : Blo 682313 1539719 := bstep (se 1 (by rfl) ⟨1154789, by rfl⟩ : syracuseStep 1539719 = 2309579) B2309579
theorem B1900217 : Blo 682313 1900217 := bstep (se 2 (by rfl) ⟨712581, by rfl⟩ : syracuseStep 1900217 = 1425163) B1425163
theorem B1539899 : Blo 682313 1539899 := bstep (se 1 (by rfl) ⟨1154924, by rfl⟩ : syracuseStep 1539899 = 2309849) B2309849
theorem B1540025 : Blo 682313 1540025 := bstep (se 2 (by rfl) ⟨577509, by rfl⟩ : syracuseStep 1540025 = 1155019) B1155019
theorem B1736711 : Blo 682313 1736711 := bstep (se 1 (by rfl) ⟨1302533, by rfl⟩ : syracuseStep 1736711 = 2605067) B2605067
theorem B21102605 : Blo 682313 21102605 := bstep (se 3 (by rfl) ⟨3956738, by rfl⟩ : syracuseStep 21102605 = 7913477) B7913477
theorem B1540115 : Blo 682313 1540115 := bstep (se 1 (by rfl) ⟨1155086, by rfl⟩ : syracuseStep 1540115 = 2310173) B2310173
theorem B4390949 : Blo 682313 4390949 := bstep (se 4 (by rfl) ⟨411651, by rfl⟩ : syracuseStep 4390949 = 823303) B823303
theorem B1736761 : Blo 682313 1736761 := bstep (se 2 (by rfl) ⟨651285, by rfl⟩ : syracuseStep 1736761 = 1302571) B1302571
theorem B10518605 : Blo 682313 10518605 := bstep (se 3 (by rfl) ⟨1972238, by rfl⟩ : syracuseStep 10518605 = 3944477) B3944477
theorem B4456529 : Blo 682313 4456529 := bstep (se 2 (by rfl) ⟨1671198, by rfl⟩ : syracuseStep 4456529 = 3342397) B3342397
theorem B5832971 : Blo 682313 5832971 := bstep (se 1 (by rfl) ⟨4374728, by rfl⟩ : syracuseStep 5832971 = 8749457) B8749457
theorem B1540457 : Blo 682313 1540457 := bstep (se 2 (by rfl) ⟨577671, by rfl⟩ : syracuseStep 1540457 = 1155343) B1155343
theorem B1737065 : Blo 682313 1737065 := bstep (se 2 (by rfl) ⟨651399, by rfl⟩ : syracuseStep 1737065 = 1302799) B1302799
theorem B1541051 : Blo 682313 1541051 := bstep (se 1 (by rfl) ⟨1155788, by rfl⟩ : syracuseStep 1541051 = 2311577) B2311577
theorem B24052787 : Blo 682313 24052787 := bstep (se 1 (by rfl) ⟨18039590, by rfl⟩ : syracuseStep 24052787 = 36079181) B36079181
theorem B1541177 : Blo 682313 1541177 := bstep (se 2 (by rfl) ⟨577941, by rfl⟩ : syracuseStep 1541177 = 1155883) B1155883
theorem B8750429 : Blo 682313 8750429 := bstep (se 3 (by rfl) ⟨1640705, by rfl⟩ : syracuseStep 8750429 = 3281411) B3281411
theorem B1541519 : Blo 682313 1541519 := bstep (se 1 (by rfl) ⟨1156139, by rfl⟩ : syracuseStep 1541519 = 2312279) B2312279
theorem B1541843 : Blo 682313 1541843 := bstep (se 1 (by rfl) ⟨1156382, by rfl⟩ : syracuseStep 1541843 = 2312765) B2312765
theorem B3704737 : Blo 682313 3704737 := bstep (se 2 (by rfl) ⟨1389276, by rfl⟩ : syracuseStep 3704737 = 2778553) B2778553
theorem B1640455 : Blo 682313 1640455 := bstep (se 1 (by rfl) ⟨1230341, by rfl⟩ : syracuseStep 1640455 = 2460683) B2460683
theorem B2590987 : Blo 682313 2590987 := bstep (se 1 (by rfl) ⟨1943240, by rfl⟩ : syracuseStep 2590987 = 3886481) B3886481
theorem B2591291 : Blo 682313 2591291 := bstep (se 1 (by rfl) ⟨1943468, by rfl⟩ : syracuseStep 2591291 = 3886937) B3886937
theorem B1542779 : Blo 682313 1542779 := bstep (se 1 (by rfl) ⟨1157084, by rfl⟩ : syracuseStep 1542779 = 2314169) B2314169
theorem B1542905 : Blo 682313 1542905 := bstep (se 2 (by rfl) ⟨578589, by rfl⟩ : syracuseStep 1542905 = 1157179) B1157179
theorem B2198345 : Blo 682313 2198345 := bstep (se 2 (by rfl) ⟨824379, by rfl⟩ : syracuseStep 2198345 = 1648759) B1648759
theorem B1543175 : Blo 682313 1543175 := bstep (se 1 (by rfl) ⟨1157381, by rfl⟩ : syracuseStep 1543175 = 2314763) B2314763
theorem B106597387 : Blo 682313 106597387 := bstep (se 1 (by rfl) ⟨79948040, by rfl⟩ : syracuseStep 106597387 = 159896081) B159896081
theorem B1543247 : Blo 682313 1543247 := bstep (se 1 (by rfl) ⟨1157435, by rfl⟩ : syracuseStep 1543247 = 2314871) B2314871
theorem B2919577 : Blo 682313 2919577 := bstep (se 2 (by rfl) ⟨1094841, by rfl⟩ : syracuseStep 2919577 = 2189683) B2189683
theorem B4885697 : Blo 682313 4885697 := bstep (se 2 (by rfl) ⟨1832136, by rfl⟩ : syracuseStep 4885697 = 3664273) B3664273
theorem B1543643 : Blo 682313 1543643 := bstep (se 1 (by rfl) ⟨1157732, by rfl⟩ : syracuseStep 1543643 = 2315465) B2315465
theorem B11079301 : Blo 682313 11079301 := bstep (se 4 (by rfl) ⟨1038684, by rfl⟩ : syracuseStep 11079301 = 2077369) B2077369
theorem B2592445 : Blo 682313 2592445 := bstep (se 3 (by rfl) ⟨486083, by rfl⟩ : syracuseStep 2592445 = 972167) B972167
theorem B2461549 : Blo 682313 2461549 := bstep (se 3 (by rfl) ⟨461540, by rfl⟩ : syracuseStep 2461549 = 923081) B923081
theorem B1544111 : Blo 682313 1544111 := bstep (se 1 (by rfl) ⟨1158083, by rfl⟩ : syracuseStep 1544111 = 2316167) B2316167
theorem B2593403 : Blo 682313 2593403 := bstep (se 1 (by rfl) ⟨1945052, by rfl⟩ : syracuseStep 2593403 = 3890105) B3890105
theorem B1151887 : Blo 682313 1151887 := bstep (se 1 (by rfl) ⟨863915, by rfl⟩ : syracuseStep 1151887 = 1727831) B1727831
theorem B2528275 : Blo 682313 2528275 := bstep (se 1 (by rfl) ⟨1896206, by rfl⟩ : syracuseStep 2528275 = 3792413) B3792413
theorem B9868337 : Blo 682313 9868337 := bstep (se 2 (by rfl) ⟨3700626, by rfl⟩ : syracuseStep 9868337 = 7401253) B7401253
theorem B1643599 : Blo 682313 1643599 := bstep (se 1 (by rfl) ⟨1232699, by rfl⟩ : syracuseStep 1643599 = 2465399) B2465399
theorem B2594177 : Blo 682313 2594177 := bstep (se 2 (by rfl) ⟨972816, by rfl⟩ : syracuseStep 2594177 = 1945633) B1945633
theorem B1152569 : Blo 682313 1152569 := bstep (se 2 (by rfl) ⟨432213, by rfl⟩ : syracuseStep 1152569 = 864427) B864427
theorem B9344659 : Blo 682313 9344659 := bstep (se 1 (by rfl) ⟨7008494, by rfl⟩ : syracuseStep 9344659 = 14016989) B14016989
theorem B4167389 : Blo 682313 4167389 := bstep (se 3 (by rfl) ⟨781385, by rfl⟩ : syracuseStep 4167389 = 1562771) B1562771
theorem B694055 : Blo 682313 694055 := bstep (se 1 (by rfl) ⟨520541, by rfl⟩ : syracuseStep 694055 = 1041083) B1041083
theorem B2627603 : Blo 682313 2627603 := bstep (se 1 (by rfl) ⟨1970702, by rfl⟩ : syracuseStep 2627603 = 3941405) B3941405
theorem B3905617 : Blo 682313 3905617 := bstep (se 2 (by rfl) ⟨1464606, by rfl⟩ : syracuseStep 3905617 = 2929213) B2929213
theorem B1153271 : Blo 682313 1153271 := bstep (se 1 (by rfl) ⟨864953, by rfl⟩ : syracuseStep 1153271 = 1729907) B1729907
theorem B2595361 : Blo 682313 2595361 := bstep (se 2 (by rfl) ⟨973260, by rfl⟩ : syracuseStep 2595361 = 1946521) B1946521
theorem B2464289 : Blo 682313 2464289 := bstep (se 2 (by rfl) ⟨924108, by rfl⟩ : syracuseStep 2464289 = 1848217) B1848217
theorem B11115053 : Blo 682313 11115053 := bstep (se 3 (by rfl) ⟨2084072, by rfl⟩ : syracuseStep 11115053 = 4168145) B4168145
theorem B1153615 : Blo 682313 1153615 := bstep (se 1 (by rfl) ⟨865211, by rfl⟩ : syracuseStep 1153615 = 1730423) B1730423
theorem B11082419 : Blo 682313 11082419 := bstep (se 1 (by rfl) ⟨8311814, by rfl⟩ : syracuseStep 11082419 = 16623629) B16623629
theorem B1153865 : Blo 682313 1153865 := bstep (se 2 (by rfl) ⟨432699, by rfl⟩ : syracuseStep 1153865 = 865399) B865399
theorem B2595847 : Blo 682313 2595847 := bstep (se 1 (by rfl) ⟨1946885, by rfl⟩ : syracuseStep 2595847 = 3893771) B3893771
theorem B924871 : Blo 682313 924871 := bstep (se 1 (by rfl) ⟨693653, by rfl⟩ : syracuseStep 924871 = 1387307) B1387307
theorem B1154297 : Blo 682313 1154297 := bstep (se 2 (by rfl) ⟨432861, by rfl⟩ : syracuseStep 1154297 = 865723) B865723
theorem B3710231 : Blo 682313 3710231 := bstep (se 1 (by rfl) ⟨2782673, by rfl⟩ : syracuseStep 3710231 = 5565347) B5565347
theorem B3513773 : Blo 682313 3513773 := bstep (se 3 (by rfl) ⟨658832, by rfl⟩ : syracuseStep 3513773 = 1317665) B1317665
theorem B1154479 : Blo 682313 1154479 := bstep (se 1 (by rfl) ⟨865859, by rfl⟩ : syracuseStep 1154479 = 1731719) B1731719
theorem B2596333 : Blo 682313 2596333 := bstep (se 3 (by rfl) ⟨486812, by rfl⟩ : syracuseStep 2596333 = 973625) B973625
theorem B1154567 : Blo 682313 1154567 := bstep (se 1 (by rfl) ⟨865925, by rfl⟩ : syracuseStep 1154567 = 1731851) B1731851
theorem B1023497 : Blo 682313 1023497 := bstep (se 2 (by rfl) ⟨383811, by rfl⟩ : syracuseStep 1023497 = 767623) B767623
theorem B1023527 : Blo 682313 1023527 := bstep (se 1 (by rfl) ⟨767645, by rfl⟩ : syracuseStep 1023527 = 1535291) B1535291
theorem B1023611 : Blo 682313 1023611 := bstep (se 1 (by rfl) ⟨767708, by rfl⟩ : syracuseStep 1023611 = 1535417) B1535417
theorem B4169339 : Blo 682313 4169339 := bstep (se 1 (by rfl) ⟨3127004, by rfl⟩ : syracuseStep 4169339 = 6254009) B6254009
theorem B1023737 : Blo 682313 1023737 := bstep (se 2 (by rfl) ⟨383901, by rfl⟩ : syracuseStep 1023737 = 767803) B767803
theorem B2596637 : Blo 682313 2596637 := bstep (se 3 (by rfl) ⟨486869, by rfl⟩ : syracuseStep 2596637 = 973739) B973739
theorem B1384265 : Blo 682313 1384265 := bstep (se 2 (by rfl) ⟨519099, by rfl⟩ : syracuseStep 1384265 = 1038199) B1038199
theorem B1023839 : Blo 682313 1023839 := bstep (se 1 (by rfl) ⟨767879, by rfl⟩ : syracuseStep 1023839 = 1535759) B1535759
theorem B1154911 : Blo 682313 1154911 := bstep (se 1 (by rfl) ⟨866183, by rfl⟩ : syracuseStep 1154911 = 1732367) B1732367
theorem B1023851 : Blo 682313 1023851 := bstep (se 1 (by rfl) ⟨767888, by rfl⟩ : syracuseStep 1023851 = 1535777) B1535777
theorem B1154999 : Blo 682313 1154999 := bstep (se 1 (by rfl) ⟨866249, by rfl⟩ : syracuseStep 1154999 = 1732499) B1732499
theorem B1024079 : Blo 682313 1024079 := bstep (se 1 (by rfl) ⟨768059, by rfl⟩ : syracuseStep 1024079 = 1536119) B1536119
theorem B729211 : Blo 682313 729211 := bstep (se 1 (by rfl) ⟨546908, by rfl⟩ : syracuseStep 729211 = 1093817) B1093817
theorem B63971477 : Blo 682313 63971477 := bstep (se 6 (by rfl) ⟨1499331, by rfl⟩ : syracuseStep 63971477 = 2998663) B2998663
theorem B5546141 : Blo 682313 5546141 := bstep (se 3 (by rfl) ⟨1039901, by rfl⟩ : syracuseStep 5546141 = 2079803) B2079803
theorem B1024199 : Blo 682313 1024199 := bstep (se 1 (by rfl) ⟨768149, by rfl⟩ : syracuseStep 1024199 = 1536299) B1536299
theorem B1024361 : Blo 682313 1024361 := bstep (se 2 (by rfl) ⟨384135, by rfl⟩ : syracuseStep 1024361 = 768271) B768271
theorem B3285353 : Blo 682313 3285353 := bstep (se 2 (by rfl) ⟨1232007, by rfl⟩ : syracuseStep 3285353 = 2464015) B2464015
theorem B1384865 : Blo 682313 1384865 := bstep (se 2 (by rfl) ⟨519324, by rfl⟩ : syracuseStep 1384865 = 1038649) B1038649
theorem B1024439 : Blo 682313 1024439 := bstep (se 1 (by rfl) ⟨768329, by rfl⟩ : syracuseStep 1024439 = 1536659) B1536659
theorem B1024475 : Blo 682313 1024475 := bstep (se 1 (by rfl) ⟨768356, by rfl⟩ : syracuseStep 1024475 = 1536713) B1536713
theorem B1155593 : Blo 682313 1155593 := bstep (se 2 (by rfl) ⟨433347, by rfl⟩ : syracuseStep 1155593 = 866695) B866695
theorem B1155755 : Blo 682313 1155755 := bstep (se 1 (by rfl) ⟨866816, by rfl⟩ : syracuseStep 1155755 = 1733633) B1733633
theorem B1024943 : Blo 682313 1024943 := bstep (se 1 (by rfl) ⟨768707, by rfl⟩ : syracuseStep 1024943 = 1537415) B1537415
theorem B730031 : Blo 682313 730031 := bstep (se 1 (by rfl) ⟨547523, by rfl⟩ : syracuseStep 730031 = 1095047) B1095047
theorem B2335675 : Blo 682313 2335675 := bstep (se 1 (by rfl) ⟨1751756, by rfl⟩ : syracuseStep 2335675 = 3503513) B3503513
theorem B1025033 : Blo 682313 1025033 := bstep (se 2 (by rfl) ⟨384387, by rfl⟩ : syracuseStep 1025033 = 768775) B768775
theorem B2302991 : Blo 682313 2302991 := bstep (se 1 (by rfl) ⟨1727243, by rfl⟩ : syracuseStep 2302991 = 3454487) B3454487
theorem B1025063 : Blo 682313 1025063 := bstep (se 1 (by rfl) ⟨768797, by rfl⟩ : syracuseStep 1025063 = 1537595) B1537595
theorem B1156153 : Blo 682313 1156153 := bstep (se 2 (by rfl) ⟨433557, by rfl⟩ : syracuseStep 1156153 = 867115) B867115
theorem B1025147 : Blo 682313 1025147 := bstep (se 1 (by rfl) ⟨768860, by rfl⟩ : syracuseStep 1025147 = 1537721) B1537721
theorem B1156295 : Blo 682313 1156295 := bstep (se 1 (by rfl) ⟨867221, by rfl⟩ : syracuseStep 1156295 = 1734443) B1734443
theorem B1025273 : Blo 682313 1025273 := bstep (se 2 (by rfl) ⟨384477, by rfl⟩ : syracuseStep 1025273 = 768955) B768955
theorem B1025375 : Blo 682313 1025375 := bstep (se 1 (by rfl) ⟨769031, by rfl⟩ : syracuseStep 1025375 = 1538063) B1538063
theorem B2139497 : Blo 682313 2139497 := bstep (se 2 (by rfl) ⟨802311, by rfl⟩ : syracuseStep 2139497 = 1604623) B1604623
theorem B1156457 : Blo 682313 1156457 := bstep (se 2 (by rfl) ⟨433671, by rfl⟩ : syracuseStep 1156457 = 867343) B867343
theorem B1025387 : Blo 682313 1025387 := bstep (se 1 (by rfl) ⟨769040, by rfl⟩ : syracuseStep 1025387 = 1538081) B1538081
theorem B730663 : Blo 682313 730663 := bstep (se 1 (by rfl) ⟨547997, by rfl⟩ : syracuseStep 730663 = 1095995) B1095995
theorem B1025615 : Blo 682313 1025615 := bstep (se 1 (by rfl) ⟨769211, by rfl⟩ : syracuseStep 1025615 = 1538423) B1538423
theorem B2303585 : Blo 682313 2303585 := bstep (se 2 (by rfl) ⟨863844, by rfl⟩ : syracuseStep 2303585 = 1727689) B1727689
theorem B1025735 : Blo 682313 1025735 := bstep (se 1 (by rfl) ⟨769301, by rfl⟩ : syracuseStep 1025735 = 1538603) B1538603
theorem B1156855 : Blo 682313 1156855 := bstep (se 1 (by rfl) ⟨867641, by rfl⟩ : syracuseStep 1156855 = 1735283) B1735283
theorem B1025897 : Blo 682313 1025897 := bstep (se 2 (by rfl) ⟨384711, by rfl⟩ : syracuseStep 1025897 = 769423) B769423
theorem B2598763 : Blo 682313 2598763 := bstep (se 1 (by rfl) ⟨1949072, by rfl⟩ : syracuseStep 2598763 = 3898145) B3898145
theorem B1025975 : Blo 682313 1025975 := bstep (se 1 (by rfl) ⟨769481, by rfl⟩ : syracuseStep 1025975 = 1538963) B1538963
theorem B1157051 : Blo 682313 1157051 := bstep (se 1 (by rfl) ⟨867788, by rfl⟩ : syracuseStep 1157051 = 1735577) B1735577
theorem B1026011 : Blo 682313 1026011 := bstep (se 1 (by rfl) ⟨769508, by rfl⟩ : syracuseStep 1026011 = 1539017) B1539017
theorem B1157159 : Blo 682313 1157159 := bstep (se 1 (by rfl) ⟨867869, by rfl⟩ : syracuseStep 1157159 = 1735739) B1735739
theorem B1386553 : Blo 682313 1386553 := bstep (se 2 (by rfl) ⟨519957, by rfl⟩ : syracuseStep 1386553 = 1039915) B1039915
theorem B1157449 : Blo 682313 1157449 := bstep (se 2 (by rfl) ⟨434043, by rfl⟩ : syracuseStep 1157449 = 868087) B868087
theorem B1157483 : Blo 682313 1157483 := bstep (se 1 (by rfl) ⟨868112, by rfl⟩ : syracuseStep 1157483 = 1736225) B1736225
theorem B1026479 : Blo 682313 1026479 := bstep (se 1 (by rfl) ⟨769859, by rfl⟩ : syracuseStep 1026479 = 1539719) B1539719
theorem B1026569 : Blo 682313 1026569 := bstep (se 2 (by rfl) ⟨384963, by rfl⟩ : syracuseStep 1026569 = 769927) B769927
theorem B1026599 : Blo 682313 1026599 := bstep (se 1 (by rfl) ⟨769949, by rfl⟩ : syracuseStep 1026599 = 1539899) B1539899
theorem B1026683 : Blo 682313 1026683 := bstep (se 1 (by rfl) ⟨770012, by rfl⟩ : syracuseStep 1026683 = 1540025) B1540025
theorem B1026809 : Blo 682313 1026809 := bstep (se 2 (by rfl) ⟨385053, by rfl⟩ : syracuseStep 1026809 = 770107) B770107
theorem B1157881 : Blo 682313 1157881 := bstep (se 2 (by rfl) ⟨434205, by rfl⟩ : syracuseStep 1157881 = 868411) B868411
theorem B1026911 : Blo 682313 1026911 := bstep (se 1 (by rfl) ⟨770183, by rfl⟩ : syracuseStep 1026911 = 1540367) B1540367
theorem B1026923 : Blo 682313 1026923 := bstep (se 1 (by rfl) ⟨770192, by rfl⟩ : syracuseStep 1026923 = 1540385) B1540385
theorem B5188535 : Blo 682313 5188535 := bstep (se 1 (by rfl) ⟨3891401, by rfl⟩ : syracuseStep 5188535 = 7782803) B7782803
theorem B1158151 : Blo 682313 1158151 := bstep (se 1 (by rfl) ⟨868613, by rfl⟩ : syracuseStep 1158151 = 1737227) B1737227
theorem B2305043 : Blo 682313 2305043 := bstep (se 1 (by rfl) ⟨1728782, by rfl⟩ : syracuseStep 2305043 = 3457565) B3457565
theorem B1027151 : Blo 682313 1027151 := bstep (se 1 (by rfl) ⟨770363, by rfl⟩ : syracuseStep 1027151 = 1540727) B1540727
theorem B1027271 : Blo 682313 1027271 := bstep (se 1 (by rfl) ⟨770453, by rfl⟩ : syracuseStep 1027271 = 1540907) B1540907
theorem B63253781 : Blo 682313 63253781 := bstep (se 6 (by rfl) ⟨1482510, by rfl⟩ : syracuseStep 63253781 = 2965021) B2965021
theorem B2305367 : Blo 682313 2305367 := bstep (se 1 (by rfl) ⟨1729025, by rfl⟩ : syracuseStep 2305367 = 3458051) B3458051
theorem B1027433 : Blo 682313 1027433 := bstep (se 2 (by rfl) ⟨385287, by rfl⟩ : syracuseStep 1027433 = 770575) B770575
theorem B1027511 : Blo 682313 1027511 := bstep (se 1 (by rfl) ⟨770633, by rfl⟩ : syracuseStep 1027511 = 1541267) B1541267
theorem B1027547 : Blo 682313 1027547 := bstep (se 1 (by rfl) ⟨770660, by rfl⟩ : syracuseStep 1027547 = 1541321) B1541321
theorem B39562829 : Blo 682313 39562829 := bstep (se 3 (by rfl) ⟨7418030, by rfl⟩ : syracuseStep 39562829 = 14836061) B14836061
theorem B1846973 : Blo 682313 1846973 := bstep (se 3 (by rfl) ⟨346307, by rfl⟩ : syracuseStep 1846973 = 692615) B692615
theorem B1945417 : Blo 682313 1945417 := bstep (se 2 (by rfl) ⟨729531, by rfl⟩ : syracuseStep 1945417 = 1459063) B1459063
theorem B1093483 : Blo 682313 1093483 := bstep (se 1 (by rfl) ⟨820112, by rfl⟩ : syracuseStep 1093483 = 1640225) B1640225
theorem B1945451 : Blo 682313 1945451 := bstep (se 1 (by rfl) ⟨1459088, by rfl⟩ : syracuseStep 1945451 = 2918177) B2918177
theorem B1028015 : Blo 682313 1028015 := bstep (se 1 (by rfl) ⟨771011, by rfl⟩ : syracuseStep 1028015 = 1542023) B1542023
theorem B6565819 : Blo 682313 6565819 := bstep (se 1 (by rfl) ⟨4924364, by rfl⟩ : syracuseStep 6565819 = 9848729) B9848729
theorem B1028105 : Blo 682313 1028105 := bstep (se 2 (by rfl) ⟨385539, by rfl⟩ : syracuseStep 1028105 = 771079) B771079
theorem B1028135 : Blo 682313 1028135 := bstep (se 1 (by rfl) ⟨771101, by rfl⟩ : syracuseStep 1028135 = 1542203) B1542203
theorem B7385165 : Blo 682313 7385165 := bstep (se 3 (by rfl) ⟨1384718, by rfl⟩ : syracuseStep 7385165 = 2769437) B2769437
theorem B1028219 : Blo 682313 1028219 := bstep (se 1 (by rfl) ⟨771164, by rfl⟩ : syracuseStep 1028219 = 1542329) B1542329
theorem B1028345 : Blo 682313 1028345 := bstep (se 2 (by rfl) ⟨385629, by rfl⟩ : syracuseStep 1028345 = 771259) B771259
theorem B1028447 : Blo 682313 1028447 := bstep (se 1 (by rfl) ⟨771335, by rfl⟩ : syracuseStep 1028447 = 1542671) B1542671
theorem B5189993 : Blo 682313 5189993 := bstep (se 2 (by rfl) ⟨1946247, by rfl⟩ : syracuseStep 5189993 = 3892495) B3892495
theorem B1028459 : Blo 682313 1028459 := bstep (se 1 (by rfl) ⟨771344, by rfl⟩ : syracuseStep 1028459 = 1542689) B1542689
theorem B2306447 : Blo 682313 2306447 := bstep (se 1 (by rfl) ⟨1729835, by rfl⟩ : syracuseStep 2306447 = 3459671) B3459671
theorem B864695 : Blo 682313 864695 := bstep (se 1 (by rfl) ⟨648521, by rfl⟩ : syracuseStep 864695 = 1297043) B1297043
theorem B2601497 : Blo 682313 2601497 := bstep (se 2 (by rfl) ⟨975561, by rfl⟩ : syracuseStep 2601497 = 1951123) B1951123
theorem B864847 : Blo 682313 864847 := bstep (se 1 (by rfl) ⟨648635, by rfl⟩ : syracuseStep 864847 = 1297271) B1297271
theorem B1028687 : Blo 682313 1028687 := bstep (se 1 (by rfl) ⟨771515, by rfl⟩ : syracuseStep 1028687 = 1543031) B1543031
theorem B1028807 : Blo 682313 1028807 := bstep (se 1 (by rfl) ⟨771605, by rfl⟩ : syracuseStep 1028807 = 1543211) B1543211
theorem B2306771 : Blo 682313 2306771 := bstep (se 1 (by rfl) ⟨1730078, by rfl⟩ : syracuseStep 2306771 = 3460157) B3460157
theorem B5845715 : Blo 682313 5845715 := bstep (se 1 (by rfl) ⟨4384286, by rfl⟩ : syracuseStep 5845715 = 8768573) B8768573
theorem B71054093 : Blo 682313 71054093 := bstep (se 3 (by rfl) ⟨13322642, by rfl⟩ : syracuseStep 71054093 = 26645285) B26645285
theorem B1028969 : Blo 682313 1028969 := bstep (se 2 (by rfl) ⟨385863, by rfl⟩ : syracuseStep 1028969 = 771727) B771727
theorem B1029047 : Blo 682313 1029047 := bstep (se 1 (by rfl) ⟨771785, by rfl⟩ : syracuseStep 1029047 = 1543571) B1543571
theorem B1029083 : Blo 682313 1029083 := bstep (se 1 (by rfl) ⟨771812, by rfl⟩ : syracuseStep 1029083 = 1543625) B1543625
theorem B18691073 : Blo 682313 18691073 := bstep (se 2 (by rfl) ⟨7009152, by rfl⟩ : syracuseStep 18691073 = 14018305) B14018305
theorem B2634947 : Blo 682313 2634947 := bstep (se 1 (by rfl) ⟨1976210, by rfl⟩ : syracuseStep 2634947 = 3952421) B3952421
theorem B2471293 : Blo 682313 2471293 := bstep (se 3 (by rfl) ⟨463367, by rfl⟩ : syracuseStep 2471293 = 926735) B926735
theorem B1947023 : Blo 682313 1947023 := bstep (se 1 (by rfl) ⟨1460267, by rfl⟩ : syracuseStep 1947023 = 2920535) B2920535
theorem B2963083 : Blo 682313 2963083 := bstep (se 1 (by rfl) ⟨2222312, by rfl⟩ : syracuseStep 2963083 = 4444625) B4444625
theorem B865991 : Blo 682313 865991 := bstep (se 1 (by rfl) ⟨649493, by rfl⟩ : syracuseStep 865991 = 1298987) B1298987
theorem B1783625 : Blo 682313 1783625 := bstep (se 2 (by rfl) ⟨668859, by rfl⟩ : syracuseStep 1783625 = 1337719) B1337719
theorem B767839 : Blo 682313 767839 := bstep (se 1 (by rfl) ⟨575879, by rfl⟩ : syracuseStep 767839 = 1151759) B1151759
theorem B866143 : Blo 682313 866143 := bstep (se 1 (by rfl) ⟨649607, by rfl⟩ : syracuseStep 866143 = 1299215) B1299215
theorem B2307959 : Blo 682313 2307959 := bstep (se 1 (by rfl) ⟨1730969, by rfl⟩ : syracuseStep 2307959 = 3461939) B3461939
theorem B2308175 : Blo 682313 2308175 := bstep (se 1 (by rfl) ⟨1731131, by rfl⟩ : syracuseStep 2308175 = 3462263) B3462263
theorem B2603123 : Blo 682313 2603123 := bstep (se 1 (by rfl) ⟨1952342, by rfl⟩ : syracuseStep 2603123 = 3904685) B3904685
theorem B768199 : Blo 682313 768199 := bstep (se 1 (by rfl) ⟨576149, by rfl⟩ : syracuseStep 768199 = 1152299) B1152299
theorem B5191937 : Blo 682313 5191937 := bstep (se 2 (by rfl) ⟨1946976, by rfl⟩ : syracuseStep 5191937 = 3893953) B3893953
theorem B8894771 : Blo 682313 8894771 := bstep (se 1 (by rfl) ⟨6671078, by rfl⟩ : syracuseStep 8894771 = 13342157) B13342157
theorem B2308553 : Blo 682313 2308553 := bstep (se 2 (by rfl) ⟨865707, by rfl⟩ : syracuseStep 2308553 = 1731415) B1731415
theorem B7027181 : Blo 682313 7027181 := bstep (se 3 (by rfl) ⟨1317596, by rfl⟩ : syracuseStep 7027181 = 2635193) B2635193
theorem B2308823 : Blo 682313 2308823 := bstep (se 1 (by rfl) ⟨1731617, by rfl⟩ : syracuseStep 2308823 = 3463235) B3463235
theorem B1096553 : Blo 682313 1096553 := bstep (se 2 (by rfl) ⟨411207, by rfl⟩ : syracuseStep 1096553 = 822415) B822415
theorem B4209515 : Blo 682313 4209515 := bstep (se 1 (by rfl) ⟨3157136, by rfl⟩ : syracuseStep 4209515 = 6314273) B6314273
theorem B2309039 : Blo 682313 2309039 := bstep (se 1 (by rfl) ⟨1731779, by rfl⟩ : syracuseStep 2309039 = 3463559) B3463559
theorem B998363 : Blo 682313 998363 := bstep (se 1 (by rfl) ⟨748772, by rfl⟩ : syracuseStep 998363 = 1497545) B1497545
theorem B769063 : Blo 682313 769063 := bstep (se 1 (by rfl) ⟨576797, by rfl⟩ : syracuseStep 769063 = 1153595) B1153595
theorem B2604413 : Blo 682313 2604413 := bstep (se 3 (by rfl) ⟨488327, by rfl⟩ : syracuseStep 2604413 = 976655) B976655
theorem B1457875 : Blo 682313 1457875 := bstep (se 1 (by rfl) ⟨1093406, by rfl⟩ : syracuseStep 1457875 = 2186813) B2186813
theorem B868315 : Blo 682313 868315 := bstep (se 1 (by rfl) ⟨651236, by rfl⟩ : syracuseStep 868315 = 1302473) B1302473
theorem B5554183 : Blo 682313 5554183 := bstep (se 1 (by rfl) ⟨4165637, by rfl⟩ : syracuseStep 5554183 = 8331275) B8331275
theorem B5849405 : Blo 682313 5849405 := bstep (se 3 (by rfl) ⟨1096763, by rfl⟩ : syracuseStep 5849405 = 2193527) B2193527
theorem B2965997 : Blo 682313 2965997 := bstep (se 3 (by rfl) ⟨556124, by rfl⟩ : syracuseStep 2965997 = 1112249) B1112249
theorem B770683 : Blo 682313 770683 := bstep (se 1 (by rfl) ⟨578012, by rfl⟩ : syracuseStep 770683 = 1156025) B1156025
theorem B771151 : Blo 682313 771151 := bstep (se 1 (by rfl) ⟨578363, by rfl⟩ : syracuseStep 771151 = 1156727) B1156727
theorem B2311415 : Blo 682313 2311415 := bstep (se 1 (by rfl) ⟨1733561, by rfl⟩ : syracuseStep 2311415 = 3467123) B3467123
theorem B771547 : Blo 682313 771547 := bstep (se 1 (by rfl) ⟨578660, by rfl⟩ : syracuseStep 771547 = 1157321) B1157321
theorem B1459721 : Blo 682313 1459721 := bstep (se 2 (by rfl) ⟨547395, by rfl⟩ : syracuseStep 1459721 = 1094791) B1094791
theorem B2311739 : Blo 682313 2311739 := bstep (se 1 (by rfl) ⟨1733804, by rfl⟩ : syracuseStep 2311739 = 3467609) B3467609
theorem B1295995 : Blo 682313 1295995 := bstep (se 1 (by rfl) ⟨971996, by rfl⟩ : syracuseStep 1295995 = 1943993) B1943993
theorem B3458699 : Blo 682313 3458699 := bstep (se 1 (by rfl) ⟨2594024, by rfl⟩ : syracuseStep 3458699 = 5188049) B5188049
theorem B1296071 : Blo 682313 1296071 := bstep (se 1 (by rfl) ⟨972053, by rfl⟩ : syracuseStep 1296071 = 1944107) B1944107
theorem B16893755 : Blo 682313 16893755 := bstep (se 1 (by rfl) ⟨12670316, by rfl⟩ : syracuseStep 16893755 = 25340633) B25340633
theorem B2312009 : Blo 682313 2312009 := bstep (se 2 (by rfl) ⟨867003, by rfl⟩ : syracuseStep 2312009 = 1734007) B1734007
theorem B772015 : Blo 682313 772015 := bstep (se 1 (by rfl) ⟨579011, by rfl⟩ : syracuseStep 772015 = 1158023) B1158023
theorem B1296481 : Blo 682313 1296481 := bstep (se 2 (by rfl) ⟨486180, by rfl⟩ : syracuseStep 1296481 = 972361) B972361
theorem B1296823 : Blo 682313 1296823 := bstep (se 1 (by rfl) ⟨972617, by rfl⟩ : syracuseStep 1296823 = 1945235) B1945235
theorem B14797241 : Blo 682313 14797241 := bstep (se 2 (by rfl) ⟨5548965, by rfl⟩ : syracuseStep 14797241 = 11097931) B11097931
theorem B5196311 : Blo 682313 5196311 := bstep (se 1 (by rfl) ⟨3897233, by rfl⟩ : syracuseStep 5196311 = 7794467) B7794467
theorem B1952353 : Blo 682313 1952353 := bstep (se 2 (by rfl) ⟨732132, by rfl⟩ : syracuseStep 1952353 = 1464265) B1464265
theorem B2771579 : Blo 682313 2771579 := bstep (se 1 (by rfl) ⟨2078684, by rfl⟩ : syracuseStep 2771579 = 4157369) B4157369
theorem B14011015 : Blo 682313 14011015 := bstep (se 1 (by rfl) ⟨10508261, by rfl⟩ : syracuseStep 14011015 = 21016523) B21016523
theorem B1297225 : Blo 682313 1297225 := bstep (se 2 (by rfl) ⟨486459, by rfl⟩ : syracuseStep 1297225 = 972919) B972919
theorem B1231777 : Blo 682313 1231777 := bstep (se 2 (by rfl) ⟨461916, by rfl⟩ : syracuseStep 1231777 = 923833) B923833
theorem B2313143 : Blo 682313 2313143 := bstep (se 1 (by rfl) ⟨1734857, by rfl⟩ : syracuseStep 2313143 = 3469715) B3469715
theorem B7785719 : Blo 682313 7785719 := bstep (se 1 (by rfl) ⟨5839289, by rfl⟩ : syracuseStep 7785719 = 11678579) B11678579
theorem B2313737 : Blo 682313 2313737 := bstep (se 2 (by rfl) ⟨867651, by rfl⟩ : syracuseStep 2313737 = 1735303) B1735303
theorem B1297939 : Blo 682313 1297939 := bstep (se 1 (by rfl) ⟨973454, by rfl⟩ : syracuseStep 1297939 = 1946909) B1946909
theorem B1461959 : Blo 682313 1461959 := bstep (se 1 (by rfl) ⟨1096469, by rfl⟩ : syracuseStep 1461959 = 2192939) B2192939
theorem B5263147 : Blo 682313 5263147 := bstep (se 1 (by rfl) ⟨3947360, by rfl⟩ : syracuseStep 5263147 = 7894721) B7894721
theorem B1298281 : Blo 682313 1298281 := bstep (se 2 (by rfl) ⟨486855, by rfl⟩ : syracuseStep 1298281 = 973711) B973711
theorem B1232815 : Blo 682313 1232815 := bstep (se 1 (by rfl) ⟨924611, by rfl⟩ : syracuseStep 1232815 = 1849223) B1849223
theorem B1953811 : Blo 682313 1953811 := bstep (se 1 (by rfl) ⟨1465358, by rfl⟩ : syracuseStep 1953811 = 2930717) B2930717
theorem B4378853 : Blo 682313 4378853 := bstep (se 4 (by rfl) ⟨410517, by rfl⟩ : syracuseStep 4378853 = 821035) B821035
theorem B1954039 : Blo 682313 1954039 := bstep (se 1 (by rfl) ⟨1465529, by rfl⟩ : syracuseStep 1954039 = 2931059) B2931059
theorem B2314601 : Blo 682313 2314601 := bstep (se 2 (by rfl) ⟨867975, by rfl⟩ : syracuseStep 2314601 = 1735951) B1735951
theorem B5067245 : Blo 682313 5067245 := bstep (se 3 (by rfl) ⟨950108, by rfl⟩ : syracuseStep 5067245 = 1900217) B1900217
theorem B1954313 : Blo 682313 1954313 := bstep (se 2 (by rfl) ⟨732867, by rfl⟩ : syracuseStep 1954313 = 1465735) B1465735
theorem B971615 : Blo 682313 971615 := bstep (se 1 (by rfl) ⟨728711, by rfl⟩ : syracuseStep 971615 = 1457423) B1457423
theorem B1266607 : Blo 682313 1266607 := bstep (se 1 (by rfl) ⟨949955, by rfl⟩ : syracuseStep 1266607 = 1899911) B1899911
theorem B1561531 : Blo 682313 1561531 := bstep (se 1 (by rfl) ⟨1171148, by rfl⟩ : syracuseStep 1561531 = 2342297) B2342297
theorem B2315195 : Blo 682313 2315195 := bstep (se 1 (by rfl) ⟨1736396, by rfl⟩ : syracuseStep 2315195 = 3472793) B3472793
theorem B1234091 : Blo 682313 1234091 := bstep (se 1 (by rfl) ⟨925568, by rfl⟩ : syracuseStep 1234091 = 1851137) B1851137
theorem B1299655 : Blo 682313 1299655 := bstep (se 1 (by rfl) ⟨974741, by rfl⟩ : syracuseStep 1299655 = 1949483) B1949483
theorem B1922809 : Blo 682313 1922809 := bstep (se 2 (by rfl) ⟨721053, by rfl⟩ : syracuseStep 1922809 = 1442107) B1442107
theorem B3463073 : Blo 682313 3463073 := bstep (se 2 (by rfl) ⟨1298652, by rfl⟩ : syracuseStep 3463073 = 2597305) B2597305
theorem B20043821 : Blo 682313 20043821 := bstep (se 3 (by rfl) ⟨3758216, by rfl⟩ : syracuseStep 20043821 = 7516433) B7516433
theorem B5855489 : Blo 682313 5855489 := bstep (se 2 (by rfl) ⟨2195808, by rfl⟩ : syracuseStep 5855489 = 4391617) B4391617
theorem B45504899 : Blo 682313 45504899 := bstep (se 1 (by rfl) ⟨34128674, by rfl⟩ : syracuseStep 45504899 = 68257349) B68257349
theorem B4938641 : Blo 682313 4938641 := bstep (se 2 (by rfl) ⟨1851990, by rfl⟩ : syracuseStep 4938641 = 3703981) B3703981
theorem B2775991 : Blo 682313 2775991 := bstep (se 1 (by rfl) ⟨2081993, by rfl⟩ : syracuseStep 2775991 = 4163987) B4163987
theorem B4938725 : Blo 682313 4938725 := bstep (se 4 (by rfl) ⟨463005, by rfl⟩ : syracuseStep 4938725 = 926011) B926011
theorem B1727507 : Blo 682313 1727507 := bstep (se 1 (by rfl) ⟨1295630, by rfl⟩ : syracuseStep 1727507 = 2591261) B2591261
theorem B1236065 : Blo 682313 1236065 := bstep (se 2 (by rfl) ⟨463524, by rfl⟩ : syracuseStep 1236065 = 927049) B927049
theorem B5627083 : Blo 682313 5627083 := bstep (se 1 (by rfl) ⟨4220312, by rfl⟩ : syracuseStep 5627083 = 8440625) B8440625
theorem B4742489 : Blo 682313 4742489 := bstep (se 2 (by rfl) ⟨1778433, by rfl⟩ : syracuseStep 4742489 = 3556867) B3556867
theorem B1301903 : Blo 682313 1301903 := bstep (se 1 (by rfl) ⟨976427, by rfl⟩ : syracuseStep 1301903 = 1952855) B1952855
theorem B974263 : Blo 682313 974263 := bstep (se 1 (by rfl) ⟨730697, by rfl⟩ : syracuseStep 974263 = 1461395) B1461395
theorem B1170875 : Blo 682313 1170875 := bstep (se 1 (by rfl) ⟨878156, by rfl⟩ : syracuseStep 1170875 = 1756313) B1756313
theorem B1727963 : Blo 682313 1727963 := bstep (se 1 (by rfl) ⟨1295972, by rfl⟩ : syracuseStep 1727963 = 2591945) B2591945
theorem B28171909 : Blo 682313 28171909 := bstep (se 4 (by rfl) ⟨2641116, by rfl⟩ : syracuseStep 28171909 = 5282233) B5282233
theorem B5201657 : Blo 682313 5201657 := bstep (se 2 (by rfl) ⟨1950621, by rfl⟩ : syracuseStep 5201657 = 3901243) B3901243
theorem B1335145 : Blo 682313 1335145 := bstep (se 2 (by rfl) ⟨500679, by rfl⟩ : syracuseStep 1335145 = 1001359) B1001359
theorem B1729147 : Blo 682313 1729147 := bstep (se 1 (by rfl) ⟨1296860, by rfl⟩ : syracuseStep 1729147 = 2593721) B2593721
theorem B975721 : Blo 682313 975721 := bstep (se 2 (by rfl) ⟨365895, by rfl⟩ : syracuseStep 975721 = 731791) B731791
theorem B975835 : Blo 682313 975835 := bstep (se 1 (by rfl) ⟨731876, by rfl⟩ : syracuseStep 975835 = 1463753) B1463753
theorem B33743891 : Blo 682313 33743891 := bstep (se 1 (by rfl) ⟨25307918, by rfl⟩ : syracuseStep 33743891 = 50615837) B50615837
theorem B5334083 : Blo 682313 5334083 := bstep (se 1 (by rfl) ⟨4000562, by rfl⟩ : syracuseStep 5334083 = 8001125) B8001125
theorem B5203115 : Blo 682313 5203115 := bstep (se 1 (by rfl) ⟨3902336, by rfl⟩ : syracuseStep 5203115 = 7804673) B7804673
theorem B4941323 : Blo 682313 4941323 := bstep (se 1 (by rfl) ⟨3705992, by rfl⟩ : syracuseStep 4941323 = 7411985) B7411985
theorem B5203601 : Blo 682313 5203601 := bstep (se 2 (by rfl) ⟨1951350, by rfl⟩ : syracuseStep 5203601 = 3902701) B3902701
theorem B976735 : Blo 682313 976735 := bstep (se 1 (by rfl) ⟨732551, by rfl⟩ : syracuseStep 976735 = 1465103) B1465103
theorem B22439873 : Blo 682313 22439873 := bstep (se 2 (by rfl) ⟨8414952, by rfl⟩ : syracuseStep 22439873 = 16829905) B16829905
theorem B3958721 : Blo 682313 3958721 := bstep (se 2 (by rfl) ⟨1484520, by rfl⟩ : syracuseStep 3958721 = 2969041) B2969041
theorem B1108091 : Blo 682313 1108091 := bstep (se 1 (by rfl) ⟨831068, by rfl⟩ : syracuseStep 1108091 = 1662137) B1662137
theorem B14838065 : Blo 682313 14838065 := bstep (se 2 (by rfl) ⟨5564274, by rfl⟩ : syracuseStep 14838065 = 11128549) B11128549
theorem B682319 : Blo 682313 682319 := bstep (se 1 (by rfl) ⟨511739, by rfl⟩ : syracuseStep 682319 = 1023479) B1023479
theorem B682335 : Blo 682313 682335 := bstep (se 1 (by rfl) ⟨511751, by rfl⟩ : syracuseStep 682335 = 1023503) B1023503
theorem B682363 : Blo 682313 682363 := bstep (se 1 (by rfl) ⟨511772, by rfl⟩ : syracuseStep 682363 = 1023545) B1023545
theorem B682415 : Blo 682313 682415 := bstep (se 1 (by rfl) ⟨511811, by rfl⟩ : syracuseStep 682415 = 1023623) B1023623
theorem B682439 : Blo 682313 682439 := bstep (se 1 (by rfl) ⟨511829, by rfl⟩ : syracuseStep 682439 = 1023659) B1023659
theorem B682459 : Blo 682313 682459 := bstep (se 1 (by rfl) ⟨511844, by rfl⟩ : syracuseStep 682459 = 1023689) B1023689
theorem B682535 : Blo 682313 682535 := bstep (se 1 (by rfl) ⟨511901, by rfl⟩ : syracuseStep 682535 = 1023803) B1023803
theorem B682575 : Blo 682313 682575 := bstep (se 1 (by rfl) ⟨511931, by rfl⟩ : syracuseStep 682575 = 1023863) B1023863
theorem B682591 : Blo 682313 682591 := bstep (se 1 (by rfl) ⟨511943, by rfl⟩ : syracuseStep 682591 = 1023887) B1023887
theorem B682619 : Blo 682313 682619 := bstep (se 1 (by rfl) ⟨511964, by rfl⟩ : syracuseStep 682619 = 1023929) B1023929
theorem B682671 : Blo 682313 682671 := bstep (se 1 (by rfl) ⟨512003, by rfl⟩ : syracuseStep 682671 = 1024007) B1024007
theorem B682695 : Blo 682313 682695 := bstep (se 1 (by rfl) ⟨512021, by rfl⟩ : syracuseStep 682695 = 1024043) B1024043
theorem B682715 : Blo 682313 682715 := bstep (se 1 (by rfl) ⟨512036, by rfl⟩ : syracuseStep 682715 = 1024073) B1024073
theorem B13200101 : Blo 682313 13200101 := bstep (se 4 (by rfl) ⟨1237509, by rfl⟩ : syracuseStep 13200101 = 2475019) B2475019
theorem B682791 : Blo 682313 682791 := bstep (se 1 (by rfl) ⟨512093, by rfl⟩ : syracuseStep 682791 = 1024187) B1024187
theorem B682831 : Blo 682313 682831 := bstep (se 1 (by rfl) ⟨512123, by rfl⟩ : syracuseStep 682831 = 1024247) B1024247
theorem B682847 : Blo 682313 682847 := bstep (se 1 (by rfl) ⟨512135, by rfl⟩ : syracuseStep 682847 = 1024271) B1024271
theorem B682875 : Blo 682313 682875 := bstep (se 1 (by rfl) ⟨512156, by rfl⟩ : syracuseStep 682875 = 1024313) B1024313
theorem B682927 : Blo 682313 682927 := bstep (se 1 (by rfl) ⟨512195, by rfl⟩ : syracuseStep 682927 = 1024391) B1024391
theorem B682951 : Blo 682313 682951 := bstep (se 1 (by rfl) ⟨512213, by rfl⟩ : syracuseStep 682951 = 1024427) B1024427
theorem B682971 : Blo 682313 682971 := bstep (se 1 (by rfl) ⟨512228, by rfl⟩ : syracuseStep 682971 = 1024457) B1024457
theorem B683047 : Blo 682313 683047 := bstep (se 1 (by rfl) ⟨512285, by rfl⟩ : syracuseStep 683047 = 1024571) B1024571
theorem B5205059 : Blo 682313 5205059 := bstep (se 1 (by rfl) ⟨3903794, by rfl⟩ : syracuseStep 5205059 = 7807589) B7807589
theorem B683087 : Blo 682313 683087 := bstep (se 1 (by rfl) ⟨512315, by rfl⟩ : syracuseStep 683087 = 1024631) B1024631
theorem B683103 : Blo 682313 683103 := bstep (se 1 (by rfl) ⟨512327, by rfl⟩ : syracuseStep 683103 = 1024655) B1024655
theorem B683131 : Blo 682313 683131 := bstep (se 1 (by rfl) ⟨512348, by rfl⟩ : syracuseStep 683131 = 1024697) B1024697
theorem B683183 : Blo 682313 683183 := bstep (se 1 (by rfl) ⟨512387, by rfl⟩ : syracuseStep 683183 = 1024775) B1024775
theorem B683207 : Blo 682313 683207 := bstep (se 1 (by rfl) ⟨512405, by rfl⟩ : syracuseStep 683207 = 1024811) B1024811
theorem B683227 : Blo 682313 683227 := bstep (se 1 (by rfl) ⟨512420, by rfl⟩ : syracuseStep 683227 = 1024841) B1024841
theorem B8416547 : Blo 682313 8416547 := bstep (se 1 (by rfl) ⟨6312410, by rfl⟩ : syracuseStep 8416547 = 12624821) B12624821
theorem B683303 : Blo 682313 683303 := bstep (se 1 (by rfl) ⟨512477, by rfl⟩ : syracuseStep 683303 = 1024955) B1024955
theorem B683343 : Blo 682313 683343 := bstep (se 1 (by rfl) ⟨512507, by rfl⟩ : syracuseStep 683343 = 1025015) B1025015
theorem B683359 : Blo 682313 683359 := bstep (se 1 (by rfl) ⟨512519, by rfl⟩ : syracuseStep 683359 = 1025039) B1025039
theorem B683387 : Blo 682313 683387 := bstep (se 1 (by rfl) ⟨512540, by rfl⟩ : syracuseStep 683387 = 1025081) B1025081
theorem B683439 : Blo 682313 683439 := bstep (se 1 (by rfl) ⟨512579, by rfl⟩ : syracuseStep 683439 = 1025159) B1025159
theorem B683463 : Blo 682313 683463 := bstep (se 1 (by rfl) ⟨512597, by rfl⟩ : syracuseStep 683463 = 1025195) B1025195
theorem B683483 : Blo 682313 683483 := bstep (se 1 (by rfl) ⟨512612, by rfl⟩ : syracuseStep 683483 = 1025225) B1025225
theorem B683559 : Blo 682313 683559 := bstep (se 1 (by rfl) ⟨512669, by rfl⟩ : syracuseStep 683559 = 1025339) B1025339
theorem B683599 : Blo 682313 683599 := bstep (se 1 (by rfl) ⟨512699, by rfl⟩ : syracuseStep 683599 = 1025399) B1025399
theorem B683615 : Blo 682313 683615 := bstep (se 1 (by rfl) ⟨512711, by rfl⟩ : syracuseStep 683615 = 1025423) B1025423
theorem B683643 : Blo 682313 683643 := bstep (se 1 (by rfl) ⟨512732, by rfl⟩ : syracuseStep 683643 = 1025465) B1025465
theorem B683695 : Blo 682313 683695 := bstep (se 1 (by rfl) ⟨512771, by rfl⟩ : syracuseStep 683695 = 1025543) B1025543
theorem B1535687 : Blo 682313 1535687 := bstep (se 1 (by rfl) ⟨1151765, by rfl⟩ : syracuseStep 1535687 = 2303531) B2303531
theorem B683719 : Blo 682313 683719 := bstep (se 1 (by rfl) ⟨512789, by rfl⟩ : syracuseStep 683719 = 1025579) B1025579
theorem B683739 : Blo 682313 683739 := bstep (se 1 (by rfl) ⟨512804, by rfl⟩ : syracuseStep 683739 = 1025609) B1025609
theorem B683815 : Blo 682313 683815 := bstep (se 1 (by rfl) ⟨512861, by rfl⟩ : syracuseStep 683815 = 1025723) B1025723
theorem B683855 : Blo 682313 683855 := bstep (se 1 (by rfl) ⟨512891, by rfl⟩ : syracuseStep 683855 = 1025783) B1025783
theorem B683871 : Blo 682313 683871 := bstep (se 1 (by rfl) ⟨512903, by rfl⟩ : syracuseStep 683871 = 1025807) B1025807
theorem B3698551 : Blo 682313 3698551 := bstep (se 1 (by rfl) ⟨2773913, by rfl⟩ : syracuseStep 3698551 = 5547827) B5547827
theorem B683899 : Blo 682313 683899 := bstep (se 1 (by rfl) ⟨512924, by rfl⟩ : syracuseStep 683899 = 1025849) B1025849
theorem B42168215 : Blo 682313 42168215 := bstep (se 1 (by rfl) ⟨31626161, by rfl⟩ : syracuseStep 42168215 = 63252323) B63252323
theorem B3567521 : Blo 682313 3567521 := bstep (se 2 (by rfl) ⟨1337820, by rfl⟩ : syracuseStep 3567521 = 2675641) B2675641
theorem B683951 : Blo 682313 683951 := bstep (se 1 (by rfl) ⟨512963, by rfl⟩ : syracuseStep 683951 = 1025927) B1025927
theorem B683975 : Blo 682313 683975 := bstep (se 1 (by rfl) ⟨512981, by rfl⟩ : syracuseStep 683975 = 1025963) B1025963
theorem B683995 : Blo 682313 683995 := bstep (se 1 (by rfl) ⟨512996, by rfl⟩ : syracuseStep 683995 = 1025993) B1025993
theorem B5206031 : Blo 682313 5206031 := bstep (se 1 (by rfl) ⟨3904523, by rfl⟩ : syracuseStep 5206031 = 7809047) B7809047
theorem B684071 : Blo 682313 684071 := bstep (se 1 (by rfl) ⟨513053, by rfl⟩ : syracuseStep 684071 = 1026107) B1026107
theorem B684111 : Blo 682313 684111 := bstep (se 1 (by rfl) ⟨513083, by rfl⟩ : syracuseStep 684111 = 1026167) B1026167
theorem B684127 : Blo 682313 684127 := bstep (se 1 (by rfl) ⟨513095, by rfl⟩ : syracuseStep 684127 = 1026191) B1026191
theorem B3895411 : Blo 682313 3895411 := bstep (se 1 (by rfl) ⟨2921558, by rfl⟩ : syracuseStep 3895411 = 5843117) B5843117
theorem B684155 : Blo 682313 684155 := bstep (se 1 (by rfl) ⟨513116, by rfl⟩ : syracuseStep 684155 = 1026233) B1026233
theorem B684207 : Blo 682313 684207 := bstep (se 1 (by rfl) ⟨513155, by rfl⟩ : syracuseStep 684207 = 1026311) B1026311
theorem B684231 : Blo 682313 684231 := bstep (se 1 (by rfl) ⟨513173, by rfl⟩ : syracuseStep 684231 = 1026347) B1026347
theorem B684251 : Blo 682313 684251 := bstep (se 1 (by rfl) ⟨513188, by rfl⟩ : syracuseStep 684251 = 1026377) B1026377
theorem B2191607 : Blo 682313 2191607 := bstep (se 1 (by rfl) ⟨1643705, by rfl⟩ : syracuseStep 2191607 = 3287411) B3287411
theorem B684327 : Blo 682313 684327 := bstep (se 1 (by rfl) ⟨513245, by rfl⟩ : syracuseStep 684327 = 1026491) B1026491
theorem B684367 : Blo 682313 684367 := bstep (se 1 (by rfl) ⟨513275, by rfl⟩ : syracuseStep 684367 = 1026551) B1026551
theorem B684383 : Blo 682313 684383 := bstep (se 1 (by rfl) ⟨513287, by rfl⟩ : syracuseStep 684383 = 1026575) B1026575
theorem B684411 : Blo 682313 684411 := bstep (se 1 (by rfl) ⟨513308, by rfl⟩ : syracuseStep 684411 = 1026617) B1026617
theorem B5534081 : Blo 682313 5534081 := bstep (se 2 (by rfl) ⟨2075280, by rfl⟩ : syracuseStep 5534081 = 4150561) B4150561
theorem B684463 : Blo 682313 684463 := bstep (se 1 (by rfl) ⟨513347, by rfl⟩ : syracuseStep 684463 = 1026695) B1026695
theorem B684487 : Blo 682313 684487 := bstep (se 1 (by rfl) ⟨513365, by rfl⟩ : syracuseStep 684487 = 1026731) B1026731
theorem B684507 : Blo 682313 684507 := bstep (se 1 (by rfl) ⟨513380, by rfl⟩ : syracuseStep 684507 = 1026761) B1026761
theorem B1536551 : Blo 682313 1536551 := bstep (se 1 (by rfl) ⟨1152413, by rfl⟩ : syracuseStep 1536551 = 2304827) B2304827
theorem B684583 : Blo 682313 684583 := bstep (se 1 (by rfl) ⟨513437, by rfl⟩ : syracuseStep 684583 = 1026875) B1026875
theorem B4682299 : Blo 682313 4682299 := bstep (se 1 (by rfl) ⟨3511724, by rfl⟩ : syracuseStep 4682299 = 7023449) B7023449
theorem B684623 : Blo 682313 684623 := bstep (se 1 (by rfl) ⟨513467, by rfl⟩ : syracuseStep 684623 = 1026935) B1026935
theorem B684639 : Blo 682313 684639 := bstep (se 1 (by rfl) ⟨513479, by rfl⟩ : syracuseStep 684639 = 1026959) B1026959
theorem B684667 : Blo 682313 684667 := bstep (se 1 (by rfl) ⟨513500, by rfl⟩ : syracuseStep 684667 = 1027001) B1027001
theorem B684719 : Blo 682313 684719 := bstep (se 1 (by rfl) ⟨513539, by rfl⟩ : syracuseStep 684719 = 1027079) B1027079
theorem B684743 : Blo 682313 684743 := bstep (se 1 (by rfl) ⟨513557, by rfl⟩ : syracuseStep 684743 = 1027115) B1027115
theorem B684763 : Blo 682313 684763 := bstep (se 1 (by rfl) ⟨513572, by rfl⟩ : syracuseStep 684763 = 1027145) B1027145
theorem B11268881 : Blo 682313 11268881 := bstep (se 2 (by rfl) ⟨4225830, by rfl⟩ : syracuseStep 11268881 = 8451661) B8451661
theorem B684839 : Blo 682313 684839 := bstep (se 1 (by rfl) ⟨513629, by rfl⟩ : syracuseStep 684839 = 1027259) B1027259
theorem B2782025 : Blo 682313 2782025 := bstep (se 2 (by rfl) ⟨1043259, by rfl⟩ : syracuseStep 2782025 = 2086519) B2086519
theorem B684879 : Blo 682313 684879 := bstep (se 1 (by rfl) ⟨513659, by rfl⟩ : syracuseStep 684879 = 1027319) B1027319
theorem B1733471 : Blo 682313 1733471 := bstep (se 1 (by rfl) ⟨1300103, by rfl⟩ : syracuseStep 1733471 = 2600207) B2600207
theorem B684895 : Blo 682313 684895 := bstep (se 1 (by rfl) ⟨513671, by rfl⟩ : syracuseStep 684895 = 1027343) B1027343
theorem B1536875 : Blo 682313 1536875 := bstep (se 1 (by rfl) ⟨1152656, by rfl⟩ : syracuseStep 1536875 = 2305313) B2305313
theorem B684923 : Blo 682313 684923 := bstep (se 1 (by rfl) ⟨513692, by rfl⟩ : syracuseStep 684923 = 1027385) B1027385
theorem B1536929 : Blo 682313 1536929 := bstep (se 2 (by rfl) ⟨576348, by rfl⟩ : syracuseStep 1536929 = 1152697) B1152697
theorem B684975 : Blo 682313 684975 := bstep (se 1 (by rfl) ⟨513731, by rfl⟩ : syracuseStep 684975 = 1027463) B1027463
theorem B684999 : Blo 682313 684999 := bstep (se 1 (by rfl) ⟨513749, by rfl⟩ : syracuseStep 684999 = 1027499) B1027499
theorem B685019 : Blo 682313 685019 := bstep (se 1 (by rfl) ⟨513764, by rfl⟩ : syracuseStep 685019 = 1027529) B1027529
theorem B685095 : Blo 682313 685095 := bstep (se 1 (by rfl) ⟨513821, by rfl⟩ : syracuseStep 685095 = 1027643) B1027643
theorem B53310517 : Blo 682313 53310517 := bstep (se 5 (by rfl) ⟨2498930, by rfl⟩ : syracuseStep 53310517 = 4997861) B4997861
theorem B685135 : Blo 682313 685135 := bstep (se 1 (by rfl) ⟨513851, by rfl⟩ : syracuseStep 685135 = 1027703) B1027703
theorem B685151 : Blo 682313 685151 := bstep (se 1 (by rfl) ⟨513863, by rfl⟩ : syracuseStep 685151 = 1027727) B1027727
theorem B685179 : Blo 682313 685179 := bstep (se 1 (by rfl) ⟨513884, by rfl⟩ : syracuseStep 685179 = 1027769) B1027769
theorem B685231 : Blo 682313 685231 := bstep (se 1 (by rfl) ⟨513923, by rfl⟩ : syracuseStep 685231 = 1027847) B1027847
theorem B685255 : Blo 682313 685255 := bstep (se 1 (by rfl) ⟨513941, by rfl⟩ : syracuseStep 685255 = 1027883) B1027883
theorem B685275 : Blo 682313 685275 := bstep (se 1 (by rfl) ⟨513956, by rfl⟩ : syracuseStep 685275 = 1027913) B1027913
theorem B1537271 : Blo 682313 1537271 := bstep (se 1 (by rfl) ⟨1152953, by rfl⟩ : syracuseStep 1537271 = 2305907) B2305907
theorem B685351 : Blo 682313 685351 := bstep (se 1 (by rfl) ⟨514013, by rfl⟩ : syracuseStep 685351 = 1028027) B1028027
theorem B685391 : Blo 682313 685391 := bstep (se 1 (by rfl) ⟨514043, by rfl⟩ : syracuseStep 685391 = 1028087) B1028087
theorem B685407 : Blo 682313 685407 := bstep (se 1 (by rfl) ⟨514055, by rfl⟩ : syracuseStep 685407 = 1028111) B1028111
theorem B685435 : Blo 682313 685435 := bstep (se 1 (by rfl) ⟨514076, by rfl⟩ : syracuseStep 685435 = 1028153) B1028153
theorem B685487 : Blo 682313 685487 := bstep (se 1 (by rfl) ⟨514115, by rfl⟩ : syracuseStep 685487 = 1028231) B1028231
theorem B685511 : Blo 682313 685511 := bstep (se 1 (by rfl) ⟨514133, by rfl⟩ : syracuseStep 685511 = 1028267) B1028267
theorem B685531 : Blo 682313 685531 := bstep (se 1 (by rfl) ⟨514148, by rfl⟩ : syracuseStep 685531 = 1028297) B1028297
theorem B1734169 : Blo 682313 1734169 := bstep (se 2 (by rfl) ⟨650313, by rfl⟩ : syracuseStep 1734169 = 1300627) B1300627
theorem B685607 : Blo 682313 685607 := bstep (se 1 (by rfl) ⟨514205, by rfl⟩ : syracuseStep 685607 = 1028411) B1028411
theorem B685647 : Blo 682313 685647 := bstep (se 1 (by rfl) ⟨514235, by rfl⟩ : syracuseStep 685647 = 1028471) B1028471
theorem B685663 : Blo 682313 685663 := bstep (se 1 (by rfl) ⟨514247, by rfl⟩ : syracuseStep 685663 = 1028495) B1028495
theorem B685691 : Blo 682313 685691 := bstep (se 1 (by rfl) ⟨514268, by rfl⟩ : syracuseStep 685691 = 1028537) B1028537
theorem B685743 : Blo 682313 685743 := bstep (se 1 (by rfl) ⟨514307, by rfl⟩ : syracuseStep 685743 = 1028615) B1028615
theorem B685767 : Blo 682313 685767 := bstep (se 1 (by rfl) ⟨514325, by rfl⟩ : syracuseStep 685767 = 1028651) B1028651
theorem B685787 : Blo 682313 685787 := bstep (se 1 (by rfl) ⟨514340, by rfl⟩ : syracuseStep 685787 = 1028681) B1028681
theorem B35452673 : Blo 682313 35452673 := bstep (se 2 (by rfl) ⟨13294752, by rfl⟩ : syracuseStep 35452673 = 26589505) B26589505
theorem B685863 : Blo 682313 685863 := bstep (se 1 (by rfl) ⟨514397, by rfl⟩ : syracuseStep 685863 = 1028795) B1028795
theorem B1537865 : Blo 682313 1537865 := bstep (se 2 (by rfl) ⟨576699, by rfl⟩ : syracuseStep 1537865 = 1153399) B1153399
theorem B1734473 : Blo 682313 1734473 := bstep (se 2 (by rfl) ⟨650427, by rfl⟩ : syracuseStep 1734473 = 1300855) B1300855
theorem B685903 : Blo 682313 685903 := bstep (se 1 (by rfl) ⟨514427, by rfl⟩ : syracuseStep 685903 = 1028855) B1028855
theorem B685919 : Blo 682313 685919 := bstep (se 1 (by rfl) ⟨514439, by rfl⟩ : syracuseStep 685919 = 1028879) B1028879
theorem B685947 : Blo 682313 685947 := bstep (se 1 (by rfl) ⟨514460, by rfl⟩ : syracuseStep 685947 = 1028921) B1028921
theorem B685999 : Blo 682313 685999 := bstep (se 1 (by rfl) ⟨514499, by rfl⟩ : syracuseStep 685999 = 1028999) B1028999
theorem B686023 : Blo 682313 686023 := bstep (se 1 (by rfl) ⟨514517, by rfl⟩ : syracuseStep 686023 = 1029035) B1029035
theorem B6584273 : Blo 682313 6584273 := bstep (se 2 (by rfl) ⟨2469102, by rfl⟩ : syracuseStep 6584273 = 4938205) B4938205
theorem B686043 : Blo 682313 686043 := bstep (se 1 (by rfl) ⟨514532, by rfl⟩ : syracuseStep 686043 = 1029065) B1029065
theorem B686119 : Blo 682313 686119 := bstep (se 1 (by rfl) ⟨514589, by rfl⟩ : syracuseStep 686119 = 1029179) B1029179
theorem B686159 : Blo 682313 686159 := bstep (se 1 (by rfl) ⟨514619, by rfl⟩ : syracuseStep 686159 = 1029239) B1029239
theorem B686175 : Blo 682313 686175 := bstep (se 1 (by rfl) ⟨514631, by rfl⟩ : syracuseStep 686175 = 1029263) B1029263
theorem B686203 : Blo 682313 686203 := bstep (se 1 (by rfl) ⟨514652, by rfl⟩ : syracuseStep 686203 = 1029305) B1029305
theorem B686255 : Blo 682313 686255 := bstep (se 1 (by rfl) ⟨514691, by rfl⟩ : syracuseStep 686255 = 1029383) B1029383
theorem B686279 : Blo 682313 686279 := bstep (se 1 (by rfl) ⟨514709, by rfl⟩ : syracuseStep 686279 = 1029419) B1029419
theorem B686299 : Blo 682313 686299 := bstep (se 1 (by rfl) ⟨514724, by rfl⟩ : syracuseStep 686299 = 1029449) B1029449
theorem B1538657 : Blo 682313 1538657 := bstep (se 2 (by rfl) ⟨576996, by rfl⟩ : syracuseStep 1538657 = 1153993) B1153993
theorem B7797383 : Blo 682313 7797383 := bstep (se 1 (by rfl) ⟨5848037, by rfl⟩ : syracuseStep 7797383 = 11696075) B11696075
theorem B5634695 : Blo 682313 5634695 := bstep (se 1 (by rfl) ⟨4226021, by rfl⟩ : syracuseStep 5634695 = 8452043) B8452043
theorem B2194067 : Blo 682313 2194067 := bstep (se 1 (by rfl) ⟨1645550, by rfl⟩ : syracuseStep 2194067 = 3291101) B3291101
theorem B1538999 : Blo 682313 1538999 := bstep (se 1 (by rfl) ⟨1154249, by rfl⟩ : syracuseStep 1538999 = 2308499) B2308499
theorem B1735607 : Blo 682313 1735607 := bstep (se 1 (by rfl) ⟨1301705, by rfl⟩ : syracuseStep 1735607 = 2603411) B2603411
theorem B14777423 : Blo 682313 14777423 := bstep (se 1 (by rfl) ⟨11083067, by rfl⟩ : syracuseStep 14777423 = 22166135) B22166135
theorem B3472631 : Blo 682313 3472631 := bstep (se 1 (by rfl) ⟨2604473, by rfl⟩ : syracuseStep 3472631 = 5208947) B5208947
theorem B5209433 : Blo 682313 5209433 := bstep (se 2 (by rfl) ⟨1953537, by rfl⟩ : syracuseStep 5209433 = 3907075) B3907075
theorem B1539593 : Blo 682313 1539593 := bstep (se 2 (by rfl) ⟨577347, by rfl⟩ : syracuseStep 1539593 = 1154695) B1154695
theorem B11107979 : Blo 682313 11107979 := bstep (se 1 (by rfl) ⟨8330984, by rfl⟩ : syracuseStep 11107979 = 16661969) B16661969
theorem B3473117 : Blo 682313 3473117 := bstep (se 3 (by rfl) ⟨651209, by rfl⟩ : syracuseStep 3473117 = 1302419) B1302419
theorem B1539935 : Blo 682313 1539935 := bstep (se 1 (by rfl) ⟨1154951, by rfl⟩ : syracuseStep 1539935 = 2309903) B2309903
theorem B7405577 : Blo 682313 7405577 := bstep (se 2 (by rfl) ⟨2777091, by rfl⟩ : syracuseStep 7405577 = 5554183) B5554183
theorem B8749093 : Blo 682313 8749093 := bstep (se 4 (by rfl) ⟨820227, by rfl⟩ : syracuseStep 8749093 = 1640455) B1640455
theorem B7012403 : Blo 682313 7012403 := bstep (se 1 (by rfl) ⟨5259302, by rfl⟩ : syracuseStep 7012403 = 10518605) B10518605
theorem B3899603 : Blo 682313 3899603 := bstep (se 1 (by rfl) ⟨2924702, by rfl⟩ : syracuseStep 3899603 = 5849405) B5849405
theorem B1540943 : Blo 682313 1540943 := bstep (se 1 (by rfl) ⟨1155707, by rfl⟩ : syracuseStep 1540943 = 2311415) B2311415
theorem B5833619 : Blo 682313 5833619 := bstep (se 1 (by rfl) ⟨4375214, by rfl⟩ : syracuseStep 5833619 = 8750429) B8750429
theorem B1541159 : Blo 682313 1541159 := bstep (se 1 (by rfl) ⟨1155869, by rfl⟩ : syracuseStep 1541159 = 2311739) B2311739
theorem B1541339 : Blo 682313 1541339 := bstep (se 1 (by rfl) ⟨1156004, by rfl⟩ : syracuseStep 1541339 = 2312009) B2312009
theorem B3114233 : Blo 682313 3114233 := bstep (se 2 (by rfl) ⟨1167837, by rfl⟩ : syracuseStep 3114233 = 2335675) B2335675
theorem B1541537 : Blo 682313 1541537 := bstep (se 2 (by rfl) ⟨578076, by rfl⟩ : syracuseStep 1541537 = 1156153) B1156153
theorem B9864827 : Blo 682313 9864827 := bstep (se 1 (by rfl) ⟨7398620, by rfl⟩ : syracuseStep 9864827 = 14797241) B14797241
theorem B1542095 : Blo 682313 1542095 := bstep (se 1 (by rfl) ⟨1156571, by rfl⟩ : syracuseStep 1542095 = 2313143) B2313143
theorem B2590973 : Blo 682313 2590973 := bstep (se 3 (by rfl) ⟨485807, by rfl⟩ : syracuseStep 2590973 = 971615) B971615
theorem B1542473 : Blo 682313 1542473 := bstep (se 2 (by rfl) ⟨578427, by rfl⟩ : syracuseStep 1542473 = 1156855) B1156855
theorem B1542491 : Blo 682313 1542491 := bstep (se 1 (by rfl) ⟨1156868, by rfl⟩ : syracuseStep 1542491 = 2313737) B2313737
theorem B2919235 : Blo 682313 2919235 := bstep (se 1 (by rfl) ⟨2189426, by rfl⟩ : syracuseStep 2919235 = 4378853) B4378853
theorem B1543067 : Blo 682313 1543067 := bstep (se 1 (by rfl) ⟨1157300, by rfl⟩ : syracuseStep 1543067 = 2314601) B2314601
theorem B1543265 : Blo 682313 1543265 := bstep (se 2 (by rfl) ⟨578724, by rfl⟩ : syracuseStep 1543265 = 1157449) B1157449
theorem B1543463 : Blo 682313 1543463 := bstep (se 1 (by rfl) ⟨1157597, by rfl⟩ : syracuseStep 1543463 = 2315195) B2315195
theorem B822727 : Blo 682313 822727 := bstep (se 1 (by rfl) ⟨617045, by rfl⟩ : syracuseStep 822727 = 1234091) B1234091
theorem B18681353 : Blo 682313 18681353 := bstep (se 2 (by rfl) ⟨7005507, by rfl⟩ : syracuseStep 18681353 = 14011015) B14011015
theorem B1543841 : Blo 682313 1543841 := bstep (se 2 (by rfl) ⟨578940, by rfl⟩ : syracuseStep 1543841 = 1157881) B1157881
theorem B1642369 : Blo 682313 1642369 := bstep (se 2 (by rfl) ⟨615888, by rfl⟩ : syracuseStep 1642369 = 1231777) B1231777
theorem B1544201 : Blo 682313 1544201 := bstep (se 2 (by rfl) ⟨579075, by rfl⟩ : syracuseStep 1544201 = 1158151) B1158151
theorem B3903659 : Blo 682313 3903659 := bstep (se 1 (by rfl) ⟨2927744, by rfl⟩ : syracuseStep 3903659 = 5855489) B5855489
theorem B1642859 : Blo 682313 1642859 := bstep (se 1 (by rfl) ⟨1232144, by rfl⟩ : syracuseStep 1642859 = 2464289) B2464289
theorem B7410035 : Blo 682313 7410035 := bstep (se 1 (by rfl) ⟨5557526, by rfl⟩ : syracuseStep 7410035 = 11115053) B11115053
theorem B11113037 : Blo 682313 11113037 := bstep (se 3 (by rfl) ⟨2083694, by rfl⟩ : syracuseStep 11113037 = 4167389) B4167389
theorem B1151671 : Blo 682313 1151671 := bstep (se 1 (by rfl) ⟨863753, by rfl⟩ : syracuseStep 1151671 = 1727507) B1727507
theorem B4756333 : Blo 682313 4756333 := bstep (se 3 (by rfl) ⟨891812, by rfl⟩ : syracuseStep 4756333 = 1783625) B1783625
theorem B1151975 : Blo 682313 1151975 := bstep (se 1 (by rfl) ⟨863981, by rfl⟩ : syracuseStep 1151975 = 1727963) B1727963
theorem B7017529 : Blo 682313 7017529 := bstep (se 2 (by rfl) ⟨2631573, by rfl⟩ : syracuseStep 7017529 = 5263147) B5263147
theorem B2593889 : Blo 682313 2593889 := bstep (se 2 (by rfl) ⟨972708, by rfl⟩ : syracuseStep 2593889 = 1945417) B1945417
theorem B3282065 : Blo 682313 3282065 := bstep (se 2 (by rfl) ⟨1230774, by rfl⟩ : syracuseStep 3282065 = 2461549) B2461549
theorem B59839661 : Blo 682313 59839661 := bstep (se 3 (by rfl) ⟨11219936, by rfl⟩ : syracuseStep 59839661 = 22439873) B22439873
theorem B922843 : Blo 682313 922843 := bstep (se 1 (by rfl) ⟨692132, by rfl⟩ : syracuseStep 922843 = 1384265) B1384265
theorem B1643753 : Blo 682313 1643753 := bstep (se 2 (by rfl) ⟨616407, by rfl⟩ : syracuseStep 1643753 = 1232815) B1232815
theorem B8754425 : Blo 682313 8754425 := bstep (se 2 (by rfl) ⟨3282909, by rfl⟩ : syracuseStep 8754425 = 6565819) B6565819
theorem B53450189 : Blo 682313 53450189 := bstep (se 3 (by rfl) ⟨10021910, by rfl⟩ : syracuseStep 53450189 = 20043821) B20043821
theorem B923243 : Blo 682313 923243 := bstep (se 1 (by rfl) ⟨692432, by rfl⟩ : syracuseStep 923243 = 1384865) B1384865
theorem B2954909 : Blo 682313 2954909 := bstep (se 3 (by rfl) ⟨554045, by rfl⟩ : syracuseStep 2954909 = 1108091) B1108091
theorem B1153129 : Blo 682313 1153129 := bstep (se 2 (by rfl) ⟨432423, by rfl⟩ : syracuseStep 1153129 = 864847) B864847
theorem B13180229 : Blo 682313 13180229 := bstep (se 4 (by rfl) ⟨1235646, by rfl⟩ : syracuseStep 13180229 = 2471293) B2471293
theorem B5611031 : Blo 682313 5611031 := bstep (se 1 (by rfl) ⟨4208273, by rfl⟩ : syracuseStep 5611031 = 8416547) B8416547
theorem B12459545 : Blo 682313 12459545 := bstep (se 2 (by rfl) ⟨4672329, by rfl⟩ : syracuseStep 12459545 = 9344659) B9344659
theorem B2563745 : Blo 682313 2563745 := bstep (se 2 (by rfl) ⟨961404, by rfl⟩ : syracuseStep 2563745 = 1922809) B1922809
theorem B1023785 : Blo 682313 1023785 := bstep (se 2 (by rfl) ⟨383919, by rfl⟩ : syracuseStep 1023785 = 767839) B767839
theorem B1154857 : Blo 682313 1154857 := bstep (se 2 (by rfl) ⟨433071, by rfl⟩ : syracuseStep 1154857 = 866143) B866143
theorem B1023791 : Blo 682313 1023791 := bstep (se 1 (by rfl) ⟨767843, by rfl⟩ : syracuseStep 1023791 = 1535687) B1535687
theorem B2662301 : Blo 682313 2662301 := bstep (se 3 (by rfl) ⟨499181, by rfl⟩ : syracuseStep 2662301 = 998363) B998363
theorem B4923443 : Blo 682313 4923443 := bstep (se 1 (by rfl) ⟨3692582, by rfl⟩ : syracuseStep 4923443 = 7385165) B7385165
theorem B1024265 : Blo 682313 1024265 := bstep (se 2 (by rfl) ⟨384099, by rfl⟩ : syracuseStep 1024265 = 768199) B768199
theorem B1024367 : Blo 682313 1024367 := bstep (se 1 (by rfl) ⟨768275, by rfl⟩ : syracuseStep 1024367 = 1536551) B1536551
theorem B7512587 : Blo 682313 7512587 := bstep (se 1 (by rfl) ⟨5634440, by rfl⟩ : syracuseStep 7512587 = 11268881) B11268881
theorem B1155647 : Blo 682313 1155647 := bstep (se 1 (by rfl) ⟨866735, by rfl⟩ : syracuseStep 1155647 = 1733471) B1733471
theorem B1024583 : Blo 682313 1024583 := bstep (se 1 (by rfl) ⟨768437, by rfl⟩ : syracuseStep 1024583 = 1536875) B1536875
theorem B1024619 : Blo 682313 1024619 := bstep (se 1 (by rfl) ⟨768464, by rfl⟩ : syracuseStep 1024619 = 1536929) B1536929
theorem B12460715 : Blo 682313 12460715 := bstep (se 1 (by rfl) ⟨9345536, by rfl⟩ : syracuseStep 12460715 = 18691073) B18691073
theorem B1024847 : Blo 682313 1024847 := bstep (se 1 (by rfl) ⟨768635, by rfl⟩ : syracuseStep 1024847 = 1537271) B1537271
theorem B3122333 : Blo 682313 3122333 := bstep (se 3 (by rfl) ⟨585437, by rfl⟩ : syracuseStep 3122333 = 1170875) B1170875
theorem B23635115 : Blo 682313 23635115 := bstep (se 1 (by rfl) ⟨17726336, by rfl⟩ : syracuseStep 23635115 = 35452673) B35452673
theorem B1025243 : Blo 682313 1025243 := bstep (se 1 (by rfl) ⟨768932, by rfl⟩ : syracuseStep 1025243 = 1537865) B1537865
theorem B1156315 : Blo 682313 1156315 := bstep (se 1 (by rfl) ⟨867236, by rfl⟩ : syracuseStep 1156315 = 1734473) B1734473
theorem B1025417 : Blo 682313 1025417 := bstep (se 2 (by rfl) ⟨384531, by rfl⟩ : syracuseStep 1025417 = 769063) B769063
theorem B1025771 : Blo 682313 1025771 := bstep (se 1 (by rfl) ⟨769328, by rfl⟩ : syracuseStep 1025771 = 1538657) B1538657
theorem B4925261 : Blo 682313 4925261 := bstep (se 3 (by rfl) ⟨923486, by rfl⟩ : syracuseStep 4925261 = 1846973) B1846973
theorem B731035 : Blo 682313 731035 := bstep (se 1 (by rfl) ⟨548276, by rfl⟩ : syracuseStep 731035 = 1096553) B1096553
theorem B1025999 : Blo 682313 1025999 := bstep (se 1 (by rfl) ⟨769499, by rfl⟩ : syracuseStep 1025999 = 1538999) B1538999
theorem B1157071 : Blo 682313 1157071 := bstep (se 1 (by rfl) ⟨867803, by rfl⟩ : syracuseStep 1157071 = 1735607) B1735607
theorem B37562545 : Blo 682313 37562545 := bstep (se 2 (by rfl) ⟨14085954, by rfl⟩ : syracuseStep 37562545 = 28171909) B28171909
theorem B1943833 : Blo 682313 1943833 := bstep (se 2 (by rfl) ⟨728937, by rfl⟩ : syracuseStep 1943833 = 1457875) B1457875
theorem B1026395 : Blo 682313 1026395 := bstep (se 1 (by rfl) ⟨769796, by rfl⟩ : syracuseStep 1026395 = 1539593) B1539593
theorem B9513389 : Blo 682313 9513389 := bstep (se 3 (by rfl) ⟨1783760, by rfl⟩ : syracuseStep 9513389 = 3567521) B3567521
theorem B1780193 : Blo 682313 1780193 := bstep (se 2 (by rfl) ⟨667572, by rfl⟩ : syracuseStep 1780193 = 1335145) B1335145
theorem B1026623 : Blo 682313 1026623 := bstep (se 1 (by rfl) ⟨769967, by rfl⟩ : syracuseStep 1026623 = 1539935) B1539935
theorem B1157753 : Blo 682313 1157753 := bstep (se 2 (by rfl) ⟨434157, by rfl⟩ : syracuseStep 1157753 = 868315) B868315
theorem B1157807 : Blo 682313 1157807 := bstep (se 1 (by rfl) ⟨868355, by rfl⟩ : syracuseStep 1157807 = 1736711) B1736711
theorem B14068403 : Blo 682313 14068403 := bstep (se 1 (by rfl) ⟨10551302, by rfl⟩ : syracuseStep 14068403 = 21102605) B21102605
theorem B1026743 : Blo 682313 1026743 := bstep (se 1 (by rfl) ⟨770057, by rfl⟩ : syracuseStep 1026743 = 1540115) B1540115
theorem B11709197 : Blo 682313 11709197 := bstep (se 3 (by rfl) ⟨2195474, by rfl⟩ : syracuseStep 11709197 = 4390949) B4390949
theorem B1026971 : Blo 682313 1026971 := bstep (se 1 (by rfl) ⟨770228, by rfl⟩ : syracuseStep 1026971 = 1540457) B1540457
theorem B1158043 : Blo 682313 1158043 := bstep (se 1 (by rfl) ⟨868532, by rfl⟩ : syracuseStep 1158043 = 1737065) B1737065
theorem B1977331 : Blo 682313 1977331 := bstep (se 1 (by rfl) ⟨1482998, by rfl⟩ : syracuseStep 1977331 = 2965997) B2965997
theorem B1027367 : Blo 682313 1027367 := bstep (se 1 (by rfl) ⟨770525, by rfl⟩ : syracuseStep 1027367 = 1541051) B1541051
theorem B16035191 : Blo 682313 16035191 := bstep (se 1 (by rfl) ⟨12026393, by rfl⟩ : syracuseStep 16035191 = 24052787) B24052787
theorem B1027451 : Blo 682313 1027451 := bstep (se 1 (by rfl) ⟨770588, by rfl⟩ : syracuseStep 1027451 = 1541177) B1541177
theorem B2305529 : Blo 682313 2305529 := bstep (se 2 (by rfl) ⟨864573, by rfl⟩ : syracuseStep 2305529 = 1729147) B1729147
theorem B1027577 : Blo 682313 1027577 := bstep (se 2 (by rfl) ⟨385341, by rfl⟩ : syracuseStep 1027577 = 770683) B770683
theorem B1027679 : Blo 682313 1027679 := bstep (se 1 (by rfl) ⟨770759, by rfl⟩ : syracuseStep 1027679 = 1541519) B1541519
theorem B13184693 : Blo 682313 13184693 := bstep (se 5 (by rfl) ⟨618032, by rfl⟩ : syracuseStep 13184693 = 1236065) B1236065
theorem B2305799 : Blo 682313 2305799 := bstep (se 1 (by rfl) ⟨1729349, by rfl⟩ : syracuseStep 2305799 = 3458699) B3458699
theorem B864047 : Blo 682313 864047 := bstep (se 1 (by rfl) ⟨648035, by rfl⟩ : syracuseStep 864047 = 1296071) B1296071
theorem B1027895 : Blo 682313 1027895 := bstep (se 1 (by rfl) ⟨770921, by rfl⟩ : syracuseStep 1027895 = 1541843) B1541843
theorem B2305853 : Blo 682313 2305853 := bstep (se 3 (by rfl) ⟨432347, by rfl⟩ : syracuseStep 2305853 = 864695) B864695
theorem B13512653 : Blo 682313 13512653 := bstep (se 3 (by rfl) ⟨2533622, by rfl⟩ : syracuseStep 13512653 = 5067245) B5067245
theorem B1028201 : Blo 682313 1028201 := bstep (se 2 (by rfl) ⟨385575, by rfl⟩ : syracuseStep 1028201 = 771151) B771151
theorem B1847719 : Blo 682313 1847719 := bstep (se 1 (by rfl) ⟨1385789, by rfl⟩ : syracuseStep 1847719 = 2771579) B2771579
theorem B1028519 : Blo 682313 1028519 := bstep (se 1 (by rfl) ⟨771389, by rfl⟩ : syracuseStep 1028519 = 1542779) B1542779
theorem B1028603 : Blo 682313 1028603 := bstep (se 1 (by rfl) ⟨771452, by rfl⟩ : syracuseStep 1028603 = 1542905) B1542905
theorem B1028729 : Blo 682313 1028729 := bstep (se 2 (by rfl) ⟨385773, by rfl⟩ : syracuseStep 1028729 = 771547) B771547
theorem B1028783 : Blo 682313 1028783 := bstep (se 1 (by rfl) ⟨771587, by rfl⟩ : syracuseStep 1028783 = 1543175) B1543175
theorem B1028831 : Blo 682313 1028831 := bstep (se 1 (by rfl) ⟨771623, by rfl⟩ : syracuseStep 1028831 = 1543247) B1543247
theorem B5190479 : Blo 682313 5190479 := bstep (se 1 (by rfl) ⟨3892859, by rfl⟩ : syracuseStep 5190479 = 7785719) B7785719
theorem B1029095 : Blo 682313 1029095 := bstep (se 1 (by rfl) ⟨771821, by rfl⟩ : syracuseStep 1029095 = 1543643) B1543643
theorem B1946749 : Blo 682313 1946749 := bstep (se 3 (by rfl) ⟨365015, by rfl⟩ : syracuseStep 1946749 = 730031) B730031
theorem B1029353 : Blo 682313 1029353 := bstep (se 2 (by rfl) ⟨386007, by rfl⟩ : syracuseStep 1029353 = 772015) B772015
theorem B1029407 : Blo 682313 1029407 := bstep (se 1 (by rfl) ⟨772055, by rfl⟩ : syracuseStep 1029407 = 1544111) B1544111
theorem B1848737 : Blo 682313 1848737 := bstep (se 2 (by rfl) ⟨693276, by rfl⟩ : syracuseStep 1848737 = 1386553) B1386553
theorem B3454649 : Blo 682313 3454649 := bstep (se 2 (by rfl) ⟨1295493, by rfl⟩ : syracuseStep 3454649 = 2590987) B2590987
theorem B2603137 : Blo 682313 2603137 := bstep (se 2 (by rfl) ⟨976176, by rfl⟩ : syracuseStep 2603137 = 1952353) B1952353
theorem B768379 : Blo 682313 768379 := bstep (se 1 (by rfl) ⟨576284, by rfl⟩ : syracuseStep 768379 = 1152569) B1152569
theorem B2308715 : Blo 682313 2308715 := bstep (se 1 (by rfl) ⟨1731536, by rfl⟩ : syracuseStep 2308715 = 3463073) B3463073
theorem B1751735 : Blo 682313 1751735 := bstep (se 1 (by rfl) ⟨1313801, by rfl⟩ : syracuseStep 1751735 = 2627603) B2627603
theorem B768847 : Blo 682313 768847 := bstep (se 1 (by rfl) ⟨576635, by rfl⟩ : syracuseStep 768847 = 1153271) B1153271
theorem B7388279 : Blo 682313 7388279 := bstep (se 1 (by rfl) ⟨5541209, by rfl⟩ : syracuseStep 7388279 = 11082419) B11082419
theorem B2309309 : Blo 682313 2309309 := bstep (se 3 (by rfl) ⟨432995, by rfl⟩ : syracuseStep 2309309 = 865991) B865991
theorem B769243 : Blo 682313 769243 := bstep (se 1 (by rfl) ⟨576932, by rfl⟩ : syracuseStep 769243 = 1153865) B1153865
theorem B3292427 : Blo 682313 3292427 := bstep (se 1 (by rfl) ⟨2469320, by rfl⟩ : syracuseStep 3292427 = 4938641) B4938641
theorem B3292483 : Blo 682313 3292483 := bstep (se 1 (by rfl) ⟨2469362, by rfl⟩ : syracuseStep 3292483 = 4938725) B4938725
theorem B1850813 : Blo 682313 1850813 := bstep (se 3 (by rfl) ⟨347027, by rfl⟩ : syracuseStep 1850813 = 694055) B694055
theorem B769531 : Blo 682313 769531 := bstep (se 1 (by rfl) ⟨577148, by rfl⟩ : syracuseStep 769531 = 1154297) B1154297
theorem B2473487 : Blo 682313 2473487 := bstep (se 1 (by rfl) ⟨1855115, by rfl⟩ : syracuseStep 2473487 = 3710231) B3710231
theorem B3161659 : Blo 682313 3161659 := bstep (se 1 (by rfl) ⟨2371244, by rfl⟩ : syracuseStep 3161659 = 4742489) B4742489
theorem B3456593 : Blo 682313 3456593 := bstep (se 2 (by rfl) ⟨1296222, by rfl⟩ : syracuseStep 3456593 = 2592445) B2592445
theorem B867935 : Blo 682313 867935 := bstep (se 1 (by rfl) ⟨650951, by rfl⟩ : syracuseStep 867935 = 1301903) B1301903
theorem B2342515 : Blo 682313 2342515 := bstep (se 1 (by rfl) ⟨1756886, by rfl⟩ : syracuseStep 2342515 = 3513773) B3513773
theorem B769711 : Blo 682313 769711 := bstep (se 1 (by rfl) ⟨577283, by rfl⟩ : syracuseStep 769711 = 1154567) B1154567
theorem B4931401 : Blo 682313 4931401 := bstep (se 2 (by rfl) ⟨1849275, by rfl⟩ : syracuseStep 4931401 = 3698551) B3698551
theorem B769999 : Blo 682313 769999 := bstep (se 1 (by rfl) ⟨577499, by rfl⟩ : syracuseStep 769999 = 1154999) B1154999
theorem B2605081 : Blo 682313 2605081 := bstep (se 2 (by rfl) ⟨976905, by rfl⟩ : syracuseStep 2605081 = 1953811) B1953811
theorem B42647651 : Blo 682313 42647651 := bstep (se 1 (by rfl) ⟨31985738, by rfl⟩ : syracuseStep 42647651 = 63971477) B63971477
theorem B5193881 : Blo 682313 5193881 := bstep (se 2 (by rfl) ⟨1947705, by rfl⟩ : syracuseStep 5193881 = 3895411) B3895411
theorem B2605385 : Blo 682313 2605385 := bstep (se 2 (by rfl) ⟨977019, by rfl⟩ : syracuseStep 2605385 = 1954039) B1954039
theorem B770395 : Blo 682313 770395 := bstep (se 1 (by rfl) ⟨577796, by rfl⟩ : syracuseStep 770395 = 1155593) B1155593
theorem B770503 : Blo 682313 770503 := bstep (se 1 (by rfl) ⟨577877, by rfl⟩ : syracuseStep 770503 = 1155755) B1155755
theorem B22495927 : Blo 682313 22495927 := bstep (se 1 (by rfl) ⟨16871945, by rfl⟩ : syracuseStep 22495927 = 33743891) B33743891
theorem B3556055 : Blo 682313 3556055 := bstep (se 1 (by rfl) ⟨2667041, by rfl⟩ : syracuseStep 3556055 = 5334083) B5334083
theorem B6243065 : Blo 682313 6243065 := bstep (se 2 (by rfl) ⟨2341149, by rfl⟩ : syracuseStep 6243065 = 4682299) B4682299
theorem B770863 : Blo 682313 770863 := bstep (se 1 (by rfl) ⟨578147, by rfl⟩ : syracuseStep 770863 = 1156295) B1156295
theorem B1426331 : Blo 682313 1426331 := bstep (se 1 (by rfl) ⟨1069748, by rfl⟩ : syracuseStep 1426331 = 2139497) B2139497
theorem B770971 : Blo 682313 770971 := bstep (se 1 (by rfl) ⟨578228, by rfl⟩ : syracuseStep 770971 = 1156457) B1156457
theorem B3294215 : Blo 682313 3294215 := bstep (se 1 (by rfl) ⟨2470661, by rfl⟩ : syracuseStep 3294215 = 4941323) B4941323
theorem B1688809 : Blo 682313 1688809 := bstep (se 2 (by rfl) ⟨633303, by rfl⟩ : syracuseStep 1688809 = 1266607) B1266607
theorem B2082041 : Blo 682313 2082041 := bstep (se 2 (by rfl) ⟨780765, by rfl⟩ : syracuseStep 2082041 = 1561531) B1561531
theorem B771367 : Blo 682313 771367 := bstep (se 1 (by rfl) ⟨578525, by rfl⟩ : syracuseStep 771367 = 1157051) B1157051
theorem B2639147 : Blo 682313 2639147 := bstep (se 1 (by rfl) ⟨1979360, by rfl⟩ : syracuseStep 2639147 = 3958721) B3958721
theorem B771439 : Blo 682313 771439 := bstep (se 1 (by rfl) ⟨578579, by rfl⟩ : syracuseStep 771439 = 1157159) B1157159
theorem B771655 : Blo 682313 771655 := bstep (se 1 (by rfl) ⟨578741, by rfl⟩ : syracuseStep 771655 = 1157483) B1157483
theorem B8800067 : Blo 682313 8800067 := bstep (se 1 (by rfl) ⟨6600050, by rfl⟩ : syracuseStep 8800067 = 13200101) B13200101
theorem B3459023 : Blo 682313 3459023 := bstep (se 1 (by rfl) ⟨2594267, by rfl⟩ : syracuseStep 3459023 = 5188535) B5188535
theorem B2312225 : Blo 682313 2312225 := bstep (se 2 (by rfl) ⟨867084, by rfl⟩ : syracuseStep 2312225 = 1734169) B1734169
theorem B3950777 : Blo 682313 3950777 := bstep (se 2 (by rfl) ⟨1481541, by rfl⟩ : syracuseStep 3950777 = 2963083) B2963083
theorem B1296967 : Blo 682313 1296967 := bstep (se 1 (by rfl) ⟨972725, by rfl⟩ : syracuseStep 1296967 = 1945451) B1945451
theorem B1461071 : Blo 682313 1461071 := bstep (se 1 (by rfl) ⟨1095803, by rfl⟩ : syracuseStep 1461071 = 2191607) B2191607
theorem B3459995 : Blo 682313 3459995 := bstep (se 1 (by rfl) ⟨2594996, by rfl⟩ : syracuseStep 3459995 = 5189993) B5189993
theorem B3689387 : Blo 682313 3689387 := bstep (se 1 (by rfl) ⟨2767040, by rfl⟩ : syracuseStep 3689387 = 5534081) B5534081
theorem B13028525 : Blo 682313 13028525 := bstep (se 3 (by rfl) ⟨2442848, by rfl⟩ : syracuseStep 13028525 = 4885697) B4885697
theorem B47369395 : Blo 682313 47369395 := bstep (se 1 (by rfl) ⟨35527046, by rfl⟩ : syracuseStep 47369395 = 71054093) B71054093
theorem B1854683 : Blo 682313 1854683 := bstep (se 1 (by rfl) ⟨1391012, by rfl⟩ : syracuseStep 1854683 = 2782025) B2782025
theorem B3460481 : Blo 682313 3460481 := bstep (se 2 (by rfl) ⟨1297680, by rfl⟩ : syracuseStep 3460481 = 2595361) B2595361
theorem B1756631 : Blo 682313 1756631 := bstep (se 1 (by rfl) ⟨1317473, by rfl⟩ : syracuseStep 1756631 = 2634947) B2634947
theorem B1298015 : Blo 682313 1298015 := bstep (se 1 (by rfl) ⟨973511, by rfl⟩ : syracuseStep 1298015 = 1947023) B1947023
theorem B3461129 : Blo 682313 3461129 := bstep (se 2 (by rfl) ⟨1297923, by rfl⟩ : syracuseStep 3461129 = 2595847) B2595847
theorem B3461291 : Blo 682313 3461291 := bstep (se 1 (by rfl) ⟨2595968, by rfl⟩ : syracuseStep 3461291 = 5191937) B5191937
theorem B1233161 : Blo 682313 1233161 := bstep (se 2 (by rfl) ⟨462435, by rfl⟩ : syracuseStep 1233161 = 924871) B924871
theorem B5198255 : Blo 682313 5198255 := bstep (se 1 (by rfl) ⟨3898691, by rfl⟩ : syracuseStep 5198255 = 7797383) B7797383
theorem B3756463 : Blo 682313 3756463 := bstep (se 1 (by rfl) ⟨2817347, by rfl⟩ : syracuseStep 3756463 = 5634695) B5634695
theorem B1462711 : Blo 682313 1462711 := bstep (se 1 (by rfl) ⟨1097033, by rfl⟩ : syracuseStep 1462711 = 2194067) B2194067
theorem B2806343 : Blo 682313 2806343 := bstep (se 1 (by rfl) ⟨2104757, by rfl⟩ : syracuseStep 2806343 = 4209515) B4209515
theorem B1299017 : Blo 682313 1299017 := bstep (se 2 (by rfl) ⟨487131, by rfl⟩ : syracuseStep 1299017 = 974263) B974263
theorem B3461777 : Blo 682313 3461777 := bstep (se 2 (by rfl) ⟨1298166, by rfl⟩ : syracuseStep 3461777 = 2596333) B2596333
theorem B9851615 : Blo 682313 9851615 := bstep (se 1 (by rfl) ⟨7388711, by rfl⟩ : syracuseStep 9851615 = 14777423) B14777423
theorem B2315087 : Blo 682313 2315087 := bstep (se 1 (by rfl) ⟨1736315, by rfl⟩ : syracuseStep 2315087 = 3472631) B3472631
theorem B2315411 : Blo 682313 2315411 := bstep (se 1 (by rfl) ⟨1736558, by rfl⟩ : syracuseStep 2315411 = 3473117) B3473117
theorem B2971019 : Blo 682313 2971019 := bstep (se 1 (by rfl) ⟨2228264, by rfl⟩ : syracuseStep 2971019 = 4456529) B4456529
theorem B2315681 : Blo 682313 2315681 := bstep (se 2 (by rfl) ⟨868380, by rfl⟩ : syracuseStep 2315681 = 1736761) B1736761
theorem B972281 : Blo 682313 972281 := bstep (se 2 (by rfl) ⟨364605, by rfl⟩ : syracuseStep 972281 = 729211) B729211
theorem B3888647 : Blo 682313 3888647 := bstep (se 1 (by rfl) ⟨2916485, by rfl⟩ : syracuseStep 3888647 = 5832971) B5832971
theorem B973147 : Blo 682313 973147 := bstep (se 1 (by rfl) ⟨729860, by rfl⟩ : syracuseStep 973147 = 1459721) B1459721
theorem B1300961 : Blo 682313 1300961 := bstep (se 2 (by rfl) ⟨487860, by rfl⟩ : syracuseStep 1300961 = 975721) B975721
theorem B11262503 : Blo 682313 11262503 := bstep (se 1 (by rfl) ⟨8446877, by rfl⟩ : syracuseStep 11262503 = 16893755) B16893755
theorem B1301113 : Blo 682313 1301113 := bstep (se 2 (by rfl) ⟨487917, by rfl⟩ : syracuseStep 1301113 = 975835) B975835
theorem B3464207 : Blo 682313 3464207 := bstep (se 1 (by rfl) ⟨2598155, by rfl⟩ : syracuseStep 3464207 = 5196311) B5196311
theorem B1727527 : Blo 682313 1727527 := bstep (se 1 (by rfl) ⟨1295645, by rfl⟩ : syracuseStep 1727527 = 2591291) B2591291
theorem B1727993 : Blo 682313 1727993 := bstep (se 2 (by rfl) ⟨647997, by rfl⟩ : syracuseStep 1727993 = 1295995) B1295995
theorem B1302313 : Blo 682313 1302313 := bstep (se 2 (by rfl) ⟨488367, by rfl⟩ : syracuseStep 1302313 = 976735) B976735
theorem B974639 : Blo 682313 974639 := bstep (se 1 (by rfl) ⟨730979, by rfl⟩ : syracuseStep 974639 = 1461959) B1461959
theorem B3465017 : Blo 682313 3465017 := bstep (se 2 (by rfl) ⟨1299381, by rfl⟩ : syracuseStep 3465017 = 2598763) B2598763
theorem B4939649 : Blo 682313 4939649 := bstep (se 2 (by rfl) ⟨1852368, by rfl⟩ : syracuseStep 4939649 = 3704737) B3704737
theorem B1728641 : Blo 682313 1728641 := bstep (se 2 (by rfl) ⟨648240, by rfl⟩ : syracuseStep 1728641 = 1296481) B1296481
theorem B1302875 : Blo 682313 1302875 := bstep (se 1 (by rfl) ⟨977156, by rfl⟩ : syracuseStep 1302875 = 1954313) B1954313
theorem B1728935 : Blo 682313 1728935 := bstep (se 1 (by rfl) ⟨1296701, by rfl⟩ : syracuseStep 1728935 = 2593403) B2593403
theorem B1729097 : Blo 682313 1729097 := bstep (se 2 (by rfl) ⟨648411, by rfl⟩ : syracuseStep 1729097 = 1296823) B1296823
theorem B6578891 : Blo 682313 6578891 := bstep (se 1 (by rfl) ⟨4934168, by rfl⟩ : syracuseStep 6578891 = 9868337) B9868337
theorem B1729451 : Blo 682313 1729451 := bstep (se 1 (by rfl) ⟨1297088, by rfl⟩ : syracuseStep 1729451 = 2594177) B2594177
theorem B1729633 : Blo 682313 1729633 := bstep (se 2 (by rfl) ⟨648612, by rfl⟩ : syracuseStep 1729633 = 1297225) B1297225
theorem B3892769 : Blo 682313 3892769 := bstep (se 2 (by rfl) ⟨1459788, by rfl⟩ : syracuseStep 3892769 = 2919577) B2919577
theorem B30336599 : Blo 682313 30336599 := bstep (se 1 (by rfl) ⟨22752449, by rfl⟩ : syracuseStep 30336599 = 45504899) B45504899
theorem B1730585 : Blo 682313 1730585 := bstep (se 2 (by rfl) ⟨648969, by rfl⟩ : syracuseStep 1730585 = 1297939) B1297939
theorem B14772401 : Blo 682313 14772401 := bstep (se 2 (by rfl) ⟨5539650, by rfl⟩ : syracuseStep 14772401 = 11079301) B11079301
theorem B682331 : Blo 682313 682331 := bstep (se 1 (by rfl) ⟨511748, by rfl⟩ : syracuseStep 682331 = 1023497) B1023497
theorem B682351 : Blo 682313 682351 := bstep (se 1 (by rfl) ⟨511763, by rfl⟩ : syracuseStep 682351 = 1023527) B1023527
theorem B682407 : Blo 682313 682407 := bstep (se 1 (by rfl) ⟨511805, by rfl⟩ : syracuseStep 682407 = 1023611) B1023611
theorem B2779559 : Blo 682313 2779559 := bstep (se 1 (by rfl) ⟨2084669, by rfl⟩ : syracuseStep 2779559 = 4169339) B4169339
theorem B1731041 : Blo 682313 1731041 := bstep (se 2 (by rfl) ⟨649140, by rfl⟩ : syracuseStep 1731041 = 1298281) B1298281
theorem B682491 : Blo 682313 682491 := bstep (se 1 (by rfl) ⟨511868, by rfl⟩ : syracuseStep 682491 = 1023737) B1023737
theorem B3467771 : Blo 682313 3467771 := bstep (se 1 (by rfl) ⟨2600828, by rfl⟩ : syracuseStep 3467771 = 5201657) B5201657
theorem B1731091 : Blo 682313 1731091 := bstep (se 1 (by rfl) ⟨1298318, by rfl⟩ : syracuseStep 1731091 = 2596637) B2596637
theorem B682559 : Blo 682313 682559 := bstep (se 1 (by rfl) ⟨511919, by rfl⟩ : syracuseStep 682559 = 1023839) B1023839
theorem B682567 : Blo 682313 682567 := bstep (se 1 (by rfl) ⟨511925, by rfl⟩ : syracuseStep 682567 = 1023851) B1023851
theorem B682719 : Blo 682313 682719 := bstep (se 1 (by rfl) ⟨512039, by rfl⟩ : syracuseStep 682719 = 1024079) B1024079
theorem B568519397 : Blo 682313 568519397 := bstep (se 4 (by rfl) ⟨53298693, by rfl⟩ : syracuseStep 568519397 = 106597387) B106597387
theorem B3697427 : Blo 682313 3697427 := bstep (se 1 (by rfl) ⟨2773070, by rfl⟩ : syracuseStep 3697427 = 5546141) B5546141
theorem B682799 : Blo 682313 682799 := bstep (se 1 (by rfl) ⟨512099, by rfl⟩ : syracuseStep 682799 = 1024199) B1024199
theorem B682907 : Blo 682313 682907 := bstep (se 1 (by rfl) ⟨512180, by rfl⟩ : syracuseStep 682907 = 1024361) B1024361
theorem B2190235 : Blo 682313 2190235 := bstep (se 1 (by rfl) ⟨1642676, by rfl⟩ : syracuseStep 2190235 = 3285353) B3285353
theorem B284322757 : Blo 682313 284322757 := bstep (se 4 (by rfl) ⟨26655258, by rfl⟩ : syracuseStep 284322757 = 53310517) B53310517
theorem B682959 : Blo 682313 682959 := bstep (se 1 (by rfl) ⟨512219, by rfl⟩ : syracuseStep 682959 = 1024439) B1024439
theorem B682983 : Blo 682313 682983 := bstep (se 1 (by rfl) ⟨512237, by rfl⟩ : syracuseStep 682983 = 1024475) B1024475
theorem B683295 : Blo 682313 683295 := bstep (se 1 (by rfl) ⟨512471, by rfl⟩ : syracuseStep 683295 = 1024943) B1024943
theorem B683355 : Blo 682313 683355 := bstep (se 1 (by rfl) ⟨512516, by rfl⟩ : syracuseStep 683355 = 1025033) B1025033
theorem B1535327 : Blo 682313 1535327 := bstep (se 1 (by rfl) ⟨1151495, by rfl⟩ : syracuseStep 1535327 = 2302991) B2302991
theorem B683375 : Blo 682313 683375 := bstep (se 1 (by rfl) ⟨512531, by rfl⟩ : syracuseStep 683375 = 1025063) B1025063
theorem B683431 : Blo 682313 683431 := bstep (se 1 (by rfl) ⟨512573, by rfl⟩ : syracuseStep 683431 = 1025147) B1025147
theorem B3468743 : Blo 682313 3468743 := bstep (se 1 (by rfl) ⟨2601557, by rfl⟩ : syracuseStep 3468743 = 5203115) B5203115
theorem B683515 : Blo 682313 683515 := bstep (se 1 (by rfl) ⟨512636, by rfl⟩ : syracuseStep 683515 = 1025273) B1025273
theorem B683583 : Blo 682313 683583 := bstep (se 1 (by rfl) ⟨512687, by rfl⟩ : syracuseStep 683583 = 1025375) B1025375
theorem B683591 : Blo 682313 683591 := bstep (se 1 (by rfl) ⟨512693, by rfl⟩ : syracuseStep 683591 = 1025387) B1025387
theorem B683743 : Blo 682313 683743 := bstep (se 1 (by rfl) ⟨512807, by rfl⟩ : syracuseStep 683743 = 1025615) B1025615
theorem B1535723 : Blo 682313 1535723 := bstep (se 1 (by rfl) ⟨1151792, by rfl⟩ : syracuseStep 1535723 = 2303585) B2303585
theorem B3469067 : Blo 682313 3469067 := bstep (se 1 (by rfl) ⟨2601800, by rfl⟩ : syracuseStep 3469067 = 5203601) B5203601
theorem B683823 : Blo 682313 683823 := bstep (se 1 (by rfl) ⟨512867, by rfl⟩ : syracuseStep 683823 = 1025735) B1025735
theorem B1535849 : Blo 682313 1535849 := bstep (se 2 (by rfl) ⟨575943, by rfl⟩ : syracuseStep 1535849 = 1151887) B1151887
theorem B683931 : Blo 682313 683931 := bstep (se 1 (by rfl) ⟨512948, by rfl⟩ : syracuseStep 683931 = 1025897) B1025897
theorem B683983 : Blo 682313 683983 := bstep (se 1 (by rfl) ⟨512987, by rfl⟩ : syracuseStep 683983 = 1025975) B1025975
theorem B684007 : Blo 682313 684007 := bstep (se 1 (by rfl) ⟨513005, by rfl⟩ : syracuseStep 684007 = 1026011) B1026011
theorem B3371033 : Blo 682313 3371033 := bstep (se 2 (by rfl) ⟨1264137, by rfl⟩ : syracuseStep 3371033 = 2528275) B2528275
theorem B2191465 : Blo 682313 2191465 := bstep (se 2 (by rfl) ⟨821799, by rfl⟩ : syracuseStep 2191465 = 1643599) B1643599
theorem B9892043 : Blo 682313 9892043 := bstep (se 1 (by rfl) ⟨7419032, by rfl⟩ : syracuseStep 9892043 = 14838065) B14838065
theorem B1732873 : Blo 682313 1732873 := bstep (se 2 (by rfl) ⟨649827, by rfl⟩ : syracuseStep 1732873 = 1299655) B1299655
theorem B684319 : Blo 682313 684319 := bstep (se 1 (by rfl) ⟨513239, by rfl⟩ : syracuseStep 684319 = 1026479) B1026479
theorem B684379 : Blo 682313 684379 := bstep (se 1 (by rfl) ⟨513284, by rfl⟩ : syracuseStep 684379 = 1026569) B1026569
theorem B684399 : Blo 682313 684399 := bstep (se 1 (by rfl) ⟨513299, by rfl⟩ : syracuseStep 684399 = 1026599) B1026599
theorem B684455 : Blo 682313 684455 := bstep (se 1 (by rfl) ⟨513341, by rfl⟩ : syracuseStep 684455 = 1026683) B1026683
theorem B684539 : Blo 682313 684539 := bstep (se 1 (by rfl) ⟨513404, by rfl⟩ : syracuseStep 684539 = 1026809) B1026809
theorem B684607 : Blo 682313 684607 := bstep (se 1 (by rfl) ⟨513455, by rfl⟩ : syracuseStep 684607 = 1026911) B1026911
theorem B684615 : Blo 682313 684615 := bstep (se 1 (by rfl) ⟨513461, by rfl⟩ : syracuseStep 684615 = 1026923) B1026923
theorem B1536695 : Blo 682313 1536695 := bstep (se 1 (by rfl) ⟨1152521, by rfl⟩ : syracuseStep 1536695 = 2305043) B2305043
theorem B3470039 : Blo 682313 3470039 := bstep (se 1 (by rfl) ⟨2602529, by rfl⟩ : syracuseStep 3470039 = 5205059) B5205059
theorem B684767 : Blo 682313 684767 := bstep (se 1 (by rfl) ⟨513575, by rfl⟩ : syracuseStep 684767 = 1027151) B1027151
theorem B684847 : Blo 682313 684847 := bstep (se 1 (by rfl) ⟨513635, by rfl⟩ : syracuseStep 684847 = 1027271) B1027271
theorem B42169187 : Blo 682313 42169187 := bstep (se 1 (by rfl) ⟨31626890, by rfl⟩ : syracuseStep 42169187 = 63253781) B63253781
theorem B5862253 : Blo 682313 5862253 := bstep (se 3 (by rfl) ⟨1099172, by rfl⟩ : syracuseStep 5862253 = 2198345) B2198345
theorem B1536911 : Blo 682313 1536911 := bstep (se 1 (by rfl) ⟨1152683, by rfl⟩ : syracuseStep 1536911 = 2305367) B2305367
theorem B684955 : Blo 682313 684955 := bstep (se 1 (by rfl) ⟨513716, by rfl⟩ : syracuseStep 684955 = 1027433) B1027433
theorem B685007 : Blo 682313 685007 := bstep (se 1 (by rfl) ⟨513755, by rfl⟩ : syracuseStep 685007 = 1027511) B1027511
theorem B685031 : Blo 682313 685031 := bstep (se 1 (by rfl) ⟨513773, by rfl⟩ : syracuseStep 685031 = 1027547) B1027547
theorem B26375219 : Blo 682313 26375219 := bstep (se 1 (by rfl) ⟨19781414, by rfl⟩ : syracuseStep 26375219 = 39562829) B39562829
theorem B28112143 : Blo 682313 28112143 := bstep (se 1 (by rfl) ⟨21084107, by rfl⟩ : syracuseStep 28112143 = 42168215) B42168215
theorem B685343 : Blo 682313 685343 := bstep (se 1 (by rfl) ⟨514007, by rfl⟩ : syracuseStep 685343 = 1028015) B1028015
theorem B685403 : Blo 682313 685403 := bstep (se 1 (by rfl) ⟨514052, by rfl⟩ : syracuseStep 685403 = 1028105) B1028105
theorem B3470687 : Blo 682313 3470687 := bstep (se 1 (by rfl) ⟨2603015, by rfl⟩ : syracuseStep 3470687 = 5206031) B5206031
theorem B685423 : Blo 682313 685423 := bstep (se 1 (by rfl) ⟨514067, by rfl⟩ : syracuseStep 685423 = 1028135) B1028135
theorem B685479 : Blo 682313 685479 := bstep (se 1 (by rfl) ⟨514109, by rfl⟩ : syracuseStep 685479 = 1028219) B1028219
theorem B5207489 : Blo 682313 5207489 := bstep (se 2 (by rfl) ⟨1952808, by rfl⟩ : syracuseStep 5207489 = 3905617) B3905617
theorem B685563 : Blo 682313 685563 := bstep (se 1 (by rfl) ⟨514172, by rfl⟩ : syracuseStep 685563 = 1028345) B1028345
theorem B3896869 : Blo 682313 3896869 := bstep (se 4 (by rfl) ⟨365331, by rfl⟩ : syracuseStep 3896869 = 730663) B730663
theorem B685631 : Blo 682313 685631 := bstep (se 1 (by rfl) ⟨514223, by rfl⟩ : syracuseStep 685631 = 1028447) B1028447
theorem B685639 : Blo 682313 685639 := bstep (se 1 (by rfl) ⟨514229, by rfl⟩ : syracuseStep 685639 = 1028459) B1028459
theorem B1537631 : Blo 682313 1537631 := bstep (se 1 (by rfl) ⟨1153223, by rfl⟩ : syracuseStep 1537631 = 2306447) B2306447
theorem B1734331 : Blo 682313 1734331 := bstep (se 1 (by rfl) ⟨1300748, by rfl⟩ : syracuseStep 1734331 = 2601497) B2601497
theorem B685791 : Blo 682313 685791 := bstep (se 1 (by rfl) ⟨514343, by rfl⟩ : syracuseStep 685791 = 1028687) B1028687
theorem B685871 : Blo 682313 685871 := bstep (se 1 (by rfl) ⟨514403, by rfl⟩ : syracuseStep 685871 = 1028807) B1028807
theorem B1537847 : Blo 682313 1537847 := bstep (se 1 (by rfl) ⟨1153385, by rfl⟩ : syracuseStep 1537847 = 2306771) B2306771
theorem B3897143 : Blo 682313 3897143 := bstep (se 1 (by rfl) ⟨2922857, by rfl⟩ : syracuseStep 3897143 = 5845715) B5845715
theorem B685979 : Blo 682313 685979 := bstep (se 1 (by rfl) ⟨514484, by rfl⟩ : syracuseStep 685979 = 1028969) B1028969
theorem B686031 : Blo 682313 686031 := bstep (se 1 (by rfl) ⟨514523, by rfl⟩ : syracuseStep 686031 = 1029047) B1029047
theorem B686055 : Blo 682313 686055 := bstep (se 1 (by rfl) ⟨514541, by rfl⟩ : syracuseStep 686055 = 1029083) B1029083
theorem B1538153 : Blo 682313 1538153 := bstep (se 2 (by rfl) ⟨576807, by rfl⟩ : syracuseStep 1538153 = 1153615) B1153615
theorem B3701321 : Blo 682313 3701321 := bstep (se 2 (by rfl) ⟨1387995, by rfl⟩ : syracuseStep 3701321 = 2775991) B2775991
theorem B1538639 : Blo 682313 1538639 := bstep (se 1 (by rfl) ⟨1153979, by rfl⟩ : syracuseStep 1538639 = 2307959) B2307959
theorem B4389515 : Blo 682313 4389515 := bstep (se 1 (by rfl) ⟨3292136, by rfl⟩ : syracuseStep 4389515 = 6584273) B6584273
theorem B1538783 : Blo 682313 1538783 := bstep (se 1 (by rfl) ⟨1154087, by rfl⟩ : syracuseStep 1538783 = 2308175) B2308175
theorem B1735415 : Blo 682313 1735415 := bstep (se 1 (by rfl) ⟨1301561, by rfl⟩ : syracuseStep 1735415 = 2603123) B2603123
theorem B5929847 : Blo 682313 5929847 := bstep (se 1 (by rfl) ⟨4447385, by rfl⟩ : syracuseStep 5929847 = 8894771) B8894771
theorem B7502777 : Blo 682313 7502777 := bstep (se 2 (by rfl) ⟨2813541, by rfl⟩ : syracuseStep 7502777 = 5627083) B5627083
theorem B1539035 : Blo 682313 1539035 := bstep (se 1 (by rfl) ⟨1154276, by rfl⟩ : syracuseStep 1539035 = 2308553) B2308553
theorem B4684787 : Blo 682313 4684787 := bstep (se 1 (by rfl) ⟨3513590, by rfl⟩ : syracuseStep 4684787 = 7027181) B7027181
theorem B1539215 : Blo 682313 1539215 := bstep (se 1 (by rfl) ⟨1154411, by rfl⟩ : syracuseStep 1539215 = 2308823) B2308823
theorem B5831909 : Blo 682313 5831909 := bstep (se 4 (by rfl) ⟨546741, by rfl⟩ : syracuseStep 5831909 = 1093483) B1093483
theorem B1539305 : Blo 682313 1539305 := bstep (se 2 (by rfl) ⟨577239, by rfl⟩ : syracuseStep 1539305 = 1154479) B1154479
theorem B1539359 : Blo 682313 1539359 := bstep (se 1 (by rfl) ⟨1154519, by rfl⟩ : syracuseStep 1539359 = 2309039) B2309039
theorem B3472955 : Blo 682313 3472955 := bstep (se 1 (by rfl) ⟨2604716, by rfl⟩ : syracuseStep 3472955 = 5209433) B5209433
theorem B1736275 : Blo 682313 1736275 := bstep (se 1 (by rfl) ⟨1302206, by rfl⟩ : syracuseStep 1736275 = 2604413) B2604413
theorem B7405319 : Blo 682313 7405319 := bstep (se 1 (by rfl) ⟨5553989, by rfl⟩ : syracuseStep 7405319 = 11107979) B11107979
theorem B1539881 : Blo 682313 1539881 := bstep (se 2 (by rfl) ⟨577455, by rfl⟩ : syracuseStep 1539881 = 1154911) B1154911
theorem B3473441 : Blo 682313 3473441 := bstep (se 2 (by rfl) ⟨1302540, by rfl⟩ : syracuseStep 3473441 = 2605081) B2605081
theorem B11665457 : Blo 682313 11665457 := bstep (se 2 (by rfl) ⟨4374546, by rfl⟩ : syracuseStep 11665457 = 8749093) B8749093
theorem B1736923 : Blo 682313 1736923 := bstep (se 1 (by rfl) ⟨1302692, by rfl⟩ : syracuseStep 1736923 = 2605385) B2605385
theorem B4162043 : Blo 682313 4162043 := bstep (se 1 (by rfl) ⟨3121532, by rfl⟩ : syracuseStep 4162043 = 6243065) B6243065
theorem B950887 : Blo 682313 950887 := bstep (se 1 (by rfl) ⟨713165, by rfl⟩ : syracuseStep 950887 = 1426331) B1426331
theorem B2196143 : Blo 682313 2196143 := bstep (se 1 (by rfl) ⟨1647107, by rfl⟩ : syracuseStep 2196143 = 3294215) B3294215
theorem B5866711 : Blo 682313 5866711 := bstep (se 1 (by rfl) ⟨4400033, by rfl⟩ : syracuseStep 5866711 = 8800067) B8800067
theorem B1541483 : Blo 682313 1541483 := bstep (se 1 (by rfl) ⟨1156112, by rfl⟩ : syracuseStep 1541483 = 2312225) B2312225
theorem B1541753 : Blo 682313 1541753 := bstep (se 2 (by rfl) ⟨578157, by rfl⟩ : syracuseStep 1541753 = 1156315) B1156315
theorem B2459591 : Blo 682313 2459591 := bstep (se 1 (by rfl) ⟨1844693, by rfl⟩ : syracuseStep 2459591 = 3689387) B3689387
theorem B8685683 : Blo 682313 8685683 := bstep (se 1 (by rfl) ⟨6514262, by rfl⟩ : syracuseStep 8685683 = 13028525) B13028525
theorem B12454235 : Blo 682313 12454235 := bstep (se 1 (by rfl) ⟨9340676, by rfl⟩ : syracuseStep 12454235 = 18681353) B18681353
theorem B1542761 : Blo 682313 1542761 := bstep (se 2 (by rfl) ⟨578535, by rfl⟩ : syracuseStep 1542761 = 1157071) B1157071
theorem B822107 : Blo 682313 822107 := bstep (se 1 (by rfl) ⟨616580, by rfl⟩ : syracuseStep 822107 = 1233161) B1233161
theorem B2591777 : Blo 682313 2591777 := bstep (se 2 (by rfl) ⟨971916, by rfl⟩ : syracuseStep 2591777 = 1943833) B1943833
theorem B1870895 : Blo 682313 1870895 := bstep (se 1 (by rfl) ⟨1403171, by rfl⟩ : syracuseStep 1870895 = 2806343) B2806343
theorem B7408691 : Blo 682313 7408691 := bstep (se 1 (by rfl) ⟨5556518, by rfl⟩ : syracuseStep 7408691 = 11113037) B11113037
theorem B1543391 : Blo 682313 1543391 := bstep (se 1 (by rfl) ⟨1157543, by rfl⟩ : syracuseStep 1543391 = 2315087) B2315087
theorem B1543607 : Blo 682313 1543607 := bstep (se 1 (by rfl) ⟨1157705, by rfl⟩ : syracuseStep 1543607 = 2315411) B2315411
theorem B5836283 : Blo 682313 5836283 := bstep (se 1 (by rfl) ⟨4377212, by rfl⟩ : syracuseStep 5836283 = 8754425) B8754425
theorem B1543787 : Blo 682313 1543787 := bstep (se 1 (by rfl) ⟨1157840, by rfl⟩ : syracuseStep 1543787 = 2315681) B2315681
theorem B2592431 : Blo 682313 2592431 := bstep (se 1 (by rfl) ⟨1944323, by rfl⟩ : syracuseStep 2592431 = 3888647) B3888647
theorem B1969939 : Blo 682313 1969939 := bstep (se 1 (by rfl) ⟨1477454, by rfl⟩ : syracuseStep 1969939 = 2954909) B2954909
theorem B2920313 : Blo 682313 2920313 := bstep (se 2 (by rfl) ⟨1095117, by rfl⟩ : syracuseStep 2920313 = 2190235) B2190235
theorem B1544057 : Blo 682313 1544057 := bstep (se 2 (by rfl) ⟨579021, by rfl⟩ : syracuseStep 1544057 = 1158043) B1158043
theorem B379097009 : Blo 682313 379097009 := bstep (se 2 (by rfl) ⟨142161378, by rfl⟩ : syracuseStep 379097009 = 284322757) B284322757
theorem B2592749 : Blo 682313 2592749 := bstep (se 3 (by rfl) ⟨486140, by rfl⟩ : syracuseStep 2592749 = 972281) B972281
theorem B8786819 : Blo 682313 8786819 := bstep (se 1 (by rfl) ⟨6590114, by rfl⟩ : syracuseStep 8786819 = 13180229) B13180229
theorem B1151995 : Blo 682313 1151995 := bstep (se 1 (by rfl) ⟨863996, by rfl⟩ : syracuseStep 1151995 = 1727993) B1727993
theorem B3740687 : Blo 682313 3740687 := bstep (se 1 (by rfl) ⟨2805515, by rfl⟩ : syracuseStep 3740687 = 5611031) B5611031
theorem B1774867 : Blo 682313 1774867 := bstep (se 1 (by rfl) ⟨1331150, by rfl⟩ : syracuseStep 1774867 = 2662301) B2662301
theorem B3282295 : Blo 682313 3282295 := bstep (se 1 (by rfl) ⟨2461721, by rfl⟩ : syracuseStep 3282295 = 4923443) B4923443
theorem B1152427 : Blo 682313 1152427 := bstep (se 1 (by rfl) ⟨864320, by rfl⟩ : syracuseStep 1152427 = 1728641) B1728641
theorem B2921953 : Blo 682313 2921953 := bstep (se 2 (by rfl) ⟨1095732, by rfl⟩ : syracuseStep 2921953 = 2191465) B2191465
theorem B1152623 : Blo 682313 1152623 := bstep (se 1 (by rfl) ⟨864467, by rfl⟩ : syracuseStep 1152623 = 1728935) B1728935
theorem B1152731 : Blo 682313 1152731 := bstep (se 1 (by rfl) ⟨864548, by rfl⟩ : syracuseStep 1152731 = 1729097) B1729097
theorem B2463625 : Blo 682313 2463625 := bstep (se 2 (by rfl) ⟨923859, by rfl⟩ : syracuseStep 2463625 = 1847719) B1847719
theorem B1152967 : Blo 682313 1152967 := bstep (se 1 (by rfl) ⟨864725, by rfl⟩ : syracuseStep 1152967 = 1729451) B1729451
theorem B2595179 : Blo 682313 2595179 := bstep (se 1 (by rfl) ⟨1946384, by rfl⟩ : syracuseStep 2595179 = 3892769) B3892769
theorem B20224399 : Blo 682313 20224399 := bstep (se 1 (by rfl) ⟨15168299, by rfl⟩ : syracuseStep 20224399 = 30336599) B30336599
theorem B4921829 : Blo 682313 4921829 := bstep (se 4 (by rfl) ⟨461421, by rfl⟩ : syracuseStep 4921829 = 922843) B922843
theorem B3283507 : Blo 682313 3283507 := bstep (se 1 (by rfl) ⟨2462630, by rfl⟩ : syracuseStep 3283507 = 4925261) B4925261
theorem B1153723 : Blo 682313 1153723 := bstep (se 1 (by rfl) ⟨865292, by rfl⟩ : syracuseStep 1153723 = 1730585) B1730585
theorem B2595665 : Blo 682313 2595665 := bstep (se 2 (by rfl) ⟨973374, by rfl⟩ : syracuseStep 2595665 = 1946749) B1946749
theorem B1154027 : Blo 682313 1154027 := bstep (se 1 (by rfl) ⟨865520, by rfl⟩ : syracuseStep 1154027 = 1731041) B1731041
theorem B1186795 : Blo 682313 1186795 := bstep (se 1 (by rfl) ⟨890096, by rfl⟩ : syracuseStep 1186795 = 1780193) B1780193
theorem B9378935 : Blo 682313 9378935 := bstep (se 1 (by rfl) ⟨7034201, by rfl⟩ : syracuseStep 9378935 = 14068403) B14068403
theorem B7806131 : Blo 682313 7806131 := bstep (se 1 (by rfl) ⟨5854598, by rfl⟩ : syracuseStep 7806131 = 11709197) B11709197
theorem B2464951 : Blo 682313 2464951 := bstep (se 1 (by rfl) ⟨1848713, by rfl⟩ : syracuseStep 2464951 = 3697427) B3697427
theorem B1023551 : Blo 682313 1023551 := bstep (se 1 (by rfl) ⟨767663, by rfl⟩ : syracuseStep 1023551 = 1535327) B1535327
theorem B10690127 : Blo 682313 10690127 := bstep (se 1 (by rfl) ⟨8017595, by rfl⟩ : syracuseStep 10690127 = 16035191) B16035191
theorem B8789795 : Blo 682313 8789795 := bstep (se 1 (by rfl) ⟨6592346, by rfl⟩ : syracuseStep 8789795 = 13184693) B13184693
theorem B1023815 : Blo 682313 1023815 := bstep (se 1 (by rfl) ⟨767861, by rfl⟩ : syracuseStep 1023815 = 1535723) B1535723
theorem B1023899 : Blo 682313 1023899 := bstep (se 1 (by rfl) ⟨767924, by rfl⟩ : syracuseStep 1023899 = 1535849) B1535849
theorem B6594695 : Blo 682313 6594695 := bstep (se 1 (by rfl) ⟨4946021, by rfl⟩ : syracuseStep 6594695 = 9892043) B9892043
theorem B1024463 : Blo 682313 1024463 := bstep (se 1 (by rfl) ⟨768347, by rfl⟩ : syracuseStep 1024463 = 1536695) B1536695
theorem B1024505 : Blo 682313 1024505 := bstep (se 2 (by rfl) ⟨384189, by rfl⟩ : syracuseStep 1024505 = 768379) B768379
theorem B1024607 : Blo 682313 1024607 := bstep (se 1 (by rfl) ⟨768455, by rfl⟩ : syracuseStep 1024607 = 1536911) B1536911
theorem B1025087 : Blo 682313 1025087 := bstep (se 1 (by rfl) ⟨768815, by rfl⟩ : syracuseStep 1025087 = 1537631) B1537631
theorem B1025129 : Blo 682313 1025129 := bstep (se 2 (by rfl) ⟨384423, by rfl⟩ : syracuseStep 1025129 = 768847) B768847
theorem B2303099 : Blo 682313 2303099 := bstep (se 1 (by rfl) ⟨1727324, by rfl⟩ : syracuseStep 2303099 = 3454649) B3454649
theorem B1025231 : Blo 682313 1025231 := bstep (se 1 (by rfl) ⟨768923, by rfl⟩ : syracuseStep 1025231 = 1537847) B1537847
theorem B2598095 : Blo 682313 2598095 := bstep (se 1 (by rfl) ⟨1948571, by rfl⟩ : syracuseStep 2598095 = 3897143) B3897143
theorem B2303369 : Blo 682313 2303369 := bstep (se 2 (by rfl) ⟨863763, by rfl⟩ : syracuseStep 2303369 = 1727527) B1727527
theorem B1025435 : Blo 682313 1025435 := bstep (se 1 (by rfl) ⟨769076, by rfl⟩ : syracuseStep 1025435 = 1538153) B1538153
theorem B1025657 : Blo 682313 1025657 := bstep (se 2 (by rfl) ⟨384621, by rfl⟩ : syracuseStep 1025657 = 769243) B769243
theorem B2467547 : Blo 682313 2467547 := bstep (se 1 (by rfl) ⟨1850660, by rfl⟩ : syracuseStep 2467547 = 3701321) B3701321
theorem B1025759 : Blo 682313 1025759 := bstep (se 1 (by rfl) ⟨769319, by rfl⟩ : syracuseStep 1025759 = 1538639) B1538639
theorem B2926343 : Blo 682313 2926343 := bstep (se 1 (by rfl) ⟨2194757, by rfl⟩ : syracuseStep 2926343 = 4389515) B4389515
theorem B1025855 : Blo 682313 1025855 := bstep (se 1 (by rfl) ⟨769391, by rfl⟩ : syracuseStep 1025855 = 1538783) B1538783
theorem B1156943 : Blo 682313 1156943 := bstep (se 1 (by rfl) ⟨867707, by rfl⟩ : syracuseStep 1156943 = 1735415) B1735415
theorem B1026023 : Blo 682313 1026023 := bstep (se 1 (by rfl) ⟨769517, by rfl⟩ : syracuseStep 1026023 = 1539035) B1539035
theorem B3123191 : Blo 682313 3123191 := bstep (se 1 (by rfl) ⟨2342393, by rfl⟩ : syracuseStep 3123191 = 4684787) B4684787
theorem B1026041 : Blo 682313 1026041 := bstep (se 2 (by rfl) ⟨384765, by rfl⟩ : syracuseStep 1026041 = 769531) B769531
theorem B4925519 : Blo 682313 4925519 := bstep (se 1 (by rfl) ⟨3694139, by rfl⟩ : syracuseStep 4925519 = 7388279) B7388279
theorem B1026143 : Blo 682313 1026143 := bstep (se 1 (by rfl) ⟨769607, by rfl⟩ : syracuseStep 1026143 = 1539215) B1539215
theorem B2304125 : Blo 682313 2304125 := bstep (se 3 (by rfl) ⟨432023, by rfl⟩ : syracuseStep 2304125 = 864047) B864047
theorem B2599037 : Blo 682313 2599037 := bstep (se 3 (by rfl) ⟨487319, by rfl⟩ : syracuseStep 2599037 = 974639) B974639
theorem B3123353 : Blo 682313 3123353 := bstep (se 2 (by rfl) ⟨1171257, by rfl⟩ : syracuseStep 3123353 = 2342515) B2342515
theorem B1026203 : Blo 682313 1026203 := bstep (se 1 (by rfl) ⟨769652, by rfl⟩ : syracuseStep 1026203 = 1539305) B1539305
theorem B1026239 : Blo 682313 1026239 := bstep (se 1 (by rfl) ⟨769679, by rfl⟩ : syracuseStep 1026239 = 1539359) B1539359
theorem B1026281 : Blo 682313 1026281 := bstep (se 2 (by rfl) ⟨384855, by rfl⟩ : syracuseStep 1026281 = 769711) B769711
theorem B1648991 : Blo 682313 1648991 := bstep (se 1 (by rfl) ⟨1236743, by rfl⟩ : syracuseStep 1648991 = 2473487) B2473487
theorem B2304395 : Blo 682313 2304395 := bstep (se 1 (by rfl) ⟨1728296, by rfl⟩ : syracuseStep 2304395 = 3456593) B3456593
theorem B1026587 : Blo 682313 1026587 := bstep (se 1 (by rfl) ⟨769940, by rfl⟩ : syracuseStep 1026587 = 1539881) B1539881
theorem B1026665 : Blo 682313 1026665 := bstep (se 2 (by rfl) ⟨384999, by rfl⟩ : syracuseStep 1026665 = 769999) B769999
theorem B2599735 : Blo 682313 2599735 := bstep (se 1 (by rfl) ⟨1949801, by rfl⟩ : syracuseStep 2599735 = 3899603) B3899603
theorem B1027193 : Blo 682313 1027193 := bstep (se 2 (by rfl) ⟨385197, by rfl⟩ : syracuseStep 1027193 = 770395) B770395
theorem B2370703 : Blo 682313 2370703 := bstep (se 1 (by rfl) ⟨1778027, by rfl⟩ : syracuseStep 2370703 = 3556055) B3556055
theorem B1027295 : Blo 682313 1027295 := bstep (se 1 (by rfl) ⟨770471, by rfl⟩ : syracuseStep 1027295 = 1540943) B1540943
theorem B1027337 : Blo 682313 1027337 := bstep (se 2 (by rfl) ⟨385251, by rfl⟩ : syracuseStep 1027337 = 770503) B770503
theorem B1027439 : Blo 682313 1027439 := bstep (se 1 (by rfl) ⟨770579, by rfl⟩ : syracuseStep 1027439 = 1541159) B1541159
theorem B1027559 : Blo 682313 1027559 := bstep (se 1 (by rfl) ⟨770669, by rfl⟩ : syracuseStep 1027559 = 1541339) B1541339
theorem B2076155 : Blo 682313 2076155 := bstep (se 1 (by rfl) ⟨1557116, by rfl⟩ : syracuseStep 2076155 = 3114233) B3114233
theorem B1388027 : Blo 682313 1388027 := bstep (se 1 (by rfl) ⟨1041020, by rfl⟩ : syracuseStep 1388027 = 2082041) B2082041
theorem B29994569 : Blo 682313 29994569 := bstep (se 2 (by rfl) ⟨11247963, by rfl⟩ : syracuseStep 29994569 = 22495927) B22495927
theorem B1027691 : Blo 682313 1027691 := bstep (se 1 (by rfl) ⟨770768, by rfl⟩ : syracuseStep 1027691 = 1541537) B1541537
theorem B1027817 : Blo 682313 1027817 := bstep (se 2 (by rfl) ⟨385431, by rfl⟩ : syracuseStep 1027817 = 770863) B770863
theorem B1027961 : Blo 682313 1027961 := bstep (se 2 (by rfl) ⟨385485, by rfl⟩ : syracuseStep 1027961 = 770971) B770971
theorem B2306015 : Blo 682313 2306015 := bstep (se 1 (by rfl) ⟨1729511, by rfl⟩ : syracuseStep 2306015 = 3459023) B3459023
theorem B1028063 : Blo 682313 1028063 := bstep (se 1 (by rfl) ⟨771047, by rfl⟩ : syracuseStep 1028063 = 1542095) B1542095
theorem B2633851 : Blo 682313 2633851 := bstep (se 1 (by rfl) ⟨1975388, by rfl⟩ : syracuseStep 2633851 = 3950777) B3950777
theorem B2306177 : Blo 682313 2306177 := bstep (se 2 (by rfl) ⟨864816, by rfl⟩ : syracuseStep 2306177 = 1729633) B1729633
theorem B1028315 : Blo 682313 1028315 := bstep (se 1 (by rfl) ⟨771236, by rfl⟩ : syracuseStep 1028315 = 1542473) B1542473
theorem B1028327 : Blo 682313 1028327 := bstep (se 1 (by rfl) ⟨771245, by rfl⟩ : syracuseStep 1028327 = 1542491) B1542491
theorem B1028489 : Blo 682313 1028489 := bstep (se 2 (by rfl) ⟨385683, by rfl⟩ : syracuseStep 1028489 = 771367) B771367
theorem B1028585 : Blo 682313 1028585 := bstep (se 2 (by rfl) ⟨385719, by rfl⟩ : syracuseStep 1028585 = 771439) B771439
theorem B2306663 : Blo 682313 2306663 := bstep (se 1 (by rfl) ⟨1729997, by rfl⟩ : syracuseStep 2306663 = 3459995) B3459995
theorem B1028711 : Blo 682313 1028711 := bstep (se 1 (by rfl) ⟨771533, by rfl⟩ : syracuseStep 1028711 = 1543067) B1543067
theorem B1028843 : Blo 682313 1028843 := bstep (se 1 (by rfl) ⟨771632, by rfl⟩ : syracuseStep 1028843 = 1543265) B1543265
theorem B1028873 : Blo 682313 1028873 := bstep (se 2 (by rfl) ⟨385827, by rfl⟩ : syracuseStep 1028873 = 771655) B771655
theorem B1028975 : Blo 682313 1028975 := bstep (se 1 (by rfl) ⟨771731, by rfl⟩ : syracuseStep 1028975 = 1543463) B1543463
theorem B20034469 : Blo 682313 20034469 := bstep (se 4 (by rfl) ⟨1878231, by rfl⟩ : syracuseStep 20034469 = 3756463) B3756463
theorem B2306987 : Blo 682313 2306987 := bstep (se 1 (by rfl) ⟨1730240, by rfl⟩ : syracuseStep 2306987 = 3460481) B3460481
theorem B865343 : Blo 682313 865343 := bstep (se 1 (by rfl) ⟨649007, by rfl⟩ : syracuseStep 865343 = 1298015) B1298015
theorem B1029227 : Blo 682313 1029227 := bstep (se 1 (by rfl) ⟨771920, by rfl⟩ : syracuseStep 1029227 = 1543841) B1543841
theorem B2307419 : Blo 682313 2307419 := bstep (se 1 (by rfl) ⟨1730564, by rfl⟩ : syracuseStep 2307419 = 3461129) B3461129
theorem B1029467 : Blo 682313 1029467 := bstep (se 1 (by rfl) ⟨772100, by rfl⟩ : syracuseStep 1029467 = 1544201) B1544201
theorem B2307527 : Blo 682313 2307527 := bstep (se 1 (by rfl) ⟨1730645, by rfl⟩ : syracuseStep 2307527 = 3461291) B3461291
theorem B2602439 : Blo 682313 2602439 := bstep (se 1 (by rfl) ⟨1951829, by rfl⟩ : syracuseStep 2602439 = 3903659) B3903659
theorem B50083393 : Blo 682313 50083393 := bstep (se 2 (by rfl) ⟨18781272, by rfl⟩ : syracuseStep 50083393 = 37562545) B37562545
theorem B1095239 : Blo 682313 1095239 := bstep (se 1 (by rfl) ⟨821429, by rfl⟩ : syracuseStep 1095239 = 1642859) B1642859
theorem B2307851 : Blo 682313 2307851 := bstep (se 1 (by rfl) ⟨1730888, by rfl⟩ : syracuseStep 2307851 = 3461777) B3461777
theorem B6567743 : Blo 682313 6567743 := bstep (se 1 (by rfl) ⟨4925807, by rfl⟩ : syracuseStep 6567743 = 9851615) B9851615
theorem B767983 : Blo 682313 767983 := bstep (se 1 (by rfl) ⟨575987, by rfl⟩ : syracuseStep 767983 = 1151975) B1151975
theorem B2308121 : Blo 682313 2308121 := bstep (se 2 (by rfl) ⟨865545, by rfl⟩ : syracuseStep 2308121 = 1731091) B1731091
theorem B35633459 : Blo 682313 35633459 := bstep (se 1 (by rfl) ⟨26725094, by rfl⟩ : syracuseStep 35633459 = 53450189) B53450189
theorem B2636441 : Blo 682313 2636441 := bstep (se 2 (by rfl) ⟨988665, by rfl⟩ : syracuseStep 2636441 = 1977331) B1977331
theorem B63159193 : Blo 682313 63159193 := bstep (se 2 (by rfl) ⟨23684697, by rfl⟩ : syracuseStep 63159193 = 47369395) B47369395
theorem B1096969 : Blo 682313 1096969 := bstep (se 2 (by rfl) ⟨411363, by rfl⟩ : syracuseStep 1096969 = 822727) B822727
theorem B2309471 : Blo 682313 2309471 := bstep (se 1 (by rfl) ⟨1732103, by rfl⟩ : syracuseStep 2309471 = 3464207) B3464207
theorem B8306363 : Blo 682313 8306363 := bstep (se 1 (by rfl) ⟨6229772, by rfl⟩ : syracuseStep 8306363 = 12459545) B12459545
theorem B2310011 : Blo 682313 2310011 := bstep (se 1 (by rfl) ⟨1732508, by rfl⟩ : syracuseStep 2310011 = 3465017) B3465017
theorem B3293099 : Blo 682313 3293099 := bstep (se 1 (by rfl) ⟨2469824, by rfl⟩ : syracuseStep 3293099 = 4939649) B4939649
theorem B868583 : Blo 682313 868583 := bstep (se 1 (by rfl) ⟨651437, by rfl⟩ : syracuseStep 868583 = 1302875) B1302875
theorem B2310497 : Blo 682313 2310497 := bstep (se 2 (by rfl) ⟨866436, by rfl⟩ : syracuseStep 2310497 = 1732873) B1732873
theorem B770431 : Blo 682313 770431 := bstep (se 1 (by rfl) ⟨577823, by rfl⟩ : syracuseStep 770431 = 1155647) B1155647
theorem B8307143 : Blo 682313 8307143 := bstep (se 1 (by rfl) ⟨6230357, by rfl⟩ : syracuseStep 8307143 = 12460715) B12460715
theorem B1950281 : Blo 682313 1950281 := bstep (se 2 (by rfl) ⟨731355, by rfl⟩ : syracuseStep 1950281 = 1462711) B1462711
theorem B2081555 : Blo 682313 2081555 := bstep (se 1 (by rfl) ⟨1561166, by rfl⟩ : syracuseStep 2081555 = 3122333) B3122333
theorem B9847925 : Blo 682313 9847925 := bstep (se 5 (by rfl) ⟨461621, by rfl⟩ : syracuseStep 9847925 = 923243) B923243
theorem B6341777 : Blo 682313 6341777 := bstep (se 2 (by rfl) ⟨2378166, by rfl⟩ : syracuseStep 6341777 = 4756333) B4756333
theorem B7816337 : Blo 682313 7816337 := bstep (se 2 (by rfl) ⟨2931126, by rfl⟩ : syracuseStep 7816337 = 5862253) B5862253
theorem B9356705 : Blo 682313 9356705 := bstep (se 2 (by rfl) ⟨3508764, by rfl⟩ : syracuseStep 9356705 = 7017529) B7017529
theorem B30033341 : Blo 682313 30033341 := bstep (se 3 (by rfl) ⟨5631251, by rfl⟩ : syracuseStep 30033341 = 11262503) B11262503
theorem B9848267 : Blo 682313 9848267 := bstep (se 1 (by rfl) ⟨7386200, by rfl⟩ : syracuseStep 9848267 = 14772401) B14772401
theorem B1853039 : Blo 682313 1853039 := bstep (se 1 (by rfl) ⟨1389779, by rfl⟩ : syracuseStep 1853039 = 2779559) B2779559
theorem B6342259 : Blo 682313 6342259 := bstep (se 1 (by rfl) ⟨4756694, by rfl⟩ : syracuseStep 6342259 = 9513389) B9513389
theorem B2311847 : Blo 682313 2311847 := bstep (se 1 (by rfl) ⟨1733885, by rfl⟩ : syracuseStep 2311847 = 3467771) B3467771
theorem B771835 : Blo 682313 771835 := bstep (se 1 (by rfl) ⟨578876, by rfl⟩ : syracuseStep 771835 = 1157753) B1157753
theorem B771871 : Blo 682313 771871 := bstep (se 1 (by rfl) ⟨578903, by rfl⟩ : syracuseStep 771871 = 1157807) B1157807
theorem B379012931 : Blo 682313 379012931 := bstep (se 1 (by rfl) ⟨284259698, by rfl⟩ : syracuseStep 379012931 = 568519397) B568519397
theorem B5195825 : Blo 682313 5195825 := bstep (se 2 (by rfl) ⟨1948434, by rfl⟩ : syracuseStep 5195825 = 3896869) B3896869
theorem B2312441 : Blo 682313 2312441 := bstep (se 2 (by rfl) ⟨867165, by rfl⟩ : syracuseStep 2312441 = 1734331) B1734331
theorem B2312495 : Blo 682313 2312495 := bstep (se 1 (by rfl) ⟨1734371, by rfl⟩ : syracuseStep 2312495 = 3468743) B3468743
theorem B2312711 : Blo 682313 2312711 := bstep (se 1 (by rfl) ⟨1734533, by rfl⟩ : syracuseStep 2312711 = 3469067) B3469067
theorem B2247355 : Blo 682313 2247355 := bstep (se 1 (by rfl) ⟨1685516, by rfl⟩ : syracuseStep 2247355 = 3371033) B3371033
theorem B1297529 : Blo 682313 1297529 := bstep (se 2 (by rfl) ⟨486573, by rfl⟩ : syracuseStep 1297529 = 973147) B973147
theorem B2313359 : Blo 682313 2313359 := bstep (se 1 (by rfl) ⟨1735019, by rfl⟩ : syracuseStep 2313359 = 3470039) B3470039
theorem B3460319 : Blo 682313 3460319 := bstep (se 1 (by rfl) ⟨2595239, by rfl⟩ : syracuseStep 3460319 = 5190479) B5190479
theorem B17583479 : Blo 682313 17583479 := bstep (se 1 (by rfl) ⟨13187609, by rfl⟩ : syracuseStep 17583479 = 26375219) B26375219
theorem B2313791 : Blo 682313 2313791 := bstep (se 1 (by rfl) ⟨1735343, by rfl⟩ : syracuseStep 2313791 = 3470687) B3470687
theorem B1232491 : Blo 682313 1232491 := bstep (se 1 (by rfl) ⟨924368, by rfl⟩ : syracuseStep 1232491 = 1848737) B1848737
theorem B2314493 : Blo 682313 2314493 := bstep (se 3 (by rfl) ⟨433967, by rfl⟩ : syracuseStep 2314493 = 867935) B867935
theorem B6836653 : Blo 682313 6836653 := bstep (se 3 (by rfl) ⟨1281872, by rfl⟩ : syracuseStep 6836653 = 2563745) B2563745
theorem B1167823 : Blo 682313 1167823 := bstep (se 1 (by rfl) ⟨875867, by rfl⟩ : syracuseStep 1167823 = 1751735) B1751735
theorem B3953231 : Blo 682313 3953231 := bstep (se 1 (by rfl) ⟨2964923, by rfl⟩ : syracuseStep 3953231 = 5929847) B5929847
theorem B5001851 : Blo 682313 5001851 := bstep (se 1 (by rfl) ⟨3751388, by rfl⟩ : syracuseStep 5001851 = 7502777) B7502777
theorem B4215545 : Blo 682313 4215545 := bstep (se 2 (by rfl) ⟨1580829, by rfl⟩ : syracuseStep 4215545 = 3161659) B3161659
theorem B2315033 : Blo 682313 2315033 := bstep (se 2 (by rfl) ⟨868137, by rfl⟩ : syracuseStep 2315033 = 1736275) B1736275
theorem B3887939 : Blo 682313 3887939 := bstep (se 1 (by rfl) ⟨2915954, by rfl⟩ : syracuseStep 3887939 = 5831909) B5831909
theorem B1233875 : Blo 682313 1233875 := bstep (se 1 (by rfl) ⟨925406, by rfl⟩ : syracuseStep 1233875 = 1850813) B1850813
theorem B2315303 : Blo 682313 2315303 := bstep (se 1 (by rfl) ⟨1736477, by rfl⟩ : syracuseStep 2315303 = 3472955) B3472955
theorem B6575201 : Blo 682313 6575201 := bstep (se 2 (by rfl) ⟨2465700, by rfl⟩ : syracuseStep 6575201 = 4931401) B4931401
theorem B4936879 : Blo 682313 4936879 := bstep (se 1 (by rfl) ⟨3702659, by rfl⟩ : syracuseStep 4936879 = 7405319) B7405319
theorem B4937051 : Blo 682313 4937051 := bstep (se 1 (by rfl) ⟨3702788, by rfl⟩ : syracuseStep 4937051 = 7405577) B7405577
theorem B4674935 : Blo 682313 4674935 := bstep (se 1 (by rfl) ⟨3506201, by rfl⟩ : syracuseStep 4674935 = 7012403) B7012403
theorem B28431767 : Blo 682313 28431767 := bstep (se 1 (by rfl) ⟨21323825, by rfl⟩ : syracuseStep 28431767 = 42647651) B42647651
theorem B3462587 : Blo 682313 3462587 := bstep (se 1 (by rfl) ⟨2596940, by rfl⟩ : syracuseStep 3462587 = 5193881) B5193881
theorem B3889079 : Blo 682313 3889079 := bstep (se 1 (by rfl) ⟨2916809, by rfl⟩ : syracuseStep 3889079 = 5833619) B5833619
theorem B6576551 : Blo 682313 6576551 := bstep (se 1 (by rfl) ⟨4932413, by rfl⟩ : syracuseStep 6576551 = 9864827) B9864827
theorem B1727315 : Blo 682313 1727315 := bstep (se 1 (by rfl) ⟨1295486, by rfl⟩ : syracuseStep 1727315 = 2590973) B2590973
theorem B3464045 : Blo 682313 3464045 := bstep (se 3 (by rfl) ⟨649508, by rfl⟩ : syracuseStep 3464045 = 1299017) B1299017
theorem B2251745 : Blo 682313 2251745 := bstep (se 2 (by rfl) ⟨844404, by rfl⟩ : syracuseStep 2251745 = 1688809) B1688809
theorem B974047 : Blo 682313 974047 := bstep (se 1 (by rfl) ⟨730535, by rfl⟩ : syracuseStep 974047 = 1461071) B1461071
theorem B1236455 : Blo 682313 1236455 := bstep (se 1 (by rfl) ⟨927341, by rfl⟩ : syracuseStep 1236455 = 1854683) B1854683
theorem B112451165 : Blo 682313 112451165 := bstep (se 3 (by rfl) ⟨21084593, by rfl⟩ : syracuseStep 112451165 = 42169187) B42169187
theorem B4940023 : Blo 682313 4940023 := bstep (se 1 (by rfl) ⟨3705017, by rfl⟩ : syracuseStep 4940023 = 7410035) B7410035
theorem B3465503 : Blo 682313 3465503 := bstep (se 1 (by rfl) ⟨2599127, by rfl⟩ : syracuseStep 3465503 = 5198255) B5198255
theorem B159572429 : Blo 682313 159572429 := bstep (se 3 (by rfl) ⟨29919830, by rfl⟩ : syracuseStep 159572429 = 59839661) B59839661
theorem B4383341 : Blo 682313 4383341 := bstep (se 3 (by rfl) ⟨821876, by rfl⟩ : syracuseStep 4383341 = 1643753) B1643753
theorem B1729259 : Blo 682313 1729259 := bstep (se 1 (by rfl) ⟨1296944, by rfl⟩ : syracuseStep 1729259 = 2593889) B2593889
theorem B1729289 : Blo 682313 1729289 := bstep (se 2 (by rfl) ⟨648483, by rfl⟩ : syracuseStep 1729289 = 1296967) B1296967
theorem B2188043 : Blo 682313 2188043 := bstep (se 1 (by rfl) ⟨1641032, by rfl⟩ : syracuseStep 2188043 = 3282065) B3282065
theorem B7037725 : Blo 682313 7037725 := bstep (se 3 (by rfl) ⟨1319573, by rfl⟩ : syracuseStep 7037725 = 2639147) B2639147
theorem B7922717 : Blo 682313 7922717 := bstep (se 3 (by rfl) ⟨1485509, by rfl⟩ : syracuseStep 7922717 = 2971019) B2971019
theorem B3892313 : Blo 682313 3892313 := bstep (se 2 (by rfl) ⟨1459617, by rfl⟩ : syracuseStep 3892313 = 2919235) B2919235
theorem B2189825 : Blo 682313 2189825 := bstep (se 2 (by rfl) ⟨821184, by rfl⟩ : syracuseStep 2189825 = 1642369) B1642369
theorem B682523 : Blo 682313 682523 := bstep (se 1 (by rfl) ⟨511892, by rfl⟩ : syracuseStep 682523 = 1023785) B1023785
theorem B682527 : Blo 682313 682527 := bstep (se 1 (by rfl) ⟨511895, by rfl⟩ : syracuseStep 682527 = 1023791) B1023791
theorem B682843 : Blo 682313 682843 := bstep (se 1 (by rfl) ⟨512132, by rfl⟩ : syracuseStep 682843 = 1024265) B1024265
theorem B682911 : Blo 682313 682911 := bstep (se 1 (by rfl) ⟨512183, by rfl⟩ : syracuseStep 682911 = 1024367) B1024367
theorem B5008391 : Blo 682313 5008391 := bstep (se 1 (by rfl) ⟨3756293, by rfl⟩ : syracuseStep 5008391 = 7512587) B7512587
theorem B683055 : Blo 682313 683055 := bstep (se 1 (by rfl) ⟨512291, by rfl⟩ : syracuseStep 683055 = 1024583) B1024583
theorem B683079 : Blo 682313 683079 := bstep (se 1 (by rfl) ⟨512309, by rfl⟩ : syracuseStep 683079 = 1024619) B1024619
theorem B4385927 : Blo 682313 4385927 := bstep (se 1 (by rfl) ⟨3289445, by rfl⟩ : syracuseStep 4385927 = 6578891) B6578891
theorem B683231 : Blo 682313 683231 := bstep (se 1 (by rfl) ⟨512423, by rfl⟩ : syracuseStep 683231 = 1024847) B1024847
theorem B15756743 : Blo 682313 15756743 := bstep (se 1 (by rfl) ⟨11817557, by rfl⟩ : syracuseStep 15756743 = 23635115) B23635115
theorem B683495 : Blo 682313 683495 := bstep (se 1 (by rfl) ⟨512621, by rfl⟩ : syracuseStep 683495 = 1025243) B1025243
theorem B1535561 : Blo 682313 1535561 := bstep (se 2 (by rfl) ⟨575835, by rfl⟩ : syracuseStep 1535561 = 1151671) B1151671
theorem B683611 : Blo 682313 683611 := bstep (se 1 (by rfl) ⟨512708, by rfl⟩ : syracuseStep 683611 = 1025417) B1025417
theorem B683847 : Blo 682313 683847 := bstep (se 1 (by rfl) ⟨512885, by rfl⟩ : syracuseStep 683847 = 1025771) B1025771
theorem B3469229 : Blo 682313 3469229 := bstep (se 3 (by rfl) ⟨650480, by rfl⟩ : syracuseStep 3469229 = 1300961) B1300961
theorem B683999 : Blo 682313 683999 := bstep (se 1 (by rfl) ⟨512999, by rfl⟩ : syracuseStep 683999 = 1025999) B1025999
theorem B684263 : Blo 682313 684263 := bstep (se 1 (by rfl) ⟨513197, by rfl⟩ : syracuseStep 684263 = 1026395) B1026395
theorem B37482857 : Blo 682313 37482857 := bstep (se 2 (by rfl) ⟨14056071, by rfl⟩ : syracuseStep 37482857 = 28112143) B28112143
theorem B684415 : Blo 682313 684415 := bstep (se 1 (by rfl) ⟨513311, by rfl⟩ : syracuseStep 684415 = 1026623) B1026623
theorem B684495 : Blo 682313 684495 := bstep (se 1 (by rfl) ⟨513371, by rfl⟩ : syracuseStep 684495 = 1026743) B1026743
theorem B684647 : Blo 682313 684647 := bstep (se 1 (by rfl) ⟨513485, by rfl⟩ : syracuseStep 684647 = 1026971) B1026971
theorem B684911 : Blo 682313 684911 := bstep (se 1 (by rfl) ⟨513683, by rfl⟩ : syracuseStep 684911 = 1027367) B1027367
theorem B684967 : Blo 682313 684967 := bstep (se 1 (by rfl) ⟨513725, by rfl⟩ : syracuseStep 684967 = 1027451) B1027451
theorem B1537019 : Blo 682313 1537019 := bstep (se 1 (by rfl) ⟨1152764, by rfl⟩ : syracuseStep 1537019 = 2305529) B2305529
theorem B685051 : Blo 682313 685051 := bstep (se 1 (by rfl) ⟨513788, by rfl⟩ : syracuseStep 685051 = 1027577) B1027577
theorem B685119 : Blo 682313 685119 := bstep (se 1 (by rfl) ⟨513839, by rfl⟩ : syracuseStep 685119 = 1027679) B1027679
theorem B1537199 : Blo 682313 1537199 := bstep (se 1 (by rfl) ⟨1152899, by rfl⟩ : syracuseStep 1537199 = 2305799) B2305799
theorem B685263 : Blo 682313 685263 := bstep (se 1 (by rfl) ⟨513947, by rfl⟩ : syracuseStep 685263 = 1027895) B1027895
theorem B1537235 : Blo 682313 1537235 := bstep (se 1 (by rfl) ⟨1152926, by rfl⟩ : syracuseStep 1537235 = 2305853) B2305853
theorem B9008435 : Blo 682313 9008435 := bstep (se 1 (by rfl) ⟨6756326, by rfl⟩ : syracuseStep 9008435 = 13512653) B13512653
theorem B685467 : Blo 682313 685467 := bstep (se 1 (by rfl) ⟨514100, by rfl⟩ : syracuseStep 685467 = 1028201) B1028201
theorem B1537505 : Blo 682313 1537505 := bstep (se 2 (by rfl) ⟨576564, by rfl⟩ : syracuseStep 1537505 = 1153129) B1153129
theorem B3470849 : Blo 682313 3470849 := bstep (se 2 (by rfl) ⟨1301568, by rfl⟩ : syracuseStep 3470849 = 2603137) B2603137
theorem B685679 : Blo 682313 685679 := bstep (se 1 (by rfl) ⟨514259, by rfl⟩ : syracuseStep 685679 = 1028519) B1028519
theorem B685735 : Blo 682313 685735 := bstep (se 1 (by rfl) ⟨514301, by rfl⟩ : syracuseStep 685735 = 1028603) B1028603
theorem B685819 : Blo 682313 685819 := bstep (se 1 (by rfl) ⟨514364, by rfl⟩ : syracuseStep 685819 = 1028729) B1028729
theorem B685855 : Blo 682313 685855 := bstep (se 1 (by rfl) ⟨514391, by rfl⟩ : syracuseStep 685855 = 1028783) B1028783
theorem B685887 : Blo 682313 685887 := bstep (se 1 (by rfl) ⟨514415, by rfl⟩ : syracuseStep 685887 = 1028831) B1028831
theorem B686063 : Blo 682313 686063 := bstep (se 1 (by rfl) ⟨514547, by rfl⟩ : syracuseStep 686063 = 1029095) B1029095
theorem B686235 : Blo 682313 686235 := bstep (se 1 (by rfl) ⟨514676, by rfl⟩ : syracuseStep 686235 = 1029353) B1029353
theorem B1734817 : Blo 682313 1734817 := bstep (se 2 (by rfl) ⟨650556, by rfl⟩ : syracuseStep 1734817 = 1301113) B1301113
theorem B686271 : Blo 682313 686271 := bstep (se 1 (by rfl) ⟨514703, by rfl⟩ : syracuseStep 686271 = 1029407) B1029407
theorem B3471659 : Blo 682313 3471659 := bstep (se 1 (by rfl) ⟨2603744, by rfl⟩ : syracuseStep 3471659 = 5207489) B5207489
theorem B4684349 : Blo 682313 4684349 := bstep (se 3 (by rfl) ⟨878315, by rfl⟩ : syracuseStep 4684349 = 1756631) B1756631
theorem B1539143 : Blo 682313 1539143 := bstep (se 1 (by rfl) ⟨1154357, by rfl⟩ : syracuseStep 1539143 = 2308715) B2308715
theorem B4389977 : Blo 682313 4389977 := bstep (se 2 (by rfl) ⟨1646241, by rfl⟩ : syracuseStep 4389977 = 3292483) B3292483
theorem B1539539 : Blo 682313 1539539 := bstep (se 1 (by rfl) ⟨1154654, by rfl⟩ : syracuseStep 1539539 = 2309309) B2309309
theorem B3898853 : Blo 682313 3898853 := bstep (se 4 (by rfl) ⟨365517, by rfl⟩ : syracuseStep 3898853 = 731035) B731035
theorem B2194951 : Blo 682313 2194951 := bstep (se 1 (by rfl) ⟨1646213, by rfl⟩ : syracuseStep 2194951 = 3292427) B3292427
theorem B1539809 : Blo 682313 1539809 := bstep (se 2 (by rfl) ⟨577428, by rfl⟩ : syracuseStep 1539809 = 1154857) B1154857
theorem B1736417 : Blo 682313 1736417 := bstep (se 2 (by rfl) ⟨651156, by rfl⟩ : syracuseStep 1736417 = 1302313) B1302313
theorem B1540331 : Blo 682313 1540331 := bstep (se 1 (by rfl) ⟨1155248, by rfl⟩ : syracuseStep 1540331 = 2310497) B2310497
theorem B5538095 : Blo 682313 5538095 := bstep (se 1 (by rfl) ⟨4153571, by rfl⟩ : syracuseStep 5538095 = 8307143) B8307143
theorem B6586697 : Blo 682313 6586697 := bstep (se 2 (by rfl) ⟨2470011, by rfl⟩ : syracuseStep 6586697 = 4940023) B4940023
theorem B4227851 : Blo 682313 4227851 := bstep (se 1 (by rfl) ⟨3170888, by rfl⟩ : syracuseStep 4227851 = 6341777) B6341777
theorem B5210891 : Blo 682313 5210891 := bstep (se 1 (by rfl) ⟨3908168, by rfl⟩ : syracuseStep 5210891 = 7816337) B7816337
theorem B20022227 : Blo 682313 20022227 := bstep (se 1 (by rfl) ⟨15016670, by rfl⟩ : syracuseStep 20022227 = 30033341) B30033341
theorem B1541231 : Blo 682313 1541231 := bstep (se 1 (by rfl) ⟨1155923, by rfl⟩ : syracuseStep 1541231 = 2311847) B2311847
theorem B252675287 : Blo 682313 252675287 := bstep (se 1 (by rfl) ⟨189506465, by rfl⟩ : syracuseStep 252675287 = 379012931) B379012931
theorem B1639727 : Blo 682313 1639727 := bstep (se 1 (by rfl) ⟨1229795, by rfl⟩ : syracuseStep 1639727 = 2459591) B2459591
theorem B1541627 : Blo 682313 1541627 := bstep (se 1 (by rfl) ⟨1156220, by rfl⟩ : syracuseStep 1541627 = 2312441) B2312441
theorem B1541663 : Blo 682313 1541663 := bstep (se 1 (by rfl) ⟨1156247, by rfl⟩ : syracuseStep 1541663 = 2312495) B2312495
theorem B1541807 : Blo 682313 1541807 := bstep (se 1 (by rfl) ⟨1156355, by rfl⟩ : syracuseStep 1541807 = 2312711) B2312711
theorem B1542239 : Blo 682313 1542239 := bstep (se 1 (by rfl) ⟨1156679, by rfl⟩ : syracuseStep 1542239 = 2313359) B2313359
theorem B8456345 : Blo 682313 8456345 := bstep (se 2 (by rfl) ⟨3171129, by rfl⟩ : syracuseStep 8456345 = 6342259) B6342259
theorem B1542527 : Blo 682313 1542527 := bstep (se 1 (by rfl) ⟨1156895, by rfl⟩ : syracuseStep 1542527 = 2313791) B2313791
theorem B6228389 : Blo 682313 6228389 := bstep (se 4 (by rfl) ⟨583911, by rfl⟩ : syracuseStep 6228389 = 1167823) B1167823
theorem B1542995 : Blo 682313 1542995 := bstep (se 1 (by rfl) ⟨1157246, by rfl⟩ : syracuseStep 1542995 = 2314493) B2314493
theorem B1543355 : Blo 682313 1543355 := bstep (se 1 (by rfl) ⟨1157516, by rfl⟩ : syracuseStep 1543355 = 2315033) B2315033
theorem B2591959 : Blo 682313 2591959 := bstep (se 1 (by rfl) ⟨1943969, by rfl⟩ : syracuseStep 2591959 = 3887939) B3887939
theorem B822583 : Blo 682313 822583 := bstep (se 1 (by rfl) ⟨616937, by rfl⟩ : syracuseStep 822583 = 1233875) B1233875
theorem B2493791 : Blo 682313 2493791 := bstep (se 1 (by rfl) ⟨1870343, by rfl⟩ : syracuseStep 2493791 = 3740687) B3740687
theorem B1543535 : Blo 682313 1543535 := bstep (se 1 (by rfl) ⟨1157651, by rfl⟩ : syracuseStep 1543535 = 2315303) B2315303
theorem B2592719 : Blo 682313 2592719 := bstep (se 1 (by rfl) ⟨1944539, by rfl⟩ : syracuseStep 2592719 = 3889079) B3889079
theorem B2920637 : Blo 682313 2920637 := bstep (se 3 (by rfl) ⟨547619, by rfl⟩ : syracuseStep 2920637 = 1095239) B1095239
theorem B3281219 : Blo 682313 3281219 := bstep (se 1 (by rfl) ⟨2460914, by rfl⟩ : syracuseStep 3281219 = 4921829) B4921829
theorem B1151543 : Blo 682313 1151543 := bstep (se 1 (by rfl) ⟨863657, by rfl⟩ : syracuseStep 1151543 = 1727315) B1727315
theorem B1643321 : Blo 682313 1643321 := bstep (se 2 (by rfl) ⟨616245, by rfl⟩ : syracuseStep 1643321 = 1232491) B1232491
theorem B824303 : Blo 682313 824303 := bstep (se 1 (by rfl) ⟨618227, by rfl⟩ : syracuseStep 824303 = 1236455) B1236455
theorem B6329573 : Blo 682313 6329573 := bstep (se 4 (by rfl) ⟨593397, by rfl⟩ : syracuseStep 6329573 = 1186795) B1186795
theorem B4396463 : Blo 682313 4396463 := bstep (se 1 (by rfl) ⟨3297347, by rfl⟩ : syracuseStep 4396463 = 6594695) B6594695
theorem B3511801 : Blo 682313 3511801 := bstep (se 2 (by rfl) ⟨1316925, by rfl⟩ : syracuseStep 3511801 = 2633851) B2633851
theorem B2922227 : Blo 682313 2922227 := bstep (se 1 (by rfl) ⟨2191670, by rfl⟩ : syracuseStep 2922227 = 4383341) B4383341
theorem B1152839 : Blo 682313 1152839 := bstep (se 1 (by rfl) ⟨864629, by rfl⟩ : syracuseStep 1152839 = 1729259) B1729259
theorem B1152859 : Blo 682313 1152859 := bstep (se 1 (by rfl) ⟨864644, by rfl⟩ : syracuseStep 1152859 = 1729289) B1729289
theorem B9115537 : Blo 682313 9115537 := bstep (se 2 (by rfl) ⟨3418326, by rfl⟩ : syracuseStep 9115537 = 6836653) B6836653
theorem B5281811 : Blo 682313 5281811 := bstep (se 1 (by rfl) ⟨3961358, by rfl⟩ : syracuseStep 5281811 = 7922717) B7922717
theorem B2594875 : Blo 682313 2594875 := bstep (se 1 (by rfl) ⟨1946156, by rfl⟩ : syracuseStep 2594875 = 3892313) B3892313
theorem B1645031 : Blo 682313 1645031 := bstep (se 1 (by rfl) ⟨1233773, by rfl⟩ : syracuseStep 1645031 = 2467547) B2467547
theorem B3283679 : Blo 682313 3283679 := bstep (se 1 (by rfl) ⟨2462759, by rfl⟩ : syracuseStep 3283679 = 4925519) B4925519
theorem B12491597 : Blo 682313 12491597 := bstep (se 3 (by rfl) ⟨2342174, by rfl⟩ : syracuseStep 12491597 = 4684349) B4684349
theorem B2366489 : Blo 682313 2366489 := bstep (se 2 (by rfl) ⟨887433, by rfl⟩ : syracuseStep 2366489 = 1774867) B1774867
theorem B2923951 : Blo 682313 2923951 := bstep (se 1 (by rfl) ⟨2192963, by rfl⟩ : syracuseStep 2923951 = 4385927) B4385927
theorem B1384103 : Blo 682313 1384103 := bstep (se 1 (by rfl) ⟨1038077, by rfl⟩ : syracuseStep 1384103 = 2076155) B2076155
theorem B925351 : Blo 682313 925351 := bstep (se 1 (by rfl) ⟨694013, by rfl⟩ : syracuseStep 925351 = 1388027) B1388027
theorem B1023707 : Blo 682313 1023707 := bstep (se 1 (by rfl) ⟨767780, by rfl⟩ : syracuseStep 1023707 = 1535561) B1535561
theorem B19996379 : Blo 682313 19996379 := bstep (se 1 (by rfl) ⟨14997284, by rfl⟩ : syracuseStep 19996379 = 29994569) B29994569
theorem B3284833 : Blo 682313 3284833 := bstep (se 2 (by rfl) ⟨1231812, by rfl⟩ : syracuseStep 3284833 = 2463625) B2463625
theorem B44965813 : Blo 682313 44965813 := bstep (se 5 (by rfl) ⟨2107772, by rfl⟩ : syracuseStep 44965813 = 4215545) B4215545
theorem B1023977 : Blo 682313 1023977 := bstep (se 2 (by rfl) ⟨383991, by rfl⟩ : syracuseStep 1023977 = 767983) B767983
theorem B4989053 : Blo 682313 4989053 := bstep (se 3 (by rfl) ⟨935447, by rfl⟩ : syracuseStep 4989053 = 1870895) B1870895
theorem B1024679 : Blo 682313 1024679 := bstep (se 1 (by rfl) ⟨768509, by rfl⟩ : syracuseStep 1024679 = 1537019) B1537019
theorem B1024799 : Blo 682313 1024799 := bstep (se 1 (by rfl) ⟨768599, by rfl⟩ : syracuseStep 1024799 = 1537199) B1537199
theorem B1024823 : Blo 682313 1024823 := bstep (se 1 (by rfl) ⟨768617, by rfl⟩ : syracuseStep 1024823 = 1537235) B1537235
theorem B6005623 : Blo 682313 6005623 := bstep (se 1 (by rfl) ⟨4504217, by rfl⟩ : syracuseStep 6005623 = 9008435) B9008435
theorem B1025003 : Blo 682313 1025003 := bstep (se 1 (by rfl) ⟨768752, by rfl⟩ : syracuseStep 1025003 = 1537505) B1537505
theorem B3286601 : Blo 682313 3286601 := bstep (se 2 (by rfl) ⟨1232475, by rfl⟩ : syracuseStep 3286601 = 2464951) B2464951
theorem B2926601 : Blo 682313 2926601 := bstep (se 2 (by rfl) ⟨1097475, by rfl⟩ : syracuseStep 2926601 = 2194951) B2194951
theorem B1026095 : Blo 682313 1026095 := bstep (se 1 (by rfl) ⟨769571, by rfl⟩ : syracuseStep 1026095 = 1539143) B1539143
theorem B2926651 : Blo 682313 2926651 := bstep (se 1 (by rfl) ⟨2194988, by rfl⟩ : syracuseStep 2926651 = 4389977) B4389977
theorem B1026359 : Blo 682313 1026359 := bstep (se 1 (by rfl) ⟨769769, by rfl⟩ : syracuseStep 1026359 = 1539539) B1539539
theorem B2599235 : Blo 682313 2599235 := bstep (se 1 (by rfl) ⟨1949426, by rfl⟩ : syracuseStep 2599235 = 3898853) B3898853
theorem B1026539 : Blo 682313 1026539 := bstep (se 1 (by rfl) ⟨769904, by rfl⟩ : syracuseStep 1026539 = 1539809) B1539809
theorem B1157611 : Blo 682313 1157611 := bstep (se 1 (by rfl) ⟨868208, by rfl⟩ : syracuseStep 1157611 = 1736417) B1736417
theorem B7776971 : Blo 682313 7776971 := bstep (se 1 (by rfl) ⟨5832728, by rfl⟩ : syracuseStep 7776971 = 11665457) B11665457
theorem B1027241 : Blo 682313 1027241 := bstep (se 2 (by rfl) ⟨385215, by rfl⟩ : syracuseStep 1027241 = 770431) B770431
theorem B1387703 : Blo 682313 1387703 := bstep (se 1 (by rfl) ⟨1040777, by rfl⟩ : syracuseStep 1387703 = 2081555) B2081555
theorem B6565283 : Blo 682313 6565283 := bstep (se 1 (by rfl) ⟨4923962, by rfl⟩ : syracuseStep 6565283 = 9847925) B9847925
theorem B1027655 : Blo 682313 1027655 := bstep (se 1 (by rfl) ⟨770741, by rfl⟩ : syracuseStep 1027655 = 1541483) B1541483
theorem B6237803 : Blo 682313 6237803 := bstep (se 1 (by rfl) ⟨4678352, by rfl⟩ : syracuseStep 6237803 = 9356705) B9356705
theorem B6565511 : Blo 682313 6565511 := bstep (se 1 (by rfl) ⟨4924133, by rfl⟩ : syracuseStep 6565511 = 9848267) B9848267
theorem B9383633 : Blo 682313 9383633 := bstep (se 2 (by rfl) ⟨3518862, by rfl⟩ : syracuseStep 9383633 = 7037725) B7037725
theorem B1027835 : Blo 682313 1027835 := bstep (se 1 (by rfl) ⟨770876, by rfl⟩ : syracuseStep 1027835 = 1541753) B1541753
theorem B8302823 : Blo 682313 8302823 := bstep (se 1 (by rfl) ⟨6227117, by rfl⟩ : syracuseStep 8302823 = 12454235) B12454235
theorem B1028507 : Blo 682313 1028507 := bstep (se 1 (by rfl) ⟨771380, by rfl⟩ : syracuseStep 1028507 = 1542761) B1542761
theorem B865019 : Blo 682313 865019 := bstep (se 1 (by rfl) ⟨648764, by rfl⟩ : syracuseStep 865019 = 1297529) B1297529
theorem B2306879 : Blo 682313 2306879 := bstep (se 1 (by rfl) ⟨1730159, by rfl⟩ : syracuseStep 2306879 = 3460319) B3460319
theorem B1028927 : Blo 682313 1028927 := bstep (se 1 (by rfl) ⟨771695, by rfl⟩ : syracuseStep 1028927 = 1543391) B1543391
theorem B1029071 : Blo 682313 1029071 := bstep (se 1 (by rfl) ⟨771803, by rfl⟩ : syracuseStep 1029071 = 1543607) B1543607
theorem B1029113 : Blo 682313 1029113 := bstep (se 2 (by rfl) ⟨385917, by rfl⟩ : syracuseStep 1029113 = 771835) B771835
theorem B1029161 : Blo 682313 1029161 := bstep (se 2 (by rfl) ⟨385935, by rfl⟩ : syracuseStep 1029161 = 771871) B771871
theorem B1029191 : Blo 682313 1029191 := bstep (se 1 (by rfl) ⟨771893, by rfl⟩ : syracuseStep 1029191 = 1543787) B1543787
theorem B1946875 : Blo 682313 1946875 := bstep (se 1 (by rfl) ⟨1460156, by rfl⟩ : syracuseStep 1946875 = 2920313) B2920313
theorem B1029371 : Blo 682313 1029371 := bstep (se 1 (by rfl) ⟨772028, by rfl⟩ : syracuseStep 1029371 = 1544057) B1544057
theorem B2307581 : Blo 682313 2307581 := bstep (se 3 (by rfl) ⟨432671, by rfl⟩ : syracuseStep 2307581 = 865343) B865343
theorem B2635487 : Blo 682313 2635487 := bstep (se 1 (by rfl) ⟨1976615, by rfl⟩ : syracuseStep 2635487 = 3953231) B3953231
theorem B3291367 : Blo 682313 3291367 := bstep (se 1 (by rfl) ⟨2468525, by rfl⟩ : syracuseStep 3291367 = 4937051) B4937051
theorem B2308391 : Blo 682313 2308391 := bstep (se 1 (by rfl) ⟨1731293, by rfl⟩ : syracuseStep 2308391 = 3462587) B3462587
theorem B12466493 : Blo 682313 12466493 := bstep (se 3 (by rfl) ⟨2337467, by rfl⟩ : syracuseStep 12466493 = 4674935) B4674935
theorem B768415 : Blo 682313 768415 := bstep (se 1 (by rfl) ⟨576311, by rfl⟩ : syracuseStep 768415 = 1152623) B1152623
theorem B768487 : Blo 682313 768487 := bstep (se 1 (by rfl) ⟨576365, by rfl⟩ : syracuseStep 768487 = 1152731) B1152731
theorem B3160937 : Blo 682313 3160937 := bstep (se 2 (by rfl) ⟨1185351, by rfl⟩ : syracuseStep 3160937 = 2370703) B2370703
theorem B2309363 : Blo 682313 2309363 := bstep (se 1 (by rfl) ⟨1732022, by rfl⟩ : syracuseStep 2309363 = 3464045) B3464045
theorem B769351 : Blo 682313 769351 := bstep (se 1 (by rfl) ⟨577013, by rfl⟩ : syracuseStep 769351 = 1154027) B1154027
theorem B7126751 : Blo 682313 7126751 := bstep (se 1 (by rfl) ⟨5345063, by rfl⟩ : syracuseStep 7126751 = 10690127) B10690127
theorem B2310335 : Blo 682313 2310335 := bstep (se 1 (by rfl) ⟨1732751, by rfl⟩ : syracuseStep 2310335 = 3465503) B3465503
theorem B106381619 : Blo 682313 106381619 := bstep (se 1 (by rfl) ⟨79786214, by rfl⟩ : syracuseStep 106381619 = 159572429) B159572429
theorem B1458695 : Blo 682313 1458695 := bstep (se 1 (by rfl) ⟨1094021, by rfl⟩ : syracuseStep 1458695 = 2188043) B2188043
theorem B1950895 : Blo 682313 1950895 := bstep (se 1 (by rfl) ⟨1463171, by rfl⟩ : syracuseStep 1950895 = 2926343) B2926343
theorem B771295 : Blo 682313 771295 := bstep (se 1 (by rfl) ⟨578471, by rfl⟩ : syracuseStep 771295 = 1156943) B1156943
theorem B2082127 : Blo 682313 2082127 := bstep (se 1 (by rfl) ⟨1561595, by rfl⟩ : syracuseStep 2082127 = 3123191) B3123191
theorem B2082235 : Blo 682313 2082235 := bstep (se 1 (by rfl) ⟨1561676, by rfl⟩ : syracuseStep 2082235 = 3123353) B3123353
theorem B1099327 : Blo 682313 1099327 := bstep (se 1 (by rfl) ⟨824495, by rfl⟩ : syracuseStep 1099327 = 1648991) B1648991
theorem B1459883 : Blo 682313 1459883 := bstep (se 1 (by rfl) ⟨1094912, by rfl⟩ : syracuseStep 1459883 = 2189825) B2189825
theorem B4376393 : Blo 682313 4376393 := bstep (se 2 (by rfl) ⟨1641147, by rfl⟩ : syracuseStep 4376393 = 3282295) B3282295
theorem B10504495 : Blo 682313 10504495 := bstep (se 1 (by rfl) ⟨7878371, by rfl⟩ : syracuseStep 10504495 = 15756743) B15756743
theorem B2312819 : Blo 682313 2312819 := bstep (se 1 (by rfl) ⟨1734614, by rfl⟩ : syracuseStep 2312819 = 3469229) B3469229
theorem B2313089 : Blo 682313 2313089 := bstep (se 2 (by rfl) ⟨867408, by rfl⟩ : syracuseStep 2313089 = 1734817) B1734817
theorem B24988571 : Blo 682313 24988571 := bstep (se 1 (by rfl) ⟨18741428, by rfl⟩ : syracuseStep 24988571 = 37482857) B37482857
theorem B4378009 : Blo 682313 4378009 := bstep (se 2 (by rfl) ⟨1641753, by rfl⟩ : syracuseStep 4378009 = 3283507) B3283507
theorem B2313899 : Blo 682313 2313899 := bstep (se 1 (by rfl) ⟨1735424, by rfl⟩ : syracuseStep 2313899 = 3470849) B3470849
theorem B4378495 : Blo 682313 4378495 := bstep (se 1 (by rfl) ⟨3283871, by rfl⟩ : syracuseStep 4378495 = 6567743) B6567743
theorem B10506341 : Blo 682313 10506341 := bstep (se 4 (by rfl) ⟨984969, by rfl⟩ : syracuseStep 10506341 = 1969939) B1969939
theorem B2314439 : Blo 682313 2314439 := bstep (se 1 (by rfl) ⟨1735829, by rfl⟩ : syracuseStep 2314439 = 3471659) B3471659
theorem B1298729 : Blo 682313 1298729 := bstep (se 2 (by rfl) ⟨487023, by rfl⟩ : syracuseStep 1298729 = 974047) B974047
theorem B1462625 : Blo 682313 1462625 := bstep (se 2 (by rfl) ⟨548484, by rfl⟩ : syracuseStep 1462625 = 1096969) B1096969
theorem B1757627 : Blo 682313 1757627 := bstep (se 1 (by rfl) ⟨1318220, by rfl⟩ : syracuseStep 1757627 = 2636441) B2636441
theorem B2315627 : Blo 682313 2315627 := bstep (se 1 (by rfl) ⟨1736720, by rfl⟩ : syracuseStep 2315627 = 3473441) B3473441
theorem B2315897 : Blo 682313 2315897 := bstep (se 2 (by rfl) ⟨868461, by rfl⟩ : syracuseStep 2315897 = 1736923) B1736923
theorem B2774695 : Blo 682313 2774695 := bstep (se 1 (by rfl) ⟨2081021, by rfl⟩ : syracuseStep 2774695 = 4162043) B4162043
theorem B1300187 : Blo 682313 1300187 := bstep (se 1 (by rfl) ⟨975140, by rfl⟩ : syracuseStep 1300187 = 1950281) B1950281
theorem B1464095 : Blo 682313 1464095 := bstep (se 1 (by rfl) ⟨1098071, by rfl⟩ : syracuseStep 1464095 = 2196143) B2196143
theorem B2316221 : Blo 682313 2316221 := bstep (se 3 (by rfl) ⟨434291, by rfl⟩ : syracuseStep 2316221 = 868583) B868583
theorem B1267849 : Blo 682313 1267849 := bstep (se 2 (by rfl) ⟨475443, by rfl⟩ : syracuseStep 1267849 = 950887) B950887
theorem B1235359 : Blo 682313 1235359 := bstep (se 1 (by rfl) ⟨926519, by rfl⟩ : syracuseStep 1235359 = 1853039) B1853039
theorem B3463883 : Blo 682313 3463883 := bstep (se 1 (by rfl) ⟨2597912, by rfl⟩ : syracuseStep 3463883 = 5195825) B5195825
theorem B5790455 : Blo 682313 5790455 := bstep (se 1 (by rfl) ⟨4342841, by rfl⟩ : syracuseStep 5790455 = 8685683) B8685683
theorem B1727851 : Blo 682313 1727851 := bstep (se 1 (by rfl) ⟨1295888, by rfl⟩ : syracuseStep 1727851 = 2591777) B2591777
theorem B4939127 : Blo 682313 4939127 := bstep (se 1 (by rfl) ⟨3704345, by rfl⟩ : syracuseStep 4939127 = 7408691) B7408691
theorem B11722319 : Blo 682313 11722319 := bstep (se 1 (by rfl) ⟨8791739, by rfl⟩ : syracuseStep 11722319 = 17583479) B17583479
theorem B3890855 : Blo 682313 3890855 := bstep (se 1 (by rfl) ⟨2918141, by rfl⟩ : syracuseStep 3890855 = 5836283) B5836283
theorem B1728287 : Blo 682313 1728287 := bstep (se 1 (by rfl) ⟨1296215, by rfl⟩ : syracuseStep 1728287 = 2592431) B2592431
theorem B252731339 : Blo 682313 252731339 := bstep (se 1 (by rfl) ⟨189548504, by rfl⟩ : syracuseStep 252731339 = 379097009) B379097009
theorem B1728499 : Blo 682313 1728499 := bstep (se 1 (by rfl) ⟨1296374, by rfl⟩ : syracuseStep 1728499 = 2592749) B2592749
theorem B3334567 : Blo 682313 3334567 := bstep (se 1 (by rfl) ⟨2500925, by rfl⟩ : syracuseStep 3334567 = 5001851) B5001851
theorem B5857879 : Blo 682313 5857879 := bstep (se 1 (by rfl) ⟨4393409, by rfl⟩ : syracuseStep 5857879 = 8786819) B8786819
theorem B4383467 : Blo 682313 4383467 := bstep (se 1 (by rfl) ⟨3287600, by rfl⟩ : syracuseStep 4383467 = 6575201) B6575201
theorem B11985893 : Blo 682313 11985893 := bstep (se 4 (by rfl) ⟨1123677, by rfl⟩ : syracuseStep 11985893 = 2247355) B2247355
theorem B75818045 : Blo 682313 75818045 := bstep (se 3 (by rfl) ⟨14215883, by rfl⟩ : syracuseStep 75818045 = 28431767) B28431767
theorem B3466313 : Blo 682313 3466313 := bstep (se 2 (by rfl) ⟨1299867, by rfl⟩ : syracuseStep 3466313 = 2599735) B2599735
theorem B1730119 : Blo 682313 1730119 := bstep (se 1 (by rfl) ⟨1297589, by rfl⟩ : syracuseStep 1730119 = 2595179) B2595179
theorem B4384367 : Blo 682313 4384367 := bstep (se 1 (by rfl) ⟨3288275, by rfl⟩ : syracuseStep 4384367 = 6576551) B6576551
theorem B1730443 : Blo 682313 1730443 := bstep (se 1 (by rfl) ⟨1297832, by rfl⟩ : syracuseStep 1730443 = 2595665) B2595665
theorem B1501163 : Blo 682313 1501163 := bstep (se 1 (by rfl) ⟨1125872, by rfl⟩ : syracuseStep 1501163 = 2251745) B2251745
theorem B6252623 : Blo 682313 6252623 := bstep (se 1 (by rfl) ⟨4689467, by rfl⟩ : syracuseStep 6252623 = 9378935) B9378935
theorem B5204087 : Blo 682313 5204087 := bstep (se 1 (by rfl) ⟨3903065, by rfl⟩ : syracuseStep 5204087 = 7806131) B7806131
theorem B106850501 : Blo 682313 106850501 := bstep (se 4 (by rfl) ⟨10017234, by rfl⟩ : syracuseStep 106850501 = 20034469) B20034469
theorem B682367 : Blo 682313 682367 := bstep (se 1 (by rfl) ⟨511775, by rfl⟩ : syracuseStep 682367 = 1023551) B1023551
theorem B74967443 : Blo 682313 74967443 := bstep (se 1 (by rfl) ⟨56225582, by rfl⟩ : syracuseStep 74967443 = 112451165) B112451165
theorem B5859863 : Blo 682313 5859863 := bstep (se 1 (by rfl) ⟨4394897, by rfl⟩ : syracuseStep 5859863 = 8789795) B8789795
theorem B682543 : Blo 682313 682543 := bstep (se 1 (by rfl) ⟨511907, by rfl⟩ : syracuseStep 682543 = 1023815) B1023815
theorem B682599 : Blo 682313 682599 := bstep (se 1 (by rfl) ⟨511949, by rfl⟩ : syracuseStep 682599 = 1023899) B1023899
theorem B682975 : Blo 682313 682975 := bstep (se 1 (by rfl) ⟨512231, by rfl⟩ : syracuseStep 682975 = 1024463) B1024463
theorem B683003 : Blo 682313 683003 := bstep (se 1 (by rfl) ⟨512252, by rfl⟩ : syracuseStep 683003 = 1024505) B1024505
theorem B683071 : Blo 682313 683071 := bstep (se 1 (by rfl) ⟨512303, by rfl⟩ : syracuseStep 683071 = 1024607) B1024607
theorem B683391 : Blo 682313 683391 := bstep (se 1 (by rfl) ⟨512543, by rfl⟩ : syracuseStep 683391 = 1025087) B1025087
theorem B683419 : Blo 682313 683419 := bstep (se 1 (by rfl) ⟨512564, by rfl⟩ : syracuseStep 683419 = 1025129) B1025129
theorem B1535399 : Blo 682313 1535399 := bstep (se 1 (by rfl) ⟨1151549, by rfl⟩ : syracuseStep 1535399 = 2303099) B2303099
theorem B683487 : Blo 682313 683487 := bstep (se 1 (by rfl) ⟨512615, by rfl⟩ : syracuseStep 683487 = 1025231) B1025231
theorem B1732063 : Blo 682313 1732063 := bstep (se 1 (by rfl) ⟨1299047, by rfl⟩ : syracuseStep 1732063 = 2598095) B2598095
theorem B1535579 : Blo 682313 1535579 := bstep (se 1 (by rfl) ⟨1151684, by rfl⟩ : syracuseStep 1535579 = 2303369) B2303369
theorem B683623 : Blo 682313 683623 := bstep (se 1 (by rfl) ⟨512717, by rfl⟩ : syracuseStep 683623 = 1025435) B1025435
theorem B683771 : Blo 682313 683771 := bstep (se 1 (by rfl) ⟨512828, by rfl⟩ : syracuseStep 683771 = 1025657) B1025657
theorem B31289125 : Blo 682313 31289125 := bstep (se 4 (by rfl) ⟨2933355, by rfl⟩ : syracuseStep 31289125 = 5866711) B5866711
theorem B683839 : Blo 682313 683839 := bstep (se 1 (by rfl) ⟨512879, by rfl⟩ : syracuseStep 683839 = 1025759) B1025759
theorem B683903 : Blo 682313 683903 := bstep (se 1 (by rfl) ⟨512927, by rfl⟩ : syracuseStep 683903 = 1025855) B1025855
theorem B684015 : Blo 682313 684015 := bstep (se 1 (by rfl) ⟨513011, by rfl⟩ : syracuseStep 684015 = 1026023) B1026023
theorem B1535993 : Blo 682313 1535993 := bstep (se 2 (by rfl) ⟨575997, by rfl⟩ : syracuseStep 1535993 = 1151995) B1151995
theorem B684027 : Blo 682313 684027 := bstep (se 1 (by rfl) ⟨513020, by rfl⟩ : syracuseStep 684027 = 1026041) B1026041
theorem B684095 : Blo 682313 684095 := bstep (se 1 (by rfl) ⟨513071, by rfl⟩ : syracuseStep 684095 = 1026143) B1026143
theorem B1536083 : Blo 682313 1536083 := bstep (se 1 (by rfl) ⟨1152062, by rfl⟩ : syracuseStep 1536083 = 2304125) B2304125
theorem B1732691 : Blo 682313 1732691 := bstep (se 1 (by rfl) ⟨1299518, by rfl⟩ : syracuseStep 1732691 = 2599037) B2599037
theorem B684135 : Blo 682313 684135 := bstep (se 1 (by rfl) ⟨513101, by rfl⟩ : syracuseStep 684135 = 1026203) B1026203
theorem B684159 : Blo 682313 684159 := bstep (se 1 (by rfl) ⟨513119, by rfl⟩ : syracuseStep 684159 = 1026239) B1026239
theorem B684187 : Blo 682313 684187 := bstep (se 1 (by rfl) ⟨513140, by rfl⟩ : syracuseStep 684187 = 1026281) B1026281
theorem B6582505 : Blo 682313 6582505 := bstep (se 2 (by rfl) ⟨2468439, by rfl⟩ : syracuseStep 6582505 = 4936879) B4936879
theorem B1536263 : Blo 682313 1536263 := bstep (se 1 (by rfl) ⟨1152197, by rfl⟩ : syracuseStep 1536263 = 2304395) B2304395
theorem B684391 : Blo 682313 684391 := bstep (se 1 (by rfl) ⟨513293, by rfl⟩ : syracuseStep 684391 = 1026587) B1026587
theorem B684443 : Blo 682313 684443 := bstep (se 1 (by rfl) ⟨513332, by rfl⟩ : syracuseStep 684443 = 1026665) B1026665
theorem B1536569 : Blo 682313 1536569 := bstep (se 2 (by rfl) ⟨576213, by rfl⟩ : syracuseStep 1536569 = 1152427) B1152427
theorem B3895937 : Blo 682313 3895937 := bstep (se 2 (by rfl) ⟨1460976, by rfl⟩ : syracuseStep 3895937 = 2921953) B2921953
theorem B3338927 : Blo 682313 3338927 := bstep (se 1 (by rfl) ⟨2504195, by rfl⟩ : syracuseStep 3338927 = 5008391) B5008391
theorem B684795 : Blo 682313 684795 := bstep (se 1 (by rfl) ⟨513596, by rfl⟩ : syracuseStep 684795 = 1027193) B1027193
theorem B66777857 : Blo 682313 66777857 := bstep (se 2 (by rfl) ⟨25041696, by rfl⟩ : syracuseStep 66777857 = 50083393) B50083393
theorem B684863 : Blo 682313 684863 := bstep (se 1 (by rfl) ⟨513647, by rfl⟩ : syracuseStep 684863 = 1027295) B1027295
theorem B684891 : Blo 682313 684891 := bstep (se 1 (by rfl) ⟨513668, by rfl⟩ : syracuseStep 684891 = 1027337) B1027337
theorem B2192285 : Blo 682313 2192285 := bstep (se 3 (by rfl) ⟨411053, by rfl⟩ : syracuseStep 2192285 = 822107) B822107
theorem B684959 : Blo 682313 684959 := bstep (se 1 (by rfl) ⟨513719, by rfl⟩ : syracuseStep 684959 = 1027439) B1027439
theorem B685039 : Blo 682313 685039 := bstep (se 1 (by rfl) ⟨513779, by rfl⟩ : syracuseStep 685039 = 1027559) B1027559
theorem B685127 : Blo 682313 685127 := bstep (se 1 (by rfl) ⟨513845, by rfl⟩ : syracuseStep 685127 = 1027691) B1027691
theorem B685211 : Blo 682313 685211 := bstep (se 1 (by rfl) ⟨513908, by rfl⟩ : syracuseStep 685211 = 1027817) B1027817
theorem B685307 : Blo 682313 685307 := bstep (se 1 (by rfl) ⟨513980, by rfl⟩ : syracuseStep 685307 = 1027961) B1027961
theorem B1537289 : Blo 682313 1537289 := bstep (se 2 (by rfl) ⟨576483, by rfl⟩ : syracuseStep 1537289 = 1152967) B1152967
theorem B1537343 : Blo 682313 1537343 := bstep (se 1 (by rfl) ⟨1153007, by rfl⟩ : syracuseStep 1537343 = 2306015) B2306015
theorem B685375 : Blo 682313 685375 := bstep (se 1 (by rfl) ⟨514031, by rfl⟩ : syracuseStep 685375 = 1028063) B1028063
theorem B1537451 : Blo 682313 1537451 := bstep (se 1 (by rfl) ⟨1153088, by rfl⟩ : syracuseStep 1537451 = 2306177) B2306177
theorem B685543 : Blo 682313 685543 := bstep (se 1 (by rfl) ⟨514157, by rfl⟩ : syracuseStep 685543 = 1028315) B1028315
theorem B685551 : Blo 682313 685551 := bstep (se 1 (by rfl) ⟨514163, by rfl⟩ : syracuseStep 685551 = 1028327) B1028327
theorem B685659 : Blo 682313 685659 := bstep (se 1 (by rfl) ⟨514244, by rfl⟩ : syracuseStep 685659 = 1028489) B1028489
theorem B685723 : Blo 682313 685723 := bstep (se 1 (by rfl) ⟨514292, by rfl⟩ : syracuseStep 685723 = 1028585) B1028585
theorem B1537775 : Blo 682313 1537775 := bstep (se 1 (by rfl) ⟨1153331, by rfl⟩ : syracuseStep 1537775 = 2306663) B2306663
theorem B685807 : Blo 682313 685807 := bstep (se 1 (by rfl) ⟨514355, by rfl⟩ : syracuseStep 685807 = 1028711) B1028711
theorem B685895 : Blo 682313 685895 := bstep (se 1 (by rfl) ⟨514421, by rfl⟩ : syracuseStep 685895 = 1028843) B1028843
theorem B685915 : Blo 682313 685915 := bstep (se 1 (by rfl) ⟨514436, by rfl⟩ : syracuseStep 685915 = 1028873) B1028873
theorem B26965865 : Blo 682313 26965865 := bstep (se 2 (by rfl) ⟨10112199, by rfl⟩ : syracuseStep 26965865 = 20224399) B20224399
theorem B685983 : Blo 682313 685983 := bstep (se 1 (by rfl) ⟨514487, by rfl⟩ : syracuseStep 685983 = 1028975) B1028975
theorem B1537991 : Blo 682313 1537991 := bstep (se 1 (by rfl) ⟨1153493, by rfl⟩ : syracuseStep 1537991 = 2306987) B2306987
theorem B686151 : Blo 682313 686151 := bstep (se 1 (by rfl) ⟨514613, by rfl⟩ : syracuseStep 686151 = 1029227) B1029227
theorem B1538279 : Blo 682313 1538279 := bstep (se 1 (by rfl) ⟨1153709, by rfl⟩ : syracuseStep 1538279 = 2307419) B2307419
theorem B686311 : Blo 682313 686311 := bstep (se 1 (by rfl) ⟨514733, by rfl⟩ : syracuseStep 686311 = 1029467) B1029467
theorem B1538297 : Blo 682313 1538297 := bstep (se 2 (by rfl) ⟨576861, by rfl⟩ : syracuseStep 1538297 = 1153723) B1153723
theorem B1538351 : Blo 682313 1538351 := bstep (se 1 (by rfl) ⟨1153763, by rfl⟩ : syracuseStep 1538351 = 2307527) B2307527
theorem B1734959 : Blo 682313 1734959 := bstep (se 1 (by rfl) ⟨1301219, by rfl⟩ : syracuseStep 1734959 = 2602439) B2602439
theorem B1538567 : Blo 682313 1538567 := bstep (se 1 (by rfl) ⟨1153925, by rfl⟩ : syracuseStep 1538567 = 2307851) B2307851
theorem B84212257 : Blo 682313 84212257 := bstep (se 2 (by rfl) ⟨31579596, by rfl⟩ : syracuseStep 84212257 = 63159193) B63159193
theorem B1538747 : Blo 682313 1538747 := bstep (se 1 (by rfl) ⟨1154060, by rfl⟩ : syracuseStep 1538747 = 2308121) B2308121
theorem B23755639 : Blo 682313 23755639 := bstep (se 1 (by rfl) ⟨17816729, by rfl⟩ : syracuseStep 23755639 = 35633459) B35633459
theorem B1539647 : Blo 682313 1539647 := bstep (se 1 (by rfl) ⟨1154735, by rfl⟩ : syracuseStep 1539647 = 2309471) B2309471
theorem B5537575 : Blo 682313 5537575 := bstep (se 1 (by rfl) ⟨4153181, by rfl⟩ : syracuseStep 5537575 = 8306363) B8306363
theorem B1540007 : Blo 682313 1540007 := bstep (se 1 (by rfl) ⟨1155005, by rfl⟩ : syracuseStep 1540007 = 2310011) B2310011
theorem B2195399 : Blo 682313 2195399 := bstep (se 1 (by rfl) ⟨1646549, by rfl⟩ : syracuseStep 2195399 = 3293099) B3293099
theorem B1540223 : Blo 682313 1540223 := bstep (se 1 (by rfl) ⟨1155167, by rfl⟩ : syracuseStep 1540223 = 2310335) B2310335
theorem B4391131 : Blo 682313 4391131 := bstep (se 1 (by rfl) ⟨3293348, by rfl⟩ : syracuseStep 4391131 = 6586697) B6586697
theorem B2818567 : Blo 682313 2818567 := bstep (se 1 (by rfl) ⟨2113925, by rfl⟩ : syracuseStep 2818567 = 4227851) B4227851
theorem B3473927 : Blo 682313 3473927 := bstep (se 1 (by rfl) ⟨2605445, by rfl⟩ : syracuseStep 3473927 = 5210891) B5210891
theorem B2917595 : Blo 682313 2917595 := bstep (se 1 (by rfl) ⟨2188196, by rfl⟩ : syracuseStep 2917595 = 4376393) B4376393
theorem B5637563 : Blo 682313 5637563 := bstep (se 1 (by rfl) ⟨4228172, by rfl⟩ : syracuseStep 5637563 = 8456345) B8456345
theorem B1541879 : Blo 682313 1541879 := bstep (se 1 (by rfl) ⟨1156409, by rfl⟩ : syracuseStep 1541879 = 2312819) B2312819
theorem B1542059 : Blo 682313 1542059 := bstep (se 1 (by rfl) ⟨1156544, by rfl⟩ : syracuseStep 1542059 = 2313089) B2313089
theorem B1542599 : Blo 682313 1542599 := bstep (se 1 (by rfl) ⟨1156949, by rfl⟩ : syracuseStep 1542599 = 2313899) B2313899
theorem B2198141 : Blo 682313 2198141 := bstep (se 3 (by rfl) ⟨412151, by rfl⟩ : syracuseStep 2198141 = 824303) B824303
theorem B3902201 : Blo 682313 3902201 := bstep (se 2 (by rfl) ⟨1463325, by rfl⟩ : syracuseStep 3902201 = 2926651) B2926651
theorem B1542959 : Blo 682313 1542959 := bstep (se 1 (by rfl) ⟨1157219, by rfl⟩ : syracuseStep 1542959 = 2314439) B2314439
theorem B202181453 : Blo 682313 202181453 := bstep (se 3 (by rfl) ⟨37909022, by rfl⟩ : syracuseStep 202181453 = 75818045) B75818045
theorem B1543481 : Blo 682313 1543481 := bstep (se 2 (by rfl) ⟨578805, by rfl⟩ : syracuseStep 1543481 = 1157611) B1157611
theorem B1543751 : Blo 682313 1543751 := bstep (se 1 (by rfl) ⟨1157813, by rfl⟩ : syracuseStep 1543751 = 2315627) B2315627
theorem B1543931 : Blo 682313 1543931 := bstep (se 1 (by rfl) ⟨1157948, by rfl⟩ : syracuseStep 1543931 = 2315897) B2315897
theorem B1544147 : Blo 682313 1544147 := bstep (se 1 (by rfl) ⟨1158110, by rfl⟩ : syracuseStep 1544147 = 2316221) B2316221
theorem B5837345 : Blo 682313 5837345 := bstep (se 2 (by rfl) ⟨2189004, by rfl⟩ : syracuseStep 5837345 = 4378009) B4378009
theorem B8327731 : Blo 682313 8327731 := bstep (se 1 (by rfl) ⟨6245798, by rfl⟩ : syracuseStep 8327731 = 12491597) B12491597
theorem B1577659 : Blo 682313 1577659 := bstep (se 1 (by rfl) ⟨1183244, by rfl⟩ : syracuseStep 1577659 = 2366489) B2366489
theorem B41718833 : Blo 682313 41718833 := bstep (se 2 (by rfl) ⟨15644562, by rfl⟩ : syracuseStep 41718833 = 31289125) B31289125
theorem B922735 : Blo 682313 922735 := bstep (se 1 (by rfl) ⟨692051, by rfl⟩ : syracuseStep 922735 = 1384103) B1384103
theorem B2593903 : Blo 682313 2593903 := bstep (se 1 (by rfl) ⟨1945427, by rfl⟩ : syracuseStep 2593903 = 3890855) B3890855
theorem B5837993 : Blo 682313 5837993 := bstep (se 2 (by rfl) ⟨2189247, by rfl⟩ : syracuseStep 5837993 = 4378495) B4378495
theorem B1152191 : Blo 682313 1152191 := bstep (se 1 (by rfl) ⟨864143, by rfl⟩ : syracuseStep 1152191 = 1728287) B1728287
theorem B2922311 : Blo 682313 2922311 := bstep (se 1 (by rfl) ⟨2191733, by rfl⟩ : syracuseStep 2922311 = 4383467) B4383467
theorem B2922911 : Blo 682313 2922911 := bstep (se 1 (by rfl) ⟨2192183, by rfl⟩ : syracuseStep 2922911 = 4384367) B4384367
theorem B4168415 : Blo 682313 4168415 := bstep (se 1 (by rfl) ⟨3126311, by rfl⟩ : syracuseStep 4168415 = 6252623) B6252623
theorem B49978295 : Blo 682313 49978295 := bstep (se 1 (by rfl) ⟨37483721, by rfl⟩ : syracuseStep 49978295 = 74967443) B74967443
theorem B2595833 : Blo 682313 2595833 := bstep (se 2 (by rfl) ⟨973437, by rfl⟩ : syracuseStep 2595833 = 1946875) B1946875
theorem B3906575 : Blo 682313 3906575 := bstep (se 1 (by rfl) ⟨2929931, by rfl⟩ : syracuseStep 3906575 = 5859863) B5859863
theorem B5184647 : Blo 682313 5184647 := bstep (se 1 (by rfl) ⟨3888485, by rfl⟩ : syracuseStep 5184647 = 7776971) B7776971
theorem B1023599 : Blo 682313 1023599 := bstep (se 1 (by rfl) ⟨767699, by rfl⟩ : syracuseStep 1023599 = 1535399) B1535399
theorem B1023719 : Blo 682313 1023719 := bstep (se 1 (by rfl) ⟨767789, by rfl⟩ : syracuseStep 1023719 = 1535579) B1535579
theorem B1023995 : Blo 682313 1023995 := bstep (se 1 (by rfl) ⟨767996, by rfl⟩ : syracuseStep 1023995 = 1535993) B1535993
theorem B1024055 : Blo 682313 1024055 := bstep (se 1 (by rfl) ⟨768041, by rfl⟩ : syracuseStep 1024055 = 1536083) B1536083
theorem B1155127 : Blo 682313 1155127 := bstep (se 1 (by rfl) ⟨866345, by rfl⟩ : syracuseStep 1155127 = 1732691) B1732691
theorem B1024175 : Blo 682313 1024175 := bstep (se 1 (by rfl) ⟨768131, by rfl⟩ : syracuseStep 1024175 = 1536263) B1536263
theorem B1024379 : Blo 682313 1024379 := bstep (se 1 (by rfl) ⟨768284, by rfl⟩ : syracuseStep 1024379 = 1536569) B1536569
theorem B2597291 : Blo 682313 2597291 := bstep (se 1 (by rfl) ⟨1947968, by rfl⟩ : syracuseStep 2597291 = 3895937) B3895937
theorem B1024553 : Blo 682313 1024553 := bstep (se 2 (by rfl) ⟨384207, by rfl⟩ : syracuseStep 1024553 = 768415) B768415
theorem B1647145 : Blo 682313 1647145 := bstep (se 2 (by rfl) ⟨617679, by rfl⟩ : syracuseStep 1647145 = 1235359) B1235359
theorem B1024649 : Blo 682313 1024649 := bstep (se 2 (by rfl) ⟨384243, by rfl⟩ : syracuseStep 1024649 = 768487) B768487
theorem B1024859 : Blo 682313 1024859 := bstep (se 1 (by rfl) ⟨768644, by rfl⟩ : syracuseStep 1024859 = 1537289) B1537289
theorem B1024895 : Blo 682313 1024895 := bstep (se 1 (by rfl) ⟨768671, by rfl⟩ : syracuseStep 1024895 = 1537343) B1537343
theorem B1024967 : Blo 682313 1024967 := bstep (se 1 (by rfl) ⟨768725, by rfl⟩ : syracuseStep 1024967 = 1537451) B1537451
theorem B1025183 : Blo 682313 1025183 := bstep (se 1 (by rfl) ⟨768887, by rfl⟩ : syracuseStep 1025183 = 1537775) B1537775
theorem B1025327 : Blo 682313 1025327 := bstep (se 1 (by rfl) ⟨768995, by rfl⟩ : syracuseStep 1025327 = 1537991) B1537991
theorem B1025519 : Blo 682313 1025519 := bstep (se 1 (by rfl) ⟨769139, by rfl⟩ : syracuseStep 1025519 = 1538279) B1538279
theorem B1025531 : Blo 682313 1025531 := bstep (se 1 (by rfl) ⟨769148, by rfl⟩ : syracuseStep 1025531 = 1538297) B1538297
theorem B1025567 : Blo 682313 1025567 := bstep (se 1 (by rfl) ⟨769175, by rfl⟩ : syracuseStep 1025567 = 1538351) B1538351
theorem B1156639 : Blo 682313 1156639 := bstep (se 1 (by rfl) ⟨867479, by rfl⟩ : syracuseStep 1156639 = 1734959) B1734959
theorem B1025711 : Blo 682313 1025711 := bstep (se 1 (by rfl) ⟨769283, by rfl⟩ : syracuseStep 1025711 = 1538567) B1538567
theorem B1025801 : Blo 682313 1025801 := bstep (se 2 (by rfl) ⟨384675, by rfl⟩ : syracuseStep 1025801 = 769351) B769351
theorem B1025831 : Blo 682313 1025831 := bstep (se 1 (by rfl) ⟨769373, by rfl⟩ : syracuseStep 1025831 = 1538747) B1538747
theorem B2303801 : Blo 682313 2303801 := bstep (se 2 (by rfl) ⟨863925, by rfl⟩ : syracuseStep 2303801 = 1727851) B1727851
theorem B2107291 : Blo 682313 2107291 := bstep (se 1 (by rfl) ⟨1580468, by rfl⟩ : syracuseStep 2107291 = 3160937) B3160937
theorem B1026431 : Blo 682313 1026431 := bstep (se 1 (by rfl) ⟨769823, by rfl⟩ : syracuseStep 1026431 = 1539647) B1539647
theorem B7383433 : Blo 682313 7383433 := bstep (se 2 (by rfl) ⟨2768787, by rfl⟩ : syracuseStep 7383433 = 5537575) B5537575
theorem B1026671 : Blo 682313 1026671 := bstep (se 1 (by rfl) ⟨770003, by rfl⟩ : syracuseStep 1026671 = 1540007) B1540007
theorem B2304665 : Blo 682313 2304665 := bstep (se 2 (by rfl) ⟨864249, by rfl⟩ : syracuseStep 2304665 = 1728499) B1728499
theorem B1026887 : Blo 682313 1026887 := bstep (se 1 (by rfl) ⟨770165, by rfl⟩ : syracuseStep 1026887 = 1540331) B1540331
theorem B70921079 : Blo 682313 70921079 := bstep (se 1 (by rfl) ⟨53190809, by rfl⟩ : syracuseStep 70921079 = 106381619) B106381619
theorem B13348151 : Blo 682313 13348151 := bstep (se 1 (by rfl) ⟨10011113, by rfl⟩ : syracuseStep 13348151 = 20022227) B20022227
theorem B6761861 : Blo 682313 6761861 := bstep (se 4 (by rfl) ⟨633924, by rfl⟩ : syracuseStep 6761861 = 1267849) B1267849
theorem B1027487 : Blo 682313 1027487 := bstep (se 1 (by rfl) ⟨770615, by rfl⟩ : syracuseStep 1027487 = 1541231) B1541231
theorem B7810505 : Blo 682313 7810505 := bstep (se 2 (by rfl) ⟨2928939, by rfl⟩ : syracuseStep 7810505 = 5857879) B5857879
theorem B1093151 : Blo 682313 1093151 := bstep (se 1 (by rfl) ⟨819863, by rfl⟩ : syracuseStep 1093151 = 1639727) B1639727
theorem B1027751 : Blo 682313 1027751 := bstep (se 1 (by rfl) ⟨770813, by rfl⟩ : syracuseStep 1027751 = 1541627) B1541627
theorem B1027775 : Blo 682313 1027775 := bstep (se 1 (by rfl) ⟨770831, by rfl⟩ : syracuseStep 1027775 = 1541663) B1541663
theorem B1027871 : Blo 682313 1027871 := bstep (se 1 (by rfl) ⟨770903, by rfl⟩ : syracuseStep 1027871 = 1541807) B1541807
theorem B8007497 : Blo 682313 8007497 := bstep (se 2 (by rfl) ⟨3002811, by rfl⟩ : syracuseStep 8007497 = 6005623) B6005623
theorem B1028159 : Blo 682313 1028159 := bstep (se 1 (by rfl) ⟨771119, by rfl⟩ : syracuseStep 1028159 = 1542239) B1542239
theorem B2601193 : Blo 682313 2601193 := bstep (se 2 (by rfl) ⟨975447, by rfl⟩ : syracuseStep 2601193 = 1950895) B1950895
theorem B1028351 : Blo 682313 1028351 := bstep (se 1 (by rfl) ⟨771263, by rfl⟩ : syracuseStep 1028351 = 1542527) B1542527
theorem B1028393 : Blo 682313 1028393 := bstep (se 2 (by rfl) ⟨385647, by rfl⟩ : syracuseStep 1028393 = 771295) B771295
theorem B1028663 : Blo 682313 1028663 := bstep (se 1 (by rfl) ⟨771497, by rfl⟩ : syracuseStep 1028663 = 1542995) B1542995
theorem B16659047 : Blo 682313 16659047 := bstep (se 1 (by rfl) ⟨12494285, by rfl⟩ : syracuseStep 16659047 = 24988571) B24988571
theorem B2306717 : Blo 682313 2306717 := bstep (se 3 (by rfl) ⟨432509, by rfl⟩ : syracuseStep 2306717 = 865019) B865019
theorem B2306825 : Blo 682313 2306825 := bstep (se 2 (by rfl) ⟨865059, by rfl⟩ : syracuseStep 2306825 = 1730119) B1730119
theorem B1028903 : Blo 682313 1028903 := bstep (se 1 (by rfl) ⟨771677, by rfl⟩ : syracuseStep 1028903 = 1543355) B1543355
theorem B1029023 : Blo 682313 1029023 := bstep (se 1 (by rfl) ⟨771767, by rfl⟩ : syracuseStep 1029023 = 1543535) B1543535
theorem B5846093 : Blo 682313 5846093 := bstep (se 3 (by rfl) ⟨1096142, by rfl⟩ : syracuseStep 5846093 = 2192285) B2192285
theorem B2307257 : Blo 682313 2307257 := bstep (se 2 (by rfl) ⟨865221, by rfl⟩ : syracuseStep 2307257 = 1730443) B1730443
theorem B1947091 : Blo 682313 1947091 := bstep (se 1 (by rfl) ⟨1460318, by rfl⟩ : syracuseStep 1947091 = 2920637) B2920637
theorem B865819 : Blo 682313 865819 := bstep (se 1 (by rfl) ⟨649364, by rfl⟩ : syracuseStep 865819 = 1298729) B1298729
theorem B767695 : Blo 682313 767695 := bstep (se 1 (by rfl) ⟨575771, by rfl⟩ : syracuseStep 767695 = 1151543) B1151543
theorem B14005993 : Blo 682313 14005993 := bstep (se 2 (by rfl) ⟨5252247, by rfl⟩ : syracuseStep 14005993 = 10504495) B10504495
theorem B1095547 : Blo 682313 1095547 := bstep (se 1 (by rfl) ⟨821660, by rfl⟩ : syracuseStep 1095547 = 1643321) B1643321
theorem B2930975 : Blo 682313 2930975 := bstep (se 1 (by rfl) ⟨2198231, by rfl⟩ : syracuseStep 2930975 = 4396463) B4396463
theorem B866791 : Blo 682313 866791 := bstep (se 1 (by rfl) ⟨650093, by rfl⟩ : syracuseStep 866791 = 1300187) B1300187
theorem B1948151 : Blo 682313 1948151 := bstep (se 1 (by rfl) ⟨1461113, by rfl⟩ : syracuseStep 1948151 = 2922227) B2922227
theorem B768559 : Blo 682313 768559 := bstep (se 1 (by rfl) ⟨576419, by rfl⟩ : syracuseStep 768559 = 1152839) B1152839
theorem B3521207 : Blo 682313 3521207 := bstep (se 1 (by rfl) ⟨2640905, by rfl⟩ : syracuseStep 3521207 = 5281811) B5281811
theorem B3455945 : Blo 682313 3455945 := bstep (se 2 (by rfl) ⟨1295979, by rfl⟩ : syracuseStep 3455945 = 2591959) B2591959
theorem B1096687 : Blo 682313 1096687 := bstep (se 1 (by rfl) ⟨822515, by rfl⟩ : syracuseStep 1096687 = 1645031) B1645031
theorem B1096777 : Blo 682313 1096777 := bstep (se 2 (by rfl) ⟨411291, by rfl⟩ : syracuseStep 1096777 = 822583) B822583
theorem B2309255 : Blo 682313 2309255 := bstep (se 1 (by rfl) ⟨1731941, by rfl⟩ : syracuseStep 2309255 = 3463883) B3463883
theorem B2309417 : Blo 682313 2309417 := bstep (se 2 (by rfl) ⟨866031, by rfl⟩ : syracuseStep 2309417 = 1732063) B1732063
theorem B3292751 : Blo 682313 3292751 := bstep (se 1 (by rfl) ⟨2469563, by rfl⟩ : syracuseStep 3292751 = 4939127) B4939127
theorem B7814879 : Blo 682313 7814879 := bstep (se 1 (by rfl) ⟨5861159, by rfl⟩ : syracuseStep 7814879 = 11722319) B11722319
theorem B3326035 : Blo 682313 3326035 := bstep (se 1 (by rfl) ⟨2494526, by rfl⟩ : syracuseStep 3326035 = 4989053) B4989053
theorem B2310875 : Blo 682313 2310875 := bstep (se 1 (by rfl) ⟨1733156, by rfl⟩ : syracuseStep 2310875 = 3466313) B3466313
theorem B1000775 : Blo 682313 1000775 := bstep (se 1 (by rfl) ⟨750581, by rfl⟩ : syracuseStep 1000775 = 1501163) B1501163
theorem B1951067 : Blo 682313 1951067 := bstep (se 1 (by rfl) ⟨1463300, by rfl⟩ : syracuseStep 1951067 = 2926601) B2926601
theorem B4376855 : Blo 682313 4376855 := bstep (se 1 (by rfl) ⟨3282641, by rfl⟩ : syracuseStep 4376855 = 6565283) B6565283
theorem B4377007 : Blo 682313 4377007 := bstep (se 1 (by rfl) ⟨3282755, by rfl⟩ : syracuseStep 4377007 = 6565511) B6565511
theorem B18729605 : Blo 682313 18729605 := bstep (se 4 (by rfl) ⟨1755900, by rfl⟩ : syracuseStep 18729605 = 3511801) B3511801
theorem B3459833 : Blo 682313 3459833 := bstep (se 2 (by rfl) ⟨1297437, by rfl⟩ : syracuseStep 3459833 = 2594875) B2594875
theorem B44518571 : Blo 682313 44518571 := bstep (se 1 (by rfl) ⟨33388928, by rfl⟩ : syracuseStep 44518571 = 66777857) B66777857
theorem B112283009 : Blo 682313 112283009 := bstep (se 2 (by rfl) ⟨42106128, by rfl⟩ : syracuseStep 112283009 = 84212257) B84212257
theorem B4935205 : Blo 682313 4935205 := bstep (se 4 (by rfl) ⟨462675, by rfl⟩ : syracuseStep 4935205 = 925351) B925351
theorem B1756991 : Blo 682313 1756991 := bstep (se 1 (by rfl) ⟨1317743, by rfl⟩ : syracuseStep 1756991 = 2635487) B2635487
theorem B31674185 : Blo 682313 31674185 := bstep (se 2 (by rfl) ⟨11877819, by rfl⟩ : syracuseStep 31674185 = 23755639) B23755639
theorem B17977243 : Blo 682313 17977243 := bstep (se 1 (by rfl) ⟨13482932, by rfl⟩ : syracuseStep 17977243 = 26965865) B26965865
theorem B8310995 : Blo 682313 8310995 := bstep (se 1 (by rfl) ⟨6233246, by rfl⟩ : syracuseStep 8310995 = 12466493) B12466493
theorem B4379777 : Blo 682313 4379777 := bstep (se 2 (by rfl) ⟨1642416, by rfl⟩ : syracuseStep 4379777 = 3284833) B3284833
theorem B59954417 : Blo 682313 59954417 := bstep (se 2 (by rfl) ⟨22482906, by rfl⟩ : syracuseStep 59954417 = 44965813) B44965813
theorem B1463599 : Blo 682313 1463599 := bstep (se 1 (by rfl) ⟨1097699, by rfl⟩ : syracuseStep 1463599 = 2195399) B2195399
theorem B3692063 : Blo 682313 3692063 := bstep (se 1 (by rfl) ⟨2769047, by rfl⟩ : syracuseStep 3692063 = 5538095) B5538095
theorem B4446089 : Blo 682313 4446089 := bstep (se 2 (by rfl) ⟨1667283, by rfl⟩ : syracuseStep 4446089 = 3334567) B3334567
theorem B168450191 : Blo 682313 168450191 := bstep (se 1 (by rfl) ⟨126337643, by rfl⟩ : syracuseStep 168450191 = 252675287) B252675287
theorem B3889853 : Blo 682313 3889853 := bstep (se 3 (by rfl) ⟨729347, by rfl⟩ : syracuseStep 3889853 = 1458695) B1458695
theorem B4152259 : Blo 682313 4152259 := bstep (se 1 (by rfl) ⟨3114194, by rfl⟩ : syracuseStep 4152259 = 6228389) B6228389
theorem B2776169 : Blo 682313 2776169 := bstep (se 2 (by rfl) ⟨1041063, by rfl⟩ : syracuseStep 2776169 = 2082127) B2082127
theorem B2776313 : Blo 682313 2776313 := bstep (se 2 (by rfl) ⟨1041117, by rfl⟩ : syracuseStep 2776313 = 2082235) B2082235
theorem B1465769 : Blo 682313 1465769 := bstep (se 2 (by rfl) ⟨549663, by rfl⟩ : syracuseStep 1465769 = 1099327) B1099327
theorem B1662527 : Blo 682313 1662527 := bstep (se 1 (by rfl) ⟨1246895, by rfl⟩ : syracuseStep 1662527 = 2493791) B2493791
theorem B1728479 : Blo 682313 1728479 := bstep (se 1 (by rfl) ⟨1296359, by rfl⟩ : syracuseStep 1728479 = 2592719) B2592719
theorem B7004227 : Blo 682313 7004227 := bstep (se 1 (by rfl) ⟨5253170, by rfl⟩ : syracuseStep 7004227 = 10506341) B10506341
theorem B2187479 : Blo 682313 2187479 := bstep (se 1 (by rfl) ⟨1640609, by rfl⟩ : syracuseStep 2187479 = 3281219) B3281219
theorem B975083 : Blo 682313 975083 := bstep (se 1 (by rfl) ⟨731312, by rfl⟩ : syracuseStep 975083 = 1462625) B1462625
theorem B1171751 : Blo 682313 1171751 := bstep (se 1 (by rfl) ⟨878813, by rfl⟩ : syracuseStep 1171751 = 1757627) B1757627
theorem B4219715 : Blo 682313 4219715 := bstep (se 1 (by rfl) ⟨3164786, by rfl⟩ : syracuseStep 4219715 = 6329573) B6329573
theorem B976063 : Blo 682313 976063 := bstep (se 1 (by rfl) ⟨732047, by rfl⟩ : syracuseStep 976063 = 1464095) B1464095
theorem B3893021 : Blo 682313 3893021 := bstep (se 3 (by rfl) ⟨729941, by rfl⟩ : syracuseStep 3893021 = 1459883) B1459883
theorem B2189119 : Blo 682313 2189119 := bstep (se 1 (by rfl) ⟨1641839, by rfl⟩ : syracuseStep 2189119 = 3283679) B3283679
theorem B3860303 : Blo 682313 3860303 := bstep (se 1 (by rfl) ⟨2895227, by rfl⟩ : syracuseStep 3860303 = 5790455) B5790455
theorem B682471 : Blo 682313 682471 := bstep (se 1 (by rfl) ⟨511853, by rfl⟩ : syracuseStep 682471 = 1023707) B1023707
theorem B13330919 : Blo 682313 13330919 := bstep (se 1 (by rfl) ⟨9998189, by rfl⟩ : syracuseStep 13330919 = 19996379) B19996379
theorem B168487559 : Blo 682313 168487559 := bstep (se 1 (by rfl) ⟨126365669, by rfl⟩ : syracuseStep 168487559 = 252731339) B252731339
theorem B682651 : Blo 682313 682651 := bstep (se 1 (by rfl) ⟨511988, by rfl⟩ : syracuseStep 682651 = 1023977) B1023977
theorem B8776673 : Blo 682313 8776673 := bstep (se 2 (by rfl) ⟨3291252, by rfl⟩ : syracuseStep 8776673 = 6582505) B6582505
theorem B683119 : Blo 682313 683119 := bstep (se 1 (by rfl) ⟨512339, by rfl⟩ : syracuseStep 683119 = 1024679) B1024679
theorem B683199 : Blo 682313 683199 := bstep (se 1 (by rfl) ⟨512399, by rfl⟩ : syracuseStep 683199 = 1024799) B1024799
theorem B683215 : Blo 682313 683215 := bstep (se 1 (by rfl) ⟨512411, by rfl⟩ : syracuseStep 683215 = 1024823) B1024823
theorem B7990595 : Blo 682313 7990595 := bstep (se 1 (by rfl) ⟨5992946, by rfl⟩ : syracuseStep 7990595 = 11985893) B11985893
theorem B683335 : Blo 682313 683335 := bstep (se 1 (by rfl) ⟨512501, by rfl⟩ : syracuseStep 683335 = 1025003) B1025003
theorem B2191067 : Blo 682313 2191067 := bstep (se 1 (by rfl) ⟨1643300, by rfl⟩ : syracuseStep 2191067 = 3286601) B3286601
theorem B684063 : Blo 682313 684063 := bstep (se 1 (by rfl) ⟨513047, by rfl⟩ : syracuseStep 684063 = 1026095) B1026095
theorem B3469391 : Blo 682313 3469391 := bstep (se 1 (by rfl) ⟨2602043, by rfl⟩ : syracuseStep 3469391 = 5204087) B5204087
theorem B71233667 : Blo 682313 71233667 := bstep (se 1 (by rfl) ⟨53425250, by rfl⟩ : syracuseStep 71233667 = 106850501) B106850501
theorem B684239 : Blo 682313 684239 := bstep (se 1 (by rfl) ⟨513179, by rfl⟩ : syracuseStep 684239 = 1026359) B1026359
theorem B1732823 : Blo 682313 1732823 := bstep (se 1 (by rfl) ⟨1299617, by rfl⟩ : syracuseStep 1732823 = 2599235) B2599235
theorem B684359 : Blo 682313 684359 := bstep (se 1 (by rfl) ⟨513269, by rfl⟩ : syracuseStep 684359 = 1026539) B1026539
theorem B684827 : Blo 682313 684827 := bstep (se 1 (by rfl) ⟨513620, by rfl⟩ : syracuseStep 684827 = 1027241) B1027241
theorem B3699593 : Blo 682313 3699593 := bstep (se 2 (by rfl) ⟨1387347, by rfl⟩ : syracuseStep 3699593 = 2774695) B2774695
theorem B685103 : Blo 682313 685103 := bstep (se 1 (by rfl) ⟨513827, by rfl⟩ : syracuseStep 685103 = 1027655) B1027655
theorem B4158535 : Blo 682313 4158535 := bstep (se 1 (by rfl) ⟨3118901, by rfl⟩ : syracuseStep 4158535 = 6237803) B6237803
theorem B1537145 : Blo 682313 1537145 := bstep (se 2 (by rfl) ⟨576429, by rfl⟩ : syracuseStep 1537145 = 1152859) B1152859
theorem B6255755 : Blo 682313 6255755 := bstep (se 1 (by rfl) ⟨4691816, by rfl⟩ : syracuseStep 6255755 = 9383633) B9383633
theorem B685223 : Blo 682313 685223 := bstep (se 1 (by rfl) ⟨513917, by rfl⟩ : syracuseStep 685223 = 1027835) B1027835
theorem B12154049 : Blo 682313 12154049 := bstep (se 2 (by rfl) ⟨4557768, by rfl⟩ : syracuseStep 12154049 = 9115537) B9115537
theorem B5535215 : Blo 682313 5535215 := bstep (se 1 (by rfl) ⟨4151411, by rfl⟩ : syracuseStep 5535215 = 8302823) B8302823
theorem B685671 : Blo 682313 685671 := bstep (se 1 (by rfl) ⟨514253, by rfl⟩ : syracuseStep 685671 = 1028507) B1028507
theorem B4388489 : Blo 682313 4388489 := bstep (se 2 (by rfl) ⟨1645683, by rfl⟩ : syracuseStep 4388489 = 3291367) B3291367
theorem B2225951 : Blo 682313 2225951 := bstep (se 1 (by rfl) ⟨1669463, by rfl⟩ : syracuseStep 2225951 = 3338927) B3338927
theorem B3700541 : Blo 682313 3700541 := bstep (se 3 (by rfl) ⟨693851, by rfl⟩ : syracuseStep 3700541 = 1387703) B1387703
theorem B1537919 : Blo 682313 1537919 := bstep (se 1 (by rfl) ⟨1153439, by rfl⟩ : syracuseStep 1537919 = 2306879) B2306879
theorem B685951 : Blo 682313 685951 := bstep (se 1 (by rfl) ⟨514463, by rfl⟩ : syracuseStep 685951 = 1028927) B1028927
theorem B686047 : Blo 682313 686047 := bstep (se 1 (by rfl) ⟨514535, by rfl⟩ : syracuseStep 686047 = 1029071) B1029071
theorem B686075 : Blo 682313 686075 := bstep (se 1 (by rfl) ⟨514556, by rfl⟩ : syracuseStep 686075 = 1029113) B1029113
theorem B686107 : Blo 682313 686107 := bstep (se 1 (by rfl) ⟨514580, by rfl⟩ : syracuseStep 686107 = 1029161) B1029161
theorem B686127 : Blo 682313 686127 := bstep (se 1 (by rfl) ⟨514595, by rfl⟩ : syracuseStep 686127 = 1029191) B1029191
theorem B686247 : Blo 682313 686247 := bstep (se 1 (by rfl) ⟨514685, by rfl⟩ : syracuseStep 686247 = 1029371) B1029371
theorem B1538387 : Blo 682313 1538387 := bstep (se 1 (by rfl) ⟨1153790, by rfl⟩ : syracuseStep 1538387 = 2307581) B2307581
theorem B1538927 : Blo 682313 1538927 := bstep (se 1 (by rfl) ⟨1154195, by rfl⟩ : syracuseStep 1538927 = 2308391) B2308391
theorem B3898601 : Blo 682313 3898601 := bstep (se 2 (by rfl) ⟨1461975, by rfl⟩ : syracuseStep 3898601 = 2923951) B2923951
theorem B19004669 : Blo 682313 19004669 := bstep (se 3 (by rfl) ⟨3563375, by rfl⟩ : syracuseStep 19004669 = 7126751) B7126751
theorem B1539575 : Blo 682313 1539575 := bstep (se 1 (by rfl) ⟨1154681, by rfl⟩ : syracuseStep 1539575 = 2309363) B2309363
theorem B1540169 : Blo 682313 1540169 := bstep (se 2 (by rfl) ⟨577563, by rfl⟩ : syracuseStep 1540169 = 1155127) B1155127
theorem B9338969 : Blo 682313 9338969 := bstep (se 2 (by rfl) ⟨3502113, by rfl⟩ : syracuseStep 9338969 = 7004227) B7004227
theorem B1540583 : Blo 682313 1540583 := bstep (se 1 (by rfl) ⟨1155437, by rfl⟩ : syracuseStep 1540583 = 2310875) B2310875
theorem B2196193 : Blo 682313 2196193 := bstep (se 2 (by rfl) ⟨823572, by rfl⟩ : syracuseStep 2196193 = 1647145) B1647145
theorem B2917903 : Blo 682313 2917903 := bstep (se 1 (by rfl) ⟨2188427, by rfl⟩ : syracuseStep 2917903 = 4376855) B4376855
theorem B12486403 : Blo 682313 12486403 := bstep (se 1 (by rfl) ⟨9364802, by rfl⟩ : syracuseStep 12486403 = 18729605) B18729605
theorem B1542185 : Blo 682313 1542185 := bstep (se 2 (by rfl) ⟨578319, by rfl⟩ : syracuseStep 1542185 = 1156639) B1156639
theorem B2918825 : Blo 682313 2918825 := bstep (se 2 (by rfl) ⟨1094559, by rfl⟩ : syracuseStep 2918825 = 2189119) B2189119
theorem B5540663 : Blo 682313 5540663 := bstep (se 1 (by rfl) ⟨4155497, by rfl⟩ : syracuseStep 5540663 = 8310995) B8310995
theorem B5836009 : Blo 682313 5836009 := bstep (se 2 (by rfl) ⟨2188503, by rfl⟩ : syracuseStep 5836009 = 4377007) B4377007
theorem B2919851 : Blo 682313 2919851 := bstep (se 1 (by rfl) ⟨2189888, by rfl⟩ : syracuseStep 2919851 = 4379777) B4379777
theorem B2461375 : Blo 682313 2461375 := bstep (se 1 (by rfl) ⟨1846031, by rfl⟩ : syracuseStep 2461375 = 3692063) B3692063
theorem B112300127 : Blo 682313 112300127 := bstep (se 1 (by rfl) ⟨84225095, by rfl⟩ : syracuseStep 112300127 = 168450191) B168450191
theorem B2593235 : Blo 682313 2593235 := bstep (se 1 (by rfl) ⟨1944926, by rfl⟩ : syracuseStep 2593235 = 3889853) B3889853
theorem B10294141 : Blo 682313 10294141 := bstep (se 3 (by rfl) ⟨1930151, by rfl⟩ : syracuseStep 10294141 = 3860303) B3860303
theorem B1152319 : Blo 682313 1152319 := bstep (se 1 (by rfl) ⟨864239, by rfl⟩ : syracuseStep 1152319 = 1728479) B1728479
theorem B2103545 : Blo 682313 2103545 := bstep (se 2 (by rfl) ⟨788829, by rfl⟩ : syracuseStep 2103545 = 1577659) B1577659
theorem B2595347 : Blo 682313 2595347 := bstep (se 1 (by rfl) ⟨1946510, by rfl⟩ : syracuseStep 2595347 = 3893021) B3893021
theorem B5544713 : Blo 682313 5544713 := bstep (se 2 (by rfl) ⟨2079267, by rfl⟩ : syracuseStep 5544713 = 4158535) B4158535
theorem B2596121 : Blo 682313 2596121 := bstep (se 2 (by rfl) ⟨973545, by rfl⟩ : syracuseStep 2596121 = 1947091) B1947091
theorem B1154425 : Blo 682313 1154425 := bstep (se 2 (by rfl) ⟨432909, by rfl⟩ : syracuseStep 1154425 = 865819) B865819
theorem B1023593 : Blo 682313 1023593 := bstep (se 2 (by rfl) ⟨383847, by rfl⟩ : syracuseStep 1023593 = 767695) B767695
theorem B728767 : Blo 682313 728767 := bstep (se 1 (by rfl) ⟨546575, by rfl⟩ : syracuseStep 728767 = 1093151) B1093151
theorem B47489111 : Blo 682313 47489111 := bstep (se 1 (by rfl) ⟨35616833, by rfl⟩ : syracuseStep 47489111 = 71233667) B71233667
theorem B1155215 : Blo 682313 1155215 := bstep (se 1 (by rfl) ⟨866411, by rfl⟩ : syracuseStep 1155215 = 1732823) B1732823
theorem B2466395 : Blo 682313 2466395 := bstep (se 1 (by rfl) ⟨1849796, by rfl⟩ : syracuseStep 2466395 = 3699593) B3699593
theorem B1155721 : Blo 682313 1155721 := bstep (se 2 (by rfl) ⟨433395, by rfl⟩ : syracuseStep 1155721 = 866791) B866791
theorem B1024745 : Blo 682313 1024745 := bstep (se 2 (by rfl) ⟨384279, by rfl⟩ : syracuseStep 1024745 = 768559) B768559
theorem B1024763 : Blo 682313 1024763 := bstep (se 1 (by rfl) ⟨768572, by rfl⟩ : syracuseStep 1024763 = 1537145) B1537145
theorem B4170503 : Blo 682313 4170503 := bstep (se 1 (by rfl) ⟨3127877, by rfl⟩ : syracuseStep 4170503 = 6255755) B6255755
theorem B8102699 : Blo 682313 8102699 := bstep (se 1 (by rfl) ⟨6077024, by rfl⟩ : syracuseStep 8102699 = 12154049) B12154049
theorem B2925659 : Blo 682313 2925659 := bstep (se 1 (by rfl) ⟨2194244, by rfl⟩ : syracuseStep 2925659 = 4388489) B4388489
theorem B1483967 : Blo 682313 1483967 := bstep (se 1 (by rfl) ⟨1112975, by rfl⟩ : syracuseStep 1483967 = 2225951) B2225951
theorem B2467027 : Blo 682313 2467027 := bstep (se 1 (by rfl) ⟨1850270, by rfl⟩ : syracuseStep 2467027 = 3700541) B3700541
theorem B1025279 : Blo 682313 1025279 := bstep (se 1 (by rfl) ⟨768959, by rfl⟩ : syracuseStep 1025279 = 1537919) B1537919
theorem B1025591 : Blo 682313 1025591 := bstep (se 1 (by rfl) ⟨769193, by rfl⟩ : syracuseStep 1025591 = 1538387) B1538387
theorem B1025951 : Blo 682313 1025951 := bstep (se 1 (by rfl) ⟨769463, by rfl⟩ : syracuseStep 1025951 = 1538927) B1538927
theorem B2303963 : Blo 682313 2303963 := bstep (se 1 (by rfl) ⟨1727972, by rfl⟩ : syracuseStep 2303963 = 3455945) B3455945
theorem B2599067 : Blo 682313 2599067 := bstep (se 1 (by rfl) ⟨1949300, by rfl⟩ : syracuseStep 2599067 = 3898601) B3898601
theorem B1026383 : Blo 682313 1026383 := bstep (se 1 (by rfl) ⟨769787, by rfl⟩ : syracuseStep 1026383 = 1539575) B1539575
theorem B1026815 : Blo 682313 1026815 := bstep (se 1 (by rfl) ⟨770111, by rfl⟩ : syracuseStep 1026815 = 1540223) B1540223
theorem B4434713 : Blo 682313 4434713 := bstep (se 2 (by rfl) ⟨1663017, by rfl⟩ : syracuseStep 4434713 = 3326035) B3326035
theorem B2600221 : Blo 682313 2600221 := bstep (se 3 (by rfl) ⟨487541, by rfl⟩ : syracuseStep 2600221 = 975083) B975083
theorem B3124669 : Blo 682313 3124669 := bstep (se 3 (by rfl) ⟨585875, by rfl⟩ : syracuseStep 3124669 = 1171751) B1171751
theorem B1945063 : Blo 682313 1945063 := bstep (se 1 (by rfl) ⟨1458797, by rfl⟩ : syracuseStep 1945063 = 2917595) B2917595
theorem B1027919 : Blo 682313 1027919 := bstep (se 1 (by rfl) ⟨770939, by rfl⟩ : syracuseStep 1027919 = 1541879) B1541879
theorem B1028039 : Blo 682313 1028039 := bstep (se 1 (by rfl) ⟨771029, by rfl⟩ : syracuseStep 1028039 = 1542059) B1542059
theorem B1028399 : Blo 682313 1028399 := bstep (se 1 (by rfl) ⟨771299, by rfl⟩ : syracuseStep 1028399 = 1542599) B1542599
theorem B2306555 : Blo 682313 2306555 := bstep (se 1 (by rfl) ⟨1729916, by rfl⟩ : syracuseStep 2306555 = 3459833) B3459833
theorem B2601467 : Blo 682313 2601467 := bstep (se 1 (by rfl) ⟨1951100, by rfl⟩ : syracuseStep 2601467 = 3902201) B3902201
theorem B1028639 : Blo 682313 1028639 := bstep (se 1 (by rfl) ⟨771479, by rfl⟩ : syracuseStep 1028639 = 1542959) B1542959
theorem B134787635 : Blo 682313 134787635 := bstep (se 1 (by rfl) ⟨101090726, by rfl⟩ : syracuseStep 134787635 = 202181453) B202181453
theorem B1028987 : Blo 682313 1028987 := bstep (se 1 (by rfl) ⟨771740, by rfl⟩ : syracuseStep 1028987 = 1543481) B1543481
theorem B74855339 : Blo 682313 74855339 := bstep (se 1 (by rfl) ⟨56141504, by rfl⟩ : syracuseStep 74855339 = 112283009) B112283009
theorem B1029167 : Blo 682313 1029167 := bstep (se 1 (by rfl) ⟨771875, by rfl⟩ : syracuseStep 1029167 = 1543751) B1543751
theorem B1029287 : Blo 682313 1029287 := bstep (se 1 (by rfl) ⟨771965, by rfl⟩ : syracuseStep 1029287 = 1543931) B1543931
theorem B21116123 : Blo 682313 21116123 := bstep (se 1 (by rfl) ⟨15837092, by rfl⟩ : syracuseStep 21116123 = 31674185) B31674185
theorem B1029431 : Blo 682313 1029431 := bstep (se 1 (by rfl) ⟨772073, by rfl⟩ : syracuseStep 1029431 = 1544147) B1544147
theorem B9844577 : Blo 682313 9844577 := bstep (se 2 (by rfl) ⟨3691716, by rfl⟩ : syracuseStep 9844577 = 7383433) B7383433
theorem B768127 : Blo 682313 768127 := bstep (se 1 (by rfl) ⟨576095, by rfl⟩ : syracuseStep 768127 = 1152191) B1152191
theorem B2668733 : Blo 682313 2668733 := bstep (se 3 (by rfl) ⟨500387, by rfl⟩ : syracuseStep 2668733 = 1000775) B1000775
theorem B1948207 : Blo 682313 1948207 := bstep (se 1 (by rfl) ⟨1461155, by rfl⟩ : syracuseStep 1948207 = 2922311) B2922311
theorem B2964059 : Blo 682313 2964059 := bstep (se 1 (by rfl) ⟨2223044, by rfl⟩ : syracuseStep 2964059 = 4446089) B4446089
theorem B1948607 : Blo 682313 1948607 := bstep (se 1 (by rfl) ⟨1461455, by rfl⟩ : syracuseStep 1948607 = 2922911) B2922911
theorem B2604383 : Blo 682313 2604383 := bstep (se 1 (by rfl) ⟨1953287, by rfl⟩ : syracuseStep 2604383 = 3906575) B3906575
theorem B1850779 : Blo 682313 1850779 := bstep (se 1 (by rfl) ⟨1388084, by rfl⟩ : syracuseStep 1850779 = 2776169) B2776169
theorem B3456431 : Blo 682313 3456431 := bstep (se 1 (by rfl) ⟨2592323, by rfl⟩ : syracuseStep 3456431 = 5184647) B5184647
theorem B23969657 : Blo 682313 23969657 := bstep (se 2 (by rfl) ⟨8988621, by rfl⟩ : syracuseStep 23969657 = 17977243) B17977243
theorem B1458319 : Blo 682313 1458319 := bstep (se 1 (by rfl) ⟨1093739, by rfl⟩ : syracuseStep 1458319 = 2187479) B2187479
theorem B1230313 : Blo 682313 1230313 := bstep (se 2 (by rfl) ⟨461367, by rfl⟩ : syracuseStep 1230313 = 922735) B922735
theorem B3458537 : Blo 682313 3458537 := bstep (se 2 (by rfl) ⟨1296951, by rfl⟩ : syracuseStep 3458537 = 2593903) B2593903
theorem B1951465 : Blo 682313 1951465 := bstep (se 2 (by rfl) ⟨731799, by rfl⟩ : syracuseStep 1951465 = 1463599) B1463599
theorem B5851115 : Blo 682313 5851115 := bstep (se 1 (by rfl) ⟨4388336, by rfl⟩ : syracuseStep 5851115 = 8776673) B8776673
theorem B8898767 : Blo 682313 8898767 := bstep (se 1 (by rfl) ⟨6674075, by rfl⟩ : syracuseStep 8898767 = 13348151) B13348151
theorem B5327063 : Blo 682313 5327063 := bstep (se 1 (by rfl) ⟨3995297, by rfl⟩ : syracuseStep 5327063 = 7990595) B7990595
theorem B4507907 : Blo 682313 4507907 := bstep (se 1 (by rfl) ⟨3380930, by rfl⟩ : syracuseStep 4507907 = 6761861) B6761861
theorem B1460711 : Blo 682313 1460711 := bstep (se 1 (by rfl) ⟨1095533, by rfl⟩ : syracuseStep 1460711 = 2191067) B2191067
theorem B1460729 : Blo 682313 1460729 := bstep (se 2 (by rfl) ⟨547773, by rfl⟩ : syracuseStep 1460729 = 1095547) B1095547
theorem B2312927 : Blo 682313 2312927 := bstep (se 1 (by rfl) ⟨1734695, by rfl⟩ : syracuseStep 2312927 = 3469391) B3469391
theorem B3690143 : Blo 682313 3690143 := bstep (se 1 (by rfl) ⟨2767607, by rfl⟩ : syracuseStep 3690143 = 5535215) B5535215
theorem B1462249 : Blo 682313 1462249 := bstep (se 2 (by rfl) ⟨548343, by rfl⟩ : syracuseStep 1462249 = 1096687) B1096687
theorem B1462369 : Blo 682313 1462369 := bstep (se 2 (by rfl) ⟨548388, by rfl⟩ : syracuseStep 1462369 = 1096777) B1096777
theorem B1953983 : Blo 682313 1953983 := bstep (se 1 (by rfl) ⟨1465487, by rfl⟩ : syracuseStep 1953983 = 2930975) B2930975
theorem B1298767 : Blo 682313 1298767 := bstep (se 1 (by rfl) ⟨974075, by rfl⟩ : syracuseStep 1298767 = 1948151) B1948151
theorem B2347471 : Blo 682313 2347471 := bstep (se 1 (by rfl) ⟨1760603, by rfl⟩ : syracuseStep 2347471 = 3521207) B3521207
theorem B12669779 : Blo 682313 12669779 := bstep (se 1 (by rfl) ⟨9502334, by rfl⟩ : syracuseStep 12669779 = 19004669) B19004669
theorem B5854841 : Blo 682313 5854841 := bstep (se 2 (by rfl) ⟨2195565, by rfl⟩ : syracuseStep 5854841 = 4391131) B4391131
theorem B2315951 : Blo 682313 2315951 := bstep (se 1 (by rfl) ⟨1736963, by rfl⟩ : syracuseStep 2315951 = 3473927) B3473927
theorem B3758089 : Blo 682313 3758089 := bstep (se 2 (by rfl) ⟨1409283, by rfl⟩ : syracuseStep 3758089 = 2818567) B2818567
theorem B1300711 : Blo 682313 1300711 := bstep (se 1 (by rfl) ⟨975533, by rfl⟩ : syracuseStep 1300711 = 1951067) B1951067
theorem B3758375 : Blo 682313 3758375 := bstep (se 1 (by rfl) ⟨2818781, by rfl⟩ : syracuseStep 3758375 = 5637563) B5637563
theorem B1301417 : Blo 682313 1301417 := bstep (se 2 (by rfl) ⟨488031, by rfl⟩ : syracuseStep 1301417 = 976063) B976063
theorem B1465427 : Blo 682313 1465427 := bstep (se 1 (by rfl) ⟨1099070, by rfl⟩ : syracuseStep 1465427 = 2198141) B2198141
theorem B29679047 : Blo 682313 29679047 := bstep (se 1 (by rfl) ⟨22259285, by rfl⟩ : syracuseStep 29679047 = 44518571) B44518571
theorem B2809721 : Blo 682313 2809721 := bstep (se 2 (by rfl) ⟨1053645, by rfl⟩ : syracuseStep 2809721 = 2107291) B2107291
theorem B1171327 : Blo 682313 1171327 := bstep (se 1 (by rfl) ⟨878495, by rfl⟩ : syracuseStep 1171327 = 1756991) B1756991
theorem B3891563 : Blo 682313 3891563 := bstep (se 1 (by rfl) ⟨2918672, by rfl⟩ : syracuseStep 3891563 = 5837345) B5837345
theorem B27812555 : Blo 682313 27812555 := bstep (se 1 (by rfl) ⟨20859416, by rfl⟩ : syracuseStep 27812555 = 41718833) B41718833
theorem B3891995 : Blo 682313 3891995 := bstep (se 1 (by rfl) ⟨2918996, by rfl⟩ : syracuseStep 3891995 = 5837993) B5837993
theorem B39969611 : Blo 682313 39969611 := bstep (se 1 (by rfl) ⟨29977208, by rfl⟩ : syracuseStep 39969611 = 59954417) B59954417
theorem B2778943 : Blo 682313 2778943 := bstep (se 1 (by rfl) ⟨2084207, by rfl⟩ : syracuseStep 2778943 = 4168415) B4168415
theorem B33318863 : Blo 682313 33318863 := bstep (se 1 (by rfl) ⟨24989147, by rfl⟩ : syracuseStep 33318863 = 49978295) B49978295
theorem B1730555 : Blo 682313 1730555 := bstep (se 1 (by rfl) ⟨1297916, by rfl⟩ : syracuseStep 1730555 = 2595833) B2595833
theorem B6580273 : Blo 682313 6580273 := bstep (se 2 (by rfl) ⟨2467602, by rfl⟩ : syracuseStep 6580273 = 4935205) B4935205
theorem B977179 : Blo 682313 977179 := bstep (se 1 (by rfl) ⟨732884, by rfl⟩ : syracuseStep 977179 = 1465769) B1465769
theorem B1108351 : Blo 682313 1108351 := bstep (se 1 (by rfl) ⟨831263, by rfl⟩ : syracuseStep 1108351 = 1662527) B1662527
theorem B682399 : Blo 682313 682399 := bstep (se 1 (by rfl) ⟨511799, by rfl⟩ : syracuseStep 682399 = 1023599) B1023599
theorem B682479 : Blo 682313 682479 := bstep (se 1 (by rfl) ⟨511859, by rfl⟩ : syracuseStep 682479 = 1023719) B1023719
theorem B682663 : Blo 682313 682663 := bstep (se 1 (by rfl) ⟨511997, by rfl⟩ : syracuseStep 682663 = 1023995) B1023995
theorem B682703 : Blo 682313 682703 := bstep (se 1 (by rfl) ⟨512027, by rfl⟩ : syracuseStep 682703 = 1024055) B1024055
theorem B682783 : Blo 682313 682783 := bstep (se 1 (by rfl) ⟨512087, by rfl⟩ : syracuseStep 682783 = 1024175) B1024175
theorem B682919 : Blo 682313 682919 := bstep (se 1 (by rfl) ⟨512189, by rfl⟩ : syracuseStep 682919 = 1024379) B1024379
theorem B1731527 : Blo 682313 1731527 := bstep (se 1 (by rfl) ⟨1298645, by rfl⟩ : syracuseStep 1731527 = 2597291) B2597291
theorem B3468257 : Blo 682313 3468257 := bstep (se 2 (by rfl) ⟨1300596, by rfl⟩ : syracuseStep 3468257 = 2601193) B2601193
theorem B683035 : Blo 682313 683035 := bstep (se 1 (by rfl) ⟨512276, by rfl⟩ : syracuseStep 683035 = 1024553) B1024553
theorem B683099 : Blo 682313 683099 := bstep (se 1 (by rfl) ⟨512324, by rfl⟩ : syracuseStep 683099 = 1024649) B1024649
theorem B2813143 : Blo 682313 2813143 := bstep (se 1 (by rfl) ⟨2109857, by rfl⟩ : syracuseStep 2813143 = 4219715) B4219715
theorem B683239 : Blo 682313 683239 := bstep (se 1 (by rfl) ⟨512429, by rfl⟩ : syracuseStep 683239 = 1024859) B1024859
theorem B683263 : Blo 682313 683263 := bstep (se 1 (by rfl) ⟨512447, by rfl⟩ : syracuseStep 683263 = 1024895) B1024895
theorem B683311 : Blo 682313 683311 := bstep (se 1 (by rfl) ⟨512483, by rfl⟩ : syracuseStep 683311 = 1024967) B1024967
theorem B11103641 : Blo 682313 11103641 := bstep (se 2 (by rfl) ⟨4163865, by rfl⟩ : syracuseStep 11103641 = 8327731) B8327731
theorem B683455 : Blo 682313 683455 := bstep (se 1 (by rfl) ⟨512591, by rfl⟩ : syracuseStep 683455 = 1025183) B1025183
theorem B683551 : Blo 682313 683551 := bstep (se 1 (by rfl) ⟨512663, by rfl⟩ : syracuseStep 683551 = 1025327) B1025327
theorem B683679 : Blo 682313 683679 := bstep (se 1 (by rfl) ⟨512759, by rfl⟩ : syracuseStep 683679 = 1025519) B1025519
theorem B683687 : Blo 682313 683687 := bstep (se 1 (by rfl) ⟨512765, by rfl⟩ : syracuseStep 683687 = 1025531) B1025531
theorem B683711 : Blo 682313 683711 := bstep (se 1 (by rfl) ⟨512783, by rfl⟩ : syracuseStep 683711 = 1025567) B1025567
theorem B683807 : Blo 682313 683807 := bstep (se 1 (by rfl) ⟨512855, by rfl⟩ : syracuseStep 683807 = 1025711) B1025711
theorem B683867 : Blo 682313 683867 := bstep (se 1 (by rfl) ⟨512900, by rfl⟩ : syracuseStep 683867 = 1025801) B1025801
theorem B683887 : Blo 682313 683887 := bstep (se 1 (by rfl) ⟨512915, by rfl⟩ : syracuseStep 683887 = 1025831) B1025831
theorem B1535867 : Blo 682313 1535867 := bstep (se 1 (by rfl) ⟨1151900, by rfl⟩ : syracuseStep 1535867 = 2303801) B2303801
theorem B35549117 : Blo 682313 35549117 := bstep (se 3 (by rfl) ⟨6665459, by rfl⟩ : syracuseStep 35549117 = 13330919) B13330919
theorem B684287 : Blo 682313 684287 := bstep (se 1 (by rfl) ⟨513215, by rfl⟩ : syracuseStep 684287 = 1026431) B1026431
theorem B684447 : Blo 682313 684447 := bstep (se 1 (by rfl) ⟨513335, by rfl⟩ : syracuseStep 684447 = 1026671) B1026671
theorem B112325039 : Blo 682313 112325039 := bstep (se 1 (by rfl) ⟨84243779, by rfl⟩ : syracuseStep 112325039 = 168487559) B168487559
theorem B1536443 : Blo 682313 1536443 := bstep (se 1 (by rfl) ⟨1152332, by rfl⟩ : syracuseStep 1536443 = 2304665) B2304665
theorem B684591 : Blo 682313 684591 := bstep (se 1 (by rfl) ⟨513443, by rfl⟩ : syracuseStep 684591 = 1026887) B1026887
theorem B47280719 : Blo 682313 47280719 := bstep (se 1 (by rfl) ⟨35460539, by rfl⟩ : syracuseStep 47280719 = 70921079) B70921079
theorem B684991 : Blo 682313 684991 := bstep (se 1 (by rfl) ⟨513743, by rfl⟩ : syracuseStep 684991 = 1027487) B1027487
theorem B5207003 : Blo 682313 5207003 := bstep (se 1 (by rfl) ⟨3905252, by rfl⟩ : syracuseStep 5207003 = 7810505) B7810505
theorem B18674657 : Blo 682313 18674657 := bstep (se 2 (by rfl) ⟨7002996, by rfl⟩ : syracuseStep 18674657 = 14005993) B14005993
theorem B685167 : Blo 682313 685167 := bstep (se 1 (by rfl) ⟨513875, by rfl⟩ : syracuseStep 685167 = 1027751) B1027751
theorem B685183 : Blo 682313 685183 := bstep (se 1 (by rfl) ⟨513887, by rfl⟩ : syracuseStep 685183 = 1027775) B1027775
theorem B685247 : Blo 682313 685247 := bstep (se 1 (by rfl) ⟨513935, by rfl⟩ : syracuseStep 685247 = 1027871) B1027871
theorem B5338331 : Blo 682313 5338331 := bstep (se 1 (by rfl) ⟨4003748, by rfl⟩ : syracuseStep 5338331 = 8007497) B8007497
theorem B685439 : Blo 682313 685439 := bstep (se 1 (by rfl) ⟨514079, by rfl⟩ : syracuseStep 685439 = 1028159) B1028159
theorem B685567 : Blo 682313 685567 := bstep (se 1 (by rfl) ⟨514175, by rfl⟩ : syracuseStep 685567 = 1028351) B1028351
theorem B685595 : Blo 682313 685595 := bstep (se 1 (by rfl) ⟨514196, by rfl⟩ : syracuseStep 685595 = 1028393) B1028393
theorem B685775 : Blo 682313 685775 := bstep (se 1 (by rfl) ⟨514331, by rfl⟩ : syracuseStep 685775 = 1028663) B1028663
theorem B11106031 : Blo 682313 11106031 := bstep (se 1 (by rfl) ⟨8329523, by rfl⟩ : syracuseStep 11106031 = 16659047) B16659047
theorem B1537811 : Blo 682313 1537811 := bstep (se 1 (by rfl) ⟨1153358, by rfl⟩ : syracuseStep 1537811 = 2306717) B2306717
theorem B1537883 : Blo 682313 1537883 := bstep (se 1 (by rfl) ⟨1153412, by rfl⟩ : syracuseStep 1537883 = 2306825) B2306825
theorem B685935 : Blo 682313 685935 := bstep (se 1 (by rfl) ⟨514451, by rfl⟩ : syracuseStep 685935 = 1028903) B1028903
theorem B686015 : Blo 682313 686015 := bstep (se 1 (by rfl) ⟨514511, by rfl⟩ : syracuseStep 686015 = 1029023) B1029023
theorem B7403501 : Blo 682313 7403501 := bstep (se 3 (by rfl) ⟨1388156, by rfl⟩ : syracuseStep 7403501 = 2776313) B2776313
theorem B3897395 : Blo 682313 3897395 := bstep (se 1 (by rfl) ⟨2923046, by rfl⟩ : syracuseStep 3897395 = 5846093) B5846093
theorem B1538171 : Blo 682313 1538171 := bstep (se 1 (by rfl) ⟨1153628, by rfl⟩ : syracuseStep 1538171 = 2307257) B2307257
theorem B5536345 : Blo 682313 5536345 := bstep (se 2 (by rfl) ⟨2076129, by rfl⟩ : syracuseStep 5536345 = 4152259) B4152259
theorem B8780669 : Blo 682313 8780669 := bstep (se 3 (by rfl) ⟨1646375, by rfl⟩ : syracuseStep 8780669 = 3292751) B3292751
theorem B1539503 : Blo 682313 1539503 := bstep (se 1 (by rfl) ⟨1154627, by rfl⟩ : syracuseStep 1539503 = 2309255) B2309255
theorem B1539611 : Blo 682313 1539611 := bstep (se 1 (by rfl) ⟨1154708, by rfl⟩ : syracuseStep 1539611 = 2309417) B2309417
theorem B5209919 : Blo 682313 5209919 := bstep (se 1 (by rfl) ⟨3907439, by rfl⟩ : syracuseStep 5209919 = 7814879) B7814879
theorem B6225979 : Blo 682313 6225979 := bstep (se 1 (by rfl) ⟨4669484, by rfl⟩ : syracuseStep 6225979 = 9338969) B9338969
theorem B1540961 : Blo 682313 1540961 := bstep (se 2 (by rfl) ⟨577860, by rfl⟩ : syracuseStep 1540961 = 1155721) B1155721
theorem B3900743 : Blo 682313 3900743 := bstep (se 1 (by rfl) ⟨2925557, by rfl⟩ : syracuseStep 3900743 = 5851115) B5851115
theorem B5932511 : Blo 682313 5932511 := bstep (se 1 (by rfl) ⟨4449383, by rfl⟩ : syracuseStep 5932511 = 8898767) B8898767
theorem B1541951 : Blo 682313 1541951 := bstep (se 1 (by rfl) ⟨1156463, by rfl⟩ : syracuseStep 1541951 = 2312927) B2312927
theorem B1640417 : Blo 682313 1640417 := bstep (se 2 (by rfl) ⟨615156, by rfl⟩ : syracuseStep 1640417 = 1230313) B1230313
theorem B16648537 : Blo 682313 16648537 := bstep (se 2 (by rfl) ⟨6243201, by rfl⟩ : syracuseStep 16648537 = 12486403) B12486403
theorem B3705257 : Blo 682313 3705257 := bstep (se 2 (by rfl) ⟨1389471, by rfl⟩ : syracuseStep 3705257 = 2778943) B2778943
theorem B2460095 : Blo 682313 2460095 := bstep (se 1 (by rfl) ⟨1845071, by rfl⟩ : syracuseStep 2460095 = 3690143) B3690143
theorem B7801757 : Blo 682313 7801757 := bstep (se 3 (by rfl) ⟨1462829, by rfl⟩ : syracuseStep 7801757 = 2925659) B2925659
theorem B1477801 : Blo 682313 1477801 := bstep (se 2 (by rfl) ⟨554175, by rfl⟩ : syracuseStep 1477801 = 1108351) B1108351
theorem B3903227 : Blo 682313 3903227 := bstep (se 1 (by rfl) ⟨2927420, by rfl⟩ : syracuseStep 3903227 = 5854841) B5854841
theorem B1543967 : Blo 682313 1543967 := bstep (se 1 (by rfl) ⟨1157975, by rfl⟩ : syracuseStep 1543967 = 2315951) B2315951
theorem B4166225 : Blo 682313 4166225 := bstep (se 2 (by rfl) ⟨1562334, by rfl⟩ : syracuseStep 4166225 = 3124669) B3124669
theorem B2593417 : Blo 682313 2593417 := bstep (se 2 (by rfl) ⟨972531, by rfl⟩ : syracuseStep 2593417 = 1945063) B1945063
theorem B3281833 : Blo 682313 3281833 := bstep (se 2 (by rfl) ⟨1230687, by rfl⟩ : syracuseStep 3281833 = 2461375) B2461375
theorem B1873147 : Blo 682313 1873147 := bstep (se 1 (by rfl) ⟨1404860, by rfl⟩ : syracuseStep 1873147 = 2809721) B2809721
theorem B31659407 : Blo 682313 31659407 := bstep (se 1 (by rfl) ⟨23744555, by rfl⟩ : syracuseStep 31659407 = 47489111) B47489111
theorem B2594375 : Blo 682313 2594375 := bstep (se 1 (by rfl) ⟨1945781, by rfl⟩ : syracuseStep 2594375 = 3891563) B3891563
theorem B1644263 : Blo 682313 1644263 := bstep (se 1 (by rfl) ⟨1233197, by rfl⟩ : syracuseStep 1644263 = 2466395) B2466395
theorem B2594663 : Blo 682313 2594663 := bstep (se 1 (by rfl) ⟨1945997, by rfl⟩ : syracuseStep 2594663 = 3891995) B3891995
theorem B26646407 : Blo 682313 26646407 := bstep (se 1 (by rfl) ⟨19984805, by rfl⟩ : syracuseStep 26646407 = 39969611) B39969611
theorem B1153703 : Blo 682313 1153703 := bstep (se 1 (by rfl) ⟨865277, by rfl⟩ : syracuseStep 1153703 = 1730555) B1730555
theorem B2956475 : Blo 682313 2956475 := bstep (se 1 (by rfl) ⟨2217356, by rfl⟩ : syracuseStep 2956475 = 4434713) B4434713
theorem B1154351 : Blo 682313 1154351 := bstep (se 1 (by rfl) ⟨865763, by rfl⟩ : syracuseStep 1154351 = 1731527) B1731527
theorem B9870821 : Blo 682313 9870821 := bstep (se 4 (by rfl) ⟨925389, by rfl⟩ : syracuseStep 9870821 = 1850779) B1850779
theorem B1023911 : Blo 682313 1023911 := bstep (se 1 (by rfl) ⟨767933, by rfl⟩ : syracuseStep 1023911 = 1535867) B1535867
theorem B23699411 : Blo 682313 23699411 := bstep (se 1 (by rfl) ⟨17774558, by rfl⟩ : syracuseStep 23699411 = 35549117) B35549117
theorem B1024169 : Blo 682313 1024169 := bstep (se 2 (by rfl) ⟨384063, by rfl⟩ : syracuseStep 1024169 = 768127) B768127
theorem B74883359 : Blo 682313 74883359 := bstep (se 1 (by rfl) ⟨56162519, by rfl⟩ : syracuseStep 74883359 = 112325039) B112325039
theorem B1024295 : Blo 682313 1024295 := bstep (se 1 (by rfl) ⟨768221, by rfl⟩ : syracuseStep 1024295 = 1536443) B1536443
theorem B89858423 : Blo 682313 89858423 := bstep (se 1 (by rfl) ⟨67393817, by rfl⟩ : syracuseStep 89858423 = 134787635) B134787635
theorem B2597609 : Blo 682313 2597609 := bstep (se 2 (by rfl) ⟨974103, by rfl⟩ : syracuseStep 2597609 = 1948207) B1948207
theorem B7381793 : Blo 682313 7381793 := bstep (se 2 (by rfl) ⟨2768172, by rfl⟩ : syracuseStep 7381793 = 5536345) B5536345
theorem B1025207 : Blo 682313 1025207 := bstep (se 1 (by rfl) ⟨768905, by rfl⟩ : syracuseStep 1025207 = 1537811) B1537811
theorem B1025255 : Blo 682313 1025255 := bstep (se 1 (by rfl) ⟨768941, by rfl⟩ : syracuseStep 1025255 = 1537883) B1537883
theorem B6563051 : Blo 682313 6563051 := bstep (se 1 (by rfl) ⟨4922288, by rfl⟩ : syracuseStep 6563051 = 9844577) B9844577
theorem B2598263 : Blo 682313 2598263 := bstep (se 1 (by rfl) ⟨1948697, by rfl⟩ : syracuseStep 2598263 = 3897395) B3897395
theorem B1025447 : Blo 682313 1025447 := bstep (se 1 (by rfl) ⟨769085, by rfl⟩ : syracuseStep 1025447 = 1538171) B1538171
theorem B1779155 : Blo 682313 1779155 := bstep (se 1 (by rfl) ⟨1334366, by rfl⟩ : syracuseStep 1779155 = 2668733) B2668733
theorem B1976039 : Blo 682313 1976039 := bstep (se 1 (by rfl) ⟨1482029, by rfl⟩ : syracuseStep 1976039 = 2964059) B2964059
theorem B2304287 : Blo 682313 2304287 := bstep (se 1 (by rfl) ⟨1728215, by rfl⟩ : syracuseStep 2304287 = 3456431) B3456431
theorem B1026335 : Blo 682313 1026335 := bstep (se 1 (by rfl) ⟨769751, by rfl⟩ : syracuseStep 1026335 = 1539503) B1539503
theorem B1026407 : Blo 682313 1026407 := bstep (se 1 (by rfl) ⟨769805, by rfl⟩ : syracuseStep 1026407 = 1539611) B1539611
theorem B1026779 : Blo 682313 1026779 := bstep (se 1 (by rfl) ⟨770084, by rfl⟩ : syracuseStep 1026779 = 1540169) B1540169
theorem B1944425 : Blo 682313 1944425 := bstep (se 2 (by rfl) ⟨729159, by rfl⟩ : syracuseStep 1944425 = 1458319) B1458319
theorem B1027055 : Blo 682313 1027055 := bstep (se 1 (by rfl) ⟨770291, by rfl⟩ : syracuseStep 1027055 = 1540583) B1540583
theorem B2928257 : Blo 682313 2928257 := bstep (se 2 (by rfl) ⟨1098096, by rfl⟩ : syracuseStep 2928257 = 2196193) B2196193
theorem B2305691 : Blo 682313 2305691 := bstep (se 1 (by rfl) ⟨1729268, by rfl⟩ : syracuseStep 2305691 = 3458537) B3458537
theorem B1028123 : Blo 682313 1028123 := bstep (se 1 (by rfl) ⟨771092, by rfl⟩ : syracuseStep 1028123 = 1542185) B1542185
theorem B3551375 : Blo 682313 3551375 := bstep (se 1 (by rfl) ⟨2663531, by rfl⟩ : syracuseStep 3551375 = 5327063) B5327063
theorem B3289369 : Blo 682313 3289369 := bstep (se 2 (by rfl) ⟨1233513, by rfl⟩ : syracuseStep 3289369 = 2467027) B2467027
theorem B1945883 : Blo 682313 1945883 := bstep (se 1 (by rfl) ⟨1459412, by rfl⟩ : syracuseStep 1945883 = 2918825) B2918825
theorem B1946567 : Blo 682313 1946567 := bstep (se 1 (by rfl) ⟨1459925, by rfl⟩ : syracuseStep 1946567 = 2919851) B2919851
theorem B2601953 : Blo 682313 2601953 := bstep (se 2 (by rfl) ⟨975732, by rfl⟩ : syracuseStep 2601953 = 1951465) B1951465
theorem B2505583 : Blo 682313 2505583 := bstep (se 1 (by rfl) ⟨1879187, by rfl⟩ : syracuseStep 2505583 = 3758375) B3758375
theorem B3750857 : Blo 682313 3750857 := bstep (se 2 (by rfl) ⟨1406571, by rfl⟩ : syracuseStep 3750857 = 2813143) B2813143
theorem B7781345 : Blo 682313 7781345 := bstep (se 2 (by rfl) ⟨2918004, by rfl⟩ : syracuseStep 7781345 = 5836009) B5836009
theorem B867611 : Blo 682313 867611 := bstep (se 1 (by rfl) ⟨650708, by rfl⟩ : syracuseStep 867611 = 1301417) B1301417
theorem B1949665 : Blo 682313 1949665 := bstep (se 2 (by rfl) ⟨731124, by rfl⟩ : syracuseStep 1949665 = 1462249) B1462249
theorem B770143 : Blo 682313 770143 := bstep (se 1 (by rfl) ⟨577607, by rfl⟩ : syracuseStep 770143 = 1155215) B1155215
theorem B1949825 : Blo 682313 1949825 := bstep (se 2 (by rfl) ⟨731184, by rfl⟩ : syracuseStep 1949825 = 1462369) B1462369
theorem B3129961 : Blo 682313 3129961 := bstep (se 2 (by rfl) ⟨1173735, by rfl⟩ : syracuseStep 3129961 = 2347471) B2347471
theorem B2312171 : Blo 682313 2312171 := bstep (se 1 (by rfl) ⟨1734128, by rfl⟩ : syracuseStep 2312171 = 3468257) B3468257
theorem B3558887 : Blo 682313 3558887 := bstep (se 1 (by rfl) ⟨2669165, by rfl⟩ : syracuseStep 3558887 = 5338331) B5338331
theorem B14077415 : Blo 682313 14077415 := bstep (se 1 (by rfl) ⟨10558061, by rfl⟩ : syracuseStep 14077415 = 21116123) B21116123
theorem B4935667 : Blo 682313 4935667 := bstep (se 1 (by rfl) ⟨3701750, by rfl⟩ : syracuseStep 4935667 = 7403501) B7403501
theorem B5853779 : Blo 682313 5853779 := bstep (se 1 (by rfl) ⟨4390334, by rfl⟩ : syracuseStep 5853779 = 8780669) B8780669
theorem B1299071 : Blo 682313 1299071 := bstep (se 1 (by rfl) ⟨974303, by rfl⟩ : syracuseStep 1299071 = 1948607) B1948607
theorem B971689 : Blo 682313 971689 := bstep (se 2 (by rfl) ⟨364383, by rfl⟩ : syracuseStep 971689 = 728767) B728767
theorem B1561769 : Blo 682313 1561769 := bstep (se 2 (by rfl) ⟨585663, by rfl⟩ : syracuseStep 1561769 = 1171327) B1171327
theorem B15979771 : Blo 682313 15979771 := bstep (se 1 (by rfl) ⟨11984828, by rfl⟩ : syracuseStep 15979771 = 23969657) B23969657
theorem B126081917 : Blo 682313 126081917 := bstep (se 3 (by rfl) ⟨23640359, by rfl⟩ : syracuseStep 126081917 = 47280719) B47280719
theorem B973819 : Blo 682313 973819 := bstep (se 1 (by rfl) ⟨730364, by rfl⟩ : syracuseStep 973819 = 1460729) B1460729
theorem B3693775 : Blo 682313 3693775 := bstep (se 1 (by rfl) ⟨2770331, by rfl⟩ : syracuseStep 3693775 = 5540663) B5540663
theorem B3890537 : Blo 682313 3890537 := bstep (se 2 (by rfl) ⟨1458951, by rfl⟩ : syracuseStep 3890537 = 2917903) B2917903
theorem B74866751 : Blo 682313 74866751 := bstep (se 1 (by rfl) ⟨56150063, by rfl⟩ : syracuseStep 74866751 = 112300127) B112300127
theorem B8773697 : Blo 682313 8773697 := bstep (se 2 (by rfl) ⟨3290136, by rfl⟩ : syracuseStep 8773697 = 6580273) B6580273
theorem B1302655 : Blo 682313 1302655 := bstep (se 1 (by rfl) ⟨976991, by rfl⟩ : syracuseStep 1302655 = 1953983) B1953983
theorem B1728823 : Blo 682313 1728823 := bstep (se 1 (by rfl) ⟨1296617, by rfl⟩ : syracuseStep 1728823 = 2593235) B2593235
theorem B1302905 : Blo 682313 1302905 := bstep (se 2 (by rfl) ⟨488589, by rfl⟩ : syracuseStep 1302905 = 977179) B977179
theorem B3957245 : Blo 682313 3957245 := bstep (se 3 (by rfl) ⟨741983, by rfl⟩ : syracuseStep 3957245 = 1483967) B1483967
theorem B8446519 : Blo 682313 8446519 := bstep (se 1 (by rfl) ⟨6334889, by rfl⟩ : syracuseStep 8446519 = 12669779) B12669779
theorem B1402363 : Blo 682313 1402363 := bstep (se 1 (by rfl) ⟨1051772, by rfl⟩ : syracuseStep 1402363 = 2103545) B2103545
theorem B1730231 : Blo 682313 1730231 := bstep (se 1 (by rfl) ⟨1297673, by rfl⟩ : syracuseStep 1730231 = 2595347) B2595347
theorem B3466961 : Blo 682313 3466961 := bstep (se 2 (by rfl) ⟨1300110, by rfl⟩ : syracuseStep 3466961 = 2600221) B2600221
theorem B3696475 : Blo 682313 3696475 := bstep (se 1 (by rfl) ⟨2772356, by rfl⟩ : syracuseStep 3696475 = 5544713) B5544713
theorem B976951 : Blo 682313 976951 := bstep (se 1 (by rfl) ⟨732713, by rfl⟩ : syracuseStep 976951 = 1465427) B1465427
theorem B1730747 : Blo 682313 1730747 := bstep (se 1 (by rfl) ⟨1298060, by rfl⟩ : syracuseStep 1730747 = 2596121) B2596121
theorem B19786031 : Blo 682313 19786031 := bstep (se 1 (by rfl) ⟨14839523, by rfl⟩ : syracuseStep 19786031 = 29679047) B29679047
theorem B682395 : Blo 682313 682395 := bstep (se 1 (by rfl) ⟨511796, by rfl⟩ : syracuseStep 682395 = 1023593) B1023593
theorem B1731689 : Blo 682313 1731689 := bstep (se 2 (by rfl) ⟨649383, by rfl⟩ : syracuseStep 1731689 = 1298767) B1298767
theorem B18541703 : Blo 682313 18541703 := bstep (se 1 (by rfl) ⟨13906277, by rfl⟩ : syracuseStep 18541703 = 27812555) B27812555
theorem B683163 : Blo 682313 683163 := bstep (se 1 (by rfl) ⟨512372, by rfl⟩ : syracuseStep 683163 = 1024745) B1024745
theorem B683175 : Blo 682313 683175 := bstep (se 1 (by rfl) ⟨512381, by rfl⟩ : syracuseStep 683175 = 1024763) B1024763
theorem B2780335 : Blo 682313 2780335 := bstep (se 1 (by rfl) ⟨2085251, by rfl⟩ : syracuseStep 2780335 = 4170503) B4170503
theorem B5401799 : Blo 682313 5401799 := bstep (se 1 (by rfl) ⟨4051349, by rfl⟩ : syracuseStep 5401799 = 8102699) B8102699
theorem B12021085 : Blo 682313 12021085 := bstep (se 3 (by rfl) ⟨2253953, by rfl⟩ : syracuseStep 12021085 = 4507907) B4507907
theorem B683519 : Blo 682313 683519 := bstep (se 1 (by rfl) ⟨512639, by rfl⟩ : syracuseStep 683519 = 1025279) B1025279
theorem B683727 : Blo 682313 683727 := bstep (se 1 (by rfl) ⟨512795, by rfl⟩ : syracuseStep 683727 = 1025591) B1025591
theorem B13725521 : Blo 682313 13725521 := bstep (se 2 (by rfl) ⟨5147070, by rfl⟩ : syracuseStep 13725521 = 10294141) B10294141
theorem B3895229 : Blo 682313 3895229 := bstep (se 3 (by rfl) ⟨730355, by rfl⟩ : syracuseStep 3895229 = 1460711) B1460711
theorem B683967 : Blo 682313 683967 := bstep (se 1 (by rfl) ⟨512975, by rfl⟩ : syracuseStep 683967 = 1025951) B1025951
theorem B22212575 : Blo 682313 22212575 := bstep (se 1 (by rfl) ⟨16659431, by rfl⟩ : syracuseStep 22212575 = 33318863) B33318863
theorem B1535975 : Blo 682313 1535975 := bstep (se 1 (by rfl) ⟨1151981, by rfl⟩ : syracuseStep 1535975 = 2303963) B2303963
theorem B1732711 : Blo 682313 1732711 := bstep (se 1 (by rfl) ⟨1299533, by rfl⟩ : syracuseStep 1732711 = 2599067) B2599067
theorem B684255 : Blo 682313 684255 := bstep (se 1 (by rfl) ⟨513191, by rfl⟩ : syracuseStep 684255 = 1026383) B1026383
theorem B1536425 : Blo 682313 1536425 := bstep (se 2 (by rfl) ⟨576159, by rfl⟩ : syracuseStep 1536425 = 1152319) B1152319
theorem B684543 : Blo 682313 684543 := bstep (se 1 (by rfl) ⟨513407, by rfl⟩ : syracuseStep 684543 = 1026815) B1026815
theorem B7402427 : Blo 682313 7402427 := bstep (se 1 (by rfl) ⟨5551820, by rfl⟩ : syracuseStep 7402427 = 11103641) B11103641
theorem B14808041 : Blo 682313 14808041 := bstep (se 2 (by rfl) ⟨5553015, by rfl⟩ : syracuseStep 14808041 = 11106031) B11106031
theorem B685279 : Blo 682313 685279 := bstep (se 1 (by rfl) ⟨513959, by rfl⟩ : syracuseStep 685279 = 1027919) B1027919
theorem B685359 : Blo 682313 685359 := bstep (se 1 (by rfl) ⟨514019, by rfl⟩ : syracuseStep 685359 = 1028039) B1028039
theorem B5010785 : Blo 682313 5010785 := bstep (se 2 (by rfl) ⟨1879044, by rfl⟩ : syracuseStep 5010785 = 3758089) B3758089
theorem B685599 : Blo 682313 685599 := bstep (se 1 (by rfl) ⟨514199, by rfl⟩ : syracuseStep 685599 = 1028399) B1028399
theorem B1734281 : Blo 682313 1734281 := bstep (se 2 (by rfl) ⟨650355, by rfl⟩ : syracuseStep 1734281 = 1300711) B1300711
theorem B1537703 : Blo 682313 1537703 := bstep (se 1 (by rfl) ⟨1153277, by rfl⟩ : syracuseStep 1537703 = 2306555) B2306555
theorem B1734311 : Blo 682313 1734311 := bstep (se 1 (by rfl) ⟨1300733, by rfl⟩ : syracuseStep 1734311 = 2601467) B2601467
theorem B685759 : Blo 682313 685759 := bstep (se 1 (by rfl) ⟨514319, by rfl⟩ : syracuseStep 685759 = 1028639) B1028639
theorem B685991 : Blo 682313 685991 := bstep (se 1 (by rfl) ⟨514493, by rfl⟩ : syracuseStep 685991 = 1028987) B1028987
theorem B49903559 : Blo 682313 49903559 := bstep (se 1 (by rfl) ⟨37427669, by rfl⟩ : syracuseStep 49903559 = 74855339) B74855339
theorem B3471335 : Blo 682313 3471335 := bstep (se 1 (by rfl) ⟨2603501, by rfl⟩ : syracuseStep 3471335 = 5207003) B5207003
theorem B12449771 : Blo 682313 12449771 := bstep (se 1 (by rfl) ⟨9337328, by rfl⟩ : syracuseStep 12449771 = 18674657) B18674657
theorem B686111 : Blo 682313 686111 := bstep (se 1 (by rfl) ⟨514583, by rfl⟩ : syracuseStep 686111 = 1029167) B1029167
theorem B686191 : Blo 682313 686191 := bstep (se 1 (by rfl) ⟨514643, by rfl⟩ : syracuseStep 686191 = 1029287) B1029287
theorem B686287 : Blo 682313 686287 := bstep (se 1 (by rfl) ⟨514715, by rfl⟩ : syracuseStep 686287 = 1029431) B1029431
theorem B1539233 : Blo 682313 1539233 := bstep (se 2 (by rfl) ⟨577212, by rfl⟩ : syracuseStep 1539233 = 1154425) B1154425
theorem B1736255 : Blo 682313 1736255 := bstep (se 1 (by rfl) ⟨1302191, by rfl⟩ : syracuseStep 1736255 = 2604383) B2604383
theorem B3473279 : Blo 682313 3473279 := bstep (se 1 (by rfl) ⟨2604959, by rfl⟩ : syracuseStep 3473279 = 5209919) B5209919
theorem B1736873 : Blo 682313 1736873 := bstep (se 2 (by rfl) ⟨651327, by rfl⟩ : syracuseStep 1736873 = 1302655) B1302655
theorem B5210405 : Blo 682313 5210405 := bstep (se 4 (by rfl) ⟨488475, by rfl⟩ : syracuseStep 5210405 = 976951) B976951
theorem B9470333 : Blo 682313 9470333 := bstep (se 3 (by rfl) ⟨1775687, by rfl⟩ : syracuseStep 9470333 = 3551375) B3551375
theorem B3474413 : Blo 682313 3474413 := bstep (se 3 (by rfl) ⟨651452, by rfl⟩ : syracuseStep 3474413 = 1302905) B1302905
theorem B1541447 : Blo 682313 1541447 := bstep (se 1 (by rfl) ⟨1156085, by rfl⟩ : syracuseStep 1541447 = 2312171) B2312171
theorem B1640063 : Blo 682313 1640063 := bstep (se 1 (by rfl) ⟨1230047, by rfl⟩ : syracuseStep 1640063 = 2460095) B2460095
theorem B1869817 : Blo 682313 1869817 := bstep (se 2 (by rfl) ⟨701181, by rfl⟩ : syracuseStep 1869817 = 1402363) B1402363
theorem B3902519 : Blo 682313 3902519 := bstep (se 1 (by rfl) ⟨2926889, by rfl⟩ : syracuseStep 3902519 = 5853779) B5853779
theorem B21106271 : Blo 682313 21106271 := bstep (se 1 (by rfl) ⟨15829703, by rfl⟩ : syracuseStep 21106271 = 31659407) B31659407
theorem B17764271 : Blo 682313 17764271 := bstep (se 1 (by rfl) ⟨13323203, by rfl⟩ : syracuseStep 17764271 = 26646407) B26646407
theorem B1970401 : Blo 682313 1970401 := bstep (se 2 (by rfl) ⟨738900, by rfl⟩ : syracuseStep 1970401 = 1477801) B1477801
theorem B16028113 : Blo 682313 16028113 := bstep (se 2 (by rfl) ⟨6010542, by rfl⟩ : syracuseStep 16028113 = 12021085) B12021085
theorem B84054611 : Blo 682313 84054611 := bstep (se 1 (by rfl) ⟨63040958, by rfl⟩ : syracuseStep 84054611 = 126081917) B126081917
theorem B1970983 : Blo 682313 1970983 := bstep (se 1 (by rfl) ⟨1478237, by rfl⟩ : syracuseStep 1970983 = 2956475) B2956475
theorem B2593691 : Blo 682313 2593691 := bstep (se 1 (by rfl) ⟨1945268, by rfl⟩ : syracuseStep 2593691 = 3890537) B3890537
theorem B15799607 : Blo 682313 15799607 := bstep (se 1 (by rfl) ⟨11849705, by rfl⟩ : syracuseStep 15799607 = 23699411) B23699411
theorem B49911167 : Blo 682313 49911167 := bstep (se 1 (by rfl) ⟨37433375, by rfl⟩ : syracuseStep 49911167 = 74866751) B74866751
theorem B4921195 : Blo 682313 4921195 := bstep (se 1 (by rfl) ⟨3690896, by rfl⟩ : syracuseStep 4921195 = 7381793) B7381793
theorem B1186103 : Blo 682313 1186103 := bstep (se 1 (by rfl) ⟨889577, by rfl⟩ : syracuseStep 1186103 = 1779155) B1779155
theorem B1153487 : Blo 682313 1153487 := bstep (se 1 (by rfl) ⟨865115, by rfl⟩ : syracuseStep 1153487 = 1730231) B1730231
theorem B1317359 : Blo 682313 1317359 := bstep (se 1 (by rfl) ⟨988019, by rfl⟩ : syracuseStep 1317359 = 1976039) B1976039
theorem B1153831 : Blo 682313 1153831 := bstep (se 1 (by rfl) ⟨865373, by rfl⟩ : syracuseStep 1153831 = 1730747) B1730747
theorem B2497529 : Blo 682313 2497529 := bstep (se 2 (by rfl) ⟨936573, by rfl⟩ : syracuseStep 2497529 = 1873147) B1873147
theorem B1154459 : Blo 682313 1154459 := bstep (se 1 (by rfl) ⟨865844, by rfl⟩ : syracuseStep 1154459 = 1731689) B1731689
theorem B12361135 : Blo 682313 12361135 := bstep (se 1 (by rfl) ⟨9270851, by rfl⟩ : syracuseStep 12361135 = 18541703) B18541703
theorem B5185133 : Blo 682313 5185133 := bstep (se 3 (by rfl) ⟨972212, by rfl⟩ : syracuseStep 5185133 = 1944425) B1944425
theorem B9150347 : Blo 682313 9150347 := bstep (se 1 (by rfl) ⟨6862760, by rfl⟩ : syracuseStep 9150347 = 13725521) B13725521
theorem B2596819 : Blo 682313 2596819 := bstep (se 1 (by rfl) ⟨1947614, by rfl⟩ : syracuseStep 2596819 = 3895229) B3895229
theorem B1023983 : Blo 682313 1023983 := bstep (se 1 (by rfl) ⟨767987, by rfl⟩ : syracuseStep 1023983 = 1535975) B1535975
theorem B1024283 : Blo 682313 1024283 := bstep (se 1 (by rfl) ⟨768212, by rfl⟩ : syracuseStep 1024283 = 1536425) B1536425
theorem B9872027 : Blo 682313 9872027 := bstep (se 1 (by rfl) ⟨7404020, by rfl⟩ : syracuseStep 9872027 = 14808041) B14808041
theorem B1156187 : Blo 682313 1156187 := bstep (se 1 (by rfl) ⟨867140, by rfl⟩ : syracuseStep 1156187 = 1734281) B1734281
theorem B1025135 : Blo 682313 1025135 := bstep (se 1 (by rfl) ⟨768851, by rfl⟩ : syracuseStep 1025135 = 1537703) B1537703
theorem B1156207 : Blo 682313 1156207 := bstep (se 1 (by rfl) ⟨867155, by rfl⟩ : syracuseStep 1156207 = 1734311) B1734311
theorem B33269039 : Blo 682313 33269039 := bstep (se 1 (by rfl) ⟨24951779, by rfl⟩ : syracuseStep 33269039 = 49903559) B49903559
theorem B8299847 : Blo 682313 8299847 := bstep (se 1 (by rfl) ⟨6224885, by rfl⟩ : syracuseStep 8299847 = 12449771) B12449771
theorem B4925033 : Blo 682313 4925033 := bstep (se 2 (by rfl) ⟨1846887, by rfl⟩ : syracuseStep 4925033 = 3693775) B3693775
theorem B2500571 : Blo 682313 2500571 := bstep (se 1 (by rfl) ⟨1875428, by rfl⟩ : syracuseStep 2500571 = 3750857) B3750857
theorem B5187563 : Blo 682313 5187563 := bstep (se 1 (by rfl) ⟨3890672, by rfl⟩ : syracuseStep 5187563 = 7781345) B7781345
theorem B1026155 : Blo 682313 1026155 := bstep (se 1 (by rfl) ⟨769616, by rfl⟩ : syracuseStep 1026155 = 1539233) B1539233
theorem B1157503 : Blo 682313 1157503 := bstep (se 1 (by rfl) ⟨868127, by rfl⟩ : syracuseStep 1157503 = 1736255) B1736255
theorem B2599553 : Blo 682313 2599553 := bstep (se 2 (by rfl) ⟨974832, by rfl⟩ : syracuseStep 2599553 = 1949665) B1949665
theorem B8301305 : Blo 682313 8301305 := bstep (se 2 (by rfl) ⟨3112989, by rfl⟩ : syracuseStep 8301305 = 6225979) B6225979
theorem B1026857 : Blo 682313 1026857 := bstep (se 2 (by rfl) ⟨385071, by rfl⟩ : syracuseStep 1026857 = 770143) B770143
theorem B2305097 : Blo 682313 2305097 := bstep (se 2 (by rfl) ⟨864411, by rfl⟩ : syracuseStep 2305097 = 1728823) B1728823
theorem B1027307 : Blo 682313 1027307 := bstep (se 1 (by rfl) ⟨770480, by rfl⟩ : syracuseStep 1027307 = 1540961) B1540961
theorem B5189021 : Blo 682313 5189021 := bstep (se 3 (by rfl) ⟨972941, by rfl⟩ : syracuseStep 5189021 = 1945883) B1945883
theorem B4173281 : Blo 682313 4173281 := bstep (se 2 (by rfl) ⟨1564980, by rfl⟩ : syracuseStep 4173281 = 3129961) B3129961
theorem B2600495 : Blo 682313 2600495 := bstep (se 1 (by rfl) ⟨1950371, by rfl⟩ : syracuseStep 2600495 = 3900743) B3900743
theorem B1027967 : Blo 682313 1027967 := bstep (se 1 (by rfl) ⟨770975, by rfl⟩ : syracuseStep 1027967 = 1541951) B1541951
theorem B2470171 : Blo 682313 2470171 := bstep (se 1 (by rfl) ⟨1852628, by rfl⟩ : syracuseStep 2470171 = 3705257) B3705257
theorem B2372591 : Blo 682313 2372591 := bstep (se 1 (by rfl) ⟨1779443, by rfl⟩ : syracuseStep 2372591 = 3558887) B3558887
theorem B4928633 : Blo 682313 4928633 := bstep (se 2 (by rfl) ⟨1848237, by rfl⟩ : syracuseStep 4928633 = 3696475) B3696475
theorem B2602151 : Blo 682313 2602151 := bstep (se 1 (by rfl) ⟨1951613, by rfl⟩ : syracuseStep 2602151 = 3903227) B3903227
theorem B1029311 : Blo 682313 1029311 := bstep (se 1 (by rfl) ⟨771983, by rfl⟩ : syracuseStep 1029311 = 1543967) B1543967
theorem B866047 : Blo 682313 866047 := bstep (se 1 (by rfl) ⟨649535, by rfl⟩ : syracuseStep 866047 = 1299071) B1299071
theorem B22198049 : Blo 682313 22198049 := bstep (se 2 (by rfl) ⟨8324268, by rfl⟩ : syracuseStep 22198049 = 16648537) B16648537
theorem B1096175 : Blo 682313 1096175 := bstep (se 1 (by rfl) ⟨822131, by rfl⟩ : syracuseStep 1096175 = 1644263) B1644263
theorem B769135 : Blo 682313 769135 := bstep (se 1 (by rfl) ⟨576851, by rfl⟩ : syracuseStep 769135 = 1153703) B1153703
theorem B769567 : Blo 682313 769567 := bstep (se 1 (by rfl) ⟨577175, by rfl⟩ : syracuseStep 769567 = 1154351) B1154351
theorem B4374445 : Blo 682313 4374445 := bstep (se 3 (by rfl) ⟨820208, by rfl⟩ : syracuseStep 4374445 = 1640417) B1640417
theorem B5849131 : Blo 682313 5849131 := bstep (se 1 (by rfl) ⟨4386848, by rfl⟩ : syracuseStep 5849131 = 8773697) B8773697
theorem B2310281 : Blo 682313 2310281 := bstep (se 2 (by rfl) ⟨866355, by rfl⟩ : syracuseStep 2310281 = 1732711) B1732711
theorem B49922239 : Blo 682313 49922239 := bstep (se 1 (by rfl) ⟨37441679, by rfl⟩ : syracuseStep 49922239 = 74883359) B74883359
theorem B2638163 : Blo 682313 2638163 := bstep (se 1 (by rfl) ⟨1978622, by rfl⟩ : syracuseStep 2638163 = 3957245) B3957245
theorem B4375367 : Blo 682313 4375367 := bstep (se 1 (by rfl) ⟨3281525, by rfl⟩ : syracuseStep 4375367 = 6563051) B6563051
theorem B3457889 : Blo 682313 3457889 := bstep (se 2 (by rfl) ⟨1296708, by rfl⟩ : syracuseStep 3457889 = 2593417) B2593417
theorem B14828453 : Blo 682313 14828453 := bstep (se 4 (by rfl) ⟨1390167, by rfl⟩ : syracuseStep 14828453 = 2780335) B2780335
theorem B2311307 : Blo 682313 2311307 := bstep (se 1 (by rfl) ⟨1733480, by rfl⟩ : syracuseStep 2311307 = 3466961) B3466961
theorem B1295585 : Blo 682313 1295585 := bstep (se 2 (by rfl) ⟨485844, by rfl⟩ : syracuseStep 1295585 = 971689) B971689
theorem B4375777 : Blo 682313 4375777 := bstep (se 2 (by rfl) ⟨1640916, by rfl⟩ : syracuseStep 4375777 = 3281833) B3281833
theorem B13190687 : Blo 682313 13190687 := bstep (se 1 (by rfl) ⟨9893015, by rfl⟩ : syracuseStep 13190687 = 19786031) B19786031
theorem B1952171 : Blo 682313 1952171 := bstep (se 1 (by rfl) ⟨1464128, by rfl⟩ : syracuseStep 1952171 = 2928257) B2928257
theorem B4934951 : Blo 682313 4934951 := bstep (se 1 (by rfl) ⟨3701213, by rfl⟩ : syracuseStep 4934951 = 7402427) B7402427
theorem B1297711 : Blo 682313 1297711 := bstep (se 1 (by rfl) ⟨973283, by rfl⟩ : syracuseStep 1297711 = 1946567) B1946567
theorem B2313629 : Blo 682313 2313629 := bstep (se 3 (by rfl) ⟨433805, by rfl⟩ : syracuseStep 2313629 = 867611) B867611
theorem B37539773 : Blo 682313 37539773 := bstep (se 3 (by rfl) ⟨7038707, by rfl⟩ : syracuseStep 37539773 = 14077415) B14077415
theorem B2314223 : Blo 682313 2314223 := bstep (se 1 (by rfl) ⟨1735667, by rfl⟩ : syracuseStep 2314223 = 3471335) B3471335
theorem B1298425 : Blo 682313 1298425 := bstep (se 2 (by rfl) ⟨486909, by rfl⟩ : syracuseStep 1298425 = 973819) B973819
theorem B2315519 : Blo 682313 2315519 := bstep (se 1 (by rfl) ⟨1736639, by rfl⟩ : syracuseStep 2315519 = 3473279) B3473279
theorem B1299883 : Blo 682313 1299883 := bstep (se 1 (by rfl) ⟨974912, by rfl⟩ : syracuseStep 1299883 = 1949825) B1949825
theorem B11262025 : Blo 682313 11262025 := bstep (se 2 (by rfl) ⟨4223259, by rfl⟩ : syracuseStep 11262025 = 8446519) B8446519
theorem B239622461 : Blo 682313 239622461 := bstep (se 3 (by rfl) ⟨44929211, by rfl⟩ : syracuseStep 239622461 = 89858423) B89858423
theorem B3955007 : Blo 682313 3955007 := bstep (se 1 (by rfl) ⟨2966255, by rfl⟩ : syracuseStep 3955007 = 5932511) B5932511
theorem B5201171 : Blo 682313 5201171 := bstep (se 1 (by rfl) ⟨3900878, by rfl⟩ : syracuseStep 5201171 = 7801757) B7801757
theorem B2777483 : Blo 682313 2777483 := bstep (se 1 (by rfl) ⟨2083112, by rfl⟩ : syracuseStep 2777483 = 4166225) B4166225
theorem B1041179 : Blo 682313 1041179 := bstep (se 1 (by rfl) ⟨780884, by rfl⟩ : syracuseStep 1041179 = 1561769) B1561769
theorem B1729583 : Blo 682313 1729583 := bstep (se 1 (by rfl) ⟨1297187, by rfl⟩ : syracuseStep 1729583 = 2594375) B2594375
theorem B1729775 : Blo 682313 1729775 := bstep (se 1 (by rfl) ⟨1297331, by rfl⟩ : syracuseStep 1729775 = 2594663) B2594663
theorem B6580547 : Blo 682313 6580547 := bstep (se 1 (by rfl) ⟨4935410, by rfl⟩ : syracuseStep 6580547 = 9870821) B9870821
theorem B682607 : Blo 682313 682607 := bstep (se 1 (by rfl) ⟨511955, by rfl⟩ : syracuseStep 682607 = 1023911) B1023911
theorem B6580889 : Blo 682313 6580889 := bstep (se 2 (by rfl) ⟨2467833, by rfl⟩ : syracuseStep 6580889 = 4935667) B4935667
theorem B682779 : Blo 682313 682779 := bstep (se 1 (by rfl) ⟨512084, by rfl⟩ : syracuseStep 682779 = 1024169) B1024169
theorem B682863 : Blo 682313 682863 := bstep (se 1 (by rfl) ⟨512147, by rfl⟩ : syracuseStep 682863 = 1024295) B1024295
theorem B4385825 : Blo 682313 4385825 := bstep (se 2 (by rfl) ⟨1644684, by rfl⟩ : syracuseStep 4385825 = 3289369) B3289369
theorem B1731739 : Blo 682313 1731739 := bstep (se 1 (by rfl) ⟨1298804, by rfl⟩ : syracuseStep 1731739 = 2597609) B2597609
theorem B683471 : Blo 682313 683471 := bstep (se 1 (by rfl) ⟨512603, by rfl⟩ : syracuseStep 683471 = 1025207) B1025207
theorem B683503 : Blo 682313 683503 := bstep (se 1 (by rfl) ⟨512627, by rfl⟩ : syracuseStep 683503 = 1025255) B1025255
theorem B1732175 : Blo 682313 1732175 := bstep (se 1 (by rfl) ⟨1299131, by rfl⟩ : syracuseStep 1732175 = 2598263) B2598263
theorem B683631 : Blo 682313 683631 := bstep (se 1 (by rfl) ⟨512723, by rfl⟩ : syracuseStep 683631 = 1025447) B1025447
theorem B85225445 : Blo 682313 85225445 := bstep (se 4 (by rfl) ⟨7989885, by rfl⟩ : syracuseStep 85225445 = 15979771) B15979771
theorem B1536191 : Blo 682313 1536191 := bstep (se 1 (by rfl) ⟨1152143, by rfl⟩ : syracuseStep 1536191 = 2304287) B2304287
theorem B684223 : Blo 682313 684223 := bstep (se 1 (by rfl) ⟨513167, by rfl⟩ : syracuseStep 684223 = 1026335) B1026335
theorem B684271 : Blo 682313 684271 := bstep (se 1 (by rfl) ⟨513203, by rfl⟩ : syracuseStep 684271 = 1026407) B1026407
theorem B684519 : Blo 682313 684519 := bstep (se 1 (by rfl) ⟨513389, by rfl⟩ : syracuseStep 684519 = 1026779) B1026779
theorem B684703 : Blo 682313 684703 := bstep (se 1 (by rfl) ⟨513527, by rfl⟩ : syracuseStep 684703 = 1027055) B1027055
theorem B3601199 : Blo 682313 3601199 := bstep (se 1 (by rfl) ⟨2700899, by rfl⟩ : syracuseStep 3601199 = 5401799) B5401799
theorem B1537127 : Blo 682313 1537127 := bstep (se 1 (by rfl) ⟨1152845, by rfl⟩ : syracuseStep 1537127 = 2305691) B2305691
theorem B14808383 : Blo 682313 14808383 := bstep (se 1 (by rfl) ⟨11106287, by rfl⟩ : syracuseStep 14808383 = 22212575) B22212575
theorem B685415 : Blo 682313 685415 := bstep (se 1 (by rfl) ⟨514061, by rfl⟩ : syracuseStep 685415 = 1028123) B1028123
theorem B1734635 : Blo 682313 1734635 := bstep (se 1 (by rfl) ⟨1300976, by rfl⟩ : syracuseStep 1734635 = 2601953) B2601953
theorem B3340523 : Blo 682313 3340523 := bstep (se 1 (by rfl) ⟨2505392, by rfl⟩ : syracuseStep 3340523 = 5010785) B5010785
theorem B3340777 : Blo 682313 3340777 := bstep (se 2 (by rfl) ⟨1252791, by rfl⟩ : syracuseStep 3340777 = 2505583) B2505583
theorem B7798841 : Blo 682313 7798841 := bstep (se 2 (by rfl) ⟨2924565, by rfl⟩ : syracuseStep 7798841 = 5849131) B5849131
theorem B1540187 : Blo 682313 1540187 := bstep (se 1 (by rfl) ⟨1155140, by rfl⟩ : syracuseStep 1540187 = 2310281) B2310281
theorem B3473603 : Blo 682313 3473603 := bstep (se 1 (by rfl) ⟨2605202, by rfl⟩ : syracuseStep 3473603 = 5210405) B5210405
theorem B2916911 : Blo 682313 2916911 := bstep (se 1 (by rfl) ⟨2187683, by rfl⟩ : syracuseStep 2916911 = 4375367) B4375367
theorem B1540871 : Blo 682313 1540871 := bstep (se 1 (by rfl) ⟨1155653, by rfl⟩ : syracuseStep 1540871 = 2311307) B2311307
theorem B1541609 : Blo 682313 1541609 := bstep (se 2 (by rfl) ⟨578103, by rfl⟩ : syracuseStep 1541609 = 1156207) B1156207
theorem B5834369 : Blo 682313 5834369 := bstep (se 2 (by rfl) ⟨2187888, by rfl⟩ : syracuseStep 5834369 = 4375777) B4375777
theorem B1542419 : Blo 682313 1542419 := bstep (se 1 (by rfl) ⟨1156814, by rfl⟩ : syracuseStep 1542419 = 2313629) B2313629
theorem B1542815 : Blo 682313 1542815 := bstep (se 1 (by rfl) ⟨1157111, by rfl⟩ : syracuseStep 1542815 = 2314223) B2314223
theorem B2493089 : Blo 682313 2493089 := bstep (se 2 (by rfl) ⟨934908, by rfl⟩ : syracuseStep 2493089 = 1869817) B1869817
theorem B1543337 : Blo 682313 1543337 := bstep (se 2 (by rfl) ⟨578751, by rfl⟩ : syracuseStep 1543337 = 1157503) B1157503
theorem B1543679 : Blo 682313 1543679 := bstep (se 1 (by rfl) ⟨1157759, by rfl⟩ : syracuseStep 1543679 = 2315519) B2315519
theorem B790735 : Blo 682313 790735 := bstep (se 1 (by rfl) ⟨593051, by rfl⟩ : syracuseStep 790735 = 1186103) B1186103
theorem B159748307 : Blo 682313 159748307 := bstep (se 1 (by rfl) ⟨119811230, by rfl⟩ : syracuseStep 159748307 = 239622461) B239622461
theorem B2627201 : Blo 682313 2627201 := bstep (se 2 (by rfl) ⟨985200, by rfl⟩ : syracuseStep 2627201 = 1970401) B1970401
theorem B21370817 : Blo 682313 21370817 := bstep (se 2 (by rfl) ⟨8014056, by rfl⟩ : syracuseStep 21370817 = 16028113) B16028113
theorem B1153055 : Blo 682313 1153055 := bstep (se 1 (by rfl) ⟨864791, by rfl⟩ : syracuseStep 1153055 = 1729583) B1729583
theorem B1153183 : Blo 682313 1153183 := bstep (se 1 (by rfl) ⟨864887, by rfl⟩ : syracuseStep 1153183 = 1729775) B1729775
theorem B2627977 : Blo 682313 2627977 := bstep (se 2 (by rfl) ⟨985491, by rfl⟩ : syracuseStep 2627977 = 1970983) B1970983
theorem B3283355 : Blo 682313 3283355 := bstep (se 1 (by rfl) ⟨2462516, by rfl⟩ : syracuseStep 3283355 = 4925033) B4925033
theorem B2923883 : Blo 682313 2923883 := bstep (se 1 (by rfl) ⟨2192912, by rfl⟩ : syracuseStep 2923883 = 4385825) B4385825
theorem B1154729 : Blo 682313 1154729 := bstep (se 2 (by rfl) ⟨433023, by rfl⟩ : syracuseStep 1154729 = 866047) B866047
theorem B1154783 : Blo 682313 1154783 := bstep (se 1 (by rfl) ⟨866087, by rfl⟩ : syracuseStep 1154783 = 1732175) B1732175
theorem B6561593 : Blo 682313 6561593 := bstep (se 2 (by rfl) ⟨2460597, by rfl⟩ : syracuseStep 6561593 = 4921195) B4921195
theorem B15016033 : Blo 682313 15016033 := bstep (se 2 (by rfl) ⟨5631012, by rfl⟩ : syracuseStep 15016033 = 11262025) B11262025
theorem B1024127 : Blo 682313 1024127 := bstep (se 1 (by rfl) ⟨768095, by rfl⟩ : syracuseStep 1024127 = 1536191) B1536191
theorem B2400799 : Blo 682313 2400799 := bstep (se 1 (by rfl) ⟨1800599, by rfl⟩ : syracuseStep 2400799 = 3601199) B3601199
theorem B1581727 : Blo 682313 1581727 := bstep (se 1 (by rfl) ⟨1186295, by rfl⟩ : syracuseStep 1581727 = 2372591) B2372591
theorem B1024751 : Blo 682313 1024751 := bstep (se 1 (by rfl) ⟨768563, by rfl⟩ : syracuseStep 1024751 = 1537127) B1537127
theorem B3285755 : Blo 682313 3285755 := bstep (se 1 (by rfl) ⟨2464316, by rfl⟩ : syracuseStep 3285755 = 4928633) B4928633
theorem B9872255 : Blo 682313 9872255 := bstep (se 1 (by rfl) ⟨7404191, by rfl⟩ : syracuseStep 9872255 = 14808383) B14808383
theorem B1156423 : Blo 682313 1156423 := bstep (se 1 (by rfl) ⟨867317, by rfl⟩ : syracuseStep 1156423 = 1734635) B1734635
theorem B1025513 : Blo 682313 1025513 := bstep (se 2 (by rfl) ⟨384567, by rfl⟩ : syracuseStep 1025513 = 769135) B769135
theorem B730783 : Blo 682313 730783 := bstep (se 1 (by rfl) ⟨548087, by rfl⟩ : syracuseStep 730783 = 1096175) B1096175
theorem B1026089 : Blo 682313 1026089 := bstep (se 2 (by rfl) ⟨384783, by rfl⟩ : syracuseStep 1026089 = 769567) B769567
theorem B1157915 : Blo 682313 1157915 := bstep (se 1 (by rfl) ⟨868436, by rfl⟩ : syracuseStep 1157915 = 1736873) B1736873
theorem B66562985 : Blo 682313 66562985 := bstep (se 2 (by rfl) ⟨24961119, by rfl⟩ : syracuseStep 66562985 = 49922239) B49922239
theorem B2305259 : Blo 682313 2305259 := bstep (se 1 (by rfl) ⟨1728944, by rfl⟩ : syracuseStep 2305259 = 3457889) B3457889
theorem B863723 : Blo 682313 863723 := bstep (se 1 (by rfl) ⟨647792, by rfl⟩ : syracuseStep 863723 = 1295585) B1295585
theorem B1027631 : Blo 682313 1027631 := bstep (se 1 (by rfl) ⟨770723, by rfl⟩ : syracuseStep 1027631 = 1541447) B1541447
theorem B8793791 : Blo 682313 8793791 := bstep (se 1 (by rfl) ⟨6595343, by rfl⟩ : syracuseStep 8793791 = 13190687) B13190687
theorem B1093375 : Blo 682313 1093375 := bstep (se 1 (by rfl) ⟨820031, by rfl⟩ : syracuseStep 1093375 = 1640063) B1640063
theorem B224145629 : Blo 682313 224145629 := bstep (se 3 (by rfl) ⟨42027305, by rfl⟩ : syracuseStep 224145629 = 84054611) B84054611
theorem B2601679 : Blo 682313 2601679 := bstep (se 1 (by rfl) ⟨1951259, by rfl⟩ : syracuseStep 2601679 = 3902519) B3902519
theorem B3289967 : Blo 682313 3289967 := bstep (se 1 (by rfl) ⟨2467475, by rfl⟩ : syracuseStep 3289967 = 4934951) B4934951
theorem B14070847 : Blo 682313 14070847 := bstep (se 1 (by rfl) ⟨10553135, by rfl⟩ : syracuseStep 14070847 = 21106271) B21106271
theorem B11842847 : Blo 682313 11842847 := bstep (se 1 (by rfl) ⟨8882135, by rfl⟩ : syracuseStep 11842847 = 17764271) B17764271
theorem B10533071 : Blo 682313 10533071 := bstep (se 1 (by rfl) ⟨7899803, by rfl⟩ : syracuseStep 10533071 = 15799607) B15799607
theorem B33274111 : Blo 682313 33274111 := bstep (se 1 (by rfl) ⟨24955583, by rfl⟩ : syracuseStep 33274111 = 49911167) B49911167
theorem B2308985 : Blo 682313 2308985 := bstep (se 2 (by rfl) ⟨865869, by rfl⟩ : syracuseStep 2308985 = 1731739) B1731739
theorem B768991 : Blo 682313 768991 := bstep (se 1 (by rfl) ⟨576743, by rfl⟩ : syracuseStep 768991 = 1153487) B1153487
theorem B769639 : Blo 682313 769639 := bstep (se 1 (by rfl) ⟨577229, by rfl⟩ : syracuseStep 769639 = 1154459) B1154459
theorem B3456755 : Blo 682313 3456755 := bstep (se 1 (by rfl) ⟨2592566, by rfl⟩ : syracuseStep 3456755 = 5185133) B5185133
theorem B1851655 : Blo 682313 1851655 := bstep (se 1 (by rfl) ⟨1388741, by rfl⟩ : syracuseStep 1851655 = 2777483) B2777483
theorem B3293561 : Blo 682313 3293561 := bstep (se 2 (by rfl) ⟨1235085, by rfl⟩ : syracuseStep 3293561 = 2470171) B2470171
theorem B770791 : Blo 682313 770791 := bstep (se 1 (by rfl) ⟨578093, by rfl⟩ : syracuseStep 770791 = 1156187) B1156187
theorem B3458375 : Blo 682313 3458375 := bstep (se 1 (by rfl) ⟨2593781, by rfl⟩ : syracuseStep 3458375 = 5187563) B5187563
theorem B22136813 : Blo 682313 22136813 := bstep (se 3 (by rfl) ⟨4150652, by rfl⟩ : syracuseStep 22136813 = 8301305) B8301305
theorem B3459347 : Blo 682313 3459347 := bstep (se 1 (by rfl) ⟨2594510, by rfl⟩ : syracuseStep 3459347 = 5189021) B5189021
theorem B14798699 : Blo 682313 14798699 := bstep (se 1 (by rfl) ⟨11099024, by rfl⟩ : syracuseStep 14798699 = 22198049) B22198049
theorem B24400925 : Blo 682313 24400925 := bstep (se 3 (by rfl) ⟨4575173, by rfl⟩ : syracuseStep 24400925 = 9150347) B9150347
theorem B3462425 : Blo 682313 3462425 := bstep (se 2 (by rfl) ⟨1298409, by rfl⟩ : syracuseStep 3462425 = 2596819) B2596819
theorem B1758775 : Blo 682313 1758775 := bstep (se 1 (by rfl) ⟨1319081, by rfl⟩ : syracuseStep 1758775 = 2638163) B2638163
theorem B6313555 : Blo 682313 6313555 := bstep (se 1 (by rfl) ⟨4735166, by rfl⟩ : syracuseStep 6313555 = 9470333) B9470333
theorem B9885635 : Blo 682313 9885635 := bstep (se 1 (by rfl) ⟨7414226, by rfl⟩ : syracuseStep 9885635 = 14828453) B14828453
theorem B2316275 : Blo 682313 2316275 := bstep (se 1 (by rfl) ⟨1737206, by rfl⟩ : syracuseStep 2316275 = 3474413) B3474413
theorem B1301447 : Blo 682313 1301447 := bstep (se 1 (by rfl) ⟨976085, by rfl⟩ : syracuseStep 1301447 = 1952171) B1952171
theorem B2776477 : Blo 682313 2776477 := bstep (se 3 (by rfl) ⟨520589, by rfl⟩ : syracuseStep 2776477 = 1041179) B1041179
theorem B25026515 : Blo 682313 25026515 := bstep (se 1 (by rfl) ⟨18769886, by rfl⟩ : syracuseStep 25026515 = 37539773) B37539773
theorem B1729127 : Blo 682313 1729127 := bstep (se 1 (by rfl) ⟨1296845, by rfl⟩ : syracuseStep 1729127 = 2593691) B2593691
theorem B878239 : Blo 682313 878239 := bstep (se 1 (by rfl) ⟨658679, by rfl⟩ : syracuseStep 878239 = 1317359) B1317359
theorem B1730281 : Blo 682313 1730281 := bstep (se 2 (by rfl) ⟨648855, by rfl⟩ : syracuseStep 1730281 = 1297711) B1297711
theorem B1665019 : Blo 682313 1665019 := bstep (se 1 (by rfl) ⟨1248764, by rfl⟩ : syracuseStep 1665019 = 2497529) B2497529
theorem B3467447 : Blo 682313 3467447 := bstep (se 1 (by rfl) ⟨2600585, by rfl⟩ : syracuseStep 3467447 = 5201171) B5201171
theorem B682655 : Blo 682313 682655 := bstep (se 1 (by rfl) ⟨511991, by rfl⟩ : syracuseStep 682655 = 1023983) B1023983
theorem B1731233 : Blo 682313 1731233 := bstep (se 2 (by rfl) ⟨649212, by rfl⟩ : syracuseStep 1731233 = 1298425) B1298425
theorem B682855 : Blo 682313 682855 := bstep (se 1 (by rfl) ⟨512141, by rfl⟩ : syracuseStep 682855 = 1024283) B1024283
theorem B6581351 : Blo 682313 6581351 := bstep (se 1 (by rfl) ⟨4936013, by rfl⟩ : syracuseStep 6581351 = 9872027) B9872027
theorem B8908061 : Blo 682313 8908061 := bstep (se 3 (by rfl) ⟨1670261, by rfl⟩ : syracuseStep 8908061 = 3340523) B3340523
theorem B683423 : Blo 682313 683423 := bstep (se 1 (by rfl) ⟨512567, by rfl⟩ : syracuseStep 683423 = 1025135) B1025135
theorem B10546685 : Blo 682313 10546685 := bstep (se 3 (by rfl) ⟨1977503, by rfl⟩ : syracuseStep 10546685 = 3955007) B3955007
theorem B22179359 : Blo 682313 22179359 := bstep (se 1 (by rfl) ⟨16634519, by rfl⟩ : syracuseStep 22179359 = 33269039) B33269039
theorem B5533231 : Blo 682313 5533231 := bstep (se 1 (by rfl) ⟨4149923, by rfl⟩ : syracuseStep 5533231 = 8299847) B8299847
theorem B1667047 : Blo 682313 1667047 := bstep (se 1 (by rfl) ⟨1250285, by rfl⟩ : syracuseStep 1667047 = 2500571) B2500571
theorem B684103 : Blo 682313 684103 := bstep (se 1 (by rfl) ⟨513077, by rfl⟩ : syracuseStep 684103 = 1026155) B1026155
theorem B4387031 : Blo 682313 4387031 := bstep (se 1 (by rfl) ⟨3290273, by rfl⟩ : syracuseStep 4387031 = 6580547) B6580547
theorem B1733035 : Blo 682313 1733035 := bstep (se 1 (by rfl) ⟨1299776, by rfl⟩ : syracuseStep 1733035 = 2599553) B2599553
theorem B4387259 : Blo 682313 4387259 := bstep (se 1 (by rfl) ⟨3290444, by rfl⟩ : syracuseStep 4387259 = 6580889) B6580889
theorem B684571 : Blo 682313 684571 := bstep (se 1 (by rfl) ⟨513428, by rfl⟩ : syracuseStep 684571 = 1026857) B1026857
theorem B1733177 : Blo 682313 1733177 := bstep (se 2 (by rfl) ⟨649941, by rfl⟩ : syracuseStep 1733177 = 1299883) B1299883
theorem B1536731 : Blo 682313 1536731 := bstep (se 1 (by rfl) ⟨1152548, by rfl⟩ : syracuseStep 1536731 = 2305097) B2305097
theorem B684871 : Blo 682313 684871 := bstep (se 1 (by rfl) ⟨513653, by rfl⟩ : syracuseStep 684871 = 1027307) B1027307
theorem B2782187 : Blo 682313 2782187 := bstep (se 1 (by rfl) ⟨2086640, by rfl⟩ : syracuseStep 2782187 = 4173281) B4173281
theorem B1733663 : Blo 682313 1733663 := bstep (se 1 (by rfl) ⟨1300247, by rfl⟩ : syracuseStep 1733663 = 2600495) B2600495
theorem B685311 : Blo 682313 685311 := bstep (se 1 (by rfl) ⟨513983, by rfl⟩ : syracuseStep 685311 = 1027967) B1027967
theorem B56816963 : Blo 682313 56816963 := bstep (se 1 (by rfl) ⟨42612722, by rfl⟩ : syracuseStep 56816963 = 85225445) B85225445
theorem B4454369 : Blo 682313 4454369 := bstep (se 2 (by rfl) ⟨1670388, by rfl⟩ : syracuseStep 4454369 = 3340777) B3340777
theorem B1734767 : Blo 682313 1734767 := bstep (se 1 (by rfl) ⟨1301075, by rfl⟩ : syracuseStep 1734767 = 2602151) B2602151
theorem B686207 : Blo 682313 686207 := bstep (se 1 (by rfl) ⟨514655, by rfl⟩ : syracuseStep 686207 = 1029311) B1029311
theorem B1538441 : Blo 682313 1538441 := bstep (se 2 (by rfl) ⟨576915, by rfl⟩ : syracuseStep 1538441 = 1153831) B1153831
theorem B16481513 : Blo 682313 16481513 := bstep (se 2 (by rfl) ⟨6180567, by rfl⟩ : syracuseStep 16481513 = 12361135) B12361135
theorem B5832593 : Blo 682313 5832593 := bstep (se 2 (by rfl) ⟨2187222, by rfl⟩ : syracuseStep 5832593 = 4374445) B4374445
theorem B20021377 : Blo 682313 20021377 := bstep (se 2 (by rfl) ⟨7508016, by rfl⟩ : syracuseStep 20021377 = 15016033) B15016033
theorem B2195707 : Blo 682313 2195707 := bstep (se 1 (by rfl) ⟨1646780, by rfl⟩ : syracuseStep 2195707 = 3293561) B3293561
theorem B1541897 : Blo 682313 1541897 := bstep (se 2 (by rfl) ⟨578211, by rfl⟩ : syracuseStep 1541897 = 1156423) B1156423
theorem B9865799 : Blo 682313 9865799 := bstep (se 1 (by rfl) ⟨7399349, by rfl⟩ : syracuseStep 9865799 = 14798699) B14798699
theorem B106498871 : Blo 682313 106498871 := bstep (se 1 (by rfl) ⟨79874153, by rfl⟩ : syracuseStep 106498871 = 159748307) B159748307
theorem B6590423 : Blo 682313 6590423 := bstep (se 1 (by rfl) ⟨4942817, by rfl⟩ : syracuseStep 6590423 = 9885635) B9885635
theorem B1544183 : Blo 682313 1544183 := bstep (se 1 (by rfl) ⟨1158137, by rfl⟩ : syracuseStep 1544183 = 2316275) B2316275
theorem B7377641 : Blo 682313 7377641 := bstep (se 2 (by rfl) ⟨2766615, by rfl⟩ : syracuseStep 7377641 = 5533231) B5533231
theorem B56988845 : Blo 682313 56988845 := bstep (se 3 (by rfl) ⟨10685408, by rfl⟩ : syracuseStep 56988845 = 21370817) B21370817
theorem B16684343 : Blo 682313 16684343 := bstep (se 1 (by rfl) ⟨12513257, by rfl⟩ : syracuseStep 16684343 = 25026515) B25026515
theorem B1054313 : Blo 682313 1054313 := bstep (se 2 (by rfl) ⟨395367, by rfl⟩ : syracuseStep 1054313 = 790735) B790735
theorem B1152751 : Blo 682313 1152751 := bstep (se 1 (by rfl) ⟨864563, by rfl⟩ : syracuseStep 1152751 = 1729127) B1729127
theorem B1154155 : Blo 682313 1154155 := bstep (se 1 (by rfl) ⟨865616, by rfl⟩ : syracuseStep 1154155 = 1731233) B1731233
theorem B44375323 : Blo 682313 44375323 := bstep (se 1 (by rfl) ⟨33281492, by rfl⟩ : syracuseStep 44375323 = 66562985) B66562985
theorem B14786239 : Blo 682313 14786239 := bstep (se 1 (by rfl) ⟨11089679, by rfl⟩ : syracuseStep 14786239 = 22179359) B22179359
theorem B2924687 : Blo 682313 2924687 := bstep (se 1 (by rfl) ⟨2193515, by rfl⟩ : syracuseStep 2924687 = 4387031) B4387031
theorem B149430419 : Blo 682313 149430419 := bstep (se 1 (by rfl) ⟨112072814, by rfl⟩ : syracuseStep 149430419 = 224145629) B224145629
theorem B2924839 : Blo 682313 2924839 := bstep (se 1 (by rfl) ⟨2193629, by rfl⟩ : syracuseStep 2924839 = 4387259) B4387259
theorem B1155451 : Blo 682313 1155451 := bstep (se 1 (by rfl) ⟨866588, by rfl⟩ : syracuseStep 1155451 = 1733177) B1733177
theorem B1024487 : Blo 682313 1024487 := bstep (se 1 (by rfl) ⟨768365, by rfl⟩ : syracuseStep 1024487 = 1536731) B1536731
theorem B43950701 : Blo 682313 43950701 := bstep (se 3 (by rfl) ⟨8240756, by rfl⟩ : syracuseStep 43950701 = 16481513) B16481513
theorem B1155775 : Blo 682313 1155775 := bstep (se 1 (by rfl) ⟨866831, by rfl⟩ : syracuseStep 1155775 = 1733663) B1733663
theorem B2303261 : Blo 682313 2303261 := bstep (se 3 (by rfl) ⟨431861, by rfl⟩ : syracuseStep 2303261 = 863723) B863723
theorem B1025321 : Blo 682313 1025321 := bstep (se 2 (by rfl) ⟨384495, by rfl⟩ : syracuseStep 1025321 = 768991) B768991
theorem B1156511 : Blo 682313 1156511 := bstep (se 1 (by rfl) ⟨867383, by rfl⟩ : syracuseStep 1156511 = 1734767) B1734767
theorem B7022047 : Blo 682313 7022047 := bstep (se 1 (by rfl) ⟨5266535, by rfl⟩ : syracuseStep 7022047 = 10533071) B10533071
theorem B1025627 : Blo 682313 1025627 := bstep (se 1 (by rfl) ⟨769220, by rfl⟩ : syracuseStep 1025627 = 1538441) B1538441
theorem B1026185 : Blo 682313 1026185 := bstep (se 2 (by rfl) ⟨384819, by rfl⟩ : syracuseStep 1026185 = 769639) B769639
theorem B2304503 : Blo 682313 2304503 := bstep (se 1 (by rfl) ⟨1728377, by rfl⟩ : syracuseStep 2304503 = 3456755) B3456755
theorem B1026791 : Blo 682313 1026791 := bstep (se 1 (by rfl) ⟨770093, by rfl⟩ : syracuseStep 1026791 = 1540187) B1540187
theorem B2468873 : Blo 682313 2468873 := bstep (se 2 (by rfl) ⟨925827, by rfl⟩ : syracuseStep 2468873 = 1851655) B1851655
theorem B1027247 : Blo 682313 1027247 := bstep (se 1 (by rfl) ⟨770435, by rfl⟩ : syracuseStep 1027247 = 1540871) B1540871
theorem B2108969 : Blo 682313 2108969 := bstep (se 2 (by rfl) ⟨790863, by rfl⟩ : syracuseStep 2108969 = 1581727) B1581727
theorem B2305583 : Blo 682313 2305583 := bstep (se 1 (by rfl) ⟨1729187, by rfl⟩ : syracuseStep 2305583 = 3458375) B3458375
theorem B1027721 : Blo 682313 1027721 := bstep (se 2 (by rfl) ⟨385395, by rfl⟩ : syracuseStep 1027721 = 770791) B770791
theorem B1027739 : Blo 682313 1027739 := bstep (se 1 (by rfl) ⟨770804, by rfl⟩ : syracuseStep 1027739 = 1541609) B1541609
theorem B14757875 : Blo 682313 14757875 := bstep (se 1 (by rfl) ⟨11068406, by rfl⟩ : syracuseStep 14757875 = 22136813) B22136813
theorem B7778429 : Blo 682313 7778429 := bstep (se 3 (by rfl) ⟨1458455, by rfl⟩ : syracuseStep 7778429 = 2916911) B2916911
theorem B2306231 : Blo 682313 2306231 := bstep (se 1 (by rfl) ⟨1729673, by rfl⟩ : syracuseStep 2306231 = 3459347) B3459347
theorem B1028279 : Blo 682313 1028279 := bstep (se 1 (by rfl) ⟨771209, by rfl⟩ : syracuseStep 1028279 = 1542419) B1542419
theorem B1028543 : Blo 682313 1028543 := bstep (se 1 (by rfl) ⟨771407, by rfl⟩ : syracuseStep 1028543 = 1542815) B1542815
theorem B1028891 : Blo 682313 1028891 := bstep (se 1 (by rfl) ⟨771668, by rfl⟩ : syracuseStep 1028891 = 1543337) B1543337
theorem B2307041 : Blo 682313 2307041 := bstep (se 2 (by rfl) ⟨865140, by rfl⟩ : syracuseStep 2307041 = 1730281) B1730281
theorem B1029119 : Blo 682313 1029119 := bstep (se 1 (by rfl) ⟨771839, by rfl⟩ : syracuseStep 1029119 = 1543679) B1543679
theorem B16267283 : Blo 682313 16267283 := bstep (se 1 (by rfl) ⟨12200462, by rfl⟩ : syracuseStep 16267283 = 24400925) B24400925
theorem B2308283 : Blo 682313 2308283 := bstep (se 1 (by rfl) ⟨1731212, by rfl⟩ : syracuseStep 2308283 = 3462425) B3462425
theorem B1751467 : Blo 682313 1751467 := bstep (se 1 (by rfl) ⟨1313600, by rfl⟩ : syracuseStep 1751467 = 2627201) B2627201
theorem B768703 : Blo 682313 768703 := bstep (se 1 (by rfl) ⟨576527, by rfl⟩ : syracuseStep 768703 = 1153055) B1153055
theorem B1949255 : Blo 682313 1949255 := bstep (se 1 (by rfl) ⟨1461941, by rfl⟩ : syracuseStep 1949255 = 2923883) B2923883
theorem B1457833 : Blo 682313 1457833 := bstep (se 2 (by rfl) ⟨546687, by rfl⟩ : syracuseStep 1457833 = 1093375) B1093375
theorem B769819 : Blo 682313 769819 := bstep (se 1 (by rfl) ⟨577364, by rfl⟩ : syracuseStep 769819 = 1154729) B1154729
theorem B769855 : Blo 682313 769855 := bstep (se 1 (by rfl) ⟨577391, by rfl⟩ : syracuseStep 769855 = 1154783) B1154783
theorem B4374395 : Blo 682313 4374395 := bstep (se 1 (by rfl) ⟨3280796, by rfl⟩ : syracuseStep 4374395 = 6561593) B6561593
theorem B2310713 : Blo 682313 2310713 := bstep (se 2 (by rfl) ⟨866517, by rfl⟩ : syracuseStep 2310713 = 1733035) B1733035
theorem B18761129 : Blo 682313 18761129 := bstep (se 2 (by rfl) ⟨7035423, by rfl⟩ : syracuseStep 18761129 = 14070847) B14070847
theorem B2311631 : Blo 682313 2311631 := bstep (se 1 (by rfl) ⟨1733723, by rfl⟩ : syracuseStep 2311631 = 3467447) B3467447
theorem B771943 : Blo 682313 771943 := bstep (se 1 (by rfl) ⟨578957, by rfl⟩ : syracuseStep 771943 = 1157915) B1157915
theorem B2345033 : Blo 682313 2345033 := bstep (se 2 (by rfl) ⟨879387, by rfl⟩ : syracuseStep 2345033 = 1758775) B1758775
theorem B7031123 : Blo 682313 7031123 := bstep (se 1 (by rfl) ⟨5273342, by rfl⟩ : syracuseStep 7031123 = 10546685) B10546685
theorem B1854791 : Blo 682313 1854791 := bstep (se 1 (by rfl) ⟨1391093, by rfl⟩ : syracuseStep 1854791 = 2782187) B2782187
theorem B2969579 : Blo 682313 2969579 := bstep (se 1 (by rfl) ⟨2227184, by rfl⟩ : syracuseStep 2969579 = 4454369) B4454369
theorem B3888395 : Blo 682313 3888395 := bstep (se 1 (by rfl) ⟨2916296, by rfl⟩ : syracuseStep 3888395 = 5832593) B5832593
theorem B5199227 : Blo 682313 5199227 := bstep (se 1 (by rfl) ⟨3899420, by rfl⟩ : syracuseStep 5199227 = 7798841) B7798841
theorem B2315735 : Blo 682313 2315735 := bstep (se 1 (by rfl) ⟨1736801, by rfl⟩ : syracuseStep 2315735 = 3473603) B3473603
theorem B3201065 : Blo 682313 3201065 := bstep (se 2 (by rfl) ⟨1200399, by rfl⟩ : syracuseStep 3201065 = 2400799) B2400799
theorem B3889579 : Blo 682313 3889579 := bstep (se 1 (by rfl) ⟨2917184, by rfl⟩ : syracuseStep 3889579 = 5834369) B5834369
theorem B1662059 : Blo 682313 1662059 := bstep (se 1 (by rfl) ⟨1246544, by rfl⟩ : syracuseStep 1662059 = 2493089) B2493089
theorem B974377 : Blo 682313 974377 := bstep (se 2 (by rfl) ⟨365391, by rfl⟩ : syracuseStep 974377 = 730783) B730783
theorem B1170985 : Blo 682313 1170985 := bstep (se 2 (by rfl) ⟨439119, by rfl⟩ : syracuseStep 1170985 = 878239) B878239
theorem B2220025 : Blo 682313 2220025 := bstep (se 2 (by rfl) ⟨832509, by rfl⟩ : syracuseStep 2220025 = 1665019) B1665019
theorem B2188903 : Blo 682313 2188903 := bstep (se 1 (by rfl) ⟨1641677, by rfl⟩ : syracuseStep 2188903 = 3283355) B3283355
theorem B2222729 : Blo 682313 2222729 := bstep (se 2 (by rfl) ⟨833523, by rfl⟩ : syracuseStep 2222729 = 1667047) B1667047
theorem B682751 : Blo 682313 682751 := bstep (se 1 (by rfl) ⟨512063, by rfl⟩ : syracuseStep 682751 = 1024127) B1024127
theorem B683167 : Blo 682313 683167 := bstep (se 1 (by rfl) ⟨512375, by rfl⟩ : syracuseStep 683167 = 1024751) B1024751
theorem B2190503 : Blo 682313 2190503 := bstep (se 1 (by rfl) ⟨1642877, by rfl⟩ : syracuseStep 2190503 = 3285755) B3285755
theorem B6581503 : Blo 682313 6581503 := bstep (se 1 (by rfl) ⟨4936127, by rfl⟩ : syracuseStep 6581503 = 9872255) B9872255
theorem B3468905 : Blo 682313 3468905 := bstep (se 2 (by rfl) ⟨1300839, by rfl⟩ : syracuseStep 3468905 = 2601679) B2601679
theorem B683675 : Blo 682313 683675 := bstep (se 1 (by rfl) ⟨512756, by rfl⟩ : syracuseStep 683675 = 1025513) B1025513
theorem B684059 : Blo 682313 684059 := bstep (se 1 (by rfl) ⟨513044, by rfl⟩ : syracuseStep 684059 = 1026089) B1026089
theorem B4387567 : Blo 682313 4387567 := bstep (se 1 (by rfl) ⟨3290675, by rfl⟩ : syracuseStep 4387567 = 6581351) B6581351
theorem B8418073 : Blo 682313 8418073 := bstep (se 2 (by rfl) ⟨3156777, by rfl⟩ : syracuseStep 8418073 = 6313555) B6313555
theorem B1536839 : Blo 682313 1536839 := bstep (se 1 (by rfl) ⟨1152629, by rfl⟩ : syracuseStep 1536839 = 2305259) B2305259
theorem B685087 : Blo 682313 685087 := bstep (se 1 (by rfl) ⟨513815, by rfl⟩ : syracuseStep 685087 = 1027631) B1027631
theorem B5862527 : Blo 682313 5862527 := bstep (se 1 (by rfl) ⟨4396895, by rfl⟩ : syracuseStep 5862527 = 8793791) B8793791
theorem B3470525 : Blo 682313 3470525 := bstep (se 3 (by rfl) ⟨650723, by rfl⟩ : syracuseStep 3470525 = 1301447) B1301447
theorem B1537577 : Blo 682313 1537577 := bstep (se 2 (by rfl) ⟨576591, by rfl⟩ : syracuseStep 1537577 = 1153183) B1153183
theorem B44365481 : Blo 682313 44365481 := bstep (se 2 (by rfl) ⟨16637055, by rfl⟩ : syracuseStep 44365481 = 33274111) B33274111
theorem B3503969 : Blo 682313 3503969 := bstep (se 2 (by rfl) ⟨1313988, by rfl⟩ : syracuseStep 3503969 = 2627977) B2627977
theorem B2193311 : Blo 682313 2193311 := bstep (se 1 (by rfl) ⟨1644983, by rfl⟩ : syracuseStep 2193311 = 3289967) B3289967
theorem B23754829 : Blo 682313 23754829 := bstep (se 3 (by rfl) ⟨4454030, by rfl⟩ : syracuseStep 23754829 = 8908061) B8908061
theorem B7895231 : Blo 682313 7895231 := bstep (se 1 (by rfl) ⟨5921423, by rfl⟩ : syracuseStep 7895231 = 11842847) B11842847
theorem B37877975 : Blo 682313 37877975 := bstep (se 1 (by rfl) ⟨28408481, by rfl⟩ : syracuseStep 37877975 = 56816963) B56816963
theorem B3701969 : Blo 682313 3701969 := bstep (se 2 (by rfl) ⟨1388238, by rfl⟩ : syracuseStep 3701969 = 2776477) B2776477
theorem B1539323 : Blo 682313 1539323 := bstep (se 1 (by rfl) ⟨1154492, by rfl⟩ : syracuseStep 1539323 = 2308985) B2308985
theorem B1540475 : Blo 682313 1540475 := bstep (se 1 (by rfl) ⟨1155356, by rfl⟩ : syracuseStep 1540475 = 2310713) B2310713
theorem B3899785 : Blo 682313 3899785 := bstep (se 2 (by rfl) ⟨1462419, by rfl⟩ : syracuseStep 3899785 = 2924839) B2924839
theorem B1540601 : Blo 682313 1540601 := bstep (se 2 (by rfl) ⟨577725, by rfl⟩ : syracuseStep 1540601 = 1155451) B1155451
theorem B1541033 : Blo 682313 1541033 := bstep (se 2 (by rfl) ⟨577887, by rfl⟩ : syracuseStep 1541033 = 1155775) B1155775
theorem B1541087 : Blo 682313 1541087 := bstep (se 1 (by rfl) ⟨1155815, by rfl⟩ : syracuseStep 1541087 = 2311631) B2311631
theorem B4687415 : Blo 682313 4687415 := bstep (se 1 (by rfl) ⟨3515561, by rfl⟩ : syracuseStep 4687415 = 7031123) B7031123
theorem B2918537 : Blo 682313 2918537 := bstep (se 2 (by rfl) ⟨1094451, by rfl⟩ : syracuseStep 2918537 = 2188903) B2188903
theorem B4393615 : Blo 682313 4393615 := bstep (se 1 (by rfl) ⟨3295211, by rfl⟩ : syracuseStep 4393615 = 6590423) B6590423
theorem B4918427 : Blo 682313 4918427 := bstep (se 1 (by rfl) ⟨3688820, by rfl⟩ : syracuseStep 4918427 = 7377641) B7377641
theorem B2592263 : Blo 682313 2592263 := bstep (se 1 (by rfl) ⟨1944197, by rfl⟩ : syracuseStep 2592263 = 3888395) B3888395
theorem B1543823 : Blo 682313 1543823 := bstep (se 1 (by rfl) ⟨1157867, by rfl⟩ : syracuseStep 1543823 = 2315735) B2315735
theorem B2134043 : Blo 682313 2134043 := bstep (se 1 (by rfl) ⟨1600532, by rfl⟩ : syracuseStep 2134043 = 3201065) B3201065
theorem B99620279 : Blo 682313 99620279 := bstep (se 1 (by rfl) ⟨74715209, by rfl⟩ : syracuseStep 99620279 = 149430419) B149430419
theorem B29300467 : Blo 682313 29300467 := bstep (se 1 (by rfl) ⟨21975350, by rfl⟩ : syracuseStep 29300467 = 43950701) B43950701
theorem B1481819 : Blo 682313 1481819 := bstep (se 1 (by rfl) ⟨1111364, by rfl⟩ : syracuseStep 1481819 = 2222729) B2222729
theorem B1645915 : Blo 682313 1645915 := bstep (se 1 (by rfl) ⟨1234436, by rfl⟩ : syracuseStep 1645915 = 2468873) B2468873
theorem B9838583 : Blo 682313 9838583 := bstep (se 1 (by rfl) ⟨7378937, by rfl⟩ : syracuseStep 9838583 = 14757875) B14757875
theorem B5185619 : Blo 682313 5185619 := bstep (se 1 (by rfl) ⟨3889214, by rfl⟩ : syracuseStep 5185619 = 7778429) B7778429
theorem B4432157 : Blo 682313 4432157 := bstep (se 3 (by rfl) ⟨831029, by rfl⟩ : syracuseStep 4432157 = 1662059) B1662059
theorem B5841341 : Blo 682313 5841341 := bstep (se 3 (by rfl) ⟨1095251, by rfl⟩ : syracuseStep 5841341 = 2190503) B2190503
theorem B1024559 : Blo 682313 1024559 := bstep (se 1 (by rfl) ⟨768419, by rfl⟩ : syracuseStep 1024559 = 1536839) B1536839
theorem B2335289 : Blo 682313 2335289 := bstep (se 2 (by rfl) ⟨875733, by rfl⟩ : syracuseStep 2335289 = 1751467) B1751467
theorem B5186105 : Blo 682313 5186105 := bstep (se 2 (by rfl) ⟨1944789, by rfl⟩ : syracuseStep 5186105 = 3889579) B3889579
theorem B3908351 : Blo 682313 3908351 := bstep (se 1 (by rfl) ⟨2931263, by rfl⟩ : syracuseStep 3908351 = 5862527) B5862527
theorem B1024937 : Blo 682313 1024937 := bstep (se 2 (by rfl) ⟨384351, by rfl⟩ : syracuseStep 1024937 = 768703) B768703
theorem B1025051 : Blo 682313 1025051 := bstep (se 1 (by rfl) ⟨768788, by rfl⟩ : syracuseStep 1025051 = 1537577) B1537577
theorem B2335979 : Blo 682313 2335979 := bstep (se 1 (by rfl) ⟨1751984, by rfl⟩ : syracuseStep 2335979 = 3503969) B3503969
theorem B2467979 : Blo 682313 2467979 := bstep (se 1 (by rfl) ⟨1850984, by rfl⟩ : syracuseStep 2467979 = 3701969) B3701969
theorem B1026215 : Blo 682313 1026215 := bstep (se 1 (by rfl) ⟨769661, by rfl⟩ : syracuseStep 1026215 = 1539323) B1539323
theorem B1943777 : Blo 682313 1943777 := bstep (se 2 (by rfl) ⟨728916, by rfl⟩ : syracuseStep 1943777 = 1457833) B1457833
theorem B1026425 : Blo 682313 1026425 := bstep (se 2 (by rfl) ⟨384909, by rfl⟩ : syracuseStep 1026425 = 769819) B769819
theorem B1026473 : Blo 682313 1026473 := bstep (se 2 (by rfl) ⟨384927, by rfl⟩ : syracuseStep 1026473 = 769855) B769855
theorem B2960033 : Blo 682313 2960033 := bstep (se 2 (by rfl) ⟨1110012, by rfl⟩ : syracuseStep 2960033 = 2220025) B2220025
theorem B2927609 : Blo 682313 2927609 := bstep (se 2 (by rfl) ⟨1097853, by rfl⟩ : syracuseStep 2927609 = 2195707) B2195707
theorem B1027931 : Blo 682313 1027931 := bstep (se 1 (by rfl) ⟨770948, by rfl⟩ : syracuseStep 1027931 = 1541897) B1541897
theorem B1029257 : Blo 682313 1029257 := bstep (se 2 (by rfl) ⟨385971, by rfl⟩ : syracuseStep 1029257 = 771943) B771943
theorem B1029455 : Blo 682313 1029455 := bstep (se 1 (by rfl) ⟨772091, by rfl⟩ : syracuseStep 1029455 = 1544183) B1544183
theorem B37992563 : Blo 682313 37992563 := bstep (se 1 (by rfl) ⟨28494422, by rfl⟩ : syracuseStep 37992563 = 56988845) B56988845
theorem B11122895 : Blo 682313 11122895 := bstep (se 1 (by rfl) ⟨8342171, by rfl⟩ : syracuseStep 11122895 = 16684343) B16684343
theorem B702875 : Blo 682313 702875 := bstep (se 1 (by rfl) ⟨527156, by rfl⟩ : syracuseStep 702875 = 1054313) B1054313
theorem B1949791 : Blo 682313 1949791 := bstep (se 1 (by rfl) ⟨1462343, by rfl⟩ : syracuseStep 1949791 = 2924687) B2924687
theorem B771007 : Blo 682313 771007 := bstep (se 1 (by rfl) ⟨578255, by rfl⟩ : syracuseStep 771007 = 1156511) B1156511
theorem B5850089 : Blo 682313 5850089 := bstep (se 2 (by rfl) ⟨2193783, by rfl⟩ : syracuseStep 5850089 = 4387567) B4387567
theorem B11224097 : Blo 682313 11224097 := bstep (se 2 (by rfl) ⟨4209036, by rfl⟩ : syracuseStep 11224097 = 8418073) B8418073
theorem B2312603 : Blo 682313 2312603 := bstep (se 1 (by rfl) ⟨1734452, by rfl⟩ : syracuseStep 2312603 = 3468905) B3468905
theorem B31673105 : Blo 682313 31673105 := bstep (se 2 (by rfl) ⟨11877414, by rfl⟩ : syracuseStep 31673105 = 23754829) B23754829
theorem B2313683 : Blo 682313 2313683 := bstep (se 1 (by rfl) ⟨1735262, by rfl⟩ : syracuseStep 2313683 = 3470525) B3470525
theorem B29576987 : Blo 682313 29576987 := bstep (se 1 (by rfl) ⟨22182740, by rfl⟩ : syracuseStep 29576987 = 44365481) B44365481
theorem B1462207 : Blo 682313 1462207 := bstep (se 1 (by rfl) ⟨1096655, by rfl⟩ : syracuseStep 1462207 = 2193311) B2193311
theorem B5263487 : Blo 682313 5263487 := bstep (se 1 (by rfl) ⟨3947615, by rfl⟩ : syracuseStep 5263487 = 7895231) B7895231
theorem B25251983 : Blo 682313 25251983 := bstep (se 1 (by rfl) ⟨18938987, by rfl⟩ : syracuseStep 25251983 = 37877975) B37877975
theorem B59167097 : Blo 682313 59167097 := bstep (se 2 (by rfl) ⟨22187661, by rfl⟩ : syracuseStep 59167097 = 44375323) B44375323
theorem B1299169 : Blo 682313 1299169 := bstep (se 2 (by rfl) ⟨487188, by rfl⟩ : syracuseStep 1299169 = 974377) B974377
theorem B1561313 : Blo 682313 1561313 := bstep (se 2 (by rfl) ⟨585492, by rfl⟩ : syracuseStep 1561313 = 1170985) B1170985
theorem B19714985 : Blo 682313 19714985 := bstep (se 2 (by rfl) ⟨7393119, by rfl⟩ : syracuseStep 19714985 = 14786239) B14786239
theorem B1299503 : Blo 682313 1299503 := bstep (se 1 (by rfl) ⟨974627, by rfl⟩ : syracuseStep 1299503 = 1949255) B1949255
theorem B7918877 : Blo 682313 7918877 := bstep (se 3 (by rfl) ⟨1484789, by rfl⟩ : syracuseStep 7918877 = 2969579) B2969579
theorem B26695169 : Blo 682313 26695169 := bstep (se 2 (by rfl) ⟨10010688, by rfl⟩ : syracuseStep 26695169 = 20021377) B20021377
theorem B12507419 : Blo 682313 12507419 := bstep (se 1 (by rfl) ⟨9380564, by rfl⟩ : syracuseStep 12507419 = 18761129) B18761129
theorem B1563355 : Blo 682313 1563355 := bstep (se 1 (by rfl) ⟨1172516, by rfl⟩ : syracuseStep 1563355 = 2345033) B2345033
theorem B6577199 : Blo 682313 6577199 := bstep (se 1 (by rfl) ⟨4932899, by rfl⟩ : syracuseStep 6577199 = 9865799) B9865799
theorem B70999247 : Blo 682313 70999247 := bstep (se 1 (by rfl) ⟨53249435, by rfl⟩ : syracuseStep 70999247 = 106498871) B106498871
theorem B9362729 : Blo 682313 9362729 := bstep (se 2 (by rfl) ⟨3511023, by rfl⟩ : syracuseStep 9362729 = 7022047) B7022047
theorem B1236527 : Blo 682313 1236527 := bstep (se 1 (by rfl) ⟨927395, by rfl⟩ : syracuseStep 1236527 = 1854791) B1854791
theorem B3466151 : Blo 682313 3466151 := bstep (se 1 (by rfl) ⟨2599613, by rfl⟩ : syracuseStep 3466151 = 5199227) B5199227
theorem B8775337 : Blo 682313 8775337 := bstep (se 2 (by rfl) ⟨3290751, by rfl⟩ : syracuseStep 8775337 = 6581503) B6581503
theorem B682991 : Blo 682313 682991 := bstep (se 1 (by rfl) ⟨512243, by rfl⟩ : syracuseStep 682991 = 1024487) B1024487
theorem B1535507 : Blo 682313 1535507 := bstep (se 1 (by rfl) ⟨1151630, by rfl⟩ : syracuseStep 1535507 = 2303261) B2303261
theorem B683547 : Blo 682313 683547 := bstep (se 1 (by rfl) ⟨512660, by rfl⟩ : syracuseStep 683547 = 1025321) B1025321
theorem B683751 : Blo 682313 683751 := bstep (se 1 (by rfl) ⟨512813, by rfl⟩ : syracuseStep 683751 = 1025627) B1025627
theorem B684123 : Blo 682313 684123 := bstep (se 1 (by rfl) ⟨513092, by rfl⟩ : syracuseStep 684123 = 1026185) B1026185
theorem B1536335 : Blo 682313 1536335 := bstep (se 1 (by rfl) ⟨1152251, by rfl⟩ : syracuseStep 1536335 = 2304503) B2304503
theorem B684527 : Blo 682313 684527 := bstep (se 1 (by rfl) ⟨513395, by rfl⟩ : syracuseStep 684527 = 1026791) B1026791
theorem B684831 : Blo 682313 684831 := bstep (se 1 (by rfl) ⟨513623, by rfl⟩ : syracuseStep 684831 = 1027247) B1027247
theorem B1537001 : Blo 682313 1537001 := bstep (se 2 (by rfl) ⟨576375, by rfl⟩ : syracuseStep 1537001 = 1152751) B1152751
theorem B1405979 : Blo 682313 1405979 := bstep (se 1 (by rfl) ⟨1054484, by rfl⟩ : syracuseStep 1405979 = 2108969) B2108969
theorem B1537055 : Blo 682313 1537055 := bstep (se 1 (by rfl) ⟨1152791, by rfl⟩ : syracuseStep 1537055 = 2305583) B2305583
theorem B685147 : Blo 682313 685147 := bstep (se 1 (by rfl) ⟨513860, by rfl⟩ : syracuseStep 685147 = 1027721) B1027721
theorem B685159 : Blo 682313 685159 := bstep (se 1 (by rfl) ⟨513869, by rfl⟩ : syracuseStep 685159 = 1027739) B1027739
theorem B1537487 : Blo 682313 1537487 := bstep (se 1 (by rfl) ⟨1153115, by rfl⟩ : syracuseStep 1537487 = 2306231) B2306231
theorem B685519 : Blo 682313 685519 := bstep (se 1 (by rfl) ⟨514139, by rfl⟩ : syracuseStep 685519 = 1028279) B1028279
theorem B685695 : Blo 682313 685695 := bstep (se 1 (by rfl) ⟨514271, by rfl⟩ : syracuseStep 685695 = 1028543) B1028543
theorem B685927 : Blo 682313 685927 := bstep (se 1 (by rfl) ⟨514445, by rfl⟩ : syracuseStep 685927 = 1028891) B1028891
theorem B1538027 : Blo 682313 1538027 := bstep (se 1 (by rfl) ⟨1153520, by rfl⟩ : syracuseStep 1538027 = 2307041) B2307041
theorem B686079 : Blo 682313 686079 := bstep (se 1 (by rfl) ⟨514559, by rfl⟩ : syracuseStep 686079 = 1029119) B1029119
theorem B10844855 : Blo 682313 10844855 := bstep (se 1 (by rfl) ⟨8133641, by rfl⟩ : syracuseStep 10844855 = 16267283) B16267283
theorem B1538855 : Blo 682313 1538855 := bstep (se 1 (by rfl) ⟨1154141, by rfl⟩ : syracuseStep 1538855 = 2308283) B2308283
theorem B1538873 : Blo 682313 1538873 := bstep (se 2 (by rfl) ⟨577077, by rfl⟩ : syracuseStep 1538873 = 1154155) B1154155
theorem B2916263 : Blo 682313 2916263 := bstep (se 1 (by rfl) ⟨2187197, by rfl⟩ : syracuseStep 2916263 = 4374395) B4374395
theorem B3900059 : Blo 682313 3900059 := bstep (se 1 (by rfl) ⟨2925044, by rfl⟩ : syracuseStep 3900059 = 5850089) B5850089
theorem B6227437 : Blo 682313 6227437 := bstep (se 3 (by rfl) ⟨1167644, by rfl⟩ : syracuseStep 6227437 = 2335289) B2335289
theorem B1541735 : Blo 682313 1541735 := bstep (se 1 (by rfl) ⟨1156301, by rfl⟩ : syracuseStep 1541735 = 2312603) B2312603
theorem B4163501 : Blo 682313 4163501 := bstep (se 3 (by rfl) ⟨780656, by rfl⟩ : syracuseStep 4163501 = 1561313) B1561313
theorem B3278951 : Blo 682313 3278951 := bstep (se 1 (by rfl) ⟨2459213, by rfl⟩ : syracuseStep 3278951 = 4918427) B4918427
theorem B11700449 : Blo 682313 11700449 := bstep (se 2 (by rfl) ⟨4387668, by rfl⟩ : syracuseStep 11700449 = 8775337) B8775337
theorem B1542455 : Blo 682313 1542455 := bstep (se 1 (by rfl) ⟨1156841, by rfl⟩ : syracuseStep 1542455 = 2313683) B2313683
theorem B3508991 : Blo 682313 3508991 := bstep (se 1 (by rfl) ⟨2631743, by rfl⟩ : syracuseStep 3508991 = 5263487) B5263487
theorem B13143323 : Blo 682313 13143323 := bstep (se 1 (by rfl) ⟨9857492, by rfl⟩ : syracuseStep 13143323 = 19714985) B19714985
theorem B5279251 : Blo 682313 5279251 := bstep (se 1 (by rfl) ⟨3959438, by rfl⟩ : syracuseStep 5279251 = 7918877) B7918877
theorem B17796779 : Blo 682313 17796779 := bstep (se 1 (by rfl) ⟨13347584, by rfl⟩ : syracuseStep 17796779 = 26695169) B26695169
theorem B824351 : Blo 682313 824351 := bstep (se 1 (by rfl) ⟨618263, by rfl⟩ : syracuseStep 824351 = 1236527) B1236527
theorem B6559055 : Blo 682313 6559055 := bstep (se 1 (by rfl) ⟨4919291, by rfl⟩ : syracuseStep 6559055 = 9838583) B9838583
theorem B2954771 : Blo 682313 2954771 := bstep (se 1 (by rfl) ⟨2216078, by rfl⟩ : syracuseStep 2954771 = 4432157) B4432157
theorem B1874333 : Blo 682313 1874333 := bstep (se 3 (by rfl) ⟨351437, by rfl⟩ : syracuseStep 1874333 = 702875) B702875
theorem B1645319 : Blo 682313 1645319 := bstep (se 1 (by rfl) ⟨1233989, by rfl⟩ : syracuseStep 1645319 = 2467979) B2467979
theorem B39067289 : Blo 682313 39067289 := bstep (se 2 (by rfl) ⟨14650233, by rfl⟩ : syracuseStep 39067289 = 29300467) B29300467
theorem B1023671 : Blo 682313 1023671 := bstep (se 1 (by rfl) ⟨767753, by rfl⟩ : syracuseStep 1023671 = 1535507) B1535507
theorem B1024223 : Blo 682313 1024223 := bstep (se 1 (by rfl) ⟨768167, by rfl⟩ : syracuseStep 1024223 = 1536335) B1536335
theorem B1024667 : Blo 682313 1024667 := bstep (se 1 (by rfl) ⟨768500, by rfl⟩ : syracuseStep 1024667 = 1537001) B1537001
theorem B1024703 : Blo 682313 1024703 := bstep (se 1 (by rfl) ⟨768527, by rfl⟩ : syracuseStep 1024703 = 1537055) B1537055
theorem B1024991 : Blo 682313 1024991 := bstep (se 1 (by rfl) ⟨768743, by rfl⟩ : syracuseStep 1024991 = 1537487) B1537487
theorem B1025351 : Blo 682313 1025351 := bstep (se 1 (by rfl) ⟨769013, by rfl⟩ : syracuseStep 1025351 = 1538027) B1538027
theorem B7415263 : Blo 682313 7415263 := bstep (se 1 (by rfl) ⟨5561447, by rfl⟩ : syracuseStep 7415263 = 11122895) B11122895
theorem B1025903 : Blo 682313 1025903 := bstep (se 1 (by rfl) ⟨769427, by rfl⟩ : syracuseStep 1025903 = 1538855) B1538855
theorem B1025915 : Blo 682313 1025915 := bstep (se 1 (by rfl) ⟨769436, by rfl⟩ : syracuseStep 1025915 = 1538873) B1538873
theorem B1944175 : Blo 682313 1944175 := bstep (se 1 (by rfl) ⟨1458131, by rfl⟩ : syracuseStep 1944175 = 2916263) B2916263
theorem B2599721 : Blo 682313 2599721 := bstep (se 2 (by rfl) ⟨974895, by rfl⟩ : syracuseStep 2599721 = 1949791) B1949791
theorem B1026983 : Blo 682313 1026983 := bstep (se 1 (by rfl) ⟨770237, by rfl⟩ : syracuseStep 1026983 = 1540475) B1540475
theorem B1027067 : Blo 682313 1027067 := bstep (se 1 (by rfl) ⟨770300, by rfl⟩ : syracuseStep 1027067 = 1540601) B1540601
theorem B1027355 : Blo 682313 1027355 := bstep (se 1 (by rfl) ⟨770516, by rfl⟩ : syracuseStep 1027355 = 1541033) B1541033
theorem B1027391 : Blo 682313 1027391 := bstep (se 1 (by rfl) ⟨770543, by rfl⟩ : syracuseStep 1027391 = 1541087) B1541087
theorem B7482731 : Blo 682313 7482731 := bstep (se 1 (by rfl) ⟨5612048, by rfl⟩ : syracuseStep 7482731 = 11224097) B11224097
theorem B3124943 : Blo 682313 3124943 := bstep (se 1 (by rfl) ⟨2343707, by rfl⟩ : syracuseStep 3124943 = 4687415) B4687415
theorem B1028009 : Blo 682313 1028009 := bstep (se 2 (by rfl) ⟨385503, by rfl⟩ : syracuseStep 1028009 = 771007) B771007
theorem B1945691 : Blo 682313 1945691 := bstep (se 1 (by rfl) ⟨1459268, by rfl⟩ : syracuseStep 1945691 = 2918537) B2918537
theorem B21115403 : Blo 682313 21115403 := bstep (se 1 (by rfl) ⟨15836552, by rfl⟩ : syracuseStep 21115403 = 31673105) B31673105
theorem B1029215 : Blo 682313 1029215 := bstep (se 1 (by rfl) ⟨771911, by rfl⟩ : syracuseStep 1029215 = 1543823) B1543823
theorem B1422695 : Blo 682313 1422695 := bstep (se 1 (by rfl) ⟨1067021, by rfl⟩ : syracuseStep 1422695 = 2134043) B2134043
theorem B47332831 : Blo 682313 47332831 := bstep (se 1 (by rfl) ⟨35499623, by rfl⟩ : syracuseStep 47332831 = 70999247) B70999247
theorem B6241819 : Blo 682313 6241819 := bstep (se 1 (by rfl) ⟨4681364, by rfl⟩ : syracuseStep 6241819 = 9362729) B9362729
theorem B1949609 : Blo 682313 1949609 := bstep (se 2 (by rfl) ⟨731103, by rfl⟩ : syracuseStep 1949609 = 1462207) B1462207
theorem B3457079 : Blo 682313 3457079 := bstep (se 1 (by rfl) ⟨2592809, by rfl⟩ : syracuseStep 3457079 = 5185619) B5185619
theorem B3457403 : Blo 682313 3457403 := bstep (se 1 (by rfl) ⟨2593052, by rfl⟩ : syracuseStep 3457403 = 5186105) B5186105
theorem B2605567 : Blo 682313 2605567 := bstep (se 1 (by rfl) ⟨1954175, by rfl⟩ : syracuseStep 2605567 = 3908351) B3908351
theorem B2310767 : Blo 682313 2310767 := bstep (se 1 (by rfl) ⟨1733075, by rfl⟩ : syracuseStep 2310767 = 3466151) B3466151
theorem B1557319 : Blo 682313 1557319 := bstep (se 1 (by rfl) ⟨1167989, by rfl⟩ : syracuseStep 1557319 = 2335979) B2335979
theorem B1295851 : Blo 682313 1295851 := bstep (se 1 (by rfl) ⟨971888, by rfl⟩ : syracuseStep 1295851 = 1943777) B1943777
theorem B31573685 : Blo 682313 31573685 := bstep (se 5 (by rfl) ⟨1480016, by rfl⟩ : syracuseStep 31573685 = 2960033) B2960033
theorem B1951739 : Blo 682313 1951739 := bstep (se 1 (by rfl) ⟨1463804, by rfl⟩ : syracuseStep 1951739 = 2927609) B2927609
theorem B3951517 : Blo 682313 3951517 := bstep (se 3 (by rfl) ⟨740909, by rfl⟩ : syracuseStep 3951517 = 1481819) B1481819
theorem B937319 : Blo 682313 937319 := bstep (se 1 (by rfl) ⟨702989, by rfl⟩ : syracuseStep 937319 = 1405979) B1405979
theorem B2084473 : Blo 682313 2084473 := bstep (se 2 (by rfl) ⟨781677, by rfl⟩ : syracuseStep 2084473 = 1563355) B1563355
theorem B7229903 : Blo 682313 7229903 := bstep (se 1 (by rfl) ⟨5422427, by rfl⟩ : syracuseStep 7229903 = 10844855) B10844855
theorem B5199713 : Blo 682313 5199713 := bstep (se 2 (by rfl) ⟨1949892, by rfl⟩ : syracuseStep 5199713 = 3899785) B3899785
theorem B1728175 : Blo 682313 1728175 := bstep (se 1 (by rfl) ⟨1296131, by rfl⟩ : syracuseStep 1728175 = 2592263) B2592263
theorem B19717991 : Blo 682313 19717991 := bstep (se 1 (by rfl) ⟨14788493, by rfl⟩ : syracuseStep 19717991 = 29576987) B29576987
theorem B16834655 : Blo 682313 16834655 := bstep (se 1 (by rfl) ⟨12625991, by rfl⟩ : syracuseStep 16834655 = 25251983) B25251983
theorem B3465341 : Blo 682313 3465341 := bstep (se 3 (by rfl) ⟨649751, by rfl⟩ : syracuseStep 3465341 = 1299503) B1299503
theorem B39444731 : Blo 682313 39444731 := bstep (se 1 (by rfl) ⟨29583548, by rfl⟩ : syracuseStep 39444731 = 59167097) B59167097
theorem B5858153 : Blo 682313 5858153 := bstep (se 2 (by rfl) ⟨2196807, by rfl⟩ : syracuseStep 5858153 = 4393615) B4393615
theorem B66413519 : Blo 682313 66413519 := bstep (se 1 (by rfl) ⟨49810139, by rfl⟩ : syracuseStep 66413519 = 99620279) B99620279
theorem B4384799 : Blo 682313 4384799 := bstep (se 1 (by rfl) ⟨3288599, by rfl⟩ : syracuseStep 4384799 = 6577199) B6577199
theorem B3894227 : Blo 682313 3894227 := bstep (se 1 (by rfl) ⟨2920670, by rfl⟩ : syracuseStep 3894227 = 5841341) B5841341
theorem B683039 : Blo 682313 683039 := bstep (se 1 (by rfl) ⟨512279, by rfl⟩ : syracuseStep 683039 = 1024559) B1024559
theorem B683291 : Blo 682313 683291 := bstep (se 1 (by rfl) ⟨512468, by rfl⟩ : syracuseStep 683291 = 1024937) B1024937
theorem B683367 : Blo 682313 683367 := bstep (se 1 (by rfl) ⟨512525, by rfl⟩ : syracuseStep 683367 = 1025051) B1025051
theorem B33353117 : Blo 682313 33353117 := bstep (se 3 (by rfl) ⟨6253709, by rfl⟩ : syracuseStep 33353117 = 12507419) B12507419
theorem B1732225 : Blo 682313 1732225 := bstep (se 2 (by rfl) ⟨649584, by rfl⟩ : syracuseStep 1732225 = 1299169) B1299169
theorem B684143 : Blo 682313 684143 := bstep (se 1 (by rfl) ⟨513107, by rfl⟩ : syracuseStep 684143 = 1026215) B1026215
theorem B684283 : Blo 682313 684283 := bstep (se 1 (by rfl) ⟨513212, by rfl⟩ : syracuseStep 684283 = 1026425) B1026425
theorem B684315 : Blo 682313 684315 := bstep (se 1 (by rfl) ⟨513236, by rfl⟩ : syracuseStep 684315 = 1026473) B1026473
theorem B685287 : Blo 682313 685287 := bstep (se 1 (by rfl) ⟨513965, by rfl⟩ : syracuseStep 685287 = 1027931) B1027931
theorem B686171 : Blo 682313 686171 := bstep (se 1 (by rfl) ⟨514628, by rfl⟩ : syracuseStep 686171 = 1029257) B1029257
theorem B686303 : Blo 682313 686303 := bstep (se 1 (by rfl) ⟨514727, by rfl⟩ : syracuseStep 686303 = 1029455) B1029455
theorem B25328375 : Blo 682313 25328375 := bstep (se 1 (by rfl) ⟨18996281, by rfl⟩ : syracuseStep 25328375 = 37992563) B37992563
theorem B2194553 : Blo 682313 2194553 := bstep (se 2 (by rfl) ⟨822957, by rfl⟩ : syracuseStep 2194553 = 1645915) B1645915
theorem B44892413 : Blo 682313 44892413 := bstep (se 3 (by rfl) ⟨8417327, by rfl⟩ : syracuseStep 44892413 = 16834655) B16834655
theorem B1540511 : Blo 682313 1540511 := bstep (se 1 (by rfl) ⟨1155383, by rfl⟩ : syracuseStep 1540511 = 2310767) B2310767
theorem B3474089 : Blo 682313 3474089 := bstep (se 2 (by rfl) ⟨1302783, by rfl⟩ : syracuseStep 3474089 = 2605567) B2605567
theorem B7800299 : Blo 682313 7800299 := bstep (se 1 (by rfl) ⟨5850224, by rfl⟩ : syracuseStep 7800299 = 11700449) B11700449
theorem B11864519 : Blo 682313 11864519 := bstep (se 1 (by rfl) ⟨8898389, by rfl⟩ : syracuseStep 11864519 = 17796779) B17796779
theorem B2198269 : Blo 682313 2198269 := bstep (se 3 (by rfl) ⟨412175, by rfl⟩ : syracuseStep 2198269 = 824351) B824351
theorem B2592233 : Blo 682313 2592233 := bstep (se 2 (by rfl) ⟨972087, by rfl⟩ : syracuseStep 2592233 = 1944175) B1944175
theorem B1969847 : Blo 682313 1969847 := bstep (se 1 (by rfl) ⟨1477385, by rfl⟩ : syracuseStep 1969847 = 2954771) B2954771
theorem B1249555 : Blo 682313 1249555 := bstep (se 1 (by rfl) ⟨937166, by rfl⟩ : syracuseStep 1249555 = 1874333) B1874333
theorem B13145327 : Blo 682313 13145327 := bstep (se 1 (by rfl) ⟨9858995, by rfl⟩ : syracuseStep 13145327 = 19717991) B19717991
theorem B3905435 : Blo 682313 3905435 := bstep (se 1 (by rfl) ⟨2929076, by rfl⟩ : syracuseStep 3905435 = 5858153) B5858153
theorem B44275679 : Blo 682313 44275679 := bstep (se 1 (by rfl) ⟨33206759, by rfl⟩ : syracuseStep 44275679 = 66413519) B66413519
theorem B2923199 : Blo 682313 2923199 := bstep (se 1 (by rfl) ⟨2192399, by rfl⟩ : syracuseStep 2923199 = 4384799) B4384799
theorem B2596151 : Blo 682313 2596151 := bstep (se 1 (by rfl) ⟨1947113, by rfl⟩ : syracuseStep 2596151 = 3894227) B3894227
theorem B11117189 : Blo 682313 11117189 := bstep (se 4 (by rfl) ⟨1042236, by rfl⟩ : syracuseStep 11117189 = 2084473) B2084473
theorem B2499517 : Blo 682313 2499517 := bstep (se 3 (by rfl) ⟨468659, by rfl⟩ : syracuseStep 2499517 = 937319) B937319
theorem B16885583 : Blo 682313 16885583 := bstep (se 1 (by rfl) ⟨12664187, by rfl⟩ : syracuseStep 16885583 = 25328375) B25328375
theorem B2304233 : Blo 682313 2304233 := bstep (se 2 (by rfl) ⟨864087, by rfl⟩ : syracuseStep 2304233 = 1728175) B1728175
theorem B2304719 : Blo 682313 2304719 := bstep (se 1 (by rfl) ⟨1728539, by rfl⟩ : syracuseStep 2304719 = 3457079) B3457079
theorem B2304935 : Blo 682313 2304935 := bstep (se 1 (by rfl) ⟨1728701, by rfl⟩ : syracuseStep 2304935 = 3457403) B3457403
theorem B2600039 : Blo 682313 2600039 := bstep (se 1 (by rfl) ⟨1950029, by rfl⟩ : syracuseStep 2600039 = 3900059) B3900059
theorem B1027823 : Blo 682313 1027823 := bstep (se 1 (by rfl) ⟨770867, by rfl⟩ : syracuseStep 1027823 = 1541735) B1541735
theorem B2076425 : Blo 682313 2076425 := bstep (se 2 (by rfl) ⟨778659, by rfl⟩ : syracuseStep 2076425 = 1557319) B1557319
theorem B19279741 : Blo 682313 19279741 := bstep (se 3 (by rfl) ⟨3614951, by rfl⟩ : syracuseStep 19279741 = 7229903) B7229903
theorem B1028303 : Blo 682313 1028303 := bstep (se 1 (by rfl) ⟨771227, by rfl⟩ : syracuseStep 1028303 = 1542455) B1542455
theorem B2339327 : Blo 682313 2339327 := bstep (se 1 (by rfl) ⟨1754495, by rfl⟩ : syracuseStep 2339327 = 3508991) B3508991
theorem B8303249 : Blo 682313 8303249 := bstep (se 2 (by rfl) ⟨3113718, by rfl⟩ : syracuseStep 8303249 = 6227437) B6227437
theorem B8762215 : Blo 682313 8762215 := bstep (se 1 (by rfl) ⟨6571661, by rfl⟩ : syracuseStep 8762215 = 13143323) B13143323
theorem B4372703 : Blo 682313 4372703 := bstep (se 1 (by rfl) ⟨3279527, by rfl⟩ : syracuseStep 4372703 = 6559055) B6559055
theorem B84196493 : Blo 682313 84196493 := bstep (se 3 (by rfl) ⟨15786842, by rfl⟩ : syracuseStep 84196493 = 31573685) B31573685
theorem B2309633 : Blo 682313 2309633 := bstep (se 2 (by rfl) ⟨866112, by rfl⟩ : syracuseStep 2309633 = 1732225) B1732225
theorem B2310227 : Blo 682313 2310227 := bstep (se 1 (by rfl) ⟨1732670, by rfl⟩ : syracuseStep 2310227 = 3465341) B3465341
theorem B26296487 : Blo 682313 26296487 := bstep (se 1 (by rfl) ⟨19722365, by rfl⟩ : syracuseStep 26296487 = 39444731) B39444731
theorem B22235411 : Blo 682313 22235411 := bstep (se 1 (by rfl) ⟨16676558, by rfl⟩ : syracuseStep 22235411 = 33353117) B33353117
theorem B2083295 : Blo 682313 2083295 := bstep (se 1 (by rfl) ⟨1562471, by rfl⟩ : syracuseStep 2083295 = 3124943) B3124943
theorem B1297127 : Blo 682313 1297127 := bstep (se 1 (by rfl) ⟨972845, by rfl⟩ : syracuseStep 1297127 = 1945691) B1945691
theorem B14076935 : Blo 682313 14076935 := bstep (se 1 (by rfl) ⟨10557701, by rfl⟩ : syracuseStep 14076935 = 21115403) B21115403
theorem B1463035 : Blo 682313 1463035 := bstep (se 1 (by rfl) ⟨1097276, by rfl⟩ : syracuseStep 1463035 = 2194553) B2194553
theorem B1299739 : Blo 682313 1299739 := bstep (se 1 (by rfl) ⟨974804, by rfl⟩ : syracuseStep 1299739 = 1949609) B1949609
theorem B2775667 : Blo 682313 2775667 := bstep (se 1 (by rfl) ⟨2081750, by rfl⟩ : syracuseStep 2775667 = 4163501) B4163501
theorem B1301159 : Blo 682313 1301159 := bstep (se 1 (by rfl) ⟨975869, by rfl⟩ : syracuseStep 1301159 = 1951739) B1951739
theorem B2185967 : Blo 682313 2185967 := bstep (se 1 (by rfl) ⟨1639475, by rfl⟩ : syracuseStep 2185967 = 3278951) B3278951
theorem B9887017 : Blo 682313 9887017 := bstep (se 2 (by rfl) ⟨3707631, by rfl⟩ : syracuseStep 9887017 = 7415263) B7415263
theorem B1727801 : Blo 682313 1727801 := bstep (se 2 (by rfl) ⟨647925, by rfl⟩ : syracuseStep 1727801 = 1295851) B1295851
theorem B3793853 : Blo 682313 3793853 := bstep (se 3 (by rfl) ⟨711347, by rfl⟩ : syracuseStep 3793853 = 1422695) B1422695
theorem B5268689 : Blo 682313 5268689 := bstep (se 2 (by rfl) ⟨1975758, by rfl⟩ : syracuseStep 5268689 = 3951517) B3951517
theorem B3466475 : Blo 682313 3466475 := bstep (se 1 (by rfl) ⟨2599856, by rfl⟩ : syracuseStep 3466475 = 5199713) B5199713
theorem B7039001 : Blo 682313 7039001 := bstep (se 2 (by rfl) ⟨2639625, by rfl⟩ : syracuseStep 7039001 = 5279251) B5279251
theorem B26044859 : Blo 682313 26044859 := bstep (se 1 (by rfl) ⟨19533644, by rfl⟩ : syracuseStep 26044859 = 39067289) B39067289
theorem B682447 : Blo 682313 682447 := bstep (se 1 (by rfl) ⟨511835, by rfl⟩ : syracuseStep 682447 = 1023671) B1023671
theorem B682815 : Blo 682313 682815 := bstep (se 1 (by rfl) ⟨512111, by rfl⟩ : syracuseStep 682815 = 1024223) B1024223
theorem B683111 : Blo 682313 683111 := bstep (se 1 (by rfl) ⟨512333, by rfl⟩ : syracuseStep 683111 = 1024667) B1024667
theorem B683135 : Blo 682313 683135 := bstep (se 1 (by rfl) ⟨512351, by rfl⟩ : syracuseStep 683135 = 1024703) B1024703
theorem B683327 : Blo 682313 683327 := bstep (se 1 (by rfl) ⟨512495, by rfl⟩ : syracuseStep 683327 = 1024991) B1024991
theorem B683567 : Blo 682313 683567 := bstep (se 1 (by rfl) ⟨512675, by rfl⟩ : syracuseStep 683567 = 1025351) B1025351
theorem B683935 : Blo 682313 683935 := bstep (se 1 (by rfl) ⟨512951, by rfl⟩ : syracuseStep 683935 = 1025903) B1025903
theorem B683943 : Blo 682313 683943 := bstep (se 1 (by rfl) ⟨512957, by rfl⟩ : syracuseStep 683943 = 1025915) B1025915
theorem B1733147 : Blo 682313 1733147 := bstep (se 1 (by rfl) ⟨1299860, by rfl⟩ : syracuseStep 1733147 = 2599721) B2599721
theorem B684655 : Blo 682313 684655 := bstep (se 1 (by rfl) ⟨513491, by rfl⟩ : syracuseStep 684655 = 1026983) B1026983
theorem B684711 : Blo 682313 684711 := bstep (se 1 (by rfl) ⟨513533, by rfl⟩ : syracuseStep 684711 = 1027067) B1027067
theorem B4387517 : Blo 682313 4387517 := bstep (se 3 (by rfl) ⟨822659, by rfl⟩ : syracuseStep 4387517 = 1645319) B1645319
theorem B684903 : Blo 682313 684903 := bstep (se 1 (by rfl) ⟨513677, by rfl⟩ : syracuseStep 684903 = 1027355) B1027355
theorem B684927 : Blo 682313 684927 := bstep (se 1 (by rfl) ⟨513695, by rfl⟩ : syracuseStep 684927 = 1027391) B1027391
theorem B685339 : Blo 682313 685339 := bstep (se 1 (by rfl) ⟨514004, by rfl⟩ : syracuseStep 685339 = 1028009) B1028009
theorem B686143 : Blo 682313 686143 := bstep (se 1 (by rfl) ⟨514607, by rfl⟩ : syracuseStep 686143 = 1029215) B1029215
theorem B19953949 : Blo 682313 19953949 := bstep (se 3 (by rfl) ⟨3741365, by rfl⟩ : syracuseStep 19953949 = 7482731) B7482731
theorem B63110441 : Blo 682313 63110441 := bstep (se 2 (by rfl) ⟨23666415, by rfl⟩ : syracuseStep 63110441 = 47332831) B47332831
theorem B8322425 : Blo 682313 8322425 := bstep (se 2 (by rfl) ⟨3120909, by rfl⟩ : syracuseStep 8322425 = 6241819) B6241819
theorem B1540151 : Blo 682313 1540151 := bstep (se 1 (by rfl) ⟨1155113, by rfl⟩ : syracuseStep 1540151 = 2310227) B2310227
theorem B17530991 : Blo 682313 17530991 := bstep (se 1 (by rfl) ⟨13148243, by rfl⟩ : syracuseStep 17530991 = 26296487) B26296487
theorem B1313231 : Blo 682313 1313231 := bstep (se 1 (by rfl) ⟨984923, by rfl⟩ : syracuseStep 1313231 = 1969847) B1969847
theorem B1151867 : Blo 682313 1151867 := bstep (se 1 (by rfl) ⟨863900, by rfl⟩ : syracuseStep 1151867 = 1727801) B1727801
theorem B7411459 : Blo 682313 7411459 := bstep (se 1 (by rfl) ⟨5558594, by rfl⟩ : syracuseStep 7411459 = 11117189) B11117189
theorem B2529235 : Blo 682313 2529235 := bstep (se 1 (by rfl) ⟨1896926, by rfl⟩ : syracuseStep 2529235 = 3793853) B3793853
theorem B3512459 : Blo 682313 3512459 := bstep (se 1 (by rfl) ⟨2634344, by rfl⟩ : syracuseStep 3512459 = 5268689) B5268689
theorem B4692667 : Blo 682313 4692667 := bstep (se 1 (by rfl) ⟨3519500, by rfl⟩ : syracuseStep 4692667 = 7039001) B7039001
theorem B1384283 : Blo 682313 1384283 := bstep (se 1 (by rfl) ⟨1038212, by rfl⟩ : syracuseStep 1384283 = 2076425) B2076425
theorem B1155431 : Blo 682313 1155431 := bstep (se 1 (by rfl) ⟨866573, by rfl⟩ : syracuseStep 1155431 = 1733147) B1733147
theorem B2925011 : Blo 682313 2925011 := bstep (se 1 (by rfl) ⟨2193758, by rfl⟩ : syracuseStep 2925011 = 4387517) B4387517
theorem B13182689 : Blo 682313 13182689 := bstep (se 2 (by rfl) ⟨4943508, by rfl⟩ : syracuseStep 13182689 = 9887017) B9887017
theorem B5548283 : Blo 682313 5548283 := bstep (se 1 (by rfl) ⟨4161212, by rfl⟩ : syracuseStep 5548283 = 8322425) B8322425
theorem B29928275 : Blo 682313 29928275 := bstep (se 1 (by rfl) ⟨22446206, by rfl⟩ : syracuseStep 29928275 = 44892413) B44892413
theorem B1027007 : Blo 682313 1027007 := bstep (se 1 (by rfl) ⟨770255, by rfl⟩ : syracuseStep 1027007 = 1540511) B1540511
theorem B6238205 : Blo 682313 6238205 := bstep (se 3 (by rfl) ⟨1169663, by rfl⟩ : syracuseStep 6238205 = 2339327) B2339327
theorem B14823607 : Blo 682313 14823607 := bstep (se 1 (by rfl) ⟨11117705, by rfl⟩ : syracuseStep 14823607 = 22235411) B22235411
theorem B7909679 : Blo 682313 7909679 := bstep (se 1 (by rfl) ⟨5932259, by rfl⟩ : syracuseStep 7909679 = 11864519) B11864519
theorem B1388863 : Blo 682313 1388863 := bstep (se 1 (by rfl) ⟨1041647, by rfl⟩ : syracuseStep 1388863 = 2083295) B2083295
theorem B864751 : Blo 682313 864751 := bstep (se 1 (by rfl) ⟨648563, by rfl⟩ : syracuseStep 864751 = 1297127) B1297127
theorem B9384623 : Blo 682313 9384623 := bstep (se 1 (by rfl) ⟨7038467, by rfl⟩ : syracuseStep 9384623 = 14076935) B14076935
theorem B8763551 : Blo 682313 8763551 := bstep (se 1 (by rfl) ⟨6572663, by rfl⟩ : syracuseStep 8763551 = 13145327) B13145327
theorem B2931025 : Blo 682313 2931025 := bstep (se 2 (by rfl) ⟨1099134, by rfl⟩ : syracuseStep 2931025 = 2198269) B2198269
theorem B2603623 : Blo 682313 2603623 := bstep (se 1 (by rfl) ⟨1952717, by rfl⟩ : syracuseStep 2603623 = 3905435) B3905435
theorem B867439 : Blo 682313 867439 := bstep (se 1 (by rfl) ⟨650579, by rfl⟩ : syracuseStep 867439 = 1301159) B1301159
theorem B1948799 : Blo 682313 1948799 := bstep (se 1 (by rfl) ⟨1461599, by rfl⟩ : syracuseStep 1948799 = 2923199) B2923199
theorem B25706321 : Blo 682313 25706321 := bstep (se 2 (by rfl) ⟨9639870, by rfl⟩ : syracuseStep 25706321 = 19279741) B19279741
theorem B2310983 : Blo 682313 2310983 := bstep (se 1 (by rfl) ⟨1733237, by rfl⟩ : syracuseStep 2310983 = 3466475) B3466475
theorem B1950713 : Blo 682313 1950713 := bstep (se 2 (by rfl) ⟨731517, by rfl⟩ : syracuseStep 1950713 = 1463035) B1463035
theorem B11682953 : Blo 682313 11682953 := bstep (se 2 (by rfl) ⟨4381107, by rfl⟩ : syracuseStep 11682953 = 8762215) B8762215
theorem B69452957 : Blo 682313 69452957 := bstep (se 3 (by rfl) ⟨13022429, by rfl⟩ : syracuseStep 69452957 = 26044859) B26044859
theorem B11257055 : Blo 682313 11257055 := bstep (se 1 (by rfl) ⟨8442791, by rfl⟩ : syracuseStep 11257055 = 16885583) B16885583
theorem B2316059 : Blo 682313 2316059 := bstep (se 1 (by rfl) ⟨1737044, by rfl⟩ : syracuseStep 2316059 = 3474089) B3474089
theorem B5200199 : Blo 682313 5200199 := bstep (se 1 (by rfl) ⟨3900149, by rfl⟩ : syracuseStep 5200199 = 7800299) B7800299
theorem B1728155 : Blo 682313 1728155 := bstep (se 1 (by rfl) ⟨1296116, by rfl⟩ : syracuseStep 1728155 = 2592233) B2592233
theorem B29517119 : Blo 682313 29517119 := bstep (se 1 (by rfl) ⟨22137839, by rfl⟩ : syracuseStep 29517119 = 44275679) B44275679
theorem B1730767 : Blo 682313 1730767 := bstep (se 1 (by rfl) ⟨1298075, by rfl⟩ : syracuseStep 1730767 = 2596151) B2596151
theorem B13330757 : Blo 682313 13330757 := bstep (se 4 (by rfl) ⟨1249758, by rfl⟩ : syracuseStep 13330757 = 2499517) B2499517
theorem B1666073 : Blo 682313 1666073 := bstep (se 2 (by rfl) ⟨624777, by rfl⟩ : syracuseStep 1666073 = 1249555) B1249555
theorem B1536155 : Blo 682313 1536155 := bstep (se 1 (by rfl) ⟨1152116, by rfl⟩ : syracuseStep 1536155 = 2304233) B2304233
theorem B1732985 : Blo 682313 1732985 := bstep (se 2 (by rfl) ⟨649869, by rfl⟩ : syracuseStep 1732985 = 1299739) B1299739
theorem B1536479 : Blo 682313 1536479 := bstep (se 1 (by rfl) ⟨1152359, by rfl⟩ : syracuseStep 1536479 = 2304719) B2304719
theorem B1536623 : Blo 682313 1536623 := bstep (se 1 (by rfl) ⟨1152467, by rfl⟩ : syracuseStep 1536623 = 2304935) B2304935
theorem B5829245 : Blo 682313 5829245 := bstep (se 3 (by rfl) ⟨1092983, by rfl⟩ : syracuseStep 5829245 = 2185967) B2185967
theorem B1733359 : Blo 682313 1733359 := bstep (se 1 (by rfl) ⟨1300019, by rfl⟩ : syracuseStep 1733359 = 2600039) B2600039
theorem B685215 : Blo 682313 685215 := bstep (se 1 (by rfl) ⟨513911, by rfl⟩ : syracuseStep 685215 = 1027823) B1027823
theorem B685535 : Blo 682313 685535 := bstep (se 1 (by rfl) ⟨514151, by rfl⟩ : syracuseStep 685535 = 1028303) B1028303
theorem B26605265 : Blo 682313 26605265 := bstep (se 2 (by rfl) ⟨9976974, by rfl⟩ : syracuseStep 26605265 = 19953949) B19953949
theorem B5535499 : Blo 682313 5535499 := bstep (se 1 (by rfl) ⟨4151624, by rfl⟩ : syracuseStep 5535499 = 8303249) B8303249
theorem B3700889 : Blo 682313 3700889 := bstep (se 2 (by rfl) ⟨1387833, by rfl⟩ : syracuseStep 3700889 = 2775667) B2775667
theorem B2915135 : Blo 682313 2915135 := bstep (se 1 (by rfl) ⟨2186351, by rfl⟩ : syracuseStep 2915135 = 4372703) B4372703
theorem B56130995 : Blo 682313 56130995 := bstep (se 1 (by rfl) ⟨42098246, by rfl⟩ : syracuseStep 56130995 = 84196493) B84196493
theorem B42073627 : Blo 682313 42073627 := bstep (se 1 (by rfl) ⟨31555220, by rfl⟩ : syracuseStep 42073627 = 63110441) B63110441
theorem B1539755 : Blo 682313 1539755 := bstep (se 1 (by rfl) ⟨1154816, by rfl⟩ : syracuseStep 1539755 = 2309633) B2309633
theorem B1540655 : Blo 682313 1540655 := bstep (se 1 (by rfl) ⟨1155491, by rfl⟩ : syracuseStep 1540655 = 2310983) B2310983
theorem B46301971 : Blo 682313 46301971 := bstep (se 1 (by rfl) ⟨34726478, by rfl⟩ : syracuseStep 46301971 = 69452957) B69452957
theorem B7504703 : Blo 682313 7504703 := bstep (se 1 (by rfl) ⟨5628527, by rfl⟩ : syracuseStep 7504703 = 11257055) B11257055
theorem B1544039 : Blo 682313 1544039 := bstep (se 1 (by rfl) ⟨1158029, by rfl⟩ : syracuseStep 1544039 = 2316059) B2316059
theorem B1152103 : Blo 682313 1152103 := bstep (se 1 (by rfl) ⟨864077, by rfl⟩ : syracuseStep 1152103 = 1728155) B1728155
theorem B922855 : Blo 682313 922855 := bstep (se 1 (by rfl) ⟨692141, by rfl⟩ : syracuseStep 922855 = 1384283) B1384283
theorem B19764809 : Blo 682313 19764809 := bstep (se 2 (by rfl) ⟨7411803, by rfl⟩ : syracuseStep 19764809 = 14823607) B14823607
theorem B1153001 : Blo 682313 1153001 := bstep (se 2 (by rfl) ⟨432375, by rfl⟩ : syracuseStep 1153001 = 864751) B864751
theorem B8788459 : Blo 682313 8788459 := bstep (se 1 (by rfl) ⟨6591344, by rfl⟩ : syracuseStep 8788459 = 13182689) B13182689
theorem B8887171 : Blo 682313 8887171 := bstep (se 1 (by rfl) ⟨6665378, by rfl⟩ : syracuseStep 8887171 = 13330757) B13330757
theorem B7380665 : Blo 682313 7380665 := bstep (se 2 (by rfl) ⟨2767749, by rfl⟩ : syracuseStep 7380665 = 5535499) B5535499
theorem B1024103 : Blo 682313 1024103 := bstep (se 1 (by rfl) ⟨768077, by rfl⟩ : syracuseStep 1024103 = 1536155) B1536155
theorem B1155323 : Blo 682313 1155323 := bstep (se 1 (by rfl) ⟨866492, by rfl⟩ : syracuseStep 1155323 = 1732985) B1732985
theorem B1024319 : Blo 682313 1024319 := bstep (se 1 (by rfl) ⟨768239, by rfl⟩ : syracuseStep 1024319 = 1536479) B1536479
theorem B1024415 : Blo 682313 1024415 := bstep (se 1 (by rfl) ⟨768311, by rfl⟩ : syracuseStep 1024415 = 1536623) B1536623
theorem B3908033 : Blo 682313 3908033 := bstep (se 2 (by rfl) ⟨1465512, by rfl⟩ : syracuseStep 3908033 = 2931025) B2931025
theorem B2467259 : Blo 682313 2467259 := bstep (se 1 (by rfl) ⟨1850444, by rfl⟩ : syracuseStep 2467259 = 3700889) B3700889
theorem B5842367 : Blo 682313 5842367 := bstep (se 1 (by rfl) ⟨4381775, by rfl⟩ : syracuseStep 5842367 = 8763551) B8763551
theorem B1156585 : Blo 682313 1156585 := bstep (se 2 (by rfl) ⟨433719, by rfl⟩ : syracuseStep 1156585 = 867439) B867439
theorem B1943423 : Blo 682313 1943423 := bstep (se 1 (by rfl) ⟨1457567, by rfl⟩ : syracuseStep 1943423 = 2915135) B2915135
theorem B1026503 : Blo 682313 1026503 := bstep (se 1 (by rfl) ⟨769877, by rfl⟩ : syracuseStep 1026503 = 1539755) B1539755
theorem B1026767 : Blo 682313 1026767 := bstep (se 1 (by rfl) ⟨770075, by rfl⟩ : syracuseStep 1026767 = 1540151) B1540151
theorem B2307689 : Blo 682313 2307689 := bstep (se 2 (by rfl) ⟨865383, by rfl⟩ : syracuseStep 2307689 = 1730767) B1730767
theorem B767911 : Blo 682313 767911 := bstep (se 1 (by rfl) ⟨575933, by rfl⟩ : syracuseStep 767911 = 1151867) B1151867
theorem B2341639 : Blo 682313 2341639 := bstep (se 1 (by rfl) ⟨1756229, by rfl⟩ : syracuseStep 2341639 = 3512459) B3512459
theorem B770287 : Blo 682313 770287 := bstep (se 1 (by rfl) ⟨577715, by rfl⟩ : syracuseStep 770287 = 1155431) B1155431
theorem B1950007 : Blo 682313 1950007 := bstep (se 1 (by rfl) ⟨1462505, by rfl⟩ : syracuseStep 1950007 = 2925011) B2925011
theorem B1851817 : Blo 682313 1851817 := bstep (se 2 (by rfl) ⟨694431, by rfl⟩ : syracuseStep 1851817 = 1388863) B1388863
theorem B19678079 : Blo 682313 19678079 := bstep (se 1 (by rfl) ⟨14758559, by rfl⟩ : syracuseStep 19678079 = 29517119) B29517119
theorem B2311145 : Blo 682313 2311145 := bstep (se 2 (by rfl) ⟨866679, by rfl⟩ : syracuseStep 2311145 = 1733359) B1733359
theorem B283789493 : Blo 682313 283789493 := bstep (se 5 (by rfl) ⟨13302632, by rfl⟩ : syracuseStep 283789493 = 26605265) B26605265
theorem B9881945 : Blo 682313 9881945 := bstep (se 2 (by rfl) ⟨3705729, by rfl⟩ : syracuseStep 9881945 = 7411459) B7411459
theorem B4442861 : Blo 682313 4442861 := bstep (se 3 (by rfl) ⟨833036, by rfl⟩ : syracuseStep 4442861 = 1666073) B1666073
theorem B5196797 : Blo 682313 5196797 := bstep (se 3 (by rfl) ⟨974399, by rfl⟩ : syracuseStep 5196797 = 1948799) B1948799
theorem B3886163 : Blo 682313 3886163 := bstep (se 1 (by rfl) ⟨2914622, by rfl⟩ : syracuseStep 3886163 = 5829245) B5829245
theorem B11687327 : Blo 682313 11687327 := bstep (se 1 (by rfl) ⟨8765495, by rfl⟩ : syracuseStep 11687327 = 17530991) B17530991
theorem B1300475 : Blo 682313 1300475 := bstep (se 1 (by rfl) ⟨975356, by rfl⟩ : syracuseStep 1300475 = 1950713) B1950713
theorem B7788635 : Blo 682313 7788635 := bstep (se 1 (by rfl) ⟨5841476, by rfl⟩ : syracuseStep 7788635 = 11682953) B11682953
theorem B3466799 : Blo 682313 3466799 := bstep (se 1 (by rfl) ⟨2600099, by rfl⟩ : syracuseStep 3466799 = 5200199) B5200199
theorem B3501949 : Blo 682313 3501949 := bstep (se 3 (by rfl) ⟨656615, by rfl⟩ : syracuseStep 3501949 = 1313231) B1313231
theorem B3698855 : Blo 682313 3698855 := bstep (se 1 (by rfl) ⟨2774141, by rfl⟩ : syracuseStep 3698855 = 5548283) B5548283
theorem B19952183 : Blo 682313 19952183 := bstep (se 1 (by rfl) ⟨14964137, by rfl⟩ : syracuseStep 19952183 = 29928275) B29928275
theorem B684671 : Blo 682313 684671 := bstep (se 1 (by rfl) ⟨513503, by rfl⟩ : syracuseStep 684671 = 1027007) B1027007
theorem B3372313 : Blo 682313 3372313 := bstep (se 2 (by rfl) ⟨1264617, by rfl⟩ : syracuseStep 3372313 = 2529235) B2529235
theorem B4158803 : Blo 682313 4158803 := bstep (se 1 (by rfl) ⟨3119102, by rfl⟩ : syracuseStep 4158803 = 6238205) B6238205
theorem B5273119 : Blo 682313 5273119 := bstep (se 1 (by rfl) ⟨3954839, by rfl⟩ : syracuseStep 5273119 = 7909679) B7909679
theorem B6256415 : Blo 682313 6256415 := bstep (se 1 (by rfl) ⟨4692311, by rfl⟩ : syracuseStep 6256415 = 9384623) B9384623
theorem B3471497 : Blo 682313 3471497 := bstep (se 2 (by rfl) ⟨1301811, by rfl⟩ : syracuseStep 3471497 = 2603623) B2603623
theorem B6256889 : Blo 682313 6256889 := bstep (se 2 (by rfl) ⟨2346333, by rfl⟩ : syracuseStep 6256889 = 4692667) B4692667
theorem B149682653 : Blo 682313 149682653 := bstep (se 3 (by rfl) ⟨28065497, by rfl⟩ : syracuseStep 149682653 = 56130995) B56130995
theorem B56098169 : Blo 682313 56098169 := bstep (se 2 (by rfl) ⟨21036813, by rfl⟩ : syracuseStep 56098169 = 42073627) B42073627
theorem B17137547 : Blo 682313 17137547 := bstep (se 1 (by rfl) ⟨12853160, by rfl⟩ : syracuseStep 17137547 = 25706321) B25706321
theorem B1540763 : Blo 682313 1540763 := bstep (se 1 (by rfl) ⟨1155572, by rfl⟩ : syracuseStep 1540763 = 2311145) B2311145
theorem B61735961 : Blo 682313 61735961 := bstep (se 2 (by rfl) ⟨23150985, by rfl⟩ : syracuseStep 61735961 = 46301971) B46301971
theorem B6587963 : Blo 682313 6587963 := bstep (se 1 (by rfl) ⟨4940972, by rfl⟩ : syracuseStep 6587963 = 9881945) B9881945
theorem B1542113 : Blo 682313 1542113 := bstep (se 2 (by rfl) ⟨578292, by rfl⟩ : syracuseStep 1542113 = 1156585) B1156585
theorem B2590775 : Blo 682313 2590775 := bstep (se 1 (by rfl) ⟨1943081, by rfl⟩ : syracuseStep 2590775 = 3886163) B3886163
theorem B13176539 : Blo 682313 13176539 := bstep (se 1 (by rfl) ⟨9882404, by rfl⟩ : syracuseStep 13176539 = 19764809) B19764809
theorem B12488741 : Blo 682313 12488741 := bstep (se 4 (by rfl) ⟨1170819, by rfl⟩ : syracuseStep 12488741 = 2341639) B2341639
theorem B4920443 : Blo 682313 4920443 := bstep (se 1 (by rfl) ⟨3690332, by rfl⟩ : syracuseStep 4920443 = 7380665) B7380665
theorem B1644839 : Blo 682313 1644839 := bstep (se 1 (by rfl) ⟨1233629, by rfl⟩ : syracuseStep 1644839 = 2467259) B2467259
theorem B4496417 : Blo 682313 4496417 := bstep (se 2 (by rfl) ⟨1686156, by rfl⟩ : syracuseStep 4496417 = 3372313) B3372313
theorem B1023881 : Blo 682313 1023881 := bstep (se 2 (by rfl) ⟨383955, by rfl⟩ : syracuseStep 1023881 = 767911) B767911
theorem B2465903 : Blo 682313 2465903 := bstep (se 1 (by rfl) ⟨1849427, by rfl⟩ : syracuseStep 2465903 = 3698855) B3698855
theorem B28123301 : Blo 682313 28123301 := bstep (se 4 (by rfl) ⟨2636559, by rfl⟩ : syracuseStep 28123301 = 5273119) B5273119
theorem B4170943 : Blo 682313 4170943 := bstep (se 1 (by rfl) ⟨3128207, by rfl⟩ : syracuseStep 4170943 = 6256415) B6256415
theorem B4171259 : Blo 682313 4171259 := bstep (se 1 (by rfl) ⟨3128444, by rfl⟩ : syracuseStep 4171259 = 6256889) B6256889
theorem B99788435 : Blo 682313 99788435 := bstep (se 1 (by rfl) ⟨74841326, by rfl⟩ : syracuseStep 99788435 = 149682653) B149682653
theorem B37398779 : Blo 682313 37398779 := bstep (se 1 (by rfl) ⟨28049084, by rfl⟩ : syracuseStep 37398779 = 56098169) B56098169
theorem B1027049 : Blo 682313 1027049 := bstep (se 2 (by rfl) ⟨385143, by rfl⟩ : syracuseStep 1027049 = 770287) B770287
theorem B1027103 : Blo 682313 1027103 := bstep (se 1 (by rfl) ⟨770327, by rfl⟩ : syracuseStep 1027103 = 1540655) B1540655
theorem B2600009 : Blo 682313 2600009 := bstep (se 2 (by rfl) ⟨975003, by rfl⟩ : syracuseStep 2600009 = 1950007) B1950007
theorem B2469089 : Blo 682313 2469089 := bstep (se 2 (by rfl) ⟨925908, by rfl⟩ : syracuseStep 2469089 = 1851817) B1851817
theorem B13118719 : Blo 682313 13118719 := bstep (se 1 (by rfl) ⟨9839039, by rfl⟩ : syracuseStep 13118719 = 19678079) B19678079
theorem B1029359 : Blo 682313 1029359 := bstep (se 1 (by rfl) ⟨772019, by rfl⟩ : syracuseStep 1029359 = 1544039) B1544039
theorem B11090141 : Blo 682313 11090141 := bstep (se 3 (by rfl) ⟨2079401, by rfl⟩ : syracuseStep 11090141 = 4158803) B4158803
theorem B768667 : Blo 682313 768667 := bstep (se 1 (by rfl) ⟨576500, by rfl⟩ : syracuseStep 768667 = 1153001) B1153001
theorem B5192423 : Blo 682313 5192423 := bstep (se 1 (by rfl) ⟨3894317, by rfl⟩ : syracuseStep 5192423 = 7788635) B7788635
theorem B4669265 : Blo 682313 4669265 := bstep (se 2 (by rfl) ⟨1750974, by rfl⟩ : syracuseStep 4669265 = 3501949) B3501949
theorem B770215 : Blo 682313 770215 := bstep (se 1 (by rfl) ⟨577661, by rfl⟩ : syracuseStep 770215 = 1155323) B1155323
theorem B2605355 : Blo 682313 2605355 := bstep (se 1 (by rfl) ⟨1954016, by rfl⟩ : syracuseStep 2605355 = 3908033) B3908033
theorem B2311199 : Blo 682313 2311199 := bstep (se 1 (by rfl) ⟨1733399, by rfl⟩ : syracuseStep 2311199 = 3466799) B3466799
theorem B1295615 : Blo 682313 1295615 := bstep (se 1 (by rfl) ⟨971711, by rfl⟩ : syracuseStep 1295615 = 1943423) B1943423
theorem B1230473 : Blo 682313 1230473 := bstep (se 2 (by rfl) ⟨461427, by rfl⟩ : syracuseStep 1230473 = 922855) B922855
theorem B11847629 : Blo 682313 11847629 := bstep (se 3 (by rfl) ⟨2221430, by rfl⟩ : syracuseStep 11847629 = 4442861) B4442861
theorem B11717945 : Blo 682313 11717945 := bstep (se 2 (by rfl) ⟨4394229, by rfl⟩ : syracuseStep 11717945 = 8788459) B8788459
theorem B11849561 : Blo 682313 11849561 := bstep (se 2 (by rfl) ⟨4443585, by rfl⟩ : syracuseStep 11849561 = 8887171) B8887171
theorem B2314331 : Blo 682313 2314331 := bstep (se 1 (by rfl) ⟨1735748, by rfl⟩ : syracuseStep 2314331 = 3471497) B3471497
theorem B11425031 : Blo 682313 11425031 := bstep (se 1 (by rfl) ⟨8568773, by rfl⟩ : syracuseStep 11425031 = 17137547) B17137547
theorem B5003135 : Blo 682313 5003135 := bstep (se 1 (by rfl) ⟨3752351, by rfl⟩ : syracuseStep 5003135 = 7504703) B7504703
theorem B189192995 : Blo 682313 189192995 := bstep (se 1 (by rfl) ⟨141894746, by rfl⟩ : syracuseStep 189192995 = 283789493) B283789493
theorem B3464531 : Blo 682313 3464531 := bstep (se 1 (by rfl) ⟨2598398, by rfl⟩ : syracuseStep 3464531 = 5196797) B5196797
theorem B7791551 : Blo 682313 7791551 := bstep (se 1 (by rfl) ⟨5843663, by rfl⟩ : syracuseStep 7791551 = 11687327) B11687327
theorem B3467933 : Blo 682313 3467933 := bstep (se 3 (by rfl) ⟨650237, by rfl⟩ : syracuseStep 3467933 = 1300475) B1300475
theorem B682735 : Blo 682313 682735 := bstep (se 1 (by rfl) ⟨512051, by rfl⟩ : syracuseStep 682735 = 1024103) B1024103
theorem B682879 : Blo 682313 682879 := bstep (se 1 (by rfl) ⟨512159, by rfl⟩ : syracuseStep 682879 = 1024319) B1024319
theorem B682943 : Blo 682313 682943 := bstep (se 1 (by rfl) ⟨512207, by rfl⟩ : syracuseStep 682943 = 1024415) B1024415
theorem B3894911 : Blo 682313 3894911 := bstep (se 1 (by rfl) ⟨2921183, by rfl⟩ : syracuseStep 3894911 = 5842367) B5842367
theorem B1536137 : Blo 682313 1536137 := bstep (se 2 (by rfl) ⟨576051, by rfl⟩ : syracuseStep 1536137 = 1152103) B1152103
theorem B684335 : Blo 682313 684335 := bstep (se 1 (by rfl) ⟨513251, by rfl⟩ : syracuseStep 684335 = 1026503) B1026503
theorem B684511 : Blo 682313 684511 := bstep (se 1 (by rfl) ⟨513383, by rfl⟩ : syracuseStep 684511 = 1026767) B1026767
theorem B13301455 : Blo 682313 13301455 := bstep (se 1 (by rfl) ⟨9976091, by rfl⟩ : syracuseStep 13301455 = 19952183) B19952183
theorem B1538459 : Blo 682313 1538459 := bstep (se 1 (by rfl) ⟨1153844, by rfl⟩ : syracuseStep 1538459 = 2307689) B2307689
theorem B1736903 : Blo 682313 1736903 := bstep (se 1 (by rfl) ⟨1302677, by rfl⟩ : syracuseStep 1736903 = 2605355) B2605355
theorem B41157307 : Blo 682313 41157307 := bstep (se 1 (by rfl) ⟨30867980, by rfl⟩ : syracuseStep 41157307 = 61735961) B61735961
theorem B1540799 : Blo 682313 1540799 := bstep (se 1 (by rfl) ⟨1155599, by rfl⟩ : syracuseStep 1540799 = 2311199) B2311199
theorem B4391975 : Blo 682313 4391975 := bstep (se 1 (by rfl) ⟨3293981, by rfl⟩ : syracuseStep 4391975 = 6587963) B6587963
theorem B820315 : Blo 682313 820315 := bstep (se 1 (by rfl) ⟨615236, by rfl⟩ : syracuseStep 820315 = 1230473) B1230473
theorem B7898419 : Blo 682313 7898419 := bstep (se 1 (by rfl) ⟨5923814, by rfl⟩ : syracuseStep 7898419 = 11847629) B11847629
theorem B8784359 : Blo 682313 8784359 := bstep (se 1 (by rfl) ⟨6588269, by rfl⟩ : syracuseStep 8784359 = 13176539) B13176539
theorem B7899707 : Blo 682313 7899707 := bstep (se 1 (by rfl) ⟨5924780, by rfl⟩ : syracuseStep 7899707 = 11849561) B11849561
theorem B8325827 : Blo 682313 8325827 := bstep (se 1 (by rfl) ⟨6244370, by rfl⟩ : syracuseStep 8325827 = 12488741) B12488741
theorem B1542887 : Blo 682313 1542887 := bstep (se 1 (by rfl) ⟨1157165, by rfl⟩ : syracuseStep 1542887 = 2314331) B2314331
theorem B3280295 : Blo 682313 3280295 := bstep (se 1 (by rfl) ⟨2460221, by rfl⟩ : syracuseStep 3280295 = 4920443) B4920443
theorem B126128663 : Blo 682313 126128663 := bstep (se 1 (by rfl) ⟨94596497, by rfl⟩ : syracuseStep 126128663 = 189192995) B189192995
theorem B18748867 : Blo 682313 18748867 := bstep (se 1 (by rfl) ⟨14061650, by rfl⟩ : syracuseStep 18748867 = 28123301) B28123301
theorem B66525623 : Blo 682313 66525623 := bstep (se 1 (by rfl) ⟨49894217, by rfl⟩ : syracuseStep 66525623 = 99788435) B99788435
theorem B17735273 : Blo 682313 17735273 := bstep (se 2 (by rfl) ⟨6650727, by rfl⟩ : syracuseStep 17735273 = 13301455) B13301455
theorem B2596607 : Blo 682313 2596607 := bstep (se 1 (by rfl) ⟨1947455, by rfl⟩ : syracuseStep 2596607 = 3894911) B3894911
theorem B1024091 : Blo 682313 1024091 := bstep (se 1 (by rfl) ⟨768068, by rfl⟩ : syracuseStep 1024091 = 1536137) B1536137
theorem B1024889 : Blo 682313 1024889 := bstep (se 2 (by rfl) ⟨384333, by rfl⟩ : syracuseStep 1024889 = 768667) B768667
theorem B1025639 : Blo 682313 1025639 := bstep (se 1 (by rfl) ⟨769229, by rfl⟩ : syracuseStep 1025639 = 1538459) B1538459
theorem B1026953 : Blo 682313 1026953 := bstep (se 2 (by rfl) ⟨385107, by rfl⟩ : syracuseStep 1026953 = 770215) B770215
theorem B1027175 : Blo 682313 1027175 := bstep (se 1 (by rfl) ⟨770381, by rfl⟩ : syracuseStep 1027175 = 1540763) B1540763
theorem B1028075 : Blo 682313 1028075 := bstep (se 1 (by rfl) ⟨771056, by rfl⟩ : syracuseStep 1028075 = 1542113) B1542113
theorem B7811963 : Blo 682313 7811963 := bstep (se 1 (by rfl) ⟨5858972, by rfl⟩ : syracuseStep 7811963 = 11717945) B11717945
theorem B3454973 : Blo 682313 3454973 := bstep (se 3 (by rfl) ⟨647807, by rfl⟩ : syracuseStep 3454973 = 1295615) B1295615
theorem B7616687 : Blo 682313 7616687 := bstep (se 1 (by rfl) ⟨5712515, by rfl⟩ : syracuseStep 7616687 = 11425031) B11425031
theorem B1096559 : Blo 682313 1096559 := bstep (se 1 (by rfl) ⟨822419, by rfl⟩ : syracuseStep 1096559 = 1644839) B1644839
theorem B2997611 : Blo 682313 2997611 := bstep (se 1 (by rfl) ⟨2248208, by rfl⟩ : syracuseStep 2997611 = 4496417) B4496417
theorem B2309687 : Blo 682313 2309687 := bstep (se 1 (by rfl) ⟨1732265, by rfl⟩ : syracuseStep 2309687 = 3464531) B3464531
theorem B5194367 : Blo 682313 5194367 := bstep (se 1 (by rfl) ⟨3895775, by rfl⟩ : syracuseStep 5194367 = 7791551) B7791551
theorem B2311955 : Blo 682313 2311955 := bstep (se 1 (by rfl) ⟨1733966, by rfl⟩ : syracuseStep 2311955 = 3467933) B3467933
theorem B7393427 : Blo 682313 7393427 := bstep (se 1 (by rfl) ⟨5545070, by rfl⟩ : syracuseStep 7393427 = 11090141) B11090141
theorem B3461615 : Blo 682313 3461615 := bstep (se 1 (by rfl) ⟨2596211, by rfl⟩ : syracuseStep 3461615 = 5192423) B5192423
theorem B6575741 : Blo 682313 6575741 := bstep (se 3 (by rfl) ⟨1232951, by rfl⟩ : syracuseStep 6575741 = 2465903) B2465903
theorem B1727183 : Blo 682313 1727183 := bstep (se 1 (by rfl) ⟨1295387, by rfl⟩ : syracuseStep 1727183 = 2590775) B2590775
theorem B5561257 : Blo 682313 5561257 := bstep (se 2 (by rfl) ⟨2085471, by rfl⟩ : syracuseStep 5561257 = 4170943) B4170943
theorem B3335423 : Blo 682313 3335423 := bstep (se 1 (by rfl) ⟨2501567, by rfl⟩ : syracuseStep 3335423 = 5003135) B5003135
theorem B17491625 : Blo 682313 17491625 := bstep (se 2 (by rfl) ⟨6559359, by rfl⟩ : syracuseStep 17491625 = 13118719) B13118719
theorem B682587 : Blo 682313 682587 := bstep (se 1 (by rfl) ⟨511940, by rfl⟩ : syracuseStep 682587 = 1023881) B1023881
theorem B2780839 : Blo 682313 2780839 := bstep (se 1 (by rfl) ⟨2085629, by rfl⟩ : syracuseStep 2780839 = 4171259) B4171259
theorem B24932519 : Blo 682313 24932519 := bstep (se 1 (by rfl) ⟨18699389, by rfl⟩ : syracuseStep 24932519 = 37398779) B37398779
theorem B684699 : Blo 682313 684699 := bstep (se 1 (by rfl) ⟨513524, by rfl⟩ : syracuseStep 684699 = 1027049) B1027049
theorem B684735 : Blo 682313 684735 := bstep (se 1 (by rfl) ⟨513551, by rfl⟩ : syracuseStep 684735 = 1027103) B1027103
theorem B1733339 : Blo 682313 1733339 := bstep (se 1 (by rfl) ⟨1300004, by rfl⟩ : syracuseStep 1733339 = 2600009) B2600009
theorem B6584237 : Blo 682313 6584237 := bstep (se 3 (by rfl) ⟨1234544, by rfl⟩ : syracuseStep 6584237 = 2469089) B2469089
theorem B686239 : Blo 682313 686239 := bstep (se 1 (by rfl) ⟨514679, by rfl⟩ : syracuseStep 686239 = 1029359) B1029359
theorem B3112843 : Blo 682313 3112843 := bstep (se 1 (by rfl) ⟨2334632, by rfl⟩ : syracuseStep 3112843 = 4669265) B4669265
theorem B1541303 : Blo 682313 1541303 := bstep (se 1 (by rfl) ⟨1155977, by rfl⟩ : syracuseStep 1541303 = 2311955) B2311955
theorem B84085775 : Blo 682313 84085775 := bstep (se 1 (by rfl) ⟨63064331, by rfl⟩ : syracuseStep 84085775 = 126128663) B126128663
theorem B1151455 : Blo 682313 1151455 := bstep (se 1 (by rfl) ⟨863591, by rfl⟩ : syracuseStep 1151455 = 1727183) B1727183
theorem B3707785 : Blo 682313 3707785 := bstep (se 2 (by rfl) ⟨1390419, by rfl⟩ : syracuseStep 3707785 = 2780839) B2780839
theorem B16621679 : Blo 682313 16621679 := bstep (se 1 (by rfl) ⟨12466259, by rfl⟩ : syracuseStep 16621679 = 24932519) B24932519
theorem B1155559 : Blo 682313 1155559 := bstep (se 1 (by rfl) ⟨866669, by rfl⟩ : syracuseStep 1155559 = 1733339) B1733339
theorem B7415009 : Blo 682313 7415009 := bstep (se 2 (by rfl) ⟨2780628, by rfl⟩ : syracuseStep 7415009 = 5561257) B5561257
theorem B2303315 : Blo 682313 2303315 := bstep (se 1 (by rfl) ⟨1727486, by rfl⟩ : syracuseStep 2303315 = 3454973) B3454973
theorem B731039 : Blo 682313 731039 := bstep (se 1 (by rfl) ⟨548279, by rfl⟩ : syracuseStep 731039 = 1096559) B1096559
theorem B1157935 : Blo 682313 1157935 := bstep (se 1 (by rfl) ⟨868451, by rfl⟩ : syracuseStep 1157935 = 1736903) B1736903
theorem B1027199 : Blo 682313 1027199 := bstep (se 1 (by rfl) ⟨770399, by rfl⟩ : syracuseStep 1027199 = 1540799) B1540799
theorem B2927983 : Blo 682313 2927983 := bstep (se 1 (by rfl) ⟨2195987, by rfl⟩ : syracuseStep 2927983 = 4391975) B4391975
theorem B1093753 : Blo 682313 1093753 := bstep (se 2 (by rfl) ⟨410157, by rfl⟩ : syracuseStep 1093753 = 820315) B820315
theorem B10531225 : Blo 682313 10531225 := bstep (se 2 (by rfl) ⟨3949209, by rfl⟩ : syracuseStep 10531225 = 7898419) B7898419
theorem B5550551 : Blo 682313 5550551 := bstep (se 1 (by rfl) ⟨4162913, by rfl⟩ : syracuseStep 5550551 = 8325827) B8325827
theorem B1028591 : Blo 682313 1028591 := bstep (se 1 (by rfl) ⟨771443, by rfl⟩ : syracuseStep 1028591 = 1542887) B1542887
theorem B4928951 : Blo 682313 4928951 := bstep (se 1 (by rfl) ⟨3696713, by rfl⟩ : syracuseStep 4928951 = 7393427) B7393427
theorem B2307743 : Blo 682313 2307743 := bstep (se 1 (by rfl) ⟨1730807, by rfl⟩ : syracuseStep 2307743 = 3461615) B3461615
theorem B8894461 : Blo 682313 8894461 := bstep (se 3 (by rfl) ⟨1667711, by rfl⟩ : syracuseStep 8894461 = 3335423) B3335423
theorem B44350415 : Blo 682313 44350415 := bstep (se 1 (by rfl) ⟨33262811, by rfl⟩ : syracuseStep 44350415 = 66525623) B66525623
theorem B4150457 : Blo 682313 4150457 := bstep (se 2 (by rfl) ⟨1556421, by rfl⟩ : syracuseStep 4150457 = 3112843) B3112843
theorem B3462911 : Blo 682313 3462911 := bstep (se 1 (by rfl) ⟨2597183, by rfl⟩ : syracuseStep 3462911 = 5194367) B5194367
theorem B54876409 : Blo 682313 54876409 := bstep (se 2 (by rfl) ⟨20578653, by rfl⟩ : syracuseStep 54876409 = 41157307) B41157307
theorem B5856239 : Blo 682313 5856239 := bstep (se 1 (by rfl) ⟨4392179, by rfl⟩ : syracuseStep 5856239 = 8784359) B8784359
theorem B5266471 : Blo 682313 5266471 := bstep (se 1 (by rfl) ⟨3949853, by rfl⟩ : syracuseStep 5266471 = 7899707) B7899707
theorem B4383827 : Blo 682313 4383827 := bstep (se 1 (by rfl) ⟨3287870, by rfl⟩ : syracuseStep 4383827 = 6575741) B6575741
theorem B11823515 : Blo 682313 11823515 := bstep (se 1 (by rfl) ⟨8867636, by rfl⟩ : syracuseStep 11823515 = 17735273) B17735273
theorem B1731071 : Blo 682313 1731071 := bstep (se 1 (by rfl) ⟨1298303, by rfl⟩ : syracuseStep 1731071 = 2596607) B2596607
theorem B682727 : Blo 682313 682727 := bstep (se 1 (by rfl) ⟨512045, by rfl⟩ : syracuseStep 682727 = 1024091) B1024091
theorem B20311165 : Blo 682313 20311165 := bstep (se 3 (by rfl) ⟨3808343, by rfl⟩ : syracuseStep 20311165 = 7616687) B7616687
theorem B683259 : Blo 682313 683259 := bstep (se 1 (by rfl) ⟨512444, by rfl⟩ : syracuseStep 683259 = 1024889) B1024889
theorem B683759 : Blo 682313 683759 := bstep (se 1 (by rfl) ⟨512819, by rfl⟩ : syracuseStep 683759 = 1025639) B1025639
theorem B11661083 : Blo 682313 11661083 := bstep (se 1 (by rfl) ⟨8745812, by rfl⟩ : syracuseStep 11661083 = 17491625) B17491625
theorem B24998489 : Blo 682313 24998489 := bstep (se 2 (by rfl) ⟨9374433, by rfl⟩ : syracuseStep 24998489 = 18748867) B18748867
theorem B684635 : Blo 682313 684635 := bstep (se 1 (by rfl) ⟨513476, by rfl⟩ : syracuseStep 684635 = 1026953) B1026953
theorem B684783 : Blo 682313 684783 := bstep (se 1 (by rfl) ⟨513587, by rfl⟩ : syracuseStep 684783 = 1027175) B1027175
theorem B685383 : Blo 682313 685383 := bstep (se 1 (by rfl) ⟨514037, by rfl⟩ : syracuseStep 685383 = 1028075) B1028075
theorem B5207975 : Blo 682313 5207975 := bstep (se 1 (by rfl) ⟨3905981, by rfl⟩ : syracuseStep 5207975 = 7811963) B7811963
theorem B8747453 : Blo 682313 8747453 := bstep (se 3 (by rfl) ⟨1640147, by rfl⟩ : syracuseStep 8747453 = 3280295) B3280295
theorem B4389491 : Blo 682313 4389491 := bstep (se 1 (by rfl) ⟨3292118, by rfl⟩ : syracuseStep 4389491 = 6584237) B6584237
theorem B1998407 : Blo 682313 1998407 := bstep (se 1 (by rfl) ⟨1498805, by rfl⟩ : syracuseStep 1998407 = 2997611) B2997611
theorem B1539791 : Blo 682313 1539791 := bstep (se 1 (by rfl) ⟨1154843, by rfl⟩ : syracuseStep 1539791 = 2309687) B2309687
theorem B1540745 : Blo 682313 1540745 := bstep (se 2 (by rfl) ⟨577779, by rfl⟩ : syracuseStep 1540745 = 1155559) B1155559
theorem B1543913 : Blo 682313 1543913 := bstep (se 2 (by rfl) ⟨578967, by rfl⟩ : syracuseStep 1543913 = 1157935) B1157935
theorem B13143869 : Blo 682313 13143869 := bstep (se 3 (by rfl) ⟨2464475, by rfl⟩ : syracuseStep 13143869 = 4928951) B4928951
theorem B3903977 : Blo 682313 3903977 := bstep (se 2 (by rfl) ⟨1463991, by rfl⟩ : syracuseStep 3903977 = 2927983) B2927983
theorem B3904159 : Blo 682313 3904159 := bstep (se 1 (by rfl) ⟨2928119, by rfl⟩ : syracuseStep 3904159 = 5856239) B5856239
theorem B11081119 : Blo 682313 11081119 := bstep (se 1 (by rfl) ⟨8310839, by rfl⟩ : syracuseStep 11081119 = 16621679) B16621679
theorem B2922551 : Blo 682313 2922551 := bstep (se 1 (by rfl) ⟨2191913, by rfl⟩ : syracuseStep 2922551 = 4383827) B4383827
theorem B1154047 : Blo 682313 1154047 := bstep (se 1 (by rfl) ⟨865535, by rfl⟩ : syracuseStep 1154047 = 1731071) B1731071
theorem B7774055 : Blo 682313 7774055 := bstep (se 1 (by rfl) ⟨5830541, by rfl⟩ : syracuseStep 7774055 = 11661083) B11661083
theorem B7021961 : Blo 682313 7021961 := bstep (se 2 (by rfl) ⟨2633235, by rfl⟩ : syracuseStep 7021961 = 5266471) B5266471
theorem B2926327 : Blo 682313 2926327 := bstep (se 1 (by rfl) ⟨2194745, by rfl⟩ : syracuseStep 2926327 = 4389491) B4389491
theorem B29566943 : Blo 682313 29566943 := bstep (se 1 (by rfl) ⟨22175207, by rfl⟩ : syracuseStep 29566943 = 44350415) B44350415
theorem B1026527 : Blo 682313 1026527 := bstep (se 1 (by rfl) ⟨769895, by rfl⟩ : syracuseStep 1026527 = 1539791) B1539791
theorem B1027535 : Blo 682313 1027535 := bstep (se 1 (by rfl) ⟨770651, by rfl⟩ : syracuseStep 1027535 = 1541303) B1541303
theorem B2766971 : Blo 682313 2766971 := bstep (se 1 (by rfl) ⟨2075228, by rfl⟩ : syracuseStep 2766971 = 4150457) B4150457
theorem B2308607 : Blo 682313 2308607 := bstep (se 1 (by rfl) ⟨1731455, by rfl⟩ : syracuseStep 2308607 = 3462911) B3462911
theorem B27081553 : Blo 682313 27081553 := bstep (se 2 (by rfl) ⟨10155582, by rfl⟩ : syracuseStep 27081553 = 20311165) B20311165
theorem B19774853 : Blo 682313 19774853 := bstep (se 4 (by rfl) ⟨1853892, by rfl⟩ : syracuseStep 19774853 = 3707785) B3707785
theorem B1949437 : Blo 682313 1949437 := bstep (se 3 (by rfl) ⟨365519, by rfl⟩ : syracuseStep 1949437 = 731039) B731039
theorem B1458337 : Blo 682313 1458337 := bstep (se 2 (by rfl) ⟨546876, by rfl⟩ : syracuseStep 1458337 = 1093753) B1093753
theorem B14041633 : Blo 682313 14041633 := bstep (se 2 (by rfl) ⟨5265612, by rfl⟩ : syracuseStep 14041633 = 10531225) B10531225
theorem B7882343 : Blo 682313 7882343 := bstep (se 1 (by rfl) ⟨5911757, by rfl⟩ : syracuseStep 7882343 = 11823515) B11823515
theorem B16665659 : Blo 682313 16665659 := bstep (se 1 (by rfl) ⟨12499244, by rfl⟩ : syracuseStep 16665659 = 24998489) B24998489
theorem B1332271 : Blo 682313 1332271 := bstep (se 1 (by rfl) ⟨999203, by rfl⟩ : syracuseStep 1332271 = 1998407) B1998407
theorem B292674181 : Blo 682313 292674181 := bstep (se 4 (by rfl) ⟨27438204, by rfl⟩ : syracuseStep 292674181 = 54876409) B54876409
theorem B56057183 : Blo 682313 56057183 := bstep (se 1 (by rfl) ⟨42042887, by rfl⟩ : syracuseStep 56057183 = 84085775) B84085775
theorem B1535273 : Blo 682313 1535273 := bstep (se 2 (by rfl) ⟨575727, by rfl⟩ : syracuseStep 1535273 = 1151455) B1151455
theorem B4943339 : Blo 682313 4943339 := bstep (se 1 (by rfl) ⟨3707504, by rfl⟩ : syracuseStep 4943339 = 7415009) B7415009
theorem B1535543 : Blo 682313 1535543 := bstep (se 1 (by rfl) ⟨1151657, by rfl⟩ : syracuseStep 1535543 = 2303315) B2303315
theorem B684799 : Blo 682313 684799 := bstep (se 1 (by rfl) ⟨513599, by rfl⟩ : syracuseStep 684799 = 1027199) B1027199
theorem B11859281 : Blo 682313 11859281 := bstep (se 2 (by rfl) ⟨4447230, by rfl⟩ : syracuseStep 11859281 = 8894461) B8894461
theorem B3700367 : Blo 682313 3700367 := bstep (se 1 (by rfl) ⟨2775275, by rfl⟩ : syracuseStep 3700367 = 5550551) B5550551
theorem B685727 : Blo 682313 685727 := bstep (se 1 (by rfl) ⟨514295, by rfl⟩ : syracuseStep 685727 = 1028591) B1028591
theorem B1538495 : Blo 682313 1538495 := bstep (se 1 (by rfl) ⟨1153871, by rfl⟩ : syracuseStep 1538495 = 2307743) B2307743
theorem B3471983 : Blo 682313 3471983 := bstep (se 1 (by rfl) ⟨2603987, by rfl⟩ : syracuseStep 3471983 = 5207975) B5207975
theorem B5831635 : Blo 682313 5831635 := bstep (se 1 (by rfl) ⟨4373726, by rfl⟩ : syracuseStep 5831635 = 8747453) B8747453
theorem B11110439 : Blo 682313 11110439 := bstep (se 1 (by rfl) ⟨8332829, by rfl⟩ : syracuseStep 11110439 = 16665659) B16665659
theorem B3901769 : Blo 682313 3901769 := bstep (se 2 (by rfl) ⟨1463163, by rfl⟩ : syracuseStep 3901769 = 2926327) B2926327
theorem B5182703 : Blo 682313 5182703 := bstep (se 1 (by rfl) ⟨3887027, by rfl⟩ : syracuseStep 5182703 = 7774055) B7774055
theorem B7378589 : Blo 682313 7378589 := bstep (se 3 (by rfl) ⟨1383485, by rfl⟩ : syracuseStep 7378589 = 2766971) B2766971
theorem B1776361 : Blo 682313 1776361 := bstep (se 2 (by rfl) ⟨666135, by rfl⟩ : syracuseStep 1776361 = 1332271) B1332271
theorem B1023515 : Blo 682313 1023515 := bstep (se 1 (by rfl) ⟨767636, by rfl⟩ : syracuseStep 1023515 = 1535273) B1535273
theorem B1023695 : Blo 682313 1023695 := bstep (se 1 (by rfl) ⟨767771, by rfl⟩ : syracuseStep 1023695 = 1535543) B1535543
theorem B7906187 : Blo 682313 7906187 := bstep (se 1 (by rfl) ⟨5929640, by rfl⟩ : syracuseStep 7906187 = 11859281) B11859281
theorem B2466911 : Blo 682313 2466911 := bstep (se 1 (by rfl) ⟨1850183, by rfl⟩ : syracuseStep 2466911 = 3700367) B3700367
theorem B7775513 : Blo 682313 7775513 := bstep (se 2 (by rfl) ⟨2915817, by rfl⟩ : syracuseStep 7775513 = 5831635) B5831635
theorem B1025663 : Blo 682313 1025663 := bstep (se 1 (by rfl) ⟨769247, by rfl⟩ : syracuseStep 1025663 = 1538495) B1538495
theorem B13183235 : Blo 682313 13183235 := bstep (se 1 (by rfl) ⟨9887426, by rfl⟩ : syracuseStep 13183235 = 19774853) B19774853
theorem B2599249 : Blo 682313 2599249 := bstep (se 2 (by rfl) ⟨974718, by rfl⟩ : syracuseStep 2599249 = 1949437) B1949437
theorem B1944449 : Blo 682313 1944449 := bstep (se 2 (by rfl) ⟨729168, by rfl⟩ : syracuseStep 1944449 = 1458337) B1458337
theorem B1027163 : Blo 682313 1027163 := bstep (se 1 (by rfl) ⟨770372, by rfl⟩ : syracuseStep 1027163 = 1540745) B1540745
theorem B18722177 : Blo 682313 18722177 := bstep (se 2 (by rfl) ⟨7020816, by rfl⟩ : syracuseStep 18722177 = 14041633) B14041633
theorem B5254895 : Blo 682313 5254895 := bstep (se 1 (by rfl) ⟨3941171, by rfl⟩ : syracuseStep 5254895 = 7882343) B7882343
theorem B1029275 : Blo 682313 1029275 := bstep (se 1 (by rfl) ⟨771956, by rfl⟩ : syracuseStep 1029275 = 1543913) B1543913
theorem B8762579 : Blo 682313 8762579 := bstep (se 1 (by rfl) ⟨6571934, by rfl⟩ : syracuseStep 8762579 = 13143869) B13143869
theorem B2602651 : Blo 682313 2602651 := bstep (se 1 (by rfl) ⟨1951988, by rfl⟩ : syracuseStep 2602651 = 3903977) B3903977
theorem B1948367 : Blo 682313 1948367 := bstep (se 1 (by rfl) ⟨1461275, by rfl⟩ : syracuseStep 1948367 = 2922551) B2922551
theorem B37371455 : Blo 682313 37371455 := bstep (se 1 (by rfl) ⟨28028591, by rfl⟩ : syracuseStep 37371455 = 56057183) B56057183
theorem B19711295 : Blo 682313 19711295 := bstep (se 1 (by rfl) ⟨14783471, by rfl⟩ : syracuseStep 19711295 = 29566943) B29566943
theorem B3295559 : Blo 682313 3295559 := bstep (se 1 (by rfl) ⟨2471669, by rfl⟩ : syracuseStep 3295559 = 4943339) B4943339
theorem B2314655 : Blo 682313 2314655 := bstep (se 1 (by rfl) ⟨1735991, by rfl⟩ : syracuseStep 2314655 = 3471983) B3471983
theorem B5205545 : Blo 682313 5205545 := bstep (se 2 (by rfl) ⟨1952079, by rfl⟩ : syracuseStep 5205545 = 3904159) B3904159
theorem B4681307 : Blo 682313 4681307 := bstep (se 1 (by rfl) ⟨3510980, by rfl⟩ : syracuseStep 4681307 = 7021961) B7021961
theorem B684351 : Blo 682313 684351 := bstep (se 1 (by rfl) ⟨513263, by rfl⟩ : syracuseStep 684351 = 1026527) B1026527
theorem B14774825 : Blo 682313 14774825 := bstep (se 2 (by rfl) ⟨5540559, by rfl⟩ : syracuseStep 14774825 = 11081119) B11081119
theorem B685023 : Blo 682313 685023 := bstep (se 1 (by rfl) ⟨513767, by rfl⟩ : syracuseStep 685023 = 1027535) B1027535
theorem B390232241 : Blo 682313 390232241 := bstep (se 2 (by rfl) ⟨146337090, by rfl⟩ : syracuseStep 390232241 = 292674181) B292674181
theorem B36108737 : Blo 682313 36108737 := bstep (se 2 (by rfl) ⟨13540776, by rfl⟩ : syracuseStep 36108737 = 27081553) B27081553
theorem B1538729 : Blo 682313 1538729 := bstep (se 2 (by rfl) ⟨577023, by rfl⟩ : syracuseStep 1538729 = 1154047) B1154047
theorem B1539071 : Blo 682313 1539071 := bstep (se 1 (by rfl) ⟨1154303, by rfl⟩ : syracuseStep 1539071 = 2308607) B2308607
theorem B13140863 : Blo 682313 13140863 := bstep (se 1 (by rfl) ⟨9855647, by rfl⟩ : syracuseStep 13140863 = 19711295) B19711295
theorem B7406959 : Blo 682313 7406959 := bstep (se 1 (by rfl) ⟨5555219, by rfl⟩ : syracuseStep 7406959 = 11110439) B11110439
theorem B2197039 : Blo 682313 2197039 := bstep (se 1 (by rfl) ⟨1647779, by rfl⟩ : syracuseStep 2197039 = 3295559) B3295559
theorem B1543103 : Blo 682313 1543103 := bstep (se 1 (by rfl) ⟨1157327, by rfl⟩ : syracuseStep 1543103 = 2314655) B2314655
theorem B4919059 : Blo 682313 4919059 := bstep (se 1 (by rfl) ⟨3689294, by rfl⟩ : syracuseStep 4919059 = 7378589) B7378589
theorem B1644607 : Blo 682313 1644607 := bstep (se 1 (by rfl) ⟨1233455, by rfl⟩ : syracuseStep 1644607 = 2466911) B2466911
theorem B5183675 : Blo 682313 5183675 := bstep (se 1 (by rfl) ⟨3887756, by rfl⟩ : syracuseStep 5183675 = 7775513) B7775513
theorem B8788823 : Blo 682313 8788823 := bstep (se 1 (by rfl) ⟨6591617, by rfl⟩ : syracuseStep 8788823 = 13183235) B13183235
theorem B3120871 : Blo 682313 3120871 := bstep (se 1 (by rfl) ⟨2340653, by rfl⟩ : syracuseStep 3120871 = 4681307) B4681307
theorem B5841719 : Blo 682313 5841719 := bstep (se 1 (by rfl) ⟨4381289, by rfl⟩ : syracuseStep 5841719 = 8762579) B8762579
theorem B2368481 : Blo 682313 2368481 := bstep (se 2 (by rfl) ⟨888180, by rfl⟩ : syracuseStep 2368481 = 1776361) B1776361
theorem B260154827 : Blo 682313 260154827 := bstep (se 1 (by rfl) ⟨195116120, by rfl⟩ : syracuseStep 260154827 = 390232241) B390232241
theorem B1025819 : Blo 682313 1025819 := bstep (se 1 (by rfl) ⟨769364, by rfl⟩ : syracuseStep 1025819 = 1538729) B1538729
theorem B1026047 : Blo 682313 1026047 := bstep (se 1 (by rfl) ⟨769535, by rfl⟩ : syracuseStep 1026047 = 1539071) B1539071
theorem B24914303 : Blo 682313 24914303 := bstep (se 1 (by rfl) ⟨18685727, by rfl⟩ : syracuseStep 24914303 = 37371455) B37371455
theorem B2601179 : Blo 682313 2601179 := bstep (se 1 (by rfl) ⟨1950884, by rfl⟩ : syracuseStep 2601179 = 3901769) B3901769
theorem B3455135 : Blo 682313 3455135 := bstep (se 1 (by rfl) ⟨2591351, by rfl⟩ : syracuseStep 3455135 = 5182703) B5182703
theorem B1296299 : Blo 682313 1296299 := bstep (se 1 (by rfl) ⟨972224, by rfl⟩ : syracuseStep 1296299 = 1944449) B1944449
theorem B9849883 : Blo 682313 9849883 := bstep (se 1 (by rfl) ⟨7387412, by rfl⟩ : syracuseStep 9849883 = 14774825) B14774825
theorem B24072491 : Blo 682313 24072491 := bstep (se 1 (by rfl) ⟨18054368, by rfl⟩ : syracuseStep 24072491 = 36108737) B36108737
theorem B1298911 : Blo 682313 1298911 := bstep (se 1 (by rfl) ⟨974183, by rfl⟩ : syracuseStep 1298911 = 1948367) B1948367
theorem B3465665 : Blo 682313 3465665 := bstep (se 2 (by rfl) ⟨1299624, by rfl⟩ : syracuseStep 3465665 = 2599249) B2599249
theorem B682343 : Blo 682313 682343 := bstep (se 1 (by rfl) ⟨511757, by rfl⟩ : syracuseStep 682343 = 1023515) B1023515
theorem B682463 : Blo 682313 682463 := bstep (se 1 (by rfl) ⟨511847, by rfl⟩ : syracuseStep 682463 = 1023695) B1023695
theorem B5270791 : Blo 682313 5270791 := bstep (se 1 (by rfl) ⟨3953093, by rfl⟩ : syracuseStep 5270791 = 7906187) B7906187
theorem B683775 : Blo 682313 683775 := bstep (se 1 (by rfl) ⟨512831, by rfl⟩ : syracuseStep 683775 = 1025663) B1025663
theorem B684775 : Blo 682313 684775 := bstep (se 1 (by rfl) ⟨513581, by rfl⟩ : syracuseStep 684775 = 1027163) B1027163
theorem B3470201 : Blo 682313 3470201 := bstep (se 2 (by rfl) ⟨1301325, by rfl⟩ : syracuseStep 3470201 = 2602651) B2602651
theorem B12481451 : Blo 682313 12481451 := bstep (se 1 (by rfl) ⟨9361088, by rfl⟩ : syracuseStep 12481451 = 18722177) B18722177
theorem B3470363 : Blo 682313 3470363 := bstep (se 1 (by rfl) ⟨2602772, by rfl⟩ : syracuseStep 3470363 = 5205545) B5205545
theorem B3503263 : Blo 682313 3503263 := bstep (se 1 (by rfl) ⟨2627447, by rfl⟩ : syracuseStep 3503263 = 5254895) B5254895
theorem B686183 : Blo 682313 686183 := bstep (se 1 (by rfl) ⟨514637, by rfl⟩ : syracuseStep 686183 = 1029275) B1029275
theorem B6558745 : Blo 682313 6558745 := bstep (se 2 (by rfl) ⟨2459529, by rfl⟩ : syracuseStep 6558745 = 4919059) B4919059
theorem B2303423 : Blo 682313 2303423 := bstep (se 1 (by rfl) ⟨1727567, by rfl⟩ : syracuseStep 2303423 = 3455135) B3455135
theorem B8760575 : Blo 682313 8760575 := bstep (se 1 (by rfl) ⟨6570431, by rfl⟩ : syracuseStep 8760575 = 13140863) B13140863
theorem B864199 : Blo 682313 864199 := bstep (se 1 (by rfl) ⟨648149, by rfl⟩ : syracuseStep 864199 = 1296299) B1296299
theorem B9875945 : Blo 682313 9875945 := bstep (se 2 (by rfl) ⟨3703479, by rfl⟩ : syracuseStep 9875945 = 7406959) B7406959
theorem B1028735 : Blo 682313 1028735 := bstep (se 1 (by rfl) ⟨771551, by rfl⟩ : syracuseStep 1028735 = 1543103) B1543103
theorem B2929385 : Blo 682313 2929385 := bstep (se 2 (by rfl) ⟨1098519, by rfl⟩ : syracuseStep 2929385 = 2197039) B2197039
theorem B3455783 : Blo 682313 3455783 := bstep (se 1 (by rfl) ⟨2591837, by rfl⟩ : syracuseStep 3455783 = 5183675) B5183675
theorem B7027721 : Blo 682313 7027721 := bstep (se 2 (by rfl) ⟨2635395, by rfl⟩ : syracuseStep 7027721 = 5270791) B5270791
theorem B2310443 : Blo 682313 2310443 := bstep (se 1 (by rfl) ⟨1732832, by rfl⟩ : syracuseStep 2310443 = 3465665) B3465665
theorem B4671017 : Blo 682313 4671017 := bstep (se 2 (by rfl) ⟨1751631, by rfl⟩ : syracuseStep 4671017 = 3503263) B3503263
theorem B2313467 : Blo 682313 2313467 := bstep (se 1 (by rfl) ⟨1735100, by rfl⟩ : syracuseStep 2313467 = 3470201) B3470201
theorem B2313575 : Blo 682313 2313575 := bstep (se 1 (by rfl) ⟨1735181, by rfl⟩ : syracuseStep 2313575 = 3470363) B3470363
theorem B8771237 : Blo 682313 8771237 := bstep (se 4 (by rfl) ⟨822303, by rfl⟩ : syracuseStep 8771237 = 1644607) B1644607
theorem B16048327 : Blo 682313 16048327 := bstep (se 1 (by rfl) ⟨12036245, by rfl⟩ : syracuseStep 16048327 = 24072491) B24072491
theorem B13133177 : Blo 682313 13133177 := bstep (se 2 (by rfl) ⟨4924941, by rfl⟩ : syracuseStep 13133177 = 9849883) B9849883
theorem B5859215 : Blo 682313 5859215 := bstep (se 1 (by rfl) ⟨4394411, by rfl⟩ : syracuseStep 5859215 = 8788823) B8788823
theorem B3894479 : Blo 682313 3894479 := bstep (se 1 (by rfl) ⟨2920859, by rfl⟩ : syracuseStep 3894479 = 5841719) B5841719
theorem B1731881 : Blo 682313 1731881 := bstep (se 2 (by rfl) ⟨649455, by rfl⟩ : syracuseStep 1731881 = 1298911) B1298911
theorem B173436551 : Blo 682313 173436551 := bstep (se 1 (by rfl) ⟨130077413, by rfl⟩ : syracuseStep 173436551 = 260154827) B260154827
theorem B683879 : Blo 682313 683879 := bstep (se 1 (by rfl) ⟨512909, by rfl⟩ : syracuseStep 683879 = 1025819) B1025819
theorem B684031 : Blo 682313 684031 := bstep (se 1 (by rfl) ⟨513023, by rfl⟩ : syracuseStep 684031 = 1026047) B1026047
theorem B16609535 : Blo 682313 16609535 := bstep (se 1 (by rfl) ⟨12457151, by rfl⟩ : syracuseStep 16609535 = 24914303) B24914303
theorem B1734119 : Blo 682313 1734119 := bstep (se 1 (by rfl) ⟨1300589, by rfl⟩ : syracuseStep 1734119 = 2601179) B2601179
theorem B8320967 : Blo 682313 8320967 := bstep (se 1 (by rfl) ⟨6240725, by rfl⟩ : syracuseStep 8320967 = 12481451) B12481451
theorem B4161161 : Blo 682313 4161161 := bstep (se 2 (by rfl) ⟨1560435, by rfl⟩ : syracuseStep 4161161 = 3120871) B3120871
theorem B25263797 : Blo 682313 25263797 := bstep (se 5 (by rfl) ⟨1184240, by rfl⟩ : syracuseStep 25263797 = 2368481) B2368481
theorem B1540295 : Blo 682313 1540295 := bstep (se 1 (by rfl) ⟨1155221, by rfl⟩ : syracuseStep 1540295 = 2310443) B2310443
theorem B21397769 : Blo 682313 21397769 := bstep (se 2 (by rfl) ⟨8024163, by rfl⟩ : syracuseStep 21397769 = 16048327) B16048327
theorem B3114011 : Blo 682313 3114011 := bstep (se 1 (by rfl) ⟨2335508, by rfl⟩ : syracuseStep 3114011 = 4671017) B4671017
theorem B1542311 : Blo 682313 1542311 := bstep (se 1 (by rfl) ⟨1156733, by rfl⟩ : syracuseStep 1542311 = 2313467) B2313467
theorem B1542383 : Blo 682313 1542383 := bstep (se 1 (by rfl) ⟨1156787, by rfl⟩ : syracuseStep 1542383 = 2313575) B2313575
theorem B1152265 : Blo 682313 1152265 := bstep (se 2 (by rfl) ⟨432099, by rfl⟩ : syracuseStep 1152265 = 864199) B864199
theorem B8755451 : Blo 682313 8755451 := bstep (se 1 (by rfl) ⟨6566588, by rfl⟩ : syracuseStep 8755451 = 13133177) B13133177
theorem B3906143 : Blo 682313 3906143 := bstep (se 1 (by rfl) ⟨2929607, by rfl⟩ : syracuseStep 3906143 = 5859215) B5859215
theorem B2596319 : Blo 682313 2596319 := bstep (se 1 (by rfl) ⟨1947239, by rfl⟩ : syracuseStep 2596319 = 3894479) B3894479
theorem B5840383 : Blo 682313 5840383 := bstep (se 1 (by rfl) ⟨4380287, by rfl⟩ : syracuseStep 5840383 = 8760575) B8760575
theorem B1154587 : Blo 682313 1154587 := bstep (se 1 (by rfl) ⟨865940, by rfl⟩ : syracuseStep 1154587 = 1731881) B1731881
theorem B1156079 : Blo 682313 1156079 := bstep (se 1 (by rfl) ⟨867059, by rfl⟩ : syracuseStep 1156079 = 1734119) B1734119
theorem B5547311 : Blo 682313 5547311 := bstep (se 1 (by rfl) ⟨4160483, by rfl⟩ : syracuseStep 5547311 = 8320967) B8320967
theorem B2303855 : Blo 682313 2303855 := bstep (se 1 (by rfl) ⟨1727891, by rfl⟩ : syracuseStep 2303855 = 3455783) B3455783
theorem B5847491 : Blo 682313 5847491 := bstep (se 1 (by rfl) ⟨4385618, by rfl⟩ : syracuseStep 5847491 = 8771237) B8771237
theorem B115624367 : Blo 682313 115624367 := bstep (se 1 (by rfl) ⟨86718275, by rfl⟩ : syracuseStep 115624367 = 173436551) B173436551
theorem B1952923 : Blo 682313 1952923 := bstep (se 1 (by rfl) ⟨1464692, by rfl⟩ : syracuseStep 1952923 = 2929385) B2929385
theorem B2774107 : Blo 682313 2774107 := bstep (se 1 (by rfl) ⟨2080580, by rfl⟩ : syracuseStep 2774107 = 4161161) B4161161
theorem B26335853 : Blo 682313 26335853 := bstep (se 3 (by rfl) ⟨4937972, by rfl⟩ : syracuseStep 26335853 = 9875945) B9875945
theorem B1535615 : Blo 682313 1535615 := bstep (se 1 (by rfl) ⟨1151711, by rfl⟩ : syracuseStep 1535615 = 2303423) B2303423
theorem B8744993 : Blo 682313 8744993 := bstep (se 2 (by rfl) ⟨3279372, by rfl⟩ : syracuseStep 8744993 = 6558745) B6558745
theorem B11073023 : Blo 682313 11073023 := bstep (se 1 (by rfl) ⟨8304767, by rfl⟩ : syracuseStep 11073023 = 16609535) B16609535
theorem B685823 : Blo 682313 685823 := bstep (se 1 (by rfl) ⟨514367, by rfl⟩ : syracuseStep 685823 = 1028735) B1028735
theorem B67370125 : Blo 682313 67370125 := bstep (se 3 (by rfl) ⟨12631898, by rfl⟩ : syracuseStep 67370125 = 25263797) B25263797
theorem B4685147 : Blo 682313 4685147 := bstep (se 1 (by rfl) ⟨3513860, by rfl⟩ : syracuseStep 4685147 = 7027721) B7027721
theorem B5836967 : Blo 682313 5836967 := bstep (se 1 (by rfl) ⟨4377725, by rfl⟩ : syracuseStep 5836967 = 8755451) B8755451
theorem B1023743 : Blo 682313 1023743 := bstep (se 1 (by rfl) ⟨767807, by rfl⟩ : syracuseStep 1023743 = 1535615) B1535615
theorem B7382015 : Blo 682313 7382015 := bstep (se 1 (by rfl) ⟨5536511, by rfl⟩ : syracuseStep 7382015 = 11073023) B11073023
theorem B89826833 : Blo 682313 89826833 := bstep (se 2 (by rfl) ⟨33685062, by rfl⟩ : syracuseStep 89826833 = 67370125) B67370125
theorem B3123431 : Blo 682313 3123431 := bstep (se 1 (by rfl) ⟨2342573, by rfl⟩ : syracuseStep 3123431 = 4685147) B4685147
theorem B1026863 : Blo 682313 1026863 := bstep (se 1 (by rfl) ⟨770147, by rfl⟩ : syracuseStep 1026863 = 1540295) B1540295
theorem B14265179 : Blo 682313 14265179 := bstep (se 1 (by rfl) ⟨10698884, by rfl⟩ : syracuseStep 14265179 = 21397769) B21397769
theorem B1028207 : Blo 682313 1028207 := bstep (se 1 (by rfl) ⟨771155, by rfl⟩ : syracuseStep 1028207 = 1542311) B1542311
theorem B1028255 : Blo 682313 1028255 := bstep (se 1 (by rfl) ⟨771191, by rfl⟩ : syracuseStep 1028255 = 1542383) B1542383
theorem B77082911 : Blo 682313 77082911 := bstep (se 1 (by rfl) ⟨57812183, by rfl⟩ : syracuseStep 77082911 = 115624367) B115624367
theorem B8304029 : Blo 682313 8304029 := bstep (se 3 (by rfl) ⟨1557005, by rfl⟩ : syracuseStep 8304029 = 3114011) B3114011
theorem B2603897 : Blo 682313 2603897 := bstep (se 2 (by rfl) ⟨976461, by rfl⟩ : syracuseStep 2603897 = 1952923) B1952923
theorem B2604095 : Blo 682313 2604095 := bstep (se 1 (by rfl) ⟨1953071, by rfl⟩ : syracuseStep 2604095 = 3906143) B3906143
theorem B14795237 : Blo 682313 14795237 := bstep (se 4 (by rfl) ⟨1387053, by rfl⟩ : syracuseStep 14795237 = 2774107) B2774107
theorem B770719 : Blo 682313 770719 := bstep (se 1 (by rfl) ⟨578039, by rfl⟩ : syracuseStep 770719 = 1156079) B1156079
theorem B7787177 : Blo 682313 7787177 := bstep (se 2 (by rfl) ⟨2920191, by rfl⟩ : syracuseStep 7787177 = 5840383) B5840383
theorem B17557235 : Blo 682313 17557235 := bstep (se 1 (by rfl) ⟨13167926, by rfl⟩ : syracuseStep 17557235 = 26335853) B26335853
theorem B1730879 : Blo 682313 1730879 := bstep (se 1 (by rfl) ⟨1298159, by rfl⟩ : syracuseStep 1730879 = 2596319) B2596319
theorem B3698207 : Blo 682313 3698207 := bstep (se 1 (by rfl) ⟨2773655, by rfl⟩ : syracuseStep 3698207 = 5547311) B5547311
theorem B1535903 : Blo 682313 1535903 := bstep (se 1 (by rfl) ⟨1151927, by rfl⟩ : syracuseStep 1535903 = 2303855) B2303855
theorem B1536353 : Blo 682313 1536353 := bstep (se 2 (by rfl) ⟨576132, by rfl⟩ : syracuseStep 1536353 = 1152265) B1152265
theorem B5829995 : Blo 682313 5829995 := bstep (se 1 (by rfl) ⟨4372496, by rfl⟩ : syracuseStep 5829995 = 8744993) B8744993
theorem B3898327 : Blo 682313 3898327 := bstep (se 1 (by rfl) ⟨2923745, by rfl⟩ : syracuseStep 3898327 = 5847491) B5847491
theorem B1539449 : Blo 682313 1539449 := bstep (se 2 (by rfl) ⟨577293, by rfl⟩ : syracuseStep 1539449 = 1154587) B1154587
theorem B9863491 : Blo 682313 9863491 := bstep (se 1 (by rfl) ⟨7397618, by rfl⟩ : syracuseStep 9863491 = 14795237) B14795237
theorem B4921343 : Blo 682313 4921343 := bstep (se 1 (by rfl) ⟨3691007, by rfl⟩ : syracuseStep 4921343 = 7382015) B7382015
theorem B11704823 : Blo 682313 11704823 := bstep (se 1 (by rfl) ⟨8778617, by rfl⟩ : syracuseStep 11704823 = 17557235) B17557235
theorem B1153919 : Blo 682313 1153919 := bstep (se 1 (by rfl) ⟨865439, by rfl⟩ : syracuseStep 1153919 = 1730879) B1730879
theorem B9510119 : Blo 682313 9510119 := bstep (se 1 (by rfl) ⟨7132589, by rfl⟩ : syracuseStep 9510119 = 14265179) B14265179
theorem B2465471 : Blo 682313 2465471 := bstep (se 1 (by rfl) ⟨1849103, by rfl⟩ : syracuseStep 2465471 = 3698207) B3698207
theorem B1023935 : Blo 682313 1023935 := bstep (se 1 (by rfl) ⟨767951, by rfl⟩ : syracuseStep 1023935 = 1535903) B1535903
theorem B51388607 : Blo 682313 51388607 := bstep (se 1 (by rfl) ⟨38541455, by rfl⟩ : syracuseStep 51388607 = 77082911) B77082911
theorem B1024235 : Blo 682313 1024235 := bstep (se 1 (by rfl) ⟨768176, by rfl⟩ : syracuseStep 1024235 = 1536353) B1536353
theorem B1026299 : Blo 682313 1026299 := bstep (se 1 (by rfl) ⟨769724, by rfl⟩ : syracuseStep 1026299 = 1539449) B1539449
theorem B1027625 : Blo 682313 1027625 := bstep (se 2 (by rfl) ⟨385359, by rfl⟩ : syracuseStep 1027625 = 770719) B770719
theorem B5191451 : Blo 682313 5191451 := bstep (se 1 (by rfl) ⟨3893588, by rfl⟩ : syracuseStep 5191451 = 7787177) B7787177
theorem B59884555 : Blo 682313 59884555 := bstep (se 1 (by rfl) ⟨44913416, by rfl⟩ : syracuseStep 59884555 = 89826833) B89826833
theorem B2082287 : Blo 682313 2082287 := bstep (se 1 (by rfl) ⟨1561715, by rfl⟩ : syracuseStep 2082287 = 3123431) B3123431
theorem B3886663 : Blo 682313 3886663 := bstep (se 1 (by rfl) ⟨2914997, by rfl⟩ : syracuseStep 3886663 = 5829995) B5829995
theorem B5197769 : Blo 682313 5197769 := bstep (se 2 (by rfl) ⟨1949163, by rfl⟩ : syracuseStep 5197769 = 3898327) B3898327
theorem B3891311 : Blo 682313 3891311 := bstep (se 1 (by rfl) ⟨2918483, by rfl⟩ : syracuseStep 3891311 = 5836967) B5836967
theorem B682495 : Blo 682313 682495 := bstep (se 1 (by rfl) ⟨511871, by rfl⟩ : syracuseStep 682495 = 1023743) B1023743
theorem B684575 : Blo 682313 684575 := bstep (se 1 (by rfl) ⟨513431, by rfl⟩ : syracuseStep 684575 = 1026863) B1026863
theorem B685471 : Blo 682313 685471 := bstep (se 1 (by rfl) ⟨514103, by rfl⟩ : syracuseStep 685471 = 1028207) B1028207
theorem B685503 : Blo 682313 685503 := bstep (se 1 (by rfl) ⟨514127, by rfl⟩ : syracuseStep 685503 = 1028255) B1028255
theorem B5536019 : Blo 682313 5536019 := bstep (se 1 (by rfl) ⟨4152014, by rfl⟩ : syracuseStep 5536019 = 8304029) B8304029
theorem B1735931 : Blo 682313 1735931 := bstep (se 1 (by rfl) ⟨1301948, by rfl⟩ : syracuseStep 1735931 = 2603897) B2603897
theorem B1736063 : Blo 682313 1736063 := bstep (se 1 (by rfl) ⟨1302047, by rfl⟩ : syracuseStep 1736063 = 2604095) B2604095
theorem B3280895 : Blo 682313 3280895 := bstep (se 1 (by rfl) ⟨2460671, by rfl⟩ : syracuseStep 3280895 = 4921343) B4921343
theorem B7803215 : Blo 682313 7803215 := bstep (se 1 (by rfl) ⟨5852411, by rfl⟩ : syracuseStep 7803215 = 11704823) B11704823
theorem B5182217 : Blo 682313 5182217 := bstep (se 2 (by rfl) ⟨1943331, by rfl⟩ : syracuseStep 5182217 = 3886663) B3886663
theorem B1643647 : Blo 682313 1643647 := bstep (se 1 (by rfl) ⟨1232735, by rfl⟩ : syracuseStep 1643647 = 2465471) B2465471
theorem B2594207 : Blo 682313 2594207 := bstep (se 1 (by rfl) ⟨1945655, by rfl⟩ : syracuseStep 2594207 = 3891311) B3891311
theorem B1157287 : Blo 682313 1157287 := bstep (se 1 (by rfl) ⟨867965, by rfl⟩ : syracuseStep 1157287 = 1735931) B1735931
theorem B1157375 : Blo 682313 1157375 := bstep (se 1 (by rfl) ⟨868031, by rfl⟩ : syracuseStep 1157375 = 1736063) B1736063
theorem B13151321 : Blo 682313 13151321 := bstep (se 2 (by rfl) ⟨4931745, by rfl⟩ : syracuseStep 13151321 = 9863491) B9863491
theorem B1388191 : Blo 682313 1388191 := bstep (se 1 (by rfl) ⟨1041143, by rfl⟩ : syracuseStep 1388191 = 2082287) B2082287
theorem B769279 : Blo 682313 769279 := bstep (se 1 (by rfl) ⟨576959, by rfl⟩ : syracuseStep 769279 = 1153919) B1153919
theorem B6340079 : Blo 682313 6340079 := bstep (se 1 (by rfl) ⟨4755059, by rfl⟩ : syracuseStep 6340079 = 9510119) B9510119
theorem B34259071 : Blo 682313 34259071 := bstep (se 1 (by rfl) ⟨25694303, by rfl⟩ : syracuseStep 34259071 = 51388607) B51388607
theorem B3460967 : Blo 682313 3460967 := bstep (se 1 (by rfl) ⟨2595725, by rfl⟩ : syracuseStep 3460967 = 5191451) B5191451
theorem B3690679 : Blo 682313 3690679 := bstep (se 1 (by rfl) ⟨2768009, by rfl⟩ : syracuseStep 3690679 = 5536019) B5536019
theorem B79846073 : Blo 682313 79846073 := bstep (se 2 (by rfl) ⟨29942277, by rfl⟩ : syracuseStep 79846073 = 59884555) B59884555
theorem B3465179 : Blo 682313 3465179 := bstep (se 1 (by rfl) ⟨2598884, by rfl⟩ : syracuseStep 3465179 = 5197769) B5197769
theorem B682623 : Blo 682313 682623 := bstep (se 1 (by rfl) ⟨511967, by rfl⟩ : syracuseStep 682623 = 1023935) B1023935
theorem B682823 : Blo 682313 682823 := bstep (se 1 (by rfl) ⟨512117, by rfl⟩ : syracuseStep 682823 = 1024235) B1024235
theorem B684199 : Blo 682313 684199 := bstep (se 1 (by rfl) ⟨513149, by rfl⟩ : syracuseStep 684199 = 1026299) B1026299
theorem B685083 : Blo 682313 685083 := bstep (se 1 (by rfl) ⟨513812, by rfl⟩ : syracuseStep 685083 = 1027625) B1027625
theorem B45678761 : Blo 682313 45678761 := bstep (se 2 (by rfl) ⟨17129535, by rfl⟩ : syracuseStep 45678761 = 34259071) B34259071
theorem B1543049 : Blo 682313 1543049 := bstep (se 2 (by rfl) ⟨578643, by rfl⟩ : syracuseStep 1543049 = 1157287) B1157287
theorem B4920905 : Blo 682313 4920905 := bstep (se 2 (by rfl) ⟨1845339, by rfl⟩ : syracuseStep 4920905 = 3690679) B3690679
theorem B1025705 : Blo 682313 1025705 := bstep (se 2 (by rfl) ⟨384639, by rfl⟩ : syracuseStep 1025705 = 769279) B769279
theorem B2307311 : Blo 682313 2307311 := bstep (se 1 (by rfl) ⟨1730483, by rfl⟩ : syracuseStep 2307311 = 3460967) B3460967
theorem B3454811 : Blo 682313 3454811 := bstep (se 1 (by rfl) ⟨2591108, by rfl⟩ : syracuseStep 3454811 = 5182217) B5182217
theorem B53230715 : Blo 682313 53230715 := bstep (se 1 (by rfl) ⟨39923036, by rfl⟩ : syracuseStep 53230715 = 79846073) B79846073
theorem B1850921 : Blo 682313 1850921 := bstep (se 2 (by rfl) ⟨694095, by rfl⟩ : syracuseStep 1850921 = 1388191) B1388191
theorem B2310119 : Blo 682313 2310119 := bstep (se 1 (by rfl) ⟨1732589, by rfl⟩ : syracuseStep 2310119 = 3465179) B3465179
theorem B771583 : Blo 682313 771583 := bstep (se 1 (by rfl) ⟨578687, by rfl⟩ : syracuseStep 771583 = 1157375) B1157375
theorem B8767547 : Blo 682313 8767547 := bstep (se 1 (by rfl) ⟨6575660, by rfl⟩ : syracuseStep 8767547 = 13151321) B13151321
theorem B2187263 : Blo 682313 2187263 := bstep (se 1 (by rfl) ⟨1640447, by rfl⟩ : syracuseStep 2187263 = 3280895) B3280895
theorem B5202143 : Blo 682313 5202143 := bstep (se 1 (by rfl) ⟨3901607, by rfl⟩ : syracuseStep 5202143 = 7803215) B7803215
theorem B1729471 : Blo 682313 1729471 := bstep (se 1 (by rfl) ⟨1297103, by rfl⟩ : syracuseStep 1729471 = 2594207) B2594207
theorem B2191529 : Blo 682313 2191529 := bstep (se 2 (by rfl) ⟨821823, by rfl⟩ : syracuseStep 2191529 = 1643647) B1643647
theorem B16906877 : Blo 682313 16906877 := bstep (se 3 (by rfl) ⟨3170039, by rfl⟩ : syracuseStep 16906877 = 6340079) B6340079
theorem B3280603 : Blo 682313 3280603 := bstep (se 1 (by rfl) ⟨2460452, by rfl⟩ : syracuseStep 3280603 = 4920905) B4920905
theorem B2303207 : Blo 682313 2303207 := bstep (se 1 (by rfl) ⟨1727405, by rfl⟩ : syracuseStep 2303207 = 3454811) B3454811
theorem B30452507 : Blo 682313 30452507 := bstep (se 1 (by rfl) ⟨22839380, by rfl⟩ : syracuseStep 30452507 = 45678761) B45678761
theorem B2305961 : Blo 682313 2305961 := bstep (se 2 (by rfl) ⟨864735, by rfl⟩ : syracuseStep 2305961 = 1729471) B1729471
theorem B5845031 : Blo 682313 5845031 := bstep (se 1 (by rfl) ⟨4383773, by rfl⟩ : syracuseStep 5845031 = 8767547) B8767547
theorem B1028699 : Blo 682313 1028699 := bstep (se 1 (by rfl) ⟨771524, by rfl⟩ : syracuseStep 1028699 = 1543049) B1543049
theorem B1028777 : Blo 682313 1028777 := bstep (se 2 (by rfl) ⟨385791, by rfl⟩ : syracuseStep 1028777 = 771583) B771583
theorem B1458175 : Blo 682313 1458175 := bstep (se 1 (by rfl) ⟨1093631, by rfl⟩ : syracuseStep 1458175 = 2187263) B2187263
theorem B1461019 : Blo 682313 1461019 := bstep (se 1 (by rfl) ⟨1095764, by rfl⟩ : syracuseStep 1461019 = 2191529) B2191529
theorem B1233947 : Blo 682313 1233947 := bstep (se 1 (by rfl) ⟨925460, by rfl⟩ : syracuseStep 1233947 = 1850921) B1850921
theorem B3468095 : Blo 682313 3468095 := bstep (se 1 (by rfl) ⟨2601071, by rfl⟩ : syracuseStep 3468095 = 5202143) B5202143
theorem B683803 : Blo 682313 683803 := bstep (se 1 (by rfl) ⟨512852, by rfl⟩ : syracuseStep 683803 = 1025705) B1025705
theorem B1538207 : Blo 682313 1538207 := bstep (se 1 (by rfl) ⟨1153655, by rfl⟩ : syracuseStep 1538207 = 2307311) B2307311
theorem B11271251 : Blo 682313 11271251 := bstep (se 1 (by rfl) ⟨8453438, by rfl⟩ : syracuseStep 11271251 = 16906877) B16906877
theorem B35487143 : Blo 682313 35487143 := bstep (se 1 (by rfl) ⟨26615357, by rfl⟩ : syracuseStep 35487143 = 53230715) B53230715
theorem B1540079 : Blo 682313 1540079 := bstep (se 1 (by rfl) ⟨1155059, by rfl⟩ : syracuseStep 1540079 = 2310119) B2310119
theorem B822631 : Blo 682313 822631 := bstep (se 1 (by rfl) ⟨616973, by rfl⟩ : syracuseStep 822631 = 1233947) B1233947
theorem B1025471 : Blo 682313 1025471 := bstep (se 1 (by rfl) ⟨769103, by rfl⟩ : syracuseStep 1025471 = 1538207) B1538207
theorem B7514167 : Blo 682313 7514167 := bstep (se 1 (by rfl) ⟨5635625, by rfl⟩ : syracuseStep 7514167 = 11271251) B11271251
theorem B1026719 : Blo 682313 1026719 := bstep (se 1 (by rfl) ⟨770039, by rfl⟩ : syracuseStep 1026719 = 1540079) B1540079
theorem B1944233 : Blo 682313 1944233 := bstep (se 2 (by rfl) ⟨729087, by rfl⟩ : syracuseStep 1944233 = 1458175) B1458175
theorem B1948025 : Blo 682313 1948025 := bstep (se 2 (by rfl) ⟨730509, by rfl⟩ : syracuseStep 1948025 = 1461019) B1461019
theorem B4374137 : Blo 682313 4374137 := bstep (se 2 (by rfl) ⟨1640301, by rfl⟩ : syracuseStep 4374137 = 3280603) B3280603
theorem B20301671 : Blo 682313 20301671 := bstep (se 1 (by rfl) ⟨15226253, by rfl⟩ : syracuseStep 20301671 = 30452507) B30452507
theorem B2312063 : Blo 682313 2312063 := bstep (se 1 (by rfl) ⟨1734047, by rfl⟩ : syracuseStep 2312063 = 3468095) B3468095
theorem B1535471 : Blo 682313 1535471 := bstep (se 1 (by rfl) ⟨1151603, by rfl⟩ : syracuseStep 1535471 = 2303207) B2303207
theorem B1537307 : Blo 682313 1537307 := bstep (se 1 (by rfl) ⟨1152980, by rfl⟩ : syracuseStep 1537307 = 2305961) B2305961
theorem B3896687 : Blo 682313 3896687 := bstep (se 1 (by rfl) ⟨2922515, by rfl⟩ : syracuseStep 3896687 = 5845031) B5845031
theorem B685799 : Blo 682313 685799 := bstep (se 1 (by rfl) ⟨514349, by rfl⟩ : syracuseStep 685799 = 1028699) B1028699
theorem B685851 : Blo 682313 685851 := bstep (se 1 (by rfl) ⟨514388, by rfl⟩ : syracuseStep 685851 = 1028777) B1028777
theorem B23658095 : Blo 682313 23658095 := bstep (se 1 (by rfl) ⟨17743571, by rfl⟩ : syracuseStep 23658095 = 35487143) B35487143
theorem B13534447 : Blo 682313 13534447 := bstep (se 1 (by rfl) ⟨10150835, by rfl⟩ : syracuseStep 13534447 = 20301671) B20301671
theorem B1541375 : Blo 682313 1541375 := bstep (se 1 (by rfl) ⟨1156031, by rfl⟩ : syracuseStep 1541375 = 2312063) B2312063
theorem B1023647 : Blo 682313 1023647 := bstep (se 1 (by rfl) ⟨767735, by rfl⟩ : syracuseStep 1023647 = 1535471) B1535471
theorem B1024871 : Blo 682313 1024871 := bstep (se 1 (by rfl) ⟨768653, by rfl⟩ : syracuseStep 1024871 = 1537307) B1537307
theorem B2597791 : Blo 682313 2597791 := bstep (se 1 (by rfl) ⟨1948343, by rfl⟩ : syracuseStep 2597791 = 3896687) B3896687
theorem B63088253 : Blo 682313 63088253 := bstep (se 3 (by rfl) ⟨11829047, by rfl⟩ : syracuseStep 63088253 = 23658095) B23658095
theorem B1096841 : Blo 682313 1096841 := bstep (se 2 (by rfl) ⟨411315, by rfl⟩ : syracuseStep 1096841 = 822631) B822631
theorem B1296155 : Blo 682313 1296155 := bstep (se 1 (by rfl) ⟨972116, by rfl⟩ : syracuseStep 1296155 = 1944233) B1944233
theorem B1298683 : Blo 682313 1298683 := bstep (se 1 (by rfl) ⟨974012, by rfl⟩ : syracuseStep 1298683 = 1948025) B1948025
theorem B10018889 : Blo 682313 10018889 := bstep (se 2 (by rfl) ⟨3757083, by rfl⟩ : syracuseStep 10018889 = 7514167) B7514167
theorem B683647 : Blo 682313 683647 := bstep (se 1 (by rfl) ⟨512735, by rfl⟩ : syracuseStep 683647 = 1025471) B1025471
theorem B684479 : Blo 682313 684479 := bstep (se 1 (by rfl) ⟨513359, by rfl⟩ : syracuseStep 684479 = 1026719) B1026719
theorem B2916091 : Blo 682313 2916091 := bstep (se 1 (by rfl) ⟨2187068, by rfl⟩ : syracuseStep 2916091 = 4374137) B4374137
theorem B2924909 : Blo 682313 2924909 := bstep (se 3 (by rfl) ⟨548420, by rfl⟩ : syracuseStep 2924909 = 1096841) B1096841
theorem B1027583 : Blo 682313 1027583 := bstep (se 1 (by rfl) ⟨770687, by rfl⟩ : syracuseStep 1027583 = 1541375) B1541375
theorem B864103 : Blo 682313 864103 := bstep (se 1 (by rfl) ⟨648077, by rfl⟩ : syracuseStep 864103 = 1296155) B1296155
theorem B42058835 : Blo 682313 42058835 := bstep (se 1 (by rfl) ⟨31544126, by rfl⟩ : syracuseStep 42058835 = 63088253) B63088253
theorem B3888121 : Blo 682313 3888121 := bstep (se 2 (by rfl) ⟨1458045, by rfl⟩ : syracuseStep 3888121 = 2916091) B2916091
theorem B3463721 : Blo 682313 3463721 := bstep (se 2 (by rfl) ⟨1298895, by rfl⟩ : syracuseStep 3463721 = 2597791) B2597791
theorem B18045929 : Blo 682313 18045929 := bstep (se 2 (by rfl) ⟨6767223, by rfl⟩ : syracuseStep 18045929 = 13534447) B13534447
theorem B682431 : Blo 682313 682431 := bstep (se 1 (by rfl) ⟨511823, by rfl⟩ : syracuseStep 682431 = 1023647) B1023647
theorem B6679259 : Blo 682313 6679259 := bstep (se 1 (by rfl) ⟨5009444, by rfl⟩ : syracuseStep 6679259 = 10018889) B10018889
theorem B1731577 : Blo 682313 1731577 := bstep (se 2 (by rfl) ⟨649341, by rfl⟩ : syracuseStep 1731577 = 1298683) B1298683
theorem B683247 : Blo 682313 683247 := bstep (se 1 (by rfl) ⟨512435, by rfl⟩ : syracuseStep 683247 = 1024871) B1024871
theorem B12030619 : Blo 682313 12030619 := bstep (se 1 (by rfl) ⟨9022964, by rfl⟩ : syracuseStep 12030619 = 18045929) B18045929
theorem B1152137 : Blo 682313 1152137 := bstep (se 2 (by rfl) ⟨432051, by rfl⟩ : syracuseStep 1152137 = 864103) B864103
theorem B5184161 : Blo 682313 5184161 := bstep (se 2 (by rfl) ⟨1944060, by rfl⟩ : syracuseStep 5184161 = 3888121) B3888121
theorem B2308769 : Blo 682313 2308769 := bstep (se 2 (by rfl) ⟨865788, by rfl⟩ : syracuseStep 2308769 = 1731577) B1731577
theorem B2309147 : Blo 682313 2309147 := bstep (se 1 (by rfl) ⟨1731860, by rfl⟩ : syracuseStep 2309147 = 3463721) B3463721
theorem B1949939 : Blo 682313 1949939 := bstep (se 1 (by rfl) ⟨1462454, by rfl⟩ : syracuseStep 1949939 = 2924909) B2924909
theorem B28039223 : Blo 682313 28039223 := bstep (se 1 (by rfl) ⟨21029417, by rfl⟩ : syracuseStep 28039223 = 42058835) B42058835
theorem B4452839 : Blo 682313 4452839 := bstep (se 1 (by rfl) ⟨3339629, by rfl⟩ : syracuseStep 4452839 = 6679259) B6679259
theorem B685055 : Blo 682313 685055 := bstep (se 1 (by rfl) ⟨513791, by rfl⟩ : syracuseStep 685055 = 1027583) B1027583
theorem B768091 : Blo 682313 768091 := bstep (se 1 (by rfl) ⟨576068, by rfl⟩ : syracuseStep 768091 = 1152137) B1152137
theorem B3456107 : Blo 682313 3456107 := bstep (se 1 (by rfl) ⟨2592080, by rfl⟩ : syracuseStep 3456107 = 5184161) B5184161
theorem B16040825 : Blo 682313 16040825 := bstep (se 2 (by rfl) ⟨6015309, by rfl⟩ : syracuseStep 16040825 = 12030619) B12030619
theorem B2968559 : Blo 682313 2968559 := bstep (se 1 (by rfl) ⟨2226419, by rfl⟩ : syracuseStep 2968559 = 4452839) B4452839
theorem B1299959 : Blo 682313 1299959 := bstep (se 1 (by rfl) ⟨974969, by rfl⟩ : syracuseStep 1299959 = 1949939) B1949939
theorem B74771261 : Blo 682313 74771261 := bstep (se 3 (by rfl) ⟨14019611, by rfl⟩ : syracuseStep 74771261 = 28039223) B28039223
theorem B1539179 : Blo 682313 1539179 := bstep (se 1 (by rfl) ⟨1154384, by rfl⟩ : syracuseStep 1539179 = 2308769) B2308769
theorem B1539431 : Blo 682313 1539431 := bstep (se 1 (by rfl) ⟨1154573, by rfl⟩ : syracuseStep 1539431 = 2309147) B2309147
theorem B49847507 : Blo 682313 49847507 := bstep (se 1 (by rfl) ⟨37385630, by rfl⟩ : syracuseStep 49847507 = 74771261) B74771261
theorem B1024121 : Blo 682313 1024121 := bstep (se 2 (by rfl) ⟨384045, by rfl⟩ : syracuseStep 1024121 = 768091) B768091
theorem B2304071 : Blo 682313 2304071 := bstep (se 1 (by rfl) ⟨1728053, by rfl⟩ : syracuseStep 2304071 = 3456107) B3456107
theorem B1026119 : Blo 682313 1026119 := bstep (se 1 (by rfl) ⟨769589, by rfl⟩ : syracuseStep 1026119 = 1539179) B1539179
theorem B1026287 : Blo 682313 1026287 := bstep (se 1 (by rfl) ⟨769715, by rfl⟩ : syracuseStep 1026287 = 1539431) B1539431
theorem B10693883 : Blo 682313 10693883 := bstep (se 1 (by rfl) ⟨8020412, by rfl⟩ : syracuseStep 10693883 = 16040825) B16040825
theorem B1979039 : Blo 682313 1979039 := bstep (se 1 (by rfl) ⟨1484279, by rfl⟩ : syracuseStep 1979039 = 2968559) B2968559
theorem B866639 : Blo 682313 866639 := bstep (se 1 (by rfl) ⟨649979, by rfl⟩ : syracuseStep 866639 = 1299959) B1299959
theorem B5277437 : Blo 682313 5277437 := bstep (se 3 (by rfl) ⟨989519, by rfl⟩ : syracuseStep 5277437 = 1979039) B1979039
theorem B33231671 : Blo 682313 33231671 := bstep (se 1 (by rfl) ⟨24923753, by rfl⟩ : syracuseStep 33231671 = 49847507) B49847507
theorem B2311037 : Blo 682313 2311037 := bstep (se 3 (by rfl) ⟨433319, by rfl⟩ : syracuseStep 2311037 = 866639) B866639
theorem B7129255 : Blo 682313 7129255 := bstep (se 1 (by rfl) ⟨5346941, by rfl⟩ : syracuseStep 7129255 = 10693883) B10693883
theorem B682747 : Blo 682313 682747 := bstep (se 1 (by rfl) ⟨512060, by rfl⟩ : syracuseStep 682747 = 1024121) B1024121
theorem B1536047 : Blo 682313 1536047 := bstep (se 1 (by rfl) ⟨1152035, by rfl⟩ : syracuseStep 1536047 = 2304071) B2304071
theorem B684079 : Blo 682313 684079 := bstep (se 1 (by rfl) ⟨513059, by rfl⟩ : syracuseStep 684079 = 1026119) B1026119
theorem B684191 : Blo 682313 684191 := bstep (se 1 (by rfl) ⟨513143, by rfl⟩ : syracuseStep 684191 = 1026287) B1026287
theorem B1540691 : Blo 682313 1540691 := bstep (se 1 (by rfl) ⟨1155518, by rfl⟩ : syracuseStep 1540691 = 2311037) B2311037
theorem B9505673 : Blo 682313 9505673 := bstep (se 2 (by rfl) ⟨3564627, by rfl⟩ : syracuseStep 9505673 = 7129255) B7129255
theorem B22154447 : Blo 682313 22154447 := bstep (se 1 (by rfl) ⟨16615835, by rfl⟩ : syracuseStep 22154447 = 33231671) B33231671
theorem B1024031 : Blo 682313 1024031 := bstep (se 1 (by rfl) ⟨768023, by rfl⟩ : syracuseStep 1024031 = 1536047) B1536047
theorem B3518291 : Blo 682313 3518291 := bstep (se 1 (by rfl) ⟨2638718, by rfl⟩ : syracuseStep 3518291 = 5277437) B5277437
theorem B1027127 : Blo 682313 1027127 := bstep (se 1 (by rfl) ⟨770345, by rfl⟩ : syracuseStep 1027127 = 1540691) B1540691
theorem B6337115 : Blo 682313 6337115 := bstep (se 1 (by rfl) ⟨4752836, by rfl⟩ : syracuseStep 6337115 = 9505673) B9505673
theorem B2345527 : Blo 682313 2345527 := bstep (se 1 (by rfl) ⟨1759145, by rfl⟩ : syracuseStep 2345527 = 3518291) B3518291
theorem B14769631 : Blo 682313 14769631 := bstep (se 1 (by rfl) ⟨11077223, by rfl⟩ : syracuseStep 14769631 = 22154447) B22154447
theorem B682687 : Blo 682313 682687 := bstep (se 1 (by rfl) ⟨512015, by rfl⟩ : syracuseStep 682687 = 1024031) B1024031
theorem B3127369 : Blo 682313 3127369 := bstep (se 2 (by rfl) ⟨1172763, by rfl⟩ : syracuseStep 3127369 = 2345527) B2345527
theorem B684751 : Blo 682313 684751 := bstep (se 1 (by rfl) ⟨513563, by rfl⟩ : syracuseStep 684751 = 1027127) B1027127
theorem B4224743 : Blo 682313 4224743 := bstep (se 1 (by rfl) ⟨3168557, by rfl⟩ : syracuseStep 4224743 = 6337115) B6337115
theorem B19692841 : Blo 682313 19692841 := bstep (se 2 (by rfl) ⟨7384815, by rfl⟩ : syracuseStep 19692841 = 14769631) B14769631
theorem B4169825 : Blo 682313 4169825 := bstep (se 2 (by rfl) ⟨1563684, by rfl⟩ : syracuseStep 4169825 = 3127369) B3127369
theorem B26257121 : Blo 682313 26257121 := bstep (se 2 (by rfl) ⟨9846420, by rfl⟩ : syracuseStep 26257121 = 19692841) B19692841
theorem B2816495 : Blo 682313 2816495 := bstep (se 1 (by rfl) ⟨2112371, by rfl⟩ : syracuseStep 2816495 = 4224743) B4224743
theorem B17504747 : Blo 682313 17504747 := bstep (se 1 (by rfl) ⟨13128560, by rfl⟩ : syracuseStep 17504747 = 26257121) B26257121
theorem B1877663 : Blo 682313 1877663 := bstep (se 1 (by rfl) ⟨1408247, by rfl⟩ : syracuseStep 1877663 = 2816495) B2816495
theorem B2779883 : Blo 682313 2779883 := bstep (se 1 (by rfl) ⟨2084912, by rfl⟩ : syracuseStep 2779883 = 4169825) B4169825
theorem B11669831 : Blo 682313 11669831 := bstep (se 1 (by rfl) ⟨8752373, by rfl⟩ : syracuseStep 11669831 = 17504747) B17504747
theorem B1251775 : Blo 682313 1251775 := bstep (se 1 (by rfl) ⟨938831, by rfl⟩ : syracuseStep 1251775 = 1877663) B1877663
theorem B1853255 : Blo 682313 1853255 := bstep (se 1 (by rfl) ⟨1389941, by rfl⟩ : syracuseStep 1853255 = 2779883) B2779883
theorem B7779887 : Blo 682313 7779887 := bstep (se 1 (by rfl) ⟨5834915, by rfl⟩ : syracuseStep 7779887 = 11669831) B11669831
theorem B1235503 : Blo 682313 1235503 := bstep (se 1 (by rfl) ⟨926627, by rfl⟩ : syracuseStep 1235503 = 1853255) B1853255
theorem B1669033 : Blo 682313 1669033 := bstep (se 2 (by rfl) ⟨625887, by rfl⟩ : syracuseStep 1669033 = 1251775) B1251775
theorem B6589349 : Blo 682313 6589349 := bstep (se 4 (by rfl) ⟨617751, by rfl⟩ : syracuseStep 6589349 = 1235503) B1235503
theorem B5186591 : Blo 682313 5186591 := bstep (se 1 (by rfl) ⟨3889943, by rfl⟩ : syracuseStep 5186591 = 7779887) B7779887
theorem B2225377 : Blo 682313 2225377 := bstep (se 2 (by rfl) ⟨834516, by rfl⟩ : syracuseStep 2225377 = 1669033) B1669033
theorem B4392899 : Blo 682313 4392899 := bstep (se 1 (by rfl) ⟨3294674, by rfl⟩ : syracuseStep 4392899 = 6589349) B6589349
theorem B11868677 : Blo 682313 11868677 := bstep (se 4 (by rfl) ⟨1112688, by rfl⟩ : syracuseStep 11868677 = 2225377) B2225377
theorem B3457727 : Blo 682313 3457727 := bstep (se 1 (by rfl) ⟨2593295, by rfl⟩ : syracuseStep 3457727 = 5186591) B5186591
theorem B2305151 : Blo 682313 2305151 := bstep (se 1 (by rfl) ⟨1728863, by rfl⟩ : syracuseStep 2305151 = 3457727) B3457727
theorem B2928599 : Blo 682313 2928599 := bstep (se 1 (by rfl) ⟨2196449, by rfl⟩ : syracuseStep 2928599 = 4392899) B4392899
theorem B7912451 : Blo 682313 7912451 := bstep (se 1 (by rfl) ⟨5934338, by rfl⟩ : syracuseStep 7912451 = 11868677) B11868677
theorem B1952399 : Blo 682313 1952399 := bstep (se 1 (by rfl) ⟨1464299, by rfl⟩ : syracuseStep 1952399 = 2928599) B2928599
theorem B1536767 : Blo 682313 1536767 := bstep (se 1 (by rfl) ⟨1152575, by rfl⟩ : syracuseStep 1536767 = 2305151) B2305151
theorem B21099869 : Blo 682313 21099869 := bstep (se 3 (by rfl) ⟨3956225, by rfl⟩ : syracuseStep 21099869 = 7912451) B7912451
theorem B1024511 : Blo 682313 1024511 := bstep (se 1 (by rfl) ⟨768383, by rfl⟩ : syracuseStep 1024511 = 1536767) B1536767
theorem B14066579 : Blo 682313 14066579 := bstep (se 1 (by rfl) ⟨10549934, by rfl⟩ : syracuseStep 14066579 = 21099869) B21099869
theorem B1301599 : Blo 682313 1301599 := bstep (se 1 (by rfl) ⟨976199, by rfl⟩ : syracuseStep 1301599 = 1952399) B1952399
theorem B37510877 : Blo 682313 37510877 := bstep (se 3 (by rfl) ⟨7033289, by rfl⟩ : syracuseStep 37510877 = 14066579) B14066579
theorem B683007 : Blo 682313 683007 := bstep (se 1 (by rfl) ⟨512255, by rfl⟩ : syracuseStep 683007 = 1024511) B1024511
theorem B1735465 : Blo 682313 1735465 := bstep (se 2 (by rfl) ⟨650799, by rfl⟩ : syracuseStep 1735465 = 1301599) B1301599
theorem B2313953 : Blo 682313 2313953 := bstep (se 2 (by rfl) ⟨867732, by rfl⟩ : syracuseStep 2313953 = 1735465) B1735465
theorem B100029005 : Blo 682313 100029005 := bstep (se 3 (by rfl) ⟨18755438, by rfl⟩ : syracuseStep 100029005 = 37510877) B37510877
theorem B1542635 : Blo 682313 1542635 := bstep (se 1 (by rfl) ⟨1156976, by rfl⟩ : syracuseStep 1542635 = 2313953) B2313953
theorem B66686003 : Blo 682313 66686003 := bstep (se 1 (by rfl) ⟨50014502, by rfl⟩ : syracuseStep 66686003 = 100029005) B100029005
theorem B1028423 : Blo 682313 1028423 := bstep (se 1 (by rfl) ⟨771317, by rfl⟩ : syracuseStep 1028423 = 1542635) B1542635
theorem B44457335 : Blo 682313 44457335 := bstep (se 1 (by rfl) ⟨33343001, by rfl⟩ : syracuseStep 44457335 = 66686003) B66686003
theorem B29638223 : Blo 682313 29638223 := bstep (se 1 (by rfl) ⟨22228667, by rfl⟩ : syracuseStep 29638223 = 44457335) B44457335
theorem B685615 : Blo 682313 685615 := bstep (se 1 (by rfl) ⟨514211, by rfl⟩ : syracuseStep 685615 = 1028423) B1028423
theorem B19758815 : Blo 682313 19758815 := bstep (se 1 (by rfl) ⟨14819111, by rfl⟩ : syracuseStep 19758815 = 29638223) B29638223
theorem B13172543 : Blo 682313 13172543 := bstep (se 1 (by rfl) ⟨9879407, by rfl⟩ : syracuseStep 13172543 = 19758815) B19758815
theorem B8781695 : Blo 682313 8781695 := bstep (se 1 (by rfl) ⟨6586271, by rfl⟩ : syracuseStep 8781695 = 13172543) B13172543
theorem B5854463 : Blo 682313 5854463 := bstep (se 1 (by rfl) ⟨4390847, by rfl⟩ : syracuseStep 5854463 = 8781695) B8781695
theorem B3902975 : Blo 682313 3902975 := bstep (se 1 (by rfl) ⟨2927231, by rfl⟩ : syracuseStep 3902975 = 5854463) B5854463
theorem B2601983 : Blo 682313 2601983 := bstep (se 1 (by rfl) ⟨1951487, by rfl⟩ : syracuseStep 2601983 = 3902975) B3902975
theorem B1734655 : Blo 682313 1734655 := bstep (se 1 (by rfl) ⟨1300991, by rfl⟩ : syracuseStep 1734655 = 2601983) B2601983
theorem B2312873 : Blo 682313 2312873 := bstep (se 2 (by rfl) ⟨867327, by rfl⟩ : syracuseStep 2312873 = 1734655) B1734655
theorem B1541915 : Blo 682313 1541915 := bstep (se 1 (by rfl) ⟨1156436, by rfl⟩ : syracuseStep 1541915 = 2312873) B2312873
theorem B1027943 : Blo 682313 1027943 := bstep (se 1 (by rfl) ⟨770957, by rfl⟩ : syracuseStep 1027943 = 1541915) B1541915
theorem B685295 : Blo 682313 685295 := bstep (se 1 (by rfl) ⟨513971, by rfl⟩ : syracuseStep 685295 = 1027943) B1027943

theorem C0 (j : ℕ) (h1 : 170578 ≤ j) (h2 : j ≤ 171277) : Blo 682313 (4 * j + 3) := by
  interval_cases j
  · exact B682315
  · exact B682319
  · exact B682323
  · exact B682327
  · exact B682331
  · exact B682335
  · exact B682339
  · exact B682343
  · exact B682347
  · exact B682351
  · exact B682355
  · exact B682359
  · exact B682363
  · exact B682367
  · exact B682371
  · exact B682375
  · exact B682379
  · exact B682383
  · exact B682387
  · exact B682391
  · exact B682395
  · exact B682399
  · exact B682403
  · exact B682407
  · exact B682411
  · exact B682415
  · exact B682419
  · exact B682423
  · exact B682427
  · exact B682431
  · exact B682435
  · exact B682439
  · exact B682443
  · exact B682447
  · exact B682451
  · exact B682455
  · exact B682459
  · exact B682463
  · exact B682467
  · exact B682471
  · exact B682475
  · exact B682479
  · exact B682483
  · exact B682487
  · exact B682491
  · exact B682495
  · exact B682499
  · exact B682503
  · exact B682507
  · exact B682511
  · exact B682515
  · exact B682519
  · exact B682523
  · exact B682527
  · exact B682531
  · exact B682535
  · exact B682539
  · exact B682543
  · exact B682547
  · exact B682551
  · exact B682555
  · exact B682559
  · exact B682563
  · exact B682567
  · exact B682571
  · exact B682575
  · exact B682579
  · exact B682583
  · exact B682587
  · exact B682591
  · exact B682595
  · exact B682599
  · exact B682603
  · exact B682607
  · exact B682611
  · exact B682615
  · exact B682619
  · exact B682623
  · exact B682627
  · exact B682631
  · exact B682635
  · exact B682639
  · exact B682643
  · exact B682647
  · exact B682651
  · exact B682655
  · exact B682659
  · exact B682663
  · exact B682667
  · exact B682671
  · exact B682675
  · exact B682679
  · exact B682683
  · exact B682687
  · exact B682691
  · exact B682695
  · exact B682699
  · exact B682703
  · exact B682707
  · exact B682711
  · exact B682715
  · exact B682719
  · exact B682723
  · exact B682727
  · exact B682731
  · exact B682735
  · exact B682739
  · exact B682743
  · exact B682747
  · exact B682751
  · exact B682755
  · exact B682759
  · exact B682763
  · exact B682767
  · exact B682771
  · exact B682775
  · exact B682779
  · exact B682783
  · exact B682787
  · exact B682791
  · exact B682795
  · exact B682799
  · exact B682803
  · exact B682807
  · exact B682811
  · exact B682815
  · exact B682819
  · exact B682823
  · exact B682827
  · exact B682831
  · exact B682835
  · exact B682839
  · exact B682843
  · exact B682847
  · exact B682851
  · exact B682855
  · exact B682859
  · exact B682863
  · exact B682867
  · exact B682871
  · exact B682875
  · exact B682879
  · exact B682883
  · exact B682887
  · exact B682891
  · exact B682895
  · exact B682899
  · exact B682903
  · exact B682907
  · exact B682911
  · exact B682915
  · exact B682919
  · exact B682923
  · exact B682927
  · exact B682931
  · exact B682935
  · exact B682939
  · exact B682943
  · exact B682947
  · exact B682951
  · exact B682955
  · exact B682959
  · exact B682963
  · exact B682967
  · exact B682971
  · exact B682975
  · exact B682979
  · exact B682983
  · exact B682987
  · exact B682991
  · exact B682995
  · exact B682999
  · exact B683003
  · exact B683007
  · exact B683011
  · exact B683015
  · exact B683019
  · exact B683023
  · exact B683027
  · exact B683031
  · exact B683035
  · exact B683039
  · exact B683043
  · exact B683047
  · exact B683051
  · exact B683055
  · exact B683059
  · exact B683063
  · exact B683067
  · exact B683071
  · exact B683075
  · exact B683079
  · exact B683083
  · exact B683087
  · exact B683091
  · exact B683095
  · exact B683099
  · exact B683103
  · exact B683107
  · exact B683111
  · exact B683115
  · exact B683119
  · exact B683123
  · exact B683127
  · exact B683131
  · exact B683135
  · exact B683139
  · exact B683143
  · exact B683147
  · exact B683151
  · exact B683155
  · exact B683159
  · exact B683163
  · exact B683167
  · exact B683171
  · exact B683175
  · exact B683179
  · exact B683183
  · exact B683187
  · exact B683191
  · exact B683195
  · exact B683199
  · exact B683203
  · exact B683207
  · exact B683211
  · exact B683215
  · exact B683219
  · exact B683223
  · exact B683227
  · exact B683231
  · exact B683235
  · exact B683239
  · exact B683243
  · exact B683247
  · exact B683251
  · exact B683255
  · exact B683259
  · exact B683263
  · exact B683267
  · exact B683271
  · exact B683275
  · exact B683279
  · exact B683283
  · exact B683287
  · exact B683291
  · exact B683295
  · exact B683299
  · exact B683303
  · exact B683307
  · exact B683311
  · exact B683315
  · exact B683319
  · exact B683323
  · exact B683327
  · exact B683331
  · exact B683335
  · exact B683339
  · exact B683343
  · exact B683347
  · exact B683351
  · exact B683355
  · exact B683359
  · exact B683363
  · exact B683367
  · exact B683371
  · exact B683375
  · exact B683379
  · exact B683383
  · exact B683387
  · exact B683391
  · exact B683395
  · exact B683399
  · exact B683403
  · exact B683407
  · exact B683411
  · exact B683415
  · exact B683419
  · exact B683423
  · exact B683427
  · exact B683431
  · exact B683435
  · exact B683439
  · exact B683443
  · exact B683447
  · exact B683451
  · exact B683455
  · exact B683459
  · exact B683463
  · exact B683467
  · exact B683471
  · exact B683475
  · exact B683479
  · exact B683483
  · exact B683487
  · exact B683491
  · exact B683495
  · exact B683499
  · exact B683503
  · exact B683507
  · exact B683511
  · exact B683515
  · exact B683519
  · exact B683523
  · exact B683527
  · exact B683531
  · exact B683535
  · exact B683539
  · exact B683543
  · exact B683547
  · exact B683551
  · exact B683555
  · exact B683559
  · exact B683563
  · exact B683567
  · exact B683571
  · exact B683575
  · exact B683579
  · exact B683583
  · exact B683587
  · exact B683591
  · exact B683595
  · exact B683599
  · exact B683603
  · exact B683607
  · exact B683611
  · exact B683615
  · exact B683619
  · exact B683623
  · exact B683627
  · exact B683631
  · exact B683635
  · exact B683639
  · exact B683643
  · exact B683647
  · exact B683651
  · exact B683655
  · exact B683659
  · exact B683663
  · exact B683667
  · exact B683671
  · exact B683675
  · exact B683679
  · exact B683683
  · exact B683687
  · exact B683691
  · exact B683695
  · exact B683699
  · exact B683703
  · exact B683707
  · exact B683711
  · exact B683715
  · exact B683719
  · exact B683723
  · exact B683727
  · exact B683731
  · exact B683735
  · exact B683739
  · exact B683743
  · exact B683747
  · exact B683751
  · exact B683755
  · exact B683759
  · exact B683763
  · exact B683767
  · exact B683771
  · exact B683775
  · exact B683779
  · exact B683783
  · exact B683787
  · exact B683791
  · exact B683795
  · exact B683799
  · exact B683803
  · exact B683807
  · exact B683811
  · exact B683815
  · exact B683819
  · exact B683823
  · exact B683827
  · exact B683831
  · exact B683835
  · exact B683839
  · exact B683843
  · exact B683847
  · exact B683851
  · exact B683855
  · exact B683859
  · exact B683863
  · exact B683867
  · exact B683871
  · exact B683875
  · exact B683879
  · exact B683883
  · exact B683887
  · exact B683891
  · exact B683895
  · exact B683899
  · exact B683903
  · exact B683907
  · exact B683911
  · exact B683915
  · exact B683919
  · exact B683923
  · exact B683927
  · exact B683931
  · exact B683935
  · exact B683939
  · exact B683943
  · exact B683947
  · exact B683951
  · exact B683955
  · exact B683959
  · exact B683963
  · exact B683967
  · exact B683971
  · exact B683975
  · exact B683979
  · exact B683983
  · exact B683987
  · exact B683991
  · exact B683995
  · exact B683999
  · exact B684003
  · exact B684007
  · exact B684011
  · exact B684015
  · exact B684019
  · exact B684023
  · exact B684027
  · exact B684031
  · exact B684035
  · exact B684039
  · exact B684043
  · exact B684047
  · exact B684051
  · exact B684055
  · exact B684059
  · exact B684063
  · exact B684067
  · exact B684071
  · exact B684075
  · exact B684079
  · exact B684083
  · exact B684087
  · exact B684091
  · exact B684095
  · exact B684099
  · exact B684103
  · exact B684107
  · exact B684111
  · exact B684115
  · exact B684119
  · exact B684123
  · exact B684127
  · exact B684131
  · exact B684135
  · exact B684139
  · exact B684143
  · exact B684147
  · exact B684151
  · exact B684155
  · exact B684159
  · exact B684163
  · exact B684167
  · exact B684171
  · exact B684175
  · exact B684179
  · exact B684183
  · exact B684187
  · exact B684191
  · exact B684195
  · exact B684199
  · exact B684203
  · exact B684207
  · exact B684211
  · exact B684215
  · exact B684219
  · exact B684223
  · exact B684227
  · exact B684231
  · exact B684235
  · exact B684239
  · exact B684243
  · exact B684247
  · exact B684251
  · exact B684255
  · exact B684259
  · exact B684263
  · exact B684267
  · exact B684271
  · exact B684275
  · exact B684279
  · exact B684283
  · exact B684287
  · exact B684291
  · exact B684295
  · exact B684299
  · exact B684303
  · exact B684307
  · exact B684311
  · exact B684315
  · exact B684319
  · exact B684323
  · exact B684327
  · exact B684331
  · exact B684335
  · exact B684339
  · exact B684343
  · exact B684347
  · exact B684351
  · exact B684355
  · exact B684359
  · exact B684363
  · exact B684367
  · exact B684371
  · exact B684375
  · exact B684379
  · exact B684383
  · exact B684387
  · exact B684391
  · exact B684395
  · exact B684399
  · exact B684403
  · exact B684407
  · exact B684411
  · exact B684415
  · exact B684419
  · exact B684423
  · exact B684427
  · exact B684431
  · exact B684435
  · exact B684439
  · exact B684443
  · exact B684447
  · exact B684451
  · exact B684455
  · exact B684459
  · exact B684463
  · exact B684467
  · exact B684471
  · exact B684475
  · exact B684479
  · exact B684483
  · exact B684487
  · exact B684491
  · exact B684495
  · exact B684499
  · exact B684503
  · exact B684507
  · exact B684511
  · exact B684515
  · exact B684519
  · exact B684523
  · exact B684527
  · exact B684531
  · exact B684535
  · exact B684539
  · exact B684543
  · exact B684547
  · exact B684551
  · exact B684555
  · exact B684559
  · exact B684563
  · exact B684567
  · exact B684571
  · exact B684575
  · exact B684579
  · exact B684583
  · exact B684587
  · exact B684591
  · exact B684595
  · exact B684599
  · exact B684603
  · exact B684607
  · exact B684611
  · exact B684615
  · exact B684619
  · exact B684623
  · exact B684627
  · exact B684631
  · exact B684635
  · exact B684639
  · exact B684643
  · exact B684647
  · exact B684651
  · exact B684655
  · exact B684659
  · exact B684663
  · exact B684667
  · exact B684671
  · exact B684675
  · exact B684679
  · exact B684683
  · exact B684687
  · exact B684691
  · exact B684695
  · exact B684699
  · exact B684703
  · exact B684707
  · exact B684711
  · exact B684715
  · exact B684719
  · exact B684723
  · exact B684727
  · exact B684731
  · exact B684735
  · exact B684739
  · exact B684743
  · exact B684747
  · exact B684751
  · exact B684755
  · exact B684759
  · exact B684763
  · exact B684767
  · exact B684771
  · exact B684775
  · exact B684779
  · exact B684783
  · exact B684787
  · exact B684791
  · exact B684795
  · exact B684799
  · exact B684803
  · exact B684807
  · exact B684811
  · exact B684815
  · exact B684819
  · exact B684823
  · exact B684827
  · exact B684831
  · exact B684835
  · exact B684839
  · exact B684843
  · exact B684847
  · exact B684851
  · exact B684855
  · exact B684859
  · exact B684863
  · exact B684867
  · exact B684871
  · exact B684875
  · exact B684879
  · exact B684883
  · exact B684887
  · exact B684891
  · exact B684895
  · exact B684899
  · exact B684903
  · exact B684907
  · exact B684911
  · exact B684915
  · exact B684919
  · exact B684923
  · exact B684927
  · exact B684931
  · exact B684935
  · exact B684939
  · exact B684943
  · exact B684947
  · exact B684951
  · exact B684955
  · exact B684959
  · exact B684963
  · exact B684967
  · exact B684971
  · exact B684975
  · exact B684979
  · exact B684983
  · exact B684987
  · exact B684991
  · exact B684995
  · exact B684999
  · exact B685003
  · exact B685007
  · exact B685011
  · exact B685015
  · exact B685019
  · exact B685023
  · exact B685027
  · exact B685031
  · exact B685035
  · exact B685039
  · exact B685043
  · exact B685047
  · exact B685051
  · exact B685055
  · exact B685059
  · exact B685063
  · exact B685067
  · exact B685071
  · exact B685075
  · exact B685079
  · exact B685083
  · exact B685087
  · exact B685091
  · exact B685095
  · exact B685099
  · exact B685103
  · exact B685107
  · exact B685111

theorem C1 (j : ℕ) (h1 : 171278 ≤ j) (h2 : j ≤ 171577) : Blo 682313 (4 * j + 3) := by
  interval_cases j
  · exact B685115
  · exact B685119
  · exact B685123
  · exact B685127
  · exact B685131
  · exact B685135
  · exact B685139
  · exact B685143
  · exact B685147
  · exact B685151
  · exact B685155
  · exact B685159
  · exact B685163
  · exact B685167
  · exact B685171
  · exact B685175
  · exact B685179
  · exact B685183
  · exact B685187
  · exact B685191
  · exact B685195
  · exact B685199
  · exact B685203
  · exact B685207
  · exact B685211
  · exact B685215
  · exact B685219
  · exact B685223
  · exact B685227
  · exact B685231
  · exact B685235
  · exact B685239
  · exact B685243
  · exact B685247
  · exact B685251
  · exact B685255
  · exact B685259
  · exact B685263
  · exact B685267
  · exact B685271
  · exact B685275
  · exact B685279
  · exact B685283
  · exact B685287
  · exact B685291
  · exact B685295
  · exact B685299
  · exact B685303
  · exact B685307
  · exact B685311
  · exact B685315
  · exact B685319
  · exact B685323
  · exact B685327
  · exact B685331
  · exact B685335
  · exact B685339
  · exact B685343
  · exact B685347
  · exact B685351
  · exact B685355
  · exact B685359
  · exact B685363
  · exact B685367
  · exact B685371
  · exact B685375
  · exact B685379
  · exact B685383
  · exact B685387
  · exact B685391
  · exact B685395
  · exact B685399
  · exact B685403
  · exact B685407
  · exact B685411
  · exact B685415
  · exact B685419
  · exact B685423
  · exact B685427
  · exact B685431
  · exact B685435
  · exact B685439
  · exact B685443
  · exact B685447
  · exact B685451
  · exact B685455
  · exact B685459
  · exact B685463
  · exact B685467
  · exact B685471
  · exact B685475
  · exact B685479
  · exact B685483
  · exact B685487
  · exact B685491
  · exact B685495
  · exact B685499
  · exact B685503
  · exact B685507
  · exact B685511
  · exact B685515
  · exact B685519
  · exact B685523
  · exact B685527
  · exact B685531
  · exact B685535
  · exact B685539
  · exact B685543
  · exact B685547
  · exact B685551
  · exact B685555
  · exact B685559
  · exact B685563
  · exact B685567
  · exact B685571
  · exact B685575
  · exact B685579
  · exact B685583
  · exact B685587
  · exact B685591
  · exact B685595
  · exact B685599
  · exact B685603
  · exact B685607
  · exact B685611
  · exact B685615
  · exact B685619
  · exact B685623
  · exact B685627
  · exact B685631
  · exact B685635
  · exact B685639
  · exact B685643
  · exact B685647
  · exact B685651
  · exact B685655
  · exact B685659
  · exact B685663
  · exact B685667
  · exact B685671
  · exact B685675
  · exact B685679
  · exact B685683
  · exact B685687
  · exact B685691
  · exact B685695
  · exact B685699
  · exact B685703
  · exact B685707
  · exact B685711
  · exact B685715
  · exact B685719
  · exact B685723
  · exact B685727
  · exact B685731
  · exact B685735
  · exact B685739
  · exact B685743
  · exact B685747
  · exact B685751
  · exact B685755
  · exact B685759
  · exact B685763
  · exact B685767
  · exact B685771
  · exact B685775
  · exact B685779
  · exact B685783
  · exact B685787
  · exact B685791
  · exact B685795
  · exact B685799
  · exact B685803
  · exact B685807
  · exact B685811
  · exact B685815
  · exact B685819
  · exact B685823
  · exact B685827
  · exact B685831
  · exact B685835
  · exact B685839
  · exact B685843
  · exact B685847
  · exact B685851
  · exact B685855
  · exact B685859
  · exact B685863
  · exact B685867
  · exact B685871
  · exact B685875
  · exact B685879
  · exact B685883
  · exact B685887
  · exact B685891
  · exact B685895
  · exact B685899
  · exact B685903
  · exact B685907
  · exact B685911
  · exact B685915
  · exact B685919
  · exact B685923
  · exact B685927
  · exact B685931
  · exact B685935
  · exact B685939
  · exact B685943
  · exact B685947
  · exact B685951
  · exact B685955
  · exact B685959
  · exact B685963
  · exact B685967
  · exact B685971
  · exact B685975
  · exact B685979
  · exact B685983
  · exact B685987
  · exact B685991
  · exact B685995
  · exact B685999
  · exact B686003
  · exact B686007
  · exact B686011
  · exact B686015
  · exact B686019
  · exact B686023
  · exact B686027
  · exact B686031
  · exact B686035
  · exact B686039
  · exact B686043
  · exact B686047
  · exact B686051
  · exact B686055
  · exact B686059
  · exact B686063
  · exact B686067
  · exact B686071
  · exact B686075
  · exact B686079
  · exact B686083
  · exact B686087
  · exact B686091
  · exact B686095
  · exact B686099
  · exact B686103
  · exact B686107
  · exact B686111
  · exact B686115
  · exact B686119
  · exact B686123
  · exact B686127
  · exact B686131
  · exact B686135
  · exact B686139
  · exact B686143
  · exact B686147
  · exact B686151
  · exact B686155
  · exact B686159
  · exact B686163
  · exact B686167
  · exact B686171
  · exact B686175
  · exact B686179
  · exact B686183
  · exact B686187
  · exact B686191
  · exact B686195
  · exact B686199
  · exact B686203
  · exact B686207
  · exact B686211
  · exact B686215
  · exact B686219
  · exact B686223
  · exact B686227
  · exact B686231
  · exact B686235
  · exact B686239
  · exact B686243
  · exact B686247
  · exact B686251
  · exact B686255
  · exact B686259
  · exact B686263
  · exact B686267
  · exact B686271
  · exact B686275
  · exact B686279
  · exact B686283
  · exact B686287
  · exact B686291
  · exact B686295
  · exact B686299
  · exact B686303
  · exact B686307
  · exact B686311

theorem solution (m : ℕ) (hlo : 682313 ≤ m) (hhi : m ≤ 686313) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 170578 ≤ j := by omega
    have hj2 : j ≤ 171577 := by omega
    have hb : Blo 682313 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 171278 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
