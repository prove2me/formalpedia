-- Prove2me | solution 1 for syracuse_descends_range_1725063_1727063
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:30:48.415825+00:00
-- url     : https://prove2.me/submissions/3fd87945-36c8-4b1a-b07d-dd05f841f7ae

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


theorem B3883013 : Blo 1725063 3883013 := bbase (se 4 (by rfl) ⟨364032, by rfl⟩ : syracuseStep 3883013 = 728065) (by norm_num)
theorem B2588693 : Blo 1725063 2588693 := bbase (se 6 (by rfl) ⟨60672, by rfl⟩ : syracuseStep 2588693 = 121345) (by norm_num)
theorem B14000149 : Blo 1725063 14000149 := bbase (se 6 (by rfl) ⟨328128, by rfl⟩ : syracuseStep 14000149 = 656257) (by norm_num)
theorem B1941529 : Blo 1725063 1941529 := bbase (se 2 (by rfl) ⟨728073, by rfl⟩ : syracuseStep 1941529 = 1456147) (by norm_num)
theorem B4915237 : Blo 1725063 4915237 := bbase (se 4 (by rfl) ⟨460803, by rfl⟩ : syracuseStep 4915237 = 921607) (by norm_num)
theorem B2588717 : Blo 1725063 2588717 := bbase (se 3 (by rfl) ⟨485384, by rfl⟩ : syracuseStep 2588717 = 970769) (by norm_num)
theorem B1867825 : Blo 1725063 1867825 := bbase (se 2 (by rfl) ⟨700434, by rfl⟩ : syracuseStep 1867825 = 1400869) (by norm_num)
theorem B1941565 : Blo 1725063 1941565 := bbase (se 3 (by rfl) ⟨364043, by rfl⟩ : syracuseStep 1941565 = 728087) (by norm_num)
theorem B2588741 : Blo 1725063 2588741 := bbase (se 4 (by rfl) ⟨242694, by rfl⟩ : syracuseStep 2588741 = 485389) (by norm_num)
theorem B3498061 : Blo 1725063 3498061 := bbase (se 3 (by rfl) ⟨655886, by rfl⟩ : syracuseStep 3498061 = 1311773) (by norm_num)
theorem B3883085 : Blo 1725063 3883085 := bbase (se 3 (by rfl) ⟨728078, by rfl⟩ : syracuseStep 3883085 = 1456157) (by norm_num)
theorem B2588765 : Blo 1725063 2588765 := bbase (se 3 (by rfl) ⟨485393, by rfl⟩ : syracuseStep 2588765 = 970787) (by norm_num)
theorem B1941601 : Blo 1725063 1941601 := bbase (se 2 (by rfl) ⟨728100, by rfl⟩ : syracuseStep 1941601 = 1456201) (by norm_num)
theorem B2588789 : Blo 1725063 2588789 := bbase (se 5 (by rfl) ⟨121349, by rfl⟩ : syracuseStep 2588789 = 242699) (by norm_num)
theorem B1941637 : Blo 1725063 1941637 := bbase (se 4 (by rfl) ⟨182028, by rfl⟩ : syracuseStep 1941637 = 364057) (by norm_num)
theorem B2588813 : Blo 1725063 2588813 := bbase (se 3 (by rfl) ⟨485402, by rfl⟩ : syracuseStep 2588813 = 970805) (by norm_num)
theorem B3154061 : Blo 1725063 3154061 := bbase (se 3 (by rfl) ⟨591386, by rfl⟩ : syracuseStep 3154061 = 1182773) (by norm_num)
theorem B3883157 : Blo 1725063 3883157 := bbase (se 6 (by rfl) ⟨91011, by rfl⟩ : syracuseStep 3883157 = 182023) (by norm_num)
theorem B2588837 : Blo 1725063 2588837 := bbase (se 4 (by rfl) ⟨242703, by rfl⟩ : syracuseStep 2588837 = 485407) (by norm_num)
theorem B1941673 : Blo 1725063 1941673 := bbase (se 2 (by rfl) ⟨728127, by rfl⟩ : syracuseStep 1941673 = 1456255) (by norm_num)
theorem B2588861 : Blo 1725063 2588861 := bbase (se 3 (by rfl) ⟨485411, by rfl⟩ : syracuseStep 2588861 = 970823) (by norm_num)
theorem B5824709 : Blo 1725063 5824709 := bbase (se 4 (by rfl) ⟨546066, by rfl⟩ : syracuseStep 5824709 = 1092133) (by norm_num)
theorem B4915397 : Blo 1725063 4915397 := bbase (se 4 (by rfl) ⟨460818, by rfl⟩ : syracuseStep 4915397 = 921637) (by norm_num)
theorem B1941709 : Blo 1725063 1941709 := bbase (se 3 (by rfl) ⟨364070, by rfl⟩ : syracuseStep 1941709 = 728141) (by norm_num)
theorem B2588885 : Blo 1725063 2588885 := bbase (se 7 (by rfl) ⟨30338, by rfl⟩ : syracuseStep 2588885 = 60677) (by norm_num)
theorem B3883229 : Blo 1725063 3883229 := bbase (se 3 (by rfl) ⟨728105, by rfl⟩ : syracuseStep 3883229 = 1456211) (by norm_num)
theorem B2588909 : Blo 1725063 2588909 := bbase (se 3 (by rfl) ⟨485420, by rfl⟩ : syracuseStep 2588909 = 970841) (by norm_num)
theorem B3277037 : Blo 1725063 3277037 := bbase (se 3 (by rfl) ⟨614444, by rfl⟩ : syracuseStep 3277037 = 1228889) (by norm_num)
theorem B1941745 : Blo 1725063 1941745 := bbase (se 2 (by rfl) ⟨728154, by rfl⟩ : syracuseStep 1941745 = 1456309) (by norm_num)
theorem B7373045 : Blo 1725063 7373045 := bbase (se 5 (by rfl) ⟨345611, by rfl⟩ : syracuseStep 7373045 = 691223) (by norm_num)
theorem B1843445 : Blo 1725063 1843445 := bbase (se 5 (by rfl) ⟨86411, by rfl⟩ : syracuseStep 1843445 = 172823) (by norm_num)
theorem B2588933 : Blo 1725063 2588933 := bbase (se 4 (by rfl) ⟨242712, by rfl⟩ : syracuseStep 2588933 = 485425) (by norm_num)
theorem B2457869 : Blo 1725063 2457869 := bbase (se 3 (by rfl) ⟨460850, by rfl⟩ : syracuseStep 2457869 = 921701) (by norm_num)
theorem B1941781 : Blo 1725063 1941781 := bbase (se 6 (by rfl) ⟨45510, by rfl⟩ : syracuseStep 1941781 = 91021) (by norm_num)
theorem B2588957 : Blo 1725063 2588957 := bbase (se 3 (by rfl) ⟨485429, by rfl⟩ : syracuseStep 2588957 = 970859) (by norm_num)
theorem B3883301 : Blo 1725063 3883301 := bbase (se 4 (by rfl) ⟨364059, by rfl⟩ : syracuseStep 3883301 = 728119) (by norm_num)
theorem B2588981 : Blo 1725063 2588981 := bbase (se 5 (by rfl) ⟨121358, by rfl⟩ : syracuseStep 2588981 = 242717) (by norm_num)
theorem B1941817 : Blo 1725063 1941817 := bbase (se 2 (by rfl) ⟨728181, by rfl⟩ : syracuseStep 1941817 = 1456363) (by norm_num)
theorem B4366669 : Blo 1725063 4366669 := bbase (se 3 (by rfl) ⟨818750, by rfl⟩ : syracuseStep 4366669 = 1637501) (by norm_num)
theorem B2589005 : Blo 1725063 2589005 := bbase (se 3 (by rfl) ⟨485438, by rfl⟩ : syracuseStep 2589005 = 970877) (by norm_num)
theorem B1941853 : Blo 1725063 1941853 := bbase (se 3 (by rfl) ⟨364097, by rfl⟩ : syracuseStep 1941853 = 728195) (by norm_num)
theorem B2589029 : Blo 1725063 2589029 := bbase (se 4 (by rfl) ⟨242721, by rfl⟩ : syracuseStep 2589029 = 485443) (by norm_num)
theorem B3883373 : Blo 1725063 3883373 := bbase (se 3 (by rfl) ⟨728132, by rfl⟩ : syracuseStep 3883373 = 1456265) (by norm_num)
theorem B2589053 : Blo 1725063 2589053 := bbase (se 3 (by rfl) ⟨485447, by rfl⟩ : syracuseStep 2589053 = 970895) (by norm_num)
theorem B1941889 : Blo 1725063 1941889 := bbase (se 2 (by rfl) ⟨728208, by rfl⟩ : syracuseStep 1941889 = 1456417) (by norm_num)
theorem B3277189 : Blo 1725063 3277189 := bbase (se 4 (by rfl) ⟨307236, by rfl⟩ : syracuseStep 3277189 = 614473) (by norm_num)
theorem B2589077 : Blo 1725063 2589077 := bbase (se 6 (by rfl) ⟨60681, by rfl⟩ : syracuseStep 2589077 = 121363) (by norm_num)
theorem B1941925 : Blo 1725063 1941925 := bbase (se 4 (by rfl) ⟨182055, by rfl⟩ : syracuseStep 1941925 = 364111) (by norm_num)
theorem B2073001 : Blo 1725063 2073001 := bbase (se 2 (by rfl) ⟨777375, by rfl⟩ : syracuseStep 2073001 = 1554751) (by norm_num)
theorem B2589101 : Blo 1725063 2589101 := bbase (se 3 (by rfl) ⟨485456, by rfl⟩ : syracuseStep 2589101 = 970913) (by norm_num)
theorem B3883445 : Blo 1725063 3883445 := bbase (se 5 (by rfl) ⟨182036, by rfl⟩ : syracuseStep 3883445 = 364073) (by norm_num)
theorem B4915637 : Blo 1725063 4915637 := bbase (se 5 (by rfl) ⟨230420, by rfl⟩ : syracuseStep 4915637 = 460841) (by norm_num)
theorem B4366781 : Blo 1725063 4366781 := bbase (se 3 (by rfl) ⟨818771, by rfl⟩ : syracuseStep 4366781 = 1637543) (by norm_num)
theorem B2589125 : Blo 1725063 2589125 := bbase (se 4 (by rfl) ⟨242730, by rfl⟩ : syracuseStep 2589125 = 485461) (by norm_num)
theorem B1941961 : Blo 1725063 1941961 := bbase (se 2 (by rfl) ⟨728235, by rfl⟩ : syracuseStep 1941961 = 1456471) (by norm_num)
theorem B2589149 : Blo 1725063 2589149 := bbase (se 3 (by rfl) ⟨485465, by rfl⟩ : syracuseStep 2589149 = 970931) (by norm_num)
theorem B1941997 : Blo 1725063 1941997 := bbase (se 3 (by rfl) ⟨364124, by rfl⟩ : syracuseStep 1941997 = 728249) (by norm_num)
theorem B2589173 : Blo 1725063 2589173 := bbase (se 5 (by rfl) ⟨121367, by rfl⟩ : syracuseStep 2589173 = 242735) (by norm_num)
theorem B3883517 : Blo 1725063 3883517 := bbase (se 3 (by rfl) ⟨728159, by rfl⟩ : syracuseStep 3883517 = 1456319) (by norm_num)
theorem B2073097 : Blo 1725063 2073097 := bbase (se 2 (by rfl) ⟨777411, by rfl⟩ : syracuseStep 2073097 = 1554823) (by norm_num)
theorem B2589197 : Blo 1725063 2589197 := bbase (se 3 (by rfl) ⟨485474, by rfl⟩ : syracuseStep 2589197 = 970949) (by norm_num)
theorem B1942033 : Blo 1725063 1942033 := bbase (se 2 (by rfl) ⟨728262, by rfl⟩ : syracuseStep 1942033 = 1456525) (by norm_num)
theorem B3686933 : Blo 1725063 3686933 := bbase (se 6 (by rfl) ⟨86412, by rfl⟩ : syracuseStep 3686933 = 172825) (by norm_num)
theorem B2589221 : Blo 1725063 2589221 := bbase (se 4 (by rfl) ⟨242739, by rfl⟩ : syracuseStep 2589221 = 485479) (by norm_num)
theorem B7979573 : Blo 1725063 7979573 := bbase (se 5 (by rfl) ⟨374042, by rfl⟩ : syracuseStep 7979573 = 748085) (by norm_num)
theorem B1942069 : Blo 1725063 1942069 := bbase (se 5 (by rfl) ⟨91034, by rfl⟩ : syracuseStep 1942069 = 182069) (by norm_num)
theorem B2589245 : Blo 1725063 2589245 := bbase (se 3 (by rfl) ⟨485483, by rfl⟩ : syracuseStep 2589245 = 970967) (by norm_num)
theorem B3883589 : Blo 1725063 3883589 := bbase (se 4 (by rfl) ⟨364086, by rfl⟩ : syracuseStep 3883589 = 728173) (by norm_num)
theorem B2589269 : Blo 1725063 2589269 := bbase (se 8 (by rfl) ⟨15171, by rfl⟩ : syracuseStep 2589269 = 30343) (by norm_num)
theorem B1942105 : Blo 1725063 1942105 := bbase (se 2 (by rfl) ⟨728289, by rfl⟩ : syracuseStep 1942105 = 1456579) (by norm_num)
theorem B2589293 : Blo 1725063 2589293 := bbase (se 3 (by rfl) ⟨485492, by rfl⟩ : syracuseStep 2589293 = 970985) (by norm_num)
theorem B5825141 : Blo 1725063 5825141 := bbase (se 5 (by rfl) ⟨273053, by rfl⟩ : syracuseStep 5825141 = 546107) (by norm_num)
theorem B4915829 : Blo 1725063 4915829 := bbase (se 5 (by rfl) ⟨230429, by rfl⟩ : syracuseStep 4915829 = 460859) (by norm_num)
theorem B4366973 : Blo 1725063 4366973 := bbase (se 3 (by rfl) ⟨818807, by rfl⟩ : syracuseStep 4366973 = 1637615) (by norm_num)
theorem B1942141 : Blo 1725063 1942141 := bbase (se 3 (by rfl) ⟨364151, by rfl⟩ : syracuseStep 1942141 = 728303) (by norm_num)
theorem B2589317 : Blo 1725063 2589317 := bbase (se 4 (by rfl) ⟨242748, by rfl⟩ : syracuseStep 2589317 = 485497) (by norm_num)
theorem B3883661 : Blo 1725063 3883661 := bbase (se 3 (by rfl) ⟨728186, by rfl⟩ : syracuseStep 3883661 = 1456373) (by norm_num)
theorem B2589341 : Blo 1725063 2589341 := bbase (se 3 (by rfl) ⟨485501, by rfl⟩ : syracuseStep 2589341 = 971003) (by norm_num)
theorem B1942177 : Blo 1725063 1942177 := bbase (se 2 (by rfl) ⟨728316, by rfl⟩ : syracuseStep 1942177 = 1456633) (by norm_num)
theorem B3687077 : Blo 1725063 3687077 := bbase (se 4 (by rfl) ⟨345663, by rfl⟩ : syracuseStep 3687077 = 691327) (by norm_num)
theorem B1843889 : Blo 1725063 1843889 := bbase (se 2 (by rfl) ⟨691458, by rfl⟩ : syracuseStep 1843889 = 1382917) (by norm_num)
theorem B2589365 : Blo 1725063 2589365 := bbase (se 5 (by rfl) ⟨121376, by rfl⟩ : syracuseStep 2589365 = 242753) (by norm_num)
theorem B3277493 : Blo 1725063 3277493 := bbase (se 5 (by rfl) ⟨153632, by rfl⟩ : syracuseStep 3277493 = 307265) (by norm_num)
theorem B1942213 : Blo 1725063 1942213 := bbase (se 4 (by rfl) ⟨182082, by rfl⟩ : syracuseStep 1942213 = 364165) (by norm_num)
theorem B2589389 : Blo 1725063 2589389 := bbase (se 3 (by rfl) ⟨485510, by rfl⟩ : syracuseStep 2589389 = 971021) (by norm_num)
theorem B3883733 : Blo 1725063 3883733 := bbase (se 7 (by rfl) ⟨45512, by rfl⟩ : syracuseStep 3883733 = 91025) (by norm_num)
theorem B2589413 : Blo 1725063 2589413 := bbase (se 4 (by rfl) ⟨242757, by rfl⟩ : syracuseStep 2589413 = 485515) (by norm_num)
theorem B1942249 : Blo 1725063 1942249 := bbase (se 2 (by rfl) ⟨728343, by rfl⟩ : syracuseStep 1942249 = 1456687) (by norm_num)
theorem B2589437 : Blo 1725063 2589437 := bbase (se 3 (by rfl) ⟨485519, by rfl⟩ : syracuseStep 2589437 = 971039) (by norm_num)
theorem B1942285 : Blo 1725063 1942285 := bbase (se 3 (by rfl) ⟨364178, by rfl⟩ : syracuseStep 1942285 = 728357) (by norm_num)
theorem B2589461 : Blo 1725063 2589461 := bbase (se 6 (by rfl) ⟨60690, by rfl⟩ : syracuseStep 2589461 = 121381) (by norm_num)
theorem B3883805 : Blo 1725063 3883805 := bbase (se 3 (by rfl) ⟨728213, by rfl⟩ : syracuseStep 3883805 = 1456427) (by norm_num)
theorem B2589485 : Blo 1725063 2589485 := bbase (se 3 (by rfl) ⟨485528, by rfl⟩ : syracuseStep 2589485 = 971057) (by norm_num)
theorem B1942321 : Blo 1725063 1942321 := bbase (se 2 (by rfl) ⟨728370, by rfl⟩ : syracuseStep 1942321 = 1456741) (by norm_num)
theorem B2589509 : Blo 1725063 2589509 := bbase (se 4 (by rfl) ⟨242766, by rfl⟩ : syracuseStep 2589509 = 485533) (by norm_num)
theorem B1942357 : Blo 1725063 1942357 := bbase (se 9 (by rfl) ⟨5690, by rfl⟩ : syracuseStep 1942357 = 11381) (by norm_num)
theorem B2589533 : Blo 1725063 2589533 := bbase (se 3 (by rfl) ⟨485537, by rfl⟩ : syracuseStep 2589533 = 971075) (by norm_num)
theorem B3883877 : Blo 1725063 3883877 := bbase (se 4 (by rfl) ⟨364113, by rfl⟩ : syracuseStep 3883877 = 728227) (by norm_num)
theorem B2589557 : Blo 1725063 2589557 := bbase (se 5 (by rfl) ⟨121385, by rfl⟩ : syracuseStep 2589557 = 242771) (by norm_num)
theorem B1942393 : Blo 1725063 1942393 := bbase (se 2 (by rfl) ⟨728397, by rfl⟩ : syracuseStep 1942393 = 1456795) (by norm_num)
theorem B2073481 : Blo 1725063 2073481 := bbase (se 2 (by rfl) ⟨777555, by rfl⟩ : syracuseStep 2073481 = 1555111) (by norm_num)
theorem B2589581 : Blo 1725063 2589581 := bbase (se 3 (by rfl) ⟨485546, by rfl⟩ : syracuseStep 2589581 = 971093) (by norm_num)
theorem B1942429 : Blo 1725063 1942429 := bbase (se 3 (by rfl) ⟨364205, by rfl⟩ : syracuseStep 1942429 = 728411) (by norm_num)
theorem B2589605 : Blo 1725063 2589605 := bbase (se 4 (by rfl) ⟨242775, by rfl⟩ : syracuseStep 2589605 = 485551) (by norm_num)
theorem B1844137 : Blo 1725063 1844137 := bbase (se 2 (by rfl) ⟨691551, by rfl⟩ : syracuseStep 1844137 = 1383103) (by norm_num)
theorem B3883949 : Blo 1725063 3883949 := bbase (se 3 (by rfl) ⟨728240, by rfl⟩ : syracuseStep 3883949 = 1456481) (by norm_num)
theorem B2589629 : Blo 1725063 2589629 := bbase (se 3 (by rfl) ⟨485555, by rfl⟩ : syracuseStep 2589629 = 971111) (by norm_num)
theorem B1942465 : Blo 1725063 1942465 := bbase (se 2 (by rfl) ⟨728424, by rfl⟩ : syracuseStep 1942465 = 1456849) (by norm_num)
theorem B4367317 : Blo 1725063 4367317 := bbase (se 7 (by rfl) ⟨51179, by rfl⟩ : syracuseStep 4367317 = 102359) (by norm_num)
theorem B2589653 : Blo 1725063 2589653 := bbase (se 7 (by rfl) ⟨30347, by rfl⟩ : syracuseStep 2589653 = 60695) (by norm_num)
theorem B1942501 : Blo 1725063 1942501 := bbase (se 4 (by rfl) ⟨182109, by rfl⟩ : syracuseStep 1942501 = 364219) (by norm_num)
theorem B2589677 : Blo 1725063 2589677 := bbase (se 3 (by rfl) ⟨485564, by rfl⟩ : syracuseStep 2589677 = 971129) (by norm_num)
theorem B3884021 : Blo 1725063 3884021 := bbase (se 5 (by rfl) ⟨182063, by rfl⟩ : syracuseStep 3884021 = 364127) (by norm_num)
theorem B2458621 : Blo 1725063 2458621 := bbase (se 3 (by rfl) ⟨460991, by rfl⟩ : syracuseStep 2458621 = 921983) (by norm_num)
theorem B2589701 : Blo 1725063 2589701 := bbase (se 4 (by rfl) ⟨242784, by rfl⟩ : syracuseStep 2589701 = 485569) (by norm_num)
theorem B1942537 : Blo 1725063 1942537 := bbase (se 2 (by rfl) ⟨728451, by rfl⟩ : syracuseStep 1942537 = 1456903) (by norm_num)
theorem B2802701 : Blo 1725063 2802701 := bbase (se 3 (by rfl) ⟨525506, by rfl⟩ : syracuseStep 2802701 = 1051013) (by norm_num)
theorem B3687437 : Blo 1725063 3687437 := bbase (se 3 (by rfl) ⟨691394, by rfl⟩ : syracuseStep 3687437 = 1382789) (by norm_num)
theorem B2589725 : Blo 1725063 2589725 := bbase (se 3 (by rfl) ⟨485573, by rfl⟩ : syracuseStep 2589725 = 971147) (by norm_num)
theorem B5825573 : Blo 1725063 5825573 := bbase (se 4 (by rfl) ⟨546147, by rfl⟩ : syracuseStep 5825573 = 1092295) (by norm_num)
theorem B1942573 : Blo 1725063 1942573 := bbase (se 3 (by rfl) ⟨364232, by rfl⟩ : syracuseStep 1942573 = 728465) (by norm_num)
theorem B2589749 : Blo 1725063 2589749 := bbase (se 5 (by rfl) ⟨121394, by rfl⟩ : syracuseStep 2589749 = 242789) (by norm_num)
theorem B3884093 : Blo 1725063 3884093 := bbase (se 3 (by rfl) ⟨728267, by rfl⟩ : syracuseStep 3884093 = 1456535) (by norm_num)
theorem B4367429 : Blo 1725063 4367429 := bbase (se 4 (by rfl) ⟨409446, by rfl⟩ : syracuseStep 4367429 = 818893) (by norm_num)
theorem B2589773 : Blo 1725063 2589773 := bbase (se 3 (by rfl) ⟨485582, by rfl⟩ : syracuseStep 2589773 = 971165) (by norm_num)
theorem B1942609 : Blo 1725063 1942609 := bbase (se 2 (by rfl) ⟨728478, by rfl⟩ : syracuseStep 1942609 = 1456957) (by norm_num)
theorem B2589797 : Blo 1725063 2589797 := bbase (se 4 (by rfl) ⟨242793, by rfl⟩ : syracuseStep 2589797 = 485587) (by norm_num)
theorem B1942645 : Blo 1725063 1942645 := bbase (se 5 (by rfl) ⟨91061, by rfl⟩ : syracuseStep 1942645 = 182123) (by norm_num)
theorem B8742005 : Blo 1725063 8742005 := bbase (se 5 (by rfl) ⟨409781, by rfl⟩ : syracuseStep 8742005 = 819563) (by norm_num)
theorem B2589821 : Blo 1725063 2589821 := bbase (se 3 (by rfl) ⟨485591, by rfl⟩ : syracuseStep 2589821 = 971183) (by norm_num)
theorem B3884165 : Blo 1725063 3884165 := bbase (se 4 (by rfl) ⟨364140, by rfl⟩ : syracuseStep 3884165 = 728281) (by norm_num)
theorem B2589845 : Blo 1725063 2589845 := bbase (se 6 (by rfl) ⟨60699, by rfl⟩ : syracuseStep 2589845 = 121399) (by norm_num)
theorem B1942681 : Blo 1725063 1942681 := bbase (se 2 (by rfl) ⟨728505, by rfl⟩ : syracuseStep 1942681 = 1457011) (by norm_num)
theorem B6554789 : Blo 1725063 6554789 := bbase (se 4 (by rfl) ⟨614511, by rfl⟩ : syracuseStep 6554789 = 1229023) (by norm_num)
theorem B2589869 : Blo 1725063 2589869 := bbase (se 3 (by rfl) ⟨485600, by rfl⟩ : syracuseStep 2589869 = 971201) (by norm_num)
theorem B14746805 : Blo 1725063 14746805 := bbase (se 5 (by rfl) ⟨691256, by rfl⟩ : syracuseStep 14746805 = 1382513) (by norm_num)
theorem B1942717 : Blo 1725063 1942717 := bbase (se 3 (by rfl) ⟨364259, by rfl⟩ : syracuseStep 1942717 = 728519) (by norm_num)
theorem B2589893 : Blo 1725063 2589893 := bbase (se 4 (by rfl) ⟨242802, by rfl⟩ : syracuseStep 2589893 = 485605) (by norm_num)
theorem B3884237 : Blo 1725063 3884237 := bbase (se 3 (by rfl) ⟨728294, by rfl⟩ : syracuseStep 3884237 = 1456589) (by norm_num)
theorem B2589917 : Blo 1725063 2589917 := bbase (se 3 (by rfl) ⟨485609, by rfl⟩ : syracuseStep 2589917 = 971219) (by norm_num)
theorem B1942753 : Blo 1725063 1942753 := bbase (se 2 (by rfl) ⟨728532, by rfl⟩ : syracuseStep 1942753 = 1457065) (by norm_num)
theorem B2589941 : Blo 1725063 2589941 := bbase (se 5 (by rfl) ⟨121403, by rfl⟩ : syracuseStep 2589941 = 242807) (by norm_num)
theorem B4367621 : Blo 1725063 4367621 := bbase (se 4 (by rfl) ⟨409464, by rfl⟩ : syracuseStep 4367621 = 818929) (by norm_num)
theorem B1942789 : Blo 1725063 1942789 := bbase (se 4 (by rfl) ⟨182136, by rfl⟩ : syracuseStep 1942789 = 364273) (by norm_num)
theorem B2589965 : Blo 1725063 2589965 := bbase (se 3 (by rfl) ⟨485618, by rfl⟩ : syracuseStep 2589965 = 971237) (by norm_num)
theorem B3884309 : Blo 1725063 3884309 := bbase (se 6 (by rfl) ⟨91038, by rfl⟩ : syracuseStep 3884309 = 182077) (by norm_num)
theorem B2589989 : Blo 1725063 2589989 := bbase (se 4 (by rfl) ⟨242811, by rfl⟩ : syracuseStep 2589989 = 485623) (by norm_num)
theorem B1942825 : Blo 1725063 1942825 := bbase (se 2 (by rfl) ⟨728559, by rfl⟩ : syracuseStep 1942825 = 1457119) (by norm_num)
theorem B2590013 : Blo 1725063 2590013 := bbase (se 3 (by rfl) ⟨485627, by rfl⟩ : syracuseStep 2590013 = 971255) (by norm_num)
theorem B1942861 : Blo 1725063 1942861 := bbase (se 3 (by rfl) ⟨364286, by rfl⟩ : syracuseStep 1942861 = 728573) (by norm_num)
theorem B2590037 : Blo 1725063 2590037 := bbase (se 12 (by rfl) ⟨948, by rfl⟩ : syracuseStep 2590037 = 1897) (by norm_num)
theorem B3884381 : Blo 1725063 3884381 := bbase (se 3 (by rfl) ⟨728321, by rfl⟩ : syracuseStep 3884381 = 1456643) (by norm_num)
theorem B2590061 : Blo 1725063 2590061 := bbase (se 3 (by rfl) ⟨485636, by rfl⟩ : syracuseStep 2590061 = 971273) (by norm_num)
theorem B1942897 : Blo 1725063 1942897 := bbase (se 2 (by rfl) ⟨728586, by rfl⟩ : syracuseStep 1942897 = 1457173) (by norm_num)
theorem B2590085 : Blo 1725063 2590085 := bbase (se 4 (by rfl) ⟨242820, by rfl⟩ : syracuseStep 2590085 = 485641) (by norm_num)
theorem B1942933 : Blo 1725063 1942933 := bbase (se 6 (by rfl) ⟨45537, by rfl⟩ : syracuseStep 1942933 = 91075) (by norm_num)
theorem B2590109 : Blo 1725063 2590109 := bbase (se 3 (by rfl) ⟨485645, by rfl⟩ : syracuseStep 2590109 = 971291) (by norm_num)
theorem B3884453 : Blo 1725063 3884453 := bbase (se 4 (by rfl) ⟨364167, by rfl⟩ : syracuseStep 3884453 = 728335) (by norm_num)
theorem B3278245 : Blo 1725063 3278245 := bbase (se 4 (by rfl) ⟨307335, by rfl⟩ : syracuseStep 3278245 = 614671) (by norm_num)
theorem B2590133 : Blo 1725063 2590133 := bbase (se 5 (by rfl) ⟨121412, by rfl⟩ : syracuseStep 2590133 = 242825) (by norm_num)
theorem B6555077 : Blo 1725063 6555077 := bbase (se 4 (by rfl) ⟨614538, by rfl⟩ : syracuseStep 6555077 = 1229077) (by norm_num)
theorem B2590157 : Blo 1725063 2590157 := bbase (se 3 (by rfl) ⟨485654, by rfl⟩ : syracuseStep 2590157 = 971309) (by norm_num)
theorem B5826005 : Blo 1725063 5826005 := bbase (se 7 (by rfl) ⟨68273, by rfl⟩ : syracuseStep 5826005 = 136547) (by norm_num)
theorem B2590181 : Blo 1725063 2590181 := bbase (se 4 (by rfl) ⟨242829, by rfl⟩ : syracuseStep 2590181 = 485659) (by norm_num)
theorem B3884525 : Blo 1725063 3884525 := bbase (se 3 (by rfl) ⟨728348, by rfl⟩ : syracuseStep 3884525 = 1456697) (by norm_num)
theorem B2590205 : Blo 1725063 2590205 := bbase (se 3 (by rfl) ⟨485663, by rfl⟩ : syracuseStep 2590205 = 971327) (by norm_num)
theorem B8734229 : Blo 1725063 8734229 := bbase (se 6 (by rfl) ⟨204708, by rfl⟩ : syracuseStep 8734229 = 409417) (by norm_num)
theorem B2590229 : Blo 1725063 2590229 := bbase (se 6 (by rfl) ⟨60708, by rfl⟩ : syracuseStep 2590229 = 121417) (by norm_num)
theorem B2590253 : Blo 1725063 2590253 := bbase (se 3 (by rfl) ⟨485672, by rfl⟩ : syracuseStep 2590253 = 971345) (by norm_num)
theorem B3884597 : Blo 1725063 3884597 := bbase (se 5 (by rfl) ⟨182090, by rfl⟩ : syracuseStep 3884597 = 364181) (by norm_num)
theorem B2491957 : Blo 1725063 2491957 := bbase (se 5 (by rfl) ⟨116810, by rfl⟩ : syracuseStep 2491957 = 233621) (by norm_num)
theorem B3278389 : Blo 1725063 3278389 := bbase (se 5 (by rfl) ⟨153674, by rfl⟩ : syracuseStep 3278389 = 307349) (by norm_num)
theorem B8291909 : Blo 1725063 8291909 := bbase (se 4 (by rfl) ⟨777366, by rfl⟩ : syracuseStep 8291909 = 1554733) (by norm_num)
theorem B2590277 : Blo 1725063 2590277 := bbase (se 4 (by rfl) ⟨242838, by rfl⟩ : syracuseStep 2590277 = 485677) (by norm_num)
theorem B4204109 : Blo 1725063 4204109 := bbase (se 3 (by rfl) ⟨788270, by rfl⟩ : syracuseStep 4204109 = 1576541) (by norm_num)
theorem B4916821 : Blo 1725063 4916821 := bbase (se 8 (by rfl) ⟨28809, by rfl⟩ : syracuseStep 4916821 = 57619) (by norm_num)
theorem B4367965 : Blo 1725063 4367965 := bbase (se 3 (by rfl) ⟨818993, by rfl⟩ : syracuseStep 4367965 = 1637987) (by norm_num)
theorem B2590301 : Blo 1725063 2590301 := bbase (se 3 (by rfl) ⟨485681, by rfl⟩ : syracuseStep 2590301 = 971363) (by norm_num)
theorem B2590325 : Blo 1725063 2590325 := bbase (se 5 (by rfl) ⟨121421, by rfl⟩ : syracuseStep 2590325 = 242843) (by norm_num)
theorem B3884669 : Blo 1725063 3884669 := bbase (se 3 (by rfl) ⟨728375, by rfl⟩ : syracuseStep 3884669 = 1456751) (by norm_num)
theorem B4204165 : Blo 1725063 4204165 := bbase (se 4 (by rfl) ⟨394140, by rfl⟩ : syracuseStep 4204165 = 788281) (by norm_num)
theorem B2590349 : Blo 1725063 2590349 := bbase (se 3 (by rfl) ⟨485690, by rfl⟩ : syracuseStep 2590349 = 971381) (by norm_num)
theorem B2950805 : Blo 1725063 2950805 := bbase (se 6 (by rfl) ⟨69159, by rfl⟩ : syracuseStep 2950805 = 138319) (by norm_num)
theorem B18663061 : Blo 1725063 18663061 := bbase (se 6 (by rfl) ⟨437415, by rfl⟩ : syracuseStep 18663061 = 874831) (by norm_num)
theorem B2590373 : Blo 1725063 2590373 := bbase (se 4 (by rfl) ⟨242847, by rfl⟩ : syracuseStep 2590373 = 485695) (by norm_num)
theorem B2590397 : Blo 1725063 2590397 := bbase (se 3 (by rfl) ⟨485699, by rfl⟩ : syracuseStep 2590397 = 971399) (by norm_num)
theorem B3884741 : Blo 1725063 3884741 := bbase (se 4 (by rfl) ⟨364194, by rfl⟩ : syracuseStep 3884741 = 728389) (by norm_num)
theorem B5531333 : Blo 1725063 5531333 := bbase (se 4 (by rfl) ⟨518562, by rfl⟩ : syracuseStep 5531333 = 1037125) (by norm_num)
theorem B4368077 : Blo 1725063 4368077 := bbase (se 3 (by rfl) ⟨819014, by rfl⟩ : syracuseStep 4368077 = 1638029) (by norm_num)
theorem B2590421 : Blo 1725063 2590421 := bbase (se 7 (by rfl) ⟨30356, by rfl⟩ : syracuseStep 2590421 = 60713) (by norm_num)
theorem B3278549 : Blo 1725063 3278549 := bbase (se 7 (by rfl) ⟨38420, by rfl⟩ : syracuseStep 3278549 = 76841) (by norm_num)
theorem B2590445 : Blo 1725063 2590445 := bbase (se 3 (by rfl) ⟨485708, by rfl⟩ : syracuseStep 2590445 = 971417) (by norm_num)
theorem B8406773 : Blo 1725063 8406773 := bbase (se 5 (by rfl) ⟨394067, by rfl⟩ : syracuseStep 8406773 = 788135) (by norm_num)
theorem B2590469 : Blo 1725063 2590469 := bbase (se 4 (by rfl) ⟨242856, by rfl⟩ : syracuseStep 2590469 = 485713) (by norm_num)
theorem B3884813 : Blo 1725063 3884813 := bbase (se 3 (by rfl) ⟨728402, by rfl⟩ : syracuseStep 3884813 = 1456805) (by norm_num)
theorem B2590493 : Blo 1725063 2590493 := bbase (se 3 (by rfl) ⟨485717, by rfl⟩ : syracuseStep 2590493 = 971435) (by norm_num)
theorem B2623277 : Blo 1725063 2623277 := bbase (se 3 (by rfl) ⟨491864, by rfl⟩ : syracuseStep 2623277 = 983729) (by norm_num)
theorem B2590517 : Blo 1725063 2590517 := bbase (se 5 (by rfl) ⟨121430, by rfl⟩ : syracuseStep 2590517 = 242861) (by norm_num)
theorem B2590541 : Blo 1725063 2590541 := bbase (se 3 (by rfl) ⟨485726, by rfl⟩ : syracuseStep 2590541 = 971453) (by norm_num)
theorem B3499861 : Blo 1725063 3499861 := bbase (se 9 (by rfl) ⟨10253, by rfl⟩ : syracuseStep 3499861 = 20507) (by norm_num)
theorem B3884885 : Blo 1725063 3884885 := bbase (se 9 (by rfl) ⟨11381, by rfl⟩ : syracuseStep 3884885 = 22763) (by norm_num)
theorem B2590565 : Blo 1725063 2590565 := bbase (se 4 (by rfl) ⟨242865, by rfl⟩ : syracuseStep 2590565 = 485731) (by norm_num)
theorem B3278693 : Blo 1725063 3278693 := bbase (se 4 (by rfl) ⟨307377, by rfl⟩ : syracuseStep 3278693 = 614755) (by norm_num)
theorem B2590589 : Blo 1725063 2590589 := bbase (se 3 (by rfl) ⟨485735, by rfl⟩ : syracuseStep 2590589 = 971471) (by norm_num)
theorem B5826437 : Blo 1725063 5826437 := bbase (se 4 (by rfl) ⟨546228, by rfl⟩ : syracuseStep 5826437 = 1092457) (by norm_num)
theorem B3688325 : Blo 1725063 3688325 := bbase (se 4 (by rfl) ⟨345780, by rfl⟩ : syracuseStep 3688325 = 691561) (by norm_num)
theorem B4368269 : Blo 1725063 4368269 := bbase (se 3 (by rfl) ⟨819050, by rfl⟩ : syracuseStep 4368269 = 1638101) (by norm_num)
theorem B3884957 : Blo 1725063 3884957 := bbase (se 3 (by rfl) ⟨728429, by rfl⟩ : syracuseStep 3884957 = 1456859) (by norm_num)
theorem B2074529 : Blo 1725063 2074529 := bbase (se 2 (by rfl) ⟨777948, by rfl⟩ : syracuseStep 2074529 = 1555897) (by norm_num)
theorem B2951093 : Blo 1725063 2951093 := bbase (se 5 (by rfl) ⟨138332, by rfl⟩ : syracuseStep 2951093 = 276665) (by norm_num)
theorem B3885029 : Blo 1725063 3885029 := bbase (se 4 (by rfl) ⟨364221, by rfl⟩ : syracuseStep 3885029 = 728443) (by norm_num)
theorem B4147213 : Blo 1725063 4147213 := bbase (se 3 (by rfl) ⟨777602, by rfl⟩ : syracuseStep 4147213 = 1555205) (by norm_num)
theorem B3885101 : Blo 1725063 3885101 := bbase (se 3 (by rfl) ⟨728456, by rfl⟩ : syracuseStep 3885101 = 1456913) (by norm_num)
theorem B3885173 : Blo 1725063 3885173 := bbase (se 5 (by rfl) ⟨182117, by rfl⟩ : syracuseStep 3885173 = 364235) (by norm_num)
theorem B4491421 : Blo 1725063 4491421 := bbase (se 3 (by rfl) ⟨842141, by rfl⟩ : syracuseStep 4491421 = 1684283) (by norm_num)
theorem B3885245 : Blo 1725063 3885245 := bbase (se 3 (by rfl) ⟨728483, by rfl⟩ : syracuseStep 3885245 = 1456967) (by norm_num)
theorem B9832661 : Blo 1725063 9832661 := bbase (se 7 (by rfl) ⟨115226, by rfl⟩ : syracuseStep 9832661 = 230453) (by norm_num)
theorem B8292581 : Blo 1725063 8292581 := bbase (se 4 (by rfl) ⟨777429, by rfl⟩ : syracuseStep 8292581 = 1554859) (by norm_num)
theorem B4368613 : Blo 1725063 4368613 := bbase (se 4 (by rfl) ⟨409557, by rfl⟩ : syracuseStep 4368613 = 819115) (by norm_num)
theorem B3885317 : Blo 1725063 3885317 := bbase (se 4 (by rfl) ⟨364248, by rfl⟩ : syracuseStep 3885317 = 728497) (by norm_num)
theorem B5826869 : Blo 1725063 5826869 := bbase (se 5 (by rfl) ⟨273134, by rfl⟩ : syracuseStep 5826869 = 546269) (by norm_num)
theorem B3885389 : Blo 1725063 3885389 := bbase (se 3 (by rfl) ⟨728510, by rfl⟩ : syracuseStep 3885389 = 1457021) (by norm_num)
theorem B25905493 : Blo 1725063 25905493 := bbase (se 10 (by rfl) ⟨37947, by rfl⟩ : syracuseStep 25905493 = 75895) (by norm_num)
theorem B4368725 : Blo 1725063 4368725 := bbase (se 10 (by rfl) ⟨6399, by rfl⟩ : syracuseStep 4368725 = 12799) (by norm_num)
theorem B2623861 : Blo 1725063 2623861 := bbase (se 5 (by rfl) ⟨122993, by rfl⟩ : syracuseStep 2623861 = 245987) (by norm_num)
theorem B3885461 : Blo 1725063 3885461 := bbase (se 6 (by rfl) ⟨91065, by rfl⟩ : syracuseStep 3885461 = 182131) (by norm_num)
theorem B11053493 : Blo 1725063 11053493 := bbase (se 5 (by rfl) ⟨518132, by rfl⟩ : syracuseStep 11053493 = 1036265) (by norm_num)
theorem B2697661 : Blo 1725063 2697661 := bbase (se 3 (by rfl) ⟨505811, by rfl⟩ : syracuseStep 2697661 = 1011623) (by norm_num)
theorem B3885533 : Blo 1725063 3885533 := bbase (se 3 (by rfl) ⟨728537, by rfl⟩ : syracuseStep 3885533 = 1457075) (by norm_num)
theorem B3500525 : Blo 1725063 3500525 := bbase (se 3 (by rfl) ⟨656348, by rfl⟩ : syracuseStep 3500525 = 1312697) (by norm_num)
theorem B4368917 : Blo 1725063 4368917 := bbase (se 6 (by rfl) ⟨102396, by rfl⟩ : syracuseStep 4368917 = 204793) (by norm_num)
theorem B4549157 : Blo 1725063 4549157 := bbase (se 4 (by rfl) ⟨426483, by rfl⟩ : syracuseStep 4549157 = 852967) (by norm_num)
theorem B3885605 : Blo 1725063 3885605 := bbase (se 4 (by rfl) ⟨364275, by rfl⟩ : syracuseStep 3885605 = 728551) (by norm_num)
theorem B5532245 : Blo 1725063 5532245 := bbase (se 8 (by rfl) ⟨32415, by rfl⟩ : syracuseStep 5532245 = 64831) (by norm_num)
theorem B6556261 : Blo 1725063 6556261 := bbase (se 4 (by rfl) ⟨614649, by rfl⟩ : syracuseStep 6556261 = 1229299) (by norm_num)
theorem B3885677 : Blo 1725063 3885677 := bbase (se 3 (by rfl) ⟨728564, by rfl⟩ : syracuseStep 3885677 = 1457129) (by norm_num)
theorem B4917925 : Blo 1725063 4917925 := bbase (se 4 (by rfl) ⟨461055, by rfl⟩ : syracuseStep 4917925 = 922111) (by norm_num)
theorem B4147885 : Blo 1725063 4147885 := bbase (se 3 (by rfl) ⟨777728, by rfl⟩ : syracuseStep 4147885 = 1555457) (by norm_num)
theorem B3885749 : Blo 1725063 3885749 := bbase (se 5 (by rfl) ⟨182144, by rfl⟩ : syracuseStep 3885749 = 364289) (by norm_num)
theorem B1968845 : Blo 1725063 1968845 := bbase (se 3 (by rfl) ⟨369158, by rfl⟩ : syracuseStep 1968845 = 738317) (by norm_num)
theorem B5827301 : Blo 1725063 5827301 := bbase (se 4 (by rfl) ⟨546309, by rfl⟩ : syracuseStep 5827301 = 1092619) (by norm_num)
theorem B3885821 : Blo 1725063 3885821 := bbase (se 3 (by rfl) ⟨728591, by rfl⟩ : syracuseStep 3885821 = 1457183) (by norm_num)
theorem B8735525 : Blo 1725063 8735525 := bbase (se 4 (by rfl) ⟨818955, by rfl⟩ : syracuseStep 8735525 = 1637911) (by norm_num)
theorem B2911045 : Blo 1725063 2911045 := bbase (se 4 (by rfl) ⟨272910, by rfl⟩ : syracuseStep 2911045 = 545821) (by norm_num)
theorem B3885893 : Blo 1725063 3885893 := bbase (se 4 (by rfl) ⟨364302, by rfl⟩ : syracuseStep 3885893 = 728605) (by norm_num)
theorem B4369261 : Blo 1725063 4369261 := bbase (se 3 (by rfl) ⟨819236, by rfl⟩ : syracuseStep 4369261 = 1638473) (by norm_num)
theorem B4148117 : Blo 1725063 4148117 := bbase (se 6 (by rfl) ⟨97221, by rfl⟩ : syracuseStep 4148117 = 194443) (by norm_num)
theorem B6556565 : Blo 1725063 6556565 := bbase (se 6 (by rfl) ⟨153669, by rfl⟩ : syracuseStep 6556565 = 307339) (by norm_num)
theorem B2911133 : Blo 1725063 2911133 := bbase (se 3 (by rfl) ⟨545837, by rfl⟩ : syracuseStep 2911133 = 1091675) (by norm_num)
theorem B4369373 : Blo 1725063 4369373 := bbase (se 3 (by rfl) ⟨819257, by rfl⟩ : syracuseStep 4369373 = 1638515) (by norm_num)
theorem B2911261 : Blo 1725063 2911261 := bbase (se 3 (by rfl) ⟨545861, by rfl⟩ : syracuseStep 2911261 = 1091723) (by norm_num)
theorem B4148261 : Blo 1725063 4148261 := bbase (se 4 (by rfl) ⟨388899, by rfl⟩ : syracuseStep 4148261 = 777799) (by norm_num)
theorem B5246021 : Blo 1725063 5246021 := bbase (se 4 (by rfl) ⟨491814, by rfl⟩ : syracuseStep 5246021 = 983629) (by norm_num)
theorem B4664405 : Blo 1725063 4664405 := bbase (se 8 (by rfl) ⟨27330, by rfl⟩ : syracuseStep 4664405 = 54661) (by norm_num)
theorem B4148309 : Blo 1725063 4148309 := bbase (se 8 (by rfl) ⟨24306, by rfl⟩ : syracuseStep 4148309 = 48613) (by norm_num)
theorem B2911349 : Blo 1725063 2911349 := bbase (se 5 (by rfl) ⟨136469, by rfl⟩ : syracuseStep 2911349 = 272939) (by norm_num)
theorem B1772689 : Blo 1725063 1772689 := bbase (se 2 (by rfl) ⟨664758, by rfl⟩ : syracuseStep 1772689 = 1329517) (by norm_num)
theorem B5827733 : Blo 1725063 5827733 := bbase (se 6 (by rfl) ⟨136587, by rfl⟩ : syracuseStep 5827733 = 273175) (by norm_num)
theorem B4369565 : Blo 1725063 4369565 := bbase (se 3 (by rfl) ⟨819293, by rfl⟩ : syracuseStep 4369565 = 1638587) (by norm_num)
theorem B2911477 : Blo 1725063 2911477 := bbase (se 5 (by rfl) ⟨136475, by rfl⟩ : syracuseStep 2911477 = 272951) (by norm_num)
theorem B2911565 : Blo 1725063 2911565 := bbase (se 3 (by rfl) ⟨545918, by rfl⟩ : syracuseStep 2911565 = 1091837) (by norm_num)
theorem B4148597 : Blo 1725063 4148597 := bbase (se 5 (by rfl) ⟨194465, by rfl⟩ : syracuseStep 4148597 = 388931) (by norm_num)
theorem B9833845 : Blo 1725063 9833845 := bbase (se 5 (by rfl) ⟨460961, by rfl⟩ : syracuseStep 9833845 = 921923) (by norm_num)
theorem B2764181 : Blo 1725063 2764181 := bbase (se 6 (by rfl) ⟨64785, by rfl⟩ : syracuseStep 2764181 = 129571) (by norm_num)
theorem B7876037 : Blo 1725063 7876037 := bbase (se 4 (by rfl) ⟨738378, by rfl⟩ : syracuseStep 7876037 = 1476757) (by norm_num)
theorem B2911693 : Blo 1725063 2911693 := bbase (se 3 (by rfl) ⟨545942, by rfl⟩ : syracuseStep 2911693 = 1091885) (by norm_num)
theorem B7376341 : Blo 1725063 7376341 := bbase (se 7 (by rfl) ⟨86441, by rfl⟩ : syracuseStep 7376341 = 172883) (by norm_num)
theorem B4369909 : Blo 1725063 4369909 := bbase (se 5 (by rfl) ⟨204839, by rfl⟩ : syracuseStep 4369909 = 409679) (by norm_num)
theorem B4664837 : Blo 1725063 4664837 := bbase (se 4 (by rfl) ⟨437328, by rfl⟩ : syracuseStep 4664837 = 874657) (by norm_num)
theorem B2764309 : Blo 1725063 2764309 := bbase (se 6 (by rfl) ⟨64788, by rfl⟩ : syracuseStep 2764309 = 129577) (by norm_num)
theorem B2911781 : Blo 1725063 2911781 := bbase (se 4 (by rfl) ⟨272979, by rfl⟩ : syracuseStep 2911781 = 545959) (by norm_num)
theorem B5828165 : Blo 1725063 5828165 := bbase (se 4 (by rfl) ⟨546390, by rfl⟩ : syracuseStep 5828165 = 1092781) (by norm_num)
theorem B4370021 : Blo 1725063 4370021 := bbase (se 4 (by rfl) ⟨409689, by rfl⟩ : syracuseStep 4370021 = 819379) (by norm_num)
theorem B2215525 : Blo 1725063 2215525 := bbase (se 4 (by rfl) ⟨207705, by rfl⟩ : syracuseStep 2215525 = 415411) (by norm_num)
theorem B20983445 : Blo 1725063 20983445 := bbase (se 6 (by rfl) ⟨491799, by rfl⟩ : syracuseStep 20983445 = 983599) (by norm_num)
theorem B1748633 : Blo 1725063 1748633 := bbase (se 2 (by rfl) ⟨655737, by rfl⟩ : syracuseStep 1748633 = 1311475) (by norm_num)
theorem B2911909 : Blo 1725063 2911909 := bbase (se 4 (by rfl) ⟨272991, by rfl⟩ : syracuseStep 2911909 = 545983) (by norm_num)
theorem B2911997 : Blo 1725063 2911997 := bbase (se 3 (by rfl) ⟨545999, by rfl⟩ : syracuseStep 2911997 = 1091999) (by norm_num)
theorem B8408837 : Blo 1725063 8408837 := bbase (se 4 (by rfl) ⟨788328, by rfl⟩ : syracuseStep 8408837 = 1576657) (by norm_num)
theorem B4370213 : Blo 1725063 4370213 := bbase (se 4 (by rfl) ⟨409707, by rfl⟩ : syracuseStep 4370213 = 819415) (by norm_num)
theorem B4665205 : Blo 1725063 4665205 := bbase (se 5 (by rfl) ⟨218681, by rfl⟩ : syracuseStep 4665205 = 437363) (by norm_num)
theorem B2912125 : Blo 1725063 2912125 := bbase (se 3 (by rfl) ⟨546023, by rfl⟩ : syracuseStep 2912125 = 1092047) (by norm_num)
theorem B2764693 : Blo 1725063 2764693 := bbase (se 6 (by rfl) ⟨64797, by rfl⟩ : syracuseStep 2764693 = 129595) (by norm_num)
theorem B2912213 : Blo 1725063 2912213 := bbase (se 7 (by rfl) ⟨34127, by rfl⟩ : syracuseStep 2912213 = 68255) (by norm_num)
theorem B5050325 : Blo 1725063 5050325 := bbase (se 7 (by rfl) ⟨59183, by rfl⟩ : syracuseStep 5050325 = 118367) (by norm_num)
theorem B5828597 : Blo 1725063 5828597 := bbase (se 5 (by rfl) ⟨273215, by rfl⟩ : syracuseStep 5828597 = 546431) (by norm_num)
theorem B5247029 : Blo 1725063 5247029 := bbase (se 5 (by rfl) ⟨245954, by rfl⟩ : syracuseStep 5247029 = 491909) (by norm_num)
theorem B8736821 : Blo 1725063 8736821 := bbase (se 5 (by rfl) ⟨409538, by rfl⟩ : syracuseStep 8736821 = 819077) (by norm_num)
theorem B2912341 : Blo 1725063 2912341 := bbase (se 8 (by rfl) ⟨17064, by rfl⟩ : syracuseStep 2912341 = 34129) (by norm_num)
theorem B4370557 : Blo 1725063 4370557 := bbase (se 3 (by rfl) ⟨819479, by rfl⟩ : syracuseStep 4370557 = 1638959) (by norm_num)
theorem B2764949 : Blo 1725063 2764949 := bbase (se 6 (by rfl) ⟨64803, by rfl⟩ : syracuseStep 2764949 = 129607) (by norm_num)
theorem B2912429 : Blo 1725063 2912429 := bbase (se 3 (by rfl) ⟨546080, by rfl⟩ : syracuseStep 2912429 = 1092161) (by norm_num)
theorem B2183365 : Blo 1725063 2183365 := bbase (se 4 (by rfl) ⟨204690, by rfl⟩ : syracuseStep 2183365 = 409381) (by norm_num)
theorem B3936485 : Blo 1725063 3936485 := bbase (se 4 (by rfl) ⟨369045, by rfl⟩ : syracuseStep 3936485 = 738091) (by norm_num)
theorem B4370669 : Blo 1725063 4370669 := bbase (se 3 (by rfl) ⟨819500, by rfl⟩ : syracuseStep 4370669 = 1639001) (by norm_num)
theorem B2912557 : Blo 1725063 2912557 := bbase (se 3 (by rfl) ⟨546104, by rfl⟩ : syracuseStep 2912557 = 1092209) (by norm_num)
theorem B2183537 : Blo 1725063 2183537 := bbase (se 2 (by rfl) ⟨818826, by rfl⟩ : syracuseStep 2183537 = 1637653) (by norm_num)
theorem B2912645 : Blo 1725063 2912645 := bbase (se 4 (by rfl) ⟨273060, by rfl⟩ : syracuseStep 2912645 = 546121) (by norm_num)
theorem B2183593 : Blo 1725063 2183593 := bbase (se 2 (by rfl) ⟨818847, by rfl⟩ : syracuseStep 2183593 = 1637695) (by norm_num)
theorem B4370861 : Blo 1725063 4370861 := bbase (se 3 (by rfl) ⟨819536, by rfl⟩ : syracuseStep 4370861 = 1639073) (by norm_num)
theorem B3109357 : Blo 1725063 3109357 := bbase (se 3 (by rfl) ⟨583004, by rfl⟩ : syracuseStep 3109357 = 1166009) (by norm_num)
theorem B2912773 : Blo 1725063 2912773 := bbase (se 4 (by rfl) ⟨273072, by rfl⟩ : syracuseStep 2912773 = 546145) (by norm_num)
theorem B2183689 : Blo 1725063 2183689 := bbase (se 2 (by rfl) ⟨818883, by rfl⟩ : syracuseStep 2183689 = 1637767) (by norm_num)
theorem B1749529 : Blo 1725063 1749529 := bbase (se 2 (by rfl) ⟨656073, by rfl⟩ : syracuseStep 1749529 = 1312147) (by norm_num)
theorem B2912861 : Blo 1725063 2912861 := bbase (se 3 (by rfl) ⟨546161, by rfl⟩ : syracuseStep 2912861 = 1092323) (by norm_num)
theorem B2183861 : Blo 1725063 2183861 := bbase (se 5 (by rfl) ⟨102368, by rfl⟩ : syracuseStep 2183861 = 204737) (by norm_num)
theorem B2912989 : Blo 1725063 2912989 := bbase (se 3 (by rfl) ⟨546185, by rfl⟩ : syracuseStep 2912989 = 1092371) (by norm_num)
theorem B2183917 : Blo 1725063 2183917 := bbase (se 3 (by rfl) ⟨409484, by rfl⟩ : syracuseStep 2183917 = 818969) (by norm_num)
theorem B4371205 : Blo 1725063 4371205 := bbase (se 4 (by rfl) ⟨409800, by rfl⟩ : syracuseStep 4371205 = 819601) (by norm_num)
theorem B35517205 : Blo 1725063 35517205 := bbase (se 6 (by rfl) ⟨832434, by rfl⟩ : syracuseStep 35517205 = 1664869) (by norm_num)
theorem B2913077 : Blo 1725063 2913077 := bbase (se 5 (by rfl) ⟨136550, by rfl⟩ : syracuseStep 2913077 = 273101) (by norm_num)
theorem B2184013 : Blo 1725063 2184013 := bbase (se 3 (by rfl) ⟨409502, by rfl⟩ : syracuseStep 2184013 = 819005) (by norm_num)
theorem B4371317 : Blo 1725063 4371317 := bbase (se 5 (by rfl) ⟨204905, by rfl⟩ : syracuseStep 4371317 = 409811) (by norm_num)
theorem B2913205 : Blo 1725063 2913205 := bbase (se 5 (by rfl) ⟨136556, by rfl⟩ : syracuseStep 2913205 = 273113) (by norm_num)
theorem B2184185 : Blo 1725063 2184185 := bbase (se 2 (by rfl) ⟨819069, by rfl⟩ : syracuseStep 2184185 = 1638139) (by norm_num)
theorem B2765821 : Blo 1725063 2765821 := bbase (se 3 (by rfl) ⟨518591, by rfl⟩ : syracuseStep 2765821 = 1037183) (by norm_num)
theorem B2913293 : Blo 1725063 2913293 := bbase (se 3 (by rfl) ⟨546242, by rfl⟩ : syracuseStep 2913293 = 1092485) (by norm_num)
theorem B2102317 : Blo 1725063 2102317 := bbase (se 3 (by rfl) ⟨394184, by rfl⟩ : syracuseStep 2102317 = 788369) (by norm_num)
theorem B2184241 : Blo 1725063 2184241 := bbase (se 2 (by rfl) ⟨819090, by rfl⟩ : syracuseStep 2184241 = 1638181) (by norm_num)
theorem B4371509 : Blo 1725063 4371509 := bbase (se 5 (by rfl) ⟨204914, by rfl⟩ : syracuseStep 4371509 = 409829) (by norm_num)
theorem B2765917 : Blo 1725063 2765917 := bbase (se 3 (by rfl) ⟨518609, by rfl⟩ : syracuseStep 2765917 = 1037219) (by norm_num)
theorem B1750133 : Blo 1725063 1750133 := bbase (se 5 (by rfl) ⟨82037, by rfl⟩ : syracuseStep 1750133 = 164075) (by norm_num)
theorem B3413125 : Blo 1725063 3413125 := bbase (se 4 (by rfl) ⟨319980, by rfl⟩ : syracuseStep 3413125 = 639961) (by norm_num)
theorem B2913421 : Blo 1725063 2913421 := bbase (se 3 (by rfl) ⟨546266, by rfl⟩ : syracuseStep 2913421 = 1092533) (by norm_num)
theorem B2184337 : Blo 1725063 2184337 := bbase (se 2 (by rfl) ⟨819126, by rfl⟩ : syracuseStep 2184337 = 1638253) (by norm_num)
theorem B2913509 : Blo 1725063 2913509 := bbase (se 4 (by rfl) ⟨273141, by rfl⟩ : syracuseStep 2913509 = 546283) (by norm_num)
theorem B2766077 : Blo 1725063 2766077 := bbase (se 3 (by rfl) ⟨518639, by rfl⟩ : syracuseStep 2766077 = 1037279) (by norm_num)
theorem B3110165 : Blo 1725063 3110165 := bbase (se 6 (by rfl) ⟨72894, by rfl⟩ : syracuseStep 3110165 = 145789) (by norm_num)
theorem B9835829 : Blo 1725063 9835829 := bbase (se 5 (by rfl) ⟨461054, by rfl⟩ : syracuseStep 9835829 = 922109) (by norm_num)
theorem B2184509 : Blo 1725063 2184509 := bbase (se 3 (by rfl) ⟨409595, by rfl⟩ : syracuseStep 2184509 = 819191) (by norm_num)
theorem B8738117 : Blo 1725063 8738117 := bbase (se 4 (by rfl) ⟨819198, by rfl⟩ : syracuseStep 8738117 = 1638397) (by norm_num)
theorem B5051717 : Blo 1725063 5051717 := bbase (se 4 (by rfl) ⟨473598, by rfl⟩ : syracuseStep 5051717 = 947197) (by norm_num)
theorem B1552389461 : Blo 1725063 1552389461 := bbase (se 14 (by rfl) ⟨142125, by rfl⟩ : syracuseStep 1552389461 = 284251) (by norm_num)
theorem B4666709 : Blo 1725063 4666709 := bbase (se 13 (by rfl) ⟨854, by rfl⟩ : syracuseStep 4666709 = 1709) (by norm_num)
theorem B2913637 : Blo 1725063 2913637 := bbase (se 4 (by rfl) ⟨273153, by rfl⟩ : syracuseStep 2913637 = 546307) (by norm_num)
theorem B6550901 : Blo 1725063 6550901 := bbase (se 5 (by rfl) ⟨307073, by rfl⟩ : syracuseStep 6550901 = 614147) (by norm_num)
theorem B2839925 : Blo 1725063 2839925 := bbase (se 5 (by rfl) ⟨133121, by rfl⟩ : syracuseStep 2839925 = 266243) (by norm_num)
theorem B2184565 : Blo 1725063 2184565 := bbase (se 5 (by rfl) ⟨102401, by rfl⟩ : syracuseStep 2184565 = 204803) (by norm_num)
theorem B4666805 : Blo 1725063 4666805 := bbase (se 5 (by rfl) ⟨218756, by rfl⟩ : syracuseStep 4666805 = 437513) (by norm_num)
theorem B2913725 : Blo 1725063 2913725 := bbase (se 3 (by rfl) ⟨546323, by rfl⟩ : syracuseStep 2913725 = 1092647) (by norm_num)
theorem B2184661 : Blo 1725063 2184661 := bbase (se 7 (by rfl) ⟨25601, by rfl⟩ : syracuseStep 2184661 = 51203) (by norm_num)
theorem B3937781 : Blo 1725063 3937781 := bbase (se 5 (by rfl) ⟨184583, by rfl⟩ : syracuseStep 3937781 = 369167) (by norm_num)
theorem B2913853 : Blo 1725063 2913853 := bbase (se 3 (by rfl) ⟨546347, by rfl⟩ : syracuseStep 2913853 = 1092695) (by norm_num)
theorem B2184833 : Blo 1725063 2184833 := bbase (se 2 (by rfl) ⟨819312, by rfl⟩ : syracuseStep 2184833 = 1638625) (by norm_num)
theorem B6551189 : Blo 1725063 6551189 := bbase (se 6 (by rfl) ⟨153543, by rfl⟩ : syracuseStep 6551189 = 307087) (by norm_num)
theorem B2913941 : Blo 1725063 2913941 := bbase (se 6 (by rfl) ⟨68295, by rfl⟩ : syracuseStep 2913941 = 136591) (by norm_num)
theorem B5822117 : Blo 1725063 5822117 := bbase (se 4 (by rfl) ⟨545823, by rfl⟩ : syracuseStep 5822117 = 1091647) (by norm_num)
theorem B2184889 : Blo 1725063 2184889 := bbase (se 2 (by rfl) ⟨819333, by rfl⟩ : syracuseStep 2184889 = 1638667) (by norm_num)
theorem B27997973 : Blo 1725063 27997973 := bbase (se 6 (by rfl) ⟨656202, by rfl⟩ : syracuseStep 27997973 = 1312405) (by norm_num)
theorem B2914069 : Blo 1725063 2914069 := bbase (se 6 (by rfl) ⟨68298, by rfl⟩ : syracuseStep 2914069 = 136597) (by norm_num)
theorem B2184985 : Blo 1725063 2184985 := bbase (se 2 (by rfl) ⟨819369, by rfl⟩ : syracuseStep 2184985 = 1638739) (by norm_num)
theorem B2914157 : Blo 1725063 2914157 := bbase (se 3 (by rfl) ⟨546404, by rfl⟩ : syracuseStep 2914157 = 1092809) (by norm_num)
theorem B2185157 : Blo 1725063 2185157 := bbase (se 4 (by rfl) ⟨204858, by rfl⟩ : syracuseStep 2185157 = 409717) (by norm_num)
theorem B2914285 : Blo 1725063 2914285 := bbase (se 3 (by rfl) ⟨546428, by rfl⟩ : syracuseStep 2914285 = 1092857) (by norm_num)
theorem B5527541 : Blo 1725063 5527541 := bbase (se 5 (by rfl) ⟨259103, by rfl⟩ : syracuseStep 5527541 = 518207) (by norm_num)
theorem B2185213 : Blo 1725063 2185213 := bbase (se 3 (by rfl) ⟨409727, by rfl⟩ : syracuseStep 2185213 = 819455) (by norm_num)
theorem B8411141 : Blo 1725063 8411141 := bbase (se 4 (by rfl) ⟨788544, by rfl⟩ : syracuseStep 8411141 = 1577089) (by norm_num)
theorem B2914373 : Blo 1725063 2914373 := bbase (se 4 (by rfl) ⟨273222, by rfl⟩ : syracuseStep 2914373 = 546445) (by norm_num)
theorem B5822549 : Blo 1725063 5822549 := bbase (se 8 (by rfl) ⟨34116, by rfl⟩ : syracuseStep 5822549 = 68233) (by norm_num)
theorem B2185309 : Blo 1725063 2185309 := bbase (se 3 (by rfl) ⟨409745, by rfl⟩ : syracuseStep 2185309 = 819491) (by norm_num)
theorem B3684541 : Blo 1725063 3684541 := bbase (se 3 (by rfl) ⟨690851, by rfl⟩ : syracuseStep 3684541 = 1381703) (by norm_num)
theorem B2185481 : Blo 1725063 2185481 := bbase (se 2 (by rfl) ⟨819555, by rfl⟩ : syracuseStep 2185481 = 1639111) (by norm_num)
theorem B2185537 : Blo 1725063 2185537 := bbase (se 2 (by rfl) ⟨819576, by rfl⟩ : syracuseStep 2185537 = 1639153) (by norm_num)
theorem B3684685 : Blo 1725063 3684685 := bbase (se 3 (by rfl) ⟨690878, by rfl⟩ : syracuseStep 3684685 = 1381757) (by norm_num)
theorem B3275093 : Blo 1725063 3275093 := bbase (se 10 (by rfl) ⟨4797, by rfl⟩ : syracuseStep 3275093 = 9595) (by norm_num)
theorem B3594653 : Blo 1725063 3594653 := bbase (se 3 (by rfl) ⟨673997, by rfl⟩ : syracuseStep 3594653 = 1347995) (by norm_num)
theorem B2185633 : Blo 1725063 2185633 := bbase (se 2 (by rfl) ⟨819612, by rfl⟩ : syracuseStep 2185633 = 1639225) (by norm_num)
theorem B6224309 : Blo 1725063 6224309 := bbase (se 5 (by rfl) ⟨291764, by rfl⟩ : syracuseStep 6224309 = 583529) (by norm_num)
theorem B3881429 : Blo 1725063 3881429 := bbase (se 7 (by rfl) ⟨45485, by rfl⟩ : syracuseStep 3881429 = 90971) (by norm_num)
theorem B3275245 : Blo 1725063 3275245 := bbase (se 3 (by rfl) ⟨614108, by rfl⟩ : syracuseStep 3275245 = 1228217) (by norm_num)
theorem B5822981 : Blo 1725063 5822981 := bbase (se 4 (by rfl) ⟨545904, by rfl⟩ : syracuseStep 5822981 = 1091809) (by norm_num)
theorem B7371269 : Blo 1725063 7371269 := bbase (se 4 (by rfl) ⟨691056, by rfl⟩ : syracuseStep 7371269 = 1382113) (by norm_num)
theorem B3881501 : Blo 1725063 3881501 := bbase (se 3 (by rfl) ⟨727781, by rfl⟩ : syracuseStep 3881501 = 1455563) (by norm_num)
theorem B2185805 : Blo 1725063 2185805 := bbase (se 3 (by rfl) ⟨409838, by rfl⟩ : syracuseStep 2185805 = 819677) (by norm_num)
theorem B8739413 : Blo 1725063 8739413 := bbase (se 8 (by rfl) ⟨51207, by rfl⟩ : syracuseStep 8739413 = 102415) (by norm_num)
theorem B3881573 : Blo 1725063 3881573 := bbase (se 4 (by rfl) ⟨363897, by rfl⟩ : syracuseStep 3881573 = 727795) (by norm_num)
theorem B3881645 : Blo 1725063 3881645 := bbase (se 3 (by rfl) ⟨727808, by rfl⟩ : syracuseStep 3881645 = 1455617) (by norm_num)
theorem B3685061 : Blo 1725063 3685061 := bbase (se 4 (by rfl) ⟨345474, by rfl⟩ : syracuseStep 3685061 = 690949) (by norm_num)
theorem B3881717 : Blo 1725063 3881717 := bbase (se 5 (by rfl) ⟨181955, by rfl⟩ : syracuseStep 3881717 = 363911) (by norm_num)
theorem B3275549 : Blo 1725063 3275549 := bbase (se 3 (by rfl) ⟨614165, by rfl⟩ : syracuseStep 3275549 = 1228331) (by norm_num)
theorem B7371557 : Blo 1725063 7371557 := bbase (se 4 (by rfl) ⟨691083, by rfl⟩ : syracuseStep 7371557 = 1382167) (by norm_num)
theorem B6552373 : Blo 1725063 6552373 := bbase (se 5 (by rfl) ⟨307142, by rfl⟩ : syracuseStep 6552373 = 614285) (by norm_num)
theorem B3881789 : Blo 1725063 3881789 := bbase (se 3 (by rfl) ⟨727835, by rfl⟩ : syracuseStep 3881789 = 1455671) (by norm_num)
theorem B3881861 : Blo 1725063 3881861 := bbase (se 4 (by rfl) ⟨363924, by rfl⟩ : syracuseStep 3881861 = 727849) (by norm_num)
theorem B4914053 : Blo 1725063 4914053 := bbase (se 4 (by rfl) ⟨460692, by rfl⟩ : syracuseStep 4914053 = 921385) (by norm_num)
theorem B5823413 : Blo 1725063 5823413 := bbase (se 5 (by rfl) ⟨272972, by rfl⟩ : syracuseStep 5823413 = 545945) (by norm_num)
theorem B6994885 : Blo 1725063 6994885 := bbase (se 4 (by rfl) ⟨655770, by rfl⟩ : syracuseStep 6994885 = 1311541) (by norm_num)
theorem B2456525 : Blo 1725063 2456525 := bbase (se 3 (by rfl) ⟨460598, by rfl⟩ : syracuseStep 2456525 = 921197) (by norm_num)
theorem B3881933 : Blo 1725063 3881933 := bbase (se 3 (by rfl) ⟨727862, by rfl⟩ : syracuseStep 3881933 = 1455725) (by norm_num)
theorem B54631381 : Blo 1725063 54631381 := bbase (se 7 (by rfl) ⟨640211, by rfl⟩ : syracuseStep 54631381 = 1280423) (by norm_num)
theorem B2587613 : Blo 1725063 2587613 := bbase (se 3 (by rfl) ⟨485177, by rfl⟩ : syracuseStep 2587613 = 970355) (by norm_num)
theorem B2587637 : Blo 1725063 2587637 := bbase (se 5 (by rfl) ⟨121295, by rfl⟩ : syracuseStep 2587637 = 242591) (by norm_num)
theorem B2587661 : Blo 1725063 2587661 := bbase (se 3 (by rfl) ⟨485186, by rfl⟩ : syracuseStep 2587661 = 970373) (by norm_num)
theorem B3882005 : Blo 1725063 3882005 := bbase (se 6 (by rfl) ⟨90984, by rfl⟩ : syracuseStep 3882005 = 181969) (by norm_num)
theorem B2456605 : Blo 1725063 2456605 := bbase (se 3 (by rfl) ⟨460613, by rfl⟩ : syracuseStep 2456605 = 921227) (by norm_num)
theorem B2587685 : Blo 1725063 2587685 := bbase (se 4 (by rfl) ⟨242595, by rfl⟩ : syracuseStep 2587685 = 485191) (by norm_num)
theorem B3685429 : Blo 1725063 3685429 := bbase (se 5 (by rfl) ⟨172754, by rfl⟩ : syracuseStep 3685429 = 345509) (by norm_num)
theorem B2587709 : Blo 1725063 2587709 := bbase (se 3 (by rfl) ⟨485195, by rfl⟩ : syracuseStep 2587709 = 970391) (by norm_num)
theorem B2587733 : Blo 1725063 2587733 := bbase (se 8 (by rfl) ⟨15162, by rfl⟩ : syracuseStep 2587733 = 30325) (by norm_num)
theorem B3882077 : Blo 1725063 3882077 := bbase (se 3 (by rfl) ⟨727889, by rfl⟩ : syracuseStep 3882077 = 1455779) (by norm_num)
theorem B6552677 : Blo 1725063 6552677 := bbase (se 4 (by rfl) ⟨614313, by rfl⟩ : syracuseStep 6552677 = 1228627) (by norm_num)
theorem B2587757 : Blo 1725063 2587757 := bbase (se 3 (by rfl) ⟨485204, by rfl⟩ : syracuseStep 2587757 = 970409) (by norm_num)
theorem B2587781 : Blo 1725063 2587781 := bbase (se 4 (by rfl) ⟨242604, by rfl⟩ : syracuseStep 2587781 = 485209) (by norm_num)
theorem B2456725 : Blo 1725063 2456725 := bbase (se 6 (by rfl) ⟨57579, by rfl⟩ : syracuseStep 2456725 = 115159) (by norm_num)
theorem B2587805 : Blo 1725063 2587805 := bbase (se 3 (by rfl) ⟨485213, by rfl⟩ : syracuseStep 2587805 = 970427) (by norm_num)
theorem B3882149 : Blo 1725063 3882149 := bbase (se 4 (by rfl) ⟨363951, by rfl⟩ : syracuseStep 3882149 = 727903) (by norm_num)
theorem B2587829 : Blo 1725063 2587829 := bbase (se 5 (by rfl) ⟨121304, by rfl⟩ : syracuseStep 2587829 = 242609) (by norm_num)
theorem B9329845 : Blo 1725063 9329845 := bbase (se 5 (by rfl) ⟨437336, by rfl⟩ : syracuseStep 9329845 = 874673) (by norm_num)
theorem B1842373 : Blo 1725063 1842373 := bbase (se 4 (by rfl) ⟨172722, by rfl⟩ : syracuseStep 1842373 = 345445) (by norm_num)
theorem B2587853 : Blo 1725063 2587853 := bbase (se 3 (by rfl) ⟨485222, by rfl⟩ : syracuseStep 2587853 = 970445) (by norm_num)
theorem B3366101 : Blo 1725063 3366101 := bbase (se 7 (by rfl) ⟨39446, by rfl⟩ : syracuseStep 3366101 = 78893) (by norm_num)
theorem B1940701 : Blo 1725063 1940701 := bbase (se 3 (by rfl) ⟨363881, by rfl⟩ : syracuseStep 1940701 = 727763) (by norm_num)
theorem B2587877 : Blo 1725063 2587877 := bbase (se 4 (by rfl) ⟨242613, by rfl⟩ : syracuseStep 2587877 = 485227) (by norm_num)
theorem B3882221 : Blo 1725063 3882221 := bbase (se 3 (by rfl) ⟨727916, by rfl⟩ : syracuseStep 3882221 = 1455833) (by norm_num)
theorem B2456821 : Blo 1725063 2456821 := bbase (se 5 (by rfl) ⟨115163, by rfl⟩ : syracuseStep 2456821 = 230327) (by norm_num)
theorem B2587901 : Blo 1725063 2587901 := bbase (se 3 (by rfl) ⟨485231, by rfl⟩ : syracuseStep 2587901 = 970463) (by norm_num)
theorem B1940737 : Blo 1725063 1940737 := bbase (se 2 (by rfl) ⟨727776, by rfl⟩ : syracuseStep 1940737 = 1455553) (by norm_num)
theorem B1842445 : Blo 1725063 1842445 := bbase (se 3 (by rfl) ⟨345458, by rfl⟩ : syracuseStep 1842445 = 690917) (by norm_num)
theorem B2587925 : Blo 1725063 2587925 := bbase (se 6 (by rfl) ⟨60654, by rfl⟩ : syracuseStep 2587925 = 121309) (by norm_num)
theorem B1940773 : Blo 1725063 1940773 := bbase (se 4 (by rfl) ⟨181947, by rfl⟩ : syracuseStep 1940773 = 363895) (by norm_num)
theorem B2587949 : Blo 1725063 2587949 := bbase (se 3 (by rfl) ⟨485240, by rfl⟩ : syracuseStep 2587949 = 970481) (by norm_num)
theorem B14941493 : Blo 1725063 14941493 := bbase (se 5 (by rfl) ⟨700382, by rfl⟩ : syracuseStep 14941493 = 1400765) (by norm_num)
theorem B3882293 : Blo 1725063 3882293 := bbase (se 5 (by rfl) ⟨181982, by rfl⟩ : syracuseStep 3882293 = 363965) (by norm_num)
theorem B2587973 : Blo 1725063 2587973 := bbase (se 4 (by rfl) ⟨242622, by rfl⟩ : syracuseStep 2587973 = 485245) (by norm_num)
theorem B1940809 : Blo 1725063 1940809 := bbase (se 2 (by rfl) ⟨727803, by rfl⟩ : syracuseStep 1940809 = 1455607) (by norm_num)
theorem B2334029 : Blo 1725063 2334029 := bbase (se 3 (by rfl) ⟨437630, by rfl⟩ : syracuseStep 2334029 = 875261) (by norm_num)
theorem B13114709 : Blo 1725063 13114709 := bbase (se 11 (by rfl) ⟨9605, by rfl⟩ : syracuseStep 13114709 = 19211) (by norm_num)
theorem B2587997 : Blo 1725063 2587997 := bbase (se 3 (by rfl) ⟨485249, by rfl⟩ : syracuseStep 2587997 = 970499) (by norm_num)
theorem B5823845 : Blo 1725063 5823845 := bbase (se 4 (by rfl) ⟨545985, by rfl⟩ : syracuseStep 5823845 = 1091971) (by norm_num)
theorem B1940845 : Blo 1725063 1940845 := bbase (se 3 (by rfl) ⟨363908, by rfl⟩ : syracuseStep 1940845 = 727817) (by norm_num)
theorem B2588021 : Blo 1725063 2588021 := bbase (se 5 (by rfl) ⟨121313, by rfl⟩ : syracuseStep 2588021 = 242627) (by norm_num)
theorem B3882365 : Blo 1725063 3882365 := bbase (se 3 (by rfl) ⟨727943, by rfl⟩ : syracuseStep 3882365 = 1455887) (by norm_num)
theorem B2588045 : Blo 1725063 2588045 := bbase (se 3 (by rfl) ⟨485258, by rfl⟩ : syracuseStep 2588045 = 970517) (by norm_num)
theorem B1940881 : Blo 1725063 1940881 := bbase (se 2 (by rfl) ⟨727830, by rfl⟩ : syracuseStep 1940881 = 1455661) (by norm_num)
theorem B2588069 : Blo 1725063 2588069 := bbase (se 4 (by rfl) ⟨242631, by rfl⟩ : syracuseStep 2588069 = 485263) (by norm_num)
theorem B3546541 : Blo 1725063 3546541 := bbase (se 3 (by rfl) ⟨664976, by rfl⟩ : syracuseStep 3546541 = 1329953) (by norm_num)
theorem B1940917 : Blo 1725063 1940917 := bbase (se 5 (by rfl) ⟨90980, by rfl⟩ : syracuseStep 1940917 = 181961) (by norm_num)
theorem B2588093 : Blo 1725063 2588093 := bbase (se 3 (by rfl) ⟨485267, by rfl⟩ : syracuseStep 2588093 = 970535) (by norm_num)
theorem B1842625 : Blo 1725063 1842625 := bbase (se 2 (by rfl) ⟨690984, by rfl⟩ : syracuseStep 1842625 = 1381969) (by norm_num)
theorem B3882437 : Blo 1725063 3882437 := bbase (se 4 (by rfl) ⟨363978, by rfl⟩ : syracuseStep 3882437 = 727957) (by norm_num)
theorem B2588117 : Blo 1725063 2588117 := bbase (se 7 (by rfl) ⟨30329, by rfl⟩ : syracuseStep 2588117 = 60659) (by norm_num)
theorem B1940953 : Blo 1725063 1940953 := bbase (se 2 (by rfl) ⟨727857, by rfl⟩ : syracuseStep 1940953 = 1455715) (by norm_num)
theorem B2588141 : Blo 1725063 2588141 := bbase (se 3 (by rfl) ⟨485276, by rfl⟩ : syracuseStep 2588141 = 970553) (by norm_num)
theorem B1940989 : Blo 1725063 1940989 := bbase (se 3 (by rfl) ⟨363935, by rfl⟩ : syracuseStep 1940989 = 727871) (by norm_num)
theorem B2588165 : Blo 1725063 2588165 := bbase (se 4 (by rfl) ⟨242640, by rfl⟩ : syracuseStep 2588165 = 485281) (by norm_num)
theorem B3882509 : Blo 1725063 3882509 := bbase (se 3 (by rfl) ⟨727970, by rfl⟩ : syracuseStep 3882509 = 1455941) (by norm_num)
theorem B3276301 : Blo 1725063 3276301 := bbase (se 3 (by rfl) ⟨614306, by rfl⟩ : syracuseStep 3276301 = 1228613) (by norm_num)
theorem B7372309 : Blo 1725063 7372309 := bbase (se 6 (by rfl) ⟨172788, by rfl⟩ : syracuseStep 7372309 = 345577) (by norm_num)
theorem B3497501 : Blo 1725063 3497501 := bbase (se 3 (by rfl) ⟨655781, by rfl⟩ : syracuseStep 3497501 = 1311563) (by norm_num)
theorem B2588189 : Blo 1725063 2588189 := bbase (se 3 (by rfl) ⟨485285, by rfl⟩ : syracuseStep 2588189 = 970571) (by norm_num)
theorem B1941025 : Blo 1725063 1941025 := bbase (se 2 (by rfl) ⟨727884, by rfl⟩ : syracuseStep 1941025 = 1455769) (by norm_num)
theorem B3497509 : Blo 1725063 3497509 := bbase (se 4 (by rfl) ⟨327891, by rfl⟩ : syracuseStep 3497509 = 655783) (by norm_num)
theorem B2588213 : Blo 1725063 2588213 := bbase (se 5 (by rfl) ⟨121322, by rfl⟩ : syracuseStep 2588213 = 242645) (by norm_num)
theorem B1941061 : Blo 1725063 1941061 := bbase (se 4 (by rfl) ⟨181974, by rfl⟩ : syracuseStep 1941061 = 363949) (by norm_num)
theorem B2588237 : Blo 1725063 2588237 := bbase (se 3 (by rfl) ⟨485294, by rfl⟩ : syracuseStep 2588237 = 970589) (by norm_num)
theorem B3882581 : Blo 1725063 3882581 := bbase (se 8 (by rfl) ⟨22749, by rfl⟩ : syracuseStep 3882581 = 45499) (by norm_num)
theorem B2588261 : Blo 1725063 2588261 := bbase (se 4 (by rfl) ⟨242649, by rfl⟩ : syracuseStep 2588261 = 485299) (by norm_num)
theorem B1941097 : Blo 1725063 1941097 := bbase (se 2 (by rfl) ⟨727911, by rfl⟩ : syracuseStep 1941097 = 1455823) (by norm_num)
theorem B2588285 : Blo 1725063 2588285 := bbase (se 3 (by rfl) ⟨485303, by rfl⟩ : syracuseStep 2588285 = 970607) (by norm_num)
theorem B1941133 : Blo 1725063 1941133 := bbase (se 3 (by rfl) ⟨363962, by rfl⟩ : syracuseStep 1941133 = 727925) (by norm_num)
theorem B2588309 : Blo 1725063 2588309 := bbase (se 6 (by rfl) ⟨60663, by rfl⟩ : syracuseStep 2588309 = 121327) (by norm_num)
theorem B3882653 : Blo 1725063 3882653 := bbase (se 3 (by rfl) ⟨727997, by rfl⟩ : syracuseStep 3882653 = 1455995) (by norm_num)
theorem B3276445 : Blo 1725063 3276445 := bbase (se 3 (by rfl) ⟨614333, by rfl⟩ : syracuseStep 3276445 = 1228667) (by norm_num)
theorem B2588333 : Blo 1725063 2588333 := bbase (se 3 (by rfl) ⟨485312, by rfl⟩ : syracuseStep 2588333 = 970625) (by norm_num)
theorem B1941169 : Blo 1725063 1941169 := bbase (se 2 (by rfl) ⟨727938, by rfl⟩ : syracuseStep 1941169 = 1455877) (by norm_num)
theorem B2588357 : Blo 1725063 2588357 := bbase (se 4 (by rfl) ⟨242658, by rfl⟩ : syracuseStep 2588357 = 485317) (by norm_num)
theorem B1941205 : Blo 1725063 1941205 := bbase (se 7 (by rfl) ⟨22748, by rfl⟩ : syracuseStep 1941205 = 45497) (by norm_num)
theorem B2588381 : Blo 1725063 2588381 := bbase (se 3 (by rfl) ⟨485321, by rfl⟩ : syracuseStep 2588381 = 970643) (by norm_num)
theorem B6217445 : Blo 1725063 6217445 := bbase (se 4 (by rfl) ⟨582885, by rfl⟩ : syracuseStep 6217445 = 1165771) (by norm_num)
theorem B3882725 : Blo 1725063 3882725 := bbase (se 4 (by rfl) ⟨364005, by rfl⟩ : syracuseStep 3882725 = 728011) (by norm_num)
theorem B2457317 : Blo 1725063 2457317 := bbase (se 4 (by rfl) ⟨230373, by rfl⟩ : syracuseStep 2457317 = 460747) (by norm_num)
theorem B2588405 : Blo 1725063 2588405 := bbase (se 5 (by rfl) ⟨121331, by rfl⟩ : syracuseStep 2588405 = 242663) (by norm_num)
theorem B13106933 : Blo 1725063 13106933 := bbase (se 5 (by rfl) ⟨614387, by rfl⟩ : syracuseStep 13106933 = 1228775) (by norm_num)
theorem B1941241 : Blo 1725063 1941241 := bbase (se 2 (by rfl) ⟨727965, by rfl⟩ : syracuseStep 1941241 = 1455931) (by norm_num)
theorem B2588429 : Blo 1725063 2588429 := bbase (se 3 (by rfl) ⟨485330, by rfl⟩ : syracuseStep 2588429 = 970661) (by norm_num)
theorem B5824277 : Blo 1725063 5824277 := bbase (se 6 (by rfl) ⟨136506, by rfl⟩ : syracuseStep 5824277 = 273013) (by norm_num)
theorem B1941277 : Blo 1725063 1941277 := bbase (se 3 (by rfl) ⟨363989, by rfl⟩ : syracuseStep 1941277 = 727979) (by norm_num)
theorem B2588453 : Blo 1725063 2588453 := bbase (se 4 (by rfl) ⟨242667, by rfl⟩ : syracuseStep 2588453 = 485335) (by norm_num)
theorem B3882797 : Blo 1725063 3882797 := bbase (se 3 (by rfl) ⟨728024, by rfl⟩ : syracuseStep 3882797 = 1456049) (by norm_num)
theorem B2588477 : Blo 1725063 2588477 := bbase (se 3 (by rfl) ⟨485339, by rfl⟩ : syracuseStep 2588477 = 970679) (by norm_num)
theorem B3276605 : Blo 1725063 3276605 := bbase (se 3 (by rfl) ⟨614363, by rfl⟩ : syracuseStep 3276605 = 1228727) (by norm_num)
theorem B1941313 : Blo 1725063 1941313 := bbase (se 2 (by rfl) ⟨727992, by rfl⟩ : syracuseStep 1941313 = 1455985) (by norm_num)
theorem B2588501 : Blo 1725063 2588501 := bbase (se 9 (by rfl) ⟨7583, by rfl⟩ : syracuseStep 2588501 = 15167) (by norm_num)
theorem B1941349 : Blo 1725063 1941349 := bbase (se 4 (by rfl) ⟨182001, by rfl⟩ : syracuseStep 1941349 = 364003) (by norm_num)
theorem B8740709 : Blo 1725063 8740709 := bbase (se 4 (by rfl) ⟨819441, by rfl⟩ : syracuseStep 8740709 = 1638883) (by norm_num)
theorem B2588525 : Blo 1725063 2588525 := bbase (se 3 (by rfl) ⟨485348, by rfl⟩ : syracuseStep 2588525 = 970697) (by norm_num)
theorem B3882869 : Blo 1725063 3882869 := bbase (se 5 (by rfl) ⟨182009, by rfl⟩ : syracuseStep 3882869 = 364019) (by norm_num)
theorem B1843069 : Blo 1725063 1843069 := bbase (se 3 (by rfl) ⟨345575, by rfl⟩ : syracuseStep 1843069 = 691151) (by norm_num)
theorem B2588549 : Blo 1725063 2588549 := bbase (se 4 (by rfl) ⟨242676, by rfl⟩ : syracuseStep 2588549 = 485353) (by norm_num)
theorem B1941385 : Blo 1725063 1941385 := bbase (se 2 (by rfl) ⟨728019, by rfl⟩ : syracuseStep 1941385 = 1456039) (by norm_num)
theorem B2588573 : Blo 1725063 2588573 := bbase (se 3 (by rfl) ⟨485357, by rfl⟩ : syracuseStep 2588573 = 970715) (by norm_num)
theorem B1941421 : Blo 1725063 1941421 := bbase (se 3 (by rfl) ⟨364016, by rfl⟩ : syracuseStep 1941421 = 728033) (by norm_num)
theorem B2588597 : Blo 1725063 2588597 := bbase (se 5 (by rfl) ⟨121340, by rfl⟩ : syracuseStep 2588597 = 242681) (by norm_num)
theorem B3882941 : Blo 1725063 3882941 := bbase (se 3 (by rfl) ⟨728051, by rfl⟩ : syracuseStep 3882941 = 1456103) (by norm_num)
theorem B2588621 : Blo 1725063 2588621 := bbase (se 3 (by rfl) ⟨485366, by rfl⟩ : syracuseStep 2588621 = 970733) (by norm_num)
theorem B3276749 : Blo 1725063 3276749 := bbase (se 3 (by rfl) ⟨614390, by rfl⟩ : syracuseStep 3276749 = 1228781) (by norm_num)
theorem B1941457 : Blo 1725063 1941457 := bbase (se 2 (by rfl) ⟨728046, by rfl⟩ : syracuseStep 1941457 = 1456093) (by norm_num)
theorem B2588645 : Blo 1725063 2588645 := bbase (se 4 (by rfl) ⟨242685, by rfl⟩ : syracuseStep 2588645 = 485371) (by norm_num)
theorem B1941493 : Blo 1725063 1941493 := bbase (se 5 (by rfl) ⟨91007, by rfl⟩ : syracuseStep 1941493 = 182015) (by norm_num)
theorem B1843193 : Blo 1725063 1843193 := bbase (se 2 (by rfl) ⟨691197, by rfl⟩ : syracuseStep 1843193 = 1382395) (by norm_num)
theorem B2588669 : Blo 1725063 2588669 := bbase (se 3 (by rfl) ⟨485375, by rfl⟩ : syracuseStep 2588669 = 970751) (by norm_num)
theorem B2588675 : Blo 1725063 2588675 := bstep (se 1 (by rfl) ⟨1941506, by rfl⟩ : syracuseStep 2588675 = 3883013) B3883013
theorem B5529617 : Blo 1725063 5529617 := bstep (se 2 (by rfl) ⟨2073606, by rfl⟩ : syracuseStep 5529617 = 4147213) B4147213
theorem B2588705 : Blo 1725063 2588705 := bstep (se 2 (by rfl) ⟨970764, by rfl⟩ : syracuseStep 2588705 = 1941529) B1941529
theorem B5824547 : Blo 1725063 5824547 := bstep (se 1 (by rfl) ⟨4368410, by rfl⟩ : syracuseStep 5824547 = 8736821) B8736821
theorem B6553649 : Blo 1725063 6553649 := bstep (se 2 (by rfl) ⟨2457618, by rfl⟩ : syracuseStep 6553649 = 4915237) B4915237
theorem B2588723 : Blo 1725063 2588723 := bstep (se 1 (by rfl) ⟨1941542, by rfl⟩ : syracuseStep 2588723 = 3883085) B3883085
theorem B2490433 : Blo 1725063 2490433 := bstep (se 2 (by rfl) ⟨933912, by rfl⟩ : syracuseStep 2490433 = 1867825) B1867825
theorem B2588753 : Blo 1725063 2588753 := bstep (se 2 (by rfl) ⟨970782, by rfl⟩ : syracuseStep 2588753 = 1941565) B1941565
theorem B2588771 : Blo 1725063 2588771 := bstep (se 1 (by rfl) ⟨1941578, by rfl⟩ : syracuseStep 2588771 = 3883157) B3883157
theorem B3883121 : Blo 1725063 3883121 := bstep (se 2 (by rfl) ⟨1456170, by rfl⟩ : syracuseStep 3883121 = 2912341) B2912341
theorem B1941619 : Blo 1725063 1941619 := bstep (se 1 (by rfl) ⟨1456214, by rfl⟩ : syracuseStep 1941619 = 2912429) B2912429
theorem B2588801 : Blo 1725063 2588801 := bstep (se 2 (by rfl) ⟨970800, by rfl⟩ : syracuseStep 2588801 = 1941601) B1941601
theorem B3883139 : Blo 1725063 3883139 := bstep (se 1 (by rfl) ⟨2912354, by rfl⟩ : syracuseStep 3883139 = 5824709) B5824709
theorem B3276931 : Blo 1725063 3276931 := bstep (se 1 (by rfl) ⟨2457698, by rfl⟩ : syracuseStep 3276931 = 4915397) B4915397
theorem B9330821 : Blo 1725063 9330821 := bstep (se 4 (by rfl) ⟨874764, by rfl⟩ : syracuseStep 9330821 = 1749529) B1749529
theorem B13992077 : Blo 1725063 13992077 := bstep (se 3 (by rfl) ⟨2623514, by rfl⟩ : syracuseStep 13992077 = 5247029) B5247029
theorem B2588819 : Blo 1725063 2588819 := bstep (se 1 (by rfl) ⟨1941614, by rfl⟩ : syracuseStep 2588819 = 3883229) B3883229
theorem B4915363 : Blo 1725063 4915363 := bstep (se 1 (by rfl) ⟨3686522, by rfl⟩ : syracuseStep 4915363 = 7373045) B7373045
theorem B2588849 : Blo 1725063 2588849 := bstep (se 2 (by rfl) ⟨970818, by rfl⟩ : syracuseStep 2588849 = 1941637) B1941637
theorem B2588867 : Blo 1725063 2588867 := bstep (se 1 (by rfl) ⟨1941650, by rfl⟩ : syracuseStep 2588867 = 3883301) B3883301
theorem B2588897 : Blo 1725063 2588897 := bstep (se 2 (by rfl) ⟨970836, by rfl⟩ : syracuseStep 2588897 = 1941673) B1941673
theorem B2588915 : Blo 1725063 2588915 := bstep (se 1 (by rfl) ⟨1941686, by rfl⟩ : syracuseStep 2588915 = 3883373) B3883373
theorem B1941763 : Blo 1725063 1941763 := bstep (se 1 (by rfl) ⟨1456322, by rfl⟩ : syracuseStep 1941763 = 2912645) B2912645
theorem B2588945 : Blo 1725063 2588945 := bstep (se 2 (by rfl) ⟨970854, by rfl⟩ : syracuseStep 2588945 = 1941709) B1941709
theorem B2588963 : Blo 1725063 2588963 := bstep (se 1 (by rfl) ⟨1941722, by rfl⟩ : syracuseStep 2588963 = 3883445) B3883445
theorem B3277091 : Blo 1725063 3277091 := bstep (se 1 (by rfl) ⟨2457818, by rfl⟩ : syracuseStep 3277091 = 4915637) B4915637
theorem B5824817 : Blo 1725063 5824817 := bstep (se 2 (by rfl) ⟨2184306, by rfl⟩ : syracuseStep 5824817 = 4368613) B4368613
theorem B2588993 : Blo 1725063 2588993 := bstep (se 2 (by rfl) ⟨970872, by rfl⟩ : syracuseStep 2588993 = 1941745) B1941745
theorem B2589011 : Blo 1725063 2589011 := bstep (se 1 (by rfl) ⟨1941758, by rfl⟩ : syracuseStep 2589011 = 3883517) B3883517
theorem B2457955 : Blo 1725063 2457955 := bstep (se 1 (by rfl) ⟨1843466, by rfl⟩ : syracuseStep 2457955 = 3686933) B3686933
theorem B2589041 : Blo 1725063 2589041 := bstep (se 2 (by rfl) ⟨970890, by rfl⟩ : syracuseStep 2589041 = 1941781) B1941781
theorem B2589059 : Blo 1725063 2589059 := bstep (se 1 (by rfl) ⟨1941794, by rfl⟩ : syracuseStep 2589059 = 3883589) B3883589
theorem B7373197 : Blo 1725063 7373197 := bstep (se 3 (by rfl) ⟨1382474, by rfl⟩ : syracuseStep 7373197 = 2764949) B2764949
theorem B3883409 : Blo 1725063 3883409 := bstep (se 2 (by rfl) ⟨1456278, by rfl⟩ : syracuseStep 3883409 = 2912557) B2912557
theorem B1941907 : Blo 1725063 1941907 := bstep (se 1 (by rfl) ⟨1456430, by rfl⟩ : syracuseStep 1941907 = 2912861) B2912861
theorem B2589089 : Blo 1725063 2589089 := bstep (se 2 (by rfl) ⟨970908, by rfl⟩ : syracuseStep 2589089 = 1941817) B1941817
theorem B3883427 : Blo 1725063 3883427 := bstep (se 1 (by rfl) ⟨2912570, by rfl⟩ : syracuseStep 3883427 = 5825141) B5825141
theorem B2589107 : Blo 1725063 2589107 := bstep (se 1 (by rfl) ⟨1941830, by rfl⟩ : syracuseStep 2589107 = 3883661) B3883661
theorem B2589137 : Blo 1725063 2589137 := bstep (se 2 (by rfl) ⟨970926, by rfl⟩ : syracuseStep 2589137 = 1941853) B1941853
theorem B2589155 : Blo 1725063 2589155 := bstep (se 1 (by rfl) ⟨1941866, by rfl⟩ : syracuseStep 2589155 = 3883733) B3883733
theorem B3498481 : Blo 1725063 3498481 := bstep (se 2 (by rfl) ⟨1311930, by rfl⟩ : syracuseStep 3498481 = 2623861) B2623861
theorem B2589185 : Blo 1725063 2589185 := bstep (se 2 (by rfl) ⟨970944, by rfl⟩ : syracuseStep 2589185 = 1941889) B1941889
theorem B2589203 : Blo 1725063 2589203 := bstep (se 1 (by rfl) ⟨1941902, by rfl⟩ : syracuseStep 2589203 = 3883805) B3883805
theorem B1942051 : Blo 1725063 1942051 := bstep (se 1 (by rfl) ⟨1456538, by rfl⟩ : syracuseStep 1942051 = 2913077) B2913077
theorem B2589233 : Blo 1725063 2589233 := bstep (se 2 (by rfl) ⟨970962, by rfl⟩ : syracuseStep 2589233 = 1941925) B1941925
theorem B2589251 : Blo 1725063 2589251 := bstep (se 1 (by rfl) ⟨1941938, by rfl⟩ : syracuseStep 2589251 = 3883877) B3883877
theorem B3596881 : Blo 1725063 3596881 := bstep (se 2 (by rfl) ⟨1348830, by rfl⟩ : syracuseStep 3596881 = 2697661) B2697661
theorem B2589281 : Blo 1725063 2589281 := bstep (se 2 (by rfl) ⟨970980, by rfl⟩ : syracuseStep 2589281 = 1941961) B1941961
theorem B2589299 : Blo 1725063 2589299 := bstep (se 1 (by rfl) ⟨1941974, by rfl⟩ : syracuseStep 2589299 = 3883949) B3883949
theorem B4915853 : Blo 1725063 4915853 := bstep (se 3 (by rfl) ⟨921722, by rfl⟩ : syracuseStep 4915853 = 1843445) B1843445
theorem B4366993 : Blo 1725063 4366993 := bstep (se 2 (by rfl) ⟨1637622, by rfl⟩ : syracuseStep 4366993 = 3275245) B3275245
theorem B2589329 : Blo 1725063 2589329 := bstep (se 2 (by rfl) ⟨970998, by rfl⟩ : syracuseStep 2589329 = 1941997) B1941997
theorem B2589347 : Blo 1725063 2589347 := bstep (se 1 (by rfl) ⟨1942010, by rfl⟩ : syracuseStep 2589347 = 3884021) B3884021
theorem B3883697 : Blo 1725063 3883697 := bstep (se 2 (by rfl) ⟨1456386, by rfl⟩ : syracuseStep 3883697 = 2912773) B2912773
theorem B1942195 : Blo 1725063 1942195 := bstep (se 1 (by rfl) ⟨1456646, by rfl⟩ : syracuseStep 1942195 = 2913293) B2913293
theorem B2458291 : Blo 1725063 2458291 := bstep (se 1 (by rfl) ⟨1843718, by rfl⟩ : syracuseStep 2458291 = 3687437) B3687437
theorem B2589377 : Blo 1725063 2589377 := bstep (se 2 (by rfl) ⟨971016, by rfl⟩ : syracuseStep 2589377 = 1942033) B1942033
theorem B3883715 : Blo 1725063 3883715 := bstep (se 1 (by rfl) ⟨2912786, by rfl⟩ : syracuseStep 3883715 = 5825573) B5825573
theorem B6554317 : Blo 1725063 6554317 := bstep (se 3 (by rfl) ⟨1228934, by rfl⟩ : syracuseStep 6554317 = 2457869) B2457869
theorem B2589395 : Blo 1725063 2589395 := bstep (se 1 (by rfl) ⟨1942046, by rfl⟩ : syracuseStep 2589395 = 3884093) B3884093
theorem B2589425 : Blo 1725063 2589425 := bstep (se 2 (by rfl) ⟨971034, by rfl⟩ : syracuseStep 2589425 = 1942069) B1942069
theorem B2589443 : Blo 1725063 2589443 := bstep (se 1 (by rfl) ⟨1942082, by rfl⟩ : syracuseStep 2589443 = 3884165) B3884165
theorem B2589473 : Blo 1725063 2589473 := bstep (se 2 (by rfl) ⟨971052, by rfl⟩ : syracuseStep 2589473 = 1942105) B1942105
theorem B9831203 : Blo 1725063 9831203 := bstep (se 1 (by rfl) ⟨7373402, by rfl⟩ : syracuseStep 9831203 = 14746805) B14746805
theorem B8741681 : Blo 1725063 8741681 := bstep (se 2 (by rfl) ⟨3278130, by rfl⟩ : syracuseStep 8741681 = 6556261) B6556261
theorem B2589491 : Blo 1725063 2589491 := bstep (se 1 (by rfl) ⟨1942118, by rfl⟩ : syracuseStep 2589491 = 3884237) B3884237
theorem B1942339 : Blo 1725063 1942339 := bstep (se 1 (by rfl) ⟨1456754, by rfl⟩ : syracuseStep 1942339 = 2913509) B2913509
theorem B5825357 : Blo 1725063 5825357 := bstep (se 3 (by rfl) ⟨1092254, by rfl⟩ : syracuseStep 5825357 = 2184509) B2184509
theorem B2589521 : Blo 1725063 2589521 := bstep (se 2 (by rfl) ⟨971070, by rfl⟩ : syracuseStep 2589521 = 1942141) B1942141
theorem B1844051 : Blo 1725063 1844051 := bstep (se 1 (by rfl) ⟨1383038, by rfl⟩ : syracuseStep 1844051 = 2766077) B2766077
theorem B2073443 : Blo 1725063 2073443 := bstep (se 1 (by rfl) ⟨1555082, by rfl⟩ : syracuseStep 2073443 = 3110165) B3110165
theorem B2589539 : Blo 1725063 2589539 := bstep (se 1 (by rfl) ⟨1942154, by rfl⟩ : syracuseStep 2589539 = 3884309) B3884309
theorem B2589569 : Blo 1725063 2589569 := bstep (se 2 (by rfl) ⟨971088, by rfl⟩ : syracuseStep 2589569 = 1942177) B1942177
theorem B5825411 : Blo 1725063 5825411 := bstep (se 1 (by rfl) ⟨4369058, by rfl⟩ : syracuseStep 5825411 = 8738117) B8738117
theorem B3367811 : Blo 1725063 3367811 := bstep (se 1 (by rfl) ⟨2525858, by rfl⟩ : syracuseStep 3367811 = 5051717) B5051717
theorem B8733581 : Blo 1725063 8733581 := bstep (se 3 (by rfl) ⟨1637546, by rfl⟩ : syracuseStep 8733581 = 3275093) B3275093
theorem B5530513 : Blo 1725063 5530513 := bstep (se 2 (by rfl) ⟨2073942, by rfl⟩ : syracuseStep 5530513 = 4147885) B4147885
theorem B2589587 : Blo 1725063 2589587 := bstep (se 1 (by rfl) ⟨1942190, by rfl⟩ : syracuseStep 2589587 = 3884381) B3884381
theorem B4367267 : Blo 1725063 4367267 := bstep (se 1 (by rfl) ⟨3275450, by rfl⟩ : syracuseStep 4367267 = 6550901) B6550901
theorem B2589617 : Blo 1725063 2589617 := bstep (se 2 (by rfl) ⟨971106, by rfl⟩ : syracuseStep 2589617 = 1942213) B1942213
theorem B2589635 : Blo 1725063 2589635 := bstep (se 1 (by rfl) ⟨1942226, by rfl⟩ : syracuseStep 2589635 = 3884453) B3884453
theorem B3883985 : Blo 1725063 3883985 := bstep (se 2 (by rfl) ⟨1456494, by rfl⟩ : syracuseStep 3883985 = 2912989) B2912989
theorem B1942483 : Blo 1725063 1942483 := bstep (se 1 (by rfl) ⟨1456862, by rfl⟩ : syracuseStep 1942483 = 2913725) B2913725
theorem B2589665 : Blo 1725063 2589665 := bstep (se 2 (by rfl) ⟨971124, by rfl⟩ : syracuseStep 2589665 = 1942249) B1942249
theorem B3884003 : Blo 1725063 3884003 := bstep (se 1 (by rfl) ⟨2913002, by rfl⟩ : syracuseStep 3884003 = 5826005) B5826005
theorem B2589683 : Blo 1725063 2589683 := bstep (se 1 (by rfl) ⟨1942262, by rfl⟩ : syracuseStep 2589683 = 3884525) B3884525
theorem B2589713 : Blo 1725063 2589713 := bstep (se 2 (by rfl) ⟨971142, by rfl⟩ : syracuseStep 2589713 = 1942285) B1942285
theorem B2589731 : Blo 1725063 2589731 := bstep (se 1 (by rfl) ⟨1942298, by rfl⟩ : syracuseStep 2589731 = 3884597) B3884597
theorem B2589761 : Blo 1725063 2589761 := bstep (se 2 (by rfl) ⟨971160, by rfl⟩ : syracuseStep 2589761 = 1942321) B1942321
theorem B2589779 : Blo 1725063 2589779 := bstep (se 1 (by rfl) ⟨1942334, by rfl⟩ : syracuseStep 2589779 = 3884669) B3884669
theorem B1967203 : Blo 1725063 1967203 := bstep (se 1 (by rfl) ⟨1475402, by rfl⟩ : syracuseStep 1967203 = 2950805) B2950805
theorem B4367459 : Blo 1725063 4367459 := bstep (se 1 (by rfl) ⟨3275594, by rfl⟩ : syracuseStep 4367459 = 6551189) B6551189
theorem B1942627 : Blo 1725063 1942627 := bstep (se 1 (by rfl) ⟨1456970, by rfl⟩ : syracuseStep 1942627 = 2913941) B2913941
theorem B2589809 : Blo 1725063 2589809 := bstep (se 2 (by rfl) ⟨971178, by rfl⟩ : syracuseStep 2589809 = 1942357) B1942357
theorem B2589827 : Blo 1725063 2589827 := bstep (se 1 (by rfl) ⟨1942370, by rfl⟩ : syracuseStep 2589827 = 3884741) B3884741
theorem B5825681 : Blo 1725063 5825681 := bstep (se 2 (by rfl) ⟨2184630, by rfl⟩ : syracuseStep 5825681 = 4369261) B4369261
theorem B2589857 : Blo 1725063 2589857 := bstep (se 2 (by rfl) ⟨971196, by rfl⟩ : syracuseStep 2589857 = 1942393) B1942393
theorem B5604515 : Blo 1725063 5604515 := bstep (se 1 (by rfl) ⟨4203386, by rfl⟩ : syracuseStep 5604515 = 8406773) B8406773
theorem B2589875 : Blo 1725063 2589875 := bstep (se 1 (by rfl) ⟨1942406, by rfl⟩ : syracuseStep 2589875 = 3884813) B3884813
theorem B2589905 : Blo 1725063 2589905 := bstep (se 2 (by rfl) ⟨971214, by rfl⟩ : syracuseStep 2589905 = 1942429) B1942429
theorem B2458849 : Blo 1725063 2458849 := bstep (se 2 (by rfl) ⟨922068, by rfl⟩ : syracuseStep 2458849 = 1844137) B1844137
theorem B2589923 : Blo 1725063 2589923 := bstep (se 1 (by rfl) ⟨1942442, by rfl⟩ : syracuseStep 2589923 = 3884885) B3884885
theorem B3884273 : Blo 1725063 3884273 := bstep (se 2 (by rfl) ⟨1456602, by rfl⟩ : syracuseStep 3884273 = 2913205) B2913205
theorem B1942771 : Blo 1725063 1942771 := bstep (se 1 (by rfl) ⟨1457078, by rfl⟩ : syracuseStep 1942771 = 2914157) B2914157
theorem B2589953 : Blo 1725063 2589953 := bstep (se 2 (by rfl) ⟨971232, by rfl⟩ : syracuseStep 2589953 = 1942465) B1942465
theorem B3884291 : Blo 1725063 3884291 := bstep (se 1 (by rfl) ⟨2913218, by rfl⟩ : syracuseStep 3884291 = 5826437) B5826437
theorem B2458883 : Blo 1725063 2458883 := bstep (se 1 (by rfl) ⟨1844162, by rfl⟩ : syracuseStep 2458883 = 3688325) B3688325
theorem B2589971 : Blo 1725063 2589971 := bstep (se 1 (by rfl) ⟨1942478, by rfl⟩ : syracuseStep 2589971 = 3884957) B3884957
theorem B1967395 : Blo 1725063 1967395 := bstep (se 1 (by rfl) ⟨1475546, by rfl⟩ : syracuseStep 1967395 = 2951093) B2951093
theorem B2590001 : Blo 1725063 2590001 := bstep (se 2 (by rfl) ⟨971250, by rfl⟩ : syracuseStep 2590001 = 1942501) B1942501
theorem B2590019 : Blo 1725063 2590019 := bstep (se 1 (by rfl) ⟨1942514, by rfl⟩ : syracuseStep 2590019 = 3885029) B3885029
theorem B3687761 : Blo 1725063 3687761 := bstep (se 2 (by rfl) ⟨1382910, by rfl⟩ : syracuseStep 3687761 = 2765821) B2765821
theorem B3278161 : Blo 1725063 3278161 := bstep (se 2 (by rfl) ⟨1229310, by rfl⟩ : syracuseStep 3278161 = 2458621) B2458621
theorem B2590049 : Blo 1725063 2590049 := bstep (se 2 (by rfl) ⟨971268, by rfl⟩ : syracuseStep 2590049 = 1942537) B1942537
theorem B2590067 : Blo 1725063 2590067 := bstep (se 1 (by rfl) ⟨1942550, by rfl⟩ : syracuseStep 2590067 = 3885101) B3885101
theorem B1942915 : Blo 1725063 1942915 := bstep (se 1 (by rfl) ⟨1457186, by rfl⟩ : syracuseStep 1942915 = 2914373) B2914373
theorem B2590097 : Blo 1725063 2590097 := bstep (se 2 (by rfl) ⟨971286, by rfl⟩ : syracuseStep 2590097 = 1942573) B1942573
theorem B2590115 : Blo 1725063 2590115 := bstep (se 1 (by rfl) ⟨1942586, by rfl⟩ : syracuseStep 2590115 = 3885173) B3885173
theorem B2590145 : Blo 1725063 2590145 := bstep (se 2 (by rfl) ⟨971304, by rfl⟩ : syracuseStep 2590145 = 1942609) B1942609
theorem B2590163 : Blo 1725063 2590163 := bstep (se 1 (by rfl) ⟨1942622, by rfl⟩ : syracuseStep 2590163 = 3885245) B3885245
theorem B6555107 : Blo 1725063 6555107 := bstep (se 1 (by rfl) ⟨4916330, by rfl⟩ : syracuseStep 6555107 = 9832661) B9832661
theorem B2590193 : Blo 1725063 2590193 := bstep (se 2 (by rfl) ⟨971322, by rfl⟩ : syracuseStep 2590193 = 1942645) B1942645
theorem B2590211 : Blo 1725063 2590211 := bstep (se 1 (by rfl) ⟨1942658, by rfl⟩ : syracuseStep 2590211 = 3885317) B3885317
theorem B3884561 : Blo 1725063 3884561 := bstep (se 2 (by rfl) ⟨1456710, by rfl⟩ : syracuseStep 3884561 = 2913421) B2913421
theorem B2590241 : Blo 1725063 2590241 := bstep (se 2 (by rfl) ⟨971340, by rfl⟩ : syracuseStep 2590241 = 1942681) B1942681
theorem B3884579 : Blo 1725063 3884579 := bstep (se 1 (by rfl) ⟨2913434, by rfl⟩ : syracuseStep 3884579 = 5826869) B5826869
theorem B2590259 : Blo 1725063 2590259 := bstep (se 1 (by rfl) ⟨1942694, by rfl⟩ : syracuseStep 2590259 = 3885389) B3885389
theorem B2590289 : Blo 1725063 2590289 := bstep (se 2 (by rfl) ⟨971358, by rfl⟩ : syracuseStep 2590289 = 1942717) B1942717
theorem B2590307 : Blo 1725063 2590307 := bstep (se 1 (by rfl) ⟨1942730, by rfl⟩ : syracuseStep 2590307 = 3885461) B3885461
theorem B2590337 : Blo 1725063 2590337 := bstep (se 2 (by rfl) ⟨971376, by rfl⟩ : syracuseStep 2590337 = 1942753) B1942753
theorem B13108877 : Blo 1725063 13108877 := bstep (se 3 (by rfl) ⟨2457914, by rfl⟩ : syracuseStep 13108877 = 4915829) B4915829
theorem B2590355 : Blo 1725063 2590355 := bstep (se 1 (by rfl) ⟨1942766, by rfl⟩ : syracuseStep 2590355 = 3885533) B3885533
theorem B5826221 : Blo 1725063 5826221 := bstep (se 3 (by rfl) ⟨1092416, by rfl⟩ : syracuseStep 5826221 = 2184833) B2184833
theorem B2590385 : Blo 1725063 2590385 := bstep (se 2 (by rfl) ⟨971394, by rfl⟩ : syracuseStep 2590385 = 1942789) B1942789
theorem B3032771 : Blo 1725063 3032771 := bstep (se 1 (by rfl) ⟨2274578, by rfl⟩ : syracuseStep 3032771 = 4549157) B4549157
theorem B2590403 : Blo 1725063 2590403 := bstep (se 1 (by rfl) ⟨1942802, by rfl⟩ : syracuseStep 2590403 = 3885605) B3885605
theorem B2590433 : Blo 1725063 2590433 := bstep (se 2 (by rfl) ⟨971412, by rfl⟩ : syracuseStep 2590433 = 1942825) B1942825
theorem B5826275 : Blo 1725063 5826275 := bstep (se 1 (by rfl) ⟨4369706, by rfl⟩ : syracuseStep 5826275 = 8739413) B8739413
theorem B3688163 : Blo 1725063 3688163 := bstep (se 1 (by rfl) ⟨2766122, by rfl⟩ : syracuseStep 3688163 = 5532245) B5532245
theorem B4663021 : Blo 1725063 4663021 := bstep (se 3 (by rfl) ⟨874316, by rfl⟩ : syracuseStep 4663021 = 1748633) B1748633
theorem B2590451 : Blo 1725063 2590451 := bstep (se 1 (by rfl) ⟨1942838, by rfl⟩ : syracuseStep 2590451 = 3885677) B3885677
theorem B9832205 : Blo 1725063 9832205 := bstep (se 3 (by rfl) ⟨1843538, by rfl⟩ : syracuseStep 9832205 = 3687077) B3687077
theorem B2590481 : Blo 1725063 2590481 := bstep (se 2 (by rfl) ⟨971430, by rfl⟩ : syracuseStep 2590481 = 1942861) B1942861
theorem B2590499 : Blo 1725063 2590499 := bstep (se 1 (by rfl) ⟨1942874, by rfl⟩ : syracuseStep 2590499 = 3885749) B3885749
theorem B4917037 : Blo 1725063 4917037 := bstep (se 3 (by rfl) ⟨921944, by rfl⟩ : syracuseStep 4917037 = 1843889) B1843889
theorem B3884849 : Blo 1725063 3884849 := bstep (se 2 (by rfl) ⟨1456818, by rfl⟩ : syracuseStep 3884849 = 2913637) B2913637
theorem B2590529 : Blo 1725063 2590529 := bstep (se 2 (by rfl) ⟨971448, by rfl⟩ : syracuseStep 2590529 = 1942897) B1942897
theorem B3884867 : Blo 1725063 3884867 := bstep (se 1 (by rfl) ⟨2913650, by rfl⟩ : syracuseStep 3884867 = 5827301) B5827301
theorem B2590547 : Blo 1725063 2590547 := bstep (se 1 (by rfl) ⟨1942910, by rfl⟩ : syracuseStep 2590547 = 3885821) B3885821
theorem B2590577 : Blo 1725063 2590577 := bstep (se 2 (by rfl) ⟨971466, by rfl⟩ : syracuseStep 2590577 = 1942933) B1942933
theorem B2590595 : Blo 1725063 2590595 := bstep (se 1 (by rfl) ⟨1942946, by rfl⟩ : syracuseStep 2590595 = 3885893) B3885893
theorem B4728721 : Blo 1725063 4728721 := bstep (se 2 (by rfl) ⟨1773270, by rfl⟩ : syracuseStep 4728721 = 3546541) B3546541
theorem B5826545 : Blo 1725063 5826545 := bstep (se 2 (by rfl) ⟨2184954, by rfl⟩ : syracuseStep 5826545 = 4369909) B4369909
theorem B4368401 : Blo 1725063 4368401 := bstep (se 2 (by rfl) ⟨1638150, by rfl⟩ : syracuseStep 4368401 = 3276301) B3276301
theorem B4663345 : Blo 1725063 4663345 := bstep (se 2 (by rfl) ⟨1748754, by rfl⟩ : syracuseStep 4663345 = 3497509) B3497509
theorem B4368451 : Blo 1725063 4368451 := bstep (se 1 (by rfl) ⟨3276338, by rfl⟩ : syracuseStep 4368451 = 6552677) B6552677
theorem B3885137 : Blo 1725063 3885137 := bstep (se 2 (by rfl) ⟨1456926, by rfl⟩ : syracuseStep 3885137 = 2913853) B2913853
theorem B3885155 : Blo 1725063 3885155 := bstep (se 1 (by rfl) ⟨2913866, by rfl⟩ : syracuseStep 3885155 = 5827733) B5827733
theorem B6555761 : Blo 1725063 6555761 := bstep (se 2 (by rfl) ⟨2458410, by rfl⟩ : syracuseStep 6555761 = 4916821) B4916821
theorem B5605553 : Blo 1725063 5605553 := bstep (se 2 (by rfl) ⟨2102082, by rfl⟩ : syracuseStep 5605553 = 4204165) B4204165
theorem B4368593 : Blo 1725063 4368593 := bstep (se 2 (by rfl) ⟨1638222, by rfl⟩ : syracuseStep 4368593 = 3276445) B3276445
theorem B8743139 : Blo 1725063 8743139 := bstep (se 1 (by rfl) ⟨6557354, by rfl⟩ : syracuseStep 8743139 = 13114709) B13114709
theorem B3885425 : Blo 1725063 3885425 := bstep (se 2 (by rfl) ⟨1457034, by rfl⟩ : syracuseStep 3885425 = 2914069) B2914069
theorem B3885443 : Blo 1725063 3885443 := bstep (se 1 (by rfl) ⟨2914082, by rfl⟩ : syracuseStep 3885443 = 5828165) B5828165
theorem B5532077 : Blo 1725063 5532077 := bstep (se 3 (by rfl) ⟨1037264, by rfl⟩ : syracuseStep 5532077 = 2074529) B2074529
theorem B6220273 : Blo 1725063 6220273 := bstep (se 2 (by rfl) ⟨2332602, by rfl⟩ : syracuseStep 6220273 = 4665205) B4665205
theorem B5605891 : Blo 1725063 5605891 := bstep (se 1 (by rfl) ⟨4204418, by rfl⟩ : syracuseStep 5605891 = 8408837) B8408837
theorem B5827085 : Blo 1725063 5827085 := bstep (se 3 (by rfl) ⟨1092578, by rfl⟩ : syracuseStep 5827085 = 2185157) B2185157
theorem B5827139 : Blo 1725063 5827139 := bstep (se 1 (by rfl) ⟨4370354, by rfl⟩ : syracuseStep 5827139 = 8740709) B8740709
theorem B16583237 : Blo 1725063 16583237 := bstep (se 4 (by rfl) ⟨1554678, by rfl⟩ : syracuseStep 16583237 = 3109357) B3109357
theorem B3885713 : Blo 1725063 3885713 := bstep (se 2 (by rfl) ⟨1457142, by rfl⟩ : syracuseStep 3885713 = 2914285) B2914285
theorem B3885731 : Blo 1725063 3885731 := bstep (se 1 (by rfl) ⟨2914298, by rfl⟩ : syracuseStep 3885731 = 5828597) B5828597
theorem B7473869 : Blo 1725063 7473869 := bstep (se 3 (by rfl) ⟨1401350, by rfl⟩ : syracuseStep 7473869 = 2802701) B2802701
theorem B4664081 : Blo 1725063 4664081 := bstep (se 2 (by rfl) ⟨1749030, by rfl⟩ : syracuseStep 4664081 = 3498061) B3498061
theorem B5827409 : Blo 1725063 5827409 := bstep (se 2 (by rfl) ⟨2185278, by rfl⟩ : syracuseStep 5827409 = 4370557) B4370557
theorem B2911153 : Blo 1725063 2911153 := bstep (se 2 (by rfl) ⟨1091682, by rfl⟩ : syracuseStep 2911153 = 2183365) B2183365
theorem B13290437 : Blo 1725063 13290437 := bstep (se 4 (by rfl) ⟨1245978, by rfl⟩ : syracuseStep 13290437 = 2491957) B2491957
theorem B2911187 : Blo 1725063 2911187 := bstep (se 1 (by rfl) ⟨2183390, by rfl⟩ : syracuseStep 2911187 = 4366781) B4366781
theorem B5319715 : Blo 1725063 5319715 := bstep (se 1 (by rfl) ⟨3989786, by rfl⟩ : syracuseStep 5319715 = 7979573) B7979573
theorem B2911315 : Blo 1725063 2911315 := bstep (se 1 (by rfl) ⟨2183486, by rfl⟩ : syracuseStep 2911315 = 4366973) B4366973
theorem B34540657 : Blo 1725063 34540657 := bstep (se 2 (by rfl) ⟨12952746, by rfl⟩ : syracuseStep 34540657 = 25905493) B25905493
theorem B4369585 : Blo 1725063 4369585 := bstep (se 2 (by rfl) ⟨1638594, by rfl⟩ : syracuseStep 4369585 = 3277189) B3277189
theorem B2911457 : Blo 1725063 2911457 := bstep (se 2 (by rfl) ⟨1091796, by rfl⟩ : syracuseStep 2911457 = 2183593) B2183593
theorem B2764001 : Blo 1725063 2764001 := bstep (se 2 (by rfl) ⟨1036500, by rfl⟩ : syracuseStep 2764001 = 2073001) B2073001
theorem B10497293 : Blo 1725063 10497293 := bstep (se 3 (by rfl) ⟨1968242, by rfl⟩ : syracuseStep 10497293 = 3936485) B3936485
theorem B95816981 : Blo 1725063 95816981 := bstep (se 6 (by rfl) ⟨2245710, by rfl⟩ : syracuseStep 95816981 = 4491421) B4491421
theorem B2911585 : Blo 1725063 2911585 := bstep (se 2 (by rfl) ⟨1091844, by rfl⟩ : syracuseStep 2911585 = 2183689) B2183689
theorem B2764129 : Blo 1725063 2764129 := bstep (se 2 (by rfl) ⟨1036548, by rfl⟩ : syracuseStep 2764129 = 2073097) B2073097
theorem B5827949 : Blo 1725063 5827949 := bstep (se 3 (by rfl) ⟨1092740, by rfl⟩ : syracuseStep 5827949 = 2185481) B2185481
theorem B2911619 : Blo 1725063 2911619 := bstep (se 1 (by rfl) ⟨2183714, by rfl⟩ : syracuseStep 2911619 = 4367429) B4367429
theorem B5828003 : Blo 1725063 5828003 := bstep (se 1 (by rfl) ⟨4371002, by rfl⟩ : syracuseStep 5828003 = 8742005) B8742005
theorem B4369859 : Blo 1725063 4369859 := bstep (se 1 (by rfl) ⟨3277394, by rfl⟩ : syracuseStep 4369859 = 6554789) B6554789
theorem B2911747 : Blo 1725063 2911747 := bstep (se 1 (by rfl) ⟨2183810, by rfl⟩ : syracuseStep 2911747 = 4367621) B4367621
theorem B6557219 : Blo 1725063 6557219 := bstep (se 1 (by rfl) ⟨4917914, by rfl⟩ : syracuseStep 6557219 = 9835829) B9835829
theorem B6557233 : Blo 1725063 6557233 := bstep (se 2 (by rfl) ⟨2458962, by rfl⟩ : syracuseStep 6557233 = 4917925) B4917925
theorem B4370051 : Blo 1725063 4370051 := bstep (se 1 (by rfl) ⟨3277538, by rfl⟩ : syracuseStep 4370051 = 6555077) B6555077
theorem B7573133 : Blo 1725063 7573133 := bstep (se 3 (by rfl) ⟨1419962, by rfl⟩ : syracuseStep 7573133 = 2839925) B2839925
theorem B11062925 : Blo 1725063 11062925 := bstep (se 3 (by rfl) ⟨2074298, by rfl⟩ : syracuseStep 11062925 = 4148597) B4148597
theorem B2911889 : Blo 1725063 2911889 := bstep (se 2 (by rfl) ⟨1091958, by rfl⟩ : syracuseStep 2911889 = 2183917) B2183917
theorem B5828273 : Blo 1725063 5828273 := bstep (se 2 (by rfl) ⟨2185602, by rfl⟩ : syracuseStep 5828273 = 4371205) B4371205
theorem B8736497 : Blo 1725063 8736497 := bstep (se 2 (by rfl) ⟨3276186, by rfl⟩ : syracuseStep 8736497 = 6552373) B6552373
theorem B2912017 : Blo 1725063 2912017 := bstep (se 2 (by rfl) ⟨1092006, by rfl⟩ : syracuseStep 2912017 = 2184013) B2184013
theorem B2912051 : Blo 1725063 2912051 := bstep (se 1 (by rfl) ⟨2184038, by rfl⟩ : syracuseStep 2912051 = 4368077) B4368077
theorem B18665315 : Blo 1725063 18665315 := bstep (se 1 (by rfl) ⟨13998986, by rfl⟩ : syracuseStep 18665315 = 27997973) B27997973
theorem B9326513 : Blo 1725063 9326513 := bstep (se 2 (by rfl) ⟨3497442, by rfl⟩ : syracuseStep 9326513 = 6994885) B6994885
theorem B2912179 : Blo 1725063 2912179 := bstep (se 1 (by rfl) ⟨2184134, by rfl⟩ : syracuseStep 2912179 = 4368269) B4368269
theorem B13103045 : Blo 1725063 13103045 := bstep (se 4 (by rfl) ⟨1228410, by rfl⟩ : syracuseStep 13103045 = 2456821) B2456821
theorem B5607427 : Blo 1725063 5607427 := bstep (se 1 (by rfl) ⟨4205570, by rfl⟩ : syracuseStep 5607427 = 8411141) B8411141
theorem B12439565 : Blo 1725063 12439565 := bstep (se 3 (by rfl) ⟨2332418, by rfl⟩ : syracuseStep 12439565 = 4664837) B4664837
theorem B2912321 : Blo 1725063 2912321 := bstep (se 2 (by rfl) ⟨1092120, by rfl⟩ : syracuseStep 2912321 = 2184241) B2184241
theorem B9826373 : Blo 1725063 9826373 := bstep (se 4 (by rfl) ⟨921222, by rfl⟩ : syracuseStep 9826373 = 1842445) B1842445
theorem B4550833 : Blo 1725063 4550833 := bstep (se 2 (by rfl) ⟨1706562, by rfl⟩ : syracuseStep 4550833 = 3413125) B3413125
theorem B2363585 : Blo 1725063 2363585 := bstep (se 2 (by rfl) ⟨886344, by rfl⟩ : syracuseStep 2363585 = 1772689) B1772689
theorem B2912449 : Blo 1725063 2912449 := bstep (se 2 (by rfl) ⟨1092168, by rfl⟩ : syracuseStep 2912449 = 2184337) B2184337
theorem B11210957 : Blo 1725063 11210957 := bstep (se 3 (by rfl) ⟨2102054, by rfl⟩ : syracuseStep 11210957 = 4204109) B4204109
theorem B5828813 : Blo 1725063 5828813 := bstep (se 3 (by rfl) ⟨1092902, by rfl⟩ : syracuseStep 5828813 = 2185805) B2185805
theorem B2912483 : Blo 1725063 2912483 := bstep (se 1 (by rfl) ⟨2184362, by rfl⟩ : syracuseStep 2912483 = 4368725) B4368725
theorem B12439793 : Blo 1725063 12439793 := bstep (se 2 (by rfl) ⟨4664922, by rfl⟩ : syracuseStep 12439793 = 9329845) B9329845
theorem B7368995 : Blo 1725063 7368995 := bstep (se 1 (by rfl) ⟨5526746, by rfl⟩ : syracuseStep 7368995 = 11053493) B11053493
theorem B4149539 : Blo 1725063 4149539 := bstep (se 1 (by rfl) ⟨3112154, by rfl⟩ : syracuseStep 4149539 = 6224309) B6224309
theorem B38342965 : Blo 1725063 38342965 := bstep (se 5 (by rfl) ⟨1797326, by rfl⟩ : syracuseStep 38342965 = 3594653) B3594653
theorem B2912611 : Blo 1725063 2912611 := bstep (se 1 (by rfl) ⟨2184458, by rfl⟩ : syracuseStep 2912611 = 4368917) B4368917
theorem B2912753 : Blo 1725063 2912753 := bstep (se 2 (by rfl) ⟨1092282, by rfl⟩ : syracuseStep 2912753 = 2184565) B2184565
theorem B13111793 : Blo 1725063 13111793 := bstep (se 2 (by rfl) ⟨4916922, by rfl⟩ : syracuseStep 13111793 = 9833845) B9833845
theorem B9826829 : Blo 1725063 9826829 := bstep (se 3 (by rfl) ⟨1842530, by rfl⟩ : syracuseStep 9826829 = 3685061) B3685061
theorem B14750221 : Blo 1725063 14750221 := bstep (se 3 (by rfl) ⟨2765666, by rfl⟩ : syracuseStep 14750221 = 5531333) B5531333
theorem B2183699 : Blo 1725063 2183699 := bstep (se 1 (by rfl) ⟨1637774, by rfl⟩ : syracuseStep 2183699 = 3275549) B3275549
theorem B4370993 : Blo 1725063 4370993 := bstep (se 2 (by rfl) ⟨1639122, by rfl⟩ : syracuseStep 4370993 = 3278245) B3278245
theorem B2765411 : Blo 1725063 2765411 := bstep (se 1 (by rfl) ⟨2074058, by rfl⟩ : syracuseStep 2765411 = 4148117) B4148117
theorem B4371043 : Blo 1725063 4371043 := bstep (se 1 (by rfl) ⟨3278282, by rfl⟩ : syracuseStep 4371043 = 6556565) B6556565
theorem B2912881 : Blo 1725063 2912881 := bstep (se 2 (by rfl) ⟨1092330, by rfl⟩ : syracuseStep 2912881 = 2184661) B2184661
theorem B9835121 : Blo 1725063 9835121 := bstep (se 2 (by rfl) ⟨3688170, by rfl⟩ : syracuseStep 9835121 = 7376341) B7376341
theorem B1725075 : Blo 1725063 1725075 := bstep (se 1 (by rfl) ⟨1293806, by rfl⟩ : syracuseStep 1725075 = 2587613) B2587613
theorem B2912915 : Blo 1725063 2912915 := bstep (se 1 (by rfl) ⟨2184686, by rfl⟩ : syracuseStep 2912915 = 4369373) B4369373
theorem B1725091 : Blo 1725063 1725091 := bstep (se 1 (by rfl) ⟨1293818, by rfl⟩ : syracuseStep 1725091 = 2587637) B2587637
theorem B1725107 : Blo 1725063 1725107 := bstep (se 1 (by rfl) ⟨1293830, by rfl⟩ : syracuseStep 1725107 = 2587661) B2587661
theorem B1725123 : Blo 1725063 1725123 := bstep (se 1 (by rfl) ⟨1293842, by rfl⟩ : syracuseStep 1725123 = 2587685) B2587685
theorem B2765507 : Blo 1725063 2765507 := bstep (se 1 (by rfl) ⟨2074130, by rfl⟩ : syracuseStep 2765507 = 4148261) B4148261
theorem B1725139 : Blo 1725063 1725139 := bstep (se 1 (by rfl) ⟨1293854, by rfl⟩ : syracuseStep 1725139 = 2587709) B2587709
theorem B1725155 : Blo 1725063 1725155 := bstep (se 1 (by rfl) ⟨1293866, by rfl⟩ : syracuseStep 1725155 = 2587733) B2587733
theorem B3109603 : Blo 1725063 3109603 := bstep (se 1 (by rfl) ⟨2332202, by rfl⟩ : syracuseStep 3109603 = 4664405) B4664405
theorem B2765539 : Blo 1725063 2765539 := bstep (se 1 (by rfl) ⟨2074154, by rfl⟩ : syracuseStep 2765539 = 4148309) B4148309
theorem B4371185 : Blo 1725063 4371185 := bstep (se 2 (by rfl) ⟨1639194, by rfl⟩ : syracuseStep 4371185 = 3278389) B3278389
theorem B1725171 : Blo 1725063 1725171 := bstep (se 1 (by rfl) ⟨1293878, by rfl⟩ : syracuseStep 1725171 = 2587757) B2587757
theorem B1725187 : Blo 1725063 1725187 := bstep (se 1 (by rfl) ⟨1293890, by rfl⟩ : syracuseStep 1725187 = 2587781) B2587781
theorem B1725203 : Blo 1725063 1725203 := bstep (se 1 (by rfl) ⟨1293902, by rfl⟩ : syracuseStep 1725203 = 2587805) B2587805
theorem B2913043 : Blo 1725063 2913043 := bstep (se 1 (by rfl) ⟨2184782, by rfl⟩ : syracuseStep 2913043 = 4369565) B4369565
theorem B1725219 : Blo 1725063 1725219 := bstep (se 1 (by rfl) ⟨1293914, by rfl⟩ : syracuseStep 1725219 = 2587829) B2587829
theorem B2954033 : Blo 1725063 2954033 := bstep (se 2 (by rfl) ⟨1107762, by rfl⟩ : syracuseStep 2954033 = 2215525) B2215525
theorem B1725235 : Blo 1725063 1725235 := bstep (se 1 (by rfl) ⟨1293926, by rfl⟩ : syracuseStep 1725235 = 2587853) B2587853
theorem B1725251 : Blo 1725063 1725251 := bstep (se 1 (by rfl) ⟨1293938, by rfl⟩ : syracuseStep 1725251 = 2587877) B2587877
theorem B1725267 : Blo 1725063 1725267 := bstep (se 1 (by rfl) ⟨1293950, by rfl⟩ : syracuseStep 1725267 = 2587901) B2587901
theorem B1725283 : Blo 1725063 1725283 := bstep (se 1 (by rfl) ⟨1293962, by rfl⟩ : syracuseStep 1725283 = 2587925) B2587925
theorem B24884081 : Blo 1725063 24884081 := bstep (se 2 (by rfl) ⟨9331530, by rfl⟩ : syracuseStep 24884081 = 18663061) B18663061
theorem B1725299 : Blo 1725063 1725299 := bstep (se 1 (by rfl) ⟨1293974, by rfl⟩ : syracuseStep 1725299 = 2587949) B2587949
theorem B1725315 : Blo 1725063 1725315 := bstep (se 1 (by rfl) ⟨1293986, by rfl⟩ : syracuseStep 1725315 = 2587973) B2587973
theorem B1725331 : Blo 1725063 1725331 := bstep (se 1 (by rfl) ⟨1293998, by rfl⟩ : syracuseStep 1725331 = 2587997) B2587997
theorem B2913185 : Blo 1725063 2913185 := bstep (se 2 (by rfl) ⟨1092444, by rfl⟩ : syracuseStep 2913185 = 2184889) B2184889
theorem B1725347 : Blo 1725063 1725347 := bstep (se 1 (by rfl) ⟨1294010, by rfl⟩ : syracuseStep 1725347 = 2588021) B2588021
theorem B1725363 : Blo 1725063 1725363 := bstep (se 1 (by rfl) ⟨1294022, by rfl⟩ : syracuseStep 1725363 = 2588045) B2588045
theorem B1725379 : Blo 1725063 1725379 := bstep (se 1 (by rfl) ⟨1294034, by rfl⟩ : syracuseStep 1725379 = 2588069) B2588069
theorem B1725395 : Blo 1725063 1725395 := bstep (se 1 (by rfl) ⟨1294046, by rfl⟩ : syracuseStep 1725395 = 2588093) B2588093
theorem B1725411 : Blo 1725063 1725411 := bstep (se 1 (by rfl) ⟨1294058, by rfl⟩ : syracuseStep 1725411 = 2588117) B2588117
theorem B1725427 : Blo 1725063 1725427 := bstep (se 1 (by rfl) ⟨1294070, by rfl⟩ : syracuseStep 1725427 = 2588141) B2588141
theorem B1725443 : Blo 1725063 1725443 := bstep (se 1 (by rfl) ⟨1294082, by rfl⟩ : syracuseStep 1725443 = 2588165) B2588165
theorem B2331667 : Blo 1725063 2331667 := bstep (se 1 (by rfl) ⟨1748750, by rfl⟩ : syracuseStep 2331667 = 3497501) B3497501
theorem B1725459 : Blo 1725063 1725459 := bstep (se 1 (by rfl) ⟨1294094, by rfl⟩ : syracuseStep 1725459 = 2588189) B2588189
theorem B2913313 : Blo 1725063 2913313 := bstep (se 2 (by rfl) ⟨1092492, by rfl⟩ : syracuseStep 2913313 = 2184985) B2184985
theorem B1725475 : Blo 1725063 1725475 := bstep (se 1 (by rfl) ⟨1294106, by rfl⟩ : syracuseStep 1725475 = 2588213) B2588213
theorem B1725491 : Blo 1725063 1725491 := bstep (se 1 (by rfl) ⟨1294118, by rfl⟩ : syracuseStep 1725491 = 2588237) B2588237
theorem B1725507 : Blo 1725063 1725507 := bstep (se 1 (by rfl) ⟨1294130, by rfl⟩ : syracuseStep 1725507 = 2588261) B2588261
theorem B2913347 : Blo 1725063 2913347 := bstep (se 1 (by rfl) ⟨2185010, by rfl⟩ : syracuseStep 2913347 = 4370021) B4370021
theorem B1725523 : Blo 1725063 1725523 := bstep (se 1 (by rfl) ⟨1294142, by rfl⟩ : syracuseStep 1725523 = 2588285) B2588285
theorem B13988963 : Blo 1725063 13988963 := bstep (se 1 (by rfl) ⟨10491722, by rfl⟩ : syracuseStep 13988963 = 20983445) B20983445
theorem B1725539 : Blo 1725063 1725539 := bstep (se 1 (by rfl) ⟨1294154, by rfl⟩ : syracuseStep 1725539 = 2588309) B2588309
theorem B4666481 : Blo 1725063 4666481 := bstep (se 2 (by rfl) ⟨1749930, by rfl⟩ : syracuseStep 4666481 = 3499861) B3499861
theorem B1725555 : Blo 1725063 1725555 := bstep (se 1 (by rfl) ⟨1294166, by rfl⟩ : syracuseStep 1725555 = 2588333) B2588333
theorem B1725571 : Blo 1725063 1725571 := bstep (se 1 (by rfl) ⟨1294178, by rfl⟩ : syracuseStep 1725571 = 2588357) B2588357
theorem B1725587 : Blo 1725063 1725587 := bstep (se 1 (by rfl) ⟨1294190, by rfl⟩ : syracuseStep 1725587 = 2588381) B2588381
theorem B1725603 : Blo 1725063 1725603 := bstep (se 1 (by rfl) ⟨1294202, by rfl⟩ : syracuseStep 1725603 = 2588405) B2588405
theorem B8737955 : Blo 1725063 8737955 := bstep (se 1 (by rfl) ⟨6553466, by rfl⟩ : syracuseStep 8737955 = 13106933) B13106933
theorem B1725619 : Blo 1725063 1725619 := bstep (se 1 (by rfl) ⟨1294214, by rfl⟩ : syracuseStep 1725619 = 2588429) B2588429
theorem B1725635 : Blo 1725063 1725635 := bstep (se 1 (by rfl) ⟨1294226, by rfl⟩ : syracuseStep 1725635 = 2588453) B2588453
theorem B2913475 : Blo 1725063 2913475 := bstep (se 1 (by rfl) ⟨2185106, by rfl⟩ : syracuseStep 2913475 = 4370213) B4370213
theorem B6550733 : Blo 1725063 6550733 := bstep (se 3 (by rfl) ⟨1228262, by rfl⟩ : syracuseStep 6550733 = 2456525) B2456525
theorem B1725651 : Blo 1725063 1725651 := bstep (se 1 (by rfl) ⟨1294238, by rfl⟩ : syracuseStep 1725651 = 2588477) B2588477
theorem B2184403 : Blo 1725063 2184403 := bstep (se 1 (by rfl) ⟨1638302, by rfl⟩ : syracuseStep 2184403 = 3276605) B3276605
theorem B1725667 : Blo 1725063 1725667 := bstep (se 1 (by rfl) ⟨1294250, by rfl⟩ : syracuseStep 1725667 = 2588501) B2588501
theorem B1725683 : Blo 1725063 1725683 := bstep (se 1 (by rfl) ⟨1294262, by rfl⟩ : syracuseStep 1725683 = 2588525) B2588525
theorem B1725699 : Blo 1725063 1725699 := bstep (se 1 (by rfl) ⟨1294274, by rfl⟩ : syracuseStep 1725699 = 2588549) B2588549
theorem B1725715 : Blo 1725063 1725715 := bstep (se 1 (by rfl) ⟨1294286, by rfl⟩ : syracuseStep 1725715 = 2588573) B2588573
theorem B1725731 : Blo 1725063 1725731 := bstep (se 1 (by rfl) ⟨1294298, by rfl⟩ : syracuseStep 1725731 = 2588597) B2588597
theorem B1725747 : Blo 1725063 1725747 := bstep (se 1 (by rfl) ⟨1294310, by rfl⟩ : syracuseStep 1725747 = 2588621) B2588621
theorem B2184499 : Blo 1725063 2184499 := bstep (se 1 (by rfl) ⟨1638374, by rfl⟩ : syracuseStep 2184499 = 3276749) B3276749
theorem B1725763 : Blo 1725063 1725763 := bstep (se 1 (by rfl) ⟨1294322, by rfl⟩ : syracuseStep 1725763 = 2588645) B2588645
theorem B2913617 : Blo 1725063 2913617 := bstep (se 2 (by rfl) ⟨1092606, by rfl⟩ : syracuseStep 2913617 = 2185213) B2185213
theorem B1725779 : Blo 1725063 1725779 := bstep (se 1 (by rfl) ⟨1294334, by rfl⟩ : syracuseStep 1725779 = 2588669) B2588669
theorem B1725795 : Blo 1725063 1725795 := bstep (se 1 (by rfl) ⟨1294346, by rfl⟩ : syracuseStep 1725795 = 2588693) B2588693
theorem B18666865 : Blo 1725063 18666865 := bstep (se 2 (by rfl) ⟨7000074, by rfl⟩ : syracuseStep 18666865 = 14000149) B14000149
theorem B1725811 : Blo 1725063 1725811 := bstep (se 1 (by rfl) ⟨1294358, by rfl⟩ : syracuseStep 1725811 = 2588717) B2588717
theorem B1725827 : Blo 1725063 1725827 := bstep (se 1 (by rfl) ⟨1294370, by rfl⟩ : syracuseStep 1725827 = 2588741) B2588741
theorem B1725843 : Blo 1725063 1725843 := bstep (se 1 (by rfl) ⟨1294382, by rfl⟩ : syracuseStep 1725843 = 2588765) B2588765
theorem B1725859 : Blo 1725063 1725859 := bstep (se 1 (by rfl) ⟨1294394, by rfl⟩ : syracuseStep 1725859 = 2588789) B2588789
theorem B1725875 : Blo 1725063 1725875 := bstep (se 1 (by rfl) ⟨1294406, by rfl⟩ : syracuseStep 1725875 = 2588813) B2588813
theorem B2102707 : Blo 1725063 2102707 := bstep (se 1 (by rfl) ⟨1577030, by rfl⟩ : syracuseStep 2102707 = 3154061) B3154061
theorem B1725891 : Blo 1725063 1725891 := bstep (se 1 (by rfl) ⟨1294418, by rfl⟩ : syracuseStep 1725891 = 2588837) B2588837
theorem B2913745 : Blo 1725063 2913745 := bstep (se 2 (by rfl) ⟨1092654, by rfl⟩ : syracuseStep 2913745 = 2185309) B2185309
theorem B1725907 : Blo 1725063 1725907 := bstep (se 1 (by rfl) ⟨1294430, by rfl⟩ : syracuseStep 1725907 = 2588861) B2588861
theorem B1725923 : Blo 1725063 1725923 := bstep (se 1 (by rfl) ⟨1294442, by rfl⟩ : syracuseStep 1725923 = 2588885) B2588885
theorem B1725939 : Blo 1725063 1725939 := bstep (se 1 (by rfl) ⟨1294454, by rfl⟩ : syracuseStep 1725939 = 2588909) B2588909
theorem B2913779 : Blo 1725063 2913779 := bstep (se 1 (by rfl) ⟨2185334, by rfl⟩ : syracuseStep 2913779 = 4370669) B4370669
theorem B1725955 : Blo 1725063 1725955 := bstep (se 1 (by rfl) ⟨1294466, by rfl⟩ : syracuseStep 1725955 = 2588933) B2588933
theorem B1725971 : Blo 1725063 1725971 := bstep (se 1 (by rfl) ⟨1294478, by rfl⟩ : syracuseStep 1725971 = 2588957) B2588957
theorem B44234261 : Blo 1725063 44234261 := bstep (se 6 (by rfl) ⟨1036740, by rfl⟩ : syracuseStep 44234261 = 2073481) B2073481
theorem B1725987 : Blo 1725063 1725987 := bstep (se 1 (by rfl) ⟨1294490, by rfl⟩ : syracuseStep 1725987 = 2588981) B2588981
theorem B1726003 : Blo 1725063 1726003 := bstep (se 1 (by rfl) ⟨1294502, by rfl⟩ : syracuseStep 1726003 = 2589005) B2589005
theorem B1726019 : Blo 1725063 1726019 := bstep (se 1 (by rfl) ⟨1294514, by rfl⟩ : syracuseStep 1726019 = 2589029) B2589029
theorem B11212357 : Blo 1725063 11212357 := bstep (se 4 (by rfl) ⟨1051158, by rfl⟩ : syracuseStep 11212357 = 2102317) B2102317
theorem B4912721 : Blo 1725063 4912721 := bstep (se 2 (by rfl) ⟨1842270, by rfl⟩ : syracuseStep 4912721 = 3684541) B3684541
theorem B1726035 : Blo 1725063 1726035 := bstep (se 1 (by rfl) ⟨1294526, by rfl⟩ : syracuseStep 1726035 = 2589053) B2589053
theorem B1726051 : Blo 1725063 1726051 := bstep (se 1 (by rfl) ⟨1294538, by rfl⟩ : syracuseStep 1726051 = 2589077) B2589077
theorem B1726067 : Blo 1725063 1726067 := bstep (se 1 (by rfl) ⟨1294550, by rfl⟩ : syracuseStep 1726067 = 2589101) B2589101
theorem B2913907 : Blo 1725063 2913907 := bstep (se 1 (by rfl) ⟨2185430, by rfl⟩ : syracuseStep 2913907 = 4370861) B4370861
theorem B1726083 : Blo 1725063 1726083 := bstep (se 1 (by rfl) ⟨1294562, by rfl⟩ : syracuseStep 1726083 = 2589125) B2589125
theorem B4667021 : Blo 1725063 4667021 := bstep (se 3 (by rfl) ⟨875066, by rfl⟩ : syracuseStep 4667021 = 1750133) B1750133
theorem B1726099 : Blo 1725063 1726099 := bstep (se 1 (by rfl) ⟨1294574, by rfl⟩ : syracuseStep 1726099 = 2589149) B2589149
theorem B1726115 : Blo 1725063 1726115 := bstep (se 1 (by rfl) ⟨1294586, by rfl⟩ : syracuseStep 1726115 = 2589173) B2589173
theorem B1726131 : Blo 1725063 1726131 := bstep (se 1 (by rfl) ⟨1294598, by rfl⟩ : syracuseStep 1726131 = 2589197) B2589197
theorem B1726147 : Blo 1725063 1726147 := bstep (se 1 (by rfl) ⟨1294610, by rfl⟩ : syracuseStep 1726147 = 2589221) B2589221
theorem B1726163 : Blo 1725063 1726163 := bstep (se 1 (by rfl) ⟨1294622, by rfl⟩ : syracuseStep 1726163 = 2589245) B2589245
theorem B1726179 : Blo 1725063 1726179 := bstep (se 1 (by rfl) ⟨1294634, by rfl⟩ : syracuseStep 1726179 = 2589269) B2589269
theorem B1726195 : Blo 1725063 1726195 := bstep (se 1 (by rfl) ⟨1294646, by rfl⟩ : syracuseStep 1726195 = 2589293) B2589293
theorem B2914049 : Blo 1725063 2914049 := bstep (se 2 (by rfl) ⟨1092768, by rfl⟩ : syracuseStep 2914049 = 2185537) B2185537
theorem B1726211 : Blo 1725063 1726211 := bstep (se 1 (by rfl) ⟨1294658, by rfl⟩ : syracuseStep 1726211 = 2589317) B2589317
theorem B5822225 : Blo 1725063 5822225 := bstep (se 2 (by rfl) ⟨2183334, by rfl⟩ : syracuseStep 5822225 = 4366669) B4366669
theorem B4912913 : Blo 1725063 4912913 := bstep (se 2 (by rfl) ⟨1842342, by rfl⟩ : syracuseStep 4912913 = 3684685) B3684685
theorem B1726227 : Blo 1725063 1726227 := bstep (se 1 (by rfl) ⟨1294670, by rfl⟩ : syracuseStep 1726227 = 2589341) B2589341
theorem B1726243 : Blo 1725063 1726243 := bstep (se 1 (by rfl) ⟨1294682, by rfl⟩ : syracuseStep 1726243 = 2589365) B2589365
theorem B2184995 : Blo 1725063 2184995 := bstep (se 1 (by rfl) ⟨1638746, by rfl⟩ : syracuseStep 2184995 = 3277493) B3277493
theorem B1726259 : Blo 1725063 1726259 := bstep (se 1 (by rfl) ⟨1294694, by rfl⟩ : syracuseStep 1726259 = 2589389) B2589389
theorem B1726275 : Blo 1725063 1726275 := bstep (se 1 (by rfl) ⟨1294706, by rfl⟩ : syracuseStep 1726275 = 2589413) B2589413
theorem B14751557 : Blo 1725063 14751557 := bstep (se 4 (by rfl) ⟨1382958, by rfl⟩ : syracuseStep 14751557 = 2765917) B2765917
theorem B1726291 : Blo 1725063 1726291 := bstep (se 1 (by rfl) ⟨1294718, by rfl⟩ : syracuseStep 1726291 = 2589437) B2589437
theorem B1726307 : Blo 1725063 1726307 := bstep (se 1 (by rfl) ⟨1294730, by rfl⟩ : syracuseStep 1726307 = 2589461) B2589461
theorem B1726323 : Blo 1725063 1726323 := bstep (se 1 (by rfl) ⟨1294742, by rfl⟩ : syracuseStep 1726323 = 2589485) B2589485
theorem B2914177 : Blo 1725063 2914177 := bstep (se 2 (by rfl) ⟨1092816, by rfl⟩ : syracuseStep 2914177 = 2185633) B2185633
theorem B1726339 : Blo 1725063 1726339 := bstep (se 1 (by rfl) ⟨1294754, by rfl⟩ : syracuseStep 1726339 = 2589509) B2589509
theorem B1726355 : Blo 1725063 1726355 := bstep (se 1 (by rfl) ⟨1294766, by rfl⟩ : syracuseStep 1726355 = 2589533) B2589533
theorem B1726371 : Blo 1725063 1726371 := bstep (se 1 (by rfl) ⟨1294778, by rfl⟩ : syracuseStep 1726371 = 2589557) B2589557
theorem B2914211 : Blo 1725063 2914211 := bstep (se 1 (by rfl) ⟨2185658, by rfl⟩ : syracuseStep 2914211 = 4371317) B4371317
theorem B1726387 : Blo 1725063 1726387 := bstep (se 1 (by rfl) ⟨1294790, by rfl⟩ : syracuseStep 1726387 = 2589581) B2589581
theorem B1726403 : Blo 1725063 1726403 := bstep (se 1 (by rfl) ⟨1294802, by rfl⟩ : syracuseStep 1726403 = 2589605) B2589605
theorem B8738765 : Blo 1725063 8738765 := bstep (se 3 (by rfl) ⟨1638518, by rfl⟩ : syracuseStep 8738765 = 3277037) B3277037
theorem B1726419 : Blo 1725063 1726419 := bstep (se 1 (by rfl) ⟨1294814, by rfl⟩ : syracuseStep 1726419 = 2589629) B2589629
theorem B1726435 : Blo 1725063 1726435 := bstep (se 1 (by rfl) ⟨1294826, by rfl⟩ : syracuseStep 1726435 = 2589653) B2589653
theorem B1726451 : Blo 1725063 1726451 := bstep (se 1 (by rfl) ⟨1294838, by rfl⟩ : syracuseStep 1726451 = 2589677) B2589677
theorem B1726467 : Blo 1725063 1726467 := bstep (se 1 (by rfl) ⟨1294850, by rfl⟩ : syracuseStep 1726467 = 2589701) B2589701
theorem B1726483 : Blo 1725063 1726483 := bstep (se 1 (by rfl) ⟨1294862, by rfl⟩ : syracuseStep 1726483 = 2589725) B2589725
theorem B1726499 : Blo 1725063 1726499 := bstep (se 1 (by rfl) ⟨1294874, by rfl⟩ : syracuseStep 1726499 = 2589749) B2589749
theorem B2914339 : Blo 1725063 2914339 := bstep (se 1 (by rfl) ⟨2185754, by rfl⟩ : syracuseStep 2914339 = 4371509) B4371509
theorem B1726515 : Blo 1725063 1726515 := bstep (se 1 (by rfl) ⟨1294886, by rfl⟩ : syracuseStep 1726515 = 2589773) B2589773
theorem B1726531 : Blo 1725063 1726531 := bstep (se 1 (by rfl) ⟨1294898, by rfl⟩ : syracuseStep 1726531 = 2589797) B2589797
theorem B1726547 : Blo 1725063 1726547 := bstep (se 1 (by rfl) ⟨1294910, by rfl⟩ : syracuseStep 1726547 = 2589821) B2589821
theorem B1726563 : Blo 1725063 1726563 := bstep (se 1 (by rfl) ⟨1294922, by rfl⟩ : syracuseStep 1726563 = 2589845) B2589845
theorem B1726579 : Blo 1725063 1726579 := bstep (se 1 (by rfl) ⟨1294934, by rfl⟩ : syracuseStep 1726579 = 2589869) B2589869
theorem B1726595 : Blo 1725063 1726595 := bstep (se 1 (by rfl) ⟨1294946, by rfl⟩ : syracuseStep 1726595 = 2589893) B2589893
theorem B1726611 : Blo 1725063 1726611 := bstep (se 1 (by rfl) ⟨1294958, by rfl⟩ : syracuseStep 1726611 = 2589917) B2589917
theorem B1726627 : Blo 1725063 1726627 := bstep (se 1 (by rfl) ⟨1294970, by rfl⟩ : syracuseStep 1726627 = 2589941) B2589941
theorem B1726643 : Blo 1725063 1726643 := bstep (se 1 (by rfl) ⟨1294982, by rfl⟩ : syracuseStep 1726643 = 2589965) B2589965
theorem B1726659 : Blo 1725063 1726659 := bstep (se 1 (by rfl) ⟨1294994, by rfl⟩ : syracuseStep 1726659 = 2589989) B2589989
theorem B6224077 : Blo 1725063 6224077 := bstep (se 3 (by rfl) ⟨1167014, by rfl⟩ : syracuseStep 6224077 = 2334029) B2334029
theorem B1726675 : Blo 1725063 1726675 := bstep (se 1 (by rfl) ⟨1295006, by rfl⟩ : syracuseStep 1726675 = 2590013) B2590013
theorem B1034926307 : Blo 1725063 1034926307 := bstep (se 1 (by rfl) ⟨776194730, by rfl⟩ : syracuseStep 1034926307 = 1552389461) B1552389461
theorem B3111139 : Blo 1725063 3111139 := bstep (se 1 (by rfl) ⟨2333354, by rfl⟩ : syracuseStep 3111139 = 4666709) B4666709
theorem B1726691 : Blo 1725063 1726691 := bstep (se 1 (by rfl) ⟨1295018, by rfl⟩ : syracuseStep 1726691 = 2590037) B2590037
theorem B1726707 : Blo 1725063 1726707 := bstep (se 1 (by rfl) ⟨1295030, by rfl⟩ : syracuseStep 1726707 = 2590061) B2590061
theorem B1726723 : Blo 1725063 1726723 := bstep (se 1 (by rfl) ⟨1295042, by rfl⟩ : syracuseStep 1726723 = 2590085) B2590085
theorem B1726739 : Blo 1725063 1726739 := bstep (se 1 (by rfl) ⟨1295054, by rfl⟩ : syracuseStep 1726739 = 2590109) B2590109
theorem B3111203 : Blo 1725063 3111203 := bstep (se 1 (by rfl) ⟨2333402, by rfl⟩ : syracuseStep 3111203 = 4666805) B4666805
theorem B1726755 : Blo 1725063 1726755 := bstep (se 1 (by rfl) ⟨1295066, by rfl⟩ : syracuseStep 1726755 = 2590133) B2590133
theorem B5822765 : Blo 1725063 5822765 := bstep (se 3 (by rfl) ⟨1091768, by rfl⟩ : syracuseStep 5822765 = 2183537) B2183537
theorem B1726771 : Blo 1725063 1726771 := bstep (se 1 (by rfl) ⟨1295078, by rfl⟩ : syracuseStep 1726771 = 2590157) B2590157
theorem B1726787 : Blo 1725063 1726787 := bstep (se 1 (by rfl) ⟨1295090, by rfl⟩ : syracuseStep 1726787 = 2590181) B2590181
theorem B1726803 : Blo 1725063 1726803 := bstep (se 1 (by rfl) ⟨1295102, by rfl⟩ : syracuseStep 1726803 = 2590205) B2590205
theorem B5822819 : Blo 1725063 5822819 := bstep (se 1 (by rfl) ⟨4367114, by rfl⟩ : syracuseStep 5822819 = 8734229) B8734229
theorem B1726819 : Blo 1725063 1726819 := bstep (se 1 (by rfl) ⟨1295114, by rfl⟩ : syracuseStep 1726819 = 2590229) B2590229
theorem B47356273 : Blo 1725063 47356273 := bstep (se 2 (by rfl) ⟨17758602, by rfl⟩ : syracuseStep 47356273 = 35517205) B35517205
theorem B1726835 : Blo 1725063 1726835 := bstep (se 1 (by rfl) ⟨1295126, by rfl⟩ : syracuseStep 1726835 = 2590253) B2590253
theorem B5527939 : Blo 1725063 5527939 := bstep (se 1 (by rfl) ⟨4145954, by rfl⟩ : syracuseStep 5527939 = 8291909) B8291909
theorem B1726851 : Blo 1725063 1726851 := bstep (se 1 (by rfl) ⟨1295138, by rfl⟩ : syracuseStep 1726851 = 2590277) B2590277
theorem B1726867 : Blo 1725063 1726867 := bstep (se 1 (by rfl) ⟨1295150, by rfl⟩ : syracuseStep 1726867 = 2590301) B2590301
theorem B1726883 : Blo 1725063 1726883 := bstep (se 1 (by rfl) ⟨1295162, by rfl⟩ : syracuseStep 1726883 = 2590325) B2590325
theorem B3881393 : Blo 1725063 3881393 := bstep (se 2 (by rfl) ⟨1455522, by rfl⟩ : syracuseStep 3881393 = 2911045) B2911045
theorem B1726899 : Blo 1725063 1726899 := bstep (se 1 (by rfl) ⟨1295174, by rfl⟩ : syracuseStep 1726899 = 2590349) B2590349
theorem B3881411 : Blo 1725063 3881411 := bstep (se 1 (by rfl) ⟨2911058, by rfl⟩ : syracuseStep 3881411 = 5822117) B5822117
theorem B1726915 : Blo 1725063 1726915 := bstep (se 1 (by rfl) ⟨1295186, by rfl⟩ : syracuseStep 1726915 = 2590373) B2590373
theorem B1726931 : Blo 1725063 1726931 := bstep (se 1 (by rfl) ⟨1295198, by rfl⟩ : syracuseStep 1726931 = 2590397) B2590397
theorem B1726947 : Blo 1725063 1726947 := bstep (se 1 (by rfl) ⟨1295210, by rfl⟩ : syracuseStep 1726947 = 2590421) B2590421
theorem B2185699 : Blo 1725063 2185699 := bstep (se 1 (by rfl) ⟨1639274, by rfl⟩ : syracuseStep 2185699 = 3278549) B3278549
theorem B1726963 : Blo 1725063 1726963 := bstep (se 1 (by rfl) ⟨1295222, by rfl⟩ : syracuseStep 1726963 = 2590445) B2590445
theorem B1726979 : Blo 1725063 1726979 := bstep (se 1 (by rfl) ⟨1295234, by rfl⟩ : syracuseStep 1726979 = 2590469) B2590469
theorem B1726995 : Blo 1725063 1726995 := bstep (se 1 (by rfl) ⟨1295246, by rfl⟩ : syracuseStep 1726995 = 2590493) B2590493
theorem B1727011 : Blo 1725063 1727011 := bstep (se 1 (by rfl) ⟨1295258, by rfl⟩ : syracuseStep 1727011 = 2590517) B2590517
theorem B1727027 : Blo 1725063 1727027 := bstep (se 1 (by rfl) ⟨1295270, by rfl⟩ : syracuseStep 1727027 = 2590541) B2590541
theorem B1727043 : Blo 1725063 1727043 := bstep (se 1 (by rfl) ⟨1295282, by rfl⟩ : syracuseStep 1727043 = 2590565) B2590565
theorem B2185795 : Blo 1725063 2185795 := bstep (se 1 (by rfl) ⟨1639346, by rfl⟩ : syracuseStep 2185795 = 3278693) B3278693
theorem B1727059 : Blo 1725063 1727059 := bstep (se 1 (by rfl) ⟨1295294, by rfl⟩ : syracuseStep 1727059 = 2590589) B2590589
theorem B5823089 : Blo 1725063 5823089 := bstep (se 2 (by rfl) ⟨2183658, by rfl⟩ : syracuseStep 5823089 = 4367317) B4367317
theorem B72841841 : Blo 1725063 72841841 := bstep (se 2 (by rfl) ⟨27315690, by rfl⟩ : syracuseStep 72841841 = 54631381) B54631381
theorem B10500749 : Blo 1725063 10500749 := bstep (se 3 (by rfl) ⟨1968890, by rfl⟩ : syracuseStep 10500749 = 3937781) B3937781
theorem B3685027 : Blo 1725063 3685027 := bstep (se 1 (by rfl) ⟨2763770, by rfl⟩ : syracuseStep 3685027 = 5527541) B5527541
theorem B3881681 : Blo 1725063 3881681 := bstep (se 2 (by rfl) ⟨1455630, by rfl⟩ : syracuseStep 3881681 = 2911261) B2911261
theorem B3275473 : Blo 1725063 3275473 := bstep (se 2 (by rfl) ⟨1228302, by rfl⟩ : syracuseStep 3275473 = 2456605) B2456605
theorem B3881699 : Blo 1725063 3881699 := bstep (se 1 (by rfl) ⟨2911274, by rfl⟩ : syracuseStep 3881699 = 5822549) B5822549
theorem B4913905 : Blo 1725063 4913905 := bstep (se 2 (by rfl) ⟨1842714, by rfl⟩ : syracuseStep 4913905 = 3685429) B3685429
theorem B5528387 : Blo 1725063 5528387 := bstep (se 1 (by rfl) ⟨4146290, by rfl⟩ : syracuseStep 5528387 = 8292581) B8292581
theorem B3275633 : Blo 1725063 3275633 := bstep (se 2 (by rfl) ⟨1228362, by rfl⟩ : syracuseStep 3275633 = 2456725) B2456725
theorem B2456497 : Blo 1725063 2456497 := bstep (se 2 (by rfl) ⟨921186, by rfl⟩ : syracuseStep 2456497 = 1842373) B1842373
theorem B2587601 : Blo 1725063 2587601 := bstep (se 2 (by rfl) ⟨970350, by rfl⟩ : syracuseStep 2587601 = 1940701) B1940701
theorem B2587619 : Blo 1725063 2587619 := bstep (se 1 (by rfl) ⟨1940714, by rfl⟩ : syracuseStep 2587619 = 3881429) B3881429
theorem B3881969 : Blo 1725063 3881969 := bstep (se 2 (by rfl) ⟨1455738, by rfl⟩ : syracuseStep 3881969 = 2911477) B2911477
theorem B2333683 : Blo 1725063 2333683 := bstep (se 1 (by rfl) ⟨1750262, by rfl⟩ : syracuseStep 2333683 = 3500525) B3500525
theorem B2587649 : Blo 1725063 2587649 := bstep (se 2 (by rfl) ⟨970368, by rfl⟩ : syracuseStep 2587649 = 1940737) B1940737
theorem B3881987 : Blo 1725063 3881987 := bstep (se 1 (by rfl) ⟨2911490, by rfl⟩ : syracuseStep 3881987 = 5822981) B5822981
theorem B4914179 : Blo 1725063 4914179 := bstep (se 1 (by rfl) ⟨3685634, by rfl⟩ : syracuseStep 4914179 = 7371269) B7371269
theorem B2587667 : Blo 1725063 2587667 := bstep (se 1 (by rfl) ⟨1940750, by rfl⟩ : syracuseStep 2587667 = 3881501) B3881501
theorem B2587697 : Blo 1725063 2587697 := bstep (se 2 (by rfl) ⟨970386, by rfl⟩ : syracuseStep 2587697 = 1940773) B1940773
theorem B2587715 : Blo 1725063 2587715 := bstep (se 1 (by rfl) ⟨1940786, by rfl⟩ : syracuseStep 2587715 = 3881573) B3881573
theorem B2587745 : Blo 1725063 2587745 := bstep (se 2 (by rfl) ⟨970404, by rfl⟩ : syracuseStep 2587745 = 1940809) B1940809
theorem B2587763 : Blo 1725063 2587763 := bstep (se 1 (by rfl) ⟨1940822, by rfl⟩ : syracuseStep 2587763 = 3881645) B3881645
theorem B5823629 : Blo 1725063 5823629 := bstep (se 3 (by rfl) ⟨1091930, by rfl⟩ : syracuseStep 5823629 = 2183861) B2183861
theorem B2587793 : Blo 1725063 2587793 := bstep (se 2 (by rfl) ⟨970422, by rfl⟩ : syracuseStep 2587793 = 1940845) B1940845
theorem B2587811 : Blo 1725063 2587811 := bstep (se 1 (by rfl) ⟨1940858, by rfl⟩ : syracuseStep 2587811 = 3881717) B3881717
theorem B2587841 : Blo 1725063 2587841 := bstep (se 2 (by rfl) ⟨970440, by rfl⟩ : syracuseStep 2587841 = 1940881) B1940881
theorem B5823683 : Blo 1725063 5823683 := bstep (se 1 (by rfl) ⟨4367762, by rfl⟩ : syracuseStep 5823683 = 8735525) B8735525
theorem B4914371 : Blo 1725063 4914371 := bstep (se 1 (by rfl) ⟨3685778, by rfl⟩ : syracuseStep 4914371 = 7371557) B7371557
theorem B5250253 : Blo 1725063 5250253 := bstep (se 3 (by rfl) ⟨984422, by rfl⟩ : syracuseStep 5250253 = 1968845) B1968845
theorem B2587859 : Blo 1725063 2587859 := bstep (se 1 (by rfl) ⟨1940894, by rfl⟩ : syracuseStep 2587859 = 3881789) B3881789
theorem B2587889 : Blo 1725063 2587889 := bstep (se 2 (by rfl) ⟨970458, by rfl⟩ : syracuseStep 2587889 = 1940917) B1940917
theorem B2456833 : Blo 1725063 2456833 := bstep (se 2 (by rfl) ⟨921312, by rfl⟩ : syracuseStep 2456833 = 1842625) B1842625
theorem B2587907 : Blo 1725063 2587907 := bstep (se 1 (by rfl) ⟨1940930, by rfl⟩ : syracuseStep 2587907 = 3881861) B3881861
theorem B3276035 : Blo 1725063 3276035 := bstep (se 1 (by rfl) ⟨2457026, by rfl⟩ : syracuseStep 3276035 = 4914053) B4914053
theorem B6552845 : Blo 1725063 6552845 := bstep (se 3 (by rfl) ⟨1228658, by rfl⟩ : syracuseStep 6552845 = 2457317) B2457317
theorem B16579853 : Blo 1725063 16579853 := bstep (se 3 (by rfl) ⟨3108722, by rfl⟩ : syracuseStep 16579853 = 6217445) B6217445
theorem B3882257 : Blo 1725063 3882257 := bstep (se 2 (by rfl) ⟨1455846, by rfl⟩ : syracuseStep 3882257 = 2911693) B2911693
theorem B1940755 : Blo 1725063 1940755 := bstep (se 1 (by rfl) ⟨1455566, by rfl⟩ : syracuseStep 1940755 = 2911133) B2911133
theorem B2587937 : Blo 1725063 2587937 := bstep (se 2 (by rfl) ⟨970476, by rfl⟩ : syracuseStep 2587937 = 1940953) B1940953
theorem B3882275 : Blo 1725063 3882275 := bstep (se 1 (by rfl) ⟨2911706, by rfl⟩ : syracuseStep 3882275 = 5823413) B5823413
theorem B2587955 : Blo 1725063 2587955 := bstep (se 1 (by rfl) ⟨1940966, by rfl⟩ : syracuseStep 2587955 = 3881933) B3881933
theorem B2587985 : Blo 1725063 2587985 := bstep (se 2 (by rfl) ⟨970494, by rfl⟩ : syracuseStep 2587985 = 1940989) B1940989
theorem B2588003 : Blo 1725063 2588003 := bstep (se 1 (by rfl) ⟨1941002, by rfl⟩ : syracuseStep 2588003 = 3882005) B3882005
theorem B3685745 : Blo 1725063 3685745 := bstep (se 2 (by rfl) ⟨1382154, by rfl⟩ : syracuseStep 3685745 = 2764309) B2764309
theorem B9829745 : Blo 1725063 9829745 := bstep (se 2 (by rfl) ⟨3686154, by rfl⟩ : syracuseStep 9829745 = 7372309) B7372309
theorem B2588033 : Blo 1725063 2588033 := bstep (se 2 (by rfl) ⟨970512, by rfl⟩ : syracuseStep 2588033 = 1941025) B1941025
theorem B3497347 : Blo 1725063 3497347 := bstep (se 1 (by rfl) ⟨2623010, by rfl⟩ : syracuseStep 3497347 = 5246021) B5246021
theorem B2588051 : Blo 1725063 2588051 := bstep (se 1 (by rfl) ⟨1941038, by rfl⟩ : syracuseStep 2588051 = 3882077) B3882077
theorem B1940899 : Blo 1725063 1940899 := bstep (se 1 (by rfl) ⟨1455674, by rfl⟩ : syracuseStep 1940899 = 2911349) B2911349
theorem B2588081 : Blo 1725063 2588081 := bstep (se 2 (by rfl) ⟨970530, by rfl⟩ : syracuseStep 2588081 = 1941061) B1941061
theorem B2588099 : Blo 1725063 2588099 := bstep (se 1 (by rfl) ⟨1941074, by rfl⟩ : syracuseStep 2588099 = 3882149) B3882149
theorem B6995405 : Blo 1725063 6995405 := bstep (se 3 (by rfl) ⟨1311638, by rfl⟩ : syracuseStep 6995405 = 2623277) B2623277
theorem B5823953 : Blo 1725063 5823953 := bstep (se 2 (by rfl) ⟨2183982, by rfl⟩ : syracuseStep 5823953 = 4367965) B4367965
theorem B2588129 : Blo 1725063 2588129 := bstep (se 2 (by rfl) ⟨970548, by rfl⟩ : syracuseStep 2588129 = 1941097) B1941097
theorem B2244067 : Blo 1725063 2244067 := bstep (se 1 (by rfl) ⟨1683050, by rfl⟩ : syracuseStep 2244067 = 3366101) B3366101
theorem B2588147 : Blo 1725063 2588147 := bstep (se 1 (by rfl) ⟨1941110, by rfl⟩ : syracuseStep 2588147 = 3882221) B3882221
theorem B2588177 : Blo 1725063 2588177 := bstep (se 2 (by rfl) ⟨970566, by rfl⟩ : syracuseStep 2588177 = 1941133) B1941133
theorem B9960995 : Blo 1725063 9960995 := bstep (se 1 (by rfl) ⟨7470746, by rfl⟩ : syracuseStep 9960995 = 14941493) B14941493
theorem B2588195 : Blo 1725063 2588195 := bstep (se 1 (by rfl) ⟨1941146, by rfl⟩ : syracuseStep 2588195 = 3882293) B3882293
theorem B3882545 : Blo 1725063 3882545 := bstep (se 2 (by rfl) ⟨1455954, by rfl⟩ : syracuseStep 3882545 = 2911909) B2911909
theorem B1941043 : Blo 1725063 1941043 := bstep (se 1 (by rfl) ⟨1455782, by rfl⟩ : syracuseStep 1941043 = 2911565) B2911565
theorem B2588225 : Blo 1725063 2588225 := bstep (se 2 (by rfl) ⟨970584, by rfl⟩ : syracuseStep 2588225 = 1941169) B1941169
theorem B3882563 : Blo 1725063 3882563 := bstep (se 1 (by rfl) ⟨2911922, by rfl⟩ : syracuseStep 3882563 = 5823845) B5823845
theorem B2588243 : Blo 1725063 2588243 := bstep (se 1 (by rfl) ⟨1941182, by rfl⟩ : syracuseStep 2588243 = 3882365) B3882365
theorem B1842787 : Blo 1725063 1842787 := bstep (se 1 (by rfl) ⟨1382090, by rfl⟩ : syracuseStep 1842787 = 2764181) B2764181
theorem B2588273 : Blo 1725063 2588273 := bstep (se 2 (by rfl) ⟨970602, by rfl⟩ : syracuseStep 2588273 = 1941205) B1941205
theorem B2588291 : Blo 1725063 2588291 := bstep (se 1 (by rfl) ⟨1941218, by rfl⟩ : syracuseStep 2588291 = 3882437) B3882437
theorem B5250691 : Blo 1725063 5250691 := bstep (se 1 (by rfl) ⟨3938018, by rfl⟩ : syracuseStep 5250691 = 7876037) B7876037
theorem B2588321 : Blo 1725063 2588321 := bstep (se 2 (by rfl) ⟨970620, by rfl⟩ : syracuseStep 2588321 = 1941241) B1941241
theorem B2588339 : Blo 1725063 2588339 := bstep (se 1 (by rfl) ⟨1941254, by rfl⟩ : syracuseStep 2588339 = 3882509) B3882509
theorem B1941187 : Blo 1725063 1941187 := bstep (se 1 (by rfl) ⟨1455890, by rfl⟩ : syracuseStep 1941187 = 2911781) B2911781
theorem B2588369 : Blo 1725063 2588369 := bstep (se 2 (by rfl) ⟨970638, by rfl⟩ : syracuseStep 2588369 = 1941277) B1941277
theorem B2588387 : Blo 1725063 2588387 := bstep (se 1 (by rfl) ⟨1941290, by rfl⟩ : syracuseStep 2588387 = 3882581) B3882581
theorem B2588417 : Blo 1725063 2588417 := bstep (se 2 (by rfl) ⟨970656, by rfl⟩ : syracuseStep 2588417 = 1941313) B1941313
theorem B2588435 : Blo 1725063 2588435 := bstep (se 1 (by rfl) ⟨1941326, by rfl⟩ : syracuseStep 2588435 = 3882653) B3882653
theorem B2588465 : Blo 1725063 2588465 := bstep (se 2 (by rfl) ⟨970674, by rfl⟩ : syracuseStep 2588465 = 1941349) B1941349
theorem B2588483 : Blo 1725063 2588483 := bstep (se 1 (by rfl) ⟨1941362, by rfl⟩ : syracuseStep 2588483 = 3882725) B3882725
theorem B3882833 : Blo 1725063 3882833 := bstep (se 2 (by rfl) ⟨1456062, by rfl⟩ : syracuseStep 3882833 = 2912125) B2912125
theorem B2457425 : Blo 1725063 2457425 := bstep (se 2 (by rfl) ⟨921534, by rfl⟩ : syracuseStep 2457425 = 1843069) B1843069
theorem B1941331 : Blo 1725063 1941331 := bstep (se 1 (by rfl) ⟨1455998, by rfl⟩ : syracuseStep 1941331 = 2911997) B2911997
theorem B2588513 : Blo 1725063 2588513 := bstep (se 2 (by rfl) ⟨970692, by rfl⟩ : syracuseStep 2588513 = 1941385) B1941385
theorem B3882851 : Blo 1725063 3882851 := bstep (se 1 (by rfl) ⟨2912138, by rfl⟩ : syracuseStep 3882851 = 5824277) B5824277
theorem B3686257 : Blo 1725063 3686257 := bstep (se 2 (by rfl) ⟨1382346, by rfl⟩ : syracuseStep 3686257 = 2764693) B2764693
theorem B2588531 : Blo 1725063 2588531 := bstep (se 1 (by rfl) ⟨1941398, by rfl⟩ : syracuseStep 2588531 = 3882797) B3882797
theorem B2588561 : Blo 1725063 2588561 := bstep (se 2 (by rfl) ⟨970710, by rfl⟩ : syracuseStep 2588561 = 1941421) B1941421
theorem B2588579 : Blo 1725063 2588579 := bstep (se 1 (by rfl) ⟨1941434, by rfl⟩ : syracuseStep 2588579 = 3882869) B3882869
theorem B2588609 : Blo 1725063 2588609 := bstep (se 2 (by rfl) ⟨970728, by rfl⟩ : syracuseStep 2588609 = 1941457) B1941457
theorem B2588627 : Blo 1725063 2588627 := bstep (se 1 (by rfl) ⟨1941470, by rfl⟩ : syracuseStep 2588627 = 3882941) B3882941
theorem B1941475 : Blo 1725063 1941475 := bstep (se 1 (by rfl) ⟨1456106, by rfl⟩ : syracuseStep 1941475 = 2912213) B2912213
theorem B3366883 : Blo 1725063 3366883 := bstep (se 1 (by rfl) ⟨2525162, by rfl⟩ : syracuseStep 3366883 = 5050325) B5050325
theorem B5824493 : Blo 1725063 5824493 := bstep (se 3 (by rfl) ⟨1092092, by rfl⟩ : syracuseStep 5824493 = 2184185) B2184185
theorem B4915181 : Blo 1725063 4915181 := bstep (se 3 (by rfl) ⟨921596, by rfl⟩ : syracuseStep 4915181 = 1843193) B1843193
theorem B2588657 : Blo 1725063 2588657 := bstep (se 2 (by rfl) ⟨970746, by rfl⟩ : syracuseStep 2588657 = 1941493) B1941493
theorem B3686411 : Blo 1725063 3686411 := bstep (se 1 (by rfl) ⟨2764808, by rfl⟩ : syracuseStep 3686411 = 5529617) B5529617
theorem B3883031 : Blo 1725063 3883031 := bstep (se 1 (by rfl) ⟨2912273, by rfl⟩ : syracuseStep 3883031 = 5824547) B5824547
theorem B1941547 : Blo 1725063 1941547 := bstep (se 1 (by rfl) ⟨1456160, by rfl⟩ : syracuseStep 1941547 = 2912321) B2912321
theorem B6217793 : Blo 1725063 6217793 := bstep (se 2 (by rfl) ⟨2331672, by rfl⟩ : syracuseStep 6217793 = 4663345) B4663345
theorem B2588747 : Blo 1725063 2588747 := bstep (se 1 (by rfl) ⟨1941560, by rfl⟩ : syracuseStep 2588747 = 3883121) B3883121
theorem B2588759 : Blo 1725063 2588759 := bstep (se 1 (by rfl) ⟨1941569, by rfl⟩ : syracuseStep 2588759 = 3883139) B3883139
theorem B5824601 : Blo 1725063 5824601 := bstep (se 2 (by rfl) ⟨2184225, by rfl⟩ : syracuseStep 5824601 = 4368451) B4368451
theorem B1941655 : Blo 1725063 1941655 := bstep (se 1 (by rfl) ⟨1456241, by rfl⟩ : syracuseStep 1941655 = 2912483) B2912483
theorem B2588825 : Blo 1725063 2588825 := bstep (se 2 (by rfl) ⟨970809, by rfl⟩ : syracuseStep 2588825 = 1941619) B1941619
theorem B3883211 : Blo 1725063 3883211 := bstep (se 1 (by rfl) ⟨2912408, by rfl⟩ : syracuseStep 3883211 = 5824817) B5824817
theorem B6553817 : Blo 1725063 6553817 := bstep (se 2 (by rfl) ⟨2457681, by rfl⟩ : syracuseStep 6553817 = 4915363) B4915363
theorem B3883265 : Blo 1725063 3883265 := bstep (se 2 (by rfl) ⟨1456224, by rfl⟩ : syracuseStep 3883265 = 2912449) B2912449
theorem B2588939 : Blo 1725063 2588939 := bstep (se 1 (by rfl) ⟨1941704, by rfl⟩ : syracuseStep 2588939 = 3883409) B3883409
theorem B8298769 : Blo 1725063 8298769 := bstep (se 2 (by rfl) ⟨3112038, by rfl⟩ : syracuseStep 8298769 = 6224077) B6224077
theorem B2588951 : Blo 1725063 2588951 := bstep (se 1 (by rfl) ⟨1941713, by rfl⟩ : syracuseStep 2588951 = 3883427) B3883427
theorem B1941835 : Blo 1725063 1941835 := bstep (se 1 (by rfl) ⟨1456376, by rfl⟩ : syracuseStep 1941835 = 2912753) B2912753
theorem B8741195 : Blo 1725063 8741195 := bstep (se 1 (by rfl) ⟨6555896, by rfl⟩ : syracuseStep 8741195 = 13111793) B13111793
theorem B2589017 : Blo 1725063 2589017 := bstep (se 2 (by rfl) ⟨970881, by rfl⟩ : syracuseStep 2589017 = 1941763) B1941763
theorem B1843607 : Blo 1725063 1843607 := bstep (se 1 (by rfl) ⟨1382705, by rfl⟩ : syracuseStep 1843607 = 2765411) B2765411
theorem B3277235 : Blo 1725063 3277235 := bstep (se 1 (by rfl) ⟨2457926, by rfl⟩ : syracuseStep 3277235 = 4915853) B4915853
theorem B1941943 : Blo 1725063 1941943 := bstep (se 1 (by rfl) ⟨1456457, by rfl⟩ : syracuseStep 1941943 = 2912915) B2912915
theorem B2589131 : Blo 1725063 2589131 := bstep (se 1 (by rfl) ⟨1941848, by rfl⟩ : syracuseStep 2589131 = 3883697) B3883697
theorem B2589143 : Blo 1725063 2589143 := bstep (se 1 (by rfl) ⟨1941857, by rfl⟩ : syracuseStep 2589143 = 3883715) B3883715
theorem B3883481 : Blo 1725063 3883481 := bstep (se 2 (by rfl) ⟨1456305, by rfl⟩ : syracuseStep 3883481 = 2912611) B2912611
theorem B3277273 : Blo 1725063 3277273 := bstep (se 2 (by rfl) ⟨1228977, by rfl⟩ : syracuseStep 3277273 = 2457955) B2457955
theorem B9830929 : Blo 1725063 9830929 := bstep (se 2 (by rfl) ⟨3686598, by rfl⟩ : syracuseStep 9830929 = 7373197) B7373197
theorem B6554135 : Blo 1725063 6554135 := bstep (se 1 (by rfl) ⟨4915601, by rfl⟩ : syracuseStep 6554135 = 9831203) B9831203
theorem B2589209 : Blo 1725063 2589209 := bstep (se 2 (by rfl) ⟨970953, by rfl⟩ : syracuseStep 2589209 = 1941907) B1941907
theorem B3883571 : Blo 1725063 3883571 := bstep (se 1 (by rfl) ⟨2912678, by rfl⟩ : syracuseStep 3883571 = 5825357) B5825357
theorem B16589387 : Blo 1725063 16589387 := bstep (se 1 (by rfl) ⟨12442040, by rfl⟩ : syracuseStep 16589387 = 24884081) B24884081
theorem B3883607 : Blo 1725063 3883607 := bstep (se 1 (by rfl) ⟨2912705, by rfl⟩ : syracuseStep 3883607 = 5825411) B5825411
theorem B2245207 : Blo 1725063 2245207 := bstep (se 1 (by rfl) ⟨1683905, by rfl⟩ : syracuseStep 2245207 = 3367811) B3367811
theorem B1942123 : Blo 1725063 1942123 := bstep (se 1 (by rfl) ⟨1456592, by rfl⟩ : syracuseStep 1942123 = 2913185) B2913185
theorem B2589323 : Blo 1725063 2589323 := bstep (se 1 (by rfl) ⟨1941992, by rfl⟩ : syracuseStep 2589323 = 3883985) B3883985
theorem B2589335 : Blo 1725063 2589335 := bstep (se 1 (by rfl) ⟨1942001, by rfl⟩ : syracuseStep 2589335 = 3884003) B3884003
theorem B1942231 : Blo 1725063 1942231 := bstep (se 1 (by rfl) ⟨1456673, by rfl⟩ : syracuseStep 1942231 = 2913347) B2913347
theorem B2589401 : Blo 1725063 2589401 := bstep (se 2 (by rfl) ⟨971025, by rfl⟩ : syracuseStep 2589401 = 1942051) B1942051
theorem B3883787 : Blo 1725063 3883787 := bstep (se 1 (by rfl) ⟨2912840, by rfl⟩ : syracuseStep 3883787 = 5825681) B5825681
theorem B3736343 : Blo 1725063 3736343 := bstep (se 1 (by rfl) ⟨2802257, by rfl⟩ : syracuseStep 3736343 = 5604515) B5604515
theorem B5825303 : Blo 1725063 5825303 := bstep (se 1 (by rfl) ⟨4368977, by rfl⟩ : syracuseStep 5825303 = 8737955) B8737955
theorem B4367155 : Blo 1725063 4367155 := bstep (se 1 (by rfl) ⟨3275366, by rfl⟩ : syracuseStep 4367155 = 6550733) B6550733
theorem B3883841 : Blo 1725063 3883841 := bstep (se 2 (by rfl) ⟨1456440, by rfl⟩ : syracuseStep 3883841 = 2912881) B2912881
theorem B2589515 : Blo 1725063 2589515 := bstep (se 1 (by rfl) ⟨1942136, by rfl⟩ : syracuseStep 2589515 = 3884273) B3884273
theorem B2589527 : Blo 1725063 2589527 := bstep (se 1 (by rfl) ⟨1942145, by rfl⟩ : syracuseStep 2589527 = 3884291) B3884291
theorem B19669877 : Blo 1725063 19669877 := bstep (se 5 (by rfl) ⟨922025, by rfl⟩ : syracuseStep 19669877 = 1844051) B1844051
theorem B1942411 : Blo 1725063 1942411 := bstep (se 1 (by rfl) ⟨1456808, by rfl⟩ : syracuseStep 1942411 = 2913617) B2913617
theorem B2458507 : Blo 1725063 2458507 := bstep (se 1 (by rfl) ⟨1843880, by rfl⟩ : syracuseStep 2458507 = 3687761) B3687761
theorem B2589593 : Blo 1725063 2589593 := bstep (se 2 (by rfl) ⟨971097, by rfl⟩ : syracuseStep 2589593 = 1942195) B1942195
theorem B3277721 : Blo 1725063 3277721 := bstep (se 2 (by rfl) ⟨1229145, by rfl⟩ : syracuseStep 3277721 = 2458291) B2458291
theorem B4367297 : Blo 1725063 4367297 := bstep (se 2 (by rfl) ⟨1637736, by rfl⟩ : syracuseStep 4367297 = 3275473) B3275473
theorem B4146137 : Blo 1725063 4146137 := bstep (se 2 (by rfl) ⟨1554801, by rfl⟩ : syracuseStep 4146137 = 3109603) B3109603
theorem B3687385 : Blo 1725063 3687385 := bstep (se 2 (by rfl) ⟨1382769, by rfl⟩ : syracuseStep 3687385 = 2765539) B2765539
theorem B1942519 : Blo 1725063 1942519 := bstep (se 1 (by rfl) ⟨1456889, by rfl⟩ : syracuseStep 1942519 = 2913779) B2913779
theorem B2589707 : Blo 1725063 2589707 := bstep (se 1 (by rfl) ⟨1942280, by rfl⟩ : syracuseStep 2589707 = 3884561) B3884561
theorem B2589719 : Blo 1725063 2589719 := bstep (se 1 (by rfl) ⟨1942289, by rfl⟩ : syracuseStep 2589719 = 3884579) B3884579
theorem B3884057 : Blo 1725063 3884057 := bstep (se 2 (by rfl) ⟨1456521, by rfl⟩ : syracuseStep 3884057 = 2913043) B2913043
theorem B2589785 : Blo 1725063 2589785 := bstep (se 2 (by rfl) ⟨971169, by rfl⟩ : syracuseStep 2589785 = 1942339) B1942339
theorem B3884147 : Blo 1725063 3884147 := bstep (se 1 (by rfl) ⟨2913110, by rfl⟩ : syracuseStep 3884147 = 5826221) B5826221
theorem B3884183 : Blo 1725063 3884183 := bstep (se 1 (by rfl) ⟨2913137, by rfl⟩ : syracuseStep 3884183 = 5826275) B5826275
theorem B2458775 : Blo 1725063 2458775 := bstep (se 1 (by rfl) ⟨1844081, by rfl⟩ : syracuseStep 2458775 = 3688163) B3688163
theorem B1942699 : Blo 1725063 1942699 := bstep (se 1 (by rfl) ⟨1457024, by rfl⟩ : syracuseStep 1942699 = 2914049) B2914049
theorem B6554803 : Blo 1725063 6554803 := bstep (se 1 (by rfl) ⟨4916102, by rfl⟩ : syracuseStep 6554803 = 9832205) B9832205
theorem B7374017 : Blo 1725063 7374017 := bstep (se 2 (by rfl) ⟨2765256, by rfl⟩ : syracuseStep 7374017 = 5530513) B5530513
theorem B2589899 : Blo 1725063 2589899 := bstep (se 1 (by rfl) ⟨1942424, by rfl⟩ : syracuseStep 2589899 = 3884849) B3884849
theorem B2589911 : Blo 1725063 2589911 := bstep (se 1 (by rfl) ⟨1942433, by rfl⟩ : syracuseStep 2589911 = 3884867) B3884867
theorem B1942807 : Blo 1725063 1942807 := bstep (se 1 (by rfl) ⟨1457105, by rfl⟩ : syracuseStep 1942807 = 2914211) B2914211
theorem B2589977 : Blo 1725063 2589977 := bstep (se 2 (by rfl) ⟨971241, by rfl⟩ : syracuseStep 2589977 = 1942483) B1942483
theorem B5825843 : Blo 1725063 5825843 := bstep (se 1 (by rfl) ⟨4369382, by rfl⟩ : syracuseStep 5825843 = 8738765) B8738765
theorem B3884363 : Blo 1725063 3884363 := bstep (se 1 (by rfl) ⟨2913272, by rfl⟩ : syracuseStep 3884363 = 5826545) B5826545
theorem B3884417 : Blo 1725063 3884417 := bstep (se 2 (by rfl) ⟨1456656, by rfl⟩ : syracuseStep 3884417 = 2913313) B2913313
theorem B2590091 : Blo 1725063 2590091 := bstep (se 1 (by rfl) ⟨1942568, by rfl⟩ : syracuseStep 2590091 = 3885137) B3885137
theorem B2590103 : Blo 1725063 2590103 := bstep (se 1 (by rfl) ⟨1942577, by rfl⟩ : syracuseStep 2590103 = 3885155) B3885155
theorem B3737035 : Blo 1725063 3737035 := bstep (se 1 (by rfl) ⟨2802776, by rfl⟩ : syracuseStep 3737035 = 5605553) B5605553
theorem B2622937 : Blo 1725063 2622937 := bstep (se 2 (by rfl) ⟨983601, by rfl⟩ : syracuseStep 2622937 = 1967203) B1967203
theorem B2590169 : Blo 1725063 2590169 := bstep (se 2 (by rfl) ⟨971313, by rfl⟩ : syracuseStep 2590169 = 1942627) B1942627
theorem B2074135 : Blo 1725063 2074135 := bstep (se 1 (by rfl) ⟨1555601, by rfl⟩ : syracuseStep 2074135 = 3111203) B3111203
theorem B5826113 : Blo 1725063 5826113 := bstep (se 2 (by rfl) ⟨2184792, by rfl⟩ : syracuseStep 5826113 = 4369585) B4369585
theorem B2590283 : Blo 1725063 2590283 := bstep (se 1 (by rfl) ⟨1942712, by rfl⟩ : syracuseStep 2590283 = 3885425) B3885425
theorem B2590295 : Blo 1725063 2590295 := bstep (se 1 (by rfl) ⟨1942721, by rfl⟩ : syracuseStep 2590295 = 3885443) B3885443
theorem B3884633 : Blo 1725063 3884633 := bstep (se 2 (by rfl) ⟨1456737, by rfl⟩ : syracuseStep 3884633 = 2913475) B2913475
theorem B3278465 : Blo 1725063 3278465 := bstep (se 2 (by rfl) ⟨1229424, by rfl⟩ : syracuseStep 3278465 = 2458849) B2458849
theorem B2590361 : Blo 1725063 2590361 := bstep (se 2 (by rfl) ⟨971385, by rfl⟩ : syracuseStep 2590361 = 1942771) B1942771
theorem B3884723 : Blo 1725063 3884723 := bstep (se 1 (by rfl) ⟨2913542, by rfl⟩ : syracuseStep 3884723 = 5827085) B5827085
theorem B20195021 : Blo 1725063 20195021 := bstep (se 3 (by rfl) ⟨3786566, by rfl⟩ : syracuseStep 20195021 = 7573133) B7573133
theorem B3884759 : Blo 1725063 3884759 := bstep (se 1 (by rfl) ⟨2913569, by rfl⟩ : syracuseStep 3884759 = 5827139) B5827139
theorem B2623193 : Blo 1725063 2623193 := bstep (se 2 (by rfl) ⟨983697, by rfl⟩ : syracuseStep 2623193 = 1967395) B1967395
theorem B2590475 : Blo 1725063 2590475 := bstep (se 1 (by rfl) ⟨1942856, by rfl⟩ : syracuseStep 2590475 = 3885713) B3885713
theorem B2590487 : Blo 1725063 2590487 := bstep (se 1 (by rfl) ⟨1942865, by rfl⟩ : syracuseStep 2590487 = 3885731) B3885731
theorem B4982579 : Blo 1725063 4982579 := bstep (se 1 (by rfl) ⟨3736934, by rfl⟩ : syracuseStep 4982579 = 7473869) B7473869
theorem B4663129 : Blo 1725063 4663129 := bstep (se 2 (by rfl) ⟨1748673, by rfl⟩ : syracuseStep 4663129 = 3497347) B3497347
theorem B2590553 : Blo 1725063 2590553 := bstep (se 2 (by rfl) ⟨971457, by rfl⟩ : syracuseStep 2590553 = 1942915) B1942915
theorem B7374685 : Blo 1725063 7374685 := bstep (se 3 (by rfl) ⟨1382753, by rfl⟩ : syracuseStep 7374685 = 2765507) B2765507
theorem B3884939 : Blo 1725063 3884939 := bstep (se 1 (by rfl) ⟨2913704, by rfl⟩ : syracuseStep 3884939 = 5827409) B5827409
theorem B2803609 : Blo 1725063 2803609 := bstep (se 2 (by rfl) ⟨1051353, by rfl⟩ : syracuseStep 2803609 = 2102707) B2102707
theorem B3884993 : Blo 1725063 3884993 := bstep (se 2 (by rfl) ⟨1456872, by rfl⟩ : syracuseStep 3884993 = 2913745) B2913745
theorem B13101101 : Blo 1725063 13101101 := bstep (se 3 (by rfl) ⟨2456456, by rfl⟩ : syracuseStep 13101101 = 4912913) B4912913
theorem B8742977 : Blo 1725063 8742977 := bstep (se 2 (by rfl) ⟨3278616, by rfl⟩ : syracuseStep 8742977 = 6557233) B6557233
theorem B5826653 : Blo 1725063 5826653 := bstep (se 3 (by rfl) ⟨1092497, by rfl⟩ : syracuseStep 5826653 = 2184995) B2184995
theorem B3885209 : Blo 1725063 3885209 := bstep (se 2 (by rfl) ⟨1456953, by rfl⟩ : syracuseStep 3885209 = 2913907) B2913907
theorem B11053235 : Blo 1725063 11053235 := bstep (se 1 (by rfl) ⟨8289926, by rfl⟩ : syracuseStep 11053235 = 16579853) B16579853
theorem B4368563 : Blo 1725063 4368563 := bstep (se 1 (by rfl) ⟨3276422, by rfl⟩ : syracuseStep 4368563 = 6552845) B6552845
theorem B6998195 : Blo 1725063 6998195 := bstep (se 1 (by rfl) ⟨5248646, by rfl⟩ : syracuseStep 6998195 = 10497293) B10497293
theorem B3885299 : Blo 1725063 3885299 := bstep (se 1 (by rfl) ⟨2913974, by rfl⟩ : syracuseStep 3885299 = 5827949) B5827949
theorem B3885335 : Blo 1725063 3885335 := bstep (se 1 (by rfl) ⟨2914001, by rfl⟩ : syracuseStep 3885335 = 5828003) B5828003
theorem B4663603 : Blo 1725063 4663603 := bstep (se 1 (by rfl) ⟨3497702, by rfl⟩ : syracuseStep 4663603 = 6995405) B6995405
theorem B6556049 : Blo 1725063 6556049 := bstep (se 2 (by rfl) ⟨2458518, by rfl⟩ : syracuseStep 6556049 = 4917037) B4917037
theorem B7375283 : Blo 1725063 7375283 := bstep (se 1 (by rfl) ⟨5531462, by rfl⟩ : syracuseStep 7375283 = 11062925) B11062925
theorem B3885515 : Blo 1725063 3885515 := bstep (se 1 (by rfl) ⟨2914136, by rfl⟩ : syracuseStep 3885515 = 5828273) B5828273
theorem B3885569 : Blo 1725063 3885569 := bstep (se 2 (by rfl) ⟨1457088, by rfl⟩ : syracuseStep 3885569 = 2914177) B2914177
theorem B35441165 : Blo 1725063 35441165 := bstep (se 3 (by rfl) ⟨6645218, by rfl⟩ : syracuseStep 35441165 = 13290437) B13290437
theorem B8735363 : Blo 1725063 8735363 := bstep (se 1 (by rfl) ⟨6551522, by rfl⟩ : syracuseStep 8735363 = 13103045) B13103045
theorem B8293043 : Blo 1725063 8293043 := bstep (se 1 (by rfl) ⟨6219782, by rfl⟩ : syracuseStep 8293043 = 12439565) B12439565
theorem B4369099 : Blo 1725063 4369099 := bstep (se 1 (by rfl) ⟨3276824, by rfl⟩ : syracuseStep 4369099 = 6553649) B6553649
theorem B3885785 : Blo 1725063 3885785 := bstep (se 2 (by rfl) ⟨1457169, by rfl⟩ : syracuseStep 3885785 = 2914339) B2914339
theorem B6220547 : Blo 1725063 6220547 := bstep (se 1 (by rfl) ⟨4665410, by rfl⟩ : syracuseStep 6220547 = 9330821) B9330821
theorem B7473971 : Blo 1725063 7473971 := bstep (se 1 (by rfl) ⟨5605478, by rfl⟩ : syracuseStep 7473971 = 11210957) B11210957
theorem B3885875 : Blo 1725063 3885875 := bstep (se 1 (by rfl) ⟨2914406, by rfl⟩ : syracuseStep 3885875 = 5828813) B5828813
theorem B8293195 : Blo 1725063 8293195 := bstep (se 1 (by rfl) ⟨6219896, by rfl⟩ : syracuseStep 8293195 = 12439793) B12439793
theorem B4369241 : Blo 1725063 4369241 := bstep (se 2 (by rfl) ⟨1638465, by rfl⟩ : syracuseStep 4369241 = 3276931) B3276931
theorem B4148185 : Blo 1725063 4148185 := bstep (se 2 (by rfl) ⟨1555569, by rfl⟩ : syracuseStep 4148185 = 3111139) B3111139
theorem B13282309 : Blo 1725063 13282309 := bstep (se 4 (by rfl) ⟨1245216, by rfl⟩ : syracuseStep 13282309 = 2490433) B2490433
theorem B6556747 : Blo 1725063 6556747 := bstep (se 1 (by rfl) ⟨4917560, by rfl⟩ : syracuseStep 6556747 = 9835121) B9835121
theorem B6302893 : Blo 1725063 6302893 := bstep (se 3 (by rfl) ⟨1181792, by rfl⟩ : syracuseStep 6302893 = 2363585) B2363585
theorem B5827787 : Blo 1725063 5827787 := bstep (se 1 (by rfl) ⟨4370840, by rfl⟩ : syracuseStep 5827787 = 8741681) B8741681
theorem B1969355 : Blo 1725063 1969355 := bstep (se 1 (by rfl) ⟨1477016, by rfl⟩ : syracuseStep 1969355 = 2954033) B2954033
theorem B184216837 : Blo 1725063 184216837 := bstep (se 4 (by rfl) ⟨17270328, by rfl⟩ : syracuseStep 184216837 = 34540657) B34540657
theorem B2911511 : Blo 1725063 2911511 := bstep (se 1 (by rfl) ⟨2183633, by rfl⟩ : syracuseStep 2911511 = 4367267) B4367267
theorem B4664641 : Blo 1725063 4664641 := bstep (se 2 (by rfl) ⟨1749240, by rfl⟩ : syracuseStep 4664641 = 3498481) B3498481
theorem B8293697 : Blo 1725063 8293697 := bstep (se 2 (by rfl) ⟨3110136, by rfl⟩ : syracuseStep 8293697 = 6220273) B6220273
theorem B6557021 : Blo 1725063 6557021 := bstep (se 3 (by rfl) ⟨1229441, by rfl⟩ : syracuseStep 6557021 = 2458883) B2458883
theorem B2911639 : Blo 1725063 2911639 := bstep (se 1 (by rfl) ⟨2183729, by rfl⟩ : syracuseStep 2911639 = 4367459) B4367459
theorem B4795841 : Blo 1725063 4795841 := bstep (se 2 (by rfl) ⟨1798440, by rfl⟩ : syracuseStep 4795841 = 3596881) B3596881
theorem B5828057 : Blo 1725063 5828057 := bstep (se 2 (by rfl) ⟨2185521, by rfl⟩ : syracuseStep 5828057 = 4371043) B4371043
theorem B4370071 : Blo 1725063 4370071 := bstep (se 1 (by rfl) ⟨3277553, by rfl⟩ : syracuseStep 4370071 = 6555107) B6555107
theorem B9834371 : Blo 1725063 9834371 := bstep (se 1 (by rfl) ⟨7375778, by rfl⟩ : syracuseStep 9834371 = 14751557) B14751557
theorem B2912267 : Blo 1725063 2912267 := bstep (se 1 (by rfl) ⟨2184200, by rfl⟩ : syracuseStep 2912267 = 4368401) B4368401
theorem B3108889 : Blo 1725063 3108889 := bstep (se 2 (by rfl) ⟨1165833, by rfl⟩ : syracuseStep 3108889 = 2331667) B2331667
theorem B4370507 : Blo 1725063 4370507 := bstep (se 1 (by rfl) ⟨3277880, by rfl⟩ : syracuseStep 4370507 = 6555761) B6555761
theorem B2912395 : Blo 1725063 2912395 := bstep (se 1 (by rfl) ⟨2184296, by rfl⟩ : syracuseStep 2912395 = 4368593) B4368593
theorem B689950871 : Blo 1725063 689950871 := bstep (se 1 (by rfl) ⟨517463153, by rfl⟩ : syracuseStep 689950871 = 1034926307) B1034926307
theorem B5828759 : Blo 1725063 5828759 := bstep (se 1 (by rfl) ⟨4371569, by rfl⟩ : syracuseStep 5828759 = 8743139) B8743139
theorem B7000337 : Blo 1725063 7000337 := bstep (se 2 (by rfl) ⟨2625126, by rfl⟩ : syracuseStep 7000337 = 5250253) B5250253
theorem B2912537 : Blo 1725063 2912537 := bstep (se 2 (by rfl) ⟨1092201, by rfl⟩ : syracuseStep 2912537 = 2184403) B2184403
theorem B11055491 : Blo 1725063 11055491 := bstep (se 1 (by rfl) ⟨8291618, by rfl⟩ : syracuseStep 11055491 = 16583237) B16583237
theorem B2912665 : Blo 1725063 2912665 := bstep (se 2 (by rfl) ⟨1092249, by rfl⟩ : syracuseStep 2912665 = 2184499) B2184499
theorem B7000499 : Blo 1725063 7000499 := bstep (se 1 (by rfl) ⟨5250374, by rfl⟩ : syracuseStep 7000499 = 10500749) B10500749
theorem B4370881 : Blo 1725063 4370881 := bstep (se 2 (by rfl) ⟨1639080, by rfl⟩ : syracuseStep 4370881 = 3278161) B3278161
theorem B3109387 : Blo 1725063 3109387 := bstep (se 1 (by rfl) ⟨2332040, by rfl⟩ : syracuseStep 3109387 = 4664081) B4664081
theorem B2183755 : Blo 1725063 2183755 := bstep (se 1 (by rfl) ⟨1637816, by rfl⟩ : syracuseStep 2183755 = 3275633) B3275633
theorem B1725067 : Blo 1725063 1725067 := bstep (se 1 (by rfl) ⟨1293800, by rfl⟩ : syracuseStep 1725067 = 2587601) B2587601
theorem B1725079 : Blo 1725063 1725079 := bstep (se 1 (by rfl) ⟨1293809, by rfl⟩ : syracuseStep 1725079 = 2587619) B2587619
theorem B1725099 : Blo 1725063 1725099 := bstep (se 1 (by rfl) ⟨1293824, by rfl⟩ : syracuseStep 1725099 = 2587649) B2587649
theorem B1725111 : Blo 1725063 1725111 := bstep (se 1 (by rfl) ⟨1293833, by rfl⟩ : syracuseStep 1725111 = 2587667) B2587667
theorem B1725131 : Blo 1725063 1725131 := bstep (se 1 (by rfl) ⟨1293848, by rfl⟩ : syracuseStep 1725131 = 2587697) B2587697
theorem B1725143 : Blo 1725063 1725143 := bstep (se 1 (by rfl) ⟨1293857, by rfl⟩ : syracuseStep 1725143 = 2587715) B2587715
theorem B1725163 : Blo 1725063 1725163 := bstep (se 1 (by rfl) ⟨1293872, by rfl⟩ : syracuseStep 1725163 = 2587745) B2587745
theorem B1725175 : Blo 1725063 1725175 := bstep (se 1 (by rfl) ⟨1293881, by rfl⟩ : syracuseStep 1725175 = 2587763) B2587763
theorem B1725195 : Blo 1725063 1725195 := bstep (se 1 (by rfl) ⟨1293896, by rfl⟩ : syracuseStep 1725195 = 2587793) B2587793
theorem B1725207 : Blo 1725063 1725207 := bstep (se 1 (by rfl) ⟨1293905, by rfl⟩ : syracuseStep 1725207 = 2587811) B2587811
theorem B1725227 : Blo 1725063 1725227 := bstep (se 1 (by rfl) ⟨1293920, by rfl⟩ : syracuseStep 1725227 = 2587841) B2587841
theorem B1725239 : Blo 1725063 1725239 := bstep (se 1 (by rfl) ⟨1293929, by rfl⟩ : syracuseStep 1725239 = 2587859) B2587859
theorem B1725259 : Blo 1725063 1725259 := bstep (se 1 (by rfl) ⟨1293944, by rfl⟩ : syracuseStep 1725259 = 2587889) B2587889
theorem B1725271 : Blo 1725063 1725271 := bstep (se 1 (by rfl) ⟨1293953, by rfl⟩ : syracuseStep 1725271 = 2587907) B2587907
theorem B2184023 : Blo 1725063 2184023 := bstep (se 1 (by rfl) ⟨1638017, by rfl⟩ : syracuseStep 2184023 = 3276035) B3276035
theorem B7000921 : Blo 1725063 7000921 := bstep (se 2 (by rfl) ⟨2625345, by rfl⟩ : syracuseStep 7000921 = 5250691) B5250691
theorem B63877987 : Blo 1725063 63877987 := bstep (se 1 (by rfl) ⟨47908490, by rfl⟩ : syracuseStep 63877987 = 95816981) B95816981
theorem B1725291 : Blo 1725063 1725291 := bstep (se 1 (by rfl) ⟨1293968, by rfl⟩ : syracuseStep 1725291 = 2587937) B2587937
theorem B1725303 : Blo 1725063 1725303 := bstep (se 1 (by rfl) ⟨1293977, by rfl⟩ : syracuseStep 1725303 = 2587955) B2587955
theorem B1725323 : Blo 1725063 1725323 := bstep (se 1 (by rfl) ⟨1293992, by rfl⟩ : syracuseStep 1725323 = 2587985) B2587985
theorem B1725335 : Blo 1725063 1725335 := bstep (se 1 (by rfl) ⟨1294001, by rfl⟩ : syracuseStep 1725335 = 2588003) B2588003
theorem B1725355 : Blo 1725063 1725355 := bstep (se 1 (by rfl) ⟨1294016, by rfl⟩ : syracuseStep 1725355 = 2588033) B2588033
theorem B1725367 : Blo 1725063 1725367 := bstep (se 1 (by rfl) ⟨1294025, by rfl⟩ : syracuseStep 1725367 = 2588051) B2588051
theorem B1725387 : Blo 1725063 1725387 := bstep (se 1 (by rfl) ⟨1294040, by rfl⟩ : syracuseStep 1725387 = 2588081) B2588081
theorem B1725399 : Blo 1725063 1725399 := bstep (se 1 (by rfl) ⟨1294049, by rfl⟩ : syracuseStep 1725399 = 2588099) B2588099
theorem B2913239 : Blo 1725063 2913239 := bstep (se 1 (by rfl) ⟨2184929, by rfl⟩ : syracuseStep 2913239 = 4369859) B4369859
theorem B1725419 : Blo 1725063 1725419 := bstep (se 1 (by rfl) ⟨1294064, by rfl⟩ : syracuseStep 1725419 = 2588129) B2588129
theorem B1725431 : Blo 1725063 1725431 := bstep (se 1 (by rfl) ⟨1294073, by rfl⟩ : syracuseStep 1725431 = 2588147) B2588147
theorem B1725451 : Blo 1725063 1725451 := bstep (se 1 (by rfl) ⟨1294088, by rfl⟩ : syracuseStep 1725451 = 2588177) B2588177
theorem B6640663 : Blo 1725063 6640663 := bstep (se 1 (by rfl) ⟨4980497, by rfl⟩ : syracuseStep 6640663 = 9960995) B9960995
theorem B1725463 : Blo 1725063 1725463 := bstep (se 1 (by rfl) ⟨1294097, by rfl⟩ : syracuseStep 1725463 = 2588195) B2588195
theorem B4371479 : Blo 1725063 4371479 := bstep (se 1 (by rfl) ⟨3278609, by rfl⟩ : syracuseStep 4371479 = 6557219) B6557219
theorem B1725483 : Blo 1725063 1725483 := bstep (se 1 (by rfl) ⟨1294112, by rfl⟩ : syracuseStep 1725483 = 2588225) B2588225
theorem B1725495 : Blo 1725063 1725495 := bstep (se 1 (by rfl) ⟨1294121, by rfl⟩ : syracuseStep 1725495 = 2588243) B2588243
theorem B1725515 : Blo 1725063 1725515 := bstep (se 1 (by rfl) ⟨1294136, by rfl⟩ : syracuseStep 1725515 = 2588273) B2588273
theorem B1725527 : Blo 1725063 1725527 := bstep (se 1 (by rfl) ⟨1294145, by rfl⟩ : syracuseStep 1725527 = 2588291) B2588291
theorem B2913367 : Blo 1725063 2913367 := bstep (se 1 (by rfl) ⟨2185025, by rfl⟩ : syracuseStep 2913367 = 4370051) B4370051
theorem B1725547 : Blo 1725063 1725547 := bstep (se 1 (by rfl) ⟨1294160, by rfl⟩ : syracuseStep 1725547 = 2588321) B2588321
theorem B1725559 : Blo 1725063 1725559 := bstep (se 1 (by rfl) ⟨1294169, by rfl⟩ : syracuseStep 1725559 = 2588339) B2588339
theorem B1725579 : Blo 1725063 1725579 := bstep (se 1 (by rfl) ⟨1294184, by rfl⟩ : syracuseStep 1725579 = 2588369) B2588369
theorem B1725591 : Blo 1725063 1725591 := bstep (se 1 (by rfl) ⟨1294193, by rfl⟩ : syracuseStep 1725591 = 2588387) B2588387
theorem B1725611 : Blo 1725063 1725611 := bstep (se 1 (by rfl) ⟨1294208, by rfl⟩ : syracuseStep 1725611 = 2588417) B2588417
theorem B1725623 : Blo 1725063 1725623 := bstep (se 1 (by rfl) ⟨1294217, by rfl⟩ : syracuseStep 1725623 = 2588435) B2588435
theorem B6304961 : Blo 1725063 6304961 := bstep (se 2 (by rfl) ⟨2364360, by rfl⟩ : syracuseStep 6304961 = 4728721) B4728721
theorem B1725643 : Blo 1725063 1725643 := bstep (se 1 (by rfl) ⟨1294232, by rfl⟩ : syracuseStep 1725643 = 2588465) B2588465
theorem B1725655 : Blo 1725063 1725655 := bstep (se 1 (by rfl) ⟨1294241, by rfl⟩ : syracuseStep 1725655 = 2588483) B2588483
theorem B1725675 : Blo 1725063 1725675 := bstep (se 1 (by rfl) ⟨1294256, by rfl⟩ : syracuseStep 1725675 = 2588513) B2588513
theorem B1725687 : Blo 1725063 1725687 := bstep (se 1 (by rfl) ⟨1294265, by rfl⟩ : syracuseStep 1725687 = 2588531) B2588531
theorem B1725707 : Blo 1725063 1725707 := bstep (se 1 (by rfl) ⟨1294280, by rfl⟩ : syracuseStep 1725707 = 2588561) B2588561
theorem B1725719 : Blo 1725063 1725719 := bstep (se 1 (by rfl) ⟨1294289, by rfl⟩ : syracuseStep 1725719 = 2588579) B2588579
theorem B1725739 : Blo 1725063 1725739 := bstep (se 1 (by rfl) ⟨1294304, by rfl⟩ : syracuseStep 1725739 = 2588609) B2588609
theorem B1725751 : Blo 1725063 1725751 := bstep (se 1 (by rfl) ⟨1294313, by rfl⟩ : syracuseStep 1725751 = 2588627) B2588627
theorem B1725771 : Blo 1725063 1725771 := bstep (se 1 (by rfl) ⟨1294328, by rfl⟩ : syracuseStep 1725771 = 2588657) B2588657
theorem B1725783 : Blo 1725063 1725783 := bstep (se 1 (by rfl) ⟨1294337, by rfl⟩ : syracuseStep 1725783 = 2588675) B2588675
theorem B7476569 : Blo 1725063 7476569 := bstep (se 2 (by rfl) ⟨2803713, by rfl⟩ : syracuseStep 7476569 = 5607427) B5607427
theorem B29898085 : Blo 1725063 29898085 := bstep (se 4 (by rfl) ⟨2802945, by rfl⟩ : syracuseStep 29898085 = 5605891) B5605891
theorem B1725803 : Blo 1725063 1725803 := bstep (se 1 (by rfl) ⟨1294352, by rfl⟩ : syracuseStep 1725803 = 2588705) B2588705
theorem B1725815 : Blo 1725063 1725815 := bstep (se 1 (by rfl) ⟨1294361, by rfl⟩ : syracuseStep 1725815 = 2588723) B2588723
theorem B6550915 : Blo 1725063 6550915 := bstep (se 1 (by rfl) ⟨4913186, by rfl⟩ : syracuseStep 6550915 = 9826373) B9826373
theorem B1725835 : Blo 1725063 1725835 := bstep (se 1 (by rfl) ⟨1294376, by rfl⟩ : syracuseStep 1725835 = 2588753) B2588753
theorem B1725847 : Blo 1725063 1725847 := bstep (se 1 (by rfl) ⟨1294385, by rfl⟩ : syracuseStep 1725847 = 2588771) B2588771
theorem B1725867 : Blo 1725063 1725867 := bstep (se 1 (by rfl) ⟨1294400, by rfl⟩ : syracuseStep 1725867 = 2588801) B2588801
theorem B9328051 : Blo 1725063 9328051 := bstep (se 1 (by rfl) ⟨6996038, by rfl⟩ : syracuseStep 9328051 = 13992077) B13992077
theorem B1725879 : Blo 1725063 1725879 := bstep (se 1 (by rfl) ⟨1294409, by rfl⟩ : syracuseStep 1725879 = 2588819) B2588819
theorem B1725899 : Blo 1725063 1725899 := bstep (se 1 (by rfl) ⟨1294424, by rfl⟩ : syracuseStep 1725899 = 2588849) B2588849
theorem B1725911 : Blo 1725063 1725911 := bstep (se 1 (by rfl) ⟨1294433, by rfl⟩ : syracuseStep 1725911 = 2588867) B2588867
theorem B1725931 : Blo 1725063 1725931 := bstep (se 1 (by rfl) ⟨1294448, by rfl⟩ : syracuseStep 1725931 = 2588897) B2588897
theorem B1725943 : Blo 1725063 1725943 := bstep (se 1 (by rfl) ⟨1294457, by rfl⟩ : syracuseStep 1725943 = 2588915) B2588915
theorem B1725963 : Blo 1725063 1725963 := bstep (se 1 (by rfl) ⟨1294472, by rfl⟩ : syracuseStep 1725963 = 2588945) B2588945
theorem B4912663 : Blo 1725063 4912663 := bstep (se 1 (by rfl) ⟨3684497, by rfl⟩ : syracuseStep 4912663 = 7368995) B7368995
theorem B1725975 : Blo 1725063 1725975 := bstep (se 1 (by rfl) ⟨1294481, by rfl⟩ : syracuseStep 1725975 = 2588963) B2588963
theorem B2184727 : Blo 1725063 2184727 := bstep (se 1 (by rfl) ⟨1638545, by rfl⟩ : syracuseStep 2184727 = 3277091) B3277091
theorem B2766359 : Blo 1725063 2766359 := bstep (se 1 (by rfl) ⟨2074769, by rfl⟩ : syracuseStep 2766359 = 4149539) B4149539
theorem B1725995 : Blo 1725063 1725995 := bstep (se 1 (by rfl) ⟨1294496, by rfl⟩ : syracuseStep 1725995 = 2588993) B2588993
theorem B1726007 : Blo 1725063 1726007 := bstep (se 1 (by rfl) ⟨1294505, by rfl⟩ : syracuseStep 1726007 = 2589011) B2589011
theorem B6067777 : Blo 1725063 6067777 := bstep (se 2 (by rfl) ⟨2275416, by rfl⟩ : syracuseStep 6067777 = 4550833) B4550833
theorem B1726027 : Blo 1725063 1726027 := bstep (se 1 (by rfl) ⟨1294520, by rfl⟩ : syracuseStep 1726027 = 2589041) B2589041
theorem B1726039 : Blo 1725063 1726039 := bstep (se 1 (by rfl) ⟨1294529, by rfl⟩ : syracuseStep 1726039 = 2589059) B2589059
theorem B37303901 : Blo 1725063 37303901 := bstep (se 3 (by rfl) ⟨6994481, by rfl⟩ : syracuseStep 37303901 = 13988963) B13988963
theorem B1726059 : Blo 1725063 1726059 := bstep (se 1 (by rfl) ⟨1294544, by rfl⟩ : syracuseStep 1726059 = 2589089) B2589089
theorem B1726071 : Blo 1725063 1726071 := bstep (se 1 (by rfl) ⟨1294553, by rfl⟩ : syracuseStep 1726071 = 2589107) B2589107
theorem B1726091 : Blo 1725063 1726091 := bstep (se 1 (by rfl) ⟨1294568, by rfl⟩ : syracuseStep 1726091 = 2589137) B2589137
theorem B1726103 : Blo 1725063 1726103 := bstep (se 1 (by rfl) ⟨1294577, by rfl⟩ : syracuseStep 1726103 = 2589155) B2589155
theorem B1726123 : Blo 1725063 1726123 := bstep (se 1 (by rfl) ⟨1294592, by rfl⟩ : syracuseStep 1726123 = 2589185) B2589185
theorem B6551219 : Blo 1725063 6551219 := bstep (se 1 (by rfl) ⟨4913414, by rfl⟩ : syracuseStep 6551219 = 9826829) B9826829
theorem B1726135 : Blo 1725063 1726135 := bstep (se 1 (by rfl) ⟨1294601, by rfl⟩ : syracuseStep 1726135 = 2589203) B2589203
theorem B1726155 : Blo 1725063 1726155 := bstep (se 1 (by rfl) ⟨1294616, by rfl⟩ : syracuseStep 1726155 = 2589233) B2589233
theorem B2913995 : Blo 1725063 2913995 := bstep (se 1 (by rfl) ⟨2185496, by rfl⟩ : syracuseStep 2913995 = 4370993) B4370993
theorem B1726167 : Blo 1725063 1726167 := bstep (se 1 (by rfl) ⟨1294625, by rfl⟩ : syracuseStep 1726167 = 2589251) B2589251
theorem B1726187 : Blo 1725063 1726187 := bstep (se 1 (by rfl) ⟨1294640, by rfl⟩ : syracuseStep 1726187 = 2589281) B2589281
theorem B51123953 : Blo 1725063 51123953 := bstep (se 2 (by rfl) ⟨19171482, by rfl⟩ : syracuseStep 51123953 = 38342965) B38342965
theorem B1726199 : Blo 1725063 1726199 := bstep (se 1 (by rfl) ⟨1294649, by rfl⟩ : syracuseStep 1726199 = 2589299) B2589299
theorem B1726219 : Blo 1725063 1726219 := bstep (se 1 (by rfl) ⟨1294664, by rfl⟩ : syracuseStep 1726219 = 2589329) B2589329
theorem B1726231 : Blo 1725063 1726231 := bstep (se 1 (by rfl) ⟨1294673, by rfl⟩ : syracuseStep 1726231 = 2589347) B2589347
theorem B1726251 : Blo 1725063 1726251 := bstep (se 1 (by rfl) ⟨1294688, by rfl⟩ : syracuseStep 1726251 = 2589377) B2589377
theorem B1726263 : Blo 1725063 1726263 := bstep (se 1 (by rfl) ⟨1294697, by rfl⟩ : syracuseStep 1726263 = 2589395) B2589395
theorem B63141697 : Blo 1725063 63141697 := bstep (se 2 (by rfl) ⟨23678136, by rfl⟩ : syracuseStep 63141697 = 47356273) B47356273
theorem B1726283 : Blo 1725063 1726283 := bstep (se 1 (by rfl) ⟨1294712, by rfl⟩ : syracuseStep 1726283 = 2589425) B2589425
theorem B2914123 : Blo 1725063 2914123 := bstep (se 1 (by rfl) ⟨2185592, by rfl⟩ : syracuseStep 2914123 = 4371185) B4371185
theorem B1726295 : Blo 1725063 1726295 := bstep (se 1 (by rfl) ⟨1294721, by rfl⟩ : syracuseStep 1726295 = 2589443) B2589443
theorem B7370585 : Blo 1725063 7370585 := bstep (se 2 (by rfl) ⟨2763969, by rfl⟩ : syracuseStep 7370585 = 5527939) B5527939
theorem B13104989 : Blo 1725063 13104989 := bstep (se 3 (by rfl) ⟨2457185, by rfl⟩ : syracuseStep 13104989 = 4914371) B4914371
theorem B1726315 : Blo 1725063 1726315 := bstep (se 1 (by rfl) ⟨1294736, by rfl⟩ : syracuseStep 1726315 = 2589473) B2589473
theorem B1726327 : Blo 1725063 1726327 := bstep (se 1 (by rfl) ⟨1294745, by rfl⟩ : syracuseStep 1726327 = 2589491) B2589491
theorem B1726347 : Blo 1725063 1726347 := bstep (se 1 (by rfl) ⟨1294760, by rfl⟩ : syracuseStep 1726347 = 2589521) B2589521
theorem B1726359 : Blo 1725063 1726359 := bstep (se 1 (by rfl) ⟨1294769, by rfl⟩ : syracuseStep 1726359 = 2589539) B2589539
theorem B1726379 : Blo 1725063 1726379 := bstep (se 1 (by rfl) ⟨1294784, by rfl⟩ : syracuseStep 1726379 = 2589569) B2589569
theorem B7370669 : Blo 1725063 7370669 := bstep (se 3 (by rfl) ⟨1382000, by rfl⟩ : syracuseStep 7370669 = 2764001) B2764001
theorem B5822387 : Blo 1725063 5822387 := bstep (se 1 (by rfl) ⟨4366790, by rfl⟩ : syracuseStep 5822387 = 8733581) B8733581
theorem B1726391 : Blo 1725063 1726391 := bstep (se 1 (by rfl) ⟨1294793, by rfl⟩ : syracuseStep 1726391 = 2589587) B2589587
theorem B1726411 : Blo 1725063 1726411 := bstep (se 1 (by rfl) ⟨1294808, by rfl⟩ : syracuseStep 1726411 = 2589617) B2589617
theorem B1726423 : Blo 1725063 1726423 := bstep (se 1 (by rfl) ⟨1294817, by rfl⟩ : syracuseStep 1726423 = 2589635) B2589635
theorem B2914265 : Blo 1725063 2914265 := bstep (se 2 (by rfl) ⟨1092849, by rfl⟩ : syracuseStep 2914265 = 2185699) B2185699
theorem B1726443 : Blo 1725063 1726443 := bstep (se 1 (by rfl) ⟨1294832, by rfl⟩ : syracuseStep 1726443 = 2589665) B2589665
theorem B1726455 : Blo 1725063 1726455 := bstep (se 1 (by rfl) ⟨1294841, by rfl⟩ : syracuseStep 1726455 = 2589683) B2589683
theorem B1726475 : Blo 1725063 1726475 := bstep (se 1 (by rfl) ⟨1294856, by rfl⟩ : syracuseStep 1726475 = 2589713) B2589713
theorem B19666961 : Blo 1725063 19666961 := bstep (se 2 (by rfl) ⟨7375110, by rfl⟩ : syracuseStep 19666961 = 14750221) B14750221
theorem B1726487 : Blo 1725063 1726487 := bstep (se 1 (by rfl) ⟨1294865, by rfl⟩ : syracuseStep 1726487 = 2589731) B2589731
theorem B1726507 : Blo 1725063 1726507 := bstep (se 1 (by rfl) ⟨1294880, by rfl⟩ : syracuseStep 1726507 = 2589761) B2589761
theorem B1726519 : Blo 1725063 1726519 := bstep (se 1 (by rfl) ⟨1294889, by rfl⟩ : syracuseStep 1726519 = 2589779) B2589779
theorem B3110987 : Blo 1725063 3110987 := bstep (se 1 (by rfl) ⟨2333240, by rfl⟩ : syracuseStep 3110987 = 4666481) B4666481
theorem B1726539 : Blo 1725063 1726539 := bstep (se 1 (by rfl) ⟨1294904, by rfl⟩ : syracuseStep 1726539 = 2589809) B2589809
theorem B1726551 : Blo 1725063 1726551 := bstep (se 1 (by rfl) ⟨1294913, by rfl⟩ : syracuseStep 1726551 = 2589827) B2589827
theorem B2914393 : Blo 1725063 2914393 := bstep (se 2 (by rfl) ⟨1092897, by rfl⟩ : syracuseStep 2914393 = 2185795) B2185795
theorem B1726571 : Blo 1725063 1726571 := bstep (se 1 (by rfl) ⟨1294928, by rfl⟩ : syracuseStep 1726571 = 2589857) B2589857
theorem B1726583 : Blo 1725063 1726583 := bstep (se 1 (by rfl) ⟨1294937, by rfl⟩ : syracuseStep 1726583 = 2589875) B2589875
theorem B1726603 : Blo 1725063 1726603 := bstep (se 1 (by rfl) ⟨1294952, by rfl⟩ : syracuseStep 1726603 = 2589905) B2589905
theorem B1726615 : Blo 1725063 1726615 := bstep (se 1 (by rfl) ⟨1294961, by rfl⟩ : syracuseStep 1726615 = 2589923) B2589923
theorem B1726635 : Blo 1725063 1726635 := bstep (se 1 (by rfl) ⟨1294976, by rfl⟩ : syracuseStep 1726635 = 2589953) B2589953
theorem B1726647 : Blo 1725063 1726647 := bstep (se 1 (by rfl) ⟨1294985, by rfl⟩ : syracuseStep 1726647 = 2589971) B2589971
theorem B5822657 : Blo 1725063 5822657 := bstep (se 2 (by rfl) ⟨2183496, by rfl⟩ : syracuseStep 5822657 = 4366993) B4366993
theorem B1726667 : Blo 1725063 1726667 := bstep (se 1 (by rfl) ⟨1295000, by rfl⟩ : syracuseStep 1726667 = 2590001) B2590001
theorem B1726679 : Blo 1725063 1726679 := bstep (se 1 (by rfl) ⟨1295009, by rfl⟩ : syracuseStep 1726679 = 2590019) B2590019
theorem B4913369 : Blo 1725063 4913369 := bstep (se 2 (by rfl) ⟨1842513, by rfl⟩ : syracuseStep 4913369 = 3685027) B3685027
theorem B1726699 : Blo 1725063 1726699 := bstep (se 1 (by rfl) ⟨1295024, by rfl⟩ : syracuseStep 1726699 = 2590049) B2590049
theorem B1726711 : Blo 1725063 1726711 := bstep (se 1 (by rfl) ⟨1295033, by rfl⟩ : syracuseStep 1726711 = 2590067) B2590067
theorem B1726731 : Blo 1725063 1726731 := bstep (se 1 (by rfl) ⟨1295048, by rfl⟩ : syracuseStep 1726731 = 2590097) B2590097
theorem B8739089 : Blo 1725063 8739089 := bstep (se 2 (by rfl) ⟨3277158, by rfl⟩ : syracuseStep 8739089 = 6554317) B6554317
theorem B1726743 : Blo 1725063 1726743 := bstep (se 1 (by rfl) ⟨1295057, by rfl⟩ : syracuseStep 1726743 = 2590115) B2590115
theorem B1726763 : Blo 1725063 1726763 := bstep (se 1 (by rfl) ⟨1295072, by rfl⟩ : syracuseStep 1726763 = 2590145) B2590145
theorem B1726775 : Blo 1725063 1726775 := bstep (se 1 (by rfl) ⟨1295081, by rfl⟩ : syracuseStep 1726775 = 2590163) B2590163
theorem B6551873 : Blo 1725063 6551873 := bstep (se 2 (by rfl) ⟨2456952, by rfl⟩ : syracuseStep 6551873 = 4913905) B4913905
theorem B1726795 : Blo 1725063 1726795 := bstep (se 1 (by rfl) ⟨1295096, by rfl⟩ : syracuseStep 1726795 = 2590193) B2590193
theorem B1726807 : Blo 1725063 1726807 := bstep (se 1 (by rfl) ⟨1295105, by rfl⟩ : syracuseStep 1726807 = 2590211) B2590211
theorem B29489507 : Blo 1725063 29489507 := bstep (se 1 (by rfl) ⟨22117130, by rfl⟩ : syracuseStep 29489507 = 44234261) B44234261
theorem B1726827 : Blo 1725063 1726827 := bstep (se 1 (by rfl) ⟨1295120, by rfl⟩ : syracuseStep 1726827 = 2590241) B2590241
theorem B1726839 : Blo 1725063 1726839 := bstep (se 1 (by rfl) ⟨1295129, by rfl⟩ : syracuseStep 1726839 = 2590259) B2590259
theorem B3275147 : Blo 1725063 3275147 := bstep (se 1 (by rfl) ⟨2456360, by rfl⟩ : syracuseStep 3275147 = 4912721) B4912721
theorem B1726859 : Blo 1725063 1726859 := bstep (se 1 (by rfl) ⟨1295144, by rfl⟩ : syracuseStep 1726859 = 2590289) B2590289
theorem B1726871 : Blo 1725063 1726871 := bstep (se 1 (by rfl) ⟨1295153, by rfl⟩ : syracuseStep 1726871 = 2590307) B2590307
theorem B1726891 : Blo 1725063 1726891 := bstep (se 1 (by rfl) ⟨1295168, by rfl⟩ : syracuseStep 1726891 = 2590337) B2590337
theorem B8739251 : Blo 1725063 8739251 := bstep (se 1 (by rfl) ⟨6554438, by rfl⟩ : syracuseStep 8739251 = 13108877) B13108877
theorem B3111347 : Blo 1725063 3111347 := bstep (se 1 (by rfl) ⟨2333510, by rfl⟩ : syracuseStep 3111347 = 4667021) B4667021
theorem B1726903 : Blo 1725063 1726903 := bstep (se 1 (by rfl) ⟨1295177, by rfl⟩ : syracuseStep 1726903 = 2590355) B2590355
theorem B1726923 : Blo 1725063 1726923 := bstep (se 1 (by rfl) ⟨1295192, by rfl⟩ : syracuseStep 1726923 = 2590385) B2590385
theorem B14752205 : Blo 1725063 14752205 := bstep (se 3 (by rfl) ⟨2766038, by rfl⟩ : syracuseStep 14752205 = 5532077) B5532077
theorem B1726935 : Blo 1725063 1726935 := bstep (se 1 (by rfl) ⟨1295201, by rfl⟩ : syracuseStep 1726935 = 2590403) B2590403
theorem B1726955 : Blo 1725063 1726955 := bstep (se 1 (by rfl) ⟨1295216, by rfl⟩ : syracuseStep 1726955 = 2590433) B2590433
theorem B1726967 : Blo 1725063 1726967 := bstep (se 1 (by rfl) ⟨1295225, by rfl⟩ : syracuseStep 1726967 = 2590451) B2590451
theorem B3881483 : Blo 1725063 3881483 := bstep (se 1 (by rfl) ⟨2911112, by rfl⟩ : syracuseStep 3881483 = 5822225) B5822225
theorem B1726987 : Blo 1725063 1726987 := bstep (se 1 (by rfl) ⟨1295240, by rfl⟩ : syracuseStep 1726987 = 2590481) B2590481
theorem B1726999 : Blo 1725063 1726999 := bstep (se 1 (by rfl) ⟨1295249, by rfl⟩ : syracuseStep 1726999 = 2590499) B2590499
theorem B1727019 : Blo 1725063 1727019 := bstep (se 1 (by rfl) ⟨1295264, by rfl⟩ : syracuseStep 1727019 = 2590529) B2590529
theorem B1727031 : Blo 1725063 1727031 := bstep (se 1 (by rfl) ⟨1295273, by rfl⟩ : syracuseStep 1727031 = 2590547) B2590547
theorem B3881537 : Blo 1725063 3881537 := bstep (se 2 (by rfl) ⟨1455576, by rfl⟩ : syracuseStep 3881537 = 2911153) B2911153
theorem B3275329 : Blo 1725063 3275329 := bstep (se 2 (by rfl) ⟨1228248, by rfl⟩ : syracuseStep 3275329 = 2456497) B2456497
theorem B1727051 : Blo 1725063 1727051 := bstep (se 1 (by rfl) ⟨1295288, by rfl⟩ : syracuseStep 1727051 = 2590577) B2590577
theorem B1727063 : Blo 1725063 1727063 := bstep (se 1 (by rfl) ⟨1295297, by rfl⟩ : syracuseStep 1727063 = 2590595) B2590595
theorem B3111577 : Blo 1725063 3111577 := bstep (se 2 (by rfl) ⟨1166841, by rfl⟩ : syracuseStep 3111577 = 2333683) B2333683
theorem B7092953 : Blo 1725063 7092953 := bstep (se 2 (by rfl) ⟨2659857, by rfl⟩ : syracuseStep 7092953 = 5319715) B5319715
theorem B5823197 : Blo 1725063 5823197 := bstep (se 3 (by rfl) ⟨1091849, by rfl⟩ : syracuseStep 5823197 = 2183699) B2183699
theorem B3881753 : Blo 1725063 3881753 := bstep (se 2 (by rfl) ⟨1455657, by rfl⟩ : syracuseStep 3881753 = 2911315) B2911315
theorem B3881843 : Blo 1725063 3881843 := bstep (se 1 (by rfl) ⟨2911382, by rfl⟩ : syracuseStep 3881843 = 5822765) B5822765
theorem B3881879 : Blo 1725063 3881879 := bstep (se 1 (by rfl) ⟨2911409, by rfl⟩ : syracuseStep 3881879 = 5822819) B5822819
theorem B2587595 : Blo 1725063 2587595 := bstep (se 1 (by rfl) ⟨1940696, by rfl⟩ : syracuseStep 2587595 = 3881393) B3881393
theorem B2587607 : Blo 1725063 2587607 := bstep (se 1 (by rfl) ⟨1940705, by rfl⟩ : syracuseStep 2587607 = 3881411) B3881411
theorem B3275777 : Blo 1725063 3275777 := bstep (se 2 (by rfl) ⟨1228416, by rfl⟩ : syracuseStep 3275777 = 2456833) B2456833
theorem B2587673 : Blo 1725063 2587673 := bstep (se 2 (by rfl) ⟨970377, by rfl⟩ : syracuseStep 2587673 = 1940755) B1940755
theorem B3882059 : Blo 1725063 3882059 := bstep (se 1 (by rfl) ⟨2911544, by rfl⟩ : syracuseStep 3882059 = 5823089) B5823089
theorem B48561227 : Blo 1725063 48561227 := bstep (se 1 (by rfl) ⟨36420920, by rfl⟩ : syracuseStep 48561227 = 72841841) B72841841
theorem B3882113 : Blo 1725063 3882113 := bstep (se 2 (by rfl) ⟨1455792, by rfl⟩ : syracuseStep 3882113 = 2911585) B2911585
theorem B3685505 : Blo 1725063 3685505 := bstep (se 2 (by rfl) ⟨1382064, by rfl⟩ : syracuseStep 3685505 = 2764129) B2764129
theorem B2587787 : Blo 1725063 2587787 := bstep (se 1 (by rfl) ⟨1940840, by rfl⟩ : syracuseStep 2587787 = 3881681) B3881681
theorem B2587799 : Blo 1725063 2587799 := bstep (se 1 (by rfl) ⟨1940849, by rfl⟩ : syracuseStep 2587799 = 3881699) B3881699
theorem B3685591 : Blo 1725063 3685591 := bstep (se 1 (by rfl) ⟨2764193, by rfl⟩ : syracuseStep 3685591 = 5528387) B5528387
theorem B2587865 : Blo 1725063 2587865 := bstep (se 2 (by rfl) ⟨970449, by rfl⟩ : syracuseStep 2587865 = 1940899) B1940899
theorem B99556613 : Blo 1725063 99556613 := bstep (se 4 (by rfl) ⟨9333432, by rfl⟩ : syracuseStep 99556613 = 18666865) B18666865
theorem B1940791 : Blo 1725063 1940791 := bstep (se 1 (by rfl) ⟨1455593, by rfl⟩ : syracuseStep 1940791 = 2911187) B2911187
theorem B2587979 : Blo 1725063 2587979 := bstep (se 1 (by rfl) ⟨1940984, by rfl⟩ : syracuseStep 2587979 = 3881969) B3881969
theorem B2587991 : Blo 1725063 2587991 := bstep (se 1 (by rfl) ⟨1940993, by rfl⟩ : syracuseStep 2587991 = 3881987) B3881987
theorem B3276119 : Blo 1725063 3276119 := bstep (se 1 (by rfl) ⟨2457089, by rfl⟩ : syracuseStep 3276119 = 4914179) B4914179
theorem B3882329 : Blo 1725063 3882329 := bstep (se 2 (by rfl) ⟨1455873, by rfl⟩ : syracuseStep 3882329 = 2911747) B2911747
theorem B32349557 : Blo 1725063 32349557 := bstep (se 5 (by rfl) ⟨1516385, by rfl⟩ : syracuseStep 32349557 = 3032771) B3032771
theorem B2588057 : Blo 1725063 2588057 := bstep (se 2 (by rfl) ⟨970521, by rfl⟩ : syracuseStep 2588057 = 1941043) B1941043
theorem B14949809 : Blo 1725063 14949809 := bstep (se 2 (by rfl) ⟨5606178, by rfl⟩ : syracuseStep 14949809 = 11212357) B11212357
theorem B3882419 : Blo 1725063 3882419 := bstep (se 1 (by rfl) ⟨2911814, by rfl⟩ : syracuseStep 3882419 = 5823629) B5823629
theorem B3882455 : Blo 1725063 3882455 := bstep (se 1 (by rfl) ⟨2911841, by rfl⟩ : syracuseStep 3882455 = 5823683) B5823683
theorem B2457049 : Blo 1725063 2457049 := bstep (se 2 (by rfl) ⟨921393, by rfl⟩ : syracuseStep 2457049 = 1842787) B1842787
theorem B1940971 : Blo 1725063 1940971 := bstep (se 1 (by rfl) ⟨1455728, by rfl⟩ : syracuseStep 1940971 = 2911457) B2911457
theorem B2588171 : Blo 1725063 2588171 := bstep (se 1 (by rfl) ⟨1941128, by rfl⟩ : syracuseStep 2588171 = 3882257) B3882257
theorem B2588183 : Blo 1725063 2588183 := bstep (se 1 (by rfl) ⟨1941137, by rfl⟩ : syracuseStep 2588183 = 3882275) B3882275
theorem B6553133 : Blo 1725063 6553133 := bstep (se 3 (by rfl) ⟨1228712, by rfl⟩ : syracuseStep 6553133 = 2457425) B2457425
theorem B2457163 : Blo 1725063 2457163 := bstep (se 1 (by rfl) ⟨1842872, by rfl⟩ : syracuseStep 2457163 = 3685745) B3685745
theorem B6553163 : Blo 1725063 6553163 := bstep (se 1 (by rfl) ⟨4914872, by rfl⟩ : syracuseStep 6553163 = 9829745) B9829745
theorem B1941079 : Blo 1725063 1941079 := bstep (se 1 (by rfl) ⟨1455809, by rfl⟩ : syracuseStep 1941079 = 2911619) B2911619
theorem B2588249 : Blo 1725063 2588249 := bstep (se 2 (by rfl) ⟨970593, by rfl⟩ : syracuseStep 2588249 = 1941187) B1941187
theorem B5529181 : Blo 1725063 5529181 := bstep (se 3 (by rfl) ⟨1036721, by rfl⟩ : syracuseStep 5529181 = 2073443) B2073443
theorem B3882635 : Blo 1725063 3882635 := bstep (se 1 (by rfl) ⟨2911976, by rfl⟩ : syracuseStep 3882635 = 5823953) B5823953
theorem B6217361 : Blo 1725063 6217361 := bstep (se 2 (by rfl) ⟨2331510, by rfl⟩ : syracuseStep 6217361 = 4663021) B4663021
theorem B3882689 : Blo 1725063 3882689 := bstep (se 2 (by rfl) ⟨1456008, by rfl⟩ : syracuseStep 3882689 = 2912017) B2912017
theorem B2588363 : Blo 1725063 2588363 := bstep (se 1 (by rfl) ⟨1941272, by rfl⟩ : syracuseStep 2588363 = 3882545) B3882545
theorem B2588375 : Blo 1725063 2588375 := bstep (se 1 (by rfl) ⟨1941281, by rfl⟩ : syracuseStep 2588375 = 3882563) B3882563
theorem B1941259 : Blo 1725063 1941259 := bstep (se 1 (by rfl) ⟨1455944, by rfl⟩ : syracuseStep 1941259 = 2911889) B2911889
theorem B2588441 : Blo 1725063 2588441 := bstep (se 2 (by rfl) ⟨970665, by rfl⟩ : syracuseStep 2588441 = 1941331) B1941331
theorem B24870701 : Blo 1725063 24870701 := bstep (se 3 (by rfl) ⟨4663256, by rfl⟩ : syracuseStep 24870701 = 9326513) B9326513
theorem B4915009 : Blo 1725063 4915009 := bstep (se 2 (by rfl) ⟨1843128, by rfl⟩ : syracuseStep 4915009 = 3686257) B3686257
theorem B5824331 : Blo 1725063 5824331 := bstep (se 1 (by rfl) ⟨4368248, by rfl⟩ : syracuseStep 5824331 = 8736497) B8736497
theorem B11968357 : Blo 1725063 11968357 := bstep (se 4 (by rfl) ⟨1122033, by rfl⟩ : syracuseStep 11968357 = 2244067) B2244067
theorem B1941367 : Blo 1725063 1941367 := bstep (se 1 (by rfl) ⟨1456025, by rfl⟩ : syracuseStep 1941367 = 2912051) B2912051
theorem B2588555 : Blo 1725063 2588555 := bstep (se 1 (by rfl) ⟨1941416, by rfl⟩ : syracuseStep 2588555 = 3882833) B3882833
theorem B2588567 : Blo 1725063 2588567 := bstep (se 1 (by rfl) ⟨1941425, by rfl⟩ : syracuseStep 2588567 = 3882851) B3882851
theorem B12443543 : Blo 1725063 12443543 := bstep (se 1 (by rfl) ⟨9332657, by rfl⟩ : syracuseStep 12443543 = 18665315) B18665315
theorem B3882905 : Blo 1725063 3882905 := bstep (se 2 (by rfl) ⟨1456089, by rfl⟩ : syracuseStep 3882905 = 2912179) B2912179
theorem B2588633 : Blo 1725063 2588633 := bstep (se 2 (by rfl) ⟨970737, by rfl⟩ : syracuseStep 2588633 = 1941475) B1941475
theorem B4489177 : Blo 1725063 4489177 := bstep (se 2 (by rfl) ⟨1683441, by rfl⟩ : syracuseStep 4489177 = 3366883) B3366883
theorem B3882995 : Blo 1725063 3882995 := bstep (se 1 (by rfl) ⟨2912246, by rfl⟩ : syracuseStep 3882995 = 5824493) B5824493
theorem B3276787 : Blo 1725063 3276787 := bstep (se 1 (by rfl) ⟨2457590, by rfl⟩ : syracuseStep 3276787 = 4915181) B4915181
theorem B1941511 : Blo 1725063 1941511 := bstep (se 1 (by rfl) ⟨1456133, by rfl⟩ : syracuseStep 1941511 = 2912267) B2912267
theorem B2588687 : Blo 1725063 2588687 := bstep (se 1 (by rfl) ⟨1941515, by rfl⟩ : syracuseStep 2588687 = 3883031) B3883031
theorem B9830429 : Blo 1725063 9830429 := bstep (se 3 (by rfl) ⟨1843205, by rfl⟩ : syracuseStep 9830429 = 3686411) B3686411
theorem B4145185 : Blo 1725063 4145185 := bstep (se 2 (by rfl) ⟨1554444, by rfl⟩ : syracuseStep 4145185 = 3108889) B3108889
theorem B4145195 : Blo 1725063 4145195 := bstep (se 1 (by rfl) ⟨3108896, by rfl⟩ : syracuseStep 4145195 = 6217793) B6217793
theorem B2588729 : Blo 1725063 2588729 := bstep (se 2 (by rfl) ⟨970773, by rfl⟩ : syracuseStep 2588729 = 1941547) B1941547
theorem B3883067 : Blo 1725063 3883067 := bstep (se 1 (by rfl) ⟨2912300, by rfl⟩ : syracuseStep 3883067 = 5824601) B5824601
theorem B2588807 : Blo 1725063 2588807 := bstep (se 1 (by rfl) ⟨1941605, by rfl⟩ : syracuseStep 2588807 = 3883211) B3883211
theorem B2588843 : Blo 1725063 2588843 := bstep (se 1 (by rfl) ⟨1941632, by rfl⟩ : syracuseStep 2588843 = 3883265) B3883265
theorem B3883193 : Blo 1725063 3883193 := bstep (se 2 (by rfl) ⟨1456197, by rfl⟩ : syracuseStep 3883193 = 2912395) B2912395
theorem B1941691 : Blo 1725063 1941691 := bstep (se 1 (by rfl) ⟨1456268, by rfl⟩ : syracuseStep 1941691 = 2912537) B2912537
theorem B2588873 : Blo 1725063 2588873 := bstep (se 2 (by rfl) ⟨970827, by rfl⟩ : syracuseStep 2588873 = 1941655) B1941655
theorem B2588987 : Blo 1725063 2588987 := bstep (se 1 (by rfl) ⟨1941740, by rfl⟩ : syracuseStep 2588987 = 3883481) B3883481
theorem B2589047 : Blo 1725063 2589047 := bstep (se 1 (by rfl) ⟨1941785, by rfl⟩ : syracuseStep 2589047 = 3883571) B3883571
theorem B11059591 : Blo 1725063 11059591 := bstep (se 1 (by rfl) ⟨8294693, by rfl⟩ : syracuseStep 11059591 = 16589387) B16589387
theorem B2589071 : Blo 1725063 2589071 := bstep (se 1 (by rfl) ⟨1941803, by rfl⟩ : syracuseStep 2589071 = 3883607) B3883607
theorem B6218137 : Blo 1725063 6218137 := bstep (se 2 (by rfl) ⟨2331801, by rfl⟩ : syracuseStep 6218137 = 4663603) B4663603
theorem B2589113 : Blo 1725063 2589113 := bstep (se 2 (by rfl) ⟨970917, by rfl⟩ : syracuseStep 2589113 = 1941835) B1941835
theorem B18661853 : Blo 1725063 18661853 := bstep (se 3 (by rfl) ⟨3499097, by rfl⟩ : syracuseStep 18661853 = 6998195) B6998195
theorem B2589191 : Blo 1725063 2589191 := bstep (se 1 (by rfl) ⟨1941893, by rfl⟩ : syracuseStep 2589191 = 3883787) B3883787
theorem B2490895 : Blo 1725063 2490895 := bstep (se 1 (by rfl) ⟨1868171, by rfl⟩ : syracuseStep 2490895 = 3736343) B3736343
theorem B3883535 : Blo 1725063 3883535 := bstep (se 1 (by rfl) ⟨2912651, by rfl⟩ : syracuseStep 3883535 = 5825303) B5825303
theorem B5251613 : Blo 1725063 5251613 := bstep (se 3 (by rfl) ⟨984677, by rfl⟩ : syracuseStep 5251613 = 1969355) B1969355
theorem B3883553 : Blo 1725063 3883553 := bstep (se 2 (by rfl) ⟨1456332, by rfl⟩ : syracuseStep 3883553 = 2912665) B2912665
theorem B2589227 : Blo 1725063 2589227 := bstep (se 1 (by rfl) ⟨1941920, by rfl⟩ : syracuseStep 2589227 = 3883841) B3883841
theorem B2589257 : Blo 1725063 2589257 := bstep (se 2 (by rfl) ⟨970971, by rfl⟩ : syracuseStep 2589257 = 1941943) B1941943
theorem B1942159 : Blo 1725063 1942159 := bstep (se 1 (by rfl) ⟨1456619, by rfl⟩ : syracuseStep 1942159 = 2913239) B2913239
theorem B4145849 : Blo 1725063 4145849 := bstep (se 2 (by rfl) ⟨1554693, by rfl⟩ : syracuseStep 4145849 = 3109387) B3109387
theorem B2589371 : Blo 1725063 2589371 := bstep (se 1 (by rfl) ⟨1942028, by rfl⟩ : syracuseStep 2589371 = 3884057) B3884057
theorem B13107905 : Blo 1725063 13107905 := bstep (se 2 (by rfl) ⟨4915464, by rfl⟩ : syracuseStep 13107905 = 9830929) B9830929
theorem B2589431 : Blo 1725063 2589431 := bstep (se 1 (by rfl) ⟨1942073, by rfl⟩ : syracuseStep 2589431 = 3884147) B3884147
theorem B4367105 : Blo 1725063 4367105 := bstep (se 2 (by rfl) ⟨1637664, by rfl⟩ : syracuseStep 4367105 = 3275329) B3275329
theorem B2589455 : Blo 1725063 2589455 := bstep (se 1 (by rfl) ⟨1942091, by rfl⟩ : syracuseStep 2589455 = 3884183) B3884183
theorem B2589497 : Blo 1725063 2589497 := bstep (se 2 (by rfl) ⟨971061, by rfl⟩ : syracuseStep 2589497 = 1942123) B1942123
theorem B3883895 : Blo 1725063 3883895 := bstep (se 1 (by rfl) ⟨2912921, by rfl⟩ : syracuseStep 3883895 = 5825843) B5825843
theorem B2589575 : Blo 1725063 2589575 := bstep (se 1 (by rfl) ⟨1942181, by rfl⟩ : syracuseStep 2589575 = 3884363) B3884363
theorem B2589611 : Blo 1725063 2589611 := bstep (se 1 (by rfl) ⟨1942208, by rfl⟩ : syracuseStep 2589611 = 3884417) B3884417
theorem B5825465 : Blo 1725063 5825465 := bstep (se 2 (by rfl) ⟨2184549, by rfl⟩ : syracuseStep 5825465 = 4369099) B4369099
theorem B2589641 : Blo 1725063 2589641 := bstep (se 2 (by rfl) ⟨971115, by rfl⟩ : syracuseStep 2589641 = 1942231) B1942231
theorem B3884075 : Blo 1725063 3884075 := bstep (se 1 (by rfl) ⟨2913056, by rfl⟩ : syracuseStep 3884075 = 5826113) B5826113
theorem B2589755 : Blo 1725063 2589755 := bstep (se 1 (by rfl) ⟨1942316, by rfl⟩ : syracuseStep 2589755 = 3884633) B3884633
theorem B4916285 : Blo 1725063 4916285 := bstep (se 3 (by rfl) ⟨921803, by rfl⟩ : syracuseStep 4916285 = 1843607) B1843607
theorem B4367479 : Blo 1725063 4367479 := bstep (se 1 (by rfl) ⟨3275609, by rfl⟩ : syracuseStep 4367479 = 6551219) B6551219
theorem B2589815 : Blo 1725063 2589815 := bstep (se 1 (by rfl) ⟨1942361, by rfl⟩ : syracuseStep 2589815 = 3884723) B3884723
theorem B1942663 : Blo 1725063 1942663 := bstep (se 1 (by rfl) ⟨1456997, by rfl⟩ : syracuseStep 1942663 = 2913995) B2913995
theorem B2589839 : Blo 1725063 2589839 := bstep (se 1 (by rfl) ⟨1942379, by rfl⟩ : syracuseStep 2589839 = 3884759) B3884759
theorem B2589881 : Blo 1725063 2589881 := bstep (se 2 (by rfl) ⟨971205, by rfl⟩ : syracuseStep 2589881 = 1942411) B1942411
theorem B3278009 : Blo 1725063 3278009 := bstep (se 2 (by rfl) ⟨1229253, by rfl⟩ : syracuseStep 3278009 = 2458507) B2458507
theorem B2589959 : Blo 1725063 2589959 := bstep (se 1 (by rfl) ⟨1942469, by rfl⟩ : syracuseStep 2589959 = 3884939) B3884939
theorem B5530913 : Blo 1725063 5530913 := bstep (se 2 (by rfl) ⟨2074092, by rfl⟩ : syracuseStep 5530913 = 4148185) B4148185
theorem B4916513 : Blo 1725063 4916513 := bstep (se 2 (by rfl) ⟨1843692, by rfl⟩ : syracuseStep 4916513 = 3687385) B3687385
theorem B2589995 : Blo 1725063 2589995 := bstep (se 1 (by rfl) ⟨1942496, by rfl⟩ : syracuseStep 2589995 = 3884993) B3884993
theorem B1942843 : Blo 1725063 1942843 := bstep (se 1 (by rfl) ⟨1457132, by rfl⟩ : syracuseStep 1942843 = 2914265) B2914265
theorem B2590025 : Blo 1725063 2590025 := bstep (se 2 (by rfl) ⟨971259, by rfl⟩ : syracuseStep 2590025 = 1942519) B1942519
theorem B8734067 : Blo 1725063 8734067 := bstep (se 1 (by rfl) ⟨6550550, by rfl⟩ : syracuseStep 8734067 = 13101101) B13101101
theorem B3884435 : Blo 1725063 3884435 := bstep (se 1 (by rfl) ⟨2913326, by rfl⟩ : syracuseStep 3884435 = 5826653) B5826653
theorem B8742329 : Blo 1725063 8742329 := bstep (se 2 (by rfl) ⟨3278373, by rfl⟩ : syracuseStep 8742329 = 6556747) B6556747
theorem B2590139 : Blo 1725063 2590139 := bstep (se 1 (by rfl) ⟨1942604, by rfl⟩ : syracuseStep 2590139 = 3885209) B3885209
theorem B3884489 : Blo 1725063 3884489 := bstep (se 2 (by rfl) ⟨1456683, by rfl⟩ : syracuseStep 3884489 = 2913367) B2913367
theorem B2590199 : Blo 1725063 2590199 := bstep (se 1 (by rfl) ⟨1942649, by rfl⟩ : syracuseStep 2590199 = 3885299) B3885299
theorem B5826059 : Blo 1725063 5826059 := bstep (se 1 (by rfl) ⟨4369544, by rfl⟩ : syracuseStep 5826059 = 8739089) B8739089
theorem B2590223 : Blo 1725063 2590223 := bstep (se 1 (by rfl) ⟨1942667, by rfl⟩ : syracuseStep 2590223 = 3885335) B3885335
theorem B4367915 : Blo 1725063 4367915 := bstep (se 1 (by rfl) ⟨3275936, by rfl⟩ : syracuseStep 4367915 = 6551873) B6551873
theorem B2590265 : Blo 1725063 2590265 := bstep (se 2 (by rfl) ⟨971349, by rfl⟩ : syracuseStep 2590265 = 1942699) B1942699
theorem B5826167 : Blo 1725063 5826167 := bstep (se 1 (by rfl) ⟨4369625, by rfl⟩ : syracuseStep 5826167 = 8739251) B8739251
theorem B2074231 : Blo 1725063 2074231 := bstep (se 1 (by rfl) ⟨1555673, by rfl⟩ : syracuseStep 2074231 = 3111347) B3111347
theorem B4916855 : Blo 1725063 4916855 := bstep (se 1 (by rfl) ⟨3687641, by rfl⟩ : syracuseStep 4916855 = 7375283) B7375283
theorem B2590343 : Blo 1725063 2590343 := bstep (se 1 (by rfl) ⟨1942757, by rfl⟩ : syracuseStep 2590343 = 3885515) B3885515
theorem B2590379 : Blo 1725063 2590379 := bstep (se 1 (by rfl) ⟨1942784, by rfl⟩ : syracuseStep 2590379 = 3885569) B3885569
theorem B245622449 : Blo 1725063 245622449 := bstep (se 2 (by rfl) ⟨92108418, by rfl⟩ : syracuseStep 245622449 = 184216837) B184216837
theorem B23627443 : Blo 1725063 23627443 := bstep (se 1 (by rfl) ⟨17720582, by rfl⟩ : syracuseStep 23627443 = 35441165) B35441165
theorem B2590409 : Blo 1725063 2590409 := bstep (se 2 (by rfl) ⟨971403, by rfl⟩ : syracuseStep 2590409 = 1942807) B1942807
theorem B6219521 : Blo 1725063 6219521 := bstep (se 2 (by rfl) ⟨2332320, by rfl⟩ : syracuseStep 6219521 = 4664641) B4664641
theorem B39864113 : Blo 1725063 39864113 := bstep (se 2 (by rfl) ⟨14949042, by rfl⟩ : syracuseStep 39864113 = 29898085) B29898085
theorem B4728635 : Blo 1725063 4728635 := bstep (se 1 (by rfl) ⟨3546476, by rfl⟩ : syracuseStep 4728635 = 7092953) B7092953
theorem B2590523 : Blo 1725063 2590523 := bstep (se 1 (by rfl) ⟨1942892, by rfl⟩ : syracuseStep 2590523 = 3885785) B3885785
theorem B4147031 : Blo 1725063 4147031 := bstep (se 1 (by rfl) ⟨3110273, by rfl⟩ : syracuseStep 4147031 = 6220547) B6220547
theorem B8734553 : Blo 1725063 8734553 := bstep (se 2 (by rfl) ⟨3275457, by rfl⟩ : syracuseStep 8734553 = 6550915) B6550915
theorem B4982647 : Blo 1725063 4982647 := bstep (se 1 (by rfl) ⟨3736985, by rfl⟩ : syracuseStep 4982647 = 7473971) B7473971
theorem B2590583 : Blo 1725063 2590583 := bstep (se 1 (by rfl) ⟨1942937, by rfl⟩ : syracuseStep 2590583 = 3885875) B3885875
theorem B12437401 : Blo 1725063 12437401 := bstep (se 2 (by rfl) ⟨4664025, by rfl⟩ : syracuseStep 12437401 = 9328051) B9328051
theorem B3885191 : Blo 1725063 3885191 := bstep (se 1 (by rfl) ⟨2913893, by rfl⟩ : syracuseStep 3885191 = 5827787) B5827787
theorem B5826761 : Blo 1725063 5826761 := bstep (se 2 (by rfl) ⟨2185035, by rfl⟩ : syracuseStep 5826761 = 4370071) B4370071
theorem B3197227 : Blo 1725063 3197227 := bstep (se 1 (by rfl) ⟨2397920, by rfl⟩ : syracuseStep 3197227 = 4795841) B4795841
theorem B3885371 : Blo 1725063 3885371 := bstep (se 1 (by rfl) ⟨2914028, by rfl⟩ : syracuseStep 3885371 = 5828057) B5828057
theorem B4368755 : Blo 1725063 4368755 := bstep (se 1 (by rfl) ⟨3276566, by rfl⟩ : syracuseStep 4368755 = 6553133) B6553133
theorem B4368775 : Blo 1725063 4368775 := bstep (se 1 (by rfl) ⟨3276581, by rfl⟩ : syracuseStep 4368775 = 6553163) B6553163
theorem B3885497 : Blo 1725063 3885497 := bstep (se 2 (by rfl) ⟨1457061, by rfl⟩ : syracuseStep 3885497 = 2914123) B2914123
theorem B9832913 : Blo 1725063 9832913 := bstep (se 2 (by rfl) ⟨3687342, by rfl⟩ : syracuseStep 9832913 = 7374685) B7374685
theorem B3738145 : Blo 1725063 3738145 := bstep (se 2 (by rfl) ⟨1401804, by rfl⟩ : syracuseStep 3738145 = 2803609) B2803609
theorem B6556247 : Blo 1725063 6556247 := bstep (se 1 (by rfl) ⟨4917185, by rfl⟩ : syracuseStep 6556247 = 9834371) B9834371
theorem B4369049 : Blo 1725063 4369049 := bstep (se 2 (by rfl) ⟨1638393, by rfl⟩ : syracuseStep 4369049 = 3276787) B3276787
theorem B70838981 : Blo 1725063 70838981 := bstep (se 4 (by rfl) ⟨6641154, by rfl⟩ : syracuseStep 70838981 = 13282309) B13282309
theorem B459967247 : Blo 1725063 459967247 := bstep (se 1 (by rfl) ⟨344975435, by rfl⟩ : syracuseStep 459967247 = 689950871) B689950871
theorem B3885839 : Blo 1725063 3885839 := bstep (se 1 (by rfl) ⟨2914379, by rfl⟩ : syracuseStep 3885839 = 5828759) B5828759
theorem B3885857 : Blo 1725063 3885857 := bstep (se 2 (by rfl) ⟨1457196, by rfl⟩ : syracuseStep 3885857 = 2914393) B2914393
theorem B4369211 : Blo 1725063 4369211 := bstep (se 1 (by rfl) ⟨3276908, by rfl⟩ : syracuseStep 4369211 = 6553817) B6553817
theorem B5827463 : Blo 1725063 5827463 := bstep (se 1 (by rfl) ⟨4370597, by rfl⟩ : syracuseStep 5827463 = 8741195) B8741195
theorem B4369423 : Blo 1725063 4369423 := bstep (se 1 (by rfl) ⟨3277067, by rfl⟩ : syracuseStep 4369423 = 6554135) B6554135
theorem B6556733 : Blo 1725063 6556733 := bstep (se 3 (by rfl) ⟨1229387, by rfl⟩ : syracuseStep 6556733 = 2458775) B2458775
theorem B16813229 : Blo 1725063 16813229 := bstep (se 3 (by rfl) ⟨3152480, by rfl⟩ : syracuseStep 16813229 = 6304961) B6304961
theorem B19664045 : Blo 1725063 19664045 := bstep (se 3 (by rfl) ⟨3687008, by rfl⟩ : syracuseStep 19664045 = 7374017) B7374017
theorem B5827841 : Blo 1725063 5827841 := bstep (se 2 (by rfl) ⟨2185440, by rfl⟩ : syracuseStep 5827841 = 4370881) B4370881
theorem B4369697 : Blo 1725063 4369697 := bstep (se 2 (by rfl) ⟨1638636, by rfl⟩ : syracuseStep 4369697 = 3277273) B3277273
theorem B2911531 : Blo 1725063 2911531 := bstep (se 1 (by rfl) ⟨2183648, by rfl⟩ : syracuseStep 2911531 = 4367297) B4367297
theorem B2764091 : Blo 1725063 2764091 := bstep (se 1 (by rfl) ⟨2073068, by rfl⟩ : syracuseStep 2764091 = 4146137) B4146137
theorem B2911673 : Blo 1725063 2911673 := bstep (se 2 (by rfl) ⟨1091877, by rfl⟩ : syracuseStep 2911673 = 2183755) B2183755
theorem B2993609 : Blo 1725063 2993609 := bstep (se 2 (by rfl) ⟨1122603, by rfl⟩ : syracuseStep 2993609 = 2245207) B2245207
theorem B4984379 : Blo 1725063 4984379 := bstep (se 1 (by rfl) ⟨3738284, by rfl⟩ : syracuseStep 4984379 = 7476569) B7476569
theorem B9334561 : Blo 1725063 9334561 := bstep (se 2 (by rfl) ⟨3500460, by rfl⟩ : syracuseStep 9334561 = 7000921) B7000921
theorem B13463347 : Blo 1725063 13463347 := bstep (se 1 (by rfl) ⟨10097510, by rfl⟩ : syracuseStep 13463347 = 20195021) B20195021
theorem B1748795 : Blo 1725063 1748795 := bstep (se 1 (by rfl) ⟨1311596, by rfl⟩ : syracuseStep 1748795 = 2623193) B2623193
theorem B3321719 : Blo 1725063 3321719 := bstep (se 1 (by rfl) ⟨2491289, by rfl⟩ : syracuseStep 3321719 = 4982579) B4982579
theorem B8736659 : Blo 1725063 8736659 := bstep (se 1 (by rfl) ⟨6552494, by rfl⟩ : syracuseStep 8736659 = 13104989) B13104989
theorem B13111307 : Blo 1725063 13111307 := bstep (se 1 (by rfl) ⟨9833480, by rfl⟩ : syracuseStep 13111307 = 19666961) B19666961
theorem B5828651 : Blo 1725063 5828651 := bstep (se 1 (by rfl) ⟨4371488, by rfl⟩ : syracuseStep 5828651 = 8742977) B8742977
theorem B7376957 : Blo 1725063 7376957 := bstep (se 3 (by rfl) ⟨1383179, by rfl⟩ : syracuseStep 7376957 = 2766359) B2766359
theorem B7368823 : Blo 1725063 7368823 := bstep (se 1 (by rfl) ⟨5526617, by rfl⟩ : syracuseStep 7368823 = 11053235) B11053235
theorem B2912375 : Blo 1725063 2912375 := bstep (se 1 (by rfl) ⟨2184281, by rfl⟩ : syracuseStep 2912375 = 4368563) B4368563
theorem B2183431 : Blo 1725063 2183431 := bstep (se 1 (by rfl) ⟨1637573, by rfl⟩ : syracuseStep 2183431 = 3275147) B3275147
theorem B4370699 : Blo 1725063 4370699 := bstep (se 1 (by rfl) ⟨3278024, by rfl⟩ : syracuseStep 4370699 = 6556049) B6556049
theorem B9834803 : Blo 1725063 9834803 := bstep (se 1 (by rfl) ⟨7376102, by rfl⟩ : syracuseStep 9834803 = 14752205) B14752205
theorem B2912827 : Blo 1725063 2912827 := bstep (se 1 (by rfl) ⟨2184620, by rfl⟩ : syracuseStep 2912827 = 4369241) B4369241
theorem B1725063 : Blo 1725063 1725063 := bstep (se 1 (by rfl) ⟨1293797, by rfl⟩ : syracuseStep 1725063 = 2587595) B2587595
theorem B1725071 : Blo 1725063 1725071 := bstep (se 1 (by rfl) ⟨1293803, by rfl⟩ : syracuseStep 1725071 = 2587607) B2587607
theorem B2183851 : Blo 1725063 2183851 := bstep (se 1 (by rfl) ⟨1637888, by rfl⟩ : syracuseStep 2183851 = 3275777) B3275777
theorem B1725115 : Blo 1725063 1725115 := bstep (se 1 (by rfl) ⟨1293836, by rfl⟩ : syracuseStep 1725115 = 2587673) B2587673
theorem B6550217 : Blo 1725063 6550217 := bstep (se 2 (by rfl) ⟨2456331, by rfl⟩ : syracuseStep 6550217 = 4912663) B4912663
theorem B2912969 : Blo 1725063 2912969 := bstep (se 2 (by rfl) ⟨1092363, by rfl⟩ : syracuseStep 2912969 = 2184727) B2184727
theorem B2765513 : Blo 1725063 2765513 := bstep (se 2 (by rfl) ⟨1037067, by rfl⟩ : syracuseStep 2765513 = 2074135) B2074135
theorem B8090369 : Blo 1725063 8090369 := bstep (se 2 (by rfl) ⟨3033888, by rfl⟩ : syracuseStep 8090369 = 6067777) B6067777
theorem B1725191 : Blo 1725063 1725191 := bstep (se 1 (by rfl) ⟨1293893, by rfl⟩ : syracuseStep 1725191 = 2587787) B2587787
theorem B1725199 : Blo 1725063 1725199 := bstep (se 1 (by rfl) ⟨1293899, by rfl⟩ : syracuseStep 1725199 = 2587799) B2587799
theorem B1725243 : Blo 1725063 1725243 := bstep (se 1 (by rfl) ⟨1293932, by rfl⟩ : syracuseStep 1725243 = 2587865) B2587865
theorem B1725319 : Blo 1725063 1725319 := bstep (se 1 (by rfl) ⟨1293989, by rfl⟩ : syracuseStep 1725319 = 2587979) B2587979
theorem B1725327 : Blo 1725063 1725327 := bstep (se 1 (by rfl) ⟨1293995, by rfl⟩ : syracuseStep 1725327 = 2587991) B2587991
theorem B2184079 : Blo 1725063 2184079 := bstep (se 1 (by rfl) ⟨1638059, by rfl⟩ : syracuseStep 2184079 = 3276119) B3276119
theorem B4371347 : Blo 1725063 4371347 := bstep (se 1 (by rfl) ⟨3278510, by rfl⟩ : syracuseStep 4371347 = 6557021) B6557021
theorem B21566371 : Blo 1725063 21566371 := bstep (se 1 (by rfl) ⟨16174778, by rfl⟩ : syracuseStep 21566371 = 32349557) B32349557
theorem B1725371 : Blo 1725063 1725371 := bstep (se 1 (by rfl) ⟨1294028, by rfl⟩ : syracuseStep 1725371 = 2588057) B2588057
theorem B9966539 : Blo 1725063 9966539 := bstep (se 1 (by rfl) ⟨7474904, by rfl⟩ : syracuseStep 9966539 = 14949809) B14949809
theorem B1725447 : Blo 1725063 1725447 := bstep (se 1 (by rfl) ⟨1294085, by rfl⟩ : syracuseStep 1725447 = 2588171) B2588171
theorem B1725455 : Blo 1725063 1725455 := bstep (se 1 (by rfl) ⟨1294091, by rfl⟩ : syracuseStep 1725455 = 2588183) B2588183
theorem B1725499 : Blo 1725063 1725499 := bstep (se 1 (by rfl) ⟨1294124, by rfl⟩ : syracuseStep 1725499 = 2588249) B2588249
theorem B1725575 : Blo 1725063 1725575 := bstep (se 1 (by rfl) ⟨1294181, by rfl⟩ : syracuseStep 1725575 = 2588363) B2588363
theorem B1725583 : Blo 1725063 1725583 := bstep (se 1 (by rfl) ⟨1294187, by rfl⟩ : syracuseStep 1725583 = 2588375) B2588375
theorem B1725627 : Blo 1725063 1725627 := bstep (se 1 (by rfl) ⟨1294220, by rfl⟩ : syracuseStep 1725627 = 2588441) B2588441
theorem B1725703 : Blo 1725063 1725703 := bstep (se 1 (by rfl) ⟨1294277, by rfl⟩ : syracuseStep 1725703 = 2588555) B2588555
theorem B1725711 : Blo 1725063 1725711 := bstep (se 1 (by rfl) ⟨1294283, by rfl⟩ : syracuseStep 1725711 = 2588567) B2588567
theorem B8295695 : Blo 1725063 8295695 := bstep (se 1 (by rfl) ⟨6221771, by rfl⟩ : syracuseStep 8295695 = 12443543) B12443543
theorem B5985569 : Blo 1725063 5985569 := bstep (se 2 (by rfl) ⟨2244588, by rfl⟩ : syracuseStep 5985569 = 4489177) B4489177
theorem B1725755 : Blo 1725063 1725755 := bstep (se 1 (by rfl) ⟨1294316, by rfl⟩ : syracuseStep 1725755 = 2588633) B2588633
theorem B1725831 : Blo 1725063 1725831 := bstep (se 1 (by rfl) ⟨1294373, by rfl⟩ : syracuseStep 1725831 = 2588747) B2588747
theorem B2913671 : Blo 1725063 2913671 := bstep (se 1 (by rfl) ⟨2185253, by rfl⟩ : syracuseStep 2913671 = 4370507) B4370507
theorem B1725839 : Blo 1725063 1725839 := bstep (se 1 (by rfl) ⟨1294379, by rfl⟩ : syracuseStep 1725839 = 2588759) B2588759
theorem B1725883 : Blo 1725063 1725883 := bstep (se 1 (by rfl) ⟨1294412, by rfl⟩ : syracuseStep 1725883 = 2588825) B2588825
theorem B1725959 : Blo 1725063 1725959 := bstep (se 1 (by rfl) ⟨1294469, by rfl⟩ : syracuseStep 1725959 = 2588939) B2588939
theorem B4666891 : Blo 1725063 4666891 := bstep (se 1 (by rfl) ⟨3500168, by rfl⟩ : syracuseStep 4666891 = 7000337) B7000337
theorem B1725967 : Blo 1725063 1725967 := bstep (se 1 (by rfl) ⟨1294475, by rfl⟩ : syracuseStep 1725967 = 2588951) B2588951
theorem B8295965 : Blo 1725063 8295965 := bstep (se 3 (by rfl) ⟨1555493, by rfl⟩ : syracuseStep 8295965 = 3110987) B3110987
theorem B1726011 : Blo 1725063 1726011 := bstep (se 1 (by rfl) ⟨1294508, by rfl⟩ : syracuseStep 1726011 = 2589017) B2589017
theorem B7370327 : Blo 1725063 7370327 := bstep (se 1 (by rfl) ⟨5527745, by rfl⟩ : syracuseStep 7370327 = 11055491) B11055491
theorem B2184823 : Blo 1725063 2184823 := bstep (se 1 (by rfl) ⟨1638617, by rfl⟩ : syracuseStep 2184823 = 3277235) B3277235
theorem B4666999 : Blo 1725063 4666999 := bstep (se 1 (by rfl) ⟨3500249, by rfl⟩ : syracuseStep 4666999 = 7000499) B7000499
theorem B1726087 : Blo 1725063 1726087 := bstep (se 1 (by rfl) ⟨1294565, by rfl⟩ : syracuseStep 1726087 = 2589131) B2589131
theorem B1726095 : Blo 1725063 1726095 := bstep (se 1 (by rfl) ⟨1294571, by rfl⟩ : syracuseStep 1726095 = 2589143) B2589143
theorem B9828013 : Blo 1725063 9828013 := bstep (se 3 (by rfl) ⟨1842752, by rfl⟩ : syracuseStep 9828013 = 3685505) B3685505
theorem B1726139 : Blo 1725063 1726139 := bstep (se 1 (by rfl) ⟨1294604, by rfl⟩ : syracuseStep 1726139 = 2589209) B2589209
theorem B11065025 : Blo 1725063 11065025 := bstep (se 2 (by rfl) ⟨4149384, by rfl⟩ : syracuseStep 11065025 = 8298769) B8298769
theorem B1726215 : Blo 1725063 1726215 := bstep (se 1 (by rfl) ⟨1294661, by rfl⟩ : syracuseStep 1726215 = 2589323) B2589323
theorem B1726223 : Blo 1725063 1726223 := bstep (se 1 (by rfl) ⟨1294667, by rfl⟩ : syracuseStep 1726223 = 2589335) B2589335
theorem B1726267 : Blo 1725063 1726267 := bstep (se 1 (by rfl) ⟨1294700, by rfl⟩ : syracuseStep 1726267 = 2589401) B2589401
theorem B1726343 : Blo 1725063 1726343 := bstep (se 1 (by rfl) ⟨1294757, by rfl⟩ : syracuseStep 1726343 = 2589515) B2589515
theorem B1726351 : Blo 1725063 1726351 := bstep (se 1 (by rfl) ⟨1294763, by rfl⟩ : syracuseStep 1726351 = 2589527) B2589527
theorem B13113251 : Blo 1725063 13113251 := bstep (se 1 (by rfl) ⟨9834938, by rfl⟩ : syracuseStep 13113251 = 19669877) B19669877
theorem B1726395 : Blo 1725063 1726395 := bstep (se 1 (by rfl) ⟨1294796, by rfl⟩ : syracuseStep 1726395 = 2589593) B2589593
theorem B2185147 : Blo 1725063 2185147 := bstep (se 1 (by rfl) ⟨1638860, by rfl⟩ : syracuseStep 2185147 = 3277721) B3277721
theorem B1726471 : Blo 1725063 1726471 := bstep (se 1 (by rfl) ⟨1294853, by rfl⟩ : syracuseStep 1726471 = 2589707) B2589707
theorem B1726479 : Blo 1725063 1726479 := bstep (se 1 (by rfl) ⟨1294859, by rfl⟩ : syracuseStep 1726479 = 2589719) B2589719
theorem B2914319 : Blo 1725063 2914319 := bstep (se 1 (by rfl) ⟨2185739, by rfl⟩ : syracuseStep 2914319 = 4371479) B4371479
theorem B1726523 : Blo 1725063 1726523 := bstep (se 1 (by rfl) ⟨1294892, by rfl⟩ : syracuseStep 1726523 = 2589785) B2589785
theorem B16595077 : Blo 1725063 16595077 := bstep (se 4 (by rfl) ⟨1555788, by rfl⟩ : syracuseStep 16595077 = 3111577) B3111577
theorem B1726599 : Blo 1725063 1726599 := bstep (se 1 (by rfl) ⟨1294949, by rfl⟩ : syracuseStep 1726599 = 2589899) B2589899
theorem B1726607 : Blo 1725063 1726607 := bstep (se 1 (by rfl) ⟨1294955, by rfl⟩ : syracuseStep 1726607 = 2589911) B2589911
theorem B1726651 : Blo 1725063 1726651 := bstep (se 1 (by rfl) ⟨1294988, by rfl⟩ : syracuseStep 1726651 = 2589977) B2589977
theorem B1726727 : Blo 1725063 1726727 := bstep (se 1 (by rfl) ⟨1295045, by rfl⟩ : syracuseStep 1726727 = 2590091) B2590091
theorem B1726735 : Blo 1725063 1726735 := bstep (se 1 (by rfl) ⟨1295051, by rfl⟩ : syracuseStep 1726735 = 2590103) B2590103
theorem B1726779 : Blo 1725063 1726779 := bstep (se 1 (by rfl) ⟨1295084, by rfl⟩ : syracuseStep 1726779 = 2590169) B2590169
theorem B1726855 : Blo 1725063 1726855 := bstep (se 1 (by rfl) ⟨1295141, by rfl⟩ : syracuseStep 1726855 = 2590283) B2590283
theorem B1726863 : Blo 1725063 1726863 := bstep (se 1 (by rfl) ⟨1295147, by rfl⟩ : syracuseStep 1726863 = 2590295) B2590295
theorem B24869267 : Blo 1725063 24869267 := bstep (se 1 (by rfl) ⟨18651950, by rfl⟩ : syracuseStep 24869267 = 37303901) B37303901
theorem B5822873 : Blo 1725063 5822873 := bstep (se 2 (by rfl) ⟨2183577, by rfl⟩ : syracuseStep 5822873 = 4367155) B4367155
theorem B2185643 : Blo 1725063 2185643 := bstep (se 1 (by rfl) ⟨1639232, by rfl⟩ : syracuseStep 2185643 = 3278465) B3278465
theorem B11057593 : Blo 1725063 11057593 := bstep (se 2 (by rfl) ⟨4146597, by rfl⟩ : syracuseStep 11057593 = 8293195) B8293195
theorem B1726907 : Blo 1725063 1726907 := bstep (se 1 (by rfl) ⟨1295180, by rfl⟩ : syracuseStep 1726907 = 2590361) B2590361
theorem B85170649 : Blo 1725063 85170649 := bstep (se 2 (by rfl) ⟨31938993, by rfl⟩ : syracuseStep 85170649 = 63877987) B63877987
theorem B1726983 : Blo 1725063 1726983 := bstep (se 1 (by rfl) ⟨1295237, by rfl⟩ : syracuseStep 1726983 = 2590475) B2590475
theorem B1726991 : Blo 1725063 1726991 := bstep (se 1 (by rfl) ⟨1295243, by rfl⟩ : syracuseStep 1726991 = 2590487) B2590487
theorem B4913723 : Blo 1725063 4913723 := bstep (se 1 (by rfl) ⟨3685292, by rfl⟩ : syracuseStep 4913723 = 7370585) B7370585
theorem B1727035 : Blo 1725063 1727035 := bstep (se 1 (by rfl) ⟨1295276, by rfl⟩ : syracuseStep 1727035 = 2590553) B2590553
theorem B4913779 : Blo 1725063 4913779 := bstep (se 1 (by rfl) ⟨3685334, by rfl⟩ : syracuseStep 4913779 = 7370669) B7370669
theorem B3881591 : Blo 1725063 3881591 := bstep (se 1 (by rfl) ⟨2911193, by rfl⟩ : syracuseStep 3881591 = 5822387) B5822387
theorem B8854217 : Blo 1725063 8854217 := bstep (se 2 (by rfl) ⟨3320331, by rfl⟩ : syracuseStep 8854217 = 6640663) B6640663
theorem B3881771 : Blo 1725063 3881771 := bstep (se 1 (by rfl) ⟨2911328, by rfl⟩ : syracuseStep 3881771 = 5822657) B5822657
theorem B3275579 : Blo 1725063 3275579 := bstep (se 1 (by rfl) ⟨2456684, by rfl⟩ : syracuseStep 3275579 = 4913369) B4913369
theorem B8403857 : Blo 1725063 8403857 := bstep (se 2 (by rfl) ⟨3151446, by rfl⟩ : syracuseStep 8403857 = 6302893) B6302893
theorem B19659671 : Blo 1725063 19659671 := bstep (se 1 (by rfl) ⟨14744753, by rfl⟩ : syracuseStep 19659671 = 29489507) B29489507
theorem B8739737 : Blo 1725063 8739737 := bstep (se 2 (by rfl) ⟨3277401, by rfl⟩ : syracuseStep 8739737 = 6554803) B6554803
theorem B4914121 : Blo 1725063 4914121 := bstep (se 2 (by rfl) ⟨1842795, by rfl⟩ : syracuseStep 4914121 = 3685591) B3685591
theorem B2587655 : Blo 1725063 2587655 := bstep (se 1 (by rfl) ⟨1940741, by rfl⟩ : syracuseStep 2587655 = 3881483) B3881483
theorem B2587691 : Blo 1725063 2587691 := bstep (se 1 (by rfl) ⟨1940768, by rfl⟩ : syracuseStep 2587691 = 3881537) B3881537
theorem B2587721 : Blo 1725063 2587721 := bstep (se 2 (by rfl) ⟨970395, by rfl⟩ : syracuseStep 2587721 = 1940791) B1940791
theorem B5823575 : Blo 1725063 5823575 := bstep (se 1 (by rfl) ⟨4367681, by rfl⟩ : syracuseStep 5823575 = 8735363) B8735363
theorem B5528695 : Blo 1725063 5528695 := bstep (se 1 (by rfl) ⟨4146521, by rfl⟩ : syracuseStep 5528695 = 8293043) B8293043
theorem B3882131 : Blo 1725063 3882131 := bstep (se 1 (by rfl) ⟨2911598, by rfl⟩ : syracuseStep 3882131 = 5823197) B5823197
theorem B2587835 : Blo 1725063 2587835 := bstep (se 1 (by rfl) ⟨1940876, by rfl⟩ : syracuseStep 2587835 = 3881753) B3881753
theorem B3882185 : Blo 1725063 3882185 := bstep (se 2 (by rfl) ⟨1455819, by rfl⟩ : syracuseStep 3882185 = 2911639) B2911639
theorem B2587895 : Blo 1725063 2587895 := bstep (se 1 (by rfl) ⟨1940921, by rfl⟩ : syracuseStep 2587895 = 3881843) B3881843
theorem B2587919 : Blo 1725063 2587919 := bstep (se 1 (by rfl) ⟨1940939, by rfl⟩ : syracuseStep 2587919 = 3881879) B3881879
theorem B3497249 : Blo 1725063 3497249 := bstep (se 2 (by rfl) ⟨1311468, by rfl⟩ : syracuseStep 3497249 = 2622937) B2622937
theorem B3276065 : Blo 1725063 3276065 := bstep (se 2 (by rfl) ⟨1228524, by rfl⟩ : syracuseStep 3276065 = 2457049) B2457049
theorem B136330541 : Blo 1725063 136330541 := bstep (se 3 (by rfl) ⟨25561976, by rfl⟩ : syracuseStep 136330541 = 51123953) B51123953
theorem B2587961 : Blo 1725063 2587961 := bstep (se 2 (by rfl) ⟨970485, by rfl⟩ : syracuseStep 2587961 = 1940971) B1940971
theorem B2588039 : Blo 1725063 2588039 := bstep (se 1 (by rfl) ⟨1941029, by rfl⟩ : syracuseStep 2588039 = 3882059) B3882059
theorem B32374151 : Blo 1725063 32374151 := bstep (se 1 (by rfl) ⟨24280613, by rfl⟩ : syracuseStep 32374151 = 48561227) B48561227
theorem B2588075 : Blo 1725063 2588075 := bstep (se 1 (by rfl) ⟨1941056, by rfl⟩ : syracuseStep 2588075 = 3882113) B3882113
theorem B3276217 : Blo 1725063 3276217 := bstep (se 2 (by rfl) ⟨1228581, by rfl⟩ : syracuseStep 3276217 = 2457163) B2457163
theorem B2588105 : Blo 1725063 2588105 := bstep (se 2 (by rfl) ⟨970539, by rfl⟩ : syracuseStep 2588105 = 1941079) B1941079
theorem B7372241 : Blo 1725063 7372241 := bstep (se 2 (by rfl) ⟨2764590, by rfl⟩ : syracuseStep 7372241 = 5529181) B5529181
theorem B66371075 : Blo 1725063 66371075 := bstep (se 1 (by rfl) ⟨49778306, by rfl⟩ : syracuseStep 66371075 = 99556613) B99556613
theorem B1941007 : Blo 1725063 1941007 := bstep (se 1 (by rfl) ⟨1455755, by rfl⟩ : syracuseStep 1941007 = 2911511) B2911511
theorem B5529131 : Blo 1725063 5529131 := bstep (se 1 (by rfl) ⟨4146848, by rfl⟩ : syracuseStep 5529131 = 8293697) B8293697
theorem B2588219 : Blo 1725063 2588219 := bstep (se 1 (by rfl) ⟨1941164, by rfl⟩ : syracuseStep 2588219 = 3882329) B3882329
theorem B5824061 : Blo 1725063 5824061 := bstep (se 3 (by rfl) ⟨1092011, by rfl⟩ : syracuseStep 5824061 = 2184023) B2184023
theorem B2588279 : Blo 1725063 2588279 := bstep (se 1 (by rfl) ⟨1941209, by rfl⟩ : syracuseStep 2588279 = 3882419) B3882419
theorem B2588303 : Blo 1725063 2588303 := bstep (se 1 (by rfl) ⟨1941227, by rfl⟩ : syracuseStep 2588303 = 3882455) B3882455
theorem B2588345 : Blo 1725063 2588345 := bstep (se 2 (by rfl) ⟨970629, by rfl⟩ : syracuseStep 2588345 = 1941259) B1941259
theorem B19930853 : Blo 1725063 19930853 := bstep (se 4 (by rfl) ⟨1868517, by rfl⟩ : syracuseStep 19930853 = 3737035) B3737035
theorem B6553345 : Blo 1725063 6553345 := bstep (se 2 (by rfl) ⟨2457504, by rfl⟩ : syracuseStep 6553345 = 4915009) B4915009
theorem B84188929 : Blo 1725063 84188929 := bstep (se 2 (by rfl) ⟨31570848, by rfl⟩ : syracuseStep 84188929 = 63141697) B63141697
theorem B2588423 : Blo 1725063 2588423 := bstep (se 1 (by rfl) ⟨1941317, by rfl⟩ : syracuseStep 2588423 = 3882635) B3882635
theorem B4144907 : Blo 1725063 4144907 := bstep (se 1 (by rfl) ⟨3108680, by rfl⟩ : syracuseStep 4144907 = 6217361) B6217361
theorem B6217505 : Blo 1725063 6217505 := bstep (se 2 (by rfl) ⟨2331564, by rfl⟩ : syracuseStep 6217505 = 4663129) B4663129
theorem B2588459 : Blo 1725063 2588459 := bstep (se 1 (by rfl) ⟨1941344, by rfl⟩ : syracuseStep 2588459 = 3882689) B3882689
theorem B15957809 : Blo 1725063 15957809 := bstep (se 2 (by rfl) ⟨5984178, by rfl⟩ : syracuseStep 15957809 = 11968357) B11968357
theorem B2588489 : Blo 1725063 2588489 := bstep (se 2 (by rfl) ⟨970683, by rfl⟩ : syracuseStep 2588489 = 1941367) B1941367
theorem B16580467 : Blo 1725063 16580467 := bstep (se 1 (by rfl) ⟨12435350, by rfl⟩ : syracuseStep 16580467 = 24870701) B24870701
theorem B3882887 : Blo 1725063 3882887 := bstep (se 1 (by rfl) ⟨2912165, by rfl⟩ : syracuseStep 3882887 = 5824331) B5824331
theorem B2588603 : Blo 1725063 2588603 := bstep (se 1 (by rfl) ⟨1941452, by rfl⟩ : syracuseStep 2588603 = 3882905) B3882905
theorem B2588663 : Blo 1725063 2588663 := bstep (se 1 (by rfl) ⟨1941497, by rfl⟩ : syracuseStep 2588663 = 3882995) B3882995
theorem B8740871 : Blo 1725063 8740871 := bstep (se 1 (by rfl) ⟨6555653, by rfl⟩ : syracuseStep 8740871 = 13111307) B13111307
theorem B2588681 : Blo 1725063 2588681 := bstep (se 2 (by rfl) ⟨970755, by rfl⟩ : syracuseStep 2588681 = 1941511) B1941511
theorem B6553619 : Blo 1725063 6553619 := bstep (se 1 (by rfl) ⟨4915214, by rfl⟩ : syracuseStep 6553619 = 9830429) B9830429
theorem B2588711 : Blo 1725063 2588711 := bstep (se 1 (by rfl) ⟨1941533, by rfl⟩ : syracuseStep 2588711 = 3883067) B3883067
theorem B1941583 : Blo 1725063 1941583 := bstep (se 1 (by rfl) ⟨1456187, by rfl⟩ : syracuseStep 1941583 = 2912375) B2912375
theorem B2588795 : Blo 1725063 2588795 := bstep (se 1 (by rfl) ⟨1941596, by rfl⟩ : syracuseStep 2588795 = 3883193) B3883193
theorem B22126769 : Blo 1725063 22126769 := bstep (se 2 (by rfl) ⟨8297538, by rfl⟩ : syracuseStep 22126769 = 16595077) B16595077
theorem B2588921 : Blo 1725063 2588921 := bstep (se 2 (by rfl) ⟨970845, by rfl⟩ : syracuseStep 2588921 = 1941691) B1941691
theorem B2589023 : Blo 1725063 2589023 := bstep (se 1 (by rfl) ⟨1941767, by rfl⟩ : syracuseStep 2589023 = 3883535) B3883535
theorem B2589035 : Blo 1725063 2589035 := bstep (se 1 (by rfl) ⟨1941776, by rfl⟩ : syracuseStep 2589035 = 3883553) B3883553
theorem B44835277 : Blo 1725063 44835277 := bstep (se 3 (by rfl) ⟨8406614, by rfl⟩ : syracuseStep 44835277 = 16813229) B16813229
theorem B4366811 : Blo 1725063 4366811 := bstep (se 1 (by rfl) ⟨3275108, by rfl⟩ : syracuseStep 4366811 = 6550217) B6550217
theorem B1941979 : Blo 1725063 1941979 := bstep (se 1 (by rfl) ⟨1456484, by rfl⟩ : syracuseStep 1941979 = 2912969) B2912969
theorem B8741357 : Blo 1725063 8741357 := bstep (se 3 (by rfl) ⟨1639004, by rfl⟩ : syracuseStep 8741357 = 3278009) B3278009
theorem B5825033 : Blo 1725063 5825033 := bstep (se 2 (by rfl) ⟨2184387, by rfl⟩ : syracuseStep 5825033 = 4368775) B4368775
theorem B14746121 : Blo 1725063 14746121 := bstep (se 2 (by rfl) ⟨5529795, by rfl⟩ : syracuseStep 14746121 = 11059591) B11059591
theorem B8290849 : Blo 1725063 8290849 := bstep (se 2 (by rfl) ⟨3109068, by rfl⟩ : syracuseStep 8290849 = 6218137) B6218137
theorem B2589263 : Blo 1725063 2589263 := bstep (se 1 (by rfl) ⟨1941947, by rfl⟩ : syracuseStep 2589263 = 3883895) B3883895
theorem B18653813 : Blo 1725063 18653813 := bstep (se 5 (by rfl) ⟨874397, by rfl⟩ : syracuseStep 18653813 = 1748795) B1748795
theorem B3883643 : Blo 1725063 3883643 := bstep (se 1 (by rfl) ⟨2912732, by rfl⟩ : syracuseStep 3883643 = 5825465) B5825465
theorem B6644359 : Blo 1725063 6644359 := bstep (se 1 (by rfl) ⟨4983269, by rfl⟩ : syracuseStep 6644359 = 9966539) B9966539
theorem B2589383 : Blo 1725063 2589383 := bstep (se 1 (by rfl) ⟨1942037, by rfl⟩ : syracuseStep 2589383 = 3884075) B3884075
theorem B3277523 : Blo 1725063 3277523 := bstep (se 1 (by rfl) ⟨2458142, by rfl⟩ : syracuseStep 3277523 = 4916285) B4916285
theorem B3883769 : Blo 1725063 3883769 := bstep (se 2 (by rfl) ⟨1456413, by rfl⟩ : syracuseStep 3883769 = 2912827) B2912827
theorem B5530463 : Blo 1725063 5530463 := bstep (se 1 (by rfl) ⟨4147847, by rfl⟩ : syracuseStep 5530463 = 8295695) B8295695
theorem B2589545 : Blo 1725063 2589545 := bstep (se 2 (by rfl) ⟨971079, by rfl⟩ : syracuseStep 2589545 = 1942159) B1942159
theorem B3990379 : Blo 1725063 3990379 := bstep (se 1 (by rfl) ⟨2992784, by rfl⟩ : syracuseStep 3990379 = 5985569) B5985569
theorem B3687275 : Blo 1725063 3687275 := bstep (se 1 (by rfl) ⟨2765456, by rfl⟩ : syracuseStep 3687275 = 5530913) B5530913
theorem B3277675 : Blo 1725063 3277675 := bstep (se 1 (by rfl) ⟨2458256, by rfl⟩ : syracuseStep 3277675 = 4916513) B4916513
theorem B1942447 : Blo 1725063 1942447 := bstep (se 1 (by rfl) ⟨1456835, by rfl⟩ : syracuseStep 1942447 = 2913671) B2913671
theorem B2589623 : Blo 1725063 2589623 := bstep (se 1 (by rfl) ⟨1942217, by rfl⟩ : syracuseStep 2589623 = 3884435) B3884435
theorem B2589659 : Blo 1725063 2589659 := bstep (se 1 (by rfl) ⟨1942244, by rfl⟩ : syracuseStep 2589659 = 3884489) B3884489
theorem B3884039 : Blo 1725063 3884039 := bstep (se 1 (by rfl) ⟨2913029, by rfl⟩ : syracuseStep 3884039 = 5826059) B5826059
theorem B5530643 : Blo 1725063 5530643 := bstep (se 1 (by rfl) ⟨4147982, by rfl⟩ : syracuseStep 5530643 = 8295965) B8295965
theorem B3884111 : Blo 1725063 3884111 := bstep (se 1 (by rfl) ⟨2913083, by rfl⟩ : syracuseStep 3884111 = 5826167) B5826167
theorem B3277903 : Blo 1725063 3277903 := bstep (se 1 (by rfl) ⟨2458427, by rfl⟩ : syracuseStep 3277903 = 4916855) B4916855
theorem B4146347 : Blo 1725063 4146347 := bstep (se 1 (by rfl) ⟨3109760, by rfl⟩ : syracuseStep 4146347 = 6219521) B6219521
theorem B26576075 : Blo 1725063 26576075 := bstep (se 1 (by rfl) ⟨19932056, by rfl⟩ : syracuseStep 26576075 = 39864113) B39864113
theorem B28755161 : Blo 1725063 28755161 := bstep (se 2 (by rfl) ⟨10783185, by rfl⟩ : syracuseStep 28755161 = 21566371) B21566371
theorem B8742167 : Blo 1725063 8742167 := bstep (se 1 (by rfl) ⟨6556625, by rfl⟩ : syracuseStep 8742167 = 13113251) B13113251
theorem B1942879 : Blo 1725063 1942879 := bstep (se 1 (by rfl) ⟨1457159, by rfl⟩ : syracuseStep 1942879 = 2914319) B2914319
theorem B5825897 : Blo 1725063 5825897 := bstep (se 2 (by rfl) ⟨2184711, by rfl⟩ : syracuseStep 5825897 = 4369423) B4369423
theorem B2590127 : Blo 1725063 2590127 := bstep (se 1 (by rfl) ⟨1942595, by rfl⟩ : syracuseStep 2590127 = 3885191) B3885191
theorem B3884507 : Blo 1725063 3884507 := bstep (se 1 (by rfl) ⟨2913380, by rfl⟩ : syracuseStep 3884507 = 5826761) B5826761
theorem B2590217 : Blo 1725063 2590217 := bstep (se 2 (by rfl) ⟨971331, by rfl⟩ : syracuseStep 2590217 = 1942663) B1942663
theorem B2590247 : Blo 1725063 2590247 := bstep (se 1 (by rfl) ⟨1942685, by rfl⟩ : syracuseStep 2590247 = 3885371) B3885371
theorem B2590331 : Blo 1725063 2590331 := bstep (se 1 (by rfl) ⟨1942748, by rfl⟩ : syracuseStep 2590331 = 3885497) B3885497
theorem B6555275 : Blo 1725063 6555275 := bstep (se 1 (by rfl) ⟨4916456, by rfl⟩ : syracuseStep 6555275 = 9832913) B9832913
theorem B2590457 : Blo 1725063 2590457 := bstep (se 2 (by rfl) ⟨971421, by rfl⟩ : syracuseStep 2590457 = 1942843) B1942843
theorem B306644831 : Blo 1725063 306644831 := bstep (se 1 (by rfl) ⟨229983623, by rfl⟩ : syracuseStep 306644831 = 459967247) B459967247
theorem B2590559 : Blo 1725063 2590559 := bstep (se 1 (by rfl) ⟨1942919, by rfl⟩ : syracuseStep 2590559 = 3885839) B3885839
theorem B2590571 : Blo 1725063 2590571 := bstep (se 1 (by rfl) ⟨1942928, by rfl⟩ : syracuseStep 2590571 = 3885857) B3885857
theorem B7374701 : Blo 1725063 7374701 := bstep (se 3 (by rfl) ⟨1382756, by rfl⟩ : syracuseStep 7374701 = 2765513) B2765513
theorem B4368289 : Blo 1725063 4368289 := bstep (se 2 (by rfl) ⟨1638108, by rfl⟩ : syracuseStep 4368289 = 3276217) B3276217
theorem B3884975 : Blo 1725063 3884975 := bstep (se 1 (by rfl) ⟨2913731, by rfl⟩ : syracuseStep 3884975 = 5827463) B5827463
theorem B5826491 : Blo 1725063 5826491 := bstep (se 1 (by rfl) ⟨4369868, by rfl⟩ : syracuseStep 5826491 = 8739737) B8739737
theorem B13109363 : Blo 1725063 13109363 := bstep (se 1 (by rfl) ⟨9832022, by rfl⟩ : syracuseStep 13109363 = 19664045) B19664045
theorem B8734877 : Blo 1725063 8734877 := bstep (se 3 (by rfl) ⟨1637789, by rfl⟩ : syracuseStep 8734877 = 3275579) B3275579
theorem B3885227 : Blo 1725063 3885227 := bstep (se 1 (by rfl) ⟨2913920, by rfl⟩ : syracuseStep 3885227 = 5827841) B5827841
theorem B44247383 : Blo 1725063 44247383 := bstep (se 1 (by rfl) ⟨33185537, by rfl⟩ : syracuseStep 44247383 = 66371075) B66371075
theorem B12446081 : Blo 1725063 12446081 := bstep (se 2 (by rfl) ⟨4667280, by rfl⟩ : syracuseStep 12446081 = 9334561) B9334561
theorem B17951129 : Blo 1725063 17951129 := bstep (se 2 (by rfl) ⟨6731673, by rfl⟩ : syracuseStep 17951129 = 13463347) B13463347
theorem B2763271 : Blo 1725063 2763271 := bstep (se 1 (by rfl) ⟨2072453, by rfl⟩ : syracuseStep 2763271 = 4144907) B4144907
theorem B16583201 : Blo 1725063 16583201 := bstep (se 2 (by rfl) ⟨6218700, by rfl⟩ : syracuseStep 16583201 = 12437401) B12437401
theorem B2214479 : Blo 1725063 2214479 := bstep (se 1 (by rfl) ⟨1660859, by rfl⟩ : syracuseStep 2214479 = 3321719) B3321719
theorem B2763463 : Blo 1725063 2763463 := bstep (se 1 (by rfl) ⟨2072597, by rfl⟩ : syracuseStep 2763463 = 4145195) B4145195
theorem B3885767 : Blo 1725063 3885767 := bstep (se 1 (by rfl) ⟨2914325, by rfl⟩ : syracuseStep 3885767 = 5828651) B5828651
theorem B4917971 : Blo 1725063 4917971 := bstep (se 1 (by rfl) ⟨3688478, by rfl⟩ : syracuseStep 4917971 = 7376957) B7376957
theorem B9825097 : Blo 1725063 9825097 := bstep (se 2 (by rfl) ⟨3684411, by rfl⟩ : syracuseStep 9825097 = 7368823) B7368823
theorem B6556535 : Blo 1725063 6556535 := bstep (se 1 (by rfl) ⟨4917401, by rfl⟩ : syracuseStep 6556535 = 9834803) B9834803
theorem B2911241 : Blo 1725063 2911241 := bstep (se 2 (by rfl) ⟨1091715, by rfl⟩ : syracuseStep 2911241 = 2183431) B2183431
theorem B4262969 : Blo 1725063 4262969 := bstep (se 2 (by rfl) ⟨1598613, by rfl⟩ : syracuseStep 4262969 = 3197227) B3197227
theorem B2763899 : Blo 1725063 2763899 := bstep (se 1 (by rfl) ⟨2072924, by rfl⟩ : syracuseStep 2763899 = 4145849) B4145849
theorem B2911403 : Blo 1725063 2911403 := bstep (se 1 (by rfl) ⟨2183552, by rfl⟩ : syracuseStep 2911403 = 4367105) B4367105
theorem B5393579 : Blo 1725063 5393579 := bstep (se 1 (by rfl) ⟨4045184, by rfl⟩ : syracuseStep 5393579 = 8090369) B8090369
theorem B113560865 : Blo 1725063 113560865 := bstep (se 2 (by rfl) ⟨42585324, by rfl⟩ : syracuseStep 113560865 = 85170649) B85170649
theorem B11062565 : Blo 1725063 11062565 := bstep (se 4 (by rfl) ⟨1037115, by rfl⟩ : syracuseStep 11062565 = 2074231) B2074231
theorem B4984193 : Blo 1725063 4984193 := bstep (se 2 (by rfl) ⟨1869072, by rfl⟩ : syracuseStep 4984193 = 3738145) B3738145
theorem B8736173 : Blo 1725063 8736173 := bstep (se 3 (by rfl) ⟨1638032, by rfl⟩ : syracuseStep 8736173 = 3276065) B3276065
theorem B2911801 : Blo 1725063 2911801 := bstep (se 2 (by rfl) ⟨1091925, by rfl⟩ : syracuseStep 2911801 = 2183851) B2183851
theorem B5828219 : Blo 1725063 5828219 := bstep (se 1 (by rfl) ⟨4371164, by rfl⟩ : syracuseStep 5828219 = 8742329) B8742329
theorem B2911943 : Blo 1725063 2911943 := bstep (se 1 (by rfl) ⟨2183957, by rfl⟩ : syracuseStep 2911943 = 4367915) B4367915
theorem B5828381 : Blo 1725063 5828381 := bstep (se 3 (by rfl) ⟨1092821, by rfl⟩ : syracuseStep 5828381 = 2185643) B2185643
theorem B7376683 : Blo 1725063 7376683 := bstep (se 1 (by rfl) ⟨5532512, by rfl⟩ : syracuseStep 7376683 = 11065025) B11065025
theorem B2912105 : Blo 1725063 2912105 := bstep (se 2 (by rfl) ⟨1092039, by rfl⟩ : syracuseStep 2912105 = 2184079) B2184079
theorem B7982957 : Blo 1725063 7982957 := bstep (se 3 (by rfl) ⟨1496804, by rfl⟩ : syracuseStep 7982957 = 2993609) B2993609
theorem B2764687 : Blo 1725063 2764687 := bstep (se 1 (by rfl) ⟨2073515, by rfl⟩ : syracuseStep 2764687 = 4147031) B4147031
theorem B14004301 : Blo 1725063 14004301 := bstep (se 3 (by rfl) ⟨2625806, by rfl⟩ : syracuseStep 14004301 = 5251613) B5251613
theorem B2912503 : Blo 1725063 2912503 := bstep (se 1 (by rfl) ⟨2184377, by rfl⟩ : syracuseStep 2912503 = 4368755) B4368755
theorem B4370831 : Blo 1725063 4370831 := bstep (se 1 (by rfl) ⟨3278123, by rfl⟩ : syracuseStep 4370831 = 6556247) B6556247
theorem B2912699 : Blo 1725063 2912699 := bstep (se 1 (by rfl) ⟨2184524, by rfl⟩ : syracuseStep 2912699 = 4369049) B4369049
theorem B5902811 : Blo 1725063 5902811 := bstep (se 1 (by rfl) ⟨4427108, by rfl⟩ : syracuseStep 5902811 = 8854217) B8854217
theorem B2912807 : Blo 1725063 2912807 := bstep (se 1 (by rfl) ⟨2184605, by rfl⟩ : syracuseStep 2912807 = 4369211) B4369211
theorem B1725103 : Blo 1725063 1725103 := bstep (se 1 (by rfl) ⟨1293827, by rfl⟩ : syracuseStep 1725103 = 2587655) B2587655
theorem B6222521 : Blo 1725063 6222521 := bstep (se 2 (by rfl) ⟨2333445, by rfl⟩ : syracuseStep 6222521 = 4666891) B4666891
theorem B1725127 : Blo 1725063 1725127 := bstep (se 1 (by rfl) ⟨1293845, by rfl⟩ : syracuseStep 1725127 = 2587691) B2587691
theorem B4371155 : Blo 1725063 4371155 := bstep (se 1 (by rfl) ⟨3278366, by rfl⟩ : syracuseStep 4371155 = 6556733) B6556733
theorem B1725147 : Blo 1725063 1725147 := bstep (se 1 (by rfl) ⟨1293860, by rfl⟩ : syracuseStep 1725147 = 2587721) B2587721
theorem B1725223 : Blo 1725063 1725223 := bstep (se 1 (by rfl) ⟨1293917, by rfl⟩ : syracuseStep 1725223 = 2587835) B2587835
theorem B2913097 : Blo 1725063 2913097 := bstep (se 2 (by rfl) ⟨1092411, by rfl⟩ : syracuseStep 2913097 = 2184823) B2184823
theorem B6222665 : Blo 1725063 6222665 := bstep (se 2 (by rfl) ⟨2333499, by rfl⟩ : syracuseStep 6222665 = 4666999) B4666999
theorem B1725263 : Blo 1725063 1725263 := bstep (se 1 (by rfl) ⟨1293947, by rfl⟩ : syracuseStep 1725263 = 2587895) B2587895
theorem B1725279 : Blo 1725063 1725279 := bstep (se 1 (by rfl) ⟨1293959, by rfl⟩ : syracuseStep 1725279 = 2587919) B2587919
theorem B2331499 : Blo 1725063 2331499 := bstep (se 1 (by rfl) ⟨1748624, by rfl⟩ : syracuseStep 2331499 = 3497249) B3497249
theorem B2913131 : Blo 1725063 2913131 := bstep (se 1 (by rfl) ⟨2184848, by rfl⟩ : syracuseStep 2913131 = 4369697) B4369697
theorem B90887027 : Blo 1725063 90887027 := bstep (se 1 (by rfl) ⟨68165270, by rfl⟩ : syracuseStep 90887027 = 136330541) B136330541
theorem B1725307 : Blo 1725063 1725307 := bstep (se 1 (by rfl) ⟨1293980, by rfl⟩ : syracuseStep 1725307 = 2587961) B2587961
theorem B13104017 : Blo 1725063 13104017 := bstep (se 2 (by rfl) ⟨4914006, by rfl⟩ : syracuseStep 13104017 = 9828013) B9828013
theorem B31503257 : Blo 1725063 31503257 := bstep (se 2 (by rfl) ⟨11813721, by rfl⟩ : syracuseStep 31503257 = 23627443) B23627443
theorem B1725359 : Blo 1725063 1725359 := bstep (se 1 (by rfl) ⟨1294019, by rfl⟩ : syracuseStep 1725359 = 2588039) B2588039
theorem B21582767 : Blo 1725063 21582767 := bstep (se 1 (by rfl) ⟨16187075, by rfl⟩ : syracuseStep 21582767 = 32374151) B32374151
theorem B1725383 : Blo 1725063 1725383 := bstep (se 1 (by rfl) ⟨1294037, by rfl⟩ : syracuseStep 1725383 = 2588075) B2588075
theorem B1725403 : Blo 1725063 1725403 := bstep (se 1 (by rfl) ⟨1294052, by rfl⟩ : syracuseStep 1725403 = 2588105) B2588105
theorem B8737793 : Blo 1725063 8737793 := bstep (se 2 (by rfl) ⟨3276672, by rfl⟩ : syracuseStep 8737793 = 6553345) B6553345
theorem B112251905 : Blo 1725063 112251905 := bstep (se 2 (by rfl) ⟨42094464, by rfl⟩ : syracuseStep 112251905 = 84188929) B84188929
theorem B1725479 : Blo 1725063 1725479 := bstep (se 1 (by rfl) ⟨1294109, by rfl⟩ : syracuseStep 1725479 = 2588219) B2588219
theorem B3322919 : Blo 1725063 3322919 := bstep (se 1 (by rfl) ⟨2492189, by rfl⟩ : syracuseStep 3322919 = 4984379) B4984379
theorem B1725519 : Blo 1725063 1725519 := bstep (se 1 (by rfl) ⟨1294139, by rfl⟩ : syracuseStep 1725519 = 2588279) B2588279
theorem B1725535 : Blo 1725063 1725535 := bstep (se 1 (by rfl) ⟨1294151, by rfl⟩ : syracuseStep 1725535 = 2588303) B2588303
theorem B1725563 : Blo 1725063 1725563 := bstep (se 1 (by rfl) ⟨1294172, by rfl⟩ : syracuseStep 1725563 = 2588345) B2588345
theorem B22107289 : Blo 1725063 22107289 := bstep (se 2 (by rfl) ⟨8290233, by rfl⟩ : syracuseStep 22107289 = 16580467) B16580467
theorem B1725615 : Blo 1725063 1725615 := bstep (se 1 (by rfl) ⟨1294211, by rfl⟩ : syracuseStep 1725615 = 2588423) B2588423
theorem B1725639 : Blo 1725063 1725639 := bstep (se 1 (by rfl) ⟨1294229, by rfl⟩ : syracuseStep 1725639 = 2588459) B2588459
theorem B10638539 : Blo 1725063 10638539 := bstep (se 1 (by rfl) ⟨7978904, by rfl⟩ : syracuseStep 10638539 = 15957809) B15957809
theorem B1725659 : Blo 1725063 1725659 := bstep (se 1 (by rfl) ⟨1294244, by rfl⟩ : syracuseStep 1725659 = 2588489) B2588489
theorem B2913529 : Blo 1725063 2913529 := bstep (se 2 (by rfl) ⟨1092573, by rfl⟩ : syracuseStep 2913529 = 2185147) B2185147
theorem B1725735 : Blo 1725063 1725735 := bstep (se 1 (by rfl) ⟨1294301, by rfl⟩ : syracuseStep 1725735 = 2588603) B2588603
theorem B1725775 : Blo 1725063 1725775 := bstep (se 1 (by rfl) ⟨1294331, by rfl⟩ : syracuseStep 1725775 = 2588663) B2588663
theorem B1725791 : Blo 1725063 1725791 := bstep (se 1 (by rfl) ⟨1294343, by rfl⟩ : syracuseStep 1725791 = 2588687) B2588687
theorem B1725819 : Blo 1725063 1725819 := bstep (se 1 (by rfl) ⟨1294364, by rfl⟩ : syracuseStep 1725819 = 2588729) B2588729
theorem B13284773 : Blo 1725063 13284773 := bstep (se 4 (by rfl) ⟨1245447, by rfl⟩ : syracuseStep 13284773 = 2490895) B2490895
theorem B1725871 : Blo 1725063 1725871 := bstep (se 1 (by rfl) ⟨1294403, by rfl⟩ : syracuseStep 1725871 = 2588807) B2588807
theorem B1725895 : Blo 1725063 1725895 := bstep (se 1 (by rfl) ⟨1294421, by rfl⟩ : syracuseStep 1725895 = 2588843) B2588843
theorem B1725915 : Blo 1725063 1725915 := bstep (se 1 (by rfl) ⟨1294436, by rfl⟩ : syracuseStep 1725915 = 2588873) B2588873
theorem B22107653 : Blo 1725063 22107653 := bstep (se 4 (by rfl) ⟨2072592, by rfl⟩ : syracuseStep 22107653 = 4145185) B4145185
theorem B2913799 : Blo 1725063 2913799 := bstep (se 1 (by rfl) ⟨2185349, by rfl⟩ : syracuseStep 2913799 = 4370699) B4370699
theorem B1725991 : Blo 1725063 1725991 := bstep (se 1 (by rfl) ⟨1294493, by rfl⟩ : syracuseStep 1725991 = 2588987) B2588987
theorem B1726031 : Blo 1725063 1726031 := bstep (se 1 (by rfl) ⟨1294523, by rfl⟩ : syracuseStep 1726031 = 2589047) B2589047
theorem B1726047 : Blo 1725063 1726047 := bstep (se 1 (by rfl) ⟨1294535, by rfl⟩ : syracuseStep 1726047 = 2589071) B2589071
theorem B1726075 : Blo 1725063 1726075 := bstep (se 1 (by rfl) ⟨1294556, by rfl⟩ : syracuseStep 1726075 = 2589113) B2589113
theorem B12441235 : Blo 1725063 12441235 := bstep (se 1 (by rfl) ⟨9330926, by rfl⟩ : syracuseStep 12441235 = 18661853) B18661853
theorem B1726127 : Blo 1725063 1726127 := bstep (se 1 (by rfl) ⟨1294595, by rfl⟩ : syracuseStep 1726127 = 2589191) B2589191
theorem B1726151 : Blo 1725063 1726151 := bstep (se 1 (by rfl) ⟨1294613, by rfl⟩ : syracuseStep 1726151 = 2589227) B2589227
theorem B1726171 : Blo 1725063 1726171 := bstep (se 1 (by rfl) ⟨1294628, by rfl⟩ : syracuseStep 1726171 = 2589257) B2589257
theorem B1726247 : Blo 1725063 1726247 := bstep (se 1 (by rfl) ⟨1294685, by rfl⟩ : syracuseStep 1726247 = 2589371) B2589371
theorem B8738603 : Blo 1725063 8738603 := bstep (se 1 (by rfl) ⟨6553952, by rfl⟩ : syracuseStep 8738603 = 13107905) B13107905
theorem B1726287 : Blo 1725063 1726287 := bstep (se 1 (by rfl) ⟨1294715, by rfl⟩ : syracuseStep 1726287 = 2589431) B2589431
theorem B1726303 : Blo 1725063 1726303 := bstep (se 1 (by rfl) ⟨1294727, by rfl⟩ : syracuseStep 1726303 = 2589455) B2589455
theorem B1726331 : Blo 1725063 1726331 := bstep (se 1 (by rfl) ⟨1294748, by rfl⟩ : syracuseStep 1726331 = 2589497) B2589497
theorem B14743457 : Blo 1725063 14743457 := bstep (se 2 (by rfl) ⟨5528796, by rfl⟩ : syracuseStep 14743457 = 11057593) B11057593
theorem B1726383 : Blo 1725063 1726383 := bstep (se 1 (by rfl) ⟨1294787, by rfl⟩ : syracuseStep 1726383 = 2589575) B2589575
theorem B2914231 : Blo 1725063 2914231 := bstep (se 1 (by rfl) ⟨2185673, by rfl⟩ : syracuseStep 2914231 = 4371347) B4371347
theorem B1726407 : Blo 1725063 1726407 := bstep (se 1 (by rfl) ⟨1294805, by rfl⟩ : syracuseStep 1726407 = 2589611) B2589611
theorem B1726427 : Blo 1725063 1726427 := bstep (se 1 (by rfl) ⟨1294820, by rfl⟩ : syracuseStep 1726427 = 2589641) B2589641
theorem B1726503 : Blo 1725063 1726503 := bstep (se 1 (by rfl) ⟨1294877, by rfl⟩ : syracuseStep 1726503 = 2589755) B2589755
theorem B1726543 : Blo 1725063 1726543 := bstep (se 1 (by rfl) ⟨1294907, by rfl⟩ : syracuseStep 1726543 = 2589815) B2589815
theorem B1726559 : Blo 1725063 1726559 := bstep (se 1 (by rfl) ⟨1294919, by rfl⟩ : syracuseStep 1726559 = 2589839) B2589839
theorem B1726587 : Blo 1725063 1726587 := bstep (se 1 (by rfl) ⟨1294940, by rfl⟩ : syracuseStep 1726587 = 2589881) B2589881
theorem B6551705 : Blo 1725063 6551705 := bstep (se 2 (by rfl) ⟨2456889, by rfl⟩ : syracuseStep 6551705 = 4913779) B4913779
theorem B7370909 : Blo 1725063 7370909 := bstep (se 3 (by rfl) ⟨1382045, by rfl⟩ : syracuseStep 7370909 = 2764091) B2764091
theorem B1726639 : Blo 1725063 1726639 := bstep (se 1 (by rfl) ⟨1294979, by rfl⟩ : syracuseStep 1726639 = 2589959) B2589959
theorem B1726663 : Blo 1725063 1726663 := bstep (se 1 (by rfl) ⟨1294997, by rfl⟩ : syracuseStep 1726663 = 2589995) B2589995
theorem B1726683 : Blo 1725063 1726683 := bstep (se 1 (by rfl) ⟨1295012, by rfl⟩ : syracuseStep 1726683 = 2590025) B2590025
theorem B5822711 : Blo 1725063 5822711 := bstep (se 1 (by rfl) ⟨4367033, by rfl⟩ : syracuseStep 5822711 = 8734067) B8734067
theorem B1726759 : Blo 1725063 1726759 := bstep (se 1 (by rfl) ⟨1295069, by rfl⟩ : syracuseStep 1726759 = 2590139) B2590139
theorem B1726799 : Blo 1725063 1726799 := bstep (se 1 (by rfl) ⟨1295099, by rfl⟩ : syracuseStep 1726799 = 2590199) B2590199
theorem B1726815 : Blo 1725063 1726815 := bstep (se 1 (by rfl) ⟨1295111, by rfl⟩ : syracuseStep 1726815 = 2590223) B2590223
theorem B1726843 : Blo 1725063 1726843 := bstep (se 1 (by rfl) ⟨1295132, by rfl⟩ : syracuseStep 1726843 = 2590265) B2590265
theorem B4913551 : Blo 1725063 4913551 := bstep (se 1 (by rfl) ⟨3685163, by rfl⟩ : syracuseStep 4913551 = 7370327) B7370327
theorem B1726895 : Blo 1725063 1726895 := bstep (se 1 (by rfl) ⟨1295171, by rfl⟩ : syracuseStep 1726895 = 2590343) B2590343
theorem B1726919 : Blo 1725063 1726919 := bstep (se 1 (by rfl) ⟨1295189, by rfl⟩ : syracuseStep 1726919 = 2590379) B2590379
theorem B163748299 : Blo 1725063 163748299 := bstep (se 1 (by rfl) ⟨122811224, by rfl⟩ : syracuseStep 163748299 = 245622449) B245622449
theorem B1726939 : Blo 1725063 1726939 := bstep (se 1 (by rfl) ⟨1295204, by rfl⟩ : syracuseStep 1726939 = 2590409) B2590409
theorem B3152423 : Blo 1725063 3152423 := bstep (se 1 (by rfl) ⟨2364317, by rfl⟩ : syracuseStep 3152423 = 4728635) B4728635
theorem B1727015 : Blo 1725063 1727015 := bstep (se 1 (by rfl) ⟨1295261, by rfl⟩ : syracuseStep 1727015 = 2590523) B2590523
theorem B5823035 : Blo 1725063 5823035 := bstep (se 1 (by rfl) ⟨4367276, by rfl⟩ : syracuseStep 5823035 = 8734553) B8734553
theorem B1727055 : Blo 1725063 1727055 := bstep (se 1 (by rfl) ⟨1295291, by rfl⟩ : syracuseStep 1727055 = 2590583) B2590583
theorem B6552161 : Blo 1725063 6552161 := bstep (se 2 (by rfl) ⟨2457060, by rfl⟩ : syracuseStep 6552161 = 4914121) B4914121
theorem B5823305 : Blo 1725063 5823305 := bstep (se 2 (by rfl) ⟨2183739, by rfl⟩ : syracuseStep 5823305 = 4367479) B4367479
theorem B7371593 : Blo 1725063 7371593 := bstep (se 2 (by rfl) ⟨2764347, by rfl⟩ : syracuseStep 7371593 = 5528695) B5528695
theorem B16579511 : Blo 1725063 16579511 := bstep (se 1 (by rfl) ⟨12434633, by rfl⟩ : syracuseStep 16579511 = 24869267) B24869267
theorem B3881915 : Blo 1725063 3881915 := bstep (se 1 (by rfl) ⟨2911436, by rfl⟩ : syracuseStep 3881915 = 5822873) B5822873
theorem B3275815 : Blo 1725063 3275815 := bstep (se 1 (by rfl) ⟨2456861, by rfl⟩ : syracuseStep 3275815 = 4913723) B4913723
theorem B3882041 : Blo 1725063 3882041 := bstep (se 2 (by rfl) ⟨1455765, by rfl⟩ : syracuseStep 3882041 = 2911531) B2911531
theorem B2587727 : Blo 1725063 2587727 := bstep (se 1 (by rfl) ⟨1940795, by rfl⟩ : syracuseStep 2587727 = 3881591) B3881591
theorem B47225987 : Blo 1725063 47225987 := bstep (se 1 (by rfl) ⟨35419490, by rfl⟩ : syracuseStep 47225987 = 70838981) B70838981
theorem B2587847 : Blo 1725063 2587847 := bstep (se 1 (by rfl) ⟨1940885, by rfl⟩ : syracuseStep 2587847 = 3881771) B3881771
theorem B5602571 : Blo 1725063 5602571 := bstep (se 1 (by rfl) ⟨4201928, by rfl⟩ : syracuseStep 5602571 = 8403857) B8403857
theorem B13106447 : Blo 1725063 13106447 := bstep (se 1 (by rfl) ⟨9829835, by rfl⟩ : syracuseStep 13106447 = 19659671) B19659671
theorem B2588009 : Blo 1725063 2588009 := bstep (se 2 (by rfl) ⟨970503, by rfl⟩ : syracuseStep 2588009 = 1941007) B1941007
theorem B3882383 : Blo 1725063 3882383 := bstep (se 1 (by rfl) ⟨2911787, by rfl⟩ : syracuseStep 3882383 = 5823575) B5823575
theorem B2588087 : Blo 1725063 2588087 := bstep (se 1 (by rfl) ⟨1941065, by rfl⟩ : syracuseStep 2588087 = 3882131) B3882131
theorem B2588123 : Blo 1725063 2588123 := bstep (se 1 (by rfl) ⟨1941092, by rfl⟩ : syracuseStep 2588123 = 3882185) B3882185
theorem B1941115 : Blo 1725063 1941115 := bstep (se 1 (by rfl) ⟨1455836, by rfl⟩ : syracuseStep 1941115 = 2911673) B2911673
theorem B4914827 : Blo 1725063 4914827 := bstep (se 1 (by rfl) ⟨3686120, by rfl⟩ : syracuseStep 4914827 = 7372241) B7372241
theorem B3686087 : Blo 1725063 3686087 := bstep (se 1 (by rfl) ⟨2764565, by rfl⟩ : syracuseStep 3686087 = 5529131) B5529131
theorem B3882707 : Blo 1725063 3882707 := bstep (se 1 (by rfl) ⟨2912030, by rfl⟩ : syracuseStep 3882707 = 5824061) B5824061
theorem B13287235 : Blo 1725063 13287235 := bstep (se 1 (by rfl) ⟨9965426, by rfl⟩ : syracuseStep 13287235 = 19930853) B19930853
theorem B6643529 : Blo 1725063 6643529 := bstep (se 2 (by rfl) ⟨2491323, by rfl⟩ : syracuseStep 6643529 = 4982647) B4982647
theorem B4145003 : Blo 1725063 4145003 := bstep (se 1 (by rfl) ⟨3108752, by rfl⟩ : syracuseStep 4145003 = 6217505) B6217505
theorem B2588591 : Blo 1725063 2588591 := bstep (se 1 (by rfl) ⟨1941443, by rfl⟩ : syracuseStep 2588591 = 3882887) B3882887
theorem B5824439 : Blo 1725063 5824439 := bstep (se 1 (by rfl) ⟨4368329, by rfl⟩ : syracuseStep 5824439 = 8736659) B8736659
theorem B2588777 : Blo 1725063 2588777 := bstep (se 2 (by rfl) ⟨970791, by rfl⟩ : syracuseStep 2588777 = 1941583) B1941583
theorem B1941799 : Blo 1725063 1941799 := bstep (se 1 (by rfl) ⟨1456349, by rfl⟩ : syracuseStep 1941799 = 2912699) B2912699
theorem B3883337 : Blo 1725063 3883337 := bstep (se 2 (by rfl) ⟨1456251, by rfl⟩ : syracuseStep 3883337 = 2912503) B2912503
theorem B3883355 : Blo 1725063 3883355 := bstep (se 1 (by rfl) ⟨2912516, by rfl⟩ : syracuseStep 3883355 = 5825033) B5825033
theorem B9830747 : Blo 1725063 9830747 := bstep (se 1 (by rfl) ⟨7373060, by rfl⟩ : syracuseStep 9830747 = 14746121) B14746121
theorem B1941871 : Blo 1725063 1941871 := bstep (se 1 (by rfl) ⟨1456403, by rfl⟩ : syracuseStep 1941871 = 2912807) B2912807
theorem B12435875 : Blo 1725063 12435875 := bstep (se 1 (by rfl) ⟨9326906, by rfl⟩ : syracuseStep 12435875 = 18653813) B18653813
theorem B2589095 : Blo 1725063 2589095 := bstep (se 1 (by rfl) ⟨1941821, by rfl⟩ : syracuseStep 2589095 = 3883643) B3883643
theorem B2589179 : Blo 1725063 2589179 := bstep (se 1 (by rfl) ⟨1941884, by rfl⟩ : syracuseStep 2589179 = 3883769) B3883769
theorem B3686975 : Blo 1725063 3686975 := bstep (se 1 (by rfl) ⟨2765231, by rfl⟩ : syracuseStep 3686975 = 5530463) B5530463
theorem B1942087 : Blo 1725063 1942087 := bstep (se 1 (by rfl) ⟨1456565, by rfl⟩ : syracuseStep 1942087 = 2913131) B2913131
theorem B2458183 : Blo 1725063 2458183 := bstep (se 1 (by rfl) ⟨1843637, by rfl⟩ : syracuseStep 2458183 = 3687275) B3687275
theorem B2589305 : Blo 1725063 2589305 := bstep (se 2 (by rfl) ⟨970989, by rfl⟩ : syracuseStep 2589305 = 1941979) B1941979
theorem B5825195 : Blo 1725063 5825195 := bstep (se 1 (by rfl) ⟨4368896, by rfl⟩ : syracuseStep 5825195 = 8737793) B8737793
theorem B74834603 : Blo 1725063 74834603 := bstep (se 1 (by rfl) ⟨56125952, by rfl⟩ : syracuseStep 74834603 = 112251905) B112251905
theorem B2589359 : Blo 1725063 2589359 := bstep (se 1 (by rfl) ⟨1942019, by rfl⟩ : syracuseStep 2589359 = 3884039) B3884039
theorem B3687095 : Blo 1725063 3687095 := bstep (se 1 (by rfl) ⟨2765321, by rfl⟩ : syracuseStep 3687095 = 5530643) B5530643
theorem B2589407 : Blo 1725063 2589407 := bstep (se 1 (by rfl) ⟨1942055, by rfl⟩ : syracuseStep 2589407 = 3884111) B3884111
theorem B19170107 : Blo 1725063 19170107 := bstep (se 1 (by rfl) ⟨14377580, by rfl⟩ : syracuseStep 19170107 = 28755161) B28755161
theorem B3883931 : Blo 1725063 3883931 := bstep (se 1 (by rfl) ⟨2912948, by rfl⟩ : syracuseStep 3883931 = 5825897) B5825897
theorem B8856515 : Blo 1725063 8856515 := bstep (se 1 (by rfl) ⟨6642386, by rfl⟩ : syracuseStep 8856515 = 13284773) B13284773
theorem B2589671 : Blo 1725063 2589671 := bstep (se 1 (by rfl) ⟨1942253, by rfl⟩ : syracuseStep 2589671 = 3884507) B3884507
theorem B14738435 : Blo 1725063 14738435 := bstep (se 1 (by rfl) ⟨11053826, by rfl⟩ : syracuseStep 14738435 = 22107653) B22107653
theorem B13100129 : Blo 1725063 13100129 := bstep (se 2 (by rfl) ⟨4912548, by rfl⟩ : syracuseStep 13100129 = 9825097) B9825097
theorem B3884129 : Blo 1725063 3884129 := bstep (se 2 (by rfl) ⟨1456548, by rfl⟩ : syracuseStep 3884129 = 2913097) B2913097
theorem B5825735 : Blo 1725063 5825735 := bstep (se 1 (by rfl) ⟨4369301, by rfl⟩ : syracuseStep 5825735 = 8738603) B8738603
theorem B2589929 : Blo 1725063 2589929 := bstep (se 2 (by rfl) ⟨971223, by rfl⟩ : syracuseStep 2589929 = 1942447) B1942447
theorem B4916467 : Blo 1725063 4916467 := bstep (se 1 (by rfl) ⟨3687350, by rfl⟩ : syracuseStep 4916467 = 7374701) B7374701
theorem B2589983 : Blo 1725063 2589983 := bstep (se 1 (by rfl) ⟨1942487, by rfl⟩ : syracuseStep 2589983 = 3884975) B3884975
theorem B3884327 : Blo 1725063 3884327 := bstep (se 1 (by rfl) ⟨2913245, by rfl⟩ : syracuseStep 3884327 = 5826491) B5826491
theorem B4367753 : Blo 1725063 4367753 := bstep (se 2 (by rfl) ⟨1637907, by rfl⟩ : syracuseStep 4367753 = 3275815) B3275815
theorem B4367803 : Blo 1725063 4367803 := bstep (se 1 (by rfl) ⟨3275852, by rfl⟩ : syracuseStep 4367803 = 6551705) B6551705
theorem B8406461 : Blo 1725063 8406461 := bstep (se 3 (by rfl) ⟨1576211, by rfl⟩ : syracuseStep 8406461 = 3152423) B3152423
theorem B2590151 : Blo 1725063 2590151 := bstep (se 1 (by rfl) ⟨1942613, by rfl⟩ : syracuseStep 2590151 = 3885227) B3885227
theorem B29476385 : Blo 1725063 29476385 := bstep (se 2 (by rfl) ⟨11053644, by rfl⟩ : syracuseStep 29476385 = 22107289) B22107289
theorem B3884705 : Blo 1725063 3884705 := bstep (se 2 (by rfl) ⟨1456764, by rfl⟩ : syracuseStep 3884705 = 2913529) B2913529
theorem B4368107 : Blo 1725063 4368107 := bstep (se 1 (by rfl) ⟨3276080, by rfl⟩ : syracuseStep 4368107 = 6552161) B6552161
theorem B2590505 : Blo 1725063 2590505 := bstep (se 2 (by rfl) ⟨971439, by rfl⟩ : syracuseStep 2590505 = 1942879) B1942879
theorem B2590511 : Blo 1725063 2590511 := bstep (se 1 (by rfl) ⟨1942883, by rfl⟩ : syracuseStep 2590511 = 3885767) B3885767
theorem B3278647 : Blo 1725063 3278647 := bstep (se 1 (by rfl) ⟨2458985, by rfl⟩ : syracuseStep 3278647 = 4917971) B4917971
theorem B11053007 : Blo 1725063 11053007 := bstep (se 1 (by rfl) ⟨8289755, by rfl⟩ : syracuseStep 11053007 = 16579511) B16579511
theorem B3885065 : Blo 1725063 3885065 := bstep (se 2 (by rfl) ⟨1456899, by rfl⟩ : syracuseStep 3885065 = 2913799) B2913799
theorem B31483991 : Blo 1725063 31483991 := bstep (se 1 (by rfl) ⟨23612993, by rfl⟩ : syracuseStep 31483991 = 47225987) B47225987
theorem B7375043 : Blo 1725063 7375043 := bstep (se 1 (by rfl) ⟨5531282, by rfl⟩ : syracuseStep 7375043 = 11062565) B11062565
theorem B3885479 : Blo 1725063 3885479 := bstep (se 1 (by rfl) ⟨2914109, by rfl⟩ : syracuseStep 3885479 = 5828219) B5828219
theorem B3885587 : Blo 1725063 3885587 := bstep (se 1 (by rfl) ⟨2914190, by rfl⟩ : syracuseStep 3885587 = 5828381) B5828381
theorem B2763335 : Blo 1725063 2763335 := bstep (se 1 (by rfl) ⟨2072501, by rfl⟩ : syracuseStep 2763335 = 4145003) B4145003
theorem B3885641 : Blo 1725063 3885641 := bstep (se 2 (by rfl) ⟨1457115, by rfl⟩ : syracuseStep 3885641 = 2914231) B2914231
theorem B5827247 : Blo 1725063 5827247 := bstep (se 1 (by rfl) ⟨4370435, by rfl⟩ : syracuseStep 5827247 = 8740871) B8740871
theorem B4369079 : Blo 1725063 4369079 := bstep (se 1 (by rfl) ⟨3276809, by rfl⟩ : syracuseStep 4369079 = 6553619) B6553619
theorem B18672401 : Blo 1725063 18672401 := bstep (se 2 (by rfl) ⟨7002150, by rfl⟩ : syracuseStep 18672401 = 14004301) B14004301
theorem B2911207 : Blo 1725063 2911207 := bstep (se 1 (by rfl) ⟨2183405, by rfl⟩ : syracuseStep 2911207 = 4366811) B4366811
theorem B3935207 : Blo 1725063 3935207 := bstep (se 1 (by rfl) ⟨2951405, by rfl⟩ : syracuseStep 3935207 = 5902811) B5902811
theorem B5827571 : Blo 1725063 5827571 := bstep (se 1 (by rfl) ⟨4370678, by rfl⟩ : syracuseStep 5827571 = 8741357) B8741357
theorem B4148347 : Blo 1725063 4148347 := bstep (se 1 (by rfl) ⟨3111260, by rfl⟩ : syracuseStep 4148347 = 6222521) B6222521
theorem B4148443 : Blo 1725063 4148443 := bstep (se 1 (by rfl) ⟨3111332, by rfl⟩ : syracuseStep 4148443 = 6222665) B6222665
theorem B8736011 : Blo 1725063 8736011 := bstep (se 1 (by rfl) ⟨6552008, by rfl⟩ : syracuseStep 8736011 = 13104017) B13104017
theorem B59780369 : Blo 1725063 59780369 := bstep (se 2 (by rfl) ⟨22417638, by rfl⟩ : syracuseStep 59780369 = 44835277) B44835277
theorem B14388511 : Blo 1725063 14388511 := bstep (se 1 (by rfl) ⟨10791383, by rfl⟩ : syracuseStep 14388511 = 21582767) B21582767
theorem B2215279 : Blo 1725063 2215279 := bstep (se 1 (by rfl) ⟨1661459, by rfl⟩ : syracuseStep 2215279 = 3322919) B3322919
theorem B11054465 : Blo 1725063 11054465 := bstep (se 2 (by rfl) ⟨4145424, by rfl⟩ : syracuseStep 11054465 = 8290849) B8290849
theorem B8859145 : Blo 1725063 8859145 := bstep (se 2 (by rfl) ⟨3322179, by rfl⟩ : syracuseStep 8859145 = 6644359) B6644359
theorem B5828111 : Blo 1725063 5828111 := bstep (se 1 (by rfl) ⟨4371083, by rfl⟩ : syracuseStep 5828111 = 8742167) B8742167
theorem B4370183 : Blo 1725063 4370183 := bstep (se 1 (by rfl) ⟨3277637, by rfl⟩ : syracuseStep 4370183 = 6555275) B6555275
theorem B3108665 : Blo 1725063 3108665 := bstep (se 2 (by rfl) ⟨1165749, by rfl⟩ : syracuseStep 3108665 = 2331499) B2331499
theorem B5320505 : Blo 1725063 5320505 := bstep (se 2 (by rfl) ⟨1995189, by rfl⟩ : syracuseStep 5320505 = 3990379) B3990379
theorem B4370233 : Blo 1725063 4370233 := bstep (se 2 (by rfl) ⟨1638837, by rfl⟩ : syracuseStep 4370233 = 3277675) B3277675
theorem B4370537 : Blo 1725063 4370537 := bstep (se 2 (by rfl) ⟨1638951, by rfl⟩ : syracuseStep 4370537 = 3277903) B3277903
theorem B11055467 : Blo 1725063 11055467 := bstep (se 1 (by rfl) ⟨8291600, by rfl⟩ : syracuseStep 11055467 = 16583201) B16583201
theorem B4371023 : Blo 1725063 4371023 := bstep (se 1 (by rfl) ⟨3278267, by rfl⟩ : syracuseStep 4371023 = 6556535) B6556535
theorem B1725151 : Blo 1725063 1725151 := bstep (se 1 (by rfl) ⟨1293863, by rfl⟩ : syracuseStep 1725151 = 2587727) B2587727
theorem B1725231 : Blo 1725063 1725231 := bstep (se 1 (by rfl) ⟨1293923, by rfl⟩ : syracuseStep 1725231 = 2587847) B2587847
theorem B8737631 : Blo 1725063 8737631 := bstep (se 1 (by rfl) ⟨6553223, by rfl⟩ : syracuseStep 8737631 = 13106447) B13106447
theorem B75707243 : Blo 1725063 75707243 := bstep (se 1 (by rfl) ⟨56780432, by rfl⟩ : syracuseStep 75707243 = 113560865) B113560865
theorem B1725339 : Blo 1725063 1725339 := bstep (se 1 (by rfl) ⟨1294004, by rfl⟩ : syracuseStep 1725339 = 2588009) B2588009
theorem B3322795 : Blo 1725063 3322795 := bstep (se 1 (by rfl) ⟨2492096, by rfl⟩ : syracuseStep 3322795 = 4984193) B4984193
theorem B1725391 : Blo 1725063 1725391 := bstep (se 1 (by rfl) ⟨1294043, by rfl⟩ : syracuseStep 1725391 = 2588087) B2588087
theorem B242365405 : Blo 1725063 242365405 := bstep (se 3 (by rfl) ⟨45443513, by rfl⟩ : syracuseStep 242365405 = 90887027) B90887027
theorem B1725415 : Blo 1725063 1725415 := bstep (se 1 (by rfl) ⟨1294061, by rfl⟩ : syracuseStep 1725415 = 2588123) B2588123
theorem B9835577 : Blo 1725063 9835577 := bstep (se 2 (by rfl) ⟨3688341, by rfl⟩ : syracuseStep 9835577 = 7376683) B7376683
theorem B17716313 : Blo 1725063 17716313 := bstep (se 2 (by rfl) ⟨6643617, by rfl⟩ : syracuseStep 17716313 = 13287235) B13287235
theorem B4429019 : Blo 1725063 4429019 := bstep (se 1 (by rfl) ⟨3321764, by rfl⟩ : syracuseStep 4429019 = 6643529) B6643529
theorem B5321971 : Blo 1725063 5321971 := bstep (se 1 (by rfl) ⟨3991478, by rfl⟩ : syracuseStep 5321971 = 7982957) B7982957
theorem B1725727 : Blo 1725063 1725727 := bstep (se 1 (by rfl) ⟨1294295, by rfl⟩ : syracuseStep 1725727 = 2588591) B2588591
theorem B1725787 : Blo 1725063 1725787 := bstep (se 1 (by rfl) ⟨1294340, by rfl⟩ : syracuseStep 1725787 = 2588681) B2588681
theorem B1725807 : Blo 1725063 1725807 := bstep (se 1 (by rfl) ⟨1294355, by rfl⟩ : syracuseStep 1725807 = 2588711) B2588711
theorem B1725863 : Blo 1725063 1725863 := bstep (se 1 (by rfl) ⟨1294397, by rfl⟩ : syracuseStep 1725863 = 2588795) B2588795
theorem B14751179 : Blo 1725063 14751179 := bstep (se 1 (by rfl) ⟨11063384, by rfl⟩ : syracuseStep 14751179 = 22126769) B22126769
theorem B1725947 : Blo 1725063 1725947 := bstep (se 1 (by rfl) ⟨1294460, by rfl⟩ : syracuseStep 1725947 = 2588921) B2588921
theorem B1726015 : Blo 1725063 1726015 := bstep (se 1 (by rfl) ⟨1294511, by rfl⟩ : syracuseStep 1726015 = 2589023) B2589023
theorem B1726023 : Blo 1725063 1726023 := bstep (se 1 (by rfl) ⟨1294517, by rfl⟩ : syracuseStep 1726023 = 2589035) B2589035
theorem B2913887 : Blo 1725063 2913887 := bstep (se 1 (by rfl) ⟨2185415, by rfl⟩ : syracuseStep 2913887 = 4370831) B4370831
theorem B1726175 : Blo 1725063 1726175 := bstep (se 1 (by rfl) ⟨1294631, by rfl⟩ : syracuseStep 1726175 = 2589263) B2589263
theorem B11056925 : Blo 1725063 11056925 := bstep (se 3 (by rfl) ⟨2073173, by rfl⟩ : syracuseStep 11056925 = 4146347) B4146347
theorem B14382877 : Blo 1725063 14382877 := bstep (se 3 (by rfl) ⟨2696789, by rfl⟩ : syracuseStep 14382877 = 5393579) B5393579
theorem B1726255 : Blo 1725063 1726255 := bstep (se 1 (by rfl) ⟨1294691, by rfl⟩ : syracuseStep 1726255 = 2589383) B2589383
theorem B2914103 : Blo 1725063 2914103 := bstep (se 1 (by rfl) ⟨2185577, by rfl⟩ : syracuseStep 2914103 = 4371155) B4371155
theorem B6551401 : Blo 1725063 6551401 := bstep (se 2 (by rfl) ⟨2456775, by rfl⟩ : syracuseStep 6551401 = 4913551) B4913551
theorem B1726363 : Blo 1725063 1726363 := bstep (se 1 (by rfl) ⟨1294772, by rfl⟩ : syracuseStep 1726363 = 2589545) B2589545
theorem B218331065 : Blo 1725063 218331065 := bstep (se 2 (by rfl) ⟨81874149, by rfl⟩ : syracuseStep 218331065 = 163748299) B163748299
theorem B21002171 : Blo 1725063 21002171 := bstep (se 1 (by rfl) ⟨15751628, by rfl⟩ : syracuseStep 21002171 = 31503257) B31503257
theorem B1726415 : Blo 1725063 1726415 := bstep (se 1 (by rfl) ⟨1294811, by rfl⟩ : syracuseStep 1726415 = 2589623) B2589623
theorem B1726439 : Blo 1725063 1726439 := bstep (se 1 (by rfl) ⟨1294829, by rfl⟩ : syracuseStep 1726439 = 2589659) B2589659
theorem B3684361 : Blo 1725063 3684361 := bstep (se 2 (by rfl) ⟨1381635, by rfl⟩ : syracuseStep 3684361 = 2763271) B2763271
theorem B7092359 : Blo 1725063 7092359 := bstep (se 1 (by rfl) ⟨5319269, by rfl⟩ : syracuseStep 7092359 = 10638539) B10638539
theorem B17717383 : Blo 1725063 17717383 := bstep (se 1 (by rfl) ⟨13288037, by rfl⟩ : syracuseStep 17717383 = 26576075) B26576075
theorem B3684617 : Blo 1725063 3684617 := bstep (se 2 (by rfl) ⟨1381731, by rfl⟩ : syracuseStep 3684617 = 2763463) B2763463
theorem B1726751 : Blo 1725063 1726751 := bstep (se 1 (by rfl) ⟨1295063, by rfl⟩ : syracuseStep 1726751 = 2590127) B2590127
theorem B1726811 : Blo 1725063 1726811 := bstep (se 1 (by rfl) ⟨1295108, by rfl⟩ : syracuseStep 1726811 = 2590217) B2590217
theorem B1726831 : Blo 1725063 1726831 := bstep (se 1 (by rfl) ⟨1295123, by rfl⟩ : syracuseStep 1726831 = 2590247) B2590247
theorem B1726887 : Blo 1725063 1726887 := bstep (se 1 (by rfl) ⟨1295165, by rfl⟩ : syracuseStep 1726887 = 2590331) B2590331
theorem B1726971 : Blo 1725063 1726971 := bstep (se 1 (by rfl) ⟨1295228, by rfl⟩ : syracuseStep 1726971 = 2590457) B2590457
theorem B204429887 : Blo 1725063 204429887 := bstep (se 1 (by rfl) ⟨153322415, by rfl⟩ : syracuseStep 204429887 = 306644831) B306644831
theorem B1727039 : Blo 1725063 1727039 := bstep (se 1 (by rfl) ⟨1295279, by rfl⟩ : syracuseStep 1727039 = 2590559) B2590559
theorem B1727047 : Blo 1725063 1727047 := bstep (se 1 (by rfl) ⟨1295285, by rfl⟩ : syracuseStep 1727047 = 2590571) B2590571
theorem B9828971 : Blo 1725063 9828971 := bstep (se 1 (by rfl) ⟨7371728, by rfl⟩ : syracuseStep 9828971 = 14743457) B14743457
theorem B8739575 : Blo 1725063 8739575 := bstep (se 1 (by rfl) ⟨6554681, by rfl⟩ : syracuseStep 8739575 = 13109363) B13109363
theorem B5823251 : Blo 1725063 5823251 := bstep (se 1 (by rfl) ⟨4367438, by rfl⟩ : syracuseStep 5823251 = 8734877) B8734877
theorem B4913939 : Blo 1725063 4913939 := bstep (se 1 (by rfl) ⟨3685454, by rfl⟩ : syracuseStep 4913939 = 7370909) B7370909
theorem B3881807 : Blo 1725063 3881807 := bstep (se 1 (by rfl) ⟨2911355, by rfl⟩ : syracuseStep 3881807 = 5822711) B5822711
theorem B5905277 : Blo 1725063 5905277 := bstep (se 3 (by rfl) ⟨1107239, by rfl⟩ : syracuseStep 5905277 = 2214479) B2214479
theorem B29498255 : Blo 1725063 29498255 := bstep (se 1 (by rfl) ⟨22123691, by rfl⟩ : syracuseStep 29498255 = 44247383) B44247383
theorem B8297387 : Blo 1725063 8297387 := bstep (se 1 (by rfl) ⟨6223040, by rfl⟩ : syracuseStep 8297387 = 12446081) B12446081
theorem B11967419 : Blo 1725063 11967419 := bstep (se 1 (by rfl) ⟨8975564, by rfl⟩ : syracuseStep 11967419 = 17951129) B17951129
theorem B3882023 : Blo 1725063 3882023 := bstep (se 1 (by rfl) ⟨2911517, by rfl⟩ : syracuseStep 3882023 = 5823035) B5823035
theorem B3882203 : Blo 1725063 3882203 := bstep (se 1 (by rfl) ⟨2911652, by rfl⟩ : syracuseStep 3882203 = 5823305) B5823305
theorem B4914395 : Blo 1725063 4914395 := bstep (se 1 (by rfl) ⟨3685796, by rfl⟩ : syracuseStep 4914395 = 7371593) B7371593
theorem B8740061 : Blo 1725063 8740061 := bstep (se 3 (by rfl) ⟨1638761, by rfl⟩ : syracuseStep 8740061 = 3277523) B3277523
theorem B2587943 : Blo 1725063 2587943 := bstep (se 1 (by rfl) ⟨1940957, by rfl⟩ : syracuseStep 2587943 = 3881915) B3881915
theorem B1940827 : Blo 1725063 1940827 := bstep (se 1 (by rfl) ⟨1455620, by rfl⟩ : syracuseStep 1940827 = 2911241) B2911241
theorem B2588027 : Blo 1725063 2588027 := bstep (se 1 (by rfl) ⟨1941020, by rfl⟩ : syracuseStep 2588027 = 3882041) B3882041
theorem B2841979 : Blo 1725063 2841979 := bstep (se 1 (by rfl) ⟨2131484, by rfl⟩ : syracuseStep 2841979 = 4262969) B4262969
theorem B3882401 : Blo 1725063 3882401 := bstep (se 2 (by rfl) ⟨1455900, by rfl⟩ : syracuseStep 3882401 = 2911801) B2911801
theorem B1842599 : Blo 1725063 1842599 := bstep (se 1 (by rfl) ⟨1381949, by rfl⟩ : syracuseStep 1842599 = 2763899) B2763899
theorem B1940935 : Blo 1725063 1940935 := bstep (se 1 (by rfl) ⟨1455701, by rfl⟩ : syracuseStep 1940935 = 2911403) B2911403
theorem B2588153 : Blo 1725063 2588153 := bstep (se 2 (by rfl) ⟨970557, by rfl⟩ : syracuseStep 2588153 = 1941115) B1941115
theorem B3735047 : Blo 1725063 3735047 := bstep (se 1 (by rfl) ⟨2801285, by rfl⟩ : syracuseStep 3735047 = 5602571) B5602571
theorem B16588313 : Blo 1725063 16588313 := bstep (se 2 (by rfl) ⟨6220617, by rfl⟩ : syracuseStep 16588313 = 12441235) B12441235
theorem B2588255 : Blo 1725063 2588255 := bstep (se 1 (by rfl) ⟨1941191, by rfl⟩ : syracuseStep 2588255 = 3882383) B3882383
theorem B5824115 : Blo 1725063 5824115 := bstep (se 1 (by rfl) ⟨4368086, by rfl⟩ : syracuseStep 5824115 = 8736173) B8736173
theorem B3276551 : Blo 1725063 3276551 := bstep (se 1 (by rfl) ⟨2457413, by rfl⟩ : syracuseStep 3276551 = 4914827) B4914827
theorem B1941295 : Blo 1725063 1941295 := bstep (se 1 (by rfl) ⟨1455971, by rfl⟩ : syracuseStep 1941295 = 2911943) B2911943
theorem B2457391 : Blo 1725063 2457391 := bstep (se 1 (by rfl) ⟨1843043, by rfl⟩ : syracuseStep 2457391 = 3686087) B3686087
theorem B2588471 : Blo 1725063 2588471 := bstep (se 1 (by rfl) ⟨1941353, by rfl⟩ : syracuseStep 2588471 = 3882707) B3882707
theorem B3686249 : Blo 1725063 3686249 := bstep (se 2 (by rfl) ⟨1382343, by rfl⟩ : syracuseStep 3686249 = 2764687) B2764687
theorem B5824385 : Blo 1725063 5824385 := bstep (se 2 (by rfl) ⟨2184144, by rfl⟩ : syracuseStep 5824385 = 4368289) B4368289
theorem B1941403 : Blo 1725063 1941403 := bstep (se 1 (by rfl) ⟨1456052, by rfl⟩ : syracuseStep 1941403 = 2912105) B2912105
theorem B3882959 : Blo 1725063 3882959 := bstep (se 1 (by rfl) ⟨2912219, by rfl⟩ : syracuseStep 3882959 = 5824439) B5824439
theorem B2588891 : Blo 1725063 2588891 := bstep (se 1 (by rfl) ⟨1941668, by rfl⟩ : syracuseStep 2588891 = 3883337) B3883337
theorem B2588903 : Blo 1725063 2588903 := bstep (se 1 (by rfl) ⟨1941677, by rfl⟩ : syracuseStep 2588903 = 3883355) B3883355
theorem B6553831 : Blo 1725063 6553831 := bstep (se 1 (by rfl) ⟨4915373, by rfl⟩ : syracuseStep 6553831 = 9830747) B9830747
theorem B8290583 : Blo 1725063 8290583 := bstep (se 1 (by rfl) ⟨6217937, by rfl⟩ : syracuseStep 8290583 = 12435875) B12435875
theorem B2457983 : Blo 1725063 2457983 := bstep (se 1 (by rfl) ⟨1843487, by rfl⟩ : syracuseStep 2457983 = 3686975) B3686975
theorem B2589065 : Blo 1725063 2589065 := bstep (se 2 (by rfl) ⟨970899, by rfl⟩ : syracuseStep 2589065 = 1941799) B1941799
theorem B3883463 : Blo 1725063 3883463 := bstep (se 1 (by rfl) ⟨2912597, by rfl⟩ : syracuseStep 3883463 = 5825195) B5825195
theorem B49889735 : Blo 1725063 49889735 := bstep (se 1 (by rfl) ⟨37417301, by rfl⟩ : syracuseStep 49889735 = 74834603) B74834603
theorem B2458063 : Blo 1725063 2458063 := bstep (se 1 (by rfl) ⟨1843547, by rfl⟩ : syracuseStep 2458063 = 3687095) B3687095
theorem B2589161 : Blo 1725063 2589161 := bstep (se 2 (by rfl) ⟨970935, by rfl⟩ : syracuseStep 2589161 = 1941871) B1941871
theorem B12780071 : Blo 1725063 12780071 := bstep (se 1 (by rfl) ⟨9585053, by rfl⟩ : syracuseStep 12780071 = 19170107) B19170107
theorem B5825087 : Blo 1725063 5825087 := bstep (se 1 (by rfl) ⟨4368815, by rfl⟩ : syracuseStep 5825087 = 8737631) B8737631
theorem B50471495 : Blo 1725063 50471495 := bstep (se 1 (by rfl) ⟨37853621, by rfl⟩ : syracuseStep 50471495 = 75707243) B75707243
theorem B2589287 : Blo 1725063 2589287 := bstep (se 1 (by rfl) ⟨1941965, by rfl⟩ : syracuseStep 2589287 = 3883931) B3883931
theorem B8733419 : Blo 1725063 8733419 := bstep (se 1 (by rfl) ⟨6550064, by rfl⟩ : syracuseStep 8733419 = 13100129) B13100129
theorem B2589419 : Blo 1725063 2589419 := bstep (se 1 (by rfl) ⟨1942064, by rfl⟩ : syracuseStep 2589419 = 3884129) B3884129
theorem B2589449 : Blo 1725063 2589449 := bstep (se 2 (by rfl) ⟨971043, by rfl⟩ : syracuseStep 2589449 = 1942087) B1942087
theorem B3277577 : Blo 1725063 3277577 := bstep (se 2 (by rfl) ⟨1229091, by rfl⟩ : syracuseStep 3277577 = 2458183) B2458183
theorem B3883823 : Blo 1725063 3883823 := bstep (se 1 (by rfl) ⟨2912867, by rfl⟩ : syracuseStep 3883823 = 5825735) B5825735
theorem B2589551 : Blo 1725063 2589551 := bstep (se 1 (by rfl) ⟨1942163, by rfl⟩ : syracuseStep 2589551 = 3884327) B3884327
theorem B1942591 : Blo 1725063 1942591 := bstep (se 1 (by rfl) ⟨1456943, by rfl⟩ : syracuseStep 1942591 = 2913887) B2913887
theorem B2589803 : Blo 1725063 2589803 := bstep (se 1 (by rfl) ⟨1942352, by rfl⟩ : syracuseStep 2589803 = 3884705) B3884705
theorem B1942735 : Blo 1725063 1942735 := bstep (se 1 (by rfl) ⟨1457051, by rfl⟩ : syracuseStep 1942735 = 2914103) B2914103
theorem B2590043 : Blo 1725063 2590043 := bstep (se 1 (by rfl) ⟨1942532, by rfl⟩ : syracuseStep 2590043 = 3885065) B3885065
theorem B20989327 : Blo 1725063 20989327 := bstep (se 1 (by rfl) ⟨15741995, by rfl⟩ : syracuseStep 20989327 = 31483991) B31483991
theorem B4728239 : Blo 1725063 4728239 := bstep (se 1 (by rfl) ⟨3546179, by rfl⟩ : syracuseStep 4728239 = 7092359) B7092359
theorem B4916695 : Blo 1725063 4916695 := bstep (se 1 (by rfl) ⟨3687521, by rfl⟩ : syracuseStep 4916695 = 7375043) B7375043
theorem B5531129 : Blo 1725063 5531129 := bstep (se 2 (by rfl) ⟨2074173, by rfl⟩ : syracuseStep 5531129 = 4148347) B4148347
theorem B2590319 : Blo 1725063 2590319 := bstep (se 1 (by rfl) ⟨1942739, by rfl⟩ : syracuseStep 2590319 = 3885479) B3885479
theorem B5531257 : Blo 1725063 5531257 := bstep (se 2 (by rfl) ⟨2074221, by rfl⟩ : syracuseStep 5531257 = 4148443) B4148443
theorem B6555289 : Blo 1725063 6555289 := bstep (se 2 (by rfl) ⟨2458233, by rfl⟩ : syracuseStep 6555289 = 4916467) B4916467
theorem B7095961 : Blo 1725063 7095961 := bstep (se 2 (by rfl) ⟨2660985, by rfl⟩ : syracuseStep 7095961 = 5321971) B5321971
theorem B2590391 : Blo 1725063 2590391 := bstep (se 1 (by rfl) ⟨1942793, by rfl⟩ : syracuseStep 2590391 = 3885587) B3885587
theorem B2590427 : Blo 1725063 2590427 := bstep (se 1 (by rfl) ⟨1942820, by rfl⟩ : syracuseStep 2590427 = 3885641) B3885641
theorem B3884831 : Blo 1725063 3884831 := bstep (se 1 (by rfl) ⟨2913623, by rfl⟩ : syracuseStep 3884831 = 5827247) B5827247
theorem B5826383 : Blo 1725063 5826383 := bstep (se 1 (by rfl) ⟨4369787, by rfl⟩ : syracuseStep 5826383 = 8739575) B8739575
theorem B11814821 : Blo 1725063 11814821 := bstep (se 4 (by rfl) ⟨1107639, by rfl⟩ : syracuseStep 11814821 = 2215279) B2215279
theorem B5531591 : Blo 1725063 5531591 := bstep (se 1 (by rfl) ⟨4148693, by rfl⟩ : syracuseStep 5531591 = 8297387) B8297387
theorem B2623471 : Blo 1725063 2623471 := bstep (se 1 (by rfl) ⟨1967603, by rfl⟩ : syracuseStep 2623471 = 3935207) B3935207
theorem B3885047 : Blo 1725063 3885047 := bstep (se 1 (by rfl) ⟨2913785, by rfl⟩ : syracuseStep 3885047 = 5827571) B5827571
theorem B49793069 : Blo 1725063 49793069 := bstep (se 3 (by rfl) ⟨9336200, by rfl⟩ : syracuseStep 49793069 = 18672401) B18672401
theorem B29485133 : Blo 1725063 29485133 := bstep (se 3 (by rfl) ⟨5528462, by rfl⟩ : syracuseStep 29485133 = 11056925) B11056925
theorem B5826707 : Blo 1725063 5826707 := bstep (se 1 (by rfl) ⟨4370030, by rfl⟩ : syracuseStep 5826707 = 8740061) B8740061
theorem B3885407 : Blo 1725063 3885407 := bstep (se 1 (by rfl) ⟨2914055, by rfl⟩ : syracuseStep 3885407 = 5828111) B5828111
theorem B5826977 : Blo 1725063 5826977 := bstep (se 2 (by rfl) ⟨2185116, by rfl⟩ : syracuseStep 5826977 = 4370233) B4370233
theorem B8735201 : Blo 1725063 8735201 := bstep (se 2 (by rfl) ⟨3275700, by rfl⟩ : syracuseStep 8735201 = 6551401) B6551401
theorem B9825623 : Blo 1725063 9825623 := bstep (se 1 (by rfl) ⟨7369217, by rfl⟩ : syracuseStep 9825623 = 14738435) B14738435
theorem B6557051 : Blo 1725063 6557051 := bstep (se 1 (by rfl) ⟨4917788, by rfl⟩ : syracuseStep 6557051 = 9835577) B9835577
theorem B2911835 : Blo 1725063 2911835 := bstep (se 1 (by rfl) ⟨2183876, by rfl⟩ : syracuseStep 2911835 = 4367753) B4367753
theorem B9834119 : Blo 1725063 9834119 := bstep (se 1 (by rfl) ⟨7375589, by rfl⟩ : syracuseStep 9834119 = 14751179) B14751179
theorem B2912071 : Blo 1725063 2912071 := bstep (se 1 (by rfl) ⟨2184053, by rfl⟩ : syracuseStep 2912071 = 4368107) B4368107
theorem B22417229 : Blo 1725063 22417229 := bstep (se 3 (by rfl) ⟨4203230, by rfl⟩ : syracuseStep 22417229 = 8406461) B8406461
theorem B323153873 : Blo 1725063 323153873 := bstep (se 2 (by rfl) ⟨121182702, by rfl⟩ : syracuseStep 323153873 = 242365405) B242365405
theorem B7368671 : Blo 1725063 7368671 := bstep (se 1 (by rfl) ⟨5526503, by rfl⟩ : syracuseStep 7368671 = 11053007) B11053007
theorem B7368893 : Blo 1725063 7368893 := bstep (se 3 (by rfl) ⟨1381667, by rfl⟩ : syracuseStep 7368893 = 2763335) B2763335
theorem B2912719 : Blo 1725063 2912719 := bstep (se 1 (by rfl) ⟨2184539, by rfl⟩ : syracuseStep 2912719 = 4369079) B4369079
theorem B3789305 : Blo 1725063 3789305 := bstep (se 2 (by rfl) ⟨1420989, by rfl⟩ : syracuseStep 3789305 = 2841979) B2841979
theorem B3936851 : Blo 1725063 3936851 := bstep (se 1 (by rfl) ⟨2952638, by rfl⟩ : syracuseStep 3936851 = 5905277) B5905277
theorem B19665503 : Blo 1725063 19665503 := bstep (se 1 (by rfl) ⟨14749127, by rfl⟩ : syracuseStep 19665503 = 29498255) B29498255
theorem B8737469 : Blo 1725063 8737469 := bstep (se 3 (by rfl) ⟨1638275, by rfl⟩ : syracuseStep 8737469 = 3276551) B3276551
theorem B1725295 : Blo 1725063 1725295 := bstep (se 1 (by rfl) ⟨1293971, by rfl⟩ : syracuseStep 1725295 = 2587943) B2587943
theorem B1725351 : Blo 1725063 1725351 := bstep (se 1 (by rfl) ⟨1294013, by rfl⟩ : syracuseStep 1725351 = 2588027) B2588027
theorem B7369643 : Blo 1725063 7369643 := bstep (se 1 (by rfl) ⟨5527232, by rfl⟩ : syracuseStep 7369643 = 11054465) B11054465
theorem B1725435 : Blo 1725063 1725435 := bstep (se 1 (by rfl) ⟨1294076, by rfl⟩ : syracuseStep 1725435 = 2588153) B2588153
theorem B1725503 : Blo 1725063 1725503 := bstep (se 1 (by rfl) ⟨1294127, by rfl⟩ : syracuseStep 1725503 = 2588255) B2588255
theorem B4371529 : Blo 1725063 4371529 := bstep (se 2 (by rfl) ⟨1639323, by rfl⟩ : syracuseStep 4371529 = 3278647) B3278647
theorem B56005789 : Blo 1725063 56005789 := bstep (se 3 (by rfl) ⟨10501085, by rfl⟩ : syracuseStep 56005789 = 21002171) B21002171
theorem B2913455 : Blo 1725063 2913455 := bstep (se 1 (by rfl) ⟨2185091, by rfl⟩ : syracuseStep 2913455 = 4370183) B4370183
theorem B1725647 : Blo 1725063 1725647 := bstep (se 1 (by rfl) ⟨1294235, by rfl⟩ : syracuseStep 1725647 = 2588471) B2588471
theorem B4912481 : Blo 1725063 4912481 := bstep (se 2 (by rfl) ⟨1842180, by rfl⟩ : syracuseStep 4912481 = 3684361) B3684361
theorem B1725851 : Blo 1725063 1725851 := bstep (se 1 (by rfl) ⟨1294388, by rfl⟩ : syracuseStep 1725851 = 2588777) B2588777
theorem B2913691 : Blo 1725063 2913691 := bstep (se 1 (by rfl) ⟨2185268, by rfl⟩ : syracuseStep 2913691 = 4370537) B4370537
theorem B23623177 : Blo 1725063 23623177 := bstep (se 2 (by rfl) ⟨8858691, by rfl⟩ : syracuseStep 23623177 = 17717383) B17717383
theorem B7370311 : Blo 1725063 7370311 := bstep (se 1 (by rfl) ⟨5527733, by rfl⟩ : syracuseStep 7370311 = 11055467) B11055467
theorem B1726063 : Blo 1725063 1726063 := bstep (se 1 (by rfl) ⟨1294547, by rfl⟩ : syracuseStep 1726063 = 2589095) B2589095
theorem B1726119 : Blo 1725063 1726119 := bstep (se 1 (by rfl) ⟨1294589, by rfl⟩ : syracuseStep 1726119 = 2589179) B2589179
theorem B2914015 : Blo 1725063 2914015 := bstep (se 1 (by rfl) ⟨2185511, by rfl⟩ : syracuseStep 2914015 = 4371023) B4371023
theorem B1726203 : Blo 1725063 1726203 := bstep (se 1 (by rfl) ⟨1294652, by rfl⟩ : syracuseStep 1726203 = 2589305) B2589305
theorem B1726239 : Blo 1725063 1726239 := bstep (se 1 (by rfl) ⟨1294679, by rfl⟩ : syracuseStep 1726239 = 2589359) B2589359
theorem B1726271 : Blo 1725063 1726271 := bstep (se 1 (by rfl) ⟨1294703, by rfl⟩ : syracuseStep 1726271 = 2589407) B2589407
theorem B11810717 : Blo 1725063 11810717 := bstep (se 3 (by rfl) ⟨2214509, by rfl⟩ : syracuseStep 11810717 = 4429019) B4429019
theorem B5904343 : Blo 1725063 5904343 := bstep (se 1 (by rfl) ⟨4428257, by rfl⟩ : syracuseStep 5904343 = 8856515) B8856515
theorem B1726447 : Blo 1725063 1726447 := bstep (se 1 (by rfl) ⟨1294835, by rfl⟩ : syracuseStep 1726447 = 2589671) B2589671
theorem B2180585461 : Blo 1725063 2180585461 := bstep (se 5 (by rfl) ⟨102214943, by rfl⟩ : syracuseStep 2180585461 = 204429887) B204429887
theorem B11810875 : Blo 1725063 11810875 := bstep (se 1 (by rfl) ⟨8858156, by rfl⟩ : syracuseStep 11810875 = 17716313) B17716313
theorem B1726619 : Blo 1725063 1726619 := bstep (se 1 (by rfl) ⟨1294964, by rfl⟩ : syracuseStep 1726619 = 2589929) B2589929
theorem B1726655 : Blo 1725063 1726655 := bstep (se 1 (by rfl) ⟨1294991, by rfl⟩ : syracuseStep 1726655 = 2589983) B2589983
theorem B1726767 : Blo 1725063 1726767 := bstep (se 1 (by rfl) ⟨1295075, by rfl⟩ : syracuseStep 1726767 = 2590151) B2590151
theorem B19650923 : Blo 1725063 19650923 := bstep (se 1 (by rfl) ⟨14738192, by rfl⟩ : syracuseStep 19650923 = 29476385) B29476385
theorem B4913597 : Blo 1725063 4913597 := bstep (se 3 (by rfl) ⟨921299, by rfl⟩ : syracuseStep 4913597 = 1842599) B1842599
theorem B1727003 : Blo 1725063 1727003 := bstep (se 1 (by rfl) ⟨1295252, by rfl⟩ : syracuseStep 1727003 = 2590505) B2590505
theorem B1727007 : Blo 1725063 1727007 := bstep (se 1 (by rfl) ⟨1295255, by rfl⟩ : syracuseStep 1727007 = 2590511) B2590511
theorem B4430393 : Blo 1725063 4430393 := bstep (se 2 (by rfl) ⟨1661397, by rfl⟩ : syracuseStep 4430393 = 3322795) B3322795
theorem B145554043 : Blo 1725063 145554043 := bstep (se 1 (by rfl) ⟨109165532, by rfl⟩ : syracuseStep 145554043 = 218331065) B218331065
theorem B3881609 : Blo 1725063 3881609 := bstep (se 2 (by rfl) ⟨1455603, by rfl⟩ : syracuseStep 3881609 = 2911207) B2911207
theorem B2456411 : Blo 1725063 2456411 := bstep (se 1 (by rfl) ⟨1842308, by rfl⟩ : syracuseStep 2456411 = 3684617) B3684617
theorem B19184681 : Blo 1725063 19184681 := bstep (se 2 (by rfl) ⟨7194255, by rfl⟩ : syracuseStep 19184681 = 14388511) B14388511
theorem B6552647 : Blo 1725063 6552647 := bstep (se 1 (by rfl) ⟨4914485, by rfl⟩ : syracuseStep 6552647 = 9828971) B9828971
theorem B2587769 : Blo 1725063 2587769 := bstep (se 2 (by rfl) ⟨970413, by rfl⟩ : syracuseStep 2587769 = 1940827) B1940827
theorem B3882167 : Blo 1725063 3882167 := bstep (se 1 (by rfl) ⟨2911625, by rfl⟩ : syracuseStep 3882167 = 5823251) B5823251
theorem B3275959 : Blo 1725063 3275959 := bstep (se 1 (by rfl) ⟨2456969, by rfl⟩ : syracuseStep 3275959 = 4913939) B4913939
theorem B2587871 : Blo 1725063 2587871 := bstep (se 1 (by rfl) ⟨1940903, by rfl⟩ : syracuseStep 2587871 = 3881807) B3881807
theorem B5823737 : Blo 1725063 5823737 := bstep (se 2 (by rfl) ⟨2183901, by rfl⟩ : syracuseStep 5823737 = 4367803) B4367803
theorem B2587913 : Blo 1725063 2587913 := bstep (se 2 (by rfl) ⟨970467, by rfl⟩ : syracuseStep 2587913 = 1940935) B1940935
theorem B7978279 : Blo 1725063 7978279 := bstep (se 1 (by rfl) ⟨5983709, by rfl⟩ : syracuseStep 7978279 = 11967419) B11967419
theorem B11812193 : Blo 1725063 11812193 := bstep (se 2 (by rfl) ⟨4429572, by rfl⟩ : syracuseStep 11812193 = 8859145) B8859145
theorem B2588015 : Blo 1725063 2588015 := bstep (se 1 (by rfl) ⟨1941011, by rfl⟩ : syracuseStep 2588015 = 3882023) B3882023
theorem B2588135 : Blo 1725063 2588135 := bstep (se 1 (by rfl) ⟨1941101, by rfl⟩ : syracuseStep 2588135 = 3882203) B3882203
theorem B3276263 : Blo 1725063 3276263 := bstep (se 1 (by rfl) ⟨2457197, by rfl⟩ : syracuseStep 3276263 = 4914395) B4914395
theorem B8289773 : Blo 1725063 8289773 := bstep (se 3 (by rfl) ⟨1554332, by rfl⟩ : syracuseStep 8289773 = 3108665) B3108665
theorem B5824007 : Blo 1725063 5824007 := bstep (se 1 (by rfl) ⟨4368005, by rfl⟩ : syracuseStep 5824007 = 8736011) B8736011
theorem B39853579 : Blo 1725063 39853579 := bstep (se 1 (by rfl) ⟨29890184, by rfl⟩ : syracuseStep 39853579 = 59780369) B59780369
theorem B2588267 : Blo 1725063 2588267 := bstep (se 1 (by rfl) ⟨1941200, by rfl⟩ : syracuseStep 2588267 = 3882401) B3882401
theorem B9829997 : Blo 1725063 9829997 := bstep (se 3 (by rfl) ⟨1843124, by rfl⟩ : syracuseStep 9829997 = 3686249) B3686249
theorem B2490031 : Blo 1725063 2490031 := bstep (se 1 (by rfl) ⟨1867523, by rfl⟩ : syracuseStep 2490031 = 3735047) B3735047
theorem B11058875 : Blo 1725063 11058875 := bstep (se 1 (by rfl) ⟨8294156, by rfl⟩ : syracuseStep 11058875 = 16588313) B16588313
theorem B19177169 : Blo 1725063 19177169 := bstep (se 2 (by rfl) ⟨7191438, by rfl⟩ : syracuseStep 19177169 = 14382877) B14382877
theorem B2588393 : Blo 1725063 2588393 := bstep (se 2 (by rfl) ⟨970647, by rfl⟩ : syracuseStep 2588393 = 1941295) B1941295
theorem B3276521 : Blo 1725063 3276521 := bstep (se 2 (by rfl) ⟨1228695, by rfl⟩ : syracuseStep 3276521 = 2457391) B2457391
theorem B3882743 : Blo 1725063 3882743 := bstep (se 1 (by rfl) ⟨2912057, by rfl⟩ : syracuseStep 3882743 = 5824115) B5824115
theorem B2588537 : Blo 1725063 2588537 := bstep (se 2 (by rfl) ⟨970701, by rfl⟩ : syracuseStep 2588537 = 1941403) B1941403
theorem B3547003 : Blo 1725063 3547003 := bstep (se 1 (by rfl) ⟨2660252, by rfl⟩ : syracuseStep 3547003 = 5320505) B5320505
theorem B3882923 : Blo 1725063 3882923 := bstep (se 1 (by rfl) ⟨2912192, by rfl⟩ : syracuseStep 3882923 = 5824385) B5824385
theorem B2588639 : Blo 1725063 2588639 := bstep (se 1 (by rfl) ⟨1941479, by rfl⟩ : syracuseStep 2588639 = 3882959) B3882959
theorem B2588975 : Blo 1725063 2588975 := bstep (se 1 (by rfl) ⟨1941731, by rfl⟩ : syracuseStep 2588975 = 3883463) B3883463
theorem B33259823 : Blo 1725063 33259823 := bstep (se 1 (by rfl) ⟨24944867, by rfl⟩ : syracuseStep 33259823 = 49889735) B49889735
theorem B8520047 : Blo 1725063 8520047 := bstep (se 1 (by rfl) ⟨6390035, by rfl⟩ : syracuseStep 8520047 = 12780071) B12780071
theorem B3883391 : Blo 1725063 3883391 := bstep (se 1 (by rfl) ⟨2912543, by rfl⟩ : syracuseStep 3883391 = 5825087) B5825087
theorem B5824979 : Blo 1725063 5824979 := bstep (se 1 (by rfl) ⟨4368734, by rfl⟩ : syracuseStep 5824979 = 8737469) B8737469
theorem B2589215 : Blo 1725063 2589215 := bstep (se 1 (by rfl) ⟨1941911, by rfl⟩ : syracuseStep 2589215 = 3883823) B3883823
theorem B3883625 : Blo 1725063 3883625 := bstep (se 2 (by rfl) ⟨1456359, by rfl⟩ : syracuseStep 3883625 = 2912719) B2912719
theorem B3277417 : Blo 1725063 3277417 := bstep (se 2 (by rfl) ⟨1229031, by rfl⟩ : syracuseStep 3277417 = 2458063) B2458063
theorem B1942303 : Blo 1725063 1942303 := bstep (se 1 (by rfl) ⟨1456727, by rfl⟩ : syracuseStep 1942303 = 2913455) B2913455
theorem B3687419 : Blo 1725063 3687419 := bstep (se 1 (by rfl) ⟨2765564, by rfl⟩ : syracuseStep 3687419 = 5531129) B5531129
theorem B6554621 : Blo 1725063 6554621 := bstep (se 3 (by rfl) ⟨1228991, by rfl⟩ : syracuseStep 6554621 = 2457983) B2457983
theorem B2589887 : Blo 1725063 2589887 := bstep (se 1 (by rfl) ⟨1942415, by rfl⟩ : syracuseStep 2589887 = 3884831) B3884831
theorem B3884255 : Blo 1725063 3884255 := bstep (se 1 (by rfl) ⟨2913191, by rfl⟩ : syracuseStep 3884255 = 5826383) B5826383
theorem B7873811 : Blo 1725063 7873811 := bstep (se 1 (by rfl) ⟨5905358, by rfl⟩ : syracuseStep 7873811 = 11810717) B11810717
theorem B3687727 : Blo 1725063 3687727 := bstep (se 1 (by rfl) ⟨2765795, by rfl⟩ : syracuseStep 3687727 = 5531591) B5531591
theorem B2590031 : Blo 1725063 2590031 := bstep (se 1 (by rfl) ⟨1942523, by rfl⟩ : syracuseStep 2590031 = 3885047) B3885047
theorem B33195379 : Blo 1725063 33195379 := bstep (se 1 (by rfl) ⟨24896534, by rfl⟩ : syracuseStep 33195379 = 49793069) B49793069
theorem B2590121 : Blo 1725063 2590121 := bstep (se 2 (by rfl) ⟨971295, by rfl⟩ : syracuseStep 2590121 = 1942591) B1942591
theorem B3884471 : Blo 1725063 3884471 := bstep (se 1 (by rfl) ⟨2913353, by rfl⟩ : syracuseStep 3884471 = 5826707) B5826707
theorem B2590271 : Blo 1725063 2590271 := bstep (se 1 (by rfl) ⟨1942703, by rfl⟩ : syracuseStep 2590271 = 3885407) B3885407
theorem B13100615 : Blo 1725063 13100615 := bstep (se 1 (by rfl) ⟨9825461, by rfl⟩ : syracuseStep 13100615 = 19650923) B19650923
theorem B4367945 : Blo 1725063 4367945 := bstep (se 2 (by rfl) ⟨1637979, by rfl⟩ : syracuseStep 4367945 = 3275959) B3275959
theorem B2590313 : Blo 1725063 2590313 := bstep (se 2 (by rfl) ⟨971367, by rfl⟩ : syracuseStep 2590313 = 1942735) B1942735
theorem B3884651 : Blo 1725063 3884651 := bstep (se 1 (by rfl) ⟨2913488, by rfl⟩ : syracuseStep 3884651 = 5826977) B5826977
theorem B27985769 : Blo 1725063 27985769 := bstep (se 2 (by rfl) ⟨10494663, by rfl⟩ : syracuseStep 27985769 = 20989327) B20989327
theorem B3884921 : Blo 1725063 3884921 := bstep (se 2 (by rfl) ⟨1456845, by rfl⟩ : syracuseStep 3884921 = 2913691) B2913691
theorem B6555593 : Blo 1725063 6555593 := bstep (se 2 (by rfl) ⟨2458347, by rfl⟩ : syracuseStep 6555593 = 4916695) B4916695
theorem B12789787 : Blo 1725063 12789787 := bstep (se 1 (by rfl) ⟨9592340, by rfl⟩ : syracuseStep 12789787 = 19184681) B19184681
theorem B4368431 : Blo 1725063 4368431 := bstep (se 1 (by rfl) ⟨3276323, by rfl⟩ : syracuseStep 4368431 = 6552647) B6552647
theorem B7375009 : Blo 1725063 7375009 := bstep (se 2 (by rfl) ⟨2765628, by rfl⟩ : syracuseStep 7375009 = 5531257) B5531257
theorem B3320041 : Blo 1725063 3320041 := bstep (se 2 (by rfl) ⟨1245015, by rfl⟩ : syracuseStep 3320041 = 2490031) B2490031
theorem B7874795 : Blo 1725063 7874795 := bstep (se 1 (by rfl) ⟨5906096, by rfl⟩ : syracuseStep 7874795 = 11812193) B11812193
theorem B3885353 : Blo 1725063 3885353 := bstep (se 2 (by rfl) ⟨1457007, by rfl⟩ : syracuseStep 3885353 = 2914015) B2914015
theorem B6556079 : Blo 1725063 6556079 := bstep (se 1 (by rfl) ⟨4917059, by rfl⟩ : syracuseStep 6556079 = 9834119) B9834119
theorem B4729337 : Blo 1725063 4729337 := bstep (se 2 (by rfl) ⟨1773501, by rfl⟩ : syracuseStep 4729337 = 3547003) B3547003
theorem B14944819 : Blo 1725063 14944819 := bstep (se 1 (by rfl) ⟨11208614, by rfl⟩ : syracuseStep 14944819 = 22417229) B22417229
theorem B215435915 : Blo 1725063 215435915 := bstep (se 1 (by rfl) ⟨161576936, by rfl⟩ : syracuseStep 215435915 = 323153873) B323153873
theorem B15747833 : Blo 1725063 15747833 := bstep (se 2 (by rfl) ⟨5905437, by rfl⟩ : syracuseStep 15747833 = 11810875) B11810875
theorem B2526203 : Blo 1725063 2526203 := bstep (se 1 (by rfl) ⟨1894652, by rfl⟩ : syracuseStep 2526203 = 3789305) B3789305
theorem B33647663 : Blo 1725063 33647663 := bstep (se 1 (by rfl) ⟨25235747, by rfl⟩ : syracuseStep 33647663 = 50471495) B50471495
theorem B2624567 : Blo 1725063 2624567 := bstep (se 1 (by rfl) ⟨1968425, by rfl⟩ : syracuseStep 2624567 = 3936851) B3936851
theorem B13110335 : Blo 1725063 13110335 := bstep (se 1 (by rfl) ⟨9832751, by rfl⟩ : syracuseStep 13110335 = 19665503) B19665503
theorem B194072057 : Blo 1725063 194072057 := bstep (se 2 (by rfl) ⟨72777021, by rfl⟩ : syracuseStep 194072057 = 145554043) B145554043
theorem B7876547 : Blo 1725063 7876547 := bstep (se 1 (by rfl) ⟨5907410, by rfl⟩ : syracuseStep 7876547 = 11814821) B11814821
theorem B19656755 : Blo 1725063 19656755 := bstep (se 1 (by rfl) ⟨14742566, by rfl⟩ : syracuseStep 19656755 = 29485133) B29485133
theorem B5828705 : Blo 1725063 5828705 := bstep (se 2 (by rfl) ⟨2185764, by rfl⟩ : syracuseStep 5828705 = 4371529) B4371529
theorem B74674385 : Blo 1725063 74674385 := bstep (se 2 (by rfl) ⟨28002894, by rfl⟩ : syracuseStep 74674385 = 56005789) B56005789
theorem B2953595 : Blo 1725063 2953595 := bstep (se 1 (by rfl) ⟨2215196, by rfl⟩ : syracuseStep 2953595 = 4430393) B4430393
theorem B10637705 : Blo 1725063 10637705 := bstep (se 2 (by rfl) ⟨3989139, by rfl⟩ : syracuseStep 10637705 = 7978279) B7978279
theorem B51139117 : Blo 1725063 51139117 := bstep (se 3 (by rfl) ⟨9588584, by rfl⟩ : syracuseStep 51139117 = 19177169) B19177169
theorem B53138105 : Blo 1725063 53138105 := bstep (se 2 (by rfl) ⟨19926789, by rfl⟩ : syracuseStep 53138105 = 39853579) B39853579
theorem B1725179 : Blo 1725063 1725179 := bstep (se 1 (by rfl) ⟨1293884, by rfl⟩ : syracuseStep 1725179 = 2587769) B2587769
theorem B9827081 : Blo 1725063 9827081 := bstep (se 2 (by rfl) ⟨3685155, by rfl⟩ : syracuseStep 9827081 = 7370311) B7370311
theorem B1725247 : Blo 1725063 1725247 := bstep (se 1 (by rfl) ⟨1293935, by rfl⟩ : syracuseStep 1725247 = 2587871) B2587871
theorem B1725275 : Blo 1725063 1725275 := bstep (se 1 (by rfl) ⟨1293956, by rfl⟩ : syracuseStep 1725275 = 2587913) B2587913
theorem B6550415 : Blo 1725063 6550415 := bstep (se 1 (by rfl) ⟨4912811, by rfl⟩ : syracuseStep 6550415 = 9825623) B9825623
theorem B6550429 : Blo 1725063 6550429 := bstep (se 3 (by rfl) ⟨1228205, by rfl⟩ : syracuseStep 6550429 = 2456411) B2456411
theorem B1725343 : Blo 1725063 1725343 := bstep (se 1 (by rfl) ⟨1294007, by rfl⟩ : syracuseStep 1725343 = 2588015) B2588015
theorem B4371367 : Blo 1725063 4371367 := bstep (se 1 (by rfl) ⟨3278525, by rfl⟩ : syracuseStep 4371367 = 6557051) B6557051
theorem B1725423 : Blo 1725063 1725423 := bstep (se 1 (by rfl) ⟨1294067, by rfl⟩ : syracuseStep 1725423 = 2588135) B2588135
theorem B2184175 : Blo 1725063 2184175 := bstep (se 1 (by rfl) ⟨1638131, by rfl⟩ : syracuseStep 2184175 = 3276263) B3276263
theorem B5526515 : Blo 1725063 5526515 := bstep (se 1 (by rfl) ⟨4144886, by rfl⟩ : syracuseStep 5526515 = 8289773) B8289773
theorem B1725511 : Blo 1725063 1725511 := bstep (se 1 (by rfl) ⟨1294133, by rfl⟩ : syracuseStep 1725511 = 2588267) B2588267
theorem B1725595 : Blo 1725063 1725595 := bstep (se 1 (by rfl) ⟨1294196, by rfl⟩ : syracuseStep 1725595 = 2588393) B2588393
theorem B2184347 : Blo 1725063 2184347 := bstep (se 1 (by rfl) ⟨1638260, by rfl⟩ : syracuseStep 2184347 = 3276521) B3276521
theorem B1725691 : Blo 1725063 1725691 := bstep (se 1 (by rfl) ⟨1294268, by rfl⟩ : syracuseStep 1725691 = 2588537) B2588537
theorem B4912447 : Blo 1725063 4912447 := bstep (se 1 (by rfl) ⟨3684335, by rfl⟩ : syracuseStep 4912447 = 7368671) B7368671
theorem B1725759 : Blo 1725063 1725759 := bstep (se 1 (by rfl) ⟨1294319, by rfl⟩ : syracuseStep 1725759 = 2588639) B2588639
theorem B4912595 : Blo 1725063 4912595 := bstep (se 1 (by rfl) ⟨3684446, by rfl⟩ : syracuseStep 4912595 = 7368893) B7368893
theorem B1725927 : Blo 1725063 1725927 := bstep (se 1 (by rfl) ⟨1294445, by rfl⟩ : syracuseStep 1725927 = 2588891) B2588891
theorem B1725935 : Blo 1725063 1725935 := bstep (se 1 (by rfl) ⟨1294451, by rfl⟩ : syracuseStep 1725935 = 2588903) B2588903
theorem B5527055 : Blo 1725063 5527055 := bstep (se 1 (by rfl) ⟨4145291, by rfl⟩ : syracuseStep 5527055 = 8290583) B8290583
theorem B1726043 : Blo 1725063 1726043 := bstep (se 1 (by rfl) ⟨1294532, by rfl⟩ : syracuseStep 1726043 = 2589065) B2589065
theorem B8738441 : Blo 1725063 8738441 := bstep (se 2 (by rfl) ⟨3276915, by rfl⟩ : syracuseStep 8738441 = 6553831) B6553831
theorem B1726107 : Blo 1725063 1726107 := bstep (se 1 (by rfl) ⟨1294580, by rfl⟩ : syracuseStep 1726107 = 2589161) B2589161
theorem B1726191 : Blo 1725063 1726191 := bstep (se 1 (by rfl) ⟨1294643, by rfl⟩ : syracuseStep 1726191 = 2589287) B2589287
theorem B5822279 : Blo 1725063 5822279 := bstep (se 1 (by rfl) ⟨4366709, by rfl⟩ : syracuseStep 5822279 = 8733419) B8733419
theorem B1726279 : Blo 1725063 1726279 := bstep (se 1 (by rfl) ⟨1294709, by rfl⟩ : syracuseStep 1726279 = 2589419) B2589419
theorem B1726299 : Blo 1725063 1726299 := bstep (se 1 (by rfl) ⟨1294724, by rfl⟩ : syracuseStep 1726299 = 2589449) B2589449
theorem B2185051 : Blo 1725063 2185051 := bstep (se 1 (by rfl) ⟨1638788, by rfl⟩ : syracuseStep 2185051 = 3277577) B3277577
theorem B1726367 : Blo 1725063 1726367 := bstep (se 1 (by rfl) ⟨1294775, by rfl⟩ : syracuseStep 1726367 = 2589551) B2589551
theorem B1726535 : Blo 1725063 1726535 := bstep (se 1 (by rfl) ⟨1294901, by rfl⟩ : syracuseStep 1726535 = 2589803) B2589803
theorem B1726695 : Blo 1725063 1726695 := bstep (se 1 (by rfl) ⟨1295021, by rfl⟩ : syracuseStep 1726695 = 2590043) B2590043
theorem B3274987 : Blo 1725063 3274987 := bstep (se 1 (by rfl) ⟨2456240, by rfl⟩ : syracuseStep 3274987 = 4912481) B4912481
theorem B3152159 : Blo 1725063 3152159 := bstep (se 1 (by rfl) ⟨2364119, by rfl⟩ : syracuseStep 3152159 = 4728239) B4728239
theorem B1726879 : Blo 1725063 1726879 := bstep (se 1 (by rfl) ⟨1295159, by rfl⟩ : syracuseStep 1726879 = 2590319) B2590319
theorem B1726927 : Blo 1725063 1726927 := bstep (se 1 (by rfl) ⟨1295195, by rfl⟩ : syracuseStep 1726927 = 2590391) B2590391
theorem B1726951 : Blo 1725063 1726951 := bstep (se 1 (by rfl) ⟨1295213, by rfl⟩ : syracuseStep 1726951 = 2590427) B2590427
theorem B3275731 : Blo 1725063 3275731 := bstep (se 1 (by rfl) ⟨2456798, by rfl⟩ : syracuseStep 3275731 = 4913597) B4913597
theorem B5823467 : Blo 1725063 5823467 := bstep (se 1 (by rfl) ⟨4367600, by rfl⟩ : syracuseStep 5823467 = 8735201) B8735201
theorem B2587739 : Blo 1725063 2587739 := bstep (se 1 (by rfl) ⟨1940804, by rfl⟩ : syracuseStep 2587739 = 3881609) B3881609
theorem B31497569 : Blo 1725063 31497569 := bstep (se 2 (by rfl) ⟨11811588, by rfl⟩ : syracuseStep 31497569 = 23623177) B23623177
theorem B2588111 : Blo 1725063 2588111 := bstep (se 1 (by rfl) ⟨1941083, by rfl⟩ : syracuseStep 2588111 = 3882167) B3882167
theorem B3882491 : Blo 1725063 3882491 := bstep (se 1 (by rfl) ⟨2911868, by rfl⟩ : syracuseStep 3882491 = 5823737) B5823737
theorem B8740385 : Blo 1725063 8740385 := bstep (se 2 (by rfl) ⟨3277644, by rfl⟩ : syracuseStep 8740385 = 6555289) B6555289
theorem B9461281 : Blo 1725063 9461281 := bstep (se 2 (by rfl) ⟨3547980, by rfl⟩ : syracuseStep 9461281 = 7095961) B7095961
theorem B55967381 : Blo 1725063 55967381 := bstep (se 6 (by rfl) ⟨1311735, by rfl⟩ : syracuseStep 55967381 = 2623471) B2623471
theorem B3882671 : Blo 1725063 3882671 := bstep (se 1 (by rfl) ⟨2912003, by rfl⟩ : syracuseStep 3882671 = 5824007) B5824007
theorem B1941223 : Blo 1725063 1941223 := bstep (se 1 (by rfl) ⟨1455917, by rfl⟩ : syracuseStep 1941223 = 2911835) B2911835
theorem B6553331 : Blo 1725063 6553331 := bstep (se 1 (by rfl) ⟨4914998, by rfl⟩ : syracuseStep 6553331 = 9829997) B9829997
theorem B3882761 : Blo 1725063 3882761 := bstep (se 2 (by rfl) ⟨1456035, by rfl⟩ : syracuseStep 3882761 = 2912071) B2912071
theorem B19652381 : Blo 1725063 19652381 := bstep (se 3 (by rfl) ⟨3684821, by rfl⟩ : syracuseStep 19652381 = 7369643) B7369643
theorem B31489829 : Blo 1725063 31489829 := bstep (se 4 (by rfl) ⟨2952171, by rfl⟩ : syracuseStep 31489829 = 5904343) B5904343
theorem B7372583 : Blo 1725063 7372583 := bstep (se 1 (by rfl) ⟨5529437, by rfl⟩ : syracuseStep 7372583 = 11058875) B11058875
theorem B2588495 : Blo 1725063 2588495 := bstep (se 1 (by rfl) ⟨1941371, by rfl⟩ : syracuseStep 2588495 = 3882743) B3882743
theorem B2588615 : Blo 1725063 2588615 := bstep (se 1 (by rfl) ⟨1941461, by rfl⟩ : syracuseStep 2588615 = 3882923) B3882923
theorem B2907447281 : Blo 1725063 2907447281 := bstep (se 2 (by rfl) ⟨1090292730, by rfl⟩ : syracuseStep 2907447281 = 2180585461) B2180585461
theorem B49782923 : Blo 1725063 49782923 := bstep (se 1 (by rfl) ⟨37337192, by rfl⟩ : syracuseStep 49782923 = 74674385) B74674385
theorem B2588927 : Blo 1725063 2588927 := bstep (se 1 (by rfl) ⟨1941695, by rfl⟩ : syracuseStep 2588927 = 3883391) B3883391
theorem B3883319 : Blo 1725063 3883319 := bstep (se 1 (by rfl) ⟨2912489, by rfl⟩ : syracuseStep 3883319 = 5824979) B5824979
theorem B4366649 : Blo 1725063 4366649 := bstep (se 2 (by rfl) ⟨1637493, by rfl⟩ : syracuseStep 4366649 = 3274987) B3274987
theorem B2589083 : Blo 1725063 2589083 := bstep (se 1 (by rfl) ⟨1941812, by rfl⟩ : syracuseStep 2589083 = 3883625) B3883625
theorem B5824925 : Blo 1725063 5824925 := bstep (se 3 (by rfl) ⟨1092173, by rfl⟩ : syracuseStep 5824925 = 2184347) B2184347
theorem B4366943 : Blo 1725063 4366943 := bstep (se 1 (by rfl) ⟨3275207, by rfl⟩ : syracuseStep 4366943 = 6550415) B6550415
theorem B2458279 : Blo 1725063 2458279 := bstep (se 1 (by rfl) ⟨1843709, by rfl⟩ : syracuseStep 2458279 = 3687419) B3687419
theorem B2589503 : Blo 1725063 2589503 := bstep (se 1 (by rfl) ⟨1942127, by rfl⟩ : syracuseStep 2589503 = 3884255) B3884255
theorem B2589647 : Blo 1725063 2589647 := bstep (se 1 (by rfl) ⟨1942235, by rfl⟩ : syracuseStep 2589647 = 3884471) B3884471
theorem B2589737 : Blo 1725063 2589737 := bstep (se 2 (by rfl) ⟨971151, by rfl⟩ : syracuseStep 2589737 = 1942303) B1942303
theorem B8733743 : Blo 1725063 8733743 := bstep (se 1 (by rfl) ⟨6550307, by rfl⟩ : syracuseStep 8733743 = 13100615) B13100615
theorem B2589767 : Blo 1725063 2589767 := bstep (se 1 (by rfl) ⟨1942325, by rfl⟩ : syracuseStep 2589767 = 3884651) B3884651
theorem B5825627 : Blo 1725063 5825627 := bstep (se 1 (by rfl) ⟨4369220, by rfl⟩ : syracuseStep 5825627 = 8738441) B8738441
theorem B8733905 : Blo 1725063 8733905 := bstep (se 2 (by rfl) ⟨3275214, by rfl⟩ : syracuseStep 8733905 = 6550429) B6550429
theorem B2589947 : Blo 1725063 2589947 := bstep (se 1 (by rfl) ⟨1942460, by rfl⟩ : syracuseStep 2589947 = 3884921) B3884921
theorem B4367641 : Blo 1725063 4367641 := bstep (se 2 (by rfl) ⟨1637865, by rfl⟩ : syracuseStep 4367641 = 3275731) B3275731
theorem B2590235 : Blo 1725063 2590235 := bstep (se 1 (by rfl) ⟨1942676, by rfl⟩ : syracuseStep 2590235 = 3885353) B3885353
theorem B4916969 : Blo 1725063 4916969 := bstep (se 2 (by rfl) ⟨1843863, by rfl⟩ : syracuseStep 4916969 = 3687727) B3687727
theorem B143623943 : Blo 1725063 143623943 := bstep (se 1 (by rfl) ⟨107717957, by rfl⟩ : syracuseStep 143623943 = 215435915) B215435915
theorem B22431775 : Blo 1725063 22431775 := bstep (se 1 (by rfl) ⟨16823831, by rfl⟩ : syracuseStep 22431775 = 33647663) B33647663
theorem B20998379 : Blo 1725063 20998379 := bstep (se 1 (by rfl) ⟨15748784, by rfl⟩ : syracuseStep 20998379 = 31497569) B31497569
theorem B5826923 : Blo 1725063 5826923 := bstep (se 1 (by rfl) ⟨4370192, by rfl⟩ : syracuseStep 5826923 = 8740385) B8740385
theorem B4368887 : Blo 1725063 4368887 := bstep (se 1 (by rfl) ⟨3276665, by rfl⟩ : syracuseStep 4368887 = 6553331) B6553331
theorem B13101587 : Blo 1725063 13101587 := bstep (se 1 (by rfl) ⟨9826190, by rfl⟩ : syracuseStep 13101587 = 19652381) B19652381
theorem B6736541 : Blo 1725063 6736541 := bstep (se 3 (by rfl) ⟨1263101, by rfl⟩ : syracuseStep 6736541 = 2526203) B2526203
theorem B3885803 : Blo 1725063 3885803 := bstep (se 1 (by rfl) ⟨2914352, by rfl⟩ : syracuseStep 3885803 = 5828705) B5828705
theorem B6998845 : Blo 1725063 6998845 := bstep (se 3 (by rfl) ⟨1312283, by rfl⟩ : syracuseStep 6998845 = 2624567) B2624567
theorem B9833345 : Blo 1725063 9833345 := bstep (se 2 (by rfl) ⟨3687504, by rfl⟩ : syracuseStep 9833345 = 7375009) B7375009
theorem B4426721 : Blo 1725063 4426721 := bstep (se 2 (by rfl) ⟨1660020, by rfl⟩ : syracuseStep 4426721 = 3320041) B3320041
theorem B33623029 : Blo 1725063 33623029 := bstep (se 5 (by rfl) ⟨1576079, by rfl⟩ : syracuseStep 33623029 = 3152159) B3152159
theorem B35425403 : Blo 1725063 35425403 := bstep (se 1 (by rfl) ⟨26569052, by rfl⟩ : syracuseStep 35425403 = 53138105) B53138105
theorem B4369747 : Blo 1725063 4369747 := bstep (se 1 (by rfl) ⟨3277310, by rfl⟩ : syracuseStep 4369747 = 6554621) B6554621
theorem B68185489 : Blo 1725063 68185489 := bstep (se 2 (by rfl) ⟨25569558, by rfl⟩ : syracuseStep 68185489 = 51139117) B51139117
theorem B19926425 : Blo 1725063 19926425 := bstep (se 2 (by rfl) ⟨7472409, by rfl⟩ : syracuseStep 19926425 = 14944819) B14944819
theorem B4369889 : Blo 1725063 4369889 := bstep (se 2 (by rfl) ⟨1638708, by rfl⟩ : syracuseStep 4369889 = 3277417) B3277417
theorem B7876253 : Blo 1725063 7876253 := bstep (se 3 (by rfl) ⟨1476797, by rfl⟩ : syracuseStep 7876253 = 2953595) B2953595
theorem B2911963 : Blo 1725063 2911963 := bstep (se 1 (by rfl) ⟨2183972, by rfl⟩ : syracuseStep 2911963 = 4367945) B4367945
theorem B5828489 : Blo 1725063 5828489 := bstep (se 2 (by rfl) ⟨2185683, by rfl⟩ : syracuseStep 5828489 = 4371367) B4371367
theorem B18657179 : Blo 1725063 18657179 := bstep (se 1 (by rfl) ⟨13992884, by rfl⟩ : syracuseStep 18657179 = 27985769) B27985769
theorem B4370395 : Blo 1725063 4370395 := bstep (se 1 (by rfl) ⟨3277796, by rfl⟩ : syracuseStep 4370395 = 6555593) B6555593
theorem B2912233 : Blo 1725063 2912233 := bstep (se 2 (by rfl) ⟨1092087, by rfl⟩ : syracuseStep 2912233 = 2184175) B2184175
theorem B2912287 : Blo 1725063 2912287 := bstep (se 1 (by rfl) ⟨2184215, by rfl⟩ : syracuseStep 2912287 = 4368431) B4368431
theorem B4370719 : Blo 1725063 4370719 := bstep (se 1 (by rfl) ⟨3278039, by rfl⟩ : syracuseStep 4370719 = 6556079) B6556079
theorem B6549929 : Blo 1725063 6549929 := bstep (se 2 (by rfl) ⟨2456223, by rfl⟩ : syracuseStep 6549929 = 4912447) B4912447
theorem B10498555 : Blo 1725063 10498555 := bstep (se 1 (by rfl) ⟨7873916, by rfl⟩ : syracuseStep 10498555 = 15747833) B15747833
theorem B1725159 : Blo 1725063 1725159 := bstep (se 1 (by rfl) ⟨1293869, by rfl⟩ : syracuseStep 1725159 = 2587739) B2587739
theorem B1725407 : Blo 1725063 1725407 := bstep (se 1 (by rfl) ⟨1294055, by rfl⟩ : syracuseStep 1725407 = 2588111) B2588111
theorem B129381371 : Blo 1725063 129381371 := bstep (se 1 (by rfl) ⟨97036028, by rfl⟩ : syracuseStep 129381371 = 194072057) B194072057
theorem B37311587 : Blo 1725063 37311587 := bstep (se 1 (by rfl) ⟨27983690, by rfl⟩ : syracuseStep 37311587 = 55967381) B55967381
theorem B2913401 : Blo 1725063 2913401 := bstep (se 2 (by rfl) ⟨1092525, by rfl⟩ : syracuseStep 2913401 = 2185051) B2185051
theorem B20993219 : Blo 1725063 20993219 := bstep (se 1 (by rfl) ⟨15744914, by rfl⟩ : syracuseStep 20993219 = 31489829) B31489829
theorem B1725663 : Blo 1725063 1725663 := bstep (se 1 (by rfl) ⟨1294247, by rfl⟩ : syracuseStep 1725663 = 2588495) B2588495
theorem B1725743 : Blo 1725063 1725743 := bstep (se 1 (by rfl) ⟨1294307, by rfl⟩ : syracuseStep 1725743 = 2588615) B2588615
theorem B1938298187 : Blo 1725063 1938298187 := bstep (se 1 (by rfl) ⟨1453723640, by rfl⟩ : syracuseStep 1938298187 = 2907447281) B2907447281
theorem B13104503 : Blo 1725063 13104503 := bstep (se 1 (by rfl) ⟨9828377, by rfl⟩ : syracuseStep 13104503 = 19656755) B19656755
theorem B17053049 : Blo 1725063 17053049 := bstep (se 2 (by rfl) ⟨6394893, by rfl⟩ : syracuseStep 17053049 = 12789787) B12789787
theorem B1725983 : Blo 1725063 1725983 := bstep (se 1 (by rfl) ⟨1294487, by rfl⟩ : syracuseStep 1725983 = 2588975) B2588975
theorem B22173215 : Blo 1725063 22173215 := bstep (se 1 (by rfl) ⟨16629911, by rfl⟩ : syracuseStep 22173215 = 33259823) B33259823
theorem B7091803 : Blo 1725063 7091803 := bstep (se 1 (by rfl) ⟨5318852, by rfl⟩ : syracuseStep 7091803 = 10637705) B10637705
theorem B1726143 : Blo 1725063 1726143 := bstep (se 1 (by rfl) ⟨1294607, by rfl⟩ : syracuseStep 1726143 = 2589215) B2589215
theorem B6551387 : Blo 1725063 6551387 := bstep (se 1 (by rfl) ⟨4913540, by rfl⟩ : syracuseStep 6551387 = 9827081) B9827081
theorem B1726591 : Blo 1725063 1726591 := bstep (se 1 (by rfl) ⟨1294943, by rfl⟩ : syracuseStep 1726591 = 2589887) B2589887
theorem B5249207 : Blo 1725063 5249207 := bstep (se 1 (by rfl) ⟨3936905, by rfl⟩ : syracuseStep 5249207 = 7873811) B7873811
theorem B1726687 : Blo 1725063 1726687 := bstep (se 1 (by rfl) ⟨1295015, by rfl⟩ : syracuseStep 1726687 = 2590031) B2590031
theorem B1726747 : Blo 1725063 1726747 := bstep (se 1 (by rfl) ⟨1295060, by rfl⟩ : syracuseStep 1726747 = 2590121) B2590121
theorem B3275063 : Blo 1725063 3275063 := bstep (se 1 (by rfl) ⟨2456297, by rfl⟩ : syracuseStep 3275063 = 4912595) B4912595
theorem B3684703 : Blo 1725063 3684703 := bstep (se 1 (by rfl) ⟨2763527, by rfl⟩ : syracuseStep 3684703 = 5527055) B5527055
theorem B1726847 : Blo 1725063 1726847 := bstep (se 1 (by rfl) ⟨1295135, by rfl⟩ : syracuseStep 1726847 = 2590271) B2590271
theorem B1726875 : Blo 1725063 1726875 := bstep (se 1 (by rfl) ⟨1295156, by rfl⟩ : syracuseStep 1726875 = 2590313) B2590313
theorem B90880501 : Blo 1725063 90880501 := bstep (se 5 (by rfl) ⟨4260023, by rfl⟩ : syracuseStep 90880501 = 8520047) B8520047
theorem B3881519 : Blo 1725063 3881519 := bstep (se 1 (by rfl) ⟨2911139, by rfl⟩ : syracuseStep 3881519 = 5822279) B5822279
theorem B5249863 : Blo 1725063 5249863 := bstep (se 1 (by rfl) ⟨3937397, by rfl⟩ : syracuseStep 5249863 = 7874795) B7874795
theorem B3152891 : Blo 1725063 3152891 := bstep (se 1 (by rfl) ⟨2364668, by rfl⟩ : syracuseStep 3152891 = 4729337) B4729337
theorem B44260505 : Blo 1725063 44260505 := bstep (se 2 (by rfl) ⟨16597689, by rfl⟩ : syracuseStep 44260505 = 33195379) B33195379
theorem B3882311 : Blo 1725063 3882311 := bstep (se 1 (by rfl) ⟨2911733, by rfl⟩ : syracuseStep 3882311 = 5823467) B5823467
theorem B8740223 : Blo 1725063 8740223 := bstep (se 1 (by rfl) ⟨6555167, by rfl⟩ : syracuseStep 8740223 = 13110335) B13110335
theorem B12615041 : Blo 1725063 12615041 := bstep (se 2 (by rfl) ⟨4730640, by rfl⟩ : syracuseStep 12615041 = 9461281) B9461281
theorem B2588297 : Blo 1725063 2588297 := bstep (se 2 (by rfl) ⟨970611, by rfl⟩ : syracuseStep 2588297 = 1941223) B1941223
theorem B2588327 : Blo 1725063 2588327 := bstep (se 1 (by rfl) ⟨1941245, by rfl⟩ : syracuseStep 2588327 = 3882491) B3882491
theorem B2588447 : Blo 1725063 2588447 := bstep (se 1 (by rfl) ⟨1941335, by rfl⟩ : syracuseStep 2588447 = 3882671) B3882671
theorem B2588507 : Blo 1725063 2588507 := bstep (se 1 (by rfl) ⟨1941380, by rfl⟩ : syracuseStep 2588507 = 3882761) B3882761
theorem B4915055 : Blo 1725063 4915055 := bstep (se 1 (by rfl) ⟨3686291, by rfl⟩ : syracuseStep 4915055 = 7372583) B7372583
theorem B5251031 : Blo 1725063 5251031 := bstep (se 1 (by rfl) ⟨3938273, by rfl⟩ : syracuseStep 5251031 = 7876547) B7876547
theorem B14737373 : Blo 1725063 14737373 := bstep (se 3 (by rfl) ⟨2763257, by rfl⟩ : syracuseStep 14737373 = 5526515) B5526515
theorem B3883049 : Blo 1725063 3883049 := bstep (se 2 (by rfl) ⟨1456143, by rfl⟩ : syracuseStep 3883049 = 2912287) B2912287
theorem B29909033 : Blo 1725063 29909033 := bstep (se 2 (by rfl) ⟨11215887, by rfl⟩ : syracuseStep 29909033 = 22431775) B22431775
theorem B2588879 : Blo 1725063 2588879 := bstep (se 1 (by rfl) ⟨1941659, by rfl⟩ : syracuseStep 2588879 = 3883319) B3883319
theorem B3883283 : Blo 1725063 3883283 := bstep (se 1 (by rfl) ⟨2912462, by rfl⟩ : syracuseStep 3883283 = 5824925) B5824925
theorem B4366619 : Blo 1725063 4366619 := bstep (se 1 (by rfl) ⟨3274964, by rfl⟩ : syracuseStep 4366619 = 6549929) B6549929
theorem B37822949 : Blo 1725063 37822949 := bstep (se 4 (by rfl) ⟨3545901, by rfl⟩ : syracuseStep 37822949 = 7091803) B7091803
theorem B86254247 : Blo 1725063 86254247 := bstep (se 1 (by rfl) ⟨64690685, by rfl⟩ : syracuseStep 86254247 = 129381371) B129381371
theorem B3883751 : Blo 1725063 3883751 := bstep (se 1 (by rfl) ⟨2912813, by rfl⟩ : syracuseStep 3883751 = 5825627) B5825627
theorem B1942267 : Blo 1725063 1942267 := bstep (se 1 (by rfl) ⟨1456700, by rfl⟩ : syracuseStep 1942267 = 2913401) B2913401
theorem B1292198791 : Blo 1725063 1292198791 := bstep (se 1 (by rfl) ⟨969149093, by rfl⟩ : syracuseStep 1292198791 = 1938298187) B1938298187
theorem B45474797 : Blo 1725063 45474797 := bstep (se 3 (by rfl) ⟨8526524, by rfl⟩ : syracuseStep 45474797 = 17053049) B17053049
theorem B9331793 : Blo 1725063 9331793 := bstep (se 2 (by rfl) ⟨3499422, by rfl⟩ : syracuseStep 9331793 = 6998845) B6998845
theorem B3277979 : Blo 1725063 3277979 := bstep (se 1 (by rfl) ⟨2458484, by rfl⟩ : syracuseStep 3277979 = 4916969) B4916969
theorem B95749295 : Blo 1725063 95749295 := bstep (se 1 (by rfl) ⟨71811971, by rfl⟩ : syracuseStep 95749295 = 143623943) B143623943
theorem B4367591 : Blo 1725063 4367591 := bstep (se 1 (by rfl) ⟨3275693, by rfl⟩ : syracuseStep 4367591 = 6551387) B6551387
theorem B3499471 : Blo 1725063 3499471 := bstep (se 1 (by rfl) ⟨2624603, by rfl⟩ : syracuseStep 3499471 = 5249207) B5249207
theorem B3884615 : Blo 1725063 3884615 := bstep (se 1 (by rfl) ⟨2913461, by rfl⟩ : syracuseStep 3884615 = 5826923) B5826923
theorem B8734391 : Blo 1725063 8734391 := bstep (se 1 (by rfl) ⟨6550793, by rfl⟩ : syracuseStep 8734391 = 13101587) B13101587
theorem B5826329 : Blo 1725063 5826329 := bstep (se 2 (by rfl) ⟨2184873, by rfl⟩ : syracuseStep 5826329 = 4369747) B4369747
theorem B2590535 : Blo 1725063 2590535 := bstep (se 1 (by rfl) ⟨1942901, by rfl⟩ : syracuseStep 2590535 = 3885803) B3885803
theorem B6555563 : Blo 1725063 6555563 := bstep (se 1 (by rfl) ⟨4916672, by rfl⟩ : syracuseStep 6555563 = 9833345) B9833345
theorem B2951147 : Blo 1725063 2951147 := bstep (se 1 (by rfl) ⟨2213360, by rfl⟩ : syracuseStep 2951147 = 4426721) B4426721
theorem B5826815 : Blo 1725063 5826815 := bstep (se 1 (by rfl) ⟨4370111, by rfl⟩ : syracuseStep 5826815 = 8740223) B8740223
theorem B3885659 : Blo 1725063 3885659 := bstep (se 1 (by rfl) ⟨2914244, by rfl⟩ : syracuseStep 3885659 = 5828489) B5828489
theorem B12438119 : Blo 1725063 12438119 := bstep (se 1 (by rfl) ⟨9328589, by rfl⟩ : syracuseStep 12438119 = 18657179) B18657179
theorem B5827193 : Blo 1725063 5827193 := bstep (se 2 (by rfl) ⟨2185197, by rfl⟩ : syracuseStep 5827193 = 4370395) B4370395
theorem B3500687 : Blo 1725063 3500687 := bstep (se 1 (by rfl) ⟨2625515, by rfl⟩ : syracuseStep 3500687 = 5251031) B5251031
theorem B9824915 : Blo 1725063 9824915 := bstep (se 1 (by rfl) ⟨7368686, by rfl⟩ : syracuseStep 9824915 = 14737373) B14737373
theorem B8407709 : Blo 1725063 8407709 := bstep (se 3 (by rfl) ⟨1576445, by rfl⟩ : syracuseStep 8407709 = 3152891) B3152891
theorem B33188615 : Blo 1725063 33188615 := bstep (se 1 (by rfl) ⟨24891461, by rfl⟩ : syracuseStep 33188615 = 49782923) B49782923
theorem B2911099 : Blo 1725063 2911099 := bstep (se 1 (by rfl) ⟨2183324, by rfl⟩ : syracuseStep 2911099 = 4366649) B4366649
theorem B5827625 : Blo 1725063 5827625 := bstep (se 2 (by rfl) ⟨2185359, by rfl⟩ : syracuseStep 5827625 = 4370719) B4370719
theorem B2911295 : Blo 1725063 2911295 := bstep (se 1 (by rfl) ⟨2183471, by rfl⟩ : syracuseStep 2911295 = 4366943) B4366943
theorem B24874391 : Blo 1725063 24874391 := bstep (se 1 (by rfl) ⟨18655793, by rfl⟩ : syracuseStep 24874391 = 37311587) B37311587
theorem B13995479 : Blo 1725063 13995479 := bstep (se 1 (by rfl) ⟨10496609, by rfl⟩ : syracuseStep 13995479 = 20993219) B20993219
theorem B13110821 : Blo 1725063 13110821 := bstep (se 4 (by rfl) ⟨1229139, by rfl⟩ : syracuseStep 13110821 = 2458279) B2458279
theorem B8736335 : Blo 1725063 8736335 := bstep (se 1 (by rfl) ⟨6552251, by rfl⟩ : syracuseStep 8736335 = 13104503) B13104503
theorem B33640109 : Blo 1725063 33640109 := bstep (se 3 (by rfl) ⟨6307520, by rfl⟩ : syracuseStep 33640109 = 12615041) B12615041
theorem B6999817 : Blo 1725063 6999817 := bstep (se 2 (by rfl) ⟨2624931, by rfl⟩ : syracuseStep 6999817 = 5249863) B5249863
theorem B44830705 : Blo 1725063 44830705 := bstep (se 2 (by rfl) ⟨16811514, by rfl⟩ : syracuseStep 44830705 = 33623029) B33623029
theorem B2183375 : Blo 1725063 2183375 := bstep (se 1 (by rfl) ⟨1637531, by rfl⟩ : syracuseStep 2183375 = 3275063) B3275063
theorem B2912591 : Blo 1725063 2912591 := bstep (se 1 (by rfl) ⟨2184443, by rfl⟩ : syracuseStep 2912591 = 4368887) B4368887
theorem B13284283 : Blo 1725063 13284283 := bstep (se 1 (by rfl) ⟨9963212, by rfl⟩ : syracuseStep 13284283 = 19926425) B19926425
theorem B2913259 : Blo 1725063 2913259 := bstep (se 1 (by rfl) ⟨2184944, by rfl⟩ : syracuseStep 2913259 = 4369889) B4369889
theorem B1725531 : Blo 1725063 1725531 := bstep (se 1 (by rfl) ⟨1294148, by rfl⟩ : syracuseStep 1725531 = 2588297) B2588297
theorem B1725551 : Blo 1725063 1725551 := bstep (se 1 (by rfl) ⟨1294163, by rfl⟩ : syracuseStep 1725551 = 2588327) B2588327
theorem B1725631 : Blo 1725063 1725631 := bstep (se 1 (by rfl) ⟨1294223, by rfl⟩ : syracuseStep 1725631 = 2588447) B2588447
theorem B1725671 : Blo 1725063 1725671 := bstep (se 1 (by rfl) ⟨1294253, by rfl⟩ : syracuseStep 1725671 = 2588507) B2588507
theorem B1725951 : Blo 1725063 1725951 := bstep (se 1 (by rfl) ⟨1294463, by rfl⟩ : syracuseStep 1725951 = 2588927) B2588927
theorem B1726055 : Blo 1725063 1726055 := bstep (se 1 (by rfl) ⟨1294541, by rfl⟩ : syracuseStep 1726055 = 2589083) B2589083
theorem B4912937 : Blo 1725063 4912937 := bstep (se 2 (by rfl) ⟨1842351, by rfl⟩ : syracuseStep 4912937 = 3684703) B3684703
theorem B1726335 : Blo 1725063 1726335 := bstep (se 1 (by rfl) ⟨1294751, by rfl⟩ : syracuseStep 1726335 = 2589503) B2589503
theorem B1726431 : Blo 1725063 1726431 := bstep (se 1 (by rfl) ⟨1294823, by rfl⟩ : syracuseStep 1726431 = 2589647) B2589647
theorem B121174001 : Blo 1725063 121174001 := bstep (se 2 (by rfl) ⟨45440250, by rfl⟩ : syracuseStep 121174001 = 90880501) B90880501
theorem B1726491 : Blo 1725063 1726491 := bstep (se 1 (by rfl) ⟨1294868, by rfl⟩ : syracuseStep 1726491 = 2589737) B2589737
theorem B5822495 : Blo 1725063 5822495 := bstep (se 1 (by rfl) ⟨4366871, by rfl⟩ : syracuseStep 5822495 = 8733743) B8733743
theorem B1726511 : Blo 1725063 1726511 := bstep (se 1 (by rfl) ⟨1294883, by rfl⟩ : syracuseStep 1726511 = 2589767) B2589767
theorem B5822603 : Blo 1725063 5822603 := bstep (se 1 (by rfl) ⟨4366952, by rfl⟩ : syracuseStep 5822603 = 8733905) B8733905
theorem B1726631 : Blo 1725063 1726631 := bstep (se 1 (by rfl) ⟨1294973, by rfl⟩ : syracuseStep 1726631 = 2589947) B2589947
theorem B1726823 : Blo 1725063 1726823 := bstep (se 1 (by rfl) ⟨1295117, by rfl⟩ : syracuseStep 1726823 = 2590235) B2590235
theorem B59128573 : Blo 1725063 59128573 := bstep (se 3 (by rfl) ⟨11086607, by rfl⟩ : syracuseStep 59128573 = 22173215) B22173215
theorem B13998919 : Blo 1725063 13998919 := bstep (se 1 (by rfl) ⟨10499189, by rfl⟩ : syracuseStep 13998919 = 20998379) B20998379
theorem B2587679 : Blo 1725063 2587679 := bstep (se 1 (by rfl) ⟨1940759, by rfl⟩ : syracuseStep 2587679 = 3881519) B3881519
theorem B5823521 : Blo 1725063 5823521 := bstep (se 2 (by rfl) ⟨2183820, by rfl⟩ : syracuseStep 5823521 = 4367641) B4367641
theorem B17964109 : Blo 1725063 17964109 := bstep (se 3 (by rfl) ⟨3368270, by rfl⟩ : syracuseStep 17964109 = 6736541) B6736541
theorem B90913985 : Blo 1725063 90913985 := bstep (se 2 (by rfl) ⟨34092744, by rfl⟩ : syracuseStep 90913985 = 68185489) B68185489
theorem B23616935 : Blo 1725063 23616935 := bstep (se 1 (by rfl) ⟨17712701, by rfl⟩ : syracuseStep 23616935 = 35425403) B35425403
theorem B29507003 : Blo 1725063 29507003 := bstep (se 1 (by rfl) ⟨22130252, by rfl⟩ : syracuseStep 29507003 = 44260505) B44260505
theorem B2588207 : Blo 1725063 2588207 := bstep (se 1 (by rfl) ⟨1941155, by rfl⟩ : syracuseStep 2588207 = 3882311) B3882311
theorem B3882617 : Blo 1725063 3882617 := bstep (se 2 (by rfl) ⟨1455981, by rfl⟩ : syracuseStep 3882617 = 2911963) B2911963
theorem B5250835 : Blo 1725063 5250835 := bstep (se 1 (by rfl) ⟨3938126, by rfl⟩ : syracuseStep 5250835 = 7876253) B7876253
theorem B3276703 : Blo 1725063 3276703 := bstep (se 1 (by rfl) ⟨2457527, by rfl⟩ : syracuseStep 3276703 = 4915055) B4915055
theorem B3882977 : Blo 1725063 3882977 := bstep (se 2 (by rfl) ⟨1456116, by rfl⟩ : syracuseStep 3882977 = 2912233) B2912233
theorem B55992293 : Blo 1725063 55992293 := bstep (se 4 (by rfl) ⟨5249277, by rfl⟩ : syracuseStep 55992293 = 10498555) B10498555
theorem B2588699 : Blo 1725063 2588699 := bstep (se 1 (by rfl) ⟨1941524, by rfl⟩ : syracuseStep 2588699 = 3883049) B3883049
theorem B19939355 : Blo 1725063 19939355 := bstep (se 1 (by rfl) ⟨14954516, by rfl⟩ : syracuseStep 19939355 = 29909033) B29909033
theorem B2588855 : Blo 1725063 2588855 := bstep (se 1 (by rfl) ⟨1941641, by rfl⟩ : syracuseStep 2588855 = 3883283) B3883283
theorem B1941727 : Blo 1725063 1941727 := bstep (se 1 (by rfl) ⟨1456295, by rfl⟩ : syracuseStep 1941727 = 2912591) B2912591
theorem B25215299 : Blo 1725063 25215299 := bstep (se 1 (by rfl) ⟨18911474, by rfl⟩ : syracuseStep 25215299 = 37822949) B37822949
theorem B2589167 : Blo 1725063 2589167 := bstep (se 1 (by rfl) ⟨1941875, by rfl⟩ : syracuseStep 2589167 = 3883751) B3883751
theorem B2589689 : Blo 1725063 2589689 := bstep (se 2 (by rfl) ⟨971133, by rfl⟩ : syracuseStep 2589689 = 1942267) B1942267
theorem B2589743 : Blo 1725063 2589743 := bstep (se 1 (by rfl) ⟨1942307, by rfl⟩ : syracuseStep 2589743 = 3884615) B3884615
theorem B66331709 : Blo 1725063 66331709 := bstep (se 3 (by rfl) ⟨12437195, by rfl⟩ : syracuseStep 66331709 = 24874391) B24874391
theorem B3884219 : Blo 1725063 3884219 := bstep (se 1 (by rfl) ⟨2913164, by rfl⟩ : syracuseStep 3884219 = 5826329) B5826329
theorem B17712377 : Blo 1725063 17712377 := bstep (se 2 (by rfl) ⟨6642141, by rfl⟩ : syracuseStep 17712377 = 13284283) B13284283
theorem B3884345 : Blo 1725063 3884345 := bstep (se 2 (by rfl) ⟨1456629, by rfl⟩ : syracuseStep 3884345 = 2913259) B2913259
theorem B1967431 : Blo 1725063 1967431 := bstep (se 1 (by rfl) ⟨1475573, by rfl⟩ : syracuseStep 1967431 = 2951147) B2951147
theorem B80782667 : Blo 1725063 80782667 := bstep (se 1 (by rfl) ⟨60587000, by rfl⟩ : syracuseStep 80782667 = 121174001) B121174001
theorem B3884543 : Blo 1725063 3884543 := bstep (se 1 (by rfl) ⟨2913407, by rfl⟩ : syracuseStep 3884543 = 5826815) B5826815
theorem B2590439 : Blo 1725063 2590439 := bstep (se 1 (by rfl) ⟨1942829, by rfl⟩ : syracuseStep 2590439 = 3885659) B3885659
theorem B8292079 : Blo 1725063 8292079 := bstep (se 1 (by rfl) ⟨6219059, by rfl⟩ : syracuseStep 8292079 = 12438119) B12438119
theorem B3884795 : Blo 1725063 3884795 := bstep (se 1 (by rfl) ⟨2913596, by rfl⟩ : syracuseStep 3884795 = 5827193) B5827193
theorem B5605139 : Blo 1725063 5605139 := bstep (se 1 (by rfl) ⟨4203854, by rfl⟩ : syracuseStep 5605139 = 8407709) B8407709
theorem B3885083 : Blo 1725063 3885083 := bstep (se 1 (by rfl) ⟨2913812, by rfl⟩ : syracuseStep 3885083 = 5827625) B5827625
theorem B19671335 : Blo 1725063 19671335 := bstep (se 1 (by rfl) ⟨14753501, by rfl⟩ : syracuseStep 19671335 = 29507003) B29507003
theorem B9333089 : Blo 1725063 9333089 := bstep (se 2 (by rfl) ⟨3499908, by rfl⟩ : syracuseStep 9333089 = 6999817) B6999817
theorem B4368937 : Blo 1725063 4368937 := bstep (se 2 (by rfl) ⟨1638351, by rfl⟩ : syracuseStep 4368937 = 3276703) B3276703
theorem B2911079 : Blo 1725063 2911079 := bstep (se 1 (by rfl) ⟨2183309, by rfl⟩ : syracuseStep 2911079 = 4366619) B4366619
theorem B255331453 : Blo 1725063 255331453 := bstep (se 3 (by rfl) ⟨47874647, by rfl⟩ : syracuseStep 255331453 = 95749295) B95749295
theorem B6221195 : Blo 1725063 6221195 := bstep (se 1 (by rfl) ⟨4665896, by rfl⟩ : syracuseStep 6221195 = 9331793) B9331793
theorem B2911727 : Blo 1725063 2911727 := bstep (se 1 (by rfl) ⟨2183795, by rfl⟩ : syracuseStep 2911727 = 4367591) B4367591
theorem B18665225 : Blo 1725063 18665225 := bstep (se 2 (by rfl) ⟨6999459, by rfl⟩ : syracuseStep 18665225 = 13998919) B13998919
theorem B4370375 : Blo 1725063 4370375 := bstep (se 1 (by rfl) ⟨3277781, by rfl⟩ : syracuseStep 4370375 = 6555563) B6555563
theorem B28004453 : Blo 1725063 28004453 := bstep (se 4 (by rfl) ⟨2625417, by rfl⟩ : syracuseStep 28004453 = 5250835) B5250835
theorem B6549943 : Blo 1725063 6549943 := bstep (se 1 (by rfl) ⟨4912457, by rfl⟩ : syracuseStep 6549943 = 9824915) B9824915
theorem B230011325 : Blo 1725063 230011325 := bstep (se 3 (by rfl) ⟨43127123, by rfl⟩ : syracuseStep 230011325 = 86254247) B86254247
theorem B4665961 : Blo 1725063 4665961 := bstep (se 2 (by rfl) ⟨1749735, by rfl⟩ : syracuseStep 4665961 = 3499471) B3499471
theorem B1725119 : Blo 1725063 1725119 := bstep (se 1 (by rfl) ⟨1293839, by rfl⟩ : syracuseStep 1725119 = 2587679) B2587679
theorem B60609323 : Blo 1725063 60609323 := bstep (se 1 (by rfl) ⟨45456992, by rfl⟩ : syracuseStep 60609323 = 90913985) B90913985
theorem B1725471 : Blo 1725063 1725471 := bstep (se 1 (by rfl) ⟨1294103, by rfl⟩ : syracuseStep 1725471 = 2588207) B2588207
theorem B22426739 : Blo 1725063 22426739 := bstep (se 1 (by rfl) ⟨16820054, by rfl⟩ : syracuseStep 22426739 = 33640109) B33640109
theorem B1261409557 : Blo 1725063 1261409557 := bstep (se 6 (by rfl) ⟨29564286, by rfl⟩ : syracuseStep 1261409557 = 59128573) B59128573
theorem B59774273 : Blo 1725063 59774273 := bstep (se 2 (by rfl) ⟨22415352, by rfl⟩ : syracuseStep 59774273 = 44830705) B44830705
theorem B37328195 : Blo 1725063 37328195 := bstep (se 1 (by rfl) ⟨27996146, by rfl⟩ : syracuseStep 37328195 = 55992293) B55992293
theorem B1725919 : Blo 1725063 1725919 := bstep (se 1 (by rfl) ⟨1294439, by rfl⟩ : syracuseStep 1725919 = 2588879) B2588879
theorem B5822333 : Blo 1725063 5822333 := bstep (se 3 (by rfl) ⟨1091687, by rfl⟩ : syracuseStep 5822333 = 2183375) B2183375
theorem B30316531 : Blo 1725063 30316531 := bstep (se 1 (by rfl) ⟨22737398, by rfl⟩ : syracuseStep 30316531 = 45474797) B45474797
theorem B2185319 : Blo 1725063 2185319 := bstep (se 1 (by rfl) ⟨1638989, by rfl⟩ : syracuseStep 2185319 = 3277979) B3277979
theorem B5822927 : Blo 1725063 5822927 := bstep (se 1 (by rfl) ⟨4367195, by rfl⟩ : syracuseStep 5822927 = 8734391) B8734391
theorem B3881465 : Blo 1725063 3881465 := bstep (se 2 (by rfl) ⟨1455549, by rfl⟩ : syracuseStep 3881465 = 2911099) B2911099
theorem B1722931721 : Blo 1725063 1722931721 := bstep (se 2 (by rfl) ⟨646099395, by rfl⟩ : syracuseStep 1722931721 = 1292198791) B1292198791
theorem B3275291 : Blo 1725063 3275291 := bstep (se 1 (by rfl) ⟨2456468, by rfl⟩ : syracuseStep 3275291 = 4912937) B4912937
theorem B1727023 : Blo 1725063 1727023 := bstep (se 1 (by rfl) ⟨1295267, by rfl⟩ : syracuseStep 1727023 = 2590535) B2590535
theorem B3881663 : Blo 1725063 3881663 := bstep (se 1 (by rfl) ⟨2911247, by rfl⟩ : syracuseStep 3881663 = 5822495) B5822495
theorem B3881735 : Blo 1725063 3881735 := bstep (se 1 (by rfl) ⟨2911301, by rfl⟩ : syracuseStep 3881735 = 5822603) B5822603
theorem B23952145 : Blo 1725063 23952145 := bstep (se 2 (by rfl) ⟨8982054, by rfl⟩ : syracuseStep 23952145 = 17964109) B17964109
theorem B2333791 : Blo 1725063 2333791 := bstep (se 1 (by rfl) ⟨1750343, by rfl⟩ : syracuseStep 2333791 = 3500687) B3500687
theorem B22125743 : Blo 1725063 22125743 := bstep (se 1 (by rfl) ⟨16594307, by rfl⟩ : syracuseStep 22125743 = 33188615) B33188615
theorem B3882347 : Blo 1725063 3882347 := bstep (se 1 (by rfl) ⟨2911760, by rfl⟩ : syracuseStep 3882347 = 5823521) B5823521
theorem B1940863 : Blo 1725063 1940863 := bstep (se 1 (by rfl) ⟨1455647, by rfl⟩ : syracuseStep 1940863 = 2911295) B2911295
theorem B15744623 : Blo 1725063 15744623 := bstep (se 1 (by rfl) ⟨11808467, by rfl⟩ : syracuseStep 15744623 = 23616935) B23616935
theorem B9330319 : Blo 1725063 9330319 := bstep (se 1 (by rfl) ⟨6997739, by rfl⟩ : syracuseStep 9330319 = 13995479) B13995479
theorem B8740547 : Blo 1725063 8740547 := bstep (se 1 (by rfl) ⟨6555410, by rfl⟩ : syracuseStep 8740547 = 13110821) B13110821
theorem B5824223 : Blo 1725063 5824223 := bstep (se 1 (by rfl) ⟨4368167, by rfl⟩ : syracuseStep 5824223 = 8736335) B8736335
theorem B2588411 : Blo 1725063 2588411 := bstep (se 1 (by rfl) ⟨1941308, by rfl⟩ : syracuseStep 2588411 = 3882617) B3882617
theorem B2588651 : Blo 1725063 2588651 := bstep (se 1 (by rfl) ⟨1941488, by rfl⟩ : syracuseStep 2588651 = 3882977) B3882977
theorem B18669635 : Blo 1725063 18669635 := bstep (se 1 (by rfl) ⟨14002226, by rfl⟩ : syracuseStep 18669635 = 28004453) B28004453
theorem B16810199 : Blo 1725063 16810199 := bstep (se 1 (by rfl) ⟨12607649, by rfl⟩ : syracuseStep 16810199 = 25215299) B25215299
theorem B2588969 : Blo 1725063 2588969 := bstep (se 2 (by rfl) ⟨970863, by rfl⟩ : syracuseStep 2588969 = 1941727) B1941727
theorem B8733257 : Blo 1725063 8733257 := bstep (se 2 (by rfl) ⟨3274971, by rfl⟩ : syracuseStep 8733257 = 6549943) B6549943
theorem B44221139 : Blo 1725063 44221139 := bstep (se 1 (by rfl) ⟨33165854, by rfl⟩ : syracuseStep 44221139 = 66331709) B66331709
theorem B5825249 : Blo 1725063 5825249 := bstep (se 2 (by rfl) ⟨2184468, by rfl⟩ : syracuseStep 5825249 = 4368937) B4368937
theorem B14951159 : Blo 1725063 14951159 := bstep (se 1 (by rfl) ⟨11213369, by rfl⟩ : syracuseStep 14951159 = 22426739) B22426739
theorem B2589479 : Blo 1725063 2589479 := bstep (se 1 (by rfl) ⟨1942109, by rfl⟩ : syracuseStep 2589479 = 3884219) B3884219
theorem B2589563 : Blo 1725063 2589563 := bstep (se 1 (by rfl) ⟨1942172, by rfl⟩ : syracuseStep 2589563 = 3884345) B3884345
theorem B53855111 : Blo 1725063 53855111 := bstep (se 1 (by rfl) ⟨40391333, by rfl⟩ : syracuseStep 53855111 = 80782667) B80782667
theorem B2589695 : Blo 1725063 2589695 := bstep (se 1 (by rfl) ⟨1942271, by rfl⟩ : syracuseStep 2589695 = 3884543) B3884543
theorem B2589863 : Blo 1725063 2589863 := bstep (se 1 (by rfl) ⟨1942397, by rfl⟩ : syracuseStep 2589863 = 3884795) B3884795
theorem B2590055 : Blo 1725063 2590055 := bstep (se 1 (by rfl) ⟨1942541, by rfl⟩ : syracuseStep 2590055 = 3885083) B3885083
theorem B41985661 : Blo 1725063 41985661 := bstep (se 3 (by rfl) ⟨7872311, by rfl⟩ : syracuseStep 41985661 = 15744623) B15744623
theorem B2623241 : Blo 1725063 2623241 := bstep (se 2 (by rfl) ⟨983715, by rfl⟩ : syracuseStep 2623241 = 1967431) B1967431
theorem B4147463 : Blo 1725063 4147463 := bstep (se 1 (by rfl) ⟨3110597, by rfl⟩ : syracuseStep 4147463 = 6221195) B6221195
theorem B5827031 : Blo 1725063 5827031 := bstep (se 1 (by rfl) ⟨4370273, by rfl⟩ : syracuseStep 5827031 = 8740547) B8740547
theorem B40422041 : Blo 1725063 40422041 := bstep (se 2 (by rfl) ⟨15158265, by rfl⟩ : syracuseStep 40422041 = 30316531) B30316531
theorem B5827517 : Blo 1725063 5827517 := bstep (se 3 (by rfl) ⟨1092659, by rfl⟩ : syracuseStep 5827517 = 2185319) B2185319
theorem B153340883 : Blo 1725063 153340883 := bstep (se 1 (by rfl) ⟨115005662, by rfl⟩ : syracuseStep 153340883 = 230011325) B230011325
theorem B12446885 : Blo 1725063 12446885 := bstep (se 4 (by rfl) ⟨1166895, by rfl⟩ : syracuseStep 12446885 = 2333791) B2333791
theorem B40406215 : Blo 1725063 40406215 := bstep (se 1 (by rfl) ⟨30304661, by rfl⟩ : syracuseStep 40406215 = 60609323) B60609323
theorem B49761701 : Blo 1725063 49761701 := bstep (se 4 (by rfl) ⟨4665159, by rfl⟩ : syracuseStep 49761701 = 9330319) B9330319
theorem B6221281 : Blo 1725063 6221281 := bstep (se 2 (by rfl) ⟨2332980, by rfl⟩ : syracuseStep 6221281 = 4665961) B4665961
theorem B11808251 : Blo 1725063 11808251 := bstep (se 1 (by rfl) ⟨8856188, by rfl⟩ : syracuseStep 11808251 = 17712377) B17712377
theorem B39849515 : Blo 1725063 39849515 := bstep (se 1 (by rfl) ⟨29887136, by rfl⟩ : syracuseStep 39849515 = 59774273) B59774273
theorem B31936193 : Blo 1725063 31936193 := bstep (se 2 (by rfl) ⟨11976072, by rfl⟩ : syracuseStep 31936193 = 23952145) B23952145
theorem B6222059 : Blo 1725063 6222059 := bstep (se 1 (by rfl) ⟨4666544, by rfl⟩ : syracuseStep 6222059 = 9333089) B9333089
theorem B1148621147 : Blo 1725063 1148621147 := bstep (se 1 (by rfl) ⟨861465860, by rfl⟩ : syracuseStep 1148621147 = 1722931721) B1722931721
theorem B2183527 : Blo 1725063 2183527 := bstep (se 1 (by rfl) ⟨1637645, by rfl⟩ : syracuseStep 2183527 = 3275291) B3275291
theorem B1681879409 : Blo 1725063 1681879409 := bstep (se 2 (by rfl) ⟨630704778, by rfl⟩ : syracuseStep 1681879409 = 1261409557) B1261409557
theorem B14947037 : Blo 1725063 14947037 := bstep (se 3 (by rfl) ⟨2802569, by rfl⟩ : syracuseStep 14947037 = 5605139) B5605139
theorem B14750495 : Blo 1725063 14750495 := bstep (se 1 (by rfl) ⟨11062871, by rfl⟩ : syracuseStep 14750495 = 22125743) B22125743
theorem B11056105 : Blo 1725063 11056105 := bstep (se 2 (by rfl) ⟨4146039, by rfl⟩ : syracuseStep 11056105 = 8292079) B8292079
theorem B1725607 : Blo 1725063 1725607 := bstep (se 1 (by rfl) ⟨1294205, by rfl⟩ : syracuseStep 1725607 = 2588411) B2588411
theorem B2913583 : Blo 1725063 2913583 := bstep (se 1 (by rfl) ⟨2185187, by rfl⟩ : syracuseStep 2913583 = 4370375) B4370375
theorem B1725767 : Blo 1725063 1725767 := bstep (se 1 (by rfl) ⟨1294325, by rfl⟩ : syracuseStep 1725767 = 2588651) B2588651
theorem B1725799 : Blo 1725063 1725799 := bstep (se 1 (by rfl) ⟨1294349, by rfl⟩ : syracuseStep 1725799 = 2588699) B2588699
theorem B13292903 : Blo 1725063 13292903 := bstep (se 1 (by rfl) ⟨9969677, by rfl⟩ : syracuseStep 13292903 = 19939355) B19939355
theorem B1725903 : Blo 1725063 1725903 := bstep (se 1 (by rfl) ⟨1294427, by rfl⟩ : syracuseStep 1725903 = 2588855) B2588855
theorem B1726111 : Blo 1725063 1726111 := bstep (se 1 (by rfl) ⟨1294583, by rfl⟩ : syracuseStep 1726111 = 2589167) B2589167
theorem B1726459 : Blo 1725063 1726459 := bstep (se 1 (by rfl) ⟨1294844, by rfl⟩ : syracuseStep 1726459 = 2589689) B2589689
theorem B1726495 : Blo 1725063 1726495 := bstep (se 1 (by rfl) ⟨1294871, by rfl⟩ : syracuseStep 1726495 = 2589743) B2589743
theorem B24885463 : Blo 1725063 24885463 := bstep (se 1 (by rfl) ⟨18664097, by rfl⟩ : syracuseStep 24885463 = 37328195) B37328195
theorem B1726959 : Blo 1725063 1726959 := bstep (se 1 (by rfl) ⟨1295219, by rfl⟩ : syracuseStep 1726959 = 2590439) B2590439
theorem B3881555 : Blo 1725063 3881555 := bstep (se 1 (by rfl) ⟨2911166, by rfl⟩ : syracuseStep 3881555 = 5822333) B5822333
theorem B340441937 : Blo 1725063 340441937 := bstep (se 2 (by rfl) ⟨127665726, by rfl⟩ : syracuseStep 340441937 = 255331453) B255331453
theorem B13114223 : Blo 1725063 13114223 := bstep (se 1 (by rfl) ⟨9835667, by rfl⟩ : syracuseStep 13114223 = 19671335) B19671335
theorem B3881951 : Blo 1725063 3881951 := bstep (se 1 (by rfl) ⟨2911463, by rfl⟩ : syracuseStep 3881951 = 5822927) B5822927
theorem B2587643 : Blo 1725063 2587643 := bstep (se 1 (by rfl) ⟨1940732, by rfl⟩ : syracuseStep 2587643 = 3881465) B3881465
theorem B2587775 : Blo 1725063 2587775 := bstep (se 1 (by rfl) ⟨1940831, by rfl⟩ : syracuseStep 2587775 = 3881663) B3881663
theorem B2587817 : Blo 1725063 2587817 := bstep (se 2 (by rfl) ⟨970431, by rfl⟩ : syracuseStep 2587817 = 1940863) B1940863
theorem B2587823 : Blo 1725063 2587823 := bstep (se 1 (by rfl) ⟨1940867, by rfl⟩ : syracuseStep 2587823 = 3881735) B3881735
theorem B1940719 : Blo 1725063 1940719 := bstep (se 1 (by rfl) ⟨1455539, by rfl⟩ : syracuseStep 1940719 = 2911079) B2911079
theorem B2588231 : Blo 1725063 2588231 := bstep (se 1 (by rfl) ⟨1941173, by rfl⟩ : syracuseStep 2588231 = 3882347) B3882347
theorem B1941151 : Blo 1725063 1941151 := bstep (se 1 (by rfl) ⟨1455863, by rfl⟩ : syracuseStep 1941151 = 2911727) B2911727
theorem B3882815 : Blo 1725063 3882815 := bstep (se 1 (by rfl) ⟨2912111, by rfl⟩ : syracuseStep 3882815 = 5824223) B5824223
theorem B12443483 : Blo 1725063 12443483 := bstep (se 1 (by rfl) ⟨9332612, by rfl⟩ : syracuseStep 12443483 = 18665225) B18665225
theorem B11206799 : Blo 1725063 11206799 := bstep (se 1 (by rfl) ⟨8405099, by rfl⟩ : syracuseStep 11206799 = 16810199) B16810199
theorem B765747431 : Blo 1725063 765747431 := bstep (se 1 (by rfl) ⟨574310573, by rfl⟩ : syracuseStep 765747431 = 1148621147) B1148621147
theorem B3883499 : Blo 1725063 3883499 := bstep (se 1 (by rfl) ⟨2912624, by rfl⟩ : syracuseStep 3883499 = 5825249) B5825249
theorem B11059901 : Blo 1725063 11059901 := bstep (se 3 (by rfl) ⟨2073731, by rfl⟩ : syracuseStep 11059901 = 4147463) B4147463
theorem B3884687 : Blo 1725063 3884687 := bstep (se 1 (by rfl) ⟨2913515, by rfl⟩ : syracuseStep 3884687 = 5827031) B5827031
theorem B3884777 : Blo 1725063 3884777 := bstep (se 2 (by rfl) ⟨1456791, by rfl⟩ : syracuseStep 3884777 = 2913583) B2913583
theorem B226961291 : Blo 1725063 226961291 := bstep (se 1 (by rfl) ⟨170220968, by rfl⟩ : syracuseStep 226961291 = 340441937) B340441937
theorem B8742815 : Blo 1725063 8742815 := bstep (se 1 (by rfl) ⟨6557111, by rfl⟩ : syracuseStep 8742815 = 13114223) B13114223
theorem B3885011 : Blo 1725063 3885011 := bstep (se 1 (by rfl) ⟨2913758, by rfl⟩ : syracuseStep 3885011 = 5827517) B5827517
theorem B12446423 : Blo 1725063 12446423 := bstep (se 1 (by rfl) ⟨9334817, by rfl⟩ : syracuseStep 12446423 = 18669635) B18669635
theorem B4148039 : Blo 1725063 4148039 := bstep (se 1 (by rfl) ⟨3111029, by rfl⟩ : syracuseStep 4148039 = 6222059) B6222059
theorem B33180617 : Blo 1725063 33180617 := bstep (se 2 (by rfl) ⟨12442731, by rfl⟩ : syracuseStep 33180617 = 24885463) B24885463
theorem B2911369 : Blo 1725063 2911369 := bstep (se 2 (by rfl) ⟨1091763, by rfl⟩ : syracuseStep 2911369 = 2183527) B2183527
theorem B9964691 : Blo 1725063 9964691 := bstep (se 1 (by rfl) ⟨7473518, by rfl⟩ : syracuseStep 9964691 = 14947037) B14947037
theorem B9833663 : Blo 1725063 9833663 := bstep (se 1 (by rfl) ⟨7375247, by rfl⟩ : syracuseStep 9833663 = 14750495) B14750495
theorem B1748827 : Blo 1725063 1748827 := bstep (se 1 (by rfl) ⟨1311620, by rfl⟩ : syracuseStep 1748827 = 2623241) B2623241
theorem B14741473 : Blo 1725063 14741473 := bstep (se 2 (by rfl) ⟨5528052, by rfl⟩ : syracuseStep 14741473 = 11056105) B11056105
theorem B53874953 : Blo 1725063 53874953 := bstep (se 2 (by rfl) ⟨20203107, by rfl⟩ : syracuseStep 53874953 = 40406215) B40406215
theorem B26948027 : Blo 1725063 26948027 := bstep (se 1 (by rfl) ⟨20211020, by rfl⟩ : syracuseStep 26948027 = 40422041) B40422041
theorem B8295041 : Blo 1725063 8295041 := bstep (se 2 (by rfl) ⟨3110640, by rfl⟩ : syracuseStep 8295041 = 6221281) B6221281
theorem B1725095 : Blo 1725063 1725095 := bstep (se 1 (by rfl) ⟨1293821, by rfl⟩ : syracuseStep 1725095 = 2587643) B2587643
theorem B1725183 : Blo 1725063 1725183 := bstep (se 1 (by rfl) ⟨1293887, by rfl⟩ : syracuseStep 1725183 = 2587775) B2587775
theorem B1725211 : Blo 1725063 1725211 := bstep (se 1 (by rfl) ⟨1293908, by rfl⟩ : syracuseStep 1725211 = 2587817) B2587817
theorem B1725215 : Blo 1725063 1725215 := bstep (se 1 (by rfl) ⟨1293911, by rfl⟩ : syracuseStep 1725215 = 2587823) B2587823
theorem B55980881 : Blo 1725063 55980881 := bstep (se 2 (by rfl) ⟨20992830, by rfl⟩ : syracuseStep 55980881 = 41985661) B41985661
theorem B33182621 : Blo 1725063 33182621 := bstep (se 3 (by rfl) ⟨6221741, by rfl⟩ : syracuseStep 33182621 = 12443483) B12443483
theorem B33174467 : Blo 1725063 33174467 := bstep (se 1 (by rfl) ⟨24880850, by rfl⟩ : syracuseStep 33174467 = 49761701) B49761701
theorem B1725487 : Blo 1725063 1725487 := bstep (se 1 (by rfl) ⟨1294115, by rfl⟩ : syracuseStep 1725487 = 2588231) B2588231
theorem B1725979 : Blo 1725063 1725979 := bstep (se 1 (by rfl) ⟨1294484, by rfl⟩ : syracuseStep 1725979 = 2588969) B2588969
theorem B1121252939 : Blo 1725063 1121252939 := bstep (se 1 (by rfl) ⟨840939704, by rfl⟩ : syracuseStep 1121252939 = 1681879409) B1681879409
theorem B5822171 : Blo 1725063 5822171 := bstep (se 1 (by rfl) ⟨4366628, by rfl⟩ : syracuseStep 5822171 = 8733257) B8733257
theorem B29480759 : Blo 1725063 29480759 := bstep (se 1 (by rfl) ⟨22110569, by rfl⟩ : syracuseStep 29480759 = 44221139) B44221139
theorem B9967439 : Blo 1725063 9967439 := bstep (se 1 (by rfl) ⟨7475579, by rfl⟩ : syracuseStep 9967439 = 14951159) B14951159
theorem B1726319 : Blo 1725063 1726319 := bstep (se 1 (by rfl) ⟨1294739, by rfl⟩ : syracuseStep 1726319 = 2589479) B2589479
theorem B1726375 : Blo 1725063 1726375 := bstep (se 1 (by rfl) ⟨1294781, by rfl⟩ : syracuseStep 1726375 = 2589563) B2589563
theorem B35903407 : Blo 1725063 35903407 := bstep (se 1 (by rfl) ⟨26927555, by rfl⟩ : syracuseStep 35903407 = 53855111) B53855111
theorem B1726463 : Blo 1725063 1726463 := bstep (se 1 (by rfl) ⟨1294847, by rfl⟩ : syracuseStep 1726463 = 2589695) B2589695
theorem B1726575 : Blo 1725063 1726575 := bstep (se 1 (by rfl) ⟨1294931, by rfl⟩ : syracuseStep 1726575 = 2589863) B2589863
theorem B1726703 : Blo 1725063 1726703 := bstep (se 1 (by rfl) ⟨1295027, by rfl⟩ : syracuseStep 1726703 = 2590055) B2590055
theorem B8861935 : Blo 1725063 8861935 := bstep (se 1 (by rfl) ⟨6646451, by rfl⟩ : syracuseStep 8861935 = 13292903) B13292903
theorem B2587625 : Blo 1725063 2587625 := bstep (se 2 (by rfl) ⟨970359, by rfl⟩ : syracuseStep 2587625 = 1940719) B1940719
theorem B2587703 : Blo 1725063 2587703 := bstep (se 1 (by rfl) ⟨1940777, by rfl⟩ : syracuseStep 2587703 = 3881555) B3881555
theorem B102227255 : Blo 1725063 102227255 := bstep (se 1 (by rfl) ⟨76670441, by rfl⟩ : syracuseStep 102227255 = 153340883) B153340883
theorem B2587967 : Blo 1725063 2587967 := bstep (se 1 (by rfl) ⟨1940975, by rfl⟩ : syracuseStep 2587967 = 3881951) B3881951
theorem B8297923 : Blo 1725063 8297923 := bstep (se 1 (by rfl) ⟨6223442, by rfl⟩ : syracuseStep 8297923 = 12446885) B12446885
theorem B2588201 : Blo 1725063 2588201 := bstep (se 2 (by rfl) ⟨970575, by rfl⟩ : syracuseStep 2588201 = 1941151) B1941151
theorem B7872167 : Blo 1725063 7872167 := bstep (se 1 (by rfl) ⟨5904125, by rfl⟩ : syracuseStep 7872167 = 11808251) B11808251
theorem B26566343 : Blo 1725063 26566343 := bstep (se 1 (by rfl) ⟨19924757, by rfl⟩ : syracuseStep 26566343 = 39849515) B39849515
theorem B21290795 : Blo 1725063 21290795 := bstep (se 1 (by rfl) ⟨15968096, by rfl⟩ : syracuseStep 21290795 = 31936193) B31936193
theorem B2588543 : Blo 1725063 2588543 := bstep (se 1 (by rfl) ⟨1941407, by rfl⟩ : syracuseStep 2588543 = 3882815) B3882815
theorem B7471199 : Blo 1725063 7471199 := bstep (se 1 (by rfl) ⟨5603399, by rfl⟩ : syracuseStep 7471199 = 11206799) B11206799
theorem B17965351 : Blo 1725063 17965351 := bstep (se 1 (by rfl) ⟨13474013, by rfl⟩ : syracuseStep 17965351 = 26948027) B26948027
theorem B2588999 : Blo 1725063 2588999 := bstep (se 1 (by rfl) ⟨1941749, by rfl⟩ : syracuseStep 2588999 = 3883499) B3883499
theorem B5530027 : Blo 1725063 5530027 := bstep (se 1 (by rfl) ⟨4147520, by rfl⟩ : syracuseStep 5530027 = 8295041) B8295041
theorem B7373267 : Blo 1725063 7373267 := bstep (se 1 (by rfl) ⟨5529950, by rfl⟩ : syracuseStep 7373267 = 11059901) B11059901
theorem B2589791 : Blo 1725063 2589791 := bstep (se 1 (by rfl) ⟨1942343, by rfl⟩ : syracuseStep 2589791 = 3884687) B3884687
theorem B2589851 : Blo 1725063 2589851 := bstep (se 1 (by rfl) ⟨1942388, by rfl⟩ : syracuseStep 2589851 = 3884777) B3884777
theorem B19653839 : Blo 1725063 19653839 := bstep (se 1 (by rfl) ⟨14740379, by rfl⟩ : syracuseStep 19653839 = 29480759) B29480759
theorem B6644959 : Blo 1725063 6644959 := bstep (se 1 (by rfl) ⟨4983719, by rfl⟩ : syracuseStep 6644959 = 9967439) B9967439
theorem B151307527 : Blo 1725063 151307527 := bstep (se 1 (by rfl) ⟨113480645, by rfl⟩ : syracuseStep 151307527 = 226961291) B226961291
theorem B2590007 : Blo 1725063 2590007 := bstep (se 1 (by rfl) ⟨1942505, by rfl⟩ : syracuseStep 2590007 = 3885011) B3885011
theorem B22120411 : Blo 1725063 22120411 := bstep (se 1 (by rfl) ⟨16590308, by rfl⟩ : syracuseStep 22120411 = 33180617) B33180617
theorem B6555775 : Blo 1725063 6555775 := bstep (se 1 (by rfl) ⟨4916831, by rfl⟩ : syracuseStep 6555775 = 9833663) B9833663
theorem B68151503 : Blo 1725063 68151503 := bstep (se 1 (by rfl) ⟨51113627, by rfl⟩ : syracuseStep 68151503 = 102227255) B102227255
theorem B19655297 : Blo 1725063 19655297 := bstep (se 2 (by rfl) ⟨7370736, by rfl⟩ : syracuseStep 19655297 = 14741473) B14741473
theorem B35916635 : Blo 1725063 35916635 := bstep (se 1 (by rfl) ⟨26937476, by rfl⟩ : syracuseStep 35916635 = 53874953) B53874953
theorem B11815913 : Blo 1725063 11815913 := bstep (se 2 (by rfl) ⟨4430967, by rfl⟩ : syracuseStep 11815913 = 8861935) B8861935
theorem B22121747 : Blo 1725063 22121747 := bstep (se 1 (by rfl) ⟨16591310, by rfl⟩ : syracuseStep 22121747 = 33182621) B33182621
theorem B5828543 : Blo 1725063 5828543 := bstep (se 1 (by rfl) ⟨4371407, by rfl⟩ : syracuseStep 5828543 = 8742815) B8742815
theorem B20992445 : Blo 1725063 20992445 := bstep (se 3 (by rfl) ⟨3936083, by rfl⟩ : syracuseStep 20992445 = 7872167) B7872167
theorem B9327077 : Blo 1725063 9327077 := bstep (se 4 (by rfl) ⟨874413, by rfl⟩ : syracuseStep 9327077 = 1748827) B1748827
theorem B2765359 : Blo 1725063 2765359 := bstep (se 1 (by rfl) ⟨2074019, by rfl⟩ : syracuseStep 2765359 = 4148039) B4148039
theorem B11063897 : Blo 1725063 11063897 := bstep (se 2 (by rfl) ⟨4148961, by rfl⟩ : syracuseStep 11063897 = 8297923) B8297923
theorem B1725083 : Blo 1725063 1725083 := bstep (se 1 (by rfl) ⟨1293812, by rfl⟩ : syracuseStep 1725083 = 2587625) B2587625
theorem B1725135 : Blo 1725063 1725135 := bstep (se 1 (by rfl) ⟨1293851, by rfl⟩ : syracuseStep 1725135 = 2587703) B2587703
theorem B1725311 : Blo 1725063 1725311 := bstep (se 1 (by rfl) ⟨1293983, by rfl⟩ : syracuseStep 1725311 = 2587967) B2587967
theorem B1725467 : Blo 1725063 1725467 := bstep (se 1 (by rfl) ⟨1294100, by rfl⟩ : syracuseStep 1725467 = 2588201) B2588201
theorem B14193863 : Blo 1725063 14193863 := bstep (se 1 (by rfl) ⟨10645397, by rfl⟩ : syracuseStep 14193863 = 21290795) B21290795
theorem B47871209 : Blo 1725063 47871209 := bstep (se 2 (by rfl) ⟨17951703, by rfl⟩ : syracuseStep 47871209 = 35903407) B35903407
theorem B1725695 : Blo 1725063 1725695 := bstep (se 1 (by rfl) ⟨1294271, by rfl⟩ : syracuseStep 1725695 = 2588543) B2588543
theorem B510498287 : Blo 1725063 510498287 := bstep (se 1 (by rfl) ⟨382873715, by rfl⟩ : syracuseStep 510498287 = 765747431) B765747431
theorem B37320587 : Blo 1725063 37320587 := bstep (se 1 (by rfl) ⟨27990440, by rfl⟩ : syracuseStep 37320587 = 55980881) B55980881
theorem B22116311 : Blo 1725063 22116311 := bstep (se 1 (by rfl) ⟨16587233, by rfl⟩ : syracuseStep 22116311 = 33174467) B33174467
theorem B747501959 : Blo 1725063 747501959 := bstep (se 1 (by rfl) ⟨560626469, by rfl⟩ : syracuseStep 747501959 = 1121252939) B1121252939
theorem B3881447 : Blo 1725063 3881447 := bstep (se 1 (by rfl) ⟨2911085, by rfl⟩ : syracuseStep 3881447 = 5822171) B5822171
theorem B3881825 : Blo 1725063 3881825 := bstep (se 2 (by rfl) ⟨1455684, by rfl⟩ : syracuseStep 3881825 = 2911369) B2911369
theorem B8297615 : Blo 1725063 8297615 := bstep (se 1 (by rfl) ⟨6223211, by rfl⟩ : syracuseStep 8297615 = 12446423) B12446423
theorem B6643127 : Blo 1725063 6643127 := bstep (se 1 (by rfl) ⟨4982345, by rfl⟩ : syracuseStep 6643127 = 9964691) B9964691
theorem B17710895 : Blo 1725063 17710895 := bstep (se 1 (by rfl) ⟨13283171, by rfl⟩ : syracuseStep 17710895 = 26566343) B26566343
theorem B4980799 : Blo 1725063 4980799 := bstep (se 1 (by rfl) ⟨3735599, by rfl⟩ : syracuseStep 4980799 = 7471199) B7471199
theorem B8741033 : Blo 1725063 8741033 := bstep (se 2 (by rfl) ⟨3277887, by rfl⟩ : syracuseStep 8741033 = 6555775) B6555775
theorem B4915511 : Blo 1725063 4915511 := bstep (se 1 (by rfl) ⟨3686633, by rfl⟩ : syracuseStep 4915511 = 7373267) B7373267
theorem B6218051 : Blo 1725063 6218051 := bstep (se 1 (by rfl) ⟨4663538, by rfl⟩ : syracuseStep 6218051 = 9327077) B9327077
theorem B23953801 : Blo 1725063 23953801 := bstep (se 2 (by rfl) ⟨8982675, by rfl⟩ : syracuseStep 23953801 = 17965351) B17965351
theorem B7373369 : Blo 1725063 7373369 := bstep (se 2 (by rfl) ⟨2765013, by rfl⟩ : syracuseStep 7373369 = 5530027) B5530027
theorem B127656557 : Blo 1725063 127656557 := bstep (se 3 (by rfl) ⟨23935604, by rfl⟩ : syracuseStep 127656557 = 47871209) B47871209
theorem B9462575 : Blo 1725063 9462575 := bstep (se 1 (by rfl) ⟨7096931, by rfl⟩ : syracuseStep 9462575 = 14193863) B14193863
theorem B35439781 : Blo 1725063 35439781 := bstep (se 4 (by rfl) ⟨3322479, by rfl⟩ : syracuseStep 35439781 = 6644959) B6644959
theorem B24880391 : Blo 1725063 24880391 := bstep (se 1 (by rfl) ⟨18660293, by rfl⟩ : syracuseStep 24880391 = 37320587) B37320587
theorem B5531743 : Blo 1725063 5531743 := bstep (se 1 (by rfl) ⟨4148807, by rfl⟩ : syracuseStep 5531743 = 8297615) B8297615
theorem B14747831 : Blo 1725063 14747831 := bstep (se 1 (by rfl) ⟨11060873, by rfl⟩ : syracuseStep 14747831 = 22121747) B22121747
theorem B11807263 : Blo 1725063 11807263 := bstep (se 1 (by rfl) ⟨8855447, by rfl⟩ : syracuseStep 11807263 = 17710895) B17710895
theorem B31509101 : Blo 1725063 31509101 := bstep (se 3 (by rfl) ⟨5907956, by rfl⟩ : syracuseStep 31509101 = 11815913) B11815913
theorem B29493881 : Blo 1725063 29493881 := bstep (se 2 (by rfl) ⟨11060205, by rfl⟩ : syracuseStep 29493881 = 22120411) B22120411
theorem B3885695 : Blo 1725063 3885695 := bstep (se 1 (by rfl) ⟨2914271, by rfl⟩ : syracuseStep 3885695 = 5828543) B5828543
theorem B14748581 : Blo 1725063 14748581 := bstep (se 4 (by rfl) ⟨1382679, by rfl⟩ : syracuseStep 14748581 = 2765359) B2765359
theorem B13994963 : Blo 1725063 13994963 := bstep (se 1 (by rfl) ⟨10496222, by rfl⟩ : syracuseStep 13994963 = 20992445) B20992445
theorem B7375931 : Blo 1725063 7375931 := bstep (se 1 (by rfl) ⟨5531948, by rfl⟩ : syracuseStep 7375931 = 11063897) B11063897
theorem B13102559 : Blo 1725063 13102559 := bstep (se 1 (by rfl) ⟨9826919, by rfl⟩ : syracuseStep 13102559 = 19653839) B19653839
theorem B340332191 : Blo 1725063 340332191 := bstep (se 1 (by rfl) ⟨255249143, by rfl⟩ : syracuseStep 340332191 = 510498287) B510498287
theorem B13103531 : Blo 1725063 13103531 := bstep (se 1 (by rfl) ⟨9827648, by rfl⟩ : syracuseStep 13103531 = 19655297) B19655297
theorem B4428751 : Blo 1725063 4428751 := bstep (se 1 (by rfl) ⟨3321563, by rfl⟩ : syracuseStep 4428751 = 6643127) B6643127
theorem B1725999 : Blo 1725063 1725999 := bstep (se 1 (by rfl) ⟨1294499, by rfl⟩ : syracuseStep 1725999 = 2588999) B2588999
theorem B181737341 : Blo 1725063 181737341 := bstep (se 3 (by rfl) ⟨34075751, by rfl⟩ : syracuseStep 181737341 = 68151503) B68151503
theorem B1726527 : Blo 1725063 1726527 := bstep (se 1 (by rfl) ⟨1294895, by rfl⟩ : syracuseStep 1726527 = 2589791) B2589791
theorem B1726567 : Blo 1725063 1726567 := bstep (se 1 (by rfl) ⟨1294925, by rfl⟩ : syracuseStep 1726567 = 2589851) B2589851
theorem B1726671 : Blo 1725063 1726671 := bstep (se 1 (by rfl) ⟨1295003, by rfl⟩ : syracuseStep 1726671 = 2590007) B2590007
theorem B14744207 : Blo 1725063 14744207 := bstep (se 1 (by rfl) ⟨11058155, by rfl⟩ : syracuseStep 14744207 = 22116311) B22116311
theorem B498334639 : Blo 1725063 498334639 := bstep (se 1 (by rfl) ⟨373750979, by rfl⟩ : syracuseStep 498334639 = 747501959) B747501959
theorem B2587631 : Blo 1725063 2587631 := bstep (se 1 (by rfl) ⟨1940723, by rfl⟩ : syracuseStep 2587631 = 3881447) B3881447
theorem B201743369 : Blo 1725063 201743369 := bstep (se 2 (by rfl) ⟨75653763, by rfl⟩ : syracuseStep 201743369 = 151307527) B151307527
theorem B23944423 : Blo 1725063 23944423 := bstep (se 1 (by rfl) ⟨17958317, by rfl⟩ : syracuseStep 23944423 = 35916635) B35916635
theorem B2587883 : Blo 1725063 2587883 := bstep (se 1 (by rfl) ⟨1940912, by rfl⟩ : syracuseStep 2587883 = 3881825) B3881825
theorem B3277007 : Blo 1725063 3277007 := bstep (se 1 (by rfl) ⟨2457755, by rfl⟩ : syracuseStep 3277007 = 4915511) B4915511
theorem B4915579 : Blo 1725063 4915579 := bstep (se 1 (by rfl) ⟨3686684, by rfl⟩ : syracuseStep 4915579 = 7373369) B7373369
theorem B6308383 : Blo 1725063 6308383 := bstep (se 1 (by rfl) ⟨4731287, by rfl⟩ : syracuseStep 6308383 = 9462575) B9462575
theorem B16581469 : Blo 1725063 16581469 := bstep (se 3 (by rfl) ⟨3109025, by rfl⟩ : syracuseStep 16581469 = 6218051) B6218051
theorem B664446185 : Blo 1725063 664446185 := bstep (se 2 (by rfl) ⟨249167319, by rfl⟩ : syracuseStep 664446185 = 498334639) B498334639
theorem B9831887 : Blo 1725063 9831887 := bstep (se 1 (by rfl) ⟨7373915, by rfl⟩ : syracuseStep 9831887 = 14747831) B14747831
theorem B47253041 : Blo 1725063 47253041 := bstep (se 2 (by rfl) ⟨17719890, by rfl⟩ : syracuseStep 47253041 = 35439781) B35439781
theorem B31925897 : Blo 1725063 31925897 := bstep (se 2 (by rfl) ⟨11972211, by rfl⟩ : syracuseStep 31925897 = 23944423) B23944423
theorem B21006067 : Blo 1725063 21006067 := bstep (se 1 (by rfl) ⟨15754550, by rfl⟩ : syracuseStep 21006067 = 31509101) B31509101
theorem B19662587 : Blo 1725063 19662587 := bstep (se 1 (by rfl) ⟨14746940, by rfl⟩ : syracuseStep 19662587 = 29493881) B29493881
theorem B2590463 : Blo 1725063 2590463 := bstep (se 1 (by rfl) ⟨1942847, by rfl⟩ : syracuseStep 2590463 = 3885695) B3885695
theorem B9832387 : Blo 1725063 9832387 := bstep (se 1 (by rfl) ⟨7374290, by rfl⟩ : syracuseStep 9832387 = 14748581) B14748581
theorem B4917287 : Blo 1725063 4917287 := bstep (se 1 (by rfl) ⟨3687965, by rfl⟩ : syracuseStep 4917287 = 7375931) B7375931
theorem B8735039 : Blo 1725063 8735039 := bstep (se 1 (by rfl) ⟨6551279, by rfl⟩ : syracuseStep 8735039 = 13102559) B13102559
theorem B226888127 : Blo 1725063 226888127 := bstep (se 1 (by rfl) ⟨170166095, by rfl⟩ : syracuseStep 226888127 = 340332191) B340332191
theorem B5827355 : Blo 1725063 5827355 := bstep (se 1 (by rfl) ⟨4370516, by rfl⟩ : syracuseStep 5827355 = 8741033) B8741033
theorem B8735687 : Blo 1725063 8735687 := bstep (se 1 (by rfl) ⟨6551765, by rfl⟩ : syracuseStep 8735687 = 13103531) B13103531
theorem B29502629 : Blo 1725063 29502629 := bstep (se 4 (by rfl) ⟨2765871, by rfl⟩ : syracuseStep 29502629 = 5531743) B5531743
theorem B1725087 : Blo 1725063 1725087 := bstep (se 1 (by rfl) ⟨1293815, by rfl⟩ : syracuseStep 1725087 = 2587631) B2587631
theorem B1725255 : Blo 1725063 1725255 := bstep (se 1 (by rfl) ⟨1293941, by rfl⟩ : syracuseStep 1725255 = 2587883) B2587883
theorem B6641065 : Blo 1725063 6641065 := bstep (se 2 (by rfl) ⟨2490399, by rfl⟩ : syracuseStep 6641065 = 4980799) B4980799
theorem B85104371 : Blo 1725063 85104371 := bstep (se 1 (by rfl) ⟨63828278, by rfl⟩ : syracuseStep 85104371 = 127656557) B127656557
theorem B31938401 : Blo 1725063 31938401 := bstep (se 2 (by rfl) ⟨11976900, by rfl⟩ : syracuseStep 31938401 = 23953801) B23953801
theorem B15743017 : Blo 1725063 15743017 := bstep (se 2 (by rfl) ⟨5903631, by rfl⟩ : syracuseStep 15743017 = 11807263) B11807263
theorem B16586927 : Blo 1725063 16586927 := bstep (se 1 (by rfl) ⟨12440195, by rfl⟩ : syracuseStep 16586927 = 24880391) B24880391
theorem B121158227 : Blo 1725063 121158227 := bstep (se 1 (by rfl) ⟨90868670, by rfl⟩ : syracuseStep 121158227 = 181737341) B181737341
theorem B5905001 : Blo 1725063 5905001 := bstep (se 2 (by rfl) ⟨2214375, by rfl⟩ : syracuseStep 5905001 = 4428751) B4428751
theorem B9829471 : Blo 1725063 9829471 := bstep (se 1 (by rfl) ⟨7372103, by rfl⟩ : syracuseStep 9829471 = 14744207) B14744207
theorem B9329975 : Blo 1725063 9329975 := bstep (se 1 (by rfl) ⟨6997481, by rfl⟩ : syracuseStep 9329975 = 13994963) B13994963
theorem B134495579 : Blo 1725063 134495579 := bstep (se 1 (by rfl) ⟨100871684, by rfl⟩ : syracuseStep 134495579 = 201743369) B201743369
theorem B6554105 : Blo 1725063 6554105 := bstep (se 2 (by rfl) ⟨2457789, by rfl⟩ : syracuseStep 6554105 = 4915579) B4915579
theorem B6554591 : Blo 1725063 6554591 := bstep (se 1 (by rfl) ⟨4915943, by rfl⟩ : syracuseStep 6554591 = 9831887) B9831887
theorem B21283931 : Blo 1725063 21283931 := bstep (se 1 (by rfl) ⟨15962948, by rfl⟩ : syracuseStep 21283931 = 31925897) B31925897
theorem B13108391 : Blo 1725063 13108391 := bstep (se 1 (by rfl) ⟨9831293, by rfl⟩ : syracuseStep 13108391 = 19662587) B19662587
theorem B21292267 : Blo 1725063 21292267 := bstep (se 1 (by rfl) ⟨15969200, by rfl⟩ : syracuseStep 21292267 = 31938401) B31938401
theorem B151258751 : Blo 1725063 151258751 := bstep (se 1 (by rfl) ⟨113444063, by rfl⟩ : syracuseStep 151258751 = 226888127) B226888127
theorem B3884903 : Blo 1725063 3884903 := bstep (se 1 (by rfl) ⟨2913677, by rfl⟩ : syracuseStep 3884903 = 5827355) B5827355
theorem B6219983 : Blo 1725063 6219983 := bstep (se 1 (by rfl) ⟨4664987, by rfl⟩ : syracuseStep 6219983 = 9329975) B9329975
theorem B89663719 : Blo 1725063 89663719 := bstep (se 1 (by rfl) ⟨67247789, by rfl⟩ : syracuseStep 89663719 = 134495579) B134495579
theorem B13109849 : Blo 1725063 13109849 := bstep (se 2 (by rfl) ⟨4916193, by rfl⟩ : syracuseStep 13109849 = 9832387) B9832387
theorem B83962757 : Blo 1725063 83962757 := bstep (se 4 (by rfl) ⟨7871508, by rfl⟩ : syracuseStep 83962757 = 15743017) B15743017
theorem B31502027 : Blo 1725063 31502027 := bstep (se 1 (by rfl) ⟨23626520, by rfl⟩ : syracuseStep 31502027 = 47253041) B47253041
theorem B3936667 : Blo 1725063 3936667 := bstep (se 1 (by rfl) ⟨2952500, by rfl⟩ : syracuseStep 3936667 = 5905001) B5905001
theorem B13112765 : Blo 1725063 13112765 := bstep (se 3 (by rfl) ⟨2458643, by rfl⟩ : syracuseStep 13112765 = 4917287) B4917287
theorem B2184671 : Blo 1725063 2184671 := bstep (se 1 (by rfl) ⟨1638503, by rfl⟩ : syracuseStep 2184671 = 3277007) B3277007
theorem B8411177 : Blo 1725063 8411177 := bstep (se 2 (by rfl) ⟨3154191, by rfl⟩ : syracuseStep 8411177 = 6308383) B6308383
theorem B442964123 : Blo 1725063 442964123 := bstep (se 1 (by rfl) ⟨332223092, by rfl⟩ : syracuseStep 442964123 = 664446185) B664446185
theorem B22108625 : Blo 1725063 22108625 := bstep (se 2 (by rfl) ⟨8290734, by rfl⟩ : syracuseStep 22108625 = 16581469) B16581469
theorem B56736247 : Blo 1725063 56736247 := bstep (se 1 (by rfl) ⟨42552185, by rfl⟩ : syracuseStep 56736247 = 85104371) B85104371
theorem B1726975 : Blo 1725063 1726975 := bstep (se 1 (by rfl) ⟨1295231, by rfl⟩ : syracuseStep 1726975 = 2590463) B2590463
theorem B11057951 : Blo 1725063 11057951 := bstep (se 1 (by rfl) ⟨8293463, by rfl⟩ : syracuseStep 11057951 = 16586927) B16586927
theorem B13105961 : Blo 1725063 13105961 := bstep (se 2 (by rfl) ⟨4914735, by rfl⟩ : syracuseStep 13105961 = 9829471) B9829471
theorem B5823359 : Blo 1725063 5823359 := bstep (se 1 (by rfl) ⟨4367519, by rfl⟩ : syracuseStep 5823359 = 8735039) B8735039
theorem B80772151 : Blo 1725063 80772151 := bstep (se 1 (by rfl) ⟨60579113, by rfl⟩ : syracuseStep 80772151 = 121158227) B121158227
theorem B8854753 : Blo 1725063 8854753 := bstep (se 2 (by rfl) ⟨3320532, by rfl⟩ : syracuseStep 8854753 = 6641065) B6641065
theorem B5823791 : Blo 1725063 5823791 := bstep (se 1 (by rfl) ⟨4367843, by rfl⟩ : syracuseStep 5823791 = 8735687) B8735687
theorem B19668419 : Blo 1725063 19668419 := bstep (se 1 (by rfl) ⟨14751314, by rfl⟩ : syracuseStep 19668419 = 29502629) B29502629
theorem B28008089 : Blo 1725063 28008089 := bstep (se 2 (by rfl) ⟨10503033, by rfl⟩ : syracuseStep 28008089 = 21006067) B21006067
theorem B14189287 : Blo 1725063 14189287 := bstep (se 1 (by rfl) ⟨10641965, by rfl⟩ : syracuseStep 14189287 = 21283931) B21283931
theorem B8741843 : Blo 1725063 8741843 := bstep (se 1 (by rfl) ⟨6556382, by rfl⟩ : syracuseStep 8741843 = 13112765) B13112765
theorem B2589935 : Blo 1725063 2589935 := bstep (se 1 (by rfl) ⟨1942451, by rfl⟩ : syracuseStep 2589935 = 3884903) B3884903
theorem B5825789 : Blo 1725063 5825789 := bstep (se 3 (by rfl) ⟨1092335, by rfl⟩ : syracuseStep 5825789 = 2184671) B2184671
theorem B4146655 : Blo 1725063 4146655 := bstep (se 1 (by rfl) ⟨3109991, by rfl⟩ : syracuseStep 4146655 = 6219983) B6219983
theorem B11806337 : Blo 1725063 11806337 := bstep (se 2 (by rfl) ⟨4427376, by rfl⟩ : syracuseStep 11806337 = 8854753) B8854753
theorem B14739083 : Blo 1725063 14739083 := bstep (se 1 (by rfl) ⟨11054312, by rfl⟩ : syracuseStep 14739083 = 22108625) B22108625
theorem B18672059 : Blo 1725063 18672059 := bstep (se 1 (by rfl) ⟨14004044, by rfl⟩ : syracuseStep 18672059 = 28008089) B28008089
theorem B4369403 : Blo 1725063 4369403 := bstep (se 1 (by rfl) ⟨3277052, by rfl⟩ : syracuseStep 4369403 = 6554105) B6554105
theorem B4369727 : Blo 1725063 4369727 := bstep (se 1 (by rfl) ⟨3277295, by rfl⟩ : syracuseStep 4369727 = 6554591) B6554591
theorem B75648329 : Blo 1725063 75648329 := bstep (se 2 (by rfl) ⟨28368123, by rfl⟩ : syracuseStep 75648329 = 56736247) B56736247
theorem B100839167 : Blo 1725063 100839167 := bstep (se 1 (by rfl) ⟨75629375, by rfl⟩ : syracuseStep 100839167 = 151258751) B151258751
theorem B5607451 : Blo 1725063 5607451 := bstep (se 1 (by rfl) ⟨4205588, by rfl⟩ : syracuseStep 5607451 = 8411177) B8411177
theorem B107696201 : Blo 1725063 107696201 := bstep (se 2 (by rfl) ⟨40386075, by rfl⟩ : syracuseStep 107696201 = 80772151) B80772151
theorem B295309415 : Blo 1725063 295309415 := bstep (se 1 (by rfl) ⟨221482061, by rfl⟩ : syracuseStep 295309415 = 442964123) B442964123
theorem B28389689 : Blo 1725063 28389689 := bstep (se 2 (by rfl) ⟨10646133, by rfl⟩ : syracuseStep 28389689 = 21292267) B21292267
theorem B8737307 : Blo 1725063 8737307 := bstep (se 1 (by rfl) ⟨6552980, by rfl⟩ : syracuseStep 8737307 = 13105961) B13105961
theorem B13112279 : Blo 1725063 13112279 := bstep (se 1 (by rfl) ⟨9834209, by rfl⟩ : syracuseStep 13112279 = 19668419) B19668419
theorem B21001351 : Blo 1725063 21001351 := bstep (se 1 (by rfl) ⟨15751013, by rfl⟩ : syracuseStep 21001351 = 31502027) B31502027
theorem B119551625 : Blo 1725063 119551625 := bstep (se 2 (by rfl) ⟨44831859, by rfl⟩ : syracuseStep 119551625 = 89663719) B89663719
theorem B5248889 : Blo 1725063 5248889 := bstep (se 2 (by rfl) ⟨1968333, by rfl⟩ : syracuseStep 5248889 = 3936667) B3936667
theorem B8738927 : Blo 1725063 8738927 := bstep (se 1 (by rfl) ⟨6554195, by rfl⟩ : syracuseStep 8738927 = 13108391) B13108391
theorem B8739899 : Blo 1725063 8739899 := bstep (se 1 (by rfl) ⟨6554924, by rfl⟩ : syracuseStep 8739899 = 13109849) B13109849
theorem B7371967 : Blo 1725063 7371967 := bstep (se 1 (by rfl) ⟨5528975, by rfl⟩ : syracuseStep 7371967 = 11057951) B11057951
theorem B3882239 : Blo 1725063 3882239 := bstep (se 1 (by rfl) ⟨2911679, by rfl⟩ : syracuseStep 3882239 = 5823359) B5823359
theorem B55975171 : Blo 1725063 55975171 := bstep (se 1 (by rfl) ⟨41981378, by rfl⟩ : syracuseStep 55975171 = 83962757) B83962757
theorem B3882527 : Blo 1725063 3882527 := bstep (se 1 (by rfl) ⟨2911895, by rfl⟩ : syracuseStep 3882527 = 5823791) B5823791
theorem B5824871 : Blo 1725063 5824871 := bstep (se 1 (by rfl) ⟨4368653, by rfl⟩ : syracuseStep 5824871 = 8737307) B8737307
theorem B8741519 : Blo 1725063 8741519 := bstep (se 1 (by rfl) ⟨6556139, by rfl⟩ : syracuseStep 8741519 = 13112279) B13112279
theorem B3883859 : Blo 1725063 3883859 := bstep (se 1 (by rfl) ⟨2912894, by rfl⟩ : syracuseStep 3883859 = 5825789) B5825789
theorem B79701083 : Blo 1725063 79701083 := bstep (se 1 (by rfl) ⟨59775812, by rfl⟩ : syracuseStep 79701083 = 119551625) B119551625
theorem B3499259 : Blo 1725063 3499259 := bstep (se 1 (by rfl) ⟨2624444, by rfl⟩ : syracuseStep 3499259 = 5248889) B5248889
theorem B5825951 : Blo 1725063 5825951 := bstep (se 1 (by rfl) ⟨4369463, by rfl⟩ : syracuseStep 5825951 = 8738927) B8738927
theorem B28001801 : Blo 1725063 28001801 := bstep (se 2 (by rfl) ⟨10500675, by rfl⟩ : syracuseStep 28001801 = 21001351) B21001351
theorem B5826599 : Blo 1725063 5826599 := bstep (se 1 (by rfl) ⟨4369949, by rfl⟩ : syracuseStep 5826599 = 8739899) B8739899
theorem B50432219 : Blo 1725063 50432219 := bstep (se 1 (by rfl) ⟨37824164, by rfl⟩ : syracuseStep 50432219 = 75648329) B75648329
theorem B67226111 : Blo 1725063 67226111 := bstep (se 1 (by rfl) ⟨50419583, by rfl⟩ : syracuseStep 67226111 = 100839167) B100839167
theorem B196872943 : Blo 1725063 196872943 := bstep (se 1 (by rfl) ⟨147654707, by rfl⟩ : syracuseStep 196872943 = 295309415) B295309415
theorem B287189869 : Blo 1725063 287189869 := bstep (se 3 (by rfl) ⟨53848100, by rfl⟩ : syracuseStep 287189869 = 107696201) B107696201
theorem B18926459 : Blo 1725063 18926459 := bstep (se 1 (by rfl) ⟨14194844, by rfl⟩ : syracuseStep 18926459 = 28389689) B28389689
theorem B5827895 : Blo 1725063 5827895 := bstep (se 1 (by rfl) ⟨4370921, by rfl⟩ : syracuseStep 5827895 = 8741843) B8741843
theorem B18919049 : Blo 1725063 18919049 := bstep (se 2 (by rfl) ⟨7094643, by rfl⟩ : syracuseStep 18919049 = 14189287) B14189287
theorem B9826055 : Blo 1725063 9826055 := bstep (se 1 (by rfl) ⟨7369541, by rfl⟩ : syracuseStep 9826055 = 14739083) B14739083
theorem B12448039 : Blo 1725063 12448039 := bstep (se 1 (by rfl) ⟨9336029, by rfl⟩ : syracuseStep 12448039 = 18672059) B18672059
theorem B74633561 : Blo 1725063 74633561 := bstep (se 2 (by rfl) ⟨27987585, by rfl⟩ : syracuseStep 74633561 = 55975171) B55975171
theorem B2912935 : Blo 1725063 2912935 := bstep (se 1 (by rfl) ⟨2184701, by rfl⟩ : syracuseStep 2912935 = 4369403) B4369403
theorem B2913151 : Blo 1725063 2913151 := bstep (se 1 (by rfl) ⟨2184863, by rfl⟩ : syracuseStep 2913151 = 4369727) B4369727
theorem B29906405 : Blo 1725063 29906405 := bstep (se 4 (by rfl) ⟨2803725, by rfl⟩ : syracuseStep 29906405 = 5607451) B5607451
theorem B1726623 : Blo 1725063 1726623 := bstep (se 1 (by rfl) ⟨1294967, by rfl⟩ : syracuseStep 1726623 = 2589935) B2589935
theorem B7870891 : Blo 1725063 7870891 := bstep (se 1 (by rfl) ⟨5903168, by rfl⟩ : syracuseStep 7870891 = 11806337) B11806337
theorem B9829289 : Blo 1725063 9829289 := bstep (se 2 (by rfl) ⟨3685983, by rfl⟩ : syracuseStep 9829289 = 7371967) B7371967
theorem B5528873 : Blo 1725063 5528873 := bstep (se 2 (by rfl) ⟨2073327, by rfl⟩ : syracuseStep 5528873 = 4146655) B4146655
theorem B2588159 : Blo 1725063 2588159 := bstep (se 1 (by rfl) ⟨1941119, by rfl⟩ : syracuseStep 2588159 = 3882239) B3882239
theorem B2588351 : Blo 1725063 2588351 := bstep (se 1 (by rfl) ⟨1941263, by rfl⟩ : syracuseStep 2588351 = 3882527) B3882527
theorem B3883247 : Blo 1725063 3883247 := bstep (se 1 (by rfl) ⟨2912435, by rfl⟩ : syracuseStep 3883247 = 5824871) B5824871
theorem B16597385 : Blo 1725063 16597385 := bstep (se 2 (by rfl) ⟨6224019, by rfl⟩ : syracuseStep 16597385 = 12448039) B12448039
theorem B2589239 : Blo 1725063 2589239 := bstep (se 1 (by rfl) ⟨1941929, by rfl⟩ : syracuseStep 2589239 = 3883859) B3883859
theorem B10494521 : Blo 1725063 10494521 := bstep (se 2 (by rfl) ⟨3935445, by rfl⟩ : syracuseStep 10494521 = 7870891) B7870891
theorem B9331357 : Blo 1725063 9331357 := bstep (se 3 (by rfl) ⟨1749629, by rfl⟩ : syracuseStep 9331357 = 3499259) B3499259
theorem B53134055 : Blo 1725063 53134055 := bstep (se 1 (by rfl) ⟨39850541, by rfl⟩ : syracuseStep 53134055 = 79701083) B79701083
theorem B3883913 : Blo 1725063 3883913 := bstep (se 2 (by rfl) ⟨1456467, by rfl⟩ : syracuseStep 3883913 = 2912935) B2912935
theorem B3883967 : Blo 1725063 3883967 := bstep (se 1 (by rfl) ⟨2912975, by rfl⟩ : syracuseStep 3883967 = 5825951) B5825951
theorem B262497257 : Blo 1725063 262497257 := bstep (se 2 (by rfl) ⟨98436471, by rfl⟩ : syracuseStep 262497257 = 196872943) B196872943
theorem B382919825 : Blo 1725063 382919825 := bstep (se 2 (by rfl) ⟨143594934, by rfl⟩ : syracuseStep 382919825 = 287189869) B287189869
theorem B3884201 : Blo 1725063 3884201 := bstep (se 2 (by rfl) ⟨1456575, by rfl⟩ : syracuseStep 3884201 = 2913151) B2913151
theorem B3884399 : Blo 1725063 3884399 := bstep (se 1 (by rfl) ⟨2913299, by rfl⟩ : syracuseStep 3884399 = 5826599) B5826599
theorem B33621479 : Blo 1725063 33621479 := bstep (se 1 (by rfl) ⟨25216109, by rfl⟩ : syracuseStep 33621479 = 50432219) B50432219
theorem B12617639 : Blo 1725063 12617639 := bstep (se 1 (by rfl) ⟨9463229, by rfl⟩ : syracuseStep 12617639 = 18926459) B18926459
theorem B3885263 : Blo 1725063 3885263 := bstep (se 1 (by rfl) ⟨2913947, by rfl⟩ : syracuseStep 3885263 = 5827895) B5827895
theorem B5827679 : Blo 1725063 5827679 := bstep (se 1 (by rfl) ⟨4370759, by rfl⟩ : syracuseStep 5827679 = 8741519) B8741519
theorem B50450797 : Blo 1725063 50450797 := bstep (se 3 (by rfl) ⟨9459524, by rfl⟩ : syracuseStep 50450797 = 18919049) B18919049
theorem B1725439 : Blo 1725063 1725439 := bstep (se 1 (by rfl) ⟨1294079, by rfl⟩ : syracuseStep 1725439 = 2588159) B2588159
theorem B1725567 : Blo 1725063 1725567 := bstep (se 1 (by rfl) ⟨1294175, by rfl⟩ : syracuseStep 1725567 = 2588351) B2588351
theorem B6550703 : Blo 1725063 6550703 := bstep (se 1 (by rfl) ⟨4913027, by rfl⟩ : syracuseStep 6550703 = 9826055) B9826055
theorem B49755707 : Blo 1725063 49755707 := bstep (se 1 (by rfl) ⟨37316780, by rfl⟩ : syracuseStep 49755707 = 74633561) B74633561
theorem B19937603 : Blo 1725063 19937603 := bstep (se 1 (by rfl) ⟨14953202, by rfl⟩ : syracuseStep 19937603 = 29906405) B29906405
theorem B18667867 : Blo 1725063 18667867 := bstep (se 1 (by rfl) ⟨14000900, by rfl⟩ : syracuseStep 18667867 = 28001801) B28001801
theorem B44817407 : Blo 1725063 44817407 := bstep (se 1 (by rfl) ⟨33613055, by rfl⟩ : syracuseStep 44817407 = 67226111) B67226111
theorem B6552859 : Blo 1725063 6552859 := bstep (se 1 (by rfl) ⟨4914644, by rfl⟩ : syracuseStep 6552859 = 9829289) B9829289
theorem B3685915 : Blo 1725063 3685915 := bstep (se 1 (by rfl) ⟨2764436, by rfl⟩ : syracuseStep 3685915 = 5528873) B5528873
theorem B2588831 : Blo 1725063 2588831 := bstep (se 1 (by rfl) ⟨1941623, by rfl⟩ : syracuseStep 2588831 = 3883247) B3883247
theorem B6996347 : Blo 1725063 6996347 := bstep (se 1 (by rfl) ⟨5247260, by rfl⟩ : syracuseStep 6996347 = 10494521) B10494521
theorem B35422703 : Blo 1725063 35422703 := bstep (se 1 (by rfl) ⟨26567027, by rfl⟩ : syracuseStep 35422703 = 53134055) B53134055
theorem B2589275 : Blo 1725063 2589275 := bstep (se 1 (by rfl) ⟨1941956, by rfl⟩ : syracuseStep 2589275 = 3883913) B3883913
theorem B2589311 : Blo 1725063 2589311 := bstep (se 1 (by rfl) ⟨1941983, by rfl⟩ : syracuseStep 2589311 = 3883967) B3883967
theorem B174998171 : Blo 1725063 174998171 := bstep (se 1 (by rfl) ⟨131248628, by rfl⟩ : syracuseStep 174998171 = 262497257) B262497257
theorem B255279883 : Blo 1725063 255279883 := bstep (se 1 (by rfl) ⟨191459912, by rfl⟩ : syracuseStep 255279883 = 382919825) B382919825
theorem B2589467 : Blo 1725063 2589467 := bstep (se 1 (by rfl) ⟨1942100, by rfl⟩ : syracuseStep 2589467 = 3884201) B3884201
theorem B4367135 : Blo 1725063 4367135 := bstep (se 1 (by rfl) ⟨3275351, by rfl⟩ : syracuseStep 4367135 = 6550703) B6550703
theorem B53166941 : Blo 1725063 53166941 := bstep (se 3 (by rfl) ⟨9968801, by rfl⟩ : syracuseStep 53166941 = 19937603) B19937603
theorem B2589599 : Blo 1725063 2589599 := bstep (se 1 (by rfl) ⟨1942199, by rfl⟩ : syracuseStep 2589599 = 3884399) B3884399
theorem B22414319 : Blo 1725063 22414319 := bstep (se 1 (by rfl) ⟨16810739, by rfl⟩ : syracuseStep 22414319 = 33621479) B33621479
theorem B33170471 : Blo 1725063 33170471 := bstep (se 1 (by rfl) ⟨24877853, by rfl⟩ : syracuseStep 33170471 = 49755707) B49755707
theorem B2590175 : Blo 1725063 2590175 := bstep (se 1 (by rfl) ⟨1942631, by rfl⟩ : syracuseStep 2590175 = 3885263) B3885263
theorem B29878271 : Blo 1725063 29878271 := bstep (se 1 (by rfl) ⟨22408703, by rfl⟩ : syracuseStep 29878271 = 44817407) B44817407
theorem B3885119 : Blo 1725063 3885119 := bstep (se 1 (by rfl) ⟨2913839, by rfl⟩ : syracuseStep 3885119 = 5827679) B5827679
theorem B24890489 : Blo 1725063 24890489 := bstep (se 2 (by rfl) ⟨9333933, by rfl⟩ : syracuseStep 24890489 = 18667867) B18667867
theorem B67267729 : Blo 1725063 67267729 := bstep (se 2 (by rfl) ⟨25225398, by rfl⟩ : syracuseStep 67267729 = 50450797) B50450797
theorem B8737145 : Blo 1725063 8737145 := bstep (se 2 (by rfl) ⟨3276429, by rfl⟩ : syracuseStep 8737145 = 6552859) B6552859
theorem B19658213 : Blo 1725063 19658213 := bstep (se 4 (by rfl) ⟨1842957, by rfl⟩ : syracuseStep 19658213 = 3685915) B3685915
theorem B11064923 : Blo 1725063 11064923 := bstep (se 1 (by rfl) ⟨8298692, by rfl⟩ : syracuseStep 11064923 = 16597385) B16597385
theorem B1726159 : Blo 1725063 1726159 := bstep (se 1 (by rfl) ⟨1294619, by rfl⟩ : syracuseStep 1726159 = 2589239) B2589239
theorem B12441809 : Blo 1725063 12441809 := bstep (se 2 (by rfl) ⟨4665678, by rfl⟩ : syracuseStep 12441809 = 9331357) B9331357
theorem B8411759 : Blo 1725063 8411759 := bstep (se 1 (by rfl) ⟨6308819, by rfl⟩ : syracuseStep 8411759 = 12617639) B12617639
theorem B5824763 : Blo 1725063 5824763 := bstep (se 1 (by rfl) ⟨4368572, by rfl⟩ : syracuseStep 5824763 = 8737145) B8737145
theorem B33178157 : Blo 1725063 33178157 := bstep (se 3 (by rfl) ⟨6220904, by rfl⟩ : syracuseStep 33178157 = 12441809) B12441809
theorem B14942879 : Blo 1725063 14942879 := bstep (se 1 (by rfl) ⟨11207159, by rfl⟩ : syracuseStep 14942879 = 22414319) B22414319
theorem B358761221 : Blo 1725063 358761221 := bstep (se 4 (by rfl) ⟨33633864, by rfl⟩ : syracuseStep 358761221 = 67267729) B67267729
theorem B2590079 : Blo 1725063 2590079 := bstep (se 1 (by rfl) ⟨1942559, by rfl⟩ : syracuseStep 2590079 = 3885119) B3885119
theorem B4664231 : Blo 1725063 4664231 := bstep (se 1 (by rfl) ⟨3498173, by rfl⟩ : syracuseStep 4664231 = 6996347) B6996347
theorem B116665447 : Blo 1725063 116665447 := bstep (se 1 (by rfl) ⟨87499085, by rfl⟩ : syracuseStep 116665447 = 174998171) B174998171
theorem B2911423 : Blo 1725063 2911423 := bstep (se 1 (by rfl) ⟨2183567, by rfl⟩ : syracuseStep 2911423 = 4367135) B4367135
theorem B22113647 : Blo 1725063 22113647 := bstep (se 1 (by rfl) ⟨16585235, by rfl⟩ : syracuseStep 22113647 = 33170471) B33170471
theorem B340373177 : Blo 1725063 340373177 := bstep (se 2 (by rfl) ⟨127639941, by rfl⟩ : syracuseStep 340373177 = 255279883) B255279883
theorem B7376615 : Blo 1725063 7376615 := bstep (se 1 (by rfl) ⟨5532461, by rfl⟩ : syracuseStep 7376615 = 11064923) B11064923
theorem B19918847 : Blo 1725063 19918847 := bstep (se 1 (by rfl) ⟨14939135, by rfl⟩ : syracuseStep 19918847 = 29878271) B29878271
theorem B5607839 : Blo 1725063 5607839 := bstep (se 1 (by rfl) ⟨4205879, by rfl⟩ : syracuseStep 5607839 = 8411759) B8411759
theorem B16593659 : Blo 1725063 16593659 := bstep (se 1 (by rfl) ⟨12445244, by rfl⟩ : syracuseStep 16593659 = 24890489) B24890489
theorem B1725887 : Blo 1725063 1725887 := bstep (se 1 (by rfl) ⟨1294415, by rfl⟩ : syracuseStep 1725887 = 2588831) B2588831
theorem B23615135 : Blo 1725063 23615135 := bstep (se 1 (by rfl) ⟨17711351, by rfl⟩ : syracuseStep 23615135 = 35422703) B35422703
theorem B1726183 : Blo 1725063 1726183 := bstep (se 1 (by rfl) ⟨1294637, by rfl⟩ : syracuseStep 1726183 = 2589275) B2589275
theorem B1726207 : Blo 1725063 1726207 := bstep (se 1 (by rfl) ⟨1294655, by rfl⟩ : syracuseStep 1726207 = 2589311) B2589311
theorem B1726311 : Blo 1725063 1726311 := bstep (se 1 (by rfl) ⟨1294733, by rfl⟩ : syracuseStep 1726311 = 2589467) B2589467
theorem B35444627 : Blo 1725063 35444627 := bstep (se 1 (by rfl) ⟨26583470, by rfl⟩ : syracuseStep 35444627 = 53166941) B53166941
theorem B1726399 : Blo 1725063 1726399 := bstep (se 1 (by rfl) ⟨1294799, by rfl⟩ : syracuseStep 1726399 = 2589599) B2589599
theorem B1726783 : Blo 1725063 1726783 := bstep (se 1 (by rfl) ⟨1295087, by rfl⟩ : syracuseStep 1726783 = 2590175) B2590175
theorem B13105475 : Blo 1725063 13105475 := bstep (se 1 (by rfl) ⟨9829106, by rfl⟩ : syracuseStep 13105475 = 19658213) B19658213
theorem B3883175 : Blo 1725063 3883175 := bstep (se 1 (by rfl) ⟨2912381, by rfl⟩ : syracuseStep 3883175 = 5824763) B5824763
theorem B22118771 : Blo 1725063 22118771 := bstep (se 1 (by rfl) ⟨16589078, by rfl⟩ : syracuseStep 22118771 = 33178157) B33178157
theorem B9961919 : Blo 1725063 9961919 := bstep (se 1 (by rfl) ⟨7471439, by rfl⟩ : syracuseStep 9961919 = 14942879) B14942879
theorem B239174147 : Blo 1725063 239174147 := bstep (se 1 (by rfl) ⟨179380610, by rfl⟩ : syracuseStep 239174147 = 358761221) B358761221
theorem B4917743 : Blo 1725063 4917743 := bstep (se 1 (by rfl) ⟨3688307, by rfl⟩ : syracuseStep 4917743 = 7376615) B7376615
theorem B11062439 : Blo 1725063 11062439 := bstep (se 1 (by rfl) ⟨8296829, by rfl⟩ : syracuseStep 11062439 = 16593659) B16593659
theorem B14954237 : Blo 1725063 14954237 := bstep (se 3 (by rfl) ⟨2803919, by rfl⟩ : syracuseStep 14954237 = 5607839) B5607839
theorem B23629751 : Blo 1725063 23629751 := bstep (se 1 (by rfl) ⟨17722313, by rfl⟩ : syracuseStep 23629751 = 35444627) B35444627
theorem B155553929 : Blo 1725063 155553929 := bstep (se 2 (by rfl) ⟨58332723, by rfl⟩ : syracuseStep 155553929 = 116665447) B116665447
theorem B8736983 : Blo 1725063 8736983 := bstep (se 1 (by rfl) ⟨6552737, by rfl⟩ : syracuseStep 8736983 = 13105475) B13105475
theorem B3109487 : Blo 1725063 3109487 := bstep (se 1 (by rfl) ⟨2332115, by rfl⟩ : syracuseStep 3109487 = 4664231) B4664231
theorem B14742431 : Blo 1725063 14742431 := bstep (se 1 (by rfl) ⟨11056823, by rfl⟩ : syracuseStep 14742431 = 22113647) B22113647
theorem B226915451 : Blo 1725063 226915451 := bstep (se 1 (by rfl) ⟨170186588, by rfl⟩ : syracuseStep 226915451 = 340373177) B340373177
theorem B1726719 : Blo 1725063 1726719 := bstep (se 1 (by rfl) ⟨1295039, by rfl⟩ : syracuseStep 1726719 = 2590079) B2590079
theorem B15743423 : Blo 1725063 15743423 := bstep (se 1 (by rfl) ⟨11807567, by rfl⟩ : syracuseStep 15743423 = 23615135) B23615135
theorem B3881897 : Blo 1725063 3881897 := bstep (se 2 (by rfl) ⟨1455711, by rfl⟩ : syracuseStep 3881897 = 2911423) B2911423
theorem B13279231 : Blo 1725063 13279231 := bstep (se 1 (by rfl) ⟨9959423, by rfl⟩ : syracuseStep 13279231 = 19918847) B19918847
theorem B103702619 : Blo 1725063 103702619 := bstep (se 1 (by rfl) ⟨77776964, by rfl⟩ : syracuseStep 103702619 = 155553929) B155553929
theorem B2588783 : Blo 1725063 2588783 := bstep (se 1 (by rfl) ⟨1941587, by rfl⟩ : syracuseStep 2588783 = 3883175) B3883175
theorem B5824655 : Blo 1725063 5824655 := bstep (se 1 (by rfl) ⟨4368491, by rfl⟩ : syracuseStep 5824655 = 8736983) B8736983
theorem B14745847 : Blo 1725063 14745847 := bstep (se 1 (by rfl) ⟨11059385, by rfl⟩ : syracuseStep 14745847 = 22118771) B22118771
theorem B159449431 : Blo 1725063 159449431 := bstep (se 1 (by rfl) ⟨119587073, by rfl⟩ : syracuseStep 159449431 = 239174147) B239174147
theorem B8291965 : Blo 1725063 8291965 := bstep (se 3 (by rfl) ⟨1554743, by rfl⟩ : syracuseStep 8291965 = 3109487) B3109487
theorem B10495615 : Blo 1725063 10495615 := bstep (se 1 (by rfl) ⟨7871711, by rfl⟩ : syracuseStep 10495615 = 15743423) B15743423
theorem B3278495 : Blo 1725063 3278495 := bstep (se 1 (by rfl) ⟨2458871, by rfl⟩ : syracuseStep 3278495 = 4917743) B4917743
theorem B7374959 : Blo 1725063 7374959 := bstep (se 1 (by rfl) ⟨5531219, by rfl⟩ : syracuseStep 7374959 = 11062439) B11062439
theorem B17705641 : Blo 1725063 17705641 := bstep (se 2 (by rfl) ⟨6639615, by rfl⟩ : syracuseStep 17705641 = 13279231) B13279231
theorem B151276967 : Blo 1725063 151276967 := bstep (se 1 (by rfl) ⟨113457725, by rfl⟩ : syracuseStep 151276967 = 226915451) B226915451
theorem B6641279 : Blo 1725063 6641279 := bstep (se 1 (by rfl) ⟨4980959, by rfl⟩ : syracuseStep 6641279 = 9961919) B9961919
theorem B9828287 : Blo 1725063 9828287 := bstep (se 1 (by rfl) ⟨7371215, by rfl⟩ : syracuseStep 9828287 = 14742431) B14742431
theorem B2587931 : Blo 1725063 2587931 := bstep (se 1 (by rfl) ⟨1940948, by rfl⟩ : syracuseStep 2587931 = 3881897) B3881897
theorem B9969491 : Blo 1725063 9969491 := bstep (se 1 (by rfl) ⟨7477118, by rfl⟩ : syracuseStep 9969491 = 14954237) B14954237
theorem B15753167 : Blo 1725063 15753167 := bstep (se 1 (by rfl) ⟨11814875, by rfl⟩ : syracuseStep 15753167 = 23629751) B23629751
theorem B3883103 : Blo 1725063 3883103 := bstep (se 1 (by rfl) ⟨2912327, by rfl⟩ : syracuseStep 3883103 = 5824655) B5824655
theorem B19661129 : Blo 1725063 19661129 := bstep (se 2 (by rfl) ⟨7372923, by rfl⟩ : syracuseStep 19661129 = 14745847) B14745847
theorem B212599241 : Blo 1725063 212599241 := bstep (se 2 (by rfl) ⟨79724715, by rfl⟩ : syracuseStep 212599241 = 159449431) B159449431
theorem B4916639 : Blo 1725063 4916639 := bstep (se 1 (by rfl) ⟨3687479, by rfl⟩ : syracuseStep 4916639 = 7374959) B7374959
theorem B8742653 : Blo 1725063 8742653 := bstep (se 3 (by rfl) ⟨1639247, by rfl⟩ : syracuseStep 8742653 = 3278495) B3278495
theorem B13994153 : Blo 1725063 13994153 := bstep (se 2 (by rfl) ⟨5247807, by rfl⟩ : syracuseStep 13994153 = 10495615) B10495615
theorem B26585309 : Blo 1725063 26585309 := bstep (se 3 (by rfl) ⟨4984745, by rfl⟩ : syracuseStep 26585309 = 9969491) B9969491
theorem B69135079 : Blo 1725063 69135079 := bstep (se 1 (by rfl) ⟨51851309, by rfl⟩ : syracuseStep 69135079 = 103702619) B103702619
theorem B4427519 : Blo 1725063 4427519 := bstep (se 1 (by rfl) ⟨3320639, by rfl⟩ : syracuseStep 4427519 = 6641279) B6641279
theorem B11055953 : Blo 1725063 11055953 := bstep (se 2 (by rfl) ⟨4145982, by rfl⟩ : syracuseStep 11055953 = 8291965) B8291965
theorem B1725287 : Blo 1725063 1725287 := bstep (se 1 (by rfl) ⟨1293965, by rfl⟩ : syracuseStep 1725287 = 2587931) B2587931
theorem B1725855 : Blo 1725063 1725855 := bstep (se 1 (by rfl) ⟨1294391, by rfl⟩ : syracuseStep 1725855 = 2588783) B2588783
theorem B23607521 : Blo 1725063 23607521 := bstep (se 2 (by rfl) ⟨8852820, by rfl⟩ : syracuseStep 23607521 = 17705641) B17705641
theorem B6552191 : Blo 1725063 6552191 := bstep (se 1 (by rfl) ⟨4914143, by rfl⟩ : syracuseStep 6552191 = 9828287) B9828287
theorem B100851311 : Blo 1725063 100851311 := bstep (se 1 (by rfl) ⟨75638483, by rfl⟩ : syracuseStep 100851311 = 151276967) B151276967
theorem B10502111 : Blo 1725063 10502111 := bstep (se 1 (by rfl) ⟨7876583, by rfl⟩ : syracuseStep 10502111 = 15753167) B15753167
theorem B2588735 : Blo 1725063 2588735 := bstep (se 1 (by rfl) ⟨1941551, by rfl⟩ : syracuseStep 2588735 = 3883103) B3883103
theorem B13107419 : Blo 1725063 13107419 := bstep (se 1 (by rfl) ⟨9830564, by rfl⟩ : syracuseStep 13107419 = 19661129) B19661129
theorem B3277759 : Blo 1725063 3277759 := bstep (se 1 (by rfl) ⟨2458319, by rfl⟩ : syracuseStep 3277759 = 4916639) B4916639
theorem B15738347 : Blo 1725063 15738347 := bstep (se 1 (by rfl) ⟨11803760, by rfl⟩ : syracuseStep 15738347 = 23607521) B23607521
theorem B4368127 : Blo 1725063 4368127 := bstep (se 1 (by rfl) ⟨3276095, by rfl⟩ : syracuseStep 4368127 = 6552191) B6552191
theorem B11806717 : Blo 1725063 11806717 := bstep (se 3 (by rfl) ⟨2213759, by rfl⟩ : syracuseStep 11806717 = 4427519) B4427519
theorem B67234207 : Blo 1725063 67234207 := bstep (se 1 (by rfl) ⟨50425655, by rfl⟩ : syracuseStep 67234207 = 100851311) B100851311
theorem B141732827 : Blo 1725063 141732827 := bstep (se 1 (by rfl) ⟨106299620, by rfl⟩ : syracuseStep 141732827 = 212599241) B212599241
theorem B92180105 : Blo 1725063 92180105 := bstep (se 2 (by rfl) ⟨34567539, by rfl⟩ : syracuseStep 92180105 = 69135079) B69135079
theorem B5828435 : Blo 1725063 5828435 := bstep (se 1 (by rfl) ⟨4371326, by rfl⟩ : syracuseStep 5828435 = 8742653) B8742653
theorem B17723539 : Blo 1725063 17723539 := bstep (se 1 (by rfl) ⟨13292654, by rfl⟩ : syracuseStep 17723539 = 26585309) B26585309
theorem B7001407 : Blo 1725063 7001407 := bstep (se 1 (by rfl) ⟨5251055, by rfl⟩ : syracuseStep 7001407 = 10502111) B10502111
theorem B7370635 : Blo 1725063 7370635 := bstep (se 1 (by rfl) ⟨5527976, by rfl⟩ : syracuseStep 7370635 = 11055953) B11055953
theorem B9329435 : Blo 1725063 9329435 := bstep (se 1 (by rfl) ⟨6997076, by rfl⟩ : syracuseStep 9329435 = 13994153) B13994153
theorem B89645609 : Blo 1725063 89645609 := bstep (se 2 (by rfl) ⟨33617103, by rfl⟩ : syracuseStep 89645609 = 67234207) B67234207
theorem B41968925 : Blo 1725063 41968925 := bstep (se 3 (by rfl) ⟨7869173, by rfl⟩ : syracuseStep 41968925 = 15738347) B15738347
theorem B37340837 : Blo 1725063 37340837 := bstep (se 4 (by rfl) ⟨3500703, by rfl⟩ : syracuseStep 37340837 = 7001407) B7001407
theorem B6219623 : Blo 1725063 6219623 := bstep (se 1 (by rfl) ⟨4664717, by rfl⟩ : syracuseStep 6219623 = 9329435) B9329435
theorem B94488551 : Blo 1725063 94488551 := bstep (se 1 (by rfl) ⟨70866413, by rfl⟩ : syracuseStep 94488551 = 141732827) B141732827
theorem B3885623 : Blo 1725063 3885623 := bstep (se 1 (by rfl) ⟨2914217, by rfl⟩ : syracuseStep 3885623 = 5828435) B5828435
theorem B4370345 : Blo 1725063 4370345 := bstep (se 2 (by rfl) ⟨1638879, by rfl⟩ : syracuseStep 4370345 = 3277759) B3277759
theorem B61453403 : Blo 1725063 61453403 := bstep (se 1 (by rfl) ⟨46090052, by rfl⟩ : syracuseStep 61453403 = 92180105) B92180105
theorem B9827513 : Blo 1725063 9827513 := bstep (se 2 (by rfl) ⟨3685317, by rfl⟩ : syracuseStep 9827513 = 7370635) B7370635
theorem B15742289 : Blo 1725063 15742289 := bstep (se 2 (by rfl) ⟨5903358, by rfl⟩ : syracuseStep 15742289 = 11806717) B11806717
theorem B1725823 : Blo 1725063 1725823 := bstep (se 1 (by rfl) ⟨1294367, by rfl⟩ : syracuseStep 1725823 = 2588735) B2588735
theorem B8738279 : Blo 1725063 8738279 := bstep (se 1 (by rfl) ⟨6553709, by rfl⟩ : syracuseStep 8738279 = 13107419) B13107419
theorem B23631385 : Blo 1725063 23631385 := bstep (se 2 (by rfl) ⟨8861769, by rfl⟩ : syracuseStep 23631385 = 17723539) B17723539
theorem B5824169 : Blo 1725063 5824169 := bstep (se 2 (by rfl) ⟨2184063, by rfl⟩ : syracuseStep 5824169 = 4368127) B4368127
theorem B40968935 : Blo 1725063 40968935 := bstep (se 1 (by rfl) ⟨30726701, by rfl⟩ : syracuseStep 40968935 = 61453403) B61453403
theorem B10494859 : Blo 1725063 10494859 := bstep (se 1 (by rfl) ⟨7871144, by rfl⟩ : syracuseStep 10494859 = 15742289) B15742289
theorem B5825519 : Blo 1725063 5825519 := bstep (se 1 (by rfl) ⟨4369139, by rfl⟩ : syracuseStep 5825519 = 8738279) B8738279
theorem B2590415 : Blo 1725063 2590415 := bstep (se 1 (by rfl) ⟨1942811, by rfl⟩ : syracuseStep 2590415 = 3885623) B3885623
theorem B31508513 : Blo 1725063 31508513 := bstep (se 2 (by rfl) ⟨11815692, by rfl⟩ : syracuseStep 31508513 = 23631385) B23631385
theorem B59763739 : Blo 1725063 59763739 := bstep (se 1 (by rfl) ⟨44822804, by rfl⟩ : syracuseStep 59763739 = 89645609) B89645609
theorem B27979283 : Blo 1725063 27979283 := bstep (se 1 (by rfl) ⟨20984462, by rfl⟩ : syracuseStep 27979283 = 41968925) B41968925
theorem B62992367 : Blo 1725063 62992367 := bstep (se 1 (by rfl) ⟨47244275, by rfl⟩ : syracuseStep 62992367 = 94488551) B94488551
theorem B16585661 : Blo 1725063 16585661 := bstep (se 3 (by rfl) ⟨3109811, by rfl⟩ : syracuseStep 16585661 = 6219623) B6219623
theorem B2913563 : Blo 1725063 2913563 := bstep (se 1 (by rfl) ⟨2185172, by rfl⟩ : syracuseStep 2913563 = 4370345) B4370345
theorem B6551675 : Blo 1725063 6551675 := bstep (se 1 (by rfl) ⟨4913756, by rfl⟩ : syracuseStep 6551675 = 9827513) B9827513
theorem B24893891 : Blo 1725063 24893891 := bstep (se 1 (by rfl) ⟨18670418, by rfl⟩ : syracuseStep 24893891 = 37340837) B37340837
theorem B3882779 : Blo 1725063 3882779 := bstep (se 1 (by rfl) ⟨2912084, by rfl⟩ : syracuseStep 3882779 = 5824169) B5824169
theorem B27312623 : Blo 1725063 27312623 := bstep (se 1 (by rfl) ⟨20484467, by rfl⟩ : syracuseStep 27312623 = 40968935) B40968935
theorem B3883679 : Blo 1725063 3883679 := bstep (se 1 (by rfl) ⟨2912759, by rfl⟩ : syracuseStep 3883679 = 5825519) B5825519
theorem B1942375 : Blo 1725063 1942375 := bstep (se 1 (by rfl) ⟨1456781, by rfl⟩ : syracuseStep 1942375 = 2913563) B2913563
theorem B13993145 : Blo 1725063 13993145 := bstep (se 2 (by rfl) ⟨5247429, by rfl⟩ : syracuseStep 13993145 = 10494859) B10494859
theorem B21005675 : Blo 1725063 21005675 := bstep (se 1 (by rfl) ⟨15754256, by rfl⟩ : syracuseStep 21005675 = 31508513) B31508513
theorem B79684985 : Blo 1725063 79684985 := bstep (se 2 (by rfl) ⟨29881869, by rfl⟩ : syracuseStep 79684985 = 59763739) B59763739
theorem B4367783 : Blo 1725063 4367783 := bstep (se 1 (by rfl) ⟨3275837, by rfl⟩ : syracuseStep 4367783 = 6551675) B6551675
theorem B41994911 : Blo 1725063 41994911 := bstep (se 1 (by rfl) ⟨31496183, by rfl⟩ : syracuseStep 41994911 = 62992367) B62992367
theorem B11057107 : Blo 1725063 11057107 := bstep (se 1 (by rfl) ⟨8292830, by rfl⟩ : syracuseStep 11057107 = 16585661) B16585661
theorem B1726943 : Blo 1725063 1726943 := bstep (se 1 (by rfl) ⟨1295207, by rfl⟩ : syracuseStep 1726943 = 2590415) B2590415
theorem B16595927 : Blo 1725063 16595927 := bstep (se 1 (by rfl) ⟨12446945, by rfl⟩ : syracuseStep 16595927 = 24893891) B24893891
theorem B18652855 : Blo 1725063 18652855 := bstep (se 1 (by rfl) ⟨13989641, by rfl⟩ : syracuseStep 18652855 = 27979283) B27979283
theorem B2588519 : Blo 1725063 2588519 := bstep (se 1 (by rfl) ⟨1941389, by rfl⟩ : syracuseStep 2588519 = 3882779) B3882779
theorem B2589119 : Blo 1725063 2589119 := bstep (se 1 (by rfl) ⟨1941839, by rfl⟩ : syracuseStep 2589119 = 3883679) B3883679
theorem B212493293 : Blo 1725063 212493293 := bstep (se 3 (by rfl) ⟨39842492, by rfl⟩ : syracuseStep 212493293 = 79684985) B79684985
theorem B2589833 : Blo 1725063 2589833 := bstep (se 2 (by rfl) ⟨971187, by rfl⟩ : syracuseStep 2589833 = 1942375) B1942375
theorem B14003783 : Blo 1725063 14003783 := bstep (se 1 (by rfl) ⟨10502837, by rfl⟩ : syracuseStep 14003783 = 21005675) B21005675
theorem B2911855 : Blo 1725063 2911855 := bstep (se 1 (by rfl) ⟨2183891, by rfl⟩ : syracuseStep 2911855 = 4367783) B4367783
theorem B27996607 : Blo 1725063 27996607 := bstep (se 1 (by rfl) ⟨20997455, by rfl⟩ : syracuseStep 27996607 = 41994911) B41994911
theorem B11063951 : Blo 1725063 11063951 := bstep (se 1 (by rfl) ⟨8297963, by rfl⟩ : syracuseStep 11063951 = 16595927) B16595927
theorem B1725679 : Blo 1725063 1725679 := bstep (se 1 (by rfl) ⟨1294259, by rfl⟩ : syracuseStep 1725679 = 2588519) B2588519
theorem B14742809 : Blo 1725063 14742809 := bstep (se 2 (by rfl) ⟨5528553, by rfl⟩ : syracuseStep 14742809 = 11057107) B11057107
theorem B18208415 : Blo 1725063 18208415 := bstep (se 1 (by rfl) ⟨13656311, by rfl⟩ : syracuseStep 18208415 = 27312623) B27312623
theorem B9328763 : Blo 1725063 9328763 := bstep (se 1 (by rfl) ⟨6996572, by rfl⟩ : syracuseStep 9328763 = 13993145) B13993145
theorem B24870473 : Blo 1725063 24870473 := bstep (se 2 (by rfl) ⟨9326427, by rfl⟩ : syracuseStep 24870473 = 18652855) B18652855
theorem B6219175 : Blo 1725063 6219175 := bstep (se 1 (by rfl) ⟨4664381, by rfl⟩ : syracuseStep 6219175 = 9328763) B9328763
theorem B7375967 : Blo 1725063 7375967 := bstep (se 1 (by rfl) ⟨5531975, by rfl⟩ : syracuseStep 7375967 = 11063951) B11063951
theorem B9335855 : Blo 1725063 9335855 := bstep (se 1 (by rfl) ⟨7001891, by rfl⟩ : syracuseStep 9335855 = 14003783) B14003783
theorem B1726079 : Blo 1725063 1726079 := bstep (se 1 (by rfl) ⟨1294559, by rfl⟩ : syracuseStep 1726079 = 2589119) B2589119
theorem B37328809 : Blo 1725063 37328809 := bstep (se 2 (by rfl) ⟨13998303, by rfl⟩ : syracuseStep 37328809 = 27996607) B27996607
theorem B141662195 : Blo 1725063 141662195 := bstep (se 1 (by rfl) ⟨106246646, by rfl⟩ : syracuseStep 141662195 = 212493293) B212493293
theorem B1726555 : Blo 1725063 1726555 := bstep (se 1 (by rfl) ⟨1294916, by rfl⟩ : syracuseStep 1726555 = 2589833) B2589833
theorem B9828539 : Blo 1725063 9828539 := bstep (se 1 (by rfl) ⟨7371404, by rfl⟩ : syracuseStep 9828539 = 14742809) B14742809
theorem B12138943 : Blo 1725063 12138943 := bstep (se 1 (by rfl) ⟨9104207, by rfl⟩ : syracuseStep 12138943 = 18208415) B18208415
theorem B3882473 : Blo 1725063 3882473 := bstep (se 2 (by rfl) ⟨1455927, by rfl⟩ : syracuseStep 3882473 = 2911855) B2911855
theorem B16580315 : Blo 1725063 16580315 := bstep (se 1 (by rfl) ⟨12435236, by rfl⟩ : syracuseStep 16580315 = 24870473) B24870473
theorem B24895613 : Blo 1725063 24895613 := bstep (se 3 (by rfl) ⟨4667927, by rfl⟩ : syracuseStep 24895613 = 9335855) B9335855
theorem B8292233 : Blo 1725063 8292233 := bstep (se 2 (by rfl) ⟨3109587, by rfl⟩ : syracuseStep 8292233 = 6219175) B6219175
theorem B4917311 : Blo 1725063 4917311 := bstep (se 1 (by rfl) ⟨3687983, by rfl⟩ : syracuseStep 4917311 = 7375967) B7375967
theorem B11053543 : Blo 1725063 11053543 := bstep (se 1 (by rfl) ⟨8290157, by rfl⟩ : syracuseStep 11053543 = 16580315) B16580315
theorem B94441463 : Blo 1725063 94441463 := bstep (se 1 (by rfl) ⟨70831097, by rfl⟩ : syracuseStep 94441463 = 141662195) B141662195
theorem B49771745 : Blo 1725063 49771745 := bstep (se 2 (by rfl) ⟨18664404, by rfl⟩ : syracuseStep 49771745 = 37328809) B37328809
theorem B16185257 : Blo 1725063 16185257 := bstep (se 2 (by rfl) ⟨6069471, by rfl⟩ : syracuseStep 16185257 = 12138943) B12138943
theorem B6552359 : Blo 1725063 6552359 := bstep (se 1 (by rfl) ⟨4914269, by rfl⟩ : syracuseStep 6552359 = 9828539) B9828539
theorem B2588315 : Blo 1725063 2588315 := bstep (se 1 (by rfl) ⟨1941236, by rfl⟩ : syracuseStep 2588315 = 3882473) B3882473
theorem B16597075 : Blo 1725063 16597075 := bstep (se 1 (by rfl) ⟨12447806, by rfl⟩ : syracuseStep 16597075 = 24895613) B24895613
theorem B14738057 : Blo 1725063 14738057 := bstep (se 2 (by rfl) ⟨5526771, by rfl⟩ : syracuseStep 14738057 = 11053543) B11053543
theorem B10790171 : Blo 1725063 10790171 := bstep (se 1 (by rfl) ⟨8092628, by rfl⟩ : syracuseStep 10790171 = 16185257) B16185257
theorem B3278207 : Blo 1725063 3278207 := bstep (se 1 (by rfl) ⟨2458655, by rfl⟩ : syracuseStep 3278207 = 4917311) B4917311
theorem B4368239 : Blo 1725063 4368239 := bstep (se 1 (by rfl) ⟨3276179, by rfl⟩ : syracuseStep 4368239 = 6552359) B6552359
theorem B22112621 : Blo 1725063 22112621 := bstep (se 3 (by rfl) ⟨4146116, by rfl⟩ : syracuseStep 22112621 = 8292233) B8292233
theorem B33181163 : Blo 1725063 33181163 := bstep (se 1 (by rfl) ⟨24885872, by rfl⟩ : syracuseStep 33181163 = 49771745) B49771745
theorem B1725543 : Blo 1725063 1725543 := bstep (se 1 (by rfl) ⟨1294157, by rfl⟩ : syracuseStep 1725543 = 2588315) B2588315
theorem B62960975 : Blo 1725063 62960975 := bstep (se 1 (by rfl) ⟨47220731, by rfl⟩ : syracuseStep 62960975 = 94441463) B94441463
theorem B7193447 : Blo 1725063 7193447 := bstep (se 1 (by rfl) ⟨5395085, by rfl⟩ : syracuseStep 7193447 = 10790171) B10790171
theorem B22120775 : Blo 1725063 22120775 := bstep (se 1 (by rfl) ⟨16590581, by rfl⟩ : syracuseStep 22120775 = 33181163) B33181163
theorem B22129433 : Blo 1725063 22129433 := bstep (se 2 (by rfl) ⟨8298537, by rfl⟩ : syracuseStep 22129433 = 16597075) B16597075
theorem B9825371 : Blo 1725063 9825371 := bstep (se 1 (by rfl) ⟨7369028, by rfl⟩ : syracuseStep 9825371 = 14738057) B14738057
theorem B2912159 : Blo 1725063 2912159 := bstep (se 1 (by rfl) ⟨2184119, by rfl⟩ : syracuseStep 2912159 = 4368239) B4368239
theorem B14741747 : Blo 1725063 14741747 := bstep (se 1 (by rfl) ⟨11056310, by rfl⟩ : syracuseStep 14741747 = 22112621) B22112621
theorem B41973983 : Blo 1725063 41973983 := bstep (se 1 (by rfl) ⟨31480487, by rfl⟩ : syracuseStep 41973983 = 62960975) B62960975
theorem B2185471 : Blo 1725063 2185471 := bstep (se 1 (by rfl) ⟨1639103, by rfl⟩ : syracuseStep 2185471 = 3278207) B3278207
theorem B14747183 : Blo 1725063 14747183 := bstep (se 1 (by rfl) ⟨11060387, by rfl⟩ : syracuseStep 14747183 = 22120775) B22120775
theorem B4795631 : Blo 1725063 4795631 := bstep (se 1 (by rfl) ⟨3596723, by rfl⟩ : syracuseStep 4795631 = 7193447) B7193447
theorem B6550247 : Blo 1725063 6550247 := bstep (se 1 (by rfl) ⟨4912685, by rfl⟩ : syracuseStep 6550247 = 9825371) B9825371
theorem B9827831 : Blo 1725063 9827831 := bstep (se 1 (by rfl) ⟨7370873, by rfl⟩ : syracuseStep 9827831 = 14741747) B14741747
theorem B2913961 : Blo 1725063 2913961 := bstep (se 2 (by rfl) ⟨1092735, by rfl⟩ : syracuseStep 2913961 = 2185471) B2185471
theorem B27982655 : Blo 1725063 27982655 := bstep (se 1 (by rfl) ⟨20986991, by rfl⟩ : syracuseStep 27982655 = 41973983) B41973983
theorem B14752955 : Blo 1725063 14752955 := bstep (se 1 (by rfl) ⟨11064716, by rfl⟩ : syracuseStep 14752955 = 22129433) B22129433
theorem B1941439 : Blo 1725063 1941439 := bstep (se 1 (by rfl) ⟨1456079, by rfl⟩ : syracuseStep 1941439 = 2912159) B2912159
theorem B4366831 : Blo 1725063 4366831 := bstep (se 1 (by rfl) ⟨3275123, by rfl⟩ : syracuseStep 4366831 = 6550247) B6550247
theorem B9831455 : Blo 1725063 9831455 := bstep (se 1 (by rfl) ⟨7373591, by rfl⟩ : syracuseStep 9831455 = 14747183) B14747183
theorem B18655103 : Blo 1725063 18655103 := bstep (se 1 (by rfl) ⟨13991327, by rfl⟩ : syracuseStep 18655103 = 27982655) B27982655
theorem B3197087 : Blo 1725063 3197087 := bstep (se 1 (by rfl) ⟨2397815, by rfl⟩ : syracuseStep 3197087 = 4795631) B4795631
theorem B3885281 : Blo 1725063 3885281 := bstep (se 2 (by rfl) ⟨1456980, by rfl⟩ : syracuseStep 3885281 = 2913961) B2913961
theorem B9835303 : Blo 1725063 9835303 := bstep (se 1 (by rfl) ⟨7376477, by rfl⟩ : syracuseStep 9835303 = 14752955) B14752955
theorem B6551887 : Blo 1725063 6551887 := bstep (se 1 (by rfl) ⟨4913915, by rfl⟩ : syracuseStep 6551887 = 9827831) B9827831
theorem B2588585 : Blo 1725063 2588585 := bstep (se 2 (by rfl) ⟨970719, by rfl⟩ : syracuseStep 2588585 = 1941439) B1941439
theorem B6554303 : Blo 1725063 6554303 := bstep (se 1 (by rfl) ⟨4915727, by rfl⟩ : syracuseStep 6554303 = 9831455) B9831455
theorem B12436735 : Blo 1725063 12436735 := bstep (se 1 (by rfl) ⟨9327551, by rfl⟩ : syracuseStep 12436735 = 18655103) B18655103
theorem B2131391 : Blo 1725063 2131391 := bstep (se 1 (by rfl) ⟨1598543, by rfl⟩ : syracuseStep 2131391 = 3197087) B3197087
theorem B2590187 : Blo 1725063 2590187 := bstep (se 1 (by rfl) ⟨1942640, by rfl⟩ : syracuseStep 2590187 = 3885281) B3885281
theorem B8735849 : Blo 1725063 8735849 := bstep (se 2 (by rfl) ⟨3275943, by rfl⟩ : syracuseStep 8735849 = 6551887) B6551887
theorem B1725723 : Blo 1725063 1725723 := bstep (se 1 (by rfl) ⟨1294292, by rfl⟩ : syracuseStep 1725723 = 2588585) B2588585
theorem B5822441 : Blo 1725063 5822441 := bstep (se 2 (by rfl) ⟨2183415, by rfl⟩ : syracuseStep 5822441 = 4366831) B4366831
theorem B13113737 : Blo 1725063 13113737 := bstep (se 2 (by rfl) ⟨4917651, by rfl⟩ : syracuseStep 13113737 = 9835303) B9835303
theorem B8742491 : Blo 1725063 8742491 := bstep (se 1 (by rfl) ⟨6556868, by rfl⟩ : syracuseStep 8742491 = 13113737) B13113737
theorem B16582313 : Blo 1725063 16582313 := bstep (se 2 (by rfl) ⟨6218367, by rfl⟩ : syracuseStep 16582313 = 12436735) B12436735
theorem B4369535 : Blo 1725063 4369535 := bstep (se 1 (by rfl) ⟨3277151, by rfl⟩ : syracuseStep 4369535 = 6554303) B6554303
theorem B1726791 : Blo 1725063 1726791 := bstep (se 1 (by rfl) ⟨1295093, by rfl⟩ : syracuseStep 1726791 = 2590187) B2590187
theorem B5683709 : Blo 1725063 5683709 := bstep (se 3 (by rfl) ⟨1065695, by rfl⟩ : syracuseStep 5683709 = 2131391) B2131391
theorem B3881627 : Blo 1725063 3881627 := bstep (se 1 (by rfl) ⟨2911220, by rfl⟩ : syracuseStep 3881627 = 5822441) B5822441
theorem B5823899 : Blo 1725063 5823899 := bstep (se 1 (by rfl) ⟨4367924, by rfl⟩ : syracuseStep 5823899 = 8735849) B8735849
theorem B5828327 : Blo 1725063 5828327 := bstep (se 1 (by rfl) ⟨4371245, by rfl⟩ : syracuseStep 5828327 = 8742491) B8742491
theorem B11054875 : Blo 1725063 11054875 := bstep (se 1 (by rfl) ⟨8291156, by rfl⟩ : syracuseStep 11054875 = 16582313) B16582313
theorem B3789139 : Blo 1725063 3789139 := bstep (se 1 (by rfl) ⟨2841854, by rfl⟩ : syracuseStep 3789139 = 5683709) B5683709
theorem B2913023 : Blo 1725063 2913023 := bstep (se 1 (by rfl) ⟨2184767, by rfl⟩ : syracuseStep 2913023 = 4369535) B4369535
theorem B2587751 : Blo 1725063 2587751 := bstep (se 1 (by rfl) ⟨1940813, by rfl⟩ : syracuseStep 2587751 = 3881627) B3881627
theorem B3882599 : Blo 1725063 3882599 := bstep (se 1 (by rfl) ⟨2911949, by rfl⟩ : syracuseStep 3882599 = 5823899) B5823899
theorem B1942015 : Blo 1725063 1942015 := bstep (se 1 (by rfl) ⟨1456511, by rfl⟩ : syracuseStep 1942015 = 2913023) B2913023
theorem B14739833 : Blo 1725063 14739833 := bstep (se 2 (by rfl) ⟨5527437, by rfl⟩ : syracuseStep 14739833 = 11054875) B11054875
theorem B3885551 : Blo 1725063 3885551 := bstep (se 1 (by rfl) ⟨2914163, by rfl⟩ : syracuseStep 3885551 = 5828327) B5828327
theorem B1725167 : Blo 1725063 1725167 := bstep (se 1 (by rfl) ⟨1293875, by rfl⟩ : syracuseStep 1725167 = 2587751) B2587751
theorem B5052185 : Blo 1725063 5052185 := bstep (se 2 (by rfl) ⟨1894569, by rfl⟩ : syracuseStep 5052185 = 3789139) B3789139
theorem B2588399 : Blo 1725063 2588399 := bstep (se 1 (by rfl) ⟨1941299, by rfl⟩ : syracuseStep 2588399 = 3882599) B3882599
theorem B2589353 : Blo 1725063 2589353 := bstep (se 2 (by rfl) ⟨971007, by rfl⟩ : syracuseStep 2589353 = 1942015) B1942015
theorem B3368123 : Blo 1725063 3368123 := bstep (se 1 (by rfl) ⟨2526092, by rfl⟩ : syracuseStep 3368123 = 5052185) B5052185
theorem B2590367 : Blo 1725063 2590367 := bstep (se 1 (by rfl) ⟨1942775, by rfl⟩ : syracuseStep 2590367 = 3885551) B3885551
theorem B9826555 : Blo 1725063 9826555 := bstep (se 1 (by rfl) ⟨7369916, by rfl⟩ : syracuseStep 9826555 = 14739833) B14739833
theorem B1725599 : Blo 1725063 1725599 := bstep (se 1 (by rfl) ⟨1294199, by rfl⟩ : syracuseStep 1725599 = 2588399) B2588399
theorem B2245415 : Blo 1725063 2245415 := bstep (se 1 (by rfl) ⟨1684061, by rfl⟩ : syracuseStep 2245415 = 3368123) B3368123
theorem B13102073 : Blo 1725063 13102073 := bstep (se 2 (by rfl) ⟨4913277, by rfl⟩ : syracuseStep 13102073 = 9826555) B9826555
theorem B1726235 : Blo 1725063 1726235 := bstep (se 1 (by rfl) ⟨1294676, by rfl⟩ : syracuseStep 1726235 = 2589353) B2589353
theorem B1726911 : Blo 1725063 1726911 := bstep (se 1 (by rfl) ⟨1295183, by rfl⟩ : syracuseStep 1726911 = 2590367) B2590367
theorem B8734715 : Blo 1725063 8734715 := bstep (se 1 (by rfl) ⟨6551036, by rfl⟩ : syracuseStep 8734715 = 13102073) B13102073
theorem B5987773 : Blo 1725063 5987773 := bstep (se 3 (by rfl) ⟨1122707, by rfl⟩ : syracuseStep 5987773 = 2245415) B2245415
theorem B7983697 : Blo 1725063 7983697 := bstep (se 2 (by rfl) ⟨2993886, by rfl⟩ : syracuseStep 7983697 = 5987773) B5987773
theorem B5823143 : Blo 1725063 5823143 := bstep (se 1 (by rfl) ⟨4367357, by rfl⟩ : syracuseStep 5823143 = 8734715) B8734715
theorem B10644929 : Blo 1725063 10644929 := bstep (se 2 (by rfl) ⟨3991848, by rfl⟩ : syracuseStep 10644929 = 7983697) B7983697
theorem B3882095 : Blo 1725063 3882095 := bstep (se 1 (by rfl) ⟨2911571, by rfl⟩ : syracuseStep 3882095 = 5823143) B5823143
theorem B7096619 : Blo 1725063 7096619 := bstep (se 1 (by rfl) ⟨5322464, by rfl⟩ : syracuseStep 7096619 = 10644929) B10644929
theorem B2588063 : Blo 1725063 2588063 := bstep (se 1 (by rfl) ⟨1941047, by rfl⟩ : syracuseStep 2588063 = 3882095) B3882095
theorem B4731079 : Blo 1725063 4731079 := bstep (se 1 (by rfl) ⟨3548309, by rfl⟩ : syracuseStep 4731079 = 7096619) B7096619
theorem B1725375 : Blo 1725063 1725375 := bstep (se 1 (by rfl) ⟨1294031, by rfl⟩ : syracuseStep 1725375 = 2588063) B2588063
theorem B6308105 : Blo 1725063 6308105 := bstep (se 2 (by rfl) ⟨2365539, by rfl⟩ : syracuseStep 6308105 = 4731079) B4731079
theorem B16821613 : Blo 1725063 16821613 := bstep (se 3 (by rfl) ⟨3154052, by rfl⟩ : syracuseStep 16821613 = 6308105) B6308105
theorem B89715269 : Blo 1725063 89715269 := bstep (se 4 (by rfl) ⟨8410806, by rfl⟩ : syracuseStep 89715269 = 16821613) B16821613
theorem B59810179 : Blo 1725063 59810179 := bstep (se 1 (by rfl) ⟨44857634, by rfl⟩ : syracuseStep 59810179 = 89715269) B89715269
theorem B79746905 : Blo 1725063 79746905 := bstep (se 2 (by rfl) ⟨29905089, by rfl⟩ : syracuseStep 79746905 = 59810179) B59810179
theorem B53164603 : Blo 1725063 53164603 := bstep (se 1 (by rfl) ⟨39873452, by rfl⟩ : syracuseStep 53164603 = 79746905) B79746905
theorem B70886137 : Blo 1725063 70886137 := bstep (se 2 (by rfl) ⟨26582301, by rfl⟩ : syracuseStep 70886137 = 53164603) B53164603
theorem B94514849 : Blo 1725063 94514849 := bstep (se 2 (by rfl) ⟨35443068, by rfl⟩ : syracuseStep 94514849 = 70886137) B70886137
theorem B63009899 : Blo 1725063 63009899 := bstep (se 1 (by rfl) ⟨47257424, by rfl⟩ : syracuseStep 63009899 = 94514849) B94514849
theorem B42006599 : Blo 1725063 42006599 := bstep (se 1 (by rfl) ⟨31504949, by rfl⟩ : syracuseStep 42006599 = 63009899) B63009899
theorem B28004399 : Blo 1725063 28004399 := bstep (se 1 (by rfl) ⟨21003299, by rfl⟩ : syracuseStep 28004399 = 42006599) B42006599
theorem B18669599 : Blo 1725063 18669599 := bstep (se 1 (by rfl) ⟨14002199, by rfl⟩ : syracuseStep 18669599 = 28004399) B28004399
theorem B12446399 : Blo 1725063 12446399 := bstep (se 1 (by rfl) ⟨9334799, by rfl⟩ : syracuseStep 12446399 = 18669599) B18669599
theorem B8297599 : Blo 1725063 8297599 := bstep (se 1 (by rfl) ⟨6223199, by rfl⟩ : syracuseStep 8297599 = 12446399) B12446399
theorem B11063465 : Blo 1725063 11063465 := bstep (se 2 (by rfl) ⟨4148799, by rfl⟩ : syracuseStep 11063465 = 8297599) B8297599
theorem B7375643 : Blo 1725063 7375643 := bstep (se 1 (by rfl) ⟨5531732, by rfl⟩ : syracuseStep 7375643 = 11063465) B11063465
theorem B4917095 : Blo 1725063 4917095 := bstep (se 1 (by rfl) ⟨3687821, by rfl⟩ : syracuseStep 4917095 = 7375643) B7375643
theorem B3278063 : Blo 1725063 3278063 := bstep (se 1 (by rfl) ⟨2458547, by rfl⟩ : syracuseStep 3278063 = 4917095) B4917095
theorem B2185375 : Blo 1725063 2185375 := bstep (se 1 (by rfl) ⟨1639031, by rfl⟩ : syracuseStep 2185375 = 3278063) B3278063
theorem B2913833 : Blo 1725063 2913833 := bstep (se 2 (by rfl) ⟨1092687, by rfl⟩ : syracuseStep 2913833 = 2185375) B2185375
theorem B1942555 : Blo 1725063 1942555 := bstep (se 1 (by rfl) ⟨1456916, by rfl⟩ : syracuseStep 1942555 = 2913833) B2913833
theorem B2590073 : Blo 1725063 2590073 := bstep (se 2 (by rfl) ⟨971277, by rfl⟩ : syracuseStep 2590073 = 1942555) B1942555
theorem B1726715 : Blo 1725063 1726715 := bstep (se 1 (by rfl) ⟨1295036, by rfl⟩ : syracuseStep 1726715 = 2590073) B2590073

theorem C0 (j : ℕ) (h1 : 431265 ≤ j) (h2 : j ≤ 431765) : Blo 1725063 (4 * j + 3) := by
  interval_cases j
  · exact B1725063
  · exact B1725067
  · exact B1725071
  · exact B1725075
  · exact B1725079
  · exact B1725083
  · exact B1725087
  · exact B1725091
  · exact B1725095
  · exact B1725099
  · exact B1725103
  · exact B1725107
  · exact B1725111
  · exact B1725115
  · exact B1725119
  · exact B1725123
  · exact B1725127
  · exact B1725131
  · exact B1725135
  · exact B1725139
  · exact B1725143
  · exact B1725147
  · exact B1725151
  · exact B1725155
  · exact B1725159
  · exact B1725163
  · exact B1725167
  · exact B1725171
  · exact B1725175
  · exact B1725179
  · exact B1725183
  · exact B1725187
  · exact B1725191
  · exact B1725195
  · exact B1725199
  · exact B1725203
  · exact B1725207
  · exact B1725211
  · exact B1725215
  · exact B1725219
  · exact B1725223
  · exact B1725227
  · exact B1725231
  · exact B1725235
  · exact B1725239
  · exact B1725243
  · exact B1725247
  · exact B1725251
  · exact B1725255
  · exact B1725259
  · exact B1725263
  · exact B1725267
  · exact B1725271
  · exact B1725275
  · exact B1725279
  · exact B1725283
  · exact B1725287
  · exact B1725291
  · exact B1725295
  · exact B1725299
  · exact B1725303
  · exact B1725307
  · exact B1725311
  · exact B1725315
  · exact B1725319
  · exact B1725323
  · exact B1725327
  · exact B1725331
  · exact B1725335
  · exact B1725339
  · exact B1725343
  · exact B1725347
  · exact B1725351
  · exact B1725355
  · exact B1725359
  · exact B1725363
  · exact B1725367
  · exact B1725371
  · exact B1725375
  · exact B1725379
  · exact B1725383
  · exact B1725387
  · exact B1725391
  · exact B1725395
  · exact B1725399
  · exact B1725403
  · exact B1725407
  · exact B1725411
  · exact B1725415
  · exact B1725419
  · exact B1725423
  · exact B1725427
  · exact B1725431
  · exact B1725435
  · exact B1725439
  · exact B1725443
  · exact B1725447
  · exact B1725451
  · exact B1725455
  · exact B1725459
  · exact B1725463
  · exact B1725467
  · exact B1725471
  · exact B1725475
  · exact B1725479
  · exact B1725483
  · exact B1725487
  · exact B1725491
  · exact B1725495
  · exact B1725499
  · exact B1725503
  · exact B1725507
  · exact B1725511
  · exact B1725515
  · exact B1725519
  · exact B1725523
  · exact B1725527
  · exact B1725531
  · exact B1725535
  · exact B1725539
  · exact B1725543
  · exact B1725547
  · exact B1725551
  · exact B1725555
  · exact B1725559
  · exact B1725563
  · exact B1725567
  · exact B1725571
  · exact B1725575
  · exact B1725579
  · exact B1725583
  · exact B1725587
  · exact B1725591
  · exact B1725595
  · exact B1725599
  · exact B1725603
  · exact B1725607
  · exact B1725611
  · exact B1725615
  · exact B1725619
  · exact B1725623
  · exact B1725627
  · exact B1725631
  · exact B1725635
  · exact B1725639
  · exact B1725643
  · exact B1725647
  · exact B1725651
  · exact B1725655
  · exact B1725659
  · exact B1725663
  · exact B1725667
  · exact B1725671
  · exact B1725675
  · exact B1725679
  · exact B1725683
  · exact B1725687
  · exact B1725691
  · exact B1725695
  · exact B1725699
  · exact B1725703
  · exact B1725707
  · exact B1725711
  · exact B1725715
  · exact B1725719
  · exact B1725723
  · exact B1725727
  · exact B1725731
  · exact B1725735
  · exact B1725739
  · exact B1725743
  · exact B1725747
  · exact B1725751
  · exact B1725755
  · exact B1725759
  · exact B1725763
  · exact B1725767
  · exact B1725771
  · exact B1725775
  · exact B1725779
  · exact B1725783
  · exact B1725787
  · exact B1725791
  · exact B1725795
  · exact B1725799
  · exact B1725803
  · exact B1725807
  · exact B1725811
  · exact B1725815
  · exact B1725819
  · exact B1725823
  · exact B1725827
  · exact B1725831
  · exact B1725835
  · exact B1725839
  · exact B1725843
  · exact B1725847
  · exact B1725851
  · exact B1725855
  · exact B1725859
  · exact B1725863
  · exact B1725867
  · exact B1725871
  · exact B1725875
  · exact B1725879
  · exact B1725883
  · exact B1725887
  · exact B1725891
  · exact B1725895
  · exact B1725899
  · exact B1725903
  · exact B1725907
  · exact B1725911
  · exact B1725915
  · exact B1725919
  · exact B1725923
  · exact B1725927
  · exact B1725931
  · exact B1725935
  · exact B1725939
  · exact B1725943
  · exact B1725947
  · exact B1725951
  · exact B1725955
  · exact B1725959
  · exact B1725963
  · exact B1725967
  · exact B1725971
  · exact B1725975
  · exact B1725979
  · exact B1725983
  · exact B1725987
  · exact B1725991
  · exact B1725995
  · exact B1725999
  · exact B1726003
  · exact B1726007
  · exact B1726011
  · exact B1726015
  · exact B1726019
  · exact B1726023
  · exact B1726027
  · exact B1726031
  · exact B1726035
  · exact B1726039
  · exact B1726043
  · exact B1726047
  · exact B1726051
  · exact B1726055
  · exact B1726059
  · exact B1726063
  · exact B1726067
  · exact B1726071
  · exact B1726075
  · exact B1726079
  · exact B1726083
  · exact B1726087
  · exact B1726091
  · exact B1726095
  · exact B1726099
  · exact B1726103
  · exact B1726107
  · exact B1726111
  · exact B1726115
  · exact B1726119
  · exact B1726123
  · exact B1726127
  · exact B1726131
  · exact B1726135
  · exact B1726139
  · exact B1726143
  · exact B1726147
  · exact B1726151
  · exact B1726155
  · exact B1726159
  · exact B1726163
  · exact B1726167
  · exact B1726171
  · exact B1726175
  · exact B1726179
  · exact B1726183
  · exact B1726187
  · exact B1726191
  · exact B1726195
  · exact B1726199
  · exact B1726203
  · exact B1726207
  · exact B1726211
  · exact B1726215
  · exact B1726219
  · exact B1726223
  · exact B1726227
  · exact B1726231
  · exact B1726235
  · exact B1726239
  · exact B1726243
  · exact B1726247
  · exact B1726251
  · exact B1726255
  · exact B1726259
  · exact B1726263
  · exact B1726267
  · exact B1726271
  · exact B1726275
  · exact B1726279
  · exact B1726283
  · exact B1726287
  · exact B1726291
  · exact B1726295
  · exact B1726299
  · exact B1726303
  · exact B1726307
  · exact B1726311
  · exact B1726315
  · exact B1726319
  · exact B1726323
  · exact B1726327
  · exact B1726331
  · exact B1726335
  · exact B1726339
  · exact B1726343
  · exact B1726347
  · exact B1726351
  · exact B1726355
  · exact B1726359
  · exact B1726363
  · exact B1726367
  · exact B1726371
  · exact B1726375
  · exact B1726379
  · exact B1726383
  · exact B1726387
  · exact B1726391
  · exact B1726395
  · exact B1726399
  · exact B1726403
  · exact B1726407
  · exact B1726411
  · exact B1726415
  · exact B1726419
  · exact B1726423
  · exact B1726427
  · exact B1726431
  · exact B1726435
  · exact B1726439
  · exact B1726443
  · exact B1726447
  · exact B1726451
  · exact B1726455
  · exact B1726459
  · exact B1726463
  · exact B1726467
  · exact B1726471
  · exact B1726475
  · exact B1726479
  · exact B1726483
  · exact B1726487
  · exact B1726491
  · exact B1726495
  · exact B1726499
  · exact B1726503
  · exact B1726507
  · exact B1726511
  · exact B1726515
  · exact B1726519
  · exact B1726523
  · exact B1726527
  · exact B1726531
  · exact B1726535
  · exact B1726539
  · exact B1726543
  · exact B1726547
  · exact B1726551
  · exact B1726555
  · exact B1726559
  · exact B1726563
  · exact B1726567
  · exact B1726571
  · exact B1726575
  · exact B1726579
  · exact B1726583
  · exact B1726587
  · exact B1726591
  · exact B1726595
  · exact B1726599
  · exact B1726603
  · exact B1726607
  · exact B1726611
  · exact B1726615
  · exact B1726619
  · exact B1726623
  · exact B1726627
  · exact B1726631
  · exact B1726635
  · exact B1726639
  · exact B1726643
  · exact B1726647
  · exact B1726651
  · exact B1726655
  · exact B1726659
  · exact B1726663
  · exact B1726667
  · exact B1726671
  · exact B1726675
  · exact B1726679
  · exact B1726683
  · exact B1726687
  · exact B1726691
  · exact B1726695
  · exact B1726699
  · exact B1726703
  · exact B1726707
  · exact B1726711
  · exact B1726715
  · exact B1726719
  · exact B1726723
  · exact B1726727
  · exact B1726731
  · exact B1726735
  · exact B1726739
  · exact B1726743
  · exact B1726747
  · exact B1726751
  · exact B1726755
  · exact B1726759
  · exact B1726763
  · exact B1726767
  · exact B1726771
  · exact B1726775
  · exact B1726779
  · exact B1726783
  · exact B1726787
  · exact B1726791
  · exact B1726795
  · exact B1726799
  · exact B1726803
  · exact B1726807
  · exact B1726811
  · exact B1726815
  · exact B1726819
  · exact B1726823
  · exact B1726827
  · exact B1726831
  · exact B1726835
  · exact B1726839
  · exact B1726843
  · exact B1726847
  · exact B1726851
  · exact B1726855
  · exact B1726859
  · exact B1726863
  · exact B1726867
  · exact B1726871
  · exact B1726875
  · exact B1726879
  · exact B1726883
  · exact B1726887
  · exact B1726891
  · exact B1726895
  · exact B1726899
  · exact B1726903
  · exact B1726907
  · exact B1726911
  · exact B1726915
  · exact B1726919
  · exact B1726923
  · exact B1726927
  · exact B1726931
  · exact B1726935
  · exact B1726939
  · exact B1726943
  · exact B1726947
  · exact B1726951
  · exact B1726955
  · exact B1726959
  · exact B1726963
  · exact B1726967
  · exact B1726971
  · exact B1726975
  · exact B1726979
  · exact B1726983
  · exact B1726987
  · exact B1726991
  · exact B1726995
  · exact B1726999
  · exact B1727003
  · exact B1727007
  · exact B1727011
  · exact B1727015
  · exact B1727019
  · exact B1727023
  · exact B1727027
  · exact B1727031
  · exact B1727035
  · exact B1727039
  · exact B1727043
  · exact B1727047
  · exact B1727051
  · exact B1727055
  · exact B1727059
  · exact B1727063

theorem solution (m : ℕ) (hlo : 1725063 ≤ m) (hhi : m ≤ 1727063) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 431265 ≤ j := by omega
    have hj2 : j ≤ 431765 := by omega
    have hb : Blo 1725063 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
