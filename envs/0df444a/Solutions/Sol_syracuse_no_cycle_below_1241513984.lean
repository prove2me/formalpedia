-- Prove2me | solution 1 for syracuse_no_cycle_below_1241513984
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-25T14:42:45.156139+00:00
-- url     : https://prove2.me/submissions/fdc403bd-ba26-4768-a571-0203acab5100

import Theorems.Thm_syracuse_periodic_reaches_one
import Theorems.Thm_syracuse_no_cycle_below_247463936
import Theorems.Thm_syracuse_descent_coprime_to_six_247463936_to_260046848
import Theorems.Thm_syracuse_descent_coprime_to_six_260046848_to_272629760
import Theorems.Thm_syracuse_descent_coprime_to_six_272629760_to_285212672
import Theorems.Thm_syracuse_descent_coprime_to_six_285212672_to_297795584
import Theorems.Thm_syracuse_descent_coprime_to_six_297795584_to_310378496
import Theorems.Thm_syracuse_descent_coprime_to_six_310378496_to_322961408
import Theorems.Thm_syracuse_descent_coprime_to_six_322961408_to_335544320
import Theorems.Thm_syracuse_descent_coprime_to_six_335544320_to_348127232
import Theorems.Thm_syracuse_descent_coprime_to_six_348127232_to_360710144
import Theorems.Thm_syracuse_descent_coprime_to_six_360710144_to_373293056
import Theorems.Thm_syracuse_descent_coprime_to_six_373293056_to_385875968
import Theorems.Thm_syracuse_descent_coprime_to_six_385875968_to_398458880
import Theorems.Thm_syracuse_descent_coprime_to_six_398458880_to_411041792
import Theorems.Thm_syracuse_descent_coprime_to_six_411041792_to_423624704
import Theorems.Thm_syracuse_descent_coprime_to_six_423624704_to_436207616
import Theorems.Thm_syracuse_descent_coprime_to_six_436207616_to_448790528
import Theorems.Thm_syracuse_descent_coprime_to_six_448790528_to_461373440
import Theorems.Thm_syracuse_descent_coprime_to_six_461373440_to_473956352
import Theorems.Thm_syracuse_descent_coprime_to_six_473956352_to_486539264
import Theorems.Thm_syracuse_descent_coprime_to_six_486539264_to_499122176
import Theorems.Thm_syracuse_descent_coprime_to_six_499122176_to_511705088
import Theorems.Thm_syracuse_descent_coprime_to_six_511705088_to_524288000
import Theorems.Thm_syracuse_descent_coprime_to_six_524288000_to_536870912
import Theorems.Thm_syracuse_descent_coprime_to_six_536870912_to_549453824
import Theorems.Thm_syracuse_descent_coprime_to_six_549453824_to_562036736
import Theorems.Thm_syracuse_descent_coprime_to_six_562036736_to_574619648
import Theorems.Thm_syracuse_descent_coprime_to_six_574619648_to_587202560
import Theorems.Thm_syracuse_descent_coprime_to_six_587202560_to_599785472
import Theorems.Thm_syracuse_descent_coprime_to_six_599785472_to_612368384
import Theorems.Thm_syracuse_descent_coprime_to_six_612368384_to_624951296
import Theorems.Thm_syracuse_descent_coprime_to_six_624951296_to_637534208
import Theorems.Thm_syracuse_descent_coprime_to_six_637534208_to_650117120
import Theorems.Thm_syracuse_descent_coprime_to_six_650117120_to_662700032
import Theorems.Thm_syracuse_descent_coprime_to_six_662700032_to_675282944
import Theorems.Thm_syracuse_descent_coprime_to_six_675282944_to_687865856
import Theorems.Thm_syracuse_descent_coprime_to_six_687865856_to_700448768
import Theorems.Thm_syracuse_descent_coprime_to_six_700448768_to_713031680
import Theorems.Thm_syracuse_descent_coprime_to_six_713031680_to_725614592
import Theorems.Thm_syracuse_descent_coprime_to_six_725614592_to_738197504
import Theorems.Thm_syracuse_descent_coprime_to_six_738197504_to_750780416
import Theorems.Thm_syracuse_descent_coprime_to_six_750780416_to_763363328
import Theorems.Thm_syracuse_descent_coprime_to_six_763363328_to_775946240
import Theorems.Thm_syracuse_descent_coprime_to_six_775946240_to_788529152
import Theorems.Thm_syracuse_descent_coprime_to_six_788529152_to_801112064
import Theorems.Thm_syracuse_descent_coprime_to_six_801112064_to_813694976
import Theorems.Thm_syracuse_descent_coprime_to_six_813694976_to_826277888
import Theorems.Thm_syracuse_descent_coprime_to_six_826277888_to_838860800
import Theorems.Thm_syracuse_descent_coprime_to_six_838860800_to_851443712
import Theorems.Thm_syracuse_descent_coprime_to_six_851443712_to_864026624
import Theorems.Thm_syracuse_descent_coprime_to_six_864026624_to_876609536
import Theorems.Thm_syracuse_descent_coprime_to_six_876609536_to_889192448
import Theorems.Thm_syracuse_descent_coprime_to_six_889192448_to_901775360
import Theorems.Thm_syracuse_descent_coprime_to_six_901775360_to_914358272
import Theorems.Thm_syracuse_descent_coprime_to_six_914358272_to_926941184
import Theorems.Thm_syracuse_descent_coprime_to_six_926941184_to_939524096
import Theorems.Thm_syracuse_descent_coprime_to_six_939524096_to_952107008
import Theorems.Thm_syracuse_descent_coprime_to_six_952107008_to_964689920
import Theorems.Thm_syracuse_descent_coprime_to_six_964689920_to_977272832
import Theorems.Thm_syracuse_descent_coprime_to_six_977272832_to_989855744
import Theorems.Thm_syracuse_descent_coprime_to_six_989855744_to_1002438656
import Theorems.Thm_syracuse_descent_coprime_to_six_1002438656_to_1015021568
import Theorems.Thm_syracuse_descent_coprime_to_six_1015021568_to_1027604480
import Theorems.Thm_syracuse_descent_coprime_to_six_1027604480_to_1040187392
import Theorems.Thm_syracuse_descent_coprime_to_six_1040187392_to_1052770304
import Theorems.Thm_syracuse_descent_coprime_to_six_1052770304_to_1065353216
import Theorems.Thm_syracuse_descent_coprime_to_six_1065353216_to_1077936128
import Theorems.Thm_syracuse_descent_coprime_to_six_1077936128_to_1090519040
import Theorems.Thm_syracuse_descent_coprime_to_six_1090519040_to_1103101952
import Theorems.Thm_syracuse_descent_coprime_to_six_1103101952_to_1115684864
import Theorems.Thm_syracuse_descent_coprime_to_six_1115684864_to_1128267776
import Theorems.Thm_syracuse_descent_coprime_to_six_1128267776_to_1140850688
import Theorems.Thm_syracuse_descent_coprime_to_six_1140850688_to_1153433600
import Theorems.Thm_syracuse_descent_coprime_to_six_1153433600_to_1166016512
import Theorems.Thm_syracuse_descent_coprime_to_six_1166016512_to_1178599424
import Theorems.Thm_syracuse_descent_coprime_to_six_1178599424_to_1191182336
import Theorems.Thm_syracuse_descent_coprime_to_six_1191182336_to_1203765248
import Theorems.Thm_syracuse_descent_coprime_to_six_1203765248_to_1216348160
import Theorems.Thm_syracuse_descent_coprime_to_six_1216348160_to_1228931072
import Theorems.Thm_syracuse_descent_coprime_to_six_1228931072_to_1241513984
import Mathlib.Tactic.IntervalCases

/-
  The orbit-minimum argument is adapted from the accepted Prove2me solutions of
  syracuse_no_cycle_below_247463936 (theorem 61375da0, CGTMoyano) and
  syracuse_no_cycle_below_twenty_million_cutoff (theorem b5e0754a, immiq; Apache-2.0 via the
  Prove2me terms). Only the band list and the cutoff changed.
-/

set_option maxRecDepth 100000 in
private theorem band_descends (x : ℕ) (hl : 247463936 ≤ x) (hu : x < 1241513984)
    (hodd : ¬2 ∣ x) (hthree : ¬3 ∣ x) : ∃ t : ℕ, syracuseStep^[t] x < x := by
  have hq := Nat.div_add_mod (x - 247463936) 12582912
  have hr := Nat.mod_lt (x - 247463936) (show 0 < 12582912 by decide)
  generalize (x - 247463936) / 12582912 = k at hq
  generalize (x - 247463936) % 12582912 = r at hq hr
  have hk : k < 79 := by omega
  interval_cases k
  · exact syracuse_descent_coprime_to_six_247463936_to_260046848 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_260046848_to_272629760 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_272629760_to_285212672 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_285212672_to_297795584 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_297795584_to_310378496 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_310378496_to_322961408 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_322961408_to_335544320 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_335544320_to_348127232 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_348127232_to_360710144 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_360710144_to_373293056 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_373293056_to_385875968 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_385875968_to_398458880 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_398458880_to_411041792 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_411041792_to_423624704 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_423624704_to_436207616 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_436207616_to_448790528 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_448790528_to_461373440 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_461373440_to_473956352 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_473956352_to_486539264 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_486539264_to_499122176 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_499122176_to_511705088 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_511705088_to_524288000 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_524288000_to_536870912 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_536870912_to_549453824 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_549453824_to_562036736 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_562036736_to_574619648 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_574619648_to_587202560 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_587202560_to_599785472 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_599785472_to_612368384 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_612368384_to_624951296 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_624951296_to_637534208 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_637534208_to_650117120 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_650117120_to_662700032 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_662700032_to_675282944 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_675282944_to_687865856 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_687865856_to_700448768 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_700448768_to_713031680 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_713031680_to_725614592 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_725614592_to_738197504 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_738197504_to_750780416 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_750780416_to_763363328 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_763363328_to_775946240 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_775946240_to_788529152 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_788529152_to_801112064 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_801112064_to_813694976 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_813694976_to_826277888 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_826277888_to_838860800 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_838860800_to_851443712 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_851443712_to_864026624 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_864026624_to_876609536 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_876609536_to_889192448 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_889192448_to_901775360 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_901775360_to_914358272 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_914358272_to_926941184 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_926941184_to_939524096 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_939524096_to_952107008 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_952107008_to_964689920 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_964689920_to_977272832 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_977272832_to_989855744 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_989855744_to_1002438656 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_1002438656_to_1015021568 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_1015021568_to_1027604480 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_1027604480_to_1040187392 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_1040187392_to_1052770304 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_1052770304_to_1065353216 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_1065353216_to_1077936128 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_1077936128_to_1090519040 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_1090519040_to_1103101952 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_1103101952_to_1115684864 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_1115684864_to_1128267776 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_1128267776_to_1140850688 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_1140850688_to_1153433600 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_1153433600_to_1166016512 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_1166016512_to_1178599424 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_1178599424_to_1191182336 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_1191182336_to_1203765248 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_1203765248_to_1216348160 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_1216348160_to_1228931072 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_1228931072_to_1241513984 x (by omega) (by omega) hodd hthree

theorem solution (m p : ℕ) (hm : 0 < m) (hp : 0 < p) (hlt : m < 1241513984)
    (hcycle : syracuseStep^[p] m = m) : m = 1 := by
  let visited (z : ℕ) := ∃ i : ℕ, syracuseStep^[i] m = z
  have hex : ∃ z, visited z := ⟨m,0,rfl⟩
  classical
  let x := Nat.find hex
  obtain ⟨i,hi⟩ := (Nat.find_spec hex : visited x)
  change syracuseStep^[i] m = x at hi
  have xmin (j : ℕ) : x ≤ syracuseStep^[j] x := by
    apply Nat.find_min' hex
    exact ⟨j+i, by rw [Function.iterate_add_apply, hi]⟩
  have hle : x ≤ m := Nat.find_min' hex (show visited m from ⟨0,rfl⟩)
  have xpos : 0 < x := by
    rw [← hi]
    cases i with
    | zero => exact hm
    | succ j => rw [Function.iterate_succ_apply']; exact Nat.ordCompl_pos 2 (by omega)
  have xcycle : syracuseStep^[p] x = x := by
    rw [← hi, ← Function.iterate_add_apply, Nat.add_comm p i, Function.iterate_add_apply, hcycle]
  by_cases small : x < 247463936
  · exact syracuse_periodic_reaches_one m p hp hcycle
      ⟨i, hi.trans (syracuse_no_cycle_below_247463936 x p xpos hp small xcycle)⟩
  · obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
    let y := syracuseStep^[j] x
    have hy : syracuseStep y = x := by
      rw [hj, Function.iterate_succ_apply'] at xcycle
      exact xcycle
    have ho : ¬ 2 ∣ x := by
      rw [← hy]
      exact Nat.not_dvd_ordCompl Nat.prime_two (by omega : 3*y+1 ≠ 0)
    have h3 : ¬ 3 ∣ x := by
      intro hdiv
      have he : 2^((3*y+1).factorization 2)*x = 3*y+1 := by
        rw [← hy]
        exact Nat.ordProj_mul_ordCompl_eq_self _ _
      have hd : 3 ∣ 3*y+1 := he ▸ (dvd_mul_of_dvd_right hdiv (2^((3*y+1).factorization 2)))
      omega
    obtain ⟨t,ht⟩ := band_descends x (by omega) (by omega) ho h3
    exact False.elim (Nat.not_lt_of_ge (xmin t) ht)
