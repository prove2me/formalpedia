-- Prove2me | solution 1 for syracuse_descends_range_1202418_1204418
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:10:45.46862+00:00
-- url     : https://prove2.me/submissions/ca946ca7-1082-45a5-88dd-491219c47a04

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


theorem B1286161 : Blo 1202418 1286161 := bbase (se 2 (by rfl) ⟨482310, by rfl⟩ : syracuseStep 1286161 = 964621) (by norm_num)
theorem B3047453 : Blo 1202418 3047453 := bbase (se 3 (by rfl) ⟨571397, by rfl⟩ : syracuseStep 3047453 = 1142795) (by norm_num)
theorem B2285597 : Blo 1202418 2285597 := bbase (se 3 (by rfl) ⟨428549, by rfl⟩ : syracuseStep 2285597 = 857099) (by norm_num)
theorem B6504533 : Blo 1202418 6504533 := bbase (se 8 (by rfl) ⟨38112, by rfl⟩ : syracuseStep 6504533 = 76225) (by norm_num)
theorem B2031709 : Blo 1202418 2031709 := bbase (se 3 (by rfl) ⟨380945, by rfl⟩ : syracuseStep 2031709 = 761891) (by norm_num)
theorem B1302653 : Blo 1202418 1302653 := bbase (se 3 (by rfl) ⟨244247, by rfl⟩ : syracuseStep 1302653 = 488495) (by norm_num)
theorem B2891933 : Blo 1202418 2891933 := bbase (se 3 (by rfl) ⟨542237, by rfl⟩ : syracuseStep 2891933 = 1084475) (by norm_num)
theorem B1523873 : Blo 1202418 1523873 := bbase (se 2 (by rfl) ⟨571452, by rfl⟩ : syracuseStep 1523873 = 1142905) (by norm_num)
theorem B2285749 : Blo 1202418 2285749 := bbase (se 5 (by rfl) ⟨107144, by rfl⟩ : syracuseStep 2285749 = 214289) (by norm_num)
theorem B2031797 : Blo 1202418 2031797 := bbase (se 5 (by rfl) ⟨95240, by rfl⟩ : syracuseStep 2031797 = 190481) (by norm_num)
theorem B1736893 : Blo 1202418 1736893 := bbase (se 3 (by rfl) ⟨325667, by rfl⟩ : syracuseStep 1736893 = 651335) (by norm_num)
theorem B4063445 : Blo 1202418 4063445 := bbase (se 7 (by rfl) ⟨47618, by rfl⟩ : syracuseStep 4063445 = 95237) (by norm_num)
theorem B1523929 : Blo 1202418 1523929 := bbase (se 2 (by rfl) ⟨571473, by rfl⟩ : syracuseStep 1523929 = 1142947) (by norm_num)
theorem B3047645 : Blo 1202418 3047645 := bbase (se 3 (by rfl) ⟨571433, by rfl⟩ : syracuseStep 3047645 = 1142867) (by norm_num)
theorem B2031925 : Blo 1202418 2031925 := bbase (se 5 (by rfl) ⟨95246, by rfl⟩ : syracuseStep 2031925 = 190493) (by norm_num)
theorem B1524025 : Blo 1202418 1524025 := bbase (se 2 (by rfl) ⟨571509, by rfl⟩ : syracuseStep 1524025 = 1143019) (by norm_num)
theorem B2892133 : Blo 1202418 2892133 := bbase (se 4 (by rfl) ⟨271137, by rfl⟩ : syracuseStep 2892133 = 542275) (by norm_num)
theorem B2032013 : Blo 1202418 2032013 := bbase (se 3 (by rfl) ⟨381002, by rfl⟩ : syracuseStep 2032013 = 762005) (by norm_num)
theorem B5136853 : Blo 1202418 5136853 := bbase (se 7 (by rfl) ⟨60197, by rfl⟩ : syracuseStep 5136853 = 120395) (by norm_num)
theorem B2286053 : Blo 1202418 2286053 := bbase (se 4 (by rfl) ⟨214317, by rfl⟩ : syracuseStep 2286053 = 428635) (by norm_num)
theorem B1524197 : Blo 1202418 1524197 := bbase (se 4 (by rfl) ⟨142893, by rfl⟩ : syracuseStep 1524197 = 285787) (by norm_num)
theorem B2032141 : Blo 1202418 2032141 := bbase (se 3 (by rfl) ⟨381026, by rfl⟩ : syracuseStep 2032141 = 762053) (by norm_num)
theorem B1524253 : Blo 1202418 1524253 := bbase (se 3 (by rfl) ⟨285797, by rfl⟩ : syracuseStep 1524253 = 571595) (by norm_num)
theorem B3047989 : Blo 1202418 3047989 := bbase (se 5 (by rfl) ⟨142874, by rfl⟩ : syracuseStep 3047989 = 285749) (by norm_num)
theorem B9765461 : Blo 1202418 9765461 := bbase (se 8 (by rfl) ⟨57219, by rfl⟩ : syracuseStep 9765461 = 114439) (by norm_num)
theorem B2032229 : Blo 1202418 2032229 := bbase (se 4 (by rfl) ⟨190521, by rfl⟩ : syracuseStep 2032229 = 381043) (by norm_num)
theorem B4063877 : Blo 1202418 4063877 := bbase (se 4 (by rfl) ⟨380988, by rfl⟩ : syracuseStep 4063877 = 761977) (by norm_num)
theorem B3424933 : Blo 1202418 3424933 := bbase (se 4 (by rfl) ⟨321087, by rfl⟩ : syracuseStep 3424933 = 642175) (by norm_num)
theorem B3048101 : Blo 1202418 3048101 := bbase (se 4 (by rfl) ⟨285759, by rfl⟩ : syracuseStep 3048101 = 571519) (by norm_num)
theorem B6095573 : Blo 1202418 6095573 := bbase (se 7 (by rfl) ⟨71432, by rfl⟩ : syracuseStep 6095573 = 142865) (by norm_num)
theorem B3089117 : Blo 1202418 3089117 := bbase (se 3 (by rfl) ⟨579209, by rfl⟩ : syracuseStep 3089117 = 1158419) (by norm_num)
theorem B2032357 : Blo 1202418 2032357 := bbase (se 4 (by rfl) ⟨190533, by rfl⟩ : syracuseStep 2032357 = 381067) (by norm_num)
theorem B2745085 : Blo 1202418 2745085 := bbase (se 3 (by rfl) ⟨514703, by rfl⟩ : syracuseStep 2745085 = 1029407) (by norm_num)
theorem B4571909 : Blo 1202418 4571909 := bbase (se 4 (by rfl) ⟨428616, by rfl⟩ : syracuseStep 4571909 = 857233) (by norm_num)
theorem B1712917 : Blo 1202418 1712917 := bbase (se 6 (by rfl) ⟨40146, by rfl⟩ : syracuseStep 1712917 = 80293) (by norm_num)
theorem B2032445 : Blo 1202418 2032445 := bbase (se 3 (by rfl) ⟨381083, by rfl⟩ : syracuseStep 2032445 = 762167) (by norm_num)
theorem B3048293 : Blo 1202418 3048293 := bbase (se 4 (by rfl) ⟨285777, by rfl⟩ : syracuseStep 3048293 = 571555) (by norm_num)
theorem B1926109 : Blo 1202418 1926109 := bbase (se 3 (by rfl) ⟨361145, by rfl⟩ : syracuseStep 1926109 = 722291) (by norm_num)
theorem B4572197 : Blo 1202418 4572197 := bbase (se 4 (by rfl) ⟨428643, by rfl⟩ : syracuseStep 4572197 = 857287) (by norm_num)
theorem B1352749 : Blo 1202418 1352749 := bbase (se 3 (by rfl) ⟨253640, by rfl⟩ : syracuseStep 1352749 = 507281) (by norm_num)
theorem B4064309 : Blo 1202418 4064309 := bbase (se 5 (by rfl) ⟨190514, by rfl⟩ : syracuseStep 4064309 = 381029) (by norm_num)
theorem B1352785 : Blo 1202418 1352785 := bbase (se 2 (by rfl) ⟨507294, by rfl⟩ : syracuseStep 1352785 = 1014589) (by norm_num)
theorem B1713253 : Blo 1202418 1713253 := bbase (se 4 (by rfl) ⟨160617, by rfl⟩ : syracuseStep 1713253 = 321235) (by norm_num)
theorem B1352821 : Blo 1202418 1352821 := bbase (se 5 (by rfl) ⟨63413, by rfl⟩ : syracuseStep 1352821 = 126827) (by norm_num)
theorem B6087797 : Blo 1202418 6087797 := bbase (se 5 (by rfl) ⟨285365, by rfl⟩ : syracuseStep 6087797 = 570731) (by norm_num)
theorem B1926269 : Blo 1202418 1926269 := bbase (se 3 (by rfl) ⟨361175, by rfl⟩ : syracuseStep 1926269 = 722351) (by norm_num)
theorem B2892941 : Blo 1202418 2892941 := bbase (se 3 (by rfl) ⟨542426, by rfl⟩ : syracuseStep 2892941 = 1084853) (by norm_num)
theorem B4334741 : Blo 1202418 4334741 := bbase (se 6 (by rfl) ⟨101595, by rfl⟩ : syracuseStep 4334741 = 203191) (by norm_num)
theorem B1352857 : Blo 1202418 1352857 := bbase (se 2 (by rfl) ⟨507321, by rfl⟩ : syracuseStep 1352857 = 1014643) (by norm_num)
theorem B1352893 : Blo 1202418 1352893 := bbase (se 3 (by rfl) ⟨253667, by rfl⟩ : syracuseStep 1352893 = 507335) (by norm_num)
theorem B3048637 : Blo 1202418 3048637 := bbase (se 3 (by rfl) ⟨571619, by rfl⟩ : syracuseStep 3048637 = 1143239) (by norm_num)
theorem B1352929 : Blo 1202418 1352929 := bbase (se 2 (by rfl) ⟨507348, by rfl⟩ : syracuseStep 1352929 = 1014697) (by norm_num)
theorem B1352965 : Blo 1202418 1352965 := bbase (se 4 (by rfl) ⟨126840, by rfl⟩ : syracuseStep 1352965 = 253681) (by norm_num)
theorem B1353001 : Blo 1202418 1353001 := bbase (se 2 (by rfl) ⟨507375, by rfl⟩ : syracuseStep 1353001 = 1014751) (by norm_num)
theorem B6849845 : Blo 1202418 6849845 := bbase (se 5 (by rfl) ⟨321086, by rfl⟩ : syracuseStep 6849845 = 642173) (by norm_num)
theorem B1713469 : Blo 1202418 1713469 := bbase (se 3 (by rfl) ⟨321275, by rfl⟩ : syracuseStep 1713469 = 642551) (by norm_num)
theorem B1353037 : Blo 1202418 1353037 := bbase (se 3 (by rfl) ⟨253694, by rfl⟩ : syracuseStep 1353037 = 507389) (by norm_num)
theorem B10020181 : Blo 1202418 10020181 := bbase (se 12 (by rfl) ⟨3669, by rfl⟩ : syracuseStep 10020181 = 7339) (by norm_num)
theorem B3523925 : Blo 1202418 3523925 := bbase (se 12 (by rfl) ⟨1290, by rfl⟩ : syracuseStep 3523925 = 2581) (by norm_num)
theorem B1803629 : Blo 1202418 1803629 := bbase (se 3 (by rfl) ⟨338180, by rfl⟩ : syracuseStep 1803629 = 676361) (by norm_num)
theorem B1353073 : Blo 1202418 1353073 := bbase (se 2 (by rfl) ⟨507402, by rfl⟩ : syracuseStep 1353073 = 1014805) (by norm_num)
theorem B1803653 : Blo 1202418 1803653 := bbase (se 4 (by rfl) ⟨169092, by rfl⟩ : syracuseStep 1803653 = 338185) (by norm_num)
theorem B1353109 : Blo 1202418 1353109 := bbase (se 6 (by rfl) ⟨31713, by rfl⟩ : syracuseStep 1353109 = 63427) (by norm_num)
theorem B1803677 : Blo 1202418 1803677 := bbase (se 3 (by rfl) ⟨338189, by rfl⟩ : syracuseStep 1803677 = 676379) (by norm_num)
theorem B1803701 : Blo 1202418 1803701 := bbase (se 5 (by rfl) ⟨84548, by rfl⟩ : syracuseStep 1803701 = 169097) (by norm_num)
theorem B1353145 : Blo 1202418 1353145 := bbase (se 2 (by rfl) ⟨507429, by rfl⟩ : syracuseStep 1353145 = 1014859) (by norm_num)
theorem B1803725 : Blo 1202418 1803725 := bbase (se 3 (by rfl) ⟨338198, by rfl⟩ : syracuseStep 1803725 = 676397) (by norm_num)
theorem B1353181 : Blo 1202418 1353181 := bbase (se 3 (by rfl) ⟨253721, by rfl⟩ : syracuseStep 1353181 = 507443) (by norm_num)
theorem B1803749 : Blo 1202418 1803749 := bbase (se 4 (by rfl) ⟨169101, by rfl⟩ : syracuseStep 1803749 = 338203) (by norm_num)
theorem B4064741 : Blo 1202418 4064741 := bbase (se 4 (by rfl) ⟨381069, by rfl⟩ : syracuseStep 4064741 = 762139) (by norm_num)
theorem B1803773 : Blo 1202418 1803773 := bbase (se 3 (by rfl) ⟨338207, by rfl⟩ : syracuseStep 1803773 = 676415) (by norm_num)
theorem B1353217 : Blo 1202418 1353217 := bbase (se 2 (by rfl) ⟨507456, by rfl⟩ : syracuseStep 1353217 = 1014913) (by norm_num)
theorem B1803797 : Blo 1202418 1803797 := bbase (se 6 (by rfl) ⟨42276, by rfl⟩ : syracuseStep 1803797 = 84553) (by norm_num)
theorem B1353253 : Blo 1202418 1353253 := bbase (se 4 (by rfl) ⟨126867, by rfl⟩ : syracuseStep 1353253 = 253735) (by norm_num)
theorem B1803821 : Blo 1202418 1803821 := bbase (se 3 (by rfl) ⟨338216, by rfl⟩ : syracuseStep 1803821 = 676433) (by norm_num)
theorem B1803845 : Blo 1202418 1803845 := bbase (se 4 (by rfl) ⟨169110, by rfl⟩ : syracuseStep 1803845 = 338221) (by norm_num)
theorem B1353289 : Blo 1202418 1353289 := bbase (se 2 (by rfl) ⟨507483, by rfl⟩ : syracuseStep 1353289 = 1014967) (by norm_num)
theorem B1803869 : Blo 1202418 1803869 := bbase (se 3 (by rfl) ⟨338225, by rfl⟩ : syracuseStep 1803869 = 676451) (by norm_num)
theorem B1353325 : Blo 1202418 1353325 := bbase (se 3 (by rfl) ⟨253748, by rfl⟩ : syracuseStep 1353325 = 507497) (by norm_num)
theorem B1320557 : Blo 1202418 1320557 := bbase (se 3 (by rfl) ⟨247604, by rfl⟩ : syracuseStep 1320557 = 495209) (by norm_num)
theorem B1803893 : Blo 1202418 1803893 := bbase (se 5 (by rfl) ⟨84557, by rfl⟩ : syracuseStep 1803893 = 169115) (by norm_num)
theorem B1803917 : Blo 1202418 1803917 := bbase (se 3 (by rfl) ⟨338234, by rfl⟩ : syracuseStep 1803917 = 676469) (by norm_num)
theorem B1353361 : Blo 1202418 1353361 := bbase (se 2 (by rfl) ⟨507510, by rfl⟩ : syracuseStep 1353361 = 1015021) (by norm_num)
theorem B1803941 : Blo 1202418 1803941 := bbase (se 4 (by rfl) ⟨169119, by rfl⟩ : syracuseStep 1803941 = 338239) (by norm_num)
theorem B1353397 : Blo 1202418 1353397 := bbase (se 5 (by rfl) ⟨63440, by rfl⟩ : syracuseStep 1353397 = 126881) (by norm_num)
theorem B1713845 : Blo 1202418 1713845 := bbase (se 5 (by rfl) ⟨80336, by rfl⟩ : syracuseStep 1713845 = 160673) (by norm_num)
theorem B1803965 : Blo 1202418 1803965 := bbase (se 3 (by rfl) ⟨338243, by rfl⟩ : syracuseStep 1803965 = 676487) (by norm_num)
theorem B1803989 : Blo 1202418 1803989 := bbase (se 7 (by rfl) ⟨21140, by rfl⟩ : syracuseStep 1803989 = 42281) (by norm_num)
theorem B1353433 : Blo 1202418 1353433 := bbase (se 2 (by rfl) ⟨507537, by rfl⟩ : syracuseStep 1353433 = 1015075) (by norm_num)
theorem B1804013 : Blo 1202418 1804013 := bbase (se 3 (by rfl) ⟨338252, by rfl⟩ : syracuseStep 1804013 = 676505) (by norm_num)
theorem B1353469 : Blo 1202418 1353469 := bbase (se 3 (by rfl) ⟨253775, by rfl⟩ : syracuseStep 1353469 = 507551) (by norm_num)
theorem B1804037 : Blo 1202418 1804037 := bbase (se 4 (by rfl) ⟨169128, by rfl⟩ : syracuseStep 1804037 = 338257) (by norm_num)
theorem B1804061 : Blo 1202418 1804061 := bbase (se 3 (by rfl) ⟨338261, by rfl⟩ : syracuseStep 1804061 = 676523) (by norm_num)
theorem B1353505 : Blo 1202418 1353505 := bbase (se 2 (by rfl) ⟨507564, by rfl⟩ : syracuseStep 1353505 = 1015129) (by norm_num)
theorem B1828645 : Blo 1202418 1828645 := bbase (se 4 (by rfl) ⟨171435, by rfl⟩ : syracuseStep 1828645 = 342871) (by norm_num)
theorem B1804085 : Blo 1202418 1804085 := bbase (se 5 (by rfl) ⟨84566, by rfl⟩ : syracuseStep 1804085 = 169133) (by norm_num)
theorem B1353541 : Blo 1202418 1353541 := bbase (se 4 (by rfl) ⟨126894, by rfl⟩ : syracuseStep 1353541 = 253789) (by norm_num)
theorem B1804109 : Blo 1202418 1804109 := bbase (se 3 (by rfl) ⟨338270, by rfl⟩ : syracuseStep 1804109 = 676541) (by norm_num)
theorem B1804133 : Blo 1202418 1804133 := bbase (se 4 (by rfl) ⟨169137, by rfl⟩ : syracuseStep 1804133 = 338275) (by norm_num)
theorem B1353577 : Blo 1202418 1353577 := bbase (se 2 (by rfl) ⟨507591, by rfl⟩ : syracuseStep 1353577 = 1015183) (by norm_num)
theorem B1804157 : Blo 1202418 1804157 := bbase (se 3 (by rfl) ⟨338279, by rfl⟩ : syracuseStep 1804157 = 676559) (by norm_num)
theorem B1353613 : Blo 1202418 1353613 := bbase (se 3 (by rfl) ⟨253802, by rfl⟩ : syracuseStep 1353613 = 507605) (by norm_num)
theorem B2893709 : Blo 1202418 2893709 := bbase (se 3 (by rfl) ⟨542570, by rfl⟩ : syracuseStep 2893709 = 1085141) (by norm_num)
theorem B1804181 : Blo 1202418 1804181 := bbase (se 6 (by rfl) ⟨42285, by rfl⟩ : syracuseStep 1804181 = 84571) (by norm_num)
theorem B3475349 : Blo 1202418 3475349 := bbase (se 6 (by rfl) ⟨81453, by rfl⟩ : syracuseStep 3475349 = 162907) (by norm_num)
theorem B1804205 : Blo 1202418 1804205 := bbase (se 3 (by rfl) ⟨338288, by rfl⟩ : syracuseStep 1804205 = 676577) (by norm_num)
theorem B1353649 : Blo 1202418 1353649 := bbase (se 2 (by rfl) ⟨507618, by rfl⟩ : syracuseStep 1353649 = 1015237) (by norm_num)
theorem B1804229 : Blo 1202418 1804229 := bbase (se 4 (by rfl) ⟨169146, by rfl⟩ : syracuseStep 1804229 = 338293) (by norm_num)
theorem B1353685 : Blo 1202418 1353685 := bbase (se 7 (by rfl) ⟨15863, by rfl⟩ : syracuseStep 1353685 = 31727) (by norm_num)
theorem B1804253 : Blo 1202418 1804253 := bbase (se 3 (by rfl) ⟨338297, by rfl⟩ : syracuseStep 1804253 = 676595) (by norm_num)
theorem B6096869 : Blo 1202418 6096869 := bbase (se 4 (by rfl) ⟨571581, by rfl⟩ : syracuseStep 6096869 = 1143163) (by norm_num)
theorem B1804277 : Blo 1202418 1804277 := bbase (se 5 (by rfl) ⟨84575, by rfl⟩ : syracuseStep 1804277 = 169151) (by norm_num)
theorem B1353721 : Blo 1202418 1353721 := bbase (se 2 (by rfl) ⟨507645, by rfl⟩ : syracuseStep 1353721 = 1015291) (by norm_num)
theorem B1804301 : Blo 1202418 1804301 := bbase (se 3 (by rfl) ⟨338306, by rfl⟩ : syracuseStep 1804301 = 676613) (by norm_num)
theorem B1353757 : Blo 1202418 1353757 := bbase (se 3 (by rfl) ⟨253829, by rfl⟩ : syracuseStep 1353757 = 507659) (by norm_num)
theorem B1804325 : Blo 1202418 1804325 := bbase (se 4 (by rfl) ⟨169155, by rfl⟩ : syracuseStep 1804325 = 338311) (by norm_num)
theorem B2705453 : Blo 1202418 2705453 := bbase (se 3 (by rfl) ⟨507272, by rfl⟩ : syracuseStep 2705453 = 1014545) (by norm_num)
theorem B1804349 : Blo 1202418 1804349 := bbase (se 3 (by rfl) ⟨338315, by rfl⟩ : syracuseStep 1804349 = 676631) (by norm_num)
theorem B1353793 : Blo 1202418 1353793 := bbase (se 2 (by rfl) ⟨507672, by rfl⟩ : syracuseStep 1353793 = 1015345) (by norm_num)
theorem B1804373 : Blo 1202418 1804373 := bbase (se 8 (by rfl) ⟨10572, by rfl⟩ : syracuseStep 1804373 = 21145) (by norm_num)
theorem B1353829 : Blo 1202418 1353829 := bbase (se 4 (by rfl) ⟨126921, by rfl⟩ : syracuseStep 1353829 = 253843) (by norm_num)
theorem B1804397 : Blo 1202418 1804397 := bbase (se 3 (by rfl) ⟨338324, by rfl⟩ : syracuseStep 1804397 = 676649) (by norm_num)
theorem B2705525 : Blo 1202418 2705525 := bbase (se 5 (by rfl) ⟨126821, by rfl⟩ : syracuseStep 2705525 = 253643) (by norm_num)
theorem B1804421 : Blo 1202418 1804421 := bbase (se 4 (by rfl) ⟨169164, by rfl⟩ : syracuseStep 1804421 = 338329) (by norm_num)
theorem B3426437 : Blo 1202418 3426437 := bbase (se 4 (by rfl) ⟨321228, by rfl⟩ : syracuseStep 3426437 = 642457) (by norm_num)
theorem B1353865 : Blo 1202418 1353865 := bbase (se 2 (by rfl) ⟨507699, by rfl⟩ : syracuseStep 1353865 = 1015399) (by norm_num)
theorem B1804445 : Blo 1202418 1804445 := bbase (se 3 (by rfl) ⟨338333, by rfl⟩ : syracuseStep 1804445 = 676667) (by norm_num)
theorem B1353901 : Blo 1202418 1353901 := bbase (se 3 (by rfl) ⟨253856, by rfl⟩ : syracuseStep 1353901 = 507713) (by norm_num)
theorem B1804469 : Blo 1202418 1804469 := bbase (se 5 (by rfl) ⟨84584, by rfl⟩ : syracuseStep 1804469 = 169169) (by norm_num)
theorem B2705597 : Blo 1202418 2705597 := bbase (se 3 (by rfl) ⟨507299, by rfl⟩ : syracuseStep 2705597 = 1014599) (by norm_num)
theorem B1804493 : Blo 1202418 1804493 := bbase (se 3 (by rfl) ⟨338342, by rfl⟩ : syracuseStep 1804493 = 676685) (by norm_num)
theorem B1353937 : Blo 1202418 1353937 := bbase (se 2 (by rfl) ⟨507726, by rfl⟩ : syracuseStep 1353937 = 1015453) (by norm_num)
theorem B1804517 : Blo 1202418 1804517 := bbase (se 4 (by rfl) ⟨169173, by rfl⟩ : syracuseStep 1804517 = 338347) (by norm_num)
theorem B1927397 : Blo 1202418 1927397 := bbase (se 4 (by rfl) ⟨180693, by rfl⟩ : syracuseStep 1927397 = 361387) (by norm_num)
theorem B1353973 : Blo 1202418 1353973 := bbase (se 5 (by rfl) ⟨63467, by rfl⟩ : syracuseStep 1353973 = 126935) (by norm_num)
theorem B1804541 : Blo 1202418 1804541 := bbase (se 3 (by rfl) ⟨338351, by rfl⟩ : syracuseStep 1804541 = 676703) (by norm_num)
theorem B2705669 : Blo 1202418 2705669 := bbase (se 4 (by rfl) ⟨253656, by rfl⟩ : syracuseStep 2705669 = 507313) (by norm_num)
theorem B1804565 : Blo 1202418 1804565 := bbase (se 6 (by rfl) ⟨42294, by rfl⟩ : syracuseStep 1804565 = 84589) (by norm_num)
theorem B7710997 : Blo 1202418 7710997 := bbase (se 6 (by rfl) ⟨180726, by rfl⟩ : syracuseStep 7710997 = 361453) (by norm_num)
theorem B1354009 : Blo 1202418 1354009 := bbase (se 2 (by rfl) ⟨507753, by rfl⟩ : syracuseStep 1354009 = 1015507) (by norm_num)
theorem B1804589 : Blo 1202418 1804589 := bbase (se 3 (by rfl) ⟨338360, by rfl⟩ : syracuseStep 1804589 = 676721) (by norm_num)
theorem B1354045 : Blo 1202418 1354045 := bbase (se 3 (by rfl) ⟨253883, by rfl⟩ : syracuseStep 1354045 = 507767) (by norm_num)
theorem B1804613 : Blo 1202418 1804613 := bbase (se 4 (by rfl) ⟨169182, by rfl⟩ : syracuseStep 1804613 = 338365) (by norm_num)
theorem B2705741 : Blo 1202418 2705741 := bbase (se 3 (by rfl) ⟨507326, by rfl⟩ : syracuseStep 2705741 = 1014653) (by norm_num)
theorem B3852629 : Blo 1202418 3852629 := bbase (se 10 (by rfl) ⟨5643, by rfl⟩ : syracuseStep 3852629 = 11287) (by norm_num)
theorem B1804637 : Blo 1202418 1804637 := bbase (se 3 (by rfl) ⟨338369, by rfl⟩ : syracuseStep 1804637 = 676739) (by norm_num)
theorem B1354081 : Blo 1202418 1354081 := bbase (se 2 (by rfl) ⟨507780, by rfl⟩ : syracuseStep 1354081 = 1015561) (by norm_num)
theorem B1804661 : Blo 1202418 1804661 := bbase (se 5 (by rfl) ⟨84593, by rfl⟩ : syracuseStep 1804661 = 169187) (by norm_num)
theorem B6089093 : Blo 1202418 6089093 := bbase (se 4 (by rfl) ⟨570852, by rfl⟩ : syracuseStep 6089093 = 1141705) (by norm_num)
theorem B1354117 : Blo 1202418 1354117 := bbase (se 4 (by rfl) ⟨126948, by rfl⟩ : syracuseStep 1354117 = 253897) (by norm_num)
theorem B1804685 : Blo 1202418 1804685 := bbase (se 3 (by rfl) ⟨338378, by rfl⟩ : syracuseStep 1804685 = 676757) (by norm_num)
theorem B2705813 : Blo 1202418 2705813 := bbase (se 6 (by rfl) ⟨63417, by rfl⟩ : syracuseStep 2705813 = 126835) (by norm_num)
theorem B4114837 : Blo 1202418 4114837 := bbase (se 6 (by rfl) ⟨96441, by rfl⟩ : syracuseStep 4114837 = 192883) (by norm_num)
theorem B1804709 : Blo 1202418 1804709 := bbase (se 4 (by rfl) ⟨169191, by rfl⟩ : syracuseStep 1804709 = 338383) (by norm_num)
theorem B1354153 : Blo 1202418 1354153 := bbase (se 2 (by rfl) ⟨507807, by rfl⟩ : syracuseStep 1354153 = 1015615) (by norm_num)
theorem B1804733 : Blo 1202418 1804733 := bbase (se 3 (by rfl) ⟨338387, by rfl⟩ : syracuseStep 1804733 = 676775) (by norm_num)
theorem B1354189 : Blo 1202418 1354189 := bbase (se 3 (by rfl) ⟨253910, by rfl⟩ : syracuseStep 1354189 = 507821) (by norm_num)
theorem B1804757 : Blo 1202418 1804757 := bbase (se 7 (by rfl) ⟨21149, by rfl⟩ : syracuseStep 1804757 = 42299) (by norm_num)
theorem B2705885 : Blo 1202418 2705885 := bbase (se 3 (by rfl) ⟨507353, by rfl⟩ : syracuseStep 2705885 = 1014707) (by norm_num)
theorem B1804781 : Blo 1202418 1804781 := bbase (se 3 (by rfl) ⟨338396, by rfl⟩ : syracuseStep 1804781 = 676793) (by norm_num)
theorem B1354225 : Blo 1202418 1354225 := bbase (se 2 (by rfl) ⟨507834, by rfl⟩ : syracuseStep 1354225 = 1015669) (by norm_num)
theorem B1804805 : Blo 1202418 1804805 := bbase (se 4 (by rfl) ⟨169200, by rfl⟩ : syracuseStep 1804805 = 338401) (by norm_num)
theorem B2476565 : Blo 1202418 2476565 := bbase (se 6 (by rfl) ⟨58044, by rfl⟩ : syracuseStep 2476565 = 116089) (by norm_num)
theorem B1354261 : Blo 1202418 1354261 := bbase (se 6 (by rfl) ⟨31740, by rfl⟩ : syracuseStep 1354261 = 63481) (by norm_num)
theorem B1804829 : Blo 1202418 1804829 := bbase (se 3 (by rfl) ⟨338405, by rfl⟩ : syracuseStep 1804829 = 676811) (by norm_num)
theorem B2705957 : Blo 1202418 2705957 := bbase (se 4 (by rfl) ⟨253683, by rfl⟩ : syracuseStep 2705957 = 507367) (by norm_num)
theorem B4336181 : Blo 1202418 4336181 := bbase (se 5 (by rfl) ⟨203258, by rfl⟩ : syracuseStep 4336181 = 406517) (by norm_num)
theorem B1804853 : Blo 1202418 1804853 := bbase (se 5 (by rfl) ⟨84602, by rfl⟩ : syracuseStep 1804853 = 169205) (by norm_num)
theorem B1354297 : Blo 1202418 1354297 := bbase (se 2 (by rfl) ⟨507861, by rfl⟩ : syracuseStep 1354297 = 1015723) (by norm_num)
theorem B1804877 : Blo 1202418 1804877 := bbase (se 3 (by rfl) ⟨338414, by rfl⟩ : syracuseStep 1804877 = 676829) (by norm_num)
theorem B4115029 : Blo 1202418 4115029 := bbase (se 8 (by rfl) ⟨24111, by rfl⟩ : syracuseStep 4115029 = 48223) (by norm_num)
theorem B1354333 : Blo 1202418 1354333 := bbase (se 3 (by rfl) ⟨253937, by rfl⟩ : syracuseStep 1354333 = 507875) (by norm_num)
theorem B4565605 : Blo 1202418 4565605 := bbase (se 4 (by rfl) ⟨428025, by rfl⟩ : syracuseStep 4565605 = 856051) (by norm_num)
theorem B1804901 : Blo 1202418 1804901 := bbase (se 4 (by rfl) ⟨169209, by rfl⟩ : syracuseStep 1804901 = 338419) (by norm_num)
theorem B2706029 : Blo 1202418 2706029 := bbase (se 3 (by rfl) ⟨507380, by rfl⟩ : syracuseStep 2706029 = 1014761) (by norm_num)
theorem B1804925 : Blo 1202418 1804925 := bbase (se 3 (by rfl) ⟨338423, by rfl⟩ : syracuseStep 1804925 = 676847) (by norm_num)
theorem B1354369 : Blo 1202418 1354369 := bbase (se 2 (by rfl) ⟨507888, by rfl⟩ : syracuseStep 1354369 = 1015777) (by norm_num)
theorem B1804949 : Blo 1202418 1804949 := bbase (se 6 (by rfl) ⟨42303, by rfl⟩ : syracuseStep 1804949 = 84607) (by norm_num)
theorem B1354405 : Blo 1202418 1354405 := bbase (se 4 (by rfl) ⟨126975, by rfl⟩ : syracuseStep 1354405 = 253951) (by norm_num)
theorem B1804973 : Blo 1202418 1804973 := bbase (se 3 (by rfl) ⟨338432, by rfl⟩ : syracuseStep 1804973 = 676865) (by norm_num)
theorem B2706101 : Blo 1202418 2706101 := bbase (se 5 (by rfl) ⟨126848, by rfl⟩ : syracuseStep 2706101 = 253697) (by norm_num)
theorem B1804997 : Blo 1202418 1804997 := bbase (se 4 (by rfl) ⟨169218, by rfl⟩ : syracuseStep 1804997 = 338437) (by norm_num)
theorem B1354441 : Blo 1202418 1354441 := bbase (se 2 (by rfl) ⟨507915, by rfl⟩ : syracuseStep 1354441 = 1015831) (by norm_num)
theorem B1805021 : Blo 1202418 1805021 := bbase (se 3 (by rfl) ⟨338441, by rfl⟩ : syracuseStep 1805021 = 676883) (by norm_num)
theorem B1927909 : Blo 1202418 1927909 := bbase (se 4 (by rfl) ⟨180741, by rfl⟩ : syracuseStep 1927909 = 361483) (by norm_num)
theorem B1354477 : Blo 1202418 1354477 := bbase (se 3 (by rfl) ⟨253964, by rfl⟩ : syracuseStep 1354477 = 507929) (by norm_num)
theorem B1805045 : Blo 1202418 1805045 := bbase (se 5 (by rfl) ⟨84611, by rfl⟩ : syracuseStep 1805045 = 169223) (by norm_num)
theorem B2706173 : Blo 1202418 2706173 := bbase (se 3 (by rfl) ⟨507407, by rfl⟩ : syracuseStep 2706173 = 1014815) (by norm_num)
theorem B1805069 : Blo 1202418 1805069 := bbase (se 3 (by rfl) ⟨338450, by rfl⟩ : syracuseStep 1805069 = 676901) (by norm_num)
theorem B1354513 : Blo 1202418 1354513 := bbase (se 2 (by rfl) ⟨507942, by rfl⟩ : syracuseStep 1354513 = 1015885) (by norm_num)
theorem B1805093 : Blo 1202418 1805093 := bbase (se 4 (by rfl) ⟨169227, by rfl⟩ : syracuseStep 1805093 = 338455) (by norm_num)
theorem B1354549 : Blo 1202418 1354549 := bbase (se 5 (by rfl) ⟨63494, by rfl⟩ : syracuseStep 1354549 = 126989) (by norm_num)
theorem B1805117 : Blo 1202418 1805117 := bbase (se 3 (by rfl) ⟨338459, by rfl⟩ : syracuseStep 1805117 = 676919) (by norm_num)
theorem B1444673 : Blo 1202418 1444673 := bbase (se 2 (by rfl) ⟨541752, by rfl⟩ : syracuseStep 1444673 = 1083505) (by norm_num)
theorem B2706245 : Blo 1202418 2706245 := bbase (se 4 (by rfl) ⟨253710, by rfl⟩ : syracuseStep 2706245 = 507421) (by norm_num)
theorem B3132229 : Blo 1202418 3132229 := bbase (se 4 (by rfl) ⟨293646, by rfl⟩ : syracuseStep 3132229 = 587293) (by norm_num)
theorem B1805141 : Blo 1202418 1805141 := bbase (se 9 (by rfl) ⟨5288, by rfl⟩ : syracuseStep 1805141 = 10577) (by norm_num)
theorem B1354585 : Blo 1202418 1354585 := bbase (se 2 (by rfl) ⟨507969, by rfl⟩ : syracuseStep 1354585 = 1015939) (by norm_num)
theorem B1805165 : Blo 1202418 1805165 := bbase (se 3 (by rfl) ⟨338468, by rfl⟩ : syracuseStep 1805165 = 676937) (by norm_num)
theorem B1354621 : Blo 1202418 1354621 := bbase (se 3 (by rfl) ⟨253991, by rfl⟩ : syracuseStep 1354621 = 507983) (by norm_num)
theorem B1805189 : Blo 1202418 1805189 := bbase (se 4 (by rfl) ⟨169236, by rfl⟩ : syracuseStep 1805189 = 338473) (by norm_num)
theorem B2706317 : Blo 1202418 2706317 := bbase (se 3 (by rfl) ⟨507434, by rfl⟩ : syracuseStep 2706317 = 1014869) (by norm_num)
theorem B4565909 : Blo 1202418 4565909 := bbase (se 6 (by rfl) ⟨107013, by rfl⟩ : syracuseStep 4565909 = 214027) (by norm_num)
theorem B1805213 : Blo 1202418 1805213 := bbase (se 3 (by rfl) ⟨338477, by rfl⟩ : syracuseStep 1805213 = 676955) (by norm_num)
theorem B1354657 : Blo 1202418 1354657 := bbase (se 2 (by rfl) ⟨507996, by rfl⟩ : syracuseStep 1354657 = 1015993) (by norm_num)
theorem B1805237 : Blo 1202418 1805237 := bbase (se 5 (by rfl) ⟨84620, by rfl⟩ : syracuseStep 1805237 = 169241) (by norm_num)
theorem B1354693 : Blo 1202418 1354693 := bbase (se 4 (by rfl) ⟨127002, by rfl⟩ : syracuseStep 1354693 = 254005) (by norm_num)
theorem B1805261 : Blo 1202418 1805261 := bbase (se 3 (by rfl) ⟨338486, by rfl⟩ : syracuseStep 1805261 = 676973) (by norm_num)
theorem B2706389 : Blo 1202418 2706389 := bbase (se 7 (by rfl) ⟨31715, by rfl⟩ : syracuseStep 2706389 = 63431) (by norm_num)
theorem B1805285 : Blo 1202418 1805285 := bbase (se 4 (by rfl) ⟨169245, by rfl⟩ : syracuseStep 1805285 = 338491) (by norm_num)
theorem B1354729 : Blo 1202418 1354729 := bbase (se 2 (by rfl) ⟨508023, by rfl⟩ : syracuseStep 1354729 = 1016047) (by norm_num)
theorem B1805309 : Blo 1202418 1805309 := bbase (se 3 (by rfl) ⟨338495, by rfl⟩ : syracuseStep 1805309 = 676991) (by norm_num)
theorem B1354765 : Blo 1202418 1354765 := bbase (se 3 (by rfl) ⟨254018, by rfl⟩ : syracuseStep 1354765 = 508037) (by norm_num)
theorem B1805333 : Blo 1202418 1805333 := bbase (se 6 (by rfl) ⟨42312, by rfl⟩ : syracuseStep 1805333 = 84625) (by norm_num)
theorem B2706461 : Blo 1202418 2706461 := bbase (se 3 (by rfl) ⟨507461, by rfl⟩ : syracuseStep 2706461 = 1014923) (by norm_num)
theorem B1805357 : Blo 1202418 1805357 := bbase (se 3 (by rfl) ⟨338504, by rfl⟩ : syracuseStep 1805357 = 677009) (by norm_num)
theorem B1354801 : Blo 1202418 1354801 := bbase (se 2 (by rfl) ⟨508050, by rfl⟩ : syracuseStep 1354801 = 1016101) (by norm_num)
theorem B10275893 : Blo 1202418 10275893 := bbase (se 5 (by rfl) ⟨481682, by rfl⟩ : syracuseStep 10275893 = 963365) (by norm_num)
theorem B1805381 : Blo 1202418 1805381 := bbase (se 4 (by rfl) ⟨169254, by rfl⟩ : syracuseStep 1805381 = 338509) (by norm_num)
theorem B1354837 : Blo 1202418 1354837 := bbase (se 8 (by rfl) ⟨7938, by rfl⟩ : syracuseStep 1354837 = 15877) (by norm_num)
theorem B1805405 : Blo 1202418 1805405 := bbase (se 3 (by rfl) ⟨338513, by rfl⟩ : syracuseStep 1805405 = 677027) (by norm_num)
theorem B2174045 : Blo 1202418 2174045 := bbase (se 3 (by rfl) ⟨407633, by rfl⟩ : syracuseStep 2174045 = 815267) (by norm_num)
theorem B2706533 : Blo 1202418 2706533 := bbase (se 4 (by rfl) ⟨253737, by rfl⟩ : syracuseStep 2706533 = 507475) (by norm_num)
theorem B1444981 : Blo 1202418 1444981 := bbase (se 5 (by rfl) ⟨67733, by rfl⟩ : syracuseStep 1444981 = 135467) (by norm_num)
theorem B1805429 : Blo 1202418 1805429 := bbase (se 5 (by rfl) ⟨84629, by rfl⟩ : syracuseStep 1805429 = 169259) (by norm_num)
theorem B6261877 : Blo 1202418 6261877 := bbase (se 5 (by rfl) ⟨293525, by rfl⟩ : syracuseStep 6261877 = 587051) (by norm_num)
theorem B1354873 : Blo 1202418 1354873 := bbase (se 2 (by rfl) ⟨508077, by rfl⟩ : syracuseStep 1354873 = 1016155) (by norm_num)
theorem B1805453 : Blo 1202418 1805453 := bbase (se 3 (by rfl) ⟨338522, by rfl⟩ : syracuseStep 1805453 = 677045) (by norm_num)
theorem B1445009 : Blo 1202418 1445009 := bbase (se 2 (by rfl) ⟨541878, by rfl⟩ : syracuseStep 1445009 = 1083757) (by norm_num)
theorem B4058261 : Blo 1202418 4058261 := bbase (se 6 (by rfl) ⟨95115, by rfl⟩ : syracuseStep 4058261 = 190231) (by norm_num)
theorem B3910805 : Blo 1202418 3910805 := bbase (se 6 (by rfl) ⟨91659, by rfl⟩ : syracuseStep 3910805 = 183319) (by norm_num)
theorem B1354909 : Blo 1202418 1354909 := bbase (se 3 (by rfl) ⟨254045, by rfl⟩ : syracuseStep 1354909 = 508091) (by norm_num)
theorem B1805477 : Blo 1202418 1805477 := bbase (se 4 (by rfl) ⟨169263, by rfl⟩ : syracuseStep 1805477 = 338527) (by norm_num)
theorem B2706605 : Blo 1202418 2706605 := bbase (se 3 (by rfl) ⟨507488, by rfl⟩ : syracuseStep 2706605 = 1014977) (by norm_num)
theorem B1805501 : Blo 1202418 1805501 := bbase (se 3 (by rfl) ⟨338531, by rfl⟩ : syracuseStep 1805501 = 677063) (by norm_num)
theorem B1354945 : Blo 1202418 1354945 := bbase (se 2 (by rfl) ⟨508104, by rfl⟩ : syracuseStep 1354945 = 1016209) (by norm_num)
theorem B1805525 : Blo 1202418 1805525 := bbase (se 7 (by rfl) ⟨21158, by rfl⟩ : syracuseStep 1805525 = 42317) (by norm_num)
theorem B3255509 : Blo 1202418 3255509 := bbase (se 7 (by rfl) ⟨38150, by rfl⟩ : syracuseStep 3255509 = 76301) (by norm_num)
theorem B1805549 : Blo 1202418 1805549 := bbase (se 3 (by rfl) ⟨338540, by rfl⟩ : syracuseStep 1805549 = 677081) (by norm_num)
theorem B2706677 : Blo 1202418 2706677 := bbase (se 5 (by rfl) ⟨126875, by rfl⟩ : syracuseStep 2706677 = 253751) (by norm_num)
theorem B1805573 : Blo 1202418 1805573 := bbase (se 4 (by rfl) ⟨169272, by rfl⟩ : syracuseStep 1805573 = 338545) (by norm_num)
theorem B1805597 : Blo 1202418 1805597 := bbase (se 3 (by rfl) ⟨338549, by rfl⟩ : syracuseStep 1805597 = 677099) (by norm_num)
theorem B1805621 : Blo 1202418 1805621 := bbase (se 5 (by rfl) ⟨84638, by rfl⟩ : syracuseStep 1805621 = 169277) (by norm_num)
theorem B2706749 : Blo 1202418 2706749 := bbase (se 3 (by rfl) ⟨507515, by rfl⟩ : syracuseStep 2706749 = 1015031) (by norm_num)
theorem B1805645 : Blo 1202418 1805645 := bbase (se 3 (by rfl) ⟨338558, by rfl⟩ : syracuseStep 1805645 = 677117) (by norm_num)
theorem B1805669 : Blo 1202418 1805669 := bbase (se 4 (by rfl) ⟨169281, by rfl⟩ : syracuseStep 1805669 = 338563) (by norm_num)
theorem B1805693 : Blo 1202418 1805693 := bbase (se 3 (by rfl) ⟨338567, by rfl⟩ : syracuseStep 1805693 = 677135) (by norm_num)
theorem B2706821 : Blo 1202418 2706821 := bbase (se 4 (by rfl) ⟨253764, by rfl⟩ : syracuseStep 2706821 = 507529) (by norm_num)
theorem B5139845 : Blo 1202418 5139845 := bbase (se 4 (by rfl) ⟨481860, by rfl⟩ : syracuseStep 5139845 = 963721) (by norm_num)
theorem B1805717 : Blo 1202418 1805717 := bbase (se 6 (by rfl) ⟨42321, by rfl⟩ : syracuseStep 1805717 = 84643) (by norm_num)
theorem B1805741 : Blo 1202418 1805741 := bbase (se 3 (by rfl) ⟨338576, by rfl⟩ : syracuseStep 1805741 = 677153) (by norm_num)
theorem B1805765 : Blo 1202418 1805765 := bbase (se 4 (by rfl) ⟨169290, by rfl⟩ : syracuseStep 1805765 = 338581) (by norm_num)
theorem B2706893 : Blo 1202418 2706893 := bbase (se 3 (by rfl) ⟨507542, by rfl⟩ : syracuseStep 2706893 = 1015085) (by norm_num)
theorem B6852053 : Blo 1202418 6852053 := bbase (se 7 (by rfl) ⟨80297, by rfl⟩ : syracuseStep 6852053 = 160595) (by norm_num)
theorem B1805789 : Blo 1202418 1805789 := bbase (se 3 (by rfl) ⟨338585, by rfl⟩ : syracuseStep 1805789 = 677171) (by norm_num)
theorem B1805813 : Blo 1202418 1805813 := bbase (se 5 (by rfl) ⟨84647, by rfl⟩ : syracuseStep 1805813 = 169295) (by norm_num)
theorem B1805837 : Blo 1202418 1805837 := bbase (se 3 (by rfl) ⟨338594, by rfl⟩ : syracuseStep 1805837 = 677189) (by norm_num)
theorem B2706965 : Blo 1202418 2706965 := bbase (se 6 (by rfl) ⟨63444, by rfl⟩ : syracuseStep 2706965 = 126889) (by norm_num)
theorem B1805861 : Blo 1202418 1805861 := bbase (se 4 (by rfl) ⟨169299, by rfl⟩ : syracuseStep 1805861 = 338599) (by norm_num)
theorem B1805885 : Blo 1202418 1805885 := bbase (se 3 (by rfl) ⟨338603, by rfl⟩ : syracuseStep 1805885 = 677207) (by norm_num)
theorem B4058693 : Blo 1202418 4058693 := bbase (se 4 (by rfl) ⟨380502, by rfl⟩ : syracuseStep 4058693 = 761005) (by norm_num)
theorem B2059853 : Blo 1202418 2059853 := bbase (se 3 (by rfl) ⟨386222, by rfl⟩ : syracuseStep 2059853 = 772445) (by norm_num)
theorem B1805909 : Blo 1202418 1805909 := bbase (se 8 (by rfl) ⟨10581, by rfl⟩ : syracuseStep 1805909 = 21163) (by norm_num)
theorem B2707037 : Blo 1202418 2707037 := bbase (se 3 (by rfl) ⟨507569, by rfl⟩ : syracuseStep 2707037 = 1015139) (by norm_num)
theorem B1371749 : Blo 1202418 1371749 := bbase (se 4 (by rfl) ⟨128601, by rfl⟩ : syracuseStep 1371749 = 257203) (by norm_num)
theorem B1805933 : Blo 1202418 1805933 := bbase (se 3 (by rfl) ⟨338612, by rfl⟩ : syracuseStep 1805933 = 677225) (by norm_num)
theorem B1371773 : Blo 1202418 1371773 := bbase (se 3 (by rfl) ⟨257207, by rfl⟩ : syracuseStep 1371773 = 514415) (by norm_num)
theorem B1445509 : Blo 1202418 1445509 := bbase (se 4 (by rfl) ⟨135516, by rfl⟩ : syracuseStep 1445509 = 271033) (by norm_num)
theorem B1805957 : Blo 1202418 1805957 := bbase (se 4 (by rfl) ⟨169308, by rfl⟩ : syracuseStep 1805957 = 338617) (by norm_num)
theorem B3853973 : Blo 1202418 3853973 := bbase (se 6 (by rfl) ⟨90327, by rfl⟩ : syracuseStep 3853973 = 180655) (by norm_num)
theorem B6090389 : Blo 1202418 6090389 := bbase (se 6 (by rfl) ⟨142743, by rfl⟩ : syracuseStep 6090389 = 285487) (by norm_num)
theorem B1805981 : Blo 1202418 1805981 := bbase (se 3 (by rfl) ⟨338621, by rfl⟩ : syracuseStep 1805981 = 677243) (by norm_num)
theorem B2707109 : Blo 1202418 2707109 := bbase (se 4 (by rfl) ⟨253791, by rfl⟩ : syracuseStep 2707109 = 507583) (by norm_num)
theorem B3428021 : Blo 1202418 3428021 := bbase (se 5 (by rfl) ⟨160688, by rfl⟩ : syracuseStep 3428021 = 321377) (by norm_num)
theorem B1806005 : Blo 1202418 1806005 := bbase (se 5 (by rfl) ⟨84656, by rfl⟩ : syracuseStep 1806005 = 169313) (by norm_num)
theorem B1806029 : Blo 1202418 1806029 := bbase (se 3 (by rfl) ⟨338630, by rfl⟩ : syracuseStep 1806029 = 677261) (by norm_num)
theorem B1928909 : Blo 1202418 1928909 := bbase (se 3 (by rfl) ⟨361670, by rfl⟩ : syracuseStep 1928909 = 723341) (by norm_num)
theorem B4116197 : Blo 1202418 4116197 := bbase (se 4 (by rfl) ⟨385893, by rfl⟩ : syracuseStep 4116197 = 771787) (by norm_num)
theorem B1806053 : Blo 1202418 1806053 := bbase (se 4 (by rfl) ⟨169317, by rfl⟩ : syracuseStep 1806053 = 338635) (by norm_num)
theorem B2707181 : Blo 1202418 2707181 := bbase (se 3 (by rfl) ⟨507596, by rfl⟩ : syracuseStep 2707181 = 1015193) (by norm_num)
theorem B1806077 : Blo 1202418 1806077 := bbase (se 3 (by rfl) ⟨338639, by rfl⟩ : syracuseStep 1806077 = 677279) (by norm_num)
theorem B1806101 : Blo 1202418 1806101 := bbase (se 6 (by rfl) ⟨42330, by rfl⟩ : syracuseStep 1806101 = 84661) (by norm_num)
theorem B1806125 : Blo 1202418 1806125 := bbase (se 3 (by rfl) ⟨338648, by rfl⟩ : syracuseStep 1806125 = 677297) (by norm_num)
theorem B2707253 : Blo 1202418 2707253 := bbase (se 5 (by rfl) ⟨126902, by rfl⟩ : syracuseStep 2707253 = 253805) (by norm_num)
theorem B1806149 : Blo 1202418 1806149 := bbase (se 4 (by rfl) ⟨169326, by rfl⟩ : syracuseStep 1806149 = 338653) (by norm_num)
theorem B1929037 : Blo 1202418 1929037 := bbase (se 3 (by rfl) ⟨361694, by rfl⟩ : syracuseStep 1929037 = 723389) (by norm_num)
theorem B1806173 : Blo 1202418 1806173 := bbase (se 3 (by rfl) ⟨338657, by rfl⟩ : syracuseStep 1806173 = 677315) (by norm_num)
theorem B4337509 : Blo 1202418 4337509 := bbase (se 4 (by rfl) ⟨406641, by rfl⟩ : syracuseStep 4337509 = 813283) (by norm_num)
theorem B1806197 : Blo 1202418 1806197 := bbase (se 5 (by rfl) ⟨84665, by rfl⟩ : syracuseStep 1806197 = 169331) (by norm_num)
theorem B2707325 : Blo 1202418 2707325 := bbase (se 3 (by rfl) ⟨507623, by rfl⟩ : syracuseStep 2707325 = 1015247) (by norm_num)
theorem B1806221 : Blo 1202418 1806221 := bbase (se 3 (by rfl) ⟨338666, by rfl⟩ : syracuseStep 1806221 = 677333) (by norm_num)
theorem B1929101 : Blo 1202418 1929101 := bbase (se 3 (by rfl) ⟨361706, by rfl⟩ : syracuseStep 1929101 = 723413) (by norm_num)
theorem B1806245 : Blo 1202418 1806245 := bbase (se 4 (by rfl) ⟨169335, by rfl⟩ : syracuseStep 1806245 = 338671) (by norm_num)
theorem B1806269 : Blo 1202418 1806269 := bbase (se 3 (by rfl) ⟨338675, by rfl⟩ : syracuseStep 1806269 = 677351) (by norm_num)
theorem B2707397 : Blo 1202418 2707397 := bbase (se 4 (by rfl) ⟨253818, by rfl⟩ : syracuseStep 2707397 = 507637) (by norm_num)
theorem B1806293 : Blo 1202418 1806293 := bbase (se 7 (by rfl) ⟨21167, by rfl⟩ : syracuseStep 1806293 = 42335) (by norm_num)
theorem B1806317 : Blo 1202418 1806317 := bbase (se 3 (by rfl) ⟨338684, by rfl⟩ : syracuseStep 1806317 = 677369) (by norm_num)
theorem B4059125 : Blo 1202418 4059125 := bbase (se 5 (by rfl) ⟨190271, by rfl⟩ : syracuseStep 4059125 = 380543) (by norm_num)
theorem B1806341 : Blo 1202418 1806341 := bbase (se 4 (by rfl) ⟨169344, by rfl⟩ : syracuseStep 1806341 = 338689) (by norm_num)
theorem B2707469 : Blo 1202418 2707469 := bbase (se 3 (by rfl) ⟨507650, by rfl⟩ : syracuseStep 2707469 = 1015301) (by norm_num)
theorem B1806365 : Blo 1202418 1806365 := bbase (se 3 (by rfl) ⟨338693, by rfl⟩ : syracuseStep 1806365 = 677387) (by norm_num)
theorem B1806389 : Blo 1202418 1806389 := bbase (se 5 (by rfl) ⟨84674, by rfl⟩ : syracuseStep 1806389 = 169349) (by norm_num)
theorem B1806413 : Blo 1202418 1806413 := bbase (se 3 (by rfl) ⟨338702, by rfl⟩ : syracuseStep 1806413 = 677405) (by norm_num)
theorem B2707541 : Blo 1202418 2707541 := bbase (se 8 (by rfl) ⟨15864, by rfl⟩ : syracuseStep 2707541 = 31729) (by norm_num)
theorem B11751509 : Blo 1202418 11751509 := bbase (se 8 (by rfl) ⟨68856, by rfl⟩ : syracuseStep 11751509 = 137713) (by norm_num)
theorem B1806437 : Blo 1202418 1806437 := bbase (se 4 (by rfl) ⟨169353, by rfl⟩ : syracuseStep 1806437 = 338707) (by norm_num)
theorem B1806461 : Blo 1202418 1806461 := bbase (se 3 (by rfl) ⟨338711, by rfl⟩ : syracuseStep 1806461 = 677423) (by norm_num)
theorem B1806485 : Blo 1202418 1806485 := bbase (se 6 (by rfl) ⟨42339, by rfl⟩ : syracuseStep 1806485 = 84679) (by norm_num)
theorem B2707613 : Blo 1202418 2707613 := bbase (se 3 (by rfl) ⟨507677, by rfl⟩ : syracuseStep 2707613 = 1015355) (by norm_num)
theorem B1806509 : Blo 1202418 1806509 := bbase (se 3 (by rfl) ⟨338720, by rfl⟩ : syracuseStep 1806509 = 677441) (by norm_num)
theorem B1806533 : Blo 1202418 1806533 := bbase (se 4 (by rfl) ⟨169362, by rfl⟩ : syracuseStep 1806533 = 338725) (by norm_num)
theorem B1806557 : Blo 1202418 1806557 := bbase (se 3 (by rfl) ⟨338729, by rfl⟩ : syracuseStep 1806557 = 677459) (by norm_num)
theorem B2707685 : Blo 1202418 2707685 := bbase (se 4 (by rfl) ⟨253845, by rfl⟩ : syracuseStep 2707685 = 507691) (by norm_num)
theorem B1806581 : Blo 1202418 1806581 := bbase (se 5 (by rfl) ⟨84683, by rfl⟩ : syracuseStep 1806581 = 169367) (by norm_num)
theorem B1806605 : Blo 1202418 1806605 := bbase (se 3 (by rfl) ⟨338738, by rfl⟩ : syracuseStep 1806605 = 677477) (by norm_num)
theorem B12521749 : Blo 1202418 12521749 := bbase (se 6 (by rfl) ⟨293478, by rfl⟩ : syracuseStep 12521749 = 586957) (by norm_num)
theorem B2707757 : Blo 1202418 2707757 := bbase (se 3 (by rfl) ⟨507704, by rfl⟩ : syracuseStep 2707757 = 1015409) (by norm_num)
theorem B9761077 : Blo 1202418 9761077 := bbase (se 5 (by rfl) ⟨457550, by rfl⟩ : syracuseStep 9761077 = 915101) (by norm_num)
theorem B19501397 : Blo 1202418 19501397 := bbase (se 10 (by rfl) ⟨28566, by rfl⟩ : syracuseStep 19501397 = 57133) (by norm_num)
theorem B3658069 : Blo 1202418 3658069 := bbase (se 10 (by rfl) ⟨5358, by rfl⟩ : syracuseStep 3658069 = 10717) (by norm_num)
theorem B3428693 : Blo 1202418 3428693 := bbase (se 10 (by rfl) ⟨5022, by rfl⟩ : syracuseStep 3428693 = 10045) (by norm_num)
theorem B2707829 : Blo 1202418 2707829 := bbase (se 5 (by rfl) ⟨126929, by rfl⟩ : syracuseStep 2707829 = 253859) (by norm_num)
theorem B5140853 : Blo 1202418 5140853 := bbase (se 5 (by rfl) ⟨240977, by rfl⟩ : syracuseStep 5140853 = 481955) (by norm_num)
theorem B2568581 : Blo 1202418 2568581 := bbase (se 4 (by rfl) ⟨240804, by rfl⟩ : syracuseStep 2568581 = 481609) (by norm_num)
theorem B4059557 : Blo 1202418 4059557 := bbase (se 4 (by rfl) ⟨380583, by rfl⟩ : syracuseStep 4059557 = 761167) (by norm_num)
theorem B3043757 : Blo 1202418 3043757 := bbase (se 3 (by rfl) ⟨570704, by rfl⟩ : syracuseStep 3043757 = 1141409) (by norm_num)
theorem B2707901 : Blo 1202418 2707901 := bbase (se 3 (by rfl) ⟨507731, by rfl⟩ : syracuseStep 2707901 = 1015463) (by norm_num)
theorem B2707973 : Blo 1202418 2707973 := bbase (se 4 (by rfl) ⟨253872, by rfl⟩ : syracuseStep 2707973 = 507745) (by norm_num)
theorem B2708045 : Blo 1202418 2708045 := bbase (se 3 (by rfl) ⟨507758, by rfl⟩ : syracuseStep 2708045 = 1015517) (by norm_num)
theorem B2568829 : Blo 1202418 2568829 := bbase (se 3 (by rfl) ⟨481655, by rfl⟩ : syracuseStep 2568829 = 963311) (by norm_num)
theorem B2708117 : Blo 1202418 2708117 := bbase (se 6 (by rfl) ⟨63471, by rfl⟩ : syracuseStep 2708117 = 126943) (by norm_num)
theorem B2437805 : Blo 1202418 2437805 := bbase (se 3 (by rfl) ⟨457088, by rfl⟩ : syracuseStep 2437805 = 914177) (by norm_num)
theorem B4338373 : Blo 1202418 4338373 := bbase (se 4 (by rfl) ⟨406722, by rfl⟩ : syracuseStep 4338373 = 813445) (by norm_num)
theorem B2708189 : Blo 1202418 2708189 := bbase (se 3 (by rfl) ⟨507785, by rfl⟩ : syracuseStep 2708189 = 1015571) (by norm_num)
theorem B3044101 : Blo 1202418 3044101 := bbase (se 4 (by rfl) ⟨285384, by rfl⟩ : syracuseStep 3044101 = 570769) (by norm_num)
theorem B3429125 : Blo 1202418 3429125 := bbase (se 4 (by rfl) ⟨321480, by rfl⟩ : syracuseStep 3429125 = 642961) (by norm_num)
theorem B2167565 : Blo 1202418 2167565 := bbase (se 3 (by rfl) ⟨406418, by rfl⟩ : syracuseStep 2167565 = 812837) (by norm_num)
theorem B2708261 : Blo 1202418 2708261 := bbase (se 4 (by rfl) ⟨253899, by rfl⟩ : syracuseStep 2708261 = 507799) (by norm_num)
theorem B1446697 : Blo 1202418 1446697 := bbase (se 2 (by rfl) ⟨542511, by rfl⟩ : syracuseStep 1446697 = 1085023) (by norm_num)
theorem B4117301 : Blo 1202418 4117301 := bbase (se 5 (by rfl) ⟨192998, by rfl⟩ : syracuseStep 4117301 = 385997) (by norm_num)
theorem B4059989 : Blo 1202418 4059989 := bbase (se 9 (by rfl) ⟨11894, by rfl⟩ : syracuseStep 4059989 = 23789) (by norm_num)
theorem B2708333 : Blo 1202418 2708333 := bbase (se 3 (by rfl) ⟨507812, by rfl⟩ : syracuseStep 2708333 = 1015625) (by norm_num)
theorem B3044213 : Blo 1202418 3044213 := bbase (se 5 (by rfl) ⟨142697, by rfl⟩ : syracuseStep 3044213 = 285395) (by norm_num)
theorem B6091685 : Blo 1202418 6091685 := bbase (se 4 (by rfl) ⟨571095, by rfl⟩ : syracuseStep 6091685 = 1142191) (by norm_num)
theorem B2708405 : Blo 1202418 2708405 := bbase (se 5 (by rfl) ⟨126956, by rfl⟩ : syracuseStep 2708405 = 253913) (by norm_num)
theorem B4568021 : Blo 1202418 4568021 := bbase (se 7 (by rfl) ⟨53531, by rfl⟩ : syracuseStep 4568021 = 107063) (by norm_num)
theorem B1446889 : Blo 1202418 1446889 := bbase (se 2 (by rfl) ⟨542583, by rfl⟩ : syracuseStep 1446889 = 1085167) (by norm_num)
theorem B2929645 : Blo 1202418 2929645 := bbase (se 3 (by rfl) ⟨549308, by rfl⟩ : syracuseStep 2929645 = 1098617) (by norm_num)
theorem B2708477 : Blo 1202418 2708477 := bbase (se 3 (by rfl) ⟨507839, by rfl⟩ : syracuseStep 2708477 = 1015679) (by norm_num)
theorem B3855397 : Blo 1202418 3855397 := bbase (se 4 (by rfl) ⟨361443, by rfl⟩ : syracuseStep 3855397 = 722887) (by norm_num)
theorem B3044405 : Blo 1202418 3044405 := bbase (se 5 (by rfl) ⟨142706, by rfl⟩ : syracuseStep 3044405 = 285413) (by norm_num)
theorem B10417205 : Blo 1202418 10417205 := bbase (se 5 (by rfl) ⟨488306, by rfl⟩ : syracuseStep 10417205 = 976613) (by norm_num)
theorem B2708549 : Blo 1202418 2708549 := bbase (se 4 (by rfl) ⟨253926, by rfl⟩ : syracuseStep 2708549 = 507853) (by norm_num)
theorem B2569333 : Blo 1202418 2569333 := bbase (se 5 (by rfl) ⟨120437, by rfl⟩ : syracuseStep 2569333 = 240875) (by norm_num)
theorem B4338821 : Blo 1202418 4338821 := bbase (se 4 (by rfl) ⟨406764, by rfl⟩ : syracuseStep 4338821 = 813529) (by norm_num)
theorem B2708621 : Blo 1202418 2708621 := bbase (se 3 (by rfl) ⟨507866, by rfl⟩ : syracuseStep 2708621 = 1015733) (by norm_num)
theorem B2929829 : Blo 1202418 2929829 := bbase (se 4 (by rfl) ⟨274671, by rfl⟩ : syracuseStep 2929829 = 549343) (by norm_num)
theorem B1627333 : Blo 1202418 1627333 := bbase (se 4 (by rfl) ⟨152562, by rfl⟩ : syracuseStep 1627333 = 305125) (by norm_num)
theorem B2708693 : Blo 1202418 2708693 := bbase (se 7 (by rfl) ⟨31742, by rfl⟩ : syracuseStep 2708693 = 63485) (by norm_num)
theorem B4568309 : Blo 1202418 4568309 := bbase (se 5 (by rfl) ⟨214139, by rfl⟩ : syracuseStep 4568309 = 428279) (by norm_num)
theorem B4060421 : Blo 1202418 4060421 := bbase (se 4 (by rfl) ⟨380664, by rfl⟩ : syracuseStep 4060421 = 761329) (by norm_num)
theorem B4338949 : Blo 1202418 4338949 := bbase (se 4 (by rfl) ⟨406776, by rfl⟩ : syracuseStep 4338949 = 813553) (by norm_num)
theorem B2708765 : Blo 1202418 2708765 := bbase (se 3 (by rfl) ⟨507893, by rfl⟩ : syracuseStep 2708765 = 1015787) (by norm_num)
theorem B2168149 : Blo 1202418 2168149 := bbase (se 14 (by rfl) ⟨198, by rfl⟩ : syracuseStep 2168149 = 397) (by norm_num)
theorem B2708837 : Blo 1202418 2708837 := bbase (se 4 (by rfl) ⟨253953, by rfl⟩ : syracuseStep 2708837 = 507907) (by norm_num)
theorem B3044749 : Blo 1202418 3044749 := bbase (se 3 (by rfl) ⟨570890, by rfl⟩ : syracuseStep 3044749 = 1141781) (by norm_num)
theorem B2282917 : Blo 1202418 2282917 := bbase (se 4 (by rfl) ⟨214023, by rfl⟩ : syracuseStep 2282917 = 428047) (by norm_num)
theorem B2348453 : Blo 1202418 2348453 := bbase (se 4 (by rfl) ⟨220167, by rfl⟩ : syracuseStep 2348453 = 440335) (by norm_num)
theorem B2708909 : Blo 1202418 2708909 := bbase (se 3 (by rfl) ⟨507920, by rfl⟩ : syracuseStep 2708909 = 1015841) (by norm_num)
theorem B3659237 : Blo 1202418 3659237 := bbase (se 4 (by rfl) ⟨343053, by rfl⟩ : syracuseStep 3659237 = 686107) (by norm_num)
theorem B2708981 : Blo 1202418 2708981 := bbase (se 5 (by rfl) ⟨126983, by rfl⟩ : syracuseStep 2708981 = 253967) (by norm_num)
theorem B3044861 : Blo 1202418 3044861 := bbase (se 3 (by rfl) ⟨570911, by rfl⟩ : syracuseStep 3044861 = 1141823) (by norm_num)
theorem B2283061 : Blo 1202418 2283061 := bbase (se 5 (by rfl) ⟨107018, by rfl⟩ : syracuseStep 2283061 = 214037) (by norm_num)
theorem B2029117 : Blo 1202418 2029117 := bbase (se 3 (by rfl) ⟨380459, by rfl⟩ : syracuseStep 2029117 = 760919) (by norm_num)
theorem B2709053 : Blo 1202418 2709053 := bbase (se 3 (by rfl) ⟨507947, by rfl⟩ : syracuseStep 2709053 = 1015895) (by norm_num)
theorem B2709125 : Blo 1202418 2709125 := bbase (se 4 (by rfl) ⟨253980, by rfl⟩ : syracuseStep 2709125 = 507961) (by norm_num)
theorem B2029205 : Blo 1202418 2029205 := bbase (se 6 (by rfl) ⟨47559, by rfl⟩ : syracuseStep 2029205 = 95119) (by norm_num)
theorem B4060853 : Blo 1202418 4060853 := bbase (se 5 (by rfl) ⟨190352, by rfl⟩ : syracuseStep 4060853 = 380705) (by norm_num)
theorem B3045053 : Blo 1202418 3045053 := bbase (se 3 (by rfl) ⟨570947, by rfl⟩ : syracuseStep 3045053 = 1141895) (by norm_num)
theorem B2709197 : Blo 1202418 2709197 := bbase (se 3 (by rfl) ⟨507974, by rfl⟩ : syracuseStep 2709197 = 1015949) (by norm_num)
theorem B2283221 : Blo 1202418 2283221 := bbase (se 7 (by rfl) ⟨26756, by rfl⟩ : syracuseStep 2283221 = 53513) (by norm_num)
theorem B2029333 : Blo 1202418 2029333 := bbase (se 6 (by rfl) ⟨47562, by rfl⟩ : syracuseStep 2029333 = 95125) (by norm_num)
theorem B2709269 : Blo 1202418 2709269 := bbase (se 6 (by rfl) ⟨63498, by rfl⟩ : syracuseStep 2709269 = 126997) (by norm_num)
theorem B2709341 : Blo 1202418 2709341 := bbase (se 3 (by rfl) ⟨508001, by rfl⟩ : syracuseStep 2709341 = 1016003) (by norm_num)
theorem B2283365 : Blo 1202418 2283365 := bbase (se 4 (by rfl) ⟨214065, by rfl⟩ : syracuseStep 2283365 = 428131) (by norm_num)
theorem B2029421 : Blo 1202418 2029421 := bbase (se 3 (by rfl) ⟨380516, by rfl⟩ : syracuseStep 2029421 = 761033) (by norm_num)
theorem B2709413 : Blo 1202418 2709413 := bbase (se 4 (by rfl) ⟨254007, by rfl⟩ : syracuseStep 2709413 = 508015) (by norm_num)
theorem B2029549 : Blo 1202418 2029549 := bbase (se 3 (by rfl) ⟨380540, by rfl⟩ : syracuseStep 2029549 = 761081) (by norm_num)
theorem B2570221 : Blo 1202418 2570221 := bbase (se 3 (by rfl) ⟨481916, by rfl⟩ : syracuseStep 2570221 = 963833) (by norm_num)
theorem B2709485 : Blo 1202418 2709485 := bbase (se 3 (by rfl) ⟨508028, by rfl⟩ : syracuseStep 2709485 = 1016057) (by norm_num)
theorem B3045397 : Blo 1202418 3045397 := bbase (se 6 (by rfl) ⟨71376, by rfl⟩ : syracuseStep 3045397 = 142753) (by norm_num)
theorem B2709557 : Blo 1202418 2709557 := bbase (se 5 (by rfl) ⟨127010, by rfl⟩ : syracuseStep 2709557 = 254021) (by norm_num)
theorem B2029637 : Blo 1202418 2029637 := bbase (se 4 (by rfl) ⟨190278, by rfl⟩ : syracuseStep 2029637 = 380557) (by norm_num)
theorem B4061285 : Blo 1202418 4061285 := bbase (se 4 (by rfl) ⟨380745, by rfl⟩ : syracuseStep 4061285 = 761491) (by norm_num)
theorem B5142629 : Blo 1202418 5142629 := bbase (se 4 (by rfl) ⟨482121, by rfl⟩ : syracuseStep 5142629 = 964243) (by norm_num)
theorem B2709629 : Blo 1202418 2709629 := bbase (se 3 (by rfl) ⟨508055, by rfl⟩ : syracuseStep 2709629 = 1016111) (by norm_num)
theorem B2283653 : Blo 1202418 2283653 := bbase (se 4 (by rfl) ⟨214092, by rfl⟩ : syracuseStep 2283653 = 428185) (by norm_num)
theorem B3045509 : Blo 1202418 3045509 := bbase (se 4 (by rfl) ⟨285516, by rfl⟩ : syracuseStep 3045509 = 571033) (by norm_num)
theorem B3709093 : Blo 1202418 3709093 := bbase (se 4 (by rfl) ⟨347727, by rfl⟩ : syracuseStep 3709093 = 695455) (by norm_num)
theorem B1284265 : Blo 1202418 1284265 := bbase (se 2 (by rfl) ⟨481599, by rfl⟩ : syracuseStep 1284265 = 963199) (by norm_num)
theorem B6092981 : Blo 1202418 6092981 := bbase (se 5 (by rfl) ⟨285608, by rfl⟩ : syracuseStep 6092981 = 571217) (by norm_num)
theorem B2029765 : Blo 1202418 2029765 := bbase (se 4 (by rfl) ⟨190290, by rfl⟩ : syracuseStep 2029765 = 380581) (by norm_num)
theorem B2709701 : Blo 1202418 2709701 := bbase (se 4 (by rfl) ⟨254034, by rfl⟩ : syracuseStep 2709701 = 508069) (by norm_num)
theorem B11565301 : Blo 1202418 11565301 := bbase (se 5 (by rfl) ⟨542123, by rfl⟩ : syracuseStep 11565301 = 1084247) (by norm_num)
theorem B1521929 : Blo 1202418 1521929 := bbase (se 2 (by rfl) ⟨570723, by rfl⟩ : syracuseStep 1521929 = 1141447) (by norm_num)
theorem B2709773 : Blo 1202418 2709773 := bbase (se 3 (by rfl) ⟨508082, by rfl⟩ : syracuseStep 2709773 = 1016165) (by norm_num)
theorem B2029853 : Blo 1202418 2029853 := bbase (se 3 (by rfl) ⟨380597, by rfl⟩ : syracuseStep 2029853 = 761195) (by norm_num)
theorem B2283805 : Blo 1202418 2283805 := bbase (se 3 (by rfl) ⟨428213, by rfl⟩ : syracuseStep 2283805 = 856427) (by norm_num)
theorem B3299621 : Blo 1202418 3299621 := bbase (se 4 (by rfl) ⟨309339, by rfl⟩ : syracuseStep 3299621 = 618679) (by norm_num)
theorem B1521985 : Blo 1202418 1521985 := bbase (se 2 (by rfl) ⟨570744, by rfl⟩ : syracuseStep 1521985 = 1141489) (by norm_num)
theorem B3045701 : Blo 1202418 3045701 := bbase (se 4 (by rfl) ⟨285534, by rfl⟩ : syracuseStep 3045701 = 571069) (by norm_num)
theorem B2709845 : Blo 1202418 2709845 := bbase (se 10 (by rfl) ⟨3969, by rfl⟩ : syracuseStep 2709845 = 7939) (by norm_num)
theorem B4569493 : Blo 1202418 4569493 := bbase (se 6 (by rfl) ⟨107097, by rfl⟩ : syracuseStep 4569493 = 214195) (by norm_num)
theorem B2029981 : Blo 1202418 2029981 := bbase (se 3 (by rfl) ⟨380621, by rfl⟩ : syracuseStep 2029981 = 761243) (by norm_num)
theorem B2709917 : Blo 1202418 2709917 := bbase (se 3 (by rfl) ⟨508109, by rfl⟩ : syracuseStep 2709917 = 1016219) (by norm_num)
theorem B1522081 : Blo 1202418 1522081 := bbase (se 2 (by rfl) ⟨570780, by rfl⟩ : syracuseStep 1522081 = 1141561) (by norm_num)
theorem B2570717 : Blo 1202418 2570717 := bbase (se 3 (by rfl) ⟨482009, by rfl⟩ : syracuseStep 2570717 = 964019) (by norm_num)
theorem B2169317 : Blo 1202418 2169317 := bbase (se 4 (by rfl) ⟨203373, by rfl⟩ : syracuseStep 2169317 = 406747) (by norm_num)
theorem B7707125 : Blo 1202418 7707125 := bbase (se 5 (by rfl) ⟨361271, by rfl⟩ : syracuseStep 7707125 = 722543) (by norm_num)
theorem B2030069 : Blo 1202418 2030069 := bbase (se 5 (by rfl) ⟨95159, by rfl⟩ : syracuseStep 2030069 = 190319) (by norm_num)
theorem B3389957 : Blo 1202418 3389957 := bbase (se 4 (by rfl) ⟨317808, by rfl⟩ : syracuseStep 3389957 = 635617) (by norm_num)
theorem B1219081 : Blo 1202418 1219081 := bbase (se 2 (by rfl) ⟨457155, by rfl⟩ : syracuseStep 1219081 = 914311) (by norm_num)
theorem B4061717 : Blo 1202418 4061717 := bbase (se 6 (by rfl) ⟨95196, by rfl⟩ : syracuseStep 4061717 = 190393) (by norm_num)
theorem B1522253 : Blo 1202418 1522253 := bbase (se 3 (by rfl) ⟨285422, by rfl⟩ : syracuseStep 1522253 = 570845) (by norm_num)
theorem B2284109 : Blo 1202418 2284109 := bbase (se 3 (by rfl) ⟨428270, by rfl⟩ : syracuseStep 2284109 = 856541) (by norm_num)
theorem B1284709 : Blo 1202418 1284709 := bbase (se 4 (by rfl) ⟨120441, by rfl⟩ : syracuseStep 1284709 = 240883) (by norm_num)
theorem B3856997 : Blo 1202418 3856997 := bbase (se 4 (by rfl) ⟨361593, by rfl⟩ : syracuseStep 3856997 = 723187) (by norm_num)
theorem B2030197 : Blo 1202418 2030197 := bbase (se 5 (by rfl) ⟨95165, by rfl⟩ : syracuseStep 2030197 = 190331) (by norm_num)
theorem B1522309 : Blo 1202418 1522309 := bbase (se 4 (by rfl) ⟨142716, by rfl⟩ : syracuseStep 1522309 = 285433) (by norm_num)
theorem B3046045 : Blo 1202418 3046045 := bbase (se 3 (by rfl) ⟨571133, by rfl⟩ : syracuseStep 3046045 = 1142267) (by norm_num)
theorem B1284769 : Blo 1202418 1284769 := bbase (se 2 (by rfl) ⟨481788, by rfl⟩ : syracuseStep 1284769 = 963577) (by norm_num)
theorem B4569797 : Blo 1202418 4569797 := bbase (se 4 (by rfl) ⟨428418, by rfl⟩ : syracuseStep 4569797 = 856837) (by norm_num)
theorem B2030285 : Blo 1202418 2030285 := bbase (se 3 (by rfl) ⟨380678, by rfl⟩ : syracuseStep 2030285 = 761357) (by norm_num)
theorem B1522405 : Blo 1202418 1522405 := bbase (se 4 (by rfl) ⟨142725, by rfl⟩ : syracuseStep 1522405 = 285451) (by norm_num)
theorem B8674037 : Blo 1202418 8674037 := bbase (se 5 (by rfl) ⟨406595, by rfl⟩ : syracuseStep 8674037 = 813191) (by norm_num)
theorem B3046157 : Blo 1202418 3046157 := bbase (se 3 (by rfl) ⟨571154, by rfl⟩ : syracuseStep 3046157 = 1142309) (by norm_num)
theorem B1391413 : Blo 1202418 1391413 := bbase (se 5 (by rfl) ⟨65222, by rfl⟩ : syracuseStep 1391413 = 130445) (by norm_num)
theorem B2030413 : Blo 1202418 2030413 := bbase (se 3 (by rfl) ⟨380702, by rfl⟩ : syracuseStep 2030413 = 761405) (by norm_num)
theorem B1522577 : Blo 1202418 1522577 := bbase (se 2 (by rfl) ⟨570966, by rfl⟩ : syracuseStep 1522577 = 1141933) (by norm_num)
theorem B5782421 : Blo 1202418 5782421 := bbase (se 6 (by rfl) ⟨135525, by rfl⟩ : syracuseStep 5782421 = 271051) (by norm_num)
theorem B2169757 : Blo 1202418 2169757 := bbase (se 3 (by rfl) ⟨406829, by rfl⟩ : syracuseStep 2169757 = 813659) (by norm_num)
theorem B2030501 : Blo 1202418 2030501 := bbase (se 4 (by rfl) ⟨190359, by rfl⟩ : syracuseStep 2030501 = 380719) (by norm_num)
theorem B9141173 : Blo 1202418 9141173 := bbase (se 5 (by rfl) ⟨428492, by rfl⟩ : syracuseStep 9141173 = 856985) (by norm_num)
theorem B4062149 : Blo 1202418 4062149 := bbase (se 4 (by rfl) ⟨380826, by rfl⟩ : syracuseStep 4062149 = 761653) (by norm_num)
theorem B1522633 : Blo 1202418 1522633 := bbase (se 2 (by rfl) ⟨570987, by rfl⟩ : syracuseStep 1522633 = 1141975) (by norm_num)
theorem B3046349 : Blo 1202418 3046349 := bbase (se 3 (by rfl) ⟨571190, by rfl⟩ : syracuseStep 3046349 = 1142381) (by norm_num)
theorem B1285085 : Blo 1202418 1285085 := bbase (se 3 (by rfl) ⟨240953, by rfl⟩ : syracuseStep 1285085 = 481907) (by norm_num)
theorem B2169821 : Blo 1202418 2169821 := bbase (se 3 (by rfl) ⟨406841, by rfl⟩ : syracuseStep 2169821 = 813683) (by norm_num)
theorem B2030629 : Blo 1202418 2030629 := bbase (se 4 (by rfl) ⟨190371, by rfl⟩ : syracuseStep 2030629 = 380743) (by norm_num)
theorem B1522729 : Blo 1202418 1522729 := bbase (se 2 (by rfl) ⟨571023, by rfl⟩ : syracuseStep 1522729 = 1142047) (by norm_num)
theorem B1219645 : Blo 1202418 1219645 := bbase (se 3 (by rfl) ⟨228683, by rfl⟩ : syracuseStep 1219645 = 457367) (by norm_num)
theorem B15416405 : Blo 1202418 15416405 := bbase (se 8 (by rfl) ⟨90330, by rfl⟩ : syracuseStep 15416405 = 180661) (by norm_num)
theorem B2030717 : Blo 1202418 2030717 := bbase (se 3 (by rfl) ⟨380759, by rfl⟩ : syracuseStep 2030717 = 761519) (by norm_num)
theorem B1236125 : Blo 1202418 1236125 := bbase (se 3 (by rfl) ⟨231773, by rfl⟩ : syracuseStep 1236125 = 463547) (by norm_num)
theorem B2604197 : Blo 1202418 2604197 := bbase (se 4 (by rfl) ⟨244143, by rfl⟩ : syracuseStep 2604197 = 488287) (by norm_num)
theorem B1522901 : Blo 1202418 1522901 := bbase (se 7 (by rfl) ⟨17846, by rfl⟩ : syracuseStep 1522901 = 35693) (by norm_num)
theorem B2030845 : Blo 1202418 2030845 := bbase (se 3 (by rfl) ⟨380783, by rfl⟩ : syracuseStep 2030845 = 761567) (by norm_num)
theorem B2170109 : Blo 1202418 2170109 := bbase (se 3 (by rfl) ⟨406895, by rfl⟩ : syracuseStep 2170109 = 813791) (by norm_num)
theorem B1522957 : Blo 1202418 1522957 := bbase (se 3 (by rfl) ⟨285554, by rfl⟩ : syracuseStep 1522957 = 571109) (by norm_num)
theorem B5782805 : Blo 1202418 5782805 := bbase (se 6 (by rfl) ⟨135534, by rfl⟩ : syracuseStep 5782805 = 271069) (by norm_num)
theorem B3046693 : Blo 1202418 3046693 := bbase (se 4 (by rfl) ⟨285627, by rfl⟩ : syracuseStep 3046693 = 571255) (by norm_num)
theorem B2284861 : Blo 1202418 2284861 := bbase (se 3 (by rfl) ⟨428411, by rfl⟩ : syracuseStep 2284861 = 856823) (by norm_num)
theorem B9133397 : Blo 1202418 9133397 := bbase (se 11 (by rfl) ⟨6689, by rfl⟩ : syracuseStep 9133397 = 13379) (by norm_num)
theorem B2030933 : Blo 1202418 2030933 := bbase (se 11 (by rfl) ⟨1487, by rfl⟩ : syracuseStep 2030933 = 2975) (by norm_num)
theorem B2571605 : Blo 1202418 2571605 := bbase (se 11 (by rfl) ⟨1883, by rfl⟩ : syracuseStep 2571605 = 3767) (by norm_num)
theorem B1523053 : Blo 1202418 1523053 := bbase (se 3 (by rfl) ⟨285572, by rfl⟩ : syracuseStep 1523053 = 571145) (by norm_num)
theorem B4062581 : Blo 1202418 4062581 := bbase (se 5 (by rfl) ⟨190433, by rfl⟩ : syracuseStep 4062581 = 380867) (by norm_num)
theorem B3046805 : Blo 1202418 3046805 := bbase (se 6 (by rfl) ⟨71409, by rfl⟩ : syracuseStep 3046805 = 142819) (by norm_num)
theorem B1285529 : Blo 1202418 1285529 := bbase (se 2 (by rfl) ⟨482073, by rfl⟩ : syracuseStep 1285529 = 964147) (by norm_num)
theorem B1465777 : Blo 1202418 1465777 := bbase (se 2 (by rfl) ⟨549666, by rfl⟩ : syracuseStep 1465777 = 1099333) (by norm_num)
theorem B6094277 : Blo 1202418 6094277 := bbase (se 4 (by rfl) ⟨571338, by rfl⟩ : syracuseStep 6094277 = 1142677) (by norm_num)
theorem B2285005 : Blo 1202418 2285005 := bbase (se 3 (by rfl) ⟨428438, by rfl⟩ : syracuseStep 2285005 = 856877) (by norm_num)
theorem B2571725 : Blo 1202418 2571725 := bbase (se 3 (by rfl) ⟨482198, by rfl⟩ : syracuseStep 2571725 = 964397) (by norm_num)
theorem B2031061 : Blo 1202418 2031061 := bbase (se 7 (by rfl) ⟨23801, by rfl⟩ : syracuseStep 2031061 = 47603) (by norm_num)
theorem B1285589 : Blo 1202418 1285589 := bbase (se 7 (by rfl) ⟨15065, by rfl⟩ : syracuseStep 1285589 = 30131) (by norm_num)
theorem B1523225 : Blo 1202418 1523225 := bbase (se 2 (by rfl) ⟨571209, by rfl⟩ : syracuseStep 1523225 = 1142419) (by norm_num)
theorem B2031149 : Blo 1202418 2031149 := bbase (se 3 (by rfl) ⟨380840, by rfl⟩ : syracuseStep 2031149 = 761681) (by norm_num)
theorem B2891317 : Blo 1202418 2891317 := bbase (se 5 (by rfl) ⟨135530, by rfl⟩ : syracuseStep 2891317 = 271061) (by norm_num)
theorem B1523281 : Blo 1202418 1523281 := bbase (se 2 (by rfl) ⟨571230, by rfl⟩ : syracuseStep 1523281 = 1142461) (by norm_num)
theorem B4628053 : Blo 1202418 4628053 := bbase (se 8 (by rfl) ⟨27117, by rfl⟩ : syracuseStep 4628053 = 54235) (by norm_num)
theorem B18775637 : Blo 1202418 18775637 := bbase (se 8 (by rfl) ⟨110013, by rfl⟩ : syracuseStep 18775637 = 220027) (by norm_num)
theorem B3046997 : Blo 1202418 3046997 := bbase (se 8 (by rfl) ⟨17853, by rfl⟩ : syracuseStep 3046997 = 35707) (by norm_num)
theorem B1285717 : Blo 1202418 1285717 := bbase (se 8 (by rfl) ⟨7533, by rfl⟩ : syracuseStep 1285717 = 15067) (by norm_num)
theorem B2285165 : Blo 1202418 2285165 := bbase (se 3 (by rfl) ⟨428468, by rfl⟩ : syracuseStep 2285165 = 856937) (by norm_num)
theorem B2031277 : Blo 1202418 2031277 := bbase (se 3 (by rfl) ⟨380864, by rfl⟩ : syracuseStep 2031277 = 761729) (by norm_num)
theorem B1523377 : Blo 1202418 1523377 := bbase (se 2 (by rfl) ⟨571266, by rfl⟩ : syracuseStep 1523377 = 1142533) (by norm_num)
theorem B3858101 : Blo 1202418 3858101 := bbase (se 5 (by rfl) ⟨180848, by rfl⟩ : syracuseStep 3858101 = 361697) (by norm_num)
theorem B1220297 : Blo 1202418 1220297 := bbase (se 2 (by rfl) ⟨457611, by rfl⟩ : syracuseStep 1220297 = 915223) (by norm_num)
theorem B2285309 : Blo 1202418 2285309 := bbase (se 3 (by rfl) ⟨428495, by rfl⟩ : syracuseStep 2285309 = 856991) (by norm_num)
theorem B2031365 : Blo 1202418 2031365 := bbase (se 4 (by rfl) ⟨190440, by rfl⟩ : syracuseStep 2031365 = 380881) (by norm_num)
theorem B4063013 : Blo 1202418 4063013 := bbase (se 4 (by rfl) ⟨380907, by rfl⟩ : syracuseStep 4063013 = 761815) (by norm_num)
theorem B1523549 : Blo 1202418 1523549 := bbase (se 3 (by rfl) ⟨285665, by rfl⟩ : syracuseStep 1523549 = 571331) (by norm_num)
theorem B2031493 : Blo 1202418 2031493 := bbase (se 4 (by rfl) ⟨190452, by rfl⟩ : syracuseStep 2031493 = 380905) (by norm_num)
theorem B1523605 : Blo 1202418 1523605 := bbase (se 6 (by rfl) ⟨35709, by rfl⟩ : syracuseStep 1523605 = 71419) (by norm_num)
theorem B3047341 : Blo 1202418 3047341 := bbase (se 3 (by rfl) ⟨571376, by rfl⟩ : syracuseStep 3047341 = 1142753) (by norm_num)
theorem B8339381 : Blo 1202418 8339381 := bbase (se 5 (by rfl) ⟨390908, by rfl⟩ : syracuseStep 8339381 = 781817) (by norm_num)
theorem B1220557 : Blo 1202418 1220557 := bbase (se 3 (by rfl) ⟨228854, by rfl⟩ : syracuseStep 1220557 = 457709) (by norm_num)
theorem B2031581 : Blo 1202418 2031581 := bbase (se 3 (by rfl) ⟨380921, by rfl⟩ : syracuseStep 2031581 = 761843) (by norm_num)
theorem B1523701 : Blo 1202418 1523701 := bbase (se 5 (by rfl) ⟨71423, by rfl⟩ : syracuseStep 1523701 = 142847) (by norm_num)
theorem B1712125 : Blo 1202418 1712125 := bbase (se 3 (by rfl) ⟨321023, by rfl⟩ : syracuseStep 1712125 = 642047) (by norm_num)
theorem B1204227 : Blo 1202418 1204227 := bstep (se 1 (by rfl) ⟨903170, by rfl⟩ : syracuseStep 1204227 = 1806341) B1806341
theorem B2031635 : Blo 1202418 2031635 := bstep (se 1 (by rfl) ⟨1523726, by rfl⟩ : syracuseStep 2031635 = 3047453) B3047453
theorem B1204243 : Blo 1202418 1204243 := bstep (se 1 (by rfl) ⟨903182, by rfl⟩ : syracuseStep 1204243 = 1806365) B1806365
theorem B1204259 : Blo 1202418 1204259 := bstep (se 1 (by rfl) ⟨903194, by rfl⟩ : syracuseStep 1204259 = 1806389) B1806389
theorem B1204275 : Blo 1202418 1204275 := bstep (se 1 (by rfl) ⟨903206, by rfl⟩ : syracuseStep 1204275 = 1806413) B1806413
theorem B1204291 : Blo 1202418 1204291 := bstep (se 1 (by rfl) ⟨903218, by rfl⟩ : syracuseStep 1204291 = 1806437) B1806437
theorem B6094925 : Blo 1202418 6094925 := bstep (se 3 (by rfl) ⟨1142798, by rfl⟩ : syracuseStep 6094925 = 2285597) B2285597
theorem B1204307 : Blo 1202418 1204307 := bstep (se 1 (by rfl) ⟨903230, by rfl⟩ : syracuseStep 1204307 = 1806461) B1806461
theorem B1204323 : Blo 1202418 1204323 := bstep (se 1 (by rfl) ⟨903242, by rfl⟩ : syracuseStep 1204323 = 1806485) B1806485
theorem B1204339 : Blo 1202418 1204339 := bstep (se 1 (by rfl) ⟨903254, by rfl⟩ : syracuseStep 1204339 = 1806509) B1806509
theorem B1204355 : Blo 1202418 1204355 := bstep (se 1 (by rfl) ⟨903266, by rfl⟩ : syracuseStep 1204355 = 1806533) B1806533
theorem B27779213 : Blo 1202418 27779213 := bstep (se 3 (by rfl) ⟨5208602, by rfl⟩ : syracuseStep 27779213 = 10417205) B10417205
theorem B2031763 : Blo 1202418 2031763 := bstep (se 1 (by rfl) ⟨1523822, by rfl⟩ : syracuseStep 2031763 = 3047645) B3047645
theorem B1204371 : Blo 1202418 1204371 := bstep (se 1 (by rfl) ⟨903278, by rfl⟩ : syracuseStep 1204371 = 1806557) B1806557
theorem B1204387 : Blo 1202418 1204387 := bstep (se 1 (by rfl) ⟨903290, by rfl⟩ : syracuseStep 1204387 = 1806581) B1806581
theorem B1204403 : Blo 1202418 1204403 := bstep (se 1 (by rfl) ⟨903302, by rfl⟩ : syracuseStep 1204403 = 1806605) B1806605
theorem B1712353 : Blo 1202418 1712353 := bstep (se 2 (by rfl) ⟨642132, by rfl⟩ : syracuseStep 1712353 = 1284265) B1284265
theorem B13000931 : Blo 1202418 13000931 := bstep (se 1 (by rfl) ⟨9750698, by rfl⟩ : syracuseStep 13000931 = 19501397) B19501397
theorem B2285795 : Blo 1202418 2285795 := bstep (se 1 (by rfl) ⟨1714346, by rfl⟩ : syracuseStep 2285795 = 3428693) B3428693
theorem B3047665 : Blo 1202418 3047665 := bstep (se 2 (by rfl) ⟨1142874, by rfl⟩ : syracuseStep 3047665 = 2285749) B2285749
theorem B1712387 : Blo 1202418 1712387 := bstep (se 1 (by rfl) ⟨1284290, by rfl⟩ : syracuseStep 1712387 = 2568581) B2568581
theorem B2031905 : Blo 1202418 2031905 := bstep (se 2 (by rfl) ⟨761964, by rfl⟩ : syracuseStep 2031905 = 1523929) B1523929
theorem B1524035 : Blo 1202418 1524035 := bstep (se 1 (by rfl) ⟨1143026, by rfl⟩ : syracuseStep 1524035 = 2286053) B2286053
theorem B3473741 : Blo 1202418 3473741 := bstep (se 3 (by rfl) ⟨651326, by rfl⟩ : syracuseStep 3473741 = 1302653) B1302653
theorem B10281329 : Blo 1202418 10281329 := bstep (se 2 (by rfl) ⟨3855498, by rfl⟩ : syracuseStep 10281329 = 7710997) B7710997
theorem B16695665 : Blo 1202418 16695665 := bstep (se 2 (by rfl) ⟨6260874, by rfl⟩ : syracuseStep 16695665 = 12521749) B12521749
theorem B2032033 : Blo 1202418 2032033 := bstep (se 2 (by rfl) ⟨762012, by rfl⟩ : syracuseStep 2032033 = 1524025) B1524025
theorem B4063661 : Blo 1202418 4063661 := bstep (se 3 (by rfl) ⟨761936, by rfl⟩ : syracuseStep 4063661 = 1523873) B1523873
theorem B2032067 : Blo 1202418 2032067 := bstep (se 1 (by rfl) ⟨1524050, by rfl⟩ : syracuseStep 2032067 = 3048101) B3048101
theorem B4063715 : Blo 1202418 4063715 := bstep (se 1 (by rfl) ⟨3047786, by rfl⟩ : syracuseStep 4063715 = 6095573) B6095573
theorem B3047939 : Blo 1202418 3047939 := bstep (se 1 (by rfl) ⟨2285954, by rfl⟩ : syracuseStep 3047939 = 4571909) B4571909
theorem B2286083 : Blo 1202418 2286083 := bstep (se 1 (by rfl) ⟨1714562, by rfl⟩ : syracuseStep 2286083 = 3429125) B3429125
theorem B2744867 : Blo 1202418 2744867 := bstep (se 1 (by rfl) ⟨2058650, by rfl⟩ : syracuseStep 2744867 = 4117301) B4117301
theorem B2032195 : Blo 1202418 2032195 := bstep (se 1 (by rfl) ⟨1524146, by rfl⟩ : syracuseStep 2032195 = 3048293) B3048293
theorem B6849137 : Blo 1202418 6849137 := bstep (se 2 (by rfl) ⟨2568426, by rfl⟩ : syracuseStep 6849137 = 5136853) B5136853
theorem B3048131 : Blo 1202418 3048131 := bstep (se 1 (by rfl) ⟨2286098, by rfl⟩ : syracuseStep 3048131 = 4572197) B4572197
theorem B7709381 : Blo 1202418 7709381 := bstep (se 4 (by rfl) ⟨722754, by rfl⟩ : syracuseStep 7709381 = 1445509) B1445509
theorem B2032337 : Blo 1202418 2032337 := bstep (se 2 (by rfl) ⟨762126, by rfl⟩ : syracuseStep 2032337 = 1524253) B1524253
theorem B4063985 : Blo 1202418 4063985 := bstep (se 2 (by rfl) ⟨1523994, by rfl⟩ : syracuseStep 4063985 = 3047989) B3047989
theorem B2892547 : Blo 1202418 2892547 := bstep (se 1 (by rfl) ⟨2169410, by rfl⟩ : syracuseStep 2892547 = 4338821) B4338821
theorem B8798989 : Blo 1202418 8798989 := bstep (se 3 (by rfl) ⟨1649810, by rfl⟩ : syracuseStep 8798989 = 3299621) B3299621
theorem B6087473 : Blo 1202418 6087473 := bstep (se 2 (by rfl) ⟨2282802, by rfl⟩ : syracuseStep 6087473 = 4565605) B4565605
theorem B1712945 : Blo 1202418 1712945 := bstep (se 2 (by rfl) ⟨642354, by rfl⟩ : syracuseStep 1712945 = 1284709) B1284709
theorem B3425105 : Blo 1202418 3425105 := bstep (se 2 (by rfl) ⟨1284414, by rfl⟩ : syracuseStep 3425105 = 2568829) B2568829
theorem B1713025 : Blo 1202418 1713025 := bstep (se 2 (by rfl) ⟨642384, by rfl⟩ : syracuseStep 1713025 = 1284769) B1284769
theorem B5784497 : Blo 1202418 5784497 := bstep (se 2 (by rfl) ⟨2169186, by rfl⟩ : syracuseStep 5784497 = 4338373) B4338373
theorem B1352803 : Blo 1202418 1352803 := bstep (se 1 (by rfl) ⟨1014602, by rfl⟩ : syracuseStep 1352803 = 2029205) B2029205
theorem B2893009 : Blo 1202418 2893009 := bstep (se 2 (by rfl) ⟨1084878, by rfl⟩ : syracuseStep 2893009 = 2169757) B2169757
theorem B1352947 : Blo 1202418 1352947 := bstep (se 1 (by rfl) ⟨1014710, by rfl⟩ : syracuseStep 1352947 = 2029421) B2029421
theorem B4064525 : Blo 1202418 4064525 := bstep (se 3 (by rfl) ⟨762098, by rfl⟩ : syracuseStep 4064525 = 1524197) B1524197
theorem B4064579 : Blo 1202418 4064579 := bstep (se 1 (by rfl) ⟨3048434, by rfl⟩ : syracuseStep 4064579 = 6096869) B6096869
theorem B1803635 : Blo 1202418 1803635 := bstep (se 1 (by rfl) ⟨1352726, by rfl⟩ : syracuseStep 1803635 = 2705453) B2705453
theorem B1353091 : Blo 1202418 1353091 := bstep (se 1 (by rfl) ⟨1014818, by rfl⟩ : syracuseStep 1353091 = 2029637) B2029637
theorem B1803665 : Blo 1202418 1803665 := bstep (se 2 (by rfl) ⟨676374, by rfl⟩ : syracuseStep 1803665 = 1352749) B1352749
theorem B1803683 : Blo 1202418 1803683 := bstep (se 1 (by rfl) ⟨1352762, by rfl⟩ : syracuseStep 1803683 = 2705525) B2705525
theorem B1803713 : Blo 1202418 1803713 := bstep (se 2 (by rfl) ⟨676392, by rfl⟩ : syracuseStep 1803713 = 1352785) B1352785
theorem B1803731 : Blo 1202418 1803731 := bstep (se 1 (by rfl) ⟨1352798, by rfl⟩ : syracuseStep 1803731 = 2705597) B2705597
theorem B1803761 : Blo 1202418 1803761 := bstep (se 2 (by rfl) ⟨676410, by rfl⟩ : syracuseStep 1803761 = 1352821) B1352821
theorem B1926641 : Blo 1202418 1926641 := bstep (se 2 (by rfl) ⟨722490, by rfl⟩ : syracuseStep 1926641 = 1444981) B1444981
theorem B3425777 : Blo 1202418 3425777 := bstep (se 2 (by rfl) ⟨1284666, by rfl⟩ : syracuseStep 3425777 = 2569333) B2569333
theorem B8349169 : Blo 1202418 8349169 := bstep (se 2 (by rfl) ⟨3130938, by rfl⟩ : syracuseStep 8349169 = 6261877) B6261877
theorem B1803779 : Blo 1202418 1803779 := bstep (se 1 (by rfl) ⟨1352834, by rfl⟩ : syracuseStep 1803779 = 2705669) B2705669
theorem B1353235 : Blo 1202418 1353235 := bstep (se 1 (by rfl) ⟨1014926, by rfl⟩ : syracuseStep 1353235 = 2029853) B2029853
theorem B1803809 : Blo 1202418 1803809 := bstep (se 2 (by rfl) ⟨676428, by rfl⟩ : syracuseStep 1803809 = 1352857) B1352857
theorem B1803827 : Blo 1202418 1803827 := bstep (se 1 (by rfl) ⟨1352870, by rfl⟩ : syracuseStep 1803827 = 2705741) B2705741
theorem B1803857 : Blo 1202418 1803857 := bstep (se 2 (by rfl) ⟨676446, by rfl⟩ : syracuseStep 1803857 = 1352893) B1352893
theorem B4064849 : Blo 1202418 4064849 := bstep (se 2 (by rfl) ⟨1524318, by rfl⟩ : syracuseStep 4064849 = 3048637) B3048637
theorem B1803875 : Blo 1202418 1803875 := bstep (se 1 (by rfl) ⟨1352906, by rfl⟩ : syracuseStep 1803875 = 2705813) B2705813
theorem B1803905 : Blo 1202418 1803905 := bstep (se 2 (by rfl) ⟨676464, by rfl⟩ : syracuseStep 1803905 = 1352929) B1352929
theorem B1803923 : Blo 1202418 1803923 := bstep (se 1 (by rfl) ⟨1352942, by rfl⟩ : syracuseStep 1803923 = 2705885) B2705885
theorem B1713811 : Blo 1202418 1713811 := bstep (se 1 (by rfl) ⟨1285358, by rfl⟩ : syracuseStep 1713811 = 2570717) B2570717
theorem B5138083 : Blo 1202418 5138083 := bstep (se 1 (by rfl) ⟨3853562, by rfl⟩ : syracuseStep 5138083 = 7707125) B7707125
theorem B1353379 : Blo 1202418 1353379 := bstep (se 1 (by rfl) ⟨1015034, by rfl⟩ : syracuseStep 1353379 = 2030069) B2030069
theorem B1803953 : Blo 1202418 1803953 := bstep (se 2 (by rfl) ⟨676482, by rfl⟩ : syracuseStep 1803953 = 1352965) B1352965
theorem B5785265 : Blo 1202418 5785265 := bstep (se 2 (by rfl) ⟨2169474, by rfl⟩ : syracuseStep 5785265 = 4338949) B4338949
theorem B1803971 : Blo 1202418 1803971 := bstep (se 1 (by rfl) ⟨1352978, by rfl⟩ : syracuseStep 1803971 = 2705957) B2705957
theorem B1804001 : Blo 1202418 1804001 := bstep (se 2 (by rfl) ⟨676500, by rfl⟩ : syracuseStep 1804001 = 1353001) B1353001
theorem B1804019 : Blo 1202418 1804019 := bstep (se 1 (by rfl) ⟨1353014, by rfl⟩ : syracuseStep 1804019 = 2706029) B2706029
theorem B1804049 : Blo 1202418 1804049 := bstep (se 2 (by rfl) ⟨676518, by rfl⟩ : syracuseStep 1804049 = 1353037) B1353037
theorem B1804067 : Blo 1202418 1804067 := bstep (se 1 (by rfl) ⟨1353050, by rfl⟩ : syracuseStep 1804067 = 2706101) B2706101
theorem B1353523 : Blo 1202418 1353523 := bstep (se 1 (by rfl) ⟨1015142, by rfl⟩ : syracuseStep 1353523 = 2030285) B2030285
theorem B1804097 : Blo 1202418 1804097 := bstep (se 2 (by rfl) ⟨676536, by rfl⟩ : syracuseStep 1804097 = 1353073) B1353073
theorem B1804115 : Blo 1202418 1804115 := bstep (se 1 (by rfl) ⟨1353086, by rfl⟩ : syracuseStep 1804115 = 2706173) B2706173
theorem B1804145 : Blo 1202418 1804145 := bstep (se 2 (by rfl) ⟨676554, by rfl⟩ : syracuseStep 1804145 = 1353109) B1353109
theorem B1804163 : Blo 1202418 1804163 := bstep (se 1 (by rfl) ⟨1353122, by rfl⟩ : syracuseStep 1804163 = 2706245) B2706245
theorem B1804193 : Blo 1202418 1804193 := bstep (se 2 (by rfl) ⟨676572, by rfl⟩ : syracuseStep 1804193 = 1353145) B1353145
theorem B1804211 : Blo 1202418 1804211 := bstep (se 1 (by rfl) ⟨1353158, by rfl⟩ : syracuseStep 1804211 = 2706317) B2706317
theorem B1353667 : Blo 1202418 1353667 := bstep (se 1 (by rfl) ⟨1015250, by rfl⟩ : syracuseStep 1353667 = 2030501) B2030501
theorem B1804241 : Blo 1202418 1804241 := bstep (se 2 (by rfl) ⟨676590, by rfl⟩ : syracuseStep 1804241 = 1353181) B1353181
theorem B1804259 : Blo 1202418 1804259 := bstep (se 1 (by rfl) ⟨1353194, by rfl⟩ : syracuseStep 1804259 = 2706389) B2706389
theorem B1804289 : Blo 1202418 1804289 := bstep (se 2 (by rfl) ⟨676608, by rfl⟩ : syracuseStep 1804289 = 1353217) B1353217
theorem B1804307 : Blo 1202418 1804307 := bstep (se 1 (by rfl) ⟨1353230, by rfl⟩ : syracuseStep 1804307 = 2706461) B2706461
theorem B6850595 : Blo 1202418 6850595 := bstep (se 1 (by rfl) ⟨5137946, by rfl⟩ : syracuseStep 6850595 = 10275893) B10275893
theorem B1804337 : Blo 1202418 1804337 := bstep (se 2 (by rfl) ⟨676626, by rfl⟩ : syracuseStep 1804337 = 1353253) B1353253
theorem B1804355 : Blo 1202418 1804355 := bstep (se 1 (by rfl) ⟨1353266, by rfl⟩ : syracuseStep 1804355 = 2706533) B2706533
theorem B2705489 : Blo 1202418 2705489 := bstep (se 2 (by rfl) ⟨1014558, by rfl⟩ : syracuseStep 2705489 = 2029117) B2029117
theorem B1353811 : Blo 1202418 1353811 := bstep (se 1 (by rfl) ⟨1015358, by rfl⟩ : syracuseStep 1353811 = 2030717) B2030717
theorem B1804385 : Blo 1202418 1804385 := bstep (se 2 (by rfl) ⟨676644, by rfl⟩ : syracuseStep 1804385 = 1353289) B1353289
theorem B2705507 : Blo 1202418 2705507 := bstep (se 1 (by rfl) ⟨2029130, by rfl⟩ : syracuseStep 2705507 = 4058261) B4058261
theorem B2607203 : Blo 1202418 2607203 := bstep (se 1 (by rfl) ⟨1955402, by rfl⟩ : syracuseStep 2607203 = 3910805) B3910805
theorem B6170737 : Blo 1202418 6170737 := bstep (se 2 (by rfl) ⟨2314026, by rfl⟩ : syracuseStep 6170737 = 4628053) B4628053
theorem B1714289 : Blo 1202418 1714289 := bstep (se 2 (by rfl) ⟨642858, by rfl⟩ : syracuseStep 1714289 = 1285717) B1285717
theorem B1804403 : Blo 1202418 1804403 := bstep (se 1 (by rfl) ⟨1353302, by rfl⟩ : syracuseStep 1804403 = 2706605) B2706605
theorem B1804433 : Blo 1202418 1804433 := bstep (se 2 (by rfl) ⟨676662, by rfl⟩ : syracuseStep 1804433 = 1353325) B1353325
theorem B1804451 : Blo 1202418 1804451 := bstep (se 1 (by rfl) ⟨1353338, by rfl⟩ : syracuseStep 1804451 = 2706677) B2706677
theorem B3852461 : Blo 1202418 3852461 := bstep (se 3 (by rfl) ⟨722336, by rfl⟩ : syracuseStep 3852461 = 1444673) B1444673
theorem B1804481 : Blo 1202418 1804481 := bstep (se 2 (by rfl) ⟨676680, by rfl⟩ : syracuseStep 1804481 = 1353361) B1353361
theorem B1804499 : Blo 1202418 1804499 := bstep (se 1 (by rfl) ⟨1353374, by rfl⟩ : syracuseStep 1804499 = 2706749) B2706749
theorem B6088931 : Blo 1202418 6088931 := bstep (se 1 (by rfl) ⟨4566698, by rfl⟩ : syracuseStep 6088931 = 9133397) B9133397
theorem B1353955 : Blo 1202418 1353955 := bstep (se 1 (by rfl) ⟨1015466, by rfl⟩ : syracuseStep 1353955 = 2030933) B2030933
theorem B1714403 : Blo 1202418 1714403 := bstep (se 1 (by rfl) ⟨1285802, by rfl⟩ : syracuseStep 1714403 = 2571605) B2571605
theorem B1804529 : Blo 1202418 1804529 := bstep (se 2 (by rfl) ⟨676698, by rfl⟩ : syracuseStep 1804529 = 1353397) B1353397
theorem B1804547 : Blo 1202418 1804547 := bstep (se 1 (by rfl) ⟨1353410, by rfl⟩ : syracuseStep 1804547 = 2706821) B2706821
theorem B3426563 : Blo 1202418 3426563 := bstep (se 1 (by rfl) ⟨2569922, by rfl⟩ : syracuseStep 3426563 = 5139845) B5139845
theorem B7817477 : Blo 1202418 7817477 := bstep (se 4 (by rfl) ⟨732888, by rfl⟩ : syracuseStep 7817477 = 1465777) B1465777
theorem B1804577 : Blo 1202418 1804577 := bstep (se 2 (by rfl) ⟨676716, by rfl⟩ : syracuseStep 1804577 = 1353433) B1353433
theorem B1804595 : Blo 1202418 1804595 := bstep (se 1 (by rfl) ⟨1353446, by rfl⟩ : syracuseStep 1804595 = 2706893) B2706893
theorem B1714483 : Blo 1202418 1714483 := bstep (se 1 (by rfl) ⟨1285862, by rfl⟩ : syracuseStep 1714483 = 2571725) B2571725
theorem B1804625 : Blo 1202418 1804625 := bstep (se 2 (by rfl) ⟨676734, by rfl⟩ : syracuseStep 1804625 = 1353469) B1353469
theorem B1804643 : Blo 1202418 1804643 := bstep (se 1 (by rfl) ⟨1353482, by rfl⟩ : syracuseStep 1804643 = 2706965) B2706965
theorem B2705777 : Blo 1202418 2705777 := bstep (se 2 (by rfl) ⟨1014666, by rfl⟩ : syracuseStep 2705777 = 2029333) B2029333
theorem B1354099 : Blo 1202418 1354099 := bstep (se 1 (by rfl) ⟨1015574, by rfl⟩ : syracuseStep 1354099 = 2031149) B2031149
theorem B1804673 : Blo 1202418 1804673 := bstep (se 2 (by rfl) ⟨676752, by rfl⟩ : syracuseStep 1804673 = 1353505) B1353505
theorem B2705795 : Blo 1202418 2705795 := bstep (se 1 (by rfl) ⟨2029346, by rfl⟩ : syracuseStep 2705795 = 4058693) B4058693
theorem B1804691 : Blo 1202418 1804691 := bstep (se 1 (by rfl) ⟨1353518, by rfl⟩ : syracuseStep 1804691 = 2707037) B2707037
theorem B1804721 : Blo 1202418 1804721 := bstep (se 2 (by rfl) ⟨676770, by rfl⟩ : syracuseStep 1804721 = 1353541) B1353541
theorem B1804739 : Blo 1202418 1804739 := bstep (se 1 (by rfl) ⟨1353554, by rfl⟩ : syracuseStep 1804739 = 2707109) B2707109
theorem B1804769 : Blo 1202418 1804769 := bstep (se 2 (by rfl) ⟨676788, by rfl⟩ : syracuseStep 1804769 = 1353577) B1353577
theorem B1804787 : Blo 1202418 1804787 := bstep (se 1 (by rfl) ⟨1353590, by rfl⟩ : syracuseStep 1804787 = 2707181) B2707181
theorem B1354243 : Blo 1202418 1354243 := bstep (se 1 (by rfl) ⟨1015682, by rfl⟩ : syracuseStep 1354243 = 2031365) B2031365
theorem B1804817 : Blo 1202418 1804817 := bstep (se 2 (by rfl) ⟨676806, by rfl⟩ : syracuseStep 1804817 = 1353613) B1353613
theorem B1804835 : Blo 1202418 1804835 := bstep (se 1 (by rfl) ⟨1353626, by rfl⟩ : syracuseStep 1804835 = 2707253) B2707253
theorem B1804865 : Blo 1202418 1804865 := bstep (se 2 (by rfl) ⟨676824, by rfl⟩ : syracuseStep 1804865 = 1353649) B1353649
theorem B3426893 : Blo 1202418 3426893 := bstep (se 3 (by rfl) ⟨642542, by rfl⟩ : syracuseStep 3426893 = 1285085) B1285085
theorem B1804883 : Blo 1202418 1804883 := bstep (se 1 (by rfl) ⟨1353662, by rfl⟩ : syracuseStep 1804883 = 2707325) B2707325
theorem B1804913 : Blo 1202418 1804913 := bstep (se 2 (by rfl) ⟨676842, by rfl⟩ : syracuseStep 1804913 = 1353685) B1353685
theorem B1804931 : Blo 1202418 1804931 := bstep (se 1 (by rfl) ⟨1353698, by rfl⟩ : syracuseStep 1804931 = 2707397) B2707397
theorem B2706065 : Blo 1202418 2706065 := bstep (se 2 (by rfl) ⟨1014774, by rfl⟩ : syracuseStep 2706065 = 2029549) B2029549
theorem B3426961 : Blo 1202418 3426961 := bstep (se 2 (by rfl) ⟨1285110, by rfl⟩ : syracuseStep 3426961 = 2570221) B2570221
theorem B1354387 : Blo 1202418 1354387 := bstep (se 1 (by rfl) ⟨1015790, by rfl⟩ : syracuseStep 1354387 = 2031581) B2031581
theorem B1804961 : Blo 1202418 1804961 := bstep (se 2 (by rfl) ⟨676860, by rfl⟩ : syracuseStep 1804961 = 1353721) B1353721
theorem B2706083 : Blo 1202418 2706083 := bstep (se 1 (by rfl) ⟨2029562, by rfl⟩ : syracuseStep 2706083 = 4059125) B4059125
theorem B1804979 : Blo 1202418 1804979 := bstep (se 1 (by rfl) ⟨1353734, by rfl⟩ : syracuseStep 1804979 = 2707469) B2707469
theorem B1805009 : Blo 1202418 1805009 := bstep (se 2 (by rfl) ⟨676878, by rfl⟩ : syracuseStep 1805009 = 1353757) B1353757
theorem B4336355 : Blo 1202418 4336355 := bstep (se 1 (by rfl) ⟨3252266, by rfl⟩ : syracuseStep 4336355 = 6504533) B6504533
theorem B1805027 : Blo 1202418 1805027 := bstep (se 1 (by rfl) ⟨1353770, by rfl⟩ : syracuseStep 1805027 = 2707541) B2707541
theorem B7834339 : Blo 1202418 7834339 := bstep (se 1 (by rfl) ⟨5875754, by rfl⟩ : syracuseStep 7834339 = 11751509) B11751509
theorem B1805057 : Blo 1202418 1805057 := bstep (se 2 (by rfl) ⟨676896, by rfl⟩ : syracuseStep 1805057 = 1353793) B1353793
theorem B6859525 : Blo 1202418 6859525 := bstep (se 4 (by rfl) ⟨643080, by rfl⟩ : syracuseStep 6859525 = 1286161) B1286161
theorem B1805075 : Blo 1202418 1805075 := bstep (se 1 (by rfl) ⟨1353806, by rfl⟩ : syracuseStep 1805075 = 2707613) B2707613
theorem B1927955 : Blo 1202418 1927955 := bstep (se 1 (by rfl) ⟨1445966, by rfl⟩ : syracuseStep 1927955 = 2891933) B2891933
theorem B1354531 : Blo 1202418 1354531 := bstep (se 1 (by rfl) ⟨1015898, by rfl⟩ : syracuseStep 1354531 = 2031797) B2031797
theorem B1805105 : Blo 1202418 1805105 := bstep (se 2 (by rfl) ⟨676914, by rfl⟩ : syracuseStep 1805105 = 1353829) B1353829
theorem B1805123 : Blo 1202418 1805123 := bstep (se 1 (by rfl) ⟨1353842, by rfl⟩ : syracuseStep 1805123 = 2707685) B2707685
theorem B1805153 : Blo 1202418 1805153 := bstep (se 2 (by rfl) ⟨676932, by rfl⟩ : syracuseStep 1805153 = 1353865) B1353865
theorem B1805171 : Blo 1202418 1805171 := bstep (se 1 (by rfl) ⟨1353878, by rfl⟩ : syracuseStep 1805171 = 2707757) B2707757
theorem B1805201 : Blo 1202418 1805201 := bstep (se 2 (by rfl) ⟨676950, by rfl⟩ : syracuseStep 1805201 = 1353901) B1353901
theorem B1805219 : Blo 1202418 1805219 := bstep (se 1 (by rfl) ⟨1353914, by rfl⟩ : syracuseStep 1805219 = 2707829) B2707829
theorem B3427235 : Blo 1202418 3427235 := bstep (se 1 (by rfl) ⟨2570426, by rfl⟩ : syracuseStep 3427235 = 5140853) B5140853
theorem B2706353 : Blo 1202418 2706353 := bstep (se 2 (by rfl) ⟨1014882, by rfl⟩ : syracuseStep 2706353 = 2029765) B2029765
theorem B1354675 : Blo 1202418 1354675 := bstep (se 1 (by rfl) ⟨1016006, by rfl⟩ : syracuseStep 1354675 = 2032013) B2032013
theorem B1805249 : Blo 1202418 1805249 := bstep (se 2 (by rfl) ⟨676968, by rfl⟩ : syracuseStep 1805249 = 1353937) B1353937
theorem B2706371 : Blo 1202418 2706371 := bstep (se 1 (by rfl) ⟨2029778, by rfl⟩ : syracuseStep 2706371 = 4059557) B4059557
theorem B1805267 : Blo 1202418 1805267 := bstep (se 1 (by rfl) ⟨1353950, by rfl⟩ : syracuseStep 1805267 = 2707901) B2707901
theorem B15420401 : Blo 1202418 15420401 := bstep (se 2 (by rfl) ⟨5782650, by rfl⟩ : syracuseStep 15420401 = 11565301) B11565301
theorem B1805297 : Blo 1202418 1805297 := bstep (se 2 (by rfl) ⟨676986, by rfl⟩ : syracuseStep 1805297 = 1353973) B1353973
theorem B1805315 : Blo 1202418 1805315 := bstep (se 1 (by rfl) ⟨1353986, by rfl⟩ : syracuseStep 1805315 = 2707973) B2707973
theorem B6089741 : Blo 1202418 6089741 := bstep (se 3 (by rfl) ⟨1141826, by rfl⟩ : syracuseStep 6089741 = 2283653) B2283653
theorem B1805345 : Blo 1202418 1805345 := bstep (se 2 (by rfl) ⟨677004, by rfl⟩ : syracuseStep 1805345 = 1354009) B1354009
theorem B1805363 : Blo 1202418 1805363 := bstep (se 1 (by rfl) ⟨1354022, by rfl⟩ : syracuseStep 1805363 = 2708045) B2708045
theorem B1354819 : Blo 1202418 1354819 := bstep (se 1 (by rfl) ⟨1016114, by rfl⟩ : syracuseStep 1354819 = 2032229) B2032229
theorem B3296333 : Blo 1202418 3296333 := bstep (se 3 (by rfl) ⟨618062, by rfl⟩ : syracuseStep 3296333 = 1236125) B1236125
theorem B1805393 : Blo 1202418 1805393 := bstep (se 2 (by rfl) ⟨677022, by rfl⟩ : syracuseStep 1805393 = 1354045) B1354045
theorem B1805411 : Blo 1202418 1805411 := bstep (se 1 (by rfl) ⟨1354058, by rfl⟩ : syracuseStep 1805411 = 2708117) B2708117
theorem B4877425 : Blo 1202418 4877425 := bstep (se 2 (by rfl) ⟨1829034, by rfl⟩ : syracuseStep 4877425 = 3658069) B3658069
theorem B1625203 : Blo 1202418 1625203 := bstep (se 1 (by rfl) ⟨1218902, by rfl⟩ : syracuseStep 1625203 = 2437805) B2437805
theorem B1805441 : Blo 1202418 1805441 := bstep (se 2 (by rfl) ⟨677040, by rfl⟩ : syracuseStep 1805441 = 1354081) B1354081
theorem B1805459 : Blo 1202418 1805459 := bstep (se 1 (by rfl) ⟨1354094, by rfl⟩ : syracuseStep 1805459 = 2708189) B2708189
theorem B1805489 : Blo 1202418 1805489 := bstep (se 2 (by rfl) ⟨677058, by rfl⟩ : syracuseStep 1805489 = 1354117) B1354117
theorem B1805507 : Blo 1202418 1805507 := bstep (se 1 (by rfl) ⟨1354130, by rfl⟩ : syracuseStep 1805507 = 2708261) B2708261
theorem B2706641 : Blo 1202418 2706641 := bstep (se 2 (by rfl) ⟨1014990, by rfl⟩ : syracuseStep 2706641 = 2029981) B2029981
theorem B1354963 : Blo 1202418 1354963 := bstep (se 1 (by rfl) ⟨1016222, by rfl⟩ : syracuseStep 1354963 = 2032445) B2032445
theorem B1805537 : Blo 1202418 1805537 := bstep (se 2 (by rfl) ⟨677076, by rfl⟩ : syracuseStep 1805537 = 1354153) B1354153
theorem B2706659 : Blo 1202418 2706659 := bstep (se 1 (by rfl) ⟨2029994, by rfl⟩ : syracuseStep 2706659 = 4059989) B4059989
theorem B1805555 : Blo 1202418 1805555 := bstep (se 1 (by rfl) ⟨1354166, by rfl⟩ : syracuseStep 1805555 = 2708333) B2708333
theorem B1805585 : Blo 1202418 1805585 := bstep (se 2 (by rfl) ⟨677094, by rfl⟩ : syracuseStep 1805585 = 1354189) B1354189
theorem B1805603 : Blo 1202418 1805603 := bstep (se 1 (by rfl) ⟨1354202, by rfl⟩ : syracuseStep 1805603 = 2708405) B2708405
theorem B1805633 : Blo 1202418 1805633 := bstep (se 2 (by rfl) ⟨677112, by rfl⟩ : syracuseStep 1805633 = 1354225) B1354225
theorem B5786957 : Blo 1202418 5786957 := bstep (se 3 (by rfl) ⟨1085054, by rfl⟩ : syracuseStep 5786957 = 2170109) B2170109
theorem B1805651 : Blo 1202418 1805651 := bstep (se 1 (by rfl) ⟨1354238, by rfl⟩ : syracuseStep 1805651 = 2708477) B2708477
theorem B1625441 : Blo 1202418 1625441 := bstep (se 2 (by rfl) ⟨609540, by rfl⟩ : syracuseStep 1625441 = 1219081) B1219081
theorem B4058477 : Blo 1202418 4058477 := bstep (se 3 (by rfl) ⟨760964, by rfl⟩ : syracuseStep 4058477 = 1521929) B1521929
theorem B1805681 : Blo 1202418 1805681 := bstep (se 2 (by rfl) ⟨677130, by rfl⟩ : syracuseStep 1805681 = 1354261) B1354261
theorem B1805699 : Blo 1202418 1805699 := bstep (se 1 (by rfl) ⟨1354274, by rfl⟩ : syracuseStep 1805699 = 2708549) B2708549
theorem B1805729 : Blo 1202418 1805729 := bstep (se 2 (by rfl) ⟨677148, by rfl⟩ : syracuseStep 1805729 = 1354297) B1354297
theorem B4058531 : Blo 1202418 4058531 := bstep (se 1 (by rfl) ⟨3043898, by rfl⟩ : syracuseStep 4058531 = 6087797) B6087797
theorem B1805747 : Blo 1202418 1805747 := bstep (se 1 (by rfl) ⟨1354310, by rfl⟩ : syracuseStep 1805747 = 2708621) B2708621
theorem B1928627 : Blo 1202418 1928627 := bstep (se 1 (by rfl) ⟨1446470, by rfl⟩ : syracuseStep 1928627 = 2892941) B2892941
theorem B1805777 : Blo 1202418 1805777 := bstep (se 2 (by rfl) ⟨677166, by rfl⟩ : syracuseStep 1805777 = 1354333) B1354333
theorem B1805795 : Blo 1202418 1805795 := bstep (se 1 (by rfl) ⟨1354346, by rfl⟩ : syracuseStep 1805795 = 2708693) B2708693
theorem B2706929 : Blo 1202418 2706929 := bstep (se 2 (by rfl) ⟨1015098, by rfl⟩ : syracuseStep 2706929 = 2030197) B2030197
theorem B1805825 : Blo 1202418 1805825 := bstep (se 2 (by rfl) ⟨677184, by rfl⟩ : syracuseStep 1805825 = 1354369) B1354369
theorem B2706947 : Blo 1202418 2706947 := bstep (se 1 (by rfl) ⟨2030210, by rfl⟩ : syracuseStep 2706947 = 4060421) B4060421
theorem B1805843 : Blo 1202418 1805843 := bstep (se 1 (by rfl) ⟨1354382, by rfl⟩ : syracuseStep 1805843 = 2708765) B2708765
theorem B4566563 : Blo 1202418 4566563 := bstep (se 1 (by rfl) ⟨3424922, by rfl⟩ : syracuseStep 4566563 = 6849845) B6849845
theorem B4566577 : Blo 1202418 4566577 := bstep (se 2 (by rfl) ⟨1712466, by rfl⟩ : syracuseStep 4566577 = 3424933) B3424933
theorem B1805873 : Blo 1202418 1805873 := bstep (se 2 (by rfl) ⟨677202, by rfl⟩ : syracuseStep 1805873 = 1354405) B1354405
theorem B1805891 : Blo 1202418 1805891 := bstep (se 1 (by rfl) ⟨1354418, by rfl⟩ : syracuseStep 1805891 = 2708837) B2708837
theorem B1805921 : Blo 1202418 1805921 := bstep (se 2 (by rfl) ⟨677220, by rfl⟩ : syracuseStep 1805921 = 1354441) B1354441
theorem B1805939 : Blo 1202418 1805939 := bstep (se 1 (by rfl) ⟨1354454, by rfl⟩ : syracuseStep 1805939 = 2708909) B2708909
theorem B1805969 : Blo 1202418 1805969 := bstep (se 2 (by rfl) ⟨677238, by rfl⟩ : syracuseStep 1805969 = 1354477) B1354477
theorem B1805987 : Blo 1202418 1805987 := bstep (se 1 (by rfl) ⟨1354490, by rfl⟩ : syracuseStep 1805987 = 2708981) B2708981
theorem B4058801 : Blo 1202418 4058801 := bstep (se 2 (by rfl) ⟨1522050, by rfl⟩ : syracuseStep 4058801 = 3044101) B3044101
theorem B1806017 : Blo 1202418 1806017 := bstep (se 2 (by rfl) ⟨677256, by rfl⟩ : syracuseStep 1806017 = 1354513) B1354513
theorem B1806035 : Blo 1202418 1806035 := bstep (se 1 (by rfl) ⟨1354526, by rfl⟩ : syracuseStep 1806035 = 2709053) B2709053
theorem B1928929 : Blo 1202418 1928929 := bstep (se 2 (by rfl) ⟨723348, by rfl⟩ : syracuseStep 1928929 = 1446697) B1446697
theorem B3428077 : Blo 1202418 3428077 := bstep (se 3 (by rfl) ⟨642764, by rfl⟩ : syracuseStep 3428077 = 1285529) B1285529
theorem B1855217 : Blo 1202418 1855217 := bstep (se 2 (by rfl) ⟨695706, by rfl⟩ : syracuseStep 1855217 = 1391413) B1391413
theorem B1806065 : Blo 1202418 1806065 := bstep (se 2 (by rfl) ⟨677274, by rfl⟩ : syracuseStep 1806065 = 1354549) B1354549
theorem B1806083 : Blo 1202418 1806083 := bstep (se 1 (by rfl) ⟨1354562, by rfl⟩ : syracuseStep 1806083 = 2709125) B2709125
theorem B6262541 : Blo 1202418 6262541 := bstep (se 3 (by rfl) ⟨1174226, by rfl⟩ : syracuseStep 6262541 = 2348453) B2348453
theorem B2707217 : Blo 1202418 2707217 := bstep (se 2 (by rfl) ⟨1015206, by rfl⟩ : syracuseStep 2707217 = 2030413) B2030413
theorem B1806113 : Blo 1202418 1806113 := bstep (se 2 (by rfl) ⟨677292, by rfl⟩ : syracuseStep 1806113 = 1354585) B1354585
theorem B2707235 : Blo 1202418 2707235 := bstep (se 1 (by rfl) ⟨2030426, by rfl⟩ : syracuseStep 2707235 = 4060853) B4060853
theorem B1806131 : Blo 1202418 1806131 := bstep (se 1 (by rfl) ⟨1354598, by rfl⟩ : syracuseStep 1806131 = 2709197) B2709197
theorem B1806161 : Blo 1202418 1806161 := bstep (se 2 (by rfl) ⟨677310, by rfl⟩ : syracuseStep 1806161 = 1354621) B1354621
theorem B1806179 : Blo 1202418 1806179 := bstep (se 1 (by rfl) ⟨1354634, by rfl⟩ : syracuseStep 1806179 = 2709269) B2709269
theorem B1806209 : Blo 1202418 1806209 := bstep (se 2 (by rfl) ⟨677328, by rfl⟩ : syracuseStep 1806209 = 1354657) B1354657
theorem B3428237 : Blo 1202418 3428237 := bstep (se 3 (by rfl) ⟨642794, by rfl⟩ : syracuseStep 3428237 = 1285589) B1285589
theorem B1806227 : Blo 1202418 1806227 := bstep (se 1 (by rfl) ⟨1354670, by rfl⟩ : syracuseStep 1806227 = 2709341) B2709341
theorem B1806257 : Blo 1202418 1806257 := bstep (se 2 (by rfl) ⟨677346, by rfl⟩ : syracuseStep 1806257 = 1354693) B1354693
theorem B1929139 : Blo 1202418 1929139 := bstep (se 1 (by rfl) ⟨1446854, by rfl⟩ : syracuseStep 1929139 = 2893709) B2893709
theorem B1806275 : Blo 1202418 1806275 := bstep (se 1 (by rfl) ⟨1354706, by rfl⟩ : syracuseStep 1806275 = 2709413) B2709413
theorem B1806305 : Blo 1202418 1806305 := bstep (se 2 (by rfl) ⟨677364, by rfl⟩ : syracuseStep 1806305 = 1354729) B1354729
theorem B1929185 : Blo 1202418 1929185 := bstep (se 2 (by rfl) ⟨723444, by rfl⟩ : syracuseStep 1929185 = 1446889) B1446889
theorem B1806323 : Blo 1202418 1806323 := bstep (se 1 (by rfl) ⟨1354742, by rfl⟩ : syracuseStep 1806323 = 2709485) B2709485
theorem B1806353 : Blo 1202418 1806353 := bstep (se 2 (by rfl) ⟨677382, by rfl⟩ : syracuseStep 1806353 = 1354765) B1354765
theorem B1806371 : Blo 1202418 1806371 := bstep (se 1 (by rfl) ⟨1354778, by rfl⟩ : syracuseStep 1806371 = 2709557) B2709557
theorem B2707505 : Blo 1202418 2707505 := bstep (se 2 (by rfl) ⟨1015314, by rfl⟩ : syracuseStep 2707505 = 2030629) B2030629
theorem B5140529 : Blo 1202418 5140529 := bstep (se 2 (by rfl) ⟨1927698, by rfl⟩ : syracuseStep 5140529 = 3855397) B3855397
theorem B1806401 : Blo 1202418 1806401 := bstep (se 2 (by rfl) ⟨677400, by rfl⟩ : syracuseStep 1806401 = 1354801) B1354801
theorem B2707523 : Blo 1202418 2707523 := bstep (se 1 (by rfl) ⟨2030642, by rfl⟩ : syracuseStep 2707523 = 4061285) B4061285
theorem B3428419 : Blo 1202418 3428419 := bstep (se 1 (by rfl) ⟨2571314, by rfl⟩ : syracuseStep 3428419 = 5142629) B5142629
theorem B1626193 : Blo 1202418 1626193 := bstep (se 2 (by rfl) ⟨609822, by rfl⟩ : syracuseStep 1626193 = 1219645) B1219645
theorem B1806419 : Blo 1202418 1806419 := bstep (se 1 (by rfl) ⟨1354814, by rfl⟩ : syracuseStep 1806419 = 2709629) B2709629
theorem B1806449 : Blo 1202418 1806449 := bstep (se 2 (by rfl) ⟨677418, by rfl⟩ : syracuseStep 1806449 = 1354837) B1354837
theorem B1806467 : Blo 1202418 1806467 := bstep (se 1 (by rfl) ⟨1354850, by rfl⟩ : syracuseStep 1806467 = 2709701) B2709701
theorem B1806497 : Blo 1202418 1806497 := bstep (se 2 (by rfl) ⟨677436, by rfl⟩ : syracuseStep 1806497 = 1354873) B1354873
theorem B1806515 : Blo 1202418 1806515 := bstep (se 1 (by rfl) ⟨1354886, by rfl⟩ : syracuseStep 1806515 = 2709773) B2709773
theorem B15413429 : Blo 1202418 15413429 := bstep (se 5 (by rfl) ⟨722504, by rfl⟩ : syracuseStep 15413429 = 1445009) B1445009
theorem B9752773 : Blo 1202418 9752773 := bstep (se 4 (by rfl) ⟨914322, by rfl⟩ : syracuseStep 9752773 = 1828645) B1828645
theorem B4059341 : Blo 1202418 4059341 := bstep (se 3 (by rfl) ⟨761126, by rfl⟩ : syracuseStep 4059341 = 1522253) B1522253
theorem B5492941 : Blo 1202418 5492941 := bstep (se 3 (by rfl) ⟨1029926, by rfl⟩ : syracuseStep 5492941 = 2059853) B2059853
theorem B1806545 : Blo 1202418 1806545 := bstep (se 2 (by rfl) ⟨677454, by rfl⟩ : syracuseStep 1806545 = 1354909) B1354909
theorem B2568419 : Blo 1202418 2568419 := bstep (se 1 (by rfl) ⟨1926314, by rfl⟩ : syracuseStep 2568419 = 3852629) B3852629
theorem B1806563 : Blo 1202418 1806563 := bstep (se 1 (by rfl) ⟨1354922, by rfl⟩ : syracuseStep 1806563 = 2709845) B2709845
theorem B1806593 : Blo 1202418 1806593 := bstep (se 2 (by rfl) ⟨677472, by rfl⟩ : syracuseStep 1806593 = 1354945) B1354945
theorem B4059395 : Blo 1202418 4059395 := bstep (se 1 (by rfl) ⟨3044546, by rfl⟩ : syracuseStep 4059395 = 6089093) B6089093
theorem B3657997 : Blo 1202418 3657997 := bstep (se 3 (by rfl) ⟨685874, by rfl⟩ : syracuseStep 3657997 = 1371749) B1371749
theorem B10285325 : Blo 1202418 10285325 := bstep (se 3 (by rfl) ⟨1928498, by rfl⟩ : syracuseStep 10285325 = 3856997) B3856997
theorem B1806611 : Blo 1202418 1806611 := bstep (se 1 (by rfl) ⟨1354958, by rfl⟩ : syracuseStep 1806611 = 2709917) B2709917
theorem B1446211 : Blo 1202418 1446211 := bstep (se 1 (by rfl) ⟨1084658, by rfl⟩ : syracuseStep 1446211 = 2169317) B2169317
theorem B3658061 : Blo 1202418 3658061 := bstep (se 3 (by rfl) ⟨685886, by rfl⟩ : syracuseStep 3658061 = 1371773) B1371773
theorem B2707793 : Blo 1202418 2707793 := bstep (se 2 (by rfl) ⟨1015422, by rfl⟩ : syracuseStep 2707793 = 2030845) B2030845
theorem B1651043 : Blo 1202418 1651043 := bstep (se 1 (by rfl) ⟨1238282, by rfl⟩ : syracuseStep 1651043 = 2476565) B2476565
theorem B2707811 : Blo 1202418 2707811 := bstep (se 1 (by rfl) ⟨2030858, by rfl⟩ : syracuseStep 2707811 = 4061717) B4061717
theorem B4059665 : Blo 1202418 4059665 := bstep (se 2 (by rfl) ⟨1522374, by rfl⟩ : syracuseStep 4059665 = 3044749) B3044749
theorem B3043889 : Blo 1202418 3043889 := bstep (se 2 (by rfl) ⟨1141458, by rfl⟩ : syracuseStep 3043889 = 2282917) B2282917
theorem B8237645 : Blo 1202418 8237645 := bstep (se 3 (by rfl) ⟨1544558, by rfl⟩ : syracuseStep 8237645 = 3089117) B3089117
theorem B3043939 : Blo 1202418 3043939 := bstep (se 1 (by rfl) ⟨2282954, by rfl⟩ : syracuseStep 3043939 = 4565909) B4565909
theorem B3854947 : Blo 1202418 3854947 := bstep (se 1 (by rfl) ⟨2891210, by rfl⟩ : syracuseStep 3854947 = 5782421) B5782421
theorem B2708081 : Blo 1202418 2708081 := bstep (se 2 (by rfl) ⟨1015530, by rfl⟩ : syracuseStep 2708081 = 2031061) B2031061
theorem B2708099 : Blo 1202418 2708099 := bstep (se 1 (by rfl) ⟨2031074, by rfl⟩ : syracuseStep 2708099 = 4062149) B4062149
theorem B1446547 : Blo 1202418 1446547 := bstep (se 1 (by rfl) ⟨1084910, by rfl⟩ : syracuseStep 1446547 = 2169821) B2169821
theorem B5780173 : Blo 1202418 5780173 := bstep (se 3 (by rfl) ⟨1083782, by rfl⟩ : syracuseStep 5780173 = 2167565) B2167565
theorem B10277603 : Blo 1202418 10277603 := bstep (se 1 (by rfl) ⟨7708202, by rfl⟩ : syracuseStep 10277603 = 15416405) B15416405
theorem B3044081 : Blo 1202418 3044081 := bstep (se 2 (by rfl) ⟨1141530, by rfl⟩ : syracuseStep 3044081 = 2283061) B2283061
theorem B3855089 : Blo 1202418 3855089 := bstep (se 2 (by rfl) ⟨1445658, by rfl⟩ : syracuseStep 3855089 = 2891317) B2891317
theorem B3855203 : Blo 1202418 3855203 := bstep (se 1 (by rfl) ⟨2891402, by rfl⟩ : syracuseStep 3855203 = 5782805) B5782805
theorem B2708369 : Blo 1202418 2708369 := bstep (se 2 (by rfl) ⟨1015638, by rfl⟩ : syracuseStep 2708369 = 2031277) B2031277
theorem B2708387 : Blo 1202418 2708387 := bstep (se 1 (by rfl) ⟨2031290, by rfl⟩ : syracuseStep 2708387 = 4062581) B4062581
theorem B4568035 : Blo 1202418 4568035 := bstep (se 1 (by rfl) ⟨3426026, by rfl⟩ : syracuseStep 4568035 = 6852053) B6852053
theorem B4060205 : Blo 1202418 4060205 := bstep (se 3 (by rfl) ⟨761288, by rfl⟩ : syracuseStep 4060205 = 1522577) B1522577
theorem B2569315 : Blo 1202418 2569315 := bstep (se 1 (by rfl) ⟨1926986, by rfl⟩ : syracuseStep 2569315 = 3853973) B3853973
theorem B4060259 : Blo 1202418 4060259 := bstep (se 1 (by rfl) ⟨3045194, by rfl⟩ : syracuseStep 4060259 = 6090389) B6090389
theorem B2708657 : Blo 1202418 2708657 := bstep (se 2 (by rfl) ⟨1015746, by rfl⟩ : syracuseStep 2708657 = 2031493) B2031493
theorem B2708675 : Blo 1202418 2708675 := bstep (se 1 (by rfl) ⟨2031506, by rfl⟩ : syracuseStep 2708675 = 4063013) B4063013
theorem B1627409 : Blo 1202418 1627409 := bstep (se 2 (by rfl) ⟨610278, by rfl⟩ : syracuseStep 1627409 = 1220557) B1220557
theorem B5559587 : Blo 1202418 5559587 := bstep (se 1 (by rfl) ⟨4169690, by rfl⟩ : syracuseStep 5559587 = 8339381) B8339381
theorem B2282833 : Blo 1202418 2282833 := bstep (se 2 (by rfl) ⟨856062, by rfl⟩ : syracuseStep 2282833 = 1712125) B1712125
theorem B4060529 : Blo 1202418 4060529 := bstep (se 2 (by rfl) ⟨1522698, by rfl⟩ : syracuseStep 4060529 = 3045397) B3045397
theorem B2708945 : Blo 1202418 2708945 := bstep (se 2 (by rfl) ⟨1015854, by rfl⟩ : syracuseStep 2708945 = 2031709) B2031709
theorem B2708963 : Blo 1202418 2708963 := bstep (se 1 (by rfl) ⟨2031722, by rfl⟩ : syracuseStep 2708963 = 4063445) B4063445
theorem B4945457 : Blo 1202418 4945457 := bstep (se 2 (by rfl) ⟨1854546, by rfl⟩ : syracuseStep 4945457 = 3709093) B3709093
theorem B5797453 : Blo 1202418 5797453 := bstep (se 3 (by rfl) ⟨1087022, by rfl⟩ : syracuseStep 5797453 = 2174045) B2174045
theorem B2029171 : Blo 1202418 2029171 := bstep (se 1 (by rfl) ⟨1521878, by rfl⟩ : syracuseStep 2029171 = 3043757) B3043757
theorem B3045073 : Blo 1202418 3045073 := bstep (se 2 (by rfl) ⟨1141902, by rfl⟩ : syracuseStep 3045073 = 2283805) B2283805
theorem B6510307 : Blo 1202418 6510307 := bstep (se 1 (by rfl) ⟨4882730, by rfl⟩ : syracuseStep 6510307 = 9765461) B9765461
theorem B13014769 : Blo 1202418 13014769 := bstep (se 2 (by rfl) ⟨4880538, by rfl⟩ : syracuseStep 13014769 = 9761077) B9761077
theorem B2709233 : Blo 1202418 2709233 := bstep (se 2 (by rfl) ⟨1015962, by rfl⟩ : syracuseStep 2709233 = 2031925) B2031925
theorem B2029313 : Blo 1202418 2029313 := bstep (se 2 (by rfl) ⟨760992, by rfl⟩ : syracuseStep 2029313 = 1521985) B1521985
theorem B2709251 : Blo 1202418 2709251 := bstep (se 1 (by rfl) ⟨2031938, by rfl⟩ : syracuseStep 2709251 = 4063877) B4063877
theorem B6944525 : Blo 1202418 6944525 := bstep (se 3 (by rfl) ⟨1302098, by rfl⟩ : syracuseStep 6944525 = 2604197) B2604197
theorem B7812877 : Blo 1202418 7812877 := bstep (se 3 (by rfl) ⟨1464914, by rfl⟩ : syracuseStep 7812877 = 2929829) B2929829
theorem B3856177 : Blo 1202418 3856177 := bstep (se 2 (by rfl) ⟨1446066, by rfl⟩ : syracuseStep 3856177 = 2892133) B2892133
theorem B5486449 : Blo 1202418 5486449 := bstep (se 2 (by rfl) ⟨2057418, by rfl⟩ : syracuseStep 5486449 = 4114837) B4114837
theorem B6092657 : Blo 1202418 6092657 := bstep (se 2 (by rfl) ⟨2284746, by rfl⟩ : syracuseStep 6092657 = 4569493) B4569493
theorem B2029441 : Blo 1202418 2029441 := bstep (se 2 (by rfl) ⟨761040, by rfl⟩ : syracuseStep 2029441 = 1522081) B1522081
theorem B4061069 : Blo 1202418 4061069 := bstep (se 3 (by rfl) ⟨761450, by rfl⟩ : syracuseStep 4061069 = 1522901) B1522901
theorem B8681357 : Blo 1202418 8681357 := bstep (se 3 (by rfl) ⟨1627754, by rfl⟩ : syracuseStep 8681357 = 3255509) B3255509
theorem B2029475 : Blo 1202418 2029475 := bstep (se 1 (by rfl) ⟨1522106, by rfl⟩ : syracuseStep 2029475 = 3044213) B3044213
theorem B4061123 : Blo 1202418 4061123 := bstep (se 1 (by rfl) ⟨3045842, by rfl⟩ : syracuseStep 4061123 = 6091685) B6091685
theorem B3045347 : Blo 1202418 3045347 := bstep (se 1 (by rfl) ⟨2284010, by rfl⟩ : syracuseStep 3045347 = 4568021) B4568021
theorem B2709521 : Blo 1202418 2709521 := bstep (se 2 (by rfl) ⟨1016070, by rfl⟩ : syracuseStep 2709521 = 2032141) B2032141
theorem B2029603 : Blo 1202418 2029603 := bstep (se 1 (by rfl) ⟨1522202, by rfl⟩ : syracuseStep 2029603 = 3044405) B3044405
theorem B2709539 : Blo 1202418 2709539 := bstep (se 1 (by rfl) ⟨2032154, by rfl⟩ : syracuseStep 2709539 = 4064309) B4064309
theorem B1284179 : Blo 1202418 1284179 := bstep (se 1 (by rfl) ⟨963134, by rfl⟩ : syracuseStep 1284179 = 1926269) B1926269
theorem B2889827 : Blo 1202418 2889827 := bstep (se 1 (by rfl) ⟨2167370, by rfl⟩ : syracuseStep 2889827 = 4334741) B4334741
theorem B5486705 : Blo 1202418 5486705 := bstep (se 2 (by rfl) ⟨2057514, by rfl⟩ : syracuseStep 5486705 = 4115029) B4115029
theorem B3045539 : Blo 1202418 3045539 := bstep (se 1 (by rfl) ⟨2284154, by rfl⟩ : syracuseStep 3045539 = 4568309) B4568309
theorem B2029745 : Blo 1202418 2029745 := bstep (se 2 (by rfl) ⟨761154, by rfl⟩ : syracuseStep 2029745 = 1522309) B1522309
theorem B4061393 : Blo 1202418 4061393 := bstep (se 2 (by rfl) ⟨1523022, by rfl⟩ : syracuseStep 4061393 = 3046045) B3046045
theorem B2349283 : Blo 1202418 2349283 := bstep (se 1 (by rfl) ⟨1761962, by rfl⟩ : syracuseStep 2349283 = 3523925) B3523925
theorem B1202419 : Blo 1202418 1202419 := bstep (se 1 (by rfl) ⟨901814, by rfl⟩ : syracuseStep 1202419 = 1803629) B1803629
theorem B1202435 : Blo 1202418 1202435 := bstep (se 1 (by rfl) ⟨901826, by rfl⟩ : syracuseStep 1202435 = 1803653) B1803653
theorem B1202451 : Blo 1202418 1202451 := bstep (se 1 (by rfl) ⟨901838, by rfl⟩ : syracuseStep 1202451 = 1803677) B1803677
theorem B1202467 : Blo 1202418 1202467 := bstep (se 1 (by rfl) ⟨901850, by rfl⟩ : syracuseStep 1202467 = 1803701) B1803701
theorem B2029873 : Blo 1202418 2029873 := bstep (se 2 (by rfl) ⟨761202, by rfl⟩ : syracuseStep 2029873 = 1522405) B1522405
theorem B2570545 : Blo 1202418 2570545 := bstep (se 2 (by rfl) ⟨963954, by rfl⟩ : syracuseStep 2570545 = 1927909) B1927909
theorem B1202483 : Blo 1202418 1202483 := bstep (se 1 (by rfl) ⟨901862, by rfl⟩ : syracuseStep 1202483 = 1803725) B1803725
theorem B2709809 : Blo 1202418 2709809 := bstep (se 2 (by rfl) ⟨1016178, by rfl⟩ : syracuseStep 2709809 = 2032357) B2032357
theorem B1202499 : Blo 1202418 1202499 := bstep (se 1 (by rfl) ⟨901874, by rfl⟩ : syracuseStep 1202499 = 1803749) B1803749
theorem B2439491 : Blo 1202418 2439491 := bstep (se 1 (by rfl) ⟨1829618, by rfl⟩ : syracuseStep 2439491 = 3659237) B3659237
theorem B9263429 : Blo 1202418 9263429 := bstep (se 4 (by rfl) ⟨868446, by rfl⟩ : syracuseStep 9263429 = 1736893) B1736893
theorem B2709827 : Blo 1202418 2709827 := bstep (se 1 (by rfl) ⟨2032370, by rfl⟩ : syracuseStep 2709827 = 4064741) B4064741
theorem B3660113 : Blo 1202418 3660113 := bstep (se 2 (by rfl) ⟨1372542, by rfl⟩ : syracuseStep 3660113 = 2745085) B2745085
theorem B1202515 : Blo 1202418 1202515 := bstep (se 1 (by rfl) ⟨901886, by rfl⟩ : syracuseStep 1202515 = 1803773) B1803773
theorem B2029907 : Blo 1202418 2029907 := bstep (se 1 (by rfl) ⟨1522430, by rfl⟩ : syracuseStep 2029907 = 3044861) B3044861
theorem B1202531 : Blo 1202418 1202531 := bstep (se 1 (by rfl) ⟨901898, by rfl⟩ : syracuseStep 1202531 = 1803797) B1803797
theorem B2283889 : Blo 1202418 2283889 := bstep (se 2 (by rfl) ⟨856458, by rfl⟩ : syracuseStep 2283889 = 1712917) B1712917
theorem B1202547 : Blo 1202418 1202547 := bstep (se 1 (by rfl) ⟨901910, by rfl⟩ : syracuseStep 1202547 = 1803821) B1803821
theorem B1202563 : Blo 1202418 1202563 := bstep (se 1 (by rfl) ⟨901922, by rfl⟩ : syracuseStep 1202563 = 1803845) B1803845
theorem B1202579 : Blo 1202418 1202579 := bstep (se 1 (by rfl) ⟨901934, by rfl⟩ : syracuseStep 1202579 = 1803869) B1803869
theorem B1202595 : Blo 1202418 1202595 := bstep (se 1 (by rfl) ⟨901946, by rfl⟩ : syracuseStep 1202595 = 1803893) B1803893
theorem B4176305 : Blo 1202418 4176305 := bstep (se 2 (by rfl) ⟨1566114, by rfl⟩ : syracuseStep 4176305 = 3132229) B3132229
theorem B1202611 : Blo 1202418 1202611 := bstep (se 1 (by rfl) ⟨901958, by rfl⟩ : syracuseStep 1202611 = 1803917) B1803917
theorem B1202627 : Blo 1202418 1202627 := bstep (se 1 (by rfl) ⟨901970, by rfl⟩ : syracuseStep 1202627 = 1803941) B1803941
theorem B1202643 : Blo 1202418 1202643 := bstep (se 1 (by rfl) ⟨901982, by rfl⟩ : syracuseStep 1202643 = 1803965) B1803965
theorem B2030035 : Blo 1202418 2030035 := bstep (se 1 (by rfl) ⟨1522526, by rfl⟩ : syracuseStep 2030035 = 3045053) B3045053
theorem B1202659 : Blo 1202418 1202659 := bstep (se 1 (by rfl) ⟨901994, by rfl⟩ : syracuseStep 1202659 = 1803989) B1803989
theorem B1522147 : Blo 1202418 1522147 := bstep (se 1 (by rfl) ⟨1141610, by rfl⟩ : syracuseStep 1522147 = 2283221) B2283221
theorem B1202675 : Blo 1202418 1202675 := bstep (se 1 (by rfl) ⟨902006, by rfl⟩ : syracuseStep 1202675 = 1804013) B1804013
theorem B1202691 : Blo 1202418 1202691 := bstep (se 1 (by rfl) ⟨902018, by rfl⟩ : syracuseStep 1202691 = 1804037) B1804037
theorem B1202707 : Blo 1202418 1202707 := bstep (se 1 (by rfl) ⟨902030, by rfl⟩ : syracuseStep 1202707 = 1804061) B1804061
theorem B1202723 : Blo 1202418 1202723 := bstep (se 1 (by rfl) ⟨902042, by rfl⟩ : syracuseStep 1202723 = 1804085) B1804085
theorem B1202739 : Blo 1202418 1202739 := bstep (se 1 (by rfl) ⟨902054, by rfl⟩ : syracuseStep 1202739 = 1804109) B1804109
theorem B1202755 : Blo 1202418 1202755 := bstep (se 1 (by rfl) ⟨902066, by rfl⟩ : syracuseStep 1202755 = 1804133) B1804133
theorem B1522243 : Blo 1202418 1522243 := bstep (se 1 (by rfl) ⟨1141682, by rfl⟩ : syracuseStep 1522243 = 2283365) B2283365
theorem B1202771 : Blo 1202418 1202771 := bstep (se 1 (by rfl) ⟨902078, by rfl⟩ : syracuseStep 1202771 = 1804157) B1804157
theorem B2030177 : Blo 1202418 2030177 := bstep (se 2 (by rfl) ⟨761316, by rfl⟩ : syracuseStep 2030177 = 1522633) B1522633
theorem B1202787 : Blo 1202418 1202787 := bstep (se 1 (by rfl) ⟨902090, by rfl⟩ : syracuseStep 1202787 = 1804181) B1804181
theorem B2316899 : Blo 1202418 2316899 := bstep (se 1 (by rfl) ⟨1737674, by rfl⟩ : syracuseStep 2316899 = 3475349) B3475349
theorem B1202803 : Blo 1202418 1202803 := bstep (se 1 (by rfl) ⟨902102, by rfl⟩ : syracuseStep 1202803 = 1804205) B1804205
theorem B1202819 : Blo 1202418 1202819 := bstep (se 1 (by rfl) ⟨902114, by rfl⟩ : syracuseStep 1202819 = 1804229) B1804229
theorem B3906193 : Blo 1202418 3906193 := bstep (se 2 (by rfl) ⟨1464822, by rfl⟩ : syracuseStep 3906193 = 2929645) B2929645
theorem B1202835 : Blo 1202418 1202835 := bstep (se 1 (by rfl) ⟨902126, by rfl⟩ : syracuseStep 1202835 = 1804253) B1804253
theorem B1202851 : Blo 1202418 1202851 := bstep (se 1 (by rfl) ⟨902138, by rfl⟩ : syracuseStep 1202851 = 1804277) B1804277
theorem B1202867 : Blo 1202418 1202867 := bstep (se 1 (by rfl) ⟨902150, by rfl⟩ : syracuseStep 1202867 = 1804301) B1804301
theorem B1202883 : Blo 1202418 1202883 := bstep (se 1 (by rfl) ⟨902162, by rfl⟩ : syracuseStep 1202883 = 1804325) B1804325
theorem B1202899 : Blo 1202418 1202899 := bstep (se 1 (by rfl) ⟨902174, by rfl⟩ : syracuseStep 1202899 = 1804349) B1804349
theorem B2030305 : Blo 1202418 2030305 := bstep (se 2 (by rfl) ⟨761364, by rfl⟩ : syracuseStep 2030305 = 1522729) B1522729
theorem B1202915 : Blo 1202418 1202915 := bstep (se 1 (by rfl) ⟨902186, by rfl⟩ : syracuseStep 1202915 = 1804373) B1804373
theorem B4061933 : Blo 1202418 4061933 := bstep (se 3 (by rfl) ⟨761612, by rfl⟩ : syracuseStep 4061933 = 1523225) B1523225
theorem B1202931 : Blo 1202418 1202931 := bstep (se 1 (by rfl) ⟨902198, by rfl⟩ : syracuseStep 1202931 = 1804397) B1804397
theorem B1202947 : Blo 1202418 1202947 := bstep (se 1 (by rfl) ⟨902210, by rfl⟩ : syracuseStep 1202947 = 1804421) B1804421
theorem B2030339 : Blo 1202418 2030339 := bstep (se 1 (by rfl) ⟨1522754, by rfl⟩ : syracuseStep 2030339 = 3045509) B3045509
theorem B2284291 : Blo 1202418 2284291 := bstep (se 1 (by rfl) ⟨1713218, by rfl⟩ : syracuseStep 2284291 = 3426437) B3426437
theorem B1202963 : Blo 1202418 1202963 := bstep (se 1 (by rfl) ⟨902222, by rfl⟩ : syracuseStep 1202963 = 1804445) B1804445
theorem B34716437 : Blo 1202418 34716437 := bstep (se 6 (by rfl) ⟨813666, by rfl⟩ : syracuseStep 34716437 = 1627333) B1627333
theorem B1202979 : Blo 1202418 1202979 := bstep (se 1 (by rfl) ⟨902234, by rfl⟩ : syracuseStep 1202979 = 1804469) B1804469
theorem B4061987 : Blo 1202418 4061987 := bstep (se 1 (by rfl) ⟨3046490, by rfl⟩ : syracuseStep 4061987 = 6092981) B6092981
theorem B2284337 : Blo 1202418 2284337 := bstep (se 2 (by rfl) ⟨856626, by rfl⟩ : syracuseStep 2284337 = 1713253) B1713253
theorem B1202995 : Blo 1202418 1202995 := bstep (se 1 (by rfl) ⟨902246, by rfl⟩ : syracuseStep 1202995 = 1804493) B1804493
theorem B1203011 : Blo 1202418 1203011 := bstep (se 1 (by rfl) ⟨902258, by rfl⟩ : syracuseStep 1203011 = 1804517) B1804517
theorem B1284931 : Blo 1202418 1284931 := bstep (se 1 (by rfl) ⟨963698, by rfl⟩ : syracuseStep 1284931 = 1927397) B1927397
theorem B1203027 : Blo 1202418 1203027 := bstep (se 1 (by rfl) ⟨902270, by rfl⟩ : syracuseStep 1203027 = 1804541) B1804541
theorem B1203043 : Blo 1202418 1203043 := bstep (se 1 (by rfl) ⟨902282, by rfl⟩ : syracuseStep 1203043 = 1804565) B1804565
theorem B1203059 : Blo 1202418 1203059 := bstep (se 1 (by rfl) ⟨902294, by rfl⟩ : syracuseStep 1203059 = 1804589) B1804589
theorem B1203075 : Blo 1202418 1203075 := bstep (se 1 (by rfl) ⟨902306, by rfl⟩ : syracuseStep 1203075 = 1804613) B1804613
theorem B2030467 : Blo 1202418 2030467 := bstep (se 1 (by rfl) ⟨1522850, by rfl⟩ : syracuseStep 2030467 = 3045701) B3045701
theorem B1203091 : Blo 1202418 1203091 := bstep (se 1 (by rfl) ⟨902318, by rfl⟩ : syracuseStep 1203091 = 1804637) B1804637
theorem B1203107 : Blo 1202418 1203107 := bstep (se 1 (by rfl) ⟨902330, by rfl⟩ : syracuseStep 1203107 = 1804661) B1804661
theorem B1203123 : Blo 1202418 1203123 := bstep (se 1 (by rfl) ⟨902342, by rfl⟩ : syracuseStep 1203123 = 1804685) B1804685
theorem B1203139 : Blo 1202418 1203139 := bstep (se 1 (by rfl) ⟨902354, by rfl⟩ : syracuseStep 1203139 = 1804709) B1804709
theorem B3521485 : Blo 1202418 3521485 := bstep (se 3 (by rfl) ⟨660278, by rfl⟩ : syracuseStep 3521485 = 1320557) B1320557
theorem B1203155 : Blo 1202418 1203155 := bstep (se 1 (by rfl) ⟨902366, by rfl⟩ : syracuseStep 1203155 = 1804733) B1804733
theorem B1203171 : Blo 1202418 1203171 := bstep (se 1 (by rfl) ⟨902378, by rfl⟩ : syracuseStep 1203171 = 1804757) B1804757
theorem B1203187 : Blo 1202418 1203187 := bstep (se 1 (by rfl) ⟨902390, by rfl⟩ : syracuseStep 1203187 = 1804781) B1804781
theorem B1203203 : Blo 1202418 1203203 := bstep (se 1 (by rfl) ⟨902402, by rfl⟩ : syracuseStep 1203203 = 1804805) B1804805
theorem B2259971 : Blo 1202418 2259971 := bstep (se 1 (by rfl) ⟨1694978, by rfl⟩ : syracuseStep 2259971 = 3389957) B3389957
theorem B2030609 : Blo 1202418 2030609 := bstep (se 2 (by rfl) ⟨761478, by rfl⟩ : syracuseStep 2030609 = 1522957) B1522957
theorem B1203219 : Blo 1202418 1203219 := bstep (se 1 (by rfl) ⟨902414, by rfl⟩ : syracuseStep 1203219 = 1804829) B1804829
theorem B2890787 : Blo 1202418 2890787 := bstep (se 1 (by rfl) ⟨2168090, by rfl⟩ : syracuseStep 2890787 = 4336181) B4336181
theorem B1203235 : Blo 1202418 1203235 := bstep (se 1 (by rfl) ⟨902426, by rfl⟩ : syracuseStep 1203235 = 1804853) B1804853
theorem B4062257 : Blo 1202418 4062257 := bstep (se 2 (by rfl) ⟨1523346, by rfl⟩ : syracuseStep 4062257 = 3046693) B3046693
theorem B1522739 : Blo 1202418 1522739 := bstep (se 1 (by rfl) ⟨1142054, by rfl⟩ : syracuseStep 1522739 = 2284109) B2284109
theorem B1203251 : Blo 1202418 1203251 := bstep (se 1 (by rfl) ⟨902438, by rfl⟩ : syracuseStep 1203251 = 1804877) B1804877
theorem B1203267 : Blo 1202418 1203267 := bstep (se 1 (by rfl) ⟨902450, by rfl⟩ : syracuseStep 1203267 = 1804901) B1804901
theorem B2284625 : Blo 1202418 2284625 := bstep (se 2 (by rfl) ⟨856734, by rfl⟩ : syracuseStep 2284625 = 1713469) B1713469
theorem B3046481 : Blo 1202418 3046481 := bstep (se 2 (by rfl) ⟨1142430, by rfl⟩ : syracuseStep 3046481 = 2284861) B2284861
theorem B1203283 : Blo 1202418 1203283 := bstep (se 1 (by rfl) ⟨902462, by rfl⟩ : syracuseStep 1203283 = 1804925) B1804925
theorem B1203299 : Blo 1202418 1203299 := bstep (se 1 (by rfl) ⟨902474, by rfl⟩ : syracuseStep 1203299 = 1804949) B1804949
theorem B13360241 : Blo 1202418 13360241 := bstep (se 2 (by rfl) ⟨5010090, by rfl⟩ : syracuseStep 13360241 = 10020181) B10020181
theorem B2890865 : Blo 1202418 2890865 := bstep (se 2 (by rfl) ⟨1084074, by rfl⟩ : syracuseStep 2890865 = 2168149) B2168149
theorem B1203315 : Blo 1202418 1203315 := bstep (se 1 (by rfl) ⟨902486, by rfl⟩ : syracuseStep 1203315 = 1804973) B1804973
theorem B1203331 : Blo 1202418 1203331 := bstep (se 1 (by rfl) ⟨902498, by rfl⟩ : syracuseStep 1203331 = 1804997) B1804997
theorem B3046531 : Blo 1202418 3046531 := bstep (se 1 (by rfl) ⟨2284898, by rfl⟩ : syracuseStep 3046531 = 4569797) B4569797
theorem B4570253 : Blo 1202418 4570253 := bstep (se 3 (by rfl) ⟨856922, by rfl⟩ : syracuseStep 4570253 = 1713845) B1713845
theorem B2030737 : Blo 1202418 2030737 := bstep (se 2 (by rfl) ⟨761526, by rfl⟩ : syracuseStep 2030737 = 1523053) B1523053
theorem B1203347 : Blo 1202418 1203347 := bstep (se 1 (by rfl) ⟨902510, by rfl⟩ : syracuseStep 1203347 = 1805021) B1805021
theorem B1203363 : Blo 1202418 1203363 := bstep (se 1 (by rfl) ⟨902522, by rfl⟩ : syracuseStep 1203363 = 1805045) B1805045
theorem B5782691 : Blo 1202418 5782691 := bstep (se 1 (by rfl) ⟨4337018, by rfl⟩ : syracuseStep 5782691 = 8674037) B8674037
theorem B1203379 : Blo 1202418 1203379 := bstep (se 1 (by rfl) ⟨902534, by rfl⟩ : syracuseStep 1203379 = 1805069) B1805069
theorem B2030771 : Blo 1202418 2030771 := bstep (se 1 (by rfl) ⟨1523078, by rfl⟩ : syracuseStep 2030771 = 3046157) B3046157
theorem B1203395 : Blo 1202418 1203395 := bstep (se 1 (by rfl) ⟨902546, by rfl⟩ : syracuseStep 1203395 = 1805093) B1805093
theorem B1203411 : Blo 1202418 1203411 := bstep (se 1 (by rfl) ⟨902558, by rfl⟩ : syracuseStep 1203411 = 1805117) B1805117
theorem B1203427 : Blo 1202418 1203427 := bstep (se 1 (by rfl) ⟨902570, by rfl⟩ : syracuseStep 1203427 = 1805141) B1805141
theorem B1203443 : Blo 1202418 1203443 := bstep (se 1 (by rfl) ⟨902582, by rfl⟩ : syracuseStep 1203443 = 1805165) B1805165
theorem B1203459 : Blo 1202418 1203459 := bstep (se 1 (by rfl) ⟨902594, by rfl⟩ : syracuseStep 1203459 = 1805189) B1805189
theorem B3046673 : Blo 1202418 3046673 := bstep (se 2 (by rfl) ⟨1142502, by rfl⟩ : syracuseStep 3046673 = 2285005) B2285005
theorem B1203475 : Blo 1202418 1203475 := bstep (se 1 (by rfl) ⟨902606, by rfl⟩ : syracuseStep 1203475 = 1805213) B1805213
theorem B1203491 : Blo 1202418 1203491 := bstep (se 1 (by rfl) ⟨902618, by rfl⟩ : syracuseStep 1203491 = 1805237) B1805237
theorem B6094115 : Blo 1202418 6094115 := bstep (se 1 (by rfl) ⟨4570586, by rfl⟩ : syracuseStep 6094115 = 9141173) B9141173
theorem B2030899 : Blo 1202418 2030899 := bstep (se 1 (by rfl) ⟨1523174, by rfl⟩ : syracuseStep 2030899 = 3046349) B3046349
theorem B1203507 : Blo 1202418 1203507 := bstep (se 1 (by rfl) ⟨902630, by rfl⟩ : syracuseStep 1203507 = 1805261) B1805261
theorem B1203523 : Blo 1202418 1203523 := bstep (se 1 (by rfl) ⟨902642, by rfl⟩ : syracuseStep 1203523 = 1805285) B1805285
theorem B1203539 : Blo 1202418 1203539 := bstep (se 1 (by rfl) ⟨902654, by rfl⟩ : syracuseStep 1203539 = 1805309) B1805309
theorem B1203555 : Blo 1202418 1203555 := bstep (se 1 (by rfl) ⟨902666, by rfl⟩ : syracuseStep 1203555 = 1805333) B1805333
theorem B1203571 : Blo 1202418 1203571 := bstep (se 1 (by rfl) ⟨902678, by rfl⟩ : syracuseStep 1203571 = 1805357) B1805357
theorem B1203587 : Blo 1202418 1203587 := bstep (se 1 (by rfl) ⟨902690, by rfl⟩ : syracuseStep 1203587 = 1805381) B1805381
theorem B1203603 : Blo 1202418 1203603 := bstep (se 1 (by rfl) ⟨902702, by rfl⟩ : syracuseStep 1203603 = 1805405) B1805405
theorem B1203619 : Blo 1202418 1203619 := bstep (se 1 (by rfl) ⟨902714, by rfl⟩ : syracuseStep 1203619 = 1805429) B1805429
theorem B1203635 : Blo 1202418 1203635 := bstep (se 1 (by rfl) ⟨902726, by rfl⟩ : syracuseStep 1203635 = 1805453) B1805453
theorem B13016501 : Blo 1202418 13016501 := bstep (se 5 (by rfl) ⟨610148, by rfl⟩ : syracuseStep 13016501 = 1220297) B1220297
theorem B2031041 : Blo 1202418 2031041 := bstep (se 2 (by rfl) ⟨761640, by rfl⟩ : syracuseStep 2031041 = 1523281) B1523281
theorem B1203651 : Blo 1202418 1203651 := bstep (se 1 (by rfl) ⟨902738, by rfl⟩ : syracuseStep 1203651 = 1805477) B1805477
theorem B1203667 : Blo 1202418 1203667 := bstep (se 1 (by rfl) ⟨902750, by rfl⟩ : syracuseStep 1203667 = 1805501) B1805501
theorem B1203683 : Blo 1202418 1203683 := bstep (se 1 (by rfl) ⟨902762, by rfl⟩ : syracuseStep 1203683 = 1805525) B1805525
theorem B1203699 : Blo 1202418 1203699 := bstep (se 1 (by rfl) ⟨902774, by rfl⟩ : syracuseStep 1203699 = 1805549) B1805549
theorem B1203715 : Blo 1202418 1203715 := bstep (se 1 (by rfl) ⟨902786, by rfl⟩ : syracuseStep 1203715 = 1805573) B1805573
theorem B1203731 : Blo 1202418 1203731 := bstep (se 1 (by rfl) ⟨902798, by rfl⟩ : syracuseStep 1203731 = 1805597) B1805597
theorem B1203747 : Blo 1202418 1203747 := bstep (se 1 (by rfl) ⟨902810, by rfl⟩ : syracuseStep 1203747 = 1805621) B1805621
theorem B1203763 : Blo 1202418 1203763 := bstep (se 1 (by rfl) ⟨902822, by rfl⟩ : syracuseStep 1203763 = 1805645) B1805645
theorem B2031169 : Blo 1202418 2031169 := bstep (se 2 (by rfl) ⟨761688, by rfl⟩ : syracuseStep 2031169 = 1523377) B1523377
theorem B1203779 : Blo 1202418 1203779 := bstep (se 1 (by rfl) ⟨902834, by rfl⟩ : syracuseStep 1203779 = 1805669) B1805669
theorem B4062797 : Blo 1202418 4062797 := bstep (se 3 (by rfl) ⟨761774, by rfl⟩ : syracuseStep 4062797 = 1523549) B1523549
theorem B1203795 : Blo 1202418 1203795 := bstep (se 1 (by rfl) ⟨902846, by rfl⟩ : syracuseStep 1203795 = 1805693) B1805693
theorem B2031203 : Blo 1202418 2031203 := bstep (se 1 (by rfl) ⟨1523402, by rfl⟩ : syracuseStep 2031203 = 3046805) B3046805
theorem B1203811 : Blo 1202418 1203811 := bstep (se 1 (by rfl) ⟨902858, by rfl⟩ : syracuseStep 1203811 = 1805717) B1805717
theorem B1203827 : Blo 1202418 1203827 := bstep (se 1 (by rfl) ⟨902870, by rfl⟩ : syracuseStep 1203827 = 1805741) B1805741
theorem B4062851 : Blo 1202418 4062851 := bstep (se 1 (by rfl) ⟨3047138, by rfl⟩ : syracuseStep 4062851 = 6094277) B6094277
theorem B1203843 : Blo 1202418 1203843 := bstep (se 1 (by rfl) ⟨902882, by rfl⟩ : syracuseStep 1203843 = 1805765) B1805765
theorem B1203859 : Blo 1202418 1203859 := bstep (se 1 (by rfl) ⟨902894, by rfl⟩ : syracuseStep 1203859 = 1805789) B1805789
theorem B1203875 : Blo 1202418 1203875 := bstep (se 1 (by rfl) ⟨902906, by rfl⟩ : syracuseStep 1203875 = 1805813) B1805813
theorem B1203891 : Blo 1202418 1203891 := bstep (se 1 (by rfl) ⟨902918, by rfl⟩ : syracuseStep 1203891 = 1805837) B1805837
theorem B1203907 : Blo 1202418 1203907 := bstep (se 1 (by rfl) ⟨902930, by rfl⟩ : syracuseStep 1203907 = 1805861) B1805861
theorem B5144269 : Blo 1202418 5144269 := bstep (se 3 (by rfl) ⟨964550, by rfl⟩ : syracuseStep 5144269 = 1929101) B1929101
theorem B1203923 : Blo 1202418 1203923 := bstep (se 1 (by rfl) ⟨902942, by rfl⟩ : syracuseStep 1203923 = 1805885) B1805885
theorem B12517091 : Blo 1202418 12517091 := bstep (se 1 (by rfl) ⟨9387818, by rfl⟩ : syracuseStep 12517091 = 18775637) B18775637
theorem B2031331 : Blo 1202418 2031331 := bstep (se 1 (by rfl) ⟨1523498, by rfl⟩ : syracuseStep 2031331 = 3046997) B3046997
theorem B1203939 : Blo 1202418 1203939 := bstep (se 1 (by rfl) ⟨902954, by rfl⟩ : syracuseStep 1203939 = 1805909) B1805909
theorem B1523443 : Blo 1202418 1523443 := bstep (se 1 (by rfl) ⟨1142582, by rfl⟩ : syracuseStep 1523443 = 2285165) B2285165
theorem B1203955 : Blo 1202418 1203955 := bstep (se 1 (by rfl) ⟨902966, by rfl⟩ : syracuseStep 1203955 = 1805933) B1805933
theorem B1203971 : Blo 1202418 1203971 := bstep (se 1 (by rfl) ⟨902978, by rfl⟩ : syracuseStep 1203971 = 1805957) B1805957
theorem B2572049 : Blo 1202418 2572049 := bstep (se 2 (by rfl) ⟨964518, by rfl⟩ : syracuseStep 2572049 = 1929037) B1929037
theorem B1203987 : Blo 1202418 1203987 := bstep (se 1 (by rfl) ⟨902990, by rfl⟩ : syracuseStep 1203987 = 1805981) B1805981
theorem B2285347 : Blo 1202418 2285347 := bstep (se 1 (by rfl) ⟨1714010, by rfl⟩ : syracuseStep 2285347 = 3428021) B3428021
theorem B1204003 : Blo 1202418 1204003 := bstep (se 1 (by rfl) ⟨903002, by rfl⟩ : syracuseStep 1204003 = 1806005) B1806005
theorem B2572067 : Blo 1202418 2572067 := bstep (se 1 (by rfl) ⟨1929050, by rfl⟩ : syracuseStep 2572067 = 3858101) B3858101
theorem B5783345 : Blo 1202418 5783345 := bstep (se 2 (by rfl) ⟨2168754, by rfl⟩ : syracuseStep 5783345 = 4337509) B4337509
theorem B1204019 : Blo 1202418 1204019 := bstep (se 1 (by rfl) ⟨903014, by rfl⟩ : syracuseStep 1204019 = 1806029) B1806029
theorem B1285939 : Blo 1202418 1285939 := bstep (se 1 (by rfl) ⟨964454, by rfl⟩ : syracuseStep 1285939 = 1928909) B1928909
theorem B2744131 : Blo 1202418 2744131 := bstep (se 1 (by rfl) ⟨2058098, by rfl⟩ : syracuseStep 2744131 = 4116197) B4116197
theorem B1204035 : Blo 1202418 1204035 := bstep (se 1 (by rfl) ⟨903026, by rfl⟩ : syracuseStep 1204035 = 1806053) B1806053
theorem B10272581 : Blo 1202418 10272581 := bstep (se 4 (by rfl) ⟨963054, by rfl⟩ : syracuseStep 10272581 = 1926109) B1926109
theorem B1523539 : Blo 1202418 1523539 := bstep (se 1 (by rfl) ⟨1142654, by rfl⟩ : syracuseStep 1523539 = 2285309) B2285309
theorem B1204051 : Blo 1202418 1204051 := bstep (se 1 (by rfl) ⟨903038, by rfl⟩ : syracuseStep 1204051 = 1806077) B1806077
theorem B1204067 : Blo 1202418 1204067 := bstep (se 1 (by rfl) ⟨903050, by rfl⟩ : syracuseStep 1204067 = 1806101) B1806101
theorem B2031473 : Blo 1202418 2031473 := bstep (se 2 (by rfl) ⟨761802, by rfl⟩ : syracuseStep 2031473 = 1523605) B1523605
theorem B1204083 : Blo 1202418 1204083 := bstep (se 1 (by rfl) ⟨903062, by rfl⟩ : syracuseStep 1204083 = 1806125) B1806125
theorem B1204099 : Blo 1202418 1204099 := bstep (se 1 (by rfl) ⟨903074, by rfl⟩ : syracuseStep 1204099 = 1806149) B1806149
theorem B4063121 : Blo 1202418 4063121 := bstep (se 2 (by rfl) ⟨1523670, by rfl⟩ : syracuseStep 4063121 = 3047341) B3047341
theorem B1204115 : Blo 1202418 1204115 := bstep (se 1 (by rfl) ⟨903086, by rfl⟩ : syracuseStep 1204115 = 1806173) B1806173
theorem B1204131 : Blo 1202418 1204131 := bstep (se 1 (by rfl) ⟨903098, by rfl⟩ : syracuseStep 1204131 = 1806197) B1806197
theorem B1204147 : Blo 1202418 1204147 := bstep (se 1 (by rfl) ⟨903110, by rfl⟩ : syracuseStep 1204147 = 1806221) B1806221
theorem B1204163 : Blo 1202418 1204163 := bstep (se 1 (by rfl) ⟨903122, by rfl⟩ : syracuseStep 1204163 = 1806245) B1806245
theorem B1204179 : Blo 1202418 1204179 := bstep (se 1 (by rfl) ⟨903134, by rfl⟩ : syracuseStep 1204179 = 1806269) B1806269
theorem B1204195 : Blo 1202418 1204195 := bstep (se 1 (by rfl) ⟨903146, by rfl⟩ : syracuseStep 1204195 = 1806293) B1806293
theorem B2031601 : Blo 1202418 2031601 := bstep (se 2 (by rfl) ⟨761850, by rfl⟩ : syracuseStep 2031601 = 1523701) B1523701
theorem B1204211 : Blo 1202418 1204211 := bstep (se 1 (by rfl) ⟨903158, by rfl⟩ : syracuseStep 1204211 = 1806317) B1806317
theorem B1204235 : Blo 1202418 1204235 := bstep (se 1 (by rfl) ⟨903176, by rfl⟩ : syracuseStep 1204235 = 1806353) B1806353
theorem B1204247 : Blo 1202418 1204247 := bstep (se 1 (by rfl) ⟨903185, by rfl⟩ : syracuseStep 1204247 = 1806371) B1806371
theorem B1204267 : Blo 1202418 1204267 := bstep (se 1 (by rfl) ⟨903200, by rfl⟩ : syracuseStep 1204267 = 1806401) B1806401
theorem B4063283 : Blo 1202418 4063283 := bstep (se 1 (by rfl) ⟨3047462, by rfl⟩ : syracuseStep 4063283 = 6094925) B6094925
theorem B1204279 : Blo 1202418 1204279 := bstep (se 1 (by rfl) ⟨903209, by rfl⟩ : syracuseStep 1204279 = 1806419) B1806419
theorem B1204299 : Blo 1202418 1204299 := bstep (se 1 (by rfl) ⟨903224, by rfl⟩ : syracuseStep 1204299 = 1806449) B1806449
theorem B1204311 : Blo 1202418 1204311 := bstep (se 1 (by rfl) ⟨903233, by rfl⟩ : syracuseStep 1204311 = 1806467) B1806467
theorem B4571225 : Blo 1202418 4571225 := bstep (se 2 (by rfl) ⟨1714209, by rfl⟩ : syracuseStep 4571225 = 3428419) B3428419
theorem B7708765 : Blo 1202418 7708765 := bstep (se 3 (by rfl) ⟨1445393, by rfl⟩ : syracuseStep 7708765 = 2890787) B2890787
theorem B1204331 : Blo 1202418 1204331 := bstep (se 1 (by rfl) ⟨903248, by rfl⟩ : syracuseStep 1204331 = 1806497) B1806497
theorem B1204343 : Blo 1202418 1204343 := bstep (se 1 (by rfl) ⟨903257, by rfl⟩ : syracuseStep 1204343 = 1806515) B1806515
theorem B1204363 : Blo 1202418 1204363 := bstep (se 1 (by rfl) ⟨903272, by rfl⟩ : syracuseStep 1204363 = 1806545) B1806545
theorem B8667287 : Blo 1202418 8667287 := bstep (se 1 (by rfl) ⟨6500465, by rfl⟩ : syracuseStep 8667287 = 13000931) B13000931
theorem B1712279 : Blo 1202418 1712279 := bstep (se 1 (by rfl) ⟨1284209, by rfl⟩ : syracuseStep 1712279 = 2568419) B2568419
theorem B1523863 : Blo 1202418 1523863 := bstep (se 1 (by rfl) ⟨1142897, by rfl⟩ : syracuseStep 1523863 = 2285795) B2285795
theorem B1204375 : Blo 1202418 1204375 := bstep (se 1 (by rfl) ⟨903281, by rfl⟩ : syracuseStep 1204375 = 1806563) B1806563
theorem B1204395 : Blo 1202418 1204395 := bstep (se 1 (by rfl) ⟨903296, by rfl⟩ : syracuseStep 1204395 = 1806593) B1806593
theorem B6856883 : Blo 1202418 6856883 := bstep (se 1 (by rfl) ⟨5142662, by rfl⟩ : syracuseStep 6856883 = 10285325) B10285325
theorem B1204407 : Blo 1202418 1204407 := bstep (se 1 (by rfl) ⟨903305, by rfl⟩ : syracuseStep 1204407 = 1806611) B1806611
theorem B8790221 : Blo 1202418 8790221 := bstep (se 3 (by rfl) ⟨1648166, by rfl⟩ : syracuseStep 8790221 = 3296333) B3296333
theorem B35627309 : Blo 1202418 35627309 := bstep (se 3 (by rfl) ⟨6680120, by rfl⟩ : syracuseStep 35627309 = 13360241) B13360241
theorem B4571437 : Blo 1202418 4571437 := bstep (se 3 (by rfl) ⟨857144, by rfl⟩ : syracuseStep 4571437 = 1714289) B1714289
theorem B4063553 : Blo 1202418 4063553 := bstep (se 2 (by rfl) ⟨1523832, by rfl⟩ : syracuseStep 4063553 = 3047665) B3047665
theorem B2031959 : Blo 1202418 2031959 := bstep (se 1 (by rfl) ⟨1523969, by rfl⟩ : syracuseStep 2031959 = 3047939) B3047939
theorem B2285977 : Blo 1202418 2285977 := bstep (se 2 (by rfl) ⟨857241, by rfl⟩ : syracuseStep 2285977 = 1714483) B1714483
theorem B10273229 : Blo 1202418 10273229 := bstep (se 3 (by rfl) ⟨1926230, by rfl⟩ : syracuseStep 10273229 = 3852461) B3852461
theorem B2032087 : Blo 1202418 2032087 := bstep (se 1 (by rfl) ⟨1524065, by rfl⟩ : syracuseStep 2032087 = 3048131) B3048131
theorem B4571741 : Blo 1202418 4571741 := bstep (se 3 (by rfl) ⟨857201, by rfl⟩ : syracuseStep 4571741 = 1714403) B1714403
theorem B8667749 : Blo 1202418 8667749 := bstep (se 4 (by rfl) ⟨812601, by rfl⟩ : syracuseStep 8667749 = 1625203) B1625203
theorem B6505309 : Blo 1202418 6505309 := bstep (se 3 (by rfl) ⟨1219745, by rfl⟩ : syracuseStep 6505309 = 2439491) B2439491
theorem B4064093 : Blo 1202418 4064093 := bstep (se 3 (by rfl) ⟨762017, by rfl⟩ : syracuseStep 4064093 = 1524035) B1524035
theorem B13697909 : Blo 1202418 13697909 := bstep (se 5 (by rfl) ⟨642089, by rfl⟩ : syracuseStep 13697909 = 1284179) B1284179
theorem B4334509 : Blo 1202418 4334509 := bstep (se 3 (by rfl) ⟨812720, by rfl⟩ : syracuseStep 4334509 = 1625441) B1625441
theorem B11731985 : Blo 1202418 11731985 := bstep (se 2 (by rfl) ⟨4399494, by rfl⟩ : syracuseStep 11731985 = 8798989) B8798989
theorem B29295685 : Blo 1202418 29295685 := bstep (se 4 (by rfl) ⟨2746470, by rfl⟩ : syracuseStep 29295685 = 5492941) B5492941
theorem B1713241 : Blo 1202418 1713241 := bstep (se 2 (by rfl) ⟨642465, by rfl⟩ : syracuseStep 1713241 = 1284931) B1284931
theorem B1352875 : Blo 1202418 1352875 := bstep (se 1 (by rfl) ⟨1014656, by rfl⟩ : syracuseStep 1352875 = 2029313) B2029313
theorem B4629683 : Blo 1202418 4629683 := bstep (se 1 (by rfl) ⟨3472262, by rfl⟩ : syracuseStep 4629683 = 6944525) B6944525
theorem B1352983 : Blo 1202418 1352983 := bstep (se 1 (by rfl) ⟨1014737, by rfl⟩ : syracuseStep 1352983 = 2029475) B2029475
theorem B6096221 : Blo 1202418 6096221 := bstep (se 3 (by rfl) ⟨1143041, by rfl⟩ : syracuseStep 6096221 = 2286083) B2286083
theorem B1803659 : Blo 1202418 1803659 := bstep (se 1 (by rfl) ⟨1352744, by rfl⟩ : syracuseStep 1803659 = 2705489) B2705489
theorem B1803671 : Blo 1202418 1803671 := bstep (se 1 (by rfl) ⟨1352753, by rfl⟩ : syracuseStep 1803671 = 2705507) B2705507
theorem B1926551 : Blo 1202418 1926551 := bstep (se 1 (by rfl) ⟨1444913, by rfl⟩ : syracuseStep 1926551 = 2889827) B2889827
theorem B1738135 : Blo 1202418 1738135 := bstep (se 1 (by rfl) ⟨1303601, by rfl⟩ : syracuseStep 1738135 = 2607203) B2607203
theorem B1353163 : Blo 1202418 1353163 := bstep (se 1 (by rfl) ⟨1014872, by rfl⟩ : syracuseStep 1353163 = 2029745) B2029745
theorem B1803737 : Blo 1202418 1803737 := bstep (se 2 (by rfl) ⟨676401, by rfl⟩ : syracuseStep 1803737 = 1352803) B1352803
theorem B3425753 : Blo 1202418 3425753 := bstep (se 2 (by rfl) ⟨1284657, by rfl⟩ : syracuseStep 3425753 = 2569315) B2569315
theorem B1353271 : Blo 1202418 1353271 := bstep (se 1 (by rfl) ⟨1014953, by rfl⟩ : syracuseStep 1353271 = 2029907) B2029907
theorem B1803851 : Blo 1202418 1803851 := bstep (se 1 (by rfl) ⟨1352888, by rfl⟩ : syracuseStep 1803851 = 2705777) B2705777
theorem B1803863 : Blo 1202418 1803863 := bstep (se 1 (by rfl) ⟨1352897, by rfl⟩ : syracuseStep 1803863 = 2705795) B2705795
theorem B6858341 : Blo 1202418 6858341 := bstep (se 4 (by rfl) ⟨642969, by rfl⟩ : syracuseStep 6858341 = 1285939) B1285939
theorem B1803929 : Blo 1202418 1803929 := bstep (se 2 (by rfl) ⟨676473, by rfl⟩ : syracuseStep 1803929 = 1352947) B1352947
theorem B1353451 : Blo 1202418 1353451 := bstep (se 1 (by rfl) ⟨1015088, by rfl⟩ : syracuseStep 1353451 = 2030177) B2030177
theorem B1804043 : Blo 1202418 1804043 := bstep (se 1 (by rfl) ⟨1353032, by rfl⟩ : syracuseStep 1804043 = 2706065) B2706065
theorem B1804055 : Blo 1202418 1804055 := bstep (se 1 (by rfl) ⟨1353041, by rfl⟩ : syracuseStep 1804055 = 2706083) B2706083
theorem B1353559 : Blo 1202418 1353559 := bstep (se 1 (by rfl) ⟨1015169, by rfl⟩ : syracuseStep 1353559 = 2030339) B2030339
theorem B1804121 : Blo 1202418 1804121 := bstep (se 2 (by rfl) ⟨676545, by rfl⟩ : syracuseStep 1804121 = 1353091) B1353091
theorem B23144291 : Blo 1202418 23144291 := bstep (se 1 (by rfl) ⟨17358218, by rfl⟩ : syracuseStep 23144291 = 34716437) B34716437
theorem B1804235 : Blo 1202418 1804235 := bstep (se 1 (by rfl) ⟨1353176, by rfl⟩ : syracuseStep 1804235 = 2706353) B2706353
theorem B1804247 : Blo 1202418 1804247 := bstep (se 1 (by rfl) ⟨1353185, by rfl⟩ : syracuseStep 1804247 = 2706371) B2706371
theorem B1353739 : Blo 1202418 1353739 := bstep (se 1 (by rfl) ⟨1015304, by rfl⟩ : syracuseStep 1353739 = 2030609) B2030609
theorem B1804313 : Blo 1202418 1804313 := bstep (se 2 (by rfl) ⟨676617, by rfl⟩ : syracuseStep 1804313 = 1353235) B1353235
theorem B6088769 : Blo 1202418 6088769 := bstep (se 2 (by rfl) ⟨2283288, by rfl⟩ : syracuseStep 6088769 = 4566577) B4566577
theorem B1927243 : Blo 1202418 1927243 := bstep (se 1 (by rfl) ⟨1445432, by rfl⟩ : syracuseStep 1927243 = 2890865) B2890865
theorem B1353847 : Blo 1202418 1353847 := bstep (se 1 (by rfl) ⟨1015385, by rfl⟩ : syracuseStep 1353847 = 2030771) B2030771
theorem B1804427 : Blo 1202418 1804427 := bstep (se 1 (by rfl) ⟨1353320, by rfl⟩ : syracuseStep 1804427 = 2706641) B2706641
theorem B1804439 : Blo 1202418 1804439 := bstep (se 1 (by rfl) ⟨1353329, by rfl⟩ : syracuseStep 1804439 = 2706659) B2706659
theorem B2705561 : Blo 1202418 2705561 := bstep (se 2 (by rfl) ⟨1014585, by rfl⟩ : syracuseStep 2705561 = 2029171) B2029171
theorem B6850777 : Blo 1202418 6850777 := bstep (se 2 (by rfl) ⟨2569041, by rfl⟩ : syracuseStep 6850777 = 5138083) B5138083
theorem B1804505 : Blo 1202418 1804505 := bstep (se 2 (by rfl) ⟨676689, by rfl⟩ : syracuseStep 1804505 = 1353379) B1353379
theorem B2705651 : Blo 1202418 2705651 := bstep (se 1 (by rfl) ⟨2029238, by rfl⟩ : syracuseStep 2705651 = 4058477) B4058477
theorem B6859025 : Blo 1202418 6859025 := bstep (se 2 (by rfl) ⟨2572134, by rfl⟩ : syracuseStep 6859025 = 5144269) B5144269
theorem B2705687 : Blo 1202418 2705687 := bstep (se 1 (by rfl) ⟨2029265, by rfl⟩ : syracuseStep 2705687 = 4058531) B4058531
theorem B8677667 : Blo 1202418 8677667 := bstep (se 1 (by rfl) ⟨6508250, by rfl⟩ : syracuseStep 8677667 = 13016501) B13016501
theorem B1354027 : Blo 1202418 1354027 := bstep (se 1 (by rfl) ⟨1015520, by rfl⟩ : syracuseStep 1354027 = 2031041) B2031041
theorem B17353025 : Blo 1202418 17353025 := bstep (se 2 (by rfl) ⟨6507384, by rfl⟩ : syracuseStep 17353025 = 13014769) B13014769
theorem B1804619 : Blo 1202418 1804619 := bstep (se 1 (by rfl) ⟨1353464, by rfl⟩ : syracuseStep 1804619 = 2706929) B2706929
theorem B1804631 : Blo 1202418 1804631 := bstep (se 1 (by rfl) ⟨1353473, by rfl⟩ : syracuseStep 1804631 = 2706947) B2706947
theorem B1354135 : Blo 1202418 1354135 := bstep (se 1 (by rfl) ⟨1015601, by rfl⟩ : syracuseStep 1354135 = 2031203) B2031203
theorem B1804697 : Blo 1202418 1804697 := bstep (se 2 (by rfl) ⟨676761, by rfl⟩ : syracuseStep 1804697 = 1353523) B1353523
theorem B2705867 : Blo 1202418 2705867 := bstep (se 1 (by rfl) ⟨2029400, by rfl⟩ : syracuseStep 2705867 = 4058801) B4058801
theorem B2705921 : Blo 1202418 2705921 := bstep (se 2 (by rfl) ⟨1014720, by rfl⟩ : syracuseStep 2705921 = 2029441) B2029441
theorem B1804811 : Blo 1202418 1804811 := bstep (se 1 (by rfl) ⟨1353608, by rfl⟩ : syracuseStep 1804811 = 2707217) B2707217
theorem B1714699 : Blo 1202418 1714699 := bstep (se 1 (by rfl) ⟨1286024, by rfl⟩ : syracuseStep 1714699 = 2572049) B2572049
theorem B1804823 : Blo 1202418 1804823 := bstep (se 1 (by rfl) ⟨1353617, by rfl⟩ : syracuseStep 1804823 = 2707235) B2707235
theorem B1714711 : Blo 1202418 1714711 := bstep (se 1 (by rfl) ⟨1286033, by rfl⟩ : syracuseStep 1714711 = 2572067) B2572067
theorem B1354315 : Blo 1202418 1354315 := bstep (se 1 (by rfl) ⟨1015736, by rfl⟩ : syracuseStep 1354315 = 2031473) B2031473
theorem B1804889 : Blo 1202418 1804889 := bstep (se 2 (by rfl) ⟨676833, by rfl⟩ : syracuseStep 1804889 = 1353667) B1353667
theorem B1354423 : Blo 1202418 1354423 := bstep (se 1 (by rfl) ⟨1015817, by rfl⟩ : syracuseStep 1354423 = 2031635) B2031635
theorem B1805003 : Blo 1202418 1805003 := bstep (se 1 (by rfl) ⟨1353752, by rfl⟩ : syracuseStep 1805003 = 2707505) B2707505
theorem B3427019 : Blo 1202418 3427019 := bstep (se 1 (by rfl) ⟨2570264, by rfl⟩ : syracuseStep 3427019 = 5140529) B5140529
theorem B1805015 : Blo 1202418 1805015 := bstep (se 1 (by rfl) ⟨1353761, by rfl⟩ : syracuseStep 1805015 = 2707523) B2707523
theorem B2706137 : Blo 1202418 2706137 := bstep (se 2 (by rfl) ⟨1014801, by rfl⟩ : syracuseStep 2706137 = 2029603) B2029603
theorem B1805081 : Blo 1202418 1805081 := bstep (se 2 (by rfl) ⟨676905, by rfl⟩ : syracuseStep 1805081 = 1353811) B1353811
theorem B10275619 : Blo 1202418 10275619 := bstep (se 1 (by rfl) ⟨7706714, by rfl⟩ : syracuseStep 10275619 = 15413429) B15413429
theorem B2706227 : Blo 1202418 2706227 := bstep (se 1 (by rfl) ⟨2029670, by rfl⟩ : syracuseStep 2706227 = 4059341) B4059341
theorem B8227649 : Blo 1202418 8227649 := bstep (se 2 (by rfl) ⟨3085368, by rfl⟩ : syracuseStep 8227649 = 6170737) B6170737
theorem B2706263 : Blo 1202418 2706263 := bstep (se 1 (by rfl) ⟨2029697, by rfl⟩ : syracuseStep 2706263 = 4059395) B4059395
theorem B1354603 : Blo 1202418 1354603 := bstep (se 1 (by rfl) ⟨1015952, by rfl⟩ : syracuseStep 1354603 = 2031905) B2031905
theorem B1805195 : Blo 1202418 1805195 := bstep (se 1 (by rfl) ⟨1353896, by rfl⟩ : syracuseStep 1805195 = 2707793) B2707793
theorem B1805207 : Blo 1202418 1805207 := bstep (se 1 (by rfl) ⟨1353905, by rfl⟩ : syracuseStep 1805207 = 2707811) B2707811
theorem B13003697 : Blo 1202418 13003697 := bstep (se 2 (by rfl) ⟨4876386, by rfl⟩ : syracuseStep 13003697 = 9752773) B9752773
theorem B1354711 : Blo 1202418 1354711 := bstep (se 1 (by rfl) ⟨1016033, by rfl⟩ : syracuseStep 1354711 = 2032067) B2032067
theorem B1805273 : Blo 1202418 1805273 := bstep (se 2 (by rfl) ⟨676977, by rfl⟩ : syracuseStep 1805273 = 1353955) B1353955
theorem B3132377 : Blo 1202418 3132377 := bstep (se 2 (by rfl) ⟨1174641, by rfl⟩ : syracuseStep 3132377 = 2349283) B2349283
theorem B2706443 : Blo 1202418 2706443 := bstep (se 1 (by rfl) ⟨2029832, by rfl⟩ : syracuseStep 2706443 = 4059665) B4059665
theorem B4877329 : Blo 1202418 4877329 := bstep (se 2 (by rfl) ⟨1828998, by rfl⟩ : syracuseStep 4877329 = 3657997) B3657997
theorem B5491763 : Blo 1202418 5491763 := bstep (se 1 (by rfl) ⟨4118822, by rfl⟩ : syracuseStep 5491763 = 8237645) B8237645
theorem B2706497 : Blo 1202418 2706497 := bstep (se 2 (by rfl) ⟨1014936, by rfl⟩ : syracuseStep 2706497 = 2029873) B2029873
theorem B4566091 : Blo 1202418 4566091 := bstep (se 1 (by rfl) ⟨3424568, by rfl⟩ : syracuseStep 4566091 = 6849137) B6849137
theorem B1805387 : Blo 1202418 1805387 := bstep (se 1 (by rfl) ⟨1354040, by rfl⟩ : syracuseStep 1805387 = 2708081) B2708081
theorem B1805399 : Blo 1202418 1805399 := bstep (se 1 (by rfl) ⟨1354049, by rfl⟩ : syracuseStep 1805399 = 2708099) B2708099
theorem B1928281 : Blo 1202418 1928281 := bstep (se 2 (by rfl) ⟨723105, by rfl⟩ : syracuseStep 1928281 = 1446211) B1446211
theorem B5139587 : Blo 1202418 5139587 := bstep (se 1 (by rfl) ⟨3854690, by rfl⟩ : syracuseStep 5139587 = 7709381) B7709381
theorem B1354891 : Blo 1202418 1354891 := bstep (se 1 (by rfl) ⟨1016168, by rfl⟩ : syracuseStep 1354891 = 2032337) B2032337
theorem B6851735 : Blo 1202418 6851735 := bstep (se 1 (by rfl) ⟨5138801, by rfl⟩ : syracuseStep 6851735 = 10277603) B10277603
theorem B1805465 : Blo 1202418 1805465 := bstep (se 2 (by rfl) ⟨677049, by rfl⟩ : syracuseStep 1805465 = 1354099) B1354099
theorem B4058315 : Blo 1202418 4058315 := bstep (se 1 (by rfl) ⟨3043736, by rfl⟩ : syracuseStep 4058315 = 6087473) B6087473
theorem B1805579 : Blo 1202418 1805579 := bstep (se 1 (by rfl) ⟨1354184, by rfl⟩ : syracuseStep 1805579 = 2708369) B2708369
theorem B1805591 : Blo 1202418 1805591 := bstep (se 1 (by rfl) ⟨1354193, by rfl⟩ : syracuseStep 1805591 = 2708387) B2708387
theorem B2706713 : Blo 1202418 2706713 := bstep (se 2 (by rfl) ⟨1015017, by rfl⟩ : syracuseStep 2706713 = 2030035) B2030035
theorem B1805657 : Blo 1202418 1805657 := bstep (se 2 (by rfl) ⟨677121, by rfl⟩ : syracuseStep 1805657 = 1354243) B1354243
theorem B4566365 : Blo 1202418 4566365 := bstep (se 3 (by rfl) ⟨856193, by rfl⟩ : syracuseStep 4566365 = 1712387) B1712387
theorem B2706803 : Blo 1202418 2706803 := bstep (se 1 (by rfl) ⟨2030102, by rfl⟩ : syracuseStep 2706803 = 4060205) B4060205
theorem B2706839 : Blo 1202418 2706839 := bstep (se 1 (by rfl) ⟨2030129, by rfl⟩ : syracuseStep 2706839 = 4060259) B4060259
theorem B1805771 : Blo 1202418 1805771 := bstep (se 1 (by rfl) ⟨1354328, by rfl⟩ : syracuseStep 1805771 = 2708657) B2708657
theorem B1805783 : Blo 1202418 1805783 := bstep (se 1 (by rfl) ⟨1354337, by rfl⟩ : syracuseStep 1805783 = 2708675) B2708675
theorem B4058585 : Blo 1202418 4058585 := bstep (se 2 (by rfl) ⟨1521969, by rfl⟩ : syracuseStep 4058585 = 3043939) B3043939
theorem B5139929 : Blo 1202418 5139929 := bstep (se 2 (by rfl) ⟨1927473, by rfl⟩ : syracuseStep 5139929 = 3854947) B3854947
theorem B3706391 : Blo 1202418 3706391 := bstep (se 1 (by rfl) ⟨2779793, by rfl⟩ : syracuseStep 3706391 = 5559587) B5559587
theorem B1805849 : Blo 1202418 1805849 := bstep (se 2 (by rfl) ⟨677193, by rfl⟩ : syracuseStep 1805849 = 1354387) B1354387
theorem B1928729 : Blo 1202418 1928729 := bstep (se 2 (by rfl) ⟨723273, by rfl⟩ : syracuseStep 1928729 = 1446547) B1446547
theorem B9760301 : Blo 1202418 9760301 := bstep (se 3 (by rfl) ⟨1830056, by rfl⟩ : syracuseStep 9760301 = 3660113) B3660113
theorem B2707019 : Blo 1202418 2707019 := bstep (se 1 (by rfl) ⟨2030264, by rfl⟩ : syracuseStep 2707019 = 4060529) B4060529
theorem B4402781 : Blo 1202418 4402781 := bstep (se 3 (by rfl) ⟨825521, by rfl⟩ : syracuseStep 4402781 = 1651043) B1651043
theorem B2707073 : Blo 1202418 2707073 := bstep (se 2 (by rfl) ⟨1015152, by rfl⟩ : syracuseStep 2707073 = 2030305) B2030305
theorem B1805963 : Blo 1202418 1805963 := bstep (se 1 (by rfl) ⟨1354472, by rfl⟩ : syracuseStep 1805963 = 2708945) B2708945
theorem B1805975 : Blo 1202418 1805975 := bstep (se 1 (by rfl) ⟨1354481, by rfl⟩ : syracuseStep 1805975 = 2708963) B2708963
theorem B9146033 : Blo 1202418 9146033 := bstep (se 2 (by rfl) ⟨3429762, by rfl⟩ : syracuseStep 9146033 = 6859525) B6859525
theorem B3296971 : Blo 1202418 3296971 := bstep (se 1 (by rfl) ⟨2472728, by rfl⟩ : syracuseStep 3296971 = 4945457) B4945457
theorem B1806041 : Blo 1202418 1806041 := bstep (se 2 (by rfl) ⟨677265, by rfl⟩ : syracuseStep 1806041 = 1354531) B1354531
theorem B1806155 : Blo 1202418 1806155 := bstep (se 1 (by rfl) ⟨1354616, by rfl⟩ : syracuseStep 1806155 = 2709233) B2709233
theorem B1806167 : Blo 1202418 1806167 := bstep (se 1 (by rfl) ⟨1354625, by rfl⟩ : syracuseStep 1806167 = 2709251) B2709251
theorem B2707289 : Blo 1202418 2707289 := bstep (se 2 (by rfl) ⟨1015233, by rfl⟩ : syracuseStep 2707289 = 2030467) B2030467
theorem B41783141 : Blo 1202418 41783141 := bstep (se 4 (by rfl) ⟨3917169, by rfl⟩ : syracuseStep 41783141 = 7834339) B7834339
theorem B1806233 : Blo 1202418 1806233 := bstep (se 2 (by rfl) ⟨677337, by rfl⟩ : syracuseStep 1806233 = 1354675) B1354675
theorem B2707379 : Blo 1202418 2707379 := bstep (se 1 (by rfl) ⟨2030534, by rfl⟩ : syracuseStep 2707379 = 4061069) B4061069
theorem B2707415 : Blo 1202418 2707415 := bstep (se 1 (by rfl) ⟨2030561, by rfl⟩ : syracuseStep 2707415 = 4061123) B4061123
theorem B6090713 : Blo 1202418 6090713 := bstep (se 2 (by rfl) ⟨2284017, by rfl⟩ : syracuseStep 6090713 = 4568035) B4568035
theorem B1806347 : Blo 1202418 1806347 := bstep (se 1 (by rfl) ⟨1354760, by rfl⟩ : syracuseStep 1806347 = 2709521) B2709521
theorem B4567063 : Blo 1202418 4567063 := bstep (se 1 (by rfl) ⟨3425297, by rfl⟩ : syracuseStep 4567063 = 6850595) B6850595
theorem B1806359 : Blo 1202418 1806359 := bstep (se 1 (by rfl) ⟨1354769, by rfl⟩ : syracuseStep 1806359 = 2709539) B2709539
theorem B3657803 : Blo 1202418 3657803 := bstep (se 1 (by rfl) ⟨2743352, by rfl⟩ : syracuseStep 3657803 = 5486705) B5486705
theorem B1806425 : Blo 1202418 1806425 := bstep (se 2 (by rfl) ⟨677409, by rfl⟩ : syracuseStep 1806425 = 1354819) B1354819
theorem B7319645 : Blo 1202418 7319645 := bstep (se 3 (by rfl) ⟨1372433, by rfl⟩ : syracuseStep 7319645 = 2744867) B2744867
theorem B2707595 : Blo 1202418 2707595 := bstep (se 1 (by rfl) ⟨2030696, by rfl⟩ : syracuseStep 2707595 = 4061393) B4061393
theorem B4059287 : Blo 1202418 4059287 := bstep (se 1 (by rfl) ⟨3044465, by rfl⟩ : syracuseStep 4059287 = 6088931) B6088931
theorem B2707649 : Blo 1202418 2707649 := bstep (se 2 (by rfl) ⟨1015368, by rfl⟩ : syracuseStep 2707649 = 2030737) B2030737
theorem B1806539 : Blo 1202418 1806539 := bstep (se 1 (by rfl) ⟨1354904, by rfl⟩ : syracuseStep 1806539 = 2709809) B2709809
theorem B1806551 : Blo 1202418 1806551 := bstep (se 1 (by rfl) ⟨1354913, by rfl⟩ : syracuseStep 1806551 = 2709827) B2709827
theorem B13709573 : Blo 1202418 13709573 := bstep (se 4 (by rfl) ⟨1285272, by rfl⟩ : syracuseStep 13709573 = 2570545) B2570545
theorem B1806617 : Blo 1202418 1806617 := bstep (se 2 (by rfl) ⟨677481, by rfl⟩ : syracuseStep 1806617 = 1354963) B1354963
theorem B1544599 : Blo 1202418 1544599 := bstep (se 1 (by rfl) ⟨1158449, by rfl⟩ : syracuseStep 1544599 = 2316899) B2316899
theorem B2707865 : Blo 1202418 2707865 := bstep (se 2 (by rfl) ⟨1015449, by rfl⟩ : syracuseStep 2707865 = 2030899) B2030899
theorem B3043777 : Blo 1202418 3043777 := bstep (se 2 (by rfl) ⟨1141416, by rfl⟩ : syracuseStep 3043777 = 2282833) B2282833
theorem B2707955 : Blo 1202418 2707955 := bstep (se 1 (by rfl) ⟨2030966, by rfl⟩ : syracuseStep 2707955 = 4061933) B4061933
theorem B2707991 : Blo 1202418 2707991 := bstep (se 1 (by rfl) ⟨2030993, by rfl⟩ : syracuseStep 2707991 = 4061987) B4061987
theorem B4059827 : Blo 1202418 4059827 := bstep (se 1 (by rfl) ⟨3044870, by rfl⟩ : syracuseStep 4059827 = 6089741) B6089741
theorem B2708171 : Blo 1202418 2708171 := bstep (se 1 (by rfl) ⟨2031128, by rfl⟩ : syracuseStep 2708171 = 4062257) B4062257
theorem B1204215 : Blo 1202418 1204215 := bstep (se 1 (by rfl) ⟨903161, by rfl⟩ : syracuseStep 1204215 = 1806323) B1806323
theorem B2708225 : Blo 1202418 2708225 := bstep (se 2 (by rfl) ⟨1015584, by rfl⟩ : syracuseStep 2708225 = 2031169) B2031169
theorem B7729937 : Blo 1202418 7729937 := bstep (se 2 (by rfl) ⟨2898726, by rfl⟩ : syracuseStep 7729937 = 5797453) B5797453
theorem B3855127 : Blo 1202418 3855127 := bstep (se 1 (by rfl) ⟨2891345, by rfl⟩ : syracuseStep 3855127 = 5782691) B5782691
theorem B4567853 : Blo 1202418 4567853 := bstep (se 3 (by rfl) ⟨856472, by rfl⟩ : syracuseStep 4567853 = 1712945) B1712945
theorem B4060097 : Blo 1202418 4060097 := bstep (se 2 (by rfl) ⟨1522536, by rfl⟩ : syracuseStep 4060097 = 3045073) B3045073
theorem B2708441 : Blo 1202418 2708441 := bstep (se 2 (by rfl) ⟨1015665, by rfl⟩ : syracuseStep 2708441 = 2031331) B2031331
theorem B8680409 : Blo 1202418 8680409 := bstep (se 2 (by rfl) ⟨3255153, by rfl⟩ : syracuseStep 8680409 = 6510307) B6510307
theorem B10417169 : Blo 1202418 10417169 := bstep (se 2 (by rfl) ⟨3906438, by rfl⟩ : syracuseStep 10417169 = 7812877) B7812877
theorem B3044375 : Blo 1202418 3044375 := bstep (se 1 (by rfl) ⟨2283281, by rfl⟩ : syracuseStep 3044375 = 4566563) B4566563
theorem B2708531 : Blo 1202418 2708531 := bstep (se 1 (by rfl) ⟨2031398, by rfl⟩ : syracuseStep 2708531 = 4062797) B4062797
theorem B5141569 : Blo 1202418 5141569 := bstep (se 2 (by rfl) ⟨1928088, by rfl⟩ : syracuseStep 5141569 = 3856177) B3856177
theorem B18781253 : Blo 1202418 18781253 := bstep (se 4 (by rfl) ⟨1760742, by rfl⟩ : syracuseStep 18781253 = 3521485) B3521485
theorem B2708567 : Blo 1202418 2708567 := bstep (se 1 (by rfl) ⟨2031425, by rfl⟩ : syracuseStep 2708567 = 4062851) B4062851
theorem B3658841 : Blo 1202418 3658841 := bstep (se 2 (by rfl) ⟨1372065, by rfl⟩ : syracuseStep 3658841 = 2744131) B2744131
theorem B8344727 : Blo 1202418 8344727 := bstep (se 1 (by rfl) ⟨6258545, by rfl⟩ : syracuseStep 8344727 = 12517091) B12517091
theorem B4175027 : Blo 1202418 4175027 := bstep (se 1 (by rfl) ⟨3131270, by rfl⟩ : syracuseStep 4175027 = 6262541) B6262541
theorem B3855563 : Blo 1202418 3855563 := bstep (se 1 (by rfl) ⟨2891672, by rfl⟩ : syracuseStep 3855563 = 5783345) B5783345
theorem B2708747 : Blo 1202418 2708747 := bstep (se 1 (by rfl) ⟨2031560, by rfl⟩ : syracuseStep 2708747 = 4063121) B4063121
theorem B2708801 : Blo 1202418 2708801 := bstep (se 2 (by rfl) ⟨1015800, by rfl⟩ : syracuseStep 2708801 = 2031601) B2031601
theorem B18519475 : Blo 1202418 18519475 := bstep (se 1 (by rfl) ⟨13889606, by rfl⟩ : syracuseStep 18519475 = 27779213) B27779213
theorem B2168257 : Blo 1202418 2168257 := bstep (se 2 (by rfl) ⟨813096, by rfl⟩ : syracuseStep 2168257 = 1626193) B1626193
theorem B4060637 : Blo 1202418 4060637 := bstep (se 3 (by rfl) ⟨761369, by rfl⟩ : syracuseStep 4060637 = 1522739) B1522739
theorem B2709017 : Blo 1202418 2709017 := bstep (se 2 (by rfl) ⟨1015881, by rfl⟩ : syracuseStep 2709017 = 2031763) B2031763
theorem B6092333 : Blo 1202418 6092333 := bstep (se 3 (by rfl) ⟨1142312, by rfl⟩ : syracuseStep 6092333 = 2284625) B2284625
theorem B2438707 : Blo 1202418 2438707 := bstep (se 1 (by rfl) ⟨1829030, by rfl⟩ : syracuseStep 2438707 = 3658061) B3658061
theorem B2315827 : Blo 1202418 2315827 := bstep (se 1 (by rfl) ⟨1736870, by rfl⟩ : syracuseStep 2315827 = 3473741) B3473741
theorem B6854219 : Blo 1202418 6854219 := bstep (se 1 (by rfl) ⟨5140664, by rfl⟩ : syracuseStep 6854219 = 10281329) B10281329
theorem B11130443 : Blo 1202418 11130443 := bstep (se 1 (by rfl) ⟨8347832, by rfl⟩ : syracuseStep 11130443 = 16695665) B16695665
theorem B2709107 : Blo 1202418 2709107 := bstep (se 1 (by rfl) ⟨2031830, by rfl⟩ : syracuseStep 2709107 = 4063661) B4063661
theorem B2283137 : Blo 1202418 2283137 := bstep (se 2 (by rfl) ⟨856176, by rfl⟩ : syracuseStep 2283137 = 1712353) B1712353
theorem B2709143 : Blo 1202418 2709143 := bstep (se 1 (by rfl) ⟨2031857, by rfl⟩ : syracuseStep 2709143 = 4063715) B4063715
theorem B2029259 : Blo 1202418 2029259 := bstep (se 1 (by rfl) ⟨1521944, by rfl⟩ : syracuseStep 2029259 = 3043889) B3043889
theorem B3045185 : Blo 1202418 3045185 := bstep (se 2 (by rfl) ⟨1141944, by rfl⟩ : syracuseStep 3045185 = 2283889) B2283889
theorem B2029387 : Blo 1202418 2029387 := bstep (se 1 (by rfl) ⟨1522040, by rfl⟩ : syracuseStep 2029387 = 3044081) B3044081
theorem B2570059 : Blo 1202418 2570059 := bstep (se 1 (by rfl) ⟨1927544, by rfl⟩ : syracuseStep 2570059 = 3855089) B3855089
theorem B2709323 : Blo 1202418 2709323 := bstep (se 1 (by rfl) ⟨2031992, by rfl⟩ : syracuseStep 2709323 = 4063985) B4063985
theorem B2709377 : Blo 1202418 2709377 := bstep (se 2 (by rfl) ⟨1016016, by rfl⟩ : syracuseStep 2709377 = 2032033) B2032033
theorem B2283403 : Blo 1202418 2283403 := bstep (se 1 (by rfl) ⟨1712552, by rfl⟩ : syracuseStep 2283403 = 3425105) B3425105
theorem B2570135 : Blo 1202418 2570135 := bstep (se 1 (by rfl) ⟨1927601, by rfl⟩ : syracuseStep 2570135 = 3855203) B3855203
theorem B3856331 : Blo 1202418 3856331 := bstep (se 1 (by rfl) ⟨2892248, by rfl⟩ : syracuseStep 3856331 = 5784497) B5784497
theorem B2029529 : Blo 1202418 2029529 := bstep (se 2 (by rfl) ⟨761073, by rfl⟩ : syracuseStep 2029529 = 1522147) B1522147
theorem B20846605 : Blo 1202418 20846605 := bstep (se 3 (by rfl) ⟨3908738, by rfl⟩ : syracuseStep 20846605 = 7817477) B7817477
theorem B4339757 : Blo 1202418 4339757 := bstep (se 3 (by rfl) ⟨813704, by rfl⟩ : syracuseStep 4339757 = 1627409) B1627409
theorem B2029657 : Blo 1202418 2029657 := bstep (se 2 (by rfl) ⟨761121, by rfl⟩ : syracuseStep 2029657 = 1522243) B1522243
theorem B2709593 : Blo 1202418 2709593 := bstep (se 2 (by rfl) ⟨1016097, by rfl⟩ : syracuseStep 2709593 = 2032195) B2032195
theorem B2709683 : Blo 1202418 2709683 := bstep (se 1 (by rfl) ⟨2032262, by rfl⟩ : syracuseStep 2709683 = 4064525) B4064525
theorem B5208257 : Blo 1202418 5208257 := bstep (se 2 (by rfl) ⟨1953096, by rfl⟩ : syracuseStep 5208257 = 3906193) B3906193
theorem B4569281 : Blo 1202418 4569281 := bstep (se 2 (by rfl) ⟨1713480, by rfl⟩ : syracuseStep 4569281 = 3426961) B3426961
theorem B2709719 : Blo 1202418 2709719 := bstep (se 1 (by rfl) ⟨2032289, by rfl⟩ : syracuseStep 2709719 = 4064579) B4064579
theorem B1202423 : Blo 1202418 1202423 := bstep (se 1 (by rfl) ⟨901817, by rfl⟩ : syracuseStep 1202423 = 1803635) B1803635
theorem B1202443 : Blo 1202418 1202443 := bstep (se 1 (by rfl) ⟨901832, by rfl⟩ : syracuseStep 1202443 = 1803665) B1803665
theorem B7706897 : Blo 1202418 7706897 := bstep (se 2 (by rfl) ⟨2890086, by rfl⟩ : syracuseStep 7706897 = 5780173) B5780173
theorem B1202455 : Blo 1202418 1202455 := bstep (se 1 (by rfl) ⟨901841, by rfl⟩ : syracuseStep 1202455 = 1803683) B1803683
theorem B1202475 : Blo 1202418 1202475 := bstep (se 1 (by rfl) ⟨901856, by rfl⟩ : syracuseStep 1202475 = 1803713) B1803713
theorem B1202487 : Blo 1202418 1202487 := bstep (se 1 (by rfl) ⟨901865, by rfl⟩ : syracuseStep 1202487 = 1803731) B1803731
theorem B1202507 : Blo 1202418 1202507 := bstep (se 1 (by rfl) ⟨901880, by rfl⟩ : syracuseStep 1202507 = 1803761) B1803761
theorem B1284427 : Blo 1202418 1284427 := bstep (se 1 (by rfl) ⟨963320, by rfl⟩ : syracuseStep 1284427 = 1926641) B1926641
theorem B2283851 : Blo 1202418 2283851 := bstep (se 1 (by rfl) ⟨1712888, by rfl⟩ : syracuseStep 2283851 = 3425777) B3425777
theorem B1202519 : Blo 1202418 1202519 := bstep (se 1 (by rfl) ⟨901889, by rfl⟩ : syracuseStep 1202519 = 1803779) B1803779
theorem B3045721 : Blo 1202418 3045721 := bstep (se 2 (by rfl) ⟨1142145, by rfl⟩ : syracuseStep 3045721 = 2284291) B2284291
theorem B3856729 : Blo 1202418 3856729 := bstep (se 2 (by rfl) ⟨1446273, by rfl⟩ : syracuseStep 3856729 = 2892547) B2892547
theorem B1202539 : Blo 1202418 1202539 := bstep (se 1 (by rfl) ⟨901904, by rfl⟩ : syracuseStep 1202539 = 1803809) B1803809
theorem B1202551 : Blo 1202418 1202551 := bstep (se 1 (by rfl) ⟨901913, by rfl⟩ : syracuseStep 1202551 = 1803827) B1803827
theorem B1202571 : Blo 1202418 1202571 := bstep (se 1 (by rfl) ⟨901928, by rfl⟩ : syracuseStep 1202571 = 1803857) B1803857
theorem B2709899 : Blo 1202418 2709899 := bstep (se 1 (by rfl) ⟨2032424, by rfl⟩ : syracuseStep 2709899 = 4064849) B4064849
theorem B1202583 : Blo 1202418 1202583 := bstep (se 1 (by rfl) ⟨901937, by rfl⟩ : syracuseStep 1202583 = 1803875) B1803875
theorem B1202603 : Blo 1202418 1202603 := bstep (se 1 (by rfl) ⟨901952, by rfl⟩ : syracuseStep 1202603 = 1803905) B1803905
theorem B1202615 : Blo 1202418 1202615 := bstep (se 1 (by rfl) ⟨901961, by rfl⟩ : syracuseStep 1202615 = 1803923) B1803923
theorem B1202635 : Blo 1202418 1202635 := bstep (se 1 (by rfl) ⟨901976, by rfl⟩ : syracuseStep 1202635 = 1803953) B1803953
theorem B3856843 : Blo 1202418 3856843 := bstep (se 1 (by rfl) ⟨2892632, by rfl⟩ : syracuseStep 3856843 = 5785265) B5785265
theorem B1202647 : Blo 1202418 1202647 := bstep (se 1 (by rfl) ⟨901985, by rfl⟩ : syracuseStep 1202647 = 1803971) B1803971
theorem B1202667 : Blo 1202418 1202667 := bstep (se 1 (by rfl) ⟨902000, by rfl⟩ : syracuseStep 1202667 = 1804001) B1804001
theorem B1202679 : Blo 1202418 1202679 := bstep (se 1 (by rfl) ⟨902009, by rfl⟩ : syracuseStep 1202679 = 1804019) B1804019
theorem B2284033 : Blo 1202418 2284033 := bstep (se 2 (by rfl) ⟨856512, by rfl⟩ : syracuseStep 2284033 = 1713025) B1713025
theorem B1202699 : Blo 1202418 1202699 := bstep (se 1 (by rfl) ⟨902024, by rfl⟩ : syracuseStep 1202699 = 1804049) B1804049
theorem B1202711 : Blo 1202418 1202711 := bstep (se 1 (by rfl) ⟨902033, by rfl⟩ : syracuseStep 1202711 = 1804067) B1804067
theorem B1202731 : Blo 1202418 1202731 := bstep (se 1 (by rfl) ⟨902048, by rfl⟩ : syracuseStep 1202731 = 1804097) B1804097
theorem B1202743 : Blo 1202418 1202743 := bstep (se 1 (by rfl) ⟨902057, by rfl⟩ : syracuseStep 1202743 = 1804115) B1804115
theorem B1202763 : Blo 1202418 1202763 := bstep (se 1 (by rfl) ⟨902072, by rfl⟩ : syracuseStep 1202763 = 1804145) B1804145
theorem B4061771 : Blo 1202418 4061771 := bstep (se 1 (by rfl) ⟨3046328, by rfl⟩ : syracuseStep 4061771 = 6092657) B6092657
theorem B1202775 : Blo 1202418 1202775 := bstep (se 1 (by rfl) ⟨902081, by rfl⟩ : syracuseStep 1202775 = 1804163) B1804163
theorem B1202795 : Blo 1202418 1202795 := bstep (se 1 (by rfl) ⟨902096, by rfl⟩ : syracuseStep 1202795 = 1804193) B1804193
theorem B1202807 : Blo 1202418 1202807 := bstep (se 1 (by rfl) ⟨902105, by rfl⟩ : syracuseStep 1202807 = 1804211) B1804211
theorem B1202827 : Blo 1202418 1202827 := bstep (se 1 (by rfl) ⟨902120, by rfl⟩ : syracuseStep 1202827 = 1804241) B1804241
theorem B1202839 : Blo 1202418 1202839 := bstep (se 1 (by rfl) ⟨902129, by rfl⟩ : syracuseStep 1202839 = 1804259) B1804259
theorem B2030231 : Blo 1202418 2030231 := bstep (se 1 (by rfl) ⟨1522673, by rfl⟩ : syracuseStep 2030231 = 3045347) B3045347
theorem B1202859 : Blo 1202418 1202859 := bstep (se 1 (by rfl) ⟨902144, by rfl⟩ : syracuseStep 1202859 = 1804289) B1804289
theorem B1202871 : Blo 1202418 1202871 := bstep (se 1 (by rfl) ⟨902153, by rfl⟩ : syracuseStep 1202871 = 1804307) B1804307
theorem B1202891 : Blo 1202418 1202891 := bstep (se 1 (by rfl) ⟨902168, by rfl⟩ : syracuseStep 1202891 = 1804337) B1804337
theorem B1202903 : Blo 1202418 1202903 := bstep (se 1 (by rfl) ⟨902177, by rfl⟩ : syracuseStep 1202903 = 1804355) B1804355
theorem B1202923 : Blo 1202418 1202923 := bstep (se 1 (by rfl) ⟨902192, by rfl⟩ : syracuseStep 1202923 = 1804385) B1804385
theorem B1202935 : Blo 1202418 1202935 := bstep (se 1 (by rfl) ⟨902201, by rfl⟩ : syracuseStep 1202935 = 1804403) B1804403
theorem B1202955 : Blo 1202418 1202955 := bstep (se 1 (by rfl) ⟨902216, by rfl⟩ : syracuseStep 1202955 = 1804433) B1804433
theorem B1202967 : Blo 1202418 1202967 := bstep (se 1 (by rfl) ⟨902225, by rfl⟩ : syracuseStep 1202967 = 1804451) B1804451
theorem B2030359 : Blo 1202418 2030359 := bstep (se 1 (by rfl) ⟨1522769, by rfl⟩ : syracuseStep 2030359 = 3045539) B3045539
theorem B1202987 : Blo 1202418 1202987 := bstep (se 1 (by rfl) ⟨902240, by rfl⟩ : syracuseStep 1202987 = 1804481) B1804481
theorem B1202999 : Blo 1202418 1202999 := bstep (se 1 (by rfl) ⟨902249, by rfl⟩ : syracuseStep 1202999 = 1804499) B1804499
theorem B6503233 : Blo 1202418 6503233 := bstep (se 2 (by rfl) ⟨2438712, by rfl⟩ : syracuseStep 6503233 = 4877425) B4877425
theorem B1203019 : Blo 1202418 1203019 := bstep (se 1 (by rfl) ⟨902264, by rfl⟩ : syracuseStep 1203019 = 1804529) B1804529
theorem B1203031 : Blo 1202418 1203031 := bstep (se 1 (by rfl) ⟨902273, by rfl⟩ : syracuseStep 1203031 = 1804547) B1804547
theorem B2284375 : Blo 1202418 2284375 := bstep (se 1 (by rfl) ⟨1713281, by rfl⟩ : syracuseStep 2284375 = 3426563) B3426563
theorem B4062041 : Blo 1202418 4062041 := bstep (se 2 (by rfl) ⟨1523265, by rfl⟩ : syracuseStep 4062041 = 3046531) B3046531
theorem B1203051 : Blo 1202418 1203051 := bstep (se 1 (by rfl) ⟨902288, by rfl⟩ : syracuseStep 1203051 = 1804577) B1804577
theorem B1203063 : Blo 1202418 1203063 := bstep (se 1 (by rfl) ⟨902297, by rfl⟩ : syracuseStep 1203063 = 1804595) B1804595
theorem B6175619 : Blo 1202418 6175619 := bstep (se 1 (by rfl) ⟨4631714, by rfl⟩ : syracuseStep 6175619 = 9263429) B9263429
theorem B1203083 : Blo 1202418 1203083 := bstep (se 1 (by rfl) ⟨902312, by rfl⟩ : syracuseStep 1203083 = 1804625) B1804625
theorem B1203095 : Blo 1202418 1203095 := bstep (se 1 (by rfl) ⟨902321, by rfl⟩ : syracuseStep 1203095 = 1804643) B1804643
theorem B1203115 : Blo 1202418 1203115 := bstep (se 1 (by rfl) ⟨902336, by rfl⟩ : syracuseStep 1203115 = 1804673) B1804673
theorem B1203127 : Blo 1202418 1203127 := bstep (se 1 (by rfl) ⟨902345, by rfl⟩ : syracuseStep 1203127 = 1804691) B1804691
theorem B3857345 : Blo 1202418 3857345 := bstep (se 2 (by rfl) ⟨1446504, by rfl⟩ : syracuseStep 3857345 = 2893009) B2893009
theorem B1203147 : Blo 1202418 1203147 := bstep (se 1 (by rfl) ⟨902360, by rfl⟩ : syracuseStep 1203147 = 1804721) B1804721
theorem B2784203 : Blo 1202418 2784203 := bstep (se 1 (by rfl) ⟨2088152, by rfl⟩ : syracuseStep 2784203 = 4176305) B4176305
theorem B1203159 : Blo 1202418 1203159 := bstep (se 1 (by rfl) ⟨902369, by rfl⟩ : syracuseStep 1203159 = 1804739) B1804739
theorem B1203179 : Blo 1202418 1203179 := bstep (se 1 (by rfl) ⟨902384, by rfl⟩ : syracuseStep 1203179 = 1804769) B1804769
theorem B1203191 : Blo 1202418 1203191 := bstep (se 1 (by rfl) ⟨902393, by rfl⟩ : syracuseStep 1203191 = 1804787) B1804787
theorem B1203211 : Blo 1202418 1203211 := bstep (se 1 (by rfl) ⟨902408, by rfl⟩ : syracuseStep 1203211 = 1804817) B1804817
theorem B1203223 : Blo 1202418 1203223 := bstep (se 1 (by rfl) ⟨902417, by rfl⟩ : syracuseStep 1203223 = 1804835) B1804835
theorem B1203243 : Blo 1202418 1203243 := bstep (se 1 (by rfl) ⟨902432, by rfl⟩ : syracuseStep 1203243 = 1804865) B1804865
theorem B2284595 : Blo 1202418 2284595 := bstep (se 1 (by rfl) ⟨1713446, by rfl⟩ : syracuseStep 2284595 = 3426893) B3426893
theorem B1203255 : Blo 1202418 1203255 := bstep (se 1 (by rfl) ⟨902441, by rfl⟩ : syracuseStep 1203255 = 1804883) B1804883
theorem B1203275 : Blo 1202418 1203275 := bstep (se 1 (by rfl) ⟨902456, by rfl⟩ : syracuseStep 1203275 = 1804913) B1804913
theorem B1203287 : Blo 1202418 1203287 := bstep (se 1 (by rfl) ⟨902465, by rfl⟩ : syracuseStep 1203287 = 1804931) B1804931
theorem B1203307 : Blo 1202418 1203307 := bstep (se 1 (by rfl) ⟨902480, by rfl⟩ : syracuseStep 1203307 = 1804961) B1804961
theorem B1203319 : Blo 1202418 1203319 := bstep (se 1 (by rfl) ⟨902489, by rfl⟩ : syracuseStep 1203319 = 1804979) B1804979
theorem B1203339 : Blo 1202418 1203339 := bstep (se 1 (by rfl) ⟨902504, by rfl⟩ : syracuseStep 1203339 = 1805009) B1805009
theorem B2890903 : Blo 1202418 2890903 := bstep (se 1 (by rfl) ⟨2168177, by rfl⟩ : syracuseStep 2890903 = 4336355) B4336355
theorem B1203351 : Blo 1202418 1203351 := bstep (se 1 (by rfl) ⟨902513, by rfl⟩ : syracuseStep 1203351 = 1805027) B1805027
theorem B1203371 : Blo 1202418 1203371 := bstep (se 1 (by rfl) ⟨902528, by rfl⟩ : syracuseStep 1203371 = 1805057) B1805057
theorem B1203383 : Blo 1202418 1203383 := bstep (se 1 (by rfl) ⟨902537, by rfl⟩ : syracuseStep 1203383 = 1805075) B1805075
theorem B1285303 : Blo 1202418 1285303 := bstep (se 1 (by rfl) ⟨963977, by rfl⟩ : syracuseStep 1285303 = 1927955) B1927955
theorem B1522891 : Blo 1202418 1522891 := bstep (se 1 (by rfl) ⟨1142168, by rfl⟩ : syracuseStep 1522891 = 2284337) B2284337
theorem B1203403 : Blo 1202418 1203403 := bstep (se 1 (by rfl) ⟨902552, by rfl⟩ : syracuseStep 1203403 = 1805105) B1805105
theorem B1203415 : Blo 1202418 1203415 := bstep (se 1 (by rfl) ⟨902561, by rfl⟩ : syracuseStep 1203415 = 1805123) B1805123
theorem B1203435 : Blo 1202418 1203435 := bstep (se 1 (by rfl) ⟨902576, by rfl⟩ : syracuseStep 1203435 = 1805153) B1805153
theorem B1203447 : Blo 1202418 1203447 := bstep (se 1 (by rfl) ⟨902585, by rfl⟩ : syracuseStep 1203447 = 1805171) B1805171
theorem B1203467 : Blo 1202418 1203467 := bstep (se 1 (by rfl) ⟨902600, by rfl⟩ : syracuseStep 1203467 = 1805201) B1805201
theorem B1203479 : Blo 1202418 1203479 := bstep (se 1 (by rfl) ⟨902609, by rfl⟩ : syracuseStep 1203479 = 1805219) B1805219
theorem B2284823 : Blo 1202418 2284823 := bstep (se 1 (by rfl) ⟨1713617, by rfl⟩ : syracuseStep 2284823 = 3427235) B3427235
theorem B1203499 : Blo 1202418 1203499 := bstep (se 1 (by rfl) ⟨902624, by rfl⟩ : syracuseStep 1203499 = 1805249) B1805249
theorem B4947245 : Blo 1202418 4947245 := bstep (se 3 (by rfl) ⟨927608, by rfl⟩ : syracuseStep 4947245 = 1855217) B1855217
theorem B1203511 : Blo 1202418 1203511 := bstep (se 1 (by rfl) ⟨902633, by rfl⟩ : syracuseStep 1203511 = 1805267) B1805267
theorem B11132225 : Blo 1202418 11132225 := bstep (se 2 (by rfl) ⟨4174584, by rfl⟩ : syracuseStep 11132225 = 8349169) B8349169
theorem B10280267 : Blo 1202418 10280267 := bstep (se 1 (by rfl) ⟨7710200, by rfl⟩ : syracuseStep 10280267 = 15420401) B15420401
theorem B1203531 : Blo 1202418 1203531 := bstep (se 1 (by rfl) ⟨902648, by rfl⟩ : syracuseStep 1203531 = 1805297) B1805297
theorem B1203543 : Blo 1202418 1203543 := bstep (se 1 (by rfl) ⟨902657, by rfl⟩ : syracuseStep 1203543 = 1805315) B1805315
theorem B1506647 : Blo 1202418 1506647 := bstep (se 1 (by rfl) ⟨1129985, by rfl⟩ : syracuseStep 1506647 = 2259971) B2259971
theorem B1203563 : Blo 1202418 1203563 := bstep (se 1 (by rfl) ⟨902672, by rfl⟩ : syracuseStep 1203563 = 1805345) B1805345
theorem B1203575 : Blo 1202418 1203575 := bstep (se 1 (by rfl) ⟨902681, by rfl⟩ : syracuseStep 1203575 = 1805363) B1805363
theorem B2030987 : Blo 1202418 2030987 := bstep (se 1 (by rfl) ⟨1523240, by rfl⟩ : syracuseStep 2030987 = 3046481) B3046481
theorem B1203595 : Blo 1202418 1203595 := bstep (se 1 (by rfl) ⟨902696, by rfl⟩ : syracuseStep 1203595 = 1805393) B1805393
theorem B1203607 : Blo 1202418 1203607 := bstep (se 1 (by rfl) ⟨902705, by rfl⟩ : syracuseStep 1203607 = 1805411) B1805411
theorem B1203627 : Blo 1202418 1203627 := bstep (se 1 (by rfl) ⟨902720, by rfl⟩ : syracuseStep 1203627 = 1805441) B1805441
theorem B3046835 : Blo 1202418 3046835 := bstep (se 1 (by rfl) ⟨2285126, by rfl⟩ : syracuseStep 3046835 = 4570253) B4570253
theorem B1203639 : Blo 1202418 1203639 := bstep (se 1 (by rfl) ⟨902729, by rfl⟩ : syracuseStep 1203639 = 1805459) B1805459
theorem B1203659 : Blo 1202418 1203659 := bstep (se 1 (by rfl) ⟨902744, by rfl⟩ : syracuseStep 1203659 = 1805489) B1805489
theorem B1203671 : Blo 1202418 1203671 := bstep (se 1 (by rfl) ⟨902753, by rfl⟩ : syracuseStep 1203671 = 1805507) B1805507
theorem B1203691 : Blo 1202418 1203691 := bstep (se 1 (by rfl) ⟨902768, by rfl⟩ : syracuseStep 1203691 = 1805537) B1805537
theorem B1203703 : Blo 1202418 1203703 := bstep (se 1 (by rfl) ⟨902777, by rfl⟩ : syracuseStep 1203703 = 1805555) B1805555
theorem B2031115 : Blo 1202418 2031115 := bstep (se 1 (by rfl) ⟨1523336, by rfl⟩ : syracuseStep 2031115 = 3046673) B3046673
theorem B1203723 : Blo 1202418 1203723 := bstep (se 1 (by rfl) ⟨902792, by rfl⟩ : syracuseStep 1203723 = 1805585) B1805585
theorem B1203735 : Blo 1202418 1203735 := bstep (se 1 (by rfl) ⟨902801, by rfl⟩ : syracuseStep 1203735 = 1805603) B1805603
theorem B4062743 : Blo 1202418 4062743 := bstep (se 1 (by rfl) ⟨3047057, by rfl⟩ : syracuseStep 4062743 = 6094115) B6094115
theorem B2285081 : Blo 1202418 2285081 := bstep (se 2 (by rfl) ⟨856905, by rfl⟩ : syracuseStep 2285081 = 1713811) B1713811
theorem B1203755 : Blo 1202418 1203755 := bstep (se 1 (by rfl) ⟨902816, by rfl⟩ : syracuseStep 1203755 = 1805633) B1805633
theorem B3857971 : Blo 1202418 3857971 := bstep (se 1 (by rfl) ⟨2893478, by rfl⟩ : syracuseStep 3857971 = 5786957) B5786957
theorem B1203767 : Blo 1202418 1203767 := bstep (se 1 (by rfl) ⟨902825, by rfl⟩ : syracuseStep 1203767 = 1805651) B1805651
theorem B1203787 : Blo 1202418 1203787 := bstep (se 1 (by rfl) ⟨902840, by rfl⟩ : syracuseStep 1203787 = 1805681) B1805681
theorem B1203799 : Blo 1202418 1203799 := bstep (se 1 (by rfl) ⟨902849, by rfl⟩ : syracuseStep 1203799 = 1805699) B1805699
theorem B10288741 : Blo 1202418 10288741 := bstep (se 4 (by rfl) ⟨964569, by rfl⟩ : syracuseStep 10288741 = 1929139) B1929139
theorem B1203819 : Blo 1202418 1203819 := bstep (se 1 (by rfl) ⟨902864, by rfl⟩ : syracuseStep 1203819 = 1805729) B1805729
theorem B1203831 : Blo 1202418 1203831 := bstep (se 1 (by rfl) ⟨902873, by rfl⟩ : syracuseStep 1203831 = 1805747) B1805747
theorem B1285751 : Blo 1202418 1285751 := bstep (se 1 (by rfl) ⟨964313, by rfl⟩ : syracuseStep 1285751 = 1928627) B1928627
theorem B2571905 : Blo 1202418 2571905 := bstep (se 2 (by rfl) ⟨964464, by rfl⟩ : syracuseStep 2571905 = 1928929) B1928929
theorem B1203851 : Blo 1202418 1203851 := bstep (se 1 (by rfl) ⟨902888, by rfl⟩ : syracuseStep 1203851 = 1805777) B1805777
theorem B4570769 : Blo 1202418 4570769 := bstep (se 2 (by rfl) ⟨1714038, by rfl⟩ : syracuseStep 4570769 = 3428077) B3428077
theorem B1203863 : Blo 1202418 1203863 := bstep (se 1 (by rfl) ⟨902897, by rfl⟩ : syracuseStep 1203863 = 1805795) B1805795
theorem B2031257 : Blo 1202418 2031257 := bstep (se 2 (by rfl) ⟨761721, by rfl⟩ : syracuseStep 2031257 = 1523443) B1523443
theorem B1203883 : Blo 1202418 1203883 := bstep (se 1 (by rfl) ⟨902912, by rfl⟩ : syracuseStep 1203883 = 1805825) B1805825
theorem B1203895 : Blo 1202418 1203895 := bstep (se 1 (by rfl) ⟨902921, by rfl⟩ : syracuseStep 1203895 = 1805843) B1805843
theorem B1203915 : Blo 1202418 1203915 := bstep (se 1 (by rfl) ⟨902936, by rfl⟩ : syracuseStep 1203915 = 1805873) B1805873
theorem B23150285 : Blo 1202418 23150285 := bstep (se 3 (by rfl) ⟨4340678, by rfl⟩ : syracuseStep 23150285 = 8681357) B8681357
theorem B1203927 : Blo 1202418 1203927 := bstep (se 1 (by rfl) ⟨902945, by rfl⟩ : syracuseStep 1203927 = 1805891) B1805891
theorem B3047129 : Blo 1202418 3047129 := bstep (se 2 (by rfl) ⟨1142673, by rfl⟩ : syracuseStep 3047129 = 2285347) B2285347
theorem B1203947 : Blo 1202418 1203947 := bstep (se 1 (by rfl) ⟨902960, by rfl⟩ : syracuseStep 1203947 = 1805921) B1805921
theorem B1203959 : Blo 1202418 1203959 := bstep (se 1 (by rfl) ⟨902969, by rfl⟩ : syracuseStep 1203959 = 1805939) B1805939
theorem B1203979 : Blo 1202418 1203979 := bstep (se 1 (by rfl) ⟨902984, by rfl⟩ : syracuseStep 1203979 = 1805969) B1805969
theorem B1203991 : Blo 1202418 1203991 := bstep (se 1 (by rfl) ⟨902993, by rfl⟩ : syracuseStep 1203991 = 1805987) B1805987
theorem B2031385 : Blo 1202418 2031385 := bstep (se 2 (by rfl) ⟨761769, by rfl⟩ : syracuseStep 2031385 = 1523539) B1523539
theorem B1204011 : Blo 1202418 1204011 := bstep (se 1 (by rfl) ⟨903008, by rfl⟩ : syracuseStep 1204011 = 1806017) B1806017
theorem B1204023 : Blo 1202418 1204023 := bstep (se 1 (by rfl) ⟨903017, by rfl⟩ : syracuseStep 1204023 = 1806035) B1806035
theorem B7315265 : Blo 1202418 7315265 := bstep (se 2 (by rfl) ⟨2743224, by rfl⟩ : syracuseStep 7315265 = 5486449) B5486449
theorem B1204043 : Blo 1202418 1204043 := bstep (se 1 (by rfl) ⟨903032, by rfl⟩ : syracuseStep 1204043 = 1806065) B1806065
theorem B1204055 : Blo 1202418 1204055 := bstep (se 1 (by rfl) ⟨903041, by rfl⟩ : syracuseStep 1204055 = 1806083) B1806083
theorem B1204075 : Blo 1202418 1204075 := bstep (se 1 (by rfl) ⟨903056, by rfl⟩ : syracuseStep 1204075 = 1806113) B1806113
theorem B1204087 : Blo 1202418 1204087 := bstep (se 1 (by rfl) ⟨903065, by rfl⟩ : syracuseStep 1204087 = 1806131) B1806131
theorem B6848387 : Blo 1202418 6848387 := bstep (se 1 (by rfl) ⟨5136290, by rfl⟩ : syracuseStep 6848387 = 10272581) B10272581
theorem B1204107 : Blo 1202418 1204107 := bstep (se 1 (by rfl) ⟨903080, by rfl⟩ : syracuseStep 1204107 = 1806161) B1806161
theorem B1204119 : Blo 1202418 1204119 := bstep (se 1 (by rfl) ⟨903089, by rfl⟩ : syracuseStep 1204119 = 1806179) B1806179
theorem B1204139 : Blo 1202418 1204139 := bstep (se 1 (by rfl) ⟨903104, by rfl⟩ : syracuseStep 1204139 = 1806209) B1806209
theorem B2285491 : Blo 1202418 2285491 := bstep (se 1 (by rfl) ⟨1714118, by rfl⟩ : syracuseStep 2285491 = 3428237) B3428237
theorem B1204151 : Blo 1202418 1204151 := bstep (se 1 (by rfl) ⟨903113, by rfl⟩ : syracuseStep 1204151 = 1806227) B1806227
theorem B1204171 : Blo 1202418 1204171 := bstep (se 1 (by rfl) ⟨903128, by rfl⟩ : syracuseStep 1204171 = 1806257) B1806257
theorem B1204183 : Blo 1202418 1204183 := bstep (se 1 (by rfl) ⟨903137, by rfl⟩ : syracuseStep 1204183 = 1806275) B1806275
theorem B1204203 : Blo 1202418 1204203 := bstep (se 1 (by rfl) ⟨903152, by rfl⟩ : syracuseStep 1204203 = 1806305) B1806305
theorem B1286123 : Blo 1202418 1286123 := bstep (se 1 (by rfl) ⟨964592, by rfl⟩ : syracuseStep 1286123 = 1929185) B1929185
theorem B1204231 : Blo 1202418 1204231 := bstep (se 1 (by rfl) ⟨903173, by rfl⟩ : syracuseStep 1204231 = 1806347) B1806347
theorem B1204239 : Blo 1202418 1204239 := bstep (se 1 (by rfl) ⟨903179, by rfl⟩ : syracuseStep 1204239 = 1806359) B1806359
theorem B27795473 : Blo 1202418 27795473 := bstep (se 2 (by rfl) ⟨10423302, by rfl⟩ : syracuseStep 27795473 = 20846605) B20846605
theorem B3047483 : Blo 1202418 3047483 := bstep (se 1 (by rfl) ⟨2285612, by rfl⟩ : syracuseStep 3047483 = 4571225) B4571225
theorem B1204283 : Blo 1202418 1204283 := bstep (se 1 (by rfl) ⟨903212, by rfl⟩ : syracuseStep 1204283 = 1806425) B1806425
theorem B4571255 : Blo 1202418 4571255 := bstep (se 1 (by rfl) ⟨3428441, by rfl⟩ : syracuseStep 4571255 = 6856883) B6856883
theorem B1204359 : Blo 1202418 1204359 := bstep (se 1 (by rfl) ⟨903269, by rfl⟩ : syracuseStep 1204359 = 1806539) B1806539
theorem B1204367 : Blo 1202418 1204367 := bstep (se 1 (by rfl) ⟨903275, by rfl⟩ : syracuseStep 1204367 = 1806551) B1806551
theorem B1204411 : Blo 1202418 1204411 := bstep (se 1 (by rfl) ⟨903308, by rfl⟩ : syracuseStep 1204411 = 1806617) B1806617
theorem B2031817 : Blo 1202418 2031817 := bstep (se 2 (by rfl) ⟨761931, by rfl⟩ : syracuseStep 2031817 = 1523863) B1523863
theorem B9134369 : Blo 1202418 9134369 := bstep (se 2 (by rfl) ⟨3425388, by rfl⟩ : syracuseStep 9134369 = 6850777) B6850777
theorem B6848819 : Blo 1202418 6848819 := bstep (se 1 (by rfl) ⟨5136614, by rfl⟩ : syracuseStep 6848819 = 10273229) B10273229
theorem B6095249 : Blo 1202418 6095249 := bstep (se 2 (by rfl) ⟨2285718, by rfl⟩ : syracuseStep 6095249 = 4571437) B4571437
theorem B3047827 : Blo 1202418 3047827 := bstep (se 1 (by rfl) ⟨2285870, by rfl⟩ : syracuseStep 3047827 = 4571741) B4571741
theorem B12345821 : Blo 1202418 12345821 := bstep (se 3 (by rfl) ⟨2314841, by rfl⟩ : syracuseStep 12345821 = 4629683) B4629683
theorem B5153291 : Blo 1202418 5153291 := bstep (se 1 (by rfl) ⟨3864968, by rfl⟩ : syracuseStep 5153291 = 7729937) B7729937
theorem B3047969 : Blo 1202418 3047969 := bstep (se 2 (by rfl) ⟨1142988, by rfl⟩ : syracuseStep 3047969 = 2285977) B2285977
theorem B2286281 : Blo 1202418 2286281 := bstep (se 2 (by rfl) ⟨857355, by rfl⟩ : syracuseStep 2286281 = 1714711) B1714711
theorem B5563151 : Blo 1202418 5563151 := bstep (se 1 (by rfl) ⟨4172363, by rfl⟩ : syracuseStep 5563151 = 8344727) B8344727
theorem B4064147 : Blo 1202418 4064147 := bstep (se 1 (by rfl) ⟨3048110, by rfl⟩ : syracuseStep 4064147 = 6096221) B6096221
theorem B5137469 : Blo 1202418 5137469 := bstep (se 3 (by rfl) ⟨963275, by rfl⟩ : syracuseStep 5137469 = 1926551) B1926551
theorem B4572227 : Blo 1202418 4572227 := bstep (se 1 (by rfl) ⟨3429170, by rfl⟩ : syracuseStep 4572227 = 6858341) B6858341
theorem B1352839 : Blo 1202418 1352839 := bstep (se 1 (by rfl) ⟨1014629, by rfl⟩ : syracuseStep 1352839 = 2029259) B2029259
theorem B9135341 : Blo 1202418 9135341 := bstep (se 3 (by rfl) ⟨1712876, by rfl⟩ : syracuseStep 9135341 = 3425753) B3425753
theorem B1353019 : Blo 1202418 1353019 := bstep (se 1 (by rfl) ⟨1014764, by rfl⟩ : syracuseStep 1353019 = 2029529) B2029529
theorem B2893171 : Blo 1202418 2893171 := bstep (se 1 (by rfl) ⟨2169878, by rfl⟩ : syracuseStep 2893171 = 4339757) B4339757
theorem B6088121 : Blo 1202418 6088121 := bstep (se 2 (by rfl) ⟨2283045, by rfl⟩ : syracuseStep 6088121 = 4566091) B4566091
theorem B1803707 : Blo 1202418 1803707 := bstep (se 1 (by rfl) ⟨1352780, by rfl⟩ : syracuseStep 1803707 = 2705561) B2705561
theorem B1803767 : Blo 1202418 1803767 := bstep (se 1 (by rfl) ⟨1352825, by rfl⟩ : syracuseStep 1803767 = 2705651) B2705651
theorem B5137931 : Blo 1202418 5137931 := bstep (se 1 (by rfl) ⟨3853448, by rfl⟩ : syracuseStep 5137931 = 7706897) B7706897
theorem B4572683 : Blo 1202418 4572683 := bstep (se 1 (by rfl) ⟨3429512, by rfl⟩ : syracuseStep 4572683 = 6859025) B6859025
theorem B1803791 : Blo 1202418 1803791 := bstep (se 1 (by rfl) ⟨1352843, by rfl⟩ : syracuseStep 1803791 = 2705687) B2705687
theorem B5785111 : Blo 1202418 5785111 := bstep (se 1 (by rfl) ⟨4338833, by rfl⟩ : syracuseStep 5785111 = 8677667) B8677667
theorem B11568683 : Blo 1202418 11568683 := bstep (se 1 (by rfl) ⟨8676512, by rfl⟩ : syracuseStep 11568683 = 17353025) B17353025
theorem B1803833 : Blo 1202418 1803833 := bstep (se 2 (by rfl) ⟨676437, by rfl⟩ : syracuseStep 1803833 = 1352875) B1352875
theorem B1713737 : Blo 1202418 1713737 := bstep (se 2 (by rfl) ⟨642651, by rfl⟩ : syracuseStep 1713737 = 1285303) B1285303
theorem B1803911 : Blo 1202418 1803911 := bstep (se 1 (by rfl) ⟨1352933, by rfl⟩ : syracuseStep 1803911 = 2705867) B2705867
theorem B1803947 : Blo 1202418 1803947 := bstep (se 1 (by rfl) ⟨1352960, by rfl⟩ : syracuseStep 1803947 = 2705921) B2705921
theorem B1803977 : Blo 1202418 1803977 := bstep (se 2 (by rfl) ⟨676491, by rfl⟩ : syracuseStep 1803977 = 1352983) B1352983
theorem B6850277 : Blo 1202418 6850277 := bstep (se 4 (by rfl) ⟨642213, by rfl⟩ : syracuseStep 6850277 = 1284427) B1284427
theorem B1353487 : Blo 1202418 1353487 := bstep (se 1 (by rfl) ⟨1015115, by rfl⟩ : syracuseStep 1353487 = 2030231) B2030231
theorem B1804091 : Blo 1202418 1804091 := bstep (se 1 (by rfl) ⟨1353068, by rfl⟩ : syracuseStep 1804091 = 2706137) B2706137
theorem B1804151 : Blo 1202418 1804151 := bstep (se 1 (by rfl) ⟨1353113, by rfl⟩ : syracuseStep 1804151 = 2706227) B2706227
theorem B1804175 : Blo 1202418 1804175 := bstep (se 1 (by rfl) ⟨1353131, by rfl⟩ : syracuseStep 1804175 = 2706263) B2706263
theorem B24692633 : Blo 1202418 24692633 := bstep (se 2 (by rfl) ⟨9259737, by rfl⟩ : syracuseStep 24692633 = 18519475) B18519475
theorem B1804217 : Blo 1202418 1804217 := bstep (se 2 (by rfl) ⟨676581, by rfl⟩ : syracuseStep 1804217 = 1353163) B1353163
theorem B1804295 : Blo 1202418 1804295 := bstep (se 1 (by rfl) ⟨1353221, by rfl⟩ : syracuseStep 1804295 = 2706443) B2706443
theorem B1804331 : Blo 1202418 1804331 := bstep (se 1 (by rfl) ⟨1353248, by rfl⟩ : syracuseStep 1804331 = 2706497) B2706497
theorem B1804361 : Blo 1202418 1804361 := bstep (se 2 (by rfl) ⟨676635, by rfl⟩ : syracuseStep 1804361 = 1353271) B1353271
theorem B3426391 : Blo 1202418 3426391 := bstep (se 1 (by rfl) ⟨2569793, by rfl⟩ : syracuseStep 3426391 = 5139587) B5139587
theorem B2705543 : Blo 1202418 2705543 := bstep (se 1 (by rfl) ⟨2029157, by rfl⟩ : syracuseStep 2705543 = 4058315) B4058315
theorem B1804475 : Blo 1202418 1804475 := bstep (se 1 (by rfl) ⟨1353356, by rfl⟩ : syracuseStep 1804475 = 2706713) B2706713
theorem B1804535 : Blo 1202418 1804535 := bstep (se 1 (by rfl) ⟨1353401, by rfl⟩ : syracuseStep 1804535 = 2706803) B2706803
theorem B1353991 : Blo 1202418 1353991 := bstep (se 1 (by rfl) ⟨1015493, by rfl⟩ : syracuseStep 1353991 = 2030987) B2030987
theorem B1804559 : Blo 1202418 1804559 := bstep (se 1 (by rfl) ⟨1353419, by rfl⟩ : syracuseStep 1804559 = 2706839) B2706839
theorem B1804601 : Blo 1202418 1804601 := bstep (se 2 (by rfl) ⟨676725, by rfl⟩ : syracuseStep 1804601 = 1353451) B1353451
theorem B2705723 : Blo 1202418 2705723 := bstep (se 1 (by rfl) ⟨2029292, by rfl⟩ : syracuseStep 2705723 = 4058585) B4058585
theorem B3426619 : Blo 1202418 3426619 := bstep (se 1 (by rfl) ⟨2569964, by rfl⟩ : syracuseStep 3426619 = 5139929) B5139929
theorem B6506867 : Blo 1202418 6506867 := bstep (se 1 (by rfl) ⟨4880150, by rfl⟩ : syracuseStep 6506867 = 9760301) B9760301
theorem B1804679 : Blo 1202418 1804679 := bstep (se 1 (by rfl) ⟨1353509, by rfl⟩ : syracuseStep 1804679 = 2707019) B2707019
theorem B2935187 : Blo 1202418 2935187 := bstep (se 1 (by rfl) ⟨2201390, by rfl⟩ : syracuseStep 2935187 = 4402781) B4402781
theorem B1804715 : Blo 1202418 1804715 := bstep (se 1 (by rfl) ⟨1353536, by rfl⟩ : syracuseStep 1804715 = 2707073) B2707073
theorem B1714603 : Blo 1202418 1714603 := bstep (se 1 (by rfl) ⟨1285952, by rfl⟩ : syracuseStep 1714603 = 2571905) B2571905
theorem B2705849 : Blo 1202418 2705849 := bstep (se 2 (by rfl) ⟨1014693, by rfl⟩ : syracuseStep 2705849 = 2029387) B2029387
theorem B3426745 : Blo 1202418 3426745 := bstep (se 2 (by rfl) ⟨1285029, by rfl⟩ : syracuseStep 3426745 = 2570059) B2570059
theorem B1354171 : Blo 1202418 1354171 := bstep (se 1 (by rfl) ⟨1015628, by rfl⟩ : syracuseStep 1354171 = 2031257) B2031257
theorem B1804745 : Blo 1202418 1804745 := bstep (se 2 (by rfl) ⟨676779, by rfl⟩ : syracuseStep 1804745 = 1353559) B1353559
theorem B6097355 : Blo 1202418 6097355 := bstep (se 1 (by rfl) ⟨4573016, by rfl⟩ : syracuseStep 6097355 = 9146033) B9146033
theorem B4876843 : Blo 1202418 4876843 := bstep (se 1 (by rfl) ⟨3657632, by rfl⟩ : syracuseStep 4876843 = 7315265) B7315265
theorem B1804859 : Blo 1202418 1804859 := bstep (se 1 (by rfl) ⟨1353644, by rfl⟩ : syracuseStep 1804859 = 2707289) B2707289
theorem B27855427 : Blo 1202418 27855427 := bstep (se 1 (by rfl) ⟨20891570, by rfl⟩ : syracuseStep 27855427 = 41783141) B41783141
theorem B4565591 : Blo 1202418 4565591 := bstep (se 1 (by rfl) ⟨3424193, by rfl⟩ : syracuseStep 4565591 = 6848387) B6848387
theorem B1804919 : Blo 1202418 1804919 := bstep (se 1 (by rfl) ⟨1353689, by rfl⟩ : syracuseStep 1804919 = 2707379) B2707379
theorem B1804943 : Blo 1202418 1804943 := bstep (se 1 (by rfl) ⟨1353707, by rfl⟩ : syracuseStep 1804943 = 2707415) B2707415
theorem B1804985 : Blo 1202418 1804985 := bstep (se 2 (by rfl) ⟨676869, by rfl⟩ : syracuseStep 1804985 = 1353739) B1353739
theorem B6089417 : Blo 1202418 6089417 := bstep (se 2 (by rfl) ⟨2283531, by rfl⟩ : syracuseStep 6089417 = 4567063) B4567063
theorem B9145061 : Blo 1202418 9145061 := bstep (se 4 (by rfl) ⟨857349, by rfl⟩ : syracuseStep 9145061 = 1714699) B1714699
theorem B1805063 : Blo 1202418 1805063 := bstep (se 1 (by rfl) ⟨1353797, by rfl⟩ : syracuseStep 1805063 = 2707595) B2707595
theorem B5778191 : Blo 1202418 5778191 := bstep (se 1 (by rfl) ⟨4333643, by rfl⟩ : syracuseStep 5778191 = 8667287) B8667287
theorem B2706191 : Blo 1202418 2706191 := bstep (se 1 (by rfl) ⟨2029643, by rfl⟩ : syracuseStep 2706191 = 4059287) B4059287
theorem B2706209 : Blo 1202418 2706209 := bstep (se 2 (by rfl) ⟨1014828, by rfl⟩ : syracuseStep 2706209 = 2029657) B2029657
theorem B1805099 : Blo 1202418 1805099 := bstep (se 1 (by rfl) ⟨1353824, by rfl⟩ : syracuseStep 1805099 = 2707649) B2707649
theorem B5860147 : Blo 1202418 5860147 := bstep (se 1 (by rfl) ⟨4395110, by rfl⟩ : syracuseStep 5860147 = 8790221) B8790221
theorem B1805129 : Blo 1202418 1805129 := bstep (se 2 (by rfl) ⟨676923, by rfl⟩ : syracuseStep 1805129 = 1353847) B1353847
theorem B23751539 : Blo 1202418 23751539 := bstep (se 1 (by rfl) ⟨17813654, by rfl⟩ : syracuseStep 23751539 = 35627309) B35627309
theorem B1354639 : Blo 1202418 1354639 := bstep (se 1 (by rfl) ⟨1015979, by rfl⟩ : syracuseStep 1354639 = 2031959) B2031959
theorem B1805243 : Blo 1202418 1805243 := bstep (se 1 (by rfl) ⟨1353932, by rfl⟩ : syracuseStep 1805243 = 2707865) B2707865
theorem B1805303 : Blo 1202418 1805303 := bstep (se 1 (by rfl) ⟨1353977, by rfl⟩ : syracuseStep 1805303 = 2707955) B2707955
theorem B1805327 : Blo 1202418 1805327 := bstep (se 1 (by rfl) ⟨1353995, by rfl⟩ : syracuseStep 1805327 = 2707991) B2707991
theorem B1805369 : Blo 1202418 1805369 := bstep (se 2 (by rfl) ⟨677013, by rfl⟩ : syracuseStep 1805369 = 1354027) B1354027
theorem B4566077 : Blo 1202418 4566077 := bstep (se 3 (by rfl) ⟨856139, by rfl⟩ : syracuseStep 4566077 = 1712279) B1712279
theorem B5778499 : Blo 1202418 5778499 := bstep (se 1 (by rfl) ⟨4333874, by rfl⟩ : syracuseStep 5778499 = 8667749) B8667749
theorem B2706551 : Blo 1202418 2706551 := bstep (se 1 (by rfl) ⟨2029913, by rfl⟩ : syracuseStep 2706551 = 4059827) B4059827
theorem B9137285 : Blo 1202418 9137285 := bstep (se 4 (by rfl) ⟨856620, by rfl⟩ : syracuseStep 9137285 = 1713241) B1713241
theorem B1805447 : Blo 1202418 1805447 := bstep (se 1 (by rfl) ⟨1354085, by rfl⟩ : syracuseStep 1805447 = 2708171) B2708171
theorem B1805483 : Blo 1202418 1805483 := bstep (se 1 (by rfl) ⟨1354112, by rfl⟩ : syracuseStep 1805483 = 2708225) B2708225
theorem B13888685 : Blo 1202418 13888685 := bstep (se 3 (by rfl) ⟨2604128, by rfl⟩ : syracuseStep 13888685 = 5208257) B5208257
theorem B1805513 : Blo 1202418 1805513 := bstep (se 2 (by rfl) ⟨677067, by rfl⟩ : syracuseStep 1805513 = 1354135) B1354135
theorem B2059465 : Blo 1202418 2059465 := bstep (se 2 (by rfl) ⟨772299, by rfl⟩ : syracuseStep 2059465 = 1544599) B1544599
theorem B4058369 : Blo 1202418 4058369 := bstep (se 2 (by rfl) ⟨1521888, by rfl⟩ : syracuseStep 4058369 = 3043777) B3043777
theorem B2706731 : Blo 1202418 2706731 := bstep (se 1 (by rfl) ⟨2030048, by rfl⟩ : syracuseStep 2706731 = 4060097) B4060097
theorem B1805627 : Blo 1202418 1805627 := bstep (se 1 (by rfl) ⟨1354220, by rfl⟩ : syracuseStep 1805627 = 2708441) B2708441
theorem B5786939 : Blo 1202418 5786939 := bstep (se 1 (by rfl) ⟨4340204, by rfl⟩ : syracuseStep 5786939 = 8680409) B8680409
theorem B1805687 : Blo 1202418 1805687 := bstep (se 1 (by rfl) ⟨1354265, by rfl⟩ : syracuseStep 1805687 = 2708531) B2708531
theorem B12520835 : Blo 1202418 12520835 := bstep (se 1 (by rfl) ⟨9390626, by rfl⟩ : syracuseStep 12520835 = 18781253) B18781253
theorem B1805711 : Blo 1202418 1805711 := bstep (se 1 (by rfl) ⟨1354283, by rfl⟩ : syracuseStep 1805711 = 2708567) B2708567
theorem B1805753 : Blo 1202418 1805753 := bstep (se 2 (by rfl) ⟨677157, by rfl⟩ : syracuseStep 1805753 = 1354315) B1354315
theorem B1805831 : Blo 1202418 1805831 := bstep (se 1 (by rfl) ⟨1354373, by rfl⟩ : syracuseStep 1805831 = 2708747) B2708747
theorem B1805867 : Blo 1202418 1805867 := bstep (se 1 (by rfl) ⟨1354400, by rfl⟩ : syracuseStep 1805867 = 2708801) B2708801
theorem B4017725 : Blo 1202418 4017725 := bstep (se 3 (by rfl) ⟨753323, by rfl⟩ : syracuseStep 4017725 = 1506647) B1506647
theorem B1805897 : Blo 1202418 1805897 := bstep (se 2 (by rfl) ⟨677211, by rfl⟩ : syracuseStep 1805897 = 1354423) B1354423
theorem B2707091 : Blo 1202418 2707091 := bstep (se 1 (by rfl) ⟨2030318, by rfl⟩ : syracuseStep 2707091 = 4060637) B4060637
theorem B1806011 : Blo 1202418 1806011 := bstep (se 1 (by rfl) ⟨1354508, by rfl⟩ : syracuseStep 1806011 = 2709017) B2709017
theorem B2707145 : Blo 1202418 2707145 := bstep (se 2 (by rfl) ⟨1015179, by rfl⟩ : syracuseStep 2707145 = 2030359) B2030359
theorem B5140169 : Blo 1202418 5140169 := bstep (se 2 (by rfl) ⟨1927563, by rfl⟩ : syracuseStep 5140169 = 3855127) B3855127
theorem B13700825 : Blo 1202418 13700825 := bstep (se 2 (by rfl) ⟨5137809, by rfl⟩ : syracuseStep 13700825 = 10275619) B10275619
theorem B1806071 : Blo 1202418 1806071 := bstep (se 1 (by rfl) ⟨1354553, by rfl⟩ : syracuseStep 1806071 = 2709107) B2709107
theorem B8670977 : Blo 1202418 8670977 := bstep (se 2 (by rfl) ⟨3251616, by rfl⟩ : syracuseStep 8670977 = 6503233) B6503233
theorem B1806095 : Blo 1202418 1806095 := bstep (se 1 (by rfl) ⟨1354571, by rfl⟩ : syracuseStep 1806095 = 2709143) B2709143
theorem B1806137 : Blo 1202418 1806137 := bstep (se 2 (by rfl) ⟨677301, by rfl⟩ : syracuseStep 1806137 = 1354603) B1354603
theorem B1806215 : Blo 1202418 1806215 := bstep (se 1 (by rfl) ⟨1354661, by rfl⟩ : syracuseStep 1806215 = 2709323) B2709323
theorem B5779345 : Blo 1202418 5779345 := bstep (se 2 (by rfl) ⟨2167254, by rfl⟩ : syracuseStep 5779345 = 4334509) B4334509
theorem B15429527 : Blo 1202418 15429527 := bstep (se 1 (by rfl) ⟨11572145, by rfl⟩ : syracuseStep 15429527 = 23144291) B23144291
theorem B1806251 : Blo 1202418 1806251 := bstep (se 1 (by rfl) ⟨1354688, by rfl⟩ : syracuseStep 1806251 = 2709377) B2709377
theorem B1806281 : Blo 1202418 1806281 := bstep (se 2 (by rfl) ⟨677355, by rfl⟩ : syracuseStep 1806281 = 1354711) B1354711
theorem B4059179 : Blo 1202418 4059179 := bstep (se 1 (by rfl) ⟨3044384, by rfl⟩ : syracuseStep 4059179 = 6088769) B6088769
theorem B1806395 : Blo 1202418 1806395 := bstep (se 1 (by rfl) ⟨1354796, by rfl⟩ : syracuseStep 1806395 = 2709593) B2709593
theorem B1806455 : Blo 1202418 1806455 := bstep (se 1 (by rfl) ⟨1354841, by rfl⟩ : syracuseStep 1806455 = 2709683) B2709683
theorem B1806479 : Blo 1202418 1806479 := bstep (se 1 (by rfl) ⟨1354859, by rfl⟩ : syracuseStep 1806479 = 2709719) B2709719
theorem B1806521 : Blo 1202418 1806521 := bstep (se 2 (by rfl) ⟨677445, by rfl⟩ : syracuseStep 1806521 = 1354891) B1354891
theorem B3854537 : Blo 1202418 3854537 := bstep (se 2 (by rfl) ⟨1445451, by rfl⟩ : syracuseStep 3854537 = 2890903) B2890903
theorem B1806599 : Blo 1202418 1806599 := bstep (se 1 (by rfl) ⟨1354949, by rfl⟩ : syracuseStep 1806599 = 2709899) B2709899
theorem B3428669 : Blo 1202418 3428669 := bstep (se 3 (by rfl) ⟨642875, by rfl⟩ : syracuseStep 3428669 = 1285751) B1285751
theorem B2707847 : Blo 1202418 2707847 := bstep (se 1 (by rfl) ⟨2030885, by rfl⟩ : syracuseStep 2707847 = 4061771) B4061771
theorem B5485099 : Blo 1202418 5485099 := bstep (se 1 (by rfl) ⟨4113824, by rfl⟩ : syracuseStep 5485099 = 8227649) B8227649
theorem B2708027 : Blo 1202418 2708027 := bstep (se 1 (by rfl) ⟨2031020, by rfl⟩ : syracuseStep 2708027 = 4062041) B4062041
theorem B4117079 : Blo 1202418 4117079 := bstep (se 1 (by rfl) ⟨3087809, by rfl⟩ : syracuseStep 4117079 = 6175619) B6175619
theorem B1856135 : Blo 1202418 1856135 := bstep (se 1 (by rfl) ⟨1392101, by rfl⟩ : syracuseStep 1856135 = 2784203) B2784203
theorem B2708153 : Blo 1202418 2708153 := bstep (se 2 (by rfl) ⟨1015557, by rfl⟩ : syracuseStep 2708153 = 2031115) B2031115
theorem B4567823 : Blo 1202418 4567823 := bstep (se 1 (by rfl) ⟨3425867, by rfl⟩ : syracuseStep 4567823 = 6851735) B6851735
theorem B9270053 : Blo 1202418 9270053 := bstep (se 4 (by rfl) ⟨869067, by rfl⟩ : syracuseStep 9270053 = 1738135) B1738135
theorem B13718321 : Blo 1202418 13718321 := bstep (se 2 (by rfl) ⟨5144370, by rfl⟩ : syracuseStep 13718321 = 10288741) B10288741
theorem B3298163 : Blo 1202418 3298163 := bstep (se 1 (by rfl) ⟨2473622, by rfl⟩ : syracuseStep 3298163 = 4947245) B4947245
theorem B6853511 : Blo 1202418 6853511 := bstep (se 1 (by rfl) ⟨5140133, by rfl⟩ : syracuseStep 6853511 = 10280267) B10280267
theorem B3044243 : Blo 1202418 3044243 := bstep (se 1 (by rfl) ⟨2283182, by rfl⟩ : syracuseStep 3044243 = 4566365) B4566365
theorem B4395961 : Blo 1202418 4395961 := bstep (se 2 (by rfl) ⟨1648485, by rfl⟩ : syracuseStep 4395961 = 3296971) B3296971
theorem B2470927 : Blo 1202418 2470927 := bstep (se 1 (by rfl) ⟨1853195, by rfl⟩ : syracuseStep 2470927 = 3706391) B3706391
theorem B2708495 : Blo 1202418 2708495 := bstep (se 1 (by rfl) ⟨2031371, by rfl⟩ : syracuseStep 2708495 = 4062743) B4062743
theorem B2708513 : Blo 1202418 2708513 := bstep (se 2 (by rfl) ⟨1015692, by rfl⟩ : syracuseStep 2708513 = 2031385) B2031385
theorem B6853693 : Blo 1202418 6853693 := bstep (se 3 (by rfl) ⟨1285067, by rfl⟩ : syracuseStep 6853693 = 2570135) B2570135
theorem B3044537 : Blo 1202418 3044537 := bstep (se 2 (by rfl) ⟨1141701, by rfl⟩ : syracuseStep 3044537 = 2283403) B2283403
theorem B3429661 : Blo 1202418 3429661 := bstep (se 3 (by rfl) ⟨643061, by rfl⟩ : syracuseStep 3429661 = 1286123) B1286123
theorem B4060475 : Blo 1202418 4060475 := bstep (se 1 (by rfl) ⟨3045356, by rfl⟩ : syracuseStep 4060475 = 6090713) B6090713
theorem B2708855 : Blo 1202418 2708855 := bstep (se 1 (by rfl) ⟨2031641, by rfl⟩ : syracuseStep 2708855 = 4063283) B4063283
theorem B4879763 : Blo 1202418 4879763 := bstep (se 1 (by rfl) ⟨3659822, by rfl⟩ : syracuseStep 4879763 = 7319645) B7319645
theorem B2569657 : Blo 1202418 2569657 := bstep (se 2 (by rfl) ⟨963621, by rfl⟩ : syracuseStep 2569657 = 1927243) B1927243
theorem B10278353 : Blo 1202418 10278353 := bstep (se 2 (by rfl) ⟨3854382, by rfl⟩ : syracuseStep 10278353 = 7708765) B7708765
theorem B9139715 : Blo 1202418 9139715 := bstep (se 1 (by rfl) ⟨6854786, by rfl⟩ : syracuseStep 9139715 = 13709573) B13709573
theorem B9754141 : Blo 1202418 9754141 := bstep (se 3 (by rfl) ⟨1828901, by rfl⟩ : syracuseStep 9754141 = 3657803) B3657803
theorem B2709035 : Blo 1202418 2709035 := bstep (se 1 (by rfl) ⟨2031776, by rfl⟩ : syracuseStep 2709035 = 4063553) B4063553
theorem B156243653 : Blo 1202418 156243653 := bstep (se 4 (by rfl) ⟨14647842, by rfl⟩ : syracuseStep 156243653 = 29295685) B29295685
theorem B4060961 : Blo 1202418 4060961 := bstep (se 2 (by rfl) ⟨1522860, by rfl⟩ : syracuseStep 4060961 = 3045721) B3045721
theorem B5142305 : Blo 1202418 5142305 := bstep (se 2 (by rfl) ⟨1928364, by rfl⟩ : syracuseStep 5142305 = 3856729) B3856729
theorem B3045235 : Blo 1202418 3045235 := bstep (se 1 (by rfl) ⟨2283926, by rfl⟩ : syracuseStep 3045235 = 4567853) B4567853
theorem B2709395 : Blo 1202418 2709395 := bstep (se 1 (by rfl) ⟨2032046, by rfl⟩ : syracuseStep 2709395 = 4064093) B4064093
theorem B9131939 : Blo 1202418 9131939 := bstep (se 1 (by rfl) ⟨6848954, by rfl⟩ : syracuseStep 9131939 = 13697909) B13697909
theorem B5142457 : Blo 1202418 5142457 := bstep (se 2 (by rfl) ⟨1928421, by rfl⟩ : syracuseStep 5142457 = 3856843) B3856843
theorem B2709449 : Blo 1202418 2709449 := bstep (se 2 (by rfl) ⟨1016043, by rfl⟩ : syracuseStep 2709449 = 2032087) B2032087
theorem B3045377 : Blo 1202418 3045377 := bstep (se 2 (by rfl) ⟨1142016, by rfl⟩ : syracuseStep 3045377 = 2284033) B2284033
theorem B6944779 : Blo 1202418 6944779 := bstep (se 1 (by rfl) ⟨5208584, by rfl⟩ : syracuseStep 6944779 = 10417169) B10417169
theorem B7821323 : Blo 1202418 7821323 := bstep (se 1 (by rfl) ⟨5865992, by rfl⟩ : syracuseStep 7821323 = 11731985) B11731985
theorem B2029583 : Blo 1202418 2029583 := bstep (se 1 (by rfl) ⟨1522187, by rfl⟩ : syracuseStep 2029583 = 3044375) B3044375
theorem B2439227 : Blo 1202418 2439227 := bstep (se 1 (by rfl) ⟨1829420, by rfl⟩ : syracuseStep 2439227 = 3658841) B3658841
theorem B2783351 : Blo 1202418 2783351 := bstep (se 1 (by rfl) ⟨2087513, by rfl⟩ : syracuseStep 2783351 = 4175027) B4175027
theorem B2570375 : Blo 1202418 2570375 := bstep (se 1 (by rfl) ⟨1927781, by rfl⟩ : syracuseStep 2570375 = 3855563) B3855563
theorem B1202439 : Blo 1202418 1202439 := bstep (se 1 (by rfl) ⟨901829, by rfl⟩ : syracuseStep 1202439 = 1803659) B1803659
theorem B1202447 : Blo 1202418 1202447 := bstep (se 1 (by rfl) ⟨901835, by rfl⟩ : syracuseStep 1202447 = 1803671) B1803671
theorem B1202491 : Blo 1202418 1202491 := bstep (se 1 (by rfl) ⟨901868, by rfl⟩ : syracuseStep 1202491 = 1803737) B1803737
theorem B4061555 : Blo 1202418 4061555 := bstep (se 1 (by rfl) ⟨3046166, by rfl⟩ : syracuseStep 4061555 = 6092333) B6092333
theorem B1202567 : Blo 1202418 1202567 := bstep (se 1 (by rfl) ⟨901925, by rfl⟩ : syracuseStep 1202567 = 1803851) B1803851
theorem B4569479 : Blo 1202418 4569479 := bstep (se 1 (by rfl) ⟨3427109, by rfl⟩ : syracuseStep 4569479 = 6854219) B6854219
theorem B7420295 : Blo 1202418 7420295 := bstep (se 1 (by rfl) ⟨5565221, by rfl⟩ : syracuseStep 7420295 = 11130443) B11130443
theorem B1202575 : Blo 1202418 1202575 := bstep (se 1 (by rfl) ⟨901931, by rfl⟩ : syracuseStep 1202575 = 1803863) B1803863
theorem B1522091 : Blo 1202418 1522091 := bstep (se 1 (by rfl) ⟨1141568, by rfl⟩ : syracuseStep 1522091 = 2283137) B2283137
theorem B1202619 : Blo 1202418 1202619 := bstep (se 1 (by rfl) ⟨901964, by rfl⟩ : syracuseStep 1202619 = 1803929) B1803929
theorem B3045833 : Blo 1202418 3045833 := bstep (se 2 (by rfl) ⟨1142187, by rfl⟩ : syracuseStep 3045833 = 2284375) B2284375
theorem B8673745 : Blo 1202418 8673745 := bstep (se 2 (by rfl) ⟨3252654, by rfl⟩ : syracuseStep 8673745 = 6505309) B6505309
theorem B1202695 : Blo 1202418 1202695 := bstep (se 1 (by rfl) ⟨902021, by rfl⟩ : syracuseStep 1202695 = 1804043) B1804043
theorem B1202703 : Blo 1202418 1202703 := bstep (se 1 (by rfl) ⟨902027, by rfl⟩ : syracuseStep 1202703 = 1804055) B1804055
theorem B2030123 : Blo 1202418 2030123 := bstep (se 1 (by rfl) ⟨1522592, by rfl⟩ : syracuseStep 2030123 = 3045185) B3045185
theorem B1202747 : Blo 1202418 1202747 := bstep (se 1 (by rfl) ⟨902060, by rfl⟩ : syracuseStep 1202747 = 1804121) B1804121
theorem B1202823 : Blo 1202418 1202823 := bstep (se 1 (by rfl) ⟨902117, by rfl⟩ : syracuseStep 1202823 = 1804235) B1804235
theorem B2570887 : Blo 1202418 2570887 := bstep (se 1 (by rfl) ⟨1928165, by rfl⟩ : syracuseStep 2570887 = 3856331) B3856331
theorem B1202831 : Blo 1202418 1202831 := bstep (se 1 (by rfl) ⟨902123, by rfl⟩ : syracuseStep 1202831 = 1804247) B1804247
theorem B1202875 : Blo 1202418 1202875 := bstep (se 1 (by rfl) ⟨902156, by rfl⟩ : syracuseStep 1202875 = 1804313) B1804313
theorem B6503105 : Blo 1202418 6503105 := bstep (se 2 (by rfl) ⟨2438664, by rfl⟩ : syracuseStep 6503105 = 4877329) B4877329
theorem B5143277 : Blo 1202418 5143277 := bstep (se 3 (by rfl) ⟨964364, by rfl⟩ : syracuseStep 5143277 = 1928729) B1928729
theorem B6855425 : Blo 1202418 6855425 := bstep (se 2 (by rfl) ⟨2570784, by rfl⟩ : syracuseStep 6855425 = 5141569) B5141569
theorem B1202951 : Blo 1202418 1202951 := bstep (se 1 (by rfl) ⟨902213, by rfl⟩ : syracuseStep 1202951 = 1804427) B1804427
theorem B1202959 : Blo 1202418 1202959 := bstep (se 1 (by rfl) ⟨902219, by rfl⟩ : syracuseStep 1202959 = 1804439) B1804439
theorem B2571041 : Blo 1202418 2571041 := bstep (se 2 (by rfl) ⟨964140, by rfl⟩ : syracuseStep 2571041 = 1928281) B1928281
theorem B3046187 : Blo 1202418 3046187 := bstep (se 1 (by rfl) ⟨2284640, by rfl⟩ : syracuseStep 3046187 = 4569281) B4569281
theorem B1203003 : Blo 1202418 1203003 := bstep (se 1 (by rfl) ⟨902252, by rfl⟩ : syracuseStep 1203003 = 1804505) B1804505
theorem B1522567 : Blo 1202418 1522567 := bstep (se 1 (by rfl) ⟨1141925, by rfl⟩ : syracuseStep 1522567 = 2283851) B2283851
theorem B1203079 : Blo 1202418 1203079 := bstep (se 1 (by rfl) ⟨902309, by rfl⟩ : syracuseStep 1203079 = 1804619) B1804619
theorem B1203087 : Blo 1202418 1203087 := bstep (se 1 (by rfl) ⟨902315, by rfl⟩ : syracuseStep 1203087 = 1804631) B1804631
theorem B2030521 : Blo 1202418 2030521 := bstep (se 2 (by rfl) ⟨761445, by rfl⟩ : syracuseStep 2030521 = 1522891) B1522891
theorem B1203131 : Blo 1202418 1203131 := bstep (se 1 (by rfl) ⟨902348, by rfl⟩ : syracuseStep 1203131 = 1804697) B1804697
theorem B1203207 : Blo 1202418 1203207 := bstep (se 1 (by rfl) ⟨902405, by rfl⟩ : syracuseStep 1203207 = 1804811) B1804811
theorem B1203215 : Blo 1202418 1203215 := bstep (se 1 (by rfl) ⟨902411, by rfl⟩ : syracuseStep 1203215 = 1804823) B1804823
theorem B1203259 : Blo 1202418 1203259 := bstep (se 1 (by rfl) ⟨902444, by rfl⟩ : syracuseStep 1203259 = 1804889) B1804889
theorem B1203335 : Blo 1202418 1203335 := bstep (se 1 (by rfl) ⟨902501, by rfl⟩ : syracuseStep 1203335 = 1805003) B1805003
theorem B2284679 : Blo 1202418 2284679 := bstep (se 1 (by rfl) ⟨1713509, by rfl⟩ : syracuseStep 2284679 = 3427019) B3427019
theorem B1203343 : Blo 1202418 1203343 := bstep (se 1 (by rfl) ⟨902507, by rfl⟩ : syracuseStep 1203343 = 1805015) B1805015
theorem B1203387 : Blo 1202418 1203387 := bstep (se 1 (by rfl) ⟨902540, by rfl⟩ : syracuseStep 1203387 = 1805081) B1805081
theorem B2891009 : Blo 1202418 2891009 := bstep (se 2 (by rfl) ⟨1084128, by rfl⟩ : syracuseStep 2891009 = 2168257) B2168257
theorem B1203463 : Blo 1202418 1203463 := bstep (se 1 (by rfl) ⟨902597, by rfl⟩ : syracuseStep 1203463 = 1805195) B1805195
theorem B1203471 : Blo 1202418 1203471 := bstep (se 1 (by rfl) ⟨902603, by rfl⟩ : syracuseStep 1203471 = 1805207) B1805207
theorem B2571563 : Blo 1202418 2571563 := bstep (se 1 (by rfl) ⟨1928672, by rfl⟩ : syracuseStep 2571563 = 3857345) B3857345
theorem B1203515 : Blo 1202418 1203515 := bstep (se 1 (by rfl) ⟨902636, by rfl⟩ : syracuseStep 1203515 = 1805273) B1805273
theorem B2088251 : Blo 1202418 2088251 := bstep (se 1 (by rfl) ⟨1566188, by rfl⟩ : syracuseStep 2088251 = 3132377) B3132377
theorem B1523063 : Blo 1202418 1523063 := bstep (se 1 (by rfl) ⟨1142297, by rfl⟩ : syracuseStep 1523063 = 2284595) B2284595
theorem B3661175 : Blo 1202418 3661175 := bstep (se 1 (by rfl) ⟨2745881, by rfl⟩ : syracuseStep 3661175 = 5491763) B5491763
theorem B1203591 : Blo 1202418 1203591 := bstep (se 1 (by rfl) ⟨902693, by rfl⟩ : syracuseStep 1203591 = 1805387) B1805387
theorem B1203599 : Blo 1202418 1203599 := bstep (se 1 (by rfl) ⟨902699, by rfl⟩ : syracuseStep 1203599 = 1805399) B1805399
theorem B3251609 : Blo 1202418 3251609 := bstep (se 2 (by rfl) ⟨1219353, by rfl⟩ : syracuseStep 3251609 = 2438707) B2438707
theorem B3087769 : Blo 1202418 3087769 := bstep (se 2 (by rfl) ⟨1157913, by rfl⟩ : syracuseStep 3087769 = 2315827) B2315827
theorem B5143961 : Blo 1202418 5143961 := bstep (se 2 (by rfl) ⟨1928985, by rfl⟩ : syracuseStep 5143961 = 3857971) B3857971
theorem B1203643 : Blo 1202418 1203643 := bstep (se 1 (by rfl) ⟨902732, by rfl⟩ : syracuseStep 1203643 = 1805465) B1805465
theorem B1203719 : Blo 1202418 1203719 := bstep (se 1 (by rfl) ⟨902789, by rfl⟩ : syracuseStep 1203719 = 1805579) B1805579
theorem B1523215 : Blo 1202418 1523215 := bstep (se 1 (by rfl) ⟨1142411, by rfl⟩ : syracuseStep 1523215 = 2284823) B2284823
theorem B1203727 : Blo 1202418 1203727 := bstep (se 1 (by rfl) ⟨902795, by rfl⟩ : syracuseStep 1203727 = 1805591) B1805591
theorem B7421483 : Blo 1202418 7421483 := bstep (se 1 (by rfl) ⟨5566112, by rfl⟩ : syracuseStep 7421483 = 11132225) B11132225
theorem B1203771 : Blo 1202418 1203771 := bstep (se 1 (by rfl) ⟨902828, by rfl⟩ : syracuseStep 1203771 = 1805657) B1805657
theorem B2031223 : Blo 1202418 2031223 := bstep (se 1 (by rfl) ⟨1523417, by rfl⟩ : syracuseStep 2031223 = 3046835) B3046835
theorem B1203847 : Blo 1202418 1203847 := bstep (se 1 (by rfl) ⟨902885, by rfl⟩ : syracuseStep 1203847 = 1805771) B1805771
theorem B1203855 : Blo 1202418 1203855 := bstep (se 1 (by rfl) ⟨902891, by rfl⟩ : syracuseStep 1203855 = 1805783) B1805783
theorem B1523387 : Blo 1202418 1523387 := bstep (se 1 (by rfl) ⟨1142540, by rfl⟩ : syracuseStep 1523387 = 2285081) B2285081
theorem B1203899 : Blo 1202418 1203899 := bstep (se 1 (by rfl) ⟨902924, by rfl⟩ : syracuseStep 1203899 = 1805849) B1805849
theorem B1203975 : Blo 1202418 1203975 := bstep (se 1 (by rfl) ⟨902981, by rfl⟩ : syracuseStep 1203975 = 1805963) B1805963
theorem B3047179 : Blo 1202418 3047179 := bstep (se 1 (by rfl) ⟨2285384, by rfl⟩ : syracuseStep 3047179 = 4570769) B4570769
theorem B1203983 : Blo 1202418 1203983 := bstep (se 1 (by rfl) ⟨902987, by rfl⟩ : syracuseStep 1203983 = 1805975) B1805975
theorem B34676525 : Blo 1202418 34676525 := bstep (se 3 (by rfl) ⟨6501848, by rfl⟩ : syracuseStep 34676525 = 13003697) B13003697
theorem B15433523 : Blo 1202418 15433523 := bstep (se 1 (by rfl) ⟨11575142, by rfl⟩ : syracuseStep 15433523 = 23150285) B23150285
theorem B2031419 : Blo 1202418 2031419 := bstep (se 1 (by rfl) ⟨1523564, by rfl⟩ : syracuseStep 2031419 = 3047129) B3047129
theorem B1204027 : Blo 1202418 1204027 := bstep (se 1 (by rfl) ⟨903020, by rfl⟩ : syracuseStep 1204027 = 1806041) B1806041
theorem B1204103 : Blo 1202418 1204103 := bstep (se 1 (by rfl) ⟨903077, by rfl⟩ : syracuseStep 1204103 = 1806155) B1806155
theorem B1204111 : Blo 1202418 1204111 := bstep (se 1 (by rfl) ⟨903083, by rfl⟩ : syracuseStep 1204111 = 1806167) B1806167
theorem B3047321 : Blo 1202418 3047321 := bstep (se 2 (by rfl) ⟨1142745, by rfl⟩ : syracuseStep 3047321 = 2285491) B2285491
theorem B1204155 : Blo 1202418 1204155 := bstep (se 1 (by rfl) ⟨903116, by rfl⟩ : syracuseStep 1204155 = 1806233) B1806233
theorem B18530315 : Blo 1202418 18530315 := bstep (se 1 (by rfl) ⟨13897736, by rfl⟩ : syracuseStep 18530315 = 27795473) B27795473
theorem B2031655 : Blo 1202418 2031655 := bstep (se 1 (by rfl) ⟨1523741, by rfl⟩ : syracuseStep 2031655 = 3047483) B3047483
theorem B1204263 : Blo 1202418 1204263 := bstep (se 1 (by rfl) ⟨903197, by rfl⟩ : syracuseStep 1204263 = 1806395) B1806395
theorem B3047503 : Blo 1202418 3047503 := bstep (se 1 (by rfl) ⟨2285627, by rfl⟩ : syracuseStep 3047503 = 4571255) B4571255
theorem B1204303 : Blo 1202418 1204303 := bstep (se 1 (by rfl) ⟨903227, by rfl⟩ : syracuseStep 1204303 = 1806455) B1806455
theorem B1204319 : Blo 1202418 1204319 := bstep (se 1 (by rfl) ⟨903239, by rfl⟩ : syracuseStep 1204319 = 1806479) B1806479
theorem B1204347 : Blo 1202418 1204347 := bstep (se 1 (by rfl) ⟨903260, by rfl⟩ : syracuseStep 1204347 = 1806521) B1806521
theorem B1204399 : Blo 1202418 1204399 := bstep (se 1 (by rfl) ⟨903299, by rfl⟩ : syracuseStep 1204399 = 1806599) B1806599
theorem B4063499 : Blo 1202418 4063499 := bstep (se 1 (by rfl) ⟨3047624, by rfl⟩ : syracuseStep 4063499 = 6095249) B6095249
theorem B2031979 : Blo 1202418 2031979 := bstep (se 1 (by rfl) ⟨1523984, by rfl⟩ : syracuseStep 2031979 = 3047969) B3047969
theorem B1524187 : Blo 1202418 1524187 := bstep (se 1 (by rfl) ⟨1143140, by rfl⟩ : syracuseStep 1524187 = 2286281) B2286281
theorem B4063769 : Blo 1202418 4063769 := bstep (se 2 (by rfl) ⟨1523913, by rfl⟩ : syracuseStep 4063769 = 3047827) B3047827
theorem B2286137 : Blo 1202418 2286137 := bstep (se 2 (by rfl) ⟨857301, by rfl⟩ : syracuseStep 2286137 = 1714603) B1714603
theorem B7709357 : Blo 1202418 7709357 := bstep (se 3 (by rfl) ⟨1445504, by rfl⟩ : syracuseStep 7709357 = 2891009) B2891009
theorem B3424979 : Blo 1202418 3424979 := bstep (se 1 (by rfl) ⟨2568734, by rfl⟩ : syracuseStep 3424979 = 5137469) B5137469
theorem B3048151 : Blo 1202418 3048151 := bstep (se 1 (by rfl) ⟨2286113, by rfl⟩ : syracuseStep 3048151 = 4572227) B4572227
theorem B9143117 : Blo 1202418 9143117 := bstep (se 3 (by rfl) ⟨1714334, by rfl⟩ : syracuseStep 9143117 = 3428669) B3428669
theorem B3253175 : Blo 1202418 3253175 := bstep (se 1 (by rfl) ⟨2439881, by rfl⟩ : syracuseStep 3253175 = 4879763) B4879763
theorem B3425287 : Blo 1202418 3425287 := bstep (se 1 (by rfl) ⟨2568965, by rfl⟩ : syracuseStep 3425287 = 5137931) B5137931
theorem B3048455 : Blo 1202418 3048455 := bstep (se 1 (by rfl) ⟨2286341, by rfl⟩ : syracuseStep 3048455 = 4572683) B4572683
theorem B104162435 : Blo 1202418 104162435 := bstep (se 1 (by rfl) ⟨78121826, by rfl⟩ : syracuseStep 104162435 = 156243653) B156243653
theorem B6087959 : Blo 1202418 6087959 := bstep (se 1 (by rfl) ⟨4565969, by rfl⟩ : syracuseStep 6087959 = 9131939) B9131939
theorem B1353055 : Blo 1202418 1353055 := bstep (se 1 (by rfl) ⟨1014791, by rfl⟩ : syracuseStep 1353055 = 2029583) B2029583
theorem B3294569 : Blo 1202418 3294569 := bstep (se 2 (by rfl) ⟨1235463, by rfl⟩ : syracuseStep 3294569 = 2470927) B2470927
theorem B1803695 : Blo 1202418 1803695 := bstep (se 1 (by rfl) ⟨1352771, by rfl⟩ : syracuseStep 1803695 = 2705543) B2705543
theorem B1713583 : Blo 1202418 1713583 := bstep (se 1 (by rfl) ⟨1285187, by rfl⟩ : syracuseStep 1713583 = 2570375) B2570375
theorem B1803785 : Blo 1202418 1803785 := bstep (se 2 (by rfl) ⟨676419, by rfl⟩ : syracuseStep 1803785 = 1352839) B1352839
theorem B1803815 : Blo 1202418 1803815 := bstep (se 1 (by rfl) ⟨1352861, by rfl⟩ : syracuseStep 1803815 = 2705723) B2705723
theorem B10978877 : Blo 1202418 10978877 := bstep (se 3 (by rfl) ⟨2058539, by rfl⟩ : syracuseStep 10978877 = 4117079) B4117079
theorem B2745953 : Blo 1202418 2745953 := bstep (se 2 (by rfl) ⟨1029732, by rfl⟩ : syracuseStep 2745953 = 2059465) B2059465
theorem B1803899 : Blo 1202418 1803899 := bstep (se 1 (by rfl) ⟨1352924, by rfl⟩ : syracuseStep 1803899 = 2705849) B2705849
theorem B4064903 : Blo 1202418 4064903 := bstep (se 1 (by rfl) ⟨3048677, by rfl⟩ : syracuseStep 4064903 = 6097355) B6097355
theorem B4949693 : Blo 1202418 4949693 := bstep (se 3 (by rfl) ⟨928067, by rfl⟩ : syracuseStep 4949693 = 1856135) B1856135
theorem B1353415 : Blo 1202418 1353415 := bstep (se 1 (by rfl) ⟨1015061, by rfl⟩ : syracuseStep 1353415 = 2030123) B2030123
theorem B4572881 : Blo 1202418 4572881 := bstep (se 2 (by rfl) ⟨1714830, by rfl⟩ : syracuseStep 4572881 = 3429661) B3429661
theorem B1804025 : Blo 1202418 1804025 := bstep (se 2 (by rfl) ⟨676509, by rfl⟩ : syracuseStep 1804025 = 1353019) B1353019
theorem B6096707 : Blo 1202418 6096707 := bstep (se 1 (by rfl) ⟨4572530, by rfl⟩ : syracuseStep 6096707 = 9145061) B9145061
theorem B3852127 : Blo 1202418 3852127 := bstep (se 1 (by rfl) ⟨2889095, by rfl⟩ : syracuseStep 3852127 = 5778191) B5778191
theorem B1804127 : Blo 1202418 1804127 := bstep (se 1 (by rfl) ⟨1353095, by rfl⟩ : syracuseStep 1804127 = 2706191) B2706191
theorem B1804139 : Blo 1202418 1804139 := bstep (se 1 (by rfl) ⟨1353104, by rfl⟩ : syracuseStep 1804139 = 2706209) B2706209
theorem B3426209 : Blo 1202418 3426209 := bstep (se 2 (by rfl) ⟨1284828, by rfl⟩ : syracuseStep 3426209 = 2569657) B2569657
theorem B13715405 : Blo 1202418 13715405 := bstep (se 3 (by rfl) ⟨2571638, by rfl⟩ : syracuseStep 13715405 = 5143277) B5143277
theorem B1804367 : Blo 1202418 1804367 := bstep (se 1 (by rfl) ⟨1353275, by rfl⟩ : syracuseStep 1804367 = 2706551) B2706551
theorem B9259123 : Blo 1202418 9259123 := bstep (se 1 (by rfl) ⟨6944342, by rfl⟩ : syracuseStep 9259123 = 13888685) B13888685
theorem B2705579 : Blo 1202418 2705579 := bstep (se 1 (by rfl) ⟨2029184, by rfl⟩ : syracuseStep 2705579 = 4058369) B4058369
theorem B1804487 : Blo 1202418 1804487 := bstep (se 1 (by rfl) ⟨1353365, by rfl⟩ : syracuseStep 1804487 = 2706731) B2706731
theorem B1714375 : Blo 1202418 1714375 := bstep (se 1 (by rfl) ⟨1285781, by rfl⟩ : syracuseStep 1714375 = 2571563) B2571563
theorem B1804649 : Blo 1202418 1804649 := bstep (se 2 (by rfl) ⟨676743, by rfl⟩ : syracuseStep 1804649 = 1353487) B1353487
theorem B1804727 : Blo 1202418 1804727 := bstep (se 1 (by rfl) ⟨1353545, by rfl⟩ : syracuseStep 1804727 = 2707091) B2707091
theorem B1804763 : Blo 1202418 1804763 := bstep (se 1 (by rfl) ⟨1353572, by rfl⟩ : syracuseStep 1804763 = 2707145) B2707145
theorem B3426779 : Blo 1202418 3426779 := bstep (se 1 (by rfl) ⟨2570084, by rfl⟩ : syracuseStep 3426779 = 5140169) B5140169
theorem B1354279 : Blo 1202418 1354279 := bstep (se 1 (by rfl) ⟨1015709, by rfl⟩ : syracuseStep 1354279 = 2031419) B2031419
theorem B9259705 : Blo 1202418 9259705 := bstep (se 2 (by rfl) ⟨3472389, by rfl⟩ : syracuseStep 9259705 = 6944779) B6944779
theorem B2706119 : Blo 1202418 2706119 := bstep (se 1 (by rfl) ⟨2029589, by rfl⟩ : syracuseStep 2706119 = 4059179) B4059179
theorem B6089579 : Blo 1202418 6089579 := bstep (se 1 (by rfl) ⟨4567184, by rfl⟩ : syracuseStep 6089579 = 9134369) B9134369
theorem B4565879 : Blo 1202418 4565879 := bstep (se 1 (by rfl) ⟨3424409, by rfl⟩ : syracuseStep 4565879 = 6848819) B6848819
theorem B1805231 : Blo 1202418 1805231 := bstep (se 1 (by rfl) ⟨1353923, by rfl⟩ : syracuseStep 1805231 = 2707847) B2707847
theorem B3435527 : Blo 1202418 3435527 := bstep (se 1 (by rfl) ⟨2576645, by rfl⟩ : syracuseStep 3435527 = 5153291) B5153291
theorem B1805321 : Blo 1202418 1805321 := bstep (se 2 (by rfl) ⟨676995, by rfl⟩ : syracuseStep 1805321 = 1353991) B1353991
theorem B1805351 : Blo 1202418 1805351 := bstep (se 1 (by rfl) ⟨1354013, by rfl⟩ : syracuseStep 1805351 = 2708027) B2708027
theorem B1805435 : Blo 1202418 1805435 := bstep (se 1 (by rfl) ⟨1354076, by rfl⟩ : syracuseStep 1805435 = 2708153) B2708153
theorem B6180035 : Blo 1202418 6180035 := bstep (se 1 (by rfl) ⟨4635026, by rfl⟩ : syracuseStep 6180035 = 9270053) B9270053
theorem B9145547 : Blo 1202418 9145547 := bstep (se 1 (by rfl) ⟨6859160, by rfl⟩ : syracuseStep 9145547 = 13718321) B13718321
theorem B1805561 : Blo 1202418 1805561 := bstep (se 2 (by rfl) ⟨677085, by rfl⟩ : syracuseStep 1805561 = 1354171) B1354171
theorem B1805663 : Blo 1202418 1805663 := bstep (se 1 (by rfl) ⟨1354247, by rfl⟩ : syracuseStep 1805663 = 2708495) B2708495
theorem B1805675 : Blo 1202418 1805675 := bstep (se 1 (by rfl) ⟨1354256, by rfl⟩ : syracuseStep 1805675 = 2708513) B2708513
theorem B6090227 : Blo 1202418 6090227 := bstep (se 1 (by rfl) ⟨4567670, by rfl⟩ : syracuseStep 6090227 = 9135341) B9135341
theorem B3427849 : Blo 1202418 3427849 := bstep (se 2 (by rfl) ⟨1285443, by rfl⟩ : syracuseStep 3427849 = 2570887) B2570887
theorem B2706983 : Blo 1202418 2706983 := bstep (se 1 (by rfl) ⟨2030237, by rfl⟩ : syracuseStep 2706983 = 4060475) B4060475
theorem B1805903 : Blo 1202418 1805903 := bstep (se 1 (by rfl) ⟨1354427, by rfl⟩ : syracuseStep 1805903 = 2708855) B2708855
theorem B4058747 : Blo 1202418 4058747 := bstep (se 1 (by rfl) ⟨3044060, by rfl⟩ : syracuseStep 4058747 = 6088121) B6088121
theorem B6852235 : Blo 1202418 6852235 := bstep (se 1 (by rfl) ⟨5139176, by rfl⟩ : syracuseStep 6852235 = 10278353) B10278353
theorem B19787453 : Blo 1202418 19787453 := bstep (se 3 (by rfl) ⟨3710147, by rfl⟩ : syracuseStep 19787453 = 7420295) B7420295
theorem B1806023 : Blo 1202418 1806023 := bstep (se 1 (by rfl) ⟨1354517, by rfl⟩ : syracuseStep 1806023 = 2709035) B2709035
theorem B4058909 : Blo 1202418 4058909 := bstep (se 3 (by rfl) ⟨761045, by rfl⟩ : syracuseStep 4058909 = 1522091) B1522091
theorem B4566851 : Blo 1202418 4566851 := bstep (se 1 (by rfl) ⟨3425138, by rfl⟩ : syracuseStep 4566851 = 6850277) B6850277
theorem B1806185 : Blo 1202418 1806185 := bstep (se 2 (by rfl) ⟨677319, by rfl⟩ : syracuseStep 1806185 = 1354639) B1354639
theorem B2707307 : Blo 1202418 2707307 := bstep (se 1 (by rfl) ⟨2030480, by rfl⟩ : syracuseStep 2707307 = 4060961) B4060961
theorem B3428203 : Blo 1202418 3428203 := bstep (se 1 (by rfl) ⟨2571152, by rfl⟩ : syracuseStep 3428203 = 5142305) B5142305
theorem B2707361 : Blo 1202418 2707361 := bstep (se 2 (by rfl) ⟨1015260, by rfl⟩ : syracuseStep 2707361 = 2030521) B2030521
theorem B5861281 : Blo 1202418 5861281 := bstep (se 2 (by rfl) ⟨2197980, by rfl⟩ : syracuseStep 5861281 = 4395961) B4395961
theorem B1806263 : Blo 1202418 1806263 := bstep (se 1 (by rfl) ⟨1354697, by rfl⟩ : syracuseStep 1806263 = 2709395) B2709395
theorem B16461755 : Blo 1202418 16461755 := bstep (se 1 (by rfl) ⟨12346316, by rfl⟩ : syracuseStep 16461755 = 24692633) B24692633
theorem B1806299 : Blo 1202418 1806299 := bstep (se 1 (by rfl) ⟨1354724, by rfl⟩ : syracuseStep 1806299 = 2709449) B2709449
theorem B5214215 : Blo 1202418 5214215 := bstep (se 1 (by rfl) ⟨3910661, by rfl⟩ : syracuseStep 5214215 = 7821323) B7821323
theorem B1626151 : Blo 1202418 1626151 := bstep (se 1 (by rfl) ⟨1219613, by rfl⟩ : syracuseStep 1626151 = 2439227) B2439227
theorem B1855567 : Blo 1202418 1855567 := bstep (se 1 (by rfl) ⟨1391675, by rfl⟩ : syracuseStep 1855567 = 2783351) B2783351
theorem B9138257 : Blo 1202418 9138257 := bstep (se 2 (by rfl) ⟨3426846, by rfl⟩ : syracuseStep 9138257 = 6853693) B6853693
theorem B7704665 : Blo 1202418 7704665 := bstep (se 2 (by rfl) ⟨2889249, by rfl⟩ : syracuseStep 7704665 = 5778499) B5778499
theorem B2707703 : Blo 1202418 2707703 := bstep (se 1 (by rfl) ⟨2030777, by rfl⟩ : syracuseStep 2707703 = 4061555) B4061555
theorem B4337911 : Blo 1202418 4337911 := bstep (se 1 (by rfl) ⟨3253433, by rfl⟩ : syracuseStep 4337911 = 6506867) B6506867
theorem B3043727 : Blo 1202418 3043727 := bstep (se 1 (by rfl) ⟨2282795, by rfl⟩ : syracuseStep 3043727 = 4565591) B4565591
theorem B4059611 : Blo 1202418 4059611 := bstep (se 1 (by rfl) ⟨3044708, by rfl⟩ : syracuseStep 4059611 = 6089417) B6089417
theorem B4117025 : Blo 1202418 4117025 := bstep (se 2 (by rfl) ⟨1543884, by rfl⟩ : syracuseStep 4117025 = 3087769) B3087769
theorem B7713481 : Blo 1202418 7713481 := bstep (se 2 (by rfl) ⟨2892555, by rfl⟩ : syracuseStep 7713481 = 5785111) B5785111
theorem B13005521 : Blo 1202418 13005521 := bstep (se 2 (by rfl) ⟨4877070, by rfl⟩ : syracuseStep 13005521 = 9754141) B9754141
theorem B3044051 : Blo 1202418 3044051 := bstep (se 1 (by rfl) ⟨2283038, by rfl⟩ : syracuseStep 3044051 = 4566077) B4566077
theorem B6091523 : Blo 1202418 6091523 := bstep (se 1 (by rfl) ⟨4568642, by rfl⟩ : syracuseStep 6091523 = 9137285) B9137285
theorem B2708297 : Blo 1202418 2708297 := bstep (se 2 (by rfl) ⟨1015611, by rfl⟩ : syracuseStep 2708297 = 2031223) B2031223
theorem B2167739 : Blo 1202418 2167739 := bstep (se 1 (by rfl) ⟨1625804, by rfl⟩ : syracuseStep 2167739 = 3251609) B3251609
theorem B3429307 : Blo 1202418 3429307 := bstep (se 1 (by rfl) ⟨2571980, by rfl⟩ : syracuseStep 3429307 = 5143961) B5143961
theorem B8795101 : Blo 1202418 8795101 := bstep (se 3 (by rfl) ⟨1649081, by rfl⟩ : syracuseStep 8795101 = 3298163) B3298163
theorem B4060313 : Blo 1202418 4060313 := bstep (se 2 (by rfl) ⟨1522617, by rfl⟩ : syracuseStep 4060313 = 3045235) B3045235
theorem B5780651 : Blo 1202418 5780651 := bstep (se 1 (by rfl) ⟨4335488, by rfl⟩ : syracuseStep 5780651 = 8670977) B8670977
theorem B7705793 : Blo 1202418 7705793 := bstep (se 2 (by rfl) ⟨2889672, by rfl⟩ : syracuseStep 7705793 = 5779345) B5779345
theorem B10286351 : Blo 1202418 10286351 := bstep (se 1 (by rfl) ⟨7714763, by rfl⟩ : syracuseStep 10286351 = 15429527) B15429527
theorem B4568521 : Blo 1202418 4568521 := bstep (se 2 (by rfl) ⟨1713195, by rfl⟩ : syracuseStep 4568521 = 3426391) B3426391
theorem B2569691 : Blo 1202418 2569691 := bstep (se 1 (by rfl) ⟨1927268, by rfl⟩ : syracuseStep 2569691 = 3854537) B3854537
theorem B2709089 : Blo 1202418 2709089 := bstep (se 2 (by rfl) ⟨1015908, by rfl⟩ : syracuseStep 2709089 = 2031817) B2031817
theorem B8230547 : Blo 1202418 8230547 := bstep (se 1 (by rfl) ⟨6172910, by rfl⟩ : syracuseStep 8230547 = 12345821) B12345821
theorem B4568825 : Blo 1202418 4568825 := bstep (se 2 (by rfl) ⟨1713309, by rfl⟩ : syracuseStep 4568825 = 3426619) B3426619
theorem B3045215 : Blo 1202418 3045215 := bstep (se 1 (by rfl) ⟨2283911, by rfl⟩ : syracuseStep 3045215 = 4567823) B4567823
theorem B3708767 : Blo 1202418 3708767 := bstep (se 1 (by rfl) ⟨2781575, by rfl⟩ : syracuseStep 3708767 = 5563151) B5563151
theorem B4568993 : Blo 1202418 4568993 := bstep (se 2 (by rfl) ⟨1713372, by rfl⟩ : syracuseStep 4568993 = 3426745) B3426745
theorem B4569007 : Blo 1202418 4569007 := bstep (se 1 (by rfl) ⟨3426755, by rfl⟩ : syracuseStep 4569007 = 6853511) B6853511
theorem B2029495 : Blo 1202418 2029495 := bstep (se 1 (by rfl) ⟨1522121, by rfl⟩ : syracuseStep 2029495 = 3044243) B3044243
theorem B2709431 : Blo 1202418 2709431 := bstep (se 1 (by rfl) ⟨2032073, by rfl⟩ : syracuseStep 2709431 = 4064147) B4064147
theorem B11564993 : Blo 1202418 11564993 := bstep (se 2 (by rfl) ⟨4336872, by rfl⟩ : syracuseStep 11564993 = 8673745) B8673745
theorem B7313465 : Blo 1202418 7313465 := bstep (se 2 (by rfl) ⟨2742549, by rfl⟩ : syracuseStep 7313465 = 5485099) B5485099
theorem B6502457 : Blo 1202418 6502457 := bstep (se 2 (by rfl) ⟨2438421, by rfl⟩ : syracuseStep 6502457 = 4876843) B4876843
theorem B37140569 : Blo 1202418 37140569 := bstep (se 2 (by rfl) ⟨13927713, by rfl⟩ : syracuseStep 37140569 = 27855427) B27855427
theorem B2029691 : Blo 1202418 2029691 := bstep (se 1 (by rfl) ⟨1522268, by rfl⟩ : syracuseStep 2029691 = 3044537) B3044537
theorem B1202471 : Blo 1202418 1202471 := bstep (se 1 (by rfl) ⟨901853, by rfl⟩ : syracuseStep 1202471 = 1803707) B1803707
theorem B4061501 : Blo 1202418 4061501 := bstep (se 3 (by rfl) ⟨761531, by rfl⟩ : syracuseStep 4061501 = 1523063) B1523063
theorem B1202511 : Blo 1202418 1202511 := bstep (se 1 (by rfl) ⟨901883, by rfl⟩ : syracuseStep 1202511 = 1803767) B1803767
theorem B6093143 : Blo 1202418 6093143 := bstep (se 1 (by rfl) ⟨4569857, by rfl⟩ : syracuseStep 6093143 = 9139715) B9139715
theorem B1202527 : Blo 1202418 1202527 := bstep (se 1 (by rfl) ⟨901895, by rfl⟩ : syracuseStep 1202527 = 1803791) B1803791
theorem B1202555 : Blo 1202418 1202555 := bstep (se 1 (by rfl) ⟨901916, by rfl⟩ : syracuseStep 1202555 = 1803833) B1803833
theorem B7813529 : Blo 1202418 7813529 := bstep (se 2 (by rfl) ⟨2930073, by rfl⟩ : syracuseStep 7813529 = 5860147) B5860147
theorem B1202607 : Blo 1202418 1202607 := bstep (se 1 (by rfl) ⟨901955, by rfl⟩ : syracuseStep 1202607 = 1803911) B1803911
theorem B1202631 : Blo 1202418 1202631 := bstep (se 1 (by rfl) ⟨901973, by rfl⟩ : syracuseStep 1202631 = 1803947) B1803947
theorem B1202651 : Blo 1202418 1202651 := bstep (se 1 (by rfl) ⟨901988, by rfl⟩ : syracuseStep 1202651 = 1803977) B1803977
theorem B2030089 : Blo 1202418 2030089 := bstep (se 2 (by rfl) ⟨761283, by rfl⟩ : syracuseStep 2030089 = 1522567) B1522567
theorem B1202727 : Blo 1202418 1202727 := bstep (se 1 (by rfl) ⟨902045, by rfl⟩ : syracuseStep 1202727 = 1804091) B1804091
theorem B1202767 : Blo 1202418 1202767 := bstep (se 1 (by rfl) ⟨902075, by rfl⟩ : syracuseStep 1202767 = 1804151) B1804151
theorem B1202783 : Blo 1202418 1202783 := bstep (se 1 (by rfl) ⟨902087, by rfl⟩ : syracuseStep 1202783 = 1804175) B1804175
theorem B1202811 : Blo 1202418 1202811 := bstep (se 1 (by rfl) ⟨902108, by rfl⟩ : syracuseStep 1202811 = 1804217) B1804217
theorem B2030251 : Blo 1202418 2030251 := bstep (se 1 (by rfl) ⟨1522688, by rfl⟩ : syracuseStep 2030251 = 3045377) B3045377
theorem B1202863 : Blo 1202418 1202863 := bstep (se 1 (by rfl) ⟨902147, by rfl⟩ : syracuseStep 1202863 = 1804295) B1804295
theorem B1202887 : Blo 1202418 1202887 := bstep (se 1 (by rfl) ⟨902165, by rfl⟩ : syracuseStep 1202887 = 1804331) B1804331
theorem B1202907 : Blo 1202418 1202907 := bstep (se 1 (by rfl) ⟨902180, by rfl⟩ : syracuseStep 1202907 = 1804361) B1804361
theorem B30849821 : Blo 1202418 30849821 := bstep (se 3 (by rfl) ⟨5784341, by rfl⟩ : syracuseStep 30849821 = 11568683) B11568683
theorem B1202983 : Blo 1202418 1202983 := bstep (se 1 (by rfl) ⟨902237, by rfl⟩ : syracuseStep 1202983 = 1804475) B1804475
theorem B1203023 : Blo 1202418 1203023 := bstep (se 1 (by rfl) ⟨902267, by rfl⟩ : syracuseStep 1203023 = 1804535) B1804535
theorem B1203039 : Blo 1202418 1203039 := bstep (se 1 (by rfl) ⟨902279, by rfl⟩ : syracuseStep 1203039 = 1804559) B1804559
theorem B4569965 : Blo 1202418 4569965 := bstep (se 3 (by rfl) ⟨856868, by rfl⟩ : syracuseStep 4569965 = 1713737) B1713737
theorem B1203067 : Blo 1202418 1203067 := bstep (se 1 (by rfl) ⟨902300, by rfl⟩ : syracuseStep 1203067 = 1804601) B1804601
theorem B1203119 : Blo 1202418 1203119 := bstep (se 1 (by rfl) ⟨902339, by rfl⟩ : syracuseStep 1203119 = 1804679) B1804679
theorem B3046319 : Blo 1202418 3046319 := bstep (se 1 (by rfl) ⟨2284739, by rfl⟩ : syracuseStep 3046319 = 4569479) B4569479
theorem B1956791 : Blo 1202418 1956791 := bstep (se 1 (by rfl) ⟨1467593, by rfl⟩ : syracuseStep 1956791 = 2935187) B2935187
theorem B1203143 : Blo 1202418 1203143 := bstep (se 1 (by rfl) ⟨902357, by rfl⟩ : syracuseStep 1203143 = 1804715) B1804715
theorem B1203163 : Blo 1202418 1203163 := bstep (se 1 (by rfl) ⟨902372, by rfl⟩ : syracuseStep 1203163 = 1804745) B1804745
theorem B2030555 : Blo 1202418 2030555 := bstep (se 1 (by rfl) ⟨1522916, by rfl⟩ : syracuseStep 2030555 = 3045833) B3045833
theorem B1203239 : Blo 1202418 1203239 := bstep (se 1 (by rfl) ⟨902429, by rfl⟩ : syracuseStep 1203239 = 1804859) B1804859
theorem B1203279 : Blo 1202418 1203279 := bstep (se 1 (by rfl) ⟨902459, by rfl⟩ : syracuseStep 1203279 = 1804919) B1804919
theorem B1203295 : Blo 1202418 1203295 := bstep (se 1 (by rfl) ⟨902471, by rfl⟩ : syracuseStep 1203295 = 1804943) B1804943
theorem B1203323 : Blo 1202418 1203323 := bstep (se 1 (by rfl) ⟨902492, by rfl⟩ : syracuseStep 1203323 = 1804985) B1804985
theorem B3857561 : Blo 1202418 3857561 := bstep (se 2 (by rfl) ⟨1446585, by rfl⟩ : syracuseStep 3857561 = 2893171) B2893171
theorem B4062365 : Blo 1202418 4062365 := bstep (se 3 (by rfl) ⟨761693, by rfl⟩ : syracuseStep 4062365 = 1523387) B1523387
theorem B4570283 : Blo 1202418 4570283 := bstep (se 1 (by rfl) ⟨3427712, by rfl⟩ : syracuseStep 4570283 = 6855425) B6855425
theorem B17341613 : Blo 1202418 17341613 := bstep (se 3 (by rfl) ⟨3251552, by rfl⟩ : syracuseStep 17341613 = 6503105) B6503105
theorem B1203375 : Blo 1202418 1203375 := bstep (se 1 (by rfl) ⟨902531, by rfl⟩ : syracuseStep 1203375 = 1805063) B1805063
theorem B1203399 : Blo 1202418 1203399 := bstep (se 1 (by rfl) ⟨902549, by rfl⟩ : syracuseStep 1203399 = 1805099) B1805099
theorem B2030791 : Blo 1202418 2030791 := bstep (se 1 (by rfl) ⟨1523093, by rfl⟩ : syracuseStep 2030791 = 3046187) B3046187
theorem B1203419 : Blo 1202418 1203419 := bstep (se 1 (by rfl) ⟨902564, by rfl⟩ : syracuseStep 1203419 = 1805129) B1805129
theorem B15834359 : Blo 1202418 15834359 := bstep (se 1 (by rfl) ⟨11875769, by rfl⟩ : syracuseStep 15834359 = 23751539) B23751539
theorem B1203495 : Blo 1202418 1203495 := bstep (se 1 (by rfl) ⟨902621, by rfl⟩ : syracuseStep 1203495 = 1805243) B1805243
theorem B1203535 : Blo 1202418 1203535 := bstep (se 1 (by rfl) ⟨902651, by rfl⟩ : syracuseStep 1203535 = 1805303) B1805303
theorem B1203551 : Blo 1202418 1203551 := bstep (se 1 (by rfl) ⟨902663, by rfl⟩ : syracuseStep 1203551 = 1805327) B1805327
theorem B2030953 : Blo 1202418 2030953 := bstep (se 2 (by rfl) ⟨761607, by rfl⟩ : syracuseStep 2030953 = 1523215) B1523215
theorem B1203579 : Blo 1202418 1203579 := bstep (se 1 (by rfl) ⟨902684, by rfl⟩ : syracuseStep 1203579 = 1805369) B1805369
theorem B6856109 : Blo 1202418 6856109 := bstep (se 3 (by rfl) ⟨1285520, by rfl⟩ : syracuseStep 6856109 = 2571041) B2571041
theorem B1523119 : Blo 1202418 1523119 := bstep (se 1 (by rfl) ⟨1142339, by rfl⟩ : syracuseStep 1523119 = 2284679) B2284679
theorem B1203631 : Blo 1202418 1203631 := bstep (se 1 (by rfl) ⟨902723, by rfl⟩ : syracuseStep 1203631 = 1805447) B1805447
theorem B1203655 : Blo 1202418 1203655 := bstep (se 1 (by rfl) ⟨902741, by rfl⟩ : syracuseStep 1203655 = 1805483) B1805483
theorem B1203675 : Blo 1202418 1203675 := bstep (se 1 (by rfl) ⟨902756, by rfl⟩ : syracuseStep 1203675 = 1805513) B1805513
theorem B1203751 : Blo 1202418 1203751 := bstep (se 1 (by rfl) ⟨902813, by rfl⟩ : syracuseStep 1203751 = 1805627) B1805627
theorem B3857959 : Blo 1202418 3857959 := bstep (se 1 (by rfl) ⟨2893469, by rfl⟩ : syracuseStep 3857959 = 5786939) B5786939
theorem B1392167 : Blo 1202418 1392167 := bstep (se 1 (by rfl) ⟨1044125, by rfl⟩ : syracuseStep 1392167 = 2088251) B2088251
theorem B1203791 : Blo 1202418 1203791 := bstep (se 1 (by rfl) ⟨902843, by rfl⟩ : syracuseStep 1203791 = 1805687) B1805687
theorem B2440783 : Blo 1202418 2440783 := bstep (se 1 (by rfl) ⟨1830587, by rfl⟩ : syracuseStep 2440783 = 3661175) B3661175
theorem B8347223 : Blo 1202418 8347223 := bstep (se 1 (by rfl) ⟨6260417, by rfl⟩ : syracuseStep 8347223 = 12520835) B12520835
theorem B1203807 : Blo 1202418 1203807 := bstep (se 1 (by rfl) ⟨902855, by rfl⟩ : syracuseStep 1203807 = 1805711) B1805711
theorem B1203835 : Blo 1202418 1203835 := bstep (se 1 (by rfl) ⟨902876, by rfl⟩ : syracuseStep 1203835 = 1805753) B1805753
theorem B1203887 : Blo 1202418 1203887 := bstep (se 1 (by rfl) ⟨902915, by rfl⟩ : syracuseStep 1203887 = 1805831) B1805831
theorem B4062905 : Blo 1202418 4062905 := bstep (se 2 (by rfl) ⟨1523589, by rfl⟩ : syracuseStep 4062905 = 3047179) B3047179
theorem B4947655 : Blo 1202418 4947655 := bstep (se 1 (by rfl) ⟨3710741, by rfl⟩ : syracuseStep 4947655 = 7421483) B7421483
theorem B1203911 : Blo 1202418 1203911 := bstep (se 1 (by rfl) ⟨902933, by rfl⟩ : syracuseStep 1203911 = 1805867) B1805867
theorem B2678483 : Blo 1202418 2678483 := bstep (se 1 (by rfl) ⟨2008862, by rfl⟩ : syracuseStep 2678483 = 4017725) B4017725
theorem B1203931 : Blo 1202418 1203931 := bstep (se 1 (by rfl) ⟨902948, by rfl⟩ : syracuseStep 1203931 = 1805897) B1805897
theorem B1204007 : Blo 1202418 1204007 := bstep (se 1 (by rfl) ⟨903005, by rfl⟩ : syracuseStep 1204007 = 1806011) B1806011
theorem B9133883 : Blo 1202418 9133883 := bstep (se 1 (by rfl) ⟨6850412, by rfl⟩ : syracuseStep 9133883 = 13700825) B13700825
theorem B1204047 : Blo 1202418 1204047 := bstep (se 1 (by rfl) ⟨903035, by rfl⟩ : syracuseStep 1204047 = 1806071) B1806071
theorem B1204063 : Blo 1202418 1204063 := bstep (se 1 (by rfl) ⟨903047, by rfl⟩ : syracuseStep 1204063 = 1806095) B1806095
theorem B23117683 : Blo 1202418 23117683 := bstep (se 1 (by rfl) ⟨17338262, by rfl⟩ : syracuseStep 23117683 = 34676525) B34676525
theorem B10289015 : Blo 1202418 10289015 := bstep (se 1 (by rfl) ⟨7716761, by rfl⟩ : syracuseStep 10289015 = 15433523) B15433523
theorem B1204091 : Blo 1202418 1204091 := bstep (se 1 (by rfl) ⟨903068, by rfl⟩ : syracuseStep 1204091 = 1806137) B1806137
theorem B6856609 : Blo 1202418 6856609 := bstep (se 2 (by rfl) ⟨2571228, by rfl⟩ : syracuseStep 6856609 = 5142457) B5142457
theorem B1204143 : Blo 1202418 1204143 := bstep (se 1 (by rfl) ⟨903107, by rfl⟩ : syracuseStep 1204143 = 1806215) B1806215
theorem B2031547 : Blo 1202418 2031547 := bstep (se 1 (by rfl) ⟨1523660, by rfl⟩ : syracuseStep 2031547 = 3047321) B3047321
theorem B1204167 : Blo 1202418 1204167 := bstep (se 1 (by rfl) ⟨903125, by rfl⟩ : syracuseStep 1204167 = 1806251) B1806251
theorem B1204187 : Blo 1202418 1204187 := bstep (se 1 (by rfl) ⟨903140, by rfl⟩ : syracuseStep 1204187 = 1806281) B1806281
theorem B12353543 : Blo 1202418 12353543 := bstep (se 1 (by rfl) ⟨9265157, by rfl⟩ : syracuseStep 12353543 = 18530315) B18530315
theorem B5136443 : Blo 1202418 5136443 := bstep (se 1 (by rfl) ⟨3852332, by rfl⟩ : syracuseStep 5136443 = 7704665) B7704665
theorem B4063337 : Blo 1202418 4063337 := bstep (se 2 (by rfl) ⟨1523751, by rfl⟩ : syracuseStep 4063337 = 3047503) B3047503
theorem B12345497 : Blo 1202418 12345497 := bstep (se 2 (by rfl) ⟨4629561, by rfl⟩ : syracuseStep 12345497 = 9259123) B9259123
theorem B2285833 : Blo 1202418 2285833 := bstep (se 2 (by rfl) ⟨857187, by rfl⟩ : syracuseStep 2285833 = 1714375) B1714375
theorem B5783881 : Blo 1202418 5783881 := bstep (se 2 (by rfl) ⟨2168955, by rfl⟩ : syracuseStep 5783881 = 4337911) B4337911
theorem B1524091 : Blo 1202418 1524091 := bstep (se 1 (by rfl) ⟨1143068, by rfl⟩ : syracuseStep 1524091 = 2286137) B2286137
theorem B9896357 : Blo 1202418 9896357 := bstep (se 4 (by rfl) ⟨927783, by rfl⟩ : syracuseStep 9896357 = 1855567) B1855567
theorem B6095411 : Blo 1202418 6095411 := bstep (se 1 (by rfl) ⟨4571558, by rfl⟩ : syracuseStep 6095411 = 9143117) B9143117
theorem B2032249 : Blo 1202418 2032249 := bstep (se 2 (by rfl) ⟨762093, by rfl⟩ : syracuseStep 2032249 = 1524187) B1524187
theorem B2032303 : Blo 1202418 2032303 := bstep (se 1 (by rfl) ⟨1524227, by rfl⟩ : syracuseStep 2032303 = 3048455) B3048455
theorem B5137195 : Blo 1202418 5137195 := bstep (se 1 (by rfl) ⟨3852896, by rfl⟩ : syracuseStep 5137195 = 7705793) B7705793
theorem B6857567 : Blo 1202418 6857567 := bstep (se 1 (by rfl) ⟨5143175, by rfl⟩ : syracuseStep 6857567 = 10286351) B10286351
theorem B2196379 : Blo 1202418 2196379 := bstep (se 1 (by rfl) ⟨1647284, by rfl⟩ : syracuseStep 2196379 = 3294569) B3294569
theorem B12346273 : Blo 1202418 12346273 := bstep (se 2 (by rfl) ⟨4629852, by rfl⟩ : syracuseStep 12346273 = 9259705) B9259705
theorem B4064201 : Blo 1202418 4064201 := bstep (se 2 (by rfl) ⟨1524075, by rfl⟩ : syracuseStep 4064201 = 3048151) B3048151
theorem B3048587 : Blo 1202418 3048587 := bstep (se 1 (by rfl) ⟨2286440, by rfl⟩ : syracuseStep 3048587 = 4572881) B4572881
theorem B4064471 : Blo 1202418 4064471 := bstep (se 1 (by rfl) ⟨3048353, by rfl⟩ : syracuseStep 4064471 = 6096707) B6096707
theorem B4572409 : Blo 1202418 4572409 := bstep (se 2 (by rfl) ⟨1714653, by rfl⟩ : syracuseStep 4572409 = 3429307) B3429307
theorem B7709995 : Blo 1202418 7709995 := bstep (se 1 (by rfl) ⟨5782496, by rfl⟩ : syracuseStep 7709995 = 11564993) B11564993
theorem B9143603 : Blo 1202418 9143603 := bstep (se 1 (by rfl) ⟨6857702, by rfl⟩ : syracuseStep 9143603 = 13715405) B13715405
theorem B4875643 : Blo 1202418 4875643 := bstep (se 1 (by rfl) ⟨3656732, by rfl⟩ : syracuseStep 4875643 = 7313465) B7313465
theorem B4334971 : Blo 1202418 4334971 := bstep (se 1 (by rfl) ⟨3251228, by rfl⟩ : syracuseStep 4334971 = 6502457) B6502457
theorem B1353127 : Blo 1202418 1353127 := bstep (se 1 (by rfl) ⟨1014845, by rfl⟩ : syracuseStep 1353127 = 2029691) B2029691
theorem B10978733 : Blo 1202418 10978733 := bstep (se 3 (by rfl) ⟨2058512, by rfl⟩ : syracuseStep 10978733 = 4117025) B4117025
theorem B3712445 : Blo 1202418 3712445 := bstep (se 3 (by rfl) ⟨696083, by rfl⟩ : syracuseStep 3712445 = 1392167) B1392167
theorem B1803719 : Blo 1202418 1803719 := bstep (se 1 (by rfl) ⟨1352789, by rfl⟩ : syracuseStep 1803719 = 2705579) B2705579
theorem B22259261 : Blo 1202418 22259261 := bstep (se 3 (by rfl) ⟨4173611, by rfl⟩ : syracuseStep 22259261 = 8347223) B8347223
theorem B1804073 : Blo 1202418 1804073 := bstep (se 2 (by rfl) ⟨676527, by rfl⟩ : syracuseStep 1804073 = 1353055) B1353055
theorem B1804079 : Blo 1202418 1804079 := bstep (se 1 (by rfl) ⟨1353059, by rfl⟩ : syracuseStep 1804079 = 2706119) B2706119
theorem B1304527 : Blo 1202418 1304527 := bstep (se 1 (by rfl) ⟨978395, by rfl⟩ : syracuseStep 1304527 = 1956791) B1956791
theorem B1353703 : Blo 1202418 1353703 := bstep (se 1 (by rfl) ⟨1015277, by rfl⟩ : syracuseStep 1353703 = 2030555) B2030555
theorem B3254377 : Blo 1202418 3254377 := bstep (se 2 (by rfl) ⟨1220391, by rfl⟩ : syracuseStep 3254377 = 2440783) B2440783
theorem B11561075 : Blo 1202418 11561075 := bstep (se 1 (by rfl) ⟨8670806, by rfl⟩ : syracuseStep 11561075 = 17341613) B17341613
theorem B6097031 : Blo 1202418 6097031 := bstep (se 1 (by rfl) ⟨4572773, by rfl⟩ : syracuseStep 6097031 = 9145547) B9145547
theorem B9136313 : Blo 1202418 9136313 := bstep (se 2 (by rfl) ⟨3426117, by rfl⟩ : syracuseStep 9136313 = 6852235) B6852235
theorem B9890045 : Blo 1202418 9890045 := bstep (se 3 (by rfl) ⟨1854383, by rfl⟩ : syracuseStep 9890045 = 3708767) B3708767
theorem B1804553 : Blo 1202418 1804553 := bstep (se 2 (by rfl) ⟨676707, by rfl⟩ : syracuseStep 1804553 = 1353415) B1353415
theorem B6596873 : Blo 1202418 6596873 := bstep (se 2 (by rfl) ⟨2473827, by rfl⟩ : syracuseStep 6596873 = 4947655) B4947655
theorem B1804655 : Blo 1202418 1804655 := bstep (se 1 (by rfl) ⟨1353491, by rfl⟩ : syracuseStep 1804655 = 2706983) B2706983
theorem B2705831 : Blo 1202418 2705831 := bstep (se 1 (by rfl) ⟨2029373, by rfl⟩ : syracuseStep 2705831 = 4058747) B4058747
theorem B13191635 : Blo 1202418 13191635 := bstep (se 1 (by rfl) ⟨9893726, by rfl⟩ : syracuseStep 13191635 = 19787453) B19787453
theorem B2705939 : Blo 1202418 2705939 := bstep (se 1 (by rfl) ⟨2029454, by rfl⟩ : syracuseStep 2705939 = 4058909) B4058909
theorem B6089255 : Blo 1202418 6089255 := bstep (se 1 (by rfl) ⟨4566941, by rfl⟩ : syracuseStep 6089255 = 9133883) B9133883
theorem B1804871 : Blo 1202418 1804871 := bstep (se 1 (by rfl) ⟨1353653, by rfl⟩ : syracuseStep 1804871 = 2707307) B2707307
theorem B2705993 : Blo 1202418 2705993 := bstep (se 2 (by rfl) ⟨1014747, by rfl⟩ : syracuseStep 2705993 = 2029495) B2029495
theorem B6859343 : Blo 1202418 6859343 := bstep (se 1 (by rfl) ⟨5144507, by rfl⟩ : syracuseStep 6859343 = 10289015) B10289015
theorem B1804907 : Blo 1202418 1804907 := bstep (se 1 (by rfl) ⟨1353680, by rfl⟩ : syracuseStep 1804907 = 2707361) B2707361
theorem B3476143 : Blo 1202418 3476143 := bstep (se 1 (by rfl) ⟨2607107, by rfl⟩ : syracuseStep 3476143 = 5214215) B5214215
theorem B1805135 : Blo 1202418 1805135 := bstep (se 1 (by rfl) ⟨1353851, by rfl⟩ : syracuseStep 1805135 = 2707703) B2707703
theorem B2706407 : Blo 1202418 2706407 := bstep (se 1 (by rfl) ⟨2029805, by rfl⟩ : syracuseStep 2706407 = 4059611) B4059611
theorem B5139571 : Blo 1202418 5139571 := bstep (se 1 (by rfl) ⟨3854678, by rfl⟩ : syracuseStep 5139571 = 7709357) B7709357
theorem B8670347 : Blo 1202418 8670347 := bstep (se 1 (by rfl) ⟨6502760, by rfl⟩ : syracuseStep 8670347 = 13005521) B13005521
theorem B1805531 : Blo 1202418 1805531 := bstep (se 1 (by rfl) ⟨1354148, by rfl⟩ : syracuseStep 1805531 = 2708297) B2708297
theorem B1445159 : Blo 1202418 1445159 := bstep (se 1 (by rfl) ⟨1083869, by rfl⟩ : syracuseStep 1445159 = 2167739) B2167739
theorem B2706785 : Blo 1202418 2706785 := bstep (se 2 (by rfl) ⟨1015044, by rfl⟩ : syracuseStep 2706785 = 2030089) B2030089
theorem B1805705 : Blo 1202418 1805705 := bstep (se 2 (by rfl) ⟨677139, by rfl⟩ : syracuseStep 1805705 = 1354279) B1354279
theorem B2706875 : Blo 1202418 2706875 := bstep (se 1 (by rfl) ⟨2030156, by rfl⟩ : syracuseStep 2706875 = 4060313) B4060313
theorem B4058639 : Blo 1202418 4058639 := bstep (se 1 (by rfl) ⟨3043979, by rfl⟩ : syracuseStep 4058639 = 6087959) B6087959
theorem B2707001 : Blo 1202418 2707001 := bstep (se 2 (by rfl) ⟨1015125, by rfl⟩ : syracuseStep 2707001 = 2030251) B2030251
theorem B10284641 : Blo 1202418 10284641 := bstep (se 2 (by rfl) ⟨3856740, by rfl⟩ : syracuseStep 10284641 = 7713481) B7713481
theorem B7319251 : Blo 1202418 7319251 := bstep (se 1 (by rfl) ⟨5489438, by rfl⟩ : syracuseStep 7319251 = 10978877) B10978877
theorem B1830635 : Blo 1202418 1830635 := bstep (se 1 (by rfl) ⟨1372976, by rfl⟩ : syracuseStep 1830635 = 2745953) B2745953
theorem B1806059 : Blo 1202418 1806059 := bstep (se 1 (by rfl) ⟨1354544, by rfl⟩ : syracuseStep 1806059 = 2709089) B2709089
theorem B6852509 : Blo 1202418 6852509 := bstep (se 3 (by rfl) ⟨1284845, by rfl⟩ : syracuseStep 6852509 = 2569691) B2569691
theorem B1806287 : Blo 1202418 1806287 := bstep (se 1 (by rfl) ⟨1354715, by rfl⟩ : syracuseStep 1806287 = 2709431) B2709431
theorem B11726801 : Blo 1202418 11726801 := bstep (se 2 (by rfl) ⟨4397550, by rfl⟩ : syracuseStep 11726801 = 8795101) B8795101
theorem B4567049 : Blo 1202418 4567049 := bstep (se 2 (by rfl) ⟨1712643, by rfl⟩ : syracuseStep 4567049 = 3425287) B3425287
theorem B24760379 : Blo 1202418 24760379 := bstep (se 1 (by rfl) ⟨18570284, by rfl⟩ : syracuseStep 24760379 = 37140569) B37140569
theorem B2707667 : Blo 1202418 2707667 := bstep (se 1 (by rfl) ⟨2030750, by rfl⟩ : syracuseStep 2707667 = 4061501) B4061501
theorem B2707721 : Blo 1202418 2707721 := bstep (se 2 (by rfl) ⟨1015395, by rfl⟩ : syracuseStep 2707721 = 2030791) B2030791
theorem B2707937 : Blo 1202418 2707937 := bstep (se 2 (by rfl) ⟨1015476, by rfl⟩ : syracuseStep 2707937 = 2030953) B2030953
theorem B20566547 : Blo 1202418 20566547 := bstep (se 1 (by rfl) ⟨15424910, by rfl⟩ : syracuseStep 20566547 = 30849821) B30849821
theorem B4059719 : Blo 1202418 4059719 := bstep (se 1 (by rfl) ⟨3044789, by rfl⟩ : syracuseStep 4059719 = 6089579) B6089579
theorem B3043919 : Blo 1202418 3043919 := bstep (se 1 (by rfl) ⟨2282939, by rfl⟩ : syracuseStep 3043919 = 4565879) B4565879
theorem B6091361 : Blo 1202418 6091361 := bstep (se 2 (by rfl) ⟨2284260, by rfl⟩ : syracuseStep 6091361 = 4568521) B4568521
theorem B2290351 : Blo 1202418 2290351 := bstep (se 1 (by rfl) ⟨1717763, by rfl⟩ : syracuseStep 2290351 = 3435527) B3435527
theorem B2708243 : Blo 1202418 2708243 := bstep (se 1 (by rfl) ⟨2031182, by rfl⟩ : syracuseStep 2708243 = 4062365) B4062365
theorem B10556239 : Blo 1202418 10556239 := bstep (se 1 (by rfl) ⟨7917179, by rfl⟩ : syracuseStep 10556239 = 15834359) B15834359
theorem B4060151 : Blo 1202418 4060151 := bstep (se 1 (by rfl) ⟨3045113, by rfl⟩ : syracuseStep 4060151 = 6090227) B6090227
theorem B2708603 : Blo 1202418 2708603 := bstep (se 1 (by rfl) ⟨2031452, by rfl⟩ : syracuseStep 2708603 = 4062905) B4062905
theorem B30823577 : Blo 1202418 30823577 := bstep (se 2 (by rfl) ⟨11558841, by rfl⟩ : syracuseStep 30823577 = 23117683) B23117683
theorem B3044567 : Blo 1202418 3044567 := bstep (se 1 (by rfl) ⟨2283425, by rfl⟩ : syracuseStep 3044567 = 4566851) B4566851
theorem B6092009 : Blo 1202418 6092009 := bstep (se 2 (by rfl) ⟨2284503, by rfl⟩ : syracuseStep 6092009 = 4569007) B4569007
theorem B2708729 : Blo 1202418 2708729 := bstep (se 2 (by rfl) ⟨1015773, by rfl⟩ : syracuseStep 2708729 = 2031547) B2031547
theorem B10974503 : Blo 1202418 10974503 := bstep (se 1 (by rfl) ⟨8230877, by rfl⟩ : syracuseStep 10974503 = 16461755) B16461755
theorem B2168201 : Blo 1202418 2168201 := bstep (se 2 (by rfl) ⟨813075, by rfl⟩ : syracuseStep 2168201 = 1626151) B1626151
theorem B2708873 : Blo 1202418 2708873 := bstep (se 2 (by rfl) ⟨1015827, by rfl⟩ : syracuseStep 2708873 = 2031655) B2031655
theorem B6092171 : Blo 1202418 6092171 := bstep (se 1 (by rfl) ⟨4569128, by rfl⟩ : syracuseStep 6092171 = 9138257) B9138257
theorem B2708999 : Blo 1202418 2708999 := bstep (se 1 (by rfl) ⟨2031749, by rfl⟩ : syracuseStep 2708999 = 4063499) B4063499
theorem B2029151 : Blo 1202418 2029151 := bstep (se 1 (by rfl) ⟨1521863, by rfl⟩ : syracuseStep 2029151 = 3043727) B3043727
theorem B2709179 : Blo 1202418 2709179 := bstep (se 1 (by rfl) ⟨2031884, by rfl⟩ : syracuseStep 2709179 = 4063769) B4063769
theorem B15415069 : Blo 1202418 15415069 := bstep (se 3 (by rfl) ⟨2890325, by rfl⟩ : syracuseStep 15415069 = 5780651) B5780651
theorem B2029367 : Blo 1202418 2029367 := bstep (se 1 (by rfl) ⟨1522025, by rfl⟩ : syracuseStep 2029367 = 3044051) B3044051
theorem B2283319 : Blo 1202418 2283319 := bstep (se 1 (by rfl) ⟨1712489, by rfl⟩ : syracuseStep 2283319 = 3424979) B3424979
theorem B2709305 : Blo 1202418 2709305 := bstep (se 2 (by rfl) ⟨1015989, by rfl⟩ : syracuseStep 2709305 = 2031979) B2031979
theorem B4061015 : Blo 1202418 4061015 := bstep (se 1 (by rfl) ⟨3045761, by rfl⟩ : syracuseStep 4061015 = 6091523) B6091523
theorem B16480093 : Blo 1202418 16480093 := bstep (se 3 (by rfl) ⟨3090017, by rfl⟩ : syracuseStep 16480093 = 6180035) B6180035
theorem B2168783 : Blo 1202418 2168783 := bstep (se 1 (by rfl) ⟨1626587, by rfl⟩ : syracuseStep 2168783 = 3253175) B3253175
theorem B69441623 : Blo 1202418 69441623 := bstep (se 1 (by rfl) ⟨52081217, by rfl⟩ : syracuseStep 69441623 = 104162435) B104162435
theorem B1202463 : Blo 1202418 1202463 := bstep (se 1 (by rfl) ⟨901847, by rfl⟩ : syracuseStep 1202463 = 1803695) B1803695
theorem B1202523 : Blo 1202418 1202523 := bstep (se 1 (by rfl) ⟨901892, by rfl⟩ : syracuseStep 1202523 = 1803785) B1803785
theorem B1202543 : Blo 1202418 1202543 := bstep (se 1 (by rfl) ⟨901907, by rfl⟩ : syracuseStep 1202543 = 1803815) B1803815
theorem B1202599 : Blo 1202418 1202599 := bstep (se 1 (by rfl) ⟨901949, by rfl⟩ : syracuseStep 1202599 = 1803899) B1803899
theorem B2709935 : Blo 1202418 2709935 := bstep (se 1 (by rfl) ⟨2032451, by rfl⟩ : syracuseStep 2709935 = 4064903) B4064903
theorem B5487031 : Blo 1202418 5487031 := bstep (se 1 (by rfl) ⟨4115273, by rfl⟩ : syracuseStep 5487031 = 8230547) B8230547
theorem B3299795 : Blo 1202418 3299795 := bstep (se 1 (by rfl) ⟨2474846, by rfl⟩ : syracuseStep 3299795 = 4949693) B4949693
theorem B1202683 : Blo 1202418 1202683 := bstep (se 1 (by rfl) ⟨902012, by rfl⟩ : syracuseStep 1202683 = 1804025) B1804025
theorem B3045883 : Blo 1202418 3045883 := bstep (se 1 (by rfl) ⟨2284412, by rfl⟩ : syracuseStep 3045883 = 4568825) B4568825
theorem B1202751 : Blo 1202418 1202751 := bstep (se 1 (by rfl) ⟨902063, by rfl⟩ : syracuseStep 1202751 = 1804127) B1804127
theorem B2030143 : Blo 1202418 2030143 := bstep (se 1 (by rfl) ⟨1522607, by rfl⟩ : syracuseStep 2030143 = 3045215) B3045215
theorem B1202759 : Blo 1202418 1202759 := bstep (se 1 (by rfl) ⟨902069, by rfl⟩ : syracuseStep 1202759 = 1804139) B1804139
theorem B2284139 : Blo 1202418 2284139 := bstep (se 1 (by rfl) ⟨1713104, by rfl⟩ : syracuseStep 2284139 = 3426209) B3426209
theorem B3045995 : Blo 1202418 3045995 := bstep (se 1 (by rfl) ⟨2284496, by rfl⟩ : syracuseStep 3045995 = 4568993) B4568993
theorem B1202911 : Blo 1202418 1202911 := bstep (se 1 (by rfl) ⟨902183, by rfl⟩ : syracuseStep 1202911 = 1804367) B1804367
theorem B1202991 : Blo 1202418 1202991 := bstep (se 1 (by rfl) ⟨902243, by rfl⟩ : syracuseStep 1202991 = 1804487) B1804487
theorem B4062095 : Blo 1202418 4062095 := bstep (se 1 (by rfl) ⟨3046571, by rfl⟩ : syracuseStep 4062095 = 6093143) B6093143
theorem B1203099 : Blo 1202418 1203099 := bstep (se 1 (by rfl) ⟨902324, by rfl⟩ : syracuseStep 1203099 = 1804649) B1804649
theorem B5209019 : Blo 1202418 5209019 := bstep (se 1 (by rfl) ⟨3906764, by rfl⟩ : syracuseStep 5209019 = 7813529) B7813529
theorem B1203151 : Blo 1202418 1203151 := bstep (se 1 (by rfl) ⟨902363, by rfl⟩ : syracuseStep 1203151 = 1804727) B1804727
theorem B1203175 : Blo 1202418 1203175 := bstep (se 1 (by rfl) ⟨902381, by rfl⟩ : syracuseStep 1203175 = 1804763) B1804763
theorem B2284519 : Blo 1202418 2284519 := bstep (se 1 (by rfl) ⟨1713389, by rfl⟩ : syracuseStep 2284519 = 3426779) B3426779
theorem B20544677 : Blo 1202418 20544677 := bstep (se 4 (by rfl) ⟨1926063, by rfl⟩ : syracuseStep 20544677 = 3852127) B3852127
theorem B2030825 : Blo 1202418 2030825 := bstep (se 2 (by rfl) ⟨761559, by rfl⟩ : syracuseStep 2030825 = 1523119) B1523119
theorem B2284777 : Blo 1202418 2284777 := bstep (se 2 (by rfl) ⟨856791, by rfl⟩ : syracuseStep 2284777 = 1713583) B1713583
theorem B3046643 : Blo 1202418 3046643 := bstep (se 1 (by rfl) ⟨2284982, by rfl⟩ : syracuseStep 3046643 = 4569965) B4569965
theorem B2030879 : Blo 1202418 2030879 := bstep (se 1 (by rfl) ⟨1523159, by rfl⟩ : syracuseStep 2030879 = 3046319) B3046319
theorem B1203487 : Blo 1202418 1203487 := bstep (se 1 (by rfl) ⟨902615, by rfl⟩ : syracuseStep 1203487 = 1805231) B1805231
theorem B1203547 : Blo 1202418 1203547 := bstep (se 1 (by rfl) ⟨902660, by rfl⟩ : syracuseStep 1203547 = 1805321) B1805321
theorem B4570465 : Blo 1202418 4570465 := bstep (se 2 (by rfl) ⟨1713924, by rfl⟩ : syracuseStep 4570465 = 3427849) B3427849
theorem B1203567 : Blo 1202418 1203567 := bstep (se 1 (by rfl) ⟨902675, by rfl⟩ : syracuseStep 1203567 = 1805351) B1805351
theorem B5143945 : Blo 1202418 5143945 := bstep (se 2 (by rfl) ⟨1928979, by rfl⟩ : syracuseStep 5143945 = 3857959) B3857959
theorem B1203623 : Blo 1202418 1203623 := bstep (se 1 (by rfl) ⟨902717, by rfl⟩ : syracuseStep 1203623 = 1805435) B1805435
theorem B2571707 : Blo 1202418 2571707 := bstep (se 1 (by rfl) ⟨1928780, by rfl⟩ : syracuseStep 2571707 = 3857561) B3857561
theorem B3046855 : Blo 1202418 3046855 := bstep (se 1 (by rfl) ⟨2285141, by rfl⟩ : syracuseStep 3046855 = 4570283) B4570283
theorem B1203707 : Blo 1202418 1203707 := bstep (se 1 (by rfl) ⟨902780, by rfl⟩ : syracuseStep 1203707 = 1805561) B1805561
theorem B1203775 : Blo 1202418 1203775 := bstep (se 1 (by rfl) ⟨902831, by rfl⟩ : syracuseStep 1203775 = 1805663) B1805663
theorem B1203783 : Blo 1202418 1203783 := bstep (se 1 (by rfl) ⟨902837, by rfl⟩ : syracuseStep 1203783 = 1805675) B1805675
theorem B4570739 : Blo 1202418 4570739 := bstep (se 1 (by rfl) ⟨3428054, by rfl⟩ : syracuseStep 4570739 = 6856109) B6856109
theorem B1203935 : Blo 1202418 1203935 := bstep (se 1 (by rfl) ⟨902951, by rfl⟩ : syracuseStep 1203935 = 1805903) B1805903
theorem B1204015 : Blo 1202418 1204015 := bstep (se 1 (by rfl) ⟨903011, by rfl⟩ : syracuseStep 1204015 = 1806023) B1806023
theorem B1785655 : Blo 1202418 1785655 := bstep (se 1 (by rfl) ⟨1339241, by rfl⟩ : syracuseStep 1785655 = 2678483) B2678483
theorem B4570937 : Blo 1202418 4570937 := bstep (se 2 (by rfl) ⟨1714101, by rfl⟩ : syracuseStep 4570937 = 3428203) B3428203
theorem B7815041 : Blo 1202418 7815041 := bstep (se 2 (by rfl) ⟨2930640, by rfl⟩ : syracuseStep 7815041 = 5861281) B5861281
theorem B9142145 : Blo 1202418 9142145 := bstep (se 2 (by rfl) ⟨3428304, by rfl⟩ : syracuseStep 9142145 = 6856609) B6856609
theorem B1204123 : Blo 1202418 1204123 := bstep (se 1 (by rfl) ⟨903092, by rfl⟩ : syracuseStep 1204123 = 1806185) B1806185
theorem B1204175 : Blo 1202418 1204175 := bstep (se 1 (by rfl) ⟨903131, by rfl⟩ : syracuseStep 1204175 = 1806263) B1806263
theorem B1204199 : Blo 1202418 1204199 := bstep (se 1 (by rfl) ⟨903149, by rfl⟩ : syracuseStep 1204199 = 1806299) B1806299
theorem B3424295 : Blo 1202418 3424295 := bstep (se 1 (by rfl) ⟨2568221, by rfl⟩ : syracuseStep 3424295 = 5136443) B5136443
theorem B16506919 : Blo 1202418 16506919 := bstep (se 1 (by rfl) ⟨12380189, by rfl⟩ : syracuseStep 16506919 = 24760379) B24760379
theorem B3047777 : Blo 1202418 3047777 := bstep (se 2 (by rfl) ⟨1142916, by rfl⟩ : syracuseStep 3047777 = 2285833) B2285833
theorem B4063607 : Blo 1202418 4063607 := bstep (se 1 (by rfl) ⟨3047705, by rfl⟩ : syracuseStep 4063607 = 6095411) B6095411
theorem B2032121 : Blo 1202418 2032121 := bstep (se 2 (by rfl) ⟨762045, by rfl⟩ : syracuseStep 2032121 = 1524091) B1524091
theorem B4571711 : Blo 1202418 4571711 := bstep (se 1 (by rfl) ⟨3428783, by rfl⟩ : syracuseStep 4571711 = 6857567) B6857567
theorem B2032391 : Blo 1202418 2032391 := bstep (se 1 (by rfl) ⟨1524293, by rfl⟩ : syracuseStep 2032391 = 3048587) B3048587
theorem B7316335 : Blo 1202418 7316335 := bstep (se 1 (by rfl) ⟨5487251, by rfl⟩ : syracuseStep 7316335 = 10974503) B10974503
theorem B6095735 : Blo 1202418 6095735 := bstep (se 1 (by rfl) ⟨4571801, by rfl⟩ : syracuseStep 6095735 = 9143603) B9143603
theorem B2474963 : Blo 1202418 2474963 := bstep (se 1 (by rfl) ⟨1856222, by rfl⟩ : syracuseStep 2474963 = 3712445) B3712445
theorem B6849593 : Blo 1202418 6849593 := bstep (se 2 (by rfl) ⟨2568597, by rfl⟩ : syracuseStep 6849593 = 5137195) B5137195
theorem B1352767 : Blo 1202418 1352767 := bstep (se 1 (by rfl) ⟨1014575, by rfl⟩ : syracuseStep 1352767 = 2029151) B2029151
theorem B39036005 : Blo 1202418 39036005 := bstep (se 4 (by rfl) ⟨3659625, by rfl⟩ : syracuseStep 39036005 = 7319251) B7319251
theorem B14074985 : Blo 1202418 14074985 := bstep (se 2 (by rfl) ⟨5278119, by rfl⟩ : syracuseStep 14074985 = 10556239) B10556239
theorem B6857885 : Blo 1202418 6857885 := bstep (se 3 (by rfl) ⟨1285853, by rfl⟩ : syracuseStep 6857885 = 2571707) B2571707
theorem B1352911 : Blo 1202418 1352911 := bstep (se 1 (by rfl) ⟨1014683, by rfl⟩ : syracuseStep 1352911 = 2029367) B2029367
theorem B46294415 : Blo 1202418 46294415 := bstep (se 1 (by rfl) ⟨34720811, by rfl⟩ : syracuseStep 46294415 = 69441623) B69441623
theorem B4064687 : Blo 1202418 4064687 := bstep (se 1 (by rfl) ⟨3048515, by rfl⟩ : syracuseStep 4064687 = 6097031) B6097031
theorem B1803887 : Blo 1202418 1803887 := bstep (se 1 (by rfl) ⟨1352915, by rfl⟩ : syracuseStep 1803887 = 2705831) B2705831
theorem B27829909 : Blo 1202418 27829909 := bstep (se 6 (by rfl) ⟨652263, by rfl⟩ : syracuseStep 27829909 = 1304527) B1304527
theorem B6096545 : Blo 1202418 6096545 := bstep (se 2 (by rfl) ⟨2286204, by rfl⟩ : syracuseStep 6096545 = 4572409) B4572409
theorem B1803959 : Blo 1202418 1803959 := bstep (se 1 (by rfl) ⟨1352969, by rfl⟩ : syracuseStep 1803959 = 2705939) B2705939
theorem B1803995 : Blo 1202418 1803995 := bstep (se 1 (by rfl) ⟨1352996, by rfl⟩ : syracuseStep 1803995 = 2705993) B2705993
theorem B4572895 : Blo 1202418 4572895 := bstep (se 1 (by rfl) ⟨3429671, by rfl⟩ : syracuseStep 4572895 = 6859343) B6859343
theorem B6858593 : Blo 1202418 6858593 := bstep (se 2 (by rfl) ⟨2571972, by rfl⟩ : syracuseStep 6858593 = 5143945) B5143945
theorem B1804169 : Blo 1202418 1804169 := bstep (se 2 (by rfl) ⟨676563, by rfl⟩ : syracuseStep 1804169 = 1353127) B1353127
theorem B26003429 : Blo 1202418 26003429 := bstep (se 4 (by rfl) ⟨2437821, by rfl⟩ : syracuseStep 26003429 = 4875643) B4875643
theorem B1804271 : Blo 1202418 1804271 := bstep (se 1 (by rfl) ⟨1353203, by rfl⟩ : syracuseStep 1804271 = 2706407) B2706407
theorem B1353883 : Blo 1202418 1353883 := bstep (se 1 (by rfl) ⟨1015412, by rfl⟩ : syracuseStep 1353883 = 2030825) B2030825
theorem B1353919 : Blo 1202418 1353919 := bstep (se 1 (by rfl) ⟨1015439, by rfl⟩ : syracuseStep 1353919 = 2030879) B2030879
theorem B1804523 : Blo 1202418 1804523 := bstep (se 1 (by rfl) ⟨1353392, by rfl⟩ : syracuseStep 1804523 = 2706785) B2706785
theorem B29264165 : Blo 1202418 29264165 := bstep (se 4 (by rfl) ⟨2743515, by rfl⟩ : syracuseStep 29264165 = 5487031) B5487031
theorem B1804583 : Blo 1202418 1804583 := bstep (se 1 (by rfl) ⟨1353437, by rfl⟩ : syracuseStep 1804583 = 2706875) B2706875
theorem B2705759 : Blo 1202418 2705759 := bstep (se 1 (by rfl) ⟨2029319, by rfl⟩ : syracuseStep 2705759 = 4058639) B4058639
theorem B1804667 : Blo 1202418 1804667 := bstep (se 1 (by rfl) ⟨1353500, by rfl⟩ : syracuseStep 1804667 = 2707001) B2707001
theorem B21973457 : Blo 1202418 21973457 := bstep (se 2 (by rfl) ⟨8240046, by rfl⟩ : syracuseStep 21973457 = 16480093) B16480093
theorem B1804937 : Blo 1202418 1804937 := bstep (se 2 (by rfl) ⟨676851, by rfl⟩ : syracuseStep 1804937 = 1353703) B1353703
theorem B7817867 : Blo 1202418 7817867 := bstep (se 1 (by rfl) ⟨5863400, by rfl⟩ : syracuseStep 7817867 = 11726801) B11726801
theorem B8235695 : Blo 1202418 8235695 := bstep (se 1 (by rfl) ⟨6176771, by rfl⟩ : syracuseStep 8235695 = 12353543) B12353543
theorem B1805111 : Blo 1202418 1805111 := bstep (se 1 (by rfl) ⟨1353833, by rfl⟩ : syracuseStep 1805111 = 2707667) B2707667
theorem B1805147 : Blo 1202418 1805147 := bstep (se 1 (by rfl) ⟨1353860, by rfl⟩ : syracuseStep 1805147 = 2707721) B2707721
theorem B1805291 : Blo 1202418 1805291 := bstep (se 1 (by rfl) ⟨1353968, by rfl⟩ : syracuseStep 1805291 = 2707937) B2707937
theorem B2706479 : Blo 1202418 2706479 := bstep (se 1 (by rfl) ⟨2029859, by rfl⟩ : syracuseStep 2706479 = 4059719) B4059719
theorem B7711841 : Blo 1202418 7711841 := bstep (se 2 (by rfl) ⟨2891940, by rfl⟩ : syracuseStep 7711841 = 5783881) B5783881
theorem B1805495 : Blo 1202418 1805495 := bstep (se 1 (by rfl) ⟨1354121, by rfl⟩ : syracuseStep 1805495 = 2708243) B2708243
theorem B2706767 : Blo 1202418 2706767 := bstep (se 1 (by rfl) ⟨2030075, by rfl⟩ : syracuseStep 2706767 = 4060151) B4060151
theorem B1805735 : Blo 1202418 1805735 := bstep (se 1 (by rfl) ⟨1354301, by rfl⟩ : syracuseStep 1805735 = 2708603) B2708603
theorem B2706857 : Blo 1202418 2706857 := bstep (se 2 (by rfl) ⟨1015071, by rfl⟩ : syracuseStep 2706857 = 2030143) B2030143
theorem B20549051 : Blo 1202418 20549051 := bstep (se 1 (by rfl) ⟨15411788, by rfl⟩ : syracuseStep 20549051 = 30823577) B30823577
theorem B3853757 : Blo 1202418 3853757 := bstep (se 3 (by rfl) ⟨722579, by rfl⟩ : syracuseStep 3853757 = 1445159) B1445159
theorem B1805819 : Blo 1202418 1805819 := bstep (se 1 (by rfl) ⟨1354364, by rfl⟩ : syracuseStep 1805819 = 2708729) B2708729
theorem B1445467 : Blo 1202418 1445467 := bstep (se 1 (by rfl) ⟨1084100, by rfl⟩ : syracuseStep 1445467 = 2168201) B2168201
theorem B1805915 : Blo 1202418 1805915 := bstep (se 1 (by rfl) ⟨1354436, by rfl⟩ : syracuseStep 1805915 = 2708873) B2708873
theorem B7319155 : Blo 1202418 7319155 := bstep (se 1 (by rfl) ⟨5489366, by rfl⟩ : syracuseStep 7319155 = 10978733) B10978733
theorem B1805999 : Blo 1202418 1805999 := bstep (se 1 (by rfl) ⟨1354499, by rfl⟩ : syracuseStep 1805999 = 2708999) B2708999
theorem B14839507 : Blo 1202418 14839507 := bstep (se 1 (by rfl) ⟨11129630, by rfl⟩ : syracuseStep 14839507 = 22259261) B22259261
theorem B26390285 : Blo 1202418 26390285 := bstep (se 3 (by rfl) ⟨4948178, by rfl⟩ : syracuseStep 26390285 = 9896357) B9896357
theorem B1806119 : Blo 1202418 1806119 := bstep (se 1 (by rfl) ⟨1354589, by rfl⟩ : syracuseStep 1806119 = 2709179) B2709179
theorem B2928505 : Blo 1202418 2928505 := bstep (se 2 (by rfl) ⟨1098189, by rfl⟩ : syracuseStep 2928505 = 2196379) B2196379
theorem B1806203 : Blo 1202418 1806203 := bstep (se 1 (by rfl) ⟨1354652, by rfl⟩ : syracuseStep 1806203 = 2709305) B2709305
theorem B2707343 : Blo 1202418 2707343 := bstep (se 1 (by rfl) ⟨2030507, by rfl⟩ : syracuseStep 2707343 = 4061015) B4061015
theorem B1445855 : Blo 1202418 1445855 := bstep (se 1 (by rfl) ⟨1084391, by rfl⟩ : syracuseStep 1445855 = 2168783) B2168783
theorem B6090875 : Blo 1202418 6090875 := bstep (se 1 (by rfl) ⟨4568156, by rfl⟩ : syracuseStep 6090875 = 9136313) B9136313
theorem B6852761 : Blo 1202418 6852761 := bstep (se 2 (by rfl) ⟨2569785, by rfl⟩ : syracuseStep 6852761 = 5139571) B5139571
theorem B6091037 : Blo 1202418 6091037 := bstep (se 3 (by rfl) ⟨1142069, by rfl⟩ : syracuseStep 6091037 = 2284139) B2284139
theorem B1806623 : Blo 1202418 1806623 := bstep (se 1 (by rfl) ⟨1354967, by rfl⟩ : syracuseStep 1806623 = 2709935) B2709935
theorem B9523493 : Blo 1202418 9523493 := bstep (se 4 (by rfl) ⟨892827, by rfl⟩ : syracuseStep 9523493 = 1785655) B1785655
theorem B8794423 : Blo 1202418 8794423 := bstep (se 1 (by rfl) ⟨6595817, by rfl⟩ : syracuseStep 8794423 = 13191635) B13191635
theorem B2199863 : Blo 1202418 2199863 := bstep (se 1 (by rfl) ⟨1649897, by rfl⟩ : syracuseStep 2199863 = 3299795) B3299795
theorem B4059503 : Blo 1202418 4059503 := bstep (se 1 (by rfl) ⟨3044627, by rfl⟩ : syracuseStep 4059503 = 6089255) B6089255
theorem B5779961 : Blo 1202418 5779961 := bstep (se 2 (by rfl) ⟨2167485, by rfl⟩ : syracuseStep 5779961 = 4334971) B4334971
theorem B2708063 : Blo 1202418 2708063 := bstep (se 1 (by rfl) ⟨2031047, by rfl⟩ : syracuseStep 2708063 = 4062095) B4062095
theorem B5780231 : Blo 1202418 5780231 := bstep (se 1 (by rfl) ⟨4335173, by rfl⟩ : syracuseStep 5780231 = 8670347) B8670347
theorem B3044425 : Blo 1202418 3044425 := bstep (se 2 (by rfl) ⟨1141659, by rfl⟩ : syracuseStep 3044425 = 2283319) B2283319
theorem B4568339 : Blo 1202418 4568339 := bstep (se 1 (by rfl) ⟨3426254, by rfl⟩ : syracuseStep 4568339 = 6852509) B6852509
theorem B3044699 : Blo 1202418 3044699 := bstep (se 1 (by rfl) ⟨2283524, by rfl⟩ : syracuseStep 3044699 = 4567049) B4567049
theorem B2708891 : Blo 1202418 2708891 := bstep (se 1 (by rfl) ⟨2031668, by rfl⟩ : syracuseStep 2708891 = 4063337) B4063337
theorem B8230331 : Blo 1202418 8230331 := bstep (se 1 (by rfl) ⟨6172748, by rfl⟩ : syracuseStep 8230331 = 12345497) B12345497
theorem B4339169 : Blo 1202418 4339169 := bstep (se 2 (by rfl) ⟨1627188, by rfl⟩ : syracuseStep 4339169 = 3254377) B3254377
theorem B13711031 : Blo 1202418 13711031 := bstep (se 1 (by rfl) ⟨10283273, by rfl⟩ : syracuseStep 13711031 = 20566547) B20566547
theorem B2029279 : Blo 1202418 2029279 := bstep (se 1 (by rfl) ⟨1521959, by rfl⟩ : syracuseStep 2029279 = 3043919) B3043919
theorem B4060907 : Blo 1202418 4060907 := bstep (se 1 (by rfl) ⟨3045680, by rfl⟩ : syracuseStep 4060907 = 6091361) B6091361
theorem B2709467 : Blo 1202418 2709467 := bstep (se 1 (by rfl) ⟨2032100, by rfl⟩ : syracuseStep 2709467 = 4064201) B4064201
theorem B4061177 : Blo 1202418 4061177 := bstep (se 2 (by rfl) ⟨1522941, by rfl⟩ : syracuseStep 4061177 = 3045883) B3045883
theorem B2029711 : Blo 1202418 2029711 := bstep (se 1 (by rfl) ⟨1522283, by rfl⟩ : syracuseStep 2029711 = 3044567) B3044567
theorem B2709647 : Blo 1202418 2709647 := bstep (se 1 (by rfl) ⟨2032235, by rfl⟩ : syracuseStep 2709647 = 4064471) B4064471
theorem B4061339 : Blo 1202418 4061339 := bstep (se 1 (by rfl) ⟨3046004, by rfl⟩ : syracuseStep 4061339 = 6092009) B6092009
theorem B2709665 : Blo 1202418 2709665 := bstep (se 2 (by rfl) ⟨1016124, by rfl⟩ : syracuseStep 2709665 = 2032249) B2032249
theorem B3053801 : Blo 1202418 3053801 := bstep (se 2 (by rfl) ⟨1145175, by rfl⟩ : syracuseStep 3053801 = 2290351) B2290351
theorem B4634857 : Blo 1202418 4634857 := bstep (se 2 (by rfl) ⟨1738071, by rfl⟩ : syracuseStep 4634857 = 3476143) B3476143
theorem B2709737 : Blo 1202418 2709737 := bstep (se 2 (by rfl) ⟨1016151, by rfl⟩ : syracuseStep 2709737 = 2032303) B2032303
theorem B4061447 : Blo 1202418 4061447 := bstep (se 1 (by rfl) ⟨3046085, by rfl⟩ : syracuseStep 4061447 = 6092171) B6092171
theorem B1202479 : Blo 1202418 1202479 := bstep (se 1 (by rfl) ⟨901859, by rfl⟩ : syracuseStep 1202479 = 1803719) B1803719
theorem B1202715 : Blo 1202418 1202715 := bstep (se 1 (by rfl) ⟨902036, by rfl⟩ : syracuseStep 1202715 = 1804073) B1804073
theorem B1202719 : Blo 1202418 1202719 := bstep (se 1 (by rfl) ⟨902039, by rfl⟩ : syracuseStep 1202719 = 1804079) B1804079
theorem B3046025 : Blo 1202418 3046025 := bstep (se 2 (by rfl) ⟨1142259, by rfl⟩ : syracuseStep 3046025 = 2284519) B2284519
theorem B7707383 : Blo 1202418 7707383 := bstep (se 1 (by rfl) ⟨5780537, by rfl⟩ : syracuseStep 7707383 = 11561075) B11561075
theorem B6593363 : Blo 1202418 6593363 := bstep (se 1 (by rfl) ⟨4945022, by rfl⟩ : syracuseStep 6593363 = 9890045) B9890045
theorem B1203035 : Blo 1202418 1203035 := bstep (se 1 (by rfl) ⟨902276, by rfl⟩ : syracuseStep 1203035 = 1804553) B1804553
theorem B4397915 : Blo 1202418 4397915 := bstep (se 1 (by rfl) ⟨3298436, by rfl⟩ : syracuseStep 4397915 = 6596873) B6596873
theorem B1203103 : Blo 1202418 1203103 := bstep (se 1 (by rfl) ⟨902327, by rfl⟩ : syracuseStep 1203103 = 1804655) B1804655
theorem B3046369 : Blo 1202418 3046369 := bstep (se 2 (by rfl) ⟨1142388, by rfl⟩ : syracuseStep 3046369 = 2284777) B2284777
theorem B1203247 : Blo 1202418 1203247 := bstep (se 1 (by rfl) ⟨902435, by rfl⟩ : syracuseStep 1203247 = 1804871) B1804871
theorem B10279993 : Blo 1202418 10279993 := bstep (se 2 (by rfl) ⟨3854997, by rfl⟩ : syracuseStep 10279993 = 7709995) B7709995
theorem B1203271 : Blo 1202418 1203271 := bstep (se 1 (by rfl) ⟨902453, by rfl⟩ : syracuseStep 1203271 = 1804907) B1804907
theorem B2030663 : Blo 1202418 2030663 := bstep (se 1 (by rfl) ⟨1522997, by rfl⟩ : syracuseStep 2030663 = 3045995) B3045995
theorem B6093953 : Blo 1202418 6093953 := bstep (se 2 (by rfl) ⟨2285232, by rfl⟩ : syracuseStep 6093953 = 4570465) B4570465
theorem B1203423 : Blo 1202418 1203423 := bstep (se 1 (by rfl) ⟨902567, by rfl⟩ : syracuseStep 1203423 = 1805135) B1805135
theorem B4062473 : Blo 1202418 4062473 := bstep (se 2 (by rfl) ⟨1523427, by rfl⟩ : syracuseStep 4062473 = 3046855) B3046855
theorem B3472679 : Blo 1202418 3472679 := bstep (se 1 (by rfl) ⟨2604509, by rfl⟩ : syracuseStep 3472679 = 5209019) B5209019
theorem B13696451 : Blo 1202418 13696451 := bstep (se 1 (by rfl) ⟨10272338, by rfl⟩ : syracuseStep 13696451 = 20544677) B20544677
theorem B1203687 : Blo 1202418 1203687 := bstep (se 1 (by rfl) ⟨902765, by rfl⟩ : syracuseStep 1203687 = 1805531) B1805531
theorem B2031095 : Blo 1202418 2031095 := bstep (se 1 (by rfl) ⟨1523321, by rfl⟩ : syracuseStep 2031095 = 3046643) B3046643
theorem B65846789 : Blo 1202418 65846789 := bstep (se 4 (by rfl) ⟨6173136, by rfl⟩ : syracuseStep 65846789 = 12346273) B12346273
theorem B1203803 : Blo 1202418 1203803 := bstep (se 1 (by rfl) ⟨902852, by rfl⟩ : syracuseStep 1203803 = 1805705) B1805705
theorem B20553425 : Blo 1202418 20553425 := bstep (se 2 (by rfl) ⟨7707534, by rfl⟩ : syracuseStep 20553425 = 15415069) B15415069
theorem B6856427 : Blo 1202418 6856427 := bstep (se 1 (by rfl) ⟨5142320, by rfl⟩ : syracuseStep 6856427 = 10284641) B10284641
theorem B3047159 : Blo 1202418 3047159 := bstep (se 1 (by rfl) ⟨2285369, by rfl⟩ : syracuseStep 3047159 = 4570739) B4570739
theorem B1220423 : Blo 1202418 1220423 := bstep (se 1 (by rfl) ⟨915317, by rfl⟩ : syracuseStep 1220423 = 1830635) B1830635
theorem B1204039 : Blo 1202418 1204039 := bstep (se 1 (by rfl) ⟨903029, by rfl⟩ : syracuseStep 1204039 = 1806059) B1806059
theorem B3047291 : Blo 1202418 3047291 := bstep (se 1 (by rfl) ⟨2285468, by rfl⟩ : syracuseStep 3047291 = 4570937) B4570937
theorem B5210027 : Blo 1202418 5210027 := bstep (se 1 (by rfl) ⟨3907520, by rfl⟩ : syracuseStep 5210027 = 7815041) B7815041
theorem B6094763 : Blo 1202418 6094763 := bstep (se 1 (by rfl) ⟨4571072, by rfl⟩ : syracuseStep 6094763 = 9142145) B9142145
theorem B1204191 : Blo 1202418 1204191 := bstep (se 1 (by rfl) ⟨903143, by rfl⟩ : syracuseStep 1204191 = 1806287) B1806287
theorem B1204415 : Blo 1202418 1204415 := bstep (se 1 (by rfl) ⟨903311, by rfl⟩ : syracuseStep 1204415 = 1806623) B1806623
theorem B6348995 : Blo 1202418 6348995 := bstep (se 1 (by rfl) ⟨4761746, by rfl⟩ : syracuseStep 6348995 = 9523493) B9523493
theorem B2031851 : Blo 1202418 2031851 := bstep (se 1 (by rfl) ⟨1523888, by rfl⟩ : syracuseStep 2031851 = 3047777) B3047777
theorem B3047807 : Blo 1202418 3047807 := bstep (se 1 (by rfl) ⟨2285855, by rfl⟩ : syracuseStep 3047807 = 4571711) B4571711
theorem B4063823 : Blo 1202418 4063823 := bstep (se 1 (by rfl) ⟨3047867, by rfl⟩ : syracuseStep 4063823 = 6095735) B6095735
theorem B4571923 : Blo 1202418 4571923 := bstep (se 1 (by rfl) ⟨3428942, by rfl⟩ : syracuseStep 4571923 = 6857885) B6857885
theorem B5866301 : Blo 1202418 5866301 := bstep (se 3 (by rfl) ⟨1099931, by rfl⟩ : syracuseStep 5866301 = 2199863) B2199863
theorem B2892779 : Blo 1202418 2892779 := bstep (se 1 (by rfl) ⟨2169584, by rfl⟩ : syracuseStep 2892779 = 4339169) B4339169
theorem B79144037 : Blo 1202418 79144037 := bstep (se 4 (by rfl) ⟨7419753, by rfl⟩ : syracuseStep 79144037 = 14839507) B14839507
theorem B4064363 : Blo 1202418 4064363 := bstep (se 1 (by rfl) ⟨3048272, by rfl⟩ : syracuseStep 4064363 = 6096545) B6096545
theorem B4572395 : Blo 1202418 4572395 := bstep (se 1 (by rfl) ⟨3429296, by rfl⟩ : syracuseStep 4572395 = 6858593) B6858593
theorem B17335619 : Blo 1202418 17335619 := bstep (se 1 (by rfl) ⟨13001714, by rfl⟩ : syracuseStep 17335619 = 26003429) B26003429
theorem B13706657 : Blo 1202418 13706657 := bstep (se 2 (by rfl) ⟨5139996, by rfl⟩ : syracuseStep 13706657 = 10279993) B10279993
theorem B1803689 : Blo 1202418 1803689 := bstep (se 2 (by rfl) ⟨676383, by rfl⟩ : syracuseStep 1803689 = 1352767) B1352767
theorem B1803839 : Blo 1202418 1803839 := bstep (se 1 (by rfl) ⟨1352879, by rfl⟩ : syracuseStep 1803839 = 2705759) B2705759
theorem B1803881 : Blo 1202418 1803881 := bstep (se 2 (by rfl) ⟨676455, by rfl⟩ : syracuseStep 1803881 = 1352911) B1352911
theorem B14648971 : Blo 1202418 14648971 := bstep (se 1 (by rfl) ⟨10986728, by rfl⟩ : syracuseStep 14648971 = 21973457) B21973457
theorem B5211911 : Blo 1202418 5211911 := bstep (se 1 (by rfl) ⟨3908933, by rfl⟩ : syracuseStep 5211911 = 7817867) B7817867
theorem B5138255 : Blo 1202418 5138255 := bstep (se 1 (by rfl) ⟨3853691, by rfl⟩ : syracuseStep 5138255 = 7707383) B7707383
theorem B1804319 : Blo 1202418 1804319 := bstep (se 1 (by rfl) ⟨1353239, by rfl⟩ : syracuseStep 1804319 = 2706479) B2706479
theorem B1353775 : Blo 1202418 1353775 := bstep (se 1 (by rfl) ⟨1015331, by rfl⟩ : syracuseStep 1353775 = 2030663) B2030663
theorem B1927289 : Blo 1202418 1927289 := bstep (se 2 (by rfl) ⟨722733, by rfl⟩ : syracuseStep 1927289 = 1445467) B1445467
theorem B9758873 : Blo 1202418 9758873 := bstep (se 2 (by rfl) ⟨3659577, by rfl⟩ : syracuseStep 9758873 = 7319155) B7319155
theorem B3254461 : Blo 1202418 3254461 := bstep (se 3 (by rfl) ⟨610211, by rfl⟩ : syracuseStep 3254461 = 1220423) B1220423
theorem B1804511 : Blo 1202418 1804511 := bstep (se 1 (by rfl) ⟨1353383, by rfl⟩ : syracuseStep 1804511 = 2706767) B2706767
theorem B1804571 : Blo 1202418 1804571 := bstep (se 1 (by rfl) ⟨1353428, by rfl⟩ : syracuseStep 1804571 = 2706857) B2706857
theorem B13699367 : Blo 1202418 13699367 := bstep (se 1 (by rfl) ⟨10274525, by rfl⟩ : syracuseStep 13699367 = 20549051) B20549051
theorem B2705705 : Blo 1202418 2705705 := bstep (se 2 (by rfl) ⟨1014639, by rfl⟩ : syracuseStep 2705705 = 2029279) B2029279
theorem B6097193 : Blo 1202418 6097193 := bstep (se 2 (by rfl) ⟨2286447, by rfl⟩ : syracuseStep 6097193 = 4572895) B4572895
theorem B1354063 : Blo 1202418 1354063 := bstep (se 1 (by rfl) ⟨1015547, by rfl⟩ : syracuseStep 1354063 = 2031095) B2031095
theorem B1804895 : Blo 1202418 1804895 := bstep (se 1 (by rfl) ⟨1353671, by rfl⟩ : syracuseStep 1804895 = 2707343) B2707343
theorem B2706281 : Blo 1202418 2706281 := bstep (se 2 (by rfl) ⟨1014855, by rfl⟩ : syracuseStep 2706281 = 2029711) B2029711
theorem B1805177 : Blo 1202418 1805177 := bstep (se 2 (by rfl) ⟨676941, by rfl⟩ : syracuseStep 1805177 = 1353883) B1353883
theorem B2706335 : Blo 1202418 2706335 := bstep (se 1 (by rfl) ⟨2029751, by rfl⟩ : syracuseStep 2706335 = 4059503) B4059503
theorem B1805225 : Blo 1202418 1805225 := bstep (se 2 (by rfl) ⟨676959, by rfl⟩ : syracuseStep 1805225 = 1353919) B1353919
theorem B6179809 : Blo 1202418 6179809 := bstep (se 2 (by rfl) ⟨2317428, by rfl⟩ : syracuseStep 6179809 = 4634857) B4634857
theorem B3853307 : Blo 1202418 3853307 := bstep (se 1 (by rfl) ⟨2889980, by rfl⟩ : syracuseStep 3853307 = 5779961) B5779961
theorem B1354747 : Blo 1202418 1354747 := bstep (se 1 (by rfl) ⟨1016060, by rfl⟩ : syracuseStep 1354747 = 2032121) B2032121
theorem B1805375 : Blo 1202418 1805375 := bstep (se 1 (by rfl) ⟨1354031, by rfl⟩ : syracuseStep 1805375 = 2708063) B2708063
theorem B11725897 : Blo 1202418 11725897 := bstep (se 2 (by rfl) ⟨4397211, by rfl⟩ : syracuseStep 11725897 = 8794423) B8794423
theorem B3853487 : Blo 1202418 3853487 := bstep (se 1 (by rfl) ⟨2890115, by rfl⟩ : syracuseStep 3853487 = 5780231) B5780231
theorem B1354927 : Blo 1202418 1354927 := bstep (se 1 (by rfl) ⟨1016195, by rfl⟩ : syracuseStep 1354927 = 2032391) B2032391
theorem B1649975 : Blo 1202418 1649975 := bstep (se 1 (by rfl) ⟨1237481, by rfl⟩ : syracuseStep 1649975 = 2474963) B2474963
theorem B4566395 : Blo 1202418 4566395 := bstep (se 1 (by rfl) ⟨3424796, by rfl⟩ : syracuseStep 4566395 = 6849593) B6849593
theorem B9260477 : Blo 1202418 9260477 := bstep (se 3 (by rfl) ⟨1736339, by rfl⟩ : syracuseStep 9260477 = 3472679) B3472679
theorem B30862943 : Blo 1202418 30862943 := bstep (se 1 (by rfl) ⟨23147207, by rfl⟩ : syracuseStep 30862943 = 46294415) B46294415
theorem B1805927 : Blo 1202418 1805927 := bstep (se 1 (by rfl) ⟨1354445, by rfl⟩ : syracuseStep 1805927 = 2708891) B2708891
theorem B2707271 : Blo 1202418 2707271 := bstep (se 1 (by rfl) ⟨2030453, by rfl⟩ : syracuseStep 2707271 = 4060907) B4060907
theorem B1806311 : Blo 1202418 1806311 := bstep (se 1 (by rfl) ⟨1354733, by rfl⟩ : syracuseStep 1806311 = 2709467) B2709467
theorem B2707451 : Blo 1202418 2707451 := bstep (se 1 (by rfl) ⟨2030588, by rfl⟩ : syracuseStep 2707451 = 4061177) B4061177
theorem B1806431 : Blo 1202418 1806431 := bstep (se 1 (by rfl) ⟨1354823, by rfl⟩ : syracuseStep 1806431 = 2709647) B2709647
theorem B4059233 : Blo 1202418 4059233 := bstep (se 2 (by rfl) ⟨1522212, by rfl⟩ : syracuseStep 4059233 = 3044425) B3044425
theorem B2707559 : Blo 1202418 2707559 := bstep (se 1 (by rfl) ⟨2030669, by rfl⟩ : syracuseStep 2707559 = 4061339) B4061339
theorem B1806443 : Blo 1202418 1806443 := bstep (se 1 (by rfl) ⟨1354832, by rfl⟩ : syracuseStep 1806443 = 2709665) B2709665
theorem B2035867 : Blo 1202418 2035867 := bstep (se 1 (by rfl) ⟨1526900, by rfl⟩ : syracuseStep 2035867 = 3053801) B3053801
theorem B1806491 : Blo 1202418 1806491 := bstep (se 1 (by rfl) ⟨1354868, by rfl⟩ : syracuseStep 1806491 = 2709737) B2709737
theorem B2707631 : Blo 1202418 2707631 := bstep (se 1 (by rfl) ⟨2030723, by rfl⟩ : syracuseStep 2707631 = 4061447) B4061447
theorem B19509443 : Blo 1202418 19509443 := bstep (se 1 (by rfl) ⟨14632082, by rfl⟩ : syracuseStep 19509443 = 29264165) B29264165
theorem B4395575 : Blo 1202418 4395575 := bstep (se 1 (by rfl) ⟨3296681, by rfl⟩ : syracuseStep 4395575 = 6593363) B6593363
theorem B5141227 : Blo 1202418 5141227 := bstep (se 1 (by rfl) ⟨3855920, by rfl⟩ : syracuseStep 5141227 = 7711841) B7711841
theorem B2708315 : Blo 1202418 2708315 := bstep (se 1 (by rfl) ⟨2031236, by rfl⟩ : syracuseStep 2708315 = 4062473) B4062473
theorem B37106545 : Blo 1202418 37106545 := bstep (se 2 (by rfl) ⟨13914954, by rfl⟩ : syracuseStep 37106545 = 27829909) B27829909
theorem B11727773 : Blo 1202418 11727773 := bstep (se 3 (by rfl) ⟨2198957, by rfl⟩ : syracuseStep 11727773 = 4397915) B4397915
theorem B2569171 : Blo 1202418 2569171 := bstep (se 1 (by rfl) ⟨1926878, by rfl⟩ : syracuseStep 2569171 = 3853757) B3853757
theorem B9130967 : Blo 1202418 9130967 := bstep (se 1 (by rfl) ⟨6848225, by rfl⟩ : syracuseStep 9130967 = 13696451) B13696451
theorem B43897859 : Blo 1202418 43897859 := bstep (se 1 (by rfl) ⟨32923394, by rfl⟩ : syracuseStep 43897859 = 65846789) B65846789
theorem B13702283 : Blo 1202418 13702283 := bstep (se 1 (by rfl) ⟨10276712, by rfl⟩ : syracuseStep 13702283 = 20553425) B20553425
theorem B3904673 : Blo 1202418 3904673 := bstep (se 2 (by rfl) ⟨1464252, by rfl⟩ : syracuseStep 3904673 = 2928505) B2928505
theorem B17593523 : Blo 1202418 17593523 := bstep (se 1 (by rfl) ⟨13195142, by rfl⟩ : syracuseStep 17593523 = 26390285) B26390285
theorem B3855613 : Blo 1202418 3855613 := bstep (se 3 (by rfl) ⟨722927, by rfl⟩ : syracuseStep 3855613 = 1445855) B1445855
theorem B4060583 : Blo 1202418 4060583 := bstep (se 1 (by rfl) ⟨3045437, by rfl⟩ : syracuseStep 4060583 = 6090875) B6090875
theorem B4568507 : Blo 1202418 4568507 := bstep (se 1 (by rfl) ⟨3426380, by rfl⟩ : syracuseStep 4568507 = 6852761) B6852761
theorem B9131453 : Blo 1202418 9131453 := bstep (se 3 (by rfl) ⟨1712147, by rfl⟩ : syracuseStep 9131453 = 3424295) B3424295
theorem B4060691 : Blo 1202418 4060691 := bstep (se 1 (by rfl) ⟨3045518, by rfl⟩ : syracuseStep 4060691 = 6091037) B6091037
theorem B88036901 : Blo 1202418 88036901 := bstep (se 4 (by rfl) ⟨8253459, by rfl⟩ : syracuseStep 88036901 = 16506919) B16506919
theorem B2709071 : Blo 1202418 2709071 := bstep (se 1 (by rfl) ⟨2031803, by rfl⟩ : syracuseStep 2709071 = 4063607) B4063607
theorem B37533293 : Blo 1202418 37533293 := bstep (se 3 (by rfl) ⟨7037492, by rfl⟩ : syracuseStep 37533293 = 14074985) B14074985
theorem B26024003 : Blo 1202418 26024003 := bstep (se 1 (by rfl) ⟨19518002, by rfl⟩ : syracuseStep 26024003 = 39036005) B39036005
theorem B3045559 : Blo 1202418 3045559 := bstep (se 1 (by rfl) ⟨2284169, by rfl⟩ : syracuseStep 3045559 = 4568339) B4568339
theorem B2029799 : Blo 1202418 2029799 := bstep (se 1 (by rfl) ⟨1522349, by rfl⟩ : syracuseStep 2029799 = 3044699) B3044699
theorem B2709791 : Blo 1202418 2709791 := bstep (se 1 (by rfl) ⟨2032343, by rfl⟩ : syracuseStep 2709791 = 4064687) B4064687
theorem B5486887 : Blo 1202418 5486887 := bstep (se 1 (by rfl) ⟨4115165, by rfl⟩ : syracuseStep 5486887 = 8230331) B8230331
theorem B1202591 : Blo 1202418 1202591 := bstep (se 1 (by rfl) ⟨901943, by rfl⟩ : syracuseStep 1202591 = 1803887) B1803887
theorem B1202639 : Blo 1202418 1202639 := bstep (se 1 (by rfl) ⟨901979, by rfl⟩ : syracuseStep 1202639 = 1803959) B1803959
theorem B9140687 : Blo 1202418 9140687 := bstep (se 1 (by rfl) ⟨6855515, by rfl⟩ : syracuseStep 9140687 = 13711031) B13711031
theorem B1202663 : Blo 1202418 1202663 := bstep (se 1 (by rfl) ⟨901997, by rfl⟩ : syracuseStep 1202663 = 1803995) B1803995
theorem B9755113 : Blo 1202418 9755113 := bstep (se 2 (by rfl) ⟨3658167, by rfl⟩ : syracuseStep 9755113 = 7316335) B7316335
theorem B1202779 : Blo 1202418 1202779 := bstep (se 1 (by rfl) ⟨902084, by rfl⟩ : syracuseStep 1202779 = 1804169) B1804169
theorem B4061825 : Blo 1202418 4061825 := bstep (se 2 (by rfl) ⟨1523184, by rfl⟩ : syracuseStep 4061825 = 3046369) B3046369
theorem B1202847 : Blo 1202418 1202847 := bstep (se 1 (by rfl) ⟨902135, by rfl⟩ : syracuseStep 1202847 = 1804271) B1804271
theorem B1203015 : Blo 1202418 1203015 := bstep (se 1 (by rfl) ⟨902261, by rfl⟩ : syracuseStep 1203015 = 1804523) B1804523
theorem B1203055 : Blo 1202418 1203055 := bstep (se 1 (by rfl) ⟨902291, by rfl⟩ : syracuseStep 1203055 = 1804583) B1804583
theorem B1203111 : Blo 1202418 1203111 := bstep (se 1 (by rfl) ⟨902333, by rfl⟩ : syracuseStep 1203111 = 1804667) B1804667
theorem B1203291 : Blo 1202418 1203291 := bstep (se 1 (by rfl) ⟨902468, by rfl⟩ : syracuseStep 1203291 = 1804937) B1804937
theorem B2030683 : Blo 1202418 2030683 := bstep (se 1 (by rfl) ⟨1523012, by rfl⟩ : syracuseStep 2030683 = 3046025) B3046025
theorem B21961853 : Blo 1202418 21961853 := bstep (se 3 (by rfl) ⟨4117847, by rfl⟩ : syracuseStep 21961853 = 8235695) B8235695
theorem B1203407 : Blo 1202418 1203407 := bstep (se 1 (by rfl) ⟨902555, by rfl⟩ : syracuseStep 1203407 = 1805111) B1805111
theorem B1203431 : Blo 1202418 1203431 := bstep (se 1 (by rfl) ⟨902573, by rfl⟩ : syracuseStep 1203431 = 1805147) B1805147
theorem B1203527 : Blo 1202418 1203527 := bstep (se 1 (by rfl) ⟨902645, by rfl⟩ : syracuseStep 1203527 = 1805291) B1805291
theorem B4062635 : Blo 1202418 4062635 := bstep (se 1 (by rfl) ⟨3046976, by rfl⟩ : syracuseStep 4062635 = 6093953) B6093953
theorem B1203663 : Blo 1202418 1203663 := bstep (se 1 (by rfl) ⟨902747, by rfl⟩ : syracuseStep 1203663 = 1805495) B1805495
theorem B1203823 : Blo 1202418 1203823 := bstep (se 1 (by rfl) ⟨902867, by rfl⟩ : syracuseStep 1203823 = 1805735) B1805735
theorem B1203879 : Blo 1202418 1203879 := bstep (se 1 (by rfl) ⟨902909, by rfl⟩ : syracuseStep 1203879 = 1805819) B1805819
theorem B1203943 : Blo 1202418 1203943 := bstep (se 1 (by rfl) ⟨902957, by rfl⟩ : syracuseStep 1203943 = 1805915) B1805915
theorem B1203999 : Blo 1202418 1203999 := bstep (se 1 (by rfl) ⟨902999, by rfl⟩ : syracuseStep 1203999 = 1805999) B1805999
theorem B4570951 : Blo 1202418 4570951 := bstep (se 1 (by rfl) ⟨3428213, by rfl⟩ : syracuseStep 4570951 = 6856427) B6856427
theorem B2031439 : Blo 1202418 2031439 := bstep (se 1 (by rfl) ⟨1523579, by rfl⟩ : syracuseStep 2031439 = 3047159) B3047159
theorem B1204079 : Blo 1202418 1204079 := bstep (se 1 (by rfl) ⟨903059, by rfl⟩ : syracuseStep 1204079 = 1806119) B1806119
theorem B2031527 : Blo 1202418 2031527 := bstep (se 1 (by rfl) ⟨1523645, by rfl⟩ : syracuseStep 2031527 = 3047291) B3047291
theorem B1204135 : Blo 1202418 1204135 := bstep (se 1 (by rfl) ⟨903101, by rfl⟩ : syracuseStep 1204135 = 1806203) B1806203
theorem B3473351 : Blo 1202418 3473351 := bstep (se 1 (by rfl) ⟨2605013, by rfl⟩ : syracuseStep 3473351 = 5210027) B5210027
theorem B4063175 : Blo 1202418 4063175 := bstep (se 1 (by rfl) ⟨3047381, by rfl⟩ : syracuseStep 4063175 = 6094763) B6094763
theorem B1204287 : Blo 1202418 1204287 := bstep (se 1 (by rfl) ⟨903215, by rfl⟩ : syracuseStep 1204287 = 1806431) B1806431
theorem B1204295 : Blo 1202418 1204295 := bstep (se 1 (by rfl) ⟨903221, by rfl⟩ : syracuseStep 1204295 = 1806443) B1806443
theorem B1204327 : Blo 1202418 1204327 := bstep (se 1 (by rfl) ⟨903245, by rfl⟩ : syracuseStep 1204327 = 1806491) B1806491
theorem B2031871 : Blo 1202418 2031871 := bstep (se 1 (by rfl) ⟨1523903, by rfl⟩ : syracuseStep 2031871 = 3047807) B3047807
theorem B7315849 : Blo 1202418 7315849 := bstep (se 2 (by rfl) ⟨2743443, by rfl⟩ : syracuseStep 7315849 = 5486887) B5486887
theorem B10412461 : Blo 1202418 10412461 := bstep (se 3 (by rfl) ⟨1952336, by rfl⟩ : syracuseStep 10412461 = 3904673) B3904673
theorem B6087311 : Blo 1202418 6087311 := bstep (se 1 (by rfl) ⟨4565483, by rfl⟩ : syracuseStep 6087311 = 9130967) B9130967
theorem B9134855 : Blo 1202418 9134855 := bstep (se 1 (by rfl) ⟨6851141, by rfl⟩ : syracuseStep 9134855 = 13702283) B13702283
theorem B4399933 : Blo 1202418 4399933 := bstep (se 3 (by rfl) ⟨824987, by rfl⟩ : syracuseStep 4399933 = 1649975) B1649975
theorem B3048263 : Blo 1202418 3048263 := bstep (se 1 (by rfl) ⟨2286197, by rfl⟩ : syracuseStep 3048263 = 4572395) B4572395
theorem B6087635 : Blo 1202418 6087635 := bstep (se 1 (by rfl) ⟨4565726, by rfl⟩ : syracuseStep 6087635 = 9131453) B9131453
theorem B6095897 : Blo 1202418 6095897 := bstep (se 2 (by rfl) ⟨2285961, by rfl⟩ : syracuseStep 6095897 = 4571923) B4571923
theorem B3425503 : Blo 1202418 3425503 := bstep (se 1 (by rfl) ⟨2569127, by rfl⟩ : syracuseStep 3425503 = 5138255) B5138255
theorem B3425561 : Blo 1202418 3425561 := bstep (se 2 (by rfl) ⟨1284585, by rfl⟩ : syracuseStep 3425561 = 2569171) B2569171
theorem B6505915 : Blo 1202418 6505915 := bstep (se 1 (by rfl) ⟨4879436, by rfl⟩ : syracuseStep 6505915 = 9758873) B9758873
theorem B1353199 : Blo 1202418 1353199 := bstep (se 1 (by rfl) ⟨1014899, by rfl⟩ : syracuseStep 1353199 = 2029799) B2029799
theorem B1803803 : Blo 1202418 1803803 := bstep (se 1 (by rfl) ⟨1352852, by rfl⟩ : syracuseStep 1803803 = 2705705) B2705705
theorem B4064795 : Blo 1202418 4064795 := bstep (se 1 (by rfl) ⟨3048596, by rfl⟩ : syracuseStep 4064795 = 6097193) B6097193
theorem B1804187 : Blo 1202418 1804187 := bstep (se 1 (by rfl) ⟨1353140, by rfl⟩ : syracuseStep 1804187 = 2706281) B2706281
theorem B1804223 : Blo 1202418 1804223 := bstep (se 1 (by rfl) ⟨1353167, by rfl⟩ : syracuseStep 1804223 = 2706335) B2706335
theorem B14641235 : Blo 1202418 14641235 := bstep (se 1 (by rfl) ⟨10980926, by rfl⟩ : syracuseStep 14641235 = 21961853) B21961853
theorem B19531961 : Blo 1202418 19531961 := bstep (se 2 (by rfl) ⟨7324485, by rfl⟩ : syracuseStep 19531961 = 14648971) B14648971
theorem B1804847 : Blo 1202418 1804847 := bstep (se 1 (by rfl) ⟨1353635, by rfl⟩ : syracuseStep 1804847 = 2707271) B2707271
theorem B1354351 : Blo 1202418 1354351 := bstep (se 1 (by rfl) ⟨1015763, by rfl⟩ : syracuseStep 1354351 = 2031527) B2031527
theorem B1804967 : Blo 1202418 1804967 := bstep (se 1 (by rfl) ⟨1353725, by rfl⟩ : syracuseStep 1804967 = 2707451) B2707451
theorem B1805033 : Blo 1202418 1805033 := bstep (se 2 (by rfl) ⟨676887, by rfl⟩ : syracuseStep 1805033 = 1353775) B1353775
theorem B2706155 : Blo 1202418 2706155 := bstep (se 1 (by rfl) ⟨2029616, by rfl⟩ : syracuseStep 2706155 = 4059233) B4059233
theorem B1805039 : Blo 1202418 1805039 := bstep (se 1 (by rfl) ⟨1353779, by rfl⟩ : syracuseStep 1805039 = 2707559) B2707559
theorem B1805087 : Blo 1202418 1805087 := bstep (se 1 (by rfl) ⟨1353815, by rfl⟩ : syracuseStep 1805087 = 2707631) B2707631
theorem B1354567 : Blo 1202418 1354567 := bstep (se 1 (by rfl) ⟨1015925, by rfl⟩ : syracuseStep 1354567 = 2031851) B2031851
theorem B2714489 : Blo 1202418 2714489 := bstep (se 2 (by rfl) ⟨1017933, by rfl⟩ : syracuseStep 2714489 = 2035867) B2035867
theorem B1805417 : Blo 1202418 1805417 := bstep (se 2 (by rfl) ⟨677031, by rfl⟩ : syracuseStep 1805417 = 1354063) B1354063
theorem B1805543 : Blo 1202418 1805543 := bstep (se 1 (by rfl) ⟨1354157, by rfl⟩ : syracuseStep 1805543 = 2708315) B2708315
theorem B7818515 : Blo 1202418 7818515 := bstep (se 1 (by rfl) ⟨5863886, by rfl⟩ : syracuseStep 7818515 = 11727773) B11727773
theorem B1928519 : Blo 1202418 1928519 := bstep (se 1 (by rfl) ⟨1446389, by rfl⟩ : syracuseStep 1928519 = 2892779) B2892779
theorem B29265239 : Blo 1202418 29265239 := bstep (se 1 (by rfl) ⟨21948929, by rfl⟩ : syracuseStep 29265239 = 43897859) B43897859
theorem B9137771 : Blo 1202418 9137771 := bstep (se 1 (by rfl) ⟨6853328, by rfl⟩ : syracuseStep 9137771 = 13706657) B13706657
theorem B2707055 : Blo 1202418 2707055 := bstep (se 1 (by rfl) ⟨2030291, by rfl⟩ : syracuseStep 2707055 = 4060583) B4060583
theorem B2707127 : Blo 1202418 2707127 := bstep (se 1 (by rfl) ⟨2030345, by rfl⟩ : syracuseStep 2707127 = 4060691) B4060691
theorem B58691267 : Blo 1202418 58691267 := bstep (se 1 (by rfl) ⟨44018450, by rfl⟩ : syracuseStep 58691267 = 88036901) B88036901
theorem B1806047 : Blo 1202418 1806047 := bstep (se 1 (by rfl) ⟨1354535, by rfl⟩ : syracuseStep 1806047 = 2709071) B2709071
theorem B25022195 : Blo 1202418 25022195 := bstep (se 1 (by rfl) ⟨18766646, by rfl⟩ : syracuseStep 25022195 = 37533293) B37533293
theorem B49475393 : Blo 1202418 49475393 := bstep (se 2 (by rfl) ⟨18553272, by rfl⟩ : syracuseStep 49475393 = 37106545) B37106545
theorem B1806329 : Blo 1202418 1806329 := bstep (se 2 (by rfl) ⟨677373, by rfl⟩ : syracuseStep 1806329 = 1354747) B1354747
theorem B15634529 : Blo 1202418 15634529 := bstep (se 2 (by rfl) ⟨5862948, by rfl⟩ : syracuseStep 15634529 = 11725897) B11725897
theorem B2707577 : Blo 1202418 2707577 := bstep (se 2 (by rfl) ⟨1015341, by rfl⟩ : syracuseStep 2707577 = 2030683) B2030683
theorem B1806527 : Blo 1202418 1806527 := bstep (se 1 (by rfl) ⟨1354895, by rfl⟩ : syracuseStep 1806527 = 2709791) B2709791
theorem B1806569 : Blo 1202418 1806569 := bstep (se 2 (by rfl) ⟨677463, by rfl⟩ : syracuseStep 1806569 = 1354927) B1354927
theorem B5140817 : Blo 1202418 5140817 := bstep (se 2 (by rfl) ⟨1927806, by rfl⟩ : syracuseStep 5140817 = 3855613) B3855613
theorem B2707883 : Blo 1202418 2707883 := bstep (se 1 (by rfl) ⟨2030912, by rfl⟩ : syracuseStep 2707883 = 4061825) B4061825
theorem B2568871 : Blo 1202418 2568871 := bstep (se 1 (by rfl) ⟨1926653, by rfl⟩ : syracuseStep 2568871 = 3853307) B3853307
theorem B13898429 : Blo 1202418 13898429 := bstep (se 3 (by rfl) ⟨2605955, by rfl⟩ : syracuseStep 13898429 = 5211911) B5211911
theorem B2568991 : Blo 1202418 2568991 := bstep (se 1 (by rfl) ⟨1926743, by rfl⟩ : syracuseStep 2568991 = 3853487) B3853487
theorem B15643469 : Blo 1202418 15643469 := bstep (se 3 (by rfl) ⟨2933150, by rfl⟩ : syracuseStep 15643469 = 5866301) B5866301
theorem B3044263 : Blo 1202418 3044263 := bstep (se 1 (by rfl) ⟨2283197, by rfl⟩ : syracuseStep 3044263 = 4566395) B4566395
theorem B2708423 : Blo 1202418 2708423 := bstep (se 1 (by rfl) ⟨2031317, by rfl⟩ : syracuseStep 2708423 = 4062635) B4062635
theorem B6173651 : Blo 1202418 6173651 := bstep (se 1 (by rfl) ⟨4630238, by rfl⟩ : syracuseStep 6173651 = 9260477) B9260477
theorem B20575295 : Blo 1202418 20575295 := bstep (se 1 (by rfl) ⟨15431471, by rfl⟩ : syracuseStep 20575295 = 30862943) B30862943
theorem B2708585 : Blo 1202418 2708585 := bstep (se 2 (by rfl) ⟨1015719, by rfl⟩ : syracuseStep 2708585 = 2031439) B2031439
theorem B2315567 : Blo 1202418 2315567 := bstep (se 1 (by rfl) ⟨1736675, by rfl⟩ : syracuseStep 2315567 = 3473351) B3473351
theorem B2708783 : Blo 1202418 2708783 := bstep (se 1 (by rfl) ⟨2031587, by rfl⟩ : syracuseStep 2708783 = 4063175) B4063175
theorem B13006295 : Blo 1202418 13006295 := bstep (se 1 (by rfl) ⟨9754721, by rfl⟩ : syracuseStep 13006295 = 19509443) B19509443
theorem B4232663 : Blo 1202418 4232663 := bstep (se 1 (by rfl) ⟨3174497, by rfl⟩ : syracuseStep 4232663 = 6348995) B6348995
theorem B4060745 : Blo 1202418 4060745 := bstep (se 2 (by rfl) ⟨1522779, by rfl⟩ : syracuseStep 4060745 = 3045559) B3045559
theorem B2930383 : Blo 1202418 2930383 := bstep (se 1 (by rfl) ⟨2197787, by rfl⟩ : syracuseStep 2930383 = 4395575) B4395575
theorem B2709215 : Blo 1202418 2709215 := bstep (se 1 (by rfl) ⟨2031911, by rfl⟩ : syracuseStep 2709215 = 4063823) B4063823
theorem B13006817 : Blo 1202418 13006817 := bstep (se 2 (by rfl) ⟨4877556, by rfl⟩ : syracuseStep 13006817 = 9755113) B9755113
theorem B52762691 : Blo 1202418 52762691 := bstep (se 1 (by rfl) ⟨39572018, by rfl⟩ : syracuseStep 52762691 = 79144037) B79144037
theorem B2709575 : Blo 1202418 2709575 := bstep (se 1 (by rfl) ⟨2032181, by rfl⟩ : syracuseStep 2709575 = 4064363) B4064363
theorem B11729015 : Blo 1202418 11729015 := bstep (se 1 (by rfl) ⟨8796761, by rfl⟩ : syracuseStep 11729015 = 17593523) B17593523
theorem B11557079 : Blo 1202418 11557079 := bstep (se 1 (by rfl) ⟨8667809, by rfl⟩ : syracuseStep 11557079 = 17335619) B17335619
theorem B1202459 : Blo 1202418 1202459 := bstep (se 1 (by rfl) ⟨901844, by rfl⟩ : syracuseStep 1202459 = 1803689) B1803689
theorem B3045671 : Blo 1202418 3045671 := bstep (se 1 (by rfl) ⟨2284253, by rfl⟩ : syracuseStep 3045671 = 4568507) B4568507
theorem B6854969 : Blo 1202418 6854969 := bstep (se 2 (by rfl) ⟨2570613, by rfl⟩ : syracuseStep 6854969 = 5141227) B5141227
theorem B17357125 : Blo 1202418 17357125 := bstep (se 4 (by rfl) ⟨1627230, by rfl⟩ : syracuseStep 17357125 = 3254461) B3254461
theorem B1202559 : Blo 1202418 1202559 := bstep (se 1 (by rfl) ⟨901919, by rfl⟩ : syracuseStep 1202559 = 1803839) B1803839
theorem B1202587 : Blo 1202418 1202587 := bstep (se 1 (by rfl) ⟨901940, by rfl⟩ : syracuseStep 1202587 = 1803881) B1803881
theorem B8239745 : Blo 1202418 8239745 := bstep (se 2 (by rfl) ⟨3089904, by rfl⟩ : syracuseStep 8239745 = 6179809) B6179809
theorem B1202879 : Blo 1202418 1202879 := bstep (se 1 (by rfl) ⟨902159, by rfl⟩ : syracuseStep 1202879 = 1804319) B1804319
theorem B17349335 : Blo 1202418 17349335 := bstep (se 1 (by rfl) ⟨13012001, by rfl⟩ : syracuseStep 17349335 = 26024003) B26024003
theorem B1284859 : Blo 1202418 1284859 := bstep (se 1 (by rfl) ⟨963644, by rfl⟩ : syracuseStep 1284859 = 1927289) B1927289
theorem B1203007 : Blo 1202418 1203007 := bstep (se 1 (by rfl) ⟨902255, by rfl⟩ : syracuseStep 1203007 = 1804511) B1804511
theorem B1203047 : Blo 1202418 1203047 := bstep (se 1 (by rfl) ⟨902285, by rfl⟩ : syracuseStep 1203047 = 1804571) B1804571
theorem B9132911 : Blo 1202418 9132911 := bstep (se 1 (by rfl) ⟨6849683, by rfl⟩ : syracuseStep 9132911 = 13699367) B13699367
theorem B6093791 : Blo 1202418 6093791 := bstep (se 1 (by rfl) ⟨4570343, by rfl⟩ : syracuseStep 6093791 = 9140687) B9140687
theorem B1203263 : Blo 1202418 1203263 := bstep (se 1 (by rfl) ⟨902447, by rfl⟩ : syracuseStep 1203263 = 1804895) B1804895
theorem B1203451 : Blo 1202418 1203451 := bstep (se 1 (by rfl) ⟨902588, by rfl⟩ : syracuseStep 1203451 = 1805177) B1805177
theorem B1203483 : Blo 1202418 1203483 := bstep (se 1 (by rfl) ⟨902612, by rfl⟩ : syracuseStep 1203483 = 1805225) B1805225
theorem B1203583 : Blo 1202418 1203583 := bstep (se 1 (by rfl) ⟨902687, by rfl⟩ : syracuseStep 1203583 = 1805375) B1805375
theorem B1203951 : Blo 1202418 1203951 := bstep (se 1 (by rfl) ⟨902963, by rfl⟩ : syracuseStep 1203951 = 1805927) B1805927
theorem B6094601 : Blo 1202418 6094601 := bstep (se 2 (by rfl) ⟨2285475, by rfl⟩ : syracuseStep 6094601 = 4570951) B4570951
theorem B1204207 : Blo 1202418 1204207 := bstep (se 1 (by rfl) ⟨903155, by rfl⟩ : syracuseStep 1204207 = 1806311) B1806311
theorem B1204351 : Blo 1202418 1204351 := bstep (se 1 (by rfl) ⟨903263, by rfl⟩ : syracuseStep 1204351 = 1806527) B1806527
theorem B1204379 : Blo 1202418 1204379 := bstep (se 1 (by rfl) ⟨903284, by rfl⟩ : syracuseStep 1204379 = 1806569) B1806569
theorem B23142833 : Blo 1202418 23142833 := bstep (se 2 (by rfl) ⟨8678562, by rfl⟩ : syracuseStep 23142833 = 17357125) B17357125
theorem B9265619 : Blo 1202418 9265619 := bstep (se 1 (by rfl) ⟨6949214, by rfl⟩ : syracuseStep 9265619 = 13898429) B13898429
theorem B2032175 : Blo 1202418 2032175 := bstep (se 1 (by rfl) ⟨1524131, by rfl⟩ : syracuseStep 2032175 = 3048263) B3048263
theorem B4063931 : Blo 1202418 4063931 := bstep (se 1 (by rfl) ⟨3047948, by rfl⟩ : syracuseStep 4063931 = 6095897) B6095897
theorem B3425161 : Blo 1202418 3425161 := bstep (se 2 (by rfl) ⟨1284435, by rfl⟩ : syracuseStep 3425161 = 2568871) B2568871
theorem B1713145 : Blo 1202418 1713145 := bstep (se 2 (by rfl) ⟨642429, by rfl⟩ : syracuseStep 1713145 = 1284859) B1284859
theorem B3425321 : Blo 1202418 3425321 := bstep (se 2 (by rfl) ⟨1284495, by rfl⟩ : syracuseStep 3425321 = 2568991) B2568991
theorem B5866577 : Blo 1202418 5866577 := bstep (se 2 (by rfl) ⟨2199966, by rfl⟩ : syracuseStep 5866577 = 4399933) B4399933
theorem B21972653 : Blo 1202418 21972653 := bstep (se 3 (by rfl) ⟨4119872, by rfl⟩ : syracuseStep 21972653 = 8239745) B8239745
theorem B1804103 : Blo 1202418 1804103 := bstep (se 1 (by rfl) ⟨1353077, by rfl⟩ : syracuseStep 1804103 = 2706155) B2706155
theorem B6088607 : Blo 1202418 6088607 := bstep (se 1 (by rfl) ⟨4566455, by rfl⟩ : syracuseStep 6088607 = 9132911) B9132911
theorem B1804265 : Blo 1202418 1804265 := bstep (se 2 (by rfl) ⟨676599, by rfl⟩ : syracuseStep 1804265 = 1353199) B1353199
theorem B5212343 : Blo 1202418 5212343 := bstep (se 1 (by rfl) ⟨3909257, by rfl⟩ : syracuseStep 5212343 = 7818515) B7818515
theorem B41715917 : Blo 1202418 41715917 := bstep (se 3 (by rfl) ⟨7821734, by rfl⟩ : syracuseStep 41715917 = 15643469) B15643469
theorem B1804703 : Blo 1202418 1804703 := bstep (se 1 (by rfl) ⟨1353527, by rfl⟩ : syracuseStep 1804703 = 2707055) B2707055
theorem B1804751 : Blo 1202418 1804751 := bstep (se 1 (by rfl) ⟨1353563, by rfl⟩ : syracuseStep 1804751 = 2707127) B2707127
theorem B39127511 : Blo 1202418 39127511 := bstep (se 1 (by rfl) ⟨29345633, by rfl⟩ : syracuseStep 39127511 = 58691267) B58691267
theorem B16681463 : Blo 1202418 16681463 := bstep (se 1 (by rfl) ⟨12511097, by rfl⟩ : syracuseStep 16681463 = 25022195) B25022195
theorem B32983595 : Blo 1202418 32983595 := bstep (se 1 (by rfl) ⟨24737696, by rfl⟩ : syracuseStep 32983595 = 49475393) B49475393
theorem B10423019 : Blo 1202418 10423019 := bstep (se 1 (by rfl) ⟨7817264, by rfl⟩ : syracuseStep 10423019 = 15634529) B15634529
theorem B1805051 : Blo 1202418 1805051 := bstep (se 1 (by rfl) ⟨1353788, by rfl⟩ : syracuseStep 1805051 = 2707577) B2707577
theorem B140700509 : Blo 1202418 140700509 := bstep (se 3 (by rfl) ⟨26381345, by rfl⟩ : syracuseStep 140700509 = 52762691) B52762691
theorem B3427211 : Blo 1202418 3427211 := bstep (se 1 (by rfl) ⟨2570408, by rfl⟩ : syracuseStep 3427211 = 5140817) B5140817
theorem B1805255 : Blo 1202418 1805255 := bstep (se 1 (by rfl) ⟨1353941, by rfl⟩ : syracuseStep 1805255 = 2707883) B2707883
theorem B4058207 : Blo 1202418 4058207 := bstep (se 1 (by rfl) ⟨3043655, by rfl⟩ : syracuseStep 4058207 = 6087311) B6087311
theorem B6089903 : Blo 1202418 6089903 := bstep (se 1 (by rfl) ⟨4567427, by rfl⟩ : syracuseStep 6089903 = 9134855) B9134855
theorem B1805615 : Blo 1202418 1805615 := bstep (se 1 (by rfl) ⟨1354211, by rfl⟩ : syracuseStep 1805615 = 2708423) B2708423
theorem B4058423 : Blo 1202418 4058423 := bstep (se 1 (by rfl) ⟨3043817, by rfl⟩ : syracuseStep 4058423 = 6087635) B6087635
theorem B4115767 : Blo 1202418 4115767 := bstep (se 1 (by rfl) ⟨3086825, by rfl⟩ : syracuseStep 4115767 = 6173651) B6173651
theorem B13716863 : Blo 1202418 13716863 := bstep (se 1 (by rfl) ⟨10287647, by rfl⟩ : syracuseStep 13716863 = 20575295) B20575295
theorem B1805723 : Blo 1202418 1805723 := bstep (se 1 (by rfl) ⟨1354292, by rfl⟩ : syracuseStep 1805723 = 2708585) B2708585
theorem B1805801 : Blo 1202418 1805801 := bstep (se 2 (by rfl) ⟨677175, by rfl⟩ : syracuseStep 1805801 = 1354351) B1354351
theorem B1543711 : Blo 1202418 1543711 := bstep (se 1 (by rfl) ⟨1157783, by rfl⟩ : syracuseStep 1543711 = 2315567) B2315567
theorem B1805855 : Blo 1202418 1805855 := bstep (se 1 (by rfl) ⟨1354391, by rfl⟩ : syracuseStep 1805855 = 2708783) B2708783
theorem B8670863 : Blo 1202418 8670863 := bstep (se 1 (by rfl) ⟨6503147, by rfl⟩ : syracuseStep 8670863 = 13006295) B13006295
theorem B2821775 : Blo 1202418 2821775 := bstep (se 1 (by rfl) ⟨2116331, by rfl⟩ : syracuseStep 2821775 = 4232663) B4232663
theorem B2707163 : Blo 1202418 2707163 := bstep (se 1 (by rfl) ⟨2030372, by rfl⟩ : syracuseStep 2707163 = 4060745) B4060745
theorem B1806089 : Blo 1202418 1806089 := bstep (se 2 (by rfl) ⟨677283, by rfl⟩ : syracuseStep 1806089 = 1354567) B1354567
theorem B1806143 : Blo 1202418 1806143 := bstep (se 1 (by rfl) ⟨1354607, by rfl⟩ : syracuseStep 1806143 = 2709215) B2709215
theorem B4059017 : Blo 1202418 4059017 := bstep (se 2 (by rfl) ⟨1522131, by rfl⟩ : syracuseStep 4059017 = 3044263) B3044263
theorem B8671211 : Blo 1202418 8671211 := bstep (se 1 (by rfl) ⟨6503408, by rfl⟩ : syracuseStep 8671211 = 13006817) B13006817
theorem B1806383 : Blo 1202418 1806383 := bstep (se 1 (by rfl) ⟨1354787, by rfl⟩ : syracuseStep 1806383 = 2709575) B2709575
theorem B9760823 : Blo 1202418 9760823 := bstep (se 1 (by rfl) ⟨7320617, by rfl⟩ : syracuseStep 9760823 = 14641235) B14641235
theorem B7819343 : Blo 1202418 7819343 := bstep (se 1 (by rfl) ⟨5864507, by rfl⟩ : syracuseStep 7819343 = 11729015) B11729015
theorem B13021307 : Blo 1202418 13021307 := bstep (se 1 (by rfl) ⟨9765980, by rfl⟩ : syracuseStep 13021307 = 19531961) B19531961
theorem B7704719 : Blo 1202418 7704719 := bstep (se 1 (by rfl) ⟨5778539, by rfl⟩ : syracuseStep 7704719 = 11557079) B11557079
theorem B4567337 : Blo 1202418 4567337 := bstep (se 2 (by rfl) ⟨1712751, by rfl⟩ : syracuseStep 4567337 = 3425503) B3425503
theorem B19510159 : Blo 1202418 19510159 := bstep (se 1 (by rfl) ⟨14632619, by rfl⟩ : syracuseStep 19510159 = 29265239) B29265239
theorem B6091847 : Blo 1202418 6091847 := bstep (se 1 (by rfl) ⟨4568885, by rfl⟩ : syracuseStep 6091847 = 9137771) B9137771
theorem B2709161 : Blo 1202418 2709161 := bstep (se 2 (by rfl) ⟨1015935, by rfl⟩ : syracuseStep 2709161 = 2031871) B2031871
theorem B9754465 : Blo 1202418 9754465 := bstep (se 2 (by rfl) ⟨3657924, by rfl⟩ : syracuseStep 9754465 = 7315849) B7315849
theorem B13883281 : Blo 1202418 13883281 := bstep (se 2 (by rfl) ⟨5206230, by rfl⟩ : syracuseStep 13883281 = 10412461) B10412461
theorem B2283707 : Blo 1202418 2283707 := bstep (se 1 (by rfl) ⟨1712780, by rfl⟩ : syracuseStep 2283707 = 3425561) B3425561
theorem B1202535 : Blo 1202418 1202535 := bstep (se 1 (by rfl) ⟨901901, by rfl⟩ : syracuseStep 1202535 = 1803803) B1803803
theorem B2709863 : Blo 1202418 2709863 := bstep (se 1 (by rfl) ⟨2032397, by rfl⟩ : syracuseStep 2709863 = 4064795) B4064795
theorem B15628709 : Blo 1202418 15628709 := bstep (se 4 (by rfl) ⟨1465191, by rfl⟩ : syracuseStep 15628709 = 2930383) B2930383
theorem B1202791 : Blo 1202418 1202791 := bstep (se 1 (by rfl) ⟨902093, by rfl⟩ : syracuseStep 1202791 = 1804187) B1804187
theorem B1202815 : Blo 1202418 1202815 := bstep (se 1 (by rfl) ⟨902111, by rfl⟩ : syracuseStep 1202815 = 1804223) B1804223
theorem B2030447 : Blo 1202418 2030447 := bstep (se 1 (by rfl) ⟨1522835, by rfl⟩ : syracuseStep 2030447 = 3045671) B3045671
theorem B4569979 : Blo 1202418 4569979 := bstep (se 1 (by rfl) ⟨3427484, by rfl⟩ : syracuseStep 4569979 = 6854969) B6854969
theorem B1203231 : Blo 1202418 1203231 := bstep (se 1 (by rfl) ⟨902423, by rfl⟩ : syracuseStep 1203231 = 1804847) B1804847
theorem B1203311 : Blo 1202418 1203311 := bstep (se 1 (by rfl) ⟨902483, by rfl⟩ : syracuseStep 1203311 = 1804967) B1804967
theorem B11566223 : Blo 1202418 11566223 := bstep (se 1 (by rfl) ⟨8674667, by rfl⟩ : syracuseStep 11566223 = 17349335) B17349335
theorem B1203355 : Blo 1202418 1203355 := bstep (se 1 (by rfl) ⟨902516, by rfl⟩ : syracuseStep 1203355 = 1805033) B1805033
theorem B1203359 : Blo 1202418 1203359 := bstep (se 1 (by rfl) ⟨902519, by rfl⟩ : syracuseStep 1203359 = 1805039) B1805039
theorem B1203391 : Blo 1202418 1203391 := bstep (se 1 (by rfl) ⟨902543, by rfl⟩ : syracuseStep 1203391 = 1805087) B1805087
theorem B8674553 : Blo 1202418 8674553 := bstep (se 2 (by rfl) ⟨3252957, by rfl⟩ : syracuseStep 8674553 = 6505915) B6505915
theorem B1809659 : Blo 1202418 1809659 := bstep (se 1 (by rfl) ⟨1357244, by rfl⟩ : syracuseStep 1809659 = 2714489) B2714489
theorem B4062527 : Blo 1202418 4062527 := bstep (se 1 (by rfl) ⟨3046895, by rfl⟩ : syracuseStep 4062527 = 6093791) B6093791
theorem B1203611 : Blo 1202418 1203611 := bstep (se 1 (by rfl) ⟨902708, by rfl⟩ : syracuseStep 1203611 = 1805417) B1805417
theorem B1203695 : Blo 1202418 1203695 := bstep (se 1 (by rfl) ⟨902771, by rfl⟩ : syracuseStep 1203695 = 1805543) B1805543
theorem B1285679 : Blo 1202418 1285679 := bstep (se 1 (by rfl) ⟨964259, by rfl⟩ : syracuseStep 1285679 = 1928519) B1928519
theorem B1204031 : Blo 1202418 1204031 := bstep (se 1 (by rfl) ⟨903023, by rfl⟩ : syracuseStep 1204031 = 1806047) B1806047
theorem B4063067 : Blo 1202418 4063067 := bstep (se 1 (by rfl) ⟨3047300, by rfl⟩ : syracuseStep 4063067 = 6094601) B6094601
theorem B1204219 : Blo 1202418 1204219 := bstep (se 1 (by rfl) ⟨903164, by rfl⟩ : syracuseStep 1204219 = 1806329) B1806329
theorem B1204255 : Blo 1202418 1204255 := bstep (se 1 (by rfl) ⟨903191, by rfl⟩ : syracuseStep 1204255 = 1806383) B1806383
theorem B5136479 : Blo 1202418 5136479 := bstep (se 1 (by rfl) ⟨3852359, by rfl⟩ : syracuseStep 5136479 = 7704719) B7704719
theorem B6177079 : Blo 1202418 6177079 := bstep (se 1 (by rfl) ⟨4632809, by rfl⟩ : syracuseStep 6177079 = 9265619) B9265619
theorem B4825757 : Blo 1202418 4825757 := bstep (se 3 (by rfl) ⟨904829, by rfl⟩ : syracuseStep 4825757 = 1809659) B1809659
theorem B14648435 : Blo 1202418 14648435 := bstep (se 1 (by rfl) ⟨10986326, by rfl⟩ : syracuseStep 14648435 = 21972653) B21972653
theorem B3474895 : Blo 1202418 3474895 := bstep (se 1 (by rfl) ⟨2606171, by rfl⟩ : syracuseStep 3474895 = 5212343) B5212343
theorem B26085007 : Blo 1202418 26085007 := bstep (se 1 (by rfl) ⟨19563755, by rfl⟩ : syracuseStep 26085007 = 39127511) B39127511
theorem B21989063 : Blo 1202418 21989063 := bstep (se 1 (by rfl) ⟨16491797, by rfl⟩ : syracuseStep 21989063 = 32983595) B32983595
theorem B93800339 : Blo 1202418 93800339 := bstep (se 1 (by rfl) ⟨70350254, by rfl⟩ : syracuseStep 93800339 = 140700509) B140700509
theorem B1353631 : Blo 1202418 1353631 := bstep (se 1 (by rfl) ⟨1015223, by rfl⟩ : syracuseStep 1353631 = 2030447) B2030447
theorem B2058281 : Blo 1202418 2058281 := bstep (se 2 (by rfl) ⟨771855, by rfl⟩ : syracuseStep 2058281 = 1543711) B1543711
theorem B2705471 : Blo 1202418 2705471 := bstep (se 1 (by rfl) ⟨2029103, by rfl⟩ : syracuseStep 2705471 = 4058207) B4058207
theorem B7710815 : Blo 1202418 7710815 := bstep (se 1 (by rfl) ⟨5783111, by rfl⟩ : syracuseStep 7710815 = 11566223) B11566223
theorem B2705615 : Blo 1202418 2705615 := bstep (se 1 (by rfl) ⟨2029211, by rfl⟩ : syracuseStep 2705615 = 4058423) B4058423
theorem B9144575 : Blo 1202418 9144575 := bstep (se 1 (by rfl) ⟨6858431, by rfl⟩ : syracuseStep 9144575 = 13716863) B13716863
theorem B1804775 : Blo 1202418 1804775 := bstep (se 1 (by rfl) ⟨1353581, by rfl⟩ : syracuseStep 1804775 = 2707163) B2707163
theorem B2706011 : Blo 1202418 2706011 := bstep (se 1 (by rfl) ⟨2029508, by rfl⟩ : syracuseStep 2706011 = 4059017) B4059017
theorem B6507215 : Blo 1202418 6507215 := bstep (se 1 (by rfl) ⟨4880411, by rfl⟩ : syracuseStep 6507215 = 9760823) B9760823
theorem B5212895 : Blo 1202418 5212895 := bstep (se 1 (by rfl) ⟨3909671, by rfl⟩ : syracuseStep 5212895 = 7819343) B7819343
theorem B15428555 : Blo 1202418 15428555 := bstep (se 1 (by rfl) ⟨11571416, by rfl⟩ : syracuseStep 15428555 = 23142833) B23142833
theorem B1354783 : Blo 1202418 1354783 := bstep (se 1 (by rfl) ⟨1016087, by rfl⟩ : syracuseStep 1354783 = 2032175) B2032175
theorem B3911051 : Blo 1202418 3911051 := bstep (se 1 (by rfl) ⟨2933288, by rfl⟩ : syracuseStep 3911051 = 5866577) B5866577
theorem B1806107 : Blo 1202418 1806107 := bstep (se 1 (by rfl) ⟨1354580, by rfl⟩ : syracuseStep 1806107 = 2709161) B2709161
theorem B4566881 : Blo 1202418 4566881 := bstep (se 2 (by rfl) ⟨1712580, by rfl⟩ : syracuseStep 4566881 = 3425161) B3425161
theorem B26013545 : Blo 1202418 26013545 := bstep (se 2 (by rfl) ⟨9755079, by rfl⟩ : syracuseStep 26013545 = 19510159) B19510159
theorem B4059071 : Blo 1202418 4059071 := bstep (se 1 (by rfl) ⟨3044303, by rfl⟩ : syracuseStep 4059071 = 6088607) B6088607
theorem B3428477 : Blo 1202418 3428477 := bstep (se 3 (by rfl) ⟨642839, by rfl⟩ : syracuseStep 3428477 = 1285679) B1285679
theorem B1806575 : Blo 1202418 1806575 := bstep (se 1 (by rfl) ⟨1354931, by rfl⟩ : syracuseStep 1806575 = 2709863) B2709863
theorem B11120975 : Blo 1202418 11120975 := bstep (se 1 (by rfl) ⟨8340731, by rfl⟩ : syracuseStep 11120975 = 16681463) B16681463
theorem B7524733 : Blo 1202418 7524733 := bstep (se 3 (by rfl) ⟨1410887, by rfl⟩ : syracuseStep 7524733 = 2821775) B2821775
theorem B74044165 : Blo 1202418 74044165 := bstep (se 4 (by rfl) ⟨6941640, by rfl⟩ : syracuseStep 74044165 = 13883281) B13883281
theorem B4059935 : Blo 1202418 4059935 := bstep (se 1 (by rfl) ⟨3044951, by rfl⟩ : syracuseStep 4059935 = 6089903) B6089903
theorem B2708351 : Blo 1202418 2708351 := bstep (se 1 (by rfl) ⟨2031263, by rfl⟩ : syracuseStep 2708351 = 4062527) B4062527
theorem B9139229 : Blo 1202418 9139229 := bstep (se 3 (by rfl) ⟨1713605, by rfl⟩ : syracuseStep 9139229 = 3427211) B3427211
theorem B5780575 : Blo 1202418 5780575 := bstep (se 1 (by rfl) ⟨4335431, by rfl⟩ : syracuseStep 5780575 = 8670863) B8670863
theorem B13005953 : Blo 1202418 13005953 := bstep (se 2 (by rfl) ⟨4877232, by rfl⟩ : syracuseStep 13005953 = 9754465) B9754465
theorem B2708711 : Blo 1202418 2708711 := bstep (se 1 (by rfl) ⟨2031533, by rfl⟩ : syracuseStep 2708711 = 4063067) B4063067
theorem B5780807 : Blo 1202418 5780807 := bstep (se 1 (by rfl) ⟨4335605, by rfl⟩ : syracuseStep 5780807 = 8671211) B8671211
theorem B8680871 : Blo 1202418 8680871 := bstep (se 1 (by rfl) ⟨6510653, by rfl⟩ : syracuseStep 8680871 = 13021307) B13021307
theorem B3044891 : Blo 1202418 3044891 := bstep (se 1 (by rfl) ⟨2283668, by rfl⟩ : syracuseStep 3044891 = 4567337) B4567337
theorem B2709287 : Blo 1202418 2709287 := bstep (se 1 (by rfl) ⟨2031965, by rfl⟩ : syracuseStep 2709287 = 4063931) B4063931
theorem B23132141 : Blo 1202418 23132141 := bstep (se 3 (by rfl) ⟨4337276, by rfl⟩ : syracuseStep 23132141 = 8674553) B8674553
theorem B2283547 : Blo 1202418 2283547 := bstep (se 1 (by rfl) ⟨1712660, by rfl⟩ : syracuseStep 2283547 = 3425321) B3425321
theorem B4061231 : Blo 1202418 4061231 := bstep (se 1 (by rfl) ⟨3045923, by rfl⟩ : syracuseStep 4061231 = 6091847) B6091847
theorem B6093305 : Blo 1202418 6093305 := bstep (se 2 (by rfl) ⟨2284989, by rfl⟩ : syracuseStep 6093305 = 4569979) B4569979
theorem B1202735 : Blo 1202418 1202735 := bstep (se 1 (by rfl) ⟨902051, by rfl⟩ : syracuseStep 1202735 = 1804103) B1804103
theorem B1202843 : Blo 1202418 1202843 := bstep (se 1 (by rfl) ⟨902132, by rfl⟩ : syracuseStep 1202843 = 1804265) B1804265
theorem B2284193 : Blo 1202418 2284193 := bstep (se 2 (by rfl) ⟨856572, by rfl⟩ : syracuseStep 2284193 = 1713145) B1713145
theorem B1522471 : Blo 1202418 1522471 := bstep (se 1 (by rfl) ⟨1141853, by rfl⟩ : syracuseStep 1522471 = 2283707) B2283707
theorem B27810611 : Blo 1202418 27810611 := bstep (se 1 (by rfl) ⟨20857958, by rfl⟩ : syracuseStep 27810611 = 41715917) B41715917
theorem B1203135 : Blo 1202418 1203135 := bstep (se 1 (by rfl) ⟨902351, by rfl⟩ : syracuseStep 1203135 = 1804703) B1804703
theorem B10419139 : Blo 1202418 10419139 := bstep (se 1 (by rfl) ⟨7814354, by rfl⟩ : syracuseStep 10419139 = 15628709) B15628709
theorem B1203167 : Blo 1202418 1203167 := bstep (se 1 (by rfl) ⟨902375, by rfl⟩ : syracuseStep 1203167 = 1804751) B1804751
theorem B5487689 : Blo 1202418 5487689 := bstep (se 2 (by rfl) ⟨2057883, by rfl⟩ : syracuseStep 5487689 = 4115767) B4115767
theorem B1203367 : Blo 1202418 1203367 := bstep (se 1 (by rfl) ⟨902525, by rfl⟩ : syracuseStep 1203367 = 1805051) B1805051
theorem B27794717 : Blo 1202418 27794717 := bstep (se 3 (by rfl) ⟨5211509, by rfl⟩ : syracuseStep 27794717 = 10423019) B10423019
theorem B1203503 : Blo 1202418 1203503 := bstep (se 1 (by rfl) ⟨902627, by rfl⟩ : syracuseStep 1203503 = 1805255) B1805255
theorem B1203743 : Blo 1202418 1203743 := bstep (se 1 (by rfl) ⟨902807, by rfl⟩ : syracuseStep 1203743 = 1805615) B1805615
theorem B1203815 : Blo 1202418 1203815 := bstep (se 1 (by rfl) ⟨902861, by rfl⟩ : syracuseStep 1203815 = 1805723) B1805723
theorem B1203867 : Blo 1202418 1203867 := bstep (se 1 (by rfl) ⟨902900, by rfl⟩ : syracuseStep 1203867 = 1805801) B1805801
theorem B1203903 : Blo 1202418 1203903 := bstep (se 1 (by rfl) ⟨902927, by rfl⟩ : syracuseStep 1203903 = 1805855) B1805855
theorem B1204059 : Blo 1202418 1204059 := bstep (se 1 (by rfl) ⟨903044, by rfl⟩ : syracuseStep 1204059 = 1806089) B1806089
theorem B1204095 : Blo 1202418 1204095 := bstep (se 1 (by rfl) ⟨903071, by rfl⟩ : syracuseStep 1204095 = 1806143) B1806143
theorem B3424319 : Blo 1202418 3424319 := bstep (se 1 (by rfl) ⟨2568239, by rfl⟩ : syracuseStep 3424319 = 5136479) B5136479
theorem B2285651 : Blo 1202418 2285651 := bstep (se 1 (by rfl) ⟨1714238, by rfl⟩ : syracuseStep 2285651 = 3428477) B3428477
theorem B1204383 : Blo 1202418 1204383 := bstep (se 1 (by rfl) ⟨903287, by rfl⟩ : syracuseStep 1204383 = 1806575) B1806575
theorem B7413983 : Blo 1202418 7413983 := bstep (se 1 (by rfl) ⟨5560487, by rfl⟩ : syracuseStep 7413983 = 11120975) B11120975
theorem B20562173 : Blo 1202418 20562173 := bstep (se 3 (by rfl) ⟨3855407, by rfl⟩ : syracuseStep 20562173 = 7710815) B7710815
theorem B9765623 : Blo 1202418 9765623 := bstep (se 1 (by rfl) ⟨7324217, by rfl⟩ : syracuseStep 9765623 = 14648435) B14648435
theorem B10429469 : Blo 1202418 10429469 := bstep (se 3 (by rfl) ⟨1955525, by rfl⟩ : syracuseStep 10429469 = 3911051) B3911051
theorem B1803647 : Blo 1202418 1803647 := bstep (se 1 (by rfl) ⟨1352735, by rfl⟩ : syracuseStep 1803647 = 2705471) B2705471
theorem B1803743 : Blo 1202418 1803743 := bstep (se 1 (by rfl) ⟨1352807, by rfl⟩ : syracuseStep 1803743 = 2705615) B2705615
theorem B6096383 : Blo 1202418 6096383 := bstep (se 1 (by rfl) ⟨4572287, by rfl⟩ : syracuseStep 6096383 = 9144575) B9144575
theorem B1804007 : Blo 1202418 1804007 := bstep (se 1 (by rfl) ⟨1353005, by rfl⟩ : syracuseStep 1804007 = 2706011) B2706011
theorem B18540407 : Blo 1202418 18540407 := bstep (se 1 (by rfl) ⟨13905305, by rfl⟩ : syracuseStep 18540407 = 27810611) B27810611
theorem B1804841 : Blo 1202418 1804841 := bstep (se 2 (by rfl) ⟨676815, by rfl⟩ : syracuseStep 1804841 = 1353631) B1353631
theorem B2706047 : Blo 1202418 2706047 := bstep (se 1 (by rfl) ⟨2029535, by rfl⟩ : syracuseStep 2706047 = 4059071) B4059071
theorem B2706623 : Blo 1202418 2706623 := bstep (se 1 (by rfl) ⟨2029967, by rfl⟩ : syracuseStep 2706623 = 4059935) B4059935
theorem B1805567 : Blo 1202418 1805567 := bstep (se 1 (by rfl) ⟨1354175, by rfl⟩ : syracuseStep 1805567 = 2708351) B2708351
theorem B8670635 : Blo 1202418 8670635 := bstep (se 1 (by rfl) ⟨6502976, by rfl⟩ : syracuseStep 8670635 = 13005953) B13005953
theorem B1805807 : Blo 1202418 1805807 := bstep (se 1 (by rfl) ⟨1354355, by rfl⟩ : syracuseStep 1805807 = 2708711) B2708711
theorem B3853871 : Blo 1202418 3853871 := bstep (se 1 (by rfl) ⟨2890403, by rfl⟩ : syracuseStep 3853871 = 5780807) B5780807
theorem B5787247 : Blo 1202418 5787247 := bstep (se 1 (by rfl) ⟨4340435, by rfl⟩ : syracuseStep 5787247 = 8680871) B8680871
theorem B98725553 : Blo 1202418 98725553 := bstep (se 2 (by rfl) ⟨37022082, by rfl⟩ : syracuseStep 98725553 = 74044165) B74044165
theorem B14659375 : Blo 1202418 14659375 := bstep (se 1 (by rfl) ⟨10994531, by rfl⟩ : syracuseStep 14659375 = 21989063) B21989063
theorem B1806191 : Blo 1202418 1806191 := bstep (se 1 (by rfl) ⟨1354643, by rfl⟩ : syracuseStep 1806191 = 2709287) B2709287
theorem B62533559 : Blo 1202418 62533559 := bstep (se 1 (by rfl) ⟨46900169, by rfl⟩ : syracuseStep 62533559 = 93800339) B93800339
theorem B15421427 : Blo 1202418 15421427 := bstep (se 1 (by rfl) ⟨11566070, by rfl⟩ : syracuseStep 15421427 = 23132141) B23132141
theorem B1372187 : Blo 1202418 1372187 := bstep (se 1 (by rfl) ⟨1029140, by rfl⟩ : syracuseStep 1372187 = 2058281) B2058281
theorem B2707487 : Blo 1202418 2707487 := bstep (se 1 (by rfl) ⟨2030615, by rfl⟩ : syracuseStep 2707487 = 4061231) B4061231
theorem B1806377 : Blo 1202418 1806377 := bstep (se 2 (by rfl) ⟨677391, by rfl⟩ : syracuseStep 1806377 = 1354783) B1354783
theorem B32944421 : Blo 1202418 32944421 := bstep (se 4 (by rfl) ⟨3088539, by rfl⟩ : syracuseStep 32944421 = 6177079) B6177079
theorem B4338143 : Blo 1202418 4338143 := bstep (se 1 (by rfl) ⟨3253607, by rfl⟩ : syracuseStep 4338143 = 6507215) B6507215
theorem B4633193 : Blo 1202418 4633193 := bstep (se 2 (by rfl) ⟨1737447, by rfl⟩ : syracuseStep 4633193 = 3474895) B3474895
theorem B10285703 : Blo 1202418 10285703 := bstep (se 1 (by rfl) ⟨7714277, by rfl⟩ : syracuseStep 10285703 = 15428555) B15428555
theorem B3658459 : Blo 1202418 3658459 := bstep (se 1 (by rfl) ⟨2743844, by rfl⟩ : syracuseStep 3658459 = 5487689) B5487689
theorem B34780009 : Blo 1202418 34780009 := bstep (se 2 (by rfl) ⟨13042503, by rfl⟩ : syracuseStep 34780009 = 26085007) B26085007
theorem B3044587 : Blo 1202418 3044587 := bstep (se 1 (by rfl) ⟨2283440, by rfl⟩ : syracuseStep 3044587 = 4566881) B4566881
theorem B3044729 : Blo 1202418 3044729 := bstep (se 2 (by rfl) ⟨1141773, by rfl⟩ : syracuseStep 3044729 = 2283547) B2283547
theorem B3217171 : Blo 1202418 3217171 := bstep (se 1 (by rfl) ⟨2412878, by rfl⟩ : syracuseStep 3217171 = 4825757) B4825757
theorem B10032977 : Blo 1202418 10032977 := bstep (se 2 (by rfl) ⟨3762366, by rfl⟩ : syracuseStep 10032977 = 7524733) B7524733
theorem B6092819 : Blo 1202418 6092819 := bstep (se 1 (by rfl) ⟨4569614, by rfl⟩ : syracuseStep 6092819 = 9139229) B9139229
theorem B2029927 : Blo 1202418 2029927 := bstep (se 1 (by rfl) ⟨1522445, by rfl⟩ : syracuseStep 2029927 = 3044891) B3044891
theorem B2029961 : Blo 1202418 2029961 := bstep (se 2 (by rfl) ⟨761235, by rfl⟩ : syracuseStep 2029961 = 1522471) B1522471
theorem B13892185 : Blo 1202418 13892185 := bstep (se 2 (by rfl) ⟨5209569, by rfl⟩ : syracuseStep 13892185 = 10419139) B10419139
theorem B7707433 : Blo 1202418 7707433 := bstep (se 2 (by rfl) ⟨2890287, by rfl⟩ : syracuseStep 7707433 = 5780575) B5780575
theorem B1203183 : Blo 1202418 1203183 := bstep (se 1 (by rfl) ⟨902387, by rfl⟩ : syracuseStep 1203183 = 1804775) B1804775
theorem B4062203 : Blo 1202418 4062203 := bstep (se 1 (by rfl) ⟨3046652, by rfl⟩ : syracuseStep 4062203 = 6093305) B6093305
theorem B1522795 : Blo 1202418 1522795 := bstep (se 1 (by rfl) ⟨1142096, by rfl⟩ : syracuseStep 1522795 = 2284193) B2284193
theorem B13901053 : Blo 1202418 13901053 := bstep (se 3 (by rfl) ⟨2606447, by rfl⟩ : syracuseStep 13901053 = 5212895) B5212895
theorem B18529811 : Blo 1202418 18529811 := bstep (se 1 (by rfl) ⟨13897358, by rfl⟩ : syracuseStep 18529811 = 27794717) B27794717
theorem B1204071 : Blo 1202418 1204071 := bstep (se 1 (by rfl) ⟨903053, by rfl⟩ : syracuseStep 1204071 = 1806107) B1806107
theorem B17342363 : Blo 1202418 17342363 := bstep (se 1 (by rfl) ⟨13006772, by rfl⟩ : syracuseStep 17342363 = 26013545) B26013545
theorem B1204251 : Blo 1202418 1204251 := bstep (se 1 (by rfl) ⟨903188, by rfl⟩ : syracuseStep 1204251 = 1806377) B1806377
theorem B1523767 : Blo 1202418 1523767 := bstep (se 1 (by rfl) ⟨1142825, by rfl⟩ : syracuseStep 1523767 = 2285651) B2285651
theorem B21962947 : Blo 1202418 21962947 := bstep (se 1 (by rfl) ⟨16472210, by rfl⟩ : syracuseStep 21962947 = 32944421) B32944421
theorem B2892095 : Blo 1202418 2892095 := bstep (se 1 (by rfl) ⟨2169071, by rfl⟩ : syracuseStep 2892095 = 4338143) B4338143
theorem B3088795 : Blo 1202418 3088795 := bstep (se 1 (by rfl) ⟨2316596, by rfl⟩ : syracuseStep 3088795 = 4633193) B4633193
theorem B6857135 : Blo 1202418 6857135 := bstep (se 1 (by rfl) ⟨5142851, by rfl⟩ : syracuseStep 6857135 = 10285703) B10285703
theorem B18522913 : Blo 1202418 18522913 := bstep (se 2 (by rfl) ⟨6946092, by rfl⟩ : syracuseStep 18522913 = 13892185) B13892185
theorem B4064255 : Blo 1202418 4064255 := bstep (se 1 (by rfl) ⟨3048191, by rfl⟩ : syracuseStep 4064255 = 6096383) B6096383
theorem B1353307 : Blo 1202418 1353307 := bstep (se 1 (by rfl) ⟨1014980, by rfl⟩ : syracuseStep 1353307 = 2029961) B2029961
theorem B1804031 : Blo 1202418 1804031 := bstep (se 1 (by rfl) ⟨1353023, by rfl⟩ : syracuseStep 1804031 = 2706047) B2706047
theorem B1804415 : Blo 1202418 1804415 := bstep (se 1 (by rfl) ⟨1353311, by rfl⟩ : syracuseStep 1804415 = 2706623) B2706623
theorem B65817035 : Blo 1202418 65817035 := bstep (se 1 (by rfl) ⟨49362776, by rfl⟩ : syracuseStep 65817035 = 98725553) B98725553
theorem B11561575 : Blo 1202418 11561575 := bstep (se 1 (by rfl) ⟨8671181, by rfl⟩ : syracuseStep 11561575 = 17342363) B17342363
theorem B1804991 : Blo 1202418 1804991 := bstep (se 1 (by rfl) ⟨1353743, by rfl⟩ : syracuseStep 1804991 = 2707487) B2707487
theorem B4942655 : Blo 1202418 4942655 := bstep (se 1 (by rfl) ⟨3706991, by rfl⟩ : syracuseStep 4942655 = 7413983) B7413983
theorem B13708115 : Blo 1202418 13708115 := bstep (se 1 (by rfl) ⟨10281086, by rfl⟩ : syracuseStep 13708115 = 20562173) B20562173
theorem B2706569 : Blo 1202418 2706569 := bstep (se 2 (by rfl) ⟨1014963, by rfl⟩ : syracuseStep 2706569 = 2029927) B2029927
theorem B4877945 : Blo 1202418 4877945 := bstep (se 2 (by rfl) ⟨1829229, by rfl⟩ : syracuseStep 4877945 = 3658459) B3658459
theorem B10276577 : Blo 1202418 10276577 := bstep (se 2 (by rfl) ⟨3853716, by rfl⟩ : syracuseStep 10276577 = 7707433) B7707433
theorem B6688651 : Blo 1202418 6688651 := bstep (se 1 (by rfl) ⟨5016488, by rfl⟩ : syracuseStep 6688651 = 10032977) B10032977
theorem B4059449 : Blo 1202418 4059449 := bstep (se 2 (by rfl) ⟨1522293, by rfl⟩ : syracuseStep 4059449 = 3044587) B3044587
theorem B18534737 : Blo 1202418 18534737 := bstep (se 2 (by rfl) ⟨6950526, by rfl⟩ : syracuseStep 18534737 = 13901053) B13901053
theorem B2708135 : Blo 1202418 2708135 := bstep (se 1 (by rfl) ⟨2031101, by rfl⟩ : syracuseStep 2708135 = 4062203) B4062203
theorem B5780423 : Blo 1202418 5780423 := bstep (se 1 (by rfl) ⟨4335317, by rfl⟩ : syracuseStep 5780423 = 8670635) B8670635
theorem B4289561 : Blo 1202418 4289561 := bstep (se 2 (by rfl) ⟨1608585, by rfl⟩ : syracuseStep 4289561 = 3217171) B3217171
theorem B2569247 : Blo 1202418 2569247 := bstep (se 1 (by rfl) ⟨1926935, by rfl⟩ : syracuseStep 2569247 = 3853871) B3853871
theorem B2282879 : Blo 1202418 2282879 := bstep (se 1 (by rfl) ⟨1712159, by rfl⟩ : syracuseStep 2282879 = 3424319) B3424319
theorem B3659165 : Blo 1202418 3659165 := bstep (se 3 (by rfl) ⟨686093, by rfl⟩ : syracuseStep 3659165 = 1372187) B1372187
theorem B6510415 : Blo 1202418 6510415 := bstep (se 1 (by rfl) ⟨4882811, by rfl⟩ : syracuseStep 6510415 = 9765623) B9765623
theorem B6952979 : Blo 1202418 6952979 := bstep (se 1 (by rfl) ⟨5214734, by rfl⟩ : syracuseStep 6952979 = 10429469) B10429469
theorem B2029819 : Blo 1202418 2029819 := bstep (se 1 (by rfl) ⟨1522364, by rfl⟩ : syracuseStep 2029819 = 3044729) B3044729
theorem B1202431 : Blo 1202418 1202431 := bstep (se 1 (by rfl) ⟨901823, by rfl⟩ : syracuseStep 1202431 = 1803647) B1803647
theorem B1202495 : Blo 1202418 1202495 := bstep (se 1 (by rfl) ⟨901871, by rfl⟩ : syracuseStep 1202495 = 1803743) B1803743
theorem B46373345 : Blo 1202418 46373345 := bstep (se 2 (by rfl) ⟨17390004, by rfl⟩ : syracuseStep 46373345 = 34780009) B34780009
theorem B1202671 : Blo 1202418 1202671 := bstep (se 1 (by rfl) ⟨902003, by rfl⟩ : syracuseStep 1202671 = 1804007) B1804007
theorem B12360271 : Blo 1202418 12360271 := bstep (se 1 (by rfl) ⟨9270203, by rfl⟩ : syracuseStep 12360271 = 18540407) B18540407
theorem B4061879 : Blo 1202418 4061879 := bstep (se 1 (by rfl) ⟨3046409, by rfl⟩ : syracuseStep 4061879 = 6092819) B6092819
theorem B2030393 : Blo 1202418 2030393 := bstep (se 2 (by rfl) ⟨761397, by rfl⟩ : syracuseStep 2030393 = 1522795) B1522795
theorem B1203227 : Blo 1202418 1203227 := bstep (se 1 (by rfl) ⟨902420, by rfl⟩ : syracuseStep 1203227 = 1804841) B1804841
theorem B7716329 : Blo 1202418 7716329 := bstep (se 2 (by rfl) ⟨2893623, by rfl⟩ : syracuseStep 7716329 = 5787247) B5787247
theorem B1203711 : Blo 1202418 1203711 := bstep (se 1 (by rfl) ⟨902783, by rfl⟩ : syracuseStep 1203711 = 1805567) B1805567
theorem B1203871 : Blo 1202418 1203871 := bstep (se 1 (by rfl) ⟨902903, by rfl⟩ : syracuseStep 1203871 = 1805807) B1805807
theorem B12353207 : Blo 1202418 12353207 := bstep (se 1 (by rfl) ⟨9264905, by rfl⟩ : syracuseStep 12353207 = 18529811) B18529811
theorem B19545833 : Blo 1202418 19545833 := bstep (se 2 (by rfl) ⟨7329687, by rfl⟩ : syracuseStep 19545833 = 14659375) B14659375
theorem B1204127 : Blo 1202418 1204127 := bstep (se 1 (by rfl) ⟨903095, by rfl⟩ : syracuseStep 1204127 = 1806191) B1806191
theorem B41689039 : Blo 1202418 41689039 := bstep (se 1 (by rfl) ⟨31266779, by rfl⟩ : syracuseStep 41689039 = 62533559) B62533559
theorem B10280951 : Blo 1202418 10280951 := bstep (se 1 (by rfl) ⟨7710713, by rfl⟩ : syracuseStep 10280951 = 15421427) B15421427
theorem B2031689 : Blo 1202418 2031689 := bstep (se 2 (by rfl) ⟨761883, by rfl⟩ : syracuseStep 2031689 = 1523767) B1523767
theorem B4571423 : Blo 1202418 4571423 := bstep (se 1 (by rfl) ⟨3428567, by rfl⟩ : syracuseStep 4571423 = 6857135) B6857135
theorem B2859707 : Blo 1202418 2859707 := bstep (se 1 (by rfl) ⟨2144780, by rfl⟩ : syracuseStep 2859707 = 4289561) B4289561
theorem B1712831 : Blo 1202418 1712831 := bstep (se 1 (by rfl) ⟨1284623, by rfl⟩ : syracuseStep 1712831 = 2569247) B2569247
theorem B43878023 : Blo 1202418 43878023 := bstep (se 1 (by rfl) ⟨32908517, by rfl⟩ : syracuseStep 43878023 = 65817035) B65817035
theorem B32941885 : Blo 1202418 32941885 := bstep (se 3 (by rfl) ⟨6176603, by rfl⟩ : syracuseStep 32941885 = 12353207) B12353207
theorem B1353595 : Blo 1202418 1353595 := bstep (se 1 (by rfl) ⟨1015196, by rfl⟩ : syracuseStep 1353595 = 2030393) B2030393
theorem B3295103 : Blo 1202418 3295103 := bstep (se 1 (by rfl) ⟨2471327, by rfl⟩ : syracuseStep 3295103 = 4942655) B4942655
theorem B1804379 : Blo 1202418 1804379 := bstep (se 1 (by rfl) ⟨1353284, by rfl⟩ : syracuseStep 1804379 = 2706569) B2706569
theorem B1804409 : Blo 1202418 1804409 := bstep (se 2 (by rfl) ⟨676653, by rfl⟩ : syracuseStep 1804409 = 1353307) B1353307
theorem B6851051 : Blo 1202418 6851051 := bstep (se 1 (by rfl) ⟨5138288, by rfl⟩ : syracuseStep 6851051 = 10276577) B10276577
theorem B55585385 : Blo 1202418 55585385 := bstep (se 2 (by rfl) ⟨20844519, by rfl⟩ : syracuseStep 55585385 = 41689039) B41689039
theorem B2706299 : Blo 1202418 2706299 := bstep (se 1 (by rfl) ⟨2029724, by rfl⟩ : syracuseStep 2706299 = 4059449) B4059449
theorem B1928063 : Blo 1202418 1928063 := bstep (se 1 (by rfl) ⟨1446047, by rfl⟩ : syracuseStep 1928063 = 2892095) B2892095
theorem B12356491 : Blo 1202418 12356491 := bstep (se 1 (by rfl) ⟨9267368, by rfl⟩ : syracuseStep 12356491 = 18534737) B18534737
theorem B2706425 : Blo 1202418 2706425 := bstep (se 2 (by rfl) ⟨1014909, by rfl⟩ : syracuseStep 2706425 = 2029819) B2029819
theorem B1805423 : Blo 1202418 1805423 := bstep (se 1 (by rfl) ⟨1354067, by rfl⟩ : syracuseStep 1805423 = 2708135) B2708135
theorem B3853615 : Blo 1202418 3853615 := bstep (se 1 (by rfl) ⟨2890211, by rfl⟩ : syracuseStep 3853615 = 5780423) B5780423
theorem B2707919 : Blo 1202418 2707919 := bstep (se 1 (by rfl) ⟨2030939, by rfl⟩ : syracuseStep 2707919 = 4061879) B4061879
theorem B9138743 : Blo 1202418 9138743 := bstep (se 1 (by rfl) ⟨6854057, by rfl⟩ : syracuseStep 9138743 = 13708115) B13708115
theorem B8680553 : Blo 1202418 8680553 := bstep (se 2 (by rfl) ⟨3255207, by rfl⟩ : syracuseStep 8680553 = 6510415) B6510415
theorem B13030555 : Blo 1202418 13030555 := bstep (se 1 (by rfl) ⟨9772916, by rfl⟩ : syracuseStep 13030555 = 19545833) B19545833
theorem B8918201 : Blo 1202418 8918201 := bstep (se 2 (by rfl) ⟨3344325, by rfl⟩ : syracuseStep 8918201 = 6688651) B6688651
theorem B6853967 : Blo 1202418 6853967 := bstep (se 1 (by rfl) ⟨5140475, by rfl⟩ : syracuseStep 6853967 = 10280951) B10280951
theorem B29283929 : Blo 1202418 29283929 := bstep (se 2 (by rfl) ⟨10981473, by rfl⟩ : syracuseStep 29283929 = 21962947) B21962947
theorem B4118393 : Blo 1202418 4118393 := bstep (se 2 (by rfl) ⟨1544397, by rfl⟩ : syracuseStep 4118393 = 3088795) B3088795
theorem B2709503 : Blo 1202418 2709503 := bstep (se 1 (by rfl) ⟨2032127, by rfl⟩ : syracuseStep 2709503 = 4064255) B4064255
theorem B16480361 : Blo 1202418 16480361 := bstep (se 2 (by rfl) ⟨6180135, by rfl⟩ : syracuseStep 16480361 = 12360271) B12360271
theorem B15415433 : Blo 1202418 15415433 := bstep (se 2 (by rfl) ⟨5780787, by rfl⟩ : syracuseStep 15415433 = 11561575) B11561575
theorem B1521919 : Blo 1202418 1521919 := bstep (se 1 (by rfl) ⟨1141439, by rfl⟩ : syracuseStep 1521919 = 2282879) B2282879
theorem B2439443 : Blo 1202418 2439443 := bstep (se 1 (by rfl) ⟨1829582, by rfl⟩ : syracuseStep 2439443 = 3659165) B3659165
theorem B24697217 : Blo 1202418 24697217 := bstep (se 2 (by rfl) ⟨9261456, by rfl⟩ : syracuseStep 24697217 = 18522913) B18522913
theorem B1202687 : Blo 1202418 1202687 := bstep (se 1 (by rfl) ⟨902015, by rfl⟩ : syracuseStep 1202687 = 1804031) B1804031
theorem B4635319 : Blo 1202418 4635319 := bstep (se 1 (by rfl) ⟨3476489, by rfl⟩ : syracuseStep 4635319 = 6952979) B6952979
theorem B1202943 : Blo 1202418 1202943 := bstep (se 1 (by rfl) ⟨902207, by rfl⟩ : syracuseStep 1202943 = 1804415) B1804415
theorem B30915563 : Blo 1202418 30915563 := bstep (se 1 (by rfl) ⟨23186672, by rfl⟩ : syracuseStep 30915563 = 46373345) B46373345
theorem B1203327 : Blo 1202418 1203327 := bstep (se 1 (by rfl) ⟨902495, by rfl⟩ : syracuseStep 1203327 = 1804991) B1804991
theorem B5144219 : Blo 1202418 5144219 := bstep (se 1 (by rfl) ⟨3858164, by rfl⟩ : syracuseStep 5144219 = 7716329) B7716329
theorem B3251963 : Blo 1202418 3251963 := bstep (se 1 (by rfl) ⟨2438972, by rfl⟩ : syracuseStep 3251963 = 4877945) B4877945
theorem B3047615 : Blo 1202418 3047615 := bstep (se 1 (by rfl) ⟨2285711, by rfl⟩ : syracuseStep 3047615 = 4571423) B4571423
theorem B6505181 : Blo 1202418 6505181 := bstep (se 3 (by rfl) ⟨1219721, by rfl⟩ : syracuseStep 6505181 = 2439443) B2439443
theorem B19522619 : Blo 1202418 19522619 := bstep (se 1 (by rfl) ⟨14641964, by rfl⟩ : syracuseStep 19522619 = 29283929) B29283929
theorem B16475321 : Blo 1202418 16475321 := bstep (se 2 (by rfl) ⟨6178245, by rfl⟩ : syracuseStep 16475321 = 12356491) B12356491
theorem B2745595 : Blo 1202418 2745595 := bstep (se 1 (by rfl) ⟨2059196, by rfl⟩ : syracuseStep 2745595 = 4118393) B4118393
theorem B5138153 : Blo 1202418 5138153 := bstep (se 2 (by rfl) ⟨1926807, by rfl⟩ : syracuseStep 5138153 = 3853615) B3853615
theorem B1804199 : Blo 1202418 1804199 := bstep (se 1 (by rfl) ⟨1353149, by rfl⟩ : syracuseStep 1804199 = 2706299) B2706299
theorem B1804283 : Blo 1202418 1804283 := bstep (se 1 (by rfl) ⟨1353212, by rfl⟩ : syracuseStep 1804283 = 2706425) B2706425
theorem B1804793 : Blo 1202418 1804793 := bstep (se 2 (by rfl) ⟨676797, by rfl⟩ : syracuseStep 1804793 = 1353595) B1353595
theorem B1354459 : Blo 1202418 1354459 := bstep (se 1 (by rfl) ⟨1015844, by rfl⟩ : syracuseStep 1354459 = 2031689) B2031689
theorem B1805279 : Blo 1202418 1805279 := bstep (se 1 (by rfl) ⟨1353959, by rfl⟩ : syracuseStep 1805279 = 2707919) B2707919
theorem B5787035 : Blo 1202418 5787035 := bstep (se 1 (by rfl) ⟨4340276, by rfl⟩ : syracuseStep 5787035 = 8680553) B8680553
theorem B6180425 : Blo 1202418 6180425 := bstep (se 2 (by rfl) ⟨2317659, by rfl⟩ : syracuseStep 6180425 = 4635319) B4635319
theorem B35147765 : Blo 1202418 35147765 := bstep (se 5 (by rfl) ⟨1647551, by rfl⟩ : syracuseStep 35147765 = 3295103) B3295103
theorem B1806335 : Blo 1202418 1806335 := bstep (se 1 (by rfl) ⟨1354751, by rfl⟩ : syracuseStep 1806335 = 2709503) B2709503
theorem B10276955 : Blo 1202418 10276955 := bstep (se 1 (by rfl) ⟨7707716, by rfl⟩ : syracuseStep 10276955 = 15415433) B15415433
theorem B4567367 : Blo 1202418 4567367 := bstep (se 1 (by rfl) ⟨3425525, by rfl⟩ : syracuseStep 4567367 = 6851051) B6851051
theorem B37056923 : Blo 1202418 37056923 := bstep (se 1 (by rfl) ⟨27792692, by rfl⟩ : syracuseStep 37056923 = 55585385) B55585385
theorem B4567549 : Blo 1202418 4567549 := bstep (se 3 (by rfl) ⟨856415, by rfl⟩ : syracuseStep 4567549 = 1712831) B1712831
theorem B5141501 : Blo 1202418 5141501 := bstep (se 3 (by rfl) ⟨964031, by rfl⟩ : syracuseStep 5141501 = 1928063) B1928063
theorem B43922513 : Blo 1202418 43922513 := bstep (se 2 (by rfl) ⟨16470942, by rfl⟩ : syracuseStep 43922513 = 32941885) B32941885
theorem B3429479 : Blo 1202418 3429479 := bstep (se 1 (by rfl) ⟨2572109, by rfl⟩ : syracuseStep 3429479 = 5144219) B5144219
theorem B329766005 : Blo 1202418 329766005 := bstep (se 5 (by rfl) ⟨15457781, by rfl⟩ : syracuseStep 329766005 = 30915563) B30915563
theorem B2167975 : Blo 1202418 2167975 := bstep (se 1 (by rfl) ⟨1625981, by rfl⟩ : syracuseStep 2167975 = 3251963) B3251963
theorem B43947629 : Blo 1202418 43947629 := bstep (se 3 (by rfl) ⟨8240180, by rfl⟩ : syracuseStep 43947629 = 16480361) B16480361
theorem B2029225 : Blo 1202418 2029225 := bstep (se 2 (by rfl) ⟨760959, by rfl⟩ : syracuseStep 2029225 = 1521919) B1521919
theorem B6092495 : Blo 1202418 6092495 := bstep (se 1 (by rfl) ⟨4569371, by rfl⟩ : syracuseStep 6092495 = 9138743) B9138743
theorem B1906471 : Blo 1202418 1906471 := bstep (se 1 (by rfl) ⟨1429853, by rfl⟩ : syracuseStep 1906471 = 2859707) B2859707
theorem B5945467 : Blo 1202418 5945467 := bstep (se 1 (by rfl) ⟨4459100, by rfl⟩ : syracuseStep 5945467 = 8918201) B8918201
theorem B4569311 : Blo 1202418 4569311 := bstep (se 1 (by rfl) ⟨3426983, by rfl⟩ : syracuseStep 4569311 = 6853967) B6853967
theorem B29252015 : Blo 1202418 29252015 := bstep (se 1 (by rfl) ⟨21939011, by rfl⟩ : syracuseStep 29252015 = 43878023) B43878023
theorem B1202919 : Blo 1202418 1202919 := bstep (se 1 (by rfl) ⟨902189, by rfl⟩ : syracuseStep 1202919 = 1804379) B1804379
theorem B1202939 : Blo 1202418 1202939 := bstep (se 1 (by rfl) ⟨902204, by rfl⟩ : syracuseStep 1202939 = 1804409) B1804409
theorem B17374073 : Blo 1202418 17374073 := bstep (se 2 (by rfl) ⟨6515277, by rfl⟩ : syracuseStep 17374073 = 13030555) B13030555
theorem B16464811 : Blo 1202418 16464811 := bstep (se 1 (by rfl) ⟨12348608, by rfl⟩ : syracuseStep 16464811 = 24697217) B24697217
theorem B1203615 : Blo 1202418 1203615 := bstep (se 1 (by rfl) ⟨902711, by rfl⟩ : syracuseStep 1203615 = 1805423) B1805423
theorem B2031743 : Blo 1202418 2031743 := bstep (se 1 (by rfl) ⟨1523807, by rfl⟩ : syracuseStep 2031743 = 3047615) B3047615
theorem B2286319 : Blo 1202418 2286319 := bstep (se 1 (by rfl) ⟨1714739, by rfl⟩ : syracuseStep 2286319 = 3429479) B3429479
theorem B3425435 : Blo 1202418 3425435 := bstep (se 1 (by rfl) ⟨2569076, by rfl⟩ : syracuseStep 3425435 = 5138153) B5138153
theorem B2705633 : Blo 1202418 2705633 := bstep (se 2 (by rfl) ⟨1014612, by rfl⟩ : syracuseStep 2705633 = 2029225) B2029225
theorem B2541961 : Blo 1202418 2541961 := bstep (se 2 (by rfl) ⟨953235, by rfl⟩ : syracuseStep 2541961 = 1906471) B1906471
theorem B23431843 : Blo 1202418 23431843 := bstep (se 1 (by rfl) ⟨17573882, by rfl⟩ : syracuseStep 23431843 = 35147765) B35147765
theorem B6851303 : Blo 1202418 6851303 := bstep (se 1 (by rfl) ⟨5138477, by rfl⟩ : syracuseStep 6851303 = 10276955) B10276955
theorem B4336787 : Blo 1202418 4336787 := bstep (se 1 (by rfl) ⟨3252590, by rfl⟩ : syracuseStep 4336787 = 6505181) B6505181
theorem B6090065 : Blo 1202418 6090065 := bstep (se 2 (by rfl) ⟨2283774, by rfl⟩ : syracuseStep 6090065 = 4567549) B4567549
theorem B3427667 : Blo 1202418 3427667 := bstep (se 1 (by rfl) ⟨2570750, by rfl⟩ : syracuseStep 3427667 = 5141501) B5141501
theorem B29281675 : Blo 1202418 29281675 := bstep (se 1 (by rfl) ⟨21961256, by rfl⟩ : syracuseStep 29281675 = 43922513) B43922513
theorem B219844003 : Blo 1202418 219844003 := bstep (se 1 (by rfl) ⟨164883002, by rfl⟩ : syracuseStep 219844003 = 329766005) B329766005
theorem B11562533 : Blo 1202418 11562533 := bstep (se 4 (by rfl) ⟨1083987, by rfl⟩ : syracuseStep 11562533 = 2167975) B2167975
theorem B1805945 : Blo 1202418 1805945 := bstep (se 2 (by rfl) ⟨677229, by rfl⟩ : syracuseStep 1805945 = 1354459) B1354459
theorem B29298419 : Blo 1202418 29298419 := bstep (se 1 (by rfl) ⟨21973814, by rfl⟩ : syracuseStep 29298419 = 43947629) B43947629
theorem B14643173 : Blo 1202418 14643173 := bstep (se 4 (by rfl) ⟨1372797, by rfl⟩ : syracuseStep 14643173 = 2745595) B2745595
theorem B19501343 : Blo 1202418 19501343 := bstep (se 1 (by rfl) ⟨14626007, by rfl⟩ : syracuseStep 19501343 = 29252015) B29252015
theorem B1204223 : Blo 1202418 1204223 := bstep (se 1 (by rfl) ⟨903167, by rfl⟩ : syracuseStep 1204223 = 1806335) B1806335
theorem B46330861 : Blo 1202418 46330861 := bstep (se 3 (by rfl) ⟨8687036, by rfl⟩ : syracuseStep 46330861 = 17374073) B17374073
theorem B7927289 : Blo 1202418 7927289 := bstep (se 2 (by rfl) ⟨2972733, by rfl⟩ : syracuseStep 7927289 = 5945467) B5945467
theorem B3044911 : Blo 1202418 3044911 := bstep (se 1 (by rfl) ⟨2283683, by rfl⟩ : syracuseStep 3044911 = 4567367) B4567367
theorem B24704615 : Blo 1202418 24704615 := bstep (se 1 (by rfl) ⟨18528461, by rfl⟩ : syracuseStep 24704615 = 37056923) B37056923
theorem B13015079 : Blo 1202418 13015079 := bstep (se 1 (by rfl) ⟨9761309, by rfl⟩ : syracuseStep 13015079 = 19522619) B19522619
theorem B10983547 : Blo 1202418 10983547 := bstep (se 1 (by rfl) ⟨8237660, by rfl⟩ : syracuseStep 10983547 = 16475321) B16475321
theorem B4061663 : Blo 1202418 4061663 := bstep (se 1 (by rfl) ⟨3046247, by rfl⟩ : syracuseStep 4061663 = 6092495) B6092495
theorem B21953081 : Blo 1202418 21953081 := bstep (se 2 (by rfl) ⟨8232405, by rfl⟩ : syracuseStep 21953081 = 16464811) B16464811
theorem B1202799 : Blo 1202418 1202799 := bstep (se 1 (by rfl) ⟨902099, by rfl⟩ : syracuseStep 1202799 = 1804199) B1804199
theorem B1202855 : Blo 1202418 1202855 := bstep (se 1 (by rfl) ⟨902141, by rfl⟩ : syracuseStep 1202855 = 1804283) B1804283
theorem B3046207 : Blo 1202418 3046207 := bstep (se 1 (by rfl) ⟨2284655, by rfl⟩ : syracuseStep 3046207 = 4569311) B4569311
theorem B1203195 : Blo 1202418 1203195 := bstep (se 1 (by rfl) ⟨902396, by rfl⟩ : syracuseStep 1203195 = 1804793) B1804793
theorem B1203519 : Blo 1202418 1203519 := bstep (se 1 (by rfl) ⟨902639, by rfl⟩ : syracuseStep 1203519 = 1805279) B1805279
theorem B3858023 : Blo 1202418 3858023 := bstep (se 1 (by rfl) ⟨2893517, by rfl⟩ : syracuseStep 3858023 = 5787035) B5787035
theorem B4120283 : Blo 1202418 4120283 := bstep (se 1 (by rfl) ⟨3090212, by rfl⟩ : syracuseStep 4120283 = 6180425) B6180425
theorem B13000895 : Blo 1202418 13000895 := bstep (se 1 (by rfl) ⟨9750671, by rfl⟩ : syracuseStep 13000895 = 19501343) B19501343
theorem B3048425 : Blo 1202418 3048425 := bstep (se 2 (by rfl) ⟨1143159, by rfl⟩ : syracuseStep 3048425 = 2286319) B2286319
theorem B8676719 : Blo 1202418 8676719 := bstep (se 1 (by rfl) ⟨6507539, by rfl⟩ : syracuseStep 8676719 = 13015079) B13015079
theorem B1803755 : Blo 1202418 1803755 := bstep (se 1 (by rfl) ⟨1352816, by rfl⟩ : syracuseStep 1803755 = 2705633) B2705633
theorem B2746855 : Blo 1202418 2746855 := bstep (se 1 (by rfl) ⟨2060141, by rfl⟩ : syracuseStep 2746855 = 4120283) B4120283
theorem B19532279 : Blo 1202418 19532279 := bstep (se 1 (by rfl) ⟨14649209, by rfl⟩ : syracuseStep 19532279 = 29298419) B29298419
theorem B1354495 : Blo 1202418 1354495 := bstep (se 1 (by rfl) ⟨1015871, by rfl⟩ : syracuseStep 1354495 = 2031743) B2031743
theorem B16469743 : Blo 1202418 16469743 := bstep (se 1 (by rfl) ⟨12352307, by rfl⟩ : syracuseStep 16469743 = 24704615) B24704615
theorem B2707775 : Blo 1202418 2707775 := bstep (se 1 (by rfl) ⟨2030831, by rfl⟩ : syracuseStep 2707775 = 4061663) B4061663
theorem B14635387 : Blo 1202418 14635387 := bstep (se 1 (by rfl) ⟨10976540, by rfl⟩ : syracuseStep 14635387 = 21953081) B21953081
theorem B4567535 : Blo 1202418 4567535 := bstep (se 1 (by rfl) ⟨3425651, by rfl⟩ : syracuseStep 4567535 = 6851303) B6851303
theorem B4059881 : Blo 1202418 4059881 := bstep (se 2 (by rfl) ⟨1522455, by rfl⟩ : syracuseStep 4059881 = 3044911) B3044911
theorem B4060043 : Blo 1202418 4060043 := bstep (se 1 (by rfl) ⟨3045032, by rfl⟩ : syracuseStep 4060043 = 6090065) B6090065
theorem B9762115 : Blo 1202418 9762115 := bstep (se 1 (by rfl) ⟨7321586, by rfl⟩ : syracuseStep 9762115 = 14643173) B14643173
theorem B14644729 : Blo 1202418 14644729 := bstep (se 2 (by rfl) ⟨5491773, by rfl⟩ : syracuseStep 14644729 = 10983547) B10983547
theorem B11564765 : Blo 1202418 11564765 := bstep (se 3 (by rfl) ⟨2168393, by rfl⟩ : syracuseStep 11564765 = 4336787) B4336787
theorem B2283623 : Blo 1202418 2283623 := bstep (se 1 (by rfl) ⟨1712717, by rfl⟩ : syracuseStep 2283623 = 3425435) B3425435
theorem B31242457 : Blo 1202418 31242457 := bstep (se 2 (by rfl) ⟨11715921, by rfl⟩ : syracuseStep 31242457 = 23431843) B23431843
theorem B4061609 : Blo 1202418 4061609 := bstep (se 2 (by rfl) ⟨1523103, by rfl⟩ : syracuseStep 4061609 = 3046207) B3046207
theorem B61774481 : Blo 1202418 61774481 := bstep (se 2 (by rfl) ⟨23165430, by rfl⟩ : syracuseStep 61774481 = 46330861) B46330861
theorem B39042233 : Blo 1202418 39042233 := bstep (se 2 (by rfl) ⟨14640837, by rfl⟩ : syracuseStep 39042233 = 29281675) B29281675
theorem B293125337 : Blo 1202418 293125337 := bstep (se 2 (by rfl) ⟨109922001, by rfl⟩ : syracuseStep 293125337 = 219844003) B219844003
theorem B13557125 : Blo 1202418 13557125 := bstep (se 4 (by rfl) ⟨1270980, by rfl⟩ : syracuseStep 13557125 = 2541961) B2541961
theorem B2285111 : Blo 1202418 2285111 := bstep (se 1 (by rfl) ⟨1713833, by rfl⟩ : syracuseStep 2285111 = 3427667) B3427667
theorem B7708355 : Blo 1202418 7708355 := bstep (se 1 (by rfl) ⟨5781266, by rfl⟩ : syracuseStep 7708355 = 11562533) B11562533
theorem B2572015 : Blo 1202418 2572015 := bstep (se 1 (by rfl) ⟨1929011, by rfl⟩ : syracuseStep 2572015 = 3858023) B3858023
theorem B1203963 : Blo 1202418 1203963 := bstep (se 1 (by rfl) ⟨902972, by rfl⟩ : syracuseStep 1203963 = 1805945) B1805945
theorem B84557749 : Blo 1202418 84557749 := bstep (se 5 (by rfl) ⟨3963644, by rfl⟩ : syracuseStep 84557749 = 7927289) B7927289
theorem B8667263 : Blo 1202418 8667263 := bstep (se 1 (by rfl) ⟨6500447, by rfl⟩ : syracuseStep 8667263 = 13000895) B13000895
theorem B41656609 : Blo 1202418 41656609 := bstep (se 2 (by rfl) ⟨15621228, by rfl⟩ : syracuseStep 41656609 = 31242457) B31242457
theorem B2032283 : Blo 1202418 2032283 := bstep (se 1 (by rfl) ⟨1524212, by rfl⟩ : syracuseStep 2032283 = 3048425) B3048425
theorem B5784479 : Blo 1202418 5784479 := bstep (se 1 (by rfl) ⟨4338359, by rfl⟩ : syracuseStep 5784479 = 8676719) B8676719
theorem B7709843 : Blo 1202418 7709843 := bstep (se 1 (by rfl) ⟨5782382, by rfl⟩ : syracuseStep 7709843 = 11564765) B11564765
theorem B41182987 : Blo 1202418 41182987 := bstep (se 1 (by rfl) ⟨30887240, by rfl⟩ : syracuseStep 41182987 = 61774481) B61774481
theorem B78055397 : Blo 1202418 78055397 := bstep (se 4 (by rfl) ⟨7317693, by rfl⟩ : syracuseStep 78055397 = 14635387) B14635387
theorem B26028155 : Blo 1202418 26028155 := bstep (se 1 (by rfl) ⟨19521116, by rfl⟩ : syracuseStep 26028155 = 39042233) B39042233
theorem B9038083 : Blo 1202418 9038083 := bstep (se 1 (by rfl) ⟨6778562, by rfl⟩ : syracuseStep 9038083 = 13557125) B13557125
theorem B5138903 : Blo 1202418 5138903 := bstep (se 1 (by rfl) ⟨3854177, by rfl⟩ : syracuseStep 5138903 = 7708355) B7708355
theorem B14649893 : Blo 1202418 14649893 := bstep (se 4 (by rfl) ⟨1373427, by rfl⟩ : syracuseStep 14649893 = 2746855) B2746855
theorem B78105221 : Blo 1202418 78105221 := bstep (se 4 (by rfl) ⟨7322364, by rfl⟩ : syracuseStep 78105221 = 14644729) B14644729
theorem B1805183 : Blo 1202418 1805183 := bstep (se 1 (by rfl) ⟨1353887, by rfl⟩ : syracuseStep 1805183 = 2707775) B2707775
theorem B2706587 : Blo 1202418 2706587 := bstep (se 1 (by rfl) ⟨2029940, by rfl⟩ : syracuseStep 2706587 = 4059881) B4059881
theorem B2706695 : Blo 1202418 2706695 := bstep (se 1 (by rfl) ⟨2030021, by rfl⟩ : syracuseStep 2706695 = 4060043) B4060043
theorem B1805993 : Blo 1202418 1805993 := bstep (se 2 (by rfl) ⟨677247, by rfl⟩ : syracuseStep 1805993 = 1354495) B1354495
theorem B2707739 : Blo 1202418 2707739 := bstep (se 1 (by rfl) ⟨2030804, by rfl⟩ : syracuseStep 2707739 = 4061609) B4061609
theorem B13021519 : Blo 1202418 13021519 := bstep (se 1 (by rfl) ⟨9766139, by rfl⟩ : syracuseStep 13021519 = 19532279) B19532279
theorem B195416891 : Blo 1202418 195416891 := bstep (se 1 (by rfl) ⟨146562668, by rfl⟩ : syracuseStep 195416891 = 293125337) B293125337
theorem B21959657 : Blo 1202418 21959657 := bstep (se 2 (by rfl) ⟨8234871, by rfl⟩ : syracuseStep 21959657 = 16469743) B16469743
theorem B3429353 : Blo 1202418 3429353 := bstep (se 2 (by rfl) ⟨1286007, by rfl⟩ : syracuseStep 3429353 = 2572015) B2572015
theorem B112743665 : Blo 1202418 112743665 := bstep (se 2 (by rfl) ⟨42278874, by rfl⟩ : syracuseStep 112743665 = 84557749) B84557749
theorem B3045023 : Blo 1202418 3045023 := bstep (se 1 (by rfl) ⟨2283767, by rfl⟩ : syracuseStep 3045023 = 4567535) B4567535
theorem B1202503 : Blo 1202418 1202503 := bstep (se 1 (by rfl) ⟨901877, by rfl⟩ : syracuseStep 1202503 = 1803755) B1803755
theorem B1522415 : Blo 1202418 1522415 := bstep (se 1 (by rfl) ⟨1141811, by rfl⟩ : syracuseStep 1522415 = 2283623) B2283623
theorem B6093629 : Blo 1202418 6093629 := bstep (se 3 (by rfl) ⟨1142555, by rfl⟩ : syracuseStep 6093629 = 2285111) B2285111
theorem B13016153 : Blo 1202418 13016153 := bstep (se 2 (by rfl) ⟨4881057, by rfl⟩ : syracuseStep 13016153 = 9762115) B9762115
theorem B34709741 : Blo 1202418 34709741 := bstep (se 3 (by rfl) ⟨6508076, by rfl⟩ : syracuseStep 34709741 = 13016153) B13016153
theorem B12050777 : Blo 1202418 12050777 := bstep (se 2 (by rfl) ⟨4519041, by rfl⟩ : syracuseStep 12050777 = 9038083) B9038083
theorem B55542145 : Blo 1202418 55542145 := bstep (se 2 (by rfl) ⟨20828304, by rfl⟩ : syracuseStep 55542145 = 41656609) B41656609
theorem B130277927 : Blo 1202418 130277927 := bstep (se 1 (by rfl) ⟨97708445, by rfl⟩ : syracuseStep 130277927 = 195416891) B195416891
theorem B14639771 : Blo 1202418 14639771 := bstep (se 1 (by rfl) ⟨10979828, by rfl⟩ : syracuseStep 14639771 = 21959657) B21959657
theorem B2286235 : Blo 1202418 2286235 := bstep (se 1 (by rfl) ⟨1714676, by rfl⟩ : syracuseStep 2286235 = 3429353) B3429353
theorem B75162443 : Blo 1202418 75162443 := bstep (se 1 (by rfl) ⟨56371832, by rfl⟩ : syracuseStep 75162443 = 112743665) B112743665
theorem B52036931 : Blo 1202418 52036931 := bstep (se 1 (by rfl) ⟨39027698, by rfl⟩ : syracuseStep 52036931 = 78055397) B78055397
theorem B17352103 : Blo 1202418 17352103 := bstep (se 1 (by rfl) ⟨13014077, by rfl⟩ : syracuseStep 17352103 = 26028155) B26028155
theorem B9766595 : Blo 1202418 9766595 := bstep (se 1 (by rfl) ⟨7324946, by rfl⟩ : syracuseStep 9766595 = 14649893) B14649893
theorem B52070147 : Blo 1202418 52070147 := bstep (se 1 (by rfl) ⟨39052610, by rfl⟩ : syracuseStep 52070147 = 78105221) B78105221
theorem B1804391 : Blo 1202418 1804391 := bstep (se 1 (by rfl) ⟨1353293, by rfl⟩ : syracuseStep 1804391 = 2706587) B2706587
theorem B1804463 : Blo 1202418 1804463 := bstep (se 1 (by rfl) ⟨1353347, by rfl⟩ : syracuseStep 1804463 = 2706695) B2706695
theorem B5778175 : Blo 1202418 5778175 := bstep (se 1 (by rfl) ⟨4333631, by rfl⟩ : syracuseStep 5778175 = 8667263) B8667263
theorem B1805159 : Blo 1202418 1805159 := bstep (se 1 (by rfl) ⟨1353869, by rfl⟩ : syracuseStep 1805159 = 2707739) B2707739
theorem B1354855 : Blo 1202418 1354855 := bstep (se 1 (by rfl) ⟨1016141, by rfl⟩ : syracuseStep 1354855 = 2032283) B2032283
theorem B17362025 : Blo 1202418 17362025 := bstep (se 2 (by rfl) ⟨6510759, by rfl⟩ : syracuseStep 17362025 = 13021519) B13021519
theorem B5139895 : Blo 1202418 5139895 := bstep (se 1 (by rfl) ⟨3854921, by rfl⟩ : syracuseStep 5139895 = 7709843) B7709843
theorem B4059773 : Blo 1202418 4059773 := bstep (se 3 (by rfl) ⟨761207, by rfl⟩ : syracuseStep 4059773 = 1522415) B1522415
theorem B3856319 : Blo 1202418 3856319 := bstep (se 1 (by rfl) ⟨2892239, by rfl⟩ : syracuseStep 3856319 = 5784479) B5784479
theorem B2030015 : Blo 1202418 2030015 := bstep (se 1 (by rfl) ⟨1522511, by rfl⟩ : syracuseStep 2030015 = 3045023) B3045023
theorem B13703741 : Blo 1202418 13703741 := bstep (se 3 (by rfl) ⟨2569451, by rfl⟩ : syracuseStep 13703741 = 5138903) B5138903
theorem B4062419 : Blo 1202418 4062419 := bstep (se 1 (by rfl) ⟨3046814, by rfl⟩ : syracuseStep 4062419 = 6093629) B6093629
theorem B1203455 : Blo 1202418 1203455 := bstep (se 1 (by rfl) ⟨902591, by rfl⟩ : syracuseStep 1203455 = 1805183) B1805183
theorem B54910649 : Blo 1202418 54910649 := bstep (se 2 (by rfl) ⟨20591493, by rfl⟩ : syracuseStep 54910649 = 41182987) B41182987
theorem B1203995 : Blo 1202418 1203995 := bstep (se 1 (by rfl) ⟨902996, by rfl⟩ : syracuseStep 1203995 = 1805993) B1805993
theorem B74056193 : Blo 1202418 74056193 := bstep (se 2 (by rfl) ⟨27771072, by rfl⟩ : syracuseStep 74056193 = 55542145) B55542145
theorem B3048313 : Blo 1202418 3048313 := bstep (se 2 (by rfl) ⟨1143117, by rfl⟩ : syracuseStep 3048313 = 2286235) B2286235
theorem B347407805 : Blo 1202418 347407805 := bstep (se 3 (by rfl) ⟨65138963, by rfl⟩ : syracuseStep 347407805 = 130277927) B130277927
theorem B1353343 : Blo 1202418 1353343 := bstep (se 1 (by rfl) ⟨1015007, by rfl⟩ : syracuseStep 1353343 = 2030015) B2030015
theorem B9135827 : Blo 1202418 9135827 := bstep (se 1 (by rfl) ⟨6851870, by rfl⟩ : syracuseStep 9135827 = 13703741) B13703741
theorem B26044253 : Blo 1202418 26044253 := bstep (se 3 (by rfl) ⟨4883297, by rfl⟩ : syracuseStep 26044253 = 9766595) B9766595
theorem B23136137 : Blo 1202418 23136137 := bstep (se 2 (by rfl) ⟨8676051, by rfl⟩ : syracuseStep 23136137 = 17352103) B17352103
theorem B2706515 : Blo 1202418 2706515 := bstep (se 1 (by rfl) ⟨2029886, by rfl⟩ : syracuseStep 2706515 = 4059773) B4059773
theorem B9759847 : Blo 1202418 9759847 := bstep (se 1 (by rfl) ⟨7319885, by rfl⟩ : syracuseStep 9759847 = 14639771) B14639771
theorem B7704233 : Blo 1202418 7704233 := bstep (se 2 (by rfl) ⟨2889087, by rfl⟩ : syracuseStep 7704233 = 5778175) B5778175
theorem B34713431 : Blo 1202418 34713431 := bstep (se 1 (by rfl) ⟨26035073, by rfl⟩ : syracuseStep 34713431 = 52070147) B52070147
theorem B1806473 : Blo 1202418 1806473 := bstep (se 2 (by rfl) ⟨677427, by rfl⟩ : syracuseStep 1806473 = 1354855) B1354855
theorem B6853193 : Blo 1202418 6853193 := bstep (se 2 (by rfl) ⟨2569947, by rfl⟩ : syracuseStep 6853193 = 5139895) B5139895
theorem B2708279 : Blo 1202418 2708279 := bstep (se 1 (by rfl) ⟨2031209, by rfl⟩ : syracuseStep 2708279 = 4062419) B4062419
theorem B36607099 : Blo 1202418 36607099 := bstep (se 1 (by rfl) ⟨27455324, by rfl⟩ : syracuseStep 36607099 = 54910649) B54910649
theorem B23139827 : Blo 1202418 23139827 := bstep (se 1 (by rfl) ⟨17354870, by rfl⟩ : syracuseStep 23139827 = 34709741) B34709741
theorem B8033851 : Blo 1202418 8033851 := bstep (se 1 (by rfl) ⟨6025388, by rfl⟩ : syracuseStep 8033851 = 12050777) B12050777
theorem B801732725 : Blo 1202418 801732725 := bstep (se 5 (by rfl) ⟨37581221, by rfl⟩ : syracuseStep 801732725 = 75162443) B75162443
theorem B34691287 : Blo 1202418 34691287 := bstep (se 1 (by rfl) ⟨26018465, by rfl⟩ : syracuseStep 34691287 = 52036931) B52036931
theorem B2570879 : Blo 1202418 2570879 := bstep (se 1 (by rfl) ⟨1928159, by rfl⟩ : syracuseStep 2570879 = 3856319) B3856319
theorem B1202927 : Blo 1202418 1202927 := bstep (se 1 (by rfl) ⟨902195, by rfl⟩ : syracuseStep 1202927 = 1804391) B1804391
theorem B1202975 : Blo 1202418 1202975 := bstep (se 1 (by rfl) ⟨902231, by rfl⟩ : syracuseStep 1202975 = 1804463) B1804463
theorem B1203439 : Blo 1202418 1203439 := bstep (se 1 (by rfl) ⟨902579, by rfl⟩ : syracuseStep 1203439 = 1805159) B1805159
theorem B11574683 : Blo 1202418 11574683 := bstep (se 1 (by rfl) ⟨8681012, by rfl⟩ : syracuseStep 11574683 = 17362025) B17362025
theorem B1204315 : Blo 1202418 1204315 := bstep (se 1 (by rfl) ⟨903236, by rfl⟩ : syracuseStep 1204315 = 1806473) B1806473
theorem B231605203 : Blo 1202418 231605203 := bstep (se 1 (by rfl) ⟨173703902, by rfl⟩ : syracuseStep 231605203 = 347407805) B347407805
theorem B15426551 : Blo 1202418 15426551 := bstep (se 1 (by rfl) ⟨11569913, by rfl⟩ : syracuseStep 15426551 = 23139827) B23139827
theorem B4064417 : Blo 1202418 4064417 := bstep (se 2 (by rfl) ⟨1524156, by rfl⟩ : syracuseStep 4064417 = 3048313) B3048313
theorem B534488483 : Blo 1202418 534488483 := bstep (se 1 (by rfl) ⟨400866362, by rfl⟩ : syracuseStep 534488483 = 801732725) B801732725
theorem B48809465 : Blo 1202418 48809465 := bstep (se 2 (by rfl) ⟨18303549, by rfl⟩ : syracuseStep 48809465 = 36607099) B36607099
theorem B1804343 : Blo 1202418 1804343 := bstep (se 1 (by rfl) ⟨1353257, by rfl⟩ : syracuseStep 1804343 = 2706515) B2706515
theorem B1804457 : Blo 1202418 1804457 := bstep (se 2 (by rfl) ⟨676671, by rfl⟩ : syracuseStep 1804457 = 1353343) B1353343
theorem B46255049 : Blo 1202418 46255049 := bstep (se 2 (by rfl) ⟨17345643, by rfl⟩ : syracuseStep 46255049 = 34691287) B34691287
theorem B1805519 : Blo 1202418 1805519 := bstep (se 1 (by rfl) ⟨1354139, by rfl⟩ : syracuseStep 1805519 = 2708279) B2708279
theorem B6090551 : Blo 1202418 6090551 := bstep (se 1 (by rfl) ⟨4567913, by rfl⟩ : syracuseStep 6090551 = 9135827) B9135827
theorem B17362835 : Blo 1202418 17362835 := bstep (se 1 (by rfl) ⟨13022126, by rfl⟩ : syracuseStep 17362835 = 26044253) B26044253
theorem B13013129 : Blo 1202418 13013129 := bstep (se 2 (by rfl) ⟨4879923, by rfl⟩ : syracuseStep 13013129 = 9759847) B9759847
theorem B10711801 : Blo 1202418 10711801 := bstep (se 2 (by rfl) ⟨4016925, by rfl⟩ : syracuseStep 10711801 = 8033851) B8033851
theorem B49370795 : Blo 1202418 49370795 := bstep (se 1 (by rfl) ⟨37028096, by rfl⟩ : syracuseStep 49370795 = 74056193) B74056193
theorem B4568795 : Blo 1202418 4568795 := bstep (se 1 (by rfl) ⟨3426596, by rfl⟩ : syracuseStep 4568795 = 6853193) B6853193
theorem B15424091 : Blo 1202418 15424091 := bstep (se 1 (by rfl) ⟨11568068, by rfl⟩ : syracuseStep 15424091 = 23136137) B23136137
theorem B6855677 : Blo 1202418 6855677 := bstep (se 3 (by rfl) ⟨1285439, by rfl⟩ : syracuseStep 6855677 = 2570879) B2570879
theorem B7716455 : Blo 1202418 7716455 := bstep (se 1 (by rfl) ⟨5787341, by rfl⟩ : syracuseStep 7716455 = 11574683) B11574683
theorem B5136155 : Blo 1202418 5136155 := bstep (se 1 (by rfl) ⟨3852116, by rfl⟩ : syracuseStep 5136155 = 7704233) B7704233
theorem B23142287 : Blo 1202418 23142287 := bstep (se 1 (by rfl) ⟨17356715, by rfl⟩ : syracuseStep 23142287 = 34713431) B34713431
theorem B8675419 : Blo 1202418 8675419 := bstep (se 1 (by rfl) ⟨6506564, by rfl⟩ : syracuseStep 8675419 = 13013129) B13013129
theorem B32539643 : Blo 1202418 32539643 := bstep (se 1 (by rfl) ⟨24404732, by rfl⟩ : syracuseStep 32539643 = 48809465) B48809465
theorem B308806937 : Blo 1202418 308806937 := bstep (se 2 (by rfl) ⟨115802601, by rfl⟩ : syracuseStep 308806937 = 231605203) B231605203
theorem B10282727 : Blo 1202418 10282727 := bstep (se 1 (by rfl) ⟨7712045, by rfl⟩ : syracuseStep 10282727 = 15424091) B15424091
theorem B30836699 : Blo 1202418 30836699 := bstep (se 1 (by rfl) ⟨23127524, by rfl⟩ : syracuseStep 30836699 = 46255049) B46255049
theorem B15428191 : Blo 1202418 15428191 := bstep (se 1 (by rfl) ⟨11571143, by rfl⟩ : syracuseStep 15428191 = 23142287) B23142287
theorem B10284367 : Blo 1202418 10284367 := bstep (se 1 (by rfl) ⟨7713275, by rfl⟩ : syracuseStep 10284367 = 15426551) B15426551
theorem B14282401 : Blo 1202418 14282401 := bstep (se 2 (by rfl) ⟨5355900, by rfl⟩ : syracuseStep 14282401 = 10711801) B10711801
theorem B4060367 : Blo 1202418 4060367 := bstep (se 1 (by rfl) ⟨3045275, by rfl⟩ : syracuseStep 4060367 = 6090551) B6090551
theorem B2709611 : Blo 1202418 2709611 := bstep (se 1 (by rfl) ⟨2032208, by rfl⟩ : syracuseStep 2709611 = 4064417) B4064417
theorem B356325655 : Blo 1202418 356325655 := bstep (se 1 (by rfl) ⟨267244241, by rfl⟩ : syracuseStep 356325655 = 534488483) B534488483
theorem B32913863 : Blo 1202418 32913863 := bstep (se 1 (by rfl) ⟨24685397, by rfl⟩ : syracuseStep 32913863 = 49370795) B49370795
theorem B3045863 : Blo 1202418 3045863 := bstep (se 1 (by rfl) ⟨2284397, by rfl⟩ : syracuseStep 3045863 = 4568795) B4568795
theorem B1202895 : Blo 1202418 1202895 := bstep (se 1 (by rfl) ⟨902171, by rfl⟩ : syracuseStep 1202895 = 1804343) B1804343
theorem B1202971 : Blo 1202418 1202971 := bstep (se 1 (by rfl) ⟨902228, by rfl⟩ : syracuseStep 1202971 = 1804457) B1804457
theorem B4570451 : Blo 1202418 4570451 := bstep (se 1 (by rfl) ⟨3427838, by rfl⟩ : syracuseStep 4570451 = 6855677) B6855677
theorem B1203679 : Blo 1202418 1203679 := bstep (se 1 (by rfl) ⟨902759, by rfl⟩ : syracuseStep 1203679 = 1805519) B1805519
theorem B5144303 : Blo 1202418 5144303 := bstep (se 1 (by rfl) ⟨3858227, by rfl⟩ : syracuseStep 5144303 = 7716455) B7716455
theorem B3424103 : Blo 1202418 3424103 := bstep (se 1 (by rfl) ⟨2568077, by rfl⟩ : syracuseStep 3424103 = 5136155) B5136155
theorem B11575223 : Blo 1202418 11575223 := bstep (se 1 (by rfl) ⟨8681417, by rfl⟩ : syracuseStep 11575223 = 17362835) B17362835
theorem B11567225 : Blo 1202418 11567225 := bstep (se 2 (by rfl) ⟨4337709, by rfl⟩ : syracuseStep 11567225 = 8675419) B8675419
theorem B21693095 : Blo 1202418 21693095 := bstep (se 1 (by rfl) ⟨16269821, by rfl⟩ : syracuseStep 21693095 = 32539643) B32539643
theorem B20570921 : Blo 1202418 20570921 := bstep (se 2 (by rfl) ⟨7714095, by rfl⟩ : syracuseStep 20570921 = 15428191) B15428191
theorem B2706911 : Blo 1202418 2706911 := bstep (se 1 (by rfl) ⟨2030183, by rfl⟩ : syracuseStep 2706911 = 4060367) B4060367
theorem B20557799 : Blo 1202418 20557799 := bstep (se 1 (by rfl) ⟨15418349, by rfl⟩ : syracuseStep 20557799 = 30836699) B30836699
theorem B1806407 : Blo 1202418 1806407 := bstep (se 1 (by rfl) ⟨1354805, by rfl⟩ : syracuseStep 1806407 = 2709611) B2709611
theorem B21942575 : Blo 1202418 21942575 := bstep (se 1 (by rfl) ⟨16456931, by rfl⟩ : syracuseStep 21942575 = 32913863) B32913863
theorem B19043201 : Blo 1202418 19043201 := bstep (se 2 (by rfl) ⟨7141200, by rfl⟩ : syracuseStep 19043201 = 14282401) B14282401
theorem B3429535 : Blo 1202418 3429535 := bstep (se 1 (by rfl) ⟨2572151, by rfl⟩ : syracuseStep 3429535 = 5144303) B5144303
theorem B2282735 : Blo 1202418 2282735 := bstep (se 1 (by rfl) ⟨1712051, by rfl⟩ : syracuseStep 2282735 = 3424103) B3424103
theorem B475100873 : Blo 1202418 475100873 := bstep (se 2 (by rfl) ⟨178162827, by rfl⟩ : syracuseStep 475100873 = 356325655) B356325655
theorem B205871291 : Blo 1202418 205871291 := bstep (se 1 (by rfl) ⟨154403468, by rfl⟩ : syracuseStep 205871291 = 308806937) B308806937
theorem B6855151 : Blo 1202418 6855151 := bstep (se 1 (by rfl) ⟨5141363, by rfl⟩ : syracuseStep 6855151 = 10282727) B10282727
theorem B2030575 : Blo 1202418 2030575 := bstep (se 1 (by rfl) ⟨1522931, by rfl⟩ : syracuseStep 2030575 = 3045863) B3045863
theorem B13712489 : Blo 1202418 13712489 := bstep (se 2 (by rfl) ⟨5142183, by rfl⟩ : syracuseStep 13712489 = 10284367) B10284367
theorem B3046967 : Blo 1202418 3046967 := bstep (se 1 (by rfl) ⟨2285225, by rfl⟩ : syracuseStep 3046967 = 4570451) B4570451
theorem B7716815 : Blo 1202418 7716815 := bstep (se 1 (by rfl) ⟨5787611, by rfl⟩ : syracuseStep 7716815 = 11575223) B11575223
theorem B1204271 : Blo 1202418 1204271 := bstep (se 1 (by rfl) ⟨903203, by rfl⟩ : syracuseStep 1204271 = 1806407) B1806407
theorem B13713947 : Blo 1202418 13713947 := bstep (se 1 (by rfl) ⟨10285460, by rfl⟩ : syracuseStep 13713947 = 20570921) B20570921
theorem B4572713 : Blo 1202418 4572713 := bstep (se 2 (by rfl) ⟨1714767, by rfl⟩ : syracuseStep 4572713 = 3429535) B3429535
theorem B1804607 : Blo 1202418 1804607 := bstep (se 1 (by rfl) ⟨1353455, by rfl⟩ : syracuseStep 1804607 = 2706911) B2706911
theorem B7711483 : Blo 1202418 7711483 := bstep (se 1 (by rfl) ⟨5783612, by rfl⟩ : syracuseStep 7711483 = 11567225) B11567225
theorem B14462063 : Blo 1202418 14462063 := bstep (se 1 (by rfl) ⟨10846547, by rfl⟩ : syracuseStep 14462063 = 21693095) B21693095
theorem B2707433 : Blo 1202418 2707433 := bstep (se 2 (by rfl) ⟨1015287, by rfl⟩ : syracuseStep 2707433 = 2030575) B2030575
theorem B14628383 : Blo 1202418 14628383 := bstep (se 1 (by rfl) ⟨10971287, by rfl⟩ : syracuseStep 14628383 = 21942575) B21942575
theorem B12695467 : Blo 1202418 12695467 := bstep (se 1 (by rfl) ⟨9521600, by rfl⟩ : syracuseStep 12695467 = 19043201) B19043201
theorem B9140201 : Blo 1202418 9140201 := bstep (se 2 (by rfl) ⟨3427575, by rfl⟩ : syracuseStep 9140201 = 6855151) B6855151
theorem B1521823 : Blo 1202418 1521823 := bstep (se 1 (by rfl) ⟨1141367, by rfl⟩ : syracuseStep 1521823 = 2282735) B2282735
theorem B316733915 : Blo 1202418 316733915 := bstep (se 1 (by rfl) ⟨237550436, by rfl⟩ : syracuseStep 316733915 = 475100873) B475100873
theorem B137247527 : Blo 1202418 137247527 := bstep (se 1 (by rfl) ⟨102935645, by rfl⟩ : syracuseStep 137247527 = 205871291) B205871291
theorem B9141659 : Blo 1202418 9141659 := bstep (se 1 (by rfl) ⟨6856244, by rfl⟩ : syracuseStep 9141659 = 13712489) B13712489
theorem B2031311 : Blo 1202418 2031311 := bstep (se 1 (by rfl) ⟨1523483, by rfl⟩ : syracuseStep 2031311 = 3046967) B3046967
theorem B5144543 : Blo 1202418 5144543 := bstep (se 1 (by rfl) ⟨3858407, by rfl⟩ : syracuseStep 5144543 = 7716815) B7716815
theorem B13705199 : Blo 1202418 13705199 := bstep (se 1 (by rfl) ⟨10278899, by rfl⟩ : syracuseStep 13705199 = 20557799) B20557799
theorem B9142631 : Blo 1202418 9142631 := bstep (se 1 (by rfl) ⟨6856973, by rfl⟩ : syracuseStep 9142631 = 13713947) B13713947
theorem B10281977 : Blo 1202418 10281977 := bstep (se 2 (by rfl) ⟨3855741, by rfl⟩ : syracuseStep 10281977 = 7711483) B7711483
theorem B3048475 : Blo 1202418 3048475 := bstep (se 1 (by rfl) ⟨2286356, by rfl⟩ : syracuseStep 3048475 = 4572713) B4572713
theorem B91498351 : Blo 1202418 91498351 := bstep (se 1 (by rfl) ⟨68623763, by rfl⟩ : syracuseStep 91498351 = 137247527) B137247527
theorem B1354207 : Blo 1202418 1354207 := bstep (se 1 (by rfl) ⟨1015655, by rfl⟩ : syracuseStep 1354207 = 2031311) B2031311
theorem B16927289 : Blo 1202418 16927289 := bstep (se 2 (by rfl) ⟨6347733, by rfl⟩ : syracuseStep 16927289 = 12695467) B12695467
theorem B1804955 : Blo 1202418 1804955 := bstep (se 1 (by rfl) ⟨1353716, by rfl⟩ : syracuseStep 1804955 = 2707433) B2707433
theorem B9136799 : Blo 1202418 9136799 := bstep (se 1 (by rfl) ⟨6852599, by rfl⟩ : syracuseStep 9136799 = 13705199) B13705199
theorem B9752255 : Blo 1202418 9752255 := bstep (se 1 (by rfl) ⟨7314191, by rfl⟩ : syracuseStep 9752255 = 14628383) B14628383
theorem B3429695 : Blo 1202418 3429695 := bstep (se 1 (by rfl) ⟨2572271, by rfl⟩ : syracuseStep 3429695 = 5144543) B5144543
theorem B2029097 : Blo 1202418 2029097 := bstep (se 2 (by rfl) ⟨760911, by rfl⟩ : syracuseStep 2029097 = 1521823) B1521823
theorem B6093467 : Blo 1202418 6093467 := bstep (se 1 (by rfl) ⟨4570100, by rfl⟩ : syracuseStep 6093467 = 9140201) B9140201
theorem B1203071 : Blo 1202418 1203071 := bstep (se 1 (by rfl) ⟨902303, by rfl⟩ : syracuseStep 1203071 = 1804607) B1804607
theorem B211155943 : Blo 1202418 211155943 := bstep (se 1 (by rfl) ⟨158366957, by rfl⟩ : syracuseStep 211155943 = 316733915) B316733915
theorem B9641375 : Blo 1202418 9641375 := bstep (se 1 (by rfl) ⟨7231031, by rfl⟩ : syracuseStep 9641375 = 14462063) B14462063
theorem B6094439 : Blo 1202418 6094439 := bstep (se 1 (by rfl) ⟨4570829, by rfl⟩ : syracuseStep 6094439 = 9141659) B9141659
theorem B6095087 : Blo 1202418 6095087 := bstep (se 1 (by rfl) ⟨4571315, by rfl⟩ : syracuseStep 6095087 = 9142631) B9142631
theorem B2286463 : Blo 1202418 2286463 := bstep (se 1 (by rfl) ⟨1714847, by rfl⟩ : syracuseStep 2286463 = 3429695) B3429695
theorem B1352731 : Blo 1202418 1352731 := bstep (se 1 (by rfl) ⟨1014548, by rfl⟩ : syracuseStep 1352731 = 2029097) B2029097
theorem B4064633 : Blo 1202418 4064633 := bstep (se 2 (by rfl) ⟨1524237, by rfl⟩ : syracuseStep 4064633 = 3048475) B3048475
theorem B121997801 : Blo 1202418 121997801 := bstep (se 2 (by rfl) ⟨45749175, by rfl⟩ : syracuseStep 121997801 = 91498351) B91498351
theorem B1805609 : Blo 1202418 1805609 := bstep (se 2 (by rfl) ⟨677103, by rfl⟩ : syracuseStep 1805609 = 1354207) B1354207
theorem B11284859 : Blo 1202418 11284859 := bstep (se 1 (by rfl) ⟨8463644, by rfl⟩ : syracuseStep 11284859 = 16927289) B16927289
theorem B6091199 : Blo 1202418 6091199 := bstep (se 1 (by rfl) ⟨4568399, by rfl⟩ : syracuseStep 6091199 = 9136799) B9136799
theorem B6427583 : Blo 1202418 6427583 := bstep (se 1 (by rfl) ⟨4820687, by rfl⟩ : syracuseStep 6427583 = 9641375) B9641375
theorem B6501503 : Blo 1202418 6501503 := bstep (se 1 (by rfl) ⟨4876127, by rfl⟩ : syracuseStep 6501503 = 9752255) B9752255
theorem B6854651 : Blo 1202418 6854651 := bstep (se 1 (by rfl) ⟨5140988, by rfl⟩ : syracuseStep 6854651 = 10281977) B10281977
theorem B281541257 : Blo 1202418 281541257 := bstep (se 2 (by rfl) ⟨105577971, by rfl⟩ : syracuseStep 281541257 = 211155943) B211155943
theorem B1203303 : Blo 1202418 1203303 := bstep (se 1 (by rfl) ⟨902477, by rfl⟩ : syracuseStep 1203303 = 1804955) B1804955
theorem B4062311 : Blo 1202418 4062311 := bstep (se 1 (by rfl) ⟨3046733, by rfl⟩ : syracuseStep 4062311 = 6093467) B6093467
theorem B4062959 : Blo 1202418 4062959 := bstep (se 1 (by rfl) ⟨3047219, by rfl⟩ : syracuseStep 4062959 = 6094439) B6094439
theorem B4063391 : Blo 1202418 4063391 := bstep (se 1 (by rfl) ⟨3047543, by rfl⟩ : syracuseStep 4063391 = 6095087) B6095087
theorem B4285055 : Blo 1202418 4285055 := bstep (se 1 (by rfl) ⟨3213791, by rfl⟩ : syracuseStep 4285055 = 6427583) B6427583
theorem B3048617 : Blo 1202418 3048617 := bstep (se 2 (by rfl) ⟨1143231, by rfl⟩ : syracuseStep 3048617 = 2286463) B2286463
theorem B1803641 : Blo 1202418 1803641 := bstep (se 2 (by rfl) ⟨676365, by rfl⟩ : syracuseStep 1803641 = 1352731) B1352731
theorem B81331867 : Blo 1202418 81331867 := bstep (se 1 (by rfl) ⟨60998900, by rfl⟩ : syracuseStep 81331867 = 121997801) B121997801
theorem B7523239 : Blo 1202418 7523239 := bstep (se 1 (by rfl) ⟨5642429, by rfl⟩ : syracuseStep 7523239 = 11284859) B11284859
theorem B17337341 : Blo 1202418 17337341 := bstep (se 3 (by rfl) ⟨3250751, by rfl⟩ : syracuseStep 17337341 = 6501503) B6501503
theorem B2708207 : Blo 1202418 2708207 := bstep (se 1 (by rfl) ⟨2031155, by rfl⟩ : syracuseStep 2708207 = 4062311) B4062311
theorem B2708639 : Blo 1202418 2708639 := bstep (se 1 (by rfl) ⟨2031479, by rfl⟩ : syracuseStep 2708639 = 4062959) B4062959
theorem B4060799 : Blo 1202418 4060799 := bstep (se 1 (by rfl) ⟨3045599, by rfl⟩ : syracuseStep 4060799 = 6091199) B6091199
theorem B2709755 : Blo 1202418 2709755 := bstep (se 1 (by rfl) ⟨2032316, by rfl⟩ : syracuseStep 2709755 = 4064633) B4064633
theorem B4569767 : Blo 1202418 4569767 := bstep (se 1 (by rfl) ⟨3427325, by rfl⟩ : syracuseStep 4569767 = 6854651) B6854651
theorem B187694171 : Blo 1202418 187694171 := bstep (se 1 (by rfl) ⟨140770628, by rfl⟩ : syracuseStep 187694171 = 281541257) B281541257
theorem B1203739 : Blo 1202418 1203739 := bstep (se 1 (by rfl) ⟨902804, by rfl⟩ : syracuseStep 1203739 = 1805609) B1805609
theorem B2032411 : Blo 1202418 2032411 := bstep (se 1 (by rfl) ⟨1524308, by rfl⟩ : syracuseStep 2032411 = 3048617) B3048617
theorem B1805471 : Blo 1202418 1805471 := bstep (se 1 (by rfl) ⟨1354103, by rfl⟩ : syracuseStep 1805471 = 2708207) B2708207
theorem B1805759 : Blo 1202418 1805759 := bstep (se 1 (by rfl) ⟨1354319, by rfl⟩ : syracuseStep 1805759 = 2708639) B2708639
theorem B2707199 : Blo 1202418 2707199 := bstep (se 1 (by rfl) ⟨2030399, by rfl⟩ : syracuseStep 2707199 = 4060799) B4060799
theorem B10030985 : Blo 1202418 10030985 := bstep (se 2 (by rfl) ⟨3761619, by rfl⟩ : syracuseStep 10030985 = 7523239) B7523239
theorem B1806503 : Blo 1202418 1806503 := bstep (se 1 (by rfl) ⟨1354877, by rfl⟩ : syracuseStep 1806503 = 2709755) B2709755
theorem B125129447 : Blo 1202418 125129447 := bstep (se 1 (by rfl) ⟨93847085, by rfl⟩ : syracuseStep 125129447 = 187694171) B187694171
theorem B108442489 : Blo 1202418 108442489 := bstep (se 2 (by rfl) ⟨40665933, by rfl⟩ : syracuseStep 108442489 = 81331867) B81331867
theorem B2708927 : Blo 1202418 2708927 := bstep (se 1 (by rfl) ⟨2031695, by rfl⟩ : syracuseStep 2708927 = 4063391) B4063391
theorem B2856703 : Blo 1202418 2856703 := bstep (se 1 (by rfl) ⟨2142527, by rfl⟩ : syracuseStep 2856703 = 4285055) B4285055
theorem B1202427 : Blo 1202418 1202427 := bstep (se 1 (by rfl) ⟨901820, by rfl⟩ : syracuseStep 1202427 = 1803641) B1803641
theorem B3046511 : Blo 1202418 3046511 := bstep (se 1 (by rfl) ⟨2284883, by rfl⟩ : syracuseStep 3046511 = 4569767) B4569767
theorem B11558227 : Blo 1202418 11558227 := bstep (se 1 (by rfl) ⟨8668670, by rfl⟩ : syracuseStep 11558227 = 17337341) B17337341
theorem B1204335 : Blo 1202418 1204335 := bstep (se 1 (by rfl) ⟨903251, by rfl⟩ : syracuseStep 1204335 = 1806503) B1806503
theorem B83419631 : Blo 1202418 83419631 := bstep (se 1 (by rfl) ⟨62564723, by rfl⟩ : syracuseStep 83419631 = 125129447) B125129447
theorem B144589985 : Blo 1202418 144589985 := bstep (se 2 (by rfl) ⟨54221244, by rfl⟩ : syracuseStep 144589985 = 108442489) B108442489
theorem B15410969 : Blo 1202418 15410969 := bstep (se 2 (by rfl) ⟨5779113, by rfl⟩ : syracuseStep 15410969 = 11558227) B11558227
theorem B1804799 : Blo 1202418 1804799 := bstep (se 1 (by rfl) ⟨1353599, by rfl⟩ : syracuseStep 1804799 = 2707199) B2707199
theorem B6687323 : Blo 1202418 6687323 := bstep (se 1 (by rfl) ⟨5015492, by rfl⟩ : syracuseStep 6687323 = 10030985) B10030985
theorem B1805951 : Blo 1202418 1805951 := bstep (se 1 (by rfl) ⟨1354463, by rfl⟩ : syracuseStep 1805951 = 2708927) B2708927
theorem B2709881 : Blo 1202418 2709881 := bstep (se 2 (by rfl) ⟨1016205, by rfl⟩ : syracuseStep 2709881 = 2032411) B2032411
theorem B2031007 : Blo 1202418 2031007 := bstep (se 1 (by rfl) ⟨1523255, by rfl⟩ : syracuseStep 2031007 = 3046511) B3046511
theorem B1203647 : Blo 1202418 1203647 := bstep (se 1 (by rfl) ⟨902735, by rfl⟩ : syracuseStep 1203647 = 1805471) B1805471
theorem B1203839 : Blo 1202418 1203839 := bstep (se 1 (by rfl) ⟨902879, by rfl⟩ : syracuseStep 1203839 = 1805759) B1805759
theorem B3808937 : Blo 1202418 3808937 := bstep (se 2 (by rfl) ⟨1428351, by rfl⟩ : syracuseStep 3808937 = 2856703) B2856703
theorem B10273979 : Blo 1202418 10273979 := bstep (se 1 (by rfl) ⟨7705484, by rfl⟩ : syracuseStep 10273979 = 15410969) B15410969
theorem B4458215 : Blo 1202418 4458215 := bstep (se 1 (by rfl) ⟨3343661, by rfl⟩ : syracuseStep 4458215 = 6687323) B6687323
theorem B1806587 : Blo 1202418 1806587 := bstep (se 1 (by rfl) ⟨1354940, by rfl⟩ : syracuseStep 1806587 = 2709881) B2709881
theorem B2708009 : Blo 1202418 2708009 := bstep (se 2 (by rfl) ⟨1015503, by rfl⟩ : syracuseStep 2708009 = 2031007) B2031007
theorem B55613087 : Blo 1202418 55613087 := bstep (se 1 (by rfl) ⟨41709815, by rfl⟩ : syracuseStep 55613087 = 83419631) B83419631
theorem B96393323 : Blo 1202418 96393323 := bstep (se 1 (by rfl) ⟨72294992, by rfl⟩ : syracuseStep 96393323 = 144589985) B144589985
theorem B1203199 : Blo 1202418 1203199 := bstep (se 1 (by rfl) ⟨902399, by rfl⟩ : syracuseStep 1203199 = 1804799) B1804799
theorem B1203967 : Blo 1202418 1203967 := bstep (se 1 (by rfl) ⟨902975, by rfl⟩ : syracuseStep 1203967 = 1805951) B1805951
theorem B2539291 : Blo 1202418 2539291 := bstep (se 1 (by rfl) ⟨1904468, by rfl⟩ : syracuseStep 2539291 = 3808937) B3808937
theorem B1204391 : Blo 1202418 1204391 := bstep (se 1 (by rfl) ⟨903293, by rfl⟩ : syracuseStep 1204391 = 1806587) B1806587
theorem B6849319 : Blo 1202418 6849319 := bstep (se 1 (by rfl) ⟨5136989, by rfl⟩ : syracuseStep 6849319 = 10273979) B10273979
theorem B3385721 : Blo 1202418 3385721 := bstep (se 2 (by rfl) ⟨1269645, by rfl⟩ : syracuseStep 3385721 = 2539291) B2539291
theorem B1805339 : Blo 1202418 1805339 := bstep (se 1 (by rfl) ⟨1354004, by rfl⟩ : syracuseStep 1805339 = 2708009) B2708009
theorem B64262215 : Blo 1202418 64262215 := bstep (se 1 (by rfl) ⟨48196661, by rfl⟩ : syracuseStep 64262215 = 96393323) B96393323
theorem B37075391 : Blo 1202418 37075391 := bstep (se 1 (by rfl) ⟨27806543, by rfl⟩ : syracuseStep 37075391 = 55613087) B55613087
theorem B2972143 : Blo 1202418 2972143 := bstep (se 1 (by rfl) ⟨2229107, by rfl⟩ : syracuseStep 2972143 = 4458215) B4458215
theorem B24716927 : Blo 1202418 24716927 := bstep (se 1 (by rfl) ⟨18537695, by rfl⟩ : syracuseStep 24716927 = 37075391) B37075391
theorem B85682953 : Blo 1202418 85682953 := bstep (se 2 (by rfl) ⟨32131107, by rfl⟩ : syracuseStep 85682953 = 64262215) B64262215
theorem B2257147 : Blo 1202418 2257147 := bstep (se 1 (by rfl) ⟨1692860, by rfl⟩ : syracuseStep 2257147 = 3385721) B3385721
theorem B3962857 : Blo 1202418 3962857 := bstep (se 2 (by rfl) ⟨1486071, by rfl⟩ : syracuseStep 3962857 = 2972143) B2972143
theorem B9132425 : Blo 1202418 9132425 := bstep (se 2 (by rfl) ⟨3424659, by rfl⟩ : syracuseStep 9132425 = 6849319) B6849319
theorem B1203559 : Blo 1202418 1203559 := bstep (se 1 (by rfl) ⟨902669, by rfl⟩ : syracuseStep 1203559 = 1805339) B1805339
theorem B456975749 : Blo 1202418 456975749 := bstep (se 4 (by rfl) ⟨42841476, by rfl⟩ : syracuseStep 456975749 = 85682953) B85682953
theorem B6088283 : Blo 1202418 6088283 := bstep (se 1 (by rfl) ⟨4566212, by rfl⟩ : syracuseStep 6088283 = 9132425) B9132425
theorem B3009529 : Blo 1202418 3009529 := bstep (se 2 (by rfl) ⟨1128573, by rfl⟩ : syracuseStep 3009529 = 2257147) B2257147
theorem B65911805 : Blo 1202418 65911805 := bstep (se 3 (by rfl) ⟨12358463, by rfl⟩ : syracuseStep 65911805 = 24716927) B24716927
theorem B5283809 : Blo 1202418 5283809 := bstep (se 2 (by rfl) ⟨1981428, by rfl⟩ : syracuseStep 5283809 = 3962857) B3962857
theorem B4058855 : Blo 1202418 4058855 := bstep (se 1 (by rfl) ⟨3044141, by rfl⟩ : syracuseStep 4058855 = 6088283) B6088283
theorem B304650499 : Blo 1202418 304650499 := bstep (se 1 (by rfl) ⟨228487874, by rfl⟩ : syracuseStep 304650499 = 456975749) B456975749
theorem B4012705 : Blo 1202418 4012705 := bstep (se 2 (by rfl) ⟨1504764, by rfl⟩ : syracuseStep 4012705 = 3009529) B3009529
theorem B43941203 : Blo 1202418 43941203 := bstep (se 1 (by rfl) ⟨32955902, by rfl⟩ : syracuseStep 43941203 = 65911805) B65911805
theorem B3522539 : Blo 1202418 3522539 := bstep (se 1 (by rfl) ⟨2641904, by rfl⟩ : syracuseStep 3522539 = 5283809) B5283809
theorem B406200665 : Blo 1202418 406200665 := bstep (se 2 (by rfl) ⟨152325249, by rfl⟩ : syracuseStep 406200665 = 304650499) B304650499
theorem B5350273 : Blo 1202418 5350273 := bstep (se 2 (by rfl) ⟨2006352, by rfl⟩ : syracuseStep 5350273 = 4012705) B4012705
theorem B2705903 : Blo 1202418 2705903 := bstep (se 1 (by rfl) ⟨2029427, by rfl⟩ : syracuseStep 2705903 = 4058855) B4058855
theorem B2348359 : Blo 1202418 2348359 := bstep (se 1 (by rfl) ⟨1761269, by rfl⟩ : syracuseStep 2348359 = 3522539) B3522539
theorem B29294135 : Blo 1202418 29294135 := bstep (se 1 (by rfl) ⟨21970601, by rfl⟩ : syracuseStep 29294135 = 43941203) B43941203
theorem B1803935 : Blo 1202418 1803935 := bstep (se 1 (by rfl) ⟨1352951, by rfl⟩ : syracuseStep 1803935 = 2705903) B2705903
theorem B28534789 : Blo 1202418 28534789 := bstep (se 4 (by rfl) ⟨2675136, by rfl⟩ : syracuseStep 28534789 = 5350273) B5350273
theorem B270800443 : Blo 1202418 270800443 := bstep (se 1 (by rfl) ⟨203100332, by rfl⟩ : syracuseStep 270800443 = 406200665) B406200665
theorem B12524581 : Blo 1202418 12524581 := bstep (se 4 (by rfl) ⟨1174179, by rfl⟩ : syracuseStep 12524581 = 2348359) B2348359
theorem B19529423 : Blo 1202418 19529423 := bstep (se 1 (by rfl) ⟨14647067, by rfl⟩ : syracuseStep 19529423 = 29294135) B29294135
theorem B13019615 : Blo 1202418 13019615 := bstep (se 1 (by rfl) ⟨9764711, by rfl⟩ : syracuseStep 13019615 = 19529423) B19529423
theorem B38046385 : Blo 1202418 38046385 := bstep (se 2 (by rfl) ⟨14267394, by rfl⟩ : syracuseStep 38046385 = 28534789) B28534789
theorem B16699441 : Blo 1202418 16699441 := bstep (se 2 (by rfl) ⟨6262290, by rfl⟩ : syracuseStep 16699441 = 12524581) B12524581
theorem B361067257 : Blo 1202418 361067257 := bstep (se 2 (by rfl) ⟨135400221, by rfl⟩ : syracuseStep 361067257 = 270800443) B270800443
theorem B1202623 : Blo 1202418 1202623 := bstep (se 1 (by rfl) ⟨901967, by rfl⟩ : syracuseStep 1202623 = 1803935) B1803935
theorem B22265921 : Blo 1202418 22265921 := bstep (se 2 (by rfl) ⟨8349720, by rfl⟩ : syracuseStep 22265921 = 16699441) B16699441
theorem B50728513 : Blo 1202418 50728513 := bstep (se 2 (by rfl) ⟨19023192, by rfl⟩ : syracuseStep 50728513 = 38046385) B38046385
theorem B481423009 : Blo 1202418 481423009 := bstep (se 2 (by rfl) ⟨180533628, by rfl⟩ : syracuseStep 481423009 = 361067257) B361067257
theorem B8679743 : Blo 1202418 8679743 := bstep (se 1 (by rfl) ⟨6509807, by rfl⟩ : syracuseStep 8679743 = 13019615) B13019615
theorem B14843947 : Blo 1202418 14843947 := bstep (se 1 (by rfl) ⟨11132960, by rfl⟩ : syracuseStep 14843947 = 22265921) B22265921
theorem B5786495 : Blo 1202418 5786495 := bstep (se 1 (by rfl) ⟨4339871, by rfl⟩ : syracuseStep 5786495 = 8679743) B8679743
theorem B67638017 : Blo 1202418 67638017 := bstep (se 2 (by rfl) ⟨25364256, by rfl⟩ : syracuseStep 67638017 = 50728513) B50728513
theorem B641897345 : Blo 1202418 641897345 := bstep (se 2 (by rfl) ⟨240711504, by rfl⟩ : syracuseStep 641897345 = 481423009) B481423009
theorem B19791929 : Blo 1202418 19791929 := bstep (se 2 (by rfl) ⟨7421973, by rfl⟩ : syracuseStep 19791929 = 14843947) B14843947
theorem B45092011 : Blo 1202418 45092011 := bstep (se 1 (by rfl) ⟨33819008, by rfl⟩ : syracuseStep 45092011 = 67638017) B67638017
theorem B3857663 : Blo 1202418 3857663 := bstep (se 1 (by rfl) ⟨2893247, by rfl⟩ : syracuseStep 3857663 = 5786495) B5786495
theorem B1711726253 : Blo 1202418 1711726253 := bstep (se 3 (by rfl) ⟨320948672, by rfl⟩ : syracuseStep 1711726253 = 641897345) B641897345
theorem B60122681 : Blo 1202418 60122681 := bstep (se 2 (by rfl) ⟨22546005, by rfl⟩ : syracuseStep 60122681 = 45092011) B45092011
theorem B1141150835 : Blo 1202418 1141150835 := bstep (se 1 (by rfl) ⟨855863126, by rfl⟩ : syracuseStep 1141150835 = 1711726253) B1711726253
theorem B13194619 : Blo 1202418 13194619 := bstep (se 1 (by rfl) ⟨9895964, by rfl⟩ : syracuseStep 13194619 = 19791929) B19791929
theorem B10287101 : Blo 1202418 10287101 := bstep (se 3 (by rfl) ⟨1928831, by rfl⟩ : syracuseStep 10287101 = 3857663) B3857663
theorem B760767223 : Blo 1202418 760767223 := bstep (se 1 (by rfl) ⟨570575417, by rfl⟩ : syracuseStep 760767223 = 1141150835) B1141150835
theorem B6858067 : Blo 1202418 6858067 := bstep (se 1 (by rfl) ⟨5143550, by rfl⟩ : syracuseStep 6858067 = 10287101) B10287101
theorem B70371301 : Blo 1202418 70371301 := bstep (se 4 (by rfl) ⟨6597309, by rfl⟩ : syracuseStep 70371301 = 13194619) B13194619
theorem B40081787 : Blo 1202418 40081787 := bstep (se 1 (by rfl) ⟨30061340, by rfl⟩ : syracuseStep 40081787 = 60122681) B60122681
theorem B9144089 : Blo 1202418 9144089 := bstep (se 2 (by rfl) ⟨3429033, by rfl⟩ : syracuseStep 9144089 = 6858067) B6858067
theorem B93828401 : Blo 1202418 93828401 := bstep (se 2 (by rfl) ⟨35185650, by rfl⟩ : syracuseStep 93828401 = 70371301) B70371301
theorem B1014356297 : Blo 1202418 1014356297 := bstep (se 2 (by rfl) ⟨380383611, by rfl⟩ : syracuseStep 1014356297 = 760767223) B760767223
theorem B26721191 : Blo 1202418 26721191 := bstep (se 1 (by rfl) ⟨20040893, by rfl⟩ : syracuseStep 26721191 = 40081787) B40081787
theorem B6096059 : Blo 1202418 6096059 := bstep (se 1 (by rfl) ⟨4572044, by rfl⟩ : syracuseStep 6096059 = 9144089) B9144089
theorem B676237531 : Blo 1202418 676237531 := bstep (se 1 (by rfl) ⟨507178148, by rfl⟩ : syracuseStep 676237531 = 1014356297) B1014356297
theorem B17814127 : Blo 1202418 17814127 := bstep (se 1 (by rfl) ⟨13360595, by rfl⟩ : syracuseStep 17814127 = 26721191) B26721191
theorem B62552267 : Blo 1202418 62552267 := bstep (se 1 (by rfl) ⟨46914200, by rfl⟩ : syracuseStep 62552267 = 93828401) B93828401
theorem B4064039 : Blo 1202418 4064039 := bstep (se 1 (by rfl) ⟨3048029, by rfl⟩ : syracuseStep 4064039 = 6096059) B6096059
theorem B23752169 : Blo 1202418 23752169 := bstep (se 2 (by rfl) ⟨8907063, by rfl⟩ : syracuseStep 23752169 = 17814127) B17814127
theorem B41701511 : Blo 1202418 41701511 := bstep (se 1 (by rfl) ⟨31276133, by rfl⟩ : syracuseStep 41701511 = 62552267) B62552267
theorem B901650041 : Blo 1202418 901650041 := bstep (se 2 (by rfl) ⟨338118765, by rfl⟩ : syracuseStep 901650041 = 676237531) B676237531
theorem B601100027 : Blo 1202418 601100027 := bstep (se 1 (by rfl) ⟨450825020, by rfl⟩ : syracuseStep 601100027 = 901650041) B901650041
theorem B111204029 : Blo 1202418 111204029 := bstep (se 3 (by rfl) ⟨20850755, by rfl⟩ : syracuseStep 111204029 = 41701511) B41701511
theorem B2709359 : Blo 1202418 2709359 := bstep (se 1 (by rfl) ⟨2032019, by rfl⟩ : syracuseStep 2709359 = 4064039) B4064039
theorem B15834779 : Blo 1202418 15834779 := bstep (se 1 (by rfl) ⟨11876084, by rfl⟩ : syracuseStep 15834779 = 23752169) B23752169
theorem B296544077 : Blo 1202418 296544077 := bstep (se 3 (by rfl) ⟨55602014, by rfl⟩ : syracuseStep 296544077 = 111204029) B111204029
theorem B1806239 : Blo 1202418 1806239 := bstep (se 1 (by rfl) ⟨1354679, by rfl⟩ : syracuseStep 1806239 = 2709359) B2709359
theorem B10556519 : Blo 1202418 10556519 := bstep (se 1 (by rfl) ⟨7917389, by rfl⟩ : syracuseStep 10556519 = 15834779) B15834779
theorem B400733351 : Blo 1202418 400733351 := bstep (se 1 (by rfl) ⟨300550013, by rfl⟩ : syracuseStep 400733351 = 601100027) B601100027
theorem B112602869 : Blo 1202418 112602869 := bstep (se 5 (by rfl) ⟨5278259, by rfl⟩ : syracuseStep 112602869 = 10556519) B10556519
theorem B267155567 : Blo 1202418 267155567 := bstep (se 1 (by rfl) ⟨200366675, by rfl⟩ : syracuseStep 267155567 = 400733351) B400733351
theorem B197696051 : Blo 1202418 197696051 := bstep (se 1 (by rfl) ⟨148272038, by rfl⟩ : syracuseStep 197696051 = 296544077) B296544077
theorem B1204159 : Blo 1202418 1204159 := bstep (se 1 (by rfl) ⟨903119, by rfl⟩ : syracuseStep 1204159 = 1806239) B1806239
theorem B178103711 : Blo 1202418 178103711 := bstep (se 1 (by rfl) ⟨133577783, by rfl⟩ : syracuseStep 178103711 = 267155567) B267155567
theorem B131797367 : Blo 1202418 131797367 := bstep (se 1 (by rfl) ⟨98848025, by rfl⟩ : syracuseStep 131797367 = 197696051) B197696051
theorem B75068579 : Blo 1202418 75068579 := bstep (se 1 (by rfl) ⟨56301434, by rfl⟩ : syracuseStep 75068579 = 112602869) B112602869
theorem B118735807 : Blo 1202418 118735807 := bstep (se 1 (by rfl) ⟨89051855, by rfl⟩ : syracuseStep 118735807 = 178103711) B178103711
theorem B200182877 : Blo 1202418 200182877 := bstep (se 3 (by rfl) ⟨37534289, by rfl⟩ : syracuseStep 200182877 = 75068579) B75068579
theorem B87864911 : Blo 1202418 87864911 := bstep (se 1 (by rfl) ⟨65898683, by rfl⟩ : syracuseStep 87864911 = 131797367) B131797367
theorem B58576607 : Blo 1202418 58576607 := bstep (se 1 (by rfl) ⟨43932455, by rfl⟩ : syracuseStep 58576607 = 87864911) B87864911
theorem B158314409 : Blo 1202418 158314409 := bstep (se 2 (by rfl) ⟨59367903, by rfl⟩ : syracuseStep 158314409 = 118735807) B118735807
theorem B133455251 : Blo 1202418 133455251 := bstep (se 1 (by rfl) ⟨100091438, by rfl⟩ : syracuseStep 133455251 = 200182877) B200182877
theorem B88970167 : Blo 1202418 88970167 := bstep (se 1 (by rfl) ⟨66727625, by rfl⟩ : syracuseStep 88970167 = 133455251) B133455251
theorem B105542939 : Blo 1202418 105542939 := bstep (se 1 (by rfl) ⟨79157204, by rfl⟩ : syracuseStep 105542939 = 158314409) B158314409
theorem B39051071 : Blo 1202418 39051071 := bstep (se 1 (by rfl) ⟨29288303, by rfl⟩ : syracuseStep 39051071 = 58576607) B58576607
theorem B70361959 : Blo 1202418 70361959 := bstep (se 1 (by rfl) ⟨52771469, by rfl⟩ : syracuseStep 70361959 = 105542939) B105542939
theorem B118626889 : Blo 1202418 118626889 := bstep (se 2 (by rfl) ⟨44485083, by rfl⟩ : syracuseStep 118626889 = 88970167) B88970167
theorem B26034047 : Blo 1202418 26034047 := bstep (se 1 (by rfl) ⟨19525535, by rfl⟩ : syracuseStep 26034047 = 39051071) B39051071
theorem B93815945 : Blo 1202418 93815945 := bstep (se 2 (by rfl) ⟨35180979, by rfl⟩ : syracuseStep 93815945 = 70361959) B70361959
theorem B17356031 : Blo 1202418 17356031 := bstep (se 1 (by rfl) ⟨13017023, by rfl⟩ : syracuseStep 17356031 = 26034047) B26034047
theorem B158169185 : Blo 1202418 158169185 := bstep (se 2 (by rfl) ⟨59313444, by rfl⟩ : syracuseStep 158169185 = 118626889) B118626889
theorem B11570687 : Blo 1202418 11570687 := bstep (se 1 (by rfl) ⟨8678015, by rfl⟩ : syracuseStep 11570687 = 17356031) B17356031
theorem B62543963 : Blo 1202418 62543963 := bstep (se 1 (by rfl) ⟨46907972, by rfl⟩ : syracuseStep 62543963 = 93815945) B93815945
theorem B105446123 : Blo 1202418 105446123 := bstep (se 1 (by rfl) ⟨79084592, by rfl⟩ : syracuseStep 105446123 = 158169185) B158169185
theorem B70297415 : Blo 1202418 70297415 := bstep (se 1 (by rfl) ⟨52723061, by rfl⟩ : syracuseStep 70297415 = 105446123) B105446123
theorem B7713791 : Blo 1202418 7713791 := bstep (se 1 (by rfl) ⟨5785343, by rfl⟩ : syracuseStep 7713791 = 11570687) B11570687
theorem B41695975 : Blo 1202418 41695975 := bstep (se 1 (by rfl) ⟨31271981, by rfl⟩ : syracuseStep 41695975 = 62543963) B62543963
theorem B55594633 : Blo 1202418 55594633 := bstep (se 2 (by rfl) ⟨20847987, by rfl⟩ : syracuseStep 55594633 = 41695975) B41695975
theorem B5142527 : Blo 1202418 5142527 := bstep (se 1 (by rfl) ⟨3856895, by rfl⟩ : syracuseStep 5142527 = 7713791) B7713791
theorem B46864943 : Blo 1202418 46864943 := bstep (se 1 (by rfl) ⟨35148707, by rfl⟩ : syracuseStep 46864943 = 70297415) B70297415
theorem B3428351 : Blo 1202418 3428351 := bstep (se 1 (by rfl) ⟨2571263, by rfl⟩ : syracuseStep 3428351 = 5142527) B5142527
theorem B74126177 : Blo 1202418 74126177 := bstep (se 2 (by rfl) ⟨27797316, by rfl⟩ : syracuseStep 74126177 = 55594633) B55594633
theorem B31243295 : Blo 1202418 31243295 := bstep (se 1 (by rfl) ⟨23432471, by rfl⟩ : syracuseStep 31243295 = 46864943) B46864943
theorem B49417451 : Blo 1202418 49417451 := bstep (se 1 (by rfl) ⟨37063088, by rfl⟩ : syracuseStep 49417451 = 74126177) B74126177
theorem B20828863 : Blo 1202418 20828863 := bstep (se 1 (by rfl) ⟨15621647, by rfl⟩ : syracuseStep 20828863 = 31243295) B31243295
theorem B2285567 : Blo 1202418 2285567 := bstep (se 1 (by rfl) ⟨1714175, by rfl⟩ : syracuseStep 2285567 = 3428351) B3428351
theorem B27771817 : Blo 1202418 27771817 := bstep (se 2 (by rfl) ⟨10414431, by rfl⟩ : syracuseStep 27771817 = 20828863) B20828863
theorem B32944967 : Blo 1202418 32944967 := bstep (se 1 (by rfl) ⟨24708725, by rfl⟩ : syracuseStep 32944967 = 49417451) B49417451
theorem B1523711 : Blo 1202418 1523711 := bstep (se 1 (by rfl) ⟨1142783, by rfl⟩ : syracuseStep 1523711 = 2285567) B2285567
theorem B21963311 : Blo 1202418 21963311 := bstep (se 1 (by rfl) ⟨16472483, by rfl⟩ : syracuseStep 21963311 = 32944967) B32944967
theorem B37029089 : Blo 1202418 37029089 := bstep (se 2 (by rfl) ⟨13885908, by rfl⟩ : syracuseStep 37029089 = 27771817) B27771817
theorem B4063229 : Blo 1202418 4063229 := bstep (se 3 (by rfl) ⟨761855, by rfl⟩ : syracuseStep 4063229 = 1523711) B1523711
theorem B14642207 : Blo 1202418 14642207 := bstep (se 1 (by rfl) ⟨10981655, by rfl⟩ : syracuseStep 14642207 = 21963311) B21963311
theorem B24686059 : Blo 1202418 24686059 := bstep (se 1 (by rfl) ⟨18514544, by rfl⟩ : syracuseStep 24686059 = 37029089) B37029089
theorem B2708819 : Blo 1202418 2708819 := bstep (se 1 (by rfl) ⟨2031614, by rfl⟩ : syracuseStep 2708819 = 4063229) B4063229
theorem B1805879 : Blo 1202418 1805879 := bstep (se 1 (by rfl) ⟨1354409, by rfl⟩ : syracuseStep 1805879 = 2708819) B2708819
theorem B9761471 : Blo 1202418 9761471 := bstep (se 1 (by rfl) ⟨7321103, by rfl⟩ : syracuseStep 9761471 = 14642207) B14642207
theorem B32914745 : Blo 1202418 32914745 := bstep (se 2 (by rfl) ⟨12343029, by rfl⟩ : syracuseStep 32914745 = 24686059) B24686059
theorem B6507647 : Blo 1202418 6507647 := bstep (se 1 (by rfl) ⟨4880735, by rfl⟩ : syracuseStep 6507647 = 9761471) B9761471
theorem B21943163 : Blo 1202418 21943163 := bstep (se 1 (by rfl) ⟨16457372, by rfl⟩ : syracuseStep 21943163 = 32914745) B32914745
theorem B1203919 : Blo 1202418 1203919 := bstep (se 1 (by rfl) ⟨902939, by rfl⟩ : syracuseStep 1203919 = 1805879) B1805879
theorem B4338431 : Blo 1202418 4338431 := bstep (se 1 (by rfl) ⟨3253823, by rfl⟩ : syracuseStep 4338431 = 6507647) B6507647
theorem B14628775 : Blo 1202418 14628775 := bstep (se 1 (by rfl) ⟨10971581, by rfl⟩ : syracuseStep 14628775 = 21943163) B21943163
theorem B2892287 : Blo 1202418 2892287 := bstep (se 1 (by rfl) ⟨2169215, by rfl⟩ : syracuseStep 2892287 = 4338431) B4338431
theorem B19505033 : Blo 1202418 19505033 := bstep (se 2 (by rfl) ⟨7314387, by rfl⟩ : syracuseStep 19505033 = 14628775) B14628775
theorem B13003355 : Blo 1202418 13003355 := bstep (se 1 (by rfl) ⟨9752516, by rfl⟩ : syracuseStep 13003355 = 19505033) B19505033
theorem B7712765 : Blo 1202418 7712765 := bstep (se 3 (by rfl) ⟨1446143, by rfl⟩ : syracuseStep 7712765 = 2892287) B2892287
theorem B8668903 : Blo 1202418 8668903 := bstep (se 1 (by rfl) ⟨6501677, by rfl⟩ : syracuseStep 8668903 = 13003355) B13003355
theorem B5141843 : Blo 1202418 5141843 := bstep (se 1 (by rfl) ⟨3856382, by rfl⟩ : syracuseStep 5141843 = 7712765) B7712765
theorem B3427895 : Blo 1202418 3427895 := bstep (se 1 (by rfl) ⟨2570921, by rfl⟩ : syracuseStep 3427895 = 5141843) B5141843
theorem B11558537 : Blo 1202418 11558537 := bstep (se 2 (by rfl) ⟨4334451, by rfl⟩ : syracuseStep 11558537 = 8668903) B8668903
theorem B7705691 : Blo 1202418 7705691 := bstep (se 1 (by rfl) ⟨5779268, by rfl⟩ : syracuseStep 7705691 = 11558537) B11558537
theorem B2285263 : Blo 1202418 2285263 := bstep (se 1 (by rfl) ⟨1713947, by rfl⟩ : syracuseStep 2285263 = 3427895) B3427895
theorem B5137127 : Blo 1202418 5137127 := bstep (se 1 (by rfl) ⟨3852845, by rfl⟩ : syracuseStep 5137127 = 7705691) B7705691
theorem B3047017 : Blo 1202418 3047017 := bstep (se 2 (by rfl) ⟨1142631, by rfl⟩ : syracuseStep 3047017 = 2285263) B2285263
theorem B3424751 : Blo 1202418 3424751 := bstep (se 1 (by rfl) ⟨2568563, by rfl⟩ : syracuseStep 3424751 = 5137127) B5137127
theorem B4062689 : Blo 1202418 4062689 := bstep (se 2 (by rfl) ⟨1523508, by rfl⟩ : syracuseStep 4062689 = 3047017) B3047017
theorem B2708459 : Blo 1202418 2708459 := bstep (se 1 (by rfl) ⟨2031344, by rfl⟩ : syracuseStep 2708459 = 4062689) B4062689
theorem B2283167 : Blo 1202418 2283167 := bstep (se 1 (by rfl) ⟨1712375, by rfl⟩ : syracuseStep 2283167 = 3424751) B3424751
theorem B6088445 : Blo 1202418 6088445 := bstep (se 3 (by rfl) ⟨1141583, by rfl⟩ : syracuseStep 6088445 = 2283167) B2283167
theorem B1805639 : Blo 1202418 1805639 := bstep (se 1 (by rfl) ⟨1354229, by rfl⟩ : syracuseStep 1805639 = 2708459) B2708459
theorem B4058963 : Blo 1202418 4058963 := bstep (se 1 (by rfl) ⟨3044222, by rfl⟩ : syracuseStep 4058963 = 6088445) B6088445
theorem B1203759 : Blo 1202418 1203759 := bstep (se 1 (by rfl) ⟨902819, by rfl⟩ : syracuseStep 1203759 = 1805639) B1805639
theorem B2705975 : Blo 1202418 2705975 := bstep (se 1 (by rfl) ⟨2029481, by rfl⟩ : syracuseStep 2705975 = 4058963) B4058963
theorem B1803983 : Blo 1202418 1803983 := bstep (se 1 (by rfl) ⟨1352987, by rfl⟩ : syracuseStep 1803983 = 2705975) B2705975
theorem B1202655 : Blo 1202418 1202655 := bstep (se 1 (by rfl) ⟨901991, by rfl⟩ : syracuseStep 1202655 = 1803983) B1803983

theorem C0 (j : ℕ) (h1 : 300604 ≤ j) (h2 : j ≤ 301103) : Blo 1202418 (4 * j + 3) := by
  interval_cases j
  · exact B1202419
  · exact B1202423
  · exact B1202427
  · exact B1202431
  · exact B1202435
  · exact B1202439
  · exact B1202443
  · exact B1202447
  · exact B1202451
  · exact B1202455
  · exact B1202459
  · exact B1202463
  · exact B1202467
  · exact B1202471
  · exact B1202475
  · exact B1202479
  · exact B1202483
  · exact B1202487
  · exact B1202491
  · exact B1202495
  · exact B1202499
  · exact B1202503
  · exact B1202507
  · exact B1202511
  · exact B1202515
  · exact B1202519
  · exact B1202523
  · exact B1202527
  · exact B1202531
  · exact B1202535
  · exact B1202539
  · exact B1202543
  · exact B1202547
  · exact B1202551
  · exact B1202555
  · exact B1202559
  · exact B1202563
  · exact B1202567
  · exact B1202571
  · exact B1202575
  · exact B1202579
  · exact B1202583
  · exact B1202587
  · exact B1202591
  · exact B1202595
  · exact B1202599
  · exact B1202603
  · exact B1202607
  · exact B1202611
  · exact B1202615
  · exact B1202619
  · exact B1202623
  · exact B1202627
  · exact B1202631
  · exact B1202635
  · exact B1202639
  · exact B1202643
  · exact B1202647
  · exact B1202651
  · exact B1202655
  · exact B1202659
  · exact B1202663
  · exact B1202667
  · exact B1202671
  · exact B1202675
  · exact B1202679
  · exact B1202683
  · exact B1202687
  · exact B1202691
  · exact B1202695
  · exact B1202699
  · exact B1202703
  · exact B1202707
  · exact B1202711
  · exact B1202715
  · exact B1202719
  · exact B1202723
  · exact B1202727
  · exact B1202731
  · exact B1202735
  · exact B1202739
  · exact B1202743
  · exact B1202747
  · exact B1202751
  · exact B1202755
  · exact B1202759
  · exact B1202763
  · exact B1202767
  · exact B1202771
  · exact B1202775
  · exact B1202779
  · exact B1202783
  · exact B1202787
  · exact B1202791
  · exact B1202795
  · exact B1202799
  · exact B1202803
  · exact B1202807
  · exact B1202811
  · exact B1202815
  · exact B1202819
  · exact B1202823
  · exact B1202827
  · exact B1202831
  · exact B1202835
  · exact B1202839
  · exact B1202843
  · exact B1202847
  · exact B1202851
  · exact B1202855
  · exact B1202859
  · exact B1202863
  · exact B1202867
  · exact B1202871
  · exact B1202875
  · exact B1202879
  · exact B1202883
  · exact B1202887
  · exact B1202891
  · exact B1202895
  · exact B1202899
  · exact B1202903
  · exact B1202907
  · exact B1202911
  · exact B1202915
  · exact B1202919
  · exact B1202923
  · exact B1202927
  · exact B1202931
  · exact B1202935
  · exact B1202939
  · exact B1202943
  · exact B1202947
  · exact B1202951
  · exact B1202955
  · exact B1202959
  · exact B1202963
  · exact B1202967
  · exact B1202971
  · exact B1202975
  · exact B1202979
  · exact B1202983
  · exact B1202987
  · exact B1202991
  · exact B1202995
  · exact B1202999
  · exact B1203003
  · exact B1203007
  · exact B1203011
  · exact B1203015
  · exact B1203019
  · exact B1203023
  · exact B1203027
  · exact B1203031
  · exact B1203035
  · exact B1203039
  · exact B1203043
  · exact B1203047
  · exact B1203051
  · exact B1203055
  · exact B1203059
  · exact B1203063
  · exact B1203067
  · exact B1203071
  · exact B1203075
  · exact B1203079
  · exact B1203083
  · exact B1203087
  · exact B1203091
  · exact B1203095
  · exact B1203099
  · exact B1203103
  · exact B1203107
  · exact B1203111
  · exact B1203115
  · exact B1203119
  · exact B1203123
  · exact B1203127
  · exact B1203131
  · exact B1203135
  · exact B1203139
  · exact B1203143
  · exact B1203147
  · exact B1203151
  · exact B1203155
  · exact B1203159
  · exact B1203163
  · exact B1203167
  · exact B1203171
  · exact B1203175
  · exact B1203179
  · exact B1203183
  · exact B1203187
  · exact B1203191
  · exact B1203195
  · exact B1203199
  · exact B1203203
  · exact B1203207
  · exact B1203211
  · exact B1203215
  · exact B1203219
  · exact B1203223
  · exact B1203227
  · exact B1203231
  · exact B1203235
  · exact B1203239
  · exact B1203243
  · exact B1203247
  · exact B1203251
  · exact B1203255
  · exact B1203259
  · exact B1203263
  · exact B1203267
  · exact B1203271
  · exact B1203275
  · exact B1203279
  · exact B1203283
  · exact B1203287
  · exact B1203291
  · exact B1203295
  · exact B1203299
  · exact B1203303
  · exact B1203307
  · exact B1203311
  · exact B1203315
  · exact B1203319
  · exact B1203323
  · exact B1203327
  · exact B1203331
  · exact B1203335
  · exact B1203339
  · exact B1203343
  · exact B1203347
  · exact B1203351
  · exact B1203355
  · exact B1203359
  · exact B1203363
  · exact B1203367
  · exact B1203371
  · exact B1203375
  · exact B1203379
  · exact B1203383
  · exact B1203387
  · exact B1203391
  · exact B1203395
  · exact B1203399
  · exact B1203403
  · exact B1203407
  · exact B1203411
  · exact B1203415
  · exact B1203419
  · exact B1203423
  · exact B1203427
  · exact B1203431
  · exact B1203435
  · exact B1203439
  · exact B1203443
  · exact B1203447
  · exact B1203451
  · exact B1203455
  · exact B1203459
  · exact B1203463
  · exact B1203467
  · exact B1203471
  · exact B1203475
  · exact B1203479
  · exact B1203483
  · exact B1203487
  · exact B1203491
  · exact B1203495
  · exact B1203499
  · exact B1203503
  · exact B1203507
  · exact B1203511
  · exact B1203515
  · exact B1203519
  · exact B1203523
  · exact B1203527
  · exact B1203531
  · exact B1203535
  · exact B1203539
  · exact B1203543
  · exact B1203547
  · exact B1203551
  · exact B1203555
  · exact B1203559
  · exact B1203563
  · exact B1203567
  · exact B1203571
  · exact B1203575
  · exact B1203579
  · exact B1203583
  · exact B1203587
  · exact B1203591
  · exact B1203595
  · exact B1203599
  · exact B1203603
  · exact B1203607
  · exact B1203611
  · exact B1203615
  · exact B1203619
  · exact B1203623
  · exact B1203627
  · exact B1203631
  · exact B1203635
  · exact B1203639
  · exact B1203643
  · exact B1203647
  · exact B1203651
  · exact B1203655
  · exact B1203659
  · exact B1203663
  · exact B1203667
  · exact B1203671
  · exact B1203675
  · exact B1203679
  · exact B1203683
  · exact B1203687
  · exact B1203691
  · exact B1203695
  · exact B1203699
  · exact B1203703
  · exact B1203707
  · exact B1203711
  · exact B1203715
  · exact B1203719
  · exact B1203723
  · exact B1203727
  · exact B1203731
  · exact B1203735
  · exact B1203739
  · exact B1203743
  · exact B1203747
  · exact B1203751
  · exact B1203755
  · exact B1203759
  · exact B1203763
  · exact B1203767
  · exact B1203771
  · exact B1203775
  · exact B1203779
  · exact B1203783
  · exact B1203787
  · exact B1203791
  · exact B1203795
  · exact B1203799
  · exact B1203803
  · exact B1203807
  · exact B1203811
  · exact B1203815
  · exact B1203819
  · exact B1203823
  · exact B1203827
  · exact B1203831
  · exact B1203835
  · exact B1203839
  · exact B1203843
  · exact B1203847
  · exact B1203851
  · exact B1203855
  · exact B1203859
  · exact B1203863
  · exact B1203867
  · exact B1203871
  · exact B1203875
  · exact B1203879
  · exact B1203883
  · exact B1203887
  · exact B1203891
  · exact B1203895
  · exact B1203899
  · exact B1203903
  · exact B1203907
  · exact B1203911
  · exact B1203915
  · exact B1203919
  · exact B1203923
  · exact B1203927
  · exact B1203931
  · exact B1203935
  · exact B1203939
  · exact B1203943
  · exact B1203947
  · exact B1203951
  · exact B1203955
  · exact B1203959
  · exact B1203963
  · exact B1203967
  · exact B1203971
  · exact B1203975
  · exact B1203979
  · exact B1203983
  · exact B1203987
  · exact B1203991
  · exact B1203995
  · exact B1203999
  · exact B1204003
  · exact B1204007
  · exact B1204011
  · exact B1204015
  · exact B1204019
  · exact B1204023
  · exact B1204027
  · exact B1204031
  · exact B1204035
  · exact B1204039
  · exact B1204043
  · exact B1204047
  · exact B1204051
  · exact B1204055
  · exact B1204059
  · exact B1204063
  · exact B1204067
  · exact B1204071
  · exact B1204075
  · exact B1204079
  · exact B1204083
  · exact B1204087
  · exact B1204091
  · exact B1204095
  · exact B1204099
  · exact B1204103
  · exact B1204107
  · exact B1204111
  · exact B1204115
  · exact B1204119
  · exact B1204123
  · exact B1204127
  · exact B1204131
  · exact B1204135
  · exact B1204139
  · exact B1204143
  · exact B1204147
  · exact B1204151
  · exact B1204155
  · exact B1204159
  · exact B1204163
  · exact B1204167
  · exact B1204171
  · exact B1204175
  · exact B1204179
  · exact B1204183
  · exact B1204187
  · exact B1204191
  · exact B1204195
  · exact B1204199
  · exact B1204203
  · exact B1204207
  · exact B1204211
  · exact B1204215
  · exact B1204219
  · exact B1204223
  · exact B1204227
  · exact B1204231
  · exact B1204235
  · exact B1204239
  · exact B1204243
  · exact B1204247
  · exact B1204251
  · exact B1204255
  · exact B1204259
  · exact B1204263
  · exact B1204267
  · exact B1204271
  · exact B1204275
  · exact B1204279
  · exact B1204283
  · exact B1204287
  · exact B1204291
  · exact B1204295
  · exact B1204299
  · exact B1204303
  · exact B1204307
  · exact B1204311
  · exact B1204315
  · exact B1204319
  · exact B1204323
  · exact B1204327
  · exact B1204331
  · exact B1204335
  · exact B1204339
  · exact B1204343
  · exact B1204347
  · exact B1204351
  · exact B1204355
  · exact B1204359
  · exact B1204363
  · exact B1204367
  · exact B1204371
  · exact B1204375
  · exact B1204379
  · exact B1204383
  · exact B1204387
  · exact B1204391
  · exact B1204395
  · exact B1204399
  · exact B1204403
  · exact B1204407
  · exact B1204411
  · exact B1204415

theorem solution (m : ℕ) (hlo : 1202418 ≤ m) (hhi : m ≤ 1204418) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 300604 ≤ j := by omega
    have hj2 : j ≤ 301103 := by omega
    have hb : Blo 1202418 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
