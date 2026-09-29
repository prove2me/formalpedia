-- Prove2me | solution 1 for syracuse_descends_range_223812_227812
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:43:57.395255+00:00
-- url     : https://prove2.me/submissions/29c46724-c421-4deb-8ed0-cc8cdab92259

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


theorem B229757 : Blo 223812 229757 := bbase (se 3 (by rfl) ⟨43079, by rfl⟩ : syracuseStep 229757 = 86159) (by norm_num)
theorem B426397 : Blo 223812 426397 := bbase (se 3 (by rfl) ⟨79949, by rfl⟩ : syracuseStep 426397 = 159899) (by norm_num)
theorem B1081781 : Blo 223812 1081781 := bbase (se 5 (by rfl) ⟨50708, by rfl⟩ : syracuseStep 1081781 = 101417) (by norm_num)
theorem B426541 : Blo 223812 426541 := bbase (se 3 (by rfl) ⟨79976, by rfl⟩ : syracuseStep 426541 = 159953) (by norm_num)
theorem B1147445 : Blo 223812 1147445 := bbase (se 5 (by rfl) ⟨53786, by rfl⟩ : syracuseStep 1147445 = 107573) (by norm_num)
theorem B852565 : Blo 223812 852565 := bbase (se 8 (by rfl) ⟨4995, by rfl⟩ : syracuseStep 852565 = 9991) (by norm_num)
theorem B426701 : Blo 223812 426701 := bbase (se 3 (by rfl) ⟨80006, by rfl⟩ : syracuseStep 426701 = 160013) (by norm_num)
theorem B361189 : Blo 223812 361189 := bbase (se 4 (by rfl) ⟨33861, by rfl⟩ : syracuseStep 361189 = 67723) (by norm_num)
theorem B17662805 : Blo 223812 17662805 := bbase (se 9 (by rfl) ⟨51746, by rfl⟩ : syracuseStep 17662805 = 103493) (by norm_num)
theorem B426845 : Blo 223812 426845 := bbase (se 3 (by rfl) ⟨80033, by rfl⟩ : syracuseStep 426845 = 160067) (by norm_num)
theorem B852869 : Blo 223812 852869 := bbase (se 4 (by rfl) ⟨79956, by rfl⟩ : syracuseStep 852869 = 159913) (by norm_num)
theorem B721813 : Blo 223812 721813 := bbase (se 6 (by rfl) ⟨16917, by rfl⟩ : syracuseStep 721813 = 33835) (by norm_num)
theorem B427133 : Blo 223812 427133 := bbase (se 3 (by rfl) ⟨80087, by rfl⟩ : syracuseStep 427133 = 160175) (by norm_num)
theorem B1213717 : Blo 223812 1213717 := bbase (se 6 (by rfl) ⟨28446, by rfl⟩ : syracuseStep 1213717 = 56893) (by norm_num)
theorem B427285 : Blo 223812 427285 := bbase (se 6 (by rfl) ⟨10014, by rfl⟩ : syracuseStep 427285 = 20029) (by norm_num)
theorem B1181141 : Blo 223812 1181141 := bbase (se 7 (by rfl) ⟨13841, by rfl⟩ : syracuseStep 1181141 = 27683) (by norm_num)
theorem B460261 : Blo 223812 460261 := bbase (se 4 (by rfl) ⟨43149, by rfl⟩ : syracuseStep 460261 = 86299) (by norm_num)
theorem B460325 : Blo 223812 460325 := bbase (se 4 (by rfl) ⟨43155, by rfl⟩ : syracuseStep 460325 = 86311) (by norm_num)
theorem B493109 : Blo 223812 493109 := bbase (se 5 (by rfl) ⟨23114, by rfl⟩ : syracuseStep 493109 = 46229) (by norm_num)
theorem B427589 : Blo 223812 427589 := bbase (se 4 (by rfl) ⟨40086, by rfl⟩ : syracuseStep 427589 = 80173) (by norm_num)
theorem B1148741 : Blo 223812 1148741 := bbase (se 4 (by rfl) ⟨107694, by rfl⟩ : syracuseStep 1148741 = 215389) (by norm_num)
theorem B1640341 : Blo 223812 1640341 := bbase (se 6 (by rfl) ⟨38445, by rfl⟩ : syracuseStep 1640341 = 76891) (by norm_num)
theorem B755621 : Blo 223812 755621 := bbase (se 4 (by rfl) ⟨70839, by rfl⟩ : syracuseStep 755621 = 141679) (by norm_num)
theorem B526357 : Blo 223812 526357 := bbase (se 6 (by rfl) ⟨12336, by rfl⟩ : syracuseStep 526357 = 24673) (by norm_num)
theorem B362573 : Blo 223812 362573 := bbase (se 3 (by rfl) ⟨67982, by rfl⟩ : syracuseStep 362573 = 135965) (by norm_num)
theorem B362765 : Blo 223812 362765 := bbase (se 3 (by rfl) ⟨68018, by rfl⟩ : syracuseStep 362765 = 136037) (by norm_num)
theorem B2492693 : Blo 223812 2492693 := bbase (se 6 (by rfl) ⟨58422, by rfl⟩ : syracuseStep 2492693 = 116845) (by norm_num)
theorem B428341 : Blo 223812 428341 := bbase (se 5 (by rfl) ⟨20078, by rfl⟩ : syracuseStep 428341 = 40157) (by norm_num)
theorem B756053 : Blo 223812 756053 := bbase (se 10 (by rfl) ⟨1107, by rfl⟩ : syracuseStep 756053 = 2215) (by norm_num)
theorem B428485 : Blo 223812 428485 := bbase (se 4 (by rfl) ⟨40170, by rfl⟩ : syracuseStep 428485 = 80341) (by norm_num)
theorem B428645 : Blo 223812 428645 := bbase (se 4 (by rfl) ⟨40185, by rfl⟩ : syracuseStep 428645 = 80371) (by norm_num)
theorem B428789 : Blo 223812 428789 := bbase (se 5 (by rfl) ⟨20099, by rfl⟩ : syracuseStep 428789 = 40199) (by norm_num)
theorem B756485 : Blo 223812 756485 := bbase (se 4 (by rfl) ⟨70920, by rfl⟩ : syracuseStep 756485 = 141841) (by norm_num)
theorem B854981 : Blo 223812 854981 := bbase (se 4 (by rfl) ⟨80154, by rfl⟩ : syracuseStep 854981 = 160309) (by norm_num)
theorem B429077 : Blo 223812 429077 := bbase (se 6 (by rfl) ⟨10056, by rfl⟩ : syracuseStep 429077 = 20113) (by norm_num)
theorem B1150037 : Blo 223812 1150037 := bbase (se 8 (by rfl) ⟨6738, by rfl⟩ : syracuseStep 1150037 = 13477) (by norm_num)
theorem B1084565 : Blo 223812 1084565 := bbase (se 6 (by rfl) ⟨25419, by rfl⟩ : syracuseStep 1084565 = 50839) (by norm_num)
theorem B429229 : Blo 223812 429229 := bbase (se 3 (by rfl) ⟨80480, by rfl⟩ : syracuseStep 429229 = 160961) (by norm_num)
theorem B756917 : Blo 223812 756917 := bbase (se 5 (by rfl) ⟨35480, by rfl⟩ : syracuseStep 756917 = 70961) (by norm_num)
theorem B855269 : Blo 223812 855269 := bbase (se 4 (by rfl) ⟨80181, by rfl⟩ : syracuseStep 855269 = 160363) (by norm_num)
theorem B1707317 : Blo 223812 1707317 := bbase (se 5 (by rfl) ⟨80030, by rfl⟩ : syracuseStep 1707317 = 160061) (by norm_num)
theorem B429533 : Blo 223812 429533 := bbase (se 3 (by rfl) ⟨80537, by rfl⟩ : syracuseStep 429533 = 161075) (by norm_num)
theorem B364085 : Blo 223812 364085 := bbase (se 5 (by rfl) ⟨17066, by rfl⟩ : syracuseStep 364085 = 34133) (by norm_num)
theorem B1183301 : Blo 223812 1183301 := bbase (se 4 (by rfl) ⟨110934, by rfl⟩ : syracuseStep 1183301 = 221869) (by norm_num)
theorem B757349 : Blo 223812 757349 := bbase (se 4 (by rfl) ⟨71001, by rfl⟩ : syracuseStep 757349 = 142003) (by norm_num)
theorem B1445525 : Blo 223812 1445525 := bbase (se 6 (by rfl) ⟨33879, by rfl⟩ : syracuseStep 1445525 = 67759) (by norm_num)
theorem B364181 : Blo 223812 364181 := bbase (se 6 (by rfl) ⟨8535, by rfl⟩ : syracuseStep 364181 = 17071) (by norm_num)
theorem B364213 : Blo 223812 364213 := bbase (se 5 (by rfl) ⟨17072, by rfl⟩ : syracuseStep 364213 = 34145) (by norm_num)
theorem B691973 : Blo 223812 691973 := bbase (se 4 (by rfl) ⟨64872, by rfl⟩ : syracuseStep 691973 = 129745) (by norm_num)
theorem B921365 : Blo 223812 921365 := bbase (se 6 (by rfl) ⟨21594, by rfl⟩ : syracuseStep 921365 = 43189) (by norm_num)
theorem B1576853 : Blo 223812 1576853 := bbase (se 6 (by rfl) ⟨36957, by rfl⟩ : syracuseStep 1576853 = 73915) (by norm_num)
theorem B2625493 : Blo 223812 2625493 := bbase (se 7 (by rfl) ⟨30767, by rfl⟩ : syracuseStep 2625493 = 61535) (by norm_num)
theorem B757781 : Blo 223812 757781 := bbase (se 6 (by rfl) ⟨17760, by rfl⟩ : syracuseStep 757781 = 35521) (by norm_num)
theorem B430285 : Blo 223812 430285 := bbase (se 3 (by rfl) ⟨80678, by rfl⟩ : syracuseStep 430285 = 161357) (by norm_num)
theorem B430429 : Blo 223812 430429 := bbase (se 3 (by rfl) ⟨80705, by rfl⟩ : syracuseStep 430429 = 161411) (by norm_num)
theorem B1151333 : Blo 223812 1151333 := bbase (se 4 (by rfl) ⟨107937, by rfl⟩ : syracuseStep 1151333 = 215875) (by norm_num)
theorem B856453 : Blo 223812 856453 := bbase (se 4 (by rfl) ⟨80292, by rfl⟩ : syracuseStep 856453 = 160585) (by norm_num)
theorem B2298293 : Blo 223812 2298293 := bbase (se 5 (by rfl) ⟨107732, by rfl⟩ : syracuseStep 2298293 = 215465) (by norm_num)
theorem B758213 : Blo 223812 758213 := bbase (se 4 (by rfl) ⟨71082, by rfl⟩ : syracuseStep 758213 = 142165) (by norm_num)
theorem B430589 : Blo 223812 430589 := bbase (se 3 (by rfl) ⟨80735, by rfl⟩ : syracuseStep 430589 = 161471) (by norm_num)
theorem B430733 : Blo 223812 430733 := bbase (se 3 (by rfl) ⟨80762, by rfl⟩ : syracuseStep 430733 = 161525) (by norm_num)
theorem B1151653 : Blo 223812 1151653 := bbase (se 4 (by rfl) ⟨107967, by rfl⟩ : syracuseStep 1151653 = 215935) (by norm_num)
theorem B856757 : Blo 223812 856757 := bbase (se 5 (by rfl) ⟨40160, by rfl⟩ : syracuseStep 856757 = 80321) (by norm_num)
theorem B758645 : Blo 223812 758645 := bbase (se 5 (by rfl) ⟨35561, by rfl⟩ : syracuseStep 758645 = 71123) (by norm_num)
theorem B431021 : Blo 223812 431021 := bbase (se 3 (by rfl) ⟨80816, by rfl⟩ : syracuseStep 431021 = 161633) (by norm_num)
theorem B922565 : Blo 223812 922565 := bbase (se 4 (by rfl) ⟨86490, by rfl⟩ : syracuseStep 922565 = 172981) (by norm_num)
theorem B431173 : Blo 223812 431173 := bbase (se 4 (by rfl) ⟨40422, by rfl⟩ : syracuseStep 431173 = 80845) (by norm_num)
theorem B759077 : Blo 223812 759077 := bbase (se 4 (by rfl) ⟨71163, by rfl⟩ : syracuseStep 759077 = 142327) (by norm_num)
theorem B431477 : Blo 223812 431477 := bbase (se 5 (by rfl) ⟨20225, by rfl⟩ : syracuseStep 431477 = 40451) (by norm_num)
theorem B1152629 : Blo 223812 1152629 := bbase (se 5 (by rfl) ⟨54029, by rfl⟩ : syracuseStep 1152629 = 108059) (by norm_num)
theorem B759509 : Blo 223812 759509 := bbase (se 7 (by rfl) ⟨8900, by rfl⟩ : syracuseStep 759509 = 17801) (by norm_num)
theorem B726965 : Blo 223812 726965 := bbase (se 5 (by rfl) ⟨34076, by rfl⟩ : syracuseStep 726965 = 68153) (by norm_num)
theorem B432229 : Blo 223812 432229 := bbase (se 4 (by rfl) ⟨40521, by rfl⟩ : syracuseStep 432229 = 81043) (by norm_num)
theorem B759941 : Blo 223812 759941 := bbase (se 4 (by rfl) ⟨71244, by rfl⟩ : syracuseStep 759941 = 142489) (by norm_num)
theorem B432373 : Blo 223812 432373 := bbase (se 5 (by rfl) ⟨20267, by rfl⟩ : syracuseStep 432373 = 40535) (by norm_num)
theorem B1939733 : Blo 223812 1939733 := bbase (se 6 (by rfl) ⟨45462, by rfl⟩ : syracuseStep 1939733 = 90925) (by norm_num)
theorem B760373 : Blo 223812 760373 := bbase (se 5 (by rfl) ⟨35642, by rfl⟩ : syracuseStep 760373 = 71285) (by norm_num)
theorem B1088101 : Blo 223812 1088101 := bbase (se 4 (by rfl) ⟨102009, by rfl⟩ : syracuseStep 1088101 = 204019) (by norm_num)
theorem B858869 : Blo 223812 858869 := bbase (se 5 (by rfl) ⟨40259, by rfl⟩ : syracuseStep 858869 = 80519) (by norm_num)
theorem B727861 : Blo 223812 727861 := bbase (se 5 (by rfl) ⟨34118, by rfl⟩ : syracuseStep 727861 = 68237) (by norm_num)
theorem B760805 : Blo 223812 760805 := bbase (se 4 (by rfl) ⟨71325, by rfl⟩ : syracuseStep 760805 = 142651) (by norm_num)
theorem B859157 : Blo 223812 859157 := bbase (se 6 (by rfl) ⟨20136, by rfl⟩ : syracuseStep 859157 = 40273) (by norm_num)
theorem B728261 : Blo 223812 728261 := bbase (se 4 (by rfl) ⟨68274, by rfl⟩ : syracuseStep 728261 = 136549) (by norm_num)
theorem B761237 : Blo 223812 761237 := bbase (se 6 (by rfl) ⟨17841, by rfl⟩ : syracuseStep 761237 = 35683) (by norm_num)
theorem B269777 : Blo 223812 269777 := bbase (se 2 (by rfl) ⟨101166, by rfl⟩ : syracuseStep 269777 = 202333) (by norm_num)
theorem B3317269 : Blo 223812 3317269 := bbase (se 6 (by rfl) ⟨77748, by rfl⟩ : syracuseStep 3317269 = 155497) (by norm_num)
theorem B1023637 : Blo 223812 1023637 := bbase (se 6 (by rfl) ⟨23991, by rfl⟩ : syracuseStep 1023637 = 47983) (by norm_num)
theorem B1220309 : Blo 223812 1220309 := bbase (se 7 (by rfl) ⟨14300, by rfl⟩ : syracuseStep 1220309 = 28601) (by norm_num)
theorem B270065 : Blo 223812 270065 := bbase (se 2 (by rfl) ⟨101274, by rfl⟩ : syracuseStep 270065 = 202549) (by norm_num)
theorem B761669 : Blo 223812 761669 := bbase (se 4 (by rfl) ⟨71406, by rfl⟩ : syracuseStep 761669 = 142813) (by norm_num)
theorem B335741 : Blo 223812 335741 := bbase (se 3 (by rfl) ⟨62951, by rfl⟩ : syracuseStep 335741 = 125903) (by norm_num)
theorem B335765 : Blo 223812 335765 := bbase (se 6 (by rfl) ⟨7869, by rfl⟩ : syracuseStep 335765 = 15739) (by norm_num)
theorem B270229 : Blo 223812 270229 := bbase (se 6 (by rfl) ⟨6333, by rfl⟩ : syracuseStep 270229 = 12667) (by norm_num)
theorem B368533 : Blo 223812 368533 := bbase (se 6 (by rfl) ⟨8637, by rfl⟩ : syracuseStep 368533 = 17275) (by norm_num)
theorem B335789 : Blo 223812 335789 := bbase (se 3 (by rfl) ⟨62960, by rfl⟩ : syracuseStep 335789 = 125921) (by norm_num)
theorem B270257 : Blo 223812 270257 := bbase (se 2 (by rfl) ⟨101346, by rfl⟩ : syracuseStep 270257 = 202693) (by norm_num)
theorem B335813 : Blo 223812 335813 := bbase (se 4 (by rfl) ⟨31482, by rfl⟩ : syracuseStep 335813 = 62965) (by norm_num)
theorem B335837 : Blo 223812 335837 := bbase (se 3 (by rfl) ⟨62969, by rfl⟩ : syracuseStep 335837 = 125939) (by norm_num)
theorem B335861 : Blo 223812 335861 := bbase (se 5 (by rfl) ⟨15743, by rfl⟩ : syracuseStep 335861 = 31487) (by norm_num)
theorem B335885 : Blo 223812 335885 := bbase (se 3 (by rfl) ⟨62978, by rfl⟩ : syracuseStep 335885 = 125957) (by norm_num)
theorem B335909 : Blo 223812 335909 := bbase (se 4 (by rfl) ⟨31491, by rfl⟩ : syracuseStep 335909 = 62983) (by norm_num)
theorem B270373 : Blo 223812 270373 := bbase (se 4 (by rfl) ⟨25347, by rfl⟩ : syracuseStep 270373 = 50695) (by norm_num)
theorem B335933 : Blo 223812 335933 := bbase (se 3 (by rfl) ⟨62987, by rfl⟩ : syracuseStep 335933 = 125975) (by norm_num)
theorem B335957 : Blo 223812 335957 := bbase (se 8 (by rfl) ⟨1968, by rfl⟩ : syracuseStep 335957 = 3937) (by norm_num)
theorem B335981 : Blo 223812 335981 := bbase (se 3 (by rfl) ⟨62996, by rfl⟩ : syracuseStep 335981 = 125993) (by norm_num)
theorem B336005 : Blo 223812 336005 := bbase (se 4 (by rfl) ⟨31500, by rfl⟩ : syracuseStep 336005 = 63001) (by norm_num)
theorem B270469 : Blo 223812 270469 := bbase (se 4 (by rfl) ⟨25356, by rfl⟩ : syracuseStep 270469 = 50713) (by norm_num)
theorem B336029 : Blo 223812 336029 := bbase (se 3 (by rfl) ⟨63005, by rfl⟩ : syracuseStep 336029 = 126011) (by norm_num)
theorem B336053 : Blo 223812 336053 := bbase (se 5 (by rfl) ⟨15752, by rfl⟩ : syracuseStep 336053 = 31505) (by norm_num)
theorem B860341 : Blo 223812 860341 := bbase (se 5 (by rfl) ⟨40328, by rfl⟩ : syracuseStep 860341 = 80657) (by norm_num)
theorem B336077 : Blo 223812 336077 := bbase (se 3 (by rfl) ⟨63014, by rfl⟩ : syracuseStep 336077 = 126029) (by norm_num)
theorem B336101 : Blo 223812 336101 := bbase (se 4 (by rfl) ⟨31509, by rfl⟩ : syracuseStep 336101 = 63019) (by norm_num)
theorem B762101 : Blo 223812 762101 := bbase (se 5 (by rfl) ⟨35723, by rfl⟩ : syracuseStep 762101 = 71447) (by norm_num)
theorem B336125 : Blo 223812 336125 := bbase (se 3 (by rfl) ⟨63023, by rfl⟩ : syracuseStep 336125 = 126047) (by norm_num)
theorem B336149 : Blo 223812 336149 := bbase (se 6 (by rfl) ⟨7878, by rfl⟩ : syracuseStep 336149 = 15757) (by norm_num)
theorem B336173 : Blo 223812 336173 := bbase (se 3 (by rfl) ⟨63032, by rfl⟩ : syracuseStep 336173 = 126065) (by norm_num)
theorem B336197 : Blo 223812 336197 := bbase (se 4 (by rfl) ⟨31518, by rfl⟩ : syracuseStep 336197 = 63037) (by norm_num)
theorem B336221 : Blo 223812 336221 := bbase (se 3 (by rfl) ⟨63041, by rfl⟩ : syracuseStep 336221 = 126083) (by norm_num)
theorem B336245 : Blo 223812 336245 := bbase (se 5 (by rfl) ⟨15761, by rfl⟩ : syracuseStep 336245 = 31523) (by norm_num)
theorem B336269 : Blo 223812 336269 := bbase (se 3 (by rfl) ⟨63050, by rfl⟩ : syracuseStep 336269 = 126101) (by norm_num)
theorem B1286549 : Blo 223812 1286549 := bbase (se 6 (by rfl) ⟨30153, by rfl⟩ : syracuseStep 1286549 = 60307) (by norm_num)
theorem B336293 : Blo 223812 336293 := bbase (se 4 (by rfl) ⟨31527, by rfl⟩ : syracuseStep 336293 = 63055) (by norm_num)
theorem B336317 : Blo 223812 336317 := bbase (se 3 (by rfl) ⟨63059, by rfl⟩ : syracuseStep 336317 = 126119) (by norm_num)
theorem B336341 : Blo 223812 336341 := bbase (se 7 (by rfl) ⟨3941, by rfl⟩ : syracuseStep 336341 = 7883) (by norm_num)
theorem B860645 : Blo 223812 860645 := bbase (se 4 (by rfl) ⟨80685, by rfl⟩ : syracuseStep 860645 = 161371) (by norm_num)
theorem B336365 : Blo 223812 336365 := bbase (se 3 (by rfl) ⟨63068, by rfl⟩ : syracuseStep 336365 = 126137) (by norm_num)
theorem B336389 : Blo 223812 336389 := bbase (se 4 (by rfl) ⟨31536, by rfl⟩ : syracuseStep 336389 = 63073) (by norm_num)
theorem B336413 : Blo 223812 336413 := bbase (se 3 (by rfl) ⟨63077, by rfl⟩ : syracuseStep 336413 = 126155) (by norm_num)
theorem B336437 : Blo 223812 336437 := bbase (se 5 (by rfl) ⟨15770, by rfl⟩ : syracuseStep 336437 = 31541) (by norm_num)
theorem B336461 : Blo 223812 336461 := bbase (se 3 (by rfl) ⟨63086, by rfl⟩ : syracuseStep 336461 = 126173) (by norm_num)
theorem B336485 : Blo 223812 336485 := bbase (se 4 (by rfl) ⟨31545, by rfl⟩ : syracuseStep 336485 = 63091) (by norm_num)
theorem B270949 : Blo 223812 270949 := bbase (se 4 (by rfl) ⟨25401, by rfl⟩ : syracuseStep 270949 = 50803) (by norm_num)
theorem B336509 : Blo 223812 336509 := bbase (se 3 (by rfl) ⟨63095, by rfl⟩ : syracuseStep 336509 = 126191) (by norm_num)
theorem B336533 : Blo 223812 336533 := bbase (se 6 (by rfl) ⟨7887, by rfl⟩ : syracuseStep 336533 = 15775) (by norm_num)
theorem B762533 : Blo 223812 762533 := bbase (se 4 (by rfl) ⟨71487, by rfl⟩ : syracuseStep 762533 = 142975) (by norm_num)
theorem B336557 : Blo 223812 336557 := bbase (se 3 (by rfl) ⟨63104, by rfl⟩ : syracuseStep 336557 = 126209) (by norm_num)
theorem B336581 : Blo 223812 336581 := bbase (se 4 (by rfl) ⟨31554, by rfl⟩ : syracuseStep 336581 = 63109) (by norm_num)
theorem B336605 : Blo 223812 336605 := bbase (se 3 (by rfl) ⟨63113, by rfl⟩ : syracuseStep 336605 = 126227) (by norm_num)
theorem B303845 : Blo 223812 303845 := bbase (se 4 (by rfl) ⟨28485, by rfl⟩ : syracuseStep 303845 = 56971) (by norm_num)
theorem B336629 : Blo 223812 336629 := bbase (se 5 (by rfl) ⟨15779, by rfl⟩ : syracuseStep 336629 = 31559) (by norm_num)
theorem B336653 : Blo 223812 336653 := bbase (se 3 (by rfl) ⟨63122, by rfl⟩ : syracuseStep 336653 = 126245) (by norm_num)
theorem B336677 : Blo 223812 336677 := bbase (se 4 (by rfl) ⟨31563, by rfl⟩ : syracuseStep 336677 = 63127) (by norm_num)
theorem B336701 : Blo 223812 336701 := bbase (se 3 (by rfl) ⟨63131, by rfl⟩ : syracuseStep 336701 = 126263) (by norm_num)
theorem B336725 : Blo 223812 336725 := bbase (se 9 (by rfl) ⟨986, by rfl⟩ : syracuseStep 336725 = 1973) (by norm_num)
theorem B336749 : Blo 223812 336749 := bbase (se 3 (by rfl) ⟨63140, by rfl⟩ : syracuseStep 336749 = 126281) (by norm_num)
theorem B336773 : Blo 223812 336773 := bbase (se 4 (by rfl) ⟨31572, by rfl⟩ : syracuseStep 336773 = 63145) (by norm_num)
theorem B336797 : Blo 223812 336797 := bbase (se 3 (by rfl) ⟨63149, by rfl⟩ : syracuseStep 336797 = 126299) (by norm_num)
theorem B336821 : Blo 223812 336821 := bbase (se 5 (by rfl) ⟨15788, by rfl⟩ : syracuseStep 336821 = 31577) (by norm_num)
theorem B336845 : Blo 223812 336845 := bbase (se 3 (by rfl) ⟨63158, by rfl⟩ : syracuseStep 336845 = 126317) (by norm_num)
theorem B336869 : Blo 223812 336869 := bbase (se 4 (by rfl) ⟨31581, by rfl⟩ : syracuseStep 336869 = 63163) (by norm_num)
theorem B336893 : Blo 223812 336893 := bbase (se 3 (by rfl) ⟨63167, by rfl⟩ : syracuseStep 336893 = 126335) (by norm_num)
theorem B336917 : Blo 223812 336917 := bbase (se 6 (by rfl) ⟨7896, by rfl⟩ : syracuseStep 336917 = 15793) (by norm_num)
theorem B336941 : Blo 223812 336941 := bbase (se 3 (by rfl) ⟨63176, by rfl⟩ : syracuseStep 336941 = 126353) (by norm_num)
theorem B336965 : Blo 223812 336965 := bbase (se 4 (by rfl) ⟨31590, by rfl⟩ : syracuseStep 336965 = 63181) (by norm_num)
theorem B762965 : Blo 223812 762965 := bbase (se 8 (by rfl) ⟨4470, by rfl⟩ : syracuseStep 762965 = 8941) (by norm_num)
theorem B336989 : Blo 223812 336989 := bbase (se 3 (by rfl) ⟨63185, by rfl⟩ : syracuseStep 336989 = 126371) (by norm_num)
theorem B337013 : Blo 223812 337013 := bbase (se 5 (by rfl) ⟨15797, by rfl⟩ : syracuseStep 337013 = 31595) (by norm_num)
theorem B337037 : Blo 223812 337037 := bbase (se 3 (by rfl) ⟨63194, by rfl⟩ : syracuseStep 337037 = 126389) (by norm_num)
theorem B337061 : Blo 223812 337061 := bbase (se 4 (by rfl) ⟨31599, by rfl⟩ : syracuseStep 337061 = 63199) (by norm_num)
theorem B337085 : Blo 223812 337085 := bbase (se 3 (by rfl) ⟨63203, by rfl⟩ : syracuseStep 337085 = 126407) (by norm_num)
theorem B337109 : Blo 223812 337109 := bbase (se 7 (by rfl) ⟨3950, by rfl⟩ : syracuseStep 337109 = 7901) (by norm_num)
theorem B337133 : Blo 223812 337133 := bbase (se 3 (by rfl) ⟨63212, by rfl⟩ : syracuseStep 337133 = 126425) (by norm_num)
theorem B337157 : Blo 223812 337157 := bbase (se 4 (by rfl) ⟨31608, by rfl⟩ : syracuseStep 337157 = 63217) (by norm_num)
theorem B337181 : Blo 223812 337181 := bbase (se 3 (by rfl) ⟨63221, by rfl⟩ : syracuseStep 337181 = 126443) (by norm_num)
theorem B337205 : Blo 223812 337205 := bbase (se 5 (by rfl) ⟨15806, by rfl⟩ : syracuseStep 337205 = 31613) (by norm_num)
theorem B337229 : Blo 223812 337229 := bbase (se 3 (by rfl) ⟨63230, by rfl⟩ : syracuseStep 337229 = 126461) (by norm_num)
theorem B337253 : Blo 223812 337253 := bbase (se 4 (by rfl) ⟨31617, by rfl⟩ : syracuseStep 337253 = 63235) (by norm_num)
theorem B337277 : Blo 223812 337277 := bbase (se 3 (by rfl) ⟨63239, by rfl⟩ : syracuseStep 337277 = 126479) (by norm_num)
theorem B337301 : Blo 223812 337301 := bbase (se 6 (by rfl) ⟨7905, by rfl⟩ : syracuseStep 337301 = 15811) (by norm_num)
theorem B337325 : Blo 223812 337325 := bbase (se 3 (by rfl) ⟨63248, by rfl⟩ : syracuseStep 337325 = 126497) (by norm_num)
theorem B239041 : Blo 223812 239041 := bbase (se 2 (by rfl) ⟨89640, by rfl⟩ : syracuseStep 239041 = 179281) (by norm_num)
theorem B337349 : Blo 223812 337349 := bbase (se 4 (by rfl) ⟨31626, by rfl⟩ : syracuseStep 337349 = 63253) (by norm_num)
theorem B959957 : Blo 223812 959957 := bbase (se 7 (by rfl) ⟨11249, by rfl⟩ : syracuseStep 959957 = 22499) (by norm_num)
theorem B304597 : Blo 223812 304597 := bbase (se 7 (by rfl) ⟨3569, by rfl⟩ : syracuseStep 304597 = 7139) (by norm_num)
theorem B337373 : Blo 223812 337373 := bbase (se 3 (by rfl) ⟨63257, by rfl⟩ : syracuseStep 337373 = 126515) (by norm_num)
theorem B337397 : Blo 223812 337397 := bbase (se 5 (by rfl) ⟨15815, by rfl⟩ : syracuseStep 337397 = 31631) (by norm_num)
theorem B763397 : Blo 223812 763397 := bbase (se 4 (by rfl) ⟨71568, by rfl⟩ : syracuseStep 763397 = 143137) (by norm_num)
theorem B566797 : Blo 223812 566797 := bbase (se 3 (by rfl) ⟨106274, by rfl⟩ : syracuseStep 566797 = 212549) (by norm_num)
theorem B337421 : Blo 223812 337421 := bbase (se 3 (by rfl) ⟨63266, by rfl⟩ : syracuseStep 337421 = 126533) (by norm_num)
theorem B337445 : Blo 223812 337445 := bbase (se 4 (by rfl) ⟨31635, by rfl⟩ : syracuseStep 337445 = 63271) (by norm_num)
theorem B337469 : Blo 223812 337469 := bbase (se 3 (by rfl) ⟨63275, by rfl⟩ : syracuseStep 337469 = 126551) (by norm_num)
theorem B337493 : Blo 223812 337493 := bbase (se 8 (by rfl) ⟨1977, by rfl⟩ : syracuseStep 337493 = 3955) (by norm_num)
theorem B337517 : Blo 223812 337517 := bbase (se 3 (by rfl) ⟨63284, by rfl⟩ : syracuseStep 337517 = 126569) (by norm_num)
theorem B566909 : Blo 223812 566909 := bbase (se 3 (by rfl) ⟨106295, by rfl⟩ : syracuseStep 566909 = 212591) (by norm_num)
theorem B337541 : Blo 223812 337541 := bbase (se 4 (by rfl) ⟨31644, by rfl⟩ : syracuseStep 337541 = 63289) (by norm_num)
theorem B337565 : Blo 223812 337565 := bbase (se 3 (by rfl) ⟨63293, by rfl⟩ : syracuseStep 337565 = 126587) (by norm_num)
theorem B337589 : Blo 223812 337589 := bbase (se 5 (by rfl) ⟨15824, by rfl⟩ : syracuseStep 337589 = 31649) (by norm_num)
theorem B337613 : Blo 223812 337613 := bbase (se 3 (by rfl) ⟨63302, by rfl⟩ : syracuseStep 337613 = 126605) (by norm_num)
theorem B337637 : Blo 223812 337637 := bbase (se 4 (by rfl) ⟨31653, by rfl⟩ : syracuseStep 337637 = 63307) (by norm_num)
theorem B337661 : Blo 223812 337661 := bbase (se 3 (by rfl) ⟨63311, by rfl⟩ : syracuseStep 337661 = 126623) (by norm_num)
theorem B337685 : Blo 223812 337685 := bbase (se 6 (by rfl) ⟨7914, by rfl⟩ : syracuseStep 337685 = 15829) (by norm_num)
theorem B337709 : Blo 223812 337709 := bbase (se 3 (by rfl) ⟨63320, by rfl⟩ : syracuseStep 337709 = 126641) (by norm_num)
theorem B567101 : Blo 223812 567101 := bbase (se 3 (by rfl) ⟨106331, by rfl⟩ : syracuseStep 567101 = 212663) (by norm_num)
theorem B337733 : Blo 223812 337733 := bbase (se 4 (by rfl) ⟨31662, by rfl⟩ : syracuseStep 337733 = 63325) (by norm_num)
theorem B337757 : Blo 223812 337757 := bbase (se 3 (by rfl) ⟨63329, by rfl⟩ : syracuseStep 337757 = 126659) (by norm_num)
theorem B239473 : Blo 223812 239473 := bbase (se 2 (by rfl) ⟨89802, by rfl⟩ : syracuseStep 239473 = 179605) (by norm_num)
theorem B337781 : Blo 223812 337781 := bbase (se 5 (by rfl) ⟨15833, by rfl⟩ : syracuseStep 337781 = 31667) (by norm_num)
theorem B337805 : Blo 223812 337805 := bbase (se 3 (by rfl) ⟨63338, by rfl⟩ : syracuseStep 337805 = 126677) (by norm_num)
theorem B337829 : Blo 223812 337829 := bbase (se 4 (by rfl) ⟨31671, by rfl⟩ : syracuseStep 337829 = 63343) (by norm_num)
theorem B763829 : Blo 223812 763829 := bbase (se 5 (by rfl) ⟨35804, by rfl⟩ : syracuseStep 763829 = 71609) (by norm_num)
theorem B239545 : Blo 223812 239545 := bbase (se 2 (by rfl) ⟨89829, by rfl⟩ : syracuseStep 239545 = 179659) (by norm_num)
theorem B337853 : Blo 223812 337853 := bbase (se 3 (by rfl) ⟨63347, by rfl⟩ : syracuseStep 337853 = 126695) (by norm_num)
theorem B403397 : Blo 223812 403397 := bbase (se 4 (by rfl) ⟨37818, by rfl⟩ : syracuseStep 403397 = 75637) (by norm_num)
theorem B272333 : Blo 223812 272333 := bbase (se 3 (by rfl) ⟨51062, by rfl⟩ : syracuseStep 272333 = 102125) (by norm_num)
theorem B337877 : Blo 223812 337877 := bbase (se 7 (by rfl) ⟨3959, by rfl⟩ : syracuseStep 337877 = 7919) (by norm_num)
theorem B337901 : Blo 223812 337901 := bbase (se 3 (by rfl) ⟨63356, by rfl⟩ : syracuseStep 337901 = 126713) (by norm_num)
theorem B337925 : Blo 223812 337925 := bbase (se 4 (by rfl) ⟨31680, by rfl⟩ : syracuseStep 337925 = 63361) (by norm_num)
theorem B337949 : Blo 223812 337949 := bbase (se 3 (by rfl) ⟨63365, by rfl⟩ : syracuseStep 337949 = 126731) (by norm_num)
theorem B337973 : Blo 223812 337973 := bbase (se 5 (by rfl) ⟨15842, by rfl⟩ : syracuseStep 337973 = 31685) (by norm_num)
theorem B337997 : Blo 223812 337997 := bbase (se 3 (by rfl) ⟨63374, by rfl⟩ : syracuseStep 337997 = 126749) (by norm_num)
theorem B338021 : Blo 223812 338021 := bbase (se 4 (by rfl) ⟨31689, by rfl⟩ : syracuseStep 338021 = 63379) (by norm_num)
theorem B338045 : Blo 223812 338045 := bbase (se 3 (by rfl) ⟨63383, by rfl⟩ : syracuseStep 338045 = 126767) (by norm_num)
theorem B1091717 : Blo 223812 1091717 := bbase (se 4 (by rfl) ⟨102348, by rfl⟩ : syracuseStep 1091717 = 204697) (by norm_num)
theorem B272521 : Blo 223812 272521 := bbase (se 2 (by rfl) ⟨102195, by rfl⟩ : syracuseStep 272521 = 204391) (by norm_num)
theorem B567445 : Blo 223812 567445 := bbase (se 6 (by rfl) ⟨13299, by rfl⟩ : syracuseStep 567445 = 26599) (by norm_num)
theorem B338069 : Blo 223812 338069 := bbase (se 6 (by rfl) ⟨7923, by rfl⟩ : syracuseStep 338069 = 15847) (by norm_num)
theorem B338093 : Blo 223812 338093 := bbase (se 3 (by rfl) ⟨63392, by rfl⟩ : syracuseStep 338093 = 126785) (by norm_num)
theorem B338117 : Blo 223812 338117 := bbase (se 4 (by rfl) ⟨31698, by rfl⟩ : syracuseStep 338117 = 63397) (by norm_num)
theorem B338141 : Blo 223812 338141 := bbase (se 3 (by rfl) ⟨63401, by rfl⟩ : syracuseStep 338141 = 126803) (by norm_num)
theorem B338165 : Blo 223812 338165 := bbase (se 5 (by rfl) ⟨15851, by rfl⟩ : syracuseStep 338165 = 31703) (by norm_num)
theorem B567557 : Blo 223812 567557 := bbase (se 4 (by rfl) ⟨53208, by rfl⟩ : syracuseStep 567557 = 106417) (by norm_num)
theorem B338189 : Blo 223812 338189 := bbase (se 3 (by rfl) ⟨63410, by rfl⟩ : syracuseStep 338189 = 126821) (by norm_num)
theorem B338213 : Blo 223812 338213 := bbase (se 4 (by rfl) ⟨31707, by rfl⟩ : syracuseStep 338213 = 63415) (by norm_num)
theorem B239917 : Blo 223812 239917 := bbase (se 3 (by rfl) ⟨44984, by rfl⟩ : syracuseStep 239917 = 89969) (by norm_num)
theorem B338237 : Blo 223812 338237 := bbase (se 3 (by rfl) ⟨63419, by rfl⟩ : syracuseStep 338237 = 126839) (by norm_num)
theorem B338261 : Blo 223812 338261 := bbase (se 10 (by rfl) ⟨495, by rfl⟩ : syracuseStep 338261 = 991) (by norm_num)
theorem B272737 : Blo 223812 272737 := bbase (se 2 (by rfl) ⟨102276, by rfl⟩ : syracuseStep 272737 = 204553) (by norm_num)
theorem B764261 : Blo 223812 764261 := bbase (se 4 (by rfl) ⟨71649, by rfl⟩ : syracuseStep 764261 = 143299) (by norm_num)
theorem B338285 : Blo 223812 338285 := bbase (se 3 (by rfl) ⟨63428, by rfl⟩ : syracuseStep 338285 = 126857) (by norm_num)
theorem B338309 : Blo 223812 338309 := bbase (se 4 (by rfl) ⟨31716, by rfl⟩ : syracuseStep 338309 = 63433) (by norm_num)
theorem B338333 : Blo 223812 338333 := bbase (se 3 (by rfl) ⟨63437, by rfl⟩ : syracuseStep 338333 = 126875) (by norm_num)
theorem B338357 : Blo 223812 338357 := bbase (se 5 (by rfl) ⟨15860, by rfl⟩ : syracuseStep 338357 = 31721) (by norm_num)
theorem B567749 : Blo 223812 567749 := bbase (se 4 (by rfl) ⟨53226, by rfl⟩ : syracuseStep 567749 = 106453) (by norm_num)
theorem B338381 : Blo 223812 338381 := bbase (se 3 (by rfl) ⟨63446, by rfl⟩ : syracuseStep 338381 = 126893) (by norm_num)
theorem B338405 : Blo 223812 338405 := bbase (se 4 (by rfl) ⟨31725, by rfl⟩ : syracuseStep 338405 = 63451) (by norm_num)
theorem B338429 : Blo 223812 338429 := bbase (se 3 (by rfl) ⟨63455, by rfl⟩ : syracuseStep 338429 = 126911) (by norm_num)
theorem B338453 : Blo 223812 338453 := bbase (se 6 (by rfl) ⟨7932, by rfl⟩ : syracuseStep 338453 = 15865) (by norm_num)
theorem B862757 : Blo 223812 862757 := bbase (se 4 (by rfl) ⟨80883, by rfl⟩ : syracuseStep 862757 = 161767) (by norm_num)
theorem B338477 : Blo 223812 338477 := bbase (se 3 (by rfl) ⟨63464, by rfl⟩ : syracuseStep 338477 = 126929) (by norm_num)
theorem B338501 : Blo 223812 338501 := bbase (se 4 (by rfl) ⟨31734, by rfl⟩ : syracuseStep 338501 = 63469) (by norm_num)
theorem B338525 : Blo 223812 338525 := bbase (se 3 (by rfl) ⟨63473, by rfl⟩ : syracuseStep 338525 = 126947) (by norm_num)
theorem B338549 : Blo 223812 338549 := bbase (se 5 (by rfl) ⟨15869, by rfl⟩ : syracuseStep 338549 = 31739) (by norm_num)
theorem B273025 : Blo 223812 273025 := bbase (se 2 (by rfl) ⟨102384, by rfl⟩ : syracuseStep 273025 = 204769) (by norm_num)
theorem B338573 : Blo 223812 338573 := bbase (se 3 (by rfl) ⟨63482, by rfl⟩ : syracuseStep 338573 = 126965) (by norm_num)
theorem B305813 : Blo 223812 305813 := bbase (se 6 (by rfl) ⟨7167, by rfl⟩ : syracuseStep 305813 = 14335) (by norm_num)
theorem B240293 : Blo 223812 240293 := bbase (se 4 (by rfl) ⟨22527, by rfl⟩ : syracuseStep 240293 = 45055) (by norm_num)
theorem B338597 : Blo 223812 338597 := bbase (se 4 (by rfl) ⟨31743, by rfl⟩ : syracuseStep 338597 = 63487) (by norm_num)
theorem B338621 : Blo 223812 338621 := bbase (se 3 (by rfl) ⟨63491, by rfl⟩ : syracuseStep 338621 = 126983) (by norm_num)
theorem B2730709 : Blo 223812 2730709 := bbase (se 7 (by rfl) ⟨32000, by rfl⟩ : syracuseStep 2730709 = 64001) (by norm_num)
theorem B338645 : Blo 223812 338645 := bbase (se 7 (by rfl) ⟨3968, by rfl⟩ : syracuseStep 338645 = 7937) (by norm_num)
theorem B240365 : Blo 223812 240365 := bbase (se 3 (by rfl) ⟨45068, by rfl⟩ : syracuseStep 240365 = 90137) (by norm_num)
theorem B338669 : Blo 223812 338669 := bbase (se 3 (by rfl) ⟨63500, by rfl⟩ : syracuseStep 338669 = 127001) (by norm_num)
theorem B338693 : Blo 223812 338693 := bbase (se 4 (by rfl) ⟨31752, by rfl⟩ : syracuseStep 338693 = 63505) (by norm_num)
theorem B764693 : Blo 223812 764693 := bbase (se 6 (by rfl) ⟨17922, by rfl⟩ : syracuseStep 764693 = 35845) (by norm_num)
theorem B568093 : Blo 223812 568093 := bbase (se 3 (by rfl) ⟨106517, by rfl⟩ : syracuseStep 568093 = 213035) (by norm_num)
theorem B338717 : Blo 223812 338717 := bbase (se 3 (by rfl) ⟨63509, by rfl⟩ : syracuseStep 338717 = 127019) (by norm_num)
theorem B338741 : Blo 223812 338741 := bbase (se 5 (by rfl) ⟨15878, by rfl⟩ : syracuseStep 338741 = 31757) (by norm_num)
theorem B863045 : Blo 223812 863045 := bbase (se 4 (by rfl) ⟨80910, by rfl⟩ : syracuseStep 863045 = 161821) (by norm_num)
theorem B338765 : Blo 223812 338765 := bbase (se 3 (by rfl) ⟨63518, by rfl⟩ : syracuseStep 338765 = 127037) (by norm_num)
theorem B338789 : Blo 223812 338789 := bbase (se 4 (by rfl) ⟨31761, by rfl⟩ : syracuseStep 338789 = 63523) (by norm_num)
theorem B338813 : Blo 223812 338813 := bbase (se 3 (by rfl) ⟨63527, by rfl⟩ : syracuseStep 338813 = 127055) (by norm_num)
theorem B568205 : Blo 223812 568205 := bbase (se 3 (by rfl) ⟨106538, by rfl⟩ : syracuseStep 568205 = 213077) (by norm_num)
theorem B1715093 : Blo 223812 1715093 := bbase (se 6 (by rfl) ⟨40197, by rfl⟩ : syracuseStep 1715093 = 80395) (by norm_num)
theorem B338837 : Blo 223812 338837 := bbase (se 6 (by rfl) ⟨7941, by rfl⟩ : syracuseStep 338837 = 15883) (by norm_num)
theorem B240553 : Blo 223812 240553 := bbase (se 2 (by rfl) ⟨90207, by rfl⟩ : syracuseStep 240553 = 180415) (by norm_num)
theorem B338861 : Blo 223812 338861 := bbase (se 3 (by rfl) ⟨63536, by rfl⟩ : syracuseStep 338861 = 127073) (by norm_num)
theorem B338885 : Blo 223812 338885 := bbase (se 4 (by rfl) ⟨31770, by rfl⟩ : syracuseStep 338885 = 63541) (by norm_num)
theorem B338909 : Blo 223812 338909 := bbase (se 3 (by rfl) ⟨63545, by rfl⟩ : syracuseStep 338909 = 127091) (by norm_num)
theorem B338933 : Blo 223812 338933 := bbase (se 5 (by rfl) ⟨15887, by rfl⟩ : syracuseStep 338933 = 31775) (by norm_num)
theorem B338957 : Blo 223812 338957 := bbase (se 3 (by rfl) ⟨63554, by rfl⟩ : syracuseStep 338957 = 127109) (by norm_num)
theorem B338981 : Blo 223812 338981 := bbase (se 4 (by rfl) ⟨31779, by rfl⟩ : syracuseStep 338981 = 63559) (by norm_num)
theorem B339005 : Blo 223812 339005 := bbase (se 3 (by rfl) ⟨63563, by rfl⟩ : syracuseStep 339005 = 127127) (by norm_num)
theorem B568397 : Blo 223812 568397 := bbase (se 3 (by rfl) ⟨106574, by rfl⟩ : syracuseStep 568397 = 213149) (by norm_num)
theorem B339029 : Blo 223812 339029 := bbase (se 8 (by rfl) ⟨1986, by rfl⟩ : syracuseStep 339029 = 3973) (by norm_num)
theorem B240737 : Blo 223812 240737 := bbase (se 2 (by rfl) ⟨90276, by rfl⟩ : syracuseStep 240737 = 180553) (by norm_num)
theorem B339053 : Blo 223812 339053 := bbase (se 3 (by rfl) ⟨63572, by rfl⟩ : syracuseStep 339053 = 127145) (by norm_num)
theorem B339077 : Blo 223812 339077 := bbase (se 4 (by rfl) ⟨31788, by rfl⟩ : syracuseStep 339077 = 63577) (by norm_num)
theorem B339101 : Blo 223812 339101 := bbase (se 3 (by rfl) ⟨63581, by rfl⟩ : syracuseStep 339101 = 127163) (by norm_num)
theorem B339125 : Blo 223812 339125 := bbase (se 5 (by rfl) ⟨15896, by rfl⟩ : syracuseStep 339125 = 31793) (by norm_num)
theorem B961733 : Blo 223812 961733 := bbase (se 4 (by rfl) ⟨90162, by rfl⟩ : syracuseStep 961733 = 180325) (by norm_num)
theorem B765125 : Blo 223812 765125 := bbase (se 4 (by rfl) ⟨71730, by rfl⟩ : syracuseStep 765125 = 143461) (by norm_num)
theorem B339149 : Blo 223812 339149 := bbase (se 3 (by rfl) ⟨63590, by rfl⟩ : syracuseStep 339149 = 127181) (by norm_num)
theorem B339173 : Blo 223812 339173 := bbase (se 4 (by rfl) ⟨31797, by rfl⟩ : syracuseStep 339173 = 63595) (by norm_num)
theorem B339197 : Blo 223812 339197 := bbase (se 3 (by rfl) ⟨63599, by rfl⟩ : syracuseStep 339197 = 127199) (by norm_num)
theorem B339221 : Blo 223812 339221 := bbase (se 6 (by rfl) ⟨7950, by rfl⟩ : syracuseStep 339221 = 15901) (by norm_num)
theorem B339245 : Blo 223812 339245 := bbase (se 3 (by rfl) ⟨63608, by rfl⟩ : syracuseStep 339245 = 127217) (by norm_num)
theorem B339269 : Blo 223812 339269 := bbase (se 4 (by rfl) ⟨31806, by rfl⟩ : syracuseStep 339269 = 63613) (by norm_num)
theorem B339293 : Blo 223812 339293 := bbase (se 3 (by rfl) ⟨63617, by rfl⟩ : syracuseStep 339293 = 127235) (by norm_num)
theorem B339317 : Blo 223812 339317 := bbase (se 5 (by rfl) ⟨15905, by rfl⟩ : syracuseStep 339317 = 31811) (by norm_num)
theorem B339341 : Blo 223812 339341 := bbase (se 3 (by rfl) ⟨63626, by rfl⟩ : syracuseStep 339341 = 127253) (by norm_num)
theorem B2174357 : Blo 223812 2174357 := bbase (se 6 (by rfl) ⟨50961, by rfl⟩ : syracuseStep 2174357 = 101923) (by norm_num)
theorem B568741 : Blo 223812 568741 := bbase (se 4 (by rfl) ⟨53319, by rfl⟩ : syracuseStep 568741 = 106639) (by norm_num)
theorem B339365 : Blo 223812 339365 := bbase (se 4 (by rfl) ⟨31815, by rfl⟩ : syracuseStep 339365 = 63631) (by norm_num)
theorem B306613 : Blo 223812 306613 := bbase (se 5 (by rfl) ⟨14372, by rfl⟩ : syracuseStep 306613 = 28745) (by norm_num)
theorem B339389 : Blo 223812 339389 := bbase (se 3 (by rfl) ⟨63635, by rfl⟩ : syracuseStep 339389 = 127271) (by norm_num)
theorem B339413 : Blo 223812 339413 := bbase (se 7 (by rfl) ⟨3977, by rfl⟩ : syracuseStep 339413 = 7955) (by norm_num)
theorem B339437 : Blo 223812 339437 := bbase (se 3 (by rfl) ⟨63644, by rfl⟩ : syracuseStep 339437 = 127289) (by norm_num)
theorem B339461 : Blo 223812 339461 := bbase (se 4 (by rfl) ⟨31824, by rfl⟩ : syracuseStep 339461 = 63649) (by norm_num)
theorem B568853 : Blo 223812 568853 := bbase (se 6 (by rfl) ⟨13332, by rfl⟩ : syracuseStep 568853 = 26665) (by norm_num)
theorem B339485 : Blo 223812 339485 := bbase (se 3 (by rfl) ⟨63653, by rfl⟩ : syracuseStep 339485 = 127307) (by norm_num)
theorem B339509 : Blo 223812 339509 := bbase (se 5 (by rfl) ⟨15914, by rfl⟩ : syracuseStep 339509 = 31829) (by norm_num)
theorem B339533 : Blo 223812 339533 := bbase (se 3 (by rfl) ⟨63662, by rfl⟩ : syracuseStep 339533 = 127325) (by norm_num)
theorem B339557 : Blo 223812 339557 := bbase (se 4 (by rfl) ⟨31833, by rfl⟩ : syracuseStep 339557 = 63667) (by norm_num)
theorem B765557 : Blo 223812 765557 := bbase (se 5 (by rfl) ⟨35885, by rfl⟩ : syracuseStep 765557 = 71771) (by norm_num)
theorem B339581 : Blo 223812 339581 := bbase (se 3 (by rfl) ⟨63671, by rfl⟩ : syracuseStep 339581 = 127343) (by norm_num)
theorem B339605 : Blo 223812 339605 := bbase (se 6 (by rfl) ⟨7959, by rfl⟩ : syracuseStep 339605 = 15919) (by norm_num)
theorem B339629 : Blo 223812 339629 := bbase (se 3 (by rfl) ⟨63680, by rfl⟩ : syracuseStep 339629 = 127361) (by norm_num)
theorem B339653 : Blo 223812 339653 := bbase (se 4 (by rfl) ⟨31842, by rfl⟩ : syracuseStep 339653 = 63685) (by norm_num)
theorem B569045 : Blo 223812 569045 := bbase (se 7 (by rfl) ⟨6668, by rfl⟩ : syracuseStep 569045 = 13337) (by norm_num)
theorem B339677 : Blo 223812 339677 := bbase (se 3 (by rfl) ⟨63689, by rfl⟩ : syracuseStep 339677 = 127379) (by norm_num)
theorem B339701 : Blo 223812 339701 := bbase (se 5 (by rfl) ⟨15923, by rfl⟩ : syracuseStep 339701 = 31847) (by norm_num)
theorem B438005 : Blo 223812 438005 := bbase (se 5 (by rfl) ⟨20531, by rfl⟩ : syracuseStep 438005 = 41063) (by norm_num)
theorem B339725 : Blo 223812 339725 := bbase (se 3 (by rfl) ⟨63698, by rfl⟩ : syracuseStep 339725 = 127397) (by norm_num)
theorem B339749 : Blo 223812 339749 := bbase (se 4 (by rfl) ⟨31851, by rfl⟩ : syracuseStep 339749 = 63703) (by norm_num)
theorem B438061 : Blo 223812 438061 := bbase (se 3 (by rfl) ⟨82136, by rfl⟩ : syracuseStep 438061 = 164273) (by norm_num)
theorem B339773 : Blo 223812 339773 := bbase (se 3 (by rfl) ⟨63707, by rfl⟩ : syracuseStep 339773 = 127415) (by norm_num)
theorem B503621 : Blo 223812 503621 := bbase (se 4 (by rfl) ⟨47214, by rfl⟩ : syracuseStep 503621 = 94429) (by norm_num)
theorem B241489 : Blo 223812 241489 := bbase (se 2 (by rfl) ⟨90558, by rfl⟩ : syracuseStep 241489 = 181117) (by norm_num)
theorem B339797 : Blo 223812 339797 := bbase (se 9 (by rfl) ⟨995, by rfl⟩ : syracuseStep 339797 = 1991) (by norm_num)
theorem B339821 : Blo 223812 339821 := bbase (se 3 (by rfl) ⟨63716, by rfl⟩ : syracuseStep 339821 = 127433) (by norm_num)
theorem B339845 : Blo 223812 339845 := bbase (se 4 (by rfl) ⟨31860, by rfl⟩ : syracuseStep 339845 = 63721) (by norm_num)
theorem B503693 : Blo 223812 503693 := bbase (se 3 (by rfl) ⟨94442, by rfl⟩ : syracuseStep 503693 = 188885) (by norm_num)
theorem B241561 : Blo 223812 241561 := bbase (se 2 (by rfl) ⟨90585, by rfl⟩ : syracuseStep 241561 = 181171) (by norm_num)
theorem B339869 : Blo 223812 339869 := bbase (se 3 (by rfl) ⟨63725, by rfl⟩ : syracuseStep 339869 = 127451) (by norm_num)
theorem B339893 : Blo 223812 339893 := bbase (se 5 (by rfl) ⟨15932, by rfl⟩ : syracuseStep 339893 = 31865) (by norm_num)
theorem B339917 : Blo 223812 339917 := bbase (se 3 (by rfl) ⟨63734, by rfl⟩ : syracuseStep 339917 = 127469) (by norm_num)
theorem B503765 : Blo 223812 503765 := bbase (se 7 (by rfl) ⟨5903, by rfl⟩ : syracuseStep 503765 = 11807) (by norm_num)
theorem B339941 : Blo 223812 339941 := bbase (se 4 (by rfl) ⟨31869, by rfl⟩ : syracuseStep 339941 = 63739) (by norm_num)
theorem B864229 : Blo 223812 864229 := bbase (se 4 (by rfl) ⟨81021, by rfl⟩ : syracuseStep 864229 = 162043) (by norm_num)
theorem B1093621 : Blo 223812 1093621 := bbase (se 5 (by rfl) ⟨51263, by rfl⟩ : syracuseStep 1093621 = 102527) (by norm_num)
theorem B339965 : Blo 223812 339965 := bbase (se 3 (by rfl) ⟨63743, by rfl⟩ : syracuseStep 339965 = 127487) (by norm_num)
theorem B1093637 : Blo 223812 1093637 := bbase (se 4 (by rfl) ⟨102528, by rfl⟩ : syracuseStep 1093637 = 205057) (by norm_num)
theorem B339989 : Blo 223812 339989 := bbase (se 6 (by rfl) ⟨7968, by rfl⟩ : syracuseStep 339989 = 15937) (by norm_num)
theorem B503837 : Blo 223812 503837 := bbase (se 3 (by rfl) ⟨94469, by rfl⟩ : syracuseStep 503837 = 188939) (by norm_num)
theorem B765989 : Blo 223812 765989 := bbase (se 4 (by rfl) ⟨71811, by rfl⟩ : syracuseStep 765989 = 143623) (by norm_num)
theorem B569389 : Blo 223812 569389 := bbase (se 3 (by rfl) ⟨106760, by rfl⟩ : syracuseStep 569389 = 213521) (by norm_num)
theorem B340013 : Blo 223812 340013 := bbase (se 3 (by rfl) ⟨63752, by rfl⟩ : syracuseStep 340013 = 127505) (by norm_num)
theorem B340037 : Blo 223812 340037 := bbase (se 4 (by rfl) ⟨31878, by rfl⟩ : syracuseStep 340037 = 63757) (by norm_num)
theorem B241741 : Blo 223812 241741 := bbase (se 3 (by rfl) ⟨45326, by rfl⟩ : syracuseStep 241741 = 90653) (by norm_num)
theorem B340061 : Blo 223812 340061 := bbase (se 3 (by rfl) ⟨63761, by rfl⟩ : syracuseStep 340061 = 127523) (by norm_num)
theorem B503909 : Blo 223812 503909 := bbase (se 4 (by rfl) ⟨47241, by rfl⟩ : syracuseStep 503909 = 94483) (by norm_num)
theorem B340085 : Blo 223812 340085 := bbase (se 5 (by rfl) ⟨15941, by rfl⟩ : syracuseStep 340085 = 31883) (by norm_num)
theorem B340109 : Blo 223812 340109 := bbase (se 3 (by rfl) ⟨63770, by rfl⟩ : syracuseStep 340109 = 127541) (by norm_num)
theorem B569501 : Blo 223812 569501 := bbase (se 3 (by rfl) ⟨106781, by rfl⟩ : syracuseStep 569501 = 213563) (by norm_num)
theorem B962725 : Blo 223812 962725 := bbase (se 4 (by rfl) ⟨90255, by rfl⟩ : syracuseStep 962725 = 180511) (by norm_num)
theorem B340133 : Blo 223812 340133 := bbase (se 4 (by rfl) ⟨31887, by rfl⟩ : syracuseStep 340133 = 63775) (by norm_num)
theorem B503981 : Blo 223812 503981 := bbase (se 3 (by rfl) ⟨94496, by rfl⟩ : syracuseStep 503981 = 188993) (by norm_num)
theorem B307381 : Blo 223812 307381 := bbase (se 5 (by rfl) ⟨14408, by rfl⟩ : syracuseStep 307381 = 28817) (by norm_num)
theorem B340157 : Blo 223812 340157 := bbase (se 3 (by rfl) ⟨63779, by rfl⟩ : syracuseStep 340157 = 127559) (by norm_num)
theorem B340181 : Blo 223812 340181 := bbase (se 7 (by rfl) ⟨3986, by rfl⟩ : syracuseStep 340181 = 7973) (by norm_num)
theorem B340205 : Blo 223812 340205 := bbase (se 3 (by rfl) ⟨63788, by rfl⟩ : syracuseStep 340205 = 127577) (by norm_num)
theorem B504053 : Blo 223812 504053 := bbase (se 5 (by rfl) ⟨23627, by rfl⟩ : syracuseStep 504053 = 47255) (by norm_num)
theorem B340229 : Blo 223812 340229 := bbase (se 4 (by rfl) ⟨31896, by rfl⟩ : syracuseStep 340229 = 63793) (by norm_num)
theorem B864533 : Blo 223812 864533 := bbase (se 6 (by rfl) ⟨20262, by rfl⟩ : syracuseStep 864533 = 40525) (by norm_num)
theorem B340253 : Blo 223812 340253 := bbase (se 3 (by rfl) ⟨63797, by rfl⟩ : syracuseStep 340253 = 127595) (by norm_num)
theorem B405805 : Blo 223812 405805 := bbase (se 3 (by rfl) ⟨76088, by rfl⟩ : syracuseStep 405805 = 152177) (by norm_num)
theorem B340277 : Blo 223812 340277 := bbase (se 5 (by rfl) ⟨15950, by rfl⟩ : syracuseStep 340277 = 31901) (by norm_num)
theorem B504125 : Blo 223812 504125 := bbase (se 3 (by rfl) ⟨94523, by rfl⟩ : syracuseStep 504125 = 189047) (by norm_num)
theorem B340301 : Blo 223812 340301 := bbase (se 3 (by rfl) ⟨63806, by rfl⟩ : syracuseStep 340301 = 127613) (by norm_num)
theorem B569693 : Blo 223812 569693 := bbase (se 3 (by rfl) ⟨106817, by rfl⟩ : syracuseStep 569693 = 213635) (by norm_num)
theorem B340325 : Blo 223812 340325 := bbase (se 4 (by rfl) ⟨31905, by rfl⟩ : syracuseStep 340325 = 63811) (by norm_num)
theorem B340349 : Blo 223812 340349 := bbase (se 3 (by rfl) ⟨63815, by rfl⟩ : syracuseStep 340349 = 127631) (by norm_num)
theorem B504197 : Blo 223812 504197 := bbase (se 4 (by rfl) ⟨47268, by rfl⟩ : syracuseStep 504197 = 94537) (by norm_num)
theorem B340373 : Blo 223812 340373 := bbase (se 6 (by rfl) ⟨7977, by rfl⟩ : syracuseStep 340373 = 15955) (by norm_num)
theorem B340397 : Blo 223812 340397 := bbase (se 3 (by rfl) ⟨63824, by rfl⟩ : syracuseStep 340397 = 127649) (by norm_num)
theorem B340421 : Blo 223812 340421 := bbase (se 4 (by rfl) ⟨31914, by rfl⟩ : syracuseStep 340421 = 63829) (by norm_num)
theorem B504269 : Blo 223812 504269 := bbase (se 3 (by rfl) ⟨94550, by rfl⟩ : syracuseStep 504269 = 189101) (by norm_num)
theorem B766421 : Blo 223812 766421 := bbase (se 7 (by rfl) ⟨8981, by rfl⟩ : syracuseStep 766421 = 17963) (by norm_num)
theorem B340445 : Blo 223812 340445 := bbase (se 3 (by rfl) ⟨63833, by rfl⟩ : syracuseStep 340445 = 127667) (by norm_num)
theorem B340469 : Blo 223812 340469 := bbase (se 5 (by rfl) ⟨15959, by rfl⟩ : syracuseStep 340469 = 31919) (by norm_num)
theorem B242185 : Blo 223812 242185 := bbase (se 2 (by rfl) ⟨90819, by rfl⟩ : syracuseStep 242185 = 181639) (by norm_num)
theorem B340493 : Blo 223812 340493 := bbase (se 3 (by rfl) ⟨63842, by rfl⟩ : syracuseStep 340493 = 127685) (by norm_num)
theorem B504341 : Blo 223812 504341 := bbase (se 6 (by rfl) ⟨11820, by rfl⟩ : syracuseStep 504341 = 23641) (by norm_num)
theorem B340517 : Blo 223812 340517 := bbase (se 4 (by rfl) ⟨31923, by rfl⟩ : syracuseStep 340517 = 63847) (by norm_num)
theorem B340541 : Blo 223812 340541 := bbase (se 3 (by rfl) ⟨63851, by rfl⟩ : syracuseStep 340541 = 127703) (by norm_num)
theorem B1618517 : Blo 223812 1618517 := bbase (se 8 (by rfl) ⟨9483, by rfl⟩ : syracuseStep 1618517 = 18967) (by norm_num)
theorem B340565 : Blo 223812 340565 := bbase (se 8 (by rfl) ⟨1995, by rfl⟩ : syracuseStep 340565 = 3991) (by norm_num)
theorem B504413 : Blo 223812 504413 := bbase (se 3 (by rfl) ⟨94577, by rfl⟩ : syracuseStep 504413 = 189155) (by norm_num)
theorem B340589 : Blo 223812 340589 := bbase (se 3 (by rfl) ⟨63860, by rfl⟩ : syracuseStep 340589 = 127721) (by norm_num)
theorem B242309 : Blo 223812 242309 := bbase (se 4 (by rfl) ⟨22716, by rfl⟩ : syracuseStep 242309 = 45433) (by norm_num)
theorem B340613 : Blo 223812 340613 := bbase (se 4 (by rfl) ⟨31932, by rfl⟩ : syracuseStep 340613 = 63865) (by norm_num)
theorem B340637 : Blo 223812 340637 := bbase (se 3 (by rfl) ⟨63869, by rfl⟩ : syracuseStep 340637 = 127739) (by norm_num)
theorem B504485 : Blo 223812 504485 := bbase (se 4 (by rfl) ⟨47295, by rfl⟩ : syracuseStep 504485 = 94591) (by norm_num)
theorem B570037 : Blo 223812 570037 := bbase (se 5 (by rfl) ⟨26720, by rfl⟩ : syracuseStep 570037 = 53441) (by norm_num)
theorem B340661 : Blo 223812 340661 := bbase (se 5 (by rfl) ⟨15968, by rfl⟩ : syracuseStep 340661 = 31937) (by norm_num)
theorem B340685 : Blo 223812 340685 := bbase (se 3 (by rfl) ⟨63878, by rfl⟩ : syracuseStep 340685 = 127757) (by norm_num)
theorem B340709 : Blo 223812 340709 := bbase (se 4 (by rfl) ⟨31941, by rfl⟩ : syracuseStep 340709 = 63883) (by norm_num)
theorem B504557 : Blo 223812 504557 := bbase (se 3 (by rfl) ⟨94604, by rfl⟩ : syracuseStep 504557 = 189209) (by norm_num)
theorem B340733 : Blo 223812 340733 := bbase (se 3 (by rfl) ⟨63887, by rfl⟩ : syracuseStep 340733 = 127775) (by norm_num)
theorem B340757 : Blo 223812 340757 := bbase (se 6 (by rfl) ⟨7986, by rfl⟩ : syracuseStep 340757 = 15973) (by norm_num)
theorem B1946389 : Blo 223812 1946389 := bbase (se 6 (by rfl) ⟨45618, by rfl⟩ : syracuseStep 1946389 = 91237) (by norm_num)
theorem B570149 : Blo 223812 570149 := bbase (se 4 (by rfl) ⟨53451, by rfl⟩ : syracuseStep 570149 = 106903) (by norm_num)
theorem B406309 : Blo 223812 406309 := bbase (se 4 (by rfl) ⟨38091, by rfl⟩ : syracuseStep 406309 = 76183) (by norm_num)
theorem B340781 : Blo 223812 340781 := bbase (se 3 (by rfl) ⟨63896, by rfl⟩ : syracuseStep 340781 = 127793) (by norm_num)
theorem B504629 : Blo 223812 504629 := bbase (se 5 (by rfl) ⟨23654, by rfl⟩ : syracuseStep 504629 = 47309) (by norm_num)
theorem B340805 : Blo 223812 340805 := bbase (se 4 (by rfl) ⟨31950, by rfl⟩ : syracuseStep 340805 = 63901) (by norm_num)
theorem B340829 : Blo 223812 340829 := bbase (se 3 (by rfl) ⟨63905, by rfl⟩ : syracuseStep 340829 = 127811) (by norm_num)
theorem B340853 : Blo 223812 340853 := bbase (se 5 (by rfl) ⟨15977, by rfl⟩ : syracuseStep 340853 = 31955) (by norm_num)
theorem B504701 : Blo 223812 504701 := bbase (se 3 (by rfl) ⟨94631, by rfl⟩ : syracuseStep 504701 = 189263) (by norm_num)
theorem B242561 : Blo 223812 242561 := bbase (se 2 (by rfl) ⟨90960, by rfl⟩ : syracuseStep 242561 = 181921) (by norm_num)
theorem B766853 : Blo 223812 766853 := bbase (se 4 (by rfl) ⟨71892, by rfl⟩ : syracuseStep 766853 = 143785) (by norm_num)
theorem B340877 : Blo 223812 340877 := bbase (se 3 (by rfl) ⟨63914, by rfl⟩ : syracuseStep 340877 = 127829) (by norm_num)
theorem B340901 : Blo 223812 340901 := bbase (se 4 (by rfl) ⟨31959, by rfl⟩ : syracuseStep 340901 = 63919) (by norm_num)
theorem B340925 : Blo 223812 340925 := bbase (se 3 (by rfl) ⟨63923, by rfl⟩ : syracuseStep 340925 = 127847) (by norm_num)
theorem B504773 : Blo 223812 504773 := bbase (se 4 (by rfl) ⟨47322, by rfl⟩ : syracuseStep 504773 = 94645) (by norm_num)
theorem B340949 : Blo 223812 340949 := bbase (se 7 (by rfl) ⟨3995, by rfl⟩ : syracuseStep 340949 = 7991) (by norm_num)
theorem B570341 : Blo 223812 570341 := bbase (se 4 (by rfl) ⟨53469, by rfl⟩ : syracuseStep 570341 = 106939) (by norm_num)
theorem B340973 : Blo 223812 340973 := bbase (se 3 (by rfl) ⟨63932, by rfl⟩ : syracuseStep 340973 = 127865) (by norm_num)
theorem B340997 : Blo 223812 340997 := bbase (se 4 (by rfl) ⟨31968, by rfl⟩ : syracuseStep 340997 = 63937) (by norm_num)
theorem B504845 : Blo 223812 504845 := bbase (se 3 (by rfl) ⟨94658, by rfl⟩ : syracuseStep 504845 = 189317) (by norm_num)
theorem B341021 : Blo 223812 341021 := bbase (se 3 (by rfl) ⟨63941, by rfl⟩ : syracuseStep 341021 = 127883) (by norm_num)
theorem B341045 : Blo 223812 341045 := bbase (se 5 (by rfl) ⟨15986, by rfl⟩ : syracuseStep 341045 = 31973) (by norm_num)
theorem B341069 : Blo 223812 341069 := bbase (se 3 (by rfl) ⟨63950, by rfl⟩ : syracuseStep 341069 = 127901) (by norm_num)
theorem B504917 : Blo 223812 504917 := bbase (se 8 (by rfl) ⟨2958, by rfl⟩ : syracuseStep 504917 = 5917) (by norm_num)
theorem B341093 : Blo 223812 341093 := bbase (se 4 (by rfl) ⟨31977, by rfl⟩ : syracuseStep 341093 = 63955) (by norm_num)
theorem B275581 : Blo 223812 275581 := bbase (se 3 (by rfl) ⟨51671, by rfl⟩ : syracuseStep 275581 = 103343) (by norm_num)
theorem B341117 : Blo 223812 341117 := bbase (se 3 (by rfl) ⟨63959, by rfl⟩ : syracuseStep 341117 = 127919) (by norm_num)
theorem B2897045 : Blo 223812 2897045 := bbase (se 6 (by rfl) ⟨67899, by rfl⟩ : syracuseStep 2897045 = 135799) (by norm_num)
theorem B341141 : Blo 223812 341141 := bbase (se 6 (by rfl) ⟨7995, by rfl⟩ : syracuseStep 341141 = 15991) (by norm_num)
theorem B504989 : Blo 223812 504989 := bbase (se 3 (by rfl) ⟨94685, by rfl⟩ : syracuseStep 504989 = 189371) (by norm_num)
theorem B341165 : Blo 223812 341165 := bbase (se 3 (by rfl) ⟨63968, by rfl⟩ : syracuseStep 341165 = 127937) (by norm_num)
theorem B341189 : Blo 223812 341189 := bbase (se 4 (by rfl) ⟨31986, by rfl⟩ : syracuseStep 341189 = 63973) (by norm_num)
theorem B341213 : Blo 223812 341213 := bbase (se 3 (by rfl) ⟨63977, by rfl⟩ : syracuseStep 341213 = 127955) (by norm_num)
theorem B505061 : Blo 223812 505061 := bbase (se 4 (by rfl) ⟨47349, by rfl⟩ : syracuseStep 505061 = 94699) (by norm_num)
theorem B341237 : Blo 223812 341237 := bbase (se 5 (by rfl) ⟨15995, by rfl⟩ : syracuseStep 341237 = 31991) (by norm_num)
theorem B341261 : Blo 223812 341261 := bbase (se 3 (by rfl) ⟨63986, by rfl⟩ : syracuseStep 341261 = 127973) (by norm_num)
theorem B341285 : Blo 223812 341285 := bbase (se 4 (by rfl) ⟨31995, by rfl⟩ : syracuseStep 341285 = 63991) (by norm_num)
theorem B505133 : Blo 223812 505133 := bbase (se 3 (by rfl) ⟨94712, by rfl⟩ : syracuseStep 505133 = 189425) (by norm_num)
theorem B767285 : Blo 223812 767285 := bbase (se 5 (by rfl) ⟨35966, by rfl⟩ : syracuseStep 767285 = 71933) (by norm_num)
theorem B570685 : Blo 223812 570685 := bbase (se 3 (by rfl) ⟨107003, by rfl⟩ : syracuseStep 570685 = 214007) (by norm_num)
theorem B341309 : Blo 223812 341309 := bbase (se 3 (by rfl) ⟨63995, by rfl⟩ : syracuseStep 341309 = 127991) (by norm_num)
theorem B243005 : Blo 223812 243005 := bbase (se 3 (by rfl) ⟨45563, by rfl⟩ : syracuseStep 243005 = 91127) (by norm_num)
theorem B341333 : Blo 223812 341333 := bbase (se 13 (by rfl) ⟨62, by rfl⟩ : syracuseStep 341333 = 125) (by norm_num)
theorem B341357 : Blo 223812 341357 := bbase (se 3 (by rfl) ⟨64004, by rfl⟩ : syracuseStep 341357 = 128009) (by norm_num)
theorem B505205 : Blo 223812 505205 := bbase (se 5 (by rfl) ⟨23681, by rfl⟩ : syracuseStep 505205 = 47363) (by norm_num)
theorem B341381 : Blo 223812 341381 := bbase (se 4 (by rfl) ⟨32004, by rfl⟩ : syracuseStep 341381 = 64009) (by norm_num)
theorem B537997 : Blo 223812 537997 := bbase (se 3 (by rfl) ⟨100874, by rfl⟩ : syracuseStep 537997 = 201749) (by norm_num)
theorem B341405 : Blo 223812 341405 := bbase (se 3 (by rfl) ⟨64013, by rfl⟩ : syracuseStep 341405 = 128027) (by norm_num)
theorem B570797 : Blo 223812 570797 := bbase (se 3 (by rfl) ⟨107024, by rfl⟩ : syracuseStep 570797 = 214049) (by norm_num)
theorem B341429 : Blo 223812 341429 := bbase (se 5 (by rfl) ⟨16004, by rfl⟩ : syracuseStep 341429 = 32009) (by norm_num)
theorem B505277 : Blo 223812 505277 := bbase (se 3 (by rfl) ⟨94739, by rfl⟩ : syracuseStep 505277 = 189479) (by norm_num)
theorem B341453 : Blo 223812 341453 := bbase (se 3 (by rfl) ⟨64022, by rfl⟩ : syracuseStep 341453 = 128045) (by norm_num)
theorem B341477 : Blo 223812 341477 := bbase (se 4 (by rfl) ⟨32013, by rfl⟩ : syracuseStep 341477 = 64027) (by norm_num)
theorem B538093 : Blo 223812 538093 := bbase (se 3 (by rfl) ⟨100892, by rfl⟩ : syracuseStep 538093 = 201785) (by norm_num)
theorem B341501 : Blo 223812 341501 := bbase (se 3 (by rfl) ⟨64031, by rfl⟩ : syracuseStep 341501 = 128063) (by norm_num)
theorem B505349 : Blo 223812 505349 := bbase (se 4 (by rfl) ⟨47376, by rfl⟩ : syracuseStep 505349 = 94753) (by norm_num)
theorem B341525 : Blo 223812 341525 := bbase (se 6 (by rfl) ⟨8004, by rfl⟩ : syracuseStep 341525 = 16009) (by norm_num)
theorem B341549 : Blo 223812 341549 := bbase (se 3 (by rfl) ⟨64040, by rfl⟩ : syracuseStep 341549 = 128081) (by norm_num)
theorem B243253 : Blo 223812 243253 := bbase (se 5 (by rfl) ⟨11402, by rfl⟩ : syracuseStep 243253 = 22805) (by norm_num)
theorem B341573 : Blo 223812 341573 := bbase (se 4 (by rfl) ⟨32022, by rfl⟩ : syracuseStep 341573 = 64045) (by norm_num)
theorem B505421 : Blo 223812 505421 := bbase (se 3 (by rfl) ⟨94766, by rfl⟩ : syracuseStep 505421 = 189533) (by norm_num)
theorem B341597 : Blo 223812 341597 := bbase (se 3 (by rfl) ⟨64049, by rfl⟩ : syracuseStep 341597 = 128099) (by norm_num)
theorem B570989 : Blo 223812 570989 := bbase (se 3 (by rfl) ⟨107060, by rfl⟩ : syracuseStep 570989 = 214121) (by norm_num)
theorem B341621 : Blo 223812 341621 := bbase (se 5 (by rfl) ⟨16013, by rfl⟩ : syracuseStep 341621 = 32027) (by norm_num)
theorem B341645 : Blo 223812 341645 := bbase (se 3 (by rfl) ⟨64058, by rfl⟩ : syracuseStep 341645 = 128117) (by norm_num)
theorem B505493 : Blo 223812 505493 := bbase (se 6 (by rfl) ⟨11847, by rfl⟩ : syracuseStep 505493 = 23695) (by norm_num)
theorem B407189 : Blo 223812 407189 := bbase (se 6 (by rfl) ⟨9543, by rfl⟩ : syracuseStep 407189 = 19087) (by norm_num)
theorem B341669 : Blo 223812 341669 := bbase (se 4 (by rfl) ⟨32031, by rfl⟩ : syracuseStep 341669 = 64063) (by norm_num)
theorem B538285 : Blo 223812 538285 := bbase (se 3 (by rfl) ⟨100928, by rfl⟩ : syracuseStep 538285 = 201857) (by norm_num)
theorem B341693 : Blo 223812 341693 := bbase (se 3 (by rfl) ⟨64067, by rfl⟩ : syracuseStep 341693 = 128135) (by norm_num)
theorem B341717 : Blo 223812 341717 := bbase (se 7 (by rfl) ⟨4004, by rfl⟩ : syracuseStep 341717 = 8009) (by norm_num)
theorem B505565 : Blo 223812 505565 := bbase (se 3 (by rfl) ⟨94793, by rfl⟩ : syracuseStep 505565 = 189587) (by norm_num)
theorem B407261 : Blo 223812 407261 := bbase (se 3 (by rfl) ⟨76361, by rfl⟩ : syracuseStep 407261 = 152723) (by norm_num)
theorem B767717 : Blo 223812 767717 := bbase (se 4 (by rfl) ⟨71973, by rfl⟩ : syracuseStep 767717 = 143947) (by norm_num)
theorem B3127061 : Blo 223812 3127061 := bbase (se 6 (by rfl) ⟨73290, by rfl⟩ : syracuseStep 3127061 = 146581) (by norm_num)
theorem B505637 : Blo 223812 505637 := bbase (se 4 (by rfl) ⟨47403, by rfl⟩ : syracuseStep 505637 = 94807) (by norm_num)
theorem B505709 : Blo 223812 505709 := bbase (se 3 (by rfl) ⟨94820, by rfl⟩ : syracuseStep 505709 = 189641) (by norm_num)
theorem B407405 : Blo 223812 407405 := bbase (se 3 (by rfl) ⟨76388, by rfl⟩ : syracuseStep 407405 = 152777) (by norm_num)
theorem B505781 : Blo 223812 505781 := bbase (se 5 (by rfl) ⟨23708, by rfl⟩ : syracuseStep 505781 = 47417) (by norm_num)
theorem B407477 : Blo 223812 407477 := bbase (se 5 (by rfl) ⟨19100, by rfl⟩ : syracuseStep 407477 = 38201) (by norm_num)
theorem B571333 : Blo 223812 571333 := bbase (se 4 (by rfl) ⟨53562, by rfl⟩ : syracuseStep 571333 = 107125) (by norm_num)
theorem B538613 : Blo 223812 538613 := bbase (se 5 (by rfl) ⟨25247, by rfl⟩ : syracuseStep 538613 = 50495) (by norm_num)
theorem B505853 : Blo 223812 505853 := bbase (se 3 (by rfl) ⟨94847, by rfl⟩ : syracuseStep 505853 = 189695) (by norm_num)
theorem B571445 : Blo 223812 571445 := bbase (se 5 (by rfl) ⟨26786, by rfl⟩ : syracuseStep 571445 = 53573) (by norm_num)
theorem B505925 : Blo 223812 505925 := bbase (se 4 (by rfl) ⟨47430, by rfl⟩ : syracuseStep 505925 = 94861) (by norm_num)
theorem B505997 : Blo 223812 505997 := bbase (se 3 (by rfl) ⟨94874, by rfl⟩ : syracuseStep 505997 = 189749) (by norm_num)
theorem B768149 : Blo 223812 768149 := bbase (se 6 (by rfl) ⟨18003, by rfl⟩ : syracuseStep 768149 = 36007) (by norm_num)
theorem B506069 : Blo 223812 506069 := bbase (se 7 (by rfl) ⟨5930, by rfl⟩ : syracuseStep 506069 = 11861) (by norm_num)
theorem B2570453 : Blo 223812 2570453 := bbase (se 7 (by rfl) ⟨30122, by rfl⟩ : syracuseStep 2570453 = 60245) (by norm_num)
theorem B571637 : Blo 223812 571637 := bbase (se 5 (by rfl) ⟨26795, by rfl⟩ : syracuseStep 571637 = 53591) (by norm_num)
theorem B506141 : Blo 223812 506141 := bbase (se 3 (by rfl) ⟨94901, by rfl⟩ : syracuseStep 506141 = 189803) (by norm_num)
theorem B506213 : Blo 223812 506213 := bbase (se 4 (by rfl) ⟨47457, by rfl⟩ : syracuseStep 506213 = 94915) (by norm_num)
theorem B539045 : Blo 223812 539045 := bbase (se 4 (by rfl) ⟨50535, by rfl⟩ : syracuseStep 539045 = 101071) (by norm_num)
theorem B506285 : Blo 223812 506285 := bbase (se 3 (by rfl) ⟨94928, by rfl⟩ : syracuseStep 506285 = 189857) (by norm_num)
theorem B506357 : Blo 223812 506357 := bbase (se 5 (by rfl) ⟨23735, by rfl⟩ : syracuseStep 506357 = 47471) (by norm_num)
theorem B506429 : Blo 223812 506429 := bbase (se 3 (by rfl) ⟨94955, by rfl⟩ : syracuseStep 506429 = 189911) (by norm_num)
theorem B768581 : Blo 223812 768581 := bbase (se 4 (by rfl) ⟨72054, by rfl⟩ : syracuseStep 768581 = 144109) (by norm_num)
theorem B342605 : Blo 223812 342605 := bbase (se 3 (by rfl) ⟨64238, by rfl⟩ : syracuseStep 342605 = 128477) (by norm_num)
theorem B571981 : Blo 223812 571981 := bbase (se 3 (by rfl) ⟨107246, by rfl⟩ : syracuseStep 571981 = 214493) (by norm_num)
theorem B506501 : Blo 223812 506501 := bbase (se 4 (by rfl) ⟨47484, by rfl⟩ : syracuseStep 506501 = 94969) (by norm_num)
theorem B572093 : Blo 223812 572093 := bbase (se 3 (by rfl) ⟨107267, by rfl⟩ : syracuseStep 572093 = 214535) (by norm_num)
theorem B506573 : Blo 223812 506573 := bbase (se 3 (by rfl) ⟨94982, by rfl⟩ : syracuseStep 506573 = 189965) (by norm_num)
theorem B408269 : Blo 223812 408269 := bbase (se 3 (by rfl) ⟨76550, by rfl⟩ : syracuseStep 408269 = 153101) (by norm_num)
theorem B277229 : Blo 223812 277229 := bbase (se 3 (by rfl) ⟨51980, by rfl⟩ : syracuseStep 277229 = 103961) (by norm_num)
theorem B539381 : Blo 223812 539381 := bbase (se 5 (by rfl) ⟨25283, by rfl⟩ : syracuseStep 539381 = 50567) (by norm_num)
theorem B506645 : Blo 223812 506645 := bbase (se 6 (by rfl) ⟨11874, by rfl⟩ : syracuseStep 506645 = 23749) (by norm_num)
theorem B637733 : Blo 223812 637733 := bbase (se 4 (by rfl) ⟨59787, by rfl⟩ : syracuseStep 637733 = 119575) (by norm_num)
theorem B506717 : Blo 223812 506717 := bbase (se 3 (by rfl) ⟨95009, by rfl⟩ : syracuseStep 506717 = 190019) (by norm_num)
theorem B244577 : Blo 223812 244577 := bbase (se 2 (by rfl) ⟨91716, by rfl⟩ : syracuseStep 244577 = 183433) (by norm_num)
theorem B572285 : Blo 223812 572285 := bbase (se 3 (by rfl) ⟨107303, by rfl⟩ : syracuseStep 572285 = 214607) (by norm_num)
theorem B506789 : Blo 223812 506789 := bbase (se 4 (by rfl) ⟨47511, by rfl⟩ : syracuseStep 506789 = 95023) (by norm_num)
theorem B506861 : Blo 223812 506861 := bbase (se 3 (by rfl) ⟨95036, by rfl⟩ : syracuseStep 506861 = 190073) (by norm_num)
theorem B506933 : Blo 223812 506933 := bbase (se 5 (by rfl) ⟨23762, by rfl⟩ : syracuseStep 506933 = 47525) (by norm_num)
theorem B507005 : Blo 223812 507005 := bbase (se 3 (by rfl) ⟨95063, by rfl⟩ : syracuseStep 507005 = 190127) (by norm_num)
theorem B507077 : Blo 223812 507077 := bbase (se 4 (by rfl) ⟨47538, by rfl⟩ : syracuseStep 507077 = 95077) (by norm_num)
theorem B277705 : Blo 223812 277705 := bbase (se 2 (by rfl) ⟨104139, by rfl⟩ : syracuseStep 277705 = 208279) (by norm_num)
theorem B572629 : Blo 223812 572629 := bbase (se 7 (by rfl) ⟨6710, by rfl⟩ : syracuseStep 572629 = 13421) (by norm_num)
theorem B343261 : Blo 223812 343261 := bbase (se 3 (by rfl) ⟨64361, by rfl⟩ : syracuseStep 343261 = 128723) (by norm_num)
theorem B343285 : Blo 223812 343285 := bbase (se 5 (by rfl) ⟨16091, by rfl⟩ : syracuseStep 343285 = 32183) (by norm_num)
theorem B507149 : Blo 223812 507149 := bbase (se 3 (by rfl) ⟨95090, by rfl⟩ : syracuseStep 507149 = 190181) (by norm_num)
theorem B572741 : Blo 223812 572741 := bbase (se 4 (by rfl) ⟨53694, by rfl⟩ : syracuseStep 572741 = 107389) (by norm_num)
theorem B507221 : Blo 223812 507221 := bbase (se 11 (by rfl) ⟨371, by rfl⟩ : syracuseStep 507221 = 743) (by norm_num)
theorem B507293 : Blo 223812 507293 := bbase (se 3 (by rfl) ⟨95117, by rfl⟩ : syracuseStep 507293 = 190235) (by norm_num)
theorem B1457621 : Blo 223812 1457621 := bbase (se 7 (by rfl) ⟨17081, by rfl⟩ : syracuseStep 1457621 = 34163) (by norm_num)
theorem B507365 : Blo 223812 507365 := bbase (se 4 (by rfl) ⟨47565, by rfl⟩ : syracuseStep 507365 = 95131) (by norm_num)
theorem B572933 : Blo 223812 572933 := bbase (se 4 (by rfl) ⟨53712, by rfl⟩ : syracuseStep 572933 = 107425) (by norm_num)
theorem B507437 : Blo 223812 507437 := bbase (se 3 (by rfl) ⟨95144, by rfl⟩ : syracuseStep 507437 = 190289) (by norm_num)
theorem B605765 : Blo 223812 605765 := bbase (se 4 (by rfl) ⟨56790, by rfl⟩ : syracuseStep 605765 = 113581) (by norm_num)
theorem B507509 : Blo 223812 507509 := bbase (se 5 (by rfl) ⟨23789, by rfl⟩ : syracuseStep 507509 = 47579) (by norm_num)
theorem B507581 : Blo 223812 507581 := bbase (se 3 (by rfl) ⟨95171, by rfl⟩ : syracuseStep 507581 = 190343) (by norm_num)
theorem B769765 : Blo 223812 769765 := bbase (se 4 (by rfl) ⟨72165, by rfl⟩ : syracuseStep 769765 = 144331) (by norm_num)
theorem B507653 : Blo 223812 507653 := bbase (se 4 (by rfl) ⟨47592, by rfl⟩ : syracuseStep 507653 = 95185) (by norm_num)
theorem B638741 : Blo 223812 638741 := bbase (se 6 (by rfl) ⟨14970, by rfl⟩ : syracuseStep 638741 = 29941) (by norm_num)
theorem B540437 : Blo 223812 540437 := bbase (se 6 (by rfl) ⟨12666, by rfl⟩ : syracuseStep 540437 = 25333) (by norm_num)
theorem B507725 : Blo 223812 507725 := bbase (se 3 (by rfl) ⟨95198, by rfl⟩ : syracuseStep 507725 = 190397) (by norm_num)
theorem B573277 : Blo 223812 573277 := bbase (se 3 (by rfl) ⟨107489, by rfl⟩ : syracuseStep 573277 = 214979) (by norm_num)
theorem B507797 : Blo 223812 507797 := bbase (se 6 (by rfl) ⟨11901, by rfl⟩ : syracuseStep 507797 = 23803) (by norm_num)
theorem B376741 : Blo 223812 376741 := bbase (se 4 (by rfl) ⟨35319, by rfl⟩ : syracuseStep 376741 = 70639) (by norm_num)
theorem B606133 : Blo 223812 606133 := bbase (se 5 (by rfl) ⟨28412, by rfl⟩ : syracuseStep 606133 = 56825) (by norm_num)
theorem B573389 : Blo 223812 573389 := bbase (se 3 (by rfl) ⟨107510, by rfl⟩ : syracuseStep 573389 = 215021) (by norm_num)
theorem B507869 : Blo 223812 507869 := bbase (se 3 (by rfl) ⟨95225, by rfl⟩ : syracuseStep 507869 = 190451) (by norm_num)
theorem B507941 : Blo 223812 507941 := bbase (se 4 (by rfl) ⟨47619, by rfl⟩ : syracuseStep 507941 = 95239) (by norm_num)
theorem B508013 : Blo 223812 508013 := bbase (se 3 (by rfl) ⟨95252, by rfl⟩ : syracuseStep 508013 = 190505) (by norm_num)
theorem B573581 : Blo 223812 573581 := bbase (se 3 (by rfl) ⟨107546, by rfl⟩ : syracuseStep 573581 = 215093) (by norm_num)
theorem B508085 : Blo 223812 508085 := bbase (se 5 (by rfl) ⟨23816, by rfl⟩ : syracuseStep 508085 = 47633) (by norm_num)
theorem B508157 : Blo 223812 508157 := bbase (se 3 (by rfl) ⟨95279, by rfl⟩ : syracuseStep 508157 = 190559) (by norm_num)
theorem B1294613 : Blo 223812 1294613 := bbase (se 6 (by rfl) ⟨30342, by rfl⟩ : syracuseStep 1294613 = 60685) (by norm_num)
theorem B508229 : Blo 223812 508229 := bbase (se 4 (by rfl) ⟨47646, by rfl⟩ : syracuseStep 508229 = 95293) (by norm_num)
theorem B508301 : Blo 223812 508301 := bbase (se 3 (by rfl) ⟨95306, by rfl⟩ : syracuseStep 508301 = 190613) (by norm_num)
theorem B508373 : Blo 223812 508373 := bbase (se 7 (by rfl) ⟨5957, by rfl⟩ : syracuseStep 508373 = 11915) (by norm_num)
theorem B573925 : Blo 223812 573925 := bbase (se 4 (by rfl) ⟨53805, by rfl⟩ : syracuseStep 573925 = 107611) (by norm_num)
theorem B508445 : Blo 223812 508445 := bbase (se 3 (by rfl) ⟨95333, by rfl⟩ : syracuseStep 508445 = 190667) (by norm_num)
theorem B574037 : Blo 223812 574037 := bbase (se 8 (by rfl) ⟨3363, by rfl⟩ : syracuseStep 574037 = 6727) (by norm_num)
theorem B508517 : Blo 223812 508517 := bbase (se 4 (by rfl) ⟨47673, by rfl⟩ : syracuseStep 508517 = 95347) (by norm_num)
theorem B508589 : Blo 223812 508589 := bbase (se 3 (by rfl) ⟨95360, by rfl⟩ : syracuseStep 508589 = 190721) (by norm_num)
theorem B508661 : Blo 223812 508661 := bbase (se 5 (by rfl) ⟨23843, by rfl⟩ : syracuseStep 508661 = 47687) (by norm_num)
theorem B574229 : Blo 223812 574229 := bbase (se 6 (by rfl) ⟨13458, by rfl⟩ : syracuseStep 574229 = 26917) (by norm_num)
theorem B508733 : Blo 223812 508733 := bbase (se 3 (by rfl) ⟨95387, by rfl⟩ : syracuseStep 508733 = 190775) (by norm_num)
theorem B508805 : Blo 223812 508805 := bbase (se 4 (by rfl) ⟨47700, by rfl⟩ : syracuseStep 508805 = 95401) (by norm_num)
theorem B377797 : Blo 223812 377797 := bbase (se 4 (by rfl) ⟨35418, by rfl⟩ : syracuseStep 377797 = 70837) (by norm_num)
theorem B508877 : Blo 223812 508877 := bbase (se 3 (by rfl) ⟨95414, by rfl⟩ : syracuseStep 508877 = 190829) (by norm_num)
theorem B345061 : Blo 223812 345061 := bbase (se 4 (by rfl) ⟨32349, by rfl⟩ : syracuseStep 345061 = 64699) (by norm_num)
theorem B508949 : Blo 223812 508949 := bbase (se 6 (by rfl) ⟨11928, by rfl⟩ : syracuseStep 508949 = 23857) (by norm_num)
theorem B377885 : Blo 223812 377885 := bbase (se 3 (by rfl) ⟨70853, by rfl⟩ : syracuseStep 377885 = 141707) (by norm_num)
theorem B967733 : Blo 223812 967733 := bbase (se 5 (by rfl) ⟨45362, by rfl⟩ : syracuseStep 967733 = 90725) (by norm_num)
theorem B607301 : Blo 223812 607301 := bbase (se 4 (by rfl) ⟨56934, by rfl⟩ : syracuseStep 607301 = 113869) (by norm_num)
theorem B509021 : Blo 223812 509021 := bbase (se 3 (by rfl) ⟨95441, by rfl⟩ : syracuseStep 509021 = 190883) (by norm_num)
theorem B574573 : Blo 223812 574573 := bbase (se 3 (by rfl) ⟨107732, by rfl⟩ : syracuseStep 574573 = 215465) (by norm_num)
theorem B378013 : Blo 223812 378013 := bbase (se 3 (by rfl) ⟨70877, by rfl⟩ : syracuseStep 378013 = 141755) (by norm_num)
theorem B509093 : Blo 223812 509093 := bbase (se 4 (by rfl) ⟨47727, by rfl⟩ : syracuseStep 509093 = 95455) (by norm_num)
theorem B574685 : Blo 223812 574685 := bbase (se 3 (by rfl) ⟨107753, by rfl⟩ : syracuseStep 574685 = 215507) (by norm_num)
theorem B509165 : Blo 223812 509165 := bbase (se 3 (by rfl) ⟨95468, by rfl⟩ : syracuseStep 509165 = 190937) (by norm_num)
theorem B378101 : Blo 223812 378101 := bbase (se 5 (by rfl) ⟨17723, by rfl⟩ : syracuseStep 378101 = 35447) (by norm_num)
theorem B509237 : Blo 223812 509237 := bbase (se 5 (by rfl) ⟨23870, by rfl⟩ : syracuseStep 509237 = 47741) (by norm_num)
theorem B640325 : Blo 223812 640325 := bbase (se 4 (by rfl) ⟨60030, by rfl⟩ : syracuseStep 640325 = 120061) (by norm_num)
theorem B968021 : Blo 223812 968021 := bbase (se 12 (by rfl) ⟨354, by rfl⟩ : syracuseStep 968021 = 709) (by norm_num)
theorem B378229 : Blo 223812 378229 := bbase (se 5 (by rfl) ⟨17729, by rfl⟩ : syracuseStep 378229 = 35459) (by norm_num)
theorem B509309 : Blo 223812 509309 := bbase (se 3 (by rfl) ⟨95495, by rfl⟩ : syracuseStep 509309 = 190991) (by norm_num)
theorem B607637 : Blo 223812 607637 := bbase (se 6 (by rfl) ⟨14241, by rfl⟩ : syracuseStep 607637 = 28483) (by norm_num)
theorem B574877 : Blo 223812 574877 := bbase (se 3 (by rfl) ⟨107789, by rfl⟩ : syracuseStep 574877 = 215579) (by norm_num)
theorem B1295797 : Blo 223812 1295797 := bbase (se 5 (by rfl) ⟨60740, by rfl⟩ : syracuseStep 1295797 = 121481) (by norm_num)
theorem B509381 : Blo 223812 509381 := bbase (se 4 (by rfl) ⟨47754, by rfl⟩ : syracuseStep 509381 = 95509) (by norm_num)
theorem B378317 : Blo 223812 378317 := bbase (se 3 (by rfl) ⟨70934, by rfl⟩ : syracuseStep 378317 = 141869) (by norm_num)
theorem B509453 : Blo 223812 509453 := bbase (se 3 (by rfl) ⟨95522, by rfl⟩ : syracuseStep 509453 = 191045) (by norm_num)
theorem B378445 : Blo 223812 378445 := bbase (se 3 (by rfl) ⟨70958, by rfl⟩ : syracuseStep 378445 = 141917) (by norm_num)
theorem B509525 : Blo 223812 509525 := bbase (se 8 (by rfl) ⟨2985, by rfl⟩ : syracuseStep 509525 = 5971) (by norm_num)
theorem B509597 : Blo 223812 509597 := bbase (se 3 (by rfl) ⟨95549, by rfl⟩ : syracuseStep 509597 = 191099) (by norm_num)
theorem B378533 : Blo 223812 378533 := bbase (se 4 (by rfl) ⟨35487, by rfl⟩ : syracuseStep 378533 = 70975) (by norm_num)
theorem B509669 : Blo 223812 509669 := bbase (se 4 (by rfl) ⟨47781, by rfl⟩ : syracuseStep 509669 = 95563) (by norm_num)
theorem B575221 : Blo 223812 575221 := bbase (se 5 (by rfl) ⟨26963, by rfl⟩ : syracuseStep 575221 = 53927) (by norm_num)
theorem B378661 : Blo 223812 378661 := bbase (se 4 (by rfl) ⟨35499, by rfl⟩ : syracuseStep 378661 = 70999) (by norm_num)
theorem B509741 : Blo 223812 509741 := bbase (se 3 (by rfl) ⟨95576, by rfl⟩ : syracuseStep 509741 = 191153) (by norm_num)
theorem B575333 : Blo 223812 575333 := bbase (se 4 (by rfl) ⟨53937, by rfl⟩ : syracuseStep 575333 = 107875) (by norm_num)
theorem B509813 : Blo 223812 509813 := bbase (se 5 (by rfl) ⟨23897, by rfl⟩ : syracuseStep 509813 = 47795) (by norm_num)
theorem B378749 : Blo 223812 378749 := bbase (se 3 (by rfl) ⟨71015, by rfl⟩ : syracuseStep 378749 = 142031) (by norm_num)
theorem B542629 : Blo 223812 542629 := bbase (se 4 (by rfl) ⟨50871, by rfl⟩ : syracuseStep 542629 = 101743) (by norm_num)
theorem B509885 : Blo 223812 509885 := bbase (se 3 (by rfl) ⟨95603, by rfl⟩ : syracuseStep 509885 = 191207) (by norm_num)
theorem B640997 : Blo 223812 640997 := bbase (se 4 (by rfl) ⟨60093, by rfl⟩ : syracuseStep 640997 = 120187) (by norm_num)
theorem B575477 : Blo 223812 575477 := bbase (se 5 (by rfl) ⟨26975, by rfl⟩ : syracuseStep 575477 = 53951) (by norm_num)
theorem B870389 : Blo 223812 870389 := bbase (se 5 (by rfl) ⟨40799, by rfl⟩ : syracuseStep 870389 = 81599) (by norm_num)
theorem B378877 : Blo 223812 378877 := bbase (se 3 (by rfl) ⟨71039, by rfl⟩ : syracuseStep 378877 = 142079) (by norm_num)
theorem B509957 : Blo 223812 509957 := bbase (se 4 (by rfl) ⟨47808, by rfl⟩ : syracuseStep 509957 = 95617) (by norm_num)
theorem B575525 : Blo 223812 575525 := bbase (se 4 (by rfl) ⟨53955, by rfl⟩ : syracuseStep 575525 = 107911) (by norm_num)
theorem B968773 : Blo 223812 968773 := bbase (se 4 (by rfl) ⟨90822, by rfl⟩ : syracuseStep 968773 = 181645) (by norm_num)
theorem B510029 : Blo 223812 510029 := bbase (se 3 (by rfl) ⟨95630, by rfl⟩ : syracuseStep 510029 = 191261) (by norm_num)
theorem B378965 : Blo 223812 378965 := bbase (se 8 (by rfl) ⟨2220, by rfl⟩ : syracuseStep 378965 = 4441) (by norm_num)
theorem B510101 : Blo 223812 510101 := bbase (se 6 (by rfl) ⟨11955, by rfl⟩ : syracuseStep 510101 = 23911) (by norm_num)
theorem B379093 : Blo 223812 379093 := bbase (se 7 (by rfl) ⟨4442, by rfl⟩ : syracuseStep 379093 = 8885) (by norm_num)
theorem B510173 : Blo 223812 510173 := bbase (se 3 (by rfl) ⟨95657, by rfl⟩ : syracuseStep 510173 = 191315) (by norm_num)
theorem B510245 : Blo 223812 510245 := bbase (se 4 (by rfl) ⟨47835, by rfl⟩ : syracuseStep 510245 = 95671) (by norm_num)
theorem B379181 : Blo 223812 379181 := bbase (se 3 (by rfl) ⟨71096, by rfl⟩ : syracuseStep 379181 = 142193) (by norm_num)
theorem B1624373 : Blo 223812 1624373 := bbase (se 5 (by rfl) ⟨76142, by rfl⟩ : syracuseStep 1624373 = 152285) (by norm_num)
theorem B510317 : Blo 223812 510317 := bbase (se 3 (by rfl) ⟨95684, by rfl⟩ : syracuseStep 510317 = 191369) (by norm_num)
theorem B575869 : Blo 223812 575869 := bbase (se 3 (by rfl) ⟨107975, by rfl⟩ : syracuseStep 575869 = 215951) (by norm_num)
theorem B641429 : Blo 223812 641429 := bbase (se 6 (by rfl) ⟨15033, by rfl⟩ : syracuseStep 641429 = 30067) (by norm_num)
theorem B379309 : Blo 223812 379309 := bbase (se 3 (by rfl) ⟨71120, by rfl⟩ : syracuseStep 379309 = 142241) (by norm_num)
theorem B510389 : Blo 223812 510389 := bbase (se 5 (by rfl) ⟨23924, by rfl⟩ : syracuseStep 510389 = 47849) (by norm_num)
theorem B575981 : Blo 223812 575981 := bbase (se 3 (by rfl) ⟨107996, by rfl⟩ : syracuseStep 575981 = 215993) (by norm_num)
theorem B1722869 : Blo 223812 1722869 := bbase (se 5 (by rfl) ⟨80759, by rfl⟩ : syracuseStep 1722869 = 161519) (by norm_num)
theorem B510461 : Blo 223812 510461 := bbase (se 3 (by rfl) ⟨95711, by rfl⟩ : syracuseStep 510461 = 191423) (by norm_num)
theorem B379397 : Blo 223812 379397 := bbase (se 4 (by rfl) ⟨35568, by rfl⟩ : syracuseStep 379397 = 71137) (by norm_num)
theorem B510533 : Blo 223812 510533 := bbase (se 4 (by rfl) ⟨47862, by rfl⟩ : syracuseStep 510533 = 95725) (by norm_num)
theorem B1133189 : Blo 223812 1133189 := bbase (se 4 (by rfl) ⟨106236, by rfl⟩ : syracuseStep 1133189 = 212473) (by norm_num)
theorem B379525 : Blo 223812 379525 := bbase (se 4 (by rfl) ⟨35580, by rfl⟩ : syracuseStep 379525 = 71161) (by norm_num)
theorem B510605 : Blo 223812 510605 := bbase (se 3 (by rfl) ⟨95738, by rfl⟩ : syracuseStep 510605 = 191477) (by norm_num)
theorem B576173 : Blo 223812 576173 := bbase (se 3 (by rfl) ⟨108032, by rfl⟩ : syracuseStep 576173 = 216065) (by norm_num)
theorem B510677 : Blo 223812 510677 := bbase (se 7 (by rfl) ⟨5984, by rfl⟩ : syracuseStep 510677 = 11969) (by norm_num)
theorem B379613 : Blo 223812 379613 := bbase (se 3 (by rfl) ⟨71177, by rfl⟩ : syracuseStep 379613 = 142355) (by norm_num)
theorem B510749 : Blo 223812 510749 := bbase (se 3 (by rfl) ⟨95765, by rfl⟩ : syracuseStep 510749 = 191531) (by norm_num)
theorem B969509 : Blo 223812 969509 := bbase (se 4 (by rfl) ⟨90891, by rfl⟩ : syracuseStep 969509 = 181783) (by norm_num)
theorem B379741 : Blo 223812 379741 := bbase (se 3 (by rfl) ⟨71201, by rfl⟩ : syracuseStep 379741 = 142403) (by norm_num)
theorem B510821 : Blo 223812 510821 := bbase (se 4 (by rfl) ⟨47889, by rfl⟩ : syracuseStep 510821 = 95779) (by norm_num)
theorem B510877 : Blo 223812 510877 := bbase (se 3 (by rfl) ⟨95789, by rfl⟩ : syracuseStep 510877 = 191579) (by norm_num)
theorem B510893 : Blo 223812 510893 := bbase (se 3 (by rfl) ⟨95792, by rfl⟩ : syracuseStep 510893 = 191585) (by norm_num)
theorem B379829 : Blo 223812 379829 := bbase (se 5 (by rfl) ⟨17804, by rfl⟩ : syracuseStep 379829 = 35609) (by norm_num)
theorem B510965 : Blo 223812 510965 := bbase (se 5 (by rfl) ⟨23951, by rfl⟩ : syracuseStep 510965 = 47903) (by norm_num)
theorem B576517 : Blo 223812 576517 := bbase (se 4 (by rfl) ⟨54048, by rfl⟩ : syracuseStep 576517 = 108097) (by norm_num)
theorem B379957 : Blo 223812 379957 := bbase (se 5 (by rfl) ⟨17810, by rfl⟩ : syracuseStep 379957 = 35621) (by norm_num)
theorem B511037 : Blo 223812 511037 := bbase (se 3 (by rfl) ⟨95819, by rfl⟩ : syracuseStep 511037 = 191639) (by norm_num)
theorem B1723477 : Blo 223812 1723477 := bbase (se 8 (by rfl) ⟨10098, by rfl⟩ : syracuseStep 1723477 = 20197) (by norm_num)
theorem B576629 : Blo 223812 576629 := bbase (se 5 (by rfl) ⟨27029, by rfl⟩ : syracuseStep 576629 = 54059) (by norm_num)
theorem B642181 : Blo 223812 642181 := bbase (se 4 (by rfl) ⟨60204, by rfl⟩ : syracuseStep 642181 = 120409) (by norm_num)
theorem B511109 : Blo 223812 511109 := bbase (se 4 (by rfl) ⟨47916, by rfl⟩ : syracuseStep 511109 = 95833) (by norm_num)
theorem B380045 : Blo 223812 380045 := bbase (se 3 (by rfl) ⟨71258, by rfl⟩ : syracuseStep 380045 = 142517) (by norm_num)
theorem B412877 : Blo 223812 412877 := bbase (se 3 (by rfl) ⟨77414, by rfl⟩ : syracuseStep 412877 = 154829) (by norm_num)
theorem B511181 : Blo 223812 511181 := bbase (se 3 (by rfl) ⟨95846, by rfl⟩ : syracuseStep 511181 = 191693) (by norm_num)
theorem B380173 : Blo 223812 380173 := bbase (se 3 (by rfl) ⟨71282, by rfl⟩ : syracuseStep 380173 = 142565) (by norm_num)
theorem B544013 : Blo 223812 544013 := bbase (se 3 (by rfl) ⟨102002, by rfl⟩ : syracuseStep 544013 = 204005) (by norm_num)
theorem B511253 : Blo 223812 511253 := bbase (se 6 (by rfl) ⟨11982, by rfl⟩ : syracuseStep 511253 = 23965) (by norm_num)
theorem B511325 : Blo 223812 511325 := bbase (se 3 (by rfl) ⟨95873, by rfl⟩ : syracuseStep 511325 = 191747) (by norm_num)
theorem B380261 : Blo 223812 380261 := bbase (se 4 (by rfl) ⟨35649, by rfl⟩ : syracuseStep 380261 = 71299) (by norm_num)
theorem B511397 : Blo 223812 511397 := bbase (se 4 (by rfl) ⟨47943, by rfl⟩ : syracuseStep 511397 = 95887) (by norm_num)
theorem B544205 : Blo 223812 544205 := bbase (se 3 (by rfl) ⟨102038, by rfl⟩ : syracuseStep 544205 = 204077) (by norm_num)
theorem B380389 : Blo 223812 380389 := bbase (se 4 (by rfl) ⟨35661, by rfl⟩ : syracuseStep 380389 = 71323) (by norm_num)
theorem B511469 : Blo 223812 511469 := bbase (se 3 (by rfl) ⟨95900, by rfl⟩ : syracuseStep 511469 = 191801) (by norm_num)
theorem B511541 : Blo 223812 511541 := bbase (se 5 (by rfl) ⟨23978, by rfl⟩ : syracuseStep 511541 = 47957) (by norm_num)
theorem B380477 : Blo 223812 380477 := bbase (se 3 (by rfl) ⟨71339, by rfl⟩ : syracuseStep 380477 = 142679) (by norm_num)
theorem B511613 : Blo 223812 511613 := bbase (se 3 (by rfl) ⟨95927, by rfl⟩ : syracuseStep 511613 = 191855) (by norm_num)
theorem B478885 : Blo 223812 478885 := bbase (se 4 (by rfl) ⟨44895, by rfl⟩ : syracuseStep 478885 = 89791) (by norm_num)
theorem B380605 : Blo 223812 380605 := bbase (se 3 (by rfl) ⟨71363, by rfl⟩ : syracuseStep 380605 = 142727) (by norm_num)
theorem B511685 : Blo 223812 511685 := bbase (se 4 (by rfl) ⟨47970, by rfl⟩ : syracuseStep 511685 = 95941) (by norm_num)
theorem B511757 : Blo 223812 511757 := bbase (se 3 (by rfl) ⟨95954, by rfl⟩ : syracuseStep 511757 = 191909) (by norm_num)
theorem B380693 : Blo 223812 380693 := bbase (se 6 (by rfl) ⟨8922, by rfl⟩ : syracuseStep 380693 = 17845) (by norm_num)
theorem B511829 : Blo 223812 511829 := bbase (se 9 (by rfl) ⟨1499, by rfl⟩ : syracuseStep 511829 = 2999) (by norm_num)
theorem B1134485 : Blo 223812 1134485 := bbase (se 6 (by rfl) ⟨26589, by rfl⟩ : syracuseStep 1134485 = 53179) (by norm_num)
theorem B380821 : Blo 223812 380821 := bbase (se 6 (by rfl) ⟨8925, by rfl⟩ : syracuseStep 380821 = 17851) (by norm_num)
theorem B511901 : Blo 223812 511901 := bbase (se 3 (by rfl) ⟨95981, by rfl⟩ : syracuseStep 511901 = 191963) (by norm_num)
theorem B511973 : Blo 223812 511973 := bbase (se 4 (by rfl) ⟨47997, by rfl⟩ : syracuseStep 511973 = 95995) (by norm_num)
theorem B380909 : Blo 223812 380909 := bbase (se 3 (by rfl) ⟨71420, by rfl⟩ : syracuseStep 380909 = 142841) (by norm_num)
theorem B512045 : Blo 223812 512045 := bbase (se 3 (by rfl) ⟨96008, by rfl⟩ : syracuseStep 512045 = 192017) (by norm_num)
theorem B413797 : Blo 223812 413797 := bbase (se 4 (by rfl) ⟨38793, by rfl⟩ : syracuseStep 413797 = 77587) (by norm_num)
theorem B381037 : Blo 223812 381037 := bbase (se 3 (by rfl) ⟨71444, by rfl⟩ : syracuseStep 381037 = 142889) (by norm_num)
theorem B512117 : Blo 223812 512117 := bbase (se 5 (by rfl) ⟨24005, by rfl⟩ : syracuseStep 512117 = 48011) (by norm_num)
theorem B2445461 : Blo 223812 2445461 := bbase (se 6 (by rfl) ⟨57315, by rfl⟩ : syracuseStep 2445461 = 114631) (by norm_num)
theorem B512189 : Blo 223812 512189 := bbase (se 3 (by rfl) ⟨96035, by rfl⟩ : syracuseStep 512189 = 192071) (by norm_num)
theorem B381125 : Blo 223812 381125 := bbase (se 4 (by rfl) ⟨35730, by rfl⟩ : syracuseStep 381125 = 71461) (by norm_num)
theorem B544973 : Blo 223812 544973 := bbase (se 3 (by rfl) ⟨102182, by rfl⟩ : syracuseStep 544973 = 204365) (by norm_num)
theorem B512261 : Blo 223812 512261 := bbase (se 4 (by rfl) ⟨48024, by rfl⟩ : syracuseStep 512261 = 96049) (by norm_num)
theorem B381253 : Blo 223812 381253 := bbase (se 4 (by rfl) ⟨35742, by rfl⟩ : syracuseStep 381253 = 71485) (by norm_num)
theorem B512333 : Blo 223812 512333 := bbase (se 3 (by rfl) ⟨96062, by rfl⟩ : syracuseStep 512333 = 192125) (by norm_num)
theorem B512405 : Blo 223812 512405 := bbase (se 6 (by rfl) ⟨12009, by rfl⟩ : syracuseStep 512405 = 24019) (by norm_num)
theorem B381341 : Blo 223812 381341 := bbase (se 3 (by rfl) ⟨71501, by rfl⟩ : syracuseStep 381341 = 143003) (by norm_num)
theorem B512477 : Blo 223812 512477 := bbase (se 3 (by rfl) ⟨96089, by rfl⟩ : syracuseStep 512477 = 192179) (by norm_num)
theorem B807413 : Blo 223812 807413 := bbase (se 5 (by rfl) ⟨37847, by rfl⟩ : syracuseStep 807413 = 75695) (by norm_num)
theorem B479773 : Blo 223812 479773 := bbase (se 3 (by rfl) ⟨89957, by rfl⟩ : syracuseStep 479773 = 179915) (by norm_num)
theorem B381469 : Blo 223812 381469 := bbase (se 3 (by rfl) ⟨71525, by rfl⟩ : syracuseStep 381469 = 143051) (by norm_num)
theorem B512549 : Blo 223812 512549 := bbase (se 4 (by rfl) ⟨48051, by rfl⟩ : syracuseStep 512549 = 96103) (by norm_num)
theorem B381557 : Blo 223812 381557 := bbase (se 5 (by rfl) ⟨17885, by rfl⟩ : syracuseStep 381557 = 35771) (by norm_num)
theorem B283277 : Blo 223812 283277 := bbase (se 3 (by rfl) ⟨53114, by rfl⟩ : syracuseStep 283277 = 106229) (by norm_num)
theorem B283333 : Blo 223812 283333 := bbase (se 4 (by rfl) ⟨26562, by rfl⟩ : syracuseStep 283333 = 53125) (by norm_num)
theorem B381685 : Blo 223812 381685 := bbase (se 5 (by rfl) ⟨17891, by rfl⟩ : syracuseStep 381685 = 35783) (by norm_num)
theorem B283429 : Blo 223812 283429 := bbase (se 4 (by rfl) ⟨26571, by rfl⟩ : syracuseStep 283429 = 53143) (by norm_num)
theorem B381773 : Blo 223812 381773 := bbase (se 3 (by rfl) ⟨71582, by rfl⟩ : syracuseStep 381773 = 143165) (by norm_num)
theorem B971669 : Blo 223812 971669 := bbase (se 6 (by rfl) ⟨22773, by rfl⟩ : syracuseStep 971669 = 45547) (by norm_num)
theorem B381901 : Blo 223812 381901 := bbase (se 3 (by rfl) ⟨71606, by rfl⟩ : syracuseStep 381901 = 143213) (by norm_num)
theorem B283601 : Blo 223812 283601 := bbase (se 2 (by rfl) ⟨106350, by rfl⟩ : syracuseStep 283601 = 212701) (by norm_num)
theorem B283657 : Blo 223812 283657 := bbase (se 2 (by rfl) ⟨106371, by rfl⟩ : syracuseStep 283657 = 212743) (by norm_num)
theorem B480269 : Blo 223812 480269 := bbase (se 3 (by rfl) ⟨90050, by rfl⟩ : syracuseStep 480269 = 180101) (by norm_num)
theorem B414733 : Blo 223812 414733 := bbase (se 3 (by rfl) ⟨77762, by rfl⟩ : syracuseStep 414733 = 155525) (by norm_num)
theorem B381989 : Blo 223812 381989 := bbase (se 4 (by rfl) ⟨35811, by rfl⟩ : syracuseStep 381989 = 71623) (by norm_num)
theorem B283753 : Blo 223812 283753 := bbase (se 2 (by rfl) ⟨106407, by rfl⟩ : syracuseStep 283753 = 212815) (by norm_num)
theorem B578669 : Blo 223812 578669 := bbase (se 3 (by rfl) ⟨108500, by rfl⟩ : syracuseStep 578669 = 217001) (by norm_num)
theorem B1135781 : Blo 223812 1135781 := bbase (se 4 (by rfl) ⟨106479, by rfl⟩ : syracuseStep 1135781 = 212959) (by norm_num)
theorem B382117 : Blo 223812 382117 := bbase (se 4 (by rfl) ⟨35823, by rfl⟩ : syracuseStep 382117 = 71647) (by norm_num)
theorem B382205 : Blo 223812 382205 := bbase (se 3 (by rfl) ⟨71663, by rfl⟩ : syracuseStep 382205 = 143327) (by norm_num)
theorem B283925 : Blo 223812 283925 := bbase (se 6 (by rfl) ⟨6654, by rfl⟩ : syracuseStep 283925 = 13309) (by norm_num)
theorem B283981 : Blo 223812 283981 := bbase (se 3 (by rfl) ⟨53246, by rfl⟩ : syracuseStep 283981 = 106493) (by norm_num)
theorem B382333 : Blo 223812 382333 := bbase (se 3 (by rfl) ⟨71687, by rfl⟩ : syracuseStep 382333 = 143375) (by norm_num)
theorem B284077 : Blo 223812 284077 := bbase (se 3 (by rfl) ⟨53264, by rfl⟩ : syracuseStep 284077 = 106529) (by norm_num)
theorem B382421 : Blo 223812 382421 := bbase (se 7 (by rfl) ⟨4481, by rfl⟩ : syracuseStep 382421 = 8963) (by norm_num)
theorem B874037 : Blo 223812 874037 := bbase (se 5 (by rfl) ⟨40970, by rfl⟩ : syracuseStep 874037 = 81941) (by norm_num)
theorem B382549 : Blo 223812 382549 := bbase (se 8 (by rfl) ⟨2241, by rfl⟩ : syracuseStep 382549 = 4483) (by norm_num)
theorem B284249 : Blo 223812 284249 := bbase (se 2 (by rfl) ⟨106593, by rfl⟩ : syracuseStep 284249 = 213187) (by norm_num)
theorem B284305 : Blo 223812 284305 := bbase (se 2 (by rfl) ⟨106614, by rfl⟩ : syracuseStep 284305 = 213229) (by norm_num)
theorem B382637 : Blo 223812 382637 := bbase (se 3 (by rfl) ⟨71744, by rfl⟩ : syracuseStep 382637 = 143489) (by norm_num)
theorem B284401 : Blo 223812 284401 := bbase (se 2 (by rfl) ⟨106650, by rfl⟩ : syracuseStep 284401 = 213301) (by norm_num)
theorem B415477 : Blo 223812 415477 := bbase (se 5 (by rfl) ⟨19475, by rfl⟩ : syracuseStep 415477 = 38951) (by norm_num)
theorem B382765 : Blo 223812 382765 := bbase (se 3 (by rfl) ⟨71768, by rfl⟩ : syracuseStep 382765 = 143537) (by norm_num)
theorem B481133 : Blo 223812 481133 := bbase (se 3 (by rfl) ⟨90212, by rfl⟩ : syracuseStep 481133 = 180425) (by norm_num)
theorem B382853 : Blo 223812 382853 := bbase (se 4 (by rfl) ⟨35892, by rfl⟩ : syracuseStep 382853 = 71785) (by norm_num)
theorem B251797 : Blo 223812 251797 := bbase (se 6 (by rfl) ⟨5901, by rfl⟩ : syracuseStep 251797 = 11803) (by norm_num)
theorem B284573 : Blo 223812 284573 := bbase (se 3 (by rfl) ⟨53357, by rfl⟩ : syracuseStep 284573 = 106715) (by norm_num)
theorem B645029 : Blo 223812 645029 := bbase (se 4 (by rfl) ⟨60471, by rfl⟩ : syracuseStep 645029 = 120943) (by norm_num)
theorem B251833 : Blo 223812 251833 := bbase (se 2 (by rfl) ⟨94437, by rfl⟩ : syracuseStep 251833 = 188875) (by norm_num)
theorem B1103813 : Blo 223812 1103813 := bbase (se 4 (by rfl) ⟨103482, by rfl⟩ : syracuseStep 1103813 = 206965) (by norm_num)
theorem B284629 : Blo 223812 284629 := bbase (se 7 (by rfl) ⟨3335, by rfl⟩ : syracuseStep 284629 = 6671) (by norm_num)
theorem B251869 : Blo 223812 251869 := bbase (se 3 (by rfl) ⟨47225, by rfl⟩ : syracuseStep 251869 = 94451) (by norm_num)
theorem B481277 : Blo 223812 481277 := bbase (se 3 (by rfl) ⟨90239, by rfl⟩ : syracuseStep 481277 = 180479) (by norm_num)
theorem B251905 : Blo 223812 251905 := bbase (se 2 (by rfl) ⟨94464, by rfl⟩ : syracuseStep 251905 = 188929) (by norm_num)
theorem B382981 : Blo 223812 382981 := bbase (se 4 (by rfl) ⟨35904, by rfl⟩ : syracuseStep 382981 = 71809) (by norm_num)
theorem B972805 : Blo 223812 972805 := bbase (se 4 (by rfl) ⟨91200, by rfl⟩ : syracuseStep 972805 = 182401) (by norm_num)
theorem B251941 : Blo 223812 251941 := bbase (se 4 (by rfl) ⟨23619, by rfl⟩ : syracuseStep 251941 = 47239) (by norm_num)
theorem B284725 : Blo 223812 284725 := bbase (se 5 (by rfl) ⟨13346, by rfl⟩ : syracuseStep 284725 = 26693) (by norm_num)
theorem B251977 : Blo 223812 251977 := bbase (se 2 (by rfl) ⟨94491, by rfl⟩ : syracuseStep 251977 = 188983) (by norm_num)
theorem B415829 : Blo 223812 415829 := bbase (se 8 (by rfl) ⟨2436, by rfl⟩ : syracuseStep 415829 = 4873) (by norm_num)
theorem B383069 : Blo 223812 383069 := bbase (se 3 (by rfl) ⟨71825, by rfl⟩ : syracuseStep 383069 = 143651) (by norm_num)
theorem B252013 : Blo 223812 252013 := bbase (se 3 (by rfl) ⟨47252, by rfl⟩ : syracuseStep 252013 = 94505) (by norm_num)
theorem B514181 : Blo 223812 514181 := bbase (se 4 (by rfl) ⟨48204, by rfl⟩ : syracuseStep 514181 = 96409) (by norm_num)
theorem B252049 : Blo 223812 252049 := bbase (se 2 (by rfl) ⟨94518, by rfl⟩ : syracuseStep 252049 = 189037) (by norm_num)
theorem B252085 : Blo 223812 252085 := bbase (se 5 (by rfl) ⟨11816, by rfl⟩ : syracuseStep 252085 = 23633) (by norm_num)
theorem B252121 : Blo 223812 252121 := bbase (se 2 (by rfl) ⟨94545, by rfl⟩ : syracuseStep 252121 = 189091) (by norm_num)
theorem B383197 : Blo 223812 383197 := bbase (se 3 (by rfl) ⟨71849, by rfl⟩ : syracuseStep 383197 = 143699) (by norm_num)
theorem B284897 : Blo 223812 284897 := bbase (se 2 (by rfl) ⟨106836, by rfl⟩ : syracuseStep 284897 = 213673) (by norm_num)
theorem B252157 : Blo 223812 252157 := bbase (se 3 (by rfl) ⟨47279, by rfl⟩ : syracuseStep 252157 = 94559) (by norm_num)
theorem B547069 : Blo 223812 547069 := bbase (se 3 (by rfl) ⟨102575, by rfl⟩ : syracuseStep 547069 = 205151) (by norm_num)
theorem B284953 : Blo 223812 284953 := bbase (se 2 (by rfl) ⟨106857, by rfl⟩ : syracuseStep 284953 = 213715) (by norm_num)
theorem B252193 : Blo 223812 252193 := bbase (se 2 (by rfl) ⟨94572, by rfl⟩ : syracuseStep 252193 = 189145) (by norm_num)
theorem B383285 : Blo 223812 383285 := bbase (se 5 (by rfl) ⟨17966, by rfl⟩ : syracuseStep 383285 = 35933) (by norm_num)
theorem B252229 : Blo 223812 252229 := bbase (se 4 (by rfl) ⟨23646, by rfl⟩ : syracuseStep 252229 = 47293) (by norm_num)
theorem B252265 : Blo 223812 252265 := bbase (se 2 (by rfl) ⟨94599, by rfl⟩ : syracuseStep 252265 = 189199) (by norm_num)
theorem B285049 : Blo 223812 285049 := bbase (se 2 (by rfl) ⟨106893, by rfl⟩ : syracuseStep 285049 = 213787) (by norm_num)
theorem B252301 : Blo 223812 252301 := bbase (se 3 (by rfl) ⟨47306, by rfl⟩ : syracuseStep 252301 = 94613) (by norm_num)
theorem B252337 : Blo 223812 252337 := bbase (se 2 (by rfl) ⟨94626, by rfl⟩ : syracuseStep 252337 = 189253) (by norm_num)
theorem B1137077 : Blo 223812 1137077 := bbase (se 5 (by rfl) ⟨53300, by rfl⟩ : syracuseStep 1137077 = 106601) (by norm_num)
theorem B383413 : Blo 223812 383413 := bbase (se 5 (by rfl) ⟨17972, by rfl⟩ : syracuseStep 383413 = 35945) (by norm_num)
theorem B252373 : Blo 223812 252373 := bbase (se 7 (by rfl) ⟨2957, by rfl⟩ : syracuseStep 252373 = 5915) (by norm_num)
theorem B252409 : Blo 223812 252409 := bbase (se 2 (by rfl) ⟨94653, by rfl⟩ : syracuseStep 252409 = 189307) (by norm_num)
theorem B383501 : Blo 223812 383501 := bbase (se 3 (by rfl) ⟨71906, by rfl⟩ : syracuseStep 383501 = 143813) (by norm_num)
theorem B1628693 : Blo 223812 1628693 := bbase (se 6 (by rfl) ⟨38172, by rfl⟩ : syracuseStep 1628693 = 76345) (by norm_num)
theorem B252445 : Blo 223812 252445 := bbase (se 3 (by rfl) ⟨47333, by rfl⟩ : syracuseStep 252445 = 94667) (by norm_num)
theorem B285221 : Blo 223812 285221 := bbase (se 4 (by rfl) ⟨26739, by rfl⟩ : syracuseStep 285221 = 53479) (by norm_num)
theorem B252481 : Blo 223812 252481 := bbase (se 2 (by rfl) ⟨94680, by rfl⟩ : syracuseStep 252481 = 189361) (by norm_num)
theorem B285277 : Blo 223812 285277 := bbase (se 3 (by rfl) ⟨53489, by rfl⟩ : syracuseStep 285277 = 106979) (by norm_num)
theorem B252517 : Blo 223812 252517 := bbase (se 4 (by rfl) ⟨23673, by rfl⟩ : syracuseStep 252517 = 47347) (by norm_num)
theorem B252553 : Blo 223812 252553 := bbase (se 2 (by rfl) ⟨94707, by rfl⟩ : syracuseStep 252553 = 189415) (by norm_num)
theorem B383629 : Blo 223812 383629 := bbase (se 3 (by rfl) ⟨71930, by rfl⟩ : syracuseStep 383629 = 143861) (by norm_num)
theorem B252589 : Blo 223812 252589 := bbase (se 3 (by rfl) ⟨47360, by rfl⟩ : syracuseStep 252589 = 94721) (by norm_num)
theorem B285373 : Blo 223812 285373 := bbase (se 3 (by rfl) ⟨53507, by rfl⟩ : syracuseStep 285373 = 107015) (by norm_num)
theorem B252625 : Blo 223812 252625 := bbase (se 2 (by rfl) ⟨94734, by rfl⟩ : syracuseStep 252625 = 189469) (by norm_num)
theorem B482021 : Blo 223812 482021 := bbase (se 4 (by rfl) ⟨45189, by rfl⟩ : syracuseStep 482021 = 90379) (by norm_num)
theorem B383717 : Blo 223812 383717 := bbase (se 4 (by rfl) ⟨35973, by rfl⟩ : syracuseStep 383717 = 71947) (by norm_num)
theorem B252661 : Blo 223812 252661 := bbase (se 5 (by rfl) ⟨11843, by rfl⟩ : syracuseStep 252661 = 23687) (by norm_num)
theorem B875269 : Blo 223812 875269 := bbase (se 4 (by rfl) ⟨82056, by rfl⟩ : syracuseStep 875269 = 164113) (by norm_num)
theorem B252697 : Blo 223812 252697 := bbase (se 2 (by rfl) ⟨94761, by rfl⟩ : syracuseStep 252697 = 189523) (by norm_num)
theorem B252733 : Blo 223812 252733 := bbase (se 3 (by rfl) ⟨47387, by rfl⟩ : syracuseStep 252733 = 94775) (by norm_num)
theorem B252769 : Blo 223812 252769 := bbase (se 2 (by rfl) ⟨94788, by rfl⟩ : syracuseStep 252769 = 189577) (by norm_num)
theorem B383845 : Blo 223812 383845 := bbase (se 4 (by rfl) ⟨35985, by rfl⟩ : syracuseStep 383845 = 71971) (by norm_num)
theorem B285545 : Blo 223812 285545 := bbase (se 2 (by rfl) ⟨107079, by rfl⟩ : syracuseStep 285545 = 214159) (by norm_num)
theorem B252805 : Blo 223812 252805 := bbase (se 4 (by rfl) ⟨23700, by rfl⟩ : syracuseStep 252805 = 47401) (by norm_num)
theorem B547733 : Blo 223812 547733 := bbase (se 6 (by rfl) ⟨12837, by rfl⟩ : syracuseStep 547733 = 25675) (by norm_num)
theorem B285601 : Blo 223812 285601 := bbase (se 2 (by rfl) ⟨107100, by rfl⟩ : syracuseStep 285601 = 214201) (by norm_num)
theorem B252841 : Blo 223812 252841 := bbase (se 2 (by rfl) ⟨94815, by rfl⟩ : syracuseStep 252841 = 189631) (by norm_num)
theorem B809909 : Blo 223812 809909 := bbase (se 5 (by rfl) ⟨37964, by rfl⟩ : syracuseStep 809909 = 75929) (by norm_num)
theorem B383933 : Blo 223812 383933 := bbase (se 3 (by rfl) ⟨71987, by rfl⟩ : syracuseStep 383933 = 143975) (by norm_num)
theorem B252877 : Blo 223812 252877 := bbase (se 3 (by rfl) ⟨47414, by rfl⟩ : syracuseStep 252877 = 94829) (by norm_num)
theorem B252913 : Blo 223812 252913 := bbase (se 2 (by rfl) ⟨94842, by rfl⟩ : syracuseStep 252913 = 189685) (by norm_num)
theorem B285697 : Blo 223812 285697 := bbase (se 2 (by rfl) ⟨107136, by rfl⟩ : syracuseStep 285697 = 214273) (by norm_num)
theorem B252949 : Blo 223812 252949 := bbase (se 6 (by rfl) ⟨5928, by rfl⟩ : syracuseStep 252949 = 11857) (by norm_num)
theorem B1956917 : Blo 223812 1956917 := bbase (se 5 (by rfl) ⟨91730, by rfl⟩ : syracuseStep 1956917 = 183461) (by norm_num)
theorem B252985 : Blo 223812 252985 := bbase (se 2 (by rfl) ⟨94869, by rfl⟩ : syracuseStep 252985 = 189739) (by norm_num)
theorem B384061 : Blo 223812 384061 := bbase (se 3 (by rfl) ⟨72011, by rfl⟩ : syracuseStep 384061 = 144023) (by norm_num)
theorem B646213 : Blo 223812 646213 := bbase (se 4 (by rfl) ⟨60582, by rfl⟩ : syracuseStep 646213 = 121165) (by norm_num)
theorem B253021 : Blo 223812 253021 := bbase (se 3 (by rfl) ⟨47441, by rfl⟩ : syracuseStep 253021 = 94883) (by norm_num)
theorem B580733 : Blo 223812 580733 := bbase (se 3 (by rfl) ⟨108887, by rfl⟩ : syracuseStep 580733 = 217775) (by norm_num)
theorem B253057 : Blo 223812 253057 := bbase (se 2 (by rfl) ⟨94896, by rfl⟩ : syracuseStep 253057 = 189793) (by norm_num)
theorem B384149 : Blo 223812 384149 := bbase (se 6 (by rfl) ⟨9003, by rfl⟩ : syracuseStep 384149 = 18007) (by norm_num)
theorem B253093 : Blo 223812 253093 := bbase (se 4 (by rfl) ⟨23727, by rfl⟩ : syracuseStep 253093 = 47455) (by norm_num)
theorem B285869 : Blo 223812 285869 := bbase (se 3 (by rfl) ⟨53600, by rfl⟩ : syracuseStep 285869 = 107201) (by norm_num)
theorem B253129 : Blo 223812 253129 := bbase (se 2 (by rfl) ⟨94923, by rfl⟩ : syracuseStep 253129 = 189847) (by norm_num)
theorem B285925 : Blo 223812 285925 := bbase (se 4 (by rfl) ⟨26805, by rfl⟩ : syracuseStep 285925 = 53611) (by norm_num)
theorem B646373 : Blo 223812 646373 := bbase (se 4 (by rfl) ⟨60597, by rfl⟩ : syracuseStep 646373 = 121195) (by norm_num)
theorem B253165 : Blo 223812 253165 := bbase (se 3 (by rfl) ⟨47468, by rfl⟩ : syracuseStep 253165 = 94937) (by norm_num)
theorem B253201 : Blo 223812 253201 := bbase (se 2 (by rfl) ⟨94950, by rfl⟩ : syracuseStep 253201 = 189901) (by norm_num)
theorem B384277 : Blo 223812 384277 := bbase (se 6 (by rfl) ⟨9006, by rfl⟩ : syracuseStep 384277 = 18013) (by norm_num)
theorem B253237 : Blo 223812 253237 := bbase (se 5 (by rfl) ⟨11870, by rfl⟩ : syracuseStep 253237 = 23741) (by norm_num)
theorem B286021 : Blo 223812 286021 := bbase (se 4 (by rfl) ⟨26814, by rfl⟩ : syracuseStep 286021 = 53629) (by norm_num)
theorem B253273 : Blo 223812 253273 := bbase (se 2 (by rfl) ⟨94977, by rfl⟩ : syracuseStep 253273 = 189955) (by norm_num)
theorem B384365 : Blo 223812 384365 := bbase (se 3 (by rfl) ⟨72068, by rfl⟩ : syracuseStep 384365 = 144137) (by norm_num)
theorem B253309 : Blo 223812 253309 := bbase (se 3 (by rfl) ⟨47495, by rfl⟩ : syracuseStep 253309 = 94991) (by norm_num)
theorem B253345 : Blo 223812 253345 := bbase (se 2 (by rfl) ⟨95004, by rfl⟩ : syracuseStep 253345 = 190009) (by norm_num)
theorem B1564085 : Blo 223812 1564085 := bbase (se 5 (by rfl) ⟨73316, by rfl⟩ : syracuseStep 1564085 = 146633) (by norm_num)
theorem B253381 : Blo 223812 253381 := bbase (se 4 (by rfl) ⟨23754, by rfl⟩ : syracuseStep 253381 = 47509) (by norm_num)
theorem B482773 : Blo 223812 482773 := bbase (se 7 (by rfl) ⟨5657, by rfl⟩ : syracuseStep 482773 = 11315) (by norm_num)
theorem B646613 : Blo 223812 646613 := bbase (se 7 (by rfl) ⟨7577, by rfl⟩ : syracuseStep 646613 = 15155) (by norm_num)
theorem B777701 : Blo 223812 777701 := bbase (se 4 (by rfl) ⟨72909, by rfl⟩ : syracuseStep 777701 = 145819) (by norm_num)
theorem B253417 : Blo 223812 253417 := bbase (se 2 (by rfl) ⟨95031, by rfl⟩ : syracuseStep 253417 = 190063) (by norm_num)
theorem B286193 : Blo 223812 286193 := bbase (se 2 (by rfl) ⟨107322, by rfl⟩ : syracuseStep 286193 = 214645) (by norm_num)
theorem B810485 : Blo 223812 810485 := bbase (se 5 (by rfl) ⟨37991, by rfl⟩ : syracuseStep 810485 = 75983) (by norm_num)
theorem B253453 : Blo 223812 253453 := bbase (se 3 (by rfl) ⟨47522, by rfl⟩ : syracuseStep 253453 = 95045) (by norm_num)
theorem B286249 : Blo 223812 286249 := bbase (se 2 (by rfl) ⟨107343, by rfl⟩ : syracuseStep 286249 = 214687) (by norm_num)
theorem B253489 : Blo 223812 253489 := bbase (se 2 (by rfl) ⟨95058, by rfl⟩ : syracuseStep 253489 = 190117) (by norm_num)
theorem B253525 : Blo 223812 253525 := bbase (se 8 (by rfl) ⟨1485, by rfl⟩ : syracuseStep 253525 = 2971) (by norm_num)
theorem B319069 : Blo 223812 319069 := bbase (se 3 (by rfl) ⟨59825, by rfl⟩ : syracuseStep 319069 = 119651) (by norm_num)
theorem B482917 : Blo 223812 482917 := bbase (se 4 (by rfl) ⟨45273, by rfl⟩ : syracuseStep 482917 = 90547) (by norm_num)
theorem B2252405 : Blo 223812 2252405 := bbase (se 5 (by rfl) ⟨105581, by rfl⟩ : syracuseStep 2252405 = 211163) (by norm_num)
theorem B253561 : Blo 223812 253561 := bbase (se 2 (by rfl) ⟨95085, by rfl⟩ : syracuseStep 253561 = 190171) (by norm_num)
theorem B286345 : Blo 223812 286345 := bbase (se 2 (by rfl) ⟨107379, by rfl⟩ : syracuseStep 286345 = 214759) (by norm_num)
theorem B646805 : Blo 223812 646805 := bbase (se 6 (by rfl) ⟨15159, by rfl⟩ : syracuseStep 646805 = 30319) (by norm_num)
theorem B253597 : Blo 223812 253597 := bbase (se 3 (by rfl) ⟨47549, by rfl⟩ : syracuseStep 253597 = 95099) (by norm_num)
theorem B614069 : Blo 223812 614069 := bbase (se 5 (by rfl) ⟨28784, by rfl⟩ : syracuseStep 614069 = 57569) (by norm_num)
theorem B253633 : Blo 223812 253633 := bbase (se 2 (by rfl) ⟨95112, by rfl⟩ : syracuseStep 253633 = 190225) (by norm_num)
theorem B1138373 : Blo 223812 1138373 := bbase (se 4 (by rfl) ⟨106722, by rfl⟩ : syracuseStep 1138373 = 213445) (by norm_num)
theorem B253669 : Blo 223812 253669 := bbase (se 4 (by rfl) ⟨23781, by rfl⟩ : syracuseStep 253669 = 47563) (by norm_num)
theorem B253705 : Blo 223812 253705 := bbase (se 2 (by rfl) ⟨95139, by rfl⟩ : syracuseStep 253705 = 190279) (by norm_num)
theorem B253741 : Blo 223812 253741 := bbase (se 3 (by rfl) ⟨47576, by rfl⟩ : syracuseStep 253741 = 95153) (by norm_num)
theorem B286517 : Blo 223812 286517 := bbase (se 5 (by rfl) ⟨13430, by rfl⟩ : syracuseStep 286517 = 26861) (by norm_num)
theorem B548669 : Blo 223812 548669 := bbase (se 3 (by rfl) ⟨102875, by rfl⟩ : syracuseStep 548669 = 205751) (by norm_num)
theorem B253777 : Blo 223812 253777 := bbase (se 2 (by rfl) ⟨95166, by rfl⟩ : syracuseStep 253777 = 190333) (by norm_num)
theorem B286573 : Blo 223812 286573 := bbase (se 3 (by rfl) ⟨53732, by rfl⟩ : syracuseStep 286573 = 107465) (by norm_num)
theorem B253813 : Blo 223812 253813 := bbase (se 5 (by rfl) ⟨11897, by rfl⟩ : syracuseStep 253813 = 23795) (by norm_num)
theorem B253849 : Blo 223812 253849 := bbase (se 2 (by rfl) ⟨95193, by rfl⟩ : syracuseStep 253849 = 190387) (by norm_num)
theorem B810917 : Blo 223812 810917 := bbase (se 4 (by rfl) ⟨76023, by rfl⟩ : syracuseStep 810917 = 152047) (by norm_num)
theorem B319405 : Blo 223812 319405 := bbase (se 3 (by rfl) ⟨59888, by rfl⟩ : syracuseStep 319405 = 119777) (by norm_num)
theorem B253885 : Blo 223812 253885 := bbase (se 3 (by rfl) ⟨47603, by rfl⟩ : syracuseStep 253885 = 95207) (by norm_num)
theorem B286669 : Blo 223812 286669 := bbase (se 3 (by rfl) ⟨53750, by rfl⟩ : syracuseStep 286669 = 107501) (by norm_num)
theorem B483293 : Blo 223812 483293 := bbase (se 3 (by rfl) ⟨90617, by rfl⟩ : syracuseStep 483293 = 181235) (by norm_num)
theorem B253921 : Blo 223812 253921 := bbase (se 2 (by rfl) ⟨95220, by rfl⟩ : syracuseStep 253921 = 190441) (by norm_num)
theorem B253957 : Blo 223812 253957 := bbase (se 4 (by rfl) ⟨23808, by rfl⟩ : syracuseStep 253957 = 47617) (by norm_num)
theorem B253993 : Blo 223812 253993 := bbase (se 2 (by rfl) ⟨95247, by rfl⟩ : syracuseStep 253993 = 190495) (by norm_num)
theorem B254029 : Blo 223812 254029 := bbase (se 3 (by rfl) ⟨47630, by rfl⟩ : syracuseStep 254029 = 95261) (by norm_num)
theorem B254065 : Blo 223812 254065 := bbase (se 2 (by rfl) ⟨95274, by rfl⟩ : syracuseStep 254065 = 190549) (by norm_num)
theorem B286841 : Blo 223812 286841 := bbase (se 2 (by rfl) ⟨107565, by rfl⟩ : syracuseStep 286841 = 215131) (by norm_num)
theorem B319621 : Blo 223812 319621 := bbase (se 4 (by rfl) ⟨29964, by rfl⟩ : syracuseStep 319621 = 59929) (by norm_num)
theorem B647317 : Blo 223812 647317 := bbase (se 6 (by rfl) ⟨15171, by rfl⟩ : syracuseStep 647317 = 30343) (by norm_num)
theorem B254101 : Blo 223812 254101 := bbase (se 6 (by rfl) ⟨5955, by rfl⟩ : syracuseStep 254101 = 11911) (by norm_num)
theorem B286897 : Blo 223812 286897 := bbase (se 2 (by rfl) ⟨107586, by rfl⟩ : syracuseStep 286897 = 215173) (by norm_num)
theorem B254137 : Blo 223812 254137 := bbase (se 2 (by rfl) ⟨95301, by rfl⟩ : syracuseStep 254137 = 190603) (by norm_num)
theorem B254173 : Blo 223812 254173 := bbase (se 3 (by rfl) ⟨47657, by rfl⟩ : syracuseStep 254173 = 95315) (by norm_num)
theorem B254209 : Blo 223812 254209 := bbase (se 2 (by rfl) ⟨95328, by rfl⟩ : syracuseStep 254209 = 190657) (by norm_num)
theorem B286993 : Blo 223812 286993 := bbase (se 2 (by rfl) ⟨107622, by rfl⟩ : syracuseStep 286993 = 215245) (by norm_num)
theorem B254245 : Blo 223812 254245 := bbase (se 4 (by rfl) ⟨23835, by rfl⟩ : syracuseStep 254245 = 47671) (by norm_num)
theorem B254281 : Blo 223812 254281 := bbase (se 2 (by rfl) ⟨95355, by rfl⟩ : syracuseStep 254281 = 190711) (by norm_num)
theorem B483661 : Blo 223812 483661 := bbase (se 3 (by rfl) ⟨90686, by rfl⟩ : syracuseStep 483661 = 181373) (by norm_num)
theorem B254317 : Blo 223812 254317 := bbase (se 3 (by rfl) ⟨47684, by rfl⟩ : syracuseStep 254317 = 95369) (by norm_num)
theorem B254353 : Blo 223812 254353 := bbase (se 2 (by rfl) ⟨95382, by rfl⟩ : syracuseStep 254353 = 190765) (by norm_num)
theorem B254389 : Blo 223812 254389 := bbase (se 5 (by rfl) ⟨11924, by rfl⟩ : syracuseStep 254389 = 23849) (by norm_num)
theorem B287165 : Blo 223812 287165 := bbase (se 3 (by rfl) ⟨53843, by rfl⟩ : syracuseStep 287165 = 107687) (by norm_num)
theorem B647621 : Blo 223812 647621 := bbase (se 4 (by rfl) ⟨60714, by rfl⟩ : syracuseStep 647621 = 121429) (by norm_num)
theorem B254425 : Blo 223812 254425 := bbase (se 2 (by rfl) ⟨95409, by rfl⟩ : syracuseStep 254425 = 190819) (by norm_num)
theorem B287221 : Blo 223812 287221 := bbase (se 5 (by rfl) ⟨13463, by rfl⟩ : syracuseStep 287221 = 26927) (by norm_num)
theorem B319997 : Blo 223812 319997 := bbase (se 3 (by rfl) ⟨59999, by rfl⟩ : syracuseStep 319997 = 119999) (by norm_num)
theorem B254461 : Blo 223812 254461 := bbase (se 3 (by rfl) ⟨47711, by rfl⟩ : syracuseStep 254461 = 95423) (by norm_num)
theorem B1925653 : Blo 223812 1925653 := bbase (se 6 (by rfl) ⟨45132, by rfl⟩ : syracuseStep 1925653 = 90265) (by norm_num)
theorem B254497 : Blo 223812 254497 := bbase (se 2 (by rfl) ⟨95436, by rfl⟩ : syracuseStep 254497 = 190873) (by norm_num)
theorem B549413 : Blo 223812 549413 := bbase (se 4 (by rfl) ⟨51507, by rfl⟩ : syracuseStep 549413 = 103015) (by norm_num)
theorem B254533 : Blo 223812 254533 := bbase (se 4 (by rfl) ⟨23862, by rfl⟩ : syracuseStep 254533 = 47725) (by norm_num)
theorem B287317 : Blo 223812 287317 := bbase (se 8 (by rfl) ⟨1683, by rfl⟩ : syracuseStep 287317 = 3367) (by norm_num)
theorem B254569 : Blo 223812 254569 := bbase (se 2 (by rfl) ⟨95463, by rfl⟩ : syracuseStep 254569 = 190927) (by norm_num)
theorem B647797 : Blo 223812 647797 := bbase (se 5 (by rfl) ⟨30365, by rfl⟩ : syracuseStep 647797 = 60731) (by norm_num)
theorem B254605 : Blo 223812 254605 := bbase (se 3 (by rfl) ⟨47738, by rfl⟩ : syracuseStep 254605 = 95477) (by norm_num)
theorem B254641 : Blo 223812 254641 := bbase (se 2 (by rfl) ⟨95490, by rfl⟩ : syracuseStep 254641 = 190981) (by norm_num)
theorem B254677 : Blo 223812 254677 := bbase (se 7 (by rfl) ⟨2984, by rfl⟩ : syracuseStep 254677 = 5969) (by norm_num)
theorem B254713 : Blo 223812 254713 := bbase (se 2 (by rfl) ⟨95517, by rfl⟩ : syracuseStep 254713 = 191035) (by norm_num)
theorem B287489 : Blo 223812 287489 := bbase (se 2 (by rfl) ⟨107808, by rfl⟩ : syracuseStep 287489 = 215617) (by norm_num)
theorem B254749 : Blo 223812 254749 := bbase (se 3 (by rfl) ⟨47765, by rfl⟩ : syracuseStep 254749 = 95531) (by norm_num)
theorem B287545 : Blo 223812 287545 := bbase (se 2 (by rfl) ⟨107829, by rfl⟩ : syracuseStep 287545 = 215659) (by norm_num)
theorem B254785 : Blo 223812 254785 := bbase (se 2 (by rfl) ⟨95544, by rfl⟩ : syracuseStep 254785 = 191089) (by norm_num)
theorem B254821 : Blo 223812 254821 := bbase (se 4 (by rfl) ⟨23889, by rfl⟩ : syracuseStep 254821 = 47779) (by norm_num)
theorem B254857 : Blo 223812 254857 := bbase (se 2 (by rfl) ⟨95571, by rfl⟩ : syracuseStep 254857 = 191143) (by norm_num)
theorem B287641 : Blo 223812 287641 := bbase (se 2 (by rfl) ⟨107865, by rfl⟩ : syracuseStep 287641 = 215731) (by norm_num)
theorem B254893 : Blo 223812 254893 := bbase (se 3 (by rfl) ⟨47792, by rfl⟩ : syracuseStep 254893 = 95585) (by norm_num)
theorem B254929 : Blo 223812 254929 := bbase (se 2 (by rfl) ⟨95598, by rfl⟩ : syracuseStep 254929 = 191197) (by norm_num)
theorem B1434581 : Blo 223812 1434581 := bbase (se 7 (by rfl) ⟨16811, by rfl⟩ : syracuseStep 1434581 = 33623) (by norm_num)
theorem B1139669 : Blo 223812 1139669 := bbase (se 7 (by rfl) ⟨13355, by rfl⟩ : syracuseStep 1139669 = 26711) (by norm_num)
theorem B254965 : Blo 223812 254965 := bbase (se 5 (by rfl) ⟨11951, by rfl⟩ : syracuseStep 254965 = 23903) (by norm_num)
theorem B2057237 : Blo 223812 2057237 := bbase (se 6 (by rfl) ⟨48216, by rfl⟩ : syracuseStep 2057237 = 96433) (by norm_num)
theorem B255001 : Blo 223812 255001 := bbase (se 2 (by rfl) ⟨95625, by rfl⟩ : syracuseStep 255001 = 191251) (by norm_num)
theorem B255037 : Blo 223812 255037 := bbase (se 3 (by rfl) ⟨47819, by rfl⟩ : syracuseStep 255037 = 95639) (by norm_num)
theorem B287813 : Blo 223812 287813 := bbase (se 4 (by rfl) ⟨26982, by rfl⟩ : syracuseStep 287813 = 53965) (by norm_num)
theorem B255073 : Blo 223812 255073 := bbase (se 2 (by rfl) ⟨95652, by rfl⟩ : syracuseStep 255073 = 191305) (by norm_num)
theorem B517229 : Blo 223812 517229 := bbase (se 3 (by rfl) ⟨96980, by rfl⟩ : syracuseStep 517229 = 193961) (by norm_num)
theorem B287869 : Blo 223812 287869 := bbase (se 3 (by rfl) ⟨53975, by rfl⟩ : syracuseStep 287869 = 107951) (by norm_num)
theorem B255109 : Blo 223812 255109 := bbase (se 4 (by rfl) ⟨23916, by rfl⟩ : syracuseStep 255109 = 47833) (by norm_num)
theorem B255145 : Blo 223812 255145 := bbase (se 2 (by rfl) ⟨95679, by rfl⟩ : syracuseStep 255145 = 191359) (by norm_num)
theorem B255181 : Blo 223812 255181 := bbase (se 3 (by rfl) ⟨47846, by rfl⟩ : syracuseStep 255181 = 95693) (by norm_num)
theorem B287965 : Blo 223812 287965 := bbase (se 3 (by rfl) ⟨53993, by rfl⟩ : syracuseStep 287965 = 107987) (by norm_num)
theorem B255217 : Blo 223812 255217 := bbase (se 2 (by rfl) ⟨95706, by rfl⟩ : syracuseStep 255217 = 191413) (by norm_num)
theorem B550141 : Blo 223812 550141 := bbase (se 3 (by rfl) ⟨103151, by rfl⟩ : syracuseStep 550141 = 206303) (by norm_num)
theorem B255253 : Blo 223812 255253 := bbase (se 6 (by rfl) ⟨5982, by rfl⟩ : syracuseStep 255253 = 11965) (by norm_num)
theorem B255289 : Blo 223812 255289 := bbase (se 2 (by rfl) ⟨95733, by rfl⟩ : syracuseStep 255289 = 191467) (by norm_num)
theorem B255325 : Blo 223812 255325 := bbase (se 3 (by rfl) ⟨47873, by rfl⟩ : syracuseStep 255325 = 95747) (by norm_num)
theorem B255361 : Blo 223812 255361 := bbase (se 2 (by rfl) ⟨95760, by rfl⟩ : syracuseStep 255361 = 191521) (by norm_num)
theorem B288137 : Blo 223812 288137 := bbase (se 2 (by rfl) ⟨108051, by rfl⟩ : syracuseStep 288137 = 216103) (by norm_num)
theorem B681365 : Blo 223812 681365 := bbase (se 6 (by rfl) ⟨15969, by rfl⟩ : syracuseStep 681365 = 31939) (by norm_num)
theorem B255397 : Blo 223812 255397 := bbase (se 4 (by rfl) ⟨23943, by rfl⟩ : syracuseStep 255397 = 47887) (by norm_num)
theorem B255421 : Blo 223812 255421 := bbase (se 3 (by rfl) ⟨47891, by rfl⟩ : syracuseStep 255421 = 95783) (by norm_num)
theorem B288193 : Blo 223812 288193 := bbase (se 2 (by rfl) ⟨108072, by rfl⟩ : syracuseStep 288193 = 216145) (by norm_num)
theorem B255433 : Blo 223812 255433 := bbase (se 2 (by rfl) ⟨95787, by rfl⟩ : syracuseStep 255433 = 191575) (by norm_num)
theorem B255469 : Blo 223812 255469 := bbase (se 3 (by rfl) ⟨47900, by rfl⟩ : syracuseStep 255469 = 95801) (by norm_num)
theorem B255505 : Blo 223812 255505 := bbase (se 2 (by rfl) ⟨95814, by rfl⟩ : syracuseStep 255505 = 191629) (by norm_num)
theorem B288289 : Blo 223812 288289 := bbase (se 2 (by rfl) ⟨108108, by rfl⟩ : syracuseStep 288289 = 216217) (by norm_num)
theorem B255541 : Blo 223812 255541 := bbase (se 5 (by rfl) ⟨11978, by rfl⟩ : syracuseStep 255541 = 23957) (by norm_num)
theorem B386621 : Blo 223812 386621 := bbase (se 3 (by rfl) ⟨72491, by rfl⟩ : syracuseStep 386621 = 144983) (by norm_num)
theorem B255577 : Blo 223812 255577 := bbase (se 2 (by rfl) ⟨95841, by rfl⟩ : syracuseStep 255577 = 191683) (by norm_num)
theorem B255613 : Blo 223812 255613 := bbase (se 3 (by rfl) ⟨47927, by rfl⟩ : syracuseStep 255613 = 95855) (by norm_num)
theorem B255649 : Blo 223812 255649 := bbase (se 2 (by rfl) ⟨95868, by rfl⟩ : syracuseStep 255649 = 191737) (by norm_num)
theorem B255685 : Blo 223812 255685 := bbase (se 4 (by rfl) ⟨23970, by rfl⟩ : syracuseStep 255685 = 47941) (by norm_num)
theorem B255721 : Blo 223812 255721 := bbase (se 2 (by rfl) ⟨95895, by rfl⟩ : syracuseStep 255721 = 191791) (by norm_num)
theorem B255757 : Blo 223812 255757 := bbase (se 3 (by rfl) ⟨47954, by rfl⟩ : syracuseStep 255757 = 95909) (by norm_num)
theorem B485165 : Blo 223812 485165 := bbase (se 3 (by rfl) ⟨90968, by rfl⟩ : syracuseStep 485165 = 181937) (by norm_num)
theorem B255793 : Blo 223812 255793 := bbase (se 2 (by rfl) ⟨95922, by rfl⟩ : syracuseStep 255793 = 191845) (by norm_num)
theorem B255829 : Blo 223812 255829 := bbase (se 9 (by rfl) ⟨749, by rfl⟩ : syracuseStep 255829 = 1499) (by norm_num)
theorem B255865 : Blo 223812 255865 := bbase (se 2 (by rfl) ⟨95949, by rfl⟩ : syracuseStep 255865 = 191899) (by norm_num)
theorem B321421 : Blo 223812 321421 := bbase (se 3 (by rfl) ⟨60266, by rfl⟩ : syracuseStep 321421 = 120533) (by norm_num)
theorem B255901 : Blo 223812 255901 := bbase (se 3 (by rfl) ⟨47981, by rfl⟩ : syracuseStep 255901 = 95963) (by norm_num)
theorem B485309 : Blo 223812 485309 := bbase (se 3 (by rfl) ⟨90995, by rfl⟩ : syracuseStep 485309 = 181991) (by norm_num)
theorem B255937 : Blo 223812 255937 := bbase (se 2 (by rfl) ⟨95976, by rfl⟩ : syracuseStep 255937 = 191953) (by norm_num)
theorem B4319189 : Blo 223812 4319189 := bbase (se 7 (by rfl) ⟨50615, by rfl⟩ : syracuseStep 4319189 = 101231) (by norm_num)
theorem B255973 : Blo 223812 255973 := bbase (se 4 (by rfl) ⟨23997, by rfl⟩ : syracuseStep 255973 = 47995) (by norm_num)
theorem B256009 : Blo 223812 256009 := bbase (se 2 (by rfl) ⟨96003, by rfl⟩ : syracuseStep 256009 = 192007) (by norm_num)
theorem B256045 : Blo 223812 256045 := bbase (se 3 (by rfl) ⟨48008, by rfl⟩ : syracuseStep 256045 = 96017) (by norm_num)
theorem B256081 : Blo 223812 256081 := bbase (se 2 (by rfl) ⟨96030, by rfl⟩ : syracuseStep 256081 = 192061) (by norm_num)
theorem B256117 : Blo 223812 256117 := bbase (se 5 (by rfl) ⟨12005, by rfl⟩ : syracuseStep 256117 = 24011) (by norm_num)
theorem B2189429 : Blo 223812 2189429 := bbase (se 5 (by rfl) ⟨102629, by rfl⟩ : syracuseStep 2189429 = 205259) (by norm_num)
theorem B256153 : Blo 223812 256153 := bbase (se 2 (by rfl) ⟨96057, by rfl⟩ : syracuseStep 256153 = 192115) (by norm_num)
theorem B256189 : Blo 223812 256189 := bbase (se 3 (by rfl) ⟨48035, by rfl⟩ : syracuseStep 256189 = 96071) (by norm_num)
theorem B256225 : Blo 223812 256225 := bbase (se 2 (by rfl) ⟨96084, by rfl⟩ : syracuseStep 256225 = 192169) (by norm_num)
theorem B1140965 : Blo 223812 1140965 := bbase (se 4 (by rfl) ⟨106965, by rfl⟩ : syracuseStep 1140965 = 213931) (by norm_num)
theorem B256261 : Blo 223812 256261 := bbase (se 4 (by rfl) ⟨24024, by rfl⟩ : syracuseStep 256261 = 48049) (by norm_num)
theorem B485669 : Blo 223812 485669 := bbase (se 4 (by rfl) ⟨45531, by rfl⟩ : syracuseStep 485669 = 91063) (by norm_num)
theorem B256297 : Blo 223812 256297 := bbase (se 2 (by rfl) ⟨96111, by rfl⟩ : syracuseStep 256297 = 192223) (by norm_num)
theorem B616837 : Blo 223812 616837 := bbase (se 4 (by rfl) ⟨57828, by rfl⟩ : syracuseStep 616837 = 115657) (by norm_num)
theorem B1304981 : Blo 223812 1304981 := bbase (se 6 (by rfl) ⟨30585, by rfl⟩ : syracuseStep 1304981 = 61171) (by norm_num)
theorem B1927637 : Blo 223812 1927637 := bbase (se 7 (by rfl) ⟨22589, by rfl⟩ : syracuseStep 1927637 = 45179) (by norm_num)
theorem B322013 : Blo 223812 322013 := bbase (se 3 (by rfl) ⟨60377, by rfl⟩ : syracuseStep 322013 = 120755) (by norm_num)
theorem B256493 : Blo 223812 256493 := bbase (se 3 (by rfl) ⟨48092, by rfl⟩ : syracuseStep 256493 = 96185) (by norm_num)
theorem B322093 : Blo 223812 322093 := bbase (se 3 (by rfl) ⟨60392, by rfl⟩ : syracuseStep 322093 = 120785) (by norm_num)
theorem B813685 : Blo 223812 813685 := bbase (se 5 (by rfl) ⟨38141, by rfl⟩ : syracuseStep 813685 = 76283) (by norm_num)
theorem B322213 : Blo 223812 322213 := bbase (se 4 (by rfl) ⟨30207, by rfl⟩ : syracuseStep 322213 = 60415) (by norm_num)
theorem B322309 : Blo 223812 322309 := bbase (se 4 (by rfl) ⟨30216, by rfl⟩ : syracuseStep 322309 = 60433) (by norm_num)
theorem B256789 : Blo 223812 256789 := bbase (se 6 (by rfl) ⟨6018, by rfl⟩ : syracuseStep 256789 = 12037) (by norm_num)
theorem B650357 : Blo 223812 650357 := bbase (se 5 (by rfl) ⟨30485, by rfl⟩ : syracuseStep 650357 = 60971) (by norm_num)
theorem B2157749 : Blo 223812 2157749 := bbase (se 5 (by rfl) ⟨101144, by rfl⟩ : syracuseStep 2157749 = 202289) (by norm_num)
theorem B1109189 : Blo 223812 1109189 := bbase (se 4 (by rfl) ⟨103986, by rfl⟩ : syracuseStep 1109189 = 207973) (by norm_num)
theorem B453853 : Blo 223812 453853 := bbase (se 3 (by rfl) ⟨85097, by rfl⟩ : syracuseStep 453853 = 170195) (by norm_num)
theorem B322805 : Blo 223812 322805 := bbase (se 5 (by rfl) ⟨15131, by rfl⟩ : syracuseStep 322805 = 30263) (by norm_num)
theorem B1142261 : Blo 223812 1142261 := bbase (se 5 (by rfl) ⟨53543, by rfl⟩ : syracuseStep 1142261 = 107087) (by norm_num)
theorem B454261 : Blo 223812 454261 := bbase (se 5 (by rfl) ⟨21293, by rfl⟩ : syracuseStep 454261 = 42587) (by norm_num)
theorem B323285 : Blo 223812 323285 := bbase (se 7 (by rfl) ⟨3788, by rfl⟩ : syracuseStep 323285 = 7577) (by norm_num)
theorem B1732309 : Blo 223812 1732309 := bbase (se 7 (by rfl) ⟨20300, by rfl⟩ : syracuseStep 1732309 = 40601) (by norm_num)
theorem B913157 : Blo 223812 913157 := bbase (se 4 (by rfl) ⟨85608, by rfl⟩ : syracuseStep 913157 = 171217) (by norm_num)
theorem B323357 : Blo 223812 323357 := bbase (se 3 (by rfl) ⟨60629, by rfl⟩ : syracuseStep 323357 = 121259) (by norm_num)
theorem B389053 : Blo 223812 389053 := bbase (se 3 (by rfl) ⟨72947, by rfl⟩ : syracuseStep 389053 = 145895) (by norm_num)
theorem B258185 : Blo 223812 258185 := bbase (se 2 (by rfl) ⟨96819, by rfl⟩ : syracuseStep 258185 = 193639) (by norm_num)
theorem B389557 : Blo 223812 389557 := bbase (se 5 (by rfl) ⟨18260, by rfl⟩ : syracuseStep 389557 = 36521) (by norm_num)
theorem B618965 : Blo 223812 618965 := bbase (se 7 (by rfl) ⟨7253, by rfl⟩ : syracuseStep 618965 = 14507) (by norm_num)
theorem B487949 : Blo 223812 487949 := bbase (se 3 (by rfl) ⟨91490, by rfl⟩ : syracuseStep 487949 = 182981) (by norm_num)
theorem B324109 : Blo 223812 324109 := bbase (se 3 (by rfl) ⟨60770, by rfl⟩ : syracuseStep 324109 = 121541) (by norm_num)
theorem B1077781 : Blo 223812 1077781 := bbase (se 6 (by rfl) ⟨25260, by rfl⟩ : syracuseStep 1077781 = 50521) (by norm_num)
theorem B815717 : Blo 223812 815717 := bbase (se 4 (by rfl) ⟨76473, by rfl⟩ : syracuseStep 815717 = 152947) (by norm_num)
theorem B1143557 : Blo 223812 1143557 := bbase (se 4 (by rfl) ⟨107208, by rfl⟩ : syracuseStep 1143557 = 214417) (by norm_num)
theorem B1373237 : Blo 223812 1373237 := bbase (se 5 (by rfl) ⟨64370, by rfl⟩ : syracuseStep 1373237 = 128741) (by norm_num)
theorem B718789 : Blo 223812 718789 := bbase (se 4 (by rfl) ⟨67386, by rfl⟩ : syracuseStep 718789 = 134773) (by norm_num)
theorem B1144853 : Blo 223812 1144853 := bbase (se 6 (by rfl) ⟨26832, by rfl⟩ : syracuseStep 1144853 = 53665) (by norm_num)
theorem B719045 : Blo 223812 719045 := bbase (se 4 (by rfl) ⟨67410, by rfl⟩ : syracuseStep 719045 = 134821) (by norm_num)
theorem B1964405 : Blo 223812 1964405 := bbase (se 5 (by rfl) ⟨92081, by rfl⟩ : syracuseStep 1964405 = 184163) (by norm_num)
theorem B2423317 : Blo 223812 2423317 := bbase (se 6 (by rfl) ⟨56796, by rfl⟩ : syracuseStep 2423317 = 113593) (by norm_num)
theorem B457285 : Blo 223812 457285 := bbase (se 4 (by rfl) ⟨42870, by rfl⟩ : syracuseStep 457285 = 85741) (by norm_num)
theorem B1276661 : Blo 223812 1276661 := bbase (se 5 (by rfl) ⟨59843, by rfl⟩ : syracuseStep 1276661 = 119687) (by norm_num)
theorem B1178389 : Blo 223812 1178389 := bbase (se 6 (by rfl) ⟨27618, by rfl⟩ : syracuseStep 1178389 = 55237) (by norm_num)
theorem B424901 : Blo 223812 424901 := bbase (se 4 (by rfl) ⟨39834, by rfl⟩ : syracuseStep 424901 = 79669) (by norm_num)
theorem B7076821 : Blo 223812 7076821 := bbase (se 7 (by rfl) ⟨82931, by rfl⟩ : syracuseStep 7076821 = 165863) (by norm_num)
theorem B457805 : Blo 223812 457805 := bbase (se 3 (by rfl) ⟨85838, by rfl⟩ : syracuseStep 457805 = 171677) (by norm_num)
theorem B326749 : Blo 223812 326749 := bbase (se 3 (by rfl) ⟨61265, by rfl⟩ : syracuseStep 326749 = 122531) (by norm_num)
theorem B359549 : Blo 223812 359549 := bbase (se 3 (by rfl) ⟨67415, by rfl⟩ : syracuseStep 359549 = 134831) (by norm_num)
theorem B851093 : Blo 223812 851093 := bbase (se 6 (by rfl) ⟨19947, by rfl⟩ : syracuseStep 851093 = 39895) (by norm_num)
theorem B425189 : Blo 223812 425189 := bbase (se 4 (by rfl) ⟨39861, by rfl⟩ : syracuseStep 425189 = 79723) (by norm_num)
theorem B458005 : Blo 223812 458005 := bbase (se 6 (by rfl) ⟨10734, by rfl⟩ : syracuseStep 458005 = 21469) (by norm_num)
theorem B1146149 : Blo 223812 1146149 := bbase (se 4 (by rfl) ⟨107451, by rfl⟩ : syracuseStep 1146149 = 214903) (by norm_num)
theorem B359741 : Blo 223812 359741 := bbase (se 3 (by rfl) ⟨67451, by rfl⟩ : syracuseStep 359741 = 134903) (by norm_num)
theorem B425341 : Blo 223812 425341 := bbase (se 3 (by rfl) ⟨79751, by rfl⟩ : syracuseStep 425341 = 159503) (by norm_num)
theorem B851381 : Blo 223812 851381 := bbase (se 5 (by rfl) ⟨39908, by rfl⟩ : syracuseStep 851381 = 79817) (by norm_num)
theorem B1638005 : Blo 223812 1638005 := bbase (se 5 (by rfl) ⟨76781, by rfl⟩ : syracuseStep 1638005 = 153563) (by norm_num)
theorem B425645 : Blo 223812 425645 := bbase (se 3 (by rfl) ⟨79808, by rfl⟩ : syracuseStep 425645 = 159617) (by norm_num)
theorem B556949 : Blo 223812 556949 := bbase (se 6 (by rfl) ⟨13053, by rfl⟩ : syracuseStep 556949 = 26107) (by norm_num)
theorem B360497 : Blo 223812 360497 := bstep (se 2 (by rfl) ⟨135186, by rfl⟩ : syracuseStep 360497 = 270373) B270373
theorem B426161 : Blo 223812 426161 := bstep (se 2 (by rfl) ⟨159810, by rfl⟩ : syracuseStep 426161 = 319621) B319621
theorem B360625 : Blo 223812 360625 := bstep (se 2 (by rfl) ⟨135234, by rfl⟩ : syracuseStep 360625 = 270469) B270469
theorem B1147121 : Blo 223812 1147121 := bstep (se 2 (by rfl) ⟨430170, by rfl⟩ : syracuseStep 1147121 = 860341) B860341
theorem B721187 : Blo 223812 721187 := bstep (se 1 (by rfl) ⟨540890, by rfl⟩ : syracuseStep 721187 = 1081781) B1081781
theorem B688493 : Blo 223812 688493 := bstep (se 3 (by rfl) ⟨129092, by rfl⟩ : syracuseStep 688493 = 258185) B258185
theorem B361265 : Blo 223812 361265 := bstep (se 2 (by rfl) ⟨135474, by rfl⟩ : syracuseStep 361265 = 270949) B270949
theorem B426883 : Blo 223812 426883 := bstep (se 1 (by rfl) ⟨320162, by rfl⟩ : syracuseStep 426883 = 640325) B640325
theorem B787427 : Blo 223812 787427 := bstep (se 1 (by rfl) ⟨590570, by rfl⟩ : syracuseStep 787427 = 1181141) B1181141
theorem B328739 : Blo 223812 328739 := bstep (se 1 (by rfl) ⟨246554, by rfl⟩ : syracuseStep 328739 = 493109) B493109
theorem B460081 : Blo 223812 460081 := bstep (se 2 (by rfl) ⟨172530, by rfl⟩ : syracuseStep 460081 = 345061) B345061
theorem B427331 : Blo 223812 427331 := bstep (se 1 (by rfl) ⟨320498, by rfl⟩ : syracuseStep 427331 = 640997) B640997
theorem B853325 : Blo 223812 853325 := bstep (se 3 (by rfl) ⟨159998, by rfl⟩ : syracuseStep 853325 = 319997) B319997
theorem B1082915 : Blo 223812 1082915 := bstep (se 1 (by rfl) ⟨812186, by rfl⟩ : syracuseStep 1082915 = 1624373) B1624373
theorem B427619 : Blo 223812 427619 := bstep (se 1 (by rfl) ⟨320714, by rfl⟩ : syracuseStep 427619 = 641429) B641429
theorem B1148579 : Blo 223812 1148579 := bstep (se 1 (by rfl) ⟨861434, by rfl⟩ : syracuseStep 1148579 = 1722869) B1722869
theorem B755405 : Blo 223812 755405 := bstep (se 3 (by rfl) ⟨141638, by rfl⟩ : syracuseStep 755405 = 283277) B283277
theorem B755459 : Blo 223812 755459 := bstep (se 1 (by rfl) ⟨566594, by rfl⟩ : syracuseStep 755459 = 1133189) B1133189
theorem B755729 : Blo 223812 755729 := bstep (se 2 (by rfl) ⟨283398, by rfl⟩ : syracuseStep 755729 = 566797) B566797
theorem B723043 : Blo 223812 723043 := bstep (se 1 (by rfl) ⟨542282, by rfl⟩ : syracuseStep 723043 = 1084565) B1084565
theorem B362675 : Blo 223812 362675 := bstep (se 1 (by rfl) ⟨272006, by rfl⟩ : syracuseStep 362675 = 544013) B544013
theorem B362803 : Blo 223812 362803 := bstep (se 1 (by rfl) ⟨272102, by rfl⟩ : syracuseStep 362803 = 544205) B544205
theorem B788867 : Blo 223812 788867 := bstep (se 1 (by rfl) ⟨591650, by rfl⟩ : syracuseStep 788867 = 1183301) B1183301
theorem B2591117 : Blo 223812 2591117 := bstep (se 3 (by rfl) ⟨485834, by rfl⟩ : syracuseStep 2591117 = 971669) B971669
theorem B1149389 : Blo 223812 1149389 := bstep (se 3 (by rfl) ⟨215510, by rfl⟩ : syracuseStep 1149389 = 431021) B431021
theorem B461315 : Blo 223812 461315 := bstep (se 1 (by rfl) ⟨345986, by rfl⟩ : syracuseStep 461315 = 691973) B691973
theorem B428561 : Blo 223812 428561 := bstep (se 2 (by rfl) ⟨160710, by rfl⟩ : syracuseStep 428561 = 321421) B321421
theorem B756269 : Blo 223812 756269 := bstep (se 3 (by rfl) ⟨141800, by rfl⟩ : syracuseStep 756269 = 283601) B283601
theorem B723505 : Blo 223812 723505 := bstep (se 2 (by rfl) ⟨271314, by rfl⟩ : syracuseStep 723505 = 542629) B542629
theorem B756323 : Blo 223812 756323 := bstep (se 1 (by rfl) ⟨567242, by rfl⟩ : syracuseStep 756323 = 1134485) B1134485
theorem B1051235 : Blo 223812 1051235 := bstep (se 1 (by rfl) ⟨788426, by rfl⟩ : syracuseStep 1051235 = 1576853) B1576853
theorem B1280717 : Blo 223812 1280717 := bstep (se 3 (by rfl) ⟨240134, by rfl⟩ : syracuseStep 1280717 = 480269) B480269
theorem B2558789 : Blo 223812 2558789 := bstep (se 4 (by rfl) ⟨239886, by rfl⟩ : syracuseStep 2558789 = 479773) B479773
theorem B363361 : Blo 223812 363361 := bstep (se 2 (by rfl) ⟨136260, by rfl⟩ : syracuseStep 363361 = 272521) B272521
theorem B756593 : Blo 223812 756593 := bstep (se 2 (by rfl) ⟨283722, by rfl⟩ : syracuseStep 756593 = 567445) B567445
theorem B1543117 : Blo 223812 1543117 := bstep (se 3 (by rfl) ⟨289334, by rfl⟩ : syracuseStep 1543117 = 578669) B578669
theorem B822449 : Blo 223812 822449 := bstep (se 2 (by rfl) ⟨308418, by rfl⟩ : syracuseStep 822449 = 616837) B616837
theorem B757133 : Blo 223812 757133 := bstep (se 3 (by rfl) ⟨141962, by rfl⟩ : syracuseStep 757133 = 283925) B283925
theorem B429457 : Blo 223812 429457 := bstep (se 2 (by rfl) ⟨161046, by rfl⟩ : syracuseStep 429457 = 322093) B322093
theorem B757187 : Blo 223812 757187 := bstep (se 1 (by rfl) ⟨567890, by rfl⟩ : syracuseStep 757187 = 1135781) B1135781
theorem B1084913 : Blo 223812 1084913 := bstep (se 2 (by rfl) ⟨406842, by rfl⟩ : syracuseStep 1084913 = 813685) B813685
theorem B364033 : Blo 223812 364033 := bstep (se 2 (by rfl) ⟨136512, by rfl⟩ : syracuseStep 364033 = 273025) B273025
theorem B429617 : Blo 223812 429617 := bstep (se 2 (by rfl) ⟨161106, by rfl⟩ : syracuseStep 429617 = 322213) B322213
theorem B3640945 : Blo 223812 3640945 := bstep (se 2 (by rfl) ⟨1365354, by rfl⟩ : syracuseStep 3640945 = 2730709) B2730709
theorem B757457 : Blo 223812 757457 := bstep (se 2 (by rfl) ⟨284046, by rfl⟩ : syracuseStep 757457 = 568093) B568093
theorem B430019 : Blo 223812 430019 := bstep (se 1 (by rfl) ⟨322514, by rfl⟩ : syracuseStep 430019 = 645029) B645029
theorem B2297969 : Blo 223812 2297969 := bstep (se 2 (by rfl) ⟨861738, by rfl⟩ : syracuseStep 2297969 = 1723477) B1723477
theorem B2330765 : Blo 223812 2330765 := bstep (se 3 (by rfl) ⟨437018, by rfl⟩ : syracuseStep 2330765 = 874037) B874037
theorem B856241 : Blo 223812 856241 := bstep (se 2 (by rfl) ⟨321090, by rfl⟩ : syracuseStep 856241 = 642181) B642181
theorem B757997 : Blo 223812 757997 := bstep (se 3 (by rfl) ⟨142124, by rfl⟩ : syracuseStep 757997 = 284249) B284249
theorem B758051 : Blo 223812 758051 := bstep (se 1 (by rfl) ⟨568538, by rfl⟩ : syracuseStep 758051 = 1137077) B1137077
theorem B1085795 : Blo 223812 1085795 := bstep (se 1 (by rfl) ⟨814346, by rfl⟩ : syracuseStep 1085795 = 1628693) B1628693
theorem B758321 : Blo 223812 758321 := bstep (se 2 (by rfl) ⟨284370, by rfl⟩ : syracuseStep 758321 = 568741) B568741
theorem B365155 : Blo 223812 365155 := bstep (se 1 (by rfl) ⟨273866, by rfl⟩ : syracuseStep 365155 = 547733) B547733
theorem B430915 : Blo 223812 430915 := bstep (se 1 (by rfl) ⟨323186, by rfl⟩ : syracuseStep 430915 = 646373) B646373
theorem B2724677 : Blo 223812 2724677 := bstep (se 4 (by rfl) ⟨255438, by rfl⟩ : syracuseStep 2724677 = 510877) B510877
theorem B1282949 : Blo 223812 1282949 := bstep (se 4 (by rfl) ⟨120276, by rfl⟩ : syracuseStep 1282949 = 240553) B240553
theorem B431075 : Blo 223812 431075 := bstep (se 1 (by rfl) ⟨323306, by rfl⟩ : syracuseStep 431075 = 646613) B646613
theorem B758861 : Blo 223812 758861 := bstep (se 3 (by rfl) ⟨142286, by rfl⟩ : syracuseStep 758861 = 284573) B284573
theorem B758915 : Blo 223812 758915 := bstep (se 1 (by rfl) ⟨569186, by rfl⟩ : syracuseStep 758915 = 1138373) B1138373
theorem B1086605 : Blo 223812 1086605 := bstep (se 3 (by rfl) ⟨203738, by rfl⟩ : syracuseStep 1086605 = 407477) B407477
theorem B726221 : Blo 223812 726221 := bstep (se 3 (by rfl) ⟨136166, by rfl⟩ : syracuseStep 726221 = 272333) B272333
theorem B365779 : Blo 223812 365779 := bstep (se 1 (by rfl) ⟨274334, by rfl⟩ : syracuseStep 365779 = 548669) B548669
theorem B1152305 : Blo 223812 1152305 := bstep (se 2 (by rfl) ⟨432114, by rfl⟩ : syracuseStep 1152305 = 864229) B864229
theorem B759185 : Blo 223812 759185 := bstep (se 2 (by rfl) ⟨284694, by rfl⟩ : syracuseStep 759185 = 569389) B569389
theorem B1283633 : Blo 223812 1283633 := bstep (se 2 (by rfl) ⟨481362, by rfl⟩ : syracuseStep 1283633 = 962725) B962725
theorem B857699 : Blo 223812 857699 := bstep (se 1 (by rfl) ⟨643274, by rfl⟩ : syracuseStep 857699 = 1286549) B1286549
theorem B431747 : Blo 223812 431747 := bstep (se 1 (by rfl) ⟨323810, by rfl⟩ : syracuseStep 431747 = 647621) B647621
theorem B366275 : Blo 223812 366275 := bstep (se 1 (by rfl) ⟨274706, by rfl⟩ : syracuseStep 366275 = 549413) B549413
theorem B759725 : Blo 223812 759725 := bstep (se 3 (by rfl) ⟨142448, by rfl⟩ : syracuseStep 759725 = 284897) B284897
theorem B956387 : Blo 223812 956387 := bstep (se 1 (by rfl) ⟨717290, by rfl⟩ : syracuseStep 956387 = 1434581) B1434581
theorem B759779 : Blo 223812 759779 := bstep (se 1 (by rfl) ⟨569834, by rfl⟩ : syracuseStep 759779 = 1139669) B1139669
theorem B432145 : Blo 223812 432145 := bstep (se 2 (by rfl) ⟨162054, by rfl⟩ : syracuseStep 432145 = 324109) B324109
theorem B760049 : Blo 223812 760049 := bstep (se 2 (by rfl) ⟨285018, by rfl⟩ : syracuseStep 760049 = 570037) B570037
theorem B2595185 : Blo 223812 2595185 := bstep (se 2 (by rfl) ⟨973194, by rfl⟩ : syracuseStep 2595185 = 1946389) B1946389
theorem B858701 : Blo 223812 858701 := bstep (se 3 (by rfl) ⟨161006, by rfl⟩ : syracuseStep 858701 = 322013) B322013
theorem B268931 : Blo 223812 268931 := bstep (se 1 (by rfl) ⟨201698, by rfl⟩ : syracuseStep 268931 = 403397) B403397
theorem B727811 : Blo 223812 727811 := bstep (se 1 (by rfl) ⟨545858, by rfl⟩ : syracuseStep 727811 = 1091717) B1091717
theorem B760589 : Blo 223812 760589 := bstep (se 3 (by rfl) ⟨142610, by rfl⟩ : syracuseStep 760589 = 285221) B285221
theorem B760643 : Blo 223812 760643 := bstep (se 1 (by rfl) ⟨570482, by rfl⟩ : syracuseStep 760643 = 1140965) B1140965
theorem B1285091 : Blo 223812 1285091 := bstep (se 1 (by rfl) ⟨963818, by rfl⟩ : syracuseStep 1285091 = 1927637) B1927637
theorem B760913 : Blo 223812 760913 := bstep (se 2 (by rfl) ⟨285342, by rfl⟩ : syracuseStep 760913 = 570685) B570685
theorem B433571 : Blo 223812 433571 := bstep (se 1 (by rfl) ⟨325178, by rfl⟩ : syracuseStep 433571 = 650357) B650357
theorem B1449571 : Blo 223812 1449571 := bstep (se 1 (by rfl) ⟨1087178, by rfl⟩ : syracuseStep 1449571 = 2174357) B2174357
theorem B761453 : Blo 223812 761453 := bstep (se 3 (by rfl) ⟨142772, by rfl⟩ : syracuseStep 761453 = 285545) B285545
theorem B761507 : Blo 223812 761507 := bstep (se 1 (by rfl) ⟨571130, by rfl⟩ : syracuseStep 761507 = 1142261) B1142261
theorem B335729 : Blo 223812 335729 := bstep (se 2 (by rfl) ⟨125898, by rfl⟩ : syracuseStep 335729 = 251797) B251797
theorem B335747 : Blo 223812 335747 := bstep (se 1 (by rfl) ⟨251810, by rfl⟩ : syracuseStep 335747 = 503621) B503621
theorem B335777 : Blo 223812 335777 := bstep (se 2 (by rfl) ⟨125916, by rfl⟩ : syracuseStep 335777 = 251833) B251833
theorem B958385 : Blo 223812 958385 := bstep (se 2 (by rfl) ⟨359394, by rfl⟩ : syracuseStep 958385 = 718789) B718789
theorem B335795 : Blo 223812 335795 := bstep (se 1 (by rfl) ⟨251846, by rfl⟩ : syracuseStep 335795 = 503693) B503693
theorem B761777 : Blo 223812 761777 := bstep (se 2 (by rfl) ⟨285666, by rfl⟩ : syracuseStep 761777 = 571333) B571333
theorem B335825 : Blo 223812 335825 := bstep (se 2 (by rfl) ⟨125934, by rfl⟩ : syracuseStep 335825 = 251869) B251869
theorem B335843 : Blo 223812 335843 := bstep (se 1 (by rfl) ⟨251882, by rfl⟩ : syracuseStep 335843 = 503765) B503765
theorem B335873 : Blo 223812 335873 := bstep (se 2 (by rfl) ⟨125952, by rfl⟩ : syracuseStep 335873 = 251905) B251905
theorem B729091 : Blo 223812 729091 := bstep (se 1 (by rfl) ⟨546818, by rfl⟩ : syracuseStep 729091 = 1093637) B1093637
theorem B335891 : Blo 223812 335891 := bstep (se 1 (by rfl) ⟨251918, by rfl⟩ : syracuseStep 335891 = 503837) B503837
theorem B335921 : Blo 223812 335921 := bstep (se 2 (by rfl) ⟨125970, by rfl⟩ : syracuseStep 335921 = 251941) B251941
theorem B335939 : Blo 223812 335939 := bstep (se 1 (by rfl) ⟨251954, by rfl⟩ : syracuseStep 335939 = 503909) B503909
theorem B335969 : Blo 223812 335969 := bstep (se 2 (by rfl) ⟨125988, by rfl⟩ : syracuseStep 335969 = 251977) B251977
theorem B335987 : Blo 223812 335987 := bstep (se 1 (by rfl) ⟨251990, by rfl⟩ : syracuseStep 335987 = 503981) B503981
theorem B5218445 : Blo 223812 5218445 := bstep (se 3 (by rfl) ⟨978458, by rfl⟩ : syracuseStep 5218445 = 1956917) B1956917
theorem B336017 : Blo 223812 336017 := bstep (se 2 (by rfl) ⟨126006, by rfl⟩ : syracuseStep 336017 = 252013) B252013
theorem B336035 : Blo 223812 336035 := bstep (se 1 (by rfl) ⟨252026, by rfl⟩ : syracuseStep 336035 = 504053) B504053
theorem B336065 : Blo 223812 336065 := bstep (se 2 (by rfl) ⟨126024, by rfl⟩ : syracuseStep 336065 = 252049) B252049
theorem B336083 : Blo 223812 336083 := bstep (se 1 (by rfl) ⟨252062, by rfl⟩ : syracuseStep 336083 = 504125) B504125
theorem B336113 : Blo 223812 336113 := bstep (se 2 (by rfl) ⟨126042, by rfl⟩ : syracuseStep 336113 = 252085) B252085
theorem B336131 : Blo 223812 336131 := bstep (se 1 (by rfl) ⟨252098, by rfl⟩ : syracuseStep 336131 = 504197) B504197
theorem B336161 : Blo 223812 336161 := bstep (se 2 (by rfl) ⟨126060, by rfl⟩ : syracuseStep 336161 = 252121) B252121
theorem B336179 : Blo 223812 336179 := bstep (se 1 (by rfl) ⟨252134, by rfl⟩ : syracuseStep 336179 = 504269) B504269
theorem B336209 : Blo 223812 336209 := bstep (se 2 (by rfl) ⟨126078, by rfl⟩ : syracuseStep 336209 = 252157) B252157
theorem B729425 : Blo 223812 729425 := bstep (se 2 (by rfl) ⟨273534, by rfl⟩ : syracuseStep 729425 = 547069) B547069
theorem B336227 : Blo 223812 336227 := bstep (se 1 (by rfl) ⟨252170, by rfl⟩ : syracuseStep 336227 = 504341) B504341
theorem B336257 : Blo 223812 336257 := bstep (se 2 (by rfl) ⟨126096, by rfl⟩ : syracuseStep 336257 = 252193) B252193
theorem B336275 : Blo 223812 336275 := bstep (se 1 (by rfl) ⟨252206, by rfl⟩ : syracuseStep 336275 = 504413) B504413
theorem B336305 : Blo 223812 336305 := bstep (se 2 (by rfl) ⟨126114, by rfl⟩ : syracuseStep 336305 = 252229) B252229
theorem B336323 : Blo 223812 336323 := bstep (se 1 (by rfl) ⟨252242, by rfl⟩ : syracuseStep 336323 = 504485) B504485
theorem B762317 : Blo 223812 762317 := bstep (se 3 (by rfl) ⟨142934, by rfl⟩ : syracuseStep 762317 = 285869) B285869
theorem B336353 : Blo 223812 336353 := bstep (se 2 (by rfl) ⟨126132, by rfl⟩ : syracuseStep 336353 = 252265) B252265
theorem B336371 : Blo 223812 336371 := bstep (se 1 (by rfl) ⟨252278, by rfl⟩ : syracuseStep 336371 = 504557) B504557
theorem B762371 : Blo 223812 762371 := bstep (se 1 (by rfl) ⟨571778, by rfl⟩ : syracuseStep 762371 = 1143557) B1143557
theorem B2564621 : Blo 223812 2564621 := bstep (se 3 (by rfl) ⟨480866, by rfl⟩ : syracuseStep 2564621 = 961733) B961733
theorem B336401 : Blo 223812 336401 := bstep (se 2 (by rfl) ⟨126150, by rfl⟩ : syracuseStep 336401 = 252301) B252301
theorem B336419 : Blo 223812 336419 := bstep (se 1 (by rfl) ⟨252314, by rfl⟩ : syracuseStep 336419 = 504629) B504629
theorem B336449 : Blo 223812 336449 := bstep (se 2 (by rfl) ⟨126168, by rfl⟩ : syracuseStep 336449 = 252337) B252337
theorem B336467 : Blo 223812 336467 := bstep (se 1 (by rfl) ⟨252350, by rfl⟩ : syracuseStep 336467 = 504701) B504701
theorem B336497 : Blo 223812 336497 := bstep (se 2 (by rfl) ⟨126186, by rfl⟩ : syracuseStep 336497 = 252373) B252373
theorem B336515 : Blo 223812 336515 := bstep (se 1 (by rfl) ⟨252386, by rfl⟩ : syracuseStep 336515 = 504773) B504773
theorem B860813 : Blo 223812 860813 := bstep (se 3 (by rfl) ⟨161402, by rfl⟩ : syracuseStep 860813 = 322805) B322805
theorem B336545 : Blo 223812 336545 := bstep (se 2 (by rfl) ⟨126204, by rfl⟩ : syracuseStep 336545 = 252409) B252409
theorem B336563 : Blo 223812 336563 := bstep (se 1 (by rfl) ⟨252422, by rfl⟩ : syracuseStep 336563 = 504845) B504845
theorem B336593 : Blo 223812 336593 := bstep (se 2 (by rfl) ⟨126222, by rfl⟩ : syracuseStep 336593 = 252445) B252445
theorem B336611 : Blo 223812 336611 := bstep (se 1 (by rfl) ⟨252458, by rfl⟩ : syracuseStep 336611 = 504917) B504917
theorem B336641 : Blo 223812 336641 := bstep (se 2 (by rfl) ⟨126240, by rfl⟩ : syracuseStep 336641 = 252481) B252481
theorem B762641 : Blo 223812 762641 := bstep (se 2 (by rfl) ⟨285990, by rfl⟩ : syracuseStep 762641 = 571981) B571981
theorem B336659 : Blo 223812 336659 := bstep (se 1 (by rfl) ⟨252494, by rfl⟩ : syracuseStep 336659 = 504989) B504989
theorem B336689 : Blo 223812 336689 := bstep (se 2 (by rfl) ⟨126258, by rfl⟩ : syracuseStep 336689 = 252517) B252517
theorem B1450801 : Blo 223812 1450801 := bstep (se 2 (by rfl) ⟨544050, by rfl⟩ : syracuseStep 1450801 = 1088101) B1088101
theorem B336707 : Blo 223812 336707 := bstep (se 1 (by rfl) ⟨252530, by rfl⟩ : syracuseStep 336707 = 505061) B505061
theorem B959309 : Blo 223812 959309 := bstep (se 3 (by rfl) ⟨179870, by rfl⟩ : syracuseStep 959309 = 359741) B359741
theorem B336737 : Blo 223812 336737 := bstep (se 2 (by rfl) ⟨126276, by rfl⟩ : syracuseStep 336737 = 252553) B252553
theorem B336755 : Blo 223812 336755 := bstep (se 1 (by rfl) ⟨252566, by rfl⟩ : syracuseStep 336755 = 505133) B505133
theorem B336785 : Blo 223812 336785 := bstep (se 2 (by rfl) ⟨126294, by rfl⟩ : syracuseStep 336785 = 252589) B252589
theorem B336803 : Blo 223812 336803 := bstep (se 1 (by rfl) ⟨252602, by rfl⟩ : syracuseStep 336803 = 505205) B505205
theorem B336833 : Blo 223812 336833 := bstep (se 2 (by rfl) ⟨126312, by rfl⟩ : syracuseStep 336833 = 252625) B252625
theorem B336851 : Blo 223812 336851 := bstep (se 1 (by rfl) ⟨252638, by rfl⟩ : syracuseStep 336851 = 505277) B505277
theorem B336881 : Blo 223812 336881 := bstep (se 2 (by rfl) ⟨126330, by rfl⟩ : syracuseStep 336881 = 252661) B252661
theorem B336899 : Blo 223812 336899 := bstep (se 1 (by rfl) ⟨252674, by rfl⟩ : syracuseStep 336899 = 505349) B505349
theorem B336929 : Blo 223812 336929 := bstep (se 2 (by rfl) ⟨126348, by rfl⟩ : syracuseStep 336929 = 252697) B252697
theorem B336947 : Blo 223812 336947 := bstep (se 1 (by rfl) ⟨252710, by rfl⟩ : syracuseStep 336947 = 505421) B505421
theorem B336977 : Blo 223812 336977 := bstep (se 2 (by rfl) ⟨126366, by rfl⟩ : syracuseStep 336977 = 252733) B252733
theorem B336995 : Blo 223812 336995 := bstep (se 1 (by rfl) ⟨252746, by rfl⟩ : syracuseStep 336995 = 505493) B505493
theorem B271459 : Blo 223812 271459 := bstep (se 1 (by rfl) ⟨203594, by rfl⟩ : syracuseStep 271459 = 407189) B407189
theorem B337025 : Blo 223812 337025 := bstep (se 2 (by rfl) ⟨126384, by rfl⟩ : syracuseStep 337025 = 252769) B252769
theorem B337043 : Blo 223812 337043 := bstep (se 1 (by rfl) ⟨252782, by rfl⟩ : syracuseStep 337043 = 505565) B505565
theorem B271507 : Blo 223812 271507 := bstep (se 1 (by rfl) ⟨203630, by rfl⟩ : syracuseStep 271507 = 407261) B407261
theorem B337073 : Blo 223812 337073 := bstep (se 2 (by rfl) ⟨126402, by rfl⟩ : syracuseStep 337073 = 252805) B252805
theorem B337091 : Blo 223812 337091 := bstep (se 1 (by rfl) ⟨252818, by rfl⟩ : syracuseStep 337091 = 505637) B505637
theorem B337121 : Blo 223812 337121 := bstep (se 2 (by rfl) ⟨126420, by rfl⟩ : syracuseStep 337121 = 252841) B252841
theorem B337139 : Blo 223812 337139 := bstep (se 1 (by rfl) ⟨252854, by rfl⟩ : syracuseStep 337139 = 505709) B505709
theorem B271603 : Blo 223812 271603 := bstep (se 1 (by rfl) ⟨203702, by rfl⟩ : syracuseStep 271603 = 407405) B407405
theorem B337169 : Blo 223812 337169 := bstep (se 2 (by rfl) ⟨126438, by rfl⟩ : syracuseStep 337169 = 252877) B252877
theorem B337187 : Blo 223812 337187 := bstep (se 1 (by rfl) ⟨252890, by rfl⟩ : syracuseStep 337187 = 505781) B505781
theorem B763181 : Blo 223812 763181 := bstep (se 3 (by rfl) ⟨143096, by rfl⟩ : syracuseStep 763181 = 286193) B286193
theorem B337217 : Blo 223812 337217 := bstep (se 2 (by rfl) ⟨126456, by rfl⟩ : syracuseStep 337217 = 252913) B252913
theorem B337235 : Blo 223812 337235 := bstep (se 1 (by rfl) ⟨252926, by rfl⟩ : syracuseStep 337235 = 505853) B505853
theorem B763235 : Blo 223812 763235 := bstep (se 1 (by rfl) ⟨572426, by rfl⟩ : syracuseStep 763235 = 1144853) B1144853
theorem B337265 : Blo 223812 337265 := bstep (se 2 (by rfl) ⟨126474, by rfl⟩ : syracuseStep 337265 = 252949) B252949
theorem B337283 : Blo 223812 337283 := bstep (se 1 (by rfl) ⟨252962, by rfl⟩ : syracuseStep 337283 = 505925) B505925
theorem B337313 : Blo 223812 337313 := bstep (se 2 (by rfl) ⟨126492, by rfl⟩ : syracuseStep 337313 = 252985) B252985
theorem B861617 : Blo 223812 861617 := bstep (se 2 (by rfl) ⟨323106, by rfl⟩ : syracuseStep 861617 = 646213) B646213
theorem B337331 : Blo 223812 337331 := bstep (se 1 (by rfl) ⟨252998, by rfl⟩ : syracuseStep 337331 = 505997) B505997
theorem B337361 : Blo 223812 337361 := bstep (se 2 (by rfl) ⟨126510, by rfl⟩ : syracuseStep 337361 = 253021) B253021
theorem B435665 : Blo 223812 435665 := bstep (se 2 (by rfl) ⟨163374, by rfl⟩ : syracuseStep 435665 = 326749) B326749
theorem B337379 : Blo 223812 337379 := bstep (se 1 (by rfl) ⟨253034, by rfl⟩ : syracuseStep 337379 = 506069) B506069
theorem B1713635 : Blo 223812 1713635 := bstep (se 1 (by rfl) ⟨1285226, by rfl⟩ : syracuseStep 1713635 = 2570453) B2570453
theorem B337409 : Blo 223812 337409 := bstep (se 2 (by rfl) ⟨126528, by rfl⟩ : syracuseStep 337409 = 253057) B253057
theorem B1615373 : Blo 223812 1615373 := bstep (se 3 (by rfl) ⟨302882, by rfl⟩ : syracuseStep 1615373 = 605765) B605765
theorem B337427 : Blo 223812 337427 := bstep (se 1 (by rfl) ⟨253070, by rfl⟩ : syracuseStep 337427 = 506141) B506141
theorem B337457 : Blo 223812 337457 := bstep (se 2 (by rfl) ⟨126546, by rfl⟩ : syracuseStep 337457 = 253093) B253093
theorem B337475 : Blo 223812 337475 := bstep (se 1 (by rfl) ⟨253106, by rfl⟩ : syracuseStep 337475 = 506213) B506213
theorem B370273 : Blo 223812 370273 := bstep (se 2 (by rfl) ⟨138852, by rfl⟩ : syracuseStep 370273 = 277705) B277705
theorem B337505 : Blo 223812 337505 := bstep (se 2 (by rfl) ⟨126564, by rfl⟩ : syracuseStep 337505 = 253129) B253129
theorem B763505 : Blo 223812 763505 := bstep (se 2 (by rfl) ⟨286314, by rfl⟩ : syracuseStep 763505 = 572629) B572629
theorem B337523 : Blo 223812 337523 := bstep (se 1 (by rfl) ⟨253142, by rfl⟩ : syracuseStep 337523 = 506285) B506285
theorem B6006413 : Blo 223812 6006413 := bstep (se 3 (by rfl) ⟨1126202, by rfl⟩ : syracuseStep 6006413 = 2252405) B2252405
theorem B4368013 : Blo 223812 4368013 := bstep (se 3 (by rfl) ⟨819002, by rfl⟩ : syracuseStep 4368013 = 1638005) B1638005
theorem B337553 : Blo 223812 337553 := bstep (se 2 (by rfl) ⟨126582, by rfl⟩ : syracuseStep 337553 = 253165) B253165
theorem B337571 : Blo 223812 337571 := bstep (se 1 (by rfl) ⟨253178, by rfl⟩ : syracuseStep 337571 = 506357) B506357
theorem B337601 : Blo 223812 337601 := bstep (se 2 (by rfl) ⟨126600, by rfl⟩ : syracuseStep 337601 = 253201) B253201
theorem B337619 : Blo 223812 337619 := bstep (se 1 (by rfl) ⟨253214, by rfl⟩ : syracuseStep 337619 = 506429) B506429
theorem B337649 : Blo 223812 337649 := bstep (se 2 (by rfl) ⟨126618, by rfl⟩ : syracuseStep 337649 = 253237) B253237
theorem B337667 : Blo 223812 337667 := bstep (se 1 (by rfl) ⟨253250, by rfl⟩ : syracuseStep 337667 = 506501) B506501
theorem B337697 : Blo 223812 337697 := bstep (se 2 (by rfl) ⟨126636, by rfl⟩ : syracuseStep 337697 = 253273) B253273
theorem B337715 : Blo 223812 337715 := bstep (se 1 (by rfl) ⟨253286, by rfl⟩ : syracuseStep 337715 = 506573) B506573
theorem B272179 : Blo 223812 272179 := bstep (se 1 (by rfl) ⟨204134, by rfl⟩ : syracuseStep 272179 = 408269) B408269
theorem B567121 : Blo 223812 567121 := bstep (se 2 (by rfl) ⟨212670, by rfl⟩ : syracuseStep 567121 = 425341) B425341
theorem B337745 : Blo 223812 337745 := bstep (se 2 (by rfl) ⟨126654, by rfl⟩ : syracuseStep 337745 = 253309) B253309
theorem B337763 : Blo 223812 337763 := bstep (se 1 (by rfl) ⟨253322, by rfl⟩ : syracuseStep 337763 = 506645) B506645
theorem B337793 : Blo 223812 337793 := bstep (se 2 (by rfl) ⟨126672, by rfl⟩ : syracuseStep 337793 = 253345) B253345
theorem B862093 : Blo 223812 862093 := bstep (se 3 (by rfl) ⟨161642, by rfl⟩ : syracuseStep 862093 = 323285) B323285
theorem B337811 : Blo 223812 337811 := bstep (se 1 (by rfl) ⟨253358, by rfl⟩ : syracuseStep 337811 = 506717) B506717
theorem B337841 : Blo 223812 337841 := bstep (se 2 (by rfl) ⟨126690, by rfl⟩ : syracuseStep 337841 = 253381) B253381
theorem B337859 : Blo 223812 337859 := bstep (se 1 (by rfl) ⟨253394, by rfl⟩ : syracuseStep 337859 = 506789) B506789
theorem B337889 : Blo 223812 337889 := bstep (se 2 (by rfl) ⟨126708, by rfl⟩ : syracuseStep 337889 = 253417) B253417
theorem B337907 : Blo 223812 337907 := bstep (se 1 (by rfl) ⟨253430, by rfl⟩ : syracuseStep 337907 = 506861) B506861
theorem B337937 : Blo 223812 337937 := bstep (se 2 (by rfl) ⟨126726, by rfl⟩ : syracuseStep 337937 = 253453) B253453
theorem B337955 : Blo 223812 337955 := bstep (se 1 (by rfl) ⟨253466, by rfl⟩ : syracuseStep 337955 = 506933) B506933
theorem B305203 : Blo 223812 305203 := bstep (se 1 (by rfl) ⟨228902, by rfl⟩ : syracuseStep 305203 = 457805) B457805
theorem B337985 : Blo 223812 337985 := bstep (se 2 (by rfl) ⟨126744, by rfl⟩ : syracuseStep 337985 = 253489) B253489
theorem B862285 : Blo 223812 862285 := bstep (se 3 (by rfl) ⟨161678, by rfl⟩ : syracuseStep 862285 = 323357) B323357
theorem B239699 : Blo 223812 239699 := bstep (se 1 (by rfl) ⟨179774, by rfl⟩ : syracuseStep 239699 = 359549) B359549
theorem B338003 : Blo 223812 338003 := bstep (se 1 (by rfl) ⟨253502, by rfl⟩ : syracuseStep 338003 = 507005) B507005
theorem B567395 : Blo 223812 567395 := bstep (se 1 (by rfl) ⟨425546, by rfl⟩ : syracuseStep 567395 = 851093) B851093
theorem B338033 : Blo 223812 338033 := bstep (se 2 (by rfl) ⟨126762, by rfl⟩ : syracuseStep 338033 = 253525) B253525
theorem B338051 : Blo 223812 338051 := bstep (se 1 (by rfl) ⟨253538, by rfl⟩ : syracuseStep 338051 = 507077) B507077
theorem B1288325 : Blo 223812 1288325 := bstep (se 4 (by rfl) ⟨120780, by rfl⟩ : syracuseStep 1288325 = 241561) B241561
theorem B764045 : Blo 223812 764045 := bstep (se 3 (by rfl) ⟨143258, by rfl⟩ : syracuseStep 764045 = 286517) B286517
theorem B338081 : Blo 223812 338081 := bstep (se 2 (by rfl) ⟨126780, by rfl⟩ : syracuseStep 338081 = 253561) B253561
theorem B338099 : Blo 223812 338099 := bstep (se 1 (by rfl) ⟨253574, by rfl⟩ : syracuseStep 338099 = 507149) B507149
theorem B764099 : Blo 223812 764099 := bstep (se 1 (by rfl) ⟨573074, by rfl⟩ : syracuseStep 764099 = 1146149) B1146149
theorem B2009285 : Blo 223812 2009285 := bstep (se 4 (by rfl) ⟨188370, by rfl⟩ : syracuseStep 2009285 = 376741) B376741
theorem B338129 : Blo 223812 338129 := bstep (se 2 (by rfl) ⟨126798, by rfl⟩ : syracuseStep 338129 = 253597) B253597
theorem B338147 : Blo 223812 338147 := bstep (se 1 (by rfl) ⟨253610, by rfl⟩ : syracuseStep 338147 = 507221) B507221
theorem B338177 : Blo 223812 338177 := bstep (se 2 (by rfl) ⟨126816, by rfl⟩ : syracuseStep 338177 = 253633) B253633
theorem B338195 : Blo 223812 338195 := bstep (se 1 (by rfl) ⟨253646, by rfl⟩ : syracuseStep 338195 = 507293) B507293
theorem B567587 : Blo 223812 567587 := bstep (se 1 (by rfl) ⟨425690, by rfl⟩ : syracuseStep 567587 = 851381) B851381
theorem B1026353 : Blo 223812 1026353 := bstep (se 2 (by rfl) ⟨384882, by rfl⟩ : syracuseStep 1026353 = 769765) B769765
theorem B338225 : Blo 223812 338225 := bstep (se 2 (by rfl) ⟨126834, by rfl⟩ : syracuseStep 338225 = 253669) B253669
theorem B338243 : Blo 223812 338243 := bstep (se 1 (by rfl) ⟨253682, by rfl⟩ : syracuseStep 338243 = 507365) B507365
theorem B338273 : Blo 223812 338273 := bstep (se 2 (by rfl) ⟨126852, by rfl⟩ : syracuseStep 338273 = 253705) B253705
theorem B338291 : Blo 223812 338291 := bstep (se 1 (by rfl) ⟨253718, by rfl⟩ : syracuseStep 338291 = 507437) B507437
theorem B338321 : Blo 223812 338321 := bstep (se 2 (by rfl) ⟨126870, by rfl⟩ : syracuseStep 338321 = 253741) B253741
theorem B338339 : Blo 223812 338339 := bstep (se 1 (by rfl) ⟨253754, by rfl⟩ : syracuseStep 338339 = 507509) B507509
theorem B338369 : Blo 223812 338369 := bstep (se 2 (by rfl) ⟨126888, by rfl⟩ : syracuseStep 338369 = 253777) B253777
theorem B764369 : Blo 223812 764369 := bstep (se 2 (by rfl) ⟨286638, by rfl⟩ : syracuseStep 764369 = 573277) B573277
theorem B338387 : Blo 223812 338387 := bstep (se 1 (by rfl) ⟨253790, by rfl⟩ : syracuseStep 338387 = 507581) B507581
theorem B338417 : Blo 223812 338417 := bstep (se 2 (by rfl) ⟨126906, by rfl⟩ : syracuseStep 338417 = 253813) B253813
theorem B338435 : Blo 223812 338435 := bstep (se 1 (by rfl) ⟨253826, by rfl⟩ : syracuseStep 338435 = 507653) B507653
theorem B338465 : Blo 223812 338465 := bstep (se 2 (by rfl) ⟨126924, by rfl⟩ : syracuseStep 338465 = 253849) B253849
theorem B338483 : Blo 223812 338483 := bstep (se 1 (by rfl) ⟨253862, by rfl⟩ : syracuseStep 338483 = 507725) B507725
theorem B1288781 : Blo 223812 1288781 := bstep (se 3 (by rfl) ⟨241646, by rfl⟩ : syracuseStep 1288781 = 483293) B483293
theorem B338513 : Blo 223812 338513 := bstep (se 2 (by rfl) ⟨126942, by rfl⟩ : syracuseStep 338513 = 253885) B253885
theorem B371299 : Blo 223812 371299 := bstep (se 1 (by rfl) ⟨278474, by rfl⟩ : syracuseStep 371299 = 556949) B556949
theorem B338531 : Blo 223812 338531 := bstep (se 1 (by rfl) ⟨253898, by rfl⟩ : syracuseStep 338531 = 507797) B507797
theorem B338561 : Blo 223812 338561 := bstep (se 2 (by rfl) ⟨126960, by rfl⟩ : syracuseStep 338561 = 253921) B253921
theorem B338579 : Blo 223812 338579 := bstep (se 1 (by rfl) ⟨253934, by rfl⟩ : syracuseStep 338579 = 507869) B507869
theorem B338609 : Blo 223812 338609 := bstep (se 2 (by rfl) ⟨126978, by rfl⟩ : syracuseStep 338609 = 253957) B253957
theorem B338627 : Blo 223812 338627 := bstep (se 1 (by rfl) ⟨253970, by rfl⟩ : syracuseStep 338627 = 507941) B507941
theorem B338657 : Blo 223812 338657 := bstep (se 2 (by rfl) ⟨126996, by rfl⟩ : syracuseStep 338657 = 253993) B253993
theorem B338675 : Blo 223812 338675 := bstep (se 1 (by rfl) ⟨254006, by rfl⟩ : syracuseStep 338675 = 508013) B508013
theorem B338705 : Blo 223812 338705 := bstep (se 2 (by rfl) ⟨127014, by rfl⟩ : syracuseStep 338705 = 254029) B254029
theorem B338723 : Blo 223812 338723 := bstep (se 1 (by rfl) ⟨254042, by rfl⟩ : syracuseStep 338723 = 508085) B508085
theorem B338753 : Blo 223812 338753 := bstep (se 2 (by rfl) ⟨127032, by rfl⟩ : syracuseStep 338753 = 254065) B254065
theorem B338771 : Blo 223812 338771 := bstep (se 1 (by rfl) ⟨254078, by rfl⟩ : syracuseStep 338771 = 508157) B508157
theorem B863075 : Blo 223812 863075 := bstep (se 1 (by rfl) ⟨647306, by rfl⟩ : syracuseStep 863075 = 1294613) B1294613
theorem B338801 : Blo 223812 338801 := bstep (se 2 (by rfl) ⟨127050, by rfl⟩ : syracuseStep 338801 = 254101) B254101
theorem B338819 : Blo 223812 338819 := bstep (se 1 (by rfl) ⟨254114, by rfl⟩ : syracuseStep 338819 = 508229) B508229
theorem B338849 : Blo 223812 338849 := bstep (se 2 (by rfl) ⟨127068, by rfl⟩ : syracuseStep 338849 = 254137) B254137
theorem B338867 : Blo 223812 338867 := bstep (se 1 (by rfl) ⟨254150, by rfl⟩ : syracuseStep 338867 = 508301) B508301
theorem B338897 : Blo 223812 338897 := bstep (se 2 (by rfl) ⟨127086, by rfl⟩ : syracuseStep 338897 = 254173) B254173
theorem B338915 : Blo 223812 338915 := bstep (se 1 (by rfl) ⟨254186, by rfl⟩ : syracuseStep 338915 = 508373) B508373
theorem B764909 : Blo 223812 764909 := bstep (se 3 (by rfl) ⟨143420, by rfl⟩ : syracuseStep 764909 = 286841) B286841
theorem B338945 : Blo 223812 338945 := bstep (se 2 (by rfl) ⟨127104, by rfl⟩ : syracuseStep 338945 = 254209) B254209
theorem B338963 : Blo 223812 338963 := bstep (se 1 (by rfl) ⟨254222, by rfl⟩ : syracuseStep 338963 = 508445) B508445
theorem B764963 : Blo 223812 764963 := bstep (se 1 (by rfl) ⟨573722, by rfl⟩ : syracuseStep 764963 = 1147445) B1147445
theorem B338993 : Blo 223812 338993 := bstep (se 2 (by rfl) ⟨127122, by rfl⟩ : syracuseStep 338993 = 254245) B254245
theorem B339011 : Blo 223812 339011 := bstep (se 1 (by rfl) ⟨254258, by rfl⟩ : syracuseStep 339011 = 508517) B508517
theorem B339041 : Blo 223812 339041 := bstep (se 2 (by rfl) ⟨127140, by rfl⟩ : syracuseStep 339041 = 254281) B254281
theorem B339059 : Blo 223812 339059 := bstep (se 1 (by rfl) ⟨254294, by rfl⟩ : syracuseStep 339059 = 508589) B508589
theorem B339089 : Blo 223812 339089 := bstep (se 2 (by rfl) ⟨127158, by rfl⟩ : syracuseStep 339089 = 254317) B254317
theorem B339107 : Blo 223812 339107 := bstep (se 1 (by rfl) ⟨254330, by rfl⟩ : syracuseStep 339107 = 508661) B508661
theorem B339137 : Blo 223812 339137 := bstep (se 2 (by rfl) ⟨127176, by rfl⟩ : syracuseStep 339137 = 254353) B254353
theorem B568529 : Blo 223812 568529 := bstep (se 2 (by rfl) ⟨213198, by rfl⟩ : syracuseStep 568529 = 426397) B426397
theorem B339155 : Blo 223812 339155 := bstep (se 1 (by rfl) ⟨254366, by rfl⟩ : syracuseStep 339155 = 508733) B508733
theorem B11775203 : Blo 223812 11775203 := bstep (se 1 (by rfl) ⟨8831402, by rfl⟩ : syracuseStep 11775203 = 17662805) B17662805
theorem B339185 : Blo 223812 339185 := bstep (se 2 (by rfl) ⟨127194, by rfl⟩ : syracuseStep 339185 = 254389) B254389
theorem B568579 : Blo 223812 568579 := bstep (se 1 (by rfl) ⟨426434, by rfl⟩ : syracuseStep 568579 = 852869) B852869
theorem B339203 : Blo 223812 339203 := bstep (se 1 (by rfl) ⟨254402, by rfl⟩ : syracuseStep 339203 = 508805) B508805
theorem B339233 : Blo 223812 339233 := bstep (se 2 (by rfl) ⟨127212, by rfl⟩ : syracuseStep 339233 = 254425) B254425
theorem B765233 : Blo 223812 765233 := bstep (se 2 (by rfl) ⟨286962, by rfl⟩ : syracuseStep 765233 = 573925) B573925
theorem B339251 : Blo 223812 339251 := bstep (se 1 (by rfl) ⟨254438, by rfl⟩ : syracuseStep 339251 = 508877) B508877
theorem B339281 : Blo 223812 339281 := bstep (se 2 (by rfl) ⟨127230, by rfl⟩ : syracuseStep 339281 = 254461) B254461
theorem B339299 : Blo 223812 339299 := bstep (se 1 (by rfl) ⟨254474, by rfl⟩ : syracuseStep 339299 = 508949) B508949
theorem B2567537 : Blo 223812 2567537 := bstep (se 2 (by rfl) ⟨962826, by rfl⟩ : syracuseStep 2567537 = 1925653) B1925653
theorem B339329 : Blo 223812 339329 := bstep (se 2 (by rfl) ⟨127248, by rfl⟩ : syracuseStep 339329 = 254497) B254497
theorem B404867 : Blo 223812 404867 := bstep (se 1 (by rfl) ⟨303650, by rfl⟩ : syracuseStep 404867 = 607301) B607301
theorem B568721 : Blo 223812 568721 := bstep (se 2 (by rfl) ⟨213270, by rfl⟩ : syracuseStep 568721 = 426541) B426541
theorem B339347 : Blo 223812 339347 := bstep (se 1 (by rfl) ⟨254510, by rfl⟩ : syracuseStep 339347 = 509021) B509021
theorem B339377 : Blo 223812 339377 := bstep (se 2 (by rfl) ⟨127266, by rfl⟩ : syracuseStep 339377 = 254533) B254533
theorem B339395 : Blo 223812 339395 := bstep (se 1 (by rfl) ⟨254546, by rfl⟩ : syracuseStep 339395 = 509093) B509093
theorem B3452357 : Blo 223812 3452357 := bstep (se 4 (by rfl) ⟨323658, by rfl⟩ : syracuseStep 3452357 = 647317) B647317
theorem B339425 : Blo 223812 339425 := bstep (se 2 (by rfl) ⟨127284, by rfl⟩ : syracuseStep 339425 = 254569) B254569
theorem B863729 : Blo 223812 863729 := bstep (se 2 (by rfl) ⟨323898, by rfl⟩ : syracuseStep 863729 = 647797) B647797
theorem B339443 : Blo 223812 339443 := bstep (se 1 (by rfl) ⟨254582, by rfl⟩ : syracuseStep 339443 = 509165) B509165
theorem B339473 : Blo 223812 339473 := bstep (se 2 (by rfl) ⟨127302, by rfl⟩ : syracuseStep 339473 = 254605) B254605
theorem B339491 : Blo 223812 339491 := bstep (se 1 (by rfl) ⟨254618, by rfl⟩ : syracuseStep 339491 = 509237) B509237
theorem B339521 : Blo 223812 339521 := bstep (se 2 (by rfl) ⟨127320, by rfl⟩ : syracuseStep 339521 = 254641) B254641
theorem B339539 : Blo 223812 339539 := bstep (se 1 (by rfl) ⟨254654, by rfl⟩ : syracuseStep 339539 = 509309) B509309
theorem B405091 : Blo 223812 405091 := bstep (se 1 (by rfl) ⟨303818, by rfl⟩ : syracuseStep 405091 = 607637) B607637
theorem B339569 : Blo 223812 339569 := bstep (se 2 (by rfl) ⟨127338, by rfl⟩ : syracuseStep 339569 = 254677) B254677
theorem B339587 : Blo 223812 339587 := bstep (se 1 (by rfl) ⟨254690, by rfl⟩ : syracuseStep 339587 = 509381) B509381
theorem B339617 : Blo 223812 339617 := bstep (se 2 (by rfl) ⟨127356, by rfl⟩ : syracuseStep 339617 = 254713) B254713
theorem B339635 : Blo 223812 339635 := bstep (se 1 (by rfl) ⟨254726, by rfl⟩ : syracuseStep 339635 = 509453) B509453
theorem B306883 : Blo 223812 306883 := bstep (se 1 (by rfl) ⟨230162, by rfl⟩ : syracuseStep 306883 = 460325) B460325
theorem B339665 : Blo 223812 339665 := bstep (se 2 (by rfl) ⟨127374, by rfl⟩ : syracuseStep 339665 = 254749) B254749
theorem B339683 : Blo 223812 339683 := bstep (se 1 (by rfl) ⟨254762, by rfl⟩ : syracuseStep 339683 = 509525) B509525
theorem B339713 : Blo 223812 339713 := bstep (se 2 (by rfl) ⟨127392, by rfl⟩ : syracuseStep 339713 = 254785) B254785
theorem B339731 : Blo 223812 339731 := bstep (se 1 (by rfl) ⟨254798, by rfl⟩ : syracuseStep 339731 = 509597) B509597
theorem B339761 : Blo 223812 339761 := bstep (se 2 (by rfl) ⟨127410, by rfl⟩ : syracuseStep 339761 = 254821) B254821
theorem B339779 : Blo 223812 339779 := bstep (se 1 (by rfl) ⟨254834, by rfl⟩ : syracuseStep 339779 = 509669) B509669
theorem B765773 : Blo 223812 765773 := bstep (se 3 (by rfl) ⟨143582, by rfl⟩ : syracuseStep 765773 = 287165) B287165
theorem B339809 : Blo 223812 339809 := bstep (se 2 (by rfl) ⟨127428, by rfl⟩ : syracuseStep 339809 = 254857) B254857
theorem B962417 : Blo 223812 962417 := bstep (se 2 (by rfl) ⟨360906, by rfl⟩ : syracuseStep 962417 = 721813) B721813
theorem B339827 : Blo 223812 339827 := bstep (se 1 (by rfl) ⟨254870, by rfl⟩ : syracuseStep 339827 = 509741) B509741
theorem B765827 : Blo 223812 765827 := bstep (se 1 (by rfl) ⟨574370, by rfl⟩ : syracuseStep 765827 = 1148741) B1148741
theorem B339857 : Blo 223812 339857 := bstep (se 2 (by rfl) ⟨127446, by rfl⟩ : syracuseStep 339857 = 254893) B254893
theorem B339875 : Blo 223812 339875 := bstep (se 1 (by rfl) ⟨254906, by rfl⟩ : syracuseStep 339875 = 509813) B509813
theorem B503729 : Blo 223812 503729 := bstep (se 2 (by rfl) ⟨188898, by rfl⟩ : syracuseStep 503729 = 377797) B377797
theorem B339905 : Blo 223812 339905 := bstep (se 2 (by rfl) ⟨127464, by rfl⟩ : syracuseStep 339905 = 254929) B254929
theorem B503747 : Blo 223812 503747 := bstep (se 1 (by rfl) ⟨377810, by rfl⟩ : syracuseStep 503747 = 755621) B755621
theorem B339923 : Blo 223812 339923 := bstep (se 1 (by rfl) ⟨254942, by rfl⟩ : syracuseStep 339923 = 509885) B509885
theorem B339953 : Blo 223812 339953 := bstep (se 2 (by rfl) ⟨127482, by rfl⟩ : syracuseStep 339953 = 254965) B254965
theorem B339971 : Blo 223812 339971 := bstep (se 1 (by rfl) ⟨254978, by rfl⟩ : syracuseStep 339971 = 509957) B509957
theorem B340001 : Blo 223812 340001 := bstep (se 2 (by rfl) ⟨127500, by rfl⟩ : syracuseStep 340001 = 255001) B255001
theorem B241715 : Blo 223812 241715 := bstep (se 1 (by rfl) ⟨181286, by rfl⟩ : syracuseStep 241715 = 362573) B362573
theorem B340019 : Blo 223812 340019 := bstep (se 1 (by rfl) ⟨255014, by rfl⟩ : syracuseStep 340019 = 510029) B510029
theorem B340049 : Blo 223812 340049 := bstep (se 2 (by rfl) ⟨127518, by rfl⟩ : syracuseStep 340049 = 255037) B255037
theorem B340067 : Blo 223812 340067 := bstep (se 1 (by rfl) ⟨255050, by rfl⟩ : syracuseStep 340067 = 510101) B510101
theorem B340097 : Blo 223812 340097 := bstep (se 2 (by rfl) ⟨127536, by rfl⟩ : syracuseStep 340097 = 255073) B255073
theorem B766097 : Blo 223812 766097 := bstep (se 2 (by rfl) ⟨287286, by rfl⟩ : syracuseStep 766097 = 574573) B574573
theorem B340115 : Blo 223812 340115 := bstep (se 1 (by rfl) ⟨255086, by rfl⟩ : syracuseStep 340115 = 510173) B510173
theorem B340145 : Blo 223812 340145 := bstep (se 2 (by rfl) ⟨127554, by rfl⟩ : syracuseStep 340145 = 255109) B255109
theorem B340163 : Blo 223812 340163 := bstep (se 1 (by rfl) ⟨255122, by rfl⟩ : syracuseStep 340163 = 510245) B510245
theorem B504017 : Blo 223812 504017 := bstep (se 2 (by rfl) ⟨189006, by rfl⟩ : syracuseStep 504017 = 378013) B378013
theorem B340193 : Blo 223812 340193 := bstep (se 2 (by rfl) ⟨127572, by rfl⟩ : syracuseStep 340193 = 255145) B255145
theorem B504035 : Blo 223812 504035 := bstep (se 1 (by rfl) ⟨378026, by rfl⟩ : syracuseStep 504035 = 756053) B756053
theorem B340211 : Blo 223812 340211 := bstep (se 1 (by rfl) ⟨255158, by rfl⟩ : syracuseStep 340211 = 510317) B510317
theorem B2175245 : Blo 223812 2175245 := bstep (se 3 (by rfl) ⟨407858, by rfl⟩ : syracuseStep 2175245 = 815717) B815717
theorem B340241 : Blo 223812 340241 := bstep (se 2 (by rfl) ⟨127590, by rfl⟩ : syracuseStep 340241 = 255181) B255181
theorem B340259 : Blo 223812 340259 := bstep (se 1 (by rfl) ⟨255194, by rfl⟩ : syracuseStep 340259 = 510389) B510389
theorem B340289 : Blo 223812 340289 := bstep (se 2 (by rfl) ⟨127608, by rfl⟩ : syracuseStep 340289 = 255217) B255217
theorem B340307 : Blo 223812 340307 := bstep (se 1 (by rfl) ⟨255230, by rfl⟩ : syracuseStep 340307 = 510461) B510461
theorem B340337 : Blo 223812 340337 := bstep (se 2 (by rfl) ⟨127626, by rfl⟩ : syracuseStep 340337 = 255253) B255253
theorem B1618289 : Blo 223812 1618289 := bstep (se 2 (by rfl) ⟨606858, by rfl⟩ : syracuseStep 1618289 = 1213717) B1213717
theorem B569713 : Blo 223812 569713 := bstep (se 2 (by rfl) ⟨213642, by rfl⟩ : syracuseStep 569713 = 427285) B427285
theorem B340355 : Blo 223812 340355 := bstep (se 1 (by rfl) ⟨255266, by rfl⟩ : syracuseStep 340355 = 510533) B510533
theorem B340385 : Blo 223812 340385 := bstep (se 2 (by rfl) ⟨127644, by rfl⟩ : syracuseStep 340385 = 255289) B255289
theorem B340403 : Blo 223812 340403 := bstep (se 1 (by rfl) ⟨255302, by rfl⟩ : syracuseStep 340403 = 510605) B510605
theorem B340433 : Blo 223812 340433 := bstep (se 2 (by rfl) ⟨127662, by rfl⟩ : syracuseStep 340433 = 255325) B255325
theorem B340451 : Blo 223812 340451 := bstep (se 1 (by rfl) ⟨255338, by rfl⟩ : syracuseStep 340451 = 510677) B510677
theorem B504305 : Blo 223812 504305 := bstep (se 2 (by rfl) ⟨189114, by rfl⟩ : syracuseStep 504305 = 378229) B378229
theorem B340481 : Blo 223812 340481 := bstep (se 2 (by rfl) ⟨127680, by rfl⟩ : syracuseStep 340481 = 255361) B255361
theorem B504323 : Blo 223812 504323 := bstep (se 1 (by rfl) ⟨378242, by rfl⟩ : syracuseStep 504323 = 756485) B756485
theorem B1454597 : Blo 223812 1454597 := bstep (se 4 (by rfl) ⟨136368, by rfl⟩ : syracuseStep 1454597 = 272737) B272737
theorem B340499 : Blo 223812 340499 := bstep (se 1 (by rfl) ⟨255374, by rfl⟩ : syracuseStep 340499 = 510749) B510749
theorem B340529 : Blo 223812 340529 := bstep (se 2 (by rfl) ⟨127698, by rfl⟩ : syracuseStep 340529 = 255397) B255397
theorem B340547 : Blo 223812 340547 := bstep (se 1 (by rfl) ⟨255410, by rfl⟩ : syracuseStep 340547 = 510821) B510821
theorem B340561 : Blo 223812 340561 := bstep (se 2 (by rfl) ⟨127710, by rfl⟩ : syracuseStep 340561 = 255421) B255421
theorem B340577 : Blo 223812 340577 := bstep (se 2 (by rfl) ⟨127716, by rfl⟩ : syracuseStep 340577 = 255433) B255433
theorem B406129 : Blo 223812 406129 := bstep (se 2 (by rfl) ⟨152298, by rfl⟩ : syracuseStep 406129 = 304597) B304597
theorem B340595 : Blo 223812 340595 := bstep (se 1 (by rfl) ⟨255446, by rfl⟩ : syracuseStep 340595 = 510893) B510893
theorem B569987 : Blo 223812 569987 := bstep (se 1 (by rfl) ⟨427490, by rfl⟩ : syracuseStep 569987 = 854981) B854981
theorem B340625 : Blo 223812 340625 := bstep (se 2 (by rfl) ⟨127734, by rfl⟩ : syracuseStep 340625 = 255469) B255469
theorem B340643 : Blo 223812 340643 := bstep (se 1 (by rfl) ⟨255482, by rfl⟩ : syracuseStep 340643 = 510965) B510965
theorem B766637 : Blo 223812 766637 := bstep (se 3 (by rfl) ⟨143744, by rfl⟩ : syracuseStep 766637 = 287489) B287489
theorem B340673 : Blo 223812 340673 := bstep (se 2 (by rfl) ⟨127752, by rfl⟩ : syracuseStep 340673 = 255505) B255505
theorem B340691 : Blo 223812 340691 := bstep (se 1 (by rfl) ⟨255518, by rfl⟩ : syracuseStep 340691 = 511037) B511037
theorem B766691 : Blo 223812 766691 := bstep (se 1 (by rfl) ⟨575018, by rfl⟩ : syracuseStep 766691 = 1150037) B1150037
theorem B340721 : Blo 223812 340721 := bstep (se 2 (by rfl) ⟨127770, by rfl⟩ : syracuseStep 340721 = 255541) B255541
theorem B340739 : Blo 223812 340739 := bstep (se 1 (by rfl) ⟨255554, by rfl⟩ : syracuseStep 340739 = 511109) B511109
theorem B504593 : Blo 223812 504593 := bstep (se 2 (by rfl) ⟨189222, by rfl⟩ : syracuseStep 504593 = 378445) B378445
theorem B340769 : Blo 223812 340769 := bstep (se 2 (by rfl) ⟨127788, by rfl⟩ : syracuseStep 340769 = 255577) B255577
theorem B504611 : Blo 223812 504611 := bstep (se 1 (by rfl) ⟨378458, by rfl⟩ : syracuseStep 504611 = 756917) B756917
theorem B275251 : Blo 223812 275251 := bstep (se 1 (by rfl) ⟨206438, by rfl⟩ : syracuseStep 275251 = 412877) B412877
theorem B340787 : Blo 223812 340787 := bstep (se 1 (by rfl) ⟨255590, by rfl⟩ : syracuseStep 340787 = 511181) B511181
theorem B5813045 : Blo 223812 5813045 := bstep (se 5 (by rfl) ⟨272486, by rfl⟩ : syracuseStep 5813045 = 544973) B544973
theorem B570179 : Blo 223812 570179 := bstep (se 1 (by rfl) ⟨427634, by rfl⟩ : syracuseStep 570179 = 855269) B855269
theorem B340817 : Blo 223812 340817 := bstep (se 2 (by rfl) ⟨127806, by rfl⟩ : syracuseStep 340817 = 255613) B255613
theorem B340835 : Blo 223812 340835 := bstep (se 1 (by rfl) ⟨255626, by rfl⟩ : syracuseStep 340835 = 511253) B511253
theorem B340865 : Blo 223812 340865 := bstep (se 2 (by rfl) ⟨127824, by rfl⟩ : syracuseStep 340865 = 255649) B255649
theorem B340883 : Blo 223812 340883 := bstep (se 1 (by rfl) ⟨255662, by rfl⟩ : syracuseStep 340883 = 511325) B511325
theorem B340913 : Blo 223812 340913 := bstep (se 2 (by rfl) ⟨127842, by rfl⟩ : syracuseStep 340913 = 255685) B255685
theorem B340931 : Blo 223812 340931 := bstep (se 1 (by rfl) ⟨255698, by rfl⟩ : syracuseStep 340931 = 511397) B511397
theorem B340961 : Blo 223812 340961 := bstep (se 2 (by rfl) ⟨127860, by rfl⟩ : syracuseStep 340961 = 255721) B255721
theorem B766961 : Blo 223812 766961 := bstep (se 2 (by rfl) ⟨287610, by rfl⟩ : syracuseStep 766961 = 575221) B575221
theorem B340979 : Blo 223812 340979 := bstep (se 1 (by rfl) ⟨255734, by rfl⟩ : syracuseStep 340979 = 511469) B511469
theorem B341009 : Blo 223812 341009 := bstep (se 2 (by rfl) ⟨127878, by rfl⟩ : syracuseStep 341009 = 255757) B255757
theorem B242723 : Blo 223812 242723 := bstep (se 1 (by rfl) ⟨182042, by rfl⟩ : syracuseStep 242723 = 364085) B364085
theorem B341027 : Blo 223812 341027 := bstep (se 1 (by rfl) ⟨255770, by rfl⟩ : syracuseStep 341027 = 511541) B511541
theorem B504881 : Blo 223812 504881 := bstep (se 2 (by rfl) ⟨189330, by rfl⟩ : syracuseStep 504881 = 378661) B378661
theorem B341057 : Blo 223812 341057 := bstep (se 2 (by rfl) ⟨127896, by rfl⟩ : syracuseStep 341057 = 255793) B255793
theorem B504899 : Blo 223812 504899 := bstep (se 1 (by rfl) ⟨378674, by rfl⟩ : syracuseStep 504899 = 757349) B757349
theorem B341075 : Blo 223812 341075 := bstep (se 1 (by rfl) ⟨255806, by rfl⟩ : syracuseStep 341075 = 511613) B511613
theorem B963683 : Blo 223812 963683 := bstep (se 1 (by rfl) ⟨722762, by rfl⟩ : syracuseStep 963683 = 1445525) B1445525
theorem B341105 : Blo 223812 341105 := bstep (se 2 (by rfl) ⟨127914, by rfl⟩ : syracuseStep 341105 = 255829) B255829
theorem B341123 : Blo 223812 341123 := bstep (se 1 (by rfl) ⟨255842, by rfl⟩ : syracuseStep 341123 = 511685) B511685
theorem B341153 : Blo 223812 341153 := bstep (se 2 (by rfl) ⟨127932, by rfl⟩ : syracuseStep 341153 = 255865) B255865
theorem B341171 : Blo 223812 341171 := bstep (se 1 (by rfl) ⟨255878, by rfl⟩ : syracuseStep 341171 = 511757) B511757
theorem B341201 : Blo 223812 341201 := bstep (se 2 (by rfl) ⟨127950, by rfl⟩ : syracuseStep 341201 = 255901) B255901
theorem B341219 : Blo 223812 341219 := bstep (se 1 (by rfl) ⟨255914, by rfl⟩ : syracuseStep 341219 = 511829) B511829
theorem B341249 : Blo 223812 341249 := bstep (se 2 (by rfl) ⟨127968, by rfl⟩ : syracuseStep 341249 = 255937) B255937
theorem B341267 : Blo 223812 341267 := bstep (se 1 (by rfl) ⟨255950, by rfl⟩ : syracuseStep 341267 = 511901) B511901
theorem B341297 : Blo 223812 341297 := bstep (se 2 (by rfl) ⟨127986, by rfl⟩ : syracuseStep 341297 = 255973) B255973
theorem B341315 : Blo 223812 341315 := bstep (se 1 (by rfl) ⟨255986, by rfl⟩ : syracuseStep 341315 = 511973) B511973
theorem B505169 : Blo 223812 505169 := bstep (se 2 (by rfl) ⟨189438, by rfl⟩ : syracuseStep 505169 = 378877) B378877
theorem B341345 : Blo 223812 341345 := bstep (se 2 (by rfl) ⟨128004, by rfl⟩ : syracuseStep 341345 = 256009) B256009
theorem B505187 : Blo 223812 505187 := bstep (se 1 (by rfl) ⟨378890, by rfl⟩ : syracuseStep 505187 = 757781) B757781
theorem B341363 : Blo 223812 341363 := bstep (se 1 (by rfl) ⟨256022, by rfl⟩ : syracuseStep 341363 = 512045) B512045
theorem B341393 : Blo 223812 341393 := bstep (se 2 (by rfl) ⟨128022, by rfl⟩ : syracuseStep 341393 = 256045) B256045
theorem B341411 : Blo 223812 341411 := bstep (se 1 (by rfl) ⟨256058, by rfl⟩ : syracuseStep 341411 = 512117) B512117
theorem B1291697 : Blo 223812 1291697 := bstep (se 2 (by rfl) ⟨484386, by rfl⟩ : syracuseStep 1291697 = 968773) B968773
theorem B341441 : Blo 223812 341441 := bstep (se 2 (by rfl) ⟨128040, by rfl⟩ : syracuseStep 341441 = 256081) B256081
theorem B341459 : Blo 223812 341459 := bstep (se 1 (by rfl) ⟨256094, by rfl⟩ : syracuseStep 341459 = 512189) B512189
theorem B341489 : Blo 223812 341489 := bstep (se 2 (by rfl) ⟨128058, by rfl⟩ : syracuseStep 341489 = 256117) B256117
theorem B341507 : Blo 223812 341507 := bstep (se 1 (by rfl) ⟨256130, by rfl⟩ : syracuseStep 341507 = 512261) B512261
theorem B767501 : Blo 223812 767501 := bstep (se 3 (by rfl) ⟨143906, by rfl⟩ : syracuseStep 767501 = 287813) B287813
theorem B341537 : Blo 223812 341537 := bstep (se 2 (by rfl) ⟨128076, by rfl⟩ : syracuseStep 341537 = 256153) B256153
theorem B341555 : Blo 223812 341555 := bstep (se 1 (by rfl) ⟨256166, by rfl⟩ : syracuseStep 341555 = 512333) B512333
theorem B767555 : Blo 223812 767555 := bstep (se 1 (by rfl) ⟨575666, by rfl⟩ : syracuseStep 767555 = 1151333) B1151333
theorem B341585 : Blo 223812 341585 := bstep (se 2 (by rfl) ⟨128094, by rfl⟩ : syracuseStep 341585 = 256189) B256189
theorem B341603 : Blo 223812 341603 := bstep (se 1 (by rfl) ⟨256202, by rfl⟩ : syracuseStep 341603 = 512405) B512405
theorem B505457 : Blo 223812 505457 := bstep (se 2 (by rfl) ⟨189546, by rfl⟩ : syracuseStep 505457 = 379093) B379093
theorem B341633 : Blo 223812 341633 := bstep (se 2 (by rfl) ⟨128112, by rfl⟩ : syracuseStep 341633 = 256225) B256225
theorem B505475 : Blo 223812 505475 := bstep (se 1 (by rfl) ⟨379106, by rfl⟩ : syracuseStep 505475 = 758213) B758213
theorem B341651 : Blo 223812 341651 := bstep (se 1 (by rfl) ⟨256238, by rfl⟩ : syracuseStep 341651 = 512477) B512477
theorem B341681 : Blo 223812 341681 := bstep (se 2 (by rfl) ⟨128130, by rfl⟩ : syracuseStep 341681 = 256261) B256261
theorem B341699 : Blo 223812 341699 := bstep (se 1 (by rfl) ⟨256274, by rfl⟩ : syracuseStep 341699 = 512549) B512549
theorem B341729 : Blo 223812 341729 := bstep (se 2 (by rfl) ⟨128148, by rfl⟩ : syracuseStep 341729 = 256297) B256297
theorem B571121 : Blo 223812 571121 := bstep (se 2 (by rfl) ⟨214170, by rfl⟩ : syracuseStep 571121 = 428341) B428341
theorem B571171 : Blo 223812 571171 := bstep (se 1 (by rfl) ⟨428378, by rfl⟩ : syracuseStep 571171 = 856757) B856757
theorem B767825 : Blo 223812 767825 := bstep (se 2 (by rfl) ⟨287934, by rfl⟩ : syracuseStep 767825 = 575869) B575869
theorem B505745 : Blo 223812 505745 := bstep (se 2 (by rfl) ⟨189654, by rfl⟩ : syracuseStep 505745 = 379309) B379309
theorem B505763 : Blo 223812 505763 := bstep (se 1 (by rfl) ⟨379322, by rfl⟩ : syracuseStep 505763 = 758645) B758645
theorem B571313 : Blo 223812 571313 := bstep (se 2 (by rfl) ⟨214242, by rfl⟩ : syracuseStep 571313 = 428485) B428485
theorem B506033 : Blo 223812 506033 := bstep (se 2 (by rfl) ⟨189762, by rfl⟩ : syracuseStep 506033 = 379525) B379525
theorem B506051 : Blo 223812 506051 := bstep (se 1 (by rfl) ⟨379538, by rfl⟩ : syracuseStep 506051 = 759077) B759077
theorem B768365 : Blo 223812 768365 := bstep (se 3 (by rfl) ⟨144068, by rfl⟩ : syracuseStep 768365 = 288137) B288137
theorem B768419 : Blo 223812 768419 := bstep (se 1 (by rfl) ⟨576314, by rfl⟩ : syracuseStep 768419 = 1152629) B1152629
theorem B506321 : Blo 223812 506321 := bstep (se 2 (by rfl) ⟨189870, by rfl⟩ : syracuseStep 506321 = 379741) B379741
theorem B506339 : Blo 223812 506339 := bstep (se 1 (by rfl) ⟨379754, by rfl⟩ : syracuseStep 506339 = 759509) B759509
theorem B735875 : Blo 223812 735875 := bstep (se 1 (by rfl) ⟨551906, by rfl⟩ : syracuseStep 735875 = 1103813) B1103813
theorem B768689 : Blo 223812 768689 := bstep (se 2 (by rfl) ⟨288258, by rfl⟩ : syracuseStep 768689 = 576517) B576517
theorem B1718981 : Blo 223812 1718981 := bstep (se 4 (by rfl) ⟨161154, by rfl⟩ : syracuseStep 1718981 = 322309) B322309
theorem B4668101 : Blo 223812 4668101 := bstep (se 4 (by rfl) ⟨437634, by rfl⟩ : syracuseStep 4668101 = 875269) B875269
theorem B277219 : Blo 223812 277219 := bstep (se 1 (by rfl) ⟨207914, by rfl⟩ : syracuseStep 277219 = 415829) B415829
theorem B506609 : Blo 223812 506609 := bstep (se 2 (by rfl) ⟨189978, by rfl⟩ : syracuseStep 506609 = 379957) B379957
theorem B506627 : Blo 223812 506627 := bstep (se 1 (by rfl) ⟨379970, by rfl⟩ : syracuseStep 506627 = 759941) B759941
theorem B342787 : Blo 223812 342787 := bstep (se 1 (by rfl) ⟨257090, by rfl⟩ : syracuseStep 342787 = 514181) B514181
theorem B1293155 : Blo 223812 1293155 := bstep (se 1 (by rfl) ⟨969866, by rfl⟩ : syracuseStep 1293155 = 1939733) B1939733
theorem B572305 : Blo 223812 572305 := bstep (se 2 (by rfl) ⟨214614, by rfl⟩ : syracuseStep 572305 = 429229) B429229
theorem B506897 : Blo 223812 506897 := bstep (se 2 (by rfl) ⟨190086, by rfl⟩ : syracuseStep 506897 = 380173) B380173
theorem B506915 : Blo 223812 506915 := bstep (se 1 (by rfl) ⟨380186, by rfl⟩ : syracuseStep 506915 = 760373) B760373
theorem B572579 : Blo 223812 572579 := bstep (se 1 (by rfl) ⟨429434, by rfl⟩ : syracuseStep 572579 = 858869) B858869
theorem B408817 : Blo 223812 408817 := bstep (se 2 (by rfl) ⟨153306, by rfl⟩ : syracuseStep 408817 = 306613) B306613
theorem B539939 : Blo 223812 539939 := bstep (se 1 (by rfl) ⟨404954, by rfl⟩ : syracuseStep 539939 = 809909) B809909
theorem B507185 : Blo 223812 507185 := bstep (se 2 (by rfl) ⟨190194, by rfl⟩ : syracuseStep 507185 = 380389) B380389
theorem B507203 : Blo 223812 507203 := bstep (se 1 (by rfl) ⟨380402, by rfl⟩ : syracuseStep 507203 = 760805) B760805
theorem B572771 : Blo 223812 572771 := bstep (se 1 (by rfl) ⟨429578, by rfl⟩ : syracuseStep 572771 = 859157) B859157
theorem B605681 : Blo 223812 605681 := bstep (se 2 (by rfl) ⟨227130, by rfl⟩ : syracuseStep 605681 = 454261) B454261
theorem B638513 : Blo 223812 638513 := bstep (se 2 (by rfl) ⟨239442, by rfl⟩ : syracuseStep 638513 = 478885) B478885
theorem B507473 : Blo 223812 507473 := bstep (se 2 (by rfl) ⟨190302, by rfl⟩ : syracuseStep 507473 = 380605) B380605
theorem B507491 : Blo 223812 507491 := bstep (se 1 (by rfl) ⟨380618, by rfl⟩ : syracuseStep 507491 = 761237) B761237
theorem B540323 : Blo 223812 540323 := bstep (se 1 (by rfl) ⟨405242, by rfl⟩ : syracuseStep 540323 = 810485) B810485
theorem B409379 : Blo 223812 409379 := bstep (se 1 (by rfl) ⟨307034, by rfl⟩ : syracuseStep 409379 = 614069) B614069
theorem B1294157 : Blo 223812 1294157 := bstep (se 3 (by rfl) ⟨242654, by rfl⟩ : syracuseStep 1294157 = 485309) B485309
theorem B507761 : Blo 223812 507761 := bstep (se 2 (by rfl) ⟨190410, by rfl⟩ : syracuseStep 507761 = 380821) B380821
theorem B507779 : Blo 223812 507779 := bstep (se 1 (by rfl) ⟨380834, by rfl⟩ : syracuseStep 507779 = 761669) B761669
theorem B540611 : Blo 223812 540611 := bstep (se 1 (by rfl) ⟨405458, by rfl⟩ : syracuseStep 540611 = 810917) B810917
theorem B1458161 : Blo 223812 1458161 := bstep (se 2 (by rfl) ⟨546810, by rfl⟩ : syracuseStep 1458161 = 1093621) B1093621
theorem B508049 : Blo 223812 508049 := bstep (se 2 (by rfl) ⟨190518, by rfl⟩ : syracuseStep 508049 = 381037) B381037
theorem B508067 : Blo 223812 508067 := bstep (se 1 (by rfl) ⟨381050, by rfl⟩ : syracuseStep 508067 = 762101) B762101
theorem B409841 : Blo 223812 409841 := bstep (se 2 (by rfl) ⟨153690, by rfl⟩ : syracuseStep 409841 = 307381) B307381
theorem B573713 : Blo 223812 573713 := bstep (se 2 (by rfl) ⟨215142, by rfl⟩ : syracuseStep 573713 = 430285) B430285
theorem B573763 : Blo 223812 573763 := bstep (se 1 (by rfl) ⟨430322, by rfl⟩ : syracuseStep 573763 = 860645) B860645
theorem B541073 : Blo 223812 541073 := bstep (se 2 (by rfl) ⟨202902, by rfl⟩ : syracuseStep 541073 = 405805) B405805
theorem B508337 : Blo 223812 508337 := bstep (se 2 (by rfl) ⟨190626, by rfl⟩ : syracuseStep 508337 = 381253) B381253
theorem B508355 : Blo 223812 508355 := bstep (se 1 (by rfl) ⟨381266, by rfl⟩ : syracuseStep 508355 = 762533) B762533
theorem B573905 : Blo 223812 573905 := bstep (se 2 (by rfl) ⟨215214, by rfl⟩ : syracuseStep 573905 = 430429) B430429
theorem B967373 : Blo 223812 967373 := bstep (se 3 (by rfl) ⟨181382, by rfl⟩ : syracuseStep 967373 = 362765) B362765
theorem B508625 : Blo 223812 508625 := bstep (se 2 (by rfl) ⟨190734, by rfl⟩ : syracuseStep 508625 = 381469) B381469
theorem B508643 : Blo 223812 508643 := bstep (se 1 (by rfl) ⟨381482, by rfl⟩ : syracuseStep 508643 = 762965) B762965
theorem B344819 : Blo 223812 344819 := bstep (se 1 (by rfl) ⟨258614, by rfl⟩ : syracuseStep 344819 = 517229) B517229
theorem B377777 : Blo 223812 377777 := bstep (se 2 (by rfl) ⟨141666, by rfl⟩ : syracuseStep 377777 = 283333) B283333
theorem B639971 : Blo 223812 639971 := bstep (se 1 (by rfl) ⟨479978, by rfl⟩ : syracuseStep 639971 = 959957) B959957
theorem B508913 : Blo 223812 508913 := bstep (se 2 (by rfl) ⟨190842, by rfl⟩ : syracuseStep 508913 = 381685) B381685
theorem B508931 : Blo 223812 508931 := bstep (se 1 (by rfl) ⟨381698, by rfl⟩ : syracuseStep 508931 = 763397) B763397
theorem B377905 : Blo 223812 377905 := bstep (se 2 (by rfl) ⟨141714, by rfl⟩ : syracuseStep 377905 = 283429) B283429
theorem B541745 : Blo 223812 541745 := bstep (se 2 (by rfl) ⟨203154, by rfl⟩ : syracuseStep 541745 = 406309) B406309
theorem B377939 : Blo 223812 377939 := bstep (se 1 (by rfl) ⟨283454, by rfl⟩ : syracuseStep 377939 = 566909) B566909
theorem B378067 : Blo 223812 378067 := bstep (se 1 (by rfl) ⟨283550, by rfl⟩ : syracuseStep 378067 = 567101) B567101
theorem B509201 : Blo 223812 509201 := bstep (se 2 (by rfl) ⟨190950, by rfl⟩ : syracuseStep 509201 = 381901) B381901
theorem B509219 : Blo 223812 509219 := bstep (se 1 (by rfl) ⟨381914, by rfl⟩ : syracuseStep 509219 = 763829) B763829
theorem B2934085 : Blo 223812 2934085 := bstep (se 4 (by rfl) ⟨275070, by rfl⟩ : syracuseStep 2934085 = 550141) B550141
theorem B378209 : Blo 223812 378209 := bstep (se 2 (by rfl) ⟨141828, by rfl⟩ : syracuseStep 378209 = 283657) B283657
theorem B1459619 : Blo 223812 1459619 := bstep (se 1 (by rfl) ⟨1094714, by rfl⟩ : syracuseStep 1459619 = 2189429) B2189429
theorem B574897 : Blo 223812 574897 := bstep (se 2 (by rfl) ⟨215586, by rfl⟩ : syracuseStep 574897 = 431173) B431173
theorem B378337 : Blo 223812 378337 := bstep (se 2 (by rfl) ⟨141876, by rfl⟩ : syracuseStep 378337 = 283753) B283753
theorem B378371 : Blo 223812 378371 := bstep (se 1 (by rfl) ⟨283778, by rfl⟩ : syracuseStep 378371 = 567557) B567557
theorem B509489 : Blo 223812 509489 := bstep (se 2 (by rfl) ⟨191058, by rfl⟩ : syracuseStep 509489 = 382117) B382117
theorem B509507 : Blo 223812 509507 := bstep (se 1 (by rfl) ⟨382130, by rfl⟩ : syracuseStep 509507 = 764261) B764261
theorem B869987 : Blo 223812 869987 := bstep (se 1 (by rfl) ⟨652490, by rfl⟩ : syracuseStep 869987 = 1304981) B1304981
theorem B378499 : Blo 223812 378499 := bstep (se 1 (by rfl) ⟨283874, by rfl⟩ : syracuseStep 378499 = 567749) B567749
theorem B575171 : Blo 223812 575171 := bstep (se 1 (by rfl) ⟨431378, by rfl⟩ : syracuseStep 575171 = 862757) B862757
theorem B640781 : Blo 223812 640781 := bstep (se 3 (by rfl) ⟨120146, by rfl⟩ : syracuseStep 640781 = 240293) B240293
theorem B378641 : Blo 223812 378641 := bstep (se 2 (by rfl) ⟨141990, by rfl⟩ : syracuseStep 378641 = 283981) B283981
theorem B509777 : Blo 223812 509777 := bstep (se 2 (by rfl) ⟨191166, by rfl⟩ : syracuseStep 509777 = 382333) B382333
theorem B509795 : Blo 223812 509795 := bstep (se 1 (by rfl) ⟨382346, by rfl⟩ : syracuseStep 509795 = 764693) B764693
theorem B575363 : Blo 223812 575363 := bstep (se 1 (by rfl) ⟨431522, by rfl⟩ : syracuseStep 575363 = 863045) B863045
theorem B378769 : Blo 223812 378769 := bstep (se 2 (by rfl) ⟨142038, by rfl⟩ : syracuseStep 378769 = 284077) B284077
theorem B378803 : Blo 223812 378803 := bstep (se 1 (by rfl) ⟨284102, by rfl⟩ : syracuseStep 378803 = 568205) B568205
theorem B640973 : Blo 223812 640973 := bstep (se 3 (by rfl) ⟨120182, by rfl⟩ : syracuseStep 640973 = 240365) B240365
theorem B739277 : Blo 223812 739277 := bstep (se 3 (by rfl) ⟨138614, by rfl⟩ : syracuseStep 739277 = 277229) B277229
theorem B378931 : Blo 223812 378931 := bstep (se 1 (by rfl) ⟨284198, by rfl⟩ : syracuseStep 378931 = 568397) B568397
theorem B510065 : Blo 223812 510065 := bstep (se 2 (by rfl) ⟨191274, by rfl⟩ : syracuseStep 510065 = 382549) B382549
theorem B510083 : Blo 223812 510083 := bstep (se 1 (by rfl) ⟨382562, by rfl⟩ : syracuseStep 510083 = 765125) B765125
theorem B739459 : Blo 223812 739459 := bstep (se 1 (by rfl) ⟨554594, by rfl⟩ : syracuseStep 739459 = 1109189) B1109189
theorem B379073 : Blo 223812 379073 := bstep (se 2 (by rfl) ⟨142152, by rfl⟩ : syracuseStep 379073 = 284305) B284305
theorem B379201 : Blo 223812 379201 := bstep (se 2 (by rfl) ⟨142200, by rfl⟩ : syracuseStep 379201 = 284401) B284401
theorem B379235 : Blo 223812 379235 := bstep (se 1 (by rfl) ⟨284426, by rfl⟩ : syracuseStep 379235 = 568853) B568853
theorem B510353 : Blo 223812 510353 := bstep (se 2 (by rfl) ⟨191382, by rfl⟩ : syracuseStep 510353 = 382765) B382765
theorem B510371 : Blo 223812 510371 := bstep (se 1 (by rfl) ⟨382778, by rfl⟩ : syracuseStep 510371 = 765557) B765557
theorem B379363 : Blo 223812 379363 := bstep (se 1 (by rfl) ⟨284522, by rfl⟩ : syracuseStep 379363 = 569045) B569045
theorem B608771 : Blo 223812 608771 := bstep (se 1 (by rfl) ⟨456578, by rfl⟩ : syracuseStep 608771 = 913157) B913157
theorem B379505 : Blo 223812 379505 := bstep (se 2 (by rfl) ⟨142314, by rfl⟩ : syracuseStep 379505 = 284629) B284629
theorem B510641 : Blo 223812 510641 := bstep (se 2 (by rfl) ⟨191490, by rfl⟩ : syracuseStep 510641 = 382981) B382981
theorem B1297073 : Blo 223812 1297073 := bstep (se 2 (by rfl) ⟨486402, by rfl⟩ : syracuseStep 1297073 = 972805) B972805
theorem B510659 : Blo 223812 510659 := bstep (se 1 (by rfl) ⟨382994, by rfl⟩ : syracuseStep 510659 = 765989) B765989
theorem B379633 : Blo 223812 379633 := bstep (se 2 (by rfl) ⟨142362, by rfl⟩ : syracuseStep 379633 = 284725) B284725
theorem B379667 : Blo 223812 379667 := bstep (se 1 (by rfl) ⟨284750, by rfl⟩ : syracuseStep 379667 = 569501) B569501
theorem B576305 : Blo 223812 576305 := bstep (se 2 (by rfl) ⟨216114, by rfl⟩ : syracuseStep 576305 = 432229) B432229
theorem B576355 : Blo 223812 576355 := bstep (se 1 (by rfl) ⟨432266, by rfl⟩ : syracuseStep 576355 = 864533) B864533
theorem B379795 : Blo 223812 379795 := bstep (se 1 (by rfl) ⟨284846, by rfl⟩ : syracuseStep 379795 = 569693) B569693
theorem B641965 : Blo 223812 641965 := bstep (se 3 (by rfl) ⟨120368, by rfl⟩ : syracuseStep 641965 = 240737) B240737
theorem B510929 : Blo 223812 510929 := bstep (se 2 (by rfl) ⟨191598, by rfl⟩ : syracuseStep 510929 = 383197) B383197
theorem B412643 : Blo 223812 412643 := bstep (se 1 (by rfl) ⟨309482, by rfl⟩ : syracuseStep 412643 = 618965) B618965
theorem B510947 : Blo 223812 510947 := bstep (se 1 (by rfl) ⟨383210, by rfl⟩ : syracuseStep 510947 = 766421) B766421
theorem B576497 : Blo 223812 576497 := bstep (se 2 (by rfl) ⟨216186, by rfl⟩ : syracuseStep 576497 = 432373) B432373
theorem B379937 : Blo 223812 379937 := bstep (se 2 (by rfl) ⟨142476, by rfl⟩ : syracuseStep 379937 = 284953) B284953
theorem B380065 : Blo 223812 380065 := bstep (se 2 (by rfl) ⟨142524, by rfl⟩ : syracuseStep 380065 = 285049) B285049
theorem B380099 : Blo 223812 380099 := bstep (se 1 (by rfl) ⟨285074, by rfl⟩ : syracuseStep 380099 = 570149) B570149
theorem B511217 : Blo 223812 511217 := bstep (se 2 (by rfl) ⟨191706, by rfl⟩ : syracuseStep 511217 = 383413) B383413
theorem B511235 : Blo 223812 511235 := bstep (se 1 (by rfl) ⟨383426, by rfl⟩ : syracuseStep 511235 = 766853) B766853
theorem B1133837 : Blo 223812 1133837 := bstep (se 3 (by rfl) ⟨212594, by rfl⟩ : syracuseStep 1133837 = 425189) B425189
theorem B380227 : Blo 223812 380227 := bstep (se 1 (by rfl) ⟨285170, by rfl⟩ : syracuseStep 380227 = 570341) B570341
theorem B3231089 : Blo 223812 3231089 := bstep (se 2 (by rfl) ⟨1211658, by rfl⟩ : syracuseStep 3231089 = 2423317) B2423317
theorem B609713 : Blo 223812 609713 := bstep (se 2 (by rfl) ⟨228642, by rfl⟩ : syracuseStep 609713 = 457285) B457285
theorem B380369 : Blo 223812 380369 := bstep (se 2 (by rfl) ⟨142638, by rfl⟩ : syracuseStep 380369 = 285277) B285277
theorem B511505 : Blo 223812 511505 := bstep (se 2 (by rfl) ⟨191814, by rfl⟩ : syracuseStep 511505 = 383629) B383629
theorem B511523 : Blo 223812 511523 := bstep (se 1 (by rfl) ⟨383642, by rfl⟩ : syracuseStep 511523 = 767285) B767285
theorem B380497 : Blo 223812 380497 := bstep (se 2 (by rfl) ⟨142686, by rfl⟩ : syracuseStep 380497 = 285373) B285373
theorem B380531 : Blo 223812 380531 := bstep (se 1 (by rfl) ⟨285398, by rfl⟩ : syracuseStep 380531 = 570797) B570797
theorem B970481 : Blo 223812 970481 := bstep (se 2 (by rfl) ⟨363930, by rfl⟩ : syracuseStep 970481 = 727861) B727861
theorem B380659 : Blo 223812 380659 := bstep (se 1 (by rfl) ⟨285494, by rfl⟩ : syracuseStep 380659 = 570989) B570989
theorem B511793 : Blo 223812 511793 := bstep (se 2 (by rfl) ⟨191922, by rfl⟩ : syracuseStep 511793 = 383845) B383845
theorem B511811 : Blo 223812 511811 := bstep (se 1 (by rfl) ⟨383858, by rfl⟩ : syracuseStep 511811 = 767717) B767717
theorem B2084707 : Blo 223812 2084707 := bstep (se 1 (by rfl) ⟨1563530, by rfl⟩ : syracuseStep 2084707 = 3127061) B3127061
theorem B380801 : Blo 223812 380801 := bstep (se 2 (by rfl) ⟨142800, by rfl⟩ : syracuseStep 380801 = 285601) B285601
theorem B380929 : Blo 223812 380929 := bstep (se 2 (by rfl) ⟨142848, by rfl⟩ : syracuseStep 380929 = 285697) B285697
theorem B380963 : Blo 223812 380963 := bstep (se 1 (by rfl) ⟨285722, by rfl⟩ : syracuseStep 380963 = 571445) B571445
theorem B512081 : Blo 223812 512081 := bstep (se 2 (by rfl) ⟨192030, by rfl⟩ : syracuseStep 512081 = 384061) B384061
theorem B512099 : Blo 223812 512099 := bstep (se 1 (by rfl) ⟨384074, by rfl⟩ : syracuseStep 512099 = 768149) B768149
theorem B479363 : Blo 223812 479363 := bstep (se 1 (by rfl) ⟨359522, by rfl⟩ : syracuseStep 479363 = 719045) B719045
theorem B381091 : Blo 223812 381091 := bstep (se 1 (by rfl) ⟨285818, by rfl⟩ : syracuseStep 381091 = 571637) B571637
theorem B381233 : Blo 223812 381233 := bstep (se 2 (by rfl) ⟨142962, by rfl⟩ : syracuseStep 381233 = 285925) B285925
theorem B610673 : Blo 223812 610673 := bstep (se 2 (by rfl) ⟨229002, by rfl⟩ : syracuseStep 610673 = 458005) B458005
theorem B512369 : Blo 223812 512369 := bstep (se 2 (by rfl) ⟨192138, by rfl⟩ : syracuseStep 512369 = 384277) B384277
theorem B512387 : Blo 223812 512387 := bstep (se 1 (by rfl) ⟨384290, by rfl⟩ : syracuseStep 512387 = 768581) B768581
theorem B1724813 : Blo 223812 1724813 := bstep (se 3 (by rfl) ⟨323402, by rfl⟩ : syracuseStep 1724813 = 646805) B646805
theorem B971149 : Blo 223812 971149 := bstep (se 3 (by rfl) ⟨182090, by rfl⟩ : syracuseStep 971149 = 364181) B364181
theorem B381361 : Blo 223812 381361 := bstep (se 2 (by rfl) ⟨143010, by rfl⟩ : syracuseStep 381361 = 286021) B286021
theorem B381395 : Blo 223812 381395 := bstep (se 1 (by rfl) ⟨286046, by rfl⟩ : syracuseStep 381395 = 572093) B572093
theorem B381523 : Blo 223812 381523 := bstep (se 1 (by rfl) ⟨286142, by rfl⟩ : syracuseStep 381523 = 572285) B572285
theorem B643697 : Blo 223812 643697 := bstep (se 2 (by rfl) ⟨241386, by rfl⟩ : syracuseStep 643697 = 482773) B482773
theorem B283267 : Blo 223812 283267 := bstep (se 1 (by rfl) ⟨212450, by rfl⟩ : syracuseStep 283267 = 424901) B424901
theorem B1168013 : Blo 223812 1168013 := bstep (se 3 (by rfl) ⟨219002, by rfl⟩ : syracuseStep 1168013 = 438005) B438005
theorem B381665 : Blo 223812 381665 := bstep (se 2 (by rfl) ⟨143124, by rfl⟩ : syracuseStep 381665 = 286249) B286249
theorem B643889 : Blo 223812 643889 := bstep (se 2 (by rfl) ⟨241458, by rfl⟩ : syracuseStep 643889 = 482917) B482917
theorem B381793 : Blo 223812 381793 := bstep (se 2 (by rfl) ⟨143172, by rfl⟩ : syracuseStep 381793 = 286345) B286345
theorem B1364849 : Blo 223812 1364849 := bstep (se 2 (by rfl) ⟨511818, by rfl⟩ : syracuseStep 1364849 = 1023637) B1023637
theorem B381827 : Blo 223812 381827 := bstep (se 1 (by rfl) ⟨286370, by rfl⟩ : syracuseStep 381827 = 572741) B572741
theorem B971747 : Blo 223812 971747 := bstep (se 1 (by rfl) ⟨728810, by rfl⟩ : syracuseStep 971747 = 1457621) B1457621
theorem B381955 : Blo 223812 381955 := bstep (se 1 (by rfl) ⟨286466, by rfl⟩ : syracuseStep 381955 = 572933) B572933
theorem B283763 : Blo 223812 283763 := bstep (se 1 (by rfl) ⟨212822, by rfl⟩ : syracuseStep 283763 = 425645) B425645
theorem B382097 : Blo 223812 382097 := bstep (se 2 (by rfl) ⟨143286, by rfl⟩ : syracuseStep 382097 = 286573) B286573
theorem B808177 : Blo 223812 808177 := bstep (se 2 (by rfl) ⟨303066, by rfl⟩ : syracuseStep 808177 = 606133) B606133
theorem B382225 : Blo 223812 382225 := bstep (se 2 (by rfl) ⟨143334, by rfl⟩ : syracuseStep 382225 = 286669) B286669
theorem B382259 : Blo 223812 382259 := bstep (se 1 (by rfl) ⟨286694, by rfl⟩ : syracuseStep 382259 = 573389) B573389
theorem B382387 : Blo 223812 382387 := bstep (se 1 (by rfl) ⟨286790, by rfl⟩ : syracuseStep 382387 = 573581) B573581
theorem B2807237 : Blo 223812 2807237 := bstep (se 4 (by rfl) ⟨263178, by rfl⟩ : syracuseStep 2807237 = 526357) B526357
theorem B382529 : Blo 223812 382529 := bstep (se 2 (by rfl) ⟨143448, by rfl⟩ : syracuseStep 382529 = 286897) B286897
theorem B382657 : Blo 223812 382657 := bstep (se 2 (by rfl) ⟨143496, by rfl⟩ : syracuseStep 382657 = 286993) B286993
theorem B382691 : Blo 223812 382691 := bstep (se 1 (by rfl) ⟨287018, by rfl⟩ : syracuseStep 382691 = 574037) B574037
theorem B644881 : Blo 223812 644881 := bstep (se 2 (by rfl) ⟨241830, by rfl⟩ : syracuseStep 644881 = 483661) B483661
theorem B284467 : Blo 223812 284467 := bstep (se 1 (by rfl) ⟨213350, by rfl⟩ : syracuseStep 284467 = 426701) B426701
theorem B382819 : Blo 223812 382819 := bstep (se 1 (by rfl) ⟨287114, by rfl⟩ : syracuseStep 382819 = 574229) B574229
theorem B284563 : Blo 223812 284563 := bstep (se 1 (by rfl) ⟨213422, by rfl⟩ : syracuseStep 284563 = 426845) B426845
theorem B382961 : Blo 223812 382961 := bstep (se 2 (by rfl) ⟨143610, by rfl⟩ : syracuseStep 382961 = 287221) B287221
theorem B251923 : Blo 223812 251923 := bstep (se 1 (by rfl) ⟨188942, by rfl⟩ : syracuseStep 251923 = 377885) B377885
theorem B645155 : Blo 223812 645155 := bstep (se 1 (by rfl) ⟨483866, by rfl⟩ : syracuseStep 645155 = 967733) B967733
theorem B1136753 : Blo 223812 1136753 := bstep (se 2 (by rfl) ⟨426282, by rfl⟩ : syracuseStep 1136753 = 852565) B852565
theorem B383089 : Blo 223812 383089 := bstep (se 2 (by rfl) ⟨143658, by rfl⟩ : syracuseStep 383089 = 287317) B287317
theorem B383123 : Blo 223812 383123 := bstep (se 1 (by rfl) ⟨287342, by rfl⟩ : syracuseStep 383123 = 574685) B574685
theorem B252067 : Blo 223812 252067 := bstep (se 1 (by rfl) ⟨189050, by rfl⟩ : syracuseStep 252067 = 378101) B378101
theorem B645347 : Blo 223812 645347 := bstep (se 1 (by rfl) ⟨484010, by rfl⟩ : syracuseStep 645347 = 968021) B968021
theorem B383251 : Blo 223812 383251 := bstep (se 1 (by rfl) ⟨287438, by rfl⟩ : syracuseStep 383251 = 574877) B574877
theorem B481585 : Blo 223812 481585 := bstep (se 2 (by rfl) ⟨180594, by rfl⟩ : syracuseStep 481585 = 361189) B361189
theorem B252211 : Blo 223812 252211 := bstep (se 1 (by rfl) ⟨189158, by rfl⟩ : syracuseStep 252211 = 378317) B378317
theorem B612685 : Blo 223812 612685 := bstep (se 3 (by rfl) ⟨114878, by rfl⟩ : syracuseStep 612685 = 229757) B229757
theorem B285059 : Blo 223812 285059 := bstep (se 1 (by rfl) ⟨213794, by rfl⟩ : syracuseStep 285059 = 427589) B427589
theorem B383393 : Blo 223812 383393 := bstep (se 2 (by rfl) ⟨143772, by rfl⟩ : syracuseStep 383393 = 287545) B287545
theorem B252355 : Blo 223812 252355 := bstep (se 1 (by rfl) ⟨189266, by rfl⟩ : syracuseStep 252355 = 378533) B378533
theorem B383521 : Blo 223812 383521 := bstep (se 2 (by rfl) ⟨143820, by rfl⟩ : syracuseStep 383521 = 287641) B287641
theorem B383555 : Blo 223812 383555 := bstep (se 1 (by rfl) ⟨287666, by rfl⟩ : syracuseStep 383555 = 575333) B575333
theorem B252499 : Blo 223812 252499 := bstep (se 1 (by rfl) ⟨189374, by rfl⟩ : syracuseStep 252499 = 378749) B378749
theorem B2153101 : Blo 223812 2153101 := bstep (se 3 (by rfl) ⟨403706, by rfl⟩ : syracuseStep 2153101 = 807413) B807413
theorem B383651 : Blo 223812 383651 := bstep (se 1 (by rfl) ⟨287738, by rfl⟩ : syracuseStep 383651 = 575477) B575477
theorem B580259 : Blo 223812 580259 := bstep (se 1 (by rfl) ⟨435194, by rfl⟩ : syracuseStep 580259 = 870389) B870389
theorem B383683 : Blo 223812 383683 := bstep (se 1 (by rfl) ⟨287762, by rfl⟩ : syracuseStep 383683 = 575525) B575525
theorem B1301197 : Blo 223812 1301197 := bstep (se 3 (by rfl) ⟨243974, by rfl⟩ : syracuseStep 1301197 = 487949) B487949
theorem B252643 : Blo 223812 252643 := bstep (se 1 (by rfl) ⟨189482, by rfl⟩ : syracuseStep 252643 = 378965) B378965
theorem B383825 : Blo 223812 383825 := bstep (se 2 (by rfl) ⟨143934, by rfl⟩ : syracuseStep 383825 = 287869) B287869
theorem B1661795 : Blo 223812 1661795 := bstep (se 1 (by rfl) ⟨1246346, by rfl⟩ : syracuseStep 1661795 = 2492693) B2492693
theorem B252787 : Blo 223812 252787 := bstep (se 1 (by rfl) ⟨189590, by rfl⟩ : syracuseStep 252787 = 379181) B379181
theorem B383953 : Blo 223812 383953 := bstep (se 2 (by rfl) ⟨143982, by rfl⟩ : syracuseStep 383953 = 287965) B287965
theorem B383987 : Blo 223812 383987 := bstep (se 1 (by rfl) ⟨287990, by rfl⟩ : syracuseStep 383987 = 575981) B575981
theorem B252931 : Blo 223812 252931 := bstep (se 1 (by rfl) ⟨189698, by rfl⟩ : syracuseStep 252931 = 379397) B379397
theorem B646157 : Blo 223812 646157 := bstep (se 3 (by rfl) ⟨121154, by rfl⟩ : syracuseStep 646157 = 242309) B242309
theorem B285763 : Blo 223812 285763 := bstep (se 1 (by rfl) ⟨214322, by rfl⟩ : syracuseStep 285763 = 428645) B428645
theorem B384115 : Blo 223812 384115 := bstep (se 1 (by rfl) ⟨288086, by rfl⟩ : syracuseStep 384115 = 576173) B576173
theorem B253075 : Blo 223812 253075 := bstep (se 1 (by rfl) ⟨189806, by rfl⟩ : syracuseStep 253075 = 379613) B379613
theorem B285859 : Blo 223812 285859 := bstep (se 1 (by rfl) ⟨214394, by rfl⟩ : syracuseStep 285859 = 428789) B428789
theorem B646339 : Blo 223812 646339 := bstep (se 1 (by rfl) ⟨484754, by rfl⟩ : syracuseStep 646339 = 969509) B969509
theorem B1727729 : Blo 223812 1727729 := bstep (se 2 (by rfl) ⟨647898, by rfl⟩ : syracuseStep 1727729 = 1295797) B1295797
theorem B384257 : Blo 223812 384257 := bstep (se 2 (by rfl) ⟨144096, by rfl⟩ : syracuseStep 384257 = 288193) B288193
theorem B810253 : Blo 223812 810253 := bstep (se 3 (by rfl) ⟨151922, by rfl⟩ : syracuseStep 810253 = 303845) B303845
theorem B253219 : Blo 223812 253219 := bstep (se 1 (by rfl) ⟨189914, by rfl⟩ : syracuseStep 253219 = 379829) B379829
theorem B384385 : Blo 223812 384385 := bstep (se 2 (by rfl) ⟨144144, by rfl⟩ : syracuseStep 384385 = 288289) B288289
theorem B384419 : Blo 223812 384419 := bstep (se 1 (by rfl) ⟨288314, by rfl⟩ : syracuseStep 384419 = 576629) B576629
theorem B253363 : Blo 223812 253363 := bstep (se 1 (by rfl) ⟨190022, by rfl⟩ : syracuseStep 253363 = 380045) B380045
theorem B1138211 : Blo 223812 1138211 := bstep (se 1 (by rfl) ⟨853658, by rfl⟩ : syracuseStep 1138211 = 1707317) B1707317
theorem B253507 : Blo 223812 253507 := bstep (se 1 (by rfl) ⟨190130, by rfl⟩ : syracuseStep 253507 = 380261) B380261
theorem B286355 : Blo 223812 286355 := bstep (se 1 (by rfl) ⟨214766, by rfl⟩ : syracuseStep 286355 = 429533) B429533
theorem B646829 : Blo 223812 646829 := bstep (se 3 (by rfl) ⟨121280, by rfl⟩ : syracuseStep 646829 = 242561) B242561
theorem B253651 : Blo 223812 253651 := bstep (se 1 (by rfl) ⟨190238, by rfl⟩ : syracuseStep 253651 = 380477) B380477
theorem B319297 : Blo 223812 319297 := bstep (se 2 (by rfl) ⟨119736, by rfl⟩ : syracuseStep 319297 = 239473) B239473
theorem B253795 : Blo 223812 253795 := bstep (se 1 (by rfl) ⟨190346, by rfl⟩ : syracuseStep 253795 = 380693) B380693
theorem B614243 : Blo 223812 614243 := bstep (se 1 (by rfl) ⟨460682, by rfl⟩ : syracuseStep 614243 = 921365) B921365
theorem B2187121 : Blo 223812 2187121 := bstep (se 2 (by rfl) ⟨820170, by rfl⟩ : syracuseStep 2187121 = 1640341) B1640341
theorem B319393 : Blo 223812 319393 := bstep (se 2 (by rfl) ⟨119772, by rfl⟩ : syracuseStep 319393 = 239545) B239545
theorem B253939 : Blo 223812 253939 := bstep (se 1 (by rfl) ⟨190454, by rfl⟩ : syracuseStep 253939 = 380909) B380909
theorem B1630307 : Blo 223812 1630307 := bstep (se 1 (by rfl) ⟨1222730, by rfl⟩ : syracuseStep 1630307 = 2445461) B2445461
theorem B254083 : Blo 223812 254083 := bstep (se 1 (by rfl) ⟨190562, by rfl⟩ : syracuseStep 254083 = 381125) B381125
theorem B254227 : Blo 223812 254227 := bstep (se 1 (by rfl) ⟨190670, by rfl⟩ : syracuseStep 254227 = 381341) B381341
theorem B1532195 : Blo 223812 1532195 := bstep (se 1 (by rfl) ⟨1149146, by rfl⟩ : syracuseStep 1532195 = 2298293) B2298293
theorem B1139021 : Blo 223812 1139021 := bstep (se 3 (by rfl) ⟨213566, by rfl⟩ : syracuseStep 1139021 = 427133) B427133
theorem B287059 : Blo 223812 287059 := bstep (se 1 (by rfl) ⟨215294, by rfl⟩ : syracuseStep 287059 = 430589) B430589
theorem B319889 : Blo 223812 319889 := bstep (se 2 (by rfl) ⟨119958, by rfl⟩ : syracuseStep 319889 = 239917) B239917
theorem B254371 : Blo 223812 254371 := bstep (se 1 (by rfl) ⟨190778, by rfl⟩ : syracuseStep 254371 = 381557) B381557
theorem B287155 : Blo 223812 287155 := bstep (se 1 (by rfl) ⟨215366, by rfl⟩ : syracuseStep 287155 = 430733) B430733
theorem B254515 : Blo 223812 254515 := bstep (se 1 (by rfl) ⟨190886, by rfl⟩ : syracuseStep 254515 = 381773) B381773
theorem B615043 : Blo 223812 615043 := bstep (se 1 (by rfl) ⟨461282, by rfl⟩ : syracuseStep 615043 = 922565) B922565
theorem B254659 : Blo 223812 254659 := bstep (se 1 (by rfl) ⟨190994, by rfl⟩ : syracuseStep 254659 = 381989) B381989
theorem B648013 : Blo 223812 648013 := bstep (se 3 (by rfl) ⟨121502, by rfl⟩ : syracuseStep 648013 = 243005) B243005
theorem B254803 : Blo 223812 254803 := bstep (se 1 (by rfl) ⟨191102, by rfl⟩ : syracuseStep 254803 = 382205) B382205
theorem B287651 : Blo 223812 287651 := bstep (se 1 (by rfl) ⟨215738, by rfl⟩ : syracuseStep 287651 = 431477) B431477
theorem B254947 : Blo 223812 254947 := bstep (se 1 (by rfl) ⟨191210, by rfl⟩ : syracuseStep 254947 = 382421) B382421
theorem B255091 : Blo 223812 255091 := bstep (se 1 (by rfl) ⟨191318, by rfl⟩ : syracuseStep 255091 = 382637) B382637
theorem B320755 : Blo 223812 320755 := bstep (se 1 (by rfl) ⟨240566, by rfl⟩ : syracuseStep 320755 = 481133) B481133
theorem B255235 : Blo 223812 255235 := bstep (se 1 (by rfl) ⟨191426, by rfl⟩ : syracuseStep 255235 = 382853) B382853
theorem B484643 : Blo 223812 484643 := bstep (se 1 (by rfl) ⟨363482, by rfl⟩ : syracuseStep 484643 = 726965) B726965
theorem B320851 : Blo 223812 320851 := bstep (se 1 (by rfl) ⟨240638, by rfl⟩ : syracuseStep 320851 = 481277) B481277
theorem B255379 : Blo 223812 255379 := bstep (se 1 (by rfl) ⟨191534, by rfl⟩ : syracuseStep 255379 = 383069) B383069
theorem B1369541 : Blo 223812 1369541 := bstep (se 4 (by rfl) ⟨128394, by rfl⟩ : syracuseStep 1369541 = 256789) B256789
theorem B255523 : Blo 223812 255523 := bstep (se 1 (by rfl) ⟨191642, by rfl⟩ : syracuseStep 255523 = 383285) B383285
theorem B255667 : Blo 223812 255667 := bstep (se 1 (by rfl) ⟨191750, by rfl⟩ : syracuseStep 255667 = 383501) B383501
theorem B321347 : Blo 223812 321347 := bstep (se 1 (by rfl) ⟨241010, by rfl⟩ : syracuseStep 321347 = 482021) B482021
theorem B255811 : Blo 223812 255811 := bstep (se 1 (by rfl) ⟨191858, by rfl⟩ : syracuseStep 255811 = 383717) B383717
theorem B255955 : Blo 223812 255955 := bstep (se 1 (by rfl) ⟨191966, by rfl⟩ : syracuseStep 255955 = 383933) B383933
theorem B387155 : Blo 223812 387155 := bstep (se 1 (by rfl) ⟨290366, by rfl⟩ : syracuseStep 387155 = 580733) B580733
theorem B256099 : Blo 223812 256099 := bstep (se 1 (by rfl) ⟨192074, by rfl⟩ : syracuseStep 256099 = 384149) B384149
theorem B485507 : Blo 223812 485507 := bstep (se 1 (by rfl) ⟨364130, by rfl⟩ : syracuseStep 485507 = 728261) B728261
theorem B485617 : Blo 223812 485617 := bstep (se 2 (by rfl) ⟨182106, by rfl⟩ : syracuseStep 485617 = 364213) B364213
theorem B256243 : Blo 223812 256243 := bstep (se 1 (by rfl) ⟨192182, by rfl⟩ : syracuseStep 256243 = 384365) B384365
theorem B1042723 : Blo 223812 1042723 := bstep (se 1 (by rfl) ⟨782042, by rfl⟩ : syracuseStep 1042723 = 1564085) B1564085
theorem B518467 : Blo 223812 518467 := bstep (se 1 (by rfl) ⟨388850, by rfl⟩ : syracuseStep 518467 = 777701) B777701
theorem B584081 : Blo 223812 584081 := bstep (se 2 (by rfl) ⟨219030, by rfl⟩ : syracuseStep 584081 = 438061) B438061
theorem B321985 : Blo 223812 321985 := bstep (se 2 (by rfl) ⟨120744, by rfl⟩ : syracuseStep 321985 = 241489) B241489
theorem B813539 : Blo 223812 813539 := bstep (se 1 (by rfl) ⟨610154, by rfl⟩ : syracuseStep 813539 = 1220309) B1220309
theorem B518737 : Blo 223812 518737 := bstep (se 2 (by rfl) ⟨194526, by rfl⟩ : syracuseStep 518737 = 389053) B389053
theorem B223827 : Blo 223812 223827 := bstep (se 1 (by rfl) ⟨167870, by rfl⟩ : syracuseStep 223827 = 335741) B335741
theorem B223843 : Blo 223812 223843 := bstep (se 1 (by rfl) ⟨167882, by rfl⟩ : syracuseStep 223843 = 335765) B335765
theorem B3500657 : Blo 223812 3500657 := bstep (se 2 (by rfl) ⟨1312746, by rfl⟩ : syracuseStep 3500657 = 2625493) B2625493
theorem B223859 : Blo 223812 223859 := bstep (se 1 (by rfl) ⟨167894, by rfl⟩ : syracuseStep 223859 = 335789) B335789
theorem B223875 : Blo 223812 223875 := bstep (se 1 (by rfl) ⟨167906, by rfl⟩ : syracuseStep 223875 = 335813) B335813
theorem B223891 : Blo 223812 223891 := bstep (se 1 (by rfl) ⟨167918, by rfl⟩ : syracuseStep 223891 = 335837) B335837
theorem B223907 : Blo 223812 223907 := bstep (se 1 (by rfl) ⟨167930, by rfl⟩ : syracuseStep 223907 = 335861) B335861
theorem B223923 : Blo 223812 223923 := bstep (se 1 (by rfl) ⟨167942, by rfl⟩ : syracuseStep 223923 = 335885) B335885
theorem B223939 : Blo 223812 223939 := bstep (se 1 (by rfl) ⟨167954, by rfl⟩ : syracuseStep 223939 = 335909) B335909
theorem B223955 : Blo 223812 223955 := bstep (se 1 (by rfl) ⟨167966, by rfl⟩ : syracuseStep 223955 = 335933) B335933
theorem B223971 : Blo 223812 223971 := bstep (se 1 (by rfl) ⟨167978, by rfl⟩ : syracuseStep 223971 = 335957) B335957
theorem B223987 : Blo 223812 223987 := bstep (se 1 (by rfl) ⟨167990, by rfl⟩ : syracuseStep 223987 = 335981) B335981
theorem B224003 : Blo 223812 224003 := bstep (se 1 (by rfl) ⟨168002, by rfl⟩ : syracuseStep 224003 = 336005) B336005
theorem B322321 : Blo 223812 322321 := bstep (se 2 (by rfl) ⟨120870, by rfl⟩ : syracuseStep 322321 = 241741) B241741
theorem B224019 : Blo 223812 224019 := bstep (se 1 (by rfl) ⟨168014, by rfl⟩ : syracuseStep 224019 = 336029) B336029
theorem B224035 : Blo 223812 224035 := bstep (se 1 (by rfl) ⟨168026, by rfl⟩ : syracuseStep 224035 = 336053) B336053
theorem B551729 : Blo 223812 551729 := bstep (se 2 (by rfl) ⟨206898, by rfl⟩ : syracuseStep 551729 = 413797) B413797
theorem B224051 : Blo 223812 224051 := bstep (se 1 (by rfl) ⟨168038, by rfl⟩ : syracuseStep 224051 = 336077) B336077
theorem B224067 : Blo 223812 224067 := bstep (se 1 (by rfl) ⟨168050, by rfl⟩ : syracuseStep 224067 = 336101) B336101
theorem B224083 : Blo 223812 224083 := bstep (se 1 (by rfl) ⟨168062, by rfl⟩ : syracuseStep 224083 = 336125) B336125
theorem B224099 : Blo 223812 224099 := bstep (se 1 (by rfl) ⟨168074, by rfl⟩ : syracuseStep 224099 = 336149) B336149
theorem B224115 : Blo 223812 224115 := bstep (se 1 (by rfl) ⟨168086, by rfl⟩ : syracuseStep 224115 = 336173) B336173
theorem B224131 : Blo 223812 224131 := bstep (se 1 (by rfl) ⟨168098, by rfl⟩ : syracuseStep 224131 = 336197) B336197
theorem B224147 : Blo 223812 224147 := bstep (se 1 (by rfl) ⟨168110, by rfl⟩ : syracuseStep 224147 = 336221) B336221
theorem B224163 : Blo 223812 224163 := bstep (se 1 (by rfl) ⟨168122, by rfl⟩ : syracuseStep 224163 = 336245) B336245
theorem B224179 : Blo 223812 224179 := bstep (se 1 (by rfl) ⟨168134, by rfl⟩ : syracuseStep 224179 = 336269) B336269
theorem B224195 : Blo 223812 224195 := bstep (se 1 (by rfl) ⟨168146, by rfl⟩ : syracuseStep 224195 = 336293) B336293
theorem B224211 : Blo 223812 224211 := bstep (se 1 (by rfl) ⟨168158, by rfl⟩ : syracuseStep 224211 = 336317) B336317
theorem B224227 : Blo 223812 224227 := bstep (se 1 (by rfl) ⟨168170, by rfl⟩ : syracuseStep 224227 = 336341) B336341
theorem B224243 : Blo 223812 224243 := bstep (se 1 (by rfl) ⟨168182, by rfl⟩ : syracuseStep 224243 = 336365) B336365
theorem B224259 : Blo 223812 224259 := bstep (se 1 (by rfl) ⟨168194, by rfl⟩ : syracuseStep 224259 = 336389) B336389
theorem B224275 : Blo 223812 224275 := bstep (se 1 (by rfl) ⟨168206, by rfl⟩ : syracuseStep 224275 = 336413) B336413
theorem B224291 : Blo 223812 224291 := bstep (se 1 (by rfl) ⟨168218, by rfl⟩ : syracuseStep 224291 = 336437) B336437
theorem B224307 : Blo 223812 224307 := bstep (se 1 (by rfl) ⟨168230, by rfl⟩ : syracuseStep 224307 = 336461) B336461
theorem B224323 : Blo 223812 224323 := bstep (se 1 (by rfl) ⟨168242, by rfl⟩ : syracuseStep 224323 = 336485) B336485
theorem B224339 : Blo 223812 224339 := bstep (se 1 (by rfl) ⟨168254, by rfl⟩ : syracuseStep 224339 = 336509) B336509
theorem B224355 : Blo 223812 224355 := bstep (se 1 (by rfl) ⟨168266, by rfl⟩ : syracuseStep 224355 = 336533) B336533
theorem B224371 : Blo 223812 224371 := bstep (se 1 (by rfl) ⟨168278, by rfl⟩ : syracuseStep 224371 = 336557) B336557
theorem B224387 : Blo 223812 224387 := bstep (se 1 (by rfl) ⟨168290, by rfl⟩ : syracuseStep 224387 = 336581) B336581
theorem B224403 : Blo 223812 224403 := bstep (se 1 (by rfl) ⟨168302, by rfl⟩ : syracuseStep 224403 = 336605) B336605
theorem B224419 : Blo 223812 224419 := bstep (se 1 (by rfl) ⟨168314, by rfl⟩ : syracuseStep 224419 = 336629) B336629
theorem B1141937 : Blo 223812 1141937 := bstep (se 2 (by rfl) ⟨428226, by rfl⟩ : syracuseStep 1141937 = 856453) B856453
theorem B224435 : Blo 223812 224435 := bstep (se 1 (by rfl) ⟨168326, by rfl⟩ : syracuseStep 224435 = 336653) B336653
theorem B224451 : Blo 223812 224451 := bstep (se 1 (by rfl) ⟨168338, by rfl⟩ : syracuseStep 224451 = 336677) B336677
theorem B224467 : Blo 223812 224467 := bstep (se 1 (by rfl) ⟨168350, by rfl⟩ : syracuseStep 224467 = 336701) B336701
theorem B224483 : Blo 223812 224483 := bstep (se 1 (by rfl) ⟨168362, by rfl⟩ : syracuseStep 224483 = 336725) B336725
theorem B519409 : Blo 223812 519409 := bstep (se 2 (by rfl) ⟨194778, by rfl⟩ : syracuseStep 519409 = 389557) B389557
theorem B224499 : Blo 223812 224499 := bstep (se 1 (by rfl) ⟨168374, by rfl⟩ : syracuseStep 224499 = 336749) B336749
theorem B224515 : Blo 223812 224515 := bstep (se 1 (by rfl) ⟨168386, by rfl⟩ : syracuseStep 224515 = 336773) B336773
theorem B224531 : Blo 223812 224531 := bstep (se 1 (by rfl) ⟨168398, by rfl⟩ : syracuseStep 224531 = 336797) B336797
theorem B224547 : Blo 223812 224547 := bstep (se 1 (by rfl) ⟨168410, by rfl⟩ : syracuseStep 224547 = 336821) B336821
theorem B224563 : Blo 223812 224563 := bstep (se 1 (by rfl) ⟨168422, by rfl⟩ : syracuseStep 224563 = 336845) B336845
theorem B224579 : Blo 223812 224579 := bstep (se 1 (by rfl) ⟨168434, by rfl⟩ : syracuseStep 224579 = 336869) B336869
theorem B1469765 : Blo 223812 1469765 := bstep (se 4 (by rfl) ⟨137790, by rfl⟩ : syracuseStep 1469765 = 275581) B275581
theorem B224595 : Blo 223812 224595 := bstep (se 1 (by rfl) ⟨168446, by rfl⟩ : syracuseStep 224595 = 336893) B336893
theorem B322913 : Blo 223812 322913 := bstep (se 2 (by rfl) ⟨121092, by rfl⟩ : syracuseStep 322913 = 242185) B242185
theorem B224611 : Blo 223812 224611 := bstep (se 1 (by rfl) ⟨168458, by rfl⟩ : syracuseStep 224611 = 336917) B336917
theorem B1371491 : Blo 223812 1371491 := bstep (se 1 (by rfl) ⟨1028618, by rfl⟩ : syracuseStep 1371491 = 2057237) B2057237
theorem B1437041 : Blo 223812 1437041 := bstep (se 2 (by rfl) ⟨538890, by rfl⟩ : syracuseStep 1437041 = 1077781) B1077781
theorem B224627 : Blo 223812 224627 := bstep (se 1 (by rfl) ⟨168470, by rfl⟩ : syracuseStep 224627 = 336941) B336941
theorem B224643 : Blo 223812 224643 := bstep (se 1 (by rfl) ⟨168482, by rfl⟩ : syracuseStep 224643 = 336965) B336965
theorem B224659 : Blo 223812 224659 := bstep (se 1 (by rfl) ⟨168494, by rfl⟩ : syracuseStep 224659 = 336989) B336989
theorem B224675 : Blo 223812 224675 := bstep (se 1 (by rfl) ⟨168506, by rfl⟩ : syracuseStep 224675 = 337013) B337013
theorem B224691 : Blo 223812 224691 := bstep (se 1 (by rfl) ⟨168518, by rfl⟩ : syracuseStep 224691 = 337037) B337037
theorem B224707 : Blo 223812 224707 := bstep (se 1 (by rfl) ⟨168530, by rfl⟩ : syracuseStep 224707 = 337061) B337061
theorem B224723 : Blo 223812 224723 := bstep (se 1 (by rfl) ⟨168542, by rfl⟩ : syracuseStep 224723 = 337085) B337085
theorem B224739 : Blo 223812 224739 := bstep (se 1 (by rfl) ⟨168554, by rfl⟩ : syracuseStep 224739 = 337109) B337109
theorem B224755 : Blo 223812 224755 := bstep (se 1 (by rfl) ⟨168566, by rfl⟩ : syracuseStep 224755 = 337133) B337133
theorem B224771 : Blo 223812 224771 := bstep (se 1 (by rfl) ⟨168578, by rfl⟩ : syracuseStep 224771 = 337157) B337157
theorem B224787 : Blo 223812 224787 := bstep (se 1 (by rfl) ⟨168590, by rfl⟩ : syracuseStep 224787 = 337181) B337181
theorem B224803 : Blo 223812 224803 := bstep (se 1 (by rfl) ⟨168602, by rfl⟩ : syracuseStep 224803 = 337205) B337205
theorem B1535537 : Blo 223812 1535537 := bstep (se 2 (by rfl) ⟨575826, by rfl⟩ : syracuseStep 1535537 = 1151653) B1151653
theorem B224819 : Blo 223812 224819 := bstep (se 1 (by rfl) ⟨168614, by rfl⟩ : syracuseStep 224819 = 337229) B337229
theorem B224835 : Blo 223812 224835 := bstep (se 1 (by rfl) ⟨168626, by rfl⟩ : syracuseStep 224835 = 337253) B337253
theorem B224851 : Blo 223812 224851 := bstep (se 1 (by rfl) ⟨168638, by rfl⟩ : syracuseStep 224851 = 337277) B337277
theorem B454243 : Blo 223812 454243 := bstep (se 1 (by rfl) ⟨340682, by rfl⟩ : syracuseStep 454243 = 681365) B681365
theorem B224867 : Blo 223812 224867 := bstep (se 1 (by rfl) ⟨168650, by rfl⟩ : syracuseStep 224867 = 337301) B337301
theorem B224883 : Blo 223812 224883 := bstep (se 1 (by rfl) ⟨168662, by rfl⟩ : syracuseStep 224883 = 337325) B337325
theorem B224899 : Blo 223812 224899 := bstep (se 1 (by rfl) ⟨168674, by rfl⟩ : syracuseStep 224899 = 337349) B337349
theorem B224915 : Blo 223812 224915 := bstep (se 1 (by rfl) ⟨168686, by rfl⟩ : syracuseStep 224915 = 337373) B337373
theorem B224931 : Blo 223812 224931 := bstep (se 1 (by rfl) ⟨168698, by rfl⟩ : syracuseStep 224931 = 337397) B337397
theorem B224947 : Blo 223812 224947 := bstep (se 1 (by rfl) ⟨168710, by rfl⟩ : syracuseStep 224947 = 337421) B337421
theorem B224963 : Blo 223812 224963 := bstep (se 1 (by rfl) ⟨168722, by rfl⟩ : syracuseStep 224963 = 337445) B337445
theorem B224979 : Blo 223812 224979 := bstep (se 1 (by rfl) ⟨168734, by rfl⟩ : syracuseStep 224979 = 337469) B337469
theorem B257747 : Blo 223812 257747 := bstep (se 1 (by rfl) ⟨193310, by rfl⟩ : syracuseStep 257747 = 386621) B386621
theorem B224995 : Blo 223812 224995 := bstep (se 1 (by rfl) ⟨168746, by rfl⟩ : syracuseStep 224995 = 337493) B337493
theorem B225011 : Blo 223812 225011 := bstep (se 1 (by rfl) ⟨168758, by rfl⟩ : syracuseStep 225011 = 337517) B337517
theorem B225027 : Blo 223812 225027 := bstep (se 1 (by rfl) ⟨168770, by rfl⟩ : syracuseStep 225027 = 337541) B337541
theorem B225043 : Blo 223812 225043 := bstep (se 1 (by rfl) ⟨168782, by rfl⟩ : syracuseStep 225043 = 337565) B337565
theorem B225059 : Blo 223812 225059 := bstep (se 1 (by rfl) ⟨168794, by rfl⟩ : syracuseStep 225059 = 337589) B337589
theorem B225075 : Blo 223812 225075 := bstep (se 1 (by rfl) ⟨168806, by rfl⟩ : syracuseStep 225075 = 337613) B337613
theorem B225091 : Blo 223812 225091 := bstep (se 1 (by rfl) ⟨168818, by rfl⟩ : syracuseStep 225091 = 337637) B337637
theorem B2420549 : Blo 223812 2420549 := bstep (se 4 (by rfl) ⟨226926, by rfl⟩ : syracuseStep 2420549 = 453853) B453853
theorem B1830725 : Blo 223812 1830725 := bstep (se 4 (by rfl) ⟨171630, by rfl⟩ : syracuseStep 1830725 = 343261) B343261
theorem B225107 : Blo 223812 225107 := bstep (se 1 (by rfl) ⟨168830, by rfl⟩ : syracuseStep 225107 = 337661) B337661
theorem B225123 : Blo 223812 225123 := bstep (se 1 (by rfl) ⟨168842, by rfl⟩ : syracuseStep 225123 = 337685) B337685
theorem B225139 : Blo 223812 225139 := bstep (se 1 (by rfl) ⟨168854, by rfl⟩ : syracuseStep 225139 = 337709) B337709
theorem B323443 : Blo 223812 323443 := bstep (se 1 (by rfl) ⟨242582, by rfl⟩ : syracuseStep 323443 = 485165) B485165
theorem B225155 : Blo 223812 225155 := bstep (se 1 (by rfl) ⟨168866, by rfl⟩ : syracuseStep 225155 = 337733) B337733
theorem B225171 : Blo 223812 225171 := bstep (se 1 (by rfl) ⟨168878, by rfl⟩ : syracuseStep 225171 = 337757) B337757
theorem B225187 : Blo 223812 225187 := bstep (se 1 (by rfl) ⟨168890, by rfl⟩ : syracuseStep 225187 = 337781) B337781
theorem B225203 : Blo 223812 225203 := bstep (se 1 (by rfl) ⟨168902, by rfl⟩ : syracuseStep 225203 = 337805) B337805
theorem B225219 : Blo 223812 225219 := bstep (se 1 (by rfl) ⟨168914, by rfl⟩ : syracuseStep 225219 = 337829) B337829
theorem B1830853 : Blo 223812 1830853 := bstep (se 4 (by rfl) ⟨171642, by rfl⟩ : syracuseStep 1830853 = 343285) B343285
theorem B683981 : Blo 223812 683981 := bstep (se 3 (by rfl) ⟨128246, by rfl⟩ : syracuseStep 683981 = 256493) B256493
theorem B225235 : Blo 223812 225235 := bstep (se 1 (by rfl) ⟨168926, by rfl⟩ : syracuseStep 225235 = 337853) B337853
theorem B2879459 : Blo 223812 2879459 := bstep (se 1 (by rfl) ⟨2159594, by rfl⟩ : syracuseStep 2879459 = 4319189) B4319189
theorem B225251 : Blo 223812 225251 := bstep (se 1 (by rfl) ⟨168938, by rfl⟩ : syracuseStep 225251 = 337877) B337877
theorem B225267 : Blo 223812 225267 := bstep (se 1 (by rfl) ⟨168950, by rfl⟩ : syracuseStep 225267 = 337901) B337901
theorem B225283 : Blo 223812 225283 := bstep (se 1 (by rfl) ⟨168962, by rfl⟩ : syracuseStep 225283 = 337925) B337925
theorem B552977 : Blo 223812 552977 := bstep (se 2 (by rfl) ⟨207366, by rfl⟩ : syracuseStep 552977 = 414733) B414733
theorem B225299 : Blo 223812 225299 := bstep (se 1 (by rfl) ⟨168974, by rfl⟩ : syracuseStep 225299 = 337949) B337949
theorem B225315 : Blo 223812 225315 := bstep (se 1 (by rfl) ⟨168986, by rfl⟩ : syracuseStep 225315 = 337973) B337973
theorem B225331 : Blo 223812 225331 := bstep (se 1 (by rfl) ⟨168998, by rfl⟩ : syracuseStep 225331 = 337997) B337997
theorem B225347 : Blo 223812 225347 := bstep (se 1 (by rfl) ⟨169010, by rfl⟩ : syracuseStep 225347 = 338021) B338021
theorem B225363 : Blo 223812 225363 := bstep (se 1 (by rfl) ⟨169022, by rfl⟩ : syracuseStep 225363 = 338045) B338045
theorem B225379 : Blo 223812 225379 := bstep (se 1 (by rfl) ⟨169034, by rfl⟩ : syracuseStep 225379 = 338069) B338069
theorem B225395 : Blo 223812 225395 := bstep (se 1 (by rfl) ⟨169046, by rfl⟩ : syracuseStep 225395 = 338093) B338093
theorem B225411 : Blo 223812 225411 := bstep (se 1 (by rfl) ⟨169058, by rfl⟩ : syracuseStep 225411 = 338117) B338117
theorem B225427 : Blo 223812 225427 := bstep (se 1 (by rfl) ⟨169070, by rfl⟩ : syracuseStep 225427 = 338141) B338141
theorem B225443 : Blo 223812 225443 := bstep (se 1 (by rfl) ⟨169082, by rfl⟩ : syracuseStep 225443 = 338165) B338165
theorem B225459 : Blo 223812 225459 := bstep (se 1 (by rfl) ⟨169094, by rfl⟩ : syracuseStep 225459 = 338189) B338189
theorem B225475 : Blo 223812 225475 := bstep (se 1 (by rfl) ⟨169106, by rfl⟩ : syracuseStep 225475 = 338213) B338213
theorem B323779 : Blo 223812 323779 := bstep (se 1 (by rfl) ⟨242834, by rfl⟩ : syracuseStep 323779 = 485669) B485669
theorem B225491 : Blo 223812 225491 := bstep (se 1 (by rfl) ⟨169118, by rfl⟩ : syracuseStep 225491 = 338237) B338237
theorem B225507 : Blo 223812 225507 := bstep (se 1 (by rfl) ⟨169130, by rfl⟩ : syracuseStep 225507 = 338261) B338261
theorem B225523 : Blo 223812 225523 := bstep (se 1 (by rfl) ⟨169142, by rfl⟩ : syracuseStep 225523 = 338285) B338285
theorem B225539 : Blo 223812 225539 := bstep (se 1 (by rfl) ⟨169154, by rfl⟩ : syracuseStep 225539 = 338309) B338309
theorem B225555 : Blo 223812 225555 := bstep (se 1 (by rfl) ⟨169166, by rfl⟩ : syracuseStep 225555 = 338333) B338333
theorem B225571 : Blo 223812 225571 := bstep (se 1 (by rfl) ⟨169178, by rfl⟩ : syracuseStep 225571 = 338357) B338357
theorem B225587 : Blo 223812 225587 := bstep (se 1 (by rfl) ⟨169190, by rfl⟩ : syracuseStep 225587 = 338381) B338381
theorem B225603 : Blo 223812 225603 := bstep (se 1 (by rfl) ⟨169202, by rfl⟩ : syracuseStep 225603 = 338405) B338405
theorem B225619 : Blo 223812 225619 := bstep (se 1 (by rfl) ⟨169214, by rfl⟩ : syracuseStep 225619 = 338429) B338429
theorem B225635 : Blo 223812 225635 := bstep (se 1 (by rfl) ⟨169226, by rfl⟩ : syracuseStep 225635 = 338453) B338453
theorem B225651 : Blo 223812 225651 := bstep (se 1 (by rfl) ⟨169238, by rfl⟩ : syracuseStep 225651 = 338477) B338477
theorem B225667 : Blo 223812 225667 := bstep (se 1 (by rfl) ⟨169250, by rfl⟩ : syracuseStep 225667 = 338501) B338501
theorem B815501 : Blo 223812 815501 := bstep (se 3 (by rfl) ⟨152906, by rfl⟩ : syracuseStep 815501 = 305813) B305813
theorem B225683 : Blo 223812 225683 := bstep (se 1 (by rfl) ⟨169262, by rfl⟩ : syracuseStep 225683 = 338525) B338525
theorem B225699 : Blo 223812 225699 := bstep (se 1 (by rfl) ⟨169274, by rfl⟩ : syracuseStep 225699 = 338549) B338549
theorem B225715 : Blo 223812 225715 := bstep (se 1 (by rfl) ⟨169286, by rfl⟩ : syracuseStep 225715 = 338573) B338573
theorem B225731 : Blo 223812 225731 := bstep (se 1 (by rfl) ⟨169298, by rfl⟩ : syracuseStep 225731 = 338597) B338597
theorem B225747 : Blo 223812 225747 := bstep (se 1 (by rfl) ⟨169310, by rfl⟩ : syracuseStep 225747 = 338621) B338621
theorem B225763 : Blo 223812 225763 := bstep (se 1 (by rfl) ⟨169322, by rfl⟩ : syracuseStep 225763 = 338645) B338645
theorem B225779 : Blo 223812 225779 := bstep (se 1 (by rfl) ⟨169334, by rfl⟩ : syracuseStep 225779 = 338669) B338669
theorem B225795 : Blo 223812 225795 := bstep (se 1 (by rfl) ⟨169346, by rfl⟩ : syracuseStep 225795 = 338693) B338693
theorem B717329 : Blo 223812 717329 := bstep (se 2 (by rfl) ⟨268998, by rfl⟩ : syracuseStep 717329 = 537997) B537997
theorem B225811 : Blo 223812 225811 := bstep (se 1 (by rfl) ⟨169358, by rfl⟩ : syracuseStep 225811 = 338717) B338717
theorem B225827 : Blo 223812 225827 := bstep (se 1 (by rfl) ⟨169370, by rfl⟩ : syracuseStep 225827 = 338741) B338741
theorem B225843 : Blo 223812 225843 := bstep (se 1 (by rfl) ⟨169382, by rfl⟩ : syracuseStep 225843 = 338765) B338765
theorem B225859 : Blo 223812 225859 := bstep (se 1 (by rfl) ⟨169394, by rfl⟩ : syracuseStep 225859 = 338789) B338789
theorem B225875 : Blo 223812 225875 := bstep (se 1 (by rfl) ⟨169406, by rfl⟩ : syracuseStep 225875 = 338813) B338813
theorem B1143395 : Blo 223812 1143395 := bstep (se 1 (by rfl) ⟨857546, by rfl⟩ : syracuseStep 1143395 = 1715093) B1715093
theorem B225891 : Blo 223812 225891 := bstep (se 1 (by rfl) ⟨169418, by rfl⟩ : syracuseStep 225891 = 338837) B338837
theorem B225907 : Blo 223812 225907 := bstep (se 1 (by rfl) ⟨169430, by rfl⟩ : syracuseStep 225907 = 338861) B338861
theorem B225923 : Blo 223812 225923 := bstep (se 1 (by rfl) ⟨169442, by rfl⟩ : syracuseStep 225923 = 338885) B338885
theorem B717457 : Blo 223812 717457 := bstep (se 2 (by rfl) ⟨269046, by rfl⟩ : syracuseStep 717457 = 538093) B538093
theorem B225939 : Blo 223812 225939 := bstep (se 1 (by rfl) ⟨169454, by rfl⟩ : syracuseStep 225939 = 338909) B338909
theorem B225955 : Blo 223812 225955 := bstep (se 1 (by rfl) ⟨169466, by rfl⟩ : syracuseStep 225955 = 338933) B338933
theorem B225971 : Blo 223812 225971 := bstep (se 1 (by rfl) ⟨169478, by rfl⟩ : syracuseStep 225971 = 338957) B338957
theorem B225987 : Blo 223812 225987 := bstep (se 1 (by rfl) ⟨169490, by rfl⟩ : syracuseStep 225987 = 338981) B338981
theorem B226003 : Blo 223812 226003 := bstep (se 1 (by rfl) ⟨169502, by rfl⟩ : syracuseStep 226003 = 339005) B339005
theorem B226019 : Blo 223812 226019 := bstep (se 1 (by rfl) ⟨169514, by rfl⟩ : syracuseStep 226019 = 339029) B339029
theorem B324337 : Blo 223812 324337 := bstep (se 2 (by rfl) ⟨121626, by rfl⟩ : syracuseStep 324337 = 243253) B243253
theorem B226035 : Blo 223812 226035 := bstep (se 1 (by rfl) ⟨169526, by rfl⟩ : syracuseStep 226035 = 339053) B339053
theorem B226051 : Blo 223812 226051 := bstep (se 1 (by rfl) ⟨169538, by rfl⟩ : syracuseStep 226051 = 339077) B339077
theorem B1700621 : Blo 223812 1700621 := bstep (se 3 (by rfl) ⟨318866, by rfl⟩ : syracuseStep 1700621 = 637733) B637733
theorem B226067 : Blo 223812 226067 := bstep (se 1 (by rfl) ⟨169550, by rfl⟩ : syracuseStep 226067 = 339101) B339101
theorem B1438499 : Blo 223812 1438499 := bstep (se 1 (by rfl) ⟨1078874, by rfl⟩ : syracuseStep 1438499 = 2157749) B2157749
theorem B226083 : Blo 223812 226083 := bstep (se 1 (by rfl) ⟨169562, by rfl⟩ : syracuseStep 226083 = 339125) B339125
theorem B226099 : Blo 223812 226099 := bstep (se 1 (by rfl) ⟨169574, by rfl⟩ : syracuseStep 226099 = 339149) B339149
theorem B226115 : Blo 223812 226115 := bstep (se 1 (by rfl) ⟨169586, by rfl⟩ : syracuseStep 226115 = 339173) B339173
theorem B226131 : Blo 223812 226131 := bstep (se 1 (by rfl) ⟨169598, by rfl⟩ : syracuseStep 226131 = 339197) B339197
theorem B226147 : Blo 223812 226147 := bstep (se 1 (by rfl) ⟨169610, by rfl⟩ : syracuseStep 226147 = 339221) B339221
theorem B226163 : Blo 223812 226163 := bstep (se 1 (by rfl) ⟨169622, by rfl⟩ : syracuseStep 226163 = 339245) B339245
theorem B226179 : Blo 223812 226179 := bstep (se 1 (by rfl) ⟨169634, by rfl⟩ : syracuseStep 226179 = 339269) B339269
theorem B717713 : Blo 223812 717713 := bstep (se 2 (by rfl) ⟨269142, by rfl⟩ : syracuseStep 717713 = 538285) B538285
theorem B226195 : Blo 223812 226195 := bstep (se 1 (by rfl) ⟨169646, by rfl⟩ : syracuseStep 226195 = 339293) B339293
theorem B226211 : Blo 223812 226211 := bstep (se 1 (by rfl) ⟨169658, by rfl⟩ : syracuseStep 226211 = 339317) B339317
theorem B652205 : Blo 223812 652205 := bstep (se 3 (by rfl) ⟨122288, by rfl⟩ : syracuseStep 652205 = 244577) B244577
theorem B226227 : Blo 223812 226227 := bstep (se 1 (by rfl) ⟨169670, by rfl⟩ : syracuseStep 226227 = 339341) B339341
theorem B226243 : Blo 223812 226243 := bstep (se 1 (by rfl) ⟨169682, by rfl⟩ : syracuseStep 226243 = 339365) B339365
theorem B226259 : Blo 223812 226259 := bstep (se 1 (by rfl) ⟨169694, by rfl⟩ : syracuseStep 226259 = 339389) B339389
theorem B226275 : Blo 223812 226275 := bstep (se 1 (by rfl) ⟨169706, by rfl⟩ : syracuseStep 226275 = 339413) B339413
theorem B553969 : Blo 223812 553969 := bstep (se 2 (by rfl) ⟨207738, by rfl⟩ : syracuseStep 553969 = 415477) B415477
theorem B226291 : Blo 223812 226291 := bstep (se 1 (by rfl) ⟨169718, by rfl⟩ : syracuseStep 226291 = 339437) B339437
theorem B226307 : Blo 223812 226307 := bstep (se 1 (by rfl) ⟨169730, by rfl⟩ : syracuseStep 226307 = 339461) B339461
theorem B1274885 : Blo 223812 1274885 := bstep (se 4 (by rfl) ⟨119520, by rfl⟩ : syracuseStep 1274885 = 239041) B239041
theorem B226323 : Blo 223812 226323 := bstep (se 1 (by rfl) ⟨169742, by rfl⟩ : syracuseStep 226323 = 339485) B339485
theorem B226339 : Blo 223812 226339 := bstep (se 1 (by rfl) ⟨169754, by rfl⟩ : syracuseStep 226339 = 339509) B339509
theorem B226355 : Blo 223812 226355 := bstep (se 1 (by rfl) ⟨169766, by rfl⟩ : syracuseStep 226355 = 339533) B339533
theorem B226371 : Blo 223812 226371 := bstep (se 1 (by rfl) ⟨169778, by rfl⟩ : syracuseStep 226371 = 339557) B339557
theorem B226387 : Blo 223812 226387 := bstep (se 1 (by rfl) ⟨169790, by rfl⟩ : syracuseStep 226387 = 339581) B339581
theorem B226403 : Blo 223812 226403 := bstep (se 1 (by rfl) ⟨169802, by rfl⟩ : syracuseStep 226403 = 339605) B339605
theorem B226419 : Blo 223812 226419 := bstep (se 1 (by rfl) ⟨169814, by rfl⟩ : syracuseStep 226419 = 339629) B339629
theorem B226435 : Blo 223812 226435 := bstep (se 1 (by rfl) ⟨169826, by rfl⟩ : syracuseStep 226435 = 339653) B339653
theorem B226451 : Blo 223812 226451 := bstep (se 1 (by rfl) ⟨169838, by rfl⟩ : syracuseStep 226451 = 339677) B339677
theorem B226467 : Blo 223812 226467 := bstep (se 1 (by rfl) ⟨169850, by rfl⟩ : syracuseStep 226467 = 339701) B339701
theorem B226483 : Blo 223812 226483 := bstep (se 1 (by rfl) ⟨169862, by rfl⟩ : syracuseStep 226483 = 339725) B339725
theorem B226499 : Blo 223812 226499 := bstep (se 1 (by rfl) ⟨169874, by rfl⟩ : syracuseStep 226499 = 339749) B339749
theorem B2454725 : Blo 223812 2454725 := bstep (se 4 (by rfl) ⟨230130, by rfl⟩ : syracuseStep 2454725 = 460261) B460261
theorem B226515 : Blo 223812 226515 := bstep (se 1 (by rfl) ⟨169886, by rfl⟩ : syracuseStep 226515 = 339773) B339773
theorem B226531 : Blo 223812 226531 := bstep (se 1 (by rfl) ⟨169898, by rfl⟩ : syracuseStep 226531 = 339797) B339797
theorem B226547 : Blo 223812 226547 := bstep (se 1 (by rfl) ⟨169910, by rfl⟩ : syracuseStep 226547 = 339821) B339821
theorem B226563 : Blo 223812 226563 := bstep (se 1 (by rfl) ⟨169922, by rfl⟩ : syracuseStep 226563 = 339845) B339845
theorem B226579 : Blo 223812 226579 := bstep (se 1 (by rfl) ⟨169934, by rfl⟩ : syracuseStep 226579 = 339869) B339869
theorem B226595 : Blo 223812 226595 := bstep (se 1 (by rfl) ⟨169946, by rfl⟩ : syracuseStep 226595 = 339893) B339893
theorem B226611 : Blo 223812 226611 := bstep (se 1 (by rfl) ⟨169958, by rfl⟩ : syracuseStep 226611 = 339917) B339917
theorem B226627 : Blo 223812 226627 := bstep (se 1 (by rfl) ⟨169970, by rfl⟩ : syracuseStep 226627 = 339941) B339941
theorem B226643 : Blo 223812 226643 := bstep (se 1 (by rfl) ⟨169982, by rfl⟩ : syracuseStep 226643 = 339965) B339965
theorem B226659 : Blo 223812 226659 := bstep (se 1 (by rfl) ⟨169994, by rfl⟩ : syracuseStep 226659 = 339989) B339989
theorem B226675 : Blo 223812 226675 := bstep (se 1 (by rfl) ⟨170006, by rfl⟩ : syracuseStep 226675 = 340013) B340013
theorem B226691 : Blo 223812 226691 := bstep (se 1 (by rfl) ⟨170018, by rfl⟩ : syracuseStep 226691 = 340037) B340037
theorem B1144205 : Blo 223812 1144205 := bstep (se 3 (by rfl) ⟨214538, by rfl⟩ : syracuseStep 1144205 = 429077) B429077
theorem B226707 : Blo 223812 226707 := bstep (se 1 (by rfl) ⟨170030, by rfl⟩ : syracuseStep 226707 = 340061) B340061
theorem B226723 : Blo 223812 226723 := bstep (se 1 (by rfl) ⟨170042, by rfl⟩ : syracuseStep 226723 = 340085) B340085
theorem B226739 : Blo 223812 226739 := bstep (se 1 (by rfl) ⟨170054, by rfl⟩ : syracuseStep 226739 = 340109) B340109
theorem B226755 : Blo 223812 226755 := bstep (se 1 (by rfl) ⟨170066, by rfl⟩ : syracuseStep 226755 = 340133) B340133
theorem B226771 : Blo 223812 226771 := bstep (se 1 (by rfl) ⟨170078, by rfl⟩ : syracuseStep 226771 = 340157) B340157
theorem B226787 : Blo 223812 226787 := bstep (se 1 (by rfl) ⟨170090, by rfl⟩ : syracuseStep 226787 = 340181) B340181
theorem B226803 : Blo 223812 226803 := bstep (se 1 (by rfl) ⟨170102, by rfl⟩ : syracuseStep 226803 = 340205) B340205
theorem B226819 : Blo 223812 226819 := bstep (se 1 (by rfl) ⟨170114, by rfl⟩ : syracuseStep 226819 = 340229) B340229
theorem B226835 : Blo 223812 226835 := bstep (se 1 (by rfl) ⟨170126, by rfl⟩ : syracuseStep 226835 = 340253) B340253
theorem B226851 : Blo 223812 226851 := bstep (se 1 (by rfl) ⟨170138, by rfl⟩ : syracuseStep 226851 = 340277) B340277
theorem B226867 : Blo 223812 226867 := bstep (se 1 (by rfl) ⟨170150, by rfl⟩ : syracuseStep 226867 = 340301) B340301
theorem B226883 : Blo 223812 226883 := bstep (se 1 (by rfl) ⟨170162, by rfl⟩ : syracuseStep 226883 = 340325) B340325
theorem B226899 : Blo 223812 226899 := bstep (se 1 (by rfl) ⟨170174, by rfl⟩ : syracuseStep 226899 = 340349) B340349
theorem B226915 : Blo 223812 226915 := bstep (se 1 (by rfl) ⟨170186, by rfl⟩ : syracuseStep 226915 = 340373) B340373
theorem B226931 : Blo 223812 226931 := bstep (se 1 (by rfl) ⟨170198, by rfl⟩ : syracuseStep 226931 = 340397) B340397
theorem B226947 : Blo 223812 226947 := bstep (se 1 (by rfl) ⟨170210, by rfl⟩ : syracuseStep 226947 = 340421) B340421
theorem B226963 : Blo 223812 226963 := bstep (se 1 (by rfl) ⟨170222, by rfl⟩ : syracuseStep 226963 = 340445) B340445
theorem B226979 : Blo 223812 226979 := bstep (se 1 (by rfl) ⟨170234, by rfl⟩ : syracuseStep 226979 = 340469) B340469
theorem B226995 : Blo 223812 226995 := bstep (se 1 (by rfl) ⟨170246, by rfl⟩ : syracuseStep 226995 = 340493) B340493
theorem B227011 : Blo 223812 227011 := bstep (se 1 (by rfl) ⟨170258, by rfl⟩ : syracuseStep 227011 = 340517) B340517
theorem B227027 : Blo 223812 227027 := bstep (se 1 (by rfl) ⟨170270, by rfl⟩ : syracuseStep 227027 = 340541) B340541
theorem B1079011 : Blo 223812 1079011 := bstep (se 1 (by rfl) ⟨809258, by rfl⟩ : syracuseStep 1079011 = 1618517) B1618517
theorem B227043 : Blo 223812 227043 := bstep (se 1 (by rfl) ⟨170282, by rfl⟩ : syracuseStep 227043 = 340565) B340565
theorem B227059 : Blo 223812 227059 := bstep (se 1 (by rfl) ⟨170294, by rfl⟩ : syracuseStep 227059 = 340589) B340589
theorem B227075 : Blo 223812 227075 := bstep (se 1 (by rfl) ⟨170306, by rfl⟩ : syracuseStep 227075 = 340613) B340613
theorem B227091 : Blo 223812 227091 := bstep (se 1 (by rfl) ⟨170318, by rfl⟩ : syracuseStep 227091 = 340637) B340637
theorem B227107 : Blo 223812 227107 := bstep (se 1 (by rfl) ⟨170330, by rfl⟩ : syracuseStep 227107 = 340661) B340661
theorem B227123 : Blo 223812 227123 := bstep (se 1 (by rfl) ⟨170342, by rfl⟩ : syracuseStep 227123 = 340685) B340685
theorem B227139 : Blo 223812 227139 := bstep (se 1 (by rfl) ⟨170354, by rfl⟩ : syracuseStep 227139 = 340709) B340709
theorem B227155 : Blo 223812 227155 := bstep (se 1 (by rfl) ⟨170366, by rfl⟩ : syracuseStep 227155 = 340733) B340733
theorem B227171 : Blo 223812 227171 := bstep (se 1 (by rfl) ⟨170378, by rfl⟩ : syracuseStep 227171 = 340757) B340757
theorem B227187 : Blo 223812 227187 := bstep (se 1 (by rfl) ⟨170390, by rfl⟩ : syracuseStep 227187 = 340781) B340781
theorem B227203 : Blo 223812 227203 := bstep (se 1 (by rfl) ⟨170402, by rfl⟩ : syracuseStep 227203 = 340805) B340805
theorem B227219 : Blo 223812 227219 := bstep (se 1 (by rfl) ⟨170414, by rfl⟩ : syracuseStep 227219 = 340829) B340829
theorem B227235 : Blo 223812 227235 := bstep (se 1 (by rfl) ⟨170426, by rfl⟩ : syracuseStep 227235 = 340853) B340853
theorem B227251 : Blo 223812 227251 := bstep (se 1 (by rfl) ⟨170438, by rfl⟩ : syracuseStep 227251 = 340877) B340877
theorem B227267 : Blo 223812 227267 := bstep (se 1 (by rfl) ⟨170450, by rfl⟩ : syracuseStep 227267 = 340901) B340901
theorem B227283 : Blo 223812 227283 := bstep (se 1 (by rfl) ⟨170462, by rfl⟩ : syracuseStep 227283 = 340925) B340925
theorem B227299 : Blo 223812 227299 := bstep (se 1 (by rfl) ⟨170474, by rfl⟩ : syracuseStep 227299 = 340949) B340949
theorem B227315 : Blo 223812 227315 := bstep (se 1 (by rfl) ⟨170486, by rfl⟩ : syracuseStep 227315 = 340973) B340973
theorem B227331 : Blo 223812 227331 := bstep (se 1 (by rfl) ⟨170498, by rfl⟩ : syracuseStep 227331 = 340997) B340997
theorem B227347 : Blo 223812 227347 := bstep (se 1 (by rfl) ⟨170510, by rfl⟩ : syracuseStep 227347 = 341021) B341021
theorem B915491 : Blo 223812 915491 := bstep (se 1 (by rfl) ⟨686618, by rfl⟩ : syracuseStep 915491 = 1373237) B1373237
theorem B227363 : Blo 223812 227363 := bstep (se 1 (by rfl) ⟨170522, by rfl⟩ : syracuseStep 227363 = 341045) B341045
theorem B227379 : Blo 223812 227379 := bstep (se 1 (by rfl) ⟨170534, by rfl⟩ : syracuseStep 227379 = 341069) B341069
theorem B227395 : Blo 223812 227395 := bstep (se 1 (by rfl) ⟨170546, by rfl⟩ : syracuseStep 227395 = 341093) B341093
theorem B227411 : Blo 223812 227411 := bstep (se 1 (by rfl) ⟨170558, by rfl⟩ : syracuseStep 227411 = 341117) B341117
theorem B1931363 : Blo 223812 1931363 := bstep (se 1 (by rfl) ⟨1448522, by rfl⟩ : syracuseStep 1931363 = 2897045) B2897045
theorem B227427 : Blo 223812 227427 := bstep (se 1 (by rfl) ⟨170570, by rfl⟩ : syracuseStep 227427 = 341141) B341141
theorem B227443 : Blo 223812 227443 := bstep (se 1 (by rfl) ⟨170582, by rfl⟩ : syracuseStep 227443 = 341165) B341165
theorem B227459 : Blo 223812 227459 := bstep (se 1 (by rfl) ⟨170594, by rfl⟩ : syracuseStep 227459 = 341189) B341189
theorem B227475 : Blo 223812 227475 := bstep (se 1 (by rfl) ⟨170606, by rfl⟩ : syracuseStep 227475 = 341213) B341213
theorem B227491 : Blo 223812 227491 := bstep (se 1 (by rfl) ⟨170618, by rfl⟩ : syracuseStep 227491 = 341237) B341237
theorem B227507 : Blo 223812 227507 := bstep (se 1 (by rfl) ⟨170630, by rfl⟩ : syracuseStep 227507 = 341261) B341261
theorem B227523 : Blo 223812 227523 := bstep (se 1 (by rfl) ⟨170642, by rfl⟩ : syracuseStep 227523 = 341285) B341285
theorem B227539 : Blo 223812 227539 := bstep (se 1 (by rfl) ⟨170654, by rfl⟩ : syracuseStep 227539 = 341309) B341309
theorem B227555 : Blo 223812 227555 := bstep (se 1 (by rfl) ⟨170666, by rfl⟩ : syracuseStep 227555 = 341333) B341333
theorem B227571 : Blo 223812 227571 := bstep (se 1 (by rfl) ⟨170678, by rfl⟩ : syracuseStep 227571 = 341357) B341357
theorem B227587 : Blo 223812 227587 := bstep (se 1 (by rfl) ⟨170690, by rfl⟩ : syracuseStep 227587 = 341381) B341381
theorem B227603 : Blo 223812 227603 := bstep (se 1 (by rfl) ⟨170702, by rfl⟩ : syracuseStep 227603 = 341405) B341405
theorem B227619 : Blo 223812 227619 := bstep (se 1 (by rfl) ⟨170714, by rfl⟩ : syracuseStep 227619 = 341429) B341429
theorem B227635 : Blo 223812 227635 := bstep (se 1 (by rfl) ⟨170726, by rfl⟩ : syracuseStep 227635 = 341453) B341453
theorem B227651 : Blo 223812 227651 := bstep (se 1 (by rfl) ⟨170738, by rfl⟩ : syracuseStep 227651 = 341477) B341477
theorem B227667 : Blo 223812 227667 := bstep (se 1 (by rfl) ⟨170750, by rfl⟩ : syracuseStep 227667 = 341501) B341501
theorem B227683 : Blo 223812 227683 := bstep (se 1 (by rfl) ⟨170762, by rfl⟩ : syracuseStep 227683 = 341525) B341525
theorem B1571185 : Blo 223812 1571185 := bstep (se 2 (by rfl) ⟨589194, by rfl⟩ : syracuseStep 1571185 = 1178389) B1178389
theorem B227699 : Blo 223812 227699 := bstep (se 1 (by rfl) ⟨170774, by rfl⟩ : syracuseStep 227699 = 341549) B341549
theorem B227715 : Blo 223812 227715 := bstep (se 1 (by rfl) ⟨170786, by rfl⟩ : syracuseStep 227715 = 341573) B341573
theorem B227731 : Blo 223812 227731 := bstep (se 1 (by rfl) ⟨170798, by rfl⟩ : syracuseStep 227731 = 341597) B341597
theorem B227747 : Blo 223812 227747 := bstep (se 1 (by rfl) ⟨170810, by rfl⟩ : syracuseStep 227747 = 341621) B341621
theorem B227763 : Blo 223812 227763 := bstep (se 1 (by rfl) ⟨170822, by rfl⟩ : syracuseStep 227763 = 341645) B341645
theorem B227779 : Blo 223812 227779 := bstep (se 1 (by rfl) ⟨170834, by rfl⟩ : syracuseStep 227779 = 341669) B341669
theorem B9238981 : Blo 223812 9238981 := bstep (se 4 (by rfl) ⟨866154, by rfl⟩ : syracuseStep 9238981 = 1732309) B1732309
theorem B227795 : Blo 223812 227795 := bstep (se 1 (by rfl) ⟨170846, by rfl⟩ : syracuseStep 227795 = 341693) B341693
theorem B227811 : Blo 223812 227811 := bstep (se 1 (by rfl) ⟨170858, by rfl⟩ : syracuseStep 227811 = 341717) B341717
theorem B719405 : Blo 223812 719405 := bstep (se 3 (by rfl) ⟨134888, by rfl⟩ : syracuseStep 719405 = 269777) B269777
theorem B9435761 : Blo 223812 9435761 := bstep (se 2 (by rfl) ⟨3538410, by rfl⟩ : syracuseStep 9435761 = 7076821) B7076821
theorem B359075 : Blo 223812 359075 := bstep (se 1 (by rfl) ⟨269306, by rfl⟩ : syracuseStep 359075 = 538613) B538613
theorem B1309603 : Blo 223812 1309603 := bstep (se 1 (by rfl) ⟨982202, by rfl⟩ : syracuseStep 1309603 = 1964405) B1964405
theorem B359363 : Blo 223812 359363 := bstep (se 1 (by rfl) ⟨269522, by rfl⟩ : syracuseStep 359363 = 539045) B539045
theorem B228403 : Blo 223812 228403 := bstep (se 1 (by rfl) ⟨171302, by rfl⟩ : syracuseStep 228403 = 342605) B342605
theorem B851107 : Blo 223812 851107 := bstep (se 1 (by rfl) ⟨638330, by rfl⟩ : syracuseStep 851107 = 1276661) B1276661
theorem B359587 : Blo 223812 359587 := bstep (se 1 (by rfl) ⟨269690, by rfl⟩ : syracuseStep 359587 = 539381) B539381
theorem B720173 : Blo 223812 720173 := bstep (se 3 (by rfl) ⟨135032, by rfl⟩ : syracuseStep 720173 = 270065) B270065
theorem B4423025 : Blo 223812 4423025 := bstep (se 2 (by rfl) ⟨1658634, by rfl⟩ : syracuseStep 4423025 = 3317269) B3317269
theorem B1441165 : Blo 223812 1441165 := bstep (se 3 (by rfl) ⟨270218, by rfl⟩ : syracuseStep 1441165 = 540437) B540437
theorem B425425 : Blo 223812 425425 := bstep (se 2 (by rfl) ⟨159534, by rfl⟩ : syracuseStep 425425 = 319069) B319069
theorem B720685 : Blo 223812 720685 := bstep (se 3 (by rfl) ⟨135128, by rfl⟩ : syracuseStep 720685 = 270257) B270257
theorem B425827 : Blo 223812 425827 := bstep (se 1 (by rfl) ⟨319370, by rfl⟩ : syracuseStep 425827 = 638741) B638741
theorem B360305 : Blo 223812 360305 := bstep (se 2 (by rfl) ⟨135114, by rfl⟩ : syracuseStep 360305 = 270229) B270229
theorem B491377 : Blo 223812 491377 := bstep (se 2 (by rfl) ⟨184266, by rfl⟩ : syracuseStep 491377 = 368533) B368533
theorem B425873 : Blo 223812 425873 := bstep (se 2 (by rfl) ⟨159702, by rfl⟩ : syracuseStep 425873 = 319405) B319405
theorem B458995 : Blo 223812 458995 := bstep (se 1 (by rfl) ⟨344246, by rfl⟩ : syracuseStep 458995 = 688493) B688493
theorem B360715 : Blo 223812 360715 := bstep (se 1 (by rfl) ⟨270536, by rfl⟩ : syracuseStep 360715 = 541073) B541073
theorem B1278301 : Blo 223812 1278301 := bstep (se 3 (by rfl) ⟨239681, by rfl⟩ : syracuseStep 1278301 = 479363) B479363
theorem B229879 : Blo 223812 229879 := bstep (se 1 (by rfl) ⟨172409, by rfl⟩ : syracuseStep 229879 = 344819) B344819
theorem B426647 : Blo 223812 426647 := bstep (se 1 (by rfl) ⟨319985, by rfl⟩ : syracuseStep 426647 = 639971) B639971
theorem B524951 : Blo 223812 524951 := bstep (se 1 (by rfl) ⟨393713, by rfl⟩ : syracuseStep 524951 = 787427) B787427
theorem B361163 : Blo 223812 361163 := bstep (se 1 (by rfl) ⟨270872, by rfl⟩ : syracuseStep 361163 = 541745) B541745
theorem B820057 : Blo 223812 820057 := bstep (se 2 (by rfl) ⟨307521, by rfl⟩ : syracuseStep 820057 = 615043) B615043
theorem B721943 : Blo 223812 721943 := bstep (se 1 (by rfl) ⟨541457, by rfl⟩ : syracuseStep 721943 = 1082915) B1082915
theorem B853037 : Blo 223812 853037 := bstep (se 3 (by rfl) ⟨159944, by rfl⟩ : syracuseStep 853037 = 319889) B319889
theorem B1934401 : Blo 223812 1934401 := bstep (se 2 (by rfl) ⟨725400, by rfl⟩ : syracuseStep 1934401 = 1450801) B1450801
theorem B427187 : Blo 223812 427187 := bstep (se 1 (by rfl) ⟨320390, by rfl⟩ : syracuseStep 427187 = 640781) B640781
theorem B492851 : Blo 223812 492851 := bstep (se 1 (by rfl) ⟨369638, by rfl⟩ : syracuseStep 492851 = 739277) B739277
theorem B361945 : Blo 223812 361945 := bstep (se 2 (by rfl) ⟨135729, by rfl⟩ : syracuseStep 361945 = 271459) B271459
theorem B362009 : Blo 223812 362009 := bstep (se 2 (by rfl) ⟨135753, by rfl⟩ : syracuseStep 362009 = 271507) B271507
theorem B525911 : Blo 223812 525911 := bstep (se 1 (by rfl) ⟨394433, by rfl⟩ : syracuseStep 525911 = 788867) B788867
theorem B427673 : Blo 223812 427673 := bstep (se 2 (by rfl) ⟨160377, by rfl⟩ : syracuseStep 427673 = 320755) B320755
theorem B362137 : Blo 223812 362137 := bstep (se 2 (by rfl) ⟨135801, by rfl⟩ : syracuseStep 362137 = 271603) B271603
theorem B853811 : Blo 223812 853811 := bstep (se 1 (by rfl) ⟨640358, by rfl⟩ : syracuseStep 853811 = 1280717) B1280717
theorem B1705859 : Blo 223812 1705859 := bstep (se 1 (by rfl) ⟨1279394, by rfl⟩ : syracuseStep 1705859 = 2558789) B2558789
theorem B3835997 : Blo 223812 3835997 := bstep (se 3 (by rfl) ⟨719249, by rfl⟩ : syracuseStep 3835997 = 1438499) B1438499
theorem B493697 : Blo 223812 493697 := bstep (se 2 (by rfl) ⟨185136, by rfl⟩ : syracuseStep 493697 = 370273) B370273
theorem B755891 : Blo 223812 755891 := bstep (se 1 (by rfl) ⟨566918, by rfl⟩ : syracuseStep 755891 = 1133837) B1133837
theorem B723275 : Blo 223812 723275 := bstep (se 1 (by rfl) ⟨542456, by rfl⟩ : syracuseStep 723275 = 1084913) B1084913
theorem B756161 : Blo 223812 756161 := bstep (se 2 (by rfl) ⟨283560, by rfl⟩ : syracuseStep 756161 = 567121) B567121
theorem B1149457 : Blo 223812 1149457 := bstep (se 2 (by rfl) ⟨431046, by rfl⟩ : syracuseStep 1149457 = 862093) B862093
theorem B1149713 : Blo 223812 1149713 := bstep (se 2 (by rfl) ⟨431142, by rfl⟩ : syracuseStep 1149713 = 862285) B862285
theorem B985945 : Blo 223812 985945 := bstep (se 2 (by rfl) ⟨369729, by rfl⟩ : syracuseStep 985945 = 739459) B739459
theorem B723863 : Blo 223812 723863 := bstep (se 1 (by rfl) ⟨542897, by rfl⟩ : syracuseStep 723863 = 1085795) B1085795
theorem B1149875 : Blo 223812 1149875 := bstep (se 1 (by rfl) ⟨862406, by rfl⟩ : syracuseStep 1149875 = 1724813) B1724813
theorem B756701 : Blo 223812 756701 := bstep (se 3 (by rfl) ⟨141881, by rfl⟩ : syracuseStep 756701 = 283763) B283763
theorem B429131 : Blo 223812 429131 := bstep (se 1 (by rfl) ⟨321848, by rfl⟩ : syracuseStep 429131 = 643697) B643697
theorem B691289 : Blo 223812 691289 := bstep (se 2 (by rfl) ⟨259233, by rfl⟩ : syracuseStep 691289 = 518467) B518467
theorem B429313 : Blo 223812 429313 := bstep (se 2 (by rfl) ⟨160992, by rfl⟩ : syracuseStep 429313 = 321985) B321985
theorem B855299 : Blo 223812 855299 := bstep (se 1 (by rfl) ⟨641474, by rfl⟩ : syracuseStep 855299 = 1282949) B1282949
theorem B724403 : Blo 223812 724403 := bstep (se 1 (by rfl) ⟨543302, by rfl⟩ : syracuseStep 724403 = 1086605) B1086605
theorem B691649 : Blo 223812 691649 := bstep (se 2 (by rfl) ⟨259368, by rfl⟩ : syracuseStep 691649 = 518737) B518737
theorem B495065 : Blo 223812 495065 := bstep (se 2 (by rfl) ⟨185649, by rfl⟩ : syracuseStep 495065 = 371299) B371299
theorem B429761 : Blo 223812 429761 := bstep (se 2 (by rfl) ⟨161160, by rfl⟩ : syracuseStep 429761 = 322321) B322321
theorem B855755 : Blo 223812 855755 := bstep (se 1 (by rfl) ⟨641816, by rfl⟩ : syracuseStep 855755 = 1283633) B1283633
theorem B855953 : Blo 223812 855953 := bstep (se 2 (by rfl) ⟨320982, by rfl⟩ : syracuseStep 855953 = 641965) B641965
theorem B430103 : Blo 223812 430103 := bstep (se 1 (by rfl) ⟨322577, by rfl⟩ : syracuseStep 430103 = 645155) B645155
theorem B757835 : Blo 223812 757835 := bstep (se 1 (by rfl) ⟨568376, by rfl⟩ : syracuseStep 757835 = 1136753) B1136753
theorem B692545 : Blo 223812 692545 := bstep (se 2 (by rfl) ⟨259704, by rfl⟩ : syracuseStep 692545 = 519409) B519409
theorem B758105 : Blo 223812 758105 := bstep (se 2 (by rfl) ⟨284289, by rfl⟩ : syracuseStep 758105 = 568579) B568579
theorem B856727 : Blo 223812 856727 := bstep (se 1 (by rfl) ⟨642545, by rfl⟩ : syracuseStep 856727 = 1285091) B1285091
theorem B430771 : Blo 223812 430771 := bstep (se 1 (by rfl) ⟨323078, by rfl⟩ : syracuseStep 430771 = 646157) B646157
theorem B4854593 : Blo 223812 4854593 := bstep (se 2 (by rfl) ⟨1820472, by rfl⟩ : syracuseStep 4854593 = 3640945) B3640945
theorem B1151819 : Blo 223812 1151819 := bstep (se 1 (by rfl) ⟨863864, by rfl⟩ : syracuseStep 1151819 = 1727729) B1727729
theorem B856925 : Blo 223812 856925 := bstep (se 3 (by rfl) ⟨160673, by rfl⟩ : syracuseStep 856925 = 321347) B321347
theorem B758807 : Blo 223812 758807 := bstep (se 1 (by rfl) ⟨569105, by rfl⟩ : syracuseStep 758807 = 1138211) B1138211
theorem B431219 : Blo 223812 431219 := bstep (se 1 (by rfl) ⟨323414, by rfl⟩ : syracuseStep 431219 = 646829) B646829
theorem B431257 : Blo 223812 431257 := bstep (se 2 (by rfl) ⟨161721, by rfl⟩ : syracuseStep 431257 = 323443) B323443
theorem B1709261 : Blo 223812 1709261 := bstep (se 3 (by rfl) ⟨320486, by rfl⟩ : syracuseStep 1709261 = 640973) B640973
theorem B2954501 : Blo 223812 2954501 := bstep (se 4 (by rfl) ⟨276984, by rfl⟩ : syracuseStep 2954501 = 553969) B553969
theorem B1086871 : Blo 223812 1086871 := bstep (se 1 (by rfl) ⟨815153, by rfl⟩ : syracuseStep 1086871 = 1630307) B1630307
theorem B3478963 : Blo 223812 3478963 := bstep (se 1 (by rfl) ⟨2609222, by rfl⟩ : syracuseStep 3478963 = 5218445) B5218445
theorem B1021463 : Blo 223812 1021463 := bstep (se 1 (by rfl) ⟨766097, by rfl⟩ : syracuseStep 1021463 = 1532195) B1532195
theorem B759347 : Blo 223812 759347 := bstep (se 1 (by rfl) ⟨569510, by rfl⟩ : syracuseStep 759347 = 1139021) B1139021
theorem B431705 : Blo 223812 431705 := bstep (se 2 (by rfl) ⟨161889, by rfl⟩ : syracuseStep 431705 = 323779) B323779
theorem B1218149 : Blo 223812 1218149 := bstep (se 4 (by rfl) ⟨114201, by rfl⟩ : syracuseStep 1218149 = 228403) B228403
theorem B1709747 : Blo 223812 1709747 := bstep (se 1 (by rfl) ⟨1282310, by rfl⟩ : syracuseStep 1709747 = 2564621) B2564621
theorem B759617 : Blo 223812 759617 := bstep (se 2 (by rfl) ⟨284856, by rfl⟩ : syracuseStep 759617 = 569713) B569713
theorem B956609 : Blo 223812 956609 := bstep (se 2 (by rfl) ⟨358728, by rfl⟩ : syracuseStep 956609 = 717457) B717457
theorem B432449 : Blo 223812 432449 := bstep (se 2 (by rfl) ⟨162168, by rfl⟩ : syracuseStep 432449 = 324337) B324337
theorem B760157 : Blo 223812 760157 := bstep (se 3 (by rfl) ⟨142529, by rfl⟩ : syracuseStep 760157 = 285059) B285059
theorem B367001 : Blo 223812 367001 := bstep (se 2 (by rfl) ⟨137625, by rfl⟩ : syracuseStep 367001 = 275251) B275251
theorem B1022381 : Blo 223812 1022381 := bstep (se 3 (by rfl) ⟨191696, by rfl⟩ : syracuseStep 1022381 = 383393) B383393
theorem B4004275 : Blo 223812 4004275 := bstep (se 1 (by rfl) ⟨3003206, by rfl⟩ : syracuseStep 4004275 = 6006413) B6006413
theorem B858883 : Blo 223812 858883 := bstep (se 1 (by rfl) ⟨644162, by rfl⟩ : syracuseStep 858883 = 1288325) B1288325
theorem B859187 : Blo 223812 859187 := bstep (se 1 (by rfl) ⟨644390, by rfl⟩ : syracuseStep 859187 = 1288781) B1288781
theorem B2333771 : Blo 223812 2333771 := bstep (se 1 (by rfl) ⟨1750328, by rfl⟩ : syracuseStep 2333771 = 3500657) B3500657
theorem B1711205 : Blo 223812 1711205 := bstep (se 4 (by rfl) ⟨160425, by rfl⟩ : syracuseStep 1711205 = 320851) B320851
theorem B761291 : Blo 223812 761291 := bstep (se 1 (by rfl) ⟨570968, by rfl⟩ : syracuseStep 761291 = 1141937) B1141937
theorem B958027 : Blo 223812 958027 := bstep (se 1 (by rfl) ⟨718520, by rfl⟩ : syracuseStep 958027 = 1437041) B1437041
theorem B1711691 : Blo 223812 1711691 := bstep (se 1 (by rfl) ⟨1283768, by rfl⟩ : syracuseStep 1711691 = 2567537) B2567537
theorem B269911 : Blo 223812 269911 := bstep (se 1 (by rfl) ⟨202433, by rfl⟩ : syracuseStep 269911 = 404867) B404867
theorem B2301571 : Blo 223812 2301571 := bstep (se 1 (by rfl) ⟨1726178, by rfl⟩ : syracuseStep 2301571 = 3452357) B3452357
theorem B859841 : Blo 223812 859841 := bstep (se 2 (by rfl) ⟨322440, by rfl⟩ : syracuseStep 859841 = 644881) B644881
theorem B1023691 : Blo 223812 1023691 := bstep (se 1 (by rfl) ⟨767768, by rfl⟩ : syracuseStep 1023691 = 1535537) B1535537
theorem B761561 : Blo 223812 761561 := bstep (se 2 (by rfl) ⟨285585, by rfl⟩ : syracuseStep 761561 = 571171) B571171
theorem B958301 : Blo 223812 958301 := bstep (se 3 (by rfl) ⟨179681, by rfl⟩ : syracuseStep 958301 = 359363) B359363
theorem B1613699 : Blo 223812 1613699 := bstep (se 1 (by rfl) ⟨1210274, by rfl⟩ : syracuseStep 1613699 = 2420549) B2420549
theorem B1220483 : Blo 223812 1220483 := bstep (se 1 (by rfl) ⟨915362, by rfl⟩ : syracuseStep 1220483 = 1830725) B1830725
theorem B335819 : Blo 223812 335819 := bstep (se 1 (by rfl) ⟨251864, by rfl⟩ : syracuseStep 335819 = 503729) B503729
theorem B335831 : Blo 223812 335831 := bstep (se 1 (by rfl) ⟨251873, by rfl⟩ : syracuseStep 335831 = 503747) B503747
theorem B1941509 : Blo 223812 1941509 := bstep (se 4 (by rfl) ⟨182016, by rfl⟩ : syracuseStep 1941509 = 364033) B364033
theorem B368651 : Blo 223812 368651 := bstep (se 1 (by rfl) ⟨276488, by rfl⟩ : syracuseStep 368651 = 552977) B552977
theorem B335897 : Blo 223812 335897 := bstep (se 2 (by rfl) ⟨125961, by rfl⟩ : syracuseStep 335897 = 251923) B251923
theorem B336011 : Blo 223812 336011 := bstep (se 1 (by rfl) ⟨252008, by rfl⟩ : syracuseStep 336011 = 504017) B504017
theorem B336023 : Blo 223812 336023 := bstep (se 1 (by rfl) ⟨252017, by rfl⟩ : syracuseStep 336023 = 504035) B504035
theorem B1450163 : Blo 223812 1450163 := bstep (se 1 (by rfl) ⟨1087622, by rfl⟩ : syracuseStep 1450163 = 2175245) B2175245
theorem B336089 : Blo 223812 336089 := bstep (se 2 (by rfl) ⟨126033, by rfl⟩ : syracuseStep 336089 = 252067) B252067
theorem B336203 : Blo 223812 336203 := bstep (se 1 (by rfl) ⟨252152, by rfl⟩ : syracuseStep 336203 = 504305) B504305
theorem B336215 : Blo 223812 336215 := bstep (se 1 (by rfl) ⟨252161, by rfl⟩ : syracuseStep 336215 = 504323) B504323
theorem B4366709 : Blo 223812 4366709 := bstep (se 5 (by rfl) ⟨204689, by rfl⟩ : syracuseStep 4366709 = 409379) B409379
theorem B762263 : Blo 223812 762263 := bstep (se 1 (by rfl) ⟨571697, by rfl⟩ : syracuseStep 762263 = 1143395) B1143395
theorem B336281 : Blo 223812 336281 := bstep (se 2 (by rfl) ⟨126105, by rfl⟩ : syracuseStep 336281 = 252211) B252211
theorem B336395 : Blo 223812 336395 := bstep (se 1 (by rfl) ⟨252296, by rfl⟩ : syracuseStep 336395 = 504593) B504593
theorem B336407 : Blo 223812 336407 := bstep (se 1 (by rfl) ⟨252305, by rfl⟩ : syracuseStep 336407 = 504611) B504611
theorem B3875363 : Blo 223812 3875363 := bstep (se 1 (by rfl) ⟨2906522, by rfl⟩ : syracuseStep 3875363 = 5813045) B5813045
theorem B336473 : Blo 223812 336473 := bstep (se 2 (by rfl) ⟨126177, by rfl⟩ : syracuseStep 336473 = 252355) B252355
theorem B434803 : Blo 223812 434803 := bstep (se 1 (by rfl) ⟨326102, by rfl⟩ : syracuseStep 434803 = 652205) B652205
theorem B336587 : Blo 223812 336587 := bstep (se 1 (by rfl) ⟨252440, by rfl⟩ : syracuseStep 336587 = 504881) B504881
theorem B336599 : Blo 223812 336599 := bstep (se 1 (by rfl) ⟨252449, by rfl⟩ : syracuseStep 336599 = 504899) B504899
theorem B336665 : Blo 223812 336665 := bstep (se 2 (by rfl) ⟨126249, by rfl⟩ : syracuseStep 336665 = 252499) B252499
theorem B336779 : Blo 223812 336779 := bstep (se 1 (by rfl) ⟨252584, by rfl⟩ : syracuseStep 336779 = 505169) B505169
theorem B336791 : Blo 223812 336791 := bstep (se 1 (by rfl) ⟨252593, by rfl⟩ : syracuseStep 336791 = 505187) B505187
theorem B861101 : Blo 223812 861101 := bstep (se 3 (by rfl) ⟨161456, by rfl⟩ : syracuseStep 861101 = 322913) B322913
theorem B762803 : Blo 223812 762803 := bstep (se 1 (by rfl) ⟨572102, by rfl⟩ : syracuseStep 762803 = 1144205) B1144205
theorem B861131 : Blo 223812 861131 := bstep (se 1 (by rfl) ⟨645848, by rfl⟩ : syracuseStep 861131 = 1291697) B1291697
theorem B336857 : Blo 223812 336857 := bstep (se 2 (by rfl) ⟨126321, by rfl⟩ : syracuseStep 336857 = 252643) B252643
theorem B369625 : Blo 223812 369625 := bstep (se 2 (by rfl) ⟨138609, by rfl⟩ : syracuseStep 369625 = 277219) B277219
theorem B336971 : Blo 223812 336971 := bstep (se 1 (by rfl) ⟨252728, by rfl⟩ : syracuseStep 336971 = 505457) B505457
theorem B336983 : Blo 223812 336983 := bstep (se 1 (by rfl) ⟨252737, by rfl⟩ : syracuseStep 336983 = 505475) B505475
theorem B1156189 : Blo 223812 1156189 := bstep (se 3 (by rfl) ⟨216785, by rfl⟩ : syracuseStep 1156189 = 433571) B433571
theorem B337049 : Blo 223812 337049 := bstep (se 2 (by rfl) ⟨126393, by rfl⟩ : syracuseStep 337049 = 252787) B252787
theorem B763073 : Blo 223812 763073 := bstep (se 2 (by rfl) ⟨286152, by rfl⟩ : syracuseStep 763073 = 572305) B572305
theorem B1746137 : Blo 223812 1746137 := bstep (se 2 (by rfl) ⟨654801, by rfl⟩ : syracuseStep 1746137 = 1309603) B1309603
theorem B337163 : Blo 223812 337163 := bstep (se 1 (by rfl) ⟨252872, by rfl⟩ : syracuseStep 337163 = 505745) B505745
theorem B337175 : Blo 223812 337175 := bstep (se 1 (by rfl) ⟨252881, by rfl⟩ : syracuseStep 337175 = 505763) B505763
theorem B337241 : Blo 223812 337241 := bstep (se 2 (by rfl) ⟨126465, by rfl⟩ : syracuseStep 337241 = 252931) B252931
theorem B1287575 : Blo 223812 1287575 := bstep (se 1 (by rfl) ⟨965681, by rfl⟩ : syracuseStep 1287575 = 1931363) B1931363
theorem B337355 : Blo 223812 337355 := bstep (se 1 (by rfl) ⟨253016, by rfl⟩ : syracuseStep 337355 = 506033) B506033
theorem B337367 : Blo 223812 337367 := bstep (se 1 (by rfl) ⟨253025, by rfl⟩ : syracuseStep 337367 = 506051) B506051
theorem B337433 : Blo 223812 337433 := bstep (se 2 (by rfl) ⟨126537, by rfl⟩ : syracuseStep 337433 = 253075) B253075
theorem B861785 : Blo 223812 861785 := bstep (se 2 (by rfl) ⟨323169, by rfl⟩ : syracuseStep 861785 = 646339) B646339
theorem B1451621 : Blo 223812 1451621 := bstep (se 4 (by rfl) ⟨136089, by rfl⟩ : syracuseStep 1451621 = 272179) B272179
theorem B337547 : Blo 223812 337547 := bstep (se 1 (by rfl) ⟨253160, by rfl⟩ : syracuseStep 337547 = 506321) B506321
theorem B337559 : Blo 223812 337559 := bstep (se 1 (by rfl) ⟨253169, by rfl⟩ : syracuseStep 337559 = 506339) B506339
theorem B337625 : Blo 223812 337625 := bstep (se 2 (by rfl) ⟨126609, by rfl⟩ : syracuseStep 337625 = 253219) B253219
theorem B763613 : Blo 223812 763613 := bstep (se 3 (by rfl) ⟨143177, by rfl⟩ : syracuseStep 763613 = 286355) B286355
theorem B239383 : Blo 223812 239383 := bstep (se 1 (by rfl) ⟨179537, by rfl⟩ : syracuseStep 239383 = 359075) B359075
theorem B337739 : Blo 223812 337739 := bstep (se 1 (by rfl) ⟨253304, by rfl⟩ : syracuseStep 337739 = 506609) B506609
theorem B337751 : Blo 223812 337751 := bstep (se 1 (by rfl) ⟨253313, by rfl⟩ : syracuseStep 337751 = 506627) B506627
theorem B862103 : Blo 223812 862103 := bstep (se 1 (by rfl) ⟨646577, by rfl⟩ : syracuseStep 862103 = 1293155) B1293155
theorem B337817 : Blo 223812 337817 := bstep (se 2 (by rfl) ⟨126681, by rfl⟩ : syracuseStep 337817 = 253363) B253363
theorem B567233 : Blo 223812 567233 := bstep (se 2 (by rfl) ⟨212712, by rfl⟩ : syracuseStep 567233 = 425425) B425425
theorem B337931 : Blo 223812 337931 := bstep (se 1 (by rfl) ⟨253448, by rfl⟩ : syracuseStep 337931 = 506897) B506897
theorem B337943 : Blo 223812 337943 := bstep (se 1 (by rfl) ⟨253457, by rfl⟩ : syracuseStep 337943 = 506915) B506915
theorem B338009 : Blo 223812 338009 := bstep (se 2 (by rfl) ⟨126753, by rfl⟩ : syracuseStep 338009 = 253507) B253507
theorem B3582133 : Blo 223812 3582133 := bstep (se 5 (by rfl) ⟨167912, by rfl⟩ : syracuseStep 3582133 = 335825) B335825
theorem B338123 : Blo 223812 338123 := bstep (se 1 (by rfl) ⟨253592, by rfl⟩ : syracuseStep 338123 = 507185) B507185
theorem B338135 : Blo 223812 338135 := bstep (se 1 (by rfl) ⟨253601, by rfl⟩ : syracuseStep 338135 = 507203) B507203
theorem B338201 : Blo 223812 338201 := bstep (se 2 (by rfl) ⟨126825, by rfl⟩ : syracuseStep 338201 = 253651) B253651
theorem B403787 : Blo 223812 403787 := bstep (se 1 (by rfl) ⟨302840, by rfl⟩ : syracuseStep 403787 = 605681) B605681
theorem B338315 : Blo 223812 338315 := bstep (se 1 (by rfl) ⟨253736, by rfl⟩ : syracuseStep 338315 = 507473) B507473
theorem B960913 : Blo 223812 960913 := bstep (se 2 (by rfl) ⟨360342, by rfl⟩ : syracuseStep 960913 = 720685) B720685
theorem B338327 : Blo 223812 338327 := bstep (se 1 (by rfl) ⟨253745, by rfl⟩ : syracuseStep 338327 = 507491) B507491
theorem B567769 : Blo 223812 567769 := bstep (se 2 (by rfl) ⟨212913, by rfl⟩ : syracuseStep 567769 = 425827) B425827
theorem B338393 : Blo 223812 338393 := bstep (se 2 (by rfl) ⟨126897, by rfl⟩ : syracuseStep 338393 = 253795) B253795
theorem B862771 : Blo 223812 862771 := bstep (se 1 (by rfl) ⟨647078, by rfl⟩ : syracuseStep 862771 = 1294157) B1294157
theorem B240203 : Blo 223812 240203 := bstep (se 1 (by rfl) ⟨180152, by rfl⟩ : syracuseStep 240203 = 360305) B360305
theorem B338507 : Blo 223812 338507 := bstep (se 1 (by rfl) ⟨253880, by rfl⟩ : syracuseStep 338507 = 507761) B507761
theorem B338519 : Blo 223812 338519 := bstep (se 1 (by rfl) ⟨253889, by rfl⟩ : syracuseStep 338519 = 507779) B507779
theorem B338585 : Blo 223812 338585 := bstep (se 2 (by rfl) ⟨126969, by rfl⟩ : syracuseStep 338585 = 253939) B253939
theorem B240331 : Blo 223812 240331 := bstep (se 1 (by rfl) ⟨180248, by rfl⟩ : syracuseStep 240331 = 360497) B360497
theorem B338699 : Blo 223812 338699 := bstep (se 1 (by rfl) ⟨254024, by rfl⟩ : syracuseStep 338699 = 508049) B508049
theorem B338711 : Blo 223812 338711 := bstep (se 1 (by rfl) ⟨254033, by rfl⟩ : syracuseStep 338711 = 508067) B508067
theorem B764747 : Blo 223812 764747 := bstep (se 1 (by rfl) ⟨573560, by rfl⟩ : syracuseStep 764747 = 1147121) B1147121
theorem B273227 : Blo 223812 273227 := bstep (se 1 (by rfl) ⟨204920, by rfl⟩ : syracuseStep 273227 = 409841) B409841
theorem B338777 : Blo 223812 338777 := bstep (se 2 (by rfl) ⟨127041, by rfl⟩ : syracuseStep 338777 = 254083) B254083
theorem B338891 : Blo 223812 338891 := bstep (se 1 (by rfl) ⟨254168, by rfl⟩ : syracuseStep 338891 = 508337) B508337
theorem B338903 : Blo 223812 338903 := bstep (se 1 (by rfl) ⟨254177, by rfl⟩ : syracuseStep 338903 = 508355) B508355
theorem B338969 : Blo 223812 338969 := bstep (se 2 (by rfl) ⟨127113, by rfl⟩ : syracuseStep 338969 = 254227) B254227
theorem B765017 : Blo 223812 765017 := bstep (se 2 (by rfl) ⟨286881, by rfl⟩ : syracuseStep 765017 = 573763) B573763
theorem B339083 : Blo 223812 339083 := bstep (se 1 (by rfl) ⟨254312, by rfl⟩ : syracuseStep 339083 = 508625) B508625
theorem B339095 : Blo 223812 339095 := bstep (se 1 (by rfl) ⟨254321, by rfl⟩ : syracuseStep 339095 = 508643) B508643
theorem B339161 : Blo 223812 339161 := bstep (se 2 (by rfl) ⟨127185, by rfl⟩ : syracuseStep 339161 = 254371) B254371
theorem B339275 : Blo 223812 339275 := bstep (se 1 (by rfl) ⟨254456, by rfl⟩ : syracuseStep 339275 = 508913) B508913
theorem B339287 : Blo 223812 339287 := bstep (se 1 (by rfl) ⟨254465, by rfl⟩ : syracuseStep 339287 = 508931) B508931
theorem B339353 : Blo 223812 339353 := bstep (se 2 (by rfl) ⟨127257, by rfl⟩ : syracuseStep 339353 = 254515) B254515
theorem B339467 : Blo 223812 339467 := bstep (se 1 (by rfl) ⟨254600, by rfl⟩ : syracuseStep 339467 = 509201) B509201
theorem B339479 : Blo 223812 339479 := bstep (se 1 (by rfl) ⟨254609, by rfl⟩ : syracuseStep 339479 = 509219) B509219
theorem B1945133 : Blo 223812 1945133 := bstep (se 3 (by rfl) ⟨364712, by rfl⟩ : syracuseStep 1945133 = 729425) B729425
theorem B568883 : Blo 223812 568883 := bstep (se 1 (by rfl) ⟨426662, by rfl⟩ : syracuseStep 568883 = 853325) B853325
theorem B339545 : Blo 223812 339545 := bstep (se 2 (by rfl) ⟨127329, by rfl⟩ : syracuseStep 339545 = 254659) B254659
theorem B339659 : Blo 223812 339659 := bstep (se 1 (by rfl) ⟨254744, by rfl⟩ : syracuseStep 339659 = 509489) B509489
theorem B339671 : Blo 223812 339671 := bstep (se 1 (by rfl) ⟨254753, by rfl⟩ : syracuseStep 339671 = 509507) B509507
theorem B864017 : Blo 223812 864017 := bstep (se 2 (by rfl) ⟨324006, by rfl⟩ : syracuseStep 864017 = 648013) B648013
theorem B765719 : Blo 223812 765719 := bstep (se 1 (by rfl) ⟨574289, by rfl⟩ : syracuseStep 765719 = 1148579) B1148579
theorem B339737 : Blo 223812 339737 := bstep (se 2 (by rfl) ⟨127401, by rfl⟩ : syracuseStep 339737 = 254803) B254803
theorem B503603 : Blo 223812 503603 := bstep (se 1 (by rfl) ⟨377702, by rfl⟩ : syracuseStep 503603 = 755405) B755405
theorem B503639 : Blo 223812 503639 := bstep (se 1 (by rfl) ⟨377729, by rfl⟩ : syracuseStep 503639 = 755459) B755459
theorem B569177 : Blo 223812 569177 := bstep (se 2 (by rfl) ⟨213441, by rfl⟩ : syracuseStep 569177 = 426883) B426883
theorem B339851 : Blo 223812 339851 := bstep (se 1 (by rfl) ⟨254888, by rfl⟩ : syracuseStep 339851 = 509777) B509777
theorem B339863 : Blo 223812 339863 := bstep (se 1 (by rfl) ⟨254897, by rfl⟩ : syracuseStep 339863 = 509795) B509795
theorem B339929 : Blo 223812 339929 := bstep (se 2 (by rfl) ⟨127473, by rfl⟩ : syracuseStep 339929 = 254947) B254947
theorem B503819 : Blo 223812 503819 := bstep (se 1 (by rfl) ⟨377864, by rfl⟩ : syracuseStep 503819 = 755729) B755729
theorem B503873 : Blo 223812 503873 := bstep (se 2 (by rfl) ⟨188952, by rfl⟩ : syracuseStep 503873 = 377905) B377905
theorem B340043 : Blo 223812 340043 := bstep (se 1 (by rfl) ⟨255032, by rfl⟩ : syracuseStep 340043 = 510065) B510065
theorem B340055 : Blo 223812 340055 := bstep (se 1 (by rfl) ⟨255041, by rfl⟩ : syracuseStep 340055 = 510083) B510083
theorem B340121 : Blo 223812 340121 := bstep (se 2 (by rfl) ⟨127545, by rfl⟩ : syracuseStep 340121 = 255091) B255091
theorem B340235 : Blo 223812 340235 := bstep (se 1 (by rfl) ⟨255176, by rfl⟩ : syracuseStep 340235 = 510353) B510353
theorem B340247 : Blo 223812 340247 := bstep (se 1 (by rfl) ⟨255185, by rfl⟩ : syracuseStep 340247 = 510371) B510371
theorem B504089 : Blo 223812 504089 := bstep (se 2 (by rfl) ⟨189033, by rfl⟩ : syracuseStep 504089 = 378067) B378067
theorem B766259 : Blo 223812 766259 := bstep (se 1 (by rfl) ⟨574694, by rfl⟩ : syracuseStep 766259 = 1149389) B1149389
theorem B405847 : Blo 223812 405847 := bstep (se 1 (by rfl) ⟨304385, by rfl⟩ : syracuseStep 405847 = 608771) B608771
theorem B340313 : Blo 223812 340313 := bstep (se 2 (by rfl) ⟨127617, by rfl⟩ : syracuseStep 340313 = 255235) B255235
theorem B504179 : Blo 223812 504179 := bstep (se 1 (by rfl) ⟨378134, by rfl⟩ : syracuseStep 504179 = 756269) B756269
theorem B504215 : Blo 223812 504215 := bstep (se 1 (by rfl) ⟨378161, by rfl⟩ : syracuseStep 504215 = 756323) B756323
theorem B700823 : Blo 223812 700823 := bstep (se 1 (by rfl) ⟨525617, by rfl⟩ : syracuseStep 700823 = 1051235) B1051235
theorem B3912113 : Blo 223812 3912113 := bstep (se 2 (by rfl) ⟨1467042, by rfl⟩ : syracuseStep 3912113 = 2934085) B2934085
theorem B340427 : Blo 223812 340427 := bstep (se 1 (by rfl) ⟨255320, by rfl⟩ : syracuseStep 340427 = 510641) B510641
theorem B864715 : Blo 223812 864715 := bstep (se 1 (by rfl) ⟨648536, by rfl⟩ : syracuseStep 864715 = 1297073) B1297073
theorem B340439 : Blo 223812 340439 := bstep (se 1 (by rfl) ⟨255329, by rfl⟩ : syracuseStep 340439 = 510659) B510659
theorem B340505 : Blo 223812 340505 := bstep (se 2 (by rfl) ⟨127689, by rfl⟩ : syracuseStep 340505 = 255379) B255379
theorem B766529 : Blo 223812 766529 := bstep (se 2 (by rfl) ⟨287448, by rfl⟩ : syracuseStep 766529 = 574897) B574897
theorem B504395 : Blo 223812 504395 := bstep (se 1 (by rfl) ⟨378296, by rfl⟩ : syracuseStep 504395 = 756593) B756593
theorem B504449 : Blo 223812 504449 := bstep (se 2 (by rfl) ⟨189168, by rfl⟩ : syracuseStep 504449 = 378337) B378337
theorem B340619 : Blo 223812 340619 := bstep (se 1 (by rfl) ⟨255464, by rfl⟩ : syracuseStep 340619 = 510929) B510929
theorem B275095 : Blo 223812 275095 := bstep (se 1 (by rfl) ⟨206321, by rfl⟩ : syracuseStep 275095 = 412643) B412643
theorem B340631 : Blo 223812 340631 := bstep (se 1 (by rfl) ⟨255473, by rfl⟩ : syracuseStep 340631 = 510947) B510947
theorem B340697 : Blo 223812 340697 := bstep (se 2 (by rfl) ⟨127761, by rfl⟩ : syracuseStep 340697 = 255523) B255523
theorem B1717037 : Blo 223812 1717037 := bstep (se 3 (by rfl) ⟨321944, by rfl⟩ : syracuseStep 1717037 = 643889) B643889
theorem B340811 : Blo 223812 340811 := bstep (se 1 (by rfl) ⟨255608, by rfl⟩ : syracuseStep 340811 = 511217) B511217
theorem B504665 : Blo 223812 504665 := bstep (se 2 (by rfl) ⟨189249, by rfl⟩ : syracuseStep 504665 = 378499) B378499
theorem B340823 : Blo 223812 340823 := bstep (se 1 (by rfl) ⟨255617, by rfl⟩ : syracuseStep 340823 = 511235) B511235
theorem B340889 : Blo 223812 340889 := bstep (se 2 (by rfl) ⟨127833, by rfl⟩ : syracuseStep 340889 = 255667) B255667
theorem B504755 : Blo 223812 504755 := bstep (se 1 (by rfl) ⟨378566, by rfl⟩ : syracuseStep 504755 = 757133) B757133
theorem B406475 : Blo 223812 406475 := bstep (se 1 (by rfl) ⟨304856, by rfl⟩ : syracuseStep 406475 = 609713) B609713
theorem B504791 : Blo 223812 504791 := bstep (se 1 (by rfl) ⟨378593, by rfl⟩ : syracuseStep 504791 = 757187) B757187
theorem B341003 : Blo 223812 341003 := bstep (se 1 (by rfl) ⟨255752, by rfl⟩ : syracuseStep 341003 = 511505) B511505
theorem B341015 : Blo 223812 341015 := bstep (se 1 (by rfl) ⟨255761, by rfl⟩ : syracuseStep 341015 = 511523) B511523
theorem B341081 : Blo 223812 341081 := bstep (se 2 (by rfl) ⟨127905, by rfl⟩ : syracuseStep 341081 = 255811) B255811
theorem B767069 : Blo 223812 767069 := bstep (se 3 (by rfl) ⟨143825, by rfl⟩ : syracuseStep 767069 = 287651) B287651
theorem B504971 : Blo 223812 504971 := bstep (se 1 (by rfl) ⟨378728, by rfl⟩ : syracuseStep 504971 = 757457) B757457
theorem B505025 : Blo 223812 505025 := bstep (se 2 (by rfl) ⟨189384, by rfl⟩ : syracuseStep 505025 = 378769) B378769
theorem B341195 : Blo 223812 341195 := bstep (se 1 (by rfl) ⟨255896, by rfl⟩ : syracuseStep 341195 = 511793) B511793
theorem B341207 : Blo 223812 341207 := bstep (se 1 (by rfl) ⟨255905, by rfl⟩ : syracuseStep 341207 = 511811) B511811
theorem B341273 : Blo 223812 341273 := bstep (se 2 (by rfl) ⟨127977, by rfl⟩ : syracuseStep 341273 = 255955) B255955
theorem B341387 : Blo 223812 341387 := bstep (se 1 (by rfl) ⟨256040, by rfl⟩ : syracuseStep 341387 = 512081) B512081
theorem B341399 : Blo 223812 341399 := bstep (se 1 (by rfl) ⟨256049, by rfl⟩ : syracuseStep 341399 = 512099) B512099
theorem B505241 : Blo 223812 505241 := bstep (se 2 (by rfl) ⟨189465, by rfl⟩ : syracuseStep 505241 = 378931) B378931
theorem B406937 : Blo 223812 406937 := bstep (se 2 (by rfl) ⟨152601, by rfl⟩ : syracuseStep 406937 = 305203) B305203
theorem B1553843 : Blo 223812 1553843 := bstep (se 1 (by rfl) ⟨1165382, by rfl⟩ : syracuseStep 1553843 = 2330765) B2330765
theorem B570827 : Blo 223812 570827 := bstep (se 1 (by rfl) ⟨428120, by rfl⟩ : syracuseStep 570827 = 856241) B856241
theorem B964057 : Blo 223812 964057 := bstep (se 2 (by rfl) ⟨361521, by rfl⟩ : syracuseStep 964057 = 723043) B723043
theorem B341465 : Blo 223812 341465 := bstep (se 2 (by rfl) ⟨128049, by rfl⟩ : syracuseStep 341465 = 256099) B256099
theorem B505331 : Blo 223812 505331 := bstep (se 1 (by rfl) ⟨378998, by rfl⟩ : syracuseStep 505331 = 757997) B757997
theorem B505367 : Blo 223812 505367 := bstep (se 1 (by rfl) ⟨379025, by rfl⟩ : syracuseStep 505367 = 758051) B758051
theorem B341579 : Blo 223812 341579 := bstep (se 1 (by rfl) ⟨256184, by rfl⟩ : syracuseStep 341579 = 512369) B512369
theorem B341591 : Blo 223812 341591 := bstep (se 1 (by rfl) ⟨256193, by rfl⟩ : syracuseStep 341591 = 512387) B512387
theorem B341657 : Blo 223812 341657 := bstep (se 2 (by rfl) ⟨128121, by rfl⟩ : syracuseStep 341657 = 256243) B256243
theorem B505547 : Blo 223812 505547 := bstep (se 1 (by rfl) ⟨379160, by rfl⟩ : syracuseStep 505547 = 758321) B758321
theorem B505601 : Blo 223812 505601 := bstep (se 2 (by rfl) ⟨189600, by rfl⟩ : syracuseStep 505601 = 379201) B379201
theorem B1947493 : Blo 223812 1947493 := bstep (se 4 (by rfl) ⟨182577, by rfl⟩ : syracuseStep 1947493 = 365155) B365155
theorem B1816451 : Blo 223812 1816451 := bstep (se 1 (by rfl) ⟨1362338, by rfl⟩ : syracuseStep 1816451 = 2724677) B2724677
theorem B505817 : Blo 223812 505817 := bstep (se 2 (by rfl) ⟨189681, by rfl⟩ : syracuseStep 505817 = 379363) B379363
theorem B505907 : Blo 223812 505907 := bstep (se 1 (by rfl) ⟨379430, by rfl⟩ : syracuseStep 505907 = 758861) B758861
theorem B964673 : Blo 223812 964673 := bstep (se 2 (by rfl) ⟨361752, by rfl⟩ : syracuseStep 964673 = 723505) B723505
theorem B505943 : Blo 223812 505943 := bstep (se 1 (by rfl) ⟨379457, by rfl⟩ : syracuseStep 505943 = 758915) B758915
theorem B1292381 : Blo 223812 1292381 := bstep (se 3 (by rfl) ⟨242321, by rfl⟩ : syracuseStep 1292381 = 484643) B484643
theorem B768203 : Blo 223812 768203 := bstep (se 1 (by rfl) ⟨576152, by rfl⟩ : syracuseStep 768203 = 1152305) B1152305
theorem B506123 : Blo 223812 506123 := bstep (se 1 (by rfl) ⟨379592, by rfl⟩ : syracuseStep 506123 = 759185) B759185
theorem B506177 : Blo 223812 506177 := bstep (se 2 (by rfl) ⟨189816, by rfl⟩ : syracuseStep 506177 = 379633) B379633
theorem B571799 : Blo 223812 571799 := bstep (se 1 (by rfl) ⟨428849, by rfl⟩ : syracuseStep 571799 = 857699) B857699
theorem B244183 : Blo 223812 244183 := bstep (se 1 (by rfl) ⟨183137, by rfl⟩ : syracuseStep 244183 = 366275) B366275
theorem B768473 : Blo 223812 768473 := bstep (se 2 (by rfl) ⟨288177, by rfl⟩ : syracuseStep 768473 = 576355) B576355
theorem B7485965 : Blo 223812 7485965 := bstep (se 3 (by rfl) ⟨1403618, by rfl⟩ : syracuseStep 7485965 = 2807237) B2807237
theorem B506393 : Blo 223812 506393 := bstep (se 2 (by rfl) ⟨189897, by rfl⟩ : syracuseStep 506393 = 379795) B379795
theorem B1161773 : Blo 223812 1161773 := bstep (se 3 (by rfl) ⟨217832, by rfl⟩ : syracuseStep 1161773 = 435665) B435665
theorem B506483 : Blo 223812 506483 := bstep (se 1 (by rfl) ⟨379862, by rfl⟩ : syracuseStep 506483 = 759725) B759725
theorem B637591 : Blo 223812 637591 := bstep (se 1 (by rfl) ⟨478193, by rfl⟩ : syracuseStep 637591 = 956387) B956387
theorem B506519 : Blo 223812 506519 := bstep (se 1 (by rfl) ⟨379889, by rfl⟩ : syracuseStep 506519 = 759779) B759779
theorem B506699 : Blo 223812 506699 := bstep (se 1 (by rfl) ⟨380024, by rfl⟩ : syracuseStep 506699 = 760049) B760049
theorem B506753 : Blo 223812 506753 := bstep (se 2 (by rfl) ⟨190032, by rfl⟩ : syracuseStep 506753 = 380065) B380065
theorem B572467 : Blo 223812 572467 := bstep (se 1 (by rfl) ⟨429350, by rfl⟩ : syracuseStep 572467 = 858701) B858701
theorem B506969 : Blo 223812 506969 := bstep (se 2 (by rfl) ⟨190113, by rfl⟩ : syracuseStep 506969 = 380227) B380227
theorem B507059 : Blo 223812 507059 := bstep (se 1 (by rfl) ⟨380294, by rfl⟩ : syracuseStep 507059 = 760589) B760589
theorem B572609 : Blo 223812 572609 := bstep (se 2 (by rfl) ⟨214728, by rfl⟩ : syracuseStep 572609 = 429457) B429457
theorem B507095 : Blo 223812 507095 := bstep (se 1 (by rfl) ⟨380321, by rfl⟩ : syracuseStep 507095 = 760643) B760643
theorem B507275 : Blo 223812 507275 := bstep (se 1 (by rfl) ⟨380456, by rfl⟩ : syracuseStep 507275 = 760913) B760913
theorem B507329 : Blo 223812 507329 := bstep (se 2 (by rfl) ⟨190248, by rfl⟩ : syracuseStep 507329 = 380497) B380497
theorem B605657 : Blo 223812 605657 := bstep (se 2 (by rfl) ⟨227121, by rfl⟩ : syracuseStep 605657 = 454243) B454243
theorem B540121 : Blo 223812 540121 := bstep (se 2 (by rfl) ⟨202545, by rfl⟩ : syracuseStep 540121 = 405091) B405091
theorem B409177 : Blo 223812 409177 := bstep (se 2 (by rfl) ⟨153441, by rfl⟩ : syracuseStep 409177 = 306883) B306883
theorem B605789 : Blo 223812 605789 := bstep (se 3 (by rfl) ⟨113585, by rfl⟩ : syracuseStep 605789 = 227171) B227171
theorem B507545 : Blo 223812 507545 := bstep (se 2 (by rfl) ⟨190329, by rfl⟩ : syracuseStep 507545 = 380659) B380659
theorem B507635 : Blo 223812 507635 := bstep (se 1 (by rfl) ⟨380726, by rfl⟩ : syracuseStep 507635 = 761453) B761453
theorem B507671 : Blo 223812 507671 := bstep (se 1 (by rfl) ⟨380753, by rfl⟩ : syracuseStep 507671 = 761507) B761507
theorem B2441137 : Blo 223812 2441137 := bstep (se 2 (by rfl) ⟨915426, by rfl⟩ : syracuseStep 2441137 = 1830853) B1830853
theorem B638923 : Blo 223812 638923 := bstep (se 1 (by rfl) ⟨479192, by rfl⟩ : syracuseStep 638923 = 958385) B958385
theorem B507851 : Blo 223812 507851 := bstep (se 1 (by rfl) ⟨380888, by rfl⟩ : syracuseStep 507851 = 761777) B761777
theorem B507905 : Blo 223812 507905 := bstep (se 2 (by rfl) ⟨190464, by rfl⟩ : syracuseStep 507905 = 380929) B380929
theorem B508121 : Blo 223812 508121 := bstep (se 2 (by rfl) ⟨190545, by rfl⟩ : syracuseStep 508121 = 381091) B381091
theorem B639197 : Blo 223812 639197 := bstep (se 3 (by rfl) ⟨119849, by rfl⟩ : syracuseStep 639197 = 239699) B239699
theorem B508211 : Blo 223812 508211 := bstep (se 1 (by rfl) ⟨381158, by rfl⟩ : syracuseStep 508211 = 762317) B762317
theorem B508247 : Blo 223812 508247 := bstep (se 1 (by rfl) ⟨381185, by rfl⟩ : syracuseStep 508247 = 762371) B762371
theorem B573875 : Blo 223812 573875 := bstep (se 1 (by rfl) ⟨430406, by rfl⟩ : syracuseStep 573875 = 860813) B860813
theorem B967133 : Blo 223812 967133 := bstep (se 3 (by rfl) ⟨181337, by rfl⟩ : syracuseStep 967133 = 362675) B362675
theorem B508427 : Blo 223812 508427 := bstep (se 1 (by rfl) ⟨381320, by rfl⟩ : syracuseStep 508427 = 762641) B762641
theorem B1294865 : Blo 223812 1294865 := bstep (se 2 (by rfl) ⟨485574, by rfl⟩ : syracuseStep 1294865 = 971149) B971149
theorem B639539 : Blo 223812 639539 := bstep (se 1 (by rfl) ⟨479654, by rfl⟩ : syracuseStep 639539 = 959309) B959309
theorem B508481 : Blo 223812 508481 := bstep (se 2 (by rfl) ⟨190680, by rfl⟩ : syracuseStep 508481 = 381361) B381361
theorem B1720925 : Blo 223812 1720925 := bstep (se 3 (by rfl) ⟨322673, by rfl⟩ : syracuseStep 1720925 = 645347) B645347
theorem B508697 : Blo 223812 508697 := bstep (se 2 (by rfl) ⟨190761, by rfl⟩ : syracuseStep 508697 = 381523) B381523
theorem B541505 : Blo 223812 541505 := bstep (se 2 (by rfl) ⟨203064, by rfl⟩ : syracuseStep 541505 = 406129) B406129
theorem B377689 : Blo 223812 377689 := bstep (se 2 (by rfl) ⟨141633, by rfl⟩ : syracuseStep 377689 = 283267) B283267
theorem B508787 : Blo 223812 508787 := bstep (se 1 (by rfl) ⟨381590, by rfl⟩ : syracuseStep 508787 = 763181) B763181
theorem B508823 : Blo 223812 508823 := bstep (se 1 (by rfl) ⟨381617, by rfl⟩ : syracuseStep 508823 = 763235) B763235
theorem B574411 : Blo 223812 574411 := bstep (se 1 (by rfl) ⟨430808, by rfl⟩ : syracuseStep 574411 = 861617) B861617
theorem B509003 : Blo 223812 509003 := bstep (se 1 (by rfl) ⟨381752, by rfl⟩ : syracuseStep 509003 = 763505) B763505
theorem B574553 : Blo 223812 574553 := bstep (se 2 (by rfl) ⟨215457, by rfl⟩ : syracuseStep 574553 = 430915) B430915
theorem B509057 : Blo 223812 509057 := bstep (se 2 (by rfl) ⟨190896, by rfl⟩ : syracuseStep 509057 = 381793) B381793
theorem B2180357 : Blo 223812 2180357 := bstep (se 4 (by rfl) ⟨204408, by rfl⟩ : syracuseStep 2180357 = 408817) B408817
theorem B509273 : Blo 223812 509273 := bstep (se 2 (by rfl) ⟨190977, by rfl⟩ : syracuseStep 509273 = 381955) B381955
theorem B1230173 : Blo 223812 1230173 := bstep (se 3 (by rfl) ⟨230657, by rfl⟩ : syracuseStep 1230173 = 461315) B461315
theorem B378263 : Blo 223812 378263 := bstep (se 1 (by rfl) ⟨283697, by rfl⟩ : syracuseStep 378263 = 567395) B567395
theorem B509363 : Blo 223812 509363 := bstep (se 1 (by rfl) ⟨382022, by rfl⟩ : syracuseStep 509363 = 764045) B764045
theorem B509399 : Blo 223812 509399 := bstep (se 1 (by rfl) ⟨382049, by rfl⟩ : syracuseStep 509399 = 764099) B764099
theorem B378391 : Blo 223812 378391 := bstep (se 1 (by rfl) ⟨283793, by rfl⟩ : syracuseStep 378391 = 567587) B567587
theorem B509579 : Blo 223812 509579 := bstep (se 1 (by rfl) ⟨382184, by rfl⟩ : syracuseStep 509579 = 764369) B764369
theorem B542359 : Blo 223812 542359 := bstep (se 1 (by rfl) ⟨406769, by rfl⟩ : syracuseStep 542359 = 813539) B813539
theorem B509633 : Blo 223812 509633 := bstep (se 2 (by rfl) ⟨191112, by rfl⟩ : syracuseStep 509633 = 382225) B382225
theorem B575383 : Blo 223812 575383 := bstep (se 1 (by rfl) ⟨431537, by rfl⟩ : syracuseStep 575383 = 863075) B863075
theorem B509849 : Blo 223812 509849 := bstep (se 2 (by rfl) ⟨191193, by rfl⟩ : syracuseStep 509849 = 382387) B382387
theorem B509939 : Blo 223812 509939 := bstep (se 1 (by rfl) ⟨382454, by rfl⟩ : syracuseStep 509939 = 764909) B764909
theorem B509975 : Blo 223812 509975 := bstep (se 1 (by rfl) ⟨382481, by rfl⟩ : syracuseStep 509975 = 764963) B764963
theorem B379019 : Blo 223812 379019 := bstep (se 1 (by rfl) ⟨284264, by rfl⟩ : syracuseStep 379019 = 568529) B568529
theorem B7850135 : Blo 223812 7850135 := bstep (se 1 (by rfl) ⟨5887601, by rfl⟩ : syracuseStep 7850135 = 11775203) B11775203
theorem B510155 : Blo 223812 510155 := bstep (se 1 (by rfl) ⟨382616, by rfl⟩ : syracuseStep 510155 = 765233) B765233
theorem B510209 : Blo 223812 510209 := bstep (se 2 (by rfl) ⟨191328, by rfl⟩ : syracuseStep 510209 = 382657) B382657
theorem B379147 : Blo 223812 379147 := bstep (se 1 (by rfl) ⟨284360, by rfl⟩ : syracuseStep 379147 = 568721) B568721
theorem B575819 : Blo 223812 575819 := bstep (se 1 (by rfl) ⟨431864, by rfl⟩ : syracuseStep 575819 = 863729) B863729
theorem B379289 : Blo 223812 379289 := bstep (se 2 (by rfl) ⟨142233, by rfl⟩ : syracuseStep 379289 = 284467) B284467
theorem B510425 : Blo 223812 510425 := bstep (se 2 (by rfl) ⟨191409, by rfl⟩ : syracuseStep 510425 = 382819) B382819
theorem B379417 : Blo 223812 379417 := bstep (se 2 (by rfl) ⟨142281, by rfl⟩ : syracuseStep 379417 = 284563) B284563
theorem B510515 : Blo 223812 510515 := bstep (se 1 (by rfl) ⟨382886, by rfl⟩ : syracuseStep 510515 = 765773) B765773
theorem B641611 : Blo 223812 641611 := bstep (se 1 (by rfl) ⟨481208, by rfl⟩ : syracuseStep 641611 = 962417) B962417
theorem B510551 : Blo 223812 510551 := bstep (se 1 (by rfl) ⟨382913, by rfl⟩ : syracuseStep 510551 = 765827) B765827
theorem B1919639 : Blo 223812 1919639 := bstep (se 1 (by rfl) ⟨1439729, by rfl⟩ : syracuseStep 1919639 = 2879459) B2879459
theorem B576193 : Blo 223812 576193 := bstep (se 2 (by rfl) ⟨216072, by rfl⟩ : syracuseStep 576193 = 432145) B432145
theorem B510731 : Blo 223812 510731 := bstep (se 1 (by rfl) ⟨383048, by rfl⟩ : syracuseStep 510731 = 766097) B766097
theorem B510785 : Blo 223812 510785 := bstep (se 2 (by rfl) ⟨191544, by rfl⟩ : syracuseStep 510785 = 383089) B383089
theorem B543667 : Blo 223812 543667 := bstep (se 1 (by rfl) ⟨407750, by rfl⟩ : syracuseStep 543667 = 815501) B815501
theorem B969731 : Blo 223812 969731 := bstep (se 1 (by rfl) ⟨727298, by rfl⟩ : syracuseStep 969731 = 1454597) B1454597
theorem B478219 : Blo 223812 478219 := bstep (se 1 (by rfl) ⟨358664, by rfl⟩ : syracuseStep 478219 = 717329) B717329
theorem B511001 : Blo 223812 511001 := bstep (se 2 (by rfl) ⟨191625, by rfl⟩ : syracuseStep 511001 = 383251) B383251
theorem B642113 : Blo 223812 642113 := bstep (se 2 (by rfl) ⟨240792, by rfl⟩ : syracuseStep 642113 = 481585) B481585
theorem B379991 : Blo 223812 379991 := bstep (se 1 (by rfl) ⟨284993, by rfl⟩ : syracuseStep 379991 = 569987) B569987
theorem B511091 : Blo 223812 511091 := bstep (se 1 (by rfl) ⟨383318, by rfl⟩ : syracuseStep 511091 = 766637) B766637
theorem B511127 : Blo 223812 511127 := bstep (se 1 (by rfl) ⟨383345, by rfl⟩ : syracuseStep 511127 = 766691) B766691
theorem B1133747 : Blo 223812 1133747 := bstep (se 1 (by rfl) ⟨850310, by rfl⟩ : syracuseStep 1133747 = 1700621) B1700621
theorem B3853493 : Blo 223812 3853493 := bstep (se 5 (by rfl) ⟨180632, by rfl⟩ : syracuseStep 3853493 = 361265) B361265
theorem B380119 : Blo 223812 380119 := bstep (se 1 (by rfl) ⟨285089, by rfl⟩ : syracuseStep 380119 = 570179) B570179
theorem B478475 : Blo 223812 478475 := bstep (se 1 (by rfl) ⟨358856, by rfl⟩ : syracuseStep 478475 = 717713) B717713
theorem B511307 : Blo 223812 511307 := bstep (se 1 (by rfl) ⟨383480, by rfl⟩ : syracuseStep 511307 = 766961) B766961
theorem B511361 : Blo 223812 511361 := bstep (se 2 (by rfl) ⟨191760, by rfl⟩ : syracuseStep 511361 = 383521) B383521
theorem B642455 : Blo 223812 642455 := bstep (se 1 (by rfl) ⟨481841, by rfl⟩ : syracuseStep 642455 = 963683) B963683
theorem B3919373 : Blo 223812 3919373 := bstep (se 3 (by rfl) ⟨734882, by rfl⟩ : syracuseStep 3919373 = 1469765) B1469765
theorem B2870801 : Blo 223812 2870801 := bstep (se 2 (by rfl) ⟨1076550, by rfl⟩ : syracuseStep 2870801 = 2153101) B2153101
theorem B511577 : Blo 223812 511577 := bstep (se 2 (by rfl) ⟨191841, by rfl⟩ : syracuseStep 511577 = 383683) B383683
theorem B511667 : Blo 223812 511667 := bstep (se 1 (by rfl) ⟨383750, by rfl⟩ : syracuseStep 511667 = 767501) B767501
theorem B511703 : Blo 223812 511703 := bstep (se 1 (by rfl) ⟨383777, by rfl⟩ : syracuseStep 511703 = 767555) B767555
theorem B380747 : Blo 223812 380747 := bstep (se 1 (by rfl) ⟨285560, by rfl⟩ : syracuseStep 380747 = 571121) B571121
theorem B511883 : Blo 223812 511883 := bstep (se 1 (by rfl) ⟨383912, by rfl⟩ : syracuseStep 511883 = 767825) B767825
theorem B511937 : Blo 223812 511937 := bstep (se 2 (by rfl) ⟨191976, by rfl⟩ : syracuseStep 511937 = 383953) B383953
theorem B380875 : Blo 223812 380875 := bstep (se 1 (by rfl) ⟨285656, by rfl⟩ : syracuseStep 380875 = 571313) B571313
theorem B610327 : Blo 223812 610327 := bstep (se 1 (by rfl) ⟨457745, by rfl⟩ : syracuseStep 610327 = 915491) B915491
theorem B381017 : Blo 223812 381017 := bstep (se 2 (by rfl) ⟨142881, by rfl⟩ : syracuseStep 381017 = 285763) B285763
theorem B512153 : Blo 223812 512153 := bstep (se 2 (by rfl) ⟨192057, by rfl⟩ : syracuseStep 512153 = 384115) B384115
theorem B1134809 : Blo 223812 1134809 := bstep (se 2 (by rfl) ⟨425553, by rfl⟩ : syracuseStep 1134809 = 851107) B851107
theorem B479449 : Blo 223812 479449 := bstep (se 2 (by rfl) ⟨179793, by rfl⟩ : syracuseStep 479449 = 359587) B359587
theorem B381145 : Blo 223812 381145 := bstep (se 2 (by rfl) ⟨142929, by rfl⟩ : syracuseStep 381145 = 285859) B285859
theorem B512243 : Blo 223812 512243 := bstep (se 1 (by rfl) ⟨384182, by rfl⟩ : syracuseStep 512243 = 768365) B768365
theorem B512279 : Blo 223812 512279 := bstep (se 1 (by rfl) ⟨384209, by rfl⟩ : syracuseStep 512279 = 768419) B768419
theorem B479603 : Blo 223812 479603 := bstep (se 1 (by rfl) ⟨359702, by rfl⟩ : syracuseStep 479603 = 719405) B719405
theorem B512459 : Blo 223812 512459 := bstep (se 1 (by rfl) ⟨384344, by rfl⟩ : syracuseStep 512459 = 768689) B768689
theorem B512513 : Blo 223812 512513 := bstep (se 2 (by rfl) ⟨192192, by rfl⟩ : syracuseStep 512513 = 384385) B384385
theorem B1921553 : Blo 223812 1921553 := bstep (se 2 (by rfl) ⟨720582, by rfl⟩ : syracuseStep 1921553 = 1441165) B1441165
theorem B381719 : Blo 223812 381719 := bstep (se 1 (by rfl) ⟨286289, by rfl⟩ : syracuseStep 381719 = 572579) B572579
theorem B480115 : Blo 223812 480115 := bstep (se 1 (by rfl) ⟨360086, by rfl⟩ : syracuseStep 480115 = 720173) B720173
theorem B381847 : Blo 223812 381847 := bstep (se 1 (by rfl) ⟨286385, by rfl⟩ : syracuseStep 381847 = 572771) B572771
theorem B283915 : Blo 223812 283915 := bstep (se 1 (by rfl) ⟨212936, by rfl⟩ : syracuseStep 283915 = 425873) B425873
theorem B972107 : Blo 223812 972107 := bstep (se 1 (by rfl) ⟨729080, by rfl⟩ : syracuseStep 972107 = 1458161) B1458161
theorem B3888485 : Blo 223812 3888485 := bstep (se 4 (by rfl) ⟨364545, by rfl⟩ : syracuseStep 3888485 = 729091) B729091
theorem B644573 : Blo 223812 644573 := bstep (se 3 (by rfl) ⟨120857, by rfl⟩ : syracuseStep 644573 = 241715) B241715
theorem B382475 : Blo 223812 382475 := bstep (se 1 (by rfl) ⟨286856, by rfl⟩ : syracuseStep 382475 = 573713) B573713
theorem B480791 : Blo 223812 480791 := bstep (se 1 (by rfl) ⟨360593, by rfl⟩ : syracuseStep 480791 = 721187) B721187
theorem B480833 : Blo 223812 480833 := bstep (se 2 (by rfl) ⟨180312, by rfl⟩ : syracuseStep 480833 = 360625) B360625
theorem B382603 : Blo 223812 382603 := bstep (se 1 (by rfl) ⟨286952, by rfl⟩ : syracuseStep 382603 = 573905) B573905
theorem B382745 : Blo 223812 382745 := bstep (se 2 (by rfl) ⟨143529, by rfl⟩ : syracuseStep 382745 = 287059) B287059
theorem B1136429 : Blo 223812 1136429 := bstep (se 3 (by rfl) ⟨213080, by rfl⟩ : syracuseStep 1136429 = 426161) B426161
theorem B644915 : Blo 223812 644915 := bstep (se 1 (by rfl) ⟨483686, by rfl⟩ : syracuseStep 644915 = 967373) B967373
theorem B382873 : Blo 223812 382873 := bstep (se 2 (by rfl) ⟨143577, by rfl⟩ : syracuseStep 382873 = 287155) B287155
theorem B251851 : Blo 223812 251851 := bstep (se 1 (by rfl) ⟨188888, by rfl⟩ : syracuseStep 251851 = 377777) B377777
theorem B251959 : Blo 223812 251959 := bstep (se 1 (by rfl) ⟨188969, by rfl⟩ : syracuseStep 251959 = 377939) B377939
theorem B284887 : Blo 223812 284887 := bstep (se 1 (by rfl) ⟨213665, by rfl⟩ : syracuseStep 284887 = 427331) B427331
theorem B252139 : Blo 223812 252139 := bstep (se 1 (by rfl) ⟨189104, by rfl⟩ : syracuseStep 252139 = 378209) B378209
theorem B973079 : Blo 223812 973079 := bstep (se 1 (by rfl) ⟨729809, by rfl⟩ : syracuseStep 973079 = 1459619) B1459619
theorem B1628461 : Blo 223812 1628461 := bstep (se 3 (by rfl) ⟨305336, by rfl⟩ : syracuseStep 1628461 = 610673) B610673
theorem B252247 : Blo 223812 252247 := bstep (se 1 (by rfl) ⟨189185, by rfl⟩ : syracuseStep 252247 = 378371) B378371
theorem B579991 : Blo 223812 579991 := bstep (se 1 (by rfl) ⟨434993, by rfl⟩ : syracuseStep 579991 = 869987) B869987
theorem B383447 : Blo 223812 383447 := bstep (se 1 (by rfl) ⟨287585, by rfl⟩ : syracuseStep 383447 = 575171) B575171
theorem B252427 : Blo 223812 252427 := bstep (se 1 (by rfl) ⟨189320, by rfl⟩ : syracuseStep 252427 = 378641) B378641
theorem B383575 : Blo 223812 383575 := bstep (se 1 (by rfl) ⟨287681, by rfl⟩ : syracuseStep 383575 = 575363) B575363
theorem B252535 : Blo 223812 252535 := bstep (se 1 (by rfl) ⟨189401, by rfl⟩ : syracuseStep 252535 = 378803) B378803
theorem B252715 : Blo 223812 252715 := bstep (se 1 (by rfl) ⟨189536, by rfl⟩ : syracuseStep 252715 = 379073) B379073
theorem B5561189 : Blo 223812 5561189 := bstep (se 4 (by rfl) ⟨521361, by rfl⟩ : syracuseStep 5561189 = 1042723) B1042723
theorem B252823 : Blo 223812 252823 := bstep (se 1 (by rfl) ⟨189617, by rfl⟩ : syracuseStep 252823 = 379235) B379235
theorem B1727411 : Blo 223812 1727411 := bstep (se 1 (by rfl) ⟨1295558, by rfl⟩ : syracuseStep 1727411 = 2591117) B2591117
theorem B285707 : Blo 223812 285707 := bstep (se 1 (by rfl) ⟨214280, by rfl⟩ : syracuseStep 285707 = 428561) B428561
theorem B613441 : Blo 223812 613441 := bstep (se 2 (by rfl) ⟨230040, by rfl⟩ : syracuseStep 613441 = 460081) B460081
theorem B253003 : Blo 223812 253003 := bstep (se 1 (by rfl) ⟨189752, by rfl⟩ : syracuseStep 253003 = 379505) B379505
theorem B253111 : Blo 223812 253111 := bstep (se 1 (by rfl) ⟨189833, by rfl⟩ : syracuseStep 253111 = 379667) B379667
theorem B384203 : Blo 223812 384203 := bstep (se 1 (by rfl) ⟨288152, by rfl⟩ : syracuseStep 384203 = 576305) B576305
theorem B384331 : Blo 223812 384331 := bstep (se 1 (by rfl) ⟨288248, by rfl⟩ : syracuseStep 384331 = 576497) B576497
theorem B253291 : Blo 223812 253291 := bstep (se 1 (by rfl) ⟨189968, by rfl⟩ : syracuseStep 253291 = 379937) B379937
theorem B548299 : Blo 223812 548299 := bstep (se 1 (by rfl) ⟨411224, by rfl⟩ : syracuseStep 548299 = 822449) B822449
theorem B253399 : Blo 223812 253399 := bstep (se 1 (by rfl) ⟨190049, by rfl⟩ : syracuseStep 253399 = 380099) B380099
theorem B2154059 : Blo 223812 2154059 := bstep (se 1 (by rfl) ⟨1615544, by rfl⟩ : syracuseStep 2154059 = 3231089) B3231089
theorem B253579 : Blo 223812 253579 := bstep (se 1 (by rfl) ⟨190184, by rfl⟩ : syracuseStep 253579 = 380369) B380369
theorem B286411 : Blo 223812 286411 := bstep (se 1 (by rfl) ⟨214808, by rfl⟩ : syracuseStep 286411 = 429617) B429617
theorem B253687 : Blo 223812 253687 := bstep (se 1 (by rfl) ⟨190265, by rfl⟩ : syracuseStep 253687 = 380531) B380531
theorem B253867 : Blo 223812 253867 := bstep (se 1 (by rfl) ⟨190400, by rfl⟩ : syracuseStep 253867 = 380801) B380801
theorem B286679 : Blo 223812 286679 := bstep (se 1 (by rfl) ⟨215009, by rfl⟩ : syracuseStep 286679 = 430019) B430019
theorem B253975 : Blo 223812 253975 := bstep (se 1 (by rfl) ⟨190481, by rfl⟩ : syracuseStep 253975 = 380963) B380963
theorem B1531979 : Blo 223812 1531979 := bstep (se 1 (by rfl) ⟨1148984, by rfl⟩ : syracuseStep 1531979 = 2297969) B2297969
theorem B647261 : Blo 223812 647261 := bstep (se 3 (by rfl) ⟨121361, by rfl⟩ : syracuseStep 647261 = 242723) B242723
theorem B876637 : Blo 223812 876637 := bstep (se 3 (by rfl) ⟨164369, by rfl⟩ : syracuseStep 876637 = 328739) B328739
theorem B254155 : Blo 223812 254155 := bstep (se 1 (by rfl) ⟨190616, by rfl⟩ : syracuseStep 254155 = 381233) B381233
theorem B93184277 : Blo 223812 93184277 := bstep (se 6 (by rfl) ⟨2184006, by rfl⟩ : syracuseStep 93184277 = 4368013) B4368013
theorem B254263 : Blo 223812 254263 := bstep (se 1 (by rfl) ⟨190697, by rfl⟩ : syracuseStep 254263 = 381395) B381395
theorem B647489 : Blo 223812 647489 := bstep (se 2 (by rfl) ⟨242808, by rfl⟩ : syracuseStep 647489 = 485617) B485617
theorem B483737 : Blo 223812 483737 := bstep (se 2 (by rfl) ⟨181401, by rfl⟩ : syracuseStep 483737 = 362803) B362803
theorem B778675 : Blo 223812 778675 := bstep (se 1 (by rfl) ⟨584006, by rfl⟩ : syracuseStep 778675 = 1168013) B1168013
theorem B254443 : Blo 223812 254443 := bstep (se 1 (by rfl) ⟨190832, by rfl⟩ : syracuseStep 254443 = 381665) B381665
theorem B6545933 : Blo 223812 6545933 := bstep (se 3 (by rfl) ⟨1227362, by rfl⟩ : syracuseStep 6545933 = 2454725) B2454725
theorem B909899 : Blo 223812 909899 := bstep (se 1 (by rfl) ⟨682424, by rfl⟩ : syracuseStep 909899 = 1364849) B1364849
theorem B254551 : Blo 223812 254551 := bstep (se 1 (by rfl) ⟨190913, by rfl⟩ : syracuseStep 254551 = 381827) B381827
theorem B287383 : Blo 223812 287383 := bstep (se 1 (by rfl) ⟨215537, by rfl⟩ : syracuseStep 287383 = 431075) B431075
theorem B647831 : Blo 223812 647831 := bstep (se 1 (by rfl) ⟨485873, by rfl⟩ : syracuseStep 647831 = 971747) B971747
theorem B254731 : Blo 223812 254731 := bstep (se 1 (by rfl) ⟨191048, by rfl⟩ : syracuseStep 254731 = 382097) B382097
theorem B484147 : Blo 223812 484147 := bstep (se 1 (by rfl) ⟨363110, by rfl⟩ : syracuseStep 484147 = 726221) B726221
theorem B254839 : Blo 223812 254839 := bstep (se 1 (by rfl) ⟨191129, by rfl⟩ : syracuseStep 254839 = 382259) B382259
theorem B255019 : Blo 223812 255019 := bstep (se 1 (by rfl) ⟨191264, by rfl⟩ : syracuseStep 255019 = 382529) B382529
theorem B287831 : Blo 223812 287831 := bstep (se 1 (by rfl) ⟨215873, by rfl⟩ : syracuseStep 287831 = 431747) B431747
theorem B484481 : Blo 223812 484481 := bstep (se 2 (by rfl) ⟨181680, by rfl⟩ : syracuseStep 484481 = 363361) B363361
theorem B255127 : Blo 223812 255127 := bstep (se 1 (by rfl) ⟨191345, by rfl⟩ : syracuseStep 255127 = 382691) B382691
theorem B2057489 : Blo 223812 2057489 := bstep (se 2 (by rfl) ⟨771558, by rfl⟩ : syracuseStep 2057489 = 1543117) B1543117
theorem B255307 : Blo 223812 255307 := bstep (se 1 (by rfl) ⟨191480, by rfl⟩ : syracuseStep 255307 = 382961) B382961
theorem B255415 : Blo 223812 255415 := bstep (se 1 (by rfl) ⟨191561, by rfl⟩ : syracuseStep 255415 = 383123) B383123
theorem B1730123 : Blo 223812 1730123 := bstep (se 1 (by rfl) ⟨1297592, by rfl⟩ : syracuseStep 1730123 = 2595185) B2595185
theorem B1140317 : Blo 223812 1140317 := bstep (se 3 (by rfl) ⟨213809, by rfl⟩ : syracuseStep 1140317 = 427619) B427619
theorem B255595 : Blo 223812 255595 := bstep (se 1 (by rfl) ⟨191696, by rfl⟩ : syracuseStep 255595 = 383393) B383393
theorem B255703 : Blo 223812 255703 := bstep (se 1 (by rfl) ⟨191777, by rfl⟩ : syracuseStep 255703 = 383555) B383555
theorem B255767 : Blo 223812 255767 := bstep (se 1 (by rfl) ⟨191825, by rfl⟩ : syracuseStep 255767 = 383651) B383651
theorem B386839 : Blo 223812 386839 := bstep (se 1 (by rfl) ⟨290129, by rfl⟩ : syracuseStep 386839 = 580259) B580259
theorem B485207 : Blo 223812 485207 := bstep (se 1 (by rfl) ⟨363905, by rfl⟩ : syracuseStep 485207 = 727811) B727811
theorem B255883 : Blo 223812 255883 := bstep (se 1 (by rfl) ⟨191912, by rfl⟩ : syracuseStep 255883 = 383825) B383825
theorem B1107863 : Blo 223812 1107863 := bstep (se 1 (by rfl) ⟨830897, by rfl⟩ : syracuseStep 1107863 = 1661795) B1661795
theorem B255991 : Blo 223812 255991 := bstep (se 1 (by rfl) ⟨191993, by rfl⟩ : syracuseStep 255991 = 383987) B383987
theorem B256171 : Blo 223812 256171 := bstep (se 1 (by rfl) ⟨192128, by rfl⟩ : syracuseStep 256171 = 384257) B384257
theorem B256279 : Blo 223812 256279 := bstep (se 1 (by rfl) ⟨192209, by rfl⟩ : syracuseStep 256279 = 384419) B384419
theorem B2779609 : Blo 223812 2779609 := bstep (se 2 (by rfl) ⟨1042353, by rfl⟩ : syracuseStep 2779609 = 2084707) B2084707
theorem B223819 : Blo 223812 223819 := bstep (se 1 (by rfl) ⟨167864, by rfl⟩ : syracuseStep 223819 = 335729) B335729
theorem B223831 : Blo 223812 223831 := bstep (se 1 (by rfl) ⟨167873, by rfl⟩ : syracuseStep 223831 = 335747) B335747
theorem B223851 : Blo 223812 223851 := bstep (se 1 (by rfl) ⟨167888, by rfl⟩ : syracuseStep 223851 = 335777) B335777
theorem B223863 : Blo 223812 223863 := bstep (se 1 (by rfl) ⟨167897, by rfl⟩ : syracuseStep 223863 = 335795) B335795
theorem B223883 : Blo 223812 223883 := bstep (se 1 (by rfl) ⟨167912, by rfl⟩ : syracuseStep 223883 = 335825) B335825
theorem B223895 : Blo 223812 223895 := bstep (se 1 (by rfl) ⟨167921, by rfl⟩ : syracuseStep 223895 = 335843) B335843
theorem B223915 : Blo 223812 223915 := bstep (se 1 (by rfl) ⟨167936, by rfl⟩ : syracuseStep 223915 = 335873) B335873
theorem B223927 : Blo 223812 223927 := bstep (se 1 (by rfl) ⟨167945, by rfl⟩ : syracuseStep 223927 = 335891) B335891
theorem B223947 : Blo 223812 223947 := bstep (se 1 (by rfl) ⟨167960, by rfl⟩ : syracuseStep 223947 = 335921) B335921
theorem B223959 : Blo 223812 223959 := bstep (se 1 (by rfl) ⟨167969, by rfl⟩ : syracuseStep 223959 = 335939) B335939
theorem B223979 : Blo 223812 223979 := bstep (se 1 (by rfl) ⟨167984, by rfl⟩ : syracuseStep 223979 = 335969) B335969
theorem B223991 : Blo 223812 223991 := bstep (se 1 (by rfl) ⟨167993, by rfl⟩ : syracuseStep 223991 = 335987) B335987
theorem B224011 : Blo 223812 224011 := bstep (se 1 (by rfl) ⟨168008, by rfl⟩ : syracuseStep 224011 = 336017) B336017
theorem B224023 : Blo 223812 224023 := bstep (se 1 (by rfl) ⟨168017, by rfl⟩ : syracuseStep 224023 = 336035) B336035
theorem B224043 : Blo 223812 224043 := bstep (se 1 (by rfl) ⟨168032, by rfl⟩ : syracuseStep 224043 = 336065) B336065
theorem B224055 : Blo 223812 224055 := bstep (se 1 (by rfl) ⟨168041, by rfl⟩ : syracuseStep 224055 = 336083) B336083
theorem B224075 : Blo 223812 224075 := bstep (se 1 (by rfl) ⟨168056, by rfl⟩ : syracuseStep 224075 = 336113) B336113
theorem B224087 : Blo 223812 224087 := bstep (se 1 (by rfl) ⟨168065, by rfl⟩ : syracuseStep 224087 = 336131) B336131
theorem B224107 : Blo 223812 224107 := bstep (se 1 (by rfl) ⟨168080, by rfl⟩ : syracuseStep 224107 = 336161) B336161
theorem B224119 : Blo 223812 224119 := bstep (se 1 (by rfl) ⟨168089, by rfl⟩ : syracuseStep 224119 = 336179) B336179
theorem B224139 : Blo 223812 224139 := bstep (se 1 (by rfl) ⟨168104, by rfl⟩ : syracuseStep 224139 = 336209) B336209
theorem B224151 : Blo 223812 224151 := bstep (se 1 (by rfl) ⟨168113, by rfl⟩ : syracuseStep 224151 = 336227) B336227
theorem B224171 : Blo 223812 224171 := bstep (se 1 (by rfl) ⟨168128, by rfl⟩ : syracuseStep 224171 = 336257) B336257
theorem B224183 : Blo 223812 224183 := bstep (se 1 (by rfl) ⟨168137, by rfl⟩ : syracuseStep 224183 = 336275) B336275
theorem B224203 : Blo 223812 224203 := bstep (se 1 (by rfl) ⟨168152, by rfl⟩ : syracuseStep 224203 = 336305) B336305
theorem B224215 : Blo 223812 224215 := bstep (se 1 (by rfl) ⟨168161, by rfl⟩ : syracuseStep 224215 = 336323) B336323
theorem B224235 : Blo 223812 224235 := bstep (se 1 (by rfl) ⟨168176, by rfl⟩ : syracuseStep 224235 = 336353) B336353
theorem B224247 : Blo 223812 224247 := bstep (se 1 (by rfl) ⟨168185, by rfl⟩ : syracuseStep 224247 = 336371) B336371
theorem B224267 : Blo 223812 224267 := bstep (se 1 (by rfl) ⟨168200, by rfl⟩ : syracuseStep 224267 = 336401) B336401
theorem B224279 : Blo 223812 224279 := bstep (se 1 (by rfl) ⟨168209, by rfl⟩ : syracuseStep 224279 = 336419) B336419
theorem B224299 : Blo 223812 224299 := bstep (se 1 (by rfl) ⟨168224, by rfl⟩ : syracuseStep 224299 = 336449) B336449
theorem B224311 : Blo 223812 224311 := bstep (se 1 (by rfl) ⟨168233, by rfl⟩ : syracuseStep 224311 = 336467) B336467
theorem B224331 : Blo 223812 224331 := bstep (se 1 (by rfl) ⟨168248, by rfl⟩ : syracuseStep 224331 = 336497) B336497
theorem B224343 : Blo 223812 224343 := bstep (se 1 (by rfl) ⟨168257, by rfl⟩ : syracuseStep 224343 = 336515) B336515
theorem B224363 : Blo 223812 224363 := bstep (se 1 (by rfl) ⟨168272, by rfl⟩ : syracuseStep 224363 = 336545) B336545
theorem B224375 : Blo 223812 224375 := bstep (se 1 (by rfl) ⟨168281, by rfl⟩ : syracuseStep 224375 = 336563) B336563
theorem B224395 : Blo 223812 224395 := bstep (se 1 (by rfl) ⟨168296, by rfl⟩ : syracuseStep 224395 = 336593) B336593
theorem B224407 : Blo 223812 224407 := bstep (se 1 (by rfl) ⟨168305, by rfl⟩ : syracuseStep 224407 = 336611) B336611
theorem B224427 : Blo 223812 224427 := bstep (se 1 (by rfl) ⟨168320, by rfl⟩ : syracuseStep 224427 = 336641) B336641
theorem B224439 : Blo 223812 224439 := bstep (se 1 (by rfl) ⟨168329, by rfl⟩ : syracuseStep 224439 = 336659) B336659
theorem B224459 : Blo 223812 224459 := bstep (se 1 (by rfl) ⟨168344, by rfl⟩ : syracuseStep 224459 = 336689) B336689
theorem B224471 : Blo 223812 224471 := bstep (se 1 (by rfl) ⟨168353, by rfl⟩ : syracuseStep 224471 = 336707) B336707
theorem B224491 : Blo 223812 224491 := bstep (se 1 (by rfl) ⟨168368, by rfl⟩ : syracuseStep 224491 = 336737) B336737
theorem B224503 : Blo 223812 224503 := bstep (se 1 (by rfl) ⟨168377, by rfl⟩ : syracuseStep 224503 = 336755) B336755
theorem B224523 : Blo 223812 224523 := bstep (se 1 (by rfl) ⟨168392, by rfl⟩ : syracuseStep 224523 = 336785) B336785
theorem B224535 : Blo 223812 224535 := bstep (se 1 (by rfl) ⟨168401, by rfl⟩ : syracuseStep 224535 = 336803) B336803
theorem B224555 : Blo 223812 224555 := bstep (se 1 (by rfl) ⟨168416, by rfl⟩ : syracuseStep 224555 = 336833) B336833
theorem B224567 : Blo 223812 224567 := bstep (se 1 (by rfl) ⟨168425, by rfl⟩ : syracuseStep 224567 = 336851) B336851
theorem B224587 : Blo 223812 224587 := bstep (se 1 (by rfl) ⟨168440, by rfl⟩ : syracuseStep 224587 = 336881) B336881
theorem B224599 : Blo 223812 224599 := bstep (se 1 (by rfl) ⟨168449, by rfl⟩ : syracuseStep 224599 = 336899) B336899
theorem B224619 : Blo 223812 224619 := bstep (se 1 (by rfl) ⟨168464, by rfl⟩ : syracuseStep 224619 = 336929) B336929
theorem B224631 : Blo 223812 224631 := bstep (se 1 (by rfl) ⟨168473, by rfl⟩ : syracuseStep 224631 = 336947) B336947
theorem B224651 : Blo 223812 224651 := bstep (se 1 (by rfl) ⟨168488, by rfl⟩ : syracuseStep 224651 = 336977) B336977
theorem B224663 : Blo 223812 224663 := bstep (se 1 (by rfl) ⟨168497, by rfl⟩ : syracuseStep 224663 = 336995) B336995
theorem B224683 : Blo 223812 224683 := bstep (se 1 (by rfl) ⟨168512, by rfl⟩ : syracuseStep 224683 = 337025) B337025
theorem B224695 : Blo 223812 224695 := bstep (se 1 (by rfl) ⟨168521, by rfl⟩ : syracuseStep 224695 = 337043) B337043
theorem B454081 : Blo 223812 454081 := bstep (se 2 (by rfl) ⟨170280, by rfl⟩ : syracuseStep 454081 = 340561) B340561
theorem B224715 : Blo 223812 224715 := bstep (se 1 (by rfl) ⟨168536, by rfl⟩ : syracuseStep 224715 = 337073) B337073
theorem B224727 : Blo 223812 224727 := bstep (se 1 (by rfl) ⟨168545, by rfl⟩ : syracuseStep 224727 = 337091) B337091
theorem B224747 : Blo 223812 224747 := bstep (se 1 (by rfl) ⟨168560, by rfl⟩ : syracuseStep 224747 = 337121) B337121
theorem B224759 : Blo 223812 224759 := bstep (se 1 (by rfl) ⟨168569, by rfl⟩ : syracuseStep 224759 = 337139) B337139
theorem B224779 : Blo 223812 224779 := bstep (se 1 (by rfl) ⟨168584, by rfl⟩ : syracuseStep 224779 = 337169) B337169
theorem B224791 : Blo 223812 224791 := bstep (se 1 (by rfl) ⟨168593, by rfl⟩ : syracuseStep 224791 = 337187) B337187
theorem B224811 : Blo 223812 224811 := bstep (se 1 (by rfl) ⟨168608, by rfl⟩ : syracuseStep 224811 = 337217) B337217
theorem B224823 : Blo 223812 224823 := bstep (se 1 (by rfl) ⟨168617, by rfl⟩ : syracuseStep 224823 = 337235) B337235
theorem B224843 : Blo 223812 224843 := bstep (se 1 (by rfl) ⟨168632, by rfl⟩ : syracuseStep 224843 = 337265) B337265
theorem B224855 : Blo 223812 224855 := bstep (se 1 (by rfl) ⟨168641, by rfl⟩ : syracuseStep 224855 = 337283) B337283
theorem B224875 : Blo 223812 224875 := bstep (se 1 (by rfl) ⟨168656, by rfl⟩ : syracuseStep 224875 = 337313) B337313
theorem B224887 : Blo 223812 224887 := bstep (se 1 (by rfl) ⟨168665, by rfl⟩ : syracuseStep 224887 = 337331) B337331
theorem B913027 : Blo 223812 913027 := bstep (se 1 (by rfl) ⟨684770, by rfl⟩ : syracuseStep 913027 = 1369541) B1369541
theorem B224907 : Blo 223812 224907 := bstep (se 1 (by rfl) ⟨168680, by rfl⟩ : syracuseStep 224907 = 337361) B337361
theorem B224919 : Blo 223812 224919 := bstep (se 1 (by rfl) ⟨168689, by rfl⟩ : syracuseStep 224919 = 337379) B337379
theorem B1142423 : Blo 223812 1142423 := bstep (se 1 (by rfl) ⟨856817, by rfl⟩ : syracuseStep 1142423 = 1713635) B1713635
theorem B224939 : Blo 223812 224939 := bstep (se 1 (by rfl) ⟨168704, by rfl⟩ : syracuseStep 224939 = 337409) B337409
theorem B1076915 : Blo 223812 1076915 := bstep (se 1 (by rfl) ⟨807686, by rfl⟩ : syracuseStep 1076915 = 1615373) B1615373
theorem B224951 : Blo 223812 224951 := bstep (se 1 (by rfl) ⟨168713, by rfl⟩ : syracuseStep 224951 = 337427) B337427
theorem B224971 : Blo 223812 224971 := bstep (se 1 (by rfl) ⟨168728, by rfl⟩ : syracuseStep 224971 = 337457) B337457
theorem B224983 : Blo 223812 224983 := bstep (se 1 (by rfl) ⟨168737, by rfl⟩ : syracuseStep 224983 = 337475) B337475
theorem B225003 : Blo 223812 225003 := bstep (se 1 (by rfl) ⟨168752, by rfl⟩ : syracuseStep 225003 = 337505) B337505
theorem B225015 : Blo 223812 225015 := bstep (se 1 (by rfl) ⟨168761, by rfl⟩ : syracuseStep 225015 = 337523) B337523
theorem B225035 : Blo 223812 225035 := bstep (se 1 (by rfl) ⟨168776, by rfl⟩ : syracuseStep 225035 = 337553) B337553
theorem B225047 : Blo 223812 225047 := bstep (se 1 (by rfl) ⟨168785, by rfl⟩ : syracuseStep 225047 = 337571) B337571
theorem B225067 : Blo 223812 225067 := bstep (se 1 (by rfl) ⟨168800, by rfl⟩ : syracuseStep 225067 = 337601) B337601
theorem B225079 : Blo 223812 225079 := bstep (se 1 (by rfl) ⟨168809, by rfl⟩ : syracuseStep 225079 = 337619) B337619
theorem B225099 : Blo 223812 225099 := bstep (se 1 (by rfl) ⟨168824, by rfl⟩ : syracuseStep 225099 = 337649) B337649
theorem B225111 : Blo 223812 225111 := bstep (se 1 (by rfl) ⟨168833, by rfl⟩ : syracuseStep 225111 = 337667) B337667
theorem B225131 : Blo 223812 225131 := bstep (se 1 (by rfl) ⟨168848, by rfl⟩ : syracuseStep 225131 = 337697) B337697
theorem B225143 : Blo 223812 225143 := bstep (se 1 (by rfl) ⟨168857, by rfl⟩ : syracuseStep 225143 = 337715) B337715
theorem B225163 : Blo 223812 225163 := bstep (se 1 (by rfl) ⟨168872, by rfl⟩ : syracuseStep 225163 = 337745) B337745
theorem B225175 : Blo 223812 225175 := bstep (se 1 (by rfl) ⟨168881, by rfl⟩ : syracuseStep 225175 = 337763) B337763
theorem B225195 : Blo 223812 225195 := bstep (se 1 (by rfl) ⟨168896, by rfl⟩ : syracuseStep 225195 = 337793) B337793
theorem B225207 : Blo 223812 225207 := bstep (se 1 (by rfl) ⟨168905, by rfl⟩ : syracuseStep 225207 = 337811) B337811
theorem B225227 : Blo 223812 225227 := bstep (se 1 (by rfl) ⟨168920, by rfl⟩ : syracuseStep 225227 = 337841) B337841
theorem B225239 : Blo 223812 225239 := bstep (se 1 (by rfl) ⟨168929, by rfl⟩ : syracuseStep 225239 = 337859) B337859
theorem B225259 : Blo 223812 225259 := bstep (se 1 (by rfl) ⟨168944, by rfl⟩ : syracuseStep 225259 = 337889) B337889
theorem B225271 : Blo 223812 225271 := bstep (se 1 (by rfl) ⟨168953, by rfl⟩ : syracuseStep 225271 = 337907) B337907
theorem B225291 : Blo 223812 225291 := bstep (se 1 (by rfl) ⟨168968, by rfl⟩ : syracuseStep 225291 = 337937) B337937
theorem B225303 : Blo 223812 225303 := bstep (se 1 (by rfl) ⟨168977, by rfl⟩ : syracuseStep 225303 = 337955) B337955
theorem B225323 : Blo 223812 225323 := bstep (se 1 (by rfl) ⟨168992, by rfl⟩ : syracuseStep 225323 = 337985) B337985
theorem B225335 : Blo 223812 225335 := bstep (se 1 (by rfl) ⟨169001, by rfl⟩ : syracuseStep 225335 = 338003) B338003
theorem B258103 : Blo 223812 258103 := bstep (se 1 (by rfl) ⟨193577, by rfl⟩ : syracuseStep 258103 = 387155) B387155
theorem B225355 : Blo 223812 225355 := bstep (se 1 (by rfl) ⟨169016, by rfl⟩ : syracuseStep 225355 = 338033) B338033
theorem B225367 : Blo 223812 225367 := bstep (se 1 (by rfl) ⟨169025, by rfl⟩ : syracuseStep 225367 = 338051) B338051
theorem B323671 : Blo 223812 323671 := bstep (se 1 (by rfl) ⟨242753, by rfl⟩ : syracuseStep 323671 = 485507) B485507
theorem B225387 : Blo 223812 225387 := bstep (se 1 (by rfl) ⟨169040, by rfl⟩ : syracuseStep 225387 = 338081) B338081
theorem B225399 : Blo 223812 225399 := bstep (se 1 (by rfl) ⟨169049, by rfl⟩ : syracuseStep 225399 = 338099) B338099
theorem B1339523 : Blo 223812 1339523 := bstep (se 1 (by rfl) ⟨1004642, by rfl⟩ : syracuseStep 1339523 = 2009285) B2009285
theorem B225419 : Blo 223812 225419 := bstep (se 1 (by rfl) ⟨169064, by rfl⟩ : syracuseStep 225419 = 338129) B338129
theorem B225431 : Blo 223812 225431 := bstep (se 1 (by rfl) ⟨169073, by rfl⟩ : syracuseStep 225431 = 338147) B338147
theorem B225451 : Blo 223812 225451 := bstep (se 1 (by rfl) ⟨169088, by rfl⟩ : syracuseStep 225451 = 338177) B338177
theorem B225463 : Blo 223812 225463 := bstep (se 1 (by rfl) ⟨169097, by rfl⟩ : syracuseStep 225463 = 338195) B338195
theorem B684235 : Blo 223812 684235 := bstep (se 1 (by rfl) ⟨513176, by rfl⟩ : syracuseStep 684235 = 1026353) B1026353
theorem B225483 : Blo 223812 225483 := bstep (se 1 (by rfl) ⟨169112, by rfl⟩ : syracuseStep 225483 = 338225) B338225
theorem B225495 : Blo 223812 225495 := bstep (se 1 (by rfl) ⟨169121, by rfl⟩ : syracuseStep 225495 = 338243) B338243
theorem B225515 : Blo 223812 225515 := bstep (se 1 (by rfl) ⟨169136, by rfl⟩ : syracuseStep 225515 = 338273) B338273
theorem B225527 : Blo 223812 225527 := bstep (se 1 (by rfl) ⟨169145, by rfl⟩ : syracuseStep 225527 = 338291) B338291
theorem B389387 : Blo 223812 389387 := bstep (se 1 (by rfl) ⟨292040, by rfl⟩ : syracuseStep 389387 = 584081) B584081
theorem B225547 : Blo 223812 225547 := bstep (se 1 (by rfl) ⟨169160, by rfl⟩ : syracuseStep 225547 = 338321) B338321
theorem B225559 : Blo 223812 225559 := bstep (se 1 (by rfl) ⟨169169, by rfl⟩ : syracuseStep 225559 = 338339) B338339
theorem B487705 : Blo 223812 487705 := bstep (se 2 (by rfl) ⟨182889, by rfl⟩ : syracuseStep 487705 = 365779) B365779
theorem B225579 : Blo 223812 225579 := bstep (se 1 (by rfl) ⟨169184, by rfl⟩ : syracuseStep 225579 = 338369) B338369
theorem B225591 : Blo 223812 225591 := bstep (se 1 (by rfl) ⟨169193, by rfl⟩ : syracuseStep 225591 = 338387) B338387
theorem B1077569 : Blo 223812 1077569 := bstep (se 2 (by rfl) ⟨404088, by rfl⟩ : syracuseStep 1077569 = 808177) B808177
theorem B225611 : Blo 223812 225611 := bstep (se 1 (by rfl) ⟨169208, by rfl⟩ : syracuseStep 225611 = 338417) B338417
theorem B225623 : Blo 223812 225623 := bstep (se 1 (by rfl) ⟨169217, by rfl⟩ : syracuseStep 225623 = 338435) B338435
theorem B717149 : Blo 223812 717149 := bstep (se 3 (by rfl) ⟨134465, by rfl⟩ : syracuseStep 717149 = 268931) B268931
theorem B225643 : Blo 223812 225643 := bstep (se 1 (by rfl) ⟨169232, by rfl⟩ : syracuseStep 225643 = 338465) B338465
theorem B225655 : Blo 223812 225655 := bstep (se 1 (by rfl) ⟨169241, by rfl⟩ : syracuseStep 225655 = 338483) B338483
theorem B225675 : Blo 223812 225675 := bstep (se 1 (by rfl) ⟨169256, by rfl⟩ : syracuseStep 225675 = 338513) B338513
theorem B225687 : Blo 223812 225687 := bstep (se 1 (by rfl) ⟨169265, by rfl⟩ : syracuseStep 225687 = 338531) B338531
theorem B225707 : Blo 223812 225707 := bstep (se 1 (by rfl) ⟨169280, by rfl⟩ : syracuseStep 225707 = 338561) B338561
theorem B225719 : Blo 223812 225719 := bstep (se 1 (by rfl) ⟨169289, by rfl⟩ : syracuseStep 225719 = 338579) B338579
theorem B225739 : Blo 223812 225739 := bstep (se 1 (by rfl) ⟨169304, by rfl⟩ : syracuseStep 225739 = 338609) B338609
theorem B225751 : Blo 223812 225751 := bstep (se 1 (by rfl) ⟨169313, by rfl⟩ : syracuseStep 225751 = 338627) B338627
theorem B225771 : Blo 223812 225771 := bstep (se 1 (by rfl) ⟨169328, by rfl⟩ : syracuseStep 225771 = 338657) B338657
theorem B225783 : Blo 223812 225783 := bstep (se 1 (by rfl) ⟨169337, by rfl⟩ : syracuseStep 225783 = 338675) B338675
theorem B225803 : Blo 223812 225803 := bstep (se 1 (by rfl) ⟨169352, by rfl⟩ : syracuseStep 225803 = 338705) B338705
theorem B225815 : Blo 223812 225815 := bstep (se 1 (by rfl) ⟨169361, by rfl⟩ : syracuseStep 225815 = 338723) B338723
theorem B225835 : Blo 223812 225835 := bstep (se 1 (by rfl) ⟨169376, by rfl⟩ : syracuseStep 225835 = 338753) B338753
theorem B225847 : Blo 223812 225847 := bstep (se 1 (by rfl) ⟨169385, by rfl⟩ : syracuseStep 225847 = 338771) B338771
theorem B225867 : Blo 223812 225867 := bstep (se 1 (by rfl) ⟨169400, by rfl⟩ : syracuseStep 225867 = 338801) B338801
theorem B225879 : Blo 223812 225879 := bstep (se 1 (by rfl) ⟨169409, by rfl⟩ : syracuseStep 225879 = 338819) B338819
theorem B225899 : Blo 223812 225899 := bstep (se 1 (by rfl) ⟨169424, by rfl⟩ : syracuseStep 225899 = 338849) B338849
theorem B225911 : Blo 223812 225911 := bstep (se 1 (by rfl) ⟨169433, by rfl⟩ : syracuseStep 225911 = 338867) B338867
theorem B225931 : Blo 223812 225931 := bstep (se 1 (by rfl) ⟨169448, by rfl⟩ : syracuseStep 225931 = 338897) B338897
theorem B225943 : Blo 223812 225943 := bstep (se 1 (by rfl) ⟨169457, by rfl⟩ : syracuseStep 225943 = 338915) B338915
theorem B225963 : Blo 223812 225963 := bstep (se 1 (by rfl) ⟨169472, by rfl⟩ : syracuseStep 225963 = 338945) B338945
theorem B225975 : Blo 223812 225975 := bstep (se 1 (by rfl) ⟨169481, by rfl⟩ : syracuseStep 225975 = 338963) B338963
theorem B225995 : Blo 223812 225995 := bstep (se 1 (by rfl) ⟨169496, by rfl⟩ : syracuseStep 225995 = 338993) B338993
theorem B226007 : Blo 223812 226007 := bstep (se 1 (by rfl) ⟨169505, by rfl⟩ : syracuseStep 226007 = 339011) B339011
theorem B226027 : Blo 223812 226027 := bstep (se 1 (by rfl) ⟨169520, by rfl⟩ : syracuseStep 226027 = 339041) B339041
theorem B226039 : Blo 223812 226039 := bstep (se 1 (by rfl) ⟨169529, by rfl⟩ : syracuseStep 226039 = 339059) B339059
theorem B226059 : Blo 223812 226059 := bstep (se 1 (by rfl) ⟨169544, by rfl⟩ : syracuseStep 226059 = 339089) B339089
theorem B226071 : Blo 223812 226071 := bstep (se 1 (by rfl) ⟨169553, by rfl⟩ : syracuseStep 226071 = 339107) B339107
theorem B226091 : Blo 223812 226091 := bstep (se 1 (by rfl) ⟨169568, by rfl⟩ : syracuseStep 226091 = 339137) B339137
theorem B1471277 : Blo 223812 1471277 := bstep (se 3 (by rfl) ⟨275864, by rfl⟩ : syracuseStep 1471277 = 551729) B551729
theorem B226103 : Blo 223812 226103 := bstep (se 1 (by rfl) ⟨169577, by rfl⟩ : syracuseStep 226103 = 339155) B339155
theorem B226123 : Blo 223812 226123 := bstep (se 1 (by rfl) ⟨169592, by rfl⟩ : syracuseStep 226123 = 339185) B339185
theorem B226135 : Blo 223812 226135 := bstep (se 1 (by rfl) ⟨169601, by rfl⟩ : syracuseStep 226135 = 339203) B339203
theorem B226155 : Blo 223812 226155 := bstep (se 1 (by rfl) ⟨169616, by rfl⟩ : syracuseStep 226155 = 339233) B339233
theorem B2749301 : Blo 223812 2749301 := bstep (se 5 (by rfl) ⟨128873, by rfl⟩ : syracuseStep 2749301 = 257747) B257747
theorem B226167 : Blo 223812 226167 := bstep (se 1 (by rfl) ⟨169625, by rfl⟩ : syracuseStep 226167 = 339251) B339251
theorem B226187 : Blo 223812 226187 := bstep (se 1 (by rfl) ⟨169640, by rfl⟩ : syracuseStep 226187 = 339281) B339281
theorem B914327 : Blo 223812 914327 := bstep (se 1 (by rfl) ⟨685745, by rfl⟩ : syracuseStep 914327 = 1371491) B1371491
theorem B226199 : Blo 223812 226199 := bstep (se 1 (by rfl) ⟨169649, by rfl⟩ : syracuseStep 226199 = 339299) B339299
theorem B226219 : Blo 223812 226219 := bstep (se 1 (by rfl) ⟨169664, by rfl⟩ : syracuseStep 226219 = 339329) B339329
theorem B226231 : Blo 223812 226231 := bstep (se 1 (by rfl) ⟨169673, by rfl⟩ : syracuseStep 226231 = 339347) B339347
theorem B226251 : Blo 223812 226251 := bstep (se 1 (by rfl) ⟨169688, by rfl⟩ : syracuseStep 226251 = 339377) B339377
theorem B226263 : Blo 223812 226263 := bstep (se 1 (by rfl) ⟨169697, by rfl⟩ : syracuseStep 226263 = 339395) B339395
theorem B1438681 : Blo 223812 1438681 := bstep (se 2 (by rfl) ⟨539505, by rfl⟩ : syracuseStep 1438681 = 1079011) B1079011
theorem B226283 : Blo 223812 226283 := bstep (se 1 (by rfl) ⟨169712, by rfl⟩ : syracuseStep 226283 = 339425) B339425
theorem B226295 : Blo 223812 226295 := bstep (se 1 (by rfl) ⟨169721, by rfl⟩ : syracuseStep 226295 = 339443) B339443
theorem B226315 : Blo 223812 226315 := bstep (se 1 (by rfl) ⟨169736, by rfl⟩ : syracuseStep 226315 = 339473) B339473
theorem B226327 : Blo 223812 226327 := bstep (se 1 (by rfl) ⟨169745, by rfl⟩ : syracuseStep 226327 = 339491) B339491
theorem B226347 : Blo 223812 226347 := bstep (se 1 (by rfl) ⟨169760, by rfl⟩ : syracuseStep 226347 = 339521) B339521
theorem B226359 : Blo 223812 226359 := bstep (se 1 (by rfl) ⟨169769, by rfl⟩ : syracuseStep 226359 = 339539) B339539
theorem B226379 : Blo 223812 226379 := bstep (se 1 (by rfl) ⟨169784, by rfl⟩ : syracuseStep 226379 = 339569) B339569
theorem B226391 : Blo 223812 226391 := bstep (se 1 (by rfl) ⟨169793, by rfl⟩ : syracuseStep 226391 = 339587) B339587
theorem B226411 : Blo 223812 226411 := bstep (se 1 (by rfl) ⟨169808, by rfl⟩ : syracuseStep 226411 = 339617) B339617
theorem B226423 : Blo 223812 226423 := bstep (se 1 (by rfl) ⟨169817, by rfl⟩ : syracuseStep 226423 = 339635) B339635
theorem B226443 : Blo 223812 226443 := bstep (se 1 (by rfl) ⟨169832, by rfl⟩ : syracuseStep 226443 = 339665) B339665
theorem B226455 : Blo 223812 226455 := bstep (se 1 (by rfl) ⟨169841, by rfl⟩ : syracuseStep 226455 = 339683) B339683
theorem B226475 : Blo 223812 226475 := bstep (se 1 (by rfl) ⟨169856, by rfl⟩ : syracuseStep 226475 = 339713) B339713
theorem B226487 : Blo 223812 226487 := bstep (se 1 (by rfl) ⟨169865, by rfl⟩ : syracuseStep 226487 = 339731) B339731
theorem B226507 : Blo 223812 226507 := bstep (se 1 (by rfl) ⟨169880, by rfl⟩ : syracuseStep 226507 = 339761) B339761
theorem B226519 : Blo 223812 226519 := bstep (se 1 (by rfl) ⟨169889, by rfl⟩ : syracuseStep 226519 = 339779) B339779
theorem B226539 : Blo 223812 226539 := bstep (se 1 (by rfl) ⟨169904, by rfl⟩ : syracuseStep 226539 = 339809) B339809
theorem B226551 : Blo 223812 226551 := bstep (se 1 (by rfl) ⟨169913, by rfl⟩ : syracuseStep 226551 = 339827) B339827
theorem B226571 : Blo 223812 226571 := bstep (se 1 (by rfl) ⟨169928, by rfl⟩ : syracuseStep 226571 = 339857) B339857
theorem B226583 : Blo 223812 226583 := bstep (se 1 (by rfl) ⟨169937, by rfl⟩ : syracuseStep 226583 = 339875) B339875
theorem B226603 : Blo 223812 226603 := bstep (se 1 (by rfl) ⟨169952, by rfl⟩ : syracuseStep 226603 = 339905) B339905
theorem B455987 : Blo 223812 455987 := bstep (se 1 (by rfl) ⟨341990, by rfl⟩ : syracuseStep 455987 = 683981) B683981
theorem B226615 : Blo 223812 226615 := bstep (se 1 (by rfl) ⟨169961, by rfl⟩ : syracuseStep 226615 = 339923) B339923
theorem B226635 : Blo 223812 226635 := bstep (se 1 (by rfl) ⟨169976, by rfl⟩ : syracuseStep 226635 = 339953) B339953
theorem B226647 : Blo 223812 226647 := bstep (se 1 (by rfl) ⟨169985, by rfl⟩ : syracuseStep 226647 = 339971) B339971
theorem B226667 : Blo 223812 226667 := bstep (se 1 (by rfl) ⟨170000, by rfl⟩ : syracuseStep 226667 = 340001) B340001
theorem B226679 : Blo 223812 226679 := bstep (se 1 (by rfl) ⟨170009, by rfl⟩ : syracuseStep 226679 = 340019) B340019
theorem B226699 : Blo 223812 226699 := bstep (se 1 (by rfl) ⟨170024, by rfl⟩ : syracuseStep 226699 = 340049) B340049
theorem B226711 : Blo 223812 226711 := bstep (se 1 (by rfl) ⟨170033, by rfl⟩ : syracuseStep 226711 = 340067) B340067
theorem B226731 : Blo 223812 226731 := bstep (se 1 (by rfl) ⟨170048, by rfl⟩ : syracuseStep 226731 = 340097) B340097
theorem B226743 : Blo 223812 226743 := bstep (se 1 (by rfl) ⟨170057, by rfl⟩ : syracuseStep 226743 = 340115) B340115
theorem B226763 : Blo 223812 226763 := bstep (se 1 (by rfl) ⟨170072, by rfl⟩ : syracuseStep 226763 = 340145) B340145
theorem B226775 : Blo 223812 226775 := bstep (se 1 (by rfl) ⟨170081, by rfl⟩ : syracuseStep 226775 = 340163) B340163
theorem B226795 : Blo 223812 226795 := bstep (se 1 (by rfl) ⟨170096, by rfl⟩ : syracuseStep 226795 = 340193) B340193
theorem B226807 : Blo 223812 226807 := bstep (se 1 (by rfl) ⟨170105, by rfl⟩ : syracuseStep 226807 = 340211) B340211
theorem B226827 : Blo 223812 226827 := bstep (se 1 (by rfl) ⟨170120, by rfl⟩ : syracuseStep 226827 = 340241) B340241
theorem B226839 : Blo 223812 226839 := bstep (se 1 (by rfl) ⟨170129, by rfl⟩ : syracuseStep 226839 = 340259) B340259
theorem B226859 : Blo 223812 226859 := bstep (se 1 (by rfl) ⟨170144, by rfl⟩ : syracuseStep 226859 = 340289) B340289
theorem B226871 : Blo 223812 226871 := bstep (se 1 (by rfl) ⟨170153, by rfl⟩ : syracuseStep 226871 = 340307) B340307
theorem B226891 : Blo 223812 226891 := bstep (se 1 (by rfl) ⟨170168, by rfl⟩ : syracuseStep 226891 = 340337) B340337
theorem B1078859 : Blo 223812 1078859 := bstep (se 1 (by rfl) ⟨809144, by rfl⟩ : syracuseStep 1078859 = 1618289) B1618289
theorem B226903 : Blo 223812 226903 := bstep (se 1 (by rfl) ⟨170177, by rfl⟩ : syracuseStep 226903 = 340355) B340355
theorem B226923 : Blo 223812 226923 := bstep (se 1 (by rfl) ⟨170192, by rfl⟩ : syracuseStep 226923 = 340385) B340385
theorem B226935 : Blo 223812 226935 := bstep (se 1 (by rfl) ⟨170201, by rfl⟩ : syracuseStep 226935 = 340403) B340403
theorem B226955 : Blo 223812 226955 := bstep (se 1 (by rfl) ⟨170216, by rfl⟩ : syracuseStep 226955 = 340433) B340433
theorem B226967 : Blo 223812 226967 := bstep (se 1 (by rfl) ⟨170225, by rfl⟩ : syracuseStep 226967 = 340451) B340451
theorem B226987 : Blo 223812 226987 := bstep (se 1 (by rfl) ⟨170240, by rfl⟩ : syracuseStep 226987 = 340481) B340481
theorem B226999 : Blo 223812 226999 := bstep (se 1 (by rfl) ⟨170249, by rfl⟩ : syracuseStep 226999 = 340499) B340499
theorem B227019 : Blo 223812 227019 := bstep (se 1 (by rfl) ⟨170264, by rfl⟩ : syracuseStep 227019 = 340529) B340529
theorem B227031 : Blo 223812 227031 := bstep (se 1 (by rfl) ⟨170273, by rfl⟩ : syracuseStep 227031 = 340547) B340547
theorem B227051 : Blo 223812 227051 := bstep (se 1 (by rfl) ⟨170288, by rfl⟩ : syracuseStep 227051 = 340577) B340577
theorem B227063 : Blo 223812 227063 := bstep (se 1 (by rfl) ⟨170297, by rfl⟩ : syracuseStep 227063 = 340595) B340595
theorem B227083 : Blo 223812 227083 := bstep (se 1 (by rfl) ⟨170312, by rfl⟩ : syracuseStep 227083 = 340625) B340625
theorem B816913 : Blo 223812 816913 := bstep (se 2 (by rfl) ⟨306342, by rfl⟩ : syracuseStep 816913 = 612685) B612685
theorem B227095 : Blo 223812 227095 := bstep (se 1 (by rfl) ⟨170321, by rfl⟩ : syracuseStep 227095 = 340643) B340643
theorem B227115 : Blo 223812 227115 := bstep (se 1 (by rfl) ⟨170336, by rfl⟩ : syracuseStep 227115 = 340673) B340673
theorem B227127 : Blo 223812 227127 := bstep (se 1 (by rfl) ⟨170345, by rfl⟩ : syracuseStep 227127 = 340691) B340691
theorem B2094913 : Blo 223812 2094913 := bstep (se 2 (by rfl) ⟨785592, by rfl⟩ : syracuseStep 2094913 = 1571185) B1571185
theorem B227147 : Blo 223812 227147 := bstep (se 1 (by rfl) ⟨170360, by rfl⟩ : syracuseStep 227147 = 340721) B340721
theorem B227159 : Blo 223812 227159 := bstep (se 1 (by rfl) ⟨170369, by rfl⟩ : syracuseStep 227159 = 340739) B340739
theorem B227179 : Blo 223812 227179 := bstep (se 1 (by rfl) ⟨170384, by rfl⟩ : syracuseStep 227179 = 340769) B340769
theorem B227191 : Blo 223812 227191 := bstep (se 1 (by rfl) ⟨170393, by rfl⟩ : syracuseStep 227191 = 340787) B340787
theorem B227211 : Blo 223812 227211 := bstep (se 1 (by rfl) ⟨170408, by rfl⟩ : syracuseStep 227211 = 340817) B340817
theorem B227223 : Blo 223812 227223 := bstep (se 1 (by rfl) ⟨170417, by rfl⟩ : syracuseStep 227223 = 340835) B340835
theorem B227243 : Blo 223812 227243 := bstep (se 1 (by rfl) ⟨170432, by rfl⟩ : syracuseStep 227243 = 340865) B340865
theorem B12318641 : Blo 223812 12318641 := bstep (se 2 (by rfl) ⟨4619490, by rfl⟩ : syracuseStep 12318641 = 9238981) B9238981
theorem B227255 : Blo 223812 227255 := bstep (se 1 (by rfl) ⟨170441, by rfl⟩ : syracuseStep 227255 = 340883) B340883
theorem B227275 : Blo 223812 227275 := bstep (se 1 (by rfl) ⟨170456, by rfl⟩ : syracuseStep 227275 = 340913) B340913
theorem B227287 : Blo 223812 227287 := bstep (se 1 (by rfl) ⟨170465, by rfl⟩ : syracuseStep 227287 = 340931) B340931
theorem B227307 : Blo 223812 227307 := bstep (se 1 (by rfl) ⟨170480, by rfl⟩ : syracuseStep 227307 = 340961) B340961
theorem B227319 : Blo 223812 227319 := bstep (se 1 (by rfl) ⟨170489, by rfl⟩ : syracuseStep 227319 = 340979) B340979
theorem B849923 : Blo 223812 849923 := bstep (se 1 (by rfl) ⟨637442, by rfl⟩ : syracuseStep 849923 = 1274885) B1274885
theorem B227339 : Blo 223812 227339 := bstep (se 1 (by rfl) ⟨170504, by rfl⟩ : syracuseStep 227339 = 341009) B341009
theorem B227351 : Blo 223812 227351 := bstep (se 1 (by rfl) ⟨170513, by rfl⟩ : syracuseStep 227351 = 341027) B341027
theorem B227371 : Blo 223812 227371 := bstep (se 1 (by rfl) ⟨170528, by rfl⟩ : syracuseStep 227371 = 341057) B341057
theorem B227383 : Blo 223812 227383 := bstep (se 1 (by rfl) ⟨170537, by rfl⟩ : syracuseStep 227383 = 341075) B341075
theorem B227403 : Blo 223812 227403 := bstep (se 1 (by rfl) ⟨170552, by rfl⟩ : syracuseStep 227403 = 341105) B341105
theorem B227415 : Blo 223812 227415 := bstep (se 1 (by rfl) ⟨170561, by rfl⟩ : syracuseStep 227415 = 341123) B341123
theorem B227435 : Blo 223812 227435 := bstep (se 1 (by rfl) ⟨170576, by rfl⟩ : syracuseStep 227435 = 341153) B341153
theorem B227447 : Blo 223812 227447 := bstep (se 1 (by rfl) ⟨170585, by rfl⟩ : syracuseStep 227447 = 341171) B341171
theorem B227467 : Blo 223812 227467 := bstep (se 1 (by rfl) ⟨170600, by rfl⟩ : syracuseStep 227467 = 341201) B341201
theorem B227479 : Blo 223812 227479 := bstep (se 1 (by rfl) ⟨170609, by rfl⟩ : syracuseStep 227479 = 341219) B341219
theorem B227499 : Blo 223812 227499 := bstep (se 1 (by rfl) ⟨170624, by rfl⟩ : syracuseStep 227499 = 341249) B341249
theorem B227511 : Blo 223812 227511 := bstep (se 1 (by rfl) ⟨170633, by rfl⟩ : syracuseStep 227511 = 341267) B341267
theorem B227531 : Blo 223812 227531 := bstep (se 1 (by rfl) ⟨170648, by rfl⟩ : syracuseStep 227531 = 341297) B341297
theorem B227543 : Blo 223812 227543 := bstep (se 1 (by rfl) ⟨170657, by rfl⟩ : syracuseStep 227543 = 341315) B341315
theorem B227563 : Blo 223812 227563 := bstep (se 1 (by rfl) ⟨170672, by rfl⟩ : syracuseStep 227563 = 341345) B341345
theorem B227575 : Blo 223812 227575 := bstep (se 1 (by rfl) ⟨170681, by rfl⟩ : syracuseStep 227575 = 341363) B341363
theorem B227595 : Blo 223812 227595 := bstep (se 1 (by rfl) ⟨170696, by rfl⟩ : syracuseStep 227595 = 341393) B341393
theorem B1734929 : Blo 223812 1734929 := bstep (se 2 (by rfl) ⟨650598, by rfl⟩ : syracuseStep 1734929 = 1301197) B1301197
theorem B227607 : Blo 223812 227607 := bstep (se 1 (by rfl) ⟨170705, by rfl⟩ : syracuseStep 227607 = 341411) B341411
theorem B227627 : Blo 223812 227627 := bstep (se 1 (by rfl) ⟨170720, by rfl⟩ : syracuseStep 227627 = 341441) B341441
theorem B11794733 : Blo 223812 11794733 := bstep (se 3 (by rfl) ⟨2211512, by rfl⟩ : syracuseStep 11794733 = 4423025) B4423025
theorem B227639 : Blo 223812 227639 := bstep (se 1 (by rfl) ⟨170729, by rfl⟩ : syracuseStep 227639 = 341459) B341459
theorem B227659 : Blo 223812 227659 := bstep (se 1 (by rfl) ⟨170744, by rfl⟩ : syracuseStep 227659 = 341489) B341489
theorem B227671 : Blo 223812 227671 := bstep (se 1 (by rfl) ⟨170753, by rfl⟩ : syracuseStep 227671 = 341507) B341507
theorem B457049 : Blo 223812 457049 := bstep (se 2 (by rfl) ⟨171393, by rfl⟩ : syracuseStep 457049 = 342787) B342787
theorem B227691 : Blo 223812 227691 := bstep (se 1 (by rfl) ⟨170768, by rfl⟩ : syracuseStep 227691 = 341537) B341537
theorem B227703 : Blo 223812 227703 := bstep (se 1 (by rfl) ⟨170777, by rfl⟩ : syracuseStep 227703 = 341555) B341555
theorem B227723 : Blo 223812 227723 := bstep (se 1 (by rfl) ⟨170792, by rfl⟩ : syracuseStep 227723 = 341585) B341585
theorem B227735 : Blo 223812 227735 := bstep (se 1 (by rfl) ⟨170801, by rfl⟩ : syracuseStep 227735 = 341603) B341603
theorem B227755 : Blo 223812 227755 := bstep (se 1 (by rfl) ⟨170816, by rfl⟩ : syracuseStep 227755 = 341633) B341633
theorem B227767 : Blo 223812 227767 := bstep (se 1 (by rfl) ⟨170825, by rfl⟩ : syracuseStep 227767 = 341651) B341651
theorem B227787 : Blo 223812 227787 := bstep (se 1 (by rfl) ⟨170840, by rfl⟩ : syracuseStep 227787 = 341681) B341681
theorem B227799 : Blo 223812 227799 := bstep (se 1 (by rfl) ⟨170849, by rfl⟩ : syracuseStep 227799 = 341699) B341699
theorem B227819 : Blo 223812 227819 := bstep (se 1 (by rfl) ⟨170864, by rfl⟩ : syracuseStep 227819 = 341729) B341729
theorem B1080337 : Blo 223812 1080337 := bstep (se 2 (by rfl) ⟨405126, by rfl⟩ : syracuseStep 1080337 = 810253) B810253
theorem B6290507 : Blo 223812 6290507 := bstep (se 1 (by rfl) ⟨4717880, by rfl⟩ : syracuseStep 6290507 = 9435761) B9435761
theorem B490583 : Blo 223812 490583 := bstep (se 1 (by rfl) ⟨367937, by rfl⟩ : syracuseStep 490583 = 735875) B735875
theorem B1145987 : Blo 223812 1145987 := bstep (se 1 (by rfl) ⟨859490, by rfl⟩ : syracuseStep 1145987 = 1718981) B1718981
theorem B3112067 : Blo 223812 3112067 := bstep (se 1 (by rfl) ⟨2334050, by rfl⟩ : syracuseStep 3112067 = 4668101) B4668101
theorem B2587949 : Blo 223812 2587949 := bstep (se 3 (by rfl) ⟨485240, by rfl⟩ : syracuseStep 2587949 = 970481) B970481
theorem B1932761 : Blo 223812 1932761 := bstep (se 2 (by rfl) ⟨724785, by rfl⟩ : syracuseStep 1932761 = 1449571) B1449571
theorem B1703429 : Blo 223812 1703429 := bstep (se 4 (by rfl) ⟨159696, by rfl⟩ : syracuseStep 1703429 = 319393) B319393
theorem B359959 : Blo 223812 359959 := bstep (se 1 (by rfl) ⟨269969, by rfl⟩ : syracuseStep 359959 = 539939) B539939
theorem B1637981 : Blo 223812 1637981 := bstep (se 3 (by rfl) ⟨307121, by rfl⟩ : syracuseStep 1637981 = 614243) B614243
theorem B1212005 : Blo 223812 1212005 := bstep (se 4 (by rfl) ⟨113625, by rfl⟩ : syracuseStep 1212005 = 227251) B227251
theorem B425675 : Blo 223812 425675 := bstep (se 1 (by rfl) ⟨319256, by rfl⟩ : syracuseStep 425675 = 638513) B638513
theorem B425729 : Blo 223812 425729 := bstep (se 2 (by rfl) ⟨159648, by rfl⟩ : syracuseStep 425729 = 319297) B319297
theorem B360215 : Blo 223812 360215 := bstep (se 1 (by rfl) ⟨270161, by rfl⟩ : syracuseStep 360215 = 540323) B540323
theorem B655169 : Blo 223812 655169 := bstep (se 2 (by rfl) ⟨245688, by rfl⟩ : syracuseStep 655169 = 491377) B491377
theorem B2916161 : Blo 223812 2916161 := bstep (se 2 (by rfl) ⟨1093560, by rfl⟩ : syracuseStep 2916161 = 2187121) B2187121
theorem B360407 : Blo 223812 360407 := bstep (se 1 (by rfl) ⟨270305, by rfl⟩ : syracuseStep 360407 = 540611) B540611
theorem B983069 : Blo 223812 983069 := bstep (se 3 (by rfl) ⟨184325, by rfl⟩ : syracuseStep 983069 = 368651) B368651
theorem B426131 : Blo 223812 426131 := bstep (se 1 (by rfl) ⟨319598, by rfl⟩ : syracuseStep 426131 = 639197) B639197
theorem B426359 : Blo 223812 426359 := bstep (se 1 (by rfl) ⟨319769, by rfl⟩ : syracuseStep 426359 = 639539) B639539
theorem B1147283 : Blo 223812 1147283 := bstep (se 1 (by rfl) ⟨860462, by rfl⟩ : syracuseStep 1147283 = 1720925) B1720925
theorem B1704401 : Blo 223812 1704401 := bstep (se 2 (by rfl) ⟨639150, by rfl⟩ : syracuseStep 1704401 = 1278301) B1278301
theorem B820115 : Blo 223812 820115 := bstep (se 1 (by rfl) ⟨615086, by rfl⟩ : syracuseStep 820115 = 1230173) B1230173
theorem B19104709 : Blo 223812 19104709 := bstep (se 4 (by rfl) ⟨1791066, by rfl⟩ : syracuseStep 19104709 = 3582133) B3582133
theorem B492833 : Blo 223812 492833 := bstep (se 2 (by rfl) ⟨184812, by rfl⟩ : syracuseStep 492833 = 369625) B369625
theorem B2557331 : Blo 223812 2557331 := bstep (se 1 (by rfl) ⟨1917998, by rfl⟩ : syracuseStep 2557331 = 3835997) B3835997
theorem B329131 : Blo 223812 329131 := bstep (se 1 (by rfl) ⟨246848, by rfl⟩ : syracuseStep 329131 = 493697) B493697
theorem B1541585 : Blo 223812 1541585 := bstep (se 2 (by rfl) ⟨578094, by rfl⟩ : syracuseStep 1541585 = 1156189) B1156189
theorem B1279759 : Blo 223812 1279759 := bstep (se 1 (by rfl) ⟨959819, by rfl⟩ : syracuseStep 1279759 = 1919639) B1919639
theorem B428075 : Blo 223812 428075 := bstep (se 1 (by rfl) ⟨321056, by rfl⟩ : syracuseStep 428075 = 642113) B642113
theorem B460859 : Blo 223812 460859 := bstep (se 1 (by rfl) ⟨345644, by rfl⟩ : syracuseStep 460859 = 691289) B691289
theorem B755831 : Blo 223812 755831 := bstep (se 1 (by rfl) ⟨566873, by rfl⟩ : syracuseStep 755831 = 1133747) B1133747
theorem B1444013 : Blo 223812 1444013 := bstep (se 3 (by rfl) ⟨270752, by rfl⟩ : syracuseStep 1444013 = 541505) B541505
theorem B428303 : Blo 223812 428303 := bstep (se 1 (by rfl) ⟨321227, by rfl⟩ : syracuseStep 428303 = 642455) B642455
theorem B461099 : Blo 223812 461099 := bstep (se 1 (by rfl) ⟨345824, by rfl⟩ : syracuseStep 461099 = 691649) B691649
theorem B330043 : Blo 223812 330043 := bstep (se 1 (by rfl) ⟨247532, by rfl⟩ : syracuseStep 330043 = 495065) B495065
theorem B756539 : Blo 223812 756539 := bstep (se 1 (by rfl) ⟨567404, by rfl⟩ : syracuseStep 756539 = 1134809) B1134809
theorem B1281035 : Blo 223812 1281035 := bstep (se 1 (by rfl) ⟨960776, by rfl⟩ : syracuseStep 1281035 = 1921553) B1921553
theorem B1281217 : Blo 223812 1281217 := bstep (se 2 (by rfl) ⟨480456, by rfl⟩ : syracuseStep 1281217 = 960913) B960913
theorem B4656365 : Blo 223812 4656365 := bstep (se 3 (by rfl) ⟨873068, by rfl⟩ : syracuseStep 4656365 = 1746137) B1746137
theorem B757025 : Blo 223812 757025 := bstep (se 2 (by rfl) ⟨283884, by rfl⟩ : syracuseStep 757025 = 567769) B567769
theorem B3706145 : Blo 223812 3706145 := bstep (se 2 (by rfl) ⟨1389804, by rfl⟩ : syracuseStep 3706145 = 2779609) B2779609
theorem B1150361 : Blo 223812 1150361 := bstep (se 2 (by rfl) ⟨431385, by rfl⟩ : syracuseStep 1150361 = 862771) B862771
theorem B855481 : Blo 223812 855481 := bstep (se 2 (by rfl) ⟨320805, by rfl⟩ : syracuseStep 855481 = 641611) B641611
theorem B1215965 : Blo 223812 1215965 := bstep (se 3 (by rfl) ⟨227993, by rfl⟩ : syracuseStep 1215965 = 455987) B455987
theorem B1314269 : Blo 223812 1314269 := bstep (se 3 (by rfl) ⟨246425, by rfl⟩ : syracuseStep 1314269 = 492851) B492851
theorem B1969667 : Blo 223812 1969667 := bstep (se 1 (by rfl) ⟨1477250, by rfl⟩ : syracuseStep 1969667 = 2954501) B2954501
theorem B2592323 : Blo 223812 2592323 := bstep (se 1 (by rfl) ⟨1944242, by rfl⟩ : syracuseStep 2592323 = 3888485) B3888485
theorem B429715 : Blo 223812 429715 := bstep (se 1 (by rfl) ⟨322286, by rfl⟩ : syracuseStep 429715 = 644573) B644573
theorem B1314593 : Blo 223812 1314593 := bstep (se 2 (by rfl) ⟨492972, by rfl⟩ : syracuseStep 1314593 = 985945) B985945
theorem B757619 : Blo 223812 757619 := bstep (se 1 (by rfl) ⟨568214, by rfl⟩ : syracuseStep 757619 = 1136429) B1136429
theorem B429943 : Blo 223812 429943 := bstep (se 1 (by rfl) ⟨322457, by rfl⟩ : syracuseStep 429943 = 644915) B644915
theorem B724889 : Blo 223812 724889 := bstep (se 2 (by rfl) ⟨271833, by rfl⟩ : syracuseStep 724889 = 543667) B543667
theorem B3870989 : Blo 223812 3870989 := bstep (se 3 (by rfl) ⟨725810, by rfl⟩ : syracuseStep 3870989 = 1451621) B1451621
theorem B3707459 : Blo 223812 3707459 := bstep (se 1 (by rfl) ⟨2780594, by rfl⟩ : syracuseStep 3707459 = 5561189) B5561189
theorem B1217369 : Blo 223812 1217369 := bstep (se 2 (by rfl) ⟨456513, by rfl⟩ : syracuseStep 1217369 = 913027) B913027
theorem B1021319 : Blo 223812 1021319 := bstep (se 1 (by rfl) ⟨765989, by rfl⟩ : syracuseStep 1021319 = 1531979) B1531979
theorem B431507 : Blo 223812 431507 := bstep (se 1 (by rfl) ⟨323630, by rfl⟩ : syracuseStep 431507 = 647261) B647261
theorem B431561 : Blo 223812 431561 := bstep (se 2 (by rfl) ⟨161835, by rfl⟩ : syracuseStep 431561 = 323671) B323671
theorem B431659 : Blo 223812 431659 := bstep (se 1 (by rfl) ⟨323744, by rfl⟩ : syracuseStep 431659 = 647489) B647489
theorem B4363955 : Blo 223812 4363955 := bstep (se 1 (by rfl) ⟨3272966, by rfl⟩ : syracuseStep 4363955 = 6545933) B6545933
theorem B923393 : Blo 223812 923393 := bstep (se 2 (by rfl) ⟨346272, by rfl⟩ : syracuseStep 923393 = 692545) B692545
theorem B431887 : Blo 223812 431887 := bstep (se 1 (by rfl) ⟨323915, by rfl⟩ : syracuseStep 431887 = 647831) B647831
theorem B1152953 : Blo 223812 1152953 := bstep (se 2 (by rfl) ⟨432357, by rfl⟩ : syracuseStep 1152953 = 864715) B864715
theorem B1218797 : Blo 223812 1218797 := bstep (se 3 (by rfl) ⟨228524, by rfl⟩ : syracuseStep 1218797 = 457049) B457049
theorem B858383 : Blo 223812 858383 := bstep (se 1 (by rfl) ⟨643787, by rfl⟩ : syracuseStep 858383 = 1287575) B1287575
theorem B1153415 : Blo 223812 1153415 := bstep (se 1 (by rfl) ⟨865061, by rfl⟩ : syracuseStep 1153415 = 1730123) B1730123
theorem B760211 : Blo 223812 760211 := bstep (se 1 (by rfl) ⟨570158, by rfl⟩ : syracuseStep 760211 = 1140317) B1140317
theorem B269191 : Blo 223812 269191 := bstep (se 1 (by rfl) ⟨201893, by rfl⟩ : syracuseStep 269191 = 403787) B403787
theorem B1449161 : Blo 223812 1449161 := bstep (se 2 (by rfl) ⟨543435, by rfl⟩ : syracuseStep 1449161 = 1086871) B1086871
theorem B1285409 : Blo 223812 1285409 := bstep (se 2 (by rfl) ⟨482028, by rfl⟩ : syracuseStep 1285409 = 964057) B964057
theorem B728605 : Blo 223812 728605 := bstep (se 3 (by rfl) ⟨136613, by rfl⟩ : syracuseStep 728605 = 273227) B273227
theorem B1089217 : Blo 223812 1089217 := bstep (se 2 (by rfl) ⟨408456, by rfl⟩ : syracuseStep 1089217 = 816913) B816913
theorem B2924261 : Blo 223812 2924261 := bstep (se 4 (by rfl) ⟨274149, by rfl⟩ : syracuseStep 2924261 = 548299) B548299
theorem B2793217 : Blo 223812 2793217 := bstep (se 2 (by rfl) ⟨1047456, by rfl⟩ : syracuseStep 2793217 = 2094913) B2094913
theorem B761615 : Blo 223812 761615 := bstep (se 1 (by rfl) ⟨571211, by rfl⟩ : syracuseStep 761615 = 1142423) B1142423
theorem B335735 : Blo 223812 335735 := bstep (se 1 (by rfl) ⟨251801, by rfl⟩ : syracuseStep 335735 = 503603) B503603
theorem B335759 : Blo 223812 335759 := bstep (se 1 (by rfl) ⟨251819, by rfl⟩ : syracuseStep 335759 = 503639) B503639
theorem B335801 : Blo 223812 335801 := bstep (se 2 (by rfl) ⟨125925, by rfl⟩ : syracuseStep 335801 = 251851) B251851
theorem B335879 : Blo 223812 335879 := bstep (se 1 (by rfl) ⟨251909, by rfl⟩ : syracuseStep 335879 = 503819) B503819
theorem B761885 : Blo 223812 761885 := bstep (se 3 (by rfl) ⟨142853, by rfl⟩ : syracuseStep 761885 = 285707) B285707
theorem B335915 : Blo 223812 335915 := bstep (se 1 (by rfl) ⟨251936, by rfl⟩ : syracuseStep 335915 = 503873) B503873
theorem B335945 : Blo 223812 335945 := bstep (se 2 (by rfl) ⟨125979, by rfl⟩ : syracuseStep 335945 = 251959) B251959
theorem B893015 : Blo 223812 893015 := bstep (se 1 (by rfl) ⟨669761, by rfl⟩ : syracuseStep 893015 = 1339523) B1339523
theorem B336059 : Blo 223812 336059 := bstep (se 1 (by rfl) ⟨252044, by rfl⟩ : syracuseStep 336059 = 504089) B504089
theorem B2728181 : Blo 223812 2728181 := bstep (se 5 (by rfl) ⟨127883, by rfl⟩ : syracuseStep 2728181 = 255767) B255767
theorem B336119 : Blo 223812 336119 := bstep (se 1 (by rfl) ⟨252089, by rfl⟩ : syracuseStep 336119 = 504179) B504179
theorem B336143 : Blo 223812 336143 := bstep (se 1 (by rfl) ⟨252107, by rfl⟩ : syracuseStep 336143 = 504215) B504215
theorem B467215 : Blo 223812 467215 := bstep (se 1 (by rfl) ⟨350411, by rfl⟩ : syracuseStep 467215 = 700823) B700823
theorem B336185 : Blo 223812 336185 := bstep (se 2 (by rfl) ⟨126069, by rfl⟩ : syracuseStep 336185 = 252139) B252139
theorem B8298845 : Blo 223812 8298845 := bstep (se 3 (by rfl) ⟨1556033, by rfl⟩ : syracuseStep 8298845 = 3112067) B3112067
theorem B336263 : Blo 223812 336263 := bstep (se 1 (by rfl) ⟨252197, by rfl⟩ : syracuseStep 336263 = 504395) B504395
theorem B2171281 : Blo 223812 2171281 := bstep (se 2 (by rfl) ⟨814230, by rfl⟩ : syracuseStep 2171281 = 1628461) B1628461
theorem B336299 : Blo 223812 336299 := bstep (se 1 (by rfl) ⟨252224, by rfl⟩ : syracuseStep 336299 = 504449) B504449
theorem B336329 : Blo 223812 336329 := bstep (se 2 (by rfl) ⟨126123, by rfl⟩ : syracuseStep 336329 = 252247) B252247
theorem B336443 : Blo 223812 336443 := bstep (se 1 (by rfl) ⟨252332, by rfl⟩ : syracuseStep 336443 = 504665) B504665
theorem B336503 : Blo 223812 336503 := bstep (se 1 (by rfl) ⟨252377, by rfl⟩ : syracuseStep 336503 = 504755) B504755
theorem B270983 : Blo 223812 270983 := bstep (se 1 (by rfl) ⟨203237, by rfl⟩ : syracuseStep 270983 = 406475) B406475
theorem B336527 : Blo 223812 336527 := bstep (se 1 (by rfl) ⟨252395, by rfl⟩ : syracuseStep 336527 = 504791) B504791
theorem B336569 : Blo 223812 336569 := bstep (se 2 (by rfl) ⟨126213, by rfl⟩ : syracuseStep 336569 = 252427) B252427
theorem B336647 : Blo 223812 336647 := bstep (se 1 (by rfl) ⟨252485, by rfl⟩ : syracuseStep 336647 = 504971) B504971
theorem B2892581 : Blo 223812 2892581 := bstep (se 4 (by rfl) ⟨271179, by rfl⟩ : syracuseStep 2892581 = 542359) B542359
theorem B336683 : Blo 223812 336683 := bstep (se 1 (by rfl) ⟨252512, by rfl⟩ : syracuseStep 336683 = 505025) B505025
theorem B336713 : Blo 223812 336713 := bstep (se 2 (by rfl) ⟨126267, by rfl⟩ : syracuseStep 336713 = 252535) B252535
theorem B336827 : Blo 223812 336827 := bstep (se 1 (by rfl) ⟨252620, by rfl⟩ : syracuseStep 336827 = 505241) B505241
theorem B271291 : Blo 223812 271291 := bstep (se 1 (by rfl) ⟨203468, by rfl⟩ : syracuseStep 271291 = 406937) B406937
theorem B336887 : Blo 223812 336887 := bstep (se 1 (by rfl) ⟨252665, by rfl⟩ : syracuseStep 336887 = 505331) B505331
theorem B336911 : Blo 223812 336911 := bstep (se 1 (by rfl) ⟨252683, by rfl⟩ : syracuseStep 336911 = 505367) B505367
theorem B336953 : Blo 223812 336953 := bstep (se 2 (by rfl) ⟨126357, by rfl⟩ : syracuseStep 336953 = 252715) B252715
theorem B337031 : Blo 223812 337031 := bstep (se 1 (by rfl) ⟨252773, by rfl⟩ : syracuseStep 337031 = 505547) B505547
theorem B337067 : Blo 223812 337067 := bstep (se 1 (by rfl) ⟨252800, by rfl⟩ : syracuseStep 337067 = 505601) B505601
theorem B337097 : Blo 223812 337097 := bstep (se 2 (by rfl) ⟨126411, by rfl⟩ : syracuseStep 337097 = 252823) B252823
theorem B1615085 : Blo 223812 1615085 := bstep (se 3 (by rfl) ⟨302828, by rfl⟩ : syracuseStep 1615085 = 605657) B605657
theorem B337211 : Blo 223812 337211 := bstep (se 1 (by rfl) ⟨252908, by rfl⟩ : syracuseStep 337211 = 505817) B505817
theorem B566615 : Blo 223812 566615 := bstep (se 1 (by rfl) ⟨424961, by rfl⟩ : syracuseStep 566615 = 849923) B849923
theorem B337271 : Blo 223812 337271 := bstep (se 1 (by rfl) ⟨252953, by rfl⟩ : syracuseStep 337271 = 505907) B505907
theorem B337295 : Blo 223812 337295 := bstep (se 1 (by rfl) ⟨252971, by rfl⟩ : syracuseStep 337295 = 505943) B505943
theorem B861587 : Blo 223812 861587 := bstep (se 1 (by rfl) ⟨646190, by rfl⟩ : syracuseStep 861587 = 1292381) B1292381
theorem B763289 : Blo 223812 763289 := bstep (se 2 (by rfl) ⟨286233, by rfl⟩ : syracuseStep 763289 = 572467) B572467
theorem B337337 : Blo 223812 337337 := bstep (se 2 (by rfl) ⟨126501, by rfl⟩ : syracuseStep 337337 = 253003) B253003
theorem B337415 : Blo 223812 337415 := bstep (se 1 (by rfl) ⟨253061, by rfl⟩ : syracuseStep 337415 = 506123) B506123
theorem B1156619 : Blo 223812 1156619 := bstep (se 1 (by rfl) ⟨867464, by rfl⟩ : syracuseStep 1156619 = 1734929) B1734929
theorem B337451 : Blo 223812 337451 := bstep (se 1 (by rfl) ⟨253088, by rfl⟩ : syracuseStep 337451 = 506177) B506177
theorem B337481 : Blo 223812 337481 := bstep (se 2 (by rfl) ⟨126555, by rfl⟩ : syracuseStep 337481 = 253111) B253111
theorem B4990643 : Blo 223812 4990643 := bstep (se 1 (by rfl) ⟨3742982, by rfl⟩ : syracuseStep 4990643 = 7485965) B7485965
theorem B337595 : Blo 223812 337595 := bstep (se 1 (by rfl) ⟨253196, by rfl⟩ : syracuseStep 337595 = 506393) B506393
theorem B337655 : Blo 223812 337655 := bstep (se 1 (by rfl) ⟨253241, by rfl⟩ : syracuseStep 337655 = 506483) B506483
theorem B337679 : Blo 223812 337679 := bstep (se 1 (by rfl) ⟨253259, by rfl⟩ : syracuseStep 337679 = 506519) B506519
theorem B337721 : Blo 223812 337721 := bstep (se 2 (by rfl) ⟨126645, by rfl⟩ : syracuseStep 337721 = 253291) B253291
theorem B18425717 : Blo 223812 18425717 := bstep (se 5 (by rfl) ⟨863705, by rfl⟩ : syracuseStep 18425717 = 1727411) B1727411
theorem B337799 : Blo 223812 337799 := bstep (se 1 (by rfl) ⟨253349, by rfl⟩ : syracuseStep 337799 = 506699) B506699
theorem B337835 : Blo 223812 337835 := bstep (se 1 (by rfl) ⟨253376, by rfl⟩ : syracuseStep 337835 = 506753) B506753
theorem B337865 : Blo 223812 337865 := bstep (se 2 (by rfl) ⟨126699, by rfl⟩ : syracuseStep 337865 = 253399) B253399
theorem B337979 : Blo 223812 337979 := bstep (se 1 (by rfl) ⟨253484, by rfl⟩ : syracuseStep 337979 = 506969) B506969
theorem B763991 : Blo 223812 763991 := bstep (se 1 (by rfl) ⟨572993, by rfl⟩ : syracuseStep 763991 = 1145987) B1145987
theorem B338039 : Blo 223812 338039 := bstep (se 1 (by rfl) ⟨253529, by rfl⟩ : syracuseStep 338039 = 507059) B507059
theorem B338063 : Blo 223812 338063 := bstep (se 1 (by rfl) ⟨253547, by rfl⟩ : syracuseStep 338063 = 507095) B507095
theorem B1747117 : Blo 223812 1747117 := bstep (se 3 (by rfl) ⟨327584, by rfl⟩ : syracuseStep 1747117 = 655169) B655169
theorem B338105 : Blo 223812 338105 := bstep (se 2 (by rfl) ⟨126789, by rfl⟩ : syracuseStep 338105 = 253579) B253579
theorem B338183 : Blo 223812 338183 := bstep (se 1 (by rfl) ⟨253637, by rfl⟩ : syracuseStep 338183 = 507275) B507275
theorem B338219 : Blo 223812 338219 := bstep (se 1 (by rfl) ⟨253664, by rfl⟩ : syracuseStep 338219 = 507329) B507329
theorem B1288507 : Blo 223812 1288507 := bstep (se 1 (by rfl) ⟨966380, by rfl⟩ : syracuseStep 1288507 = 1932761) B1932761
theorem B338249 : Blo 223812 338249 := bstep (se 2 (by rfl) ⟨126843, by rfl⟩ : syracuseStep 338249 = 253687) B253687
theorem B403859 : Blo 223812 403859 := bstep (se 1 (by rfl) ⟨302894, by rfl⟩ : syracuseStep 403859 = 605789) B605789
theorem B1091987 : Blo 223812 1091987 := bstep (se 1 (by rfl) ⟨818990, by rfl⟩ : syracuseStep 1091987 = 1637981) B1637981
theorem B338363 : Blo 223812 338363 := bstep (se 1 (by rfl) ⟨253772, by rfl⟩ : syracuseStep 338363 = 507545) B507545
theorem B338423 : Blo 223812 338423 := bstep (se 1 (by rfl) ⟨253817, by rfl⟩ : syracuseStep 338423 = 507635) B507635
theorem B240143 : Blo 223812 240143 := bstep (se 1 (by rfl) ⟨180107, by rfl⟩ : syracuseStep 240143 = 360215) B360215
theorem B338447 : Blo 223812 338447 := bstep (se 1 (by rfl) ⟨253835, by rfl⟩ : syracuseStep 338447 = 507671) B507671
theorem B1944107 : Blo 223812 1944107 := bstep (se 1 (by rfl) ⟨1458080, by rfl⟩ : syracuseStep 1944107 = 2916161) B2916161
theorem B338489 : Blo 223812 338489 := bstep (se 2 (by rfl) ⟨126933, by rfl⟩ : syracuseStep 338489 = 253867) B253867
theorem B961085 : Blo 223812 961085 := bstep (se 3 (by rfl) ⟨180203, by rfl⟩ : syracuseStep 961085 = 360407) B360407
theorem B764477 : Blo 223812 764477 := bstep (se 3 (by rfl) ⟨143339, by rfl⟩ : syracuseStep 764477 = 286679) B286679
theorem B3254849 : Blo 223812 3254849 := bstep (se 2 (by rfl) ⟨1220568, by rfl⟩ : syracuseStep 3254849 = 2441137) B2441137
theorem B338567 : Blo 223812 338567 := bstep (se 1 (by rfl) ⟨253925, by rfl⟩ : syracuseStep 338567 = 507851) B507851
theorem B338603 : Blo 223812 338603 := bstep (se 1 (by rfl) ⟨253952, by rfl⟩ : syracuseStep 338603 = 507905) B507905
theorem B338633 : Blo 223812 338633 := bstep (se 2 (by rfl) ⟨126987, by rfl⟩ : syracuseStep 338633 = 253975) B253975
theorem B338747 : Blo 223812 338747 := bstep (se 1 (by rfl) ⟨254060, by rfl⟩ : syracuseStep 338747 = 508121) B508121
theorem B338807 : Blo 223812 338807 := bstep (se 1 (by rfl) ⟨254105, by rfl⟩ : syracuseStep 338807 = 508211) B508211
theorem B338831 : Blo 223812 338831 := bstep (se 1 (by rfl) ⟨254123, by rfl⟩ : syracuseStep 338831 = 508247) B508247
theorem B338873 : Blo 223812 338873 := bstep (se 2 (by rfl) ⟨127077, by rfl⟩ : syracuseStep 338873 = 254155) B254155
theorem B338951 : Blo 223812 338951 := bstep (se 1 (by rfl) ⟨254213, by rfl⟩ : syracuseStep 338951 = 508427) B508427
theorem B863243 : Blo 223812 863243 := bstep (se 1 (by rfl) ⟨647432, by rfl⟩ : syracuseStep 863243 = 1294865) B1294865
theorem B338987 : Blo 223812 338987 := bstep (se 1 (by rfl) ⟨254240, by rfl⟩ : syracuseStep 338987 = 508481) B508481
theorem B339017 : Blo 223812 339017 := bstep (se 2 (by rfl) ⟨127131, by rfl⟩ : syracuseStep 339017 = 254263) B254263
theorem B240775 : Blo 223812 240775 := bstep (se 1 (by rfl) ⟨180581, by rfl⟩ : syracuseStep 240775 = 361163) B361163
theorem B339131 : Blo 223812 339131 := bstep (se 1 (by rfl) ⟨254348, by rfl⟩ : syracuseStep 339131 = 508697) B508697
theorem B339191 : Blo 223812 339191 := bstep (se 1 (by rfl) ⟨254393, by rfl⟩ : syracuseStep 339191 = 508787) B508787
theorem B339215 : Blo 223812 339215 := bstep (se 1 (by rfl) ⟨254411, by rfl⟩ : syracuseStep 339215 = 508823) B508823
theorem B339257 : Blo 223812 339257 := bstep (se 2 (by rfl) ⟨127221, by rfl⟩ : syracuseStep 339257 = 254443) B254443
theorem B306505 : Blo 223812 306505 := bstep (se 2 (by rfl) ⟨114939, by rfl⟩ : syracuseStep 306505 = 229879) B229879
theorem B568691 : Blo 223812 568691 := bstep (se 1 (by rfl) ⟨426518, by rfl⟩ : syracuseStep 568691 = 853037) B853037
theorem B339335 : Blo 223812 339335 := bstep (se 1 (by rfl) ⟨254501, by rfl⟩ : syracuseStep 339335 = 509003) B509003
theorem B248491405 : Blo 223812 248491405 := bstep (se 3 (by rfl) ⟨46592138, by rfl⟩ : syracuseStep 248491405 = 93184277) B93184277
theorem B339371 : Blo 223812 339371 := bstep (se 1 (by rfl) ⟨254528, by rfl⟩ : syracuseStep 339371 = 509057) B509057
theorem B339401 : Blo 223812 339401 := bstep (se 2 (by rfl) ⟨127275, by rfl⟩ : syracuseStep 339401 = 254551) B254551
theorem B1453571 : Blo 223812 1453571 := bstep (se 1 (by rfl) ⟨1090178, by rfl⟩ : syracuseStep 1453571 = 2180357) B2180357
theorem B339515 : Blo 223812 339515 := bstep (se 1 (by rfl) ⟨254636, by rfl⟩ : syracuseStep 339515 = 509273) B509273
theorem B339575 : Blo 223812 339575 := bstep (se 1 (by rfl) ⟨254681, by rfl⟩ : syracuseStep 339575 = 509363) B509363
theorem B339599 : Blo 223812 339599 := bstep (se 1 (by rfl) ⟨254699, by rfl⟩ : syracuseStep 339599 = 509399) B509399
theorem B339641 : Blo 223812 339641 := bstep (se 2 (by rfl) ⟨127365, by rfl⟩ : syracuseStep 339641 = 254731) B254731
theorem B1289965 : Blo 223812 1289965 := bstep (se 3 (by rfl) ⟨241868, by rfl⟩ : syracuseStep 1289965 = 483737) B483737
theorem B339719 : Blo 223812 339719 := bstep (se 1 (by rfl) ⟨254789, by rfl⟩ : syracuseStep 339719 = 509579) B509579
theorem B503585 : Blo 223812 503585 := bstep (se 2 (by rfl) ⟨188844, by rfl⟩ : syracuseStep 503585 = 377689) B377689
theorem B1093409 : Blo 223812 1093409 := bstep (se 2 (by rfl) ⟨410028, by rfl⟩ : syracuseStep 1093409 = 820057) B820057
theorem B339755 : Blo 223812 339755 := bstep (se 1 (by rfl) ⟨254816, by rfl⟩ : syracuseStep 339755 = 509633) B509633
theorem B339785 : Blo 223812 339785 := bstep (se 2 (by rfl) ⟨127419, by rfl⟩ : syracuseStep 339785 = 254839) B254839
theorem B569207 : Blo 223812 569207 := bstep (se 1 (by rfl) ⟨426905, by rfl⟩ : syracuseStep 569207 = 853811) B853811
theorem B765881 : Blo 223812 765881 := bstep (se 2 (by rfl) ⟨287205, by rfl⟩ : syracuseStep 765881 = 574411) B574411
theorem B339899 : Blo 223812 339899 := bstep (se 1 (by rfl) ⟨254924, by rfl⟩ : syracuseStep 339899 = 509849) B509849
theorem B339959 : Blo 223812 339959 := bstep (se 1 (by rfl) ⟨254969, by rfl⟩ : syracuseStep 339959 = 509939) B509939
theorem B339983 : Blo 223812 339983 := bstep (se 1 (by rfl) ⟨254987, by rfl⟩ : syracuseStep 339983 = 509975) B509975
theorem B340025 : Blo 223812 340025 := bstep (se 2 (by rfl) ⟨127509, by rfl⟩ : syracuseStep 340025 = 255019) B255019
theorem B503927 : Blo 223812 503927 := bstep (se 1 (by rfl) ⟨377945, by rfl⟩ : syracuseStep 503927 = 755891) B755891
theorem B340103 : Blo 223812 340103 := bstep (se 1 (by rfl) ⟨255077, by rfl⟩ : syracuseStep 340103 = 510155) B510155
theorem B340139 : Blo 223812 340139 := bstep (se 1 (by rfl) ⟨255104, by rfl⟩ : syracuseStep 340139 = 510209) B510209
theorem B340169 : Blo 223812 340169 := bstep (se 2 (by rfl) ⟨127563, by rfl⟩ : syracuseStep 340169 = 255127) B255127
theorem B504107 : Blo 223812 504107 := bstep (se 1 (by rfl) ⟨378080, by rfl⟩ : syracuseStep 504107 = 756161) B756161
theorem B340283 : Blo 223812 340283 := bstep (se 1 (by rfl) ⟨255212, by rfl⟩ : syracuseStep 340283 = 510425) B510425
theorem B340343 : Blo 223812 340343 := bstep (se 1 (by rfl) ⟨255257, by rfl⟩ : syracuseStep 340343 = 510515) B510515
theorem B340367 : Blo 223812 340367 := bstep (se 1 (by rfl) ⟨255275, by rfl⟩ : syracuseStep 340367 = 510551) B510551
theorem B340409 : Blo 223812 340409 := bstep (se 2 (by rfl) ⟨127653, by rfl⟩ : syracuseStep 340409 = 255307) B255307
theorem B340487 : Blo 223812 340487 := bstep (se 1 (by rfl) ⟨255365, by rfl⟩ : syracuseStep 340487 = 510731) B510731
theorem B766475 : Blo 223812 766475 := bstep (se 1 (by rfl) ⟨574856, by rfl⟩ : syracuseStep 766475 = 1149713) B1149713
theorem B340523 : Blo 223812 340523 := bstep (se 1 (by rfl) ⟨255392, by rfl⟩ : syracuseStep 340523 = 510785) B510785
theorem B340553 : Blo 223812 340553 := bstep (se 2 (by rfl) ⟨127707, by rfl⟩ : syracuseStep 340553 = 255415) B255415
theorem B766583 : Blo 223812 766583 := bstep (se 1 (by rfl) ⟨574937, by rfl⟩ : syracuseStep 766583 = 1149875) B1149875
theorem B504467 : Blo 223812 504467 := bstep (se 1 (by rfl) ⟨378350, by rfl⟩ : syracuseStep 504467 = 756701) B756701
theorem B340667 : Blo 223812 340667 := bstep (se 1 (by rfl) ⟨255500, by rfl⟩ : syracuseStep 340667 = 511001) B511001
theorem B504521 : Blo 223812 504521 := bstep (se 2 (by rfl) ⟨189195, by rfl⟩ : syracuseStep 504521 = 378391) B378391
theorem B340727 : Blo 223812 340727 := bstep (se 1 (by rfl) ⟨255545, by rfl⟩ : syracuseStep 340727 = 511091) B511091
theorem B340751 : Blo 223812 340751 := bstep (se 1 (by rfl) ⟨255563, by rfl⟩ : syracuseStep 340751 = 511127) B511127
theorem B2568995 : Blo 223812 2568995 := bstep (se 1 (by rfl) ⟨1926746, by rfl⟩ : syracuseStep 2568995 = 3853493) B3853493
theorem B340793 : Blo 223812 340793 := bstep (se 2 (by rfl) ⟨127797, by rfl⟩ : syracuseStep 340793 = 255595) B255595
theorem B570199 : Blo 223812 570199 := bstep (se 1 (by rfl) ⟨427649, by rfl⟩ : syracuseStep 570199 = 855299) B855299
theorem B340871 : Blo 223812 340871 := bstep (se 1 (by rfl) ⟨255653, by rfl⟩ : syracuseStep 340871 = 511307) B511307
theorem B340907 : Blo 223812 340907 := bstep (se 1 (by rfl) ⟨255680, by rfl⟩ : syracuseStep 340907 = 511361) B511361
theorem B340937 : Blo 223812 340937 := bstep (se 2 (by rfl) ⟨127851, by rfl⟩ : syracuseStep 340937 = 255703) B255703
theorem B1913867 : Blo 223812 1913867 := bstep (se 1 (by rfl) ⟨1435400, by rfl⟩ : syracuseStep 1913867 = 2870801) B2870801
theorem B341051 : Blo 223812 341051 := bstep (se 1 (by rfl) ⟨255788, by rfl⟩ : syracuseStep 341051 = 511577) B511577
theorem B341111 : Blo 223812 341111 := bstep (se 1 (by rfl) ⟨255833, by rfl⟩ : syracuseStep 341111 = 511667) B511667
theorem B570503 : Blo 223812 570503 := bstep (se 1 (by rfl) ⟨427877, by rfl⟩ : syracuseStep 570503 = 855755) B855755
theorem B341135 : Blo 223812 341135 := bstep (se 1 (by rfl) ⟨255851, by rfl⟩ : syracuseStep 341135 = 511703) B511703
theorem B341177 : Blo 223812 341177 := bstep (se 2 (by rfl) ⟨127941, by rfl⟩ : syracuseStep 341177 = 255883) B255883
theorem B767177 : Blo 223812 767177 := bstep (se 2 (by rfl) ⟨287691, by rfl⟩ : syracuseStep 767177 = 575383) B575383
theorem B341255 : Blo 223812 341255 := bstep (se 1 (by rfl) ⟨255941, by rfl⟩ : syracuseStep 341255 = 511883) B511883
theorem B570635 : Blo 223812 570635 := bstep (se 1 (by rfl) ⟨427976, by rfl⟩ : syracuseStep 570635 = 855953) B855953
theorem B341291 : Blo 223812 341291 := bstep (se 1 (by rfl) ⟨255968, by rfl⟩ : syracuseStep 341291 = 511937) B511937
theorem B341321 : Blo 223812 341321 := bstep (se 2 (by rfl) ⟨127995, by rfl⟩ : syracuseStep 341321 = 255991) B255991
theorem B505223 : Blo 223812 505223 := bstep (se 1 (by rfl) ⟨378917, by rfl⟩ : syracuseStep 505223 = 757835) B757835
theorem B341435 : Blo 223812 341435 := bstep (se 1 (by rfl) ⟨256076, by rfl⟩ : syracuseStep 341435 = 512153) B512153
theorem B341495 : Blo 223812 341495 := bstep (se 1 (by rfl) ⟨256121, by rfl⟩ : syracuseStep 341495 = 512243) B512243
theorem B341519 : Blo 223812 341519 := bstep (se 1 (by rfl) ⟨256139, by rfl⟩ : syracuseStep 341519 = 512279) B512279
theorem B341561 : Blo 223812 341561 := bstep (se 2 (by rfl) ⟨128085, by rfl⟩ : syracuseStep 341561 = 256171) B256171
theorem B505403 : Blo 223812 505403 := bstep (se 1 (by rfl) ⟨379052, by rfl⟩ : syracuseStep 505403 = 758105) B758105
theorem B767549 : Blo 223812 767549 := bstep (se 3 (by rfl) ⟨143915, by rfl⟩ : syracuseStep 767549 = 287831) B287831
theorem B341639 : Blo 223812 341639 := bstep (se 1 (by rfl) ⟨256229, by rfl⟩ : syracuseStep 341639 = 512459) B512459
theorem B341675 : Blo 223812 341675 := bstep (se 1 (by rfl) ⟨256256, by rfl⟩ : syracuseStep 341675 = 512513) B512513
theorem B1291949 : Blo 223812 1291949 := bstep (se 3 (by rfl) ⟨242240, by rfl⟩ : syracuseStep 1291949 = 484481) B484481
theorem B505529 : Blo 223812 505529 := bstep (se 2 (by rfl) ⟨189573, by rfl⟩ : syracuseStep 505529 = 379147) B379147
theorem B341705 : Blo 223812 341705 := bstep (se 2 (by rfl) ⟨128139, by rfl⟩ : syracuseStep 341705 = 256279) B256279
theorem B571151 : Blo 223812 571151 := bstep (se 1 (by rfl) ⟨428363, by rfl⟩ : syracuseStep 571151 = 856727) B856727
theorem B767879 : Blo 223812 767879 := bstep (se 1 (by rfl) ⟨575909, by rfl⟩ : syracuseStep 767879 = 1151819) B1151819
theorem B571283 : Blo 223812 571283 := bstep (se 1 (by rfl) ⟨428462, by rfl⟩ : syracuseStep 571283 = 856925) B856925
theorem B505871 : Blo 223812 505871 := bstep (se 1 (by rfl) ⟨379403, by rfl⟩ : syracuseStep 505871 = 758807) B758807
theorem B505889 : Blo 223812 505889 := bstep (se 2 (by rfl) ⟨189708, by rfl⟩ : syracuseStep 505889 = 379417) B379417
theorem B768257 : Blo 223812 768257 := bstep (se 2 (by rfl) ⟨288096, by rfl⟩ : syracuseStep 768257 = 576193) B576193
theorem B506231 : Blo 223812 506231 := bstep (se 1 (by rfl) ⟨379673, by rfl⟩ : syracuseStep 506231 = 759347) B759347
theorem B4143581 : Blo 223812 4143581 := bstep (se 3 (by rfl) ⟨776921, by rfl⟩ : syracuseStep 4143581 = 1553843) B1553843
theorem B506411 : Blo 223812 506411 := bstep (se 1 (by rfl) ⟨379808, by rfl⟩ : syracuseStep 506411 = 759617) B759617
theorem B637625 : Blo 223812 637625 := bstep (se 2 (by rfl) ⟨239109, by rfl⟩ : syracuseStep 637625 = 478219) B478219
theorem B965357 : Blo 223812 965357 := bstep (se 3 (by rfl) ⟨181004, by rfl⟩ : syracuseStep 965357 = 362009) B362009
theorem B637739 : Blo 223812 637739 := bstep (se 1 (by rfl) ⟨478304, by rfl⟩ : syracuseStep 637739 = 956609) B956609
theorem B506771 : Blo 223812 506771 := bstep (se 1 (by rfl) ⟨380078, by rfl⟩ : syracuseStep 506771 = 760157) B760157
theorem B244667 : Blo 223812 244667 := bstep (se 1 (by rfl) ⟨183500, by rfl⟩ : syracuseStep 244667 = 367001) B367001
theorem B506825 : Blo 223812 506825 := bstep (se 2 (by rfl) ⟨190059, by rfl⟩ : syracuseStep 506825 = 380119) B380119
theorem B572417 : Blo 223812 572417 := bstep (se 2 (by rfl) ⟨214656, by rfl⟩ : syracuseStep 572417 = 429313) B429313
theorem B605441 : Blo 223812 605441 := bstep (se 2 (by rfl) ⟨227040, by rfl⟩ : syracuseStep 605441 = 454081) B454081
theorem B572791 : Blo 223812 572791 := bstep (se 1 (by rfl) ⟨429593, by rfl⟩ : syracuseStep 572791 = 859187) B859187
theorem B1555847 : Blo 223812 1555847 := bstep (se 1 (by rfl) ⟨1166885, by rfl⟩ : syracuseStep 1555847 = 2333771) B2333771
theorem B507527 : Blo 223812 507527 := bstep (se 1 (by rfl) ⟨380645, by rfl⟩ : syracuseStep 507527 = 761291) B761291
theorem B573227 : Blo 223812 573227 := bstep (se 1 (by rfl) ⟨429920, by rfl⟩ : syracuseStep 573227 = 859841) B859841
theorem B507707 : Blo 223812 507707 := bstep (se 1 (by rfl) ⟨380780, by rfl⟩ : syracuseStep 507707 = 761561) B761561
theorem B638867 : Blo 223812 638867 := bstep (se 1 (by rfl) ⟨479150, by rfl⟩ : syracuseStep 638867 = 958301) B958301
theorem B507833 : Blo 223812 507833 := bstep (se 2 (by rfl) ⟨190437, by rfl⟩ : syracuseStep 507833 = 380875) B380875
theorem B1294339 : Blo 223812 1294339 := bstep (se 1 (by rfl) ⟨970754, by rfl⟩ : syracuseStep 1294339 = 1941509) B1941509
theorem B344137 : Blo 223812 344137 := bstep (se 2 (by rfl) ⟨129051, by rfl⟩ : syracuseStep 344137 = 258103) B258103
theorem B966775 : Blo 223812 966775 := bstep (se 1 (by rfl) ⟨725081, by rfl⟩ : syracuseStep 966775 = 1450163) B1450163
theorem B508175 : Blo 223812 508175 := bstep (se 1 (by rfl) ⟨381131, by rfl⟩ : syracuseStep 508175 = 762263) B762263
theorem B639265 : Blo 223812 639265 := bstep (se 2 (by rfl) ⟨239724, by rfl⟩ : syracuseStep 639265 = 479449) B479449
theorem B508193 : Blo 223812 508193 := bstep (se 2 (by rfl) ⟨190572, by rfl⟩ : syracuseStep 508193 = 381145) B381145
theorem B606599 : Blo 223812 606599 := bstep (se 1 (by rfl) ⟨454949, by rfl⟩ : syracuseStep 606599 = 909899) B909899
theorem B541129 : Blo 223812 541129 := bstep (se 2 (by rfl) ⟨202923, by rfl⟩ : syracuseStep 541129 = 405847) B405847
theorem B574067 : Blo 223812 574067 := bstep (se 1 (by rfl) ⟨430550, by rfl⟩ : syracuseStep 574067 = 861101) B861101
theorem B508535 : Blo 223812 508535 := bstep (se 1 (by rfl) ⟨381401, by rfl⟩ : syracuseStep 508535 = 762803) B762803
theorem B574087 : Blo 223812 574087 := bstep (se 1 (by rfl) ⟨430565, by rfl⟩ : syracuseStep 574087 = 861131) B861131
theorem B508715 : Blo 223812 508715 := bstep (se 1 (by rfl) ⟨381536, by rfl⟩ : syracuseStep 508715 = 763073) B763073
theorem B574361 : Blo 223812 574361 := bstep (se 2 (by rfl) ⟨215385, by rfl⟩ : syracuseStep 574361 = 430771) B430771
theorem B574523 : Blo 223812 574523 := bstep (se 1 (by rfl) ⟨430892, by rfl⟩ : syracuseStep 574523 = 861785) B861785
theorem B509075 : Blo 223812 509075 := bstep (se 1 (by rfl) ⟨381806, by rfl⟩ : syracuseStep 509075 = 763613) B763613
theorem B640153 : Blo 223812 640153 := bstep (se 2 (by rfl) ⟨240057, by rfl⟩ : syracuseStep 640153 = 480115) B480115
theorem B509129 : Blo 223812 509129 := bstep (se 2 (by rfl) ⟨190923, by rfl⟩ : syracuseStep 509129 = 381847) B381847
theorem B574735 : Blo 223812 574735 := bstep (se 1 (by rfl) ⟨431051, by rfl⟩ : syracuseStep 574735 = 862103) B862103
theorem B738575 : Blo 223812 738575 := bstep (se 1 (by rfl) ⟨553931, by rfl⟩ : syracuseStep 738575 = 1107863) B1107863
theorem B607517 : Blo 223812 607517 := bstep (se 3 (by rfl) ⟨113909, by rfl⟩ : syracuseStep 607517 = 227819) B227819
theorem B1918241 : Blo 223812 1918241 := bstep (se 2 (by rfl) ⟨719340, by rfl⟩ : syracuseStep 1918241 = 1438681) B1438681
theorem B378155 : Blo 223812 378155 := bstep (se 1 (by rfl) ⟨283616, by rfl⟩ : syracuseStep 378155 = 567233) B567233
theorem B640541 : Blo 223812 640541 := bstep (se 3 (by rfl) ⟨120101, by rfl⟩ : syracuseStep 640541 = 240203) B240203
theorem B575009 : Blo 223812 575009 := bstep (se 2 (by rfl) ⟨215628, by rfl⟩ : syracuseStep 575009 = 431257) B431257
theorem B378553 : Blo 223812 378553 := bstep (se 2 (by rfl) ⟨141957, by rfl⟩ : syracuseStep 378553 = 283915) B283915
theorem B509831 : Blo 223812 509831 := bstep (se 1 (by rfl) ⟨382373, by rfl⟩ : syracuseStep 509831 = 764747) B764747
theorem B4638617 : Blo 223812 4638617 := bstep (se 2 (by rfl) ⟨1739481, by rfl⟩ : syracuseStep 4638617 = 3478963) B3478963
theorem B510011 : Blo 223812 510011 := bstep (se 1 (by rfl) ⟨382508, by rfl⟩ : syracuseStep 510011 = 765017) B765017
theorem B510137 : Blo 223812 510137 := bstep (se 2 (by rfl) ⟨191301, by rfl⟩ : syracuseStep 510137 = 382603) B382603
theorem B1296755 : Blo 223812 1296755 := bstep (se 1 (by rfl) ⟨972566, by rfl⟩ : syracuseStep 1296755 = 1945133) B1945133
theorem B379255 : Blo 223812 379255 := bstep (se 1 (by rfl) ⟨284441, by rfl⟩ : syracuseStep 379255 = 568883) B568883
theorem B576011 : Blo 223812 576011 := bstep (se 1 (by rfl) ⟨432008, by rfl⟩ : syracuseStep 576011 = 864017) B864017
theorem B510479 : Blo 223812 510479 := bstep (se 1 (by rfl) ⟨382859, by rfl⟩ : syracuseStep 510479 = 765719) B765719
theorem B510497 : Blo 223812 510497 := bstep (se 2 (by rfl) ⟨191436, by rfl⟩ : syracuseStep 510497 = 382873) B382873
theorem B379451 : Blo 223812 379451 := bstep (se 1 (by rfl) ⟨284588, by rfl⟩ : syracuseStep 379451 = 569177) B569177
theorem B510839 : Blo 223812 510839 := bstep (se 1 (by rfl) ⟨383129, by rfl⟩ : syracuseStep 510839 = 766259) B766259
theorem B478099 : Blo 223812 478099 := bstep (se 1 (by rfl) ⟨358574, by rfl⟩ : syracuseStep 478099 = 717149) B717149
theorem B379849 : Blo 223812 379849 := bstep (se 2 (by rfl) ⟨142443, by rfl⟩ : syracuseStep 379849 = 284887) B284887
theorem B2608075 : Blo 223812 2608075 := bstep (se 1 (by rfl) ⟨1956056, by rfl⟩ : syracuseStep 2608075 = 3912113) B3912113
theorem B511019 : Blo 223812 511019 := bstep (se 1 (by rfl) ⟨383264, by rfl⟩ : syracuseStep 511019 = 766529) B766529
theorem B2182277 : Blo 223812 2182277 := bstep (se 4 (by rfl) ⟨204588, by rfl⟩ : syracuseStep 2182277 = 409177) B409177
theorem B773321 : Blo 223812 773321 := bstep (se 2 (by rfl) ⟨289995, by rfl⟩ : syracuseStep 773321 = 579991) B579991
theorem B609551 : Blo 223812 609551 := bstep (se 1 (by rfl) ⟨457163, by rfl⟩ : syracuseStep 609551 = 914327) B914327
theorem B511379 : Blo 223812 511379 := bstep (se 1 (by rfl) ⟨383534, by rfl⟩ : syracuseStep 511379 = 767069) B767069
theorem B511433 : Blo 223812 511433 := bstep (se 2 (by rfl) ⟨191787, by rfl⟩ : syracuseStep 511433 = 383575) B383575
theorem B380551 : Blo 223812 380551 := bstep (se 1 (by rfl) ⟨285413, by rfl⟩ : syracuseStep 380551 = 570827) B570827
theorem B8212427 : Blo 223812 8212427 := bstep (se 1 (by rfl) ⟨6159320, by rfl⟩ : syracuseStep 8212427 = 12318641) B12318641
theorem B643115 : Blo 223812 643115 := bstep (se 1 (by rfl) ⟨482336, by rfl⟩ : syracuseStep 643115 = 964673) B964673
theorem B512135 : Blo 223812 512135 := bstep (se 1 (by rfl) ⟨384101, by rfl⟩ : syracuseStep 512135 = 768203) B768203
theorem B381199 : Blo 223812 381199 := bstep (se 1 (by rfl) ⟨285899, by rfl⟩ : syracuseStep 381199 = 571799) B571799
theorem B512315 : Blo 223812 512315 := bstep (se 1 (by rfl) ⟨384236, by rfl⟩ : syracuseStep 512315 = 768473) B768473
theorem B774515 : Blo 223812 774515 := bstep (se 1 (by rfl) ⟨580886, by rfl⟩ : syracuseStep 774515 = 1161773) B1161773
theorem B512441 : Blo 223812 512441 := bstep (se 2 (by rfl) ⟨192165, by rfl⟩ : syracuseStep 512441 = 384331) B384331
theorem B2871773 : Blo 223812 2871773 := bstep (se 3 (by rfl) ⟨538457, by rfl⟩ : syracuseStep 2871773 = 1076915) B1076915
theorem B1135133 : Blo 223812 1135133 := bstep (se 3 (by rfl) ⟨212837, by rfl⟩ : syracuseStep 1135133 = 425675) B425675
theorem B479945 : Blo 223812 479945 := bstep (se 2 (by rfl) ⟨179979, by rfl⟩ : syracuseStep 479945 = 359959) B359959
theorem B381739 : Blo 223812 381739 := bstep (se 1 (by rfl) ⟨286304, by rfl⟩ : syracuseStep 381739 = 572609) B572609
theorem B3068761 : Blo 223812 3068761 := bstep (se 2 (by rfl) ⟨1150785, by rfl⟩ : syracuseStep 3068761 = 2301571) B2301571
theorem B1725299 : Blo 223812 1725299 := bstep (se 1 (by rfl) ⟨1293974, by rfl⟩ : syracuseStep 1725299 = 2587949) B2587949
theorem B1364921 : Blo 223812 1364921 := bstep (se 2 (by rfl) ⟨511845, by rfl⟩ : syracuseStep 1364921 = 1023691) B1023691
theorem B381881 : Blo 223812 381881 := bstep (se 2 (by rfl) ⟨143205, by rfl⟩ : syracuseStep 381881 = 286411) B286411
theorem B1135619 : Blo 223812 1135619 := bstep (se 1 (by rfl) ⟨851714, by rfl⟩ : syracuseStep 1135619 = 1703429) B1703429
theorem B808003 : Blo 223812 808003 := bstep (se 1 (by rfl) ⟨606002, by rfl⟩ : syracuseStep 808003 = 1212005) B1212005
theorem B283819 : Blo 223812 283819 := bstep (se 1 (by rfl) ⟨212864, by rfl⟩ : syracuseStep 283819 = 425729) B425729
theorem B1168849 : Blo 223812 1168849 := bstep (se 2 (by rfl) ⟨438318, by rfl⟩ : syracuseStep 1168849 = 876637) B876637
theorem B382583 : Blo 223812 382583 := bstep (se 1 (by rfl) ⟨286937, by rfl⟩ : syracuseStep 382583 = 573875) B573875
theorem B644755 : Blo 223812 644755 := bstep (se 1 (by rfl) ⟨483566, by rfl⟩ : syracuseStep 644755 = 967133) B967133
theorem B611993 : Blo 223812 611993 := bstep (se 2 (by rfl) ⟨229497, by rfl⟩ : syracuseStep 611993 = 458995) B458995
theorem B480953 : Blo 223812 480953 := bstep (se 2 (by rfl) ⟨180357, by rfl⟩ : syracuseStep 480953 = 360715) B360715
theorem B349967 : Blo 223812 349967 := bstep (se 1 (by rfl) ⟨262475, by rfl⟩ : syracuseStep 349967 = 524951) B524951
theorem B1038233 : Blo 223812 1038233 := bstep (se 2 (by rfl) ⟨389337, by rfl⟩ : syracuseStep 1038233 = 778675) B778675
theorem B481295 : Blo 223812 481295 := bstep (se 1 (by rfl) ⟨360971, by rfl⟩ : syracuseStep 481295 = 721943) B721943
theorem B383035 : Blo 223812 383035 := bstep (se 1 (by rfl) ⟨287276, by rfl⟩ : syracuseStep 383035 = 574553) B574553
theorem B284791 : Blo 223812 284791 := bstep (se 1 (by rfl) ⟨213593, by rfl⟩ : syracuseStep 284791 = 427187) B427187
theorem B579737 : Blo 223812 579737 := bstep (se 2 (by rfl) ⟨217401, by rfl⟩ : syracuseStep 579737 = 434803) B434803
theorem B383177 : Blo 223812 383177 := bstep (se 2 (by rfl) ⟨143691, by rfl⟩ : syracuseStep 383177 = 287383) B287383
theorem B252175 : Blo 223812 252175 := bstep (se 1 (by rfl) ⟨189131, by rfl⟩ : syracuseStep 252175 = 378263) B378263
theorem B285115 : Blo 223812 285115 := bstep (se 1 (by rfl) ⟨213836, by rfl⟩ : syracuseStep 285115 = 427673) B427673
theorem B1137239 : Blo 223812 1137239 := bstep (se 1 (by rfl) ⟨852929, by rfl⟩ : syracuseStep 1137239 = 1705859) B1705859
theorem B2579201 : Blo 223812 2579201 := bstep (se 2 (by rfl) ⟨967200, by rfl⟩ : syracuseStep 2579201 = 1934401) B1934401
theorem B252679 : Blo 223812 252679 := bstep (se 1 (by rfl) ⟨189509, by rfl⟩ : syracuseStep 252679 = 379019) B379019
theorem B5233423 : Blo 223812 5233423 := bstep (se 1 (by rfl) ⟨3925067, by rfl⟩ : syracuseStep 5233423 = 7850135) B7850135
theorem B482183 : Blo 223812 482183 := bstep (se 1 (by rfl) ⟨361637, by rfl⟩ : syracuseStep 482183 = 723275) B723275
theorem B383879 : Blo 223812 383879 := bstep (se 1 (by rfl) ⟨287909, by rfl⟩ : syracuseStep 383879 = 575819) B575819
theorem B252859 : Blo 223812 252859 := bstep (se 1 (by rfl) ⟨189644, by rfl⟩ : syracuseStep 252859 = 379289) B379289
theorem B1137725 : Blo 223812 1137725 := bstep (se 3 (by rfl) ⟨213323, by rfl⟩ : syracuseStep 1137725 = 426647) B426647
theorem B482593 : Blo 223812 482593 := bstep (se 2 (by rfl) ⟨180972, by rfl⟩ : syracuseStep 482593 = 361945) B361945
theorem B646487 : Blo 223812 646487 := bstep (se 1 (by rfl) ⟨484865, by rfl⟩ : syracuseStep 646487 = 969731) B969731
theorem B286087 : Blo 223812 286087 := bstep (se 1 (by rfl) ⟨214565, by rfl⟩ : syracuseStep 286087 = 429131) B429131
theorem B253327 : Blo 223812 253327 := bstep (se 1 (by rfl) ⟨189995, by rfl⟩ : syracuseStep 253327 = 379991) B379991
theorem B318983 : Blo 223812 318983 := bstep (se 1 (by rfl) ⟨239237, by rfl⟩ : syracuseStep 318983 = 478475) B478475
theorem B482849 : Blo 223812 482849 := bstep (se 2 (by rfl) ⟨181068, by rfl⟩ : syracuseStep 482849 = 362137) B362137
theorem B482935 : Blo 223812 482935 := bstep (se 1 (by rfl) ⟨362201, by rfl⟩ : syracuseStep 482935 = 724403) B724403
theorem B2612915 : Blo 223812 2612915 := bstep (se 1 (by rfl) ⟨1959686, by rfl⟩ : syracuseStep 2612915 = 3919373) B3919373
theorem B319177 : Blo 223812 319177 := bstep (se 2 (by rfl) ⟨119691, by rfl⟩ : syracuseStep 319177 = 239383) B239383
theorem B286507 : Blo 223812 286507 := bstep (se 1 (by rfl) ⟨214880, by rfl⟩ : syracuseStep 286507 = 429761) B429761
theorem B253831 : Blo 223812 253831 := bstep (se 1 (by rfl) ⟨190373, by rfl⟩ : syracuseStep 253831 = 380747) B380747
theorem B286735 : Blo 223812 286735 := bstep (se 1 (by rfl) ⟨215051, by rfl⟩ : syracuseStep 286735 = 430103) B430103
theorem B254011 : Blo 223812 254011 := bstep (se 1 (by rfl) ⟨190508, by rfl⟩ : syracuseStep 254011 = 381017) B381017
theorem B319735 : Blo 223812 319735 := bstep (se 1 (by rfl) ⟨239801, by rfl⟩ : syracuseStep 319735 = 479603) B479603
theorem B254479 : Blo 223812 254479 := bstep (se 1 (by rfl) ⟨190859, by rfl⟩ : syracuseStep 254479 = 381719) B381719
theorem B3236395 : Blo 223812 3236395 := bstep (se 1 (by rfl) ⟨2427296, by rfl⟩ : syracuseStep 3236395 = 4854593) B4854593
theorem B1532609 : Blo 223812 1532609 := bstep (se 2 (by rfl) ⟨574728, by rfl⟩ : syracuseStep 1532609 = 1149457) B1149457
theorem B287479 : Blo 223812 287479 := bstep (se 1 (by rfl) ⟨215609, by rfl⟩ : syracuseStep 287479 = 431219) B431219
theorem B1467173 : Blo 223812 1467173 := bstep (se 4 (by rfl) ⟨137547, by rfl⟩ : syracuseStep 1467173 = 275095) B275095
theorem B1139507 : Blo 223812 1139507 := bstep (se 1 (by rfl) ⟨854630, by rfl⟩ : syracuseStep 1139507 = 1709261) B1709261
theorem B648071 : Blo 223812 648071 := bstep (se 1 (by rfl) ⟨486053, by rfl⟩ : syracuseStep 648071 = 972107) B972107
theorem B320441 : Blo 223812 320441 := bstep (se 2 (by rfl) ⟨120165, by rfl⟩ : syracuseStep 320441 = 240331) B240331
theorem B254983 : Blo 223812 254983 := bstep (se 1 (by rfl) ⟨191237, by rfl⟩ : syracuseStep 254983 = 382475) B382475
theorem B680975 : Blo 223812 680975 := bstep (se 1 (by rfl) ⟨510731, by rfl⟩ : syracuseStep 680975 = 1021463) B1021463
theorem B320527 : Blo 223812 320527 := bstep (se 1 (by rfl) ⟨240395, by rfl⟩ : syracuseStep 320527 = 480791) B480791
theorem B320555 : Blo 223812 320555 := bstep (se 1 (by rfl) ⟨240416, by rfl⟩ : syracuseStep 320555 = 480833) B480833
theorem B287803 : Blo 223812 287803 := bstep (se 1 (by rfl) ⟨215852, by rfl⟩ : syracuseStep 287803 = 431705) B431705
theorem B812099 : Blo 223812 812099 := bstep (se 1 (by rfl) ⟨609074, by rfl⟩ : syracuseStep 812099 = 1218149) B1218149
theorem B1139831 : Blo 223812 1139831 := bstep (se 1 (by rfl) ⟨854873, by rfl⟩ : syracuseStep 1139831 = 1709747) B1709747
theorem B255163 : Blo 223812 255163 := bstep (se 1 (by rfl) ⟨191372, by rfl⟩ : syracuseStep 255163 = 382745) B382745
theorem B648719 : Blo 223812 648719 := bstep (se 1 (by rfl) ⟨486539, by rfl⟩ : syracuseStep 648719 = 973079) B973079
theorem B288299 : Blo 223812 288299 := bstep (se 1 (by rfl) ⟨216224, by rfl⟩ : syracuseStep 288299 = 432449) B432449
theorem B1402429 : Blo 223812 1402429 := bstep (se 3 (by rfl) ⟨262955, by rfl⟩ : syracuseStep 1402429 = 525911) B525911
theorem B2582117 : Blo 223812 2582117 := bstep (se 4 (by rfl) ⟨242073, by rfl⟩ : syracuseStep 2582117 = 484147) B484147
theorem B681587 : Blo 223812 681587 := bstep (se 1 (by rfl) ⟨511190, by rfl⟩ : syracuseStep 681587 = 1022381) B1022381
theorem B255631 : Blo 223812 255631 := bstep (se 1 (by rfl) ⟨191723, by rfl⟩ : syracuseStep 255631 = 383447) B383447
theorem B1140803 : Blo 223812 1140803 := bstep (se 1 (by rfl) ⟨855602, by rfl⟩ : syracuseStep 1140803 = 1711205) B1711205
theorem B256135 : Blo 223812 256135 := bstep (se 1 (by rfl) ⟨192101, by rfl⟩ : syracuseStep 256135 = 384203) B384203
theorem B1436039 : Blo 223812 1436039 := bstep (se 1 (by rfl) ⟨1077029, by rfl⟩ : syracuseStep 1436039 = 2154059) B2154059
theorem B1141127 : Blo 223812 1141127 := bstep (se 1 (by rfl) ⟨855845, by rfl⟩ : syracuseStep 1141127 = 1711691) B1711691
theorem B1075799 : Blo 223812 1075799 := bstep (se 1 (by rfl) ⟨806849, by rfl⟩ : syracuseStep 1075799 = 1613699) B1613699
theorem B813655 : Blo 223812 813655 := bstep (se 1 (by rfl) ⟨610241, by rfl⟩ : syracuseStep 813655 = 1220483) B1220483
theorem B223879 : Blo 223812 223879 := bstep (se 1 (by rfl) ⟨167909, by rfl⟩ : syracuseStep 223879 = 335819) B335819
theorem B223887 : Blo 223812 223887 := bstep (se 1 (by rfl) ⟨167915, by rfl⟩ : syracuseStep 223887 = 335831) B335831
theorem B223931 : Blo 223812 223931 := bstep (se 1 (by rfl) ⟨167948, by rfl⟩ : syracuseStep 223931 = 335897) B335897
theorem B813769 : Blo 223812 813769 := bstep (se 2 (by rfl) ⟨305163, by rfl⟩ : syracuseStep 813769 = 610327) B610327
theorem B224007 : Blo 223812 224007 := bstep (se 1 (by rfl) ⟨168005, by rfl⟩ : syracuseStep 224007 = 336011) B336011
theorem B224015 : Blo 223812 224015 := bstep (se 1 (by rfl) ⟨168011, by rfl⟩ : syracuseStep 224015 = 336023) B336023
theorem B224059 : Blo 223812 224059 := bstep (se 1 (by rfl) ⟨168044, by rfl⟩ : syracuseStep 224059 = 336089) B336089
theorem B224135 : Blo 223812 224135 := bstep (se 1 (by rfl) ⟨168101, by rfl⟩ : syracuseStep 224135 = 336203) B336203
theorem B224143 : Blo 223812 224143 := bstep (se 1 (by rfl) ⟨168107, by rfl⟩ : syracuseStep 224143 = 336215) B336215
theorem B2911139 : Blo 223812 2911139 := bstep (se 1 (by rfl) ⟨2183354, by rfl⟩ : syracuseStep 2911139 = 4366709) B4366709
theorem B912313 : Blo 223812 912313 := bstep (se 2 (by rfl) ⟨342117, by rfl⟩ : syracuseStep 912313 = 684235) B684235
theorem B224187 : Blo 223812 224187 := bstep (se 1 (by rfl) ⟨168140, by rfl⟩ : syracuseStep 224187 = 336281) B336281
theorem B224263 : Blo 223812 224263 := bstep (se 1 (by rfl) ⟨168197, by rfl⟩ : syracuseStep 224263 = 336395) B336395
theorem B224271 : Blo 223812 224271 := bstep (se 1 (by rfl) ⟨168203, by rfl⟩ : syracuseStep 224271 = 336407) B336407
theorem B2583575 : Blo 223812 2583575 := bstep (se 1 (by rfl) ⟨1937681, by rfl⟩ : syracuseStep 2583575 = 3875363) B3875363
theorem B650273 : Blo 223812 650273 := bstep (se 2 (by rfl) ⟨243852, by rfl⟩ : syracuseStep 650273 = 487705) B487705
theorem B224315 : Blo 223812 224315 := bstep (se 1 (by rfl) ⟨168236, by rfl⟩ : syracuseStep 224315 = 336473) B336473
theorem B224391 : Blo 223812 224391 := bstep (se 1 (by rfl) ⟨168293, by rfl⟩ : syracuseStep 224391 = 336587) B336587
theorem B224399 : Blo 223812 224399 := bstep (se 1 (by rfl) ⟨168299, by rfl⟩ : syracuseStep 224399 = 336599) B336599
theorem B224443 : Blo 223812 224443 := bstep (se 1 (by rfl) ⟨168332, by rfl⟩ : syracuseStep 224443 = 336665) B336665
theorem B224519 : Blo 223812 224519 := bstep (se 1 (by rfl) ⟨168389, by rfl⟩ : syracuseStep 224519 = 336779) B336779
theorem B224527 : Blo 223812 224527 := bstep (se 1 (by rfl) ⟨168395, by rfl⟩ : syracuseStep 224527 = 336791) B336791
theorem B224571 : Blo 223812 224571 := bstep (se 1 (by rfl) ⟨168428, by rfl⟩ : syracuseStep 224571 = 336857) B336857
theorem B224647 : Blo 223812 224647 := bstep (se 1 (by rfl) ⟨168485, by rfl⟩ : syracuseStep 224647 = 336971) B336971
theorem B224655 : Blo 223812 224655 := bstep (se 1 (by rfl) ⟨168491, by rfl⟩ : syracuseStep 224655 = 336983) B336983
theorem B224699 : Blo 223812 224699 := bstep (se 1 (by rfl) ⟨168524, by rfl⟩ : syracuseStep 224699 = 337049) B337049
theorem B224775 : Blo 223812 224775 := bstep (se 1 (by rfl) ⟨168581, by rfl⟩ : syracuseStep 224775 = 337163) B337163
theorem B1371659 : Blo 223812 1371659 := bstep (se 1 (by rfl) ⟨1028744, by rfl⟩ : syracuseStep 1371659 = 2057489) B2057489
theorem B224783 : Blo 223812 224783 := bstep (se 1 (by rfl) ⟨168587, by rfl⟩ : syracuseStep 224783 = 337175) B337175
theorem B224827 : Blo 223812 224827 := bstep (se 1 (by rfl) ⟨168620, by rfl⟩ : syracuseStep 224827 = 337241) B337241
theorem B224903 : Blo 223812 224903 := bstep (se 1 (by rfl) ⟨168677, by rfl⟩ : syracuseStep 224903 = 337355) B337355
theorem B224911 : Blo 223812 224911 := bstep (se 1 (by rfl) ⟨168683, by rfl⟩ : syracuseStep 224911 = 337367) B337367
theorem B224955 : Blo 223812 224955 := bstep (se 1 (by rfl) ⟨168716, by rfl⟩ : syracuseStep 224955 = 337433) B337433
theorem B225031 : Blo 223812 225031 := bstep (se 1 (by rfl) ⟨168773, by rfl⟩ : syracuseStep 225031 = 337547) B337547
theorem B225039 : Blo 223812 225039 := bstep (se 1 (by rfl) ⟨168779, by rfl⟩ : syracuseStep 225039 = 337559) B337559
theorem B225083 : Blo 223812 225083 := bstep (se 1 (by rfl) ⟨168812, by rfl⟩ : syracuseStep 225083 = 337625) B337625
theorem B225159 : Blo 223812 225159 := bstep (se 1 (by rfl) ⟨168869, by rfl⟩ : syracuseStep 225159 = 337739) B337739
theorem B225167 : Blo 223812 225167 := bstep (se 1 (by rfl) ⟨168875, by rfl⟩ : syracuseStep 225167 = 337751) B337751
theorem B323471 : Blo 223812 323471 := bstep (se 1 (by rfl) ⟨242603, by rfl⟩ : syracuseStep 323471 = 485207) B485207
theorem B225211 : Blo 223812 225211 := bstep (se 1 (by rfl) ⟨168908, by rfl⟩ : syracuseStep 225211 = 337817) B337817
theorem B225287 : Blo 223812 225287 := bstep (se 1 (by rfl) ⟨168965, by rfl⟩ : syracuseStep 225287 = 337931) B337931
theorem B225295 : Blo 223812 225295 := bstep (se 1 (by rfl) ⟨168971, by rfl⟩ : syracuseStep 225295 = 337943) B337943
theorem B225339 : Blo 223812 225339 := bstep (se 1 (by rfl) ⟨169004, by rfl⟩ : syracuseStep 225339 = 338009) B338009
theorem B225415 : Blo 223812 225415 := bstep (se 1 (by rfl) ⟨169061, by rfl⟩ : syracuseStep 225415 = 338123) B338123
theorem B225423 : Blo 223812 225423 := bstep (se 1 (by rfl) ⟨169067, by rfl⟩ : syracuseStep 225423 = 338135) B338135
theorem B225467 : Blo 223812 225467 := bstep (se 1 (by rfl) ⟨169100, by rfl⟩ : syracuseStep 225467 = 338201) B338201
theorem B225543 : Blo 223812 225543 := bstep (se 1 (by rfl) ⟨169157, by rfl⟩ : syracuseStep 225543 = 338315) B338315
theorem B225551 : Blo 223812 225551 := bstep (se 1 (by rfl) ⟨169163, by rfl⟩ : syracuseStep 225551 = 338327) B338327
theorem B225595 : Blo 223812 225595 := bstep (se 1 (by rfl) ⟨169196, by rfl⟩ : syracuseStep 225595 = 338393) B338393
theorem B225671 : Blo 223812 225671 := bstep (se 1 (by rfl) ⟨169253, by rfl⟩ : syracuseStep 225671 = 338507) B338507
theorem B225679 : Blo 223812 225679 := bstep (se 1 (by rfl) ⟨169259, by rfl⟩ : syracuseStep 225679 = 338519) B338519
theorem B225723 : Blo 223812 225723 := bstep (se 1 (by rfl) ⟨169292, by rfl⟩ : syracuseStep 225723 = 338585) B338585
theorem B225799 : Blo 223812 225799 := bstep (se 1 (by rfl) ⟨169349, by rfl⟩ : syracuseStep 225799 = 338699) B338699
theorem B225807 : Blo 223812 225807 := bstep (se 1 (by rfl) ⟨169355, by rfl⟩ : syracuseStep 225807 = 338711) B338711
theorem B225851 : Blo 223812 225851 := bstep (se 1 (by rfl) ⟨169388, by rfl⟩ : syracuseStep 225851 = 338777) B338777
theorem B225927 : Blo 223812 225927 := bstep (se 1 (by rfl) ⟨169445, by rfl⟩ : syracuseStep 225927 = 338891) B338891
theorem B225935 : Blo 223812 225935 := bstep (se 1 (by rfl) ⟨169451, by rfl⟩ : syracuseStep 225935 = 338903) B338903
theorem B225979 : Blo 223812 225979 := bstep (se 1 (by rfl) ⟨169484, by rfl⟩ : syracuseStep 225979 = 338969) B338969
theorem B226055 : Blo 223812 226055 := bstep (se 1 (by rfl) ⟨169541, by rfl⟩ : syracuseStep 226055 = 339083) B339083
theorem B226063 : Blo 223812 226063 := bstep (se 1 (by rfl) ⟨169547, by rfl⟩ : syracuseStep 226063 = 339095) B339095
theorem B226107 : Blo 223812 226107 := bstep (se 1 (by rfl) ⟨169580, by rfl⟩ : syracuseStep 226107 = 339161) B339161
theorem B226183 : Blo 223812 226183 := bstep (se 1 (by rfl) ⟨169637, by rfl⟩ : syracuseStep 226183 = 339275) B339275
theorem B226191 : Blo 223812 226191 := bstep (se 1 (by rfl) ⟨169643, by rfl⟩ : syracuseStep 226191 = 339287) B339287
theorem B226235 : Blo 223812 226235 := bstep (se 1 (by rfl) ⟨169676, by rfl⟩ : syracuseStep 226235 = 339353) B339353
theorem B226311 : Blo 223812 226311 := bstep (se 1 (by rfl) ⟨169733, by rfl⟩ : syracuseStep 226311 = 339467) B339467
theorem B226319 : Blo 223812 226319 := bstep (se 1 (by rfl) ⟨169739, by rfl⟩ : syracuseStep 226319 = 339479) B339479
theorem B226363 : Blo 223812 226363 := bstep (se 1 (by rfl) ⟨169772, by rfl⟩ : syracuseStep 226363 = 339545) B339545
theorem B1930301 : Blo 223812 1930301 := bstep (se 3 (by rfl) ⟨361931, by rfl⟩ : syracuseStep 1930301 = 723863) B723863
theorem B226439 : Blo 223812 226439 := bstep (se 1 (by rfl) ⟨169829, by rfl⟩ : syracuseStep 226439 = 339659) B339659
theorem B226447 : Blo 223812 226447 := bstep (se 1 (by rfl) ⟨169835, by rfl⟩ : syracuseStep 226447 = 339671) B339671
theorem B226491 : Blo 223812 226491 := bstep (se 1 (by rfl) ⟨169868, by rfl⟩ : syracuseStep 226491 = 339737) B339737
theorem B226567 : Blo 223812 226567 := bstep (se 1 (by rfl) ⟨169925, by rfl⟩ : syracuseStep 226567 = 339851) B339851
theorem B226575 : Blo 223812 226575 := bstep (se 1 (by rfl) ⟨169931, by rfl⟩ : syracuseStep 226575 = 339863) B339863
theorem B226619 : Blo 223812 226619 := bstep (se 1 (by rfl) ⟨169964, by rfl⟩ : syracuseStep 226619 = 339929) B339929
theorem B226695 : Blo 223812 226695 := bstep (se 1 (by rfl) ⟨170021, by rfl⟩ : syracuseStep 226695 = 340043) B340043
theorem B226703 : Blo 223812 226703 := bstep (se 1 (by rfl) ⟨170027, by rfl⟩ : syracuseStep 226703 = 340055) B340055
theorem B226747 : Blo 223812 226747 := bstep (se 1 (by rfl) ⟨170060, by rfl⟩ : syracuseStep 226747 = 340121) B340121
theorem B259591 : Blo 223812 259591 := bstep (se 1 (by rfl) ⟨194693, by rfl⟩ : syracuseStep 259591 = 389387) B389387
theorem B226823 : Blo 223812 226823 := bstep (se 1 (by rfl) ⟨170117, by rfl⟩ : syracuseStep 226823 = 340235) B340235
theorem B226831 : Blo 223812 226831 := bstep (se 1 (by rfl) ⟨170123, by rfl⟩ : syracuseStep 226831 = 340247) B340247
theorem B16774685 : Blo 223812 16774685 := bstep (se 3 (by rfl) ⟨3145253, by rfl⟩ : syracuseStep 16774685 = 6290507) B6290507
theorem B718379 : Blo 223812 718379 := bstep (se 1 (by rfl) ⟨538784, by rfl⟩ : syracuseStep 718379 = 1077569) B1077569
theorem B226875 : Blo 223812 226875 := bstep (se 1 (by rfl) ⟨170156, by rfl⟩ : syracuseStep 226875 = 340313) B340313
theorem B1308221 : Blo 223812 1308221 := bstep (se 3 (by rfl) ⟨245291, by rfl⟩ : syracuseStep 1308221 = 490583) B490583
theorem B226951 : Blo 223812 226951 := bstep (se 1 (by rfl) ⟨170213, by rfl⟩ : syracuseStep 226951 = 340427) B340427
theorem B226959 : Blo 223812 226959 := bstep (se 1 (by rfl) ⟨170219, by rfl⟩ : syracuseStep 226959 = 340439) B340439
theorem B227003 : Blo 223812 227003 := bstep (se 1 (by rfl) ⟨170252, by rfl⟩ : syracuseStep 227003 = 340505) B340505
theorem B1210085 : Blo 223812 1210085 := bstep (se 4 (by rfl) ⟨113445, by rfl⟩ : syracuseStep 1210085 = 226891) B226891
theorem B227079 : Blo 223812 227079 := bstep (se 1 (by rfl) ⟨170309, by rfl⟩ : syracuseStep 227079 = 340619) B340619
theorem B227087 : Blo 223812 227087 := bstep (se 1 (by rfl) ⟨170315, by rfl⟩ : syracuseStep 227087 = 340631) B340631
theorem B1439525 : Blo 223812 1439525 := bstep (se 4 (by rfl) ⟨134955, by rfl⟩ : syracuseStep 1439525 = 269911) B269911
theorem B227131 : Blo 223812 227131 := bstep (se 1 (by rfl) ⟨170348, by rfl⟩ : syracuseStep 227131 = 340697) B340697
theorem B1144691 : Blo 223812 1144691 := bstep (se 1 (by rfl) ⟨858518, by rfl⟩ : syracuseStep 1144691 = 1717037) B1717037
theorem B980851 : Blo 223812 980851 := bstep (se 1 (by rfl) ⟨735638, by rfl⟩ : syracuseStep 980851 = 1471277) B1471277
theorem B227207 : Blo 223812 227207 := bstep (se 1 (by rfl) ⟨170405, by rfl⟩ : syracuseStep 227207 = 340811) B340811
theorem B227215 : Blo 223812 227215 := bstep (se 1 (by rfl) ⟨170411, by rfl⟩ : syracuseStep 227215 = 340823) B340823
theorem B5339033 : Blo 223812 5339033 := bstep (se 2 (by rfl) ⟨2002137, by rfl⟩ : syracuseStep 5339033 = 4004275) B4004275
theorem B1832867 : Blo 223812 1832867 := bstep (se 1 (by rfl) ⟨1374650, by rfl⟩ : syracuseStep 1832867 = 2749301) B2749301
theorem B227259 : Blo 223812 227259 := bstep (se 1 (by rfl) ⟨170444, by rfl⟩ : syracuseStep 227259 = 340889) B340889
theorem B325577 : Blo 223812 325577 := bstep (se 2 (by rfl) ⟨122091, by rfl⟩ : syracuseStep 325577 = 244183) B244183
theorem B227335 : Blo 223812 227335 := bstep (se 1 (by rfl) ⟨170501, by rfl⟩ : syracuseStep 227335 = 341003) B341003
theorem B227343 : Blo 223812 227343 := bstep (se 1 (by rfl) ⟨170507, by rfl⟩ : syracuseStep 227343 = 341015) B341015
theorem B227387 : Blo 223812 227387 := bstep (se 1 (by rfl) ⟨170540, by rfl⟩ : syracuseStep 227387 = 341081) B341081
theorem B227463 : Blo 223812 227463 := bstep (se 1 (by rfl) ⟨170597, by rfl⟩ : syracuseStep 227463 = 341195) B341195
theorem B227471 : Blo 223812 227471 := bstep (se 1 (by rfl) ⟨170603, by rfl⟩ : syracuseStep 227471 = 341207) B341207
theorem B227515 : Blo 223812 227515 := bstep (se 1 (by rfl) ⟨170636, by rfl⟩ : syracuseStep 227515 = 341273) B341273
theorem B850121 : Blo 223812 850121 := bstep (se 2 (by rfl) ⟨318795, by rfl⟩ : syracuseStep 850121 = 637591) B637591
theorem B227591 : Blo 223812 227591 := bstep (se 1 (by rfl) ⟨170693, by rfl⟩ : syracuseStep 227591 = 341387) B341387
theorem B227599 : Blo 223812 227599 := bstep (se 1 (by rfl) ⟨170699, by rfl⟩ : syracuseStep 227599 = 341399) B341399
theorem B227643 : Blo 223812 227643 := bstep (se 1 (by rfl) ⟨170732, by rfl⟩ : syracuseStep 227643 = 341465) B341465
theorem B1145177 : Blo 223812 1145177 := bstep (se 2 (by rfl) ⟨429441, by rfl⟩ : syracuseStep 1145177 = 858883) B858883
theorem B719239 : Blo 223812 719239 := bstep (se 1 (by rfl) ⟨539429, by rfl⟩ : syracuseStep 719239 = 1078859) B1078859
theorem B227719 : Blo 223812 227719 := bstep (se 1 (by rfl) ⟨170789, by rfl⟩ : syracuseStep 227719 = 341579) B341579
theorem B227727 : Blo 223812 227727 := bstep (se 1 (by rfl) ⟨170795, by rfl⟩ : syracuseStep 227727 = 341591) B341591
theorem B227771 : Blo 223812 227771 := bstep (se 1 (by rfl) ⟨170828, by rfl⟩ : syracuseStep 227771 = 341657) B341657
theorem B1210967 : Blo 223812 1210967 := bstep (se 1 (by rfl) ⟨908225, by rfl⟩ : syracuseStep 1210967 = 1816451) B1816451
theorem B1440449 : Blo 223812 1440449 := bstep (se 2 (by rfl) ⟨540168, by rfl⟩ : syracuseStep 1440449 = 1080337) B1080337
theorem B817921 : Blo 223812 817921 := bstep (se 2 (by rfl) ⟨306720, by rfl⟩ : syracuseStep 817921 = 613441) B613441
theorem B2063141 : Blo 223812 2063141 := bstep (se 4 (by rfl) ⟨193419, by rfl⟩ : syracuseStep 2063141 = 386839) B386839
theorem B7863155 : Blo 223812 7863155 := bstep (se 1 (by rfl) ⟨5897366, by rfl⟩ : syracuseStep 7863155 = 11794733) B11794733
theorem B10386629 : Blo 223812 10386629 := bstep (se 4 (by rfl) ⟨973746, by rfl⟩ : syracuseStep 10386629 = 1947493) B1947493
theorem B720161 : Blo 223812 720161 := bstep (se 2 (by rfl) ⟨270060, by rfl⟩ : syracuseStep 720161 = 540121) B540121
theorem B1277369 : Blo 223812 1277369 := bstep (se 2 (by rfl) ⟨479013, by rfl⟩ : syracuseStep 1277369 = 958027) B958027
theorem B851897 : Blo 223812 851897 := bstep (se 2 (by rfl) ⟨319461, by rfl⟩ : syracuseStep 851897 = 638923) B638923
theorem B655379 : Blo 223812 655379 := bstep (se 1 (by rfl) ⟨491534, by rfl⟩ : syracuseStep 655379 = 983069) B983069
theorem B458849 : Blo 223812 458849 := bstep (se 2 (by rfl) ⟨172068, by rfl⟩ : syracuseStep 458849 = 344137) B344137
theorem B426313 : Blo 223812 426313 := bstep (se 2 (by rfl) ⟨159867, by rfl⟩ : syracuseStep 426313 = 319735) B319735
theorem B852353 : Blo 223812 852353 := bstep (se 2 (by rfl) ⟨319632, by rfl⟩ : syracuseStep 852353 = 639265) B639265
theorem B721505 : Blo 223812 721505 := bstep (se 2 (by rfl) ⟨270564, by rfl⟩ : syracuseStep 721505 = 541129) B541129
theorem B4915829 : Blo 223812 4915829 := bstep (se 5 (by rfl) ⟨230429, by rfl⟩ : syracuseStep 4915829 = 460859) B460859
theorem B492383 : Blo 223812 492383 := bstep (se 1 (by rfl) ⟨369287, by rfl⟩ : syracuseStep 492383 = 738575) B738575
theorem B1278827 : Blo 223812 1278827 := bstep (se 1 (by rfl) ⟨959120, by rfl⟩ : syracuseStep 1278827 = 1918241) B1918241
theorem B328555 : Blo 223812 328555 := bstep (se 1 (by rfl) ⟨246416, by rfl⟩ : syracuseStep 328555 = 492833) B492833
theorem B1704887 : Blo 223812 1704887 := bstep (se 1 (by rfl) ⟨1278665, by rfl⟩ : syracuseStep 1704887 = 2557331) B2557331
theorem B427027 : Blo 223812 427027 := bstep (se 1 (by rfl) ⟨320270, by rfl⟩ : syracuseStep 427027 = 640541) B640541
theorem B361721 : Blo 223812 361721 := bstep (se 2 (by rfl) ⟨135645, by rfl⟩ : syracuseStep 361721 = 271291) B271291
theorem B427369 : Blo 223812 427369 := bstep (se 2 (by rfl) ⟨160263, by rfl⟩ : syracuseStep 427369 = 320527) B320527
theorem B2491813 : Blo 223812 2491813 := bstep (se 4 (by rfl) ⟨233607, by rfl⟩ : syracuseStep 2491813 = 467215) B467215
theorem B853537 : Blo 223812 853537 := bstep (se 2 (by rfl) ⟨320076, by rfl⟩ : syracuseStep 853537 = 640153) B640153
theorem B722621 : Blo 223812 722621 := bstep (se 3 (by rfl) ⟨135491, by rfl⟩ : syracuseStep 722621 = 270983) B270983
theorem B854023 : Blo 223812 854023 := bstep (se 1 (by rfl) ⟨640517, by rfl⟩ : syracuseStep 854023 = 1281035) B1281035
theorem B1869905 : Blo 223812 1869905 := bstep (se 2 (by rfl) ⟨701214, by rfl⟩ : syracuseStep 1869905 = 1402429) B1402429
theorem B1313111 : Blo 223812 1313111 := bstep (se 1 (by rfl) ⟨984833, by rfl⟩ : syracuseStep 1313111 = 1969667) B1969667
theorem B1706345 : Blo 223812 1706345 := bstep (se 2 (by rfl) ⟨639879, by rfl⟩ : syracuseStep 1706345 = 1279759) B1279759
theorem B854509 : Blo 223812 854509 := bstep (se 3 (by rfl) ⟨160220, by rfl⟩ : syracuseStep 854509 = 320441) B320441
theorem B5474951 : Blo 223812 5474951 := bstep (se 1 (by rfl) ⟨4106213, by rfl⟩ : syracuseStep 5474951 = 8212427) B8212427
theorem B428743 : Blo 223812 428743 := bstep (se 1 (by rfl) ⟨321557, by rfl⟩ : syracuseStep 428743 = 643115) B643115
theorem B854813 : Blo 223812 854813 := bstep (se 3 (by rfl) ⟨160277, by rfl⟩ : syracuseStep 854813 = 320555) B320555
theorem B2329489 : Blo 223812 2329489 := bstep (se 2 (by rfl) ⟨873558, by rfl⟩ : syracuseStep 2329489 = 1747117) B1747117
theorem B756755 : Blo 223812 756755 := bstep (se 1 (by rfl) ⟨567566, by rfl⟩ : syracuseStep 756755 = 1135133) B1135133
theorem B1150199 : Blo 223812 1150199 := bstep (se 1 (by rfl) ⟨862649, by rfl⟩ : syracuseStep 1150199 = 1725299) B1725299
theorem B757079 : Blo 223812 757079 := bstep (se 1 (by rfl) ⟨567809, by rfl⟩ : syracuseStep 757079 = 1135619) B1135619
theorem B1084873 : Blo 223812 1084873 := bstep (se 2 (by rfl) ⟨406827, by rfl⟩ : syracuseStep 1084873 = 813655) B813655
theorem B1150685 : Blo 223812 1150685 := bstep (se 3 (by rfl) ⟨215753, by rfl⟩ : syracuseStep 1150685 = 431507) B431507
theorem B233311 : Blo 223812 233311 := bstep (se 1 (by rfl) ⟨174983, by rfl⟩ : syracuseStep 233311 = 349967) B349967
theorem B1216417 : Blo 223812 1216417 := bstep (se 2 (by rfl) ⟨456156, by rfl⟩ : syracuseStep 1216417 = 912313) B912313
theorem B3477433 : Blo 223812 3477433 := bstep (se 2 (by rfl) ⟨1304037, by rfl⟩ : syracuseStep 3477433 = 2608075) B2608075
theorem B692155 : Blo 223812 692155 := bstep (se 1 (by rfl) ⟨519116, by rfl⟩ : syracuseStep 692155 = 1038233) B1038233
theorem B4362245 : Blo 223812 4362245 := bstep (se 4 (by rfl) ⟨408960, by rfl⟩ : syracuseStep 4362245 = 817921) B817921
theorem B1708289 : Blo 223812 1708289 := bstep (se 2 (by rfl) ⟨640608, by rfl⟩ : syracuseStep 1708289 = 1281217) B1281217
theorem B758159 : Blo 223812 758159 := bstep (se 1 (by rfl) ⟨568619, by rfl⟩ : syracuseStep 758159 = 1137239) B1137239
theorem B331321873 : Blo 223812 331321873 := bstep (se 2 (by rfl) ⟨124245702, by rfl⟩ : syracuseStep 331321873 = 248491405) B248491405
theorem B758483 : Blo 223812 758483 := bstep (se 1 (by rfl) ⟨568862, by rfl⟩ : syracuseStep 758483 = 1137725) B1137725
theorem B856939 : Blo 223812 856939 := bstep (se 1 (by rfl) ⟨642704, by rfl⟩ : syracuseStep 856939 = 1285409) B1285409
theorem B430991 : Blo 223812 430991 := bstep (se 1 (by rfl) ⟨323243, by rfl⟩ : syracuseStep 430991 = 646487) B646487
theorem B1741943 : Blo 223812 1741943 := bstep (se 1 (by rfl) ⟨1306457, by rfl⟩ : syracuseStep 1741943 = 2612915) B2612915
theorem B595343 : Blo 223812 595343 := bstep (se 1 (by rfl) ⟨446507, by rfl⟩ : syracuseStep 595343 = 893015) B893015
theorem B1545965 : Blo 223812 1545965 := bstep (se 3 (by rfl) ⟨289868, by rfl⟩ : syracuseStep 1545965 = 579737) B579737
theorem B1021739 : Blo 223812 1021739 := bstep (se 1 (by rfl) ⟨766304, by rfl⟩ : syracuseStep 1021739 = 1532609) B1532609
theorem B759671 : Blo 223812 759671 := bstep (se 1 (by rfl) ⟨569753, by rfl⟩ : syracuseStep 759671 = 1139507) B1139507
theorem B432047 : Blo 223812 432047 := bstep (se 1 (by rfl) ⟨324035, by rfl⟩ : syracuseStep 432047 = 648071) B648071
theorem B1284133 : Blo 223812 1284133 := bstep (se 4 (by rfl) ⟨120387, by rfl⟩ : syracuseStep 1284133 = 240775) B240775
theorem B759887 : Blo 223812 759887 := bstep (se 1 (by rfl) ⟨569915, by rfl⟩ : syracuseStep 759887 = 1139831) B1139831
theorem B432479 : Blo 223812 432479 := bstep (se 1 (by rfl) ⟨324359, by rfl⟩ : syracuseStep 432479 = 648719) B648719
theorem B760265 : Blo 223812 760265 := bstep (se 2 (by rfl) ⟨285099, by rfl⟩ : syracuseStep 760265 = 570199) B570199
theorem B760535 : Blo 223812 760535 := bstep (se 1 (by rfl) ⟨570401, by rfl⟩ : syracuseStep 760535 = 1140803) B1140803
theorem B957359 : Blo 223812 957359 := bstep (se 1 (by rfl) ⟨718019, by rfl⟩ : syracuseStep 957359 = 1436039) B1436039
theorem B760751 : Blo 223812 760751 := bstep (se 1 (by rfl) ⟨570563, by rfl⟩ : syracuseStep 760751 = 1141127) B1141127
theorem B269239 : Blo 223812 269239 := bstep (se 1 (by rfl) ⟨201929, by rfl⟩ : syracuseStep 269239 = 403859) B403859
theorem B727991 : Blo 223812 727991 := bstep (se 1 (by rfl) ⟨545993, by rfl⟩ : syracuseStep 727991 = 1091987) B1091987
theorem B2169899 : Blo 223812 2169899 := bstep (se 1 (by rfl) ⟨1627424, by rfl⟩ : syracuseStep 2169899 = 3254849) B3254849
theorem B1940759 : Blo 223812 1940759 := bstep (se 1 (by rfl) ⟨1455569, by rfl⟩ : syracuseStep 1940759 = 2911139) B2911139
theorem B859673 : Blo 223812 859673 := bstep (se 2 (by rfl) ⟨322377, by rfl⟩ : syracuseStep 859673 = 644755) B644755
theorem B6233861 : Blo 223812 6233861 := bstep (se 4 (by rfl) ⟨584424, by rfl⟩ : syracuseStep 6233861 = 1168849) B1168849
theorem B335723 : Blo 223812 335723 := bstep (se 1 (by rfl) ⟨251792, by rfl⟩ : syracuseStep 335723 = 503585) B503585
theorem B728939 : Blo 223812 728939 := bstep (se 1 (by rfl) ⟨546704, by rfl⟩ : syracuseStep 728939 = 1093409) B1093409
theorem B335951 : Blo 223812 335951 := bstep (se 1 (by rfl) ⟨251963, by rfl⟩ : syracuseStep 335951 = 503927) B503927
theorem B336071 : Blo 223812 336071 := bstep (se 1 (by rfl) ⟨252053, by rfl⟩ : syracuseStep 336071 = 504107) B504107
theorem B336233 : Blo 223812 336233 := bstep (se 2 (by rfl) ⟨126087, by rfl⟩ : syracuseStep 336233 = 252175) B252175
theorem B336311 : Blo 223812 336311 := bstep (se 1 (by rfl) ⟨252233, by rfl⟩ : syracuseStep 336311 = 504467) B504467
theorem B336347 : Blo 223812 336347 := bstep (se 1 (by rfl) ⟨252260, by rfl⟩ : syracuseStep 336347 = 504521) B504521
theorem B958985 : Blo 223812 958985 := bstep (se 2 (by rfl) ⟨359619, by rfl⟩ : syracuseStep 958985 = 719239) B719239
theorem B1712663 : Blo 223812 1712663 := bstep (se 1 (by rfl) ⟨1284497, by rfl⟩ : syracuseStep 1712663 = 2568995) B2568995
theorem B1286867 : Blo 223812 1286867 := bstep (se 1 (by rfl) ⟨965150, by rfl⟩ : syracuseStep 1286867 = 1930301) B1930301
theorem B336815 : Blo 223812 336815 := bstep (se 1 (by rfl) ⟨252611, by rfl⟩ : syracuseStep 336815 = 505223) B505223
theorem B336905 : Blo 223812 336905 := bstep (se 2 (by rfl) ⟨126339, by rfl⟩ : syracuseStep 336905 = 252679) B252679
theorem B11183123 : Blo 223812 11183123 := bstep (se 1 (by rfl) ⟨8387342, by rfl⟩ : syracuseStep 11183123 = 16774685) B16774685
theorem B336935 : Blo 223812 336935 := bstep (se 1 (by rfl) ⟨252701, by rfl⟩ : syracuseStep 336935 = 505403) B505403
theorem B861299 : Blo 223812 861299 := bstep (se 1 (by rfl) ⟨645974, by rfl⟩ : syracuseStep 861299 = 1291949) B1291949
theorem B337019 : Blo 223812 337019 := bstep (se 1 (by rfl) ⟨252764, by rfl⟩ : syracuseStep 337019 = 505529) B505529
theorem B959683 : Blo 223812 959683 := bstep (se 1 (by rfl) ⟨719762, by rfl⟩ : syracuseStep 959683 = 1439525) B1439525
theorem B763127 : Blo 223812 763127 := bstep (se 1 (by rfl) ⟨572345, by rfl⟩ : syracuseStep 763127 = 1144691) B1144691
theorem B337145 : Blo 223812 337145 := bstep (se 2 (by rfl) ⟨126429, by rfl⟩ : syracuseStep 337145 = 252859) B252859
theorem B1221911 : Blo 223812 1221911 := bstep (se 1 (by rfl) ⟨916433, by rfl⟩ : syracuseStep 1221911 = 1832867) B1832867
theorem B337247 : Blo 223812 337247 := bstep (se 1 (by rfl) ⟨252935, by rfl⟩ : syracuseStep 337247 = 505871) B505871
theorem B337259 : Blo 223812 337259 := bstep (se 1 (by rfl) ⟨252944, by rfl⟩ : syracuseStep 337259 = 505889) B505889
theorem B566747 : Blo 223812 566747 := bstep (se 1 (by rfl) ⟨425060, by rfl⟩ : syracuseStep 566747 = 850121) B850121
theorem B763451 : Blo 223812 763451 := bstep (se 1 (by rfl) ⟨572588, by rfl⟩ : syracuseStep 763451 = 1145177) B1145177
theorem B337487 : Blo 223812 337487 := bstep (se 1 (by rfl) ⟨253115, by rfl⟩ : syracuseStep 337487 = 506231) B506231
theorem B2762387 : Blo 223812 2762387 := bstep (se 1 (by rfl) ⟨2071790, by rfl⟩ : syracuseStep 2762387 = 4143581) B4143581
theorem B337607 : Blo 223812 337607 := bstep (se 1 (by rfl) ⟨253205, by rfl⟩ : syracuseStep 337607 = 506411) B506411
theorem B960299 : Blo 223812 960299 := bstep (se 1 (by rfl) ⟨720224, by rfl⟩ : syracuseStep 960299 = 1440449) B1440449
theorem B763721 : Blo 223812 763721 := bstep (se 2 (by rfl) ⟨286395, by rfl⟩ : syracuseStep 763721 = 572791) B572791
theorem B337769 : Blo 223812 337769 := bstep (se 2 (by rfl) ⟨126663, by rfl⟩ : syracuseStep 337769 = 253327) B253327
theorem B337847 : Blo 223812 337847 := bstep (se 1 (by rfl) ⟨253385, by rfl⟩ : syracuseStep 337847 = 506771) B506771
theorem B337883 : Blo 223812 337883 := bstep (se 1 (by rfl) ⟨253412, by rfl⟩ : syracuseStep 337883 = 506825) B506825
theorem B6924419 : Blo 223812 6924419 := bstep (se 1 (by rfl) ⟨5193314, by rfl⟩ : syracuseStep 6924419 = 10386629) B10386629
theorem B403627 : Blo 223812 403627 := bstep (se 1 (by rfl) ⟨302720, by rfl⟩ : syracuseStep 403627 = 605441) B605441
theorem B1452289 : Blo 223812 1452289 := bstep (se 2 (by rfl) ⟨544608, by rfl⟩ : syracuseStep 1452289 = 1089217) B1089217
theorem B862589 : Blo 223812 862589 := bstep (se 3 (by rfl) ⟨161735, by rfl⟩ : syracuseStep 862589 = 323471) B323471
theorem B338351 : Blo 223812 338351 := bstep (se 1 (by rfl) ⟨253763, by rfl⟩ : syracuseStep 338351 = 507527) B507527
theorem B338441 : Blo 223812 338441 := bstep (se 2 (by rfl) ⟨126915, by rfl⟩ : syracuseStep 338441 = 253831) B253831
theorem B338471 : Blo 223812 338471 := bstep (se 1 (by rfl) ⟨253853, by rfl⟩ : syracuseStep 338471 = 507707) B507707
theorem B567931 : Blo 223812 567931 := bstep (se 1 (by rfl) ⟨425948, by rfl⟩ : syracuseStep 567931 = 851897) B851897
theorem B338555 : Blo 223812 338555 := bstep (se 1 (by rfl) ⟨253916, by rfl⟩ : syracuseStep 338555 = 507833) B507833
theorem B338681 : Blo 223812 338681 := bstep (se 2 (by rfl) ⟨127005, by rfl⟩ : syracuseStep 338681 = 254011) B254011
theorem B1289033 : Blo 223812 1289033 := bstep (se 2 (by rfl) ⟨483387, by rfl⟩ : syracuseStep 1289033 = 966775) B966775
theorem B338783 : Blo 223812 338783 := bstep (se 1 (by rfl) ⟨254087, by rfl⟩ : syracuseStep 338783 = 508175) B508175
theorem B338795 : Blo 223812 338795 := bstep (se 1 (by rfl) ⟨254096, by rfl⟩ : syracuseStep 338795 = 508193) B508193
theorem B404399 : Blo 223812 404399 := bstep (se 1 (by rfl) ⟨303299, by rfl⟩ : syracuseStep 404399 = 606599) B606599
theorem B764855 : Blo 223812 764855 := bstep (se 1 (by rfl) ⟨573641, by rfl⟩ : syracuseStep 764855 = 1147283) B1147283
theorem B339023 : Blo 223812 339023 := bstep (se 1 (by rfl) ⟨254267, by rfl⟩ : syracuseStep 339023 = 508535) B508535
theorem B2895041 : Blo 223812 2895041 := bstep (se 2 (by rfl) ⟨1085640, by rfl⟩ : syracuseStep 2895041 = 2171281) B2171281
theorem B339143 : Blo 223812 339143 := bstep (se 1 (by rfl) ⟨254357, by rfl⟩ : syracuseStep 339143 = 508715) B508715
theorem B339305 : Blo 223812 339305 := bstep (se 2 (by rfl) ⟨127239, by rfl⟩ : syracuseStep 339305 = 254479) B254479
theorem B339383 : Blo 223812 339383 := bstep (se 1 (by rfl) ⟨254537, by rfl⟩ : syracuseStep 339383 = 509075) B509075
theorem B339419 : Blo 223812 339419 := bstep (se 1 (by rfl) ⟨254564, by rfl⟩ : syracuseStep 339419 = 509129) B509129
theorem B765449 : Blo 223812 765449 := bstep (se 2 (by rfl) ⟨287043, by rfl⟩ : syracuseStep 765449 = 574087) B574087
theorem B405011 : Blo 223812 405011 := bstep (se 1 (by rfl) ⟨303758, by rfl⟩ : syracuseStep 405011 = 607517) B607517
theorem B1027723 : Blo 223812 1027723 := bstep (se 1 (by rfl) ⟨770792, by rfl⟩ : syracuseStep 1027723 = 1541585) B1541585
theorem B339887 : Blo 223812 339887 := bstep (se 1 (by rfl) ⟨254915, by rfl⟩ : syracuseStep 339887 = 509831) B509831
theorem B25472945 : Blo 223812 25472945 := bstep (se 2 (by rfl) ⟨9552354, by rfl⟩ : syracuseStep 25472945 = 19104709) B19104709
theorem B3092411 : Blo 223812 3092411 := bstep (se 1 (by rfl) ⟨2319308, by rfl⟩ : syracuseStep 3092411 = 4638617) B4638617
theorem B339977 : Blo 223812 339977 := bstep (se 2 (by rfl) ⟨127491, by rfl⟩ : syracuseStep 339977 = 254983) B254983
theorem B340007 : Blo 223812 340007 := bstep (se 1 (by rfl) ⟨255005, by rfl⟩ : syracuseStep 340007 = 510011) B510011
theorem B962675 : Blo 223812 962675 := bstep (se 1 (by rfl) ⟨722006, by rfl⟩ : syracuseStep 962675 = 1444013) B1444013
theorem B340091 : Blo 223812 340091 := bstep (se 1 (by rfl) ⟨255068, by rfl⟩ : syracuseStep 340091 = 510137) B510137
theorem B307399 : Blo 223812 307399 := bstep (se 1 (by rfl) ⟨230549, by rfl⟩ : syracuseStep 307399 = 461099) B461099
theorem B864503 : Blo 223812 864503 := bstep (se 1 (by rfl) ⟨648377, by rfl⟩ : syracuseStep 864503 = 1296755) B1296755
theorem B340217 : Blo 223812 340217 := bstep (se 2 (by rfl) ⟨127581, by rfl⟩ : syracuseStep 340217 = 255163) B255163
theorem B340319 : Blo 223812 340319 := bstep (se 1 (by rfl) ⟨255239, by rfl⟩ : syracuseStep 340319 = 510479) B510479
theorem B766313 : Blo 223812 766313 := bstep (se 2 (by rfl) ⟨287367, by rfl⟩ : syracuseStep 766313 = 574735) B574735
theorem B340331 : Blo 223812 340331 := bstep (se 1 (by rfl) ⟨255248, by rfl⟩ : syracuseStep 340331 = 510497) B510497
theorem B504359 : Blo 223812 504359 := bstep (se 1 (by rfl) ⟨378269, by rfl⟩ : syracuseStep 504359 = 756539) B756539
theorem B438841 : Blo 223812 438841 := bstep (se 2 (by rfl) ⟨164565, by rfl⟩ : syracuseStep 438841 = 329131) B329131
theorem B340559 : Blo 223812 340559 := bstep (se 1 (by rfl) ⟨255419, by rfl⟩ : syracuseStep 340559 = 510839) B510839
theorem B340679 : Blo 223812 340679 := bstep (se 1 (by rfl) ⟨255509, by rfl⟩ : syracuseStep 340679 = 511019) B511019
theorem B1454851 : Blo 223812 1454851 := bstep (se 1 (by rfl) ⟨1091138, by rfl⟩ : syracuseStep 1454851 = 2182277) B2182277
theorem B3912461 : Blo 223812 3912461 := bstep (se 3 (by rfl) ⟨733586, by rfl⟩ : syracuseStep 3912461 = 1467173) B1467173
theorem B406367 : Blo 223812 406367 := bstep (se 1 (by rfl) ⟨304775, by rfl⟩ : syracuseStep 406367 = 609551) B609551
theorem B340841 : Blo 223812 340841 := bstep (se 2 (by rfl) ⟨127815, by rfl⟩ : syracuseStep 340841 = 255631) B255631
theorem B504683 : Blo 223812 504683 := bstep (se 1 (by rfl) ⟨378512, by rfl⟩ : syracuseStep 504683 = 757025) B757025
theorem B2470763 : Blo 223812 2470763 := bstep (se 1 (by rfl) ⟨1853072, by rfl⟩ : syracuseStep 2470763 = 3706145) B3706145
theorem B504737 : Blo 223812 504737 := bstep (se 2 (by rfl) ⟨189276, by rfl⟩ : syracuseStep 504737 = 378553) B378553
theorem B340919 : Blo 223812 340919 := bstep (se 1 (by rfl) ⟨255689, by rfl⟩ : syracuseStep 340919 = 511379) B511379
theorem B766907 : Blo 223812 766907 := bstep (se 1 (by rfl) ⟨575180, by rfl⟩ : syracuseStep 766907 = 1150361) B1150361
theorem B340955 : Blo 223812 340955 := bstep (se 1 (by rfl) ⟨255716, by rfl⟩ : syracuseStep 340955 = 511433) B511433
theorem B505079 : Blo 223812 505079 := bstep (se 1 (by rfl) ⟨378809, by rfl⟩ : syracuseStep 505079 = 757619) B757619
theorem B341423 : Blo 223812 341423 := bstep (se 1 (by rfl) ⟨256067, by rfl⟩ : syracuseStep 341423 = 512135) B512135
theorem B341513 : Blo 223812 341513 := bstep (se 2 (by rfl) ⟨128067, by rfl⟩ : syracuseStep 341513 = 256135) B256135
theorem B341543 : Blo 223812 341543 := bstep (se 1 (by rfl) ⟨256157, by rfl⟩ : syracuseStep 341543 = 512315) B512315
theorem B341627 : Blo 223812 341627 := bstep (se 1 (by rfl) ⟨256220, by rfl⟩ : syracuseStep 341627 = 512441) B512441
theorem B1914515 : Blo 223812 1914515 := bstep (se 1 (by rfl) ⟨1435886, by rfl⟩ : syracuseStep 1914515 = 2871773) B2871773
theorem B2471639 : Blo 223812 2471639 := bstep (se 1 (by rfl) ⟨1853729, by rfl⟩ : syracuseStep 2471639 = 3707459) B3707459
theorem B440057 : Blo 223812 440057 := bstep (se 2 (by rfl) ⟨165021, by rfl⟩ : syracuseStep 440057 = 330043) B330043
theorem B1718009 : Blo 223812 1718009 := bstep (se 2 (by rfl) ⟨644253, by rfl⟩ : syracuseStep 1718009 = 1288507) B1288507
theorem B505673 : Blo 223812 505673 := bstep (se 2 (by rfl) ⟨189627, by rfl⟩ : syracuseStep 505673 = 379255) B379255
theorem B4340101 : Blo 223812 4340101 := bstep (se 4 (by rfl) ⟨406884, by rfl⟩ : syracuseStep 4340101 = 813769) B813769
theorem B637465 : Blo 223812 637465 := bstep (se 2 (by rfl) ⟨239049, by rfl⟩ : syracuseStep 637465 = 478099) B478099
theorem B506465 : Blo 223812 506465 := bstep (se 2 (by rfl) ⟨189924, by rfl⟩ : syracuseStep 506465 = 379849) B379849
theorem B768635 : Blo 223812 768635 := bstep (se 1 (by rfl) ⟨576476, by rfl⟩ : syracuseStep 768635 = 1152953) B1152953
theorem B768797 : Blo 223812 768797 := bstep (se 3 (by rfl) ⟨144149, by rfl⟩ : syracuseStep 768797 = 288299) B288299
theorem B572255 : Blo 223812 572255 := bstep (se 1 (by rfl) ⟨429191, by rfl⟩ : syracuseStep 572255 = 858383) B858383
theorem B768943 : Blo 223812 768943 := bstep (se 1 (by rfl) ⟨576707, by rfl⟩ : syracuseStep 768943 = 1153415) B1153415
theorem B506807 : Blo 223812 506807 := bstep (se 1 (by rfl) ⟨380105, by rfl⟩ : syracuseStep 506807 = 760211) B760211
theorem B408673 : Blo 223812 408673 := bstep (se 2 (by rfl) ⟨153252, by rfl⟩ : syracuseStep 408673 = 306505) B306505
theorem B1719467 : Blo 223812 1719467 := bstep (se 1 (by rfl) ⟨1289600, by rfl⟩ : syracuseStep 1719467 = 2579201) B2579201
theorem B966107 : Blo 223812 966107 := bstep (se 1 (by rfl) ⟨724580, by rfl⟩ : syracuseStep 966107 = 1449161) B1449161
theorem B507401 : Blo 223812 507401 := bstep (se 2 (by rfl) ⟨190275, by rfl⟩ : syracuseStep 507401 = 380551) B380551
theorem B572953 : Blo 223812 572953 := bstep (se 2 (by rfl) ⟨214857, by rfl⟩ : syracuseStep 572953 = 429715) B429715
theorem B1719953 : Blo 223812 1719953 := bstep (se 2 (by rfl) ⟨644982, by rfl⟩ : syracuseStep 1719953 = 1289965) B1289965
theorem B1949507 : Blo 223812 1949507 := bstep (se 1 (by rfl) ⟨1462130, by rfl⟩ : syracuseStep 1949507 = 2924261) B2924261
theorem B573257 : Blo 223812 573257 := bstep (se 2 (by rfl) ⟨214971, by rfl⟩ : syracuseStep 573257 = 429943) B429943
theorem B507743 : Blo 223812 507743 := bstep (se 1 (by rfl) ⟨380807, by rfl⟩ : syracuseStep 507743 = 761615) B761615
theorem B868205 : Blo 223812 868205 := bstep (se 3 (by rfl) ⟨162788, by rfl⟩ : syracuseStep 868205 = 325577) B325577
theorem B507923 : Blo 223812 507923 := bstep (se 1 (by rfl) ⟨380942, by rfl⟩ : syracuseStep 507923 = 761885) B761885
theorem B1818787 : Blo 223812 1818787 := bstep (se 1 (by rfl) ⟨1364090, by rfl⟩ : syracuseStep 1818787 = 2728181) B2728181
theorem B2015549 : Blo 223812 2015549 := bstep (se 3 (by rfl) ⟨377915, by rfl⟩ : syracuseStep 2015549 = 755831) B755831
theorem B508265 : Blo 223812 508265 := bstep (se 2 (by rfl) ⟨190599, by rfl⟩ : syracuseStep 508265 = 381199) B381199
theorem B541399 : Blo 223812 541399 := bstep (se 1 (by rfl) ⟨406049, by rfl⟩ : syracuseStep 541399 = 812099) B812099
theorem B377743 : Blo 223812 377743 := bstep (se 1 (by rfl) ⟨283307, by rfl⟩ : syracuseStep 377743 = 566615) B566615
theorem B574391 : Blo 223812 574391 := bstep (se 1 (by rfl) ⟨430793, by rfl⟩ : syracuseStep 574391 = 861587) B861587
theorem B508859 : Blo 223812 508859 := bstep (se 1 (by rfl) ⟨381644, by rfl⟩ : syracuseStep 508859 = 763289) B763289
theorem B771079 : Blo 223812 771079 := bstep (se 1 (by rfl) ⟨578309, by rfl⟩ : syracuseStep 771079 = 1156619) B1156619
theorem B508985 : Blo 223812 508985 := bstep (se 2 (by rfl) ⟨190869, by rfl⟩ : syracuseStep 508985 = 381739) B381739
theorem B1721411 : Blo 223812 1721411 := bstep (se 1 (by rfl) ⟨1291058, by rfl⟩ : syracuseStep 1721411 = 2582117) B2582117
theorem B3327095 : Blo 223812 3327095 := bstep (se 1 (by rfl) ⟨2495321, by rfl⟩ : syracuseStep 3327095 = 4990643) B4990643
theorem B640381 : Blo 223812 640381 := bstep (se 3 (by rfl) ⟨120071, by rfl⟩ : syracuseStep 640381 = 240143) B240143
theorem B509327 : Blo 223812 509327 := bstep (se 1 (by rfl) ⟨381995, by rfl⟩ : syracuseStep 509327 = 763991) B763991
theorem B378425 : Blo 223812 378425 := bstep (se 2 (by rfl) ⟨141909, by rfl⟩ : syracuseStep 378425 = 283819) B283819
theorem B2868797 : Blo 223812 2868797 := bstep (se 3 (by rfl) ⟨537899, by rfl⟩ : syracuseStep 2868797 = 1075799) B1075799
theorem B1296071 : Blo 223812 1296071 := bstep (se 1 (by rfl) ⟨972053, by rfl⟩ : syracuseStep 1296071 = 1944107) B1944107
theorem B640723 : Blo 223812 640723 := bstep (se 1 (by rfl) ⟨480542, by rfl⟩ : syracuseStep 640723 = 961085) B961085
theorem B509651 : Blo 223812 509651 := bstep (se 1 (by rfl) ⟨382238, by rfl⟩ : syracuseStep 509651 = 764477) B764477
theorem B575495 : Blo 223812 575495 := bstep (se 1 (by rfl) ⟨431621, by rfl⟩ : syracuseStep 575495 = 863243) B863243
theorem B346121 : Blo 223812 346121 := bstep (se 2 (by rfl) ⟨129795, by rfl⟩ : syracuseStep 346121 = 259591) B259591
theorem B1722383 : Blo 223812 1722383 := bstep (se 1 (by rfl) ⟨1291787, by rfl⟩ : syracuseStep 1722383 = 2583575) B2583575
theorem B575545 : Blo 223812 575545 := bstep (se 2 (by rfl) ⟨215829, by rfl⟩ : syracuseStep 575545 = 431659) B431659
theorem B379127 : Blo 223812 379127 := bstep (se 1 (by rfl) ⟨284345, by rfl⟩ : syracuseStep 379127 = 568691) B568691
theorem B969047 : Blo 223812 969047 := bstep (se 1 (by rfl) ⟨726785, by rfl⟩ : syracuseStep 969047 = 1453571) B1453571
theorem B575849 : Blo 223812 575849 := bstep (se 2 (by rfl) ⟨215943, by rfl⟩ : syracuseStep 575849 = 431887) B431887
theorem B379471 : Blo 223812 379471 := bstep (se 1 (by rfl) ⟨284603, by rfl⟩ : syracuseStep 379471 = 569207) B569207
theorem B510587 : Blo 223812 510587 := bstep (se 1 (by rfl) ⟨382940, by rfl⟩ : syracuseStep 510587 = 765881) B765881
theorem B510713 : Blo 223812 510713 := bstep (se 2 (by rfl) ⟨191517, by rfl⟩ : syracuseStep 510713 = 383035) B383035
theorem B379721 : Blo 223812 379721 := bstep (se 2 (by rfl) ⟨142395, by rfl⟩ : syracuseStep 379721 = 284791) B284791
theorem B510983 : Blo 223812 510983 := bstep (se 1 (by rfl) ⟨383237, by rfl⟩ : syracuseStep 510983 = 766475) B766475
theorem B511055 : Blo 223812 511055 := bstep (se 1 (by rfl) ⟨383291, by rfl⟩ : syracuseStep 511055 = 766583) B766583
theorem B380153 : Blo 223812 380153 := bstep (se 2 (by rfl) ⟨142557, by rfl⟩ : syracuseStep 380153 = 285115) B285115
theorem B380335 : Blo 223812 380335 := bstep (se 1 (by rfl) ⟨285251, by rfl⟩ : syracuseStep 380335 = 570503) B570503
theorem B511451 : Blo 223812 511451 := bstep (se 1 (by rfl) ⟨383588, by rfl⟩ : syracuseStep 511451 = 767177) B767177
theorem B380423 : Blo 223812 380423 := bstep (se 1 (by rfl) ⟨285317, by rfl⟩ : syracuseStep 380423 = 570635) B570635
theorem B478919 : Blo 223812 478919 := bstep (se 1 (by rfl) ⟨359189, by rfl⟩ : syracuseStep 478919 = 718379) B718379
theorem B511699 : Blo 223812 511699 := bstep (se 1 (by rfl) ⟨383774, by rfl⟩ : syracuseStep 511699 = 767549) B767549
theorem B872147 : Blo 223812 872147 := bstep (se 1 (by rfl) ⟨654110, by rfl⟩ : syracuseStep 872147 = 1308221) B1308221
theorem B806723 : Blo 223812 806723 := bstep (se 1 (by rfl) ⟨605042, by rfl⟩ : syracuseStep 806723 = 1210085) B1210085
theorem B380767 : Blo 223812 380767 := bstep (se 1 (by rfl) ⟨285575, by rfl⟩ : syracuseStep 380767 = 571151) B571151
theorem B511919 : Blo 223812 511919 := bstep (se 1 (by rfl) ⟨383939, by rfl⟩ : syracuseStep 511919 = 767879) B767879
theorem B380855 : Blo 223812 380855 := bstep (se 1 (by rfl) ⟨285641, by rfl⟩ : syracuseStep 380855 = 571283) B571283
theorem B3559355 : Blo 223812 3559355 := bstep (se 1 (by rfl) ⟨2669516, by rfl⟩ : syracuseStep 3559355 = 5339033) B5339033
theorem B3657757 : Blo 223812 3657757 := bstep (se 3 (by rfl) ⟨685829, by rfl⟩ : syracuseStep 3657757 = 1371659) B1371659
theorem B512171 : Blo 223812 512171 := bstep (se 1 (by rfl) ⟨384128, by rfl⟩ : syracuseStep 512171 = 768257) B768257
theorem B643457 : Blo 223812 643457 := bstep (se 2 (by rfl) ⟨241296, by rfl⟩ : syracuseStep 643457 = 482593) B482593
theorem B807311 : Blo 223812 807311 := bstep (se 1 (by rfl) ⟨605483, by rfl⟩ : syracuseStep 807311 = 1210967) B1210967
theorem B643571 : Blo 223812 643571 := bstep (se 1 (by rfl) ⟨482678, by rfl⟩ : syracuseStep 643571 = 965357) B965357
theorem B381449 : Blo 223812 381449 := bstep (se 2 (by rfl) ⟨143043, by rfl⟩ : syracuseStep 381449 = 286087) B286087
theorem B381611 : Blo 223812 381611 := bstep (se 1 (by rfl) ⟨286208, by rfl⟩ : syracuseStep 381611 = 572417) B572417
theorem B971473 : Blo 223812 971473 := bstep (se 2 (by rfl) ⟨364302, by rfl⟩ : syracuseStep 971473 = 728605) B728605
theorem B643913 : Blo 223812 643913 := bstep (se 2 (by rfl) ⟨241467, by rfl⟩ : syracuseStep 643913 = 482935) B482935
theorem B480107 : Blo 223812 480107 := bstep (se 1 (by rfl) ⟨360080, by rfl⟩ : syracuseStep 480107 = 720161) B720161
theorem B1037231 : Blo 223812 1037231 := bstep (se 1 (by rfl) ⟨777923, by rfl⟩ : syracuseStep 1037231 = 1555847) B1555847
theorem B3724289 : Blo 223812 3724289 := bstep (se 2 (by rfl) ⟨1396608, by rfl⟩ : syracuseStep 3724289 = 2793217) B2793217
theorem B382009 : Blo 223812 382009 := bstep (se 2 (by rfl) ⟨143253, by rfl⟩ : syracuseStep 382009 = 286507) B286507
theorem B382151 : Blo 223812 382151 := bstep (se 1 (by rfl) ⟨286613, by rfl⟩ : syracuseStep 382151 = 573227) B573227
theorem B1725785 : Blo 223812 1725785 := bstep (se 2 (by rfl) ⟨647169, by rfl⟩ : syracuseStep 1725785 = 1294339) B1294339
theorem B382313 : Blo 223812 382313 := bstep (se 2 (by rfl) ⟨143367, by rfl⟩ : syracuseStep 382313 = 286735) B286735
theorem B284087 : Blo 223812 284087 := bstep (se 1 (by rfl) ⟨213065, by rfl⟩ : syracuseStep 284087 = 426131) B426131
theorem B284239 : Blo 223812 284239 := bstep (se 1 (by rfl) ⟨213179, by rfl⟩ : syracuseStep 284239 = 426359) B426359
theorem B1136267 : Blo 223812 1136267 := bstep (se 1 (by rfl) ⟨852200, by rfl⟩ : syracuseStep 1136267 = 1704401) B1704401
theorem B382711 : Blo 223812 382711 := bstep (se 1 (by rfl) ⟨287033, by rfl⟩ : syracuseStep 382711 = 574067) B574067
theorem B546743 : Blo 223812 546743 := bstep (se 1 (by rfl) ⟨410057, by rfl⟩ : syracuseStep 546743 = 820115) B820115
theorem B382907 : Blo 223812 382907 := bstep (se 1 (by rfl) ⟨287180, by rfl⟩ : syracuseStep 382907 = 574361) B574361
theorem B383015 : Blo 223812 383015 := bstep (se 1 (by rfl) ⟨287261, by rfl⟩ : syracuseStep 383015 = 574523) B574523
theorem B4315193 : Blo 223812 4315193 := bstep (se 2 (by rfl) ⟨1618197, by rfl⟩ : syracuseStep 4315193 = 3236395) B3236395
theorem B252103 : Blo 223812 252103 := bstep (se 1 (by rfl) ⟨189077, by rfl⟩ : syracuseStep 252103 = 378155) B378155
theorem B383305 : Blo 223812 383305 := bstep (se 2 (by rfl) ⟨143739, by rfl⟩ : syracuseStep 383305 = 287479) B287479
theorem B383339 : Blo 223812 383339 := bstep (se 1 (by rfl) ⟨287504, by rfl⟩ : syracuseStep 383339 = 575009) B575009
theorem B285383 : Blo 223812 285383 := bstep (se 1 (by rfl) ⟨214037, by rfl⟩ : syracuseStep 285383 = 428075) B428075
theorem B383737 : Blo 223812 383737 := bstep (se 2 (by rfl) ⟨143901, by rfl⟩ : syracuseStep 383737 = 287803) B287803
theorem B285535 : Blo 223812 285535 := bstep (se 1 (by rfl) ⟨214151, by rfl⟩ : syracuseStep 285535 = 428303) B428303
theorem B384007 : Blo 223812 384007 := bstep (se 1 (by rfl) ⟨288005, by rfl⟩ : syracuseStep 384007 = 576011) B576011
theorem B252967 : Blo 223812 252967 := bstep (se 1 (by rfl) ⟨189725, by rfl⟩ : syracuseStep 252967 = 379451) B379451
theorem B3104243 : Blo 223812 3104243 := bstep (se 1 (by rfl) ⟨2328182, by rfl⟩ : syracuseStep 3104243 = 4656365) B4656365
theorem B810643 : Blo 223812 810643 := bstep (se 1 (by rfl) ⟨607982, by rfl⟩ : syracuseStep 810643 = 1215965) B1215965
theorem B876179 : Blo 223812 876179 := bstep (se 1 (by rfl) ⟨657134, by rfl⟩ : syracuseStep 876179 = 1314269) B1314269
theorem B1728215 : Blo 223812 1728215 := bstep (se 1 (by rfl) ⟨1296161, by rfl⟩ : syracuseStep 1728215 = 2592323) B2592323
theorem B876395 : Blo 223812 876395 := bstep (se 1 (by rfl) ⟨657296, by rfl⟩ : syracuseStep 876395 = 1314593) B1314593
theorem B483259 : Blo 223812 483259 := bstep (se 1 (by rfl) ⟨362444, by rfl⟩ : syracuseStep 483259 = 724889) B724889
theorem B2580659 : Blo 223812 2580659 := bstep (se 1 (by rfl) ⟨1935494, by rfl⟩ : syracuseStep 2580659 = 3870989) B3870989
theorem B516343 : Blo 223812 516343 := bstep (se 1 (by rfl) ⟨387257, by rfl⟩ : syracuseStep 516343 = 774515) B774515
theorem B319963 : Blo 223812 319963 := bstep (se 1 (by rfl) ⟨239972, by rfl⟩ : syracuseStep 319963 = 479945) B479945
theorem B811579 : Blo 223812 811579 := bstep (se 1 (by rfl) ⟨608684, by rfl⟩ : syracuseStep 811579 = 1217369) B1217369
theorem B909947 : Blo 223812 909947 := bstep (se 1 (by rfl) ⟨682460, by rfl⟩ : syracuseStep 909947 = 1364921) B1364921
theorem B254587 : Blo 223812 254587 := bstep (se 1 (by rfl) ⟨190940, by rfl⟩ : syracuseStep 254587 = 381881) B381881
theorem B680879 : Blo 223812 680879 := bstep (se 1 (by rfl) ⟨510659, by rfl⟩ : syracuseStep 680879 = 1021319) B1021319
theorem B287707 : Blo 223812 287707 := bstep (se 1 (by rfl) ⟨215780, by rfl⟩ : syracuseStep 287707 = 431561) B431561
theorem B255055 : Blo 223812 255055 := bstep (se 1 (by rfl) ⟨191291, by rfl⟩ : syracuseStep 255055 = 382583) B382583
theorem B2909303 : Blo 223812 2909303 := bstep (se 1 (by rfl) ⟨2181977, by rfl⟩ : syracuseStep 2909303 = 4363955) B4363955
theorem B320635 : Blo 223812 320635 := bstep (se 1 (by rfl) ⟨240476, by rfl⟩ : syracuseStep 320635 = 480953) B480953
theorem B615595 : Blo 223812 615595 := bstep (se 1 (by rfl) ⟨461696, by rfl⟩ : syracuseStep 615595 = 923393) B923393
theorem B320863 : Blo 223812 320863 := bstep (se 1 (by rfl) ⟨240647, by rfl⟩ : syracuseStep 320863 = 481295) B481295
theorem B255451 : Blo 223812 255451 := bstep (se 1 (by rfl) ⟨191588, by rfl⟩ : syracuseStep 255451 = 383177) B383177
theorem B812531 : Blo 223812 812531 := bstep (se 1 (by rfl) ⟨609398, by rfl⟩ : syracuseStep 812531 = 1218797) B1218797
theorem B1631981 : Blo 223812 1631981 := bstep (se 3 (by rfl) ⟨305996, by rfl⟩ : syracuseStep 1631981 = 611993) B611993
theorem B1140641 : Blo 223812 1140641 := bstep (se 2 (by rfl) ⟨427740, by rfl⟩ : syracuseStep 1140641 = 855481) B855481
theorem B321455 : Blo 223812 321455 := bstep (se 1 (by rfl) ⟨241091, by rfl⟩ : syracuseStep 321455 = 482183) B482183
theorem B255919 : Blo 223812 255919 := bstep (se 1 (by rfl) ⟨191939, by rfl⟩ : syracuseStep 255919 = 383879) B383879
theorem B321899 : Blo 223812 321899 := bstep (se 1 (by rfl) ⟨241424, by rfl⟩ : syracuseStep 321899 = 482849) B482849
theorem B223823 : Blo 223812 223823 := bstep (se 1 (by rfl) ⟨167867, by rfl⟩ : syracuseStep 223823 = 335735) B335735
theorem B223839 : Blo 223812 223839 := bstep (se 1 (by rfl) ⟨167879, by rfl⟩ : syracuseStep 223839 = 335759) B335759
theorem B223867 : Blo 223812 223867 := bstep (se 1 (by rfl) ⟨167900, by rfl⟩ : syracuseStep 223867 = 335801) B335801
theorem B223919 : Blo 223812 223919 := bstep (se 1 (by rfl) ⟨167939, by rfl⟩ : syracuseStep 223919 = 335879) B335879
theorem B223943 : Blo 223812 223943 := bstep (se 1 (by rfl) ⟨167957, by rfl⟩ : syracuseStep 223943 = 335915) B335915
theorem B223963 : Blo 223812 223963 := bstep (se 1 (by rfl) ⟨167972, by rfl⟩ : syracuseStep 223963 = 335945) B335945
theorem B224039 : Blo 223812 224039 := bstep (se 1 (by rfl) ⟨168029, by rfl⟩ : syracuseStep 224039 = 336059) B336059
theorem B224079 : Blo 223812 224079 := bstep (se 1 (by rfl) ⟨168059, by rfl⟩ : syracuseStep 224079 = 336119) B336119
theorem B224095 : Blo 223812 224095 := bstep (se 1 (by rfl) ⟨168071, by rfl⟩ : syracuseStep 224095 = 336143) B336143
theorem B224123 : Blo 223812 224123 := bstep (se 1 (by rfl) ⟨168092, by rfl⟩ : syracuseStep 224123 = 336185) B336185
theorem B5532563 : Blo 223812 5532563 := bstep (se 1 (by rfl) ⟨4149422, by rfl⟩ : syracuseStep 5532563 = 8298845) B8298845
theorem B224175 : Blo 223812 224175 := bstep (se 1 (by rfl) ⟨168131, by rfl⟩ : syracuseStep 224175 = 336263) B336263
theorem B224199 : Blo 223812 224199 := bstep (se 1 (by rfl) ⟨168149, by rfl⟩ : syracuseStep 224199 = 336299) B336299
theorem B224219 : Blo 223812 224219 := bstep (se 1 (by rfl) ⟨168164, by rfl⟩ : syracuseStep 224219 = 336329) B336329
theorem B224295 : Blo 223812 224295 := bstep (se 1 (by rfl) ⟨168221, by rfl⟩ : syracuseStep 224295 = 336443) B336443
theorem B224335 : Blo 223812 224335 := bstep (se 1 (by rfl) ⟨168251, by rfl⟩ : syracuseStep 224335 = 336503) B336503
theorem B224351 : Blo 223812 224351 := bstep (se 1 (by rfl) ⟨168263, by rfl⟩ : syracuseStep 224351 = 336527) B336527
theorem B224379 : Blo 223812 224379 := bstep (se 1 (by rfl) ⟨168284, by rfl⟩ : syracuseStep 224379 = 336569) B336569
theorem B224431 : Blo 223812 224431 := bstep (se 1 (by rfl) ⟨168323, by rfl⟩ : syracuseStep 224431 = 336647) B336647
theorem B1928387 : Blo 223812 1928387 := bstep (se 1 (by rfl) ⟨1446290, by rfl⟩ : syracuseStep 1928387 = 2892581) B2892581
theorem B224455 : Blo 223812 224455 := bstep (se 1 (by rfl) ⟨168341, by rfl⟩ : syracuseStep 224455 = 336683) B336683
theorem B224475 : Blo 223812 224475 := bstep (se 1 (by rfl) ⟨168356, by rfl⟩ : syracuseStep 224475 = 336713) B336713
theorem B224551 : Blo 223812 224551 := bstep (se 1 (by rfl) ⟨168413, by rfl⟩ : syracuseStep 224551 = 336827) B336827
theorem B224591 : Blo 223812 224591 := bstep (se 1 (by rfl) ⟨168443, by rfl⟩ : syracuseStep 224591 = 336887) B336887
theorem B453983 : Blo 223812 453983 := bstep (se 1 (by rfl) ⟨340487, by rfl⟩ : syracuseStep 453983 = 680975) B680975
theorem B224607 : Blo 223812 224607 := bstep (se 1 (by rfl) ⟨168455, by rfl⟩ : syracuseStep 224607 = 336911) B336911
theorem B224635 : Blo 223812 224635 := bstep (se 1 (by rfl) ⟨168476, by rfl⟩ : syracuseStep 224635 = 336953) B336953
theorem B224687 : Blo 223812 224687 := bstep (se 1 (by rfl) ⟨168515, by rfl⟩ : syracuseStep 224687 = 337031) B337031
theorem B224711 : Blo 223812 224711 := bstep (se 1 (by rfl) ⟨168533, by rfl⟩ : syracuseStep 224711 = 337067) B337067
theorem B224731 : Blo 223812 224731 := bstep (se 1 (by rfl) ⟨168548, by rfl⟩ : syracuseStep 224731 = 337097) B337097
theorem B1076723 : Blo 223812 1076723 := bstep (se 1 (by rfl) ⟨807542, by rfl⟩ : syracuseStep 1076723 = 1615085) B1615085
theorem B224807 : Blo 223812 224807 := bstep (se 1 (by rfl) ⟨168605, by rfl⟩ : syracuseStep 224807 = 337211) B337211
theorem B224847 : Blo 223812 224847 := bstep (se 1 (by rfl) ⟨168635, by rfl⟩ : syracuseStep 224847 = 337271) B337271
theorem B224863 : Blo 223812 224863 := bstep (se 1 (by rfl) ⟨168647, by rfl⟩ : syracuseStep 224863 = 337295) B337295
theorem B224891 : Blo 223812 224891 := bstep (se 1 (by rfl) ⟨168668, by rfl⟩ : syracuseStep 224891 = 337337) B337337
theorem B224943 : Blo 223812 224943 := bstep (se 1 (by rfl) ⟨168707, by rfl⟩ : syracuseStep 224943 = 337415) B337415
theorem B224967 : Blo 223812 224967 := bstep (se 1 (by rfl) ⟨168725, by rfl⟩ : syracuseStep 224967 = 337451) B337451
theorem B224987 : Blo 223812 224987 := bstep (se 1 (by rfl) ⟨168740, by rfl⟩ : syracuseStep 224987 = 337481) B337481
theorem B454391 : Blo 223812 454391 := bstep (se 1 (by rfl) ⟨340793, by rfl⟩ : syracuseStep 454391 = 681587) B681587
theorem B4091681 : Blo 223812 4091681 := bstep (se 2 (by rfl) ⟨1534380, by rfl⟩ : syracuseStep 4091681 = 3068761) B3068761
theorem B225063 : Blo 223812 225063 := bstep (se 1 (by rfl) ⟨168797, by rfl⟩ : syracuseStep 225063 = 337595) B337595
theorem B225103 : Blo 223812 225103 := bstep (se 1 (by rfl) ⟨168827, by rfl⟩ : syracuseStep 225103 = 337655) B337655
theorem B225119 : Blo 223812 225119 := bstep (se 1 (by rfl) ⟨168839, by rfl⟩ : syracuseStep 225119 = 337679) B337679
theorem B225147 : Blo 223812 225147 := bstep (se 1 (by rfl) ⟨168860, by rfl⟩ : syracuseStep 225147 = 337721) B337721
theorem B12283811 : Blo 223812 12283811 := bstep (se 1 (by rfl) ⟨9212858, by rfl⟩ : syracuseStep 12283811 = 18425717) B18425717
theorem B225199 : Blo 223812 225199 := bstep (se 1 (by rfl) ⟨168899, by rfl⟩ : syracuseStep 225199 = 337799) B337799
theorem B225223 : Blo 223812 225223 := bstep (se 1 (by rfl) ⟨168917, by rfl⟩ : syracuseStep 225223 = 337835) B337835
theorem B225243 : Blo 223812 225243 := bstep (se 1 (by rfl) ⟨168932, by rfl⟩ : syracuseStep 225243 = 337865) B337865
theorem B225319 : Blo 223812 225319 := bstep (se 1 (by rfl) ⟨168989, by rfl⟩ : syracuseStep 225319 = 337979) B337979
theorem B225359 : Blo 223812 225359 := bstep (se 1 (by rfl) ⟨169019, by rfl⟩ : syracuseStep 225359 = 338039) B338039
theorem B1077337 : Blo 223812 1077337 := bstep (se 2 (by rfl) ⟨404001, by rfl⟩ : syracuseStep 1077337 = 808003) B808003
theorem B225375 : Blo 223812 225375 := bstep (se 1 (by rfl) ⟨169031, by rfl⟩ : syracuseStep 225375 = 338063) B338063
theorem B225403 : Blo 223812 225403 := bstep (se 1 (by rfl) ⟨169052, by rfl⟩ : syracuseStep 225403 = 338105) B338105
theorem B225455 : Blo 223812 225455 := bstep (se 1 (by rfl) ⟨169091, by rfl⟩ : syracuseStep 225455 = 338183) B338183
theorem B225479 : Blo 223812 225479 := bstep (se 1 (by rfl) ⟨169109, by rfl⟩ : syracuseStep 225479 = 338219) B338219
theorem B225499 : Blo 223812 225499 := bstep (se 1 (by rfl) ⟨169124, by rfl⟩ : syracuseStep 225499 = 338249) B338249
theorem B225575 : Blo 223812 225575 := bstep (se 1 (by rfl) ⟨169181, by rfl⟩ : syracuseStep 225575 = 338363) B338363
theorem B225615 : Blo 223812 225615 := bstep (se 1 (by rfl) ⟨169211, by rfl⟩ : syracuseStep 225615 = 338423) B338423
theorem B225631 : Blo 223812 225631 := bstep (se 1 (by rfl) ⟨169223, by rfl⟩ : syracuseStep 225631 = 338447) B338447
theorem B225659 : Blo 223812 225659 := bstep (se 1 (by rfl) ⟨169244, by rfl⟩ : syracuseStep 225659 = 338489) B338489
theorem B225711 : Blo 223812 225711 := bstep (se 1 (by rfl) ⟨169283, by rfl⟩ : syracuseStep 225711 = 338567) B338567
theorem B225735 : Blo 223812 225735 := bstep (se 1 (by rfl) ⟨169301, by rfl⟩ : syracuseStep 225735 = 338603) B338603
theorem B225755 : Blo 223812 225755 := bstep (se 1 (by rfl) ⟨169316, by rfl⟩ : syracuseStep 225755 = 338633) B338633
theorem B225831 : Blo 223812 225831 := bstep (se 1 (by rfl) ⟨169373, by rfl⟩ : syracuseStep 225831 = 338747) B338747
theorem B225871 : Blo 223812 225871 := bstep (se 1 (by rfl) ⟨169403, by rfl⟩ : syracuseStep 225871 = 338807) B338807
theorem B225887 : Blo 223812 225887 := bstep (se 1 (by rfl) ⟨169415, by rfl⟩ : syracuseStep 225887 = 338831) B338831
theorem B225915 : Blo 223812 225915 := bstep (se 1 (by rfl) ⟨169436, by rfl⟩ : syracuseStep 225915 = 338873) B338873
theorem B225967 : Blo 223812 225967 := bstep (se 1 (by rfl) ⟨169475, by rfl⟩ : syracuseStep 225967 = 338951) B338951
theorem B225991 : Blo 223812 225991 := bstep (se 1 (by rfl) ⟨169493, by rfl⟩ : syracuseStep 225991 = 338987) B338987
theorem B226011 : Blo 223812 226011 := bstep (se 1 (by rfl) ⟨169508, by rfl⟩ : syracuseStep 226011 = 339017) B339017
theorem B226087 : Blo 223812 226087 := bstep (se 1 (by rfl) ⟨169565, by rfl⟩ : syracuseStep 226087 = 339131) B339131
theorem B226127 : Blo 223812 226127 := bstep (se 1 (by rfl) ⟨169595, by rfl⟩ : syracuseStep 226127 = 339191) B339191
theorem B226143 : Blo 223812 226143 := bstep (se 1 (by rfl) ⟨169607, by rfl⟩ : syracuseStep 226143 = 339215) B339215
theorem B226171 : Blo 223812 226171 := bstep (se 1 (by rfl) ⟨169628, by rfl⟩ : syracuseStep 226171 = 339257) B339257
theorem B226223 : Blo 223812 226223 := bstep (se 1 (by rfl) ⟨169667, by rfl⟩ : syracuseStep 226223 = 339335) B339335
theorem B226247 : Blo 223812 226247 := bstep (se 1 (by rfl) ⟨169685, by rfl⟩ : syracuseStep 226247 = 339371) B339371
theorem B226267 : Blo 223812 226267 := bstep (se 1 (by rfl) ⟨169700, by rfl⟩ : syracuseStep 226267 = 339401) B339401
theorem B226343 : Blo 223812 226343 := bstep (se 1 (by rfl) ⟨169757, by rfl⟩ : syracuseStep 226343 = 339515) B339515
theorem B226383 : Blo 223812 226383 := bstep (se 1 (by rfl) ⟨169787, by rfl⟩ : syracuseStep 226383 = 339575) B339575
theorem B226399 : Blo 223812 226399 := bstep (se 1 (by rfl) ⟨169799, by rfl⟩ : syracuseStep 226399 = 339599) B339599
theorem B226427 : Blo 223812 226427 := bstep (se 1 (by rfl) ⟨169820, by rfl⟩ : syracuseStep 226427 = 339641) B339641
theorem B1307801 : Blo 223812 1307801 := bstep (se 2 (by rfl) ⟨490425, by rfl⟩ : syracuseStep 1307801 = 980851) B980851
theorem B652445 : Blo 223812 652445 := bstep (se 3 (by rfl) ⟨122333, by rfl⟩ : syracuseStep 652445 = 244667) B244667
theorem B226479 : Blo 223812 226479 := bstep (se 1 (by rfl) ⟨169859, by rfl⟩ : syracuseStep 226479 = 339719) B339719
theorem B226503 : Blo 223812 226503 := bstep (se 1 (by rfl) ⟨169877, by rfl⟩ : syracuseStep 226503 = 339755) B339755
theorem B226523 : Blo 223812 226523 := bstep (se 1 (by rfl) ⟨169892, by rfl⟩ : syracuseStep 226523 = 339785) B339785
theorem B226599 : Blo 223812 226599 := bstep (se 1 (by rfl) ⟨169949, by rfl⟩ : syracuseStep 226599 = 339899) B339899
theorem B226639 : Blo 223812 226639 := bstep (se 1 (by rfl) ⟨169979, by rfl⟩ : syracuseStep 226639 = 339959) B339959
theorem B226655 : Blo 223812 226655 := bstep (se 1 (by rfl) ⟨169991, by rfl⟩ : syracuseStep 226655 = 339983) B339983
theorem B226683 : Blo 223812 226683 := bstep (se 1 (by rfl) ⟨170012, by rfl⟩ : syracuseStep 226683 = 340025) B340025
theorem B1734061 : Blo 223812 1734061 := bstep (se 3 (by rfl) ⟨325136, by rfl⟩ : syracuseStep 1734061 = 650273) B650273
theorem B226735 : Blo 223812 226735 := bstep (se 1 (by rfl) ⟨170051, by rfl⟩ : syracuseStep 226735 = 340103) B340103
theorem B226759 : Blo 223812 226759 := bstep (se 1 (by rfl) ⟨170069, by rfl⟩ : syracuseStep 226759 = 340139) B340139
theorem B226779 : Blo 223812 226779 := bstep (se 1 (by rfl) ⟨170084, by rfl⟩ : syracuseStep 226779 = 340169) B340169
theorem B226855 : Blo 223812 226855 := bstep (se 1 (by rfl) ⟨170141, by rfl⟩ : syracuseStep 226855 = 340283) B340283
theorem B226895 : Blo 223812 226895 := bstep (se 1 (by rfl) ⟨170171, by rfl⟩ : syracuseStep 226895 = 340343) B340343
theorem B226911 : Blo 223812 226911 := bstep (se 1 (by rfl) ⟨170183, by rfl⟩ : syracuseStep 226911 = 340367) B340367
theorem B226939 : Blo 223812 226939 := bstep (se 1 (by rfl) ⟨170204, by rfl⟩ : syracuseStep 226939 = 340409) B340409
theorem B226991 : Blo 223812 226991 := bstep (se 1 (by rfl) ⟨170243, by rfl⟩ : syracuseStep 226991 = 340487) B340487
theorem B227015 : Blo 223812 227015 := bstep (se 1 (by rfl) ⟨170261, by rfl⟩ : syracuseStep 227015 = 340523) B340523
theorem B227035 : Blo 223812 227035 := bstep (se 1 (by rfl) ⟨170276, by rfl⟩ : syracuseStep 227035 = 340553) B340553
theorem B227111 : Blo 223812 227111 := bstep (se 1 (by rfl) ⟨170333, by rfl⟩ : syracuseStep 227111 = 340667) B340667
theorem B227151 : Blo 223812 227151 := bstep (se 1 (by rfl) ⟨170363, by rfl⟩ : syracuseStep 227151 = 340727) B340727
theorem B227167 : Blo 223812 227167 := bstep (se 1 (by rfl) ⟨170375, by rfl⟩ : syracuseStep 227167 = 340751) B340751
theorem B2062189 : Blo 223812 2062189 := bstep (se 3 (by rfl) ⟨386660, by rfl⟩ : syracuseStep 2062189 = 773321) B773321
theorem B227195 : Blo 223812 227195 := bstep (se 1 (by rfl) ⟨170396, by rfl⟩ : syracuseStep 227195 = 340793) B340793
theorem B227247 : Blo 223812 227247 := bstep (se 1 (by rfl) ⟨170435, by rfl⟩ : syracuseStep 227247 = 340871) B340871
theorem B227271 : Blo 223812 227271 := bstep (se 1 (by rfl) ⟨170453, by rfl⟩ : syracuseStep 227271 = 340907) B340907
theorem B227291 : Blo 223812 227291 := bstep (se 1 (by rfl) ⟨170468, by rfl⟩ : syracuseStep 227291 = 340937) B340937
theorem B1275911 : Blo 223812 1275911 := bstep (se 1 (by rfl) ⟨956933, by rfl⟩ : syracuseStep 1275911 = 1913867) B1913867
theorem B227367 : Blo 223812 227367 := bstep (se 1 (by rfl) ⟨170525, by rfl⟩ : syracuseStep 227367 = 341051) B341051
theorem B227407 : Blo 223812 227407 := bstep (se 1 (by rfl) ⟨170555, by rfl⟩ : syracuseStep 227407 = 341111) B341111
theorem B227423 : Blo 223812 227423 := bstep (se 1 (by rfl) ⟨170567, by rfl⟩ : syracuseStep 227423 = 341135) B341135
theorem B227451 : Blo 223812 227451 := bstep (se 1 (by rfl) ⟨170588, by rfl⟩ : syracuseStep 227451 = 341177) B341177
theorem B227503 : Blo 223812 227503 := bstep (se 1 (by rfl) ⟨170627, by rfl⟩ : syracuseStep 227503 = 341255) B341255
theorem B227527 : Blo 223812 227527 := bstep (se 1 (by rfl) ⟨170645, by rfl⟩ : syracuseStep 227527 = 341291) B341291
theorem B227547 : Blo 223812 227547 := bstep (se 1 (by rfl) ⟨170660, by rfl⟩ : syracuseStep 227547 = 341321) B341321
theorem B227623 : Blo 223812 227623 := bstep (se 1 (by rfl) ⟨170717, by rfl⟩ : syracuseStep 227623 = 341435) B341435
theorem B227663 : Blo 223812 227663 := bstep (se 1 (by rfl) ⟨170747, by rfl⟩ : syracuseStep 227663 = 341495) B341495
theorem B227679 : Blo 223812 227679 := bstep (se 1 (by rfl) ⟨170759, by rfl⟩ : syracuseStep 227679 = 341519) B341519
theorem B6977897 : Blo 223812 6977897 := bstep (se 2 (by rfl) ⟨2616711, by rfl⟩ : syracuseStep 6977897 = 5233423) B5233423
theorem B227707 : Blo 223812 227707 := bstep (se 1 (by rfl) ⟨170780, by rfl⟩ : syracuseStep 227707 = 341561) B341561
theorem B227759 : Blo 223812 227759 := bstep (se 1 (by rfl) ⟨170819, by rfl⟩ : syracuseStep 227759 = 341639) B341639
theorem B227783 : Blo 223812 227783 := bstep (se 1 (by rfl) ⟨170837, by rfl⟩ : syracuseStep 227783 = 341675) B341675
theorem B227803 : Blo 223812 227803 := bstep (se 1 (by rfl) ⟨170852, by rfl⟩ : syracuseStep 227803 = 341705) B341705
theorem B358921 : Blo 223812 358921 := bstep (se 2 (by rfl) ⟨134595, by rfl⟩ : syracuseStep 358921 = 269191) B269191
theorem B850621 : Blo 223812 850621 := bstep (se 3 (by rfl) ⟨159491, by rfl⟩ : syracuseStep 850621 = 318983) B318983
theorem B425083 : Blo 223812 425083 := bstep (se 1 (by rfl) ⟨318812, by rfl⟩ : syracuseStep 425083 = 637625) B637625
theorem B1375427 : Blo 223812 1375427 := bstep (se 1 (by rfl) ⟨1031570, by rfl⟩ : syracuseStep 1375427 = 2063141) B2063141
theorem B425159 : Blo 223812 425159 := bstep (se 1 (by rfl) ⟨318869, by rfl⟩ : syracuseStep 425159 = 637739) B637739
theorem B5242103 : Blo 223812 5242103 := bstep (se 1 (by rfl) ⟨3931577, by rfl⟩ : syracuseStep 5242103 = 7863155) B7863155
theorem B425569 : Blo 223812 425569 := bstep (se 2 (by rfl) ⟨159588, by rfl⟩ : syracuseStep 425569 = 319177) B319177
theorem B851579 : Blo 223812 851579 := bstep (se 1 (by rfl) ⟨638684, by rfl⟩ : syracuseStep 851579 = 1277369) B1277369
theorem B425911 : Blo 223812 425911 := bstep (se 1 (by rfl) ⟨319433, by rfl⟩ : syracuseStep 425911 = 638867) B638867
theorem B1343699 : Blo 223812 1343699 := bstep (se 1 (by rfl) ⟨1007774, by rfl⟩ : syracuseStep 1343699 = 2015549) B2015549
theorem B2425049 : Blo 223812 2425049 := bstep (se 2 (by rfl) ⟨909393, by rfl⟩ : syracuseStep 2425049 = 1818787) B1818787
theorem B688457 : Blo 223812 688457 := bstep (se 2 (by rfl) ⟨258171, by rfl⟩ : syracuseStep 688457 = 516343) B516343
theorem B328255 : Blo 223812 328255 := bstep (se 1 (by rfl) ⟨246191, by rfl⟩ : syracuseStep 328255 = 492383) B492383
theorem B852551 : Blo 223812 852551 := bstep (se 1 (by rfl) ⟨639413, by rfl⟩ : syracuseStep 852551 = 1278827) B1278827
theorem B426617 : Blo 223812 426617 := bstep (se 2 (by rfl) ⟨159981, by rfl⟩ : syracuseStep 426617 = 319963) B319963
theorem B1147607 : Blo 223812 1147607 := bstep (se 1 (by rfl) ⟨860705, by rfl⟩ : syracuseStep 1147607 = 1721411) B1721411
theorem B1082105 : Blo 223812 1082105 := bstep (se 2 (by rfl) ⟨405789, by rfl⟩ : syracuseStep 1082105 = 811579) B811579
theorem B721865 : Blo 223812 721865 := bstep (se 2 (by rfl) ⟨270699, by rfl⟩ : syracuseStep 721865 = 541399) B541399
theorem B230747 : Blo 223812 230747 := bstep (se 1 (by rfl) ⟨173060, by rfl⟩ : syracuseStep 230747 = 346121) B346121
theorem B1148255 : Blo 223812 1148255 := bstep (se 1 (by rfl) ⟨861191, by rfl⟩ : syracuseStep 1148255 = 1722383) B1722383
theorem B1246603 : Blo 223812 1246603 := bstep (se 1 (by rfl) ⟨934952, by rfl⟩ : syracuseStep 1246603 = 1869905) B1869905
theorem B427513 : Blo 223812 427513 := bstep (se 2 (by rfl) ⟨160317, by rfl⟩ : syracuseStep 427513 = 320635) B320635
theorem B820793 : Blo 223812 820793 := bstep (se 2 (by rfl) ⟨307797, by rfl⟩ : syracuseStep 820793 = 615595) B615595
theorem B1279577 : Blo 223812 1279577 := bstep (se 2 (by rfl) ⟨479841, by rfl⟩ : syracuseStep 1279577 = 959683) B959683
theorem B13108877 : Blo 223812 13108877 := bstep (se 3 (by rfl) ⟨2457914, by rfl⟩ : syracuseStep 13108877 = 4915829) B4915829
theorem B427817 : Blo 223812 427817 := bstep (se 2 (by rfl) ⟨160431, by rfl⟩ : syracuseStep 427817 = 320863) B320863
theorem B853841 : Blo 223812 853841 := bstep (se 2 (by rfl) ⟨320190, by rfl⟩ : syracuseStep 853841 = 640381) B640381
theorem B854297 : Blo 223812 854297 := bstep (se 2 (by rfl) ⟨320361, by rfl⟩ : syracuseStep 854297 = 640723) B640723
theorem B1280285 : Blo 223812 1280285 := bstep (se 3 (by rfl) ⟨240053, by rfl⟩ : syracuseStep 1280285 = 480107) B480107
theorem B428971 : Blo 223812 428971 := bstep (se 1 (by rfl) ⟨321728, by rfl⟩ : syracuseStep 428971 = 643457) B643457
theorem B429047 : Blo 223812 429047 := bstep (se 1 (by rfl) ⟨321785, by rfl⟩ : syracuseStep 429047 = 643571) B643571
theorem B1936385 : Blo 223812 1936385 := bstep (se 2 (by rfl) ⟨726144, by rfl⟩ : syracuseStep 1936385 = 1452289) B1452289
theorem B429275 : Blo 223812 429275 := bstep (se 1 (by rfl) ⟨321956, by rfl⟩ : syracuseStep 429275 = 643913) B643913
theorem B691487 : Blo 223812 691487 := bstep (se 1 (by rfl) ⟨518615, by rfl⟩ : syracuseStep 691487 = 1037231) B1037231
theorem B757241 : Blo 223812 757241 := bstep (se 2 (by rfl) ⟨283965, by rfl⟩ : syracuseStep 757241 = 567931) B567931
theorem B1150523 : Blo 223812 1150523 := bstep (se 1 (by rfl) ⟨862892, by rfl⟩ : syracuseStep 1150523 = 1725785) B1725785
theorem B396895 : Blo 223812 396895 := bstep (se 1 (by rfl) ⟨297671, by rfl⟩ : syracuseStep 396895 = 595343) B595343
theorem B757511 : Blo 223812 757511 := bstep (se 1 (by rfl) ⟨568133, by rfl⟩ : syracuseStep 757511 = 1136267) B1136267
theorem B757565 : Blo 223812 757565 := bstep (se 3 (by rfl) ⟨142043, by rfl⟩ : syracuseStep 757565 = 284087) B284087
theorem B364495 : Blo 223812 364495 := bstep (se 1 (by rfl) ⟨273371, by rfl⟩ : syracuseStep 364495 = 546743) B546743
theorem B2166749 : Blo 223812 2166749 := bstep (se 3 (by rfl) ⟨406265, by rfl⟩ : syracuseStep 2166749 = 812531) B812531
theorem B1446497 : Blo 223812 1446497 := bstep (se 2 (by rfl) ⟨542436, by rfl⟩ : syracuseStep 1446497 = 1084873) B1084873
theorem B1446599 : Blo 223812 1446599 := bstep (se 1 (by rfl) ⟨1084949, by rfl⟩ : syracuseStep 1446599 = 2169899) B2169899
theorem B2724637 : Blo 223812 2724637 := bstep (se 3 (by rfl) ⟨510869, by rfl⟩ : syracuseStep 2724637 = 1021739) B1021739
theorem B2069495 : Blo 223812 2069495 := bstep (se 1 (by rfl) ⟨1552121, by rfl⟩ : syracuseStep 2069495 = 3104243) B3104243
theorem B857213 : Blo 223812 857213 := bstep (se 3 (by rfl) ⟨160727, by rfl⟩ : syracuseStep 857213 = 321455) B321455
theorem B1152143 : Blo 223812 1152143 := bstep (se 1 (by rfl) ⟨864107, by rfl⟩ : syracuseStep 1152143 = 1728215) B1728215
theorem B922873 : Blo 223812 922873 := bstep (se 2 (by rfl) ⟨346077, by rfl⟩ : syracuseStep 922873 = 692155) B692155
theorem B857911 : Blo 223812 857911 := bstep (se 1 (by rfl) ⟨643433, by rfl⟩ : syracuseStep 857911 = 1286867) B1286867
theorem B1939535 : Blo 223812 1939535 := bstep (se 1 (by rfl) ⟨1454651, by rfl⟩ : syracuseStep 1939535 = 2909303) B2909303
theorem B1153277 : Blo 223812 1153277 := bstep (se 3 (by rfl) ⟨216239, by rfl⟩ : syracuseStep 1153277 = 432479) B432479
theorem B858397 : Blo 223812 858397 := bstep (se 3 (by rfl) ⟨160949, by rfl⟩ : syracuseStep 858397 = 321899) B321899
theorem B1939801 : Blo 223812 1939801 := bstep (se 2 (by rfl) ⟨727425, by rfl⟩ : syracuseStep 1939801 = 1454851) B1454851
theorem B1841591 : Blo 223812 1841591 := bstep (se 1 (by rfl) ⟨1381193, by rfl⟩ : syracuseStep 1841591 = 2762387) B2762387
theorem B1087987 : Blo 223812 1087987 := bstep (se 1 (by rfl) ⟨815990, by rfl⟩ : syracuseStep 1087987 = 1631981) B1631981
theorem B760427 : Blo 223812 760427 := bstep (se 1 (by rfl) ⟨570320, by rfl⟩ : syracuseStep 760427 = 1140641) B1140641
theorem B761021 : Blo 223812 761021 := bstep (se 3 (by rfl) ⟨142691, by rfl⟩ : syracuseStep 761021 = 285383) B285383
theorem B859355 : Blo 223812 859355 := bstep (se 1 (by rfl) ⟨644516, by rfl⟩ : syracuseStep 859355 = 1289033) B1289033
theorem B1285591 : Blo 223812 1285591 := bstep (se 1 (by rfl) ⟨964193, by rfl⟩ : syracuseStep 1285591 = 1928387) B1928387
theorem B1712177 : Blo 223812 1712177 := bstep (se 2 (by rfl) ⟨642066, by rfl⟩ : syracuseStep 1712177 = 1284133) B1284133
theorem B336137 : Blo 223812 336137 := bstep (se 2 (by rfl) ⟨126051, by rfl⟩ : syracuseStep 336137 = 252103) B252103
theorem B336239 : Blo 223812 336239 := bstep (se 1 (by rfl) ⟨252179, by rfl⟩ : syracuseStep 336239 = 504359) B504359
theorem B270911 : Blo 223812 270911 := bstep (se 1 (by rfl) ⟨203183, by rfl⟩ : syracuseStep 270911 = 406367) B406367
theorem B336455 : Blo 223812 336455 := bstep (se 1 (by rfl) ⟨252341, by rfl⟩ : syracuseStep 336455 = 504683) B504683
theorem B1647175 : Blo 223812 1647175 := bstep (se 1 (by rfl) ⟨1235381, by rfl⟩ : syracuseStep 1647175 = 2470763) B2470763
theorem B336491 : Blo 223812 336491 := bstep (se 1 (by rfl) ⟨252368, by rfl⟩ : syracuseStep 336491 = 504737) B504737
theorem B434963 : Blo 223812 434963 := bstep (se 1 (by rfl) ⟨326222, by rfl⟩ : syracuseStep 434963 = 652445) B652445
theorem B336719 : Blo 223812 336719 := bstep (se 1 (by rfl) ⟨252539, by rfl⟩ : syracuseStep 336719 = 505079) B505079
theorem B337115 : Blo 223812 337115 := bstep (se 1 (by rfl) ⟨252836, by rfl⟩ : syracuseStep 337115 = 505673) B505673
theorem B1025257 : Blo 223812 1025257 := bstep (se 2 (by rfl) ⟨384471, by rfl⟩ : syracuseStep 1025257 = 768943) B768943
theorem B337289 : Blo 223812 337289 := bstep (se 2 (by rfl) ⟨126483, by rfl⟩ : syracuseStep 337289 = 252967) B252967
theorem B566777 : Blo 223812 566777 := bstep (se 2 (by rfl) ⟨212541, by rfl⟩ : syracuseStep 566777 = 425083) B425083
theorem B337643 : Blo 223812 337643 := bstep (se 1 (by rfl) ⟨253232, by rfl⟩ : syracuseStep 337643 = 506465) B506465
theorem B337871 : Blo 223812 337871 := bstep (se 1 (by rfl) ⟨253403, by rfl⟩ : syracuseStep 337871 = 506807) B506807
theorem B16623629 : Blo 223812 16623629 := bstep (se 3 (by rfl) ⟨3116930, by rfl⟩ : syracuseStep 16623629 = 6233861) B6233861
theorem B763937 : Blo 223812 763937 := bstep (se 2 (by rfl) ⟨286476, by rfl⟩ : syracuseStep 763937 = 572953) B572953
theorem B567425 : Blo 223812 567425 := bstep (se 2 (by rfl) ⟨212784, by rfl⟩ : syracuseStep 567425 = 425569) B425569
theorem B338267 : Blo 223812 338267 := bstep (se 1 (by rfl) ⟨253700, by rfl⟩ : syracuseStep 338267 = 507401) B507401
theorem B567719 : Blo 223812 567719 := bstep (se 1 (by rfl) ⟨425789, by rfl⟩ : syracuseStep 567719 = 851579) B851579
theorem B338495 : Blo 223812 338495 := bstep (se 1 (by rfl) ⟨253871, by rfl⟩ : syracuseStep 338495 = 507743) B507743
theorem B567881 : Blo 223812 567881 := bstep (se 2 (by rfl) ⟨212955, by rfl⟩ : syracuseStep 567881 = 425911) B425911
theorem B338615 : Blo 223812 338615 := bstep (se 1 (by rfl) ⟨253961, by rfl⟩ : syracuseStep 338615 = 507923) B507923
theorem B436919 : Blo 223812 436919 := bstep (se 1 (by rfl) ⟨327689, by rfl⟩ : syracuseStep 436919 = 655379) B655379
theorem B305899 : Blo 223812 305899 := bstep (se 1 (by rfl) ⟨229424, by rfl⟩ : syracuseStep 305899 = 458849) B458849
theorem B338843 : Blo 223812 338843 := bstep (se 1 (by rfl) ⟨254132, by rfl⟩ : syracuseStep 338843 = 508265) B508265
theorem B568235 : Blo 223812 568235 := bstep (se 1 (by rfl) ⟨426176, by rfl⟩ : syracuseStep 568235 = 852353) B852353
theorem B568417 : Blo 223812 568417 := bstep (se 2 (by rfl) ⟨213156, by rfl⟩ : syracuseStep 568417 = 426313) B426313
theorem B339239 : Blo 223812 339239 := bstep (se 1 (by rfl) ⟨254429, by rfl⟩ : syracuseStep 339239 = 508859) B508859
theorem B339323 : Blo 223812 339323 := bstep (se 1 (by rfl) ⟨254492, by rfl⟩ : syracuseStep 339323 = 508985) B508985
theorem B339449 : Blo 223812 339449 := bstep (se 2 (by rfl) ⟨127293, by rfl⟩ : syracuseStep 339449 = 254587) B254587
theorem B241147 : Blo 223812 241147 := bstep (se 1 (by rfl) ⟨180860, by rfl⟩ : syracuseStep 241147 = 361721) B361721
theorem B339551 : Blo 223812 339551 := bstep (se 1 (by rfl) ⟨254663, by rfl⟩ : syracuseStep 339551 = 509327) B509327
theorem B1912531 : Blo 223812 1912531 := bstep (se 1 (by rfl) ⟨1434398, by rfl⟩ : syracuseStep 1912531 = 2868797) B2868797
theorem B864047 : Blo 223812 864047 := bstep (se 1 (by rfl) ⟨648035, by rfl⟩ : syracuseStep 864047 = 1296071) B1296071
theorem B339767 : Blo 223812 339767 := bstep (se 1 (by rfl) ⟨254825, by rfl⟩ : syracuseStep 339767 = 509651) B509651
theorem B503657 : Blo 223812 503657 := bstep (se 2 (by rfl) ⟨188871, by rfl⟩ : syracuseStep 503657 = 377743) B377743
theorem B1028105 : Blo 223812 1028105 := bstep (se 2 (by rfl) ⟨385539, by rfl⟩ : syracuseStep 1028105 = 771079) B771079
theorem B569369 : Blo 223812 569369 := bstep (se 2 (by rfl) ⟨213513, by rfl⟩ : syracuseStep 569369 = 427027) B427027
theorem B340073 : Blo 223812 340073 := bstep (se 2 (by rfl) ⟨127527, by rfl⟩ : syracuseStep 340073 = 255055) B255055
theorem B340391 : Blo 223812 340391 := bstep (se 1 (by rfl) ⟨255293, by rfl⟩ : syracuseStep 340391 = 510587) B510587
theorem B3649967 : Blo 223812 3649967 := bstep (se 1 (by rfl) ⟨2737475, by rfl⟩ : syracuseStep 3649967 = 5474951) B5474951
theorem B569825 : Blo 223812 569825 := bstep (se 2 (by rfl) ⟨213684, by rfl⟩ : syracuseStep 569825 = 427369) B427369
theorem B340475 : Blo 223812 340475 := bstep (se 1 (by rfl) ⟨255356, by rfl⟩ : syracuseStep 340475 = 510713) B510713
theorem B569875 : Blo 223812 569875 := bstep (se 1 (by rfl) ⟨427406, by rfl⟩ : syracuseStep 569875 = 854813) B854813
theorem B340601 : Blo 223812 340601 := bstep (se 2 (by rfl) ⟨127725, by rfl⟩ : syracuseStep 340601 = 255451) B255451
theorem B340655 : Blo 223812 340655 := bstep (se 1 (by rfl) ⟨255491, by rfl⟩ : syracuseStep 340655 = 510983) B510983
theorem B504503 : Blo 223812 504503 := bstep (se 1 (by rfl) ⟨378377, by rfl⟩ : syracuseStep 504503 = 756755) B756755
theorem B340703 : Blo 223812 340703 := bstep (se 1 (by rfl) ⟨255527, by rfl⟩ : syracuseStep 340703 = 511055) B511055
theorem B766799 : Blo 223812 766799 := bstep (se 1 (by rfl) ⟨575099, by rfl⟩ : syracuseStep 766799 = 1150199) B1150199
theorem B504719 : Blo 223812 504719 := bstep (se 1 (by rfl) ⟨378539, by rfl⟩ : syracuseStep 504719 = 757079) B757079
theorem B340967 : Blo 223812 340967 := bstep (se 1 (by rfl) ⟨255725, by rfl⟩ : syracuseStep 340967 = 511451) B511451
theorem B767123 : Blo 223812 767123 := bstep (se 1 (by rfl) ⟨575342, by rfl⟩ : syracuseStep 767123 = 1150685) B1150685
theorem B537815 : Blo 223812 537815 := bstep (se 1 (by rfl) ⟨403361, by rfl⟩ : syracuseStep 537815 = 806723) B806723
theorem B341225 : Blo 223812 341225 := bstep (se 2 (by rfl) ⟨127959, by rfl⟩ : syracuseStep 341225 = 255919) B255919
theorem B341279 : Blo 223812 341279 := bstep (se 1 (by rfl) ⟨255959, by rfl⟩ : syracuseStep 341279 = 511919) B511919
theorem B2372903 : Blo 223812 2372903 := bstep (se 1 (by rfl) ⟨1779677, by rfl⟩ : syracuseStep 2372903 = 3559355) B3559355
theorem B767393 : Blo 223812 767393 := bstep (se 2 (by rfl) ⟨287772, by rfl⟩ : syracuseStep 767393 = 575545) B575545
theorem B341447 : Blo 223812 341447 := bstep (se 1 (by rfl) ⟨256085, by rfl⟩ : syracuseStep 341447 = 512171) B512171
theorem B538169 : Blo 223812 538169 := bstep (se 2 (by rfl) ⟨201813, by rfl⟩ : syracuseStep 538169 = 403627) B403627
theorem B538207 : Blo 223812 538207 := bstep (se 1 (by rfl) ⟨403655, by rfl⟩ : syracuseStep 538207 = 807311) B807311
theorem B505439 : Blo 223812 505439 := bstep (se 1 (by rfl) ⟨379079, by rfl⟩ : syracuseStep 505439 = 758159) B758159
theorem B2340485 : Blo 223812 2340485 := bstep (se 4 (by rfl) ⟨219420, by rfl⟩ : syracuseStep 2340485 = 438841) B438841
theorem B505655 : Blo 223812 505655 := bstep (se 1 (by rfl) ⟨379241, by rfl⟩ : syracuseStep 505655 = 758483) B758483
theorem B505961 : Blo 223812 505961 := bstep (se 2 (by rfl) ⟨189735, by rfl⟩ : syracuseStep 505961 = 379471) B379471
theorem B571657 : Blo 223812 571657 := bstep (se 2 (by rfl) ⟨214371, by rfl⟩ : syracuseStep 571657 = 428743) B428743
theorem B1030643 : Blo 223812 1030643 := bstep (se 1 (by rfl) ⟨772982, by rfl⟩ : syracuseStep 1030643 = 1545965) B1545965
theorem B506447 : Blo 223812 506447 := bstep (se 1 (by rfl) ⟨379835, by rfl⟩ : syracuseStep 506447 = 759671) B759671
theorem B506591 : Blo 223812 506591 := bstep (se 1 (by rfl) ⟨379943, by rfl⟩ : syracuseStep 506591 = 759887) B759887
theorem B506843 : Blo 223812 506843 := bstep (se 1 (by rfl) ⟨380132, by rfl⟩ : syracuseStep 506843 = 760265) B760265
theorem B507023 : Blo 223812 507023 := bstep (se 1 (by rfl) ⟨380267, by rfl⟩ : syracuseStep 507023 = 760535) B760535
theorem B1752293 : Blo 223812 1752293 := bstep (se 4 (by rfl) ⟨164277, by rfl⟩ : syracuseStep 1752293 = 328555) B328555
theorem B507113 : Blo 223812 507113 := bstep (se 2 (by rfl) ⟨190167, by rfl⟩ : syracuseStep 507113 = 380335) B380335
theorem B507167 : Blo 223812 507167 := bstep (se 1 (by rfl) ⟨380375, by rfl⟩ : syracuseStep 507167 = 760751) B760751
theorem B1293839 : Blo 223812 1293839 := bstep (se 1 (by rfl) ⟨970379, by rfl⟩ : syracuseStep 1293839 = 1940759) B1940759
theorem B573115 : Blo 223812 573115 := bstep (se 1 (by rfl) ⟨429836, by rfl⟩ : syracuseStep 573115 = 859673) B859673
theorem B507689 : Blo 223812 507689 := bstep (se 2 (by rfl) ⟨190383, by rfl⟩ : syracuseStep 507689 = 380767) B380767
theorem B311081 : Blo 223812 311081 := bstep (se 2 (by rfl) ⟨116655, by rfl⟩ : syracuseStep 311081 = 233311) B233311
theorem B1621889 : Blo 223812 1621889 := bstep (se 2 (by rfl) ⟨608208, by rfl⟩ : syracuseStep 1621889 = 1216417) B1216417
theorem B4636577 : Blo 223812 4636577 := bstep (se 2 (by rfl) ⟨1738716, by rfl⟩ : syracuseStep 4636577 = 3477433) B3477433
theorem B1720439 : Blo 223812 1720439 := bstep (se 1 (by rfl) ⟨1290329, by rfl⟩ : syracuseStep 1720439 = 2580659) B2580659
theorem B409865 : Blo 223812 409865 := bstep (se 2 (by rfl) ⟨153699, by rfl⟩ : syracuseStep 409865 = 307399) B307399
theorem B639323 : Blo 223812 639323 := bstep (se 1 (by rfl) ⟨479492, by rfl⟩ : syracuseStep 639323 = 958985) B958985
theorem B606631 : Blo 223812 606631 := bstep (se 1 (by rfl) ⟨454973, by rfl⟩ : syracuseStep 606631 = 909947) B909947
theorem B7455415 : Blo 223812 7455415 := bstep (se 1 (by rfl) ⟨5591561, by rfl⟩ : syracuseStep 7455415 = 11183123) B11183123
theorem B441762497 : Blo 223812 441762497 := bstep (se 2 (by rfl) ⟨165660936, by rfl⟩ : syracuseStep 441762497 = 331321873) B331321873
theorem B574199 : Blo 223812 574199 := bstep (se 1 (by rfl) ⟨430649, by rfl⟩ : syracuseStep 574199 = 861299) B861299
theorem B508751 : Blo 223812 508751 := bstep (se 1 (by rfl) ⟨381563, by rfl⟩ : syracuseStep 508751 = 763127) B763127
theorem B1295297 : Blo 223812 1295297 := bstep (se 2 (by rfl) ⟨485736, by rfl⟩ : syracuseStep 1295297 = 971473) B971473
theorem B377831 : Blo 223812 377831 := bstep (se 1 (by rfl) ⟨283373, by rfl⟩ : syracuseStep 377831 = 566747) B566747
theorem B508967 : Blo 223812 508967 := bstep (se 1 (by rfl) ⟨381725, by rfl⟩ : syracuseStep 508967 = 763451) B763451
theorem B640199 : Blo 223812 640199 := bstep (se 1 (by rfl) ⟨480149, by rfl⟩ : syracuseStep 640199 = 960299) B960299
theorem B509147 : Blo 223812 509147 := bstep (se 1 (by rfl) ⟨381860, by rfl⟩ : syracuseStep 509147 = 763721) B763721
theorem B509345 : Blo 223812 509345 := bstep (se 2 (by rfl) ⟨191004, by rfl⟩ : syracuseStep 509345 = 382009) B382009
theorem B575059 : Blo 223812 575059 := bstep (se 1 (by rfl) ⟨431294, by rfl⟩ : syracuseStep 575059 = 862589) B862589
theorem B2312081 : Blo 223812 2312081 := bstep (se 2 (by rfl) ⟨867030, by rfl⟩ : syracuseStep 2312081 = 1734061) B1734061
theorem B3688375 : Blo 223812 3688375 := bstep (se 1 (by rfl) ⟨2766281, by rfl⟩ : syracuseStep 3688375 = 5532563) B5532563
theorem B509903 : Blo 223812 509903 := bstep (se 1 (by rfl) ⟨382427, by rfl⟩ : syracuseStep 509903 = 764855) B764855
theorem B378985 : Blo 223812 378985 := bstep (se 2 (by rfl) ⟨142119, by rfl⟩ : syracuseStep 378985 = 284239) B284239
theorem B13289669 : Blo 223812 13289669 := bstep (se 4 (by rfl) ⟨1245906, by rfl⟩ : syracuseStep 13289669 = 2491813) B2491813
theorem B26364149 : Blo 223812 26364149 := bstep (se 5 (by rfl) ⟨1235819, by rfl⟩ : syracuseStep 26364149 = 2471639) B2471639
theorem B510281 : Blo 223812 510281 := bstep (se 2 (by rfl) ⟨191355, by rfl⟩ : syracuseStep 510281 = 382711) B382711
theorem B510299 : Blo 223812 510299 := bstep (se 1 (by rfl) ⟨382724, by rfl⟩ : syracuseStep 510299 = 765449) B765449
theorem B641783 : Blo 223812 641783 := bstep (se 1 (by rfl) ⟨481337, by rfl⟩ : syracuseStep 641783 = 962675) B962675
theorem B576335 : Blo 223812 576335 := bstep (se 1 (by rfl) ⟨432251, by rfl⟩ : syracuseStep 576335 = 864503) B864503
theorem B510875 : Blo 223812 510875 := bstep (se 1 (by rfl) ⟨383156, by rfl⟩ : syracuseStep 510875 = 766313) B766313
theorem B511073 : Blo 223812 511073 := bstep (se 2 (by rfl) ⟨191652, by rfl⟩ : syracuseStep 511073 = 383305) B383305
theorem B5786801 : Blo 223812 5786801 := bstep (se 2 (by rfl) ⟨2170050, by rfl⟩ : syracuseStep 5786801 = 4340101) B4340101
theorem B2608307 : Blo 223812 2608307 := bstep (se 1 (by rfl) ⟨1956230, by rfl⟩ : syracuseStep 2608307 = 3912461) B3912461
theorem B511271 : Blo 223812 511271 := bstep (se 1 (by rfl) ⟨383453, by rfl⟩ : syracuseStep 511271 = 766907) B766907
theorem B478561 : Blo 223812 478561 := bstep (se 2 (by rfl) ⟨179460, by rfl⟩ : syracuseStep 478561 = 358921) B358921
theorem B871867 : Blo 223812 871867 := bstep (se 1 (by rfl) ⟨653900, by rfl⟩ : syracuseStep 871867 = 1307801) B1307801
theorem B1134161 : Blo 223812 1134161 := bstep (se 2 (by rfl) ⟨425310, by rfl⟩ : syracuseStep 1134161 = 850621) B850621
theorem B511649 : Blo 223812 511649 := bstep (se 2 (by rfl) ⟨191868, by rfl⟩ : syracuseStep 511649 = 383737) B383737
theorem B380713 : Blo 223812 380713 := bstep (se 2 (by rfl) ⟨142767, by rfl⟩ : syracuseStep 380713 = 285535) B285535
theorem B2576285 : Blo 223812 2576285 := bstep (se 3 (by rfl) ⟨483053, by rfl⟩ : syracuseStep 2576285 = 966107) B966107
theorem B512009 : Blo 223812 512009 := bstep (se 2 (by rfl) ⟨192003, by rfl⟩ : syracuseStep 512009 = 384007) B384007
theorem B544897 : Blo 223812 544897 := bstep (se 2 (by rfl) ⟨204336, by rfl⟩ : syracuseStep 544897 = 408673) B408673
theorem B512423 : Blo 223812 512423 := bstep (se 1 (by rfl) ⟨384317, by rfl⟩ : syracuseStep 512423 = 768635) B768635
theorem B512531 : Blo 223812 512531 := bstep (se 1 (by rfl) ⟨384398, by rfl⟩ : syracuseStep 512531 = 768797) B768797
theorem B381503 : Blo 223812 381503 := bstep (se 1 (by rfl) ⟨286127, by rfl⟩ : syracuseStep 381503 = 572255) B572255
theorem B10998341 : Blo 223812 10998341 := bstep (se 4 (by rfl) ⟨1031094, by rfl⟩ : syracuseStep 10998341 = 2062189) B2062189
theorem B283439 : Blo 223812 283439 := bstep (se 1 (by rfl) ⟨212579, by rfl⟩ : syracuseStep 283439 = 425159) B425159
theorem B3494735 : Blo 223812 3494735 := bstep (se 1 (by rfl) ⟨2621051, by rfl⟩ : syracuseStep 3494735 = 5242103) B5242103
theorem B2315213 : Blo 223812 2315213 := bstep (se 3 (by rfl) ⟨434102, by rfl⟩ : syracuseStep 2315213 = 868205) B868205
theorem B1299671 : Blo 223812 1299671 := bstep (se 1 (by rfl) ⟨974753, by rfl⟩ : syracuseStep 1299671 = 1949507) B1949507
theorem B382171 : Blo 223812 382171 := bstep (se 1 (by rfl) ⟨286628, by rfl⟩ : syracuseStep 382171 = 573257) B573257
theorem B644345 : Blo 223812 644345 := bstep (se 2 (by rfl) ⟨241629, by rfl⟩ : syracuseStep 644345 = 483259) B483259
theorem B1136591 : Blo 223812 1136591 := bstep (se 1 (by rfl) ⟨852443, by rfl⟩ : syracuseStep 1136591 = 1704887) B1704887
theorem B382927 : Blo 223812 382927 := bstep (se 1 (by rfl) ⟨287195, by rfl⟩ : syracuseStep 382927 = 574391) B574391
theorem B2218063 : Blo 223812 2218063 := bstep (se 1 (by rfl) ⟨1663547, by rfl⟩ : syracuseStep 2218063 = 3327095) B3327095
theorem B252283 : Blo 223812 252283 := bstep (se 1 (by rfl) ⟨189212, by rfl⟩ : syracuseStep 252283 = 378425) B378425
theorem B383609 : Blo 223812 383609 := bstep (se 2 (by rfl) ⟨143853, by rfl⟩ : syracuseStep 383609 = 287707) B287707
theorem B383663 : Blo 223812 383663 := bstep (se 1 (by rfl) ⟨287747, by rfl⟩ : syracuseStep 383663 = 575495) B575495
theorem B252751 : Blo 223812 252751 := bstep (se 1 (by rfl) ⟨189563, by rfl⟩ : syracuseStep 252751 = 379127) B379127
theorem B646031 : Blo 223812 646031 := bstep (se 1 (by rfl) ⟨484523, by rfl⟩ : syracuseStep 646031 = 969047) B969047
theorem B1137563 : Blo 223812 1137563 := bstep (se 1 (by rfl) ⟨853172, by rfl⟩ : syracuseStep 1137563 = 1706345) B1706345
theorem B383899 : Blo 223812 383899 := bstep (se 1 (by rfl) ⟨287924, by rfl⟩ : syracuseStep 383899 = 575849) B575849
theorem B1924013 : Blo 223812 1924013 := bstep (se 3 (by rfl) ⟨360752, by rfl⟩ : syracuseStep 1924013 = 721505) B721505
theorem B253147 : Blo 223812 253147 := bstep (se 1 (by rfl) ⟨189860, by rfl⟩ : syracuseStep 253147 = 379721) B379721
theorem B1138049 : Blo 223812 1138049 := bstep (se 2 (by rfl) ⟨426768, by rfl⟩ : syracuseStep 1138049 = 853537) B853537
theorem B253435 : Blo 223812 253435 := bstep (se 1 (by rfl) ⟨190076, by rfl⟩ : syracuseStep 253435 = 380153) B380153
theorem B253615 : Blo 223812 253615 := bstep (se 1 (by rfl) ⟨190211, by rfl⟩ : syracuseStep 253615 = 380423) B380423
theorem B581431 : Blo 223812 581431 := bstep (se 1 (by rfl) ⟨436073, by rfl⟩ : syracuseStep 581431 = 872147) B872147
theorem B253903 : Blo 223812 253903 := bstep (se 1 (by rfl) ⟨190427, by rfl⟩ : syracuseStep 253903 = 380855) B380855
theorem B2908163 : Blo 223812 2908163 := bstep (se 1 (by rfl) ⟨2181122, by rfl⟩ : syracuseStep 2908163 = 4362245) B4362245
theorem B1138697 : Blo 223812 1138697 := bstep (se 2 (by rfl) ⟨427011, by rfl⟩ : syracuseStep 1138697 = 854023) B854023
theorem B1138859 : Blo 223812 1138859 := bstep (se 1 (by rfl) ⟨854144, by rfl⟩ : syracuseStep 1138859 = 1708289) B1708289
theorem B4645181 : Blo 223812 4645181 := bstep (se 3 (by rfl) ⟨870971, by rfl⟩ : syracuseStep 4645181 = 1741943) B1741943
theorem B254299 : Blo 223812 254299 := bstep (se 1 (by rfl) ⟨190724, by rfl⟩ : syracuseStep 254299 = 381449) B381449
theorem B254407 : Blo 223812 254407 := bstep (se 1 (by rfl) ⟨190805, by rfl⟩ : syracuseStep 254407 = 381611) B381611
theorem B287327 : Blo 223812 287327 := bstep (se 1 (by rfl) ⟨215495, by rfl⟩ : syracuseStep 287327 = 430991) B430991
theorem B1139345 : Blo 223812 1139345 := bstep (se 2 (by rfl) ⟨427254, by rfl⟩ : syracuseStep 1139345 = 854509) B854509
theorem B2482859 : Blo 223812 2482859 := bstep (se 1 (by rfl) ⟨1862144, by rfl⟩ : syracuseStep 2482859 = 3724289) B3724289
theorem B254767 : Blo 223812 254767 := bstep (se 1 (by rfl) ⟨191075, by rfl⟩ : syracuseStep 254767 = 382151) B382151
theorem B254875 : Blo 223812 254875 := bstep (se 1 (by rfl) ⟨191156, by rfl⟩ : syracuseStep 254875 = 382313) B382313
theorem B3105985 : Blo 223812 3105985 := bstep (se 2 (by rfl) ⟨1164744, by rfl⟩ : syracuseStep 3105985 = 2329489) B2329489
theorem B288031 : Blo 223812 288031 := bstep (se 1 (by rfl) ⟨216023, by rfl⟩ : syracuseStep 288031 = 432047) B432047
theorem B255271 : Blo 223812 255271 := bstep (se 1 (by rfl) ⟨191453, by rfl⟩ : syracuseStep 255271 = 382907) B382907
theorem B255343 : Blo 223812 255343 := bstep (se 1 (by rfl) ⟨191507, by rfl⟩ : syracuseStep 255343 = 383015) B383015
theorem B2876795 : Blo 223812 2876795 := bstep (se 1 (by rfl) ⟨2157596, by rfl⟩ : syracuseStep 2876795 = 4315193) B4315193
theorem B255559 : Blo 223812 255559 := bstep (se 1 (by rfl) ⟨191669, by rfl⟩ : syracuseStep 255559 = 383339) B383339
theorem B1926989 : Blo 223812 1926989 := bstep (se 3 (by rfl) ⟨361310, by rfl⟩ : syracuseStep 1926989 = 722621) B722621
theorem B485327 : Blo 223812 485327 := bstep (se 1 (by rfl) ⟨363995, by rfl⟩ : syracuseStep 485327 = 727991) B727991
theorem B1370297 : Blo 223812 1370297 := bstep (se 2 (by rfl) ⟨513861, by rfl⟩ : syracuseStep 1370297 = 1027723) B1027723
theorem B682265 : Blo 223812 682265 := bstep (se 2 (by rfl) ⟨255849, by rfl⟩ : syracuseStep 682265 = 511699) B511699
theorem B584119 : Blo 223812 584119 := bstep (se 1 (by rfl) ⟨438089, by rfl⟩ : syracuseStep 584119 = 876179) B876179
theorem B223815 : Blo 223812 223815 := bstep (se 1 (by rfl) ⟨167861, by rfl⟩ : syracuseStep 223815 = 335723) B335723
theorem B485959 : Blo 223812 485959 := bstep (se 1 (by rfl) ⟨364469, by rfl⟩ : syracuseStep 485959 = 728939) B728939
theorem B584263 : Blo 223812 584263 := bstep (se 1 (by rfl) ⟨438197, by rfl⟩ : syracuseStep 584263 = 876395) B876395
theorem B4877009 : Blo 223812 4877009 := bstep (se 2 (by rfl) ⟨1828878, by rfl⟩ : syracuseStep 4877009 = 3657757) B3657757
theorem B223967 : Blo 223812 223967 := bstep (se 1 (by rfl) ⟨167975, by rfl⟩ : syracuseStep 223967 = 335951) B335951
theorem B1436449 : Blo 223812 1436449 := bstep (se 2 (by rfl) ⟨538668, by rfl⟩ : syracuseStep 1436449 = 1077337) B1077337
theorem B224047 : Blo 223812 224047 := bstep (se 1 (by rfl) ⟨168035, by rfl⟩ : syracuseStep 224047 = 336071) B336071
theorem B224155 : Blo 223812 224155 := bstep (se 1 (by rfl) ⟨168116, by rfl⟩ : syracuseStep 224155 = 336233) B336233
theorem B224207 : Blo 223812 224207 := bstep (se 1 (by rfl) ⟨168155, by rfl⟩ : syracuseStep 224207 = 336311) B336311
theorem B224231 : Blo 223812 224231 := bstep (se 1 (by rfl) ⟨168173, by rfl⟩ : syracuseStep 224231 = 336347) B336347
theorem B1141775 : Blo 223812 1141775 := bstep (se 1 (by rfl) ⟨856331, by rfl⟩ : syracuseStep 1141775 = 1712663) B1712663
theorem B453919 : Blo 223812 453919 := bstep (se 1 (by rfl) ⟨340439, by rfl⟩ : syracuseStep 453919 = 680879) B680879
theorem B224543 : Blo 223812 224543 := bstep (se 1 (by rfl) ⟨168407, by rfl⟩ : syracuseStep 224543 = 336815) B336815
theorem B224603 : Blo 223812 224603 := bstep (se 1 (by rfl) ⟨168452, by rfl⟩ : syracuseStep 224603 = 336905) B336905
theorem B224623 : Blo 223812 224623 := bstep (se 1 (by rfl) ⟨168467, by rfl⟩ : syracuseStep 224623 = 336935) B336935
theorem B224679 : Blo 223812 224679 := bstep (se 1 (by rfl) ⟨168509, by rfl⟩ : syracuseStep 224679 = 337019) B337019
theorem B224763 : Blo 223812 224763 := bstep (se 1 (by rfl) ⟨168572, by rfl⟩ : syracuseStep 224763 = 337145) B337145
theorem B814607 : Blo 223812 814607 := bstep (se 1 (by rfl) ⟨610955, by rfl⟩ : syracuseStep 814607 = 1221911) B1221911
theorem B3501629 : Blo 223812 3501629 := bstep (se 3 (by rfl) ⟨656555, by rfl⟩ : syracuseStep 3501629 = 1313111) B1313111
theorem B224831 : Blo 223812 224831 := bstep (se 1 (by rfl) ⟨168623, by rfl⟩ : syracuseStep 224831 = 337247) B337247
theorem B224839 : Blo 223812 224839 := bstep (se 1 (by rfl) ⟨168629, by rfl⟩ : syracuseStep 224839 = 337259) B337259
theorem B224991 : Blo 223812 224991 := bstep (se 1 (by rfl) ⟨168743, by rfl⟩ : syracuseStep 224991 = 337487) B337487
theorem B225071 : Blo 223812 225071 := bstep (se 1 (by rfl) ⟨168803, by rfl⟩ : syracuseStep 225071 = 337607) B337607
theorem B1142585 : Blo 223812 1142585 := bstep (se 2 (by rfl) ⟨428469, by rfl⟩ : syracuseStep 1142585 = 856939) B856939
theorem B225179 : Blo 223812 225179 := bstep (se 1 (by rfl) ⟨168884, by rfl⟩ : syracuseStep 225179 = 337769) B337769
theorem B225231 : Blo 223812 225231 := bstep (se 1 (by rfl) ⟨168923, by rfl⟩ : syracuseStep 225231 = 337847) B337847
theorem B225255 : Blo 223812 225255 := bstep (se 1 (by rfl) ⟨168941, by rfl⟩ : syracuseStep 225255 = 337883) B337883
theorem B4616279 : Blo 223812 4616279 := bstep (se 1 (by rfl) ⟨3462209, by rfl⟩ : syracuseStep 4616279 = 6924419) B6924419
theorem B225567 : Blo 223812 225567 := bstep (se 1 (by rfl) ⟨169175, by rfl⟩ : syracuseStep 225567 = 338351) B338351
theorem B225627 : Blo 223812 225627 := bstep (se 1 (by rfl) ⟨169220, by rfl⟩ : syracuseStep 225627 = 338441) B338441
theorem B225647 : Blo 223812 225647 := bstep (se 1 (by rfl) ⟨169235, by rfl⟩ : syracuseStep 225647 = 338471) B338471
theorem B225703 : Blo 223812 225703 := bstep (se 1 (by rfl) ⟨169277, by rfl⟩ : syracuseStep 225703 = 338555) B338555
theorem B225787 : Blo 223812 225787 := bstep (se 1 (by rfl) ⟨169340, by rfl⟩ : syracuseStep 225787 = 338681) B338681
theorem B225855 : Blo 223812 225855 := bstep (se 1 (by rfl) ⟨169391, by rfl⟩ : syracuseStep 225855 = 338783) B338783
theorem B225863 : Blo 223812 225863 := bstep (se 1 (by rfl) ⟨169397, by rfl⟩ : syracuseStep 225863 = 338795) B338795
theorem B226015 : Blo 223812 226015 := bstep (se 1 (by rfl) ⟨169511, by rfl⟩ : syracuseStep 226015 = 339023) B339023
theorem B1930027 : Blo 223812 1930027 := bstep (se 1 (by rfl) ⟨1447520, by rfl⟩ : syracuseStep 1930027 = 2895041) B2895041
theorem B226095 : Blo 223812 226095 := bstep (se 1 (by rfl) ⟨169571, by rfl⟩ : syracuseStep 226095 = 339143) B339143
theorem B226203 : Blo 223812 226203 := bstep (se 1 (by rfl) ⟨169652, by rfl⟩ : syracuseStep 226203 = 339305) B339305
theorem B226255 : Blo 223812 226255 := bstep (se 1 (by rfl) ⟨169691, by rfl⟩ : syracuseStep 226255 = 339383) B339383
theorem B226279 : Blo 223812 226279 := bstep (se 1 (by rfl) ⟨169709, by rfl⟩ : syracuseStep 226279 = 339419) B339419
theorem B717815 : Blo 223812 717815 := bstep (se 1 (by rfl) ⟨538361, by rfl⟩ : syracuseStep 717815 = 1076723) B1076723
theorem B2552957 : Blo 223812 2552957 := bstep (se 3 (by rfl) ⟨478679, by rfl⟩ : syracuseStep 2552957 = 957359) B957359
theorem B1078397 : Blo 223812 1078397 := bstep (se 3 (by rfl) ⟨202199, by rfl⟩ : syracuseStep 1078397 = 404399) B404399
theorem B4846837 : Blo 223812 4846837 := bstep (se 5 (by rfl) ⟨227195, by rfl⟩ : syracuseStep 4846837 = 454391) B454391
theorem B8189207 : Blo 223812 8189207 := bstep (se 1 (by rfl) ⟨6141905, by rfl⟩ : syracuseStep 8189207 = 12283811) B12283811
theorem B226591 : Blo 223812 226591 := bstep (se 1 (by rfl) ⟨169943, by rfl⟩ : syracuseStep 226591 = 339887) B339887
theorem B2061607 : Blo 223812 2061607 := bstep (se 1 (by rfl) ⟨1546205, by rfl⟩ : syracuseStep 2061607 = 3092411) B3092411
theorem B226651 : Blo 223812 226651 := bstep (se 1 (by rfl) ⟨169988, by rfl⟩ : syracuseStep 226651 = 339977) B339977
theorem B226671 : Blo 223812 226671 := bstep (se 1 (by rfl) ⟨170003, by rfl⟩ : syracuseStep 226671 = 340007) B340007
theorem B226727 : Blo 223812 226727 := bstep (se 1 (by rfl) ⟨170045, by rfl⟩ : syracuseStep 226727 = 340091) B340091
theorem B226811 : Blo 223812 226811 := bstep (se 1 (by rfl) ⟨170108, by rfl⟩ : syracuseStep 226811 = 340217) B340217
theorem B226879 : Blo 223812 226879 := bstep (se 1 (by rfl) ⟨170159, by rfl⟩ : syracuseStep 226879 = 340319) B340319
theorem B226887 : Blo 223812 226887 := bstep (se 1 (by rfl) ⟨170165, by rfl⟩ : syracuseStep 226887 = 340331) B340331
theorem B227039 : Blo 223812 227039 := bstep (se 1 (by rfl) ⟨170279, by rfl⟩ : syracuseStep 227039 = 340559) B340559
theorem B227119 : Blo 223812 227119 := bstep (se 1 (by rfl) ⟨170339, by rfl⟩ : syracuseStep 227119 = 340679) B340679
theorem B3667805 : Blo 223812 3667805 := bstep (se 3 (by rfl) ⟨687713, by rfl⟩ : syracuseStep 3667805 = 1375427) B1375427
theorem B227227 : Blo 223812 227227 := bstep (se 1 (by rfl) ⟨170420, by rfl⟩ : syracuseStep 227227 = 340841) B340841
theorem B227279 : Blo 223812 227279 := bstep (se 1 (by rfl) ⟨170459, by rfl⟩ : syracuseStep 227279 = 340919) B340919
theorem B227303 : Blo 223812 227303 := bstep (se 1 (by rfl) ⟨170477, by rfl⟩ : syracuseStep 227303 = 340955) B340955
theorem B849953 : Blo 223812 849953 := bstep (se 2 (by rfl) ⟨318732, by rfl⟩ : syracuseStep 849953 = 637465) B637465
theorem B1210621 : Blo 223812 1210621 := bstep (se 3 (by rfl) ⟨226991, by rfl⟩ : syracuseStep 1210621 = 453983) B453983
theorem B227615 : Blo 223812 227615 := bstep (se 1 (by rfl) ⟨170711, by rfl⟩ : syracuseStep 227615 = 341423) B341423
theorem B227675 : Blo 223812 227675 := bstep (se 1 (by rfl) ⟨170756, by rfl⟩ : syracuseStep 227675 = 341513) B341513
theorem B227695 : Blo 223812 227695 := bstep (se 1 (by rfl) ⟨170771, by rfl⟩ : syracuseStep 227695 = 341543) B341543
theorem B227751 : Blo 223812 227751 := bstep (se 1 (by rfl) ⟨170813, by rfl⟩ : syracuseStep 227751 = 341627) B341627
theorem B1276343 : Blo 223812 1276343 := bstep (se 1 (by rfl) ⟨957257, by rfl⟩ : syracuseStep 1276343 = 1914515) B1914515
theorem B293371 : Blo 223812 293371 := bstep (se 1 (by rfl) ⟨220028, by rfl⟩ : syracuseStep 293371 = 440057) B440057
theorem B1145339 : Blo 223812 1145339 := bstep (se 1 (by rfl) ⟨859004, by rfl⟩ : syracuseStep 1145339 = 1718009) B1718009
theorem B358985 : Blo 223812 358985 := bstep (se 2 (by rfl) ⟨134619, by rfl⟩ : syracuseStep 358985 = 269239) B269239
theorem B850607 : Blo 223812 850607 := bstep (se 1 (by rfl) ⟨637955, by rfl⟩ : syracuseStep 850607 = 1275911) B1275911
theorem B1080029 : Blo 223812 1080029 := bstep (se 3 (by rfl) ⟨202505, by rfl⟩ : syracuseStep 1080029 = 405011) B405011
theorem B4651931 : Blo 223812 4651931 := bstep (se 1 (by rfl) ⟨3488948, by rfl⟩ : syracuseStep 4651931 = 6977897) B6977897
theorem B1277117 : Blo 223812 1277117 := bstep (se 3 (by rfl) ⟨239459, by rfl⟩ : syracuseStep 1277117 = 478919) B478919
theorem B10911149 : Blo 223812 10911149 := bstep (se 3 (by rfl) ⟨2045840, by rfl⟩ : syracuseStep 10911149 = 4091681) B4091681
theorem B1146311 : Blo 223812 1146311 := bstep (se 1 (by rfl) ⟨859733, by rfl⟩ : syracuseStep 1146311 = 1719467) B1719467
theorem B1080857 : Blo 223812 1080857 := bstep (se 2 (by rfl) ⟨405321, by rfl⟩ : syracuseStep 1080857 = 810643) B810643
theorem B1146635 : Blo 223812 1146635 := bstep (se 1 (by rfl) ⟨859976, by rfl⟩ : syracuseStep 1146635 = 1719953) B1719953
theorem B67927853 : Blo 223812 67927853 := bstep (se 3 (by rfl) ⟨12736472, by rfl⟩ : syracuseStep 67927853 = 25472945) B25472945
theorem B1146959 : Blo 223812 1146959 := bstep (se 1 (by rfl) ⟨860219, by rfl⟩ : syracuseStep 1146959 = 1720439) B1720439
theorem B426215 : Blo 223812 426215 := bstep (se 1 (by rfl) ⟨319661, by rfl⟩ : syracuseStep 426215 = 639323) B639323
theorem B721403 : Blo 223812 721403 := bstep (se 1 (by rfl) ⟨541052, by rfl⟩ : syracuseStep 721403 = 1082105) B1082105
theorem B2196233 : Blo 223812 2196233 := bstep (se 2 (by rfl) ⟨823587, by rfl⟩ : syracuseStep 2196233 = 1647175) B1647175
theorem B426799 : Blo 223812 426799 := bstep (se 1 (by rfl) ⟨320099, by rfl⟩ : syracuseStep 426799 = 640199) B640199
theorem B1835885 : Blo 223812 1835885 := bstep (se 3 (by rfl) ⟨344228, by rfl⟩ : syracuseStep 1835885 = 688457) B688457
theorem B853051 : Blo 223812 853051 := bstep (se 1 (by rfl) ⟨639788, by rfl⟩ : syracuseStep 853051 = 1279577) B1279577
theorem B1541387 : Blo 223812 1541387 := bstep (se 1 (by rfl) ⟨1156040, by rfl⟩ : syracuseStep 1541387 = 2312081) B2312081
theorem B722429 : Blo 223812 722429 := bstep (se 3 (by rfl) ⟨135455, by rfl⟩ : syracuseStep 722429 = 270911) B270911
theorem B853523 : Blo 223812 853523 := bstep (se 1 (by rfl) ⟨640142, by rfl⟩ : syracuseStep 853523 = 1280285) B1280285
theorem B6620957 : Blo 223812 6620957 := bstep (se 3 (by rfl) ⟨1241429, by rfl⟩ : syracuseStep 6620957 = 2482859) B2482859
theorem B427855 : Blo 223812 427855 := bstep (se 1 (by rfl) ⟨320891, by rfl⟩ : syracuseStep 427855 = 641783) B641783
theorem B1738871 : Blo 223812 1738871 := bstep (se 1 (by rfl) ⟨1304153, by rfl⟩ : syracuseStep 1738871 = 2608307) B2608307
theorem B755837 : Blo 223812 755837 := bstep (se 3 (by rfl) ⟨141719, by rfl⟩ : syracuseStep 755837 = 283439) B283439
theorem B460991 : Blo 223812 460991 := bstep (se 1 (by rfl) ⟨345743, by rfl⟩ : syracuseStep 460991 = 691487) B691487
theorem B756107 : Blo 223812 756107 := bstep (se 1 (by rfl) ⟨567080, by rfl⟩ : syracuseStep 756107 = 1134161) B1134161
theorem B4917833 : Blo 223812 4917833 := bstep (se 2 (by rfl) ⟨1844187, by rfl⟩ : syracuseStep 4917833 = 3688375) B3688375
theorem B1444499 : Blo 223812 1444499 := bstep (se 1 (by rfl) ⟨1083374, by rfl⟩ : syracuseStep 1444499 = 2166749) B2166749
theorem B2329823 : Blo 223812 2329823 := bstep (se 1 (by rfl) ⟨1747367, by rfl⟩ : syracuseStep 2329823 = 3494735) B3494735
theorem B1543475 : Blo 223812 1543475 := bstep (se 1 (by rfl) ⟨1157606, by rfl⟩ : syracuseStep 1543475 = 2315213) B2315213
theorem B1379663 : Blo 223812 1379663 := bstep (se 1 (by rfl) ⟨1034747, by rfl⟩ : syracuseStep 1379663 = 2069495) B2069495
theorem B429563 : Blo 223812 429563 := bstep (se 1 (by rfl) ⟨322172, by rfl⟩ : syracuseStep 429563 = 644345) B644345
theorem B757727 : Blo 223812 757727 := bstep (se 1 (by rfl) ⟨568295, by rfl⟩ : syracuseStep 757727 = 1136591) B1136591
theorem B757889 : Blo 223812 757889 := bstep (se 2 (by rfl) ⟨284208, by rfl⟩ : syracuseStep 757889 = 568417) B568417
theorem B430687 : Blo 223812 430687 := bstep (se 1 (by rfl) ⟨323015, by rfl⟩ : syracuseStep 430687 = 646031) B646031
theorem B758375 : Blo 223812 758375 := bstep (se 1 (by rfl) ⟨568781, by rfl⟩ : syracuseStep 758375 = 1137563) B1137563
theorem B1282675 : Blo 223812 1282675 := bstep (se 1 (by rfl) ⟨962006, by rfl⟩ : syracuseStep 1282675 = 1924013) B1924013
theorem B529193 : Blo 223812 529193 := bstep (se 2 (by rfl) ⟨198447, by rfl⟩ : syracuseStep 529193 = 396895) B396895
theorem B758699 : Blo 223812 758699 := bstep (se 1 (by rfl) ⟨569024, by rfl⟩ : syracuseStep 758699 = 1138049) B1138049
theorem B1938775 : Blo 223812 1938775 := bstep (se 1 (by rfl) ⟨1454081, by rfl⟩ : syracuseStep 1938775 = 2908163) B2908163
theorem B759131 : Blo 223812 759131 := bstep (se 1 (by rfl) ⟨569348, by rfl⟩ : syracuseStep 759131 = 1138697) B1138697
theorem B759239 : Blo 223812 759239 := bstep (se 1 (by rfl) ⟨569429, by rfl⟩ : syracuseStep 759239 = 1138859) B1138859
theorem B726529 : Blo 223812 726529 := bstep (se 2 (by rfl) ⟨272448, by rfl⟩ : syracuseStep 726529 = 544897) B544897
theorem B759563 : Blo 223812 759563 := bstep (se 1 (by rfl) ⟨569672, by rfl⟩ : syracuseStep 759563 = 1139345) B1139345
theorem B759833 : Blo 223812 759833 := bstep (se 2 (by rfl) ⟨284937, by rfl⟩ : syracuseStep 759833 = 569875) B569875
theorem B1284659 : Blo 223812 1284659 := bstep (se 1 (by rfl) ⟨963494, by rfl⟩ : syracuseStep 1284659 = 1926989) B1926989
theorem B11082419 : Blo 223812 11082419 := bstep (se 1 (by rfl) ⟨8311814, by rfl⟩ : syracuseStep 11082419 = 16623629) B16623629
theorem B6462449 : Blo 223812 6462449 := bstep (se 2 (by rfl) ⟨2423418, by rfl⟩ : syracuseStep 6462449 = 4846837) B4846837
theorem B3251339 : Blo 223812 3251339 := bstep (se 1 (by rfl) ⟨2438504, by rfl⟩ : syracuseStep 3251339 = 4877009) B4877009
theorem B761183 : Blo 223812 761183 := bstep (se 1 (by rfl) ⟨570887, by rfl⟩ : syracuseStep 761183 = 1141775) B1141775
theorem B2334419 : Blo 223812 2334419 := bstep (se 1 (by rfl) ⟨1750814, by rfl⟩ : syracuseStep 2334419 = 3501629) B3501629
theorem B761723 : Blo 223812 761723 := bstep (se 1 (by rfl) ⟨571292, by rfl⟩ : syracuseStep 761723 = 1142585) B1142585
theorem B335771 : Blo 223812 335771 := bstep (se 1 (by rfl) ⟨251828, by rfl⟩ : syracuseStep 335771 = 503657) B503657
theorem B1286117 : Blo 223812 1286117 := bstep (se 4 (by rfl) ⟨120573, by rfl⟩ : syracuseStep 1286117 = 241147) B241147
theorem B2957417 : Blo 223812 2957417 := bstep (se 2 (by rfl) ⟨1109031, by rfl⟩ : syracuseStep 2957417 = 2218063) B2218063
theorem B2433311 : Blo 223812 2433311 := bstep (se 1 (by rfl) ⟨1824983, by rfl⟩ : syracuseStep 2433311 = 3649967) B3649967
theorem B1614161 : Blo 223812 1614161 := bstep (se 2 (by rfl) ⟨605310, by rfl⟩ : syracuseStep 1614161 = 1210621) B1210621
theorem B762209 : Blo 223812 762209 := bstep (se 2 (by rfl) ⟨285828, by rfl⟩ : syracuseStep 762209 = 571657) B571657
theorem B336335 : Blo 223812 336335 := bstep (se 1 (by rfl) ⟨252251, by rfl⟩ : syracuseStep 336335 = 504503) B504503
theorem B336377 : Blo 223812 336377 := bstep (se 2 (by rfl) ⟨126141, by rfl⟩ : syracuseStep 336377 = 252283) B252283
theorem B336479 : Blo 223812 336479 := bstep (se 1 (by rfl) ⟨252359, by rfl⟩ : syracuseStep 336479 = 504719) B504719
theorem B1450649 : Blo 223812 1450649 := bstep (se 2 (by rfl) ⟨543993, by rfl⟩ : syracuseStep 1450649 = 1087987) B1087987
theorem B1581935 : Blo 223812 1581935 := bstep (se 1 (by rfl) ⟨1186451, by rfl⟩ : syracuseStep 1581935 = 2372903) B2372903
theorem B336959 : Blo 223812 336959 := bstep (se 1 (by rfl) ⟨252719, by rfl⟩ : syracuseStep 336959 = 505439) B505439
theorem B337001 : Blo 223812 337001 := bstep (se 2 (by rfl) ⟨126375, by rfl⟩ : syracuseStep 337001 = 252751) B252751
theorem B337103 : Blo 223812 337103 := bstep (se 1 (by rfl) ⟨252827, by rfl⟩ : syracuseStep 337103 = 505655) B505655
theorem B566635 : Blo 223812 566635 := bstep (se 1 (by rfl) ⟨424976, by rfl⟩ : syracuseStep 566635 = 849953) B849953
theorem B337307 : Blo 223812 337307 := bstep (se 1 (by rfl) ⟨252980, by rfl⟩ : syracuseStep 337307 = 505961) B505961
theorem B337529 : Blo 223812 337529 := bstep (se 2 (by rfl) ⟨126573, by rfl⟩ : syracuseStep 337529 = 253147) B253147
theorem B763559 : Blo 223812 763559 := bstep (se 1 (by rfl) ⟨572669, by rfl⟩ : syracuseStep 763559 = 1145339) B1145339
theorem B239323 : Blo 223812 239323 := bstep (se 1 (by rfl) ⟨179492, by rfl⟩ : syracuseStep 239323 = 358985) B358985
theorem B337631 : Blo 223812 337631 := bstep (se 1 (by rfl) ⟨253223, by rfl⟩ : syracuseStep 337631 = 506447) B506447
theorem B567071 : Blo 223812 567071 := bstep (se 1 (by rfl) ⟨425303, by rfl⟩ : syracuseStep 567071 = 850607) B850607
theorem B337727 : Blo 223812 337727 := bstep (se 1 (by rfl) ⟨253295, by rfl⟩ : syracuseStep 337727 = 506591) B506591
theorem B1714121 : Blo 223812 1714121 := bstep (se 2 (by rfl) ⟨642795, by rfl⟩ : syracuseStep 1714121 = 1285591) B1285591
theorem B337895 : Blo 223812 337895 := bstep (se 1 (by rfl) ⟨253421, by rfl⟩ : syracuseStep 337895 = 506843) B506843
theorem B337913 : Blo 223812 337913 := bstep (se 2 (by rfl) ⟨126717, by rfl⟩ : syracuseStep 337913 = 253435) B253435
theorem B338015 : Blo 223812 338015 := bstep (se 1 (by rfl) ⟨253511, by rfl⟩ : syracuseStep 338015 = 507023) B507023
theorem B829549 : Blo 223812 829549 := bstep (se 3 (by rfl) ⟨155540, by rfl⟩ : syracuseStep 829549 = 311081) B311081
theorem B338075 : Blo 223812 338075 := bstep (se 1 (by rfl) ⟨253556, by rfl⟩ : syracuseStep 338075 = 507113) B507113
theorem B338111 : Blo 223812 338111 := bstep (se 1 (by rfl) ⟨253583, by rfl⟩ : syracuseStep 338111 = 507167) B507167
theorem B338153 : Blo 223812 338153 := bstep (se 2 (by rfl) ⟨126807, by rfl⟩ : syracuseStep 338153 = 253615) B253615
theorem B764153 : Blo 223812 764153 := bstep (se 2 (by rfl) ⟨286557, by rfl⟩ : syracuseStep 764153 = 573115) B573115
theorem B764207 : Blo 223812 764207 := bstep (se 1 (by rfl) ⟨573155, by rfl⟩ : syracuseStep 764207 = 1146311) B1146311
theorem B862559 : Blo 223812 862559 := bstep (se 1 (by rfl) ⟨646919, by rfl⟩ : syracuseStep 862559 = 1293839) B1293839
theorem B764423 : Blo 223812 764423 := bstep (se 1 (by rfl) ⟨573317, by rfl⟩ : syracuseStep 764423 = 1146635) B1146635
theorem B338459 : Blo 223812 338459 := bstep (se 1 (by rfl) ⟨253844, by rfl⟩ : syracuseStep 338459 = 507689) B507689
theorem B338537 : Blo 223812 338537 := bstep (se 2 (by rfl) ⟨126951, by rfl⟩ : syracuseStep 338537 = 253903) B253903
theorem B3091051 : Blo 223812 3091051 := bstep (se 1 (by rfl) ⟨2318288, by rfl⟩ : syracuseStep 3091051 = 4636577) B4636577
theorem B895799 : Blo 223812 895799 := bstep (se 1 (by rfl) ⟨671849, by rfl⟩ : syracuseStep 895799 = 1343699) B1343699
theorem B1616699 : Blo 223812 1616699 := bstep (se 1 (by rfl) ⟨1212524, by rfl⟩ : syracuseStep 1616699 = 2425049) B2425049
theorem B568367 : Blo 223812 568367 := bstep (se 1 (by rfl) ⟨426275, by rfl⟩ : syracuseStep 568367 = 852551) B852551
theorem B339065 : Blo 223812 339065 := bstep (se 2 (by rfl) ⟨127149, by rfl⟩ : syracuseStep 339065 = 254299) B254299
theorem B765071 : Blo 223812 765071 := bstep (se 1 (by rfl) ⟨573803, by rfl⟩ : syracuseStep 765071 = 1147607) B1147607
theorem B339167 : Blo 223812 339167 := bstep (se 1 (by rfl) ⟨254375, by rfl⟩ : syracuseStep 339167 = 508751) B508751
theorem B339209 : Blo 223812 339209 := bstep (se 2 (by rfl) ⟨127203, by rfl⟩ : syracuseStep 339209 = 254407) B254407
theorem B863531 : Blo 223812 863531 := bstep (se 1 (by rfl) ⟨647648, by rfl⟩ : syracuseStep 863531 = 1295297) B1295297
theorem B1092973 : Blo 223812 1092973 := bstep (se 3 (by rfl) ⟨204932, by rfl⟩ : syracuseStep 1092973 = 409865) B409865
theorem B339311 : Blo 223812 339311 := bstep (se 1 (by rfl) ⟨254483, by rfl⟩ : syracuseStep 339311 = 508967) B508967
theorem B339431 : Blo 223812 339431 := bstep (se 1 (by rfl) ⟨254573, by rfl⟩ : syracuseStep 339431 = 509147) B509147
theorem B765503 : Blo 223812 765503 := bstep (se 1 (by rfl) ⟨574127, by rfl⟩ : syracuseStep 765503 = 1148255) B1148255
theorem B9940553 : Blo 223812 9940553 := bstep (se 2 (by rfl) ⟨3727707, by rfl⟩ : syracuseStep 9940553 = 7455415) B7455415
theorem B339563 : Blo 223812 339563 := bstep (se 1 (by rfl) ⟨254672, by rfl⟩ : syracuseStep 339563 = 509345) B509345
theorem B339689 : Blo 223812 339689 := bstep (se 2 (by rfl) ⟨127383, by rfl⟩ : syracuseStep 339689 = 254767) B254767
theorem B339833 : Blo 223812 339833 := bstep (se 2 (by rfl) ⟨127437, by rfl⟩ : syracuseStep 339833 = 254875) B254875
theorem B569227 : Blo 223812 569227 := bstep (se 1 (by rfl) ⟨426920, by rfl⟩ : syracuseStep 569227 = 853841) B853841
theorem B339935 : Blo 223812 339935 := bstep (se 1 (by rfl) ⟨254951, by rfl⟩ : syracuseStep 339935 = 509903) B509903
theorem B8859779 : Blo 223812 8859779 := bstep (se 1 (by rfl) ⟨6644834, by rfl⟩ : syracuseStep 8859779 = 13289669) B13289669
theorem B17576099 : Blo 223812 17576099 := bstep (se 1 (by rfl) ⟨13182074, by rfl⟩ : syracuseStep 17576099 = 26364149) B26364149
theorem B569531 : Blo 223812 569531 := bstep (se 1 (by rfl) ⟨427148, by rfl⟩ : syracuseStep 569531 = 854297) B854297
theorem B340187 : Blo 223812 340187 := bstep (se 1 (by rfl) ⟨255140, by rfl⟩ : syracuseStep 340187 = 510281) B510281
theorem B340199 : Blo 223812 340199 := bstep (se 1 (by rfl) ⟨255149, by rfl⟩ : syracuseStep 340199 = 510299) B510299
theorem B766205 : Blo 223812 766205 := bstep (se 3 (by rfl) ⟨143663, by rfl⟩ : syracuseStep 766205 = 287327) B287327
theorem B4141313 : Blo 223812 4141313 := bstep (se 2 (by rfl) ⟨1552992, by rfl⟩ : syracuseStep 4141313 = 3105985) B3105985
theorem B340361 : Blo 223812 340361 := bstep (se 2 (by rfl) ⟨127635, by rfl⟩ : syracuseStep 340361 = 255271) B255271
theorem B340457 : Blo 223812 340457 := bstep (se 2 (by rfl) ⟨127671, by rfl⟩ : syracuseStep 340457 = 255343) B255343
theorem B340583 : Blo 223812 340583 := bstep (se 1 (by rfl) ⟨255437, by rfl⟩ : syracuseStep 340583 = 510875) B510875
theorem B570017 : Blo 223812 570017 := bstep (se 2 (by rfl) ⟨213756, by rfl⟩ : syracuseStep 570017 = 427513) B427513
theorem B1290923 : Blo 223812 1290923 := bstep (se 1 (by rfl) ⟨968192, by rfl⟩ : syracuseStep 1290923 = 1936385) B1936385
theorem B1159901 : Blo 223812 1159901 := bstep (se 3 (by rfl) ⟨217481, by rfl⟩ : syracuseStep 1159901 = 434963) B434963
theorem B340715 : Blo 223812 340715 := bstep (se 1 (by rfl) ⟨255536, by rfl⟩ : syracuseStep 340715 = 511073) B511073
theorem B340745 : Blo 223812 340745 := bstep (se 2 (by rfl) ⟨127779, by rfl⟩ : syracuseStep 340745 = 255559) B255559
theorem B766745 : Blo 223812 766745 := bstep (se 2 (by rfl) ⟨287529, by rfl⟩ : syracuseStep 766745 = 575059) B575059
theorem B340847 : Blo 223812 340847 := bstep (se 1 (by rfl) ⟨255635, by rfl⟩ : syracuseStep 340847 = 511271) B511271
theorem B504827 : Blo 223812 504827 := bstep (se 1 (by rfl) ⟨378620, by rfl⟩ : syracuseStep 504827 = 757241) B757241
theorem B767015 : Blo 223812 767015 := bstep (se 1 (by rfl) ⟨575261, by rfl⟩ : syracuseStep 767015 = 1150523) B1150523
theorem B341099 : Blo 223812 341099 := bstep (se 1 (by rfl) ⟨255824, by rfl⟩ : syracuseStep 341099 = 511649) B511649
theorem B505007 : Blo 223812 505007 := bstep (se 1 (by rfl) ⟨378755, by rfl⟩ : syracuseStep 505007 = 757511) B757511
theorem B505043 : Blo 223812 505043 := bstep (se 1 (by rfl) ⟨378782, by rfl⟩ : syracuseStep 505043 = 757565) B757565
theorem B1717523 : Blo 223812 1717523 := bstep (se 1 (by rfl) ⟨1288142, by rfl⟩ : syracuseStep 1717523 = 2576285) B2576285
theorem B341339 : Blo 223812 341339 := bstep (se 1 (by rfl) ⟨256004, by rfl⟩ : syracuseStep 341339 = 512009) B512009
theorem B505313 : Blo 223812 505313 := bstep (se 2 (by rfl) ⟨189492, by rfl⟩ : syracuseStep 505313 = 378985) B378985
theorem B341615 : Blo 223812 341615 := bstep (se 1 (by rfl) ⟨256211, by rfl⟩ : syracuseStep 341615 = 512423) B512423
theorem B341687 : Blo 223812 341687 := bstep (se 1 (by rfl) ⟨256265, by rfl⟩ : syracuseStep 341687 = 512531) B512531
theorem B964331 : Blo 223812 964331 := bstep (se 1 (by rfl) ⟨723248, by rfl⟩ : syracuseStep 964331 = 1446497) B1446497
theorem B964399 : Blo 223812 964399 := bstep (se 1 (by rfl) ⟨723299, by rfl⟩ : syracuseStep 964399 = 1446599) B1446599
theorem B571475 : Blo 223812 571475 := bstep (se 1 (by rfl) ⟨428606, by rfl⟩ : syracuseStep 571475 = 857213) B857213
theorem B768095 : Blo 223812 768095 := bstep (se 1 (by rfl) ⟨576071, by rfl⟩ : syracuseStep 768095 = 1152143) B1152143
theorem B866447 : Blo 223812 866447 := bstep (se 1 (by rfl) ⟨649835, by rfl⟩ : syracuseStep 866447 = 1299671) B1299671
theorem B1915265 : Blo 223812 1915265 := bstep (se 2 (by rfl) ⟨718224, by rfl⟩ : syracuseStep 1915265 = 1436449) B1436449
theorem B571961 : Blo 223812 571961 := bstep (se 2 (by rfl) ⟨214485, by rfl⟩ : syracuseStep 571961 = 428971) B428971
theorem B1293023 : Blo 223812 1293023 := bstep (se 1 (by rfl) ⟨969767, by rfl⟩ : syracuseStep 1293023 = 1939535) B1939535
theorem B768851 : Blo 223812 768851 := bstep (se 1 (by rfl) ⟨576638, by rfl⟩ : syracuseStep 768851 = 1153277) B1153277
theorem B1227727 : Blo 223812 1227727 := bstep (se 1 (by rfl) ⟨920795, by rfl⟩ : syracuseStep 1227727 = 1841591) B1841591
theorem B605225 : Blo 223812 605225 := bstep (se 2 (by rfl) ⟨226959, by rfl⟩ : syracuseStep 605225 = 453919) B453919
theorem B506951 : Blo 223812 506951 := bstep (se 1 (by rfl) ⟨380213, by rfl⟩ : syracuseStep 506951 = 760427) B760427
theorem B638081 : Blo 223812 638081 := bstep (se 2 (by rfl) ⟨239280, by rfl⟩ : syracuseStep 638081 = 478561) B478561
theorem B507347 : Blo 223812 507347 := bstep (se 1 (by rfl) ⟨380510, by rfl⟩ : syracuseStep 507347 = 761021) B761021
theorem B572903 : Blo 223812 572903 := bstep (se 1 (by rfl) ⟨429677, by rfl⟩ : syracuseStep 572903 = 859355) B859355
theorem B507617 : Blo 223812 507617 := bstep (se 2 (by rfl) ⟨190356, by rfl⟩ : syracuseStep 507617 = 380713) B380713
theorem B3096787 : Blo 223812 3096787 := bstep (se 1 (by rfl) ⟨2322590, by rfl⟩ : syracuseStep 3096787 = 4645181) B4645181
theorem B1917863 : Blo 223812 1917863 := bstep (se 1 (by rfl) ⟨1438397, by rfl⟩ : syracuseStep 1917863 = 2876795) B2876795
theorem B377851 : Blo 223812 377851 := bstep (se 1 (by rfl) ⟨283388, by rfl⟩ : syracuseStep 377851 = 566777) B566777
theorem B2573369 : Blo 223812 2573369 := bstep (se 2 (by rfl) ⟨965013, by rfl⟩ : syracuseStep 2573369 = 1930027) B1930027
theorem B509291 : Blo 223812 509291 := bstep (se 1 (by rfl) ⟨381968, by rfl⟩ : syracuseStep 509291 = 763937) B763937
theorem B378283 : Blo 223812 378283 := bstep (se 1 (by rfl) ⟨283712, by rfl⟩ : syracuseStep 378283 = 567425) B567425
theorem B378479 : Blo 223812 378479 := bstep (se 1 (by rfl) ⟨283859, by rfl⟩ : syracuseStep 378479 = 567719) B567719
theorem B509561 : Blo 223812 509561 := bstep (se 2 (by rfl) ⟨191085, by rfl⟩ : syracuseStep 509561 = 382171) B382171
theorem B1230497 : Blo 223812 1230497 := bstep (se 2 (by rfl) ⟨461436, by rfl⟩ : syracuseStep 1230497 = 922873) B922873
theorem B378587 : Blo 223812 378587 := bstep (se 1 (by rfl) ⟨283940, by rfl⟩ : syracuseStep 378587 = 567881) B567881
theorem B1165117 : Blo 223812 1165117 := bstep (se 3 (by rfl) ⟨218459, by rfl⟩ : syracuseStep 1165117 = 436919) B436919
theorem B378823 : Blo 223812 378823 := bstep (se 1 (by rfl) ⟨284117, by rfl⟩ : syracuseStep 378823 = 568235) B568235
theorem B543071 : Blo 223812 543071 := bstep (se 1 (by rfl) ⟨407303, by rfl⟩ : syracuseStep 543071 = 814607) B814607
theorem B576031 : Blo 223812 576031 := bstep (se 1 (by rfl) ⟨432023, by rfl⟩ : syracuseStep 576031 = 864047) B864047
theorem B510569 : Blo 223812 510569 := bstep (se 2 (by rfl) ⟨191463, by rfl⟩ : syracuseStep 510569 = 382927) B382927
theorem B379579 : Blo 223812 379579 := bstep (se 1 (by rfl) ⟨284684, by rfl⟩ : syracuseStep 379579 = 569369) B569369
theorem B379883 : Blo 223812 379883 := bstep (se 1 (by rfl) ⟨284912, by rfl⟩ : syracuseStep 379883 = 569825) B569825
theorem B2870437 : Blo 223812 2870437 := bstep (se 4 (by rfl) ⟨269103, by rfl⟩ : syracuseStep 2870437 = 538207) B538207
theorem B511199 : Blo 223812 511199 := bstep (se 1 (by rfl) ⟨383399, by rfl⟩ : syracuseStep 511199 = 766799) B766799
theorem B478543 : Blo 223812 478543 := bstep (se 1 (by rfl) ⟨358907, by rfl⟩ : syracuseStep 478543 = 717815) B717815
theorem B511415 : Blo 223812 511415 := bstep (se 1 (by rfl) ⟨383561, by rfl⟩ : syracuseStep 511415 = 767123) B767123
theorem B5459471 : Blo 223812 5459471 := bstep (se 1 (by rfl) ⟨4094603, by rfl⟩ : syracuseStep 5459471 = 8189207) B8189207
theorem B511595 : Blo 223812 511595 := bstep (se 1 (by rfl) ⟨383696, by rfl⟩ : syracuseStep 511595 = 767393) B767393
theorem B1560323 : Blo 223812 1560323 := bstep (se 1 (by rfl) ⟨1170242, by rfl⟩ : syracuseStep 1560323 = 2340485) B2340485
theorem B511865 : Blo 223812 511865 := bstep (se 2 (by rfl) ⟨191949, by rfl⟩ : syracuseStep 511865 = 383899) B383899
theorem B2445203 : Blo 223812 2445203 := bstep (se 1 (by rfl) ⟨1833902, by rfl⟩ : syracuseStep 2445203 = 3667805) B3667805
theorem B3101287 : Blo 223812 3101287 := bstep (se 1 (by rfl) ⟨2325965, by rfl⟩ : syracuseStep 3101287 = 4651931) B4651931
theorem B1168195 : Blo 223812 1168195 := bstep (se 1 (by rfl) ⟨876146, by rfl⟩ : syracuseStep 1168195 = 1752293) B1752293
theorem B775241 : Blo 223812 775241 := bstep (se 2 (by rfl) ⟨290715, by rfl⟩ : syracuseStep 775241 = 581431) B581431
theorem B284411 : Blo 223812 284411 := bstep (se 1 (by rfl) ⟨213308, by rfl⟩ : syracuseStep 284411 = 426617) B426617
theorem B294508331 : Blo 223812 294508331 := bstep (se 1 (by rfl) ⟨220881248, by rfl⟩ : syracuseStep 294508331 = 441762497) B441762497
theorem B382799 : Blo 223812 382799 := bstep (se 1 (by rfl) ⟨287099, by rfl⟩ : syracuseStep 382799 = 574199) B574199
theorem B808841 : Blo 223812 808841 := bstep (se 2 (by rfl) ⟨303315, by rfl⟩ : syracuseStep 808841 = 606631) B606631
theorem B481243 : Blo 223812 481243 := bstep (se 1 (by rfl) ⟨360932, by rfl⟩ : syracuseStep 481243 = 721865) B721865
theorem B251887 : Blo 223812 251887 := bstep (se 1 (by rfl) ⟨188915, by rfl⟩ : syracuseStep 251887 = 377831) B377831
theorem B547195 : Blo 223812 547195 := bstep (se 1 (by rfl) ⟨410396, by rfl⟩ : syracuseStep 547195 = 820793) B820793
theorem B8739251 : Blo 223812 8739251 := bstep (se 1 (by rfl) ⟨6554438, by rfl⟩ : syracuseStep 8739251 = 13108877) B13108877
theorem B285211 : Blo 223812 285211 := bstep (se 1 (by rfl) ⟨213908, by rfl⟩ : syracuseStep 285211 = 427817) B427817
theorem B7002773 : Blo 223812 7002773 := bstep (se 6 (by rfl) ⟨164127, by rfl⟩ : syracuseStep 7002773 = 328255) B328255
theorem B1367009 : Blo 223812 1367009 := bstep (se 2 (by rfl) ⟨512628, by rfl⟩ : syracuseStep 1367009 = 1025257) B1025257
theorem B384041 : Blo 223812 384041 := bstep (se 2 (by rfl) ⟨144015, by rfl⟩ : syracuseStep 384041 = 288031) B288031
theorem B1662137 : Blo 223812 1662137 := bstep (se 2 (by rfl) ⟨623301, by rfl⟩ : syracuseStep 1662137 = 1246603) B1246603
theorem B384223 : Blo 223812 384223 := bstep (se 1 (by rfl) ⟨288167, by rfl⟩ : syracuseStep 384223 = 576335) B576335
theorem B286031 : Blo 223812 286031 := bstep (se 1 (by rfl) ⟨214523, by rfl⟩ : syracuseStep 286031 = 429047) B429047
theorem B3857867 : Blo 223812 3857867 := bstep (se 1 (by rfl) ⟨2893400, by rfl⟩ : syracuseStep 3857867 = 5786801) B5786801
theorem B286183 : Blo 223812 286183 := bstep (se 1 (by rfl) ⟨214637, by rfl⟩ : syracuseStep 286183 = 429275) B429275
theorem B1564645 : Blo 223812 1564645 := bstep (se 4 (by rfl) ⟨146685, by rfl⟩ : syracuseStep 1564645 = 293371) B293371
theorem B254335 : Blo 223812 254335 := bstep (se 1 (by rfl) ⟨190751, by rfl⟩ : syracuseStep 254335 = 381503) B381503
theorem B7332227 : Blo 223812 7332227 := bstep (se 1 (by rfl) ⟨5499170, by rfl⟩ : syracuseStep 7332227 = 10998341) B10998341
theorem B778825 : Blo 223812 778825 := bstep (se 2 (by rfl) ⟨292059, by rfl⟩ : syracuseStep 778825 = 584119) B584119
theorem B647945 : Blo 223812 647945 := bstep (se 2 (by rfl) ⟨242979, by rfl⟩ : syracuseStep 647945 = 485959) B485959
theorem B779017 : Blo 223812 779017 := bstep (se 2 (by rfl) ⟨292131, by rfl⟩ : syracuseStep 779017 = 584263) B584263
theorem B615325 : Blo 223812 615325 := bstep (se 3 (by rfl) ⟨115373, by rfl⟩ : syracuseStep 615325 = 230747) B230747
theorem B1631461 : Blo 223812 1631461 := bstep (se 4 (by rfl) ⟨152949, by rfl⟩ : syracuseStep 1631461 = 305899) B305899
theorem B1435117 : Blo 223812 1435117 := bstep (se 3 (by rfl) ⟨269084, by rfl⟩ : syracuseStep 1435117 = 538169) B538169
theorem B255739 : Blo 223812 255739 := bstep (se 1 (by rfl) ⟨191804, by rfl⟩ : syracuseStep 255739 = 383609) B383609
theorem B255775 : Blo 223812 255775 := bstep (se 1 (by rfl) ⟨191831, by rfl⟩ : syracuseStep 255775 = 383663) B383663
theorem B2550041 : Blo 223812 2550041 := bstep (se 2 (by rfl) ⟨956265, by rfl⟩ : syracuseStep 2550041 = 1912531) B1912531
theorem B485993 : Blo 223812 485993 := bstep (se 2 (by rfl) ⟨182247, by rfl⟩ : syracuseStep 485993 = 364495) B364495
theorem B1141451 : Blo 223812 1141451 := bstep (se 1 (by rfl) ⟨856088, by rfl⟩ : syracuseStep 1141451 = 1712177) B1712177
theorem B224091 : Blo 223812 224091 := bstep (se 1 (by rfl) ⟨168068, by rfl⟩ : syracuseStep 224091 = 336137) B336137
theorem B224159 : Blo 223812 224159 := bstep (se 1 (by rfl) ⟨168119, by rfl⟩ : syracuseStep 224159 = 336239) B336239
theorem B224303 : Blo 223812 224303 := bstep (se 1 (by rfl) ⟨168227, by rfl⟩ : syracuseStep 224303 = 336455) B336455
theorem B224327 : Blo 223812 224327 := bstep (se 1 (by rfl) ⟨168245, by rfl⟩ : syracuseStep 224327 = 336491) B336491
theorem B224479 : Blo 223812 224479 := bstep (se 1 (by rfl) ⟨168359, by rfl⟩ : syracuseStep 224479 = 336719) B336719
theorem B224743 : Blo 223812 224743 := bstep (se 1 (by rfl) ⟨168557, by rfl⟩ : syracuseStep 224743 = 337115) B337115
theorem B224859 : Blo 223812 224859 := bstep (se 1 (by rfl) ⟨168644, by rfl⟩ : syracuseStep 224859 = 337289) B337289
theorem B3632849 : Blo 223812 3632849 := bstep (se 2 (by rfl) ⟨1362318, by rfl⟩ : syracuseStep 3632849 = 2724637) B2724637
theorem B225095 : Blo 223812 225095 := bstep (se 1 (by rfl) ⟨168821, by rfl⟩ : syracuseStep 225095 = 337643) B337643
theorem B225247 : Blo 223812 225247 := bstep (se 1 (by rfl) ⟨168935, by rfl⟩ : syracuseStep 225247 = 337871) B337871
theorem B323551 : Blo 223812 323551 := bstep (se 1 (by rfl) ⟨242663, by rfl⟩ : syracuseStep 323551 = 485327) B485327
theorem B913531 : Blo 223812 913531 := bstep (se 1 (by rfl) ⟨685148, by rfl⟩ : syracuseStep 913531 = 1370297) B1370297
theorem B454843 : Blo 223812 454843 := bstep (se 1 (by rfl) ⟨341132, by rfl⟩ : syracuseStep 454843 = 682265) B682265
theorem B225511 : Blo 223812 225511 := bstep (se 1 (by rfl) ⟨169133, by rfl⟩ : syracuseStep 225511 = 338267) B338267
theorem B225663 : Blo 223812 225663 := bstep (se 1 (by rfl) ⟨169247, by rfl⟩ : syracuseStep 225663 = 338495) B338495
theorem B2748809 : Blo 223812 2748809 := bstep (se 2 (by rfl) ⟨1030803, by rfl⟩ : syracuseStep 2748809 = 2061607) B2061607
theorem B225743 : Blo 223812 225743 := bstep (se 1 (by rfl) ⟨169307, by rfl⟩ : syracuseStep 225743 = 338615) B338615
theorem B225895 : Blo 223812 225895 := bstep (se 1 (by rfl) ⟨169421, by rfl⟩ : syracuseStep 225895 = 338843) B338843
theorem B226159 : Blo 223812 226159 := bstep (se 1 (by rfl) ⟨169619, by rfl⟩ : syracuseStep 226159 = 339239) B339239
theorem B226215 : Blo 223812 226215 := bstep (se 1 (by rfl) ⟨169661, by rfl⟩ : syracuseStep 226215 = 339323) B339323
theorem B4649957 : Blo 223812 4649957 := bstep (se 4 (by rfl) ⟨435933, by rfl⟩ : syracuseStep 4649957 = 871867) B871867
theorem B226299 : Blo 223812 226299 := bstep (se 1 (by rfl) ⟨169724, by rfl⟩ : syracuseStep 226299 = 339449) B339449
theorem B226367 : Blo 223812 226367 := bstep (se 1 (by rfl) ⟨169775, by rfl⟩ : syracuseStep 226367 = 339551) B339551
theorem B1143881 : Blo 223812 1143881 := bstep (se 2 (by rfl) ⟨428955, by rfl⟩ : syracuseStep 1143881 = 857911) B857911
theorem B226511 : Blo 223812 226511 := bstep (se 1 (by rfl) ⟨169883, by rfl⟩ : syracuseStep 226511 = 339767) B339767
theorem B685403 : Blo 223812 685403 := bstep (se 1 (by rfl) ⟨514052, by rfl⟩ : syracuseStep 685403 = 1028105) B1028105
theorem B3077519 : Blo 223812 3077519 := bstep (se 1 (by rfl) ⟨2308139, by rfl⟩ : syracuseStep 3077519 = 4616279) B4616279
theorem B226715 : Blo 223812 226715 := bstep (se 1 (by rfl) ⟨170036, by rfl⟩ : syracuseStep 226715 = 340073) B340073
theorem B226927 : Blo 223812 226927 := bstep (se 1 (by rfl) ⟨170195, by rfl⟩ : syracuseStep 226927 = 340391) B340391
theorem B226983 : Blo 223812 226983 := bstep (se 1 (by rfl) ⟨170237, by rfl⟩ : syracuseStep 226983 = 340475) B340475
theorem B1144529 : Blo 223812 1144529 := bstep (se 2 (by rfl) ⟨429198, by rfl⟩ : syracuseStep 1144529 = 858397) B858397
theorem B227067 : Blo 223812 227067 := bstep (se 1 (by rfl) ⟨170300, by rfl⟩ : syracuseStep 227067 = 340601) B340601
theorem B227103 : Blo 223812 227103 := bstep (se 1 (by rfl) ⟨170327, by rfl⟩ : syracuseStep 227103 = 340655) B340655
theorem B2586401 : Blo 223812 2586401 := bstep (se 2 (by rfl) ⟨969900, by rfl⟩ : syracuseStep 2586401 = 1939801) B1939801
theorem B227135 : Blo 223812 227135 := bstep (se 1 (by rfl) ⟨170351, by rfl⟩ : syracuseStep 227135 = 340703) B340703
theorem B227311 : Blo 223812 227311 := bstep (se 1 (by rfl) ⟨170483, by rfl⟩ : syracuseStep 227311 = 340967) B340967
theorem B1701971 : Blo 223812 1701971 := bstep (se 1 (by rfl) ⟨1276478, by rfl⟩ : syracuseStep 1701971 = 2552957) B2552957
theorem B718931 : Blo 223812 718931 := bstep (se 1 (by rfl) ⟨539198, by rfl⟩ : syracuseStep 718931 = 1078397) B1078397
theorem B358543 : Blo 223812 358543 := bstep (se 1 (by rfl) ⟨268907, by rfl⟩ : syracuseStep 358543 = 537815) B537815
theorem B227483 : Blo 223812 227483 := bstep (se 1 (by rfl) ⟨170612, by rfl⟩ : syracuseStep 227483 = 341225) B341225
theorem B227519 : Blo 223812 227519 := bstep (se 1 (by rfl) ⟨170639, by rfl⟩ : syracuseStep 227519 = 341279) B341279
theorem B227631 : Blo 223812 227631 := bstep (se 1 (by rfl) ⟨170723, by rfl⟩ : syracuseStep 227631 = 341447) B341447
theorem B850895 : Blo 223812 850895 := bstep (se 1 (by rfl) ⟨638171, by rfl⟩ : syracuseStep 850895 = 1276343) B1276343
theorem B687095 : Blo 223812 687095 := bstep (se 1 (by rfl) ⟨515321, by rfl⟩ : syracuseStep 687095 = 1030643) B1030643
theorem B720019 : Blo 223812 720019 := bstep (se 1 (by rfl) ⟨540014, by rfl⟩ : syracuseStep 720019 = 1080029) B1080029
theorem B181140941 : Blo 223812 181140941 := bstep (se 3 (by rfl) ⟨33963926, by rfl⟩ : syracuseStep 181140941 = 67927853) B67927853
theorem B851411 : Blo 223812 851411 := bstep (se 1 (by rfl) ⟨638558, by rfl⟩ : syracuseStep 851411 = 1277117) B1277117
theorem B7274099 : Blo 223812 7274099 := bstep (se 1 (by rfl) ⟨5455574, by rfl⟩ : syracuseStep 7274099 = 10911149) B10911149
theorem B720571 : Blo 223812 720571 := bstep (se 1 (by rfl) ⟨540428, by rfl⟩ : syracuseStep 720571 = 1080857) B1080857
theorem B1081259 : Blo 223812 1081259 := bstep (se 1 (by rfl) ⟨810944, by rfl⟩ : syracuseStep 1081259 = 1621889) B1621889
theorem B4129049 : Blo 223812 4129049 := bstep (se 2 (by rfl) ⟨1548393, by rfl⟩ : syracuseStep 4129049 = 3096787) B3096787
theorem B1278575 : Blo 223812 1278575 := bstep (se 1 (by rfl) ⟨958931, by rfl⟩ : syracuseStep 1278575 = 1917863) B1917863
theorem B820331 : Blo 223812 820331 := bstep (se 1 (by rfl) ⟨615248, by rfl⟩ : syracuseStep 820331 = 1230497) B1230497
theorem B820433 : Blo 223812 820433 := bstep (se 2 (by rfl) ⟨307662, by rfl⟩ : syracuseStep 820433 = 615325) B615325
theorem B3278555 : Blo 223812 3278555 := bstep (se 1 (by rfl) ⟨2458916, by rfl⟩ : syracuseStep 3278555 = 4917833) B4917833
theorem B755513 : Blo 223812 755513 := bstep (se 2 (by rfl) ⟨283317, by rfl⟩ : syracuseStep 755513 = 566635) B566635
theorem B1411181 : Blo 223812 1411181 := bstep (se 3 (by rfl) ⟨264596, by rfl⟩ : syracuseStep 1411181 = 529193) B529193
theorem B919775 : Blo 223812 919775 := bstep (se 1 (by rfl) ⟨689831, by rfl⟩ : syracuseStep 919775 = 1379663) B1379663
theorem B3639647 : Blo 223812 3639647 := bstep (se 1 (by rfl) ⟨2729735, by rfl⟩ : syracuseStep 3639647 = 5459471) B5459471
theorem B856439 : Blo 223812 856439 := bstep (se 1 (by rfl) ⟨642329, by rfl⟩ : syracuseStep 856439 = 1284659) B1284659
theorem B758429 : Blo 223812 758429 := bstep (se 3 (by rfl) ⟨142205, by rfl⟩ : syracuseStep 758429 = 284411) B284411
theorem B2167559 : Blo 223812 2167559 := bstep (se 1 (by rfl) ⟨1625669, by rfl⟩ : syracuseStep 2167559 = 3251339) B3251339
theorem B758969 : Blo 223812 758969 := bstep (se 2 (by rfl) ⟨284613, by rfl⟩ : syracuseStep 758969 = 569227) B569227
theorem B431401 : Blo 223812 431401 := bstep (se 2 (by rfl) ⟨161775, by rfl⟩ : syracuseStep 431401 = 323551) B323551
theorem B857411 : Blo 223812 857411 := bstep (se 1 (by rfl) ⟨643058, by rfl⟩ : syracuseStep 857411 = 1286117) B1286117
theorem B1971611 : Blo 223812 1971611 := bstep (se 1 (by rfl) ⟨1478708, by rfl⟩ : syracuseStep 1971611 = 2957417) B2957417
theorem B1218041 : Blo 223812 1218041 := bstep (se 2 (by rfl) ⟨456765, by rfl⟩ : syracuseStep 1218041 = 913531) B913531
theorem B4888151 : Blo 223812 4888151 := bstep (se 1 (by rfl) ⟨3666113, by rfl⟩ : syracuseStep 4888151 = 7332227) B7332227
theorem B431963 : Blo 223812 431963 := bstep (se 1 (by rfl) ⟨323972, by rfl⟩ : syracuseStep 431963 = 647945) B647945
theorem B4135049 : Blo 223812 4135049 := bstep (se 2 (by rfl) ⟨1550643, by rfl⟩ : syracuseStep 4135049 = 3101287) B3101287
theorem B1710233 : Blo 223812 1710233 := bstep (se 2 (by rfl) ⟨641337, by rfl⟩ : syracuseStep 1710233 = 1282675) B1282675
theorem B1448189 : Blo 223812 1448189 := bstep (se 3 (by rfl) ⟨271535, by rfl⟩ : syracuseStep 1448189 = 543071) B543071
theorem B760967 : Blo 223812 760967 := bstep (se 1 (by rfl) ⟨570725, by rfl⟩ : syracuseStep 760967 = 1141451) B1141451
theorem B6627035 : Blo 223812 6627035 := bstep (se 1 (by rfl) ⟨4970276, by rfl⟩ : syracuseStep 6627035 = 9940553) B9940553
theorem B1285865 : Blo 223812 1285865 := bstep (se 2 (by rfl) ⟨482199, by rfl⟩ : syracuseStep 1285865 = 964399) B964399
theorem B335849 : Blo 223812 335849 := bstep (se 2 (by rfl) ⟨125943, by rfl⟩ : syracuseStep 335849 = 251887) B251887
theorem B5906519 : Blo 223812 5906519 := bstep (se 1 (by rfl) ⟨4429889, by rfl⟩ : syracuseStep 5906519 = 8859779) B8859779
theorem B2760875 : Blo 223812 2760875 := bstep (se 1 (by rfl) ⟨2070656, by rfl⟩ : syracuseStep 2760875 = 4141313) B4141313
theorem B860615 : Blo 223812 860615 := bstep (se 1 (by rfl) ⟨645461, by rfl⟩ : syracuseStep 860615 = 1290923) B1290923
theorem B729593 : Blo 223812 729593 := bstep (se 2 (by rfl) ⟨273597, by rfl⟩ : syracuseStep 729593 = 547195) B547195
theorem B336551 : Blo 223812 336551 := bstep (se 1 (by rfl) ⟨252413, by rfl⟩ : syracuseStep 336551 = 504827) B504827
theorem B762587 : Blo 223812 762587 := bstep (se 1 (by rfl) ⟨571940, by rfl⟩ : syracuseStep 762587 = 1143881) B1143881
theorem B336671 : Blo 223812 336671 := bstep (se 1 (by rfl) ⟨252503, by rfl⟩ : syracuseStep 336671 = 505007) B505007
theorem B336695 : Blo 223812 336695 := bstep (se 1 (by rfl) ⟨252521, by rfl⟩ : syracuseStep 336695 = 505043) B505043
theorem B762749 : Blo 223812 762749 := bstep (se 3 (by rfl) ⟨143015, by rfl⟩ : syracuseStep 762749 = 286031) B286031
theorem B336875 : Blo 223812 336875 := bstep (se 1 (by rfl) ⟨252656, by rfl⟩ : syracuseStep 336875 = 505313) B505313
theorem B763019 : Blo 223812 763019 := bstep (se 1 (by rfl) ⟨572264, by rfl⟩ : syracuseStep 763019 = 1144529) B1144529
theorem B960025 : Blo 223812 960025 := bstep (se 2 (by rfl) ⟨360009, by rfl⟩ : syracuseStep 960025 = 720019) B720019
theorem B862015 : Blo 223812 862015 := bstep (se 1 (by rfl) ⟨646511, by rfl⟩ : syracuseStep 862015 = 1293023) B1293023
theorem B567263 : Blo 223812 567263 := bstep (se 1 (by rfl) ⟨425447, by rfl⟩ : syracuseStep 567263 = 850895) B850895
theorem B403483 : Blo 223812 403483 := bstep (se 1 (by rfl) ⟨302612, by rfl⟩ : syracuseStep 403483 = 605225) B605225
theorem B337967 : Blo 223812 337967 := bstep (se 1 (by rfl) ⟨253475, by rfl⟩ : syracuseStep 337967 = 506951) B506951
theorem B960761 : Blo 223812 960761 := bstep (se 2 (by rfl) ⟨360285, by rfl⟩ : syracuseStep 960761 = 720571) B720571
theorem B120760627 : Blo 223812 120760627 := bstep (se 1 (by rfl) ⟨90570470, by rfl⟩ : syracuseStep 120760627 = 181140941) B181140941
theorem B567607 : Blo 223812 567607 := bstep (se 1 (by rfl) ⟨425705, by rfl⟩ : syracuseStep 567607 = 851411) B851411
theorem B338231 : Blo 223812 338231 := bstep (se 1 (by rfl) ⟨253673, by rfl⟩ : syracuseStep 338231 = 507347) B507347
theorem B338411 : Blo 223812 338411 := bstep (se 1 (by rfl) ⟨253808, by rfl⟩ : syracuseStep 338411 = 507617) B507617
theorem B764639 : Blo 223812 764639 := bstep (se 1 (by rfl) ⟨573479, by rfl⟩ : syracuseStep 764639 = 1146959) B1146959
theorem B339113 : Blo 223812 339113 := bstep (se 2 (by rfl) ⟨127167, by rfl⟩ : syracuseStep 339113 = 254335) B254335
theorem B1223923 : Blo 223812 1223923 := bstep (se 1 (by rfl) ⟨917942, by rfl⟩ : syracuseStep 1223923 = 1835885) B1835885
theorem B1715579 : Blo 223812 1715579 := bstep (se 1 (by rfl) ⟨1286684, by rfl⟩ : syracuseStep 1715579 = 2573369) B2573369
theorem B1027591 : Blo 223812 1027591 := bstep (se 1 (by rfl) ⟨770693, by rfl⟩ : syracuseStep 1027591 = 1541387) B1541387
theorem B339527 : Blo 223812 339527 := bstep (se 1 (by rfl) ⟨254645, by rfl⟩ : syracuseStep 339527 = 509291) B509291
theorem B569015 : Blo 223812 569015 := bstep (se 1 (by rfl) ⟨426761, by rfl⟩ : syracuseStep 569015 = 853523) B853523
theorem B569065 : Blo 223812 569065 := bstep (se 2 (by rfl) ⟨213399, by rfl⟩ : syracuseStep 569065 = 426799) B426799
theorem B339707 : Blo 223812 339707 := bstep (se 1 (by rfl) ⟨254780, by rfl⟩ : syracuseStep 339707 = 509561) B509561
theorem B503801 : Blo 223812 503801 := bstep (se 2 (by rfl) ⟨188925, by rfl⟩ : syracuseStep 503801 = 377851) B377851
theorem B1159247 : Blo 223812 1159247 := bstep (se 1 (by rfl) ⟨869435, by rfl⟩ : syracuseStep 1159247 = 1738871) B1738871
theorem B503891 : Blo 223812 503891 := bstep (se 1 (by rfl) ⟨377918, by rfl⟩ : syracuseStep 503891 = 755837) B755837
theorem B307327 : Blo 223812 307327 := bstep (se 1 (by rfl) ⟨230495, by rfl⟩ : syracuseStep 307327 = 460991) B460991
theorem B504071 : Blo 223812 504071 := bstep (se 1 (by rfl) ⟨378053, by rfl⟩ : syracuseStep 504071 = 756107) B756107
theorem B2175281 : Blo 223812 2175281 := bstep (se 2 (by rfl) ⟨815730, by rfl⟩ : syracuseStep 2175281 = 1631461) B1631461
theorem B340379 : Blo 223812 340379 := bstep (se 1 (by rfl) ⟨255284, by rfl⟩ : syracuseStep 340379 = 510569) B510569
theorem B962999 : Blo 223812 962999 := bstep (se 1 (by rfl) ⟨722249, by rfl⟩ : syracuseStep 962999 = 1444499) B1444499
theorem B504377 : Blo 223812 504377 := bstep (se 2 (by rfl) ⟨189141, by rfl⟩ : syracuseStep 504377 = 378283) B378283
theorem B1913489 : Blo 223812 1913489 := bstep (se 2 (by rfl) ⟨717558, by rfl⟩ : syracuseStep 1913489 = 1435117) B1435117
theorem B1553215 : Blo 223812 1553215 := bstep (se 1 (by rfl) ⟨1164911, by rfl⟩ : syracuseStep 1553215 = 2329823) B2329823
theorem B340799 : Blo 223812 340799 := bstep (se 1 (by rfl) ⟨255599, by rfl⟩ : syracuseStep 340799 = 511199) B511199
theorem B340943 : Blo 223812 340943 := bstep (se 1 (by rfl) ⟨255707, by rfl⟩ : syracuseStep 340943 = 511415) B511415
theorem B340985 : Blo 223812 340985 := bstep (se 2 (by rfl) ⟨127869, by rfl⟩ : syracuseStep 340985 = 255739) B255739
theorem B341033 : Blo 223812 341033 := bstep (se 2 (by rfl) ⟨127887, by rfl⟩ : syracuseStep 341033 = 255775) B255775
theorem B341063 : Blo 223812 341063 := bstep (se 1 (by rfl) ⟨255797, by rfl⟩ : syracuseStep 341063 = 511595) B511595
theorem B1553489 : Blo 223812 1553489 := bstep (se 2 (by rfl) ⟨582558, by rfl⟩ : syracuseStep 1553489 = 1165117) B1165117
theorem B570473 : Blo 223812 570473 := bstep (se 2 (by rfl) ⟨213927, by rfl⟩ : syracuseStep 570473 = 427855) B427855
theorem B341243 : Blo 223812 341243 := bstep (se 1 (by rfl) ⟨255932, by rfl⟩ : syracuseStep 341243 = 511865) B511865
theorem B505097 : Blo 223812 505097 := bstep (se 2 (by rfl) ⟨189411, by rfl⟩ : syracuseStep 505097 = 378823) B378823
theorem B505151 : Blo 223812 505151 := bstep (se 1 (by rfl) ⟨378863, by rfl⟩ : syracuseStep 505151 = 757727) B757727
theorem B505259 : Blo 223812 505259 := bstep (se 1 (by rfl) ⟨378944, by rfl⟩ : syracuseStep 505259 = 757889) B757889
theorem B505583 : Blo 223812 505583 := bstep (se 1 (by rfl) ⟨379187, by rfl⟩ : syracuseStep 505583 = 758375) B758375
theorem B505799 : Blo 223812 505799 := bstep (se 1 (by rfl) ⟨379349, by rfl⟩ : syracuseStep 505799 = 758699) B758699
theorem B768041 : Blo 223812 768041 := bstep (se 2 (by rfl) ⟨288015, by rfl⟩ : syracuseStep 768041 = 576031) B576031
theorem B506087 : Blo 223812 506087 := bstep (se 1 (by rfl) ⟨379565, by rfl⟩ : syracuseStep 506087 = 759131) B759131
theorem B506105 : Blo 223812 506105 := bstep (se 2 (by rfl) ⟨189789, by rfl⟩ : syracuseStep 506105 = 379579) B379579
theorem B506159 : Blo 223812 506159 := bstep (se 1 (by rfl) ⟨379619, by rfl⟩ : syracuseStep 506159 = 759239) B759239
theorem B506375 : Blo 223812 506375 := bstep (se 1 (by rfl) ⟨379781, by rfl⟩ : syracuseStep 506375 = 759563) B759563
theorem B539227 : Blo 223812 539227 := bstep (se 1 (by rfl) ⟨404420, by rfl⟩ : syracuseStep 539227 = 808841) B808841
theorem B506555 : Blo 223812 506555 := bstep (se 1 (by rfl) ⟨379916, by rfl⟩ : syracuseStep 506555 = 759833) B759833
theorem B4668515 : Blo 223812 4668515 := bstep (se 1 (by rfl) ⟨3501386, by rfl⟩ : syracuseStep 4668515 = 7002773) B7002773
theorem B638057 : Blo 223812 638057 := bstep (se 2 (by rfl) ⟨239271, by rfl⟩ : syracuseStep 638057 = 478543) B478543
theorem B7388279 : Blo 223812 7388279 := bstep (se 1 (by rfl) ⟨5541209, by rfl⟩ : syracuseStep 7388279 = 11082419) B11082419
theorem B1457297 : Blo 223812 1457297 := bstep (se 2 (by rfl) ⟨546486, by rfl⟩ : syracuseStep 1457297 = 1092973) B1092973
theorem B4308299 : Blo 223812 4308299 := bstep (se 1 (by rfl) ⟨3231224, by rfl⟩ : syracuseStep 4308299 = 6462449) B6462449
theorem B507455 : Blo 223812 507455 := bstep (se 1 (by rfl) ⟨380591, by rfl⟩ : syracuseStep 507455 = 761183) B761183
theorem B2571911 : Blo 223812 2571911 := bstep (se 1 (by rfl) ⟨1928933, by rfl⟩ : syracuseStep 2571911 = 3857867) B3857867
theorem B1556279 : Blo 223812 1556279 := bstep (se 1 (by rfl) ⟨1167209, by rfl⟩ : syracuseStep 1556279 = 2334419) B2334419
theorem B507815 : Blo 223812 507815 := bstep (se 1 (by rfl) ⟨380861, by rfl⟩ : syracuseStep 507815 = 761723) B761723
theorem B1622207 : Blo 223812 1622207 := bstep (se 1 (by rfl) ⟨1216655, by rfl⟩ : syracuseStep 1622207 = 2433311) B2433311
theorem B508139 : Blo 223812 508139 := bstep (se 1 (by rfl) ⟨381104, by rfl⟩ : syracuseStep 508139 = 762209) B762209
theorem B606457 : Blo 223812 606457 := bstep (se 2 (by rfl) ⟨227421, by rfl⟩ : syracuseStep 606457 = 454843) B454843
theorem B967099 : Blo 223812 967099 := bstep (se 1 (by rfl) ⟨725324, by rfl⟩ : syracuseStep 967099 = 1450649) B1450649
theorem B574249 : Blo 223812 574249 := bstep (se 2 (by rfl) ⟨215343, by rfl⟩ : syracuseStep 574249 = 430687) B430687
theorem B1557593 : Blo 223812 1557593 := bstep (se 2 (by rfl) ⟨584097, by rfl⟩ : syracuseStep 1557593 = 1168195) B1168195
theorem B509039 : Blo 223812 509039 := bstep (se 1 (by rfl) ⟨381779, by rfl⟩ : syracuseStep 509039 = 763559) B763559
theorem B378047 : Blo 223812 378047 := bstep (se 1 (by rfl) ⟨283535, by rfl⟩ : syracuseStep 378047 = 567071) B567071
theorem B509435 : Blo 223812 509435 := bstep (se 1 (by rfl) ⟨382076, by rfl⟩ : syracuseStep 509435 = 764153) B764153
theorem B509471 : Blo 223812 509471 := bstep (se 1 (by rfl) ⟨382103, by rfl⟩ : syracuseStep 509471 = 764207) B764207
theorem B575039 : Blo 223812 575039 := bstep (se 1 (by rfl) ⟨431279, by rfl⟩ : syracuseStep 575039 = 862559) B862559
theorem B509615 : Blo 223812 509615 := bstep (se 1 (by rfl) ⟨382211, by rfl⟩ : syracuseStep 509615 = 764423) B764423
theorem B968705 : Blo 223812 968705 := bstep (se 2 (by rfl) ⟨363264, by rfl⟩ : syracuseStep 968705 = 726529) B726529
theorem B378911 : Blo 223812 378911 := bstep (se 1 (by rfl) ⟨284183, by rfl⟩ : syracuseStep 378911 = 568367) B568367
theorem B510047 : Blo 223812 510047 := bstep (se 1 (by rfl) ⟨382535, by rfl⟩ : syracuseStep 510047 = 765071) B765071
theorem B575687 : Blo 223812 575687 := bstep (se 1 (by rfl) ⟨431765, by rfl⟩ : syracuseStep 575687 = 863531) B863531
theorem B510335 : Blo 223812 510335 := bstep (se 1 (by rfl) ⟨382751, by rfl⟩ : syracuseStep 510335 = 765503) B765503
theorem B641657 : Blo 223812 641657 := bstep (se 2 (by rfl) ⟨240621, by rfl⟩ : syracuseStep 641657 = 481243) B481243
theorem B11717399 : Blo 223812 11717399 := bstep (se 1 (by rfl) ⟨8788049, by rfl⟩ : syracuseStep 11717399 = 17576099) B17576099
theorem B379687 : Blo 223812 379687 := bstep (se 1 (by rfl) ⟨284765, by rfl⟩ : syracuseStep 379687 = 569531) B569531
theorem B510803 : Blo 223812 510803 := bstep (se 1 (by rfl) ⟨383102, by rfl⟩ : syracuseStep 510803 = 766205) B766205
theorem B478057 : Blo 223812 478057 := bstep (se 2 (by rfl) ⟨179271, by rfl⟩ : syracuseStep 478057 = 358543) B358543
theorem B380011 : Blo 223812 380011 := bstep (se 1 (by rfl) ⟨285008, by rfl⟩ : syracuseStep 380011 = 570017) B570017
theorem B773267 : Blo 223812 773267 := bstep (se 1 (by rfl) ⟨579950, by rfl⟩ : syracuseStep 773267 = 1159901) B1159901
theorem B511163 : Blo 223812 511163 := bstep (se 1 (by rfl) ⟨383372, by rfl⟩ : syracuseStep 511163 = 766745) B766745
theorem B3099971 : Blo 223812 3099971 := bstep (se 1 (by rfl) ⟨2324978, by rfl⟩ : syracuseStep 3099971 = 4649957) B4649957
theorem B511343 : Blo 223812 511343 := bstep (se 1 (by rfl) ⟨383507, by rfl⟩ : syracuseStep 511343 = 767015) B767015
theorem B380281 : Blo 223812 380281 := bstep (se 2 (by rfl) ⟨142605, by rfl⟩ : syracuseStep 380281 = 285211) B285211
theorem B4115933 : Blo 223812 4115933 := bstep (se 3 (by rfl) ⟨771737, by rfl⟩ : syracuseStep 4115933 = 1543475) B1543475
theorem B642887 : Blo 223812 642887 := bstep (se 1 (by rfl) ⟨482165, by rfl⟩ : syracuseStep 642887 = 964331) B964331
theorem B1724267 : Blo 223812 1724267 := bstep (se 1 (by rfl) ⟨1293200, by rfl⟩ : syracuseStep 1724267 = 2586401) B2586401
theorem B1134647 : Blo 223812 1134647 := bstep (se 1 (by rfl) ⟨850985, by rfl⟩ : syracuseStep 1134647 = 1701971) B1701971
theorem B479287 : Blo 223812 479287 := bstep (se 1 (by rfl) ⟨359465, by rfl⟩ : syracuseStep 479287 = 718931) B718931
theorem B380983 : Blo 223812 380983 := bstep (se 1 (by rfl) ⟨285737, by rfl⟩ : syracuseStep 380983 = 571475) B571475
theorem B512063 : Blo 223812 512063 := bstep (se 1 (by rfl) ⟨384047, by rfl⟩ : syracuseStep 512063 = 768095) B768095
theorem B577631 : Blo 223812 577631 := bstep (se 1 (by rfl) ⟨433223, by rfl⟩ : syracuseStep 577631 = 866447) B866447
theorem B512297 : Blo 223812 512297 := bstep (se 2 (by rfl) ⟨192111, by rfl⟩ : syracuseStep 512297 = 384223) B384223
theorem B381307 : Blo 223812 381307 := bstep (se 1 (by rfl) ⟨285980, by rfl⟩ : syracuseStep 381307 = 571961) B571961
theorem B512567 : Blo 223812 512567 := bstep (se 1 (by rfl) ⟨384425, by rfl⟩ : syracuseStep 512567 = 768851) B768851
theorem B381577 : Blo 223812 381577 := bstep (se 2 (by rfl) ⟨143091, by rfl⟩ : syracuseStep 381577 = 286183) B286183
theorem B381935 : Blo 223812 381935 := bstep (se 1 (by rfl) ⟨286451, by rfl⟩ : syracuseStep 381935 = 572903) B572903
theorem B2086193 : Blo 223812 2086193 := bstep (se 2 (by rfl) ⟨782322, by rfl⟩ : syracuseStep 2086193 = 1564645) B1564645
theorem B284143 : Blo 223812 284143 := bstep (se 1 (by rfl) ⟨213107, by rfl⟩ : syracuseStep 284143 = 426215) B426215
theorem B480935 : Blo 223812 480935 := bstep (se 1 (by rfl) ⟨360701, by rfl⟩ : syracuseStep 480935 = 721403) B721403
theorem B1464155 : Blo 223812 1464155 := bstep (se 1 (by rfl) ⟨1098116, by rfl⟩ : syracuseStep 1464155 = 2196233) B2196233
theorem B1038433 : Blo 223812 1038433 := bstep (se 2 (by rfl) ⟨389412, by rfl⟩ : syracuseStep 1038433 = 778825) B778825
theorem B481619 : Blo 223812 481619 := bstep (se 1 (by rfl) ⟨361214, by rfl⟩ : syracuseStep 481619 = 722429) B722429
theorem B1038689 : Blo 223812 1038689 := bstep (se 2 (by rfl) ⟨389508, by rfl⟩ : syracuseStep 1038689 = 779017) B779017
theorem B252319 : Blo 223812 252319 := bstep (se 1 (by rfl) ⟨189239, by rfl⟩ : syracuseStep 252319 = 378479) B378479
theorem B252391 : Blo 223812 252391 := bstep (se 1 (by rfl) ⟨189293, by rfl⟩ : syracuseStep 252391 = 378587) B378587
theorem B4413971 : Blo 223812 4413971 := bstep (se 1 (by rfl) ⟨3310478, by rfl⟩ : syracuseStep 4413971 = 6620957) B6620957
theorem B1137401 : Blo 223812 1137401 := bstep (se 2 (by rfl) ⟨426525, by rfl⟩ : syracuseStep 1137401 = 853051) B853051
theorem B253255 : Blo 223812 253255 := bstep (se 1 (by rfl) ⟨189941, by rfl⟩ : syracuseStep 253255 = 379883) B379883
theorem B319097 : Blo 223812 319097 := bstep (se 2 (by rfl) ⟨119661, by rfl⟩ : syracuseStep 319097 = 239323) B239323
theorem B4218493 : Blo 223812 4218493 := bstep (se 3 (by rfl) ⟨790967, by rfl⟩ : syracuseStep 4218493 = 1581935) B1581935
theorem B1040215 : Blo 223812 1040215 := bstep (se 1 (by rfl) ⟨780161, by rfl⟩ : syracuseStep 1040215 = 1560323) B1560323
theorem B1630135 : Blo 223812 1630135 := bstep (se 1 (by rfl) ⟨1222601, by rfl⟩ : syracuseStep 1630135 = 2445203) B2445203
theorem B1106065 : Blo 223812 1106065 := bstep (se 2 (by rfl) ⟨414774, by rfl⟩ : syracuseStep 1106065 = 829549) B829549
theorem B516827 : Blo 223812 516827 := bstep (se 1 (by rfl) ⟨387620, by rfl⟩ : syracuseStep 516827 = 775241) B775241
theorem B4121401 : Blo 223812 4121401 := bstep (se 2 (by rfl) ⟨1545525, by rfl⟩ : syracuseStep 4121401 = 3091051) B3091051
theorem B196338887 : Blo 223812 196338887 := bstep (se 1 (by rfl) ⟨147254165, by rfl⟩ : syracuseStep 196338887 = 294508331) B294508331
theorem B255199 : Blo 223812 255199 := bstep (se 1 (by rfl) ⟨191399, by rfl⟩ : syracuseStep 255199 = 382799) B382799
theorem B32826869 : Blo 223812 32826869 := bstep (se 5 (by rfl) ⟨1538759, by rfl⟩ : syracuseStep 32826869 = 3077519) B3077519
theorem B3827249 : Blo 223812 3827249 := bstep (se 2 (by rfl) ⟨1435218, by rfl⟩ : syracuseStep 3827249 = 2870437) B2870437
theorem B5826167 : Blo 223812 5826167 := bstep (se 1 (by rfl) ⟨4369625, by rfl⟩ : syracuseStep 5826167 = 8739251) B8739251
theorem B911339 : Blo 223812 911339 := bstep (se 1 (by rfl) ⟨683504, by rfl⟩ : syracuseStep 911339 = 1367009) B1367009
theorem B256027 : Blo 223812 256027 := bstep (se 1 (by rfl) ⟨192020, by rfl⟩ : syracuseStep 256027 = 384041) B384041
theorem B1108091 : Blo 223812 1108091 := bstep (se 1 (by rfl) ⟨831068, by rfl⟩ : syracuseStep 1108091 = 1662137) B1662137
theorem B6547877 : Blo 223812 6547877 := bstep (se 4 (by rfl) ⟨613863, by rfl⟩ : syracuseStep 6547877 = 1227727) B1227727
theorem B223847 : Blo 223812 223847 := bstep (se 1 (by rfl) ⟨167885, by rfl⟩ : syracuseStep 223847 = 335771) B335771
theorem B1076107 : Blo 223812 1076107 := bstep (se 1 (by rfl) ⟨807080, by rfl⟩ : syracuseStep 1076107 = 1614161) B1614161
theorem B224223 : Blo 223812 224223 := bstep (se 1 (by rfl) ⟨168167, by rfl⟩ : syracuseStep 224223 = 336335) B336335
theorem B224251 : Blo 223812 224251 := bstep (se 1 (by rfl) ⟨168188, by rfl⟩ : syracuseStep 224251 = 336377) B336377
theorem B224319 : Blo 223812 224319 := bstep (se 1 (by rfl) ⟨168239, by rfl⟩ : syracuseStep 224319 = 336479) B336479
theorem B224639 : Blo 223812 224639 := bstep (se 1 (by rfl) ⟨168479, by rfl⟩ : syracuseStep 224639 = 336959) B336959
theorem B224667 : Blo 223812 224667 := bstep (se 1 (by rfl) ⟨168500, by rfl⟩ : syracuseStep 224667 = 337001) B337001
theorem B224735 : Blo 223812 224735 := bstep (se 1 (by rfl) ⟨168551, by rfl⟩ : syracuseStep 224735 = 337103) B337103
theorem B224871 : Blo 223812 224871 := bstep (se 1 (by rfl) ⟨168653, by rfl⟩ : syracuseStep 224871 = 337307) B337307
theorem B225019 : Blo 223812 225019 := bstep (se 1 (by rfl) ⟨168764, by rfl⟩ : syracuseStep 225019 = 337529) B337529
theorem B225087 : Blo 223812 225087 := bstep (se 1 (by rfl) ⟨168815, by rfl⟩ : syracuseStep 225087 = 337631) B337631
theorem B225151 : Blo 223812 225151 := bstep (se 1 (by rfl) ⟨168863, by rfl⟩ : syracuseStep 225151 = 337727) B337727
theorem B1142747 : Blo 223812 1142747 := bstep (se 1 (by rfl) ⟨857060, by rfl⟩ : syracuseStep 1142747 = 1714121) B1714121
theorem B225263 : Blo 223812 225263 := bstep (se 1 (by rfl) ⟨168947, by rfl⟩ : syracuseStep 225263 = 337895) B337895
theorem B225275 : Blo 223812 225275 := bstep (se 1 (by rfl) ⟨168956, by rfl⟩ : syracuseStep 225275 = 337913) B337913
theorem B225343 : Blo 223812 225343 := bstep (se 1 (by rfl) ⟨169007, by rfl⟩ : syracuseStep 225343 = 338015) B338015
theorem B225383 : Blo 223812 225383 := bstep (se 1 (by rfl) ⟨169037, by rfl⟩ : syracuseStep 225383 = 338075) B338075
theorem B225407 : Blo 223812 225407 := bstep (se 1 (by rfl) ⟨169055, by rfl⟩ : syracuseStep 225407 = 338111) B338111
theorem B225435 : Blo 223812 225435 := bstep (se 1 (by rfl) ⟨169076, by rfl⟩ : syracuseStep 225435 = 338153) B338153
theorem B1700027 : Blo 223812 1700027 := bstep (se 1 (by rfl) ⟨1275020, by rfl⟩ : syracuseStep 1700027 = 2550041) B2550041
theorem B225639 : Blo 223812 225639 := bstep (se 1 (by rfl) ⟨169229, by rfl⟩ : syracuseStep 225639 = 338459) B338459
theorem B225691 : Blo 223812 225691 := bstep (se 1 (by rfl) ⟨169268, by rfl⟩ : syracuseStep 225691 = 338537) B338537
theorem B323995 : Blo 223812 323995 := bstep (se 1 (by rfl) ⟨242996, by rfl⟩ : syracuseStep 323995 = 485993) B485993
theorem B2585033 : Blo 223812 2585033 := bstep (se 2 (by rfl) ⟨969387, by rfl⟩ : syracuseStep 2585033 = 1938775) B1938775
theorem B1077799 : Blo 223812 1077799 := bstep (se 1 (by rfl) ⟨808349, by rfl⟩ : syracuseStep 1077799 = 1616699) B1616699
theorem B226043 : Blo 223812 226043 := bstep (se 1 (by rfl) ⟨169532, by rfl⟩ : syracuseStep 226043 = 339065) B339065
theorem B2388797 : Blo 223812 2388797 := bstep (se 3 (by rfl) ⟨447899, by rfl⟩ : syracuseStep 2388797 = 895799) B895799
theorem B226111 : Blo 223812 226111 := bstep (se 1 (by rfl) ⟨169583, by rfl⟩ : syracuseStep 226111 = 339167) B339167
theorem B226139 : Blo 223812 226139 := bstep (se 1 (by rfl) ⟨169604, by rfl⟩ : syracuseStep 226139 = 339209) B339209
theorem B226207 : Blo 223812 226207 := bstep (se 1 (by rfl) ⟨169655, by rfl⟩ : syracuseStep 226207 = 339311) B339311
theorem B226287 : Blo 223812 226287 := bstep (se 1 (by rfl) ⟨169715, by rfl⟩ : syracuseStep 226287 = 339431) B339431
theorem B226375 : Blo 223812 226375 := bstep (se 1 (by rfl) ⟨169781, by rfl⟩ : syracuseStep 226375 = 339563) B339563
theorem B2421899 : Blo 223812 2421899 := bstep (se 1 (by rfl) ⟨1816424, by rfl⟩ : syracuseStep 2421899 = 3632849) B3632849
theorem B226459 : Blo 223812 226459 := bstep (se 1 (by rfl) ⟨169844, by rfl⟩ : syracuseStep 226459 = 339689) B339689
theorem B226555 : Blo 223812 226555 := bstep (se 1 (by rfl) ⟨169916, by rfl⟩ : syracuseStep 226555 = 339833) B339833
theorem B226623 : Blo 223812 226623 := bstep (se 1 (by rfl) ⟨169967, by rfl⟩ : syracuseStep 226623 = 339935) B339935
theorem B226791 : Blo 223812 226791 := bstep (se 1 (by rfl) ⟨170093, by rfl⟩ : syracuseStep 226791 = 340187) B340187
theorem B226799 : Blo 223812 226799 := bstep (se 1 (by rfl) ⟨170099, by rfl⟩ : syracuseStep 226799 = 340199) B340199
theorem B1832539 : Blo 223812 1832539 := bstep (se 1 (by rfl) ⟨1374404, by rfl⟩ : syracuseStep 1832539 = 2748809) B2748809
theorem B226907 : Blo 223812 226907 := bstep (se 1 (by rfl) ⟨170180, by rfl⟩ : syracuseStep 226907 = 340361) B340361
theorem B226971 : Blo 223812 226971 := bstep (se 1 (by rfl) ⟨170228, by rfl⟩ : syracuseStep 226971 = 340457) B340457
theorem B227055 : Blo 223812 227055 := bstep (se 1 (by rfl) ⟨170291, by rfl⟩ : syracuseStep 227055 = 340583) B340583
theorem B227143 : Blo 223812 227143 := bstep (se 1 (by rfl) ⟨170357, by rfl⟩ : syracuseStep 227143 = 340715) B340715
theorem B227163 : Blo 223812 227163 := bstep (se 1 (by rfl) ⟨170372, by rfl⟩ : syracuseStep 227163 = 340745) B340745
theorem B227231 : Blo 223812 227231 := bstep (se 1 (by rfl) ⟨170423, by rfl⟩ : syracuseStep 227231 = 340847) B340847
theorem B227399 : Blo 223812 227399 := bstep (se 1 (by rfl) ⟨170549, by rfl⟩ : syracuseStep 227399 = 341099) B341099
theorem B1145015 : Blo 223812 1145015 := bstep (se 1 (by rfl) ⟨858761, by rfl⟩ : syracuseStep 1145015 = 1717523) B1717523
theorem B456935 : Blo 223812 456935 := bstep (se 1 (by rfl) ⟨342701, by rfl⟩ : syracuseStep 456935 = 685403) B685403
theorem B227559 : Blo 223812 227559 := bstep (se 1 (by rfl) ⟨170669, by rfl⟩ : syracuseStep 227559 = 341339) B341339
theorem B227743 : Blo 223812 227743 := bstep (se 1 (by rfl) ⟨170807, by rfl⟩ : syracuseStep 227743 = 341615) B341615
theorem B227791 : Blo 223812 227791 := bstep (se 1 (by rfl) ⟨170843, by rfl⟩ : syracuseStep 227791 = 341687) B341687
theorem B1145501 : Blo 223812 1145501 := bstep (se 3 (by rfl) ⟨214781, by rfl⟩ : syracuseStep 1145501 = 429563) B429563
theorem B1276843 : Blo 223812 1276843 := bstep (se 1 (by rfl) ⟨957632, by rfl⟩ : syracuseStep 1276843 = 1915265) B1915265
theorem B458063 : Blo 223812 458063 := bstep (se 1 (by rfl) ⟨343547, by rfl⟩ : syracuseStep 458063 = 687095) B687095
theorem B425387 : Blo 223812 425387 := bstep (se 1 (by rfl) ⟨319040, by rfl⟩ : syracuseStep 425387 = 638081) B638081
theorem B4849399 : Blo 223812 4849399 := bstep (se 1 (by rfl) ⟨3637049, by rfl⟩ : syracuseStep 4849399 = 7274099) B7274099
theorem B720839 : Blo 223812 720839 := bstep (se 1 (by rfl) ⟨540629, by rfl⟩ : syracuseStep 720839 = 1081259) B1081259
theorem B21921941 : Blo 223812 21921941 := bstep (se 6 (by rfl) ⟨513795, by rfl⟩ : syracuseStep 21921941 = 1027591) B1027591
theorem B2752699 : Blo 223812 2752699 := bstep (se 1 (by rfl) ⟨2064524, by rfl⟩ : syracuseStep 2752699 = 4129049) B4129049
theorem B1540349 : Blo 223812 1540349 := bstep (se 3 (by rfl) ⟨288815, by rfl⟩ : syracuseStep 1540349 = 577631) B577631
theorem B852383 : Blo 223812 852383 := bstep (se 1 (by rfl) ⟨639287, by rfl⟩ : syracuseStep 852383 = 1278575) B1278575
theorem B4325885 : Blo 223812 4325885 := bstep (se 3 (by rfl) ⟨811103, by rfl⟩ : syracuseStep 4325885 = 1622207) B1622207
theorem B5899013 : Blo 223812 5899013 := bstep (se 4 (by rfl) ⟨553032, by rfl⟩ : syracuseStep 5899013 = 1106065) B1106065
theorem B2426431 : Blo 223812 2426431 := bstep (se 1 (by rfl) ⟨1819823, by rfl⟩ : syracuseStep 2426431 = 3639647) B3639647
theorem B427771 : Blo 223812 427771 := bstep (se 1 (by rfl) ⟨320828, by rfl⟩ : syracuseStep 427771 = 641657) B641657
theorem B1378205 : Blo 223812 1378205 := bstep (se 3 (by rfl) ⟨258413, by rfl⟩ : syracuseStep 1378205 = 516827) B516827
theorem B1280033 : Blo 223812 1280033 := bstep (se 2 (by rfl) ⟨480012, by rfl⟩ : syracuseStep 1280033 = 960025) B960025
theorem B2066647 : Blo 223812 2066647 := bstep (se 1 (by rfl) ⟨1549985, by rfl⟩ : syracuseStep 2066647 = 3099971) B3099971
theorem B1149353 : Blo 223812 1149353 := bstep (se 2 (by rfl) ⟨431007, by rfl⟩ : syracuseStep 1149353 = 862015) B862015
theorem B428591 : Blo 223812 428591 := bstep (se 1 (by rfl) ⟨321443, by rfl⟩ : syracuseStep 428591 = 642887) B642887
theorem B756431 : Blo 223812 756431 := bstep (se 1 (by rfl) ⟨567323, by rfl⟩ : syracuseStep 756431 = 1134647) B1134647
theorem B756809 : Blo 223812 756809 := bstep (se 2 (by rfl) ⟨283803, by rfl⟩ : syracuseStep 756809 = 567607) B567607
theorem B1445039 : Blo 223812 1445039 := bstep (se 1 (by rfl) ⟨1083779, by rfl⟩ : syracuseStep 1445039 = 2167559) B2167559
theorem B1314407 : Blo 223812 1314407 := bstep (se 1 (by rfl) ⟨985805, by rfl⟩ : syracuseStep 1314407 = 1971611) B1971611
theorem B2756699 : Blo 223812 2756699 := bstep (se 1 (by rfl) ⟨2067524, by rfl⟩ : syracuseStep 2756699 = 4135049) B4135049
theorem B692459 : Blo 223812 692459 := bstep (se 1 (by rfl) ⟨519344, by rfl⟩ : syracuseStep 692459 = 1038689) B1038689
theorem B1282493 : Blo 223812 1282493 := bstep (se 3 (by rfl) ⟨240467, by rfl⟩ : syracuseStep 1282493 = 480935) B480935
theorem B758267 : Blo 223812 758267 := bstep (se 1 (by rfl) ⟨568700, by rfl⟩ : syracuseStep 758267 = 1137401) B1137401
theorem B758753 : Blo 223812 758753 := bstep (se 2 (by rfl) ⟨284532, by rfl⟩ : syracuseStep 758753 = 569065) B569065
theorem B857243 : Blo 223812 857243 := bstep (se 1 (by rfl) ⟨642932, by rfl⟩ : syracuseStep 857243 = 1285865) B1285865
theorem B3937679 : Blo 223812 3937679 := bstep (se 1 (by rfl) ⟨2953259, by rfl⟩ : syracuseStep 3937679 = 5906519) B5906519
theorem B1840583 : Blo 223812 1840583 := bstep (se 1 (by rfl) ⟨1380437, by rfl⟩ : syracuseStep 1840583 = 2760875) B2760875
theorem B2954909 : Blo 223812 2954909 := bstep (se 3 (by rfl) ⟨554045, by rfl⟩ : syracuseStep 2954909 = 1108091) B1108091
theorem B431993 : Blo 223812 431993 := bstep (se 2 (by rfl) ⟨161997, by rfl⟩ : syracuseStep 431993 = 323995) B323995
theorem B1218493 : Blo 223812 1218493 := bstep (se 3 (by rfl) ⟨228467, by rfl⟩ : syracuseStep 1218493 = 456935) B456935
theorem B2070953 : Blo 223812 2070953 := bstep (se 2 (by rfl) ⟨776607, by rfl⟩ : syracuseStep 2070953 = 1553215) B1553215
theorem B4365251 : Blo 223812 4365251 := bstep (se 1 (by rfl) ⟨3273938, by rfl⟩ : syracuseStep 4365251 = 6547877) B6547877
theorem B761831 : Blo 223812 761831 := bstep (se 1 (by rfl) ⟨571373, by rfl⟩ : syracuseStep 761831 = 1142747) B1142747
theorem B335867 : Blo 223812 335867 := bstep (se 1 (by rfl) ⟨251900, by rfl⟩ : syracuseStep 335867 = 503801) B503801
theorem B335927 : Blo 223812 335927 := bstep (se 1 (by rfl) ⟨251945, by rfl⟩ : syracuseStep 335927 = 503891) B503891
theorem B1384577 : Blo 223812 1384577 := bstep (se 2 (by rfl) ⟨519216, by rfl⟩ : syracuseStep 1384577 = 1038433) B1038433
theorem B336047 : Blo 223812 336047 := bstep (se 1 (by rfl) ⟨252035, by rfl⟩ : syracuseStep 336047 = 504071) B504071
theorem B1450187 : Blo 223812 1450187 := bstep (se 1 (by rfl) ⟨1087640, by rfl⟩ : syracuseStep 1450187 = 2175281) B2175281
theorem B336251 : Blo 223812 336251 := bstep (se 1 (by rfl) ⟨252188, by rfl⟩ : syracuseStep 336251 = 504377) B504377
theorem B336425 : Blo 223812 336425 := bstep (se 2 (by rfl) ⟨126159, by rfl⟩ : syracuseStep 336425 = 252319) B252319
theorem B336521 : Blo 223812 336521 := bstep (se 2 (by rfl) ⟨126195, by rfl⟩ : syracuseStep 336521 = 252391) B252391
theorem B1614599 : Blo 223812 1614599 := bstep (se 1 (by rfl) ⟨1210949, by rfl⟩ : syracuseStep 1614599 = 2421899) B2421899
theorem B336731 : Blo 223812 336731 := bstep (se 1 (by rfl) ⟨252548, by rfl⟩ : syracuseStep 336731 = 505097) B505097
theorem B336767 : Blo 223812 336767 := bstep (se 1 (by rfl) ⟨252575, by rfl⟩ : syracuseStep 336767 = 505151) B505151
theorem B336839 : Blo 223812 336839 := bstep (se 1 (by rfl) ⟨252629, by rfl⟩ : syracuseStep 336839 = 505259) B505259
theorem B337055 : Blo 223812 337055 := bstep (se 1 (by rfl) ⟨252791, by rfl⟩ : syracuseStep 337055 = 505583) B505583
theorem B337199 : Blo 223812 337199 := bstep (se 1 (by rfl) ⟨252899, by rfl⟩ : syracuseStep 337199 = 505799) B505799
theorem B763343 : Blo 223812 763343 := bstep (se 1 (by rfl) ⟨572507, by rfl⟩ : syracuseStep 763343 = 1145015) B1145015
theorem B337391 : Blo 223812 337391 := bstep (se 1 (by rfl) ⟨253043, by rfl⟩ : syracuseStep 337391 = 506087) B506087
theorem B337403 : Blo 223812 337403 := bstep (se 1 (by rfl) ⟨253052, by rfl⟩ : syracuseStep 337403 = 506105) B506105
theorem B337439 : Blo 223812 337439 := bstep (se 1 (by rfl) ⟨253079, by rfl⟩ : syracuseStep 337439 = 506159) B506159
theorem B337583 : Blo 223812 337583 := bstep (se 1 (by rfl) ⟨253187, by rfl⟩ : syracuseStep 337583 = 506375) B506375
theorem B337673 : Blo 223812 337673 := bstep (se 2 (by rfl) ⟨126627, by rfl⟩ : syracuseStep 337673 = 253255) B253255
theorem B763667 : Blo 223812 763667 := bstep (se 1 (by rfl) ⟨572750, by rfl⟩ : syracuseStep 763667 = 1145501) B1145501
theorem B337703 : Blo 223812 337703 := bstep (se 1 (by rfl) ⟨253277, by rfl⟩ : syracuseStep 337703 = 506555) B506555
theorem B4925519 : Blo 223812 4925519 := bstep (se 1 (by rfl) ⟨3694139, by rfl⟩ : syracuseStep 4925519 = 7388279) B7388279
theorem B305375 : Blo 223812 305375 := bstep (se 1 (by rfl) ⟨229031, by rfl⟩ : syracuseStep 305375 = 458063) B458063
theorem B4598045 : Blo 223812 4598045 := bstep (se 3 (by rfl) ⟨862133, by rfl⟩ : syracuseStep 4598045 = 1724267) B1724267
theorem B6465865 : Blo 223812 6465865 := bstep (se 2 (by rfl) ⟨2424699, by rfl⟩ : syracuseStep 6465865 = 4849399) B4849399
theorem B338303 : Blo 223812 338303 := bstep (se 1 (by rfl) ⟨253727, by rfl⟩ : syracuseStep 338303 = 507455) B507455
theorem B1714607 : Blo 223812 1714607 := bstep (se 1 (by rfl) ⟨1285955, by rfl⟩ : syracuseStep 1714607 = 2571911) B2571911
theorem B1386953 : Blo 223812 1386953 := bstep (se 2 (by rfl) ⟨520107, by rfl⟩ : syracuseStep 1386953 = 1040215) B1040215
theorem B2173513 : Blo 223812 2173513 := bstep (se 2 (by rfl) ⟨815067, by rfl⟩ : syracuseStep 2173513 = 1630135) B1630135
theorem B338543 : Blo 223812 338543 := bstep (se 1 (by rfl) ⟨253907, by rfl⟩ : syracuseStep 338543 = 507815) B507815
theorem B338759 : Blo 223812 338759 := bstep (se 1 (by rfl) ⟨254069, by rfl⟩ : syracuseStep 338759 = 508139) B508139
theorem B1289465 : Blo 223812 1289465 := bstep (se 2 (by rfl) ⟨483549, by rfl⟩ : syracuseStep 1289465 = 967099) B967099
theorem B339359 : Blo 223812 339359 := bstep (se 1 (by rfl) ⟨254519, by rfl⟩ : syracuseStep 339359 = 509039) B509039
theorem B339623 : Blo 223812 339623 := bstep (se 1 (by rfl) ⟨254717, by rfl⟩ : syracuseStep 339623 = 509435) B509435
theorem B339647 : Blo 223812 339647 := bstep (se 1 (by rfl) ⟨254735, by rfl⟩ : syracuseStep 339647 = 509471) B509471
theorem B765665 : Blo 223812 765665 := bstep (se 2 (by rfl) ⟨287124, by rfl⟩ : syracuseStep 765665 = 574249) B574249
theorem B339743 : Blo 223812 339743 := bstep (se 1 (by rfl) ⟨254807, by rfl⟩ : syracuseStep 339743 = 509615) B509615
theorem B503675 : Blo 223812 503675 := bstep (se 1 (by rfl) ⟨377756, by rfl⟩ : syracuseStep 503675 = 755513) B755513
theorem B340031 : Blo 223812 340031 := bstep (se 1 (by rfl) ⟨255023, by rfl⟩ : syracuseStep 340031 = 510047) B510047
theorem B340223 : Blo 223812 340223 := bstep (se 1 (by rfl) ⟨255167, by rfl⟩ : syracuseStep 340223 = 510335) B510335
theorem B340265 : Blo 223812 340265 := bstep (se 2 (by rfl) ⟨127599, by rfl⟩ : syracuseStep 340265 = 255199) B255199
theorem B7811599 : Blo 223812 7811599 := bstep (se 1 (by rfl) ⟨5858699, by rfl⟩ : syracuseStep 7811599 = 11717399) B11717399
theorem B340535 : Blo 223812 340535 := bstep (se 1 (by rfl) ⟨255401, by rfl⟩ : syracuseStep 340535 = 510803) B510803
theorem B340775 : Blo 223812 340775 := bstep (se 1 (by rfl) ⟨255581, by rfl⟩ : syracuseStep 340775 = 511163) B511163
theorem B340895 : Blo 223812 340895 := bstep (se 1 (by rfl) ⟨255671, by rfl⟩ : syracuseStep 340895 = 511343) B511343
theorem B537977 : Blo 223812 537977 := bstep (se 2 (by rfl) ⟨201741, by rfl⟩ : syracuseStep 537977 = 403483) B403483
theorem B341369 : Blo 223812 341369 := bstep (se 2 (by rfl) ⟨128013, by rfl⟩ : syracuseStep 341369 = 256027) B256027
theorem B341375 : Blo 223812 341375 := bstep (se 1 (by rfl) ⟨256031, by rfl⟩ : syracuseStep 341375 = 512063) B512063
theorem B341531 : Blo 223812 341531 := bstep (se 1 (by rfl) ⟨256148, by rfl⟩ : syracuseStep 341531 = 512297) B512297
theorem B570959 : Blo 223812 570959 := bstep (se 1 (by rfl) ⟨428219, by rfl⟩ : syracuseStep 570959 = 856439) B856439
theorem B341711 : Blo 223812 341711 := bstep (se 1 (by rfl) ⟨256283, by rfl⟩ : syracuseStep 341711 = 512567) B512567
theorem B505619 : Blo 223812 505619 := bstep (se 1 (by rfl) ⟨379214, by rfl⟩ : syracuseStep 505619 = 758429) B758429
theorem B505979 : Blo 223812 505979 := bstep (se 1 (by rfl) ⟨379484, by rfl⟩ : syracuseStep 505979 = 758969) B758969
theorem B571607 : Blo 223812 571607 := bstep (se 1 (by rfl) ⟨428705, by rfl⟩ : syracuseStep 571607 = 857411) B857411
theorem B506249 : Blo 223812 506249 := bstep (se 2 (by rfl) ⟨189843, by rfl⟩ : syracuseStep 506249 = 379687) B379687
theorem B3258767 : Blo 223812 3258767 := bstep (se 1 (by rfl) ⟨2444075, by rfl⟩ : syracuseStep 3258767 = 4888151) B4888151
theorem B637409 : Blo 223812 637409 := bstep (se 2 (by rfl) ⟨239028, by rfl⟩ : syracuseStep 637409 = 478057) B478057
theorem B506681 : Blo 223812 506681 := bstep (se 2 (by rfl) ⟨190005, by rfl⟩ : syracuseStep 506681 = 380011) B380011
theorem B965459 : Blo 223812 965459 := bstep (se 1 (by rfl) ⟨724094, by rfl⟩ : syracuseStep 965459 = 1448189) B1448189
theorem B507041 : Blo 223812 507041 := bstep (se 2 (by rfl) ⟨190140, by rfl⟩ : syracuseStep 507041 = 380281) B380281
theorem B507311 : Blo 223812 507311 := bstep (se 1 (by rfl) ⟨380483, by rfl⟩ : syracuseStep 507311 = 760967) B760967
theorem B639049 : Blo 223812 639049 := bstep (se 2 (by rfl) ⟨239643, by rfl⟩ : syracuseStep 639049 = 479287) B479287
theorem B507977 : Blo 223812 507977 := bstep (se 2 (by rfl) ⟨190491, by rfl⟩ : syracuseStep 507977 = 380983) B380983
theorem B409769 : Blo 223812 409769 := bstep (se 2 (by rfl) ⟨153663, by rfl⟩ : syracuseStep 409769 = 307327) B307327
theorem B573743 : Blo 223812 573743 := bstep (se 1 (by rfl) ⟨430307, by rfl⟩ : syracuseStep 573743 = 860615) B860615
theorem B508391 : Blo 223812 508391 := bstep (se 1 (by rfl) ⟨381293, by rfl⟩ : syracuseStep 508391 = 762587) B762587
theorem B508409 : Blo 223812 508409 := bstep (se 2 (by rfl) ⟨190653, by rfl⟩ : syracuseStep 508409 = 381307) B381307
theorem B508499 : Blo 223812 508499 := bstep (se 1 (by rfl) ⟨381374, by rfl⟩ : syracuseStep 508499 = 762749) B762749
theorem B508679 : Blo 223812 508679 := bstep (se 1 (by rfl) ⟨381509, by rfl⟩ : syracuseStep 508679 = 763019) B763019
theorem B130892591 : Blo 223812 130892591 := bstep (se 1 (by rfl) ⟨98169443, by rfl⟩ : syracuseStep 130892591 = 196338887) B196338887
theorem B508769 : Blo 223812 508769 := bstep (se 2 (by rfl) ⟨190788, by rfl⟩ : syracuseStep 508769 = 381577) B381577
theorem B3884111 : Blo 223812 3884111 := bstep (se 1 (by rfl) ⟨2913083, by rfl⟩ : syracuseStep 3884111 = 5826167) B5826167
theorem B378175 : Blo 223812 378175 := bstep (se 1 (by rfl) ⟨283631, by rfl⟩ : syracuseStep 378175 = 567263) B567263
theorem B607559 : Blo 223812 607559 := bstep (se 1 (by rfl) ⟨455669, by rfl⟩ : syracuseStep 607559 = 911339) B911339
theorem B640507 : Blo 223812 640507 := bstep (se 1 (by rfl) ⟨480380, by rfl⟩ : syracuseStep 640507 = 960761) B960761
theorem B575201 : Blo 223812 575201 := bstep (se 2 (by rfl) ⟨215700, by rfl⟩ : syracuseStep 575201 = 431401) B431401
theorem B509759 : Blo 223812 509759 := bstep (se 1 (by rfl) ⟨382319, by rfl⟩ : syracuseStep 509759 = 764639) B764639
theorem B378857 : Blo 223812 378857 := bstep (se 2 (by rfl) ⟨142071, by rfl⟩ : syracuseStep 378857 = 284143) B284143
theorem B2443385 : Blo 223812 2443385 := bstep (se 2 (by rfl) ⟨916269, by rfl⟩ : syracuseStep 2443385 = 1832539) B1832539
theorem B379343 : Blo 223812 379343 := bstep (se 1 (by rfl) ⟨284507, by rfl⟩ : syracuseStep 379343 = 569015) B569015
theorem B772831 : Blo 223812 772831 := bstep (se 1 (by rfl) ⟨579623, by rfl⟩ : syracuseStep 772831 = 1159247) B1159247
theorem B1133351 : Blo 223812 1133351 := bstep (se 1 (by rfl) ⟨850013, by rfl⟩ : syracuseStep 1133351 = 1700027) B1700027
theorem B641999 : Blo 223812 641999 := bstep (se 1 (by rfl) ⟨481499, by rfl⟩ : syracuseStep 641999 = 962999) B962999
theorem B1723355 : Blo 223812 1723355 := bstep (se 1 (by rfl) ⟨1292516, by rfl⟩ : syracuseStep 1723355 = 2585033) B2585033
theorem B1592531 : Blo 223812 1592531 := bstep (se 1 (by rfl) ⟨1194398, by rfl⟩ : syracuseStep 1592531 = 2388797) B2388797
theorem B1035659 : Blo 223812 1035659 := bstep (se 1 (by rfl) ⟨776744, by rfl⟩ : syracuseStep 1035659 = 1553489) B1553489
theorem B380315 : Blo 223812 380315 := bstep (se 1 (by rfl) ⟨285236, by rfl⟩ : syracuseStep 380315 = 570473) B570473
theorem B512027 : Blo 223812 512027 := bstep (se 1 (by rfl) ⟨384020, by rfl⟩ : syracuseStep 512027 = 768041) B768041
theorem B971531 : Blo 223812 971531 := bstep (se 1 (by rfl) ⟨728648, by rfl⟩ : syracuseStep 971531 = 1457297) B1457297
theorem B5624657 : Blo 223812 5624657 := bstep (se 2 (by rfl) ⟨2109246, by rfl⟩ : syracuseStep 5624657 = 4218493) B4218493
theorem B2872199 : Blo 223812 2872199 := bstep (se 1 (by rfl) ⟨2154149, by rfl⟩ : syracuseStep 2872199 = 4308299) B4308299
theorem B283591 : Blo 223812 283591 := bstep (se 1 (by rfl) ⟨212693, by rfl⟩ : syracuseStep 283591 = 425387) B425387
theorem B1922237 : Blo 223812 1922237 := bstep (se 3 (by rfl) ⟨360419, by rfl⟩ : syracuseStep 1922237 = 720839) B720839
theorem B1037519 : Blo 223812 1037519 := bstep (se 1 (by rfl) ⟨778139, by rfl⟩ : syracuseStep 1037519 = 1556279) B1556279
theorem B1038395 : Blo 223812 1038395 := bstep (se 1 (by rfl) ⟨778796, by rfl⟩ : syracuseStep 1038395 = 1557593) B1557593
theorem B546887 : Blo 223812 546887 := bstep (se 1 (by rfl) ⟨410165, by rfl⟩ : syracuseStep 546887 = 820331) B820331
theorem B252031 : Blo 223812 252031 := bstep (se 1 (by rfl) ⟨189023, by rfl⟩ : syracuseStep 252031 = 378047) B378047
theorem B546955 : Blo 223812 546955 := bstep (se 1 (by rfl) ⟨410216, by rfl⟩ : syracuseStep 546955 = 820433) B820433
theorem B383359 : Blo 223812 383359 := bstep (se 1 (by rfl) ⟨287519, by rfl⟩ : syracuseStep 383359 = 575039) B575039
theorem B5495201 : Blo 223812 5495201 := bstep (se 2 (by rfl) ⟨2060700, by rfl⟩ : syracuseStep 5495201 = 4121401) B4121401
theorem B2185703 : Blo 223812 2185703 := bstep (se 1 (by rfl) ⟨1639277, by rfl⟩ : syracuseStep 2185703 = 3278555) B3278555
theorem B3234437 : Blo 223812 3234437 := bstep (se 4 (by rfl) ⟨303228, by rfl⟩ : syracuseStep 3234437 = 606457) B606457
theorem B645803 : Blo 223812 645803 := bstep (se 1 (by rfl) ⟨484352, by rfl⟩ : syracuseStep 645803 = 968705) B968705
theorem B252607 : Blo 223812 252607 := bstep (se 1 (by rfl) ⟨189455, by rfl⟩ : syracuseStep 252607 = 378911) B378911
theorem B940787 : Blo 223812 940787 := bstep (se 1 (by rfl) ⟨705590, by rfl⟩ : syracuseStep 940787 = 1411181) B1411181
theorem B383791 : Blo 223812 383791 := bstep (se 1 (by rfl) ⟨287843, by rfl⟩ : syracuseStep 383791 = 575687) B575687
theorem B613183 : Blo 223812 613183 := bstep (se 1 (by rfl) ⟨459887, by rfl⟩ : syracuseStep 613183 = 919775) B919775
theorem B2743955 : Blo 223812 2743955 := bstep (se 1 (by rfl) ⟨2057966, by rfl⟩ : syracuseStep 2743955 = 4115933) B4115933
theorem B161014169 : Blo 223812 161014169 := bstep (se 2 (by rfl) ⟨60380313, by rfl⟩ : syracuseStep 161014169 = 120760627) B120760627
theorem B254623 : Blo 223812 254623 := bstep (se 1 (by rfl) ⟨190967, by rfl⟩ : syracuseStep 254623 = 381935) B381935
theorem B5563181 : Blo 223812 5563181 := bstep (se 3 (by rfl) ⟨1043096, by rfl⟩ : syracuseStep 5563181 = 2086193) B2086193
theorem B812027 : Blo 223812 812027 := bstep (se 1 (by rfl) ⟨609020, by rfl⟩ : syracuseStep 812027 = 1218041) B1218041
theorem B1434809 : Blo 223812 1434809 := bstep (se 2 (by rfl) ⟨538053, by rfl⟩ : syracuseStep 1434809 = 1076107) B1076107
theorem B976103 : Blo 223812 976103 := bstep (se 1 (by rfl) ⟨732077, by rfl⟩ : syracuseStep 976103 = 1464155) B1464155
theorem B287975 : Blo 223812 287975 := bstep (se 1 (by rfl) ⟨215981, by rfl⟩ : syracuseStep 287975 = 431963) B431963
theorem B1140155 : Blo 223812 1140155 := bstep (se 1 (by rfl) ⟨855116, by rfl⟩ : syracuseStep 1140155 = 1710233) B1710233
theorem B321079 : Blo 223812 321079 := bstep (se 1 (by rfl) ⟨240809, by rfl⟩ : syracuseStep 321079 = 481619) B481619
theorem B1631897 : Blo 223812 1631897 := bstep (se 2 (by rfl) ⟨611961, by rfl⟩ : syracuseStep 1631897 = 1223923) B1223923
theorem B2942647 : Blo 223812 2942647 := bstep (se 1 (by rfl) ⟨2206985, by rfl⟩ : syracuseStep 2942647 = 4413971) B4413971
theorem B4418023 : Blo 223812 4418023 := bstep (se 1 (by rfl) ⟨3313517, by rfl⟩ : syracuseStep 4418023 = 6627035) B6627035
theorem B223899 : Blo 223812 223899 := bstep (se 1 (by rfl) ⟨167924, by rfl⟩ : syracuseStep 223899 = 335849) B335849
theorem B486395 : Blo 223812 486395 := bstep (se 1 (by rfl) ⟨364796, by rfl⟩ : syracuseStep 486395 = 729593) B729593
theorem B224367 : Blo 223812 224367 := bstep (se 1 (by rfl) ⟨168275, by rfl⟩ : syracuseStep 224367 = 336551) B336551
theorem B224447 : Blo 223812 224447 := bstep (se 1 (by rfl) ⟨168335, by rfl⟩ : syracuseStep 224447 = 336671) B336671
theorem B224463 : Blo 223812 224463 := bstep (se 1 (by rfl) ⟨168347, by rfl⟩ : syracuseStep 224463 = 336695) B336695
theorem B224583 : Blo 223812 224583 := bstep (se 1 (by rfl) ⟨168437, by rfl⟩ : syracuseStep 224583 = 336875) B336875
theorem B1437065 : Blo 223812 1437065 := bstep (se 2 (by rfl) ⟨538899, by rfl⟩ : syracuseStep 1437065 = 1077799) B1077799
theorem B21884579 : Blo 223812 21884579 := bstep (se 1 (by rfl) ⟨16413434, by rfl⟩ : syracuseStep 21884579 = 32826869) B32826869
theorem B2551499 : Blo 223812 2551499 := bstep (se 1 (by rfl) ⟨1913624, by rfl⟩ : syracuseStep 2551499 = 3827249) B3827249
theorem B225311 : Blo 223812 225311 := bstep (se 1 (by rfl) ⟨168983, by rfl⟩ : syracuseStep 225311 = 337967) B337967
theorem B225487 : Blo 223812 225487 := bstep (se 1 (by rfl) ⟨169115, by rfl⟩ : syracuseStep 225487 = 338231) B338231
theorem B225607 : Blo 223812 225607 := bstep (se 1 (by rfl) ⟨169205, by rfl⟩ : syracuseStep 225607 = 338411) B338411
theorem B226075 : Blo 223812 226075 := bstep (se 1 (by rfl) ⟨169556, by rfl⟩ : syracuseStep 226075 = 339113) B339113
theorem B1143719 : Blo 223812 1143719 := bstep (se 1 (by rfl) ⟨857789, by rfl⟩ : syracuseStep 1143719 = 1715579) B1715579
theorem B226351 : Blo 223812 226351 := bstep (se 1 (by rfl) ⟨169763, by rfl⟩ : syracuseStep 226351 = 339527) B339527
theorem B226471 : Blo 223812 226471 := bstep (se 1 (by rfl) ⟨169853, by rfl⟩ : syracuseStep 226471 = 339707) B339707
theorem B226919 : Blo 223812 226919 := bstep (se 1 (by rfl) ⟨170189, by rfl⟩ : syracuseStep 226919 = 340379) B340379
theorem B1701485 : Blo 223812 1701485 := bstep (se 3 (by rfl) ⟨319028, by rfl⟩ : syracuseStep 1701485 = 638057) B638057
theorem B2062045 : Blo 223812 2062045 := bstep (se 3 (by rfl) ⟨386633, by rfl⟩ : syracuseStep 2062045 = 773267) B773267
theorem B1275659 : Blo 223812 1275659 := bstep (se 1 (by rfl) ⟨956744, by rfl⟩ : syracuseStep 1275659 = 1913489) B1913489
theorem B227199 : Blo 223812 227199 := bstep (se 1 (by rfl) ⟨170399, by rfl⟩ : syracuseStep 227199 = 340799) B340799
theorem B227295 : Blo 223812 227295 := bstep (se 1 (by rfl) ⟨170471, by rfl⟩ : syracuseStep 227295 = 340943) B340943
theorem B227323 : Blo 223812 227323 := bstep (se 1 (by rfl) ⟨170492, by rfl⟩ : syracuseStep 227323 = 340985) B340985
theorem B227355 : Blo 223812 227355 := bstep (se 1 (by rfl) ⟨170516, by rfl⟩ : syracuseStep 227355 = 341033) B341033
theorem B227375 : Blo 223812 227375 := bstep (se 1 (by rfl) ⟨170531, by rfl⟩ : syracuseStep 227375 = 341063) B341063
theorem B718969 : Blo 223812 718969 := bstep (se 2 (by rfl) ⟨269613, by rfl⟩ : syracuseStep 718969 = 539227) B539227
theorem B227495 : Blo 223812 227495 := bstep (se 1 (by rfl) ⟨170621, by rfl⟩ : syracuseStep 227495 = 341243) B341243
theorem B1702457 : Blo 223812 1702457 := bstep (se 2 (by rfl) ⟨638421, by rfl⟩ : syracuseStep 1702457 = 1276843) B1276843
theorem B850925 : Blo 223812 850925 := bstep (se 3 (by rfl) ⟨159548, by rfl⟩ : syracuseStep 850925 = 319097) B319097
theorem B3112343 : Blo 223812 3112343 := bstep (se 1 (by rfl) ⟨2334257, by rfl⟩ : syracuseStep 3112343 = 4668515) B4668515
theorem B852065 : Blo 223812 852065 := bstep (se 2 (by rfl) ⟨319524, by rfl⟩ : syracuseStep 852065 = 639049) B639049
theorem B14614627 : Blo 223812 14614627 := bstep (se 1 (by rfl) ⟨10960970, by rfl⟩ : syracuseStep 14614627 = 21921941) B21921941
theorem B3670265 : Blo 223812 3670265 := bstep (se 2 (by rfl) ⟨1376349, by rfl⟩ : syracuseStep 3670265 = 2752699) B2752699
theorem B2883923 : Blo 223812 2883923 := bstep (se 1 (by rfl) ⟨2162942, by rfl⟩ : syracuseStep 2883923 = 4325885) B4325885
theorem B3932675 : Blo 223812 3932675 := bstep (se 1 (by rfl) ⟨2949506, by rfl⟩ : syracuseStep 3932675 = 5899013) B5899013
theorem B2589407 : Blo 223812 2589407 := bstep (se 1 (by rfl) ⟨1942055, by rfl⟩ : syracuseStep 2589407 = 3884111) B3884111
theorem B2917093 : Blo 223812 2917093 := bstep (se 4 (by rfl) ⟨273477, by rfl⟩ : syracuseStep 2917093 = 546955) B546955
theorem B918803 : Blo 223812 918803 := bstep (se 1 (by rfl) ⟨689102, by rfl⟩ : syracuseStep 918803 = 1378205) B1378205
theorem B853355 : Blo 223812 853355 := bstep (se 1 (by rfl) ⟨640016, by rfl⟩ : syracuseStep 853355 = 1280033) B1280033
theorem B755567 : Blo 223812 755567 := bstep (se 1 (by rfl) ⟨566675, by rfl⟩ : syracuseStep 755567 = 1133351) B1133351
theorem B427999 : Blo 223812 427999 := bstep (se 1 (by rfl) ⟨320999, by rfl⟩ : syracuseStep 427999 = 641999) B641999
theorem B1148903 : Blo 223812 1148903 := bstep (se 1 (by rfl) ⟨861677, by rfl⟩ : syracuseStep 1148903 = 1723355) B1723355
theorem B854009 : Blo 223812 854009 := bstep (se 2 (by rfl) ⟨320253, by rfl⟩ : syracuseStep 854009 = 640507) B640507
theorem B428105 : Blo 223812 428105 := bstep (se 2 (by rfl) ⟨160539, by rfl⟩ : syracuseStep 428105 = 321079) B321079
theorem B349046909 : Blo 223812 349046909 := bstep (se 3 (by rfl) ⟨65446295, by rfl⟩ : syracuseStep 349046909 = 130892591) B130892591
theorem B690439 : Blo 223812 690439 := bstep (se 1 (by rfl) ⟨517829, by rfl⟩ : syracuseStep 690439 = 1035659) B1035659
theorem B1837799 : Blo 223812 1837799 := bstep (se 1 (by rfl) ⟨1378349, by rfl⟩ : syracuseStep 1837799 = 2756699) B2756699
theorem B461639 : Blo 223812 461639 := bstep (se 1 (by rfl) ⟨346229, by rfl⟩ : syracuseStep 461639 = 692459) B692459
theorem B2755529 : Blo 223812 2755529 := bstep (se 2 (by rfl) ⟨1033323, by rfl⟩ : syracuseStep 2755529 = 2066647) B2066647
theorem B854995 : Blo 223812 854995 := bstep (se 1 (by rfl) ⟨641246, by rfl⟩ : syracuseStep 854995 = 1282493) B1282493
theorem B8621153 : Blo 223812 8621153 := bstep (se 2 (by rfl) ⟨3232932, by rfl⟩ : syracuseStep 8621153 = 6465865) B6465865
theorem B1281491 : Blo 223812 1281491 := bstep (se 1 (by rfl) ⟨961118, by rfl⟩ : syracuseStep 1281491 = 1922237) B1922237
theorem B691679 : Blo 223812 691679 := bstep (se 1 (by rfl) ⟨518759, by rfl⟩ : syracuseStep 691679 = 1037519) B1037519
theorem B2625119 : Blo 223812 2625119 := bstep (se 1 (by rfl) ⟨1968839, by rfl⟩ : syracuseStep 2625119 = 3937679) B3937679
theorem B1969939 : Blo 223812 1969939 := bstep (se 1 (by rfl) ⟨1477454, by rfl⟩ : syracuseStep 1969939 = 2954909) B2954909
theorem B692263 : Blo 223812 692263 := bstep (se 1 (by rfl) ⟨519197, by rfl⟩ : syracuseStep 692263 = 1038395) B1038395
theorem B364591 : Blo 223812 364591 := bstep (se 1 (by rfl) ⟨273443, by rfl⟩ : syracuseStep 364591 = 546887) B546887
theorem B1380635 : Blo 223812 1380635 := bstep (se 1 (by rfl) ⟨1035476, by rfl⟩ : syracuseStep 1380635 = 2070953) B2070953
theorem B430535 : Blo 223812 430535 := bstep (se 1 (by rfl) ⟨322901, by rfl⟩ : syracuseStep 430535 = 645803) B645803
theorem B627191 : Blo 223812 627191 := bstep (se 1 (by rfl) ⟨470393, by rfl⟩ : syracuseStep 627191 = 940787) B940787
theorem B1151981 : Blo 223812 1151981 := bstep (se 3 (by rfl) ⟨215996, by rfl⟩ : syracuseStep 1151981 = 431993) B431993
theorem B923051 : Blo 223812 923051 := bstep (se 1 (by rfl) ⟨692288, by rfl⟩ : syracuseStep 923051 = 1384577) B1384577
theorem B3708787 : Blo 223812 3708787 := bstep (se 1 (by rfl) ⟨2781590, by rfl⟩ : syracuseStep 3708787 = 5563181) B5563181
theorem B956539 : Blo 223812 956539 := bstep (se 1 (by rfl) ⟨717404, by rfl⟩ : syracuseStep 956539 = 1434809) B1434809
theorem B760103 : Blo 223812 760103 := bstep (se 1 (by rfl) ⟨570077, by rfl⟩ : syracuseStep 760103 = 1140155) B1140155
theorem B1087931 : Blo 223812 1087931 := bstep (se 1 (by rfl) ⟨815948, by rfl⟩ : syracuseStep 1087931 = 1631897) B1631897
theorem B3283679 : Blo 223812 3283679 := bstep (se 1 (by rfl) ⟨2462759, by rfl⟩ : syracuseStep 3283679 = 4925519) B4925519
theorem B924635 : Blo 223812 924635 := bstep (se 1 (by rfl) ⟨693476, by rfl⟩ : syracuseStep 924635 = 1386953) B1386953
theorem B859643 : Blo 223812 859643 := bstep (se 1 (by rfl) ⟨644732, by rfl⟩ : syracuseStep 859643 = 1289465) B1289465
theorem B958043 : Blo 223812 958043 := bstep (se 1 (by rfl) ⟨718532, by rfl⟩ : syracuseStep 958043 = 1437065) B1437065
theorem B14589719 : Blo 223812 14589719 := bstep (se 1 (by rfl) ⟨10942289, by rfl⟩ : syracuseStep 14589719 = 21884579) B21884579
theorem B335783 : Blo 223812 335783 := bstep (se 1 (by rfl) ⟨251837, by rfl⟩ : syracuseStep 335783 = 503675) B503675
theorem B958625 : Blo 223812 958625 := bstep (se 2 (by rfl) ⟨359484, by rfl⟩ : syracuseStep 958625 = 718969) B718969
theorem B336041 : Blo 223812 336041 := bstep (se 2 (by rfl) ⟨126015, by rfl⟩ : syracuseStep 336041 = 252031) B252031
theorem B762479 : Blo 223812 762479 := bstep (se 1 (by rfl) ⟨571859, by rfl⟩ : syracuseStep 762479 = 1143719) B1143719
theorem B336809 : Blo 223812 336809 := bstep (se 2 (by rfl) ⟨126303, by rfl⟩ : syracuseStep 336809 = 252607) B252607
theorem B337079 : Blo 223812 337079 := bstep (se 1 (by rfl) ⟨252809, by rfl⟩ : syracuseStep 337079 = 505619) B505619
theorem B337319 : Blo 223812 337319 := bstep (se 1 (by rfl) ⟨252989, by rfl⟩ : syracuseStep 337319 = 505979) B505979
theorem B337499 : Blo 223812 337499 := bstep (se 1 (by rfl) ⟨253124, by rfl⟩ : syracuseStep 337499 = 506249) B506249
theorem B2172511 : Blo 223812 2172511 := bstep (se 1 (by rfl) ⟨1629383, by rfl⟩ : syracuseStep 2172511 = 3258767) B3258767
theorem B337787 : Blo 223812 337787 := bstep (se 1 (by rfl) ⟨253340, by rfl⟩ : syracuseStep 337787 = 506681) B506681
theorem B567283 : Blo 223812 567283 := bstep (se 1 (by rfl) ⟨425462, by rfl⟩ : syracuseStep 567283 = 850925) B850925
theorem B338027 : Blo 223812 338027 := bstep (se 1 (by rfl) ⟨253520, by rfl⟩ : syracuseStep 338027 = 507041) B507041
theorem B2074895 : Blo 223812 2074895 := bstep (se 1 (by rfl) ⟨1556171, by rfl⟩ : syracuseStep 2074895 = 3112343) B3112343
theorem B338207 : Blo 223812 338207 := bstep (se 1 (by rfl) ⟨253655, by rfl⟩ : syracuseStep 338207 = 507311) B507311
theorem B338651 : Blo 223812 338651 := bstep (se 1 (by rfl) ⟨253988, by rfl⟩ : syracuseStep 338651 = 507977) B507977
theorem B273179 : Blo 223812 273179 := bstep (se 1 (by rfl) ⟨204884, by rfl⟩ : syracuseStep 273179 = 409769) B409769
theorem B1026899 : Blo 223812 1026899 := bstep (se 1 (by rfl) ⟨770174, by rfl⟩ : syracuseStep 1026899 = 1540349) B1540349
theorem B568255 : Blo 223812 568255 := bstep (se 1 (by rfl) ⟨426191, by rfl⟩ : syracuseStep 568255 = 852383) B852383
theorem B338927 : Blo 223812 338927 := bstep (se 1 (by rfl) ⟨254195, by rfl⟩ : syracuseStep 338927 = 508391) B508391
theorem B338939 : Blo 223812 338939 := bstep (se 1 (by rfl) ⟨254204, by rfl⟩ : syracuseStep 338939 = 508409) B508409
theorem B338999 : Blo 223812 338999 := bstep (se 1 (by rfl) ⟨254249, by rfl⟩ : syracuseStep 338999 = 508499) B508499
theorem B339119 : Blo 223812 339119 := bstep (se 1 (by rfl) ⟨254339, by rfl⟩ : syracuseStep 339119 = 508679) B508679
theorem B339179 : Blo 223812 339179 := bstep (se 1 (by rfl) ⟨254384, by rfl⟩ : syracuseStep 339179 = 508769) B508769
theorem B339497 : Blo 223812 339497 := bstep (se 2 (by rfl) ⟨127311, by rfl⟩ : syracuseStep 339497 = 254623) B254623
theorem B339839 : Blo 223812 339839 := bstep (se 1 (by rfl) ⟨254879, by rfl⟩ : syracuseStep 339839 = 509759) B509759
theorem B766235 : Blo 223812 766235 := bstep (se 1 (by rfl) ⟨574676, by rfl⟩ : syracuseStep 766235 = 1149353) B1149353
theorem B504233 : Blo 223812 504233 := bstep (se 2 (by rfl) ⟨189087, by rfl⟩ : syracuseStep 504233 = 378175) B378175
theorem B504287 : Blo 223812 504287 := bstep (se 1 (by rfl) ⟨378215, by rfl⟩ : syracuseStep 504287 = 756431) B756431
theorem B504539 : Blo 223812 504539 := bstep (se 1 (by rfl) ⟨378404, by rfl⟩ : syracuseStep 504539 = 756809) B756809
theorem B963359 : Blo 223812 963359 := bstep (se 1 (by rfl) ⟨722519, by rfl⟩ : syracuseStep 963359 = 1445039) B1445039
theorem B1061687 : Blo 223812 1061687 := bstep (se 1 (by rfl) ⟨796265, by rfl⟩ : syracuseStep 1061687 = 1592531) B1592531
theorem B3257333 : Blo 223812 3257333 := bstep (se 5 (by rfl) ⟨152687, by rfl⟩ : syracuseStep 3257333 = 305375) B305375
theorem B570361 : Blo 223812 570361 := bstep (se 2 (by rfl) ⟨213885, by rfl⟩ : syracuseStep 570361 = 427771) B427771
theorem B341351 : Blo 223812 341351 := bstep (se 1 (by rfl) ⟨256013, by rfl⟩ : syracuseStep 341351 = 512027) B512027
theorem B505511 : Blo 223812 505511 := bstep (se 1 (by rfl) ⟨379133, by rfl⟩ : syracuseStep 505511 = 758267) B758267
theorem B3749771 : Blo 223812 3749771 := bstep (se 1 (by rfl) ⟨2812328, by rfl⟩ : syracuseStep 3749771 = 5624657) B5624657
theorem B1914799 : Blo 223812 1914799 := bstep (se 1 (by rfl) ⟨1436099, by rfl⟩ : syracuseStep 1914799 = 2872199) B2872199
theorem B767933 : Blo 223812 767933 := bstep (se 3 (by rfl) ⟨143987, by rfl⟩ : syracuseStep 767933 = 287975) B287975
theorem B505835 : Blo 223812 505835 := bstep (se 1 (by rfl) ⟨379376, by rfl⟩ : syracuseStep 505835 = 758753) B758753
theorem B2898017 : Blo 223812 2898017 := bstep (se 2 (by rfl) ⟨1086756, by rfl⟩ : syracuseStep 2898017 = 2173513) B2173513
theorem B571495 : Blo 223812 571495 := bstep (se 1 (by rfl) ⟨428621, by rfl⟩ : syracuseStep 571495 = 857243) B857243
theorem B1620157 : Blo 223812 1620157 := bstep (se 3 (by rfl) ⟨303779, by rfl⟩ : syracuseStep 1620157 = 607559) B607559
theorem B1457135 : Blo 223812 1457135 := bstep (se 1 (by rfl) ⟨1092851, by rfl⟩ : syracuseStep 1457135 = 2185703) B2185703
theorem B507887 : Blo 223812 507887 := bstep (se 1 (by rfl) ⟨380915, by rfl⟩ : syracuseStep 507887 = 761831) B761831
theorem B966791 : Blo 223812 966791 := bstep (se 1 (by rfl) ⟨725093, by rfl⟩ : syracuseStep 966791 = 1450187) B1450187
theorem B541351 : Blo 223812 541351 := bstep (se 1 (by rfl) ⟨406013, by rfl⟩ : syracuseStep 541351 = 812027) B812027
theorem B508895 : Blo 223812 508895 := bstep (se 1 (by rfl) ⟨381671, by rfl⟩ : syracuseStep 508895 = 763343) B763343
theorem B509111 : Blo 223812 509111 := bstep (se 1 (by rfl) ⟨381833, by rfl⟩ : syracuseStep 509111 = 763667) B763667
theorem B378121 : Blo 223812 378121 := bstep (se 2 (by rfl) ⟨141795, by rfl⟩ : syracuseStep 378121 = 283591) B283591
theorem B3065363 : Blo 223812 3065363 := bstep (se 1 (by rfl) ⟨2299022, by rfl⟩ : syracuseStep 3065363 = 4598045) B4598045
theorem B510443 : Blo 223812 510443 := bstep (se 1 (by rfl) ⟨382832, by rfl⟩ : syracuseStep 510443 = 765665) B765665
theorem B1624657 : Blo 223812 1624657 := bstep (se 2 (by rfl) ⟨609246, by rfl⟩ : syracuseStep 1624657 = 1218493) B1218493
theorem B511145 : Blo 223812 511145 := bstep (se 2 (by rfl) ⟨191679, by rfl⟩ : syracuseStep 511145 = 383359) B383359
theorem B380639 : Blo 223812 380639 := bstep (se 1 (by rfl) ⟨285479, by rfl⟩ : syracuseStep 380639 = 570959) B570959
theorem B511721 : Blo 223812 511721 := bstep (se 2 (by rfl) ⟨191895, by rfl⟩ : syracuseStep 511721 = 383791) B383791
theorem B1134323 : Blo 223812 1134323 := bstep (se 1 (by rfl) ⟨850742, by rfl⟩ : syracuseStep 1134323 = 1701485) B1701485
theorem B381071 : Blo 223812 381071 := bstep (se 1 (by rfl) ⟨285803, by rfl⟩ : syracuseStep 381071 = 571607) B571607
theorem B1134971 : Blo 223812 1134971 := bstep (se 1 (by rfl) ⟨851228, by rfl⟩ : syracuseStep 1134971 = 1702457) B1702457
theorem B643639 : Blo 223812 643639 := bstep (se 1 (by rfl) ⟨482729, by rfl⟩ : syracuseStep 643639 = 965459) B965459
theorem B382495 : Blo 223812 382495 := bstep (se 1 (by rfl) ⟨286871, by rfl⟩ : syracuseStep 382495 = 573743) B573743
theorem B383467 : Blo 223812 383467 := bstep (se 1 (by rfl) ⟨287600, by rfl⟩ : syracuseStep 383467 = 575201) B575201
theorem B252571 : Blo 223812 252571 := bstep (se 1 (by rfl) ⟨189428, by rfl⟩ : syracuseStep 252571 = 378857) B378857
theorem B1628923 : Blo 223812 1628923 := bstep (se 1 (by rfl) ⟨1221692, by rfl⟩ : syracuseStep 1628923 = 2443385) B2443385
theorem B252895 : Blo 223812 252895 := bstep (se 1 (by rfl) ⟨189671, by rfl⟩ : syracuseStep 252895 = 379343) B379343
theorem B3235241 : Blo 223812 3235241 := bstep (se 2 (by rfl) ⟨1213215, by rfl⟩ : syracuseStep 3235241 = 2426431) B2426431
theorem B253543 : Blo 223812 253543 := bstep (se 1 (by rfl) ⟨190157, by rfl⟩ : syracuseStep 253543 = 380315) B380315
theorem B876271 : Blo 223812 876271 := bstep (se 1 (by rfl) ⟨657203, by rfl⟩ : syracuseStep 876271 = 1314407) B1314407
theorem B647687 : Blo 223812 647687 := bstep (se 1 (by rfl) ⟨485765, by rfl⟩ : syracuseStep 647687 = 971531) B971531
theorem B5890697 : Blo 223812 5890697 := bstep (se 2 (by rfl) ⟨2209011, by rfl⟩ : syracuseStep 5890697 = 4418023) B4418023
theorem B4121765 : Blo 223812 4121765 := bstep (se 4 (by rfl) ⟨386415, by rfl⟩ : syracuseStep 4121765 = 772831) B772831
theorem B4908221 : Blo 223812 4908221 := bstep (se 3 (by rfl) ⟨920291, by rfl⟩ : syracuseStep 4908221 = 1840583) B1840583
theorem B3663467 : Blo 223812 3663467 := bstep (se 1 (by rfl) ⟨2747600, by rfl⟩ : syracuseStep 3663467 = 5495201) B5495201
theorem B2156291 : Blo 223812 2156291 := bstep (se 1 (by rfl) ⟨1617218, by rfl⟩ : syracuseStep 2156291 = 3234437) B3234437
theorem B2910167 : Blo 223812 2910167 := bstep (se 1 (by rfl) ⟨2182625, by rfl⟩ : syracuseStep 2910167 = 4365251) B4365251
theorem B1829303 : Blo 223812 1829303 := bstep (se 1 (by rfl) ⟨1371977, by rfl⟩ : syracuseStep 1829303 = 2743955) B2743955
theorem B223911 : Blo 223812 223911 := bstep (se 1 (by rfl) ⟨167933, by rfl⟩ : syracuseStep 223911 = 335867) B335867
theorem B223951 : Blo 223812 223951 := bstep (se 1 (by rfl) ⟨167963, by rfl⟩ : syracuseStep 223951 = 335927) B335927
theorem B224031 : Blo 223812 224031 := bstep (se 1 (by rfl) ⟨168023, by rfl⟩ : syracuseStep 224031 = 336047) B336047
theorem B224167 : Blo 223812 224167 := bstep (se 1 (by rfl) ⟨168125, by rfl⟩ : syracuseStep 224167 = 336251) B336251
theorem B107342779 : Blo 223812 107342779 := bstep (se 1 (by rfl) ⟨80507084, by rfl⟩ : syracuseStep 107342779 = 161014169) B161014169
theorem B224283 : Blo 223812 224283 := bstep (se 1 (by rfl) ⟨168212, by rfl⟩ : syracuseStep 224283 = 336425) B336425
theorem B224347 : Blo 223812 224347 := bstep (se 1 (by rfl) ⟨168260, by rfl⟩ : syracuseStep 224347 = 336521) B336521
theorem B1076399 : Blo 223812 1076399 := bstep (se 1 (by rfl) ⟨807299, by rfl⟩ : syracuseStep 1076399 = 1614599) B1614599
theorem B224487 : Blo 223812 224487 := bstep (se 1 (by rfl) ⟨168365, by rfl⟩ : syracuseStep 224487 = 336731) B336731
theorem B224511 : Blo 223812 224511 := bstep (se 1 (by rfl) ⟨168383, by rfl⟩ : syracuseStep 224511 = 336767) B336767
theorem B224559 : Blo 223812 224559 := bstep (se 1 (by rfl) ⟨168419, by rfl⟩ : syracuseStep 224559 = 336839) B336839
theorem B10415465 : Blo 223812 10415465 := bstep (se 2 (by rfl) ⟨3905799, by rfl⟩ : syracuseStep 10415465 = 7811599) B7811599
theorem B224703 : Blo 223812 224703 := bstep (se 1 (by rfl) ⟨168527, by rfl⟩ : syracuseStep 224703 = 337055) B337055
theorem B650735 : Blo 223812 650735 := bstep (se 1 (by rfl) ⟨488051, by rfl⟩ : syracuseStep 650735 = 976103) B976103
theorem B224799 : Blo 223812 224799 := bstep (se 1 (by rfl) ⟨168599, by rfl⟩ : syracuseStep 224799 = 337199) B337199
theorem B224927 : Blo 223812 224927 := bstep (se 1 (by rfl) ⟨168695, by rfl⟩ : syracuseStep 224927 = 337391) B337391
theorem B224935 : Blo 223812 224935 := bstep (se 1 (by rfl) ⟨168701, by rfl⟩ : syracuseStep 224935 = 337403) B337403
theorem B224959 : Blo 223812 224959 := bstep (se 1 (by rfl) ⟨168719, by rfl⟩ : syracuseStep 224959 = 337439) B337439
theorem B225055 : Blo 223812 225055 := bstep (se 1 (by rfl) ⟨168791, by rfl⟩ : syracuseStep 225055 = 337583) B337583
theorem B225115 : Blo 223812 225115 := bstep (se 1 (by rfl) ⟨168836, by rfl⟩ : syracuseStep 225115 = 337673) B337673
theorem B225135 : Blo 223812 225135 := bstep (se 1 (by rfl) ⟨168851, by rfl⟩ : syracuseStep 225135 = 337703) B337703
theorem B1142909 : Blo 223812 1142909 := bstep (se 3 (by rfl) ⟨214295, by rfl⟩ : syracuseStep 1142909 = 428591) B428591
theorem B225535 : Blo 223812 225535 := bstep (se 1 (by rfl) ⟨169151, by rfl⟩ : syracuseStep 225535 = 338303) B338303
theorem B1143071 : Blo 223812 1143071 := bstep (se 1 (by rfl) ⟨857303, by rfl⟩ : syracuseStep 1143071 = 1714607) B1714607
theorem B225695 : Blo 223812 225695 := bstep (se 1 (by rfl) ⟨169271, by rfl⟩ : syracuseStep 225695 = 338543) B338543
theorem B225839 : Blo 223812 225839 := bstep (se 1 (by rfl) ⟨169379, by rfl⟩ : syracuseStep 225839 = 338759) B338759
theorem B324263 : Blo 223812 324263 := bstep (se 1 (by rfl) ⟨243197, by rfl⟩ : syracuseStep 324263 = 486395) B486395
theorem B226239 : Blo 223812 226239 := bstep (se 1 (by rfl) ⟨169679, by rfl⟩ : syracuseStep 226239 = 339359) B339359
theorem B2749393 : Blo 223812 2749393 := bstep (se 2 (by rfl) ⟨1031022, by rfl⟩ : syracuseStep 2749393 = 2062045) B2062045
theorem B226415 : Blo 223812 226415 := bstep (se 1 (by rfl) ⟨169811, by rfl⟩ : syracuseStep 226415 = 339623) B339623
theorem B226431 : Blo 223812 226431 := bstep (se 1 (by rfl) ⟨169823, by rfl⟩ : syracuseStep 226431 = 339647) B339647
theorem B1700999 : Blo 223812 1700999 := bstep (se 1 (by rfl) ⟨1275749, by rfl⟩ : syracuseStep 1700999 = 2551499) B2551499
theorem B226495 : Blo 223812 226495 := bstep (se 1 (by rfl) ⟨169871, by rfl⟩ : syracuseStep 226495 = 339743) B339743
theorem B226687 : Blo 223812 226687 := bstep (se 1 (by rfl) ⟨170015, by rfl⟩ : syracuseStep 226687 = 340031) B340031
theorem B226815 : Blo 223812 226815 := bstep (se 1 (by rfl) ⟨170111, by rfl⟩ : syracuseStep 226815 = 340223) B340223
theorem B226843 : Blo 223812 226843 := bstep (se 1 (by rfl) ⟨170132, by rfl⟩ : syracuseStep 226843 = 340265) B340265
theorem B227023 : Blo 223812 227023 := bstep (se 1 (by rfl) ⟨170267, by rfl⟩ : syracuseStep 227023 = 340535) B340535
theorem B227183 : Blo 223812 227183 := bstep (se 1 (by rfl) ⟨170387, by rfl⟩ : syracuseStep 227183 = 340775) B340775
theorem B227263 : Blo 223812 227263 := bstep (se 1 (by rfl) ⟨170447, by rfl⟩ : syracuseStep 227263 = 340895) B340895
theorem B358651 : Blo 223812 358651 := bstep (se 1 (by rfl) ⟨268988, by rfl⟩ : syracuseStep 358651 = 537977) B537977
theorem B227579 : Blo 223812 227579 := bstep (se 1 (by rfl) ⟨170684, by rfl⟩ : syracuseStep 227579 = 341369) B341369
theorem B227583 : Blo 223812 227583 := bstep (se 1 (by rfl) ⟨170687, by rfl⟩ : syracuseStep 227583 = 341375) B341375
theorem B15694117 : Blo 223812 15694117 := bstep (se 4 (by rfl) ⟨1471323, by rfl⟩ : syracuseStep 15694117 = 2942647) B2942647
theorem B227687 : Blo 223812 227687 := bstep (se 1 (by rfl) ⟨170765, by rfl⟩ : syracuseStep 227687 = 341531) B341531
theorem B817577 : Blo 223812 817577 := bstep (se 2 (by rfl) ⟨306591, by rfl⟩ : syracuseStep 817577 = 613183) B613183
theorem B227807 : Blo 223812 227807 := bstep (se 1 (by rfl) ⟨170855, by rfl⟩ : syracuseStep 227807 = 341711) B341711
theorem B850439 : Blo 223812 850439 := bstep (se 1 (by rfl) ⟨637829, by rfl⟩ : syracuseStep 850439 = 1275659) B1275659
theorem B424939 : Blo 223812 424939 := bstep (se 1 (by rfl) ⟨318704, by rfl⟩ : syracuseStep 424939 = 637409) B637409
theorem B2621783 : Blo 223812 2621783 := bstep (se 1 (by rfl) ⟨1966337, by rfl⟩ : syracuseStep 2621783 = 3932675) B3932675
theorem B721801 : Blo 223812 721801 := bstep (se 2 (by rfl) ⟨270675, by rfl⟩ : syracuseStep 721801 = 541351) B541351
theorem B1148093 : Blo 223812 1148093 := bstep (se 3 (by rfl) ⟨215267, by rfl⟩ : syracuseStep 1148093 = 430535) B430535
theorem B1837019 : Blo 223812 1837019 := bstep (se 1 (by rfl) ⟨1377764, by rfl⟩ : syracuseStep 1837019 = 2755529) B2755529
theorem B854327 : Blo 223812 854327 := bstep (se 1 (by rfl) ⟨640745, by rfl⟩ : syracuseStep 854327 = 1281491) B1281491
theorem B756215 : Blo 223812 756215 := bstep (se 1 (by rfl) ⟨567161, by rfl⟩ : syracuseStep 756215 = 1134323) B1134323
theorem B756377 : Blo 223812 756377 := bstep (se 2 (by rfl) ⟨283641, by rfl⟩ : syracuseStep 756377 = 567283) B567283
theorem B920423 : Blo 223812 920423 := bstep (se 1 (by rfl) ⟨690317, by rfl⟩ : syracuseStep 920423 = 1380635) B1380635
theorem B756647 : Blo 223812 756647 := bstep (se 1 (by rfl) ⟨567485, by rfl⟩ : syracuseStep 756647 = 1134971) B1134971
theorem B920585 : Blo 223812 920585 := bstep (se 2 (by rfl) ⟨345219, by rfl⟩ : syracuseStep 920585 = 690439) B690439
theorem B2166209 : Blo 223812 2166209 := bstep (se 2 (by rfl) ⟨812328, by rfl⟩ : syracuseStep 2166209 = 1624657) B1624657
theorem B757673 : Blo 223812 757673 := bstep (se 2 (by rfl) ⟨284127, by rfl⟩ : syracuseStep 757673 = 568255) B568255
theorem B725287 : Blo 223812 725287 := bstep (se 1 (by rfl) ⟨543965, by rfl⟩ : syracuseStep 725287 = 1087931) B1087931
theorem B9999389 : Blo 223812 9999389 := bstep (se 3 (by rfl) ⟨1874885, by rfl⟩ : syracuseStep 9999389 = 3749771) B3749771
theorem B923017 : Blo 223812 923017 := bstep (se 2 (by rfl) ⟨346131, by rfl⟩ : syracuseStep 923017 = 692263) B692263
theorem B858185 : Blo 223812 858185 := bstep (se 2 (by rfl) ⟨321819, by rfl⟩ : syracuseStep 858185 = 643639) B643639
theorem B1940111 : Blo 223812 1940111 := bstep (se 1 (by rfl) ⟨1455083, by rfl⟩ : syracuseStep 1940111 = 2910167) B2910167
theorem B760481 : Blo 223812 760481 := bstep (se 2 (by rfl) ⟨285180, by rfl⟩ : syracuseStep 760481 = 570361) B570361
theorem B1383263 : Blo 223812 1383263 := bstep (se 1 (by rfl) ⟨1037447, by rfl⟩ : syracuseStep 1383263 = 2074895) B2074895
theorem B1219535 : Blo 223812 1219535 := bstep (se 1 (by rfl) ⟨914651, by rfl⟩ : syracuseStep 1219535 = 1829303) B1829303
theorem B728477 : Blo 223812 728477 := bstep (se 3 (by rfl) ⟨136589, by rfl⟩ : syracuseStep 728477 = 273179) B273179
theorem B761939 : Blo 223812 761939 := bstep (se 1 (by rfl) ⟨571454, by rfl⟩ : syracuseStep 761939 = 1142909) B1142909
theorem B761993 : Blo 223812 761993 := bstep (se 2 (by rfl) ⟨285747, by rfl⟩ : syracuseStep 761993 = 571495) B571495
theorem B762047 : Blo 223812 762047 := bstep (se 1 (by rfl) ⟨571535, by rfl⟩ : syracuseStep 762047 = 1143071) B1143071
theorem B336155 : Blo 223812 336155 := bstep (se 1 (by rfl) ⟨252116, by rfl⟩ : syracuseStep 336155 = 504233) B504233
theorem B336191 : Blo 223812 336191 := bstep (se 1 (by rfl) ⟨252143, by rfl⟩ : syracuseStep 336191 = 504287) B504287
theorem B336359 : Blo 223812 336359 := bstep (se 1 (by rfl) ⟨252269, by rfl⟩ : syracuseStep 336359 = 504539) B504539
theorem B2171555 : Blo 223812 2171555 := bstep (se 1 (by rfl) ⟨1628666, by rfl⟩ : syracuseStep 2171555 = 3257333) B3257333
theorem B10953589 : Blo 223812 10953589 := bstep (se 5 (by rfl) ⟨513449, by rfl⟩ : syracuseStep 10953589 = 1026899) B1026899
theorem B336761 : Blo 223812 336761 := bstep (se 2 (by rfl) ⟨126285, by rfl⟩ : syracuseStep 336761 = 252571) B252571
theorem B2171897 : Blo 223812 2171897 := bstep (se 2 (by rfl) ⟨814461, by rfl⟩ : syracuseStep 2171897 = 1628923) B1628923
theorem B337007 : Blo 223812 337007 := bstep (se 1 (by rfl) ⟨252755, by rfl⟩ : syracuseStep 337007 = 505511) B505511
theorem B1844477 : Blo 223812 1844477 := bstep (se 3 (by rfl) ⟨345839, by rfl⟩ : syracuseStep 1844477 = 691679) B691679
theorem B337193 : Blo 223812 337193 := bstep (se 2 (by rfl) ⟨126447, by rfl⟩ : syracuseStep 337193 = 252895) B252895
theorem B566585 : Blo 223812 566585 := bstep (se 2 (by rfl) ⟨212469, by rfl⟩ : syracuseStep 566585 = 424939) B424939
theorem B337223 : Blo 223812 337223 := bstep (se 1 (by rfl) ⟨252917, by rfl⟩ : syracuseStep 337223 = 505835) B505835
theorem B566959 : Blo 223812 566959 := bstep (se 1 (by rfl) ⟨425219, by rfl⟩ : syracuseStep 566959 = 850439) B850439
theorem B338057 : Blo 223812 338057 := bstep (se 2 (by rfl) ⟨126771, by rfl⟩ : syracuseStep 338057 = 253543) B253543
theorem B338591 : Blo 223812 338591 := bstep (se 1 (by rfl) ⟨253943, by rfl⟩ : syracuseStep 338591 = 507887) B507887
theorem B568043 : Blo 223812 568043 := bstep (se 1 (by rfl) ⟨426032, by rfl⟩ : syracuseStep 568043 = 852065) B852065
theorem B1944485 : Blo 223812 1944485 := bstep (se 4 (by rfl) ⟨182295, by rfl⟩ : syracuseStep 1944485 = 364591) B364591
theorem B339263 : Blo 223812 339263 := bstep (se 1 (by rfl) ⟨254447, by rfl⟩ : syracuseStep 339263 = 508895) B508895
theorem B339407 : Blo 223812 339407 := bstep (se 1 (by rfl) ⟨254555, by rfl⟩ : syracuseStep 339407 = 509111) B509111
theorem B568903 : Blo 223812 568903 := bstep (se 1 (by rfl) ⟨426677, by rfl⟩ : syracuseStep 568903 = 853355) B853355
theorem B2043575 : Blo 223812 2043575 := bstep (se 1 (by rfl) ⟨1532681, by rfl⟩ : syracuseStep 2043575 = 3065363) B3065363
theorem B503711 : Blo 223812 503711 := bstep (se 1 (by rfl) ⟨377783, by rfl⟩ : syracuseStep 503711 = 755567) B755567
theorem B1912805 : Blo 223812 1912805 := bstep (se 4 (by rfl) ⟨179325, by rfl⟩ : syracuseStep 1912805 = 358651) B358651
theorem B765935 : Blo 223812 765935 := bstep (se 1 (by rfl) ⟨574451, by rfl⟩ : syracuseStep 765935 = 1148903) B1148903
theorem B569339 : Blo 223812 569339 := bstep (se 1 (by rfl) ⟨427004, by rfl⟩ : syracuseStep 569339 = 854009) B854009
theorem B232697939 : Blo 223812 232697939 := bstep (se 1 (by rfl) ⟨174523454, by rfl⟩ : syracuseStep 232697939 = 349046909) B349046909
theorem B83701957 : Blo 223812 83701957 := bstep (se 4 (by rfl) ⟨7847058, by rfl⟩ : syracuseStep 83701957 = 15694117) B15694117
theorem B340295 : Blo 223812 340295 := bstep (se 1 (by rfl) ⟨255221, by rfl⟩ : syracuseStep 340295 = 510443) B510443
theorem B504161 : Blo 223812 504161 := bstep (se 2 (by rfl) ⟨189060, by rfl⟩ : syracuseStep 504161 = 378121) B378121
theorem B864701 : Blo 223812 864701 := bstep (se 3 (by rfl) ⟨162131, by rfl⟩ : syracuseStep 864701 = 324263) B324263
theorem B1225199 : Blo 223812 1225199 := bstep (se 1 (by rfl) ⟨918899, by rfl⟩ : syracuseStep 1225199 = 1837799) B1837799
theorem B5747435 : Blo 223812 5747435 := bstep (se 1 (by rfl) ⟨4310576, by rfl⟩ : syracuseStep 5747435 = 8621153) B8621153
theorem B340763 : Blo 223812 340763 := bstep (se 1 (by rfl) ⟨255572, by rfl⟩ : syracuseStep 340763 = 511145) B511145
theorem B2896681 : Blo 223812 2896681 := bstep (se 2 (by rfl) ⟨1086255, by rfl⟩ : syracuseStep 2896681 = 2172511) B2172511
theorem B1750079 : Blo 223812 1750079 := bstep (se 1 (by rfl) ⟨1312559, by rfl⟩ : syracuseStep 1750079 = 2625119) B2625119
theorem B341147 : Blo 223812 341147 := bstep (se 1 (by rfl) ⟨255860, by rfl⟩ : syracuseStep 341147 = 511721) B511721
theorem B570665 : Blo 223812 570665 := bstep (se 2 (by rfl) ⟨213999, by rfl⟩ : syracuseStep 570665 = 427999) B427999
theorem B767987 : Blo 223812 767987 := bstep (se 1 (by rfl) ⟨575990, by rfl⟩ : syracuseStep 767987 = 1151981) B1151981
theorem B506735 : Blo 223812 506735 := bstep (se 1 (by rfl) ⟨380051, by rfl⟩ : syracuseStep 506735 = 760103) B760103
theorem B573095 : Blo 223812 573095 := bstep (se 1 (by rfl) ⟨429821, by rfl⟩ : syracuseStep 573095 = 859643) B859643
theorem B638695 : Blo 223812 638695 := bstep (se 1 (by rfl) ⟨479021, by rfl⟩ : syracuseStep 638695 = 958043) B958043
theorem B639083 : Blo 223812 639083 := bstep (se 1 (by rfl) ⟨479312, by rfl⟩ : syracuseStep 639083 = 958625) B958625
theorem B508319 : Blo 223812 508319 := bstep (se 1 (by rfl) ⟨381239, by rfl⟩ : syracuseStep 508319 = 762479) B762479
theorem B2442311 : Blo 223812 2442311 := bstep (se 1 (by rfl) ⟨1831733, by rfl⟩ : syracuseStep 2442311 = 3663467) B3663467
theorem B509993 : Blo 223812 509993 := bstep (se 2 (by rfl) ⟨191247, by rfl⟩ : syracuseStep 509993 = 382495) B382495
theorem B1231037 : Blo 223812 1231037 := bstep (se 3 (by rfl) ⟨230819, by rfl⟩ : syracuseStep 1231037 = 461639) B461639
theorem B510823 : Blo 223812 510823 := bstep (se 1 (by rfl) ⟨383117, by rfl⟩ : syracuseStep 510823 = 766235) B766235
theorem B642239 : Blo 223812 642239 := bstep (se 1 (by rfl) ⟨481679, by rfl⟩ : syracuseStep 642239 = 963359) B963359
theorem B707791 : Blo 223812 707791 := bstep (se 1 (by rfl) ⟨530843, by rfl⟩ : syracuseStep 707791 = 1061687) B1061687
theorem B511289 : Blo 223812 511289 := bstep (se 2 (by rfl) ⟨191733, by rfl⟩ : syracuseStep 511289 = 383467) B383467
theorem B1133999 : Blo 223812 1133999 := bstep (se 1 (by rfl) ⟨850499, by rfl⟩ : syracuseStep 1133999 = 1700999) B1700999
theorem B511955 : Blo 223812 511955 := bstep (se 1 (by rfl) ⟨383966, by rfl⟩ : syracuseStep 511955 = 767933) B767933
theorem B10506341 : Blo 223812 10506341 := bstep (se 4 (by rfl) ⟨984969, by rfl⟩ : syracuseStep 10506341 = 1969939) B1969939
theorem B545051 : Blo 223812 545051 := bstep (se 1 (by rfl) ⟨408788, by rfl⟩ : syracuseStep 545051 = 817577) B817577
theorem B971423 : Blo 223812 971423 := bstep (se 1 (by rfl) ⟨728567, by rfl⟩ : syracuseStep 971423 = 1457135) B1457135
theorem B1168361 : Blo 223812 1168361 := bstep (se 2 (by rfl) ⟨438135, by rfl⟩ : syracuseStep 1168361 = 876271) B876271
theorem B644527 : Blo 223812 644527 := bstep (se 1 (by rfl) ⟨483395, by rfl⟩ : syracuseStep 644527 = 966791) B966791
theorem B19486169 : Blo 223812 19486169 := bstep (se 2 (by rfl) ⟨7307313, by rfl⟩ : syracuseStep 19486169 = 14614627) B14614627
theorem B2446843 : Blo 223812 2446843 := bstep (se 1 (by rfl) ⟨1835132, by rfl⟩ : syracuseStep 2446843 = 3670265) B3670265
theorem B1922615 : Blo 223812 1922615 := bstep (se 1 (by rfl) ⟨1441961, by rfl⟩ : syracuseStep 1922615 = 2883923) B2883923
theorem B1726271 : Blo 223812 1726271 := bstep (se 1 (by rfl) ⟨1294703, by rfl⟩ : syracuseStep 1726271 = 2589407) B2589407
theorem B612535 : Blo 223812 612535 := bstep (se 1 (by rfl) ⟨459401, by rfl⟩ : syracuseStep 612535 = 918803) B918803
theorem B3889457 : Blo 223812 3889457 := bstep (se 2 (by rfl) ⟨1458546, by rfl⟩ : syracuseStep 3889457 = 2917093) B2917093
theorem B1727165 : Blo 223812 1727165 := bstep (se 3 (by rfl) ⟨323843, by rfl⟩ : syracuseStep 1727165 = 647687) B647687
theorem B253759 : Blo 223812 253759 := bstep (se 1 (by rfl) ⟨190319, by rfl⟩ : syracuseStep 253759 = 380639) B380639
theorem B254047 : Blo 223812 254047 := bstep (se 1 (by rfl) ⟨190535, by rfl⟩ : syracuseStep 254047 = 381071) B381071
theorem B418127 : Blo 223812 418127 := bstep (se 1 (by rfl) ⟨313595, by rfl⟩ : syracuseStep 418127 = 627191) B627191
theorem B615367 : Blo 223812 615367 := bstep (se 1 (by rfl) ⟨461525, by rfl⟩ : syracuseStep 615367 = 923051) B923051
theorem B143123705 : Blo 223812 143123705 := bstep (se 2 (by rfl) ⟨53671389, by rfl⟩ : syracuseStep 143123705 = 107342779) B107342779
theorem B1139993 : Blo 223812 1139993 := bstep (se 2 (by rfl) ⟨427497, by rfl⟩ : syracuseStep 1139993 = 854995) B854995
theorem B2189119 : Blo 223812 2189119 := bstep (se 1 (by rfl) ⟨1641839, by rfl⟩ : syracuseStep 2189119 = 3283679) B3283679
theorem B616423 : Blo 223812 616423 := bstep (se 1 (by rfl) ⟨462317, by rfl⟩ : syracuseStep 616423 = 924635) B924635
theorem B2156827 : Blo 223812 2156827 := bstep (se 1 (by rfl) ⟨1617620, by rfl⟩ : syracuseStep 2156827 = 3235241) B3235241
theorem B6941173 : Blo 223812 6941173 := bstep (se 5 (by rfl) ⟨325367, by rfl⟩ : syracuseStep 6941173 = 650735) B650735
theorem B9726479 : Blo 223812 9726479 := bstep (se 1 (by rfl) ⟨7294859, by rfl⟩ : syracuseStep 9726479 = 14589719) B14589719
theorem B223855 : Blo 223812 223855 := bstep (se 1 (by rfl) ⟨167891, by rfl⟩ : syracuseStep 223855 = 335783) B335783
theorem B224027 : Blo 223812 224027 := bstep (se 1 (by rfl) ⟨168020, by rfl⟩ : syracuseStep 224027 = 336041) B336041
theorem B1141613 : Blo 223812 1141613 := bstep (se 3 (by rfl) ⟨214052, by rfl⟩ : syracuseStep 1141613 = 428105) B428105
theorem B3927131 : Blo 223812 3927131 := bstep (se 1 (by rfl) ⟨2945348, by rfl⟩ : syracuseStep 3927131 = 5890697) B5890697
theorem B224539 : Blo 223812 224539 := bstep (se 1 (by rfl) ⟨168404, by rfl⟩ : syracuseStep 224539 = 336809) B336809
theorem B2747843 : Blo 223812 2747843 := bstep (se 1 (by rfl) ⟨2060882, by rfl⟩ : syracuseStep 2747843 = 4121765) B4121765
theorem B224719 : Blo 223812 224719 := bstep (se 1 (by rfl) ⟨168539, by rfl⟩ : syracuseStep 224719 = 337079) B337079
theorem B3272147 : Blo 223812 3272147 := bstep (se 1 (by rfl) ⟨2454110, by rfl⟩ : syracuseStep 3272147 = 4908221) B4908221
theorem B224879 : Blo 223812 224879 := bstep (se 1 (by rfl) ⟨168659, by rfl⟩ : syracuseStep 224879 = 337319) B337319
theorem B224999 : Blo 223812 224999 := bstep (se 1 (by rfl) ⟨168749, by rfl⟩ : syracuseStep 224999 = 337499) B337499
theorem B1437527 : Blo 223812 1437527 := bstep (se 1 (by rfl) ⟨1078145, by rfl⟩ : syracuseStep 1437527 = 2156291) B2156291
theorem B225191 : Blo 223812 225191 := bstep (se 1 (by rfl) ⟨168893, by rfl⟩ : syracuseStep 225191 = 337787) B337787
theorem B3665857 : Blo 223812 3665857 := bstep (se 2 (by rfl) ⟨1374696, by rfl⟩ : syracuseStep 3665857 = 2749393) B2749393
theorem B225351 : Blo 223812 225351 := bstep (se 1 (by rfl) ⟨169013, by rfl⟩ : syracuseStep 225351 = 338027) B338027
theorem B225471 : Blo 223812 225471 := bstep (se 1 (by rfl) ⟨169103, by rfl⟩ : syracuseStep 225471 = 338207) B338207
theorem B225767 : Blo 223812 225767 := bstep (se 1 (by rfl) ⟨169325, by rfl⟩ : syracuseStep 225767 = 338651) B338651
theorem B225951 : Blo 223812 225951 := bstep (se 1 (by rfl) ⟨169463, by rfl⟩ : syracuseStep 225951 = 338927) B338927
theorem B225959 : Blo 223812 225959 := bstep (se 1 (by rfl) ⟨169469, by rfl⟩ : syracuseStep 225959 = 338939) B338939
theorem B225999 : Blo 223812 225999 := bstep (se 1 (by rfl) ⟨169499, by rfl⟩ : syracuseStep 225999 = 338999) B338999
theorem B717599 : Blo 223812 717599 := bstep (se 1 (by rfl) ⟨538199, by rfl⟩ : syracuseStep 717599 = 1076399) B1076399
theorem B226079 : Blo 223812 226079 := bstep (se 1 (by rfl) ⟨169559, by rfl⟩ : syracuseStep 226079 = 339119) B339119
theorem B226119 : Blo 223812 226119 := bstep (se 1 (by rfl) ⟨169589, by rfl⟩ : syracuseStep 226119 = 339179) B339179
theorem B6943643 : Blo 223812 6943643 := bstep (se 1 (by rfl) ⟨5207732, by rfl⟩ : syracuseStep 6943643 = 10415465) B10415465
theorem B226331 : Blo 223812 226331 := bstep (se 1 (by rfl) ⟨169748, by rfl⟩ : syracuseStep 226331 = 339497) B339497
theorem B4945049 : Blo 223812 4945049 := bstep (se 2 (by rfl) ⟨1854393, by rfl⟩ : syracuseStep 4945049 = 3708787) B3708787
theorem B2553065 : Blo 223812 2553065 := bstep (se 2 (by rfl) ⟨957399, by rfl⟩ : syracuseStep 2553065 = 1914799) B1914799
theorem B226559 : Blo 223812 226559 := bstep (se 1 (by rfl) ⟨169919, by rfl⟩ : syracuseStep 226559 = 339839) B339839
theorem B1275385 : Blo 223812 1275385 := bstep (se 2 (by rfl) ⟨478269, by rfl⟩ : syracuseStep 1275385 = 956539) B956539
theorem B2160209 : Blo 223812 2160209 := bstep (se 2 (by rfl) ⟨810078, by rfl⟩ : syracuseStep 2160209 = 1620157) B1620157
theorem B227567 : Blo 223812 227567 := bstep (se 1 (by rfl) ⟨170675, by rfl⟩ : syracuseStep 227567 = 341351) B341351
theorem B1932011 : Blo 223812 1932011 := bstep (se 1 (by rfl) ⟨1449008, by rfl⟩ : syracuseStep 1932011 = 2898017) B2898017
theorem B426055 : Blo 223812 426055 := bstep (se 1 (by rfl) ⟨319541, by rfl⟩ : syracuseStep 426055 = 639083) B639083
theorem B620527837 : Blo 223812 620527837 := bstep (se 3 (by rfl) ⟨116348969, by rfl⟩ : syracuseStep 620527837 = 232697939) B232697939
theorem B1115005 : Blo 223812 1115005 := bstep (se 3 (by rfl) ⟨209063, by rfl⟩ : syracuseStep 1115005 = 418127) B418127
theorem B820691 : Blo 223812 820691 := bstep (se 1 (by rfl) ⟨615518, by rfl⟩ : syracuseStep 820691 = 1231037) B1231037
theorem B428159 : Blo 223812 428159 := bstep (se 1 (by rfl) ⟨321119, by rfl⟩ : syracuseStep 428159 = 642239) B642239
theorem B755945 : Blo 223812 755945 := bstep (se 2 (by rfl) ⟨283479, by rfl⟩ : syracuseStep 755945 = 566959) B566959
theorem B755999 : Blo 223812 755999 := bstep (se 1 (by rfl) ⟨566999, by rfl⟩ : syracuseStep 755999 = 1133999) B1133999
theorem B1444139 : Blo 223812 1444139 := bstep (se 1 (by rfl) ⟨1083104, by rfl⟩ : syracuseStep 1444139 = 2166209) B2166209
theorem B2918825 : Blo 223812 2918825 := bstep (se 2 (by rfl) ⟨1094559, by rfl⟩ : syracuseStep 2918825 = 2189119) B2189119
theorem B821897 : Blo 223812 821897 := bstep (se 2 (by rfl) ⟨308211, by rfl⟩ : syracuseStep 821897 = 616423) B616423
theorem B363367 : Blo 223812 363367 := bstep (se 1 (by rfl) ⟨272525, by rfl⟩ : syracuseStep 363367 = 545051) B545051
theorem B1281743 : Blo 223812 1281743 := bstep (se 1 (by rfl) ⟨961307, by rfl⟩ : syracuseStep 1281743 = 1922615) B1922615
theorem B1150847 : Blo 223812 1150847 := bstep (se 1 (by rfl) ⟨863135, by rfl⟩ : syracuseStep 1150847 = 1726271) B1726271
theorem B2592971 : Blo 223812 2592971 := bstep (se 1 (by rfl) ⟨1944728, by rfl⟩ : syracuseStep 2592971 = 3889457) B3889457
theorem B1151443 : Blo 223812 1151443 := bstep (se 1 (by rfl) ⟨863582, by rfl⟩ : syracuseStep 1151443 = 1727165) B1727165
theorem B922175 : Blo 223812 922175 := bstep (se 1 (by rfl) ⟨691631, by rfl⟩ : syracuseStep 922175 = 1383263) B1383263
theorem B758537 : Blo 223812 758537 := bstep (se 2 (by rfl) ⟨284451, by rfl⟩ : syracuseStep 758537 = 568903) B568903
theorem B3281957 : Blo 223812 3281957 := bstep (se 4 (by rfl) ⟨307683, by rfl⟩ : syracuseStep 3281957 = 615367) B615367
theorem B4887809 : Blo 223812 4887809 := bstep (se 2 (by rfl) ⟨1832928, by rfl⟩ : syracuseStep 4887809 = 3665857) B3665857
theorem B1447703 : Blo 223812 1447703 := bstep (se 1 (by rfl) ⟨1085777, by rfl⟩ : syracuseStep 1447703 = 2171555) B2171555
theorem B1447931 : Blo 223812 1447931 := bstep (se 1 (by rfl) ⟨1085948, by rfl⟩ : syracuseStep 1447931 = 2171897) B2171897
theorem B759995 : Blo 223812 759995 := bstep (se 1 (by rfl) ⟨569996, by rfl⟩ : syracuseStep 759995 = 1139993) B1139993
theorem B859369 : Blo 223812 859369 := bstep (se 2 (by rfl) ⟨322263, by rfl⟩ : syracuseStep 859369 = 644527) B644527
theorem B761075 : Blo 223812 761075 := bstep (se 1 (by rfl) ⟨570806, by rfl⟩ : syracuseStep 761075 = 1141613) B1141613
theorem B958351 : Blo 223812 958351 := bstep (se 1 (by rfl) ⟨718763, by rfl⟩ : syracuseStep 958351 = 1437527) B1437527
theorem B335807 : Blo 223812 335807 := bstep (se 1 (by rfl) ⟨251855, by rfl⟩ : syracuseStep 335807 = 503711) B503711
theorem B336107 : Blo 223812 336107 := bstep (se 1 (by rfl) ⟨252080, by rfl⟩ : syracuseStep 336107 = 504161) B504161
theorem B4629095 : Blo 223812 4629095 := bstep (se 1 (by rfl) ⟨3471821, by rfl⟩ : syracuseStep 4629095 = 6943643) B6943643
theorem B1288007 : Blo 223812 1288007 := bstep (se 1 (by rfl) ⟨966005, by rfl⟩ : syracuseStep 1288007 = 1932011) B1932011
theorem B337823 : Blo 223812 337823 := bstep (se 1 (by rfl) ⟨253367, by rfl⟩ : syracuseStep 337823 = 506735) B506735
theorem B338345 : Blo 223812 338345 := bstep (se 2 (by rfl) ⟨126879, by rfl⟩ : syracuseStep 338345 = 253759) B253759
theorem B338729 : Blo 223812 338729 := bstep (se 2 (by rfl) ⟨127023, by rfl⟩ : syracuseStep 338729 = 254047) B254047
theorem B1747855 : Blo 223812 1747855 := bstep (se 1 (by rfl) ⟨1310891, by rfl⟩ : syracuseStep 1747855 = 2621783) B2621783
theorem B338879 : Blo 223812 338879 := bstep (se 1 (by rfl) ⟨254159, by rfl⟩ : syracuseStep 338879 = 508319) B508319
theorem B765395 : Blo 223812 765395 := bstep (se 1 (by rfl) ⟨574046, by rfl⟩ : syracuseStep 765395 = 1148093) B1148093
theorem B962401 : Blo 223812 962401 := bstep (se 2 (by rfl) ⟨360900, by rfl⟩ : syracuseStep 962401 = 721801) B721801
theorem B1224679 : Blo 223812 1224679 := bstep (se 1 (by rfl) ⟨918509, by rfl⟩ : syracuseStep 1224679 = 1837019) B1837019
theorem B339995 : Blo 223812 339995 := bstep (se 1 (by rfl) ⟨254996, by rfl⟩ : syracuseStep 339995 = 509993) B509993
theorem B569551 : Blo 223812 569551 := bstep (se 1 (by rfl) ⟨427163, by rfl⟩ : syracuseStep 569551 = 854327) B854327
theorem B504143 : Blo 223812 504143 := bstep (se 1 (by rfl) ⟨378107, by rfl⟩ : syracuseStep 504143 = 756215) B756215
theorem B504251 : Blo 223812 504251 := bstep (se 1 (by rfl) ⟨378188, by rfl⟩ : syracuseStep 504251 = 756377) B756377
theorem B504431 : Blo 223812 504431 := bstep (se 1 (by rfl) ⟨378323, by rfl⟩ : syracuseStep 504431 = 756647) B756647
theorem B340859 : Blo 223812 340859 := bstep (se 1 (by rfl) ⟨255644, by rfl⟩ : syracuseStep 340859 = 511289) B511289
theorem B505115 : Blo 223812 505115 := bstep (se 1 (by rfl) ⟨378836, by rfl⟩ : syracuseStep 505115 = 757673) B757673
theorem B341303 : Blo 223812 341303 := bstep (se 1 (by rfl) ⟨255977, by rfl⟩ : syracuseStep 341303 = 511955) B511955
theorem B9254897 : Blo 223812 9254897 := bstep (se 2 (by rfl) ⟨3470586, by rfl⟩ : syracuseStep 9254897 = 6941173) B6941173
theorem B6666259 : Blo 223812 6666259 := bstep (se 1 (by rfl) ⟨4999694, by rfl⟩ : syracuseStep 6666259 = 9999389) B9999389
theorem B12990779 : Blo 223812 12990779 := bstep (se 1 (by rfl) ⟨9743084, by rfl⟩ : syracuseStep 12990779 = 19486169) B19486169
theorem B572123 : Blo 223812 572123 := bstep (se 1 (by rfl) ⟨429092, by rfl⟩ : syracuseStep 572123 = 858185) B858185
theorem B1293407 : Blo 223812 1293407 := bstep (se 1 (by rfl) ⟨970055, by rfl⟩ : syracuseStep 1293407 = 1940111) B1940111
theorem B506987 : Blo 223812 506987 := bstep (se 1 (by rfl) ⟨380240, by rfl⟩ : syracuseStep 506987 = 760481) B760481
theorem B507959 : Blo 223812 507959 := bstep (se 1 (by rfl) ⟨380969, by rfl⟩ : syracuseStep 507959 = 761939) B761939
theorem B507995 : Blo 223812 507995 := bstep (se 1 (by rfl) ⟨380996, by rfl⟩ : syracuseStep 507995 = 761993) B761993
theorem B508031 : Blo 223812 508031 := bstep (se 1 (by rfl) ⟨381023, by rfl⟩ : syracuseStep 508031 = 762047) B762047
theorem B967049 : Blo 223812 967049 := bstep (se 2 (by rfl) ⟨362643, by rfl⟩ : syracuseStep 967049 = 725287) B725287
theorem B1229651 : Blo 223812 1229651 := bstep (se 1 (by rfl) ⟨922238, by rfl⟩ : syracuseStep 1229651 = 1844477) B1844477
theorem B377723 : Blo 223812 377723 := bstep (se 1 (by rfl) ⟨283292, by rfl⟩ : syracuseStep 377723 = 566585) B566585
theorem B378695 : Blo 223812 378695 := bstep (se 1 (by rfl) ⟨284021, by rfl⟩ : syracuseStep 378695 = 568043) B568043
theorem B1230689 : Blo 223812 1230689 := bstep (se 2 (by rfl) ⟨461508, by rfl⟩ : syracuseStep 1230689 = 923017) B923017
theorem B1296323 : Blo 223812 1296323 := bstep (se 1 (by rfl) ⟨972242, by rfl⟩ : syracuseStep 1296323 = 1944485) B1944485
theorem B3262457 : Blo 223812 3262457 := bstep (se 2 (by rfl) ⟨1223421, by rfl⟩ : syracuseStep 3262457 = 2446843) B2446843
theorem B2181431 : Blo 223812 2181431 := bstep (se 1 (by rfl) ⟨1636073, by rfl⟩ : syracuseStep 2181431 = 3272147) B3272147
theorem B1362383 : Blo 223812 1362383 := bstep (se 1 (by rfl) ⟨1021787, by rfl⟩ : syracuseStep 1362383 = 2043575) B2043575
theorem B510623 : Blo 223812 510623 := bstep (se 1 (by rfl) ⟨382967, by rfl⟩ : syracuseStep 510623 = 765935) B765935
theorem B379559 : Blo 223812 379559 := bstep (se 1 (by rfl) ⟨284669, by rfl⟩ : syracuseStep 379559 = 569339) B569339
theorem B576467 : Blo 223812 576467 := bstep (se 1 (by rfl) ⟨432350, by rfl⟩ : syracuseStep 576467 = 864701) B864701
theorem B478399 : Blo 223812 478399 := bstep (se 1 (by rfl) ⟨358799, by rfl⟩ : syracuseStep 478399 = 717599) B717599
theorem B1166719 : Blo 223812 1166719 := bstep (se 1 (by rfl) ⟨875039, by rfl⟩ : syracuseStep 1166719 = 1750079) B1750079
theorem B3296699 : Blo 223812 3296699 := bstep (se 1 (by rfl) ⟨2472524, by rfl⟩ : syracuseStep 3296699 = 4945049) B4945049
theorem B380443 : Blo 223812 380443 := bstep (se 1 (by rfl) ⟨285332, by rfl⟩ : syracuseStep 380443 = 570665) B570665
theorem B511991 : Blo 223812 511991 := bstep (se 1 (by rfl) ⟨383993, by rfl⟩ : syracuseStep 511991 = 767987) B767987
theorem B382063 : Blo 223812 382063 := bstep (se 1 (by rfl) ⟨286547, by rfl⟩ : syracuseStep 382063 = 573095) B573095
theorem B1628207 : Blo 223812 1628207 := bstep (se 1 (by rfl) ⟨1221155, by rfl⟩ : syracuseStep 1628207 = 2442311) B2442311
theorem B14604785 : Blo 223812 14604785 := bstep (se 2 (by rfl) ⟨5476794, by rfl⟩ : syracuseStep 14604785 = 10953589) B10953589
theorem B613615 : Blo 223812 613615 := bstep (se 1 (by rfl) ⟨460211, by rfl⟩ : syracuseStep 613615 = 920423) B920423
theorem B7004227 : Blo 223812 7004227 := bstep (se 1 (by rfl) ⟨5253170, by rfl⟩ : syracuseStep 7004227 = 10506341) B10506341
theorem B2875769 : Blo 223812 2875769 := bstep (se 2 (by rfl) ⟨1078413, by rfl⟩ : syracuseStep 2875769 = 2156827) B2156827
theorem B647615 : Blo 223812 647615 := bstep (se 1 (by rfl) ⟨485711, by rfl⟩ : syracuseStep 647615 = 971423) B971423
theorem B778907 : Blo 223812 778907 := bstep (se 1 (by rfl) ⟨584180, by rfl⟩ : syracuseStep 778907 = 1168361) B1168361
theorem B681097 : Blo 223812 681097 := bstep (se 2 (by rfl) ⟨255411, by rfl⟩ : syracuseStep 681097 = 510823) B510823
theorem B5760557 : Blo 223812 5760557 := bstep (se 3 (by rfl) ⟨1080104, by rfl⟩ : syracuseStep 5760557 = 2160209) B2160209
theorem B943721 : Blo 223812 943721 := bstep (se 2 (by rfl) ⟨353895, by rfl⟩ : syracuseStep 943721 = 707791) B707791
theorem B813023 : Blo 223812 813023 := bstep (se 1 (by rfl) ⟨609767, by rfl⟩ : syracuseStep 813023 = 1219535) B1219535
theorem B485651 : Blo 223812 485651 := bstep (se 1 (by rfl) ⟨364238, by rfl⟩ : syracuseStep 485651 = 728477) B728477
theorem B224103 : Blo 223812 224103 := bstep (se 1 (by rfl) ⟨168077, by rfl⟩ : syracuseStep 224103 = 336155) B336155
theorem B224127 : Blo 223812 224127 := bstep (se 1 (by rfl) ⟨168095, by rfl⟩ : syracuseStep 224127 = 336191) B336191
theorem B111602609 : Blo 223812 111602609 := bstep (se 2 (by rfl) ⟨41850978, by rfl⟩ : syracuseStep 111602609 = 83701957) B83701957
theorem B224239 : Blo 223812 224239 := bstep (se 1 (by rfl) ⟨168179, by rfl⟩ : syracuseStep 224239 = 336359) B336359
theorem B224507 : Blo 223812 224507 := bstep (se 1 (by rfl) ⟨168380, by rfl⟩ : syracuseStep 224507 = 336761) B336761
theorem B224671 : Blo 223812 224671 := bstep (se 1 (by rfl) ⟨168503, by rfl⟩ : syracuseStep 224671 = 337007) B337007
theorem B95415803 : Blo 223812 95415803 := bstep (se 1 (by rfl) ⟨71561852, by rfl⟩ : syracuseStep 95415803 = 143123705) B143123705
theorem B224795 : Blo 223812 224795 := bstep (se 1 (by rfl) ⟨168596, by rfl⟩ : syracuseStep 224795 = 337193) B337193
theorem B224815 : Blo 223812 224815 := bstep (se 1 (by rfl) ⟨168611, by rfl⟩ : syracuseStep 224815 = 337223) B337223
theorem B3862241 : Blo 223812 3862241 := bstep (se 2 (by rfl) ⟨1448340, by rfl⟩ : syracuseStep 3862241 = 2896681) B2896681
theorem B225371 : Blo 223812 225371 := bstep (se 1 (by rfl) ⟨169028, by rfl⟩ : syracuseStep 225371 = 338057) B338057
theorem B6484319 : Blo 223812 6484319 := bstep (se 1 (by rfl) ⟨4863239, by rfl⟩ : syracuseStep 6484319 = 9726479) B9726479
theorem B225727 : Blo 223812 225727 := bstep (se 1 (by rfl) ⟨169295, by rfl⟩ : syracuseStep 225727 = 338591) B338591
theorem B1700513 : Blo 223812 1700513 := bstep (se 2 (by rfl) ⟨637692, by rfl⟩ : syracuseStep 1700513 = 1275385) B1275385
theorem B2618087 : Blo 223812 2618087 := bstep (se 1 (by rfl) ⟨1963565, by rfl⟩ : syracuseStep 2618087 = 3927131) B3927131
theorem B226175 : Blo 223812 226175 := bstep (se 1 (by rfl) ⟨169631, by rfl⟩ : syracuseStep 226175 = 339263) B339263
theorem B1831895 : Blo 223812 1831895 := bstep (se 1 (by rfl) ⟨1373921, by rfl⟩ : syracuseStep 1831895 = 2747843) B2747843
theorem B226271 : Blo 223812 226271 := bstep (se 1 (by rfl) ⟨169703, by rfl⟩ : syracuseStep 226271 = 339407) B339407
theorem B1275203 : Blo 223812 1275203 := bstep (se 1 (by rfl) ⟨956402, by rfl⟩ : syracuseStep 1275203 = 1912805) B1912805
theorem B2454893 : Blo 223812 2454893 := bstep (se 3 (by rfl) ⟨460292, by rfl⟩ : syracuseStep 2454893 = 920585) B920585
theorem B226863 : Blo 223812 226863 := bstep (se 1 (by rfl) ⟨170147, by rfl⟩ : syracuseStep 226863 = 340295) B340295
theorem B816713 : Blo 223812 816713 := bstep (se 2 (by rfl) ⟨306267, by rfl⟩ : syracuseStep 816713 = 612535) B612535
theorem B816799 : Blo 223812 816799 := bstep (se 1 (by rfl) ⟨612599, by rfl⟩ : syracuseStep 816799 = 1225199) B1225199
theorem B3831623 : Blo 223812 3831623 := bstep (se 1 (by rfl) ⟨2873717, by rfl⟩ : syracuseStep 3831623 = 5747435) B5747435
theorem B227175 : Blo 223812 227175 := bstep (se 1 (by rfl) ⟨170381, by rfl⟩ : syracuseStep 227175 = 340763) B340763
theorem B227431 : Blo 223812 227431 := bstep (se 1 (by rfl) ⟨170573, by rfl⟩ : syracuseStep 227431 = 341147) B341147
theorem B1702043 : Blo 223812 1702043 := bstep (se 1 (by rfl) ⟨1276532, by rfl⟩ : syracuseStep 1702043 = 2553065) B2553065
theorem B851593 : Blo 223812 851593 := bstep (se 2 (by rfl) ⟨319347, by rfl⟩ : syracuseStep 851593 = 638695) B638695
theorem B9338969 : Blo 223812 9338969 := bstep (se 2 (by rfl) ⟨3502113, by rfl⟩ : syracuseStep 9338969 = 7004227) B7004227
theorem B819767 : Blo 223812 819767 := bstep (se 1 (by rfl) ⟨614825, by rfl⟩ : syracuseStep 819767 = 1229651) B1229651
theorem B820459 : Blo 223812 820459 := bstep (se 1 (by rfl) ⟨615344, by rfl⟩ : syracuseStep 820459 = 1230689) B1230689
theorem B6981565 : Blo 223812 6981565 := bstep (se 3 (by rfl) ⟨1309043, by rfl⟩ : syracuseStep 6981565 = 2618087) B2618087
theorem B2197799 : Blo 223812 2197799 := bstep (se 1 (by rfl) ⟨1648349, by rfl⟩ : syracuseStep 2197799 = 3296699) B3296699
theorem B854495 : Blo 223812 854495 := bstep (se 1 (by rfl) ⟨640871, by rfl⟩ : syracuseStep 854495 = 1281743) B1281743
theorem B2330473 : Blo 223812 2330473 := bstep (se 2 (by rfl) ⟨873927, by rfl⟩ : syracuseStep 2330473 = 1747855) B1747855
theorem B1085471 : Blo 223812 1085471 := bstep (se 1 (by rfl) ⟨814103, by rfl⟩ : syracuseStep 1085471 = 1628207) B1628207
theorem B9736523 : Blo 223812 9736523 := bstep (se 1 (by rfl) ⟨7302392, by rfl⟩ : syracuseStep 9736523 = 14604785) B14604785
theorem B1283201 : Blo 223812 1283201 := bstep (se 2 (by rfl) ⟨481200, by rfl⟩ : syracuseStep 1283201 = 962401) B962401
theorem B759401 : Blo 223812 759401 := bstep (se 2 (by rfl) ⟨284775, by rfl⟩ : syracuseStep 759401 = 569551) B569551
theorem B431743 : Blo 223812 431743 := bstep (se 1 (by rfl) ⟨323807, by rfl⟩ : syracuseStep 431743 = 647615) B647615
theorem B3086063 : Blo 223812 3086063 := bstep (se 1 (by rfl) ⟨2314547, by rfl⟩ : syracuseStep 3086063 = 4629095) B4629095
theorem B3840371 : Blo 223812 3840371 := bstep (se 1 (by rfl) ⟨2880278, by rfl⟩ : syracuseStep 3840371 = 5760557) B5760557
theorem B629147 : Blo 223812 629147 := bstep (se 1 (by rfl) ⟨471860, by rfl⟩ : syracuseStep 629147 = 943721) B943721
theorem B858671 : Blo 223812 858671 := bstep (se 1 (by rfl) ⟨644003, by rfl⟩ : syracuseStep 858671 = 1288007) B1288007
theorem B1089065 : Blo 223812 1089065 := bstep (se 2 (by rfl) ⟨408399, by rfl⟩ : syracuseStep 1089065 = 816799) B816799
theorem B63610535 : Blo 223812 63610535 := bstep (se 1 (by rfl) ⟨47707901, by rfl⟩ : syracuseStep 63610535 = 95415803) B95415803
theorem B8888345 : Blo 223812 8888345 := bstep (se 2 (by rfl) ⟨3333129, by rfl⟩ : syracuseStep 8888345 = 6666259) B6666259
theorem B336095 : Blo 223812 336095 := bstep (se 1 (by rfl) ⟨252071, by rfl⟩ : syracuseStep 336095 = 504143) B504143
theorem B336167 : Blo 223812 336167 := bstep (se 1 (by rfl) ⟨252125, by rfl⟩ : syracuseStep 336167 = 504251) B504251
theorem B336287 : Blo 223812 336287 := bstep (se 1 (by rfl) ⟨252215, by rfl⟩ : syracuseStep 336287 = 504431) B504431
theorem B1221263 : Blo 223812 1221263 := bstep (se 1 (by rfl) ⟨915947, by rfl⟩ : syracuseStep 1221263 = 1831895) B1831895
theorem B336743 : Blo 223812 336743 := bstep (se 1 (by rfl) ⟨252557, by rfl⟩ : syracuseStep 336743 = 505115) B505115
theorem B6169931 : Blo 223812 6169931 := bstep (se 1 (by rfl) ⟨4627448, by rfl⟩ : syracuseStep 6169931 = 9254897) B9254897
theorem B8660519 : Blo 223812 8660519 := bstep (se 1 (by rfl) ⟨6495389, by rfl⟩ : syracuseStep 8660519 = 12990779) B12990779
theorem B862271 : Blo 223812 862271 := bstep (se 1 (by rfl) ⟨646703, by rfl⟩ : syracuseStep 862271 = 1293407) B1293407
theorem B337991 : Blo 223812 337991 := bstep (se 1 (by rfl) ⟨253493, by rfl⟩ : syracuseStep 337991 = 506987) B506987
theorem B338639 : Blo 223812 338639 := bstep (se 1 (by rfl) ⟨253979, by rfl⟩ : syracuseStep 338639 = 507959) B507959
theorem B338663 : Blo 223812 338663 := bstep (se 1 (by rfl) ⟨253997, by rfl⟩ : syracuseStep 338663 = 507995) B507995
theorem B338687 : Blo 223812 338687 := bstep (se 1 (by rfl) ⟨254015, by rfl⟩ : syracuseStep 338687 = 508031) B508031
theorem B568073 : Blo 223812 568073 := bstep (se 2 (by rfl) ⟨213027, by rfl⟩ : syracuseStep 568073 = 426055) B426055
theorem B827370449 : Blo 223812 827370449 := bstep (se 2 (by rfl) ⟨310263918, by rfl⟩ : syracuseStep 827370449 = 620527837) B620527837
theorem B1486673 : Blo 223812 1486673 := bstep (se 2 (by rfl) ⟨557502, by rfl⟩ : syracuseStep 1486673 = 1115005) B1115005
theorem B864215 : Blo 223812 864215 := bstep (se 1 (by rfl) ⟨648161, by rfl⟩ : syracuseStep 864215 = 1296323) B1296323
theorem B503963 : Blo 223812 503963 := bstep (se 1 (by rfl) ⟨377972, by rfl⟩ : syracuseStep 503963 = 755945) B755945
theorem B503999 : Blo 223812 503999 := bstep (se 1 (by rfl) ⟨377999, by rfl⟩ : syracuseStep 503999 = 755999) B755999
theorem B962759 : Blo 223812 962759 := bstep (se 1 (by rfl) ⟨722069, by rfl⟩ : syracuseStep 962759 = 1444139) B1444139
theorem B1454287 : Blo 223812 1454287 := bstep (se 1 (by rfl) ⟨1090715, by rfl⟩ : syracuseStep 1454287 = 2181431) B2181431
theorem B1945883 : Blo 223812 1945883 := bstep (se 1 (by rfl) ⟨1459412, by rfl⟩ : syracuseStep 1945883 = 2918825) B2918825
theorem B2077085 : Blo 223812 2077085 := bstep (se 3 (by rfl) ⟨389453, by rfl⟩ : syracuseStep 2077085 = 778907) B778907
theorem B340415 : Blo 223812 340415 := bstep (se 1 (by rfl) ⟨255311, by rfl⟩ : syracuseStep 340415 = 510623) B510623
theorem B767231 : Blo 223812 767231 := bstep (se 1 (by rfl) ⟨575423, by rfl⟩ : syracuseStep 767231 = 1150847) B1150847
theorem B341327 : Blo 223812 341327 := bstep (se 1 (by rfl) ⟨255995, by rfl⟩ : syracuseStep 341327 = 511991) B511991
theorem B505691 : Blo 223812 505691 := bstep (se 1 (by rfl) ⟨379268, by rfl⟩ : syracuseStep 505691 = 758537) B758537
theorem B3258539 : Blo 223812 3258539 := bstep (se 1 (by rfl) ⟨2443904, by rfl⟩ : syracuseStep 3258539 = 4887809) B4887809
theorem B965135 : Blo 223812 965135 := bstep (se 1 (by rfl) ⟨723851, by rfl⟩ : syracuseStep 965135 = 1447703) B1447703
theorem B965287 : Blo 223812 965287 := bstep (se 1 (by rfl) ⟨723965, by rfl⟩ : syracuseStep 965287 = 1447931) B1447931
theorem B506663 : Blo 223812 506663 := bstep (se 1 (by rfl) ⟨379997, by rfl⟩ : syracuseStep 506663 = 759995) B759995
theorem B637865 : Blo 223812 637865 := bstep (se 2 (by rfl) ⟨239199, by rfl⟩ : syracuseStep 637865 = 478399) B478399
theorem B1555625 : Blo 223812 1555625 := bstep (se 2 (by rfl) ⟨583359, by rfl⟩ : syracuseStep 1555625 = 1166719) B1166719
theorem B507257 : Blo 223812 507257 := bstep (se 2 (by rfl) ⟨190221, by rfl⟩ : syracuseStep 507257 = 380443) B380443
theorem B507383 : Blo 223812 507383 := bstep (se 1 (by rfl) ⟨380537, by rfl⟩ : syracuseStep 507383 = 761075) B761075
theorem B8699885 : Blo 223812 8699885 := bstep (se 3 (by rfl) ⟨1631228, by rfl⟩ : syracuseStep 8699885 = 3262457) B3262457
theorem B1917179 : Blo 223812 1917179 := bstep (se 1 (by rfl) ⟨1437884, by rfl⟩ : syracuseStep 1917179 = 2875769) B2875769
theorem B542015 : Blo 223812 542015 := bstep (se 1 (by rfl) ⟨406511, by rfl⟩ : syracuseStep 542015 = 813023) B813023
theorem B509417 : Blo 223812 509417 := bstep (se 2 (by rfl) ⟨191031, by rfl⟩ : syracuseStep 509417 = 382063) B382063
theorem B74401739 : Blo 223812 74401739 := bstep (se 1 (by rfl) ⟨55801304, by rfl⟩ : syracuseStep 74401739 = 111602609) B111602609
theorem B510263 : Blo 223812 510263 := bstep (se 1 (by rfl) ⟨382697, by rfl⟩ : syracuseStep 510263 = 765395) B765395
theorem B2574827 : Blo 223812 2574827 := bstep (se 1 (by rfl) ⟨1931120, by rfl⟩ : syracuseStep 2574827 = 3862241) B3862241
theorem B1133675 : Blo 223812 1133675 := bstep (se 1 (by rfl) ⟨850256, by rfl⟩ : syracuseStep 1133675 = 1700513) B1700513
theorem B544475 : Blo 223812 544475 := bstep (se 1 (by rfl) ⟨408356, by rfl⟩ : syracuseStep 544475 = 816713) B816713
theorem B1134695 : Blo 223812 1134695 := bstep (se 1 (by rfl) ⟨851021, by rfl⟩ : syracuseStep 1134695 = 1702043) B1702043
theorem B381415 : Blo 223812 381415 := bstep (se 1 (by rfl) ⟨286061, by rfl⟩ : syracuseStep 381415 = 572123) B572123
theorem B1135457 : Blo 223812 1135457 := bstep (se 2 (by rfl) ⟨425796, by rfl⟩ : syracuseStep 1135457 = 851593) B851593
theorem B644699 : Blo 223812 644699 := bstep (se 1 (by rfl) ⟨483524, by rfl⟩ : syracuseStep 644699 = 967049) B967049
theorem B251815 : Blo 223812 251815 := bstep (se 1 (by rfl) ⟨188861, by rfl⟩ : syracuseStep 251815 = 377723) B377723
theorem B547127 : Blo 223812 547127 := bstep (se 1 (by rfl) ⟨410345, by rfl⟩ : syracuseStep 547127 = 820691) B820691
theorem B252463 : Blo 223812 252463 := bstep (se 1 (by rfl) ⟨189347, by rfl⟩ : syracuseStep 252463 = 378695) B378695
theorem B285439 : Blo 223812 285439 := bstep (se 1 (by rfl) ⟨214079, by rfl⟩ : syracuseStep 285439 = 428159) B428159
theorem B908129 : Blo 223812 908129 := bstep (se 2 (by rfl) ⟨340548, by rfl⟩ : syracuseStep 908129 = 681097) B681097
theorem B908255 : Blo 223812 908255 := bstep (se 1 (by rfl) ⟨681191, by rfl⟩ : syracuseStep 908255 = 1362383) B1362383
theorem B547931 : Blo 223812 547931 := bstep (se 1 (by rfl) ⟨410948, by rfl⟩ : syracuseStep 547931 = 821897) B821897
theorem B253039 : Blo 223812 253039 := bstep (se 1 (by rfl) ⟨189779, by rfl⟩ : syracuseStep 253039 = 379559) B379559
theorem B384311 : Blo 223812 384311 := bstep (se 1 (by rfl) ⟨288233, by rfl⟩ : syracuseStep 384311 = 576467) B576467
theorem B1728647 : Blo 223812 1728647 := bstep (se 1 (by rfl) ⟨1296485, by rfl⟩ : syracuseStep 1728647 = 2592971) B2592971
theorem B614783 : Blo 223812 614783 := bstep (se 1 (by rfl) ⟨461087, by rfl⟩ : syracuseStep 614783 = 922175) B922175
theorem B2187971 : Blo 223812 2187971 := bstep (se 1 (by rfl) ⟨1640978, by rfl⟩ : syracuseStep 2187971 = 3281957) B3281957
theorem B484489 : Blo 223812 484489 := bstep (se 2 (by rfl) ⟨181683, by rfl⟩ : syracuseStep 484489 = 363367) B363367
theorem B223871 : Blo 223812 223871 := bstep (se 1 (by rfl) ⟨167903, by rfl⟩ : syracuseStep 223871 = 335807) B335807
theorem B1632905 : Blo 223812 1632905 := bstep (se 2 (by rfl) ⟨612339, by rfl⟩ : syracuseStep 1632905 = 1224679) B1224679
theorem B224071 : Blo 223812 224071 := bstep (se 1 (by rfl) ⟨168053, by rfl⟩ : syracuseStep 224071 = 336107) B336107
theorem B1535257 : Blo 223812 1535257 := bstep (se 2 (by rfl) ⟨575721, by rfl⟩ : syracuseStep 1535257 = 1151443) B1151443
theorem B225215 : Blo 223812 225215 := bstep (se 1 (by rfl) ⟨168911, by rfl⟩ : syracuseStep 225215 = 337823) B337823
theorem B323767 : Blo 223812 323767 := bstep (se 1 (by rfl) ⟨242825, by rfl⟩ : syracuseStep 323767 = 485651) B485651
theorem B225563 : Blo 223812 225563 := bstep (se 1 (by rfl) ⟨169172, by rfl⟩ : syracuseStep 225563 = 338345) B338345
theorem B225819 : Blo 223812 225819 := bstep (se 1 (by rfl) ⟨169364, by rfl⟩ : syracuseStep 225819 = 338729) B338729
theorem B225919 : Blo 223812 225919 := bstep (se 1 (by rfl) ⟨169439, by rfl⟩ : syracuseStep 225919 = 338879) B338879
theorem B226663 : Blo 223812 226663 := bstep (se 1 (by rfl) ⟨169997, by rfl⟩ : syracuseStep 226663 = 339995) B339995
theorem B4322879 : Blo 223812 4322879 := bstep (se 1 (by rfl) ⟨3242159, by rfl⟩ : syracuseStep 4322879 = 6484319) B6484319
theorem B227239 : Blo 223812 227239 := bstep (se 1 (by rfl) ⟨170429, by rfl⟩ : syracuseStep 227239 = 340859) B340859
theorem B227535 : Blo 223812 227535 := bstep (se 1 (by rfl) ⟨170651, by rfl⟩ : syracuseStep 227535 = 341303) B341303
theorem B850135 : Blo 223812 850135 := bstep (se 1 (by rfl) ⟨637601, by rfl⟩ : syracuseStep 850135 = 1275203) B1275203
theorem B1636595 : Blo 223812 1636595 := bstep (se 1 (by rfl) ⟨1227446, by rfl⟩ : syracuseStep 1636595 = 2454893) B2454893
theorem B2554415 : Blo 223812 2554415 := bstep (se 1 (by rfl) ⟨1915811, by rfl⟩ : syracuseStep 2554415 = 3831623) B3831623
theorem B1145825 : Blo 223812 1145825 := bstep (se 2 (by rfl) ⟨429684, by rfl⟩ : syracuseStep 1145825 = 859369) B859369
theorem B818153 : Blo 223812 818153 := bstep (se 2 (by rfl) ⟨306807, by rfl⟩ : syracuseStep 818153 = 613615) B613615
theorem B1277801 : Blo 223812 1277801 := bstep (se 2 (by rfl) ⟨479175, by rfl⟩ : syracuseStep 1277801 = 958351) B958351
theorem B6225979 : Blo 223812 6225979 := bstep (se 1 (by rfl) ⟨4669484, by rfl⟩ : syracuseStep 6225979 = 9338969) B9338969
theorem B1278119 : Blo 223812 1278119 := bstep (se 1 (by rfl) ⟨958589, by rfl⟩ : syracuseStep 1278119 = 1917179) B1917179
theorem B361343 : Blo 223812 361343 := bstep (se 1 (by rfl) ⟨271007, by rfl⟩ : syracuseStep 361343 = 542015) B542015
theorem B5538893 : Blo 223812 5538893 := bstep (se 3 (by rfl) ⟨1038542, by rfl⟩ : syracuseStep 5538893 = 2077085) B2077085
theorem B755783 : Blo 223812 755783 := bstep (se 1 (by rfl) ⟨566837, by rfl⟩ : syracuseStep 755783 = 1133675) B1133675
theorem B362983 : Blo 223812 362983 := bstep (se 1 (by rfl) ⟨272237, by rfl⟩ : syracuseStep 362983 = 544475) B544475
theorem B9308753 : Blo 223812 9308753 := bstep (se 2 (by rfl) ⟨3490782, by rfl⟩ : syracuseStep 9308753 = 6981565) B6981565
theorem B723647 : Blo 223812 723647 := bstep (se 1 (by rfl) ⟨542735, by rfl⟩ : syracuseStep 723647 = 1085471) B1085471
theorem B756463 : Blo 223812 756463 := bstep (se 1 (by rfl) ⟨567347, by rfl⟩ : syracuseStep 756463 = 1134695) B1134695
theorem B6491015 : Blo 223812 6491015 := bstep (se 1 (by rfl) ⟨4868261, by rfl⟩ : syracuseStep 6491015 = 9736523) B9736523
theorem B756971 : Blo 223812 756971 := bstep (se 1 (by rfl) ⟨567728, by rfl⟩ : syracuseStep 756971 = 1135457) B1135457
theorem B855467 : Blo 223812 855467 := bstep (se 1 (by rfl) ⟨641600, by rfl⟩ : syracuseStep 855467 = 1283201) B1283201
theorem B429799 : Blo 223812 429799 := bstep (se 1 (by rfl) ⟨322349, by rfl⟩ : syracuseStep 429799 = 644699) B644699
theorem B364751 : Blo 223812 364751 := bstep (se 1 (by rfl) ⟨273563, by rfl⟩ : syracuseStep 364751 = 547127) B547127
theorem B2560247 : Blo 223812 2560247 := bstep (se 1 (by rfl) ⟨1920185, by rfl⟩ : syracuseStep 2560247 = 3840371) B3840371
theorem B726043 : Blo 223812 726043 := bstep (se 1 (by rfl) ⟨544532, by rfl⟩ : syracuseStep 726043 = 1089065) B1089065
theorem B42407023 : Blo 223812 42407023 := bstep (se 1 (by rfl) ⟨31805267, by rfl⟩ : syracuseStep 42407023 = 63610535) B63610535
theorem B1152431 : Blo 223812 1152431 := bstep (se 1 (by rfl) ⟨864323, by rfl⟩ : syracuseStep 1152431 = 1728647) B1728647
theorem B1939049 : Blo 223812 1939049 := bstep (se 2 (by rfl) ⟨727143, by rfl⟩ : syracuseStep 1939049 = 1454287) B1454287
theorem B5773679 : Blo 223812 5773679 := bstep (se 1 (by rfl) ⟨4330259, by rfl⟩ : syracuseStep 5773679 = 8660519) B8660519
theorem B1088603 : Blo 223812 1088603 := bstep (se 1 (by rfl) ⟨816452, by rfl⟩ : syracuseStep 1088603 = 1632905) B1632905
theorem B335753 : Blo 223812 335753 := bstep (se 2 (by rfl) ⟨125907, by rfl⟩ : syracuseStep 335753 = 251815) B251815
theorem B991115 : Blo 223812 991115 := bstep (se 1 (by rfl) ⟨743336, by rfl⟩ : syracuseStep 991115 = 1486673) B1486673
theorem B335975 : Blo 223812 335975 := bstep (se 1 (by rfl) ⟨251981, by rfl⟩ : syracuseStep 335975 = 503963) B503963
theorem B335999 : Blo 223812 335999 := bstep (se 1 (by rfl) ⟨251999, by rfl⟩ : syracuseStep 335999 = 503999) B503999
theorem B336617 : Blo 223812 336617 := bstep (se 2 (by rfl) ⟨126231, by rfl⟩ : syracuseStep 336617 = 252463) B252463
theorem B1287049 : Blo 223812 1287049 := bstep (se 2 (by rfl) ⟨482643, by rfl⟩ : syracuseStep 1287049 = 965287) B965287
theorem B337127 : Blo 223812 337127 := bstep (se 1 (by rfl) ⟨252845, by rfl⟩ : syracuseStep 337127 = 505691) B505691
theorem B2172359 : Blo 223812 2172359 := bstep (se 1 (by rfl) ⟨1629269, by rfl⟩ : syracuseStep 2172359 = 3258539) B3258539
theorem B337385 : Blo 223812 337385 := bstep (se 2 (by rfl) ⟨126519, by rfl⟩ : syracuseStep 337385 = 253039) B253039
theorem B1091063 : Blo 223812 1091063 := bstep (se 1 (by rfl) ⟨818297, by rfl⟩ : syracuseStep 1091063 = 1636595) B1636595
theorem B337775 : Blo 223812 337775 := bstep (se 1 (by rfl) ⟨253331, by rfl⟩ : syracuseStep 337775 = 506663) B506663
theorem B763883 : Blo 223812 763883 := bstep (se 1 (by rfl) ⟨572912, by rfl⟩ : syracuseStep 763883 = 1145825) B1145825
theorem B338171 : Blo 223812 338171 := bstep (se 1 (by rfl) ⟨253628, by rfl⟩ : syracuseStep 338171 = 507257) B507257
theorem B338255 : Blo 223812 338255 := bstep (se 1 (by rfl) ⟨253691, by rfl⟩ : syracuseStep 338255 = 507383) B507383
theorem B339611 : Blo 223812 339611 := bstep (se 1 (by rfl) ⟨254708, by rfl⟩ : syracuseStep 339611 = 509417) B509417
theorem B340175 : Blo 223812 340175 := bstep (se 1 (by rfl) ⟨255131, by rfl⟩ : syracuseStep 340175 = 510263) B510263
theorem B1093945 : Blo 223812 1093945 := bstep (se 2 (by rfl) ⟨410229, by rfl⟩ : syracuseStep 1093945 = 820459) B820459
theorem B569663 : Blo 223812 569663 := bstep (se 1 (by rfl) ⟨427247, by rfl⟩ : syracuseStep 569663 = 854495) B854495
theorem B1716551 : Blo 223812 1716551 := bstep (se 1 (by rfl) ⟨1287413, by rfl⟩ : syracuseStep 1716551 = 2574827) B2574827
theorem B506267 : Blo 223812 506267 := bstep (se 1 (by rfl) ⟨379700, by rfl⟩ : syracuseStep 506267 = 759401) B759401
theorem B572447 : Blo 223812 572447 := bstep (se 1 (by rfl) ⟨429335, by rfl⟩ : syracuseStep 572447 = 858671) B858671
theorem B605503 : Blo 223812 605503 := bstep (se 1 (by rfl) ⟨454127, by rfl⟩ : syracuseStep 605503 = 908255) B908255
theorem B409855 : Blo 223812 409855 := bstep (se 1 (by rfl) ⟨307391, by rfl⟩ : syracuseStep 409855 = 614783) B614783
theorem B1458647 : Blo 223812 1458647 := bstep (se 1 (by rfl) ⟨1093985, by rfl⟩ : syracuseStep 1458647 = 2187971) B2187971
theorem B508553 : Blo 223812 508553 := bstep (se 2 (by rfl) ⟨190707, by rfl⟩ : syracuseStep 508553 = 381415) B381415
theorem B4113287 : Blo 223812 4113287 := bstep (se 1 (by rfl) ⟨3084965, by rfl⟩ : syracuseStep 4113287 = 6169931) B6169931
theorem B574847 : Blo 223812 574847 := bstep (se 1 (by rfl) ⟨431135, by rfl⟩ : syracuseStep 574847 = 862271) B862271
theorem B378715 : Blo 223812 378715 := bstep (se 1 (by rfl) ⟨284036, by rfl⟩ : syracuseStep 378715 = 568073) B568073
theorem B575657 : Blo 223812 575657 := bstep (se 2 (by rfl) ⟨215871, by rfl⟩ : syracuseStep 575657 = 431743) B431743
theorem B576143 : Blo 223812 576143 := bstep (se 1 (by rfl) ⟨432107, by rfl⟩ : syracuseStep 576143 = 864215) B864215
theorem B641839 : Blo 223812 641839 := bstep (se 1 (by rfl) ⟨481379, by rfl⟩ : syracuseStep 641839 = 962759) B962759
theorem B1297255 : Blo 223812 1297255 := bstep (se 1 (by rfl) ⟨972941, by rfl⟩ : syracuseStep 1297255 = 1945883) B1945883
theorem B1461149 : Blo 223812 1461149 := bstep (se 3 (by rfl) ⟨273965, by rfl⟩ : syracuseStep 1461149 = 547931) B547931
theorem B1133513 : Blo 223812 1133513 := bstep (se 2 (by rfl) ⟨425067, by rfl⟩ : syracuseStep 1133513 = 850135) B850135
theorem B511487 : Blo 223812 511487 := bstep (se 1 (by rfl) ⟨383615, by rfl⟩ : syracuseStep 511487 = 767231) B767231
theorem B380585 : Blo 223812 380585 := bstep (se 2 (by rfl) ⟨142719, by rfl⟩ : syracuseStep 380585 = 285439) B285439
theorem B643423 : Blo 223812 643423 := bstep (se 1 (by rfl) ⟨482567, by rfl⟩ : syracuseStep 643423 = 965135) B965135
theorem B545435 : Blo 223812 545435 := bstep (se 1 (by rfl) ⟨409076, by rfl⟩ : syracuseStep 545435 = 818153) B818153
theorem B1037083 : Blo 223812 1037083 := bstep (se 1 (by rfl) ⟨777812, by rfl⟩ : syracuseStep 1037083 = 1555625) B1555625
theorem B546511 : Blo 223812 546511 := bstep (se 1 (by rfl) ⟨409883, by rfl⟩ : syracuseStep 546511 = 819767) B819767
theorem B1726757 : Blo 223812 1726757 := bstep (se 4 (by rfl) ⟨161883, by rfl⟩ : syracuseStep 1726757 = 323767) B323767
theorem B49601159 : Blo 223812 49601159 := bstep (se 1 (by rfl) ⟨37200869, by rfl⟩ : syracuseStep 49601159 = 74401739) B74401739
theorem B645985 : Blo 223812 645985 := bstep (se 2 (by rfl) ⟨242244, by rfl⟩ : syracuseStep 645985 = 484489) B484489
theorem B1465199 : Blo 223812 1465199 := bstep (se 1 (by rfl) ⟨1098899, by rfl⟩ : syracuseStep 1465199 = 2197799) B2197799
theorem B2057375 : Blo 223812 2057375 := bstep (se 1 (by rfl) ⟨1543031, by rfl⟩ : syracuseStep 2057375 = 3086063) B3086063
theorem B419431 : Blo 223812 419431 := bstep (se 1 (by rfl) ⟨314573, by rfl⟩ : syracuseStep 419431 = 629147) B629147
theorem B256207 : Blo 223812 256207 := bstep (se 1 (by rfl) ⟨192155, by rfl⟩ : syracuseStep 256207 = 384311) B384311
theorem B3107297 : Blo 223812 3107297 := bstep (se 2 (by rfl) ⟨1165236, by rfl⟩ : syracuseStep 3107297 = 2330473) B2330473
theorem B5925563 : Blo 223812 5925563 := bstep (se 1 (by rfl) ⟨4444172, by rfl⟩ : syracuseStep 5925563 = 8888345) B8888345
theorem B224063 : Blo 223812 224063 := bstep (se 1 (by rfl) ⟨168047, by rfl⟩ : syracuseStep 224063 = 336095) B336095
theorem B224111 : Blo 223812 224111 := bstep (se 1 (by rfl) ⟨168083, by rfl⟩ : syracuseStep 224111 = 336167) B336167
theorem B224191 : Blo 223812 224191 := bstep (se 1 (by rfl) ⟨168143, by rfl⟩ : syracuseStep 224191 = 336287) B336287
theorem B814175 : Blo 223812 814175 := bstep (se 1 (by rfl) ⟨610631, by rfl⟩ : syracuseStep 814175 = 1221263) B1221263
theorem B224495 : Blo 223812 224495 := bstep (se 1 (by rfl) ⟨168371, by rfl⟩ : syracuseStep 224495 = 336743) B336743
theorem B225327 : Blo 223812 225327 := bstep (se 1 (by rfl) ⟨168995, by rfl⟩ : syracuseStep 225327 = 337991) B337991
theorem B8188037 : Blo 223812 8188037 := bstep (se 4 (by rfl) ⟨767628, by rfl⟩ : syracuseStep 8188037 = 1535257) B1535257
theorem B225759 : Blo 223812 225759 := bstep (se 1 (by rfl) ⟨169319, by rfl⟩ : syracuseStep 225759 = 338639) B338639
theorem B225775 : Blo 223812 225775 := bstep (se 1 (by rfl) ⟨169331, by rfl⟩ : syracuseStep 225775 = 338663) B338663
theorem B225791 : Blo 223812 225791 := bstep (se 1 (by rfl) ⟨169343, by rfl⟩ : syracuseStep 225791 = 338687) B338687
theorem B551580299 : Blo 223812 551580299 := bstep (se 1 (by rfl) ⟨413685224, by rfl⟩ : syracuseStep 551580299 = 827370449) B827370449
theorem B2421677 : Blo 223812 2421677 := bstep (se 3 (by rfl) ⟨454064, by rfl⟩ : syracuseStep 2421677 = 908129) B908129
theorem B226943 : Blo 223812 226943 := bstep (se 1 (by rfl) ⟨170207, by rfl⟩ : syracuseStep 226943 = 340415) B340415
theorem B227551 : Blo 223812 227551 := bstep (se 1 (by rfl) ⟨170663, by rfl⟩ : syracuseStep 227551 = 341327) B341327
theorem B2881919 : Blo 223812 2881919 := bstep (se 1 (by rfl) ⟨2161439, by rfl⟩ : syracuseStep 2881919 = 4322879) B4322879
theorem B1702943 : Blo 223812 1702943 := bstep (se 1 (by rfl) ⟨1277207, by rfl⟩ : syracuseStep 1702943 = 2554415) B2554415
theorem B425243 : Blo 223812 425243 := bstep (se 1 (by rfl) ⟨318932, by rfl⟩ : syracuseStep 425243 = 637865) B637865
theorem B851867 : Blo 223812 851867 := bstep (se 1 (by rfl) ⟨638900, by rfl⟩ : syracuseStep 851867 = 1277801) B1277801
theorem B5799923 : Blo 223812 5799923 := bstep (se 1 (by rfl) ⟨4349942, by rfl⟩ : syracuseStep 5799923 = 8699885) B8699885
theorem B852079 : Blo 223812 852079 := bstep (se 1 (by rfl) ⟨639059, by rfl⟩ : syracuseStep 852079 = 1278119) B1278119
theorem B59081525 : Blo 223812 59081525 := bstep (se 5 (by rfl) ⟨2769446, by rfl⟩ : syracuseStep 59081525 = 5538893) B5538893
theorem B4327343 : Blo 223812 4327343 := bstep (se 1 (by rfl) ⟨3245507, by rfl⟩ : syracuseStep 4327343 = 6491015) B6491015
theorem B755675 : Blo 223812 755675 := bstep (se 1 (by rfl) ⟨566756, by rfl⟩ : syracuseStep 755675 = 1133513) B1133513
theorem B559241 : Blo 223812 559241 := bstep (se 2 (by rfl) ⟨209715, by rfl⟩ : syracuseStep 559241 = 419431) B419431
theorem B1706831 : Blo 223812 1706831 := bstep (se 1 (by rfl) ⟨1280123, by rfl⟩ : syracuseStep 1706831 = 2560247) B2560247
theorem B363623 : Blo 223812 363623 := bstep (se 1 (by rfl) ⟨272717, by rfl⟩ : syracuseStep 363623 = 545435) B545435
theorem B855785 : Blo 223812 855785 := bstep (se 2 (by rfl) ⟨320919, by rfl⟩ : syracuseStep 855785 = 641839) B641839
theorem B1151171 : Blo 223812 1151171 := bstep (se 1 (by rfl) ⟨863378, by rfl⟩ : syracuseStep 1151171 = 1726757) B1726757
theorem B33067439 : Blo 223812 33067439 := bstep (se 1 (by rfl) ⟨24800579, by rfl⟩ : syracuseStep 33067439 = 49601159) B49601159
theorem B725735 : Blo 223812 725735 := bstep (se 1 (by rfl) ⟨544301, by rfl⟩ : syracuseStep 725735 = 1088603) B1088603
theorem B660743 : Blo 223812 660743 := bstep (se 1 (by rfl) ⟨495557, by rfl⟩ : syracuseStep 660743 = 991115) B991115
theorem B857897 : Blo 223812 857897 := bstep (se 2 (by rfl) ⟨321711, by rfl⟩ : syracuseStep 857897 = 643423) B643423
theorem B1448239 : Blo 223812 1448239 := bstep (se 1 (by rfl) ⟨1086179, by rfl⟩ : syracuseStep 1448239 = 2172359) B2172359
theorem B727375 : Blo 223812 727375 := bstep (se 1 (by rfl) ⟨545531, by rfl⟩ : syracuseStep 727375 = 1091063) B1091063
theorem B1382777 : Blo 223812 1382777 := bstep (se 2 (by rfl) ⟨518541, by rfl⟩ : syracuseStep 1382777 = 1037083) B1037083
theorem B2071531 : Blo 223812 2071531 := bstep (se 1 (by rfl) ⟨1553648, by rfl⟩ : syracuseStep 2071531 = 3107297) B3107297
theorem B728681 : Blo 223812 728681 := bstep (se 2 (by rfl) ⟨273255, by rfl⟩ : syracuseStep 728681 = 546511) B546511
theorem B1614451 : Blo 223812 1614451 := bstep (se 1 (by rfl) ⟨1210838, by rfl⟩ : syracuseStep 1614451 = 2421677) B2421677
theorem B861313 : Blo 223812 861313 := bstep (se 2 (by rfl) ⟨322992, by rfl⟩ : syracuseStep 861313 = 645985) B645985
theorem B337511 : Blo 223812 337511 := bstep (se 1 (by rfl) ⟨253133, by rfl⟩ : syracuseStep 337511 = 506267) B506267
theorem B567911 : Blo 223812 567911 := bstep (se 1 (by rfl) ⟨425933, by rfl⟩ : syracuseStep 567911 = 851867) B851867
theorem B8301305 : Blo 223812 8301305 := bstep (se 2 (by rfl) ⟨3112989, by rfl⟩ : syracuseStep 8301305 = 6225979) B6225979
theorem B339035 : Blo 223812 339035 := bstep (se 1 (by rfl) ⟨254276, by rfl⟩ : syracuseStep 339035 = 508553) B508553
theorem B240895 : Blo 223812 240895 := bstep (se 1 (by rfl) ⟨180671, by rfl⟩ : syracuseStep 240895 = 361343) B361343
theorem B1716065 : Blo 223812 1716065 := bstep (se 2 (by rfl) ⟨643524, by rfl⟩ : syracuseStep 1716065 = 1287049) B1287049
theorem B503855 : Blo 223812 503855 := bstep (se 1 (by rfl) ⟨377891, by rfl⟩ : syracuseStep 503855 = 755783) B755783
theorem B6205835 : Blo 223812 6205835 := bstep (se 1 (by rfl) ⟨4654376, by rfl⟩ : syracuseStep 6205835 = 9308753) B9308753
theorem B504647 : Blo 223812 504647 := bstep (se 1 (by rfl) ⟨378485, by rfl⟩ : syracuseStep 504647 = 756971) B756971
theorem B570311 : Blo 223812 570311 := bstep (se 1 (by rfl) ⟨427733, by rfl⟩ : syracuseStep 570311 = 855467) B855467
theorem B340991 : Blo 223812 340991 := bstep (se 1 (by rfl) ⟨255743, by rfl⟩ : syracuseStep 340991 = 511487) B511487
theorem B504953 : Blo 223812 504953 := bstep (se 2 (by rfl) ⟨189357, by rfl⟩ : syracuseStep 504953 = 378715) B378715
theorem B243167 : Blo 223812 243167 := bstep (se 1 (by rfl) ⟨182375, by rfl⟩ : syracuseStep 243167 = 364751) B364751
theorem B341609 : Blo 223812 341609 := bstep (se 2 (by rfl) ⟨128103, by rfl⟩ : syracuseStep 341609 = 256207) B256207
theorem B768287 : Blo 223812 768287 := bstep (se 1 (by rfl) ⟨576215, by rfl⟩ : syracuseStep 768287 = 1152431) B1152431
theorem B1292699 : Blo 223812 1292699 := bstep (se 1 (by rfl) ⟨969524, by rfl⟩ : syracuseStep 1292699 = 1939049) B1939049
theorem B3849119 : Blo 223812 3849119 := bstep (se 1 (by rfl) ⟨2886839, by rfl⟩ : syracuseStep 3849119 = 5773679) B5773679
theorem B573065 : Blo 223812 573065 := bstep (se 2 (by rfl) ⟨214899, by rfl⟩ : syracuseStep 573065 = 429799) B429799
theorem B1458593 : Blo 223812 1458593 := bstep (se 2 (by rfl) ⟨546972, by rfl⟩ : syracuseStep 1458593 = 1093945) B1093945
theorem B509255 : Blo 223812 509255 := bstep (se 1 (by rfl) ⟨381941, by rfl⟩ : syracuseStep 509255 = 763883) B763883
theorem B968057 : Blo 223812 968057 := bstep (se 2 (by rfl) ⟨363021, by rfl⟩ : syracuseStep 968057 = 726043) B726043
theorem B56542697 : Blo 223812 56542697 := bstep (se 2 (by rfl) ⟨21203511, by rfl⟩ : syracuseStep 56542697 = 42407023) B42407023
theorem B3950375 : Blo 223812 3950375 := bstep (se 1 (by rfl) ⟨2962781, by rfl⟩ : syracuseStep 3950375 = 5925563) B5925563
theorem B542783 : Blo 223812 542783 := bstep (se 1 (by rfl) ⟨407087, by rfl⟩ : syracuseStep 542783 = 814175) B814175
theorem B5458691 : Blo 223812 5458691 := bstep (se 1 (by rfl) ⟨4094018, by rfl⟩ : syracuseStep 5458691 = 8188037) B8188037
theorem B379775 : Blo 223812 379775 := bstep (se 1 (by rfl) ⟨284831, by rfl⟩ : syracuseStep 379775 = 569663) B569663
theorem B1921279 : Blo 223812 1921279 := bstep (se 1 (by rfl) ⟨1440959, by rfl⟩ : syracuseStep 1921279 = 2881919) B2881919
theorem B807337 : Blo 223812 807337 := bstep (se 2 (by rfl) ⟨302751, by rfl⟩ : syracuseStep 807337 = 605503) B605503
theorem B1135295 : Blo 223812 1135295 := bstep (se 1 (by rfl) ⟨851471, by rfl⟩ : syracuseStep 1135295 = 1702943) B1702943
theorem B381631 : Blo 223812 381631 := bstep (se 1 (by rfl) ⟨286223, by rfl⟩ : syracuseStep 381631 = 572447) B572447
theorem B283495 : Blo 223812 283495 := bstep (se 1 (by rfl) ⟨212621, by rfl⟩ : syracuseStep 283495 = 425243) B425243
theorem B972431 : Blo 223812 972431 := bstep (se 1 (by rfl) ⟨729323, by rfl⟩ : syracuseStep 972431 = 1458647) B1458647
theorem B546473 : Blo 223812 546473 := bstep (se 2 (by rfl) ⟨204927, by rfl⟩ : syracuseStep 546473 = 409855) B409855
theorem B2742191 : Blo 223812 2742191 := bstep (se 1 (by rfl) ⟨2056643, by rfl⟩ : syracuseStep 2742191 = 4113287) B4113287
theorem B383231 : Blo 223812 383231 := bstep (se 1 (by rfl) ⟨287423, by rfl⟩ : syracuseStep 383231 = 574847) B574847
theorem B383771 : Blo 223812 383771 := bstep (se 1 (by rfl) ⟨287828, by rfl⟩ : syracuseStep 383771 = 575657) B575657
theorem B384095 : Blo 223812 384095 := bstep (se 1 (by rfl) ⟨288071, by rfl⟩ : syracuseStep 384095 = 576143) B576143
theorem B482431 : Blo 223812 482431 := bstep (se 1 (by rfl) ⟨361823, by rfl⟩ : syracuseStep 482431 = 723647) B723647
theorem B974099 : Blo 223812 974099 := bstep (se 1 (by rfl) ⟨730574, by rfl⟩ : syracuseStep 974099 = 1461149) B1461149
theorem B253723 : Blo 223812 253723 := bstep (se 1 (by rfl) ⟨190292, by rfl⟩ : syracuseStep 253723 = 380585) B380585
theorem B483977 : Blo 223812 483977 := bstep (se 2 (by rfl) ⟨181491, by rfl⟩ : syracuseStep 483977 = 362983) B362983
theorem B1008617 : Blo 223812 1008617 := bstep (se 2 (by rfl) ⟨378231, by rfl⟩ : syracuseStep 1008617 = 756463) B756463
theorem B1729673 : Blo 223812 1729673 := bstep (se 2 (by rfl) ⟨648627, by rfl⟩ : syracuseStep 1729673 = 1297255) B1297255
theorem B976799 : Blo 223812 976799 := bstep (se 1 (by rfl) ⟨732599, by rfl⟩ : syracuseStep 976799 = 1465199) B1465199
theorem B223835 : Blo 223812 223835 := bstep (se 1 (by rfl) ⟨167876, by rfl⟩ : syracuseStep 223835 = 335753) B335753
theorem B223983 : Blo 223812 223983 := bstep (se 1 (by rfl) ⟨167987, by rfl⟩ : syracuseStep 223983 = 335975) B335975
theorem B223999 : Blo 223812 223999 := bstep (se 1 (by rfl) ⟨167999, by rfl⟩ : syracuseStep 223999 = 335999) B335999
theorem B224411 : Blo 223812 224411 := bstep (se 1 (by rfl) ⟨168308, by rfl⟩ : syracuseStep 224411 = 336617) B336617
theorem B1371583 : Blo 223812 1371583 := bstep (se 1 (by rfl) ⟨1028687, by rfl⟩ : syracuseStep 1371583 = 2057375) B2057375
theorem B224751 : Blo 223812 224751 := bstep (se 1 (by rfl) ⟨168563, by rfl⟩ : syracuseStep 224751 = 337127) B337127
theorem B224923 : Blo 223812 224923 := bstep (se 1 (by rfl) ⟨168692, by rfl⟩ : syracuseStep 224923 = 337385) B337385
theorem B225183 : Blo 223812 225183 := bstep (se 1 (by rfl) ⟨168887, by rfl⟩ : syracuseStep 225183 = 337775) B337775
theorem B225447 : Blo 223812 225447 := bstep (se 1 (by rfl) ⟨169085, by rfl⟩ : syracuseStep 225447 = 338171) B338171
theorem B225503 : Blo 223812 225503 := bstep (se 1 (by rfl) ⟨169127, by rfl⟩ : syracuseStep 225503 = 338255) B338255
theorem B226407 : Blo 223812 226407 := bstep (se 1 (by rfl) ⟨169805, by rfl⟩ : syracuseStep 226407 = 339611) B339611
theorem B226783 : Blo 223812 226783 := bstep (se 1 (by rfl) ⟨170087, by rfl⟩ : syracuseStep 226783 = 340175) B340175
theorem B1144367 : Blo 223812 1144367 := bstep (se 1 (by rfl) ⟨858275, by rfl⟩ : syracuseStep 1144367 = 1716551) B1716551
theorem B367720199 : Blo 223812 367720199 := bstep (se 1 (by rfl) ⟨275790149, by rfl⟩ : syracuseStep 367720199 = 551580299) B551580299
theorem B3866615 : Blo 223812 3866615 := bstep (se 1 (by rfl) ⟨2899961, by rfl⟩ : syracuseStep 3866615 = 5799923) B5799923
theorem B39387683 : Blo 223812 39387683 := bstep (se 1 (by rfl) ⟨29540762, by rfl⟩ : syracuseStep 39387683 = 59081525) B59081525
theorem B16548893 : Blo 223812 16548893 := bstep (se 3 (by rfl) ⟨3102917, by rfl⟩ : syracuseStep 16548893 = 6205835) B6205835
theorem B2884895 : Blo 223812 2884895 := bstep (se 1 (by rfl) ⟨2163671, by rfl⟩ : syracuseStep 2884895 = 4327343) B4327343
theorem B361855 : Blo 223812 361855 := bstep (se 1 (by rfl) ⟨271391, by rfl⟩ : syracuseStep 361855 = 542783) B542783
theorem B1148417 : Blo 223812 1148417 := bstep (se 2 (by rfl) ⟨430656, by rfl⟩ : syracuseStep 1148417 = 861313) B861313
theorem B3639127 : Blo 223812 3639127 := bstep (se 1 (by rfl) ⟨2729345, by rfl⟩ : syracuseStep 3639127 = 5458691) B5458691
theorem B2689645 : Blo 223812 2689645 := bstep (se 3 (by rfl) ⟨504308, by rfl⟩ : syracuseStep 2689645 = 1008617) B1008617
theorem B756863 : Blo 223812 756863 := bstep (se 1 (by rfl) ⟨567647, by rfl⟩ : syracuseStep 756863 = 1135295) B1135295
theorem B921851 : Blo 223812 921851 := bstep (se 1 (by rfl) ⟨691388, by rfl⟩ : syracuseStep 921851 = 1382777) B1382777
theorem B2593781 : Blo 223812 2593781 := bstep (se 5 (by rfl) ⟨121583, by rfl⟩ : syracuseStep 2593781 = 243167) B243167
theorem B2561705 : Blo 223812 2561705 := bstep (se 2 (by rfl) ⟨960639, by rfl⟩ : syracuseStep 2561705 = 1921279) B1921279
theorem B1153115 : Blo 223812 1153115 := bstep (se 1 (by rfl) ⟨864836, by rfl⟩ : syracuseStep 1153115 = 1729673) B1729673
theorem B335903 : Blo 223812 335903 := bstep (se 1 (by rfl) ⟨251927, by rfl⟩ : syracuseStep 335903 = 503855) B503855
theorem B336431 : Blo 223812 336431 := bstep (se 1 (by rfl) ⟨252323, by rfl⟩ : syracuseStep 336431 = 504647) B504647
theorem B336635 : Blo 223812 336635 := bstep (se 1 (by rfl) ⟨252476, by rfl⟩ : syracuseStep 336635 = 504953) B504953
theorem B762911 : Blo 223812 762911 := bstep (se 1 (by rfl) ⟨572183, by rfl⟩ : syracuseStep 762911 = 1144367) B1144367
theorem B245146799 : Blo 223812 245146799 := bstep (se 1 (by rfl) ⟨183860099, by rfl⟩ : syracuseStep 245146799 = 367720199) B367720199
theorem B2762041 : Blo 223812 2762041 := bstep (se 2 (by rfl) ⟨1035765, by rfl⟩ : syracuseStep 2762041 = 2071531) B2071531
theorem B861799 : Blo 223812 861799 := bstep (se 1 (by rfl) ⟨646349, by rfl⟩ : syracuseStep 861799 = 1292699) B1292699
theorem B1943149 : Blo 223812 1943149 := bstep (se 3 (by rfl) ⟨364340, by rfl⟩ : syracuseStep 1943149 = 728681) B728681
theorem B2566079 : Blo 223812 2566079 := bstep (se 1 (by rfl) ⟨1924559, by rfl⟩ : syracuseStep 2566079 = 3849119) B3849119
theorem B338297 : Blo 223812 338297 := bstep (se 2 (by rfl) ⟨126861, by rfl⟩ : syracuseStep 338297 = 253723) B253723
theorem B339503 : Blo 223812 339503 := bstep (se 1 (by rfl) ⟨254627, by rfl⟩ : syracuseStep 339503 = 509255) B509255
theorem B37695131 : Blo 223812 37695131 := bstep (se 1 (by rfl) ⟨28271348, by rfl⟩ : syracuseStep 37695131 = 56542697) B56542697
theorem B503783 : Blo 223812 503783 := bstep (se 1 (by rfl) ⟨377837, by rfl⟩ : syracuseStep 503783 = 755675) B755675
theorem B372827 : Blo 223812 372827 := bstep (se 1 (by rfl) ⟨279620, by rfl⟩ : syracuseStep 372827 = 559241) B559241
theorem B570523 : Blo 223812 570523 := bstep (se 1 (by rfl) ⟨427892, by rfl⟩ : syracuseStep 570523 = 855785) B855785
theorem B767447 : Blo 223812 767447 := bstep (se 1 (by rfl) ⟨575585, by rfl⟩ : syracuseStep 767447 = 1151171) B1151171
theorem B440495 : Blo 223812 440495 := bstep (se 1 (by rfl) ⟨330371, by rfl⟩ : syracuseStep 440495 = 660743) B660743
theorem B571931 : Blo 223812 571931 := bstep (se 1 (by rfl) ⟨428948, by rfl⟩ : syracuseStep 571931 = 857897) B857897
theorem B1457261 : Blo 223812 1457261 := bstep (se 3 (by rfl) ⟨273236, by rfl⟩ : syracuseStep 1457261 = 546473) B546473
theorem B508841 : Blo 223812 508841 := bstep (se 2 (by rfl) ⟨190815, by rfl⟩ : syracuseStep 508841 = 381631) B381631
theorem B377993 : Blo 223812 377993 := bstep (se 2 (by rfl) ⟨141747, by rfl⟩ : syracuseStep 377993 = 283495) B283495
theorem B378607 : Blo 223812 378607 := bstep (se 1 (by rfl) ⟨283955, by rfl⟩ : syracuseStep 378607 = 567911) B567911
theorem B22136813 : Blo 223812 22136813 := bstep (se 3 (by rfl) ⟨4150652, by rfl⟩ : syracuseStep 22136813 = 8301305) B8301305
theorem B969661 : Blo 223812 969661 := bstep (se 3 (by rfl) ⟨181811, by rfl⟩ : syracuseStep 969661 = 363623) B363623
theorem B969833 : Blo 223812 969833 := bstep (se 2 (by rfl) ⟨363687, by rfl⟩ : syracuseStep 969833 = 727375) B727375
theorem B380207 : Blo 223812 380207 := bstep (se 1 (by rfl) ⟨285155, by rfl⟩ : syracuseStep 380207 = 570311) B570311
theorem B643241 : Blo 223812 643241 := bstep (se 2 (by rfl) ⟨241215, by rfl⟩ : syracuseStep 643241 = 482431) B482431
theorem B512191 : Blo 223812 512191 := bstep (se 1 (by rfl) ⟨384143, by rfl⟩ : syracuseStep 512191 = 768287) B768287
theorem B382043 : Blo 223812 382043 := bstep (se 1 (by rfl) ⟨286532, by rfl⟩ : syracuseStep 382043 = 573065) B573065
theorem B2577743 : Blo 223812 2577743 := bstep (se 1 (by rfl) ⟨1933307, by rfl⟩ : syracuseStep 2577743 = 3866615) B3866615
theorem B1136105 : Blo 223812 1136105 := bstep (se 2 (by rfl) ⟨426039, by rfl⟩ : syracuseStep 1136105 = 852079) B852079
theorem B972395 : Blo 223812 972395 := bstep (se 1 (by rfl) ⟨729296, by rfl⟩ : syracuseStep 972395 = 1458593) B1458593
theorem B2152601 : Blo 223812 2152601 := bstep (se 2 (by rfl) ⟨807225, by rfl⟩ : syracuseStep 2152601 = 1614451) B1614451
theorem B645371 : Blo 223812 645371 := bstep (se 1 (by rfl) ⟨484028, by rfl⟩ : syracuseStep 645371 = 968057) B968057
theorem B1137887 : Blo 223812 1137887 := bstep (se 1 (by rfl) ⟨853415, by rfl⟩ : syracuseStep 1137887 = 1706831) B1706831
theorem B253183 : Blo 223812 253183 := bstep (se 1 (by rfl) ⟨189887, by rfl⟩ : syracuseStep 253183 = 379775) B379775
theorem B22044959 : Blo 223812 22044959 := bstep (se 1 (by rfl) ⟨16533719, by rfl⟩ : syracuseStep 22044959 = 33067439) B33067439
theorem B483823 : Blo 223812 483823 := bstep (se 1 (by rfl) ⟨362867, by rfl⟩ : syracuseStep 483823 = 725735) B725735
theorem B648287 : Blo 223812 648287 := bstep (se 1 (by rfl) ⟨486215, by rfl⟩ : syracuseStep 648287 = 972431) B972431
theorem B1828127 : Blo 223812 1828127 := bstep (se 1 (by rfl) ⟨1371095, by rfl⟩ : syracuseStep 1828127 = 2742191) B2742191
theorem B255487 : Blo 223812 255487 := bstep (se 1 (by rfl) ⟨191615, by rfl⟩ : syracuseStep 255487 = 383231) B383231
theorem B321193 : Blo 223812 321193 := bstep (se 2 (by rfl) ⟨120447, by rfl⟩ : syracuseStep 321193 = 240895) B240895
theorem B255847 : Blo 223812 255847 := bstep (se 1 (by rfl) ⟨191885, by rfl⟩ : syracuseStep 255847 = 383771) B383771
theorem B1828777 : Blo 223812 1828777 := bstep (se 2 (by rfl) ⟨685791, by rfl⟩ : syracuseStep 1828777 = 1371583) B1371583
theorem B256063 : Blo 223812 256063 := bstep (se 1 (by rfl) ⟨192047, by rfl⟩ : syracuseStep 256063 = 384095) B384095
theorem B649399 : Blo 223812 649399 := bstep (se 1 (by rfl) ⟨487049, by rfl⟩ : syracuseStep 649399 = 974099) B974099
theorem B322651 : Blo 223812 322651 := bstep (se 1 (by rfl) ⟨241988, by rfl⟩ : syracuseStep 322651 = 483977) B483977
theorem B1076449 : Blo 223812 1076449 := bstep (se 2 (by rfl) ⟨403668, by rfl⟩ : syracuseStep 1076449 = 807337) B807337
theorem B225007 : Blo 223812 225007 := bstep (se 1 (by rfl) ⟨168755, by rfl⟩ : syracuseStep 225007 = 337511) B337511
theorem B651199 : Blo 223812 651199 := bstep (se 1 (by rfl) ⟨488399, by rfl⟩ : syracuseStep 651199 = 976799) B976799
theorem B226023 : Blo 223812 226023 := bstep (se 1 (by rfl) ⟨169517, by rfl⟩ : syracuseStep 226023 = 339035) B339035
theorem B1144043 : Blo 223812 1144043 := bstep (se 1 (by rfl) ⟨858032, by rfl⟩ : syracuseStep 1144043 = 1716065) B1716065
theorem B1930985 : Blo 223812 1930985 := bstep (se 2 (by rfl) ⟨724119, by rfl⟩ : syracuseStep 1930985 = 1448239) B1448239
theorem B42137333 : Blo 223812 42137333 := bstep (se 5 (by rfl) ⟨1975187, by rfl⟩ : syracuseStep 42137333 = 3950375) B3950375
theorem B227327 : Blo 223812 227327 := bstep (se 1 (by rfl) ⟨170495, by rfl⟩ : syracuseStep 227327 = 340991) B340991
theorem B227739 : Blo 223812 227739 := bstep (se 1 (by rfl) ⟨170804, by rfl⟩ : syracuseStep 227739 = 341609) B341609
theorem B1149065 : Blo 223812 1149065 := bstep (se 2 (by rfl) ⟨430899, by rfl⟩ : syracuseStep 1149065 = 861799) B861799
theorem B2590865 : Blo 223812 2590865 := bstep (se 2 (by rfl) ⟨971574, by rfl⟩ : syracuseStep 2590865 = 1943149) B1943149
theorem B428257 : Blo 223812 428257 := bstep (se 2 (by rfl) ⟨160596, by rfl⟩ : syracuseStep 428257 = 321193) B321193
theorem B4852169 : Blo 223812 4852169 := bstep (se 2 (by rfl) ⟨1819563, by rfl⟩ : syracuseStep 4852169 = 3639127) B3639127
theorem B428827 : Blo 223812 428827 := bstep (se 1 (by rfl) ⟨321620, by rfl⟩ : syracuseStep 428827 = 643241) B643241
theorem B757403 : Blo 223812 757403 := bstep (se 1 (by rfl) ⟨568052, by rfl⟩ : syracuseStep 757403 = 1136105) B1136105
theorem B1707803 : Blo 223812 1707803 := bstep (se 1 (by rfl) ⟨1280852, by rfl⟩ : syracuseStep 1707803 = 2561705) B2561705
theorem B430201 : Blo 223812 430201 := bstep (se 2 (by rfl) ⟨161325, by rfl⟩ : syracuseStep 430201 = 322651) B322651
theorem B430247 : Blo 223812 430247 := bstep (se 1 (by rfl) ⟨322685, by rfl⟩ : syracuseStep 430247 = 645371) B645371
theorem B758591 : Blo 223812 758591 := bstep (se 1 (by rfl) ⟨568943, by rfl⟩ : syracuseStep 758591 = 1137887) B1137887
theorem B432191 : Blo 223812 432191 := bstep (se 1 (by rfl) ⟨324143, by rfl⟩ : syracuseStep 432191 = 648287) B648287
theorem B1710719 : Blo 223812 1710719 := bstep (se 1 (by rfl) ⟨1283039, by rfl⟩ : syracuseStep 1710719 = 2566079) B2566079
theorem B760697 : Blo 223812 760697 := bstep (se 2 (by rfl) ⟨285261, by rfl⟩ : syracuseStep 760697 = 570523) B570523
theorem B335855 : Blo 223812 335855 := bstep (se 1 (by rfl) ⟨251891, by rfl⟩ : syracuseStep 335855 = 503783) B503783
theorem B762695 : Blo 223812 762695 := bstep (se 1 (by rfl) ⟨572021, by rfl⟩ : syracuseStep 762695 = 1144043) B1144043
theorem B1287323 : Blo 223812 1287323 := bstep (se 1 (by rfl) ⟨965492, by rfl⟩ : syracuseStep 1287323 = 1930985) B1930985
theorem B28091555 : Blo 223812 28091555 := bstep (se 1 (by rfl) ⟨21068666, by rfl⟩ : syracuseStep 28091555 = 42137333) B42137333
theorem B337577 : Blo 223812 337577 := bstep (se 2 (by rfl) ⟨126591, by rfl⟩ : syracuseStep 337577 = 253183) B253183
theorem B26258455 : Blo 223812 26258455 := bstep (se 1 (by rfl) ⟨19693841, by rfl⟩ : syracuseStep 26258455 = 39387683) B39387683
theorem B339227 : Blo 223812 339227 := bstep (se 1 (by rfl) ⟨254420, by rfl⟩ : syracuseStep 339227 = 508841) B508841
theorem B765611 : Blo 223812 765611 := bstep (se 1 (by rfl) ⟨574208, by rfl⟩ : syracuseStep 765611 = 1148417) B1148417
theorem B14757875 : Blo 223812 14757875 := bstep (se 1 (by rfl) ⟨11068406, by rfl⟩ : syracuseStep 14757875 = 22136813) B22136813
theorem B3682721 : Blo 223812 3682721 := bstep (se 2 (by rfl) ⟨1381020, by rfl⟩ : syracuseStep 3682721 = 2762041) B2762041
theorem B340649 : Blo 223812 340649 := bstep (se 2 (by rfl) ⟨127743, by rfl⟩ : syracuseStep 340649 = 255487) B255487
theorem B504575 : Blo 223812 504575 := bstep (se 1 (by rfl) ⟨378431, by rfl⟩ : syracuseStep 504575 = 756863) B756863
theorem B504809 : Blo 223812 504809 := bstep (se 2 (by rfl) ⟨189303, by rfl⟩ : syracuseStep 504809 = 378607) B378607
theorem B341129 : Blo 223812 341129 := bstep (se 2 (by rfl) ⟨127923, by rfl⟩ : syracuseStep 341129 = 255847) B255847
theorem B2438369 : Blo 223812 2438369 := bstep (se 2 (by rfl) ⟨914388, by rfl⟩ : syracuseStep 2438369 = 1828777) B1828777
theorem B341417 : Blo 223812 341417 := bstep (se 2 (by rfl) ⟨128031, by rfl⟩ : syracuseStep 341417 = 256063) B256063
theorem B865865 : Blo 223812 865865 := bstep (se 2 (by rfl) ⟨324699, by rfl⟩ : syracuseStep 865865 = 649399) B649399
theorem B3586193 : Blo 223812 3586193 := bstep (se 2 (by rfl) ⟨1344822, by rfl⟩ : syracuseStep 3586193 = 2689645) B2689645
theorem B1718495 : Blo 223812 1718495 := bstep (se 1 (by rfl) ⟨1288871, by rfl⟩ : syracuseStep 1718495 = 2577743) B2577743
theorem B1292881 : Blo 223812 1292881 := bstep (se 2 (by rfl) ⟨484830, by rfl⟩ : syracuseStep 1292881 = 969661) B969661
theorem B768743 : Blo 223812 768743 := bstep (se 1 (by rfl) ⟨576557, by rfl⟩ : syracuseStep 768743 = 1153115) B1153115
theorem B868265 : Blo 223812 868265 := bstep (se 2 (by rfl) ⟨325599, by rfl⟩ : syracuseStep 868265 = 651199) B651199
theorem B14696639 : Blo 223812 14696639 := bstep (se 1 (by rfl) ⟨11022479, by rfl⟩ : syracuseStep 14696639 = 22044959) B22044959
theorem B508607 : Blo 223812 508607 := bstep (se 1 (by rfl) ⟨381455, by rfl⟩ : syracuseStep 508607 = 762911) B762911
theorem B163431199 : Blo 223812 163431199 := bstep (se 1 (by rfl) ⟨122573399, by rfl⟩ : syracuseStep 163431199 = 245146799) B245146799
theorem B248551 : Blo 223812 248551 := bstep (se 1 (by rfl) ⟨186413, by rfl⟩ : syracuseStep 248551 = 372827) B372827
theorem B511631 : Blo 223812 511631 := bstep (se 1 (by rfl) ⟨383723, by rfl⟩ : syracuseStep 511631 = 767447) B767447
theorem B381287 : Blo 223812 381287 := bstep (se 1 (by rfl) ⟨285965, by rfl⟩ : syracuseStep 381287 = 571931) B571931
theorem B971507 : Blo 223812 971507 := bstep (se 1 (by rfl) ⟨728630, by rfl⟩ : syracuseStep 971507 = 1457261) B1457261
theorem B645097 : Blo 223812 645097 := bstep (se 2 (by rfl) ⟨241911, by rfl⟩ : syracuseStep 645097 = 483823) B483823
theorem B11032595 : Blo 223812 11032595 := bstep (se 1 (by rfl) ⟨8274446, by rfl⟩ : syracuseStep 11032595 = 16548893) B16548893
theorem B251995 : Blo 223812 251995 := bstep (se 1 (by rfl) ⟨188996, by rfl⟩ : syracuseStep 251995 = 377993) B377993
theorem B1923263 : Blo 223812 1923263 := bstep (se 1 (by rfl) ⟨1442447, by rfl⟩ : syracuseStep 1923263 = 2884895) B2884895
theorem B482473 : Blo 223812 482473 := bstep (se 2 (by rfl) ⟨180927, by rfl⟩ : syracuseStep 482473 = 361855) B361855
theorem B646555 : Blo 223812 646555 := bstep (se 1 (by rfl) ⟨484916, by rfl⟩ : syracuseStep 646555 = 969833) B969833
theorem B253471 : Blo 223812 253471 := bstep (se 1 (by rfl) ⟨190103, by rfl⟩ : syracuseStep 253471 = 380207) B380207
theorem B614567 : Blo 223812 614567 := bstep (se 1 (by rfl) ⟨460925, by rfl⟩ : syracuseStep 614567 = 921851) B921851
theorem B1729187 : Blo 223812 1729187 := bstep (se 1 (by rfl) ⟨1296890, by rfl⟩ : syracuseStep 1729187 = 2593781) B2593781
theorem B254695 : Blo 223812 254695 := bstep (se 1 (by rfl) ⟨191021, by rfl⟩ : syracuseStep 254695 = 382043) B382043
theorem B4875005 : Blo 223812 4875005 := bstep (se 3 (by rfl) ⟨914063, by rfl⟩ : syracuseStep 4875005 = 1828127) B1828127
theorem B648263 : Blo 223812 648263 := bstep (se 1 (by rfl) ⟨486197, by rfl⟩ : syracuseStep 648263 = 972395) B972395
theorem B1435067 : Blo 223812 1435067 := bstep (se 1 (by rfl) ⟨1076300, by rfl⟩ : syracuseStep 1435067 = 2152601) B2152601
theorem B1435265 : Blo 223812 1435265 := bstep (se 2 (by rfl) ⟨538224, by rfl⟩ : syracuseStep 1435265 = 1076449) B1076449
theorem B223935 : Blo 223812 223935 := bstep (se 1 (by rfl) ⟨167951, by rfl⟩ : syracuseStep 223935 = 335903) B335903
theorem B682921 : Blo 223812 682921 := bstep (se 2 (by rfl) ⟨256095, by rfl⟩ : syracuseStep 682921 = 512191) B512191
theorem B224287 : Blo 223812 224287 := bstep (se 1 (by rfl) ⟨168215, by rfl⟩ : syracuseStep 224287 = 336431) B336431
theorem B224423 : Blo 223812 224423 := bstep (se 1 (by rfl) ⟨168317, by rfl⟩ : syracuseStep 224423 = 336635) B336635
theorem B225531 : Blo 223812 225531 := bstep (se 1 (by rfl) ⟨169148, by rfl⟩ : syracuseStep 225531 = 338297) B338297
theorem B226335 : Blo 223812 226335 := bstep (se 1 (by rfl) ⟨169751, by rfl⟩ : syracuseStep 226335 = 339503) B339503
theorem B25130087 : Blo 223812 25130087 := bstep (se 1 (by rfl) ⟨18847565, by rfl⟩ : syracuseStep 25130087 = 37695131) B37695131
theorem B293663 : Blo 223812 293663 := bstep (se 1 (by rfl) ⟨220247, by rfl⟩ : syracuseStep 293663 = 440495) B440495
theorem B9797759 : Blo 223812 9797759 := bstep (se 1 (by rfl) ⟨7348319, by rfl⟩ : syracuseStep 9797759 = 14696639) B14696639
theorem B217908265 : Blo 223812 217908265 := bstep (se 2 (by rfl) ⟨81715599, by rfl⟩ : syracuseStep 217908265 = 163431199) B163431199
theorem B1282175 : Blo 223812 1282175 := bstep (se 1 (by rfl) ⟨961631, by rfl⟩ : syracuseStep 1282175 = 1923263) B1923263
theorem B3642245 : Blo 223812 3642245 := bstep (se 4 (by rfl) ⟨341460, by rfl⟩ : syracuseStep 3642245 = 682921) B682921
theorem B1152791 : Blo 223812 1152791 := bstep (se 1 (by rfl) ⟨864593, by rfl⟩ : syracuseStep 1152791 = 1729187) B1729187
theorem B3250003 : Blo 223812 3250003 := bstep (se 1 (by rfl) ⟨2437502, by rfl⟩ : syracuseStep 3250003 = 4875005) B4875005
theorem B858215 : Blo 223812 858215 := bstep (se 1 (by rfl) ⟨643661, by rfl⟩ : syracuseStep 858215 = 1287323) B1287323
theorem B956711 : Blo 223812 956711 := bstep (se 1 (by rfl) ⟨717533, by rfl⟩ : syracuseStep 956711 = 1435067) B1435067
theorem B956843 : Blo 223812 956843 := bstep (se 1 (by rfl) ⟨717632, by rfl⟩ : syracuseStep 956843 = 1435265) B1435265
theorem B860129 : Blo 223812 860129 := bstep (se 2 (by rfl) ⟨322548, by rfl⟩ : syracuseStep 860129 = 645097) B645097
theorem B9838583 : Blo 223812 9838583 := bstep (se 1 (by rfl) ⟨7378937, by rfl⟩ : syracuseStep 9838583 = 14757875) B14757875
theorem B335993 : Blo 223812 335993 := bstep (se 2 (by rfl) ⟨125997, by rfl⟩ : syracuseStep 335993 = 251995) B251995
theorem B336383 : Blo 223812 336383 := bstep (se 1 (by rfl) ⟨252287, by rfl⟩ : syracuseStep 336383 = 504575) B504575
theorem B336539 : Blo 223812 336539 := bstep (se 1 (by rfl) ⟨252404, by rfl⟩ : syracuseStep 336539 = 504809) B504809
theorem B16753391 : Blo 223812 16753391 := bstep (se 1 (by rfl) ⟨12565043, by rfl⟩ : syracuseStep 16753391 = 25130087) B25130087
theorem B862073 : Blo 223812 862073 := bstep (se 2 (by rfl) ⟨323277, by rfl⟩ : syracuseStep 862073 = 646555) B646555
theorem B337961 : Blo 223812 337961 := bstep (se 2 (by rfl) ⟨126735, by rfl⟩ : syracuseStep 337961 = 253471) B253471
theorem B339071 : Blo 223812 339071 := bstep (se 1 (by rfl) ⟨254303, by rfl⟩ : syracuseStep 339071 = 508607) B508607
theorem B339593 : Blo 223812 339593 := bstep (se 2 (by rfl) ⟨127347, by rfl⟩ : syracuseStep 339593 = 254695) B254695
theorem B766043 : Blo 223812 766043 := bstep (se 1 (by rfl) ⟨574532, by rfl⟩ : syracuseStep 766043 = 1149065) B1149065
theorem B341087 : Blo 223812 341087 := bstep (se 1 (by rfl) ⟨255815, by rfl⟩ : syracuseStep 341087 = 511631) B511631
theorem B504935 : Blo 223812 504935 := bstep (se 1 (by rfl) ⟨378701, by rfl⟩ : syracuseStep 504935 = 757403) B757403
theorem B571009 : Blo 223812 571009 := bstep (se 2 (by rfl) ⟨214128, by rfl⟩ : syracuseStep 571009 = 428257) B428257
theorem B505727 : Blo 223812 505727 := bstep (se 1 (by rfl) ⟨379295, by rfl⟩ : syracuseStep 505727 = 758591) B758591
theorem B571769 : Blo 223812 571769 := bstep (se 2 (by rfl) ⟨214413, by rfl⟩ : syracuseStep 571769 = 428827) B428827
theorem B1325605 : Blo 223812 1325605 := bstep (se 4 (by rfl) ⟨124275, by rfl⟩ : syracuseStep 1325605 = 248551) B248551
theorem B7355063 : Blo 223812 7355063 := bstep (se 1 (by rfl) ⟨5516297, by rfl⟩ : syracuseStep 7355063 = 11032595) B11032595
theorem B35011273 : Blo 223812 35011273 := bstep (se 2 (by rfl) ⟨13129227, by rfl⟩ : syracuseStep 35011273 = 26258455) B26258455
theorem B507131 : Blo 223812 507131 := bstep (se 1 (by rfl) ⟨380348, by rfl⟩ : syracuseStep 507131 = 760697) B760697
theorem B409711 : Blo 223812 409711 := bstep (se 1 (by rfl) ⟨307283, by rfl⟩ : syracuseStep 409711 = 614567) B614567
theorem B573601 : Blo 223812 573601 := bstep (se 2 (by rfl) ⟨215100, by rfl⟩ : syracuseStep 573601 = 430201) B430201
theorem B508463 : Blo 223812 508463 := bstep (se 1 (by rfl) ⟨381347, by rfl⟩ : syracuseStep 508463 = 762695) B762695
theorem B18727703 : Blo 223812 18727703 := bstep (se 1 (by rfl) ⟨14045777, by rfl⟩ : syracuseStep 18727703 = 28091555) B28091555
theorem B510407 : Blo 223812 510407 := bstep (se 1 (by rfl) ⟨382805, by rfl⟩ : syracuseStep 510407 = 765611) B765611
theorem B1723841 : Blo 223812 1723841 := bstep (se 2 (by rfl) ⟨646440, by rfl⟩ : syracuseStep 1723841 = 1292881) B1292881
theorem B1625579 : Blo 223812 1625579 := bstep (se 1 (by rfl) ⟨1219184, by rfl⟩ : syracuseStep 1625579 = 2438369) B2438369
theorem B577243 : Blo 223812 577243 := bstep (se 1 (by rfl) ⟨432932, by rfl⟩ : syracuseStep 577243 = 865865) B865865
theorem B643297 : Blo 223812 643297 := bstep (se 2 (by rfl) ⟨241236, by rfl⟩ : syracuseStep 643297 = 482473) B482473
theorem B512495 : Blo 223812 512495 := bstep (se 1 (by rfl) ⟨384371, by rfl⟩ : syracuseStep 512495 = 768743) B768743
theorem B578843 : Blo 223812 578843 := bstep (se 1 (by rfl) ⟨434132, by rfl⟩ : syracuseStep 578843 = 868265) B868265
theorem B1727243 : Blo 223812 1727243 := bstep (se 1 (by rfl) ⟨1295432, by rfl⟩ : syracuseStep 1727243 = 2590865) B2590865
theorem B3234779 : Blo 223812 3234779 := bstep (se 1 (by rfl) ⟨2426084, by rfl⟩ : syracuseStep 3234779 = 4852169) B4852169
theorem B1138535 : Blo 223812 1138535 := bstep (se 1 (by rfl) ⟨853901, by rfl⟩ : syracuseStep 1138535 = 1707803) B1707803
theorem B286831 : Blo 223812 286831 := bstep (se 1 (by rfl) ⟨215123, by rfl⟩ : syracuseStep 286831 = 430247) B430247
theorem B1728701 : Blo 223812 1728701 := bstep (se 3 (by rfl) ⟨324131, by rfl⟩ : syracuseStep 1728701 = 648263) B648263
theorem B254191 : Blo 223812 254191 := bstep (se 1 (by rfl) ⟨190643, by rfl⟩ : syracuseStep 254191 = 381287) B381287
theorem B647671 : Blo 223812 647671 := bstep (se 1 (by rfl) ⟨485753, by rfl⟩ : syracuseStep 647671 = 971507) B971507
theorem B288127 : Blo 223812 288127 := bstep (se 1 (by rfl) ⟨216095, by rfl⟩ : syracuseStep 288127 = 432191) B432191
theorem B1140479 : Blo 223812 1140479 := bstep (se 1 (by rfl) ⟨855359, by rfl⟩ : syracuseStep 1140479 = 1710719) B1710719
theorem B223903 : Blo 223812 223903 := bstep (se 1 (by rfl) ⟨167927, by rfl⟩ : syracuseStep 223903 = 335855) B335855
theorem B225051 : Blo 223812 225051 := bstep (se 1 (by rfl) ⟨168788, by rfl⟩ : syracuseStep 225051 = 337577) B337577
theorem B783101 : Blo 223812 783101 := bstep (se 3 (by rfl) ⟨146831, by rfl⟩ : syracuseStep 783101 = 293663) B293663
theorem B226151 : Blo 223812 226151 := bstep (se 1 (by rfl) ⟨169613, by rfl⟩ : syracuseStep 226151 = 339227) B339227
theorem B2455147 : Blo 223812 2455147 := bstep (se 1 (by rfl) ⟨1841360, by rfl⟩ : syracuseStep 2455147 = 3682721) B3682721
theorem B227099 : Blo 223812 227099 := bstep (se 1 (by rfl) ⟨170324, by rfl⟩ : syracuseStep 227099 = 340649) B340649
theorem B227419 : Blo 223812 227419 := bstep (se 1 (by rfl) ⟨170564, by rfl⟩ : syracuseStep 227419 = 341129) B341129
theorem B227611 : Blo 223812 227611 := bstep (se 1 (by rfl) ⟨170708, by rfl⟩ : syracuseStep 227611 = 341417) B341417
theorem B2390795 : Blo 223812 2390795 := bstep (se 1 (by rfl) ⟨1793096, by rfl⟩ : syracuseStep 2390795 = 3586193) B3586193
theorem B1145663 : Blo 223812 1145663 := bstep (se 1 (by rfl) ⟨859247, by rfl⟩ : syracuseStep 1145663 = 1718495) B1718495
theorem B12485135 : Blo 223812 12485135 := bstep (se 1 (by rfl) ⟨9363851, by rfl⟩ : syracuseStep 12485135 = 18727703) B18727703
theorem B1149227 : Blo 223812 1149227 := bstep (se 1 (by rfl) ⟨861920, by rfl⟩ : syracuseStep 1149227 = 1723841) B1723841
theorem B1083719 : Blo 223812 1083719 := bstep (se 1 (by rfl) ⟨812789, by rfl⟩ : syracuseStep 1083719 = 1625579) B1625579
theorem B854783 : Blo 223812 854783 := bstep (se 1 (by rfl) ⟨641087, by rfl⟩ : syracuseStep 854783 = 1282175) B1282175
theorem B2428163 : Blo 223812 2428163 := bstep (se 1 (by rfl) ⟨1821122, by rfl⟩ : syracuseStep 2428163 = 3642245) B3642245
theorem B1151495 : Blo 223812 1151495 := bstep (se 1 (by rfl) ⟨863621, by rfl⟩ : syracuseStep 1151495 = 1727243) B1727243
theorem B759023 : Blo 223812 759023 := bstep (se 1 (by rfl) ⟨569267, by rfl⟩ : syracuseStep 759023 = 1138535) B1138535
theorem B6559055 : Blo 223812 6559055 := bstep (se 1 (by rfl) ⟨4919291, by rfl⟩ : syracuseStep 6559055 = 9838583) B9838583
theorem B1152467 : Blo 223812 1152467 := bstep (se 1 (by rfl) ⟨864350, by rfl⟩ : syracuseStep 1152467 = 1728701) B1728701
theorem B857729 : Blo 223812 857729 := bstep (se 2 (by rfl) ⟨321648, by rfl⟩ : syracuseStep 857729 = 643297) B643297
theorem B760319 : Blo 223812 760319 := bstep (se 1 (by rfl) ⟨570239, by rfl⟩ : syracuseStep 760319 = 1140479) B1140479
theorem B761345 : Blo 223812 761345 := bstep (se 2 (by rfl) ⟨285504, by rfl⟩ : syracuseStep 761345 = 571009) B571009
theorem B4333337 : Blo 223812 4333337 := bstep (se 2 (by rfl) ⟨1625001, by rfl⟩ : syracuseStep 4333337 = 3250003) B3250003
theorem B336623 : Blo 223812 336623 := bstep (se 1 (by rfl) ⟨252467, by rfl⟩ : syracuseStep 336623 = 504935) B504935
theorem B337151 : Blo 223812 337151 := bstep (se 1 (by rfl) ⟨252863, by rfl⟩ : syracuseStep 337151 = 505727) B505727
theorem B763775 : Blo 223812 763775 := bstep (se 1 (by rfl) ⟨572831, by rfl⟩ : syracuseStep 763775 = 1145663) B1145663
theorem B338087 : Blo 223812 338087 := bstep (se 1 (by rfl) ⟨253565, by rfl⟩ : syracuseStep 338087 = 507131) B507131
theorem B6531839 : Blo 223812 6531839 := bstep (se 1 (by rfl) ⟨4898879, by rfl⟩ : syracuseStep 6531839 = 9797759) B9797759
theorem B764801 : Blo 223812 764801 := bstep (se 2 (by rfl) ⟨286800, by rfl⟩ : syracuseStep 764801 = 573601) B573601
theorem B338921 : Blo 223812 338921 := bstep (se 2 (by rfl) ⟨127095, by rfl⟩ : syracuseStep 338921 = 254191) B254191
theorem B338975 : Blo 223812 338975 := bstep (se 1 (by rfl) ⟨254231, by rfl⟩ : syracuseStep 338975 = 508463) B508463
theorem B863561 : Blo 223812 863561 := bstep (se 2 (by rfl) ⟨323835, by rfl⟩ : syracuseStep 863561 = 647671) B647671
theorem B340271 : Blo 223812 340271 := bstep (se 1 (by rfl) ⟨255203, by rfl⟩ : syracuseStep 340271 = 510407) B510407
theorem B341663 : Blo 223812 341663 := bstep (se 1 (by rfl) ⟨256247, by rfl⟩ : syracuseStep 341663 = 512495) B512495
theorem B768527 : Blo 223812 768527 := bstep (se 1 (by rfl) ⟨576395, by rfl⟩ : syracuseStep 768527 = 1152791) B1152791
theorem B572143 : Blo 223812 572143 := bstep (se 1 (by rfl) ⟨429107, by rfl⟩ : syracuseStep 572143 = 858215) B858215
theorem B637807 : Blo 223812 637807 := bstep (se 1 (by rfl) ⟨478355, by rfl⟩ : syracuseStep 637807 = 956711) B956711
theorem B637895 : Blo 223812 637895 := bstep (se 1 (by rfl) ⟨478421, by rfl⟩ : syracuseStep 637895 = 956843) B956843
theorem B769657 : Blo 223812 769657 := bstep (se 2 (by rfl) ⟨288621, by rfl⟩ : syracuseStep 769657 = 577243) B577243
theorem B573419 : Blo 223812 573419 := bstep (se 1 (by rfl) ⟨430064, by rfl⟩ : syracuseStep 573419 = 860129) B860129
theorem B574715 : Blo 223812 574715 := bstep (se 1 (by rfl) ⟨431036, by rfl⟩ : syracuseStep 574715 = 862073) B862073
theorem B510695 : Blo 223812 510695 := bstep (se 1 (by rfl) ⟨383021, by rfl⟩ : syracuseStep 510695 = 766043) B766043
theorem B46681697 : Blo 223812 46681697 := bstep (se 2 (by rfl) ⟨17505636, by rfl⟩ : syracuseStep 46681697 = 35011273) B35011273
theorem B381179 : Blo 223812 381179 := bstep (se 1 (by rfl) ⟨285884, by rfl⟩ : syracuseStep 381179 = 571769) B571769
theorem B4903375 : Blo 223812 4903375 := bstep (se 1 (by rfl) ⟨3677531, by rfl⟩ : syracuseStep 4903375 = 7355063) B7355063
theorem B1593863 : Blo 223812 1593863 := bstep (se 1 (by rfl) ⟨1195397, by rfl⟩ : syracuseStep 1593863 = 2390795) B2390795
theorem B382441 : Blo 223812 382441 := bstep (se 2 (by rfl) ⟨143415, by rfl⟩ : syracuseStep 382441 = 286831) B286831
theorem B546281 : Blo 223812 546281 := bstep (se 2 (by rfl) ⟨204855, by rfl⟩ : syracuseStep 546281 = 409711) B409711
theorem B290544353 : Blo 223812 290544353 := bstep (se 2 (by rfl) ⟨108954132, by rfl⟩ : syracuseStep 290544353 = 217908265) B217908265
theorem B384169 : Blo 223812 384169 := bstep (se 2 (by rfl) ⟨144063, by rfl⟩ : syracuseStep 384169 = 288127) B288127
theorem B385895 : Blo 223812 385895 := bstep (se 1 (by rfl) ⟨289421, by rfl⟩ : syracuseStep 385895 = 578843) B578843
theorem B2156519 : Blo 223812 2156519 := bstep (se 1 (by rfl) ⟨1617389, by rfl⟩ : syracuseStep 2156519 = 3234779) B3234779
theorem B223995 : Blo 223812 223995 := bstep (se 1 (by rfl) ⟨167996, by rfl⟩ : syracuseStep 223995 = 335993) B335993
theorem B224255 : Blo 223812 224255 := bstep (se 1 (by rfl) ⟨168191, by rfl⟩ : syracuseStep 224255 = 336383) B336383
theorem B224359 : Blo 223812 224359 := bstep (se 1 (by rfl) ⟨168269, by rfl⟩ : syracuseStep 224359 = 336539) B336539
theorem B11168927 : Blo 223812 11168927 := bstep (se 1 (by rfl) ⟨8376695, by rfl⟩ : syracuseStep 11168927 = 16753391) B16753391
theorem B225307 : Blo 223812 225307 := bstep (se 1 (by rfl) ⟨168980, by rfl⟩ : syracuseStep 225307 = 337961) B337961
theorem B226047 : Blo 223812 226047 := bstep (se 1 (by rfl) ⟨169535, by rfl⟩ : syracuseStep 226047 = 339071) B339071
theorem B3273529 : Blo 223812 3273529 := bstep (se 2 (by rfl) ⟨1227573, by rfl⟩ : syracuseStep 3273529 = 2455147) B2455147
theorem B226395 : Blo 223812 226395 := bstep (se 1 (by rfl) ⟨169796, by rfl⟩ : syracuseStep 226395 = 339593) B339593
theorem B522067 : Blo 223812 522067 := bstep (se 1 (by rfl) ⟨391550, by rfl⟩ : syracuseStep 522067 = 783101) B783101
theorem B1767473 : Blo 223812 1767473 := bstep (se 2 (by rfl) ⟨662802, by rfl⟩ : syracuseStep 1767473 = 1325605) B1325605
theorem B227391 : Blo 223812 227391 := bstep (se 1 (by rfl) ⟨170543, by rfl⟩ : syracuseStep 227391 = 341087) B341087
theorem B33293693 : Blo 223812 33293693 := bstep (se 3 (by rfl) ⟨6242567, by rfl⟩ : syracuseStep 33293693 = 12485135) B12485135
theorem B364187 : Blo 223812 364187 := bstep (se 1 (by rfl) ⟨273140, by rfl⟩ : syracuseStep 364187 = 546281) B546281
theorem B193696235 : Blo 223812 193696235 := bstep (se 1 (by rfl) ⟨145272176, by rfl⟩ : syracuseStep 193696235 = 290544353) B290544353
theorem B2888891 : Blo 223812 2888891 := bstep (se 1 (by rfl) ⟨2166668, by rfl⟩ : syracuseStep 2888891 = 4333337) B4333337
theorem B2889917 : Blo 223812 2889917 := bstep (se 3 (by rfl) ⟨541859, by rfl⟩ : syracuseStep 2889917 = 1083719) B1083719
theorem B4364705 : Blo 223812 4364705 := bstep (se 2 (by rfl) ⟨1636764, by rfl⟩ : syracuseStep 4364705 = 3273529) B3273529
theorem B7445951 : Blo 223812 7445951 := bstep (se 1 (by rfl) ⟨5584463, by rfl⟩ : syracuseStep 7445951 = 11168927) B11168927
theorem B696089 : Blo 223812 696089 := bstep (se 2 (by rfl) ⟨261033, by rfl⟩ : syracuseStep 696089 = 522067) B522067
theorem B762857 : Blo 223812 762857 := bstep (se 2 (by rfl) ⟨286071, by rfl⟩ : syracuseStep 762857 = 572143) B572143
theorem B1026209 : Blo 223812 1026209 := bstep (se 2 (by rfl) ⟨384828, by rfl⟩ : syracuseStep 1026209 = 769657) B769657
theorem B766151 : Blo 223812 766151 := bstep (se 1 (by rfl) ⟨574613, by rfl⟩ : syracuseStep 766151 = 1149227) B1149227
theorem B340463 : Blo 223812 340463 := bstep (se 1 (by rfl) ⟨255347, by rfl⟩ : syracuseStep 340463 = 510695) B510695
theorem B569855 : Blo 223812 569855 := bstep (se 1 (by rfl) ⟨427391, by rfl⟩ : syracuseStep 569855 = 854783) B854783
theorem B1618775 : Blo 223812 1618775 := bstep (se 1 (by rfl) ⟨1214081, by rfl⟩ : syracuseStep 1618775 = 2428163) B2428163
theorem B1062575 : Blo 223812 1062575 := bstep (se 1 (by rfl) ⟨796931, by rfl⟩ : syracuseStep 1062575 = 1593863) B1593863
theorem B767663 : Blo 223812 767663 := bstep (se 1 (by rfl) ⟨575747, by rfl⟩ : syracuseStep 767663 = 1151495) B1151495
theorem B506015 : Blo 223812 506015 := bstep (se 1 (by rfl) ⟨379511, by rfl⟩ : syracuseStep 506015 = 759023) B759023
theorem B4372703 : Blo 223812 4372703 := bstep (se 1 (by rfl) ⟨3279527, by rfl⟩ : syracuseStep 4372703 = 6559055) B6559055
theorem B768311 : Blo 223812 768311 := bstep (se 1 (by rfl) ⟨576233, by rfl⟩ : syracuseStep 768311 = 1152467) B1152467
theorem B571819 : Blo 223812 571819 := bstep (se 1 (by rfl) ⟨428864, by rfl⟩ : syracuseStep 571819 = 857729) B857729
theorem B506879 : Blo 223812 506879 := bstep (se 1 (by rfl) ⟨380159, by rfl⟩ : syracuseStep 506879 = 760319) B760319
theorem B507563 : Blo 223812 507563 := bstep (se 1 (by rfl) ⟨380672, by rfl⟩ : syracuseStep 507563 = 761345) B761345
theorem B6537833 : Blo 223812 6537833 := bstep (se 2 (by rfl) ⟨2451687, by rfl⟩ : syracuseStep 6537833 = 4903375) B4903375
theorem B509183 : Blo 223812 509183 := bstep (se 1 (by rfl) ⟨381887, by rfl⟩ : syracuseStep 509183 = 763775) B763775
theorem B509867 : Blo 223812 509867 := bstep (se 1 (by rfl) ⟨382400, by rfl⟩ : syracuseStep 509867 = 764801) B764801
theorem B509921 : Blo 223812 509921 := bstep (se 2 (by rfl) ⟨191220, by rfl⟩ : syracuseStep 509921 = 382441) B382441
theorem B575707 : Blo 223812 575707 := bstep (se 1 (by rfl) ⟨431780, by rfl⟩ : syracuseStep 575707 = 863561) B863561
theorem B512225 : Blo 223812 512225 := bstep (se 2 (by rfl) ⟨192084, by rfl⟩ : syracuseStep 512225 = 384169) B384169
theorem B512351 : Blo 223812 512351 := bstep (se 1 (by rfl) ⟨384263, by rfl⟩ : syracuseStep 512351 = 768527) B768527
theorem B382279 : Blo 223812 382279 := bstep (se 1 (by rfl) ⟨286709, by rfl⟩ : syracuseStep 382279 = 573419) B573419
theorem B383143 : Blo 223812 383143 := bstep (se 1 (by rfl) ⟨287357, by rfl⟩ : syracuseStep 383143 = 574715) B574715
theorem B31121131 : Blo 223812 31121131 := bstep (se 1 (by rfl) ⟨23340848, by rfl⟩ : syracuseStep 31121131 = 46681697) B46681697
theorem B254119 : Blo 223812 254119 := bstep (se 1 (by rfl) ⟨190589, by rfl⟩ : syracuseStep 254119 = 381179) B381179
theorem B224415 : Blo 223812 224415 := bstep (se 1 (by rfl) ⟨168311, by rfl⟩ : syracuseStep 224415 = 336623) B336623
theorem B257263 : Blo 223812 257263 := bstep (se 1 (by rfl) ⟨192947, by rfl⟩ : syracuseStep 257263 = 385895) B385895
theorem B224767 : Blo 223812 224767 := bstep (se 1 (by rfl) ⟨168575, by rfl⟩ : syracuseStep 224767 = 337151) B337151
theorem B1437679 : Blo 223812 1437679 := bstep (se 1 (by rfl) ⟨1078259, by rfl⟩ : syracuseStep 1437679 = 2156519) B2156519
theorem B225391 : Blo 223812 225391 := bstep (se 1 (by rfl) ⟨169043, by rfl⟩ : syracuseStep 225391 = 338087) B338087
theorem B4354559 : Blo 223812 4354559 := bstep (se 1 (by rfl) ⟨3265919, by rfl⟩ : syracuseStep 4354559 = 6531839) B6531839
theorem B225947 : Blo 223812 225947 := bstep (se 1 (by rfl) ⟨169460, by rfl⟩ : syracuseStep 225947 = 338921) B338921
theorem B225983 : Blo 223812 225983 := bstep (se 1 (by rfl) ⟨169487, by rfl⟩ : syracuseStep 225983 = 338975) B338975
theorem B226847 : Blo 223812 226847 := bstep (se 1 (by rfl) ⟨170135, by rfl⟩ : syracuseStep 226847 = 340271) B340271
theorem B227775 : Blo 223812 227775 := bstep (se 1 (by rfl) ⟨170831, by rfl⟩ : syracuseStep 227775 = 341663) B341663
theorem B850409 : Blo 223812 850409 := bstep (se 2 (by rfl) ⟨318903, by rfl⟩ : syracuseStep 850409 = 637807) B637807
theorem B1178315 : Blo 223812 1178315 := bstep (se 1 (by rfl) ⟨883736, by rfl⟩ : syracuseStep 1178315 = 1767473) B1767473
theorem B425263 : Blo 223812 425263 := bstep (se 1 (by rfl) ⟨318947, by rfl⟩ : syracuseStep 425263 = 637895) B637895
theorem B4358555 : Blo 223812 4358555 := bstep (se 1 (by rfl) ⟨3268916, by rfl⟩ : syracuseStep 4358555 = 6537833) B6537833
theorem B464059 : Blo 223812 464059 := bstep (se 1 (by rfl) ⟨348044, by rfl⟩ : syracuseStep 464059 = 696089) B696089
theorem B762425 : Blo 223812 762425 := bstep (se 2 (by rfl) ⟨285909, by rfl⟩ : syracuseStep 762425 = 571819) B571819
theorem B337343 : Blo 223812 337343 := bstep (se 1 (by rfl) ⟨253007, by rfl⟩ : syracuseStep 337343 = 506015) B506015
theorem B566939 : Blo 223812 566939 := bstep (se 1 (by rfl) ⟨425204, by rfl⟩ : syracuseStep 566939 = 850409) B850409
theorem B567017 : Blo 223812 567017 := bstep (se 2 (by rfl) ⟨212631, by rfl⟩ : syracuseStep 567017 = 425263) B425263
theorem B337919 : Blo 223812 337919 := bstep (se 1 (by rfl) ⟨253439, by rfl⟩ : syracuseStep 337919 = 506879) B506879
theorem B41494841 : Blo 223812 41494841 := bstep (se 2 (by rfl) ⟨15560565, by rfl⟩ : syracuseStep 41494841 = 31121131) B31121131
theorem B338375 : Blo 223812 338375 := bstep (se 1 (by rfl) ⟨253781, by rfl⟩ : syracuseStep 338375 = 507563) B507563
theorem B338825 : Blo 223812 338825 := bstep (se 2 (by rfl) ⟨127059, by rfl⟩ : syracuseStep 338825 = 254119) B254119
theorem B339455 : Blo 223812 339455 := bstep (se 1 (by rfl) ⟨254591, by rfl⟩ : syracuseStep 339455 = 509183) B509183
theorem B22195795 : Blo 223812 22195795 := bstep (se 1 (by rfl) ⟨16646846, by rfl⟩ : syracuseStep 22195795 = 33293693) B33293693
theorem B339911 : Blo 223812 339911 := bstep (se 1 (by rfl) ⟨254933, by rfl⟩ : syracuseStep 339911 = 509867) B509867
theorem B339947 : Blo 223812 339947 := bstep (se 1 (by rfl) ⟨254960, by rfl⟩ : syracuseStep 339947 = 509921) B509921
theorem B341483 : Blo 223812 341483 := bstep (se 1 (by rfl) ⟨256112, by rfl⟩ : syracuseStep 341483 = 512225) B512225
theorem B341567 : Blo 223812 341567 := bstep (se 1 (by rfl) ⟨256175, by rfl⟩ : syracuseStep 341567 = 512351) B512351
theorem B767609 : Blo 223812 767609 := bstep (se 2 (by rfl) ⟨287853, by rfl⟩ : syracuseStep 767609 = 575707) B575707
theorem B4963967 : Blo 223812 4963967 := bstep (se 1 (by rfl) ⟨3722975, by rfl⟩ : syracuseStep 4963967 = 7445951) B7445951
theorem B1916905 : Blo 223812 1916905 := bstep (se 2 (by rfl) ⟨718839, by rfl⟩ : syracuseStep 1916905 = 1437679) B1437679
theorem B508571 : Blo 223812 508571 := bstep (se 1 (by rfl) ⟨381428, by rfl⟩ : syracuseStep 508571 = 762857) B762857
theorem B509705 : Blo 223812 509705 := bstep (se 2 (by rfl) ⟨191139, by rfl⟩ : syracuseStep 509705 = 382279) B382279
theorem B510767 : Blo 223812 510767 := bstep (se 1 (by rfl) ⟨383075, by rfl⟩ : syracuseStep 510767 = 766151) B766151
theorem B510857 : Blo 223812 510857 := bstep (se 2 (by rfl) ⟨191571, by rfl⟩ : syracuseStep 510857 = 383143) B383143
theorem B379903 : Blo 223812 379903 := bstep (se 1 (by rfl) ⟨284927, by rfl⟩ : syracuseStep 379903 = 569855) B569855
theorem B2903039 : Blo 223812 2903039 := bstep (se 1 (by rfl) ⟨2177279, by rfl⟩ : syracuseStep 2903039 = 4354559) B4354559
theorem B708383 : Blo 223812 708383 := bstep (se 1 (by rfl) ⟨531287, by rfl⟩ : syracuseStep 708383 = 1062575) B1062575
theorem B511775 : Blo 223812 511775 := bstep (se 1 (by rfl) ⟨383831, by rfl⟩ : syracuseStep 511775 = 767663) B767663
theorem B512207 : Blo 223812 512207 := bstep (se 1 (by rfl) ⟨384155, by rfl⟩ : syracuseStep 512207 = 768311) B768311
theorem B971165 : Blo 223812 971165 := bstep (se 3 (by rfl) ⟨182093, by rfl⟩ : syracuseStep 971165 = 364187) B364187
theorem B129130823 : Blo 223812 129130823 := bstep (se 1 (by rfl) ⟨96848117, by rfl⟩ : syracuseStep 129130823 = 193696235) B193696235
theorem B1925927 : Blo 223812 1925927 := bstep (se 1 (by rfl) ⟨1444445, by rfl⟩ : syracuseStep 1925927 = 2888891) B2888891
theorem B1926611 : Blo 223812 1926611 := bstep (se 1 (by rfl) ⟨1444958, by rfl⟩ : syracuseStep 1926611 = 2889917) B2889917
theorem B2909803 : Blo 223812 2909803 := bstep (se 1 (by rfl) ⟨2182352, by rfl⟩ : syracuseStep 2909803 = 4364705) B4364705
theorem B1372069 : Blo 223812 1372069 := bstep (se 4 (by rfl) ⟨128631, by rfl⟩ : syracuseStep 1372069 = 257263) B257263
theorem B684139 : Blo 223812 684139 := bstep (se 1 (by rfl) ⟨513104, by rfl⟩ : syracuseStep 684139 = 1026209) B1026209
theorem B226975 : Blo 223812 226975 := bstep (se 1 (by rfl) ⟨170231, by rfl⟩ : syracuseStep 226975 = 340463) B340463
theorem B1079183 : Blo 223812 1079183 := bstep (se 1 (by rfl) ⟨809387, by rfl⟩ : syracuseStep 1079183 = 1618775) B1618775
theorem B2915135 : Blo 223812 2915135 := bstep (se 1 (by rfl) ⟨2186351, by rfl⟩ : syracuseStep 2915135 = 4372703) B4372703
theorem B785543 : Blo 223812 785543 := bstep (se 1 (by rfl) ⟨589157, by rfl⟩ : syracuseStep 785543 = 1178315) B1178315
theorem B1935359 : Blo 223812 1935359 := bstep (se 1 (by rfl) ⟨1451519, by rfl⟩ : syracuseStep 1935359 = 2903039) B2903039
theorem B29594393 : Blo 223812 29594393 := bstep (se 2 (by rfl) ⟨11097897, by rfl⟩ : syracuseStep 29594393 = 22195795) B22195795
theorem B86087215 : Blo 223812 86087215 := bstep (se 1 (by rfl) ⟨64565411, by rfl⟩ : syracuseStep 86087215 = 129130823) B129130823
theorem B1283951 : Blo 223812 1283951 := bstep (se 1 (by rfl) ⟨962963, by rfl⟩ : syracuseStep 1283951 = 1925927) B1925927
theorem B1284407 : Blo 223812 1284407 := bstep (se 1 (by rfl) ⟨963305, by rfl⟩ : syracuseStep 1284407 = 1926611) B1926611
theorem B27663227 : Blo 223812 27663227 := bstep (se 1 (by rfl) ⟨20747420, by rfl⟩ : syracuseStep 27663227 = 41494841) B41494841
theorem B1943423 : Blo 223812 1943423 := bstep (se 1 (by rfl) ⟨1457567, by rfl⟩ : syracuseStep 1943423 = 2915135) B2915135
theorem B7317701 : Blo 223812 7317701 := bstep (se 4 (by rfl) ⟨686034, by rfl⟩ : syracuseStep 7317701 = 1372069) B1372069
theorem B339047 : Blo 223812 339047 := bstep (se 1 (by rfl) ⟨254285, by rfl⟩ : syracuseStep 339047 = 508571) B508571
theorem B339803 : Blo 223812 339803 := bstep (se 1 (by rfl) ⟨254852, by rfl⟩ : syracuseStep 339803 = 509705) B509705
theorem B340511 : Blo 223812 340511 := bstep (se 1 (by rfl) ⟨255383, by rfl⟩ : syracuseStep 340511 = 510767) B510767
theorem B340571 : Blo 223812 340571 := bstep (se 1 (by rfl) ⟨255428, by rfl⟩ : syracuseStep 340571 = 510857) B510857
theorem B3879737 : Blo 223812 3879737 := bstep (se 2 (by rfl) ⟨1454901, by rfl⟩ : syracuseStep 3879737 = 2909803) B2909803
theorem B472255 : Blo 223812 472255 := bstep (se 1 (by rfl) ⟨354191, by rfl⟩ : syracuseStep 472255 = 708383) B708383
theorem B341183 : Blo 223812 341183 := bstep (se 1 (by rfl) ⟨255887, by rfl⟩ : syracuseStep 341183 = 511775) B511775
theorem B341471 : Blo 223812 341471 := bstep (se 1 (by rfl) ⟨256103, by rfl⟩ : syracuseStep 341471 = 512207) B512207
theorem B506537 : Blo 223812 506537 := bstep (se 2 (by rfl) ⟨189951, by rfl⟩ : syracuseStep 506537 = 379903) B379903
theorem B508283 : Blo 223812 508283 := bstep (se 1 (by rfl) ⟨381212, by rfl⟩ : syracuseStep 508283 = 762425) B762425
theorem B377959 : Blo 223812 377959 := bstep (se 1 (by rfl) ⟨283469, by rfl⟩ : syracuseStep 377959 = 566939) B566939
theorem B378011 : Blo 223812 378011 := bstep (se 1 (by rfl) ⟨283508, by rfl⟩ : syracuseStep 378011 = 567017) B567017
theorem B511739 : Blo 223812 511739 := bstep (se 1 (by rfl) ⟨383804, by rfl⟩ : syracuseStep 511739 = 767609) B767609
theorem B2905703 : Blo 223812 2905703 := bstep (se 1 (by rfl) ⟨2179277, by rfl⟩ : syracuseStep 2905703 = 4358555) B4358555
theorem B647443 : Blo 223812 647443 := bstep (se 1 (by rfl) ⟨485582, by rfl⟩ : syracuseStep 647443 = 971165) B971165
theorem B912185 : Blo 223812 912185 := bstep (se 2 (by rfl) ⟨342069, by rfl⟩ : syracuseStep 912185 = 684139) B684139
theorem B224895 : Blo 223812 224895 := bstep (se 1 (by rfl) ⟨168671, by rfl⟩ : syracuseStep 224895 = 337343) B337343
theorem B225279 : Blo 223812 225279 := bstep (se 1 (by rfl) ⟨168959, by rfl⟩ : syracuseStep 225279 = 337919) B337919
theorem B618745 : Blo 223812 618745 := bstep (se 2 (by rfl) ⟨232029, by rfl⟩ : syracuseStep 618745 = 464059) B464059
theorem B225583 : Blo 223812 225583 := bstep (se 1 (by rfl) ⟨169187, by rfl⟩ : syracuseStep 225583 = 338375) B338375
theorem B225883 : Blo 223812 225883 := bstep (se 1 (by rfl) ⟨169412, by rfl⟩ : syracuseStep 225883 = 338825) B338825
theorem B226303 : Blo 223812 226303 := bstep (se 1 (by rfl) ⟨169727, by rfl⟩ : syracuseStep 226303 = 339455) B339455
theorem B226607 : Blo 223812 226607 := bstep (se 1 (by rfl) ⟨169955, by rfl⟩ : syracuseStep 226607 = 339911) B339911
theorem B226631 : Blo 223812 226631 := bstep (se 1 (by rfl) ⟨169973, by rfl⟩ : syracuseStep 226631 = 339947) B339947
theorem B2094781 : Blo 223812 2094781 := bstep (se 3 (by rfl) ⟨392771, by rfl⟩ : syracuseStep 2094781 = 785543) B785543
theorem B227655 : Blo 223812 227655 := bstep (se 1 (by rfl) ⟨170741, by rfl⟩ : syracuseStep 227655 = 341483) B341483
theorem B227711 : Blo 223812 227711 := bstep (se 1 (by rfl) ⟨170783, by rfl⟩ : syracuseStep 227711 = 341567) B341567
theorem B719455 : Blo 223812 719455 := bstep (se 1 (by rfl) ⟨539591, by rfl⟩ : syracuseStep 719455 = 1079183) B1079183
theorem B3309311 : Blo 223812 3309311 := bstep (se 1 (by rfl) ⟨2481983, by rfl⟩ : syracuseStep 3309311 = 4963967) B4963967
theorem B2555873 : Blo 223812 2555873 := bstep (se 2 (by rfl) ⟨958452, by rfl⟩ : syracuseStep 2555873 = 1916905) B1916905
theorem B19729595 : Blo 223812 19729595 := bstep (se 1 (by rfl) ⟨14797196, by rfl⟩ : syracuseStep 19729595 = 29594393) B29594393
theorem B1937135 : Blo 223812 1937135 := bstep (se 1 (by rfl) ⟨1452851, by rfl⟩ : syracuseStep 1937135 = 2905703) B2905703
theorem B855967 : Blo 223812 855967 := bstep (se 1 (by rfl) ⟨641975, by rfl⟩ : syracuseStep 855967 = 1283951) B1283951
theorem B856271 : Blo 223812 856271 := bstep (se 1 (by rfl) ⟨642203, by rfl⟩ : syracuseStep 856271 = 1284407) B1284407
theorem B824993 : Blo 223812 824993 := bstep (se 2 (by rfl) ⟨309372, by rfl⟩ : syracuseStep 824993 = 618745) B618745
theorem B2793041 : Blo 223812 2793041 := bstep (se 2 (by rfl) ⟨1047390, by rfl⟩ : syracuseStep 2793041 = 2094781) B2094781
theorem B959273 : Blo 223812 959273 := bstep (se 2 (by rfl) ⟨359727, by rfl⟩ : syracuseStep 959273 = 719455) B719455
theorem B337691 : Blo 223812 337691 := bstep (se 1 (by rfl) ⟨253268, by rfl⟩ : syracuseStep 337691 = 506537) B506537
theorem B2206207 : Blo 223812 2206207 := bstep (se 1 (by rfl) ⟨1654655, by rfl⟩ : syracuseStep 2206207 = 3309311) B3309311
theorem B338855 : Blo 223812 338855 := bstep (se 1 (by rfl) ⟨254141, by rfl⟩ : syracuseStep 338855 = 508283) B508283
theorem B863257 : Blo 223812 863257 := bstep (se 2 (by rfl) ⟨323721, by rfl⟩ : syracuseStep 863257 = 647443) B647443
theorem B1290239 : Blo 223812 1290239 := bstep (se 1 (by rfl) ⟨967679, by rfl⟩ : syracuseStep 1290239 = 1935359) B1935359
theorem B503945 : Blo 223812 503945 := bstep (se 2 (by rfl) ⟨188979, by rfl⟩ : syracuseStep 503945 = 377959) B377959
theorem B341159 : Blo 223812 341159 := bstep (se 1 (by rfl) ⟨255869, by rfl⟩ : syracuseStep 341159 = 511739) B511739
theorem B10074773 : Blo 223812 10074773 := bstep (se 6 (by rfl) ⟨236127, by rfl⟩ : syracuseStep 10074773 = 472255) B472255
theorem B1295615 : Blo 223812 1295615 := bstep (se 1 (by rfl) ⟨971711, by rfl⟩ : syracuseStep 1295615 = 1943423) B1943423
theorem B608123 : Blo 223812 608123 := bstep (se 1 (by rfl) ⟨456092, by rfl⟩ : syracuseStep 608123 = 912185) B912185
theorem B252007 : Blo 223812 252007 := bstep (se 1 (by rfl) ⟨189005, by rfl⟩ : syracuseStep 252007 = 378011) B378011
theorem B18442151 : Blo 223812 18442151 := bstep (se 1 (by rfl) ⟨13831613, by rfl⟩ : syracuseStep 18442151 = 27663227) B27663227
theorem B4878467 : Blo 223812 4878467 := bstep (se 1 (by rfl) ⟨3658850, by rfl⟩ : syracuseStep 4878467 = 7317701) B7317701
theorem B114782953 : Blo 223812 114782953 := bstep (se 2 (by rfl) ⟨43043607, by rfl⟩ : syracuseStep 114782953 = 86087215) B86087215
theorem B226031 : Blo 223812 226031 := bstep (se 1 (by rfl) ⟨169523, by rfl⟩ : syracuseStep 226031 = 339047) B339047
theorem B226535 : Blo 223812 226535 := bstep (se 1 (by rfl) ⟨169901, by rfl⟩ : syracuseStep 226535 = 339803) B339803
theorem B227007 : Blo 223812 227007 := bstep (se 1 (by rfl) ⟨170255, by rfl⟩ : syracuseStep 227007 = 340511) B340511
theorem B227047 : Blo 223812 227047 := bstep (se 1 (by rfl) ⟨170285, by rfl⟩ : syracuseStep 227047 = 340571) B340571
theorem B2586491 : Blo 223812 2586491 := bstep (se 1 (by rfl) ⟨1939868, by rfl⟩ : syracuseStep 2586491 = 3879737) B3879737
theorem B227455 : Blo 223812 227455 := bstep (se 1 (by rfl) ⟨170591, by rfl⟩ : syracuseStep 227455 = 341183) B341183
theorem B227647 : Blo 223812 227647 := bstep (se 1 (by rfl) ⟨170735, by rfl⟩ : syracuseStep 227647 = 341471) B341471
theorem B1703915 : Blo 223812 1703915 := bstep (se 1 (by rfl) ⟨1277936, by rfl⟩ : syracuseStep 1703915 = 2555873) B2555873
theorem B5376149 : Blo 223812 5376149 := bstep (se 6 (by rfl) ⟨126003, by rfl⟩ : syracuseStep 5376149 = 252007) B252007
theorem B11766437 : Blo 223812 11766437 := bstep (se 4 (by rfl) ⟨1103103, by rfl⟩ : syracuseStep 11766437 = 2206207) B2206207
theorem B1151009 : Blo 223812 1151009 := bstep (se 2 (by rfl) ⟨431628, by rfl⟩ : syracuseStep 1151009 = 863257) B863257
theorem B12294767 : Blo 223812 12294767 := bstep (se 1 (by rfl) ⟨9221075, by rfl⟩ : syracuseStep 12294767 = 18442151) B18442151
theorem B860159 : Blo 223812 860159 := bstep (se 1 (by rfl) ⟨645119, by rfl⟩ : syracuseStep 860159 = 1290239) B1290239
theorem B3252311 : Blo 223812 3252311 := bstep (se 1 (by rfl) ⟨2439233, by rfl⟩ : syracuseStep 3252311 = 4878467) B4878467
theorem B335963 : Blo 223812 335963 := bstep (se 1 (by rfl) ⟨251972, by rfl⟩ : syracuseStep 335963 = 503945) B503945
theorem B863743 : Blo 223812 863743 := bstep (se 1 (by rfl) ⟨647807, by rfl⟩ : syracuseStep 863743 = 1295615) B1295615
theorem B405415 : Blo 223812 405415 := bstep (se 1 (by rfl) ⟨304061, by rfl⟩ : syracuseStep 405415 = 608123) B608123
theorem B13153063 : Blo 223812 13153063 := bstep (se 1 (by rfl) ⟨9864797, by rfl⟩ : syracuseStep 13153063 = 19729595) B19729595
theorem B1291423 : Blo 223812 1291423 := bstep (se 1 (by rfl) ⟨968567, by rfl⟩ : syracuseStep 1291423 = 1937135) B1937135
theorem B570847 : Blo 223812 570847 := bstep (se 1 (by rfl) ⟨428135, by rfl⟩ : syracuseStep 570847 = 856271) B856271
theorem B639515 : Blo 223812 639515 := bstep (se 1 (by rfl) ⟨479636, by rfl⟩ : syracuseStep 639515 = 959273) B959273
theorem B153043937 : Blo 223812 153043937 := bstep (se 2 (by rfl) ⟨57391476, by rfl⟩ : syracuseStep 153043937 = 114782953) B114782953
theorem B1724327 : Blo 223812 1724327 := bstep (se 1 (by rfl) ⟨1293245, by rfl⟩ : syracuseStep 1724327 = 2586491) B2586491
theorem B1135943 : Blo 223812 1135943 := bstep (se 1 (by rfl) ⟨851957, by rfl⟩ : syracuseStep 1135943 = 1703915) B1703915
theorem B549995 : Blo 223812 549995 := bstep (se 1 (by rfl) ⟨412496, by rfl⟩ : syracuseStep 549995 = 824993) B824993
theorem B1862027 : Blo 223812 1862027 := bstep (se 1 (by rfl) ⟨1396520, by rfl⟩ : syracuseStep 1862027 = 2793041) B2793041
theorem B1141289 : Blo 223812 1141289 := bstep (se 2 (by rfl) ⟨427983, by rfl⟩ : syracuseStep 1141289 = 855967) B855967
theorem B225127 : Blo 223812 225127 := bstep (se 1 (by rfl) ⟨168845, by rfl⟩ : syracuseStep 225127 = 337691) B337691
theorem B225903 : Blo 223812 225903 := bstep (se 1 (by rfl) ⟨169427, by rfl⟩ : syracuseStep 225903 = 338855) B338855
theorem B227439 : Blo 223812 227439 := bstep (se 1 (by rfl) ⟨170579, by rfl⟩ : syracuseStep 227439 = 341159) B341159
theorem B6716515 : Blo 223812 6716515 := bstep (se 1 (by rfl) ⟨5037386, by rfl⟩ : syracuseStep 6716515 = 10074773) B10074773
theorem B5866613 : Blo 223812 5866613 := bstep (se 5 (by rfl) ⟨274997, by rfl⟩ : syracuseStep 5866613 = 549995) B549995
theorem B1705373 : Blo 223812 1705373 := bstep (se 3 (by rfl) ⟨319757, by rfl⟩ : syracuseStep 1705373 = 639515) B639515
theorem B1149551 : Blo 223812 1149551 := bstep (se 1 (by rfl) ⟨862163, by rfl⟩ : syracuseStep 1149551 = 1724327) B1724327
theorem B757295 : Blo 223812 757295 := bstep (se 1 (by rfl) ⟨567971, by rfl⟩ : syracuseStep 757295 = 1135943) B1135943
theorem B8196511 : Blo 223812 8196511 := bstep (se 1 (by rfl) ⟨6147383, by rfl⟩ : syracuseStep 8196511 = 12294767) B12294767
theorem B1151657 : Blo 223812 1151657 := bstep (se 2 (by rfl) ⟨431871, by rfl⟩ : syracuseStep 1151657 = 863743) B863743
theorem B2168207 : Blo 223812 2168207 := bstep (se 1 (by rfl) ⟨1626155, by rfl⟩ : syracuseStep 2168207 = 3252311) B3252311
theorem B17537417 : Blo 223812 17537417 := bstep (se 2 (by rfl) ⟨6576531, by rfl⟩ : syracuseStep 17537417 = 13153063) B13153063
theorem B760859 : Blo 223812 760859 := bstep (se 1 (by rfl) ⟨570644, by rfl⟩ : syracuseStep 760859 = 1141289) B1141289
theorem B761129 : Blo 223812 761129 := bstep (se 2 (by rfl) ⟨285423, by rfl⟩ : syracuseStep 761129 = 570847) B570847
theorem B8955353 : Blo 223812 8955353 := bstep (se 2 (by rfl) ⟨3358257, by rfl⟩ : syracuseStep 8955353 = 6716515) B6716515
theorem B3584099 : Blo 223812 3584099 := bstep (se 1 (by rfl) ⟨2688074, by rfl⟩ : syracuseStep 3584099 = 5376149) B5376149
theorem B7844291 : Blo 223812 7844291 := bstep (se 1 (by rfl) ⟨5883218, by rfl⟩ : syracuseStep 7844291 = 11766437) B11766437
theorem B767339 : Blo 223812 767339 := bstep (se 1 (by rfl) ⟨575504, by rfl⟩ : syracuseStep 767339 = 1151009) B1151009
theorem B573439 : Blo 223812 573439 := bstep (se 1 (by rfl) ⟨430079, by rfl⟩ : syracuseStep 573439 = 860159) B860159
theorem B1721897 : Blo 223812 1721897 := bstep (se 2 (by rfl) ⟨645711, by rfl⟩ : syracuseStep 1721897 = 1291423) B1291423
theorem B102029291 : Blo 223812 102029291 := bstep (se 1 (by rfl) ⟨76521968, by rfl⟩ : syracuseStep 102029291 = 153043937) B153043937
theorem B223975 : Blo 223812 223975 := bstep (se 1 (by rfl) ⟨167981, by rfl⟩ : syracuseStep 223975 = 335963) B335963
theorem B1241351 : Blo 223812 1241351 := bstep (se 1 (by rfl) ⟨931013, by rfl⟩ : syracuseStep 1241351 = 1862027) B1862027
theorem B2162213 : Blo 223812 2162213 := bstep (se 4 (by rfl) ⟨202707, by rfl⟩ : syracuseStep 2162213 = 405415) B405415
theorem B1147931 : Blo 223812 1147931 := bstep (se 1 (by rfl) ⟨860948, by rfl⟩ : syracuseStep 1147931 = 1721897) B1721897
theorem B1445471 : Blo 223812 1445471 := bstep (se 1 (by rfl) ⟨1084103, by rfl⟩ : syracuseStep 1445471 = 2168207) B2168207
theorem B5970235 : Blo 223812 5970235 := bstep (se 1 (by rfl) ⟨4477676, by rfl⟩ : syracuseStep 5970235 = 8955353) B8955353
theorem B827567 : Blo 223812 827567 := bstep (se 1 (by rfl) ⟨620675, by rfl⟩ : syracuseStep 827567 = 1241351) B1241351
theorem B764585 : Blo 223812 764585 := bstep (se 2 (by rfl) ⟨286719, by rfl⟩ : syracuseStep 764585 = 573439) B573439
theorem B3911075 : Blo 223812 3911075 := bstep (se 1 (by rfl) ⟨2933306, by rfl⟩ : syracuseStep 3911075 = 5866613) B5866613
theorem B766367 : Blo 223812 766367 := bstep (se 1 (by rfl) ⟨574775, by rfl⟩ : syracuseStep 766367 = 1149551) B1149551
theorem B504863 : Blo 223812 504863 := bstep (se 1 (by rfl) ⟨378647, by rfl⟩ : syracuseStep 504863 = 757295) B757295
theorem B767771 : Blo 223812 767771 := bstep (se 1 (by rfl) ⟨575828, by rfl⟩ : syracuseStep 767771 = 1151657) B1151657
theorem B507239 : Blo 223812 507239 := bstep (se 1 (by rfl) ⟨380429, by rfl⟩ : syracuseStep 507239 = 760859) B760859
theorem B507419 : Blo 223812 507419 := bstep (se 1 (by rfl) ⟨380564, by rfl⟩ : syracuseStep 507419 = 761129) B761129
theorem B10928681 : Blo 223812 10928681 := bstep (se 2 (by rfl) ⟨4098255, by rfl⟩ : syracuseStep 10928681 = 8196511) B8196511
theorem B5229527 : Blo 223812 5229527 := bstep (se 1 (by rfl) ⟨3922145, by rfl⟩ : syracuseStep 5229527 = 7844291) B7844291
theorem B511559 : Blo 223812 511559 := bstep (se 1 (by rfl) ⟨383669, by rfl⟩ : syracuseStep 511559 = 767339) B767339
theorem B9557597 : Blo 223812 9557597 := bstep (se 3 (by rfl) ⟨1792049, by rfl⟩ : syracuseStep 9557597 = 3584099) B3584099
theorem B1136915 : Blo 223812 1136915 := bstep (se 1 (by rfl) ⟨852686, by rfl⟩ : syracuseStep 1136915 = 1705373) B1705373
theorem B68019527 : Blo 223812 68019527 := bstep (se 1 (by rfl) ⟨51014645, by rfl⟩ : syracuseStep 68019527 = 102029291) B102029291
theorem B11691611 : Blo 223812 11691611 := bstep (se 1 (by rfl) ⟨8768708, by rfl⟩ : syracuseStep 11691611 = 17537417) B17537417
theorem B1441475 : Blo 223812 1441475 := bstep (se 1 (by rfl) ⟨1081106, by rfl⟩ : syracuseStep 1441475 = 2162213) B2162213
theorem B757943 : Blo 223812 757943 := bstep (se 1 (by rfl) ⟨568457, by rfl⟩ : syracuseStep 757943 = 1136915) B1136915
theorem B336575 : Blo 223812 336575 := bstep (se 1 (by rfl) ⟨252431, by rfl⟩ : syracuseStep 336575 = 504863) B504863
theorem B338159 : Blo 223812 338159 := bstep (se 1 (by rfl) ⟨253619, by rfl⟩ : syracuseStep 338159 = 507239) B507239
theorem B338279 : Blo 223812 338279 := bstep (se 1 (by rfl) ⟨253709, by rfl⟩ : syracuseStep 338279 = 507419) B507419
theorem B960983 : Blo 223812 960983 := bstep (se 1 (by rfl) ⟨720737, by rfl⟩ : syracuseStep 960983 = 1441475) B1441475
theorem B7285787 : Blo 223812 7285787 := bstep (se 1 (by rfl) ⟨5464340, by rfl⟩ : syracuseStep 7285787 = 10928681) B10928681
theorem B765287 : Blo 223812 765287 := bstep (se 1 (by rfl) ⟨573965, by rfl⟩ : syracuseStep 765287 = 1147931) B1147931
theorem B341039 : Blo 223812 341039 := bstep (se 1 (by rfl) ⟨255779, by rfl⟩ : syracuseStep 341039 = 511559) B511559
theorem B963647 : Blo 223812 963647 := bstep (se 1 (by rfl) ⟨722735, by rfl⟩ : syracuseStep 963647 = 1445471) B1445471
theorem B6371731 : Blo 223812 6371731 := bstep (se 1 (by rfl) ⟨4778798, by rfl⟩ : syracuseStep 6371731 = 9557597) B9557597
theorem B509723 : Blo 223812 509723 := bstep (se 1 (by rfl) ⟨382292, by rfl⟩ : syracuseStep 509723 = 764585) B764585
theorem B2607383 : Blo 223812 2607383 := bstep (se 1 (by rfl) ⟨1955537, by rfl⟩ : syracuseStep 2607383 = 3911075) B3911075
theorem B13945405 : Blo 223812 13945405 := bstep (se 3 (by rfl) ⟨2614763, by rfl⟩ : syracuseStep 13945405 = 5229527) B5229527
theorem B510911 : Blo 223812 510911 := bstep (se 1 (by rfl) ⟨383183, by rfl⟩ : syracuseStep 510911 = 766367) B766367
theorem B511847 : Blo 223812 511847 := bstep (se 1 (by rfl) ⟨383885, by rfl⟩ : syracuseStep 511847 = 767771) B767771
theorem B551711 : Blo 223812 551711 := bstep (se 1 (by rfl) ⟨413783, by rfl⟩ : syracuseStep 551711 = 827567) B827567
theorem B45346351 : Blo 223812 45346351 := bstep (se 1 (by rfl) ⟨34009763, by rfl⟩ : syracuseStep 45346351 = 68019527) B68019527
theorem B7794407 : Blo 223812 7794407 := bstep (se 1 (by rfl) ⟨5845805, by rfl⟩ : syracuseStep 7794407 = 11691611) B11691611
theorem B7960313 : Blo 223812 7960313 := bstep (se 2 (by rfl) ⟨2985117, by rfl⟩ : syracuseStep 7960313 = 5970235) B5970235
theorem B1738255 : Blo 223812 1738255 := bstep (se 1 (by rfl) ⟨1303691, by rfl⟩ : syracuseStep 1738255 = 2607383) B2607383
theorem B60461801 : Blo 223812 60461801 := bstep (se 2 (by rfl) ⟨22673175, by rfl⟩ : syracuseStep 60461801 = 45346351) B45346351
theorem B4857191 : Blo 223812 4857191 := bstep (se 1 (by rfl) ⟨3642893, by rfl⟩ : syracuseStep 4857191 = 7285787) B7285787
theorem B8495641 : Blo 223812 8495641 := bstep (se 2 (by rfl) ⟨3185865, by rfl⟩ : syracuseStep 8495641 = 6371731) B6371731
theorem B339815 : Blo 223812 339815 := bstep (se 1 (by rfl) ⟨254861, by rfl⟩ : syracuseStep 339815 = 509723) B509723
theorem B340607 : Blo 223812 340607 := bstep (se 1 (by rfl) ⟨255455, by rfl⟩ : syracuseStep 340607 = 510911) B510911
theorem B341231 : Blo 223812 341231 := bstep (se 1 (by rfl) ⟨255923, by rfl⟩ : syracuseStep 341231 = 511847) B511847
theorem B505295 : Blo 223812 505295 := bstep (se 1 (by rfl) ⟨378971, by rfl⟩ : syracuseStep 505295 = 757943) B757943
theorem B18593873 : Blo 223812 18593873 := bstep (se 2 (by rfl) ⟨6972702, by rfl⟩ : syracuseStep 18593873 = 13945405) B13945405
theorem B640655 : Blo 223812 640655 := bstep (se 1 (by rfl) ⟨480491, by rfl⟩ : syracuseStep 640655 = 960983) B960983
theorem B510191 : Blo 223812 510191 := bstep (se 1 (by rfl) ⟨382643, by rfl⟩ : syracuseStep 510191 = 765287) B765287
theorem B5196271 : Blo 223812 5196271 := bstep (se 1 (by rfl) ⟨3897203, by rfl⟩ : syracuseStep 5196271 = 7794407) B7794407
theorem B642431 : Blo 223812 642431 := bstep (se 1 (by rfl) ⟨481823, by rfl⟩ : syracuseStep 642431 = 963647) B963647
theorem B21227501 : Blo 223812 21227501 := bstep (se 3 (by rfl) ⟨3980156, by rfl⟩ : syracuseStep 21227501 = 7960313) B7960313
theorem B224383 : Blo 223812 224383 := bstep (se 1 (by rfl) ⟨168287, by rfl⟩ : syracuseStep 224383 = 336575) B336575
theorem B225439 : Blo 223812 225439 := bstep (se 1 (by rfl) ⟨169079, by rfl⟩ : syracuseStep 225439 = 338159) B338159
theorem B225519 : Blo 223812 225519 := bstep (se 1 (by rfl) ⟨169139, by rfl⟩ : syracuseStep 225519 = 338279) B338279
theorem B1471229 : Blo 223812 1471229 := bstep (se 3 (by rfl) ⟨275855, by rfl⟩ : syracuseStep 1471229 = 551711) B551711
theorem B227359 : Blo 223812 227359 := bstep (se 1 (by rfl) ⟨170519, by rfl⟩ : syracuseStep 227359 = 341039) B341039
theorem B427103 : Blo 223812 427103 := bstep (se 1 (by rfl) ⟨320327, by rfl⟩ : syracuseStep 427103 = 640655) B640655
theorem B40307867 : Blo 223812 40307867 := bstep (se 1 (by rfl) ⟨30230900, by rfl⟩ : syracuseStep 40307867 = 60461801) B60461801
theorem B336863 : Blo 223812 336863 := bstep (se 1 (by rfl) ⟨252647, by rfl⟩ : syracuseStep 336863 = 505295) B505295
theorem B1713149 : Blo 223812 1713149 := bstep (se 3 (by rfl) ⟨321215, by rfl⟩ : syracuseStep 1713149 = 642431) B642431
theorem B12395915 : Blo 223812 12395915 := bstep (se 1 (by rfl) ⟨9296936, by rfl⟩ : syracuseStep 12395915 = 18593873) B18593873
theorem B340127 : Blo 223812 340127 := bstep (se 1 (by rfl) ⟨255095, by rfl⟩ : syracuseStep 340127 = 510191) B510191
theorem B6928361 : Blo 223812 6928361 := bstep (se 2 (by rfl) ⟨2598135, by rfl⟩ : syracuseStep 6928361 = 5196271) B5196271
theorem B11327521 : Blo 223812 11327521 := bstep (se 2 (by rfl) ⟨4247820, by rfl⟩ : syracuseStep 11327521 = 8495641) B8495641
theorem B2317673 : Blo 223812 2317673 := bstep (se 2 (by rfl) ⟨869127, by rfl⟩ : syracuseStep 2317673 = 1738255) B1738255
theorem B3238127 : Blo 223812 3238127 := bstep (se 1 (by rfl) ⟨2428595, by rfl⟩ : syracuseStep 3238127 = 4857191) B4857191
theorem B14151667 : Blo 223812 14151667 := bstep (se 1 (by rfl) ⟨10613750, by rfl⟩ : syracuseStep 14151667 = 21227501) B21227501
theorem B226543 : Blo 223812 226543 := bstep (se 1 (by rfl) ⟨169907, by rfl⟩ : syracuseStep 226543 = 339815) B339815
theorem B227071 : Blo 223812 227071 := bstep (se 1 (by rfl) ⟨170303, by rfl⟩ : syracuseStep 227071 = 340607) B340607
theorem B980819 : Blo 223812 980819 := bstep (se 1 (by rfl) ⟨735614, by rfl⟩ : syracuseStep 980819 = 1471229) B1471229
theorem B227487 : Blo 223812 227487 := bstep (se 1 (by rfl) ⟨170615, by rfl⟩ : syracuseStep 227487 = 341231) B341231
theorem B26871911 : Blo 223812 26871911 := bstep (se 1 (by rfl) ⟨20153933, by rfl⟩ : syracuseStep 26871911 = 40307867) B40307867
theorem B8263943 : Blo 223812 8263943 := bstep (se 1 (by rfl) ⟨6197957, by rfl⟩ : syracuseStep 8263943 = 12395915) B12395915
theorem B6180461 : Blo 223812 6180461 := bstep (se 3 (by rfl) ⟨1158836, by rfl⟩ : syracuseStep 6180461 = 2317673) B2317673
theorem B284735 : Blo 223812 284735 := bstep (se 1 (by rfl) ⟨213551, by rfl⟩ : syracuseStep 284735 = 427103) B427103
theorem B18868889 : Blo 223812 18868889 := bstep (se 2 (by rfl) ⟨7075833, by rfl⟩ : syracuseStep 18868889 = 14151667) B14151667
theorem B224575 : Blo 223812 224575 := bstep (se 1 (by rfl) ⟨168431, by rfl⟩ : syracuseStep 224575 = 336863) B336863
theorem B1142099 : Blo 223812 1142099 := bstep (se 1 (by rfl) ⟨856574, by rfl⟩ : syracuseStep 1142099 = 1713149) B1713149
theorem B2158751 : Blo 223812 2158751 := bstep (se 1 (by rfl) ⟨1619063, by rfl⟩ : syracuseStep 2158751 = 3238127) B3238127
theorem B15103361 : Blo 223812 15103361 := bstep (se 2 (by rfl) ⟨5663760, by rfl⟩ : syracuseStep 15103361 = 11327521) B11327521
theorem B226751 : Blo 223812 226751 := bstep (se 1 (by rfl) ⟨170063, by rfl⟩ : syracuseStep 226751 = 340127) B340127
theorem B653879 : Blo 223812 653879 := bstep (se 1 (by rfl) ⟨490409, by rfl⟩ : syracuseStep 653879 = 980819) B980819
theorem B4618907 : Blo 223812 4618907 := bstep (se 1 (by rfl) ⟨3464180, by rfl⟩ : syracuseStep 4618907 = 6928361) B6928361
theorem B5509295 : Blo 223812 5509295 := bstep (se 1 (by rfl) ⟨4131971, by rfl⟩ : syracuseStep 5509295 = 8263943) B8263943
theorem B759293 : Blo 223812 759293 := bstep (se 3 (by rfl) ⟨142367, by rfl⟩ : syracuseStep 759293 = 284735) B284735
theorem B1743677 : Blo 223812 1743677 := bstep (se 3 (by rfl) ⟨326939, by rfl⟩ : syracuseStep 1743677 = 653879) B653879
theorem B761399 : Blo 223812 761399 := bstep (se 1 (by rfl) ⟨571049, by rfl⟩ : syracuseStep 761399 = 1142099) B1142099
theorem B10068907 : Blo 223812 10068907 := bstep (se 1 (by rfl) ⟨7551680, by rfl⟩ : syracuseStep 10068907 = 15103361) B15103361
theorem B17914607 : Blo 223812 17914607 := bstep (se 1 (by rfl) ⟨13435955, by rfl⟩ : syracuseStep 17914607 = 26871911) B26871911
theorem B4120307 : Blo 223812 4120307 := bstep (se 1 (by rfl) ⟨3090230, by rfl⟩ : syracuseStep 4120307 = 6180461) B6180461
theorem B12579259 : Blo 223812 12579259 := bstep (se 1 (by rfl) ⟨9434444, by rfl⟩ : syracuseStep 12579259 = 18868889) B18868889
theorem B1439167 : Blo 223812 1439167 := bstep (se 1 (by rfl) ⟨1079375, by rfl⟩ : syracuseStep 1439167 = 2158751) B2158751
theorem B3079271 : Blo 223812 3079271 := bstep (se 1 (by rfl) ⟨2309453, by rfl⟩ : syracuseStep 3079271 = 4618907) B4618907
theorem B3672863 : Blo 223812 3672863 := bstep (se 1 (by rfl) ⟨2754647, by rfl⟩ : syracuseStep 3672863 = 5509295) B5509295
theorem B506195 : Blo 223812 506195 := bstep (se 1 (by rfl) ⟨379646, by rfl⟩ : syracuseStep 506195 = 759293) B759293
theorem B11943071 : Blo 223812 11943071 := bstep (se 1 (by rfl) ⟨8957303, by rfl⟩ : syracuseStep 11943071 = 17914607) B17914607
theorem B1162451 : Blo 223812 1162451 := bstep (se 1 (by rfl) ⟨871838, by rfl⟩ : syracuseStep 1162451 = 1743677) B1743677
theorem B507599 : Blo 223812 507599 := bstep (se 1 (by rfl) ⟨380699, by rfl⟩ : syracuseStep 507599 = 761399) B761399
theorem B1918889 : Blo 223812 1918889 := bstep (se 2 (by rfl) ⟨719583, by rfl⟩ : syracuseStep 1918889 = 1439167) B1439167
theorem B2052847 : Blo 223812 2052847 := bstep (se 1 (by rfl) ⟨1539635, by rfl⟩ : syracuseStep 2052847 = 3079271) B3079271
theorem B13425209 : Blo 223812 13425209 := bstep (se 2 (by rfl) ⟨5034453, by rfl⟩ : syracuseStep 13425209 = 10068907) B10068907
theorem B2746871 : Blo 223812 2746871 := bstep (se 1 (by rfl) ⟨2060153, by rfl⟩ : syracuseStep 2746871 = 4120307) B4120307
theorem B16772345 : Blo 223812 16772345 := bstep (se 2 (by rfl) ⟨6289629, by rfl⟩ : syracuseStep 16772345 = 12579259) B12579259
theorem B1279259 : Blo 223812 1279259 := bstep (se 1 (by rfl) ⟨959444, by rfl⟩ : syracuseStep 1279259 = 1918889) B1918889
theorem B10948517 : Blo 223812 10948517 := bstep (se 4 (by rfl) ⟨1026423, by rfl⟩ : syracuseStep 10948517 = 2052847) B2052847
theorem B8950139 : Blo 223812 8950139 := bstep (se 1 (by rfl) ⟨6712604, by rfl⟩ : syracuseStep 8950139 = 13425209) B13425209
theorem B11181563 : Blo 223812 11181563 := bstep (se 1 (by rfl) ⟨8386172, by rfl⟩ : syracuseStep 11181563 = 16772345) B16772345
theorem B337463 : Blo 223812 337463 := bstep (se 1 (by rfl) ⟨253097, by rfl⟩ : syracuseStep 337463 = 506195) B506195
theorem B338399 : Blo 223812 338399 := bstep (se 1 (by rfl) ⟨253799, by rfl⟩ : syracuseStep 338399 = 507599) B507599
theorem B3099869 : Blo 223812 3099869 := bstep (se 3 (by rfl) ⟨581225, by rfl⟩ : syracuseStep 3099869 = 1162451) B1162451
theorem B2448575 : Blo 223812 2448575 := bstep (se 1 (by rfl) ⟨1836431, by rfl⟩ : syracuseStep 2448575 = 3672863) B3672863
theorem B1831247 : Blo 223812 1831247 := bstep (se 1 (by rfl) ⟨1373435, by rfl⟩ : syracuseStep 1831247 = 2746871) B2746871
theorem B7962047 : Blo 223812 7962047 := bstep (se 1 (by rfl) ⟨5971535, by rfl⟩ : syracuseStep 7962047 = 11943071) B11943071
theorem B852839 : Blo 223812 852839 := bstep (se 1 (by rfl) ⟨639629, by rfl⟩ : syracuseStep 852839 = 1279259) B1279259
theorem B2066579 : Blo 223812 2066579 := bstep (se 1 (by rfl) ⟨1549934, by rfl⟩ : syracuseStep 2066579 = 3099869) B3099869
theorem B5966759 : Blo 223812 5966759 := bstep (se 1 (by rfl) ⟨4475069, by rfl⟩ : syracuseStep 5966759 = 8950139) B8950139
theorem B1220831 : Blo 223812 1220831 := bstep (se 1 (by rfl) ⟨915623, by rfl⟩ : syracuseStep 1220831 = 1831247) B1831247
theorem B7454375 : Blo 223812 7454375 := bstep (se 1 (by rfl) ⟨5590781, by rfl⟩ : syracuseStep 7454375 = 11181563) B11181563
theorem B7299011 : Blo 223812 7299011 := bstep (se 1 (by rfl) ⟨5474258, by rfl⟩ : syracuseStep 7299011 = 10948517) B10948517
theorem B1632383 : Blo 223812 1632383 := bstep (se 1 (by rfl) ⟨1224287, by rfl⟩ : syracuseStep 1632383 = 2448575) B2448575
theorem B224975 : Blo 223812 224975 := bstep (se 1 (by rfl) ⟨168731, by rfl⟩ : syracuseStep 224975 = 337463) B337463
theorem B225599 : Blo 223812 225599 := bstep (se 1 (by rfl) ⟨169199, by rfl⟩ : syracuseStep 225599 = 338399) B338399
theorem B5308031 : Blo 223812 5308031 := bstep (se 1 (by rfl) ⟨3981023, by rfl⟩ : syracuseStep 5308031 = 7962047) B7962047
theorem B1377719 : Blo 223812 1377719 := bstep (se 1 (by rfl) ⟨1033289, by rfl⟩ : syracuseStep 1377719 = 2066579) B2066579
theorem B1088255 : Blo 223812 1088255 := bstep (se 1 (by rfl) ⟨816191, by rfl⟩ : syracuseStep 1088255 = 1632383) B1632383
theorem B568559 : Blo 223812 568559 := bstep (se 1 (by rfl) ⟨426419, by rfl⟩ : syracuseStep 568559 = 852839) B852839
theorem B3977839 : Blo 223812 3977839 := bstep (se 1 (by rfl) ⟨2983379, by rfl⟩ : syracuseStep 3977839 = 5966759) B5966759
theorem B4866007 : Blo 223812 4866007 := bstep (se 1 (by rfl) ⟨3649505, by rfl⟩ : syracuseStep 4866007 = 7299011) B7299011
theorem B4969583 : Blo 223812 4969583 := bstep (se 1 (by rfl) ⟨3727187, by rfl⟩ : syracuseStep 4969583 = 7454375) B7454375
theorem B813887 : Blo 223812 813887 := bstep (se 1 (by rfl) ⟨610415, by rfl⟩ : syracuseStep 813887 = 1220831) B1220831
theorem B3538687 : Blo 223812 3538687 := bstep (se 1 (by rfl) ⟨2654015, by rfl⟩ : syracuseStep 3538687 = 5308031) B5308031
theorem B918479 : Blo 223812 918479 := bstep (se 1 (by rfl) ⟨688859, by rfl⟩ : syracuseStep 918479 = 1377719) B1377719
theorem B3313055 : Blo 223812 3313055 := bstep (se 1 (by rfl) ⟨2484791, by rfl⟩ : syracuseStep 3313055 = 4969583) B4969583
theorem B21215141 : Blo 223812 21215141 := bstep (se 4 (by rfl) ⟨1988919, by rfl⟩ : syracuseStep 21215141 = 3977839) B3977839
theorem B542591 : Blo 223812 542591 := bstep (se 1 (by rfl) ⟨406943, by rfl⟩ : syracuseStep 542591 = 813887) B813887
theorem B2902013 : Blo 223812 2902013 := bstep (se 3 (by rfl) ⟨544127, by rfl⟩ : syracuseStep 2902013 = 1088255) B1088255
theorem B379039 : Blo 223812 379039 := bstep (se 1 (by rfl) ⟨284279, by rfl⟩ : syracuseStep 379039 = 568559) B568559
theorem B4718249 : Blo 223812 4718249 := bstep (se 2 (by rfl) ⟨1769343, by rfl⟩ : syracuseStep 4718249 = 3538687) B3538687
theorem B6488009 : Blo 223812 6488009 := bstep (se 2 (by rfl) ⟨2433003, by rfl⟩ : syracuseStep 6488009 = 4866007) B4866007
theorem B361727 : Blo 223812 361727 := bstep (se 1 (by rfl) ⟨271295, by rfl⟩ : syracuseStep 361727 = 542591) B542591
theorem B1934675 : Blo 223812 1934675 := bstep (se 1 (by rfl) ⟨1451006, by rfl⟩ : syracuseStep 1934675 = 2902013) B2902013
theorem B2208703 : Blo 223812 2208703 := bstep (se 1 (by rfl) ⟨1656527, by rfl⟩ : syracuseStep 2208703 = 3313055) B3313055
theorem B505385 : Blo 223812 505385 := bstep (se 2 (by rfl) ⟨189519, by rfl⟩ : syracuseStep 505385 = 379039) B379039
theorem B14143427 : Blo 223812 14143427 := bstep (se 1 (by rfl) ⟨10607570, by rfl⟩ : syracuseStep 14143427 = 21215141) B21215141
theorem B612319 : Blo 223812 612319 := bstep (se 1 (by rfl) ⟨459239, by rfl⟩ : syracuseStep 612319 = 918479) B918479
theorem B3145499 : Blo 223812 3145499 := bstep (se 1 (by rfl) ⟨2359124, by rfl⟩ : syracuseStep 3145499 = 4718249) B4718249
theorem B4325339 : Blo 223812 4325339 := bstep (se 1 (by rfl) ⟨3244004, by rfl⟩ : syracuseStep 4325339 = 6488009) B6488009
theorem B336923 : Blo 223812 336923 := bstep (se 1 (by rfl) ⟨252692, by rfl⟩ : syracuseStep 336923 = 505385) B505385
theorem B241151 : Blo 223812 241151 := bstep (se 1 (by rfl) ⟨180863, by rfl⟩ : syracuseStep 241151 = 361727) B361727
theorem B1289783 : Blo 223812 1289783 := bstep (se 1 (by rfl) ⟨967337, by rfl⟩ : syracuseStep 1289783 = 1934675) B1934675
theorem B9428951 : Blo 223812 9428951 := bstep (se 1 (by rfl) ⟨7071713, by rfl⟩ : syracuseStep 9428951 = 14143427) B14143427
theorem B2944937 : Blo 223812 2944937 := bstep (se 2 (by rfl) ⟨1104351, by rfl⟩ : syracuseStep 2944937 = 2208703) B2208703
theorem B816425 : Blo 223812 816425 := bstep (se 2 (by rfl) ⟨306159, by rfl⟩ : syracuseStep 816425 = 612319) B612319
theorem B2096999 : Blo 223812 2096999 := bstep (se 1 (by rfl) ⟨1572749, by rfl⟩ : syracuseStep 2096999 = 3145499) B3145499
theorem B2883559 : Blo 223812 2883559 := bstep (se 1 (by rfl) ⟨2162669, by rfl⟩ : syracuseStep 2883559 = 4325339) B4325339
theorem B859855 : Blo 223812 859855 := bstep (se 1 (by rfl) ⟨644891, by rfl⟩ : syracuseStep 859855 = 1289783) B1289783
theorem B3844745 : Blo 223812 3844745 := bstep (se 2 (by rfl) ⟨1441779, by rfl⟩ : syracuseStep 3844745 = 2883559) B2883559
theorem B544283 : Blo 223812 544283 := bstep (se 1 (by rfl) ⟨408212, by rfl⟩ : syracuseStep 544283 = 816425) B816425
theorem B643069 : Blo 223812 643069 := bstep (se 3 (by rfl) ⟨120575, by rfl⟩ : syracuseStep 643069 = 241151) B241151
theorem B1397999 : Blo 223812 1397999 := bstep (se 1 (by rfl) ⟨1048499, by rfl⟩ : syracuseStep 1397999 = 2096999) B2096999
theorem B6285967 : Blo 223812 6285967 := bstep (se 1 (by rfl) ⟨4714475, by rfl⟩ : syracuseStep 6285967 = 9428951) B9428951
theorem B224615 : Blo 223812 224615 := bstep (se 1 (by rfl) ⟨168461, by rfl⟩ : syracuseStep 224615 = 336923) B336923
theorem B1963291 : Blo 223812 1963291 := bstep (se 1 (by rfl) ⟨1472468, by rfl⟩ : syracuseStep 1963291 = 2944937) B2944937
theorem B362855 : Blo 223812 362855 := bstep (se 1 (by rfl) ⟨272141, by rfl⟩ : syracuseStep 362855 = 544283) B544283
theorem B857425 : Blo 223812 857425 := bstep (se 2 (by rfl) ⟨321534, by rfl⟩ : syracuseStep 857425 = 643069) B643069
theorem B2563163 : Blo 223812 2563163 := bstep (se 1 (by rfl) ⟨1922372, by rfl⟩ : syracuseStep 2563163 = 3844745) B3844745
theorem B134100629 : Blo 223812 134100629 := bstep (se 6 (by rfl) ⟨3142983, by rfl⟩ : syracuseStep 134100629 = 6285967) B6285967
theorem B931999 : Blo 223812 931999 := bstep (se 1 (by rfl) ⟨698999, by rfl⟩ : syracuseStep 931999 = 1397999) B1397999
theorem B2617721 : Blo 223812 2617721 := bstep (se 2 (by rfl) ⟨981645, by rfl⟩ : syracuseStep 2617721 = 1963291) B1963291
theorem B1146473 : Blo 223812 1146473 := bstep (se 2 (by rfl) ⟨429927, by rfl⟩ : syracuseStep 1146473 = 859855) B859855
theorem B1708775 : Blo 223812 1708775 := bstep (se 1 (by rfl) ⟨1281581, by rfl⟩ : syracuseStep 1708775 = 2563163) B2563163
theorem B1745147 : Blo 223812 1745147 := bstep (se 1 (by rfl) ⟨1308860, by rfl⟩ : syracuseStep 1745147 = 2617721) B2617721
theorem B89400419 : Blo 223812 89400419 := bstep (se 1 (by rfl) ⟨67050314, by rfl⟩ : syracuseStep 89400419 = 134100629) B134100629
theorem B764315 : Blo 223812 764315 := bstep (se 1 (by rfl) ⟨573236, by rfl⟩ : syracuseStep 764315 = 1146473) B1146473
theorem B241903 : Blo 223812 241903 := bstep (se 1 (by rfl) ⟨181427, by rfl⟩ : syracuseStep 241903 = 362855) B362855
theorem B1143233 : Blo 223812 1143233 := bstep (se 2 (by rfl) ⟨428712, by rfl⟩ : syracuseStep 1143233 = 857425) B857425
theorem B1242665 : Blo 223812 1242665 := bstep (se 2 (by rfl) ⟨465999, by rfl⟩ : syracuseStep 1242665 = 931999) B931999
theorem B762155 : Blo 223812 762155 := bstep (se 1 (by rfl) ⟨571616, by rfl⟩ : syracuseStep 762155 = 1143233) B1143233
theorem B828443 : Blo 223812 828443 := bstep (se 1 (by rfl) ⟨621332, by rfl⟩ : syracuseStep 828443 = 1242665) B1242665
theorem B1163431 : Blo 223812 1163431 := bstep (se 1 (by rfl) ⟨872573, by rfl⟩ : syracuseStep 1163431 = 1745147) B1745147
theorem B509543 : Blo 223812 509543 := bstep (se 1 (by rfl) ⟨382157, by rfl⟩ : syracuseStep 509543 = 764315) B764315
theorem B1139183 : Blo 223812 1139183 := bstep (se 1 (by rfl) ⟨854387, by rfl⟩ : syracuseStep 1139183 = 1708775) B1708775
theorem B322537 : Blo 223812 322537 := bstep (se 2 (by rfl) ⟨120951, by rfl⟩ : syracuseStep 322537 = 241903) B241903
theorem B59600279 : Blo 223812 59600279 := bstep (se 1 (by rfl) ⟨44700209, by rfl⟩ : syracuseStep 59600279 = 89400419) B89400419
theorem B430049 : Blo 223812 430049 := bstep (se 2 (by rfl) ⟨161268, by rfl⟩ : syracuseStep 430049 = 322537) B322537
theorem B759455 : Blo 223812 759455 := bstep (se 1 (by rfl) ⟨569591, by rfl⟩ : syracuseStep 759455 = 1139183) B1139183
theorem B1551241 : Blo 223812 1551241 := bstep (se 2 (by rfl) ⟨581715, by rfl⟩ : syracuseStep 1551241 = 1163431) B1163431
theorem B339695 : Blo 223812 339695 := bstep (se 1 (by rfl) ⟨254771, by rfl⟩ : syracuseStep 339695 = 509543) B509543
theorem B508103 : Blo 223812 508103 := bstep (se 1 (by rfl) ⟨381077, by rfl⟩ : syracuseStep 508103 = 762155) B762155
theorem B39733519 : Blo 223812 39733519 := bstep (se 1 (by rfl) ⟨29800139, by rfl⟩ : syracuseStep 39733519 = 59600279) B59600279
theorem B552295 : Blo 223812 552295 := bstep (se 1 (by rfl) ⟨414221, by rfl⟩ : syracuseStep 552295 = 828443) B828443
theorem B338735 : Blo 223812 338735 := bstep (se 1 (by rfl) ⟨254051, by rfl⟩ : syracuseStep 338735 = 508103) B508103
theorem B506303 : Blo 223812 506303 := bstep (se 1 (by rfl) ⟨379727, by rfl⟩ : syracuseStep 506303 = 759455) B759455
theorem B736393 : Blo 223812 736393 := bstep (se 2 (by rfl) ⟨276147, by rfl⟩ : syracuseStep 736393 = 552295) B552295
theorem B8273285 : Blo 223812 8273285 := bstep (se 4 (by rfl) ⟨775620, by rfl⟩ : syracuseStep 8273285 = 1551241) B1551241
theorem B52978025 : Blo 223812 52978025 := bstep (se 2 (by rfl) ⟨19866759, by rfl⟩ : syracuseStep 52978025 = 39733519) B39733519
theorem B226463 : Blo 223812 226463 := bstep (se 1 (by rfl) ⟨169847, by rfl⟩ : syracuseStep 226463 = 339695) B339695
theorem B1146797 : Blo 223812 1146797 := bstep (se 3 (by rfl) ⟨215024, by rfl⟩ : syracuseStep 1146797 = 430049) B430049
theorem B337535 : Blo 223812 337535 := bstep (se 1 (by rfl) ⟨253151, by rfl⟩ : syracuseStep 337535 = 506303) B506303
theorem B5515523 : Blo 223812 5515523 := bstep (se 1 (by rfl) ⟨4136642, by rfl⟩ : syracuseStep 5515523 = 8273285) B8273285
theorem B764531 : Blo 223812 764531 := bstep (se 1 (by rfl) ⟨573398, by rfl⟩ : syracuseStep 764531 = 1146797) B1146797
theorem B35318683 : Blo 223812 35318683 := bstep (se 1 (by rfl) ⟨26489012, by rfl⟩ : syracuseStep 35318683 = 52978025) B52978025
theorem B225823 : Blo 223812 225823 := bstep (se 1 (by rfl) ⟨169367, by rfl⟩ : syracuseStep 225823 = 338735) B338735
theorem B981857 : Blo 223812 981857 := bstep (se 2 (by rfl) ⟨368196, by rfl⟩ : syracuseStep 981857 = 736393) B736393
theorem B47091577 : Blo 223812 47091577 := bstep (se 2 (by rfl) ⟨17659341, by rfl⟩ : syracuseStep 47091577 = 35318683) B35318683
theorem B3677015 : Blo 223812 3677015 := bstep (se 1 (by rfl) ⟨2757761, by rfl⟩ : syracuseStep 3677015 = 5515523) B5515523
theorem B509687 : Blo 223812 509687 := bstep (se 1 (by rfl) ⟨382265, by rfl⟩ : syracuseStep 509687 = 764531) B764531
theorem B225023 : Blo 223812 225023 := bstep (se 1 (by rfl) ⟨168767, by rfl⟩ : syracuseStep 225023 = 337535) B337535
theorem B654571 : Blo 223812 654571 := bstep (se 1 (by rfl) ⟨490928, by rfl⟩ : syracuseStep 654571 = 981857) B981857
theorem B62788769 : Blo 223812 62788769 := bstep (se 2 (by rfl) ⟨23545788, by rfl⟩ : syracuseStep 62788769 = 47091577) B47091577
theorem B339791 : Blo 223812 339791 := bstep (se 1 (by rfl) ⟨254843, by rfl⟩ : syracuseStep 339791 = 509687) B509687
theorem B3491045 : Blo 223812 3491045 := bstep (se 4 (by rfl) ⟨327285, by rfl⟩ : syracuseStep 3491045 = 654571) B654571
theorem B2451343 : Blo 223812 2451343 := bstep (se 1 (by rfl) ⟨1838507, by rfl⟩ : syracuseStep 2451343 = 3677015) B3677015
theorem B2327363 : Blo 223812 2327363 := bstep (se 1 (by rfl) ⟨1745522, by rfl⟩ : syracuseStep 2327363 = 3491045) B3491045
theorem B41859179 : Blo 223812 41859179 := bstep (se 1 (by rfl) ⟨31394384, by rfl⟩ : syracuseStep 41859179 = 62788769) B62788769
theorem B3268457 : Blo 223812 3268457 := bstep (se 2 (by rfl) ⟨1225671, by rfl⟩ : syracuseStep 3268457 = 2451343) B2451343
theorem B226527 : Blo 223812 226527 := bstep (se 1 (by rfl) ⟨169895, by rfl⟩ : syracuseStep 226527 = 339791) B339791
theorem B1551575 : Blo 223812 1551575 := bstep (se 1 (by rfl) ⟨1163681, by rfl⟩ : syracuseStep 1551575 = 2327363) B2327363
theorem B2178971 : Blo 223812 2178971 := bstep (se 1 (by rfl) ⟨1634228, by rfl⟩ : syracuseStep 2178971 = 3268457) B3268457
theorem B27906119 : Blo 223812 27906119 := bstep (se 1 (by rfl) ⟨20929589, by rfl⟩ : syracuseStep 27906119 = 41859179) B41859179
theorem B1452647 : Blo 223812 1452647 := bstep (se 1 (by rfl) ⟨1089485, by rfl⟩ : syracuseStep 1452647 = 2178971) B2178971
theorem B1034383 : Blo 223812 1034383 := bstep (se 1 (by rfl) ⟨775787, by rfl⟩ : syracuseStep 1034383 = 1551575) B1551575
theorem B18604079 : Blo 223812 18604079 := bstep (se 1 (by rfl) ⟨13953059, by rfl⟩ : syracuseStep 18604079 = 27906119) B27906119
theorem B1379177 : Blo 223812 1379177 := bstep (se 2 (by rfl) ⟨517191, by rfl⟩ : syracuseStep 1379177 = 1034383) B1034383
theorem B12402719 : Blo 223812 12402719 := bstep (se 1 (by rfl) ⟨9302039, by rfl⟩ : syracuseStep 12402719 = 18604079) B18604079
theorem B968431 : Blo 223812 968431 := bstep (se 1 (by rfl) ⟨726323, by rfl⟩ : syracuseStep 968431 = 1452647) B1452647
theorem B919451 : Blo 223812 919451 := bstep (se 1 (by rfl) ⟨689588, by rfl⟩ : syracuseStep 919451 = 1379177) B1379177
theorem B8268479 : Blo 223812 8268479 := bstep (se 1 (by rfl) ⟨6201359, by rfl⟩ : syracuseStep 8268479 = 12402719) B12402719
theorem B1291241 : Blo 223812 1291241 := bstep (se 2 (by rfl) ⟨484215, by rfl⟩ : syracuseStep 1291241 = 968431) B968431
theorem B5512319 : Blo 223812 5512319 := bstep (se 1 (by rfl) ⟨4134239, by rfl⟩ : syracuseStep 5512319 = 8268479) B8268479
theorem B860827 : Blo 223812 860827 := bstep (se 1 (by rfl) ⟨645620, by rfl⟩ : syracuseStep 860827 = 1291241) B1291241
theorem B2451869 : Blo 223812 2451869 := bstep (se 3 (by rfl) ⟨459725, by rfl⟩ : syracuseStep 2451869 = 919451) B919451
theorem B1147769 : Blo 223812 1147769 := bstep (se 2 (by rfl) ⟨430413, by rfl⟩ : syracuseStep 1147769 = 860827) B860827
theorem B3674879 : Blo 223812 3674879 := bstep (se 1 (by rfl) ⟨2756159, by rfl⟩ : syracuseStep 3674879 = 5512319) B5512319
theorem B1634579 : Blo 223812 1634579 := bstep (se 1 (by rfl) ⟨1225934, by rfl⟩ : syracuseStep 1634579 = 2451869) B2451869
theorem B1089719 : Blo 223812 1089719 := bstep (se 1 (by rfl) ⟨817289, by rfl⟩ : syracuseStep 1089719 = 1634579) B1634579
theorem B765179 : Blo 223812 765179 := bstep (se 1 (by rfl) ⟨573884, by rfl⟩ : syracuseStep 765179 = 1147769) B1147769
theorem B2449919 : Blo 223812 2449919 := bstep (se 1 (by rfl) ⟨1837439, by rfl⟩ : syracuseStep 2449919 = 3674879) B3674879
theorem B726479 : Blo 223812 726479 := bstep (se 1 (by rfl) ⟨544859, by rfl⟩ : syracuseStep 726479 = 1089719) B1089719
theorem B510119 : Blo 223812 510119 := bstep (se 1 (by rfl) ⟨382589, by rfl⟩ : syracuseStep 510119 = 765179) B765179
theorem B1633279 : Blo 223812 1633279 := bstep (se 1 (by rfl) ⟨1224959, by rfl⟩ : syracuseStep 1633279 = 2449919) B2449919
theorem B340079 : Blo 223812 340079 := bstep (se 1 (by rfl) ⟨255059, by rfl⟩ : syracuseStep 340079 = 510119) B510119
theorem B2177705 : Blo 223812 2177705 := bstep (se 2 (by rfl) ⟨816639, by rfl⟩ : syracuseStep 2177705 = 1633279) B1633279
theorem B484319 : Blo 223812 484319 := bstep (se 1 (by rfl) ⟨363239, by rfl⟩ : syracuseStep 484319 = 726479) B726479
theorem B1451803 : Blo 223812 1451803 := bstep (se 1 (by rfl) ⟨1088852, by rfl⟩ : syracuseStep 1451803 = 2177705) B2177705
theorem B322879 : Blo 223812 322879 := bstep (se 1 (by rfl) ⟨242159, by rfl⟩ : syracuseStep 322879 = 484319) B484319
theorem B226719 : Blo 223812 226719 := bstep (se 1 (by rfl) ⟨170039, by rfl⟩ : syracuseStep 226719 = 340079) B340079
theorem B1935737 : Blo 223812 1935737 := bstep (se 2 (by rfl) ⟨725901, by rfl⟩ : syracuseStep 1935737 = 1451803) B1451803
theorem B430505 : Blo 223812 430505 := bstep (se 2 (by rfl) ⟨161439, by rfl⟩ : syracuseStep 430505 = 322879) B322879
theorem B1290491 : Blo 223812 1290491 := bstep (se 1 (by rfl) ⟨967868, by rfl⟩ : syracuseStep 1290491 = 1935737) B1935737
theorem B287003 : Blo 223812 287003 := bstep (se 1 (by rfl) ⟨215252, by rfl⟩ : syracuseStep 287003 = 430505) B430505
theorem B860327 : Blo 223812 860327 := bstep (se 1 (by rfl) ⟨645245, by rfl⟩ : syracuseStep 860327 = 1290491) B1290491
theorem B765341 : Blo 223812 765341 := bstep (se 3 (by rfl) ⟨143501, by rfl⟩ : syracuseStep 765341 = 287003) B287003
theorem B573551 : Blo 223812 573551 := bstep (se 1 (by rfl) ⟨430163, by rfl⟩ : syracuseStep 573551 = 860327) B860327
theorem B510227 : Blo 223812 510227 := bstep (se 1 (by rfl) ⟨382670, by rfl⟩ : syracuseStep 510227 = 765341) B765341
theorem B340151 : Blo 223812 340151 := bstep (se 1 (by rfl) ⟨255113, by rfl⟩ : syracuseStep 340151 = 510227) B510227
theorem B382367 : Blo 223812 382367 := bstep (se 1 (by rfl) ⟨286775, by rfl⟩ : syracuseStep 382367 = 573551) B573551
theorem B254911 : Blo 223812 254911 := bstep (se 1 (by rfl) ⟨191183, by rfl⟩ : syracuseStep 254911 = 382367) B382367
theorem B226767 : Blo 223812 226767 := bstep (se 1 (by rfl) ⟨170075, by rfl⟩ : syracuseStep 226767 = 340151) B340151
theorem B339881 : Blo 223812 339881 := bstep (se 2 (by rfl) ⟨127455, by rfl⟩ : syracuseStep 339881 = 254911) B254911
theorem B226587 : Blo 223812 226587 := bstep (se 1 (by rfl) ⟨169940, by rfl⟩ : syracuseStep 226587 = 339881) B339881

theorem C0 (j : ℕ) (h1 : 55953 ≤ j) (h2 : j ≤ 56652) : Blo 223812 (4 * j + 3) := by
  interval_cases j
  · exact B223815
  · exact B223819
  · exact B223823
  · exact B223827
  · exact B223831
  · exact B223835
  · exact B223839
  · exact B223843
  · exact B223847
  · exact B223851
  · exact B223855
  · exact B223859
  · exact B223863
  · exact B223867
  · exact B223871
  · exact B223875
  · exact B223879
  · exact B223883
  · exact B223887
  · exact B223891
  · exact B223895
  · exact B223899
  · exact B223903
  · exact B223907
  · exact B223911
  · exact B223915
  · exact B223919
  · exact B223923
  · exact B223927
  · exact B223931
  · exact B223935
  · exact B223939
  · exact B223943
  · exact B223947
  · exact B223951
  · exact B223955
  · exact B223959
  · exact B223963
  · exact B223967
  · exact B223971
  · exact B223975
  · exact B223979
  · exact B223983
  · exact B223987
  · exact B223991
  · exact B223995
  · exact B223999
  · exact B224003
  · exact B224007
  · exact B224011
  · exact B224015
  · exact B224019
  · exact B224023
  · exact B224027
  · exact B224031
  · exact B224035
  · exact B224039
  · exact B224043
  · exact B224047
  · exact B224051
  · exact B224055
  · exact B224059
  · exact B224063
  · exact B224067
  · exact B224071
  · exact B224075
  · exact B224079
  · exact B224083
  · exact B224087
  · exact B224091
  · exact B224095
  · exact B224099
  · exact B224103
  · exact B224107
  · exact B224111
  · exact B224115
  · exact B224119
  · exact B224123
  · exact B224127
  · exact B224131
  · exact B224135
  · exact B224139
  · exact B224143
  · exact B224147
  · exact B224151
  · exact B224155
  · exact B224159
  · exact B224163
  · exact B224167
  · exact B224171
  · exact B224175
  · exact B224179
  · exact B224183
  · exact B224187
  · exact B224191
  · exact B224195
  · exact B224199
  · exact B224203
  · exact B224207
  · exact B224211
  · exact B224215
  · exact B224219
  · exact B224223
  · exact B224227
  · exact B224231
  · exact B224235
  · exact B224239
  · exact B224243
  · exact B224247
  · exact B224251
  · exact B224255
  · exact B224259
  · exact B224263
  · exact B224267
  · exact B224271
  · exact B224275
  · exact B224279
  · exact B224283
  · exact B224287
  · exact B224291
  · exact B224295
  · exact B224299
  · exact B224303
  · exact B224307
  · exact B224311
  · exact B224315
  · exact B224319
  · exact B224323
  · exact B224327
  · exact B224331
  · exact B224335
  · exact B224339
  · exact B224343
  · exact B224347
  · exact B224351
  · exact B224355
  · exact B224359
  · exact B224363
  · exact B224367
  · exact B224371
  · exact B224375
  · exact B224379
  · exact B224383
  · exact B224387
  · exact B224391
  · exact B224395
  · exact B224399
  · exact B224403
  · exact B224407
  · exact B224411
  · exact B224415
  · exact B224419
  · exact B224423
  · exact B224427
  · exact B224431
  · exact B224435
  · exact B224439
  · exact B224443
  · exact B224447
  · exact B224451
  · exact B224455
  · exact B224459
  · exact B224463
  · exact B224467
  · exact B224471
  · exact B224475
  · exact B224479
  · exact B224483
  · exact B224487
  · exact B224491
  · exact B224495
  · exact B224499
  · exact B224503
  · exact B224507
  · exact B224511
  · exact B224515
  · exact B224519
  · exact B224523
  · exact B224527
  · exact B224531
  · exact B224535
  · exact B224539
  · exact B224543
  · exact B224547
  · exact B224551
  · exact B224555
  · exact B224559
  · exact B224563
  · exact B224567
  · exact B224571
  · exact B224575
  · exact B224579
  · exact B224583
  · exact B224587
  · exact B224591
  · exact B224595
  · exact B224599
  · exact B224603
  · exact B224607
  · exact B224611
  · exact B224615
  · exact B224619
  · exact B224623
  · exact B224627
  · exact B224631
  · exact B224635
  · exact B224639
  · exact B224643
  · exact B224647
  · exact B224651
  · exact B224655
  · exact B224659
  · exact B224663
  · exact B224667
  · exact B224671
  · exact B224675
  · exact B224679
  · exact B224683
  · exact B224687
  · exact B224691
  · exact B224695
  · exact B224699
  · exact B224703
  · exact B224707
  · exact B224711
  · exact B224715
  · exact B224719
  · exact B224723
  · exact B224727
  · exact B224731
  · exact B224735
  · exact B224739
  · exact B224743
  · exact B224747
  · exact B224751
  · exact B224755
  · exact B224759
  · exact B224763
  · exact B224767
  · exact B224771
  · exact B224775
  · exact B224779
  · exact B224783
  · exact B224787
  · exact B224791
  · exact B224795
  · exact B224799
  · exact B224803
  · exact B224807
  · exact B224811
  · exact B224815
  · exact B224819
  · exact B224823
  · exact B224827
  · exact B224831
  · exact B224835
  · exact B224839
  · exact B224843
  · exact B224847
  · exact B224851
  · exact B224855
  · exact B224859
  · exact B224863
  · exact B224867
  · exact B224871
  · exact B224875
  · exact B224879
  · exact B224883
  · exact B224887
  · exact B224891
  · exact B224895
  · exact B224899
  · exact B224903
  · exact B224907
  · exact B224911
  · exact B224915
  · exact B224919
  · exact B224923
  · exact B224927
  · exact B224931
  · exact B224935
  · exact B224939
  · exact B224943
  · exact B224947
  · exact B224951
  · exact B224955
  · exact B224959
  · exact B224963
  · exact B224967
  · exact B224971
  · exact B224975
  · exact B224979
  · exact B224983
  · exact B224987
  · exact B224991
  · exact B224995
  · exact B224999
  · exact B225003
  · exact B225007
  · exact B225011
  · exact B225015
  · exact B225019
  · exact B225023
  · exact B225027
  · exact B225031
  · exact B225035
  · exact B225039
  · exact B225043
  · exact B225047
  · exact B225051
  · exact B225055
  · exact B225059
  · exact B225063
  · exact B225067
  · exact B225071
  · exact B225075
  · exact B225079
  · exact B225083
  · exact B225087
  · exact B225091
  · exact B225095
  · exact B225099
  · exact B225103
  · exact B225107
  · exact B225111
  · exact B225115
  · exact B225119
  · exact B225123
  · exact B225127
  · exact B225131
  · exact B225135
  · exact B225139
  · exact B225143
  · exact B225147
  · exact B225151
  · exact B225155
  · exact B225159
  · exact B225163
  · exact B225167
  · exact B225171
  · exact B225175
  · exact B225179
  · exact B225183
  · exact B225187
  · exact B225191
  · exact B225195
  · exact B225199
  · exact B225203
  · exact B225207
  · exact B225211
  · exact B225215
  · exact B225219
  · exact B225223
  · exact B225227
  · exact B225231
  · exact B225235
  · exact B225239
  · exact B225243
  · exact B225247
  · exact B225251
  · exact B225255
  · exact B225259
  · exact B225263
  · exact B225267
  · exact B225271
  · exact B225275
  · exact B225279
  · exact B225283
  · exact B225287
  · exact B225291
  · exact B225295
  · exact B225299
  · exact B225303
  · exact B225307
  · exact B225311
  · exact B225315
  · exact B225319
  · exact B225323
  · exact B225327
  · exact B225331
  · exact B225335
  · exact B225339
  · exact B225343
  · exact B225347
  · exact B225351
  · exact B225355
  · exact B225359
  · exact B225363
  · exact B225367
  · exact B225371
  · exact B225375
  · exact B225379
  · exact B225383
  · exact B225387
  · exact B225391
  · exact B225395
  · exact B225399
  · exact B225403
  · exact B225407
  · exact B225411
  · exact B225415
  · exact B225419
  · exact B225423
  · exact B225427
  · exact B225431
  · exact B225435
  · exact B225439
  · exact B225443
  · exact B225447
  · exact B225451
  · exact B225455
  · exact B225459
  · exact B225463
  · exact B225467
  · exact B225471
  · exact B225475
  · exact B225479
  · exact B225483
  · exact B225487
  · exact B225491
  · exact B225495
  · exact B225499
  · exact B225503
  · exact B225507
  · exact B225511
  · exact B225515
  · exact B225519
  · exact B225523
  · exact B225527
  · exact B225531
  · exact B225535
  · exact B225539
  · exact B225543
  · exact B225547
  · exact B225551
  · exact B225555
  · exact B225559
  · exact B225563
  · exact B225567
  · exact B225571
  · exact B225575
  · exact B225579
  · exact B225583
  · exact B225587
  · exact B225591
  · exact B225595
  · exact B225599
  · exact B225603
  · exact B225607
  · exact B225611
  · exact B225615
  · exact B225619
  · exact B225623
  · exact B225627
  · exact B225631
  · exact B225635
  · exact B225639
  · exact B225643
  · exact B225647
  · exact B225651
  · exact B225655
  · exact B225659
  · exact B225663
  · exact B225667
  · exact B225671
  · exact B225675
  · exact B225679
  · exact B225683
  · exact B225687
  · exact B225691
  · exact B225695
  · exact B225699
  · exact B225703
  · exact B225707
  · exact B225711
  · exact B225715
  · exact B225719
  · exact B225723
  · exact B225727
  · exact B225731
  · exact B225735
  · exact B225739
  · exact B225743
  · exact B225747
  · exact B225751
  · exact B225755
  · exact B225759
  · exact B225763
  · exact B225767
  · exact B225771
  · exact B225775
  · exact B225779
  · exact B225783
  · exact B225787
  · exact B225791
  · exact B225795
  · exact B225799
  · exact B225803
  · exact B225807
  · exact B225811
  · exact B225815
  · exact B225819
  · exact B225823
  · exact B225827
  · exact B225831
  · exact B225835
  · exact B225839
  · exact B225843
  · exact B225847
  · exact B225851
  · exact B225855
  · exact B225859
  · exact B225863
  · exact B225867
  · exact B225871
  · exact B225875
  · exact B225879
  · exact B225883
  · exact B225887
  · exact B225891
  · exact B225895
  · exact B225899
  · exact B225903
  · exact B225907
  · exact B225911
  · exact B225915
  · exact B225919
  · exact B225923
  · exact B225927
  · exact B225931
  · exact B225935
  · exact B225939
  · exact B225943
  · exact B225947
  · exact B225951
  · exact B225955
  · exact B225959
  · exact B225963
  · exact B225967
  · exact B225971
  · exact B225975
  · exact B225979
  · exact B225983
  · exact B225987
  · exact B225991
  · exact B225995
  · exact B225999
  · exact B226003
  · exact B226007
  · exact B226011
  · exact B226015
  · exact B226019
  · exact B226023
  · exact B226027
  · exact B226031
  · exact B226035
  · exact B226039
  · exact B226043
  · exact B226047
  · exact B226051
  · exact B226055
  · exact B226059
  · exact B226063
  · exact B226067
  · exact B226071
  · exact B226075
  · exact B226079
  · exact B226083
  · exact B226087
  · exact B226091
  · exact B226095
  · exact B226099
  · exact B226103
  · exact B226107
  · exact B226111
  · exact B226115
  · exact B226119
  · exact B226123
  · exact B226127
  · exact B226131
  · exact B226135
  · exact B226139
  · exact B226143
  · exact B226147
  · exact B226151
  · exact B226155
  · exact B226159
  · exact B226163
  · exact B226167
  · exact B226171
  · exact B226175
  · exact B226179
  · exact B226183
  · exact B226187
  · exact B226191
  · exact B226195
  · exact B226199
  · exact B226203
  · exact B226207
  · exact B226211
  · exact B226215
  · exact B226219
  · exact B226223
  · exact B226227
  · exact B226231
  · exact B226235
  · exact B226239
  · exact B226243
  · exact B226247
  · exact B226251
  · exact B226255
  · exact B226259
  · exact B226263
  · exact B226267
  · exact B226271
  · exact B226275
  · exact B226279
  · exact B226283
  · exact B226287
  · exact B226291
  · exact B226295
  · exact B226299
  · exact B226303
  · exact B226307
  · exact B226311
  · exact B226315
  · exact B226319
  · exact B226323
  · exact B226327
  · exact B226331
  · exact B226335
  · exact B226339
  · exact B226343
  · exact B226347
  · exact B226351
  · exact B226355
  · exact B226359
  · exact B226363
  · exact B226367
  · exact B226371
  · exact B226375
  · exact B226379
  · exact B226383
  · exact B226387
  · exact B226391
  · exact B226395
  · exact B226399
  · exact B226403
  · exact B226407
  · exact B226411
  · exact B226415
  · exact B226419
  · exact B226423
  · exact B226427
  · exact B226431
  · exact B226435
  · exact B226439
  · exact B226443
  · exact B226447
  · exact B226451
  · exact B226455
  · exact B226459
  · exact B226463
  · exact B226467
  · exact B226471
  · exact B226475
  · exact B226479
  · exact B226483
  · exact B226487
  · exact B226491
  · exact B226495
  · exact B226499
  · exact B226503
  · exact B226507
  · exact B226511
  · exact B226515
  · exact B226519
  · exact B226523
  · exact B226527
  · exact B226531
  · exact B226535
  · exact B226539
  · exact B226543
  · exact B226547
  · exact B226551
  · exact B226555
  · exact B226559
  · exact B226563
  · exact B226567
  · exact B226571
  · exact B226575
  · exact B226579
  · exact B226583
  · exact B226587
  · exact B226591
  · exact B226595
  · exact B226599
  · exact B226603
  · exact B226607
  · exact B226611

theorem C1 (j : ℕ) (h1 : 56653 ≤ j) (h2 : j ≤ 56952) : Blo 223812 (4 * j + 3) := by
  interval_cases j
  · exact B226615
  · exact B226619
  · exact B226623
  · exact B226627
  · exact B226631
  · exact B226635
  · exact B226639
  · exact B226643
  · exact B226647
  · exact B226651
  · exact B226655
  · exact B226659
  · exact B226663
  · exact B226667
  · exact B226671
  · exact B226675
  · exact B226679
  · exact B226683
  · exact B226687
  · exact B226691
  · exact B226695
  · exact B226699
  · exact B226703
  · exact B226707
  · exact B226711
  · exact B226715
  · exact B226719
  · exact B226723
  · exact B226727
  · exact B226731
  · exact B226735
  · exact B226739
  · exact B226743
  · exact B226747
  · exact B226751
  · exact B226755
  · exact B226759
  · exact B226763
  · exact B226767
  · exact B226771
  · exact B226775
  · exact B226779
  · exact B226783
  · exact B226787
  · exact B226791
  · exact B226795
  · exact B226799
  · exact B226803
  · exact B226807
  · exact B226811
  · exact B226815
  · exact B226819
  · exact B226823
  · exact B226827
  · exact B226831
  · exact B226835
  · exact B226839
  · exact B226843
  · exact B226847
  · exact B226851
  · exact B226855
  · exact B226859
  · exact B226863
  · exact B226867
  · exact B226871
  · exact B226875
  · exact B226879
  · exact B226883
  · exact B226887
  · exact B226891
  · exact B226895
  · exact B226899
  · exact B226903
  · exact B226907
  · exact B226911
  · exact B226915
  · exact B226919
  · exact B226923
  · exact B226927
  · exact B226931
  · exact B226935
  · exact B226939
  · exact B226943
  · exact B226947
  · exact B226951
  · exact B226955
  · exact B226959
  · exact B226963
  · exact B226967
  · exact B226971
  · exact B226975
  · exact B226979
  · exact B226983
  · exact B226987
  · exact B226991
  · exact B226995
  · exact B226999
  · exact B227003
  · exact B227007
  · exact B227011
  · exact B227015
  · exact B227019
  · exact B227023
  · exact B227027
  · exact B227031
  · exact B227035
  · exact B227039
  · exact B227043
  · exact B227047
  · exact B227051
  · exact B227055
  · exact B227059
  · exact B227063
  · exact B227067
  · exact B227071
  · exact B227075
  · exact B227079
  · exact B227083
  · exact B227087
  · exact B227091
  · exact B227095
  · exact B227099
  · exact B227103
  · exact B227107
  · exact B227111
  · exact B227115
  · exact B227119
  · exact B227123
  · exact B227127
  · exact B227131
  · exact B227135
  · exact B227139
  · exact B227143
  · exact B227147
  · exact B227151
  · exact B227155
  · exact B227159
  · exact B227163
  · exact B227167
  · exact B227171
  · exact B227175
  · exact B227179
  · exact B227183
  · exact B227187
  · exact B227191
  · exact B227195
  · exact B227199
  · exact B227203
  · exact B227207
  · exact B227211
  · exact B227215
  · exact B227219
  · exact B227223
  · exact B227227
  · exact B227231
  · exact B227235
  · exact B227239
  · exact B227243
  · exact B227247
  · exact B227251
  · exact B227255
  · exact B227259
  · exact B227263
  · exact B227267
  · exact B227271
  · exact B227275
  · exact B227279
  · exact B227283
  · exact B227287
  · exact B227291
  · exact B227295
  · exact B227299
  · exact B227303
  · exact B227307
  · exact B227311
  · exact B227315
  · exact B227319
  · exact B227323
  · exact B227327
  · exact B227331
  · exact B227335
  · exact B227339
  · exact B227343
  · exact B227347
  · exact B227351
  · exact B227355
  · exact B227359
  · exact B227363
  · exact B227367
  · exact B227371
  · exact B227375
  · exact B227379
  · exact B227383
  · exact B227387
  · exact B227391
  · exact B227395
  · exact B227399
  · exact B227403
  · exact B227407
  · exact B227411
  · exact B227415
  · exact B227419
  · exact B227423
  · exact B227427
  · exact B227431
  · exact B227435
  · exact B227439
  · exact B227443
  · exact B227447
  · exact B227451
  · exact B227455
  · exact B227459
  · exact B227463
  · exact B227467
  · exact B227471
  · exact B227475
  · exact B227479
  · exact B227483
  · exact B227487
  · exact B227491
  · exact B227495
  · exact B227499
  · exact B227503
  · exact B227507
  · exact B227511
  · exact B227515
  · exact B227519
  · exact B227523
  · exact B227527
  · exact B227531
  · exact B227535
  · exact B227539
  · exact B227543
  · exact B227547
  · exact B227551
  · exact B227555
  · exact B227559
  · exact B227563
  · exact B227567
  · exact B227571
  · exact B227575
  · exact B227579
  · exact B227583
  · exact B227587
  · exact B227591
  · exact B227595
  · exact B227599
  · exact B227603
  · exact B227607
  · exact B227611
  · exact B227615
  · exact B227619
  · exact B227623
  · exact B227627
  · exact B227631
  · exact B227635
  · exact B227639
  · exact B227643
  · exact B227647
  · exact B227651
  · exact B227655
  · exact B227659
  · exact B227663
  · exact B227667
  · exact B227671
  · exact B227675
  · exact B227679
  · exact B227683
  · exact B227687
  · exact B227691
  · exact B227695
  · exact B227699
  · exact B227703
  · exact B227707
  · exact B227711
  · exact B227715
  · exact B227719
  · exact B227723
  · exact B227727
  · exact B227731
  · exact B227735
  · exact B227739
  · exact B227743
  · exact B227747
  · exact B227751
  · exact B227755
  · exact B227759
  · exact B227763
  · exact B227767
  · exact B227771
  · exact B227775
  · exact B227779
  · exact B227783
  · exact B227787
  · exact B227791
  · exact B227795
  · exact B227799
  · exact B227803
  · exact B227807
  · exact B227811

theorem solution (m : ℕ) (hlo : 223812 ≤ m) (hhi : m ≤ 227812) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 55953 ≤ j := by omega
    have hj2 : j ≤ 56952 := by omega
    have hb : Blo 223812 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 56653 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
