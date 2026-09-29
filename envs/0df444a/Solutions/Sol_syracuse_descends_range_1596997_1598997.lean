-- Prove2me | solution 1 for syracuse_descends_range_1596997_1598997
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:09:26.168692+00:00
-- url     : https://prove2.me/submissions/039f02f6-2c63-46d3-b6d9-79c39877681a

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


theorem B4046861 : Blo 1596997 4046861 := bbase (se 3 (by rfl) ⟨758786, by rfl⟩ : syracuseStep 4046861 = 1517573) (by norm_num)
theorem B3596309 : Blo 1596997 3596309 := bbase (se 6 (by rfl) ⟨84288, by rfl⟩ : syracuseStep 3596309 = 168577) (by norm_num)
theorem B2023481 : Blo 1596997 2023481 := bbase (se 2 (by rfl) ⟨758805, by rfl⟩ : syracuseStep 2023481 = 1517611) (by norm_num)
theorem B2695261 : Blo 1596997 2695261 := bbase (se 3 (by rfl) ⟨505361, by rfl⟩ : syracuseStep 2695261 = 1010723) (by norm_num)
theorem B3596381 : Blo 1596997 3596381 := bbase (se 3 (by rfl) ⟨674321, by rfl⟩ : syracuseStep 3596381 = 1348643) (by norm_num)
theorem B2023537 : Blo 1596997 2023537 := bbase (se 2 (by rfl) ⟨758826, by rfl⟩ : syracuseStep 2023537 = 1517653) (by norm_num)
theorem B9101429 : Blo 1596997 9101429 := bbase (se 5 (by rfl) ⟨426629, by rfl⟩ : syracuseStep 9101429 = 853259) (by norm_num)
theorem B3596453 : Blo 1596997 3596453 := bbase (se 4 (by rfl) ⟨337167, by rfl⟩ : syracuseStep 3596453 = 674335) (by norm_num)
theorem B2695349 : Blo 1596997 2695349 := bbase (se 5 (by rfl) ⟨126344, by rfl⟩ : syracuseStep 2695349 = 252689) (by norm_num)
theorem B2023633 : Blo 1596997 2023633 := bbase (se 2 (by rfl) ⟨758862, by rfl⟩ : syracuseStep 2023633 = 1517725) (by norm_num)
theorem B5390549 : Blo 1596997 5390549 := bbase (se 7 (by rfl) ⟨63170, by rfl⟩ : syracuseStep 5390549 = 126341) (by norm_num)
theorem B8536277 : Blo 1596997 8536277 := bbase (se 7 (by rfl) ⟨100034, by rfl⟩ : syracuseStep 8536277 = 200069) (by norm_num)
theorem B3596525 : Blo 1596997 3596525 := bbase (se 3 (by rfl) ⟨674348, by rfl⟩ : syracuseStep 3596525 = 1348697) (by norm_num)
theorem B8642837 : Blo 1596997 8642837 := bbase (se 6 (by rfl) ⟨202566, by rfl⟩ : syracuseStep 8642837 = 405133) (by norm_num)
theorem B6070565 : Blo 1596997 6070565 := bbase (se 4 (by rfl) ⟨569115, by rfl⟩ : syracuseStep 6070565 = 1138231) (by norm_num)
theorem B2695477 : Blo 1596997 2695477 := bbase (se 5 (by rfl) ⟨126350, by rfl⟩ : syracuseStep 2695477 = 252701) (by norm_num)
theorem B3596597 : Blo 1596997 3596597 := bbase (se 5 (by rfl) ⟨168590, by rfl⟩ : syracuseStep 3596597 = 337181) (by norm_num)
theorem B13844789 : Blo 1596997 13844789 := bbase (se 5 (by rfl) ⟨648974, by rfl⟩ : syracuseStep 13844789 = 1297949) (by norm_num)
theorem B8094005 : Blo 1596997 8094005 := bbase (se 5 (by rfl) ⟨379406, by rfl⟩ : syracuseStep 8094005 = 758813) (by norm_num)
theorem B1728857 : Blo 1596997 1728857 := bbase (se 2 (by rfl) ⟨648321, by rfl⟩ : syracuseStep 1728857 = 1296643) (by norm_num)
theorem B4047205 : Blo 1596997 4047205 := bbase (se 4 (by rfl) ⟨379425, by rfl⟩ : syracuseStep 4047205 = 758851) (by norm_num)
theorem B3596669 : Blo 1596997 3596669 := bbase (se 3 (by rfl) ⟨674375, by rfl⟩ : syracuseStep 3596669 = 1348751) (by norm_num)
theorem B2695565 : Blo 1596997 2695565 := bbase (se 3 (by rfl) ⟨505418, by rfl⟩ : syracuseStep 2695565 = 1010837) (by norm_num)
theorem B3596741 : Blo 1596997 3596741 := bbase (se 4 (by rfl) ⟨337194, by rfl⟩ : syracuseStep 3596741 = 674389) (by norm_num)
theorem B4047317 : Blo 1596997 4047317 := bbase (se 7 (by rfl) ⟨47429, by rfl⟩ : syracuseStep 4047317 = 94859) (by norm_num)
theorem B5620229 : Blo 1596997 5620229 := bbase (se 4 (by rfl) ⟨526896, by rfl⟩ : syracuseStep 5620229 = 1053793) (by norm_num)
theorem B2695693 : Blo 1596997 2695693 := bbase (se 3 (by rfl) ⟨505442, by rfl⟩ : syracuseStep 2695693 = 1010885) (by norm_num)
theorem B3596813 : Blo 1596997 3596813 := bbase (se 3 (by rfl) ⟨674402, by rfl⟩ : syracuseStep 3596813 = 1348805) (by norm_num)
theorem B36905557 : Blo 1596997 36905557 := bbase (se 8 (by rfl) ⟨216243, by rfl⟩ : syracuseStep 36905557 = 432487) (by norm_num)
theorem B3596885 : Blo 1596997 3596885 := bbase (se 8 (by rfl) ⟨21075, by rfl⟩ : syracuseStep 3596885 = 42151) (by norm_num)
theorem B2695781 : Blo 1596997 2695781 := bbase (se 4 (by rfl) ⟨252729, by rfl⟩ : syracuseStep 2695781 = 505459) (by norm_num)
theorem B5390981 : Blo 1596997 5390981 := bbase (se 4 (by rfl) ⟨505404, by rfl⟩ : syracuseStep 5390981 = 1010809) (by norm_num)
theorem B1729165 : Blo 1596997 1729165 := bbase (se 3 (by rfl) ⟨324218, by rfl⟩ : syracuseStep 1729165 = 648437) (by norm_num)
theorem B3596957 : Blo 1596997 3596957 := bbase (se 3 (by rfl) ⟨674429, by rfl⟩ : syracuseStep 3596957 = 1348859) (by norm_num)
theorem B5186261 : Blo 1596997 5186261 := bbase (se 7 (by rfl) ⟨60776, by rfl⟩ : syracuseStep 5186261 = 121553) (by norm_num)
theorem B8086229 : Blo 1596997 8086229 := bbase (se 7 (by rfl) ⟨94760, by rfl⟩ : syracuseStep 8086229 = 189521) (by norm_num)
theorem B2695909 : Blo 1596997 2695909 := bbase (se 4 (by rfl) ⟨252741, by rfl⟩ : syracuseStep 2695909 = 505483) (by norm_num)
theorem B3597029 : Blo 1596997 3597029 := bbase (se 4 (by rfl) ⟨337221, by rfl⟩ : syracuseStep 3597029 = 674443) (by norm_num)
theorem B3031805 : Blo 1596997 3031805 := bbase (se 3 (by rfl) ⟨568463, by rfl⟩ : syracuseStep 3031805 = 1136927) (by norm_num)
theorem B3597101 : Blo 1596997 3597101 := bbase (se 3 (by rfl) ⟨674456, by rfl⟩ : syracuseStep 3597101 = 1348913) (by norm_num)
theorem B2695997 : Blo 1596997 2695997 := bbase (se 3 (by rfl) ⟨505499, by rfl⟩ : syracuseStep 2695997 = 1010999) (by norm_num)
theorem B3597173 : Blo 1596997 3597173 := bbase (se 5 (by rfl) ⟨168617, by rfl⟩ : syracuseStep 3597173 = 337235) (by norm_num)
theorem B2696125 : Blo 1596997 2696125 := bbase (se 3 (by rfl) ⟨505523, by rfl⟩ : syracuseStep 2696125 = 1011047) (by norm_num)
theorem B3597245 : Blo 1596997 3597245 := bbase (se 3 (by rfl) ⟨674483, by rfl⟩ : syracuseStep 3597245 = 1348967) (by norm_num)
theorem B5465029 : Blo 1596997 5465029 := bbase (se 4 (by rfl) ⟨512346, by rfl⟩ : syracuseStep 5465029 = 1024693) (by norm_num)
theorem B3597317 : Blo 1596997 3597317 := bbase (se 4 (by rfl) ⟨337248, by rfl⟩ : syracuseStep 3597317 = 674497) (by norm_num)
theorem B2696213 : Blo 1596997 2696213 := bbase (se 6 (by rfl) ⟨63192, by rfl⟩ : syracuseStep 2696213 = 126385) (by norm_num)
theorem B3032093 : Blo 1596997 3032093 := bbase (se 3 (by rfl) ⟨568517, by rfl⟩ : syracuseStep 3032093 = 1137035) (by norm_num)
theorem B5391413 : Blo 1596997 5391413 := bbase (se 5 (by rfl) ⟨252722, by rfl⟩ : syracuseStep 5391413 = 505445) (by norm_num)
theorem B3597389 : Blo 1596997 3597389 := bbase (se 3 (by rfl) ⟨674510, by rfl⟩ : syracuseStep 3597389 = 1349021) (by norm_num)
theorem B5121157 : Blo 1596997 5121157 := bbase (se 4 (by rfl) ⟨480108, by rfl⟩ : syracuseStep 5121157 = 960217) (by norm_num)
theorem B6915221 : Blo 1596997 6915221 := bbase (se 6 (by rfl) ⟨162075, by rfl⟩ : syracuseStep 6915221 = 324151) (by norm_num)
theorem B2696341 : Blo 1596997 2696341 := bbase (se 6 (by rfl) ⟨63195, by rfl⟩ : syracuseStep 2696341 = 126391) (by norm_num)
theorem B3597461 : Blo 1596997 3597461 := bbase (se 6 (by rfl) ⟨84315, by rfl⟩ : syracuseStep 3597461 = 168631) (by norm_num)
theorem B4547765 : Blo 1596997 4547765 := bbase (se 5 (by rfl) ⟨213176, by rfl⟩ : syracuseStep 4547765 = 426353) (by norm_num)
theorem B3032245 : Blo 1596997 3032245 := bbase (se 5 (by rfl) ⟨142136, by rfl⟩ : syracuseStep 3032245 = 284273) (by norm_num)
theorem B3597533 : Blo 1596997 3597533 := bbase (se 3 (by rfl) ⟨674537, by rfl⟩ : syracuseStep 3597533 = 1349075) (by norm_num)
theorem B2696429 : Blo 1596997 2696429 := bbase (se 3 (by rfl) ⟨505580, by rfl⟩ : syracuseStep 2696429 = 1011161) (by norm_num)
theorem B3646709 : Blo 1596997 3646709 := bbase (se 5 (by rfl) ⟨170939, by rfl⟩ : syracuseStep 3646709 = 341879) (by norm_num)
theorem B3597605 : Blo 1596997 3597605 := bbase (se 4 (by rfl) ⟨337275, by rfl⟩ : syracuseStep 3597605 = 674551) (by norm_num)
theorem B2188589 : Blo 1596997 2188589 := bbase (se 3 (by rfl) ⟨410360, by rfl⟩ : syracuseStep 2188589 = 820721) (by norm_num)
theorem B2696557 : Blo 1596997 2696557 := bbase (se 3 (by rfl) ⟨505604, by rfl⟩ : syracuseStep 2696557 = 1011209) (by norm_num)
theorem B3597677 : Blo 1596997 3597677 := bbase (se 3 (by rfl) ⟨674564, by rfl⟩ : syracuseStep 3597677 = 1349129) (by norm_num)
theorem B2770309 : Blo 1596997 2770309 := bbase (se 4 (by rfl) ⟨259716, by rfl⟩ : syracuseStep 2770309 = 519433) (by norm_num)
theorem B2696645 : Blo 1596997 2696645 := bbase (se 4 (by rfl) ⟨252810, by rfl⟩ : syracuseStep 2696645 = 505621) (by norm_num)
theorem B1705433 : Blo 1596997 1705433 := bbase (se 2 (by rfl) ⟨639537, by rfl⟩ : syracuseStep 1705433 = 1279075) (by norm_num)
theorem B3032549 : Blo 1596997 3032549 := bbase (se 4 (by rfl) ⟨284301, by rfl⟩ : syracuseStep 3032549 = 568603) (by norm_num)
theorem B5391845 : Blo 1596997 5391845 := bbase (se 4 (by rfl) ⟨505485, by rfl⟩ : syracuseStep 5391845 = 1010971) (by norm_num)
theorem B1705493 : Blo 1596997 1705493 := bbase (se 6 (by rfl) ⟨39972, by rfl⟩ : syracuseStep 1705493 = 79945) (by norm_num)
theorem B2696773 : Blo 1596997 2696773 := bbase (se 4 (by rfl) ⟨252822, by rfl⟩ : syracuseStep 2696773 = 505645) (by norm_num)
theorem B5121605 : Blo 1596997 5121605 := bbase (se 4 (by rfl) ⟨480150, by rfl⟩ : syracuseStep 5121605 = 960301) (by norm_num)
theorem B1705621 : Blo 1596997 1705621 := bbase (se 6 (by rfl) ⟨39975, by rfl⟩ : syracuseStep 1705621 = 79951) (by norm_num)
theorem B2696861 : Blo 1596997 2696861 := bbase (se 3 (by rfl) ⟨505661, by rfl⟩ : syracuseStep 2696861 = 1011323) (by norm_num)
theorem B2049709 : Blo 1596997 2049709 := bbase (se 3 (by rfl) ⟨384320, by rfl⟩ : syracuseStep 2049709 = 768641) (by norm_num)
theorem B4318933 : Blo 1596997 4318933 := bbase (se 7 (by rfl) ⟨50612, by rfl⟩ : syracuseStep 4318933 = 101225) (by norm_num)
theorem B59926229 : Blo 1596997 59926229 := bbase (se 7 (by rfl) ⟨702260, by rfl⟩ : syracuseStep 59926229 = 1404521) (by norm_num)
theorem B1730273 : Blo 1596997 1730273 := bbase (se 2 (by rfl) ⟨648852, by rfl⟩ : syracuseStep 1730273 = 1297705) (by norm_num)
theorem B2696989 : Blo 1596997 2696989 := bbase (se 3 (by rfl) ⟨505685, by rfl⟩ : syracuseStep 2696989 = 1011371) (by norm_num)
theorem B4548437 : Blo 1596997 4548437 := bbase (se 9 (by rfl) ⟨13325, by rfl⟩ : syracuseStep 4548437 = 26651) (by norm_num)
theorem B3237749 : Blo 1596997 3237749 := bbase (se 5 (by rfl) ⟨151769, by rfl⟩ : syracuseStep 3237749 = 303539) (by norm_num)
theorem B2697077 : Blo 1596997 2697077 := bbase (se 5 (by rfl) ⟨126425, by rfl⟩ : syracuseStep 2697077 = 252851) (by norm_num)
theorem B5392277 : Blo 1596997 5392277 := bbase (se 6 (by rfl) ⟨126381, by rfl⟩ : syracuseStep 5392277 = 252763) (by norm_num)
theorem B2049961 : Blo 1596997 2049961 := bbase (se 2 (by rfl) ⟨768735, by rfl⟩ : syracuseStep 2049961 = 1537471) (by norm_num)
theorem B3237821 : Blo 1596997 3237821 := bbase (se 3 (by rfl) ⟨607091, by rfl⟩ : syracuseStep 3237821 = 1214183) (by norm_num)
theorem B8087525 : Blo 1596997 8087525 := bbase (se 4 (by rfl) ⟨758205, by rfl⟩ : syracuseStep 8087525 = 1516411) (by norm_num)
theorem B2697205 : Blo 1596997 2697205 := bbase (se 5 (by rfl) ⟨126431, by rfl⟩ : syracuseStep 2697205 = 252863) (by norm_num)
theorem B2697293 : Blo 1596997 2697293 := bbase (se 3 (by rfl) ⟨505742, by rfl⟩ : syracuseStep 2697293 = 1011485) (by norm_num)
theorem B1706065 : Blo 1596997 1706065 := bbase (se 2 (by rfl) ⟨639774, by rfl⟩ : syracuseStep 1706065 = 1279549) (by norm_num)
theorem B7784533 : Blo 1596997 7784533 := bbase (se 8 (by rfl) ⟨45612, by rfl⟩ : syracuseStep 7784533 = 91225) (by norm_num)
theorem B61450325 : Blo 1596997 61450325 := bbase (se 8 (by rfl) ⟨360060, by rfl⟩ : syracuseStep 61450325 = 720121) (by norm_num)
theorem B1919089 : Blo 1596997 1919089 := bbase (se 2 (by rfl) ⟨719658, by rfl⟩ : syracuseStep 1919089 = 1439317) (by norm_num)
theorem B2050165 : Blo 1596997 2050165 := bbase (se 5 (by rfl) ⟨96101, by rfl⟩ : syracuseStep 2050165 = 192203) (by norm_num)
theorem B3893429 : Blo 1596997 3893429 := bbase (se 5 (by rfl) ⟨182504, by rfl⟩ : syracuseStep 3893429 = 365009) (by norm_num)
theorem B1706185 : Blo 1596997 1706185 := bbase (se 2 (by rfl) ⟨639819, by rfl⟩ : syracuseStep 1706185 = 1279639) (by norm_num)
theorem B2697421 : Blo 1596997 2697421 := bbase (se 3 (by rfl) ⟨505766, by rfl⟩ : syracuseStep 2697421 = 1011533) (by norm_num)
theorem B3033301 : Blo 1596997 3033301 := bbase (se 7 (by rfl) ⟨35546, by rfl⟩ : syracuseStep 3033301 = 71093) (by norm_num)
theorem B4548869 : Blo 1596997 4548869 := bbase (se 4 (by rfl) ⟨426456, by rfl⟩ : syracuseStep 4548869 = 852913) (by norm_num)
theorem B2697509 : Blo 1596997 2697509 := bbase (se 4 (by rfl) ⟨252891, by rfl⟩ : syracuseStep 2697509 = 505783) (by norm_num)
theorem B1919281 : Blo 1596997 1919281 := bbase (se 2 (by rfl) ⟨719730, by rfl⟩ : syracuseStep 1919281 = 1439461) (by norm_num)
theorem B5392709 : Blo 1596997 5392709 := bbase (se 4 (by rfl) ⟨505566, by rfl⟩ : syracuseStep 5392709 = 1011133) (by norm_num)
theorem B27298133 : Blo 1596997 27298133 := bbase (se 10 (by rfl) ⟨39987, by rfl⟩ : syracuseStep 27298133 = 79975) (by norm_num)
theorem B10242389 : Blo 1596997 10242389 := bbase (se 10 (by rfl) ⟨15003, by rfl⟩ : syracuseStep 10242389 = 30007) (by norm_num)
theorem B3033445 : Blo 1596997 3033445 := bbase (se 4 (by rfl) ⟨284385, by rfl⟩ : syracuseStep 3033445 = 568771) (by norm_num)
theorem B1919381 : Blo 1596997 1919381 := bbase (se 6 (by rfl) ⟨44985, by rfl⟩ : syracuseStep 1919381 = 89971) (by norm_num)
theorem B2697637 : Blo 1596997 2697637 := bbase (se 4 (by rfl) ⟨252903, by rfl⟩ : syracuseStep 2697637 = 505807) (by norm_num)
theorem B1706437 : Blo 1596997 1706437 := bbase (se 4 (by rfl) ⟨159978, by rfl⟩ : syracuseStep 1706437 = 319957) (by norm_num)
theorem B1706441 : Blo 1596997 1706441 := bbase (se 2 (by rfl) ⟨639915, by rfl⟩ : syracuseStep 1706441 = 1279831) (by norm_num)
theorem B6482389 : Blo 1596997 6482389 := bbase (se 7 (by rfl) ⟨75965, by rfl⟩ : syracuseStep 6482389 = 151931) (by norm_num)
theorem B3893741 : Blo 1596997 3893741 := bbase (se 3 (by rfl) ⟨730076, by rfl⟩ : syracuseStep 3893741 = 1460153) (by norm_num)
theorem B2697725 : Blo 1596997 2697725 := bbase (se 3 (by rfl) ⟨505823, by rfl⟩ : syracuseStep 2697725 = 1011647) (by norm_num)
theorem B3033605 : Blo 1596997 3033605 := bbase (se 4 (by rfl) ⟨284400, by rfl⟩ : syracuseStep 3033605 = 568801) (by norm_num)
theorem B1796629 : Blo 1596997 1796629 := bbase (se 6 (by rfl) ⟨42108, by rfl⟩ : syracuseStep 1796629 = 84217) (by norm_num)
theorem B12134933 : Blo 1596997 12134933 := bbase (se 6 (by rfl) ⟨284412, by rfl⟩ : syracuseStep 12134933 = 568825) (by norm_num)
theorem B6826517 : Blo 1596997 6826517 := bbase (se 6 (by rfl) ⟨159996, by rfl⟩ : syracuseStep 6826517 = 319993) (by norm_num)
theorem B1796665 : Blo 1596997 1796665 := bbase (se 2 (by rfl) ⟨673749, by rfl⟩ : syracuseStep 1796665 = 1347499) (by norm_num)
theorem B1796701 : Blo 1596997 1796701 := bbase (se 3 (by rfl) ⟨336881, by rfl⟩ : syracuseStep 1796701 = 673763) (by norm_num)
theorem B2697853 : Blo 1596997 2697853 := bbase (se 3 (by rfl) ⟨505847, by rfl⟩ : syracuseStep 2697853 = 1011695) (by norm_num)
theorem B1796737 : Blo 1596997 1796737 := bbase (se 2 (by rfl) ⟨673776, by rfl⟩ : syracuseStep 1796737 = 1347553) (by norm_num)
theorem B3033749 : Blo 1596997 3033749 := bbase (se 6 (by rfl) ⟨71103, by rfl⟩ : syracuseStep 3033749 = 142207) (by norm_num)
theorem B1796773 : Blo 1596997 1796773 := bbase (se 4 (by rfl) ⟨168447, by rfl⟩ : syracuseStep 1796773 = 336895) (by norm_num)
theorem B1796809 : Blo 1596997 1796809 := bbase (se 2 (by rfl) ⟨673803, by rfl⟩ : syracuseStep 1796809 = 1347607) (by norm_num)
theorem B2697941 : Blo 1596997 2697941 := bbase (se 7 (by rfl) ⟨31616, by rfl⟩ : syracuseStep 2697941 = 63233) (by norm_num)
theorem B1796845 : Blo 1596997 1796845 := bbase (se 3 (by rfl) ⟨336908, by rfl⟩ : syracuseStep 1796845 = 673817) (by norm_num)
theorem B5393141 : Blo 1596997 5393141 := bbase (se 5 (by rfl) ⟨252803, by rfl⟩ : syracuseStep 5393141 = 505607) (by norm_num)
theorem B6064901 : Blo 1596997 6064901 := bbase (se 4 (by rfl) ⟨568584, by rfl⟩ : syracuseStep 6064901 = 1137169) (by norm_num)
theorem B1796881 : Blo 1596997 1796881 := bbase (se 2 (by rfl) ⟨673830, by rfl⟩ : syracuseStep 1796881 = 1347661) (by norm_num)
theorem B1846049 : Blo 1596997 1846049 := bbase (se 2 (by rfl) ⟨692268, by rfl⟩ : syracuseStep 1846049 = 1384537) (by norm_num)
theorem B2558765 : Blo 1596997 2558765 := bbase (se 3 (by rfl) ⟨479768, by rfl⟩ : syracuseStep 2558765 = 959537) (by norm_num)
theorem B1796917 : Blo 1596997 1796917 := bbase (se 5 (by rfl) ⟨84230, by rfl⟩ : syracuseStep 1796917 = 168461) (by norm_num)
theorem B2698069 : Blo 1596997 2698069 := bbase (se 9 (by rfl) ⟨7904, by rfl⟩ : syracuseStep 2698069 = 15809) (by norm_num)
theorem B1796953 : Blo 1596997 1796953 := bbase (se 2 (by rfl) ⟨673857, by rfl⟩ : syracuseStep 1796953 = 1347715) (by norm_num)
theorem B1796989 : Blo 1596997 1796989 := bbase (se 3 (by rfl) ⟨336935, by rfl⟩ : syracuseStep 1796989 = 673871) (by norm_num)
theorem B1797025 : Blo 1596997 1797025 := bbase (se 2 (by rfl) ⟨673884, by rfl⟩ : syracuseStep 1797025 = 1347769) (by norm_num)
theorem B1641377 : Blo 1596997 1641377 := bbase (se 2 (by rfl) ⟨615516, by rfl⟩ : syracuseStep 1641377 = 1231033) (by norm_num)
theorem B2558893 : Blo 1596997 2558893 := bbase (se 3 (by rfl) ⟨479792, by rfl⟩ : syracuseStep 2558893 = 959585) (by norm_num)
theorem B2698157 : Blo 1596997 2698157 := bbase (se 3 (by rfl) ⟨505904, by rfl⟩ : syracuseStep 2698157 = 1011809) (by norm_num)
theorem B3034037 : Blo 1596997 3034037 := bbase (se 5 (by rfl) ⟨142220, by rfl⟩ : syracuseStep 3034037 = 284441) (by norm_num)
theorem B1797061 : Blo 1596997 1797061 := bbase (se 4 (by rfl) ⟨168474, by rfl⟩ : syracuseStep 1797061 = 336949) (by norm_num)
theorem B1797097 : Blo 1596997 1797097 := bbase (se 2 (by rfl) ⟨673911, by rfl⟩ : syracuseStep 1797097 = 1347823) (by norm_num)
theorem B2558957 : Blo 1596997 2558957 := bbase (se 3 (by rfl) ⟨479804, by rfl⟩ : syracuseStep 2558957 = 959609) (by norm_num)
theorem B4549621 : Blo 1596997 4549621 := bbase (se 5 (by rfl) ⟨213263, by rfl⟩ : syracuseStep 4549621 = 426527) (by norm_num)
theorem B1707005 : Blo 1596997 1707005 := bbase (se 3 (by rfl) ⟨320063, by rfl⟩ : syracuseStep 1707005 = 640127) (by norm_num)
theorem B1797133 : Blo 1596997 1797133 := bbase (se 3 (by rfl) ⟨336962, by rfl⟩ : syracuseStep 1797133 = 673925) (by norm_num)
theorem B12471317 : Blo 1596997 12471317 := bbase (se 6 (by rfl) ⟨292296, by rfl⟩ : syracuseStep 12471317 = 584593) (by norm_num)
theorem B3894293 : Blo 1596997 3894293 := bbase (se 6 (by rfl) ⟨91272, by rfl⟩ : syracuseStep 3894293 = 182545) (by norm_num)
theorem B6065189 : Blo 1596997 6065189 := bbase (se 4 (by rfl) ⟨568611, by rfl⟩ : syracuseStep 6065189 = 1137223) (by norm_num)
theorem B2698285 : Blo 1596997 2698285 := bbase (se 3 (by rfl) ⟨505928, by rfl⟩ : syracuseStep 2698285 = 1011857) (by norm_num)
theorem B1797169 : Blo 1596997 1797169 := bbase (se 2 (by rfl) ⟨673938, by rfl⟩ : syracuseStep 1797169 = 1347877) (by norm_num)
theorem B3034189 : Blo 1596997 3034189 := bbase (se 3 (by rfl) ⟨568910, by rfl⟩ : syracuseStep 3034189 = 1137821) (by norm_num)
theorem B1797205 : Blo 1596997 1797205 := bbase (se 8 (by rfl) ⟨10530, by rfl⟩ : syracuseStep 1797205 = 21061) (by norm_num)
theorem B1797241 : Blo 1596997 1797241 := bbase (se 2 (by rfl) ⟨673965, by rfl⟩ : syracuseStep 1797241 = 1347931) (by norm_num)
theorem B1797277 : Blo 1596997 1797277 := bbase (se 3 (by rfl) ⟨336989, by rfl⟩ : syracuseStep 1797277 = 673979) (by norm_num)
theorem B5393573 : Blo 1596997 5393573 := bbase (se 4 (by rfl) ⟨505647, by rfl⟩ : syracuseStep 5393573 = 1011295) (by norm_num)
theorem B1920169 : Blo 1596997 1920169 := bbase (se 2 (by rfl) ⟨720063, by rfl⟩ : syracuseStep 1920169 = 1440127) (by norm_num)
theorem B1707193 : Blo 1596997 1707193 := bbase (se 2 (by rfl) ⟨640197, by rfl⟩ : syracuseStep 1707193 = 1280395) (by norm_num)
theorem B1797313 : Blo 1596997 1797313 := bbase (se 2 (by rfl) ⟨673992, by rfl⟩ : syracuseStep 1797313 = 1347985) (by norm_num)
theorem B1797349 : Blo 1596997 1797349 := bbase (se 4 (by rfl) ⟨168501, by rfl⟩ : syracuseStep 1797349 = 337003) (by norm_num)
theorem B8088821 : Blo 1596997 8088821 := bbase (se 5 (by rfl) ⟨379163, by rfl⟩ : syracuseStep 8088821 = 758327) (by norm_num)
theorem B1797385 : Blo 1596997 1797385 := bbase (se 2 (by rfl) ⟨674019, by rfl⟩ : syracuseStep 1797385 = 1348039) (by norm_num)
theorem B1797421 : Blo 1596997 1797421 := bbase (se 3 (by rfl) ⟨337016, by rfl⟩ : syracuseStep 1797421 = 674033) (by norm_num)
theorem B1797457 : Blo 1596997 1797457 := bbase (se 2 (by rfl) ⟨674046, by rfl⟩ : syracuseStep 1797457 = 1348093) (by norm_num)
theorem B1797493 : Blo 1596997 1797493 := bbase (se 5 (by rfl) ⟨84257, by rfl⟩ : syracuseStep 1797493 = 168515) (by norm_num)
theorem B2395517 : Blo 1596997 2395517 := bbase (se 3 (by rfl) ⟨449159, by rfl⟩ : syracuseStep 2395517 = 898319) (by norm_num)
theorem B3034493 : Blo 1596997 3034493 := bbase (se 3 (by rfl) ⟨568967, by rfl⟩ : syracuseStep 3034493 = 1137935) (by norm_num)
theorem B2395541 : Blo 1596997 2395541 := bbase (se 6 (by rfl) ⟨56145, by rfl⟩ : syracuseStep 2395541 = 112291) (by norm_num)
theorem B1797529 : Blo 1596997 1797529 := bbase (se 2 (by rfl) ⟨674073, by rfl⟩ : syracuseStep 1797529 = 1348147) (by norm_num)
theorem B2395565 : Blo 1596997 2395565 := bbase (se 3 (by rfl) ⟨449168, by rfl⟩ : syracuseStep 2395565 = 898337) (by norm_num)
theorem B1797565 : Blo 1596997 1797565 := bbase (se 3 (by rfl) ⟨337043, by rfl⟩ : syracuseStep 1797565 = 674087) (by norm_num)
theorem B2395589 : Blo 1596997 2395589 := bbase (se 4 (by rfl) ⟨224586, by rfl⟩ : syracuseStep 2395589 = 449173) (by norm_num)
theorem B3411413 : Blo 1596997 3411413 := bbase (se 7 (by rfl) ⟨39977, by rfl⟩ : syracuseStep 3411413 = 79955) (by norm_num)
theorem B2395613 : Blo 1596997 2395613 := bbase (se 3 (by rfl) ⟨449177, by rfl⟩ : syracuseStep 2395613 = 898355) (by norm_num)
theorem B1797601 : Blo 1596997 1797601 := bbase (se 2 (by rfl) ⟨674100, by rfl⟩ : syracuseStep 1797601 = 1348201) (by norm_num)
theorem B2395637 : Blo 1596997 2395637 := bbase (se 5 (by rfl) ⟨112295, by rfl⟩ : syracuseStep 2395637 = 224591) (by norm_num)
theorem B1797637 : Blo 1596997 1797637 := bbase (se 4 (by rfl) ⟨168528, by rfl⟩ : syracuseStep 1797637 = 337057) (by norm_num)
theorem B2395661 : Blo 1596997 2395661 := bbase (se 3 (by rfl) ⟨449186, by rfl⟩ : syracuseStep 2395661 = 898373) (by norm_num)
theorem B2395685 : Blo 1596997 2395685 := bbase (se 4 (by rfl) ⟨224595, by rfl⟩ : syracuseStep 2395685 = 449191) (by norm_num)
theorem B1797673 : Blo 1596997 1797673 := bbase (se 2 (by rfl) ⟨674127, by rfl⟩ : syracuseStep 1797673 = 1348255) (by norm_num)
theorem B2395709 : Blo 1596997 2395709 := bbase (se 3 (by rfl) ⟨449195, by rfl⟩ : syracuseStep 2395709 = 898391) (by norm_num)
theorem B3411533 : Blo 1596997 3411533 := bbase (se 3 (by rfl) ⟨639662, by rfl⟩ : syracuseStep 3411533 = 1279325) (by norm_num)
theorem B1797709 : Blo 1596997 1797709 := bbase (se 3 (by rfl) ⟨337070, by rfl⟩ : syracuseStep 1797709 = 674141) (by norm_num)
theorem B2395733 : Blo 1596997 2395733 := bbase (se 8 (by rfl) ⟨14037, by rfl⟩ : syracuseStep 2395733 = 28075) (by norm_num)
theorem B5394005 : Blo 1596997 5394005 := bbase (se 8 (by rfl) ⟨31605, by rfl⟩ : syracuseStep 5394005 = 63211) (by norm_num)
theorem B2395757 : Blo 1596997 2395757 := bbase (se 3 (by rfl) ⟨449204, by rfl⟩ : syracuseStep 2395757 = 898409) (by norm_num)
theorem B1797745 : Blo 1596997 1797745 := bbase (se 2 (by rfl) ⟨674154, by rfl⟩ : syracuseStep 1797745 = 1348309) (by norm_num)
theorem B2395781 : Blo 1596997 2395781 := bbase (se 4 (by rfl) ⟨224604, by rfl⟩ : syracuseStep 2395781 = 449209) (by norm_num)
theorem B1797781 : Blo 1596997 1797781 := bbase (se 6 (by rfl) ⟨42135, by rfl⟩ : syracuseStep 1797781 = 84271) (by norm_num)
theorem B2395805 : Blo 1596997 2395805 := bbase (se 3 (by rfl) ⟨449213, by rfl⟩ : syracuseStep 2395805 = 898427) (by norm_num)
theorem B2395829 : Blo 1596997 2395829 := bbase (se 5 (by rfl) ⟨112304, by rfl⟩ : syracuseStep 2395829 = 224609) (by norm_num)
theorem B3239605 : Blo 1596997 3239605 := bbase (se 5 (by rfl) ⟨151856, by rfl⟩ : syracuseStep 3239605 = 303713) (by norm_num)
theorem B1797817 : Blo 1596997 1797817 := bbase (se 2 (by rfl) ⟨674181, by rfl⟩ : syracuseStep 1797817 = 1348363) (by norm_num)
theorem B2395853 : Blo 1596997 2395853 := bbase (se 3 (by rfl) ⟨449222, by rfl⟩ : syracuseStep 2395853 = 898445) (by norm_num)
theorem B8752853 : Blo 1596997 8752853 := bbase (se 7 (by rfl) ⟨102572, by rfl⟩ : syracuseStep 8752853 = 205145) (by norm_num)
theorem B1797853 : Blo 1596997 1797853 := bbase (se 3 (by rfl) ⟨337097, by rfl⟩ : syracuseStep 1797853 = 674195) (by norm_num)
theorem B2395877 : Blo 1596997 2395877 := bbase (se 4 (by rfl) ⟨224613, by rfl⟩ : syracuseStep 2395877 = 449227) (by norm_num)
theorem B2395901 : Blo 1596997 2395901 := bbase (se 3 (by rfl) ⟨449231, by rfl⟩ : syracuseStep 2395901 = 898463) (by norm_num)
theorem B1797889 : Blo 1596997 1797889 := bbase (se 2 (by rfl) ⟨674208, by rfl⟩ : syracuseStep 1797889 = 1348417) (by norm_num)
theorem B2395925 : Blo 1596997 2395925 := bbase (se 6 (by rfl) ⟨56154, by rfl⟩ : syracuseStep 2395925 = 112309) (by norm_num)
theorem B3837725 : Blo 1596997 3837725 := bbase (se 3 (by rfl) ⟨719573, by rfl⟩ : syracuseStep 3837725 = 1439147) (by norm_num)
theorem B1797925 : Blo 1596997 1797925 := bbase (se 4 (by rfl) ⟨168555, by rfl⟩ : syracuseStep 1797925 = 337111) (by norm_num)
theorem B2395949 : Blo 1596997 2395949 := bbase (se 3 (by rfl) ⟨449240, by rfl⟩ : syracuseStep 2395949 = 898481) (by norm_num)
theorem B2305837 : Blo 1596997 2305837 := bbase (se 3 (by rfl) ⟨432344, by rfl⟩ : syracuseStep 2305837 = 864689) (by norm_num)
theorem B2395973 : Blo 1596997 2395973 := bbase (se 4 (by rfl) ⟨224622, by rfl⟩ : syracuseStep 2395973 = 449245) (by norm_num)
theorem B1797961 : Blo 1596997 1797961 := bbase (se 2 (by rfl) ⟨674235, by rfl⟩ : syracuseStep 1797961 = 1348471) (by norm_num)
theorem B2158429 : Blo 1596997 2158429 := bbase (se 3 (by rfl) ⟨404705, by rfl⟩ : syracuseStep 2158429 = 809411) (by norm_num)
theorem B2395997 : Blo 1596997 2395997 := bbase (se 3 (by rfl) ⟨449249, by rfl⟩ : syracuseStep 2395997 = 898499) (by norm_num)
theorem B1797997 : Blo 1596997 1797997 := bbase (se 3 (by rfl) ⟨337124, by rfl⟩ : syracuseStep 1797997 = 674249) (by norm_num)
theorem B1920881 : Blo 1596997 1920881 := bbase (se 2 (by rfl) ⟨720330, by rfl⟩ : syracuseStep 1920881 = 1440661) (by norm_num)
theorem B2396021 : Blo 1596997 2396021 := bbase (se 5 (by rfl) ⟨112313, by rfl⟩ : syracuseStep 2396021 = 224627) (by norm_num)
theorem B2396045 : Blo 1596997 2396045 := bbase (se 3 (by rfl) ⟨449258, by rfl⟩ : syracuseStep 2396045 = 898517) (by norm_num)
theorem B3461005 : Blo 1596997 3461005 := bbase (se 3 (by rfl) ⟨648938, by rfl⟩ : syracuseStep 3461005 = 1297877) (by norm_num)
theorem B1798033 : Blo 1596997 1798033 := bbase (se 2 (by rfl) ⟨674262, by rfl⟩ : syracuseStep 1798033 = 1348525) (by norm_num)
theorem B2879389 : Blo 1596997 2879389 := bbase (se 3 (by rfl) ⟨539885, by rfl⟩ : syracuseStep 2879389 = 1079771) (by norm_num)
theorem B2396069 : Blo 1596997 2396069 := bbase (se 4 (by rfl) ⟨224631, by rfl⟩ : syracuseStep 2396069 = 449263) (by norm_num)
theorem B4042669 : Blo 1596997 4042669 := bbase (se 3 (by rfl) ⟨758000, by rfl⟩ : syracuseStep 4042669 = 1516001) (by norm_num)
theorem B1798069 : Blo 1596997 1798069 := bbase (se 5 (by rfl) ⟨84284, by rfl⟩ : syracuseStep 1798069 = 168569) (by norm_num)
theorem B2396093 : Blo 1596997 2396093 := bbase (se 3 (by rfl) ⟨449267, by rfl⟩ : syracuseStep 2396093 = 898535) (by norm_num)
theorem B2396117 : Blo 1596997 2396117 := bbase (se 7 (by rfl) ⟨28079, by rfl⟩ : syracuseStep 2396117 = 56159) (by norm_num)
theorem B1798105 : Blo 1596997 1798105 := bbase (se 2 (by rfl) ⟨674289, by rfl⟩ : syracuseStep 1798105 = 1348579) (by norm_num)
theorem B2396141 : Blo 1596997 2396141 := bbase (se 3 (by rfl) ⟨449276, by rfl⟩ : syracuseStep 2396141 = 898553) (by norm_num)
theorem B1798141 : Blo 1596997 1798141 := bbase (se 3 (by rfl) ⟨337151, by rfl⟩ : syracuseStep 1798141 = 674303) (by norm_num)
theorem B2396165 : Blo 1596997 2396165 := bbase (se 4 (by rfl) ⟨224640, by rfl⟩ : syracuseStep 2396165 = 449281) (by norm_num)
theorem B5615621 : Blo 1596997 5615621 := bbase (se 4 (by rfl) ⟨526464, by rfl⟩ : syracuseStep 5615621 = 1052929) (by norm_num)
theorem B5394437 : Blo 1596997 5394437 := bbase (se 4 (by rfl) ⟨505728, by rfl⟩ : syracuseStep 5394437 = 1011457) (by norm_num)
theorem B4042781 : Blo 1596997 4042781 := bbase (se 3 (by rfl) ⟨758021, by rfl⟩ : syracuseStep 4042781 = 1516043) (by norm_num)
theorem B2396189 : Blo 1596997 2396189 := bbase (se 3 (by rfl) ⟨449285, by rfl⟩ : syracuseStep 2396189 = 898571) (by norm_num)
theorem B1798177 : Blo 1596997 1798177 := bbase (se 2 (by rfl) ⟨674316, by rfl⟩ : syracuseStep 1798177 = 1348633) (by norm_num)
theorem B2879533 : Blo 1596997 2879533 := bbase (se 3 (by rfl) ⟨539912, by rfl⟩ : syracuseStep 2879533 = 1079825) (by norm_num)
theorem B2396213 : Blo 1596997 2396213 := bbase (se 5 (by rfl) ⟨112322, by rfl⟩ : syracuseStep 2396213 = 224645) (by norm_num)
theorem B1798213 : Blo 1596997 1798213 := bbase (se 4 (by rfl) ⟨168582, by rfl⟩ : syracuseStep 1798213 = 337165) (by norm_num)
theorem B2396237 : Blo 1596997 2396237 := bbase (se 3 (by rfl) ⟨449294, by rfl⟩ : syracuseStep 2396237 = 898589) (by norm_num)
theorem B2396261 : Blo 1596997 2396261 := bbase (se 4 (by rfl) ⟨224649, by rfl⟩ : syracuseStep 2396261 = 449299) (by norm_num)
theorem B1798249 : Blo 1596997 1798249 := bbase (se 2 (by rfl) ⟨674343, by rfl⟩ : syracuseStep 1798249 = 1348687) (by norm_num)
theorem B3035245 : Blo 1596997 3035245 := bbase (se 3 (by rfl) ⟨569108, by rfl⟩ : syracuseStep 3035245 = 1138217) (by norm_num)
theorem B2396285 : Blo 1596997 2396285 := bbase (se 3 (by rfl) ⟨449303, by rfl⟩ : syracuseStep 2396285 = 898607) (by norm_num)
theorem B1798285 : Blo 1596997 1798285 := bbase (se 3 (by rfl) ⟨337178, by rfl⟩ : syracuseStep 1798285 = 674357) (by norm_num)
theorem B2396309 : Blo 1596997 2396309 := bbase (se 6 (by rfl) ⟨56163, by rfl⟩ : syracuseStep 2396309 = 112327) (by norm_num)
theorem B2396333 : Blo 1596997 2396333 := bbase (se 3 (by rfl) ⟨449312, by rfl⟩ : syracuseStep 2396333 = 898625) (by norm_num)
theorem B1798321 : Blo 1596997 1798321 := bbase (se 2 (by rfl) ⟨674370, by rfl⟩ : syracuseStep 1798321 = 1348741) (by norm_num)
theorem B2396357 : Blo 1596997 2396357 := bbase (se 4 (by rfl) ⟨224658, by rfl⟩ : syracuseStep 2396357 = 449317) (by norm_num)
theorem B3412165 : Blo 1596997 3412165 := bbase (se 4 (by rfl) ⟨319890, by rfl⟩ : syracuseStep 3412165 = 639781) (by norm_num)
theorem B6066373 : Blo 1596997 6066373 := bbase (se 4 (by rfl) ⟨568722, by rfl⟩ : syracuseStep 6066373 = 1137445) (by norm_num)
theorem B5836997 : Blo 1596997 5836997 := bbase (se 4 (by rfl) ⟨547218, by rfl⟩ : syracuseStep 5836997 = 1094437) (by norm_num)
theorem B7680197 : Blo 1596997 7680197 := bbase (se 4 (by rfl) ⟨720018, by rfl⟩ : syracuseStep 7680197 = 1440037) (by norm_num)
theorem B1798357 : Blo 1596997 1798357 := bbase (se 7 (by rfl) ⟨21074, by rfl⟩ : syracuseStep 1798357 = 42149) (by norm_num)
theorem B4042973 : Blo 1596997 4042973 := bbase (se 3 (by rfl) ⟨758057, by rfl⟩ : syracuseStep 4042973 = 1516115) (by norm_num)
theorem B2396381 : Blo 1596997 2396381 := bbase (se 3 (by rfl) ⟨449321, by rfl⟩ : syracuseStep 2396381 = 898643) (by norm_num)
theorem B3240157 : Blo 1596997 3240157 := bbase (se 3 (by rfl) ⟨607529, by rfl⟩ : syracuseStep 3240157 = 1215059) (by norm_num)
theorem B2396405 : Blo 1596997 2396405 := bbase (se 5 (by rfl) ⟨112331, by rfl⟩ : syracuseStep 2396405 = 224663) (by norm_num)
theorem B1798393 : Blo 1596997 1798393 := bbase (se 2 (by rfl) ⟨674397, by rfl⟩ : syracuseStep 1798393 = 1348795) (by norm_num)
theorem B3035389 : Blo 1596997 3035389 := bbase (se 3 (by rfl) ⟨569135, by rfl⟩ : syracuseStep 3035389 = 1138271) (by norm_num)
theorem B6828293 : Blo 1596997 6828293 := bbase (se 4 (by rfl) ⟨640152, by rfl⟩ : syracuseStep 6828293 = 1280305) (by norm_num)
theorem B2396429 : Blo 1596997 2396429 := bbase (se 3 (by rfl) ⟨449330, by rfl⟩ : syracuseStep 2396429 = 898661) (by norm_num)
theorem B12955925 : Blo 1596997 12955925 := bbase (se 6 (by rfl) ⟨303654, by rfl⟩ : syracuseStep 12955925 = 607309) (by norm_num)
theorem B2560277 : Blo 1596997 2560277 := bbase (se 6 (by rfl) ⟨60006, by rfl⟩ : syracuseStep 2560277 = 120013) (by norm_num)
theorem B1798429 : Blo 1596997 1798429 := bbase (se 3 (by rfl) ⟨337205, by rfl⟩ : syracuseStep 1798429 = 674411) (by norm_num)
theorem B2396453 : Blo 1596997 2396453 := bbase (se 4 (by rfl) ⟨224667, by rfl⟩ : syracuseStep 2396453 = 449335) (by norm_num)
theorem B2396477 : Blo 1596997 2396477 := bbase (se 3 (by rfl) ⟨449339, by rfl⟩ : syracuseStep 2396477 = 898679) (by norm_num)
theorem B1798465 : Blo 1596997 1798465 := bbase (se 2 (by rfl) ⟨674424, by rfl⟩ : syracuseStep 1798465 = 1348849) (by norm_num)
theorem B2396501 : Blo 1596997 2396501 := bbase (se 10 (by rfl) ⟨3510, by rfl⟩ : syracuseStep 2396501 = 7021) (by norm_num)
theorem B1798501 : Blo 1596997 1798501 := bbase (se 4 (by rfl) ⟨168609, by rfl⟩ : syracuseStep 1798501 = 337219) (by norm_num)
theorem B2396525 : Blo 1596997 2396525 := bbase (se 3 (by rfl) ⟨449348, by rfl⟩ : syracuseStep 2396525 = 898697) (by norm_num)
theorem B2396549 : Blo 1596997 2396549 := bbase (se 4 (by rfl) ⟨224676, by rfl⟩ : syracuseStep 2396549 = 449353) (by norm_num)
theorem B1798537 : Blo 1596997 1798537 := bbase (se 2 (by rfl) ⟨674451, by rfl⟩ : syracuseStep 1798537 = 1348903) (by norm_num)
theorem B2560405 : Blo 1596997 2560405 := bbase (se 6 (by rfl) ⟨60009, by rfl⟩ : syracuseStep 2560405 = 120019) (by norm_num)
theorem B2396573 : Blo 1596997 2396573 := bbase (se 3 (by rfl) ⟨449357, by rfl⟩ : syracuseStep 2396573 = 898715) (by norm_num)
theorem B3035549 : Blo 1596997 3035549 := bbase (se 3 (by rfl) ⟨569165, by rfl⟩ : syracuseStep 3035549 = 1138331) (by norm_num)
theorem B1798573 : Blo 1596997 1798573 := bbase (se 3 (by rfl) ⟨337232, by rfl⟩ : syracuseStep 1798573 = 674465) (by norm_num)
theorem B2396597 : Blo 1596997 2396597 := bbase (se 5 (by rfl) ⟨112340, by rfl⟩ : syracuseStep 2396597 = 224681) (by norm_num)
theorem B5394869 : Blo 1596997 5394869 := bbase (se 5 (by rfl) ⟨252884, by rfl⟩ : syracuseStep 5394869 = 505769) (by norm_num)
theorem B2396621 : Blo 1596997 2396621 := bbase (se 3 (by rfl) ⟨449366, by rfl⟩ : syracuseStep 2396621 = 898733) (by norm_num)
theorem B1798609 : Blo 1596997 1798609 := bbase (se 2 (by rfl) ⟨674478, by rfl⟩ : syracuseStep 1798609 = 1348957) (by norm_num)
theorem B2396645 : Blo 1596997 2396645 := bbase (se 4 (by rfl) ⟨224685, by rfl⟩ : syracuseStep 2396645 = 449371) (by norm_num)
theorem B4321765 : Blo 1596997 4321765 := bbase (se 4 (by rfl) ⟨405165, by rfl⟩ : syracuseStep 4321765 = 810331) (by norm_num)
theorem B6066677 : Blo 1596997 6066677 := bbase (se 5 (by rfl) ⟨284375, by rfl⟩ : syracuseStep 6066677 = 568751) (by norm_num)
theorem B6828533 : Blo 1596997 6828533 := bbase (se 5 (by rfl) ⟨320087, by rfl⟩ : syracuseStep 6828533 = 640175) (by norm_num)
theorem B1798645 : Blo 1596997 1798645 := bbase (se 5 (by rfl) ⟨84311, by rfl⟩ : syracuseStep 1798645 = 168623) (by norm_num)
theorem B2396669 : Blo 1596997 2396669 := bbase (se 3 (by rfl) ⟨449375, by rfl⟩ : syracuseStep 2396669 = 898751) (by norm_num)
theorem B8090117 : Blo 1596997 8090117 := bbase (se 4 (by rfl) ⟨758448, by rfl⟩ : syracuseStep 8090117 = 1516897) (by norm_num)
theorem B2396693 : Blo 1596997 2396693 := bbase (se 6 (by rfl) ⟨56172, by rfl⟩ : syracuseStep 2396693 = 112345) (by norm_num)
theorem B1798681 : Blo 1596997 1798681 := bbase (se 2 (by rfl) ⟨674505, by rfl⟩ : syracuseStep 1798681 = 1349011) (by norm_num)
theorem B3838493 : Blo 1596997 3838493 := bbase (se 3 (by rfl) ⟨719717, by rfl⟩ : syracuseStep 3838493 = 1439435) (by norm_num)
theorem B2396717 : Blo 1596997 2396717 := bbase (se 3 (by rfl) ⟨449384, by rfl⟩ : syracuseStep 2396717 = 898769) (by norm_num)
theorem B4043317 : Blo 1596997 4043317 := bbase (se 5 (by rfl) ⟨189530, by rfl⟩ : syracuseStep 4043317 = 379061) (by norm_num)
theorem B1798717 : Blo 1596997 1798717 := bbase (se 3 (by rfl) ⟨337259, by rfl⟩ : syracuseStep 1798717 = 674519) (by norm_num)
theorem B2396741 : Blo 1596997 2396741 := bbase (se 4 (by rfl) ⟨224694, by rfl⟩ : syracuseStep 2396741 = 449389) (by norm_num)
theorem B2396765 : Blo 1596997 2396765 := bbase (se 3 (by rfl) ⟨449393, by rfl⟩ : syracuseStep 2396765 = 898787) (by norm_num)
theorem B2429533 : Blo 1596997 2429533 := bbase (se 3 (by rfl) ⟨455537, by rfl⟩ : syracuseStep 2429533 = 911075) (by norm_num)
theorem B1798753 : Blo 1596997 1798753 := bbase (se 2 (by rfl) ⟨674532, by rfl⟩ : syracuseStep 1798753 = 1349065) (by norm_num)
theorem B2396789 : Blo 1596997 2396789 := bbase (se 5 (by rfl) ⟨112349, by rfl⟩ : syracuseStep 2396789 = 224699) (by norm_num)
theorem B1798789 : Blo 1596997 1798789 := bbase (se 4 (by rfl) ⟨168636, by rfl⟩ : syracuseStep 1798789 = 337273) (by norm_num)
theorem B2396813 : Blo 1596997 2396813 := bbase (se 3 (by rfl) ⟨449402, by rfl⟩ : syracuseStep 2396813 = 898805) (by norm_num)
theorem B25916053 : Blo 1596997 25916053 := bbase (se 6 (by rfl) ⟨607407, by rfl⟩ : syracuseStep 25916053 = 1214815) (by norm_num)
theorem B4043429 : Blo 1596997 4043429 := bbase (se 4 (by rfl) ⟨379071, by rfl⟩ : syracuseStep 4043429 = 758143) (by norm_num)
theorem B2396837 : Blo 1596997 2396837 := bbase (se 4 (by rfl) ⟨224703, by rfl⟩ : syracuseStep 2396837 = 449407) (by norm_num)
theorem B1798825 : Blo 1596997 1798825 := bbase (se 2 (by rfl) ⟨674559, by rfl⟩ : syracuseStep 1798825 = 1349119) (by norm_num)
theorem B2396861 : Blo 1596997 2396861 := bbase (se 3 (by rfl) ⟨449411, by rfl⟩ : syracuseStep 2396861 = 898823) (by norm_num)
theorem B1798861 : Blo 1596997 1798861 := bbase (se 3 (by rfl) ⟨337286, by rfl⟩ : syracuseStep 1798861 = 674573) (by norm_num)
theorem B2396885 : Blo 1596997 2396885 := bbase (se 7 (by rfl) ⟨28088, by rfl⟩ : syracuseStep 2396885 = 56177) (by norm_num)
theorem B2396909 : Blo 1596997 2396909 := bbase (se 3 (by rfl) ⟨449420, by rfl⟩ : syracuseStep 2396909 = 898841) (by norm_num)
theorem B2396933 : Blo 1596997 2396933 := bbase (se 4 (by rfl) ⟨224712, by rfl⟩ : syracuseStep 2396933 = 449425) (by norm_num)
theorem B4322069 : Blo 1596997 4322069 := bbase (se 6 (by rfl) ⟨101298, by rfl⟩ : syracuseStep 4322069 = 202597) (by norm_num)
theorem B2396957 : Blo 1596997 2396957 := bbase (se 3 (by rfl) ⟨449429, by rfl⟩ : syracuseStep 2396957 = 898859) (by norm_num)
theorem B5116709 : Blo 1596997 5116709 := bbase (se 4 (by rfl) ⟨479691, by rfl⟩ : syracuseStep 5116709 = 959383) (by norm_num)
theorem B2396981 : Blo 1596997 2396981 := bbase (se 5 (by rfl) ⟨112358, by rfl⟩ : syracuseStep 2396981 = 224717) (by norm_num)
theorem B2397005 : Blo 1596997 2397005 := bbase (se 3 (by rfl) ⟨449438, by rfl⟩ : syracuseStep 2397005 = 898877) (by norm_num)
theorem B4043621 : Blo 1596997 4043621 := bbase (se 4 (by rfl) ⟨379089, by rfl⟩ : syracuseStep 4043621 = 758179) (by norm_num)
theorem B2397029 : Blo 1596997 2397029 := bbase (se 4 (by rfl) ⟨224721, by rfl⟩ : syracuseStep 2397029 = 449443) (by norm_num)
theorem B3240805 : Blo 1596997 3240805 := bbase (se 4 (by rfl) ⟨303825, by rfl⟩ : syracuseStep 3240805 = 607651) (by norm_num)
theorem B5395301 : Blo 1596997 5395301 := bbase (se 4 (by rfl) ⟨505809, by rfl⟩ : syracuseStep 5395301 = 1011619) (by norm_num)
theorem B2397053 : Blo 1596997 2397053 := bbase (se 3 (by rfl) ⟨449447, by rfl⟩ : syracuseStep 2397053 = 898895) (by norm_num)
theorem B2397077 : Blo 1596997 2397077 := bbase (se 6 (by rfl) ⟨56181, by rfl⟩ : syracuseStep 2397077 = 112363) (by norm_num)
theorem B2397101 : Blo 1596997 2397101 := bbase (se 3 (by rfl) ⟨449456, by rfl⟩ : syracuseStep 2397101 = 898913) (by norm_num)
theorem B2397125 : Blo 1596997 2397125 := bbase (se 4 (by rfl) ⟨224730, by rfl⟩ : syracuseStep 2397125 = 449461) (by norm_num)
theorem B2397149 : Blo 1596997 2397149 := bbase (se 3 (by rfl) ⟨449465, by rfl⟩ : syracuseStep 2397149 = 898931) (by norm_num)
theorem B2397173 : Blo 1596997 2397173 := bbase (se 5 (by rfl) ⟨112367, by rfl⟩ : syracuseStep 2397173 = 224735) (by norm_num)
theorem B2397197 : Blo 1596997 2397197 := bbase (se 3 (by rfl) ⟨449474, by rfl⟩ : syracuseStep 2397197 = 898949) (by norm_num)
theorem B2397221 : Blo 1596997 2397221 := bbase (se 4 (by rfl) ⟨224739, by rfl⟩ : syracuseStep 2397221 = 449479) (by norm_num)
theorem B2593853 : Blo 1596997 2593853 := bbase (se 3 (by rfl) ⟨486347, by rfl⟩ : syracuseStep 2593853 = 972695) (by norm_num)
theorem B3413053 : Blo 1596997 3413053 := bbase (se 3 (by rfl) ⟨639947, by rfl⟩ : syracuseStep 3413053 = 1279895) (by norm_num)
theorem B2397245 : Blo 1596997 2397245 := bbase (se 3 (by rfl) ⟨449483, by rfl⟩ : syracuseStep 2397245 = 898967) (by norm_num)
theorem B3593285 : Blo 1596997 3593285 := bbase (se 4 (by rfl) ⟨336870, by rfl⟩ : syracuseStep 3593285 = 673741) (by norm_num)
theorem B2397269 : Blo 1596997 2397269 := bbase (se 8 (by rfl) ⟨14046, by rfl⟩ : syracuseStep 2397269 = 28093) (by norm_num)
theorem B2397293 : Blo 1596997 2397293 := bbase (se 3 (by rfl) ⟨449492, by rfl⟩ : syracuseStep 2397293 = 898985) (by norm_num)
theorem B2397317 : Blo 1596997 2397317 := bbase (se 4 (by rfl) ⟨224748, by rfl⟩ : syracuseStep 2397317 = 449497) (by norm_num)
theorem B3593357 : Blo 1596997 3593357 := bbase (se 3 (by rfl) ⟨673754, by rfl⟩ : syracuseStep 3593357 = 1347509) (by norm_num)
theorem B2397341 : Blo 1596997 2397341 := bbase (se 3 (by rfl) ⟨449501, by rfl⟩ : syracuseStep 2397341 = 899003) (by norm_num)
theorem B2159797 : Blo 1596997 2159797 := bbase (se 5 (by rfl) ⟨101240, by rfl⟩ : syracuseStep 2159797 = 202481) (by norm_num)
theorem B3413173 : Blo 1596997 3413173 := bbase (se 5 (by rfl) ⟨159992, by rfl⟩ : syracuseStep 3413173 = 319985) (by norm_num)
theorem B2397365 : Blo 1596997 2397365 := bbase (se 5 (by rfl) ⟨112376, by rfl⟩ : syracuseStep 2397365 = 224753) (by norm_num)
theorem B4043965 : Blo 1596997 4043965 := bbase (se 3 (by rfl) ⟨758243, by rfl⟩ : syracuseStep 4043965 = 1516487) (by norm_num)
theorem B2561213 : Blo 1596997 2561213 := bbase (se 3 (by rfl) ⟨480227, by rfl⟩ : syracuseStep 2561213 = 960455) (by norm_num)
theorem B2397389 : Blo 1596997 2397389 := bbase (se 3 (by rfl) ⟨449510, by rfl⟩ : syracuseStep 2397389 = 899021) (by norm_num)
theorem B3593429 : Blo 1596997 3593429 := bbase (se 7 (by rfl) ⟨42110, by rfl⟩ : syracuseStep 3593429 = 84221) (by norm_num)
theorem B2397413 : Blo 1596997 2397413 := bbase (se 4 (by rfl) ⟨224757, by rfl⟩ : syracuseStep 2397413 = 449515) (by norm_num)
theorem B2397437 : Blo 1596997 2397437 := bbase (se 3 (by rfl) ⟨449519, by rfl⟩ : syracuseStep 2397437 = 899039) (by norm_num)
theorem B2880773 : Blo 1596997 2880773 := bbase (se 4 (by rfl) ⟨270072, by rfl⟩ : syracuseStep 2880773 = 540145) (by norm_num)
theorem B2397461 : Blo 1596997 2397461 := bbase (se 6 (by rfl) ⟨56190, by rfl⟩ : syracuseStep 2397461 = 112381) (by norm_num)
theorem B5395733 : Blo 1596997 5395733 := bbase (se 6 (by rfl) ⟨126462, by rfl⟩ : syracuseStep 5395733 = 252925) (by norm_num)
theorem B3593501 : Blo 1596997 3593501 := bbase (se 3 (by rfl) ⟨673781, by rfl⟩ : syracuseStep 3593501 = 1347563) (by norm_num)
theorem B4044077 : Blo 1596997 4044077 := bbase (se 3 (by rfl) ⟨758264, by rfl⟩ : syracuseStep 4044077 = 1516529) (by norm_num)
theorem B2397485 : Blo 1596997 2397485 := bbase (se 3 (by rfl) ⟨449528, by rfl⟩ : syracuseStep 2397485 = 899057) (by norm_num)
theorem B2397509 : Blo 1596997 2397509 := bbase (se 4 (by rfl) ⟨224766, by rfl⟩ : syracuseStep 2397509 = 449533) (by norm_num)
theorem B2397533 : Blo 1596997 2397533 := bbase (se 3 (by rfl) ⟨449537, by rfl⟩ : syracuseStep 2397533 = 899075) (by norm_num)
theorem B3593573 : Blo 1596997 3593573 := bbase (se 4 (by rfl) ⟨336897, by rfl⟩ : syracuseStep 3593573 = 673795) (by norm_num)
theorem B2397557 : Blo 1596997 2397557 := bbase (se 5 (by rfl) ⟨112385, by rfl⟩ : syracuseStep 2397557 = 224771) (by norm_num)
theorem B2397581 : Blo 1596997 2397581 := bbase (se 3 (by rfl) ⟨449546, by rfl⟩ : syracuseStep 2397581 = 899093) (by norm_num)
theorem B2397605 : Blo 1596997 2397605 := bbase (se 4 (by rfl) ⟨224775, by rfl⟩ : syracuseStep 2397605 = 449551) (by norm_num)
theorem B3593645 : Blo 1596997 3593645 := bbase (se 3 (by rfl) ⟨673808, by rfl⟩ : syracuseStep 3593645 = 1347617) (by norm_num)
theorem B3413429 : Blo 1596997 3413429 := bbase (se 5 (by rfl) ⟨160004, by rfl⟩ : syracuseStep 3413429 = 320009) (by norm_num)
theorem B2397629 : Blo 1596997 2397629 := bbase (se 3 (by rfl) ⟨449555, by rfl⟩ : syracuseStep 2397629 = 899111) (by norm_num)
theorem B2397653 : Blo 1596997 2397653 := bbase (se 7 (by rfl) ⟨28097, by rfl⟩ : syracuseStep 2397653 = 56195) (by norm_num)
theorem B5469653 : Blo 1596997 5469653 := bbase (se 7 (by rfl) ⟨64097, by rfl⟩ : syracuseStep 5469653 = 128195) (by norm_num)
theorem B4044269 : Blo 1596997 4044269 := bbase (se 3 (by rfl) ⟨758300, by rfl⟩ : syracuseStep 4044269 = 1516601) (by norm_num)
theorem B2397677 : Blo 1596997 2397677 := bbase (se 3 (by rfl) ⟨449564, by rfl⟩ : syracuseStep 2397677 = 899129) (by norm_num)
theorem B3593717 : Blo 1596997 3593717 := bbase (se 5 (by rfl) ⟨168455, by rfl⟩ : syracuseStep 3593717 = 336911) (by norm_num)
theorem B2397701 : Blo 1596997 2397701 := bbase (se 4 (by rfl) ⟨224784, by rfl⟩ : syracuseStep 2397701 = 449569) (by norm_num)
theorem B2397725 : Blo 1596997 2397725 := bbase (se 3 (by rfl) ⟨449573, by rfl⟩ : syracuseStep 2397725 = 899147) (by norm_num)
theorem B8640053 : Blo 1596997 8640053 := bbase (se 5 (by rfl) ⟨405002, by rfl⟩ : syracuseStep 8640053 = 810005) (by norm_num)
theorem B2397749 : Blo 1596997 2397749 := bbase (se 5 (by rfl) ⟨112394, by rfl⟩ : syracuseStep 2397749 = 224789) (by norm_num)
theorem B3593789 : Blo 1596997 3593789 := bbase (se 3 (by rfl) ⟨673835, by rfl⟩ : syracuseStep 3593789 = 1347671) (by norm_num)
theorem B2397773 : Blo 1596997 2397773 := bbase (se 3 (by rfl) ⟨449582, by rfl⟩ : syracuseStep 2397773 = 899165) (by norm_num)
theorem B2397797 : Blo 1596997 2397797 := bbase (se 4 (by rfl) ⟨224793, by rfl⟩ : syracuseStep 2397797 = 449587) (by norm_num)
theorem B2397821 : Blo 1596997 2397821 := bbase (se 3 (by rfl) ⟨449591, by rfl⟩ : syracuseStep 2397821 = 899183) (by norm_num)
theorem B3593861 : Blo 1596997 3593861 := bbase (se 4 (by rfl) ⟨336924, by rfl⟩ : syracuseStep 3593861 = 673849) (by norm_num)
theorem B18200213 : Blo 1596997 18200213 := bbase (se 6 (by rfl) ⟨426567, by rfl⟩ : syracuseStep 18200213 = 853135) (by norm_num)
theorem B23041685 : Blo 1596997 23041685 := bbase (se 6 (by rfl) ⟨540039, by rfl⟩ : syracuseStep 23041685 = 1080079) (by norm_num)
theorem B2397845 : Blo 1596997 2397845 := bbase (se 6 (by rfl) ⟨56199, by rfl⟩ : syracuseStep 2397845 = 112399) (by norm_num)
theorem B2397869 : Blo 1596997 2397869 := bbase (se 3 (by rfl) ⟨449600, by rfl⟩ : syracuseStep 2397869 = 899201) (by norm_num)
theorem B2397893 : Blo 1596997 2397893 := bbase (se 4 (by rfl) ⟨224802, by rfl⟩ : syracuseStep 2397893 = 449605) (by norm_num)
theorem B5396165 : Blo 1596997 5396165 := bbase (se 4 (by rfl) ⟨505890, by rfl⟩ : syracuseStep 5396165 = 1011781) (by norm_num)
theorem B3593933 : Blo 1596997 3593933 := bbase (se 3 (by rfl) ⟨673862, by rfl⟩ : syracuseStep 3593933 = 1347725) (by norm_num)
theorem B3282653 : Blo 1596997 3282653 := bbase (se 3 (by rfl) ⟨615497, by rfl⟩ : syracuseStep 3282653 = 1230995) (by norm_num)
theorem B2397917 : Blo 1596997 2397917 := bbase (se 3 (by rfl) ⟨449609, by rfl⟩ : syracuseStep 2397917 = 899219) (by norm_num)
theorem B2397941 : Blo 1596997 2397941 := bbase (se 5 (by rfl) ⟨112403, by rfl⟩ : syracuseStep 2397941 = 224807) (by norm_num)
theorem B2397965 : Blo 1596997 2397965 := bbase (se 3 (by rfl) ⟨449618, by rfl⟩ : syracuseStep 2397965 = 899237) (by norm_num)
theorem B3594005 : Blo 1596997 3594005 := bbase (se 6 (by rfl) ⟨84234, by rfl⟩ : syracuseStep 3594005 = 168469) (by norm_num)
theorem B8091413 : Blo 1596997 8091413 := bbase (se 6 (by rfl) ⟨189642, by rfl⟩ : syracuseStep 8091413 = 379285) (by norm_num)
theorem B4552469 : Blo 1596997 4552469 := bbase (se 6 (by rfl) ⟨106698, by rfl⟩ : syracuseStep 4552469 = 213397) (by norm_num)
theorem B2397989 : Blo 1596997 2397989 := bbase (se 4 (by rfl) ⟨224811, by rfl⟩ : syracuseStep 2397989 = 449623) (by norm_num)
theorem B2398013 : Blo 1596997 2398013 := bbase (se 3 (by rfl) ⟨449627, by rfl⟩ : syracuseStep 2398013 = 899255) (by norm_num)
theorem B4044613 : Blo 1596997 4044613 := bbase (se 4 (by rfl) ⟨379182, by rfl⟩ : syracuseStep 4044613 = 758365) (by norm_num)
theorem B2275141 : Blo 1596997 2275141 := bbase (se 4 (by rfl) ⟨213294, by rfl⟩ : syracuseStep 2275141 = 426589) (by norm_num)
theorem B2398037 : Blo 1596997 2398037 := bbase (se 9 (by rfl) ⟨7025, by rfl⟩ : syracuseStep 2398037 = 14051) (by norm_num)
theorem B2021213 : Blo 1596997 2021213 := bbase (se 3 (by rfl) ⟨378977, by rfl⟩ : syracuseStep 2021213 = 757955) (by norm_num)
theorem B3594077 : Blo 1596997 3594077 := bbase (se 3 (by rfl) ⟨673889, by rfl⟩ : syracuseStep 3594077 = 1347779) (by norm_num)
theorem B2398061 : Blo 1596997 2398061 := bbase (se 3 (by rfl) ⟨449636, by rfl⟩ : syracuseStep 2398061 = 899273) (by norm_num)
theorem B5117813 : Blo 1596997 5117813 := bbase (se 5 (by rfl) ⟨239897, by rfl⟩ : syracuseStep 5117813 = 479795) (by norm_num)
theorem B2398085 : Blo 1596997 2398085 := bbase (se 4 (by rfl) ⟨224820, by rfl⟩ : syracuseStep 2398085 = 449641) (by norm_num)
theorem B2021269 : Blo 1596997 2021269 := bbase (se 6 (by rfl) ⟨47373, by rfl⟩ : syracuseStep 2021269 = 94747) (by norm_num)
theorem B2398109 : Blo 1596997 2398109 := bbase (se 3 (by rfl) ⟨449645, by rfl⟩ : syracuseStep 2398109 = 899291) (by norm_num)
theorem B3594149 : Blo 1596997 3594149 := bbase (se 4 (by rfl) ⟨336951, by rfl⟩ : syracuseStep 3594149 = 673903) (by norm_num)
theorem B4044725 : Blo 1596997 4044725 := bbase (se 5 (by rfl) ⟨189596, by rfl⟩ : syracuseStep 4044725 = 379193) (by norm_num)
theorem B2398133 : Blo 1596997 2398133 := bbase (se 5 (by rfl) ⟨112412, by rfl⟩ : syracuseStep 2398133 = 224825) (by norm_num)
theorem B2398157 : Blo 1596997 2398157 := bbase (se 3 (by rfl) ⟨449654, by rfl⟩ : syracuseStep 2398157 = 899309) (by norm_num)
theorem B2398181 : Blo 1596997 2398181 := bbase (se 4 (by rfl) ⟨224829, by rfl⟩ : syracuseStep 2398181 = 449659) (by norm_num)
theorem B3594221 : Blo 1596997 3594221 := bbase (se 3 (by rfl) ⟨673916, by rfl⟩ : syracuseStep 3594221 = 1347833) (by norm_num)
theorem B2021365 : Blo 1596997 2021365 := bbase (se 5 (by rfl) ⟨94751, by rfl⟩ : syracuseStep 2021365 = 189503) (by norm_num)
theorem B2398205 : Blo 1596997 2398205 := bbase (se 3 (by rfl) ⟨449663, by rfl⟩ : syracuseStep 2398205 = 899327) (by norm_num)
theorem B5756933 : Blo 1596997 5756933 := bbase (se 4 (by rfl) ⟨539712, by rfl⟩ : syracuseStep 5756933 = 1079425) (by norm_num)
theorem B1619989 : Blo 1596997 1619989 := bbase (se 6 (by rfl) ⟨37968, by rfl⟩ : syracuseStep 1619989 = 75937) (by norm_num)
theorem B2398229 : Blo 1596997 2398229 := bbase (se 6 (by rfl) ⟨56208, by rfl⟩ : syracuseStep 2398229 = 112417) (by norm_num)
theorem B2398253 : Blo 1596997 2398253 := bbase (se 3 (by rfl) ⟨449672, by rfl⟩ : syracuseStep 2398253 = 899345) (by norm_num)
theorem B3594293 : Blo 1596997 3594293 := bbase (se 5 (by rfl) ⟨168482, by rfl⟩ : syracuseStep 3594293 = 336965) (by norm_num)
theorem B2398277 : Blo 1596997 2398277 := bbase (se 4 (by rfl) ⟨224838, by rfl⟩ : syracuseStep 2398277 = 449677) (by norm_num)
theorem B2734157 : Blo 1596997 2734157 := bbase (se 3 (by rfl) ⟨512654, by rfl⟩ : syracuseStep 2734157 = 1025309) (by norm_num)
theorem B2398301 : Blo 1596997 2398301 := bbase (se 3 (by rfl) ⟨449681, by rfl⟩ : syracuseStep 2398301 = 899363) (by norm_num)
theorem B4044917 : Blo 1596997 4044917 := bbase (se 5 (by rfl) ⟨189605, by rfl⟩ : syracuseStep 4044917 = 379211) (by norm_num)
theorem B2398325 : Blo 1596997 2398325 := bbase (se 5 (by rfl) ⟨112421, by rfl⟩ : syracuseStep 2398325 = 224843) (by norm_num)
theorem B5396597 : Blo 1596997 5396597 := bbase (se 5 (by rfl) ⟨252965, by rfl⟩ : syracuseStep 5396597 = 505931) (by norm_num)
theorem B3594365 : Blo 1596997 3594365 := bbase (se 3 (by rfl) ⟨673943, by rfl⟩ : syracuseStep 3594365 = 1347887) (by norm_num)
theorem B2398349 : Blo 1596997 2398349 := bbase (se 3 (by rfl) ⟨449690, by rfl⟩ : syracuseStep 2398349 = 899381) (by norm_num)
theorem B2021537 : Blo 1596997 2021537 := bbase (se 2 (by rfl) ⟨758076, by rfl⟩ : syracuseStep 2021537 = 1516153) (by norm_num)
theorem B2398373 : Blo 1596997 2398373 := bbase (se 4 (by rfl) ⟨224847, by rfl⟩ : syracuseStep 2398373 = 449695) (by norm_num)
theorem B2398397 : Blo 1596997 2398397 := bbase (se 3 (by rfl) ⟨449699, by rfl⟩ : syracuseStep 2398397 = 899399) (by norm_num)
theorem B3594437 : Blo 1596997 3594437 := bbase (se 4 (by rfl) ⟨336978, by rfl⟩ : syracuseStep 3594437 = 673957) (by norm_num)
theorem B3840205 : Blo 1596997 3840205 := bbase (se 3 (by rfl) ⟨720038, by rfl⟩ : syracuseStep 3840205 = 1440077) (by norm_num)
theorem B2398421 : Blo 1596997 2398421 := bbase (se 7 (by rfl) ⟨28106, by rfl⟩ : syracuseStep 2398421 = 56213) (by norm_num)
theorem B2021593 : Blo 1596997 2021593 := bbase (se 2 (by rfl) ⟨758097, by rfl⟩ : syracuseStep 2021593 = 1516195) (by norm_num)
theorem B2218205 : Blo 1596997 2218205 := bbase (se 3 (by rfl) ⟨415913, by rfl⟩ : syracuseStep 2218205 = 831827) (by norm_num)
theorem B2398445 : Blo 1596997 2398445 := bbase (se 3 (by rfl) ⟨449708, by rfl⟩ : syracuseStep 2398445 = 899417) (by norm_num)
theorem B2398469 : Blo 1596997 2398469 := bbase (se 4 (by rfl) ⟨224856, by rfl⟩ : syracuseStep 2398469 = 449713) (by norm_num)
theorem B3594509 : Blo 1596997 3594509 := bbase (se 3 (by rfl) ⟨673970, by rfl⟩ : syracuseStep 3594509 = 1347941) (by norm_num)
theorem B2398493 : Blo 1596997 2398493 := bbase (se 3 (by rfl) ⟨449717, by rfl⟩ : syracuseStep 2398493 = 899435) (by norm_num)
theorem B3414317 : Blo 1596997 3414317 := bbase (se 3 (by rfl) ⟨640184, by rfl⟩ : syracuseStep 3414317 = 1280369) (by norm_num)
theorem B2021689 : Blo 1596997 2021689 := bbase (se 2 (by rfl) ⟨758133, by rfl⟩ : syracuseStep 2021689 = 1516267) (by norm_num)
theorem B1620305 : Blo 1596997 1620305 := bbase (se 2 (by rfl) ⟨607614, by rfl⟩ : syracuseStep 1620305 = 1215229) (by norm_num)
theorem B3594581 : Blo 1596997 3594581 := bbase (se 10 (by rfl) ⟨5265, by rfl⟩ : syracuseStep 3594581 = 10531) (by norm_num)
theorem B6822245 : Blo 1596997 6822245 := bbase (se 4 (by rfl) ⟨639585, by rfl⟩ : syracuseStep 6822245 = 1279171) (by norm_num)
theorem B2275733 : Blo 1596997 2275733 := bbase (se 6 (by rfl) ⟨53337, by rfl⟩ : syracuseStep 2275733 = 106675) (by norm_num)
theorem B3594653 : Blo 1596997 3594653 := bbase (se 3 (by rfl) ⟨673997, by rfl⟩ : syracuseStep 3594653 = 1347995) (by norm_num)
theorem B15366581 : Blo 1596997 15366581 := bbase (se 5 (by rfl) ⟨720308, by rfl⟩ : syracuseStep 15366581 = 1440617) (by norm_num)
theorem B4045261 : Blo 1596997 4045261 := bbase (se 3 (by rfl) ⟨758486, by rfl⟩ : syracuseStep 4045261 = 1516973) (by norm_num)
theorem B46053845 : Blo 1596997 46053845 := bbase (se 7 (by rfl) ⟨539693, by rfl⟩ : syracuseStep 46053845 = 1079387) (by norm_num)
theorem B2021861 : Blo 1596997 2021861 := bbase (se 4 (by rfl) ⟨189549, by rfl⟩ : syracuseStep 2021861 = 379099) (by norm_num)
theorem B3594725 : Blo 1596997 3594725 := bbase (se 4 (by rfl) ⟨337005, by rfl⟩ : syracuseStep 3594725 = 674011) (by norm_num)
theorem B2275813 : Blo 1596997 2275813 := bbase (se 4 (by rfl) ⟨213357, by rfl⟩ : syracuseStep 2275813 = 426715) (by norm_num)
theorem B2021917 : Blo 1596997 2021917 := bbase (se 3 (by rfl) ⟨379109, by rfl⟩ : syracuseStep 2021917 = 758219) (by norm_num)
theorem B1972765 : Blo 1596997 1972765 := bbase (se 3 (by rfl) ⟨369893, by rfl⟩ : syracuseStep 1972765 = 739787) (by norm_num)
theorem B3414557 : Blo 1596997 3414557 := bbase (se 3 (by rfl) ⟨640229, by rfl⟩ : syracuseStep 3414557 = 1280459) (by norm_num)
theorem B3594797 : Blo 1596997 3594797 := bbase (se 3 (by rfl) ⟨674024, by rfl⟩ : syracuseStep 3594797 = 1348049) (by norm_num)
theorem B6068789 : Blo 1596997 6068789 := bbase (se 5 (by rfl) ⟨284474, by rfl⟩ : syracuseStep 6068789 = 568949) (by norm_num)
theorem B4045373 : Blo 1596997 4045373 := bbase (se 3 (by rfl) ⟨758507, by rfl⟩ : syracuseStep 4045373 = 1517015) (by norm_num)
theorem B2808389 : Blo 1596997 2808389 := bbase (se 4 (by rfl) ⟨263286, by rfl⟩ : syracuseStep 2808389 = 526573) (by norm_num)
theorem B2275933 : Blo 1596997 2275933 := bbase (se 3 (by rfl) ⟨426737, by rfl⟩ : syracuseStep 2275933 = 853475) (by norm_num)
theorem B3594869 : Blo 1596997 3594869 := bbase (se 5 (by rfl) ⟨168509, by rfl⟩ : syracuseStep 3594869 = 337019) (by norm_num)
theorem B2022013 : Blo 1596997 2022013 := bbase (se 3 (by rfl) ⟨379127, by rfl⟩ : syracuseStep 2022013 = 758255) (by norm_num)
theorem B3594941 : Blo 1596997 3594941 := bbase (se 3 (by rfl) ⟨674051, by rfl⟩ : syracuseStep 3594941 = 1348103) (by norm_num)
theorem B2276029 : Blo 1596997 2276029 := bbase (se 3 (by rfl) ⟨426755, by rfl⟩ : syracuseStep 2276029 = 853511) (by norm_num)
theorem B4045565 : Blo 1596997 4045565 := bbase (se 3 (by rfl) ⟨758543, by rfl⟩ : syracuseStep 4045565 = 1517087) (by norm_num)
theorem B3595013 : Blo 1596997 3595013 := bbase (se 4 (by rfl) ⟨337032, by rfl⟩ : syracuseStep 3595013 = 674065) (by norm_num)
theorem B7289605 : Blo 1596997 7289605 := bbase (se 4 (by rfl) ⟨683400, by rfl⟩ : syracuseStep 7289605 = 1366801) (by norm_num)
theorem B6478613 : Blo 1596997 6478613 := bbase (se 6 (by rfl) ⟨151842, by rfl⟩ : syracuseStep 6478613 = 303685) (by norm_num)
theorem B2022185 : Blo 1596997 2022185 := bbase (se 2 (by rfl) ⟨758319, by rfl⟩ : syracuseStep 2022185 = 1516639) (by norm_num)
theorem B3840821 : Blo 1596997 3840821 := bbase (se 5 (by rfl) ⟨180038, by rfl⟩ : syracuseStep 3840821 = 360077) (by norm_num)
theorem B3595085 : Blo 1596997 3595085 := bbase (se 3 (by rfl) ⟨674078, by rfl⟩ : syracuseStep 3595085 = 1348157) (by norm_num)
theorem B6069077 : Blo 1596997 6069077 := bbase (se 9 (by rfl) ⟨17780, by rfl⟩ : syracuseStep 6069077 = 35561) (by norm_num)
theorem B2022241 : Blo 1596997 2022241 := bbase (se 2 (by rfl) ⟨758340, by rfl⟩ : syracuseStep 2022241 = 1516681) (by norm_num)
theorem B3595157 : Blo 1596997 3595157 := bbase (se 6 (by rfl) ⟨84261, by rfl⟩ : syracuseStep 3595157 = 168523) (by norm_num)
theorem B2022337 : Blo 1596997 2022337 := bbase (se 2 (by rfl) ⟨758376, by rfl⟩ : syracuseStep 2022337 = 1516753) (by norm_num)
theorem B3595229 : Blo 1596997 3595229 := bbase (se 3 (by rfl) ⟨674105, by rfl⟩ : syracuseStep 3595229 = 1348211) (by norm_num)
theorem B3595301 : Blo 1596997 3595301 := bbase (se 4 (by rfl) ⟨337059, by rfl⟩ : syracuseStep 3595301 = 674119) (by norm_num)
theorem B8092709 : Blo 1596997 8092709 := bbase (se 4 (by rfl) ⟨758691, by rfl⟩ : syracuseStep 8092709 = 1517383) (by norm_num)
theorem B4856917 : Blo 1596997 4856917 := bbase (se 8 (by rfl) ⟨28458, by rfl⟩ : syracuseStep 4856917 = 56917) (by norm_num)
theorem B4045909 : Blo 1596997 4045909 := bbase (se 8 (by rfl) ⟨23706, by rfl⟩ : syracuseStep 4045909 = 47413) (by norm_num)
theorem B3595373 : Blo 1596997 3595373 := bbase (se 3 (by rfl) ⟨674132, by rfl⟩ : syracuseStep 3595373 = 1348265) (by norm_num)
theorem B2022509 : Blo 1596997 2022509 := bbase (se 3 (by rfl) ⟨379220, by rfl⟩ : syracuseStep 2022509 = 758441) (by norm_num)
theorem B2022565 : Blo 1596997 2022565 := bbase (se 4 (by rfl) ⟨189615, by rfl⟩ : syracuseStep 2022565 = 379231) (by norm_num)
theorem B2276525 : Blo 1596997 2276525 := bbase (se 3 (by rfl) ⟨426848, by rfl⟩ : syracuseStep 2276525 = 853697) (by norm_num)
theorem B3595445 : Blo 1596997 3595445 := bbase (se 5 (by rfl) ⟨168536, by rfl⟩ : syracuseStep 3595445 = 337073) (by norm_num)
theorem B4046021 : Blo 1596997 4046021 := bbase (se 4 (by rfl) ⟨379314, by rfl⟩ : syracuseStep 4046021 = 758629) (by norm_num)
theorem B3841253 : Blo 1596997 3841253 := bbase (se 4 (by rfl) ⟨360117, by rfl⟩ : syracuseStep 3841253 = 720235) (by norm_num)
theorem B3595517 : Blo 1596997 3595517 := bbase (se 3 (by rfl) ⟨674159, by rfl⟩ : syracuseStep 3595517 = 1348319) (by norm_num)
theorem B2022661 : Blo 1596997 2022661 := bbase (se 4 (by rfl) ⟨189624, by rfl⟩ : syracuseStep 2022661 = 379249) (by norm_num)
theorem B11672885 : Blo 1596997 11672885 := bbase (se 5 (by rfl) ⟨547166, by rfl⟩ : syracuseStep 11672885 = 1094333) (by norm_num)
theorem B3595589 : Blo 1596997 3595589 := bbase (se 4 (by rfl) ⟨337086, by rfl⟩ : syracuseStep 3595589 = 674173) (by norm_num)
theorem B4046213 : Blo 1596997 4046213 := bbase (se 4 (by rfl) ⟨379332, by rfl⟩ : syracuseStep 4046213 = 758665) (by norm_num)
theorem B3595661 : Blo 1596997 3595661 := bbase (se 3 (by rfl) ⟨674186, by rfl⟩ : syracuseStep 3595661 = 1348373) (by norm_num)
theorem B2022833 : Blo 1596997 2022833 := bbase (se 2 (by rfl) ⟨758562, by rfl⟩ : syracuseStep 2022833 = 1517125) (by norm_num)
theorem B8084933 : Blo 1596997 8084933 := bbase (se 4 (by rfl) ⟨757962, by rfl⟩ : syracuseStep 8084933 = 1515925) (by norm_num)
theorem B3595733 : Blo 1596997 3595733 := bbase (se 7 (by rfl) ⟨42137, by rfl⟩ : syracuseStep 3595733 = 84275) (by norm_num)
theorem B4857317 : Blo 1596997 4857317 := bbase (se 4 (by rfl) ⟨455373, by rfl⟩ : syracuseStep 4857317 = 910747) (by norm_num)
theorem B2022889 : Blo 1596997 2022889 := bbase (se 2 (by rfl) ⟨758583, by rfl⟩ : syracuseStep 2022889 = 1517167) (by norm_num)
theorem B3595805 : Blo 1596997 3595805 := bbase (se 3 (by rfl) ⟨674213, by rfl⟩ : syracuseStep 3595805 = 1348427) (by norm_num)
theorem B2022985 : Blo 1596997 2022985 := bbase (se 2 (by rfl) ⟨758619, by rfl⟩ : syracuseStep 2022985 = 1517239) (by norm_num)
theorem B3595877 : Blo 1596997 3595877 := bbase (se 4 (by rfl) ⟨337113, by rfl⟩ : syracuseStep 3595877 = 674227) (by norm_num)
theorem B3595949 : Blo 1596997 3595949 := bbase (se 3 (by rfl) ⟨674240, by rfl⟩ : syracuseStep 3595949 = 1348481) (by norm_num)
theorem B4046557 : Blo 1596997 4046557 := bbase (se 3 (by rfl) ⟨758729, by rfl⟩ : syracuseStep 4046557 = 1517459) (by norm_num)
theorem B5119733 : Blo 1596997 5119733 := bbase (se 5 (by rfl) ⟨239987, by rfl⟩ : syracuseStep 5119733 = 479975) (by norm_num)
theorem B3596021 : Blo 1596997 3596021 := bbase (se 5 (by rfl) ⟨168563, by rfl⟩ : syracuseStep 3596021 = 337127) (by norm_num)
theorem B2023157 : Blo 1596997 2023157 := bbase (se 5 (by rfl) ⟨94835, by rfl⟩ : syracuseStep 2023157 = 189671) (by norm_num)
theorem B5390117 : Blo 1596997 5390117 := bbase (se 4 (by rfl) ⟨505323, by rfl⟩ : syracuseStep 5390117 = 1010647) (by norm_num)
theorem B2023213 : Blo 1596997 2023213 := bbase (se 3 (by rfl) ⟨379352, by rfl⟩ : syracuseStep 2023213 = 758705) (by norm_num)
theorem B3596093 : Blo 1596997 3596093 := bbase (se 3 (by rfl) ⟨674267, by rfl⟩ : syracuseStep 3596093 = 1348535) (by norm_num)
theorem B4046669 : Blo 1596997 4046669 := bbase (se 3 (by rfl) ⟨758750, by rfl⟩ : syracuseStep 4046669 = 1517501) (by norm_num)
theorem B2695045 : Blo 1596997 2695045 := bbase (se 4 (by rfl) ⟨252660, by rfl⟩ : syracuseStep 2695045 = 505321) (by norm_num)
theorem B3596165 : Blo 1596997 3596165 := bbase (se 4 (by rfl) ⟨337140, by rfl⟩ : syracuseStep 3596165 = 674281) (by norm_num)
theorem B2023309 : Blo 1596997 2023309 := bbase (se 3 (by rfl) ⟨379370, by rfl⟩ : syracuseStep 2023309 = 758741) (by norm_num)
theorem B3596237 : Blo 1596997 3596237 := bbase (se 3 (by rfl) ⟨674294, by rfl⟩ : syracuseStep 3596237 = 1348589) (by norm_num)
theorem B2695133 : Blo 1596997 2695133 := bbase (se 3 (by rfl) ⟨505337, by rfl⟩ : syracuseStep 2695133 = 1010675) (by norm_num)
theorem B6070261 : Blo 1596997 6070261 := bbase (se 5 (by rfl) ⟨284543, by rfl⟩ : syracuseStep 6070261 = 569087) (by norm_num)
theorem B1597443 : Blo 1596997 1597443 := bstep (se 1 (by rfl) ⟨1198082, by rfl⟩ : syracuseStep 1597443 = 2396165) B2396165
theorem B3743747 : Blo 1596997 3743747 := bstep (se 1 (by rfl) ⟨2807810, by rfl⟩ : syracuseStep 3743747 = 5615621) B5615621
theorem B3596291 : Blo 1596997 3596291 := bstep (se 1 (by rfl) ⟨2697218, by rfl⟩ : syracuseStep 3596291 = 5394437) B5394437
theorem B2695187 : Blo 1596997 2695187 := bstep (se 1 (by rfl) ⟨2021390, by rfl⟩ : syracuseStep 2695187 = 4042781) B4042781
theorem B1597459 : Blo 1596997 1597459 := bstep (se 1 (by rfl) ⟨1198094, by rfl⟩ : syracuseStep 1597459 = 2396189) B2396189
theorem B1597475 : Blo 1596997 1597475 := bstep (se 1 (by rfl) ⟨1198106, by rfl⟩ : syracuseStep 1597475 = 2396213) B2396213
theorem B1597491 : Blo 1596997 1597491 := bstep (se 1 (by rfl) ⟨1198118, by rfl⟩ : syracuseStep 1597491 = 2396237) B2396237
theorem B1597507 : Blo 1596997 1597507 := bstep (se 1 (by rfl) ⟨1198130, by rfl⟩ : syracuseStep 1597507 = 2396261) B2396261
theorem B8085581 : Blo 1596997 8085581 := bstep (se 3 (by rfl) ⟨1516046, by rfl⟩ : syracuseStep 8085581 = 3032093) B3032093
theorem B1597523 : Blo 1596997 1597523 := bstep (se 1 (by rfl) ⟨1198142, by rfl⟩ : syracuseStep 1597523 = 2396285) B2396285
theorem B1597539 : Blo 1596997 1597539 := bstep (se 1 (by rfl) ⟨1198154, by rfl⟩ : syracuseStep 1597539 = 2396309) B2396309
theorem B10379377 : Blo 1596997 10379377 := bstep (se 2 (by rfl) ⟨3892266, by rfl⟩ : syracuseStep 10379377 = 7784533) B7784533
theorem B1597555 : Blo 1596997 1597555 := bstep (se 1 (by rfl) ⟨1198166, by rfl⟩ : syracuseStep 1597555 = 2396333) B2396333
theorem B1597571 : Blo 1596997 1597571 := bstep (se 1 (by rfl) ⟨1198178, by rfl⟩ : syracuseStep 1597571 = 2396357) B2396357
theorem B3891331 : Blo 1596997 3891331 := bstep (se 1 (by rfl) ⟨2918498, by rfl⟩ : syracuseStep 3891331 = 5836997) B5836997
theorem B4046993 : Blo 1596997 4046993 := bstep (se 2 (by rfl) ⟨1517622, by rfl⟩ : syracuseStep 4046993 = 3035245) B3035245
theorem B2695315 : Blo 1596997 2695315 := bstep (se 1 (by rfl) ⟨2021486, by rfl⟩ : syracuseStep 2695315 = 4042973) B4042973
theorem B1597587 : Blo 1596997 1597587 := bstep (se 1 (by rfl) ⟨1198190, by rfl⟩ : syracuseStep 1597587 = 2396381) B2396381
theorem B1597603 : Blo 1596997 1597603 := bstep (se 1 (by rfl) ⟨1198202, by rfl⟩ : syracuseStep 1597603 = 2396405) B2396405
theorem B1597619 : Blo 1596997 1597619 := bstep (se 1 (by rfl) ⟨1198214, by rfl⟩ : syracuseStep 1597619 = 2396429) B2396429
theorem B1597635 : Blo 1596997 1597635 := bstep (se 1 (by rfl) ⟨1198226, by rfl⟩ : syracuseStep 1597635 = 2396453) B2396453
theorem B4047043 : Blo 1596997 4047043 := bstep (se 1 (by rfl) ⟨3035282, by rfl⟩ : syracuseStep 4047043 = 6070565) B6070565
theorem B1597651 : Blo 1596997 1597651 := bstep (se 1 (by rfl) ⟨1198238, by rfl⟩ : syracuseStep 1597651 = 2396477) B2396477
theorem B1597667 : Blo 1596997 1597667 := bstep (se 1 (by rfl) ⟨1198250, by rfl⟩ : syracuseStep 1597667 = 2396501) B2396501
theorem B1597683 : Blo 1596997 1597683 := bstep (se 1 (by rfl) ⟨1198262, by rfl⟩ : syracuseStep 1597683 = 2396525) B2396525
theorem B1597699 : Blo 1596997 1597699 := bstep (se 1 (by rfl) ⟨1198274, by rfl⟩ : syracuseStep 1597699 = 2396549) B2396549
theorem B5120273 : Blo 1596997 5120273 := bstep (se 2 (by rfl) ⟨1920102, by rfl⟩ : syracuseStep 5120273 = 3840205) B3840205
theorem B3596561 : Blo 1596997 3596561 := bstep (se 2 (by rfl) ⟨1348710, by rfl⟩ : syracuseStep 3596561 = 2697421) B2697421
theorem B1597715 : Blo 1596997 1597715 := bstep (se 1 (by rfl) ⟨1198286, by rfl⟩ : syracuseStep 1597715 = 2396573) B2396573
theorem B2023699 : Blo 1596997 2023699 := bstep (se 1 (by rfl) ⟨1517774, by rfl⟩ : syracuseStep 2023699 = 3035549) B3035549
theorem B2695457 : Blo 1596997 2695457 := bstep (se 2 (by rfl) ⟨1010796, by rfl⟩ : syracuseStep 2695457 = 2021593) B2021593
theorem B1597731 : Blo 1596997 1597731 := bstep (se 1 (by rfl) ⟨1198298, by rfl⟩ : syracuseStep 1597731 = 2396597) B2396597
theorem B3596579 : Blo 1596997 3596579 := bstep (se 1 (by rfl) ⟨2697434, by rfl⟩ : syracuseStep 3596579 = 5394869) B5394869
theorem B1597747 : Blo 1596997 1597747 := bstep (se 1 (by rfl) ⟨1198310, by rfl⟩ : syracuseStep 1597747 = 2396621) B2396621
theorem B1597763 : Blo 1596997 1597763 := bstep (se 1 (by rfl) ⟨1198322, by rfl⟩ : syracuseStep 1597763 = 2396645) B2396645
theorem B4047185 : Blo 1596997 4047185 := bstep (se 2 (by rfl) ⟨1517694, by rfl⟩ : syracuseStep 4047185 = 3035389) B3035389
theorem B1597779 : Blo 1596997 1597779 := bstep (se 1 (by rfl) ⟨1198334, by rfl⟩ : syracuseStep 1597779 = 2396669) B2396669
theorem B1597795 : Blo 1596997 1597795 := bstep (se 1 (by rfl) ⟨1198346, by rfl⟩ : syracuseStep 1597795 = 2396693) B2396693
theorem B1597811 : Blo 1596997 1597811 := bstep (se 1 (by rfl) ⟨1198358, by rfl⟩ : syracuseStep 1597811 = 2396717) B2396717
theorem B1597827 : Blo 1596997 1597827 := bstep (se 1 (by rfl) ⟨1198370, by rfl⟩ : syracuseStep 1597827 = 2396741) B2396741
theorem B1597843 : Blo 1596997 1597843 := bstep (se 1 (by rfl) ⟨1198382, by rfl⟩ : syracuseStep 1597843 = 2396765) B2396765
theorem B2695585 : Blo 1596997 2695585 := bstep (se 2 (by rfl) ⟨1010844, by rfl⟩ : syracuseStep 2695585 = 2021689) B2021689
theorem B1597859 : Blo 1596997 1597859 := bstep (se 1 (by rfl) ⟨1198394, by rfl⟩ : syracuseStep 1597859 = 2396789) B2396789
theorem B5390765 : Blo 1596997 5390765 := bstep (se 3 (by rfl) ⟨1010768, by rfl⟩ : syracuseStep 5390765 = 2021537) B2021537
theorem B1597875 : Blo 1596997 1597875 := bstep (se 1 (by rfl) ⟨1198406, by rfl⟩ : syracuseStep 1597875 = 2396813) B2396813
theorem B2695619 : Blo 1596997 2695619 := bstep (se 1 (by rfl) ⟨2021714, by rfl⟩ : syracuseStep 2695619 = 4043429) B4043429
theorem B1597891 : Blo 1596997 1597891 := bstep (se 1 (by rfl) ⟨1198418, by rfl⟩ : syracuseStep 1597891 = 2396837) B2396837
theorem B6070733 : Blo 1596997 6070733 := bstep (se 3 (by rfl) ⟨1138262, by rfl⟩ : syracuseStep 6070733 = 2276525) B2276525
theorem B1597907 : Blo 1596997 1597907 := bstep (se 1 (by rfl) ⟨1198430, by rfl⟩ : syracuseStep 1597907 = 2396861) B2396861
theorem B3457507 : Blo 1596997 3457507 := bstep (se 1 (by rfl) ⟨2593130, by rfl⟩ : syracuseStep 3457507 = 5186261) B5186261
theorem B5390819 : Blo 1596997 5390819 := bstep (se 1 (by rfl) ⟨4043114, by rfl⟩ : syracuseStep 5390819 = 8086229) B8086229
theorem B1597923 : Blo 1596997 1597923 := bstep (se 1 (by rfl) ⟨1198442, by rfl⟩ : syracuseStep 1597923 = 2396885) B2396885
theorem B1597939 : Blo 1596997 1597939 := bstep (se 1 (by rfl) ⟨1198454, by rfl⟩ : syracuseStep 1597939 = 2396909) B2396909
theorem B1597955 : Blo 1596997 1597955 := bstep (se 1 (by rfl) ⟨1198466, by rfl⟩ : syracuseStep 1597955 = 2396933) B2396933
theorem B20480525 : Blo 1596997 20480525 := bstep (se 3 (by rfl) ⟨3840098, by rfl⟩ : syracuseStep 20480525 = 7680197) B7680197
theorem B1597971 : Blo 1596997 1597971 := bstep (se 1 (by rfl) ⟨1198478, by rfl⟩ : syracuseStep 1597971 = 2396957) B2396957
theorem B1597987 : Blo 1596997 1597987 := bstep (se 1 (by rfl) ⟨1198490, by rfl⟩ : syracuseStep 1597987 = 2396981) B2396981
theorem B3596849 : Blo 1596997 3596849 := bstep (se 2 (by rfl) ⟨1348818, by rfl⟩ : syracuseStep 3596849 = 2697637) B2697637
theorem B1598003 : Blo 1596997 1598003 := bstep (se 1 (by rfl) ⟨1198502, by rfl⟩ : syracuseStep 1598003 = 2397005) B2397005
theorem B2695747 : Blo 1596997 2695747 := bstep (se 1 (by rfl) ⟨2021810, by rfl⟩ : syracuseStep 2695747 = 4043621) B4043621
theorem B1598019 : Blo 1596997 1598019 := bstep (se 1 (by rfl) ⟨1198514, by rfl⟩ : syracuseStep 1598019 = 2397029) B2397029
theorem B3596867 : Blo 1596997 3596867 := bstep (se 1 (by rfl) ⟨2697650, by rfl⟩ : syracuseStep 3596867 = 5395301) B5395301
theorem B5915213 : Blo 1596997 5915213 := bstep (se 3 (by rfl) ⟨1109102, by rfl⟩ : syracuseStep 5915213 = 2218205) B2218205
theorem B1598035 : Blo 1596997 1598035 := bstep (se 1 (by rfl) ⟨1198526, by rfl⟩ : syracuseStep 1598035 = 2397053) B2397053
theorem B1598051 : Blo 1596997 1598051 := bstep (se 1 (by rfl) ⟨1198538, by rfl⟩ : syracuseStep 1598051 = 2397077) B2397077
theorem B8643185 : Blo 1596997 8643185 := bstep (se 2 (by rfl) ⟨3241194, by rfl⟩ : syracuseStep 8643185 = 6482389) B6482389
theorem B1598067 : Blo 1596997 1598067 := bstep (se 1 (by rfl) ⟨1198550, by rfl⟩ : syracuseStep 1598067 = 2397101) B2397101
theorem B1598083 : Blo 1596997 1598083 := bstep (se 1 (by rfl) ⟨1198562, by rfl⟩ : syracuseStep 1598083 = 2397125) B2397125
theorem B1598099 : Blo 1596997 1598099 := bstep (se 1 (by rfl) ⟨1198574, by rfl⟩ : syracuseStep 1598099 = 2397149) B2397149
theorem B1598115 : Blo 1596997 1598115 := bstep (se 1 (by rfl) ⟨1198586, by rfl⟩ : syracuseStep 1598115 = 2397173) B2397173
theorem B1598131 : Blo 1596997 1598131 := bstep (se 1 (by rfl) ⟨1198598, by rfl⟩ : syracuseStep 1598131 = 2397197) B2397197
theorem B1598147 : Blo 1596997 1598147 := bstep (se 1 (by rfl) ⟨1198610, by rfl⟩ : syracuseStep 1598147 = 2397221) B2397221
theorem B2695889 : Blo 1596997 2695889 := bstep (se 2 (by rfl) ⟨1010958, by rfl⟩ : syracuseStep 2695889 = 2021917) B2021917
theorem B1729235 : Blo 1596997 1729235 := bstep (se 1 (by rfl) ⟨1296926, by rfl⟩ : syracuseStep 1729235 = 2593853) B2593853
theorem B1598163 : Blo 1596997 1598163 := bstep (se 1 (by rfl) ⟨1198622, by rfl⟩ : syracuseStep 1598163 = 2397245) B2397245
theorem B1598179 : Blo 1596997 1598179 := bstep (se 1 (by rfl) ⟨1198634, by rfl⟩ : syracuseStep 1598179 = 2397269) B2397269
theorem B5391089 : Blo 1596997 5391089 := bstep (se 2 (by rfl) ⟨2021658, by rfl⟩ : syracuseStep 5391089 = 4043317) B4043317
theorem B1598195 : Blo 1596997 1598195 := bstep (se 1 (by rfl) ⟨1198646, by rfl⟩ : syracuseStep 1598195 = 2397293) B2397293
theorem B1598211 : Blo 1596997 1598211 := bstep (se 1 (by rfl) ⟨1198658, by rfl⟩ : syracuseStep 1598211 = 2397317) B2397317
theorem B1598227 : Blo 1596997 1598227 := bstep (se 1 (by rfl) ⟨1198670, by rfl⟩ : syracuseStep 1598227 = 2397341) B2397341
theorem B3031843 : Blo 1596997 3031843 := bstep (se 1 (by rfl) ⟨2273882, by rfl⟩ : syracuseStep 3031843 = 4547765) B4547765
theorem B1598243 : Blo 1596997 1598243 := bstep (se 1 (by rfl) ⟨1198682, by rfl⟩ : syracuseStep 1598243 = 2397365) B2397365
theorem B1598259 : Blo 1596997 1598259 := bstep (se 1 (by rfl) ⟨1198694, by rfl⟩ : syracuseStep 1598259 = 2397389) B2397389
theorem B1598275 : Blo 1596997 1598275 := bstep (se 1 (by rfl) ⟨1198706, by rfl⟩ : syracuseStep 1598275 = 2397413) B2397413
theorem B2696017 : Blo 1596997 2696017 := bstep (se 2 (by rfl) ⟨1011006, by rfl⟩ : syracuseStep 2696017 = 2022013) B2022013
theorem B3597137 : Blo 1596997 3597137 := bstep (se 2 (by rfl) ⟨1348926, by rfl⟩ : syracuseStep 3597137 = 2697853) B2697853
theorem B1598291 : Blo 1596997 1598291 := bstep (se 1 (by rfl) ⟨1198718, by rfl⟩ : syracuseStep 1598291 = 2397437) B2397437
theorem B1598307 : Blo 1596997 1598307 := bstep (se 1 (by rfl) ⟨1198730, by rfl⟩ : syracuseStep 1598307 = 2397461) B2397461
theorem B3597155 : Blo 1596997 3597155 := bstep (se 1 (by rfl) ⟨2697866, by rfl⟩ : syracuseStep 3597155 = 5395733) B5395733
theorem B34554737 : Blo 1596997 34554737 := bstep (se 2 (by rfl) ⟨12958026, by rfl⟩ : syracuseStep 34554737 = 25916053) B25916053
theorem B2696051 : Blo 1596997 2696051 := bstep (se 1 (by rfl) ⟨2022038, by rfl⟩ : syracuseStep 2696051 = 4044077) B4044077
theorem B1598323 : Blo 1596997 1598323 := bstep (se 1 (by rfl) ⟨1198742, by rfl⟩ : syracuseStep 1598323 = 2397485) B2397485
theorem B1598339 : Blo 1596997 1598339 := bstep (se 1 (by rfl) ⟨1198754, by rfl⟩ : syracuseStep 1598339 = 2397509) B2397509
theorem B10240901 : Blo 1596997 10240901 := bstep (se 4 (by rfl) ⟨960084, by rfl⟩ : syracuseStep 10240901 = 1920169) B1920169
theorem B1598355 : Blo 1596997 1598355 := bstep (se 1 (by rfl) ⟨1198766, by rfl⟩ : syracuseStep 1598355 = 2397533) B2397533
theorem B1598371 : Blo 1596997 1598371 := bstep (se 1 (by rfl) ⟨1198778, by rfl⟩ : syracuseStep 1598371 = 2397557) B2397557
theorem B1598387 : Blo 1596997 1598387 := bstep (se 1 (by rfl) ⟨1198790, by rfl⟩ : syracuseStep 1598387 = 2397581) B2397581
theorem B1598403 : Blo 1596997 1598403 := bstep (se 1 (by rfl) ⟨1198802, by rfl⟩ : syracuseStep 1598403 = 2397605) B2397605
theorem B17277893 : Blo 1596997 17277893 := bstep (se 4 (by rfl) ⟨1619802, by rfl⟩ : syracuseStep 17277893 = 3239605) B3239605
theorem B1598419 : Blo 1596997 1598419 := bstep (se 1 (by rfl) ⟨1198814, by rfl⟩ : syracuseStep 1598419 = 2397629) B2397629
theorem B1598435 : Blo 1596997 1598435 := bstep (se 1 (by rfl) ⟨1198826, by rfl⟩ : syracuseStep 1598435 = 2397653) B2397653
theorem B2696179 : Blo 1596997 2696179 := bstep (se 1 (by rfl) ⟨2022134, by rfl⟩ : syracuseStep 2696179 = 4044269) B4044269
theorem B1598451 : Blo 1596997 1598451 := bstep (se 1 (by rfl) ⟨1198838, by rfl⟩ : syracuseStep 1598451 = 2397677) B2397677
theorem B1598467 : Blo 1596997 1598467 := bstep (se 1 (by rfl) ⟨1198850, by rfl⟩ : syracuseStep 1598467 = 2397701) B2397701
theorem B1598483 : Blo 1596997 1598483 := bstep (se 1 (by rfl) ⟨1198862, by rfl⟩ : syracuseStep 1598483 = 2397725) B2397725
theorem B5760035 : Blo 1596997 5760035 := bstep (se 1 (by rfl) ⟨4320026, by rfl⟩ : syracuseStep 5760035 = 8640053) B8640053
theorem B1598499 : Blo 1596997 1598499 := bstep (se 1 (by rfl) ⟨1198874, by rfl⟩ : syracuseStep 1598499 = 2397749) B2397749
theorem B1598515 : Blo 1596997 1598515 := bstep (se 1 (by rfl) ⟨1198886, by rfl⟩ : syracuseStep 1598515 = 2397773) B2397773
theorem B1598531 : Blo 1596997 1598531 := bstep (se 1 (by rfl) ⟨1198898, by rfl⟩ : syracuseStep 1598531 = 2397797) B2397797
theorem B1598547 : Blo 1596997 1598547 := bstep (se 1 (by rfl) ⟨1198910, by rfl⟩ : syracuseStep 1598547 = 2397821) B2397821
theorem B12133475 : Blo 1596997 12133475 := bstep (se 1 (by rfl) ⟨9100106, by rfl⟩ : syracuseStep 12133475 = 18200213) B18200213
theorem B15361123 : Blo 1596997 15361123 := bstep (se 1 (by rfl) ⟨11520842, by rfl⟩ : syracuseStep 15361123 = 23041685) B23041685
theorem B1598563 : Blo 1596997 1598563 := bstep (se 1 (by rfl) ⟨1198922, by rfl⟩ : syracuseStep 1598563 = 2397845) B2397845
theorem B3597425 : Blo 1596997 3597425 := bstep (se 2 (by rfl) ⟨1349034, by rfl⟩ : syracuseStep 3597425 = 2698069) B2698069
theorem B1598579 : Blo 1596997 1598579 := bstep (se 1 (by rfl) ⟨1198934, by rfl⟩ : syracuseStep 1598579 = 2397869) B2397869
theorem B2696321 : Blo 1596997 2696321 := bstep (se 2 (by rfl) ⟨1011120, by rfl⟩ : syracuseStep 2696321 = 2022241) B2022241
theorem B1598595 : Blo 1596997 1598595 := bstep (se 1 (by rfl) ⟨1198946, by rfl⟩ : syracuseStep 1598595 = 2397893) B2397893
theorem B3597443 : Blo 1596997 3597443 := bstep (se 1 (by rfl) ⟨2698082, by rfl⟩ : syracuseStep 3597443 = 5396165) B5396165
theorem B2188435 : Blo 1596997 2188435 := bstep (se 1 (by rfl) ⟨1641326, by rfl⟩ : syracuseStep 2188435 = 3282653) B3282653
theorem B1598611 : Blo 1596997 1598611 := bstep (se 1 (by rfl) ⟨1198958, by rfl⟩ : syracuseStep 1598611 = 2397917) B2397917
theorem B1598627 : Blo 1596997 1598627 := bstep (se 1 (by rfl) ⟨1198970, by rfl⟩ : syracuseStep 1598627 = 2397941) B2397941
theorem B1598643 : Blo 1596997 1598643 := bstep (se 1 (by rfl) ⟨1198982, by rfl⟩ : syracuseStep 1598643 = 2397965) B2397965
theorem B1598659 : Blo 1596997 1598659 := bstep (se 1 (by rfl) ⟨1198994, by rfl⟩ : syracuseStep 1598659 = 2397989) B2397989
theorem B1598675 : Blo 1596997 1598675 := bstep (se 1 (by rfl) ⟨1199006, by rfl⟩ : syracuseStep 1598675 = 2398013) B2398013
theorem B3032291 : Blo 1596997 3032291 := bstep (se 1 (by rfl) ⟨2274218, by rfl⟩ : syracuseStep 3032291 = 4548437) B4548437
theorem B1598691 : Blo 1596997 1598691 := bstep (se 1 (by rfl) ⟨1199018, by rfl⟩ : syracuseStep 1598691 = 2398037) B2398037
theorem B4547821 : Blo 1596997 4547821 := bstep (se 3 (by rfl) ⟨852716, by rfl⟩ : syracuseStep 4547821 = 1705433) B1705433
theorem B1598707 : Blo 1596997 1598707 := bstep (se 1 (by rfl) ⟨1199030, by rfl⟩ : syracuseStep 1598707 = 2398061) B2398061
theorem B2696449 : Blo 1596997 2696449 := bstep (se 2 (by rfl) ⟨1011168, by rfl⟩ : syracuseStep 2696449 = 2022337) B2022337
theorem B1598723 : Blo 1596997 1598723 := bstep (se 1 (by rfl) ⟨1199042, by rfl⟩ : syracuseStep 1598723 = 2398085) B2398085
theorem B5391629 : Blo 1596997 5391629 := bstep (se 3 (by rfl) ⟨1010930, by rfl⟩ : syracuseStep 5391629 = 2021861) B2021861
theorem B1598739 : Blo 1596997 1598739 := bstep (se 1 (by rfl) ⟨1199054, by rfl⟩ : syracuseStep 1598739 = 2398109) B2398109
theorem B2696483 : Blo 1596997 2696483 := bstep (se 1 (by rfl) ⟨2022362, by rfl⟩ : syracuseStep 2696483 = 4044725) B4044725
theorem B1598755 : Blo 1596997 1598755 := bstep (se 1 (by rfl) ⟨1199066, by rfl⟩ : syracuseStep 1598755 = 2398133) B2398133
theorem B1598771 : Blo 1596997 1598771 := bstep (se 1 (by rfl) ⟨1199078, by rfl⟩ : syracuseStep 1598771 = 2398157) B2398157
theorem B5391683 : Blo 1596997 5391683 := bstep (se 1 (by rfl) ⟨4043762, by rfl⟩ : syracuseStep 5391683 = 8087525) B8087525
theorem B1598787 : Blo 1596997 1598787 := bstep (se 1 (by rfl) ⟨1199090, by rfl⟩ : syracuseStep 1598787 = 2398181) B2398181
theorem B1598803 : Blo 1596997 1598803 := bstep (se 1 (by rfl) ⟨1199102, by rfl⟩ : syracuseStep 1598803 = 2398205) B2398205
theorem B1598819 : Blo 1596997 1598819 := bstep (se 1 (by rfl) ⟨1199114, by rfl⟩ : syracuseStep 1598819 = 2398229) B2398229
theorem B1598835 : Blo 1596997 1598835 := bstep (se 1 (by rfl) ⟨1199126, by rfl⟩ : syracuseStep 1598835 = 2398253) B2398253
theorem B1598851 : Blo 1596997 1598851 := bstep (se 1 (by rfl) ⟨1199138, by rfl⟩ : syracuseStep 1598851 = 2398277) B2398277
theorem B4547981 : Blo 1596997 4547981 := bstep (se 3 (by rfl) ⟨852746, by rfl⟩ : syracuseStep 4547981 = 1705493) B1705493
theorem B3597713 : Blo 1596997 3597713 := bstep (se 2 (by rfl) ⟨1349142, by rfl⟩ : syracuseStep 3597713 = 2698285) B2698285
theorem B1598867 : Blo 1596997 1598867 := bstep (se 1 (by rfl) ⟨1199150, by rfl⟩ : syracuseStep 1598867 = 2398301) B2398301
theorem B2696611 : Blo 1596997 2696611 := bstep (se 1 (by rfl) ⟨2022458, by rfl⟩ : syracuseStep 2696611 = 4044917) B4044917
theorem B1598883 : Blo 1596997 1598883 := bstep (se 1 (by rfl) ⟨1199162, by rfl⟩ : syracuseStep 1598883 = 2398325) B2398325
theorem B3597731 : Blo 1596997 3597731 := bstep (se 1 (by rfl) ⟨2698298, by rfl⟩ : syracuseStep 3597731 = 5396597) B5396597
theorem B1598899 : Blo 1596997 1598899 := bstep (se 1 (by rfl) ⟨1199174, by rfl⟩ : syracuseStep 1598899 = 2398349) B2398349
theorem B1598915 : Blo 1596997 1598915 := bstep (se 1 (by rfl) ⟨1199186, by rfl⟩ : syracuseStep 1598915 = 2398373) B2398373
theorem B1598931 : Blo 1596997 1598931 := bstep (se 1 (by rfl) ⟨1199198, by rfl⟩ : syracuseStep 1598931 = 2398397) B2398397
theorem B1598947 : Blo 1596997 1598947 := bstep (se 1 (by rfl) ⟨1199210, by rfl⟩ : syracuseStep 1598947 = 2398421) B2398421
theorem B1598963 : Blo 1596997 1598963 := bstep (se 1 (by rfl) ⟨1199222, by rfl⟩ : syracuseStep 1598963 = 2398445) B2398445
theorem B3032579 : Blo 1596997 3032579 := bstep (se 1 (by rfl) ⟨2274434, by rfl⟩ : syracuseStep 3032579 = 4548869) B4548869
theorem B1598979 : Blo 1596997 1598979 := bstep (se 1 (by rfl) ⟨1199234, by rfl⟩ : syracuseStep 1598979 = 2398469) B2398469
theorem B7489037 : Blo 1596997 7489037 := bstep (se 3 (by rfl) ⟨1404194, by rfl⟩ : syracuseStep 7489037 = 2808389) B2808389
theorem B1598995 : Blo 1596997 1598995 := bstep (se 1 (by rfl) ⟨1199246, by rfl⟩ : syracuseStep 1598995 = 2398493) B2398493
theorem B2696753 : Blo 1596997 2696753 := bstep (se 2 (by rfl) ⟨1011282, by rfl⟩ : syracuseStep 2696753 = 2022565) B2022565
theorem B20473397 : Blo 1596997 20473397 := bstep (se 5 (by rfl) ⟨959690, by rfl⟩ : syracuseStep 20473397 = 1919381) B1919381
theorem B4548163 : Blo 1596997 4548163 := bstep (se 1 (by rfl) ⟨3411122, by rfl⟩ : syracuseStep 4548163 = 6822245) B6822245
theorem B5391953 : Blo 1596997 5391953 := bstep (se 2 (by rfl) ⟨2021982, by rfl⟩ : syracuseStep 5391953 = 4043965) B4043965
theorem B2696881 : Blo 1596997 2696881 := bstep (se 2 (by rfl) ⟨1011330, by rfl⟩ : syracuseStep 2696881 = 2022661) B2022661
theorem B2696915 : Blo 1596997 2696915 := bstep (se 1 (by rfl) ⟨2022686, by rfl⟩ : syracuseStep 2696915 = 4045373) B4045373
theorem B2697043 : Blo 1596997 2697043 := bstep (se 1 (by rfl) ⟨2022782, by rfl⟩ : syracuseStep 2697043 = 4045565) B4045565
theorem B4319075 : Blo 1596997 4319075 := bstep (se 1 (by rfl) ⟨3239306, by rfl⟩ : syracuseStep 4319075 = 6478613) B6478613
theorem B1705843 : Blo 1596997 1705843 := bstep (se 1 (by rfl) ⟨1279382, by rfl⟩ : syracuseStep 1705843 = 2558765) B2558765
theorem B2697185 : Blo 1596997 2697185 := bstep (se 2 (by rfl) ⟨1011444, by rfl⟩ : syracuseStep 2697185 = 2022889) B2022889
theorem B2697313 : Blo 1596997 2697313 := bstep (se 2 (by rfl) ⟨1011492, by rfl⟩ : syracuseStep 2697313 = 2022985) B2022985
theorem B5392493 : Blo 1596997 5392493 := bstep (se 3 (by rfl) ⟨1011092, by rfl⟩ : syracuseStep 5392493 = 2022185) B2022185
theorem B2697347 : Blo 1596997 2697347 := bstep (se 1 (by rfl) ⟨2023010, by rfl⟩ : syracuseStep 2697347 = 4046021) B4046021
theorem B5392547 : Blo 1596997 5392547 := bstep (se 1 (by rfl) ⟨4044410, by rfl⟩ : syracuseStep 5392547 = 8088821) B8088821
theorem B2697475 : Blo 1596997 2697475 := bstep (se 1 (by rfl) ⟨2023106, by rfl⟩ : syracuseStep 2697475 = 4046213) B4046213
theorem B5122349 : Blo 1596997 5122349 := bstep (se 3 (by rfl) ⟨960440, by rfl⟩ : syracuseStep 5122349 = 1920881) B1920881
theorem B3238211 : Blo 1596997 3238211 := bstep (se 1 (by rfl) ⟨2428658, by rfl⟩ : syracuseStep 3238211 = 4857317) B4857317
theorem B3074449 : Blo 1596997 3074449 := bstep (se 2 (by rfl) ⟨1152918, by rfl⟩ : syracuseStep 3074449 = 2305837) B2305837
theorem B2697617 : Blo 1596997 2697617 := bstep (se 2 (by rfl) ⟨1011606, by rfl⟩ : syracuseStep 2697617 = 2023213) B2023213
theorem B4377005 : Blo 1596997 4377005 := bstep (se 3 (by rfl) ⟨820688, by rfl⟩ : syracuseStep 4377005 = 1641377) B1641377
theorem B5392817 : Blo 1596997 5392817 := bstep (se 2 (by rfl) ⟨2022306, by rfl⟩ : syracuseStep 5392817 = 4044613) B4044613
theorem B3033521 : Blo 1596997 3033521 := bstep (se 2 (by rfl) ⟨1137570, by rfl⟩ : syracuseStep 3033521 = 2275141) B2275141
theorem B2877905 : Blo 1596997 2877905 := bstep (se 2 (by rfl) ⟨1079214, by rfl⟩ : syracuseStep 2877905 = 2158429) B2158429
theorem B5835235 : Blo 1596997 5835235 := bstep (se 1 (by rfl) ⟨4376426, by rfl⟩ : syracuseStep 5835235 = 8752853) B8752853
theorem B2697745 : Blo 1596997 2697745 := bstep (se 2 (by rfl) ⟨1011654, by rfl⟩ : syracuseStep 2697745 = 2023309) B2023309
theorem B4614673 : Blo 1596997 4614673 := bstep (se 2 (by rfl) ⟨1730502, by rfl⟩ : syracuseStep 4614673 = 3461005) B3461005
theorem B2558483 : Blo 1596997 2558483 := bstep (se 1 (by rfl) ⟨1918862, by rfl⟩ : syracuseStep 2558483 = 3837725) B3837725
theorem B2697779 : Blo 1596997 2697779 := bstep (se 1 (by rfl) ⟨2023334, by rfl⟩ : syracuseStep 2697779 = 4046669) B4046669
theorem B1796755 : Blo 1596997 1796755 := bstep (se 1 (by rfl) ⟨1347566, by rfl⟩ : syracuseStep 1796755 = 2695133) B2695133
theorem B2697907 : Blo 1596997 2697907 := bstep (se 1 (by rfl) ⟨2023430, by rfl⟩ : syracuseStep 2697907 = 4046861) B4046861
theorem B1796899 : Blo 1596997 1796899 := bstep (se 1 (by rfl) ⟨1347674, by rfl⟩ : syracuseStep 1796899 = 2695349) B2695349
theorem B2558785 : Blo 1596997 2558785 := bstep (se 2 (by rfl) ⟨959544, by rfl⟩ : syracuseStep 2558785 = 1919089) B1919089
theorem B2698049 : Blo 1596997 2698049 := bstep (se 2 (by rfl) ⟨1011768, by rfl⟩ : syracuseStep 2698049 = 2023537) B2023537
theorem B10521413 : Blo 1596997 10521413 := bstep (se 4 (by rfl) ⟨986382, by rfl⟩ : syracuseStep 10521413 = 1972765) B1972765
theorem B8637283 : Blo 1596997 8637283 := bstep (se 1 (by rfl) ⟨6477962, by rfl⟩ : syracuseStep 8637283 = 12955925) B12955925
theorem B1706851 : Blo 1596997 1706851 := bstep (se 1 (by rfl) ⟨1280138, by rfl⟩ : syracuseStep 1706851 = 2560277) B2560277
theorem B5761891 : Blo 1596997 5761891 := bstep (se 1 (by rfl) ⟨4321418, by rfl⟩ : syracuseStep 5761891 = 8642837) B8642837
theorem B4549553 : Blo 1596997 4549553 := bstep (se 2 (by rfl) ⟨1706082, by rfl⟩ : syracuseStep 4549553 = 3412165) B3412165
theorem B8088497 : Blo 1596997 8088497 := bstep (se 2 (by rfl) ⟨3033186, by rfl⟩ : syracuseStep 8088497 = 6066373) B6066373
theorem B1797043 : Blo 1596997 1797043 := bstep (se 1 (by rfl) ⟨1347782, by rfl⟩ : syracuseStep 1797043 = 2695565) B2695565
theorem B2698177 : Blo 1596997 2698177 := bstep (se 2 (by rfl) ⟨1011816, by rfl⟩ : syracuseStep 2698177 = 2023633) B2023633
theorem B5393357 : Blo 1596997 5393357 := bstep (se 3 (by rfl) ⟨1011254, by rfl⟩ : syracuseStep 5393357 = 2022509) B2022509
theorem B4320209 : Blo 1596997 4320209 := bstep (se 2 (by rfl) ⟨1620078, by rfl⟩ : syracuseStep 4320209 = 3240157) B3240157
theorem B2698211 : Blo 1596997 2698211 := bstep (se 1 (by rfl) ⟨2023658, by rfl⟩ : syracuseStep 2698211 = 4047317) B4047317
theorem B5393411 : Blo 1596997 5393411 := bstep (se 1 (by rfl) ⟨4045058, by rfl⟩ : syracuseStep 5393411 = 8090117) B8090117
theorem B3746819 : Blo 1596997 3746819 := bstep (se 1 (by rfl) ⟨2810114, by rfl⟩ : syracuseStep 3746819 = 5620229) B5620229
theorem B2558995 : Blo 1596997 2558995 := bstep (se 1 (by rfl) ⟨1919246, by rfl⟩ : syracuseStep 2558995 = 3838493) B3838493
theorem B2559041 : Blo 1596997 2559041 := bstep (se 2 (by rfl) ⟨959640, by rfl⟩ : syracuseStep 2559041 = 1919281) B1919281
theorem B1797187 : Blo 1596997 1797187 := bstep (se 1 (by rfl) ⟨1347890, by rfl⟩ : syracuseStep 1797187 = 2695781) B2695781
theorem B1797331 : Blo 1596997 1797331 := bstep (se 1 (by rfl) ⟨1347998, by rfl⟩ : syracuseStep 1797331 = 2695997) B2695997
theorem B5393681 : Blo 1596997 5393681 := bstep (se 2 (by rfl) ⟨2022630, by rfl⟩ : syracuseStep 5393681 = 4045261) B4045261
theorem B3034417 : Blo 1596997 3034417 := bstep (se 2 (by rfl) ⟨1137906, by rfl⟩ : syracuseStep 3034417 = 2275813) B2275813
theorem B5762353 : Blo 1596997 5762353 := bstep (se 2 (by rfl) ⟨2160882, by rfl⟩ : syracuseStep 5762353 = 4321765) B4321765
theorem B1797475 : Blo 1596997 1797475 := bstep (se 1 (by rfl) ⟨1348106, by rfl⟩ : syracuseStep 1797475 = 2696213) B2696213
theorem B2395505 : Blo 1596997 2395505 := bstep (se 2 (by rfl) ⟨898314, by rfl⟩ : syracuseStep 2395505 = 1796629) B1796629
theorem B2395523 : Blo 1596997 2395523 := bstep (se 1 (by rfl) ⟨1796642, by rfl⟩ : syracuseStep 2395523 = 3593285) B3593285
theorem B2395553 : Blo 1596997 2395553 := bstep (se 2 (by rfl) ⟨898332, by rfl⟩ : syracuseStep 2395553 = 1796665) B1796665
theorem B2395571 : Blo 1596997 2395571 := bstep (se 1 (by rfl) ⟨1796678, by rfl⟩ : syracuseStep 2395571 = 3593357) B3593357
theorem B9104845 : Blo 1596997 9104845 := bstep (se 3 (by rfl) ⟨1707158, by rfl⟩ : syracuseStep 9104845 = 3414317) B3414317
theorem B2395601 : Blo 1596997 2395601 := bstep (se 2 (by rfl) ⟨898350, by rfl⟩ : syracuseStep 2395601 = 1796701) B1796701
theorem B3034577 : Blo 1596997 3034577 := bstep (se 2 (by rfl) ⟨1137966, by rfl⟩ : syracuseStep 3034577 = 2275933) B2275933
theorem B1707475 : Blo 1596997 1707475 := bstep (se 1 (by rfl) ⟨1280606, by rfl⟩ : syracuseStep 1707475 = 2561213) B2561213
theorem B2395619 : Blo 1596997 2395619 := bstep (se 1 (by rfl) ⟨1796714, by rfl⟩ : syracuseStep 2395619 = 3593429) B3593429
theorem B1797619 : Blo 1596997 1797619 := bstep (se 1 (by rfl) ⟨1348214, by rfl⟩ : syracuseStep 1797619 = 2696429) B2696429
theorem B2395649 : Blo 1596997 2395649 := bstep (se 2 (by rfl) ⟨898368, by rfl⟩ : syracuseStep 2395649 = 1796737) B1796737
theorem B1920515 : Blo 1596997 1920515 := bstep (se 1 (by rfl) ⟨1440386, by rfl⟩ : syracuseStep 1920515 = 2880773) B2880773
theorem B2305553 : Blo 1596997 2305553 := bstep (se 2 (by rfl) ⟨864582, by rfl⟩ : syracuseStep 2305553 = 1729165) B1729165
theorem B2395667 : Blo 1596997 2395667 := bstep (se 1 (by rfl) ⟨1796750, by rfl⟩ : syracuseStep 2395667 = 3593501) B3593501
theorem B2395697 : Blo 1596997 2395697 := bstep (se 2 (by rfl) ⟨898386, by rfl⟩ : syracuseStep 2395697 = 1796773) B1796773
theorem B2395715 : Blo 1596997 2395715 := bstep (se 1 (by rfl) ⟨1796786, by rfl⟩ : syracuseStep 2395715 = 3593573) B3593573
theorem B2395745 : Blo 1596997 2395745 := bstep (se 2 (by rfl) ⟨898404, by rfl⟩ : syracuseStep 2395745 = 1796809) B1796809
theorem B2395763 : Blo 1596997 2395763 := bstep (se 1 (by rfl) ⟨1796822, by rfl⟩ : syracuseStep 2395763 = 3593645) B3593645
theorem B1797763 : Blo 1596997 1797763 := bstep (se 1 (by rfl) ⟨1348322, by rfl⟩ : syracuseStep 1797763 = 2696645) B2696645
theorem B2395793 : Blo 1596997 2395793 := bstep (se 2 (by rfl) ⟨898422, by rfl⟩ : syracuseStep 2395793 = 1796845) B1796845
theorem B2395811 : Blo 1596997 2395811 := bstep (se 1 (by rfl) ⟨1796858, by rfl⟩ : syracuseStep 2395811 = 3593717) B3593717
theorem B9719473 : Blo 1596997 9719473 := bstep (se 2 (by rfl) ⟨3644802, by rfl⟩ : syracuseStep 9719473 = 7289605) B7289605
theorem B2395841 : Blo 1596997 2395841 := bstep (se 2 (by rfl) ⟨898440, by rfl⟩ : syracuseStep 2395841 = 1796881) B1796881
theorem B2395859 : Blo 1596997 2395859 := bstep (se 1 (by rfl) ⟨1796894, by rfl⟩ : syracuseStep 2395859 = 3593789) B3593789
theorem B2395889 : Blo 1596997 2395889 := bstep (se 2 (by rfl) ⟨898458, by rfl⟩ : syracuseStep 2395889 = 1796917) B1796917
theorem B2395907 : Blo 1596997 2395907 := bstep (se 1 (by rfl) ⟨1796930, by rfl⟩ : syracuseStep 2395907 = 3593861) B3593861
theorem B1797907 : Blo 1596997 1797907 := bstep (se 1 (by rfl) ⟨1348430, by rfl⟩ : syracuseStep 1797907 = 2696861) B2696861
theorem B2395937 : Blo 1596997 2395937 := bstep (se 2 (by rfl) ⟨898476, by rfl⟩ : syracuseStep 2395937 = 1796953) B1796953
theorem B5394221 : Blo 1596997 5394221 := bstep (se 3 (by rfl) ⟨1011416, by rfl⟩ : syracuseStep 5394221 = 2022833) B2022833
theorem B4321073 : Blo 1596997 4321073 := bstep (se 2 (by rfl) ⟨1620402, by rfl⟩ : syracuseStep 4321073 = 3240805) B3240805
theorem B2395955 : Blo 1596997 2395955 := bstep (se 1 (by rfl) ⟨1796966, by rfl⟩ : syracuseStep 2395955 = 3593933) B3593933
theorem B2395985 : Blo 1596997 2395985 := bstep (se 2 (by rfl) ⟨898494, by rfl⟩ : syracuseStep 2395985 = 1796989) B1796989
theorem B2396003 : Blo 1596997 2396003 := bstep (se 1 (by rfl) ⟨1797002, by rfl⟩ : syracuseStep 2396003 = 3594005) B3594005
theorem B5394275 : Blo 1596997 5394275 := bstep (se 1 (by rfl) ⟨4045706, by rfl⟩ : syracuseStep 5394275 = 8091413) B8091413
theorem B3034979 : Blo 1596997 3034979 := bstep (se 1 (by rfl) ⟨2276234, by rfl⟩ : syracuseStep 3034979 = 4552469) B4552469
theorem B4550509 : Blo 1596997 4550509 := bstep (se 3 (by rfl) ⟨853220, by rfl⟩ : syracuseStep 4550509 = 1706441) B1706441
theorem B2396033 : Blo 1596997 2396033 := bstep (se 2 (by rfl) ⟨898512, by rfl⟩ : syracuseStep 2396033 = 1797025) B1797025
theorem B14585741 : Blo 1596997 14585741 := bstep (se 3 (by rfl) ⟨2734826, by rfl⟩ : syracuseStep 14585741 = 5469653) B5469653
theorem B3411857 : Blo 1596997 3411857 := bstep (se 2 (by rfl) ⟨1279446, by rfl⟩ : syracuseStep 3411857 = 2558893) B2558893
theorem B2396051 : Blo 1596997 2396051 := bstep (se 1 (by rfl) ⟨1797038, by rfl⟩ : syracuseStep 2396051 = 3594077) B3594077
theorem B2158499 : Blo 1596997 2158499 := bstep (se 1 (by rfl) ⟨1618874, by rfl⟩ : syracuseStep 2158499 = 3237749) B3237749
theorem B3411875 : Blo 1596997 3411875 := bstep (se 1 (by rfl) ⟨2558906, by rfl⟩ : syracuseStep 3411875 = 5117813) B5117813
theorem B1798051 : Blo 1596997 1798051 := bstep (se 1 (by rfl) ⟨1348538, by rfl⟩ : syracuseStep 1798051 = 2697077) B2697077
theorem B2396081 : Blo 1596997 2396081 := bstep (se 2 (by rfl) ⟨898530, by rfl⟩ : syracuseStep 2396081 = 1797061) B1797061
theorem B7286705 : Blo 1596997 7286705 := bstep (se 2 (by rfl) ⟨2732514, by rfl⟩ : syracuseStep 7286705 = 5465029) B5465029
theorem B2396099 : Blo 1596997 2396099 := bstep (se 1 (by rfl) ⟨1797074, by rfl⟩ : syracuseStep 2396099 = 3594149) B3594149
theorem B2158547 : Blo 1596997 2158547 := bstep (se 1 (by rfl) ⟨1618910, by rfl⟩ : syracuseStep 2158547 = 3237821) B3237821
theorem B2396129 : Blo 1596997 2396129 := bstep (se 2 (by rfl) ⟨898548, by rfl⟩ : syracuseStep 2396129 = 1797097) B1797097
theorem B6066161 : Blo 1596997 6066161 := bstep (se 2 (by rfl) ⟨2274810, by rfl⟩ : syracuseStep 6066161 = 4549621) B4549621
theorem B2396147 : Blo 1596997 2396147 := bstep (se 1 (by rfl) ⟨1797110, by rfl⟩ : syracuseStep 2396147 = 3594221) B3594221
theorem B3837955 : Blo 1596997 3837955 := bstep (se 1 (by rfl) ⟨2878466, by rfl⟩ : syracuseStep 3837955 = 5756933) B5756933
theorem B2396177 : Blo 1596997 2396177 := bstep (se 2 (by rfl) ⟨898566, by rfl⟩ : syracuseStep 2396177 = 1797133) B1797133
theorem B2396195 : Blo 1596997 2396195 := bstep (se 1 (by rfl) ⟨1797146, by rfl⟩ : syracuseStep 2396195 = 3594293) B3594293
theorem B1798195 : Blo 1596997 1798195 := bstep (se 1 (by rfl) ⟨1348646, by rfl⟩ : syracuseStep 1798195 = 2697293) B2697293
theorem B1822771 : Blo 1596997 1822771 := bstep (se 1 (by rfl) ⟨1367078, by rfl⟩ : syracuseStep 1822771 = 2734157) B2734157
theorem B2396225 : Blo 1596997 2396225 := bstep (se 2 (by rfl) ⟨898584, by rfl⟩ : syracuseStep 2396225 = 1797169) B1797169
theorem B4550737 : Blo 1596997 4550737 := bstep (se 2 (by rfl) ⟨1706526, by rfl⟩ : syracuseStep 4550737 = 3413053) B3413053
theorem B2396243 : Blo 1596997 2396243 := bstep (se 1 (by rfl) ⟨1797182, by rfl⟩ : syracuseStep 2396243 = 3594365) B3594365
theorem B6475889 : Blo 1596997 6475889 := bstep (se 2 (by rfl) ⟨2428458, by rfl⟩ : syracuseStep 6475889 = 4856917) B4856917
theorem B2396273 : Blo 1596997 2396273 := bstep (se 2 (by rfl) ⟨898602, by rfl⟩ : syracuseStep 2396273 = 1797205) B1797205
theorem B5394545 : Blo 1596997 5394545 := bstep (se 2 (by rfl) ⟨2022954, by rfl⟩ : syracuseStep 5394545 = 4045909) B4045909
theorem B2396291 : Blo 1596997 2396291 := bstep (se 1 (by rfl) ⟨1797218, by rfl⟩ : syracuseStep 2396291 = 3594437) B3594437
theorem B2396321 : Blo 1596997 2396321 := bstep (se 2 (by rfl) ⟨898620, by rfl⟩ : syracuseStep 2396321 = 1797241) B1797241
theorem B6828209 : Blo 1596997 6828209 := bstep (se 2 (by rfl) ⟨2560578, by rfl⟩ : syracuseStep 6828209 = 5121157) B5121157
theorem B2396339 : Blo 1596997 2396339 := bstep (se 1 (by rfl) ⟨1797254, by rfl⟩ : syracuseStep 2396339 = 3594509) B3594509
theorem B1798339 : Blo 1596997 1798339 := bstep (se 1 (by rfl) ⟨1348754, by rfl⟩ : syracuseStep 1798339 = 2697509) B2697509
theorem B2396369 : Blo 1596997 2396369 := bstep (se 2 (by rfl) ⟨898638, by rfl⟩ : syracuseStep 2396369 = 1797277) B1797277
theorem B2396387 : Blo 1596997 2396387 := bstep (se 1 (by rfl) ⟨1797290, by rfl⟩ : syracuseStep 2396387 = 3594581) B3594581
theorem B18198755 : Blo 1596997 18198755 := bstep (se 1 (by rfl) ⟨13649066, by rfl⟩ : syracuseStep 18198755 = 27298133) B27298133
theorem B6828259 : Blo 1596997 6828259 := bstep (se 1 (by rfl) ⟨5121194, by rfl⟩ : syracuseStep 6828259 = 10242389) B10242389
theorem B4042993 : Blo 1596997 4042993 := bstep (se 2 (by rfl) ⟨1516122, by rfl⟩ : syracuseStep 4042993 = 3032245) B3032245
theorem B2879729 : Blo 1596997 2879729 := bstep (se 2 (by rfl) ⟨1079898, by rfl⟩ : syracuseStep 2879729 = 2159797) B2159797
theorem B4550897 : Blo 1596997 4550897 := bstep (se 2 (by rfl) ⟨1706586, by rfl⟩ : syracuseStep 4550897 = 3413173) B3413173
theorem B2396417 : Blo 1596997 2396417 := bstep (se 2 (by rfl) ⟨898656, by rfl⟩ : syracuseStep 2396417 = 1797313) B1797313
theorem B2396435 : Blo 1596997 2396435 := bstep (se 1 (by rfl) ⟨1797326, by rfl⟩ : syracuseStep 2396435 = 3594653) B3594653
theorem B10244387 : Blo 1596997 10244387 := bstep (se 1 (by rfl) ⟨7683290, by rfl⟩ : syracuseStep 10244387 = 15366581) B15366581
theorem B2396465 : Blo 1596997 2396465 := bstep (se 2 (by rfl) ⟨898674, by rfl⟩ : syracuseStep 2396465 = 1797349) B1797349
theorem B2396483 : Blo 1596997 2396483 := bstep (se 1 (by rfl) ⟨1797362, by rfl⟩ : syracuseStep 2396483 = 3594725) B3594725
theorem B1798483 : Blo 1596997 1798483 := bstep (se 1 (by rfl) ⟨1348862, by rfl⟩ : syracuseStep 1798483 = 2697725) B2697725
theorem B2396513 : Blo 1596997 2396513 := bstep (se 2 (by rfl) ⟨898692, by rfl⟩ : syracuseStep 2396513 = 1797385) B1797385
theorem B8089955 : Blo 1596997 8089955 := bstep (se 1 (by rfl) ⟨6067466, by rfl⟩ : syracuseStep 8089955 = 12134933) B12134933
theorem B4551011 : Blo 1596997 4551011 := bstep (se 1 (by rfl) ⟨3413258, by rfl⟩ : syracuseStep 4551011 = 6826517) B6826517
theorem B2396531 : Blo 1596997 2396531 := bstep (se 1 (by rfl) ⟨1797398, by rfl⟩ : syracuseStep 2396531 = 3594797) B3594797
theorem B2396561 : Blo 1596997 2396561 := bstep (se 2 (by rfl) ⟨898710, by rfl⟩ : syracuseStep 2396561 = 1797421) B1797421
theorem B2396579 : Blo 1596997 2396579 := bstep (se 1 (by rfl) ⟨1797434, by rfl⟩ : syracuseStep 2396579 = 3594869) B3594869
theorem B2396609 : Blo 1596997 2396609 := bstep (se 2 (by rfl) ⟨898728, by rfl⟩ : syracuseStep 2396609 = 1797457) B1797457
theorem B2396627 : Blo 1596997 2396627 := bstep (se 1 (by rfl) ⟨1797470, by rfl⟩ : syracuseStep 2396627 = 3594941) B3594941
theorem B1798627 : Blo 1596997 1798627 := bstep (se 1 (by rfl) ⟨1348970, by rfl⟩ : syracuseStep 1798627 = 2697941) B2697941
theorem B2396657 : Blo 1596997 2396657 := bstep (se 2 (by rfl) ⟨898746, by rfl⟩ : syracuseStep 2396657 = 1797493) B1797493
theorem B4043267 : Blo 1596997 4043267 := bstep (se 1 (by rfl) ⟨3032450, by rfl⟩ : syracuseStep 4043267 = 6064901) B6064901
theorem B2396675 : Blo 1596997 2396675 := bstep (se 1 (by rfl) ⟨1797506, by rfl⟩ : syracuseStep 2396675 = 3595013) B3595013
theorem B2396705 : Blo 1596997 2396705 := bstep (se 2 (by rfl) ⟨898764, by rfl⟩ : syracuseStep 2396705 = 1797529) B1797529
theorem B2560547 : Blo 1596997 2560547 := bstep (se 1 (by rfl) ⟨1920410, by rfl⟩ : syracuseStep 2560547 = 3840821) B3840821
theorem B2396723 : Blo 1596997 2396723 := bstep (se 1 (by rfl) ⟨1797542, by rfl⟩ : syracuseStep 2396723 = 3595085) B3595085
theorem B2396753 : Blo 1596997 2396753 := bstep (se 2 (by rfl) ⟨898782, by rfl⟩ : syracuseStep 2396753 = 1797565) B1797565
theorem B2396771 : Blo 1596997 2396771 := bstep (se 1 (by rfl) ⟨1797578, by rfl⟩ : syracuseStep 2396771 = 3595157) B3595157
theorem B1798771 : Blo 1596997 1798771 := bstep (se 1 (by rfl) ⟨1349078, by rfl⟩ : syracuseStep 1798771 = 2698157) B2698157
theorem B2396801 : Blo 1596997 2396801 := bstep (se 2 (by rfl) ⟨898800, by rfl⟩ : syracuseStep 2396801 = 1797601) B1797601
theorem B13652621 : Blo 1596997 13652621 := bstep (se 3 (by rfl) ⟨2559866, by rfl⟩ : syracuseStep 13652621 = 5119733) B5119733
theorem B5395085 : Blo 1596997 5395085 := bstep (se 3 (by rfl) ⟨1011578, by rfl⟩ : syracuseStep 5395085 = 2023157) B2023157
theorem B2396819 : Blo 1596997 2396819 := bstep (se 1 (by rfl) ⟨1797614, by rfl⟩ : syracuseStep 2396819 = 3595229) B3595229
theorem B2396849 : Blo 1596997 2396849 := bstep (se 2 (by rfl) ⟨898818, by rfl⟩ : syracuseStep 2396849 = 1797637) B1797637
theorem B4043459 : Blo 1596997 4043459 := bstep (se 1 (by rfl) ⟨3032594, by rfl⟩ : syracuseStep 4043459 = 6065189) B6065189
theorem B2396867 : Blo 1596997 2396867 := bstep (se 1 (by rfl) ⟨1797650, by rfl⟩ : syracuseStep 2396867 = 3595301) B3595301
theorem B5395139 : Blo 1596997 5395139 := bstep (se 1 (by rfl) ⟨4046354, by rfl⟩ : syracuseStep 5395139 = 8092709) B8092709
theorem B2396897 : Blo 1596997 2396897 := bstep (se 2 (by rfl) ⟨898836, by rfl⟩ : syracuseStep 2396897 = 1797673) B1797673
theorem B2396915 : Blo 1596997 2396915 := bstep (se 1 (by rfl) ⟨1797686, by rfl⟩ : syracuseStep 2396915 = 3595373) B3595373
theorem B13644557 : Blo 1596997 13644557 := bstep (se 3 (by rfl) ⟨2558354, by rfl⟩ : syracuseStep 13644557 = 5116709) B5116709
theorem B2396945 : Blo 1596997 2396945 := bstep (se 2 (by rfl) ⟨898854, by rfl⟩ : syracuseStep 2396945 = 1797709) B1797709
theorem B2396963 : Blo 1596997 2396963 := bstep (se 1 (by rfl) ⟨1797722, by rfl⟩ : syracuseStep 2396963 = 3595445) B3595445
theorem B2396993 : Blo 1596997 2396993 := bstep (se 2 (by rfl) ⟨898872, by rfl⟩ : syracuseStep 2396993 = 1797745) B1797745
theorem B2560835 : Blo 1596997 2560835 := bstep (se 1 (by rfl) ⟨1920626, by rfl⟩ : syracuseStep 2560835 = 3841253) B3841253
theorem B2397011 : Blo 1596997 2397011 := bstep (se 1 (by rfl) ⟨1797758, by rfl⟩ : syracuseStep 2397011 = 3595517) B3595517
theorem B2274161 : Blo 1596997 2274161 := bstep (se 2 (by rfl) ⟨852810, by rfl⟩ : syracuseStep 2274161 = 1705621) B1705621
theorem B2397041 : Blo 1596997 2397041 := bstep (se 2 (by rfl) ⟨898890, by rfl⟩ : syracuseStep 2397041 = 1797781) B1797781
theorem B2397059 : Blo 1596997 2397059 := bstep (se 1 (by rfl) ⟨1797794, by rfl⟩ : syracuseStep 2397059 = 3595589) B3595589
theorem B2732945 : Blo 1596997 2732945 := bstep (se 2 (by rfl) ⟨1024854, by rfl⟩ : syracuseStep 2732945 = 2049709) B2049709
theorem B2397089 : Blo 1596997 2397089 := bstep (se 2 (by rfl) ⟨898908, by rfl⟩ : syracuseStep 2397089 = 1797817) B1797817
theorem B2397107 : Blo 1596997 2397107 := bstep (se 1 (by rfl) ⟨1797830, by rfl⟩ : syracuseStep 2397107 = 3595661) B3595661
theorem B2397137 : Blo 1596997 2397137 := bstep (se 2 (by rfl) ⟨898926, by rfl⟩ : syracuseStep 2397137 = 1797853) B1797853
theorem B5395409 : Blo 1596997 5395409 := bstep (se 2 (by rfl) ⟨2023278, by rfl⟩ : syracuseStep 5395409 = 4046557) B4046557
theorem B2274275 : Blo 1596997 2274275 := bstep (se 1 (by rfl) ⟨1705706, by rfl⟩ : syracuseStep 2274275 = 3411413) B3411413
theorem B2397155 : Blo 1596997 2397155 := bstep (se 1 (by rfl) ⟨1797866, by rfl⟩ : syracuseStep 2397155 = 3595733) B3595733
theorem B2397185 : Blo 1596997 2397185 := bstep (se 2 (by rfl) ⟨898944, by rfl⟩ : syracuseStep 2397185 = 1797889) B1797889
theorem B2397203 : Blo 1596997 2397203 := bstep (se 1 (by rfl) ⟨1797902, by rfl⟩ : syracuseStep 2397203 = 3595805) B3595805
theorem B2397233 : Blo 1596997 2397233 := bstep (se 2 (by rfl) ⟨898962, by rfl⟩ : syracuseStep 2397233 = 1797925) B1797925
theorem B2274355 : Blo 1596997 2274355 := bstep (se 1 (by rfl) ⟨1705766, by rfl⟩ : syracuseStep 2274355 = 3411533) B3411533
theorem B2397251 : Blo 1596997 2397251 := bstep (se 1 (by rfl) ⟨1797938, by rfl⟩ : syracuseStep 2397251 = 3595877) B3595877
theorem B2397281 : Blo 1596997 2397281 := bstep (se 2 (by rfl) ⟨898980, by rfl⟩ : syracuseStep 2397281 = 1797961) B1797961
theorem B2397299 : Blo 1596997 2397299 := bstep (se 1 (by rfl) ⟨1797974, by rfl⟩ : syracuseStep 2397299 = 3595949) B3595949
theorem B8090765 : Blo 1596997 8090765 := bstep (se 3 (by rfl) ⟨1517018, by rfl⟩ : syracuseStep 8090765 = 3034037) B3034037
theorem B2397329 : Blo 1596997 2397329 := bstep (se 2 (by rfl) ⟨898998, by rfl⟩ : syracuseStep 2397329 = 1797997) B1797997
theorem B2397347 : Blo 1596997 2397347 := bstep (se 1 (by rfl) ⟨1798010, by rfl⟩ : syracuseStep 2397347 = 3596021) B3596021
theorem B3593393 : Blo 1596997 3593393 := bstep (se 2 (by rfl) ⟨1347522, by rfl⟩ : syracuseStep 3593393 = 2695045) B2695045
theorem B2397377 : Blo 1596997 2397377 := bstep (se 2 (by rfl) ⟨899016, by rfl⟩ : syracuseStep 2397377 = 1798033) B1798033
theorem B3593411 : Blo 1596997 3593411 := bstep (se 1 (by rfl) ⟨2695058, by rfl⟩ : syracuseStep 3593411 = 5390117) B5390117
theorem B3839185 : Blo 1596997 3839185 := bstep (se 2 (by rfl) ⟨1439694, by rfl⟩ : syracuseStep 3839185 = 2879389) B2879389
theorem B2397395 : Blo 1596997 2397395 := bstep (se 1 (by rfl) ⟨1798046, by rfl⟩ : syracuseStep 2397395 = 3596093) B3596093
theorem B2733281 : Blo 1596997 2733281 := bstep (se 2 (by rfl) ⟨1024980, by rfl⟩ : syracuseStep 2733281 = 2049961) B2049961
theorem B2397425 : Blo 1596997 2397425 := bstep (se 2 (by rfl) ⟨899034, by rfl⟩ : syracuseStep 2397425 = 1798069) B1798069
theorem B2397443 : Blo 1596997 2397443 := bstep (se 1 (by rfl) ⟨1798082, by rfl⟩ : syracuseStep 2397443 = 3596165) B3596165
theorem B2397473 : Blo 1596997 2397473 := bstep (se 2 (by rfl) ⟨899052, by rfl⟩ : syracuseStep 2397473 = 1798105) B1798105
theorem B2397491 : Blo 1596997 2397491 := bstep (se 1 (by rfl) ⟨1798118, by rfl⟩ : syracuseStep 2397491 = 3596237) B3596237
theorem B4552013 : Blo 1596997 4552013 := bstep (se 3 (by rfl) ⟨853502, by rfl⟩ : syracuseStep 4552013 = 1707005) B1707005
theorem B2397521 : Blo 1596997 2397521 := bstep (se 2 (by rfl) ⟨899070, by rfl⟩ : syracuseStep 2397521 = 1798141) B1798141
theorem B2397539 : Blo 1596997 2397539 := bstep (se 1 (by rfl) ⟨1798154, by rfl⟩ : syracuseStep 2397539 = 3596309) B3596309
theorem B2397569 : Blo 1596997 2397569 := bstep (se 2 (by rfl) ⟨899088, by rfl⟩ : syracuseStep 2397569 = 1798177) B1798177
theorem B2397587 : Blo 1596997 2397587 := bstep (se 1 (by rfl) ⟨1798190, by rfl⟩ : syracuseStep 2397587 = 3596381) B3596381
theorem B6067619 : Blo 1596997 6067619 := bstep (se 1 (by rfl) ⟨4550714, by rfl⟩ : syracuseStep 6067619 = 9101429) B9101429
theorem B2397617 : Blo 1596997 2397617 := bstep (se 2 (by rfl) ⟨899106, by rfl⟩ : syracuseStep 2397617 = 1798213) B1798213
theorem B2397635 : Blo 1596997 2397635 := bstep (se 1 (by rfl) ⟨1798226, by rfl⟩ : syracuseStep 2397635 = 3596453) B3596453
theorem B8639941 : Blo 1596997 8639941 := bstep (se 4 (by rfl) ⟨809994, by rfl⟩ : syracuseStep 8639941 = 1619989) B1619989
theorem B3593681 : Blo 1596997 3593681 := bstep (se 2 (by rfl) ⟨1347630, by rfl⟩ : syracuseStep 3593681 = 2695261) B2695261
theorem B2397665 : Blo 1596997 2397665 := bstep (se 2 (by rfl) ⟨899124, by rfl⟩ : syracuseStep 2397665 = 1798249) B1798249
theorem B3593699 : Blo 1596997 3593699 := bstep (se 1 (by rfl) ⟨2695274, by rfl⟩ : syracuseStep 3593699 = 5390549) B5390549
theorem B2733553 : Blo 1596997 2733553 := bstep (se 2 (by rfl) ⟨1025082, by rfl⟩ : syracuseStep 2733553 = 2050165) B2050165
theorem B5395949 : Blo 1596997 5395949 := bstep (se 3 (by rfl) ⟨1011740, by rfl⟩ : syracuseStep 5395949 = 2023481) B2023481
theorem B2397683 : Blo 1596997 2397683 := bstep (se 1 (by rfl) ⟨1798262, by rfl⟩ : syracuseStep 2397683 = 3596525) B3596525
theorem B4552195 : Blo 1596997 4552195 := bstep (se 1 (by rfl) ⟨3414146, by rfl⟩ : syracuseStep 4552195 = 6828293) B6828293
theorem B2397713 : Blo 1596997 2397713 := bstep (se 2 (by rfl) ⟨899142, by rfl⟩ : syracuseStep 2397713 = 1798285) B1798285
theorem B2397731 : Blo 1596997 2397731 := bstep (se 1 (by rfl) ⟨1798298, by rfl⟩ : syracuseStep 2397731 = 3596597) B3596597
theorem B9229859 : Blo 1596997 9229859 := bstep (se 1 (by rfl) ⟨6922394, by rfl⟩ : syracuseStep 9229859 = 13844789) B13844789
theorem B5396003 : Blo 1596997 5396003 := bstep (se 1 (by rfl) ⟨4047002, by rfl⟩ : syracuseStep 5396003 = 8094005) B8094005
theorem B2397761 : Blo 1596997 2397761 := bstep (se 2 (by rfl) ⟨899160, by rfl⟩ : syracuseStep 2397761 = 1798321) B1798321
theorem B15357509 : Blo 1596997 15357509 := bstep (se 4 (by rfl) ⟨1439766, by rfl⟩ : syracuseStep 15357509 = 2879533) B2879533
theorem B2397779 : Blo 1596997 2397779 := bstep (se 1 (by rfl) ⟨1798334, by rfl⟩ : syracuseStep 2397779 = 3596669) B3596669
theorem B2274913 : Blo 1596997 2274913 := bstep (se 2 (by rfl) ⟨853092, by rfl⟩ : syracuseStep 2274913 = 1706185) B1706185
theorem B4044401 : Blo 1596997 4044401 := bstep (se 2 (by rfl) ⟨1516650, by rfl⟩ : syracuseStep 4044401 = 3033301) B3033301
theorem B2397809 : Blo 1596997 2397809 := bstep (se 2 (by rfl) ⟨899178, by rfl⟩ : syracuseStep 2397809 = 1798357) B1798357
theorem B2397827 : Blo 1596997 2397827 := bstep (se 1 (by rfl) ⟨1798370, by rfl⟩ : syracuseStep 2397827 = 3596741) B3596741
theorem B2397857 : Blo 1596997 2397857 := bstep (se 2 (by rfl) ⟨899196, by rfl⟩ : syracuseStep 2397857 = 1798393) B1798393
theorem B4044451 : Blo 1596997 4044451 := bstep (se 1 (by rfl) ⟨3033338, by rfl⟩ : syracuseStep 4044451 = 6066677) B6066677
theorem B4552355 : Blo 1596997 4552355 := bstep (se 1 (by rfl) ⟨3414266, by rfl⟩ : syracuseStep 4552355 = 6828533) B6828533
theorem B2397875 : Blo 1596997 2397875 := bstep (se 1 (by rfl) ⟨1798406, by rfl⟩ : syracuseStep 2397875 = 3596813) B3596813
theorem B2397905 : Blo 1596997 2397905 := bstep (se 2 (by rfl) ⟨899214, by rfl⟩ : syracuseStep 2397905 = 1798429) B1798429
theorem B2397923 : Blo 1596997 2397923 := bstep (se 1 (by rfl) ⟨1798442, by rfl⟩ : syracuseStep 2397923 = 3596885) B3596885
theorem B3593969 : Blo 1596997 3593969 := bstep (se 2 (by rfl) ⟨1347738, by rfl⟩ : syracuseStep 3593969 = 2695477) B2695477
theorem B2397953 : Blo 1596997 2397953 := bstep (se 2 (by rfl) ⟨899232, by rfl⟩ : syracuseStep 2397953 = 1798465) B1798465
theorem B3593987 : Blo 1596997 3593987 := bstep (se 1 (by rfl) ⟨2695490, by rfl⟩ : syracuseStep 3593987 = 5390981) B5390981
theorem B9099013 : Blo 1596997 9099013 := bstep (se 4 (by rfl) ⟨853032, by rfl⟩ : syracuseStep 9099013 = 1706065) B1706065
theorem B2397971 : Blo 1596997 2397971 := bstep (se 1 (by rfl) ⟨1798478, by rfl⟩ : syracuseStep 2397971 = 3596957) B3596957
theorem B4044593 : Blo 1596997 4044593 := bstep (se 2 (by rfl) ⟨1516722, by rfl⟩ : syracuseStep 4044593 = 3033445) B3033445
theorem B2398001 : Blo 1596997 2398001 := bstep (se 2 (by rfl) ⟨899250, by rfl⟩ : syracuseStep 2398001 = 1798501) B1798501
theorem B5396273 : Blo 1596997 5396273 := bstep (se 2 (by rfl) ⟨2023602, by rfl⟩ : syracuseStep 5396273 = 4047205) B4047205
theorem B23344949 : Blo 1596997 23344949 := bstep (se 5 (by rfl) ⟨1094294, by rfl⟩ : syracuseStep 23344949 = 2188589) B2188589
theorem B2398019 : Blo 1596997 2398019 := bstep (se 1 (by rfl) ⟨1798514, by rfl⟩ : syracuseStep 2398019 = 3597029) B3597029
theorem B12957509 : Blo 1596997 12957509 := bstep (se 4 (by rfl) ⟨1214766, by rfl⟩ : syracuseStep 12957509 = 2429533) B2429533
theorem B2021203 : Blo 1596997 2021203 := bstep (se 1 (by rfl) ⟨1515902, by rfl⟩ : syracuseStep 2021203 = 3031805) B3031805
theorem B2398049 : Blo 1596997 2398049 := bstep (se 2 (by rfl) ⟨899268, by rfl⟩ : syracuseStep 2398049 = 1798537) B1798537
theorem B2881379 : Blo 1596997 2881379 := bstep (se 1 (by rfl) ⟨2161034, by rfl⟩ : syracuseStep 2881379 = 4322069) B4322069
theorem B3413873 : Blo 1596997 3413873 := bstep (se 2 (by rfl) ⟨1280202, by rfl⟩ : syracuseStep 3413873 = 2560405) B2560405
theorem B2398067 : Blo 1596997 2398067 := bstep (se 1 (by rfl) ⟨1798550, by rfl⟩ : syracuseStep 2398067 = 3597101) B3597101
theorem B22763405 : Blo 1596997 22763405 := bstep (se 3 (by rfl) ⟨4268138, by rfl⟩ : syracuseStep 22763405 = 8536277) B8536277
theorem B2398097 : Blo 1596997 2398097 := bstep (se 2 (by rfl) ⟨899286, by rfl⟩ : syracuseStep 2398097 = 1798573) B1798573
theorem B2398115 : Blo 1596997 2398115 := bstep (se 1 (by rfl) ⟨1798586, by rfl⟩ : syracuseStep 2398115 = 3597173) B3597173
theorem B2398145 : Blo 1596997 2398145 := bstep (se 2 (by rfl) ⟨899304, by rfl⟩ : syracuseStep 2398145 = 1798609) B1798609
theorem B2398163 : Blo 1596997 2398163 := bstep (se 1 (by rfl) ⟨1798622, by rfl⟩ : syracuseStep 2398163 = 3597245) B3597245
theorem B2398193 : Blo 1596997 2398193 := bstep (se 2 (by rfl) ⟨899322, by rfl⟩ : syracuseStep 2398193 = 1798645) B1798645
theorem B2398211 : Blo 1596997 2398211 := bstep (se 1 (by rfl) ⟨1798658, by rfl⟩ : syracuseStep 2398211 = 3597317) B3597317
theorem B3594257 : Blo 1596997 3594257 := bstep (se 2 (by rfl) ⟨1347846, by rfl⟩ : syracuseStep 3594257 = 2695693) B2695693
theorem B2398241 : Blo 1596997 2398241 := bstep (se 2 (by rfl) ⟨899340, by rfl⟩ : syracuseStep 2398241 = 1798681) B1798681
theorem B3594275 : Blo 1596997 3594275 := bstep (se 1 (by rfl) ⟨2695706, by rfl⟩ : syracuseStep 3594275 = 5391413) B5391413
theorem B2398259 : Blo 1596997 2398259 := bstep (se 1 (by rfl) ⟨1798694, by rfl⟩ : syracuseStep 2398259 = 3597389) B3597389
theorem B2398289 : Blo 1596997 2398289 := bstep (se 2 (by rfl) ⟨899358, by rfl⟩ : syracuseStep 2398289 = 1798717) B1798717
theorem B4610147 : Blo 1596997 4610147 := bstep (se 1 (by rfl) ⟨3457610, by rfl⟩ : syracuseStep 4610147 = 6915221) B6915221
theorem B2398307 : Blo 1596997 2398307 := bstep (se 1 (by rfl) ⟨1798730, by rfl⟩ : syracuseStep 2398307 = 3597461) B3597461
theorem B49207409 : Blo 1596997 49207409 := bstep (se 2 (by rfl) ⟨18452778, by rfl⟩ : syracuseStep 49207409 = 36905557) B36905557
theorem B2398337 : Blo 1596997 2398337 := bstep (se 2 (by rfl) ⟨899376, by rfl⟩ : syracuseStep 2398337 = 1798753) B1798753
theorem B2398355 : Blo 1596997 2398355 := bstep (se 1 (by rfl) ⟨1798766, by rfl⟩ : syracuseStep 2398355 = 3597533) B3597533
theorem B2431139 : Blo 1596997 2431139 := bstep (se 1 (by rfl) ⟨1823354, by rfl⟩ : syracuseStep 2431139 = 3646709) B3646709
theorem B2398385 : Blo 1596997 2398385 := bstep (se 2 (by rfl) ⟨899394, by rfl⟩ : syracuseStep 2398385 = 1798789) B1798789
theorem B17283253 : Blo 1596997 17283253 := bstep (se 5 (by rfl) ⟨810152, by rfl⟩ : syracuseStep 17283253 = 1620305) B1620305
theorem B2398403 : Blo 1596997 2398403 := bstep (se 1 (by rfl) ⟨1798802, by rfl⟩ : syracuseStep 2398403 = 3597605) B3597605
theorem B2398433 : Blo 1596997 2398433 := bstep (se 2 (by rfl) ⟨899412, by rfl⟩ : syracuseStep 2398433 = 1798825) B1798825
theorem B4610285 : Blo 1596997 4610285 := bstep (se 3 (by rfl) ⟨864428, by rfl⟩ : syracuseStep 4610285 = 1728857) B1728857
theorem B2398451 : Blo 1596997 2398451 := bstep (se 1 (by rfl) ⟨1798838, by rfl⟩ : syracuseStep 2398451 = 3597677) B3597677
theorem B2398481 : Blo 1596997 2398481 := bstep (se 2 (by rfl) ⟨899430, by rfl⟩ : syracuseStep 2398481 = 1798861) B1798861
theorem B2275619 : Blo 1596997 2275619 := bstep (se 1 (by rfl) ⟨1706714, by rfl⟩ : syracuseStep 2275619 = 3413429) B3413429
theorem B3594545 : Blo 1596997 3594545 := bstep (se 2 (by rfl) ⟨1347954, by rfl⟩ : syracuseStep 3594545 = 2695909) B2695909
theorem B2021699 : Blo 1596997 2021699 := bstep (se 1 (by rfl) ⟨1516274, by rfl⟩ : syracuseStep 2021699 = 3032549) B3032549
theorem B3594563 : Blo 1596997 3594563 := bstep (se 1 (by rfl) ⟨2695922, by rfl⟩ : syracuseStep 3594563 = 5391845) B5391845
theorem B12138821 : Blo 1596997 12138821 := bstep (se 4 (by rfl) ⟨1138014, by rfl⟩ : syracuseStep 12138821 = 2276029) B2276029
theorem B3414403 : Blo 1596997 3414403 := bstep (se 1 (by rfl) ⟨2560802, by rfl⟩ : syracuseStep 3414403 = 5121605) B5121605
theorem B6068621 : Blo 1596997 6068621 := bstep (se 3 (by rfl) ⟨1137866, by rfl⟩ : syracuseStep 6068621 = 2275733) B2275733
theorem B39950819 : Blo 1596997 39950819 := bstep (se 1 (by rfl) ⟨29963114, by rfl⟩ : syracuseStep 39950819 = 59926229) B59926229
theorem B3594833 : Blo 1596997 3594833 := bstep (se 2 (by rfl) ⟨1348062, by rfl⟩ : syracuseStep 3594833 = 2696125) B2696125
theorem B3594851 : Blo 1596997 3594851 := bstep (se 1 (by rfl) ⟨2696138, by rfl⟩ : syracuseStep 3594851 = 5392277) B5392277
theorem B40966883 : Blo 1596997 40966883 := bstep (se 1 (by rfl) ⟨30725162, by rfl⟩ : syracuseStep 40966883 = 61450325) B61450325
theorem B4045585 : Blo 1596997 4045585 := bstep (se 2 (by rfl) ⟨1517094, by rfl⟩ : syracuseStep 4045585 = 3034189) B3034189
theorem B2595619 : Blo 1596997 2595619 := bstep (se 1 (by rfl) ⟨1946714, by rfl⟩ : syracuseStep 2595619 = 3893429) B3893429
theorem B3595121 : Blo 1596997 3595121 := bstep (se 2 (by rfl) ⟨1348170, by rfl⟩ : syracuseStep 3595121 = 2696341) B2696341
theorem B3595139 : Blo 1596997 3595139 := bstep (se 1 (by rfl) ⟨2696354, by rfl⟩ : syracuseStep 3595139 = 5392709) B5392709
theorem B2276257 : Blo 1596997 2276257 := bstep (se 2 (by rfl) ⟨853596, by rfl⟩ : syracuseStep 2276257 = 1707193) B1707193
theorem B30702563 : Blo 1596997 30702563 := bstep (se 1 (by rfl) ⟨23026922, by rfl⟩ : syracuseStep 30702563 = 46053845) B46053845
theorem B2595827 : Blo 1596997 2595827 := bstep (se 1 (by rfl) ⟨1946870, by rfl⟩ : syracuseStep 2595827 = 3893741) B3893741
theorem B2022403 : Blo 1596997 2022403 := bstep (se 1 (by rfl) ⟨1516802, by rfl⟩ : syracuseStep 2022403 = 3033605) B3033605
theorem B2276371 : Blo 1596997 2276371 := bstep (se 1 (by rfl) ⟨1707278, by rfl⟩ : syracuseStep 2276371 = 3414557) B3414557
theorem B4045859 : Blo 1596997 4045859 := bstep (se 1 (by rfl) ⟨3034394, by rfl⟩ : syracuseStep 4045859 = 6068789) B6068789
theorem B2022499 : Blo 1596997 2022499 := bstep (se 1 (by rfl) ⟨1516874, by rfl⟩ : syracuseStep 2022499 = 3033749) B3033749
theorem B3595409 : Blo 1596997 3595409 := bstep (se 2 (by rfl) ⟨1348278, by rfl⟩ : syracuseStep 3595409 = 2696557) B2696557
theorem B3595427 : Blo 1596997 3595427 := bstep (se 1 (by rfl) ⟨2696570, by rfl⟩ : syracuseStep 3595427 = 5393141) B5393141
theorem B3693745 : Blo 1596997 3693745 := bstep (se 2 (by rfl) ⟨1385154, by rfl⟩ : syracuseStep 3693745 = 2770309) B2770309
theorem B4046051 : Blo 1596997 4046051 := bstep (se 1 (by rfl) ⟨3034538, by rfl⟩ : syracuseStep 4046051 = 6069077) B6069077
theorem B8314211 : Blo 1596997 8314211 := bstep (se 1 (by rfl) ⟨6235658, by rfl⟩ : syracuseStep 8314211 = 12471317) B12471317
theorem B2596195 : Blo 1596997 2596195 := bstep (se 1 (by rfl) ⟨1947146, by rfl⟩ : syracuseStep 2596195 = 3894293) B3894293
theorem B4922797 : Blo 1596997 4922797 := bstep (se 3 (by rfl) ⟨923024, by rfl⟩ : syracuseStep 4922797 = 1846049) B1846049
theorem B3595697 : Blo 1596997 3595697 := bstep (se 2 (by rfl) ⟨1348386, by rfl⟩ : syracuseStep 3595697 = 2696773) B2696773
theorem B3595715 : Blo 1596997 3595715 := bstep (se 1 (by rfl) ⟨2696786, by rfl⟩ : syracuseStep 3595715 = 5393573) B5393573
theorem B7781923 : Blo 1596997 7781923 := bstep (se 1 (by rfl) ⟨5836442, by rfl⟩ : syracuseStep 7781923 = 11672885) B11672885
theorem B5389901 : Blo 1596997 5389901 := bstep (se 3 (by rfl) ⟨1010606, by rfl⟩ : syracuseStep 5389901 = 2021213) B2021213
theorem B1597011 : Blo 1596997 1597011 := bstep (se 1 (by rfl) ⟨1197758, by rfl⟩ : syracuseStep 1597011 = 2395517) B2395517
theorem B2022995 : Blo 1596997 2022995 := bstep (se 1 (by rfl) ⟨1517246, by rfl⟩ : syracuseStep 2022995 = 3034493) B3034493
theorem B1597027 : Blo 1596997 1597027 := bstep (se 1 (by rfl) ⟨1197770, by rfl⟩ : syracuseStep 1597027 = 2395541) B2395541
theorem B5758577 : Blo 1596997 5758577 := bstep (se 2 (by rfl) ⟨2159466, by rfl⟩ : syracuseStep 5758577 = 4318933) B4318933
theorem B1597043 : Blo 1596997 1597043 := bstep (se 1 (by rfl) ⟨1197782, by rfl⟩ : syracuseStep 1597043 = 2395565) B2395565
theorem B5389955 : Blo 1596997 5389955 := bstep (se 1 (by rfl) ⟨4042466, by rfl⟩ : syracuseStep 5389955 = 8084933) B8084933
theorem B1597059 : Blo 1596997 1597059 := bstep (se 1 (by rfl) ⟨1197794, by rfl⟩ : syracuseStep 1597059 = 2395589) B2395589
theorem B1597075 : Blo 1596997 1597075 := bstep (se 1 (by rfl) ⟨1197806, by rfl⟩ : syracuseStep 1597075 = 2395613) B2395613
theorem B1597091 : Blo 1596997 1597091 := bstep (se 1 (by rfl) ⟨1197818, by rfl⟩ : syracuseStep 1597091 = 2395637) B2395637
theorem B1597107 : Blo 1596997 1597107 := bstep (se 1 (by rfl) ⟨1197830, by rfl⟩ : syracuseStep 1597107 = 2395661) B2395661
theorem B18456245 : Blo 1596997 18456245 := bstep (se 5 (by rfl) ⟨865136, by rfl⟩ : syracuseStep 18456245 = 1730273) B1730273
theorem B1597123 : Blo 1596997 1597123 := bstep (se 1 (by rfl) ⟨1197842, by rfl⟩ : syracuseStep 1597123 = 2395685) B2395685
theorem B9100997 : Blo 1596997 9100997 := bstep (se 4 (by rfl) ⟨853218, by rfl⟩ : syracuseStep 9100997 = 1706437) B1706437
theorem B3595985 : Blo 1596997 3595985 := bstep (se 2 (by rfl) ⟨1348494, by rfl⟩ : syracuseStep 3595985 = 2696989) B2696989
theorem B1597139 : Blo 1596997 1597139 := bstep (se 1 (by rfl) ⟨1197854, by rfl⟩ : syracuseStep 1597139 = 2395709) B2395709
theorem B1597155 : Blo 1596997 1597155 := bstep (se 1 (by rfl) ⟨1197866, by rfl⟩ : syracuseStep 1597155 = 2395733) B2395733
theorem B3596003 : Blo 1596997 3596003 := bstep (se 1 (by rfl) ⟨2697002, by rfl⟩ : syracuseStep 3596003 = 5394005) B5394005
theorem B1597171 : Blo 1596997 1597171 := bstep (se 1 (by rfl) ⟨1197878, by rfl⟩ : syracuseStep 1597171 = 2395757) B2395757
theorem B1597187 : Blo 1596997 1597187 := bstep (se 1 (by rfl) ⟨1197890, by rfl⟩ : syracuseStep 1597187 = 2395781) B2395781
theorem B1597203 : Blo 1596997 1597203 := bstep (se 1 (by rfl) ⟨1197902, by rfl⟩ : syracuseStep 1597203 = 2395805) B2395805
theorem B1597219 : Blo 1596997 1597219 := bstep (se 1 (by rfl) ⟨1197914, by rfl⟩ : syracuseStep 1597219 = 2395829) B2395829
theorem B1597235 : Blo 1596997 1597235 := bstep (se 1 (by rfl) ⟨1197926, by rfl⟩ : syracuseStep 1597235 = 2395853) B2395853
theorem B1597251 : Blo 1596997 1597251 := bstep (se 1 (by rfl) ⟨1197938, by rfl⟩ : syracuseStep 1597251 = 2395877) B2395877
theorem B1597267 : Blo 1596997 1597267 := bstep (se 1 (by rfl) ⟨1197950, by rfl⟩ : syracuseStep 1597267 = 2395901) B2395901
theorem B1597283 : Blo 1596997 1597283 := bstep (se 1 (by rfl) ⟨1197962, by rfl⟩ : syracuseStep 1597283 = 2395925) B2395925
theorem B2695025 : Blo 1596997 2695025 := bstep (se 2 (by rfl) ⟨1010634, by rfl⟩ : syracuseStep 2695025 = 2021269) B2021269
theorem B1597299 : Blo 1596997 1597299 := bstep (se 1 (by rfl) ⟨1197974, by rfl⟩ : syracuseStep 1597299 = 2395949) B2395949
theorem B1597315 : Blo 1596997 1597315 := bstep (se 1 (by rfl) ⟨1197986, by rfl⟩ : syracuseStep 1597315 = 2395973) B2395973
theorem B5390225 : Blo 1596997 5390225 := bstep (se 2 (by rfl) ⟨2021334, by rfl⟩ : syracuseStep 5390225 = 4042669) B4042669
theorem B1597331 : Blo 1596997 1597331 := bstep (se 1 (by rfl) ⟨1197998, by rfl⟩ : syracuseStep 1597331 = 2395997) B2395997
theorem B1597347 : Blo 1596997 1597347 := bstep (se 1 (by rfl) ⟨1198010, by rfl⟩ : syracuseStep 1597347 = 2396021) B2396021
theorem B1597363 : Blo 1596997 1597363 := bstep (se 1 (by rfl) ⟨1198022, by rfl⟩ : syracuseStep 1597363 = 2396045) B2396045
theorem B1597379 : Blo 1596997 1597379 := bstep (se 1 (by rfl) ⟨1198034, by rfl⟩ : syracuseStep 1597379 = 2396069) B2396069
theorem B6823885 : Blo 1596997 6823885 := bstep (se 3 (by rfl) ⟨1279478, by rfl⟩ : syracuseStep 6823885 = 2558957) B2558957
theorem B1597395 : Blo 1596997 1597395 := bstep (se 1 (by rfl) ⟨1198046, by rfl⟩ : syracuseStep 1597395 = 2396093) B2396093
theorem B1597411 : Blo 1596997 1597411 := bstep (se 1 (by rfl) ⟨1198058, by rfl⟩ : syracuseStep 1597411 = 2396117) B2396117
theorem B2695153 : Blo 1596997 2695153 := bstep (se 2 (by rfl) ⟨1010682, by rfl⟩ : syracuseStep 2695153 = 2021365) B2021365
theorem B3596273 : Blo 1596997 3596273 := bstep (se 2 (by rfl) ⟨1348602, by rfl⟩ : syracuseStep 3596273 = 2697205) B2697205
theorem B1597427 : Blo 1596997 1597427 := bstep (se 1 (by rfl) ⟨1198070, by rfl⟩ : syracuseStep 1597427 = 2396141) B2396141
theorem B8093681 : Blo 1596997 8093681 := bstep (se 2 (by rfl) ⟨3035130, by rfl⟩ : syracuseStep 8093681 = 6070261) B6070261
theorem B1597451 : Blo 1596997 1597451 := bstep (se 1 (by rfl) ⟨1198088, by rfl⟩ : syracuseStep 1597451 = 2396177) B2396177
theorem B1597463 : Blo 1596997 1597463 := bstep (se 1 (by rfl) ⟨1198097, by rfl⟩ : syracuseStep 1597463 = 2396195) B2396195
theorem B1597483 : Blo 1596997 1597483 := bstep (se 1 (by rfl) ⟨1198112, by rfl⟩ : syracuseStep 1597483 = 2396225) B2396225
theorem B5390387 : Blo 1596997 5390387 := bstep (se 1 (by rfl) ⟨4042790, by rfl⟩ : syracuseStep 5390387 = 8085581) B8085581
theorem B1597495 : Blo 1596997 1597495 := bstep (se 1 (by rfl) ⟨1198121, by rfl⟩ : syracuseStep 1597495 = 2396243) B2396243
theorem B4317259 : Blo 1596997 4317259 := bstep (se 1 (by rfl) ⟨3237944, by rfl⟩ : syracuseStep 4317259 = 6475889) B6475889
theorem B1597515 : Blo 1596997 1597515 := bstep (se 1 (by rfl) ⟨1198136, by rfl⟩ : syracuseStep 1597515 = 2396273) B2396273
theorem B3596363 : Blo 1596997 3596363 := bstep (se 1 (by rfl) ⟨2697272, by rfl⟩ : syracuseStep 3596363 = 5394545) B5394545
theorem B1597527 : Blo 1596997 1597527 := bstep (se 1 (by rfl) ⟨1198145, by rfl⟩ : syracuseStep 1597527 = 2396291) B2396291
theorem B13647973 : Blo 1596997 13647973 := bstep (se 4 (by rfl) ⟨1279497, by rfl⟩ : syracuseStep 13647973 = 2558995) B2558995
theorem B1597547 : Blo 1596997 1597547 := bstep (se 1 (by rfl) ⟨1198160, by rfl⟩ : syracuseStep 1597547 = 2396321) B2396321
theorem B1597559 : Blo 1596997 1597559 := bstep (se 1 (by rfl) ⟨1198169, by rfl⟩ : syracuseStep 1597559 = 2396339) B2396339
theorem B3596417 : Blo 1596997 3596417 := bstep (se 2 (by rfl) ⟨1348656, by rfl⟩ : syracuseStep 3596417 = 2697313) B2697313
theorem B1597579 : Blo 1596997 1597579 := bstep (se 1 (by rfl) ⟨1198184, by rfl⟩ : syracuseStep 1597579 = 2396369) B2396369
theorem B1597591 : Blo 1596997 1597591 := bstep (se 1 (by rfl) ⟨1198193, by rfl⟩ : syracuseStep 1597591 = 2396387) B2396387
theorem B12132503 : Blo 1596997 12132503 := bstep (se 1 (by rfl) ⟨9099377, by rfl⟩ : syracuseStep 12132503 = 18198755) B18198755
theorem B1597611 : Blo 1596997 1597611 := bstep (se 1 (by rfl) ⟨1198208, by rfl⟩ : syracuseStep 1597611 = 2396417) B2396417
theorem B24592565 : Blo 1596997 24592565 := bstep (se 5 (by rfl) ⟨1152776, by rfl⟩ : syracuseStep 24592565 = 2305553) B2305553
theorem B1597623 : Blo 1596997 1597623 := bstep (se 1 (by rfl) ⟨1198217, by rfl⟩ : syracuseStep 1597623 = 2396435) B2396435
theorem B1597643 : Blo 1596997 1597643 := bstep (se 1 (by rfl) ⟨1198232, by rfl⟩ : syracuseStep 1597643 = 2396465) B2396465
theorem B1597655 : Blo 1596997 1597655 := bstep (se 1 (by rfl) ⟨1198241, by rfl⟩ : syracuseStep 1597655 = 2396483) B2396483
theorem B1597675 : Blo 1596997 1597675 := bstep (se 1 (by rfl) ⟨1198256, by rfl⟩ : syracuseStep 1597675 = 2396513) B2396513
theorem B23044337 : Blo 1596997 23044337 := bstep (se 2 (by rfl) ⟨8641626, by rfl⟩ : syracuseStep 23044337 = 17283253) B17283253
theorem B1597687 : Blo 1596997 1597687 := bstep (se 1 (by rfl) ⟨1198265, by rfl⟩ : syracuseStep 1597687 = 2396531) B2396531
theorem B1597707 : Blo 1596997 1597707 := bstep (se 1 (by rfl) ⟨1198280, by rfl⟩ : syracuseStep 1597707 = 2396561) B2396561
theorem B1597719 : Blo 1596997 1597719 := bstep (se 1 (by rfl) ⟨1198289, by rfl⟩ : syracuseStep 1597719 = 2396579) B2396579
theorem B1597739 : Blo 1596997 1597739 := bstep (se 1 (by rfl) ⟨1198304, by rfl⟩ : syracuseStep 1597739 = 2396609) B2396609
theorem B4047155 : Blo 1596997 4047155 := bstep (se 1 (by rfl) ⟨3035366, by rfl⟩ : syracuseStep 4047155 = 6070733) B6070733
theorem B1597751 : Blo 1596997 1597751 := bstep (se 1 (by rfl) ⟨1198313, by rfl⟩ : syracuseStep 1597751 = 2396627) B2396627
theorem B5390657 : Blo 1596997 5390657 := bstep (se 2 (by rfl) ⟨2021496, by rfl⟩ : syracuseStep 5390657 = 4042993) B4042993
theorem B1597771 : Blo 1596997 1597771 := bstep (se 1 (by rfl) ⟨1198328, by rfl⟩ : syracuseStep 1597771 = 2396657) B2396657
theorem B2695511 : Blo 1596997 2695511 := bstep (se 1 (by rfl) ⟨2021633, by rfl⟩ : syracuseStep 2695511 = 4043267) B4043267
theorem B1597783 : Blo 1596997 1597783 := bstep (se 1 (by rfl) ⟨1198337, by rfl⟩ : syracuseStep 1597783 = 2396675) B2396675
theorem B3596633 : Blo 1596997 3596633 := bstep (se 2 (by rfl) ⟨1348737, by rfl⟩ : syracuseStep 3596633 = 2697475) B2697475
theorem B1597803 : Blo 1596997 1597803 := bstep (se 1 (by rfl) ⟨1198352, by rfl⟩ : syracuseStep 1597803 = 2396705) B2396705
theorem B1597815 : Blo 1596997 1597815 := bstep (se 1 (by rfl) ⟨1198361, by rfl⟩ : syracuseStep 1597815 = 2396723) B2396723
theorem B1597835 : Blo 1596997 1597835 := bstep (se 1 (by rfl) ⟨1198376, by rfl⟩ : syracuseStep 1597835 = 2396753) B2396753
theorem B1597847 : Blo 1596997 1597847 := bstep (se 1 (by rfl) ⟨1198385, by rfl⟩ : syracuseStep 1597847 = 2396771) B2396771
theorem B1597867 : Blo 1596997 1597867 := bstep (se 1 (by rfl) ⟨1198400, by rfl⟩ : syracuseStep 1597867 = 2396801) B2396801
theorem B9101747 : Blo 1596997 9101747 := bstep (se 1 (by rfl) ⟨6826310, by rfl⟩ : syracuseStep 9101747 = 13652621) B13652621
theorem B3596723 : Blo 1596997 3596723 := bstep (se 1 (by rfl) ⟨2697542, by rfl⟩ : syracuseStep 3596723 = 5395085) B5395085
theorem B1597879 : Blo 1596997 1597879 := bstep (se 1 (by rfl) ⟨1198409, by rfl⟩ : syracuseStep 1597879 = 2396819) B2396819
theorem B1597899 : Blo 1596997 1597899 := bstep (se 1 (by rfl) ⟨1198424, by rfl⟩ : syracuseStep 1597899 = 2396849) B2396849
theorem B2695639 : Blo 1596997 2695639 := bstep (se 1 (by rfl) ⟨2021729, by rfl⟩ : syracuseStep 2695639 = 4043459) B4043459
theorem B1597911 : Blo 1596997 1597911 := bstep (se 1 (by rfl) ⟨1198433, by rfl⟩ : syracuseStep 1597911 = 2396867) B2396867
theorem B3596759 : Blo 1596997 3596759 := bstep (se 1 (by rfl) ⟨2697569, by rfl⟩ : syracuseStep 3596759 = 5395139) B5395139
theorem B1597931 : Blo 1596997 1597931 := bstep (se 1 (by rfl) ⟨1198448, by rfl⟩ : syracuseStep 1597931 = 2396897) B2396897
theorem B1597943 : Blo 1596997 1597943 := bstep (se 1 (by rfl) ⟨1198457, by rfl⟩ : syracuseStep 1597943 = 2396915) B2396915
theorem B1597963 : Blo 1596997 1597963 := bstep (se 1 (by rfl) ⟨1198472, by rfl⟩ : syracuseStep 1597963 = 2396945) B2396945
theorem B1597975 : Blo 1596997 1597975 := bstep (se 1 (by rfl) ⟨1198481, by rfl⟩ : syracuseStep 1597975 = 2396963) B2396963
theorem B1597995 : Blo 1596997 1597995 := bstep (se 1 (by rfl) ⟨1198496, by rfl⟩ : syracuseStep 1597995 = 2396993) B2396993
theorem B1598007 : Blo 1596997 1598007 := bstep (se 1 (by rfl) ⟨1198505, by rfl⟩ : syracuseStep 1598007 = 2397011) B2397011
theorem B23036491 : Blo 1596997 23036491 := bstep (se 1 (by rfl) ⟨17277368, by rfl⟩ : syracuseStep 23036491 = 34554737) B34554737
theorem B1598027 : Blo 1596997 1598027 := bstep (se 1 (by rfl) ⟨1198520, by rfl⟩ : syracuseStep 1598027 = 2397041) B2397041
theorem B1598039 : Blo 1596997 1598039 := bstep (se 1 (by rfl) ⟨1198529, by rfl⟩ : syracuseStep 1598039 = 2397059) B2397059
theorem B1598059 : Blo 1596997 1598059 := bstep (se 1 (by rfl) ⟨1198544, by rfl⟩ : syracuseStep 1598059 = 2397089) B2397089
theorem B1598071 : Blo 1596997 1598071 := bstep (se 1 (by rfl) ⟨1198553, by rfl⟩ : syracuseStep 1598071 = 2397107) B2397107
theorem B11518595 : Blo 1596997 11518595 := bstep (se 1 (by rfl) ⟨8638946, by rfl⟩ : syracuseStep 11518595 = 17277893) B17277893
theorem B1598091 : Blo 1596997 1598091 := bstep (se 1 (by rfl) ⟨1198568, by rfl⟩ : syracuseStep 1598091 = 2397137) B2397137
theorem B3596939 : Blo 1596997 3596939 := bstep (se 1 (by rfl) ⟨2697704, by rfl⟩ : syracuseStep 3596939 = 5395409) B5395409
theorem B1598103 : Blo 1596997 1598103 := bstep (se 1 (by rfl) ⟨1198577, by rfl⟩ : syracuseStep 1598103 = 2397155) B2397155
theorem B1598123 : Blo 1596997 1598123 := bstep (se 1 (by rfl) ⟨1198592, by rfl⟩ : syracuseStep 1598123 = 2397185) B2397185
theorem B1598135 : Blo 1596997 1598135 := bstep (se 1 (by rfl) ⟨1198601, by rfl⟩ : syracuseStep 1598135 = 2397203) B2397203
theorem B3596993 : Blo 1596997 3596993 := bstep (se 2 (by rfl) ⟨1348872, by rfl⟩ : syracuseStep 3596993 = 2697745) B2697745
theorem B6152897 : Blo 1596997 6152897 := bstep (se 2 (by rfl) ⟨2307336, by rfl⟩ : syracuseStep 6152897 = 4614673) B4614673
theorem B1598155 : Blo 1596997 1598155 := bstep (se 1 (by rfl) ⟨1198616, by rfl⟩ : syracuseStep 1598155 = 2397233) B2397233
theorem B1598167 : Blo 1596997 1598167 := bstep (se 1 (by rfl) ⟨1198625, by rfl⟩ : syracuseStep 1598167 = 2397251) B2397251
theorem B1598187 : Blo 1596997 1598187 := bstep (se 1 (by rfl) ⟨1198640, by rfl⟩ : syracuseStep 1598187 = 2397281) B2397281
theorem B1598199 : Blo 1596997 1598199 := bstep (se 1 (by rfl) ⟨1198649, by rfl⟩ : syracuseStep 1598199 = 2397299) B2397299
theorem B1598219 : Blo 1596997 1598219 := bstep (se 1 (by rfl) ⟨1198664, by rfl⟩ : syracuseStep 1598219 = 2397329) B2397329
theorem B1598231 : Blo 1596997 1598231 := bstep (se 1 (by rfl) ⟨1198673, by rfl⟩ : syracuseStep 1598231 = 2397347) B2397347
theorem B1598251 : Blo 1596997 1598251 := bstep (se 1 (by rfl) ⟨1198688, by rfl⟩ : syracuseStep 1598251 = 2397377) B2397377
theorem B1598263 : Blo 1596997 1598263 := bstep (se 1 (by rfl) ⟨1198697, by rfl⟩ : syracuseStep 1598263 = 2397395) B2397395
theorem B1598283 : Blo 1596997 1598283 := bstep (se 1 (by rfl) ⟨1198712, by rfl⟩ : syracuseStep 1598283 = 2397425) B2397425
theorem B1598295 : Blo 1596997 1598295 := bstep (se 1 (by rfl) ⟨1198721, by rfl⟩ : syracuseStep 1598295 = 2397443) B2397443
theorem B5391197 : Blo 1596997 5391197 := bstep (se 3 (by rfl) ⟨1010849, by rfl⟩ : syracuseStep 5391197 = 2021699) B2021699
theorem B1598315 : Blo 1596997 1598315 := bstep (se 1 (by rfl) ⟨1198736, by rfl⟩ : syracuseStep 1598315 = 2397473) B2397473
theorem B1598327 : Blo 1596997 1598327 := bstep (se 1 (by rfl) ⟨1198745, by rfl⟩ : syracuseStep 1598327 = 2397491) B2397491
theorem B1598347 : Blo 1596997 1598347 := bstep (se 1 (by rfl) ⟨1198760, by rfl⟩ : syracuseStep 1598347 = 2397521) B2397521
theorem B1598359 : Blo 1596997 1598359 := bstep (se 1 (by rfl) ⟨1198769, by rfl⟩ : syracuseStep 1598359 = 2397539) B2397539
theorem B3597209 : Blo 1596997 3597209 := bstep (se 2 (by rfl) ⟨1348953, by rfl⟩ : syracuseStep 3597209 = 2697907) B2697907
theorem B1598379 : Blo 1596997 1598379 := bstep (se 1 (by rfl) ⟨1198784, by rfl⟩ : syracuseStep 1598379 = 2397569) B2397569
theorem B3031987 : Blo 1596997 3031987 := bstep (se 1 (by rfl) ⟨2273990, by rfl⟩ : syracuseStep 3031987 = 4547981) B4547981
theorem B1598391 : Blo 1596997 1598391 := bstep (se 1 (by rfl) ⟨1198793, by rfl⟩ : syracuseStep 1598391 = 2397587) B2397587
theorem B1598411 : Blo 1596997 1598411 := bstep (se 1 (by rfl) ⟨1198808, by rfl⟩ : syracuseStep 1598411 = 2397617) B2397617
theorem B1598423 : Blo 1596997 1598423 := bstep (se 1 (by rfl) ⟨1198817, by rfl⟩ : syracuseStep 1598423 = 2397635) B2397635
theorem B1598443 : Blo 1596997 1598443 := bstep (se 1 (by rfl) ⟨1198832, by rfl⟩ : syracuseStep 1598443 = 2397665) B2397665
theorem B3597299 : Blo 1596997 3597299 := bstep (se 1 (by rfl) ⟨2697974, by rfl⟩ : syracuseStep 3597299 = 5395949) B5395949
theorem B1598455 : Blo 1596997 1598455 := bstep (se 1 (by rfl) ⟨1198841, by rfl⟩ : syracuseStep 1598455 = 2397683) B2397683
theorem B1598475 : Blo 1596997 1598475 := bstep (se 1 (by rfl) ⟨1198856, by rfl⟩ : syracuseStep 1598475 = 2397713) B2397713
theorem B1598487 : Blo 1596997 1598487 := bstep (se 1 (by rfl) ⟨1198865, by rfl⟩ : syracuseStep 1598487 = 2397731) B2397731
theorem B6153239 : Blo 1596997 6153239 := bstep (se 1 (by rfl) ⟨4614929, by rfl⟩ : syracuseStep 6153239 = 9229859) B9229859
theorem B3597335 : Blo 1596997 3597335 := bstep (se 1 (by rfl) ⟨2698001, by rfl⟩ : syracuseStep 3597335 = 5396003) B5396003
theorem B13648931 : Blo 1596997 13648931 := bstep (se 1 (by rfl) ⟨10236698, by rfl⟩ : syracuseStep 13648931 = 20473397) B20473397
theorem B1598507 : Blo 1596997 1598507 := bstep (se 1 (by rfl) ⟨1198880, by rfl⟩ : syracuseStep 1598507 = 2397761) B2397761
theorem B1598519 : Blo 1596997 1598519 := bstep (se 1 (by rfl) ⟨1198889, by rfl⟩ : syracuseStep 1598519 = 2397779) B2397779
theorem B2696267 : Blo 1596997 2696267 := bstep (se 1 (by rfl) ⟨2022200, by rfl⟩ : syracuseStep 2696267 = 4044401) B4044401
theorem B1598539 : Blo 1596997 1598539 := bstep (se 1 (by rfl) ⟨1198904, by rfl⟩ : syracuseStep 1598539 = 2397809) B2397809
theorem B1598551 : Blo 1596997 1598551 := bstep (se 1 (by rfl) ⟨1198913, by rfl⟩ : syracuseStep 1598551 = 2397827) B2397827
theorem B1598571 : Blo 1596997 1598571 := bstep (se 1 (by rfl) ⟨1198928, by rfl⟩ : syracuseStep 1598571 = 2397857) B2397857
theorem B1598583 : Blo 1596997 1598583 := bstep (se 1 (by rfl) ⟨1198937, by rfl⟩ : syracuseStep 1598583 = 2397875) B2397875
theorem B1598603 : Blo 1596997 1598603 := bstep (se 1 (by rfl) ⟨1198952, by rfl⟩ : syracuseStep 1598603 = 2397905) B2397905
theorem B1598615 : Blo 1596997 1598615 := bstep (se 1 (by rfl) ⟨1198961, by rfl⟩ : syracuseStep 1598615 = 2397923) B2397923
theorem B1598635 : Blo 1596997 1598635 := bstep (se 1 (by rfl) ⟨1198976, by rfl⟩ : syracuseStep 1598635 = 2397953) B2397953
theorem B1598647 : Blo 1596997 1598647 := bstep (se 1 (by rfl) ⟨1198985, by rfl⟩ : syracuseStep 1598647 = 2397971) B2397971
theorem B2696395 : Blo 1596997 2696395 := bstep (se 1 (by rfl) ⟨2022296, by rfl⟩ : syracuseStep 2696395 = 4044593) B4044593
theorem B1598667 : Blo 1596997 1598667 := bstep (se 1 (by rfl) ⟨1199000, by rfl⟩ : syracuseStep 1598667 = 2398001) B2398001
theorem B3597515 : Blo 1596997 3597515 := bstep (se 1 (by rfl) ⟨2698136, by rfl⟩ : syracuseStep 3597515 = 5396273) B5396273
theorem B1598679 : Blo 1596997 1598679 := bstep (se 1 (by rfl) ⟨1199009, by rfl⟩ : syracuseStep 1598679 = 2398019) B2398019
theorem B1598699 : Blo 1596997 1598699 := bstep (se 1 (by rfl) ⟨1199024, by rfl⟩ : syracuseStep 1598699 = 2398049) B2398049
theorem B1598711 : Blo 1596997 1598711 := bstep (se 1 (by rfl) ⟨1199033, by rfl⟩ : syracuseStep 1598711 = 2398067) B2398067
theorem B3597569 : Blo 1596997 3597569 := bstep (se 2 (by rfl) ⟨1349088, by rfl⟩ : syracuseStep 3597569 = 2698177) B2698177
theorem B1598731 : Blo 1596997 1598731 := bstep (se 1 (by rfl) ⟨1199048, by rfl⟩ : syracuseStep 1598731 = 2398097) B2398097
theorem B1598743 : Blo 1596997 1598743 := bstep (se 1 (by rfl) ⟨1199057, by rfl⟩ : syracuseStep 1598743 = 2398115) B2398115
theorem B1598763 : Blo 1596997 1598763 := bstep (se 1 (by rfl) ⟨1199072, by rfl⟩ : syracuseStep 1598763 = 2398145) B2398145
theorem B1598775 : Blo 1596997 1598775 := bstep (se 1 (by rfl) ⟨1199081, by rfl⟩ : syracuseStep 1598775 = 2398163) B2398163
theorem B1598795 : Blo 1596997 1598795 := bstep (se 1 (by rfl) ⟨1199096, by rfl⟩ : syracuseStep 1598795 = 2398193) B2398193
theorem B1598807 : Blo 1596997 1598807 := bstep (se 1 (by rfl) ⟨1199105, by rfl⟩ : syracuseStep 1598807 = 2398211) B2398211
theorem B2696537 : Blo 1596997 2696537 := bstep (se 2 (by rfl) ⟨1011201, by rfl⟩ : syracuseStep 2696537 = 2022403) B2022403
theorem B8086877 : Blo 1596997 8086877 := bstep (se 3 (by rfl) ⟨1516289, by rfl⟩ : syracuseStep 8086877 = 3032579) B3032579
theorem B1598827 : Blo 1596997 1598827 := bstep (se 1 (by rfl) ⟨1199120, by rfl⟩ : syracuseStep 1598827 = 2398241) B2398241
theorem B1598839 : Blo 1596997 1598839 := bstep (se 1 (by rfl) ⟨1199129, by rfl⟩ : syracuseStep 1598839 = 2398259) B2398259
theorem B1598859 : Blo 1596997 1598859 := bstep (se 1 (by rfl) ⟨1199144, by rfl⟩ : syracuseStep 1598859 = 2398289) B2398289
theorem B1598871 : Blo 1596997 1598871 := bstep (se 1 (by rfl) ⟨1199153, by rfl⟩ : syracuseStep 1598871 = 2398307) B2398307
theorem B3032473 : Blo 1596997 3032473 := bstep (se 2 (by rfl) ⟨1137177, by rfl⟩ : syracuseStep 3032473 = 2274355) B2274355
theorem B1598891 : Blo 1596997 1598891 := bstep (se 1 (by rfl) ⟨1199168, by rfl⟩ : syracuseStep 1598891 = 2398337) B2398337
theorem B1598903 : Blo 1596997 1598903 := bstep (se 1 (by rfl) ⟨1199177, by rfl⟩ : syracuseStep 1598903 = 2398355) B2398355
theorem B1598923 : Blo 1596997 1598923 := bstep (se 1 (by rfl) ⟨1199192, by rfl⟩ : syracuseStep 1598923 = 2398385) B2398385
theorem B1598935 : Blo 1596997 1598935 := bstep (se 1 (by rfl) ⟨1199201, by rfl⟩ : syracuseStep 1598935 = 2398403) B2398403
theorem B2696665 : Blo 1596997 2696665 := bstep (se 2 (by rfl) ⟨1011249, by rfl⟩ : syracuseStep 2696665 = 2022499) B2022499
theorem B20481497 : Blo 1596997 20481497 := bstep (se 2 (by rfl) ⟨7680561, by rfl⟩ : syracuseStep 20481497 = 15361123) B15361123
theorem B1598955 : Blo 1596997 1598955 := bstep (se 1 (by rfl) ⟨1199216, by rfl⟩ : syracuseStep 1598955 = 2398433) B2398433
theorem B3073523 : Blo 1596997 3073523 := bstep (se 1 (by rfl) ⟨2305142, by rfl⟩ : syracuseStep 3073523 = 4610285) B4610285
theorem B1598967 : Blo 1596997 1598967 := bstep (se 1 (by rfl) ⟨1199225, by rfl⟩ : syracuseStep 1598967 = 2398451) B2398451
theorem B1598987 : Blo 1596997 1598987 := bstep (se 1 (by rfl) ⟨1199240, by rfl⟩ : syracuseStep 1598987 = 2398481) B2398481
theorem B2917913 : Blo 1596997 2917913 := bstep (se 2 (by rfl) ⟨1094217, by rfl⟩ : syracuseStep 2917913 = 2188435) B2188435
theorem B4924993 : Blo 1596997 4924993 := bstep (se 2 (by rfl) ⟨1846872, by rfl⟩ : syracuseStep 4924993 = 3693745) B3693745
theorem B2918003 : Blo 1596997 2918003 := bstep (se 1 (by rfl) ⟨2188502, by rfl⟩ : syracuseStep 2918003 = 4377005) B4377005
theorem B1918603 : Blo 1596997 1918603 := bstep (se 1 (by rfl) ⟨1438952, by rfl⟩ : syracuseStep 1918603 = 2877905) B2877905
theorem B6063761 : Blo 1596997 6063761 := bstep (se 2 (by rfl) ⟨2273910, by rfl⟩ : syracuseStep 6063761 = 4547821) B4547821
theorem B26633879 : Blo 1596997 26633879 := bstep (se 1 (by rfl) ⟨19975409, by rfl⟩ : syracuseStep 26633879 = 39950819) B39950819
theorem B1705655 : Blo 1596997 1705655 := bstep (se 1 (by rfl) ⟨1279241, by rfl⟩ : syracuseStep 1705655 = 2558483) B2558483
theorem B9103205 : Blo 1596997 9103205 := bstep (se 4 (by rfl) ⟨853425, by rfl⟩ : syracuseStep 9103205 = 1706851) B1706851
theorem B13846373 : Blo 1596997 13846373 := bstep (se 4 (by rfl) ⟨1298097, by rfl⟩ : syracuseStep 13846373 = 2596195) B2596195
theorem B7014275 : Blo 1596997 7014275 := bstep (se 1 (by rfl) ⟨5260706, by rfl⟩ : syracuseStep 7014275 = 10521413) B10521413
theorem B6563729 : Blo 1596997 6563729 := bstep (se 2 (by rfl) ⟨2461398, by rfl⟩ : syracuseStep 6563729 = 4922797) B4922797
theorem B11519921 : Blo 1596997 11519921 := bstep (se 2 (by rfl) ⟨4319970, by rfl⟩ : syracuseStep 11519921 = 8639941) B8639941
theorem B3033035 : Blo 1596997 3033035 := bstep (se 1 (by rfl) ⟨2274776, by rfl⟩ : syracuseStep 3033035 = 4549553) B4549553
theorem B5392331 : Blo 1596997 5392331 := bstep (se 1 (by rfl) ⟨4044248, by rfl⟩ : syracuseStep 5392331 = 8088497) B8088497
theorem B2697239 : Blo 1596997 2697239 := bstep (se 1 (by rfl) ⟨2022929, by rfl⟩ : syracuseStep 2697239 = 4045859) B4045859
theorem B1706027 : Blo 1596997 1706027 := bstep (se 1 (by rfl) ⟨1279520, by rfl⟩ : syracuseStep 1706027 = 2559041) B2559041
theorem B6064217 : Blo 1596997 6064217 := bstep (se 2 (by rfl) ⟨2274081, by rfl⟩ : syracuseStep 6064217 = 4548163) B4548163
theorem B3033217 : Blo 1596997 3033217 := bstep (se 2 (by rfl) ⟨1137456, by rfl⟩ : syracuseStep 3033217 = 2274913) B2274913
theorem B62253197 : Blo 1596997 62253197 := bstep (se 3 (by rfl) ⟨11672474, by rfl⟩ : syracuseStep 62253197 = 23344949) B23344949
theorem B2697367 : Blo 1596997 2697367 := bstep (se 1 (by rfl) ⟨2023025, by rfl⟩ : syracuseStep 2697367 = 4046051) B4046051
theorem B5392601 : Blo 1596997 5392601 := bstep (se 2 (by rfl) ⟨2022225, by rfl⟩ : syracuseStep 5392601 = 4044451) B4044451
theorem B6064429 : Blo 1596997 6064429 := bstep (se 3 (by rfl) ⟨1137080, by rfl⟩ : syracuseStep 6064429 = 2274161) B2274161
theorem B9103661 : Blo 1596997 9103661 := bstep (se 3 (by rfl) ⟨1706936, by rfl⟩ : syracuseStep 9103661 = 3413873) B3413873
theorem B1796683 : Blo 1596997 1796683 := bstep (se 1 (by rfl) ⟨1347512, by rfl⟩ : syracuseStep 1796683 = 2695025) B2695025
theorem B6064733 : Blo 1596997 6064733 := bstep (se 3 (by rfl) ⟨1137137, by rfl⟩ : syracuseStep 6064733 = 2274275) B2274275
theorem B1796791 : Blo 1596997 1796791 := bstep (se 1 (by rfl) ⟨1347593, by rfl⟩ : syracuseStep 1796791 = 2695187) B2695187
theorem B2697995 : Blo 1596997 2697995 := bstep (se 1 (by rfl) ⟨2023496, by rfl⟩ : syracuseStep 2697995 = 4046993) B4046993
theorem B13839169 : Blo 1596997 13839169 := bstep (se 2 (by rfl) ⟨5189688, by rfl⟩ : syracuseStep 13839169 = 10379377) B10379377
theorem B1919819 : Blo 1596997 1919819 := bstep (se 1 (by rfl) ⟨1439864, by rfl⟩ : syracuseStep 1919819 = 2879729) B2879729
theorem B3033931 : Blo 1596997 3033931 := bstep (se 1 (by rfl) ⟨2275448, by rfl⟩ : syracuseStep 3033931 = 4550897) B4550897
theorem B5188441 : Blo 1596997 5188441 := bstep (se 2 (by rfl) ⟨1945665, by rfl⟩ : syracuseStep 5188441 = 3891331) B3891331
theorem B41503589 : Blo 1596997 41503589 := bstep (se 4 (by rfl) ⟨3890961, by rfl⟩ : syracuseStep 41503589 = 7781923) B7781923
theorem B1796971 : Blo 1596997 1796971 := bstep (se 1 (by rfl) ⟨1347728, by rfl⟩ : syracuseStep 1796971 = 2695457) B2695457
theorem B2698123 : Blo 1596997 2698123 := bstep (se 1 (by rfl) ⟨2023592, by rfl⟩ : syracuseStep 2698123 = 4047185) B4047185
theorem B5393303 : Blo 1596997 5393303 := bstep (se 1 (by rfl) ⟨4044977, by rfl⟩ : syracuseStep 5393303 = 8089955) B8089955
theorem B3034007 : Blo 1596997 3034007 := bstep (se 1 (by rfl) ⟨2275505, by rfl⟩ : syracuseStep 3034007 = 4551011) B4551011
theorem B1797079 : Blo 1596997 1797079 := bstep (se 1 (by rfl) ⟨1347809, by rfl⟩ : syracuseStep 1797079 = 2695619) B2695619
theorem B9104345 : Blo 1596997 9104345 := bstep (se 2 (by rfl) ⟨3414129, by rfl⟩ : syracuseStep 9104345 = 6828259) B6828259
theorem B1707031 : Blo 1596997 1707031 := bstep (se 1 (by rfl) ⟨1280273, by rfl⟩ : syracuseStep 1707031 = 2560547) B2560547
theorem B2698265 : Blo 1596997 2698265 := bstep (se 2 (by rfl) ⟨1011849, by rfl⟩ : syracuseStep 2698265 = 2023699) B2023699
theorem B3943475 : Blo 1596997 3943475 := bstep (se 1 (by rfl) ⟨2957606, by rfl⟩ : syracuseStep 3943475 = 5915213) B5915213
theorem B5762123 : Blo 1596997 5762123 := bstep (se 1 (by rfl) ⟨4321592, by rfl⟩ : syracuseStep 5762123 = 8643185) B8643185
theorem B1797259 : Blo 1596997 1797259 := bstep (se 1 (by rfl) ⟨1347944, by rfl⟩ : syracuseStep 1797259 = 2695889) B2695889
theorem B9096371 : Blo 1596997 9096371 := bstep (se 1 (by rfl) ⟨6822278, by rfl⟩ : syracuseStep 9096371 = 13644557) B13644557
theorem B4099265 : Blo 1596997 4099265 := bstep (se 2 (by rfl) ⟨1537224, by rfl⟩ : syracuseStep 4099265 = 3074449) B3074449
theorem B1797367 : Blo 1596997 1797367 := bstep (se 1 (by rfl) ⟨1348025, by rfl⟩ : syracuseStep 1797367 = 2696051) B2696051
theorem B6827267 : Blo 1596997 6827267 := bstep (se 1 (by rfl) ⟨5120450, by rfl⟩ : syracuseStep 6827267 = 10240901) B10240901
theorem B8088983 : Blo 1596997 8088983 := bstep (se 1 (by rfl) ⟨6066737, by rfl⟩ : syracuseStep 8088983 = 12133475) B12133475
theorem B1797547 : Blo 1596997 1797547 := bstep (se 1 (by rfl) ⟨1348160, by rfl⟩ : syracuseStep 1797547 = 2696321) B2696321
theorem B5393843 : Blo 1596997 5393843 := bstep (se 1 (by rfl) ⟨4045382, by rfl⟩ : syracuseStep 5393843 = 8090765) B8090765
theorem B2395595 : Blo 1596997 2395595 := bstep (se 1 (by rfl) ⟨1796696, by rfl⟩ : syracuseStep 2395595 = 3593393) B3593393
theorem B2395607 : Blo 1596997 2395607 := bstep (se 1 (by rfl) ⟨1796705, by rfl⟩ : syracuseStep 2395607 = 3593411) B3593411
theorem B1822187 : Blo 1596997 1822187 := bstep (se 1 (by rfl) ⟨1366640, by rfl⟩ : syracuseStep 1822187 = 2733281) B2733281
theorem B1797655 : Blo 1596997 1797655 := bstep (se 1 (by rfl) ⟨1348241, by rfl⟩ : syracuseStep 1797655 = 2696483) B2696483
theorem B2395673 : Blo 1596997 2395673 := bstep (se 2 (by rfl) ⟨898377, by rfl⟩ : syracuseStep 2395673 = 1796755) B1796755
theorem B3034675 : Blo 1596997 3034675 := bstep (se 1 (by rfl) ⟨2276006, by rfl⟩ : syracuseStep 3034675 = 4552013) B4552013
theorem B22171229 : Blo 1596997 22171229 := bstep (se 3 (by rfl) ⟨4157105, by rfl⟩ : syracuseStep 22171229 = 8314211) B8314211
theorem B2395787 : Blo 1596997 2395787 := bstep (se 1 (by rfl) ⟨1796840, by rfl⟩ : syracuseStep 2395787 = 3593681) B3593681
theorem B2395799 : Blo 1596997 2395799 := bstep (se 1 (by rfl) ⟨1796849, by rfl⟩ : syracuseStep 2395799 = 3593699) B3593699
theorem B4992691 : Blo 1596997 4992691 := bstep (se 1 (by rfl) ⟨3744518, by rfl⟩ : syracuseStep 4992691 = 7489037) B7489037
theorem B5394113 : Blo 1596997 5394113 := bstep (se 2 (by rfl) ⟨2022792, by rfl⟩ : syracuseStep 5394113 = 4045585) B4045585
theorem B1797835 : Blo 1596997 1797835 := bstep (se 1 (by rfl) ⟨1348376, by rfl⟩ : syracuseStep 1797835 = 2696753) B2696753
theorem B4042457 : Blo 1596997 4042457 := bstep (se 2 (by rfl) ⟨1515921, by rfl⟩ : syracuseStep 4042457 = 3031843) B3031843
theorem B2395865 : Blo 1596997 2395865 := bstep (se 2 (by rfl) ⟨898449, by rfl⟩ : syracuseStep 2395865 = 1796899) B1796899
theorem B3460825 : Blo 1596997 3460825 := bstep (se 2 (by rfl) ⟨1297809, by rfl⟩ : syracuseStep 3460825 = 2595619) B2595619
theorem B3411713 : Blo 1596997 3411713 := bstep (se 2 (by rfl) ⟨1279392, by rfl⟩ : syracuseStep 3411713 = 2558785) B2558785
theorem B3034903 : Blo 1596997 3034903 := bstep (se 1 (by rfl) ⟨2276177, by rfl⟩ : syracuseStep 3034903 = 4552355) B4552355
theorem B1797943 : Blo 1596997 1797943 := bstep (se 1 (by rfl) ⟨1348457, by rfl⟩ : syracuseStep 1797943 = 2696915) B2696915
theorem B2395979 : Blo 1596997 2395979 := bstep (se 1 (by rfl) ⟨1796984, by rfl⟩ : syracuseStep 2395979 = 3593969) B3593969
theorem B2395991 : Blo 1596997 2395991 := bstep (se 1 (by rfl) ⟨1796993, by rfl⟩ : syracuseStep 2395991 = 3593987) B3593987
theorem B8638339 : Blo 1596997 8638339 := bstep (se 1 (by rfl) ⟨6478754, by rfl⟩ : syracuseStep 8638339 = 12957509) B12957509
theorem B3035009 : Blo 1596997 3035009 := bstep (se 2 (by rfl) ⟨1138128, by rfl⟩ : syracuseStep 3035009 = 2276257) B2276257
theorem B2879383 : Blo 1596997 2879383 := bstep (se 1 (by rfl) ⟨2159537, by rfl⟩ : syracuseStep 2879383 = 4319075) B4319075
theorem B1920919 : Blo 1596997 1920919 := bstep (se 1 (by rfl) ⟨1440689, by rfl⟩ : syracuseStep 1920919 = 2881379) B2881379
theorem B2396057 : Blo 1596997 2396057 := bstep (se 2 (by rfl) ⟨898521, by rfl⟩ : syracuseStep 2396057 = 1797043) B1797043
theorem B15175603 : Blo 1596997 15175603 := bstep (se 1 (by rfl) ⟨11381702, by rfl⟩ : syracuseStep 15175603 = 22763405) B22763405
theorem B1798123 : Blo 1596997 1798123 := bstep (se 1 (by rfl) ⟨1348592, by rfl⟩ : syracuseStep 1798123 = 2697185) B2697185
theorem B2396171 : Blo 1596997 2396171 := bstep (se 1 (by rfl) ⟨1797128, by rfl⟩ : syracuseStep 2396171 = 3594257) B3594257
theorem B2396183 : Blo 1596997 2396183 := bstep (se 1 (by rfl) ⟨1797137, by rfl⟩ : syracuseStep 2396183 = 3594275) B3594275
theorem B3035161 : Blo 1596997 3035161 := bstep (se 2 (by rfl) ⟨1138185, by rfl⟩ : syracuseStep 3035161 = 2276371) B2276371
theorem B32804939 : Blo 1596997 32804939 := bstep (se 1 (by rfl) ⟨24603704, by rfl⟩ : syracuseStep 32804939 = 49207409) B49207409
theorem B1798231 : Blo 1596997 1798231 := bstep (se 1 (by rfl) ⟨1348673, by rfl⟩ : syracuseStep 1798231 = 2697347) B2697347
theorem B2396249 : Blo 1596997 2396249 := bstep (se 2 (by rfl) ⟨898593, by rfl⟩ : syracuseStep 2396249 = 1797187) B1797187
theorem B29151413 : Blo 1596997 29151413 := bstep (se 5 (by rfl) ⟨1366472, by rfl⟩ : syracuseStep 29151413 = 2732945) B2732945
theorem B2396363 : Blo 1596997 2396363 := bstep (se 1 (by rfl) ⟨1797272, by rfl⟩ : syracuseStep 2396363 = 3594545) B3594545
theorem B2158807 : Blo 1596997 2158807 := bstep (se 1 (by rfl) ⟨1619105, by rfl⟩ : syracuseStep 2158807 = 3238211) B3238211
theorem B2396375 : Blo 1596997 2396375 := bstep (se 1 (by rfl) ⟨1797281, by rfl⟩ : syracuseStep 2396375 = 3594563) B3594563
theorem B5394653 : Blo 1596997 5394653 := bstep (se 3 (by rfl) ⟨1011497, by rfl⟩ : syracuseStep 5394653 = 2022995) B2022995
theorem B1798411 : Blo 1596997 1798411 := bstep (se 1 (by rfl) ⟨1348808, by rfl⟩ : syracuseStep 1798411 = 2697617) B2697617
theorem B2396441 : Blo 1596997 2396441 := bstep (se 2 (by rfl) ⟨898665, by rfl⟩ : syracuseStep 2396441 = 1797331) B1797331
theorem B25932149 : Blo 1596997 25932149 := bstep (se 5 (by rfl) ⟨1215569, by rfl⟩ : syracuseStep 25932149 = 2431139) B2431139
theorem B1798519 : Blo 1596997 1798519 := bstep (se 1 (by rfl) ⟨1348889, by rfl⟩ : syracuseStep 1798519 = 2697779) B2697779
theorem B2396555 : Blo 1596997 2396555 := bstep (se 1 (by rfl) ⟨1797416, by rfl⟩ : syracuseStep 2396555 = 3594833) B3594833
theorem B2396567 : Blo 1596997 2396567 := bstep (se 1 (by rfl) ⟨1797425, by rfl⟩ : syracuseStep 2396567 = 3594851) B3594851
theorem B2396633 : Blo 1596997 2396633 := bstep (se 2 (by rfl) ⟨898737, by rfl⟩ : syracuseStep 2396633 = 1797475) B1797475
theorem B1798699 : Blo 1596997 1798699 := bstep (se 1 (by rfl) ⟨1349024, by rfl⟩ : syracuseStep 1798699 = 2698049) B2698049
theorem B2396747 : Blo 1596997 2396747 := bstep (se 1 (by rfl) ⟨1797560, by rfl⟩ : syracuseStep 2396747 = 3595121) B3595121
theorem B2396759 : Blo 1596997 2396759 := bstep (se 1 (by rfl) ⟨1797569, by rfl⟩ : syracuseStep 2396759 = 3595139) B3595139
theorem B9097829 : Blo 1596997 9097829 := bstep (se 4 (by rfl) ⟨852921, by rfl⟩ : syracuseStep 9097829 = 1705843) B1705843
theorem B2880139 : Blo 1596997 2880139 := bstep (se 1 (by rfl) ⟨2160104, by rfl⟩ : syracuseStep 2880139 = 4320209) B4320209
theorem B20468375 : Blo 1596997 20468375 := bstep (se 1 (by rfl) ⟨15351281, by rfl⟩ : syracuseStep 20468375 = 30702563) B30702563
theorem B1798807 : Blo 1596997 1798807 := bstep (se 1 (by rfl) ⟨1349105, by rfl⟩ : syracuseStep 1798807 = 2698211) B2698211
theorem B2396825 : Blo 1596997 2396825 := bstep (se 2 (by rfl) ⟨898809, by rfl⟩ : syracuseStep 2396825 = 1797619) B1797619
theorem B2396939 : Blo 1596997 2396939 := bstep (se 1 (by rfl) ⟨1797704, by rfl⟩ : syracuseStep 2396939 = 3595409) B3595409
theorem B2396951 : Blo 1596997 2396951 := bstep (se 1 (by rfl) ⟨1797713, by rfl⟩ : syracuseStep 2396951 = 3595427) B3595427
theorem B2397017 : Blo 1596997 2397017 := bstep (se 2 (by rfl) ⟨898881, by rfl⟩ : syracuseStep 2397017 = 1797763) B1797763
theorem B6828893 : Blo 1596997 6828893 := bstep (se 3 (by rfl) ⟨1280417, by rfl⟩ : syracuseStep 6828893 = 2560835) B2560835
theorem B2397131 : Blo 1596997 2397131 := bstep (se 1 (by rfl) ⟨1797848, by rfl⟩ : syracuseStep 2397131 = 3595697) B3595697
theorem B2397143 : Blo 1596997 2397143 := bstep (se 1 (by rfl) ⟨1797857, by rfl⟩ : syracuseStep 2397143 = 3595715) B3595715
theorem B2397209 : Blo 1596997 2397209 := bstep (se 2 (by rfl) ⟨898953, by rfl⟩ : syracuseStep 2397209 = 1797907) B1797907
theorem B3593267 : Blo 1596997 3593267 := bstep (se 1 (by rfl) ⟨2694950, by rfl⟩ : syracuseStep 3593267 = 5389901) B5389901
theorem B3839051 : Blo 1596997 3839051 := bstep (se 1 (by rfl) ⟨2879288, by rfl⟩ : syracuseStep 3839051 = 5758577) B5758577
theorem B3593303 : Blo 1596997 3593303 := bstep (se 1 (by rfl) ⟨2694977, by rfl⟩ : syracuseStep 3593303 = 5389955) B5389955
theorem B5755997 : Blo 1596997 5755997 := bstep (se 3 (by rfl) ⟨1079249, by rfl⟩ : syracuseStep 5755997 = 2158499) B2158499
theorem B6067331 : Blo 1596997 6067331 := bstep (se 1 (by rfl) ⟨4550498, by rfl⟩ : syracuseStep 6067331 = 9100997) B9100997
theorem B2397323 : Blo 1596997 2397323 := bstep (se 1 (by rfl) ⟨1797992, by rfl⟩ : syracuseStep 2397323 = 3595985) B3595985
theorem B6067345 : Blo 1596997 6067345 := bstep (se 2 (by rfl) ⟨2275254, by rfl⟩ : syracuseStep 6067345 = 4550509) B4550509
theorem B2397335 : Blo 1596997 2397335 := bstep (se 1 (by rfl) ⟨1798001, by rfl⟩ : syracuseStep 2397335 = 3596003) B3596003
theorem B2880715 : Blo 1596997 2880715 := bstep (se 1 (by rfl) ⟨2160536, by rfl⟩ : syracuseStep 2880715 = 4321073) B4321073
theorem B2397401 : Blo 1596997 2397401 := bstep (se 2 (by rfl) ⟨899025, by rfl⟩ : syracuseStep 2397401 = 1798051) B1798051
theorem B5756125 : Blo 1596997 5756125 := bstep (se 3 (by rfl) ⟨1079273, by rfl⟩ : syracuseStep 5756125 = 2158547) B2158547
theorem B14578949 : Blo 1596997 14578949 := bstep (se 4 (by rfl) ⟨1366776, by rfl⟩ : syracuseStep 14578949 = 2733553) B2733553
theorem B3593483 : Blo 1596997 3593483 := bstep (se 1 (by rfl) ⟨2695112, by rfl⟩ : syracuseStep 3593483 = 5390225) B5390225
theorem B2274571 : Blo 1596997 2274571 := bstep (se 1 (by rfl) ⟨1705928, by rfl⟩ : syracuseStep 2274571 = 3411857) B3411857
theorem B9098513 : Blo 1596997 9098513 := bstep (se 2 (by rfl) ⟨3411942, by rfl⟩ : syracuseStep 9098513 = 6823885) B6823885
theorem B2274583 : Blo 1596997 2274583 := bstep (se 1 (by rfl) ⟨1705937, by rfl⟩ : syracuseStep 2274583 = 3411875) B3411875
theorem B3593537 : Blo 1596997 3593537 := bstep (se 2 (by rfl) ⟨1347576, by rfl⟩ : syracuseStep 3593537 = 2695153) B2695153
theorem B4044107 : Blo 1596997 4044107 := bstep (se 1 (by rfl) ⟨3033080, by rfl⟩ : syracuseStep 4044107 = 6066161) B6066161
theorem B2397515 : Blo 1596997 2397515 := bstep (se 1 (by rfl) ⟨1798136, by rfl⟩ : syracuseStep 2397515 = 3596273) B3596273
theorem B5395787 : Blo 1596997 5395787 := bstep (se 1 (by rfl) ⟨4046840, by rfl⟩ : syracuseStep 5395787 = 8093681) B8093681
theorem B2495831 : Blo 1596997 2495831 := bstep (se 1 (by rfl) ⟨1871873, by rfl⟩ : syracuseStep 2495831 = 3743747) B3743747
theorem B5117273 : Blo 1596997 5117273 := bstep (se 2 (by rfl) ⟨1918977, by rfl⟩ : syracuseStep 5117273 = 3837955) B3837955
theorem B2397527 : Blo 1596997 2397527 := bstep (se 1 (by rfl) ⟨1798145, by rfl⟩ : syracuseStep 2397527 = 3596291) B3596291
theorem B20485493 : Blo 1596997 20485493 := bstep (se 5 (by rfl) ⟨960257, by rfl⟩ : syracuseStep 20485493 = 1920515) B1920515
theorem B2397593 : Blo 1596997 2397593 := bstep (se 2 (by rfl) ⟨899097, by rfl⟩ : syracuseStep 2397593 = 1798195) B1798195
theorem B2430361 : Blo 1596997 2430361 := bstep (se 2 (by rfl) ⟨911385, by rfl⟩ : syracuseStep 2430361 = 1822771) B1822771
theorem B6067649 : Blo 1596997 6067649 := bstep (se 2 (by rfl) ⟨2275368, by rfl⟩ : syracuseStep 6067649 = 4550737) B4550737
theorem B4552139 : Blo 1596997 4552139 := bstep (se 1 (by rfl) ⟨3414104, by rfl⟩ : syracuseStep 4552139 = 6828209) B6828209
theorem B3413515 : Blo 1596997 3413515 := bstep (se 1 (by rfl) ⟨2560136, by rfl⟩ : syracuseStep 3413515 = 5120273) B5120273
theorem B2397707 : Blo 1596997 2397707 := bstep (se 1 (by rfl) ⟨1798280, by rfl⟩ : syracuseStep 2397707 = 3596561) B3596561
theorem B2397719 : Blo 1596997 2397719 := bstep (se 1 (by rfl) ⟨1798289, by rfl⟩ : syracuseStep 2397719 = 3596579) B3596579
theorem B6829591 : Blo 1596997 6829591 := bstep (se 1 (by rfl) ⟨5122193, by rfl⟩ : syracuseStep 6829591 = 10244387) B10244387
theorem B3593753 : Blo 1596997 3593753 := bstep (se 2 (by rfl) ⟨1347657, by rfl⟩ : syracuseStep 3593753 = 2695315) B2695315
theorem B2397785 : Blo 1596997 2397785 := bstep (se 2 (by rfl) ⟨899169, by rfl⟩ : syracuseStep 2397785 = 1798339) B1798339
theorem B5396057 : Blo 1596997 5396057 := bstep (se 2 (by rfl) ⟨2023521, by rfl⟩ : syracuseStep 5396057 = 4047043) B4047043
theorem B3593843 : Blo 1596997 3593843 := bstep (se 1 (by rfl) ⟨2695382, by rfl⟩ : syracuseStep 3593843 = 5390765) B5390765
theorem B3593879 : Blo 1596997 3593879 := bstep (se 1 (by rfl) ⟨2695409, by rfl⟩ : syracuseStep 3593879 = 5390819) B5390819
theorem B13653683 : Blo 1596997 13653683 := bstep (se 1 (by rfl) ⟨10240262, by rfl⟩ : syracuseStep 13653683 = 20480525) B20480525
theorem B2397899 : Blo 1596997 2397899 := bstep (se 1 (by rfl) ⟨1798424, by rfl⟩ : syracuseStep 2397899 = 3596849) B3596849
theorem B2397911 : Blo 1596997 2397911 := bstep (se 1 (by rfl) ⟨1798433, by rfl⟩ : syracuseStep 2397911 = 3596867) B3596867
theorem B2397977 : Blo 1596997 2397977 := bstep (se 2 (by rfl) ⟨899241, by rfl⟩ : syracuseStep 2397977 = 1798483) B1798483
theorem B3594059 : Blo 1596997 3594059 := bstep (se 1 (by rfl) ⟨2695544, by rfl⟩ : syracuseStep 3594059 = 5391089) B5391089
theorem B4552537 : Blo 1596997 4552537 := bstep (se 2 (by rfl) ⟨1707201, by rfl⟩ : syracuseStep 4552537 = 3414403) B3414403
theorem B3594113 : Blo 1596997 3594113 := bstep (se 2 (by rfl) ⟨1347792, by rfl⟩ : syracuseStep 3594113 = 2695585) B2695585
theorem B2398091 : Blo 1596997 2398091 := bstep (se 1 (by rfl) ⟨1798568, by rfl⟩ : syracuseStep 2398091 = 3597137) B3597137
theorem B2398103 : Blo 1596997 2398103 := bstep (se 1 (by rfl) ⟨1798577, by rfl⟩ : syracuseStep 2398103 = 3597155) B3597155
theorem B4610009 : Blo 1596997 4610009 := bstep (se 2 (by rfl) ⟨1728753, by rfl⟩ : syracuseStep 4610009 = 3457507) B3457507
theorem B7780313 : Blo 1596997 7780313 := bstep (se 2 (by rfl) ⟨2917617, by rfl⟩ : syracuseStep 7780313 = 5835235) B5835235
theorem B2398169 : Blo 1596997 2398169 := bstep (se 2 (by rfl) ⟨899313, by rfl⟩ : syracuseStep 2398169 = 1798627) B1798627
theorem B3840023 : Blo 1596997 3840023 := bstep (se 1 (by rfl) ⟨2880017, by rfl⟩ : syracuseStep 3840023 = 5760035) B5760035
theorem B2398283 : Blo 1596997 2398283 := bstep (se 1 (by rfl) ⟨1798712, by rfl⟩ : syracuseStep 2398283 = 3597425) B3597425
theorem B2398295 : Blo 1596997 2398295 := bstep (se 1 (by rfl) ⟨1798721, by rfl⟩ : syracuseStep 2398295 = 3597443) B3597443
theorem B3594329 : Blo 1596997 3594329 := bstep (se 2 (by rfl) ⟨1347873, by rfl⟩ : syracuseStep 3594329 = 2695747) B2695747
theorem B6068317 : Blo 1596997 6068317 := bstep (se 3 (by rfl) ⟨1137809, by rfl⟩ : syracuseStep 6068317 = 2275619) B2275619
theorem B2021527 : Blo 1596997 2021527 := bstep (se 1 (by rfl) ⟨1516145, by rfl⟩ : syracuseStep 2021527 = 3032291) B3032291
theorem B2398361 : Blo 1596997 2398361 := bstep (se 2 (by rfl) ⟨899385, by rfl⟩ : syracuseStep 2398361 = 1798771) B1798771
theorem B3594419 : Blo 1596997 3594419 := bstep (se 1 (by rfl) ⟨2695814, by rfl⟩ : syracuseStep 3594419 = 5391629) B5391629
theorem B3594455 : Blo 1596997 3594455 := bstep (se 1 (by rfl) ⟨2695841, by rfl⟩ : syracuseStep 3594455 = 5391683) B5391683
theorem B2398475 : Blo 1596997 2398475 := bstep (se 1 (by rfl) ⟨1798856, by rfl⟩ : syracuseStep 2398475 = 3597713) B3597713
theorem B4045079 : Blo 1596997 4045079 := bstep (se 1 (by rfl) ⟨3033809, by rfl⟩ : syracuseStep 4045079 = 6067619) B6067619
theorem B2398487 : Blo 1596997 2398487 := bstep (se 1 (by rfl) ⟨1798865, by rfl⟩ : syracuseStep 2398487 = 3597731) B3597731
theorem B49174901 : Blo 1596997 49174901 := bstep (se 5 (by rfl) ⟨2305073, by rfl⟩ : syracuseStep 49174901 = 4610147) B4610147
theorem B10238339 : Blo 1596997 10238339 := bstep (se 1 (by rfl) ⟨7678754, by rfl⟩ : syracuseStep 10238339 = 15357509) B15357509
theorem B3594635 : Blo 1596997 3594635 := bstep (se 1 (by rfl) ⟨2695976, by rfl⟩ : syracuseStep 3594635 = 5391953) B5391953
theorem B3594689 : Blo 1596997 3594689 := bstep (se 2 (by rfl) ⟨1348008, by rfl⟩ : syracuseStep 3594689 = 2696017) B2696017
theorem B11516377 : Blo 1596997 11516377 := bstep (se 2 (by rfl) ⟨4318641, by rfl⟩ : syracuseStep 11516377 = 8637283) B8637283
theorem B7682521 : Blo 1596997 7682521 := bstep (se 2 (by rfl) ⟨2880945, by rfl⟩ : syracuseStep 7682521 = 5761891) B5761891
theorem B3594905 : Blo 1596997 3594905 := bstep (se 2 (by rfl) ⟨1348089, by rfl⟩ : syracuseStep 3594905 = 2696179) B2696179
theorem B3594995 : Blo 1596997 3594995 := bstep (se 1 (by rfl) ⟨2696246, by rfl⟩ : syracuseStep 3594995 = 5392493) B5392493
theorem B3595031 : Blo 1596997 3595031 := bstep (se 1 (by rfl) ⟨2696273, by rfl⟩ : syracuseStep 3595031 = 5392547) B5392547
theorem B3414899 : Blo 1596997 3414899 := bstep (se 1 (by rfl) ⟨2561174, by rfl⟩ : syracuseStep 3414899 = 5122349) B5122349
theorem B8092547 : Blo 1596997 8092547 := bstep (se 1 (by rfl) ⟨6069410, by rfl⟩ : syracuseStep 8092547 = 12138821) B12138821
theorem B4045747 : Blo 1596997 4045747 := bstep (se 1 (by rfl) ⟨3034310, by rfl⟩ : syracuseStep 4045747 = 6068621) B6068621
theorem B5118913 : Blo 1596997 5118913 := bstep (se 2 (by rfl) ⟨1919592, by rfl⟩ : syracuseStep 5118913 = 3839185) B3839185
theorem B3595211 : Blo 1596997 3595211 := bstep (se 1 (by rfl) ⟨2696408, by rfl⟩ : syracuseStep 3595211 = 5392817) B5392817
theorem B2022347 : Blo 1596997 2022347 := bstep (se 1 (by rfl) ⟨1516760, by rfl⟩ : syracuseStep 2022347 = 3033521) B3033521
theorem B3595265 : Blo 1596997 3595265 := bstep (se 2 (by rfl) ⟨1348224, by rfl⟩ : syracuseStep 3595265 = 2696449) B2696449
theorem B4045889 : Blo 1596997 4045889 := bstep (se 2 (by rfl) ⟨1517208, by rfl⟩ : syracuseStep 4045889 = 3034417) B3034417
theorem B7683137 : Blo 1596997 7683137 := bstep (se 2 (by rfl) ⟨2881176, by rfl⟩ : syracuseStep 7683137 = 5762353) B5762353
theorem B27311255 : Blo 1596997 27311255 := bstep (se 1 (by rfl) ⟨20483441, by rfl⟩ : syracuseStep 27311255 = 40966883) B40966883
theorem B3595481 : Blo 1596997 3595481 := bstep (se 2 (by rfl) ⟨1348305, by rfl⟩ : syracuseStep 3595481 = 2696611) B2696611
theorem B4611293 : Blo 1596997 4611293 := bstep (se 3 (by rfl) ⟨864617, by rfl⟩ : syracuseStep 4611293 = 1729235) B1729235
theorem B12139793 : Blo 1596997 12139793 := bstep (se 2 (by rfl) ⟨4552422, by rfl⟩ : syracuseStep 12139793 = 9104845) B9104845
theorem B2276633 : Blo 1596997 2276633 := bstep (se 2 (by rfl) ⟨853737, by rfl⟩ : syracuseStep 2276633 = 1707475) B1707475
theorem B3595571 : Blo 1596997 3595571 := bstep (se 1 (by rfl) ⟨2696678, by rfl⟩ : syracuseStep 3595571 = 5393357) B5393357
theorem B3595607 : Blo 1596997 3595607 := bstep (se 1 (by rfl) ⟨2696705, by rfl⟩ : syracuseStep 3595607 = 5393411) B5393411
theorem B2497879 : Blo 1596997 2497879 := bstep (se 1 (by rfl) ⟨1873409, by rfl⟩ : syracuseStep 2497879 = 3746819) B3746819
theorem B6069593 : Blo 1596997 6069593 := bstep (se 2 (by rfl) ⟨2276097, by rfl⟩ : syracuseStep 6069593 = 4552195) B4552195
theorem B3595787 : Blo 1596997 3595787 := bstep (se 1 (by rfl) ⟨2696840, by rfl⟩ : syracuseStep 3595787 = 5393681) B5393681
theorem B12959297 : Blo 1596997 12959297 := bstep (se 2 (by rfl) ⟨4859736, by rfl⟩ : syracuseStep 12959297 = 9719473) B9719473
theorem B3595841 : Blo 1596997 3595841 := bstep (se 2 (by rfl) ⟨1348440, by rfl⟩ : syracuseStep 3595841 = 2696881) B2696881
theorem B1597003 : Blo 1596997 1597003 := bstep (se 1 (by rfl) ⟨1197752, by rfl⟩ : syracuseStep 1597003 = 2395505) B2395505
theorem B1597015 : Blo 1596997 1597015 := bstep (se 1 (by rfl) ⟨1197761, by rfl⟩ : syracuseStep 1597015 = 2395523) B2395523
theorem B1597035 : Blo 1596997 1597035 := bstep (se 1 (by rfl) ⟨1197776, by rfl⟩ : syracuseStep 1597035 = 2395553) B2395553
theorem B1597047 : Blo 1596997 1597047 := bstep (se 1 (by rfl) ⟨1197785, by rfl⟩ : syracuseStep 1597047 = 2395571) B2395571
theorem B1597067 : Blo 1596997 1597067 := bstep (se 1 (by rfl) ⟨1197800, by rfl⟩ : syracuseStep 1597067 = 2395601) B2395601
theorem B2023051 : Blo 1596997 2023051 := bstep (se 1 (by rfl) ⟨1517288, by rfl⟩ : syracuseStep 2023051 = 3034577) B3034577
theorem B1597079 : Blo 1596997 1597079 := bstep (se 1 (by rfl) ⟨1197809, by rfl⟩ : syracuseStep 1597079 = 2395619) B2395619
theorem B1597099 : Blo 1596997 1597099 := bstep (se 1 (by rfl) ⟨1197824, by rfl⟩ : syracuseStep 1597099 = 2395649) B2395649
theorem B12132017 : Blo 1596997 12132017 := bstep (se 2 (by rfl) ⟨4549506, by rfl⟩ : syracuseStep 12132017 = 9099013) B9099013
theorem B1597111 : Blo 1596997 1597111 := bstep (se 1 (by rfl) ⟨1197833, by rfl⟩ : syracuseStep 1597111 = 2395667) B2395667
theorem B1597131 : Blo 1596997 1597131 := bstep (se 1 (by rfl) ⟨1197848, by rfl⟩ : syracuseStep 1597131 = 2395697) B2395697
theorem B1597143 : Blo 1596997 1597143 := bstep (se 1 (by rfl) ⟨1197857, by rfl⟩ : syracuseStep 1597143 = 2395715) B2395715
theorem B1597163 : Blo 1596997 1597163 := bstep (se 1 (by rfl) ⟨1197872, by rfl⟩ : syracuseStep 1597163 = 2395745) B2395745
theorem B1597175 : Blo 1596997 1597175 := bstep (se 1 (by rfl) ⟨1197881, by rfl⟩ : syracuseStep 1597175 = 2395763) B2395763
theorem B1597195 : Blo 1596997 1597195 := bstep (se 1 (by rfl) ⟨1197896, by rfl⟩ : syracuseStep 1597195 = 2395793) B2395793
theorem B1597207 : Blo 1596997 1597207 := bstep (se 1 (by rfl) ⟨1197905, by rfl⟩ : syracuseStep 1597207 = 2395811) B2395811
theorem B2694937 : Blo 1596997 2694937 := bstep (se 2 (by rfl) ⟨1010601, by rfl⟩ : syracuseStep 2694937 = 2021203) B2021203
theorem B3596057 : Blo 1596997 3596057 := bstep (se 2 (by rfl) ⟨1348521, by rfl⟩ : syracuseStep 3596057 = 2697043) B2697043
theorem B12304163 : Blo 1596997 12304163 := bstep (se 1 (by rfl) ⟨9228122, by rfl⟩ : syracuseStep 12304163 = 18456245) B18456245
theorem B1597227 : Blo 1596997 1597227 := bstep (se 1 (by rfl) ⟨1197920, by rfl⟩ : syracuseStep 1597227 = 2395841) B2395841
theorem B1597239 : Blo 1596997 1597239 := bstep (se 1 (by rfl) ⟨1197929, by rfl⟩ : syracuseStep 1597239 = 2395859) B2395859
theorem B1597259 : Blo 1596997 1597259 := bstep (se 1 (by rfl) ⟨1197944, by rfl⟩ : syracuseStep 1597259 = 2395889) B2395889
theorem B1597271 : Blo 1596997 1597271 := bstep (se 1 (by rfl) ⟨1197953, by rfl⟩ : syracuseStep 1597271 = 2395907) B2395907
theorem B1597291 : Blo 1596997 1597291 := bstep (se 1 (by rfl) ⟨1197968, by rfl⟩ : syracuseStep 1597291 = 2395937) B2395937
theorem B3596147 : Blo 1596997 3596147 := bstep (se 1 (by rfl) ⟨2697110, by rfl⟩ : syracuseStep 3596147 = 5394221) B5394221
theorem B1597303 : Blo 1596997 1597303 := bstep (se 1 (by rfl) ⟨1197977, by rfl⟩ : syracuseStep 1597303 = 2395955) B2395955
theorem B1597323 : Blo 1596997 1597323 := bstep (se 1 (by rfl) ⟨1197992, by rfl⟩ : syracuseStep 1597323 = 2395985) B2395985
theorem B1597335 : Blo 1596997 1597335 := bstep (se 1 (by rfl) ⟨1198001, by rfl⟩ : syracuseStep 1597335 = 2396003) B2396003
theorem B3596183 : Blo 1596997 3596183 := bstep (se 1 (by rfl) ⟨2697137, by rfl⟩ : syracuseStep 3596183 = 5394275) B5394275
theorem B2023319 : Blo 1596997 2023319 := bstep (se 1 (by rfl) ⟨1517489, by rfl⟩ : syracuseStep 2023319 = 3034979) B3034979
theorem B1597355 : Blo 1596997 1597355 := bstep (se 1 (by rfl) ⟨1198016, by rfl⟩ : syracuseStep 1597355 = 2396033) B2396033
theorem B9723827 : Blo 1596997 9723827 := bstep (se 1 (by rfl) ⟨7292870, by rfl⟩ : syracuseStep 9723827 = 14585741) B14585741
theorem B1597367 : Blo 1596997 1597367 := bstep (se 1 (by rfl) ⟨1198025, by rfl⟩ : syracuseStep 1597367 = 2396051) B2396051
theorem B1597387 : Blo 1596997 1597387 := bstep (se 1 (by rfl) ⟨1198040, by rfl⟩ : syracuseStep 1597387 = 2396081) B2396081
theorem B4857803 : Blo 1596997 4857803 := bstep (se 1 (by rfl) ⟨3643352, by rfl⟩ : syracuseStep 4857803 = 7286705) B7286705
theorem B1597399 : Blo 1596997 1597399 := bstep (se 1 (by rfl) ⟨1198049, by rfl⟩ : syracuseStep 1597399 = 2396099) B2396099
theorem B6922205 : Blo 1596997 6922205 := bstep (se 3 (by rfl) ⟨1297913, by rfl⟩ : syracuseStep 6922205 = 2595827) B2595827
theorem B1597419 : Blo 1596997 1597419 := bstep (se 1 (by rfl) ⟨1198064, by rfl⟩ : syracuseStep 1597419 = 2396129) B2396129
theorem B1597431 : Blo 1596997 1597431 := bstep (se 1 (by rfl) ⟨1198073, by rfl⟩ : syracuseStep 1597431 = 2396147) B2396147
theorem B1597447 : Blo 1596997 1597447 := bstep (se 1 (by rfl) ⟨1198085, by rfl⟩ : syracuseStep 1597447 = 2396171) B2396171
theorem B1597455 : Blo 1596997 1597455 := bstep (se 1 (by rfl) ⟨1198091, by rfl⟩ : syracuseStep 1597455 = 2396183) B2396183
theorem B4046881 : Blo 1596997 4046881 := bstep (se 2 (by rfl) ⟨1517580, by rfl⟩ : syracuseStep 4046881 = 3035161) B3035161
theorem B1597499 : Blo 1596997 1597499 := bstep (se 1 (by rfl) ⟨1198124, by rfl⟩ : syracuseStep 1597499 = 2396249) B2396249
theorem B1597575 : Blo 1596997 1597575 := bstep (se 1 (by rfl) ⟨1198181, by rfl⟩ : syracuseStep 1597575 = 2396363) B2396363
theorem B1597583 : Blo 1596997 1597583 := bstep (se 1 (by rfl) ⟨1198187, by rfl⟩ : syracuseStep 1597583 = 2396375) B2396375
theorem B3596435 : Blo 1596997 3596435 := bstep (se 1 (by rfl) ⟨2697326, by rfl⟩ : syracuseStep 3596435 = 5394653) B5394653
theorem B1597627 : Blo 1596997 1597627 := bstep (se 1 (by rfl) ⟨1198220, by rfl⟩ : syracuseStep 1597627 = 2396441) B2396441
theorem B2695369 : Blo 1596997 2695369 := bstep (se 2 (by rfl) ⟨1010763, by rfl⟩ : syracuseStep 2695369 = 2021527) B2021527
theorem B3596489 : Blo 1596997 3596489 := bstep (se 2 (by rfl) ⟨1348683, by rfl⟩ : syracuseStep 3596489 = 2697367) B2697367
theorem B1597703 : Blo 1596997 1597703 := bstep (se 1 (by rfl) ⟨1198277, by rfl⟩ : syracuseStep 1597703 = 2396555) B2396555
theorem B1597711 : Blo 1596997 1597711 := bstep (se 1 (by rfl) ⟨1198283, by rfl⟩ : syracuseStep 1597711 = 2396567) B2396567
theorem B1597755 : Blo 1596997 1597755 := bstep (se 1 (by rfl) ⟨1198316, by rfl⟩ : syracuseStep 1597755 = 2396633) B2396633
theorem B1597831 : Blo 1596997 1597831 := bstep (se 1 (by rfl) ⟨1198373, by rfl⟩ : syracuseStep 1597831 = 2396747) B2396747
theorem B1597839 : Blo 1596997 1597839 := bstep (se 1 (by rfl) ⟨1198379, by rfl⟩ : syracuseStep 1597839 = 2396759) B2396759
theorem B8085905 : Blo 1596997 8085905 := bstep (se 2 (by rfl) ⟨3032214, by rfl⟩ : syracuseStep 8085905 = 6064429) B6064429
theorem B1597883 : Blo 1596997 1597883 := bstep (se 1 (by rfl) ⟨1198412, by rfl⟩ : syracuseStep 1597883 = 2396825) B2396825
theorem B1597959 : Blo 1596997 1597959 := bstep (se 1 (by rfl) ⟨1198469, by rfl⟩ : syracuseStep 1597959 = 2396939) B2396939
theorem B1597967 : Blo 1596997 1597967 := bstep (se 1 (by rfl) ⟨1198475, by rfl⟩ : syracuseStep 1597967 = 2396951) B2396951
theorem B1598011 : Blo 1596997 1598011 := bstep (se 1 (by rfl) ⟨1198508, by rfl⟩ : syracuseStep 1598011 = 2397017) B2397017
theorem B1598087 : Blo 1596997 1598087 := bstep (se 1 (by rfl) ⟨1198565, by rfl⟩ : syracuseStep 1598087 = 2397131) B2397131
theorem B1598095 : Blo 1596997 1598095 := bstep (se 1 (by rfl) ⟨1198571, by rfl⟩ : syracuseStep 1598095 = 2397143) B2397143
theorem B1598139 : Blo 1596997 1598139 := bstep (se 1 (by rfl) ⟨1198604, by rfl⟩ : syracuseStep 1598139 = 2397209) B2397209
theorem B6071021 : Blo 1596997 6071021 := bstep (se 3 (by rfl) ⟨1138316, by rfl⟩ : syracuseStep 6071021 = 2276633) B2276633
theorem B1598215 : Blo 1596997 1598215 := bstep (se 1 (by rfl) ⟨1198661, by rfl⟩ : syracuseStep 1598215 = 2397323) B2397323
theorem B1598223 : Blo 1596997 1598223 := bstep (se 1 (by rfl) ⟨1198667, by rfl⟩ : syracuseStep 1598223 = 2397335) B2397335
theorem B1598267 : Blo 1596997 1598267 := bstep (se 1 (by rfl) ⟨1198700, by rfl⟩ : syracuseStep 1598267 = 2397401) B2397401
theorem B2696071 : Blo 1596997 2696071 := bstep (se 1 (by rfl) ⟨2022053, by rfl⟩ : syracuseStep 2696071 = 4044107) B4044107
theorem B1598343 : Blo 1596997 1598343 := bstep (se 1 (by rfl) ⟨1198757, by rfl⟩ : syracuseStep 1598343 = 2397515) B2397515
theorem B3597191 : Blo 1596997 3597191 := bstep (se 1 (by rfl) ⟨2697893, by rfl⟩ : syracuseStep 3597191 = 5395787) B5395787
theorem B1598351 : Blo 1596997 1598351 := bstep (se 1 (by rfl) ⟨1198763, by rfl⟩ : syracuseStep 1598351 = 2397527) B2397527
theorem B5391251 : Blo 1596997 5391251 := bstep (se 1 (by rfl) ⟨4043438, by rfl⟩ : syracuseStep 5391251 = 8086877) B8086877
theorem B13656995 : Blo 1596997 13656995 := bstep (se 1 (by rfl) ⟨10242746, by rfl⟩ : syracuseStep 13656995 = 20485493) B20485493
theorem B1598395 : Blo 1596997 1598395 := bstep (se 1 (by rfl) ⟨1198796, by rfl⟩ : syracuseStep 1598395 = 2397593) B2397593
theorem B1598471 : Blo 1596997 1598471 := bstep (se 1 (by rfl) ⟨1198853, by rfl⟩ : syracuseStep 1598471 = 2397707) B2397707
theorem B1598479 : Blo 1596997 1598479 := bstep (se 1 (by rfl) ⟨1198859, by rfl⟩ : syracuseStep 1598479 = 2397719) B2397719
theorem B1598523 : Blo 1596997 1598523 := bstep (se 1 (by rfl) ⟨1198892, by rfl⟩ : syracuseStep 1598523 = 2397785) B2397785
theorem B3597371 : Blo 1596997 3597371 := bstep (se 1 (by rfl) ⟨2698028, by rfl⟩ : syracuseStep 3597371 = 5396057) B5396057
theorem B9102455 : Blo 1596997 9102455 := bstep (se 1 (by rfl) ⟨6826841, by rfl⟩ : syracuseStep 9102455 = 13653683) B13653683
theorem B18457733 : Blo 1596997 18457733 := bstep (se 4 (by rfl) ⟨1730412, by rfl⟩ : syracuseStep 18457733 = 3460825) B3460825
theorem B1598599 : Blo 1596997 1598599 := bstep (se 1 (by rfl) ⟨1198949, by rfl⟩ : syracuseStep 1598599 = 2397899) B2397899
theorem B1598607 : Blo 1596997 1598607 := bstep (se 1 (by rfl) ⟨1198955, by rfl⟩ : syracuseStep 1598607 = 2397911) B2397911
theorem B3597497 : Blo 1596997 3597497 := bstep (se 2 (by rfl) ⟨1349061, by rfl⟩ : syracuseStep 3597497 = 2698123) B2698123
theorem B1598651 : Blo 1596997 1598651 := bstep (se 1 (by rfl) ⟨1198988, by rfl⟩ : syracuseStep 1598651 = 2397977) B2397977
theorem B6825217 : Blo 1596997 6825217 := bstep (se 2 (by rfl) ⟨2559456, by rfl⟩ : syracuseStep 6825217 = 5118913) B5118913
theorem B1598727 : Blo 1596997 1598727 := bstep (se 1 (by rfl) ⟨1199045, by rfl⟩ : syracuseStep 1598727 = 2398091) B2398091
theorem B4375819 : Blo 1596997 4375819 := bstep (se 1 (by rfl) ⟨3281864, by rfl⟩ : syracuseStep 4375819 = 6563729) B6563729
theorem B1598735 : Blo 1596997 1598735 := bstep (se 1 (by rfl) ⟨1199051, by rfl⟩ : syracuseStep 1598735 = 2398103) B2398103
theorem B4859165 : Blo 1596997 4859165 := bstep (se 3 (by rfl) ⟨911093, by rfl⟩ : syracuseStep 4859165 = 1822187) B1822187
theorem B3073339 : Blo 1596997 3073339 := bstep (se 1 (by rfl) ⟨2305004, by rfl⟩ : syracuseStep 3073339 = 4610009) B4610009
theorem B1598779 : Blo 1596997 1598779 := bstep (se 1 (by rfl) ⟨1199084, by rfl⟩ : syracuseStep 1598779 = 2398169) B2398169
theorem B1598855 : Blo 1596997 1598855 := bstep (se 1 (by rfl) ⟨1199141, by rfl⟩ : syracuseStep 1598855 = 2398283) B2398283
theorem B1598863 : Blo 1596997 1598863 := bstep (se 1 (by rfl) ⟨1199147, by rfl⟩ : syracuseStep 1598863 = 2398295) B2398295
theorem B41502131 : Blo 1596997 41502131 := bstep (se 1 (by rfl) ⟨31126598, by rfl⟩ : syracuseStep 41502131 = 62253197) B62253197
theorem B1598907 : Blo 1596997 1598907 := bstep (se 1 (by rfl) ⟨1199180, by rfl⟩ : syracuseStep 1598907 = 2398361) B2398361
theorem B1598983 : Blo 1596997 1598983 := bstep (se 1 (by rfl) ⟨1199237, by rfl⟩ : syracuseStep 1598983 = 2398475) B2398475
theorem B2696719 : Blo 1596997 2696719 := bstep (se 1 (by rfl) ⟨2022539, by rfl⟩ : syracuseStep 2696719 = 4045079) B4045079
theorem B1598991 : Blo 1596997 1598991 := bstep (se 1 (by rfl) ⟨1199243, by rfl⟩ : syracuseStep 1598991 = 2398487) B2398487
theorem B6825559 : Blo 1596997 6825559 := bstep (se 1 (by rfl) ⟨5119169, by rfl⟩ : syracuseStep 6825559 = 10238339) B10238339
theorem B3032777 : Blo 1596997 3032777 := bstep (se 2 (by rfl) ⟨1137291, by rfl⟩ : syracuseStep 3032777 = 2274583) B2274583
theorem B4548413 : Blo 1596997 4548413 := bstep (se 3 (by rfl) ⟨852827, by rfl⟩ : syracuseStep 4548413 = 1705655) B1705655
theorem B2697259 : Blo 1596997 2697259 := bstep (se 1 (by rfl) ⟨2022944, by rfl⟩ : syracuseStep 2697259 = 4045889) B4045889
theorem B5122091 : Blo 1596997 5122091 := bstep (se 1 (by rfl) ⟨3841568, by rfl⟩ : syracuseStep 5122091 = 7683137) B7683137
theorem B32811101 : Blo 1596997 32811101 := bstep (se 3 (by rfl) ⟨6152081, by rfl⟩ : syracuseStep 32811101 = 12304163) B12304163
theorem B6064247 : Blo 1596997 6064247 := bstep (se 1 (by rfl) ⟨4548185, by rfl⟩ : syracuseStep 6064247 = 9096371) B9096371
theorem B3074195 : Blo 1596997 3074195 := bstep (se 1 (by rfl) ⟨2305646, by rfl⟩ : syracuseStep 3074195 = 4611293) B4611293
theorem B2558137 : Blo 1596997 2558137 := bstep (se 2 (by rfl) ⟨959301, by rfl⟩ : syracuseStep 2558137 = 1918603) B1918603
theorem B2697401 : Blo 1596997 2697401 := bstep (se 2 (by rfl) ⟨1011525, by rfl⟩ : syracuseStep 2697401 = 2023051) B2023051
theorem B5392655 : Blo 1596997 5392655 := bstep (se 1 (by rfl) ⟨4044491, by rfl⟩ : syracuseStep 5392655 = 8088983) B8088983
theorem B14780819 : Blo 1596997 14780819 := bstep (se 1 (by rfl) ⟨11085614, by rfl⟩ : syracuseStep 14780819 = 22171229) B22171229
theorem B8088011 : Blo 1596997 8088011 := bstep (se 1 (by rfl) ⟨6066008, by rfl⟩ : syracuseStep 8088011 = 12132017) B12132017
theorem B5392925 : Blo 1596997 5392925 := bstep (se 3 (by rfl) ⟨1011173, by rfl⟩ : syracuseStep 5392925 = 2022347) B2022347
theorem B6482551 : Blo 1596997 6482551 := bstep (se 1 (by rfl) ⟨4861913, by rfl⟩ : syracuseStep 6482551 = 9723827) B9723827
theorem B3238535 : Blo 1596997 3238535 := bstep (se 1 (by rfl) ⟨2428901, by rfl⟩ : syracuseStep 3238535 = 4857803) B4857803
theorem B4614803 : Blo 1596997 4614803 := bstep (se 1 (by rfl) ⟨3461102, by rfl⟩ : syracuseStep 4614803 = 6922205) B6922205
theorem B8088335 : Blo 1596997 8088335 := bstep (se 1 (by rfl) ⟨6066251, by rfl⟩ : syracuseStep 8088335 = 12132503) B12132503
theorem B4549405 : Blo 1596997 4549405 := bstep (se 3 (by rfl) ⟨853013, by rfl⟩ : syracuseStep 4549405 = 1706027) B1706027
theorem B16395043 : Blo 1596997 16395043 := bstep (se 1 (by rfl) ⟨12296282, by rfl⟩ : syracuseStep 16395043 = 24592565) B24592565
theorem B19434275 : Blo 1596997 19434275 := bstep (se 1 (by rfl) ⟨14575706, by rfl⟩ : syracuseStep 19434275 = 29151413) B29151413
theorem B18197297 : Blo 1596997 18197297 := bstep (se 2 (by rfl) ⟨6823986, by rfl⟩ : syracuseStep 18197297 = 13647973) B13647973
theorem B15362891 : Blo 1596997 15362891 := bstep (se 1 (by rfl) ⟨11522168, by rfl⟩ : syracuseStep 15362891 = 23044337) B23044337
theorem B2698103 : Blo 1596997 2698103 := bstep (se 1 (by rfl) ⟨2023577, by rfl⟩ : syracuseStep 2698103 = 4047155) B4047155
theorem B1797007 : Blo 1596997 1797007 := bstep (se 1 (by rfl) ⟨1347755, by rfl⟩ : syracuseStep 1797007 = 2695511) B2695511
theorem B17288099 : Blo 1596997 17288099 := bstep (se 1 (by rfl) ⟨12966074, by rfl⟩ : syracuseStep 17288099 = 25932149) B25932149
theorem B31124405 : Blo 1596997 31124405 := bstep (se 5 (by rfl) ⟨1458956, by rfl⟩ : syracuseStep 31124405 = 2917913) B2917913
theorem B2878409 : Blo 1596997 2878409 := bstep (se 2 (by rfl) ⟨1079403, by rfl⟩ : syracuseStep 2878409 = 2158807) B2158807
theorem B6065219 : Blo 1596997 6065219 := bstep (se 1 (by rfl) ⟨4548914, by rfl⟩ : syracuseStep 6065219 = 9097829) B9097829
theorem B7679063 : Blo 1596997 7679063 := bstep (se 1 (by rfl) ⟨5759297, by rfl⟩ : syracuseStep 7679063 = 11518595) B11518595
theorem B15355169 : Blo 1596997 15355169 := bstep (se 2 (by rfl) ⟨5758188, by rfl⟩ : syracuseStep 15355169 = 11516377) B11516377
theorem B10243361 : Blo 1596997 10243361 := bstep (se 2 (by rfl) ⟨3841260, by rfl⟩ : syracuseStep 10243361 = 7682521) B7682521
theorem B18206045 : Blo 1596997 18206045 := bstep (se 3 (by rfl) ⟨3413633, by rfl⟩ : syracuseStep 18206045 = 6827267) B6827267
theorem B2395511 : Blo 1596997 2395511 := bstep (se 1 (by rfl) ⟨1796633, by rfl⟩ : syracuseStep 2395511 = 3593267) B3593267
theorem B1797511 : Blo 1596997 1797511 := bstep (se 1 (by rfl) ⟨1348133, by rfl⟩ : syracuseStep 1797511 = 2696267) B2696267
theorem B2559367 : Blo 1596997 2559367 := bstep (se 1 (by rfl) ⟨1919525, by rfl⟩ : syracuseStep 2559367 = 3839051) B3839051
theorem B2395535 : Blo 1596997 2395535 := bstep (se 1 (by rfl) ⟨1796651, by rfl⟩ : syracuseStep 2395535 = 3593303) B3593303
theorem B3837331 : Blo 1596997 3837331 := bstep (se 1 (by rfl) ⟨2877998, by rfl⟩ : syracuseStep 3837331 = 5755997) B5755997
theorem B2395577 : Blo 1596997 2395577 := bstep (se 2 (by rfl) ⟨898341, by rfl⟩ : syracuseStep 2395577 = 1796683) B1796683
theorem B30715321 : Blo 1596997 30715321 := bstep (se 2 (by rfl) ⟨11518245, by rfl⟩ : syracuseStep 30715321 = 23036491) B23036491
theorem B9719299 : Blo 1596997 9719299 := bstep (se 1 (by rfl) ⟨7289474, by rfl⟩ : syracuseStep 9719299 = 14578949) B14578949
theorem B2395655 : Blo 1596997 2395655 := bstep (se 1 (by rfl) ⟨1796741, by rfl⟩ : syracuseStep 2395655 = 3593483) B3593483
theorem B6065675 : Blo 1596997 6065675 := bstep (se 1 (by rfl) ⟨4549256, by rfl⟩ : syracuseStep 6065675 = 9098513) B9098513
theorem B2395691 : Blo 1596997 2395691 := bstep (se 1 (by rfl) ⟨1796768, by rfl⟩ : syracuseStep 2395691 = 3593537) B3593537
theorem B3411515 : Blo 1596997 3411515 := bstep (se 1 (by rfl) ⟨2558636, by rfl⟩ : syracuseStep 3411515 = 5117273) B5117273
theorem B1797691 : Blo 1596997 1797691 := bstep (se 1 (by rfl) ⟨1348268, by rfl⟩ : syracuseStep 1797691 = 2696537) B2696537
theorem B6655549 : Blo 1596997 6655549 := bstep (se 3 (by rfl) ⟨1247915, by rfl⟩ : syracuseStep 6655549 = 2495831) B2495831
theorem B2395721 : Blo 1596997 2395721 := bstep (se 2 (by rfl) ⟨898395, by rfl⟩ : syracuseStep 2395721 = 1796791) B1796791
theorem B3034759 : Blo 1596997 3034759 := bstep (se 1 (by rfl) ⟨2276069, by rfl⟩ : syracuseStep 3034759 = 4552139) B4552139
theorem B2395835 : Blo 1596997 2395835 := bstep (se 1 (by rfl) ⟨1796876, by rfl⟩ : syracuseStep 2395835 = 3593753) B3593753
theorem B2395895 : Blo 1596997 2395895 := bstep (se 1 (by rfl) ⟨1796921, by rfl⟩ : syracuseStep 2395895 = 3593843) B3593843
theorem B18452225 : Blo 1596997 18452225 := bstep (se 2 (by rfl) ⟨6919584, by rfl⟩ : syracuseStep 18452225 = 13839169) B13839169
theorem B4042507 : Blo 1596997 4042507 := bstep (se 1 (by rfl) ⟨3031880, by rfl⟩ : syracuseStep 4042507 = 6063761) B6063761
theorem B2395919 : Blo 1596997 2395919 := bstep (se 1 (by rfl) ⟨1796939, by rfl⟩ : syracuseStep 2395919 = 3593879) B3593879
theorem B17755919 : Blo 1596997 17755919 := bstep (se 1 (by rfl) ⟨13316939, by rfl⟩ : syracuseStep 17755919 = 26633879) B26633879
theorem B6917921 : Blo 1596997 6917921 := bstep (se 2 (by rfl) ⟨2594220, by rfl⟩ : syracuseStep 6917921 = 5188441) B5188441
theorem B2395961 : Blo 1596997 2395961 := bstep (se 2 (by rfl) ⟨898485, by rfl⟩ : syracuseStep 2395961 = 1796971) B1796971
theorem B2396039 : Blo 1596997 2396039 := bstep (se 1 (by rfl) ⟨1797029, by rfl⟩ : syracuseStep 2396039 = 3594059) B3594059
theorem B4042649 : Blo 1596997 4042649 := bstep (se 2 (by rfl) ⟨1515993, by rfl⟩ : syracuseStep 4042649 = 3031987) B3031987
theorem B5394329 : Blo 1596997 5394329 := bstep (se 2 (by rfl) ⟨2022873, by rfl⟩ : syracuseStep 5394329 = 4045747) B4045747
theorem B2396075 : Blo 1596997 2396075 := bstep (se 1 (by rfl) ⟨1797056, by rfl⟩ : syracuseStep 2396075 = 3594113) B3594113
theorem B2396105 : Blo 1596997 2396105 := bstep (se 2 (by rfl) ⟨898539, by rfl⟩ : syracuseStep 2396105 = 1797079) B1797079
theorem B7679947 : Blo 1596997 7679947 := bstep (se 1 (by rfl) ⟨5759960, by rfl⟩ : syracuseStep 7679947 = 11519921) B11519921
theorem B8196061 : Blo 1596997 8196061 := bstep (se 3 (by rfl) ⟨1536761, by rfl⟩ : syracuseStep 8196061 = 3073523) B3073523
theorem B2560015 : Blo 1596997 2560015 := bstep (se 1 (by rfl) ⟨1920011, by rfl⟩ : syracuseStep 2560015 = 3840023) B3840023
theorem B1798159 : Blo 1596997 1798159 := bstep (se 1 (by rfl) ⟨1348619, by rfl⟩ : syracuseStep 1798159 = 2697239) B2697239
theorem B4042811 : Blo 1596997 4042811 := bstep (se 1 (by rfl) ⟨3032108, by rfl⟩ : syracuseStep 4042811 = 6064217) B6064217
theorem B2396219 : Blo 1596997 2396219 := bstep (se 1 (by rfl) ⟨1797164, by rfl⟩ : syracuseStep 2396219 = 3594329) B3594329
theorem B2396279 : Blo 1596997 2396279 := bstep (se 1 (by rfl) ⟨1797209, by rfl⟩ : syracuseStep 2396279 = 3594419) B3594419
theorem B2396303 : Blo 1596997 2396303 := bstep (se 1 (by rfl) ⟨1797227, by rfl⟩ : syracuseStep 2396303 = 3594455) B3594455
theorem B2396345 : Blo 1596997 2396345 := bstep (se 2 (by rfl) ⟨898629, by rfl⟩ : syracuseStep 2396345 = 1797259) B1797259
theorem B8089793 : Blo 1596997 8089793 := bstep (se 2 (by rfl) ⟨3033672, by rfl⟩ : syracuseStep 8089793 = 6067345) B6067345
theorem B2396423 : Blo 1596997 2396423 := bstep (se 1 (by rfl) ⟨1797317, by rfl⟩ : syracuseStep 2396423 = 3594635) B3594635
theorem B2396459 : Blo 1596997 2396459 := bstep (se 1 (by rfl) ⟨1797344, by rfl⟩ : syracuseStep 2396459 = 3594689) B3594689
theorem B2396489 : Blo 1596997 2396489 := bstep (se 2 (by rfl) ⟨898683, by rfl⟩ : syracuseStep 2396489 = 1797367) B1797367
theorem B4043155 : Blo 1596997 4043155 := bstep (se 1 (by rfl) ⟨3032366, by rfl⟩ : syracuseStep 4043155 = 6064733) B6064733
theorem B2396603 : Blo 1596997 2396603 := bstep (se 1 (by rfl) ⟨1797452, by rfl⟩ : syracuseStep 2396603 = 3594905) B3594905
theorem B3330505 : Blo 1596997 3330505 := bstep (se 2 (by rfl) ⟨1248939, by rfl⟩ : syracuseStep 3330505 = 2497879) B2497879
theorem B2396663 : Blo 1596997 2396663 := bstep (se 1 (by rfl) ⟨1797497, by rfl⟩ : syracuseStep 2396663 = 3594995) B3594995
theorem B1798663 : Blo 1596997 1798663 := bstep (se 1 (by rfl) ⟨1348997, by rfl⟩ : syracuseStep 1798663 = 2697995) B2697995
theorem B2396687 : Blo 1596997 2396687 := bstep (se 1 (by rfl) ⟨1797515, by rfl⟩ : syracuseStep 2396687 = 3595031) B3595031
theorem B4043297 : Blo 1596997 4043297 := bstep (se 2 (by rfl) ⟨1516236, by rfl⟩ : syracuseStep 4043297 = 3032473) B3032473
theorem B3240481 : Blo 1596997 3240481 := bstep (se 2 (by rfl) ⟨1215180, by rfl⟩ : syracuseStep 3240481 = 2430361) B2430361
theorem B2396729 : Blo 1596997 2396729 := bstep (se 2 (by rfl) ⟨898773, by rfl⟩ : syracuseStep 2396729 = 1797547) B1797547
theorem B27669059 : Blo 1596997 27669059 := bstep (se 1 (by rfl) ⟨20751794, by rfl⟩ : syracuseStep 27669059 = 41503589) B41503589
theorem B5395031 : Blo 1596997 5395031 := bstep (se 1 (by rfl) ⟨4046273, by rfl⟩ : syracuseStep 5395031 = 8092547) B8092547
theorem B2396807 : Blo 1596997 2396807 := bstep (se 1 (by rfl) ⟨1797605, by rfl⟩ : syracuseStep 2396807 = 3595211) B3595211
theorem B2396843 : Blo 1596997 2396843 := bstep (se 1 (by rfl) ⟨1797632, by rfl⟩ : syracuseStep 2396843 = 3595265) B3595265
theorem B4551353 : Blo 1596997 4551353 := bstep (se 2 (by rfl) ⟨1706757, by rfl⟩ : syracuseStep 4551353 = 3413515) B3413515
theorem B1798843 : Blo 1596997 1798843 := bstep (se 1 (by rfl) ⟨1349132, by rfl⟩ : syracuseStep 1798843 = 2698265) B2698265
theorem B2396873 : Blo 1596997 2396873 := bstep (se 2 (by rfl) ⟨898827, by rfl⟩ : syracuseStep 2396873 = 1797655) B1797655
theorem B9106121 : Blo 1596997 9106121 := bstep (se 2 (by rfl) ⟨3414795, by rfl⟩ : syracuseStep 9106121 = 6829591) B6829591
theorem B6566657 : Blo 1596997 6566657 := bstep (se 2 (by rfl) ⟨2462496, by rfl⟩ : syracuseStep 6566657 = 4924993) B4924993
theorem B18207503 : Blo 1596997 18207503 := bstep (se 1 (by rfl) ⟨13655627, by rfl⟩ : syracuseStep 18207503 = 27311255) B27311255
theorem B2732843 : Blo 1596997 2732843 := bstep (se 1 (by rfl) ⟨2049632, by rfl⟩ : syracuseStep 2732843 = 4099265) B4099265
theorem B2396987 : Blo 1596997 2396987 := bstep (se 1 (by rfl) ⟨1797740, by rfl⟩ : syracuseStep 2396987 = 3595481) B3595481
theorem B2397047 : Blo 1596997 2397047 := bstep (se 1 (by rfl) ⟨1797785, by rfl⟩ : syracuseStep 2397047 = 3595571) B3595571
theorem B2397071 : Blo 1596997 2397071 := bstep (se 1 (by rfl) ⟨1797803, by rfl⟩ : syracuseStep 2397071 = 3595607) B3595607
theorem B6656921 : Blo 1596997 6656921 := bstep (se 2 (by rfl) ⟨2496345, by rfl⟩ : syracuseStep 6656921 = 4992691) B4992691
theorem B2397113 : Blo 1596997 2397113 := bstep (se 2 (by rfl) ⟨898917, by rfl⟩ : syracuseStep 2397113 = 1797835) B1797835
theorem B2397191 : Blo 1596997 2397191 := bstep (se 1 (by rfl) ⟨1797893, by rfl⟩ : syracuseStep 2397191 = 3595787) B3595787
theorem B3593249 : Blo 1596997 3593249 := bstep (se 2 (by rfl) ⟨1347468, by rfl⟩ : syracuseStep 3593249 = 2694937) B2694937
theorem B8639531 : Blo 1596997 8639531 := bstep (se 1 (by rfl) ⟨6479648, by rfl⟩ : syracuseStep 8639531 = 12959297) B12959297
theorem B2397227 : Blo 1596997 2397227 := bstep (se 1 (by rfl) ⟨1797920, by rfl⟩ : syracuseStep 2397227 = 3595841) B3595841
theorem B5395517 : Blo 1596997 5395517 := bstep (se 3 (by rfl) ⟨1011659, by rfl⟩ : syracuseStep 5395517 = 2023319) B2023319
theorem B2397257 : Blo 1596997 2397257 := bstep (se 2 (by rfl) ⟨898971, by rfl⟩ : syracuseStep 2397257 = 1797943) B1797943
theorem B2274475 : Blo 1596997 2274475 := bstep (se 1 (by rfl) ⟨1705856, by rfl⟩ : syracuseStep 2274475 = 3411713) B3411713
theorem B2397371 : Blo 1596997 2397371 := bstep (se 1 (by rfl) ⟨1798028, by rfl⟩ : syracuseStep 2397371 = 3596057) B3596057
theorem B3839177 : Blo 1596997 3839177 := bstep (se 2 (by rfl) ⟨1439691, by rfl⟩ : syracuseStep 3839177 = 2879383) B2879383
theorem B2561225 : Blo 1596997 2561225 := bstep (se 2 (by rfl) ⟨960459, by rfl⟩ : syracuseStep 2561225 = 1920919) B1920919
theorem B20747501 : Blo 1596997 20747501 := bstep (se 3 (by rfl) ⟨3890156, by rfl⟩ : syracuseStep 20747501 = 7780313) B7780313
theorem B2397431 : Blo 1596997 2397431 := bstep (se 1 (by rfl) ⟨1798073, by rfl⟩ : syracuseStep 2397431 = 3596147) B3596147
theorem B2397455 : Blo 1596997 2397455 := bstep (se 1 (by rfl) ⟨1798091, by rfl⟩ : syracuseStep 2397455 = 3596183) B3596183
theorem B2397497 : Blo 1596997 2397497 := bstep (se 2 (by rfl) ⟨899061, by rfl⟩ : syracuseStep 2397497 = 1798123) B1798123
theorem B3593591 : Blo 1596997 3593591 := bstep (se 1 (by rfl) ⟨2695193, by rfl⟩ : syracuseStep 3593591 = 5390387) B5390387
theorem B21869959 : Blo 1596997 21869959 := bstep (se 1 (by rfl) ⟨16402469, by rfl⟩ : syracuseStep 21869959 = 32804939) B32804939
theorem B2397575 : Blo 1596997 2397575 := bstep (se 1 (by rfl) ⟨1798181, by rfl⟩ : syracuseStep 2397575 = 3596363) B3596363
theorem B2397611 : Blo 1596997 2397611 := bstep (se 1 (by rfl) ⟨1798208, by rfl⟩ : syracuseStep 2397611 = 3596417) B3596417
theorem B5756345 : Blo 1596997 5756345 := bstep (se 2 (by rfl) ⟨2158629, by rfl⟩ : syracuseStep 5756345 = 4317259) B4317259
theorem B2397641 : Blo 1596997 2397641 := bstep (se 2 (by rfl) ⟨899115, by rfl⟩ : syracuseStep 2397641 = 1798231) B1798231
theorem B8091089 : Blo 1596997 8091089 := bstep (se 2 (by rfl) ⟨3034158, by rfl⟩ : syracuseStep 8091089 = 6068317) B6068317
theorem B4044289 : Blo 1596997 4044289 := bstep (se 2 (by rfl) ⟨1516608, by rfl⟩ : syracuseStep 4044289 = 3033217) B3033217
theorem B3593771 : Blo 1596997 3593771 := bstep (se 1 (by rfl) ⟨2695328, by rfl⟩ : syracuseStep 3593771 = 5390657) B5390657
theorem B2397755 : Blo 1596997 2397755 := bstep (se 1 (by rfl) ⟨1798316, by rfl⟩ : syracuseStep 2397755 = 3596633) B3596633
theorem B6067831 : Blo 1596997 6067831 := bstep (se 1 (by rfl) ⟨4550873, by rfl⟩ : syracuseStep 6067831 = 9101747) B9101747
theorem B2397815 : Blo 1596997 2397815 := bstep (se 1 (by rfl) ⟨1798361, by rfl⟩ : syracuseStep 2397815 = 3596723) B3596723
theorem B2397839 : Blo 1596997 2397839 := bstep (se 1 (by rfl) ⟨1798379, by rfl⟩ : syracuseStep 2397839 = 3596759) B3596759
theorem B2397881 : Blo 1596997 2397881 := bstep (se 2 (by rfl) ⟨899205, by rfl⟩ : syracuseStep 2397881 = 1798411) B1798411
theorem B2397959 : Blo 1596997 2397959 := bstep (se 1 (by rfl) ⟨1798469, by rfl⟩ : syracuseStep 2397959 = 3596939) B3596939
theorem B13645583 : Blo 1596997 13645583 := bstep (se 1 (by rfl) ⟨10234187, by rfl⟩ : syracuseStep 13645583 = 20468375) B20468375
theorem B2397995 : Blo 1596997 2397995 := bstep (se 1 (by rfl) ⟨1798496, by rfl⟩ : syracuseStep 2397995 = 3596993) B3596993
theorem B4101931 : Blo 1596997 4101931 := bstep (se 1 (by rfl) ⟨3076448, by rfl⟩ : syracuseStep 4101931 = 6152897) B6152897
theorem B2398025 : Blo 1596997 2398025 := bstep (se 2 (by rfl) ⟨899259, by rfl⟩ : syracuseStep 2398025 = 1798519) B1798519
theorem B3594131 : Blo 1596997 3594131 := bstep (se 1 (by rfl) ⟨2695598, by rfl⟩ : syracuseStep 3594131 = 5391197) B5391197
theorem B4552595 : Blo 1596997 4552595 := bstep (se 1 (by rfl) ⟨3414446, by rfl⟩ : syracuseStep 4552595 = 6828893) B6828893
theorem B2398139 : Blo 1596997 2398139 := bstep (se 1 (by rfl) ⟨1798604, by rfl⟩ : syracuseStep 2398139 = 3597209) B3597209
theorem B3594185 : Blo 1596997 3594185 := bstep (se 2 (by rfl) ⟨1347819, by rfl⟩ : syracuseStep 3594185 = 2695639) B2695639
theorem B2398199 : Blo 1596997 2398199 := bstep (se 1 (by rfl) ⟨1798649, by rfl⟩ : syracuseStep 2398199 = 3597299) B3597299
theorem B4102159 : Blo 1596997 4102159 := bstep (se 1 (by rfl) ⟨3076619, by rfl⟩ : syracuseStep 4102159 = 6153239) B6153239
theorem B2398223 : Blo 1596997 2398223 := bstep (se 1 (by rfl) ⟨1798667, by rfl⟩ : syracuseStep 2398223 = 3597335) B3597335
theorem B9099287 : Blo 1596997 9099287 := bstep (se 1 (by rfl) ⟨6824465, by rfl⟩ : syracuseStep 9099287 = 13648931) B13648931
theorem B2398265 : Blo 1596997 2398265 := bstep (se 2 (by rfl) ⟨899349, by rfl⟩ : syracuseStep 2398265 = 1798699) B1798699
theorem B4044887 : Blo 1596997 4044887 := bstep (se 1 (by rfl) ⟨3033665, by rfl⟩ : syracuseStep 4044887 = 6067331) B6067331
theorem B2398343 : Blo 1596997 2398343 := bstep (se 1 (by rfl) ⟨1798757, by rfl⟩ : syracuseStep 2398343 = 3597515) B3597515
theorem B2398379 : Blo 1596997 2398379 := bstep (se 1 (by rfl) ⟨1798784, by rfl⟩ : syracuseStep 2398379 = 3597569) B3597569
theorem B3840185 : Blo 1596997 3840185 := bstep (se 2 (by rfl) ⟨1440069, by rfl⟩ : syracuseStep 3840185 = 2880139) B2880139
theorem B2398409 : Blo 1596997 2398409 := bstep (se 2 (by rfl) ⟨899403, by rfl⟩ : syracuseStep 2398409 = 1798807) B1798807
theorem B4045099 : Blo 1596997 4045099 := bstep (se 1 (by rfl) ⟨3033824, by rfl⟩ : syracuseStep 4045099 = 6067649) B6067649
theorem B13654331 : Blo 1596997 13654331 := bstep (se 1 (by rfl) ⟨10240748, by rfl⟩ : syracuseStep 13654331 = 20481497) B20481497
theorem B4045241 : Blo 1596997 4045241 := bstep (se 2 (by rfl) ⟨1516965, by rfl⟩ : syracuseStep 4045241 = 3033931) B3033931
theorem B6068803 : Blo 1596997 6068803 := bstep (se 1 (by rfl) ⟨4551602, by rfl⟩ : syracuseStep 6068803 = 9103205) B9103205
theorem B9230915 : Blo 1596997 9230915 := bstep (se 1 (by rfl) ⟨6923186, by rfl⟩ : syracuseStep 9230915 = 13846373) B13846373
theorem B4676183 : Blo 1596997 4676183 := bstep (se 1 (by rfl) ⟨3507137, by rfl⟩ : syracuseStep 4676183 = 7014275) B7014275
theorem B2022023 : Blo 1596997 2022023 := bstep (se 1 (by rfl) ⟨1516517, by rfl⟩ : syracuseStep 2022023 = 3033035) B3033035
theorem B3594887 : Blo 1596997 3594887 := bstep (se 1 (by rfl) ⟨2696165, by rfl⟩ : syracuseStep 3594887 = 5392331) B5392331
theorem B2276041 : Blo 1596997 2276041 := bstep (se 2 (by rfl) ⟨853515, by rfl⟩ : syracuseStep 2276041 = 1707031) B1707031
theorem B12131045 : Blo 1596997 12131045 := bstep (se 4 (by rfl) ⟨1137285, by rfl⟩ : syracuseStep 12131045 = 2274571) B2274571
theorem B3595067 : Blo 1596997 3595067 := bstep (se 1 (by rfl) ⟨2696300, by rfl⟩ : syracuseStep 3595067 = 5392601) B5392601
theorem B6069107 : Blo 1596997 6069107 := bstep (se 1 (by rfl) ⟨4551830, by rfl⟩ : syracuseStep 6069107 = 9103661) B9103661
theorem B32783267 : Blo 1596997 32783267 := bstep (se 1 (by rfl) ⟨24587450, by rfl⟩ : syracuseStep 32783267 = 49174901) B49174901
theorem B3595193 : Blo 1596997 3595193 := bstep (se 2 (by rfl) ⟨1348197, by rfl⟩ : syracuseStep 3595193 = 2696395) B2696395
theorem B3840953 : Blo 1596997 3840953 := bstep (se 2 (by rfl) ⟨1440357, by rfl⟩ : syracuseStep 3840953 = 2880715) B2880715
theorem B7674833 : Blo 1596997 7674833 := bstep (se 2 (by rfl) ⟨2878062, by rfl⟩ : syracuseStep 7674833 = 5756125) B5756125
theorem B7781341 : Blo 1596997 7781341 := bstep (se 3 (by rfl) ⟨1459001, by rfl⟩ : syracuseStep 7781341 = 2918003) B2918003
theorem B2276599 : Blo 1596997 2276599 := bstep (se 1 (by rfl) ⟨1707449, by rfl⟩ : syracuseStep 2276599 = 3414899) B3414899
theorem B3595535 : Blo 1596997 3595535 := bstep (se 1 (by rfl) ⟨2696651, by rfl⟩ : syracuseStep 3595535 = 5393303) B5393303
theorem B2022671 : Blo 1596997 2022671 := bstep (se 1 (by rfl) ⟨1517003, by rfl⟩ : syracuseStep 2022671 = 3034007) B3034007
theorem B3595553 : Blo 1596997 3595553 := bstep (se 2 (by rfl) ⟨1348332, by rfl⟩ : syracuseStep 3595553 = 2696665) B2696665
theorem B6069563 : Blo 1596997 6069563 := bstep (se 1 (by rfl) ⟨4552172, by rfl⟩ : syracuseStep 6069563 = 9104345) B9104345
theorem B2628983 : Blo 1596997 2628983 := bstep (se 1 (by rfl) ⟨1971737, by rfl⟩ : syracuseStep 2628983 = 3943475) B3943475
theorem B3841415 : Blo 1596997 3841415 := bstep (se 1 (by rfl) ⟨2881061, by rfl⟩ : syracuseStep 3841415 = 5762123) B5762123
theorem B4046233 : Blo 1596997 4046233 := bstep (se 2 (by rfl) ⟨1517337, by rfl⟩ : syracuseStep 4046233 = 3034675) B3034675
theorem B8093195 : Blo 1596997 8093195 := bstep (se 1 (by rfl) ⟨6069896, by rfl⟩ : syracuseStep 8093195 = 12139793) B12139793
theorem B5119517 : Blo 1596997 5119517 := bstep (se 3 (by rfl) ⟨959909, by rfl⟩ : syracuseStep 5119517 = 1919819) B1919819
theorem B4046395 : Blo 1596997 4046395 := bstep (se 1 (by rfl) ⟨3034796, by rfl⟩ : syracuseStep 4046395 = 6069593) B6069593
theorem B3595895 : Blo 1596997 3595895 := bstep (se 1 (by rfl) ⟨2696921, by rfl⟩ : syracuseStep 3595895 = 5393843) B5393843
theorem B1597063 : Blo 1596997 1597063 := bstep (se 1 (by rfl) ⟨1197797, by rfl⟩ : syracuseStep 1597063 = 2395595) B2395595
theorem B1597071 : Blo 1596997 1597071 := bstep (se 1 (by rfl) ⟨1197803, by rfl⟩ : syracuseStep 1597071 = 2395607) B2395607
theorem B8093357 : Blo 1596997 8093357 := bstep (se 3 (by rfl) ⟨1517504, by rfl⟩ : syracuseStep 8093357 = 3035009) B3035009
theorem B1597115 : Blo 1596997 1597115 := bstep (se 1 (by rfl) ⟨1197836, by rfl⟩ : syracuseStep 1597115 = 2395673) B2395673
theorem B4046537 : Blo 1596997 4046537 := bstep (se 2 (by rfl) ⟨1517451, by rfl⟩ : syracuseStep 4046537 = 3034903) B3034903
theorem B1597191 : Blo 1596997 1597191 := bstep (se 1 (by rfl) ⟨1197893, by rfl⟩ : syracuseStep 1597191 = 2395787) B2395787
theorem B1597199 : Blo 1596997 1597199 := bstep (se 1 (by rfl) ⟨1197899, by rfl⟩ : syracuseStep 1597199 = 2395799) B2395799
theorem B6070049 : Blo 1596997 6070049 := bstep (se 2 (by rfl) ⟨2276268, by rfl⟩ : syracuseStep 6070049 = 4552537) B4552537
theorem B3596075 : Blo 1596997 3596075 := bstep (se 1 (by rfl) ⟨2697056, by rfl⟩ : syracuseStep 3596075 = 5394113) B5394113
theorem B2694971 : Blo 1596997 2694971 := bstep (se 1 (by rfl) ⟨2021228, by rfl⟩ : syracuseStep 2694971 = 4042457) B4042457
theorem B1597243 : Blo 1596997 1597243 := bstep (se 1 (by rfl) ⟨1197932, by rfl⟩ : syracuseStep 1597243 = 2395865) B2395865
theorem B11517785 : Blo 1596997 11517785 := bstep (se 2 (by rfl) ⟨4319169, by rfl⟩ : syracuseStep 11517785 = 8638339) B8638339
theorem B1597319 : Blo 1596997 1597319 := bstep (se 1 (by rfl) ⟨1197989, by rfl⟩ : syracuseStep 1597319 = 2395979) B2395979
theorem B1597327 : Blo 1596997 1597327 := bstep (se 1 (by rfl) ⟨1197995, by rfl⟩ : syracuseStep 1597327 = 2395991) B2395991
theorem B20234137 : Blo 1596997 20234137 := bstep (se 2 (by rfl) ⟨7587801, by rfl⟩ : syracuseStep 20234137 = 15175603) B15175603
theorem B1597371 : Blo 1596997 1597371 := bstep (se 1 (by rfl) ⟨1198028, by rfl⟩ : syracuseStep 1597371 = 2396057) B2396057
theorem B2695207 : Blo 1596997 2695207 := bstep (se 1 (by rfl) ⟨2021405, by rfl⟩ : syracuseStep 2695207 = 4042811) B4042811
theorem B1597479 : Blo 1596997 1597479 := bstep (se 1 (by rfl) ⟨1198109, by rfl⟩ : syracuseStep 1597479 = 2396219) B2396219
theorem B3596345 : Blo 1596997 3596345 := bstep (se 2 (by rfl) ⟨1348629, by rfl⟩ : syracuseStep 3596345 = 2697259) B2697259
theorem B1597519 : Blo 1596997 1597519 := bstep (se 1 (by rfl) ⟨1198139, by rfl⟩ : syracuseStep 1597519 = 2396279) B2396279
theorem B1597535 : Blo 1596997 1597535 := bstep (se 1 (by rfl) ⟨1198151, by rfl⟩ : syracuseStep 1597535 = 2396303) B2396303
theorem B1597563 : Blo 1596997 1597563 := bstep (se 1 (by rfl) ⟨1198172, by rfl⟩ : syracuseStep 1597563 = 2396345) B2396345
theorem B1597615 : Blo 1596997 1597615 := bstep (se 1 (by rfl) ⟨1198211, by rfl⟩ : syracuseStep 1597615 = 2396423) B2396423
theorem B1597639 : Blo 1596997 1597639 := bstep (se 1 (by rfl) ⟨1198229, by rfl⟩ : syracuseStep 1597639 = 2396459) B2396459
theorem B1597659 : Blo 1596997 1597659 := bstep (se 1 (by rfl) ⟨1198244, by rfl⟩ : syracuseStep 1597659 = 2396489) B2396489
theorem B5390603 : Blo 1596997 5390603 := bstep (se 1 (by rfl) ⟨4042952, by rfl⟩ : syracuseStep 5390603 = 8085905) B8085905
theorem B1597735 : Blo 1596997 1597735 := bstep (se 1 (by rfl) ⟨1198301, by rfl⟩ : syracuseStep 1597735 = 2396603) B2396603
theorem B1597775 : Blo 1596997 1597775 := bstep (se 1 (by rfl) ⟨1198331, by rfl⟩ : syracuseStep 1597775 = 2396663) B2396663
theorem B1597791 : Blo 1596997 1597791 := bstep (se 1 (by rfl) ⟨1198343, by rfl⟩ : syracuseStep 1597791 = 2396687) B2396687
theorem B2695531 : Blo 1596997 2695531 := bstep (se 1 (by rfl) ⟨2021648, by rfl⟩ : syracuseStep 2695531 = 4043297) B4043297
theorem B1597819 : Blo 1596997 1597819 := bstep (se 1 (by rfl) ⟨1198364, by rfl⟩ : syracuseStep 1597819 = 2396729) B2396729
theorem B3596687 : Blo 1596997 3596687 := bstep (se 1 (by rfl) ⟨2697515, by rfl⟩ : syracuseStep 3596687 = 5395031) B5395031
theorem B1597871 : Blo 1596997 1597871 := bstep (se 1 (by rfl) ⟨1198403, by rfl⟩ : syracuseStep 1597871 = 2396807) B2396807
theorem B1597895 : Blo 1596997 1597895 := bstep (se 1 (by rfl) ⟨1198421, by rfl⟩ : syracuseStep 1597895 = 2396843) B2396843
theorem B1597915 : Blo 1596997 1597915 := bstep (se 1 (by rfl) ⟨1198436, by rfl⟩ : syracuseStep 1597915 = 2396873) B2396873
theorem B6070747 : Blo 1596997 6070747 := bstep (se 1 (by rfl) ⟨4553060, by rfl⟩ : syracuseStep 6070747 = 9106121) B9106121
theorem B4047347 : Blo 1596997 4047347 := bstep (se 1 (by rfl) ⟨3035510, by rfl⟩ : syracuseStep 4047347 = 6071021) B6071021
theorem B5390873 : Blo 1596997 5390873 := bstep (se 2 (by rfl) ⟨2021577, by rfl⟩ : syracuseStep 5390873 = 4043155) B4043155
theorem B1597991 : Blo 1596997 1597991 := bstep (se 1 (by rfl) ⟨1198493, by rfl⟩ : syracuseStep 1597991 = 2396987) B2396987
theorem B1598031 : Blo 1596997 1598031 := bstep (se 1 (by rfl) ⟨1198523, by rfl⟩ : syracuseStep 1598031 = 2397047) B2397047
theorem B1598047 : Blo 1596997 1598047 := bstep (se 1 (by rfl) ⟨1198535, by rfl⟩ : syracuseStep 1598047 = 2397071) B2397071
theorem B4440673 : Blo 1596997 4440673 := bstep (se 2 (by rfl) ⟨1665252, by rfl⟩ : syracuseStep 4440673 = 3330505) B3330505
theorem B1598075 : Blo 1596997 1598075 := bstep (se 1 (by rfl) ⟨1198556, by rfl⟩ : syracuseStep 1598075 = 2397113) B2397113
theorem B1598127 : Blo 1596997 1598127 := bstep (se 1 (by rfl) ⟨1198595, by rfl⟩ : syracuseStep 1598127 = 2397191) B2397191
theorem B5759687 : Blo 1596997 5759687 := bstep (se 1 (by rfl) ⟨4319765, by rfl⟩ : syracuseStep 5759687 = 8639531) B8639531
theorem B1598151 : Blo 1596997 1598151 := bstep (se 1 (by rfl) ⟨1198613, by rfl⟩ : syracuseStep 1598151 = 2397227) B2397227
theorem B3597011 : Blo 1596997 3597011 := bstep (se 1 (by rfl) ⟨2697758, by rfl⟩ : syracuseStep 3597011 = 5395517) B5395517
theorem B1598171 : Blo 1596997 1598171 := bstep (se 1 (by rfl) ⟨1198628, by rfl⟩ : syracuseStep 1598171 = 2397257) B2397257
theorem B1598247 : Blo 1596997 1598247 := bstep (se 1 (by rfl) ⟨1198685, by rfl⟩ : syracuseStep 1598247 = 2397371) B2397371
theorem B8643401 : Blo 1596997 8643401 := bstep (se 2 (by rfl) ⟨3241275, by rfl⟩ : syracuseStep 8643401 = 6482551) B6482551
theorem B1598287 : Blo 1596997 1598287 := bstep (se 1 (by rfl) ⟨1198715, by rfl⟩ : syracuseStep 1598287 = 2397431) B2397431
theorem B1598303 : Blo 1596997 1598303 := bstep (se 1 (by rfl) ⟨1198727, by rfl⟩ : syracuseStep 1598303 = 2397455) B2397455
theorem B1598331 : Blo 1596997 1598331 := bstep (se 1 (by rfl) ⟨1198748, by rfl⟩ : syracuseStep 1598331 = 2397497) B2397497
theorem B1598383 : Blo 1596997 1598383 := bstep (se 1 (by rfl) ⟨1198787, by rfl⟩ : syracuseStep 1598383 = 2397575) B2397575
theorem B1598407 : Blo 1596997 1598407 := bstep (se 1 (by rfl) ⟨1198805, by rfl⟩ : syracuseStep 1598407 = 2397611) B2397611
theorem B1598427 : Blo 1596997 1598427 := bstep (se 1 (by rfl) ⟨1198820, by rfl⟩ : syracuseStep 1598427 = 2397641) B2397641
theorem B1598503 : Blo 1596997 1598503 := bstep (se 1 (by rfl) ⟨1198877, by rfl⟩ : syracuseStep 1598503 = 2397755) B2397755
theorem B1598543 : Blo 1596997 1598543 := bstep (se 1 (by rfl) ⟨1198907, by rfl⟩ : syracuseStep 1598543 = 2397815) B2397815
theorem B1598559 : Blo 1596997 1598559 := bstep (se 1 (by rfl) ⟨1198919, by rfl⟩ : syracuseStep 1598559 = 2397839) B2397839
theorem B1598587 : Blo 1596997 1598587 := bstep (se 1 (by rfl) ⟨1198940, by rfl⟩ : syracuseStep 1598587 = 2397881) B2397881
theorem B1598639 : Blo 1596997 1598639 := bstep (se 1 (by rfl) ⟨1198979, by rfl⟩ : syracuseStep 1598639 = 2397959) B2397959
theorem B1598663 : Blo 1596997 1598663 := bstep (se 1 (by rfl) ⟨1198997, by rfl⟩ : syracuseStep 1598663 = 2397995) B2397995
theorem B1598683 : Blo 1596997 1598683 := bstep (se 1 (by rfl) ⟨1199012, by rfl⟩ : syracuseStep 1598683 = 2398025) B2398025
theorem B1598759 : Blo 1596997 1598759 := bstep (se 1 (by rfl) ⟨1199069, by rfl⟩ : syracuseStep 1598759 = 2398139) B2398139
theorem B1598799 : Blo 1596997 1598799 := bstep (se 1 (by rfl) ⟨1199099, by rfl⟩ : syracuseStep 1598799 = 2398199) B2398199
theorem B1598815 : Blo 1596997 1598815 := bstep (se 1 (by rfl) ⟨1199111, by rfl⟩ : syracuseStep 1598815 = 2398223) B2398223
theorem B1598843 : Blo 1596997 1598843 := bstep (se 1 (by rfl) ⟨1199132, by rfl⟩ : syracuseStep 1598843 = 2398265) B2398265
theorem B2696591 : Blo 1596997 2696591 := bstep (se 1 (by rfl) ⟨2022443, by rfl⟩ : syracuseStep 2696591 = 4044887) B4044887
theorem B21874067 : Blo 1596997 21874067 := bstep (se 1 (by rfl) ⟨16405550, by rfl⟩ : syracuseStep 21874067 = 32811101) B32811101
theorem B1598895 : Blo 1596997 1598895 := bstep (se 1 (by rfl) ⟨1199171, by rfl⟩ : syracuseStep 1598895 = 2398343) B2398343
theorem B2049463 : Blo 1596997 2049463 := bstep (se 1 (by rfl) ⟨1537097, by rfl⟩ : syracuseStep 2049463 = 3074195) B3074195
theorem B1598919 : Blo 1596997 1598919 := bstep (se 1 (by rfl) ⟨1199189, by rfl⟩ : syracuseStep 1598919 = 2398379) B2398379
theorem B1598939 : Blo 1596997 1598939 := bstep (se 1 (by rfl) ⟨1199204, by rfl⟩ : syracuseStep 1598939 = 2398409) B2398409
theorem B9102887 : Blo 1596997 9102887 := bstep (se 1 (by rfl) ⟨6827165, by rfl⟩ : syracuseStep 9102887 = 13654331) B13654331
theorem B3032633 : Blo 1596997 3032633 := bstep (se 2 (by rfl) ⟨1137237, by rfl⟩ : syracuseStep 3032633 = 2274475) B2274475
theorem B2696827 : Blo 1596997 2696827 := bstep (se 1 (by rfl) ⟨2022620, by rfl⟩ : syracuseStep 2696827 = 4045241) B4045241
theorem B5392007 : Blo 1596997 5392007 := bstep (se 1 (by rfl) ⟨4044005, by rfl⟩ : syracuseStep 5392007 = 8088011) B8088011
theorem B5834425 : Blo 1596997 5834425 := bstep (se 2 (by rfl) ⟨2187909, by rfl⟩ : syracuseStep 5834425 = 4375819) B4375819
theorem B5392061 : Blo 1596997 5392061 := bstep (se 3 (by rfl) ⟨1011011, by rfl⟩ : syracuseStep 5392061 = 2022023) B2022023
theorem B6153943 : Blo 1596997 6153943 := bstep (se 1 (by rfl) ⟨4615457, by rfl⟩ : syracuseStep 6153943 = 9230915) B9230915
theorem B4097785 : Blo 1596997 4097785 := bstep (se 2 (by rfl) ⟨1536669, by rfl⟩ : syracuseStep 4097785 = 3073339) B3073339
theorem B8087363 : Blo 1596997 8087363 := bstep (se 1 (by rfl) ⟨6065522, by rfl⟩ : syracuseStep 8087363 = 12131045) B12131045
theorem B5392223 : Blo 1596997 5392223 := bstep (se 1 (by rfl) ⟨4044167, by rfl⟩ : syracuseStep 5392223 = 8088335) B8088335
theorem B10241927 : Blo 1596997 10241927 := bstep (se 1 (by rfl) ⟨7681445, by rfl⟩ : syracuseStep 10241927 = 15362891) B15362891
theorem B40953761 : Blo 1596997 40953761 := bstep (se 2 (by rfl) ⟨15357660, by rfl⟩ : syracuseStep 40953761 = 30715321) B30715321
theorem B1918939 : Blo 1596997 1918939 := bstep (se 1 (by rfl) ⟨1439204, by rfl⟩ : syracuseStep 1918939 = 2878409) B2878409
theorem B5392385 : Blo 1596997 5392385 := bstep (se 2 (by rfl) ⟨2022144, by rfl⟩ : syracuseStep 5392385 = 4044289) B4044289
theorem B13649957 : Blo 1596997 13649957 := bstep (se 4 (by rfl) ⟨1279683, by rfl⟩ : syracuseStep 13649957 = 2559367) B2559367
theorem B8874065 : Blo 1596997 8874065 := bstep (se 2 (by rfl) ⟨3327774, by rfl⟩ : syracuseStep 8874065 = 6655549) B6655549
theorem B2697691 : Blo 1596997 2697691 := bstep (se 1 (by rfl) ⟨2023268, by rfl⟩ : syracuseStep 2697691 = 4046537) B4046537
theorem B10242541 : Blo 1596997 10242541 := bstep (se 3 (by rfl) ⟨1920476, by rfl⟩ : syracuseStep 10242541 = 3840953) B3840953
theorem B26978849 : Blo 1596997 26978849 := bstep (se 2 (by rfl) ⟨10117068, by rfl⟩ : syracuseStep 26978849 = 20234137) B20234137
theorem B1796647 : Blo 1596997 1796647 := bstep (se 1 (by rfl) ⟨1347485, by rfl⟩ : syracuseStep 1796647 = 2694971) B2694971
theorem B7678523 : Blo 1596997 7678523 := bstep (se 1 (by rfl) ⟨5758892, by rfl⟩ : syracuseStep 7678523 = 11517785) B11517785
theorem B5393195 : Blo 1596997 5393195 := bstep (se 1 (by rfl) ⟨4044896, by rfl⟩ : syracuseStep 5393195 = 8089793) B8089793
theorem B3410849 : Blo 1596997 3410849 := bstep (se 2 (by rfl) ⟨1279068, by rfl⟩ : syracuseStep 3410849 = 2558137) B2558137
theorem B49220621 : Blo 1596997 49220621 := bstep (se 3 (by rfl) ⟨9228866, by rfl⟩ : syracuseStep 49220621 = 18457733) B18457733
theorem B5393465 : Blo 1596997 5393465 := bstep (se 2 (by rfl) ⟨2022549, by rfl⟩ : syracuseStep 5393465 = 4045099) B4045099
theorem B3034235 : Blo 1596997 3034235 := bstep (se 1 (by rfl) ⟨2275676, by rfl⟩ : syracuseStep 3034235 = 4551353) B4551353
theorem B1821895 : Blo 1596997 1821895 := bstep (se 1 (by rfl) ⟨1366421, by rfl⟩ : syracuseStep 1821895 = 2732843) B2732843
theorem B9104663 : Blo 1596997 9104663 := bstep (se 1 (by rfl) ⟨6828497, by rfl⟩ : syracuseStep 9104663 = 13656995) B13656995
theorem B2395499 : Blo 1596997 2395499 := bstep (se 1 (by rfl) ⟨1796624, by rfl⟩ : syracuseStep 2395499 = 3593249) B3593249
theorem B5393789 : Blo 1596997 5393789 := bstep (se 3 (by rfl) ⟨1011335, by rfl⟩ : syracuseStep 5393789 = 2022671) B2022671
theorem B4320641 : Blo 1596997 4320641 := bstep (se 2 (by rfl) ⟨1620240, by rfl⟩ : syracuseStep 4320641 = 3240481) B3240481
theorem B27315629 : Blo 1596997 27315629 := bstep (se 3 (by rfl) ⟨5121680, by rfl⟩ : syracuseStep 27315629 = 10243361) B10243361
theorem B2559451 : Blo 1596997 2559451 := bstep (se 1 (by rfl) ⟨1919588, by rfl⟩ : syracuseStep 2559451 = 3839177) B3839177
theorem B13831667 : Blo 1596997 13831667 := bstep (se 1 (by rfl) ⟨10373750, by rfl⟩ : syracuseStep 13831667 = 20747501) B20747501
theorem B3239443 : Blo 1596997 3239443 := bstep (se 1 (by rfl) ⟨2429582, by rfl⟩ : syracuseStep 3239443 = 4859165) B4859165
theorem B2395727 : Blo 1596997 2395727 := bstep (se 1 (by rfl) ⟨1796795, by rfl⟩ : syracuseStep 2395727 = 3593591) B3593591
theorem B3034721 : Blo 1596997 3034721 := bstep (se 2 (by rfl) ⟨1138020, by rfl⟩ : syracuseStep 3034721 = 2276041) B2276041
theorem B27668087 : Blo 1596997 27668087 := bstep (se 1 (by rfl) ⟨20751065, by rfl⟩ : syracuseStep 27668087 = 41502131) B41502131
theorem B3837563 : Blo 1596997 3837563 := bstep (se 1 (by rfl) ⟨2878172, by rfl⟩ : syracuseStep 3837563 = 5756345) B5756345
theorem B5394059 : Blo 1596997 5394059 := bstep (se 1 (by rfl) ⟨4045544, by rfl⟩ : syracuseStep 5394059 = 8091089) B8091089
theorem B2395847 : Blo 1596997 2395847 := bstep (se 1 (by rfl) ⟨1796885, by rfl⟩ : syracuseStep 2395847 = 3593771) B3593771
theorem B6065873 : Blo 1596997 6065873 := bstep (se 2 (by rfl) ⟨2274702, by rfl⟩ : syracuseStep 6065873 = 4549405) B4549405
theorem B21860057 : Blo 1596997 21860057 := bstep (se 2 (by rfl) ⟨8197521, by rfl⟩ : syracuseStep 21860057 = 16395043) B16395043
theorem B39415517 : Blo 1596997 39415517 := bstep (se 3 (by rfl) ⟨7390409, by rfl⟩ : syracuseStep 39415517 = 14780819) B14780819
theorem B9097055 : Blo 1596997 9097055 := bstep (se 1 (by rfl) ⟨6822791, by rfl⟩ : syracuseStep 9097055 = 13645583) B13645583
theorem B2396009 : Blo 1596997 2396009 := bstep (se 2 (by rfl) ⟨898503, by rfl⟩ : syracuseStep 2396009 = 1797007) B1797007
theorem B2396087 : Blo 1596997 2396087 := bstep (se 1 (by rfl) ⟨1797065, by rfl⟩ : syracuseStep 2396087 = 3594131) B3594131
theorem B3035063 : Blo 1596997 3035063 := bstep (se 1 (by rfl) ⟨2276297, by rfl⟩ : syracuseStep 3035063 = 4552595) B4552595
theorem B10375121 : Blo 1596997 10375121 := bstep (se 2 (by rfl) ⟨3890670, by rfl⟩ : syracuseStep 10375121 = 7781341) B7781341
theorem B2396123 : Blo 1596997 2396123 := bstep (se 1 (by rfl) ⟨1797092, by rfl⟩ : syracuseStep 2396123 = 3594185) B3594185
theorem B6066191 : Blo 1596997 6066191 := bstep (se 1 (by rfl) ⟨4549643, by rfl⟩ : syracuseStep 6066191 = 9099287) B9099287
theorem B4042831 : Blo 1596997 4042831 := bstep (se 1 (by rfl) ⟨3032123, by rfl⟩ : syracuseStep 4042831 = 6064247) B6064247
theorem B2560123 : Blo 1596997 2560123 := bstep (se 1 (by rfl) ⟨1920092, by rfl⟩ : syracuseStep 2560123 = 3840185) B3840185
theorem B1798267 : Blo 1596997 1798267 := bstep (se 1 (by rfl) ⟨1348700, by rfl⟩ : syracuseStep 1798267 = 2697401) B2697401
theorem B9097373 : Blo 1596997 9097373 := bstep (se 3 (by rfl) ⟨1705757, by rfl⟩ : syracuseStep 9097373 = 3411515) B3411515
theorem B21876965 : Blo 1596997 21876965 := bstep (se 4 (by rfl) ⟨2050965, by rfl⟩ : syracuseStep 21876965 = 4101931) B4101931
theorem B3035465 : Blo 1596997 3035465 := bstep (se 2 (by rfl) ⟨1138299, by rfl⟩ : syracuseStep 3035465 = 2276599) B2276599
theorem B3117455 : Blo 1596997 3117455 := bstep (se 1 (by rfl) ⟨2338091, by rfl⟩ : syracuseStep 3117455 = 4676183) B4676183
theorem B2159023 : Blo 1596997 2159023 := bstep (se 1 (by rfl) ⟨1619267, by rfl⟩ : syracuseStep 2159023 = 3238535) B3238535
theorem B2396591 : Blo 1596997 2396591 := bstep (se 1 (by rfl) ⟨1797443, by rfl⟩ : syracuseStep 2396591 = 3594887) B3594887
theorem B3076535 : Blo 1596997 3076535 := bstep (se 1 (by rfl) ⟨2307401, by rfl⟩ : syracuseStep 3076535 = 4614803) B4614803
theorem B2396681 : Blo 1596997 2396681 := bstep (se 2 (by rfl) ⟨898755, by rfl⟩ : syracuseStep 2396681 = 1797511) B1797511
theorem B29159945 : Blo 1596997 29159945 := bstep (se 2 (by rfl) ⟨10934979, by rfl⟩ : syracuseStep 29159945 = 21869959) B21869959
theorem B12956183 : Blo 1596997 12956183 := bstep (se 1 (by rfl) ⟨9717137, by rfl⟩ : syracuseStep 12956183 = 19434275) B19434275
theorem B5116441 : Blo 1596997 5116441 := bstep (se 2 (by rfl) ⟨1918665, by rfl⟩ : syracuseStep 5116441 = 3837331) B3837331
theorem B5394977 : Blo 1596997 5394977 := bstep (se 2 (by rfl) ⟨2023116, by rfl⟩ : syracuseStep 5394977 = 4046233) B4046233
theorem B2396711 : Blo 1596997 2396711 := bstep (se 1 (by rfl) ⟨1797533, by rfl⟩ : syracuseStep 2396711 = 3595067) B3595067
theorem B1798735 : Blo 1596997 1798735 := bstep (se 1 (by rfl) ⟨1349051, by rfl⟩ : syracuseStep 1798735 = 2698103) B2698103
theorem B2396795 : Blo 1596997 2396795 := bstep (se 1 (by rfl) ⟨1797596, by rfl⟩ : syracuseStep 2396795 = 3595193) B3595193
theorem B5116555 : Blo 1596997 5116555 := bstep (se 1 (by rfl) ⟨3837416, by rfl⟩ : syracuseStep 5116555 = 7674833) B7674833
theorem B17511085 : Blo 1596997 17511085 := bstep (se 3 (by rfl) ⟨3283328, by rfl⟩ : syracuseStep 17511085 = 6566657) B6566657
theorem B4043479 : Blo 1596997 4043479 := bstep (se 1 (by rfl) ⟨3032609, by rfl⟩ : syracuseStep 4043479 = 6065219) B6065219
theorem B2396921 : Blo 1596997 2396921 := bstep (se 2 (by rfl) ⟨898845, by rfl⟩ : syracuseStep 2396921 = 1797691) B1797691
theorem B5395193 : Blo 1596997 5395193 := bstep (se 2 (by rfl) ⟨2023197, by rfl⟩ : syracuseStep 5395193 = 4046395) B4046395
theorem B8090441 : Blo 1596997 8090441 := bstep (se 2 (by rfl) ⟨3033915, by rfl⟩ : syracuseStep 8090441 = 6067831) B6067831
theorem B12129101 : Blo 1596997 12129101 := bstep (se 3 (by rfl) ⟨2274206, by rfl⟩ : syracuseStep 12129101 = 4548413) B4548413
theorem B2397023 : Blo 1596997 2397023 := bstep (se 1 (by rfl) ⟨1797767, by rfl⟩ : syracuseStep 2397023 = 3595535) B3595535
theorem B10236779 : Blo 1596997 10236779 := bstep (se 1 (by rfl) ⟨7677584, by rfl⟩ : syracuseStep 10236779 = 15355169) B15355169
theorem B2397035 : Blo 1596997 2397035 := bstep (se 1 (by rfl) ⟨1797776, by rfl⟩ : syracuseStep 2397035 = 3595553) B3595553
theorem B12137363 : Blo 1596997 12137363 := bstep (se 1 (by rfl) ⟨9103022, by rfl⟩ : syracuseStep 12137363 = 18206045) B18206045
theorem B2560943 : Blo 1596997 2560943 := bstep (se 1 (by rfl) ⟨1920707, by rfl⟩ : syracuseStep 2560943 = 3841415) B3841415
theorem B4043783 : Blo 1596997 4043783 := bstep (se 1 (by rfl) ⟨3032837, by rfl⟩ : syracuseStep 4043783 = 6065675) B6065675
theorem B5395463 : Blo 1596997 5395463 := bstep (se 1 (by rfl) ⟨4046597, by rfl⟩ : syracuseStep 5395463 = 8093195) B8093195
theorem B3413011 : Blo 1596997 3413011 := bstep (se 1 (by rfl) ⟨2559758, by rfl⟩ : syracuseStep 3413011 = 5119517) B5119517
theorem B2397263 : Blo 1596997 2397263 := bstep (se 1 (by rfl) ⟨1797947, by rfl⟩ : syracuseStep 2397263 = 3595895) B3595895
theorem B5395571 : Blo 1596997 5395571 := bstep (se 1 (by rfl) ⟨4046678, by rfl⟩ : syracuseStep 5395571 = 8093357) B8093357
theorem B12301483 : Blo 1596997 12301483 := bstep (se 1 (by rfl) ⟨9226112, by rfl⟩ : syracuseStep 12301483 = 18452225) B18452225
theorem B2397383 : Blo 1596997 2397383 := bstep (se 1 (by rfl) ⟨1798037, by rfl⟩ : syracuseStep 2397383 = 3596075) B3596075
theorem B3413353 : Blo 1596997 3413353 := bstep (se 2 (by rfl) ⟨1280007, by rfl⟩ : syracuseStep 3413353 = 2560015) B2560015
theorem B2397545 : Blo 1596997 2397545 := bstep (se 2 (by rfl) ⟨899079, by rfl⟩ : syracuseStep 2397545 = 1798159) B1798159
theorem B5469545 : Blo 1596997 5469545 := bstep (se 2 (by rfl) ⟨2051079, by rfl⟩ : syracuseStep 5469545 = 4102159) B4102159
theorem B5395841 : Blo 1596997 5395841 := bstep (se 2 (by rfl) ⟨2023440, by rfl⟩ : syracuseStep 5395841 = 4046881) B4046881
theorem B2397623 : Blo 1596997 2397623 := bstep (se 1 (by rfl) ⟨1798217, by rfl⟩ : syracuseStep 2397623 = 3596435) B3596435
theorem B2397659 : Blo 1596997 2397659 := bstep (se 1 (by rfl) ⟨1798244, by rfl⟩ : syracuseStep 2397659 = 3596489) B3596489
theorem B3593825 : Blo 1596997 3593825 := bstep (se 2 (by rfl) ⟨1347684, by rfl⟩ : syracuseStep 3593825 = 2695369) B2695369
theorem B73791157 : Blo 1596997 73791157 := bstep (se 5 (by rfl) ⟨3458960, by rfl⟩ : syracuseStep 73791157 = 6917921) B6917921
theorem B18446039 : Blo 1596997 18446039 := bstep (se 1 (by rfl) ⟨13834529, by rfl⟩ : syracuseStep 18446039 = 27669059) B27669059
theorem B12138335 : Blo 1596997 12138335 := bstep (se 1 (by rfl) ⟨9103751, by rfl⟩ : syracuseStep 12138335 = 18207503) B18207503
theorem B6829933 : Blo 1596997 6829933 := bstep (se 3 (by rfl) ⟨1280612, by rfl⟩ : syracuseStep 6829933 = 2561225) B2561225
theorem B2398127 : Blo 1596997 2398127 := bstep (se 1 (by rfl) ⟨1798595, by rfl⟩ : syracuseStep 2398127 = 3597191) B3597191
theorem B3594167 : Blo 1596997 3594167 := bstep (se 1 (by rfl) ⟨2695625, by rfl⟩ : syracuseStep 3594167 = 5391251) B5391251
theorem B4437947 : Blo 1596997 4437947 := bstep (se 1 (by rfl) ⟨3328460, by rfl⟩ : syracuseStep 4437947 = 6656921) B6656921
theorem B2398217 : Blo 1596997 2398217 := bstep (se 2 (by rfl) ⟨899331, by rfl⟩ : syracuseStep 2398217 = 1798663) B1798663
theorem B2398247 : Blo 1596997 2398247 := bstep (se 1 (by rfl) ⟨1798685, by rfl⟩ : syracuseStep 2398247 = 3597371) B3597371
theorem B6068303 : Blo 1596997 6068303 := bstep (se 1 (by rfl) ⟨4551227, by rfl⟩ : syracuseStep 6068303 = 9102455) B9102455
theorem B8091737 : Blo 1596997 8091737 := bstep (se 2 (by rfl) ⟨3034401, by rfl⟩ : syracuseStep 8091737 = 6068803) B6068803
theorem B2398331 : Blo 1596997 2398331 := bstep (se 1 (by rfl) ⟨1798748, by rfl⟩ : syracuseStep 2398331 = 3597497) B3597497
theorem B2398457 : Blo 1596997 2398457 := bstep (se 2 (by rfl) ⟨899421, by rfl⟩ : syracuseStep 2398457 = 1798843) B1798843
theorem B7010621 : Blo 1596997 7010621 := bstep (se 3 (by rfl) ⟨1314491, by rfl⟩ : syracuseStep 7010621 = 2628983) B2628983
theorem B2021851 : Blo 1596997 2021851 := bstep (se 1 (by rfl) ⟨1516388, by rfl⟩ : syracuseStep 2021851 = 3032777) B3032777
theorem B3594761 : Blo 1596997 3594761 := bstep (se 2 (by rfl) ⟨1348035, by rfl⟩ : syracuseStep 3594761 = 2696071) B2696071
theorem B3414727 : Blo 1596997 3414727 := bstep (se 1 (by rfl) ⟨2561045, by rfl⟩ : syracuseStep 3414727 = 5122091) B5122091
theorem B3595103 : Blo 1596997 3595103 := bstep (se 1 (by rfl) ⟨2696327, by rfl⟩ : syracuseStep 3595103 = 5392655) B5392655
theorem B9100289 : Blo 1596997 9100289 := bstep (se 2 (by rfl) ⟨3412608, by rfl⟩ : syracuseStep 9100289 = 6825217) B6825217
theorem B3595283 : Blo 1596997 3595283 := bstep (se 1 (by rfl) ⟨2696462, by rfl⟩ : syracuseStep 3595283 = 5392925) B5392925
theorem B12131531 : Blo 1596997 12131531 := bstep (se 1 (by rfl) ⟨9098648, by rfl⟩ : syracuseStep 12131531 = 18197297) B18197297
theorem B4046071 : Blo 1596997 4046071 := bstep (se 1 (by rfl) ⟨3034553, by rfl⟩ : syracuseStep 4046071 = 6069107) B6069107
theorem B21855511 : Blo 1596997 21855511 := bstep (se 1 (by rfl) ⟨16391633, by rfl⟩ : syracuseStep 21855511 = 32783267) B32783267
theorem B11525399 : Blo 1596997 11525399 := bstep (se 1 (by rfl) ⟨8644049, by rfl⟩ : syracuseStep 11525399 = 17288099) B17288099
theorem B20749603 : Blo 1596997 20749603 := bstep (se 1 (by rfl) ⟨15562202, by rfl⟩ : syracuseStep 20749603 = 31124405) B31124405
theorem B12959065 : Blo 1596997 12959065 := bstep (se 2 (by rfl) ⟨4859649, by rfl⟩ : syracuseStep 12959065 = 9719299) B9719299
theorem B3595625 : Blo 1596997 3595625 := bstep (se 2 (by rfl) ⟨1348359, by rfl⟩ : syracuseStep 3595625 = 2696719) B2696719
theorem B5119375 : Blo 1596997 5119375 := bstep (se 1 (by rfl) ⟨3839531, by rfl⟩ : syracuseStep 5119375 = 7679063) B7679063
theorem B9100745 : Blo 1596997 9100745 := bstep (se 2 (by rfl) ⟨3412779, by rfl⟩ : syracuseStep 9100745 = 6825559) B6825559
theorem B4046345 : Blo 1596997 4046345 := bstep (se 2 (by rfl) ⟨1517379, by rfl⟩ : syracuseStep 4046345 = 3034759) B3034759
theorem B4046375 : Blo 1596997 4046375 := bstep (se 1 (by rfl) ⟨3034781, by rfl⟩ : syracuseStep 4046375 = 6069563) B6069563
theorem B1597007 : Blo 1596997 1597007 := bstep (se 1 (by rfl) ⟨1197755, by rfl⟩ : syracuseStep 1597007 = 2395511) B2395511
theorem B1597023 : Blo 1596997 1597023 := bstep (se 1 (by rfl) ⟨1197767, by rfl⟩ : syracuseStep 1597023 = 2395535) B2395535
theorem B1597051 : Blo 1596997 1597051 := bstep (se 1 (by rfl) ⟨1197788, by rfl⟩ : syracuseStep 1597051 = 2395577) B2395577
theorem B1597103 : Blo 1596997 1597103 := bstep (se 1 (by rfl) ⟨1197827, by rfl⟩ : syracuseStep 1597103 = 2395655) B2395655
theorem B5390009 : Blo 1596997 5390009 := bstep (se 2 (by rfl) ⟨2021253, by rfl⟩ : syracuseStep 5390009 = 4042507) B4042507
theorem B1597127 : Blo 1596997 1597127 := bstep (se 1 (by rfl) ⟨1197845, by rfl⟩ : syracuseStep 1597127 = 2395691) B2395691
theorem B1597147 : Blo 1596997 1597147 := bstep (se 1 (by rfl) ⟨1197860, by rfl⟩ : syracuseStep 1597147 = 2395721) B2395721
theorem B1597223 : Blo 1596997 1597223 := bstep (se 1 (by rfl) ⟨1197917, by rfl⟩ : syracuseStep 1597223 = 2395835) B2395835
theorem B1597263 : Blo 1596997 1597263 := bstep (se 1 (by rfl) ⟨1197947, by rfl⟩ : syracuseStep 1597263 = 2395895) B2395895
theorem B1597279 : Blo 1596997 1597279 := bstep (se 1 (by rfl) ⟨1197959, by rfl⟩ : syracuseStep 1597279 = 2395919) B2395919
theorem B11837279 : Blo 1596997 11837279 := bstep (se 1 (by rfl) ⟨8877959, by rfl⟩ : syracuseStep 11837279 = 17755919) B17755919
theorem B4046699 : Blo 1596997 4046699 := bstep (se 1 (by rfl) ⟨3035024, by rfl⟩ : syracuseStep 4046699 = 6070049) B6070049
theorem B1597307 : Blo 1596997 1597307 := bstep (se 1 (by rfl) ⟨1197980, by rfl⟩ : syracuseStep 1597307 = 2395961) B2395961
theorem B1597359 : Blo 1596997 1597359 := bstep (se 1 (by rfl) ⟨1198019, by rfl⟩ : syracuseStep 1597359 = 2396039) B2396039
theorem B10239929 : Blo 1596997 10239929 := bstep (se 2 (by rfl) ⟨3839973, by rfl⟩ : syracuseStep 10239929 = 7679947) B7679947
theorem B2695099 : Blo 1596997 2695099 := bstep (se 1 (by rfl) ⟨2021324, by rfl⟩ : syracuseStep 2695099 = 4042649) B4042649
theorem B3596219 : Blo 1596997 3596219 := bstep (se 1 (by rfl) ⟨2697164, by rfl⟩ : syracuseStep 3596219 = 5394329) B5394329
theorem B1597383 : Blo 1596997 1597383 := bstep (se 1 (by rfl) ⟨1198037, by rfl⟩ : syracuseStep 1597383 = 2396075) B2396075
theorem B10928081 : Blo 1596997 10928081 := bstep (se 2 (by rfl) ⟨4098030, by rfl⟩ : syracuseStep 10928081 = 8196061) B8196061
theorem B1597403 : Blo 1596997 1597403 := bstep (se 1 (by rfl) ⟨1198052, by rfl⟩ : syracuseStep 1597403 = 2396105) B2396105
theorem B5390441 : Blo 1596997 5390441 := bstep (se 2 (by rfl) ⟨2021415, by rfl⟩ : syracuseStep 5390441 = 4042831) B4042831
theorem B2023643 : Blo 1596997 2023643 := bstep (se 1 (by rfl) ⟨1517732, by rfl⟩ : syracuseStep 2023643 = 3035465) B3035465
theorem B1597727 : Blo 1596997 1597727 := bstep (se 1 (by rfl) ⟨1198295, by rfl⟩ : syracuseStep 1597727 = 2396591) B2396591
theorem B1597787 : Blo 1596997 1597787 := bstep (se 1 (by rfl) ⟨1198340, by rfl⟩ : syracuseStep 1597787 = 2396681) B2396681
theorem B19439963 : Blo 1596997 19439963 := bstep (se 1 (by rfl) ⟨14579972, by rfl⟩ : syracuseStep 19439963 = 29159945) B29159945
theorem B3596651 : Blo 1596997 3596651 := bstep (se 1 (by rfl) ⟨2697488, by rfl⟩ : syracuseStep 3596651 = 5394977) B5394977
theorem B1597807 : Blo 1596997 1597807 := bstep (se 1 (by rfl) ⟨1198355, by rfl⟩ : syracuseStep 1597807 = 2396711) B2396711
theorem B1597863 : Blo 1596997 1597863 := bstep (se 1 (by rfl) ⟨1198397, by rfl⟩ : syracuseStep 1597863 = 2396795) B2396795
theorem B1597947 : Blo 1596997 1597947 := bstep (se 1 (by rfl) ⟨1198460, by rfl⟩ : syracuseStep 1597947 = 2396921) B2396921
theorem B3596795 : Blo 1596997 3596795 := bstep (se 1 (by rfl) ⟨2697596, by rfl⟩ : syracuseStep 3596795 = 5395193) B5395193
theorem B8086067 : Blo 1596997 8086067 := bstep (se 1 (by rfl) ⟨6064550, by rfl⟩ : syracuseStep 8086067 = 12129101) B12129101
theorem B1598015 : Blo 1596997 1598015 := bstep (se 1 (by rfl) ⟨1198511, by rfl⟩ : syracuseStep 1598015 = 2397023) B2397023
theorem B6824519 : Blo 1596997 6824519 := bstep (se 1 (by rfl) ⟨5118389, by rfl⟩ : syracuseStep 6824519 = 10236779) B10236779
theorem B1598023 : Blo 1596997 1598023 := bstep (se 1 (by rfl) ⟨1198517, by rfl⟩ : syracuseStep 1598023 = 2397035) B2397035
theorem B2695801 : Blo 1596997 2695801 := bstep (se 2 (by rfl) ⟨1010925, by rfl⟩ : syracuseStep 2695801 = 2021851) B2021851
theorem B3596921 : Blo 1596997 3596921 := bstep (se 2 (by rfl) ⟨1348845, by rfl⟩ : syracuseStep 3596921 = 2697691) B2697691
theorem B8094329 : Blo 1596997 8094329 := bstep (se 2 (by rfl) ⟨3035373, by rfl⟩ : syracuseStep 8094329 = 6070747) B6070747
theorem B13656721 : Blo 1596997 13656721 := bstep (se 2 (by rfl) ⟨5121270, by rfl⟩ : syracuseStep 13656721 = 10242541) B10242541
theorem B2695855 : Blo 1596997 2695855 := bstep (se 1 (by rfl) ⟨2021891, by rfl⟩ : syracuseStep 2695855 = 4043783) B4043783
theorem B3596975 : Blo 1596997 3596975 := bstep (se 1 (by rfl) ⟨2697731, by rfl⟩ : syracuseStep 3596975 = 5395463) B5395463
theorem B1598175 : Blo 1596997 1598175 := bstep (se 1 (by rfl) ⟨1198631, by rfl⟩ : syracuseStep 1598175 = 2397263) B2397263
theorem B3597047 : Blo 1596997 3597047 := bstep (se 1 (by rfl) ⟨2697785, by rfl⟩ : syracuseStep 3597047 = 5395571) B5395571
theorem B1598255 : Blo 1596997 1598255 := bstep (se 1 (by rfl) ⟨1198691, by rfl⟩ : syracuseStep 1598255 = 2397383) B2397383
theorem B1598363 : Blo 1596997 1598363 := bstep (se 1 (by rfl) ⟨1198772, by rfl⟩ : syracuseStep 1598363 = 2397545) B2397545
theorem B3597227 : Blo 1596997 3597227 := bstep (se 1 (by rfl) ⟨2697920, by rfl⟩ : syracuseStep 3597227 = 5395841) B5395841
theorem B14582711 : Blo 1596997 14582711 := bstep (se 1 (by rfl) ⟨10937033, by rfl⟩ : syracuseStep 14582711 = 21874067) B21874067
theorem B5391305 : Blo 1596997 5391305 := bstep (se 2 (by rfl) ⟨2021739, by rfl⟩ : syracuseStep 5391305 = 4043479) B4043479
theorem B1598415 : Blo 1596997 1598415 := bstep (se 1 (by rfl) ⟨1198811, by rfl⟩ : syracuseStep 1598415 = 2397623) B2397623
theorem B1598439 : Blo 1596997 1598439 := bstep (se 1 (by rfl) ⟨1198829, by rfl⟩ : syracuseStep 1598439 = 2397659) B2397659
theorem B9716773 : Blo 1596997 9716773 := bstep (se 4 (by rfl) ⟨910947, by rfl⟩ : syracuseStep 9716773 = 1821895) B1821895
theorem B18211877 : Blo 1596997 18211877 := bstep (se 4 (by rfl) ⟨1707363, by rfl⟩ : syracuseStep 18211877 = 3414727) B3414727
theorem B12297359 : Blo 1596997 12297359 := bstep (se 1 (by rfl) ⟨9223019, by rfl⟩ : syracuseStep 12297359 = 18446039) B18446039
theorem B5391575 : Blo 1596997 5391575 := bstep (se 1 (by rfl) ⟨4043681, by rfl⟩ : syracuseStep 5391575 = 8087363) B8087363
theorem B1598751 : Blo 1596997 1598751 := bstep (se 1 (by rfl) ⟨1199063, by rfl⟩ : syracuseStep 1598751 = 2398127) B2398127
theorem B1598811 : Blo 1596997 1598811 := bstep (se 1 (by rfl) ⟨1199108, by rfl⟩ : syracuseStep 1598811 = 2398217) B2398217
theorem B1598831 : Blo 1596997 1598831 := bstep (se 1 (by rfl) ⟨1199123, by rfl⟩ : syracuseStep 1598831 = 2398247) B2398247
theorem B5916043 : Blo 1596997 5916043 := bstep (se 1 (by rfl) ⟨4437032, by rfl⟩ : syracuseStep 5916043 = 8874065) B8874065
theorem B1598887 : Blo 1596997 1598887 := bstep (se 1 (by rfl) ⟨1199165, by rfl⟩ : syracuseStep 1598887 = 2398331) B2398331
theorem B1598971 : Blo 1596997 1598971 := bstep (se 1 (by rfl) ⟨1199228, by rfl⟩ : syracuseStep 1598971 = 2398457) B2398457
theorem B16401977 : Blo 1596997 16401977 := bstep (se 2 (by rfl) ⟨6150741, by rfl⟩ : syracuseStep 16401977 = 12301483) B12301483
theorem B27666137 : Blo 1596997 27666137 := bstep (se 2 (by rfl) ⟨10374801, by rfl⟩ : syracuseStep 27666137 = 20749603) B20749603
theorem B17278753 : Blo 1596997 17278753 := bstep (se 2 (by rfl) ⟨6479532, by rfl⟩ : syracuseStep 17278753 = 12959065) B12959065
theorem B6825833 : Blo 1596997 6825833 := bstep (se 2 (by rfl) ⟨2559687, by rfl⟩ : syracuseStep 6825833 = 5119375) B5119375
theorem B4319257 : Blo 1596997 4319257 := bstep (se 2 (by rfl) ⟨1619721, by rfl⟩ : syracuseStep 4319257 = 3239443) B3239443
theorem B8087687 : Blo 1596997 8087687 := bstep (se 1 (by rfl) ⟨6065765, by rfl⟩ : syracuseStep 8087687 = 12131531) B12131531
theorem B98388209 : Blo 1596997 98388209 := bstep (se 2 (by rfl) ⟨36895578, by rfl⟩ : syracuseStep 98388209 = 73791157) B73791157
theorem B2697563 : Blo 1596997 2697563 := bstep (se 1 (by rfl) ⟨2023172, by rfl⟩ : syracuseStep 2697563 = 4046345) B4046345
theorem B2697583 : Blo 1596997 2697583 := bstep (se 1 (by rfl) ⟨2023187, by rfl⟩ : syracuseStep 2697583 = 4046375) B4046375
theorem B2558375 : Blo 1596997 2558375 := bstep (se 1 (by rfl) ⟨1918781, by rfl⟩ : syracuseStep 2558375 = 3837563) B3837563
theorem B9095597 : Blo 1596997 9095597 := bstep (se 3 (by rfl) ⟨1705424, by rfl⟩ : syracuseStep 9095597 = 3410849) B3410849
theorem B6064703 : Blo 1596997 6064703 := bstep (se 1 (by rfl) ⟨4548527, by rfl⟩ : syracuseStep 6064703 = 9097055) B9097055
theorem B7891519 : Blo 1596997 7891519 := bstep (se 1 (by rfl) ⟨5918639, by rfl⟩ : syracuseStep 7891519 = 11837279) B11837279
theorem B2697799 : Blo 1596997 2697799 := bstep (se 1 (by rfl) ⟨2023349, by rfl⟩ : syracuseStep 2697799 = 4046699) B4046699
theorem B2558585 : Blo 1596997 2558585 := bstep (se 2 (by rfl) ⟨959469, by rfl⟩ : syracuseStep 2558585 = 1918939) B1918939
theorem B6826619 : Blo 1596997 6826619 := bstep (se 1 (by rfl) ⟨5119964, by rfl⟩ : syracuseStep 6826619 = 10239929) B10239929
theorem B7285387 : Blo 1596997 7285387 := bstep (se 1 (by rfl) ⟨5464040, by rfl⟩ : syracuseStep 7285387 = 10928081) B10928081
theorem B6916747 : Blo 1596997 6916747 := bstep (se 1 (by rfl) ⟨5187560, by rfl⟩ : syracuseStep 6916747 = 10375121) B10375121
theorem B6064915 : Blo 1596997 6064915 := bstep (se 1 (by rfl) ⟨4548686, by rfl⟩ : syracuseStep 6064915 = 9097373) B9097373
theorem B14584643 : Blo 1596997 14584643 := bstep (se 1 (by rfl) ⟨10938482, by rfl⟩ : syracuseStep 14584643 = 21876965) B21876965
theorem B2051023 : Blo 1596997 2051023 := bstep (se 1 (by rfl) ⟨1538267, by rfl⟩ : syracuseStep 2051023 = 3076535) B3076535
theorem B2698231 : Blo 1596997 2698231 := bstep (se 1 (by rfl) ⟨2023673, by rfl⟩ : syracuseStep 2698231 = 4047347) B4047347
theorem B8637455 : Blo 1596997 8637455 := bstep (se 1 (by rfl) ⟨6478091, by rfl⟩ : syracuseStep 8637455 = 12956183) B12956183
theorem B5393627 : Blo 1596997 5393627 := bstep (se 1 (by rfl) ⟨4045220, by rfl⟩ : syracuseStep 5393627 = 8090441) B8090441
theorem B5762267 : Blo 1596997 5762267 := bstep (se 1 (by rfl) ⟨4321700, by rfl⟩ : syracuseStep 5762267 = 8643401) B8643401
theorem B2878697 : Blo 1596997 2878697 := bstep (se 2 (by rfl) ⟨1079511, by rfl⟩ : syracuseStep 2878697 = 2159023) B2159023
theorem B2395529 : Blo 1596997 2395529 := bstep (se 2 (by rfl) ⟨898323, by rfl⟩ : syracuseStep 2395529 = 1796647) B1796647
theorem B93392453 : Blo 1596997 93392453 := bstep (se 4 (by rfl) ⟨8755542, by rfl⟩ : syracuseStep 93392453 = 17511085) B17511085
theorem B1797727 : Blo 1596997 1797727 := bstep (se 1 (by rfl) ⟨1348295, by rfl⟩ : syracuseStep 1797727 = 2696591) B2696591
theorem B14585453 : Blo 1596997 14585453 := bstep (se 3 (by rfl) ⟨2734772, by rfl⟩ : syracuseStep 14585453 = 5469545) B5469545
theorem B11521709 : Blo 1596997 11521709 := bstep (se 3 (by rfl) ⟨2160320, by rfl⟩ : syracuseStep 11521709 = 4320641) B4320641
theorem B2395883 : Blo 1596997 2395883 := bstep (se 1 (by rfl) ⟨1796912, by rfl⟩ : syracuseStep 2395883 = 3593825) B3593825
theorem B6827951 : Blo 1596997 6827951 := bstep (se 1 (by rfl) ⟨5120963, by rfl⟩ : syracuseStep 6827951 = 10241927) B10241927
theorem B2396111 : Blo 1596997 2396111 := bstep (se 1 (by rfl) ⟨1797083, by rfl⟩ : syracuseStep 2396111 = 3594167) B3594167
theorem B4550681 : Blo 1596997 4550681 := bstep (se 2 (by rfl) ⟨1706505, by rfl⟩ : syracuseStep 4550681 = 3413011) B3413011
theorem B5394491 : Blo 1596997 5394491 := bstep (se 1 (by rfl) ⟨4045868, by rfl⟩ : syracuseStep 5394491 = 8091737) B8091737
theorem B20476061 : Blo 1596997 20476061 := bstep (se 3 (by rfl) ⟨3839261, by rfl⟩ : syracuseStep 20476061 = 7678523) B7678523
theorem B4673747 : Blo 1596997 4673747 := bstep (se 1 (by rfl) ⟨3505310, by rfl⟩ : syracuseStep 4673747 = 7010621) B7010621
theorem B5394761 : Blo 1596997 5394761 := bstep (se 2 (by rfl) ⟨2023035, by rfl⟩ : syracuseStep 5394761 = 4046071) B4046071
theorem B2396507 : Blo 1596997 2396507 := bstep (se 1 (by rfl) ⟨1797380, by rfl⟩ : syracuseStep 2396507 = 3594761) B3594761
theorem B17985899 : Blo 1596997 17985899 := bstep (se 1 (by rfl) ⟨13489424, by rfl⟩ : syracuseStep 17985899 = 26978849) B26978849
theorem B4551137 : Blo 1596997 4551137 := bstep (se 2 (by rfl) ⟨1706676, by rfl⟩ : syracuseStep 4551137 = 3413353) B3413353
theorem B2396735 : Blo 1596997 2396735 := bstep (se 1 (by rfl) ⟨1797551, by rfl⟩ : syracuseStep 2396735 = 3595103) B3595103
theorem B2732617 : Blo 1596997 2732617 := bstep (se 2 (by rfl) ⟨1024731, by rfl⟩ : syracuseStep 2732617 = 2049463) B2049463
theorem B3412601 : Blo 1596997 3412601 := bstep (se 2 (by rfl) ⟨1279725, by rfl⟩ : syracuseStep 3412601 = 2559451) B2559451
theorem B6066859 : Blo 1596997 6066859 := bstep (se 1 (by rfl) ⟨4550144, by rfl⟩ : syracuseStep 6066859 = 9100289) B9100289
theorem B32813747 : Blo 1596997 32813747 := bstep (se 1 (by rfl) ⟨24610310, by rfl⟩ : syracuseStep 32813747 = 49220621) B49220621
theorem B2396855 : Blo 1596997 2396855 := bstep (se 1 (by rfl) ⟨1797641, by rfl⟩ : syracuseStep 2396855 = 3595283) B3595283
theorem B2397083 : Blo 1596997 2397083 := bstep (se 1 (by rfl) ⟨1797812, by rfl⟩ : syracuseStep 2397083 = 3595625) B3595625
theorem B7779233 : Blo 1596997 7779233 := bstep (se 2 (by rfl) ⟨2917212, by rfl⟩ : syracuseStep 7779233 = 5834425) B5834425
theorem B8205257 : Blo 1596997 8205257 := bstep (se 2 (by rfl) ⟨3076971, by rfl⟩ : syracuseStep 8205257 = 6153943) B6153943
theorem B6067163 : Blo 1596997 6067163 := bstep (se 1 (by rfl) ⟨4550372, by rfl⟩ : syracuseStep 6067163 = 9100745) B9100745
theorem B9221111 : Blo 1596997 9221111 := bstep (se 1 (by rfl) ⟨6915833, by rfl⟩ : syracuseStep 9221111 = 13831667) B13831667
theorem B18445391 : Blo 1596997 18445391 := bstep (se 1 (by rfl) ⟨13834043, by rfl⟩ : syracuseStep 18445391 = 27668087) B27668087
theorem B3593339 : Blo 1596997 3593339 := bstep (se 1 (by rfl) ⟨2695004, by rfl⟩ : syracuseStep 3593339 = 5390009) B5390009
theorem B6829181 : Blo 1596997 6829181 := bstep (se 3 (by rfl) ⟨1280471, by rfl⟩ : syracuseStep 6829181 = 2560943) B2560943
theorem B4043915 : Blo 1596997 4043915 := bstep (se 1 (by rfl) ⟨3032936, by rfl⟩ : syracuseStep 4043915 = 6065873) B6065873
theorem B26277011 : Blo 1596997 26277011 := bstep (se 1 (by rfl) ⟨19707758, by rfl⟩ : syracuseStep 26277011 = 39415517) B39415517
theorem B9106577 : Blo 1596997 9106577 := bstep (se 2 (by rfl) ⟨3414966, by rfl⟩ : syracuseStep 9106577 = 6829933) B6829933
theorem B11834525 : Blo 1596997 11834525 := bstep (se 3 (by rfl) ⟨2218973, by rfl⟩ : syracuseStep 11834525 = 4437947) B4437947
theorem B3593465 : Blo 1596997 3593465 := bstep (se 2 (by rfl) ⟨1347549, by rfl⟩ : syracuseStep 3593465 = 2695099) B2695099
theorem B2397479 : Blo 1596997 2397479 := bstep (se 1 (by rfl) ⟨1798109, by rfl⟩ : syracuseStep 2397479 = 3596219) B3596219
theorem B4044127 : Blo 1596997 4044127 := bstep (se 1 (by rfl) ⟨3033095, by rfl⟩ : syracuseStep 4044127 = 6066191) B6066191
theorem B2397563 : Blo 1596997 2397563 := bstep (se 1 (by rfl) ⟨1798172, by rfl⟩ : syracuseStep 2397563 = 3596345) B3596345
theorem B3593609 : Blo 1596997 3593609 := bstep (se 2 (by rfl) ⟨1347603, by rfl⟩ : syracuseStep 3593609 = 2695207) B2695207
theorem B3413497 : Blo 1596997 3413497 := bstep (se 2 (by rfl) ⟨1280061, by rfl⟩ : syracuseStep 3413497 = 2560123) B2560123
theorem B2397689 : Blo 1596997 2397689 := bstep (se 2 (by rfl) ⟨899133, by rfl⟩ : syracuseStep 2397689 = 1798267) B1798267
theorem B3593735 : Blo 1596997 3593735 := bstep (se 1 (by rfl) ⟨2695301, by rfl⟩ : syracuseStep 3593735 = 5390603) B5390603
theorem B2078303 : Blo 1596997 2078303 := bstep (se 1 (by rfl) ⟨1558727, by rfl⟩ : syracuseStep 2078303 = 3117455) B3117455
theorem B2397791 : Blo 1596997 2397791 := bstep (se 1 (by rfl) ⟨1798343, by rfl⟩ : syracuseStep 2397791 = 3596687) B3596687
theorem B3593915 : Blo 1596997 3593915 := bstep (se 1 (by rfl) ⟨2695436, by rfl⟩ : syracuseStep 3593915 = 5390873) B5390873
theorem B2398007 : Blo 1596997 2398007 := bstep (se 1 (by rfl) ⟨1798505, by rfl⟩ : syracuseStep 2398007 = 3597011) B3597011
theorem B3594041 : Blo 1596997 3594041 := bstep (se 2 (by rfl) ⟨1347765, by rfl⟩ : syracuseStep 3594041 = 2695531) B2695531
theorem B8091575 : Blo 1596997 8091575 := bstep (se 1 (by rfl) ⟨6068681, by rfl⟩ : syracuseStep 8091575 = 12137363) B12137363
theorem B6821921 : Blo 1596997 6821921 := bstep (se 2 (by rfl) ⟨2558220, by rfl⟩ : syracuseStep 6821921 = 5116441) B5116441
theorem B2398313 : Blo 1596997 2398313 := bstep (se 2 (by rfl) ⟨899367, by rfl⟩ : syracuseStep 2398313 = 1798735) B1798735
theorem B5920897 : Blo 1596997 5920897 := bstep (se 2 (by rfl) ⟨2220336, by rfl⟩ : syracuseStep 5920897 = 4440673) B4440673
theorem B6822073 : Blo 1596997 6822073 := bstep (se 2 (by rfl) ⟨2558277, by rfl⟩ : syracuseStep 6822073 = 5116555) B5116555
theorem B6068591 : Blo 1596997 6068591 := bstep (se 1 (by rfl) ⟨4551443, by rfl⟩ : syracuseStep 6068591 = 9102887) B9102887
theorem B2021755 : Blo 1596997 2021755 := bstep (se 1 (by rfl) ⟨1516316, by rfl⟩ : syracuseStep 2021755 = 3032633) B3032633
theorem B3594671 : Blo 1596997 3594671 := bstep (se 1 (by rfl) ⟨2696003, by rfl⟩ : syracuseStep 3594671 = 5392007) B5392007
theorem B3594707 : Blo 1596997 3594707 := bstep (se 1 (by rfl) ⟨2696030, by rfl⟩ : syracuseStep 3594707 = 5392061) B5392061
theorem B3594815 : Blo 1596997 3594815 := bstep (se 1 (by rfl) ⟨2696111, by rfl⟩ : syracuseStep 3594815 = 5392223) B5392223
theorem B8092223 : Blo 1596997 8092223 := bstep (se 1 (by rfl) ⟨6069167, by rfl⟩ : syracuseStep 8092223 = 12138335) B12138335
theorem B27302507 : Blo 1596997 27302507 := bstep (se 1 (by rfl) ⟨20476880, by rfl⟩ : syracuseStep 27302507 = 40953761) B40953761
theorem B3594923 : Blo 1596997 3594923 := bstep (se 1 (by rfl) ⟨2696192, by rfl⟩ : syracuseStep 3594923 = 5392385) B5392385
theorem B9099971 : Blo 1596997 9099971 := bstep (se 1 (by rfl) ⟨6824978, by rfl⟩ : syracuseStep 9099971 = 13649957) B13649957
theorem B4045535 : Blo 1596997 4045535 := bstep (se 1 (by rfl) ⟨3034151, by rfl⟩ : syracuseStep 4045535 = 6068303) B6068303
theorem B116562725 : Blo 1596997 116562725 := bstep (se 4 (by rfl) ⟨10927755, by rfl⟩ : syracuseStep 116562725 = 21855511) B21855511
theorem B15359165 : Blo 1596997 15359165 := bstep (se 3 (by rfl) ⟨2879843, by rfl⟩ : syracuseStep 15359165 = 5759687) B5759687
theorem B3595463 : Blo 1596997 3595463 := bstep (se 1 (by rfl) ⟨2696597, by rfl⟩ : syracuseStep 3595463 = 5393195) B5393195
theorem B3595643 : Blo 1596997 3595643 := bstep (se 1 (by rfl) ⟨2696732, by rfl⟩ : syracuseStep 3595643 = 5393465) B5393465
theorem B2022823 : Blo 1596997 2022823 := bstep (se 1 (by rfl) ⟨1517117, by rfl⟩ : syracuseStep 2022823 = 3034235) B3034235
theorem B3595769 : Blo 1596997 3595769 := bstep (se 2 (by rfl) ⟨1348413, by rfl⟩ : syracuseStep 3595769 = 2696827) B2696827
theorem B6069775 : Blo 1596997 6069775 := bstep (se 1 (by rfl) ⟨4552331, by rfl⟩ : syracuseStep 6069775 = 9104663) B9104663
theorem B7683599 : Blo 1596997 7683599 := bstep (se 1 (by rfl) ⟨5762699, by rfl⟩ : syracuseStep 7683599 = 11525399) B11525399
theorem B1596999 : Blo 1596997 1596999 := bstep (se 1 (by rfl) ⟨1197749, by rfl⟩ : syracuseStep 1596999 = 2395499) B2395499
theorem B3595859 : Blo 1596997 3595859 := bstep (se 1 (by rfl) ⟨2696894, by rfl⟩ : syracuseStep 3595859 = 5393789) B5393789
theorem B18210419 : Blo 1596997 18210419 := bstep (se 1 (by rfl) ⟨13657814, by rfl⟩ : syracuseStep 18210419 = 27315629) B27315629
theorem B5463713 : Blo 1596997 5463713 := bstep (se 2 (by rfl) ⟨2048892, by rfl⟩ : syracuseStep 5463713 = 4097785) B4097785
theorem B1597151 : Blo 1596997 1597151 := bstep (se 1 (by rfl) ⟨1197863, by rfl⟩ : syracuseStep 1597151 = 2395727) B2395727
theorem B2023147 : Blo 1596997 2023147 := bstep (se 1 (by rfl) ⟨1517360, by rfl⟩ : syracuseStep 2023147 = 3034721) B3034721
theorem B3596039 : Blo 1596997 3596039 := bstep (se 1 (by rfl) ⟨2697029, by rfl⟩ : syracuseStep 3596039 = 5394059) B5394059
theorem B1597231 : Blo 1596997 1597231 := bstep (se 1 (by rfl) ⟨1197923, by rfl⟩ : syracuseStep 1597231 = 2395847) B2395847
theorem B14573371 : Blo 1596997 14573371 := bstep (se 1 (by rfl) ⟨10930028, by rfl⟩ : syracuseStep 14573371 = 21860057) B21860057
theorem B1597339 : Blo 1596997 1597339 := bstep (se 1 (by rfl) ⟨1198004, by rfl⟩ : syracuseStep 1597339 = 2396009) B2396009
theorem B1597391 : Blo 1596997 1597391 := bstep (se 1 (by rfl) ⟨1198043, by rfl⟩ : syracuseStep 1597391 = 2396087) B2396087
theorem B2023375 : Blo 1596997 2023375 := bstep (se 1 (by rfl) ⟨1517531, by rfl⟩ : syracuseStep 2023375 = 3035063) B3035063
theorem B1597415 : Blo 1596997 1597415 := bstep (se 1 (by rfl) ⟨1198061, by rfl⟩ : syracuseStep 1597415 = 2396123) B2396123
theorem B5759009 : Blo 1596997 5759009 := bstep (se 2 (by rfl) ⟨2159628, by rfl⟩ : syracuseStep 5759009 = 4319257) B4319257
theorem B3596327 : Blo 1596997 3596327 := bstep (se 1 (by rfl) ⟨2697245, by rfl⟩ : syracuseStep 3596327 = 5394491) B5394491
theorem B3596507 : Blo 1596997 3596507 := bstep (se 1 (by rfl) ⟨2697380, by rfl⟩ : syracuseStep 3596507 = 5394761) B5394761
theorem B1597671 : Blo 1596997 1597671 := bstep (se 1 (by rfl) ⟨1198253, by rfl⟩ : syracuseStep 1597671 = 2396507) B2396507
theorem B12959975 : Blo 1596997 12959975 := bstep (se 1 (by rfl) ⟨9719981, by rfl⟩ : syracuseStep 12959975 = 19439963) B19439963
theorem B5390711 : Blo 1596997 5390711 := bstep (se 1 (by rfl) ⟨4043033, by rfl⟩ : syracuseStep 5390711 = 8086067) B8086067
theorem B32792957 : Blo 1596997 32792957 := bstep (se 3 (by rfl) ⟨6148679, by rfl⟩ : syracuseStep 32792957 = 12297359) B12297359
theorem B1597823 : Blo 1596997 1597823 := bstep (se 1 (by rfl) ⟨1198367, by rfl⟩ : syracuseStep 1597823 = 2396735) B2396735
theorem B1597903 : Blo 1596997 1597903 := bstep (se 1 (by rfl) ⟨1198427, by rfl⟩ : syracuseStep 1597903 = 2396855) B2396855
theorem B3596777 : Blo 1596997 3596777 := bstep (se 2 (by rfl) ⟨1348791, by rfl⟩ : syracuseStep 3596777 = 2697583) B2697583
theorem B2695673 : Blo 1596997 2695673 := bstep (se 2 (by rfl) ⟨1010877, by rfl⟩ : syracuseStep 2695673 = 2021755) B2021755
theorem B1598055 : Blo 1596997 1598055 := bstep (se 1 (by rfl) ⟨1198541, by rfl⟩ : syracuseStep 1598055 = 2397083) B2397083
theorem B5186155 : Blo 1596997 5186155 := bstep (se 1 (by rfl) ⟨3889616, by rfl⟩ : syracuseStep 5186155 = 7779233) B7779233
theorem B7676525 : Blo 1596997 7676525 := bstep (se 3 (by rfl) ⟨1439348, by rfl⟩ : syracuseStep 7676525 = 2878697) B2878697
theorem B12141251 : Blo 1596997 12141251 := bstep (se 1 (by rfl) ⟨9105938, by rfl⟩ : syracuseStep 12141251 = 18211877) B18211877
theorem B12296927 : Blo 1596997 12296927 := bstep (se 1 (by rfl) ⟨9222695, by rfl⟩ : syracuseStep 12296927 = 18445391) B18445391
theorem B2695943 : Blo 1596997 2695943 := bstep (se 1 (by rfl) ⟨2021957, by rfl⟩ : syracuseStep 2695943 = 4043915) B4043915
theorem B3597065 : Blo 1596997 3597065 := bstep (se 2 (by rfl) ⟨1348899, by rfl⟩ : syracuseStep 3597065 = 2697799) B2697799
theorem B6071051 : Blo 1596997 6071051 := bstep (se 1 (by rfl) ⟨4553288, by rfl⟩ : syracuseStep 6071051 = 9106577) B9106577
theorem B7889683 : Blo 1596997 7889683 := bstep (se 1 (by rfl) ⟨5917262, by rfl⟩ : syracuseStep 7889683 = 11834525) B11834525
theorem B1598319 : Blo 1596997 1598319 := bstep (se 1 (by rfl) ⟨1198739, by rfl⟩ : syracuseStep 1598319 = 2397479) B2397479
theorem B1598375 : Blo 1596997 1598375 := bstep (se 1 (by rfl) ⟨1198781, by rfl⟩ : syracuseStep 1598375 = 2397563) B2397563
theorem B1598459 : Blo 1596997 1598459 := bstep (se 1 (by rfl) ⟨1198844, by rfl⟩ : syracuseStep 1598459 = 2397689) B2397689
theorem B8086553 : Blo 1596997 8086553 := bstep (se 2 (by rfl) ⟨3032457, by rfl⟩ : syracuseStep 8086553 = 6064915) B6064915
theorem B1598527 : Blo 1596997 1598527 := bstep (se 1 (by rfl) ⟨1198895, by rfl⟩ : syracuseStep 1598527 = 2397791) B2397791
theorem B1598671 : Blo 1596997 1598671 := bstep (se 1 (by rfl) ⟨1199003, by rfl⟩ : syracuseStep 1598671 = 2398007) B2398007
theorem B3597641 : Blo 1596997 3597641 := bstep (se 2 (by rfl) ⟨1349115, by rfl⟩ : syracuseStep 3597641 = 2698231) B2698231
theorem B4547947 : Blo 1596997 4547947 := bstep (se 1 (by rfl) ⟨3410960, by rfl⟩ : syracuseStep 4547947 = 6821921) B6821921
theorem B1598875 : Blo 1596997 1598875 := bstep (se 1 (by rfl) ⟨1199156, by rfl⟩ : syracuseStep 1598875 = 2398313) B2398313
theorem B5391791 : Blo 1596997 5391791 := bstep (se 1 (by rfl) ⟨4043843, by rfl⟩ : syracuseStep 5391791 = 8087687) B8087687
theorem B1705583 : Blo 1596997 1705583 := bstep (se 1 (by rfl) ⟨1279187, by rfl⟩ : syracuseStep 1705583 = 2558375) B2558375
theorem B6063731 : Blo 1596997 6063731 := bstep (se 1 (by rfl) ⟨4547798, by rfl⟩ : syracuseStep 6063731 = 9095597) B9095597
theorem B5392169 : Blo 1596997 5392169 := bstep (se 2 (by rfl) ⟨2022063, by rfl⟩ : syracuseStep 5392169 = 4044127) B4044127
theorem B2697023 : Blo 1596997 2697023 := bstep (se 1 (by rfl) ⟨2022767, by rfl⟩ : syracuseStep 2697023 = 4045535) B4045535
theorem B2697097 : Blo 1596997 2697097 := bstep (se 2 (by rfl) ⟨1011411, by rfl⟩ : syracuseStep 2697097 = 2022823) B2022823
theorem B2697529 : Blo 1596997 2697529 := bstep (se 2 (by rfl) ⟨1011573, by rfl⟩ : syracuseStep 2697529 = 2023147) B2023147
theorem B5122399 : Blo 1596997 5122399 := bstep (se 1 (by rfl) ⟨3841799, by rfl⟩ : syracuseStep 5122399 = 7683599) B7683599
theorem B23038337 : Blo 1596997 23038337 := bstep (se 2 (by rfl) ⟨8639376, by rfl⟩ : syracuseStep 23038337 = 17278753) B17278753
theorem B62261635 : Blo 1596997 62261635 := bstep (se 1 (by rfl) ⟨46696226, by rfl⟩ : syracuseStep 62261635 = 93392453) B93392453
theorem B2697833 : Blo 1596997 2697833 := bstep (se 2 (by rfl) ⟨1011687, by rfl⟩ : syracuseStep 2697833 = 2023375) B2023375
theorem B3033787 : Blo 1596997 3033787 := bstep (se 1 (by rfl) ⟨2275340, by rfl⟩ : syracuseStep 3033787 = 4550681) B4550681
theorem B13650707 : Blo 1596997 13650707 := bstep (se 1 (by rfl) ⟨10238030, by rfl⟩ : syracuseStep 13650707 = 20476061) B20476061
theorem B3115831 : Blo 1596997 3115831 := bstep (se 1 (by rfl) ⟨2336873, by rfl⟩ : syracuseStep 3115831 = 4673747) B4673747
theorem B9096097 : Blo 1596997 9096097 := bstep (se 2 (by rfl) ⟨3411036, by rfl⟩ : syracuseStep 9096097 = 6822073) B6822073
theorem B3034091 : Blo 1596997 3034091 := bstep (se 1 (by rfl) ⟨2275568, by rfl⟩ : syracuseStep 3034091 = 4551137) B4551137
theorem B4549679 : Blo 1596997 4549679 := bstep (se 1 (by rfl) ⟨3412259, by rfl⟩ : syracuseStep 4549679 = 6824519) B6824519
theorem B21875831 : Blo 1596997 21875831 := bstep (se 1 (by rfl) ⟨16406873, by rfl⟩ : syracuseStep 21875831 = 32813747) B32813747
theorem B6147407 : Blo 1596997 6147407 := bstep (se 1 (by rfl) ⟨4610555, by rfl⟩ : syracuseStep 6147407 = 9221111) B9221111
theorem B2395559 : Blo 1596997 2395559 := bstep (se 1 (by rfl) ⟨1796669, by rfl⟩ : syracuseStep 2395559 = 3593339) B3593339
theorem B10522025 : Blo 1596997 10522025 := bstep (se 2 (by rfl) ⟨3945759, by rfl⟩ : syracuseStep 10522025 = 7891519) B7891519
theorem B17518007 : Blo 1596997 17518007 := bstep (se 1 (by rfl) ⟨13138505, by rfl⟩ : syracuseStep 17518007 = 26277011) B26277011
theorem B2395643 : Blo 1596997 2395643 := bstep (se 1 (by rfl) ⟨1796732, by rfl⟩ : syracuseStep 2395643 = 3593465) B3593465
theorem B8089145 : Blo 1596997 8089145 := bstep (se 2 (by rfl) ⟨3033429, by rfl⟩ : syracuseStep 8089145 = 6066859) B6066859
theorem B2395739 : Blo 1596997 2395739 := bstep (se 1 (by rfl) ⟨1796804, by rfl⟩ : syracuseStep 2395739 = 3593609) B3593609
theorem B2395823 : Blo 1596997 2395823 := bstep (se 1 (by rfl) ⟨1796867, by rfl⟩ : syracuseStep 2395823 = 3593735) B3593735
theorem B2395943 : Blo 1596997 2395943 := bstep (se 1 (by rfl) ⟨1796957, by rfl⟩ : syracuseStep 2395943 = 3593915) B3593915
theorem B2396027 : Blo 1596997 2396027 := bstep (se 1 (by rfl) ⟨1797020, by rfl⟩ : syracuseStep 2396027 = 3594041) B3594041
theorem B4550555 : Blo 1596997 4550555 := bstep (se 1 (by rfl) ⟨3412916, by rfl⟩ : syracuseStep 4550555 = 6825833) B6825833
theorem B5394383 : Blo 1596997 5394383 := bstep (se 1 (by rfl) ⟨4045787, by rfl⟩ : syracuseStep 5394383 = 8091575) B8091575
theorem B12955697 : Blo 1596997 12955697 := bstep (se 2 (by rfl) ⟨4858386, by rfl⟩ : syracuseStep 12955697 = 9716773) B9716773
theorem B1798375 : Blo 1596997 1798375 := bstep (se 1 (by rfl) ⟨1348781, by rfl⟩ : syracuseStep 1798375 = 2697563) B2697563
theorem B5542141 : Blo 1596997 5542141 := bstep (se 3 (by rfl) ⟨1039151, by rfl⟩ : syracuseStep 5542141 = 2078303) B2078303
theorem B2396447 : Blo 1596997 2396447 := bstep (se 1 (by rfl) ⟨1797335, by rfl⟩ : syracuseStep 2396447 = 3594671) B3594671
theorem B2396471 : Blo 1596997 2396471 := bstep (se 1 (by rfl) ⟨1797353, by rfl⟩ : syracuseStep 2396471 = 3594707) B3594707
theorem B4043135 : Blo 1596997 4043135 := bstep (se 1 (by rfl) ⟨3032351, by rfl⟩ : syracuseStep 4043135 = 6064703) B6064703
theorem B2396543 : Blo 1596997 2396543 := bstep (se 1 (by rfl) ⟨1797407, by rfl⟩ : syracuseStep 2396543 = 3594815) B3594815
theorem B5394815 : Blo 1596997 5394815 := bstep (se 1 (by rfl) ⟨4046111, by rfl⟩ : syracuseStep 5394815 = 8092223) B8092223
theorem B4551079 : Blo 1596997 4551079 := bstep (se 1 (by rfl) ⟨3413309, by rfl⟩ : syracuseStep 4551079 = 6826619) B6826619
theorem B14569901 : Blo 1596997 14569901 := bstep (se 3 (by rfl) ⟨2731856, by rfl⟩ : syracuseStep 14569901 = 5463713) B5463713
theorem B2396615 : Blo 1596997 2396615 := bstep (se 1 (by rfl) ⟨1797461, by rfl⟩ : syracuseStep 2396615 = 3594923) B3594923
theorem B6066647 : Blo 1596997 6066647 := bstep (se 1 (by rfl) ⟨4549985, by rfl⟩ : syracuseStep 6066647 = 9099971) B9099971
theorem B4551329 : Blo 1596997 4551329 := bstep (se 2 (by rfl) ⟨1706748, by rfl⟩ : syracuseStep 4551329 = 3413497) B3413497
theorem B31552229 : Blo 1596997 31552229 := bstep (se 4 (by rfl) ⟨2958021, by rfl⟩ : syracuseStep 31552229 = 5916043) B5916043
theorem B2396969 : Blo 1596997 2396969 := bstep (se 2 (by rfl) ⟨898863, by rfl⟩ : syracuseStep 2396969 = 1797727) B1797727
theorem B2396975 : Blo 1596997 2396975 := bstep (se 1 (by rfl) ⟨1797731, by rfl⟩ : syracuseStep 2396975 = 3595463) B3595463
theorem B2397095 : Blo 1596997 2397095 := bstep (se 1 (by rfl) ⟨1797821, by rfl⟩ : syracuseStep 2397095 = 3595643) B3595643
theorem B2397179 : Blo 1596997 2397179 := bstep (se 1 (by rfl) ⟨1797884, by rfl⟩ : syracuseStep 2397179 = 3595769) B3595769
theorem B2397239 : Blo 1596997 2397239 := bstep (se 1 (by rfl) ⟨1797929, by rfl⟩ : syracuseStep 2397239 = 3595859) B3595859
theorem B7681139 : Blo 1596997 7681139 := bstep (se 1 (by rfl) ⟨5760854, by rfl⟩ : syracuseStep 7681139 = 11521709) B11521709
theorem B2397359 : Blo 1596997 2397359 := bstep (se 1 (by rfl) ⟨1798019, by rfl⟩ : syracuseStep 2397359 = 3596039) B3596039
theorem B4551967 : Blo 1596997 4551967 := bstep (se 1 (by rfl) ⟨3413975, by rfl⟩ : syracuseStep 4551967 = 6827951) B6827951
theorem B3593627 : Blo 1596997 3593627 := bstep (se 1 (by rfl) ⟨2695220, by rfl⟩ : syracuseStep 3593627 = 5390441) B5390441
theorem B7894529 : Blo 1596997 7894529 := bstep (se 2 (by rfl) ⟨2960448, by rfl⟩ : syracuseStep 7894529 = 5920897) B5920897
theorem B2397767 : Blo 1596997 2397767 := bstep (se 1 (by rfl) ⟨1798325, by rfl⟩ : syracuseStep 2397767 = 3596651) B3596651
theorem B2397863 : Blo 1596997 2397863 := bstep (se 1 (by rfl) ⟨1798397, by rfl⟩ : syracuseStep 2397863 = 3596795) B3596795
theorem B2275067 : Blo 1596997 2275067 := bstep (se 1 (by rfl) ⟨1706300, by rfl⟩ : syracuseStep 2275067 = 3412601) B3412601
theorem B2397947 : Blo 1596997 2397947 := bstep (se 1 (by rfl) ⟨1798460, by rfl⟩ : syracuseStep 2397947 = 3596921) B3596921
theorem B5396219 : Blo 1596997 5396219 := bstep (se 1 (by rfl) ⟨4047164, by rfl⟩ : syracuseStep 5396219 = 8094329) B8094329
theorem B2397983 : Blo 1596997 2397983 := bstep (se 1 (by rfl) ⟨1798487, by rfl⟩ : syracuseStep 2397983 = 3596975) B3596975
theorem B2398031 : Blo 1596997 2398031 := bstep (se 1 (by rfl) ⟨1798523, by rfl⟩ : syracuseStep 2398031 = 3597047) B3597047
theorem B5396381 : Blo 1596997 5396381 := bstep (se 3 (by rfl) ⟨1011821, by rfl⟩ : syracuseStep 5396381 = 2023643) B2023643
theorem B2398151 : Blo 1596997 2398151 := bstep (se 1 (by rfl) ⟨1798613, by rfl⟩ : syracuseStep 2398151 = 3597227) B3597227
theorem B3594203 : Blo 1596997 3594203 := bstep (se 1 (by rfl) ⟨2695652, by rfl⟩ : syracuseStep 3594203 = 5391305) B5391305
theorem B4044775 : Blo 1596997 4044775 := bstep (se 1 (by rfl) ⟨3033581, by rfl⟩ : syracuseStep 4044775 = 6067163) B6067163
theorem B4552787 : Blo 1596997 4552787 := bstep (se 1 (by rfl) ⟨3414590, by rfl⟩ : syracuseStep 4552787 = 6829181) B6829181
theorem B3643489 : Blo 1596997 3643489 := bstep (se 2 (by rfl) ⟨1366308, by rfl⟩ : syracuseStep 3643489 = 2732617) B2732617
theorem B3594383 : Blo 1596997 3594383 := bstep (se 1 (by rfl) ⟨2695787, by rfl⟩ : syracuseStep 3594383 = 5391575) B5391575
theorem B3594401 : Blo 1596997 3594401 := bstep (se 2 (by rfl) ⟨1347900, by rfl⟩ : syracuseStep 3594401 = 2695801) B2695801
theorem B9713849 : Blo 1596997 9713849 := bstep (se 2 (by rfl) ⟨3642693, by rfl⟩ : syracuseStep 9713849 = 7285387) B7285387
theorem B9222329 : Blo 1596997 9222329 := bstep (se 2 (by rfl) ⟨3458373, by rfl⟩ : syracuseStep 9222329 = 6916747) B6916747
theorem B18208961 : Blo 1596997 18208961 := bstep (se 2 (by rfl) ⟨6828360, by rfl⟩ : syracuseStep 18208961 = 13656721) B13656721
theorem B3594473 : Blo 1596997 3594473 := bstep (se 2 (by rfl) ⟨1347927, by rfl⟩ : syracuseStep 3594473 = 2695855) B2695855
theorem B47962397 : Blo 1596997 47962397 := bstep (se 3 (by rfl) ⟨8992949, by rfl⟩ : syracuseStep 47962397 = 17985899) B17985899
theorem B10934651 : Blo 1596997 10934651 := bstep (se 1 (by rfl) ⟨8200988, by rfl⟩ : syracuseStep 10934651 = 16401977) B16401977
theorem B2734697 : Blo 1596997 2734697 := bstep (se 2 (by rfl) ⟨1025511, by rfl⟩ : syracuseStep 2734697 = 2051023) B2051023
theorem B65592139 : Blo 1596997 65592139 := bstep (se 1 (by rfl) ⟨49194104, by rfl⟩ : syracuseStep 65592139 = 98388209) B98388209
theorem B4045727 : Blo 1596997 4045727 := bstep (se 1 (by rfl) ⟨3034295, by rfl⟩ : syracuseStep 4045727 = 6068591) B6068591
theorem B6822893 : Blo 1596997 6822893 := bstep (se 3 (by rfl) ⟨1279292, by rfl⟩ : syracuseStep 6822893 = 2558585) B2558585
theorem B18201671 : Blo 1596997 18201671 := bstep (se 1 (by rfl) ⟨13651253, by rfl⟩ : syracuseStep 18201671 = 27302507) B27302507
theorem B77708483 : Blo 1596997 77708483 := bstep (se 1 (by rfl) ⟨58281362, by rfl⟩ : syracuseStep 77708483 = 116562725) B116562725
theorem B9723095 : Blo 1596997 9723095 := bstep (se 1 (by rfl) ⟨7292321, by rfl⟩ : syracuseStep 9723095 = 14584643) B14584643
theorem B73776365 : Blo 1596997 73776365 := bstep (se 3 (by rfl) ⟨13833068, by rfl⟩ : syracuseStep 73776365 = 27666137) B27666137
theorem B5758303 : Blo 1596997 5758303 := bstep (se 1 (by rfl) ⟨4318727, by rfl⟩ : syracuseStep 5758303 = 8637455) B8637455
theorem B8093033 : Blo 1596997 8093033 := bstep (se 2 (by rfl) ⟨3034887, by rfl⟩ : syracuseStep 8093033 = 6069775) B6069775
theorem B10239443 : Blo 1596997 10239443 := bstep (se 1 (by rfl) ⟨7679582, by rfl⟩ : syracuseStep 10239443 = 15359165) B15359165
theorem B3595751 : Blo 1596997 3595751 := bstep (se 1 (by rfl) ⟨2696813, by rfl⟩ : syracuseStep 3595751 = 5393627) B5393627
theorem B3841511 : Blo 1596997 3841511 := bstep (se 1 (by rfl) ⟨2881133, by rfl⟩ : syracuseStep 3841511 = 5762267) B5762267
theorem B1597019 : Blo 1596997 1597019 := bstep (se 1 (by rfl) ⟨1197764, by rfl⟩ : syracuseStep 1597019 = 2395529) B2395529
theorem B9723635 : Blo 1596997 9723635 := bstep (se 1 (by rfl) ⟨7292726, by rfl⟩ : syracuseStep 9723635 = 14585453) B14585453
theorem B19431161 : Blo 1596997 19431161 := bstep (se 2 (by rfl) ⟨7286685, by rfl⟩ : syracuseStep 19431161 = 14573371) B14573371
theorem B12140279 : Blo 1596997 12140279 := bstep (se 1 (by rfl) ⟨9105209, by rfl⟩ : syracuseStep 12140279 = 18210419) B18210419
theorem B38887229 : Blo 1596997 38887229 := bstep (se 3 (by rfl) ⟨7291355, by rfl⟩ : syracuseStep 38887229 = 14582711) B14582711
theorem B1597255 : Blo 1596997 1597255 := bstep (se 1 (by rfl) ⟨1197941, by rfl⟩ : syracuseStep 1597255 = 2395883) B2395883
theorem B21880685 : Blo 1596997 21880685 := bstep (se 3 (by rfl) ⟨4102628, by rfl⟩ : syracuseStep 21880685 = 8205257) B8205257
theorem B1597407 : Blo 1596997 1597407 := bstep (se 1 (by rfl) ⟨1198055, by rfl⟩ : syracuseStep 1597407 = 2396111) B2396111
theorem B4857985 : Blo 1596997 4857985 := bstep (se 2 (by rfl) ⟨1821744, by rfl⟩ : syracuseStep 4857985 = 3643489) B3643489
theorem B1597631 : Blo 1596997 1597631 := bstep (se 1 (by rfl) ⟨1198223, by rfl⟩ : syracuseStep 1597631 = 2396447) B2396447
theorem B1597647 : Blo 1596997 1597647 := bstep (se 1 (by rfl) ⟨1198235, by rfl⟩ : syracuseStep 1597647 = 2396471) B2396471
theorem B12140765 : Blo 1596997 12140765 := bstep (se 3 (by rfl) ⟨2276393, by rfl⟩ : syracuseStep 12140765 = 4552787) B4552787
theorem B2695423 : Blo 1596997 2695423 := bstep (se 1 (by rfl) ⟨2021567, by rfl⟩ : syracuseStep 2695423 = 4043135) B4043135
theorem B1597695 : Blo 1596997 1597695 := bstep (se 1 (by rfl) ⟨1198271, by rfl⟩ : syracuseStep 1597695 = 2396543) B2396543
theorem B3596543 : Blo 1596997 3596543 := bstep (se 1 (by rfl) ⟨2697407, by rfl⟩ : syracuseStep 3596543 = 5394815) B5394815
theorem B1597743 : Blo 1596997 1597743 := bstep (se 1 (by rfl) ⟨1198307, by rfl⟩ : syracuseStep 1597743 = 2396615) B2396615
theorem B7389521 : Blo 1596997 7389521 := bstep (se 2 (by rfl) ⟨2771070, by rfl⟩ : syracuseStep 7389521 = 5542141) B5542141
theorem B3596705 : Blo 1596997 3596705 := bstep (se 2 (by rfl) ⟨1348764, by rfl⟩ : syracuseStep 3596705 = 2697529) B2697529
theorem B8094167 : Blo 1596997 8094167 := bstep (se 1 (by rfl) ⟨6070625, by rfl⟩ : syracuseStep 8094167 = 12141251) B12141251
theorem B4047367 : Blo 1596997 4047367 := bstep (se 1 (by rfl) ⟨3035525, by rfl⟩ : syracuseStep 4047367 = 6071051) B6071051
theorem B1597979 : Blo 1596997 1597979 := bstep (se 1 (by rfl) ⟨1198484, by rfl⟩ : syracuseStep 1597979 = 2396969) B2396969
theorem B1597983 : Blo 1596997 1597983 := bstep (se 1 (by rfl) ⟨1198487, by rfl⟩ : syracuseStep 1597983 = 2396975) B2396975
theorem B1598063 : Blo 1596997 1598063 := bstep (se 1 (by rfl) ⟨1198547, by rfl⟩ : syracuseStep 1598063 = 2397095) B2397095
theorem B1598119 : Blo 1596997 1598119 := bstep (se 1 (by rfl) ⟨1198589, by rfl⟩ : syracuseStep 1598119 = 2397179) B2397179
theorem B5391035 : Blo 1596997 5391035 := bstep (se 1 (by rfl) ⟨4043276, by rfl⟩ : syracuseStep 5391035 = 8086553) B8086553
theorem B1598159 : Blo 1596997 1598159 := bstep (se 1 (by rfl) ⟨1198619, by rfl⟩ : syracuseStep 1598159 = 2397239) B2397239
theorem B5120759 : Blo 1596997 5120759 := bstep (se 1 (by rfl) ⟨3840569, by rfl⟩ : syracuseStep 5120759 = 7681139) B7681139
theorem B1598239 : Blo 1596997 1598239 := bstep (se 1 (by rfl) ⟨1198679, by rfl⟩ : syracuseStep 1598239 = 2397359) B2397359
theorem B6914873 : Blo 1596997 6914873 := bstep (se 2 (by rfl) ⟨2593077, by rfl⟩ : syracuseStep 6914873 = 5186155) B5186155
theorem B10519577 : Blo 1596997 10519577 := bstep (se 2 (by rfl) ⟨3944841, by rfl⟩ : syracuseStep 10519577 = 7889683) B7889683
theorem B1598511 : Blo 1596997 1598511 := bstep (se 1 (by rfl) ⟨1198883, by rfl⟩ : syracuseStep 1598511 = 2397767) B2397767
theorem B4154441 : Blo 1596997 4154441 := bstep (se 2 (by rfl) ⟨1557915, by rfl⟩ : syracuseStep 4154441 = 3115831) B3115831
theorem B1598575 : Blo 1596997 1598575 := bstep (se 1 (by rfl) ⟨1198931, by rfl⟩ : syracuseStep 1598575 = 2397863) B2397863
theorem B1598631 : Blo 1596997 1598631 := bstep (se 1 (by rfl) ⟨1198973, by rfl⟩ : syracuseStep 1598631 = 2397947) B2397947
theorem B3597479 : Blo 1596997 3597479 := bstep (se 1 (by rfl) ⟨2698109, by rfl⟩ : syracuseStep 3597479 = 5396219) B5396219
theorem B1598655 : Blo 1596997 1598655 := bstep (se 1 (by rfl) ⟨1198991, by rfl⟩ : syracuseStep 1598655 = 2397983) B2397983
theorem B1598687 : Blo 1596997 1598687 := bstep (se 1 (by rfl) ⟨1199015, by rfl⟩ : syracuseStep 1598687 = 2398031) B2398031
theorem B3597587 : Blo 1596997 3597587 := bstep (se 1 (by rfl) ⟨2698190, by rfl⟩ : syracuseStep 3597587 = 5396381) B5396381
theorem B1598767 : Blo 1596997 1598767 := bstep (se 1 (by rfl) ⟨1199075, by rfl⟩ : syracuseStep 1598767 = 2398151) B2398151
theorem B31974931 : Blo 1596997 31974931 := bstep (se 1 (by rfl) ⟨23981198, by rfl⟩ : syracuseStep 31974931 = 47962397) B47962397
theorem B4548221 : Blo 1596997 4548221 := bstep (se 3 (by rfl) ⟨852791, by rfl⟩ : syracuseStep 4548221 = 1705583) B1705583
theorem B7677737 : Blo 1596997 7677737 := bstep (se 2 (by rfl) ⟨2879151, by rfl⟩ : syracuseStep 7677737 = 5758303) B5758303
theorem B6063929 : Blo 1596997 6063929 := bstep (se 2 (by rfl) ⟨2273973, by rfl⟩ : syracuseStep 6063929 = 4547947) B4547947
theorem B103614389 : Blo 1596997 103614389 := bstep (se 5 (by rfl) ⟨4856924, by rfl⟩ : syracuseStep 103614389 = 9713849) B9713849
theorem B2697151 : Blo 1596997 2697151 := bstep (se 1 (by rfl) ⟨2022863, by rfl⟩ : syracuseStep 2697151 = 4045727) B4045727
theorem B3033119 : Blo 1596997 3033119 := bstep (se 1 (by rfl) ⟨2274839, by rfl⟩ : syracuseStep 3033119 = 4549679) B4549679
theorem B12134447 : Blo 1596997 12134447 := bstep (se 1 (by rfl) ⟨9100835, by rfl⟩ : syracuseStep 12134447 = 18201671) B18201671
theorem B14583887 : Blo 1596997 14583887 := bstep (se 1 (by rfl) ⟨10937915, by rfl⟩ : syracuseStep 14583887 = 21875831) B21875831
theorem B6482063 : Blo 1596997 6482063 := bstep (se 1 (by rfl) ⟨4861547, by rfl⟩ : syracuseStep 6482063 = 9723095) B9723095
theorem B4098271 : Blo 1596997 4098271 := bstep (se 1 (by rfl) ⟨3073703, by rfl⟩ : syracuseStep 4098271 = 6147407) B6147407
theorem B7014683 : Blo 1596997 7014683 := bstep (se 1 (by rfl) ⟨5261012, by rfl⟩ : syracuseStep 7014683 = 10522025) B10522025
theorem B6826295 : Blo 1596997 6826295 := bstep (se 1 (by rfl) ⟨5119721, by rfl⟩ : syracuseStep 6826295 = 10239443) B10239443
theorem B5392763 : Blo 1596997 5392763 := bstep (se 1 (by rfl) ⟨4044572, by rfl⟩ : syracuseStep 5392763 = 8089145) B8089145
theorem B6482423 : Blo 1596997 6482423 := bstep (se 1 (by rfl) ⟨4861817, by rfl⟩ : syracuseStep 6482423 = 9723635) B9723635
theorem B12954107 : Blo 1596997 12954107 := bstep (se 1 (by rfl) ⟨9715580, by rfl⟩ : syracuseStep 12954107 = 19431161) B19431161
theorem B3033703 : Blo 1596997 3033703 := bstep (se 1 (by rfl) ⟨2275277, by rfl⟩ : syracuseStep 3033703 = 4550555) B4550555
theorem B5393033 : Blo 1596997 5393033 := bstep (se 2 (by rfl) ⟨2022387, by rfl⟩ : syracuseStep 5393033 = 4044775) B4044775
theorem B84208309 : Blo 1596997 84208309 := bstep (se 5 (by rfl) ⟨3947264, by rfl⟩ : syracuseStep 84208309 = 7894529) B7894529
theorem B8637131 : Blo 1596997 8637131 := bstep (se 1 (by rfl) ⟨6477848, by rfl⟩ : syracuseStep 8637131 = 12955697) B12955697
theorem B1797115 : Blo 1596997 1797115 := bstep (se 1 (by rfl) ⟨1347836, by rfl⟩ : syracuseStep 1797115 = 2695673) B2695673
theorem B1797295 : Blo 1596997 1797295 := bstep (se 1 (by rfl) ⟨1347971, by rfl⟩ : syracuseStep 1797295 = 2695943) B2695943
theorem B2395751 : Blo 1596997 2395751 := bstep (se 1 (by rfl) ⟨1796813, by rfl⟩ : syracuseStep 2395751 = 3593627) B3593627
theorem B4042487 : Blo 1596997 4042487 := bstep (se 1 (by rfl) ⟨3031865, by rfl⟩ : syracuseStep 4042487 = 6063731) B6063731
theorem B1798015 : Blo 1596997 1798015 := bstep (se 1 (by rfl) ⟨1348511, by rfl⟩ : syracuseStep 1798015 = 2697023) B2697023
theorem B12128129 : Blo 1596997 12128129 := bstep (se 2 (by rfl) ⟨4548048, by rfl⟩ : syracuseStep 12128129 = 9096097) B9096097
theorem B10244029 : Blo 1596997 10244029 := bstep (se 3 (by rfl) ⟨1920755, by rfl⟩ : syracuseStep 10244029 = 3841511) B3841511
theorem B2396135 : Blo 1596997 2396135 := bstep (se 1 (by rfl) ⟨1797101, by rfl⟩ : syracuseStep 2396135 = 3594203) B3594203
theorem B2396255 : Blo 1596997 2396255 := bstep (se 1 (by rfl) ⟨1797191, by rfl⟩ : syracuseStep 2396255 = 3594383) B3594383
theorem B2396267 : Blo 1596997 2396267 := bstep (se 1 (by rfl) ⟨1797200, by rfl⟩ : syracuseStep 2396267 = 3594401) B3594401
theorem B6148219 : Blo 1596997 6148219 := bstep (se 1 (by rfl) ⟨4611164, by rfl⟩ : syracuseStep 6148219 = 9222329) B9222329
theorem B2396315 : Blo 1596997 2396315 := bstep (se 1 (by rfl) ⟨1797236, by rfl⟩ : syracuseStep 2396315 = 3594473) B3594473
theorem B1798555 : Blo 1596997 1798555 := bstep (se 1 (by rfl) ⟨1348916, by rfl⟩ : syracuseStep 1798555 = 2697833) B2697833
theorem B1823131 : Blo 1596997 1823131 := bstep (se 1 (by rfl) ⟨1367348, by rfl⟩ : syracuseStep 1823131 = 2734697) B2734697
theorem B12136877 : Blo 1596997 12136877 := bstep (se 3 (by rfl) ⟨2275664, by rfl⟩ : syracuseStep 12136877 = 4551329) B4551329
theorem B6066845 : Blo 1596997 6066845 := bstep (se 3 (by rfl) ⟨1137533, by rfl⟩ : syracuseStep 6066845 = 2275067) B2275067
theorem B5395355 : Blo 1596997 5395355 := bstep (se 1 (by rfl) ⟨4046516, by rfl⟩ : syracuseStep 5395355 = 8093033) B8093033
theorem B11678671 : Blo 1596997 11678671 := bstep (se 1 (by rfl) ⟨8759003, by rfl⟩ : syracuseStep 11678671 = 17518007) B17518007
theorem B2397167 : Blo 1596997 2397167 := bstep (se 1 (by rfl) ⟨1797875, by rfl⟩ : syracuseStep 2397167 = 3595751) B3595751
theorem B25924819 : Blo 1596997 25924819 := bstep (se 1 (by rfl) ⟨19443614, by rfl⟩ : syracuseStep 25924819 = 38887229) B38887229
theorem B14587123 : Blo 1596997 14587123 := bstep (se 1 (by rfl) ⟨10940342, by rfl⟩ : syracuseStep 14587123 = 21880685) B21880685
theorem B3839339 : Blo 1596997 3839339 := bstep (se 1 (by rfl) ⟨2879504, by rfl⟩ : syracuseStep 3839339 = 5759009) B5759009
theorem B2397551 : Blo 1596997 2397551 := bstep (se 1 (by rfl) ⟨1798163, by rfl⟩ : syracuseStep 2397551 = 3596327) B3596327
theorem B2397671 : Blo 1596997 2397671 := bstep (se 1 (by rfl) ⟨1798253, by rfl⟩ : syracuseStep 2397671 = 3596507) B3596507
theorem B8639983 : Blo 1596997 8639983 := bstep (se 1 (by rfl) ⟨6479987, by rfl⟩ : syracuseStep 8639983 = 12959975) B12959975
theorem B3593807 : Blo 1596997 3593807 := bstep (se 1 (by rfl) ⟨2695355, by rfl⟩ : syracuseStep 3593807 = 5390711) B5390711
theorem B21861971 : Blo 1596997 21861971 := bstep (se 1 (by rfl) ⟨16396478, by rfl⟩ : syracuseStep 21861971 = 32792957) B32792957
theorem B9713267 : Blo 1596997 9713267 := bstep (se 1 (by rfl) ⟨7284950, by rfl⟩ : syracuseStep 9713267 = 14569901) B14569901
theorem B2397833 : Blo 1596997 2397833 := bstep (se 2 (by rfl) ⟨899187, by rfl⟩ : syracuseStep 2397833 = 1798375) B1798375
theorem B4044431 : Blo 1596997 4044431 := bstep (se 1 (by rfl) ⟨3033323, by rfl⟩ : syracuseStep 4044431 = 6066647) B6066647
theorem B2397851 : Blo 1596997 2397851 := bstep (se 1 (by rfl) ⟨1798388, by rfl⟩ : syracuseStep 2397851 = 3596777) B3596777
theorem B5117683 : Blo 1596997 5117683 := bstep (se 1 (by rfl) ⟨3838262, by rfl⟩ : syracuseStep 5117683 = 7676525) B7676525
theorem B6829865 : Blo 1596997 6829865 := bstep (se 2 (by rfl) ⟨2561199, by rfl⟩ : syracuseStep 6829865 = 5122399) B5122399
theorem B8197951 : Blo 1596997 8197951 := bstep (se 1 (by rfl) ⟨6148463, by rfl⟩ : syracuseStep 8197951 = 12296927) B12296927
theorem B21034819 : Blo 1596997 21034819 := bstep (se 1 (by rfl) ⟨15776114, by rfl⟩ : syracuseStep 21034819 = 31552229) B31552229
theorem B83015513 : Blo 1596997 83015513 := bstep (se 2 (by rfl) ⟨31130817, by rfl⟩ : syracuseStep 83015513 = 62261635) B62261635
theorem B2398043 : Blo 1596997 2398043 := bstep (se 1 (by rfl) ⟨1798532, by rfl⟩ : syracuseStep 2398043 = 3597065) B3597065
theorem B6068105 : Blo 1596997 6068105 := bstep (se 2 (by rfl) ⟨2275539, by rfl⟩ : syracuseStep 6068105 = 4551079) B4551079
theorem B2398427 : Blo 1596997 2398427 := bstep (se 1 (by rfl) ⟨1798820, by rfl⟩ : syracuseStep 2398427 = 3597641) B3597641
theorem B4045049 : Blo 1596997 4045049 := bstep (se 2 (by rfl) ⟨1516893, by rfl⟩ : syracuseStep 4045049 = 3033787) B3033787
theorem B3594527 : Blo 1596997 3594527 := bstep (se 1 (by rfl) ⟨2695895, by rfl⟩ : syracuseStep 3594527 = 5391791) B5391791
theorem B87456185 : Blo 1596997 87456185 := bstep (se 2 (by rfl) ⟨32796069, by rfl⟩ : syracuseStep 87456185 = 65592139) B65592139
theorem B3594779 : Blo 1596997 3594779 := bstep (se 1 (by rfl) ⟨2696084, by rfl⟩ : syracuseStep 3594779 = 5392169) B5392169
theorem B12139307 : Blo 1596997 12139307 := bstep (se 1 (by rfl) ⟨9104480, by rfl⟩ : syracuseStep 12139307 = 18208961) B18208961
theorem B7289767 : Blo 1596997 7289767 := bstep (se 1 (by rfl) ⟨5467325, by rfl⟩ : syracuseStep 7289767 = 10934651) B10934651
theorem B15358891 : Blo 1596997 15358891 := bstep (se 1 (by rfl) ⟨11519168, by rfl⟩ : syracuseStep 15358891 = 23038337) B23038337
theorem B6069289 : Blo 1596997 6069289 := bstep (se 2 (by rfl) ⟨2275983, by rfl⟩ : syracuseStep 6069289 = 4551967) B4551967
theorem B9100471 : Blo 1596997 9100471 := bstep (se 1 (by rfl) ⟨6825353, by rfl⟩ : syracuseStep 9100471 = 13650707) B13650707
theorem B2022727 : Blo 1596997 2022727 := bstep (se 1 (by rfl) ⟨1517045, by rfl⟩ : syracuseStep 2022727 = 3034091) B3034091
theorem B51805655 : Blo 1596997 51805655 := bstep (se 1 (by rfl) ⟨38854241, by rfl⟩ : syracuseStep 51805655 = 77708483) B77708483
theorem B49184243 : Blo 1596997 49184243 := bstep (se 1 (by rfl) ⟨36888182, by rfl⟩ : syracuseStep 49184243 = 73776365) B73776365
theorem B1597039 : Blo 1596997 1597039 := bstep (se 1 (by rfl) ⟨1197779, by rfl⟩ : syracuseStep 1597039 = 2395559) B2395559
theorem B1597095 : Blo 1596997 1597095 := bstep (se 1 (by rfl) ⟨1197821, by rfl⟩ : syracuseStep 1597095 = 2395643) B2395643
theorem B1597159 : Blo 1596997 1597159 := bstep (se 1 (by rfl) ⟨1197869, by rfl⟩ : syracuseStep 1597159 = 2395739) B2395739
theorem B1597215 : Blo 1596997 1597215 := bstep (se 1 (by rfl) ⟨1197911, by rfl⟩ : syracuseStep 1597215 = 2395823) B2395823
theorem B8093519 : Blo 1596997 8093519 := bstep (se 1 (by rfl) ⟨6070139, by rfl⟩ : syracuseStep 8093519 = 12140279) B12140279
theorem B3596129 : Blo 1596997 3596129 := bstep (se 2 (by rfl) ⟨1348548, by rfl⟩ : syracuseStep 3596129 = 2697097) B2697097
theorem B1597295 : Blo 1596997 1597295 := bstep (se 1 (by rfl) ⟨1197971, by rfl⟩ : syracuseStep 1597295 = 2395943) B2395943
theorem B1597351 : Blo 1596997 1597351 := bstep (se 1 (by rfl) ⟨1198013, by rfl⟩ : syracuseStep 1597351 = 2396027) B2396027
theorem B18194381 : Blo 1596997 18194381 := bstep (se 3 (by rfl) ⟨3411446, by rfl⟩ : syracuseStep 18194381 = 6822893) B6822893
theorem B3596255 : Blo 1596997 3596255 := bstep (se 1 (by rfl) ⟨2697191, by rfl⟩ : syracuseStep 3596255 = 5394383) B5394383
theorem B1597503 : Blo 1596997 1597503 := bstep (se 1 (by rfl) ⟨1198127, by rfl⟩ : syracuseStep 1597503 = 2396255) B2396255
theorem B1597511 : Blo 1596997 1597511 := bstep (se 1 (by rfl) ⟨1198133, by rfl⟩ : syracuseStep 1597511 = 2396267) B2396267
theorem B170532965 : Blo 1596997 170532965 := bstep (se 4 (by rfl) ⟨15987465, by rfl⟩ : syracuseStep 170532965 = 31974931) B31974931
theorem B1597543 : Blo 1596997 1597543 := bstep (se 1 (by rfl) ⟨1198157, by rfl⟩ : syracuseStep 1597543 = 2396315) B2396315
theorem B8093843 : Blo 1596997 8093843 := bstep (se 1 (by rfl) ⟨6070382, by rfl⟩ : syracuseStep 8093843 = 12140765) B12140765
theorem B5464361 : Blo 1596997 5464361 := bstep (se 2 (by rfl) ⟨2049135, by rfl⟩ : syracuseStep 5464361 = 4098271) B4098271
theorem B17285501 : Blo 1596997 17285501 := bstep (se 3 (by rfl) ⟨3241031, by rfl⟩ : syracuseStep 17285501 = 6482063) B6482063
theorem B3596903 : Blo 1596997 3596903 := bstep (se 1 (by rfl) ⟨2697677, by rfl⟩ : syracuseStep 3596903 = 5395355) B5395355
theorem B1598111 : Blo 1596997 1598111 := bstep (se 1 (by rfl) ⟨1198583, by rfl⟩ : syracuseStep 1598111 = 2397167) B2397167
theorem B7013051 : Blo 1596997 7013051 := bstep (se 1 (by rfl) ⟨5259788, by rfl⟩ : syracuseStep 7013051 = 10519577) B10519577
theorem B1598367 : Blo 1596997 1598367 := bstep (se 1 (by rfl) ⟨1198775, by rfl⟩ : syracuseStep 1598367 = 2397551) B2397551
theorem B449110981 : Blo 1596997 449110981 := bstep (se 4 (by rfl) ⟨42104154, by rfl⟩ : syracuseStep 449110981 = 84208309) B84208309
theorem B1598447 : Blo 1596997 1598447 := bstep (se 1 (by rfl) ⟨1198835, by rfl⟩ : syracuseStep 1598447 = 2397671) B2397671
theorem B14574647 : Blo 1596997 14574647 := bstep (se 1 (by rfl) ⟨10930985, by rfl⟩ : syracuseStep 14574647 = 21861971) B21861971
theorem B3032147 : Blo 1596997 3032147 := bstep (se 1 (by rfl) ⟨2274110, by rfl⟩ : syracuseStep 3032147 = 4548221) B4548221
theorem B1598555 : Blo 1596997 1598555 := bstep (se 1 (by rfl) ⟨1198916, by rfl⟩ : syracuseStep 1598555 = 2397833) B2397833
theorem B2696287 : Blo 1596997 2696287 := bstep (se 1 (by rfl) ⟨2022215, by rfl⟩ : syracuseStep 2696287 = 4044431) B4044431
theorem B1598567 : Blo 1596997 1598567 := bstep (se 1 (by rfl) ⟨1198925, by rfl⟩ : syracuseStep 1598567 = 2397851) B2397851
theorem B1598695 : Blo 1596997 1598695 := bstep (se 1 (by rfl) ⟨1199021, by rfl⟩ : syracuseStep 1598695 = 2398043) B2398043
theorem B69076259 : Blo 1596997 69076259 := bstep (se 1 (by rfl) ⟨51807194, by rfl⟩ : syracuseStep 69076259 = 103614389) B103614389
theorem B1598951 : Blo 1596997 1598951 := bstep (se 1 (by rfl) ⟨1199213, by rfl⟩ : syracuseStep 1598951 = 2398427) B2398427
theorem B2696699 : Blo 1596997 2696699 := bstep (se 1 (by rfl) ⟨2022524, by rfl⟩ : syracuseStep 2696699 = 4045049) B4045049
theorem B12133961 : Blo 1596997 12133961 := bstep (se 2 (by rfl) ⟨4550235, by rfl⟩ : syracuseStep 12133961 = 9100471) B9100471
theorem B58304123 : Blo 1596997 58304123 := bstep (se 1 (by rfl) ⟨43728092, by rfl⟩ : syracuseStep 58304123 = 87456185) B87456185
theorem B19449497 : Blo 1596997 19449497 := bstep (se 2 (by rfl) ⟨7293561, by rfl⟩ : syracuseStep 19449497 = 14587123) B14587123
theorem B8636071 : Blo 1596997 8636071 := bstep (se 1 (by rfl) ⟨6477053, by rfl⟩ : syracuseStep 8636071 = 12954107) B12954107
theorem B2696969 : Blo 1596997 2696969 := bstep (se 2 (by rfl) ⟨1011363, by rfl⟩ : syracuseStep 2696969 = 2022727) B2022727
theorem B11519977 : Blo 1596997 11519977 := bstep (se 2 (by rfl) ⟨4319991, by rfl⟩ : syracuseStep 11519977 = 8639983) B8639983
theorem B10930601 : Blo 1596997 10930601 := bstep (se 2 (by rfl) ⟨4098975, by rfl⟩ : syracuseStep 10930601 = 8197951) B8197951
theorem B13658705 : Blo 1596997 13658705 := bstep (se 2 (by rfl) ⟨5122014, by rfl⟩ : syracuseStep 13658705 = 10244029) B10244029
theorem B4926347 : Blo 1596997 4926347 := bstep (se 1 (by rfl) ⟨3694760, by rfl⟩ : syracuseStep 4926347 = 7389521) B7389521
theorem B44314037 : Blo 1596997 44314037 := bstep (se 5 (by rfl) ⟨2077220, by rfl⟩ : syracuseStep 44314037 = 4154441) B4154441
theorem B2395871 : Blo 1596997 2395871 := bstep (se 1 (by rfl) ⟨1796903, by rfl⟩ : syracuseStep 2395871 = 3593807) B3593807
theorem B6475511 : Blo 1596997 6475511 := bstep (se 1 (by rfl) ⟨4856633, by rfl⟩ : syracuseStep 6475511 = 9713267) B9713267
theorem B4042619 : Blo 1596997 4042619 := bstep (se 1 (by rfl) ⟨3031964, by rfl⟩ : syracuseStep 4042619 = 6063929) B6063929
theorem B9719689 : Blo 1596997 9719689 := bstep (se 2 (by rfl) ⟨3644883, by rfl⟩ : syracuseStep 9719689 = 7289767) B7289767
theorem B2396153 : Blo 1596997 2396153 := bstep (se 2 (by rfl) ⟨898557, by rfl⟩ : syracuseStep 2396153 = 1797115) B1797115
theorem B8089631 : Blo 1596997 8089631 := bstep (se 1 (by rfl) ⟨6067223, by rfl⟩ : syracuseStep 8089631 = 12134447) B12134447
theorem B2396351 : Blo 1596997 2396351 := bstep (se 1 (by rfl) ⟨1797263, by rfl⟩ : syracuseStep 2396351 = 3594527) B3594527
theorem B4550863 : Blo 1596997 4550863 := bstep (se 1 (by rfl) ⟨3413147, by rfl⟩ : syracuseStep 4550863 = 6826295) B6826295
theorem B2396393 : Blo 1596997 2396393 := bstep (se 2 (by rfl) ⟨898647, by rfl⟩ : syracuseStep 2396393 = 1797295) B1797295
theorem B34566425 : Blo 1596997 34566425 := bstep (se 2 (by rfl) ⟨12962409, by rfl⟩ : syracuseStep 34566425 = 25924819) B25924819
theorem B4321615 : Blo 1596997 4321615 := bstep (se 1 (by rfl) ⟨3241211, by rfl⟩ : syracuseStep 4321615 = 6482423) B6482423
theorem B2396519 : Blo 1596997 2396519 := bstep (se 1 (by rfl) ⟨1797389, by rfl⟩ : syracuseStep 2396519 = 3594779) B3594779
theorem B32789495 : Blo 1596997 32789495 := bstep (se 1 (by rfl) ⟨24592121, by rfl⟩ : syracuseStep 32789495 = 49184243) B49184243
theorem B28046425 : Blo 1596997 28046425 := bstep (se 2 (by rfl) ⟨10517409, by rfl⟩ : syracuseStep 28046425 = 21034819) B21034819
theorem B2397353 : Blo 1596997 2397353 := bstep (se 2 (by rfl) ⟨899007, by rfl⟩ : syracuseStep 2397353 = 1798015) B1798015
theorem B5395679 : Blo 1596997 5395679 := bstep (se 1 (by rfl) ⟨4046759, by rfl⟩ : syracuseStep 5395679 = 8093519) B8093519
theorem B2397419 : Blo 1596997 2397419 := bstep (se 1 (by rfl) ⟨1798064, by rfl⟩ : syracuseStep 2397419 = 3596129) B3596129
theorem B12129587 : Blo 1596997 12129587 := bstep (se 1 (by rfl) ⟨9097190, by rfl⟩ : syracuseStep 12129587 = 18194381) B18194381
theorem B2397503 : Blo 1596997 2397503 := bstep (se 1 (by rfl) ⟨1798127, by rfl⟩ : syracuseStep 2397503 = 3596255) B3596255
theorem B8197625 : Blo 1596997 8197625 := bstep (se 2 (by rfl) ⟨3074109, by rfl⟩ : syracuseStep 8197625 = 6148219) B6148219
theorem B2397695 : Blo 1596997 2397695 := bstep (se 1 (by rfl) ⟨1798271, by rfl⟩ : syracuseStep 2397695 = 3596543) B3596543
theorem B2397803 : Blo 1596997 2397803 := bstep (se 1 (by rfl) ⟨1798352, by rfl⟩ : syracuseStep 2397803 = 3596705) B3596705
theorem B8091251 : Blo 1596997 8091251 := bstep (se 1 (by rfl) ⟨6068438, by rfl⟩ : syracuseStep 8091251 = 12136877) B12136877
theorem B5396111 : Blo 1596997 5396111 := bstep (se 1 (by rfl) ⟨4047083, by rfl⟩ : syracuseStep 5396111 = 8094167) B8094167
theorem B3593897 : Blo 1596997 3593897 := bstep (se 2 (by rfl) ⟨1347711, by rfl⟩ : syracuseStep 3593897 = 2695423) B2695423
theorem B4044563 : Blo 1596997 4044563 := bstep (se 1 (by rfl) ⟨3033422, by rfl⟩ : syracuseStep 4044563 = 6066845) B6066845
theorem B3594023 : Blo 1596997 3594023 := bstep (se 1 (by rfl) ⟨2695517, by rfl⟩ : syracuseStep 3594023 = 5391035) B5391035
theorem B3413839 : Blo 1596997 3413839 := bstep (se 1 (by rfl) ⟨2560379, by rfl⟩ : syracuseStep 3413839 = 5120759) B5120759
theorem B2398073 : Blo 1596997 2398073 := bstep (se 2 (by rfl) ⟨899277, by rfl⟩ : syracuseStep 2398073 = 1798555) B1798555
theorem B4609915 : Blo 1596997 4609915 := bstep (se 1 (by rfl) ⟨3457436, by rfl⟩ : syracuseStep 4609915 = 6914873) B6914873
theorem B25909253 : Blo 1596997 25909253 := bstep (se 4 (by rfl) ⟨2428992, by rfl⟩ : syracuseStep 25909253 = 4857985) B4857985
theorem B5396489 : Blo 1596997 5396489 := bstep (se 2 (by rfl) ⟨2023683, by rfl⟩ : syracuseStep 5396489 = 4047367) B4047367
theorem B2398319 : Blo 1596997 2398319 := bstep (se 1 (by rfl) ⟨1798739, by rfl⟩ : syracuseStep 2398319 = 3597479) B3597479
theorem B4044937 : Blo 1596997 4044937 := bstep (se 2 (by rfl) ⟨1516851, by rfl⟩ : syracuseStep 4044937 = 3033703) B3033703
theorem B2398391 : Blo 1596997 2398391 := bstep (se 1 (by rfl) ⟨1798793, by rfl⟩ : syracuseStep 2398391 = 3597587) B3597587
theorem B10238237 : Blo 1596997 10238237 := bstep (se 3 (by rfl) ⟨1919669, by rfl⟩ : syracuseStep 10238237 = 3839339) B3839339
theorem B5118491 : Blo 1596997 5118491 := bstep (se 1 (by rfl) ⟨3838868, by rfl⟩ : syracuseStep 5118491 = 7677737) B7677737
theorem B4553243 : Blo 1596997 4553243 := bstep (se 1 (by rfl) ⟨3414932, by rfl⟩ : syracuseStep 4553243 = 6829865) B6829865
theorem B20478521 : Blo 1596997 20478521 := bstep (se 2 (by rfl) ⟨7679445, by rfl⟩ : syracuseStep 20478521 = 15358891) B15358891
theorem B55343675 : Blo 1596997 55343675 := bstep (se 1 (by rfl) ⟨41507756, by rfl⟩ : syracuseStep 55343675 = 83015513) B83015513
theorem B4045403 : Blo 1596997 4045403 := bstep (se 1 (by rfl) ⟨3034052, by rfl⟩ : syracuseStep 4045403 = 6068105) B6068105
theorem B15571561 : Blo 1596997 15571561 := bstep (se 2 (by rfl) ⟨5839335, by rfl⟩ : syracuseStep 15571561 = 11678671) B11678671
theorem B2022079 : Blo 1596997 2022079 := bstep (se 1 (by rfl) ⟨1516559, by rfl⟩ : syracuseStep 2022079 = 3033119) B3033119
theorem B9722591 : Blo 1596997 9722591 := bstep (se 1 (by rfl) ⟨7291943, by rfl⟩ : syracuseStep 9722591 = 14583887) B14583887
theorem B8092385 : Blo 1596997 8092385 := bstep (se 2 (by rfl) ⟨3034644, by rfl⟩ : syracuseStep 8092385 = 6069289) B6069289
theorem B4676455 : Blo 1596997 4676455 := bstep (se 1 (by rfl) ⟨3507341, by rfl⟩ : syracuseStep 4676455 = 7014683) B7014683
theorem B3595175 : Blo 1596997 3595175 := bstep (se 1 (by rfl) ⟨2696381, by rfl⟩ : syracuseStep 3595175 = 5392763) B5392763
theorem B3595355 : Blo 1596997 3595355 := bstep (se 1 (by rfl) ⟨2696516, by rfl⟩ : syracuseStep 3595355 = 5393033) B5393033
theorem B5758087 : Blo 1596997 5758087 := bstep (se 1 (by rfl) ⟨4318565, by rfl⟩ : syracuseStep 5758087 = 8637131) B8637131
theorem B8092871 : Blo 1596997 8092871 := bstep (se 1 (by rfl) ⟨6069653, by rfl⟩ : syracuseStep 8092871 = 12139307) B12139307
theorem B9723365 : Blo 1596997 9723365 := bstep (se 4 (by rfl) ⟨911565, by rfl⟩ : syracuseStep 9723365 = 1823131) B1823131
theorem B34537103 : Blo 1596997 34537103 := bstep (se 1 (by rfl) ⟨25902827, by rfl⟩ : syracuseStep 34537103 = 51805655) B51805655
theorem B6823577 : Blo 1596997 6823577 := bstep (se 2 (by rfl) ⟨2558841, by rfl⟩ : syracuseStep 6823577 = 5117683) B5117683
theorem B1597167 : Blo 1596997 1597167 := bstep (se 1 (by rfl) ⟨1197875, by rfl⟩ : syracuseStep 1597167 = 2395751) B2395751
theorem B2694991 : Blo 1596997 2694991 := bstep (se 1 (by rfl) ⟨2021243, by rfl⟩ : syracuseStep 2694991 = 4042487) B4042487
theorem B3596201 : Blo 1596997 3596201 := bstep (se 2 (by rfl) ⟨1348575, by rfl⟩ : syracuseStep 3596201 = 2697151) B2697151
theorem B8085419 : Blo 1596997 8085419 := bstep (se 1 (by rfl) ⟨6064064, by rfl⟩ : syracuseStep 8085419 = 12128129) B12128129
theorem B1597423 : Blo 1596997 1597423 := bstep (se 1 (by rfl) ⟨1198067, by rfl⟩ : syracuseStep 1597423 = 2396135) B2396135
theorem B113688643 : Blo 1596997 113688643 := bstep (se 1 (by rfl) ⟨85266482, by rfl⟩ : syracuseStep 113688643 = 170532965) B170532965
theorem B1597567 : Blo 1596997 1597567 := bstep (se 1 (by rfl) ⟨1198175, by rfl⟩ : syracuseStep 1597567 = 2396351) B2396351
theorem B1597595 : Blo 1596997 1597595 := bstep (se 1 (by rfl) ⟨1198196, by rfl⟩ : syracuseStep 1597595 = 2396393) B2396393
theorem B23044283 : Blo 1596997 23044283 := bstep (se 1 (by rfl) ⟨17283212, by rfl⟩ : syracuseStep 23044283 = 34566425) B34566425
theorem B1597679 : Blo 1596997 1597679 := bstep (se 1 (by rfl) ⟨1198259, by rfl⟩ : syracuseStep 1597679 = 2396519) B2396519
theorem B9716431 : Blo 1596997 9716431 := bstep (se 1 (by rfl) ⟨7287323, by rfl⟩ : syracuseStep 9716431 = 14574647) B14574647
theorem B1597435 : Blo 1596997 1597435 := bstep (se 1 (by rfl) ⟨1198076, by rfl⟩ : syracuseStep 1597435 = 2396153) B2396153
theorem B1598235 : Blo 1596997 1598235 := bstep (se 1 (by rfl) ⟨1198676, by rfl⟩ : syracuseStep 1598235 = 2397353) B2397353
theorem B3597119 : Blo 1596997 3597119 := bstep (se 1 (by rfl) ⟨2697839, by rfl⟩ : syracuseStep 3597119 = 5395679) B5395679
theorem B1598279 : Blo 1596997 1598279 := bstep (se 1 (by rfl) ⟨1198709, by rfl⟩ : syracuseStep 1598279 = 2397419) B2397419
theorem B8086391 : Blo 1596997 8086391 := bstep (se 1 (by rfl) ⟨6064793, by rfl⟩ : syracuseStep 8086391 = 12129587) B12129587
theorem B1598335 : Blo 1596997 1598335 := bstep (se 1 (by rfl) ⟨1198751, by rfl⟩ : syracuseStep 1598335 = 2397503) B2397503
theorem B2696105 : Blo 1596997 2696105 := bstep (se 2 (by rfl) ⟨1011039, by rfl⟩ : syracuseStep 2696105 = 2022079) B2022079
theorem B5465083 : Blo 1596997 5465083 := bstep (se 1 (by rfl) ⟨4098812, by rfl⟩ : syracuseStep 5465083 = 8197625) B8197625
theorem B1598463 : Blo 1596997 1598463 := bstep (se 1 (by rfl) ⟨1198847, by rfl⟩ : syracuseStep 1598463 = 2397695) B2397695
theorem B1598535 : Blo 1596997 1598535 := bstep (se 1 (by rfl) ⟨1198901, by rfl⟩ : syracuseStep 1598535 = 2397803) B2397803
theorem B3597407 : Blo 1596997 3597407 := bstep (se 1 (by rfl) ⟨2698055, by rfl⟩ : syracuseStep 3597407 = 5396111) B5396111
theorem B6235273 : Blo 1596997 6235273 := bstep (se 2 (by rfl) ⟨2338227, by rfl⟩ : syracuseStep 6235273 = 4676455) B4676455
theorem B2696375 : Blo 1596997 2696375 := bstep (se 1 (by rfl) ⟨2022281, by rfl⟩ : syracuseStep 2696375 = 4044563) B4044563
theorem B1598715 : Blo 1596997 1598715 := bstep (se 1 (by rfl) ⟨1199036, by rfl⟩ : syracuseStep 1598715 = 2398073) B2398073
theorem B3597659 : Blo 1596997 3597659 := bstep (se 1 (by rfl) ⟨2698244, by rfl⟩ : syracuseStep 3597659 = 5396489) B5396489
theorem B13649309 : Blo 1596997 13649309 := bstep (se 3 (by rfl) ⟨2559245, by rfl⟩ : syracuseStep 13649309 = 5118491) B5118491
theorem B1598879 : Blo 1596997 1598879 := bstep (se 1 (by rfl) ⟨1199159, by rfl⟩ : syracuseStep 1598879 = 2398319) B2398319
theorem B1598927 : Blo 1596997 1598927 := bstep (se 1 (by rfl) ⟨1199195, by rfl⟩ : syracuseStep 1598927 = 2398391) B2398391
theorem B7677449 : Blo 1596997 7677449 := bstep (se 2 (by rfl) ⟨2879043, by rfl⟩ : syracuseStep 7677449 = 5758087) B5758087
theorem B6825491 : Blo 1596997 6825491 := bstep (se 1 (by rfl) ⟨5119118, by rfl⟩ : syracuseStep 6825491 = 10238237) B10238237
theorem B2696935 : Blo 1596997 2696935 := bstep (se 1 (by rfl) ⟨2022701, by rfl⟩ : syracuseStep 2696935 = 4045403) B4045403
theorem B6481727 : Blo 1596997 6481727 := bstep (se 1 (by rfl) ⟨4861295, by rfl⟩ : syracuseStep 6481727 = 9722591) B9722591
theorem B24586213 : Blo 1596997 24586213 := bstep (se 4 (by rfl) ⟨2304957, by rfl⟩ : syracuseStep 24586213 = 4609915) B4609915
theorem B29542691 : Blo 1596997 29542691 := bstep (se 1 (by rfl) ⟨22157018, by rfl⟩ : syracuseStep 29542691 = 44314037) B44314037
theorem B6482243 : Blo 1596997 6482243 := bstep (se 1 (by rfl) ⟨4861682, by rfl⟩ : syracuseStep 6482243 = 9723365) B9723365
theorem B4549051 : Blo 1596997 4549051 := bstep (se 1 (by rfl) ⟨3411788, by rfl⟩ : syracuseStep 4549051 = 6823577) B6823577
theorem B5393087 : Blo 1596997 5393087 := bstep (se 1 (by rfl) ⟨4044815, by rfl⟩ : syracuseStep 5393087 = 8089631) B8089631
theorem B5393249 : Blo 1596997 5393249 := bstep (se 2 (by rfl) ⟨2022468, by rfl⟩ : syracuseStep 5393249 = 4044937) B4044937
theorem B5762153 : Blo 1596997 5762153 := bstep (se 2 (by rfl) ⟨2160807, by rfl⟩ : syracuseStep 5762153 = 4321615) B4321615
theorem B20762081 : Blo 1596997 20762081 := bstep (se 2 (by rfl) ⟨7785780, by rfl⟩ : syracuseStep 20762081 = 15571561) B15571561
theorem B46050839 : Blo 1596997 46050839 := bstep (se 1 (by rfl) ⟨34538129, by rfl⟩ : syracuseStep 46050839 = 69076259) B69076259
theorem B1797799 : Blo 1596997 1797799 := bstep (se 1 (by rfl) ⟨1348349, by rfl⟩ : syracuseStep 1797799 = 2696699) B2696699
theorem B8089307 : Blo 1596997 8089307 := bstep (se 1 (by rfl) ⟨6066980, by rfl⟩ : syracuseStep 8089307 = 12133961) B12133961
theorem B5394167 : Blo 1596997 5394167 := bstep (se 1 (by rfl) ⟨4045625, by rfl⟩ : syracuseStep 5394167 = 8091251) B8091251
theorem B2395931 : Blo 1596997 2395931 := bstep (se 1 (by rfl) ⟨1796948, by rfl⟩ : syracuseStep 2395931 = 3593897) B3593897
theorem B1797979 : Blo 1596997 1797979 := bstep (se 1 (by rfl) ⟨1348484, by rfl⟩ : syracuseStep 1797979 = 2696969) B2696969
theorem B2396015 : Blo 1596997 2396015 := bstep (se 1 (by rfl) ⟨1797011, by rfl⟩ : syracuseStep 2396015 = 3594023) B3594023
theorem B598814641 : Blo 1596997 598814641 := bstep (se 2 (by rfl) ⟨224555490, by rfl⟩ : syracuseStep 598814641 = 449110981) B449110981
theorem B17272835 : Blo 1596997 17272835 := bstep (se 1 (by rfl) ⟨12954626, by rfl⟩ : syracuseStep 17272835 = 25909253) B25909253
theorem B7287067 : Blo 1596997 7287067 := bstep (se 1 (by rfl) ⟨5465300, by rfl⟩ : syracuseStep 7287067 = 10930601) B10930601
theorem B3035495 : Blo 1596997 3035495 := bstep (se 1 (by rfl) ⟨2276621, by rfl⟩ : syracuseStep 3035495 = 4553243) B4553243
theorem B13652347 : Blo 1596997 13652347 := bstep (se 1 (by rfl) ⟨10239260, by rfl⟩ : syracuseStep 13652347 = 20478521) B20478521
theorem B9105803 : Blo 1596997 9105803 := bstep (se 1 (by rfl) ⟨6829352, by rfl⟩ : syracuseStep 9105803 = 13658705) B13658705
theorem B5394923 : Blo 1596997 5394923 := bstep (se 1 (by rfl) ⟨4046192, by rfl⟩ : syracuseStep 5394923 = 8092385) B8092385
theorem B2396783 : Blo 1596997 2396783 := bstep (se 1 (by rfl) ⟨1797587, by rfl⟩ : syracuseStep 2396783 = 3595175) B3595175
theorem B2396903 : Blo 1596997 2396903 := bstep (se 1 (by rfl) ⟨1797677, by rfl⟩ : syracuseStep 2396903 = 3595355) B3595355
theorem B5395247 : Blo 1596997 5395247 := bstep (se 1 (by rfl) ⟨4046435, by rfl⟩ : syracuseStep 5395247 = 8092871) B8092871
theorem B11514761 : Blo 1596997 11514761 := bstep (se 2 (by rfl) ⟨4318035, by rfl⟩ : syracuseStep 11514761 = 8636071) B8636071
theorem B23024735 : Blo 1596997 23024735 := bstep (se 1 (by rfl) ⟨17268551, by rfl⟩ : syracuseStep 23024735 = 34537103) B34537103
theorem B3593321 : Blo 1596997 3593321 := bstep (se 2 (by rfl) ⟨1347495, by rfl⟩ : syracuseStep 3593321 = 2694991) B2694991
theorem B4551785 : Blo 1596997 4551785 := bstep (se 2 (by rfl) ⟨1706919, by rfl⟩ : syracuseStep 4551785 = 3413839) B3413839
theorem B2397467 : Blo 1596997 2397467 := bstep (se 1 (by rfl) ⟨1798100, by rfl⟩ : syracuseStep 2397467 = 3596201) B3596201
theorem B87438653 : Blo 1596997 87438653 := bstep (se 3 (by rfl) ⟨16394747, by rfl⟩ : syracuseStep 87438653 = 32789495) B32789495
theorem B5395895 : Blo 1596997 5395895 := bstep (se 1 (by rfl) ⟨4046921, by rfl⟩ : syracuseStep 5395895 = 8093843) B8093843
theorem B3642907 : Blo 1596997 3642907 := bstep (se 1 (by rfl) ⟨2732180, by rfl⟩ : syracuseStep 3642907 = 5464361) B5464361
theorem B6067817 : Blo 1596997 6067817 := bstep (se 2 (by rfl) ⟨2275431, by rfl⟩ : syracuseStep 6067817 = 4550863) B4550863
theorem B2397935 : Blo 1596997 2397935 := bstep (se 1 (by rfl) ⟨1798451, by rfl⟩ : syracuseStep 2397935 = 3596903) B3596903
theorem B4675367 : Blo 1596997 4675367 := bstep (se 1 (by rfl) ⟨3506525, by rfl⟩ : syracuseStep 4675367 = 7013051) B7013051
theorem B2021431 : Blo 1596997 2021431 := bstep (se 1 (by rfl) ⟨1516073, by rfl⟩ : syracuseStep 2021431 = 3032147) B3032147
theorem B46094669 : Blo 1596997 46094669 := bstep (se 3 (by rfl) ⟨8642750, by rfl⟩ : syracuseStep 46094669 = 17285501) B17285501
theorem B38869415 : Blo 1596997 38869415 := bstep (se 1 (by rfl) ⟨29152061, by rfl⟩ : syracuseStep 38869415 = 58304123) B58304123
theorem B12966331 : Blo 1596997 12966331 := bstep (se 1 (by rfl) ⟨9724748, by rfl⟩ : syracuseStep 12966331 = 19449497) B19449497
theorem B37395233 : Blo 1596997 37395233 := bstep (se 2 (by rfl) ⟨14023212, by rfl⟩ : syracuseStep 37395233 = 28046425) B28046425
theorem B3595049 : Blo 1596997 3595049 := bstep (se 2 (by rfl) ⟨1348143, by rfl⟩ : syracuseStep 3595049 = 2696287) B2696287
theorem B36895783 : Blo 1596997 36895783 := bstep (se 1 (by rfl) ⟨27671837, by rfl⟩ : syracuseStep 36895783 = 55343675) B55343675
theorem B3284231 : Blo 1596997 3284231 := bstep (se 1 (by rfl) ⟨2463173, by rfl⟩ : syracuseStep 3284231 = 4926347) B4926347
theorem B17268029 : Blo 1596997 17268029 := bstep (se 3 (by rfl) ⟨3237755, by rfl⟩ : syracuseStep 17268029 = 6475511) B6475511
theorem B1597247 : Blo 1596997 1597247 := bstep (se 1 (by rfl) ⟨1197935, by rfl⟩ : syracuseStep 1597247 = 2395871) B2395871
theorem B12959585 : Blo 1596997 12959585 := bstep (se 2 (by rfl) ⟨4859844, by rfl⟩ : syracuseStep 12959585 = 9719689) B9719689
theorem B2695079 : Blo 1596997 2695079 := bstep (se 1 (by rfl) ⟨2021309, by rfl⟩ : syracuseStep 2695079 = 4042619) B4042619
theorem B5390279 : Blo 1596997 5390279 := bstep (se 1 (by rfl) ⟨4042709, by rfl⟩ : syracuseStep 5390279 = 8085419) B8085419
theorem B15359969 : Blo 1596997 15359969 := bstep (se 2 (by rfl) ⟨5759988, by rfl⟩ : syracuseStep 15359969 = 11519977) B11519977
theorem B2695241 : Blo 1596997 2695241 := bstep (se 2 (by rfl) ⟨1010715, by rfl⟩ : syracuseStep 2695241 = 2021431) B2021431
theorem B151584857 : Blo 1596997 151584857 := bstep (se 2 (by rfl) ⟨56844321, by rfl⟩ : syracuseStep 151584857 = 113688643) B113688643
theorem B6070535 : Blo 1596997 6070535 := bstep (se 1 (by rfl) ⟨4552901, by rfl⟩ : syracuseStep 6070535 = 9105803) B9105803
theorem B3596615 : Blo 1596997 3596615 := bstep (se 1 (by rfl) ⟨2697461, by rfl⟩ : syracuseStep 3596615 = 5394923) B5394923
theorem B1597855 : Blo 1596997 1597855 := bstep (se 1 (by rfl) ⟨1198391, by rfl⟩ : syracuseStep 1597855 = 2396783) B2396783
theorem B1597935 : Blo 1596997 1597935 := bstep (se 1 (by rfl) ⟨1198451, by rfl⟩ : syracuseStep 1597935 = 2396903) B2396903
theorem B18203129 : Blo 1596997 18203129 := bstep (se 2 (by rfl) ⟨6826173, by rfl⟩ : syracuseStep 18203129 = 13652347) B13652347
theorem B3596831 : Blo 1596997 3596831 := bstep (se 1 (by rfl) ⟨2697623, by rfl⟩ : syracuseStep 3596831 = 5395247) B5395247
theorem B5390927 : Blo 1596997 5390927 := bstep (se 1 (by rfl) ⟨4043195, by rfl⟩ : syracuseStep 5390927 = 8086391) B8086391
theorem B7676507 : Blo 1596997 7676507 := bstep (se 1 (by rfl) ⟨5757380, by rfl⟩ : syracuseStep 7676507 = 11514761) B11514761
theorem B8757949 : Blo 1596997 8757949 := bstep (se 3 (by rfl) ⟨1642115, by rfl⟩ : syracuseStep 8757949 = 3284231) B3284231
theorem B1598311 : Blo 1596997 1598311 := bstep (se 1 (by rfl) ⟨1198733, by rfl⟩ : syracuseStep 1598311 = 2397467) B2397467
theorem B8094653 : Blo 1596997 8094653 := bstep (se 3 (by rfl) ⟨1517747, by rfl⟩ : syracuseStep 8094653 = 3035495) B3035495
theorem B3597263 : Blo 1596997 3597263 := bstep (se 1 (by rfl) ⟨2697947, by rfl⟩ : syracuseStep 3597263 = 5395895) B5395895
theorem B1598623 : Blo 1596997 1598623 := bstep (se 1 (by rfl) ⟨1198967, by rfl⟩ : syracuseStep 1598623 = 2397935) B2397935
theorem B49194377 : Blo 1596997 49194377 := bstep (se 2 (by rfl) ⟨18447891, by rfl⟩ : syracuseStep 49194377 = 36895783) B36895783
theorem B38864357 : Blo 1596997 38864357 := bstep (se 4 (by rfl) ⟨3643533, by rfl⟩ : syracuseStep 38864357 = 7287067) B7287067
theorem B30729779 : Blo 1596997 30729779 := bstep (se 1 (by rfl) ⟨23047334, by rfl⟩ : syracuseStep 30729779 = 46094669) B46094669
theorem B25912943 : Blo 1596997 25912943 := bstep (se 1 (by rfl) ⟨19434707, by rfl⟩ : syracuseStep 25912943 = 38869415) B38869415
theorem B24930155 : Blo 1596997 24930155 := bstep (se 1 (by rfl) ⟨18697616, by rfl⟩ : syracuseStep 24930155 = 37395233) B37395233
theorem B11512019 : Blo 1596997 11512019 := bstep (se 1 (by rfl) ⟨8634014, by rfl⟩ : syracuseStep 11512019 = 17268029) B17268029
theorem B5392871 : Blo 1596997 5392871 := bstep (se 1 (by rfl) ⟨4044653, by rfl⟩ : syracuseStep 5392871 = 8089307) B8089307
theorem B798419521 : Blo 1596997 798419521 := bstep (se 2 (by rfl) ⟨299407320, by rfl⟩ : syracuseStep 798419521 = 598814641) B598814641
theorem B1796719 : Blo 1596997 1796719 := bstep (se 1 (by rfl) ⟨1347539, by rfl⟩ : syracuseStep 1796719 = 2695079) B2695079
theorem B15362855 : Blo 1596997 15362855 := bstep (se 1 (by rfl) ⟨11522141, by rfl⟩ : syracuseStep 15362855 = 23044283) B23044283
theorem B6065401 : Blo 1596997 6065401 := bstep (se 2 (by rfl) ⟨2274525, by rfl⟩ : syracuseStep 6065401 = 4549051) B4549051
theorem B17288441 : Blo 1596997 17288441 := bstep (se 2 (by rfl) ⟨6483165, by rfl⟩ : syracuseStep 17288441 = 12966331) B12966331
theorem B1797403 : Blo 1596997 1797403 := bstep (se 1 (by rfl) ⟨1348052, by rfl⟩ : syracuseStep 1797403 = 2696105) B2696105
theorem B2395547 : Blo 1596997 2395547 := bstep (se 1 (by rfl) ⟨1796660, by rfl⟩ : syracuseStep 2395547 = 3593321) B3593321
theorem B3034523 : Blo 1596997 3034523 := bstep (se 1 (by rfl) ⟨2275892, by rfl⟩ : syracuseStep 3034523 = 4551785) B4551785
theorem B1797583 : Blo 1596997 1797583 := bstep (se 1 (by rfl) ⟨1348187, by rfl⟩ : syracuseStep 1797583 = 2696375) B2696375
theorem B12955241 : Blo 1596997 12955241 := bstep (se 2 (by rfl) ⟨4858215, by rfl⟩ : syracuseStep 12955241 = 9716431) B9716431
theorem B4550327 : Blo 1596997 4550327 := bstep (se 1 (by rfl) ⟨3412745, by rfl⟩ : syracuseStep 4550327 = 6825491) B6825491
theorem B3116911 : Blo 1596997 3116911 := bstep (se 1 (by rfl) ⟨2337683, by rfl⟩ : syracuseStep 3116911 = 4675367) B4675367
theorem B4321151 : Blo 1596997 4321151 := bstep (se 1 (by rfl) ⟨3240863, by rfl⟩ : syracuseStep 4321151 = 6481727) B6481727
theorem B7286777 : Blo 1596997 7286777 := bstep (se 2 (by rfl) ⟨2732541, by rfl⟩ : syracuseStep 7286777 = 5465083) B5465083
theorem B4321495 : Blo 1596997 4321495 := bstep (se 1 (by rfl) ⟨3241121, by rfl⟩ : syracuseStep 4321495 = 6482243) B6482243
theorem B2396699 : Blo 1596997 2396699 := bstep (se 1 (by rfl) ⟨1797524, by rfl⟩ : syracuseStep 2396699 = 3595049) B3595049
theorem B2397065 : Blo 1596997 2397065 := bstep (se 2 (by rfl) ⟨898899, by rfl⟩ : syracuseStep 2397065 = 1797799) B1797799
theorem B13841387 : Blo 1596997 13841387 := bstep (se 1 (by rfl) ⟨10381040, by rfl⟩ : syracuseStep 13841387 = 20762081) B20762081
theorem B30700559 : Blo 1596997 30700559 := bstep (se 1 (by rfl) ⟨23025419, by rfl⟩ : syracuseStep 30700559 = 46050839) B46050839
theorem B2397305 : Blo 1596997 2397305 := bstep (se 2 (by rfl) ⟨898989, by rfl⟩ : syracuseStep 2397305 = 1797979) B1797979
theorem B8639723 : Blo 1596997 8639723 := bstep (se 1 (by rfl) ⟨6479792, by rfl⟩ : syracuseStep 8639723 = 12959585) B12959585
theorem B3593519 : Blo 1596997 3593519 := bstep (se 1 (by rfl) ⟨2695139, by rfl⟩ : syracuseStep 3593519 = 5390279) B5390279
theorem B32781617 : Blo 1596997 32781617 := bstep (se 2 (by rfl) ⟨12293106, by rfl⟩ : syracuseStep 32781617 = 24586213) B24586213
theorem B11515223 : Blo 1596997 11515223 := bstep (se 1 (by rfl) ⟨8636417, by rfl⟩ : syracuseStep 11515223 = 17272835) B17272835
theorem B2398079 : Blo 1596997 2398079 := bstep (se 1 (by rfl) ⟨1798559, by rfl⟩ : syracuseStep 2398079 = 3597119) B3597119
theorem B15349823 : Blo 1596997 15349823 := bstep (se 1 (by rfl) ⟨11512367, by rfl⟩ : syracuseStep 15349823 = 23024735) B23024735
theorem B2398271 : Blo 1596997 2398271 := bstep (se 1 (by rfl) ⟨1798703, by rfl⟩ : syracuseStep 2398271 = 3597407) B3597407
theorem B78780509 : Blo 1596997 78780509 := bstep (se 3 (by rfl) ⟨14771345, by rfl⟩ : syracuseStep 78780509 = 29542691) B29542691
theorem B58292435 : Blo 1596997 58292435 := bstep (se 1 (by rfl) ⟨43719326, by rfl⟩ : syracuseStep 58292435 = 87438653) B87438653
theorem B2398439 : Blo 1596997 2398439 := bstep (se 1 (by rfl) ⟨1798829, by rfl⟩ : syracuseStep 2398439 = 3597659) B3597659
theorem B9099539 : Blo 1596997 9099539 := bstep (se 1 (by rfl) ⟨6824654, by rfl⟩ : syracuseStep 9099539 = 13649309) B13649309
theorem B5118299 : Blo 1596997 5118299 := bstep (se 1 (by rfl) ⟨3838724, by rfl⟩ : syracuseStep 5118299 = 7677449) B7677449
theorem B4045211 : Blo 1596997 4045211 := bstep (se 1 (by rfl) ⟨3033908, by rfl⟩ : syracuseStep 4045211 = 6067817) B6067817
theorem B8313697 : Blo 1596997 8313697 := bstep (se 2 (by rfl) ⟨3117636, by rfl⟩ : syracuseStep 8313697 = 6235273) B6235273
theorem B3595391 : Blo 1596997 3595391 := bstep (se 1 (by rfl) ⟨2696543, by rfl⟩ : syracuseStep 3595391 = 5393087) B5393087
theorem B3595499 : Blo 1596997 3595499 := bstep (se 1 (by rfl) ⟨2696624, by rfl⟩ : syracuseStep 3595499 = 5393249) B5393249
theorem B4857209 : Blo 1596997 4857209 := bstep (se 2 (by rfl) ⟨1821453, by rfl⟩ : syracuseStep 4857209 = 3642907) B3642907
theorem B3841435 : Blo 1596997 3841435 := bstep (se 1 (by rfl) ⟨2881076, by rfl⟩ : syracuseStep 3841435 = 5762153) B5762153
theorem B3595913 : Blo 1596997 3595913 := bstep (se 2 (by rfl) ⟨1348467, by rfl⟩ : syracuseStep 3595913 = 2696935) B2696935
theorem B3596111 : Blo 1596997 3596111 := bstep (se 1 (by rfl) ⟨2697083, by rfl⟩ : syracuseStep 3596111 = 5394167) B5394167
theorem B1597287 : Blo 1596997 1597287 := bstep (se 1 (by rfl) ⟨1197965, by rfl⟩ : syracuseStep 1597287 = 2395931) B2395931
theorem B1597343 : Blo 1596997 1597343 := bstep (se 1 (by rfl) ⟨1198007, by rfl⟩ : syracuseStep 1597343 = 2396015) B2396015
theorem B10239979 : Blo 1596997 10239979 := bstep (se 1 (by rfl) ⟨7679984, by rfl⟩ : syracuseStep 10239979 = 15359969) B15359969
theorem B101056571 : Blo 1596997 101056571 := bstep (se 1 (by rfl) ⟨75792428, by rfl⟩ : syracuseStep 101056571 = 151584857) B151584857
theorem B4047023 : Blo 1596997 4047023 := bstep (se 1 (by rfl) ⟨3035267, by rfl⟩ : syracuseStep 4047023 = 6070535) B6070535
theorem B1597799 : Blo 1596997 1597799 := bstep (se 1 (by rfl) ⟨1198349, by rfl⟩ : syracuseStep 1597799 = 2396699) B2396699
theorem B1598043 : Blo 1596997 1598043 := bstep (se 1 (by rfl) ⟨1198532, by rfl⟩ : syracuseStep 1598043 = 2397065) B2397065
theorem B1598203 : Blo 1596997 1598203 := bstep (se 1 (by rfl) ⟨1198652, by rfl⟩ : syracuseStep 1598203 = 2397305) B2397305
theorem B1064559361 : Blo 1596997 1064559361 := bstep (se 2 (by rfl) ⟨399209760, by rfl⟩ : syracuseStep 1064559361 = 798419521) B798419521
theorem B7676815 : Blo 1596997 7676815 := bstep (se 1 (by rfl) ⟨5757611, by rfl⟩ : syracuseStep 7676815 = 11515223) B11515223
theorem B1598719 : Blo 1596997 1598719 := bstep (se 1 (by rfl) ⟨1199039, by rfl⟩ : syracuseStep 1598719 = 2398079) B2398079
theorem B10233215 : Blo 1596997 10233215 := bstep (se 1 (by rfl) ⟨7674911, by rfl⟩ : syracuseStep 10233215 = 15349823) B15349823
theorem B1598847 : Blo 1596997 1598847 := bstep (se 1 (by rfl) ⟨1199135, by rfl⟩ : syracuseStep 1598847 = 2398271) B2398271
theorem B52520339 : Blo 1596997 52520339 := bstep (se 1 (by rfl) ⟨39390254, by rfl⟩ : syracuseStep 52520339 = 78780509) B78780509
theorem B1598959 : Blo 1596997 1598959 := bstep (se 1 (by rfl) ⟨1199219, by rfl⟩ : syracuseStep 1598959 = 2398439) B2398439
theorem B2696807 : Blo 1596997 2696807 := bstep (se 1 (by rfl) ⟨2022605, by rfl⟩ : syracuseStep 2696807 = 4045211) B4045211
theorem B34547309 : Blo 1596997 34547309 := bstep (se 3 (by rfl) ⟨6477620, by rfl⟩ : syracuseStep 34547309 = 12955241) B12955241
theorem B8087201 : Blo 1596997 8087201 := bstep (se 2 (by rfl) ⟨3032700, by rfl⟩ : syracuseStep 8087201 = 6065401) B6065401
theorem B10241903 : Blo 1596997 10241903 := bstep (se 1 (by rfl) ⟨7681427, by rfl⟩ : syracuseStep 10241903 = 15362855) B15362855
theorem B5121913 : Blo 1596997 5121913 := bstep (se 2 (by rfl) ⟨1920717, by rfl⟩ : syracuseStep 5121913 = 3841435) B3841435
theorem B3238139 : Blo 1596997 3238139 := bstep (se 1 (by rfl) ⟨2428604, by rfl⟩ : syracuseStep 3238139 = 4857209) B4857209
theorem B3033551 : Blo 1596997 3033551 := bstep (se 1 (by rfl) ⟨2275163, by rfl⟩ : syracuseStep 3033551 = 4550327) B4550327
theorem B4155881 : Blo 1596997 4155881 := bstep (se 2 (by rfl) ⟨1558455, by rfl⟩ : syracuseStep 4155881 = 3116911) B3116911
theorem B1796827 : Blo 1596997 1796827 := bstep (se 1 (by rfl) ⟨1347620, by rfl⟩ : syracuseStep 1796827 = 2695241) B2695241
theorem B12135419 : Blo 1596997 12135419 := bstep (se 1 (by rfl) ⟨9101564, by rfl⟩ : syracuseStep 12135419 = 18203129) B18203129
theorem B23039261 : Blo 1596997 23039261 := bstep (se 3 (by rfl) ⟨4319861, by rfl⟩ : syracuseStep 23039261 = 8639723) B8639723
theorem B9227591 : Blo 1596997 9227591 := bstep (se 1 (by rfl) ⟨6920693, by rfl⟩ : syracuseStep 9227591 = 13841387) B13841387
theorem B20467039 : Blo 1596997 20467039 := bstep (se 1 (by rfl) ⟨15350279, by rfl⟩ : syracuseStep 20467039 = 30700559) B30700559
theorem B2395625 : Blo 1596997 2395625 := bstep (se 2 (by rfl) ⟨898359, by rfl⟩ : syracuseStep 2395625 = 1796719) B1796719
theorem B2395679 : Blo 1596997 2395679 := bstep (se 1 (by rfl) ⟨1796759, by rfl⟩ : syracuseStep 2395679 = 3593519) B3593519
theorem B11677265 : Blo 1596997 11677265 := bstep (se 2 (by rfl) ⟨4378974, by rfl⟩ : syracuseStep 11677265 = 8757949) B8757949
theorem B32796251 : Blo 1596997 32796251 := bstep (se 1 (by rfl) ⟨24597188, by rfl⟩ : syracuseStep 32796251 = 49194377) B49194377
theorem B23047973 : Blo 1596997 23047973 := bstep (se 4 (by rfl) ⟨2160747, by rfl⟩ : syracuseStep 23047973 = 4321495) B4321495
theorem B6066359 : Blo 1596997 6066359 := bstep (se 1 (by rfl) ⟨4549769, by rfl⟩ : syracuseStep 6066359 = 9099539) B9099539
theorem B3412199 : Blo 1596997 3412199 := bstep (se 1 (by rfl) ⟨2559149, by rfl⟩ : syracuseStep 3412199 = 5118299) B5118299
theorem B2396537 : Blo 1596997 2396537 := bstep (se 2 (by rfl) ⟨898701, by rfl⟩ : syracuseStep 2396537 = 1797403) B1797403
theorem B44339717 : Blo 1596997 44339717 := bstep (se 4 (by rfl) ⟨4156848, by rfl⟩ : syracuseStep 44339717 = 8313697) B8313697
theorem B2396777 : Blo 1596997 2396777 := bstep (se 2 (by rfl) ⟨898791, by rfl⟩ : syracuseStep 2396777 = 1797583) B1797583
theorem B2396927 : Blo 1596997 2396927 := bstep (se 1 (by rfl) ⟨1797695, by rfl⟩ : syracuseStep 2396927 = 3595391) B3595391
theorem B2396999 : Blo 1596997 2396999 := bstep (se 1 (by rfl) ⟨1797749, by rfl⟩ : syracuseStep 2396999 = 3595499) B3595499
theorem B2397275 : Blo 1596997 2397275 := bstep (se 1 (by rfl) ⟨1797956, by rfl⟩ : syracuseStep 2397275 = 3595913) B3595913
theorem B2397407 : Blo 1596997 2397407 := bstep (se 1 (by rfl) ⟨1798055, by rfl⟩ : syracuseStep 2397407 = 3596111) B3596111
theorem B2880767 : Blo 1596997 2880767 := bstep (se 1 (by rfl) ⟨2160575, by rfl⟩ : syracuseStep 2880767 = 4321151) B4321151
theorem B13653305 : Blo 1596997 13653305 := bstep (se 2 (by rfl) ⟨5119989, by rfl⟩ : syracuseStep 13653305 = 10239979) B10239979
theorem B2397743 : Blo 1596997 2397743 := bstep (se 1 (by rfl) ⟨1798307, by rfl⟩ : syracuseStep 2397743 = 3596615) B3596615
theorem B2397887 : Blo 1596997 2397887 := bstep (se 1 (by rfl) ⟨1798415, by rfl⟩ : syracuseStep 2397887 = 3596831) B3596831
theorem B3593951 : Blo 1596997 3593951 := bstep (se 1 (by rfl) ⟨2695463, by rfl⟩ : syracuseStep 3593951 = 5390927) B5390927
theorem B5117671 : Blo 1596997 5117671 := bstep (se 1 (by rfl) ⟨3838253, by rfl⟩ : syracuseStep 5117671 = 7676507) B7676507
theorem B5396435 : Blo 1596997 5396435 := bstep (se 1 (by rfl) ⟨4047326, by rfl⟩ : syracuseStep 5396435 = 8094653) B8094653
theorem B2398175 : Blo 1596997 2398175 := bstep (se 1 (by rfl) ⟨1798631, by rfl⟩ : syracuseStep 2398175 = 3597263) B3597263
theorem B21854411 : Blo 1596997 21854411 := bstep (se 1 (by rfl) ⟨16390808, by rfl⟩ : syracuseStep 21854411 = 32781617) B32781617
theorem B25909571 : Blo 1596997 25909571 := bstep (se 1 (by rfl) ⟨19432178, by rfl⟩ : syracuseStep 25909571 = 38864357) B38864357
theorem B20486519 : Blo 1596997 20486519 := bstep (se 1 (by rfl) ⟨15364889, by rfl⟩ : syracuseStep 20486519 = 30729779) B30729779
theorem B8092061 : Blo 1596997 8092061 := bstep (se 3 (by rfl) ⟨1517261, by rfl⟩ : syracuseStep 8092061 = 3034523) B3034523
theorem B17275295 : Blo 1596997 17275295 := bstep (se 1 (by rfl) ⟨12956471, by rfl⟩ : syracuseStep 17275295 = 25912943) B25912943
theorem B16620103 : Blo 1596997 16620103 := bstep (se 1 (by rfl) ⟨12465077, by rfl⟩ : syracuseStep 16620103 = 24930155) B24930155
theorem B7674679 : Blo 1596997 7674679 := bstep (se 1 (by rfl) ⟨5756009, by rfl⟩ : syracuseStep 7674679 = 11512019) B11512019
theorem B38861623 : Blo 1596997 38861623 := bstep (se 1 (by rfl) ⟨29146217, by rfl⟩ : syracuseStep 38861623 = 58292435) B58292435
theorem B3595247 : Blo 1596997 3595247 := bstep (se 1 (by rfl) ⟨2696435, by rfl⟩ : syracuseStep 3595247 = 5392871) B5392871
theorem B11525627 : Blo 1596997 11525627 := bstep (se 1 (by rfl) ⟨8644220, by rfl⟩ : syracuseStep 11525627 = 17288441) B17288441
theorem B1597031 : Blo 1596997 1597031 := bstep (se 1 (by rfl) ⟨1197773, by rfl⟩ : syracuseStep 1597031 = 2395547) B2395547
theorem B4857851 : Blo 1596997 4857851 := bstep (se 1 (by rfl) ⟨3643388, by rfl⟩ : syracuseStep 4857851 = 7286777) B7286777
theorem B67371047 : Blo 1596997 67371047 := bstep (se 1 (by rfl) ⟨50528285, by rfl⟩ : syracuseStep 67371047 = 101056571) B101056571
theorem B1597691 : Blo 1596997 1597691 := bstep (se 1 (by rfl) ⟨1198268, by rfl⟩ : syracuseStep 1597691 = 2396537) B2396537
theorem B1597851 : Blo 1596997 1597851 := bstep (se 1 (by rfl) ⟨1198388, by rfl⟩ : syracuseStep 1597851 = 2396777) B2396777
theorem B1597951 : Blo 1596997 1597951 := bstep (se 1 (by rfl) ⟨1198463, by rfl⟩ : syracuseStep 1597951 = 2396927) B2396927
theorem B1597999 : Blo 1596997 1597999 := bstep (se 1 (by rfl) ⟨1198499, by rfl⟩ : syracuseStep 1597999 = 2396999) B2396999
theorem B1598183 : Blo 1596997 1598183 := bstep (se 1 (by rfl) ⟨1198637, by rfl⟩ : syracuseStep 1598183 = 2397275) B2397275
theorem B22160137 : Blo 1596997 22160137 := bstep (se 2 (by rfl) ⟨8310051, by rfl⟩ : syracuseStep 22160137 = 16620103) B16620103
theorem B1598271 : Blo 1596997 1598271 := bstep (se 1 (by rfl) ⟨1198703, by rfl⟩ : syracuseStep 1598271 = 2397407) B2397407
theorem B9102203 : Blo 1596997 9102203 := bstep (se 1 (by rfl) ⟨6826652, by rfl⟩ : syracuseStep 9102203 = 13653305) B13653305
theorem B35013559 : Blo 1596997 35013559 := bstep (se 1 (by rfl) ⟨26260169, by rfl⟩ : syracuseStep 35013559 = 52520339) B52520339
theorem B1419412481 : Blo 1596997 1419412481 := bstep (se 2 (by rfl) ⟨532279680, by rfl⟩ : syracuseStep 1419412481 = 1064559361) B1064559361
theorem B1598495 : Blo 1596997 1598495 := bstep (se 1 (by rfl) ⟨1198871, by rfl⟩ : syracuseStep 1598495 = 2397743) B2397743
theorem B10232905 : Blo 1596997 10232905 := bstep (se 2 (by rfl) ⟨3837339, by rfl⟩ : syracuseStep 10232905 = 7674679) B7674679
theorem B5391467 : Blo 1596997 5391467 := bstep (se 1 (by rfl) ⟨4043600, by rfl⟩ : syracuseStep 5391467 = 8087201) B8087201
theorem B1598591 : Blo 1596997 1598591 := bstep (se 1 (by rfl) ⟨1198943, by rfl⟩ : syracuseStep 1598591 = 2397887) B2397887
theorem B3597623 : Blo 1596997 3597623 := bstep (se 1 (by rfl) ⟨2698217, by rfl⟩ : syracuseStep 3597623 = 5396435) B5396435
theorem B1598783 : Blo 1596997 1598783 := bstep (se 1 (by rfl) ⟨1199087, by rfl⟩ : syracuseStep 1598783 = 2398175) B2398175
theorem B13657679 : Blo 1596997 13657679 := bstep (se 1 (by rfl) ⟨10243259, by rfl⟩ : syracuseStep 13657679 = 20486519) B20486519
theorem B27289385 : Blo 1596997 27289385 := bstep (se 2 (by rfl) ⟨10233519, by rfl⟩ : syracuseStep 27289385 = 20467039) B20467039
theorem B7784843 : Blo 1596997 7784843 := bstep (se 1 (by rfl) ⟨5838632, by rfl⟩ : syracuseStep 7784843 = 11677265) B11677265
theorem B12954269 : Blo 1596997 12954269 := bstep (se 3 (by rfl) ⟨2428925, by rfl⟩ : syracuseStep 12954269 = 4857851) B4857851
theorem B2698015 : Blo 1596997 2698015 := bstep (se 1 (by rfl) ⟨2023511, by rfl⟩ : syracuseStep 2698015 = 4047023) B4047023
theorem B29559811 : Blo 1596997 29559811 := bstep (se 1 (by rfl) ⟨22169858, by rfl⟩ : syracuseStep 29559811 = 44339717) B44339717
theorem B1920511 : Blo 1596997 1920511 := bstep (se 1 (by rfl) ⟨1440383, by rfl⟩ : syracuseStep 1920511 = 2880767) B2880767
theorem B2395769 : Blo 1596997 2395769 := bstep (se 2 (by rfl) ⟨898413, by rfl⟩ : syracuseStep 2395769 = 1796827) B1796827
theorem B1797871 : Blo 1596997 1797871 := bstep (se 1 (by rfl) ⟨1348403, by rfl⟩ : syracuseStep 1797871 = 2696807) B2696807
theorem B23031539 : Blo 1596997 23031539 := bstep (se 1 (by rfl) ⟨17273654, by rfl⟩ : syracuseStep 23031539 = 34547309) B34547309
theorem B2395967 : Blo 1596997 2395967 := bstep (se 1 (by rfl) ⟨1796975, by rfl⟩ : syracuseStep 2395967 = 3593951) B3593951
theorem B10235753 : Blo 1596997 10235753 := bstep (se 2 (by rfl) ⟨3838407, by rfl⟩ : syracuseStep 10235753 = 7676815) B7676815
theorem B8089469 : Blo 1596997 8089469 := bstep (se 3 (by rfl) ⟨1516775, by rfl⟩ : syracuseStep 8089469 = 3033551) B3033551
theorem B6827935 : Blo 1596997 6827935 := bstep (se 1 (by rfl) ⟨5120951, by rfl⟩ : syracuseStep 6827935 = 10241903) B10241903
theorem B14569607 : Blo 1596997 14569607 := bstep (se 1 (by rfl) ⟨10927205, by rfl⟩ : syracuseStep 14569607 = 21854411) B21854411
theorem B2158759 : Blo 1596997 2158759 := bstep (se 1 (by rfl) ⟨1619069, by rfl⟩ : syracuseStep 2158759 = 3238139) B3238139
theorem B17273047 : Blo 1596997 17273047 := bstep (se 1 (by rfl) ⟨12954785, by rfl⟩ : syracuseStep 17273047 = 25909571) B25909571
theorem B5394707 : Blo 1596997 5394707 := bstep (se 1 (by rfl) ⟨4046030, by rfl⟩ : syracuseStep 5394707 = 8092061) B8092061
theorem B207261989 : Blo 1596997 207261989 := bstep (se 4 (by rfl) ⟨19430811, by rfl⟩ : syracuseStep 207261989 = 38861623) B38861623
theorem B2396831 : Blo 1596997 2396831 := bstep (se 1 (by rfl) ⟨1797623, by rfl⟩ : syracuseStep 2396831 = 3595247) B3595247
theorem B8090279 : Blo 1596997 8090279 := bstep (se 1 (by rfl) ⟨6067709, by rfl⟩ : syracuseStep 8090279 = 12135419) B12135419
theorem B6829217 : Blo 1596997 6829217 := bstep (se 2 (by rfl) ⟨2560956, by rfl⟩ : syracuseStep 6829217 = 5121913) B5121913
theorem B15365315 : Blo 1596997 15365315 := bstep (se 1 (by rfl) ⟨11523986, by rfl⟩ : syracuseStep 15365315 = 23047973) B23047973
theorem B4044239 : Blo 1596997 4044239 := bstep (se 1 (by rfl) ⟨3033179, by rfl⟩ : syracuseStep 4044239 = 6066359) B6066359
theorem B2274799 : Blo 1596997 2274799 := bstep (se 1 (by rfl) ⟨1706099, by rfl⟩ : syracuseStep 2274799 = 3412199) B3412199
theorem B6822143 : Blo 1596997 6822143 := bstep (se 1 (by rfl) ⟨5116607, by rfl⟩ : syracuseStep 6822143 = 10233215) B10233215
theorem B11082349 : Blo 1596997 11082349 := bstep (se 3 (by rfl) ⟨2077940, by rfl⟩ : syracuseStep 11082349 = 4155881) B4155881
theorem B11516863 : Blo 1596997 11516863 := bstep (se 1 (by rfl) ⟨8637647, by rfl⟩ : syracuseStep 11516863 = 17275295) B17275295
theorem B15359507 : Blo 1596997 15359507 := bstep (se 1 (by rfl) ⟨11519630, by rfl⟩ : syracuseStep 15359507 = 23039261) B23039261
theorem B6151727 : Blo 1596997 6151727 := bstep (se 1 (by rfl) ⟨4613795, by rfl⟩ : syracuseStep 6151727 = 9227591) B9227591
theorem B6823561 : Blo 1596997 6823561 := bstep (se 2 (by rfl) ⟨2558835, by rfl⟩ : syracuseStep 6823561 = 5117671) B5117671
theorem B1597083 : Blo 1596997 1597083 := bstep (se 1 (by rfl) ⟨1197812, by rfl⟩ : syracuseStep 1597083 = 2395625) B2395625
theorem B7683751 : Blo 1596997 7683751 := bstep (se 1 (by rfl) ⟨5762813, by rfl⟩ : syracuseStep 7683751 = 11525627) B11525627
theorem B1597119 : Blo 1596997 1597119 := bstep (se 1 (by rfl) ⟨1197839, by rfl⟩ : syracuseStep 1597119 = 2395679) B2395679
theorem B21864167 : Blo 1596997 21864167 := bstep (se 1 (by rfl) ⟨16398125, by rfl⟩ : syracuseStep 21864167 = 32796251) B32796251
theorem B3596471 : Blo 1596997 3596471 := bstep (se 1 (by rfl) ⟨2697353, by rfl⟩ : syracuseStep 3596471 = 5394707) B5394707
theorem B138174659 : Blo 1596997 138174659 := bstep (se 1 (by rfl) ⟨103630994, by rfl⟩ : syracuseStep 138174659 = 207261989) B207261989
theorem B1597887 : Blo 1596997 1597887 := bstep (se 1 (by rfl) ⟨1198415, by rfl⟩ : syracuseStep 1597887 = 2396831) B2396831
theorem B946274987 : Blo 1596997 946274987 := bstep (se 1 (by rfl) ⟨709706240, by rfl⟩ : syracuseStep 946274987 = 1419412481) B1419412481
theorem B2696159 : Blo 1596997 2696159 := bstep (se 1 (by rfl) ⟨2022119, by rfl⟩ : syracuseStep 2696159 = 4044239) B4044239
theorem B20759581 : Blo 1596997 20759581 := bstep (se 3 (by rfl) ⟨3892421, by rfl⟩ : syracuseStep 20759581 = 7784843) B7784843
theorem B3597353 : Blo 1596997 3597353 := bstep (se 2 (by rfl) ⟨1349007, by rfl⟩ : syracuseStep 3597353 = 2698015) B2698015
theorem B39413081 : Blo 1596997 39413081 := bstep (se 2 (by rfl) ⟨14779905, by rfl⟩ : syracuseStep 39413081 = 29559811) B29559811
theorem B4548095 : Blo 1596997 4548095 := bstep (se 1 (by rfl) ⟨3411071, by rfl⟩ : syracuseStep 4548095 = 6822143) B6822143
theorem B8636179 : Blo 1596997 8636179 := bstep (se 1 (by rfl) ⟨6477134, by rfl⟩ : syracuseStep 8636179 = 12954269) B12954269
theorem B3033065 : Blo 1596997 3033065 := bstep (se 2 (by rfl) ⟨1137399, by rfl⟩ : syracuseStep 3033065 = 2274799) B2274799
theorem B14576111 : Blo 1596997 14576111 := bstep (se 1 (by rfl) ⟨10932083, by rfl⟩ : syracuseStep 14576111 = 21864167) B21864167
theorem B15354359 : Blo 1596997 15354359 := bstep (se 1 (by rfl) ⟨11515769, by rfl⟩ : syracuseStep 15354359 = 23031539) B23031539
theorem B9103913 : Blo 1596997 9103913 := bstep (se 2 (by rfl) ⟨3413967, by rfl⟩ : syracuseStep 9103913 = 6827935) B6827935
theorem B5392979 : Blo 1596997 5392979 := bstep (se 1 (by rfl) ⟨4044734, by rfl⟩ : syracuseStep 5392979 = 8089469) B8089469
theorem B2878345 : Blo 1596997 2878345 := bstep (se 2 (by rfl) ⟨1079379, by rfl⟩ : syracuseStep 2878345 = 2158759) B2158759
theorem B23030729 : Blo 1596997 23030729 := bstep (se 2 (by rfl) ⟨8636523, by rfl⟩ : syracuseStep 23030729 = 17273047) B17273047
theorem B5393519 : Blo 1596997 5393519 := bstep (se 1 (by rfl) ⟨4045139, by rfl⟩ : syracuseStep 5393519 = 8090279) B8090279
theorem B10243543 : Blo 1596997 10243543 := bstep (se 1 (by rfl) ⟨7682657, by rfl⟩ : syracuseStep 10243543 = 15365315) B15365315
theorem B40980005 : Blo 1596997 40980005 := bstep (se 4 (by rfl) ⟨3841875, by rfl⟩ : syracuseStep 40980005 = 7683751) B7683751
theorem B9105119 : Blo 1596997 9105119 := bstep (se 1 (by rfl) ⟨6828839, by rfl⟩ : syracuseStep 9105119 = 13657679) B13657679
theorem B15355817 : Blo 1596997 15355817 := bstep (se 2 (by rfl) ⟨5758431, by rfl⟩ : syracuseStep 15355817 = 11516863) B11516863
theorem B13643873 : Blo 1596997 13643873 := bstep (se 2 (by rfl) ⟨5116452, by rfl⟩ : syracuseStep 13643873 = 10232905) B10232905
theorem B2560681 : Blo 1596997 2560681 := bstep (se 2 (by rfl) ⟨960255, by rfl⟩ : syracuseStep 2560681 = 1920511) B1920511
theorem B9098081 : Blo 1596997 9098081 := bstep (se 2 (by rfl) ⟨3411780, by rfl⟩ : syracuseStep 9098081 = 6823561) B6823561
theorem B2397161 : Blo 1596997 2397161 := bstep (se 2 (by rfl) ⟨898935, by rfl⟩ : syracuseStep 2397161 = 1797871) B1797871
theorem B4101151 : Blo 1596997 4101151 := bstep (se 1 (by rfl) ⟨3075863, by rfl⟩ : syracuseStep 4101151 = 6151727) B6151727
theorem B44914031 : Blo 1596997 44914031 := bstep (se 1 (by rfl) ⟨33685523, by rfl⟩ : syracuseStep 44914031 = 67371047) B67371047
theorem B9713071 : Blo 1596997 9713071 := bstep (se 1 (by rfl) ⟨7284803, by rfl⟩ : syracuseStep 9713071 = 14569607) B14569607
theorem B6068135 : Blo 1596997 6068135 := bstep (se 1 (by rfl) ⟨4551101, by rfl⟩ : syracuseStep 6068135 = 9102203) B9102203
theorem B3594311 : Blo 1596997 3594311 := bstep (se 1 (by rfl) ⟨2695733, by rfl⟩ : syracuseStep 3594311 = 5391467) B5391467
theorem B4552811 : Blo 1596997 4552811 := bstep (se 1 (by rfl) ⟨3414608, by rfl⟩ : syracuseStep 4552811 = 6829217) B6829217
theorem B14776465 : Blo 1596997 14776465 := bstep (se 2 (by rfl) ⟨5541174, by rfl⟩ : syracuseStep 14776465 = 11082349) B11082349
theorem B2398415 : Blo 1596997 2398415 := bstep (se 1 (by rfl) ⟨1798811, by rfl⟩ : syracuseStep 2398415 = 3597623) B3597623
theorem B29546849 : Blo 1596997 29546849 := bstep (se 2 (by rfl) ⟨11080068, by rfl⟩ : syracuseStep 29546849 = 22160137) B22160137
theorem B18192923 : Blo 1596997 18192923 := bstep (se 1 (by rfl) ⟨13644692, by rfl⟩ : syracuseStep 18192923 = 27289385) B27289385
theorem B46684745 : Blo 1596997 46684745 := bstep (se 2 (by rfl) ⟨17506779, by rfl⟩ : syracuseStep 46684745 = 35013559) B35013559
theorem B10239671 : Blo 1596997 10239671 := bstep (se 1 (by rfl) ⟨7679753, by rfl⟩ : syracuseStep 10239671 = 15359507) B15359507
theorem B1597179 : Blo 1596997 1597179 := bstep (se 1 (by rfl) ⟨1197884, by rfl⟩ : syracuseStep 1597179 = 2395769) B2395769
theorem B1597311 : Blo 1596997 1597311 := bstep (se 1 (by rfl) ⟨1197983, by rfl⟩ : syracuseStep 1597311 = 2395967) B2395967
theorem B6823835 : Blo 1596997 6823835 := bstep (se 1 (by rfl) ⟨5117876, by rfl⟩ : syracuseStep 6823835 = 10235753) B10235753
theorem B19701953 : Blo 1596997 19701953 := bstep (se 2 (by rfl) ⟨7388232, by rfl⟩ : syracuseStep 19701953 = 14776465) B14776465
theorem B1598107 : Blo 1596997 1598107 := bstep (se 1 (by rfl) ⟨1198580, by rfl⟩ : syracuseStep 1598107 = 2397161) B2397161
theorem B29942687 : Blo 1596997 29942687 := bstep (se 1 (by rfl) ⟨22457015, by rfl⟩ : syracuseStep 29942687 = 44914031) B44914031
theorem B3032063 : Blo 1596997 3032063 := bstep (se 1 (by rfl) ⟨2274047, by rfl⟩ : syracuseStep 3032063 = 4548095) B4548095
theorem B1598943 : Blo 1596997 1598943 := bstep (se 1 (by rfl) ⟨1199207, by rfl⟩ : syracuseStep 1598943 = 2398415) B2398415
theorem B9717407 : Blo 1596997 9717407 := bstep (se 1 (by rfl) ⟨7288055, by rfl⟩ : syracuseStep 9717407 = 14576111) B14576111
theorem B31123163 : Blo 1596997 31123163 := bstep (se 1 (by rfl) ⟨23342372, by rfl⟩ : syracuseStep 31123163 = 46684745) B46684745
theorem B2523399965 : Blo 1596997 2523399965 := bstep (se 3 (by rfl) ⟨473137493, by rfl⟩ : syracuseStep 2523399965 = 946274987) B946274987
theorem B13658057 : Blo 1596997 13658057 := bstep (se 2 (by rfl) ⟨5121771, by rfl⟩ : syracuseStep 13658057 = 10243543) B10243543
theorem B15353819 : Blo 1596997 15353819 := bstep (se 1 (by rfl) ⟨11515364, by rfl⟩ : syracuseStep 15353819 = 23030729) B23030729
theorem B6826447 : Blo 1596997 6826447 := bstep (se 1 (by rfl) ⟨5119835, by rfl⟩ : syracuseStep 6826447 = 10239671) B10239671
theorem B4549223 : Blo 1596997 4549223 := bstep (se 1 (by rfl) ⟨3411917, by rfl⟩ : syracuseStep 4549223 = 6823835) B6823835
theorem B8088173 : Blo 1596997 8088173 := bstep (se 3 (by rfl) ⟨1516532, by rfl⟩ : syracuseStep 8088173 = 3033065) B3033065
theorem B9095915 : Blo 1596997 9095915 := bstep (se 1 (by rfl) ⟨6821936, by rfl⟩ : syracuseStep 9095915 = 13643873) B13643873
theorem B110717765 : Blo 1596997 110717765 := bstep (se 4 (by rfl) ⟨10379790, by rfl⟩ : syracuseStep 110717765 = 20759581) B20759581
theorem B6065387 : Blo 1596997 6065387 := bstep (se 1 (by rfl) ⟨4549040, by rfl⟩ : syracuseStep 6065387 = 9098081) B9098081
theorem B1797439 : Blo 1596997 1797439 := bstep (se 1 (by rfl) ⟨1348079, by rfl⟩ : syracuseStep 1797439 = 2696159) B2696159
theorem B3837793 : Blo 1596997 3837793 := bstep (se 2 (by rfl) ⟨1439172, by rfl⟩ : syracuseStep 3837793 = 2878345) B2878345
theorem B5468201 : Blo 1596997 5468201 := bstep (se 2 (by rfl) ⟨2050575, by rfl⟩ : syracuseStep 5468201 = 4101151) B4101151
theorem B2396207 : Blo 1596997 2396207 := bstep (se 1 (by rfl) ⟨1797155, by rfl⟩ : syracuseStep 2396207 = 3594311) B3594311
theorem B3035207 : Blo 1596997 3035207 := bstep (se 1 (by rfl) ⟨2276405, by rfl⟩ : syracuseStep 3035207 = 4552811) B4552811
theorem B19697899 : Blo 1596997 19697899 := bstep (se 1 (by rfl) ⟨14773424, by rfl⟩ : syracuseStep 19697899 = 29546849) B29546849
theorem B10236239 : Blo 1596997 10236239 := bstep (se 1 (by rfl) ⟨7677179, by rfl⟩ : syracuseStep 10236239 = 15354359) B15354359
theorem B12128615 : Blo 1596997 12128615 := bstep (se 1 (by rfl) ⟨9096461, by rfl⟩ : syracuseStep 12128615 = 18192923) B18192923
theorem B11514905 : Blo 1596997 11514905 := bstep (se 2 (by rfl) ⟨4318089, by rfl⟩ : syracuseStep 11514905 = 8636179) B8636179
theorem B10237211 : Blo 1596997 10237211 := bstep (se 1 (by rfl) ⟨7677908, by rfl⟩ : syracuseStep 10237211 = 15355817) B15355817
theorem B2397647 : Blo 1596997 2397647 := bstep (se 1 (by rfl) ⟨1798235, by rfl⟩ : syracuseStep 2397647 = 3596471) B3596471
theorem B92116439 : Blo 1596997 92116439 := bstep (se 1 (by rfl) ⟨69087329, by rfl⟩ : syracuseStep 92116439 = 138174659) B138174659
theorem B2398235 : Blo 1596997 2398235 := bstep (se 1 (by rfl) ⟨1798676, by rfl⟩ : syracuseStep 2398235 = 3597353) B3597353
theorem B3414241 : Blo 1596997 3414241 := bstep (se 2 (by rfl) ⟨1280340, by rfl⟩ : syracuseStep 3414241 = 2560681) B2560681
theorem B105101549 : Blo 1596997 105101549 := bstep (se 3 (by rfl) ⟨19706540, by rfl⟩ : syracuseStep 105101549 = 39413081) B39413081
theorem B4045423 : Blo 1596997 4045423 := bstep (se 1 (by rfl) ⟨3034067, by rfl⟩ : syracuseStep 4045423 = 6068135) B6068135
theorem B6069275 : Blo 1596997 6069275 := bstep (se 1 (by rfl) ⟨4551956, by rfl⟩ : syracuseStep 6069275 = 9103913) B9103913
theorem B3595319 : Blo 1596997 3595319 := bstep (se 1 (by rfl) ⟨2696489, by rfl⟩ : syracuseStep 3595319 = 5392979) B5392979
theorem B12950761 : Blo 1596997 12950761 := bstep (se 2 (by rfl) ⟨4856535, by rfl⟩ : syracuseStep 12950761 = 9713071) B9713071
theorem B3595679 : Blo 1596997 3595679 := bstep (se 1 (by rfl) ⟨2696759, by rfl⟩ : syracuseStep 3595679 = 5393519) B5393519
theorem B27320003 : Blo 1596997 27320003 := bstep (se 1 (by rfl) ⟨20490002, by rfl⟩ : syracuseStep 27320003 = 40980005) B40980005
theorem B6070079 : Blo 1596997 6070079 := bstep (se 1 (by rfl) ⟨4552559, by rfl⟩ : syracuseStep 6070079 = 9105119) B9105119
theorem B3645467 : Blo 1596997 3645467 := bstep (se 1 (by rfl) ⟨2734100, by rfl⟩ : syracuseStep 3645467 = 5468201) B5468201
theorem B1597471 : Blo 1596997 1597471 := bstep (se 1 (by rfl) ⟨1198103, by rfl⟩ : syracuseStep 1597471 = 2396207) B2396207
theorem B2023471 : Blo 1596997 2023471 := bstep (se 1 (by rfl) ⟨1517603, by rfl⟩ : syracuseStep 2023471 = 3035207) B3035207
theorem B6824159 : Blo 1596997 6824159 := bstep (se 1 (by rfl) ⟨5118119, by rfl⟩ : syracuseStep 6824159 = 10236239) B10236239
theorem B8085743 : Blo 1596997 8085743 := bstep (se 1 (by rfl) ⟨6064307, by rfl⟩ : syracuseStep 8085743 = 12128615) B12128615
theorem B26263865 : Blo 1596997 26263865 := bstep (se 2 (by rfl) ⟨9848949, by rfl⟩ : syracuseStep 26263865 = 19697899) B19697899
theorem B9101929 : Blo 1596997 9101929 := bstep (se 2 (by rfl) ⟨3413223, by rfl⟩ : syracuseStep 9101929 = 6826447) B6826447
theorem B7676603 : Blo 1596997 7676603 := bstep (se 1 (by rfl) ⟨5757452, by rfl⟩ : syracuseStep 7676603 = 11514905) B11514905
theorem B6824807 : Blo 1596997 6824807 := bstep (se 1 (by rfl) ⟨5118605, by rfl⟩ : syracuseStep 6824807 = 10237211) B10237211
theorem B1598431 : Blo 1596997 1598431 := bstep (se 1 (by rfl) ⟨1198823, by rfl⟩ : syracuseStep 1598431 = 2397647) B2397647
theorem B1598823 : Blo 1596997 1598823 := bstep (se 1 (by rfl) ⟨1199117, by rfl⟩ : syracuseStep 1598823 = 2398235) B2398235
theorem B70067699 : Blo 1596997 70067699 := bstep (se 1 (by rfl) ⟨52550774, by rfl⟩ : syracuseStep 70067699 = 105101549) B105101549
theorem B3032815 : Blo 1596997 3032815 := bstep (se 1 (by rfl) ⟨2274611, by rfl⟩ : syracuseStep 3032815 = 4549223) B4549223
theorem B5392115 : Blo 1596997 5392115 := bstep (se 1 (by rfl) ⟨4044086, by rfl⟩ : syracuseStep 5392115 = 8088173) B8088173
theorem B6063943 : Blo 1596997 6063943 := bstep (se 1 (by rfl) ⟨4547957, by rfl⟩ : syracuseStep 6063943 = 9095915) B9095915
theorem B73811843 : Blo 1596997 73811843 := bstep (se 1 (by rfl) ⟨55358882, by rfl⟩ : syracuseStep 73811843 = 110717765) B110717765
theorem B82995101 : Blo 1596997 82995101 := bstep (se 3 (by rfl) ⟨15561581, by rfl⟩ : syracuseStep 82995101 = 31123163) B31123163
theorem B18213335 : Blo 1596997 18213335 := bstep (se 1 (by rfl) ⟨13660001, by rfl⟩ : syracuseStep 18213335 = 27320003) B27320003
theorem B13134635 : Blo 1596997 13134635 := bstep (se 1 (by rfl) ⟨9850976, by rfl⟩ : syracuseStep 13134635 = 19701953) B19701953
theorem B5393897 : Blo 1596997 5393897 := bstep (se 2 (by rfl) ⟨2022711, by rfl⟩ : syracuseStep 5393897 = 4045423) B4045423
theorem B61410959 : Blo 1596997 61410959 := bstep (se 1 (by rfl) ⟨46058219, by rfl⟩ : syracuseStep 61410959 = 92116439) B92116439
theorem B9105371 : Blo 1596997 9105371 := bstep (se 1 (by rfl) ⟨6829028, by rfl⟩ : syracuseStep 9105371 = 13658057) B13658057
theorem B10235879 : Blo 1596997 10235879 := bstep (se 1 (by rfl) ⟨7676909, by rfl⟩ : syracuseStep 10235879 = 15353819) B15353819
theorem B2396585 : Blo 1596997 2396585 := bstep (se 2 (by rfl) ⟨898719, by rfl⟩ : syracuseStep 2396585 = 1797439) B1797439
theorem B2396879 : Blo 1596997 2396879 := bstep (se 1 (by rfl) ⟨1797659, by rfl⟩ : syracuseStep 2396879 = 3595319) B3595319
theorem B4043591 : Blo 1596997 4043591 := bstep (se 1 (by rfl) ⟨3032693, by rfl⟩ : syracuseStep 4043591 = 6065387) B6065387
theorem B2397119 : Blo 1596997 2397119 := bstep (se 1 (by rfl) ⟨1797839, by rfl⟩ : syracuseStep 2397119 = 3595679) B3595679
theorem B5117057 : Blo 1596997 5117057 := bstep (se 2 (by rfl) ⟨1918896, by rfl⟩ : syracuseStep 5117057 = 3837793) B3837793
theorem B4552321 : Blo 1596997 4552321 := bstep (se 2 (by rfl) ⟨1707120, by rfl⟩ : syracuseStep 4552321 = 3414241) B3414241
theorem B2021375 : Blo 1596997 2021375 := bstep (se 1 (by rfl) ⟨1516031, by rfl⟩ : syracuseStep 2021375 = 3032063) B3032063
theorem B6478271 : Blo 1596997 6478271 := bstep (se 1 (by rfl) ⟨4858703, by rfl⟩ : syracuseStep 6478271 = 9717407) B9717407
theorem B1682266643 : Blo 1596997 1682266643 := bstep (se 1 (by rfl) ⟨1261699982, by rfl⟩ : syracuseStep 1682266643 = 2523399965) B2523399965
theorem B17267681 : Blo 1596997 17267681 := bstep (se 2 (by rfl) ⟨6475380, by rfl⟩ : syracuseStep 17267681 = 12950761) B12950761
theorem B4046183 : Blo 1596997 4046183 := bstep (se 1 (by rfl) ⟨3034637, by rfl⟩ : syracuseStep 4046183 = 6069275) B6069275
theorem B79847165 : Blo 1596997 79847165 := bstep (se 3 (by rfl) ⟨14971343, by rfl⟩ : syracuseStep 79847165 = 29942687) B29942687
theorem B4046719 : Blo 1596997 4046719 := bstep (se 1 (by rfl) ⟨3035039, by rfl⟩ : syracuseStep 4046719 = 6070079) B6070079
theorem B5390495 : Blo 1596997 5390495 := bstep (se 1 (by rfl) ⟨4042871, by rfl⟩ : syracuseStep 5390495 = 8085743) B8085743
theorem B1597723 : Blo 1596997 1597723 := bstep (se 1 (by rfl) ⟨1198292, by rfl⟩ : syracuseStep 1597723 = 2396585) B2396585
theorem B1597919 : Blo 1596997 1597919 := bstep (se 1 (by rfl) ⟨1198439, by rfl⟩ : syracuseStep 1597919 = 2396879) B2396879
theorem B2695727 : Blo 1596997 2695727 := bstep (se 1 (by rfl) ⟨2021795, by rfl⟩ : syracuseStep 2695727 = 4043591) B4043591
theorem B1598079 : Blo 1596997 1598079 := bstep (se 1 (by rfl) ⟨1198559, by rfl⟩ : syracuseStep 1598079 = 2397119) B2397119
theorem B46711799 : Blo 1596997 46711799 := bstep (se 1 (by rfl) ⟨35033849, by rfl⟩ : syracuseStep 46711799 = 70067699) B70067699
theorem B55330067 : Blo 1596997 55330067 := bstep (se 1 (by rfl) ⟨41497550, by rfl⟩ : syracuseStep 55330067 = 82995101) B82995101
theorem B4318847 : Blo 1596997 4318847 := bstep (se 1 (by rfl) ⟨3239135, by rfl⟩ : syracuseStep 4318847 = 6478271) B6478271
theorem B12142223 : Blo 1596997 12142223 := bstep (se 1 (by rfl) ⟨9106667, by rfl⟩ : syracuseStep 12142223 = 18213335) B18213335
theorem B1121511095 : Blo 1596997 1121511095 := bstep (se 1 (by rfl) ⟨841133321, by rfl⟩ : syracuseStep 1121511095 = 1682266643) B1682266643
theorem B2697455 : Blo 1596997 2697455 := bstep (se 1 (by rfl) ⟨2023091, by rfl⟩ : syracuseStep 2697455 = 4046183) B4046183
theorem B2697961 : Blo 1596997 2697961 := bstep (se 2 (by rfl) ⟨1011735, by rfl⟩ : syracuseStep 2697961 = 2023471) B2023471
theorem B4549439 : Blo 1596997 4549439 := bstep (se 1 (by rfl) ⟨3412079, by rfl⟩ : syracuseStep 4549439 = 6824159) B6824159
theorem B17509243 : Blo 1596997 17509243 := bstep (se 1 (by rfl) ⟨13131932, by rfl⟩ : syracuseStep 17509243 = 26263865) B26263865
theorem B4549871 : Blo 1596997 4549871 := bstep (se 1 (by rfl) ⟨3412403, by rfl⟩ : syracuseStep 4549871 = 6824807) B6824807
theorem B3411371 : Blo 1596997 3411371 := bstep (se 1 (by rfl) ⟨2558528, by rfl⟩ : syracuseStep 3411371 = 5117057) B5117057
theorem B12135905 : Blo 1596997 12135905 := bstep (se 2 (by rfl) ⟨4550964, by rfl⟩ : syracuseStep 12135905 = 9101929) B9101929
theorem B4043753 : Blo 1596997 4043753 := bstep (se 2 (by rfl) ⟨1516407, by rfl⟩ : syracuseStep 4043753 = 3032815) B3032815
theorem B40940639 : Blo 1596997 40940639 := bstep (se 1 (by rfl) ⟨30705479, by rfl⟩ : syracuseStep 40940639 = 61410959) B61410959
theorem B5395625 : Blo 1596997 5395625 := bstep (se 2 (by rfl) ⟨2023359, by rfl⟩ : syracuseStep 5395625 = 4046719) B4046719
theorem B38884981 : Blo 1596997 38884981 := bstep (se 5 (by rfl) ⟨1822733, by rfl⟩ : syracuseStep 38884981 = 3645467) B3645467
theorem B5117735 : Blo 1596997 5117735 := bstep (se 1 (by rfl) ⟨3838301, by rfl⟩ : syracuseStep 5117735 = 7676603) B7676603
theorem B3594743 : Blo 1596997 3594743 := bstep (se 1 (by rfl) ⟨2696057, by rfl⟩ : syracuseStep 3594743 = 5392115) B5392115
theorem B49207895 : Blo 1596997 49207895 := bstep (se 1 (by rfl) ⟨36905921, by rfl⟩ : syracuseStep 49207895 = 73811843) B73811843
theorem B8756423 : Blo 1596997 8756423 := bstep (se 1 (by rfl) ⟨6567317, by rfl⟩ : syracuseStep 8756423 = 13134635) B13134635
theorem B212925773 : Blo 1596997 212925773 := bstep (se 3 (by rfl) ⟨39923582, by rfl⟩ : syracuseStep 212925773 = 79847165) B79847165
theorem B6069761 : Blo 1596997 6069761 := bstep (se 2 (by rfl) ⟨2276160, by rfl⟩ : syracuseStep 6069761 = 4552321) B4552321
theorem B3595931 : Blo 1596997 3595931 := bstep (se 1 (by rfl) ⟨2696948, by rfl⟩ : syracuseStep 3595931 = 5393897) B5393897
theorem B8085257 : Blo 1596997 8085257 := bstep (se 2 (by rfl) ⟨3031971, by rfl⟩ : syracuseStep 8085257 = 6063943) B6063943
theorem B46047149 : Blo 1596997 46047149 := bstep (se 3 (by rfl) ⟨8633840, by rfl⟩ : syracuseStep 46047149 = 17267681) B17267681
theorem B6070247 : Blo 1596997 6070247 := bstep (se 1 (by rfl) ⟨4552685, by rfl⟩ : syracuseStep 6070247 = 9105371) B9105371
theorem B6823919 : Blo 1596997 6823919 := bstep (se 1 (by rfl) ⟨5117939, by rfl⟩ : syracuseStep 6823919 = 10235879) B10235879
theorem B5390333 : Blo 1596997 5390333 := bstep (se 3 (by rfl) ⟨1010687, by rfl⟩ : syracuseStep 5390333 = 2021375) B2021375
theorem B12132989 : Blo 1596997 12132989 := bstep (se 3 (by rfl) ⟨2274935, by rfl⟩ : syracuseStep 12132989 = 4549871) B4549871
theorem B2695835 : Blo 1596997 2695835 := bstep (se 1 (by rfl) ⟨2021876, by rfl⟩ : syracuseStep 2695835 = 4043753) B4043753
theorem B147546845 : Blo 1596997 147546845 := bstep (se 3 (by rfl) ⟨27665033, by rfl⟩ : syracuseStep 147546845 = 55330067) B55330067
theorem B3597083 : Blo 1596997 3597083 := bstep (se 1 (by rfl) ⟨2697812, by rfl⟩ : syracuseStep 3597083 = 5395625) B5395625
theorem B3597281 : Blo 1596997 3597281 := bstep (se 2 (by rfl) ⟨1348980, by rfl⟩ : syracuseStep 3597281 = 2697961) B2697961
theorem B8094815 : Blo 1596997 8094815 := bstep (se 1 (by rfl) ⟨6071111, by rfl⟩ : syracuseStep 8094815 = 12142223) B12142223
theorem B3032959 : Blo 1596997 3032959 := bstep (se 1 (by rfl) ⟨2274719, by rfl⟩ : syracuseStep 3032959 = 4549439) B4549439
theorem B30698099 : Blo 1596997 30698099 := bstep (se 1 (by rfl) ⟨23023574, by rfl⟩ : syracuseStep 30698099 = 46047149) B46047149
theorem B4549279 : Blo 1596997 4549279 := bstep (se 1 (by rfl) ⟨3411959, by rfl⟩ : syracuseStep 4549279 = 6823919) B6823919
theorem B1797151 : Blo 1596997 1797151 := bstep (se 1 (by rfl) ⟨1347863, by rfl⟩ : syracuseStep 1797151 = 2695727) B2695727
theorem B31141199 : Blo 1596997 31141199 := bstep (se 1 (by rfl) ⟨23355899, by rfl⟩ : syracuseStep 31141199 = 46711799) B46711799
theorem B2879231 : Blo 1596997 2879231 := bstep (se 1 (by rfl) ⟨2159423, by rfl⟩ : syracuseStep 2879231 = 4318847) B4318847
theorem B3411823 : Blo 1596997 3411823 := bstep (se 1 (by rfl) ⟨2558867, by rfl⟩ : syracuseStep 3411823 = 5117735) B5117735
theorem B1798303 : Blo 1596997 1798303 := bstep (se 1 (by rfl) ⟨1348727, by rfl⟩ : syracuseStep 1798303 = 2697455) B2697455
theorem B2396495 : Blo 1596997 2396495 := bstep (se 1 (by rfl) ⟨1797371, by rfl⟩ : syracuseStep 2396495 = 3594743) B3594743
theorem B32805263 : Blo 1596997 32805263 := bstep (se 1 (by rfl) ⟨24603947, by rfl⟩ : syracuseStep 32805263 = 49207895) B49207895
theorem B5837615 : Blo 1596997 5837615 := bstep (se 1 (by rfl) ⟨4378211, by rfl⟩ : syracuseStep 5837615 = 8756423) B8756423
theorem B2274247 : Blo 1596997 2274247 := bstep (se 1 (by rfl) ⟨1705685, by rfl⟩ : syracuseStep 2274247 = 3411371) B3411371
theorem B8090603 : Blo 1596997 8090603 := bstep (se 1 (by rfl) ⟨6067952, by rfl⟩ : syracuseStep 8090603 = 12135905) B12135905
theorem B2397287 : Blo 1596997 2397287 := bstep (se 1 (by rfl) ⟨1797965, by rfl⟩ : syracuseStep 2397287 = 3595931) B3595931
theorem B3593555 : Blo 1596997 3593555 := bstep (se 1 (by rfl) ⟨2695166, by rfl⟩ : syracuseStep 3593555 = 5390333) B5390333
theorem B3593663 : Blo 1596997 3593663 := bstep (se 1 (by rfl) ⟨2695247, by rfl⟩ : syracuseStep 3593663 = 5390495) B5390495
theorem B27293759 : Blo 1596997 27293759 := bstep (se 1 (by rfl) ⟨20470319, by rfl⟩ : syracuseStep 27293759 = 40940639) B40940639
theorem B747674063 : Blo 1596997 747674063 := bstep (se 1 (by rfl) ⟨560755547, by rfl⟩ : syracuseStep 747674063 = 1121511095) B1121511095
theorem B23345657 : Blo 1596997 23345657 := bstep (se 2 (by rfl) ⟨8754621, by rfl⟩ : syracuseStep 23345657 = 17509243) B17509243
theorem B51846641 : Blo 1596997 51846641 := bstep (se 2 (by rfl) ⟨19442490, by rfl⟩ : syracuseStep 51846641 = 38884981) B38884981
theorem B141950515 : Blo 1596997 141950515 := bstep (se 1 (by rfl) ⟨106462886, by rfl⟩ : syracuseStep 141950515 = 212925773) B212925773
theorem B4046507 : Blo 1596997 4046507 := bstep (se 1 (by rfl) ⟨3034880, by rfl⟩ : syracuseStep 4046507 = 6069761) B6069761
theorem B5390171 : Blo 1596997 5390171 := bstep (se 1 (by rfl) ⟨4042628, by rfl⟩ : syracuseStep 5390171 = 8085257) B8085257
theorem B4046831 : Blo 1596997 4046831 := bstep (se 1 (by rfl) ⟨3035123, by rfl⟩ : syracuseStep 4046831 = 6070247) B6070247
theorem B1597663 : Blo 1596997 1597663 := bstep (se 1 (by rfl) ⟨1198247, by rfl⟩ : syracuseStep 1597663 = 2396495) B2396495
theorem B3891743 : Blo 1596997 3891743 := bstep (se 1 (by rfl) ⟨2918807, by rfl⟩ : syracuseStep 3891743 = 5837615) B5837615
theorem B1598191 : Blo 1596997 1598191 := bstep (se 1 (by rfl) ⟨1198643, by rfl⟩ : syracuseStep 1598191 = 2397287) B2397287
theorem B3032329 : Blo 1596997 3032329 := bstep (se 2 (by rfl) ⟨1137123, by rfl⟩ : syracuseStep 3032329 = 2274247) B2274247
theorem B18195839 : Blo 1596997 18195839 := bstep (se 1 (by rfl) ⟨13646879, by rfl⟩ : syracuseStep 18195839 = 27293759) B27293759
theorem B20465399 : Blo 1596997 20465399 := bstep (se 1 (by rfl) ⟨15349049, by rfl⟩ : syracuseStep 20465399 = 30698099) B30698099
theorem B7677949 : Blo 1596997 7677949 := bstep (se 3 (by rfl) ⟨1439615, by rfl⟩ : syracuseStep 7677949 = 2879231) B2879231
theorem B20760799 : Blo 1596997 20760799 := bstep (se 1 (by rfl) ⟨15570599, by rfl⟩ : syracuseStep 20760799 = 31141199) B31141199
theorem B34564427 : Blo 1596997 34564427 := bstep (se 1 (by rfl) ⟨25923320, by rfl⟩ : syracuseStep 34564427 = 51846641) B51846641
theorem B2697671 : Blo 1596997 2697671 := bstep (se 1 (by rfl) ⟨2023253, by rfl⟩ : syracuseStep 2697671 = 4046507) B4046507
theorem B4549097 : Blo 1596997 4549097 := bstep (se 2 (by rfl) ⟨1705911, by rfl⟩ : syracuseStep 4549097 = 3411823) B3411823
theorem B2697887 : Blo 1596997 2697887 := bstep (se 1 (by rfl) ⟨2023415, by rfl⟩ : syracuseStep 2697887 = 4046831) B4046831
theorem B8088659 : Blo 1596997 8088659 := bstep (se 1 (by rfl) ⟨6066494, by rfl⟩ : syracuseStep 8088659 = 12132989) B12132989
theorem B1797223 : Blo 1596997 1797223 := bstep (se 1 (by rfl) ⟨1347917, by rfl⟩ : syracuseStep 1797223 = 2695835) B2695835
theorem B98364563 : Blo 1596997 98364563 := bstep (se 1 (by rfl) ⟨73773422, by rfl⟩ : syracuseStep 98364563 = 147546845) B147546845
theorem B5393735 : Blo 1596997 5393735 := bstep (se 1 (by rfl) ⟨4045301, by rfl⟩ : syracuseStep 5393735 = 8090603) B8090603
theorem B6065705 : Blo 1596997 6065705 := bstep (se 2 (by rfl) ⟨2274639, by rfl⟩ : syracuseStep 6065705 = 4549279) B4549279
theorem B2395703 : Blo 1596997 2395703 := bstep (se 1 (by rfl) ⟨1796777, by rfl⟩ : syracuseStep 2395703 = 3593555) B3593555
theorem B2395775 : Blo 1596997 2395775 := bstep (se 1 (by rfl) ⟨1796831, by rfl⟩ : syracuseStep 2395775 = 3593663) B3593663
theorem B2396201 : Blo 1596997 2396201 := bstep (se 2 (by rfl) ⟨898575, by rfl⟩ : syracuseStep 2396201 = 1797151) B1797151
theorem B4043945 : Blo 1596997 4043945 := bstep (se 2 (by rfl) ⟨1516479, by rfl⟩ : syracuseStep 4043945 = 3032959) B3032959
theorem B3593447 : Blo 1596997 3593447 := bstep (se 1 (by rfl) ⟨2695085, by rfl⟩ : syracuseStep 3593447 = 5390171) B5390171
theorem B2397737 : Blo 1596997 2397737 := bstep (se 2 (by rfl) ⟨899151, by rfl⟩ : syracuseStep 2397737 = 1798303) B1798303
theorem B21870175 : Blo 1596997 21870175 := bstep (se 1 (by rfl) ⟨16402631, by rfl⟩ : syracuseStep 21870175 = 32805263) B32805263
theorem B2398055 : Blo 1596997 2398055 := bstep (se 1 (by rfl) ⟨1798541, by rfl⟩ : syracuseStep 2398055 = 3597083) B3597083
theorem B2398187 : Blo 1596997 2398187 := bstep (se 1 (by rfl) ⟨1798640, by rfl⟩ : syracuseStep 2398187 = 3597281) B3597281
theorem B5396543 : Blo 1596997 5396543 := bstep (se 1 (by rfl) ⟨4047407, by rfl⟩ : syracuseStep 5396543 = 8094815) B8094815
theorem B498449375 : Blo 1596997 498449375 := bstep (se 1 (by rfl) ⟨373837031, by rfl⟩ : syracuseStep 498449375 = 747674063) B747674063
theorem B15563771 : Blo 1596997 15563771 := bstep (se 1 (by rfl) ⟨11672828, by rfl⟩ : syracuseStep 15563771 = 23345657) B23345657
theorem B189267353 : Blo 1596997 189267353 := bstep (se 2 (by rfl) ⟨70975257, by rfl⟩ : syracuseStep 189267353 = 141950515) B141950515
theorem B1597467 : Blo 1596997 1597467 := bstep (se 1 (by rfl) ⟨1198100, by rfl⟩ : syracuseStep 1597467 = 2396201) B2396201
theorem B27681065 : Blo 1596997 27681065 := bstep (se 2 (by rfl) ⟨10380399, by rfl⟩ : syracuseStep 27681065 = 20760799) B20760799
theorem B2695963 : Blo 1596997 2695963 := bstep (se 1 (by rfl) ⟨2021972, by rfl⟩ : syracuseStep 2695963 = 4043945) B4043945
theorem B1598491 : Blo 1596997 1598491 := bstep (se 1 (by rfl) ⟨1198868, by rfl⟩ : syracuseStep 1598491 = 2397737) B2397737
theorem B1598703 : Blo 1596997 1598703 := bstep (se 1 (by rfl) ⟨1199027, by rfl⟩ : syracuseStep 1598703 = 2398055) B2398055
theorem B1598791 : Blo 1596997 1598791 := bstep (se 1 (by rfl) ⟨1199093, by rfl⟩ : syracuseStep 1598791 = 2398187) B2398187
theorem B3597695 : Blo 1596997 3597695 := bstep (se 1 (by rfl) ⟨2698271, by rfl⟩ : syracuseStep 3597695 = 5396543) B5396543
theorem B3032731 : Blo 1596997 3032731 := bstep (se 1 (by rfl) ⟨2274548, by rfl⟩ : syracuseStep 3032731 = 4549097) B4549097
theorem B5392439 : Blo 1596997 5392439 := bstep (se 1 (by rfl) ⟨4044329, by rfl⟩ : syracuseStep 5392439 = 8088659) B8088659
theorem B2395631 : Blo 1596997 2395631 := bstep (se 1 (by rfl) ⟨1796723, by rfl⟩ : syracuseStep 2395631 = 3593447) B3593447
theorem B13643599 : Blo 1596997 13643599 := bstep (se 1 (by rfl) ⟨10232699, by rfl⟩ : syracuseStep 13643599 = 20465399) B20465399
theorem B2396297 : Blo 1596997 2396297 := bstep (se 2 (by rfl) ⟨898611, by rfl⟩ : syracuseStep 2396297 = 1797223) B1797223
theorem B1798447 : Blo 1596997 1798447 := bstep (se 1 (by rfl) ⟨1348835, by rfl⟩ : syracuseStep 1798447 = 2697671) B2697671
theorem B4043105 : Blo 1596997 4043105 := bstep (se 2 (by rfl) ⟨1516164, by rfl⟩ : syracuseStep 4043105 = 3032329) B3032329
theorem B1798591 : Blo 1596997 1798591 := bstep (se 1 (by rfl) ⟨1348943, by rfl⟩ : syracuseStep 1798591 = 2697887) B2697887
theorem B10375847 : Blo 1596997 10375847 := bstep (se 1 (by rfl) ⟨7781885, by rfl⟩ : syracuseStep 10375847 = 15563771) B15563771
theorem B29160233 : Blo 1596997 29160233 := bstep (se 2 (by rfl) ⟨10935087, by rfl⟩ : syracuseStep 29160233 = 21870175) B21870175
theorem B126178235 : Blo 1596997 126178235 := bstep (se 1 (by rfl) ⟨94633676, by rfl⟩ : syracuseStep 126178235 = 189267353) B189267353
theorem B4043803 : Blo 1596997 4043803 := bstep (se 1 (by rfl) ⟨3032852, by rfl⟩ : syracuseStep 4043803 = 6065705) B6065705
theorem B10237265 : Blo 1596997 10237265 := bstep (se 2 (by rfl) ⟨3838974, by rfl⟩ : syracuseStep 10237265 = 7677949) B7677949
theorem B2594495 : Blo 1596997 2594495 := bstep (se 1 (by rfl) ⟨1945871, by rfl⟩ : syracuseStep 2594495 = 3891743) B3891743
theorem B12130559 : Blo 1596997 12130559 := bstep (se 1 (by rfl) ⟨9097919, by rfl⟩ : syracuseStep 12130559 = 18195839) B18195839
theorem B23042951 : Blo 1596997 23042951 := bstep (se 1 (by rfl) ⟨17282213, by rfl⟩ : syracuseStep 23042951 = 34564427) B34564427
theorem B332299583 : Blo 1596997 332299583 := bstep (se 1 (by rfl) ⟨249224687, by rfl⟩ : syracuseStep 332299583 = 498449375) B498449375
theorem B65576375 : Blo 1596997 65576375 := bstep (se 1 (by rfl) ⟨49182281, by rfl⟩ : syracuseStep 65576375 = 98364563) B98364563
theorem B3595823 : Blo 1596997 3595823 := bstep (se 1 (by rfl) ⟨2696867, by rfl⟩ : syracuseStep 3595823 = 5393735) B5393735
theorem B1597135 : Blo 1596997 1597135 := bstep (se 1 (by rfl) ⟨1197851, by rfl⟩ : syracuseStep 1597135 = 2395703) B2395703
theorem B1597183 : Blo 1596997 1597183 := bstep (se 1 (by rfl) ⟨1197887, by rfl⟩ : syracuseStep 1597183 = 2395775) B2395775
theorem B1597531 : Blo 1596997 1597531 := bstep (se 1 (by rfl) ⟨1198148, by rfl⟩ : syracuseStep 1597531 = 2396297) B2396297
theorem B2695403 : Blo 1596997 2695403 := bstep (se 1 (by rfl) ⟨2021552, by rfl⟩ : syracuseStep 2695403 = 4043105) B4043105
theorem B19440155 : Blo 1596997 19440155 := bstep (se 1 (by rfl) ⟨14580116, by rfl⟩ : syracuseStep 19440155 = 29160233) B29160233
theorem B6824843 : Blo 1596997 6824843 := bstep (se 1 (by rfl) ⟨5118632, by rfl⟩ : syracuseStep 6824843 = 10237265) B10237265
theorem B1729663 : Blo 1596997 1729663 := bstep (se 1 (by rfl) ⟨1297247, by rfl⟩ : syracuseStep 1729663 = 2594495) B2594495
theorem B5391737 : Blo 1596997 5391737 := bstep (se 2 (by rfl) ⟨2021901, by rfl⟩ : syracuseStep 5391737 = 4043803) B4043803
theorem B8087039 : Blo 1596997 8087039 := bstep (se 1 (by rfl) ⟨6065279, by rfl⟩ : syracuseStep 8087039 = 12130559) B12130559
theorem B15361967 : Blo 1596997 15361967 := bstep (se 1 (by rfl) ⟨11521475, by rfl⟩ : syracuseStep 15361967 = 23042951) B23042951
theorem B6917231 : Blo 1596997 6917231 := bstep (se 1 (by rfl) ⟨5187923, by rfl⟩ : syracuseStep 6917231 = 10375847) B10375847
theorem B84118823 : Blo 1596997 84118823 := bstep (se 1 (by rfl) ⟨63089117, by rfl⟩ : syracuseStep 84118823 = 126178235) B126178235
theorem B4043641 : Blo 1596997 4043641 := bstep (se 2 (by rfl) ⟨1516365, by rfl⟩ : syracuseStep 4043641 = 3032731) B3032731
theorem B221533055 : Blo 1596997 221533055 := bstep (se 1 (by rfl) ⟨166149791, by rfl⟩ : syracuseStep 221533055 = 332299583) B332299583
theorem B43717583 : Blo 1596997 43717583 := bstep (se 1 (by rfl) ⟨32788187, by rfl⟩ : syracuseStep 43717583 = 65576375) B65576375
theorem B2397215 : Blo 1596997 2397215 := bstep (se 1 (by rfl) ⟨1797911, by rfl⟩ : syracuseStep 2397215 = 3595823) B3595823
theorem B18191465 : Blo 1596997 18191465 := bstep (se 2 (by rfl) ⟨6821799, by rfl⟩ : syracuseStep 18191465 = 13643599) B13643599
theorem B18454043 : Blo 1596997 18454043 := bstep (se 1 (by rfl) ⟨13840532, by rfl⟩ : syracuseStep 18454043 = 27681065) B27681065
theorem B2397929 : Blo 1596997 2397929 := bstep (se 2 (by rfl) ⟨899223, by rfl⟩ : syracuseStep 2397929 = 1798447) B1798447
theorem B2398121 : Blo 1596997 2398121 := bstep (se 2 (by rfl) ⟨899295, by rfl⟩ : syracuseStep 2398121 = 1798591) B1798591
theorem B2398463 : Blo 1596997 2398463 := bstep (se 1 (by rfl) ⟨1798847, by rfl⟩ : syracuseStep 2398463 = 3597695) B3597695
theorem B3594617 : Blo 1596997 3594617 := bstep (se 2 (by rfl) ⟨1347981, by rfl⟩ : syracuseStep 3594617 = 2695963) B2695963
theorem B3594959 : Blo 1596997 3594959 := bstep (se 1 (by rfl) ⟨2696219, by rfl⟩ : syracuseStep 3594959 = 5392439) B5392439
theorem B1597087 : Blo 1596997 1597087 := bstep (se 1 (by rfl) ⟨1197815, by rfl⟩ : syracuseStep 1597087 = 2395631) B2395631
theorem B12960103 : Blo 1596997 12960103 := bstep (se 1 (by rfl) ⟨9720077, by rfl⟩ : syracuseStep 12960103 = 19440155) B19440155
theorem B9224869 : Blo 1596997 9224869 := bstep (se 4 (by rfl) ⟨864831, by rfl⟩ : syracuseStep 9224869 = 1729663) B1729663
theorem B1598143 : Blo 1596997 1598143 := bstep (se 1 (by rfl) ⟨1198607, by rfl⟩ : syracuseStep 1598143 = 2397215) B2397215
theorem B5391359 : Blo 1596997 5391359 := bstep (se 1 (by rfl) ⟨4043519, by rfl⟩ : syracuseStep 5391359 = 8087039) B8087039
theorem B1598619 : Blo 1596997 1598619 := bstep (se 1 (by rfl) ⟨1198964, by rfl⟩ : syracuseStep 1598619 = 2397929) B2397929
theorem B5391521 : Blo 1596997 5391521 := bstep (se 2 (by rfl) ⟨2021820, by rfl⟩ : syracuseStep 5391521 = 4043641) B4043641
theorem B1598747 : Blo 1596997 1598747 := bstep (se 1 (by rfl) ⟨1199060, by rfl⟩ : syracuseStep 1598747 = 2398121) B2398121
theorem B10241311 : Blo 1596997 10241311 := bstep (se 1 (by rfl) ⟨7680983, by rfl⟩ : syracuseStep 10241311 = 15361967) B15361967
theorem B1598975 : Blo 1596997 1598975 := bstep (se 1 (by rfl) ⟨1199231, by rfl⟩ : syracuseStep 1598975 = 2398463) B2398463
theorem B1796935 : Blo 1596997 1796935 := bstep (se 1 (by rfl) ⟨1347701, by rfl⟩ : syracuseStep 1796935 = 2695403) B2695403
theorem B147688703 : Blo 1596997 147688703 := bstep (se 1 (by rfl) ⟨110766527, by rfl⟩ : syracuseStep 147688703 = 221533055) B221533055
theorem B4549895 : Blo 1596997 4549895 := bstep (se 1 (by rfl) ⟨3412421, by rfl⟩ : syracuseStep 4549895 = 6824843) B6824843
theorem B12127643 : Blo 1596997 12127643 := bstep (se 1 (by rfl) ⟨9095732, by rfl⟩ : syracuseStep 12127643 = 18191465) B18191465
theorem B2396411 : Blo 1596997 2396411 := bstep (se 1 (by rfl) ⟨1797308, by rfl⟩ : syracuseStep 2396411 = 3594617) B3594617
theorem B2396639 : Blo 1596997 2396639 := bstep (se 1 (by rfl) ⟨1797479, by rfl⟩ : syracuseStep 2396639 = 3594959) B3594959
theorem B56079215 : Blo 1596997 56079215 := bstep (se 1 (by rfl) ⟨42059411, by rfl⟩ : syracuseStep 56079215 = 84118823) B84118823
theorem B29145055 : Blo 1596997 29145055 := bstep (se 1 (by rfl) ⟨21858791, by rfl⟩ : syracuseStep 29145055 = 43717583) B43717583
theorem B3594491 : Blo 1596997 3594491 := bstep (se 1 (by rfl) ⟨2695868, by rfl⟩ : syracuseStep 3594491 = 5391737) B5391737
theorem B12302695 : Blo 1596997 12302695 := bstep (se 1 (by rfl) ⟨9227021, by rfl⟩ : syracuseStep 12302695 = 18454043) B18454043
theorem B4611487 : Blo 1596997 4611487 := bstep (se 1 (by rfl) ⟨3458615, by rfl⟩ : syracuseStep 4611487 = 6917231) B6917231
theorem B1597607 : Blo 1596997 1597607 := bstep (se 1 (by rfl) ⟨1198205, by rfl⟩ : syracuseStep 1597607 = 2396411) B2396411
theorem B1597759 : Blo 1596997 1597759 := bstep (se 1 (by rfl) ⟨1198319, by rfl⟩ : syracuseStep 1597759 = 2396639) B2396639
theorem B3033263 : Blo 1596997 3033263 := bstep (se 1 (by rfl) ⟨2274947, by rfl⟩ : syracuseStep 3033263 = 4549895) B4549895
theorem B17280137 : Blo 1596997 17280137 := bstep (se 2 (by rfl) ⟨6480051, by rfl⟩ : syracuseStep 17280137 = 12960103) B12960103
theorem B16403593 : Blo 1596997 16403593 := bstep (se 2 (by rfl) ⟨6151347, by rfl⟩ : syracuseStep 16403593 = 12302695) B12302695
theorem B12299825 : Blo 1596997 12299825 := bstep (se 2 (by rfl) ⟨4612434, by rfl⟩ : syracuseStep 12299825 = 9224869) B9224869
theorem B2395913 : Blo 1596997 2395913 := bstep (se 2 (by rfl) ⟨898467, by rfl⟩ : syracuseStep 2395913 = 1796935) B1796935
theorem B2396327 : Blo 1596997 2396327 := bstep (se 1 (by rfl) ⟨1797245, by rfl⟩ : syracuseStep 2396327 = 3594491) B3594491
theorem B6148649 : Blo 1596997 6148649 := bstep (se 2 (by rfl) ⟨2305743, by rfl⟩ : syracuseStep 6148649 = 4611487) B4611487
theorem B38860073 : Blo 1596997 38860073 := bstep (se 2 (by rfl) ⟨14572527, by rfl⟩ : syracuseStep 38860073 = 29145055) B29145055
theorem B37386143 : Blo 1596997 37386143 := bstep (se 1 (by rfl) ⟨28039607, by rfl⟩ : syracuseStep 37386143 = 56079215) B56079215
theorem B3594239 : Blo 1596997 3594239 := bstep (se 1 (by rfl) ⟨2695679, by rfl⟩ : syracuseStep 3594239 = 5391359) B5391359
theorem B3594347 : Blo 1596997 3594347 := bstep (se 1 (by rfl) ⟨2695760, by rfl⟩ : syracuseStep 3594347 = 5391521) B5391521
theorem B13655081 : Blo 1596997 13655081 := bstep (se 2 (by rfl) ⟨5120655, by rfl⟩ : syracuseStep 13655081 = 10241311) B10241311
theorem B98459135 : Blo 1596997 98459135 := bstep (se 1 (by rfl) ⟨73844351, by rfl⟩ : syracuseStep 98459135 = 147688703) B147688703
theorem B8085095 : Blo 1596997 8085095 := bstep (se 1 (by rfl) ⟨6063821, by rfl⟩ : syracuseStep 8085095 = 12127643) B12127643
theorem B1597551 : Blo 1596997 1597551 := bstep (se 1 (by rfl) ⟨1198163, by rfl⟩ : syracuseStep 1597551 = 2396327) B2396327
theorem B9103387 : Blo 1596997 9103387 := bstep (se 1 (by rfl) ⟨6827540, by rfl⟩ : syracuseStep 9103387 = 13655081) B13655081
theorem B11520091 : Blo 1596997 11520091 := bstep (se 1 (by rfl) ⟨8640068, by rfl⟩ : syracuseStep 11520091 = 17280137) B17280137
theorem B4099099 : Blo 1596997 4099099 := bstep (se 1 (by rfl) ⟨3074324, by rfl⟩ : syracuseStep 4099099 = 6148649) B6148649
theorem B25906715 : Blo 1596997 25906715 := bstep (se 1 (by rfl) ⟨19430036, by rfl⟩ : syracuseStep 25906715 = 38860073) B38860073
theorem B24924095 : Blo 1596997 24924095 := bstep (se 1 (by rfl) ⟨18693071, by rfl⟩ : syracuseStep 24924095 = 37386143) B37386143
theorem B2396159 : Blo 1596997 2396159 := bstep (se 1 (by rfl) ⟨1797119, by rfl⟩ : syracuseStep 2396159 = 3594239) B3594239
theorem B2396231 : Blo 1596997 2396231 := bstep (se 1 (by rfl) ⟨1797173, by rfl⟩ : syracuseStep 2396231 = 3594347) B3594347
theorem B65639423 : Blo 1596997 65639423 := bstep (se 1 (by rfl) ⟨49229567, by rfl⟩ : syracuseStep 65639423 = 98459135) B98459135
theorem B2022175 : Blo 1596997 2022175 := bstep (se 1 (by rfl) ⟨1516631, by rfl⟩ : syracuseStep 2022175 = 3033263) B3033263
theorem B21871457 : Blo 1596997 21871457 := bstep (se 2 (by rfl) ⟨8201796, by rfl⟩ : syracuseStep 21871457 = 16403593) B16403593
theorem B8199883 : Blo 1596997 8199883 := bstep (se 1 (by rfl) ⟨6149912, by rfl⟩ : syracuseStep 8199883 = 12299825) B12299825
theorem B5390063 : Blo 1596997 5390063 := bstep (se 1 (by rfl) ⟨4042547, by rfl⟩ : syracuseStep 5390063 = 8085095) B8085095
theorem B1597275 : Blo 1596997 1597275 := bstep (se 1 (by rfl) ⟨1197956, by rfl⟩ : syracuseStep 1597275 = 2395913) B2395913
theorem B1597487 : Blo 1596997 1597487 := bstep (se 1 (by rfl) ⟨1198115, by rfl⟩ : syracuseStep 1597487 = 2396231) B2396231
theorem B15360121 : Blo 1596997 15360121 := bstep (se 2 (by rfl) ⟨5760045, by rfl⟩ : syracuseStep 15360121 = 11520091) B11520091
theorem B2696233 : Blo 1596997 2696233 := bstep (se 2 (by rfl) ⟨1011087, by rfl⟩ : syracuseStep 2696233 = 2022175) B2022175
theorem B5465465 : Blo 1596997 5465465 := bstep (se 2 (by rfl) ⟨2049549, by rfl⟩ : syracuseStep 5465465 = 4099099) B4099099
theorem B17271143 : Blo 1596997 17271143 := bstep (se 1 (by rfl) ⟨12953357, by rfl⟩ : syracuseStep 17271143 = 25906715) B25906715
theorem B16616063 : Blo 1596997 16616063 := bstep (se 1 (by rfl) ⟨12462047, by rfl⟩ : syracuseStep 16616063 = 24924095) B24924095
theorem B43732709 : Blo 1596997 43732709 := bstep (se 4 (by rfl) ⟨4099941, by rfl⟩ : syracuseStep 43732709 = 8199883) B8199883
theorem B3593375 : Blo 1596997 3593375 := bstep (se 1 (by rfl) ⟨2695031, by rfl⟩ : syracuseStep 3593375 = 5390063) B5390063
theorem B12137849 : Blo 1596997 12137849 := bstep (se 2 (by rfl) ⟨4551693, by rfl⟩ : syracuseStep 12137849 = 9103387) B9103387
theorem B43759615 : Blo 1596997 43759615 := bstep (se 1 (by rfl) ⟨32819711, by rfl⟩ : syracuseStep 43759615 = 65639423) B65639423
theorem B14580971 : Blo 1596997 14580971 := bstep (se 1 (by rfl) ⟨10935728, by rfl⟩ : syracuseStep 14580971 = 21871457) B21871457
theorem B1597439 : Blo 1596997 1597439 := bstep (se 1 (by rfl) ⟨1198079, by rfl⟩ : syracuseStep 1597439 = 2396159) B2396159
theorem B20480161 : Blo 1596997 20480161 := bstep (se 2 (by rfl) ⟨7680060, by rfl⟩ : syracuseStep 20480161 = 15360121) B15360121
theorem B58346153 : Blo 1596997 58346153 := bstep (se 2 (by rfl) ⟨21879807, by rfl⟩ : syracuseStep 58346153 = 43759615) B43759615
theorem B2395583 : Blo 1596997 2395583 := bstep (se 1 (by rfl) ⟨1796687, by rfl⟩ : syracuseStep 2395583 = 3593375) B3593375
theorem B11514095 : Blo 1596997 11514095 := bstep (se 1 (by rfl) ⟨8635571, by rfl⟩ : syracuseStep 11514095 = 17271143) B17271143
theorem B9720647 : Blo 1596997 9720647 := bstep (se 1 (by rfl) ⟨7290485, by rfl⟩ : syracuseStep 9720647 = 14580971) B14580971
theorem B3643643 : Blo 1596997 3643643 := bstep (se 1 (by rfl) ⟨2732732, by rfl⟩ : syracuseStep 3643643 = 5465465) B5465465
theorem B8091899 : Blo 1596997 8091899 := bstep (se 1 (by rfl) ⟨6068924, by rfl⟩ : syracuseStep 8091899 = 12137849) B12137849
theorem B3594977 : Blo 1596997 3594977 := bstep (se 2 (by rfl) ⟨1348116, by rfl⟩ : syracuseStep 3594977 = 2696233) B2696233
theorem B44309501 : Blo 1596997 44309501 := bstep (se 3 (by rfl) ⟨8308031, by rfl⟩ : syracuseStep 44309501 = 16616063) B16616063
theorem B29155139 : Blo 1596997 29155139 := bstep (se 1 (by rfl) ⟨21866354, by rfl⟩ : syracuseStep 29155139 = 43732709) B43732709
theorem B7676063 : Blo 1596997 7676063 := bstep (se 1 (by rfl) ⟨5757047, by rfl⟩ : syracuseStep 7676063 = 11514095) B11514095
theorem B6480431 : Blo 1596997 6480431 := bstep (se 1 (by rfl) ⟨4860323, by rfl⟩ : syracuseStep 6480431 = 9720647) B9720647
theorem B9716381 : Blo 1596997 9716381 := bstep (se 3 (by rfl) ⟨1821821, by rfl⟩ : syracuseStep 9716381 = 3643643) B3643643
theorem B38897435 : Blo 1596997 38897435 := bstep (se 1 (by rfl) ⟨29173076, by rfl⟩ : syracuseStep 38897435 = 58346153) B58346153
theorem B27306881 : Blo 1596997 27306881 := bstep (se 2 (by rfl) ⟨10240080, by rfl⟩ : syracuseStep 27306881 = 20480161) B20480161
theorem B5394599 : Blo 1596997 5394599 := bstep (se 1 (by rfl) ⟨4045949, by rfl⟩ : syracuseStep 5394599 = 8091899) B8091899
theorem B2396651 : Blo 1596997 2396651 := bstep (se 1 (by rfl) ⟨1797488, by rfl⟩ : syracuseStep 2396651 = 3594977) B3594977
theorem B19436759 : Blo 1596997 19436759 := bstep (se 1 (by rfl) ⟨14577569, by rfl⟩ : syracuseStep 19436759 = 29155139) B29155139
theorem B29539667 : Blo 1596997 29539667 := bstep (se 1 (by rfl) ⟨22154750, by rfl⟩ : syracuseStep 29539667 = 44309501) B44309501
theorem B1597055 : Blo 1596997 1597055 := bstep (se 1 (by rfl) ⟨1197791, by rfl⟩ : syracuseStep 1597055 = 2395583) B2395583
theorem B3596399 : Blo 1596997 3596399 := bstep (se 1 (by rfl) ⟨2697299, by rfl⟩ : syracuseStep 3596399 = 5394599) B5394599
theorem B1597767 : Blo 1596997 1597767 := bstep (se 1 (by rfl) ⟨1198325, by rfl⟩ : syracuseStep 1597767 = 2396651) B2396651
theorem B18204587 : Blo 1596997 18204587 := bstep (se 1 (by rfl) ⟨13653440, by rfl⟩ : syracuseStep 18204587 = 27306881) B27306881
theorem B4320287 : Blo 1596997 4320287 := bstep (se 1 (by rfl) ⟨3240215, by rfl⟩ : syracuseStep 4320287 = 6480431) B6480431
theorem B5117375 : Blo 1596997 5117375 := bstep (se 1 (by rfl) ⟨3838031, by rfl⟩ : syracuseStep 5117375 = 7676063) B7676063
theorem B6477587 : Blo 1596997 6477587 := bstep (se 1 (by rfl) ⟨4858190, by rfl⟩ : syracuseStep 6477587 = 9716381) B9716381
theorem B12957839 : Blo 1596997 12957839 := bstep (se 1 (by rfl) ⟨9718379, by rfl⟩ : syracuseStep 12957839 = 19436759) B19436759
theorem B78772445 : Blo 1596997 78772445 := bstep (se 3 (by rfl) ⟨14769833, by rfl⟩ : syracuseStep 78772445 = 29539667) B29539667
theorem B103726493 : Blo 1596997 103726493 := bstep (se 3 (by rfl) ⟨19448717, by rfl⟩ : syracuseStep 103726493 = 38897435) B38897435
theorem B4318391 : Blo 1596997 4318391 := bstep (se 1 (by rfl) ⟨3238793, by rfl⟩ : syracuseStep 4318391 = 6477587) B6477587
theorem B69150995 : Blo 1596997 69150995 := bstep (se 1 (by rfl) ⟨51863246, by rfl⟩ : syracuseStep 69150995 = 103726493) B103726493
theorem B12136391 : Blo 1596997 12136391 := bstep (se 1 (by rfl) ⟨9102293, by rfl⟩ : syracuseStep 12136391 = 18204587) B18204587
theorem B8638559 : Blo 1596997 8638559 := bstep (se 1 (by rfl) ⟨6478919, by rfl⟩ : syracuseStep 8638559 = 12957839) B12957839
theorem B52514963 : Blo 1596997 52514963 := bstep (se 1 (by rfl) ⟨39386222, by rfl⟩ : syracuseStep 52514963 = 78772445) B78772445
theorem B2880191 : Blo 1596997 2880191 := bstep (se 1 (by rfl) ⟨2160143, by rfl⟩ : syracuseStep 2880191 = 4320287) B4320287
theorem B2397599 : Blo 1596997 2397599 := bstep (se 1 (by rfl) ⟨1798199, by rfl⟩ : syracuseStep 2397599 = 3596399) B3596399
theorem B13646333 : Blo 1596997 13646333 := bstep (se 3 (by rfl) ⟨2558687, by rfl⟩ : syracuseStep 13646333 = 5117375) B5117375
theorem B5759039 : Blo 1596997 5759039 := bstep (se 1 (by rfl) ⟨4319279, by rfl⟩ : syracuseStep 5759039 = 8638559) B8638559
theorem B1598399 : Blo 1596997 1598399 := bstep (se 1 (by rfl) ⟨1198799, by rfl⟩ : syracuseStep 1598399 = 2397599) B2397599
theorem B1920127 : Blo 1596997 1920127 := bstep (se 1 (by rfl) ⟨1440095, by rfl⟩ : syracuseStep 1920127 = 2880191) B2880191
theorem B46100663 : Blo 1596997 46100663 := bstep (se 1 (by rfl) ⟨34575497, by rfl⟩ : syracuseStep 46100663 = 69150995) B69150995
theorem B9097555 : Blo 1596997 9097555 := bstep (se 1 (by rfl) ⟨6823166, by rfl⟩ : syracuseStep 9097555 = 13646333) B13646333
theorem B8090927 : Blo 1596997 8090927 := bstep (se 1 (by rfl) ⟨6068195, by rfl⟩ : syracuseStep 8090927 = 12136391) B12136391
theorem B35009975 : Blo 1596997 35009975 := bstep (se 1 (by rfl) ⟨26257481, by rfl⟩ : syracuseStep 35009975 = 52514963) B52514963
theorem B11515709 : Blo 1596997 11515709 := bstep (se 3 (by rfl) ⟨2159195, by rfl⟩ : syracuseStep 11515709 = 4318391) B4318391
theorem B23339983 : Blo 1596997 23339983 := bstep (se 1 (by rfl) ⟨17504987, by rfl⟩ : syracuseStep 23339983 = 35009975) B35009975
theorem B5393951 : Blo 1596997 5393951 := bstep (se 1 (by rfl) ⟨4045463, by rfl⟩ : syracuseStep 5393951 = 8090927) B8090927
theorem B2560169 : Blo 1596997 2560169 := bstep (se 2 (by rfl) ⟨960063, by rfl⟩ : syracuseStep 2560169 = 1920127) B1920127
theorem B30708557 : Blo 1596997 30708557 := bstep (se 3 (by rfl) ⟨5757854, by rfl⟩ : syracuseStep 30708557 = 11515709) B11515709
theorem B3839359 : Blo 1596997 3839359 := bstep (se 1 (by rfl) ⟨2879519, by rfl⟩ : syracuseStep 3839359 = 5759039) B5759039
theorem B30733775 : Blo 1596997 30733775 := bstep (se 1 (by rfl) ⟨23050331, by rfl⟩ : syracuseStep 30733775 = 46100663) B46100663
theorem B12130073 : Blo 1596997 12130073 := bstep (se 2 (by rfl) ⟨4548777, by rfl⟩ : syracuseStep 12130073 = 9097555) B9097555
theorem B20472371 : Blo 1596997 20472371 := bstep (se 1 (by rfl) ⟨15354278, by rfl⟩ : syracuseStep 20472371 = 30708557) B30708557
theorem B20489183 : Blo 1596997 20489183 := bstep (se 1 (by rfl) ⟨15366887, by rfl⟩ : syracuseStep 20489183 = 30733775) B30733775
theorem B8086715 : Blo 1596997 8086715 := bstep (se 1 (by rfl) ⟨6065036, by rfl⟩ : syracuseStep 8086715 = 12130073) B12130073
theorem B1706779 : Blo 1596997 1706779 := bstep (se 1 (by rfl) ⟨1280084, by rfl⟩ : syracuseStep 1706779 = 2560169) B2560169
theorem B31119977 : Blo 1596997 31119977 := bstep (se 2 (by rfl) ⟨11669991, by rfl⟩ : syracuseStep 31119977 = 23339983) B23339983
theorem B5119145 : Blo 1596997 5119145 := bstep (se 2 (by rfl) ⟨1919679, by rfl⟩ : syracuseStep 5119145 = 3839359) B3839359
theorem B3595967 : Blo 1596997 3595967 := bstep (se 1 (by rfl) ⟨2696975, by rfl⟩ : syracuseStep 3595967 = 5393951) B5393951
theorem B13648247 : Blo 1596997 13648247 := bstep (se 1 (by rfl) ⟨10236185, by rfl⟩ : syracuseStep 13648247 = 20472371) B20472371
theorem B5391143 : Blo 1596997 5391143 := bstep (se 1 (by rfl) ⟨4043357, by rfl⟩ : syracuseStep 5391143 = 8086715) B8086715
theorem B82986605 : Blo 1596997 82986605 := bstep (se 3 (by rfl) ⟨15559988, by rfl⟩ : syracuseStep 82986605 = 31119977) B31119977
theorem B13659455 : Blo 1596997 13659455 := bstep (se 1 (by rfl) ⟨10244591, by rfl⟩ : syracuseStep 13659455 = 20489183) B20489183
theorem B3412763 : Blo 1596997 3412763 := bstep (se 1 (by rfl) ⟨2559572, by rfl⟩ : syracuseStep 3412763 = 5119145) B5119145
theorem B2397311 : Blo 1596997 2397311 := bstep (se 1 (by rfl) ⟨1797983, by rfl⟩ : syracuseStep 2397311 = 3595967) B3595967
theorem B2275705 : Blo 1596997 2275705 := bstep (se 2 (by rfl) ⟨853389, by rfl⟩ : syracuseStep 2275705 = 1706779) B1706779
theorem B1598207 : Blo 1596997 1598207 := bstep (se 1 (by rfl) ⟨1198655, by rfl⟩ : syracuseStep 1598207 = 2397311) B2397311
theorem B3034273 : Blo 1596997 3034273 := bstep (se 2 (by rfl) ⟨1137852, by rfl⟩ : syracuseStep 3034273 = 2275705) B2275705
theorem B55324403 : Blo 1596997 55324403 := bstep (se 1 (by rfl) ⟨41493302, by rfl⟩ : syracuseStep 55324403 = 82986605) B82986605
theorem B9106303 : Blo 1596997 9106303 := bstep (se 1 (by rfl) ⟨6829727, by rfl⟩ : syracuseStep 9106303 = 13659455) B13659455
theorem B9098831 : Blo 1596997 9098831 := bstep (se 1 (by rfl) ⟨6824123, by rfl⟩ : syracuseStep 9098831 = 13648247) B13648247
theorem B2275175 : Blo 1596997 2275175 := bstep (se 1 (by rfl) ⟨1706381, by rfl⟩ : syracuseStep 2275175 = 3412763) B3412763
theorem B3594095 : Blo 1596997 3594095 := bstep (se 1 (by rfl) ⟨2695571, by rfl⟩ : syracuseStep 3594095 = 5391143) B5391143
theorem B12141737 : Blo 1596997 12141737 := bstep (se 2 (by rfl) ⟨4553151, by rfl⟩ : syracuseStep 12141737 = 9106303) B9106303
theorem B36882935 : Blo 1596997 36882935 := bstep (se 1 (by rfl) ⟨27662201, by rfl⟩ : syracuseStep 36882935 = 55324403) B55324403
theorem B6065887 : Blo 1596997 6065887 := bstep (se 1 (by rfl) ⟨4549415, by rfl⟩ : syracuseStep 6065887 = 9098831) B9098831
theorem B2396063 : Blo 1596997 2396063 := bstep (se 1 (by rfl) ⟨1797047, by rfl⟩ : syracuseStep 2396063 = 3594095) B3594095
theorem B6067133 : Blo 1596997 6067133 := bstep (se 3 (by rfl) ⟨1137587, by rfl⟩ : syracuseStep 6067133 = 2275175) B2275175
theorem B4045697 : Blo 1596997 4045697 := bstep (se 2 (by rfl) ⟨1517136, by rfl⟩ : syracuseStep 4045697 = 3034273) B3034273
theorem B8094491 : Blo 1596997 8094491 := bstep (se 1 (by rfl) ⟨6070868, by rfl⟩ : syracuseStep 8094491 = 12141737) B12141737
theorem B2697131 : Blo 1596997 2697131 := bstep (se 1 (by rfl) ⟨2022848, by rfl⟩ : syracuseStep 2697131 = 4045697) B4045697
theorem B8087849 : Blo 1596997 8087849 := bstep (se 2 (by rfl) ⟨3032943, by rfl⟩ : syracuseStep 8087849 = 6065887) B6065887
theorem B24588623 : Blo 1596997 24588623 := bstep (se 1 (by rfl) ⟨18441467, by rfl⟩ : syracuseStep 24588623 = 36882935) B36882935
theorem B4044755 : Blo 1596997 4044755 := bstep (se 1 (by rfl) ⟨3033566, by rfl⟩ : syracuseStep 4044755 = 6067133) B6067133
theorem B1597375 : Blo 1596997 1597375 := bstep (se 1 (by rfl) ⟨1198031, by rfl⟩ : syracuseStep 1597375 = 2396063) B2396063
theorem B16392415 : Blo 1596997 16392415 := bstep (se 1 (by rfl) ⟨12294311, by rfl⟩ : syracuseStep 16392415 = 24588623) B24588623
theorem B2696503 : Blo 1596997 2696503 := bstep (se 1 (by rfl) ⟨2022377, by rfl⟩ : syracuseStep 2696503 = 4044755) B4044755
theorem B5391899 : Blo 1596997 5391899 := bstep (se 1 (by rfl) ⟨4043924, by rfl⟩ : syracuseStep 5391899 = 8087849) B8087849
theorem B1798087 : Blo 1596997 1798087 := bstep (se 1 (by rfl) ⟨1348565, by rfl⟩ : syracuseStep 1798087 = 2697131) B2697131
theorem B5396327 : Blo 1596997 5396327 := bstep (se 1 (by rfl) ⟨4047245, by rfl⟩ : syracuseStep 5396327 = 8094491) B8094491
theorem B21856553 : Blo 1596997 21856553 := bstep (se 2 (by rfl) ⟨8196207, by rfl⟩ : syracuseStep 21856553 = 16392415) B16392415
theorem B3597551 : Blo 1596997 3597551 := bstep (se 1 (by rfl) ⟨2698163, by rfl⟩ : syracuseStep 3597551 = 5396327) B5396327
theorem B2397449 : Blo 1596997 2397449 := bstep (se 2 (by rfl) ⟨899043, by rfl⟩ : syracuseStep 2397449 = 1798087) B1798087
theorem B3594599 : Blo 1596997 3594599 := bstep (se 1 (by rfl) ⟨2695949, by rfl⟩ : syracuseStep 3594599 = 5391899) B5391899
theorem B3595337 : Blo 1596997 3595337 := bstep (se 2 (by rfl) ⟨1348251, by rfl⟩ : syracuseStep 3595337 = 2696503) B2696503
theorem B1598299 : Blo 1596997 1598299 := bstep (se 1 (by rfl) ⟨1198724, by rfl⟩ : syracuseStep 1598299 = 2397449) B2397449
theorem B2396399 : Blo 1596997 2396399 := bstep (se 1 (by rfl) ⟨1797299, by rfl⟩ : syracuseStep 2396399 = 3594599) B3594599
theorem B2396891 : Blo 1596997 2396891 := bstep (se 1 (by rfl) ⟨1797668, by rfl⟩ : syracuseStep 2396891 = 3595337) B3595337
theorem B14571035 : Blo 1596997 14571035 := bstep (se 1 (by rfl) ⟨10928276, by rfl⟩ : syracuseStep 14571035 = 21856553) B21856553
theorem B2398367 : Blo 1596997 2398367 := bstep (se 1 (by rfl) ⟨1798775, by rfl⟩ : syracuseStep 2398367 = 3597551) B3597551
theorem B1597599 : Blo 1596997 1597599 := bstep (se 1 (by rfl) ⟨1198199, by rfl⟩ : syracuseStep 1597599 = 2396399) B2396399
theorem B1597927 : Blo 1596997 1597927 := bstep (se 1 (by rfl) ⟨1198445, by rfl⟩ : syracuseStep 1597927 = 2396891) B2396891
theorem B1598911 : Blo 1596997 1598911 := bstep (se 1 (by rfl) ⟨1199183, by rfl⟩ : syracuseStep 1598911 = 2398367) B2398367
theorem B9714023 : Blo 1596997 9714023 := bstep (se 1 (by rfl) ⟨7285517, by rfl⟩ : syracuseStep 9714023 = 14571035) B14571035
theorem B6476015 : Blo 1596997 6476015 := bstep (se 1 (by rfl) ⟨4857011, by rfl⟩ : syracuseStep 6476015 = 9714023) B9714023
theorem B4317343 : Blo 1596997 4317343 := bstep (se 1 (by rfl) ⟨3238007, by rfl⟩ : syracuseStep 4317343 = 6476015) B6476015
theorem B23025829 : Blo 1596997 23025829 := bstep (se 4 (by rfl) ⟨2158671, by rfl⟩ : syracuseStep 23025829 = 4317343) B4317343
theorem B30701105 : Blo 1596997 30701105 := bstep (se 2 (by rfl) ⟨11512914, by rfl⟩ : syracuseStep 30701105 = 23025829) B23025829
theorem B20467403 : Blo 1596997 20467403 := bstep (se 1 (by rfl) ⟨15350552, by rfl⟩ : syracuseStep 20467403 = 30701105) B30701105
theorem B13644935 : Blo 1596997 13644935 := bstep (se 1 (by rfl) ⟨10233701, by rfl⟩ : syracuseStep 13644935 = 20467403) B20467403
theorem B9096623 : Blo 1596997 9096623 := bstep (se 1 (by rfl) ⟨6822467, by rfl⟩ : syracuseStep 9096623 = 13644935) B13644935
theorem B6064415 : Blo 1596997 6064415 := bstep (se 1 (by rfl) ⟨4548311, by rfl⟩ : syracuseStep 6064415 = 9096623) B9096623
theorem B4042943 : Blo 1596997 4042943 := bstep (se 1 (by rfl) ⟨3032207, by rfl⟩ : syracuseStep 4042943 = 6064415) B6064415
theorem B2695295 : Blo 1596997 2695295 := bstep (se 1 (by rfl) ⟨2021471, by rfl⟩ : syracuseStep 2695295 = 4042943) B4042943
theorem B1796863 : Blo 1596997 1796863 := bstep (se 1 (by rfl) ⟨1347647, by rfl⟩ : syracuseStep 1796863 = 2695295) B2695295
theorem B2395817 : Blo 1596997 2395817 := bstep (se 2 (by rfl) ⟨898431, by rfl⟩ : syracuseStep 2395817 = 1796863) B1796863
theorem B1597211 : Blo 1596997 1597211 := bstep (se 1 (by rfl) ⟨1197908, by rfl⟩ : syracuseStep 1597211 = 2395817) B2395817

theorem C0 (j : ℕ) (h1 : 399249 ≤ j) (h2 : j ≤ 399748) : Blo 1596997 (4 * j + 3) := by
  interval_cases j
  · exact B1596999
  · exact B1597003
  · exact B1597007
  · exact B1597011
  · exact B1597015
  · exact B1597019
  · exact B1597023
  · exact B1597027
  · exact B1597031
  · exact B1597035
  · exact B1597039
  · exact B1597043
  · exact B1597047
  · exact B1597051
  · exact B1597055
  · exact B1597059
  · exact B1597063
  · exact B1597067
  · exact B1597071
  · exact B1597075
  · exact B1597079
  · exact B1597083
  · exact B1597087
  · exact B1597091
  · exact B1597095
  · exact B1597099
  · exact B1597103
  · exact B1597107
  · exact B1597111
  · exact B1597115
  · exact B1597119
  · exact B1597123
  · exact B1597127
  · exact B1597131
  · exact B1597135
  · exact B1597139
  · exact B1597143
  · exact B1597147
  · exact B1597151
  · exact B1597155
  · exact B1597159
  · exact B1597163
  · exact B1597167
  · exact B1597171
  · exact B1597175
  · exact B1597179
  · exact B1597183
  · exact B1597187
  · exact B1597191
  · exact B1597195
  · exact B1597199
  · exact B1597203
  · exact B1597207
  · exact B1597211
  · exact B1597215
  · exact B1597219
  · exact B1597223
  · exact B1597227
  · exact B1597231
  · exact B1597235
  · exact B1597239
  · exact B1597243
  · exact B1597247
  · exact B1597251
  · exact B1597255
  · exact B1597259
  · exact B1597263
  · exact B1597267
  · exact B1597271
  · exact B1597275
  · exact B1597279
  · exact B1597283
  · exact B1597287
  · exact B1597291
  · exact B1597295
  · exact B1597299
  · exact B1597303
  · exact B1597307
  · exact B1597311
  · exact B1597315
  · exact B1597319
  · exact B1597323
  · exact B1597327
  · exact B1597331
  · exact B1597335
  · exact B1597339
  · exact B1597343
  · exact B1597347
  · exact B1597351
  · exact B1597355
  · exact B1597359
  · exact B1597363
  · exact B1597367
  · exact B1597371
  · exact B1597375
  · exact B1597379
  · exact B1597383
  · exact B1597387
  · exact B1597391
  · exact B1597395
  · exact B1597399
  · exact B1597403
  · exact B1597407
  · exact B1597411
  · exact B1597415
  · exact B1597419
  · exact B1597423
  · exact B1597427
  · exact B1597431
  · exact B1597435
  · exact B1597439
  · exact B1597443
  · exact B1597447
  · exact B1597451
  · exact B1597455
  · exact B1597459
  · exact B1597463
  · exact B1597467
  · exact B1597471
  · exact B1597475
  · exact B1597479
  · exact B1597483
  · exact B1597487
  · exact B1597491
  · exact B1597495
  · exact B1597499
  · exact B1597503
  · exact B1597507
  · exact B1597511
  · exact B1597515
  · exact B1597519
  · exact B1597523
  · exact B1597527
  · exact B1597531
  · exact B1597535
  · exact B1597539
  · exact B1597543
  · exact B1597547
  · exact B1597551
  · exact B1597555
  · exact B1597559
  · exact B1597563
  · exact B1597567
  · exact B1597571
  · exact B1597575
  · exact B1597579
  · exact B1597583
  · exact B1597587
  · exact B1597591
  · exact B1597595
  · exact B1597599
  · exact B1597603
  · exact B1597607
  · exact B1597611
  · exact B1597615
  · exact B1597619
  · exact B1597623
  · exact B1597627
  · exact B1597631
  · exact B1597635
  · exact B1597639
  · exact B1597643
  · exact B1597647
  · exact B1597651
  · exact B1597655
  · exact B1597659
  · exact B1597663
  · exact B1597667
  · exact B1597671
  · exact B1597675
  · exact B1597679
  · exact B1597683
  · exact B1597687
  · exact B1597691
  · exact B1597695
  · exact B1597699
  · exact B1597703
  · exact B1597707
  · exact B1597711
  · exact B1597715
  · exact B1597719
  · exact B1597723
  · exact B1597727
  · exact B1597731
  · exact B1597735
  · exact B1597739
  · exact B1597743
  · exact B1597747
  · exact B1597751
  · exact B1597755
  · exact B1597759
  · exact B1597763
  · exact B1597767
  · exact B1597771
  · exact B1597775
  · exact B1597779
  · exact B1597783
  · exact B1597787
  · exact B1597791
  · exact B1597795
  · exact B1597799
  · exact B1597803
  · exact B1597807
  · exact B1597811
  · exact B1597815
  · exact B1597819
  · exact B1597823
  · exact B1597827
  · exact B1597831
  · exact B1597835
  · exact B1597839
  · exact B1597843
  · exact B1597847
  · exact B1597851
  · exact B1597855
  · exact B1597859
  · exact B1597863
  · exact B1597867
  · exact B1597871
  · exact B1597875
  · exact B1597879
  · exact B1597883
  · exact B1597887
  · exact B1597891
  · exact B1597895
  · exact B1597899
  · exact B1597903
  · exact B1597907
  · exact B1597911
  · exact B1597915
  · exact B1597919
  · exact B1597923
  · exact B1597927
  · exact B1597931
  · exact B1597935
  · exact B1597939
  · exact B1597943
  · exact B1597947
  · exact B1597951
  · exact B1597955
  · exact B1597959
  · exact B1597963
  · exact B1597967
  · exact B1597971
  · exact B1597975
  · exact B1597979
  · exact B1597983
  · exact B1597987
  · exact B1597991
  · exact B1597995
  · exact B1597999
  · exact B1598003
  · exact B1598007
  · exact B1598011
  · exact B1598015
  · exact B1598019
  · exact B1598023
  · exact B1598027
  · exact B1598031
  · exact B1598035
  · exact B1598039
  · exact B1598043
  · exact B1598047
  · exact B1598051
  · exact B1598055
  · exact B1598059
  · exact B1598063
  · exact B1598067
  · exact B1598071
  · exact B1598075
  · exact B1598079
  · exact B1598083
  · exact B1598087
  · exact B1598091
  · exact B1598095
  · exact B1598099
  · exact B1598103
  · exact B1598107
  · exact B1598111
  · exact B1598115
  · exact B1598119
  · exact B1598123
  · exact B1598127
  · exact B1598131
  · exact B1598135
  · exact B1598139
  · exact B1598143
  · exact B1598147
  · exact B1598151
  · exact B1598155
  · exact B1598159
  · exact B1598163
  · exact B1598167
  · exact B1598171
  · exact B1598175
  · exact B1598179
  · exact B1598183
  · exact B1598187
  · exact B1598191
  · exact B1598195
  · exact B1598199
  · exact B1598203
  · exact B1598207
  · exact B1598211
  · exact B1598215
  · exact B1598219
  · exact B1598223
  · exact B1598227
  · exact B1598231
  · exact B1598235
  · exact B1598239
  · exact B1598243
  · exact B1598247
  · exact B1598251
  · exact B1598255
  · exact B1598259
  · exact B1598263
  · exact B1598267
  · exact B1598271
  · exact B1598275
  · exact B1598279
  · exact B1598283
  · exact B1598287
  · exact B1598291
  · exact B1598295
  · exact B1598299
  · exact B1598303
  · exact B1598307
  · exact B1598311
  · exact B1598315
  · exact B1598319
  · exact B1598323
  · exact B1598327
  · exact B1598331
  · exact B1598335
  · exact B1598339
  · exact B1598343
  · exact B1598347
  · exact B1598351
  · exact B1598355
  · exact B1598359
  · exact B1598363
  · exact B1598367
  · exact B1598371
  · exact B1598375
  · exact B1598379
  · exact B1598383
  · exact B1598387
  · exact B1598391
  · exact B1598395
  · exact B1598399
  · exact B1598403
  · exact B1598407
  · exact B1598411
  · exact B1598415
  · exact B1598419
  · exact B1598423
  · exact B1598427
  · exact B1598431
  · exact B1598435
  · exact B1598439
  · exact B1598443
  · exact B1598447
  · exact B1598451
  · exact B1598455
  · exact B1598459
  · exact B1598463
  · exact B1598467
  · exact B1598471
  · exact B1598475
  · exact B1598479
  · exact B1598483
  · exact B1598487
  · exact B1598491
  · exact B1598495
  · exact B1598499
  · exact B1598503
  · exact B1598507
  · exact B1598511
  · exact B1598515
  · exact B1598519
  · exact B1598523
  · exact B1598527
  · exact B1598531
  · exact B1598535
  · exact B1598539
  · exact B1598543
  · exact B1598547
  · exact B1598551
  · exact B1598555
  · exact B1598559
  · exact B1598563
  · exact B1598567
  · exact B1598571
  · exact B1598575
  · exact B1598579
  · exact B1598583
  · exact B1598587
  · exact B1598591
  · exact B1598595
  · exact B1598599
  · exact B1598603
  · exact B1598607
  · exact B1598611
  · exact B1598615
  · exact B1598619
  · exact B1598623
  · exact B1598627
  · exact B1598631
  · exact B1598635
  · exact B1598639
  · exact B1598643
  · exact B1598647
  · exact B1598651
  · exact B1598655
  · exact B1598659
  · exact B1598663
  · exact B1598667
  · exact B1598671
  · exact B1598675
  · exact B1598679
  · exact B1598683
  · exact B1598687
  · exact B1598691
  · exact B1598695
  · exact B1598699
  · exact B1598703
  · exact B1598707
  · exact B1598711
  · exact B1598715
  · exact B1598719
  · exact B1598723
  · exact B1598727
  · exact B1598731
  · exact B1598735
  · exact B1598739
  · exact B1598743
  · exact B1598747
  · exact B1598751
  · exact B1598755
  · exact B1598759
  · exact B1598763
  · exact B1598767
  · exact B1598771
  · exact B1598775
  · exact B1598779
  · exact B1598783
  · exact B1598787
  · exact B1598791
  · exact B1598795
  · exact B1598799
  · exact B1598803
  · exact B1598807
  · exact B1598811
  · exact B1598815
  · exact B1598819
  · exact B1598823
  · exact B1598827
  · exact B1598831
  · exact B1598835
  · exact B1598839
  · exact B1598843
  · exact B1598847
  · exact B1598851
  · exact B1598855
  · exact B1598859
  · exact B1598863
  · exact B1598867
  · exact B1598871
  · exact B1598875
  · exact B1598879
  · exact B1598883
  · exact B1598887
  · exact B1598891
  · exact B1598895
  · exact B1598899
  · exact B1598903
  · exact B1598907
  · exact B1598911
  · exact B1598915
  · exact B1598919
  · exact B1598923
  · exact B1598927
  · exact B1598931
  · exact B1598935
  · exact B1598939
  · exact B1598943
  · exact B1598947
  · exact B1598951
  · exact B1598955
  · exact B1598959
  · exact B1598963
  · exact B1598967
  · exact B1598971
  · exact B1598975
  · exact B1598979
  · exact B1598983
  · exact B1598987
  · exact B1598991
  · exact B1598995

theorem solution (m : ℕ) (hlo : 1596997 ≤ m) (hhi : m ≤ 1598997) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 399249 ≤ j := by omega
    have hj2 : j ≤ 399748 := by omega
    have hb : Blo 1596997 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
