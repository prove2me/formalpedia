-- Prove2me | solution 1 for syracuse_descends_range_1178406_1180406
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:10:31.532987+00:00
-- url     : https://prove2.me/submissions/2e8a339a-babd-4ea6-8bf4-6dbf24b5560f

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


theorem B1769477 : Blo 1178406 1769477 := bbase (se 4 (by rfl) ⟨165888, by rfl⟩ : syracuseStep 1769477 = 331777) (by norm_num)
theorem B1990669 : Blo 1178406 1990669 := bbase (se 3 (by rfl) ⟨373250, by rfl⟩ : syracuseStep 1990669 = 746501) (by norm_num)
theorem B1327117 : Blo 1178406 1327117 := bbase (se 3 (by rfl) ⟨248834, by rfl⟩ : syracuseStep 1327117 = 497669) (by norm_num)
theorem B1769501 : Blo 1178406 1769501 := bbase (se 3 (by rfl) ⟨331781, by rfl⟩ : syracuseStep 1769501 = 663563) (by norm_num)
theorem B1327153 : Blo 1178406 1327153 := bbase (se 2 (by rfl) ⟨497682, by rfl⟩ : syracuseStep 1327153 = 995365) (by norm_num)
theorem B3981365 : Blo 1178406 3981365 := bbase (se 5 (by rfl) ⟨186626, by rfl⟩ : syracuseStep 3981365 = 373253) (by norm_num)
theorem B2654261 : Blo 1178406 2654261 := bbase (se 5 (by rfl) ⟨124418, by rfl⟩ : syracuseStep 2654261 = 248837) (by norm_num)
theorem B1769525 : Blo 1178406 1769525 := bbase (se 5 (by rfl) ⟨82946, by rfl⟩ : syracuseStep 1769525 = 165893) (by norm_num)
theorem B1769549 : Blo 1178406 1769549 := bbase (se 3 (by rfl) ⟨331790, by rfl⟩ : syracuseStep 1769549 = 663581) (by norm_num)
theorem B1327189 : Blo 1178406 1327189 := bbase (se 8 (by rfl) ⟨7776, by rfl⟩ : syracuseStep 1327189 = 15553) (by norm_num)
theorem B1990757 : Blo 1178406 1990757 := bbase (se 4 (by rfl) ⟨186633, by rfl⟩ : syracuseStep 1990757 = 373267) (by norm_num)
theorem B1769573 : Blo 1178406 1769573 := bbase (se 4 (by rfl) ⟨165897, by rfl⟩ : syracuseStep 1769573 = 331795) (by norm_num)
theorem B1327225 : Blo 1178406 1327225 := bbase (se 2 (by rfl) ⟨497709, by rfl⟩ : syracuseStep 1327225 = 995419) (by norm_num)
theorem B2654333 : Blo 1178406 2654333 := bbase (se 3 (by rfl) ⟨497687, by rfl⟩ : syracuseStep 2654333 = 995375) (by norm_num)
theorem B1769597 : Blo 1178406 1769597 := bbase (se 3 (by rfl) ⟨331799, by rfl⟩ : syracuseStep 1769597 = 663599) (by norm_num)
theorem B1769621 : Blo 1178406 1769621 := bbase (se 6 (by rfl) ⟨41475, by rfl⟩ : syracuseStep 1769621 = 82951) (by norm_num)
theorem B1327261 : Blo 1178406 1327261 := bbase (se 3 (by rfl) ⟨248861, by rfl⟩ : syracuseStep 1327261 = 497723) (by norm_num)
theorem B4087973 : Blo 1178406 4087973 := bbase (se 4 (by rfl) ⟨383247, by rfl⟩ : syracuseStep 4087973 = 766495) (by norm_num)
theorem B1769645 : Blo 1178406 1769645 := bbase (se 3 (by rfl) ⟨331808, by rfl⟩ : syracuseStep 1769645 = 663617) (by norm_num)
theorem B1327297 : Blo 1178406 1327297 := bbase (se 2 (by rfl) ⟨497736, by rfl⟩ : syracuseStep 1327297 = 995473) (by norm_num)
theorem B2654405 : Blo 1178406 2654405 := bbase (se 4 (by rfl) ⟨248850, by rfl⟩ : syracuseStep 2654405 = 497701) (by norm_num)
theorem B1769669 : Blo 1178406 1769669 := bbase (se 4 (by rfl) ⟨165906, by rfl⟩ : syracuseStep 1769669 = 331813) (by norm_num)
theorem B5382341 : Blo 1178406 5382341 := bbase (se 4 (by rfl) ⟨504594, by rfl⟩ : syracuseStep 5382341 = 1009189) (by norm_num)
theorem B1769693 : Blo 1178406 1769693 := bbase (se 3 (by rfl) ⟨331817, by rfl⟩ : syracuseStep 1769693 = 663635) (by norm_num)
theorem B1990885 : Blo 1178406 1990885 := bbase (se 4 (by rfl) ⟨186645, by rfl⟩ : syracuseStep 1990885 = 373291) (by norm_num)
theorem B1327333 : Blo 1178406 1327333 := bbase (se 4 (by rfl) ⟨124437, by rfl⟩ : syracuseStep 1327333 = 248875) (by norm_num)
theorem B1769717 : Blo 1178406 1769717 := bbase (se 5 (by rfl) ⟨82955, by rfl⟩ : syracuseStep 1769717 = 165911) (by norm_num)
theorem B1327369 : Blo 1178406 1327369 := bbase (se 2 (by rfl) ⟨497763, by rfl⟩ : syracuseStep 1327369 = 995527) (by norm_num)
theorem B2654477 : Blo 1178406 2654477 := bbase (se 3 (by rfl) ⟨497714, by rfl⟩ : syracuseStep 2654477 = 995429) (by norm_num)
theorem B1769741 : Blo 1178406 1769741 := bbase (se 3 (by rfl) ⟨331826, by rfl⟩ : syracuseStep 1769741 = 663653) (by norm_num)
theorem B8962325 : Blo 1178406 8962325 := bbase (se 6 (by rfl) ⟨210054, by rfl⟩ : syracuseStep 8962325 = 420109) (by norm_num)
theorem B1769765 : Blo 1178406 1769765 := bbase (se 4 (by rfl) ⟨165915, by rfl⟩ : syracuseStep 1769765 = 331831) (by norm_num)
theorem B1327405 : Blo 1178406 1327405 := bbase (se 3 (by rfl) ⟨248888, by rfl⟩ : syracuseStep 1327405 = 497777) (by norm_num)
theorem B1990973 : Blo 1178406 1990973 := bbase (se 3 (by rfl) ⟨373307, by rfl⟩ : syracuseStep 1990973 = 746615) (by norm_num)
theorem B1769789 : Blo 1178406 1769789 := bbase (se 3 (by rfl) ⟨331835, by rfl⟩ : syracuseStep 1769789 = 663671) (by norm_num)
theorem B1327441 : Blo 1178406 1327441 := bbase (se 2 (by rfl) ⟨497790, by rfl⟩ : syracuseStep 1327441 = 995581) (by norm_num)
theorem B2654549 : Blo 1178406 2654549 := bbase (se 10 (by rfl) ⟨3888, by rfl⟩ : syracuseStep 2654549 = 7777) (by norm_num)
theorem B1769813 : Blo 1178406 1769813 := bbase (se 10 (by rfl) ⟨2592, by rfl⟩ : syracuseStep 1769813 = 5185) (by norm_num)
theorem B1769837 : Blo 1178406 1769837 := bbase (se 3 (by rfl) ⟨331844, by rfl⟩ : syracuseStep 1769837 = 663689) (by norm_num)
theorem B1327477 : Blo 1178406 1327477 := bbase (se 5 (by rfl) ⟨62225, by rfl⟩ : syracuseStep 1327477 = 124451) (by norm_num)
theorem B1769861 : Blo 1178406 1769861 := bbase (se 4 (by rfl) ⟨165924, by rfl⟩ : syracuseStep 1769861 = 331849) (by norm_num)
theorem B1417609 : Blo 1178406 1417609 := bbase (se 2 (by rfl) ⟨531603, by rfl⟩ : syracuseStep 1417609 = 1063207) (by norm_num)
theorem B1327513 : Blo 1178406 1327513 := bbase (se 2 (by rfl) ⟨497817, by rfl⟩ : syracuseStep 1327513 = 995635) (by norm_num)
theorem B2654621 : Blo 1178406 2654621 := bbase (se 3 (by rfl) ⟨497741, by rfl⟩ : syracuseStep 2654621 = 995483) (by norm_num)
theorem B1769885 : Blo 1178406 1769885 := bbase (se 3 (by rfl) ⟨331853, by rfl⟩ : syracuseStep 1769885 = 663707) (by norm_num)
theorem B3359141 : Blo 1178406 3359141 := bbase (se 4 (by rfl) ⟨314919, by rfl⟩ : syracuseStep 3359141 = 629839) (by norm_num)
theorem B1769909 : Blo 1178406 1769909 := bbase (se 5 (by rfl) ⟨82964, by rfl⟩ : syracuseStep 1769909 = 165929) (by norm_num)
theorem B1991101 : Blo 1178406 1991101 := bbase (se 3 (by rfl) ⟨373331, by rfl⟩ : syracuseStep 1991101 = 746663) (by norm_num)
theorem B1327549 : Blo 1178406 1327549 := bbase (se 3 (by rfl) ⟨248915, by rfl⟩ : syracuseStep 1327549 = 497831) (by norm_num)
theorem B1769933 : Blo 1178406 1769933 := bbase (se 3 (by rfl) ⟨331862, by rfl⟩ : syracuseStep 1769933 = 663725) (by norm_num)
theorem B1196497 : Blo 1178406 1196497 := bbase (se 2 (by rfl) ⟨448686, by rfl⟩ : syracuseStep 1196497 = 897373) (by norm_num)
theorem B2154973 : Blo 1178406 2154973 := bbase (se 3 (by rfl) ⟨404057, by rfl⟩ : syracuseStep 2154973 = 808115) (by norm_num)
theorem B1327585 : Blo 1178406 1327585 := bbase (se 2 (by rfl) ⟨497844, by rfl⟩ : syracuseStep 1327585 = 995689) (by norm_num)
theorem B5972453 : Blo 1178406 5972453 := bbase (se 4 (by rfl) ⟨559917, by rfl⟩ : syracuseStep 5972453 = 1119835) (by norm_num)
theorem B3981797 : Blo 1178406 3981797 := bbase (se 4 (by rfl) ⟨373293, by rfl⟩ : syracuseStep 3981797 = 746587) (by norm_num)
theorem B2654693 : Blo 1178406 2654693 := bbase (se 4 (by rfl) ⟨248877, by rfl⟩ : syracuseStep 2654693 = 497755) (by norm_num)
theorem B1769957 : Blo 1178406 1769957 := bbase (se 4 (by rfl) ⟨165933, by rfl⟩ : syracuseStep 1769957 = 331867) (by norm_num)
theorem B1769981 : Blo 1178406 1769981 := bbase (se 3 (by rfl) ⟨331871, by rfl⟩ : syracuseStep 1769981 = 663743) (by norm_num)
theorem B1327621 : Blo 1178406 1327621 := bbase (se 4 (by rfl) ⟨124464, by rfl⟩ : syracuseStep 1327621 = 248929) (by norm_num)
theorem B1491473 : Blo 1178406 1491473 := bbase (se 2 (by rfl) ⟨559302, by rfl⟩ : syracuseStep 1491473 = 1118605) (by norm_num)
theorem B1991189 : Blo 1178406 1991189 := bbase (se 6 (by rfl) ⟨46668, by rfl⟩ : syracuseStep 1991189 = 93337) (by norm_num)
theorem B1770005 : Blo 1178406 1770005 := bbase (se 6 (by rfl) ⟨41484, by rfl⟩ : syracuseStep 1770005 = 82969) (by norm_num)
theorem B1417753 : Blo 1178406 1417753 := bbase (se 2 (by rfl) ⟨531657, by rfl⟩ : syracuseStep 1417753 = 1063315) (by norm_num)
theorem B1327657 : Blo 1178406 1327657 := bbase (se 2 (by rfl) ⟨497871, by rfl⟩ : syracuseStep 1327657 = 995743) (by norm_num)
theorem B2654765 : Blo 1178406 2654765 := bbase (se 3 (by rfl) ⟨497768, by rfl⟩ : syracuseStep 2654765 = 995537) (by norm_num)
theorem B1770029 : Blo 1178406 1770029 := bbase (se 3 (by rfl) ⟨331880, by rfl⟩ : syracuseStep 1770029 = 663761) (by norm_num)
theorem B1770053 : Blo 1178406 1770053 := bbase (se 4 (by rfl) ⟨165942, by rfl⟩ : syracuseStep 1770053 = 331885) (by norm_num)
theorem B1491529 : Blo 1178406 1491529 := bbase (se 2 (by rfl) ⟨559323, by rfl⟩ : syracuseStep 1491529 = 1118647) (by norm_num)
theorem B1327693 : Blo 1178406 1327693 := bbase (se 3 (by rfl) ⟨248942, by rfl⟩ : syracuseStep 1327693 = 497885) (by norm_num)
theorem B1770077 : Blo 1178406 1770077 := bbase (se 3 (by rfl) ⟨331889, by rfl⟩ : syracuseStep 1770077 = 663779) (by norm_num)
theorem B1327729 : Blo 1178406 1327729 := bbase (se 2 (by rfl) ⟨497898, by rfl⟩ : syracuseStep 1327729 = 995797) (by norm_num)
theorem B2654837 : Blo 1178406 2654837 := bbase (se 5 (by rfl) ⟨124445, by rfl⟩ : syracuseStep 2654837 = 248891) (by norm_num)
theorem B1770101 : Blo 1178406 1770101 := bbase (se 5 (by rfl) ⟨82973, by rfl⟩ : syracuseStep 1770101 = 165947) (by norm_num)
theorem B1770125 : Blo 1178406 1770125 := bbase (se 3 (by rfl) ⟨331898, by rfl⟩ : syracuseStep 1770125 = 663797) (by norm_num)
theorem B1991317 : Blo 1178406 1991317 := bbase (se 6 (by rfl) ⟨46671, by rfl⟩ : syracuseStep 1991317 = 93343) (by norm_num)
theorem B1327765 : Blo 1178406 1327765 := bbase (se 6 (by rfl) ⟨31119, by rfl⟩ : syracuseStep 1327765 = 62239) (by norm_num)
theorem B9085589 : Blo 1178406 9085589 := bbase (se 6 (by rfl) ⟨212943, by rfl⟩ : syracuseStep 9085589 = 425887) (by norm_num)
theorem B1770149 : Blo 1178406 1770149 := bbase (se 4 (by rfl) ⟨165951, by rfl⟩ : syracuseStep 1770149 = 331903) (by norm_num)
theorem B1491625 : Blo 1178406 1491625 := bbase (se 2 (by rfl) ⟨559359, by rfl⟩ : syracuseStep 1491625 = 1118719) (by norm_num)
theorem B8954549 : Blo 1178406 8954549 := bbase (se 5 (by rfl) ⟨419744, by rfl⟩ : syracuseStep 8954549 = 839489) (by norm_num)
theorem B1327801 : Blo 1178406 1327801 := bbase (se 2 (by rfl) ⟨497925, by rfl⟩ : syracuseStep 1327801 = 995851) (by norm_num)
theorem B2654909 : Blo 1178406 2654909 := bbase (se 3 (by rfl) ⟨497795, by rfl⟩ : syracuseStep 2654909 = 995591) (by norm_num)
theorem B1770173 : Blo 1178406 1770173 := bbase (se 3 (by rfl) ⟨331907, by rfl⟩ : syracuseStep 1770173 = 663815) (by norm_num)
theorem B1770197 : Blo 1178406 1770197 := bbase (se 7 (by rfl) ⟨20744, by rfl⟩ : syracuseStep 1770197 = 41489) (by norm_num)
theorem B2237149 : Blo 1178406 2237149 := bbase (se 3 (by rfl) ⟨419465, by rfl⟩ : syracuseStep 2237149 = 838931) (by norm_num)
theorem B1327837 : Blo 1178406 1327837 := bbase (se 3 (by rfl) ⟨248969, by rfl⟩ : syracuseStep 1327837 = 497939) (by norm_num)
theorem B1991405 : Blo 1178406 1991405 := bbase (se 3 (by rfl) ⟨373388, by rfl⟩ : syracuseStep 1991405 = 746777) (by norm_num)
theorem B1770221 : Blo 1178406 1770221 := bbase (se 3 (by rfl) ⟨331916, by rfl⟩ : syracuseStep 1770221 = 663833) (by norm_num)
theorem B3023605 : Blo 1178406 3023605 := bbase (se 5 (by rfl) ⟨141731, by rfl⟩ : syracuseStep 3023605 = 283463) (by norm_num)
theorem B1327873 : Blo 1178406 1327873 := bbase (se 2 (by rfl) ⟨497952, by rfl⟩ : syracuseStep 1327873 = 995905) (by norm_num)
theorem B2654981 : Blo 1178406 2654981 := bbase (se 4 (by rfl) ⟨248904, by rfl⟩ : syracuseStep 2654981 = 497809) (by norm_num)
theorem B1770245 : Blo 1178406 1770245 := bbase (se 4 (by rfl) ⟨165960, by rfl⟩ : syracuseStep 1770245 = 331921) (by norm_num)
theorem B15319829 : Blo 1178406 15319829 := bbase (se 6 (by rfl) ⟨359058, by rfl⟩ : syracuseStep 15319829 = 718117) (by norm_num)
theorem B1770269 : Blo 1178406 1770269 := bbase (se 3 (by rfl) ⟨331925, by rfl⟩ : syracuseStep 1770269 = 663851) (by norm_num)
theorem B1327909 : Blo 1178406 1327909 := bbase (se 4 (by rfl) ⟨124491, by rfl⟩ : syracuseStep 1327909 = 248983) (by norm_num)
theorem B1770293 : Blo 1178406 1770293 := bbase (se 5 (by rfl) ⟨82982, by rfl⟩ : syracuseStep 1770293 = 165965) (by norm_num)
theorem B1327945 : Blo 1178406 1327945 := bbase (se 2 (by rfl) ⟨497979, by rfl⟩ : syracuseStep 1327945 = 995959) (by norm_num)
theorem B2655053 : Blo 1178406 2655053 := bbase (se 3 (by rfl) ⟨497822, by rfl⟩ : syracuseStep 2655053 = 995645) (by norm_num)
theorem B1770317 : Blo 1178406 1770317 := bbase (se 3 (by rfl) ⟨331934, by rfl⟩ : syracuseStep 1770317 = 663869) (by norm_num)
theorem B1491797 : Blo 1178406 1491797 := bbase (se 9 (by rfl) ⟨4370, by rfl⟩ : syracuseStep 1491797 = 8741) (by norm_num)
theorem B1770341 : Blo 1178406 1770341 := bbase (se 4 (by rfl) ⟨165969, by rfl⟩ : syracuseStep 1770341 = 331939) (by norm_num)
theorem B1991533 : Blo 1178406 1991533 := bbase (se 3 (by rfl) ⟨373412, by rfl⟩ : syracuseStep 1991533 = 746825) (by norm_num)
theorem B1770365 : Blo 1178406 1770365 := bbase (se 3 (by rfl) ⟨331943, by rfl⟩ : syracuseStep 1770365 = 663887) (by norm_num)
theorem B1491853 : Blo 1178406 1491853 := bbase (se 3 (by rfl) ⟨279722, by rfl⟩ : syracuseStep 1491853 = 559445) (by norm_num)
theorem B3982229 : Blo 1178406 3982229 := bbase (se 6 (by rfl) ⟨93333, by rfl⟩ : syracuseStep 3982229 = 186667) (by norm_num)
theorem B2655125 : Blo 1178406 2655125 := bbase (se 6 (by rfl) ⟨62229, by rfl⟩ : syracuseStep 2655125 = 124459) (by norm_num)
theorem B1680277 : Blo 1178406 1680277 := bbase (se 6 (by rfl) ⟨39381, by rfl⟩ : syracuseStep 1680277 = 78763) (by norm_num)
theorem B1770389 : Blo 1178406 1770389 := bbase (se 6 (by rfl) ⟨41493, by rfl⟩ : syracuseStep 1770389 = 82987) (by norm_num)
theorem B3777445 : Blo 1178406 3777445 := bbase (se 4 (by rfl) ⟨354135, by rfl⟩ : syracuseStep 3777445 = 708271) (by norm_num)
theorem B1532845 : Blo 1178406 1532845 := bbase (se 3 (by rfl) ⟨287408, by rfl⟩ : syracuseStep 1532845 = 574817) (by norm_num)
theorem B1770413 : Blo 1178406 1770413 := bbase (se 3 (by rfl) ⟨331952, by rfl⟩ : syracuseStep 1770413 = 663905) (by norm_num)
theorem B2982845 : Blo 1178406 2982845 := bbase (se 3 (by rfl) ⟨559283, by rfl⟩ : syracuseStep 2982845 = 1118567) (by norm_num)
theorem B1991621 : Blo 1178406 1991621 := bbase (se 4 (by rfl) ⟨186714, by rfl⟩ : syracuseStep 1991621 = 373429) (by norm_num)
theorem B1770437 : Blo 1178406 1770437 := bbase (se 4 (by rfl) ⟨165978, by rfl⟩ : syracuseStep 1770437 = 331957) (by norm_num)
theorem B2655197 : Blo 1178406 2655197 := bbase (se 3 (by rfl) ⟨497849, by rfl⟩ : syracuseStep 2655197 = 995699) (by norm_num)
theorem B1770461 : Blo 1178406 1770461 := bbase (se 3 (by rfl) ⟨331961, by rfl⟩ : syracuseStep 1770461 = 663923) (by norm_num)
theorem B1344481 : Blo 1178406 1344481 := bbase (se 2 (by rfl) ⟨504180, by rfl⟩ : syracuseStep 1344481 = 1008361) (by norm_num)
theorem B1491949 : Blo 1178406 1491949 := bbase (se 3 (by rfl) ⟨279740, by rfl⟩ : syracuseStep 1491949 = 559481) (by norm_num)
theorem B1770485 : Blo 1178406 1770485 := bbase (se 5 (by rfl) ⟨82991, by rfl⟩ : syracuseStep 1770485 = 165983) (by norm_num)
theorem B2237453 : Blo 1178406 2237453 := bbase (se 3 (by rfl) ⟨419522, by rfl⟩ : syracuseStep 2237453 = 839045) (by norm_num)
theorem B1770509 : Blo 1178406 1770509 := bbase (se 3 (by rfl) ⟨331970, by rfl⟩ : syracuseStep 1770509 = 663941) (by norm_num)
theorem B2655269 : Blo 1178406 2655269 := bbase (se 4 (by rfl) ⟨248931, by rfl⟩ : syracuseStep 2655269 = 497863) (by norm_num)
theorem B1770533 : Blo 1178406 1770533 := bbase (se 4 (by rfl) ⟨165987, by rfl⟩ : syracuseStep 1770533 = 331975) (by norm_num)
theorem B1770557 : Blo 1178406 1770557 := bbase (se 3 (by rfl) ⟨331979, by rfl⟩ : syracuseStep 1770557 = 663959) (by norm_num)
theorem B1991749 : Blo 1178406 1991749 := bbase (se 4 (by rfl) ⟨186726, by rfl⟩ : syracuseStep 1991749 = 373453) (by norm_num)
theorem B1770581 : Blo 1178406 1770581 := bbase (se 8 (by rfl) ⟨10374, by rfl⟩ : syracuseStep 1770581 = 20749) (by norm_num)
theorem B2655341 : Blo 1178406 2655341 := bbase (se 3 (by rfl) ⟨497876, by rfl⟩ : syracuseStep 2655341 = 995753) (by norm_num)
theorem B1770605 : Blo 1178406 1770605 := bbase (se 3 (by rfl) ⟨331988, by rfl⟩ : syracuseStep 1770605 = 663977) (by norm_num)
theorem B3359893 : Blo 1178406 3359893 := bbase (se 6 (by rfl) ⟨78747, by rfl⟩ : syracuseStep 3359893 = 157495) (by norm_num)
theorem B1492121 : Blo 1178406 1492121 := bbase (se 2 (by rfl) ⟨559545, by rfl⟩ : syracuseStep 1492121 = 1119091) (by norm_num)
theorem B1991837 : Blo 1178406 1991837 := bbase (se 3 (by rfl) ⟨373469, by rfl⟩ : syracuseStep 1991837 = 746939) (by norm_num)
theorem B2655413 : Blo 1178406 2655413 := bbase (se 5 (by rfl) ⟨124472, by rfl⟩ : syracuseStep 2655413 = 248945) (by norm_num)
theorem B1492177 : Blo 1178406 1492177 := bbase (se 2 (by rfl) ⟨559566, by rfl⟩ : syracuseStep 1492177 = 1119133) (by norm_num)
theorem B2655485 : Blo 1178406 2655485 := bbase (se 3 (by rfl) ⟨497903, by rfl⟩ : syracuseStep 2655485 = 995807) (by norm_num)
theorem B2983189 : Blo 1178406 2983189 := bbase (se 6 (by rfl) ⟨69918, by rfl⟩ : syracuseStep 2983189 = 139837) (by norm_num)
theorem B1492273 : Blo 1178406 1492273 := bbase (se 2 (by rfl) ⟨559602, by rfl⟩ : syracuseStep 1492273 = 1119205) (by norm_num)
theorem B3982661 : Blo 1178406 3982661 := bbase (se 4 (by rfl) ⟨373374, by rfl⟩ : syracuseStep 3982661 = 746749) (by norm_num)
theorem B2655557 : Blo 1178406 2655557 := bbase (se 4 (by rfl) ⟨248958, by rfl⟩ : syracuseStep 2655557 = 497917) (by norm_num)
theorem B2835805 : Blo 1178406 2835805 := bbase (se 3 (by rfl) ⟨531713, by rfl⟩ : syracuseStep 2835805 = 1063427) (by norm_num)
theorem B2983301 : Blo 1178406 2983301 := bbase (se 4 (by rfl) ⟨279684, by rfl⟩ : syracuseStep 2983301 = 559369) (by norm_num)
theorem B2655629 : Blo 1178406 2655629 := bbase (se 3 (by rfl) ⟨497930, by rfl⟩ : syracuseStep 2655629 = 995861) (by norm_num)
theorem B11331029 : Blo 1178406 11331029 := bbase (se 7 (by rfl) ⟨132785, by rfl⟩ : syracuseStep 11331029 = 265571) (by norm_num)
theorem B2655701 : Blo 1178406 2655701 := bbase (se 7 (by rfl) ⟨31121, by rfl⟩ : syracuseStep 2655701 = 62243) (by norm_num)
theorem B1492445 : Blo 1178406 1492445 := bbase (se 3 (by rfl) ⟨279833, by rfl⟩ : syracuseStep 1492445 = 559667) (by norm_num)
theorem B3065357 : Blo 1178406 3065357 := bbase (se 3 (by rfl) ⟨574754, by rfl⟩ : syracuseStep 3065357 = 1149509) (by norm_num)
theorem B1492501 : Blo 1178406 1492501 := bbase (se 6 (by rfl) ⟨34980, by rfl⟩ : syracuseStep 1492501 = 69961) (by norm_num)
theorem B2655773 : Blo 1178406 2655773 := bbase (se 3 (by rfl) ⟨497957, by rfl⟩ : syracuseStep 2655773 = 995915) (by norm_num)
theorem B2983493 : Blo 1178406 2983493 := bbase (se 4 (by rfl) ⟨279702, by rfl⟩ : syracuseStep 2983493 = 559405) (by norm_num)
theorem B8619605 : Blo 1178406 8619605 := bbase (se 8 (by rfl) ⟨50505, by rfl⟩ : syracuseStep 8619605 = 101011) (by norm_num)
theorem B2655845 : Blo 1178406 2655845 := bbase (se 4 (by rfl) ⟨248985, by rfl⟩ : syracuseStep 2655845 = 497971) (by norm_num)
theorem B1492597 : Blo 1178406 1492597 := bbase (se 5 (by rfl) ⟨69965, by rfl⟩ : syracuseStep 1492597 = 139931) (by norm_num)
theorem B5973749 : Blo 1178406 5973749 := bbase (se 5 (by rfl) ⟨280019, by rfl⟩ : syracuseStep 5973749 = 560039) (by norm_num)
theorem B3983093 : Blo 1178406 3983093 := bbase (se 5 (by rfl) ⟨186707, by rfl⟩ : syracuseStep 3983093 = 373415) (by norm_num)
theorem B2238205 : Blo 1178406 2238205 := bbase (se 3 (by rfl) ⟨419663, by rfl⟩ : syracuseStep 2238205 = 839327) (by norm_num)
theorem B1492769 : Blo 1178406 1492769 := bbase (se 2 (by rfl) ⟨559788, by rfl⟩ : syracuseStep 1492769 = 1119577) (by norm_num)
theorem B4474709 : Blo 1178406 4474709 := bbase (se 9 (by rfl) ⟨13109, by rfl⟩ : syracuseStep 4474709 = 26219) (by norm_num)
theorem B1492825 : Blo 1178406 1492825 := bbase (se 2 (by rfl) ⟨559809, by rfl⟩ : syracuseStep 1492825 = 1119619) (by norm_num)
theorem B2516845 : Blo 1178406 2516845 := bbase (se 3 (by rfl) ⟨471908, by rfl⟩ : syracuseStep 2516845 = 943817) (by norm_num)
theorem B1345393 : Blo 1178406 1345393 := bbase (se 2 (by rfl) ⟨504522, by rfl⟩ : syracuseStep 1345393 = 1009045) (by norm_num)
theorem B4843397 : Blo 1178406 4843397 := bbase (se 4 (by rfl) ⟨454068, by rfl⟩ : syracuseStep 4843397 = 908137) (by norm_num)
theorem B2238349 : Blo 1178406 2238349 := bbase (se 3 (by rfl) ⟨419690, by rfl⟩ : syracuseStep 2238349 = 839381) (by norm_num)
theorem B2983837 : Blo 1178406 2983837 := bbase (se 3 (by rfl) ⟨559469, by rfl⟩ : syracuseStep 2983837 = 1118939) (by norm_num)
theorem B1492921 : Blo 1178406 1492921 := bbase (se 2 (by rfl) ⟨559845, by rfl⟩ : syracuseStep 1492921 = 1119691) (by norm_num)
theorem B4032485 : Blo 1178406 4032485 := bbase (se 4 (by rfl) ⟨378045, by rfl⟩ : syracuseStep 4032485 = 756091) (by norm_num)
theorem B2983949 : Blo 1178406 2983949 := bbase (se 3 (by rfl) ⟨559490, by rfl⟩ : syracuseStep 2983949 = 1118981) (by norm_num)
theorem B12757013 : Blo 1178406 12757013 := bbase (se 6 (by rfl) ⟨298992, by rfl⟩ : syracuseStep 12757013 = 597985) (by norm_num)
theorem B2238509 : Blo 1178406 2238509 := bbase (se 3 (by rfl) ⟨419720, by rfl⟩ : syracuseStep 2238509 = 839441) (by norm_num)
theorem B3778613 : Blo 1178406 3778613 := bbase (se 5 (by rfl) ⟨177122, by rfl⟩ : syracuseStep 3778613 = 354245) (by norm_num)
theorem B1534009 : Blo 1178406 1534009 := bbase (se 2 (by rfl) ⟨575253, by rfl⟩ : syracuseStep 1534009 = 1150507) (by norm_num)
theorem B3188821 : Blo 1178406 3188821 := bbase (se 8 (by rfl) ⟨18684, by rfl⟩ : syracuseStep 3188821 = 37369) (by norm_num)
theorem B1493093 : Blo 1178406 1493093 := bbase (se 4 (by rfl) ⟨139977, by rfl⟩ : syracuseStep 1493093 = 279955) (by norm_num)
theorem B4474997 : Blo 1178406 4474997 := bbase (se 5 (by rfl) ⟨209765, by rfl⟩ : syracuseStep 4474997 = 419531) (by norm_num)
theorem B1534073 : Blo 1178406 1534073 := bbase (se 2 (by rfl) ⟨575277, by rfl⟩ : syracuseStep 1534073 = 1150555) (by norm_num)
theorem B5965973 : Blo 1178406 5965973 := bbase (se 6 (by rfl) ⟨139827, by rfl⟩ : syracuseStep 5965973 = 279655) (by norm_num)
theorem B1493149 : Blo 1178406 1493149 := bbase (se 3 (by rfl) ⟨279965, by rfl⟩ : syracuseStep 1493149 = 559931) (by norm_num)
theorem B3983525 : Blo 1178406 3983525 := bbase (se 4 (by rfl) ⟨373455, by rfl⟩ : syracuseStep 3983525 = 746911) (by norm_num)
theorem B2238653 : Blo 1178406 2238653 := bbase (se 3 (by rfl) ⟨419747, by rfl⟩ : syracuseStep 2238653 = 839495) (by norm_num)
theorem B2984141 : Blo 1178406 2984141 := bbase (se 3 (by rfl) ⟨559526, by rfl⟩ : syracuseStep 2984141 = 1119053) (by norm_num)
theorem B2689253 : Blo 1178406 2689253 := bbase (se 4 (by rfl) ⟨252117, by rfl⟩ : syracuseStep 2689253 = 504235) (by norm_num)
theorem B1493245 : Blo 1178406 1493245 := bbase (se 3 (by rfl) ⟨279983, by rfl⟩ : syracuseStep 1493245 = 559967) (by norm_num)
theorem B8063381 : Blo 1178406 8063381 := bbase (se 6 (by rfl) ⟨188985, by rfl⟩ : syracuseStep 8063381 = 377971) (by norm_num)
theorem B1493417 : Blo 1178406 1493417 := bbase (se 2 (by rfl) ⟨560031, by rfl⟩ : syracuseStep 1493417 = 1120063) (by norm_num)
theorem B2238941 : Blo 1178406 2238941 := bbase (se 3 (by rfl) ⟨419801, by rfl⟩ : syracuseStep 2238941 = 839603) (by norm_num)
theorem B1493473 : Blo 1178406 1493473 := bbase (se 2 (by rfl) ⟨560052, by rfl⟩ : syracuseStep 1493473 = 1120105) (by norm_num)
theorem B5671397 : Blo 1178406 5671397 := bbase (se 4 (by rfl) ⟨531693, by rfl⟩ : syracuseStep 5671397 = 1063387) (by norm_num)
theorem B2984485 : Blo 1178406 2984485 := bbase (se 4 (by rfl) ⟨279795, by rfl⟩ : syracuseStep 2984485 = 559591) (by norm_num)
theorem B1493569 : Blo 1178406 1493569 := bbase (se 2 (by rfl) ⟨560088, by rfl⟩ : syracuseStep 1493569 = 1120177) (by norm_num)
theorem B3025493 : Blo 1178406 3025493 := bbase (se 8 (by rfl) ⟨17727, by rfl⟩ : syracuseStep 3025493 = 35455) (by norm_num)
theorem B2239093 : Blo 1178406 2239093 := bbase (se 5 (by rfl) ⟨104957, by rfl⟩ : syracuseStep 2239093 = 209915) (by norm_num)
theorem B2984597 : Blo 1178406 2984597 := bbase (se 6 (by rfl) ⟨69951, by rfl⟩ : syracuseStep 2984597 = 139903) (by norm_num)
theorem B6810293 : Blo 1178406 6810293 := bbase (se 5 (by rfl) ⟨319232, by rfl⟩ : syracuseStep 6810293 = 638465) (by norm_num)
theorem B2517733 : Blo 1178406 2517733 := bbase (se 4 (by rfl) ⟨236037, by rfl⟩ : syracuseStep 2517733 = 472075) (by norm_num)
theorem B1493741 : Blo 1178406 1493741 := bbase (se 3 (by rfl) ⟨280076, by rfl⟩ : syracuseStep 1493741 = 560153) (by norm_num)
theorem B6712085 : Blo 1178406 6712085 := bbase (se 6 (by rfl) ⟨157314, by rfl⟩ : syracuseStep 6712085 = 314629) (by norm_num)
theorem B1493797 : Blo 1178406 1493797 := bbase (se 4 (by rfl) ⟨140043, by rfl⟩ : syracuseStep 1493797 = 280087) (by norm_num)
theorem B2984789 : Blo 1178406 2984789 := bbase (se 9 (by rfl) ⟨8744, by rfl⟩ : syracuseStep 2984789 = 17489) (by norm_num)
theorem B5376901 : Blo 1178406 5376901 := bbase (se 4 (by rfl) ⟨504084, by rfl⟩ : syracuseStep 5376901 = 1008169) (by norm_num)
theorem B1493893 : Blo 1178406 1493893 := bbase (se 4 (by rfl) ⟨140052, by rfl⟩ : syracuseStep 1493893 = 280105) (by norm_num)
theorem B2239397 : Blo 1178406 2239397 := bbase (se 4 (by rfl) ⟨209943, by rfl⟩ : syracuseStep 2239397 = 419887) (by norm_num)
theorem B5975045 : Blo 1178406 5975045 := bbase (se 4 (by rfl) ⟨560160, by rfl⟩ : syracuseStep 5975045 = 1120321) (by norm_num)
theorem B2124893 : Blo 1178406 2124893 := bbase (se 3 (by rfl) ⟨398417, by rfl⟩ : syracuseStep 2124893 = 796835) (by norm_num)
theorem B2985133 : Blo 1178406 2985133 := bbase (se 3 (by rfl) ⟨559712, by rfl⟩ : syracuseStep 2985133 = 1119425) (by norm_num)
theorem B2518229 : Blo 1178406 2518229 := bbase (se 7 (by rfl) ⟨29510, by rfl⟩ : syracuseStep 2518229 = 59021) (by norm_num)
theorem B1363213 : Blo 1178406 1363213 := bbase (se 3 (by rfl) ⟨255602, by rfl⟩ : syracuseStep 1363213 = 511205) (by norm_num)
theorem B4476181 : Blo 1178406 4476181 := bbase (se 6 (by rfl) ⟨104910, by rfl⟩ : syracuseStep 4476181 = 209821) (by norm_num)
theorem B2985245 : Blo 1178406 2985245 := bbase (se 3 (by rfl) ⟨559733, by rfl⟩ : syracuseStep 2985245 = 1119467) (by norm_num)
theorem B5967269 : Blo 1178406 5967269 := bbase (se 4 (by rfl) ⟨559431, by rfl⟩ : syracuseStep 5967269 = 1118863) (by norm_num)
theorem B2985437 : Blo 1178406 2985437 := bbase (se 3 (by rfl) ⟨559769, by rfl⟩ : syracuseStep 2985437 = 1119539) (by norm_num)
theorem B4476485 : Blo 1178406 4476485 := bbase (se 4 (by rfl) ⟨419670, by rfl⟩ : syracuseStep 4476485 = 839341) (by norm_num)
theorem B1887877 : Blo 1178406 1887877 := bbase (se 4 (by rfl) ⟨176988, by rfl⟩ : syracuseStep 1887877 = 353977) (by norm_num)
theorem B2240149 : Blo 1178406 2240149 := bbase (se 6 (by rfl) ⟨52503, by rfl⟩ : syracuseStep 2240149 = 105007) (by norm_num)
theorem B5041925 : Blo 1178406 5041925 := bbase (se 4 (by rfl) ⟨472680, by rfl⟩ : syracuseStep 5041925 = 945361) (by norm_num)
theorem B2240293 : Blo 1178406 2240293 := bbase (se 4 (by rfl) ⟨210027, by rfl⟩ : syracuseStep 2240293 = 420055) (by norm_num)
theorem B2985781 : Blo 1178406 2985781 := bbase (se 5 (by rfl) ⟨139958, by rfl⟩ : syracuseStep 2985781 = 279917) (by norm_num)
theorem B3780469 : Blo 1178406 3780469 := bbase (se 5 (by rfl) ⟨177209, by rfl⟩ : syracuseStep 3780469 = 354419) (by norm_num)
theorem B2985893 : Blo 1178406 2985893 := bbase (se 4 (by rfl) ⟨279927, by rfl⟩ : syracuseStep 2985893 = 559855) (by norm_num)
theorem B2240453 : Blo 1178406 2240453 := bbase (se 4 (by rfl) ⟨210042, by rfl⟩ : syracuseStep 2240453 = 420085) (by norm_num)
theorem B6131717 : Blo 1178406 6131717 := bbase (se 4 (by rfl) ⟨574848, by rfl⟩ : syracuseStep 6131717 = 1149697) (by norm_num)
theorem B5378069 : Blo 1178406 5378069 := bbase (se 6 (by rfl) ⟨126048, by rfl⟩ : syracuseStep 5378069 = 252097) (by norm_num)
theorem B2519117 : Blo 1178406 2519117 := bbase (se 3 (by rfl) ⟨472334, by rfl⟩ : syracuseStep 2519117 = 944669) (by norm_num)
theorem B2240597 : Blo 1178406 2240597 := bbase (se 8 (by rfl) ⟨13128, by rfl⟩ : syracuseStep 2240597 = 26257) (by norm_num)
theorem B2986085 : Blo 1178406 2986085 := bbase (se 4 (by rfl) ⟨279945, by rfl⟩ : syracuseStep 2986085 = 559891) (by norm_num)
theorem B2519237 : Blo 1178406 2519237 := bbase (se 4 (by rfl) ⟨236178, by rfl⟩ : syracuseStep 2519237 = 472357) (by norm_num)
theorem B3584213 : Blo 1178406 3584213 := bbase (se 7 (by rfl) ⟨42002, by rfl⟩ : syracuseStep 3584213 = 84005) (by norm_num)
theorem B14356693 : Blo 1178406 14356693 := bbase (se 7 (by rfl) ⟨168242, by rfl⟩ : syracuseStep 14356693 = 336485) (by norm_num)
theorem B1593589 : Blo 1178406 1593589 := bbase (se 5 (by rfl) ⟨74699, by rfl⟩ : syracuseStep 1593589 = 149399) (by norm_num)
theorem B3977477 : Blo 1178406 3977477 := bbase (se 4 (by rfl) ⟨372888, by rfl⟩ : syracuseStep 3977477 = 745777) (by norm_num)
theorem B1888589 : Blo 1178406 1888589 := bbase (se 3 (by rfl) ⟨354110, by rfl⟩ : syracuseStep 1888589 = 708221) (by norm_num)
theorem B2126197 : Blo 1178406 2126197 := bbase (se 5 (by rfl) ⟨99665, by rfl⟩ : syracuseStep 2126197 = 199331) (by norm_num)
theorem B2240885 : Blo 1178406 2240885 := bbase (se 5 (by rfl) ⟨105041, by rfl⟩ : syracuseStep 2240885 = 210083) (by norm_num)
theorem B6721973 : Blo 1178406 6721973 := bbase (se 5 (by rfl) ⟨315092, by rfl⟩ : syracuseStep 6721973 = 630185) (by norm_num)
theorem B2986429 : Blo 1178406 2986429 := bbase (se 3 (by rfl) ⟨559955, by rfl⟩ : syracuseStep 2986429 = 1119911) (by norm_num)
theorem B2126341 : Blo 1178406 2126341 := bbase (se 4 (by rfl) ⟨199344, by rfl⟩ : syracuseStep 2126341 = 398689) (by norm_num)
theorem B2691589 : Blo 1178406 2691589 := bbase (se 4 (by rfl) ⟨252336, by rfl⟩ : syracuseStep 2691589 = 504673) (by norm_num)
theorem B2986541 : Blo 1178406 2986541 := bbase (se 3 (by rfl) ⟨559976, by rfl⟩ : syracuseStep 2986541 = 1119953) (by norm_num)
theorem B3977909 : Blo 1178406 3977909 := bbase (se 5 (by rfl) ⟨186464, by rfl⟩ : syracuseStep 3977909 = 372929) (by norm_num)
theorem B5968565 : Blo 1178406 5968565 := bbase (se 5 (by rfl) ⟨279776, by rfl⟩ : syracuseStep 5968565 = 559553) (by norm_num)
theorem B2986733 : Blo 1178406 2986733 := bbase (se 3 (by rfl) ⟨560012, by rfl⟩ : syracuseStep 2986733 = 1120025) (by norm_num)
theorem B2126645 : Blo 1178406 2126645 := bbase (se 5 (by rfl) ⟨99686, by rfl⟩ : syracuseStep 2126645 = 199373) (by norm_num)
theorem B2519869 : Blo 1178406 2519869 := bbase (se 3 (by rfl) ⟨472475, by rfl⟩ : syracuseStep 2519869 = 944951) (by norm_num)
theorem B1512265 : Blo 1178406 1512265 := bbase (se 2 (by rfl) ⟨567099, by rfl⟩ : syracuseStep 1512265 = 1134199) (by norm_num)
theorem B3232613 : Blo 1178406 3232613 := bbase (se 4 (by rfl) ⟨303057, by rfl⟩ : syracuseStep 3232613 = 606115) (by norm_num)
theorem B5034869 : Blo 1178406 5034869 := bbase (se 5 (by rfl) ⟨236009, by rfl⟩ : syracuseStep 5034869 = 472019) (by norm_num)
theorem B1594237 : Blo 1178406 1594237 := bbase (se 3 (by rfl) ⟨298919, by rfl⟩ : syracuseStep 1594237 = 597839) (by norm_num)
theorem B1512413 : Blo 1178406 1512413 := bbase (se 3 (by rfl) ⟨283577, by rfl⟩ : syracuseStep 1512413 = 567155) (by norm_num)
theorem B1258465 : Blo 1178406 1258465 := bbase (se 2 (by rfl) ⟨471924, by rfl⟩ : syracuseStep 1258465 = 943849) (by norm_num)
theorem B1889261 : Blo 1178406 1889261 := bbase (se 3 (by rfl) ⟨354236, by rfl⟩ : syracuseStep 1889261 = 708473) (by norm_num)
theorem B1258525 : Blo 1178406 1258525 := bbase (se 3 (by rfl) ⟨235973, by rfl⟩ : syracuseStep 1258525 = 471947) (by norm_num)
theorem B2987077 : Blo 1178406 2987077 := bbase (se 4 (by rfl) ⟨280038, by rfl⟩ : syracuseStep 2987077 = 560077) (by norm_num)
theorem B3978341 : Blo 1178406 3978341 := bbase (se 4 (by rfl) ⟨372969, by rfl⟩ : syracuseStep 3978341 = 745939) (by norm_num)
theorem B2987189 : Blo 1178406 2987189 := bbase (se 5 (by rfl) ⟨140024, by rfl⟩ : syracuseStep 2987189 = 280049) (by norm_num)
theorem B2651453 : Blo 1178406 2651453 := bbase (se 3 (by rfl) ⟨497147, by rfl⟩ : syracuseStep 2651453 = 994295) (by norm_num)
theorem B1258841 : Blo 1178406 1258841 := bbase (se 2 (by rfl) ⟨472065, by rfl⟩ : syracuseStep 1258841 = 944131) (by norm_num)
theorem B2987381 : Blo 1178406 2987381 := bbase (se 5 (by rfl) ⟨140033, by rfl⟩ : syracuseStep 2987381 = 280067) (by norm_num)
theorem B2651525 : Blo 1178406 2651525 := bbase (se 4 (by rfl) ⟨248580, by rfl⟩ : syracuseStep 2651525 = 497161) (by norm_num)
theorem B13620629 : Blo 1178406 13620629 := bbase (se 6 (by rfl) ⟨319233, by rfl⟩ : syracuseStep 13620629 = 638467) (by norm_num)
theorem B1512869 : Blo 1178406 1512869 := bbase (se 4 (by rfl) ⟨141831, by rfl⟩ : syracuseStep 1512869 = 283663) (by norm_num)
theorem B2651597 : Blo 1178406 2651597 := bbase (se 3 (by rfl) ⟨497174, by rfl⟩ : syracuseStep 2651597 = 994349) (by norm_num)
theorem B10221013 : Blo 1178406 10221013 := bbase (se 7 (by rfl) ⟨119777, by rfl⟩ : syracuseStep 10221013 = 239555) (by norm_num)
theorem B1889773 : Blo 1178406 1889773 := bbase (se 3 (by rfl) ⟨354332, by rfl⟩ : syracuseStep 1889773 = 708665) (by norm_num)
theorem B2831885 : Blo 1178406 2831885 := bbase (se 3 (by rfl) ⟨530978, by rfl⟩ : syracuseStep 2831885 = 1061957) (by norm_num)
theorem B2651669 : Blo 1178406 2651669 := bbase (se 6 (by rfl) ⟨62148, by rfl⟩ : syracuseStep 2651669 = 124297) (by norm_num)
theorem B3978773 : Blo 1178406 3978773 := bbase (se 6 (by rfl) ⟨93252, by rfl⟩ : syracuseStep 3978773 = 186505) (by norm_num)
theorem B1513033 : Blo 1178406 1513033 := bbase (se 2 (by rfl) ⟨567387, by rfl⟩ : syracuseStep 1513033 = 1134775) (by norm_num)
theorem B2651741 : Blo 1178406 2651741 := bbase (se 3 (by rfl) ⟨497201, by rfl⟩ : syracuseStep 2651741 = 994403) (by norm_num)
theorem B2389637 : Blo 1178406 2389637 := bbase (se 4 (by rfl) ⟨224028, by rfl⟩ : syracuseStep 2389637 = 448057) (by norm_num)
theorem B4478597 : Blo 1178406 4478597 := bbase (se 4 (by rfl) ⟨419868, by rfl⟩ : syracuseStep 4478597 = 839737) (by norm_num)
theorem B2651813 : Blo 1178406 2651813 := bbase (se 4 (by rfl) ⟨248607, by rfl⟩ : syracuseStep 2651813 = 497215) (by norm_num)
theorem B2520757 : Blo 1178406 2520757 := bbase (se 5 (by rfl) ⟨118160, by rfl⟩ : syracuseStep 2520757 = 236321) (by norm_num)
theorem B2987725 : Blo 1178406 2987725 := bbase (se 3 (by rfl) ⟨560198, by rfl⟩ : syracuseStep 2987725 = 1120397) (by norm_num)
theorem B2651885 : Blo 1178406 2651885 := bbase (se 3 (by rfl) ⟨497228, by rfl⟩ : syracuseStep 2651885 = 994457) (by norm_num)
theorem B1259285 : Blo 1178406 1259285 := bbase (se 6 (by rfl) ⟨29514, by rfl⟩ : syracuseStep 1259285 = 59029) (by norm_num)
theorem B3356453 : Blo 1178406 3356453 := bbase (se 4 (by rfl) ⟨314667, by rfl⟩ : syracuseStep 3356453 = 629335) (by norm_num)
theorem B2520877 : Blo 1178406 2520877 := bbase (se 3 (by rfl) ⟨472664, by rfl⟩ : syracuseStep 2520877 = 945329) (by norm_num)
theorem B2651957 : Blo 1178406 2651957 := bbase (se 5 (by rfl) ⟨124310, by rfl⟩ : syracuseStep 2651957 = 248621) (by norm_num)
theorem B2987837 : Blo 1178406 2987837 := bbase (se 3 (by rfl) ⟨560219, by rfl⟩ : syracuseStep 2987837 = 1120439) (by norm_num)
theorem B1259345 : Blo 1178406 1259345 := bbase (se 2 (by rfl) ⟨472254, by rfl⟩ : syracuseStep 1259345 = 944509) (by norm_num)
theorem B5035877 : Blo 1178406 5035877 := bbase (se 4 (by rfl) ⟨472113, by rfl⟩ : syracuseStep 5035877 = 944227) (by norm_num)
theorem B2652029 : Blo 1178406 2652029 := bbase (se 3 (by rfl) ⟨497255, by rfl⟩ : syracuseStep 2652029 = 994511) (by norm_num)
theorem B4478885 : Blo 1178406 4478885 := bbase (se 4 (by rfl) ⟨419895, by rfl⟩ : syracuseStep 4478885 = 839791) (by norm_num)
theorem B1890229 : Blo 1178406 1890229 := bbase (se 5 (by rfl) ⟨88604, by rfl⟩ : syracuseStep 1890229 = 177209) (by norm_num)
theorem B2652101 : Blo 1178406 2652101 := bbase (se 4 (by rfl) ⟨248634, by rfl⟩ : syracuseStep 2652101 = 497269) (by norm_num)
theorem B3979205 : Blo 1178406 3979205 := bbase (se 4 (by rfl) ⟨373050, by rfl⟩ : syracuseStep 3979205 = 746101) (by norm_num)
theorem B5969861 : Blo 1178406 5969861 := bbase (se 4 (by rfl) ⟨559674, by rfl⟩ : syracuseStep 5969861 = 1119349) (by norm_num)
theorem B1259473 : Blo 1178406 1259473 := bbase (se 2 (by rfl) ⟨472302, by rfl⟩ : syracuseStep 1259473 = 944605) (by norm_num)
theorem B1988597 : Blo 1178406 1988597 := bbase (se 5 (by rfl) ⟨93215, by rfl⟩ : syracuseStep 1988597 = 186431) (by norm_num)
theorem B2652173 : Blo 1178406 2652173 := bbase (se 3 (by rfl) ⟨497282, by rfl⟩ : syracuseStep 2652173 = 994565) (by norm_num)
theorem B2652245 : Blo 1178406 2652245 := bbase (se 8 (by rfl) ⟨15540, by rfl⟩ : syracuseStep 2652245 = 31081) (by norm_num)
theorem B1988725 : Blo 1178406 1988725 := bbase (se 5 (by rfl) ⟨93221, by rfl⟩ : syracuseStep 1988725 = 186443) (by norm_num)
theorem B2652317 : Blo 1178406 2652317 := bbase (se 3 (by rfl) ⟨497309, by rfl⟩ : syracuseStep 2652317 = 994619) (by norm_num)
theorem B5667013 : Blo 1178406 5667013 := bbase (se 4 (by rfl) ⟨531282, by rfl⟩ : syracuseStep 5667013 = 1062565) (by norm_num)
theorem B1767629 : Blo 1178406 1767629 := bbase (se 3 (by rfl) ⟨331430, by rfl⟩ : syracuseStep 1767629 = 662861) (by norm_num)
theorem B1988813 : Blo 1178406 1988813 := bbase (se 3 (by rfl) ⟨372902, by rfl⟩ : syracuseStep 1988813 = 745805) (by norm_num)
theorem B1767653 : Blo 1178406 1767653 := bbase (se 4 (by rfl) ⟨165717, by rfl⟩ : syracuseStep 1767653 = 331435) (by norm_num)
theorem B2652389 : Blo 1178406 2652389 := bbase (se 4 (by rfl) ⟨248661, by rfl⟩ : syracuseStep 2652389 = 497323) (by norm_num)
theorem B1767677 : Blo 1178406 1767677 := bbase (se 3 (by rfl) ⟨331439, by rfl⟩ : syracuseStep 1767677 = 662879) (by norm_num)
theorem B1767701 : Blo 1178406 1767701 := bbase (se 6 (by rfl) ⟨41430, by rfl⟩ : syracuseStep 1767701 = 82861) (by norm_num)
theorem B2832661 : Blo 1178406 2832661 := bbase (se 6 (by rfl) ⟨66390, by rfl⟩ : syracuseStep 2832661 = 132781) (by norm_num)
theorem B13441301 : Blo 1178406 13441301 := bbase (se 6 (by rfl) ⟨315030, by rfl⟩ : syracuseStep 13441301 = 630061) (by norm_num)
theorem B1767725 : Blo 1178406 1767725 := bbase (se 3 (by rfl) ⟨331448, by rfl⟩ : syracuseStep 1767725 = 662897) (by norm_num)
theorem B2652461 : Blo 1178406 2652461 := bbase (se 3 (by rfl) ⟨497336, by rfl⟩ : syracuseStep 2652461 = 994673) (by norm_num)
theorem B2390317 : Blo 1178406 2390317 := bbase (se 3 (by rfl) ⟨448184, by rfl⟩ : syracuseStep 2390317 = 896369) (by norm_num)
theorem B1767749 : Blo 1178406 1767749 := bbase (se 4 (by rfl) ⟨165726, by rfl⟩ : syracuseStep 1767749 = 331453) (by norm_num)
theorem B1988941 : Blo 1178406 1988941 := bbase (se 3 (by rfl) ⟨372926, by rfl⟩ : syracuseStep 1988941 = 745853) (by norm_num)
theorem B1767773 : Blo 1178406 1767773 := bbase (se 3 (by rfl) ⟨331457, by rfl⟩ : syracuseStep 1767773 = 662915) (by norm_num)
theorem B1767797 : Blo 1178406 1767797 := bbase (se 5 (by rfl) ⟨82865, by rfl⟩ : syracuseStep 1767797 = 165731) (by norm_num)
theorem B2652533 : Blo 1178406 2652533 := bbase (se 5 (by rfl) ⟨124337, by rfl⟩ : syracuseStep 2652533 = 248675) (by norm_num)
theorem B3979637 : Blo 1178406 3979637 := bbase (se 5 (by rfl) ⟨186545, by rfl⟩ : syracuseStep 3979637 = 373091) (by norm_num)
theorem B1767821 : Blo 1178406 1767821 := bbase (se 3 (by rfl) ⟨331466, by rfl⟩ : syracuseStep 1767821 = 662933) (by norm_num)
theorem B1259917 : Blo 1178406 1259917 := bbase (se 3 (by rfl) ⟨236234, by rfl⟩ : syracuseStep 1259917 = 472469) (by norm_num)
theorem B1767845 : Blo 1178406 1767845 := bbase (se 4 (by rfl) ⟨165735, by rfl⟩ : syracuseStep 1767845 = 331471) (by norm_num)
theorem B1989029 : Blo 1178406 1989029 := bbase (se 4 (by rfl) ⟨186471, by rfl⟩ : syracuseStep 1989029 = 372943) (by norm_num)
theorem B1767869 : Blo 1178406 1767869 := bbase (se 3 (by rfl) ⟨331475, by rfl⟩ : syracuseStep 1767869 = 662951) (by norm_num)
theorem B2652605 : Blo 1178406 2652605 := bbase (se 3 (by rfl) ⟨497363, by rfl⟩ : syracuseStep 2652605 = 994727) (by norm_num)
theorem B1513937 : Blo 1178406 1513937 := bbase (se 2 (by rfl) ⟨567726, by rfl⟩ : syracuseStep 1513937 = 1135453) (by norm_num)
theorem B1767893 : Blo 1178406 1767893 := bbase (se 7 (by rfl) ⟨20717, by rfl⟩ : syracuseStep 1767893 = 41435) (by norm_num)
theorem B1767917 : Blo 1178406 1767917 := bbase (se 3 (by rfl) ⟨331484, by rfl⟩ : syracuseStep 1767917 = 662969) (by norm_num)
theorem B2726389 : Blo 1178406 2726389 := bbase (se 5 (by rfl) ⟨127799, by rfl⟩ : syracuseStep 2726389 = 255599) (by norm_num)
theorem B3635701 : Blo 1178406 3635701 := bbase (se 5 (by rfl) ⟨170423, by rfl⟩ : syracuseStep 3635701 = 340847) (by norm_num)
theorem B3832309 : Blo 1178406 3832309 := bbase (se 5 (by rfl) ⟨179639, by rfl⟩ : syracuseStep 3832309 = 359279) (by norm_num)
theorem B1767941 : Blo 1178406 1767941 := bbase (se 4 (by rfl) ⟨165744, by rfl⟩ : syracuseStep 1767941 = 331489) (by norm_num)
theorem B2652677 : Blo 1178406 2652677 := bbase (se 4 (by rfl) ⟨248688, by rfl⟩ : syracuseStep 2652677 = 497377) (by norm_num)
theorem B1260037 : Blo 1178406 1260037 := bbase (se 4 (by rfl) ⟨118128, by rfl⟩ : syracuseStep 1260037 = 236257) (by norm_num)
theorem B1767965 : Blo 1178406 1767965 := bbase (se 3 (by rfl) ⟨331493, by rfl⟩ : syracuseStep 1767965 = 662987) (by norm_num)
theorem B1989157 : Blo 1178406 1989157 := bbase (se 4 (by rfl) ⟨186483, by rfl⟩ : syracuseStep 1989157 = 372967) (by norm_num)
theorem B1767989 : Blo 1178406 1767989 := bbase (se 5 (by rfl) ⟨82874, by rfl⟩ : syracuseStep 1767989 = 165749) (by norm_num)
theorem B1768013 : Blo 1178406 1768013 := bbase (se 3 (by rfl) ⟨331502, by rfl⟩ : syracuseStep 1768013 = 663005) (by norm_num)
theorem B2652749 : Blo 1178406 2652749 := bbase (se 3 (by rfl) ⟨497390, by rfl⟩ : syracuseStep 2652749 = 994781) (by norm_num)
theorem B1677925 : Blo 1178406 1677925 := bbase (se 4 (by rfl) ⟨157305, by rfl⟩ : syracuseStep 1677925 = 314611) (by norm_num)
theorem B1768037 : Blo 1178406 1768037 := bbase (se 4 (by rfl) ⟨165753, by rfl⟩ : syracuseStep 1768037 = 331507) (by norm_num)
theorem B1915501 : Blo 1178406 1915501 := bbase (se 3 (by rfl) ⟨359156, by rfl⟩ : syracuseStep 1915501 = 718313) (by norm_num)
theorem B1768061 : Blo 1178406 1768061 := bbase (se 3 (by rfl) ⟨331511, by rfl⟩ : syracuseStep 1768061 = 663023) (by norm_num)
theorem B1989245 : Blo 1178406 1989245 := bbase (se 3 (by rfl) ⟨372983, by rfl⟩ : syracuseStep 1989245 = 745967) (by norm_num)
theorem B1325713 : Blo 1178406 1325713 := bbase (se 2 (by rfl) ⟨497142, by rfl⟩ : syracuseStep 1325713 = 994285) (by norm_num)
theorem B1768085 : Blo 1178406 1768085 := bbase (se 6 (by rfl) ⟨41439, by rfl⟩ : syracuseStep 1768085 = 82879) (by norm_num)
theorem B2652821 : Blo 1178406 2652821 := bbase (se 6 (by rfl) ⟨62175, by rfl⟩ : syracuseStep 2652821 = 124351) (by norm_num)
theorem B1768109 : Blo 1178406 1768109 := bbase (se 3 (by rfl) ⟨331520, by rfl⟩ : syracuseStep 1768109 = 663041) (by norm_num)
theorem B1325749 : Blo 1178406 1325749 := bbase (se 5 (by rfl) ⟨62144, by rfl⟩ : syracuseStep 1325749 = 124289) (by norm_num)
theorem B12114613 : Blo 1178406 12114613 := bbase (se 5 (by rfl) ⟨567872, by rfl⟩ : syracuseStep 12114613 = 1135745) (by norm_num)
theorem B1415869 : Blo 1178406 1415869 := bbase (se 3 (by rfl) ⟨265475, by rfl⟩ : syracuseStep 1415869 = 530951) (by norm_num)
theorem B1194689 : Blo 1178406 1194689 := bbase (se 2 (by rfl) ⟨448008, by rfl⟩ : syracuseStep 1194689 = 896017) (by norm_num)
theorem B1768133 : Blo 1178406 1768133 := bbase (se 4 (by rfl) ⟨165762, by rfl⟩ : syracuseStep 1768133 = 331525) (by norm_num)
theorem B12761813 : Blo 1178406 12761813 := bbase (se 7 (by rfl) ⟨149552, by rfl⟩ : syracuseStep 12761813 = 299105) (by norm_num)
theorem B1325785 : Blo 1178406 1325785 := bbase (se 2 (by rfl) ⟨497169, by rfl⟩ : syracuseStep 1325785 = 994339) (by norm_num)
theorem B1768157 : Blo 1178406 1768157 := bbase (se 3 (by rfl) ⟨331529, by rfl⟩ : syracuseStep 1768157 = 663059) (by norm_num)
theorem B2652893 : Blo 1178406 2652893 := bbase (se 3 (by rfl) ⟨497417, by rfl⟩ : syracuseStep 2652893 = 994835) (by norm_num)
theorem B1768181 : Blo 1178406 1768181 := bbase (se 5 (by rfl) ⟨82883, by rfl⟩ : syracuseStep 1768181 = 165767) (by norm_num)
theorem B1325821 : Blo 1178406 1325821 := bbase (se 3 (by rfl) ⟨248591, by rfl⟩ : syracuseStep 1325821 = 497183) (by norm_num)
theorem B1989373 : Blo 1178406 1989373 := bbase (se 3 (by rfl) ⟨373007, by rfl⟩ : syracuseStep 1989373 = 746015) (by norm_num)
theorem B1260289 : Blo 1178406 1260289 := bbase (se 2 (by rfl) ⟨472608, by rfl⟩ : syracuseStep 1260289 = 945217) (by norm_num)
theorem B1260293 : Blo 1178406 1260293 := bbase (se 4 (by rfl) ⟨118152, by rfl⟩ : syracuseStep 1260293 = 236305) (by norm_num)
theorem B1768205 : Blo 1178406 1768205 := bbase (se 3 (by rfl) ⟨331538, by rfl⟩ : syracuseStep 1768205 = 663077) (by norm_num)
theorem B1325857 : Blo 1178406 1325857 := bbase (se 2 (by rfl) ⟨497196, by rfl⟩ : syracuseStep 1325857 = 994393) (by norm_num)
theorem B1768229 : Blo 1178406 1768229 := bbase (se 4 (by rfl) ⟨165771, by rfl⟩ : syracuseStep 1768229 = 331543) (by norm_num)
theorem B2652965 : Blo 1178406 2652965 := bbase (se 4 (by rfl) ⟨248715, by rfl⟩ : syracuseStep 2652965 = 497431) (by norm_num)
theorem B3980069 : Blo 1178406 3980069 := bbase (se 4 (by rfl) ⟨373131, by rfl⟩ : syracuseStep 3980069 = 746263) (by norm_num)
theorem B1768253 : Blo 1178406 1768253 := bbase (se 3 (by rfl) ⟨331547, by rfl⟩ : syracuseStep 1768253 = 663095) (by norm_num)
theorem B1325893 : Blo 1178406 1325893 := bbase (se 4 (by rfl) ⟨124302, by rfl⟩ : syracuseStep 1325893 = 248605) (by norm_num)
theorem B1768277 : Blo 1178406 1768277 := bbase (se 9 (by rfl) ⟨5180, by rfl⟩ : syracuseStep 1768277 = 10361) (by norm_num)
theorem B1989461 : Blo 1178406 1989461 := bbase (se 9 (by rfl) ⟨5828, by rfl⟩ : syracuseStep 1989461 = 11657) (by norm_num)
theorem B1325929 : Blo 1178406 1325929 := bbase (se 2 (by rfl) ⟨497223, by rfl⟩ : syracuseStep 1325929 = 994447) (by norm_num)
theorem B1768301 : Blo 1178406 1768301 := bbase (se 3 (by rfl) ⟨331556, by rfl⟩ : syracuseStep 1768301 = 663113) (by norm_num)
theorem B2653037 : Blo 1178406 2653037 := bbase (se 3 (by rfl) ⟨497444, by rfl⟩ : syracuseStep 2653037 = 994889) (by norm_num)
theorem B1768325 : Blo 1178406 1768325 := bbase (se 4 (by rfl) ⟨165780, by rfl⟩ : syracuseStep 1768325 = 331561) (by norm_num)
theorem B1325965 : Blo 1178406 1325965 := bbase (se 3 (by rfl) ⟨248618, by rfl⟩ : syracuseStep 1325965 = 497237) (by norm_num)
theorem B7551893 : Blo 1178406 7551893 := bbase (se 6 (by rfl) ⟨176997, by rfl⟩ : syracuseStep 7551893 = 353995) (by norm_num)
theorem B1768349 : Blo 1178406 1768349 := bbase (se 3 (by rfl) ⟨331565, by rfl⟩ : syracuseStep 1768349 = 663131) (by norm_num)
theorem B1326001 : Blo 1178406 1326001 := bbase (se 2 (by rfl) ⟨497250, by rfl⟩ : syracuseStep 1326001 = 994501) (by norm_num)
theorem B1678261 : Blo 1178406 1678261 := bbase (se 5 (by rfl) ⟨78668, by rfl⟩ : syracuseStep 1678261 = 157337) (by norm_num)
theorem B1768373 : Blo 1178406 1768373 := bbase (se 5 (by rfl) ⟨82892, by rfl⟩ : syracuseStep 1768373 = 165785) (by norm_num)
theorem B2653109 : Blo 1178406 2653109 := bbase (se 5 (by rfl) ⟨124364, by rfl⟩ : syracuseStep 2653109 = 248729) (by norm_num)
theorem B4250549 : Blo 1178406 4250549 := bbase (se 5 (by rfl) ⟨199244, by rfl⟩ : syracuseStep 4250549 = 398489) (by norm_num)
theorem B1768397 : Blo 1178406 1768397 := bbase (se 3 (by rfl) ⟨331574, by rfl⟩ : syracuseStep 1768397 = 663149) (by norm_num)
theorem B1194961 : Blo 1178406 1194961 := bbase (se 2 (by rfl) ⟨448110, by rfl⟩ : syracuseStep 1194961 = 896221) (by norm_num)
theorem B1326037 : Blo 1178406 1326037 := bbase (se 7 (by rfl) ⟨15539, by rfl⟩ : syracuseStep 1326037 = 31079) (by norm_num)
theorem B1989589 : Blo 1178406 1989589 := bbase (se 7 (by rfl) ⟨23315, by rfl⟩ : syracuseStep 1989589 = 46631) (by norm_num)
theorem B2833373 : Blo 1178406 2833373 := bbase (se 3 (by rfl) ⟨531257, by rfl⟩ : syracuseStep 2833373 = 1062515) (by norm_num)
theorem B1768421 : Blo 1178406 1768421 := bbase (se 4 (by rfl) ⟨165789, by rfl⟩ : syracuseStep 1768421 = 331579) (by norm_num)
theorem B2153453 : Blo 1178406 2153453 := bbase (se 3 (by rfl) ⟨403772, by rfl⟩ : syracuseStep 2153453 = 807545) (by norm_num)
theorem B1326073 : Blo 1178406 1326073 := bbase (se 2 (by rfl) ⟨497277, by rfl⟩ : syracuseStep 1326073 = 994555) (by norm_num)
theorem B1768445 : Blo 1178406 1768445 := bbase (se 3 (by rfl) ⟨331583, by rfl⟩ : syracuseStep 1768445 = 663167) (by norm_num)
theorem B2653181 : Blo 1178406 2653181 := bbase (se 3 (by rfl) ⟨497471, by rfl⟩ : syracuseStep 2653181 = 994943) (by norm_num)
theorem B1768469 : Blo 1178406 1768469 := bbase (se 6 (by rfl) ⟨41448, by rfl⟩ : syracuseStep 1768469 = 82897) (by norm_num)
theorem B1326109 : Blo 1178406 1326109 := bbase (se 3 (by rfl) ⟨248645, by rfl⟩ : syracuseStep 1326109 = 497291) (by norm_num)
theorem B1768493 : Blo 1178406 1768493 := bbase (se 3 (by rfl) ⟨331592, by rfl⟩ : syracuseStep 1768493 = 663185) (by norm_num)
theorem B1989677 : Blo 1178406 1989677 := bbase (se 3 (by rfl) ⟨373064, by rfl⟩ : syracuseStep 1989677 = 746129) (by norm_num)
theorem B1326145 : Blo 1178406 1326145 := bbase (se 2 (by rfl) ⟨497304, by rfl⟩ : syracuseStep 1326145 = 994609) (by norm_num)
theorem B1768517 : Blo 1178406 1768517 := bbase (se 4 (by rfl) ⟨165798, by rfl⟩ : syracuseStep 1768517 = 331597) (by norm_num)
theorem B2653253 : Blo 1178406 2653253 := bbase (se 4 (by rfl) ⟨248742, by rfl⟩ : syracuseStep 2653253 = 497485) (by norm_num)
theorem B4480069 : Blo 1178406 4480069 := bbase (se 4 (by rfl) ⟨420006, by rfl⟩ : syracuseStep 4480069 = 840013) (by norm_num)
theorem B1768541 : Blo 1178406 1768541 := bbase (se 3 (by rfl) ⟨331601, by rfl⟩ : syracuseStep 1768541 = 663203) (by norm_num)
theorem B1326181 : Blo 1178406 1326181 := bbase (se 4 (by rfl) ⟨124329, by rfl⟩ : syracuseStep 1326181 = 248659) (by norm_num)
theorem B1768565 : Blo 1178406 1768565 := bbase (se 5 (by rfl) ⟨82901, by rfl⟩ : syracuseStep 1768565 = 165803) (by norm_num)
theorem B1326217 : Blo 1178406 1326217 := bbase (se 2 (by rfl) ⟨497331, by rfl⟩ : syracuseStep 1326217 = 994663) (by norm_num)
theorem B1678477 : Blo 1178406 1678477 := bbase (se 3 (by rfl) ⟨314714, by rfl⟩ : syracuseStep 1678477 = 629429) (by norm_num)
theorem B1768589 : Blo 1178406 1768589 := bbase (se 3 (by rfl) ⟨331610, by rfl⟩ : syracuseStep 1768589 = 663221) (by norm_num)
theorem B2653325 : Blo 1178406 2653325 := bbase (se 3 (by rfl) ⟨497498, by rfl⟩ : syracuseStep 2653325 = 994997) (by norm_num)
theorem B1768613 : Blo 1178406 1768613 := bbase (se 4 (by rfl) ⟨165807, by rfl⟩ : syracuseStep 1768613 = 331615) (by norm_num)
theorem B1326253 : Blo 1178406 1326253 := bbase (se 3 (by rfl) ⟨248672, by rfl⟩ : syracuseStep 1326253 = 497345) (by norm_num)
theorem B1989805 : Blo 1178406 1989805 := bbase (se 3 (by rfl) ⟨373088, by rfl⟩ : syracuseStep 1989805 = 746177) (by norm_num)
theorem B1768637 : Blo 1178406 1768637 := bbase (se 3 (by rfl) ⟨331619, by rfl⟩ : syracuseStep 1768637 = 663239) (by norm_num)
theorem B1326289 : Blo 1178406 1326289 := bbase (se 2 (by rfl) ⟨497358, by rfl⟩ : syracuseStep 1326289 = 994717) (by norm_num)
theorem B1768661 : Blo 1178406 1768661 := bbase (se 7 (by rfl) ⟨20726, by rfl⟩ : syracuseStep 1768661 = 41453) (by norm_num)
theorem B2653397 : Blo 1178406 2653397 := bbase (se 7 (by rfl) ⟨31094, by rfl⟩ : syracuseStep 2653397 = 62189) (by norm_num)
theorem B3980501 : Blo 1178406 3980501 := bbase (se 7 (by rfl) ⟨46646, by rfl⟩ : syracuseStep 3980501 = 93293) (by norm_num)
theorem B5971157 : Blo 1178406 5971157 := bbase (se 7 (by rfl) ⟨69974, by rfl⟩ : syracuseStep 5971157 = 139949) (by norm_num)
theorem B1768685 : Blo 1178406 1768685 := bbase (se 3 (by rfl) ⟨331628, by rfl⟩ : syracuseStep 1768685 = 663257) (by norm_num)
theorem B1326325 : Blo 1178406 1326325 := bbase (se 5 (by rfl) ⟨62171, by rfl⟩ : syracuseStep 1326325 = 124343) (by norm_num)
theorem B1989893 : Blo 1178406 1989893 := bbase (se 4 (by rfl) ⟨186552, by rfl⟩ : syracuseStep 1989893 = 373105) (by norm_num)
theorem B1768709 : Blo 1178406 1768709 := bbase (se 4 (by rfl) ⟨165816, by rfl⟩ : syracuseStep 1768709 = 331633) (by norm_num)
theorem B1195273 : Blo 1178406 1195273 := bbase (se 2 (by rfl) ⟨448227, by rfl⟩ : syracuseStep 1195273 = 896455) (by norm_num)
theorem B20159765 : Blo 1178406 20159765 := bbase (se 6 (by rfl) ⟨472494, by rfl⟩ : syracuseStep 20159765 = 944989) (by norm_num)
theorem B1326361 : Blo 1178406 1326361 := bbase (se 2 (by rfl) ⟨497385, by rfl⟩ : syracuseStep 1326361 = 994771) (by norm_num)
theorem B1768733 : Blo 1178406 1768733 := bbase (se 3 (by rfl) ⟨331637, by rfl⟩ : syracuseStep 1768733 = 663275) (by norm_num)
theorem B2653469 : Blo 1178406 2653469 := bbase (se 3 (by rfl) ⟨497525, by rfl⟩ : syracuseStep 2653469 = 995051) (by norm_num)
theorem B2424109 : Blo 1178406 2424109 := bbase (se 3 (by rfl) ⟨454520, by rfl⟩ : syracuseStep 2424109 = 909041) (by norm_num)
theorem B1400113 : Blo 1178406 1400113 := bbase (se 2 (by rfl) ⟨525042, by rfl⟩ : syracuseStep 1400113 = 1050085) (by norm_num)
theorem B1768757 : Blo 1178406 1768757 := bbase (se 5 (by rfl) ⟨82910, by rfl⟩ : syracuseStep 1768757 = 165821) (by norm_num)
theorem B1326397 : Blo 1178406 1326397 := bbase (se 3 (by rfl) ⟨248699, by rfl⟩ : syracuseStep 1326397 = 497399) (by norm_num)
theorem B1768781 : Blo 1178406 1768781 := bbase (se 3 (by rfl) ⟨331646, by rfl⟩ : syracuseStep 1768781 = 663293) (by norm_num)
theorem B3358037 : Blo 1178406 3358037 := bbase (se 11 (by rfl) ⟨2459, by rfl⟩ : syracuseStep 3358037 = 4919) (by norm_num)
theorem B1326433 : Blo 1178406 1326433 := bbase (se 2 (by rfl) ⟨497412, by rfl⟩ : syracuseStep 1326433 = 994825) (by norm_num)
theorem B1768805 : Blo 1178406 1768805 := bbase (se 4 (by rfl) ⟨165825, by rfl⟩ : syracuseStep 1768805 = 331651) (by norm_num)
theorem B2653541 : Blo 1178406 2653541 := bbase (se 4 (by rfl) ⟨248769, by rfl⟩ : syracuseStep 2653541 = 497539) (by norm_num)
theorem B4480373 : Blo 1178406 4480373 := bbase (se 5 (by rfl) ⟨210017, by rfl⟩ : syracuseStep 4480373 = 420035) (by norm_num)
theorem B1768829 : Blo 1178406 1768829 := bbase (se 3 (by rfl) ⟨331655, by rfl⟩ : syracuseStep 1768829 = 663311) (by norm_num)
theorem B1326469 : Blo 1178406 1326469 := bbase (se 4 (by rfl) ⟨124356, by rfl⟩ : syracuseStep 1326469 = 248713) (by norm_num)
theorem B1990021 : Blo 1178406 1990021 := bbase (se 4 (by rfl) ⟨186564, by rfl⟩ : syracuseStep 1990021 = 373129) (by norm_num)
theorem B1768853 : Blo 1178406 1768853 := bbase (se 6 (by rfl) ⟨41457, by rfl⟩ : syracuseStep 1768853 = 82915) (by norm_num)
theorem B1326505 : Blo 1178406 1326505 := bbase (se 2 (by rfl) ⟨497439, by rfl⟩ : syracuseStep 1326505 = 994879) (by norm_num)
theorem B1768877 : Blo 1178406 1768877 := bbase (se 3 (by rfl) ⟨331664, by rfl⟩ : syracuseStep 1768877 = 663329) (by norm_num)
theorem B2653613 : Blo 1178406 2653613 := bbase (se 3 (by rfl) ⟨497552, by rfl⟩ : syracuseStep 2653613 = 995105) (by norm_num)
theorem B1768901 : Blo 1178406 1768901 := bbase (se 4 (by rfl) ⟨165834, by rfl⟩ : syracuseStep 1768901 = 331669) (by norm_num)
theorem B1326541 : Blo 1178406 1326541 := bbase (se 3 (by rfl) ⟨248726, by rfl⟩ : syracuseStep 1326541 = 497453) (by norm_num)
theorem B1768925 : Blo 1178406 1768925 := bbase (se 3 (by rfl) ⟨331673, by rfl⟩ : syracuseStep 1768925 = 663347) (by norm_num)
theorem B1990109 : Blo 1178406 1990109 := bbase (se 3 (by rfl) ⟨373145, by rfl⟩ : syracuseStep 1990109 = 746291) (by norm_num)
theorem B1326577 : Blo 1178406 1326577 := bbase (se 2 (by rfl) ⟨497466, by rfl⟩ : syracuseStep 1326577 = 994933) (by norm_num)
theorem B1768949 : Blo 1178406 1768949 := bbase (se 5 (by rfl) ⟨82919, by rfl⟩ : syracuseStep 1768949 = 165839) (by norm_num)
theorem B2653685 : Blo 1178406 2653685 := bbase (se 5 (by rfl) ⟨124391, by rfl⟩ : syracuseStep 2653685 = 248783) (by norm_num)
theorem B1678853 : Blo 1178406 1678853 := bbase (se 4 (by rfl) ⟨157392, by rfl⟩ : syracuseStep 1678853 = 314785) (by norm_num)
theorem B1768973 : Blo 1178406 1768973 := bbase (se 3 (by rfl) ⟨331682, by rfl⟩ : syracuseStep 1768973 = 663365) (by norm_num)
theorem B1326613 : Blo 1178406 1326613 := bbase (se 6 (by rfl) ⟨31092, by rfl⟩ : syracuseStep 1326613 = 62185) (by norm_num)
theorem B20708885 : Blo 1178406 20708885 := bbase (se 6 (by rfl) ⟨485364, by rfl⟩ : syracuseStep 20708885 = 970729) (by norm_num)
theorem B1768997 : Blo 1178406 1768997 := bbase (se 4 (by rfl) ⟨165843, by rfl⟩ : syracuseStep 1768997 = 331687) (by norm_num)
theorem B1416749 : Blo 1178406 1416749 := bbase (se 3 (by rfl) ⟨265640, by rfl⟩ : syracuseStep 1416749 = 531281) (by norm_num)
theorem B1326649 : Blo 1178406 1326649 := bbase (se 2 (by rfl) ⟨497493, by rfl⟩ : syracuseStep 1326649 = 994987) (by norm_num)
theorem B1769021 : Blo 1178406 1769021 := bbase (se 3 (by rfl) ⟨331691, by rfl⟩ : syracuseStep 1769021 = 663383) (by norm_num)
theorem B2653757 : Blo 1178406 2653757 := bbase (se 3 (by rfl) ⟨497579, by rfl⟩ : syracuseStep 2653757 = 995159) (by norm_num)
theorem B1769045 : Blo 1178406 1769045 := bbase (se 8 (by rfl) ⟨10365, by rfl⟩ : syracuseStep 1769045 = 20731) (by norm_num)
theorem B5037653 : Blo 1178406 5037653 := bbase (se 8 (by rfl) ⟨29517, by rfl⟩ : syracuseStep 5037653 = 59035) (by norm_num)
theorem B1326685 : Blo 1178406 1326685 := bbase (se 3 (by rfl) ⟨248753, by rfl⟩ : syracuseStep 1326685 = 497507) (by norm_num)
theorem B1990237 : Blo 1178406 1990237 := bbase (se 3 (by rfl) ⟨373169, by rfl⟩ : syracuseStep 1990237 = 746339) (by norm_num)
theorem B1769069 : Blo 1178406 1769069 := bbase (se 3 (by rfl) ⟨331700, by rfl⟩ : syracuseStep 1769069 = 663401) (by norm_num)
theorem B2834045 : Blo 1178406 2834045 := bbase (se 3 (by rfl) ⟨531383, by rfl⟩ : syracuseStep 2834045 = 1062767) (by norm_num)
theorem B1326721 : Blo 1178406 1326721 := bbase (se 2 (by rfl) ⟨497520, by rfl⟩ : syracuseStep 1326721 = 995041) (by norm_num)
theorem B1769093 : Blo 1178406 1769093 := bbase (se 4 (by rfl) ⟨165852, by rfl⟩ : syracuseStep 1769093 = 331705) (by norm_num)
theorem B2653829 : Blo 1178406 2653829 := bbase (se 4 (by rfl) ⟨248796, by rfl⟩ : syracuseStep 2653829 = 497593) (by norm_num)
theorem B3980933 : Blo 1178406 3980933 := bbase (se 4 (by rfl) ⟨373212, by rfl⟩ : syracuseStep 3980933 = 746425) (by norm_num)
theorem B1769117 : Blo 1178406 1769117 := bbase (se 3 (by rfl) ⟨331709, by rfl⟩ : syracuseStep 1769117 = 663419) (by norm_num)
theorem B1416865 : Blo 1178406 1416865 := bbase (se 2 (by rfl) ⟨531324, by rfl⟩ : syracuseStep 1416865 = 1062649) (by norm_num)
theorem B1326757 : Blo 1178406 1326757 := bbase (se 4 (by rfl) ⟨124383, by rfl⟩ : syracuseStep 1326757 = 248767) (by norm_num)
theorem B1769141 : Blo 1178406 1769141 := bbase (se 5 (by rfl) ⟨82928, by rfl⟩ : syracuseStep 1769141 = 165857) (by norm_num)
theorem B1990325 : Blo 1178406 1990325 := bbase (se 5 (by rfl) ⟨93296, by rfl⟩ : syracuseStep 1990325 = 186593) (by norm_num)
theorem B3546821 : Blo 1178406 3546821 := bbase (se 4 (by rfl) ⟨332514, by rfl⟩ : syracuseStep 3546821 = 665029) (by norm_num)
theorem B1326793 : Blo 1178406 1326793 := bbase (se 2 (by rfl) ⟨497547, by rfl⟩ : syracuseStep 1326793 = 995095) (by norm_num)
theorem B1769165 : Blo 1178406 1769165 := bbase (se 3 (by rfl) ⟨331718, by rfl⟩ : syracuseStep 1769165 = 663437) (by norm_num)
theorem B2653901 : Blo 1178406 2653901 := bbase (se 3 (by rfl) ⟨497606, by rfl⟩ : syracuseStep 2653901 = 995213) (by norm_num)
theorem B1769189 : Blo 1178406 1769189 := bbase (se 4 (by rfl) ⟨165861, by rfl⟩ : syracuseStep 1769189 = 331723) (by norm_num)
theorem B1326829 : Blo 1178406 1326829 := bbase (se 3 (by rfl) ⟨248780, by rfl⟩ : syracuseStep 1326829 = 497561) (by norm_num)
theorem B1793773 : Blo 1178406 1793773 := bbase (se 3 (by rfl) ⟨336332, by rfl⟩ : syracuseStep 1793773 = 672665) (by norm_num)
theorem B9567989 : Blo 1178406 9567989 := bbase (se 5 (by rfl) ⟨448499, by rfl⟩ : syracuseStep 9567989 = 896999) (by norm_num)
theorem B4849397 : Blo 1178406 4849397 := bbase (se 5 (by rfl) ⟨227315, by rfl⟩ : syracuseStep 4849397 = 454631) (by norm_num)
theorem B1769213 : Blo 1178406 1769213 := bbase (se 3 (by rfl) ⟨331727, by rfl⟩ : syracuseStep 1769213 = 663455) (by norm_num)
theorem B1326865 : Blo 1178406 1326865 := bbase (se 2 (by rfl) ⟨497574, by rfl⟩ : syracuseStep 1326865 = 995149) (by norm_num)
theorem B1769237 : Blo 1178406 1769237 := bbase (se 6 (by rfl) ⟨41466, by rfl⟩ : syracuseStep 1769237 = 82933) (by norm_num)
theorem B2653973 : Blo 1178406 2653973 := bbase (se 6 (by rfl) ⟨62202, by rfl⟩ : syracuseStep 2653973 = 124405) (by norm_num)
theorem B1769261 : Blo 1178406 1769261 := bbase (se 3 (by rfl) ⟨331736, by rfl⟩ : syracuseStep 1769261 = 663473) (by norm_num)
theorem B1326901 : Blo 1178406 1326901 := bbase (se 5 (by rfl) ⟨62198, by rfl⟩ : syracuseStep 1326901 = 124397) (by norm_num)
theorem B1990453 : Blo 1178406 1990453 := bbase (se 5 (by rfl) ⟨93302, by rfl⟩ : syracuseStep 1990453 = 186605) (by norm_num)
theorem B1769285 : Blo 1178406 1769285 := bbase (se 4 (by rfl) ⟨165870, by rfl⟩ : syracuseStep 1769285 = 331741) (by norm_num)
theorem B5103445 : Blo 1178406 5103445 := bbase (se 9 (by rfl) ⟨14951, by rfl⟩ : syracuseStep 5103445 = 29903) (by norm_num)
theorem B1326937 : Blo 1178406 1326937 := bbase (se 2 (by rfl) ⟨497601, by rfl⟩ : syracuseStep 1326937 = 995203) (by norm_num)
theorem B1769309 : Blo 1178406 1769309 := bbase (se 3 (by rfl) ⟨331745, by rfl⟩ : syracuseStep 1769309 = 663491) (by norm_num)
theorem B2654045 : Blo 1178406 2654045 := bbase (se 3 (by rfl) ⟨497633, by rfl⟩ : syracuseStep 2654045 = 995267) (by norm_num)
theorem B3776357 : Blo 1178406 3776357 := bbase (se 4 (by rfl) ⟨354033, by rfl⟩ : syracuseStep 3776357 = 708067) (by norm_num)
theorem B1417061 : Blo 1178406 1417061 := bbase (se 4 (by rfl) ⟨132849, by rfl⟩ : syracuseStep 1417061 = 265699) (by norm_num)
theorem B1769333 : Blo 1178406 1769333 := bbase (se 5 (by rfl) ⟨82937, by rfl⟩ : syracuseStep 1769333 = 165875) (by norm_num)
theorem B1326973 : Blo 1178406 1326973 := bbase (se 3 (by rfl) ⟨248807, by rfl⟩ : syracuseStep 1326973 = 497615) (by norm_num)
theorem B1769357 : Blo 1178406 1769357 := bbase (se 3 (by rfl) ⟨331754, by rfl⟩ : syracuseStep 1769357 = 663509) (by norm_num)
theorem B1990541 : Blo 1178406 1990541 := bbase (se 3 (by rfl) ⟨373226, by rfl⟩ : syracuseStep 1990541 = 746453) (by norm_num)
theorem B1327009 : Blo 1178406 1327009 := bbase (se 2 (by rfl) ⟨497628, by rfl⟩ : syracuseStep 1327009 = 995257) (by norm_num)
theorem B1769381 : Blo 1178406 1769381 := bbase (se 4 (by rfl) ⟨165879, by rfl⟩ : syracuseStep 1769381 = 331759) (by norm_num)
theorem B2654117 : Blo 1178406 2654117 := bbase (se 4 (by rfl) ⟨248823, by rfl⟩ : syracuseStep 2654117 = 497647) (by norm_num)
theorem B1769405 : Blo 1178406 1769405 := bbase (se 3 (by rfl) ⟨331763, by rfl⟩ : syracuseStep 1769405 = 663527) (by norm_num)
theorem B1327045 : Blo 1178406 1327045 := bbase (se 4 (by rfl) ⟨124410, by rfl⟩ : syracuseStep 1327045 = 248821) (by norm_num)
theorem B1769429 : Blo 1178406 1769429 := bbase (se 7 (by rfl) ⟨20735, by rfl⟩ : syracuseStep 1769429 = 41471) (by norm_num)
theorem B1327081 : Blo 1178406 1327081 := bbase (se 2 (by rfl) ⟨497655, by rfl⟩ : syracuseStep 1327081 = 995311) (by norm_num)
theorem B1769453 : Blo 1178406 1769453 := bbase (se 3 (by rfl) ⟨331772, by rfl⟩ : syracuseStep 1769453 = 663545) (by norm_num)
theorem B2654189 : Blo 1178406 2654189 := bbase (se 3 (by rfl) ⟨497660, by rfl⟩ : syracuseStep 2654189 = 995321) (by norm_num)
theorem B3358709 : Blo 1178406 3358709 := bbase (se 5 (by rfl) ⟨157439, by rfl⟩ : syracuseStep 3358709 = 314879) (by norm_num)
theorem B4087811 : Blo 1178406 4087811 := bstep (se 1 (by rfl) ⟨3065858, by rfl⟩ : syracuseStep 4087811 = 6131717) B6131717
theorem B1179651 : Blo 1178406 1179651 := bstep (se 1 (by rfl) ⟨884738, by rfl⟩ : syracuseStep 1179651 = 1769477) B1769477
theorem B2654225 : Blo 1178406 2654225 := bstep (se 2 (by rfl) ⟨995334, by rfl⟩ : syracuseStep 2654225 = 1990669) B1990669
theorem B1769489 : Blo 1178406 1769489 := bstep (se 2 (by rfl) ⟨663558, by rfl⟩ : syracuseStep 1769489 = 1327117) B1327117
theorem B1179667 : Blo 1178406 1179667 := bstep (se 1 (by rfl) ⟨884750, by rfl⟩ : syracuseStep 1179667 = 1769501) B1769501
theorem B2654243 : Blo 1178406 2654243 := bstep (se 1 (by rfl) ⟨1990682, by rfl⟩ : syracuseStep 2654243 = 3981365) B3981365
theorem B1769507 : Blo 1178406 1769507 := bstep (se 1 (by rfl) ⟨1327130, by rfl⟩ : syracuseStep 1769507 = 2654261) B2654261
theorem B1179683 : Blo 1178406 1179683 := bstep (se 1 (by rfl) ⟨884762, by rfl⟩ : syracuseStep 1179683 = 1769525) B1769525
theorem B1679411 : Blo 1178406 1679411 := bstep (se 1 (by rfl) ⟨1259558, by rfl⟩ : syracuseStep 1679411 = 2519117) B2519117
theorem B1179699 : Blo 1178406 1179699 := bstep (se 1 (by rfl) ⟨884774, by rfl⟩ : syracuseStep 1179699 = 1769549) B1769549
theorem B1769537 : Blo 1178406 1769537 := bstep (se 2 (by rfl) ⟨663576, by rfl⟩ : syracuseStep 1769537 = 1327153) B1327153
theorem B1990723 : Blo 1178406 1990723 := bstep (se 1 (by rfl) ⟨1493042, by rfl⟩ : syracuseStep 1990723 = 2986085) B2986085
theorem B1327171 : Blo 1178406 1327171 := bstep (se 1 (by rfl) ⟨995378, by rfl⟩ : syracuseStep 1327171 = 1990757) B1990757
theorem B1179715 : Blo 1178406 1179715 := bstep (se 1 (by rfl) ⟨884786, by rfl⟩ : syracuseStep 1179715 = 1769573) B1769573
theorem B1769555 : Blo 1178406 1769555 := bstep (se 1 (by rfl) ⟨1327166, by rfl⟩ : syracuseStep 1769555 = 2654333) B2654333
theorem B1179731 : Blo 1178406 1179731 := bstep (se 1 (by rfl) ⟨884798, by rfl⟩ : syracuseStep 1179731 = 1769597) B1769597
theorem B1179747 : Blo 1178406 1179747 := bstep (se 1 (by rfl) ⟨884810, by rfl⟩ : syracuseStep 1179747 = 1769621) B1769621
theorem B4251761 : Blo 1178406 4251761 := bstep (se 2 (by rfl) ⟨1594410, by rfl⟩ : syracuseStep 4251761 = 3188821) B3188821
theorem B1769585 : Blo 1178406 1769585 := bstep (se 2 (by rfl) ⟨663594, by rfl⟩ : syracuseStep 1769585 = 1327189) B1327189
theorem B1179763 : Blo 1178406 1179763 := bstep (se 1 (by rfl) ⟨884822, by rfl⟩ : syracuseStep 1179763 = 1769645) B1769645
theorem B1679491 : Blo 1178406 1679491 := bstep (se 1 (by rfl) ⟨1259618, by rfl⟩ : syracuseStep 1679491 = 2519237) B2519237
theorem B1769603 : Blo 1178406 1769603 := bstep (se 1 (by rfl) ⟨1327202, by rfl⟩ : syracuseStep 1769603 = 2654405) B2654405
theorem B1179779 : Blo 1178406 1179779 := bstep (se 1 (by rfl) ⟨884834, by rfl⟩ : syracuseStep 1179779 = 1769669) B1769669
theorem B3588227 : Blo 1178406 3588227 := bstep (se 1 (by rfl) ⟨2691170, by rfl⟩ : syracuseStep 3588227 = 5382341) B5382341
theorem B7561349 : Blo 1178406 7561349 := bstep (se 4 (by rfl) ⟨708876, by rfl⟩ : syracuseStep 7561349 = 1417753) B1417753
theorem B1179795 : Blo 1178406 1179795 := bstep (se 1 (by rfl) ⟨884846, by rfl⟩ : syracuseStep 1179795 = 1769693) B1769693
theorem B1769633 : Blo 1178406 1769633 := bstep (se 2 (by rfl) ⟨663612, by rfl⟩ : syracuseStep 1769633 = 1327225) B1327225
theorem B1179811 : Blo 1178406 1179811 := bstep (se 1 (by rfl) ⟨884858, by rfl⟩ : syracuseStep 1179811 = 1769717) B1769717
theorem B1769651 : Blo 1178406 1769651 := bstep (se 1 (by rfl) ⟨1327238, by rfl⟩ : syracuseStep 1769651 = 2654477) B2654477
theorem B1179827 : Blo 1178406 1179827 := bstep (se 1 (by rfl) ⟨884870, by rfl⟩ : syracuseStep 1179827 = 1769741) B1769741
theorem B1179843 : Blo 1178406 1179843 := bstep (se 1 (by rfl) ⟨884882, by rfl⟩ : syracuseStep 1179843 = 1769765) B1769765
theorem B1990865 : Blo 1178406 1990865 := bstep (se 2 (by rfl) ⟨746574, by rfl⟩ : syracuseStep 1990865 = 1493149) B1493149
theorem B1769681 : Blo 1178406 1769681 := bstep (se 2 (by rfl) ⟨663630, by rfl⟩ : syracuseStep 1769681 = 1327261) B1327261
theorem B1327315 : Blo 1178406 1327315 := bstep (se 1 (by rfl) ⟨995486, by rfl⟩ : syracuseStep 1327315 = 1990973) B1990973
theorem B1179859 : Blo 1178406 1179859 := bstep (se 1 (by rfl) ⟨884894, by rfl⟩ : syracuseStep 1179859 = 1769789) B1769789
theorem B1769699 : Blo 1178406 1769699 := bstep (se 1 (by rfl) ⟨1327274, by rfl⟩ : syracuseStep 1769699 = 2654549) B2654549
theorem B1179875 : Blo 1178406 1179875 := bstep (se 1 (by rfl) ⟨884906, by rfl⟩ : syracuseStep 1179875 = 1769813) B1769813
theorem B1179891 : Blo 1178406 1179891 := bstep (se 1 (by rfl) ⟨884918, by rfl⟩ : syracuseStep 1179891 = 1769837) B1769837
theorem B1769729 : Blo 1178406 1769729 := bstep (se 2 (by rfl) ⟨663648, by rfl⟩ : syracuseStep 1769729 = 1327297) B1327297
theorem B1179907 : Blo 1178406 1179907 := bstep (se 1 (by rfl) ⟨884930, by rfl⟩ : syracuseStep 1179907 = 1769861) B1769861
theorem B3981581 : Blo 1178406 3981581 := bstep (se 3 (by rfl) ⟨746546, by rfl⟩ : syracuseStep 3981581 = 1493093) B1493093
theorem B1769747 : Blo 1178406 1769747 := bstep (se 1 (by rfl) ⟨1327310, by rfl⟩ : syracuseStep 1769747 = 2654621) B2654621
theorem B1179923 : Blo 1178406 1179923 := bstep (se 1 (by rfl) ⟨884942, by rfl⟩ : syracuseStep 1179923 = 1769885) B1769885
theorem B1179939 : Blo 1178406 1179939 := bstep (se 1 (by rfl) ⟨884954, by rfl⟩ : syracuseStep 1179939 = 1769909) B1769909
theorem B4481315 : Blo 1178406 4481315 := bstep (se 1 (by rfl) ⟨3360986, by rfl⟩ : syracuseStep 4481315 = 6721973) B6721973
theorem B2654513 : Blo 1178406 2654513 := bstep (se 2 (by rfl) ⟨995442, by rfl⟩ : syracuseStep 2654513 = 1990885) B1990885
theorem B1769777 : Blo 1178406 1769777 := bstep (se 2 (by rfl) ⟨663666, by rfl⟩ : syracuseStep 1769777 = 1327333) B1327333
theorem B1179955 : Blo 1178406 1179955 := bstep (se 1 (by rfl) ⟨884966, by rfl⟩ : syracuseStep 1179955 = 1769933) B1769933
theorem B3981635 : Blo 1178406 3981635 := bstep (se 1 (by rfl) ⟨2986226, by rfl⟩ : syracuseStep 3981635 = 5972453) B5972453
theorem B2654531 : Blo 1178406 2654531 := bstep (se 1 (by rfl) ⟨1990898, by rfl⟩ : syracuseStep 2654531 = 3981797) B3981797
theorem B1769795 : Blo 1178406 1769795 := bstep (se 1 (by rfl) ⟨1327346, by rfl⟩ : syracuseStep 1769795 = 2654693) B2654693
theorem B1179971 : Blo 1178406 1179971 := bstep (se 1 (by rfl) ⟨884978, by rfl⟩ : syracuseStep 1179971 = 1769957) B1769957
theorem B1990993 : Blo 1178406 1990993 := bstep (se 2 (by rfl) ⟨746622, by rfl⟩ : syracuseStep 1990993 = 1493245) B1493245
theorem B1179987 : Blo 1178406 1179987 := bstep (se 1 (by rfl) ⟨884990, by rfl⟩ : syracuseStep 1179987 = 1769981) B1769981
theorem B1769825 : Blo 1178406 1769825 := bstep (se 2 (by rfl) ⟨663684, by rfl⟩ : syracuseStep 1769825 = 1327369) B1327369
theorem B1327459 : Blo 1178406 1327459 := bstep (se 1 (by rfl) ⟨995594, by rfl⟩ : syracuseStep 1327459 = 1991189) B1991189
theorem B1180003 : Blo 1178406 1180003 := bstep (se 1 (by rfl) ⟨885002, by rfl⟩ : syracuseStep 1180003 = 1770005) B1770005
theorem B3776881 : Blo 1178406 3776881 := bstep (se 2 (by rfl) ⟨1416330, by rfl⟩ : syracuseStep 3776881 = 2832661) B2832661
theorem B1991027 : Blo 1178406 1991027 := bstep (se 1 (by rfl) ⟨1493270, by rfl⟩ : syracuseStep 1991027 = 2986541) B2986541
theorem B1769843 : Blo 1178406 1769843 := bstep (se 1 (by rfl) ⟨1327382, by rfl⟩ : syracuseStep 1769843 = 2654765) B2654765
theorem B1180019 : Blo 1178406 1180019 := bstep (se 1 (by rfl) ⟨885014, by rfl⟩ : syracuseStep 1180019 = 1770029) B1770029
theorem B1180035 : Blo 1178406 1180035 := bstep (se 1 (by rfl) ⟨885026, by rfl⟩ : syracuseStep 1180035 = 1770053) B1770053
theorem B8069509 : Blo 1178406 8069509 := bstep (se 4 (by rfl) ⟨756516, by rfl⟩ : syracuseStep 8069509 = 1513033) B1513033
theorem B1769873 : Blo 1178406 1769873 := bstep (se 2 (by rfl) ⟨663702, by rfl⟩ : syracuseStep 1769873 = 1327405) B1327405
theorem B1180051 : Blo 1178406 1180051 := bstep (se 1 (by rfl) ⟨885038, by rfl⟩ : syracuseStep 1180051 = 1770077) B1770077
theorem B1769891 : Blo 1178406 1769891 := bstep (se 1 (by rfl) ⟨1327418, by rfl⟩ : syracuseStep 1769891 = 2654837) B2654837
theorem B1180067 : Blo 1178406 1180067 := bstep (se 1 (by rfl) ⟨885050, by rfl⟩ : syracuseStep 1180067 = 1770101) B1770101
theorem B1180083 : Blo 1178406 1180083 := bstep (se 1 (by rfl) ⟨885062, by rfl⟩ : syracuseStep 1180083 = 1770125) B1770125
theorem B1769921 : Blo 1178406 1769921 := bstep (se 2 (by rfl) ⟨663720, by rfl⟩ : syracuseStep 1769921 = 1327441) B1327441
theorem B1180099 : Blo 1178406 1180099 := bstep (se 1 (by rfl) ⟨885074, by rfl⟩ : syracuseStep 1180099 = 1770149) B1770149
theorem B1769939 : Blo 1178406 1769939 := bstep (se 1 (by rfl) ⟨1327454, by rfl⟩ : syracuseStep 1769939 = 2654909) B2654909
theorem B1180115 : Blo 1178406 1180115 := bstep (se 1 (by rfl) ⟨885086, by rfl⟩ : syracuseStep 1180115 = 1770173) B1770173
theorem B1180131 : Blo 1178406 1180131 := bstep (se 1 (by rfl) ⟨885098, by rfl⟩ : syracuseStep 1180131 = 1770197) B1770197
theorem B2834929 : Blo 1178406 2834929 := bstep (se 2 (by rfl) ⟨1063098, by rfl⟩ : syracuseStep 2834929 = 2126197) B2126197
theorem B1769969 : Blo 1178406 1769969 := bstep (se 2 (by rfl) ⟨663738, by rfl⟩ : syracuseStep 1769969 = 1327477) B1327477
theorem B1991155 : Blo 1178406 1991155 := bstep (se 1 (by rfl) ⟨1493366, by rfl⟩ : syracuseStep 1991155 = 2986733) B2986733
theorem B1327603 : Blo 1178406 1327603 := bstep (se 1 (by rfl) ⟨995702, by rfl⟩ : syracuseStep 1327603 = 1991405) B1991405
theorem B1180147 : Blo 1178406 1180147 := bstep (se 1 (by rfl) ⟨885110, by rfl⟩ : syracuseStep 1180147 = 1770221) B1770221
theorem B1769987 : Blo 1178406 1769987 := bstep (se 1 (by rfl) ⟨1327490, by rfl⟩ : syracuseStep 1769987 = 2654981) B2654981
theorem B1180163 : Blo 1178406 1180163 := bstep (se 1 (by rfl) ⟨885122, by rfl⟩ : syracuseStep 1180163 = 1770245) B1770245
theorem B1180179 : Blo 1178406 1180179 := bstep (se 1 (by rfl) ⟨885134, by rfl⟩ : syracuseStep 1180179 = 1770269) B1770269
theorem B1770017 : Blo 1178406 1770017 := bstep (se 2 (by rfl) ⟨663756, by rfl⟩ : syracuseStep 1770017 = 1327513) B1327513
theorem B1417763 : Blo 1178406 1417763 := bstep (se 1 (by rfl) ⟨1063322, by rfl⟩ : syracuseStep 1417763 = 2126645) B2126645
theorem B1180195 : Blo 1178406 1180195 := bstep (se 1 (by rfl) ⟨885146, by rfl⟩ : syracuseStep 1180195 = 1770293) B1770293
theorem B1770035 : Blo 1178406 1770035 := bstep (se 1 (by rfl) ⟨1327526, by rfl⟩ : syracuseStep 1770035 = 2655053) B2655053
theorem B1180211 : Blo 1178406 1180211 := bstep (se 1 (by rfl) ⟨885158, by rfl⟩ : syracuseStep 1180211 = 1770317) B1770317
theorem B2155075 : Blo 1178406 2155075 := bstep (se 1 (by rfl) ⟨1616306, by rfl⟩ : syracuseStep 2155075 = 3232613) B3232613
theorem B1180227 : Blo 1178406 1180227 := bstep (se 1 (by rfl) ⟨885170, by rfl⟩ : syracuseStep 1180227 = 1770341) B1770341
theorem B3981905 : Blo 1178406 3981905 := bstep (se 2 (by rfl) ⟨1493214, by rfl⟩ : syracuseStep 3981905 = 2986429) B2986429
theorem B2654801 : Blo 1178406 2654801 := bstep (se 2 (by rfl) ⟨995550, by rfl⟩ : syracuseStep 2654801 = 1991101) B1991101
theorem B1770065 : Blo 1178406 1770065 := bstep (se 2 (by rfl) ⟨663774, by rfl⟩ : syracuseStep 1770065 = 1327549) B1327549
theorem B1180243 : Blo 1178406 1180243 := bstep (se 1 (by rfl) ⟨885182, by rfl⟩ : syracuseStep 1180243 = 1770365) B1770365
theorem B2654819 : Blo 1178406 2654819 := bstep (se 1 (by rfl) ⟨1991114, by rfl⟩ : syracuseStep 2654819 = 3982229) B3982229
theorem B1770083 : Blo 1178406 1770083 := bstep (se 1 (by rfl) ⟨1327562, by rfl⟩ : syracuseStep 1770083 = 2655125) B2655125
theorem B1180259 : Blo 1178406 1180259 := bstep (se 1 (by rfl) ⟨885194, by rfl⟩ : syracuseStep 1180259 = 1770389) B1770389
theorem B1180275 : Blo 1178406 1180275 := bstep (se 1 (by rfl) ⟨885206, by rfl⟩ : syracuseStep 1180275 = 1770413) B1770413
theorem B1991297 : Blo 1178406 1991297 := bstep (se 2 (by rfl) ⟨746736, by rfl⟩ : syracuseStep 1991297 = 1493473) B1493473
theorem B1770113 : Blo 1178406 1770113 := bstep (se 2 (by rfl) ⟨663792, by rfl⟩ : syracuseStep 1770113 = 1327585) B1327585
theorem B1327747 : Blo 1178406 1327747 := bstep (se 1 (by rfl) ⟨995810, by rfl⟩ : syracuseStep 1327747 = 1991621) B1991621
theorem B1180291 : Blo 1178406 1180291 := bstep (se 1 (by rfl) ⟨885218, by rfl⟩ : syracuseStep 1180291 = 1770437) B1770437
theorem B1770131 : Blo 1178406 1770131 := bstep (se 1 (by rfl) ⟨1327598, by rfl⟩ : syracuseStep 1770131 = 2655197) B2655197
theorem B1180307 : Blo 1178406 1180307 := bstep (se 1 (by rfl) ⟨885230, by rfl⟩ : syracuseStep 1180307 = 1770461) B1770461
theorem B1180323 : Blo 1178406 1180323 := bstep (se 1 (by rfl) ⟨885242, by rfl⟩ : syracuseStep 1180323 = 1770485) B1770485
theorem B1680049 : Blo 1178406 1680049 := bstep (se 2 (by rfl) ⟨630018, by rfl⟩ : syracuseStep 1680049 = 1260037) B1260037
theorem B1491635 : Blo 1178406 1491635 := bstep (se 1 (by rfl) ⟨1118726, by rfl⟩ : syracuseStep 1491635 = 2237453) B2237453
theorem B1770161 : Blo 1178406 1770161 := bstep (se 2 (by rfl) ⟨663810, by rfl⟩ : syracuseStep 1770161 = 1327621) B1327621
theorem B3588785 : Blo 1178406 3588785 := bstep (se 2 (by rfl) ⟨1345794, by rfl⟩ : syracuseStep 3588785 = 2691589) B2691589
theorem B1180339 : Blo 1178406 1180339 := bstep (se 1 (by rfl) ⟨885254, by rfl⟩ : syracuseStep 1180339 = 1770509) B1770509
theorem B1770179 : Blo 1178406 1770179 := bstep (se 1 (by rfl) ⟨1327634, by rfl⟩ : syracuseStep 1770179 = 2655269) B2655269
theorem B1180355 : Blo 1178406 1180355 := bstep (se 1 (by rfl) ⟨885266, by rfl⟩ : syracuseStep 1180355 = 1770533) B1770533
theorem B1180371 : Blo 1178406 1180371 := bstep (se 1 (by rfl) ⟨885278, by rfl⟩ : syracuseStep 1180371 = 1770557) B1770557
theorem B1770209 : Blo 1178406 1770209 := bstep (se 2 (by rfl) ⟨663828, by rfl⟩ : syracuseStep 1770209 = 1327657) B1327657
theorem B1180387 : Blo 1178406 1180387 := bstep (se 1 (by rfl) ⟨885290, by rfl⟩ : syracuseStep 1180387 = 1770581) B1770581
theorem B1770227 : Blo 1178406 1770227 := bstep (se 1 (by rfl) ⟨1327670, by rfl⟩ : syracuseStep 1770227 = 2655341) B2655341
theorem B1180403 : Blo 1178406 1180403 := bstep (se 1 (by rfl) ⟨885302, by rfl⟩ : syracuseStep 1180403 = 1770605) B1770605
theorem B1991425 : Blo 1178406 1991425 := bstep (se 2 (by rfl) ⟨746784, by rfl⟩ : syracuseStep 1991425 = 1493569) B1493569
theorem B1770257 : Blo 1178406 1770257 := bstep (se 2 (by rfl) ⟨663846, by rfl⟩ : syracuseStep 1770257 = 1327693) B1327693
theorem B1327891 : Blo 1178406 1327891 := bstep (se 1 (by rfl) ⟨995918, by rfl⟩ : syracuseStep 1327891 = 1991837) B1991837
theorem B1991459 : Blo 1178406 1991459 := bstep (se 1 (by rfl) ⟨1493594, by rfl⟩ : syracuseStep 1991459 = 2987189) B2987189
theorem B1770275 : Blo 1178406 1770275 := bstep (se 1 (by rfl) ⟨1327706, by rfl⟩ : syracuseStep 1770275 = 2655413) B2655413
theorem B2237233 : Blo 1178406 2237233 := bstep (se 2 (by rfl) ⟨838962, by rfl⟩ : syracuseStep 2237233 = 1677925) B1677925
theorem B1770305 : Blo 1178406 1770305 := bstep (se 2 (by rfl) ⟨663864, by rfl⟩ : syracuseStep 1770305 = 1327729) B1327729
theorem B1770323 : Blo 1178406 1770323 := bstep (se 1 (by rfl) ⟨1327742, by rfl⟩ : syracuseStep 1770323 = 2655485) B2655485
theorem B2655089 : Blo 1178406 2655089 := bstep (se 2 (by rfl) ⟨995658, by rfl⟩ : syracuseStep 2655089 = 1991317) B1991317
theorem B1770353 : Blo 1178406 1770353 := bstep (se 2 (by rfl) ⟨663882, by rfl⟩ : syracuseStep 1770353 = 1327765) B1327765
theorem B2655107 : Blo 1178406 2655107 := bstep (se 1 (by rfl) ⟨1991330, by rfl⟩ : syracuseStep 2655107 = 3982661) B3982661
theorem B1770371 : Blo 1178406 1770371 := bstep (se 1 (by rfl) ⟨1327778, by rfl⟩ : syracuseStep 1770371 = 2655557) B2655557
theorem B1770401 : Blo 1178406 1770401 := bstep (se 2 (by rfl) ⟨663900, by rfl⟩ : syracuseStep 1770401 = 1327801) B1327801
theorem B1991587 : Blo 1178406 1991587 := bstep (se 1 (by rfl) ⟨1493690, by rfl⟩ : syracuseStep 1991587 = 2987381) B2987381
theorem B1770419 : Blo 1178406 1770419 := bstep (se 1 (by rfl) ⟨1327814, by rfl⟩ : syracuseStep 1770419 = 2655629) B2655629
theorem B2982865 : Blo 1178406 2982865 := bstep (se 2 (by rfl) ⟨1118574, by rfl⟩ : syracuseStep 2982865 = 2237149) B2237149
theorem B1770449 : Blo 1178406 1770449 := bstep (se 2 (by rfl) ⟨663918, by rfl⟩ : syracuseStep 1770449 = 1327837) B1327837
theorem B7554019 : Blo 1178406 7554019 := bstep (se 1 (by rfl) ⟨5665514, by rfl⟩ : syracuseStep 7554019 = 11331029) B11331029
theorem B1770467 : Blo 1178406 1770467 := bstep (se 1 (by rfl) ⟨1327850, by rfl⟩ : syracuseStep 1770467 = 2655701) B2655701
theorem B4031473 : Blo 1178406 4031473 := bstep (se 2 (by rfl) ⟨1511802, by rfl⟩ : syracuseStep 4031473 = 3023605) B3023605
theorem B1770497 : Blo 1178406 1770497 := bstep (se 2 (by rfl) ⟨663936, by rfl⟩ : syracuseStep 1770497 = 1327873) B1327873
theorem B1770515 : Blo 1178406 1770515 := bstep (se 1 (by rfl) ⟨1327886, by rfl⟩ : syracuseStep 1770515 = 2655773) B2655773
theorem B1991729 : Blo 1178406 1991729 := bstep (se 2 (by rfl) ⟨746898, by rfl⟩ : syracuseStep 1991729 = 1493797) B1493797
theorem B1770545 : Blo 1178406 1770545 := bstep (se 2 (by rfl) ⟨663954, by rfl⟩ : syracuseStep 1770545 = 1327909) B1327909
theorem B1770563 : Blo 1178406 1770563 := bstep (se 1 (by rfl) ⟨1327922, by rfl⟩ : syracuseStep 1770563 = 2655845) B2655845
theorem B3359825 : Blo 1178406 3359825 := bstep (se 2 (by rfl) ⟨1259934, by rfl⟩ : syracuseStep 3359825 = 2519869) B2519869
theorem B2016353 : Blo 1178406 2016353 := bstep (se 2 (by rfl) ⟨756132, by rfl⟩ : syracuseStep 2016353 = 1512265) B1512265
theorem B1770593 : Blo 1178406 1770593 := bstep (se 2 (by rfl) ⟨663972, by rfl⟩ : syracuseStep 1770593 = 1327945) B1327945
theorem B3982445 : Blo 1178406 3982445 := bstep (se 3 (by rfl) ⟨746708, by rfl⟩ : syracuseStep 3982445 = 1493417) B1493417
theorem B2655377 : Blo 1178406 2655377 := bstep (se 2 (by rfl) ⟨995766, by rfl⟩ : syracuseStep 2655377 = 1991533) B1991533
theorem B3982499 : Blo 1178406 3982499 := bstep (se 1 (by rfl) ⟨2986874, by rfl⟩ : syracuseStep 3982499 = 5973749) B5973749
theorem B2655395 : Blo 1178406 2655395 := bstep (se 1 (by rfl) ⟨1991546, by rfl⟩ : syracuseStep 2655395 = 3983093) B3983093
theorem B7169201 : Blo 1178406 7169201 := bstep (se 2 (by rfl) ⟨2688450, by rfl⟩ : syracuseStep 7169201 = 5376901) B5376901
theorem B1991857 : Blo 1178406 1991857 := bstep (se 2 (by rfl) ⟨746946, by rfl⟩ : syracuseStep 1991857 = 1493893) B1493893
theorem B2237635 : Blo 1178406 2237635 := bstep (se 1 (by rfl) ⟨1678226, by rfl⟩ : syracuseStep 2237635 = 3356453) B3356453
theorem B1991891 : Blo 1178406 1991891 := bstep (se 1 (by rfl) ⟨1493918, by rfl⟩ : syracuseStep 1991891 = 2987837) B2987837
theorem B2983139 : Blo 1178406 2983139 := bstep (se 1 (by rfl) ⟨2237354, by rfl⟩ : syracuseStep 2983139 = 4474709) B4474709
theorem B2237681 : Blo 1178406 2237681 := bstep (se 2 (by rfl) ⟨839130, by rfl⟩ : syracuseStep 2237681 = 1678261) B1678261
theorem B3228931 : Blo 1178406 3228931 := bstep (se 1 (by rfl) ⟨2421698, by rfl⟩ : syracuseStep 3228931 = 4843397) B4843397
theorem B2688323 : Blo 1178406 2688323 := bstep (se 1 (by rfl) ⟨2016242, by rfl⟩ : syracuseStep 2688323 = 4032485) B4032485
theorem B8504675 : Blo 1178406 8504675 := bstep (se 1 (by rfl) ⟨6378506, by rfl⟩ : syracuseStep 8504675 = 12757013) B12757013
theorem B1492339 : Blo 1178406 1492339 := bstep (se 1 (by rfl) ⟨1119254, by rfl⟩ : syracuseStep 1492339 = 2238509) B2238509
theorem B2983331 : Blo 1178406 2983331 := bstep (se 1 (by rfl) ⟨2237498, by rfl⟩ : syracuseStep 2983331 = 4474997) B4474997
theorem B5973425 : Blo 1178406 5973425 := bstep (se 2 (by rfl) ⟨2240034, by rfl⟩ : syracuseStep 5973425 = 4480069) B4480069
theorem B3982769 : Blo 1178406 3982769 := bstep (se 2 (by rfl) ⟨1493538, by rfl⟩ : syracuseStep 3982769 = 2987077) B2987077
theorem B2655665 : Blo 1178406 2655665 := bstep (se 2 (by rfl) ⟨995874, by rfl⟩ : syracuseStep 2655665 = 1991749) B1991749
theorem B2655683 : Blo 1178406 2655683 := bstep (se 1 (by rfl) ⟨1991762, by rfl⟩ : syracuseStep 2655683 = 3983525) B3983525
theorem B3777997 : Blo 1178406 3777997 := bstep (se 3 (by rfl) ⟨708374, by rfl⟩ : syracuseStep 3777997 = 1416749) B1416749
theorem B1492435 : Blo 1178406 1492435 := bstep (se 1 (by rfl) ⟨1119326, by rfl⟩ : syracuseStep 1492435 = 2238653) B2238653
theorem B2237969 : Blo 1178406 2237969 := bstep (se 2 (by rfl) ⟨839238, by rfl⟩ : syracuseStep 2237969 = 1678477) B1678477
theorem B12748357 : Blo 1178406 12748357 := bstep (se 4 (by rfl) ⟨1195158, by rfl⟩ : syracuseStep 12748357 = 2390317) B2390317
theorem B5375587 : Blo 1178406 5375587 := bstep (se 1 (by rfl) ⟨4031690, by rfl⟩ : syracuseStep 5375587 = 8063381) B8063381
theorem B2016995 : Blo 1178406 2016995 := bstep (se 1 (by rfl) ⟨1512746, by rfl⟩ : syracuseStep 2016995 = 3025493) B3025493
theorem B4540195 : Blo 1178406 4540195 := bstep (se 1 (by rfl) ⟨3405146, by rfl⟩ : syracuseStep 4540195 = 6810293) B6810293
theorem B4474723 : Blo 1178406 4474723 := bstep (se 1 (by rfl) ⟨3356042, by rfl⟩ : syracuseStep 4474723 = 6712085) B6712085
theorem B1492931 : Blo 1178406 1492931 := bstep (se 1 (by rfl) ⟨1119698, by rfl⟩ : syracuseStep 1492931 = 2239397) B2239397
theorem B3983309 : Blo 1178406 3983309 := bstep (se 3 (by rfl) ⟨746870, by rfl⟩ : syracuseStep 3983309 = 1493741) B1493741
theorem B3983363 : Blo 1178406 3983363 := bstep (se 1 (by rfl) ⟨2987522, by rfl⟩ : syracuseStep 3983363 = 5975045) B5975045
theorem B3360781 : Blo 1178406 3360781 := bstep (se 3 (by rfl) ⟨630146, by rfl⟩ : syracuseStep 3360781 = 1260293) B1260293
theorem B6719557 : Blo 1178406 6719557 := bstep (se 4 (by rfl) ⟨629958, by rfl⟩ : syracuseStep 6719557 = 1259917) B1259917
theorem B2517169 : Blo 1178406 2517169 := bstep (se 2 (by rfl) ⟨943938, by rfl⟩ : syracuseStep 2517169 = 1887877) B1887877
theorem B2238691 : Blo 1178406 2238691 := bstep (se 1 (by rfl) ⟨1679018, by rfl⟩ : syracuseStep 2238691 = 3358037) B3358037
theorem B3361009 : Blo 1178406 3361009 := bstep (se 2 (by rfl) ⟨1260378, by rfl⟩ : syracuseStep 3361009 = 2520757) B2520757
theorem B3778829 : Blo 1178406 3778829 := bstep (se 3 (by rfl) ⟨708530, by rfl⟩ : syracuseStep 3778829 = 1417061) B1417061
theorem B3983633 : Blo 1178406 3983633 := bstep (se 2 (by rfl) ⟨1493862, by rfl⟩ : syracuseStep 3983633 = 2987725) B2987725
theorem B16132405 : Blo 1178406 16132405 := bstep (se 5 (by rfl) ⟨756206, by rfl⟩ : syracuseStep 16132405 = 1512413) B1512413
theorem B2984273 : Blo 1178406 2984273 := bstep (se 2 (by rfl) ⟨1119102, by rfl⟩ : syracuseStep 2984273 = 2238205) B2238205
theorem B13805923 : Blo 1178406 13805923 := bstep (se 1 (by rfl) ⟨10354442, by rfl⟩ : syracuseStep 13805923 = 20708885) B20708885
theorem B2984323 : Blo 1178406 2984323 := bstep (se 1 (by rfl) ⟨2238242, by rfl⟩ : syracuseStep 2984323 = 4476485) B4476485
theorem B3361169 : Blo 1178406 3361169 := bstep (se 2 (by rfl) ⟨1260438, by rfl⟩ : syracuseStep 3361169 = 2520877) B2520877
theorem B5040625 : Blo 1178406 5040625 := bstep (se 2 (by rfl) ⟨1890234, by rfl⟩ : syracuseStep 5040625 = 3780469) B3780469
theorem B3361283 : Blo 1178406 3361283 := bstep (se 1 (by rfl) ⟨2520962, by rfl⟩ : syracuseStep 3361283 = 5041925) B5041925
theorem B7170565 : Blo 1178406 7170565 := bstep (se 4 (by rfl) ⟨672240, by rfl⟩ : syracuseStep 7170565 = 1344481) B1344481
theorem B2984465 : Blo 1178406 2984465 := bstep (se 2 (by rfl) ⟨1119174, by rfl⟩ : syracuseStep 2984465 = 2238349) B2238349
theorem B2517571 : Blo 1178406 2517571 := bstep (se 1 (by rfl) ⟨1888178, by rfl⟩ : syracuseStep 2517571 = 3776357) B3776357
theorem B10078789 : Blo 1178406 10078789 := bstep (se 4 (by rfl) ⟨944886, by rfl⟩ : syracuseStep 10078789 = 1889773) B1889773
theorem B1493635 : Blo 1178406 1493635 := bstep (se 1 (by rfl) ⟨1120226, by rfl⟩ : syracuseStep 1493635 = 2240453) B2240453
theorem B2239139 : Blo 1178406 2239139 := bstep (se 1 (by rfl) ⟨1679354, by rfl⟩ : syracuseStep 2239139 = 3358709) B3358709
theorem B11340485 : Blo 1178406 11340485 := bstep (se 4 (by rfl) ⟨1063170, by rfl⟩ : syracuseStep 11340485 = 2126341) B2126341
theorem B1493731 : Blo 1178406 1493731 := bstep (se 1 (by rfl) ⟨1120298, by rfl⟩ : syracuseStep 1493731 = 2240597) B2240597
theorem B5974883 : Blo 1178406 5974883 := bstep (se 1 (by rfl) ⟨4481162, by rfl⟩ : syracuseStep 5974883 = 8962325) B8962325
theorem B7556017 : Blo 1178406 7556017 := bstep (se 2 (by rfl) ⟨2833506, by rfl⟩ : syracuseStep 7556017 = 5667013) B5667013
theorem B2239427 : Blo 1178406 2239427 := bstep (se 1 (by rfl) ⟨1679570, by rfl⟩ : syracuseStep 2239427 = 3359141) B3359141
theorem B4090861 : Blo 1178406 4090861 := bstep (se 3 (by rfl) ⟨767036, by rfl⟩ : syracuseStep 4090861 = 1534073) B1534073
theorem B2124785 : Blo 1178406 2124785 := bstep (se 2 (by rfl) ⟨796794, by rfl⟩ : syracuseStep 2124785 = 1593589) B1593589
theorem B6057059 : Blo 1178406 6057059 := bstep (se 1 (by rfl) ⟨4542794, by rfl⟩ : syracuseStep 6057059 = 9085589) B9085589
theorem B2985457 : Blo 1178406 2985457 := bstep (se 2 (by rfl) ⟨1119546, by rfl⟩ : syracuseStep 2985457 = 2239093) B2239093
theorem B9080419 : Blo 1178406 9080419 := bstep (se 1 (by rfl) ⟨6810314, by rfl⟩ : syracuseStep 9080419 = 13620629) B13620629
theorem B5975693 : Blo 1178406 5975693 := bstep (se 3 (by rfl) ⟨1120442, by rfl⟩ : syracuseStep 5975693 = 2240885) B2240885
theorem B1887923 : Blo 1178406 1887923 := bstep (se 1 (by rfl) ⟨1415942, by rfl⟩ : syracuseStep 1887923 = 2831885) B2831885
theorem B2043571 : Blo 1178406 2043571 := bstep (se 1 (by rfl) ⟨1532678, by rfl⟩ : syracuseStep 2043571 = 3065357) B3065357
theorem B5746403 : Blo 1178406 5746403 := bstep (se 1 (by rfl) ⟨4309802, by rfl⟩ : syracuseStep 5746403 = 8619605) B8619605
theorem B1593091 : Blo 1178406 1593091 := bstep (se 1 (by rfl) ⟨1194818, by rfl⟩ : syracuseStep 1593091 = 2389637) B2389637
theorem B2985731 : Blo 1178406 2985731 := bstep (se 1 (by rfl) ⟨2239298, by rfl⟩ : syracuseStep 2985731 = 4478597) B4478597
theorem B4034317 : Blo 1178406 4034317 := bstep (se 3 (by rfl) ⟨756434, by rfl⟩ : syracuseStep 4034317 = 1512869) B1512869
theorem B2125649 : Blo 1178406 2125649 := bstep (se 2 (by rfl) ⟨797118, by rfl⟩ : syracuseStep 2125649 = 1594237) B1594237
theorem B2240369 : Blo 1178406 2240369 := bstep (se 2 (by rfl) ⟨840138, by rfl⟩ : syracuseStep 2240369 = 1680277) B1680277
theorem B1593281 : Blo 1178406 1593281 := bstep (se 2 (by rfl) ⟨597480, by rfl⟩ : syracuseStep 1593281 = 1194961) B1194961
theorem B2985923 : Blo 1178406 2985923 := bstep (se 1 (by rfl) ⟨2239442, by rfl⟩ : syracuseStep 2985923 = 4478885) B4478885
theorem B6721541 : Blo 1178406 6721541 := bstep (se 4 (by rfl) ⟨630144, by rfl⟩ : syracuseStep 6721541 = 1260289) B1260289
theorem B4476941 : Blo 1178406 4476941 := bstep (se 3 (by rfl) ⟨839426, by rfl⟩ : syracuseStep 4476941 = 1678853) B1678853
theorem B2519075 : Blo 1178406 2519075 := bstep (se 1 (by rfl) ⟨1889306, by rfl⟩ : syracuseStep 2519075 = 3778613) B3778613
theorem B3977261 : Blo 1178406 3977261 := bstep (se 3 (by rfl) ⟨745736, by rfl⟩ : syracuseStep 3977261 = 1491473) B1491473
theorem B7270469 : Blo 1178406 7270469 := bstep (se 4 (by rfl) ⟨681606, by rfl⟩ : syracuseStep 7270469 = 1363213) B1363213
theorem B3977315 : Blo 1178406 3977315 := bstep (se 1 (by rfl) ⟨2982986, by rfl⟩ : syracuseStep 3977315 = 5965973) B5965973
theorem B3780931 : Blo 1178406 3780931 := bstep (se 1 (by rfl) ⟨2835698, by rfl⟩ : syracuseStep 3780931 = 5671397) B5671397
theorem B1593697 : Blo 1178406 1593697 := bstep (se 2 (by rfl) ⟨597636, by rfl⟩ : syracuseStep 1593697 = 1195273) B1195273
theorem B3977585 : Blo 1178406 3977585 := bstep (se 2 (by rfl) ⟨1491594, by rfl⟩ : syracuseStep 3977585 = 2983189) B2983189
theorem B5968241 : Blo 1178406 5968241 := bstep (se 2 (by rfl) ⟨2238090, by rfl⟩ : syracuseStep 5968241 = 4476181) B4476181
theorem B3232145 : Blo 1178406 3232145 := bstep (se 2 (by rfl) ⟨1212054, by rfl⟩ : syracuseStep 3232145 = 2424109) B2424109
theorem B3781073 : Blo 1178406 3781073 := bstep (se 2 (by rfl) ⟨1417902, by rfl⟩ : syracuseStep 3781073 = 2835805) B2835805
theorem B8507875 : Blo 1178406 8507875 := bstep (se 1 (by rfl) ⟨6380906, by rfl⟩ : syracuseStep 8507875 = 12761813) B12761813
theorem B5034595 : Blo 1178406 5034595 := bstep (se 1 (by rfl) ⟨3775946, by rfl⟩ : syracuseStep 5034595 = 7551893) B7551893
theorem B13628017 : Blo 1178406 13628017 := bstep (se 2 (by rfl) ⟨5110506, by rfl⟩ : syracuseStep 13628017 = 10221013) B10221013
theorem B1888915 : Blo 1178406 1888915 := bstep (se 1 (by rfl) ⟨1416686, by rfl⟩ : syracuseStep 1888915 = 2833373) B2833373
theorem B13439843 : Blo 1178406 13439843 := bstep (se 1 (by rfl) ⟨10079882, by rfl⟩ : syracuseStep 13439843 = 20159765) B20159765
theorem B2986865 : Blo 1178406 2986865 := bstep (se 2 (by rfl) ⟨1120074, by rfl⟩ : syracuseStep 2986865 = 2240149) B2240149
theorem B1889153 : Blo 1178406 1889153 := bstep (se 2 (by rfl) ⟨708432, by rfl⟩ : syracuseStep 1889153 = 1416865) B1416865
theorem B3978125 : Blo 1178406 3978125 := bstep (se 3 (by rfl) ⟨745898, by rfl⟩ : syracuseStep 3978125 = 1491797) B1491797
theorem B2986915 : Blo 1178406 2986915 := bstep (se 1 (by rfl) ⟨2240186, by rfl⟩ : syracuseStep 2986915 = 4480373) B4480373
theorem B3978179 : Blo 1178406 3978179 := bstep (se 1 (by rfl) ⟨2983634, by rfl⟩ : syracuseStep 3978179 = 5967269) B5967269
theorem B2987057 : Blo 1178406 2987057 := bstep (se 2 (by rfl) ⟨1120146, by rfl⟩ : syracuseStep 2987057 = 2240293) B2240293
theorem B1889363 : Blo 1178406 1889363 := bstep (se 1 (by rfl) ⟨1417022, by rfl⟩ : syracuseStep 1889363 = 2834045) B2834045
theorem B6804593 : Blo 1178406 6804593 := bstep (se 2 (by rfl) ⟨2551722, by rfl⟩ : syracuseStep 6804593 = 5103445) B5103445
theorem B2364547 : Blo 1178406 2364547 := bstep (se 1 (by rfl) ⟨1773410, by rfl⟩ : syracuseStep 2364547 = 3546821) B3546821
theorem B3355793 : Blo 1178406 3355793 := bstep (se 2 (by rfl) ⟨1258422, by rfl⟩ : syracuseStep 3355793 = 2516845) B2516845
theorem B6378659 : Blo 1178406 6378659 := bstep (se 1 (by rfl) ⟨4783994, by rfl⟩ : syracuseStep 6378659 = 9567989) B9567989
theorem B3232931 : Blo 1178406 3232931 := bstep (se 1 (by rfl) ⟨2424698, by rfl⟩ : syracuseStep 3232931 = 4849397) B4849397
theorem B3978449 : Blo 1178406 3978449 := bstep (se 2 (by rfl) ⟨1491918, by rfl⟩ : syracuseStep 3978449 = 2983837) B2983837
theorem B2520305 : Blo 1178406 2520305 := bstep (se 2 (by rfl) ⟨945114, by rfl⟩ : syracuseStep 2520305 = 1890229) B1890229
theorem B3585379 : Blo 1178406 3585379 := bstep (se 1 (by rfl) ⟨2689034, by rfl⟩ : syracuseStep 3585379 = 5378069) B5378069
theorem B2045345 : Blo 1178406 2045345 := bstep (se 2 (by rfl) ⟨767004, by rfl⟩ : syracuseStep 2045345 = 1534009) B1534009
theorem B2725315 : Blo 1178406 2725315 := bstep (se 1 (by rfl) ⟨2043986, by rfl⟩ : syracuseStep 2725315 = 4087973) B4087973
theorem B2389475 : Blo 1178406 2389475 := bstep (se 1 (by rfl) ⟨1792106, by rfl⟩ : syracuseStep 2389475 = 3584213) B3584213
theorem B2651633 : Blo 1178406 2651633 := bstep (se 2 (by rfl) ⟨994362, by rfl⟩ : syracuseStep 2651633 = 1988725) B1988725
theorem B2651651 : Blo 1178406 2651651 := bstep (se 1 (by rfl) ⟨1988738, by rfl⟩ : syracuseStep 2651651 = 3977477) B3977477
theorem B1259059 : Blo 1178406 1259059 := bstep (se 1 (by rfl) ⟨944294, by rfl⟩ : syracuseStep 1259059 = 1888589) B1888589
theorem B5666381 : Blo 1178406 5666381 := bstep (se 3 (by rfl) ⟨1062446, by rfl⟩ : syracuseStep 5666381 = 2124893) B2124893
theorem B19142257 : Blo 1178406 19142257 := bstep (se 2 (by rfl) ⟨7178346, by rfl⟩ : syracuseStep 19142257 = 14356693) B14356693
theorem B3978989 : Blo 1178406 3978989 := bstep (se 3 (by rfl) ⟨746060, by rfl⟩ : syracuseStep 3978989 = 1492121) B1492121
theorem B2651921 : Blo 1178406 2651921 := bstep (se 2 (by rfl) ⟨994470, by rfl⟩ : syracuseStep 2651921 = 1988941) B1988941
theorem B2651939 : Blo 1178406 2651939 := bstep (se 1 (by rfl) ⟨1988954, by rfl⟩ : syracuseStep 2651939 = 3977909) B3977909
theorem B3979043 : Blo 1178406 3979043 := bstep (se 1 (by rfl) ⟨2984282, by rfl⟩ : syracuseStep 3979043 = 5968565) B5968565
theorem B5969699 : Blo 1178406 5969699 := bstep (se 1 (by rfl) ⟨4477274, by rfl⟩ : syracuseStep 5969699 = 8954549) B8954549
theorem B1890145 : Blo 1178406 1890145 := bstep (se 2 (by rfl) ⟨708804, by rfl⟩ : syracuseStep 1890145 = 1417609) B1417609
theorem B10213219 : Blo 1178406 10213219 := bstep (se 1 (by rfl) ⟨7659914, by rfl⟩ : syracuseStep 10213219 = 15319829) B15319829
theorem B3356579 : Blo 1178406 3356579 := bstep (se 1 (by rfl) ⟨2517434, by rfl⟩ : syracuseStep 3356579 = 5034869) B5034869
theorem B2873297 : Blo 1178406 2873297 := bstep (se 2 (by rfl) ⟨1077486, by rfl⟩ : syracuseStep 2873297 = 2154973) B2154973
theorem B1988563 : Blo 1178406 1988563 := bstep (se 1 (by rfl) ⟨1491422, by rfl⟩ : syracuseStep 1988563 = 2982845) B2982845
theorem B5109745 : Blo 1178406 5109745 := bstep (se 2 (by rfl) ⟨1916154, by rfl⟩ : syracuseStep 5109745 = 3832309) B3832309
theorem B1259507 : Blo 1178406 1259507 := bstep (se 1 (by rfl) ⟨944630, by rfl⟩ : syracuseStep 1259507 = 1889261) B1889261
theorem B2652209 : Blo 1178406 2652209 := bstep (se 2 (by rfl) ⟨994578, by rfl⟩ : syracuseStep 2652209 = 1989157) B1989157
theorem B3979313 : Blo 1178406 3979313 := bstep (se 2 (by rfl) ⟨1492242, by rfl⟩ : syracuseStep 3979313 = 2984485) B2984485
theorem B2652227 : Blo 1178406 2652227 := bstep (se 1 (by rfl) ⟨1989170, by rfl⟩ : syracuseStep 2652227 = 3978341) B3978341
theorem B1988705 : Blo 1178406 1988705 := bstep (se 2 (by rfl) ⟨745764, by rfl⟩ : syracuseStep 1988705 = 1491529) B1491529
theorem B2554001 : Blo 1178406 2554001 := bstep (se 2 (by rfl) ⟨957750, by rfl⟩ : syracuseStep 2554001 = 1915501) B1915501
theorem B1767617 : Blo 1178406 1767617 := bstep (se 2 (by rfl) ⟨662856, by rfl⟩ : syracuseStep 1767617 = 1325713) B1325713
theorem B1767635 : Blo 1178406 1767635 := bstep (se 1 (by rfl) ⟨1325726, by rfl⟩ : syracuseStep 1767635 = 2651453) B2651453
theorem B1988833 : Blo 1178406 1988833 := bstep (se 2 (by rfl) ⟨745812, by rfl⟩ : syracuseStep 1988833 = 1491625) B1491625
theorem B3356909 : Blo 1178406 3356909 := bstep (se 3 (by rfl) ⟨629420, by rfl⟩ : syracuseStep 3356909 = 1258841) B1258841
theorem B1767665 : Blo 1178406 1767665 := bstep (se 2 (by rfl) ⟨662874, by rfl⟩ : syracuseStep 1767665 = 1325749) B1325749
theorem B16152817 : Blo 1178406 16152817 := bstep (se 2 (by rfl) ⟨6057306, by rfl⟩ : syracuseStep 16152817 = 12114613) B12114613
theorem B1767683 : Blo 1178406 1767683 := bstep (se 1 (by rfl) ⟨1325762, by rfl⟩ : syracuseStep 1767683 = 2651525) B2651525
theorem B1988867 : Blo 1178406 1988867 := bstep (se 1 (by rfl) ⟨1491650, by rfl⟩ : syracuseStep 1988867 = 2983301) B2983301
theorem B1767713 : Blo 1178406 1767713 := bstep (se 2 (by rfl) ⟨662892, by rfl⟩ : syracuseStep 1767713 = 1325785) B1325785
theorem B3356977 : Blo 1178406 3356977 := bstep (se 2 (by rfl) ⟨1258866, by rfl⟩ : syracuseStep 3356977 = 2517733) B2517733
theorem B1767731 : Blo 1178406 1767731 := bstep (se 1 (by rfl) ⟨1325798, by rfl⟩ : syracuseStep 1767731 = 2651597) B2651597
theorem B7551301 : Blo 1178406 7551301 := bstep (se 4 (by rfl) ⟨707934, by rfl⟩ : syracuseStep 7551301 = 1415869) B1415869
theorem B1767761 : Blo 1178406 1767761 := bstep (se 2 (by rfl) ⟨662910, by rfl⟩ : syracuseStep 1767761 = 1325821) B1325821
theorem B2652497 : Blo 1178406 2652497 := bstep (se 2 (by rfl) ⟨994686, by rfl⟩ : syracuseStep 2652497 = 1989373) B1989373
theorem B1767779 : Blo 1178406 1767779 := bstep (se 1 (by rfl) ⟨1325834, by rfl⟩ : syracuseStep 1767779 = 2651669) B2651669
theorem B2652515 : Blo 1178406 2652515 := bstep (se 1 (by rfl) ⟨1989386, by rfl⟩ : syracuseStep 2652515 = 3978773) B3978773
theorem B1767809 : Blo 1178406 1767809 := bstep (se 2 (by rfl) ⟨662928, by rfl⟩ : syracuseStep 1767809 = 1325857) B1325857
theorem B1988995 : Blo 1178406 1988995 := bstep (se 1 (by rfl) ⟨1491746, by rfl⟩ : syracuseStep 1988995 = 2983493) B2983493
theorem B1767827 : Blo 1178406 1767827 := bstep (se 1 (by rfl) ⟨1325870, by rfl⟩ : syracuseStep 1767827 = 2651741) B2651741
theorem B1767857 : Blo 1178406 1767857 := bstep (se 2 (by rfl) ⟨662946, by rfl⟩ : syracuseStep 1767857 = 1325893) B1325893
theorem B1767875 : Blo 1178406 1767875 := bstep (se 1 (by rfl) ⟨1325906, by rfl⟩ : syracuseStep 1767875 = 2651813) B2651813
theorem B1767905 : Blo 1178406 1767905 := bstep (se 2 (by rfl) ⟨662964, by rfl⟩ : syracuseStep 1767905 = 1325929) B1325929
theorem B1767923 : Blo 1178406 1767923 := bstep (se 1 (by rfl) ⟨1325942, by rfl⟩ : syracuseStep 1767923 = 2651885) B2651885
theorem B1767953 : Blo 1178406 1767953 := bstep (se 2 (by rfl) ⟨662982, by rfl⟩ : syracuseStep 1767953 = 1325965) B1325965
theorem B1989137 : Blo 1178406 1989137 := bstep (se 2 (by rfl) ⟨745926, by rfl⟩ : syracuseStep 1989137 = 1491853) B1491853
theorem B1767971 : Blo 1178406 1767971 := bstep (se 1 (by rfl) ⟨1325978, by rfl⟩ : syracuseStep 1767971 = 2651957) B2651957
theorem B4037165 : Blo 1178406 4037165 := bstep (se 3 (by rfl) ⟨756968, by rfl⟩ : syracuseStep 4037165 = 1513937) B1513937
theorem B5036593 : Blo 1178406 5036593 := bstep (se 2 (by rfl) ⟨1888722, by rfl⟩ : syracuseStep 5036593 = 3777445) B3777445
theorem B1768001 : Blo 1178406 1768001 := bstep (se 2 (by rfl) ⟨663000, by rfl⟩ : syracuseStep 1768001 = 1326001) B1326001
theorem B3357251 : Blo 1178406 3357251 := bstep (se 1 (by rfl) ⟨2517938, by rfl⟩ : syracuseStep 3357251 = 5035877) B5035877
theorem B3979853 : Blo 1178406 3979853 := bstep (se 3 (by rfl) ⟨746222, by rfl⟩ : syracuseStep 3979853 = 1492445) B1492445
theorem B5970509 : Blo 1178406 5970509 := bstep (se 3 (by rfl) ⟨1119470, by rfl⟩ : syracuseStep 5970509 = 2238941) B2238941
theorem B1768019 : Blo 1178406 1768019 := bstep (se 1 (by rfl) ⟨1326014, by rfl⟩ : syracuseStep 1768019 = 2652029) B2652029
theorem B1768049 : Blo 1178406 1768049 := bstep (se 2 (by rfl) ⟨663018, by rfl⟩ : syracuseStep 1768049 = 1326037) B1326037
theorem B2652785 : Blo 1178406 2652785 := bstep (se 2 (by rfl) ⟨994794, by rfl⟩ : syracuseStep 2652785 = 1989589) B1989589
theorem B1677953 : Blo 1178406 1677953 := bstep (se 2 (by rfl) ⟨629232, by rfl⟩ : syracuseStep 1677953 = 1258465) B1258465
theorem B1768067 : Blo 1178406 1768067 := bstep (se 1 (by rfl) ⟨1326050, by rfl⟩ : syracuseStep 1768067 = 2652101) B2652101
theorem B2652803 : Blo 1178406 2652803 := bstep (se 1 (by rfl) ⟨1989602, by rfl⟩ : syracuseStep 2652803 = 3979205) B3979205
theorem B3979907 : Blo 1178406 3979907 := bstep (se 1 (by rfl) ⟨2984930, by rfl⟩ : syracuseStep 3979907 = 5969861) B5969861
theorem B1989265 : Blo 1178406 1989265 := bstep (se 2 (by rfl) ⟨745974, by rfl⟩ : syracuseStep 1989265 = 1491949) B1491949
theorem B1768097 : Blo 1178406 1768097 := bstep (se 2 (by rfl) ⟨663036, by rfl⟩ : syracuseStep 1768097 = 1326073) B1326073
theorem B1325731 : Blo 1178406 1325731 := bstep (se 1 (by rfl) ⟨994298, by rfl⟩ : syracuseStep 1325731 = 1988597) B1988597
theorem B1768115 : Blo 1178406 1768115 := bstep (se 1 (by rfl) ⟨1326086, by rfl⟩ : syracuseStep 1768115 = 2652173) B2652173
theorem B1989299 : Blo 1178406 1989299 := bstep (se 1 (by rfl) ⟨1491974, by rfl⟩ : syracuseStep 1989299 = 2983949) B2983949
theorem B1678033 : Blo 1178406 1678033 := bstep (se 2 (by rfl) ⟨629262, by rfl⟩ : syracuseStep 1678033 = 1258525) B1258525
theorem B1768145 : Blo 1178406 1768145 := bstep (se 2 (by rfl) ⟨663054, by rfl⟩ : syracuseStep 1768145 = 1326109) B1326109
theorem B1768163 : Blo 1178406 1768163 := bstep (se 1 (by rfl) ⟨1326122, by rfl⟩ : syracuseStep 1768163 = 2652245) B2652245
theorem B1768193 : Blo 1178406 1768193 := bstep (se 2 (by rfl) ⟨663072, by rfl⟩ : syracuseStep 1768193 = 1326145) B1326145
theorem B1768211 : Blo 1178406 1768211 := bstep (se 1 (by rfl) ⟨1326158, by rfl⟩ : syracuseStep 1768211 = 2652317) B2652317
theorem B1768241 : Blo 1178406 1768241 := bstep (se 2 (by rfl) ⟨663090, by rfl⟩ : syracuseStep 1768241 = 1326181) B1326181
theorem B1178419 : Blo 1178406 1178419 := bstep (se 1 (by rfl) ⟨883814, by rfl⟩ : syracuseStep 1178419 = 1767629) B1767629
theorem B1325875 : Blo 1178406 1325875 := bstep (se 1 (by rfl) ⟨994406, by rfl⟩ : syracuseStep 1325875 = 1988813) B1988813
theorem B1989427 : Blo 1178406 1989427 := bstep (se 1 (by rfl) ⟨1492070, by rfl⟩ : syracuseStep 1989427 = 2984141) B2984141
theorem B1178435 : Blo 1178406 1178435 := bstep (se 1 (by rfl) ⟨883826, by rfl⟩ : syracuseStep 1178435 = 1767653) B1767653
theorem B1768259 : Blo 1178406 1768259 := bstep (se 1 (by rfl) ⟨1326194, by rfl⟩ : syracuseStep 1768259 = 2652389) B2652389
theorem B1792835 : Blo 1178406 1792835 := bstep (se 1 (by rfl) ⟨1344626, by rfl⟩ : syracuseStep 1792835 = 2689253) B2689253
theorem B1178451 : Blo 1178406 1178451 := bstep (se 1 (by rfl) ⟨883838, by rfl⟩ : syracuseStep 1178451 = 1767677) B1767677
theorem B1768289 : Blo 1178406 1768289 := bstep (se 2 (by rfl) ⟨663108, by rfl⟩ : syracuseStep 1768289 = 1326217) B1326217
theorem B1178467 : Blo 1178406 1178467 := bstep (se 1 (by rfl) ⟨883850, by rfl⟩ : syracuseStep 1178467 = 1767701) B1767701
theorem B8960867 : Blo 1178406 8960867 := bstep (se 1 (by rfl) ⟨6720650, by rfl⟩ : syracuseStep 8960867 = 13441301) B13441301
theorem B4479857 : Blo 1178406 4479857 := bstep (se 2 (by rfl) ⟨1679946, by rfl⟩ : syracuseStep 4479857 = 3359893) B3359893
theorem B1178483 : Blo 1178406 1178483 := bstep (se 1 (by rfl) ⟨883862, by rfl⟩ : syracuseStep 1178483 = 1767725) B1767725
theorem B1768307 : Blo 1178406 1768307 := bstep (se 1 (by rfl) ⟨1326230, by rfl⟩ : syracuseStep 1768307 = 2652461) B2652461
theorem B1178499 : Blo 1178406 1178499 := bstep (se 1 (by rfl) ⟨883874, by rfl⟩ : syracuseStep 1178499 = 1767749) B1767749
theorem B1768337 : Blo 1178406 1768337 := bstep (se 2 (by rfl) ⟨663126, by rfl⟩ : syracuseStep 1768337 = 1326253) B1326253
theorem B2653073 : Blo 1178406 2653073 := bstep (se 2 (by rfl) ⟨994902, by rfl⟩ : syracuseStep 2653073 = 1989805) B1989805
theorem B1178515 : Blo 1178406 1178515 := bstep (se 1 (by rfl) ⟨883886, by rfl⟩ : syracuseStep 1178515 = 1767773) B1767773
theorem B3980177 : Blo 1178406 3980177 := bstep (se 2 (by rfl) ⟨1492566, by rfl⟩ : syracuseStep 3980177 = 2985133) B2985133
theorem B1178531 : Blo 1178406 1178531 := bstep (se 1 (by rfl) ⟨883898, by rfl⟩ : syracuseStep 1178531 = 1767797) B1767797
theorem B1768355 : Blo 1178406 1768355 := bstep (se 1 (by rfl) ⟨1326266, by rfl⟩ : syracuseStep 1768355 = 2652533) B2652533
theorem B2653091 : Blo 1178406 2653091 := bstep (se 1 (by rfl) ⟨1989818, by rfl⟩ : syracuseStep 2653091 = 3979637) B3979637
theorem B1178547 : Blo 1178406 1178547 := bstep (se 1 (by rfl) ⟨883910, by rfl⟩ : syracuseStep 1178547 = 1767821) B1767821
theorem B1768385 : Blo 1178406 1768385 := bstep (se 2 (by rfl) ⟨663144, by rfl⟩ : syracuseStep 1768385 = 1326289) B1326289
theorem B1989569 : Blo 1178406 1989569 := bstep (se 2 (by rfl) ⟨746088, by rfl⟩ : syracuseStep 1989569 = 1492177) B1492177
theorem B1178563 : Blo 1178406 1178563 := bstep (se 1 (by rfl) ⟨883922, by rfl⟩ : syracuseStep 1178563 = 1767845) B1767845
theorem B1326019 : Blo 1178406 1326019 := bstep (se 1 (by rfl) ⟨994514, by rfl⟩ : syracuseStep 1326019 = 1989029) B1989029
theorem B1178579 : Blo 1178406 1178579 := bstep (se 1 (by rfl) ⟨883934, by rfl⟩ : syracuseStep 1178579 = 1767869) B1767869
theorem B1768403 : Blo 1178406 1768403 := bstep (se 1 (by rfl) ⟨1326302, by rfl⟩ : syracuseStep 1768403 = 2652605) B2652605
theorem B1178595 : Blo 1178406 1178595 := bstep (se 1 (by rfl) ⟨883946, by rfl⟩ : syracuseStep 1178595 = 1767893) B1767893
theorem B1768433 : Blo 1178406 1768433 := bstep (se 2 (by rfl) ⟨663162, by rfl⟩ : syracuseStep 1768433 = 1326325) B1326325
theorem B1178611 : Blo 1178406 1178611 := bstep (se 1 (by rfl) ⟨883958, by rfl⟩ : syracuseStep 1178611 = 1767917) B1767917
theorem B1178627 : Blo 1178406 1178627 := bstep (se 1 (by rfl) ⟨883970, by rfl⟩ : syracuseStep 1178627 = 1767941) B1767941
theorem B1768451 : Blo 1178406 1768451 := bstep (se 1 (by rfl) ⟨1326338, by rfl⟩ : syracuseStep 1768451 = 2652677) B2652677
theorem B1178643 : Blo 1178406 1178643 := bstep (se 1 (by rfl) ⟨883982, by rfl⟩ : syracuseStep 1178643 = 1767965) B1767965
theorem B1768481 : Blo 1178406 1768481 := bstep (se 2 (by rfl) ⟨663180, by rfl⟩ : syracuseStep 1768481 = 1326361) B1326361
theorem B1178659 : Blo 1178406 1178659 := bstep (se 1 (by rfl) ⟨883994, by rfl⟩ : syracuseStep 1178659 = 1767989) B1767989
theorem B1178675 : Blo 1178406 1178675 := bstep (se 1 (by rfl) ⟨884006, by rfl⟩ : syracuseStep 1178675 = 1768013) B1768013
theorem B1768499 : Blo 1178406 1768499 := bstep (se 1 (by rfl) ⟨1326374, by rfl⟩ : syracuseStep 1768499 = 2652749) B2652749
theorem B1866817 : Blo 1178406 1866817 := bstep (se 2 (by rfl) ⟨700056, by rfl⟩ : syracuseStep 1866817 = 1400113) B1400113
theorem B1178691 : Blo 1178406 1178691 := bstep (se 1 (by rfl) ⟨884018, by rfl⟩ : syracuseStep 1178691 = 1768037) B1768037
theorem B1989697 : Blo 1178406 1989697 := bstep (se 2 (by rfl) ⟨746136, by rfl⟩ : syracuseStep 1989697 = 1492273) B1492273
theorem B1768529 : Blo 1178406 1768529 := bstep (se 2 (by rfl) ⟨663198, by rfl⟩ : syracuseStep 1768529 = 1326397) B1326397
theorem B1178707 : Blo 1178406 1178707 := bstep (se 1 (by rfl) ⟨884030, by rfl⟩ : syracuseStep 1178707 = 1768061) B1768061
theorem B1326163 : Blo 1178406 1326163 := bstep (se 1 (by rfl) ⟨994622, by rfl⟩ : syracuseStep 1326163 = 1989245) B1989245
theorem B1178723 : Blo 1178406 1178723 := bstep (se 1 (by rfl) ⟨884042, by rfl⟩ : syracuseStep 1178723 = 1768085) B1768085
theorem B1768547 : Blo 1178406 1768547 := bstep (se 1 (by rfl) ⟨1326410, by rfl⟩ : syracuseStep 1768547 = 2652821) B2652821
theorem B1989731 : Blo 1178406 1989731 := bstep (se 1 (by rfl) ⟨1492298, by rfl⟩ : syracuseStep 1989731 = 2984597) B2984597
theorem B1178739 : Blo 1178406 1178739 := bstep (se 1 (by rfl) ⟨884054, by rfl⟩ : syracuseStep 1178739 = 1768109) B1768109
theorem B1768577 : Blo 1178406 1768577 := bstep (se 2 (by rfl) ⟨663216, by rfl⟩ : syracuseStep 1768577 = 1326433) B1326433
theorem B1178755 : Blo 1178406 1178755 := bstep (se 1 (by rfl) ⟨884066, by rfl⟩ : syracuseStep 1178755 = 1768133) B1768133
theorem B1178771 : Blo 1178406 1178771 := bstep (se 1 (by rfl) ⟨884078, by rfl⟩ : syracuseStep 1178771 = 1768157) B1768157
theorem B1768595 : Blo 1178406 1768595 := bstep (se 1 (by rfl) ⟨1326446, by rfl⟩ : syracuseStep 1768595 = 2652893) B2652893
theorem B1178787 : Blo 1178406 1178787 := bstep (se 1 (by rfl) ⟨884090, by rfl⟩ : syracuseStep 1178787 = 1768181) B1768181
theorem B3185837 : Blo 1178406 3185837 := bstep (se 3 (by rfl) ⟨597344, by rfl⟩ : syracuseStep 3185837 = 1194689) B1194689
theorem B1768625 : Blo 1178406 1768625 := bstep (se 2 (by rfl) ⟨663234, by rfl⟩ : syracuseStep 1768625 = 1326469) B1326469
theorem B2653361 : Blo 1178406 2653361 := bstep (se 2 (by rfl) ⟨995010, by rfl⟩ : syracuseStep 2653361 = 1990021) B1990021
theorem B1178803 : Blo 1178406 1178803 := bstep (se 1 (by rfl) ⟨884102, by rfl⟩ : syracuseStep 1178803 = 1768205) B1768205
theorem B1178819 : Blo 1178406 1178819 := bstep (se 1 (by rfl) ⟨884114, by rfl⟩ : syracuseStep 1178819 = 1768229) B1768229
theorem B1768643 : Blo 1178406 1768643 := bstep (se 1 (by rfl) ⟨1326482, by rfl⟩ : syracuseStep 1768643 = 2652965) B2652965
theorem B2653379 : Blo 1178406 2653379 := bstep (se 1 (by rfl) ⟨1990034, by rfl⟩ : syracuseStep 2653379 = 3980069) B3980069
theorem B1178835 : Blo 1178406 1178835 := bstep (se 1 (by rfl) ⟨884126, by rfl⟩ : syracuseStep 1178835 = 1768253) B1768253
theorem B1768673 : Blo 1178406 1768673 := bstep (se 2 (by rfl) ⟨663252, by rfl⟩ : syracuseStep 1768673 = 1326505) B1326505
theorem B1178851 : Blo 1178406 1178851 := bstep (se 1 (by rfl) ⟨884138, by rfl⟩ : syracuseStep 1178851 = 1768277) B1768277
theorem B1326307 : Blo 1178406 1326307 := bstep (se 1 (by rfl) ⟨994730, by rfl⟩ : syracuseStep 1326307 = 1989461) B1989461
theorem B1989859 : Blo 1178406 1989859 := bstep (se 1 (by rfl) ⟨1492394, by rfl⟩ : syracuseStep 1989859 = 2984789) B2984789
theorem B1178867 : Blo 1178406 1178867 := bstep (se 1 (by rfl) ⟨884150, by rfl⟩ : syracuseStep 1178867 = 1768301) B1768301
theorem B1768691 : Blo 1178406 1768691 := bstep (se 1 (by rfl) ⟨1326518, by rfl⟩ : syracuseStep 1768691 = 2653037) B2653037
theorem B1178883 : Blo 1178406 1178883 := bstep (se 1 (by rfl) ⟨884162, by rfl⟩ : syracuseStep 1178883 = 1768325) B1768325
theorem B7175429 : Blo 1178406 7175429 := bstep (se 4 (by rfl) ⟨672696, by rfl⟩ : syracuseStep 7175429 = 1345393) B1345393
theorem B1768721 : Blo 1178406 1768721 := bstep (se 2 (by rfl) ⟨663270, by rfl⟩ : syracuseStep 1768721 = 1326541) B1326541
theorem B1178899 : Blo 1178406 1178899 := bstep (se 1 (by rfl) ⟨884174, by rfl⟩ : syracuseStep 1178899 = 1768349) B1768349
theorem B1178915 : Blo 1178406 1178915 := bstep (se 1 (by rfl) ⟨884186, by rfl⟩ : syracuseStep 1178915 = 1768373) B1768373
theorem B1768739 : Blo 1178406 1768739 := bstep (se 1 (by rfl) ⟨1326554, by rfl⟩ : syracuseStep 1768739 = 2653109) B2653109
theorem B2833699 : Blo 1178406 2833699 := bstep (se 1 (by rfl) ⟨2125274, by rfl⟩ : syracuseStep 2833699 = 4250549) B4250549
theorem B1178931 : Blo 1178406 1178931 := bstep (se 1 (by rfl) ⟨884198, by rfl⟩ : syracuseStep 1178931 = 1768397) B1768397
theorem B1768769 : Blo 1178406 1768769 := bstep (se 2 (by rfl) ⟨663288, by rfl⟩ : syracuseStep 1768769 = 1326577) B1326577
theorem B1178947 : Blo 1178406 1178947 := bstep (se 1 (by rfl) ⟨884210, by rfl⟩ : syracuseStep 1178947 = 1768421) B1768421
theorem B1178963 : Blo 1178406 1178963 := bstep (se 1 (by rfl) ⟨884222, by rfl⟩ : syracuseStep 1178963 = 1768445) B1768445
theorem B1768787 : Blo 1178406 1768787 := bstep (se 1 (by rfl) ⟨1326590, by rfl⟩ : syracuseStep 1768787 = 2653181) B2653181
theorem B1178979 : Blo 1178406 1178979 := bstep (se 1 (by rfl) ⟨884234, by rfl⟩ : syracuseStep 1178979 = 1768469) B1768469
theorem B1768817 : Blo 1178406 1768817 := bstep (se 2 (by rfl) ⟨663306, by rfl⟩ : syracuseStep 1768817 = 1326613) B1326613
theorem B1990001 : Blo 1178406 1990001 := bstep (se 2 (by rfl) ⟨746250, by rfl⟩ : syracuseStep 1990001 = 1492501) B1492501
theorem B1178995 : Blo 1178406 1178995 := bstep (se 1 (by rfl) ⟨884246, by rfl⟩ : syracuseStep 1178995 = 1768493) B1768493
theorem B1326451 : Blo 1178406 1326451 := bstep (se 1 (by rfl) ⟨994838, by rfl⟩ : syracuseStep 1326451 = 1989677) B1989677
theorem B1179011 : Blo 1178406 1179011 := bstep (se 1 (by rfl) ⟨884258, by rfl⟩ : syracuseStep 1179011 = 1768517) B1768517
theorem B1768835 : Blo 1178406 1768835 := bstep (se 1 (by rfl) ⟨1326626, by rfl⟩ : syracuseStep 1768835 = 2653253) B2653253
theorem B3358093 : Blo 1178406 3358093 := bstep (se 3 (by rfl) ⟨629642, by rfl⟩ : syracuseStep 3358093 = 1259285) B1259285
theorem B1179027 : Blo 1178406 1179027 := bstep (se 1 (by rfl) ⟨884270, by rfl⟩ : syracuseStep 1179027 = 1768541) B1768541
theorem B1768865 : Blo 1178406 1768865 := bstep (se 2 (by rfl) ⟨663324, by rfl⟩ : syracuseStep 1768865 = 1326649) B1326649
theorem B1179043 : Blo 1178406 1179043 := bstep (se 1 (by rfl) ⟨884282, by rfl⟩ : syracuseStep 1179043 = 1768565) B1768565
theorem B1179059 : Blo 1178406 1179059 := bstep (se 1 (by rfl) ⟨884294, by rfl⟩ : syracuseStep 1179059 = 1768589) B1768589
theorem B1768883 : Blo 1178406 1768883 := bstep (se 1 (by rfl) ⟨1326662, by rfl⟩ : syracuseStep 1768883 = 2653325) B2653325
theorem B3980717 : Blo 1178406 3980717 := bstep (se 3 (by rfl) ⟨746384, by rfl⟩ : syracuseStep 3980717 = 1492769) B1492769
theorem B1179075 : Blo 1178406 1179075 := bstep (se 1 (by rfl) ⟨884306, by rfl⟩ : syracuseStep 1179075 = 1768613) B1768613
theorem B1768913 : Blo 1178406 1768913 := bstep (se 2 (by rfl) ⟨663342, by rfl⟩ : syracuseStep 1768913 = 1326685) B1326685
theorem B2653649 : Blo 1178406 2653649 := bstep (se 2 (by rfl) ⟨995118, by rfl⟩ : syracuseStep 2653649 = 1990237) B1990237
theorem B1179091 : Blo 1178406 1179091 := bstep (se 1 (by rfl) ⟨884318, by rfl⟩ : syracuseStep 1179091 = 1768637) B1768637
theorem B1678819 : Blo 1178406 1678819 := bstep (se 1 (by rfl) ⟨1259114, by rfl⟩ : syracuseStep 1678819 = 2518229) B2518229
theorem B1179107 : Blo 1178406 1179107 := bstep (se 1 (by rfl) ⟨884330, by rfl⟩ : syracuseStep 1179107 = 1768661) B1768661
theorem B1768931 : Blo 1178406 1768931 := bstep (se 1 (by rfl) ⟨1326698, by rfl⟩ : syracuseStep 1768931 = 2653397) B2653397
theorem B2653667 : Blo 1178406 2653667 := bstep (se 1 (by rfl) ⟨1990250, by rfl⟩ : syracuseStep 2653667 = 3980501) B3980501
theorem B3980771 : Blo 1178406 3980771 := bstep (se 1 (by rfl) ⟨2985578, by rfl⟩ : syracuseStep 3980771 = 5971157) B5971157
theorem B1990129 : Blo 1178406 1990129 := bstep (se 2 (by rfl) ⟨746298, by rfl⟩ : syracuseStep 1990129 = 1492597) B1492597
theorem B1179123 : Blo 1178406 1179123 := bstep (se 1 (by rfl) ⟨884342, by rfl⟩ : syracuseStep 1179123 = 1768685) B1768685
theorem B1768961 : Blo 1178406 1768961 := bstep (se 2 (by rfl) ⟨663360, by rfl⟩ : syracuseStep 1768961 = 1326721) B1326721
theorem B1179139 : Blo 1178406 1179139 := bstep (se 1 (by rfl) ⟨884354, by rfl⟩ : syracuseStep 1179139 = 1768709) B1768709
theorem B1326595 : Blo 1178406 1326595 := bstep (se 1 (by rfl) ⟨994946, by rfl⟩ : syracuseStep 1326595 = 1989893) B1989893
theorem B1179155 : Blo 1178406 1179155 := bstep (se 1 (by rfl) ⟨884366, by rfl⟩ : syracuseStep 1179155 = 1768733) B1768733
theorem B1768979 : Blo 1178406 1768979 := bstep (se 1 (by rfl) ⟨1326734, by rfl⟩ : syracuseStep 1768979 = 2653469) B2653469
theorem B1990163 : Blo 1178406 1990163 := bstep (se 1 (by rfl) ⟨1492622, by rfl⟩ : syracuseStep 1990163 = 2985245) B2985245
theorem B1179171 : Blo 1178406 1179171 := bstep (se 1 (by rfl) ⟨884378, by rfl⟩ : syracuseStep 1179171 = 1768757) B1768757
theorem B3358253 : Blo 1178406 3358253 := bstep (se 3 (by rfl) ⟨629672, by rfl⟩ : syracuseStep 3358253 = 1259345) B1259345
theorem B1769009 : Blo 1178406 1769009 := bstep (se 2 (by rfl) ⟨663378, by rfl⟩ : syracuseStep 1769009 = 1326757) B1326757
theorem B1179187 : Blo 1178406 1179187 := bstep (se 1 (by rfl) ⟨884390, by rfl⟩ : syracuseStep 1179187 = 1768781) B1768781
theorem B1179203 : Blo 1178406 1179203 := bstep (se 1 (by rfl) ⟨884402, by rfl⟩ : syracuseStep 1179203 = 1768805) B1768805
theorem B1769027 : Blo 1178406 1769027 := bstep (se 1 (by rfl) ⟨1326770, by rfl⟩ : syracuseStep 1769027 = 2653541) B2653541
theorem B8175173 : Blo 1178406 8175173 := bstep (se 4 (by rfl) ⟨766422, by rfl⟩ : syracuseStep 8175173 = 1532845) B1532845
theorem B1179219 : Blo 1178406 1179219 := bstep (se 1 (by rfl) ⟨884414, by rfl⟩ : syracuseStep 1179219 = 1768829) B1768829
theorem B1769057 : Blo 1178406 1769057 := bstep (se 2 (by rfl) ⟨663396, by rfl⟩ : syracuseStep 1769057 = 1326793) B1326793
theorem B1179235 : Blo 1178406 1179235 := bstep (se 1 (by rfl) ⟨884426, by rfl⟩ : syracuseStep 1179235 = 1768853) B1768853
theorem B1179251 : Blo 1178406 1179251 := bstep (se 1 (by rfl) ⟨884438, by rfl⟩ : syracuseStep 1179251 = 1768877) B1768877
theorem B1769075 : Blo 1178406 1769075 := bstep (se 1 (by rfl) ⟨1326806, by rfl⟩ : syracuseStep 1769075 = 2653613) B2653613
theorem B1179267 : Blo 1178406 1179267 := bstep (se 1 (by rfl) ⟨884450, by rfl⟩ : syracuseStep 1179267 = 1768901) B1768901
theorem B1769105 : Blo 1178406 1769105 := bstep (se 2 (by rfl) ⟨663414, by rfl⟩ : syracuseStep 1769105 = 1326829) B1326829
theorem B2391697 : Blo 1178406 2391697 := bstep (se 2 (by rfl) ⟨896886, by rfl⟩ : syracuseStep 2391697 = 1793773) B1793773
theorem B1179283 : Blo 1178406 1179283 := bstep (se 1 (by rfl) ⟨884462, by rfl⟩ : syracuseStep 1179283 = 1768925) B1768925
theorem B1326739 : Blo 1178406 1326739 := bstep (se 1 (by rfl) ⟨995054, by rfl⟩ : syracuseStep 1326739 = 1990109) B1990109
theorem B1990291 : Blo 1178406 1990291 := bstep (se 1 (by rfl) ⟨1492718, by rfl⟩ : syracuseStep 1990291 = 2985437) B2985437
theorem B1179299 : Blo 1178406 1179299 := bstep (se 1 (by rfl) ⟨884474, by rfl⟩ : syracuseStep 1179299 = 1768949) B1768949
theorem B1769123 : Blo 1178406 1769123 := bstep (se 1 (by rfl) ⟨1326842, by rfl⟩ : syracuseStep 1769123 = 2653685) B2653685
theorem B1179315 : Blo 1178406 1179315 := bstep (se 1 (by rfl) ⟨884486, by rfl⟩ : syracuseStep 1179315 = 1768973) B1768973
theorem B1769153 : Blo 1178406 1769153 := bstep (se 2 (by rfl) ⟨663432, by rfl⟩ : syracuseStep 1769153 = 1326865) B1326865
theorem B1179331 : Blo 1178406 1179331 := bstep (se 1 (by rfl) ⟨884498, by rfl⟩ : syracuseStep 1179331 = 1768997) B1768997
theorem B1179347 : Blo 1178406 1179347 := bstep (se 1 (by rfl) ⟨884510, by rfl⟩ : syracuseStep 1179347 = 1769021) B1769021
theorem B1769171 : Blo 1178406 1769171 := bstep (se 1 (by rfl) ⟨1326878, by rfl⟩ : syracuseStep 1769171 = 2653757) B2653757
theorem B1179363 : Blo 1178406 1179363 := bstep (se 1 (by rfl) ⟨884522, by rfl⟩ : syracuseStep 1179363 = 1769045) B1769045
theorem B3358435 : Blo 1178406 3358435 := bstep (se 1 (by rfl) ⟨2518826, by rfl⟩ : syracuseStep 3358435 = 5037653) B5037653
theorem B1769201 : Blo 1178406 1769201 := bstep (se 2 (by rfl) ⟨663450, by rfl⟩ : syracuseStep 1769201 = 1326901) B1326901
theorem B2653937 : Blo 1178406 2653937 := bstep (se 2 (by rfl) ⟨995226, by rfl⟩ : syracuseStep 2653937 = 1990453) B1990453
theorem B1179379 : Blo 1178406 1179379 := bstep (se 1 (by rfl) ⟨884534, by rfl⟩ : syracuseStep 1179379 = 1769069) B1769069
theorem B3981041 : Blo 1178406 3981041 := bstep (se 2 (by rfl) ⟨1492890, by rfl⟩ : syracuseStep 3981041 = 2985781) B2985781
theorem B1179395 : Blo 1178406 1179395 := bstep (se 1 (by rfl) ⟨884546, by rfl⟩ : syracuseStep 1179395 = 1769093) B1769093
theorem B1769219 : Blo 1178406 1769219 := bstep (se 1 (by rfl) ⟨1326914, by rfl⟩ : syracuseStep 1769219 = 2653829) B2653829
theorem B2653955 : Blo 1178406 2653955 := bstep (se 1 (by rfl) ⟨1990466, by rfl⟩ : syracuseStep 2653955 = 3980933) B3980933
theorem B6381317 : Blo 1178406 6381317 := bstep (se 4 (by rfl) ⟨598248, by rfl⟩ : syracuseStep 6381317 = 1196497) B1196497
theorem B1179411 : Blo 1178406 1179411 := bstep (se 1 (by rfl) ⟨884558, by rfl⟩ : syracuseStep 1179411 = 1769117) B1769117
theorem B77561621 : Blo 1178406 77561621 := bstep (se 6 (by rfl) ⟨1817850, by rfl⟩ : syracuseStep 77561621 = 3635701) B3635701
theorem B1769249 : Blo 1178406 1769249 := bstep (se 2 (by rfl) ⟨663468, by rfl⟩ : syracuseStep 1769249 = 1326937) B1326937
theorem B1179427 : Blo 1178406 1179427 := bstep (se 1 (by rfl) ⟨884570, by rfl⟩ : syracuseStep 1179427 = 1769141) B1769141
theorem B1326883 : Blo 1178406 1326883 := bstep (se 1 (by rfl) ⟨995162, by rfl⟩ : syracuseStep 1326883 = 1990325) B1990325
theorem B1990433 : Blo 1178406 1990433 := bstep (se 2 (by rfl) ⟨746412, by rfl⟩ : syracuseStep 1990433 = 1492825) B1492825
theorem B1179443 : Blo 1178406 1179443 := bstep (se 1 (by rfl) ⟨884582, by rfl⟩ : syracuseStep 1179443 = 1769165) B1769165
theorem B1769267 : Blo 1178406 1769267 := bstep (se 1 (by rfl) ⟨1326950, by rfl⟩ : syracuseStep 1769267 = 2653901) B2653901
theorem B1179459 : Blo 1178406 1179459 := bstep (se 1 (by rfl) ⟨884594, by rfl⟩ : syracuseStep 1179459 = 1769189) B1769189
theorem B1769297 : Blo 1178406 1769297 := bstep (se 2 (by rfl) ⟨663486, by rfl⟩ : syracuseStep 1769297 = 1326973) B1326973
theorem B1179475 : Blo 1178406 1179475 := bstep (se 1 (by rfl) ⟨884606, by rfl⟩ : syracuseStep 1179475 = 1769213) B1769213
theorem B1179491 : Blo 1178406 1179491 := bstep (se 1 (by rfl) ⟨884618, by rfl⟩ : syracuseStep 1179491 = 1769237) B1769237
theorem B1769315 : Blo 1178406 1769315 := bstep (se 1 (by rfl) ⟨1326986, by rfl⟩ : syracuseStep 1769315 = 2653973) B2653973
theorem B1179507 : Blo 1178406 1179507 := bstep (se 1 (by rfl) ⟨884630, by rfl⟩ : syracuseStep 1179507 = 1769261) B1769261
theorem B1769345 : Blo 1178406 1769345 := bstep (se 2 (by rfl) ⟨663504, by rfl⟩ : syracuseStep 1769345 = 1327009) B1327009
theorem B1179523 : Blo 1178406 1179523 := bstep (se 1 (by rfl) ⟨884642, by rfl⟩ : syracuseStep 1179523 = 1769285) B1769285
theorem B1179539 : Blo 1178406 1179539 := bstep (se 1 (by rfl) ⟨884654, by rfl⟩ : syracuseStep 1179539 = 1769309) B1769309
theorem B1769363 : Blo 1178406 1769363 := bstep (se 1 (by rfl) ⟨1327022, by rfl⟩ : syracuseStep 1769363 = 2654045) B2654045
theorem B1990561 : Blo 1178406 1990561 := bstep (se 2 (by rfl) ⟨746460, by rfl⟩ : syracuseStep 1990561 = 1492921) B1492921
theorem B1179555 : Blo 1178406 1179555 := bstep (se 1 (by rfl) ⟨884666, by rfl⟩ : syracuseStep 1179555 = 1769333) B1769333
theorem B1769393 : Blo 1178406 1769393 := bstep (se 2 (by rfl) ⟨663522, by rfl⟩ : syracuseStep 1769393 = 1327045) B1327045
theorem B1179571 : Blo 1178406 1179571 := bstep (se 1 (by rfl) ⟨884678, by rfl⟩ : syracuseStep 1179571 = 1769357) B1769357
theorem B1327027 : Blo 1178406 1327027 := bstep (se 1 (by rfl) ⟨995270, by rfl⟩ : syracuseStep 1327027 = 1990541) B1990541
theorem B1679297 : Blo 1178406 1679297 := bstep (se 2 (by rfl) ⟨629736, by rfl⟩ : syracuseStep 1679297 = 1259473) B1259473
theorem B1179587 : Blo 1178406 1179587 := bstep (se 1 (by rfl) ⟨884690, by rfl⟩ : syracuseStep 1179587 = 1769381) B1769381
theorem B1769411 : Blo 1178406 1769411 := bstep (se 1 (by rfl) ⟨1327058, by rfl⟩ : syracuseStep 1769411 = 2654117) B2654117
theorem B14540741 : Blo 1178406 14540741 := bstep (se 4 (by rfl) ⟨1363194, by rfl⟩ : syracuseStep 14540741 = 2726389) B2726389
theorem B1990595 : Blo 1178406 1990595 := bstep (se 1 (by rfl) ⟨1492946, by rfl⟩ : syracuseStep 1990595 = 2985893) B2985893
theorem B5742541 : Blo 1178406 5742541 := bstep (se 3 (by rfl) ⟨1076726, by rfl⟩ : syracuseStep 5742541 = 2153453) B2153453
theorem B1179603 : Blo 1178406 1179603 := bstep (se 1 (by rfl) ⟨884702, by rfl⟩ : syracuseStep 1179603 = 1769405) B1769405
theorem B1769441 : Blo 1178406 1769441 := bstep (se 2 (by rfl) ⟨663540, by rfl⟩ : syracuseStep 1769441 = 1327081) B1327081
theorem B1179619 : Blo 1178406 1179619 := bstep (se 1 (by rfl) ⟨884714, by rfl⟩ : syracuseStep 1179619 = 1769429) B1769429
theorem B1179635 : Blo 1178406 1179635 := bstep (se 1 (by rfl) ⟨884726, by rfl⟩ : syracuseStep 1179635 = 1769453) B1769453
theorem B1769459 : Blo 1178406 1769459 := bstep (se 1 (by rfl) ⟨1327094, by rfl⟩ : syracuseStep 1769459 = 2654189) B2654189
theorem B4481027 : Blo 1178406 4481027 := bstep (se 1 (by rfl) ⟨3360770, by rfl⟩ : syracuseStep 4481027 = 6721541) B6721541
theorem B1769483 : Blo 1178406 1769483 := bstep (se 1 (by rfl) ⟨1327112, by rfl⟩ : syracuseStep 1769483 = 2654225) B2654225
theorem B1179659 : Blo 1178406 1179659 := bstep (se 1 (by rfl) ⟨884744, by rfl⟩ : syracuseStep 1179659 = 1769489) B1769489
theorem B4481041 : Blo 1178406 4481041 := bstep (se 2 (by rfl) ⟨1680390, by rfl⟩ : syracuseStep 4481041 = 3360781) B3360781
theorem B1679383 : Blo 1178406 1679383 := bstep (se 1 (by rfl) ⟨1259537, by rfl⟩ : syracuseStep 1679383 = 2519075) B2519075
theorem B1769495 : Blo 1178406 1769495 := bstep (se 1 (by rfl) ⟨1327121, by rfl⟩ : syracuseStep 1769495 = 2654243) B2654243
theorem B1179671 : Blo 1178406 1179671 := bstep (se 1 (by rfl) ⟨884753, by rfl⟩ : syracuseStep 1179671 = 1769507) B1769507
theorem B1179691 : Blo 1178406 1179691 := bstep (se 1 (by rfl) ⟨884768, by rfl⟩ : syracuseStep 1179691 = 1769537) B1769537
theorem B1179703 : Blo 1178406 1179703 := bstep (se 1 (by rfl) ⟨884777, by rfl⟩ : syracuseStep 1179703 = 1769555) B1769555
theorem B2834507 : Blo 1178406 2834507 := bstep (se 1 (by rfl) ⟨2125880, by rfl⟩ : syracuseStep 2834507 = 4251761) B4251761
theorem B1179723 : Blo 1178406 1179723 := bstep (se 1 (by rfl) ⟨884792, by rfl⟩ : syracuseStep 1179723 = 1769585) B1769585
theorem B1179735 : Blo 1178406 1179735 := bstep (se 1 (by rfl) ⟨884801, by rfl⟩ : syracuseStep 1179735 = 1769603) B1769603
theorem B2392151 : Blo 1178406 2392151 := bstep (se 1 (by rfl) ⟨1794113, by rfl⟩ : syracuseStep 2392151 = 3588227) B3588227
theorem B2654297 : Blo 1178406 2654297 := bstep (se 2 (by rfl) ⟨995361, by rfl⟩ : syracuseStep 2654297 = 1990723) B1990723
theorem B1769561 : Blo 1178406 1769561 := bstep (se 2 (by rfl) ⟨663585, by rfl⟩ : syracuseStep 1769561 = 1327171) B1327171
theorem B1179755 : Blo 1178406 1179755 := bstep (se 1 (by rfl) ⟨884816, by rfl⟩ : syracuseStep 1179755 = 1769633) B1769633
theorem B1179767 : Blo 1178406 1179767 := bstep (se 1 (by rfl) ⟨884825, by rfl⟩ : syracuseStep 1179767 = 1769651) B1769651
theorem B1327243 : Blo 1178406 1327243 := bstep (se 1 (by rfl) ⟨995432, by rfl⟩ : syracuseStep 1327243 = 1990865) B1990865
theorem B1179787 : Blo 1178406 1179787 := bstep (se 1 (by rfl) ⟨884840, by rfl⟩ : syracuseStep 1179787 = 1769681) B1769681
theorem B1179799 : Blo 1178406 1179799 := bstep (se 1 (by rfl) ⟨884849, by rfl⟩ : syracuseStep 1179799 = 1769699) B1769699
theorem B1179819 : Blo 1178406 1179819 := bstep (se 1 (by rfl) ⟨884864, by rfl⟩ : syracuseStep 1179819 = 1769729) B1769729
theorem B2654387 : Blo 1178406 2654387 := bstep (se 1 (by rfl) ⟨1990790, by rfl⟩ : syracuseStep 2654387 = 3981581) B3981581
theorem B1179831 : Blo 1178406 1179831 := bstep (se 1 (by rfl) ⟨884873, by rfl⟩ : syracuseStep 1179831 = 1769747) B1769747
theorem B1769675 : Blo 1178406 1769675 := bstep (se 1 (by rfl) ⟨1327256, by rfl⟩ : syracuseStep 1769675 = 2654513) B2654513
theorem B1179851 : Blo 1178406 1179851 := bstep (se 1 (by rfl) ⟨884888, by rfl⟩ : syracuseStep 1179851 = 1769777) B1769777
theorem B2654423 : Blo 1178406 2654423 := bstep (se 1 (by rfl) ⟨1990817, by rfl⟩ : syracuseStep 2654423 = 3981635) B3981635
theorem B1769687 : Blo 1178406 1769687 := bstep (se 1 (by rfl) ⟨1327265, by rfl⟩ : syracuseStep 1769687 = 2654531) B2654531
theorem B1179863 : Blo 1178406 1179863 := bstep (se 1 (by rfl) ⟨884897, by rfl⟩ : syracuseStep 1179863 = 1769795) B1769795
theorem B5038301 : Blo 1178406 5038301 := bstep (se 3 (by rfl) ⟨944681, by rfl⟩ : syracuseStep 5038301 = 1889363) B1889363
theorem B1179883 : Blo 1178406 1179883 := bstep (se 1 (by rfl) ⟨884912, by rfl⟩ : syracuseStep 1179883 = 1769825) B1769825
theorem B1327351 : Blo 1178406 1327351 := bstep (se 1 (by rfl) ⟨995513, by rfl⟩ : syracuseStep 1327351 = 1991027) B1991027
theorem B1179895 : Blo 1178406 1179895 := bstep (se 1 (by rfl) ⟨884921, by rfl⟩ : syracuseStep 1179895 = 1769843) B1769843
theorem B2154763 : Blo 1178406 2154763 := bstep (se 1 (by rfl) ⟨1616072, by rfl⟩ : syracuseStep 2154763 = 3232145) B3232145
theorem B1179915 : Blo 1178406 1179915 := bstep (se 1 (by rfl) ⟨884936, by rfl⟩ : syracuseStep 1179915 = 1769873) B1769873
theorem B1179927 : Blo 1178406 1179927 := bstep (se 1 (by rfl) ⟨884945, by rfl⟩ : syracuseStep 1179927 = 1769891) B1769891
theorem B1769753 : Blo 1178406 1769753 := bstep (se 2 (by rfl) ⟨663657, by rfl⟩ : syracuseStep 1769753 = 1327315) B1327315
theorem B1179947 : Blo 1178406 1179947 := bstep (se 1 (by rfl) ⟨884960, by rfl⟩ : syracuseStep 1179947 = 1769921) B1769921
theorem B1179959 : Blo 1178406 1179959 := bstep (se 1 (by rfl) ⟨884969, by rfl⟩ : syracuseStep 1179959 = 1769939) B1769939
theorem B4481345 : Blo 1178406 4481345 := bstep (se 2 (by rfl) ⟨1680504, by rfl⟩ : syracuseStep 4481345 = 3361009) B3361009
theorem B1179979 : Blo 1178406 1179979 := bstep (se 1 (by rfl) ⟨884984, by rfl⟩ : syracuseStep 1179979 = 1769969) B1769969
theorem B1179991 : Blo 1178406 1179991 := bstep (se 1 (by rfl) ⟨884993, by rfl⟩ : syracuseStep 1179991 = 1769987) B1769987
theorem B11493733 : Blo 1178406 11493733 := bstep (se 4 (by rfl) ⟨1077537, by rfl⟩ : syracuseStep 11493733 = 2155075) B2155075
theorem B1180011 : Blo 1178406 1180011 := bstep (se 1 (by rfl) ⟨885008, by rfl⟩ : syracuseStep 1180011 = 1770017) B1770017
theorem B1180023 : Blo 1178406 1180023 := bstep (se 1 (by rfl) ⟨885017, by rfl⟩ : syracuseStep 1180023 = 1770035) B1770035
theorem B2654603 : Blo 1178406 2654603 := bstep (se 1 (by rfl) ⟨1990952, by rfl⟩ : syracuseStep 2654603 = 3981905) B3981905
theorem B1769867 : Blo 1178406 1769867 := bstep (se 1 (by rfl) ⟨1327400, by rfl⟩ : syracuseStep 1769867 = 2654801) B2654801
theorem B1180043 : Blo 1178406 1180043 := bstep (se 1 (by rfl) ⟨885032, by rfl⟩ : syracuseStep 1180043 = 1770065) B1770065
theorem B1769879 : Blo 1178406 1769879 := bstep (se 1 (by rfl) ⟨1327409, by rfl⟩ : syracuseStep 1769879 = 2654819) B2654819
theorem B1180055 : Blo 1178406 1180055 := bstep (se 1 (by rfl) ⟨885041, by rfl⟩ : syracuseStep 1180055 = 1770083) B1770083
theorem B1327531 : Blo 1178406 1327531 := bstep (se 1 (by rfl) ⟨995648, by rfl⟩ : syracuseStep 1327531 = 1991297) B1991297
theorem B1180075 : Blo 1178406 1180075 := bstep (se 1 (by rfl) ⟨885056, by rfl⟩ : syracuseStep 1180075 = 1770113) B1770113
theorem B10068401 : Blo 1178406 10068401 := bstep (se 2 (by rfl) ⟨3775650, by rfl⟩ : syracuseStep 10068401 = 7551301) B7551301
theorem B1180087 : Blo 1178406 1180087 := bstep (se 1 (by rfl) ⟨885065, by rfl⟩ : syracuseStep 1180087 = 1770131) B1770131
theorem B2654657 : Blo 1178406 2654657 := bstep (se 2 (by rfl) ⟨995496, by rfl⟩ : syracuseStep 2654657 = 1990993) B1990993
theorem B1180107 : Blo 1178406 1180107 := bstep (se 1 (by rfl) ⟨885080, by rfl⟩ : syracuseStep 1180107 = 1770161) B1770161
theorem B2392523 : Blo 1178406 2392523 := bstep (se 1 (by rfl) ⟨1794392, by rfl⟩ : syracuseStep 2392523 = 3588785) B3588785
theorem B1180119 : Blo 1178406 1180119 := bstep (se 1 (by rfl) ⟨885089, by rfl⟩ : syracuseStep 1180119 = 1770179) B1770179
theorem B18407897 : Blo 1178406 18407897 := bstep (se 2 (by rfl) ⟨6902961, by rfl⟩ : syracuseStep 18407897 = 13805923) B13805923
theorem B1769945 : Blo 1178406 1769945 := bstep (se 2 (by rfl) ⟨663729, by rfl⟩ : syracuseStep 1769945 = 1327459) B1327459
theorem B1180139 : Blo 1178406 1180139 := bstep (se 1 (by rfl) ⟨885104, by rfl⟩ : syracuseStep 1180139 = 1770209) B1770209
theorem B1180151 : Blo 1178406 1180151 := bstep (se 1 (by rfl) ⟨885113, by rfl⟩ : syracuseStep 1180151 = 1770227) B1770227
theorem B1180171 : Blo 1178406 1180171 := bstep (se 1 (by rfl) ⟨885128, by rfl⟩ : syracuseStep 1180171 = 1770257) B1770257
theorem B1327639 : Blo 1178406 1327639 := bstep (se 1 (by rfl) ⟨995729, by rfl⟩ : syracuseStep 1327639 = 1991459) B1991459
theorem B1180183 : Blo 1178406 1180183 := bstep (se 1 (by rfl) ⟨885137, by rfl⟩ : syracuseStep 1180183 = 1770275) B1770275
theorem B1180203 : Blo 1178406 1180203 := bstep (se 1 (by rfl) ⟨885152, by rfl⟩ : syracuseStep 1180203 = 1770305) B1770305
theorem B1180215 : Blo 1178406 1180215 := bstep (se 1 (by rfl) ⟨885161, by rfl⟩ : syracuseStep 1180215 = 1770323) B1770323
theorem B1991243 : Blo 1178406 1991243 := bstep (se 1 (by rfl) ⟨1493432, by rfl⟩ : syracuseStep 1991243 = 2986865) B2986865
theorem B1770059 : Blo 1178406 1770059 := bstep (se 1 (by rfl) ⟨1327544, by rfl⟩ : syracuseStep 1770059 = 2655089) B2655089
theorem B1180235 : Blo 1178406 1180235 := bstep (se 1 (by rfl) ⟨885176, by rfl⟩ : syracuseStep 1180235 = 1770353) B1770353
theorem B1770071 : Blo 1178406 1770071 := bstep (se 1 (by rfl) ⟨1327553, by rfl⟩ : syracuseStep 1770071 = 2655107) B2655107
theorem B1180247 : Blo 1178406 1180247 := bstep (se 1 (by rfl) ⟨885185, by rfl⟩ : syracuseStep 1180247 = 1770371) B1770371
theorem B1180267 : Blo 1178406 1180267 := bstep (se 1 (by rfl) ⟨885200, by rfl⟩ : syracuseStep 1180267 = 1770401) B1770401
theorem B1180279 : Blo 1178406 1180279 := bstep (se 1 (by rfl) ⟨885209, by rfl⟩ : syracuseStep 1180279 = 1770419) B1770419
theorem B1180299 : Blo 1178406 1180299 := bstep (se 1 (by rfl) ⟨885224, by rfl⟩ : syracuseStep 1180299 = 1770449) B1770449
theorem B1180311 : Blo 1178406 1180311 := bstep (se 1 (by rfl) ⟨885233, by rfl⟩ : syracuseStep 1180311 = 1770467) B1770467
theorem B2654873 : Blo 1178406 2654873 := bstep (se 2 (by rfl) ⟨995577, by rfl⟩ : syracuseStep 2654873 = 1991155) B1991155
theorem B1770137 : Blo 1178406 1770137 := bstep (se 2 (by rfl) ⟨663801, by rfl⟩ : syracuseStep 1770137 = 1327603) B1327603
theorem B1180331 : Blo 1178406 1180331 := bstep (se 1 (by rfl) ⟨885248, by rfl⟩ : syracuseStep 1180331 = 1770497) B1770497
theorem B9560753 : Blo 1178406 9560753 := bstep (se 2 (by rfl) ⟨3585282, by rfl⟩ : syracuseStep 9560753 = 7170565) B7170565
theorem B1180343 : Blo 1178406 1180343 := bstep (se 1 (by rfl) ⟨885257, by rfl⟩ : syracuseStep 1180343 = 1770515) B1770515
theorem B1991371 : Blo 1178406 1991371 := bstep (se 1 (by rfl) ⟨1493528, by rfl⟩ : syracuseStep 1991371 = 2987057) B2987057
theorem B1327819 : Blo 1178406 1327819 := bstep (se 1 (by rfl) ⟨995864, by rfl⟩ : syracuseStep 1327819 = 1991729) B1991729
theorem B1180363 : Blo 1178406 1180363 := bstep (se 1 (by rfl) ⟨885272, by rfl⟩ : syracuseStep 1180363 = 1770545) B1770545
theorem B1180375 : Blo 1178406 1180375 := bstep (se 1 (by rfl) ⟨885281, by rfl⟩ : syracuseStep 1180375 = 1770563) B1770563
theorem B1180395 : Blo 1178406 1180395 := bstep (se 1 (by rfl) ⟨885296, by rfl⟩ : syracuseStep 1180395 = 1770593) B1770593
theorem B2654963 : Blo 1178406 2654963 := bstep (se 1 (by rfl) ⟨1991222, by rfl⟩ : syracuseStep 2654963 = 3982445) B3982445
theorem B2237195 : Blo 1178406 2237195 := bstep (se 1 (by rfl) ⟨1677896, by rfl⟩ : syracuseStep 2237195 = 3355793) B3355793
theorem B1770251 : Blo 1178406 1770251 := bstep (se 1 (by rfl) ⟨1327688, by rfl⟩ : syracuseStep 1770251 = 2655377) B2655377
theorem B4252439 : Blo 1178406 4252439 := bstep (se 1 (by rfl) ⟨3189329, by rfl⟩ : syracuseStep 4252439 = 6378659) B6378659
theorem B2654999 : Blo 1178406 2654999 := bstep (se 1 (by rfl) ⟨1991249, by rfl⟩ : syracuseStep 2654999 = 3982499) B3982499
theorem B1770263 : Blo 1178406 1770263 := bstep (se 1 (by rfl) ⟨1327697, by rfl⟩ : syracuseStep 1770263 = 2655395) B2655395
theorem B1327927 : Blo 1178406 1327927 := bstep (se 1 (by rfl) ⟨995945, by rfl⟩ : syracuseStep 1327927 = 1991891) B1991891
theorem B1491787 : Blo 1178406 1491787 := bstep (se 1 (by rfl) ⟨1118840, by rfl⟩ : syracuseStep 1491787 = 2237681) B2237681
theorem B1680203 : Blo 1178406 1680203 := bstep (se 1 (by rfl) ⟨1260152, by rfl⟩ : syracuseStep 1680203 = 2520305) B2520305
theorem B1991513 : Blo 1178406 1991513 := bstep (se 2 (by rfl) ⟨746817, by rfl⟩ : syracuseStep 1991513 = 1493635) B1493635
theorem B1770329 : Blo 1178406 1770329 := bstep (se 2 (by rfl) ⟨663873, by rfl⟩ : syracuseStep 1770329 = 1327747) B1327747
theorem B7168861 : Blo 1178406 7168861 := bstep (se 3 (by rfl) ⟨1344161, by rfl⟩ : syracuseStep 7168861 = 2688323) B2688323
theorem B5669783 : Blo 1178406 5669783 := bstep (se 1 (by rfl) ⟨4252337, by rfl⟩ : syracuseStep 5669783 = 8504675) B8504675
theorem B2237377 : Blo 1178406 2237377 := bstep (se 2 (by rfl) ⟨839016, by rfl⟩ : syracuseStep 2237377 = 1678033) B1678033
theorem B3982283 : Blo 1178406 3982283 := bstep (se 1 (by rfl) ⟨2986712, by rfl⟩ : syracuseStep 3982283 = 5973425) B5973425
theorem B2655179 : Blo 1178406 2655179 := bstep (se 1 (by rfl) ⟨1991384, by rfl⟩ : syracuseStep 2655179 = 3982769) B3982769
theorem B1770443 : Blo 1178406 1770443 := bstep (se 1 (by rfl) ⟨1327832, by rfl⟩ : syracuseStep 1770443 = 2655665) B2655665
theorem B1770455 : Blo 1178406 1770455 := bstep (se 1 (by rfl) ⟨1327841, by rfl⟩ : syracuseStep 1770455 = 2655683) B2655683
theorem B1991641 : Blo 1178406 1991641 := bstep (se 2 (by rfl) ⟨746865, by rfl⟩ : syracuseStep 1991641 = 1493731) B1493731
theorem B2655233 : Blo 1178406 2655233 := bstep (se 2 (by rfl) ⟨995712, by rfl⟩ : syracuseStep 2655233 = 1991425) B1991425
theorem B1770521 : Blo 1178406 1770521 := bstep (se 2 (by rfl) ⟨663945, by rfl⟩ : syracuseStep 1770521 = 1327891) B1327891
theorem B3777587 : Blo 1178406 3777587 := bstep (se 1 (by rfl) ⟨2833190, by rfl⟩ : syracuseStep 3777587 = 5666381) B5666381
theorem B2982977 : Blo 1178406 2982977 := bstep (se 2 (by rfl) ⟨1118616, by rfl⟩ : syracuseStep 2982977 = 2237233) B2237233
theorem B3982553 : Blo 1178406 3982553 := bstep (se 2 (by rfl) ⟨1493457, by rfl⟩ : syracuseStep 3982553 = 2986915) B2986915
theorem B2655449 : Blo 1178406 2655449 := bstep (se 2 (by rfl) ⟨995793, by rfl⟩ : syracuseStep 2655449 = 1991587) B1991587
theorem B2237719 : Blo 1178406 2237719 := bstep (se 1 (by rfl) ⟨1678289, by rfl⟩ : syracuseStep 2237719 = 3356579) B3356579
theorem B2655539 : Blo 1178406 2655539 := bstep (se 1 (by rfl) ⟨1991654, by rfl⟩ : syracuseStep 2655539 = 3983309) B3983309
theorem B5375297 : Blo 1178406 5375297 := bstep (se 2 (by rfl) ⟨2015736, by rfl⟩ : syracuseStep 5375297 = 4031473) B4031473
theorem B2655575 : Blo 1178406 2655575 := bstep (se 1 (by rfl) ⟨1991681, by rfl⟩ : syracuseStep 2655575 = 3983363) B3983363
theorem B8496485 : Blo 1178406 8496485 := bstep (se 4 (by rfl) ⟨796545, by rfl⟩ : syracuseStep 8496485 = 1593091) B1593091
theorem B2237939 : Blo 1178406 2237939 := bstep (se 1 (by rfl) ⟨1678454, by rfl⟩ : syracuseStep 2237939 = 3356909) B3356909
theorem B2655755 : Blo 1178406 2655755 := bstep (se 1 (by rfl) ⟨1991816, by rfl⟩ : syracuseStep 2655755 = 3983633) B3983633
theorem B21800461 : Blo 1178406 21800461 := bstep (se 3 (by rfl) ⟨4087586, by rfl⟩ : syracuseStep 21800461 = 8175173) B8175173
theorem B2655809 : Blo 1178406 2655809 := bstep (se 2 (by rfl) ⟨995928, by rfl⟩ : syracuseStep 2655809 = 1991857) B1991857
theorem B2983513 : Blo 1178406 2983513 := bstep (se 2 (by rfl) ⟨1118817, by rfl⟩ : syracuseStep 2983513 = 2237635) B2237635
theorem B4474541 : Blo 1178406 4474541 := bstep (se 3 (by rfl) ⟨838976, by rfl⟩ : syracuseStep 4474541 = 1677953) B1677953
theorem B2238167 : Blo 1178406 2238167 := bstep (se 1 (by rfl) ⟨1678625, by rfl⟩ : syracuseStep 2238167 = 3357251) B3357251
theorem B3778265 : Blo 1178406 3778265 := bstep (se 2 (by rfl) ⟨1416849, by rfl⟩ : syracuseStep 3778265 = 2833699) B2833699
theorem B1492759 : Blo 1178406 1492759 := bstep (se 1 (by rfl) ⟨1119569, by rfl⟩ : syracuseStep 1492759 = 2239139) B2239139
theorem B54470501 : Blo 1178406 54470501 := bstep (se 4 (by rfl) ⟨5106609, by rfl⟩ : syracuseStep 54470501 = 10213219) B10213219
theorem B5973911 : Blo 1178406 5973911 := bstep (se 1 (by rfl) ⟨4480433, by rfl⟩ : syracuseStep 5973911 = 8960867) B8960867
theorem B3983255 : Blo 1178406 3983255 := bstep (se 1 (by rfl) ⟨2987441, by rfl⟩ : syracuseStep 3983255 = 5974883) B5974883
theorem B2238425 : Blo 1178406 2238425 := bstep (se 2 (by rfl) ⟨839409, by rfl⟩ : syracuseStep 2238425 = 1678819) B1678819
theorem B2123891 : Blo 1178406 2123891 := bstep (se 1 (by rfl) ⟨1592918, by rfl⟩ : syracuseStep 2123891 = 3185837) B3185837
theorem B3188929 : Blo 1178406 3188929 := bstep (se 2 (by rfl) ⟨1195848, by rfl⟩ : syracuseStep 3188929 = 2391697) B2391697
theorem B14535013 : Blo 1178406 14535013 := bstep (se 4 (by rfl) ⟨1362657, by rfl⟩ : syracuseStep 14535013 = 2725315) B2725315
theorem B2238835 : Blo 1178406 2238835 := bstep (se 1 (by rfl) ⟨1679126, by rfl⟩ : syracuseStep 2238835 = 3358253) B3358253
theorem B3983795 : Blo 1178406 3983795 := bstep (se 1 (by rfl) ⟨2987846, by rfl⟩ : syracuseStep 3983795 = 5975693) B5975693
theorem B5966297 : Blo 1178406 5966297 := bstep (se 2 (by rfl) ⟨2237361, by rfl⟩ : syracuseStep 5966297 = 4474723) B4474723
theorem B4254211 : Blo 1178406 4254211 := bstep (se 1 (by rfl) ⟨3190658, by rfl⟩ : syracuseStep 4254211 = 6381317) B6381317
theorem B1493579 : Blo 1178406 1493579 := bstep (se 1 (by rfl) ⟨1120184, by rfl⟩ : syracuseStep 1493579 = 2240369) B2240369
theorem B9693827 : Blo 1178406 9693827 := bstep (se 1 (by rfl) ⟨7270370, by rfl⟩ : syracuseStep 9693827 = 14540741) B14540741
theorem B2984627 : Blo 1178406 2984627 := bstep (se 1 (by rfl) ⟨2238470, by rfl⟩ : syracuseStep 2984627 = 4476941) B4476941
theorem B5040899 : Blo 1178406 5040899 := bstep (se 1 (by rfl) ⟨3780674, by rfl⟩ : syracuseStep 5040899 = 7561349) B7561349
theorem B21537089 : Blo 1178406 21537089 := bstep (se 2 (by rfl) ⟨8076408, by rfl⟩ : syracuseStep 21537089 = 16152817) B16152817
theorem B2239321 : Blo 1178406 2239321 := bstep (se 2 (by rfl) ⟨839745, by rfl⟩ : syracuseStep 2239321 = 1679491) B1679491
theorem B5376941 : Blo 1178406 5376941 := bstep (se 3 (by rfl) ⟨1008176, by rfl⟩ : syracuseStep 5376941 = 2016353) B2016353
theorem B2984921 : Blo 1178406 2984921 := bstep (se 2 (by rfl) ⟨1119345, by rfl⟩ : syracuseStep 2984921 = 2238691) B2238691
theorem B9956357 : Blo 1178406 9956357 := bstep (se 4 (by rfl) ⟨933408, by rfl⟩ : syracuseStep 9956357 = 1866817) B1866817
theorem B4475969 : Blo 1178406 4475969 := bstep (se 2 (by rfl) ⟨1678488, by rfl⟩ : syracuseStep 4475969 = 3356977) B3356977
theorem B5041241 : Blo 1178406 5041241 := bstep (se 2 (by rfl) ⟨1890465, by rfl⟩ : syracuseStep 5041241 = 3780931) B3780931
theorem B8621149 : Blo 1178406 8621149 := bstep (se 3 (by rfl) ⟨1616465, by rfl⟩ : syracuseStep 8621149 = 3232931) B3232931
theorem B2124929 : Blo 1178406 2124929 := bstep (se 2 (by rfl) ⟨796848, by rfl⟩ : syracuseStep 2124929 = 1593697) B1593697
theorem B72682757 : Blo 1178406 72682757 := bstep (se 4 (by rfl) ⟨6814008, by rfl⟩ : syracuseStep 72682757 = 13628017) B13628017
theorem B6720833 : Blo 1178406 6720833 := bstep (se 2 (by rfl) ⟨2520312, by rfl⟩ : syracuseStep 6720833 = 5040625) B5040625
theorem B19123573 : Blo 1178406 19123573 := bstep (se 5 (by rfl) ⟨896417, by rfl⟩ : syracuseStep 19123573 = 1792835) B1792835
theorem B2239883 : Blo 1178406 2239883 := bstep (se 1 (by rfl) ⟨1679912, by rfl⟩ : syracuseStep 2239883 = 3359825) B3359825
theorem B13438385 : Blo 1178406 13438385 := bstep (se 2 (by rfl) ⟨5039394, by rfl⟩ : syracuseStep 13438385 = 10078789) B10078789
theorem B4779467 : Blo 1178406 4779467 := bstep (se 1 (by rfl) ⟨3584600, by rfl⟩ : syracuseStep 4779467 = 7169201) B7169201
theorem B6712793 : Blo 1178406 6712793 := bstep (se 2 (by rfl) ⟨2517297, by rfl⟩ : syracuseStep 6712793 = 5034595) B5034595
theorem B2518553 : Blo 1178406 2518553 := bstep (se 2 (by rfl) ⟨944457, by rfl⟩ : syracuseStep 2518553 = 1888915) B1888915
theorem B2240065 : Blo 1178406 2240065 := bstep (se 2 (by rfl) ⟨840024, by rfl⟩ : syracuseStep 2240065 = 1680049) B1680049
theorem B1592983 : Blo 1178406 1592983 := bstep (se 1 (by rfl) ⟨1194737, by rfl⟩ : syracuseStep 1592983 = 2389475) B2389475
theorem B3977153 : Blo 1178406 3977153 := bstep (se 2 (by rfl) ⟨1491432, by rfl⟩ : syracuseStep 3977153 = 2982865) B2982865
theorem B10072025 : Blo 1178406 10072025 := bstep (se 2 (by rfl) ⟨3777009, by rfl⟩ : syracuseStep 10072025 = 7554019) B7554019
theorem B5967917 : Blo 1178406 5967917 := bstep (se 3 (by rfl) ⟨1118984, by rfl⟩ : syracuseStep 5967917 = 2237969) B2237969
theorem B3780701 : Blo 1178406 3780701 := bstep (se 3 (by rfl) ⟨708881, by rfl⟩ : syracuseStep 3780701 = 1417763) B1417763
theorem B2519219 : Blo 1178406 2519219 := bstep (se 1 (by rfl) ⟨1889414, by rfl⟩ : syracuseStep 2519219 = 3778829) B3778829
theorem B2240779 : Blo 1178406 2240779 := bstep (se 1 (by rfl) ⟨1680584, by rfl⟩ : syracuseStep 2240779 = 3361169) B3361169
theorem B2240855 : Blo 1178406 2240855 := bstep (se 1 (by rfl) ⟨1680641, by rfl⟩ : syracuseStep 2240855 = 3361283) B3361283
theorem B4305241 : Blo 1178406 4305241 := bstep (se 2 (by rfl) ⟨1614465, by rfl⟩ : syracuseStep 4305241 = 3228931) B3228931
theorem B2691443 : Blo 1178406 2691443 := bstep (se 1 (by rfl) ⟨2018582, by rfl⟩ : syracuseStep 2691443 = 4037165) B4037165
theorem B4780505 : Blo 1178406 4780505 := bstep (se 2 (by rfl) ⟨1792689, by rfl⟩ : syracuseStep 4780505 = 3585379) B3585379
theorem B3977693 : Blo 1178406 3977693 := bstep (se 3 (by rfl) ⟨745817, by rfl⟩ : syracuseStep 3977693 = 1491635) B1491635
theorem B10080773 : Blo 1178406 10080773 := bstep (se 4 (by rfl) ⟨945072, by rfl⟩ : syracuseStep 10080773 = 1890145) B1890145
theorem B4477457 : Blo 1178406 4477457 := bstep (se 2 (by rfl) ⟨1679046, by rfl⟩ : syracuseStep 4477457 = 3358093) B3358093
theorem B2986571 : Blo 1178406 2986571 := bstep (se 1 (by rfl) ⟨2239928, by rfl⟩ : syracuseStep 2986571 = 4479857) B4479857
theorem B5378653 : Blo 1178406 5378653 := bstep (se 3 (by rfl) ⟨1008497, by rfl⟩ : syracuseStep 5378653 = 2016995) B2016995
theorem B15323741 : Blo 1178406 15323741 := bstep (se 3 (by rfl) ⟨2873201, by rfl⟩ : syracuseStep 15323741 = 5746403) B5746403
theorem B43037381 : Blo 1178406 43037381 := bstep (se 4 (by rfl) ⟨4034754, by rfl⟩ : syracuseStep 43037381 = 8069509) B8069509
theorem B25523009 : Blo 1178406 25523009 := bstep (se 2 (by rfl) ⟨9571128, by rfl⟩ : syracuseStep 25523009 = 19142257) B19142257
theorem B2724761 : Blo 1178406 2724761 := bstep (se 2 (by rfl) ⟨1021785, by rfl⟩ : syracuseStep 2724761 = 2043571) B2043571
theorem B4477913 : Blo 1178406 4477913 := bstep (se 2 (by rfl) ⟨1679217, by rfl⟩ : syracuseStep 4477913 = 3358435) B3358435
theorem B5379089 : Blo 1178406 5379089 := bstep (se 2 (by rfl) ⟨2017158, by rfl⟩ : syracuseStep 5379089 = 4034317) B4034317
theorem B30626885 : Blo 1178406 30626885 := bstep (se 4 (by rfl) ⟨2871270, by rfl⟩ : syracuseStep 30626885 = 5742541) B5742541
theorem B1258615 : Blo 1178406 1258615 := bstep (se 1 (by rfl) ⟨943961, by rfl⟩ : syracuseStep 1258615 = 1887923) B1887923
theorem B4248749 : Blo 1178406 4248749 := bstep (se 3 (by rfl) ⟨796640, by rfl⟩ : syracuseStep 4248749 = 1593281) B1593281
theorem B4478125 : Blo 1178406 4478125 := bstep (se 3 (by rfl) ⟨839648, by rfl⟩ : syracuseStep 4478125 = 1679297) B1679297
theorem B15119621 : Blo 1178406 15119621 := bstep (se 4 (by rfl) ⟨1417464, by rfl⟩ : syracuseStep 15119621 = 2834929) B2834929
theorem B2651417 : Blo 1178406 2651417 := bstep (se 2 (by rfl) ⟨994281, by rfl⟩ : syracuseStep 2651417 = 1988563) B1988563
theorem B6812993 : Blo 1178406 6812993 := bstep (se 2 (by rfl) ⟨2554872, by rfl⟩ : syracuseStep 6812993 = 5109745) B5109745
theorem B2725207 : Blo 1178406 2725207 := bstep (se 1 (by rfl) ⟨2043905, by rfl⟩ : syracuseStep 2725207 = 4087811) B4087811
theorem B2651507 : Blo 1178406 2651507 := bstep (se 1 (by rfl) ⟨1988630, by rfl⟩ : syracuseStep 2651507 = 3977261) B3977261
theorem B4846979 : Blo 1178406 4846979 := bstep (se 1 (by rfl) ⟨3635234, by rfl⟩ : syracuseStep 4846979 = 7270469) B7270469
theorem B2651543 : Blo 1178406 2651543 := bstep (se 1 (by rfl) ⟨1988657, by rfl⟩ : syracuseStep 2651543 = 3977315) B3977315
theorem B8959409 : Blo 1178406 8959409 := bstep (se 2 (by rfl) ⟨3359778, by rfl⟩ : syracuseStep 8959409 = 6719557) B6719557
theorem B4478429 : Blo 1178406 4478429 := bstep (se 3 (by rfl) ⟨839705, by rfl⟩ : syracuseStep 4478429 = 1679411) B1679411
theorem B2987543 : Blo 1178406 2987543 := bstep (se 1 (by rfl) ⟨2240657, by rfl⟩ : syracuseStep 2987543 = 4481315) B4481315
theorem B3356225 : Blo 1178406 3356225 := bstep (se 2 (by rfl) ⟨1258584, by rfl⟩ : syracuseStep 3356225 = 2517169) B2517169
theorem B2651723 : Blo 1178406 2651723 := bstep (se 1 (by rfl) ⟨1988792, by rfl⟩ : syracuseStep 2651723 = 3977585) B3977585
theorem B3978827 : Blo 1178406 3978827 := bstep (se 1 (by rfl) ⟨2984120, by rfl⟩ : syracuseStep 3978827 = 5968241) B5968241
theorem B16152157 : Blo 1178406 16152157 := bstep (se 3 (by rfl) ⟨3028529, by rfl⟩ : syracuseStep 16152157 = 6057059) B6057059
theorem B2651777 : Blo 1178406 2651777 := bstep (se 2 (by rfl) ⟨994416, by rfl⟩ : syracuseStep 2651777 = 1988833) B1988833
theorem B2520715 : Blo 1178406 2520715 := bstep (se 1 (by rfl) ⟨1890536, by rfl⟩ : syracuseStep 2520715 = 3781073) B3781073
theorem B21509873 : Blo 1178406 21509873 := bstep (se 2 (by rfl) ⟨8066202, by rfl⟩ : syracuseStep 21509873 = 16132405) B16132405
theorem B5035841 : Blo 1178406 5035841 := bstep (se 2 (by rfl) ⟨1888440, by rfl⟩ : syracuseStep 5035841 = 3776881) B3776881
theorem B2651993 : Blo 1178406 2651993 := bstep (se 2 (by rfl) ⟨994497, by rfl⟩ : syracuseStep 2651993 = 1988995) B1988995
theorem B3979097 : Blo 1178406 3979097 := bstep (se 2 (by rfl) ⟨1492161, by rfl⟩ : syracuseStep 3979097 = 2984323) B2984323
theorem B8959895 : Blo 1178406 8959895 := bstep (se 1 (by rfl) ⟨6719921, by rfl⟩ : syracuseStep 8959895 = 13439843) B13439843
theorem B1259435 : Blo 1178406 1259435 := bstep (se 1 (by rfl) ⟨944576, by rfl⟩ : syracuseStep 1259435 = 1889153) B1889153
theorem B2652083 : Blo 1178406 2652083 := bstep (se 1 (by rfl) ⟨1989062, by rfl⟩ : syracuseStep 2652083 = 3978125) B3978125
theorem B2652119 : Blo 1178406 2652119 := bstep (se 1 (by rfl) ⟨1989089, by rfl⟩ : syracuseStep 2652119 = 3978179) B3978179
theorem B11343833 : Blo 1178406 11343833 := bstep (se 2 (by rfl) ⟨4253937, by rfl⟩ : syracuseStep 11343833 = 8507875) B8507875
theorem B6715457 : Blo 1178406 6715457 := bstep (se 2 (by rfl) ⟨2518296, by rfl⟩ : syracuseStep 6715457 = 5036593) B5036593
theorem B4536395 : Blo 1178406 4536395 := bstep (se 1 (by rfl) ⟨3402296, by rfl⟩ : syracuseStep 4536395 = 6804593) B6804593
theorem B3356761 : Blo 1178406 3356761 := bstep (se 2 (by rfl) ⟨1258785, by rfl⟩ : syracuseStep 3356761 = 2517571) B2517571
theorem B2652299 : Blo 1178406 2652299 := bstep (se 1 (by rfl) ⟨1989224, by rfl⟩ : syracuseStep 2652299 = 3978449) B3978449
theorem B1988759 : Blo 1178406 1988759 := bstep (se 1 (by rfl) ⟨1491569, by rfl⟩ : syracuseStep 1988759 = 2983139) B2983139
theorem B2652353 : Blo 1178406 2652353 := bstep (se 2 (by rfl) ⟨994632, by rfl⟩ : syracuseStep 2652353 = 1989265) B1989265
theorem B1767641 : Blo 1178406 1767641 := bstep (se 2 (by rfl) ⟨662865, by rfl⟩ : syracuseStep 1767641 = 1325731) B1325731
theorem B1988887 : Blo 1178406 1988887 := bstep (se 1 (by rfl) ⟨1491665, by rfl⟩ : syracuseStep 1988887 = 2983331) B2983331
theorem B1767755 : Blo 1178406 1767755 := bstep (se 1 (by rfl) ⟨1325816, by rfl⟩ : syracuseStep 1767755 = 2651633) B2651633
theorem B1767767 : Blo 1178406 1767767 := bstep (se 1 (by rfl) ⟨1325825, by rfl⟩ : syracuseStep 1767767 = 2651651) B2651651
theorem B1767833 : Blo 1178406 1767833 := bstep (se 2 (by rfl) ⟨662937, by rfl⟩ : syracuseStep 1767833 = 1325875) B1325875
theorem B2652569 : Blo 1178406 2652569 := bstep (se 2 (by rfl) ⟨994713, by rfl⟩ : syracuseStep 2652569 = 1989427) B1989427
theorem B5454253 : Blo 1178406 5454253 := bstep (se 3 (by rfl) ⟨1022672, by rfl⟩ : syracuseStep 5454253 = 2045345) B2045345
theorem B2652659 : Blo 1178406 2652659 := bstep (se 1 (by rfl) ⟨1989494, by rfl⟩ : syracuseStep 2652659 = 3978989) B3978989
theorem B1767947 : Blo 1178406 1767947 := bstep (se 1 (by rfl) ⟨1325960, by rfl⟩ : syracuseStep 1767947 = 2651921) B2651921
theorem B1767959 : Blo 1178406 1767959 := bstep (se 1 (by rfl) ⟨1325969, by rfl⟩ : syracuseStep 1767959 = 2651939) B2651939
theorem B2652695 : Blo 1178406 2652695 := bstep (se 1 (by rfl) ⟨1989521, by rfl⟩ : syracuseStep 2652695 = 3979043) B3979043
theorem B3979799 : Blo 1178406 3979799 := bstep (se 1 (by rfl) ⟨2984849, by rfl⟩ : syracuseStep 3979799 = 5969699) B5969699
theorem B10074689 : Blo 1178406 10074689 := bstep (se 2 (by rfl) ⟨3778008, by rfl⟩ : syracuseStep 10074689 = 7556017) B7556017
theorem B1768025 : Blo 1178406 1768025 := bstep (se 2 (by rfl) ⟨663009, by rfl⟩ : syracuseStep 1768025 = 1326019) B1326019
theorem B1915531 : Blo 1178406 1915531 := bstep (se 1 (by rfl) ⟨1436648, by rfl⟩ : syracuseStep 1915531 = 2873297) B2873297
theorem B5454481 : Blo 1178406 5454481 := bstep (se 2 (by rfl) ⟨2045430, by rfl⟩ : syracuseStep 5454481 = 4090861) B4090861
theorem B1768139 : Blo 1178406 1768139 := bstep (se 1 (by rfl) ⟨1326104, by rfl⟩ : syracuseStep 1768139 = 2652209) B2652209
theorem B2652875 : Blo 1178406 2652875 := bstep (se 1 (by rfl) ⟨1989656, by rfl⟩ : syracuseStep 2652875 = 3979313) B3979313
theorem B1768151 : Blo 1178406 1768151 := bstep (se 1 (by rfl) ⟨1326113, by rfl⟩ : syracuseStep 1768151 = 2652227) B2652227
theorem B1325803 : Blo 1178406 1325803 := bstep (se 1 (by rfl) ⟨994352, by rfl⟩ : syracuseStep 1325803 = 1988705) B1988705
theorem B2652929 : Blo 1178406 2652929 := bstep (se 2 (by rfl) ⟨994848, by rfl⟩ : syracuseStep 2652929 = 1989697) B1989697
theorem B1702667 : Blo 1178406 1702667 := bstep (se 1 (by rfl) ⟨1277000, by rfl⟩ : syracuseStep 1702667 = 2554001) B2554001
theorem B1768217 : Blo 1178406 1768217 := bstep (se 2 (by rfl) ⟨663081, by rfl⟩ : syracuseStep 1768217 = 1326163) B1326163
theorem B1178411 : Blo 1178406 1178411 := bstep (se 1 (by rfl) ⟨883808, by rfl⟩ : syracuseStep 1178411 = 1767617) B1767617
theorem B1178423 : Blo 1178406 1178423 := bstep (se 1 (by rfl) ⟨883817, by rfl⟩ : syracuseStep 1178423 = 1767635) B1767635
theorem B1178443 : Blo 1178406 1178443 := bstep (se 1 (by rfl) ⟨883832, by rfl⟩ : syracuseStep 1178443 = 1767665) B1767665
theorem B1178455 : Blo 1178406 1178455 := bstep (se 1 (by rfl) ⟨883841, by rfl⟩ : syracuseStep 1178455 = 1767683) B1767683
theorem B1325911 : Blo 1178406 1325911 := bstep (se 1 (by rfl) ⟨994433, by rfl⟩ : syracuseStep 1325911 = 1988867) B1988867
theorem B3152729 : Blo 1178406 3152729 := bstep (se 2 (by rfl) ⟨1182273, by rfl⟩ : syracuseStep 3152729 = 2364547) B2364547
theorem B24214373 : Blo 1178406 24214373 := bstep (se 4 (by rfl) ⟨2270097, by rfl⟩ : syracuseStep 24214373 = 4540195) B4540195
theorem B1178475 : Blo 1178406 1178475 := bstep (se 1 (by rfl) ⟨883856, by rfl⟩ : syracuseStep 1178475 = 1767713) B1767713
theorem B1178487 : Blo 1178406 1178487 := bstep (se 1 (by rfl) ⟨883865, by rfl⟩ : syracuseStep 1178487 = 1767731) B1767731
theorem B1178507 : Blo 1178406 1178507 := bstep (se 1 (by rfl) ⟨883880, by rfl⟩ : syracuseStep 1178507 = 1767761) B1767761
theorem B1768331 : Blo 1178406 1768331 := bstep (se 1 (by rfl) ⟨1326248, by rfl⟩ : syracuseStep 1768331 = 2652497) B2652497
theorem B1989515 : Blo 1178406 1989515 := bstep (se 1 (by rfl) ⟨1492136, by rfl⟩ : syracuseStep 1989515 = 2984273) B2984273
theorem B1178519 : Blo 1178406 1178519 := bstep (se 1 (by rfl) ⟨883889, by rfl⟩ : syracuseStep 1178519 = 1767779) B1767779
theorem B1768343 : Blo 1178406 1768343 := bstep (se 1 (by rfl) ⟨1326257, by rfl⟩ : syracuseStep 1768343 = 2652515) B2652515
theorem B1178539 : Blo 1178406 1178539 := bstep (se 1 (by rfl) ⟨883904, by rfl⟩ : syracuseStep 1178539 = 1767809) B1767809
theorem B1178551 : Blo 1178406 1178551 := bstep (se 1 (by rfl) ⟨883913, by rfl⟩ : syracuseStep 1178551 = 1767827) B1767827
theorem B1178571 : Blo 1178406 1178571 := bstep (se 1 (by rfl) ⟨883928, by rfl⟩ : syracuseStep 1178571 = 1767857) B1767857
theorem B1178583 : Blo 1178406 1178583 := bstep (se 1 (by rfl) ⟨883937, by rfl⟩ : syracuseStep 1178583 = 1767875) B1767875
theorem B1768409 : Blo 1178406 1768409 := bstep (se 2 (by rfl) ⟨663153, by rfl⟩ : syracuseStep 1768409 = 1326307) B1326307
theorem B2653145 : Blo 1178406 2653145 := bstep (se 2 (by rfl) ⟨994929, by rfl⟩ : syracuseStep 2653145 = 1989859) B1989859
theorem B1178603 : Blo 1178406 1178603 := bstep (se 1 (by rfl) ⟨883952, by rfl⟩ : syracuseStep 1178603 = 1767905) B1767905
theorem B1178615 : Blo 1178406 1178615 := bstep (se 1 (by rfl) ⟨883961, by rfl⟩ : syracuseStep 1178615 = 1767923) B1767923
theorem B1178635 : Blo 1178406 1178635 := bstep (se 1 (by rfl) ⟨883976, by rfl⟩ : syracuseStep 1178635 = 1767953) B1767953
theorem B1326091 : Blo 1178406 1326091 := bstep (se 1 (by rfl) ⟨994568, by rfl⟩ : syracuseStep 1326091 = 1989137) B1989137
theorem B1989643 : Blo 1178406 1989643 := bstep (se 1 (by rfl) ⟨1492232, by rfl⟩ : syracuseStep 1989643 = 2984465) B2984465
theorem B1178647 : Blo 1178406 1178647 := bstep (se 1 (by rfl) ⟨883985, by rfl⟩ : syracuseStep 1178647 = 1767971) B1767971
theorem B1178667 : Blo 1178406 1178667 := bstep (se 1 (by rfl) ⟨884000, by rfl⟩ : syracuseStep 1178667 = 1768001) B1768001
theorem B2653235 : Blo 1178406 2653235 := bstep (se 1 (by rfl) ⟨1989926, by rfl⟩ : syracuseStep 2653235 = 3979853) B3979853
theorem B3980339 : Blo 1178406 3980339 := bstep (se 1 (by rfl) ⟨2985254, by rfl⟩ : syracuseStep 3980339 = 5970509) B5970509
theorem B1178679 : Blo 1178406 1178679 := bstep (se 1 (by rfl) ⟨884009, by rfl⟩ : syracuseStep 1178679 = 1768019) B1768019
theorem B1178699 : Blo 1178406 1178699 := bstep (se 1 (by rfl) ⟨884024, by rfl⟩ : syracuseStep 1178699 = 1768049) B1768049
theorem B1768523 : Blo 1178406 1768523 := bstep (se 1 (by rfl) ⟨1326392, by rfl⟩ : syracuseStep 1768523 = 2652785) B2652785
theorem B1178711 : Blo 1178406 1178711 := bstep (se 1 (by rfl) ⟨884033, by rfl⟩ : syracuseStep 1178711 = 1768067) B1768067
theorem B1768535 : Blo 1178406 1768535 := bstep (se 1 (by rfl) ⟨1326401, by rfl⟩ : syracuseStep 1768535 = 2652803) B2652803
theorem B2653271 : Blo 1178406 2653271 := bstep (se 1 (by rfl) ⟨1989953, by rfl⟩ : syracuseStep 2653271 = 3979907) B3979907
theorem B1178731 : Blo 1178406 1178731 := bstep (se 1 (by rfl) ⟨884048, by rfl⟩ : syracuseStep 1178731 = 1768097) B1768097
theorem B1178743 : Blo 1178406 1178743 := bstep (se 1 (by rfl) ⟨884057, by rfl⟩ : syracuseStep 1178743 = 1768115) B1768115
theorem B1326199 : Blo 1178406 1326199 := bstep (se 1 (by rfl) ⟨994649, by rfl⟩ : syracuseStep 1326199 = 1989299) B1989299
theorem B7560323 : Blo 1178406 7560323 := bstep (se 1 (by rfl) ⟨5670242, by rfl⟩ : syracuseStep 7560323 = 11340485) B11340485
theorem B1178763 : Blo 1178406 1178763 := bstep (se 1 (by rfl) ⟨884072, by rfl⟩ : syracuseStep 1178763 = 1768145) B1768145
theorem B1178775 : Blo 1178406 1178775 := bstep (se 1 (by rfl) ⟨884081, by rfl⟩ : syracuseStep 1178775 = 1768163) B1768163
theorem B1989785 : Blo 1178406 1989785 := bstep (se 2 (by rfl) ⟨746169, by rfl⟩ : syracuseStep 1989785 = 1492339) B1492339
theorem B1768601 : Blo 1178406 1768601 := bstep (se 2 (by rfl) ⟨663225, by rfl⟩ : syracuseStep 1768601 = 1326451) B1326451
theorem B1178795 : Blo 1178406 1178795 := bstep (se 1 (by rfl) ⟨884096, by rfl⟩ : syracuseStep 1178795 = 1768193) B1768193
theorem B1178807 : Blo 1178406 1178807 := bstep (se 1 (by rfl) ⟨884105, by rfl⟩ : syracuseStep 1178807 = 1768211) B1768211
theorem B1178827 : Blo 1178406 1178827 := bstep (se 1 (by rfl) ⟨884120, by rfl⟩ : syracuseStep 1178827 = 1768241) B1768241
theorem B1178839 : Blo 1178406 1178839 := bstep (se 1 (by rfl) ⟨884129, by rfl⟩ : syracuseStep 1178839 = 1768259) B1768259
theorem B1178859 : Blo 1178406 1178859 := bstep (se 1 (by rfl) ⟨884144, by rfl⟩ : syracuseStep 1178859 = 1768289) B1768289
theorem B1178871 : Blo 1178406 1178871 := bstep (se 1 (by rfl) ⟨884153, by rfl⟩ : syracuseStep 1178871 = 1768307) B1768307
theorem B1178891 : Blo 1178406 1178891 := bstep (se 1 (by rfl) ⟨884168, by rfl⟩ : syracuseStep 1178891 = 1768337) B1768337
theorem B1768715 : Blo 1178406 1768715 := bstep (se 1 (by rfl) ⟨1326536, by rfl⟩ : syracuseStep 1768715 = 2653073) B2653073
theorem B2653451 : Blo 1178406 2653451 := bstep (se 1 (by rfl) ⟨1990088, by rfl⟩ : syracuseStep 2653451 = 3980177) B3980177
theorem B5037329 : Blo 1178406 5037329 := bstep (se 2 (by rfl) ⟨1888998, by rfl⟩ : syracuseStep 5037329 = 3777997) B3777997
theorem B1178903 : Blo 1178406 1178903 := bstep (se 1 (by rfl) ⟨884177, by rfl⟩ : syracuseStep 1178903 = 1768355) B1768355
theorem B1768727 : Blo 1178406 1768727 := bstep (se 1 (by rfl) ⟨1326545, by rfl⟩ : syracuseStep 1768727 = 2653091) B2653091
theorem B1989913 : Blo 1178406 1989913 := bstep (se 2 (by rfl) ⟨746217, by rfl⟩ : syracuseStep 1989913 = 1492435) B1492435
theorem B1178923 : Blo 1178406 1178923 := bstep (se 1 (by rfl) ⟨884192, by rfl⟩ : syracuseStep 1178923 = 1768385) B1768385
theorem B1326379 : Blo 1178406 1326379 := bstep (se 1 (by rfl) ⟨994784, by rfl⟩ : syracuseStep 1326379 = 1989569) B1989569
theorem B1178935 : Blo 1178406 1178935 := bstep (se 1 (by rfl) ⟨884201, by rfl⟩ : syracuseStep 1178935 = 1768403) B1768403
theorem B2653505 : Blo 1178406 2653505 := bstep (se 2 (by rfl) ⟨995064, by rfl⟩ : syracuseStep 2653505 = 1990129) B1990129
theorem B3980609 : Blo 1178406 3980609 := bstep (se 2 (by rfl) ⟨1492728, by rfl⟩ : syracuseStep 3980609 = 2985457) B2985457
theorem B1178955 : Blo 1178406 1178955 := bstep (se 1 (by rfl) ⟨884216, by rfl⟩ : syracuseStep 1178955 = 1768433) B1768433
theorem B1416523 : Blo 1178406 1416523 := bstep (se 1 (by rfl) ⟨1062392, by rfl⟩ : syracuseStep 1416523 = 2124785) B2124785
theorem B1178967 : Blo 1178406 1178967 := bstep (se 1 (by rfl) ⟨884225, by rfl⟩ : syracuseStep 1178967 = 1768451) B1768451
theorem B1768793 : Blo 1178406 1768793 := bstep (se 2 (by rfl) ⟨663297, by rfl⟩ : syracuseStep 1768793 = 1326595) B1326595
theorem B1178987 : Blo 1178406 1178987 := bstep (se 1 (by rfl) ⟨884240, by rfl⟩ : syracuseStep 1178987 = 1768481) B1768481
theorem B1178999 : Blo 1178406 1178999 := bstep (se 1 (by rfl) ⟨884249, by rfl⟩ : syracuseStep 1178999 = 1768499) B1768499
theorem B1179019 : Blo 1178406 1179019 := bstep (se 1 (by rfl) ⟨884264, by rfl⟩ : syracuseStep 1179019 = 1768529) B1768529
theorem B1179031 : Blo 1178406 1179031 := bstep (se 1 (by rfl) ⟨884273, by rfl⟩ : syracuseStep 1179031 = 1768547) B1768547
theorem B1326487 : Blo 1178406 1326487 := bstep (se 1 (by rfl) ⟨994865, by rfl⟩ : syracuseStep 1326487 = 1989731) B1989731
theorem B1678745 : Blo 1178406 1678745 := bstep (se 2 (by rfl) ⟨629529, by rfl⟩ : syracuseStep 1678745 = 1259059) B1259059
theorem B1179051 : Blo 1178406 1179051 := bstep (se 1 (by rfl) ⟨884288, by rfl⟩ : syracuseStep 1179051 = 1768577) B1768577
theorem B16997809 : Blo 1178406 16997809 := bstep (se 2 (by rfl) ⟨6374178, by rfl⟩ : syracuseStep 16997809 = 12748357) B12748357
theorem B1179063 : Blo 1178406 1179063 := bstep (se 1 (by rfl) ⟨884297, by rfl⟩ : syracuseStep 1179063 = 1768595) B1768595
theorem B1179083 : Blo 1178406 1179083 := bstep (se 1 (by rfl) ⟨884312, by rfl⟩ : syracuseStep 1179083 = 1768625) B1768625
theorem B1768907 : Blo 1178406 1768907 := bstep (se 1 (by rfl) ⟨1326680, by rfl⟩ : syracuseStep 1768907 = 2653361) B2653361
theorem B1179095 : Blo 1178406 1179095 := bstep (se 1 (by rfl) ⟨884321, by rfl⟩ : syracuseStep 1179095 = 1768643) B1768643
theorem B1768919 : Blo 1178406 1768919 := bstep (se 1 (by rfl) ⟨1326689, by rfl⟩ : syracuseStep 1768919 = 2653379) B2653379
theorem B7167449 : Blo 1178406 7167449 := bstep (se 2 (by rfl) ⟨2687793, by rfl⟩ : syracuseStep 7167449 = 5375587) B5375587
theorem B12107225 : Blo 1178406 12107225 := bstep (se 2 (by rfl) ⟨4540209, by rfl⟩ : syracuseStep 12107225 = 9080419) B9080419
theorem B1179115 : Blo 1178406 1179115 := bstep (se 1 (by rfl) ⟨884336, by rfl⟩ : syracuseStep 1179115 = 1768673) B1768673
theorem B1179127 : Blo 1178406 1179127 := bstep (se 1 (by rfl) ⟨884345, by rfl⟩ : syracuseStep 1179127 = 1768691) B1768691
theorem B4783619 : Blo 1178406 4783619 := bstep (se 1 (by rfl) ⟨3587714, by rfl⟩ : syracuseStep 4783619 = 7175429) B7175429
theorem B1179147 : Blo 1178406 1179147 := bstep (se 1 (by rfl) ⟨884360, by rfl⟩ : syracuseStep 1179147 = 1768721) B1768721
theorem B1179159 : Blo 1178406 1179159 := bstep (se 1 (by rfl) ⟨884369, by rfl⟩ : syracuseStep 1179159 = 1768739) B1768739
theorem B1768985 : Blo 1178406 1768985 := bstep (se 2 (by rfl) ⟨663369, by rfl⟩ : syracuseStep 1768985 = 1326739) B1326739
theorem B2653721 : Blo 1178406 2653721 := bstep (se 2 (by rfl) ⟨995145, by rfl⟩ : syracuseStep 2653721 = 1990291) B1990291
theorem B1179179 : Blo 1178406 1179179 := bstep (se 1 (by rfl) ⟨884384, by rfl⟩ : syracuseStep 1179179 = 1768769) B1768769
theorem B5668397 : Blo 1178406 5668397 := bstep (se 3 (by rfl) ⟨1062824, by rfl⟩ : syracuseStep 5668397 = 2125649) B2125649
theorem B1179191 : Blo 1178406 1179191 := bstep (se 1 (by rfl) ⟨884393, by rfl⟩ : syracuseStep 1179191 = 1768787) B1768787
theorem B1179211 : Blo 1178406 1179211 := bstep (se 1 (by rfl) ⟨884408, by rfl⟩ : syracuseStep 1179211 = 1768817) B1768817
theorem B1326667 : Blo 1178406 1326667 := bstep (se 1 (by rfl) ⟨995000, by rfl⟩ : syracuseStep 1326667 = 1990001) B1990001
theorem B1179223 : Blo 1178406 1179223 := bstep (se 1 (by rfl) ⟨884417, by rfl⟩ : syracuseStep 1179223 = 1768835) B1768835
theorem B1179243 : Blo 1178406 1179243 := bstep (se 1 (by rfl) ⟨884432, by rfl⟩ : syracuseStep 1179243 = 1768865) B1768865
theorem B2653811 : Blo 1178406 2653811 := bstep (se 1 (by rfl) ⟨1990358, by rfl⟩ : syracuseStep 2653811 = 3980717) B3980717
theorem B1179255 : Blo 1178406 1179255 := bstep (se 1 (by rfl) ⟨884441, by rfl⟩ : syracuseStep 1179255 = 1768883) B1768883
theorem B1179275 : Blo 1178406 1179275 := bstep (se 1 (by rfl) ⟨884456, by rfl⟩ : syracuseStep 1179275 = 1768913) B1768913
theorem B1769099 : Blo 1178406 1769099 := bstep (se 1 (by rfl) ⟨1326824, by rfl⟩ : syracuseStep 1769099 = 2653649) B2653649
theorem B1179287 : Blo 1178406 1179287 := bstep (se 1 (by rfl) ⟨884465, by rfl⟩ : syracuseStep 1179287 = 1768931) B1768931
theorem B1769111 : Blo 1178406 1769111 := bstep (se 1 (by rfl) ⟨1326833, by rfl⟩ : syracuseStep 1769111 = 2653667) B2653667
theorem B2653847 : Blo 1178406 2653847 := bstep (se 1 (by rfl) ⟨1990385, by rfl⟩ : syracuseStep 2653847 = 3980771) B3980771
theorem B1179307 : Blo 1178406 1179307 := bstep (se 1 (by rfl) ⟨884480, by rfl⟩ : syracuseStep 1179307 = 1768961) B1768961
theorem B1179319 : Blo 1178406 1179319 := bstep (se 1 (by rfl) ⟨884489, by rfl⟩ : syracuseStep 1179319 = 1768979) B1768979
theorem B1326775 : Blo 1178406 1326775 := bstep (se 1 (by rfl) ⟨995081, by rfl⟩ : syracuseStep 1326775 = 1990163) B1990163
theorem B1179339 : Blo 1178406 1179339 := bstep (se 1 (by rfl) ⟨884504, by rfl⟩ : syracuseStep 1179339 = 1769009) B1769009
theorem B1179351 : Blo 1178406 1179351 := bstep (se 1 (by rfl) ⟨884513, by rfl⟩ : syracuseStep 1179351 = 1769027) B1769027
theorem B1769177 : Blo 1178406 1769177 := bstep (se 2 (by rfl) ⟨663441, by rfl⟩ : syracuseStep 1769177 = 1326883) B1326883
theorem B1179371 : Blo 1178406 1179371 := bstep (se 1 (by rfl) ⟨884528, by rfl⟩ : syracuseStep 1179371 = 1769057) B1769057
theorem B1179383 : Blo 1178406 1179383 := bstep (se 1 (by rfl) ⟨884537, by rfl⟩ : syracuseStep 1179383 = 1769075) B1769075
theorem B1179403 : Blo 1178406 1179403 := bstep (se 1 (by rfl) ⟨884552, by rfl⟩ : syracuseStep 1179403 = 1769105) B1769105
theorem B1179415 : Blo 1178406 1179415 := bstep (se 1 (by rfl) ⟨884561, by rfl⟩ : syracuseStep 1179415 = 1769123) B1769123
theorem B1179435 : Blo 1178406 1179435 := bstep (se 1 (by rfl) ⟨884576, by rfl⟩ : syracuseStep 1179435 = 1769153) B1769153
theorem B1179447 : Blo 1178406 1179447 := bstep (se 1 (by rfl) ⟨884585, by rfl⟩ : syracuseStep 1179447 = 1769171) B1769171
theorem B1179467 : Blo 1178406 1179467 := bstep (se 1 (by rfl) ⟨884600, by rfl⟩ : syracuseStep 1179467 = 1769201) B1769201
theorem B1769291 : Blo 1178406 1769291 := bstep (se 1 (by rfl) ⟨1326968, by rfl⟩ : syracuseStep 1769291 = 2653937) B2653937
theorem B2654027 : Blo 1178406 2654027 := bstep (se 1 (by rfl) ⟨1990520, by rfl⟩ : syracuseStep 2654027 = 3981041) B3981041
theorem B1179479 : Blo 1178406 1179479 := bstep (se 1 (by rfl) ⟨884609, by rfl⟩ : syracuseStep 1179479 = 1769219) B1769219
theorem B1769303 : Blo 1178406 1769303 := bstep (se 1 (by rfl) ⟨1326977, by rfl⟩ : syracuseStep 1769303 = 2653955) B2653955
theorem B1990487 : Blo 1178406 1990487 := bstep (se 1 (by rfl) ⟨1492865, by rfl⟩ : syracuseStep 1990487 = 2985731) B2985731
theorem B3981149 : Blo 1178406 3981149 := bstep (se 3 (by rfl) ⟨746465, by rfl⟩ : syracuseStep 3981149 = 1492931) B1492931
theorem B5971805 : Blo 1178406 5971805 := bstep (se 3 (by rfl) ⟨1119713, by rfl⟩ : syracuseStep 5971805 = 2239427) B2239427
theorem B51707747 : Blo 1178406 51707747 := bstep (se 1 (by rfl) ⟨38780810, by rfl⟩ : syracuseStep 51707747 = 77561621) B77561621
theorem B1179499 : Blo 1178406 1179499 := bstep (se 1 (by rfl) ⟨884624, by rfl⟩ : syracuseStep 1179499 = 1769249) B1769249
theorem B1326955 : Blo 1178406 1326955 := bstep (se 1 (by rfl) ⟨995216, by rfl⟩ : syracuseStep 1326955 = 1990433) B1990433
theorem B1179511 : Blo 1178406 1179511 := bstep (se 1 (by rfl) ⟨884633, by rfl⟩ : syracuseStep 1179511 = 1769267) B1769267
theorem B2654081 : Blo 1178406 2654081 := bstep (se 2 (by rfl) ⟨995280, by rfl⟩ : syracuseStep 2654081 = 1990561) B1990561
theorem B1179531 : Blo 1178406 1179531 := bstep (se 1 (by rfl) ⟨884648, by rfl⟩ : syracuseStep 1179531 = 1769297) B1769297
theorem B1179543 : Blo 1178406 1179543 := bstep (se 1 (by rfl) ⟨884657, by rfl⟩ : syracuseStep 1179543 = 1769315) B1769315
theorem B1769369 : Blo 1178406 1769369 := bstep (se 2 (by rfl) ⟨663513, by rfl⟩ : syracuseStep 1769369 = 1327027) B1327027
theorem B1179563 : Blo 1178406 1179563 := bstep (se 1 (by rfl) ⟨884672, by rfl⟩ : syracuseStep 1179563 = 1769345) B1769345
theorem B1179575 : Blo 1178406 1179575 := bstep (se 1 (by rfl) ⟨884681, by rfl⟩ : syracuseStep 1179575 = 1769363) B1769363
theorem B1179595 : Blo 1178406 1179595 := bstep (se 1 (by rfl) ⟨884696, by rfl⟩ : syracuseStep 1179595 = 1769393) B1769393
theorem B1179607 : Blo 1178406 1179607 := bstep (se 1 (by rfl) ⟨884705, by rfl⟩ : syracuseStep 1179607 = 1769411) B1769411
theorem B1327063 : Blo 1178406 1327063 := bstep (se 1 (by rfl) ⟨995297, by rfl⟩ : syracuseStep 1327063 = 1990595) B1990595
theorem B1990615 : Blo 1178406 1990615 := bstep (se 1 (by rfl) ⟨1492961, by rfl⟩ : syracuseStep 1990615 = 2985923) B2985923
theorem B3358685 : Blo 1178406 3358685 := bstep (se 3 (by rfl) ⟨629753, by rfl⟩ : syracuseStep 3358685 = 1259507) B1259507
theorem B1179627 : Blo 1178406 1179627 := bstep (se 1 (by rfl) ⟨884720, by rfl⟩ : syracuseStep 1179627 = 1769441) B1769441
theorem B1179639 : Blo 1178406 1179639 := bstep (se 1 (by rfl) ⟨884729, by rfl⟩ : syracuseStep 1179639 = 1769459) B1769459
theorem B1179655 : Blo 1178406 1179655 := bstep (se 1 (by rfl) ⟨884741, by rfl⟩ : syracuseStep 1179655 = 1769483) B1769483
theorem B1179663 : Blo 1178406 1179663 := bstep (se 1 (by rfl) ⟨884747, by rfl⟩ : syracuseStep 1179663 = 1769495) B1769495
theorem B14344237 : Blo 1178406 14344237 := bstep (se 3 (by rfl) ⟨2689544, by rfl⟩ : syracuseStep 14344237 = 5379089) B5379089
theorem B1769531 : Blo 1178406 1769531 := bstep (se 1 (by rfl) ⟨1327148, by rfl⟩ : syracuseStep 1769531 = 2654297) B2654297
theorem B1179707 : Blo 1178406 1179707 := bstep (se 1 (by rfl) ⟨884780, by rfl⟩ : syracuseStep 1179707 = 1769561) B1769561
theorem B1769591 : Blo 1178406 1769591 := bstep (se 1 (by rfl) ⟨1327193, by rfl⟩ : syracuseStep 1769591 = 2654387) B2654387
theorem B1179783 : Blo 1178406 1179783 := bstep (se 1 (by rfl) ⟨884837, by rfl⟩ : syracuseStep 1179783 = 1769675) B1769675
theorem B1769615 : Blo 1178406 1769615 := bstep (se 1 (by rfl) ⟨1327211, by rfl⟩ : syracuseStep 1769615 = 2654423) B2654423
theorem B1179791 : Blo 1178406 1179791 := bstep (se 1 (by rfl) ⟨884843, by rfl⟩ : syracuseStep 1179791 = 1769687) B1769687
theorem B1769657 : Blo 1178406 1769657 := bstep (se 2 (by rfl) ⟨663621, by rfl⟩ : syracuseStep 1769657 = 1327243) B1327243
theorem B1179835 : Blo 1178406 1179835 := bstep (se 1 (by rfl) ⟨884876, by rfl⟩ : syracuseStep 1179835 = 1769753) B1769753
theorem B1794295 : Blo 1178406 1794295 := bstep (se 1 (by rfl) ⟨1345721, by rfl⟩ : syracuseStep 1794295 = 2691443) B2691443
theorem B4251905 : Blo 1178406 4251905 := bstep (se 2 (by rfl) ⟨1594464, by rfl⟩ : syracuseStep 4251905 = 3188929) B3188929
theorem B1769735 : Blo 1178406 1769735 := bstep (se 1 (by rfl) ⟨1327301, by rfl⟩ : syracuseStep 1769735 = 2654603) B2654603
theorem B1179911 : Blo 1178406 1179911 := bstep (se 1 (by rfl) ⟨884933, by rfl⟩ : syracuseStep 1179911 = 1769867) B1769867
theorem B1179919 : Blo 1178406 1179919 := bstep (se 1 (by rfl) ⟨884939, by rfl⟩ : syracuseStep 1179919 = 1769879) B1769879
theorem B1769771 : Blo 1178406 1769771 := bstep (se 1 (by rfl) ⟨1327328, by rfl⟩ : syracuseStep 1769771 = 2654657) B2654657
theorem B12271931 : Blo 1178406 12271931 := bstep (se 1 (by rfl) ⟨9203948, by rfl⟩ : syracuseStep 12271931 = 18407897) B18407897
theorem B1179963 : Blo 1178406 1179963 := bstep (se 1 (by rfl) ⟨884972, by rfl⟩ : syracuseStep 1179963 = 1769945) B1769945
theorem B1769801 : Blo 1178406 1769801 := bstep (se 2 (by rfl) ⟨663675, by rfl⟩ : syracuseStep 1769801 = 1327351) B1327351
theorem B1991047 : Blo 1178406 1991047 := bstep (se 1 (by rfl) ⟨1493285, by rfl⟩ : syracuseStep 1991047 = 2986571) B2986571
theorem B1327495 : Blo 1178406 1327495 := bstep (se 1 (by rfl) ⟨995621, by rfl⟩ : syracuseStep 1327495 = 1991243) B1991243
theorem B1180039 : Blo 1178406 1180039 := bstep (se 1 (by rfl) ⟨885029, by rfl⟩ : syracuseStep 1180039 = 1770059) B1770059
theorem B1180047 : Blo 1178406 1180047 := bstep (se 1 (by rfl) ⟨885035, by rfl⟩ : syracuseStep 1180047 = 1770071) B1770071
theorem B10215827 : Blo 1178406 10215827 := bstep (se 1 (by rfl) ⟨7661870, by rfl⟩ : syracuseStep 10215827 = 15323741) B15323741
theorem B1769915 : Blo 1178406 1769915 := bstep (se 1 (by rfl) ⟨1327436, by rfl⟩ : syracuseStep 1769915 = 2654873) B2654873
theorem B1180091 : Blo 1178406 1180091 := bstep (se 1 (by rfl) ⟨885068, by rfl⟩ : syracuseStep 1180091 = 1770137) B1770137
theorem B6373835 : Blo 1178406 6373835 := bstep (se 1 (by rfl) ⟨4780376, by rfl⟩ : syracuseStep 6373835 = 9560753) B9560753
theorem B6717917 : Blo 1178406 6717917 := bstep (se 3 (by rfl) ⟨1259609, by rfl⟩ : syracuseStep 6717917 = 2519219) B2519219
theorem B1769975 : Blo 1178406 1769975 := bstep (se 1 (by rfl) ⟨1327481, by rfl⟩ : syracuseStep 1769975 = 2654963) B2654963
theorem B1491463 : Blo 1178406 1491463 := bstep (se 1 (by rfl) ⟨1118597, by rfl⟩ : syracuseStep 1491463 = 2237195) B2237195
theorem B1180167 : Blo 1178406 1180167 := bstep (se 1 (by rfl) ⟨885125, by rfl⟩ : syracuseStep 1180167 = 1770251) B1770251
theorem B1769999 : Blo 1178406 1769999 := bstep (se 1 (by rfl) ⟨1327499, by rfl⟩ : syracuseStep 1769999 = 2654999) B2654999
theorem B1180175 : Blo 1178406 1180175 := bstep (se 1 (by rfl) ⟨885131, by rfl⟩ : syracuseStep 1180175 = 1770263) B1770263
theorem B17015339 : Blo 1178406 17015339 := bstep (se 1 (by rfl) ⟨12761504, by rfl⟩ : syracuseStep 17015339 = 25523009) B25523009
theorem B1770041 : Blo 1178406 1770041 := bstep (se 2 (by rfl) ⟨663765, by rfl⟩ : syracuseStep 1770041 = 1327531) B1327531
theorem B1327675 : Blo 1178406 1327675 := bstep (se 1 (by rfl) ⟨995756, by rfl⟩ : syracuseStep 1327675 = 1991513) B1991513
theorem B1180219 : Blo 1178406 1180219 := bstep (se 1 (by rfl) ⟨885164, by rfl⟩ : syracuseStep 1180219 = 1770329) B1770329
theorem B13435469 : Blo 1178406 13435469 := bstep (se 3 (by rfl) ⟨2519150, by rfl⟩ : syracuseStep 13435469 = 5038301) B5038301
theorem B2654855 : Blo 1178406 2654855 := bstep (se 1 (by rfl) ⟨1991141, by rfl⟩ : syracuseStep 2654855 = 3982283) B3982283
theorem B1770119 : Blo 1178406 1770119 := bstep (se 1 (by rfl) ⟨1327589, by rfl⟩ : syracuseStep 1770119 = 2655179) B2655179
theorem B1180295 : Blo 1178406 1180295 := bstep (se 1 (by rfl) ⟨885221, by rfl⟩ : syracuseStep 1180295 = 1770443) B1770443
theorem B1180303 : Blo 1178406 1180303 := bstep (se 1 (by rfl) ⟨885227, by rfl⟩ : syracuseStep 1180303 = 1770455) B1770455
theorem B1770155 : Blo 1178406 1770155 := bstep (se 1 (by rfl) ⟨1327616, by rfl⟩ : syracuseStep 1770155 = 2655233) B2655233
theorem B1180347 : Blo 1178406 1180347 := bstep (se 1 (by rfl) ⟨885260, by rfl⟩ : syracuseStep 1180347 = 1770521) B1770521
theorem B1770185 : Blo 1178406 1770185 := bstep (se 2 (by rfl) ⟨663819, by rfl⟩ : syracuseStep 1770185 = 1327639) B1327639
theorem B10216165 : Blo 1178406 10216165 := bstep (se 4 (by rfl) ⟨957765, by rfl⟩ : syracuseStep 10216165 = 1915531) B1915531
theorem B2655035 : Blo 1178406 2655035 := bstep (se 1 (by rfl) ⟨1991276, by rfl⟩ : syracuseStep 2655035 = 3982553) B3982553
theorem B1770299 : Blo 1178406 1770299 := bstep (se 1 (by rfl) ⟨1327724, by rfl⟩ : syracuseStep 1770299 = 2655449) B2655449
theorem B1770359 : Blo 1178406 1770359 := bstep (se 1 (by rfl) ⟨1327769, by rfl⟩ : syracuseStep 1770359 = 2655539) B2655539
theorem B1770383 : Blo 1178406 1770383 := bstep (se 1 (by rfl) ⟨1327787, by rfl⟩ : syracuseStep 1770383 = 2655575) B2655575
theorem B2655161 : Blo 1178406 2655161 := bstep (se 2 (by rfl) ⟨995685, by rfl⟩ : syracuseStep 2655161 = 1991371) B1991371
theorem B1770425 : Blo 1178406 1770425 := bstep (se 2 (by rfl) ⟨663909, by rfl⟩ : syracuseStep 1770425 = 1327819) B1327819
theorem B5972939 : Blo 1178406 5972939 := bstep (se 1 (by rfl) ⟨4479704, by rfl⟩ : syracuseStep 5972939 = 8959409) B8959409
theorem B1491959 : Blo 1178406 1491959 := bstep (se 1 (by rfl) ⟨1118969, by rfl⟩ : syracuseStep 1491959 = 2237939) B2237939
theorem B1770503 : Blo 1178406 1770503 := bstep (se 1 (by rfl) ⟨1327877, by rfl⟩ : syracuseStep 1770503 = 2655755) B2655755
theorem B1991695 : Blo 1178406 1991695 := bstep (se 1 (by rfl) ⟨1493771, by rfl⟩ : syracuseStep 1991695 = 2987543) B2987543
theorem B2237483 : Blo 1178406 2237483 := bstep (se 1 (by rfl) ⟨1678112, by rfl⟩ : syracuseStep 2237483 = 3356225) B3356225
theorem B1770539 : Blo 1178406 1770539 := bstep (se 1 (by rfl) ⟨1327904, by rfl⟩ : syracuseStep 1770539 = 2655809) B2655809
theorem B1770569 : Blo 1178406 1770569 := bstep (se 2 (by rfl) ⟨663963, by rfl⟩ : syracuseStep 1770569 = 1327927) B1327927
theorem B2983027 : Blo 1178406 2983027 := bstep (se 1 (by rfl) ⟨2237270, by rfl⟩ : syracuseStep 2983027 = 4474541) B4474541
theorem B1492111 : Blo 1178406 1492111 := bstep (se 1 (by rfl) ⟨1119083, by rfl⟩ : syracuseStep 1492111 = 2238167) B2238167
theorem B12748013 : Blo 1178406 12748013 := bstep (se 3 (by rfl) ⟨2390252, by rfl⟩ : syracuseStep 12748013 = 4780505) B4780505
theorem B2983169 : Blo 1178406 2983169 := bstep (se 2 (by rfl) ⟨1118688, by rfl⟩ : syracuseStep 2983169 = 2237377) B2237377
theorem B5973263 : Blo 1178406 5973263 := bstep (se 1 (by rfl) ⟨4479947, by rfl⟩ : syracuseStep 5973263 = 8959895) B8959895
theorem B3982607 : Blo 1178406 3982607 := bstep (se 1 (by rfl) ⟨2986955, by rfl⟩ : syracuseStep 3982607 = 5973911) B5973911
theorem B2655503 : Blo 1178406 2655503 := bstep (se 1 (by rfl) ⟨1991627, by rfl⟩ : syracuseStep 2655503 = 3983255) B3983255
theorem B2655521 : Blo 1178406 2655521 := bstep (se 2 (by rfl) ⟨995820, by rfl⟩ : syracuseStep 2655521 = 1991641) B1991641
theorem B1492283 : Blo 1178406 1492283 := bstep (se 1 (by rfl) ⟨1119212, by rfl⟩ : syracuseStep 1492283 = 2238425) B2238425
theorem B7562555 : Blo 1178406 7562555 := bstep (se 1 (by rfl) ⟨5671916, by rfl⟩ : syracuseStep 7562555 = 11343833) B11343833
theorem B3024263 : Blo 1178406 3024263 := bstep (se 1 (by rfl) ⟨2268197, by rfl⟩ : syracuseStep 3024263 = 4536395) B4536395
theorem B11494865 : Blo 1178406 11494865 := bstep (se 2 (by rfl) ⟨4310574, by rfl⟩ : syracuseStep 11494865 = 8621149) B8621149
theorem B3982877 : Blo 1178406 3982877 := bstep (se 3 (by rfl) ⟨746789, by rfl⟩ : syracuseStep 3982877 = 1493579) B1493579
theorem B2655863 : Blo 1178406 2655863 := bstep (se 1 (by rfl) ⟨1991897, by rfl⟩ : syracuseStep 2655863 = 3983795) B3983795
theorem B2983625 : Blo 1178406 2983625 := bstep (se 2 (by rfl) ⟨1118859, by rfl⟩ : syracuseStep 2983625 = 2237719) B2237719
theorem B14534437 : Blo 1178406 14534437 := bstep (se 4 (by rfl) ⟨1362603, by rfl⟩ : syracuseStep 14534437 = 2725207) B2725207
theorem B3360599 : Blo 1178406 3360599 := bstep (se 1 (by rfl) ⟨2520449, by rfl⟩ : syracuseStep 3360599 = 5040899) B5040899
theorem B6637571 : Blo 1178406 6637571 := bstep (se 1 (by rfl) ⟨4978178, by rfl⟩ : syracuseStep 6637571 = 9956357) B9956357
theorem B29067281 : Blo 1178406 29067281 := bstep (se 2 (by rfl) ⟨10900230, by rfl⟩ : syracuseStep 29067281 = 21800461) B21800461
theorem B4540445 : Blo 1178406 4540445 := bstep (se 3 (by rfl) ⟨851333, by rfl⟩ : syracuseStep 4540445 = 1702667) B1702667
theorem B2983979 : Blo 1178406 2983979 := bstep (se 1 (by rfl) ⟨2237984, by rfl⟩ : syracuseStep 2983979 = 4475969) B4475969
theorem B11339837 : Blo 1178406 11339837 := bstep (se 3 (by rfl) ⟨2126219, by rfl⟩ : syracuseStep 11339837 = 4252439) B4252439
theorem B3360827 : Blo 1178406 3360827 := bstep (se 1 (by rfl) ⟨2520620, by rfl⟩ : syracuseStep 3360827 = 5041241) B5041241
theorem B5040215 : Blo 1178406 5040215 := bstep (se 1 (by rfl) ⟨3780161, by rfl⟩ : syracuseStep 5040215 = 7560323) B7560323
theorem B3360953 : Blo 1178406 3360953 := bstep (se 2 (by rfl) ⟨1260357, by rfl⟩ : syracuseStep 3360953 = 2520715) B2520715
theorem B2123977 : Blo 1178406 2123977 := bstep (se 2 (by rfl) ⟨796491, by rfl⟩ : syracuseStep 2123977 = 1592983) B1592983
theorem B8407277 : Blo 1178406 8407277 := bstep (se 3 (by rfl) ⟨1576364, by rfl⟩ : syracuseStep 8407277 = 3152729) B3152729
theorem B1493255 : Blo 1178406 1493255 := bstep (se 1 (by rfl) ⟨1119941, by rfl⟩ : syracuseStep 1493255 = 2239883) B2239883
theorem B4778299 : Blo 1178406 4778299 := bstep (se 1 (by rfl) ⟨3583724, by rfl⟩ : syracuseStep 4778299 = 7167449) B7167449
theorem B4475195 : Blo 1178406 4475195 := bstep (se 1 (by rfl) ⟨3356396, by rfl⟩ : syracuseStep 4475195 = 6712793) B6712793
theorem B8071483 : Blo 1178406 8071483 := bstep (se 1 (by rfl) ⟨6053612, by rfl⟩ : syracuseStep 8071483 = 12107225) B12107225
theorem B3189079 : Blo 1178406 3189079 := bstep (se 1 (by rfl) ⟨2391809, by rfl⟩ : syracuseStep 3189079 = 4783619) B4783619
theorem B3778931 : Blo 1178406 3778931 := bstep (se 1 (by rfl) ⟨2834198, by rfl⟩ : syracuseStep 3778931 = 5668397) B5668397
theorem B8956493 : Blo 1178406 8956493 := bstep (se 3 (by rfl) ⟨1679342, by rfl⟩ : syracuseStep 8956493 = 3358685) B3358685
theorem B5974721 : Blo 1178406 5974721 := bstep (se 2 (by rfl) ⟨2240520, by rfl⟩ : syracuseStep 5974721 = 4481041) B4481041
theorem B2239177 : Blo 1178406 2239177 := bstep (se 2 (by rfl) ⟨839691, by rfl⟩ : syracuseStep 2239177 = 1679383) B1679383
theorem B4475681 : Blo 1178406 4475681 := bstep (se 2 (by rfl) ⟨1678380, by rfl⟩ : syracuseStep 4475681 = 3356761) B3356761
theorem B1493903 : Blo 1178406 1493903 := bstep (se 1 (by rfl) ⟨1120427, by rfl⟩ : syracuseStep 1493903 = 2240855) B2240855
theorem B6712267 : Blo 1178406 6712267 := bstep (se 1 (by rfl) ⟨5034200, by rfl⟩ : syracuseStep 6712267 = 10068401) B10068401
theorem B6720515 : Blo 1178406 6720515 := bstep (se 1 (by rfl) ⟨5040386, by rfl⟩ : syracuseStep 6720515 = 10080773) B10080773
theorem B2984971 : Blo 1178406 2984971 := bstep (se 1 (by rfl) ⟨2238728, by rfl⟩ : syracuseStep 2984971 = 4477457) B4477457
theorem B28691587 : Blo 1178406 28691587 := bstep (se 1 (by rfl) ⟨21518690, by rfl⟩ : syracuseStep 28691587 = 43037381) B43037381
theorem B2985113 : Blo 1178406 2985113 := bstep (se 2 (by rfl) ⟨1119417, by rfl⟩ : syracuseStep 2985113 = 2238835) B2238835
theorem B3779855 : Blo 1178406 3779855 := bstep (se 1 (by rfl) ⟨2834891, by rfl⟩ : syracuseStep 3779855 = 5669783) B5669783
theorem B2985275 : Blo 1178406 2985275 := bstep (se 1 (by rfl) ⟨2238956, by rfl⟩ : syracuseStep 2985275 = 4477913) B4477913
theorem B5672281 : Blo 1178406 5672281 := bstep (se 2 (by rfl) ⟨2127105, by rfl⟩ : syracuseStep 5672281 = 4254211) B4254211
theorem B2518391 : Blo 1178406 2518391 := bstep (se 1 (by rfl) ⟨1888793, by rfl⟩ : syracuseStep 2518391 = 3777587) B3777587
theorem B20417923 : Blo 1178406 20417923 := bstep (se 1 (by rfl) ⟨15313442, by rfl⟩ : syracuseStep 20417923 = 30626885) B30626885
theorem B10079747 : Blo 1178406 10079747 := bstep (se 1 (by rfl) ⟨7559810, by rfl⟩ : syracuseStep 10079747 = 15119621) B15119621
theorem B3583531 : Blo 1178406 3583531 := bstep (se 1 (by rfl) ⟨2687648, by rfl⟩ : syracuseStep 3583531 = 5375297) B5375297
theorem B4541995 : Blo 1178406 4541995 := bstep (se 1 (by rfl) ⟨3406496, by rfl⟩ : syracuseStep 4541995 = 6812993) B6812993
theorem B5664323 : Blo 1178406 5664323 := bstep (se 1 (by rfl) ⟨4248242, by rfl⟩ : syracuseStep 5664323 = 8496485) B8496485
theorem B2985619 : Blo 1178406 2985619 := bstep (se 1 (by rfl) ⟨2239214, by rfl⟩ : syracuseStep 2985619 = 4478429) B4478429
theorem B4476653 : Blo 1178406 4476653 := bstep (se 3 (by rfl) ⟨839372, by rfl⟩ : syracuseStep 4476653 = 1678745) B1678745
theorem B2985761 : Blo 1178406 2985761 := bstep (se 2 (by rfl) ⟨1119660, by rfl⟩ : syracuseStep 2985761 = 2239321) B2239321
theorem B14339915 : Blo 1178406 14339915 := bstep (se 1 (by rfl) ⟨10754936, by rfl⟩ : syracuseStep 14339915 = 21509873) B21509873
theorem B4476971 : Blo 1178406 4476971 := bstep (se 1 (by rfl) ⟨3357728, by rfl⟩ : syracuseStep 4476971 = 6715457) B6715457
theorem B3977531 : Blo 1178406 3977531 := bstep (se 1 (by rfl) ⟨2983148, by rfl⟩ : syracuseStep 3977531 = 5966297) B5966297
theorem B1888697 : Blo 1178406 1888697 := bstep (se 2 (by rfl) ⟨708261, by rfl⟩ : syracuseStep 1888697 = 1416523) B1416523
theorem B25498097 : Blo 1178406 25498097 := bstep (se 2 (by rfl) ⟨9561786, by rfl⟩ : syracuseStep 25498097 = 19123573) B19123573
theorem B22663745 : Blo 1178406 22663745 := bstep (se 2 (by rfl) ⟨8498904, by rfl⟩ : syracuseStep 22663745 = 16997809) B16997809
theorem B16142915 : Blo 1178406 16142915 := bstep (se 1 (by rfl) ⟨12107186, by rfl⟩ : syracuseStep 16142915 = 24214373) B24214373
theorem B3584627 : Blo 1178406 3584627 := bstep (se 1 (by rfl) ⟨2688470, by rfl⟩ : syracuseStep 3584627 = 5376941) B5376941
theorem B2986753 : Blo 1178406 2986753 := bstep (se 2 (by rfl) ⟨1120032, by rfl⟩ : syracuseStep 2986753 = 2240065) B2240065
theorem B3978017 : Blo 1178406 3978017 := bstep (se 2 (by rfl) ⟨1491756, by rfl⟩ : syracuseStep 3978017 = 2983513) B2983513
theorem B8958923 : Blo 1178406 8958923 := bstep (se 1 (by rfl) ⟨6719192, by rfl⟩ : syracuseStep 8958923 = 13438385) B13438385
theorem B2651435 : Blo 1178406 2651435 := bstep (se 1 (by rfl) ⟨1988576, by rfl⟩ : syracuseStep 2651435 = 3977153) B3977153
theorem B6714683 : Blo 1178406 6714683 := bstep (se 1 (by rfl) ⟨5036012, by rfl⟩ : syracuseStep 6714683 = 10072025) B10072025
theorem B2987351 : Blo 1178406 2987351 := bstep (se 1 (by rfl) ⟨2240513, by rfl⟩ : syracuseStep 2987351 = 4481027) B4481027
theorem B3978611 : Blo 1178406 3978611 := bstep (se 1 (by rfl) ⟨2983958, by rfl⟩ : syracuseStep 3978611 = 5967917) B5967917
theorem B1889671 : Blo 1178406 1889671 := bstep (se 1 (by rfl) ⟨1417253, by rfl⟩ : syracuseStep 1889671 = 2834507) B2834507
theorem B2520467 : Blo 1178406 2520467 := bstep (se 1 (by rfl) ⟨1890350, by rfl⟩ : syracuseStep 2520467 = 3780701) B3780701
theorem B2987563 : Blo 1178406 2987563 := bstep (se 1 (by rfl) ⟨2240672, by rfl⟩ : syracuseStep 2987563 = 4481345) B4481345
theorem B14358059 : Blo 1178406 14358059 := bstep (se 1 (by rfl) ⟨10768544, by rfl⟩ : syracuseStep 14358059 = 21537089) B21537089
theorem B6379069 : Blo 1178406 6379069 := bstep (se 3 (by rfl) ⟨1196075, by rfl⟩ : syracuseStep 6379069 = 2392151) B2392151
theorem B1595015 : Blo 1178406 1595015 := bstep (se 1 (by rfl) ⟨1196261, by rfl⟩ : syracuseStep 1595015 = 2392523) B2392523
theorem B2651795 : Blo 1178406 2651795 := bstep (se 1 (by rfl) ⟨1988846, by rfl⟩ : syracuseStep 2651795 = 3977693) B3977693
theorem B2873017 : Blo 1178406 2873017 := bstep (se 2 (by rfl) ⟨1077381, by rfl⟩ : syracuseStep 2873017 = 2154763) B2154763
theorem B2987705 : Blo 1178406 2987705 := bstep (se 2 (by rfl) ⟨1120389, by rfl⟩ : syracuseStep 2987705 = 2240779) B2240779
theorem B2651849 : Blo 1178406 2651849 := bstep (se 2 (by rfl) ⟨994443, by rfl⟩ : syracuseStep 2651849 = 1988887) B1988887
theorem B5740321 : Blo 1178406 5740321 := bstep (se 2 (by rfl) ⟨2152620, by rfl⟩ : syracuseStep 5740321 = 4305241) B4305241
theorem B19380017 : Blo 1178406 19380017 := bstep (se 2 (by rfl) ⟨7267506, by rfl⟩ : syracuseStep 19380017 = 14535013) B14535013
theorem B15324977 : Blo 1178406 15324977 := bstep (se 2 (by rfl) ⟨5746866, by rfl⟩ : syracuseStep 15324977 = 11493733) B11493733
theorem B28686149 : Blo 1178406 28686149 := bstep (se 4 (by rfl) ⟨2689326, by rfl⟩ : syracuseStep 28686149 = 5378653) B5378653
theorem B7272337 : Blo 1178406 7272337 := bstep (se 2 (by rfl) ⟨2727126, by rfl⟩ : syracuseStep 7272337 = 5454253) B5454253
theorem B1816507 : Blo 1178406 1816507 := bstep (se 1 (by rfl) ⟨1362380, by rfl⟩ : syracuseStep 1816507 = 2724761) B2724761
theorem B1988651 : Blo 1178406 1988651 := bstep (se 1 (by rfl) ⟨1491488, by rfl⟩ : syracuseStep 1988651 = 2982977) B2982977
theorem B2832499 : Blo 1178406 2832499 := bstep (se 1 (by rfl) ⟨2124374, by rfl⟩ : syracuseStep 2832499 = 4248749) B4248749
theorem B1767611 : Blo 1178406 1767611 := bstep (se 1 (by rfl) ⟨1325708, by rfl⟩ : syracuseStep 1767611 = 2651417) B2651417
theorem B7272641 : Blo 1178406 7272641 := bstep (se 2 (by rfl) ⟨2727240, by rfl⟩ : syracuseStep 7272641 = 5454481) B5454481
theorem B1767671 : Blo 1178406 1767671 := bstep (se 1 (by rfl) ⟨1325753, by rfl⟩ : syracuseStep 1767671 = 2651507) B2651507
theorem B1767695 : Blo 1178406 1767695 := bstep (se 1 (by rfl) ⟨1325771, by rfl⟩ : syracuseStep 1767695 = 2651543) B2651543
theorem B1767737 : Blo 1178406 1767737 := bstep (se 2 (by rfl) ⟨662901, by rfl⟩ : syracuseStep 1767737 = 1325803) B1325803
theorem B12925277 : Blo 1178406 12925277 := bstep (se 3 (by rfl) ⟨2423489, by rfl⟩ : syracuseStep 12925277 = 4846979) B4846979
theorem B1767815 : Blo 1178406 1767815 := bstep (se 1 (by rfl) ⟨1325861, by rfl⟩ : syracuseStep 1767815 = 2651723) B2651723
theorem B2652551 : Blo 1178406 2652551 := bstep (se 1 (by rfl) ⟨1989413, by rfl⟩ : syracuseStep 2652551 = 3978827) B3978827
theorem B1767851 : Blo 1178406 1767851 := bstep (se 1 (by rfl) ⟨1325888, by rfl⟩ : syracuseStep 1767851 = 2651777) B2651777
theorem B1989049 : Blo 1178406 1989049 := bstep (se 2 (by rfl) ⟨745893, by rfl⟩ : syracuseStep 1989049 = 1491787) B1491787
theorem B1767881 : Blo 1178406 1767881 := bstep (se 2 (by rfl) ⟨662955, by rfl⟩ : syracuseStep 1767881 = 1325911) B1325911
theorem B9558481 : Blo 1178406 9558481 := bstep (se 2 (by rfl) ⟨3584430, by rfl⟩ : syracuseStep 9558481 = 7168861) B7168861
theorem B3357227 : Blo 1178406 3357227 := bstep (se 1 (by rfl) ⟨2517920, by rfl⟩ : syracuseStep 3357227 = 5035841) B5035841
theorem B1767995 : Blo 1178406 1767995 := bstep (se 1 (by rfl) ⟨1325996, by rfl⟩ : syracuseStep 1767995 = 2651993) B2651993
theorem B2652731 : Blo 1178406 2652731 := bstep (se 1 (by rfl) ⟨1989548, by rfl⟩ : syracuseStep 2652731 = 3979097) B3979097
theorem B36313667 : Blo 1178406 36313667 := bstep (se 1 (by rfl) ⟨27235250, by rfl⟩ : syracuseStep 36313667 = 54470501) B54470501
theorem B1768055 : Blo 1178406 1768055 := bstep (se 1 (by rfl) ⟨1326041, by rfl⟩ : syracuseStep 1768055 = 2652083) B2652083
theorem B1768079 : Blo 1178406 1768079 := bstep (se 1 (by rfl) ⟨1326059, by rfl⟩ : syracuseStep 1768079 = 2652119) B2652119
theorem B1768121 : Blo 1178406 1768121 := bstep (se 2 (by rfl) ⟨663045, by rfl⟩ : syracuseStep 1768121 = 1326091) B1326091
theorem B2652857 : Blo 1178406 2652857 := bstep (se 2 (by rfl) ⟨994821, by rfl⟩ : syracuseStep 2652857 = 1989643) B1989643
theorem B6716141 : Blo 1178406 6716141 := bstep (se 3 (by rfl) ⟨1259276, by rfl⟩ : syracuseStep 6716141 = 2518553) B2518553
theorem B1415927 : Blo 1178406 1415927 := bstep (se 1 (by rfl) ⟨1061945, by rfl⟩ : syracuseStep 1415927 = 2123891) B2123891
theorem B1768199 : Blo 1178406 1768199 := bstep (se 1 (by rfl) ⟨1326149, by rfl⟩ : syracuseStep 1768199 = 2652299) B2652299
theorem B1325839 : Blo 1178406 1325839 := bstep (se 1 (by rfl) ⟨994379, by rfl⟩ : syracuseStep 1325839 = 1988759) B1988759
theorem B1768235 : Blo 1178406 1768235 := bstep (se 1 (by rfl) ⟨1326176, by rfl⟩ : syracuseStep 1768235 = 2652353) B2652353
theorem B1178427 : Blo 1178406 1178427 := bstep (se 1 (by rfl) ⟨883820, by rfl⟩ : syracuseStep 1178427 = 1767641) B1767641
theorem B1678153 : Blo 1178406 1678153 := bstep (se 2 (by rfl) ⟨629307, by rfl⟩ : syracuseStep 1678153 = 1258615) B1258615
theorem B1768265 : Blo 1178406 1768265 := bstep (se 2 (by rfl) ⟨663099, by rfl⟩ : syracuseStep 1768265 = 1326199) B1326199
theorem B1178503 : Blo 1178406 1178503 := bstep (se 1 (by rfl) ⟨883877, by rfl⟩ : syracuseStep 1178503 = 1767755) B1767755
theorem B1178511 : Blo 1178406 1178511 := bstep (se 1 (by rfl) ⟨883883, by rfl⟩ : syracuseStep 1178511 = 1767767) B1767767
theorem B5970833 : Blo 1178406 5970833 := bstep (se 2 (by rfl) ⟨2239062, by rfl⟩ : syracuseStep 5970833 = 4478125) B4478125
theorem B1178555 : Blo 1178406 1178555 := bstep (se 1 (by rfl) ⟨883916, by rfl⟩ : syracuseStep 1178555 = 1767833) B1767833
theorem B1768379 : Blo 1178406 1768379 := bstep (se 1 (by rfl) ⟨1326284, by rfl⟩ : syracuseStep 1768379 = 2652569) B2652569
theorem B1768439 : Blo 1178406 1768439 := bstep (se 1 (by rfl) ⟨1326329, by rfl⟩ : syracuseStep 1768439 = 2652659) B2652659
theorem B1178631 : Blo 1178406 1178631 := bstep (se 1 (by rfl) ⟨883973, by rfl⟩ : syracuseStep 1178631 = 1767947) B1767947
theorem B1178639 : Blo 1178406 1178639 := bstep (se 1 (by rfl) ⟨883979, by rfl⟩ : syracuseStep 1178639 = 1767959) B1767959
theorem B1768463 : Blo 1178406 1768463 := bstep (se 1 (by rfl) ⟨1326347, by rfl⟩ : syracuseStep 1768463 = 2652695) B2652695
theorem B2653199 : Blo 1178406 2653199 := bstep (se 1 (by rfl) ⟨1989899, by rfl⟩ : syracuseStep 2653199 = 3979799) B3979799
theorem B2653217 : Blo 1178406 2653217 := bstep (se 2 (by rfl) ⟨994956, by rfl⟩ : syracuseStep 2653217 = 1989913) B1989913
theorem B6716459 : Blo 1178406 6716459 := bstep (se 1 (by rfl) ⟨5037344, by rfl⟩ : syracuseStep 6716459 = 10074689) B10074689
theorem B1768505 : Blo 1178406 1768505 := bstep (se 2 (by rfl) ⟨663189, by rfl⟩ : syracuseStep 1768505 = 1326379) B1326379
theorem B1178683 : Blo 1178406 1178683 := bstep (se 1 (by rfl) ⟨884012, by rfl⟩ : syracuseStep 1178683 = 1768025) B1768025
theorem B6462551 : Blo 1178406 6462551 := bstep (se 1 (by rfl) ⟨4846913, by rfl⟩ : syracuseStep 6462551 = 9693827) B9693827
theorem B1989751 : Blo 1178406 1989751 := bstep (se 1 (by rfl) ⟨1492313, by rfl⟩ : syracuseStep 1989751 = 2984627) B2984627
theorem B1178759 : Blo 1178406 1178759 := bstep (se 1 (by rfl) ⟨884069, by rfl⟩ : syracuseStep 1178759 = 1768139) B1768139
theorem B1768583 : Blo 1178406 1768583 := bstep (se 1 (by rfl) ⟨1326437, by rfl⟩ : syracuseStep 1768583 = 2652875) B2652875
theorem B1178767 : Blo 1178406 1178767 := bstep (se 1 (by rfl) ⟨884075, by rfl⟩ : syracuseStep 1178767 = 1768151) B1768151
theorem B1768619 : Blo 1178406 1768619 := bstep (se 1 (by rfl) ⟨1326464, by rfl⟩ : syracuseStep 1768619 = 2652929) B2652929
theorem B1178811 : Blo 1178406 1178811 := bstep (se 1 (by rfl) ⟨884108, by rfl⟩ : syracuseStep 1178811 = 1768217) B1768217
theorem B1768649 : Blo 1178406 1768649 := bstep (se 2 (by rfl) ⟨663243, by rfl⟩ : syracuseStep 1768649 = 1326487) B1326487
theorem B10075373 : Blo 1178406 10075373 := bstep (se 3 (by rfl) ⟨1889132, by rfl⟩ : syracuseStep 10075373 = 3778265) B3778265
theorem B1178887 : Blo 1178406 1178887 := bstep (se 1 (by rfl) ⟨884165, by rfl⟩ : syracuseStep 1178887 = 1768331) B1768331
theorem B1326343 : Blo 1178406 1326343 := bstep (se 1 (by rfl) ⟨994757, by rfl⟩ : syracuseStep 1326343 = 1989515) B1989515
theorem B1178895 : Blo 1178406 1178895 := bstep (se 1 (by rfl) ⟨884171, by rfl⟩ : syracuseStep 1178895 = 1768343) B1768343
theorem B1768763 : Blo 1178406 1768763 := bstep (se 1 (by rfl) ⟨1326572, by rfl⟩ : syracuseStep 1768763 = 2653145) B2653145
theorem B1989947 : Blo 1178406 1989947 := bstep (se 1 (by rfl) ⟨1492460, by rfl⟩ : syracuseStep 1989947 = 2984921) B2984921
theorem B1178939 : Blo 1178406 1178939 := bstep (se 1 (by rfl) ⟨884204, by rfl⟩ : syracuseStep 1178939 = 1768409) B1768409
theorem B1768823 : Blo 1178406 1768823 := bstep (se 1 (by rfl) ⟨1326617, by rfl⟩ : syracuseStep 1768823 = 2653235) B2653235
theorem B2653559 : Blo 1178406 2653559 := bstep (se 1 (by rfl) ⟨1990169, by rfl⟩ : syracuseStep 2653559 = 3980339) B3980339
theorem B1179015 : Blo 1178406 1179015 := bstep (se 1 (by rfl) ⟨884261, by rfl⟩ : syracuseStep 1179015 = 1768523) B1768523
theorem B1179023 : Blo 1178406 1179023 := bstep (se 1 (by rfl) ⟨884267, by rfl⟩ : syracuseStep 1179023 = 1768535) B1768535
theorem B1768847 : Blo 1178406 1768847 := bstep (se 1 (by rfl) ⟨1326635, by rfl⟩ : syracuseStep 1768847 = 2653271) B2653271
theorem B1416619 : Blo 1178406 1416619 := bstep (se 1 (by rfl) ⟨1062464, by rfl⟩ : syracuseStep 1416619 = 2124929) B2124929
theorem B1768889 : Blo 1178406 1768889 := bstep (se 2 (by rfl) ⟨663333, by rfl⟩ : syracuseStep 1768889 = 1326667) B1326667
theorem B1179067 : Blo 1178406 1179067 := bstep (se 1 (by rfl) ⟨884300, by rfl⟩ : syracuseStep 1179067 = 1768601) B1768601
theorem B1326523 : Blo 1178406 1326523 := bstep (se 1 (by rfl) ⟨994892, by rfl⟩ : syracuseStep 1326523 = 1989785) B1989785
theorem B21536209 : Blo 1178406 21536209 := bstep (se 2 (by rfl) ⟨8076078, by rfl⟩ : syracuseStep 21536209 = 16152157) B16152157
theorem B1179143 : Blo 1178406 1179143 := bstep (se 1 (by rfl) ⟨884357, by rfl⟩ : syracuseStep 1179143 = 1768715) B1768715
theorem B1768967 : Blo 1178406 1768967 := bstep (se 1 (by rfl) ⟨1326725, by rfl⟩ : syracuseStep 1768967 = 2653451) B2653451
theorem B48455171 : Blo 1178406 48455171 := bstep (se 1 (by rfl) ⟨36341378, by rfl⟩ : syracuseStep 48455171 = 72682757) B72682757
theorem B3358219 : Blo 1178406 3358219 := bstep (se 1 (by rfl) ⟨2518664, by rfl⟩ : syracuseStep 3358219 = 5037329) B5037329
theorem B1179151 : Blo 1178406 1179151 := bstep (se 1 (by rfl) ⟨884363, by rfl⟩ : syracuseStep 1179151 = 1768727) B1768727
theorem B4480541 : Blo 1178406 4480541 := bstep (se 3 (by rfl) ⟨840101, by rfl⟩ : syracuseStep 4480541 = 1680203) B1680203
theorem B1769003 : Blo 1178406 1769003 := bstep (se 1 (by rfl) ⟨1326752, by rfl⟩ : syracuseStep 1769003 = 2653505) B2653505
theorem B2653739 : Blo 1178406 2653739 := bstep (se 1 (by rfl) ⟨1990304, by rfl⟩ : syracuseStep 2653739 = 3980609) B3980609
theorem B4480555 : Blo 1178406 4480555 := bstep (se 1 (by rfl) ⟨3360416, by rfl⟩ : syracuseStep 4480555 = 6720833) B6720833
theorem B1179195 : Blo 1178406 1179195 := bstep (se 1 (by rfl) ⟨884396, by rfl⟩ : syracuseStep 1179195 = 1768793) B1768793
theorem B1769033 : Blo 1178406 1769033 := bstep (se 2 (by rfl) ⟨663387, by rfl⟩ : syracuseStep 1769033 = 1326775) B1326775
theorem B3186311 : Blo 1178406 3186311 := bstep (se 1 (by rfl) ⟨2389733, by rfl⟩ : syracuseStep 3186311 = 4779467) B4779467
theorem B1179271 : Blo 1178406 1179271 := bstep (se 1 (by rfl) ⟨884453, by rfl⟩ : syracuseStep 1179271 = 1768907) B1768907
theorem B1179279 : Blo 1178406 1179279 := bstep (se 1 (by rfl) ⟨884459, by rfl⟩ : syracuseStep 1179279 = 1768919) B1768919
theorem B1179323 : Blo 1178406 1179323 := bstep (se 1 (by rfl) ⟨884492, by rfl⟩ : syracuseStep 1179323 = 1768985) B1768985
theorem B1769147 : Blo 1178406 1769147 := bstep (se 1 (by rfl) ⟨1326860, by rfl⟩ : syracuseStep 1769147 = 2653721) B2653721
theorem B1990345 : Blo 1178406 1990345 := bstep (se 2 (by rfl) ⟨746379, by rfl⟩ : syracuseStep 1990345 = 1492759) B1492759
theorem B1769207 : Blo 1178406 1769207 := bstep (se 1 (by rfl) ⟨1326905, by rfl⟩ : syracuseStep 1769207 = 2653811) B2653811
theorem B1179399 : Blo 1178406 1179399 := bstep (se 1 (by rfl) ⟨884549, by rfl⟩ : syracuseStep 1179399 = 1769099) B1769099
theorem B1179407 : Blo 1178406 1179407 := bstep (se 1 (by rfl) ⟨884555, by rfl⟩ : syracuseStep 1179407 = 1769111) B1769111
theorem B1769231 : Blo 1178406 1769231 := bstep (se 1 (by rfl) ⟨1326923, by rfl⟩ : syracuseStep 1769231 = 2653847) B2653847
theorem B3358493 : Blo 1178406 3358493 := bstep (se 3 (by rfl) ⟨629717, by rfl⟩ : syracuseStep 3358493 = 1259435) B1259435
theorem B1769273 : Blo 1178406 1769273 := bstep (se 2 (by rfl) ⟨663477, by rfl⟩ : syracuseStep 1769273 = 1326955) B1326955
theorem B1179451 : Blo 1178406 1179451 := bstep (se 1 (by rfl) ⟨884588, by rfl⟩ : syracuseStep 1179451 = 1769177) B1769177
theorem B1179527 : Blo 1178406 1179527 := bstep (se 1 (by rfl) ⟨884645, by rfl⟩ : syracuseStep 1179527 = 1769291) B1769291
theorem B1769351 : Blo 1178406 1769351 := bstep (se 1 (by rfl) ⟨1327013, by rfl⟩ : syracuseStep 1769351 = 2654027) B2654027
theorem B1179535 : Blo 1178406 1179535 := bstep (se 1 (by rfl) ⟨884651, by rfl⟩ : syracuseStep 1179535 = 1769303) B1769303
theorem B1326991 : Blo 1178406 1326991 := bstep (se 1 (by rfl) ⟨995243, by rfl⟩ : syracuseStep 1326991 = 1990487) B1990487
theorem B2654099 : Blo 1178406 2654099 := bstep (se 1 (by rfl) ⟨1990574, by rfl⟩ : syracuseStep 2654099 = 3981149) B3981149
theorem B3981203 : Blo 1178406 3981203 := bstep (se 1 (by rfl) ⟨2985902, by rfl⟩ : syracuseStep 3981203 = 5971805) B5971805
theorem B34471831 : Blo 1178406 34471831 := bstep (se 1 (by rfl) ⟨25853873, by rfl⟩ : syracuseStep 34471831 = 51707747) B51707747
theorem B1769387 : Blo 1178406 1769387 := bstep (se 1 (by rfl) ⟨1327040, by rfl⟩ : syracuseStep 1769387 = 2654081) B2654081
theorem B1179579 : Blo 1178406 1179579 := bstep (se 1 (by rfl) ⟨884684, by rfl⟩ : syracuseStep 1179579 = 1769369) B1769369
theorem B1769417 : Blo 1178406 1769417 := bstep (se 2 (by rfl) ⟨663531, by rfl⟩ : syracuseStep 1769417 = 1327063) B1327063
theorem B2654153 : Blo 1178406 2654153 := bstep (se 2 (by rfl) ⟨995307, by rfl⟩ : syracuseStep 2654153 = 1990615) B1990615
theorem B1179687 : Blo 1178406 1179687 := bstep (se 1 (by rfl) ⟨884765, by rfl⟩ : syracuseStep 1179687 = 1769531) B1769531
theorem B1179727 : Blo 1178406 1179727 := bstep (se 1 (by rfl) ⟨884795, by rfl⟩ : syracuseStep 1179727 = 1769591) B1769591
theorem B1179743 : Blo 1178406 1179743 := bstep (se 1 (by rfl) ⟨884807, by rfl⟩ : syracuseStep 1179743 = 1769615) B1769615
theorem B1179771 : Blo 1178406 1179771 := bstep (se 1 (by rfl) ⟨884828, by rfl⟩ : syracuseStep 1179771 = 1769657) B1769657
theorem B3776665 : Blo 1178406 3776665 := bstep (se 2 (by rfl) ⟨1416249, by rfl⟩ : syracuseStep 3776665 = 2832499) B2832499
theorem B2834603 : Blo 1178406 2834603 := bstep (se 1 (by rfl) ⟨2125952, by rfl⟩ : syracuseStep 2834603 = 4251905) B4251905
theorem B1179823 : Blo 1178406 1179823 := bstep (se 1 (by rfl) ⟨884867, by rfl⟩ : syracuseStep 1179823 = 1769735) B1769735
theorem B1179847 : Blo 1178406 1179847 := bstep (se 1 (by rfl) ⟨884885, by rfl⟩ : syracuseStep 1179847 = 1769771) B1769771
theorem B1179867 : Blo 1178406 1179867 := bstep (se 1 (by rfl) ⟨884900, by rfl⟩ : syracuseStep 1179867 = 1769801) B1769801
theorem B1179943 : Blo 1178406 1179943 := bstep (se 1 (by rfl) ⟨884957, by rfl⟩ : syracuseStep 1179943 = 1769915) B1769915
theorem B16998731 : Blo 1178406 16998731 := bstep (se 1 (by rfl) ⟨12749048, by rfl⟩ : syracuseStep 16998731 = 25498097) B25498097
theorem B1179983 : Blo 1178406 1179983 := bstep (se 1 (by rfl) ⟨884987, by rfl⟩ : syracuseStep 1179983 = 1769975) B1769975
theorem B1179999 : Blo 1178406 1179999 := bstep (se 1 (by rfl) ⟨884999, by rfl⟩ : syracuseStep 1179999 = 1769999) B1769999
theorem B1180027 : Blo 1178406 1180027 := bstep (se 1 (by rfl) ⟨885020, by rfl⟩ : syracuseStep 1180027 = 1770041) B1770041
theorem B1769903 : Blo 1178406 1769903 := bstep (se 1 (by rfl) ⟨1327427, by rfl⟩ : syracuseStep 1769903 = 2654855) B2654855
theorem B1180079 : Blo 1178406 1180079 := bstep (se 1 (by rfl) ⟨885059, by rfl⟩ : syracuseStep 1180079 = 1770119) B1770119
theorem B1180103 : Blo 1178406 1180103 := bstep (se 1 (by rfl) ⟨885077, by rfl⟩ : syracuseStep 1180103 = 1770155) B1770155
theorem B4252105 : Blo 1178406 4252105 := bstep (se 2 (by rfl) ⟨1594539, by rfl⟩ : syracuseStep 4252105 = 3189079) B3189079
theorem B1180123 : Blo 1178406 1180123 := bstep (se 1 (by rfl) ⟨885092, by rfl⟩ : syracuseStep 1180123 = 1770185) B1770185
theorem B2654729 : Blo 1178406 2654729 := bstep (se 2 (by rfl) ⟨995523, by rfl⟩ : syracuseStep 2654729 = 1991047) B1991047
theorem B1769993 : Blo 1178406 1769993 := bstep (se 2 (by rfl) ⟨663747, by rfl⟩ : syracuseStep 1769993 = 1327495) B1327495
theorem B1770023 : Blo 1178406 1770023 := bstep (se 1 (by rfl) ⟨1327517, by rfl⟩ : syracuseStep 1770023 = 2655035) B2655035
theorem B1180199 : Blo 1178406 1180199 := bstep (se 1 (by rfl) ⟨885149, by rfl⟩ : syracuseStep 1180199 = 1770299) B1770299
theorem B1180239 : Blo 1178406 1180239 := bstep (se 1 (by rfl) ⟨885179, by rfl⟩ : syracuseStep 1180239 = 1770359) B1770359
theorem B1180255 : Blo 1178406 1180255 := bstep (se 1 (by rfl) ⟨885191, by rfl⟩ : syracuseStep 1180255 = 1770383) B1770383
theorem B1770107 : Blo 1178406 1770107 := bstep (se 1 (by rfl) ⟨1327580, by rfl⟩ : syracuseStep 1770107 = 2655161) B2655161
theorem B1180283 : Blo 1178406 1180283 := bstep (se 1 (by rfl) ⟨885212, by rfl⟩ : syracuseStep 1180283 = 1770425) B1770425
theorem B5972615 : Blo 1178406 5972615 := bstep (se 1 (by rfl) ⟨4479461, by rfl⟩ : syracuseStep 5972615 = 8958923) B8958923
theorem B3981959 : Blo 1178406 3981959 := bstep (se 1 (by rfl) ⟨2986469, by rfl⟩ : syracuseStep 3981959 = 5972939) B5972939
theorem B1180335 : Blo 1178406 1180335 := bstep (se 1 (by rfl) ⟨885251, by rfl⟩ : syracuseStep 1180335 = 1770503) B1770503
theorem B3982013 : Blo 1178406 3982013 := bstep (se 3 (by rfl) ⟨746627, by rfl⟩ : syracuseStep 3982013 = 1493255) B1493255
theorem B1180359 : Blo 1178406 1180359 := bstep (se 1 (by rfl) ⟨885269, by rfl⟩ : syracuseStep 1180359 = 1770539) B1770539
theorem B1180379 : Blo 1178406 1180379 := bstep (se 1 (by rfl) ⟨885284, by rfl⟩ : syracuseStep 1180379 = 1770569) B1770569
theorem B1770233 : Blo 1178406 1770233 := bstep (se 2 (by rfl) ⟨663837, by rfl⟩ : syracuseStep 1770233 = 1327675) B1327675
theorem B3982175 : Blo 1178406 3982175 := bstep (se 1 (by rfl) ⟨2986631, by rfl⟩ : syracuseStep 3982175 = 5973263) B5973263
theorem B2655071 : Blo 1178406 2655071 := bstep (se 1 (by rfl) ⟨1991303, by rfl⟩ : syracuseStep 2655071 = 3982607) B3982607
theorem B1770335 : Blo 1178406 1770335 := bstep (se 1 (by rfl) ⟨1327751, by rfl⟩ : syracuseStep 1770335 = 2655503) B2655503
theorem B1770347 : Blo 1178406 1770347 := bstep (se 1 (by rfl) ⟨1327760, by rfl⟩ : syracuseStep 1770347 = 2655521) B2655521
theorem B1991567 : Blo 1178406 1991567 := bstep (se 1 (by rfl) ⟨1493675, by rfl⟩ : syracuseStep 1991567 = 2987351) B2987351
theorem B2016175 : Blo 1178406 2016175 := bstep (se 1 (by rfl) ⟨1512131, by rfl⟩ : syracuseStep 2016175 = 3024263) B3024263
theorem B1680311 : Blo 1178406 1680311 := bstep (se 1 (by rfl) ⟨1260233, by rfl⟩ : syracuseStep 1680311 = 2520467) B2520467
theorem B10077149 : Blo 1178406 10077149 := bstep (se 3 (by rfl) ⟨1889465, by rfl⟩ : syracuseStep 10077149 = 3778931) B3778931
theorem B3982337 : Blo 1178406 3982337 := bstep (se 2 (by rfl) ⟨1493376, by rfl⟩ : syracuseStep 3982337 = 2986753) B2986753
theorem B2655251 : Blo 1178406 2655251 := bstep (se 1 (by rfl) ⟨1991438, by rfl⟩ : syracuseStep 2655251 = 3982877) B3982877
theorem B1770575 : Blo 1178406 1770575 := bstep (se 1 (by rfl) ⟨1327931, by rfl⟩ : syracuseStep 1770575 = 2655863) B2655863
theorem B2237537 : Blo 1178406 2237537 := bstep (se 2 (by rfl) ⟨839076, by rfl⟩ : syracuseStep 2237537 = 1678153) B1678153
theorem B1991803 : Blo 1178406 1991803 := bstep (se 1 (by rfl) ⟨1493852, by rfl⟩ : syracuseStep 1991803 = 2987705) B2987705
theorem B10216651 : Blo 1178406 10216651 := bstep (se 1 (by rfl) ⟨7662488, by rfl⟩ : syracuseStep 10216651 = 15324977) B15324977
theorem B9569573 : Blo 1178406 9569573 := bstep (se 4 (by rfl) ⟨897147, by rfl⟩ : syracuseStep 9569573 = 1794295) B1794295
theorem B4425047 : Blo 1178406 4425047 := bstep (se 1 (by rfl) ⟨3318785, by rfl⟩ : syracuseStep 4425047 = 6637571) B6637571
theorem B2655593 : Blo 1178406 2655593 := bstep (se 2 (by rfl) ⟨995847, by rfl⟩ : syracuseStep 2655593 = 1991695) B1991695
theorem B3360143 : Blo 1178406 3360143 := bstep (se 1 (by rfl) ⟨2520107, by rfl⟩ : syracuseStep 3360143 = 5040215) B5040215
theorem B5604851 : Blo 1178406 5604851 := bstep (se 1 (by rfl) ⟨4203638, by rfl⟩ : syracuseStep 5604851 = 8407277) B8407277
theorem B2983463 : Blo 1178406 2983463 := bstep (se 1 (by rfl) ⟨2237597, by rfl⟩ : syracuseStep 2983463 = 4475195) B4475195
theorem B8496829 : Blo 1178406 8496829 := bstep (se 3 (by rfl) ⟨1593155, by rfl⟩ : syracuseStep 8496829 = 3186311) B3186311
theorem B24209111 : Blo 1178406 24209111 := bstep (se 1 (by rfl) ⟨18156833, by rfl⟩ : syracuseStep 24209111 = 36313667) B36313667
theorem B7563041 : Blo 1178406 7563041 := bstep (se 2 (by rfl) ⟨2836140, by rfl⟩ : syracuseStep 7563041 = 5672281) B5672281
theorem B3983147 : Blo 1178406 3983147 := bstep (se 1 (by rfl) ⟨2987360, by rfl⟩ : syracuseStep 3983147 = 5974721) B5974721
theorem B27223897 : Blo 1178406 27223897 := bstep (se 2 (by rfl) ⟨10208961, by rfl⟩ : syracuseStep 27223897 = 20417923) B20417923
theorem B2983787 : Blo 1178406 2983787 := bstep (se 1 (by rfl) ⟨2237840, by rfl⟩ : syracuseStep 2983787 = 4475681) B4475681
theorem B28714945 : Blo 1178406 28714945 := bstep (se 2 (by rfl) ⟨10768104, by rfl⟩ : syracuseStep 28714945 = 21536209) B21536209
theorem B4778041 : Blo 1178406 4778041 := bstep (se 2 (by rfl) ⟨1791765, by rfl⟩ : syracuseStep 4778041 = 3583531) B3583531
theorem B5974073 : Blo 1178406 5974073 := bstep (se 2 (by rfl) ⟨2240277, by rfl⟩ : syracuseStep 5974073 = 4480555) B4480555
theorem B6055993 : Blo 1178406 6055993 := bstep (se 2 (by rfl) ⟨2270997, by rfl⟩ : syracuseStep 6055993 = 4541995) B4541995
theorem B3983417 : Blo 1178406 3983417 := bstep (se 2 (by rfl) ⟨1493781, by rfl⟩ : syracuseStep 3983417 = 2987563) B2987563
theorem B8505425 : Blo 1178406 8505425 := bstep (se 2 (by rfl) ⟨3189534, by rfl⟩ : syracuseStep 8505425 = 6379069) B6379069
theorem B7555301 : Blo 1178406 7555301 := bstep (se 4 (by rfl) ⟨708309, by rfl⟩ : syracuseStep 7555301 = 1416619) B1416619
theorem B6719831 : Blo 1178406 6719831 := bstep (se 1 (by rfl) ⟨5039873, by rfl⟩ : syracuseStep 6719831 = 10079747) B10079747
theorem B32303447 : Blo 1178406 32303447 := bstep (se 1 (by rfl) ⟨24227585, by rfl⟩ : syracuseStep 32303447 = 48455171) B48455171
theorem B3983741 : Blo 1178406 3983741 := bstep (se 3 (by rfl) ⟨746951, by rfl⟩ : syracuseStep 3983741 = 1493903) B1493903
theorem B7653761 : Blo 1178406 7653761 := bstep (se 2 (by rfl) ⟨2870160, by rfl⟩ : syracuseStep 7653761 = 5740321) B5740321
theorem B2984435 : Blo 1178406 2984435 := bstep (se 1 (by rfl) ⟨2238326, by rfl⟩ : syracuseStep 2984435 = 4476653) B4476653
theorem B2238995 : Blo 1178406 2238995 := bstep (se 1 (by rfl) ⟨1679246, by rfl⟩ : syracuseStep 2238995 = 3358493) B3358493
theorem B2984647 : Blo 1178406 2984647 := bstep (se 1 (by rfl) ⟨2238485, by rfl⟩ : syracuseStep 2984647 = 4476971) B4476971
theorem B5966621 : Blo 1178406 5966621 := bstep (se 3 (by rfl) ⟨1118741, by rfl⟩ : syracuseStep 5966621 = 2237483) B2237483
theorem B6810551 : Blo 1178406 6810551 := bstep (se 1 (by rfl) ⟨5107913, by rfl⟩ : syracuseStep 6810551 = 10215827) B10215827
theorem B15109163 : Blo 1178406 15109163 := bstep (se 1 (by rfl) ⟨11331872, by rfl⟩ : syracuseStep 15109163 = 22663745) B22663745
theorem B8956979 : Blo 1178406 8956979 := bstep (se 1 (by rfl) ⟨6717734, by rfl⟩ : syracuseStep 8956979 = 13435469) B13435469
theorem B8498675 : Blo 1178406 8498675 := bstep (se 1 (by rfl) ⟨6374006, by rfl⟩ : syracuseStep 8498675 = 12748013) B12748013
theorem B4476455 : Blo 1178406 4476455 := bstep (se 1 (by rfl) ⟨3357341, by rfl⟩ : syracuseStep 4476455 = 6714683) B6714683
theorem B5041703 : Blo 1178406 5041703 := bstep (se 1 (by rfl) ⟨3781277, by rfl⟩ : syracuseStep 5041703 = 7562555) B7562555
theorem B2985569 : Blo 1178406 2985569 := bstep (se 2 (by rfl) ⟨1119588, by rfl⟩ : syracuseStep 2985569 = 2239177) B2239177
theorem B7663243 : Blo 1178406 7663243 := bstep (se 1 (by rfl) ⟨5747432, by rfl⟩ : syracuseStep 7663243 = 11494865) B11494865
theorem B9572039 : Blo 1178406 9572039 := bstep (se 1 (by rfl) ⟨7179029, by rfl⟩ : syracuseStep 9572039 = 14358059) B14358059
theorem B19124099 : Blo 1178406 19124099 := bstep (se 1 (by rfl) ⟨14343074, by rfl⟩ : syracuseStep 19124099 = 28686149) B28686149
theorem B2240399 : Blo 1178406 2240399 := bstep (se 1 (by rfl) ⟨1680299, by rfl⟩ : syracuseStep 2240399 = 3360599) B3360599
theorem B8949689 : Blo 1178406 8949689 := bstep (se 2 (by rfl) ⟨3356133, by rfl⟩ : syracuseStep 8949689 = 6712267) B6712267
theorem B19378187 : Blo 1178406 19378187 := bstep (se 1 (by rfl) ⟨14533640, by rfl⟩ : syracuseStep 19378187 = 29067281) B29067281
theorem B3026963 : Blo 1178406 3026963 := bstep (se 1 (by rfl) ⟨2270222, by rfl⟩ : syracuseStep 3026963 = 4540445) B4540445
theorem B2240551 : Blo 1178406 2240551 := bstep (se 1 (by rfl) ⟨1680413, by rfl⟩ : syracuseStep 2240551 = 3360827) B3360827
theorem B2240635 : Blo 1178406 2240635 := bstep (se 1 (by rfl) ⟨1680476, by rfl⟩ : syracuseStep 2240635 = 3360953) B3360953
theorem B3977369 : Blo 1178406 3977369 := bstep (se 2 (by rfl) ⟨1491513, by rfl⟩ : syracuseStep 3977369 = 2983027) B2983027
theorem B4477427 : Blo 1178406 4477427 := bstep (se 1 (by rfl) ⟨3358070, by rfl⟩ : syracuseStep 4477427 = 6716141) B6716141
theorem B2519561 : Blo 1178406 2519561 := bstep (se 2 (by rfl) ⟨944835, by rfl⟩ : syracuseStep 2519561 = 1889671) B1889671
theorem B4477625 : Blo 1178406 4477625 := bstep (se 2 (by rfl) ⟨1679109, by rfl⟩ : syracuseStep 4477625 = 3358219) B3358219
theorem B4477639 : Blo 1178406 4477639 := bstep (se 1 (by rfl) ⟨3358229, by rfl⟩ : syracuseStep 4477639 = 6716459) B6716459
theorem B51680045 : Blo 1178406 51680045 := bstep (se 3 (by rfl) ⟨9690008, by rfl⟩ : syracuseStep 51680045 = 19380017) B19380017
theorem B2519903 : Blo 1178406 2519903 := bstep (se 1 (by rfl) ⟨1889927, by rfl⟩ : syracuseStep 2519903 = 3779855) B3779855
theorem B3830689 : Blo 1178406 3830689 := bstep (se 2 (by rfl) ⟨1436508, by rfl⟩ : syracuseStep 3830689 = 2873017) B2873017
theorem B2987027 : Blo 1178406 2987027 := bstep (se 1 (by rfl) ⟨2240270, by rfl⟩ : syracuseStep 2987027 = 4480541) B4480541
theorem B19379249 : Blo 1178406 19379249 := bstep (se 2 (by rfl) ⟨7267218, by rfl⟩ : syracuseStep 19379249 = 14534437) B14534437
theorem B9696449 : Blo 1178406 9696449 := bstep (se 2 (by rfl) ⟨3636168, by rfl⟩ : syracuseStep 9696449 = 7272337) B7272337
theorem B45962441 : Blo 1178406 45962441 := bstep (se 2 (by rfl) ⟨17235915, by rfl⟩ : syracuseStep 45962441 = 34471831) B34471831
theorem B2422009 : Blo 1178406 2422009 := bstep (se 2 (by rfl) ⟨908253, by rfl⟩ : syracuseStep 2422009 = 1816507) B1816507
theorem B3978557 : Blo 1178406 3978557 := bstep (se 3 (by rfl) ⟨745979, by rfl⟩ : syracuseStep 3978557 = 1491959) B1491959
theorem B19125649 : Blo 1178406 19125649 := bstep (se 2 (by rfl) ⟨7172118, by rfl⟩ : syracuseStep 19125649 = 14344237) B14344237
theorem B2651687 : Blo 1178406 2651687 := bstep (se 1 (by rfl) ⟨1988765, by rfl⟩ : syracuseStep 2651687 = 3977531) B3977531
theorem B8181287 : Blo 1178406 8181287 := bstep (se 1 (by rfl) ⟨6135965, by rfl⟩ : syracuseStep 8181287 = 12271931) B12271931
theorem B17233469 : Blo 1178406 17233469 := bstep (se 3 (by rfl) ⟨3231275, by rfl⟩ : syracuseStep 17233469 = 6462551) B6462551
theorem B2831969 : Blo 1178406 2831969 := bstep (se 2 (by rfl) ⟨1061988, by rfl⟩ : syracuseStep 2831969 = 2123977) B2123977
theorem B4249223 : Blo 1178406 4249223 := bstep (se 1 (by rfl) ⟨3186917, by rfl⟩ : syracuseStep 4249223 = 6373835) B6373835
theorem B4478611 : Blo 1178406 4478611 := bstep (se 1 (by rfl) ⟨3358958, by rfl⟩ : syracuseStep 4478611 = 6717917) B6717917
theorem B11343559 : Blo 1178406 11343559 := bstep (se 1 (by rfl) ⟨8507669, by rfl⟩ : syracuseStep 11343559 = 17015339) B17015339
theorem B10761943 : Blo 1178406 10761943 := bstep (se 1 (by rfl) ⟨8071457, by rfl⟩ : syracuseStep 10761943 = 16142915) B16142915
theorem B2389751 : Blo 1178406 2389751 := bstep (se 1 (by rfl) ⟨1792313, by rfl⟩ : syracuseStep 2389751 = 3584627) B3584627
theorem B6371065 : Blo 1178406 6371065 := bstep (se 2 (by rfl) ⟨2389149, by rfl⟩ : syracuseStep 6371065 = 4778299) B4778299
theorem B10761977 : Blo 1178406 10761977 := bstep (se 2 (by rfl) ⟨4035741, by rfl⟩ : syracuseStep 10761977 = 8071483) B8071483
theorem B2652011 : Blo 1178406 2652011 := bstep (se 1 (by rfl) ⟨1989008, by rfl⟩ : syracuseStep 2652011 = 3978017) B3978017
theorem B2652065 : Blo 1178406 2652065 := bstep (se 2 (by rfl) ⟨994524, by rfl⟩ : syracuseStep 2652065 = 1989049) B1989049
theorem B12744641 : Blo 1178406 12744641 := bstep (se 2 (by rfl) ⟨4779240, by rfl⟩ : syracuseStep 12744641 = 9558481) B9558481
theorem B1988617 : Blo 1178406 1988617 := bstep (se 2 (by rfl) ⟨745731, by rfl⟩ : syracuseStep 1988617 = 1491463) B1491463
theorem B3979421 : Blo 1178406 3979421 := bstep (se 3 (by rfl) ⟨746141, by rfl⟩ : syracuseStep 3979421 = 1492283) B1492283
theorem B1988779 : Blo 1178406 1988779 := bstep (se 1 (by rfl) ⟨1491584, by rfl⟩ : syracuseStep 1988779 = 2983169) B2983169
theorem B1767623 : Blo 1178406 1767623 := bstep (se 1 (by rfl) ⟨1325717, by rfl⟩ : syracuseStep 1767623 = 2651435) B2651435
theorem B2652407 : Blo 1178406 2652407 := bstep (se 1 (by rfl) ⟨1989305, by rfl⟩ : syracuseStep 2652407 = 3978611) B3978611
theorem B13621553 : Blo 1178406 13621553 := bstep (se 2 (by rfl) ⟨5108082, by rfl⟩ : syracuseStep 13621553 = 10216165) B10216165
theorem B6715709 : Blo 1178406 6715709 := bstep (se 3 (by rfl) ⟨1259195, by rfl⟩ : syracuseStep 6715709 = 2518391) B2518391
theorem B1767785 : Blo 1178406 1767785 := bstep (se 2 (by rfl) ⟨662919, by rfl⟩ : syracuseStep 1767785 = 1325839) B1325839
theorem B1767863 : Blo 1178406 1767863 := bstep (se 1 (by rfl) ⟨1325897, by rfl⟩ : syracuseStep 1767863 = 2651795) B2651795
theorem B1767899 : Blo 1178406 1767899 := bstep (se 1 (by rfl) ⟨1325924, by rfl⟩ : syracuseStep 1767899 = 2651849) B2651849
theorem B1989083 : Blo 1178406 1989083 := bstep (se 1 (by rfl) ⟨1491812, by rfl⟩ : syracuseStep 1989083 = 2983625) B2983625
theorem B5036525 : Blo 1178406 5036525 := bstep (se 3 (by rfl) ⟨944348, by rfl⟩ : syracuseStep 5036525 = 1888697) B1888697
theorem B3979961 : Blo 1178406 3979961 := bstep (se 2 (by rfl) ⟨1492485, by rfl⟩ : syracuseStep 3979961 = 2984971) B2984971
theorem B1325767 : Blo 1178406 1325767 := bstep (se 1 (by rfl) ⟨994325, by rfl⟩ : syracuseStep 1325767 = 1988651) B1988651
theorem B1989319 : Blo 1178406 1989319 := bstep (se 1 (by rfl) ⟨1491989, by rfl⟩ : syracuseStep 1989319 = 2983979) B2983979
theorem B7559891 : Blo 1178406 7559891 := bstep (se 1 (by rfl) ⟨5669918, by rfl⟩ : syracuseStep 7559891 = 11339837) B11339837
theorem B17013493 : Blo 1178406 17013493 := bstep (se 5 (by rfl) ⟨797507, by rfl⟩ : syracuseStep 17013493 = 1595015) B1595015
theorem B8952605 : Blo 1178406 8952605 := bstep (se 3 (by rfl) ⟨1678613, by rfl⟩ : syracuseStep 8952605 = 3357227) B3357227
theorem B1178407 : Blo 1178406 1178407 := bstep (se 1 (by rfl) ⟨883805, by rfl⟩ : syracuseStep 1178407 = 1767611) B1767611
theorem B4848427 : Blo 1178406 4848427 := bstep (se 1 (by rfl) ⟨3636320, by rfl⟩ : syracuseStep 4848427 = 7272641) B7272641
theorem B2653001 : Blo 1178406 2653001 := bstep (se 2 (by rfl) ⟨994875, by rfl⟩ : syracuseStep 2653001 = 1989751) B1989751
theorem B1178447 : Blo 1178406 1178447 := bstep (se 1 (by rfl) ⟨883835, by rfl⟩ : syracuseStep 1178447 = 1767671) B1767671
theorem B38255449 : Blo 1178406 38255449 := bstep (se 2 (by rfl) ⟨14345793, by rfl⟩ : syracuseStep 38255449 = 28691587) B28691587
theorem B1178463 : Blo 1178406 1178463 := bstep (se 1 (by rfl) ⟨883847, by rfl⟩ : syracuseStep 1178463 = 1767695) B1767695
theorem B1989481 : Blo 1178406 1989481 := bstep (se 2 (by rfl) ⟨746055, by rfl⟩ : syracuseStep 1989481 = 1492111) B1492111
theorem B1178491 : Blo 1178406 1178491 := bstep (se 1 (by rfl) ⟨883868, by rfl⟩ : syracuseStep 1178491 = 1767737) B1767737
theorem B8616851 : Blo 1178406 8616851 := bstep (se 1 (by rfl) ⟨6462638, by rfl⟩ : syracuseStep 8616851 = 12925277) B12925277
theorem B1178543 : Blo 1178406 1178543 := bstep (se 1 (by rfl) ⟨883907, by rfl⟩ : syracuseStep 1178543 = 1767815) B1767815
theorem B1768367 : Blo 1178406 1768367 := bstep (se 1 (by rfl) ⟨1326275, by rfl⟩ : syracuseStep 1768367 = 2652551) B2652551
theorem B1178567 : Blo 1178406 1178567 := bstep (se 1 (by rfl) ⟨883925, by rfl⟩ : syracuseStep 1178567 = 1767851) B1767851
theorem B1178587 : Blo 1178406 1178587 := bstep (se 1 (by rfl) ⟨883940, by rfl⟩ : syracuseStep 1178587 = 1767881) B1767881
theorem B1768457 : Blo 1178406 1768457 := bstep (se 2 (by rfl) ⟨663171, by rfl⟩ : syracuseStep 1768457 = 1326343) B1326343
theorem B1178663 : Blo 1178406 1178663 := bstep (se 1 (by rfl) ⟨883997, by rfl⟩ : syracuseStep 1178663 = 1767995) B1767995
theorem B1768487 : Blo 1178406 1768487 := bstep (se 1 (by rfl) ⟨1326365, by rfl⟩ : syracuseStep 1768487 = 2652731) B2652731
theorem B5970995 : Blo 1178406 5970995 := bstep (se 1 (by rfl) ⟨4478246, by rfl⟩ : syracuseStep 5970995 = 8956493) B8956493
theorem B1178703 : Blo 1178406 1178703 := bstep (se 1 (by rfl) ⟨884027, by rfl⟩ : syracuseStep 1178703 = 1768055) B1768055
theorem B1178719 : Blo 1178406 1178719 := bstep (se 1 (by rfl) ⟨884039, by rfl⟩ : syracuseStep 1178719 = 1768079) B1768079
theorem B1178747 : Blo 1178406 1178747 := bstep (se 1 (by rfl) ⟨884060, by rfl⟩ : syracuseStep 1178747 = 1768121) B1768121
theorem B1768571 : Blo 1178406 1768571 := bstep (se 1 (by rfl) ⟨1326428, by rfl⟩ : syracuseStep 1768571 = 2652857) B2652857
theorem B1178799 : Blo 1178406 1178799 := bstep (se 1 (by rfl) ⟨884099, by rfl⟩ : syracuseStep 1178799 = 1768199) B1768199
theorem B1178823 : Blo 1178406 1178823 := bstep (se 1 (by rfl) ⟨884117, by rfl⟩ : syracuseStep 1178823 = 1768235) B1768235
theorem B1178843 : Blo 1178406 1178843 := bstep (se 1 (by rfl) ⟨884132, by rfl⟩ : syracuseStep 1178843 = 1768265) B1768265
theorem B1768697 : Blo 1178406 1768697 := bstep (se 2 (by rfl) ⟨663261, by rfl⟩ : syracuseStep 1768697 = 1326523) B1326523
theorem B3980555 : Blo 1178406 3980555 := bstep (se 1 (by rfl) ⟨2985416, by rfl⟩ : syracuseStep 3980555 = 5970833) B5970833
theorem B1178919 : Blo 1178406 1178919 := bstep (se 1 (by rfl) ⟨884189, by rfl⟩ : syracuseStep 1178919 = 1768379) B1768379
theorem B3775805 : Blo 1178406 3775805 := bstep (se 3 (by rfl) ⟨707963, by rfl⟩ : syracuseStep 3775805 = 1415927) B1415927
theorem B1178959 : Blo 1178406 1178959 := bstep (se 1 (by rfl) ⟨884219, by rfl⟩ : syracuseStep 1178959 = 1768439) B1768439
theorem B4480343 : Blo 1178406 4480343 := bstep (se 1 (by rfl) ⟨3360257, by rfl⟩ : syracuseStep 4480343 = 6720515) B6720515
theorem B1178975 : Blo 1178406 1178975 := bstep (se 1 (by rfl) ⟨884231, by rfl⟩ : syracuseStep 1178975 = 1768463) B1768463
theorem B1768799 : Blo 1178406 1768799 := bstep (se 1 (by rfl) ⟨1326599, by rfl⟩ : syracuseStep 1768799 = 2653199) B2653199
theorem B1768811 : Blo 1178406 1768811 := bstep (se 1 (by rfl) ⟨1326608, by rfl⟩ : syracuseStep 1768811 = 2653217) B2653217
theorem B1179003 : Blo 1178406 1179003 := bstep (se 1 (by rfl) ⟨884252, by rfl⟩ : syracuseStep 1179003 = 1768505) B1768505
theorem B1179055 : Blo 1178406 1179055 := bstep (se 1 (by rfl) ⟨884291, by rfl⟩ : syracuseStep 1179055 = 1768583) B1768583
theorem B1990075 : Blo 1178406 1990075 := bstep (se 1 (by rfl) ⟨1492556, by rfl⟩ : syracuseStep 1990075 = 2985113) B2985113
theorem B1179079 : Blo 1178406 1179079 := bstep (se 1 (by rfl) ⟨884309, by rfl⟩ : syracuseStep 1179079 = 1768619) B1768619
theorem B1179099 : Blo 1178406 1179099 := bstep (se 1 (by rfl) ⟨884324, by rfl⟩ : syracuseStep 1179099 = 1768649) B1768649
theorem B6716915 : Blo 1178406 6716915 := bstep (se 1 (by rfl) ⟨5037686, by rfl⟩ : syracuseStep 6716915 = 10075373) B10075373
theorem B3980825 : Blo 1178406 3980825 := bstep (se 2 (by rfl) ⟨1492809, by rfl⟩ : syracuseStep 3980825 = 2985619) B2985619
theorem B1179175 : Blo 1178406 1179175 := bstep (se 1 (by rfl) ⟨884381, by rfl⟩ : syracuseStep 1179175 = 1768763) B1768763
theorem B1326631 : Blo 1178406 1326631 := bstep (se 1 (by rfl) ⟨994973, by rfl⟩ : syracuseStep 1326631 = 1989947) B1989947
theorem B1990183 : Blo 1178406 1990183 := bstep (se 1 (by rfl) ⟨1492637, by rfl⟩ : syracuseStep 1990183 = 2985275) B2985275
theorem B1179215 : Blo 1178406 1179215 := bstep (se 1 (by rfl) ⟨884411, by rfl⟩ : syracuseStep 1179215 = 1768823) B1768823
theorem B1769039 : Blo 1178406 1769039 := bstep (se 1 (by rfl) ⟨1326779, by rfl⟩ : syracuseStep 1769039 = 2653559) B2653559
theorem B1179231 : Blo 1178406 1179231 := bstep (se 1 (by rfl) ⟨884423, by rfl⟩ : syracuseStep 1179231 = 1768847) B1768847
theorem B2653793 : Blo 1178406 2653793 := bstep (se 2 (by rfl) ⟨995172, by rfl⟩ : syracuseStep 2653793 = 1990345) B1990345
theorem B1179259 : Blo 1178406 1179259 := bstep (se 1 (by rfl) ⟨884444, by rfl⟩ : syracuseStep 1179259 = 1768889) B1768889
theorem B1179311 : Blo 1178406 1179311 := bstep (se 1 (by rfl) ⟨884483, by rfl⟩ : syracuseStep 1179311 = 1768967) B1768967
theorem B1179335 : Blo 1178406 1179335 := bstep (se 1 (by rfl) ⟨884501, by rfl⟩ : syracuseStep 1179335 = 1769003) B1769003
theorem B1769159 : Blo 1178406 1769159 := bstep (se 1 (by rfl) ⟨1326869, by rfl⟩ : syracuseStep 1769159 = 2653739) B2653739
theorem B3776215 : Blo 1178406 3776215 := bstep (se 1 (by rfl) ⟨2832161, by rfl⟩ : syracuseStep 3776215 = 5664323) B5664323
theorem B1179355 : Blo 1178406 1179355 := bstep (se 1 (by rfl) ⟨884516, by rfl⟩ : syracuseStep 1179355 = 1769033) B1769033
theorem B1179431 : Blo 1178406 1179431 := bstep (se 1 (by rfl) ⟨884573, by rfl⟩ : syracuseStep 1179431 = 1769147) B1769147
theorem B1179471 : Blo 1178406 1179471 := bstep (se 1 (by rfl) ⟨884603, by rfl⟩ : syracuseStep 1179471 = 1769207) B1769207
theorem B1179487 : Blo 1178406 1179487 := bstep (se 1 (by rfl) ⟨884615, by rfl⟩ : syracuseStep 1179487 = 1769231) B1769231
theorem B1769321 : Blo 1178406 1769321 := bstep (se 2 (by rfl) ⟨663495, by rfl⟩ : syracuseStep 1769321 = 1326991) B1326991
theorem B1990507 : Blo 1178406 1990507 := bstep (se 1 (by rfl) ⟨1492880, by rfl⟩ : syracuseStep 1990507 = 2985761) B2985761
theorem B1179515 : Blo 1178406 1179515 := bstep (se 1 (by rfl) ⟨884636, by rfl⟩ : syracuseStep 1179515 = 1769273) B1769273
theorem B9559943 : Blo 1178406 9559943 := bstep (se 1 (by rfl) ⟨7169957, by rfl⟩ : syracuseStep 9559943 = 14339915) B14339915
theorem B1179567 : Blo 1178406 1179567 := bstep (se 1 (by rfl) ⟨884675, by rfl⟩ : syracuseStep 1179567 = 1769351) B1769351
theorem B1769399 : Blo 1178406 1769399 := bstep (se 1 (by rfl) ⟨1327049, by rfl⟩ : syracuseStep 1769399 = 2654099) B2654099
theorem B2654135 : Blo 1178406 2654135 := bstep (se 1 (by rfl) ⟨1990601, by rfl⟩ : syracuseStep 2654135 = 3981203) B3981203
theorem B1179591 : Blo 1178406 1179591 := bstep (se 1 (by rfl) ⟨884693, by rfl⟩ : syracuseStep 1179591 = 1769387) B1769387
theorem B1179611 : Blo 1178406 1179611 := bstep (se 1 (by rfl) ⟨884708, by rfl⟩ : syracuseStep 1179611 = 1769417) B1769417
theorem B1769435 : Blo 1178406 1769435 := bstep (se 1 (by rfl) ⟨1327076, by rfl⟩ : syracuseStep 1769435 = 2654153) B2654153
theorem B12918791 : Blo 1178406 12918791 := bstep (se 1 (by rfl) ⟨9689093, by rfl⟩ : syracuseStep 12918791 = 19378187) B19378187
theorem B1179935 : Blo 1178406 1179935 := bstep (se 1 (by rfl) ⟨884951, by rfl⟩ : syracuseStep 1179935 = 1769903) B1769903
theorem B1679707 : Blo 1178406 1679707 := bstep (se 1 (by rfl) ⟨1259780, by rfl⟩ : syracuseStep 1679707 = 2519561) B2519561
theorem B1769819 : Blo 1178406 1769819 := bstep (se 1 (by rfl) ⟨1327364, by rfl⟩ : syracuseStep 1769819 = 2654729) B2654729
theorem B1179995 : Blo 1178406 1179995 := bstep (se 1 (by rfl) ⟨884996, by rfl⟩ : syracuseStep 1179995 = 1769993) B1769993
theorem B1180015 : Blo 1178406 1180015 := bstep (se 1 (by rfl) ⟨885011, by rfl⟩ : syracuseStep 1180015 = 1770023) B1770023
theorem B1180071 : Blo 1178406 1180071 := bstep (se 1 (by rfl) ⟨885053, by rfl⟩ : syracuseStep 1180071 = 1770107) B1770107
theorem B3981743 : Blo 1178406 3981743 := bstep (se 1 (by rfl) ⟨2986307, by rfl⟩ : syracuseStep 3981743 = 5972615) B5972615
theorem B2654639 : Blo 1178406 2654639 := bstep (se 1 (by rfl) ⟨1990979, by rfl⟩ : syracuseStep 2654639 = 3981959) B3981959
theorem B2654675 : Blo 1178406 2654675 := bstep (se 1 (by rfl) ⟨1991006, by rfl⟩ : syracuseStep 2654675 = 3982013) B3982013
theorem B1180155 : Blo 1178406 1180155 := bstep (se 1 (by rfl) ⟨885116, by rfl⟩ : syracuseStep 1180155 = 1770233) B1770233
theorem B1679935 : Blo 1178406 1679935 := bstep (se 1 (by rfl) ⟨1259951, by rfl⟩ : syracuseStep 1679935 = 2519903) B2519903
theorem B2654783 : Blo 1178406 2654783 := bstep (se 1 (by rfl) ⟨1991087, by rfl⟩ : syracuseStep 2654783 = 3982175) B3982175
theorem B1770047 : Blo 1178406 1770047 := bstep (se 1 (by rfl) ⟨1327535, by rfl⟩ : syracuseStep 1770047 = 2655071) B2655071
theorem B1180223 : Blo 1178406 1180223 := bstep (se 1 (by rfl) ⟨885167, by rfl⟩ : syracuseStep 1180223 = 1770335) B1770335
theorem B1180231 : Blo 1178406 1180231 := bstep (se 1 (by rfl) ⟨885173, by rfl⟩ : syracuseStep 1180231 = 1770347) B1770347
theorem B1327711 : Blo 1178406 1327711 := bstep (se 1 (by rfl) ⟨995783, by rfl⟩ : syracuseStep 1327711 = 1991567) B1991567
theorem B6718099 : Blo 1178406 6718099 := bstep (se 1 (by rfl) ⟨5038574, by rfl⟩ : syracuseStep 6718099 = 10077149) B10077149
theorem B2654891 : Blo 1178406 2654891 := bstep (se 1 (by rfl) ⟨1991168, by rfl⟩ : syracuseStep 2654891 = 3982337) B3982337
theorem B1991351 : Blo 1178406 1991351 := bstep (se 1 (by rfl) ⟨1493513, by rfl⟩ : syracuseStep 1991351 = 2987027) B2987027
theorem B1770167 : Blo 1178406 1770167 := bstep (se 1 (by rfl) ⟨1327625, by rfl⟩ : syracuseStep 1770167 = 2655251) B2655251
theorem B12919499 : Blo 1178406 12919499 := bstep (se 1 (by rfl) ⟨9689624, by rfl⟩ : syracuseStep 12919499 = 19379249) B19379249
theorem B1180383 : Blo 1178406 1180383 := bstep (se 1 (by rfl) ⟨885287, by rfl⟩ : syracuseStep 1180383 = 1770575) B1770575
theorem B1491691 : Blo 1178406 1491691 := bstep (se 1 (by rfl) ⟨1118768, by rfl⟩ : syracuseStep 1491691 = 2237537) B2237537
theorem B2950031 : Blo 1178406 2950031 := bstep (se 1 (by rfl) ⟨2212523, by rfl⟩ : syracuseStep 2950031 = 4425047) B4425047
theorem B1770395 : Blo 1178406 1770395 := bstep (se 1 (by rfl) ⟨1327796, by rfl⟩ : syracuseStep 1770395 = 2655593) B2655593
theorem B22684657 : Blo 1178406 22684657 := bstep (se 2 (by rfl) ⟨8506746, by rfl⟩ : syracuseStep 22684657 = 17013493) B17013493
theorem B3736567 : Blo 1178406 3736567 := bstep (se 1 (by rfl) ⟨2802425, by rfl⟩ : syracuseStep 3736567 = 5604851) B5604851
theorem B16139407 : Blo 1178406 16139407 := bstep (se 1 (by rfl) ⟨12104555, by rfl⟩ : syracuseStep 16139407 = 24209111) B24209111
theorem B2655431 : Blo 1178406 2655431 := bstep (se 1 (by rfl) ⟨1991573, by rfl⟩ : syracuseStep 2655431 = 3983147) B3983147
theorem B2688233 : Blo 1178406 2688233 := bstep (se 2 (by rfl) ⟨1008087, by rfl⟩ : syracuseStep 2688233 = 2016175) B2016175
theorem B8496427 : Blo 1178406 8496427 := bstep (se 1 (by rfl) ⟨6372320, by rfl⟩ : syracuseStep 8496427 = 12744641) B12744641
theorem B3982715 : Blo 1178406 3982715 := bstep (se 1 (by rfl) ⟨2987036, by rfl⟩ : syracuseStep 3982715 = 5974073) B5974073
theorem B2655611 : Blo 1178406 2655611 := bstep (se 1 (by rfl) ⟨1991708, by rfl⟩ : syracuseStep 2655611 = 3983417) B3983417
theorem B5670283 : Blo 1178406 5670283 := bstep (se 1 (by rfl) ⟨4252712, by rfl⟩ : syracuseStep 5670283 = 8505425) B8505425
theorem B2655737 : Blo 1178406 2655737 := bstep (se 2 (by rfl) ⟨995901, by rfl⟩ : syracuseStep 2655737 = 1991803) B1991803
theorem B2655827 : Blo 1178406 2655827 := bstep (se 1 (by rfl) ⟨1991870, by rfl⟩ : syracuseStep 2655827 = 3983741) B3983741
theorem B3229345 : Blo 1178406 3229345 := bstep (se 2 (by rfl) ⟨1211004, by rfl⟩ : syracuseStep 3229345 = 2422009) B2422009
theorem B1492663 : Blo 1178406 1492663 := bstep (se 1 (by rfl) ⟨1119497, by rfl⟩ : syracuseStep 1492663 = 2238995) B2238995
theorem B5039927 : Blo 1178406 5039927 := bstep (se 1 (by rfl) ⟨3779945, by rfl⟩ : syracuseStep 5039927 = 7559891) B7559891
theorem B5744567 : Blo 1178406 5744567 := bstep (se 1 (by rfl) ⟨4308425, by rfl⟩ : syracuseStep 5744567 = 8616851) B8616851
theorem B4540367 : Blo 1178406 4540367 := bstep (se 1 (by rfl) ⟨3405275, by rfl⟩ : syracuseStep 4540367 = 6810551) B6810551
theorem B10217657 : Blo 1178406 10217657 := bstep (se 2 (by rfl) ⟨3831621, by rfl⟩ : syracuseStep 10217657 = 7663243) B7663243
theorem B2517203 : Blo 1178406 2517203 := bstep (se 1 (by rfl) ⟨1887902, by rfl⟩ : syracuseStep 2517203 = 3775805) B3775805
theorem B15124745 : Blo 1178406 15124745 := bstep (se 2 (by rfl) ⟨5671779, by rfl⟩ : syracuseStep 15124745 = 11343559) B11343559
theorem B2984303 : Blo 1178406 2984303 := bstep (se 1 (by rfl) ⟨2238227, by rfl⟩ : syracuseStep 2984303 = 4476455) B4476455
theorem B3361135 : Blo 1178406 3361135 := bstep (se 1 (by rfl) ⟨2520851, by rfl⟩ : syracuseStep 3361135 = 5041703) B5041703
theorem B5974397 : Blo 1178406 5974397 := bstep (se 3 (by rfl) ⟨1120199, by rfl⟩ : syracuseStep 5974397 = 2240399) B2240399
theorem B22677893 : Blo 1178406 22677893 := bstep (se 4 (by rfl) ⟨2126052, by rfl⟩ : syracuseStep 22677893 = 4252105) B4252105
theorem B12749399 : Blo 1178406 12749399 := bstep (se 1 (by rfl) ⟨9562049, by rfl⟩ : syracuseStep 12749399 = 19124099) B19124099
theorem B5966459 : Blo 1178406 5966459 := bstep (se 1 (by rfl) ⟨4474844, by rfl⟩ : syracuseStep 5966459 = 8949689) B8949689
theorem B2017975 : Blo 1178406 2017975 := bstep (se 1 (by rfl) ⟨1513481, by rfl⟩ : syracuseStep 2017975 = 3026963) B3026963
theorem B11332487 : Blo 1178406 11332487 := bstep (se 1 (by rfl) ⟨8499365, by rfl⟩ : syracuseStep 11332487 = 16998731) B16998731
theorem B2984951 : Blo 1178406 2984951 := bstep (se 1 (by rfl) ⟨2238713, by rfl⟩ : syracuseStep 2984951 = 4477427) B4477427
theorem B2985083 : Blo 1178406 2985083 := bstep (se 1 (by rfl) ⟨2238812, by rfl⟩ : syracuseStep 2985083 = 4477625) B4477625
theorem B25857197 : Blo 1178406 25857197 := bstep (se 3 (by rfl) ⟨4848224, by rfl⟩ : syracuseStep 25857197 = 9696449) B9696449
theorem B30641627 : Blo 1178406 30641627 := bstep (se 1 (by rfl) ⟨22981220, by rfl⟩ : syracuseStep 30641627 = 45962441) B45962441
theorem B21535631 : Blo 1178406 21535631 := bstep (se 1 (by rfl) ⟨16151723, by rfl⟩ : syracuseStep 21535631 = 32303447) B32303447
theorem B11488979 : Blo 1178406 11488979 := bstep (se 1 (by rfl) ⟨8616734, by rfl⟩ : syracuseStep 11488979 = 17233469) B17233469
theorem B51007265 : Blo 1178406 51007265 := bstep (se 2 (by rfl) ⟨19127724, by rfl⟩ : syracuseStep 51007265 = 38255449) B38255449
theorem B1593167 : Blo 1178406 1593167 := bstep (se 1 (by rfl) ⟨1194875, by rfl⟩ : syracuseStep 1593167 = 2389751) B2389751
theorem B5042027 : Blo 1178406 5042027 := bstep (se 1 (by rfl) ⟨3781520, by rfl⟩ : syracuseStep 5042027 = 7563041) B7563041
theorem B5107585 : Blo 1178406 5107585 := bstep (se 2 (by rfl) ⟨1915344, by rfl⟩ : syracuseStep 5107585 = 3830689) B3830689
theorem B9081035 : Blo 1178406 9081035 := bstep (se 1 (by rfl) ⟨6810776, by rfl⟩ : syracuseStep 9081035 = 13621553) B13621553
theorem B4477139 : Blo 1178406 4477139 := bstep (se 1 (by rfl) ⟨3357854, by rfl⟩ : syracuseStep 4477139 = 6715709) B6715709
theorem B25858277 : Blo 1178406 25858277 := bstep (se 4 (by rfl) ⟨2424213, by rfl⟩ : syracuseStep 25858277 = 4848427) B4848427
theorem B3977747 : Blo 1178406 3977747 := bstep (se 1 (by rfl) ⟨2983310, by rfl⟩ : syracuseStep 3977747 = 5966621) B5966621
theorem B5968403 : Blo 1178406 5968403 := bstep (se 1 (by rfl) ⟨4476302, by rfl⟩ : syracuseStep 5968403 = 8952605) B8952605
theorem B10072775 : Blo 1178406 10072775 := bstep (se 1 (by rfl) ⟨7554581, by rfl⟩ : syracuseStep 10072775 = 15109163) B15109163
theorem B2986895 : Blo 1178406 2986895 := bstep (se 1 (by rfl) ⟨2240171, by rfl⟩ : syracuseStep 2986895 = 4480343) B4480343
theorem B5034953 : Blo 1178406 5034953 := bstep (se 2 (by rfl) ⟨1888107, by rfl⟩ : syracuseStep 5034953 = 3776215) B3776215
theorem B14349257 : Blo 1178406 14349257 := bstep (se 2 (by rfl) ⟨5380971, by rfl⟩ : syracuseStep 14349257 = 10761943) B10761943
theorem B5665783 : Blo 1178406 5665783 := bstep (se 1 (by rfl) ⟨4249337, by rfl⟩ : syracuseStep 5665783 = 8498675) B8498675
theorem B4477943 : Blo 1178406 4477943 := bstep (se 1 (by rfl) ⟨3358457, by rfl⟩ : syracuseStep 4477943 = 6716915) B6716915
theorem B38286593 : Blo 1178406 38286593 := bstep (se 2 (by rfl) ⟨14357472, by rfl⟩ : syracuseStep 38286593 = 28714945) B28714945
theorem B2651489 : Blo 1178406 2651489 := bstep (se 2 (by rfl) ⟨994308, by rfl⟩ : syracuseStep 2651489 = 1988617) B1988617
theorem B2987401 : Blo 1178406 2987401 := bstep (se 2 (by rfl) ⟨1120275, by rfl⟩ : syracuseStep 2987401 = 2240551) B2240551
theorem B6370721 : Blo 1178406 6370721 := bstep (se 2 (by rfl) ⟨2389020, by rfl⟩ : syracuseStep 6370721 = 4778041) B4778041
theorem B8074657 : Blo 1178406 8074657 := bstep (se 2 (by rfl) ⟨3027996, by rfl⟩ : syracuseStep 8074657 = 6055993) B6055993
theorem B2651579 : Blo 1178406 2651579 := bstep (se 1 (by rfl) ⟨1988684, by rfl⟩ : syracuseStep 2651579 = 3977369) B3977369
theorem B1889735 : Blo 1178406 1889735 := bstep (se 1 (by rfl) ⟨1417301, by rfl⟩ : syracuseStep 1889735 = 2834603) B2834603
theorem B2987513 : Blo 1178406 2987513 := bstep (se 2 (by rfl) ⟨1120317, by rfl⟩ : syracuseStep 2987513 = 2240635) B2240635
theorem B5035553 : Blo 1178406 5035553 := bstep (se 2 (by rfl) ⟨1888332, by rfl⟩ : syracuseStep 5035553 = 3776665) B3776665
theorem B2651705 : Blo 1178406 2651705 := bstep (se 2 (by rfl) ⟨994389, by rfl⟩ : syracuseStep 2651705 = 1988779) B1988779
theorem B34453363 : Blo 1178406 34453363 := bstep (se 1 (by rfl) ⟨25840022, by rfl⟩ : syracuseStep 34453363 = 51680045) B51680045
theorem B6379715 : Blo 1178406 6379715 := bstep (se 1 (by rfl) ⟨4784786, by rfl⟩ : syracuseStep 6379715 = 9569573) B9569573
theorem B2652371 : Blo 1178406 2652371 := bstep (se 1 (by rfl) ⟨1989278, by rfl⟩ : syracuseStep 2652371 = 3978557) B3978557
theorem B1767689 : Blo 1178406 1767689 := bstep (se 2 (by rfl) ⟨662883, by rfl⟩ : syracuseStep 1767689 = 1325767) B1325767
theorem B2652425 : Blo 1178406 2652425 := bstep (se 2 (by rfl) ⟨994659, by rfl⟩ : syracuseStep 2652425 = 1989319) B1989319
theorem B3979529 : Blo 1178406 3979529 := bstep (se 2 (by rfl) ⟨1492323, by rfl⟩ : syracuseStep 3979529 = 2984647) B2984647
theorem B5970185 : Blo 1178406 5970185 := bstep (se 2 (by rfl) ⟨2238819, by rfl⟩ : syracuseStep 5970185 = 4477639) B4477639
theorem B1767791 : Blo 1178406 1767791 := bstep (se 1 (by rfl) ⟨1325843, by rfl⟩ : syracuseStep 1767791 = 2651687) B2651687
theorem B1988975 : Blo 1178406 1988975 := bstep (se 1 (by rfl) ⟨1491731, by rfl⟩ : syracuseStep 1988975 = 2983463) B2983463
theorem B5454191 : Blo 1178406 5454191 := bstep (se 1 (by rfl) ⟨4090643, by rfl⟩ : syracuseStep 5454191 = 8181287) B8181287
theorem B8960381 : Blo 1178406 8960381 := bstep (se 3 (by rfl) ⟨1680071, by rfl⟩ : syracuseStep 8960381 = 3360143) B3360143
theorem B2832815 : Blo 1178406 2832815 := bstep (se 1 (by rfl) ⟨2124611, by rfl⟩ : syracuseStep 2832815 = 4249223) B4249223
theorem B2652641 : Blo 1178406 2652641 := bstep (se 2 (by rfl) ⟨994740, by rfl⟩ : syracuseStep 2652641 = 1989481) B1989481
theorem B7174651 : Blo 1178406 7174651 := bstep (se 1 (by rfl) ⟨5380988, by rfl⟩ : syracuseStep 7174651 = 10761977) B10761977
theorem B1768007 : Blo 1178406 1768007 := bstep (se 1 (by rfl) ⟨1326005, by rfl⟩ : syracuseStep 1768007 = 2652011) B2652011
theorem B1989191 : Blo 1178406 1989191 := bstep (se 1 (by rfl) ⟨1491893, by rfl⟩ : syracuseStep 1989191 = 2983787) B2983787
theorem B1768043 : Blo 1178406 1768043 := bstep (se 1 (by rfl) ⟨1326032, by rfl⟩ : syracuseStep 1768043 = 2652065) B2652065
theorem B2652947 : Blo 1178406 2652947 := bstep (se 1 (by rfl) ⟨1989710, by rfl⟩ : syracuseStep 2652947 = 3979421) B3979421
theorem B1178415 : Blo 1178406 1178415 := bstep (se 1 (by rfl) ⟨883811, by rfl⟩ : syracuseStep 1178415 = 1767623) B1767623
theorem B5036867 : Blo 1178406 5036867 := bstep (se 1 (by rfl) ⟨3777650, by rfl⟩ : syracuseStep 5036867 = 7555301) B7555301
theorem B1768271 : Blo 1178406 1768271 := bstep (se 1 (by rfl) ⟨1326203, by rfl⟩ : syracuseStep 1768271 = 2652407) B2652407
theorem B4479887 : Blo 1178406 4479887 := bstep (se 1 (by rfl) ⟨3359915, by rfl⟩ : syracuseStep 4479887 = 6719831) B6719831
theorem B1178523 : Blo 1178406 1178523 := bstep (se 1 (by rfl) ⟨883892, by rfl⟩ : syracuseStep 1178523 = 1767785) B1767785
theorem B5102507 : Blo 1178406 5102507 := bstep (se 1 (by rfl) ⟨3826880, by rfl⟩ : syracuseStep 5102507 = 7653761) B7653761
theorem B7551917 : Blo 1178406 7551917 := bstep (se 3 (by rfl) ⟨1415984, by rfl⟩ : syracuseStep 7551917 = 2831969) B2831969
theorem B13622201 : Blo 1178406 13622201 := bstep (se 2 (by rfl) ⟨5108325, by rfl⟩ : syracuseStep 13622201 = 10216651) B10216651
theorem B1178575 : Blo 1178406 1178575 := bstep (se 1 (by rfl) ⟨883931, by rfl⟩ : syracuseStep 1178575 = 1767863) B1767863
theorem B1178599 : Blo 1178406 1178599 := bstep (se 1 (by rfl) ⟨883949, by rfl⟩ : syracuseStep 1178599 = 1767899) B1767899
theorem B1326055 : Blo 1178406 1326055 := bstep (se 1 (by rfl) ⟨994541, by rfl⟩ : syracuseStep 1326055 = 1989083) B1989083
theorem B3357683 : Blo 1178406 3357683 := bstep (se 1 (by rfl) ⟨2518262, by rfl⟩ : syracuseStep 3357683 = 5036525) B5036525
theorem B1989623 : Blo 1178406 1989623 := bstep (se 1 (by rfl) ⟨1492217, by rfl⟩ : syracuseStep 1989623 = 2984435) B2984435
theorem B2653307 : Blo 1178406 2653307 := bstep (se 1 (by rfl) ⟨1989980, by rfl⟩ : syracuseStep 2653307 = 3979961) B3979961
theorem B25500865 : Blo 1178406 25500865 := bstep (se 2 (by rfl) ⟨9562824, by rfl⟩ : syracuseStep 25500865 = 19125649) B19125649
theorem B1768667 : Blo 1178406 1768667 := bstep (se 1 (by rfl) ⟨1326500, by rfl⟩ : syracuseStep 1768667 = 2653001) B2653001
theorem B2653433 : Blo 1178406 2653433 := bstep (se 2 (by rfl) ⟨995037, by rfl⟩ : syracuseStep 2653433 = 1990075) B1990075
theorem B1178911 : Blo 1178406 1178911 := bstep (se 1 (by rfl) ⟨884183, by rfl⟩ : syracuseStep 1178911 = 1768367) B1768367
theorem B1178971 : Blo 1178406 1178971 := bstep (se 1 (by rfl) ⟨884228, by rfl⟩ : syracuseStep 1178971 = 1768457) B1768457
theorem B1178991 : Blo 1178406 1178991 := bstep (se 1 (by rfl) ⟨884243, by rfl⟩ : syracuseStep 1178991 = 1768487) B1768487
theorem B3980663 : Blo 1178406 3980663 := bstep (se 1 (by rfl) ⟨2985497, by rfl⟩ : syracuseStep 3980663 = 5970995) B5970995
theorem B5971319 : Blo 1178406 5971319 := bstep (se 1 (by rfl) ⟨4478489, by rfl⟩ : syracuseStep 5971319 = 8956979) B8956979
theorem B1768841 : Blo 1178406 1768841 := bstep (se 2 (by rfl) ⟨663315, by rfl⟩ : syracuseStep 1768841 = 1326631) B1326631
theorem B2653577 : Blo 1178406 2653577 := bstep (se 2 (by rfl) ⟨995091, by rfl⟩ : syracuseStep 2653577 = 1990183) B1990183
theorem B1179047 : Blo 1178406 1179047 := bstep (se 1 (by rfl) ⟨884285, by rfl⟩ : syracuseStep 1179047 = 1768571) B1768571
theorem B1179131 : Blo 1178406 1179131 := bstep (se 1 (by rfl) ⟨884348, by rfl⟩ : syracuseStep 1179131 = 1768697) B1768697
theorem B2653703 : Blo 1178406 2653703 := bstep (se 1 (by rfl) ⟨1990277, by rfl⟩ : syracuseStep 2653703 = 3980555) B3980555
theorem B5971481 : Blo 1178406 5971481 := bstep (se 2 (by rfl) ⟨2239305, by rfl⟩ : syracuseStep 5971481 = 4478611) B4478611
theorem B1179199 : Blo 1178406 1179199 := bstep (se 1 (by rfl) ⟨884399, by rfl⟩ : syracuseStep 1179199 = 1768799) B1768799
theorem B1179207 : Blo 1178406 1179207 := bstep (se 1 (by rfl) ⟨884405, by rfl⟩ : syracuseStep 1179207 = 1768811) B1768811
theorem B11329105 : Blo 1178406 11329105 := bstep (se 2 (by rfl) ⟨4248414, by rfl⟩ : syracuseStep 11329105 = 8496829) B8496829
theorem B8494753 : Blo 1178406 8494753 := bstep (se 2 (by rfl) ⟨3185532, by rfl⟩ : syracuseStep 8494753 = 6371065) B6371065
theorem B2653883 : Blo 1178406 2653883 := bstep (se 1 (by rfl) ⟨1990412, by rfl⟩ : syracuseStep 2653883 = 3980825) B3980825
theorem B1179359 : Blo 1178406 1179359 := bstep (se 1 (by rfl) ⟨884519, by rfl⟩ : syracuseStep 1179359 = 1769039) B1769039
theorem B1769195 : Blo 1178406 1769195 := bstep (se 1 (by rfl) ⟨1326896, by rfl⟩ : syracuseStep 1769195 = 2653793) B2653793
theorem B1990379 : Blo 1178406 1990379 := bstep (se 1 (by rfl) ⟨1492784, by rfl⟩ : syracuseStep 1990379 = 2985569) B2985569
theorem B36298529 : Blo 1178406 36298529 := bstep (se 2 (by rfl) ⟨13611948, by rfl⟩ : syracuseStep 36298529 = 27223897) B27223897
theorem B1179439 : Blo 1178406 1179439 := bstep (se 1 (by rfl) ⟨884579, by rfl⟩ : syracuseStep 1179439 = 1769159) B1769159
theorem B6381359 : Blo 1178406 6381359 := bstep (se 1 (by rfl) ⟨4786019, by rfl⟩ : syracuseStep 6381359 = 9572039) B9572039
theorem B2654009 : Blo 1178406 2654009 := bstep (se 2 (by rfl) ⟨995253, by rfl⟩ : syracuseStep 2654009 = 1990507) B1990507
theorem B4480829 : Blo 1178406 4480829 := bstep (se 3 (by rfl) ⟨840155, by rfl⟩ : syracuseStep 4480829 = 1680311) B1680311
theorem B1179547 : Blo 1178406 1179547 := bstep (se 1 (by rfl) ⟨884660, by rfl⟩ : syracuseStep 1179547 = 1769321) B1769321
theorem B6373295 : Blo 1178406 6373295 := bstep (se 1 (by rfl) ⟨4779971, by rfl⟩ : syracuseStep 6373295 = 9559943) B9559943
theorem B1179599 : Blo 1178406 1179599 := bstep (se 1 (by rfl) ⟨884699, by rfl⟩ : syracuseStep 1179599 = 1769399) B1769399
theorem B1769423 : Blo 1178406 1769423 := bstep (se 1 (by rfl) ⟨1327067, by rfl⟩ : syracuseStep 1769423 = 2654135) B2654135
theorem B1179623 : Blo 1178406 1179623 := bstep (se 1 (by rfl) ⟨884717, by rfl⟩ : syracuseStep 1179623 = 1769435) B1769435
theorem B6054023 : Blo 1178406 6054023 := bstep (se 1 (by rfl) ⟨4540517, by rfl⟩ : syracuseStep 6054023 = 9081035) B9081035
theorem B1179879 : Blo 1178406 1179879 := bstep (se 1 (by rfl) ⟨884909, by rfl⟩ : syracuseStep 1179879 = 1769819) B1769819
theorem B2654495 : Blo 1178406 2654495 := bstep (se 1 (by rfl) ⟨1990871, by rfl⟩ : syracuseStep 2654495 = 3981743) B3981743
theorem B1769759 : Blo 1178406 1769759 := bstep (se 1 (by rfl) ⟨1327319, by rfl⟩ : syracuseStep 1769759 = 2654639) B2654639
theorem B1769783 : Blo 1178406 1769783 := bstep (se 1 (by rfl) ⟨1327337, by rfl⟩ : syracuseStep 1769783 = 2654675) B2654675
theorem B1769855 : Blo 1178406 1769855 := bstep (se 1 (by rfl) ⟨1327391, by rfl⟩ : syracuseStep 1769855 = 2654783) B2654783
theorem B1180031 : Blo 1178406 1180031 := bstep (se 1 (by rfl) ⟨885023, by rfl⟩ : syracuseStep 1180031 = 1770047) B1770047
theorem B1769927 : Blo 1178406 1769927 := bstep (se 1 (by rfl) ⟨1327445, by rfl⟩ : syracuseStep 1769927 = 2654891) B2654891
theorem B1327567 : Blo 1178406 1327567 := bstep (se 1 (by rfl) ⟨995675, by rfl⟩ : syracuseStep 1327567 = 1991351) B1991351
theorem B1180111 : Blo 1178406 1180111 := bstep (se 1 (by rfl) ⟨885083, by rfl⟩ : syracuseStep 1180111 = 1770167) B1770167
theorem B4481513 : Blo 1178406 4481513 := bstep (se 2 (by rfl) ⟨1680567, by rfl⟩ : syracuseStep 4481513 = 3361135) B3361135
theorem B1966687 : Blo 1178406 1966687 := bstep (se 1 (by rfl) ⟨1475015, by rfl⟩ : syracuseStep 1966687 = 2950031) B2950031
theorem B1991263 : Blo 1178406 1991263 := bstep (se 1 (by rfl) ⟨1493447, by rfl⟩ : syracuseStep 1991263 = 2986895) B2986895
theorem B1180263 : Blo 1178406 1180263 := bstep (se 1 (by rfl) ⟨885197, by rfl⟩ : syracuseStep 1180263 = 1770395) B1770395
theorem B7168621 : Blo 1178406 7168621 := bstep (se 3 (by rfl) ⟨1344116, by rfl⟩ : syracuseStep 7168621 = 2688233) B2688233
theorem B1770281 : Blo 1178406 1770281 := bstep (se 2 (by rfl) ⟨663855, by rfl⟩ : syracuseStep 1770281 = 1327711) B1327711
theorem B1770287 : Blo 1178406 1770287 := bstep (se 1 (by rfl) ⟨1327715, by rfl⟩ : syracuseStep 1770287 = 2655431) B2655431
theorem B2655143 : Blo 1178406 2655143 := bstep (se 1 (by rfl) ⟨1991357, by rfl⟩ : syracuseStep 2655143 = 3982715) B3982715
theorem B1770407 : Blo 1178406 1770407 := bstep (se 1 (by rfl) ⟨1327805, by rfl⟩ : syracuseStep 1770407 = 2655611) B2655611
theorem B1991675 : Blo 1178406 1991675 := bstep (se 1 (by rfl) ⟨1493756, by rfl⟩ : syracuseStep 1991675 = 2987513) B2987513
theorem B1770491 : Blo 1178406 1770491 := bstep (se 1 (by rfl) ⟨1327868, by rfl⟩ : syracuseStep 1770491 = 2655737) B2655737
theorem B1770551 : Blo 1178406 1770551 := bstep (se 1 (by rfl) ⟨1327913, by rfl⟩ : syracuseStep 1770551 = 2655827) B2655827
theorem B5039293 : Blo 1178406 5039293 := bstep (se 3 (by rfl) ⟨944867, by rfl⟩ : syracuseStep 5039293 = 1889735) B1889735
theorem B3359951 : Blo 1178406 3359951 := bstep (se 1 (by rfl) ⟨2519963, by rfl⟩ : syracuseStep 3359951 = 5039927) B5039927
theorem B30246209 : Blo 1178406 30246209 := bstep (se 2 (by rfl) ⟨11342328, by rfl⟩ : syracuseStep 30246209 = 22684657) B22684657
theorem B7554377 : Blo 1178406 7554377 := bstep (se 2 (by rfl) ⟨2832891, by rfl⟩ : syracuseStep 7554377 = 5665783) B5665783
theorem B4253143 : Blo 1178406 4253143 := bstep (se 1 (by rfl) ⟨3189857, by rfl⟩ : syracuseStep 4253143 = 6379715) B6379715
theorem B5973587 : Blo 1178406 5973587 := bstep (se 1 (by rfl) ⟨4480190, by rfl⟩ : syracuseStep 5973587 = 8960381) B8960381
theorem B3982931 : Blo 1178406 3982931 := bstep (se 1 (by rfl) ⟨2987198, by rfl⟩ : syracuseStep 3982931 = 5974397) B5974397
theorem B3983201 : Blo 1178406 3983201 := bstep (se 2 (by rfl) ⟨1493700, by rfl⟩ : syracuseStep 3983201 = 2987401) B2987401
theorem B10766209 : Blo 1178406 10766209 := bstep (se 2 (by rfl) ⟨4037328, by rfl⟩ : syracuseStep 10766209 = 8074657) B8074657
theorem B3401671 : Blo 1178406 3401671 := bstep (se 1 (by rfl) ⟨2551253, by rfl⟩ : syracuseStep 3401671 = 5102507) B5102507
theorem B2238455 : Blo 1178406 2238455 := bstep (se 1 (by rfl) ⟨1678841, by rfl⟩ : syracuseStep 2238455 = 3357683) B3357683
theorem B17238131 : Blo 1178406 17238131 := bstep (se 1 (by rfl) ⟨12928598, by rfl⟩ : syracuseStep 17238131 = 25857197) B25857197
theorem B6810113 : Blo 1178406 6810113 := bstep (se 2 (by rfl) ⟨2553792, by rfl⟩ : syracuseStep 6810113 = 5107585) B5107585
theorem B4254239 : Blo 1178406 4254239 := bstep (se 1 (by rfl) ⟨3190679, by rfl⟩ : syracuseStep 4254239 = 6381359) B6381359
theorem B3361351 : Blo 1178406 3361351 := bstep (se 1 (by rfl) ⟨2521013, by rfl⟩ : syracuseStep 3361351 = 5042027) B5042027
theorem B8612527 : Blo 1178406 8612527 := bstep (se 1 (by rfl) ⟨6459395, by rfl⟩ : syracuseStep 8612527 = 12918791) B12918791
theorem B2984759 : Blo 1178406 2984759 := bstep (se 1 (by rfl) ⟨2238569, by rfl⟩ : syracuseStep 2984759 = 4477139) B4477139
theorem B17238851 : Blo 1178406 17238851 := bstep (se 1 (by rfl) ⟨12929138, by rfl⟩ : syracuseStep 17238851 = 25858277) B25858277
theorem B8612999 : Blo 1178406 8612999 := bstep (se 1 (by rfl) ⟨6459749, by rfl⟩ : syracuseStep 8612999 = 12919499) B12919499
theorem B6712541 : Blo 1178406 6712541 := bstep (se 3 (by rfl) ⟨1258601, by rfl⟩ : syracuseStep 6712541 = 2517203) B2517203
theorem B2985295 : Blo 1178406 2985295 := bstep (se 1 (by rfl) ⟨2238971, by rfl⟩ : syracuseStep 2985295 = 4477943) B4477943
theorem B2239913 : Blo 1178406 2239913 := bstep (se 2 (by rfl) ⟨839967, by rfl⟩ : syracuseStep 2239913 = 1679935) B1679935
theorem B8957465 : Blo 1178406 8957465 := bstep (se 2 (by rfl) ⟨3359049, by rfl⟩ : syracuseStep 8957465 = 6718099) B6718099
theorem B2690633 : Blo 1178406 2690633 := bstep (se 2 (by rfl) ⟨1008987, by rfl⟩ : syracuseStep 2690633 = 2017975) B2017975
theorem B4247147 : Blo 1178406 4247147 := bstep (se 1 (by rfl) ⟨3185360, by rfl⟩ : syracuseStep 4247147 = 6370721) B6370721
theorem B3026911 : Blo 1178406 3026911 := bstep (se 1 (by rfl) ⟨2270183, by rfl⟩ : syracuseStep 3026911 = 4540367) B4540367
theorem B6811771 : Blo 1178406 6811771 := bstep (se 1 (by rfl) ⟨5108828, by rfl⟩ : syracuseStep 6811771 = 10217657) B10217657
theorem B34001153 : Blo 1178406 34001153 := bstep (se 2 (by rfl) ⟨12750432, by rfl⟩ : syracuseStep 34001153 = 25500865) B25500865
theorem B15118595 : Blo 1178406 15118595 := bstep (se 1 (by rfl) ⟨11338946, by rfl⟩ : syracuseStep 15118595 = 22677893) B22677893
theorem B1888543 : Blo 1178406 1888543 := bstep (se 1 (by rfl) ⟨1416407, by rfl⟩ : syracuseStep 1888543 = 2832815) B2832815
theorem B8499599 : Blo 1178406 8499599 := bstep (se 1 (by rfl) ⟨6374699, by rfl⟩ : syracuseStep 8499599 = 12749399) B12749399
theorem B3977639 : Blo 1178406 3977639 := bstep (se 1 (by rfl) ⟨2983229, by rfl⟩ : syracuseStep 3977639 = 5966459) B5966459
theorem B8958437 : Blo 1178406 8958437 := bstep (se 4 (by rfl) ⟨839853, by rfl⟩ : syracuseStep 8958437 = 1679707) B1679707
theorem B2986591 : Blo 1178406 2986591 := bstep (se 1 (by rfl) ⟨2239943, by rfl⟩ : syracuseStep 2986591 = 4479887) B4479887
theorem B14357087 : Blo 1178406 14357087 := bstep (se 1 (by rfl) ⟨10767815, by rfl⟩ : syracuseStep 14357087 = 21535631) B21535631
theorem B5034611 : Blo 1178406 5034611 := bstep (se 1 (by rfl) ⟨3775958, by rfl⟩ : syracuseStep 5034611 = 7551917) B7551917
theorem B9081467 : Blo 1178406 9081467 := bstep (se 1 (by rfl) ⟨6811100, by rfl⟩ : syracuseStep 9081467 = 13622201) B13622201
theorem B4248445 : Blo 1178406 4248445 := bstep (se 3 (by rfl) ⟨796583, by rfl⟩ : syracuseStep 4248445 = 1593167) B1593167
theorem B4305793 : Blo 1178406 4305793 := bstep (se 2 (by rfl) ⟨1614672, by rfl⟩ : syracuseStep 4305793 = 3229345) B3229345
theorem B11326337 : Blo 1178406 11326337 := bstep (se 2 (by rfl) ⟨4247376, by rfl⟩ : syracuseStep 11326337 = 8494753) B8494753
theorem B20427751 : Blo 1178406 20427751 := bstep (se 1 (by rfl) ⟨15320813, by rfl⟩ : syracuseStep 20427751 = 30641627) B30641627
theorem B45937817 : Blo 1178406 45937817 := bstep (se 2 (by rfl) ⟨17226681, by rfl⟩ : syracuseStep 45937817 = 34453363) B34453363
theorem B2987219 : Blo 1178406 2987219 := bstep (se 1 (by rfl) ⟨2240414, by rfl⟩ : syracuseStep 2987219 = 4480829) B4480829
theorem B4248863 : Blo 1178406 4248863 := bstep (se 1 (by rfl) ⟨3186647, by rfl⟩ : syracuseStep 4248863 = 6373295) B6373295
theorem B19928357 : Blo 1178406 19928357 := bstep (se 4 (by rfl) ⟨1868283, by rfl⟩ : syracuseStep 19928357 = 3736567) B3736567
theorem B2651831 : Blo 1178406 2651831 := bstep (se 1 (by rfl) ⟨1988873, by rfl⟩ : syracuseStep 2651831 = 3977747) B3977747
theorem B3978935 : Blo 1178406 3978935 := bstep (se 1 (by rfl) ⟨2984201, by rfl⟩ : syracuseStep 3978935 = 5968403) B5968403
theorem B6715183 : Blo 1178406 6715183 := bstep (se 1 (by rfl) ⟨5036387, by rfl⟩ : syracuseStep 6715183 = 10072775) B10072775
theorem B3356635 : Blo 1178406 3356635 := bstep (se 1 (by rfl) ⟨2517476, by rfl⟩ : syracuseStep 3356635 = 5034953) B5034953
theorem B9566171 : Blo 1178406 9566171 := bstep (se 1 (by rfl) ⟨7174628, by rfl⟩ : syracuseStep 9566171 = 14349257) B14349257
theorem B9566201 : Blo 1178406 9566201 := bstep (se 2 (by rfl) ⟨3587325, by rfl⟩ : syracuseStep 9566201 = 7174651) B7174651
theorem B25524395 : Blo 1178406 25524395 := bstep (se 1 (by rfl) ⟨19143296, by rfl⟩ : syracuseStep 25524395 = 38286593) B38286593
theorem B1767659 : Blo 1178406 1767659 := bstep (se 1 (by rfl) ⟨1325744, by rfl⟩ : syracuseStep 1767659 = 2651489) B2651489
theorem B1767719 : Blo 1178406 1767719 := bstep (se 1 (by rfl) ⟨1325789, by rfl⟩ : syracuseStep 1767719 = 2651579) B2651579
theorem B1988921 : Blo 1178406 1988921 := bstep (se 2 (by rfl) ⟨745845, by rfl⟩ : syracuseStep 1988921 = 1491691) B1491691
theorem B3357035 : Blo 1178406 3357035 := bstep (se 1 (by rfl) ⟨2517776, by rfl⟩ : syracuseStep 3357035 = 5035553) B5035553
theorem B1767803 : Blo 1178406 1767803 := bstep (se 1 (by rfl) ⟨1325852, by rfl⟩ : syracuseStep 1767803 = 2651705) B2651705
theorem B1768073 : Blo 1178406 1768073 := bstep (se 2 (by rfl) ⟨663027, by rfl⟩ : syracuseStep 1768073 = 1326055) B1326055
theorem B1768247 : Blo 1178406 1768247 := bstep (se 1 (by rfl) ⟨1326185, by rfl⟩ : syracuseStep 1768247 = 2652371) B2652371
theorem B1178459 : Blo 1178406 1178459 := bstep (se 1 (by rfl) ⟨883844, by rfl⟩ : syracuseStep 1178459 = 1767689) B1767689
theorem B1768283 : Blo 1178406 1768283 := bstep (se 1 (by rfl) ⟨1326212, by rfl⟩ : syracuseStep 1768283 = 2652425) B2652425
theorem B2653019 : Blo 1178406 2653019 := bstep (se 1 (by rfl) ⟨1989764, by rfl⟩ : syracuseStep 2653019 = 3979529) B3979529
theorem B3980123 : Blo 1178406 3980123 := bstep (se 1 (by rfl) ⟨2985092, by rfl⟩ : syracuseStep 3980123 = 5970185) B5970185
theorem B10083163 : Blo 1178406 10083163 := bstep (se 1 (by rfl) ⟨7562372, by rfl⟩ : syracuseStep 10083163 = 15124745) B15124745
theorem B21519209 : Blo 1178406 21519209 := bstep (se 2 (by rfl) ⟨8069703, by rfl⟩ : syracuseStep 21519209 = 16139407) B16139407
theorem B1178527 : Blo 1178406 1178527 := bstep (se 1 (by rfl) ⟨883895, by rfl⟩ : syracuseStep 1178527 = 1767791) B1767791
theorem B1325983 : Blo 1178406 1325983 := bstep (se 1 (by rfl) ⟨994487, by rfl⟩ : syracuseStep 1325983 = 1988975) B1988975
theorem B1989535 : Blo 1178406 1989535 := bstep (se 1 (by rfl) ⟨1492151, by rfl⟩ : syracuseStep 1989535 = 2984303) B2984303
theorem B3636127 : Blo 1178406 3636127 := bstep (se 1 (by rfl) ⟨2727095, by rfl⟩ : syracuseStep 3636127 = 5454191) B5454191
theorem B1768427 : Blo 1178406 1768427 := bstep (se 1 (by rfl) ⟨1326320, by rfl⟩ : syracuseStep 1768427 = 2652641) B2652641
theorem B1178671 : Blo 1178406 1178671 := bstep (se 1 (by rfl) ⟨884003, by rfl⟩ : syracuseStep 1178671 = 1768007) B1768007
theorem B1326127 : Blo 1178406 1326127 := bstep (se 1 (by rfl) ⟨994595, by rfl⟩ : syracuseStep 1326127 = 1989191) B1989191
theorem B11328569 : Blo 1178406 11328569 := bstep (se 2 (by rfl) ⟨4248213, by rfl⟩ : syracuseStep 11328569 = 8496427) B8496427
theorem B1178695 : Blo 1178406 1178695 := bstep (se 1 (by rfl) ⟨884021, by rfl⟩ : syracuseStep 1178695 = 1768043) B1768043
theorem B1768631 : Blo 1178406 1768631 := bstep (se 1 (by rfl) ⟨1326473, by rfl⟩ : syracuseStep 1768631 = 2652947) B2652947
theorem B7560377 : Blo 1178406 7560377 := bstep (se 2 (by rfl) ⟨2835141, by rfl⟩ : syracuseStep 7560377 = 5670283) B5670283
theorem B3357911 : Blo 1178406 3357911 := bstep (se 1 (by rfl) ⟨2518433, by rfl⟩ : syracuseStep 3357911 = 5036867) B5036867
theorem B1178847 : Blo 1178406 1178847 := bstep (se 1 (by rfl) ⟨884135, by rfl⟩ : syracuseStep 1178847 = 1768271) B1768271
theorem B1989967 : Blo 1178406 1989967 := bstep (se 1 (by rfl) ⟨1492475, by rfl⟩ : syracuseStep 1989967 = 2984951) B2984951
theorem B1326415 : Blo 1178406 1326415 := bstep (se 1 (by rfl) ⟨994811, by rfl⟩ : syracuseStep 1326415 = 1989623) B1989623
theorem B1768871 : Blo 1178406 1768871 := bstep (se 1 (by rfl) ⟨1326653, by rfl⟩ : syracuseStep 1768871 = 2653307) B2653307
theorem B1990055 : Blo 1178406 1990055 := bstep (se 1 (by rfl) ⟨1492541, by rfl⟩ : syracuseStep 1990055 = 2985083) B2985083
theorem B15105473 : Blo 1178406 15105473 := bstep (se 2 (by rfl) ⟨5664552, by rfl⟩ : syracuseStep 15105473 = 11329105) B11329105
theorem B1179111 : Blo 1178406 1179111 := bstep (se 1 (by rfl) ⟨884333, by rfl⟩ : syracuseStep 1179111 = 1768667) B1768667
theorem B1768955 : Blo 1178406 1768955 := bstep (se 1 (by rfl) ⟨1326716, by rfl⟩ : syracuseStep 1768955 = 2653433) B2653433
theorem B1990217 : Blo 1178406 1990217 := bstep (se 2 (by rfl) ⟨746331, by rfl⟩ : syracuseStep 1990217 = 1492663) B1492663
theorem B2653775 : Blo 1178406 2653775 := bstep (se 1 (by rfl) ⟨1990331, by rfl⟩ : syracuseStep 2653775 = 3980663) B3980663
theorem B3980879 : Blo 1178406 3980879 := bstep (se 1 (by rfl) ⟨2985659, by rfl⟩ : syracuseStep 3980879 = 5971319) B5971319
theorem B1179227 : Blo 1178406 1179227 := bstep (se 1 (by rfl) ⟨884420, by rfl⟩ : syracuseStep 1179227 = 1768841) B1768841
theorem B1769051 : Blo 1178406 1769051 := bstep (se 1 (by rfl) ⟨1326788, by rfl⟩ : syracuseStep 1769051 = 2653577) B2653577
theorem B1769135 : Blo 1178406 1769135 := bstep (se 1 (by rfl) ⟨1326851, by rfl⟩ : syracuseStep 1769135 = 2653703) B2653703
theorem B30219965 : Blo 1178406 30219965 := bstep (se 3 (by rfl) ⟨5666243, by rfl⟩ : syracuseStep 30219965 = 11332487) B11332487
theorem B3980987 : Blo 1178406 3980987 := bstep (se 1 (by rfl) ⟨2985740, by rfl⟩ : syracuseStep 3980987 = 5971481) B5971481
theorem B1769255 : Blo 1178406 1769255 := bstep (se 1 (by rfl) ⟨1326941, by rfl⟩ : syracuseStep 1769255 = 2653883) B2653883
theorem B7659319 : Blo 1178406 7659319 := bstep (se 1 (by rfl) ⟨5744489, by rfl⟩ : syracuseStep 7659319 = 11488979) B11488979
theorem B15318845 : Blo 1178406 15318845 := bstep (se 3 (by rfl) ⟨2872283, by rfl⟩ : syracuseStep 15318845 = 5744567) B5744567
theorem B1179463 : Blo 1178406 1179463 := bstep (se 1 (by rfl) ⟨884597, by rfl⟩ : syracuseStep 1179463 = 1769195) B1769195
theorem B1326919 : Blo 1178406 1326919 := bstep (se 1 (by rfl) ⟨995189, by rfl⟩ : syracuseStep 1326919 = 1990379) B1990379
theorem B24199019 : Blo 1178406 24199019 := bstep (se 1 (by rfl) ⟨18149264, by rfl⟩ : syracuseStep 24199019 = 36298529) B36298529
theorem B34004843 : Blo 1178406 34004843 := bstep (se 1 (by rfl) ⟨25503632, by rfl⟩ : syracuseStep 34004843 = 51007265) B51007265
theorem B1769339 : Blo 1178406 1769339 := bstep (se 1 (by rfl) ⟨1327004, by rfl⟩ : syracuseStep 1769339 = 2654009) B2654009
theorem B1179615 : Blo 1178406 1179615 := bstep (se 1 (by rfl) ⟨884711, by rfl⟩ : syracuseStep 1179615 = 1769423) B1769423
theorem B22667435 : Blo 1178406 22667435 := bstep (se 1 (by rfl) ⟨17000576, by rfl⟩ : syracuseStep 22667435 = 34001153) B34001153
theorem B1769663 : Blo 1178406 1769663 := bstep (se 1 (by rfl) ⟨1327247, by rfl⟩ : syracuseStep 1769663 = 2654495) B2654495
theorem B1179839 : Blo 1178406 1179839 := bstep (se 1 (by rfl) ⟨884879, by rfl⟩ : syracuseStep 1179839 = 1769759) B1769759
theorem B1179855 : Blo 1178406 1179855 := bstep (se 1 (by rfl) ⟨884891, by rfl⟩ : syracuseStep 1179855 = 1769783) B1769783
theorem B1179903 : Blo 1178406 1179903 := bstep (se 1 (by rfl) ⟨884927, by rfl⟩ : syracuseStep 1179903 = 1769855) B1769855
theorem B1179951 : Blo 1178406 1179951 := bstep (se 1 (by rfl) ⟨884963, by rfl⟩ : syracuseStep 1179951 = 1769927) B1769927
theorem B5972291 : Blo 1178406 5972291 := bstep (se 1 (by rfl) ⟨4479218, by rfl⟩ : syracuseStep 5972291 = 8958437) B8958437
theorem B6054311 : Blo 1178406 6054311 := bstep (se 1 (by rfl) ⟨4540733, by rfl⟩ : syracuseStep 6054311 = 9081467) B9081467
theorem B1180187 : Blo 1178406 1180187 := bstep (se 1 (by rfl) ⟨885140, by rfl⟩ : syracuseStep 1180187 = 1770281) B1770281
theorem B1180191 : Blo 1178406 1180191 := bstep (se 1 (by rfl) ⟨885143, by rfl⟩ : syracuseStep 1180191 = 1770287) B1770287
theorem B1770089 : Blo 1178406 1770089 := bstep (se 2 (by rfl) ⟨663783, by rfl⟩ : syracuseStep 1770089 = 1327567) B1327567
theorem B1770095 : Blo 1178406 1770095 := bstep (se 1 (by rfl) ⟨1327571, by rfl⟩ : syracuseStep 1770095 = 2655143) B2655143
theorem B1180271 : Blo 1178406 1180271 := bstep (se 1 (by rfl) ⟨885203, by rfl⟩ : syracuseStep 1180271 = 1770407) B1770407
theorem B1327783 : Blo 1178406 1327783 := bstep (se 1 (by rfl) ⟨995837, by rfl⟩ : syracuseStep 1327783 = 1991675) B1991675
theorem B1180327 : Blo 1178406 1180327 := bstep (se 1 (by rfl) ⟨885245, by rfl⟩ : syracuseStep 1180327 = 1770491) B1770491
theorem B1180367 : Blo 1178406 1180367 := bstep (se 1 (by rfl) ⟨885275, by rfl⟩ : syracuseStep 1180367 = 1770551) B1770551
theorem B4481801 : Blo 1178406 4481801 := bstep (se 2 (by rfl) ⟨1680675, by rfl⟩ : syracuseStep 4481801 = 3361351) B3361351
theorem B3982121 : Blo 1178406 3982121 := bstep (se 2 (by rfl) ⟨1493295, by rfl⟩ : syracuseStep 3982121 = 2986591) B2986591
theorem B2655017 : Blo 1178406 2655017 := bstep (se 2 (by rfl) ⟨995631, by rfl⟩ : syracuseStep 2655017 = 1991263) B1991263
theorem B1991479 : Blo 1178406 1991479 := bstep (se 1 (by rfl) ⟨1493609, by rfl⟩ : syracuseStep 1991479 = 2987219) B2987219
theorem B3982391 : Blo 1178406 3982391 := bstep (se 1 (by rfl) ⟨2986793, by rfl⟩ : syracuseStep 3982391 = 5973587) B5973587
theorem B2655287 : Blo 1178406 2655287 := bstep (se 1 (by rfl) ⟨1991465, by rfl⟩ : syracuseStep 2655287 = 3982931) B3982931
theorem B5973101 : Blo 1178406 5973101 := bstep (se 3 (by rfl) ⟨1119956, by rfl⟩ : syracuseStep 5973101 = 2239913) B2239913
theorem B13444217 : Blo 1178406 13444217 := bstep (se 2 (by rfl) ⟨5041581, by rfl⟩ : syracuseStep 13444217 = 10083163) B10083163
theorem B2655467 : Blo 1178406 2655467 := bstep (se 1 (by rfl) ⟨1991600, by rfl⟩ : syracuseStep 2655467 = 3983201) B3983201
theorem B17016263 : Blo 1178406 17016263 := bstep (se 1 (by rfl) ⟨12762197, by rfl⟩ : syracuseStep 17016263 = 25524395) B25524395
theorem B2238023 : Blo 1178406 2238023 := bstep (se 1 (by rfl) ⟨1678517, by rfl⟩ : syracuseStep 2238023 = 3357035) B3357035
theorem B6719057 : Blo 1178406 6719057 := bstep (se 2 (by rfl) ⟨2519646, by rfl⟩ : syracuseStep 6719057 = 5039293) B5039293
theorem B5670857 : Blo 1178406 5670857 := bstep (se 2 (by rfl) ⟨2126571, by rfl⟩ : syracuseStep 5670857 = 4253143) B4253143
theorem B5040251 : Blo 1178406 5040251 := bstep (se 1 (by rfl) ⟨3780188, by rfl⟩ : syracuseStep 5040251 = 7560377) B7560377
theorem B2238607 : Blo 1178406 2238607 := bstep (se 1 (by rfl) ⟨1678955, by rfl⟩ : syracuseStep 2238607 = 3357911) B3357911
theorem B4475027 : Blo 1178406 4475027 := bstep (se 1 (by rfl) ⟨3356270, by rfl⟩ : syracuseStep 4475027 = 6712541) B6712541
theorem B10070315 : Blo 1178406 10070315 := bstep (se 1 (by rfl) ⟨7552736, by rfl⟩ : syracuseStep 10070315 = 15105473) B15105473
theorem B20146643 : Blo 1178406 20146643 := bstep (se 1 (by rfl) ⟨15109982, by rfl⟩ : syracuseStep 20146643 = 30219965) B30219965
theorem B14354945 : Blo 1178406 14354945 := bstep (se 2 (by rfl) ⟨5383104, by rfl⟩ : syracuseStep 14354945 = 10766209) B10766209
theorem B16132679 : Blo 1178406 16132679 := bstep (se 1 (by rfl) ⟨12099509, by rfl⟩ : syracuseStep 16132679 = 24199019) B24199019
theorem B22669895 : Blo 1178406 22669895 := bstep (se 1 (by rfl) ⟨17002421, by rfl⟩ : syracuseStep 22669895 = 34004843) B34004843
theorem B4475513 : Blo 1178406 4475513 := bstep (se 2 (by rfl) ⟨1678317, by rfl⟩ : syracuseStep 4475513 = 3356635) B3356635
theorem B10079063 : Blo 1178406 10079063 := bstep (se 1 (by rfl) ⟨7559297, by rfl⟩ : syracuseStep 10079063 = 15118595) B15118595
theorem B2518057 : Blo 1178406 2518057 := bstep (se 2 (by rfl) ⟨944271, by rfl⟩ : syracuseStep 2518057 = 1888543) B1888543
theorem B9571391 : Blo 1178406 9571391 := bstep (se 1 (by rfl) ⟨7178543, by rfl⟩ : syracuseStep 9571391 = 14357087) B14357087
theorem B10488997 : Blo 1178406 10488997 := bstep (se 4 (by rfl) ⟨983343, by rfl⟩ : syracuseStep 10488997 = 1966687) B1966687
theorem B30625211 : Blo 1178406 30625211 := bstep (se 1 (by rfl) ⟨22968908, by rfl⟩ : syracuseStep 30625211 = 45937817) B45937817
theorem B2239967 : Blo 1178406 2239967 := bstep (se 1 (by rfl) ⟨1679975, by rfl⟩ : syracuseStep 2239967 = 3359951) B3359951
theorem B20164139 : Blo 1178406 20164139 := bstep (se 1 (by rfl) ⟨15123104, by rfl⟩ : syracuseStep 20164139 = 30246209) B30246209
theorem B5664593 : Blo 1178406 5664593 := bstep (se 2 (by rfl) ⟨2124222, by rfl⟩ : syracuseStep 5664593 = 4248445) B4248445
theorem B183873397 : Blo 1178406 183873397 := bstep (se 5 (by rfl) ⟨8619065, by rfl⟩ : syracuseStep 183873397 = 17238131) B17238131
theorem B6377447 : Blo 1178406 6377447 := bstep (se 1 (by rfl) ⟨4783085, by rfl⟩ : syracuseStep 6377447 = 9566171) B9566171
theorem B6377467 : Blo 1178406 6377467 := bstep (se 1 (by rfl) ⟨4783100, by rfl⟩ : syracuseStep 6377467 = 9566201) B9566201
theorem B5971643 : Blo 1178406 5971643 := bstep (se 1 (by rfl) ⟨4478732, by rfl⟩ : syracuseStep 5971643 = 8957465) B8957465
theorem B2831431 : Blo 1178406 2831431 := bstep (se 1 (by rfl) ⟨2123573, by rfl⟩ : syracuseStep 2831431 = 4247147) B4247147
theorem B10212425 : Blo 1178406 10212425 := bstep (se 2 (by rfl) ⟨3829659, by rfl⟩ : syracuseStep 10212425 = 7659319) B7659319
theorem B10212563 : Blo 1178406 10212563 := bstep (se 1 (by rfl) ⟨7659422, by rfl⟩ : syracuseStep 10212563 = 15318845) B15318845
theorem B4535561 : Blo 1178406 4535561 := bstep (se 2 (by rfl) ⟨1700835, by rfl⟩ : syracuseStep 4535561 = 3401671) B3401671
theorem B4035881 : Blo 1178406 4035881 := bstep (se 2 (by rfl) ⟨1513455, by rfl⟩ : syracuseStep 4035881 = 3026911) B3026911
theorem B5969213 : Blo 1178406 5969213 := bstep (se 3 (by rfl) ⟨1119227, by rfl⟩ : syracuseStep 5969213 = 2238455) B2238455
theorem B4036015 : Blo 1178406 4036015 := bstep (se 1 (by rfl) ⟨3027011, by rfl⟩ : syracuseStep 4036015 = 6054023) B6054023
theorem B9082361 : Blo 1178406 9082361 := bstep (se 2 (by rfl) ⟨3405885, by rfl⟩ : syracuseStep 9082361 = 6811771) B6811771
theorem B5666399 : Blo 1178406 5666399 := bstep (se 1 (by rfl) ⟨4249799, by rfl⟩ : syracuseStep 5666399 = 8499599) B8499599
theorem B2651759 : Blo 1178406 2651759 := bstep (se 1 (by rfl) ⟨1988819, by rfl⟩ : syracuseStep 2651759 = 3977639) B3977639
theorem B2987675 : Blo 1178406 2987675 := bstep (se 1 (by rfl) ⟨2240756, by rfl⟩ : syracuseStep 2987675 = 4481513) B4481513
theorem B3356407 : Blo 1178406 3356407 := bstep (se 1 (by rfl) ⟨2517305, by rfl⟩ : syracuseStep 3356407 = 5034611) B5034611
theorem B7550891 : Blo 1178406 7550891 := bstep (se 1 (by rfl) ⟨5663168, by rfl⟩ : syracuseStep 7550891 = 11326337) B11326337
theorem B9558161 : Blo 1178406 9558161 := bstep (se 2 (by rfl) ⟨3584310, by rfl⟩ : syracuseStep 9558161 = 7168621) B7168621
theorem B2832575 : Blo 1178406 2832575 := bstep (se 1 (by rfl) ⟨2124431, by rfl⟩ : syracuseStep 2832575 = 4248863) B4248863
theorem B13285571 : Blo 1178406 13285571 := bstep (se 1 (by rfl) ⟨9964178, by rfl⟩ : syracuseStep 13285571 = 19928357) B19928357
theorem B5036251 : Blo 1178406 5036251 := bstep (se 1 (by rfl) ⟨3777188, by rfl⟩ : syracuseStep 5036251 = 7554377) B7554377
theorem B11483369 : Blo 1178406 11483369 := bstep (se 2 (by rfl) ⟨4306263, by rfl⟩ : syracuseStep 11483369 = 8612527) B8612527
theorem B1767887 : Blo 1178406 1767887 := bstep (se 1 (by rfl) ⟨1325915, by rfl⟩ : syracuseStep 1767887 = 2651831) B2651831
theorem B2652623 : Blo 1178406 2652623 := bstep (se 1 (by rfl) ⟨1989467, by rfl⟩ : syracuseStep 2652623 = 3978935) B3978935
theorem B5741057 : Blo 1178406 5741057 := bstep (se 2 (by rfl) ⟨2152896, by rfl⟩ : syracuseStep 5741057 = 4305793) B4305793
theorem B1767977 : Blo 1178406 1767977 := bstep (se 2 (by rfl) ⟨662991, by rfl⟩ : syracuseStep 1767977 = 1325983) B1325983
theorem B2652713 : Blo 1178406 2652713 := bstep (se 2 (by rfl) ⟨994767, by rfl⟩ : syracuseStep 2652713 = 1989535) B1989535
theorem B4848169 : Blo 1178406 4848169 := bstep (se 2 (by rfl) ⟨1818063, by rfl⟩ : syracuseStep 4848169 = 3636127) B3636127
theorem B27237001 : Blo 1178406 27237001 := bstep (se 2 (by rfl) ⟨10213875, by rfl⟩ : syracuseStep 27237001 = 20427751) B20427751
theorem B18160301 : Blo 1178406 18160301 := bstep (se 3 (by rfl) ⟨3405056, by rfl⟩ : syracuseStep 18160301 = 6810113) B6810113
theorem B1768169 : Blo 1178406 1768169 := bstep (se 2 (by rfl) ⟨663063, by rfl⟩ : syracuseStep 1768169 = 1326127) B1326127
theorem B11344637 : Blo 1178406 11344637 := bstep (se 3 (by rfl) ⟨2127119, by rfl⟩ : syracuseStep 11344637 = 4254239) B4254239
theorem B1178439 : Blo 1178406 1178439 := bstep (se 1 (by rfl) ⟨883829, by rfl⟩ : syracuseStep 1178439 = 1767659) B1767659
theorem B1178479 : Blo 1178406 1178479 := bstep (se 1 (by rfl) ⟨883859, by rfl⟩ : syracuseStep 1178479 = 1767719) B1767719
theorem B1325947 : Blo 1178406 1325947 := bstep (se 1 (by rfl) ⟨994460, by rfl⟩ : syracuseStep 1325947 = 1988921) B1988921
theorem B1178535 : Blo 1178406 1178535 := bstep (se 1 (by rfl) ⟨883901, by rfl⟩ : syracuseStep 1178535 = 1767803) B1767803
theorem B1178715 : Blo 1178406 1178715 := bstep (se 1 (by rfl) ⟨884036, by rfl⟩ : syracuseStep 1178715 = 1768073) B1768073
theorem B1768553 : Blo 1178406 1768553 := bstep (se 2 (by rfl) ⟨663207, by rfl⟩ : syracuseStep 1768553 = 1326415) B1326415
theorem B2653289 : Blo 1178406 2653289 := bstep (se 2 (by rfl) ⟨994983, by rfl⟩ : syracuseStep 2653289 = 1989967) B1989967
theorem B3980393 : Blo 1178406 3980393 := bstep (se 2 (by rfl) ⟨1492647, by rfl⟩ : syracuseStep 3980393 = 2985295) B2985295
theorem B1178831 : Blo 1178406 1178831 := bstep (se 1 (by rfl) ⟨884123, by rfl⟩ : syracuseStep 1178831 = 1768247) B1768247
theorem B1989839 : Blo 1178406 1989839 := bstep (se 1 (by rfl) ⟨1492379, by rfl⟩ : syracuseStep 1989839 = 2984759) B2984759
theorem B11492567 : Blo 1178406 11492567 := bstep (se 1 (by rfl) ⟨8619425, by rfl⟩ : syracuseStep 11492567 = 17238851) B17238851
theorem B1178855 : Blo 1178406 1178855 := bstep (se 1 (by rfl) ⟨884141, by rfl⟩ : syracuseStep 1178855 = 1768283) B1768283
theorem B1768679 : Blo 1178406 1768679 := bstep (se 1 (by rfl) ⟨1326509, by rfl⟩ : syracuseStep 1768679 = 2653019) B2653019
theorem B2653415 : Blo 1178406 2653415 := bstep (se 1 (by rfl) ⟨1990061, by rfl⟩ : syracuseStep 2653415 = 3980123) B3980123
theorem B1178951 : Blo 1178406 1178951 := bstep (se 1 (by rfl) ⟨884213, by rfl⟩ : syracuseStep 1178951 = 1768427) B1768427
theorem B7552379 : Blo 1178406 7552379 := bstep (se 1 (by rfl) ⟨5664284, by rfl⟩ : syracuseStep 7552379 = 11328569) B11328569
theorem B5741999 : Blo 1178406 5741999 := bstep (se 1 (by rfl) ⟨4306499, by rfl⟩ : syracuseStep 5741999 = 8612999) B8612999
theorem B1179087 : Blo 1178406 1179087 := bstep (se 1 (by rfl) ⟨884315, by rfl⟩ : syracuseStep 1179087 = 1768631) B1768631
theorem B57384557 : Blo 1178406 57384557 := bstep (se 3 (by rfl) ⟨10759604, by rfl⟩ : syracuseStep 57384557 = 21519209) B21519209
theorem B1179247 : Blo 1178406 1179247 := bstep (se 1 (by rfl) ⟨884435, by rfl⟩ : syracuseStep 1179247 = 1768871) B1768871
theorem B1326703 : Blo 1178406 1326703 := bstep (se 1 (by rfl) ⟨995027, by rfl⟩ : syracuseStep 1326703 = 1990055) B1990055
theorem B1179303 : Blo 1178406 1179303 := bstep (se 1 (by rfl) ⟨884477, by rfl⟩ : syracuseStep 1179303 = 1768955) B1768955
theorem B1326811 : Blo 1178406 1326811 := bstep (se 1 (by rfl) ⟨995108, by rfl⟩ : syracuseStep 1326811 = 1990217) B1990217
theorem B1793755 : Blo 1178406 1793755 := bstep (se 1 (by rfl) ⟨1345316, by rfl⟩ : syracuseStep 1793755 = 2690633) B2690633
theorem B1769183 : Blo 1178406 1769183 := bstep (se 1 (by rfl) ⟨1326887, by rfl⟩ : syracuseStep 1769183 = 2653775) B2653775
theorem B2653919 : Blo 1178406 2653919 := bstep (se 1 (by rfl) ⟨1990439, by rfl⟩ : syracuseStep 2653919 = 3980879) B3980879
theorem B1179367 : Blo 1178406 1179367 := bstep (se 1 (by rfl) ⟨884525, by rfl⟩ : syracuseStep 1179367 = 1769051) B1769051
theorem B8953577 : Blo 1178406 8953577 := bstep (se 2 (by rfl) ⟨3357591, by rfl⟩ : syracuseStep 8953577 = 6715183) B6715183
theorem B1769225 : Blo 1178406 1769225 := bstep (se 2 (by rfl) ⟨663459, by rfl⟩ : syracuseStep 1769225 = 1326919) B1326919
theorem B1179423 : Blo 1178406 1179423 := bstep (se 1 (by rfl) ⟨884567, by rfl⟩ : syracuseStep 1179423 = 1769135) B1769135
theorem B2653991 : Blo 1178406 2653991 := bstep (se 1 (by rfl) ⟨1990493, by rfl⟩ : syracuseStep 2653991 = 3980987) B3980987
theorem B1179503 : Blo 1178406 1179503 := bstep (se 1 (by rfl) ⟨884627, by rfl⟩ : syracuseStep 1179503 = 1769255) B1769255
theorem B1179559 : Blo 1178406 1179559 := bstep (se 1 (by rfl) ⟨884669, by rfl⟩ : syracuseStep 1179559 = 1769339) B1769339
theorem B1179775 : Blo 1178406 1179775 := bstep (se 1 (by rfl) ⟨884831, by rfl⟩ : syracuseStep 1179775 = 1769663) B1769663
theorem B3981527 : Blo 1178406 3981527 := bstep (se 1 (by rfl) ⟨2986145, by rfl⟩ : syracuseStep 3981527 = 5972291) B5972291
theorem B1180059 : Blo 1178406 1180059 := bstep (se 1 (by rfl) ⟨885044, by rfl⟩ : syracuseStep 1180059 = 1770089) B1770089
theorem B1180063 : Blo 1178406 1180063 := bstep (se 1 (by rfl) ⟨885047, by rfl⟩ : syracuseStep 1180063 = 1770095) B1770095
theorem B7553533 : Blo 1178406 7553533 := bstep (se 3 (by rfl) ⟨1416287, by rfl⟩ : syracuseStep 7553533 = 2832575) B2832575
theorem B2654747 : Blo 1178406 2654747 := bstep (se 1 (by rfl) ⟨1991060, by rfl⟩ : syracuseStep 2654747 = 3982121) B3982121
theorem B1770011 : Blo 1178406 1770011 := bstep (se 1 (by rfl) ⟨1327508, by rfl⟩ : syracuseStep 1770011 = 2655017) B2655017
theorem B2654927 : Blo 1178406 2654927 := bstep (se 1 (by rfl) ⟨1991195, by rfl⟩ : syracuseStep 2654927 = 3982391) B3982391
theorem B1770191 : Blo 1178406 1770191 := bstep (se 1 (by rfl) ⟨1327643, by rfl⟩ : syracuseStep 1770191 = 2655287) B2655287
theorem B6808283 : Blo 1178406 6808283 := bstep (se 1 (by rfl) ⟨5106212, by rfl⟩ : syracuseStep 6808283 = 10212425) B10212425
theorem B6464225 : Blo 1178406 6464225 := bstep (se 2 (by rfl) ⟨2424084, by rfl⟩ : syracuseStep 6464225 = 4848169) B4848169
theorem B3982067 : Blo 1178406 3982067 := bstep (se 1 (by rfl) ⟨2986550, by rfl⟩ : syracuseStep 3982067 = 5973101) B5973101
theorem B8962811 : Blo 1178406 8962811 := bstep (se 1 (by rfl) ⟨6722108, by rfl⟩ : syracuseStep 8962811 = 13444217) B13444217
theorem B6808375 : Blo 1178406 6808375 := bstep (se 1 (by rfl) ⟨5106281, by rfl⟩ : syracuseStep 6808375 = 10212563) B10212563
theorem B1770311 : Blo 1178406 1770311 := bstep (se 1 (by rfl) ⟨1327733, by rfl⟩ : syracuseStep 1770311 = 2655467) B2655467
theorem B36316001 : Blo 1178406 36316001 := bstep (se 2 (by rfl) ⟨13618500, by rfl⟩ : syracuseStep 36316001 = 27237001) B27237001
theorem B1770377 : Blo 1178406 1770377 := bstep (se 2 (by rfl) ⟨663891, by rfl⟩ : syracuseStep 1770377 = 1327783) B1327783
theorem B6054907 : Blo 1178406 6054907 := bstep (se 1 (by rfl) ⟨4541180, by rfl⟩ : syracuseStep 6054907 = 9082361) B9082361
theorem B1492015 : Blo 1178406 1492015 := bstep (se 1 (by rfl) ⟨1119011, by rfl⟩ : syracuseStep 1492015 = 2238023) B2238023
theorem B3777599 : Blo 1178406 3777599 := bstep (se 1 (by rfl) ⟨2833199, by rfl⟩ : syracuseStep 3777599 = 5666399) B5666399
theorem B2655305 : Blo 1178406 2655305 := bstep (se 2 (by rfl) ⟨995739, by rfl⟩ : syracuseStep 2655305 = 1991479) B1991479
theorem B1991783 : Blo 1178406 1991783 := bstep (se 1 (by rfl) ⟨1493837, by rfl⟩ : syracuseStep 1991783 = 2987675) B2987675
theorem B3360167 : Blo 1178406 3360167 := bstep (se 1 (by rfl) ⟨2520125, by rfl⟩ : syracuseStep 3360167 = 5040251) B5040251
theorem B2983351 : Blo 1178406 2983351 := bstep (se 1 (by rfl) ⟨2237513, by rfl⟩ : syracuseStep 2983351 = 4475027) B4475027
theorem B13985329 : Blo 1178406 13985329 := bstep (se 2 (by rfl) ⟨5244498, by rfl⟩ : syracuseStep 13985329 = 10488997) B10488997
theorem B9569963 : Blo 1178406 9569963 := bstep (se 1 (by rfl) ⟨7177472, by rfl⟩ : syracuseStep 9569963 = 14354945) B14354945
theorem B2983675 : Blo 1178406 2983675 := bstep (se 1 (by rfl) ⟨2237756, by rfl⟩ : syracuseStep 2983675 = 4475513) B4475513
theorem B7563091 : Blo 1178406 7563091 := bstep (se 1 (by rfl) ⟨5672318, by rfl⟩ : syracuseStep 7563091 = 11344637) B11344637
theorem B6719375 : Blo 1178406 6719375 := bstep (se 1 (by rfl) ⟨5039531, by rfl⟩ : syracuseStep 6719375 = 10079063) B10079063
theorem B7661711 : Blo 1178406 7661711 := bstep (se 1 (by rfl) ⟨5746283, by rfl⟩ : syracuseStep 7661711 = 11492567) B11492567
theorem B3827999 : Blo 1178406 3827999 := bstep (se 1 (by rfl) ⟨2870999, by rfl⟩ : syracuseStep 3827999 = 5741999) B5741999
theorem B20416807 : Blo 1178406 20416807 := bstep (se 1 (by rfl) ⟨15312605, by rfl⟩ : syracuseStep 20416807 = 30625211) B30625211
theorem B1493311 : Blo 1178406 1493311 := bstep (se 1 (by rfl) ⟨1119983, by rfl⟩ : syracuseStep 1493311 = 2239967) B2239967
theorem B4475209 : Blo 1178406 4475209 := bstep (se 2 (by rfl) ⟨1678203, by rfl⟩ : syracuseStep 4475209 = 3356407) B3356407
theorem B245164529 : Blo 1178406 245164529 := bstep (se 2 (by rfl) ⟨91936698, by rfl⟩ : syracuseStep 245164529 = 183873397) B183873397
theorem B2984809 : Blo 1178406 2984809 := bstep (se 2 (by rfl) ⟨1119303, by rfl⟩ : syracuseStep 2984809 = 2238607) B2238607
theorem B13429637 : Blo 1178406 13429637 := bstep (se 4 (by rfl) ⟨1259028, by rfl⟩ : syracuseStep 13429637 = 2518057) B2518057
theorem B12094829 : Blo 1178406 12094829 := bstep (se 3 (by rfl) ⟨2267780, by rfl⟩ : syracuseStep 12094829 = 4535561) B4535561
theorem B8503289 : Blo 1178406 8503289 := bstep (se 2 (by rfl) ⟨3188733, by rfl⟩ : syracuseStep 8503289 = 6377467) B6377467
theorem B2690587 : Blo 1178406 2690587 := bstep (se 1 (by rfl) ⟨2017940, by rfl⟩ : syracuseStep 2690587 = 4035881) B4035881
theorem B5033927 : Blo 1178406 5033927 := bstep (se 1 (by rfl) ⟨3775445, by rfl⟩ : syracuseStep 5033927 = 7550891) B7550891
theorem B7655579 : Blo 1178406 7655579 := bstep (se 1 (by rfl) ⟨5741684, by rfl⟩ : syracuseStep 7655579 = 11483369) B11483369
theorem B6713543 : Blo 1178406 6713543 := bstep (se 1 (by rfl) ⟨5035157, by rfl⟩ : syracuseStep 6713543 = 10070315) B10070315
theorem B13431095 : Blo 1178406 13431095 := bstep (se 1 (by rfl) ⟨10073321, by rfl⟩ : syracuseStep 13431095 = 20146643) B20146643
theorem B5034919 : Blo 1178406 5034919 := bstep (se 1 (by rfl) ⟨3776189, by rfl⟩ : syracuseStep 5034919 = 7552379) B7552379
theorem B5969051 : Blo 1178406 5969051 := bstep (se 1 (by rfl) ⟨4476788, by rfl⟩ : syracuseStep 5969051 = 8953577) B8953577
theorem B15111623 : Blo 1178406 15111623 := bstep (se 1 (by rfl) ⟨11333717, by rfl⟩ : syracuseStep 15111623 = 22667435) B22667435
theorem B6715001 : Blo 1178406 6715001 := bstep (se 2 (by rfl) ⟨2518125, by rfl⟩ : syracuseStep 6715001 = 5036251) B5036251
theorem B2987867 : Blo 1178406 2987867 := bstep (se 1 (by rfl) ⟨2240900, by rfl⟩ : syracuseStep 2987867 = 4481801) B4481801
theorem B3979475 : Blo 1178406 3979475 := bstep (se 1 (by rfl) ⟨2984606, by rfl⟩ : syracuseStep 3979475 = 5969213) B5969213
theorem B11344175 : Blo 1178406 11344175 := bstep (se 1 (by rfl) ⟨8508131, by rfl⟩ : syracuseStep 11344175 = 17016263) B17016263
theorem B4479371 : Blo 1178406 4479371 := bstep (se 1 (by rfl) ⟨3359528, by rfl⟩ : syracuseStep 4479371 = 6719057) B6719057
theorem B1767839 : Blo 1178406 1767839 := bstep (se 1 (by rfl) ⟨1325879, by rfl⟩ : syracuseStep 1767839 = 2651759) B2651759
theorem B16144829 : Blo 1178406 16144829 := bstep (se 3 (by rfl) ⟨3027155, by rfl⟩ : syracuseStep 16144829 = 6054311) B6054311
theorem B1767929 : Blo 1178406 1767929 := bstep (se 2 (by rfl) ⟨662973, by rfl⟩ : syracuseStep 1767929 = 1325947) B1325947
theorem B15309485 : Blo 1178406 15309485 := bstep (se 3 (by rfl) ⟨2870528, by rfl⟩ : syracuseStep 15309485 = 5741057) B5741057
theorem B3775241 : Blo 1178406 3775241 := bstep (se 2 (by rfl) ⟨1415715, by rfl⟩ : syracuseStep 3775241 = 2831431) B2831431
theorem B6372107 : Blo 1178406 6372107 := bstep (se 1 (by rfl) ⟨4779080, by rfl⟩ : syracuseStep 6372107 = 9558161) B9558161
theorem B1178591 : Blo 1178406 1178591 := bstep (se 1 (by rfl) ⟨883943, by rfl⟩ : syracuseStep 1178591 = 1767887) B1767887
theorem B1768415 : Blo 1178406 1768415 := bstep (se 1 (by rfl) ⟨1326311, by rfl⟩ : syracuseStep 1768415 = 2652623) B2652623
theorem B1178651 : Blo 1178406 1178651 := bstep (se 1 (by rfl) ⟨883988, by rfl⟩ : syracuseStep 1178651 = 1767977) B1767977
theorem B1768475 : Blo 1178406 1768475 := bstep (se 1 (by rfl) ⟨1326356, by rfl⟩ : syracuseStep 1768475 = 2652713) B2652713
theorem B10755119 : Blo 1178406 10755119 := bstep (se 1 (by rfl) ⟨8066339, by rfl⟩ : syracuseStep 10755119 = 16132679) B16132679
theorem B15113263 : Blo 1178406 15113263 := bstep (se 1 (by rfl) ⟨11334947, by rfl⟩ : syracuseStep 15113263 = 22669895) B22669895
theorem B12106867 : Blo 1178406 12106867 := bstep (se 1 (by rfl) ⟨9080150, by rfl⟩ : syracuseStep 12106867 = 18160301) B18160301
theorem B1178779 : Blo 1178406 1178779 := bstep (se 1 (by rfl) ⟨884084, by rfl⟩ : syracuseStep 1178779 = 1768169) B1768169
theorem B5381353 : Blo 1178406 5381353 := bstep (se 2 (by rfl) ⟨2018007, by rfl⟩ : syracuseStep 5381353 = 4036015) B4036015
theorem B141712757 : Blo 1178406 141712757 := bstep (se 5 (by rfl) ⟨6642785, by rfl⟩ : syracuseStep 141712757 = 13285571) B13285571
theorem B6380927 : Blo 1178406 6380927 := bstep (se 1 (by rfl) ⟨4785695, by rfl⟩ : syracuseStep 6380927 = 9571391) B9571391
theorem B1179035 : Blo 1178406 1179035 := bstep (se 1 (by rfl) ⟨884276, by rfl⟩ : syracuseStep 1179035 = 1768553) B1768553
theorem B1768859 : Blo 1178406 1768859 := bstep (se 1 (by rfl) ⟨1326644, by rfl⟩ : syracuseStep 1768859 = 2653289) B2653289
theorem B2653595 : Blo 1178406 2653595 := bstep (se 1 (by rfl) ⟨1990196, by rfl⟩ : syracuseStep 2653595 = 3980393) B3980393
theorem B1326559 : Blo 1178406 1326559 := bstep (se 1 (by rfl) ⟨994919, by rfl⟩ : syracuseStep 1326559 = 1989839) B1989839
theorem B1768937 : Blo 1178406 1768937 := bstep (se 2 (by rfl) ⟨663351, by rfl⟩ : syracuseStep 1768937 = 1326703) B1326703
theorem B1179119 : Blo 1178406 1179119 := bstep (se 1 (by rfl) ⟨884339, by rfl⟩ : syracuseStep 1179119 = 1768679) B1768679
theorem B1768943 : Blo 1178406 1768943 := bstep (se 1 (by rfl) ⟨1326707, by rfl⟩ : syracuseStep 1768943 = 2653415) B2653415
theorem B1769081 : Blo 1178406 1769081 := bstep (se 2 (by rfl) ⟨663405, by rfl⟩ : syracuseStep 1769081 = 1326811) B1326811
theorem B2391673 : Blo 1178406 2391673 := bstep (se 2 (by rfl) ⟨896877, by rfl⟩ : syracuseStep 2391673 = 1793755) B1793755
theorem B13442759 : Blo 1178406 13442759 := bstep (se 1 (by rfl) ⟨10082069, by rfl⟩ : syracuseStep 13442759 = 20164139) B20164139
theorem B38256371 : Blo 1178406 38256371 := bstep (se 1 (by rfl) ⟨28692278, by rfl⟩ : syracuseStep 38256371 = 57384557) B57384557
theorem B3981095 : Blo 1178406 3981095 := bstep (se 1 (by rfl) ⟨2985821, by rfl⟩ : syracuseStep 3981095 = 5971643) B5971643
theorem B1179455 : Blo 1178406 1179455 := bstep (se 1 (by rfl) ⟨884591, by rfl⟩ : syracuseStep 1179455 = 1769183) B1769183
theorem B1769279 : Blo 1178406 1769279 := bstep (se 1 (by rfl) ⟨1326959, by rfl⟩ : syracuseStep 1769279 = 2653919) B2653919
theorem B1179483 : Blo 1178406 1179483 := bstep (se 1 (by rfl) ⟨884612, by rfl⟩ : syracuseStep 1179483 = 1769225) B1769225
theorem B1769327 : Blo 1178406 1769327 := bstep (se 1 (by rfl) ⟨1326995, by rfl⟩ : syracuseStep 1769327 = 2653991) B2653991
theorem B15122285 : Blo 1178406 15122285 := bstep (se 3 (by rfl) ⟨2835428, by rfl⟩ : syracuseStep 15122285 = 5670857) B5670857
theorem B3776395 : Blo 1178406 3776395 := bstep (se 1 (by rfl) ⟨2832296, by rfl⟩ : syracuseStep 3776395 = 5664593) B5664593
theorem B4251631 : Blo 1178406 4251631 := bstep (se 1 (by rfl) ⟨3188723, by rfl⟩ : syracuseStep 4251631 = 6377447) B6377447
theorem B5103719 : Blo 1178406 5103719 := bstep (se 1 (by rfl) ⟨3827789, by rfl⟩ : syracuseStep 5103719 = 7655579) B7655579
theorem B28680317 : Blo 1178406 28680317 := bstep (se 3 (by rfl) ⟨5377559, by rfl⟩ : syracuseStep 28680317 = 10755119) B10755119
theorem B2654351 : Blo 1178406 2654351 := bstep (se 1 (by rfl) ⟨1990763, by rfl⟩ : syracuseStep 2654351 = 3981527) B3981527
theorem B8954063 : Blo 1178406 8954063 := bstep (se 1 (by rfl) ⟨6715547, by rfl⟩ : syracuseStep 8954063 = 13431095) B13431095
theorem B1769831 : Blo 1178406 1769831 := bstep (se 1 (by rfl) ⟨1327373, by rfl⟩ : syracuseStep 1769831 = 2654747) B2654747
theorem B1180007 : Blo 1178406 1180007 := bstep (se 1 (by rfl) ⟨885005, by rfl⟩ : syracuseStep 1180007 = 1770011) B1770011
theorem B27222409 : Blo 1178406 27222409 := bstep (se 2 (by rfl) ⟨10208403, by rfl⟩ : syracuseStep 27222409 = 20416807) B20416807
theorem B1991081 : Blo 1178406 1991081 := bstep (se 2 (by rfl) ⟨746655, by rfl⟩ : syracuseStep 1991081 = 1493311) B1493311
theorem B1769951 : Blo 1178406 1769951 := bstep (se 1 (by rfl) ⟨1327463, by rfl⟩ : syracuseStep 1769951 = 2654927) B2654927
theorem B1180127 : Blo 1178406 1180127 := bstep (se 1 (by rfl) ⟨885095, by rfl⟩ : syracuseStep 1180127 = 1770191) B1770191
theorem B4538855 : Blo 1178406 4538855 := bstep (se 1 (by rfl) ⟨3404141, by rfl⟩ : syracuseStep 4538855 = 6808283) B6808283
theorem B2654711 : Blo 1178406 2654711 := bstep (se 1 (by rfl) ⟨1991033, by rfl⟩ : syracuseStep 2654711 = 3982067) B3982067
theorem B1180207 : Blo 1178406 1180207 := bstep (se 1 (by rfl) ⟨885155, by rfl⟩ : syracuseStep 1180207 = 1770311) B1770311
theorem B1180251 : Blo 1178406 1180251 := bstep (se 1 (by rfl) ⟨885188, by rfl⟩ : syracuseStep 1180251 = 1770377) B1770377
theorem B1770203 : Blo 1178406 1770203 := bstep (se 1 (by rfl) ⟨1327652, by rfl⟩ : syracuseStep 1770203 = 2655305) B2655305
theorem B1327855 : Blo 1178406 1327855 := bstep (se 1 (by rfl) ⟨995891, by rfl⟩ : syracuseStep 1327855 = 1991783) B1991783
theorem B9077833 : Blo 1178406 9077833 := bstep (se 2 (by rfl) ⟨3404187, by rfl⟩ : syracuseStep 9077833 = 6808375) B6808375
theorem B1991911 : Blo 1178406 1991911 := bstep (se 1 (by rfl) ⟨1493933, by rfl⟩ : syracuseStep 1991911 = 2987867) B2987867
theorem B7562783 : Blo 1178406 7562783 := bstep (se 1 (by rfl) ⟨5672087, by rfl⟩ : syracuseStep 7562783 = 11344175) B11344175
theorem B2516827 : Blo 1178406 2516827 := bstep (se 1 (by rfl) ⟨1887620, by rfl⟩ : syracuseStep 2516827 = 3775241) B3775241
theorem B17237933 : Blo 1178406 17237933 := bstep (se 3 (by rfl) ⟨3232112, by rfl⟩ : syracuseStep 17237933 = 6464225) B6464225
theorem B18647105 : Blo 1178406 18647105 := bstep (se 2 (by rfl) ⟨6992664, by rfl⟩ : syracuseStep 18647105 = 13985329) B13985329
theorem B3188897 : Blo 1178406 3188897 := bstep (se 2 (by rfl) ⟨1195836, by rfl⟩ : syracuseStep 3188897 = 2391673) B2391673
theorem B8063219 : Blo 1178406 8063219 := bstep (se 1 (by rfl) ⟨6047414, by rfl⟩ : syracuseStep 8063219 = 12094829) B12094829
theorem B4253951 : Blo 1178406 4253951 := bstep (se 1 (by rfl) ⟨3190463, by rfl⟩ : syracuseStep 4253951 = 6380927) B6380927
theorem B25504247 : Blo 1178406 25504247 := bstep (se 1 (by rfl) ⟨19128185, by rfl⟩ : syracuseStep 25504247 = 38256371) B38256371
theorem B4475695 : Blo 1178406 4475695 := bstep (se 1 (by rfl) ⟨3356771, by rfl⟩ : syracuseStep 4475695 = 6713543) B6713543
theorem B5966945 : Blo 1178406 5966945 := bstep (se 2 (by rfl) ⟨2237604, by rfl⟩ : syracuseStep 5966945 = 4475209) B4475209
theorem B5975207 : Blo 1178406 5975207 := bstep (se 1 (by rfl) ⟨4481405, by rfl⟩ : syracuseStep 5975207 = 8962811) B8962811
theorem B24210667 : Blo 1178406 24210667 := bstep (se 1 (by rfl) ⟨18158000, by rfl⟩ : syracuseStep 24210667 = 36316001) B36316001
theorem B10071377 : Blo 1178406 10071377 := bstep (se 2 (by rfl) ⟨3776766, by rfl⟩ : syracuseStep 10071377 = 7553533) B7553533
theorem B2518399 : Blo 1178406 2518399 := bstep (se 1 (by rfl) ⟨1888799, by rfl⟩ : syracuseStep 2518399 = 3777599) B3777599
theorem B2240111 : Blo 1178406 2240111 := bstep (se 1 (by rfl) ⟨1680083, by rfl⟩ : syracuseStep 2240111 = 3360167) B3360167
theorem B4476667 : Blo 1178406 4476667 := bstep (se 1 (by rfl) ⟨3357500, by rfl⟩ : syracuseStep 4476667 = 6715001) B6715001
theorem B6713225 : Blo 1178406 6713225 := bstep (se 2 (by rfl) ⟨2517459, by rfl⟩ : syracuseStep 6713225 = 5034919) B5034919
theorem B8073209 : Blo 1178406 8073209 := bstep (se 2 (by rfl) ⟨3027453, by rfl⟩ : syracuseStep 8073209 = 6054907) B6054907
theorem B5107807 : Blo 1178406 5107807 := bstep (se 1 (by rfl) ⟨3830855, by rfl⟩ : syracuseStep 5107807 = 7661711) B7661711
theorem B16142489 : Blo 1178406 16142489 := bstep (se 2 (by rfl) ⟨6053433, by rfl⟩ : syracuseStep 16142489 = 12106867) B12106867
theorem B2551999 : Blo 1178406 2551999 := bstep (se 1 (by rfl) ⟨1913999, by rfl⟩ : syracuseStep 2551999 = 3827999) B3827999
theorem B2986247 : Blo 1178406 2986247 := bstep (se 1 (by rfl) ⟨2239685, by rfl⟩ : syracuseStep 2986247 = 4479371) B4479371
theorem B163443019 : Blo 1178406 163443019 := bstep (se 1 (by rfl) ⟨122582264, by rfl⟩ : syracuseStep 163443019 = 245164529) B245164529
theorem B4248071 : Blo 1178406 4248071 := bstep (se 1 (by rfl) ⟨3186053, by rfl⟩ : syracuseStep 4248071 = 6372107) B6372107
theorem B3977801 : Blo 1178406 3977801 := bstep (se 2 (by rfl) ⟨1491675, by rfl⟩ : syracuseStep 3977801 = 2983351) B2983351
theorem B94475171 : Blo 1178406 94475171 := bstep (se 1 (by rfl) ⟨70856378, by rfl⟩ : syracuseStep 94475171 = 141712757) B141712757
theorem B5668859 : Blo 1178406 5668859 := bstep (se 1 (by rfl) ⟨4251644, by rfl⟩ : syracuseStep 5668859 = 8503289) B8503289
theorem B3978233 : Blo 1178406 3978233 := bstep (se 2 (by rfl) ⟨1491837, by rfl⟩ : syracuseStep 3978233 = 2983675) B2983675
theorem B5035193 : Blo 1178406 5035193 := bstep (se 2 (by rfl) ⟨1888197, by rfl⟩ : syracuseStep 5035193 = 3776395) B3776395
theorem B13423805 : Blo 1178406 13423805 := bstep (se 3 (by rfl) ⟨2516963, by rfl⟩ : syracuseStep 13423805 = 5033927) B5033927
theorem B10081523 : Blo 1178406 10081523 := bstep (se 1 (by rfl) ⟨7561142, by rfl⟩ : syracuseStep 10081523 = 15122285) B15122285
theorem B14349797 : Blo 1178406 14349797 := bstep (se 4 (by rfl) ⟨1345293, by rfl⟩ : syracuseStep 14349797 = 2690587) B2690587
theorem B3979367 : Blo 1178406 3979367 := bstep (se 1 (by rfl) ⟨2984525, by rfl⟩ : syracuseStep 3979367 = 5969051) B5969051
theorem B10074415 : Blo 1178406 10074415 := bstep (se 1 (by rfl) ⟨7555811, by rfl⟩ : syracuseStep 10074415 = 15111623) B15111623
theorem B6379975 : Blo 1178406 6379975 := bstep (se 1 (by rfl) ⟨4784981, by rfl⟩ : syracuseStep 6379975 = 9569963) B9569963
theorem B3979745 : Blo 1178406 3979745 := bstep (se 2 (by rfl) ⟨1492404, by rfl⟩ : syracuseStep 3979745 = 2984809) B2984809
theorem B4479583 : Blo 1178406 4479583 := bstep (se 1 (by rfl) ⟨3359687, by rfl⟩ : syracuseStep 4479583 = 6719375) B6719375
theorem B1989353 : Blo 1178406 1989353 := bstep (se 2 (by rfl) ⟨746007, by rfl⟩ : syracuseStep 1989353 = 1492015) B1492015
theorem B20151017 : Blo 1178406 20151017 := bstep (se 2 (by rfl) ⟨7556631, by rfl⟩ : syracuseStep 20151017 = 15113263) B15113263
theorem B2652983 : Blo 1178406 2652983 := bstep (se 1 (by rfl) ⟨1989737, by rfl⟩ : syracuseStep 2652983 = 3979475) B3979475
theorem B1178559 : Blo 1178406 1178559 := bstep (se 1 (by rfl) ⟨883919, by rfl⟩ : syracuseStep 1178559 = 1767839) B1767839
theorem B10763219 : Blo 1178406 10763219 := bstep (se 1 (by rfl) ⟨8072414, by rfl⟩ : syracuseStep 10763219 = 16144829) B16144829
theorem B7175137 : Blo 1178406 7175137 := bstep (se 2 (by rfl) ⟨2690676, by rfl⟩ : syracuseStep 7175137 = 5381353) B5381353
theorem B1178619 : Blo 1178406 1178619 := bstep (se 1 (by rfl) ⟨883964, by rfl⟩ : syracuseStep 1178619 = 1767929) B1767929
theorem B10206323 : Blo 1178406 10206323 := bstep (se 1 (by rfl) ⟨7654742, by rfl⟩ : syracuseStep 10206323 = 15309485) B15309485
theorem B8953091 : Blo 1178406 8953091 := bstep (se 1 (by rfl) ⟨6714818, by rfl⟩ : syracuseStep 8953091 = 13429637) B13429637
theorem B1768745 : Blo 1178406 1768745 := bstep (se 2 (by rfl) ⟨663279, by rfl⟩ : syracuseStep 1768745 = 1326559) B1326559
theorem B1178943 : Blo 1178406 1178943 := bstep (se 1 (by rfl) ⟨884207, by rfl⟩ : syracuseStep 1178943 = 1768415) B1768415
theorem B1178983 : Blo 1178406 1178983 := bstep (se 1 (by rfl) ⟨884237, by rfl⟩ : syracuseStep 1178983 = 1768475) B1768475
theorem B1179239 : Blo 1178406 1179239 := bstep (se 1 (by rfl) ⟨884429, by rfl⟩ : syracuseStep 1179239 = 1768859) B1768859
theorem B1769063 : Blo 1178406 1769063 := bstep (se 1 (by rfl) ⟨1326797, by rfl⟩ : syracuseStep 1769063 = 2653595) B2653595
theorem B1179291 : Blo 1178406 1179291 := bstep (se 1 (by rfl) ⟨884468, by rfl⟩ : syracuseStep 1179291 = 1768937) B1768937
theorem B1179295 : Blo 1178406 1179295 := bstep (se 1 (by rfl) ⟨884471, by rfl⟩ : syracuseStep 1179295 = 1768943) B1768943
theorem B1179387 : Blo 1178406 1179387 := bstep (se 1 (by rfl) ⟨884540, by rfl⟩ : syracuseStep 1179387 = 1769081) B1769081
theorem B10084121 : Blo 1178406 10084121 := bstep (se 2 (by rfl) ⟨3781545, by rfl⟩ : syracuseStep 10084121 = 7563091) B7563091
theorem B8961839 : Blo 1178406 8961839 := bstep (se 1 (by rfl) ⟨6721379, by rfl⟩ : syracuseStep 8961839 = 13442759) B13442759
theorem B2654063 : Blo 1178406 2654063 := bstep (se 1 (by rfl) ⟨1990547, by rfl⟩ : syracuseStep 2654063 = 3981095) B3981095
theorem B1179519 : Blo 1178406 1179519 := bstep (se 1 (by rfl) ⟨884639, by rfl⟩ : syracuseStep 1179519 = 1769279) B1769279
theorem B1179551 : Blo 1178406 1179551 := bstep (se 1 (by rfl) ⟨884663, by rfl⟩ : syracuseStep 1179551 = 1769327) B1769327
theorem B5668841 : Blo 1178406 5668841 := bstep (se 2 (by rfl) ⟨2125815, by rfl⟩ : syracuseStep 5668841 = 4251631) B4251631
theorem B19120211 : Blo 1178406 19120211 := bstep (se 1 (by rfl) ⟨14340158, by rfl⟩ : syracuseStep 19120211 = 28680317) B28680317
theorem B1769567 : Blo 1178406 1769567 := bstep (se 1 (by rfl) ⟨1327175, by rfl⟩ : syracuseStep 1769567 = 2654351) B2654351
theorem B49725613 : Blo 1178406 49725613 := bstep (se 3 (by rfl) ⟨9323552, by rfl⟩ : syracuseStep 49725613 = 18647105) B18647105
theorem B1990831 : Blo 1178406 1990831 := bstep (se 1 (by rfl) ⟨1493123, by rfl⟩ : syracuseStep 1990831 = 2986247) B2986247
theorem B1179887 : Blo 1178406 1179887 := bstep (se 1 (by rfl) ⟨884915, by rfl⟩ : syracuseStep 1179887 = 1769831) B1769831
theorem B1327387 : Blo 1178406 1327387 := bstep (se 1 (by rfl) ⟨995540, by rfl⟩ : syracuseStep 1327387 = 1991081) B1991081
theorem B1179967 : Blo 1178406 1179967 := bstep (se 1 (by rfl) ⟨884975, by rfl⟩ : syracuseStep 1179967 = 1769951) B1769951
theorem B1769807 : Blo 1178406 1769807 := bstep (se 1 (by rfl) ⟨1327355, by rfl⟩ : syracuseStep 1769807 = 2654711) B2654711
theorem B217924025 : Blo 1178406 217924025 := bstep (se 2 (by rfl) ⟨81721509, by rfl⟩ : syracuseStep 217924025 = 163443019) B163443019
theorem B1180135 : Blo 1178406 1180135 := bstep (se 1 (by rfl) ⟨885101, by rfl⟩ : syracuseStep 1180135 = 1770203) B1770203
theorem B5972777 : Blo 1178406 5972777 := bstep (se 2 (by rfl) ⟨2239791, by rfl⟩ : syracuseStep 5972777 = 4479583) B4479583
theorem B1770473 : Blo 1178406 1770473 := bstep (se 2 (by rfl) ⟨663927, by rfl⟩ : syracuseStep 1770473 = 1327855) B1327855
theorem B129123557 : Blo 1178406 129123557 := bstep (se 4 (by rfl) ⟨12105333, by rfl⟩ : syracuseStep 129123557 = 24210667) B24210667
theorem B5375479 : Blo 1178406 5375479 := bstep (se 1 (by rfl) ⟨4031609, by rfl⟩ : syracuseStep 5375479 = 8063219) B8063219
theorem B2835967 : Blo 1178406 2835967 := bstep (se 1 (by rfl) ⟨2126975, by rfl⟩ : syracuseStep 2835967 = 4253951) B4253951
theorem B2655881 : Blo 1178406 2655881 := bstep (se 2 (by rfl) ⟨995955, by rfl⟩ : syracuseStep 2655881 = 1991911) B1991911
theorem B3983471 : Blo 1178406 3983471 := bstep (se 1 (by rfl) ⟨2987603, by rfl⟩ : syracuseStep 3983471 = 5975207) B5975207
theorem B1493407 : Blo 1178406 1493407 := bstep (se 1 (by rfl) ⟨1120055, by rfl⟩ : syracuseStep 1493407 = 2240111) B2240111
theorem B5974559 : Blo 1178406 5974559 := bstep (se 1 (by rfl) ⟨4480919, by rfl⟩ : syracuseStep 5974559 = 8961839) B8961839
theorem B4475483 : Blo 1178406 4475483 := bstep (se 1 (by rfl) ⟨3356612, by rfl⟩ : syracuseStep 4475483 = 6713225) B6713225
theorem B3779227 : Blo 1178406 3779227 := bstep (se 1 (by rfl) ⟨2834420, by rfl⟩ : syracuseStep 3779227 = 5668841) B5668841
theorem B3779239 : Blo 1178406 3779239 := bstep (se 1 (by rfl) ⟨2834429, by rfl⟩ : syracuseStep 3779239 = 5668859) B5668859
theorem B3402479 : Blo 1178406 3402479 := bstep (se 1 (by rfl) ⟨2551859, by rfl⟩ : syracuseStep 3402479 = 5103719) B5103719
theorem B6810409 : Blo 1178406 6810409 := bstep (se 2 (by rfl) ⟨2553903, by rfl⟩ : syracuseStep 6810409 = 5107807) B5107807
theorem B3402665 : Blo 1178406 3402665 := bstep (se 2 (by rfl) ⟨1275999, by rfl⟩ : syracuseStep 3402665 = 2551999) B2551999
theorem B3025903 : Blo 1178406 3025903 := bstep (se 1 (by rfl) ⟨2269427, by rfl⟩ : syracuseStep 3025903 = 4538855) B4538855
theorem B8506633 : Blo 1178406 8506633 := bstep (se 2 (by rfl) ⟨3189987, by rfl⟩ : syracuseStep 8506633 = 6379975) B6379975
theorem B8949203 : Blo 1178406 8949203 := bstep (se 1 (by rfl) ⟨6711902, by rfl⟩ : syracuseStep 8949203 = 13423805) B13423805
theorem B6721015 : Blo 1178406 6721015 := bstep (se 1 (by rfl) ⟨5040761, by rfl⟩ : syracuseStep 6721015 = 10081523) B10081523
theorem B5041855 : Blo 1178406 5041855 := bstep (se 1 (by rfl) ⟨3781391, by rfl⟩ : syracuseStep 5041855 = 7562783) B7562783
theorem B5967593 : Blo 1178406 5967593 := bstep (se 2 (by rfl) ⟨2237847, by rfl⟩ : syracuseStep 5967593 = 4475695) B4475695
theorem B12103777 : Blo 1178406 12103777 := bstep (se 2 (by rfl) ⟨4538916, by rfl⟩ : syracuseStep 12103777 = 9077833) B9077833
theorem B2125931 : Blo 1178406 2125931 := bstep (se 1 (by rfl) ⟨1594448, by rfl⟩ : syracuseStep 2125931 = 3188897) B3188897
theorem B5382139 : Blo 1178406 5382139 := bstep (se 1 (by rfl) ⟨4036604, by rfl⟩ : syracuseStep 5382139 = 8073209) B8073209
theorem B17002831 : Blo 1178406 17002831 := bstep (se 1 (by rfl) ⟨12752123, by rfl⟩ : syracuseStep 17002831 = 25504247) B25504247
theorem B3977963 : Blo 1178406 3977963 := bstep (se 1 (by rfl) ⟨2983472, by rfl⟩ : syracuseStep 3977963 = 5966945) B5966945
theorem B6804215 : Blo 1178406 6804215 := bstep (se 1 (by rfl) ⟨5103161, by rfl⟩ : syracuseStep 6804215 = 10206323) B10206323
theorem B5968727 : Blo 1178406 5968727 := bstep (se 1 (by rfl) ⟨4476545, by rfl⟩ : syracuseStep 5968727 = 8953091) B8953091
theorem B6714251 : Blo 1178406 6714251 := bstep (se 1 (by rfl) ⟨5035688, by rfl⟩ : syracuseStep 6714251 = 10071377) B10071377
theorem B5968889 : Blo 1178406 5968889 := bstep (se 2 (by rfl) ⟨2238333, by rfl⟩ : syracuseStep 5968889 = 4476667) B4476667
theorem B251933789 : Blo 1178406 251933789 := bstep (se 3 (by rfl) ⟨47237585, by rfl⟩ : syracuseStep 251933789 = 94475171) B94475171
theorem B3355769 : Blo 1178406 3355769 := bstep (se 2 (by rfl) ⟨1258413, by rfl⟩ : syracuseStep 3355769 = 2516827) B2516827
theorem B6722747 : Blo 1178406 6722747 := bstep (se 1 (by rfl) ⟨5042060, by rfl⟩ : syracuseStep 6722747 = 10084121) B10084121
theorem B10761659 : Blo 1178406 10761659 := bstep (se 1 (by rfl) ⟨8071244, by rfl⟩ : syracuseStep 10761659 = 16142489) B16142489
theorem B5969375 : Blo 1178406 5969375 := bstep (se 1 (by rfl) ⟨4477031, by rfl⟩ : syracuseStep 5969375 = 8954063) B8954063
theorem B2832047 : Blo 1178406 2832047 := bstep (se 1 (by rfl) ⟨2124035, by rfl⟩ : syracuseStep 2832047 = 4248071) B4248071
theorem B2651867 : Blo 1178406 2651867 := bstep (se 1 (by rfl) ⟨1988900, by rfl⟩ : syracuseStep 2651867 = 3977801) B3977801
theorem B13432553 : Blo 1178406 13432553 := bstep (se 2 (by rfl) ⟨5037207, by rfl⟩ : syracuseStep 13432553 = 10074415) B10074415
theorem B36296545 : Blo 1178406 36296545 := bstep (se 2 (by rfl) ⟨13611204, by rfl⟩ : syracuseStep 36296545 = 27222409) B27222409
theorem B2652155 : Blo 1178406 2652155 := bstep (se 1 (by rfl) ⟨1989116, by rfl⟩ : syracuseStep 2652155 = 3978233) B3978233
theorem B3356795 : Blo 1178406 3356795 := bstep (se 1 (by rfl) ⟨2517596, by rfl⟩ : syracuseStep 3356795 = 5035193) B5035193
theorem B9566531 : Blo 1178406 9566531 := bstep (se 1 (by rfl) ⟨7174898, by rfl⟩ : syracuseStep 9566531 = 14349797) B14349797
theorem B11491955 : Blo 1178406 11491955 := bstep (se 1 (by rfl) ⟨8618966, by rfl⟩ : syracuseStep 11491955 = 17237933) B17237933
theorem B9566849 : Blo 1178406 9566849 := bstep (se 2 (by rfl) ⟨3587568, by rfl⟩ : syracuseStep 9566849 = 7175137) B7175137
theorem B2652911 : Blo 1178406 2652911 := bstep (se 1 (by rfl) ⟨1989683, by rfl⟩ : syracuseStep 2652911 = 3979367) B3979367
theorem B2653163 : Blo 1178406 2653163 := bstep (se 1 (by rfl) ⟨1989872, by rfl⟩ : syracuseStep 2653163 = 3979745) B3979745
theorem B1326235 : Blo 1178406 1326235 := bstep (se 1 (by rfl) ⟨994676, by rfl⟩ : syracuseStep 1326235 = 1989353) B1989353
theorem B13434011 : Blo 1178406 13434011 := bstep (se 1 (by rfl) ⟨10075508, by rfl⟩ : syracuseStep 13434011 = 20151017) B20151017
theorem B3357865 : Blo 1178406 3357865 := bstep (se 2 (by rfl) ⟨1259199, by rfl⟩ : syracuseStep 3357865 = 2518399) B2518399
theorem B1768655 : Blo 1178406 1768655 := bstep (se 1 (by rfl) ⟨1326491, by rfl⟩ : syracuseStep 1768655 = 2652983) B2652983
theorem B7175479 : Blo 1178406 7175479 := bstep (se 1 (by rfl) ⟨5381609, by rfl⟩ : syracuseStep 7175479 = 10763219) B10763219
theorem B1179163 : Blo 1178406 1179163 := bstep (se 1 (by rfl) ⟨884372, by rfl⟩ : syracuseStep 1179163 = 1768745) B1768745
theorem B1179375 : Blo 1178406 1179375 := bstep (se 1 (by rfl) ⟨884531, by rfl⟩ : syracuseStep 1179375 = 1769063) B1769063
theorem B1769375 : Blo 1178406 1769375 := bstep (se 1 (by rfl) ⟨1327031, by rfl⟩ : syracuseStep 1769375 = 2654063) B2654063
theorem B12746807 : Blo 1178406 12746807 := bstep (se 1 (by rfl) ⟨9560105, by rfl⟩ : syracuseStep 12746807 = 19120211) B19120211
theorem B1179711 : Blo 1178406 1179711 := bstep (se 1 (by rfl) ⟨884783, by rfl⟩ : syracuseStep 1179711 = 1769567) B1769567
theorem B16138369 : Blo 1178406 16138369 := bstep (se 2 (by rfl) ⟨6051888, by rfl⟩ : syracuseStep 16138369 = 12103777) B12103777
theorem B1179871 : Blo 1178406 1179871 := bstep (se 1 (by rfl) ⟨884903, by rfl⟩ : syracuseStep 1179871 = 1769807) B1769807
theorem B2654441 : Blo 1178406 2654441 := bstep (se 2 (by rfl) ⟨995415, by rfl⟩ : syracuseStep 2654441 = 1990831) B1990831
theorem B5669149 : Blo 1178406 5669149 := bstep (se 3 (by rfl) ⟨1062965, by rfl⟩ : syracuseStep 5669149 = 2125931) B2125931
theorem B1769849 : Blo 1178406 1769849 := bstep (se 2 (by rfl) ⟨663693, by rfl⟩ : syracuseStep 1769849 = 1327387) B1327387
theorem B3981851 : Blo 1178406 3981851 := bstep (se 1 (by rfl) ⟨2986388, by rfl⟩ : syracuseStep 3981851 = 5972777) B5972777
theorem B1991209 : Blo 1178406 1991209 := bstep (se 2 (by rfl) ⟨746703, by rfl⟩ : syracuseStep 1991209 = 1493407) B1493407
theorem B1180315 : Blo 1178406 1180315 := bstep (se 1 (by rfl) ⟨885236, by rfl⟩ : syracuseStep 1180315 = 1770473) B1770473
theorem B4481831 : Blo 1178406 4481831 := bstep (se 1 (by rfl) ⟨3361373, by rfl⟩ : syracuseStep 4481831 = 6722747) B6722747
theorem B86082371 : Blo 1178406 86082371 := bstep (se 1 (by rfl) ⟨64561778, by rfl⟩ : syracuseStep 86082371 = 129123557) B129123557
theorem B5038969 : Blo 1178406 5038969 := bstep (se 2 (by rfl) ⟨1889613, by rfl⟩ : syracuseStep 5038969 = 3779227) B3779227
theorem B5038985 : Blo 1178406 5038985 := bstep (se 2 (by rfl) ⟨1889619, by rfl⟩ : syracuseStep 5038985 = 3779239) B3779239
theorem B1770587 : Blo 1178406 1770587 := bstep (se 1 (by rfl) ⟨1327940, by rfl⟩ : syracuseStep 1770587 = 2655881) B2655881
theorem B8955035 : Blo 1178406 8955035 := bstep (se 1 (by rfl) ⟨6716276, by rfl⟩ : syracuseStep 8955035 = 13432553) B13432553
theorem B2655647 : Blo 1178406 2655647 := bstep (se 1 (by rfl) ⟨1991735, by rfl⟩ : syracuseStep 2655647 = 3983471) B3983471
theorem B2237863 : Blo 1178406 2237863 := bstep (se 1 (by rfl) ⟨1678397, by rfl⟩ : syracuseStep 2237863 = 3356795) B3356795
theorem B25511597 : Blo 1178406 25511597 := bstep (se 3 (by rfl) ⟨4783424, by rfl⟩ : syracuseStep 25511597 = 9566849) B9566849
theorem B3983039 : Blo 1178406 3983039 := bstep (se 1 (by rfl) ⟨2987279, by rfl⟩ : syracuseStep 3983039 = 5974559) B5974559
theorem B2983655 : Blo 1178406 2983655 := bstep (se 1 (by rfl) ⟨2237741, by rfl⟩ : syracuseStep 2983655 = 4475483) B4475483
theorem B7661303 : Blo 1178406 7661303 := bstep (se 1 (by rfl) ⟨5745977, by rfl⟩ : syracuseStep 7661303 = 11491955) B11491955
theorem B8956007 : Blo 1178406 8956007 := bstep (se 1 (by rfl) ⟨6717005, by rfl⟩ : syracuseStep 8956007 = 13434011) B13434011
theorem B5966135 : Blo 1178406 5966135 := bstep (se 1 (by rfl) ⟨4474601, by rfl⟩ : syracuseStep 5966135 = 8949203) B8949203
theorem B66300817 : Blo 1178406 66300817 := bstep (se 2 (by rfl) ⟨24862806, by rfl⟩ : syracuseStep 66300817 = 49725613) B49725613
theorem B7176185 : Blo 1178406 7176185 := bstep (se 2 (by rfl) ⟨2691069, by rfl⟩ : syracuseStep 7176185 = 5382139) B5382139
theorem B8948717 : Blo 1178406 8948717 := bstep (se 3 (by rfl) ⟨1677884, by rfl⟩ : syracuseStep 8948717 = 3355769) B3355769
theorem B22670441 : Blo 1178406 22670441 := bstep (se 2 (by rfl) ⟨8501415, by rfl⟩ : syracuseStep 22670441 = 17002831) B17002831
theorem B4476167 : Blo 1178406 4476167 := bstep (se 1 (by rfl) ⟨3357125, by rfl⟩ : syracuseStep 4476167 = 6714251) B6714251
theorem B167955859 : Blo 1178406 167955859 := bstep (se 1 (by rfl) ⟨125966894, by rfl⟩ : syracuseStep 167955859 = 251933789) B251933789
theorem B9080545 : Blo 1178406 9080545 := bstep (se 2 (by rfl) ⟨3405204, by rfl⟩ : syracuseStep 9080545 = 6810409) B6810409
theorem B1888031 : Blo 1178406 1888031 := bstep (se 1 (by rfl) ⟨1416023, by rfl⟩ : syracuseStep 1888031 = 2832047) B2832047
theorem B4034537 : Blo 1178406 4034537 := bstep (se 2 (by rfl) ⟨1512951, by rfl⟩ : syracuseStep 4034537 = 3025903) B3025903
theorem B6377687 : Blo 1178406 6377687 := bstep (se 1 (by rfl) ⟨4783265, by rfl⟩ : syracuseStep 6377687 = 9566531) B9566531
theorem B4477153 : Blo 1178406 4477153 := bstep (se 2 (by rfl) ⟨1678932, by rfl⟩ : syracuseStep 4477153 = 3357865) B3357865
theorem B11342177 : Blo 1178406 11342177 := bstep (se 2 (by rfl) ⟨4253316, by rfl⟩ : syracuseStep 11342177 = 8506633) B8506633
theorem B3781289 : Blo 1178406 3781289 := bstep (se 2 (by rfl) ⟨1417983, by rfl⟩ : syracuseStep 3781289 = 2835967) B2835967
theorem B6722473 : Blo 1178406 6722473 := bstep (se 2 (by rfl) ⟨2520927, by rfl⟩ : syracuseStep 6722473 = 5041855) B5041855
theorem B48395393 : Blo 1178406 48395393 := bstep (se 2 (by rfl) ⟨18148272, by rfl⟩ : syracuseStep 48395393 = 36296545) B36296545
theorem B3978395 : Blo 1178406 3978395 := bstep (se 1 (by rfl) ⟨2983796, by rfl⟩ : syracuseStep 3978395 = 5967593) B5967593
theorem B2651975 : Blo 1178406 2651975 := bstep (se 1 (by rfl) ⟨1988981, by rfl⟩ : syracuseStep 2651975 = 3977963) B3977963
theorem B4536143 : Blo 1178406 4536143 := bstep (se 1 (by rfl) ⟨3402107, by rfl⟩ : syracuseStep 4536143 = 6804215) B6804215
theorem B3979151 : Blo 1178406 3979151 := bstep (se 1 (by rfl) ⟨2984363, by rfl⟩ : syracuseStep 3979151 = 5968727) B5968727
theorem B3979259 : Blo 1178406 3979259 := bstep (se 1 (by rfl) ⟨2984444, by rfl⟩ : syracuseStep 3979259 = 5968889) B5968889
theorem B7174439 : Blo 1178406 7174439 := bstep (se 1 (by rfl) ⟨5380829, by rfl⟩ : syracuseStep 7174439 = 10761659) B10761659
theorem B3979583 : Blo 1178406 3979583 := bstep (se 1 (by rfl) ⟨2984687, by rfl⟩ : syracuseStep 3979583 = 5969375) B5969375
theorem B1767911 : Blo 1178406 1767911 := bstep (se 1 (by rfl) ⟨1325933, by rfl⟩ : syracuseStep 1767911 = 2651867) B2651867
theorem B581130733 : Blo 1178406 581130733 := bstep (se 3 (by rfl) ⟨108962012, by rfl⟩ : syracuseStep 581130733 = 217924025) B217924025
theorem B1768103 : Blo 1178406 1768103 := bstep (se 1 (by rfl) ⟨1326077, by rfl⟩ : syracuseStep 1768103 = 2652155) B2652155
theorem B1768313 : Blo 1178406 1768313 := bstep (se 2 (by rfl) ⟨663117, by rfl⟩ : syracuseStep 1768313 = 1326235) B1326235
theorem B9567305 : Blo 1178406 9567305 := bstep (se 2 (by rfl) ⟨3587739, by rfl⟩ : syracuseStep 9567305 = 7175479) B7175479
theorem B2268319 : Blo 1178406 2268319 := bstep (se 1 (by rfl) ⟨1701239, by rfl⟩ : syracuseStep 2268319 = 3402479) B3402479
theorem B1768607 : Blo 1178406 1768607 := bstep (se 1 (by rfl) ⟨1326455, by rfl⟩ : syracuseStep 1768607 = 2652911) B2652911
theorem B2268443 : Blo 1178406 2268443 := bstep (se 1 (by rfl) ⟨1701332, by rfl⟩ : syracuseStep 2268443 = 3402665) B3402665
theorem B1768775 : Blo 1178406 1768775 := bstep (se 1 (by rfl) ⟨1326581, by rfl⟩ : syracuseStep 1768775 = 2653163) B2653163
theorem B7167305 : Blo 1178406 7167305 := bstep (se 2 (by rfl) ⟨2687739, by rfl⟩ : syracuseStep 7167305 = 5375479) B5375479
theorem B8961353 : Blo 1178406 8961353 := bstep (se 2 (by rfl) ⟨3360507, by rfl⟩ : syracuseStep 8961353 = 6721015) B6721015
theorem B1179103 : Blo 1178406 1179103 := bstep (se 1 (by rfl) ⟨884327, by rfl⟩ : syracuseStep 1179103 = 1768655) B1768655
theorem B1179583 : Blo 1178406 1179583 := bstep (se 1 (by rfl) ⟨884687, by rfl⟩ : syracuseStep 1179583 = 1769375) B1769375
theorem B4251791 : Blo 1178406 4251791 := bstep (se 1 (by rfl) ⟨3188843, by rfl⟩ : syracuseStep 4251791 = 6377687) B6377687
theorem B1769627 : Blo 1178406 1769627 := bstep (se 1 (by rfl) ⟨1327220, by rfl⟩ : syracuseStep 1769627 = 2654441) B2654441
theorem B7561451 : Blo 1178406 7561451 := bstep (se 1 (by rfl) ⟨5671088, by rfl⟩ : syracuseStep 7561451 = 11342177) B11342177
theorem B1179899 : Blo 1178406 1179899 := bstep (se 1 (by rfl) ⟨884924, by rfl⟩ : syracuseStep 1179899 = 1769849) B1769849
theorem B2654567 : Blo 1178406 2654567 := bstep (se 1 (by rfl) ⟨1990925, by rfl⟩ : syracuseStep 2654567 = 3981851) B3981851
theorem B3359323 : Blo 1178406 3359323 := bstep (se 1 (by rfl) ⟨2519492, by rfl⟩ : syracuseStep 3359323 = 5038985) B5038985
theorem B774840977 : Blo 1178406 774840977 := bstep (se 2 (by rfl) ⟨290565366, by rfl⟩ : syracuseStep 774840977 = 581130733) B581130733
theorem B2654945 : Blo 1178406 2654945 := bstep (se 2 (by rfl) ⟨995604, by rfl⟩ : syracuseStep 2654945 = 1991209) B1991209
theorem B1180391 : Blo 1178406 1180391 := bstep (se 1 (by rfl) ⟨885293, by rfl⟩ : syracuseStep 1180391 = 1770587) B1770587
theorem B1770431 : Blo 1178406 1770431 := bstep (se 1 (by rfl) ⟨1327823, by rfl⟩ : syracuseStep 1770431 = 2655647) B2655647
theorem B17007731 : Blo 1178406 17007731 := bstep (se 1 (by rfl) ⟨12755798, by rfl⟩ : syracuseStep 17007731 = 25511597) B25511597
theorem B2655359 : Blo 1178406 2655359 := bstep (se 1 (by rfl) ⟨1991519, by rfl⟩ : syracuseStep 2655359 = 3983039) B3983039
theorem B6718625 : Blo 1178406 6718625 := bstep (se 2 (by rfl) ⟨2519484, by rfl⟩ : syracuseStep 6718625 = 5038969) B5038969
theorem B88401089 : Blo 1178406 88401089 := bstep (se 2 (by rfl) ⟨33150408, by rfl⟩ : syracuseStep 88401089 = 66300817) B66300817
theorem B8963297 : Blo 1178406 8963297 := bstep (se 2 (by rfl) ⟨3361236, by rfl⟩ : syracuseStep 8963297 = 6722473) B6722473
theorem B3024425 : Blo 1178406 3024425 := bstep (se 2 (by rfl) ⟨1134159, by rfl⟩ : syracuseStep 3024425 = 2268319) B2268319
theorem B2983817 : Blo 1178406 2983817 := bstep (se 2 (by rfl) ⟨1118931, by rfl⟩ : syracuseStep 2983817 = 2237863) B2237863
theorem B4784123 : Blo 1178406 4784123 := bstep (se 1 (by rfl) ⟨3588092, by rfl⟩ : syracuseStep 4784123 = 7176185) B7176185
theorem B5965811 : Blo 1178406 5965811 := bstep (se 1 (by rfl) ⟨4474358, by rfl⟩ : syracuseStep 5965811 = 8948717) B8948717
theorem B2984111 : Blo 1178406 2984111 := bstep (se 1 (by rfl) ⟨2238083, by rfl⟩ : syracuseStep 2984111 = 4476167) B4476167
theorem B4778203 : Blo 1178406 4778203 := bstep (se 1 (by rfl) ⟨3583652, by rfl⟩ : syracuseStep 4778203 = 7167305) B7167305
theorem B5974235 : Blo 1178406 5974235 := bstep (se 1 (by rfl) ⟨4480676, by rfl⟩ : syracuseStep 5974235 = 8961353) B8961353
theorem B2689691 : Blo 1178406 2689691 := bstep (se 1 (by rfl) ⟨2017268, by rfl⟩ : syracuseStep 2689691 = 4034537) B4034537
theorem B8497871 : Blo 1178406 8497871 := bstep (se 1 (by rfl) ⟨6373403, by rfl⟩ : syracuseStep 8497871 = 12746807) B12746807
theorem B57388247 : Blo 1178406 57388247 := bstep (se 1 (by rfl) ⟨43041185, by rfl⟩ : syracuseStep 57388247 = 86082371) B86082371
theorem B6049181 : Blo 1178406 6049181 := bstep (se 3 (by rfl) ⟨1134221, by rfl⟩ : syracuseStep 6049181 = 2268443) B2268443
theorem B32263595 : Blo 1178406 32263595 := bstep (se 1 (by rfl) ⟨24197696, by rfl⟩ : syracuseStep 32263595 = 48395393) B48395393
theorem B48385525 : Blo 1178406 48385525 := bstep (se 5 (by rfl) ⟨2268071, by rfl⟩ : syracuseStep 48385525 = 4536143) B4536143
theorem B5107535 : Blo 1178406 5107535 := bstep (se 1 (by rfl) ⟨3830651, by rfl⟩ : syracuseStep 5107535 = 7661303) B7661303
theorem B3977423 : Blo 1178406 3977423 := bstep (se 1 (by rfl) ⟨2983067, by rfl⟩ : syracuseStep 3977423 = 5966135) B5966135
theorem B223941145 : Blo 1178406 223941145 := bstep (se 2 (by rfl) ⟨83977929, by rfl⟩ : syracuseStep 223941145 = 167955859) B167955859
theorem B6378203 : Blo 1178406 6378203 := bstep (se 1 (by rfl) ⟨4783652, by rfl⟩ : syracuseStep 6378203 = 9567305) B9567305
theorem B1258687 : Blo 1178406 1258687 := bstep (se 1 (by rfl) ⟨944015, by rfl⟩ : syracuseStep 1258687 = 1888031) B1888031
theorem B21517825 : Blo 1178406 21517825 := bstep (se 2 (by rfl) ⟨8069184, by rfl⟩ : syracuseStep 21517825 = 16138369) B16138369
theorem B5969537 : Blo 1178406 5969537 := bstep (se 2 (by rfl) ⟨2238576, by rfl⟩ : syracuseStep 5969537 = 4477153) B4477153
theorem B7558865 : Blo 1178406 7558865 := bstep (se 2 (by rfl) ⟨2834574, by rfl⟩ : syracuseStep 7558865 = 5669149) B5669149
theorem B2987887 : Blo 1178406 2987887 := bstep (se 1 (by rfl) ⟨2240915, by rfl⟩ : syracuseStep 2987887 = 4481831) B4481831
theorem B2652263 : Blo 1178406 2652263 := bstep (se 1 (by rfl) ⟨1989197, by rfl⟩ : syracuseStep 2652263 = 3978395) B3978395
theorem B5970023 : Blo 1178406 5970023 := bstep (se 1 (by rfl) ⟨4477517, by rfl⟩ : syracuseStep 5970023 = 8955035) B8955035
theorem B1989103 : Blo 1178406 1989103 := bstep (se 1 (by rfl) ⟨1491827, by rfl⟩ : syracuseStep 1989103 = 2983655) B2983655
theorem B1767983 : Blo 1178406 1767983 := bstep (se 1 (by rfl) ⟨1325987, by rfl⟩ : syracuseStep 1767983 = 2651975) B2651975
theorem B2652767 : Blo 1178406 2652767 := bstep (se 1 (by rfl) ⟨1989575, by rfl⟩ : syracuseStep 2652767 = 3979151) B3979151
theorem B2652839 : Blo 1178406 2652839 := bstep (se 1 (by rfl) ⟨1989629, by rfl⟩ : syracuseStep 2652839 = 3979259) B3979259
theorem B5970671 : Blo 1178406 5970671 := bstep (se 1 (by rfl) ⟨4478003, by rfl⟩ : syracuseStep 5970671 = 8956007) B8956007
theorem B4782959 : Blo 1178406 4782959 := bstep (se 1 (by rfl) ⟨3587219, by rfl⟩ : syracuseStep 4782959 = 7174439) B7174439
theorem B2653055 : Blo 1178406 2653055 := bstep (se 1 (by rfl) ⟨1989791, by rfl⟩ : syracuseStep 2653055 = 3979583) B3979583
theorem B1178607 : Blo 1178406 1178607 := bstep (se 1 (by rfl) ⟨883955, by rfl⟩ : syracuseStep 1178607 = 1767911) B1767911
theorem B10083437 : Blo 1178406 10083437 := bstep (se 3 (by rfl) ⟨1890644, by rfl⟩ : syracuseStep 10083437 = 3781289) B3781289
theorem B1178735 : Blo 1178406 1178735 := bstep (se 1 (by rfl) ⟨884051, by rfl⟩ : syracuseStep 1178735 = 1768103) B1768103
theorem B1178875 : Blo 1178406 1178875 := bstep (se 1 (by rfl) ⟨884156, by rfl⟩ : syracuseStep 1178875 = 1768313) B1768313
theorem B15113627 : Blo 1178406 15113627 := bstep (se 1 (by rfl) ⟨11335220, by rfl⟩ : syracuseStep 15113627 = 22670441) B22670441
theorem B1179071 : Blo 1178406 1179071 := bstep (se 1 (by rfl) ⟨884303, by rfl⟩ : syracuseStep 1179071 = 1768607) B1768607
theorem B1179183 : Blo 1178406 1179183 := bstep (se 1 (by rfl) ⟨884387, by rfl⟩ : syracuseStep 1179183 = 1768775) B1768775
theorem B12107393 : Blo 1178406 12107393 := bstep (se 2 (by rfl) ⟨4540272, by rfl⟩ : syracuseStep 12107393 = 9080545) B9080545
theorem B2834527 : Blo 1178406 2834527 := bstep (se 1 (by rfl) ⟨2125895, by rfl⟩ : syracuseStep 2834527 = 4251791) B4251791
theorem B1179751 : Blo 1178406 1179751 := bstep (se 1 (by rfl) ⟨884813, by rfl⟩ : syracuseStep 1179751 = 1769627) B1769627
theorem B1769711 : Blo 1178406 1769711 := bstep (se 1 (by rfl) ⟨1327283, by rfl⟩ : syracuseStep 1769711 = 2654567) B2654567
theorem B1769963 : Blo 1178406 1769963 := bstep (se 1 (by rfl) ⟨1327472, by rfl⟩ : syracuseStep 1769963 = 2654945) B2654945
theorem B1180287 : Blo 1178406 1180287 := bstep (se 1 (by rfl) ⟨885215, by rfl⟩ : syracuseStep 1180287 = 1770431) B1770431
theorem B11338487 : Blo 1178406 11338487 := bstep (se 1 (by rfl) ⟨8503865, by rfl⟩ : syracuseStep 11338487 = 17007731) B17007731
theorem B1770239 : Blo 1178406 1770239 := bstep (se 1 (by rfl) ⟨1327679, by rfl⟩ : syracuseStep 1770239 = 2655359) B2655359
theorem B5039243 : Blo 1178406 5039243 := bstep (se 1 (by rfl) ⟨3779432, by rfl⟩ : syracuseStep 5039243 = 7558865) B7558865
theorem B3982823 : Blo 1178406 3982823 := bstep (se 1 (by rfl) ⟨2987117, by rfl⟩ : syracuseStep 3982823 = 5974235) B5974235
theorem B28690037 : Blo 1178406 28690037 := bstep (se 5 (by rfl) ⟨1344845, by rfl⟩ : syracuseStep 28690037 = 2689691) B2689691
theorem B17008541 : Blo 1178406 17008541 := bstep (se 3 (by rfl) ⟨3189101, by rfl⟩ : syracuseStep 17008541 = 6378203) B6378203
theorem B3188639 : Blo 1178406 3188639 := bstep (se 1 (by rfl) ⟨2391479, by rfl⟩ : syracuseStep 3188639 = 4782959) B4782959
theorem B64514033 : Blo 1178406 64514033 := bstep (se 2 (by rfl) ⟨24192762, by rfl⟩ : syracuseStep 64514033 = 48385525) B48385525
theorem B28690433 : Blo 1178406 28690433 := bstep (se 2 (by rfl) ⟨10758912, by rfl⟩ : syracuseStep 28690433 = 21517825) B21517825
theorem B38258831 : Blo 1178406 38258831 := bstep (se 1 (by rfl) ⟨28694123, by rfl⟩ : syracuseStep 38258831 = 57388247) B57388247
theorem B4032787 : Blo 1178406 4032787 := bstep (se 1 (by rfl) ⟨3024590, by rfl⟩ : syracuseStep 4032787 = 6049181) B6049181
theorem B8071595 : Blo 1178406 8071595 := bstep (se 1 (by rfl) ⟨6053696, by rfl⟩ : syracuseStep 8071595 = 12107393) B12107393
theorem B3983849 : Blo 1178406 3983849 := bstep (se 2 (by rfl) ⟨1493943, by rfl⟩ : syracuseStep 3983849 = 2987887) B2987887
theorem B12757661 : Blo 1178406 12757661 := bstep (se 3 (by rfl) ⟨2392061, by rfl⟩ : syracuseStep 12757661 = 4784123) B4784123
theorem B5040967 : Blo 1178406 5040967 := bstep (se 1 (by rfl) ⟨3780725, by rfl⟩ : syracuseStep 5040967 = 7561451) B7561451
theorem B235736237 : Blo 1178406 235736237 := bstep (se 3 (by rfl) ⟨44200544, by rfl⟩ : syracuseStep 235736237 = 88401089) B88401089
theorem B5975531 : Blo 1178406 5975531 := bstep (se 1 (by rfl) ⟨4481648, by rfl⟩ : syracuseStep 5975531 = 8963297) B8963297
theorem B3977207 : Blo 1178406 3977207 := bstep (se 1 (by rfl) ⟨2982905, by rfl⟩ : syracuseStep 3977207 = 5965811) B5965811
theorem B8065133 : Blo 1178406 8065133 := bstep (se 3 (by rfl) ⟨1512212, by rfl⟩ : syracuseStep 8065133 = 3024425) B3024425
theorem B5665247 : Blo 1178406 5665247 := bstep (se 1 (by rfl) ⟨4248935, by rfl⟩ : syracuseStep 5665247 = 8497871) B8497871
theorem B6722291 : Blo 1178406 6722291 := bstep (se 1 (by rfl) ⟨5041718, by rfl⟩ : syracuseStep 6722291 = 10083437) B10083437
theorem B21509063 : Blo 1178406 21509063 := bstep (se 1 (by rfl) ⟨16131797, by rfl⟩ : syracuseStep 21509063 = 32263595) B32263595
theorem B3405023 : Blo 1178406 3405023 := bstep (se 1 (by rfl) ⟨2553767, by rfl⟩ : syracuseStep 3405023 = 5107535) B5107535
theorem B2651615 : Blo 1178406 2651615 := bstep (se 1 (by rfl) ⟨1988711, by rfl⟩ : syracuseStep 2651615 = 3977423) B3977423
theorem B6370937 : Blo 1178406 6370937 := bstep (se 2 (by rfl) ⟨2389101, by rfl⟩ : syracuseStep 6370937 = 4778203) B4778203
theorem B516560651 : Blo 1178406 516560651 := bstep (se 1 (by rfl) ⟨387420488, by rfl⟩ : syracuseStep 516560651 = 774840977) B774840977
theorem B2652137 : Blo 1178406 2652137 := bstep (se 2 (by rfl) ⟨994551, by rfl⟩ : syracuseStep 2652137 = 1989103) B1989103
theorem B298588193 : Blo 1178406 298588193 := bstep (se 2 (by rfl) ⟨111970572, by rfl⟩ : syracuseStep 298588193 = 223941145) B223941145
theorem B4479083 : Blo 1178406 4479083 := bstep (se 1 (by rfl) ⟨3359312, by rfl⟩ : syracuseStep 4479083 = 6718625) B6718625
theorem B4479097 : Blo 1178406 4479097 := bstep (se 2 (by rfl) ⟨1679661, by rfl⟩ : syracuseStep 4479097 = 3359323) B3359323
theorem B3979691 : Blo 1178406 3979691 := bstep (se 1 (by rfl) ⟨2984768, by rfl⟩ : syracuseStep 3979691 = 5969537) B5969537
theorem B1989211 : Blo 1178406 1989211 := bstep (se 1 (by rfl) ⟨1491908, by rfl⟩ : syracuseStep 1989211 = 2983817) B2983817
theorem B1768175 : Blo 1178406 1768175 := bstep (se 1 (by rfl) ⟨1326131, by rfl⟩ : syracuseStep 1768175 = 2652263) B2652263
theorem B3980015 : Blo 1178406 3980015 := bstep (se 1 (by rfl) ⟨2985011, by rfl⟩ : syracuseStep 3980015 = 5970023) B5970023
theorem B1989407 : Blo 1178406 1989407 := bstep (se 1 (by rfl) ⟨1492055, by rfl⟩ : syracuseStep 1989407 = 2984111) B2984111
theorem B1678249 : Blo 1178406 1678249 := bstep (se 2 (by rfl) ⟨629343, by rfl⟩ : syracuseStep 1678249 = 1258687) B1258687
theorem B1178655 : Blo 1178406 1178655 := bstep (se 1 (by rfl) ⟨883991, by rfl⟩ : syracuseStep 1178655 = 1767983) B1767983
theorem B1768511 : Blo 1178406 1768511 := bstep (se 1 (by rfl) ⟨1326383, by rfl⟩ : syracuseStep 1768511 = 2652767) B2652767
theorem B1768559 : Blo 1178406 1768559 := bstep (se 1 (by rfl) ⟨1326419, by rfl⟩ : syracuseStep 1768559 = 2652839) B2652839
theorem B3980447 : Blo 1178406 3980447 := bstep (se 1 (by rfl) ⟨2985335, by rfl⟩ : syracuseStep 3980447 = 5970671) B5970671
theorem B1768703 : Blo 1178406 1768703 := bstep (se 1 (by rfl) ⟨1326527, by rfl⟩ : syracuseStep 1768703 = 2653055) B2653055
theorem B10075751 : Blo 1178406 10075751 := bstep (se 1 (by rfl) ⟨7556813, by rfl⟩ : syracuseStep 10075751 = 15113627) B15113627
theorem B1179807 : Blo 1178406 1179807 := bstep (se 1 (by rfl) ⟨884855, by rfl⟩ : syracuseStep 1179807 = 1769711) B1769711
theorem B5972129 : Blo 1178406 5972129 := bstep (se 2 (by rfl) ⟨2239548, by rfl⟩ : syracuseStep 5972129 = 4479097) B4479097
theorem B3776831 : Blo 1178406 3776831 := bstep (se 1 (by rfl) ⟨2832623, by rfl⟩ : syracuseStep 3776831 = 5665247) B5665247
theorem B1179975 : Blo 1178406 1179975 := bstep (se 1 (by rfl) ⟨884981, by rfl⟩ : syracuseStep 1179975 = 1769963) B1769963
theorem B4481527 : Blo 1178406 4481527 := bstep (se 1 (by rfl) ⟨3361145, by rfl⟩ : syracuseStep 4481527 = 6722291) B6722291
theorem B1180159 : Blo 1178406 1180159 := bstep (se 1 (by rfl) ⟨885119, by rfl⟩ : syracuseStep 1180159 = 1770239) B1770239
theorem B3359495 : Blo 1178406 3359495 := bstep (se 1 (by rfl) ⟨2519621, by rfl⟩ : syracuseStep 3359495 = 5039243) B5039243
theorem B2270015 : Blo 1178406 2270015 := bstep (se 1 (by rfl) ⟨1702511, by rfl⟩ : syracuseStep 2270015 = 3405023) B3405023
theorem B2655215 : Blo 1178406 2655215 := bstep (se 1 (by rfl) ⟨1991411, by rfl⟩ : syracuseStep 2655215 = 3982823) B3982823
theorem B11339027 : Blo 1178406 11339027 := bstep (se 1 (by rfl) ⟨8504270, by rfl⟩ : syracuseStep 11339027 = 17008541) B17008541
theorem B43009355 : Blo 1178406 43009355 := bstep (se 1 (by rfl) ⟨32257016, by rfl⟩ : syracuseStep 43009355 = 64514033) B64514033
theorem B199058795 : Blo 1178406 199058795 := bstep (se 1 (by rfl) ⟨149294096, by rfl⟩ : syracuseStep 199058795 = 298588193) B298588193
theorem B2655899 : Blo 1178406 2655899 := bstep (se 1 (by rfl) ⟨1991924, by rfl⟩ : syracuseStep 2655899 = 3983849) B3983849
theorem B8505107 : Blo 1178406 8505107 := bstep (se 1 (by rfl) ⟨6378830, by rfl⟩ : syracuseStep 8505107 = 12757661) B12757661
theorem B157157491 : Blo 1178406 157157491 := bstep (se 1 (by rfl) ⟨117868118, by rfl⟩ : syracuseStep 157157491 = 235736237) B235736237
theorem B3983687 : Blo 1178406 3983687 := bstep (se 1 (by rfl) ⟨2987765, by rfl⟩ : syracuseStep 3983687 = 5975531) B5975531
theorem B5376755 : Blo 1178406 5376755 := bstep (se 1 (by rfl) ⟨4032566, by rfl⟩ : syracuseStep 5376755 = 8065133) B8065133
theorem B3779369 : Blo 1178406 3779369 := bstep (se 2 (by rfl) ⟨1417263, by rfl⟩ : syracuseStep 3779369 = 2834527) B2834527
theorem B5377049 : Blo 1178406 5377049 := bstep (se 2 (by rfl) ⟨2016393, by rfl⟩ : syracuseStep 5377049 = 4032787) B4032787
theorem B14339375 : Blo 1178406 14339375 := bstep (se 1 (by rfl) ⟨10754531, by rfl⟩ : syracuseStep 14339375 = 21509063) B21509063
theorem B4247291 : Blo 1178406 4247291 := bstep (se 1 (by rfl) ⟨3185468, by rfl⟩ : syracuseStep 4247291 = 6370937) B6370937
theorem B6721289 : Blo 1178406 6721289 := bstep (se 2 (by rfl) ⟨2520483, by rfl⟩ : syracuseStep 6721289 = 5040967) B5040967
theorem B2125759 : Blo 1178406 2125759 := bstep (se 1 (by rfl) ⟨1594319, by rfl⟩ : syracuseStep 2125759 = 3188639) B3188639
theorem B2986055 : Blo 1178406 2986055 := bstep (se 1 (by rfl) ⟨2239541, by rfl⟩ : syracuseStep 2986055 = 4479083) B4479083
theorem B25505887 : Blo 1178406 25505887 := bstep (se 1 (by rfl) ⟨19129415, by rfl⟩ : syracuseStep 25505887 = 38258831) B38258831
theorem B8950661 : Blo 1178406 8950661 := bstep (se 4 (by rfl) ⟨839124, by rfl⟩ : syracuseStep 8950661 = 1678249) B1678249
theorem B2651471 : Blo 1178406 2651471 := bstep (se 1 (by rfl) ⟨1988603, by rfl⟩ : syracuseStep 2651471 = 3977207) B3977207
theorem B7558991 : Blo 1178406 7558991 := bstep (se 1 (by rfl) ⟨5669243, by rfl⟩ : syracuseStep 7558991 = 11338487) B11338487
theorem B2652281 : Blo 1178406 2652281 := bstep (se 2 (by rfl) ⟨994605, by rfl⟩ : syracuseStep 2652281 = 1989211) B1989211
theorem B1767743 : Blo 1178406 1767743 := bstep (se 1 (by rfl) ⟨1325807, by rfl⟩ : syracuseStep 1767743 = 2651615) B2651615
theorem B19126691 : Blo 1178406 19126691 := bstep (se 1 (by rfl) ⟨14345018, by rfl⟩ : syracuseStep 19126691 = 28690037) B28690037
theorem B344373767 : Blo 1178406 344373767 := bstep (se 1 (by rfl) ⟨258280325, by rfl⟩ : syracuseStep 344373767 = 516560651) B516560651
theorem B1768091 : Blo 1178406 1768091 := bstep (se 1 (by rfl) ⟨1326068, by rfl⟩ : syracuseStep 1768091 = 2652137) B2652137
theorem B19126955 : Blo 1178406 19126955 := bstep (se 1 (by rfl) ⟨14345216, by rfl⟩ : syracuseStep 19126955 = 28690433) B28690433
theorem B2653127 : Blo 1178406 2653127 := bstep (se 1 (by rfl) ⟨1989845, by rfl⟩ : syracuseStep 2653127 = 3979691) B3979691
theorem B5381063 : Blo 1178406 5381063 := bstep (se 1 (by rfl) ⟨4035797, by rfl⟩ : syracuseStep 5381063 = 8071595) B8071595
theorem B1178783 : Blo 1178406 1178783 := bstep (se 1 (by rfl) ⟨884087, by rfl⟩ : syracuseStep 1178783 = 1768175) B1768175
theorem B2653343 : Blo 1178406 2653343 := bstep (se 1 (by rfl) ⟨1990007, by rfl⟩ : syracuseStep 2653343 = 3980015) B3980015
theorem B1326271 : Blo 1178406 1326271 := bstep (se 1 (by rfl) ⟨994703, by rfl⟩ : syracuseStep 1326271 = 1989407) B1989407
theorem B1179007 : Blo 1178406 1179007 := bstep (se 1 (by rfl) ⟨884255, by rfl⟩ : syracuseStep 1179007 = 1768511) B1768511
theorem B1179039 : Blo 1178406 1179039 := bstep (se 1 (by rfl) ⟨884279, by rfl⟩ : syracuseStep 1179039 = 1768559) B1768559
theorem B2653631 : Blo 1178406 2653631 := bstep (se 1 (by rfl) ⟨1990223, by rfl⟩ : syracuseStep 2653631 = 3980447) B3980447
theorem B1179135 : Blo 1178406 1179135 := bstep (se 1 (by rfl) ⟨884351, by rfl⟩ : syracuseStep 1179135 = 1768703) B1768703
theorem B6717167 : Blo 1178406 6717167 := bstep (se 1 (by rfl) ⟨5037875, by rfl⟩ : syracuseStep 6717167 = 10075751) B10075751
theorem B1990703 : Blo 1178406 1990703 := bstep (se 1 (by rfl) ⟨1493027, by rfl⟩ : syracuseStep 1990703 = 2986055) B2986055
theorem B3981419 : Blo 1178406 3981419 := bstep (se 1 (by rfl) ⟨2986064, by rfl⟩ : syracuseStep 3981419 = 5972129) B5972129
theorem B209543321 : Blo 1178406 209543321 := bstep (se 2 (by rfl) ⟨78578745, by rfl⟩ : syracuseStep 209543321 = 157157491) B157157491
theorem B1770143 : Blo 1178406 1770143 := bstep (se 1 (by rfl) ⟨1327607, by rfl⟩ : syracuseStep 1770143 = 2655215) B2655215
theorem B28672903 : Blo 1178406 28672903 := bstep (se 1 (by rfl) ⟨21504677, by rfl⟩ : syracuseStep 28672903 = 43009355) B43009355
theorem B1770599 : Blo 1178406 1770599 := bstep (se 1 (by rfl) ⟨1327949, by rfl⟩ : syracuseStep 1770599 = 2655899) B2655899
theorem B5670071 : Blo 1178406 5670071 := bstep (se 1 (by rfl) ⟨4252553, by rfl⟩ : syracuseStep 5670071 = 8505107) B8505107
theorem B5039327 : Blo 1178406 5039327 := bstep (se 1 (by rfl) ⟨3779495, by rfl⟩ : syracuseStep 5039327 = 7558991) B7558991
theorem B2655791 : Blo 1178406 2655791 := bstep (se 1 (by rfl) ⟨1991843, by rfl⟩ : syracuseStep 2655791 = 3983687) B3983687
theorem B229582511 : Blo 1178406 229582511 := bstep (se 1 (by rfl) ⟨172186883, by rfl⟩ : syracuseStep 229582511 = 344373767) B344373767
theorem B34007849 : Blo 1178406 34007849 := bstep (se 2 (by rfl) ⟨12752943, by rfl⟩ : syracuseStep 34007849 = 25505887) B25505887
theorem B2517887 : Blo 1178406 2517887 := bstep (se 1 (by rfl) ⟨1888415, by rfl⟩ : syracuseStep 2517887 = 3776831) B3776831
theorem B2239663 : Blo 1178406 2239663 := bstep (se 1 (by rfl) ⟨1679747, by rfl⟩ : syracuseStep 2239663 = 3359495) B3359495
theorem B5967107 : Blo 1178406 5967107 := bstep (se 1 (by rfl) ⟨4475330, by rfl⟩ : syracuseStep 5967107 = 8950661) B8950661
theorem B5975369 : Blo 1178406 5975369 := bstep (se 2 (by rfl) ⟨2240763, by rfl⟩ : syracuseStep 5975369 = 4481527) B4481527
theorem B132705863 : Blo 1178406 132705863 := bstep (se 1 (by rfl) ⟨99529397, by rfl⟩ : syracuseStep 132705863 = 199058795) B199058795
theorem B12751127 : Blo 1178406 12751127 := bstep (se 1 (by rfl) ⟨9563345, by rfl⟩ : syracuseStep 12751127 = 19126691) B19126691
theorem B12751303 : Blo 1178406 12751303 := bstep (se 1 (by rfl) ⟨9563477, by rfl⟩ : syracuseStep 12751303 = 19126955) B19126955
theorem B3584503 : Blo 1178406 3584503 := bstep (se 1 (by rfl) ⟨2688377, by rfl⟩ : syracuseStep 3584503 = 5376755) B5376755
theorem B2519579 : Blo 1178406 2519579 := bstep (se 1 (by rfl) ⟨1889684, by rfl⟩ : syracuseStep 2519579 = 3779369) B3779369
theorem B3584699 : Blo 1178406 3584699 := bstep (se 1 (by rfl) ⟨2688524, by rfl⟩ : syracuseStep 3584699 = 5377049) B5377049
theorem B4478111 : Blo 1178406 4478111 := bstep (se 1 (by rfl) ⟨3358583, by rfl⟩ : syracuseStep 4478111 = 6717167) B6717167
theorem B2831527 : Blo 1178406 2831527 := bstep (se 1 (by rfl) ⟨2123645, by rfl⟩ : syracuseStep 2831527 = 4247291) B4247291
theorem B1513343 : Blo 1178406 1513343 := bstep (se 1 (by rfl) ⟨1135007, by rfl⟩ : syracuseStep 1513343 = 2270015) B2270015
theorem B7559351 : Blo 1178406 7559351 := bstep (se 1 (by rfl) ⟨5669513, by rfl⟩ : syracuseStep 7559351 = 11339027) B11339027
theorem B1767647 : Blo 1178406 1767647 := bstep (se 1 (by rfl) ⟨1325735, by rfl⟩ : syracuseStep 1767647 = 2651471) B2651471
theorem B1768187 : Blo 1178406 1768187 := bstep (se 1 (by rfl) ⟨1326140, by rfl⟩ : syracuseStep 1768187 = 2652281) B2652281
theorem B1178495 : Blo 1178406 1178495 := bstep (se 1 (by rfl) ⟨883871, by rfl⟩ : syracuseStep 1178495 = 1767743) B1767743
theorem B1768361 : Blo 1178406 1768361 := bstep (se 2 (by rfl) ⟨663135, by rfl⟩ : syracuseStep 1768361 = 1326271) B1326271
theorem B1178727 : Blo 1178406 1178727 := bstep (se 1 (by rfl) ⟨884045, by rfl⟩ : syracuseStep 1178727 = 1768091) B1768091
theorem B1768751 : Blo 1178406 1768751 := bstep (se 1 (by rfl) ⟨1326563, by rfl⟩ : syracuseStep 1768751 = 2653127) B2653127
theorem B3587375 : Blo 1178406 3587375 := bstep (se 1 (by rfl) ⟨2690531, by rfl⟩ : syracuseStep 3587375 = 5381063) B5381063
theorem B1768895 : Blo 1178406 1768895 := bstep (se 1 (by rfl) ⟨1326671, by rfl⟩ : syracuseStep 1768895 = 2653343) B2653343
theorem B9559583 : Blo 1178406 9559583 := bstep (se 1 (by rfl) ⟨7169687, by rfl⟩ : syracuseStep 9559583 = 14339375) B14339375
theorem B1769087 : Blo 1178406 1769087 := bstep (se 1 (by rfl) ⟨1326815, by rfl⟩ : syracuseStep 1769087 = 2653631) B2653631
theorem B4480859 : Blo 1178406 4480859 := bstep (se 1 (by rfl) ⟨3360644, by rfl⟩ : syracuseStep 4480859 = 6721289) B6721289
theorem B2834345 : Blo 1178406 2834345 := bstep (se 2 (by rfl) ⟨1062879, by rfl⟩ : syracuseStep 2834345 = 2125759) B2125759
theorem B1327135 : Blo 1178406 1327135 := bstep (se 1 (by rfl) ⟨995351, by rfl⟩ : syracuseStep 1327135 = 1990703) B1990703
theorem B2654279 : Blo 1178406 2654279 := bstep (se 1 (by rfl) ⟨1990709, by rfl⟩ : syracuseStep 2654279 = 3981419) B3981419
theorem B1679719 : Blo 1178406 1679719 := bstep (se 1 (by rfl) ⟨1259789, by rfl⟩ : syracuseStep 1679719 = 2519579) B2519579
theorem B1180095 : Blo 1178406 1180095 := bstep (se 1 (by rfl) ⟨885071, by rfl⟩ : syracuseStep 1180095 = 1770143) B1770143
theorem B1180399 : Blo 1178406 1180399 := bstep (se 1 (by rfl) ⟨885299, by rfl⟩ : syracuseStep 1180399 = 1770599) B1770599
theorem B3359551 : Blo 1178406 3359551 := bstep (se 1 (by rfl) ⟨2519663, by rfl⟩ : syracuseStep 3359551 = 5039327) B5039327
theorem B1770527 : Blo 1178406 1770527 := bstep (se 1 (by rfl) ⟨1327895, by rfl⟩ : syracuseStep 1770527 = 2655791) B2655791
theorem B5039567 : Blo 1178406 5039567 := bstep (se 1 (by rfl) ⟨3779675, by rfl⟩ : syracuseStep 5039567 = 7559351) B7559351
theorem B3983579 : Blo 1178406 3983579 := bstep (se 1 (by rfl) ⟨2987684, by rfl⟩ : syracuseStep 3983579 = 5975369) B5975369
theorem B17001737 : Blo 1178406 17001737 := bstep (se 2 (by rfl) ⟨6375651, by rfl⟩ : syracuseStep 17001737 = 12751303) B12751303
theorem B4779337 : Blo 1178406 4779337 := bstep (se 2 (by rfl) ⟨1792251, by rfl⟩ : syracuseStep 4779337 = 3584503) B3584503
theorem B2985407 : Blo 1178406 2985407 := bstep (se 1 (by rfl) ⟨2239055, by rfl⟩ : syracuseStep 2985407 = 4478111) B4478111
theorem B3780047 : Blo 1178406 3780047 := bstep (se 1 (by rfl) ⟨2835035, by rfl⟩ : syracuseStep 3780047 = 5670071) B5670071
theorem B15101477 : Blo 1178406 15101477 := bstep (se 4 (by rfl) ⟨1415763, by rfl⟩ : syracuseStep 15101477 = 2831527) B2831527
theorem B153055007 : Blo 1178406 153055007 := bstep (se 1 (by rfl) ⟨114791255, by rfl⟩ : syracuseStep 153055007 = 229582511) B229582511
theorem B2986217 : Blo 1178406 2986217 := bstep (se 2 (by rfl) ⟨1119831, by rfl⟩ : syracuseStep 2986217 = 2239663) B2239663
theorem B22671899 : Blo 1178406 22671899 := bstep (se 1 (by rfl) ⟨17003924, by rfl⟩ : syracuseStep 22671899 = 34007849) B34007849
theorem B3978071 : Blo 1178406 3978071 := bstep (se 1 (by rfl) ⟨2983553, by rfl⟩ : syracuseStep 3978071 = 5967107) B5967107
theorem B4035581 : Blo 1178406 4035581 := bstep (se 3 (by rfl) ⟨756671, by rfl⟩ : syracuseStep 4035581 = 1513343) B1513343
theorem B88470575 : Blo 1178406 88470575 := bstep (se 1 (by rfl) ⟨66352931, by rfl⟩ : syracuseStep 88470575 = 132705863) B132705863
theorem B2987239 : Blo 1178406 2987239 := bstep (se 1 (by rfl) ⟨2240429, by rfl⟩ : syracuseStep 2987239 = 4480859) B4480859
theorem B1889563 : Blo 1178406 1889563 := bstep (se 1 (by rfl) ⟨1417172, by rfl⟩ : syracuseStep 1889563 = 2834345) B2834345
theorem B139695547 : Blo 1178406 139695547 := bstep (se 1 (by rfl) ⟨104771660, by rfl⟩ : syracuseStep 139695547 = 209543321) B209543321
theorem B8500751 : Blo 1178406 8500751 := bstep (se 1 (by rfl) ⟨6375563, by rfl⟩ : syracuseStep 8500751 = 12751127) B12751127
theorem B2389799 : Blo 1178406 2389799 := bstep (se 1 (by rfl) ⟨1792349, by rfl⟩ : syracuseStep 2389799 = 3584699) B3584699
theorem B9566333 : Blo 1178406 9566333 := bstep (se 3 (by rfl) ⟨1793687, by rfl⟩ : syracuseStep 9566333 = 3587375) B3587375
theorem B38230537 : Blo 1178406 38230537 := bstep (se 2 (by rfl) ⟨14336451, by rfl⟩ : syracuseStep 38230537 = 28672903) B28672903
theorem B1178431 : Blo 1178406 1178431 := bstep (se 1 (by rfl) ⟨883823, by rfl⟩ : syracuseStep 1178431 = 1767647) B1767647
theorem B1178791 : Blo 1178406 1178791 := bstep (se 1 (by rfl) ⟨884093, by rfl⟩ : syracuseStep 1178791 = 1768187) B1768187
theorem B1678591 : Blo 1178406 1678591 := bstep (se 1 (by rfl) ⟨1258943, by rfl⟩ : syracuseStep 1678591 = 2517887) B2517887
theorem B1178907 : Blo 1178406 1178907 := bstep (se 1 (by rfl) ⟨884180, by rfl⟩ : syracuseStep 1178907 = 1768361) B1768361
theorem B1179167 : Blo 1178406 1179167 := bstep (se 1 (by rfl) ⟨884375, by rfl⟩ : syracuseStep 1179167 = 1768751) B1768751
theorem B1179263 : Blo 1178406 1179263 := bstep (se 1 (by rfl) ⟨884447, by rfl⟩ : syracuseStep 1179263 = 1768895) B1768895
theorem B6373055 : Blo 1178406 6373055 := bstep (se 1 (by rfl) ⟨4779791, by rfl⟩ : syracuseStep 6373055 = 9559583) B9559583
theorem B1179391 : Blo 1178406 1179391 := bstep (se 1 (by rfl) ⟨884543, by rfl⟩ : syracuseStep 1179391 = 1769087) B1769087
theorem B1769513 : Blo 1178406 1769513 := bstep (se 2 (by rfl) ⟨663567, by rfl⟩ : syracuseStep 1769513 = 1327135) B1327135
theorem B1769519 : Blo 1178406 1769519 := bstep (se 1 (by rfl) ⟨1327139, by rfl⟩ : syracuseStep 1769519 = 2654279) B2654279
theorem B1990811 : Blo 1178406 1990811 := bstep (se 1 (by rfl) ⟨1493108, by rfl⟩ : syracuseStep 1990811 = 2986217) B2986217
theorem B15114599 : Blo 1178406 15114599 := bstep (se 1 (by rfl) ⟨11335949, by rfl⟩ : syracuseStep 15114599 = 22671899) B22671899
theorem B1180351 : Blo 1178406 1180351 := bstep (se 1 (by rfl) ⟨885263, by rfl⟩ : syracuseStep 1180351 = 1770527) B1770527
theorem B3359711 : Blo 1178406 3359711 := bstep (se 1 (by rfl) ⟨2519783, by rfl⟩ : syracuseStep 3359711 = 5039567) B5039567
theorem B2655719 : Blo 1178406 2655719 := bstep (se 1 (by rfl) ⟨1991789, by rfl⟩ : syracuseStep 2655719 = 3983579) B3983579
theorem B3982985 : Blo 1178406 3982985 := bstep (se 2 (by rfl) ⟨1493619, by rfl⟩ : syracuseStep 3982985 = 2987239) B2987239
theorem B2238121 : Blo 1178406 2238121 := bstep (se 2 (by rfl) ⟨839295, by rfl⟩ : syracuseStep 2238121 = 1678591) B1678591
theorem B2239625 : Blo 1178406 2239625 := bstep (se 2 (by rfl) ⟨839859, by rfl⟩ : syracuseStep 2239625 = 1679719) B1679719
theorem B2690387 : Blo 1178406 2690387 := bstep (se 1 (by rfl) ⟨2017790, by rfl⟩ : syracuseStep 2690387 = 4035581) B4035581
theorem B50974049 : Blo 1178406 50974049 := bstep (se 2 (by rfl) ⟨19115268, by rfl⟩ : syracuseStep 50974049 = 38230537) B38230537
theorem B1593199 : Blo 1178406 1593199 := bstep (se 1 (by rfl) ⟨1194899, by rfl⟩ : syracuseStep 1593199 = 2389799) B2389799
theorem B10080125 : Blo 1178406 10080125 := bstep (se 3 (by rfl) ⟨1890023, by rfl⟩ : syracuseStep 10080125 = 3780047) B3780047
theorem B6377555 : Blo 1178406 6377555 := bstep (se 1 (by rfl) ⟨4783166, by rfl⟩ : syracuseStep 6377555 = 9566333) B9566333
theorem B2519417 : Blo 1178406 2519417 := bstep (se 2 (by rfl) ⟨944781, by rfl⟩ : syracuseStep 2519417 = 1889563) B1889563
theorem B11334491 : Blo 1178406 11334491 := bstep (se 1 (by rfl) ⟨8500868, by rfl⟩ : syracuseStep 11334491 = 17001737) B17001737
theorem B4248703 : Blo 1178406 4248703 := bstep (se 1 (by rfl) ⟨3186527, by rfl⟩ : syracuseStep 4248703 = 6373055) B6373055
theorem B102036671 : Blo 1178406 102036671 := bstep (se 1 (by rfl) ⟨76527503, by rfl⟩ : syracuseStep 102036671 = 153055007) B153055007
theorem B2652047 : Blo 1178406 2652047 := bstep (se 1 (by rfl) ⟨1989035, by rfl⟩ : syracuseStep 2652047 = 3978071) B3978071
theorem B58980383 : Blo 1178406 58980383 := bstep (se 1 (by rfl) ⟨44235287, by rfl⟩ : syracuseStep 58980383 = 88470575) B88470575
theorem B5667167 : Blo 1178406 5667167 := bstep (se 1 (by rfl) ⟨4250375, by rfl⟩ : syracuseStep 5667167 = 8500751) B8500751
theorem B4479401 : Blo 1178406 4479401 := bstep (se 2 (by rfl) ⟨1679775, by rfl⟩ : syracuseStep 4479401 = 3359551) B3359551
theorem B6372449 : Blo 1178406 6372449 := bstep (se 2 (by rfl) ⟨2389668, by rfl⟩ : syracuseStep 6372449 = 4779337) B4779337
theorem B186260729 : Blo 1178406 186260729 := bstep (se 2 (by rfl) ⟨69847773, by rfl⟩ : syracuseStep 186260729 = 139695547) B139695547
theorem B1990271 : Blo 1178406 1990271 := bstep (se 1 (by rfl) ⟨1492703, by rfl⟩ : syracuseStep 1990271 = 2985407) B2985407
theorem B10067651 : Blo 1178406 10067651 := bstep (se 1 (by rfl) ⟨7550738, by rfl⟩ : syracuseStep 10067651 = 15101477) B15101477
theorem B1179675 : Blo 1178406 1179675 := bstep (se 1 (by rfl) ⟨884756, by rfl⟩ : syracuseStep 1179675 = 1769513) B1769513
theorem B1179679 : Blo 1178406 1179679 := bstep (se 1 (by rfl) ⟨884759, by rfl⟩ : syracuseStep 1179679 = 1769519) B1769519
theorem B4251703 : Blo 1178406 4251703 := bstep (se 1 (by rfl) ⟨3188777, by rfl⟩ : syracuseStep 4251703 = 6377555) B6377555
theorem B1327207 : Blo 1178406 1327207 := bstep (se 1 (by rfl) ⟨995405, by rfl⟩ : syracuseStep 1327207 = 1990811) B1990811
theorem B10076399 : Blo 1178406 10076399 := bstep (se 1 (by rfl) ⟨7557299, by rfl⟩ : syracuseStep 10076399 = 15114599) B15114599
theorem B1679611 : Blo 1178406 1679611 := bstep (se 1 (by rfl) ⟨1259708, by rfl⟩ : syracuseStep 1679611 = 2519417) B2519417
theorem B22659749 : Blo 1178406 22659749 := bstep (se 4 (by rfl) ⟨2124351, by rfl⟩ : syracuseStep 22659749 = 4248703) B4248703
theorem B1770479 : Blo 1178406 1770479 := bstep (se 1 (by rfl) ⟨1327859, by rfl⟩ : syracuseStep 1770479 = 2655719) B2655719
theorem B2655323 : Blo 1178406 2655323 := bstep (se 1 (by rfl) ⟨1991492, by rfl⟩ : syracuseStep 2655323 = 3982985) B3982985
theorem B3778111 : Blo 1178406 3778111 := bstep (se 1 (by rfl) ⟨2833583, by rfl⟩ : syracuseStep 3778111 = 5667167) B5667167
theorem B8497061 : Blo 1178406 8497061 := bstep (se 4 (by rfl) ⟨796599, by rfl⟩ : syracuseStep 8497061 = 1593199) B1593199
theorem B1493083 : Blo 1178406 1493083 := bstep (se 1 (by rfl) ⟨1119812, by rfl⟩ : syracuseStep 1493083 = 2239625) B2239625
theorem B2984161 : Blo 1178406 2984161 := bstep (se 2 (by rfl) ⟨1119060, by rfl⟩ : syracuseStep 2984161 = 2238121) B2238121
theorem B33982699 : Blo 1178406 33982699 := bstep (se 1 (by rfl) ⟨25487024, by rfl⟩ : syracuseStep 33982699 = 50974049) B50974049
theorem B6711767 : Blo 1178406 6711767 := bstep (se 1 (by rfl) ⟨5033825, by rfl⟩ : syracuseStep 6711767 = 10067651) B10067651
theorem B6720083 : Blo 1178406 6720083 := bstep (se 1 (by rfl) ⟨5040062, by rfl⟩ : syracuseStep 6720083 = 10080125) B10080125
theorem B7556327 : Blo 1178406 7556327 := bstep (se 1 (by rfl) ⟨5667245, by rfl⟩ : syracuseStep 7556327 = 11334491) B11334491
theorem B2239807 : Blo 1178406 2239807 := bstep (se 1 (by rfl) ⟨1679855, by rfl⟩ : syracuseStep 2239807 = 3359711) B3359711
theorem B2986267 : Blo 1178406 2986267 := bstep (se 1 (by rfl) ⟨2239700, by rfl⟩ : syracuseStep 2986267 = 4479401) B4479401
theorem B4248299 : Blo 1178406 4248299 := bstep (se 1 (by rfl) ⟨3186224, by rfl⟩ : syracuseStep 4248299 = 6372449) B6372449
theorem B496695277 : Blo 1178406 496695277 := bstep (se 3 (by rfl) ⟨93130364, by rfl⟩ : syracuseStep 496695277 = 186260729) B186260729
theorem B68024447 : Blo 1178406 68024447 := bstep (se 1 (by rfl) ⟨51018335, by rfl⟩ : syracuseStep 68024447 = 102036671) B102036671
theorem B1768031 : Blo 1178406 1768031 := bstep (se 1 (by rfl) ⟨1326023, by rfl⟩ : syracuseStep 1768031 = 2652047) B2652047
theorem B39320255 : Blo 1178406 39320255 := bstep (se 1 (by rfl) ⟨29490191, by rfl⟩ : syracuseStep 39320255 = 58980383) B58980383
theorem B1793591 : Blo 1178406 1793591 := bstep (se 1 (by rfl) ⟨1345193, by rfl⟩ : syracuseStep 1793591 = 2690387) B2690387
theorem B1326847 : Blo 1178406 1326847 := bstep (se 1 (by rfl) ⟨995135, by rfl⟩ : syracuseStep 1326847 = 1990271) B1990271
theorem B5668937 : Blo 1178406 5668937 := bstep (se 2 (by rfl) ⟨2125851, by rfl⟩ : syracuseStep 5668937 = 4251703) B4251703
theorem B1990777 : Blo 1178406 1990777 := bstep (se 2 (by rfl) ⟨746541, by rfl⟩ : syracuseStep 1990777 = 1493083) B1493083
theorem B1769609 : Blo 1178406 1769609 := bstep (se 2 (by rfl) ⟨663603, by rfl⟩ : syracuseStep 1769609 = 1327207) B1327207
theorem B6717599 : Blo 1178406 6717599 := bstep (se 1 (by rfl) ⟨5038199, by rfl⟩ : syracuseStep 6717599 = 10076399) B10076399
theorem B45310265 : Blo 1178406 45310265 := bstep (se 2 (by rfl) ⟨16991349, by rfl⟩ : syracuseStep 45310265 = 33982699) B33982699
theorem B3981689 : Blo 1178406 3981689 := bstep (se 2 (by rfl) ⟨1493133, by rfl⟩ : syracuseStep 3981689 = 2986267) B2986267
theorem B15106499 : Blo 1178406 15106499 := bstep (se 1 (by rfl) ⟨11329874, by rfl⟩ : syracuseStep 15106499 = 22659749) B22659749
theorem B1180319 : Blo 1178406 1180319 := bstep (se 1 (by rfl) ⟨885239, by rfl⟩ : syracuseStep 1180319 = 1770479) B1770479
theorem B1770215 : Blo 1178406 1770215 := bstep (se 1 (by rfl) ⟨1327661, by rfl⟩ : syracuseStep 1770215 = 2655323) B2655323
theorem B4474511 : Blo 1178406 4474511 := bstep (se 1 (by rfl) ⟨3355883, by rfl⟩ : syracuseStep 4474511 = 6711767) B6711767
theorem B662260369 : Blo 1178406 662260369 := bstep (se 2 (by rfl) ⟨248347638, by rfl⟩ : syracuseStep 662260369 = 496695277) B496695277
theorem B2239481 : Blo 1178406 2239481 := bstep (se 2 (by rfl) ⟨839805, by rfl⟩ : syracuseStep 2239481 = 1679611) B1679611
theorem B5664707 : Blo 1178406 5664707 := bstep (se 1 (by rfl) ⟨4248530, by rfl⟩ : syracuseStep 5664707 = 8497061) B8497061
theorem B2986409 : Blo 1178406 2986409 := bstep (se 2 (by rfl) ⟨1119903, by rfl⟩ : syracuseStep 2986409 = 2239807) B2239807
theorem B3978881 : Blo 1178406 3978881 := bstep (se 2 (by rfl) ⟨1492080, by rfl⟩ : syracuseStep 3978881 = 2984161) B2984161
theorem B45349631 : Blo 1178406 45349631 := bstep (se 1 (by rfl) ⟨34012223, by rfl⟩ : syracuseStep 45349631 = 68024447) B68024447
theorem B4480055 : Blo 1178406 4480055 := bstep (se 1 (by rfl) ⟨3360041, by rfl⟩ : syracuseStep 4480055 = 6720083) B6720083
theorem B1178687 : Blo 1178406 1178687 := bstep (se 1 (by rfl) ⟨884015, by rfl⟩ : syracuseStep 1178687 = 1768031) B1768031
theorem B26213503 : Blo 1178406 26213503 := bstep (se 1 (by rfl) ⟨19660127, by rfl⟩ : syracuseStep 26213503 = 39320255) B39320255
theorem B11328797 : Blo 1178406 11328797 := bstep (se 3 (by rfl) ⟨2124149, by rfl⟩ : syracuseStep 11328797 = 4248299) B4248299
theorem B5037481 : Blo 1178406 5037481 := bstep (se 2 (by rfl) ⟨1889055, by rfl⟩ : syracuseStep 5037481 = 3778111) B3778111
theorem B5037551 : Blo 1178406 5037551 := bstep (se 1 (by rfl) ⟨3778163, by rfl⟩ : syracuseStep 5037551 = 7556327) B7556327
theorem B1769129 : Blo 1178406 1769129 := bstep (se 2 (by rfl) ⟨663423, by rfl⟩ : syracuseStep 1769129 = 1326847) B1326847
theorem B1195727 : Blo 1178406 1195727 := bstep (se 1 (by rfl) ⟨896795, by rfl⟩ : syracuseStep 1195727 = 1793591) B1793591
theorem B1179739 : Blo 1178406 1179739 := bstep (se 1 (by rfl) ⟨884804, by rfl⟩ : syracuseStep 1179739 = 1769609) B1769609
theorem B2654369 : Blo 1178406 2654369 := bstep (se 2 (by rfl) ⟨995388, by rfl⟩ : syracuseStep 2654369 = 1990777) B1990777
theorem B2654459 : Blo 1178406 2654459 := bstep (se 1 (by rfl) ⟨1990844, by rfl⟩ : syracuseStep 2654459 = 3981689) B3981689
theorem B1990939 : Blo 1178406 1990939 := bstep (se 1 (by rfl) ⟨1493204, by rfl⟩ : syracuseStep 1990939 = 2986409) B2986409
theorem B1180143 : Blo 1178406 1180143 := bstep (se 1 (by rfl) ⟨885107, by rfl⟩ : syracuseStep 1180143 = 1770215) B1770215
theorem B2983007 : Blo 1178406 2983007 := bstep (se 1 (by rfl) ⟨2237255, by rfl⟩ : syracuseStep 2983007 = 4474511) B4474511
theorem B3188605 : Blo 1178406 3188605 := bstep (se 3 (by rfl) ⟨597863, by rfl⟩ : syracuseStep 3188605 = 1195727) B1195727
theorem B1492987 : Blo 1178406 1492987 := bstep (se 1 (by rfl) ⟨1119740, by rfl⟩ : syracuseStep 1492987 = 2239481) B2239481
theorem B3779291 : Blo 1178406 3779291 := bstep (se 1 (by rfl) ⟨2834468, by rfl⟩ : syracuseStep 3779291 = 5668937) B5668937
theorem B30206843 : Blo 1178406 30206843 := bstep (se 1 (by rfl) ⟨22655132, by rfl⟩ : syracuseStep 30206843 = 45310265) B45310265
theorem B10070999 : Blo 1178406 10070999 := bstep (se 1 (by rfl) ⟨7553249, by rfl⟩ : syracuseStep 10070999 = 15106499) B15106499
theorem B34951337 : Blo 1178406 34951337 := bstep (se 2 (by rfl) ⟨13106751, by rfl⟩ : syracuseStep 34951337 = 26213503) B26213503
theorem B30233087 : Blo 1178406 30233087 := bstep (se 1 (by rfl) ⟨22674815, by rfl⟩ : syracuseStep 30233087 = 45349631) B45349631
theorem B2986703 : Blo 1178406 2986703 := bstep (se 1 (by rfl) ⟨2240027, by rfl⟩ : syracuseStep 2986703 = 4480055) B4480055
theorem B4478399 : Blo 1178406 4478399 := bstep (se 1 (by rfl) ⟨3358799, by rfl⟩ : syracuseStep 4478399 = 6717599) B6717599
theorem B883013825 : Blo 1178406 883013825 := bstep (se 2 (by rfl) ⟨331130184, by rfl⟩ : syracuseStep 883013825 = 662260369) B662260369
theorem B2652587 : Blo 1178406 2652587 := bstep (se 1 (by rfl) ⟨1989440, by rfl⟩ : syracuseStep 2652587 = 3978881) B3978881
theorem B6716641 : Blo 1178406 6716641 := bstep (se 2 (by rfl) ⟨2518740, by rfl⟩ : syracuseStep 6716641 = 5037481) B5037481
theorem B7552531 : Blo 1178406 7552531 := bstep (se 1 (by rfl) ⟨5664398, by rfl⟩ : syracuseStep 7552531 = 11328797) B11328797
theorem B3358367 : Blo 1178406 3358367 := bstep (se 1 (by rfl) ⟨2518775, by rfl⟩ : syracuseStep 3358367 = 5037551) B5037551
theorem B1179419 : Blo 1178406 1179419 := bstep (se 1 (by rfl) ⟨884564, by rfl⟩ : syracuseStep 1179419 = 1769129) B1769129
theorem B3776471 : Blo 1178406 3776471 := bstep (se 1 (by rfl) ⟨2832353, by rfl⟩ : syracuseStep 3776471 = 5664707) B5664707
theorem B1769579 : Blo 1178406 1769579 := bstep (se 1 (by rfl) ⟨1327184, by rfl⟩ : syracuseStep 1769579 = 2654369) B2654369
theorem B1769639 : Blo 1178406 1769639 := bstep (se 1 (by rfl) ⟨1327229, by rfl⟩ : syracuseStep 1769639 = 2654459) B2654459
theorem B2654585 : Blo 1178406 2654585 := bstep (se 2 (by rfl) ⟨995469, by rfl⟩ : syracuseStep 2654585 = 1990939) B1990939
theorem B1991135 : Blo 1178406 1991135 := bstep (se 1 (by rfl) ⟨1493351, by rfl⟩ : syracuseStep 1991135 = 2986703) B2986703
theorem B8955521 : Blo 1178406 8955521 := bstep (se 2 (by rfl) ⟨3358320, by rfl⟩ : syracuseStep 8955521 = 6716641) B6716641
theorem B20137895 : Blo 1178406 20137895 := bstep (se 1 (by rfl) ⟨15103421, by rfl⟩ : syracuseStep 20137895 = 30206843) B30206843
theorem B10070041 : Blo 1178406 10070041 := bstep (se 2 (by rfl) ⟨3776265, by rfl⟩ : syracuseStep 10070041 = 7552531) B7552531
theorem B2238911 : Blo 1178406 2238911 := bstep (se 1 (by rfl) ⟨1679183, by rfl⟩ : syracuseStep 2238911 = 3358367) B3358367
theorem B2517647 : Blo 1178406 2517647 := bstep (se 1 (by rfl) ⟨1888235, by rfl⟩ : syracuseStep 2517647 = 3776471) B3776471
theorem B23300891 : Blo 1178406 23300891 := bstep (se 1 (by rfl) ⟨17475668, by rfl⟩ : syracuseStep 23300891 = 34951337) B34951337
theorem B20155391 : Blo 1178406 20155391 := bstep (se 1 (by rfl) ⟨15116543, by rfl⟩ : syracuseStep 20155391 = 30233087) B30233087
theorem B2985599 : Blo 1178406 2985599 := bstep (se 1 (by rfl) ⟨2239199, by rfl⟩ : syracuseStep 2985599 = 4478399) B4478399
theorem B2519527 : Blo 1178406 2519527 := bstep (se 1 (by rfl) ⟨1889645, by rfl⟩ : syracuseStep 2519527 = 3779291) B3779291
theorem B6713999 : Blo 1178406 6713999 := bstep (se 1 (by rfl) ⟨5035499, by rfl⟩ : syracuseStep 6713999 = 10070999) B10070999
theorem B1990649 : Blo 1178406 1990649 := bstep (se 2 (by rfl) ⟨746493, by rfl⟩ : syracuseStep 1990649 = 1492987) B1492987
theorem B1988671 : Blo 1178406 1988671 := bstep (se 1 (by rfl) ⟨1491503, by rfl⟩ : syracuseStep 1988671 = 2983007) B2983007
theorem B588675883 : Blo 1178406 588675883 := bstep (se 1 (by rfl) ⟨441506912, by rfl⟩ : syracuseStep 588675883 = 883013825) B883013825
theorem B1768391 : Blo 1178406 1768391 := bstep (se 1 (by rfl) ⟨1326293, by rfl⟩ : syracuseStep 1768391 = 2652587) B2652587
theorem B4251473 : Blo 1178406 4251473 := bstep (se 2 (by rfl) ⟨1594302, by rfl⟩ : syracuseStep 4251473 = 3188605) B3188605
theorem B13426721 : Blo 1178406 13426721 := bstep (se 2 (by rfl) ⟨5035020, by rfl⟩ : syracuseStep 13426721 = 10070041) B10070041
theorem B1179719 : Blo 1178406 1179719 := bstep (se 1 (by rfl) ⟨884789, by rfl⟩ : syracuseStep 1179719 = 1769579) B1769579
theorem B1179759 : Blo 1178406 1179759 := bstep (se 1 (by rfl) ⟨884819, by rfl⟩ : syracuseStep 1179759 = 1769639) B1769639
theorem B1769723 : Blo 1178406 1769723 := bstep (se 1 (by rfl) ⟨1327292, by rfl⟩ : syracuseStep 1769723 = 2654585) B2654585
theorem B1327423 : Blo 1178406 1327423 := bstep (se 1 (by rfl) ⟨995567, by rfl⟩ : syracuseStep 1327423 = 1991135) B1991135
theorem B1327099 : Blo 1178406 1327099 := bstep (se 1 (by rfl) ⟨995324, by rfl⟩ : syracuseStep 1327099 = 1990649) B1990649
theorem B3359369 : Blo 1178406 3359369 := bstep (se 2 (by rfl) ⟨1259763, by rfl⟩ : syracuseStep 3359369 = 2519527) B2519527
theorem B784901177 : Blo 1178406 784901177 := bstep (se 2 (by rfl) ⟨294337941, by rfl⟩ : syracuseStep 784901177 = 588675883) B588675883
theorem B1492607 : Blo 1178406 1492607 := bstep (se 1 (by rfl) ⟨1119455, by rfl⟩ : syracuseStep 1492607 = 2238911) B2238911
theorem B15533927 : Blo 1178406 15533927 := bstep (se 1 (by rfl) ⟨11650445, by rfl⟩ : syracuseStep 15533927 = 23300891) B23300891
theorem B13436927 : Blo 1178406 13436927 := bstep (se 1 (by rfl) ⟨10077695, by rfl⟩ : syracuseStep 13436927 = 20155391) B20155391
theorem B4475999 : Blo 1178406 4475999 := bstep (se 1 (by rfl) ⟨3356999, by rfl⟩ : syracuseStep 4475999 = 6713999) B6713999
theorem B6713725 : Blo 1178406 6713725 := bstep (se 3 (by rfl) ⟨1258823, by rfl⟩ : syracuseStep 6713725 = 2517647) B2517647
theorem B2651561 : Blo 1178406 2651561 := bstep (se 2 (by rfl) ⟨994335, by rfl⟩ : syracuseStep 2651561 = 1988671) B1988671
theorem B5970347 : Blo 1178406 5970347 := bstep (se 1 (by rfl) ⟨4477760, by rfl⟩ : syracuseStep 5970347 = 8955521) B8955521
theorem B13425263 : Blo 1178406 13425263 := bstep (se 1 (by rfl) ⟨10068947, by rfl⟩ : syracuseStep 13425263 = 20137895) B20137895
theorem B1178927 : Blo 1178406 1178927 := bstep (se 1 (by rfl) ⟨884195, by rfl⟩ : syracuseStep 1178927 = 1768391) B1768391
theorem B1990399 : Blo 1178406 1990399 := bstep (se 1 (by rfl) ⟨1492799, by rfl⟩ : syracuseStep 1990399 = 2985599) B2985599
theorem B2834315 : Blo 1178406 2834315 := bstep (se 1 (by rfl) ⟨2125736, by rfl⟩ : syracuseStep 2834315 = 4251473) B4251473
theorem B1179815 : Blo 1178406 1179815 := bstep (se 1 (by rfl) ⟨884861, by rfl⟩ : syracuseStep 1179815 = 1769723) B1769723
theorem B1769897 : Blo 1178406 1769897 := bstep (se 2 (by rfl) ⟨663711, by rfl⟩ : syracuseStep 1769897 = 1327423) B1327423
theorem B10355951 : Blo 1178406 10355951 := bstep (se 1 (by rfl) ⟨7766963, by rfl⟩ : syracuseStep 10355951 = 15533927) B15533927
theorem B2983999 : Blo 1178406 2983999 := bstep (se 1 (by rfl) ⟨2237999, by rfl⟩ : syracuseStep 2983999 = 4475999) B4475999
theorem B2239579 : Blo 1178406 2239579 := bstep (se 1 (by rfl) ⟨1679684, by rfl⟩ : syracuseStep 2239579 = 3359369) B3359369
theorem B523267451 : Blo 1178406 523267451 := bstep (se 1 (by rfl) ⟨392450588, by rfl⟩ : syracuseStep 523267451 = 784901177) B784901177
theorem B8957951 : Blo 1178406 8957951 := bstep (se 1 (by rfl) ⟨6718463, by rfl⟩ : syracuseStep 8957951 = 13436927) B13436927
theorem B8950175 : Blo 1178406 8950175 := bstep (se 1 (by rfl) ⟨6712631, by rfl⟩ : syracuseStep 8950175 = 13425263) B13425263
theorem B1889543 : Blo 1178406 1889543 := bstep (se 1 (by rfl) ⟨1417157, by rfl⟩ : syracuseStep 1889543 = 2834315) B2834315
theorem B8951147 : Blo 1178406 8951147 := bstep (se 1 (by rfl) ⟨6713360, by rfl⟩ : syracuseStep 8951147 = 13426721) B13426721
theorem B8951633 : Blo 1178406 8951633 := bstep (se 2 (by rfl) ⟨3356862, by rfl⟩ : syracuseStep 8951633 = 6713725) B6713725
theorem B1767707 : Blo 1178406 1767707 := bstep (se 1 (by rfl) ⟨1325780, by rfl⟩ : syracuseStep 1767707 = 2651561) B2651561
theorem B3980231 : Blo 1178406 3980231 := bstep (se 1 (by rfl) ⟨2985173, by rfl⟩ : syracuseStep 3980231 = 5970347) B5970347
theorem B3980285 : Blo 1178406 3980285 := bstep (se 3 (by rfl) ⟨746303, by rfl⟩ : syracuseStep 3980285 = 1492607) B1492607
theorem B2653865 : Blo 1178406 2653865 := bstep (se 2 (by rfl) ⟨995199, by rfl⟩ : syracuseStep 2653865 = 1990399) B1990399
theorem B1769465 : Blo 1178406 1769465 := bstep (se 2 (by rfl) ⟨663549, by rfl⟩ : syracuseStep 1769465 = 1327099) B1327099
theorem B1179931 : Blo 1178406 1179931 := bstep (se 1 (by rfl) ⟨884948, by rfl⟩ : syracuseStep 1179931 = 1769897) B1769897
theorem B5966783 : Blo 1178406 5966783 := bstep (se 1 (by rfl) ⟨4475087, by rfl⟩ : syracuseStep 5966783 = 8950175) B8950175
theorem B5967431 : Blo 1178406 5967431 := bstep (se 1 (by rfl) ⟨4475573, by rfl⟩ : syracuseStep 5967431 = 8951147) B8951147
theorem B5967755 : Blo 1178406 5967755 := bstep (se 1 (by rfl) ⟨4475816, by rfl⟩ : syracuseStep 5967755 = 8951633) B8951633
theorem B2986105 : Blo 1178406 2986105 := bstep (se 2 (by rfl) ⟨1119789, by rfl⟩ : syracuseStep 2986105 = 2239579) B2239579
theorem B348844967 : Blo 1178406 348844967 := bstep (se 1 (by rfl) ⟨261633725, by rfl⟩ : syracuseStep 348844967 = 523267451) B523267451
theorem B3978665 : Blo 1178406 3978665 := bstep (se 2 (by rfl) ⟨1491999, by rfl⟩ : syracuseStep 3978665 = 2983999) B2983999
theorem B6903967 : Blo 1178406 6903967 := bstep (se 1 (by rfl) ⟨5177975, by rfl⟩ : syracuseStep 6903967 = 10355951) B10355951
theorem B1259695 : Blo 1178406 1259695 := bstep (se 1 (by rfl) ⟨944771, by rfl⟩ : syracuseStep 1259695 = 1889543) B1889543
theorem B5971967 : Blo 1178406 5971967 := bstep (se 1 (by rfl) ⟨4478975, by rfl⟩ : syracuseStep 5971967 = 8957951) B8957951
theorem B1178471 : Blo 1178406 1178471 := bstep (se 1 (by rfl) ⟨883853, by rfl⟩ : syracuseStep 1178471 = 1767707) B1767707
theorem B2653487 : Blo 1178406 2653487 := bstep (se 1 (by rfl) ⟨1990115, by rfl⟩ : syracuseStep 2653487 = 3980231) B3980231
theorem B2653523 : Blo 1178406 2653523 := bstep (se 1 (by rfl) ⟨1990142, by rfl⟩ : syracuseStep 2653523 = 3980285) B3980285
theorem B1769243 : Blo 1178406 1769243 := bstep (se 1 (by rfl) ⟨1326932, by rfl⟩ : syracuseStep 1769243 = 2653865) B2653865
theorem B1179643 : Blo 1178406 1179643 := bstep (se 1 (by rfl) ⟨884732, by rfl⟩ : syracuseStep 1179643 = 1769465) B1769465
theorem B3981473 : Blo 1178406 3981473 := bstep (se 2 (by rfl) ⟨1493052, by rfl⟩ : syracuseStep 3981473 = 2986105) B2986105
theorem B232563311 : Blo 1178406 232563311 := bstep (se 1 (by rfl) ⟨174422483, by rfl⟩ : syracuseStep 232563311 = 348844967) B348844967
theorem B6718373 : Blo 1178406 6718373 := bstep (se 4 (by rfl) ⟨629847, by rfl⟩ : syracuseStep 6718373 = 1259695) B1259695
theorem B3981311 : Blo 1178406 3981311 := bstep (se 1 (by rfl) ⟨2985983, by rfl⟩ : syracuseStep 3981311 = 5971967) B5971967
theorem B3977855 : Blo 1178406 3977855 := bstep (se 1 (by rfl) ⟨2983391, by rfl⟩ : syracuseStep 3977855 = 5966783) B5966783
theorem B3978287 : Blo 1178406 3978287 := bstep (se 1 (by rfl) ⟨2983715, by rfl⟩ : syracuseStep 3978287 = 5967431) B5967431
theorem B3978503 : Blo 1178406 3978503 := bstep (se 1 (by rfl) ⟨2983877, by rfl⟩ : syracuseStep 3978503 = 5967755) B5967755
theorem B9205289 : Blo 1178406 9205289 := bstep (se 2 (by rfl) ⟨3451983, by rfl⟩ : syracuseStep 9205289 = 6903967) B6903967
theorem B2652443 : Blo 1178406 2652443 := bstep (se 1 (by rfl) ⟨1989332, by rfl⟩ : syracuseStep 2652443 = 3978665) B3978665
theorem B1768991 : Blo 1178406 1768991 := bstep (se 1 (by rfl) ⟨1326743, by rfl⟩ : syracuseStep 1768991 = 2653487) B2653487
theorem B1769015 : Blo 1178406 1769015 := bstep (se 1 (by rfl) ⟨1326761, by rfl⟩ : syracuseStep 1769015 = 2653523) B2653523
theorem B1179495 : Blo 1178406 1179495 := bstep (se 1 (by rfl) ⟨884621, by rfl⟩ : syracuseStep 1179495 = 1769243) B1769243
theorem B2654315 : Blo 1178406 2654315 := bstep (se 1 (by rfl) ⟨1990736, by rfl⟩ : syracuseStep 2654315 = 3981473) B3981473
theorem B155042207 : Blo 1178406 155042207 := bstep (se 1 (by rfl) ⟨116281655, by rfl⟩ : syracuseStep 155042207 = 232563311) B232563311
theorem B2654207 : Blo 1178406 2654207 := bstep (se 1 (by rfl) ⟨1990655, by rfl⟩ : syracuseStep 2654207 = 3981311) B3981311
theorem B6136859 : Blo 1178406 6136859 := bstep (se 1 (by rfl) ⟨4602644, by rfl⟩ : syracuseStep 6136859 = 9205289) B9205289
theorem B2651903 : Blo 1178406 2651903 := bstep (se 1 (by rfl) ⟨1988927, by rfl⟩ : syracuseStep 2651903 = 3977855) B3977855
theorem B4478915 : Blo 1178406 4478915 := bstep (se 1 (by rfl) ⟨3359186, by rfl⟩ : syracuseStep 4478915 = 6718373) B6718373
theorem B2652191 : Blo 1178406 2652191 := bstep (se 1 (by rfl) ⟨1989143, by rfl⟩ : syracuseStep 2652191 = 3978287) B3978287
theorem B2652335 : Blo 1178406 2652335 := bstep (se 1 (by rfl) ⟨1989251, by rfl⟩ : syracuseStep 2652335 = 3978503) B3978503
theorem B1768295 : Blo 1178406 1768295 := bstep (se 1 (by rfl) ⟨1326221, by rfl⟩ : syracuseStep 1768295 = 2652443) B2652443
theorem B1179327 : Blo 1178406 1179327 := bstep (se 1 (by rfl) ⟨884495, by rfl⟩ : syracuseStep 1179327 = 1768991) B1768991
theorem B1179343 : Blo 1178406 1179343 := bstep (se 1 (by rfl) ⟨884507, by rfl⟩ : syracuseStep 1179343 = 1769015) B1769015
theorem B1769543 : Blo 1178406 1769543 := bstep (se 1 (by rfl) ⟨1327157, by rfl⟩ : syracuseStep 1769543 = 2654315) B2654315
theorem B103361471 : Blo 1178406 103361471 := bstep (se 1 (by rfl) ⟨77521103, by rfl⟩ : syracuseStep 103361471 = 155042207) B155042207
theorem B4091239 : Blo 1178406 4091239 := bstep (se 1 (by rfl) ⟨3068429, by rfl⟩ : syracuseStep 4091239 = 6136859) B6136859
theorem B2985943 : Blo 1178406 2985943 := bstep (se 1 (by rfl) ⟨2239457, by rfl⟩ : syracuseStep 2985943 = 4478915) B4478915
theorem B1769471 : Blo 1178406 1769471 := bstep (se 1 (by rfl) ⟨1327103, by rfl⟩ : syracuseStep 1769471 = 2654207) B2654207
theorem B1767935 : Blo 1178406 1767935 := bstep (se 1 (by rfl) ⟨1325951, by rfl⟩ : syracuseStep 1767935 = 2651903) B2651903
theorem B1768127 : Blo 1178406 1768127 := bstep (se 1 (by rfl) ⟨1326095, by rfl⟩ : syracuseStep 1768127 = 2652191) B2652191
theorem B1768223 : Blo 1178406 1768223 := bstep (se 1 (by rfl) ⟨1326167, by rfl⟩ : syracuseStep 1768223 = 2652335) B2652335
theorem B1178863 : Blo 1178406 1178863 := bstep (se 1 (by rfl) ⟨884147, by rfl⟩ : syracuseStep 1178863 = 1768295) B1768295
theorem B1179695 : Blo 1178406 1179695 := bstep (se 1 (by rfl) ⟨884771, by rfl⟩ : syracuseStep 1179695 = 1769543) B1769543
theorem B21819941 : Blo 1178406 21819941 := bstep (se 4 (by rfl) ⟨2045619, by rfl⟩ : syracuseStep 21819941 = 4091239) B4091239
theorem B68907647 : Blo 1178406 68907647 := bstep (se 1 (by rfl) ⟨51680735, by rfl⟩ : syracuseStep 68907647 = 103361471) B103361471
theorem B1178623 : Blo 1178406 1178623 := bstep (se 1 (by rfl) ⟨883967, by rfl⟩ : syracuseStep 1178623 = 1767935) B1767935
theorem B1178751 : Blo 1178406 1178751 := bstep (se 1 (by rfl) ⟨884063, by rfl⟩ : syracuseStep 1178751 = 1768127) B1768127
theorem B1178815 : Blo 1178406 1178815 := bstep (se 1 (by rfl) ⟨884111, by rfl⟩ : syracuseStep 1178815 = 1768223) B1768223
theorem B3981257 : Blo 1178406 3981257 := bstep (se 2 (by rfl) ⟨1492971, by rfl⟩ : syracuseStep 3981257 = 2985943) B2985943
theorem B1179647 : Blo 1178406 1179647 := bstep (se 1 (by rfl) ⟨884735, by rfl⟩ : syracuseStep 1179647 = 1769471) B1769471
theorem B14546627 : Blo 1178406 14546627 := bstep (se 1 (by rfl) ⟨10909970, by rfl⟩ : syracuseStep 14546627 = 21819941) B21819941
theorem B45938431 : Blo 1178406 45938431 := bstep (se 1 (by rfl) ⟨34453823, by rfl⟩ : syracuseStep 45938431 = 68907647) B68907647
theorem B2654171 : Blo 1178406 2654171 := bstep (se 1 (by rfl) ⟨1990628, by rfl⟩ : syracuseStep 2654171 = 3981257) B3981257
theorem B9697751 : Blo 1178406 9697751 := bstep (se 1 (by rfl) ⟨7273313, by rfl⟩ : syracuseStep 9697751 = 14546627) B14546627
theorem B61251241 : Blo 1178406 61251241 := bstep (se 2 (by rfl) ⟨22969215, by rfl⟩ : syracuseStep 61251241 = 45938431) B45938431
theorem B1769447 : Blo 1178406 1769447 := bstep (se 1 (by rfl) ⟨1327085, by rfl⟩ : syracuseStep 1769447 = 2654171) B2654171
theorem B6465167 : Blo 1178406 6465167 := bstep (se 1 (by rfl) ⟨4848875, by rfl⟩ : syracuseStep 6465167 = 9697751) B9697751
theorem B81668321 : Blo 1178406 81668321 := bstep (se 2 (by rfl) ⟨30625620, by rfl⟩ : syracuseStep 81668321 = 61251241) B61251241
theorem B1179631 : Blo 1178406 1179631 := bstep (se 1 (by rfl) ⟨884723, by rfl⟩ : syracuseStep 1179631 = 1769447) B1769447
theorem B4310111 : Blo 1178406 4310111 := bstep (se 1 (by rfl) ⟨3232583, by rfl⟩ : syracuseStep 4310111 = 6465167) B6465167
theorem B54445547 : Blo 1178406 54445547 := bstep (se 1 (by rfl) ⟨40834160, by rfl⟩ : syracuseStep 54445547 = 81668321) B81668321
theorem B2873407 : Blo 1178406 2873407 := bstep (se 1 (by rfl) ⟨2155055, by rfl⟩ : syracuseStep 2873407 = 4310111) B4310111
theorem B36297031 : Blo 1178406 36297031 := bstep (se 1 (by rfl) ⟨27222773, by rfl⟩ : syracuseStep 36297031 = 54445547) B54445547
theorem B3831209 : Blo 1178406 3831209 := bstep (se 2 (by rfl) ⟨1436703, by rfl⟩ : syracuseStep 3831209 = 2873407) B2873407
theorem B48396041 : Blo 1178406 48396041 := bstep (se 2 (by rfl) ⟨18148515, by rfl⟩ : syracuseStep 48396041 = 36297031) B36297031
theorem B32264027 : Blo 1178406 32264027 := bstep (se 1 (by rfl) ⟨24198020, by rfl⟩ : syracuseStep 32264027 = 48396041) B48396041
theorem B2554139 : Blo 1178406 2554139 := bstep (se 1 (by rfl) ⟨1915604, by rfl⟩ : syracuseStep 2554139 = 3831209) B3831209
theorem B6811037 : Blo 1178406 6811037 := bstep (se 3 (by rfl) ⟨1277069, by rfl⟩ : syracuseStep 6811037 = 2554139) B2554139
theorem B21509351 : Blo 1178406 21509351 := bstep (se 1 (by rfl) ⟨16132013, by rfl⟩ : syracuseStep 21509351 = 32264027) B32264027
theorem B4540691 : Blo 1178406 4540691 := bstep (se 1 (by rfl) ⟨3405518, by rfl⟩ : syracuseStep 4540691 = 6811037) B6811037
theorem B14339567 : Blo 1178406 14339567 := bstep (se 1 (by rfl) ⟨10754675, by rfl⟩ : syracuseStep 14339567 = 21509351) B21509351
theorem B3027127 : Blo 1178406 3027127 := bstep (se 1 (by rfl) ⟨2270345, by rfl⟩ : syracuseStep 3027127 = 4540691) B4540691
theorem B9559711 : Blo 1178406 9559711 := bstep (se 1 (by rfl) ⟨7169783, by rfl⟩ : syracuseStep 9559711 = 14339567) B14339567
theorem B4036169 : Blo 1178406 4036169 := bstep (se 2 (by rfl) ⟨1513563, by rfl⟩ : syracuseStep 4036169 = 3027127) B3027127
theorem B12746281 : Blo 1178406 12746281 := bstep (se 2 (by rfl) ⟨4779855, by rfl⟩ : syracuseStep 12746281 = 9559711) B9559711
theorem B16995041 : Blo 1178406 16995041 := bstep (se 2 (by rfl) ⟨6373140, by rfl⟩ : syracuseStep 16995041 = 12746281) B12746281
theorem B10763117 : Blo 1178406 10763117 := bstep (se 3 (by rfl) ⟨2018084, by rfl⟩ : syracuseStep 10763117 = 4036169) B4036169
theorem B11330027 : Blo 1178406 11330027 := bstep (se 1 (by rfl) ⟨8497520, by rfl⟩ : syracuseStep 11330027 = 16995041) B16995041
theorem B7175411 : Blo 1178406 7175411 := bstep (se 1 (by rfl) ⟨5381558, by rfl⟩ : syracuseStep 7175411 = 10763117) B10763117
theorem B7553351 : Blo 1178406 7553351 := bstep (se 1 (by rfl) ⟨5665013, by rfl⟩ : syracuseStep 7553351 = 11330027) B11330027
theorem B4783607 : Blo 1178406 4783607 := bstep (se 1 (by rfl) ⟨3587705, by rfl⟩ : syracuseStep 4783607 = 7175411) B7175411
theorem B3189071 : Blo 1178406 3189071 := bstep (se 1 (by rfl) ⟨2391803, by rfl⟩ : syracuseStep 3189071 = 4783607) B4783607
theorem B20142269 : Blo 1178406 20142269 := bstep (se 3 (by rfl) ⟨3776675, by rfl⟩ : syracuseStep 20142269 = 7553351) B7553351
theorem B13428179 : Blo 1178406 13428179 := bstep (se 1 (by rfl) ⟨10071134, by rfl⟩ : syracuseStep 13428179 = 20142269) B20142269
theorem B2126047 : Blo 1178406 2126047 := bstep (se 1 (by rfl) ⟨1594535, by rfl⟩ : syracuseStep 2126047 = 3189071) B3189071
theorem B2834729 : Blo 1178406 2834729 := bstep (se 2 (by rfl) ⟨1063023, by rfl⟩ : syracuseStep 2834729 = 2126047) B2126047
theorem B8952119 : Blo 1178406 8952119 := bstep (se 1 (by rfl) ⟨6714089, by rfl⟩ : syracuseStep 8952119 = 13428179) B13428179
theorem B5968079 : Blo 1178406 5968079 := bstep (se 1 (by rfl) ⟨4476059, by rfl⟩ : syracuseStep 5968079 = 8952119) B8952119
theorem B1889819 : Blo 1178406 1889819 := bstep (se 1 (by rfl) ⟨1417364, by rfl⟩ : syracuseStep 1889819 = 2834729) B2834729
theorem B3978719 : Blo 1178406 3978719 := bstep (se 1 (by rfl) ⟨2984039, by rfl⟩ : syracuseStep 3978719 = 5968079) B5968079
theorem B1259879 : Blo 1178406 1259879 := bstep (se 1 (by rfl) ⟨944909, by rfl⟩ : syracuseStep 1259879 = 1889819) B1889819
theorem B3359677 : Blo 1178406 3359677 := bstep (se 3 (by rfl) ⟨629939, by rfl⟩ : syracuseStep 3359677 = 1259879) B1259879
theorem B2652479 : Blo 1178406 2652479 := bstep (se 1 (by rfl) ⟨1989359, by rfl⟩ : syracuseStep 2652479 = 3978719) B3978719
theorem B4479569 : Blo 1178406 4479569 := bstep (se 2 (by rfl) ⟨1679838, by rfl⟩ : syracuseStep 4479569 = 3359677) B3359677
theorem B1768319 : Blo 1178406 1768319 := bstep (se 1 (by rfl) ⟨1326239, by rfl⟩ : syracuseStep 1768319 = 2652479) B2652479
theorem B2986379 : Blo 1178406 2986379 := bstep (se 1 (by rfl) ⟨2239784, by rfl⟩ : syracuseStep 2986379 = 4479569) B4479569
theorem B1178879 : Blo 1178406 1178879 := bstep (se 1 (by rfl) ⟨884159, by rfl⟩ : syracuseStep 1178879 = 1768319) B1768319
theorem B1990919 : Blo 1178406 1990919 := bstep (se 1 (by rfl) ⟨1493189, by rfl⟩ : syracuseStep 1990919 = 2986379) B2986379
theorem B1327279 : Blo 1178406 1327279 := bstep (se 1 (by rfl) ⟨995459, by rfl⟩ : syracuseStep 1327279 = 1990919) B1990919
theorem B1769705 : Blo 1178406 1769705 := bstep (se 2 (by rfl) ⟨663639, by rfl⟩ : syracuseStep 1769705 = 1327279) B1327279
theorem B1179803 : Blo 1178406 1179803 := bstep (se 1 (by rfl) ⟨884852, by rfl⟩ : syracuseStep 1179803 = 1769705) B1769705

theorem C0 (j : ℕ) (h1 : 294601 ≤ j) (h2 : j ≤ 295100) : Blo 1178406 (4 * j + 3) := by
  interval_cases j
  · exact B1178407
  · exact B1178411
  · exact B1178415
  · exact B1178419
  · exact B1178423
  · exact B1178427
  · exact B1178431
  · exact B1178435
  · exact B1178439
  · exact B1178443
  · exact B1178447
  · exact B1178451
  · exact B1178455
  · exact B1178459
  · exact B1178463
  · exact B1178467
  · exact B1178471
  · exact B1178475
  · exact B1178479
  · exact B1178483
  · exact B1178487
  · exact B1178491
  · exact B1178495
  · exact B1178499
  · exact B1178503
  · exact B1178507
  · exact B1178511
  · exact B1178515
  · exact B1178519
  · exact B1178523
  · exact B1178527
  · exact B1178531
  · exact B1178535
  · exact B1178539
  · exact B1178543
  · exact B1178547
  · exact B1178551
  · exact B1178555
  · exact B1178559
  · exact B1178563
  · exact B1178567
  · exact B1178571
  · exact B1178575
  · exact B1178579
  · exact B1178583
  · exact B1178587
  · exact B1178591
  · exact B1178595
  · exact B1178599
  · exact B1178603
  · exact B1178607
  · exact B1178611
  · exact B1178615
  · exact B1178619
  · exact B1178623
  · exact B1178627
  · exact B1178631
  · exact B1178635
  · exact B1178639
  · exact B1178643
  · exact B1178647
  · exact B1178651
  · exact B1178655
  · exact B1178659
  · exact B1178663
  · exact B1178667
  · exact B1178671
  · exact B1178675
  · exact B1178679
  · exact B1178683
  · exact B1178687
  · exact B1178691
  · exact B1178695
  · exact B1178699
  · exact B1178703
  · exact B1178707
  · exact B1178711
  · exact B1178715
  · exact B1178719
  · exact B1178723
  · exact B1178727
  · exact B1178731
  · exact B1178735
  · exact B1178739
  · exact B1178743
  · exact B1178747
  · exact B1178751
  · exact B1178755
  · exact B1178759
  · exact B1178763
  · exact B1178767
  · exact B1178771
  · exact B1178775
  · exact B1178779
  · exact B1178783
  · exact B1178787
  · exact B1178791
  · exact B1178795
  · exact B1178799
  · exact B1178803
  · exact B1178807
  · exact B1178811
  · exact B1178815
  · exact B1178819
  · exact B1178823
  · exact B1178827
  · exact B1178831
  · exact B1178835
  · exact B1178839
  · exact B1178843
  · exact B1178847
  · exact B1178851
  · exact B1178855
  · exact B1178859
  · exact B1178863
  · exact B1178867
  · exact B1178871
  · exact B1178875
  · exact B1178879
  · exact B1178883
  · exact B1178887
  · exact B1178891
  · exact B1178895
  · exact B1178899
  · exact B1178903
  · exact B1178907
  · exact B1178911
  · exact B1178915
  · exact B1178919
  · exact B1178923
  · exact B1178927
  · exact B1178931
  · exact B1178935
  · exact B1178939
  · exact B1178943
  · exact B1178947
  · exact B1178951
  · exact B1178955
  · exact B1178959
  · exact B1178963
  · exact B1178967
  · exact B1178971
  · exact B1178975
  · exact B1178979
  · exact B1178983
  · exact B1178987
  · exact B1178991
  · exact B1178995
  · exact B1178999
  · exact B1179003
  · exact B1179007
  · exact B1179011
  · exact B1179015
  · exact B1179019
  · exact B1179023
  · exact B1179027
  · exact B1179031
  · exact B1179035
  · exact B1179039
  · exact B1179043
  · exact B1179047
  · exact B1179051
  · exact B1179055
  · exact B1179059
  · exact B1179063
  · exact B1179067
  · exact B1179071
  · exact B1179075
  · exact B1179079
  · exact B1179083
  · exact B1179087
  · exact B1179091
  · exact B1179095
  · exact B1179099
  · exact B1179103
  · exact B1179107
  · exact B1179111
  · exact B1179115
  · exact B1179119
  · exact B1179123
  · exact B1179127
  · exact B1179131
  · exact B1179135
  · exact B1179139
  · exact B1179143
  · exact B1179147
  · exact B1179151
  · exact B1179155
  · exact B1179159
  · exact B1179163
  · exact B1179167
  · exact B1179171
  · exact B1179175
  · exact B1179179
  · exact B1179183
  · exact B1179187
  · exact B1179191
  · exact B1179195
  · exact B1179199
  · exact B1179203
  · exact B1179207
  · exact B1179211
  · exact B1179215
  · exact B1179219
  · exact B1179223
  · exact B1179227
  · exact B1179231
  · exact B1179235
  · exact B1179239
  · exact B1179243
  · exact B1179247
  · exact B1179251
  · exact B1179255
  · exact B1179259
  · exact B1179263
  · exact B1179267
  · exact B1179271
  · exact B1179275
  · exact B1179279
  · exact B1179283
  · exact B1179287
  · exact B1179291
  · exact B1179295
  · exact B1179299
  · exact B1179303
  · exact B1179307
  · exact B1179311
  · exact B1179315
  · exact B1179319
  · exact B1179323
  · exact B1179327
  · exact B1179331
  · exact B1179335
  · exact B1179339
  · exact B1179343
  · exact B1179347
  · exact B1179351
  · exact B1179355
  · exact B1179359
  · exact B1179363
  · exact B1179367
  · exact B1179371
  · exact B1179375
  · exact B1179379
  · exact B1179383
  · exact B1179387
  · exact B1179391
  · exact B1179395
  · exact B1179399
  · exact B1179403
  · exact B1179407
  · exact B1179411
  · exact B1179415
  · exact B1179419
  · exact B1179423
  · exact B1179427
  · exact B1179431
  · exact B1179435
  · exact B1179439
  · exact B1179443
  · exact B1179447
  · exact B1179451
  · exact B1179455
  · exact B1179459
  · exact B1179463
  · exact B1179467
  · exact B1179471
  · exact B1179475
  · exact B1179479
  · exact B1179483
  · exact B1179487
  · exact B1179491
  · exact B1179495
  · exact B1179499
  · exact B1179503
  · exact B1179507
  · exact B1179511
  · exact B1179515
  · exact B1179519
  · exact B1179523
  · exact B1179527
  · exact B1179531
  · exact B1179535
  · exact B1179539
  · exact B1179543
  · exact B1179547
  · exact B1179551
  · exact B1179555
  · exact B1179559
  · exact B1179563
  · exact B1179567
  · exact B1179571
  · exact B1179575
  · exact B1179579
  · exact B1179583
  · exact B1179587
  · exact B1179591
  · exact B1179595
  · exact B1179599
  · exact B1179603
  · exact B1179607
  · exact B1179611
  · exact B1179615
  · exact B1179619
  · exact B1179623
  · exact B1179627
  · exact B1179631
  · exact B1179635
  · exact B1179639
  · exact B1179643
  · exact B1179647
  · exact B1179651
  · exact B1179655
  · exact B1179659
  · exact B1179663
  · exact B1179667
  · exact B1179671
  · exact B1179675
  · exact B1179679
  · exact B1179683
  · exact B1179687
  · exact B1179691
  · exact B1179695
  · exact B1179699
  · exact B1179703
  · exact B1179707
  · exact B1179711
  · exact B1179715
  · exact B1179719
  · exact B1179723
  · exact B1179727
  · exact B1179731
  · exact B1179735
  · exact B1179739
  · exact B1179743
  · exact B1179747
  · exact B1179751
  · exact B1179755
  · exact B1179759
  · exact B1179763
  · exact B1179767
  · exact B1179771
  · exact B1179775
  · exact B1179779
  · exact B1179783
  · exact B1179787
  · exact B1179791
  · exact B1179795
  · exact B1179799
  · exact B1179803
  · exact B1179807
  · exact B1179811
  · exact B1179815
  · exact B1179819
  · exact B1179823
  · exact B1179827
  · exact B1179831
  · exact B1179835
  · exact B1179839
  · exact B1179843
  · exact B1179847
  · exact B1179851
  · exact B1179855
  · exact B1179859
  · exact B1179863
  · exact B1179867
  · exact B1179871
  · exact B1179875
  · exact B1179879
  · exact B1179883
  · exact B1179887
  · exact B1179891
  · exact B1179895
  · exact B1179899
  · exact B1179903
  · exact B1179907
  · exact B1179911
  · exact B1179915
  · exact B1179919
  · exact B1179923
  · exact B1179927
  · exact B1179931
  · exact B1179935
  · exact B1179939
  · exact B1179943
  · exact B1179947
  · exact B1179951
  · exact B1179955
  · exact B1179959
  · exact B1179963
  · exact B1179967
  · exact B1179971
  · exact B1179975
  · exact B1179979
  · exact B1179983
  · exact B1179987
  · exact B1179991
  · exact B1179995
  · exact B1179999
  · exact B1180003
  · exact B1180007
  · exact B1180011
  · exact B1180015
  · exact B1180019
  · exact B1180023
  · exact B1180027
  · exact B1180031
  · exact B1180035
  · exact B1180039
  · exact B1180043
  · exact B1180047
  · exact B1180051
  · exact B1180055
  · exact B1180059
  · exact B1180063
  · exact B1180067
  · exact B1180071
  · exact B1180075
  · exact B1180079
  · exact B1180083
  · exact B1180087
  · exact B1180091
  · exact B1180095
  · exact B1180099
  · exact B1180103
  · exact B1180107
  · exact B1180111
  · exact B1180115
  · exact B1180119
  · exact B1180123
  · exact B1180127
  · exact B1180131
  · exact B1180135
  · exact B1180139
  · exact B1180143
  · exact B1180147
  · exact B1180151
  · exact B1180155
  · exact B1180159
  · exact B1180163
  · exact B1180167
  · exact B1180171
  · exact B1180175
  · exact B1180179
  · exact B1180183
  · exact B1180187
  · exact B1180191
  · exact B1180195
  · exact B1180199
  · exact B1180203
  · exact B1180207
  · exact B1180211
  · exact B1180215
  · exact B1180219
  · exact B1180223
  · exact B1180227
  · exact B1180231
  · exact B1180235
  · exact B1180239
  · exact B1180243
  · exact B1180247
  · exact B1180251
  · exact B1180255
  · exact B1180259
  · exact B1180263
  · exact B1180267
  · exact B1180271
  · exact B1180275
  · exact B1180279
  · exact B1180283
  · exact B1180287
  · exact B1180291
  · exact B1180295
  · exact B1180299
  · exact B1180303
  · exact B1180307
  · exact B1180311
  · exact B1180315
  · exact B1180319
  · exact B1180323
  · exact B1180327
  · exact B1180331
  · exact B1180335
  · exact B1180339
  · exact B1180343
  · exact B1180347
  · exact B1180351
  · exact B1180355
  · exact B1180359
  · exact B1180363
  · exact B1180367
  · exact B1180371
  · exact B1180375
  · exact B1180379
  · exact B1180383
  · exact B1180387
  · exact B1180391
  · exact B1180395
  · exact B1180399
  · exact B1180403

theorem solution (m : ℕ) (hlo : 1178406 ≤ m) (hhi : m ≤ 1180406) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 294601 ≤ j := by omega
    have hj2 : j ≤ 295100 := by omega
    have hb : Blo 1178406 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
