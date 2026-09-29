-- Prove2me | solution 1 for syracuse_descends_range_1598998_1600998
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:10:33.25115+00:00
-- url     : https://prove2.me/submissions/3624156a-2ee6-4227-bfd9-97df7878d45f

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


theorem B2400269 : Blo 1598998 2400269 := bbase (se 3 (by rfl) ⟨450050, by rfl⟩ : syracuseStep 2400269 = 900101) (by norm_num)
theorem B7299109 : Blo 1598998 7299109 := bbase (se 4 (by rfl) ⟨684291, by rfl⟩ : syracuseStep 7299109 = 1368583) (by norm_num)
theorem B2400293 : Blo 1598998 2400293 := bbase (se 4 (by rfl) ⟨225027, by rfl⟩ : syracuseStep 2400293 = 450055) (by norm_num)
theorem B3039277 : Blo 1598998 3039277 := bbase (se 3 (by rfl) ⟨569864, by rfl⟩ : syracuseStep 3039277 = 1139729) (by norm_num)
theorem B2736181 : Blo 1598998 2736181 := bbase (se 5 (by rfl) ⟨128258, by rfl⟩ : syracuseStep 2736181 = 256517) (by norm_num)
theorem B2400317 : Blo 1598998 2400317 := bbase (se 3 (by rfl) ⟨450059, by rfl⟩ : syracuseStep 2400317 = 900119) (by norm_num)
theorem B1622089 : Blo 1598998 1622089 := bbase (se 2 (by rfl) ⟨608283, by rfl⟩ : syracuseStep 1622089 = 1216567) (by norm_num)
theorem B2400341 : Blo 1598998 2400341 := bbase (se 8 (by rfl) ⟨14064, by rfl⟩ : syracuseStep 2400341 = 28129) (by norm_num)
theorem B2883685 : Blo 1598998 2883685 := bbase (se 4 (by rfl) ⟨270345, by rfl⟩ : syracuseStep 2883685 = 540691) (by norm_num)
theorem B2400365 : Blo 1598998 2400365 := bbase (se 3 (by rfl) ⟨450068, by rfl⟩ : syracuseStep 2400365 = 900137) (by norm_num)
theorem B3416197 : Blo 1598998 3416197 := bbase (se 4 (by rfl) ⟨320268, by rfl⟩ : syracuseStep 3416197 = 640537) (by norm_num)
theorem B2400389 : Blo 1598998 2400389 := bbase (se 4 (by rfl) ⟨225036, by rfl⟩ : syracuseStep 2400389 = 450073) (by norm_num)
theorem B2564237 : Blo 1598998 2564237 := bbase (se 3 (by rfl) ⟨480794, by rfl⟩ : syracuseStep 2564237 = 961589) (by norm_num)
theorem B15384725 : Blo 1598998 15384725 := bbase (se 6 (by rfl) ⟨360579, by rfl⟩ : syracuseStep 15384725 = 721159) (by norm_num)
theorem B2400413 : Blo 1598998 2400413 := bbase (se 3 (by rfl) ⟨450077, by rfl⟩ : syracuseStep 2400413 = 900155) (by norm_num)
theorem B6832309 : Blo 1598998 6832309 := bbase (se 5 (by rfl) ⟨320264, by rfl⟩ : syracuseStep 6832309 = 640529) (by norm_num)
theorem B2400437 : Blo 1598998 2400437 := bbase (se 5 (by rfl) ⟨112520, by rfl⟩ : syracuseStep 2400437 = 225041) (by norm_num)
theorem B6832325 : Blo 1598998 6832325 := bbase (se 4 (by rfl) ⟨640530, by rfl⟩ : syracuseStep 6832325 = 1281061) (by norm_num)
theorem B2400461 : Blo 1598998 2400461 := bbase (se 3 (by rfl) ⟨450086, by rfl⟩ : syracuseStep 2400461 = 900173) (by norm_num)
theorem B5398757 : Blo 1598998 5398757 := bbase (se 4 (by rfl) ⟨506133, by rfl⟩ : syracuseStep 5398757 = 1012267) (by norm_num)
theorem B2400485 : Blo 1598998 2400485 := bbase (se 4 (by rfl) ⟨225045, by rfl⟩ : syracuseStep 2400485 = 450091) (by norm_num)
theorem B2400509 : Blo 1598998 2400509 := bbase (se 3 (by rfl) ⟨450095, by rfl⟩ : syracuseStep 2400509 = 900191) (by norm_num)
theorem B2883845 : Blo 1598998 2883845 := bbase (se 4 (by rfl) ⟨270360, by rfl⟩ : syracuseStep 2883845 = 540721) (by norm_num)
theorem B2400533 : Blo 1598998 2400533 := bbase (se 6 (by rfl) ⟨56262, by rfl⟩ : syracuseStep 2400533 = 112525) (by norm_num)
theorem B2400557 : Blo 1598998 2400557 := bbase (se 3 (by rfl) ⟨450104, by rfl⟩ : syracuseStep 2400557 = 900209) (by norm_num)
theorem B2400581 : Blo 1598998 2400581 := bbase (se 4 (by rfl) ⟨225054, by rfl⟩ : syracuseStep 2400581 = 450109) (by norm_num)
theorem B2597197 : Blo 1598998 2597197 := bbase (se 3 (by rfl) ⟨486974, by rfl⟩ : syracuseStep 2597197 = 973949) (by norm_num)
theorem B2883917 : Blo 1598998 2883917 := bbase (se 3 (by rfl) ⟨540734, by rfl⟩ : syracuseStep 2883917 = 1081469) (by norm_num)
theorem B2466133 : Blo 1598998 2466133 := bbase (se 10 (by rfl) ⟨3612, by rfl⟩ : syracuseStep 2466133 = 7225) (by norm_num)
theorem B2400605 : Blo 1598998 2400605 := bbase (se 3 (by rfl) ⟨450113, by rfl⟩ : syracuseStep 2400605 = 900227) (by norm_num)
theorem B1622381 : Blo 1598998 1622381 := bbase (se 3 (by rfl) ⟨304196, by rfl⟩ : syracuseStep 1622381 = 608393) (by norm_num)
theorem B2400629 : Blo 1598998 2400629 := bbase (se 5 (by rfl) ⟨112529, by rfl⟩ : syracuseStep 2400629 = 225059) (by norm_num)
theorem B2023805 : Blo 1598998 2023805 := bbase (se 3 (by rfl) ⟨379463, by rfl⟩ : syracuseStep 2023805 = 758927) (by norm_num)
theorem B2400653 : Blo 1598998 2400653 := bbase (se 3 (by rfl) ⟨450122, by rfl⟩ : syracuseStep 2400653 = 900245) (by norm_num)
theorem B3842453 : Blo 1598998 3842453 := bbase (se 6 (by rfl) ⟨90057, by rfl⟩ : syracuseStep 3842453 = 180115) (by norm_num)
theorem B2400677 : Blo 1598998 2400677 := bbase (se 4 (by rfl) ⟨225063, by rfl⟩ : syracuseStep 2400677 = 450127) (by norm_num)
theorem B2023861 : Blo 1598998 2023861 := bbase (se 5 (by rfl) ⟨94868, by rfl⟩ : syracuseStep 2023861 = 189737) (by norm_num)
theorem B2400701 : Blo 1598998 2400701 := bbase (se 3 (by rfl) ⟨450131, by rfl⟩ : syracuseStep 2400701 = 900263) (by norm_num)
theorem B2277829 : Blo 1598998 2277829 := bbase (se 4 (by rfl) ⟨213546, by rfl⟩ : syracuseStep 2277829 = 427093) (by norm_num)
theorem B2400725 : Blo 1598998 2400725 := bbase (se 7 (by rfl) ⟨28133, by rfl⟩ : syracuseStep 2400725 = 56267) (by norm_num)
theorem B7791077 : Blo 1598998 7791077 := bbase (se 4 (by rfl) ⟨730413, by rfl⟩ : syracuseStep 7791077 = 1460827) (by norm_num)
theorem B4555237 : Blo 1598998 4555237 := bbase (se 4 (by rfl) ⟨427053, by rfl⟩ : syracuseStep 4555237 = 854107) (by norm_num)
theorem B2400749 : Blo 1598998 2400749 := bbase (se 3 (by rfl) ⟨450140, by rfl⟩ : syracuseStep 2400749 = 900281) (by norm_num)
theorem B3416573 : Blo 1598998 3416573 := bbase (se 3 (by rfl) ⟨640607, by rfl⟩ : syracuseStep 3416573 = 1281215) (by norm_num)
theorem B2400773 : Blo 1598998 2400773 := bbase (se 4 (by rfl) ⟨225072, by rfl⟩ : syracuseStep 2400773 = 450145) (by norm_num)
theorem B2023957 : Blo 1598998 2023957 := bbase (se 6 (by rfl) ⟨47436, by rfl⟩ : syracuseStep 2023957 = 94873) (by norm_num)
theorem B2400797 : Blo 1598998 2400797 := bbase (se 3 (by rfl) ⟨450149, by rfl⟩ : syracuseStep 2400797 = 900299) (by norm_num)
theorem B2400821 : Blo 1598998 2400821 := bbase (se 5 (by rfl) ⟨112538, by rfl⟩ : syracuseStep 2400821 = 225077) (by norm_num)
theorem B2400845 : Blo 1598998 2400845 := bbase (se 3 (by rfl) ⟨450158, by rfl⟩ : syracuseStep 2400845 = 900317) (by norm_num)
theorem B2400869 : Blo 1598998 2400869 := bbase (se 4 (by rfl) ⟨225081, by rfl⟩ : syracuseStep 2400869 = 450163) (by norm_num)
theorem B2400893 : Blo 1598998 2400893 := bbase (se 3 (by rfl) ⟨450167, by rfl⟩ : syracuseStep 2400893 = 900335) (by norm_num)
theorem B4047509 : Blo 1598998 4047509 := bbase (se 6 (by rfl) ⟨94863, by rfl⟩ : syracuseStep 4047509 = 189727) (by norm_num)
theorem B5399189 : Blo 1598998 5399189 := bbase (se 6 (by rfl) ⟨126543, by rfl⟩ : syracuseStep 5399189 = 253087) (by norm_num)
theorem B21897877 : Blo 1598998 21897877 := bbase (se 6 (by rfl) ⟨513231, by rfl⟩ : syracuseStep 21897877 = 1026463) (by norm_num)
theorem B2400917 : Blo 1598998 2400917 := bbase (se 6 (by rfl) ⟨56271, by rfl⟩ : syracuseStep 2400917 = 112543) (by norm_num)
theorem B2400941 : Blo 1598998 2400941 := bbase (se 3 (by rfl) ⟨450176, by rfl⟩ : syracuseStep 2400941 = 900353) (by norm_num)
theorem B2024129 : Blo 1598998 2024129 := bbase (se 2 (by rfl) ⟨759048, by rfl⟩ : syracuseStep 2024129 = 1518097) (by norm_num)
theorem B2400965 : Blo 1598998 2400965 := bbase (se 4 (by rfl) ⟨225090, by rfl⟩ : syracuseStep 2400965 = 450181) (by norm_num)
theorem B2400989 : Blo 1598998 2400989 := bbase (se 3 (by rfl) ⟨450185, by rfl⟩ : syracuseStep 2400989 = 900371) (by norm_num)
theorem B2401013 : Blo 1598998 2401013 := bbase (se 5 (by rfl) ⟨112547, by rfl⟩ : syracuseStep 2401013 = 225095) (by norm_num)
theorem B2024185 : Blo 1598998 2024185 := bbase (se 2 (by rfl) ⟨759069, by rfl⟩ : syracuseStep 2024185 = 1518139) (by norm_num)
theorem B2401037 : Blo 1598998 2401037 := bbase (se 3 (by rfl) ⟨450194, by rfl⟩ : syracuseStep 2401037 = 900389) (by norm_num)
theorem B2401061 : Blo 1598998 2401061 := bbase (se 4 (by rfl) ⟨225099, by rfl⟩ : syracuseStep 2401061 = 450199) (by norm_num)
theorem B2401085 : Blo 1598998 2401085 := bbase (se 3 (by rfl) ⟨450203, by rfl⟩ : syracuseStep 2401085 = 900407) (by norm_num)
theorem B2401109 : Blo 1598998 2401109 := bbase (se 9 (by rfl) ⟨7034, by rfl⟩ : syracuseStep 2401109 = 14069) (by norm_num)
theorem B2024281 : Blo 1598998 2024281 := bbase (se 2 (by rfl) ⟨759105, by rfl⟩ : syracuseStep 2024281 = 1518211) (by norm_num)
theorem B2401133 : Blo 1598998 2401133 := bbase (se 3 (by rfl) ⟨450212, by rfl⟩ : syracuseStep 2401133 = 900425) (by norm_num)
theorem B4105093 : Blo 1598998 4105093 := bbase (se 4 (by rfl) ⟨384852, by rfl⟩ : syracuseStep 4105093 = 769705) (by norm_num)
theorem B2401157 : Blo 1598998 2401157 := bbase (se 4 (by rfl) ⟨225108, by rfl⟩ : syracuseStep 2401157 = 450217) (by norm_num)
theorem B14599061 : Blo 1598998 14599061 := bbase (se 6 (by rfl) ⟨342165, by rfl⟩ : syracuseStep 14599061 = 684331) (by norm_num)
theorem B2401181 : Blo 1598998 2401181 := bbase (se 3 (by rfl) ⟨450221, by rfl⟩ : syracuseStep 2401181 = 900443) (by norm_num)
theorem B2401205 : Blo 1598998 2401205 := bbase (se 5 (by rfl) ⟨112556, by rfl⟩ : syracuseStep 2401205 = 225113) (by norm_num)
theorem B2401229 : Blo 1598998 2401229 := bbase (se 3 (by rfl) ⟨450230, by rfl⟩ : syracuseStep 2401229 = 900461) (by norm_num)
theorem B11535317 : Blo 1598998 11535317 := bbase (se 7 (by rfl) ⟨135179, by rfl⟩ : syracuseStep 11535317 = 270359) (by norm_num)
theorem B2401253 : Blo 1598998 2401253 := bbase (se 4 (by rfl) ⟨225117, by rfl⟩ : syracuseStep 2401253 = 450235) (by norm_num)
theorem B4047853 : Blo 1598998 4047853 := bbase (se 3 (by rfl) ⟨758972, by rfl⟩ : syracuseStep 4047853 = 1517945) (by norm_num)
theorem B2401277 : Blo 1598998 2401277 := bbase (se 3 (by rfl) ⟨450239, by rfl⟩ : syracuseStep 2401277 = 900479) (by norm_num)
theorem B2024453 : Blo 1598998 2024453 := bbase (se 4 (by rfl) ⟨189792, by rfl⟩ : syracuseStep 2024453 = 379585) (by norm_num)
theorem B2401301 : Blo 1598998 2401301 := bbase (se 6 (by rfl) ⟨56280, by rfl⟩ : syracuseStep 2401301 = 112561) (by norm_num)
theorem B2401325 : Blo 1598998 2401325 := bbase (se 3 (by rfl) ⟨450248, by rfl⟩ : syracuseStep 2401325 = 900497) (by norm_num)
theorem B2024509 : Blo 1598998 2024509 := bbase (se 3 (by rfl) ⟨379595, by rfl⟩ : syracuseStep 2024509 = 759191) (by norm_num)
theorem B5399621 : Blo 1598998 5399621 := bbase (se 4 (by rfl) ⟨506214, by rfl⟩ : syracuseStep 5399621 = 1012429) (by norm_num)
theorem B2401349 : Blo 1598998 2401349 := bbase (se 4 (by rfl) ⟨225126, by rfl⟩ : syracuseStep 2401349 = 450253) (by norm_num)
theorem B4047965 : Blo 1598998 4047965 := bbase (se 3 (by rfl) ⟨758993, by rfl⟩ : syracuseStep 4047965 = 1517987) (by norm_num)
theorem B2401373 : Blo 1598998 2401373 := bbase (se 3 (by rfl) ⟨450257, by rfl⟩ : syracuseStep 2401373 = 900515) (by norm_num)
theorem B5768293 : Blo 1598998 5768293 := bbase (se 4 (by rfl) ⟨540777, by rfl⟩ : syracuseStep 5768293 = 1081555) (by norm_num)
theorem B2401397 : Blo 1598998 2401397 := bbase (se 5 (by rfl) ⟨112565, by rfl⟩ : syracuseStep 2401397 = 225131) (by norm_num)
theorem B2401421 : Blo 1598998 2401421 := bbase (se 3 (by rfl) ⟨450266, by rfl⟩ : syracuseStep 2401421 = 900533) (by norm_num)
theorem B9110677 : Blo 1598998 9110677 := bbase (se 6 (by rfl) ⟨213531, by rfl⟩ : syracuseStep 9110677 = 427063) (by norm_num)
theorem B2024605 : Blo 1598998 2024605 := bbase (se 3 (by rfl) ⟨379613, by rfl⟩ : syracuseStep 2024605 = 759227) (by norm_num)
theorem B8103077 : Blo 1598998 8103077 := bbase (se 4 (by rfl) ⟨759663, by rfl⟩ : syracuseStep 8103077 = 1519327) (by norm_num)
theorem B2401445 : Blo 1598998 2401445 := bbase (se 4 (by rfl) ⟨225135, by rfl⟩ : syracuseStep 2401445 = 450271) (by norm_num)
theorem B12313781 : Blo 1598998 12313781 := bbase (se 5 (by rfl) ⟨577208, by rfl⟩ : syracuseStep 12313781 = 1154417) (by norm_num)
theorem B7300277 : Blo 1598998 7300277 := bbase (se 5 (by rfl) ⟨342200, by rfl⟩ : syracuseStep 7300277 = 684401) (by norm_num)
theorem B2401469 : Blo 1598998 2401469 := bbase (se 3 (by rfl) ⟨450275, by rfl⟩ : syracuseStep 2401469 = 900551) (by norm_num)
theorem B2401493 : Blo 1598998 2401493 := bbase (se 7 (by rfl) ⟨28142, by rfl⟩ : syracuseStep 2401493 = 56285) (by norm_num)
theorem B2278621 : Blo 1598998 2278621 := bbase (se 3 (by rfl) ⟨427241, by rfl⟩ : syracuseStep 2278621 = 854483) (by norm_num)
theorem B11535605 : Blo 1598998 11535605 := bbase (se 5 (by rfl) ⟨540731, by rfl⟩ : syracuseStep 11535605 = 1081463) (by norm_num)
theorem B4048157 : Blo 1598998 4048157 := bbase (se 3 (by rfl) ⟨759029, by rfl⟩ : syracuseStep 4048157 = 1518059) (by norm_num)
theorem B2884925 : Blo 1598998 2884925 := bbase (se 3 (by rfl) ⟨540923, by rfl⟩ : syracuseStep 2884925 = 1081847) (by norm_num)
theorem B2024777 : Blo 1598998 2024777 := bbase (se 2 (by rfl) ⟨759291, by rfl⟩ : syracuseStep 2024777 = 1518583) (by norm_num)
theorem B2024833 : Blo 1598998 2024833 := bbase (se 2 (by rfl) ⟨759312, by rfl⟩ : syracuseStep 2024833 = 1518625) (by norm_num)
theorem B3597749 : Blo 1598998 3597749 := bbase (se 5 (by rfl) ⟨168644, by rfl⟩ : syracuseStep 3597749 = 337289) (by norm_num)
theorem B2024929 : Blo 1598998 2024929 := bbase (se 2 (by rfl) ⟨759348, by rfl⟩ : syracuseStep 2024929 = 1518697) (by norm_num)
theorem B5400053 : Blo 1598998 5400053 := bbase (se 5 (by rfl) ⟨253127, by rfl⟩ : syracuseStep 5400053 = 506255) (by norm_num)
theorem B3597821 : Blo 1598998 3597821 := bbase (se 3 (by rfl) ⟨674591, by rfl⟩ : syracuseStep 3597821 = 1349183) (by norm_num)
theorem B2278957 : Blo 1598998 2278957 := bbase (se 3 (by rfl) ⟨427304, by rfl⟩ : syracuseStep 2278957 = 854609) (by norm_num)
theorem B4556341 : Blo 1598998 4556341 := bbase (se 5 (by rfl) ⟨213578, by rfl⟩ : syracuseStep 4556341 = 427157) (by norm_num)
theorem B3597893 : Blo 1598998 3597893 := bbase (se 4 (by rfl) ⟨337302, by rfl⟩ : syracuseStep 3597893 = 674605) (by norm_num)
theorem B8095301 : Blo 1598998 8095301 := bbase (se 4 (by rfl) ⟨758934, by rfl⟩ : syracuseStep 8095301 = 1517869) (by norm_num)
theorem B12977749 : Blo 1598998 12977749 := bbase (se 8 (by rfl) ⟨76041, by rfl⟩ : syracuseStep 12977749 = 152083) (by norm_num)
theorem B4048501 : Blo 1598998 4048501 := bbase (se 5 (by rfl) ⟨189773, by rfl⟩ : syracuseStep 4048501 = 379547) (by norm_num)
theorem B3597965 : Blo 1598998 3597965 := bbase (se 3 (by rfl) ⟨674618, by rfl⟩ : syracuseStep 3597965 = 1349237) (by norm_num)
theorem B2025101 : Blo 1598998 2025101 := bbase (se 3 (by rfl) ⟨379706, by rfl⟩ : syracuseStep 2025101 = 759413) (by norm_num)
theorem B2025157 : Blo 1598998 2025157 := bbase (se 4 (by rfl) ⟨189858, by rfl⟩ : syracuseStep 2025157 = 379717) (by norm_num)
theorem B3598037 : Blo 1598998 3598037 := bbase (se 7 (by rfl) ⟨42164, by rfl⟩ : syracuseStep 3598037 = 84329) (by norm_num)
theorem B12150485 : Blo 1598998 12150485 := bbase (se 7 (by rfl) ⟨142388, by rfl⟩ : syracuseStep 12150485 = 284777) (by norm_num)
theorem B4048613 : Blo 1598998 4048613 := bbase (se 4 (by rfl) ⟨379557, by rfl⟩ : syracuseStep 4048613 = 759115) (by norm_num)
theorem B2279173 : Blo 1598998 2279173 := bbase (se 4 (by rfl) ⟨213672, by rfl⟩ : syracuseStep 2279173 = 427345) (by norm_num)
theorem B3598109 : Blo 1598998 3598109 := bbase (se 3 (by rfl) ⟨674645, by rfl⟩ : syracuseStep 3598109 = 1349291) (by norm_num)
theorem B2025253 : Blo 1598998 2025253 := bbase (se 4 (by rfl) ⟨189867, by rfl⟩ : syracuseStep 2025253 = 379735) (by norm_num)
theorem B3598181 : Blo 1598998 3598181 := bbase (se 4 (by rfl) ⟨337329, by rfl⟩ : syracuseStep 3598181 = 674659) (by norm_num)
theorem B4048805 : Blo 1598998 4048805 := bbase (se 4 (by rfl) ⟨379575, by rfl⟩ : syracuseStep 4048805 = 759151) (by norm_num)
theorem B5400485 : Blo 1598998 5400485 := bbase (se 4 (by rfl) ⟨506295, by rfl⟩ : syracuseStep 5400485 = 1012591) (by norm_num)
theorem B3598253 : Blo 1598998 3598253 := bbase (se 3 (by rfl) ⟨674672, by rfl⟩ : syracuseStep 3598253 = 1349345) (by norm_num)
theorem B2025425 : Blo 1598998 2025425 := bbase (se 2 (by rfl) ⟨759534, by rfl⟩ : syracuseStep 2025425 = 1519069) (by norm_num)
theorem B3598325 : Blo 1598998 3598325 := bbase (se 5 (by rfl) ⟨168671, by rfl⟩ : syracuseStep 3598325 = 337343) (by norm_num)
theorem B2025481 : Blo 1598998 2025481 := bbase (se 2 (by rfl) ⟨759555, by rfl⟩ : syracuseStep 2025481 = 1519111) (by norm_num)
theorem B7686197 : Blo 1598998 7686197 := bbase (se 5 (by rfl) ⟨360290, by rfl⟩ : syracuseStep 7686197 = 720581) (by norm_num)
theorem B3598397 : Blo 1598998 3598397 := bbase (se 3 (by rfl) ⟨674699, by rfl⟩ : syracuseStep 3598397 = 1349399) (by norm_num)
theorem B3418213 : Blo 1598998 3418213 := bbase (se 4 (by rfl) ⟨320457, by rfl⟩ : syracuseStep 3418213 = 640915) (by norm_num)
theorem B2025577 : Blo 1598998 2025577 := bbase (se 2 (by rfl) ⟨759591, by rfl⟩ : syracuseStep 2025577 = 1519183) (by norm_num)
theorem B12142709 : Blo 1598998 12142709 := bbase (se 5 (by rfl) ⟨569189, by rfl⟩ : syracuseStep 12142709 = 1138379) (by norm_num)
theorem B3598469 : Blo 1598998 3598469 := bbase (se 4 (by rfl) ⟨337356, by rfl⟩ : syracuseStep 3598469 = 674713) (by norm_num)
theorem B7301285 : Blo 1598998 7301285 := bbase (se 4 (by rfl) ⟨684495, by rfl⟩ : syracuseStep 7301285 = 1368991) (by norm_num)
theorem B3598541 : Blo 1598998 3598541 := bbase (se 3 (by rfl) ⟨674726, by rfl⟩ : syracuseStep 3598541 = 1349453) (by norm_num)
theorem B4049149 : Blo 1598998 4049149 := bbase (se 3 (by rfl) ⟨759215, by rfl⟩ : syracuseStep 4049149 = 1518431) (by norm_num)
theorem B3598613 : Blo 1598998 3598613 := bbase (se 6 (by rfl) ⟨84342, by rfl⟩ : syracuseStep 3598613 = 168685) (by norm_num)
theorem B2025749 : Blo 1598998 2025749 := bbase (se 6 (by rfl) ⟨47478, by rfl⟩ : syracuseStep 2025749 = 94957) (by norm_num)
theorem B2025805 : Blo 1598998 2025805 := bbase (se 3 (by rfl) ⟨379838, by rfl⟩ : syracuseStep 2025805 = 759677) (by norm_num)
theorem B5400917 : Blo 1598998 5400917 := bbase (se 10 (by rfl) ⟨7911, by rfl⟩ : syracuseStep 5400917 = 15823) (by norm_num)
theorem B3598685 : Blo 1598998 3598685 := bbase (se 3 (by rfl) ⟨674753, by rfl⟩ : syracuseStep 3598685 = 1349507) (by norm_num)
theorem B6072677 : Blo 1598998 6072677 := bbase (se 4 (by rfl) ⟨569313, by rfl⟩ : syracuseStep 6072677 = 1138627) (by norm_num)
theorem B4049261 : Blo 1598998 4049261 := bbase (se 3 (by rfl) ⟨759236, by rfl⟩ : syracuseStep 4049261 = 1518473) (by norm_num)
theorem B6834581 : Blo 1598998 6834581 := bbase (se 6 (by rfl) ⟨160185, by rfl⟩ : syracuseStep 6834581 = 320371) (by norm_num)
theorem B3598757 : Blo 1598998 3598757 := bbase (se 4 (by rfl) ⟨337383, by rfl⟩ : syracuseStep 3598757 = 674767) (by norm_num)
theorem B2025901 : Blo 1598998 2025901 := bbase (se 3 (by rfl) ⟨379856, by rfl⟩ : syracuseStep 2025901 = 759713) (by norm_num)
theorem B8104373 : Blo 1598998 8104373 := bbase (se 5 (by rfl) ⟨379892, by rfl⟩ : syracuseStep 8104373 = 759785) (by norm_num)
theorem B3598829 : Blo 1598998 3598829 := bbase (se 3 (by rfl) ⟨674780, by rfl⟩ : syracuseStep 3598829 = 1349561) (by norm_num)
theorem B13666805 : Blo 1598998 13666805 := bbase (se 5 (by rfl) ⟨640631, by rfl⟩ : syracuseStep 13666805 = 1281263) (by norm_num)
theorem B2599445 : Blo 1598998 2599445 := bbase (se 6 (by rfl) ⟨60924, by rfl⟩ : syracuseStep 2599445 = 121849) (by norm_num)
theorem B4049453 : Blo 1598998 4049453 := bbase (se 3 (by rfl) ⟨759272, by rfl⟩ : syracuseStep 4049453 = 1518545) (by norm_num)
theorem B3598901 : Blo 1598998 3598901 := bbase (se 5 (by rfl) ⟨168698, by rfl⟩ : syracuseStep 3598901 = 337397) (by norm_num)
theorem B2026073 : Blo 1598998 2026073 := bbase (se 2 (by rfl) ⟨759777, by rfl⟩ : syracuseStep 2026073 = 1519555) (by norm_num)
theorem B3598973 : Blo 1598998 3598973 := bbase (se 3 (by rfl) ⟨674807, by rfl⟩ : syracuseStep 3598973 = 1349615) (by norm_num)
theorem B6072965 : Blo 1598998 6072965 := bbase (se 4 (by rfl) ⟨569340, by rfl⟩ : syracuseStep 6072965 = 1138681) (by norm_num)
theorem B3844741 : Blo 1598998 3844741 := bbase (se 4 (by rfl) ⟨360444, by rfl⟩ : syracuseStep 3844741 = 720889) (by norm_num)
theorem B2026129 : Blo 1598998 2026129 := bbase (se 2 (by rfl) ⟨759798, by rfl⟩ : syracuseStep 2026129 = 1519597) (by norm_num)
theorem B8440469 : Blo 1598998 8440469 := bbase (se 6 (by rfl) ⟨197823, by rfl⟩ : syracuseStep 8440469 = 395647) (by norm_num)
theorem B3599045 : Blo 1598998 3599045 := bbase (se 4 (by rfl) ⟨337410, by rfl⟩ : syracuseStep 3599045 = 674821) (by norm_num)
theorem B3844837 : Blo 1598998 3844837 := bbase (se 4 (by rfl) ⟨360453, by rfl⟩ : syracuseStep 3844837 = 720907) (by norm_num)
theorem B2026225 : Blo 1598998 2026225 := bbase (se 2 (by rfl) ⟨759834, by rfl⟩ : syracuseStep 2026225 = 1519669) (by norm_num)
theorem B5401349 : Blo 1598998 5401349 := bbase (se 4 (by rfl) ⟨506376, by rfl⟩ : syracuseStep 5401349 = 1012753) (by norm_num)
theorem B3599117 : Blo 1598998 3599117 := bbase (se 3 (by rfl) ⟨674834, by rfl⟩ : syracuseStep 3599117 = 1349669) (by norm_num)
theorem B8096597 : Blo 1598998 8096597 := bbase (se 9 (by rfl) ⟨23720, by rfl⟩ : syracuseStep 8096597 = 47441) (by norm_num)
theorem B3599189 : Blo 1598998 3599189 := bbase (se 9 (by rfl) ⟨10544, by rfl⟩ : syracuseStep 3599189 = 21089) (by norm_num)
theorem B4049797 : Blo 1598998 4049797 := bbase (se 4 (by rfl) ⟨379668, by rfl⟩ : syracuseStep 4049797 = 759337) (by norm_num)
theorem B3599261 : Blo 1598998 3599261 := bbase (se 3 (by rfl) ⟨674861, by rfl⟩ : syracuseStep 3599261 = 1349723) (by norm_num)
theorem B3845029 : Blo 1598998 3845029 := bbase (se 4 (by rfl) ⟨360471, by rfl⟩ : syracuseStep 3845029 = 720943) (by norm_num)
theorem B3509173 : Blo 1598998 3509173 := bbase (se 5 (by rfl) ⟨164492, by rfl⟩ : syracuseStep 3509173 = 328985) (by norm_num)
theorem B3419101 : Blo 1598998 3419101 := bbase (se 3 (by rfl) ⟨641081, by rfl⟩ : syracuseStep 3419101 = 1282163) (by norm_num)
theorem B3599333 : Blo 1598998 3599333 := bbase (se 4 (by rfl) ⟨337437, by rfl⟩ : syracuseStep 3599333 = 674875) (by norm_num)
theorem B4049909 : Blo 1598998 4049909 := bbase (se 5 (by rfl) ⟨189839, by rfl⟩ : syracuseStep 4049909 = 379679) (by norm_num)
theorem B3951613 : Blo 1598998 3951613 := bbase (se 3 (by rfl) ⟨740927, by rfl⟩ : syracuseStep 3951613 = 1481855) (by norm_num)
theorem B4557845 : Blo 1598998 4557845 := bbase (se 6 (by rfl) ⟨106824, by rfl⟩ : syracuseStep 4557845 = 213649) (by norm_num)
theorem B3599405 : Blo 1598998 3599405 := bbase (se 3 (by rfl) ⟨674888, by rfl⟩ : syracuseStep 3599405 = 1349777) (by norm_num)
theorem B9112661 : Blo 1598998 9112661 := bbase (se 8 (by rfl) ⟨53394, by rfl⟩ : syracuseStep 9112661 = 106789) (by norm_num)
theorem B3599477 : Blo 1598998 3599477 := bbase (se 5 (by rfl) ⟨168725, by rfl⟩ : syracuseStep 3599477 = 337451) (by norm_num)
theorem B2698373 : Blo 1598998 2698373 := bbase (se 4 (by rfl) ⟨252972, by rfl⟩ : syracuseStep 2698373 = 505945) (by norm_num)
theorem B4050101 : Blo 1598998 4050101 := bbase (se 5 (by rfl) ⟨189848, by rfl⟩ : syracuseStep 4050101 = 379697) (by norm_num)
theorem B5401781 : Blo 1598998 5401781 := bbase (se 5 (by rfl) ⟨253208, by rfl⟩ : syracuseStep 5401781 = 506417) (by norm_num)
theorem B3599549 : Blo 1598998 3599549 := bbase (se 3 (by rfl) ⟨674915, by rfl⟩ : syracuseStep 3599549 = 1349831) (by norm_num)
theorem B3845357 : Blo 1598998 3845357 := bbase (se 3 (by rfl) ⟨721004, by rfl⟩ : syracuseStep 3845357 = 1442009) (by norm_num)
theorem B2698501 : Blo 1598998 2698501 := bbase (se 4 (by rfl) ⟨252984, by rfl⟩ : syracuseStep 2698501 = 505969) (by norm_num)
theorem B3599621 : Blo 1598998 3599621 := bbase (se 4 (by rfl) ⟨337464, by rfl⟩ : syracuseStep 3599621 = 674929) (by norm_num)
theorem B3599693 : Blo 1598998 3599693 := bbase (se 3 (by rfl) ⟨674942, by rfl⟩ : syracuseStep 3599693 = 1349885) (by norm_num)
theorem B2698589 : Blo 1598998 2698589 := bbase (se 3 (by rfl) ⟨505985, by rfl⟩ : syracuseStep 2698589 = 1011971) (by norm_num)
theorem B3599765 : Blo 1598998 3599765 := bbase (se 6 (by rfl) ⟨84369, by rfl⟩ : syracuseStep 3599765 = 168739) (by norm_num)
theorem B30739925 : Blo 1598998 30739925 := bbase (se 7 (by rfl) ⟨360233, by rfl⟩ : syracuseStep 30739925 = 720467) (by norm_num)
theorem B2698717 : Blo 1598998 2698717 := bbase (se 3 (by rfl) ⟨506009, by rfl⟩ : syracuseStep 2698717 = 1012019) (by norm_num)
theorem B3599837 : Blo 1598998 3599837 := bbase (se 3 (by rfl) ⟨674969, by rfl⟩ : syracuseStep 3599837 = 1349939) (by norm_num)
theorem B4050445 : Blo 1598998 4050445 := bbase (se 3 (by rfl) ⟨759458, by rfl⟩ : syracuseStep 4050445 = 1518917) (by norm_num)
theorem B3599909 : Blo 1598998 3599909 := bbase (se 4 (by rfl) ⟨337491, by rfl⟩ : syracuseStep 3599909 = 674983) (by norm_num)
theorem B2698805 : Blo 1598998 2698805 := bbase (se 5 (by rfl) ⟨126506, by rfl⟩ : syracuseStep 2698805 = 253013) (by norm_num)
theorem B5402213 : Blo 1598998 5402213 := bbase (se 4 (by rfl) ⟨506457, by rfl⟩ : syracuseStep 5402213 = 1012915) (by norm_num)
theorem B3599981 : Blo 1598998 3599981 := bbase (se 3 (by rfl) ⟨674996, by rfl⟩ : syracuseStep 3599981 = 1349993) (by norm_num)
theorem B4050557 : Blo 1598998 4050557 := bbase (se 3 (by rfl) ⟨759479, by rfl⟩ : syracuseStep 4050557 = 1518959) (by norm_num)
theorem B3845789 : Blo 1598998 3845789 := bbase (se 3 (by rfl) ⟨721085, by rfl⟩ : syracuseStep 3845789 = 1442171) (by norm_num)
theorem B2698933 : Blo 1598998 2698933 := bbase (se 5 (by rfl) ⟨126512, by rfl⟩ : syracuseStep 2698933 = 253025) (by norm_num)
theorem B3600053 : Blo 1598998 3600053 := bbase (se 5 (by rfl) ⟨168752, by rfl⟩ : syracuseStep 3600053 = 337505) (by norm_num)
theorem B3600125 : Blo 1598998 3600125 := bbase (se 3 (by rfl) ⟨675023, by rfl⟩ : syracuseStep 3600125 = 1350047) (by norm_num)
theorem B2699021 : Blo 1598998 2699021 := bbase (se 3 (by rfl) ⟨506066, by rfl⟩ : syracuseStep 2699021 = 1012133) (by norm_num)
theorem B5123861 : Blo 1598998 5123861 := bbase (se 6 (by rfl) ⟨120090, by rfl⟩ : syracuseStep 5123861 = 240181) (by norm_num)
theorem B6074149 : Blo 1598998 6074149 := bbase (se 4 (by rfl) ⟨569451, by rfl⟩ : syracuseStep 6074149 = 1138903) (by norm_num)
theorem B4050749 : Blo 1598998 4050749 := bbase (se 3 (by rfl) ⟨759515, by rfl⟩ : syracuseStep 4050749 = 1519031) (by norm_num)
theorem B3600197 : Blo 1598998 3600197 := bbase (se 4 (by rfl) ⟨337518, by rfl⟩ : syracuseStep 3600197 = 675037) (by norm_num)
theorem B2699149 : Blo 1598998 2699149 := bbase (se 3 (by rfl) ⟨506090, by rfl⟩ : syracuseStep 2699149 = 1012181) (by norm_num)
theorem B3600269 : Blo 1598998 3600269 := bbase (se 3 (by rfl) ⟨675050, by rfl⟩ : syracuseStep 3600269 = 1350101) (by norm_num)
theorem B30773141 : Blo 1598998 30773141 := bbase (se 6 (by rfl) ⟨721245, by rfl⟩ : syracuseStep 30773141 = 1442491) (by norm_num)
theorem B3600341 : Blo 1598998 3600341 := bbase (se 7 (by rfl) ⟨42191, by rfl⟩ : syracuseStep 3600341 = 84383) (by norm_num)
theorem B2699237 : Blo 1598998 2699237 := bbase (se 4 (by rfl) ⟨253053, by rfl⟩ : syracuseStep 2699237 = 506107) (by norm_num)
theorem B1708013 : Blo 1598998 1708013 := bbase (se 3 (by rfl) ⟨320252, by rfl⟩ : syracuseStep 1708013 = 640505) (by norm_num)
theorem B3846125 : Blo 1598998 3846125 := bbase (se 3 (by rfl) ⟨721148, by rfl⟩ : syracuseStep 3846125 = 1442297) (by norm_num)
theorem B2633717 : Blo 1598998 2633717 := bbase (se 5 (by rfl) ⟨123455, by rfl⟩ : syracuseStep 2633717 = 246911) (by norm_num)
theorem B5402645 : Blo 1598998 5402645 := bbase (se 6 (by rfl) ⟨126624, by rfl⟩ : syracuseStep 5402645 = 253249) (by norm_num)
theorem B3600413 : Blo 1598998 3600413 := bbase (se 3 (by rfl) ⟨675077, by rfl⟩ : syracuseStep 3600413 = 1350155) (by norm_num)
theorem B6074453 : Blo 1598998 6074453 := bbase (se 8 (by rfl) ⟨35592, by rfl⟩ : syracuseStep 6074453 = 71185) (by norm_num)
theorem B8097893 : Blo 1598998 8097893 := bbase (se 4 (by rfl) ⟨759177, by rfl⟩ : syracuseStep 8097893 = 1518355) (by norm_num)
theorem B2699365 : Blo 1598998 2699365 := bbase (se 4 (by rfl) ⟨253065, by rfl⟩ : syracuseStep 2699365 = 506131) (by norm_num)
theorem B3600485 : Blo 1598998 3600485 := bbase (se 4 (by rfl) ⟨337545, by rfl⟩ : syracuseStep 3600485 = 675091) (by norm_num)
theorem B3289229 : Blo 1598998 3289229 := bbase (se 3 (by rfl) ⟨616730, by rfl⟩ : syracuseStep 3289229 = 1233461) (by norm_num)
theorem B32452757 : Blo 1598998 32452757 := bbase (se 6 (by rfl) ⟨760611, by rfl⟩ : syracuseStep 32452757 = 1521223) (by norm_num)
theorem B4051093 : Blo 1598998 4051093 := bbase (se 6 (by rfl) ⟨94947, by rfl⟩ : syracuseStep 4051093 = 189895) (by norm_num)
theorem B3600557 : Blo 1598998 3600557 := bbase (se 3 (by rfl) ⟨675104, by rfl⟩ : syracuseStep 3600557 = 1350209) (by norm_num)
theorem B2699453 : Blo 1598998 2699453 := bbase (se 3 (by rfl) ⟨506147, by rfl⟩ : syracuseStep 2699453 = 1012295) (by norm_num)
theorem B1921217 : Blo 1598998 1921217 := bbase (se 2 (by rfl) ⟨720456, by rfl⟩ : syracuseStep 1921217 = 1440913) (by norm_num)
theorem B3600629 : Blo 1598998 3600629 := bbase (se 5 (by rfl) ⟨168779, by rfl⟩ : syracuseStep 3600629 = 337559) (by norm_num)
theorem B4051205 : Blo 1598998 4051205 := bbase (se 4 (by rfl) ⟨379800, by rfl⟩ : syracuseStep 4051205 = 759601) (by norm_num)
theorem B10252565 : Blo 1598998 10252565 := bbase (se 6 (by rfl) ⟨240294, by rfl⟩ : syracuseStep 10252565 = 480589) (by norm_num)
theorem B1921333 : Blo 1598998 1921333 := bbase (se 5 (by rfl) ⟨90062, by rfl⟩ : syracuseStep 1921333 = 180125) (by norm_num)
theorem B2699581 : Blo 1598998 2699581 := bbase (se 3 (by rfl) ⟨506171, by rfl⟩ : syracuseStep 2699581 = 1012343) (by norm_num)
theorem B3600701 : Blo 1598998 3600701 := bbase (se 3 (by rfl) ⟨675131, by rfl⟩ : syracuseStep 3600701 = 1350263) (by norm_num)
theorem B1921357 : Blo 1598998 1921357 := bbase (se 3 (by rfl) ⟨360254, by rfl⟩ : syracuseStep 1921357 = 720509) (by norm_num)
theorem B3600773 : Blo 1598998 3600773 := bbase (se 4 (by rfl) ⟨337572, by rfl⟩ : syracuseStep 3600773 = 675145) (by norm_num)
theorem B2699669 : Blo 1598998 2699669 := bbase (se 6 (by rfl) ⟨63273, by rfl⟩ : syracuseStep 2699669 = 126547) (by norm_num)
theorem B1708457 : Blo 1598998 1708457 := bbase (se 2 (by rfl) ⟨640671, by rfl⟩ : syracuseStep 1708457 = 1281343) (by norm_num)
theorem B4051397 : Blo 1598998 4051397 := bbase (se 4 (by rfl) ⟨379818, by rfl⟩ : syracuseStep 4051397 = 759637) (by norm_num)
theorem B5403077 : Blo 1598998 5403077 := bbase (se 4 (by rfl) ⟨506538, by rfl⟩ : syracuseStep 5403077 = 1013077) (by norm_num)
theorem B3600845 : Blo 1598998 3600845 := bbase (se 3 (by rfl) ⟨675158, by rfl⟩ : syracuseStep 3600845 = 1350317) (by norm_num)
theorem B2699797 : Blo 1598998 2699797 := bbase (se 6 (by rfl) ⟨63276, by rfl⟩ : syracuseStep 2699797 = 126553) (by norm_num)
theorem B3600917 : Blo 1598998 3600917 := bbase (se 6 (by rfl) ⟨84396, by rfl⟩ : syracuseStep 3600917 = 168793) (by norm_num)
theorem B3035693 : Blo 1598998 3035693 := bbase (se 3 (by rfl) ⟨569192, by rfl⟩ : syracuseStep 3035693 = 1138385) (by norm_num)
theorem B3600989 : Blo 1598998 3600989 := bbase (se 3 (by rfl) ⟨675185, by rfl⟩ : syracuseStep 3600989 = 1350371) (by norm_num)
theorem B6156901 : Blo 1598998 6156901 := bbase (se 4 (by rfl) ⟨577209, by rfl⟩ : syracuseStep 6156901 = 1154419) (by norm_num)
theorem B2699885 : Blo 1598998 2699885 := bbase (se 3 (by rfl) ⟨506228, by rfl⟩ : syracuseStep 2699885 = 1012457) (by norm_num)
theorem B1708705 : Blo 1598998 1708705 := bbase (se 2 (by rfl) ⟨640764, by rfl⟩ : syracuseStep 1708705 = 1281529) (by norm_num)
theorem B3601061 : Blo 1598998 3601061 := bbase (se 4 (by rfl) ⟨337599, by rfl⟩ : syracuseStep 3601061 = 675199) (by norm_num)
theorem B6484661 : Blo 1598998 6484661 := bbase (se 5 (by rfl) ⟨303968, by rfl⟩ : syracuseStep 6484661 = 607937) (by norm_num)
theorem B4862693 : Blo 1598998 4862693 := bbase (se 4 (by rfl) ⟨455877, by rfl⟩ : syracuseStep 4862693 = 911755) (by norm_num)
theorem B2700013 : Blo 1598998 2700013 := bbase (se 3 (by rfl) ⟨506252, by rfl⟩ : syracuseStep 2700013 = 1012505) (by norm_num)
theorem B3601133 : Blo 1598998 3601133 := bbase (se 3 (by rfl) ⟨675212, by rfl⟩ : syracuseStep 3601133 = 1350425) (by norm_num)
theorem B1798897 : Blo 1598998 1798897 := bbase (se 2 (by rfl) ⟨674586, by rfl⟩ : syracuseStep 1798897 = 1349173) (by norm_num)
theorem B1798933 : Blo 1598998 1798933 := bbase (se 6 (by rfl) ⟨42162, by rfl⟩ : syracuseStep 1798933 = 84325) (by norm_num)
theorem B4051741 : Blo 1598998 4051741 := bbase (se 3 (by rfl) ⟨759701, by rfl⟩ : syracuseStep 4051741 = 1519403) (by norm_num)
theorem B3601205 : Blo 1598998 3601205 := bbase (se 5 (by rfl) ⟨168806, by rfl⟩ : syracuseStep 3601205 = 337613) (by norm_num)
theorem B1798969 : Blo 1598998 1798969 := bbase (se 2 (by rfl) ⟨674613, by rfl⟩ : syracuseStep 1798969 = 1349227) (by norm_num)
theorem B2700101 : Blo 1598998 2700101 := bbase (se 4 (by rfl) ⟨253134, by rfl⟩ : syracuseStep 2700101 = 506269) (by norm_num)
theorem B3035981 : Blo 1598998 3035981 := bbase (se 3 (by rfl) ⟨569246, by rfl⟩ : syracuseStep 3035981 = 1138493) (by norm_num)
theorem B1799005 : Blo 1598998 1799005 := bbase (se 3 (by rfl) ⟨337313, by rfl⟩ : syracuseStep 1799005 = 674627) (by norm_num)
theorem B9237365 : Blo 1598998 9237365 := bbase (se 5 (by rfl) ⟨433001, by rfl⟩ : syracuseStep 9237365 = 866003) (by norm_num)
theorem B3601277 : Blo 1598998 3601277 := bbase (se 3 (by rfl) ⟨675239, by rfl⟩ : syracuseStep 3601277 = 1350479) (by norm_num)
theorem B3208061 : Blo 1598998 3208061 := bbase (se 3 (by rfl) ⟨601511, by rfl⟩ : syracuseStep 3208061 = 1203023) (by norm_num)
theorem B1799041 : Blo 1598998 1799041 := bbase (se 2 (by rfl) ⟨674640, by rfl⟩ : syracuseStep 1799041 = 1349281) (by norm_num)
theorem B1823629 : Blo 1598998 1823629 := bbase (se 3 (by rfl) ⟨341930, by rfl⟩ : syracuseStep 1823629 = 683861) (by norm_num)
theorem B4051853 : Blo 1598998 4051853 := bbase (se 3 (by rfl) ⟨759722, by rfl⟩ : syracuseStep 4051853 = 1519445) (by norm_num)
theorem B1799077 : Blo 1598998 1799077 := bbase (se 4 (by rfl) ⟨168663, by rfl⟩ : syracuseStep 1799077 = 337327) (by norm_num)
theorem B2700229 : Blo 1598998 2700229 := bbase (se 4 (by rfl) ⟨253146, by rfl⟩ : syracuseStep 2700229 = 506293) (by norm_num)
theorem B3601349 : Blo 1598998 3601349 := bbase (se 4 (by rfl) ⟨337626, by rfl⟩ : syracuseStep 3601349 = 675253) (by norm_num)
theorem B1799113 : Blo 1598998 1799113 := bbase (se 2 (by rfl) ⟨674667, by rfl⟩ : syracuseStep 1799113 = 1349335) (by norm_num)
theorem B3036133 : Blo 1598998 3036133 := bbase (se 4 (by rfl) ⟨284637, by rfl⟩ : syracuseStep 3036133 = 569275) (by norm_num)
theorem B1643497 : Blo 1598998 1643497 := bbase (se 2 (by rfl) ⟨616311, by rfl⟩ : syracuseStep 1643497 = 1232623) (by norm_num)
theorem B1799149 : Blo 1598998 1799149 := bbase (se 3 (by rfl) ⟨337340, by rfl⟩ : syracuseStep 1799149 = 674681) (by norm_num)
theorem B1922053 : Blo 1598998 1922053 := bbase (se 4 (by rfl) ⟨180192, by rfl⟩ : syracuseStep 1922053 = 360385) (by norm_num)
theorem B3601421 : Blo 1598998 3601421 := bbase (se 3 (by rfl) ⟨675266, by rfl⟩ : syracuseStep 3601421 = 1350533) (by norm_num)
theorem B1799185 : Blo 1598998 1799185 := bbase (se 2 (by rfl) ⟨674694, by rfl⟩ : syracuseStep 1799185 = 1349389) (by norm_num)
theorem B2700317 : Blo 1598998 2700317 := bbase (se 3 (by rfl) ⟨506309, by rfl⟩ : syracuseStep 2700317 = 1012619) (by norm_num)
theorem B1799221 : Blo 1598998 1799221 := bbase (se 5 (by rfl) ⟨84338, by rfl⟩ : syracuseStep 1799221 = 168677) (by norm_num)
theorem B4052045 : Blo 1598998 4052045 := bbase (se 3 (by rfl) ⟨759758, by rfl⟩ : syracuseStep 4052045 = 1519517) (by norm_num)
theorem B1709137 : Blo 1598998 1709137 := bbase (se 2 (by rfl) ⟨640926, by rfl⟩ : syracuseStep 1709137 = 1281853) (by norm_num)
theorem B3601493 : Blo 1598998 3601493 := bbase (se 8 (by rfl) ⟨21102, by rfl⟩ : syracuseStep 3601493 = 42205) (by norm_num)
theorem B1799257 : Blo 1598998 1799257 := bbase (se 2 (by rfl) ⟨674721, by rfl⟩ : syracuseStep 1799257 = 1349443) (by norm_num)
theorem B1922149 : Blo 1598998 1922149 := bbase (se 4 (by rfl) ⟨180201, by rfl⟩ : syracuseStep 1922149 = 360403) (by norm_num)
theorem B1799293 : Blo 1598998 1799293 := bbase (se 3 (by rfl) ⟨337367, by rfl⟩ : syracuseStep 1799293 = 674735) (by norm_num)
theorem B1709209 : Blo 1598998 1709209 := bbase (se 2 (by rfl) ⟨640953, by rfl⟩ : syracuseStep 1709209 = 1281907) (by norm_num)
theorem B2700445 : Blo 1598998 2700445 := bbase (se 3 (by rfl) ⟨506333, by rfl⟩ : syracuseStep 2700445 = 1012667) (by norm_num)
theorem B3601565 : Blo 1598998 3601565 := bbase (se 3 (by rfl) ⟨675293, by rfl⟩ : syracuseStep 3601565 = 1350587) (by norm_num)
theorem B1799329 : Blo 1598998 1799329 := bbase (se 2 (by rfl) ⟨674748, by rfl⟩ : syracuseStep 1799329 = 1349497) (by norm_num)
theorem B4617397 : Blo 1598998 4617397 := bbase (se 5 (by rfl) ⟨216440, by rfl⟩ : syracuseStep 4617397 = 432881) (by norm_num)
theorem B1799365 : Blo 1598998 1799365 := bbase (se 4 (by rfl) ⟨168690, by rfl⟩ : syracuseStep 1799365 = 337381) (by norm_num)
theorem B3601637 : Blo 1598998 3601637 := bbase (se 4 (by rfl) ⟨337653, by rfl⟩ : syracuseStep 3601637 = 675307) (by norm_num)
theorem B1799401 : Blo 1598998 1799401 := bbase (se 2 (by rfl) ⟨674775, by rfl⟩ : syracuseStep 1799401 = 1349551) (by norm_num)
theorem B2700533 : Blo 1598998 2700533 := bbase (se 5 (by rfl) ⟨126587, by rfl⟩ : syracuseStep 2700533 = 253175) (by norm_num)
theorem B9114869 : Blo 1598998 9114869 := bbase (se 5 (by rfl) ⟨427259, by rfl⟩ : syracuseStep 9114869 = 854519) (by norm_num)
theorem B1799437 : Blo 1598998 1799437 := bbase (se 3 (by rfl) ⟨337394, by rfl⟩ : syracuseStep 1799437 = 674789) (by norm_num)
theorem B3036437 : Blo 1598998 3036437 := bbase (se 6 (by rfl) ⟨71166, by rfl⟩ : syracuseStep 3036437 = 142333) (by norm_num)
theorem B3601709 : Blo 1598998 3601709 := bbase (se 3 (by rfl) ⟨675320, by rfl⟩ : syracuseStep 3601709 = 1350641) (by norm_num)
theorem B3650861 : Blo 1598998 3650861 := bbase (se 3 (by rfl) ⟨684536, by rfl⟩ : syracuseStep 3650861 = 1369073) (by norm_num)
theorem B1799473 : Blo 1598998 1799473 := bbase (se 2 (by rfl) ⟨674802, by rfl⟩ : syracuseStep 1799473 = 1349605) (by norm_num)
theorem B1799509 : Blo 1598998 1799509 := bbase (se 13 (by rfl) ⟨329, by rfl⟩ : syracuseStep 1799509 = 659) (by norm_num)
theorem B1848685 : Blo 1598998 1848685 := bbase (se 3 (by rfl) ⟨346628, by rfl⟩ : syracuseStep 1848685 = 693257) (by norm_num)
theorem B8099189 : Blo 1598998 8099189 := bbase (se 5 (by rfl) ⟨379649, by rfl⟩ : syracuseStep 8099189 = 759299) (by norm_num)
theorem B2700661 : Blo 1598998 2700661 := bbase (se 5 (by rfl) ⟨126593, by rfl⟩ : syracuseStep 2700661 = 253187) (by norm_num)
theorem B3601781 : Blo 1598998 3601781 := bbase (se 5 (by rfl) ⟨168833, by rfl⟩ : syracuseStep 3601781 = 337667) (by norm_num)
theorem B1799545 : Blo 1598998 1799545 := bbase (se 2 (by rfl) ⟨674829, by rfl⟩ : syracuseStep 1799545 = 1349659) (by norm_num)
theorem B3650933 : Blo 1598998 3650933 := bbase (se 5 (by rfl) ⟨171137, by rfl⟩ : syracuseStep 3650933 = 342275) (by norm_num)
theorem B1799581 : Blo 1598998 1799581 := bbase (se 3 (by rfl) ⟨337421, by rfl⟩ : syracuseStep 1799581 = 674843) (by norm_num)
theorem B4052389 : Blo 1598998 4052389 := bbase (se 4 (by rfl) ⟨379911, by rfl⟩ : syracuseStep 4052389 = 759823) (by norm_num)
theorem B8648117 : Blo 1598998 8648117 := bbase (se 5 (by rfl) ⟨405380, by rfl⟩ : syracuseStep 8648117 = 810761) (by norm_num)
theorem B3601853 : Blo 1598998 3601853 := bbase (se 3 (by rfl) ⟨675347, by rfl⟩ : syracuseStep 3601853 = 1350695) (by norm_num)
theorem B1799617 : Blo 1598998 1799617 := bbase (se 2 (by rfl) ⟨674856, by rfl⟩ : syracuseStep 1799617 = 1349713) (by norm_num)
theorem B2700749 : Blo 1598998 2700749 := bbase (se 3 (by rfl) ⟨506390, by rfl⟩ : syracuseStep 2700749 = 1012781) (by norm_num)
theorem B2561501 : Blo 1598998 2561501 := bbase (se 3 (by rfl) ⟨480281, by rfl⟩ : syracuseStep 2561501 = 960563) (by norm_num)
theorem B1799653 : Blo 1598998 1799653 := bbase (se 4 (by rfl) ⟨168717, by rfl⟩ : syracuseStep 1799653 = 337435) (by norm_num)
theorem B3601925 : Blo 1598998 3601925 := bbase (se 4 (by rfl) ⟨337680, by rfl⟩ : syracuseStep 3601925 = 675361) (by norm_num)
theorem B1799689 : Blo 1598998 1799689 := bbase (se 2 (by rfl) ⟨674883, by rfl⟩ : syracuseStep 1799689 = 1349767) (by norm_num)
theorem B1709581 : Blo 1598998 1709581 := bbase (se 3 (by rfl) ⟨320546, by rfl⟩ : syracuseStep 1709581 = 641093) (by norm_num)
theorem B4052501 : Blo 1598998 4052501 := bbase (se 6 (by rfl) ⟨94980, by rfl⟩ : syracuseStep 4052501 = 189961) (by norm_num)
theorem B1799725 : Blo 1598998 1799725 := bbase (se 3 (by rfl) ⟨337448, by rfl⟩ : syracuseStep 1799725 = 674897) (by norm_num)
theorem B1947205 : Blo 1598998 1947205 := bbase (se 4 (by rfl) ⟨182550, by rfl⟩ : syracuseStep 1947205 = 365101) (by norm_num)
theorem B2700877 : Blo 1598998 2700877 := bbase (se 3 (by rfl) ⟨506414, by rfl⟩ : syracuseStep 2700877 = 1012829) (by norm_num)
theorem B3601997 : Blo 1598998 3601997 := bbase (se 3 (by rfl) ⟨675374, by rfl⟩ : syracuseStep 3601997 = 1350749) (by norm_num)
theorem B1799761 : Blo 1598998 1799761 := bbase (se 2 (by rfl) ⟨674910, by rfl⟩ : syracuseStep 1799761 = 1349821) (by norm_num)
theorem B1799797 : Blo 1598998 1799797 := bbase (se 5 (by rfl) ⟨84365, by rfl⟩ : syracuseStep 1799797 = 168731) (by norm_num)
theorem B3602069 : Blo 1598998 3602069 := bbase (se 6 (by rfl) ⟨84423, by rfl⟩ : syracuseStep 3602069 = 168847) (by norm_num)
theorem B1799833 : Blo 1598998 1799833 := bbase (se 2 (by rfl) ⟨674937, by rfl⟩ : syracuseStep 1799833 = 1349875) (by norm_num)
theorem B2700965 : Blo 1598998 2700965 := bbase (se 4 (by rfl) ⟨253215, by rfl⟩ : syracuseStep 2700965 = 506431) (by norm_num)
theorem B1799869 : Blo 1598998 1799869 := bbase (se 3 (by rfl) ⟨337475, by rfl⟩ : syracuseStep 1799869 = 674951) (by norm_num)
theorem B3602141 : Blo 1598998 3602141 := bbase (se 3 (by rfl) ⟨675401, by rfl⟩ : syracuseStep 3602141 = 1350803) (by norm_num)
theorem B1799905 : Blo 1598998 1799905 := bbase (se 2 (by rfl) ⟨674964, by rfl⟩ : syracuseStep 1799905 = 1349929) (by norm_num)
theorem B1799941 : Blo 1598998 1799941 := bbase (se 4 (by rfl) ⟨168744, by rfl⟩ : syracuseStep 1799941 = 337489) (by norm_num)
theorem B2701093 : Blo 1598998 2701093 := bbase (se 4 (by rfl) ⟨253227, by rfl⟩ : syracuseStep 2701093 = 506455) (by norm_num)
theorem B3602213 : Blo 1598998 3602213 := bbase (se 4 (by rfl) ⟨337707, by rfl⟩ : syracuseStep 3602213 = 675415) (by norm_num)
theorem B1799977 : Blo 1598998 1799977 := bbase (se 2 (by rfl) ⟨674991, by rfl⟩ : syracuseStep 1799977 = 1349983) (by norm_num)
theorem B1800013 : Blo 1598998 1800013 := bbase (se 3 (by rfl) ⟨337502, by rfl⟩ : syracuseStep 1800013 = 675005) (by norm_num)
theorem B1800049 : Blo 1598998 1800049 := bbase (se 2 (by rfl) ⟨675018, by rfl⟩ : syracuseStep 1800049 = 1350037) (by norm_num)
theorem B2561917 : Blo 1598998 2561917 := bbase (se 3 (by rfl) ⟨480359, by rfl⟩ : syracuseStep 2561917 = 960719) (by norm_num)
theorem B2701181 : Blo 1598998 2701181 := bbase (se 3 (by rfl) ⟨506471, by rfl⟩ : syracuseStep 2701181 = 1012943) (by norm_num)
theorem B1800085 : Blo 1598998 1800085 := bbase (se 6 (by rfl) ⟨42189, by rfl⟩ : syracuseStep 1800085 = 84379) (by norm_num)
theorem B3463069 : Blo 1598998 3463069 := bbase (se 3 (by rfl) ⟨649325, by rfl⟩ : syracuseStep 3463069 = 1298651) (by norm_num)
theorem B1800121 : Blo 1598998 1800121 := bbase (se 2 (by rfl) ⟨675045, by rfl⟩ : syracuseStep 1800121 = 1350091) (by norm_num)
theorem B1800157 : Blo 1598998 1800157 := bbase (se 3 (by rfl) ⟨337529, by rfl⟩ : syracuseStep 1800157 = 675059) (by norm_num)
theorem B2701309 : Blo 1598998 2701309 := bbase (se 3 (by rfl) ⟨506495, by rfl⟩ : syracuseStep 2701309 = 1012991) (by norm_num)
theorem B1800193 : Blo 1598998 1800193 := bbase (se 2 (by rfl) ⟨675072, by rfl⟩ : syracuseStep 1800193 = 1350145) (by norm_num)
theorem B3037189 : Blo 1598998 3037189 := bbase (se 4 (by rfl) ⟨284736, by rfl⟩ : syracuseStep 3037189 = 569473) (by norm_num)
theorem B3078173 : Blo 1598998 3078173 := bbase (se 3 (by rfl) ⟨577157, by rfl⟩ : syracuseStep 3078173 = 1154315) (by norm_num)
theorem B1800229 : Blo 1598998 1800229 := bbase (se 4 (by rfl) ⟨168771, by rfl⟩ : syracuseStep 1800229 = 337543) (by norm_num)
theorem B1800265 : Blo 1598998 1800265 := bbase (se 2 (by rfl) ⟨675099, by rfl⟩ : syracuseStep 1800265 = 1350199) (by norm_num)
theorem B1923149 : Blo 1598998 1923149 := bbase (se 3 (by rfl) ⟨360590, by rfl⟩ : syracuseStep 1923149 = 721181) (by norm_num)
theorem B23074901 : Blo 1598998 23074901 := bbase (se 8 (by rfl) ⟨135204, by rfl⟩ : syracuseStep 23074901 = 270409) (by norm_num)
theorem B2701397 : Blo 1598998 2701397 := bbase (se 8 (by rfl) ⟨15828, by rfl⟩ : syracuseStep 2701397 = 31657) (by norm_num)
theorem B2922589 : Blo 1598998 2922589 := bbase (se 3 (by rfl) ⟨547985, by rfl⟩ : syracuseStep 2922589 = 1095971) (by norm_num)
theorem B8321125 : Blo 1598998 8321125 := bbase (se 4 (by rfl) ⟨780105, by rfl⟩ : syracuseStep 8321125 = 1560211) (by norm_num)
theorem B1800301 : Blo 1598998 1800301 := bbase (se 3 (by rfl) ⟨337556, by rfl⟩ : syracuseStep 1800301 = 675113) (by norm_num)
theorem B1800337 : Blo 1598998 1800337 := bbase (se 2 (by rfl) ⟨675126, by rfl⟩ : syracuseStep 1800337 = 1350253) (by norm_num)
theorem B3037333 : Blo 1598998 3037333 := bbase (se 6 (by rfl) ⟨71187, by rfl⟩ : syracuseStep 3037333 = 142375) (by norm_num)
theorem B6076565 : Blo 1598998 6076565 := bbase (se 6 (by rfl) ⟨142419, by rfl⟩ : syracuseStep 6076565 = 284839) (by norm_num)
theorem B1800373 : Blo 1598998 1800373 := bbase (se 5 (by rfl) ⟨84392, by rfl⟩ : syracuseStep 1800373 = 168785) (by norm_num)
theorem B4864213 : Blo 1598998 4864213 := bbase (se 7 (by rfl) ⟨57002, by rfl⟩ : syracuseStep 4864213 = 114005) (by norm_num)
theorem B2701525 : Blo 1598998 2701525 := bbase (se 7 (by rfl) ⟨31658, by rfl⟩ : syracuseStep 2701525 = 63317) (by norm_num)
theorem B1800409 : Blo 1598998 1800409 := bbase (se 2 (by rfl) ⟨675153, by rfl⟩ : syracuseStep 1800409 = 1350307) (by norm_num)
theorem B1800445 : Blo 1598998 1800445 := bbase (se 3 (by rfl) ⟨337583, by rfl⟩ : syracuseStep 1800445 = 675167) (by norm_num)
theorem B1800481 : Blo 1598998 1800481 := bbase (se 2 (by rfl) ⟨675180, by rfl⟩ : syracuseStep 1800481 = 1350361) (by norm_num)
theorem B2922797 : Blo 1598998 2922797 := bbase (se 3 (by rfl) ⟨548024, by rfl⟩ : syracuseStep 2922797 = 1096049) (by norm_num)
theorem B2701613 : Blo 1598998 2701613 := bbase (se 3 (by rfl) ⟨506552, by rfl⟩ : syracuseStep 2701613 = 1013105) (by norm_num)
theorem B2398517 : Blo 1598998 2398517 := bbase (se 5 (by rfl) ⟨112430, by rfl⟩ : syracuseStep 2398517 = 224861) (by norm_num)
theorem B3037493 : Blo 1598998 3037493 := bbase (se 5 (by rfl) ⟨142382, by rfl⟩ : syracuseStep 3037493 = 284765) (by norm_num)
theorem B1644853 : Blo 1598998 1644853 := bbase (se 5 (by rfl) ⟨77102, by rfl⟩ : syracuseStep 1644853 = 154205) (by norm_num)
theorem B1800517 : Blo 1598998 1800517 := bbase (se 4 (by rfl) ⟨168798, by rfl⟩ : syracuseStep 1800517 = 337597) (by norm_num)
theorem B2398541 : Blo 1598998 2398541 := bbase (se 3 (by rfl) ⟨449726, by rfl⟩ : syracuseStep 2398541 = 899453) (by norm_num)
theorem B41564501 : Blo 1598998 41564501 := bbase (se 10 (by rfl) ⟨60885, by rfl⟩ : syracuseStep 41564501 = 121771) (by norm_num)
theorem B6838613 : Blo 1598998 6838613 := bbase (se 10 (by rfl) ⟨10017, by rfl⟩ : syracuseStep 6838613 = 20035) (by norm_num)
theorem B2398565 : Blo 1598998 2398565 := bbase (se 4 (by rfl) ⟨224865, by rfl⟩ : syracuseStep 2398565 = 449731) (by norm_num)
theorem B1800553 : Blo 1598998 1800553 := bbase (se 2 (by rfl) ⟨675207, by rfl⟩ : syracuseStep 1800553 = 1350415) (by norm_num)
theorem B7297397 : Blo 1598998 7297397 := bbase (se 5 (by rfl) ⟨342065, by rfl⟩ : syracuseStep 7297397 = 684131) (by norm_num)
theorem B2398589 : Blo 1598998 2398589 := bbase (se 3 (by rfl) ⟨449735, by rfl⟩ : syracuseStep 2398589 = 899471) (by norm_num)
theorem B1800589 : Blo 1598998 1800589 := bbase (se 3 (by rfl) ⟨337610, by rfl⟩ : syracuseStep 1800589 = 675221) (by norm_num)
theorem B2398613 : Blo 1598998 2398613 := bbase (se 6 (by rfl) ⟨56217, by rfl⟩ : syracuseStep 2398613 = 112435) (by norm_num)
theorem B2398637 : Blo 1598998 2398637 := bbase (se 3 (by rfl) ⟨449744, by rfl⟩ : syracuseStep 2398637 = 899489) (by norm_num)
theorem B1800625 : Blo 1598998 1800625 := bbase (se 2 (by rfl) ⟨675234, by rfl⟩ : syracuseStep 1800625 = 1350469) (by norm_num)
theorem B6076853 : Blo 1598998 6076853 := bbase (se 5 (by rfl) ⟨284852, by rfl⟩ : syracuseStep 6076853 = 569705) (by norm_num)
theorem B2398661 : Blo 1598998 2398661 := bbase (se 4 (by rfl) ⟨224874, by rfl⟩ : syracuseStep 2398661 = 449749) (by norm_num)
theorem B3037637 : Blo 1598998 3037637 := bbase (se 4 (by rfl) ⟨284778, by rfl⟩ : syracuseStep 3037637 = 569557) (by norm_num)
theorem B1800661 : Blo 1598998 1800661 := bbase (se 7 (by rfl) ⟨21101, by rfl⟩ : syracuseStep 1800661 = 42203) (by norm_num)
theorem B2398685 : Blo 1598998 2398685 := bbase (se 3 (by rfl) ⟨449753, by rfl⟩ : syracuseStep 2398685 = 899507) (by norm_num)
theorem B2398709 : Blo 1598998 2398709 := bbase (se 5 (by rfl) ⟨112439, by rfl⟩ : syracuseStep 2398709 = 224879) (by norm_num)
theorem B1800697 : Blo 1598998 1800697 := bbase (se 2 (by rfl) ⟨675261, by rfl⟩ : syracuseStep 1800697 = 1350523) (by norm_num)
theorem B7297541 : Blo 1598998 7297541 := bbase (se 4 (by rfl) ⟨684144, by rfl⟩ : syracuseStep 7297541 = 1368289) (by norm_num)
theorem B2398733 : Blo 1598998 2398733 := bbase (se 3 (by rfl) ⟨449762, by rfl⟩ : syracuseStep 2398733 = 899525) (by norm_num)
theorem B2161181 : Blo 1598998 2161181 := bbase (se 3 (by rfl) ⟨405221, by rfl⟩ : syracuseStep 2161181 = 810443) (by norm_num)
theorem B1800733 : Blo 1598998 1800733 := bbase (se 3 (by rfl) ⟨337637, by rfl⟩ : syracuseStep 1800733 = 675275) (by norm_num)
theorem B5397029 : Blo 1598998 5397029 := bbase (se 4 (by rfl) ⟨505971, by rfl⟩ : syracuseStep 5397029 = 1011943) (by norm_num)
theorem B2398757 : Blo 1598998 2398757 := bbase (se 4 (by rfl) ⟨224883, by rfl⟩ : syracuseStep 2398757 = 449767) (by norm_num)
theorem B2398781 : Blo 1598998 2398781 := bbase (se 3 (by rfl) ⟨449771, by rfl⟩ : syracuseStep 2398781 = 899543) (by norm_num)
theorem B3463741 : Blo 1598998 3463741 := bbase (se 3 (by rfl) ⟨649451, by rfl⟩ : syracuseStep 3463741 = 1298903) (by norm_num)
theorem B1800769 : Blo 1598998 1800769 := bbase (se 2 (by rfl) ⟨675288, by rfl⟩ : syracuseStep 1800769 = 1350577) (by norm_num)
theorem B2398805 : Blo 1598998 2398805 := bbase (se 8 (by rfl) ⟨14055, by rfl⟩ : syracuseStep 2398805 = 28111) (by norm_num)
theorem B1800805 : Blo 1598998 1800805 := bbase (se 4 (by rfl) ⟨168825, by rfl⟩ : syracuseStep 1800805 = 337651) (by norm_num)
theorem B2398829 : Blo 1598998 2398829 := bbase (se 3 (by rfl) ⟨449780, by rfl⟩ : syracuseStep 2398829 = 899561) (by norm_num)
theorem B2398853 : Blo 1598998 2398853 := bbase (se 4 (by rfl) ⟨224892, by rfl⟩ : syracuseStep 2398853 = 449785) (by norm_num)
theorem B8100485 : Blo 1598998 8100485 := bbase (se 4 (by rfl) ⟨759420, by rfl⟩ : syracuseStep 8100485 = 1518841) (by norm_num)
theorem B1800841 : Blo 1598998 1800841 := bbase (se 2 (by rfl) ⟨675315, by rfl⟩ : syracuseStep 1800841 = 1350631) (by norm_num)
theorem B2398877 : Blo 1598998 2398877 := bbase (se 3 (by rfl) ⟨449789, by rfl⟩ : syracuseStep 2398877 = 899579) (by norm_num)
theorem B1800877 : Blo 1598998 1800877 := bbase (se 3 (by rfl) ⟨337664, by rfl⟩ : syracuseStep 1800877 = 675329) (by norm_num)
theorem B2398901 : Blo 1598998 2398901 := bbase (se 5 (by rfl) ⟨112448, by rfl⟩ : syracuseStep 2398901 = 224897) (by norm_num)
theorem B5765813 : Blo 1598998 5765813 := bbase (se 5 (by rfl) ⟨270272, by rfl⟩ : syracuseStep 5765813 = 540545) (by norm_num)
theorem B2398925 : Blo 1598998 2398925 := bbase (se 3 (by rfl) ⟨449798, by rfl⟩ : syracuseStep 2398925 = 899597) (by norm_num)
theorem B1800913 : Blo 1598998 1800913 := bbase (se 2 (by rfl) ⟨675342, by rfl⟩ : syracuseStep 1800913 = 1350685) (by norm_num)
theorem B6830821 : Blo 1598998 6830821 := bbase (se 4 (by rfl) ⟨640389, by rfl⟩ : syracuseStep 6830821 = 1280779) (by norm_num)
theorem B2398949 : Blo 1598998 2398949 := bbase (se 4 (by rfl) ⟨224901, by rfl⟩ : syracuseStep 2398949 = 449803) (by norm_num)
theorem B3037925 : Blo 1598998 3037925 := bbase (se 4 (by rfl) ⟨284805, by rfl⟩ : syracuseStep 3037925 = 569611) (by norm_num)
theorem B1800949 : Blo 1598998 1800949 := bbase (se 5 (by rfl) ⟨84419, by rfl⟩ : syracuseStep 1800949 = 168839) (by norm_num)
theorem B2398973 : Blo 1598998 2398973 := bbase (se 3 (by rfl) ⟨449807, by rfl⟩ : syracuseStep 2398973 = 899615) (by norm_num)
theorem B2398997 : Blo 1598998 2398997 := bbase (se 6 (by rfl) ⟨56226, by rfl⟩ : syracuseStep 2398997 = 112453) (by norm_num)
theorem B1800985 : Blo 1598998 1800985 := bbase (se 2 (by rfl) ⟨675369, by rfl⟩ : syracuseStep 1800985 = 1350739) (by norm_num)
theorem B2562853 : Blo 1598998 2562853 := bbase (se 4 (by rfl) ⟨240267, by rfl⟩ : syracuseStep 2562853 = 480535) (by norm_num)
theorem B4102957 : Blo 1598998 4102957 := bbase (se 3 (by rfl) ⟨769304, by rfl⟩ : syracuseStep 4102957 = 1538609) (by norm_num)
theorem B2399021 : Blo 1598998 2399021 := bbase (se 3 (by rfl) ⟨449816, by rfl⟩ : syracuseStep 2399021 = 899633) (by norm_num)
theorem B1801021 : Blo 1598998 1801021 := bbase (se 3 (by rfl) ⟨337691, by rfl⟩ : syracuseStep 1801021 = 675383) (by norm_num)
theorem B2399045 : Blo 1598998 2399045 := bbase (se 4 (by rfl) ⟨224910, by rfl⟩ : syracuseStep 2399045 = 449821) (by norm_num)
theorem B2399069 : Blo 1598998 2399069 := bbase (se 3 (by rfl) ⟨449825, by rfl⟩ : syracuseStep 2399069 = 899651) (by norm_num)
theorem B1801057 : Blo 1598998 1801057 := bbase (se 2 (by rfl) ⟨675396, by rfl⟩ : syracuseStep 1801057 = 1350793) (by norm_num)
theorem B2399093 : Blo 1598998 2399093 := bbase (se 5 (by rfl) ⟨112457, by rfl⟩ : syracuseStep 2399093 = 224915) (by norm_num)
theorem B3038077 : Blo 1598998 3038077 := bbase (se 3 (by rfl) ⟨569639, by rfl⟩ : syracuseStep 3038077 = 1139279) (by norm_num)
theorem B1801093 : Blo 1598998 1801093 := bbase (se 4 (by rfl) ⟨168852, by rfl⟩ : syracuseStep 1801093 = 337705) (by norm_num)
theorem B2399117 : Blo 1598998 2399117 := bbase (se 3 (by rfl) ⟨449834, by rfl⟩ : syracuseStep 2399117 = 899669) (by norm_num)
theorem B2882461 : Blo 1598998 2882461 := bbase (se 3 (by rfl) ⟨540461, by rfl⟩ : syracuseStep 2882461 = 1080923) (by norm_num)
theorem B2399141 : Blo 1598998 2399141 := bbase (se 4 (by rfl) ⟨224919, by rfl⟩ : syracuseStep 2399141 = 449839) (by norm_num)
theorem B4553653 : Blo 1598998 4553653 := bbase (se 5 (by rfl) ⟨213452, by rfl⟩ : syracuseStep 4553653 = 426905) (by norm_num)
theorem B2399165 : Blo 1598998 2399165 := bbase (se 3 (by rfl) ⟨449843, by rfl⟩ : syracuseStep 2399165 = 899687) (by norm_num)
theorem B1850321 : Blo 1598998 1850321 := bbase (se 2 (by rfl) ⟨693870, by rfl⟩ : syracuseStep 1850321 = 1387741) (by norm_num)
theorem B5397461 : Blo 1598998 5397461 := bbase (se 7 (by rfl) ⟨63251, by rfl⟩ : syracuseStep 5397461 = 126503) (by norm_num)
theorem B2399189 : Blo 1598998 2399189 := bbase (se 7 (by rfl) ⟨28115, by rfl⟩ : syracuseStep 2399189 = 56231) (by norm_num)
theorem B2399213 : Blo 1598998 2399213 := bbase (se 3 (by rfl) ⟨449852, by rfl⟩ : syracuseStep 2399213 = 899705) (by norm_num)
theorem B2399237 : Blo 1598998 2399237 := bbase (se 4 (by rfl) ⟨224928, by rfl⟩ : syracuseStep 2399237 = 449857) (by norm_num)
theorem B7691269 : Blo 1598998 7691269 := bbase (se 4 (by rfl) ⟨721056, by rfl⟩ : syracuseStep 7691269 = 1442113) (by norm_num)
theorem B3415061 : Blo 1598998 3415061 := bbase (se 6 (by rfl) ⟨80040, by rfl⟩ : syracuseStep 3415061 = 160081) (by norm_num)
theorem B3415069 : Blo 1598998 3415069 := bbase (se 3 (by rfl) ⟨640325, by rfl⟩ : syracuseStep 3415069 = 1280651) (by norm_num)
theorem B2399261 : Blo 1598998 2399261 := bbase (se 3 (by rfl) ⟨449861, by rfl⟩ : syracuseStep 2399261 = 899723) (by norm_num)
theorem B2399285 : Blo 1598998 2399285 := bbase (se 5 (by rfl) ⟨112466, by rfl⟩ : syracuseStep 2399285 = 224933) (by norm_num)
theorem B2399309 : Blo 1598998 2399309 := bbase (se 3 (by rfl) ⟨449870, by rfl⟩ : syracuseStep 2399309 = 899741) (by norm_num)
theorem B4553813 : Blo 1598998 4553813 := bbase (se 8 (by rfl) ⟨26682, by rfl⟩ : syracuseStep 4553813 = 53365) (by norm_num)
theorem B2399333 : Blo 1598998 2399333 := bbase (se 4 (by rfl) ⟨224937, by rfl⟩ : syracuseStep 2399333 = 449875) (by norm_num)
theorem B2399357 : Blo 1598998 2399357 := bbase (se 3 (by rfl) ⟨449879, by rfl⟩ : syracuseStep 2399357 = 899759) (by norm_num)
theorem B2399381 : Blo 1598998 2399381 := bbase (se 6 (by rfl) ⟨56235, by rfl⟩ : syracuseStep 2399381 = 112471) (by norm_num)
theorem B2399405 : Blo 1598998 2399405 := bbase (se 3 (by rfl) ⟨449888, by rfl⟩ : syracuseStep 2399405 = 899777) (by norm_num)
theorem B3038381 : Blo 1598998 3038381 := bbase (se 3 (by rfl) ⟨569696, by rfl⟩ : syracuseStep 3038381 = 1139393) (by norm_num)
theorem B1621181 : Blo 1598998 1621181 := bbase (se 3 (by rfl) ⟨303971, by rfl⟩ : syracuseStep 1621181 = 607943) (by norm_num)
theorem B2882749 : Blo 1598998 2882749 := bbase (se 3 (by rfl) ⟨540515, by rfl⟩ : syracuseStep 2882749 = 1081031) (by norm_num)
theorem B2399429 : Blo 1598998 2399429 := bbase (se 4 (by rfl) ⟨224946, by rfl⟩ : syracuseStep 2399429 = 449893) (by norm_num)
theorem B2399453 : Blo 1598998 2399453 := bbase (se 3 (by rfl) ⟨449897, by rfl⟩ : syracuseStep 2399453 = 899795) (by norm_num)
theorem B2399477 : Blo 1598998 2399477 := bbase (se 5 (by rfl) ⟨112475, by rfl⟩ : syracuseStep 2399477 = 224951) (by norm_num)
theorem B2399501 : Blo 1598998 2399501 := bbase (se 3 (by rfl) ⟨449906, by rfl⟩ : syracuseStep 2399501 = 899813) (by norm_num)
theorem B2399525 : Blo 1598998 2399525 := bbase (se 4 (by rfl) ⟨224955, by rfl⟩ : syracuseStep 2399525 = 449911) (by norm_num)
theorem B2399549 : Blo 1598998 2399549 := bbase (se 3 (by rfl) ⟨449915, by rfl⟩ : syracuseStep 2399549 = 899831) (by norm_num)
theorem B4554053 : Blo 1598998 4554053 := bbase (se 4 (by rfl) ⟨426942, by rfl⟩ : syracuseStep 4554053 = 853885) (by norm_num)
theorem B2399573 : Blo 1598998 2399573 := bbase (se 11 (by rfl) ⟨1757, by rfl⟩ : syracuseStep 2399573 = 3515) (by norm_num)
theorem B1949017 : Blo 1598998 1949017 := bbase (se 2 (by rfl) ⟨730881, by rfl⟩ : syracuseStep 1949017 = 1461763) (by norm_num)
theorem B2399597 : Blo 1598998 2399597 := bbase (se 3 (by rfl) ⟨449924, by rfl⟩ : syracuseStep 2399597 = 899849) (by norm_num)
theorem B5397893 : Blo 1598998 5397893 := bbase (se 4 (by rfl) ⟨506052, by rfl⟩ : syracuseStep 5397893 = 1012105) (by norm_num)
theorem B2399621 : Blo 1598998 2399621 := bbase (se 4 (by rfl) ⟨224964, by rfl⟩ : syracuseStep 2399621 = 449929) (by norm_num)
theorem B2399645 : Blo 1598998 2399645 := bbase (se 3 (by rfl) ⟨449933, by rfl⟩ : syracuseStep 2399645 = 899867) (by norm_num)
theorem B2399669 : Blo 1598998 2399669 := bbase (se 5 (by rfl) ⟨112484, by rfl⟩ : syracuseStep 2399669 = 224969) (by norm_num)
theorem B2399693 : Blo 1598998 2399693 := bbase (se 3 (by rfl) ⟨449942, by rfl⟩ : syracuseStep 2399693 = 899885) (by norm_num)
theorem B2399717 : Blo 1598998 2399717 := bbase (se 4 (by rfl) ⟨224973, by rfl⟩ : syracuseStep 2399717 = 449947) (by norm_num)
theorem B2399741 : Blo 1598998 2399741 := bbase (se 3 (by rfl) ⟨449951, by rfl⟩ : syracuseStep 2399741 = 899903) (by norm_num)
theorem B4554245 : Blo 1598998 4554245 := bbase (se 4 (by rfl) ⟨426960, by rfl⟩ : syracuseStep 4554245 = 853921) (by norm_num)
theorem B2399765 : Blo 1598998 2399765 := bbase (se 6 (by rfl) ⟨56244, by rfl⟩ : syracuseStep 2399765 = 112489) (by norm_num)
theorem B2399789 : Blo 1598998 2399789 := bbase (se 3 (by rfl) ⟨449960, by rfl⟩ : syracuseStep 2399789 = 899921) (by norm_num)
theorem B2399813 : Blo 1598998 2399813 := bbase (se 4 (by rfl) ⟨224982, by rfl⟩ : syracuseStep 2399813 = 449965) (by norm_num)
theorem B13663829 : Blo 1598998 13663829 := bbase (se 8 (by rfl) ⟨80061, by rfl⟩ : syracuseStep 13663829 = 160123) (by norm_num)
theorem B6078037 : Blo 1598998 6078037 := bbase (se 8 (by rfl) ⟨35613, by rfl⟩ : syracuseStep 6078037 = 71227) (by norm_num)
theorem B2399837 : Blo 1598998 2399837 := bbase (se 3 (by rfl) ⟨449969, by rfl⟩ : syracuseStep 2399837 = 899939) (by norm_num)
theorem B5127781 : Blo 1598998 5127781 := bbase (se 4 (by rfl) ⟨480729, by rfl⟩ : syracuseStep 5127781 = 961459) (by norm_num)
theorem B2399861 : Blo 1598998 2399861 := bbase (se 5 (by rfl) ⟨112493, by rfl⟩ : syracuseStep 2399861 = 224987) (by norm_num)
theorem B2399885 : Blo 1598998 2399885 := bbase (se 3 (by rfl) ⟨449978, by rfl⟩ : syracuseStep 2399885 = 899957) (by norm_num)
theorem B2399909 : Blo 1598998 2399909 := bbase (se 4 (by rfl) ⟨224991, by rfl⟩ : syracuseStep 2399909 = 449983) (by norm_num)
theorem B2399933 : Blo 1598998 2399933 := bbase (se 3 (by rfl) ⟨449987, by rfl⟩ : syracuseStep 2399933 = 899975) (by norm_num)
theorem B2277077 : Blo 1598998 2277077 := bbase (se 7 (by rfl) ⟨26684, by rfl⟩ : syracuseStep 2277077 = 53369) (by norm_num)
theorem B2399957 : Blo 1598998 2399957 := bbase (se 7 (by rfl) ⟨28124, by rfl⟩ : syracuseStep 2399957 = 56249) (by norm_num)
theorem B1621729 : Blo 1598998 1621729 := bbase (se 2 (by rfl) ⟨608148, by rfl⟩ : syracuseStep 1621729 = 1216297) (by norm_num)
theorem B2399981 : Blo 1598998 2399981 := bbase (se 3 (by rfl) ⟨449996, by rfl⟩ : syracuseStep 2399981 = 899993) (by norm_num)
theorem B2400005 : Blo 1598998 2400005 := bbase (se 4 (by rfl) ⟨225000, by rfl⟩ : syracuseStep 2400005 = 450001) (by norm_num)
theorem B2400029 : Blo 1598998 2400029 := bbase (se 3 (by rfl) ⟨450005, by rfl⟩ : syracuseStep 2400029 = 900011) (by norm_num)
theorem B5398325 : Blo 1598998 5398325 := bbase (se 5 (by rfl) ⟨253046, by rfl⟩ : syracuseStep 5398325 = 506093) (by norm_num)
theorem B2400053 : Blo 1598998 2400053 := bbase (se 5 (by rfl) ⟨112502, by rfl⟩ : syracuseStep 2400053 = 225005) (by norm_num)
theorem B2400077 : Blo 1598998 2400077 := bbase (se 3 (by rfl) ⟨450014, by rfl⟩ : syracuseStep 2400077 = 900029) (by norm_num)
theorem B2400101 : Blo 1598998 2400101 := bbase (se 4 (by rfl) ⟨225009, by rfl⟩ : syracuseStep 2400101 = 450019) (by norm_num)
theorem B5128037 : Blo 1598998 5128037 := bbase (se 4 (by rfl) ⟨480753, by rfl⟩ : syracuseStep 5128037 = 961507) (by norm_num)
theorem B2400125 : Blo 1598998 2400125 := bbase (se 3 (by rfl) ⟨450023, by rfl⟩ : syracuseStep 2400125 = 900047) (by norm_num)
theorem B6078341 : Blo 1598998 6078341 := bbase (se 4 (by rfl) ⟨569844, by rfl⟩ : syracuseStep 6078341 = 1139689) (by norm_num)
theorem B2400149 : Blo 1598998 2400149 := bbase (se 6 (by rfl) ⟨56253, by rfl⟩ : syracuseStep 2400149 = 112507) (by norm_num)
theorem B8101781 : Blo 1598998 8101781 := bbase (se 6 (by rfl) ⟨189885, by rfl⟩ : syracuseStep 8101781 = 379771) (by norm_num)
theorem B3039133 : Blo 1598998 3039133 := bbase (se 3 (by rfl) ⟨569837, by rfl⟩ : syracuseStep 3039133 = 1139675) (by norm_num)
theorem B2400173 : Blo 1598998 2400173 := bbase (se 3 (by rfl) ⟨450032, by rfl⟩ : syracuseStep 2400173 = 900065) (by norm_num)
theorem B2400197 : Blo 1598998 2400197 := bbase (se 4 (by rfl) ⟨225018, by rfl⟩ : syracuseStep 2400197 = 450037) (by norm_num)
theorem B2564045 : Blo 1598998 2564045 := bbase (se 3 (by rfl) ⟨480758, by rfl⟩ : syracuseStep 2564045 = 961517) (by norm_num)
theorem B2883541 : Blo 1598998 2883541 := bbase (se 7 (by rfl) ⟨33791, by rfl⟩ : syracuseStep 2883541 = 67583) (by norm_num)
theorem B2400221 : Blo 1598998 2400221 := bbase (se 3 (by rfl) ⟨450041, by rfl⟩ : syracuseStep 2400221 = 900083) (by norm_num)
theorem B9109493 : Blo 1598998 9109493 := bbase (se 5 (by rfl) ⟨427007, by rfl⟩ : syracuseStep 9109493 = 854015) (by norm_num)
theorem B2400245 : Blo 1598998 2400245 := bbase (se 5 (by rfl) ⟨112511, by rfl⟩ : syracuseStep 2400245 = 225023) (by norm_num)
theorem B2400257 : Blo 1598998 2400257 := bstep (se 2 (by rfl) ⟨900096, by rfl⟩ : syracuseStep 2400257 = 1800193) B1800193
theorem B5398541 : Blo 1598998 5398541 := bstep (se 3 (by rfl) ⟨1012226, by rfl⟩ : syracuseStep 5398541 = 2024453) B2024453
theorem B2400275 : Blo 1598998 2400275 := bstep (se 1 (by rfl) ⟨1800206, by rfl⟩ : syracuseStep 2400275 = 3600413) B3600413
theorem B9732145 : Blo 1598998 9732145 := bstep (se 2 (by rfl) ⟨3649554, by rfl⟩ : syracuseStep 9732145 = 7299109) B7299109
theorem B2400305 : Blo 1598998 2400305 := bstep (se 2 (by rfl) ⟨900114, by rfl⟩ : syracuseStep 2400305 = 1800229) B1800229
theorem B5398595 : Blo 1598998 5398595 := bstep (se 1 (by rfl) ⟨4048946, by rfl⟩ : syracuseStep 5398595 = 8097893) B8097893
theorem B2400323 : Blo 1598998 2400323 := bstep (se 1 (by rfl) ⟨1800242, by rfl⟩ : syracuseStep 2400323 = 3600485) B3600485
theorem B8208461 : Blo 1598998 8208461 := bstep (se 3 (by rfl) ⟨1539086, by rfl⟩ : syracuseStep 8208461 = 3078173) B3078173
theorem B2400353 : Blo 1598998 2400353 := bstep (se 2 (by rfl) ⟨900132, by rfl⟩ : syracuseStep 2400353 = 1800265) B1800265
theorem B21635171 : Blo 1598998 21635171 := bstep (se 1 (by rfl) ⟨16226378, by rfl⟩ : syracuseStep 21635171 = 32452757) B32452757
theorem B10256483 : Blo 1598998 10256483 := bstep (se 1 (by rfl) ⟨7692362, by rfl⟩ : syracuseStep 10256483 = 15384725) B15384725
theorem B2400371 : Blo 1598998 2400371 := bstep (se 1 (by rfl) ⟨1800278, by rfl⟩ : syracuseStep 2400371 = 3600557) B3600557
theorem B4554883 : Blo 1598998 4554883 := bstep (se 1 (by rfl) ⟨3416162, by rfl⟩ : syracuseStep 4554883 = 6832325) B6832325
theorem B2400401 : Blo 1598998 2400401 := bstep (se 2 (by rfl) ⟨900150, by rfl⟩ : syracuseStep 2400401 = 1800301) B1800301
theorem B2400419 : Blo 1598998 2400419 := bstep (se 1 (by rfl) ⟨1800314, by rfl⟩ : syracuseStep 2400419 = 3600629) B3600629
theorem B4554929 : Blo 1598998 4554929 := bstep (se 2 (by rfl) ⟨1708098, by rfl⟩ : syracuseStep 4554929 = 3416197) B3416197
theorem B2400449 : Blo 1598998 2400449 := bstep (se 2 (by rfl) ⟨900168, by rfl⟩ : syracuseStep 2400449 = 1800337) B1800337
theorem B5128397 : Blo 1598998 5128397 := bstep (se 3 (by rfl) ⟨961574, by rfl⟩ : syracuseStep 5128397 = 1923149) B1923149
theorem B2400467 : Blo 1598998 2400467 := bstep (se 1 (by rfl) ⟨1800350, by rfl⟩ : syracuseStep 2400467 = 3600701) B3600701
theorem B9109745 : Blo 1598998 9109745 := bstep (se 2 (by rfl) ⟨3416154, by rfl⟩ : syracuseStep 9109745 = 6832309) B6832309
theorem B2400497 : Blo 1598998 2400497 := bstep (se 2 (by rfl) ⟨900186, by rfl⟩ : syracuseStep 2400497 = 1800373) B1800373
theorem B2400515 : Blo 1598998 2400515 := bstep (se 1 (by rfl) ⟨1800386, by rfl⟩ : syracuseStep 2400515 = 3600773) B3600773
theorem B2400545 : Blo 1598998 2400545 := bstep (se 2 (by rfl) ⟨900204, by rfl⟩ : syracuseStep 2400545 = 1800409) B1800409
theorem B2400563 : Blo 1598998 2400563 := bstep (se 1 (by rfl) ⟨1800422, by rfl⟩ : syracuseStep 2400563 = 3600845) B3600845
theorem B18473285 : Blo 1598998 18473285 := bstep (se 4 (by rfl) ⟨1731870, by rfl⟩ : syracuseStep 18473285 = 3463741) B3463741
theorem B5398865 : Blo 1598998 5398865 := bstep (se 2 (by rfl) ⟨2024574, by rfl⟩ : syracuseStep 5398865 = 4049149) B4049149
theorem B2400593 : Blo 1598998 2400593 := bstep (se 2 (by rfl) ⟨900222, by rfl⟩ : syracuseStep 2400593 = 1800445) B1800445
theorem B2277715 : Blo 1598998 2277715 := bstep (se 1 (by rfl) ⟨1708286, by rfl⟩ : syracuseStep 2277715 = 3416573) B3416573
theorem B2400611 : Blo 1598998 2400611 := bstep (se 1 (by rfl) ⟨1800458, by rfl⟩ : syracuseStep 2400611 = 3600917) B3600917
theorem B2023795 : Blo 1598998 2023795 := bstep (se 1 (by rfl) ⟨1517846, by rfl⟩ : syracuseStep 2023795 = 3035693) B3035693
theorem B2400641 : Blo 1598998 2400641 := bstep (se 2 (by rfl) ⟨900240, by rfl⟩ : syracuseStep 2400641 = 1800481) B1800481
theorem B8651141 : Blo 1598998 8651141 := bstep (se 4 (by rfl) ⟨811044, by rfl⟩ : syracuseStep 8651141 = 1622089) B1622089
theorem B2400659 : Blo 1598998 2400659 := bstep (se 1 (by rfl) ⟨1800494, by rfl⟩ : syracuseStep 2400659 = 3600989) B3600989
theorem B2400689 : Blo 1598998 2400689 := bstep (se 2 (by rfl) ⟨900258, by rfl⟩ : syracuseStep 2400689 = 1800517) B1800517
theorem B2400707 : Blo 1598998 2400707 := bstep (se 1 (by rfl) ⟨1800530, by rfl⟩ : syracuseStep 2400707 = 3601061) B3601061
theorem B2400737 : Blo 1598998 2400737 := bstep (se 2 (by rfl) ⟨900276, by rfl⟩ : syracuseStep 2400737 = 1800553) B1800553
theorem B2400755 : Blo 1598998 2400755 := bstep (se 1 (by rfl) ⟨1800566, by rfl⟩ : syracuseStep 2400755 = 3601133) B3601133
theorem B2400785 : Blo 1598998 2400785 := bstep (se 2 (by rfl) ⟨900294, by rfl⟩ : syracuseStep 2400785 = 1800589) B1800589
theorem B2400803 : Blo 1598998 2400803 := bstep (se 1 (by rfl) ⟨1800602, by rfl⟩ : syracuseStep 2400803 = 3601205) B3601205
theorem B2400833 : Blo 1598998 2400833 := bstep (se 2 (by rfl) ⟨900312, by rfl⟩ : syracuseStep 2400833 = 1800625) B1800625
theorem B2400851 : Blo 1598998 2400851 := bstep (se 1 (by rfl) ⟨1800638, by rfl⟩ : syracuseStep 2400851 = 3601277) B3601277
theorem B2138707 : Blo 1598998 2138707 := bstep (se 1 (by rfl) ⟨1604030, by rfl⟩ : syracuseStep 2138707 = 3208061) B3208061
theorem B9732707 : Blo 1598998 9732707 := bstep (se 1 (by rfl) ⟨7299530, by rfl⟩ : syracuseStep 9732707 = 14599061) B14599061
theorem B2400881 : Blo 1598998 2400881 := bstep (se 2 (by rfl) ⟨900330, by rfl⟩ : syracuseStep 2400881 = 1800661) B1800661
theorem B2400899 : Blo 1598998 2400899 := bstep (se 1 (by rfl) ⟨1800674, by rfl⟩ : syracuseStep 2400899 = 3601349) B3601349
theorem B2400929 : Blo 1598998 2400929 := bstep (se 2 (by rfl) ⟨900348, by rfl⟩ : syracuseStep 2400929 = 1800697) B1800697
theorem B2400947 : Blo 1598998 2400947 := bstep (se 1 (by rfl) ⟨1800710, by rfl⟩ : syracuseStep 2400947 = 3601421) B3601421
theorem B2400977 : Blo 1598998 2400977 := bstep (se 2 (by rfl) ⟨900366, by rfl⟩ : syracuseStep 2400977 = 1800733) B1800733
theorem B2400995 : Blo 1598998 2400995 := bstep (se 1 (by rfl) ⟨1800746, by rfl⟩ : syracuseStep 2400995 = 3601493) B3601493
theorem B2401025 : Blo 1598998 2401025 := bstep (se 2 (by rfl) ⟨900384, by rfl⟩ : syracuseStep 2401025 = 1800769) B1800769
theorem B2401043 : Blo 1598998 2401043 := bstep (se 1 (by rfl) ⟨1800782, by rfl⟩ : syracuseStep 2401043 = 3601565) B3601565
theorem B8209187 : Blo 1598998 8209187 := bstep (se 1 (by rfl) ⟨6156890, by rfl⟩ : syracuseStep 8209187 = 12313781) B12313781
theorem B4866851 : Blo 1598998 4866851 := bstep (se 1 (by rfl) ⟨3650138, by rfl⟩ : syracuseStep 4866851 = 7300277) B7300277
theorem B8209201 : Blo 1598998 8209201 := bstep (se 2 (by rfl) ⟨3078450, by rfl⟩ : syracuseStep 8209201 = 6156901) B6156901
theorem B2401073 : Blo 1598998 2401073 := bstep (se 2 (by rfl) ⟨900402, by rfl⟩ : syracuseStep 2401073 = 1800805) B1800805
theorem B2401091 : Blo 1598998 2401091 := bstep (se 1 (by rfl) ⟨1800818, by rfl⟩ : syracuseStep 2401091 = 3601637) B3601637
theorem B2401121 : Blo 1598998 2401121 := bstep (se 2 (by rfl) ⟨900420, by rfl⟩ : syracuseStep 2401121 = 1800841) B1800841
theorem B2024291 : Blo 1598998 2024291 := bstep (se 1 (by rfl) ⟨1518218, by rfl⟩ : syracuseStep 2024291 = 3036437) B3036437
theorem B5399405 : Blo 1598998 5399405 := bstep (se 3 (by rfl) ⟨1012388, by rfl⟩ : syracuseStep 5399405 = 2024777) B2024777
theorem B29197169 : Blo 1598998 29197169 := bstep (se 2 (by rfl) ⟨10948938, by rfl⟩ : syracuseStep 29197169 = 21897877) B21897877
theorem B2401139 : Blo 1598998 2401139 := bstep (se 1 (by rfl) ⟨1800854, by rfl⟩ : syracuseStep 2401139 = 3601709) B3601709
theorem B2433907 : Blo 1598998 2433907 := bstep (se 1 (by rfl) ⟨1825430, by rfl⟩ : syracuseStep 2433907 = 3650861) B3650861
theorem B2401169 : Blo 1598998 2401169 := bstep (se 2 (by rfl) ⟨900438, by rfl⟩ : syracuseStep 2401169 = 1800877) B1800877
theorem B5399459 : Blo 1598998 5399459 := bstep (se 1 (by rfl) ⟨4049594, by rfl⟩ : syracuseStep 5399459 = 8099189) B8099189
theorem B2401187 : Blo 1598998 2401187 := bstep (se 1 (by rfl) ⟨1800890, by rfl⟩ : syracuseStep 2401187 = 3601781) B3601781
theorem B2401217 : Blo 1598998 2401217 := bstep (se 2 (by rfl) ⟨900456, by rfl⟩ : syracuseStep 2401217 = 1800913) B1800913
theorem B2401235 : Blo 1598998 2401235 := bstep (se 1 (by rfl) ⟨1800926, by rfl⟩ : syracuseStep 2401235 = 3601853) B3601853
theorem B2401265 : Blo 1598998 2401265 := bstep (se 2 (by rfl) ⟨900474, by rfl⟩ : syracuseStep 2401265 = 1800949) B1800949
theorem B2401283 : Blo 1598998 2401283 := bstep (se 1 (by rfl) ⟨1800962, by rfl⟩ : syracuseStep 2401283 = 3601925) B3601925
theorem B2401313 : Blo 1598998 2401313 := bstep (se 2 (by rfl) ⟨900492, by rfl⟩ : syracuseStep 2401313 = 1800985) B1800985
theorem B3417137 : Blo 1598998 3417137 := bstep (se 2 (by rfl) ⟨1281426, by rfl⟩ : syracuseStep 3417137 = 2562853) B2562853
theorem B2401331 : Blo 1598998 2401331 := bstep (se 1 (by rfl) ⟨1800998, by rfl⟩ : syracuseStep 2401331 = 3601997) B3601997
theorem B2401361 : Blo 1598998 2401361 := bstep (se 2 (by rfl) ⟨900510, by rfl⟩ : syracuseStep 2401361 = 1801021) B1801021
theorem B2401379 : Blo 1598998 2401379 := bstep (se 1 (by rfl) ⟨1801034, by rfl⟩ : syracuseStep 2401379 = 3602069) B3602069
theorem B2401409 : Blo 1598998 2401409 := bstep (se 2 (by rfl) ⟨900528, by rfl⟩ : syracuseStep 2401409 = 1801057) B1801057
theorem B2401427 : Blo 1598998 2401427 := bstep (se 1 (by rfl) ⟨1801070, by rfl⟩ : syracuseStep 2401427 = 3602141) B3602141
theorem B5399729 : Blo 1598998 5399729 := bstep (se 2 (by rfl) ⟨2024898, by rfl⟩ : syracuseStep 5399729 = 4049797) B4049797
theorem B5473457 : Blo 1598998 5473457 := bstep (se 2 (by rfl) ⟨2052546, by rfl⟩ : syracuseStep 5473457 = 4105093) B4105093
theorem B2401457 : Blo 1598998 2401457 := bstep (se 2 (by rfl) ⟨900546, by rfl⟩ : syracuseStep 2401457 = 1801093) B1801093
theorem B2401475 : Blo 1598998 2401475 := bstep (se 1 (by rfl) ⟨1801106, by rfl⟩ : syracuseStep 2401475 = 3602213) B3602213
theorem B3843281 : Blo 1598998 3843281 := bstep (se 2 (by rfl) ⟨1441230, by rfl⟩ : syracuseStep 3843281 = 2882461) B2882461
theorem B6071537 : Blo 1598998 6071537 := bstep (se 2 (by rfl) ⟨2276826, by rfl⟩ : syracuseStep 6071537 = 4553653) B4553653
theorem B4678897 : Blo 1598998 4678897 := bstep (se 2 (by rfl) ⟨1754586, by rfl⟩ : syracuseStep 4678897 = 3509173) B3509173
theorem B20776205 : Blo 1598998 20776205 := bstep (se 3 (by rfl) ⟨3895538, by rfl⟩ : syracuseStep 20776205 = 7791077) B7791077
theorem B4048177 : Blo 1598998 4048177 := bstep (se 2 (by rfl) ⟨1518066, by rfl⟩ : syracuseStep 4048177 = 3036133) B3036133
theorem B5268817 : Blo 1598998 5268817 := bstep (se 2 (by rfl) ⟨1975806, by rfl⟩ : syracuseStep 5268817 = 3951613) B3951613
theorem B8095139 : Blo 1598998 8095139 := bstep (se 1 (by rfl) ⟨6071354, by rfl⟩ : syracuseStep 8095139 = 12142709) B12142709
theorem B2278849 : Blo 1598998 2278849 := bstep (se 2 (by rfl) ⟨854568, by rfl⟩ : syracuseStep 2278849 = 1709137) B1709137
theorem B4867523 : Blo 1598998 4867523 := bstep (se 1 (by rfl) ⟨3650642, by rfl⟩ : syracuseStep 4867523 = 7301285) B7301285
theorem B2278945 : Blo 1598998 2278945 := bstep (se 2 (by rfl) ⟨854604, by rfl⟩ : syracuseStep 2278945 = 1709209) B1709209
theorem B1599011 : Blo 1598998 1599011 := bstep (se 1 (by rfl) ⟨1199258, by rfl⟩ : syracuseStep 1599011 = 2398517) B2398517
theorem B2024995 : Blo 1598998 2024995 := bstep (se 1 (by rfl) ⟨1518746, by rfl⟩ : syracuseStep 2024995 = 3037493) B3037493
theorem B1599027 : Blo 1598998 1599027 := bstep (se 1 (by rfl) ⟨1199270, by rfl⟩ : syracuseStep 1599027 = 2398541) B2398541
theorem B1599043 : Blo 1598998 1599043 := bstep (se 1 (by rfl) ⟨1199282, by rfl⟩ : syracuseStep 1599043 = 2398565) B2398565
theorem B4048451 : Blo 1598998 4048451 := bstep (se 1 (by rfl) ⟨3036338, by rfl⟩ : syracuseStep 4048451 = 6072677) B6072677
theorem B3843665 : Blo 1598998 3843665 := bstep (se 2 (by rfl) ⟨1441374, by rfl⟩ : syracuseStep 3843665 = 2882749) B2882749
theorem B1599059 : Blo 1598998 1599059 := bstep (se 1 (by rfl) ⟨1199294, by rfl⟩ : syracuseStep 1599059 = 2398589) B2398589
theorem B1599075 : Blo 1598998 1599075 := bstep (se 1 (by rfl) ⟨1199306, by rfl⟩ : syracuseStep 1599075 = 2398613) B2398613
theorem B4556387 : Blo 1598998 4556387 := bstep (se 1 (by rfl) ⟨3417290, by rfl⟩ : syracuseStep 4556387 = 6834581) B6834581
theorem B1599091 : Blo 1598998 1599091 := bstep (se 1 (by rfl) ⟨1199318, by rfl⟩ : syracuseStep 1599091 = 2398637) B2398637
theorem B1599107 : Blo 1598998 1599107 := bstep (se 1 (by rfl) ⟨1199330, by rfl⟩ : syracuseStep 1599107 = 2398661) B2398661
theorem B2025091 : Blo 1598998 2025091 := bstep (se 1 (by rfl) ⟨1518818, by rfl⟩ : syracuseStep 2025091 = 3037637) B3037637
theorem B1599123 : Blo 1598998 1599123 := bstep (se 1 (by rfl) ⟨1199342, by rfl⟩ : syracuseStep 1599123 = 2398685) B2398685
theorem B1599139 : Blo 1598998 1599139 := bstep (se 1 (by rfl) ⟨1199354, by rfl⟩ : syracuseStep 1599139 = 2398709) B2398709
theorem B9111203 : Blo 1598998 9111203 := bstep (se 1 (by rfl) ⟨6833402, by rfl⟩ : syracuseStep 9111203 = 13666805) B13666805
theorem B3598001 : Blo 1598998 3598001 := bstep (se 2 (by rfl) ⟨1349250, by rfl⟩ : syracuseStep 3598001 = 2698501) B2698501
theorem B1599155 : Blo 1598998 1599155 := bstep (se 1 (by rfl) ⟨1199366, by rfl⟩ : syracuseStep 1599155 = 2398733) B2398733
theorem B3598019 : Blo 1598998 3598019 := bstep (se 1 (by rfl) ⟨2698514, by rfl⟩ : syracuseStep 3598019 = 5397029) B5397029
theorem B1599171 : Blo 1598998 1599171 := bstep (se 1 (by rfl) ⟨1199378, by rfl⟩ : syracuseStep 1599171 = 2398757) B2398757
theorem B5400269 : Blo 1598998 5400269 := bstep (se 3 (by rfl) ⟨1012550, by rfl⟩ : syracuseStep 5400269 = 2025101) B2025101
theorem B1599187 : Blo 1598998 1599187 := bstep (se 1 (by rfl) ⟨1199390, by rfl⟩ : syracuseStep 1599187 = 2398781) B2398781
theorem B1599203 : Blo 1598998 1599203 := bstep (se 1 (by rfl) ⟨1199402, by rfl⟩ : syracuseStep 1599203 = 2398805) B2398805
theorem B1599219 : Blo 1598998 1599219 := bstep (se 1 (by rfl) ⟨1199414, by rfl⟩ : syracuseStep 1599219 = 2398829) B2398829
theorem B1599235 : Blo 1598998 1599235 := bstep (se 1 (by rfl) ⟨1199426, by rfl⟩ : syracuseStep 1599235 = 2398853) B2398853
theorem B4048643 : Blo 1598998 4048643 := bstep (se 1 (by rfl) ⟨3036482, by rfl⟩ : syracuseStep 4048643 = 6072965) B6072965
theorem B5400323 : Blo 1598998 5400323 := bstep (se 1 (by rfl) ⟨4050242, by rfl⟩ : syracuseStep 5400323 = 8100485) B8100485
theorem B1599251 : Blo 1598998 1599251 := bstep (se 1 (by rfl) ⟨1199438, by rfl⟩ : syracuseStep 1599251 = 2398877) B2398877
theorem B2598689 : Blo 1598998 2598689 := bstep (se 2 (by rfl) ⟨974508, by rfl⟩ : syracuseStep 2598689 = 1949017) B1949017
theorem B1599267 : Blo 1598998 1599267 := bstep (se 1 (by rfl) ⟨1199450, by rfl⟩ : syracuseStep 1599267 = 2398901) B2398901
theorem B3843875 : Blo 1598998 3843875 := bstep (se 1 (by rfl) ⟨2882906, by rfl⟩ : syracuseStep 3843875 = 5765813) B5765813
theorem B1599283 : Blo 1598998 1599283 := bstep (se 1 (by rfl) ⟨1199462, by rfl⟩ : syracuseStep 1599283 = 2398925) B2398925
theorem B1599299 : Blo 1598998 1599299 := bstep (se 1 (by rfl) ⟨1199474, by rfl⟩ : syracuseStep 1599299 = 2398949) B2398949
theorem B1599315 : Blo 1598998 1599315 := bstep (se 1 (by rfl) ⟨1199486, by rfl⟩ : syracuseStep 1599315 = 2398973) B2398973
theorem B1599331 : Blo 1598998 1599331 := bstep (se 1 (by rfl) ⟨1199498, by rfl⟩ : syracuseStep 1599331 = 2398997) B2398997
theorem B1599347 : Blo 1598998 1599347 := bstep (se 1 (by rfl) ⟨1199510, by rfl⟩ : syracuseStep 1599347 = 2399021) B2399021
theorem B1599363 : Blo 1598998 1599363 := bstep (se 1 (by rfl) ⟨1199522, by rfl⟩ : syracuseStep 1599363 = 2399045) B2399045
theorem B6072205 : Blo 1598998 6072205 := bstep (se 3 (by rfl) ⟨1138538, by rfl⟩ : syracuseStep 6072205 = 2277077) B2277077
theorem B1599379 : Blo 1598998 1599379 := bstep (se 1 (by rfl) ⟨1199534, by rfl⟩ : syracuseStep 1599379 = 2399069) B2399069
theorem B1599395 : Blo 1598998 1599395 := bstep (se 1 (by rfl) ⟨1199546, by rfl⟩ : syracuseStep 1599395 = 2399093) B2399093
theorem B1599411 : Blo 1598998 1599411 := bstep (se 1 (by rfl) ⟨1199558, by rfl⟩ : syracuseStep 1599411 = 2399117) B2399117
theorem B1599427 : Blo 1598998 1599427 := bstep (se 1 (by rfl) ⟨1199570, by rfl⟩ : syracuseStep 1599427 = 2399141) B2399141
theorem B3598289 : Blo 1598998 3598289 := bstep (se 2 (by rfl) ⟨1349358, by rfl⟩ : syracuseStep 3598289 = 2698717) B2698717
theorem B1599443 : Blo 1598998 1599443 := bstep (se 1 (by rfl) ⟨1199582, by rfl⟩ : syracuseStep 1599443 = 2399165) B2399165
theorem B3598307 : Blo 1598998 3598307 := bstep (se 1 (by rfl) ⟨2698730, by rfl⟩ : syracuseStep 3598307 = 5397461) B5397461
theorem B1599459 : Blo 1598998 1599459 := bstep (se 1 (by rfl) ⟨1199594, by rfl⟩ : syracuseStep 1599459 = 2399189) B2399189
theorem B1599475 : Blo 1598998 1599475 := bstep (se 1 (by rfl) ⟨1199606, by rfl⟩ : syracuseStep 1599475 = 2399213) B2399213
theorem B1599491 : Blo 1598998 1599491 := bstep (se 1 (by rfl) ⟨1199618, by rfl⟩ : syracuseStep 1599491 = 2399237) B2399237
theorem B5400593 : Blo 1598998 5400593 := bstep (se 2 (by rfl) ⟨2025222, by rfl⟩ : syracuseStep 5400593 = 4050445) B4050445
theorem B2279441 : Blo 1598998 2279441 := bstep (se 2 (by rfl) ⟨854790, by rfl⟩ : syracuseStep 2279441 = 1709581) B1709581
theorem B1599507 : Blo 1598998 1599507 := bstep (se 1 (by rfl) ⟨1199630, by rfl⟩ : syracuseStep 1599507 = 2399261) B2399261
theorem B1599523 : Blo 1598998 1599523 := bstep (se 1 (by rfl) ⟨1199642, by rfl⟩ : syracuseStep 1599523 = 2399285) B2399285
theorem B1599539 : Blo 1598998 1599539 := bstep (se 1 (by rfl) ⟨1199654, by rfl⟩ : syracuseStep 1599539 = 2399309) B2399309
theorem B1599555 : Blo 1598998 1599555 := bstep (se 1 (by rfl) ⟨1199666, by rfl⟩ : syracuseStep 1599555 = 2399333) B2399333
theorem B1599571 : Blo 1598998 1599571 := bstep (se 1 (by rfl) ⟨1199678, by rfl⟩ : syracuseStep 1599571 = 2399357) B2399357
theorem B1599587 : Blo 1598998 1599587 := bstep (se 1 (by rfl) ⟨1199690, by rfl⟩ : syracuseStep 1599587 = 2399381) B2399381
theorem B17303665 : Blo 1598998 17303665 := bstep (se 2 (by rfl) ⟨6488874, by rfl⟩ : syracuseStep 17303665 = 12977749) B12977749
theorem B8104049 : Blo 1598998 8104049 := bstep (se 2 (by rfl) ⟨3039018, by rfl⟩ : syracuseStep 8104049 = 6078037) B6078037
theorem B1599603 : Blo 1598998 1599603 := bstep (se 1 (by rfl) ⟨1199702, by rfl⟩ : syracuseStep 1599603 = 2399405) B2399405
theorem B2025587 : Blo 1598998 2025587 := bstep (se 1 (by rfl) ⟨1519190, by rfl⟩ : syracuseStep 2025587 = 3038381) B3038381
theorem B1599619 : Blo 1598998 1599619 := bstep (se 1 (by rfl) ⟨1199714, by rfl⟩ : syracuseStep 1599619 = 2399429) B2399429
theorem B1599635 : Blo 1598998 1599635 := bstep (se 1 (by rfl) ⟨1199726, by rfl⟩ : syracuseStep 1599635 = 2399453) B2399453
theorem B1599651 : Blo 1598998 1599651 := bstep (se 1 (by rfl) ⟨1199738, by rfl⟩ : syracuseStep 1599651 = 2399477) B2399477
theorem B1599667 : Blo 1598998 1599667 := bstep (se 1 (by rfl) ⟨1199750, by rfl⟩ : syracuseStep 1599667 = 2399501) B2399501
theorem B1599683 : Blo 1598998 1599683 := bstep (se 1 (by rfl) ⟨1199762, by rfl⟩ : syracuseStep 1599683 = 2399525) B2399525
theorem B8095949 : Blo 1598998 8095949 := bstep (se 3 (by rfl) ⟨1517990, by rfl⟩ : syracuseStep 8095949 = 3035981) B3035981
theorem B1599699 : Blo 1598998 1599699 := bstep (se 1 (by rfl) ⟨1199774, by rfl⟩ : syracuseStep 1599699 = 2399549) B2399549
theorem B1599715 : Blo 1598998 1599715 := bstep (se 1 (by rfl) ⟨1199786, by rfl⟩ : syracuseStep 1599715 = 2399573) B2399573
theorem B3598577 : Blo 1598998 3598577 := bstep (se 2 (by rfl) ⟨1349466, by rfl⟩ : syracuseStep 3598577 = 2698933) B2698933
theorem B1599731 : Blo 1598998 1599731 := bstep (se 1 (by rfl) ⟨1199798, by rfl⟩ : syracuseStep 1599731 = 2399597) B2399597
theorem B3598595 : Blo 1598998 3598595 := bstep (se 1 (by rfl) ⟨2698946, by rfl⟩ : syracuseStep 3598595 = 5397893) B5397893
theorem B1599747 : Blo 1598998 1599747 := bstep (se 1 (by rfl) ⟨1199810, by rfl⟩ : syracuseStep 1599747 = 2399621) B2399621
theorem B1599763 : Blo 1598998 1599763 := bstep (se 1 (by rfl) ⟨1199822, by rfl⟩ : syracuseStep 1599763 = 2399645) B2399645
theorem B1599779 : Blo 1598998 1599779 := bstep (se 1 (by rfl) ⟨1199834, by rfl⟩ : syracuseStep 1599779 = 2399669) B2399669
theorem B1599795 : Blo 1598998 1599795 := bstep (se 1 (by rfl) ⟨1199846, by rfl⟩ : syracuseStep 1599795 = 2399693) B2399693
theorem B1599811 : Blo 1598998 1599811 := bstep (se 1 (by rfl) ⟨1199858, by rfl⟩ : syracuseStep 1599811 = 2399717) B2399717
theorem B1599827 : Blo 1598998 1599827 := bstep (se 1 (by rfl) ⟨1199870, by rfl⟩ : syracuseStep 1599827 = 2399741) B2399741
theorem B1599843 : Blo 1598998 1599843 := bstep (se 1 (by rfl) ⟨1199882, by rfl⟩ : syracuseStep 1599843 = 2399765) B2399765
theorem B1599859 : Blo 1598998 1599859 := bstep (se 1 (by rfl) ⟨1199894, by rfl⟩ : syracuseStep 1599859 = 2399789) B2399789
theorem B1599875 : Blo 1598998 1599875 := bstep (se 1 (by rfl) ⟨1199906, by rfl⟩ : syracuseStep 1599875 = 2399813) B2399813
theorem B1599891 : Blo 1598998 1599891 := bstep (se 1 (by rfl) ⟨1199918, by rfl⟩ : syracuseStep 1599891 = 2399837) B2399837
theorem B1599907 : Blo 1598998 1599907 := bstep (se 1 (by rfl) ⟨1199930, by rfl⟩ : syracuseStep 1599907 = 2399861) B2399861
theorem B1599923 : Blo 1598998 1599923 := bstep (se 1 (by rfl) ⟨1199942, by rfl⟩ : syracuseStep 1599923 = 2399885) B2399885
theorem B1599939 : Blo 1598998 1599939 := bstep (se 1 (by rfl) ⟨1199954, by rfl⟩ : syracuseStep 1599939 = 2399909) B2399909
theorem B1599955 : Blo 1598998 1599955 := bstep (se 1 (by rfl) ⟨1199966, by rfl⟩ : syracuseStep 1599955 = 2399933) B2399933
theorem B1599971 : Blo 1598998 1599971 := bstep (se 1 (by rfl) ⟨1199978, by rfl⟩ : syracuseStep 1599971 = 2399957) B2399957
theorem B1599987 : Blo 1598998 1599987 := bstep (se 1 (by rfl) ⟨1199990, by rfl⟩ : syracuseStep 1599987 = 2399981) B2399981
theorem B1600003 : Blo 1598998 1600003 := bstep (se 1 (by rfl) ⟨1200002, by rfl⟩ : syracuseStep 1600003 = 2400005) B2400005
theorem B3598865 : Blo 1598998 3598865 := bstep (se 2 (by rfl) ⟨1349574, by rfl⟩ : syracuseStep 3598865 = 2699149) B2699149
theorem B1600019 : Blo 1598998 1600019 := bstep (se 1 (by rfl) ⟨1200014, by rfl⟩ : syracuseStep 1600019 = 2400029) B2400029
theorem B3598883 : Blo 1598998 3598883 := bstep (se 1 (by rfl) ⟨2699162, by rfl⟩ : syracuseStep 3598883 = 5398325) B5398325
theorem B1600035 : Blo 1598998 1600035 := bstep (se 1 (by rfl) ⟨1200026, by rfl⟩ : syracuseStep 1600035 = 2400053) B2400053
theorem B5401133 : Blo 1598998 5401133 := bstep (se 3 (by rfl) ⟨1012712, by rfl⟩ : syracuseStep 5401133 = 2025425) B2025425
theorem B4934189 : Blo 1598998 4934189 := bstep (se 3 (by rfl) ⟨925160, by rfl⟩ : syracuseStep 4934189 = 1850321) B1850321
theorem B1600051 : Blo 1598998 1600051 := bstep (se 1 (by rfl) ⟨1200038, by rfl⟩ : syracuseStep 1600051 = 2400077) B2400077
theorem B1600067 : Blo 1598998 1600067 := bstep (se 1 (by rfl) ⟨1200050, by rfl⟩ : syracuseStep 1600067 = 2400101) B2400101
theorem B3418691 : Blo 1598998 3418691 := bstep (se 1 (by rfl) ⟨2564018, by rfl⟩ : syracuseStep 3418691 = 5128037) B5128037
theorem B1600083 : Blo 1598998 1600083 := bstep (se 1 (by rfl) ⟨1200062, by rfl⟩ : syracuseStep 1600083 = 2400125) B2400125
theorem B1600099 : Blo 1598998 1600099 := bstep (se 1 (by rfl) ⟨1200074, by rfl⟩ : syracuseStep 1600099 = 2400149) B2400149
theorem B5401187 : Blo 1598998 5401187 := bstep (se 1 (by rfl) ⟨4050890, by rfl⟩ : syracuseStep 5401187 = 8101781) B8101781
theorem B20515427 : Blo 1598998 20515427 := bstep (se 1 (by rfl) ⟨15386570, by rfl⟩ : syracuseStep 20515427 = 30773141) B30773141
theorem B3844721 : Blo 1598998 3844721 := bstep (se 2 (by rfl) ⟨1441770, by rfl⟩ : syracuseStep 3844721 = 2883541) B2883541
theorem B1600115 : Blo 1598998 1600115 := bstep (se 1 (by rfl) ⟨1200086, by rfl⟩ : syracuseStep 1600115 = 2400173) B2400173
theorem B1600131 : Blo 1598998 1600131 := bstep (se 1 (by rfl) ⟨1200098, by rfl⟩ : syracuseStep 1600131 = 2400197) B2400197
theorem B7023245 : Blo 1598998 7023245 := bstep (se 3 (by rfl) ⟨1316858, by rfl⟩ : syracuseStep 7023245 = 2633717) B2633717
theorem B1600147 : Blo 1598998 1600147 := bstep (se 1 (by rfl) ⟨1200110, by rfl⟩ : syracuseStep 1600147 = 2400221) B2400221
theorem B6072995 : Blo 1598998 6072995 := bstep (se 1 (by rfl) ⟨4554746, by rfl⟩ : syracuseStep 6072995 = 9109493) B9109493
theorem B1600163 : Blo 1598998 1600163 := bstep (se 1 (by rfl) ⟨1200122, by rfl⟩ : syracuseStep 1600163 = 2400245) B2400245
theorem B4049585 : Blo 1598998 4049585 := bstep (se 2 (by rfl) ⟨1518594, by rfl⟩ : syracuseStep 4049585 = 3037189) B3037189
theorem B1600179 : Blo 1598998 1600179 := bstep (se 1 (by rfl) ⟨1200134, by rfl⟩ : syracuseStep 1600179 = 2400269) B2400269
theorem B1600195 : Blo 1598998 1600195 := bstep (se 1 (by rfl) ⟨1200146, by rfl⟩ : syracuseStep 1600195 = 2400293) B2400293
theorem B1600211 : Blo 1598998 1600211 := bstep (se 1 (by rfl) ⟨1200158, by rfl⟩ : syracuseStep 1600211 = 2400317) B2400317
theorem B4049635 : Blo 1598998 4049635 := bstep (se 1 (by rfl) ⟨3037226, by rfl⟩ : syracuseStep 4049635 = 6074453) B6074453
theorem B1600227 : Blo 1598998 1600227 := bstep (se 1 (by rfl) ⟨1200170, by rfl⟩ : syracuseStep 1600227 = 2400341) B2400341
theorem B3648241 : Blo 1598998 3648241 := bstep (se 2 (by rfl) ⟨1368090, by rfl⟩ : syracuseStep 3648241 = 2736181) B2736181
theorem B1600243 : Blo 1598998 1600243 := bstep (se 1 (by rfl) ⟨1200182, by rfl⟩ : syracuseStep 1600243 = 2400365) B2400365
theorem B1600259 : Blo 1598998 1600259 := bstep (se 1 (by rfl) ⟨1200194, by rfl⟩ : syracuseStep 1600259 = 2400389) B2400389
theorem B1600275 : Blo 1598998 1600275 := bstep (se 1 (by rfl) ⟨1200206, by rfl⟩ : syracuseStep 1600275 = 2400413) B2400413
theorem B1600291 : Blo 1598998 1600291 := bstep (se 1 (by rfl) ⟨1200218, by rfl⟩ : syracuseStep 1600291 = 2400437) B2400437
theorem B3599153 : Blo 1598998 3599153 := bstep (se 2 (by rfl) ⟨1349682, by rfl⟩ : syracuseStep 3599153 = 2699365) B2699365
theorem B11094833 : Blo 1598998 11094833 := bstep (se 2 (by rfl) ⟨4160562, by rfl⟩ : syracuseStep 11094833 = 8321125) B8321125
theorem B3844913 : Blo 1598998 3844913 := bstep (se 2 (by rfl) ⟨1441842, by rfl⟩ : syracuseStep 3844913 = 2883685) B2883685
theorem B1600307 : Blo 1598998 1600307 := bstep (se 1 (by rfl) ⟨1200230, by rfl⟩ : syracuseStep 1600307 = 2400461) B2400461
theorem B4557617 : Blo 1598998 4557617 := bstep (se 2 (by rfl) ⟨1709106, by rfl⟩ : syracuseStep 4557617 = 3418213) B3418213
theorem B3599171 : Blo 1598998 3599171 := bstep (se 1 (by rfl) ⟨2699378, by rfl⟩ : syracuseStep 3599171 = 5398757) B5398757
theorem B1600323 : Blo 1598998 1600323 := bstep (se 1 (by rfl) ⟨1200242, by rfl⟩ : syracuseStep 1600323 = 2400485) B2400485
theorem B1600339 : Blo 1598998 1600339 := bstep (se 1 (by rfl) ⟨1200254, by rfl⟩ : syracuseStep 1600339 = 2400509) B2400509
theorem B6835043 : Blo 1598998 6835043 := bstep (se 1 (by rfl) ⟨5126282, by rfl⟩ : syracuseStep 6835043 = 10252565) B10252565
theorem B1600355 : Blo 1598998 1600355 := bstep (se 1 (by rfl) ⟨1200266, by rfl⟩ : syracuseStep 1600355 = 2400533) B2400533
theorem B4049777 : Blo 1598998 4049777 := bstep (se 2 (by rfl) ⟨1518666, by rfl⟩ : syracuseStep 4049777 = 3037333) B3037333
theorem B5401457 : Blo 1598998 5401457 := bstep (se 2 (by rfl) ⟨2025546, by rfl⟩ : syracuseStep 5401457 = 4051093) B4051093
theorem B1600371 : Blo 1598998 1600371 := bstep (se 1 (by rfl) ⟨1200278, by rfl⟩ : syracuseStep 1600371 = 2400557) B2400557
theorem B1600387 : Blo 1598998 1600387 := bstep (se 1 (by rfl) ⟨1200290, by rfl⟩ : syracuseStep 1600387 = 2400581) B2400581
theorem B1600403 : Blo 1598998 1600403 := bstep (se 1 (by rfl) ⟨1200302, by rfl⟩ : syracuseStep 1600403 = 2400605) B2400605
theorem B1600419 : Blo 1598998 1600419 := bstep (se 1 (by rfl) ⟨1200314, by rfl⟩ : syracuseStep 1600419 = 2400629) B2400629
theorem B1600435 : Blo 1598998 1600435 := bstep (se 1 (by rfl) ⟨1200326, by rfl⟩ : syracuseStep 1600435 = 2400653) B2400653
theorem B1600451 : Blo 1598998 1600451 := bstep (se 1 (by rfl) ⟨1200338, by rfl⟩ : syracuseStep 1600451 = 2400677) B2400677
theorem B1600467 : Blo 1598998 1600467 := bstep (se 1 (by rfl) ⟨1200350, by rfl⟩ : syracuseStep 1600467 = 2400701) B2400701
theorem B1600483 : Blo 1598998 1600483 := bstep (se 1 (by rfl) ⟨1200362, by rfl⟩ : syracuseStep 1600483 = 2400725) B2400725
theorem B1600499 : Blo 1598998 1600499 := bstep (se 1 (by rfl) ⟨1200374, by rfl⟩ : syracuseStep 1600499 = 2400749) B2400749
theorem B1600515 : Blo 1598998 1600515 := bstep (se 1 (by rfl) ⟨1200386, by rfl⟩ : syracuseStep 1600515 = 2400773) B2400773
theorem B1600531 : Blo 1598998 1600531 := bstep (se 1 (by rfl) ⟨1200398, by rfl⟩ : syracuseStep 1600531 = 2400797) B2400797
theorem B1600547 : Blo 1598998 1600547 := bstep (se 1 (by rfl) ⟨1200410, by rfl⟩ : syracuseStep 1600547 = 2400821) B2400821
theorem B1600563 : Blo 1598998 1600563 := bstep (se 1 (by rfl) ⟨1200422, by rfl⟩ : syracuseStep 1600563 = 2400845) B2400845
theorem B1600579 : Blo 1598998 1600579 := bstep (se 1 (by rfl) ⟨1200434, by rfl⟩ : syracuseStep 1600579 = 2400869) B2400869
theorem B3599441 : Blo 1598998 3599441 := bstep (se 2 (by rfl) ⟨1349790, by rfl⟩ : syracuseStep 3599441 = 2699581) B2699581
theorem B1600595 : Blo 1598998 1600595 := bstep (se 1 (by rfl) ⟨1200446, by rfl⟩ : syracuseStep 1600595 = 2400893) B2400893
theorem B2698339 : Blo 1598998 2698339 := bstep (se 1 (by rfl) ⟨2023754, by rfl⟩ : syracuseStep 2698339 = 4047509) B4047509
theorem B3599459 : Blo 1598998 3599459 := bstep (se 1 (by rfl) ⟨2699594, by rfl⟩ : syracuseStep 3599459 = 5399189) B5399189
theorem B1600611 : Blo 1598998 1600611 := bstep (se 1 (by rfl) ⟨1200458, by rfl⟩ : syracuseStep 1600611 = 2400917) B2400917
theorem B1600627 : Blo 1598998 1600627 := bstep (se 1 (by rfl) ⟨1200470, by rfl⟩ : syracuseStep 1600627 = 2400941) B2400941
theorem B1600643 : Blo 1598998 1600643 := bstep (se 1 (by rfl) ⟨1200482, by rfl⟩ : syracuseStep 1600643 = 2400965) B2400965
theorem B1600659 : Blo 1598998 1600659 := bstep (se 1 (by rfl) ⟨1200494, by rfl⟩ : syracuseStep 1600659 = 2400989) B2400989
theorem B1600675 : Blo 1598998 1600675 := bstep (se 1 (by rfl) ⟨1200506, by rfl⟩ : syracuseStep 1600675 = 2401013) B2401013
theorem B5123245 : Blo 1598998 5123245 := bstep (se 3 (by rfl) ⟨960608, by rfl⟩ : syracuseStep 5123245 = 1921217) B1921217
theorem B1600691 : Blo 1598998 1600691 := bstep (se 1 (by rfl) ⟨1200518, by rfl⟩ : syracuseStep 1600691 = 2401037) B2401037
theorem B1600707 : Blo 1598998 1600707 := bstep (se 1 (by rfl) ⟨1200530, by rfl⟩ : syracuseStep 1600707 = 2401061) B2401061
theorem B10251461 : Blo 1598998 10251461 := bstep (se 4 (by rfl) ⟨961074, by rfl⟩ : syracuseStep 10251461 = 1922149) B1922149
theorem B1600723 : Blo 1598998 1600723 := bstep (se 1 (by rfl) ⟨1200542, by rfl⟩ : syracuseStep 1600723 = 2401085) B2401085
theorem B1600739 : Blo 1598998 1600739 := bstep (se 1 (by rfl) ⟨1200554, by rfl⟩ : syracuseStep 1600739 = 2401109) B2401109
theorem B2698481 : Blo 1598998 2698481 := bstep (se 2 (by rfl) ⟨1011930, by rfl⟩ : syracuseStep 2698481 = 2023861) B2023861
theorem B1600755 : Blo 1598998 1600755 := bstep (se 1 (by rfl) ⟨1200566, by rfl⟩ : syracuseStep 1600755 = 2401133) B2401133
theorem B1600771 : Blo 1598998 1600771 := bstep (se 1 (by rfl) ⟨1200578, by rfl⟩ : syracuseStep 1600771 = 2401157) B2401157
theorem B1600787 : Blo 1598998 1600787 := bstep (se 1 (by rfl) ⟨1200590, by rfl⟩ : syracuseStep 1600787 = 2401181) B2401181
theorem B1600803 : Blo 1598998 1600803 := bstep (se 1 (by rfl) ⟨1200602, by rfl⟩ : syracuseStep 1600803 = 2401205) B2401205
theorem B6073649 : Blo 1598998 6073649 := bstep (se 2 (by rfl) ⟨2277618, by rfl⟩ : syracuseStep 6073649 = 4555237) B4555237
theorem B1600819 : Blo 1598998 1600819 := bstep (se 1 (by rfl) ⟨1200614, by rfl⟩ : syracuseStep 1600819 = 2401229) B2401229
theorem B1600835 : Blo 1598998 1600835 := bstep (se 1 (by rfl) ⟨1200626, by rfl⟩ : syracuseStep 1600835 = 2401253) B2401253
theorem B1600851 : Blo 1598998 1600851 := bstep (se 1 (by rfl) ⟨1200638, by rfl⟩ : syracuseStep 1600851 = 2401277) B2401277
theorem B1600867 : Blo 1598998 1600867 := bstep (se 1 (by rfl) ⟨1200650, by rfl⟩ : syracuseStep 1600867 = 2401301) B2401301
theorem B2698609 : Blo 1598998 2698609 := bstep (se 2 (by rfl) ⟨1011978, by rfl⟩ : syracuseStep 2698609 = 2023957) B2023957
theorem B3599729 : Blo 1598998 3599729 := bstep (se 2 (by rfl) ⟨1349898, by rfl⟩ : syracuseStep 3599729 = 2699797) B2699797
theorem B1600883 : Blo 1598998 1600883 := bstep (se 1 (by rfl) ⟨1200662, by rfl⟩ : syracuseStep 1600883 = 2401325) B2401325
theorem B3599747 : Blo 1598998 3599747 := bstep (se 1 (by rfl) ⟨2699810, by rfl⟩ : syracuseStep 3599747 = 5399621) B5399621
theorem B1600899 : Blo 1598998 1600899 := bstep (se 1 (by rfl) ⟨1200674, by rfl⟩ : syracuseStep 1600899 = 2401349) B2401349
theorem B5401997 : Blo 1598998 5401997 := bstep (se 3 (by rfl) ⟨1012874, by rfl⟩ : syracuseStep 5401997 = 2025749) B2025749
theorem B2698643 : Blo 1598998 2698643 := bstep (se 1 (by rfl) ⟨2023982, by rfl⟩ : syracuseStep 2698643 = 4047965) B4047965
theorem B1600915 : Blo 1598998 1600915 := bstep (se 1 (by rfl) ⟨1200686, by rfl⟩ : syracuseStep 1600915 = 2401373) B2401373
theorem B1600931 : Blo 1598998 1600931 := bstep (se 1 (by rfl) ⟨1200698, by rfl⟩ : syracuseStep 1600931 = 2401397) B2401397
theorem B1600947 : Blo 1598998 1600947 := bstep (se 1 (by rfl) ⟨1200710, by rfl⟩ : syracuseStep 1600947 = 2401421) B2401421
theorem B5402051 : Blo 1598998 5402051 := bstep (se 1 (by rfl) ⟨4051538, by rfl⟩ : syracuseStep 5402051 = 8103077) B8103077
theorem B1600963 : Blo 1598998 1600963 := bstep (se 1 (by rfl) ⟨1200722, by rfl⟩ : syracuseStep 1600963 = 2401445) B2401445
theorem B1600979 : Blo 1598998 1600979 := bstep (se 1 (by rfl) ⟨1200734, by rfl⟩ : syracuseStep 1600979 = 2401469) B2401469
theorem B1600995 : Blo 1598998 1600995 := bstep (se 1 (by rfl) ⟨1200746, by rfl⟩ : syracuseStep 1600995 = 2401493) B2401493
theorem B9113093 : Blo 1598998 9113093 := bstep (se 4 (by rfl) ⟨854352, by rfl⟩ : syracuseStep 9113093 = 1708705) B1708705
theorem B2698771 : Blo 1598998 2698771 := bstep (se 1 (by rfl) ⟨2024078, by rfl⟩ : syracuseStep 2698771 = 4048157) B4048157
theorem B9735821 : Blo 1598998 9735821 := bstep (se 3 (by rfl) ⟨1825466, by rfl⟩ : syracuseStep 9735821 = 3650933) B3650933
theorem B3600017 : Blo 1598998 3600017 := bstep (se 2 (by rfl) ⟨1350006, by rfl⟩ : syracuseStep 3600017 = 2700013) B2700013
theorem B2698913 : Blo 1598998 2698913 := bstep (se 2 (by rfl) ⟨1012092, by rfl⟩ : syracuseStep 2698913 = 2024185) B2024185
theorem B3600035 : Blo 1598998 3600035 := bstep (se 1 (by rfl) ⟨2700026, by rfl⟩ : syracuseStep 3600035 = 5400053) B5400053
theorem B5402321 : Blo 1598998 5402321 := bstep (se 2 (by rfl) ⟨2025870, by rfl⟩ : syracuseStep 5402321 = 4051741) B4051741
theorem B2699041 : Blo 1598998 2699041 := bstep (se 2 (by rfl) ⟨1012140, by rfl⟩ : syracuseStep 2699041 = 2024281) B2024281
theorem B17305397 : Blo 1598998 17305397 := bstep (se 5 (by rfl) ⟨811190, by rfl⟩ : syracuseStep 17305397 = 1622381) B1622381
theorem B2699075 : Blo 1598998 2699075 := bstep (se 1 (by rfl) ⟨2024306, by rfl⟩ : syracuseStep 2699075 = 4048613) B4048613
theorem B4050769 : Blo 1598998 4050769 := bstep (se 2 (by rfl) ⟨1519038, by rfl⟩ : syracuseStep 4050769 = 3038077) B3038077
theorem B3600305 : Blo 1598998 3600305 := bstep (se 2 (by rfl) ⟨1350114, by rfl⟩ : syracuseStep 3600305 = 2700229) B2700229
theorem B2699203 : Blo 1598998 2699203 := bstep (se 1 (by rfl) ⟨2024402, by rfl⟩ : syracuseStep 2699203 = 4048805) B4048805
theorem B3600323 : Blo 1598998 3600323 := bstep (se 1 (by rfl) ⟨2700242, by rfl⟩ : syracuseStep 3600323 = 5400485) B5400485
theorem B12144653 : Blo 1598998 12144653 := bstep (se 3 (by rfl) ⟨2277122, by rfl⟩ : syracuseStep 12144653 = 4554245) B4554245
theorem B5124131 : Blo 1598998 5124131 := bstep (se 1 (by rfl) ⟨3843098, by rfl⟩ : syracuseStep 5124131 = 7686197) B7686197
theorem B5763149 : Blo 1598998 5763149 := bstep (se 3 (by rfl) ⟨1080590, by rfl⟩ : syracuseStep 5763149 = 2161181) B2161181
theorem B2699345 : Blo 1598998 2699345 := bstep (se 2 (by rfl) ⟨1012254, by rfl⟩ : syracuseStep 2699345 = 2024509) B2024509
theorem B4051043 : Blo 1598998 4051043 := bstep (se 1 (by rfl) ⟨3038282, by rfl⟩ : syracuseStep 4051043 = 6076565) B6076565
theorem B2699473 : Blo 1598998 2699473 := bstep (se 2 (by rfl) ⟨1012302, by rfl⟩ : syracuseStep 2699473 = 2024605) B2024605
theorem B3600593 : Blo 1598998 3600593 := bstep (se 2 (by rfl) ⟨1350222, by rfl⟩ : syracuseStep 3600593 = 2700445) B2700445
theorem B27709667 : Blo 1598998 27709667 := bstep (se 1 (by rfl) ⟨20782250, by rfl⟩ : syracuseStep 27709667 = 41564501) B41564501
theorem B3600611 : Blo 1598998 3600611 := bstep (se 1 (by rfl) ⟨2700458, by rfl⟩ : syracuseStep 3600611 = 5400917) B5400917
theorem B4559075 : Blo 1598998 4559075 := bstep (se 1 (by rfl) ⟨3419306, by rfl⟩ : syracuseStep 4559075 = 6838613) B6838613
theorem B5402861 : Blo 1598998 5402861 := bstep (se 3 (by rfl) ⟨1013036, by rfl⟩ : syracuseStep 5402861 = 2026073) B2026073
theorem B6156529 : Blo 1598998 6156529 := bstep (se 2 (by rfl) ⟨2308698, by rfl⟩ : syracuseStep 6156529 = 4617397) B4617397
theorem B2699507 : Blo 1598998 2699507 := bstep (se 1 (by rfl) ⟨2024630, by rfl⟩ : syracuseStep 2699507 = 4049261) B4049261
theorem B4051235 : Blo 1598998 4051235 := bstep (se 1 (by rfl) ⟨3038426, by rfl⟩ : syracuseStep 4051235 = 6076853) B6076853
theorem B5402915 : Blo 1598998 5402915 := bstep (se 1 (by rfl) ⟨4052186, by rfl⟩ : syracuseStep 5402915 = 8104373) B8104373
theorem B1732963 : Blo 1598998 1732963 := bstep (se 1 (by rfl) ⟨1299722, by rfl⟩ : syracuseStep 1732963 = 2599445) B2599445
theorem B2699635 : Blo 1598998 2699635 := bstep (se 1 (by rfl) ⟨2024726, by rfl⟩ : syracuseStep 2699635 = 4049453) B4049453
theorem B18223541 : Blo 1598998 18223541 := bstep (se 5 (by rfl) ⟨854228, by rfl⟩ : syracuseStep 18223541 = 1708457) B1708457
theorem B13152709 : Blo 1598998 13152709 := bstep (se 4 (by rfl) ⟨1233066, by rfl⟩ : syracuseStep 13152709 = 2466133) B2466133
theorem B3600881 : Blo 1598998 3600881 := bstep (se 2 (by rfl) ⟨1350330, by rfl⟩ : syracuseStep 3600881 = 2700661) B2700661
theorem B2699777 : Blo 1598998 2699777 := bstep (se 2 (by rfl) ⟨1012416, by rfl⟩ : syracuseStep 2699777 = 2024833) B2024833
theorem B3600899 : Blo 1598998 3600899 := bstep (se 1 (by rfl) ⟨2700674, by rfl⟩ : syracuseStep 3600899 = 5401349) B5401349
theorem B5403185 : Blo 1598998 5403185 := bstep (se 2 (by rfl) ⟨2026194, by rfl⟩ : syracuseStep 5403185 = 4052389) B4052389
theorem B2699905 : Blo 1598998 2699905 := bstep (se 2 (by rfl) ⟨1012464, by rfl⟩ : syracuseStep 2699905 = 2024929) B2024929
theorem B2699939 : Blo 1598998 2699939 := bstep (se 1 (by rfl) ⟨2024954, by rfl⟩ : syracuseStep 2699939 = 4049909) B4049909
theorem B3035875 : Blo 1598998 3035875 := bstep (se 1 (by rfl) ⟨2276906, by rfl⟩ : syracuseStep 3035875 = 4553813) B4553813
theorem B6075107 : Blo 1598998 6075107 := bstep (se 1 (by rfl) ⟨4556330, by rfl⟩ : syracuseStep 6075107 = 9112661) B9112661
theorem B6075121 : Blo 1598998 6075121 := bstep (se 2 (by rfl) ⟨2278170, by rfl⟩ : syracuseStep 6075121 = 4556341) B4556341
theorem B1798915 : Blo 1598998 1798915 := bstep (se 1 (by rfl) ⟨1349186, by rfl⟩ : syracuseStep 1798915 = 2698373) B2698373
theorem B3601169 : Blo 1598998 3601169 := bstep (se 2 (by rfl) ⟨1350438, by rfl⟩ : syracuseStep 3601169 = 2700877) B2700877
theorem B2700067 : Blo 1598998 2700067 := bstep (se 1 (by rfl) ⟨2025050, by rfl⟩ : syracuseStep 2700067 = 4050101) B4050101
theorem B3601187 : Blo 1598998 3601187 := bstep (se 1 (by rfl) ⟨2700890, by rfl⟩ : syracuseStep 3601187 = 5401781) B5401781
theorem B6837041 : Blo 1598998 6837041 := bstep (se 2 (by rfl) ⟨2563890, by rfl⟩ : syracuseStep 6837041 = 5127781) B5127781
theorem B3036035 : Blo 1598998 3036035 := bstep (se 1 (by rfl) ⟨2277026, by rfl⟩ : syracuseStep 3036035 = 4554053) B4554053
theorem B1799059 : Blo 1598998 1799059 := bstep (se 1 (by rfl) ⟨1349294, by rfl⟩ : syracuseStep 1799059 = 2698589) B2698589
theorem B2700209 : Blo 1598998 2700209 := bstep (se 2 (by rfl) ⟨1012578, by rfl⟩ : syracuseStep 2700209 = 2025157) B2025157
theorem B20493283 : Blo 1598998 20493283 := bstep (se 1 (by rfl) ⟨15369962, by rfl⟩ : syracuseStep 20493283 = 30739925) B30739925
theorem B1799203 : Blo 1598998 1799203 := bstep (se 1 (by rfl) ⟨1349402, by rfl⟩ : syracuseStep 1799203 = 2698805) B2698805
theorem B8098865 : Blo 1598998 8098865 := bstep (se 2 (by rfl) ⟨3037074, by rfl⟩ : syracuseStep 8098865 = 6074149) B6074149
theorem B2700337 : Blo 1598998 2700337 := bstep (se 2 (by rfl) ⟨1012626, by rfl⟩ : syracuseStep 2700337 = 2025253) B2025253
theorem B3601457 : Blo 1598998 3601457 := bstep (se 2 (by rfl) ⟨1350546, by rfl⟩ : syracuseStep 3601457 = 2701093) B2701093
theorem B3601475 : Blo 1598998 3601475 := bstep (se 1 (by rfl) ⟨2701106, by rfl⟩ : syracuseStep 3601475 = 5402213) B5402213
theorem B2700371 : Blo 1598998 2700371 := bstep (se 1 (by rfl) ⟨2025278, by rfl⟩ : syracuseStep 2700371 = 4050557) B4050557
theorem B249394261 : Blo 1598998 249394261 := bstep (se 8 (by rfl) ⟨1461294, by rfl⟩ : syracuseStep 249394261 = 2922589) B2922589
theorem B1799347 : Blo 1598998 1799347 := bstep (se 1 (by rfl) ⟨1349510, by rfl⟩ : syracuseStep 1799347 = 2699021) B2699021
theorem B4617425 : Blo 1598998 4617425 := bstep (se 2 (by rfl) ⟨1731534, by rfl⟩ : syracuseStep 4617425 = 3463069) B3463069
theorem B4052177 : Blo 1598998 4052177 := bstep (se 2 (by rfl) ⟨1519566, by rfl⟩ : syracuseStep 4052177 = 3039133) B3039133
theorem B2700499 : Blo 1598998 2700499 := bstep (se 1 (by rfl) ⟨2025374, by rfl⟩ : syracuseStep 2700499 = 4050749) B4050749
theorem B4052227 : Blo 1598998 4052227 := bstep (se 1 (by rfl) ⟨3039170, by rfl⟩ : syracuseStep 4052227 = 6078341) B6078341
theorem B1709363 : Blo 1598998 1709363 := bstep (se 1 (by rfl) ⟨1282022, by rfl⟩ : syracuseStep 1709363 = 2564045) B2564045
theorem B1799491 : Blo 1598998 1799491 := bstep (se 1 (by rfl) ⟨1349618, by rfl⟩ : syracuseStep 1799491 = 2699237) B2699237
theorem B3601745 : Blo 1598998 3601745 := bstep (se 2 (by rfl) ⟨1350654, by rfl⟩ : syracuseStep 3601745 = 2701309) B2701309
theorem B2700641 : Blo 1598998 2700641 := bstep (se 2 (by rfl) ⟨1012740, by rfl⟩ : syracuseStep 2700641 = 2025481) B2025481
theorem B3601763 : Blo 1598998 3601763 := bstep (se 1 (by rfl) ⟨2701322, by rfl⟩ : syracuseStep 3601763 = 5402645) B5402645
theorem B9106829 : Blo 1598998 9106829 := bstep (se 3 (by rfl) ⟨1707530, by rfl⟩ : syracuseStep 9106829 = 3415061) B3415061
theorem B4052369 : Blo 1598998 4052369 := bstep (se 2 (by rfl) ⟨1519638, by rfl⟩ : syracuseStep 4052369 = 3039277) B3039277
theorem B2192819 : Blo 1598998 2192819 := bstep (se 1 (by rfl) ⟨1644614, by rfl⟩ : syracuseStep 2192819 = 3289229) B3289229
theorem B1799635 : Blo 1598998 1799635 := bstep (se 1 (by rfl) ⟨1349726, by rfl⟩ : syracuseStep 1799635 = 2699453) B2699453
theorem B2700769 : Blo 1598998 2700769 := bstep (se 2 (by rfl) ⟨1012788, by rfl⟩ : syracuseStep 2700769 = 2025577) B2025577
theorem B1922563 : Blo 1598998 1922563 := bstep (se 1 (by rfl) ⟨1441922, by rfl⟩ : syracuseStep 1922563 = 2883845) B2883845
theorem B2700803 : Blo 1598998 2700803 := bstep (se 1 (by rfl) ⟨2025602, by rfl⟩ : syracuseStep 2700803 = 4051205) B4051205
theorem B1922611 : Blo 1598998 1922611 := bstep (se 1 (by rfl) ⟨1441958, by rfl⟩ : syracuseStep 1922611 = 2883917) B2883917
theorem B2561635 : Blo 1598998 2561635 := bstep (se 1 (by rfl) ⟨1921226, by rfl⟩ : syracuseStep 2561635 = 3842453) B3842453
theorem B1799779 : Blo 1598998 1799779 := bstep (se 1 (by rfl) ⟨1349834, by rfl⟩ : syracuseStep 1799779 = 2699669) B2699669
theorem B6485617 : Blo 1598998 6485617 := bstep (se 2 (by rfl) ⟨2432106, by rfl⟩ : syracuseStep 6485617 = 4864213) B4864213
theorem B3602033 : Blo 1598998 3602033 := bstep (se 2 (by rfl) ⟨1350762, by rfl⟩ : syracuseStep 3602033 = 2701525) B2701525
theorem B2700931 : Blo 1598998 2700931 := bstep (se 1 (by rfl) ⟨2025698, by rfl⟩ : syracuseStep 2700931 = 4051397) B4051397
theorem B3602051 : Blo 1598998 3602051 := bstep (se 1 (by rfl) ⟨2701538, by rfl⟩ : syracuseStep 3602051 = 5403077) B5403077
theorem B10385093 : Blo 1598998 10385093 := bstep (se 4 (by rfl) ⟨973602, by rfl⟩ : syracuseStep 10385093 = 1947205) B1947205
theorem B6837965 : Blo 1598998 6837965 := bstep (se 3 (by rfl) ⟨1282118, by rfl⟩ : syracuseStep 6837965 = 2564237) B2564237
theorem B2561777 : Blo 1598998 2561777 := bstep (se 2 (by rfl) ⟨960666, by rfl⟩ : syracuseStep 2561777 = 1921333) B1921333
theorem B1799923 : Blo 1598998 1799923 := bstep (se 1 (by rfl) ⟨1349942, by rfl⟩ : syracuseStep 1799923 = 2699885) B2699885
theorem B2193137 : Blo 1598998 2193137 := bstep (se 2 (by rfl) ⟨822426, by rfl⟩ : syracuseStep 2193137 = 1644853) B1644853
theorem B2561809 : Blo 1598998 2561809 := bstep (se 2 (by rfl) ⟨960678, by rfl⟩ : syracuseStep 2561809 = 1921357) B1921357
theorem B3462929 : Blo 1598998 3462929 := bstep (se 2 (by rfl) ⟨1298598, by rfl⟩ : syracuseStep 3462929 = 2597197) B2597197
theorem B2701073 : Blo 1598998 2701073 := bstep (se 2 (by rfl) ⟨1012902, by rfl⟩ : syracuseStep 2701073 = 2025805) B2025805
theorem B4323107 : Blo 1598998 4323107 := bstep (se 1 (by rfl) ⟨3242330, by rfl⟩ : syracuseStep 4323107 = 6484661) B6484661
theorem B3241795 : Blo 1598998 3241795 := bstep (se 1 (by rfl) ⟨2431346, by rfl⟩ : syracuseStep 3241795 = 4862693) B4862693
theorem B4323149 : Blo 1598998 4323149 := bstep (se 3 (by rfl) ⟨810590, by rfl⟩ : syracuseStep 4323149 = 1621181) B1621181
theorem B1800067 : Blo 1598998 1800067 := bstep (se 1 (by rfl) ⟨1350050, by rfl⟩ : syracuseStep 1800067 = 2700101) B2700101
theorem B2701201 : Blo 1598998 2701201 := bstep (se 2 (by rfl) ⟨1012950, by rfl⟩ : syracuseStep 2701201 = 2025901) B2025901
theorem B6158243 : Blo 1598998 6158243 := bstep (se 1 (by rfl) ⟨4618682, by rfl⟩ : syracuseStep 6158243 = 9237365) B9237365
theorem B3037105 : Blo 1598998 3037105 := bstep (se 2 (by rfl) ⟨1138914, by rfl⟩ : syracuseStep 3037105 = 2277829) B2277829
theorem B2701235 : Blo 1598998 2701235 := bstep (se 1 (by rfl) ⟨2025926, by rfl⟩ : syracuseStep 2701235 = 4051853) B4051853
theorem B7690211 : Blo 1598998 7690211 := bstep (se 1 (by rfl) ⟨5767658, by rfl⟩ : syracuseStep 7690211 = 11535317) B11535317
theorem B1800211 : Blo 1598998 1800211 := bstep (se 1 (by rfl) ⟨1350158, by rfl⟩ : syracuseStep 1800211 = 2700317) B2700317
theorem B2701363 : Blo 1598998 2701363 := bstep (se 1 (by rfl) ⟨2026022, by rfl⟩ : syracuseStep 2701363 = 4052045) B4052045
theorem B1800355 : Blo 1598998 1800355 := bstep (se 1 (by rfl) ⟨1350266, by rfl⟩ : syracuseStep 1800355 = 2700533) B2700533
theorem B7690403 : Blo 1598998 7690403 := bstep (se 1 (by rfl) ⟨5767802, by rfl⟩ : syracuseStep 7690403 = 11535605) B11535605
theorem B6076579 : Blo 1598998 6076579 := bstep (se 1 (by rfl) ⟨4557434, by rfl⟩ : syracuseStep 6076579 = 9114869) B9114869
theorem B5126321 : Blo 1598998 5126321 := bstep (se 2 (by rfl) ⟨1922370, by rfl⟩ : syracuseStep 5126321 = 3844741) B3844741
theorem B2701505 : Blo 1598998 2701505 := bstep (se 2 (by rfl) ⟨1013064, by rfl⟩ : syracuseStep 2701505 = 2026129) B2026129
theorem B1923283 : Blo 1598998 1923283 := bstep (se 1 (by rfl) ⟨1442462, by rfl⟩ : syracuseStep 1923283 = 2884925) B2884925
theorem B2398499 : Blo 1598998 2398499 := bstep (se 1 (by rfl) ⟨1798874, by rfl⟩ : syracuseStep 2398499 = 3597749) B3597749
theorem B5765411 : Blo 1598998 5765411 := bstep (se 1 (by rfl) ⟨4324058, by rfl⟩ : syracuseStep 5765411 = 8648117) B8648117
theorem B9107761 : Blo 1598998 9107761 := bstep (se 2 (by rfl) ⟨3415410, by rfl⟩ : syracuseStep 9107761 = 6830821) B6830821
theorem B5126449 : Blo 1598998 5126449 := bstep (se 2 (by rfl) ⟨1922418, by rfl⟩ : syracuseStep 5126449 = 3844837) B3844837
theorem B1800499 : Blo 1598998 1800499 := bstep (se 1 (by rfl) ⟨1350374, by rfl⟩ : syracuseStep 1800499 = 2700749) B2700749
theorem B2398529 : Blo 1598998 2398529 := bstep (se 2 (by rfl) ⟨899448, by rfl⟩ : syracuseStep 2398529 = 1798897) B1798897
theorem B2701633 : Blo 1598998 2701633 := bstep (se 2 (by rfl) ⟨1013112, by rfl⟩ : syracuseStep 2701633 = 2026225) B2026225
theorem B5396813 : Blo 1598998 5396813 := bstep (se 3 (by rfl) ⟨1011902, by rfl⟩ : syracuseStep 5396813 = 2023805) B2023805
theorem B2398547 : Blo 1598998 2398547 := bstep (se 1 (by rfl) ⟨1798910, by rfl⟩ : syracuseStep 2398547 = 3597821) B3597821
theorem B2701667 : Blo 1598998 2701667 := bstep (se 1 (by rfl) ⟨2026250, by rfl⟩ : syracuseStep 2701667 = 4052501) B4052501
theorem B2398577 : Blo 1598998 2398577 := bstep (se 2 (by rfl) ⟨899466, by rfl⟩ : syracuseStep 2398577 = 1798933) B1798933
theorem B2398595 : Blo 1598998 2398595 := bstep (se 1 (by rfl) ⟨1798946, by rfl⟩ : syracuseStep 2398595 = 3597893) B3597893
theorem B5396867 : Blo 1598998 5396867 := bstep (se 1 (by rfl) ⟨4047650, by rfl⟩ : syracuseStep 5396867 = 8095301) B8095301
theorem B5470609 : Blo 1598998 5470609 := bstep (se 2 (by rfl) ⟨2051478, by rfl⟩ : syracuseStep 5470609 = 4102957) B4102957
theorem B2398625 : Blo 1598998 2398625 := bstep (se 2 (by rfl) ⟨899484, by rfl⟩ : syracuseStep 2398625 = 1798969) B1798969
theorem B2398643 : Blo 1598998 2398643 := bstep (se 1 (by rfl) ⟨1798982, by rfl⟩ : syracuseStep 2398643 = 3597965) B3597965
theorem B1800643 : Blo 1598998 1800643 := bstep (se 1 (by rfl) ⟨1350482, by rfl⟩ : syracuseStep 1800643 = 2700965) B2700965
theorem B2398673 : Blo 1598998 2398673 := bstep (se 2 (by rfl) ⟨899502, by rfl⟩ : syracuseStep 2398673 = 1799005) B1799005
theorem B2398691 : Blo 1598998 2398691 := bstep (se 1 (by rfl) ⟨1799018, by rfl⟩ : syracuseStep 2398691 = 3598037) B3598037
theorem B8100323 : Blo 1598998 8100323 := bstep (se 1 (by rfl) ⟨6075242, by rfl⟩ : syracuseStep 8100323 = 12150485) B12150485
theorem B2398721 : Blo 1598998 2398721 := bstep (se 2 (by rfl) ⟨899520, by rfl⟩ : syracuseStep 2398721 = 1799041) B1799041
theorem B2431505 : Blo 1598998 2431505 := bstep (se 2 (by rfl) ⟨911814, by rfl⟩ : syracuseStep 2431505 = 1823629) B1823629
theorem B2398739 : Blo 1598998 2398739 := bstep (se 1 (by rfl) ⟨1799054, by rfl⟩ : syracuseStep 2398739 = 3598109) B3598109
theorem B2398769 : Blo 1598998 2398769 := bstep (se 2 (by rfl) ⟨899538, by rfl⟩ : syracuseStep 2398769 = 1799077) B1799077
theorem B5126705 : Blo 1598998 5126705 := bstep (se 2 (by rfl) ⟨1922514, by rfl⟩ : syracuseStep 5126705 = 3845029) B3845029
theorem B2398787 : Blo 1598998 2398787 := bstep (se 1 (by rfl) ⟨1799090, by rfl⟩ : syracuseStep 2398787 = 3598181) B3598181
theorem B6830669 : Blo 1598998 6830669 := bstep (se 3 (by rfl) ⟨1280750, by rfl⟩ : syracuseStep 6830669 = 2561501) B2561501
theorem B1800787 : Blo 1598998 1800787 := bstep (se 1 (by rfl) ⟨1350590, by rfl⟩ : syracuseStep 1800787 = 2701181) B2701181
theorem B2398817 : Blo 1598998 2398817 := bstep (se 2 (by rfl) ⟨899556, by rfl⟩ : syracuseStep 2398817 = 1799113) B1799113
theorem B2398835 : Blo 1598998 2398835 := bstep (se 1 (by rfl) ⟨1799126, by rfl⟩ : syracuseStep 2398835 = 3598253) B3598253
theorem B5397137 : Blo 1598998 5397137 := bstep (se 2 (by rfl) ⟨2023926, by rfl⟩ : syracuseStep 5397137 = 4047853) B4047853
theorem B2398865 : Blo 1598998 2398865 := bstep (se 2 (by rfl) ⟨899574, by rfl⟩ : syracuseStep 2398865 = 1799149) B1799149
theorem B2398883 : Blo 1598998 2398883 := bstep (se 1 (by rfl) ⟨1799162, by rfl⟩ : syracuseStep 2398883 = 3598325) B3598325
theorem B2562737 : Blo 1598998 2562737 := bstep (se 2 (by rfl) ⟨961026, by rfl⟩ : syracuseStep 2562737 = 1922053) B1922053
theorem B10255025 : Blo 1598998 10255025 := bstep (se 2 (by rfl) ⟨3845634, by rfl⟩ : syracuseStep 10255025 = 7691269) B7691269
theorem B2398913 : Blo 1598998 2398913 := bstep (se 2 (by rfl) ⟨899592, by rfl⟩ : syracuseStep 2398913 = 1799185) B1799185
theorem B4553425 : Blo 1598998 4553425 := bstep (se 2 (by rfl) ⟨1707534, by rfl⟩ : syracuseStep 4553425 = 3415069) B3415069
theorem B2398931 : Blo 1598998 2398931 := bstep (se 1 (by rfl) ⟨1799198, by rfl⟩ : syracuseStep 2398931 = 3598397) B3598397
theorem B15383267 : Blo 1598998 15383267 := bstep (se 1 (by rfl) ⟨11537450, by rfl⟩ : syracuseStep 15383267 = 23074901) B23074901
theorem B1800931 : Blo 1598998 1800931 := bstep (se 1 (by rfl) ⟨1350698, by rfl⟩ : syracuseStep 1800931 = 2701397) B2701397
theorem B2398961 : Blo 1598998 2398961 := bstep (se 2 (by rfl) ⟨899610, by rfl⟩ : syracuseStep 2398961 = 1799221) B1799221
theorem B2398979 : Blo 1598998 2398979 := bstep (se 1 (by rfl) ⟨1799234, by rfl⟩ : syracuseStep 2398979 = 3598469) B3598469
theorem B2399009 : Blo 1598998 2399009 := bstep (se 2 (by rfl) ⟨899628, by rfl⟩ : syracuseStep 2399009 = 1799257) B1799257
theorem B7691057 : Blo 1598998 7691057 := bstep (se 2 (by rfl) ⟨2884146, by rfl⟩ : syracuseStep 7691057 = 5768293) B5768293
theorem B2399027 : Blo 1598998 2399027 := bstep (se 1 (by rfl) ⟨1799270, by rfl⟩ : syracuseStep 2399027 = 3598541) B3598541
theorem B2399057 : Blo 1598998 2399057 := bstep (se 2 (by rfl) ⟨899646, by rfl⟩ : syracuseStep 2399057 = 1799293) B1799293
theorem B2399075 : Blo 1598998 2399075 := bstep (se 1 (by rfl) ⟨1799306, by rfl⟩ : syracuseStep 2399075 = 3598613) B3598613
theorem B12147569 : Blo 1598998 12147569 := bstep (se 2 (by rfl) ⟨4555338, by rfl⟩ : syracuseStep 12147569 = 9110677) B9110677
theorem B1948531 : Blo 1598998 1948531 := bstep (se 1 (by rfl) ⟨1461398, by rfl⟩ : syracuseStep 1948531 = 2922797) B2922797
theorem B1801075 : Blo 1598998 1801075 := bstep (se 1 (by rfl) ⟨1350806, by rfl⟩ : syracuseStep 1801075 = 2701613) B2701613
theorem B2399105 : Blo 1598998 2399105 := bstep (se 2 (by rfl) ⟨899664, by rfl⟩ : syracuseStep 2399105 = 1799329) B1799329
theorem B2399123 : Blo 1598998 2399123 := bstep (se 1 (by rfl) ⟨1799342, by rfl⟩ : syracuseStep 2399123 = 3598685) B3598685
theorem B4864931 : Blo 1598998 4864931 := bstep (se 1 (by rfl) ⟨3648698, by rfl⟩ : syracuseStep 4864931 = 7297397) B7297397
theorem B2399153 : Blo 1598998 2399153 := bstep (se 2 (by rfl) ⟨899682, by rfl⟩ : syracuseStep 2399153 = 1799365) B1799365
theorem B2399171 : Blo 1598998 2399171 := bstep (se 1 (by rfl) ⟨1799378, by rfl⟩ : syracuseStep 2399171 = 3598757) B3598757
theorem B3038161 : Blo 1598998 3038161 := bstep (se 2 (by rfl) ⟨1139310, by rfl⟩ : syracuseStep 3038161 = 2278621) B2278621
theorem B2399201 : Blo 1598998 2399201 := bstep (se 2 (by rfl) ⟨899700, by rfl⟩ : syracuseStep 2399201 = 1799401) B1799401
theorem B2399219 : Blo 1598998 2399219 := bstep (se 1 (by rfl) ⟨1799414, by rfl⟩ : syracuseStep 2399219 = 3598829) B3598829
theorem B4865027 : Blo 1598998 4865027 := bstep (se 1 (by rfl) ⟨3648770, by rfl⟩ : syracuseStep 4865027 = 7297541) B7297541
theorem B2399249 : Blo 1598998 2399249 := bstep (se 2 (by rfl) ⟨899718, by rfl⟩ : syracuseStep 2399249 = 1799437) B1799437
theorem B2399267 : Blo 1598998 2399267 := bstep (se 1 (by rfl) ⟨1799450, by rfl⟩ : syracuseStep 2399267 = 3598901) B3598901
theorem B2399297 : Blo 1598998 2399297 := bstep (se 2 (by rfl) ⟨899736, by rfl⟩ : syracuseStep 2399297 = 1799473) B1799473
theorem B2399315 : Blo 1598998 2399315 := bstep (se 1 (by rfl) ⟨1799486, by rfl⟩ : syracuseStep 2399315 = 3598973) B3598973
theorem B5626979 : Blo 1598998 5626979 := bstep (se 1 (by rfl) ⟨4220234, by rfl⟩ : syracuseStep 5626979 = 8440469) B8440469
theorem B2399345 : Blo 1598998 2399345 := bstep (se 2 (by rfl) ⟨899754, by rfl⟩ : syracuseStep 2399345 = 1799509) B1799509
theorem B2399363 : Blo 1598998 2399363 := bstep (se 1 (by rfl) ⟨1799522, by rfl⟩ : syracuseStep 2399363 = 3599045) B3599045
theorem B2464913 : Blo 1598998 2464913 := bstep (se 2 (by rfl) ⟨924342, by rfl⟩ : syracuseStep 2464913 = 1848685) B1848685
theorem B2399393 : Blo 1598998 2399393 := bstep (se 2 (by rfl) ⟨899772, by rfl⟩ : syracuseStep 2399393 = 1799545) B1799545
theorem B5397677 : Blo 1598998 5397677 := bstep (se 3 (by rfl) ⟨1012064, by rfl⟩ : syracuseStep 5397677 = 2024129) B2024129
theorem B2399411 : Blo 1598998 2399411 := bstep (se 1 (by rfl) ⟨1799558, by rfl⟩ : syracuseStep 2399411 = 3599117) B3599117
theorem B2399441 : Blo 1598998 2399441 := bstep (se 2 (by rfl) ⟨899790, by rfl⟩ : syracuseStep 2399441 = 1799581) B1799581
theorem B5397731 : Blo 1598998 5397731 := bstep (se 1 (by rfl) ⟨4048298, by rfl⟩ : syracuseStep 5397731 = 8096597) B8096597
theorem B2399459 : Blo 1598998 2399459 := bstep (se 1 (by rfl) ⟨1799594, by rfl⟩ : syracuseStep 2399459 = 3599189) B3599189
theorem B2399489 : Blo 1598998 2399489 := bstep (se 2 (by rfl) ⟨899808, by rfl⟩ : syracuseStep 2399489 = 1799617) B1799617
theorem B8101133 : Blo 1598998 8101133 := bstep (se 3 (by rfl) ⟨1518962, by rfl⟩ : syracuseStep 8101133 = 3037925) B3037925
theorem B2399507 : Blo 1598998 2399507 := bstep (se 1 (by rfl) ⟨1799630, by rfl⟩ : syracuseStep 2399507 = 3599261) B3599261
theorem B2399537 : Blo 1598998 2399537 := bstep (se 2 (by rfl) ⟨899826, by rfl⟩ : syracuseStep 2399537 = 1799653) B1799653
theorem B2399555 : Blo 1598998 2399555 := bstep (se 1 (by rfl) ⟨1799666, by rfl⟩ : syracuseStep 2399555 = 3599333) B3599333
theorem B2399585 : Blo 1598998 2399585 := bstep (se 2 (by rfl) ⟨899844, by rfl⟩ : syracuseStep 2399585 = 1799689) B1799689
theorem B3038563 : Blo 1598998 3038563 := bstep (se 1 (by rfl) ⟨2278922, by rfl⟩ : syracuseStep 3038563 = 4557845) B4557845
theorem B2399603 : Blo 1598998 2399603 := bstep (se 1 (by rfl) ⟨1799702, by rfl⟩ : syracuseStep 2399603 = 3599405) B3599405
theorem B2399633 : Blo 1598998 2399633 := bstep (se 2 (by rfl) ⟨899862, by rfl⟩ : syracuseStep 2399633 = 1799725) B1799725
theorem B3038609 : Blo 1598998 3038609 := bstep (se 2 (by rfl) ⟨1139478, by rfl⟩ : syracuseStep 3038609 = 2278957) B2278957
theorem B2399651 : Blo 1598998 2399651 := bstep (se 1 (by rfl) ⟨1799738, by rfl⟩ : syracuseStep 2399651 = 3599477) B3599477
theorem B2399681 : Blo 1598998 2399681 := bstep (se 2 (by rfl) ⟨899880, by rfl⟩ : syracuseStep 2399681 = 1799761) B1799761
theorem B2399699 : Blo 1598998 2399699 := bstep (se 1 (by rfl) ⟨1799774, by rfl⟩ : syracuseStep 2399699 = 3599549) B3599549
theorem B5398001 : Blo 1598998 5398001 := bstep (se 2 (by rfl) ⟨2024250, by rfl⟩ : syracuseStep 5398001 = 4048501) B4048501
theorem B2399729 : Blo 1598998 2399729 := bstep (se 2 (by rfl) ⟨899898, by rfl⟩ : syracuseStep 2399729 = 1799797) B1799797
theorem B2563571 : Blo 1598998 2563571 := bstep (se 1 (by rfl) ⟨1922678, by rfl⟩ : syracuseStep 2563571 = 3845357) B3845357
theorem B2399747 : Blo 1598998 2399747 := bstep (se 1 (by rfl) ⟨1799810, by rfl⟩ : syracuseStep 2399747 = 3599621) B3599621
theorem B2399777 : Blo 1598998 2399777 := bstep (se 2 (by rfl) ⟨899916, by rfl⟩ : syracuseStep 2399777 = 1799833) B1799833
theorem B2399795 : Blo 1598998 2399795 := bstep (se 1 (by rfl) ⟨1799846, by rfl⟩ : syracuseStep 2399795 = 3599693) B3599693
theorem B2399825 : Blo 1598998 2399825 := bstep (se 2 (by rfl) ⟨899934, by rfl⟩ : syracuseStep 2399825 = 1799869) B1799869
theorem B2399843 : Blo 1598998 2399843 := bstep (se 1 (by rfl) ⟨1799882, by rfl⟩ : syracuseStep 2399843 = 3599765) B3599765
theorem B2162305 : Blo 1598998 2162305 := bstep (se 2 (by rfl) ⟨810864, by rfl⟩ : syracuseStep 2162305 = 1621729) B1621729
theorem B2399873 : Blo 1598998 2399873 := bstep (se 2 (by rfl) ⟨899952, by rfl⟩ : syracuseStep 2399873 = 1799905) B1799905
theorem B2399891 : Blo 1598998 2399891 := bstep (se 1 (by rfl) ⟨1799918, by rfl⟩ : syracuseStep 2399891 = 3599837) B3599837
theorem B2399921 : Blo 1598998 2399921 := bstep (se 2 (by rfl) ⟨899970, by rfl⟩ : syracuseStep 2399921 = 1799941) B1799941
theorem B3038897 : Blo 1598998 3038897 := bstep (se 2 (by rfl) ⟨1139586, by rfl⟩ : syracuseStep 3038897 = 2279173) B2279173
theorem B2399939 : Blo 1598998 2399939 := bstep (se 1 (by rfl) ⟨1799954, by rfl⟩ : syracuseStep 2399939 = 3599909) B3599909
theorem B2399969 : Blo 1598998 2399969 := bstep (se 2 (by rfl) ⟨899988, by rfl⟩ : syracuseStep 2399969 = 1799977) B1799977
theorem B9109219 : Blo 1598998 9109219 := bstep (se 1 (by rfl) ⟨6831914, by rfl⟩ : syracuseStep 9109219 = 13663829) B13663829
theorem B2399987 : Blo 1598998 2399987 := bstep (se 1 (by rfl) ⟨1799990, by rfl⟩ : syracuseStep 2399987 = 3599981) B3599981
theorem B2400017 : Blo 1598998 2400017 := bstep (se 2 (by rfl) ⟨900006, by rfl⟩ : syracuseStep 2400017 = 1800013) B1800013
theorem B2563859 : Blo 1598998 2563859 := bstep (se 1 (by rfl) ⟨1922894, by rfl⟩ : syracuseStep 2563859 = 3845789) B3845789
theorem B2400035 : Blo 1598998 2400035 := bstep (se 1 (by rfl) ⟨1800026, by rfl⟩ : syracuseStep 2400035 = 3600053) B3600053
theorem B2400065 : Blo 1598998 2400065 := bstep (se 2 (by rfl) ⟨900024, by rfl⟩ : syracuseStep 2400065 = 1800049) B1800049
theorem B18235205 : Blo 1598998 18235205 := bstep (se 4 (by rfl) ⟨1709550, by rfl⟩ : syracuseStep 18235205 = 3419101) B3419101
theorem B3415889 : Blo 1598998 3415889 := bstep (se 2 (by rfl) ⟨1280958, by rfl⟩ : syracuseStep 3415889 = 2561917) B2561917
theorem B2400083 : Blo 1598998 2400083 := bstep (se 1 (by rfl) ⟨1800062, by rfl⟩ : syracuseStep 2400083 = 3600125) B3600125
theorem B3415907 : Blo 1598998 3415907 := bstep (se 1 (by rfl) ⟨2561930, by rfl⟩ : syracuseStep 3415907 = 5123861) B5123861
theorem B2400113 : Blo 1598998 2400113 := bstep (se 2 (by rfl) ⟨900042, by rfl⟩ : syracuseStep 2400113 = 1800085) B1800085
theorem B2400131 : Blo 1598998 2400131 := bstep (se 1 (by rfl) ⟨1800098, by rfl⟩ : syracuseStep 2400131 = 3600197) B3600197
theorem B8765317 : Blo 1598998 8765317 := bstep (se 4 (by rfl) ⟨821748, by rfl⟩ : syracuseStep 8765317 = 1643497) B1643497
theorem B2400161 : Blo 1598998 2400161 := bstep (se 2 (by rfl) ⟨900060, by rfl⟩ : syracuseStep 2400161 = 1800121) B1800121
theorem B2400179 : Blo 1598998 2400179 := bstep (se 1 (by rfl) ⟨1800134, by rfl⟩ : syracuseStep 2400179 = 3600269) B3600269
theorem B4554701 : Blo 1598998 4554701 := bstep (se 3 (by rfl) ⟨854006, by rfl⟩ : syracuseStep 4554701 = 1708013) B1708013
theorem B2400209 : Blo 1598998 2400209 := bstep (se 2 (by rfl) ⟨900078, by rfl⟩ : syracuseStep 2400209 = 1800157) B1800157
theorem B2400227 : Blo 1598998 2400227 := bstep (se 1 (by rfl) ⟨1800170, by rfl⟩ : syracuseStep 2400227 = 3600341) B3600341
theorem B2564083 : Blo 1598998 2564083 := bstep (se 1 (by rfl) ⟨1923062, by rfl⟩ : syracuseStep 2564083 = 3846125) B3846125
theorem B3416087 : Blo 1598998 3416087 := bstep (se 1 (by rfl) ⟨2562065, by rfl⟩ : syracuseStep 3416087 = 5124131) B5124131
theorem B2400281 : Blo 1598998 2400281 := bstep (se 2 (by rfl) ⟨900105, by rfl⟩ : syracuseStep 2400281 = 1800211) B1800211
theorem B6078509 : Blo 1598998 6078509 := bstep (se 3 (by rfl) ⟨1139720, by rfl⟩ : syracuseStep 6078509 = 2279441) B2279441
theorem B3842099 : Blo 1598998 3842099 := bstep (se 1 (by rfl) ⟨2881574, by rfl⟩ : syracuseStep 3842099 = 5763149) B5763149
theorem B5472307 : Blo 1598998 5472307 := bstep (se 1 (by rfl) ⟨4104230, by rfl⟩ : syracuseStep 5472307 = 8208461) B8208461
theorem B12976193 : Blo 1598998 12976193 := bstep (se 2 (by rfl) ⟨4866072, by rfl⟩ : syracuseStep 12976193 = 9732145) B9732145
theorem B2400395 : Blo 1598998 2400395 := bstep (se 1 (by rfl) ⟨1800296, by rfl⟩ : syracuseStep 2400395 = 3600593) B3600593
theorem B18473111 : Blo 1598998 18473111 := bstep (se 1 (by rfl) ⟨13854833, by rfl⟩ : syracuseStep 18473111 = 27709667) B27709667
theorem B2400407 : Blo 1598998 2400407 := bstep (se 1 (by rfl) ⟨1800305, by rfl⟩ : syracuseStep 2400407 = 3600611) B3600611
theorem B3039383 : Blo 1598998 3039383 := bstep (se 1 (by rfl) ⟨2279537, by rfl⟩ : syracuseStep 3039383 = 4559075) B4559075
theorem B2400473 : Blo 1598998 2400473 := bstep (se 2 (by rfl) ⟨900177, by rfl⟩ : syracuseStep 2400473 = 1800355) B1800355
theorem B8102105 : Blo 1598998 8102105 := bstep (se 2 (by rfl) ⟨3038289, by rfl⟩ : syracuseStep 8102105 = 6076579) B6076579
theorem B5767427 : Blo 1598998 5767427 := bstep (se 1 (by rfl) ⟨4325570, by rfl⟩ : syracuseStep 5767427 = 8651141) B8651141
theorem B12149027 : Blo 1598998 12149027 := bstep (se 1 (by rfl) ⟨9111770, by rfl⟩ : syracuseStep 12149027 = 18223541) B18223541
theorem B2400587 : Blo 1598998 2400587 := bstep (se 1 (by rfl) ⟨1800440, by rfl⟩ : syracuseStep 2400587 = 3600881) B3600881
theorem B2400599 : Blo 1598998 2400599 := bstep (se 1 (by rfl) ⟨1800449, by rfl⟩ : syracuseStep 2400599 = 3600899) B3600899
theorem B6488471 : Blo 1598998 6488471 := bstep (se 1 (by rfl) ⟨4866353, by rfl⟩ : syracuseStep 6488471 = 9732707) B9732707
theorem B2400665 : Blo 1598998 2400665 := bstep (se 2 (by rfl) ⟨900249, by rfl⟩ : syracuseStep 2400665 = 1800499) B1800499
theorem B2310617 : Blo 1598998 2310617 := bstep (se 2 (by rfl) ⟨866481, by rfl⟩ : syracuseStep 2310617 = 1732963) B1732963
theorem B2400779 : Blo 1598998 2400779 := bstep (se 1 (by rfl) ⟨1800584, by rfl⟩ : syracuseStep 2400779 = 3601169) B3601169
theorem B5472791 : Blo 1598998 5472791 := bstep (se 1 (by rfl) ⟨4104593, by rfl⟩ : syracuseStep 5472791 = 8209187) B8209187
theorem B2400791 : Blo 1598998 2400791 := bstep (se 1 (by rfl) ⟨1800593, by rfl⟩ : syracuseStep 2400791 = 3601187) B3601187
theorem B19464779 : Blo 1598998 19464779 := bstep (se 1 (by rfl) ⟨14598584, by rfl⟩ : syracuseStep 19464779 = 29197169) B29197169
theorem B2024023 : Blo 1598998 2024023 := bstep (se 1 (by rfl) ⟨1518017, by rfl⟩ : syracuseStep 2024023 = 3036035) B3036035
theorem B2400857 : Blo 1598998 2400857 := bstep (se 2 (by rfl) ⟨900321, by rfl⟩ : syracuseStep 2400857 = 1800643) B1800643
theorem B5399243 : Blo 1598998 5399243 := bstep (se 1 (by rfl) ⟨4049432, by rfl⟩ : syracuseStep 5399243 = 8098865) B8098865
theorem B2278091 : Blo 1598998 2278091 := bstep (se 1 (by rfl) ⟨1708568, by rfl⟩ : syracuseStep 2278091 = 3417137) B3417137
theorem B2400971 : Blo 1598998 2400971 := bstep (se 1 (by rfl) ⟨1800728, by rfl⟩ : syracuseStep 2400971 = 3601457) B3601457
theorem B2400983 : Blo 1598998 2400983 := bstep (se 1 (by rfl) ⟨1800737, by rfl⟩ : syracuseStep 2400983 = 3601475) B3601475
theorem B2851609 : Blo 1598998 2851609 := bstep (se 2 (by rfl) ⟨1069353, by rfl⟩ : syracuseStep 2851609 = 2138707) B2138707
theorem B2401049 : Blo 1598998 2401049 := bstep (se 2 (by rfl) ⟨900393, by rfl⟩ : syracuseStep 2401049 = 1800787) B1800787
theorem B4047691 : Blo 1598998 4047691 := bstep (se 1 (by rfl) ⟨3035768, by rfl⟩ : syracuseStep 4047691 = 6071537) B6071537
theorem B2401163 : Blo 1598998 2401163 := bstep (se 1 (by rfl) ⟨1800872, by rfl⟩ : syracuseStep 2401163 = 3601745) B3601745
theorem B2401175 : Blo 1598998 2401175 := bstep (se 1 (by rfl) ⟨1800881, by rfl⟩ : syracuseStep 2401175 = 3601763) B3601763
theorem B6071219 : Blo 1598998 6071219 := bstep (se 1 (by rfl) ⟨4553414, by rfl⟩ : syracuseStep 6071219 = 9106829) B9106829
theorem B6071233 : Blo 1598998 6071233 := bstep (se 2 (by rfl) ⟨2276712, by rfl⟩ : syracuseStep 6071233 = 4553425) B4553425
theorem B3245015 : Blo 1598998 3245015 := bstep (se 1 (by rfl) ⟨2433761, by rfl⟩ : syracuseStep 3245015 = 4867523) B4867523
theorem B4047833 : Blo 1598998 4047833 := bstep (se 2 (by rfl) ⟨1517937, by rfl⟩ : syracuseStep 4047833 = 3035875) B3035875
theorem B5399513 : Blo 1598998 5399513 := bstep (se 2 (by rfl) ⟨2024817, by rfl⟩ : syracuseStep 5399513 = 4049635) B4049635
theorem B2401241 : Blo 1598998 2401241 := bstep (se 2 (by rfl) ⟨900465, by rfl⟩ : syracuseStep 2401241 = 1800931) B1800931
theorem B10945601 : Blo 1598998 10945601 := bstep (se 2 (by rfl) ⟨4104600, by rfl⟩ : syracuseStep 10945601 = 8209201) B8209201
theorem B2401355 : Blo 1598998 2401355 := bstep (se 1 (by rfl) ⟨1801016, by rfl⟩ : syracuseStep 2401355 = 3602033) B3602033
theorem B2401367 : Blo 1598998 2401367 := bstep (se 1 (by rfl) ⟨1801025, by rfl⟩ : syracuseStep 2401367 = 3602051) B3602051
theorem B10257509 : Blo 1598998 10257509 := bstep (se 4 (by rfl) ⟨961641, by rfl⟩ : syracuseStep 10257509 = 1923283) B1923283
theorem B6923395 : Blo 1598998 6923395 := bstep (se 1 (by rfl) ⟨5192546, by rfl⟩ : syracuseStep 6923395 = 10385093) B10385093
theorem B2598041 : Blo 1598998 2598041 := bstep (se 2 (by rfl) ⟨974265, by rfl⟩ : syracuseStep 2598041 = 1948531) B1948531
theorem B2401433 : Blo 1598998 2401433 := bstep (se 2 (by rfl) ⟨900537, by rfl⟩ : syracuseStep 2401433 = 1801075) B1801075
theorem B32834821 : Blo 1598998 32834821 := bstep (se 4 (by rfl) ⟨3078264, by rfl⟩ : syracuseStep 32834821 = 6156529) B6156529
theorem B4105495 : Blo 1598998 4105495 := bstep (se 1 (by rfl) ⟨3079121, by rfl⟩ : syracuseStep 4105495 = 6158243) B6158243
theorem B3417547 : Blo 1598998 3417547 := bstep (se 1 (by rfl) ⟨2563160, by rfl⟩ : syracuseStep 3417547 = 5126321) B5126321
theorem B3597785 : Blo 1598998 3597785 := bstep (se 2 (by rfl) ⟨1349169, by rfl⟩ : syracuseStep 3597785 = 2698339) B2698339
theorem B1598999 : Blo 1598998 1598999 := bstep (se 1 (by rfl) ⟨1199249, by rfl⟩ : syracuseStep 1598999 = 2398499) B2398499
theorem B3843607 : Blo 1598998 3843607 := bstep (se 1 (by rfl) ⟨2882705, by rfl⟩ : syracuseStep 3843607 = 5765411) B5765411
theorem B1599019 : Blo 1598998 1599019 := bstep (se 1 (by rfl) ⟨1199264, by rfl⟩ : syracuseStep 1599019 = 2398529) B2398529
theorem B3597875 : Blo 1598998 3597875 := bstep (se 1 (by rfl) ⟨2698406, by rfl⟩ : syracuseStep 3597875 = 5396813) B5396813
theorem B1599031 : Blo 1598998 1599031 := bstep (se 1 (by rfl) ⟨1199273, by rfl⟩ : syracuseStep 1599031 = 2398547) B2398547
theorem B1599051 : Blo 1598998 1599051 := bstep (se 1 (by rfl) ⟨1199288, by rfl⟩ : syracuseStep 1599051 = 2398577) B2398577
theorem B1599063 : Blo 1598998 1599063 := bstep (se 1 (by rfl) ⟨1199297, by rfl⟩ : syracuseStep 1599063 = 2398595) B2398595
theorem B3597911 : Blo 1598998 3597911 := bstep (se 1 (by rfl) ⟨2698433, by rfl⟩ : syracuseStep 3597911 = 5396867) B5396867
theorem B1599083 : Blo 1598998 1599083 := bstep (se 1 (by rfl) ⟨1199312, by rfl⟩ : syracuseStep 1599083 = 2398625) B2398625
theorem B1599095 : Blo 1598998 1599095 := bstep (se 1 (by rfl) ⟨1199321, by rfl⟩ : syracuseStep 1599095 = 2398643) B2398643
theorem B1599115 : Blo 1598998 1599115 := bstep (se 1 (by rfl) ⟨1199336, by rfl⟩ : syracuseStep 1599115 = 2398673) B2398673
theorem B1599127 : Blo 1598998 1599127 := bstep (se 1 (by rfl) ⟨1199345, by rfl⟩ : syracuseStep 1599127 = 2398691) B2398691
theorem B5400215 : Blo 1598998 5400215 := bstep (se 1 (by rfl) ⟨4050161, by rfl⟩ : syracuseStep 5400215 = 8100323) B8100323
theorem B1599147 : Blo 1598998 1599147 := bstep (se 1 (by rfl) ⟨1199360, by rfl⟩ : syracuseStep 1599147 = 2398721) B2398721
theorem B1599159 : Blo 1598998 1599159 := bstep (se 1 (by rfl) ⟨1199369, by rfl⟩ : syracuseStep 1599159 = 2398739) B2398739
theorem B1599179 : Blo 1598998 1599179 := bstep (se 1 (by rfl) ⟨1199384, by rfl⟩ : syracuseStep 1599179 = 2398769) B2398769
theorem B3417803 : Blo 1598998 3417803 := bstep (se 1 (by rfl) ⟨2563352, by rfl⟩ : syracuseStep 3417803 = 5126705) B5126705
theorem B18728653 : Blo 1598998 18728653 := bstep (se 3 (by rfl) ⟨3511622, by rfl⟩ : syracuseStep 18728653 = 7023245) B7023245
theorem B1599191 : Blo 1598998 1599191 := bstep (se 1 (by rfl) ⟨1199393, by rfl⟩ : syracuseStep 1599191 = 2398787) B2398787
theorem B1599211 : Blo 1598998 1599211 := bstep (se 1 (by rfl) ⟨1199408, by rfl⟩ : syracuseStep 1599211 = 2398817) B2398817
theorem B1599223 : Blo 1598998 1599223 := bstep (se 1 (by rfl) ⟨1199417, by rfl⟩ : syracuseStep 1599223 = 2398835) B2398835
theorem B3598091 : Blo 1598998 3598091 := bstep (se 1 (by rfl) ⟨2698568, by rfl⟩ : syracuseStep 3598091 = 5397137) B5397137
theorem B1599243 : Blo 1598998 1599243 := bstep (se 1 (by rfl) ⟨1199432, by rfl⟩ : syracuseStep 1599243 = 2398865) B2398865
theorem B1599255 : Blo 1598998 1599255 := bstep (se 1 (by rfl) ⟨1199441, by rfl⟩ : syracuseStep 1599255 = 2398883) B2398883
theorem B4048663 : Blo 1598998 4048663 := bstep (se 1 (by rfl) ⟨3036497, by rfl⟩ : syracuseStep 4048663 = 6072995) B6072995
theorem B1599275 : Blo 1598998 1599275 := bstep (se 1 (by rfl) ⟨1199456, by rfl⟩ : syracuseStep 1599275 = 2398913) B2398913
theorem B6833965 : Blo 1598998 6833965 := bstep (se 3 (by rfl) ⟨1281368, by rfl⟩ : syracuseStep 6833965 = 2562737) B2562737
theorem B8103725 : Blo 1598998 8103725 := bstep (se 3 (by rfl) ⟨1519448, by rfl⟩ : syracuseStep 8103725 = 3038897) B3038897
theorem B1599287 : Blo 1598998 1599287 := bstep (se 1 (by rfl) ⟨1199465, by rfl⟩ : syracuseStep 1599287 = 2398931) B2398931
theorem B3598145 : Blo 1598998 3598145 := bstep (se 2 (by rfl) ⟨1349304, by rfl⟩ : syracuseStep 3598145 = 2698609) B2698609
theorem B1599307 : Blo 1598998 1599307 := bstep (se 1 (by rfl) ⟨1199480, by rfl⟩ : syracuseStep 1599307 = 2398961) B2398961
theorem B1599319 : Blo 1598998 1599319 := bstep (se 1 (by rfl) ⟨1199489, by rfl⟩ : syracuseStep 1599319 = 2398979) B2398979
theorem B1599339 : Blo 1598998 1599339 := bstep (se 1 (by rfl) ⟨1199504, by rfl⟩ : syracuseStep 1599339 = 2399009) B2399009
theorem B1599351 : Blo 1598998 1599351 := bstep (se 1 (by rfl) ⟨1199513, by rfl⟩ : syracuseStep 1599351 = 2399027) B2399027
theorem B1599371 : Blo 1598998 1599371 := bstep (se 1 (by rfl) ⟨1199528, by rfl⟩ : syracuseStep 1599371 = 2399057) B2399057
theorem B1599383 : Blo 1598998 1599383 := bstep (se 1 (by rfl) ⟨1199537, by rfl⟩ : syracuseStep 1599383 = 2399075) B2399075
theorem B4556695 : Blo 1598998 4556695 := bstep (se 1 (by rfl) ⟨3417521, by rfl⟩ : syracuseStep 4556695 = 6835043) B6835043
theorem B1599403 : Blo 1598998 1599403 := bstep (se 1 (by rfl) ⟨1199552, by rfl⟩ : syracuseStep 1599403 = 2399105) B2399105
theorem B1599415 : Blo 1598998 1599415 := bstep (se 1 (by rfl) ⟨1199561, by rfl⟩ : syracuseStep 1599415 = 2399123) B2399123
theorem B1599435 : Blo 1598998 1599435 := bstep (se 1 (by rfl) ⟨1199576, by rfl⟩ : syracuseStep 1599435 = 2399153) B2399153
theorem B1599447 : Blo 1598998 1599447 := bstep (se 1 (by rfl) ⟨1199585, by rfl⟩ : syracuseStep 1599447 = 2399171) B2399171
theorem B1599467 : Blo 1598998 1599467 := bstep (se 1 (by rfl) ⟨1199600, by rfl⟩ : syracuseStep 1599467 = 2399201) B2399201
theorem B1599479 : Blo 1598998 1599479 := bstep (se 1 (by rfl) ⟨1199609, by rfl⟩ : syracuseStep 1599479 = 2399219) B2399219
theorem B1599499 : Blo 1598998 1599499 := bstep (se 1 (by rfl) ⟨1199624, by rfl⟩ : syracuseStep 1599499 = 2399249) B2399249
theorem B1599511 : Blo 1598998 1599511 := bstep (se 1 (by rfl) ⟨1199633, by rfl⟩ : syracuseStep 1599511 = 2399267) B2399267
theorem B3598361 : Blo 1598998 3598361 := bstep (se 2 (by rfl) ⟨1349385, by rfl⟩ : syracuseStep 3598361 = 2698771) B2698771
theorem B1599531 : Blo 1598998 1599531 := bstep (se 1 (by rfl) ⟨1199648, by rfl⟩ : syracuseStep 1599531 = 2399297) B2399297
theorem B1599543 : Blo 1598998 1599543 := bstep (se 1 (by rfl) ⟨1199657, by rfl⟩ : syracuseStep 1599543 = 2399315) B2399315
theorem B1599563 : Blo 1598998 1599563 := bstep (se 1 (by rfl) ⟨1199672, by rfl⟩ : syracuseStep 1599563 = 2399345) B2399345
theorem B1599575 : Blo 1598998 1599575 := bstep (se 1 (by rfl) ⟨1199681, by rfl⟩ : syracuseStep 1599575 = 2399363) B2399363
theorem B10250333 : Blo 1598998 10250333 := bstep (se 3 (by rfl) ⟨1921937, by rfl⟩ : syracuseStep 10250333 = 3843875) B3843875
theorem B12978269 : Blo 1598998 12978269 := bstep (se 3 (by rfl) ⟨2433425, by rfl⟩ : syracuseStep 12978269 = 4866851) B4866851
theorem B1599595 : Blo 1598998 1599595 := bstep (se 1 (by rfl) ⟨1199696, by rfl⟩ : syracuseStep 1599595 = 2399393) B2399393
theorem B3598451 : Blo 1598998 3598451 := bstep (se 1 (by rfl) ⟨2698838, by rfl⟩ : syracuseStep 3598451 = 5397677) B5397677
theorem B1599607 : Blo 1598998 1599607 := bstep (se 1 (by rfl) ⟨1199705, by rfl⟩ : syracuseStep 1599607 = 2399411) B2399411
theorem B6834307 : Blo 1598998 6834307 := bstep (se 1 (by rfl) ⟨5125730, by rfl⟩ : syracuseStep 6834307 = 10251461) B10251461
theorem B1599627 : Blo 1598998 1599627 := bstep (se 1 (by rfl) ⟨1199720, by rfl⟩ : syracuseStep 1599627 = 2399441) B2399441
theorem B3598487 : Blo 1598998 3598487 := bstep (se 1 (by rfl) ⟨2698865, by rfl⟩ : syracuseStep 3598487 = 5397731) B5397731
theorem B1599639 : Blo 1598998 1599639 := bstep (se 1 (by rfl) ⟨1199729, by rfl⟩ : syracuseStep 1599639 = 2399459) B2399459
theorem B1599659 : Blo 1598998 1599659 := bstep (se 1 (by rfl) ⟨1199744, by rfl⟩ : syracuseStep 1599659 = 2399489) B2399489
theorem B5400755 : Blo 1598998 5400755 := bstep (se 1 (by rfl) ⟨4050566, by rfl⟩ : syracuseStep 5400755 = 8101133) B8101133
theorem B1599671 : Blo 1598998 1599671 := bstep (se 1 (by rfl) ⟨1199753, by rfl⟩ : syracuseStep 1599671 = 2399507) B2399507
theorem B4049099 : Blo 1598998 4049099 := bstep (se 1 (by rfl) ⟨3036824, by rfl⟩ : syracuseStep 4049099 = 6073649) B6073649
theorem B1599691 : Blo 1598998 1599691 := bstep (se 1 (by rfl) ⟨1199768, by rfl⟩ : syracuseStep 1599691 = 2399537) B2399537
theorem B1599703 : Blo 1598998 1599703 := bstep (se 1 (by rfl) ⟨1199777, by rfl⟩ : syracuseStep 1599703 = 2399555) B2399555
theorem B1599723 : Blo 1598998 1599723 := bstep (se 1 (by rfl) ⟨1199792, by rfl⟩ : syracuseStep 1599723 = 2399585) B2399585
theorem B1599735 : Blo 1598998 1599735 := bstep (se 1 (by rfl) ⟨1199801, by rfl⟩ : syracuseStep 1599735 = 2399603) B2399603
theorem B1599755 : Blo 1598998 1599755 := bstep (se 1 (by rfl) ⟨1199816, by rfl⟩ : syracuseStep 1599755 = 2399633) B2399633
theorem B2025739 : Blo 1598998 2025739 := bstep (se 1 (by rfl) ⟨1519304, by rfl⟩ : syracuseStep 2025739 = 3038609) B3038609
theorem B1599767 : Blo 1598998 1599767 := bstep (se 1 (by rfl) ⟨1199825, by rfl⟩ : syracuseStep 1599767 = 2399651) B2399651
theorem B1599787 : Blo 1598998 1599787 := bstep (se 1 (by rfl) ⟨1199840, by rfl⟩ : syracuseStep 1599787 = 2399681) B2399681
theorem B1599799 : Blo 1598998 1599799 := bstep (se 1 (by rfl) ⟨1199849, by rfl⟩ : syracuseStep 1599799 = 2399699) B2399699
theorem B3598667 : Blo 1598998 3598667 := bstep (se 1 (by rfl) ⟨2699000, by rfl⟩ : syracuseStep 3598667 = 5398001) B5398001
theorem B1599819 : Blo 1598998 1599819 := bstep (se 1 (by rfl) ⟨1199864, by rfl⟩ : syracuseStep 1599819 = 2399729) B2399729
theorem B1599831 : Blo 1598998 1599831 := bstep (se 1 (by rfl) ⟨1199873, by rfl⟩ : syracuseStep 1599831 = 2399747) B2399747
theorem B1599851 : Blo 1598998 1599851 := bstep (se 1 (by rfl) ⟨1199888, by rfl⟩ : syracuseStep 1599851 = 2399777) B2399777
theorem B1599863 : Blo 1598998 1599863 := bstep (se 1 (by rfl) ⟨1199897, by rfl⟩ : syracuseStep 1599863 = 2399795) B2399795
theorem B3598721 : Blo 1598998 3598721 := bstep (se 2 (by rfl) ⟨1349520, by rfl⟩ : syracuseStep 3598721 = 2699041) B2699041
theorem B1599883 : Blo 1598998 1599883 := bstep (se 1 (by rfl) ⟨1199912, by rfl⟩ : syracuseStep 1599883 = 2399825) B2399825
theorem B1599895 : Blo 1598998 1599895 := bstep (se 1 (by rfl) ⟨1199921, by rfl⟩ : syracuseStep 1599895 = 2399843) B2399843
theorem B1599915 : Blo 1598998 1599915 := bstep (se 1 (by rfl) ⟨1199936, by rfl⟩ : syracuseStep 1599915 = 2399873) B2399873
theorem B6490547 : Blo 1598998 6490547 := bstep (se 1 (by rfl) ⟨4867910, by rfl⟩ : syracuseStep 6490547 = 9735821) B9735821
theorem B1599927 : Blo 1598998 1599927 := bstep (se 1 (by rfl) ⟨1199945, by rfl⟩ : syracuseStep 1599927 = 2399891) B2399891
theorem B5401025 : Blo 1598998 5401025 := bstep (se 2 (by rfl) ⟨2025384, by rfl⟩ : syracuseStep 5401025 = 4050769) B4050769
theorem B1599947 : Blo 1598998 1599947 := bstep (se 1 (by rfl) ⟨1199960, by rfl⟩ : syracuseStep 1599947 = 2399921) B2399921
theorem B1599959 : Blo 1598998 1599959 := bstep (se 1 (by rfl) ⟨1199969, by rfl⟩ : syracuseStep 1599959 = 2399939) B2399939
theorem B1599979 : Blo 1598998 1599979 := bstep (se 1 (by rfl) ⟨1199984, by rfl⟩ : syracuseStep 1599979 = 2399969) B2399969
theorem B1599991 : Blo 1598998 1599991 := bstep (se 1 (by rfl) ⟨1199993, by rfl⟩ : syracuseStep 1599991 = 2399987) B2399987
theorem B1600011 : Blo 1598998 1600011 := bstep (se 1 (by rfl) ⟨1200008, by rfl⟩ : syracuseStep 1600011 = 2400017) B2400017
theorem B8096273 : Blo 1598998 8096273 := bstep (se 2 (by rfl) ⟨3036102, by rfl⟩ : syracuseStep 8096273 = 6072205) B6072205
theorem B1600023 : Blo 1598998 1600023 := bstep (se 1 (by rfl) ⟨1200017, by rfl⟩ : syracuseStep 1600023 = 2400035) B2400035
theorem B11536931 : Blo 1598998 11536931 := bstep (se 1 (by rfl) ⟨8652698, by rfl⟩ : syracuseStep 11536931 = 17305397) B17305397
theorem B1600043 : Blo 1598998 1600043 := bstep (se 1 (by rfl) ⟨1200032, by rfl⟩ : syracuseStep 1600043 = 2400065) B2400065
theorem B1600055 : Blo 1598998 1600055 := bstep (se 1 (by rfl) ⟨1200041, by rfl⟩ : syracuseStep 1600055 = 2400083) B2400083
theorem B4049473 : Blo 1598998 4049473 := bstep (se 2 (by rfl) ⟨1518552, by rfl⟩ : syracuseStep 4049473 = 3037105) B3037105
theorem B1600075 : Blo 1598998 1600075 := bstep (se 1 (by rfl) ⟨1200056, by rfl⟩ : syracuseStep 1600075 = 2400113) B2400113
theorem B1600087 : Blo 1598998 1600087 := bstep (se 1 (by rfl) ⟨1200065, by rfl⟩ : syracuseStep 1600087 = 2400131) B2400131
theorem B3598937 : Blo 1598998 3598937 := bstep (se 2 (by rfl) ⟨1349601, by rfl⟩ : syracuseStep 3598937 = 2699203) B2699203
theorem B1600107 : Blo 1598998 1600107 := bstep (se 1 (by rfl) ⟨1200080, by rfl⟩ : syracuseStep 1600107 = 2400161) B2400161
theorem B1600119 : Blo 1598998 1600119 := bstep (se 1 (by rfl) ⟨1200089, by rfl⟩ : syracuseStep 1600119 = 2400179) B2400179
theorem B1600139 : Blo 1598998 1600139 := bstep (se 1 (by rfl) ⟨1200104, by rfl⟩ : syracuseStep 1600139 = 2400209) B2400209
theorem B1600151 : Blo 1598998 1600151 := bstep (se 1 (by rfl) ⟨1200113, by rfl⟩ : syracuseStep 1600151 = 2400227) B2400227
theorem B3418777 : Blo 1598998 3418777 := bstep (se 2 (by rfl) ⟨1282041, by rfl⟩ : syracuseStep 3418777 = 2564083) B2564083
theorem B1600171 : Blo 1598998 1600171 := bstep (se 1 (by rfl) ⟨1200128, by rfl⟩ : syracuseStep 1600171 = 2400257) B2400257
theorem B8096435 : Blo 1598998 8096435 := bstep (se 1 (by rfl) ⟨6072326, by rfl⟩ : syracuseStep 8096435 = 12144653) B12144653
theorem B3599027 : Blo 1598998 3599027 := bstep (se 1 (by rfl) ⟨2699270, by rfl⟩ : syracuseStep 3599027 = 5398541) B5398541
theorem B1600183 : Blo 1598998 1600183 := bstep (se 1 (by rfl) ⟨1200137, by rfl⟩ : syracuseStep 1600183 = 2400275) B2400275
theorem B1600203 : Blo 1598998 1600203 := bstep (se 1 (by rfl) ⟨1200152, by rfl⟩ : syracuseStep 1600203 = 2400305) B2400305
theorem B3599063 : Blo 1598998 3599063 := bstep (se 1 (by rfl) ⟨2699297, by rfl⟩ : syracuseStep 3599063 = 5398595) B5398595
theorem B1600215 : Blo 1598998 1600215 := bstep (se 1 (by rfl) ⟨1200161, by rfl⟩ : syracuseStep 1600215 = 2400323) B2400323
theorem B1600235 : Blo 1598998 1600235 := bstep (se 1 (by rfl) ⟨1200176, by rfl⟩ : syracuseStep 1600235 = 2400353) B2400353
theorem B1600247 : Blo 1598998 1600247 := bstep (se 1 (by rfl) ⟨1200185, by rfl⟩ : syracuseStep 1600247 = 2400371) B2400371
theorem B1600267 : Blo 1598998 1600267 := bstep (se 1 (by rfl) ⟨1200200, by rfl⟩ : syracuseStep 1600267 = 2400401) B2400401
theorem B1600279 : Blo 1598998 1600279 := bstep (se 1 (by rfl) ⟨1200209, by rfl⟩ : syracuseStep 1600279 = 2400419) B2400419
theorem B1600299 : Blo 1598998 1600299 := bstep (se 1 (by rfl) ⟨1200224, by rfl⟩ : syracuseStep 1600299 = 2400449) B2400449
theorem B3418931 : Blo 1598998 3418931 := bstep (se 1 (by rfl) ⟨2564198, by rfl⟩ : syracuseStep 3418931 = 5128397) B5128397
theorem B1600311 : Blo 1598998 1600311 := bstep (se 1 (by rfl) ⟨1200233, by rfl⟩ : syracuseStep 1600311 = 2400467) B2400467
theorem B23071553 : Blo 1598998 23071553 := bstep (se 2 (by rfl) ⟨8651832, by rfl⟩ : syracuseStep 23071553 = 17303665) B17303665
theorem B6073163 : Blo 1598998 6073163 := bstep (se 1 (by rfl) ⟨4554872, by rfl⟩ : syracuseStep 6073163 = 9109745) B9109745
theorem B1600331 : Blo 1598998 1600331 := bstep (se 1 (by rfl) ⟨1200248, by rfl⟩ : syracuseStep 1600331 = 2400497) B2400497
theorem B1600343 : Blo 1598998 1600343 := bstep (se 1 (by rfl) ⟨1200257, by rfl⟩ : syracuseStep 1600343 = 2400515) B2400515
theorem B6073177 : Blo 1598998 6073177 := bstep (se 2 (by rfl) ⟨2277441, by rfl⟩ : syracuseStep 6073177 = 4554883) B4554883
theorem B1600363 : Blo 1598998 1600363 := bstep (se 1 (by rfl) ⟨1200272, by rfl⟩ : syracuseStep 1600363 = 2400545) B2400545
theorem B1600375 : Blo 1598998 1600375 := bstep (se 1 (by rfl) ⟨1200281, by rfl⟩ : syracuseStep 1600375 = 2400563) B2400563
theorem B3599243 : Blo 1598998 3599243 := bstep (se 1 (by rfl) ⟨2699432, by rfl⟩ : syracuseStep 3599243 = 5398865) B5398865
theorem B1600395 : Blo 1598998 1600395 := bstep (se 1 (by rfl) ⟨1200296, by rfl⟩ : syracuseStep 1600395 = 2400593) B2400593
theorem B1600407 : Blo 1598998 1600407 := bstep (se 1 (by rfl) ⟨1200305, by rfl⟩ : syracuseStep 1600407 = 2400611) B2400611
theorem B1600427 : Blo 1598998 1600427 := bstep (se 1 (by rfl) ⟨1200320, by rfl⟩ : syracuseStep 1600427 = 2400641) B2400641
theorem B1600439 : Blo 1598998 1600439 := bstep (se 1 (by rfl) ⟨1200329, by rfl⟩ : syracuseStep 1600439 = 2400659) B2400659
theorem B3599297 : Blo 1598998 3599297 := bstep (se 2 (by rfl) ⟨1349736, by rfl⟩ : syracuseStep 3599297 = 2699473) B2699473
theorem B1600459 : Blo 1598998 1600459 := bstep (se 1 (by rfl) ⟨1200344, by rfl⟩ : syracuseStep 1600459 = 2400689) B2400689
theorem B1600471 : Blo 1598998 1600471 := bstep (se 1 (by rfl) ⟨1200353, by rfl⟩ : syracuseStep 1600471 = 2400707) B2400707
theorem B5401565 : Blo 1598998 5401565 := bstep (se 3 (by rfl) ⟨1012793, by rfl⟩ : syracuseStep 5401565 = 2025587) B2025587
theorem B1600491 : Blo 1598998 1600491 := bstep (se 1 (by rfl) ⟨1200368, by rfl⟩ : syracuseStep 1600491 = 2400737) B2400737
theorem B1600503 : Blo 1598998 1600503 := bstep (se 1 (by rfl) ⟨1200377, by rfl⟩ : syracuseStep 1600503 = 2400755) B2400755
theorem B1600523 : Blo 1598998 1600523 := bstep (se 1 (by rfl) ⟨1200392, by rfl⟩ : syracuseStep 1600523 = 2400785) B2400785
theorem B1600535 : Blo 1598998 1600535 := bstep (se 1 (by rfl) ⟨1200401, by rfl⟩ : syracuseStep 1600535 = 2400803) B2400803
theorem B1600555 : Blo 1598998 1600555 := bstep (se 1 (by rfl) ⟨1200416, by rfl⟩ : syracuseStep 1600555 = 2400833) B2400833
theorem B1600567 : Blo 1598998 1600567 := bstep (se 1 (by rfl) ⟨1200425, by rfl⟩ : syracuseStep 1600567 = 2400851) B2400851
theorem B12143681 : Blo 1598998 12143681 := bstep (se 2 (by rfl) ⟨4553880, by rfl⟩ : syracuseStep 12143681 = 9107761) B9107761
theorem B6835265 : Blo 1598998 6835265 := bstep (se 2 (by rfl) ⟨2563224, by rfl⟩ : syracuseStep 6835265 = 5126449) B5126449
theorem B1600587 : Blo 1598998 1600587 := bstep (se 1 (by rfl) ⟨1200440, by rfl⟩ : syracuseStep 1600587 = 2400881) B2400881
theorem B1600599 : Blo 1598998 1600599 := bstep (se 1 (by rfl) ⟨1200449, by rfl⟩ : syracuseStep 1600599 = 2400899) B2400899
theorem B20507741 : Blo 1598998 20507741 := bstep (se 3 (by rfl) ⟨3845201, by rfl⟩ : syracuseStep 20507741 = 7690403) B7690403
theorem B1600619 : Blo 1598998 1600619 := bstep (se 1 (by rfl) ⟨1200464, by rfl⟩ : syracuseStep 1600619 = 2400929) B2400929
theorem B1600631 : Blo 1598998 1600631 := bstep (se 1 (by rfl) ⟨1200473, by rfl⟩ : syracuseStep 1600631 = 2400947) B2400947
theorem B1600651 : Blo 1598998 1600651 := bstep (se 1 (by rfl) ⟨1200488, by rfl⟩ : syracuseStep 1600651 = 2400977) B2400977
theorem B4050071 : Blo 1598998 4050071 := bstep (se 1 (by rfl) ⟨3037553, by rfl⟩ : syracuseStep 4050071 = 6075107) B6075107
theorem B1600663 : Blo 1598998 1600663 := bstep (se 1 (by rfl) ⟨1200497, by rfl⟩ : syracuseStep 1600663 = 2400995) B2400995
theorem B2698393 : Blo 1598998 2698393 := bstep (se 2 (by rfl) ⟨1011897, by rfl⟩ : syracuseStep 2698393 = 2023795) B2023795
theorem B3599513 : Blo 1598998 3599513 := bstep (se 2 (by rfl) ⟨1349817, by rfl⟩ : syracuseStep 3599513 = 2699635) B2699635
theorem B1600683 : Blo 1598998 1600683 := bstep (se 1 (by rfl) ⟨1200512, by rfl⟩ : syracuseStep 1600683 = 2401025) B2401025
theorem B1600695 : Blo 1598998 1600695 := bstep (se 1 (by rfl) ⟨1200521, by rfl⟩ : syracuseStep 1600695 = 2401043) B2401043
theorem B7294145 : Blo 1598998 7294145 := bstep (se 2 (by rfl) ⟨2735304, by rfl⟩ : syracuseStep 7294145 = 5470609) B5470609
theorem B4558027 : Blo 1598998 4558027 := bstep (se 1 (by rfl) ⟨3418520, by rfl⟩ : syracuseStep 4558027 = 6837041) B6837041
theorem B1600715 : Blo 1598998 1600715 := bstep (se 1 (by rfl) ⟨1200536, by rfl⟩ : syracuseStep 1600715 = 2401073) B2401073
theorem B1600727 : Blo 1598998 1600727 := bstep (se 1 (by rfl) ⟨1200545, by rfl⟩ : syracuseStep 1600727 = 2401091) B2401091
theorem B1600747 : Blo 1598998 1600747 := bstep (se 1 (by rfl) ⟨1200560, by rfl⟩ : syracuseStep 1600747 = 2401121) B2401121
theorem B3599603 : Blo 1598998 3599603 := bstep (se 1 (by rfl) ⟨2699702, by rfl⟩ : syracuseStep 3599603 = 5399405) B5399405
theorem B1600759 : Blo 1598998 1600759 := bstep (se 1 (by rfl) ⟨1200569, by rfl⟩ : syracuseStep 1600759 = 2401139) B2401139
theorem B1600779 : Blo 1598998 1600779 := bstep (se 1 (by rfl) ⟨1200584, by rfl⟩ : syracuseStep 1600779 = 2401169) B2401169
theorem B3599639 : Blo 1598998 3599639 := bstep (se 1 (by rfl) ⟨2699729, by rfl⟩ : syracuseStep 3599639 = 5399459) B5399459
theorem B1600791 : Blo 1598998 1600791 := bstep (se 1 (by rfl) ⟨1200593, by rfl⟩ : syracuseStep 1600791 = 2401187) B2401187
theorem B1600811 : Blo 1598998 1600811 := bstep (se 1 (by rfl) ⟨1200608, by rfl⟩ : syracuseStep 1600811 = 2401217) B2401217
theorem B1600823 : Blo 1598998 1600823 := bstep (se 1 (by rfl) ⟨1200617, by rfl⟩ : syracuseStep 1600823 = 2401235) B2401235
theorem B1600843 : Blo 1598998 1600843 := bstep (se 1 (by rfl) ⟨1200632, by rfl⟩ : syracuseStep 1600843 = 2401265) B2401265
theorem B1600855 : Blo 1598998 1600855 := bstep (se 1 (by rfl) ⟨1200641, by rfl⟩ : syracuseStep 1600855 = 2401283) B2401283
theorem B1600875 : Blo 1598998 1600875 := bstep (se 1 (by rfl) ⟨1200656, by rfl⟩ : syracuseStep 1600875 = 2401313) B2401313
theorem B1600887 : Blo 1598998 1600887 := bstep (se 1 (by rfl) ⟨1200665, by rfl⟩ : syracuseStep 1600887 = 2401331) B2401331
theorem B1600907 : Blo 1598998 1600907 := bstep (se 1 (by rfl) ⟨1200680, by rfl⟩ : syracuseStep 1600907 = 2401361) B2401361
theorem B1600919 : Blo 1598998 1600919 := bstep (se 1 (by rfl) ⟨1200689, by rfl⟩ : syracuseStep 1600919 = 2401379) B2401379
theorem B1600939 : Blo 1598998 1600939 := bstep (se 1 (by rfl) ⟨1200704, by rfl⟩ : syracuseStep 1600939 = 2401409) B2401409
theorem B1600951 : Blo 1598998 1600951 := bstep (se 1 (by rfl) ⟨1200713, by rfl⟩ : syracuseStep 1600951 = 2401427) B2401427
theorem B3599819 : Blo 1598998 3599819 := bstep (se 1 (by rfl) ⟨2699864, by rfl⟩ : syracuseStep 3599819 = 5399729) B5399729
theorem B3648971 : Blo 1598998 3648971 := bstep (se 1 (by rfl) ⟨2736728, by rfl⟩ : syracuseStep 3648971 = 5473457) B5473457
theorem B1600971 : Blo 1598998 1600971 := bstep (se 1 (by rfl) ⟨1200728, by rfl⟩ : syracuseStep 1600971 = 2401457) B2401457
theorem B1600983 : Blo 1598998 1600983 := bstep (se 1 (by rfl) ⟨1200737, by rfl⟩ : syracuseStep 1600983 = 2401475) B2401475
theorem B4558301 : Blo 1598998 4558301 := bstep (se 3 (by rfl) ⟨854681, by rfl⟩ : syracuseStep 4558301 = 1709363) B1709363
theorem B3599873 : Blo 1598998 3599873 := bstep (se 2 (by rfl) ⟨1349952, by rfl⟩ : syracuseStep 3599873 = 2699905) B2699905
theorem B49262093 : Blo 1598998 49262093 := bstep (se 3 (by rfl) ⟨9236642, by rfl⟩ : syracuseStep 49262093 = 18473285) B18473285
theorem B2698967 : Blo 1598998 2698967 := bstep (se 1 (by rfl) ⟨2024225, by rfl⟩ : syracuseStep 2698967 = 4048451) B4048451
theorem B3600089 : Blo 1598998 3600089 := bstep (se 2 (by rfl) ⟨1350033, by rfl⟩ : syracuseStep 3600089 = 2700067) B2700067
theorem B6074135 : Blo 1598998 6074135 := bstep (se 1 (by rfl) ⟨4555601, by rfl⟩ : syracuseStep 6074135 = 9111203) B9111203
theorem B3600179 : Blo 1598998 3600179 := bstep (se 1 (by rfl) ⟨2700134, by rfl⟩ : syracuseStep 3600179 = 5400269) B5400269
theorem B4558643 : Blo 1598998 4558643 := bstep (se 1 (by rfl) ⟨3418982, by rfl⟩ : syracuseStep 4558643 = 6837965) B6837965
theorem B1707851 : Blo 1598998 1707851 := bstep (se 1 (by rfl) ⟨1280888, by rfl⟩ : syracuseStep 1707851 = 2561777) B2561777
theorem B2699095 : Blo 1598998 2699095 := bstep (se 1 (by rfl) ⟨2024321, by rfl⟩ : syracuseStep 2699095 = 4048643) B4048643
theorem B3600215 : Blo 1598998 3600215 := bstep (se 1 (by rfl) ⟨2700161, by rfl⟩ : syracuseStep 3600215 = 5400323) B5400323
theorem B4050881 : Blo 1598998 4050881 := bstep (se 2 (by rfl) ⟨1519080, by rfl⟩ : syracuseStep 4050881 = 3038161) B3038161
theorem B27324377 : Blo 1598998 27324377 := bstep (se 2 (by rfl) ⟨10246641, by rfl⟩ : syracuseStep 27324377 = 20493283) B20493283
theorem B3600395 : Blo 1598998 3600395 := bstep (se 1 (by rfl) ⟨2700296, by rfl⟩ : syracuseStep 3600395 = 5400593) B5400593
theorem B3600449 : Blo 1598998 3600449 := bstep (se 2 (by rfl) ⟨1350168, by rfl⟩ : syracuseStep 3600449 = 2700337) B2700337
theorem B5402699 : Blo 1598998 5402699 := bstep (se 1 (by rfl) ⟨4052024, by rfl⟩ : syracuseStep 5402699 = 8104049) B8104049
theorem B332525681 : Blo 1598998 332525681 := bstep (se 2 (by rfl) ⟨124697130, by rfl⟩ : syracuseStep 332525681 = 249394261) B249394261
theorem B3600665 : Blo 1598998 3600665 := bstep (se 2 (by rfl) ⟨1350249, by rfl⟩ : syracuseStep 3600665 = 2700499) B2700499
theorem B6238529 : Blo 1598998 6238529 := bstep (se 2 (by rfl) ⟨2339448, by rfl⟩ : syracuseStep 6238529 = 4678897) B4678897
theorem B5402969 : Blo 1598998 5402969 := bstep (se 2 (by rfl) ⟨2026113, by rfl⟩ : syracuseStep 5402969 = 4052227) B4052227
theorem B3600755 : Blo 1598998 3600755 := bstep (se 1 (by rfl) ⟨2700566, by rfl⟩ : syracuseStep 3600755 = 5401133) B5401133
theorem B3289459 : Blo 1598998 3289459 := bstep (se 1 (by rfl) ⟨2467094, by rfl⟩ : syracuseStep 3289459 = 4934189) B4934189
theorem B3600791 : Blo 1598998 3600791 := bstep (se 1 (by rfl) ⟨2700593, by rfl⟩ : syracuseStep 3600791 = 5401187) B5401187
theorem B13676951 : Blo 1598998 13676951 := bstep (se 1 (by rfl) ⟨10257713, by rfl⟩ : syracuseStep 13676951 = 20515427) B20515427
theorem B7025089 : Blo 1598998 7025089 := bstep (se 2 (by rfl) ⟨2634408, by rfl⟩ : syracuseStep 7025089 = 5268817) B5268817
theorem B2699723 : Blo 1598998 2699723 := bstep (se 1 (by rfl) ⟨2024792, by rfl⟩ : syracuseStep 2699723 = 4049585) B4049585
theorem B6836683 : Blo 1598998 6836683 := bstep (se 1 (by rfl) ⟨5127512, by rfl⟩ : syracuseStep 6836683 = 10255025) B10255025
theorem B4051417 : Blo 1598998 4051417 := bstep (se 2 (by rfl) ⟨1519281, by rfl⟩ : syracuseStep 4051417 = 3038563) B3038563
theorem B8098379 : Blo 1598998 8098379 := bstep (se 1 (by rfl) ⟨6073784, by rfl⟩ : syracuseStep 8098379 = 12147569) B12147569
theorem B2699851 : Blo 1598998 2699851 := bstep (se 1 (by rfl) ⟨2024888, by rfl⟩ : syracuseStep 2699851 = 4049777) B4049777
theorem B3600971 : Blo 1598998 3600971 := bstep (se 1 (by rfl) ⟨2700728, by rfl⟩ : syracuseStep 3600971 = 5401457) B5401457
theorem B12980837 : Blo 1598998 12980837 := bstep (se 4 (by rfl) ⟨1216953, by rfl⟩ : syracuseStep 12980837 = 2433907) B2433907
theorem B3601025 : Blo 1598998 3601025 := bstep (se 2 (by rfl) ⟨1350384, by rfl⟩ : syracuseStep 3601025 = 2700769) B2700769
theorem B2699993 : Blo 1598998 2699993 := bstep (se 2 (by rfl) ⟨1012497, by rfl⟩ : syracuseStep 2699993 = 2024995) B2024995
theorem B6836957 : Blo 1598998 6836957 := bstep (se 3 (by rfl) ⟨1281929, by rfl⟩ : syracuseStep 6836957 = 2563859) B2563859
theorem B1643275 : Blo 1598998 1643275 := bstep (se 1 (by rfl) ⟨1232456, by rfl⟩ : syracuseStep 1643275 = 2464913) B2464913
theorem B10253101 : Blo 1598998 10253101 := bstep (se 3 (by rfl) ⟨1922456, by rfl⟩ : syracuseStep 10253101 = 3844913) B3844913
theorem B8647489 : Blo 1598998 8647489 := bstep (se 2 (by rfl) ⟨3242808, by rfl⟩ : syracuseStep 8647489 = 6485617) B6485617
theorem B1798987 : Blo 1598998 1798987 := bstep (se 1 (by rfl) ⟨1349240, by rfl⟩ : syracuseStep 1798987 = 2698481) B2698481
theorem B2700121 : Blo 1598998 2700121 := bstep (se 2 (by rfl) ⟨1012545, by rfl⟩ : syracuseStep 2700121 = 2025091) B2025091
theorem B3601241 : Blo 1598998 3601241 := bstep (se 2 (by rfl) ⟨1350465, by rfl⟩ : syracuseStep 3601241 = 2700931) B2700931
theorem B3601331 : Blo 1598998 3601331 := bstep (se 1 (by rfl) ⟨2700998, by rfl⟩ : syracuseStep 3601331 = 5401997) B5401997
theorem B1799095 : Blo 1598998 1799095 := bstep (se 1 (by rfl) ⟨1349321, by rfl⟩ : syracuseStep 1799095 = 2698643) B2698643
theorem B3601367 : Blo 1598998 3601367 := bstep (se 1 (by rfl) ⟨2701025, by rfl⟩ : syracuseStep 3601367 = 5402051) B5402051
theorem B12145625 : Blo 1598998 12145625 := bstep (se 2 (by rfl) ⟨4554609, by rfl⟩ : syracuseStep 12145625 = 9109219) B9109219
theorem B1709047 : Blo 1598998 1709047 := bstep (se 1 (by rfl) ⟨1281785, by rfl⟩ : syracuseStep 1709047 = 2563571) B2563571
theorem B6075395 : Blo 1598998 6075395 := bstep (se 1 (by rfl) ⟨4556546, by rfl⟩ : syracuseStep 6075395 = 9113093) B9113093
theorem B4322393 : Blo 1598998 4322393 := bstep (se 2 (by rfl) ⟨1620897, by rfl⟩ : syracuseStep 4322393 = 3241795) B3241795
theorem B1799275 : Blo 1598998 1799275 := bstep (se 1 (by rfl) ⟨1349456, by rfl⟩ : syracuseStep 1799275 = 2698913) B2698913
theorem B3601547 : Blo 1598998 3601547 := bstep (se 1 (by rfl) ⟨2701160, by rfl⟩ : syracuseStep 3601547 = 5402321) B5402321
theorem B11687089 : Blo 1598998 11687089 := bstep (se 2 (by rfl) ⟨4382658, by rfl⟩ : syracuseStep 11687089 = 8765317) B8765317
theorem B23393461 : Blo 1598998 23393461 := bstep (se 5 (by rfl) ⟨1096568, by rfl⟩ : syracuseStep 23393461 = 2193137) B2193137
theorem B3601601 : Blo 1598998 3601601 := bstep (se 2 (by rfl) ⟨1350600, by rfl⟩ : syracuseStep 3601601 = 2701201) B2701201
theorem B1799383 : Blo 1598998 1799383 := bstep (se 1 (by rfl) ⟨1349537, by rfl⟩ : syracuseStep 1799383 = 2699075) B2699075
theorem B3036467 : Blo 1598998 3036467 := bstep (se 1 (by rfl) ⟨2277350, by rfl⟩ : syracuseStep 3036467 = 4554701) B4554701
theorem B12973405 : Blo 1598998 12973405 := bstep (se 3 (by rfl) ⟨2432513, by rfl⟩ : syracuseStep 12973405 = 4865027) B4865027
theorem B1799563 : Blo 1598998 1799563 := bstep (se 1 (by rfl) ⟨1349672, by rfl⟩ : syracuseStep 1799563 = 2699345) B2699345
theorem B14423447 : Blo 1598998 14423447 := bstep (se 1 (by rfl) ⟨10817585, by rfl⟩ : syracuseStep 14423447 = 21635171) B21635171
theorem B2700695 : Blo 1598998 2700695 := bstep (se 1 (by rfl) ⟨2025521, by rfl⟩ : syracuseStep 2700695 = 4051043) B4051043
theorem B3601817 : Blo 1598998 3601817 := bstep (se 2 (by rfl) ⟨1350681, by rfl⟩ : syracuseStep 3601817 = 2701363) B2701363
theorem B3036619 : Blo 1598998 3036619 := bstep (se 1 (by rfl) ⟨2277464, by rfl⟩ : syracuseStep 3036619 = 4554929) B4554929
theorem B3601907 : Blo 1598998 3601907 := bstep (se 1 (by rfl) ⟨2701430, by rfl⟩ : syracuseStep 3601907 = 5402861) B5402861
theorem B1799671 : Blo 1598998 1799671 := bstep (se 1 (by rfl) ⟨1349753, by rfl⟩ : syracuseStep 1799671 = 2699507) B2699507
theorem B12154373 : Blo 1598998 12154373 := bstep (se 4 (by rfl) ⟨1139472, by rfl⟩ : syracuseStep 12154373 = 2278945) B2278945
theorem B2700823 : Blo 1598998 2700823 := bstep (se 1 (by rfl) ⟨2025617, by rfl⟩ : syracuseStep 2700823 = 4051235) B4051235
theorem B3601943 : Blo 1598998 3601943 := bstep (se 1 (by rfl) ⟨2701457, by rfl⟩ : syracuseStep 3601943 = 5402915) B5402915
theorem B27350621 : Blo 1598998 27350621 := bstep (se 3 (by rfl) ⟨5128241, by rfl⟩ : syracuseStep 27350621 = 10256483) B10256483
theorem B1799851 : Blo 1598998 1799851 := bstep (se 1 (by rfl) ⟨1349888, by rfl⟩ : syracuseStep 1799851 = 2699777) B2699777
theorem B3602123 : Blo 1598998 3602123 := bstep (se 1 (by rfl) ⟨2701592, by rfl⟩ : syracuseStep 3602123 = 5403185) B5403185
theorem B3602177 : Blo 1598998 3602177 := bstep (se 2 (by rfl) ⟨1350816, by rfl⟩ : syracuseStep 3602177 = 2701633) B2701633
theorem B1799959 : Blo 1598998 1799959 := bstep (se 1 (by rfl) ⟨1349969, by rfl⟩ : syracuseStep 1799959 = 2699939) B2699939
theorem B3036953 : Blo 1598998 3036953 := bstep (se 2 (by rfl) ⟨1138857, by rfl⟩ : syracuseStep 3036953 = 2277715) B2277715
theorem B13662053 : Blo 1598998 13662053 := bstep (se 4 (by rfl) ⟨1280817, by rfl⟩ : syracuseStep 13662053 = 2561635) B2561635
theorem B17536945 : Blo 1598998 17536945 := bstep (se 2 (by rfl) ⟨6576354, by rfl⟩ : syracuseStep 17536945 = 13152709) B13152709
theorem B1800139 : Blo 1598998 1800139 := bstep (se 1 (by rfl) ⟨1350104, by rfl⟩ : syracuseStep 1800139 = 2700209) B2700209
theorem B11532293 : Blo 1598998 11532293 := bstep (se 4 (by rfl) ⟨1081152, by rfl⟩ : syracuseStep 11532293 = 2162305) B2162305
theorem B1800247 : Blo 1598998 1800247 := bstep (se 1 (by rfl) ⟨1350185, by rfl⟩ : syracuseStep 1800247 = 2700371) B2700371
theorem B2562187 : Blo 1598998 2562187 := bstep (se 1 (by rfl) ⟨1921640, by rfl⟩ : syracuseStep 2562187 = 3843281) B3843281
theorem B3078283 : Blo 1598998 3078283 := bstep (se 1 (by rfl) ⟨2308712, by rfl⟩ : syracuseStep 3078283 = 4617425) B4617425
theorem B2701451 : Blo 1598998 2701451 := bstep (se 1 (by rfl) ⟨2026088, by rfl⟩ : syracuseStep 2701451 = 4052177) B4052177
theorem B13850803 : Blo 1598998 13850803 := bstep (se 1 (by rfl) ⟨10388102, by rfl⟩ : syracuseStep 13850803 = 20776205) B20776205
theorem B1800427 : Blo 1598998 1800427 := bstep (se 1 (by rfl) ⟨1350320, by rfl⟩ : syracuseStep 1800427 = 2700641) B2700641
theorem B2701579 : Blo 1598998 2701579 := bstep (se 1 (by rfl) ⟨2026184, by rfl⟩ : syracuseStep 2701579 = 4052369) B4052369
theorem B5396759 : Blo 1598998 5396759 := bstep (se 1 (by rfl) ⟨4047569, by rfl⟩ : syracuseStep 5396759 = 8095139) B8095139
theorem B4864321 : Blo 1598998 4864321 := bstep (se 2 (by rfl) ⟨1824120, by rfl⟩ : syracuseStep 4864321 = 3648241) B3648241
theorem B8100161 : Blo 1598998 8100161 := bstep (se 2 (by rfl) ⟨3037560, by rfl⟩ : syracuseStep 8100161 = 6075121) B6075121
theorem B1800535 : Blo 1598998 1800535 := bstep (se 1 (by rfl) ⟨1350401, by rfl⟩ : syracuseStep 1800535 = 2700803) B2700803
theorem B2398553 : Blo 1598998 2398553 := bstep (se 2 (by rfl) ⟨899457, by rfl⟩ : syracuseStep 2398553 = 1798915) B1798915
theorem B2562443 : Blo 1598998 2562443 := bstep (se 1 (by rfl) ⟨1921832, by rfl⟩ : syracuseStep 2562443 = 3843665) B3843665
theorem B3037591 : Blo 1598998 3037591 := bstep (se 1 (by rfl) ⟨2278193, by rfl⟩ : syracuseStep 3037591 = 4556387) B4556387
theorem B2398667 : Blo 1598998 2398667 := bstep (se 1 (by rfl) ⟨1799000, by rfl⟩ : syracuseStep 2398667 = 3598001) B3598001
theorem B2398679 : Blo 1598998 2398679 := bstep (se 1 (by rfl) ⟨1799009, by rfl⟩ : syracuseStep 2398679 = 3598019) B3598019
theorem B5847517 : Blo 1598998 5847517 := bstep (se 3 (by rfl) ⟨1096409, by rfl⟩ : syracuseStep 5847517 = 2192819) B2192819
theorem B2308619 : Blo 1598998 2308619 := bstep (se 1 (by rfl) ⟨1731464, by rfl⟩ : syracuseStep 2308619 = 3462929) B3462929
theorem B1800715 : Blo 1598998 1800715 := bstep (se 1 (by rfl) ⟨1350536, by rfl⟩ : syracuseStep 1800715 = 2701073) B2701073
theorem B2882071 : Blo 1598998 2882071 := bstep (se 1 (by rfl) ⟨2161553, by rfl⟩ : syracuseStep 2882071 = 4323107) B4323107
theorem B2398745 : Blo 1598998 2398745 := bstep (se 2 (by rfl) ⟨899529, by rfl⟩ : syracuseStep 2398745 = 1799059) B1799059
theorem B2882099 : Blo 1598998 2882099 := bstep (se 1 (by rfl) ⟨2161574, by rfl⟩ : syracuseStep 2882099 = 4323149) B4323149
theorem B1800823 : Blo 1598998 1800823 := bstep (se 1 (by rfl) ⟨1350617, by rfl⟩ : syracuseStep 1800823 = 2701235) B2701235
theorem B2398859 : Blo 1598998 2398859 := bstep (se 1 (by rfl) ⟨1799144, by rfl⟩ : syracuseStep 2398859 = 3598289) B3598289
theorem B2398871 : Blo 1598998 2398871 := bstep (se 1 (by rfl) ⟨1799153, by rfl⟩ : syracuseStep 2398871 = 3598307) B3598307
theorem B5126807 : Blo 1598998 5126807 := bstep (se 1 (by rfl) ⟨3845105, by rfl⟩ : syracuseStep 5126807 = 7690211) B7690211
theorem B2398937 : Blo 1598998 2398937 := bstep (se 2 (by rfl) ⟨899601, by rfl⟩ : syracuseStep 2398937 = 1799203) B1799203
theorem B1801003 : Blo 1598998 1801003 := bstep (se 1 (by rfl) ⟨1350752, by rfl⟩ : syracuseStep 1801003 = 2701505) B2701505
theorem B5397299 : Blo 1598998 5397299 := bstep (se 1 (by rfl) ⟨4047974, by rfl⟩ : syracuseStep 5397299 = 8095949) B8095949
theorem B2399051 : Blo 1598998 2399051 := bstep (se 1 (by rfl) ⟨1799288, by rfl⟩ : syracuseStep 2399051 = 3598577) B3598577
theorem B2399063 : Blo 1598998 2399063 := bstep (se 1 (by rfl) ⟨1799297, by rfl⟩ : syracuseStep 2399063 = 3598595) B3598595
theorem B9116509 : Blo 1598998 9116509 := bstep (se 3 (by rfl) ⟨1709345, by rfl⟩ : syracuseStep 9116509 = 3418691) B3418691
theorem B6830993 : Blo 1598998 6830993 := bstep (se 2 (by rfl) ⟨2561622, by rfl⟩ : syracuseStep 6830993 = 5123245) B5123245
theorem B1801111 : Blo 1598998 1801111 := bstep (se 1 (by rfl) ⟨1350833, by rfl⟩ : syracuseStep 1801111 = 2701667) B2701667
theorem B2399129 : Blo 1598998 2399129 := bstep (se 2 (by rfl) ⟨899673, by rfl⟩ : syracuseStep 2399129 = 1799347) B1799347
theorem B1621003 : Blo 1598998 1621003 := bstep (se 1 (by rfl) ⟨1215752, by rfl⟩ : syracuseStep 1621003 = 2431505) B2431505
theorem B2399243 : Blo 1598998 2399243 := bstep (se 1 (by rfl) ⟨1799432, by rfl⟩ : syracuseStep 2399243 = 3598865) B3598865
theorem B2399255 : Blo 1598998 2399255 := bstep (se 1 (by rfl) ⟨1799441, by rfl⟩ : syracuseStep 2399255 = 3598883) B3598883
theorem B4553779 : Blo 1598998 4553779 := bstep (se 1 (by rfl) ⟨3415334, by rfl⟩ : syracuseStep 4553779 = 6830669) B6830669
theorem B5397569 : Blo 1598998 5397569 := bstep (se 2 (by rfl) ⟨2024088, by rfl⟩ : syracuseStep 5397569 = 4048177) B4048177
theorem B2563147 : Blo 1598998 2563147 := bstep (se 1 (by rfl) ⟨1922360, by rfl⟩ : syracuseStep 2563147 = 3844721) B3844721
theorem B2399321 : Blo 1598998 2399321 := bstep (se 2 (by rfl) ⟨899745, by rfl⟩ : syracuseStep 2399321 = 1799491) B1799491
theorem B10255511 : Blo 1598998 10255511 := bstep (se 1 (by rfl) ⟨7691633, by rfl⟩ : syracuseStep 10255511 = 15383267) B15383267
theorem B2399435 : Blo 1598998 2399435 := bstep (se 1 (by rfl) ⟨1799576, by rfl⟩ : syracuseStep 2399435 = 3599153) B3599153
theorem B7396555 : Blo 1598998 7396555 := bstep (se 1 (by rfl) ⟨5547416, by rfl⟩ : syracuseStep 7396555 = 11094833) B11094833
theorem B3038411 : Blo 1598998 3038411 := bstep (se 1 (by rfl) ⟨2278808, by rfl⟩ : syracuseStep 3038411 = 4557617) B4557617
theorem B5127371 : Blo 1598998 5127371 := bstep (se 1 (by rfl) ⟨3845528, by rfl⟩ : syracuseStep 5127371 = 7691057) B7691057
theorem B2399447 : Blo 1598998 2399447 := bstep (se 1 (by rfl) ⟨1799585, by rfl⟩ : syracuseStep 2399447 = 3599171) B3599171
theorem B3038465 : Blo 1598998 3038465 := bstep (se 2 (by rfl) ⟨1139424, by rfl⟩ : syracuseStep 3038465 = 2278849) B2278849
theorem B3243287 : Blo 1598998 3243287 := bstep (se 1 (by rfl) ⟨2432465, by rfl⟩ : syracuseStep 3243287 = 4864931) B4864931
theorem B2399513 : Blo 1598998 2399513 := bstep (se 2 (by rfl) ⟨899817, by rfl⟩ : syracuseStep 2399513 = 1799635) B1799635
theorem B2563417 : Blo 1598998 2563417 := bstep (se 2 (by rfl) ⟨961281, by rfl⟩ : syracuseStep 2563417 = 1922563) B1922563
theorem B2399627 : Blo 1598998 2399627 := bstep (se 1 (by rfl) ⟨1799720, by rfl⟩ : syracuseStep 2399627 = 3599441) B3599441
theorem B2399639 : Blo 1598998 2399639 := bstep (se 1 (by rfl) ⟨1799729, by rfl⟩ : syracuseStep 2399639 = 3599459) B3599459
theorem B2563481 : Blo 1598998 2563481 := bstep (se 2 (by rfl) ⟨961305, by rfl⟩ : syracuseStep 2563481 = 1922611) B1922611
theorem B3751319 : Blo 1598998 3751319 := bstep (se 1 (by rfl) ⟨2813489, by rfl⟩ : syracuseStep 3751319 = 5626979) B5626979
theorem B6929837 : Blo 1598998 6929837 := bstep (se 3 (by rfl) ⟨1299344, by rfl⟩ : syracuseStep 6929837 = 2598689) B2598689
theorem B2399705 : Blo 1598998 2399705 := bstep (se 2 (by rfl) ⟨899889, by rfl⟩ : syracuseStep 2399705 = 1799779) B1799779
theorem B9109037 : Blo 1598998 9109037 := bstep (se 3 (by rfl) ⟨1707944, by rfl⟩ : syracuseStep 9109037 = 3415889) B3415889
theorem B2399819 : Blo 1598998 2399819 := bstep (se 1 (by rfl) ⟨1799864, by rfl⟩ : syracuseStep 2399819 = 3599729) B3599729
theorem B2399831 : Blo 1598998 2399831 := bstep (se 1 (by rfl) ⟨1799873, by rfl⟩ : syracuseStep 2399831 = 3599747) B3599747
theorem B5398109 : Blo 1598998 5398109 := bstep (se 3 (by rfl) ⟨1012145, by rfl⟩ : syracuseStep 5398109 = 2024291) B2024291
theorem B2399897 : Blo 1598998 2399897 := bstep (se 2 (by rfl) ⟨899961, by rfl⟩ : syracuseStep 2399897 = 1799923) B1799923
theorem B3415745 : Blo 1598998 3415745 := bstep (se 2 (by rfl) ⟨1280904, by rfl⟩ : syracuseStep 3415745 = 2561809) B2561809
theorem B2400011 : Blo 1598998 2400011 := bstep (se 1 (by rfl) ⟨1800008, by rfl⟩ : syracuseStep 2400011 = 3600017) B3600017
theorem B2400023 : Blo 1598998 2400023 := bstep (se 1 (by rfl) ⟨1800017, by rfl⟩ : syracuseStep 2400023 = 3600035) B3600035
theorem B2400089 : Blo 1598998 2400089 := bstep (se 2 (by rfl) ⟨900033, by rfl⟩ : syracuseStep 2400089 = 1800067) B1800067
theorem B12156803 : Blo 1598998 12156803 := bstep (se 1 (by rfl) ⟨9117602, by rfl⟩ : syracuseStep 12156803 = 18235205) B18235205
theorem B2277271 : Blo 1598998 2277271 := bstep (se 1 (by rfl) ⟨1707953, by rfl⟩ : syracuseStep 2277271 = 3415907) B3415907
theorem B2400203 : Blo 1598998 2400203 := bstep (se 1 (by rfl) ⟨1800152, by rfl⟩ : syracuseStep 2400203 = 3600305) B3600305
theorem B2400215 : Blo 1598998 2400215 := bstep (se 1 (by rfl) ⟨1800161, by rfl⟩ : syracuseStep 2400215 = 3600323) B3600323
theorem B2400263 : Blo 1598998 2400263 := bstep (se 1 (by rfl) ⟨1800197, by rfl⟩ : syracuseStep 2400263 = 3600395) B3600395
theorem B2277391 : Blo 1598998 2277391 := bstep (se 1 (by rfl) ⟨1708043, by rfl⟩ : syracuseStep 2277391 = 3416087) B3416087
theorem B8650795 : Blo 1598998 8650795 := bstep (se 1 (by rfl) ⟨6488096, by rfl⟩ : syracuseStep 8650795 = 12976193) B12976193
theorem B2400299 : Blo 1598998 2400299 := bstep (se 1 (by rfl) ⟨1800224, by rfl⟩ : syracuseStep 2400299 = 3600449) B3600449
theorem B2400329 : Blo 1598998 2400329 := bstep (se 2 (by rfl) ⟨900123, by rfl⟩ : syracuseStep 2400329 = 1800247) B1800247
theorem B221683787 : Blo 1598998 221683787 := bstep (se 1 (by rfl) ⟨166262840, by rfl⟩ : syracuseStep 221683787 = 332525681) B332525681
theorem B3416249 : Blo 1598998 3416249 := bstep (se 2 (by rfl) ⟨1281093, by rfl⟩ : syracuseStep 3416249 = 2562187) B2562187
theorem B4104377 : Blo 1598998 4104377 := bstep (se 2 (by rfl) ⟨1539141, by rfl⟩ : syracuseStep 4104377 = 3078283) B3078283
theorem B2400443 : Blo 1598998 2400443 := bstep (se 1 (by rfl) ⟨1800332, by rfl⟩ : syracuseStep 2400443 = 3600665) B3600665
theorem B2400503 : Blo 1598998 2400503 := bstep (se 1 (by rfl) ⟨1800377, by rfl⟩ : syracuseStep 2400503 = 3600755) B3600755
theorem B4325647 : Blo 1598998 4325647 := bstep (se 1 (by rfl) ⟨3244235, by rfl⟩ : syracuseStep 4325647 = 6488471) B6488471
theorem B2400527 : Blo 1598998 2400527 := bstep (se 1 (by rfl) ⟨1800395, by rfl⟩ : syracuseStep 2400527 = 3600791) B3600791
theorem B9117967 : Blo 1598998 9117967 := bstep (se 1 (by rfl) ⟨6838475, by rfl⟩ : syracuseStep 9117967 = 13676951) B13676951
theorem B2400569 : Blo 1598998 2400569 := bstep (se 2 (by rfl) ⟨900213, by rfl⟩ : syracuseStep 2400569 = 1800427) B1800427
theorem B5398919 : Blo 1598998 5398919 := bstep (se 1 (by rfl) ⟨4049189, by rfl⟩ : syracuseStep 5398919 = 8098379) B8098379
theorem B12976519 : Blo 1598998 12976519 := bstep (se 1 (by rfl) ⟨9732389, by rfl⟩ : syracuseStep 12976519 = 19464779) B19464779
theorem B2400647 : Blo 1598998 2400647 := bstep (se 1 (by rfl) ⟨1800485, by rfl⟩ : syracuseStep 2400647 = 3600971) B3600971
theorem B2400683 : Blo 1598998 2400683 := bstep (se 1 (by rfl) ⟨1800512, by rfl⟩ : syracuseStep 2400683 = 3601025) B3601025
theorem B2400713 : Blo 1598998 2400713 := bstep (se 2 (by rfl) ⟨900267, by rfl⟩ : syracuseStep 2400713 = 1800535) B1800535
theorem B8102429 : Blo 1598998 8102429 := bstep (se 3 (by rfl) ⟨1519205, by rfl⟩ : syracuseStep 8102429 = 3038411) B3038411
theorem B2400827 : Blo 1598998 2400827 := bstep (se 1 (by rfl) ⟨1800620, by rfl⟩ : syracuseStep 2400827 = 3601241) B3601241
theorem B4047479 : Blo 1598998 4047479 := bstep (se 1 (by rfl) ⟨3035609, by rfl⟩ : syracuseStep 4047479 = 6071219) B6071219
theorem B2400887 : Blo 1598998 2400887 := bstep (se 1 (by rfl) ⟨1800665, by rfl⟩ : syracuseStep 2400887 = 3601331) B3601331
theorem B2400911 : Blo 1598998 2400911 := bstep (se 1 (by rfl) ⟨1800683, by rfl⟩ : syracuseStep 2400911 = 3601367) B3601367
theorem B2163343 : Blo 1598998 2163343 := bstep (se 1 (by rfl) ⟨1622507, by rfl⟩ : syracuseStep 2163343 = 3245015) B3245015
theorem B2400953 : Blo 1598998 2400953 := bstep (se 2 (by rfl) ⟨900357, by rfl⟩ : syracuseStep 2400953 = 1800715) B1800715
theorem B3842761 : Blo 1598998 3842761 := bstep (se 2 (by rfl) ⟨1441035, by rfl⟩ : syracuseStep 3842761 = 2882071) B2882071
theorem B5399297 : Blo 1598998 5399297 := bstep (se 2 (by rfl) ⟨2024736, by rfl⟩ : syracuseStep 5399297 = 4049473) B4049473
theorem B2401031 : Blo 1598998 2401031 := bstep (se 1 (by rfl) ⟨1800773, by rfl⟩ : syracuseStep 2401031 = 3601547) B3601547
theorem B2401067 : Blo 1598998 2401067 := bstep (se 1 (by rfl) ⟨1800800, by rfl⟩ : syracuseStep 2401067 = 3601601) B3601601
theorem B2401097 : Blo 1598998 2401097 := bstep (se 2 (by rfl) ⟨900411, by rfl⟩ : syracuseStep 2401097 = 1800823) B1800823
theorem B2401211 : Blo 1598998 2401211 := bstep (se 1 (by rfl) ⟨1800908, by rfl⟩ : syracuseStep 2401211 = 3601817) B3601817
theorem B2401271 : Blo 1598998 2401271 := bstep (se 1 (by rfl) ⟨1800953, by rfl⟩ : syracuseStep 2401271 = 3601907) B3601907
theorem B8102915 : Blo 1598998 8102915 := bstep (se 1 (by rfl) ⟨6077186, by rfl⟩ : syracuseStep 8102915 = 12154373) B12154373
theorem B2401295 : Blo 1598998 2401295 := bstep (se 1 (by rfl) ⟨1800971, by rfl⟩ : syracuseStep 2401295 = 3601943) B3601943
theorem B3802145 : Blo 1598998 3802145 := bstep (se 2 (by rfl) ⟨1425804, by rfl⟩ : syracuseStep 3802145 = 2851609) B2851609
theorem B2401337 : Blo 1598998 2401337 := bstep (se 2 (by rfl) ⟨900501, by rfl⟩ : syracuseStep 2401337 = 1801003) B1801003
theorem B10003517 : Blo 1598998 10003517 := bstep (se 3 (by rfl) ⟨1875659, by rfl⟩ : syracuseStep 10003517 = 3751319) B3751319
theorem B2278535 : Blo 1598998 2278535 := bstep (se 1 (by rfl) ⟨1708901, by rfl⟩ : syracuseStep 2278535 = 3417803) B3417803
theorem B2401415 : Blo 1598998 2401415 := bstep (se 1 (by rfl) ⟨1801061, by rfl⟩ : syracuseStep 2401415 = 3602123) B3602123
theorem B2401451 : Blo 1598998 2401451 := bstep (se 1 (by rfl) ⟨1801088, by rfl⟩ : syracuseStep 2401451 = 3602177) B3602177
theorem B2401481 : Blo 1598998 2401481 := bstep (se 2 (by rfl) ⟨900555, by rfl⟩ : syracuseStep 2401481 = 1801111) B1801111
theorem B6161645 : Blo 1598998 6161645 := bstep (se 3 (by rfl) ⟨1155308, by rfl⟩ : syracuseStep 6161645 = 2310617) B2310617
theorem B8094977 : Blo 1598998 8094977 := bstep (se 2 (by rfl) ⟨3035616, by rfl⟩ : syracuseStep 8094977 = 6071233) B6071233
theorem B2278729 : Blo 1598998 2278729 := bstep (se 2 (by rfl) ⟨854523, by rfl⟩ : syracuseStep 2278729 = 1709047) B1709047
theorem B6833555 : Blo 1598998 6833555 := bstep (se 1 (by rfl) ⟨5125166, by rfl⟩ : syracuseStep 6833555 = 10250333) B10250333
theorem B8652179 : Blo 1598998 8652179 := bstep (se 1 (by rfl) ⟨6489134, by rfl⟩ : syracuseStep 8652179 = 12978269) B12978269
theorem B6071705 : Blo 1598998 6071705 := bstep (se 2 (by rfl) ⟨2276889, by rfl⟩ : syracuseStep 6071705 = 4553779) B4553779
theorem B7685597 : Blo 1598998 7685597 := bstep (se 3 (by rfl) ⟨1441049, by rfl⟩ : syracuseStep 7685597 = 2882099) B2882099
theorem B3597839 : Blo 1598998 3597839 := bstep (se 1 (by rfl) ⟨2698379, by rfl⟩ : syracuseStep 3597839 = 5396759) B5396759
theorem B3597857 : Blo 1598998 3597857 := bstep (se 2 (by rfl) ⟨1349196, by rfl⟩ : syracuseStep 3597857 = 2698393) B2698393
theorem B5400107 : Blo 1598998 5400107 := bstep (se 1 (by rfl) ⟨4050080, by rfl⟩ : syracuseStep 5400107 = 8100161) B8100161
theorem B1599035 : Blo 1598998 1599035 := bstep (se 1 (by rfl) ⟨1199276, by rfl⟩ : syracuseStep 1599035 = 2398553) B2398553
theorem B15582785 : Blo 1598998 15582785 := bstep (se 2 (by rfl) ⟨5843544, by rfl⟩ : syracuseStep 15582785 = 11687089) B11687089
theorem B4327031 : Blo 1598998 4327031 := bstep (se 1 (by rfl) ⟨3245273, by rfl⟩ : syracuseStep 4327031 = 6490547) B6490547
theorem B1599111 : Blo 1598998 1599111 := bstep (se 1 (by rfl) ⟨1199333, by rfl⟩ : syracuseStep 1599111 = 2398667) B2398667
theorem B1599119 : Blo 1598998 1599119 := bstep (se 1 (by rfl) ⟨1199339, by rfl⟩ : syracuseStep 1599119 = 2398679) B2398679
theorem B43779761 : Blo 1598998 43779761 := bstep (se 2 (by rfl) ⟨16417410, by rfl⟩ : syracuseStep 43779761 = 32834821) B32834821
theorem B1599163 : Blo 1598998 1599163 := bstep (se 1 (by rfl) ⟨1199372, by rfl⟩ : syracuseStep 1599163 = 2398745) B2398745
theorem B5473993 : Blo 1598998 5473993 := bstep (se 2 (by rfl) ⟨2052747, by rfl⟩ : syracuseStep 5473993 = 4105495) B4105495
theorem B1599239 : Blo 1598998 1599239 := bstep (se 1 (by rfl) ⟨1199429, by rfl⟩ : syracuseStep 1599239 = 2398859) B2398859
theorem B1599247 : Blo 1598998 1599247 := bstep (se 1 (by rfl) ⟨1199435, by rfl⟩ : syracuseStep 1599247 = 2398871) B2398871
theorem B3417871 : Blo 1598998 3417871 := bstep (se 1 (by rfl) ⟨2563403, by rfl⟩ : syracuseStep 3417871 = 5126807) B5126807
theorem B3417889 : Blo 1598998 3417889 := bstep (se 2 (by rfl) ⟨1281708, by rfl⟩ : syracuseStep 3417889 = 2563417) B2563417
theorem B1599291 : Blo 1598998 1599291 := bstep (se 1 (by rfl) ⟨1199468, by rfl⟩ : syracuseStep 1599291 = 2398937) B2398937
theorem B3598199 : Blo 1598998 3598199 := bstep (se 1 (by rfl) ⟨2698649, by rfl⟩ : syracuseStep 3598199 = 5397299) B5397299
theorem B2279287 : Blo 1598998 2279287 := bstep (se 1 (by rfl) ⟨1709465, by rfl⟩ : syracuseStep 2279287 = 3418931) B3418931
theorem B1599367 : Blo 1598998 1599367 := bstep (se 1 (by rfl) ⟨1199525, by rfl⟩ : syracuseStep 1599367 = 2399051) B2399051
theorem B4048775 : Blo 1598998 4048775 := bstep (se 1 (by rfl) ⟨3036581, by rfl⟩ : syracuseStep 4048775 = 6073163) B6073163
theorem B1599375 : Blo 1598998 1599375 := bstep (se 1 (by rfl) ⟨1199531, by rfl⟩ : syracuseStep 1599375 = 2399063) B2399063
theorem B4048825 : Blo 1598998 4048825 := bstep (se 2 (by rfl) ⟨1518309, by rfl⟩ : syracuseStep 4048825 = 3036619) B3036619
theorem B4556729 : Blo 1598998 4556729 := bstep (se 2 (by rfl) ⟨1708773, by rfl⟩ : syracuseStep 4556729 = 3417547) B3417547
theorem B1599419 : Blo 1598998 1599419 := bstep (se 1 (by rfl) ⟨1199564, by rfl⟩ : syracuseStep 1599419 = 2399129) B2399129
theorem B1599495 : Blo 1598998 1599495 := bstep (se 1 (by rfl) ⟨1199621, by rfl⟩ : syracuseStep 1599495 = 2399243) B2399243
theorem B1599503 : Blo 1598998 1599503 := bstep (se 1 (by rfl) ⟨1199627, by rfl⟩ : syracuseStep 1599503 = 2399255) B2399255
theorem B8095787 : Blo 1598998 8095787 := bstep (se 1 (by rfl) ⟨6071840, by rfl⟩ : syracuseStep 8095787 = 12143681) B12143681
theorem B3598379 : Blo 1598998 3598379 := bstep (se 1 (by rfl) ⟨2698784, by rfl⟩ : syracuseStep 3598379 = 5397569) B5397569
theorem B4556843 : Blo 1598998 4556843 := bstep (se 1 (by rfl) ⟨3417632, by rfl⟩ : syracuseStep 4556843 = 6835265) B6835265
theorem B1599547 : Blo 1598998 1599547 := bstep (se 1 (by rfl) ⟨1199660, by rfl⟩ : syracuseStep 1599547 = 2399321) B2399321
theorem B1599623 : Blo 1598998 1599623 := bstep (se 1 (by rfl) ⟨1199717, by rfl⟩ : syracuseStep 1599623 = 2399435) B2399435
theorem B3418247 : Blo 1598998 3418247 := bstep (se 1 (by rfl) ⟨2563685, by rfl⟩ : syracuseStep 3418247 = 5127371) B5127371
theorem B1599631 : Blo 1598998 1599631 := bstep (se 1 (by rfl) ⟨1199723, by rfl⟩ : syracuseStep 1599631 = 2399447) B2399447
theorem B2025643 : Blo 1598998 2025643 := bstep (se 1 (by rfl) ⟨1519232, by rfl⟩ : syracuseStep 2025643 = 3038465) B3038465
theorem B1599675 : Blo 1598998 1599675 := bstep (se 1 (by rfl) ⟨1199756, by rfl⟩ : syracuseStep 1599675 = 2399513) B2399513
theorem B1599751 : Blo 1598998 1599751 := bstep (se 1 (by rfl) ⟨1199813, by rfl⟩ : syracuseStep 1599751 = 2399627) B2399627
theorem B1599759 : Blo 1598998 1599759 := bstep (se 1 (by rfl) ⟨1199819, by rfl⟩ : syracuseStep 1599759 = 2399639) B2399639
theorem B24971537 : Blo 1598998 24971537 := bstep (se 2 (by rfl) ⟨9364326, by rfl⟩ : syracuseStep 24971537 = 18728653) B18728653
theorem B1599803 : Blo 1598998 1599803 := bstep (se 1 (by rfl) ⟨1199852, by rfl⟩ : syracuseStep 1599803 = 2399705) B2399705
theorem B6072691 : Blo 1598998 6072691 := bstep (se 1 (by rfl) ⟨4554518, by rfl⟩ : syracuseStep 6072691 = 9109037) B9109037
theorem B1599879 : Blo 1598998 1599879 := bstep (se 1 (by rfl) ⟨1199909, by rfl⟩ : syracuseStep 1599879 = 2399819) B2399819
theorem B1599887 : Blo 1598998 1599887 := bstep (se 1 (by rfl) ⟨1199915, by rfl⟩ : syracuseStep 1599887 = 2399831) B2399831
theorem B9111953 : Blo 1598998 9111953 := bstep (se 2 (by rfl) ⟨3416982, by rfl⟩ : syracuseStep 9111953 = 6833965) B6833965
theorem B3598739 : Blo 1598998 3598739 := bstep (se 1 (by rfl) ⟨2699054, by rfl⟩ : syracuseStep 3598739 = 5398109) B5398109
theorem B1599931 : Blo 1598998 1599931 := bstep (se 1 (by rfl) ⟨1199948, by rfl⟩ : syracuseStep 1599931 = 2399897) B2399897
theorem B3598793 : Blo 1598998 3598793 := bstep (se 2 (by rfl) ⟨1349547, by rfl⟩ : syracuseStep 3598793 = 2699095) B2699095
theorem B1600007 : Blo 1598998 1600007 := bstep (se 1 (by rfl) ⟨1200005, by rfl⟩ : syracuseStep 1600007 = 2400011) B2400011
theorem B4049423 : Blo 1598998 4049423 := bstep (se 1 (by rfl) ⟨3037067, by rfl⟩ : syracuseStep 4049423 = 6074135) B6074135
theorem B1600015 : Blo 1598998 1600015 := bstep (se 1 (by rfl) ⟨1200011, by rfl⟩ : syracuseStep 1600015 = 2400023) B2400023
theorem B1600059 : Blo 1598998 1600059 := bstep (se 1 (by rfl) ⟨1200044, by rfl⟩ : syracuseStep 1600059 = 2400089) B2400089
theorem B23382593 : Blo 1598998 23382593 := bstep (se 2 (by rfl) ⟨8768472, by rfl⟩ : syracuseStep 23382593 = 17536945) B17536945
theorem B8104535 : Blo 1598998 8104535 := bstep (se 1 (by rfl) ⟨6078401, by rfl⟩ : syracuseStep 8104535 = 12156803) B12156803
theorem B1600135 : Blo 1598998 1600135 := bstep (se 1 (by rfl) ⟨1200101, by rfl⟩ : syracuseStep 1600135 = 2400203) B2400203
theorem B1600143 : Blo 1598998 1600143 := bstep (se 1 (by rfl) ⟨1200107, by rfl⟩ : syracuseStep 1600143 = 2400215) B2400215
theorem B1600187 : Blo 1598998 1600187 := bstep (se 1 (by rfl) ⟨1200140, by rfl⟩ : syracuseStep 1600187 = 2400281) B2400281
theorem B1600263 : Blo 1598998 1600263 := bstep (se 1 (by rfl) ⟨1200197, by rfl⟩ : syracuseStep 1600263 = 2400395) B2400395
theorem B12315407 : Blo 1598998 12315407 := bstep (se 1 (by rfl) ⟨9236555, by rfl⟩ : syracuseStep 12315407 = 18473111) B18473111
theorem B1600271 : Blo 1598998 1600271 := bstep (se 1 (by rfl) ⟨1200203, by rfl⟩ : syracuseStep 1600271 = 2400407) B2400407
theorem B1600315 : Blo 1598998 1600315 := bstep (se 1 (by rfl) ⟨1200236, by rfl⟩ : syracuseStep 1600315 = 2400473) B2400473
theorem B5401403 : Blo 1598998 5401403 := bstep (se 1 (by rfl) ⟨4051052, by rfl⟩ : syracuseStep 5401403 = 8102105) B8102105
theorem B3844951 : Blo 1598998 3844951 := bstep (se 1 (by rfl) ⟨2883713, by rfl⟩ : syracuseStep 3844951 = 5767427) B5767427
theorem B9112409 : Blo 1598998 9112409 := bstep (se 2 (by rfl) ⟨3417153, by rfl⟩ : syracuseStep 9112409 = 6834307) B6834307
theorem B1600391 : Blo 1598998 1600391 := bstep (se 1 (by rfl) ⟨1200293, by rfl⟩ : syracuseStep 1600391 = 2400587) B2400587
theorem B1600399 : Blo 1598998 1600399 := bstep (se 1 (by rfl) ⟨1200299, by rfl⟩ : syracuseStep 1600399 = 2400599) B2400599
theorem B1600443 : Blo 1598998 1600443 := bstep (se 1 (by rfl) ⟨1200332, by rfl⟩ : syracuseStep 1600443 = 2400665) B2400665
theorem B1600519 : Blo 1598998 1600519 := bstep (se 1 (by rfl) ⟨1200389, by rfl⟩ : syracuseStep 1600519 = 2400779) B2400779
theorem B3648527 : Blo 1598998 3648527 := bstep (se 1 (by rfl) ⟨2736395, by rfl⟩ : syracuseStep 3648527 = 5472791) B5472791
theorem B1600527 : Blo 1598998 1600527 := bstep (se 1 (by rfl) ⟨1200395, by rfl⟩ : syracuseStep 1600527 = 2400791) B2400791
theorem B1600571 : Blo 1598998 1600571 := bstep (se 1 (by rfl) ⟨1200428, by rfl⟩ : syracuseStep 1600571 = 2400857) B2400857
theorem B8105021 : Blo 1598998 8105021 := bstep (se 3 (by rfl) ⟨1519691, by rfl⟩ : syracuseStep 8105021 = 3039383) B3039383
theorem B8653891 : Blo 1598998 8653891 := bstep (se 1 (by rfl) ⟨6490418, by rfl⟩ : syracuseStep 8653891 = 12980837) B12980837
theorem B3599495 : Blo 1598998 3599495 := bstep (se 1 (by rfl) ⟨2699621, by rfl⟩ : syracuseStep 3599495 = 5399243) B5399243
theorem B1600647 : Blo 1598998 1600647 := bstep (se 1 (by rfl) ⟨1200485, by rfl⟩ : syracuseStep 1600647 = 2400971) B2400971
theorem B1600655 : Blo 1598998 1600655 := bstep (se 1 (by rfl) ⟨1200491, by rfl⟩ : syracuseStep 1600655 = 2400983) B2400983
theorem B4557971 : Blo 1598998 4557971 := bstep (se 1 (by rfl) ⟨3418478, by rfl⟩ : syracuseStep 4557971 = 6836957) B6836957
theorem B4385945 : Blo 1598998 4385945 := bstep (se 2 (by rfl) ⟨1644729, by rfl⟩ : syracuseStep 4385945 = 3289459) B3289459
theorem B19451053 : Blo 1598998 19451053 := bstep (se 3 (by rfl) ⟨3647072, by rfl⟩ : syracuseStep 19451053 = 7294145) B7294145
theorem B1600699 : Blo 1598998 1600699 := bstep (se 1 (by rfl) ⟨1200524, by rfl⟩ : syracuseStep 1600699 = 2401049) B2401049
theorem B4050121 : Blo 1598998 4050121 := bstep (se 2 (by rfl) ⟨1518795, by rfl⟩ : syracuseStep 4050121 = 3037591) B3037591
theorem B9366785 : Blo 1598998 9366785 := bstep (se 2 (by rfl) ⟨3512544, by rfl⟩ : syracuseStep 9366785 = 7025089) B7025089
theorem B1600775 : Blo 1598998 1600775 := bstep (se 1 (by rfl) ⟨1200581, by rfl⟩ : syracuseStep 1600775 = 2401163) B2401163
theorem B1600783 : Blo 1598998 1600783 := bstep (se 1 (by rfl) ⟨1200587, by rfl⟩ : syracuseStep 1600783 = 2401175) B2401175
theorem B5401889 : Blo 1598998 5401889 := bstep (se 2 (by rfl) ⟨2025708, by rfl⟩ : syracuseStep 5401889 = 4051417) B4051417
theorem B2698555 : Blo 1598998 2698555 := bstep (se 1 (by rfl) ⟨2023916, by rfl⟩ : syracuseStep 2698555 = 4047833) B4047833
theorem B8097083 : Blo 1598998 8097083 := bstep (se 1 (by rfl) ⟨6072812, by rfl⟩ : syracuseStep 8097083 = 12145625) B12145625
theorem B3599675 : Blo 1598998 3599675 := bstep (se 1 (by rfl) ⟨2699756, by rfl⟩ : syracuseStep 3599675 = 5399513) B5399513
theorem B1600827 : Blo 1598998 1600827 := bstep (se 1 (by rfl) ⟨1200620, by rfl⟩ : syracuseStep 1600827 = 2401241) B2401241
theorem B4050263 : Blo 1598998 4050263 := bstep (se 1 (by rfl) ⟨3037697, by rfl⟩ : syracuseStep 4050263 = 6075395) B6075395
theorem B1600903 : Blo 1598998 1600903 := bstep (se 1 (by rfl) ⟨1200677, by rfl⟩ : syracuseStep 1600903 = 2401355) B2401355
theorem B1600911 : Blo 1598998 1600911 := bstep (se 1 (by rfl) ⟨1200683, by rfl⟩ : syracuseStep 1600911 = 2401367) B2401367
theorem B3599801 : Blo 1598998 3599801 := bstep (se 2 (by rfl) ⟨1349925, by rfl⟩ : syracuseStep 3599801 = 2699851) B2699851
theorem B1600955 : Blo 1598998 1600955 := bstep (se 1 (by rfl) ⟨1200716, by rfl⟩ : syracuseStep 1600955 = 2401433) B2401433
theorem B2698697 : Blo 1598998 2698697 := bstep (se 2 (by rfl) ⟨1012011, by rfl⟩ : syracuseStep 2698697 = 2024023) B2024023
theorem B8097245 : Blo 1598998 8097245 := bstep (se 3 (by rfl) ⟨1518233, by rfl⟩ : syracuseStep 8097245 = 3036467) B3036467
theorem B4558369 : Blo 1598998 4558369 := bstep (se 2 (by rfl) ⟨1709388, by rfl⟩ : syracuseStep 4558369 = 3418777) B3418777
theorem B73870949 : Blo 1598998 73870949 := bstep (se 4 (by rfl) ⟨6925401, by rfl⟩ : syracuseStep 73870949 = 13850803) B13850803
theorem B2191033 : Blo 1598998 2191033 := bstep (se 2 (by rfl) ⟨821637, by rfl⟩ : syracuseStep 2191033 = 1643275) B1643275
theorem B11529985 : Blo 1598998 11529985 := bstep (se 2 (by rfl) ⟨4323744, by rfl⟩ : syracuseStep 11529985 = 8647489) B8647489
theorem B3600143 : Blo 1598998 3600143 := bstep (se 1 (by rfl) ⟨2700107, by rfl⟩ : syracuseStep 3600143 = 5400215) B5400215
theorem B8097569 : Blo 1598998 8097569 := bstep (se 2 (by rfl) ⟨3036588, by rfl⟩ : syracuseStep 8097569 = 6073177) B6073177
theorem B3600161 : Blo 1598998 3600161 := bstep (se 2 (by rfl) ⟨1350060, by rfl⟩ : syracuseStep 3600161 = 2700121) B2700121
theorem B5402483 : Blo 1598998 5402483 := bstep (se 1 (by rfl) ⟨4051862, by rfl⟩ : syracuseStep 5402483 = 8103725) B8103725
theorem B7688195 : Blo 1598998 7688195 := bstep (se 1 (by rfl) ⟨5766146, by rfl⟩ : syracuseStep 7688195 = 11532293) B11532293
theorem B6156317 : Blo 1598998 6156317 := bstep (se 3 (by rfl) ⟨1154309, by rfl⟩ : syracuseStep 6156317 = 2308619) B2308619
theorem B3600503 : Blo 1598998 3600503 := bstep (se 1 (by rfl) ⟨2700377, by rfl⟩ : syracuseStep 3600503 = 5400755) B5400755
theorem B2699399 : Blo 1598998 2699399 := bstep (se 1 (by rfl) ⟨2024549, by rfl⟩ : syracuseStep 2699399 = 4049099) B4049099
theorem B31191281 : Blo 1598998 31191281 := bstep (se 2 (by rfl) ⟨11696730, by rfl⟩ : syracuseStep 31191281 = 23393461) B23393461
theorem B1708295 : Blo 1598998 1708295 := bstep (se 1 (by rfl) ⟨1281221, by rfl⟩ : syracuseStep 1708295 = 2562443) B2562443
theorem B3600683 : Blo 1598998 3600683 := bstep (se 1 (by rfl) ⟨2700512, by rfl⟩ : syracuseStep 3600683 = 5401025) B5401025
theorem B17297873 : Blo 1598998 17297873 := bstep (se 2 (by rfl) ⟨6486702, by rfl⟩ : syracuseStep 17297873 = 12973405) B12973405
theorem B6074909 : Blo 1598998 6074909 := bstep (se 3 (by rfl) ⟨1139045, by rfl⟩ : syracuseStep 6074909 = 2278091) B2278091
theorem B15381035 : Blo 1598998 15381035 := bstep (se 1 (by rfl) ⟨11535776, by rfl⟩ : syracuseStep 15381035 = 23071553) B23071553
theorem B3601043 : Blo 1598998 3601043 := bstep (se 1 (by rfl) ⟨2700782, by rfl⟩ : syracuseStep 3601043 = 5401565) B5401565
theorem B5124809 : Blo 1598998 5124809 := bstep (se 2 (by rfl) ⟨1921803, by rfl⟩ : syracuseStep 5124809 = 3843607) B3843607
theorem B3601097 : Blo 1598998 3601097 := bstep (se 2 (by rfl) ⟨1350411, by rfl⟩ : syracuseStep 3601097 = 2700823) B2700823
theorem B8098541 : Blo 1598998 8098541 := bstep (se 3 (by rfl) ⟨1518476, by rfl⟩ : syracuseStep 8098541 = 3036953) B3036953
theorem B2700047 : Blo 1598998 2700047 := bstep (se 1 (by rfl) ⟨2025035, by rfl⟩ : syracuseStep 2700047 = 4050071) B4050071
theorem B6837007 : Blo 1598998 6837007 := bstep (se 1 (by rfl) ⟨5127755, by rfl⟩ : syracuseStep 6837007 = 10255511) B10255511
theorem B1708987 : Blo 1598998 1708987 := bstep (se 1 (by rfl) ⟨1281740, by rfl⟩ : syracuseStep 1708987 = 2563481) B2563481
theorem B1799311 : Blo 1598998 1799311 := bstep (se 1 (by rfl) ⟨1349483, by rfl⟩ : syracuseStep 1799311 = 2698967) B2698967
theorem B3036361 : Blo 1598998 3036361 := bstep (se 2 (by rfl) ⟨1138635, by rfl⟩ : syracuseStep 3036361 = 2277271) B2277271
theorem B6075593 : Blo 1598998 6075593 := bstep (se 2 (by rfl) ⟨2278347, by rfl⟩ : syracuseStep 6075593 = 4556695) B4556695
theorem B2700587 : Blo 1598998 2700587 := bstep (se 1 (by rfl) ⟨2025440, by rfl⟩ : syracuseStep 2700587 = 4050881) B4050881
theorem B18216251 : Blo 1598998 18216251 := bstep (se 1 (by rfl) ⟨13662188, by rfl⟩ : syracuseStep 18216251 = 27324377) B27324377
theorem B4052339 : Blo 1598998 4052339 := bstep (se 1 (by rfl) ⟨3039254, by rfl⟩ : syracuseStep 4052339 = 6078509) B6078509
theorem B2561399 : Blo 1598998 2561399 := bstep (se 1 (by rfl) ⟨1921049, by rfl⟩ : syracuseStep 2561399 = 3842099) B3842099
theorem B3601799 : Blo 1598998 3601799 := bstep (se 1 (by rfl) ⟨2701349, by rfl⟩ : syracuseStep 3601799 = 5402699) B5402699
theorem B7296409 : Blo 1598998 7296409 := bstep (se 2 (by rfl) ⟨2736153, by rfl⟩ : syracuseStep 7296409 = 5472307) B5472307
theorem B8099351 : Blo 1598998 8099351 := bstep (se 1 (by rfl) ⟨6074513, by rfl⟩ : syracuseStep 8099351 = 12149027) B12149027
theorem B4159019 : Blo 1598998 4159019 := bstep (se 1 (by rfl) ⟨3119264, by rfl⟩ : syracuseStep 4159019 = 6238529) B6238529
theorem B3601979 : Blo 1598998 3601979 := bstep (se 1 (by rfl) ⟨2701484, by rfl⟩ : syracuseStep 3601979 = 5402969) B5402969
theorem B1799815 : Blo 1598998 1799815 := bstep (se 1 (by rfl) ⟨1349861, by rfl⟩ : syracuseStep 1799815 = 2699723) B2699723
theorem B2700985 : Blo 1598998 2700985 := bstep (se 2 (by rfl) ⟨1012869, by rfl⟩ : syracuseStep 2700985 = 2025739) B2025739
theorem B3602105 : Blo 1598998 3602105 := bstep (se 2 (by rfl) ⟨1350789, by rfl⟩ : syracuseStep 3602105 = 2701579) B2701579
theorem B13670117 : Blo 1598998 13670117 := bstep (se 4 (by rfl) ⟨1281573, by rfl⟩ : syracuseStep 13670117 = 2563147) B2563147
theorem B6928109 : Blo 1598998 6928109 := bstep (se 3 (by rfl) ⟨1299020, by rfl⟩ : syracuseStep 6928109 = 2598041) B2598041
theorem B6485761 : Blo 1598998 6485761 := bstep (se 2 (by rfl) ⟨2432160, by rfl⟩ : syracuseStep 6485761 = 4864321) B4864321
theorem B1799995 : Blo 1598998 1799995 := bstep (se 1 (by rfl) ⟨1349996, by rfl⟩ : syracuseStep 1799995 = 2699993) B2699993
theorem B9115577 : Blo 1598998 9115577 := bstep (se 2 (by rfl) ⟨3418341, by rfl⟩ : syracuseStep 9115577 = 6836683) B6836683
theorem B7297067 : Blo 1598998 7297067 := bstep (se 1 (by rfl) ⟨5472800, by rfl⟩ : syracuseStep 7297067 = 10945601) B10945601
theorem B2881595 : Blo 1598998 2881595 := bstep (se 1 (by rfl) ⟨2161196, by rfl⟩ : syracuseStep 2881595 = 4322393) B4322393
theorem B8648765 : Blo 1598998 8648765 := bstep (se 3 (by rfl) ⟨1621643, by rfl⟩ : syracuseStep 8648765 = 3243287) B3243287
theorem B6838339 : Blo 1598998 6838339 := bstep (se 1 (by rfl) ⟨5128754, by rfl⟩ : syracuseStep 6838339 = 10257509) B10257509
theorem B9615631 : Blo 1598998 9615631 := bstep (se 1 (by rfl) ⟨7211723, by rfl⟩ : syracuseStep 9615631 = 14423447) B14423447
theorem B1800463 : Blo 1598998 1800463 := bstep (se 1 (by rfl) ⟨1350347, by rfl⟩ : syracuseStep 1800463 = 2700695) B2700695
theorem B2398523 : Blo 1598998 2398523 := bstep (se 1 (by rfl) ⟨1798892, by rfl⟩ : syracuseStep 2398523 = 3597785) B3597785
theorem B2398583 : Blo 1598998 2398583 := bstep (se 1 (by rfl) ⟨1798937, by rfl⟩ : syracuseStep 2398583 = 3597875) B3597875
theorem B2398607 : Blo 1598998 2398607 := bstep (se 1 (by rfl) ⟨1798955, by rfl⟩ : syracuseStep 2398607 = 3597911) B3597911
theorem B13670801 : Blo 1598998 13670801 := bstep (se 2 (by rfl) ⟨5126550, by rfl⟩ : syracuseStep 13670801 = 10253101) B10253101
theorem B18233747 : Blo 1598998 18233747 := bstep (se 1 (by rfl) ⟨13675310, by rfl⟩ : syracuseStep 18233747 = 27350621) B27350621
theorem B5396921 : Blo 1598998 5396921 := bstep (se 2 (by rfl) ⟨2023845, by rfl⟩ : syracuseStep 5396921 = 4047691) B4047691
theorem B2398649 : Blo 1598998 2398649 := bstep (se 2 (by rfl) ⟨899493, by rfl⟩ : syracuseStep 2398649 = 1798987) B1798987
theorem B12155345 : Blo 1598998 12155345 := bstep (se 2 (by rfl) ⟨4558254, by rfl⟩ : syracuseStep 12155345 = 9116509) B9116509
theorem B2398727 : Blo 1598998 2398727 := bstep (se 1 (by rfl) ⟨1799045, by rfl⟩ : syracuseStep 2398727 = 3598091) B3598091
theorem B2398763 : Blo 1598998 2398763 := bstep (se 1 (by rfl) ⟨1799072, by rfl⟩ : syracuseStep 2398763 = 3598145) B3598145
theorem B9108035 : Blo 1598998 9108035 := bstep (se 1 (by rfl) ⟨6831026, by rfl⟩ : syracuseStep 9108035 = 13662053) B13662053
theorem B2398793 : Blo 1598998 2398793 := bstep (se 2 (by rfl) ⟨899547, by rfl⟩ : syracuseStep 2398793 = 1799095) B1799095
theorem B2161337 : Blo 1598998 2161337 := bstep (se 2 (by rfl) ⟨810501, by rfl⟩ : syracuseStep 2161337 = 1621003) B1621003
theorem B2398907 : Blo 1598998 2398907 := bstep (se 1 (by rfl) ⟨1799180, by rfl⟩ : syracuseStep 2398907 = 3598361) B3598361
theorem B2398967 : Blo 1598998 2398967 := bstep (se 1 (by rfl) ⟨1799225, by rfl⟩ : syracuseStep 2398967 = 3598451) B3598451
theorem B1800967 : Blo 1598998 1800967 := bstep (se 1 (by rfl) ⟨1350725, by rfl⟩ : syracuseStep 1800967 = 2701451) B2701451
theorem B2398991 : Blo 1598998 2398991 := bstep (se 1 (by rfl) ⟨1799243, by rfl⟩ : syracuseStep 2398991 = 3598487) B3598487
theorem B2399033 : Blo 1598998 2399033 := bstep (se 2 (by rfl) ⟨899637, by rfl⟩ : syracuseStep 2399033 = 1799275) B1799275
theorem B9231193 : Blo 1598998 9231193 := bstep (se 2 (by rfl) ⟨3461697, by rfl⟩ : syracuseStep 9231193 = 6923395) B6923395
theorem B2399111 : Blo 1598998 2399111 := bstep (se 1 (by rfl) ⟨1799333, by rfl⟩ : syracuseStep 2399111 = 3598667) B3598667
theorem B2399147 : Blo 1598998 2399147 := bstep (se 1 (by rfl) ⟨1799360, by rfl⟩ : syracuseStep 2399147 = 3598721) B3598721
theorem B9862073 : Blo 1598998 9862073 := bstep (se 2 (by rfl) ⟨3698277, by rfl⟩ : syracuseStep 9862073 = 7396555) B7396555
theorem B6077369 : Blo 1598998 6077369 := bstep (se 2 (by rfl) ⟨2279013, by rfl⟩ : syracuseStep 6077369 = 4558027) B4558027
theorem B2399177 : Blo 1598998 2399177 := bstep (se 2 (by rfl) ⟨899691, by rfl⟩ : syracuseStep 2399177 = 1799383) B1799383
theorem B5397515 : Blo 1598998 5397515 := bstep (se 1 (by rfl) ⟨4048136, by rfl⟩ : syracuseStep 5397515 = 8096273) B8096273
theorem B7691287 : Blo 1598998 7691287 := bstep (se 1 (by rfl) ⟨5768465, by rfl⟩ : syracuseStep 7691287 = 11536931) B11536931
theorem B2399291 : Blo 1598998 2399291 := bstep (se 1 (by rfl) ⟨1799468, by rfl⟩ : syracuseStep 2399291 = 3598937) B3598937
theorem B5397623 : Blo 1598998 5397623 := bstep (se 1 (by rfl) ⟨4048217, by rfl⟩ : syracuseStep 5397623 = 8096435) B8096435
theorem B2399351 : Blo 1598998 2399351 := bstep (se 1 (by rfl) ⟨1799513, by rfl⟩ : syracuseStep 2399351 = 3599027) B3599027
theorem B2399375 : Blo 1598998 2399375 := bstep (se 1 (by rfl) ⟨1799531, by rfl⟩ : syracuseStep 2399375 = 3599063) B3599063
theorem B2399417 : Blo 1598998 2399417 := bstep (se 2 (by rfl) ⟨899781, by rfl⟩ : syracuseStep 2399417 = 1799563) B1799563
theorem B2399495 : Blo 1598998 2399495 := bstep (se 1 (by rfl) ⟨1799621, by rfl⟩ : syracuseStep 2399495 = 3599243) B3599243
theorem B4553995 : Blo 1598998 4553995 := bstep (se 1 (by rfl) ⟨3415496, by rfl⟩ : syracuseStep 4553995 = 6830993) B6830993
theorem B2399531 : Blo 1598998 2399531 := bstep (se 1 (by rfl) ⟨1799648, by rfl⟩ : syracuseStep 2399531 = 3599297) B3599297
theorem B2399561 : Blo 1598998 2399561 := bstep (se 2 (by rfl) ⟨899835, by rfl⟩ : syracuseStep 2399561 = 1799671) B1799671
theorem B13671827 : Blo 1598998 13671827 := bstep (se 1 (by rfl) ⟨10253870, by rfl⟩ : syracuseStep 13671827 = 20507741) B20507741
theorem B2399675 : Blo 1598998 2399675 := bstep (se 1 (by rfl) ⟨1799756, by rfl⟩ : syracuseStep 2399675 = 3599513) B3599513
theorem B2399735 : Blo 1598998 2399735 := bstep (se 1 (by rfl) ⟨1799801, by rfl⟩ : syracuseStep 2399735 = 3599603) B3599603
theorem B2399759 : Blo 1598998 2399759 := bstep (se 1 (by rfl) ⟨1799819, by rfl⟩ : syracuseStep 2399759 = 3599639) B3599639
theorem B4554269 : Blo 1598998 4554269 := bstep (se 3 (by rfl) ⟨853925, by rfl⟩ : syracuseStep 4554269 = 1707851) B1707851
theorem B2399801 : Blo 1598998 2399801 := bstep (se 2 (by rfl) ⟨899925, by rfl⟩ : syracuseStep 2399801 = 1799851) B1799851
theorem B4619891 : Blo 1598998 4619891 := bstep (se 1 (by rfl) ⟨3464918, by rfl⟩ : syracuseStep 4619891 = 6929837) B6929837
theorem B2399879 : Blo 1598998 2399879 := bstep (se 1 (by rfl) ⟨1799909, by rfl⟩ : syracuseStep 2399879 = 3599819) B3599819
theorem B2432647 : Blo 1598998 2432647 := bstep (se 1 (by rfl) ⟨1824485, by rfl⟩ : syracuseStep 2432647 = 3648971) B3648971
theorem B3038867 : Blo 1598998 3038867 := bstep (se 1 (by rfl) ⟨2279150, by rfl⟩ : syracuseStep 3038867 = 4558301) B4558301
theorem B2399915 : Blo 1598998 2399915 := bstep (se 1 (by rfl) ⟨1799936, by rfl⟩ : syracuseStep 2399915 = 3599873) B3599873
theorem B32841395 : Blo 1598998 32841395 := bstep (se 1 (by rfl) ⟨24631046, by rfl⟩ : syracuseStep 32841395 = 49262093) B49262093
theorem B5398217 : Blo 1598998 5398217 := bstep (se 2 (by rfl) ⟨2024331, by rfl⟩ : syracuseStep 5398217 = 4048663) B4048663
theorem B2399945 : Blo 1598998 2399945 := bstep (se 2 (by rfl) ⟨899979, by rfl⟩ : syracuseStep 2399945 = 1799959) B1799959
theorem B2277163 : Blo 1598998 2277163 := bstep (se 1 (by rfl) ⟨1707872, by rfl⟩ : syracuseStep 2277163 = 3415745) B3415745
theorem B2400059 : Blo 1598998 2400059 := bstep (se 1 (by rfl) ⟨1800044, by rfl⟩ : syracuseStep 2400059 = 3600089) B3600089
theorem B31186757 : Blo 1598998 31186757 := bstep (se 4 (by rfl) ⟨2923758, by rfl⟩ : syracuseStep 31186757 = 5847517) B5847517
theorem B2400119 : Blo 1598998 2400119 := bstep (se 1 (by rfl) ⟨1800089, by rfl⟩ : syracuseStep 2400119 = 3600179) B3600179
theorem B3039095 : Blo 1598998 3039095 := bstep (se 1 (by rfl) ⟨2279321, by rfl⟩ : syracuseStep 3039095 = 4558643) B4558643
theorem B2400143 : Blo 1598998 2400143 := bstep (se 1 (by rfl) ⟨1800107, by rfl⟩ : syracuseStep 2400143 = 3600215) B3600215
theorem B2400185 : Blo 1598998 2400185 := bstep (se 2 (by rfl) ⟨900069, by rfl⟩ : syracuseStep 2400185 = 1800139) B1800139
theorem B4104211 : Blo 1598998 4104211 := bstep (se 1 (by rfl) ⟨3078158, by rfl⟩ : syracuseStep 4104211 = 6156317) B6156317
theorem B11534393 : Blo 1598998 11534393 := bstep (se 2 (by rfl) ⟨4325397, by rfl⟩ : syracuseStep 11534393 = 8650795) B8650795
theorem B2400335 : Blo 1598998 2400335 := bstep (se 1 (by rfl) ⟨1800251, by rfl⟩ : syracuseStep 2400335 = 3600503) B3600503
theorem B9117785 : Blo 1598998 9117785 := bstep (se 2 (by rfl) ⟨3419169, by rfl⟩ : syracuseStep 9117785 = 6838339) B6838339
theorem B2277499 : Blo 1598998 2277499 := bstep (se 1 (by rfl) ⟨1708124, by rfl⟩ : syracuseStep 2277499 = 3416249) B3416249
theorem B2736251 : Blo 1598998 2736251 := bstep (se 1 (by rfl) ⟨2052188, by rfl⟩ : syracuseStep 2736251 = 4104377) B4104377
theorem B7684253 : Blo 1598998 7684253 := bstep (se 3 (by rfl) ⟨1440797, by rfl⟩ : syracuseStep 7684253 = 2881595) B2881595
theorem B2400455 : Blo 1598998 2400455 := bstep (se 1 (by rfl) ⟨1800341, by rfl⟩ : syracuseStep 2400455 = 3600683) B3600683
theorem B12820841 : Blo 1598998 12820841 := bstep (se 2 (by rfl) ⟨4807815, by rfl⟩ : syracuseStep 12820841 = 9615631) B9615631
theorem B5767529 : Blo 1598998 5767529 := bstep (se 2 (by rfl) ⟨2162823, by rfl⟩ : syracuseStep 5767529 = 4325647) B4325647
theorem B2400617 : Blo 1598998 2400617 := bstep (se 2 (by rfl) ⟨900231, by rfl⟩ : syracuseStep 2400617 = 1800463) B1800463
theorem B12157289 : Blo 1598998 12157289 := bstep (se 2 (by rfl) ⟨4558983, by rfl⟩ : syracuseStep 12157289 = 9117967) B9117967
theorem B2400695 : Blo 1598998 2400695 := bstep (se 1 (by rfl) ⟨1800521, by rfl⟩ : syracuseStep 2400695 = 3601043) B3601043
theorem B3416539 : Blo 1598998 3416539 := bstep (se 1 (by rfl) ⟨2562404, by rfl⟩ : syracuseStep 3416539 = 5124809) B5124809
theorem B2400731 : Blo 1598998 2400731 := bstep (se 1 (by rfl) ⟨1800548, by rfl⟩ : syracuseStep 2400731 = 3601097) B3601097
theorem B5399027 : Blo 1598998 5399027 := bstep (se 1 (by rfl) ⟨4049270, by rfl⟩ : syracuseStep 5399027 = 8098541) B8098541
theorem B17302025 : Blo 1598998 17302025 := bstep (se 2 (by rfl) ⟨6488259, by rfl⟩ : syracuseStep 17302025 = 12976519) B12976519
theorem B166216373 : Blo 1598998 166216373 := bstep (se 5 (by rfl) ⟨7791392, by rfl⟩ : syracuseStep 166216373 = 15582785) B15582785
theorem B4555453 : Blo 1598998 4555453 := bstep (se 3 (by rfl) ⟨854147, by rfl⟩ : syracuseStep 4555453 = 1708295) B1708295
theorem B6669011 : Blo 1598998 6669011 := bstep (se 1 (by rfl) ⟨5001758, by rfl⟩ : syracuseStep 6669011 = 10003517) B10003517
theorem B2884457 : Blo 1598998 2884457 := bstep (se 2 (by rfl) ⟨1081671, by rfl⟩ : syracuseStep 2884457 = 2163343) B2163343
theorem B2401199 : Blo 1598998 2401199 := bstep (se 1 (by rfl) ⟨1800899, by rfl⟩ : syracuseStep 2401199 = 3601799) B3601799
theorem B4555703 : Blo 1598998 4555703 := bstep (se 1 (by rfl) ⟨3416777, by rfl⟩ : syracuseStep 4555703 = 6833555) B6833555
theorem B5768119 : Blo 1598998 5768119 := bstep (se 1 (by rfl) ⟨4326089, by rfl⟩ : syracuseStep 5768119 = 8652179) B8652179
theorem B4047803 : Blo 1598998 4047803 := bstep (se 1 (by rfl) ⟨3035852, by rfl⟩ : syracuseStep 4047803 = 6071705) B6071705
theorem B2401289 : Blo 1598998 2401289 := bstep (se 2 (by rfl) ⟨900483, by rfl⟩ : syracuseStep 2401289 = 1800967) B1800967
theorem B5399567 : Blo 1598998 5399567 := bstep (se 1 (by rfl) ⟨4049675, by rfl⟩ : syracuseStep 5399567 = 8099351) B8099351
theorem B2401319 : Blo 1598998 2401319 := bstep (se 1 (by rfl) ⟨1800989, by rfl⟩ : syracuseStep 2401319 = 3601979) B3601979
theorem B2401403 : Blo 1598998 2401403 := bstep (se 1 (by rfl) ⟨1801052, by rfl⟩ : syracuseStep 2401403 = 3602105) B3602105
theorem B2278649 : Blo 1598998 2278649 := bstep (se 2 (by rfl) ⟨854493, by rfl⟩ : syracuseStep 2278649 = 1708987) B1708987
theorem B16647691 : Blo 1598998 16647691 := bstep (se 1 (by rfl) ⟨12485768, by rfl⟩ : syracuseStep 16647691 = 24971537) B24971537
theorem B1599015 : Blo 1598998 1599015 := bstep (se 1 (by rfl) ⟨1199261, by rfl⟩ : syracuseStep 1599015 = 2398523) B2398523
theorem B1599055 : Blo 1598998 1599055 := bstep (se 1 (by rfl) ⟨1199291, by rfl⟩ : syracuseStep 1599055 = 2398583) B2398583
theorem B1599071 : Blo 1598998 1599071 := bstep (se 1 (by rfl) ⟨1199303, by rfl⟩ : syracuseStep 1599071 = 2398607) B2398607
theorem B4048481 : Blo 1598998 4048481 := bstep (se 2 (by rfl) ⟨1518180, by rfl⟩ : syracuseStep 4048481 = 3036361) B3036361
theorem B5400161 : Blo 1598998 5400161 := bstep (se 2 (by rfl) ⟨2025060, by rfl⟩ : syracuseStep 5400161 = 4050121) B4050121
theorem B3597947 : Blo 1598998 3597947 := bstep (se 1 (by rfl) ⟨2698460, by rfl⟩ : syracuseStep 3597947 = 5396921) B5396921
theorem B1599099 : Blo 1598998 1599099 := bstep (se 1 (by rfl) ⟨1199324, by rfl⟩ : syracuseStep 1599099 = 2398649) B2398649
theorem B8103563 : Blo 1598998 8103563 := bstep (se 1 (by rfl) ⟨6077672, by rfl⟩ : syracuseStep 8103563 = 12155345) B12155345
theorem B1599151 : Blo 1598998 1599151 := bstep (se 1 (by rfl) ⟨1199363, by rfl⟩ : syracuseStep 1599151 = 2398727) B2398727
theorem B6071993 : Blo 1598998 6071993 := bstep (se 2 (by rfl) ⟨2276997, by rfl⟩ : syracuseStep 6071993 = 4553995) B4553995
theorem B1599175 : Blo 1598998 1599175 := bstep (se 1 (by rfl) ⟨1199381, by rfl⟩ : syracuseStep 1599175 = 2398763) B2398763
theorem B6072023 : Blo 1598998 6072023 := bstep (se 1 (by rfl) ⟨4554017, by rfl⟩ : syracuseStep 6072023 = 9108035) B9108035
theorem B1599195 : Blo 1598998 1599195 := bstep (se 1 (by rfl) ⟨1199396, by rfl⟩ : syracuseStep 1599195 = 2398793) B2398793
theorem B3598073 : Blo 1598998 3598073 := bstep (se 2 (by rfl) ⟨1349277, by rfl⟩ : syracuseStep 3598073 = 2698555) B2698555
theorem B20506405 : Blo 1598998 20506405 := bstep (se 4 (by rfl) ⟨1922475, by rfl⟩ : syracuseStep 20506405 = 3844951) B3844951
theorem B1599271 : Blo 1598998 1599271 := bstep (se 1 (by rfl) ⟨1199453, by rfl⟩ : syracuseStep 1599271 = 2398907) B2398907
theorem B1599311 : Blo 1598998 1599311 := bstep (se 1 (by rfl) ⟨1199483, by rfl⟩ : syracuseStep 1599311 = 2398967) B2398967
theorem B1599327 : Blo 1598998 1599327 := bstep (se 1 (by rfl) ⟨1199495, by rfl⟩ : syracuseStep 1599327 = 2398991) B2398991
theorem B1599355 : Blo 1598998 1599355 := bstep (se 1 (by rfl) ⟨1199516, by rfl⟩ : syracuseStep 1599355 = 2399033) B2399033
theorem B1599407 : Blo 1598998 1599407 := bstep (se 1 (by rfl) ⟨1199555, by rfl⟩ : syracuseStep 1599407 = 2399111) B2399111
theorem B1599431 : Blo 1598998 1599431 := bstep (se 1 (by rfl) ⟨1199573, by rfl⟩ : syracuseStep 1599431 = 2399147) B2399147
theorem B1599451 : Blo 1598998 1599451 := bstep (se 1 (by rfl) ⟨1199588, by rfl⟩ : syracuseStep 1599451 = 2399177) B2399177
theorem B3598343 : Blo 1598998 3598343 := bstep (se 1 (by rfl) ⟨2698757, by rfl⟩ : syracuseStep 3598343 = 5397515) B5397515
theorem B1599527 : Blo 1598998 1599527 := bstep (se 1 (by rfl) ⟨1199645, by rfl⟩ : syracuseStep 1599527 = 2399291) B2399291
theorem B3598415 : Blo 1598998 3598415 := bstep (se 1 (by rfl) ⟨2698811, by rfl⟩ : syracuseStep 3598415 = 5397623) B5397623
theorem B1599567 : Blo 1598998 1599567 := bstep (se 1 (by rfl) ⟨1199675, by rfl⟩ : syracuseStep 1599567 = 2399351) B2399351
theorem B1599583 : Blo 1598998 1599583 := bstep (se 1 (by rfl) ⟨1199687, by rfl⟩ : syracuseStep 1599583 = 2399375) B2399375
theorem B1599611 : Blo 1598998 1599611 := bstep (se 1 (by rfl) ⟨1199708, by rfl⟩ : syracuseStep 1599611 = 2399417) B2399417
theorem B38914181 : Blo 1598998 38914181 := bstep (se 4 (by rfl) ⟨3648204, by rfl⟩ : syracuseStep 38914181 = 7296409) B7296409
theorem B6244523 : Blo 1598998 6244523 := bstep (se 1 (by rfl) ⟨4683392, by rfl⟩ : syracuseStep 6244523 = 9366785) B9366785
theorem B1599663 : Blo 1598998 1599663 := bstep (se 1 (by rfl) ⟨1199747, by rfl⟩ : syracuseStep 1599663 = 2399495) B2399495
theorem B1599687 : Blo 1598998 1599687 := bstep (se 1 (by rfl) ⟨1199765, by rfl⟩ : syracuseStep 1599687 = 2399531) B2399531
theorem B1599707 : Blo 1598998 1599707 := bstep (se 1 (by rfl) ⟨1199780, by rfl⟩ : syracuseStep 1599707 = 2399561) B2399561
theorem B1599783 : Blo 1598998 1599783 := bstep (se 1 (by rfl) ⟨1199837, by rfl⟩ : syracuseStep 1599783 = 2399675) B2399675
theorem B1599823 : Blo 1598998 1599823 := bstep (se 1 (by rfl) ⟨1199867, by rfl⟩ : syracuseStep 1599823 = 2399735) B2399735
theorem B1599839 : Blo 1598998 1599839 := bstep (se 1 (by rfl) ⟨1199879, by rfl⟩ : syracuseStep 1599839 = 2399759) B2399759
theorem B4557161 : Blo 1598998 4557161 := bstep (se 2 (by rfl) ⟨1708935, by rfl⟩ : syracuseStep 4557161 = 3417871) B3417871
theorem B1599867 : Blo 1598998 1599867 := bstep (se 1 (by rfl) ⟨1199900, by rfl⟩ : syracuseStep 1599867 = 2399801) B2399801
theorem B4557185 : Blo 1598998 4557185 := bstep (se 2 (by rfl) ⟨1708944, by rfl⟩ : syracuseStep 4557185 = 3417889) B3417889
theorem B1599919 : Blo 1598998 1599919 := bstep (se 1 (by rfl) ⟨1199939, by rfl⟩ : syracuseStep 1599919 = 2399879) B2399879
theorem B2025911 : Blo 1598998 2025911 := bstep (se 1 (by rfl) ⟨1519433, by rfl⟩ : syracuseStep 2025911 = 3038867) B3038867
theorem B1599943 : Blo 1598998 1599943 := bstep (se 1 (by rfl) ⟨1199957, by rfl⟩ : syracuseStep 1599943 = 2399915) B2399915
theorem B3598811 : Blo 1598998 3598811 := bstep (se 1 (by rfl) ⟨2699108, by rfl⟩ : syracuseStep 3598811 = 5398217) B5398217
theorem B1599963 : Blo 1598998 1599963 := bstep (se 1 (by rfl) ⟨1199972, by rfl⟩ : syracuseStep 1599963 = 2399945) B2399945
theorem B1600039 : Blo 1598998 1600039 := bstep (se 1 (by rfl) ⟨1200029, by rfl⟩ : syracuseStep 1600039 = 2400059) B2400059
theorem B1600079 : Blo 1598998 1600079 := bstep (se 1 (by rfl) ⟨1200059, by rfl⟩ : syracuseStep 1600079 = 2400119) B2400119
theorem B2026063 : Blo 1598998 2026063 := bstep (se 1 (by rfl) ⟨1519547, by rfl⟩ : syracuseStep 2026063 = 3039095) B3039095
theorem B1600095 : Blo 1598998 1600095 := bstep (se 1 (by rfl) ⟨1200071, by rfl⟩ : syracuseStep 1600095 = 2400143) B2400143
theorem B1600123 : Blo 1598998 1600123 := bstep (se 1 (by rfl) ⟨1200092, by rfl⟩ : syracuseStep 1600123 = 2400185) B2400185
theorem B1600175 : Blo 1598998 1600175 := bstep (se 1 (by rfl) ⟨1200131, by rfl⟩ : syracuseStep 1600175 = 2400263) B2400263
theorem B1600199 : Blo 1598998 1600199 := bstep (se 1 (by rfl) ⟨1200149, by rfl⟩ : syracuseStep 1600199 = 2400299) B2400299
theorem B1600219 : Blo 1598998 1600219 := bstep (se 1 (by rfl) ⟨1200164, by rfl⟩ : syracuseStep 1600219 = 2400329) B2400329
theorem B1600295 : Blo 1598998 1600295 := bstep (se 1 (by rfl) ⟨1200221, by rfl⟩ : syracuseStep 1600295 = 2400443) B2400443
theorem B20794187 : Blo 1598998 20794187 := bstep (se 1 (by rfl) ⟨15595640, by rfl⟩ : syracuseStep 20794187 = 31191281) B31191281
theorem B1600335 : Blo 1598998 1600335 := bstep (se 1 (by rfl) ⟨1200251, by rfl⟩ : syracuseStep 1600335 = 2400503) B2400503
theorem B1600351 : Blo 1598998 1600351 := bstep (se 1 (by rfl) ⟨1200263, by rfl⟩ : syracuseStep 1600351 = 2400527) B2400527
theorem B1600379 : Blo 1598998 1600379 := bstep (se 1 (by rfl) ⟨1200284, by rfl⟩ : syracuseStep 1600379 = 2400569) B2400569
theorem B3599279 : Blo 1598998 3599279 := bstep (se 1 (by rfl) ⟨2699459, by rfl⟩ : syracuseStep 3599279 = 5398919) B5398919
theorem B1600431 : Blo 1598998 1600431 := bstep (se 1 (by rfl) ⟨1200323, by rfl⟩ : syracuseStep 1600431 = 2400647) B2400647
theorem B1600455 : Blo 1598998 1600455 := bstep (se 1 (by rfl) ⟨1200341, by rfl⟩ : syracuseStep 1600455 = 2400683) B2400683
theorem B1600475 : Blo 1598998 1600475 := bstep (se 1 (by rfl) ⟨1200356, by rfl⟩ : syracuseStep 1600475 = 2400713) B2400713
theorem B4049939 : Blo 1598998 4049939 := bstep (se 1 (by rfl) ⟨3037454, by rfl⟩ : syracuseStep 4049939 = 6074909) B6074909
theorem B5401619 : Blo 1598998 5401619 := bstep (se 1 (by rfl) ⟨4051214, by rfl⟩ : syracuseStep 5401619 = 8102429) B8102429
theorem B1600551 : Blo 1598998 1600551 := bstep (se 1 (by rfl) ⟨1200413, by rfl⟩ : syracuseStep 1600551 = 2400827) B2400827
theorem B2698319 : Blo 1598998 2698319 := bstep (se 1 (by rfl) ⟨2023739, by rfl⟩ : syracuseStep 2698319 = 4047479) B4047479
theorem B1600591 : Blo 1598998 1600591 := bstep (se 1 (by rfl) ⟨1200443, by rfl⟩ : syracuseStep 1600591 = 2400887) B2400887
theorem B1600607 : Blo 1598998 1600607 := bstep (se 1 (by rfl) ⟨1200455, by rfl⟩ : syracuseStep 1600607 = 2400911) B2400911
theorem B1600635 : Blo 1598998 1600635 := bstep (se 1 (by rfl) ⟨1200476, by rfl⟩ : syracuseStep 1600635 = 2400953) B2400953
theorem B8096921 : Blo 1598998 8096921 := bstep (se 2 (by rfl) ⟨3036345, by rfl⟩ : syracuseStep 8096921 = 6072691) B6072691
theorem B3599531 : Blo 1598998 3599531 := bstep (se 1 (by rfl) ⟨2699648, by rfl⟩ : syracuseStep 3599531 = 5399297) B5399297
theorem B1600687 : Blo 1598998 1600687 := bstep (se 1 (by rfl) ⟨1200515, by rfl⟩ : syracuseStep 1600687 = 2401031) B2401031
theorem B1600711 : Blo 1598998 1600711 := bstep (se 1 (by rfl) ⟨1200533, by rfl⟩ : syracuseStep 1600711 = 2401067) B2401067
theorem B1600731 : Blo 1598998 1600731 := bstep (se 1 (by rfl) ⟨1200548, by rfl⟩ : syracuseStep 1600731 = 2401097) B2401097
theorem B1600807 : Blo 1598998 1600807 := bstep (se 1 (by rfl) ⟨1200605, by rfl⟩ : syracuseStep 1600807 = 2401211) B2401211
theorem B1600847 : Blo 1598998 1600847 := bstep (se 1 (by rfl) ⟨1200635, by rfl⟩ : syracuseStep 1600847 = 2401271) B2401271
theorem B5401943 : Blo 1598998 5401943 := bstep (se 1 (by rfl) ⟨4051457, by rfl⟩ : syracuseStep 5401943 = 8102915) B8102915
theorem B1600863 : Blo 1598998 1600863 := bstep (se 1 (by rfl) ⟨1200647, by rfl⟩ : syracuseStep 1600863 = 2401295) B2401295
theorem B1600891 : Blo 1598998 1600891 := bstep (se 1 (by rfl) ⟨1200668, by rfl⟩ : syracuseStep 1600891 = 2401337) B2401337
theorem B1600943 : Blo 1598998 1600943 := bstep (se 1 (by rfl) ⟨1200707, by rfl⟩ : syracuseStep 1600943 = 2401415) B2401415
theorem B1600967 : Blo 1598998 1600967 := bstep (se 1 (by rfl) ⟨1200725, by rfl⟩ : syracuseStep 1600967 = 2401451) B2401451
theorem B4050395 : Blo 1598998 4050395 := bstep (se 1 (by rfl) ⟨3037796, by rfl⟩ : syracuseStep 4050395 = 6075593) B6075593
theorem B1600987 : Blo 1598998 1600987 := bstep (se 1 (by rfl) ⟨1200740, by rfl⟩ : syracuseStep 1600987 = 2401481) B2401481
theorem B4107763 : Blo 1598998 4107763 := bstep (se 1 (by rfl) ⟨3080822, by rfl⟩ : syracuseStep 4107763 = 6161645) B6161645
theorem B12144167 : Blo 1598998 12144167 := bstep (se 1 (by rfl) ⟨9108125, by rfl⟩ : syracuseStep 12144167 = 18216251) B18216251
theorem B1707599 : Blo 1598998 1707599 := bstep (se 1 (by rfl) ⟨1280699, by rfl⟩ : syracuseStep 1707599 = 2561399) B2561399
theorem B5123681 : Blo 1598998 5123681 := bstep (se 2 (by rfl) ⟨1921380, by rfl⟩ : syracuseStep 5123681 = 3842761) B3842761
theorem B11685509 : Blo 1598998 11685509 := bstep (se 4 (by rfl) ⟨1095516, by rfl⟩ : syracuseStep 11685509 = 2191033) B2191033
theorem B5123731 : Blo 1598998 5123731 := bstep (se 1 (by rfl) ⟨3842798, by rfl⟩ : syracuseStep 5123731 = 7685597) B7685597
theorem B3600071 : Blo 1598998 3600071 := bstep (se 1 (by rfl) ⟨2700053, by rfl⟩ : syracuseStep 3600071 = 5400107) B5400107
theorem B12308257 : Blo 1598998 12308257 := bstep (se 2 (by rfl) ⟨4615596, by rfl⟩ : syracuseStep 12308257 = 9231193) B9231193
theorem B9113411 : Blo 1598998 9113411 := bstep (se 1 (by rfl) ⟨6835058, by rfl⟩ : syracuseStep 9113411 = 13670117) B13670117
theorem B2699183 : Blo 1598998 2699183 := bstep (se 1 (by rfl) ⟨2024387, by rfl⟩ : syracuseStep 2699183 = 4048775) B4048775
theorem B11538521 : Blo 1598998 11538521 := bstep (se 2 (by rfl) ⟨4326945, by rfl⟩ : syracuseStep 11538521 = 8653891) B8653891
theorem B6074635 : Blo 1598998 6074635 := bstep (se 1 (by rfl) ⟨4555976, by rfl⟩ : syracuseStep 6074635 = 9111953) B9111953
theorem B9113867 : Blo 1598998 9113867 := bstep (se 1 (by rfl) ⟨6835400, by rfl⟩ : syracuseStep 9113867 = 13670801) B13670801
theorem B11538749 : Blo 1598998 11538749 := bstep (se 3 (by rfl) ⟨2163515, by rfl⟩ : syracuseStep 11538749 = 4327031) B4327031
theorem B2699615 : Blo 1598998 2699615 := bstep (se 1 (by rfl) ⟨2024711, by rfl⟩ : syracuseStep 2699615 = 4049423) B4049423
theorem B5403023 : Blo 1598998 5403023 := bstep (se 1 (by rfl) ⟨4052267, by rfl⟩ : syracuseStep 5403023 = 8104535) B8104535
theorem B5763565 : Blo 1598998 5763565 := bstep (se 3 (by rfl) ⟨1080668, by rfl⟩ : syracuseStep 5763565 = 2161337) B2161337
theorem B3600935 : Blo 1598998 3600935 := bstep (se 1 (by rfl) ⟨2700701, by rfl⟩ : syracuseStep 3600935 = 5401403) B5401403
theorem B6074939 : Blo 1598998 6074939 := bstep (se 1 (by rfl) ⟨4556204, by rfl⟩ : syracuseStep 6074939 = 9112409) B9112409
theorem B6574715 : Blo 1598998 6574715 := bstep (se 1 (by rfl) ⟨4931036, by rfl⟩ : syracuseStep 6574715 = 9862073) B9862073
theorem B4051579 : Blo 1598998 4051579 := bstep (se 1 (by rfl) ⟨3038684, by rfl⟩ : syracuseStep 4051579 = 6077369) B6077369
theorem B5403347 : Blo 1598998 5403347 := bstep (se 1 (by rfl) ⟨4052510, by rfl⟩ : syracuseStep 5403347 = 8105021) B8105021
theorem B3601259 : Blo 1598998 3601259 := bstep (se 1 (by rfl) ⟨2700944, by rfl⟩ : syracuseStep 3601259 = 5401889) B5401889
theorem B2700175 : Blo 1598998 2700175 := bstep (se 1 (by rfl) ⟨2025131, by rfl⟩ : syracuseStep 2700175 = 4050263) B4050263
theorem B3601313 : Blo 1598998 3601313 := bstep (se 2 (by rfl) ⟨1350492, by rfl⟩ : syracuseStep 3601313 = 2700985) B2700985
theorem B9114551 : Blo 1598998 9114551 := bstep (se 1 (by rfl) ⟨6835913, by rfl⟩ : syracuseStep 9114551 = 13671827) B13671827
theorem B1799131 : Blo 1598998 1799131 := bstep (se 1 (by rfl) ⟨1349348, by rfl⟩ : syracuseStep 1799131 = 2698697) B2698697
theorem B15373313 : Blo 1598998 15373313 := bstep (se 2 (by rfl) ⟨5764992, by rfl⟩ : syracuseStep 15373313 = 11529985) B11529985
theorem B8647681 : Blo 1598998 8647681 := bstep (se 2 (by rfl) ⟨3242880, by rfl⟩ : syracuseStep 8647681 = 6485761) B6485761
theorem B3036179 : Blo 1598998 3036179 := bstep (se 1 (by rfl) ⟨2277134, by rfl⟩ : syracuseStep 3036179 = 4554269) B4554269
theorem B3036217 : Blo 1598998 3036217 := bstep (se 2 (by rfl) ⟨1138581, by rfl⟩ : syracuseStep 3036217 = 2277163) B2277163
theorem B49247299 : Blo 1598998 49247299 := bstep (se 1 (by rfl) ⟨36935474, by rfl⟩ : syracuseStep 49247299 = 73870949) B73870949
theorem B21894263 : Blo 1598998 21894263 := bstep (se 1 (by rfl) ⟨16420697, by rfl⟩ : syracuseStep 21894263 = 32841395) B32841395
theorem B3601655 : Blo 1598998 3601655 := bstep (se 1 (by rfl) ⟨2701241, by rfl⟩ : syracuseStep 3601655 = 5402483) B5402483
theorem B5125463 : Blo 1598998 5125463 := bstep (se 1 (by rfl) ⟨3844097, by rfl⟩ : syracuseStep 5125463 = 7688195) B7688195
theorem B3036521 : Blo 1598998 3036521 := bstep (se 2 (by rfl) ⟨1138695, by rfl⟩ : syracuseStep 3036521 = 2277391) B2277391
theorem B147789191 : Blo 1598998 147789191 := bstep (se 1 (by rfl) ⟨110841893, by rfl⟩ : syracuseStep 147789191 = 221683787) B221683787
theorem B10139053 : Blo 1598998 10139053 := bstep (se 3 (by rfl) ⟨1901072, by rfl⟩ : syracuseStep 10139053 = 3802145) B3802145
theorem B1799599 : Blo 1598998 1799599 := bstep (se 1 (by rfl) ⟨1349699, by rfl⟩ : syracuseStep 1799599 = 2699399) B2699399
theorem B2700857 : Blo 1598998 2700857 := bstep (se 2 (by rfl) ⟨1012821, by rfl⟩ : syracuseStep 2700857 = 2025643) B2025643
theorem B11531915 : Blo 1598998 11531915 := bstep (se 1 (by rfl) ⟨8648936, by rfl⟩ : syracuseStep 11531915 = 17297873) B17297873
theorem B6076093 : Blo 1598998 6076093 := bstep (se 3 (by rfl) ⟨1139267, by rfl⟩ : syracuseStep 6076093 = 2278535) B2278535
theorem B9115325 : Blo 1598998 9115325 := bstep (se 3 (by rfl) ⟨1709123, by rfl⟩ : syracuseStep 9115325 = 3418247) B3418247
theorem B10254023 : Blo 1598998 10254023 := bstep (se 1 (by rfl) ⟨7690517, by rfl⟩ : syracuseStep 10254023 = 15381035) B15381035
theorem B11695853 : Blo 1598998 11695853 := bstep (se 3 (by rfl) ⟨2192972, by rfl⟩ : syracuseStep 11695853 = 4385945) B4385945
theorem B1800031 : Blo 1598998 1800031 := bstep (se 1 (by rfl) ⟨1350023, by rfl⟩ : syracuseStep 1800031 = 2700047) B2700047
theorem B5396651 : Blo 1598998 5396651 := bstep (se 1 (by rfl) ⟨4047488, by rfl⟩ : syracuseStep 5396651 = 8094977) B8094977
theorem B1800391 : Blo 1598998 1800391 := bstep (se 1 (by rfl) ⟨1350293, by rfl⟩ : syracuseStep 1800391 = 2700587) B2700587
theorem B2701559 : Blo 1598998 2701559 := bstep (se 1 (by rfl) ⟨2026169, by rfl⟩ : syracuseStep 2701559 = 4052339) B4052339
theorem B2398559 : Blo 1598998 2398559 := bstep (se 1 (by rfl) ⟨1798919, by rfl⟩ : syracuseStep 2398559 = 3597839) B3597839
theorem B9116009 : Blo 1598998 9116009 := bstep (se 2 (by rfl) ⟨3418503, by rfl⟩ : syracuseStep 9116009 = 6837007) B6837007
theorem B2398571 : Blo 1598998 2398571 := bstep (se 1 (by rfl) ⟨1798928, by rfl⟩ : syracuseStep 2398571 = 3597857) B3597857
theorem B29186507 : Blo 1598998 29186507 := bstep (se 1 (by rfl) ⟨21889880, by rfl⟩ : syracuseStep 29186507 = 43779761) B43779761
theorem B4618739 : Blo 1598998 4618739 := bstep (se 1 (by rfl) ⟨3464054, by rfl⟩ : syracuseStep 4618739 = 6928109) B6928109
theorem B2398799 : Blo 1598998 2398799 := bstep (se 1 (by rfl) ⟨1799099, by rfl⟩ : syracuseStep 2398799 = 3598199) B3598199
theorem B3037819 : Blo 1598998 3037819 := bstep (se 1 (by rfl) ⟨2278364, by rfl⟩ : syracuseStep 3037819 = 4556729) B4556729
theorem B6077051 : Blo 1598998 6077051 := bstep (se 1 (by rfl) ⟨4557788, by rfl⟩ : syracuseStep 6077051 = 9115577) B9115577
theorem B5397191 : Blo 1598998 5397191 := bstep (se 1 (by rfl) ⟨4047893, by rfl⟩ : syracuseStep 5397191 = 8095787) B8095787
theorem B2398919 : Blo 1598998 2398919 := bstep (se 1 (by rfl) ⟨1799189, by rfl⟩ : syracuseStep 2398919 = 3598379) B3598379
theorem B4864711 : Blo 1598998 4864711 := bstep (se 1 (by rfl) ⟨3648533, by rfl⟩ : syracuseStep 4864711 = 7297067) B7297067
theorem B3037895 : Blo 1598998 3037895 := bstep (se 1 (by rfl) ⟨2278421, by rfl⟩ : syracuseStep 3037895 = 4556843) B4556843
theorem B10255049 : Blo 1598998 10255049 := bstep (se 2 (by rfl) ⟨3845643, by rfl⟩ : syracuseStep 10255049 = 7691287) B7691287
theorem B5765843 : Blo 1598998 5765843 := bstep (se 1 (by rfl) ⟨4324382, by rfl⟩ : syracuseStep 5765843 = 8648765) B8648765
theorem B11090717 : Blo 1598998 11090717 := bstep (se 3 (by rfl) ⟨2079509, by rfl⟩ : syracuseStep 11090717 = 4159019) B4159019
theorem B2399081 : Blo 1598998 2399081 := bstep (se 2 (by rfl) ⟨899655, by rfl⟩ : syracuseStep 2399081 = 1799311) B1799311
theorem B25934737 : Blo 1598998 25934737 := bstep (se 2 (by rfl) ⟨9725526, by rfl⟩ : syracuseStep 25934737 = 19451053) B19451053
theorem B2399159 : Blo 1598998 2399159 := bstep (se 1 (by rfl) ⟨1799369, by rfl⟩ : syracuseStep 2399159 = 3598739) B3598739
theorem B12155831 : Blo 1598998 12155831 := bstep (se 1 (by rfl) ⟨9116873, by rfl⟩ : syracuseStep 12155831 = 18233747) B18233747
theorem B2399195 : Blo 1598998 2399195 := bstep (se 1 (by rfl) ⟨1799396, by rfl⟩ : syracuseStep 2399195 = 3598793) B3598793
theorem B15588395 : Blo 1598998 15588395 := bstep (se 1 (by rfl) ⟨11691296, by rfl⟩ : syracuseStep 15588395 = 23382593) B23382593
theorem B3038305 : Blo 1598998 3038305 := bstep (se 2 (by rfl) ⟨1139364, by rfl⟩ : syracuseStep 3038305 = 2278729) B2278729
theorem B2432351 : Blo 1598998 2432351 := bstep (se 1 (by rfl) ⟨1824263, by rfl⟩ : syracuseStep 2432351 = 3648527) B3648527
theorem B32841085 : Blo 1598998 32841085 := bstep (se 3 (by rfl) ⟨6157703, by rfl⟩ : syracuseStep 32841085 = 12315407) B12315407
theorem B6077825 : Blo 1598998 6077825 := bstep (se 2 (by rfl) ⟨2279184, by rfl⟩ : syracuseStep 6077825 = 4558369) B4558369
theorem B2399663 : Blo 1598998 2399663 := bstep (se 1 (by rfl) ⟨1799747, by rfl⟩ : syracuseStep 2399663 = 3599495) B3599495
theorem B3038647 : Blo 1598998 3038647 := bstep (se 1 (by rfl) ⟨2278985, by rfl⟩ : syracuseStep 3038647 = 4557971) B4557971
theorem B2399753 : Blo 1598998 2399753 := bstep (se 2 (by rfl) ⟨899907, by rfl⟩ : syracuseStep 2399753 = 1799815) B1799815
theorem B3243529 : Blo 1598998 3243529 := bstep (se 2 (by rfl) ⟨1216323, by rfl⟩ : syracuseStep 3243529 = 2432647) B2432647
theorem B5398055 : Blo 1598998 5398055 := bstep (se 1 (by rfl) ⟨4048541, by rfl⟩ : syracuseStep 5398055 = 8097083) B8097083
theorem B2399783 : Blo 1598998 2399783 := bstep (se 1 (by rfl) ⟨1799837, by rfl⟩ : syracuseStep 2399783 = 3599675) B3599675
theorem B7298657 : Blo 1598998 7298657 := bstep (se 2 (by rfl) ⟨2736996, by rfl⟩ : syracuseStep 7298657 = 5473993) B5473993
theorem B2399867 : Blo 1598998 2399867 := bstep (se 1 (by rfl) ⟨1799900, by rfl⟩ : syracuseStep 2399867 = 3599801) B3599801
theorem B5398163 : Blo 1598998 5398163 := bstep (se 1 (by rfl) ⟨4048622, by rfl⟩ : syracuseStep 5398163 = 8097245) B8097245
theorem B3079927 : Blo 1598998 3079927 := bstep (se 1 (by rfl) ⟨2309945, by rfl⟩ : syracuseStep 3079927 = 4619891) B4619891
theorem B2399993 : Blo 1598998 2399993 := bstep (se 2 (by rfl) ⟨899997, by rfl⟩ : syracuseStep 2399993 = 1799995) B1799995
theorem B3039049 : Blo 1598998 3039049 := bstep (se 2 (by rfl) ⟨1139643, by rfl⟩ : syracuseStep 3039049 = 2279287) B2279287
theorem B2400095 : Blo 1598998 2400095 := bstep (se 1 (by rfl) ⟨1800071, by rfl⟩ : syracuseStep 2400095 = 3600143) B3600143
theorem B5398379 : Blo 1598998 5398379 := bstep (se 1 (by rfl) ⟨4048784, by rfl⟩ : syracuseStep 5398379 = 8097569) B8097569
theorem B2400107 : Blo 1598998 2400107 := bstep (se 1 (by rfl) ⟨1800080, by rfl⟩ : syracuseStep 2400107 = 3600161) B3600161
theorem B20791171 : Blo 1598998 20791171 := bstep (se 1 (by rfl) ⟨15593378, by rfl⟩ : syracuseStep 20791171 = 31186757) B31186757
theorem B5398433 : Blo 1598998 5398433 := bstep (se 2 (by rfl) ⟨2024412, by rfl⟩ : syracuseStep 5398433 = 4048825) B4048825
theorem B5472281 : Blo 1598998 5472281 := bstep (se 2 (by rfl) ⟨2052105, by rfl⟩ : syracuseStep 5472281 = 4104211) B4104211
theorem B7692347 : Blo 1598998 7692347 := bstep (se 1 (by rfl) ⟨5769260, by rfl⟩ : syracuseStep 7692347 = 11538521) B11538521
theorem B6078523 : Blo 1598998 6078523 := bstep (se 1 (by rfl) ⟨4558892, by rfl⟩ : syracuseStep 6078523 = 9117785) B9117785
theorem B7692499 : Blo 1598998 7692499 := bstep (se 1 (by rfl) ⟨5769374, by rfl⟩ : syracuseStep 7692499 = 11538749) B11538749
theorem B2400521 : Blo 1598998 2400521 := bstep (se 2 (by rfl) ⟨900195, by rfl⟩ : syracuseStep 2400521 = 1800391) B1800391
theorem B118300981 : Blo 1598998 118300981 := bstep (se 5 (by rfl) ⟨5545358, by rfl⟩ : syracuseStep 118300981 = 11090717) B11090717
theorem B11534683 : Blo 1598998 11534683 := bstep (se 1 (by rfl) ⟨8651012, by rfl⟩ : syracuseStep 11534683 = 17302025) B17302025
theorem B2400623 : Blo 1598998 2400623 := bstep (se 1 (by rfl) ⟨1800467, by rfl⟩ : syracuseStep 2400623 = 3600935) B3600935
theorem B4383143 : Blo 1598998 4383143 := bstep (se 1 (by rfl) ⟨3287357, by rfl⟩ : syracuseStep 4383143 = 6574715) B6574715
theorem B2400839 : Blo 1598998 2400839 := bstep (se 1 (by rfl) ⟨1800629, by rfl⟩ : syracuseStep 2400839 = 3601259) B3601259
theorem B2400875 : Blo 1598998 2400875 := bstep (se 1 (by rfl) ⟨1800656, by rfl⟩ : syracuseStep 2400875 = 3601313) B3601313
theorem B4555385 : Blo 1598998 4555385 := bstep (se 2 (by rfl) ⟨1708269, by rfl⟩ : syracuseStep 4555385 = 3416539) B3416539
theorem B7684753 : Blo 1598998 7684753 := bstep (se 2 (by rfl) ⟨2881782, by rfl⟩ : syracuseStep 7684753 = 5763565) B5763565
theorem B10248875 : Blo 1598998 10248875 := bstep (se 1 (by rfl) ⟨7686656, by rfl⟩ : syracuseStep 10248875 = 15373313) B15373313
theorem B2024119 : Blo 1598998 2024119 := bstep (se 1 (by rfl) ⟨1518089, by rfl⟩ : syracuseStep 2024119 = 3036179) B3036179
theorem B2401103 : Blo 1598998 2401103 := bstep (se 1 (by rfl) ⟨1800827, by rfl⟩ : syracuseStep 2401103 = 3601655) B3601655
theorem B3416975 : Blo 1598998 3416975 := bstep (se 1 (by rfl) ⟨2562731, by rfl⟩ : syracuseStep 3416975 = 5125463) B5125463
theorem B2024347 : Blo 1598998 2024347 := bstep (se 1 (by rfl) ⟨1518260, by rfl⟩ : syracuseStep 2024347 = 3036521) B3036521
theorem B98526127 : Blo 1598998 98526127 := bstep (se 1 (by rfl) ⟨73894595, by rfl⟩ : syracuseStep 98526127 = 147789191) B147789191
theorem B4047995 : Blo 1598998 4047995 := bstep (se 1 (by rfl) ⟨3035996, by rfl⟩ : syracuseStep 4047995 = 6071993) B6071993
theorem B4048015 : Blo 1598998 4048015 := bstep (se 1 (by rfl) ⟨3036011, by rfl⟩ : syracuseStep 4048015 = 6072023) B6072023
theorem B34579649 : Blo 1598998 34579649 := bstep (se 2 (by rfl) ⟨12967368, by rfl⟩ : syracuseStep 34579649 = 25934737) B25934737
theorem B4048289 : Blo 1598998 4048289 := bstep (se 2 (by rfl) ⟨1518108, by rfl⟩ : syracuseStep 4048289 = 3036217) B3036217
theorem B3597767 : Blo 1598998 3597767 := bstep (se 1 (by rfl) ⟨2698325, by rfl⟩ : syracuseStep 3597767 = 5396651) B5396651
theorem B4163015 : Blo 1598998 4163015 := bstep (se 1 (by rfl) ⟨3122261, by rfl⟩ : syracuseStep 4163015 = 6244523) B6244523
theorem B1599039 : Blo 1598998 1599039 := bstep (se 1 (by rfl) ⟨1199279, by rfl⟩ : syracuseStep 1599039 = 2398559) B2398559
theorem B1599047 : Blo 1598998 1599047 := bstep (se 1 (by rfl) ⟨1199285, by rfl⟩ : syracuseStep 1599047 = 2398571) B2398571
theorem B19457671 : Blo 1598998 19457671 := bstep (se 1 (by rfl) ⟨14593253, by rfl⟩ : syracuseStep 19457671 = 29186507) B29186507
theorem B1599199 : Blo 1598998 1599199 := bstep (se 1 (by rfl) ⟨1199399, by rfl⟩ : syracuseStep 1599199 = 2398799) B2398799
theorem B3598127 : Blo 1598998 3598127 := bstep (se 1 (by rfl) ⟨2698595, by rfl⟩ : syracuseStep 3598127 = 5397191) B5397191
theorem B1599279 : Blo 1598998 1599279 := bstep (se 1 (by rfl) ⟨1199459, by rfl⟩ : syracuseStep 1599279 = 2398919) B2398919
theorem B2025263 : Blo 1598998 2025263 := bstep (se 1 (by rfl) ⟨1518947, by rfl⟩ : syracuseStep 2025263 = 3037895) B3037895
theorem B43788113 : Blo 1598998 43788113 := bstep (se 2 (by rfl) ⟨16420542, by rfl⟩ : syracuseStep 43788113 = 32841085) B32841085
theorem B13862791 : Blo 1598998 13862791 := bstep (se 1 (by rfl) ⟨10397093, by rfl⟩ : syracuseStep 13862791 = 20794187) B20794187
theorem B13518737 : Blo 1598998 13518737 := bstep (se 2 (by rfl) ⟨5069526, by rfl⟩ : syracuseStep 13518737 = 10139053) B10139053
theorem B1599387 : Blo 1598998 1599387 := bstep (se 1 (by rfl) ⟨1199540, by rfl⟩ : syracuseStep 1599387 = 2399081) B2399081
theorem B31188941 : Blo 1598998 31188941 := bstep (se 3 (by rfl) ⟨5847926, by rfl⟩ : syracuseStep 31188941 = 11695853) B11695853
theorem B1599439 : Blo 1598998 1599439 := bstep (se 1 (by rfl) ⟨1199579, by rfl⟩ : syracuseStep 1599439 = 2399159) B2399159
theorem B8103887 : Blo 1598998 8103887 := bstep (se 1 (by rfl) ⟨6077915, by rfl⟩ : syracuseStep 8103887 = 12155831) B12155831
theorem B1599463 : Blo 1598998 1599463 := bstep (se 1 (by rfl) ⟨1199597, by rfl⟩ : syracuseStep 1599463 = 2399195) B2399195
theorem B1599775 : Blo 1598998 1599775 := bstep (se 1 (by rfl) ⟨1199831, by rfl⟩ : syracuseStep 1599775 = 2399663) B2399663
theorem B4106569 : Blo 1598998 4106569 := bstep (se 2 (by rfl) ⟨1539963, by rfl⟩ : syracuseStep 4106569 = 3079927) B3079927
theorem B1599835 : Blo 1598998 1599835 := bstep (se 1 (by rfl) ⟨1199876, by rfl⟩ : syracuseStep 1599835 = 2399753) B2399753
theorem B8096111 : Blo 1598998 8096111 := bstep (se 1 (by rfl) ⟨6072083, by rfl⟩ : syracuseStep 8096111 = 12144167) B12144167
theorem B3598703 : Blo 1598998 3598703 := bstep (se 1 (by rfl) ⟨2699027, by rfl⟩ : syracuseStep 3598703 = 5398055) B5398055
theorem B1599855 : Blo 1598998 1599855 := bstep (se 1 (by rfl) ⟨1199891, by rfl⟩ : syracuseStep 1599855 = 2399783) B2399783
theorem B16411009 : Blo 1598998 16411009 := bstep (se 2 (by rfl) ⟨6154128, by rfl⟩ : syracuseStep 16411009 = 12308257) B12308257
theorem B1599911 : Blo 1598998 1599911 := bstep (se 1 (by rfl) ⟨1199933, by rfl⟩ : syracuseStep 1599911 = 2399867) B2399867
theorem B3598775 : Blo 1598998 3598775 := bstep (se 1 (by rfl) ⟨2699081, by rfl⟩ : syracuseStep 3598775 = 5398163) B5398163
theorem B1599995 : Blo 1598998 1599995 := bstep (se 1 (by rfl) ⟨1199996, by rfl⟩ : syracuseStep 1599995 = 2399993) B2399993
theorem B1600063 : Blo 1598998 1600063 := bstep (se 1 (by rfl) ⟨1200047, by rfl⟩ : syracuseStep 1600063 = 2400095) B2400095
theorem B3598919 : Blo 1598998 3598919 := bstep (se 1 (by rfl) ⟨2699189, by rfl⟩ : syracuseStep 3598919 = 5398379) B5398379
theorem B1600071 : Blo 1598998 1600071 := bstep (se 1 (by rfl) ⟨1200053, by rfl⟩ : syracuseStep 1600071 = 2400107) B2400107
theorem B21908069 : Blo 1598998 21908069 := bstep (se 4 (by rfl) ⟨2053881, by rfl⟩ : syracuseStep 21908069 = 4107763) B4107763
theorem B3598955 : Blo 1598998 3598955 := bstep (se 1 (by rfl) ⟨2699216, by rfl⟩ : syracuseStep 3598955 = 5398433) B5398433
theorem B1600223 : Blo 1598998 1600223 := bstep (se 1 (by rfl) ⟨1200167, by rfl⟩ : syracuseStep 1600223 = 2400335) B2400335
theorem B5122835 : Blo 1598998 5122835 := bstep (se 1 (by rfl) ⟨3842126, by rfl⟩ : syracuseStep 5122835 = 7684253) B7684253
theorem B1600303 : Blo 1598998 1600303 := bstep (se 1 (by rfl) ⟨1200227, by rfl⟩ : syracuseStep 1600303 = 2400455) B2400455
theorem B8547227 : Blo 1598998 8547227 := bstep (se 1 (by rfl) ⟨6410420, by rfl⟩ : syracuseStep 8547227 = 12820841) B12820841
theorem B1600411 : Blo 1598998 1600411 := bstep (se 1 (by rfl) ⟨1200308, by rfl⟩ : syracuseStep 1600411 = 2400617) B2400617
theorem B8104859 : Blo 1598998 8104859 := bstep (se 1 (by rfl) ⟨6078644, by rfl⟩ : syracuseStep 8104859 = 12157289) B12157289
theorem B1600463 : Blo 1598998 1600463 := bstep (se 1 (by rfl) ⟨1200347, by rfl⟩ : syracuseStep 1600463 = 2400695) B2400695
theorem B1600487 : Blo 1598998 1600487 := bstep (se 1 (by rfl) ⟨1200365, by rfl⟩ : syracuseStep 1600487 = 2400731) B2400731
theorem B3599351 : Blo 1598998 3599351 := bstep (se 1 (by rfl) ⟨2699513, by rfl⟩ : syracuseStep 3599351 = 5399027) B5399027
theorem B4049959 : Blo 1598998 4049959 := bstep (se 1 (by rfl) ⟨3037469, by rfl⟩ : syracuseStep 4049959 = 6074939) B6074939
theorem B1600799 : Blo 1598998 1600799 := bstep (se 1 (by rfl) ⟨1200599, by rfl⟩ : syracuseStep 1600799 = 2401199) B2401199
theorem B2698535 : Blo 1598998 2698535 := bstep (se 1 (by rfl) ⟨2023901, by rfl⟩ : syracuseStep 2698535 = 4047803) B4047803
theorem B1600859 : Blo 1598998 1600859 := bstep (se 1 (by rfl) ⟨1200644, by rfl⟩ : syracuseStep 1600859 = 2401289) B2401289
theorem B3599711 : Blo 1598998 3599711 := bstep (se 1 (by rfl) ⟨2699783, by rfl⟩ : syracuseStep 3599711 = 5399567) B5399567
theorem B1600879 : Blo 1598998 1600879 := bstep (se 1 (by rfl) ⟨1200659, by rfl⟩ : syracuseStep 1600879 = 2401319) B2401319
theorem B1600935 : Blo 1598998 1600935 := bstep (se 1 (by rfl) ⟨1200701, by rfl⟩ : syracuseStep 1600935 = 2401403) B2401403
theorem B4050425 : Blo 1598998 4050425 := bstep (se 2 (by rfl) ⟨1518909, by rfl⟩ : syracuseStep 4050425 = 3037819) B3037819
theorem B5402105 : Blo 1598998 5402105 := bstep (se 2 (by rfl) ⟨2025789, by rfl⟩ : syracuseStep 5402105 = 4051579) B4051579
theorem B6073937 : Blo 1598998 6073937 := bstep (se 2 (by rfl) ⟨2277726, by rfl⟩ : syracuseStep 6073937 = 4555453) B4555453
theorem B15380077 : Blo 1598998 15380077 := bstep (se 3 (by rfl) ⟨2883764, by rfl⟩ : syracuseStep 15380077 = 5767529) B5767529
theorem B12152429 : Blo 1598998 12152429 := bstep (se 3 (by rfl) ⟨2278580, by rfl⟩ : syracuseStep 12152429 = 4557161) B4557161
theorem B2698987 : Blo 1598998 2698987 := bstep (se 1 (by rfl) ⟨2024240, by rfl⟩ : syracuseStep 2698987 = 4048481) B4048481
theorem B3600107 : Blo 1598998 3600107 := bstep (se 1 (by rfl) ⟨2700080, by rfl⟩ : syracuseStep 3600107 = 5400161) B5400161
theorem B7687943 : Blo 1598998 7687943 := bstep (se 1 (by rfl) ⟨5765957, by rfl⟩ : syracuseStep 7687943 = 11531915) B11531915
theorem B5402375 : Blo 1598998 5402375 := bstep (se 1 (by rfl) ⟨4051781, by rfl⟩ : syracuseStep 5402375 = 8103563) B8103563
theorem B6836015 : Blo 1598998 6836015 := bstep (se 1 (by rfl) ⟨5127011, by rfl⟩ : syracuseStep 6836015 = 10254023) B10254023
theorem B5402429 : Blo 1598998 5402429 := bstep (se 3 (by rfl) ⟨1012955, by rfl⟩ : syracuseStep 5402429 = 2025911) B2025911
theorem B3600233 : Blo 1598998 3600233 := bstep (se 2 (by rfl) ⟨1350087, by rfl⟩ : syracuseStep 3600233 = 2700175) B2700175
theorem B12316637 : Blo 1598998 12316637 := bstep (se 3 (by rfl) ⟨2309369, by rfl⟩ : syracuseStep 12316637 = 4618739) B4618739
theorem B11530241 : Blo 1598998 11530241 := bstep (se 2 (by rfl) ⟨4323840, by rfl⟩ : syracuseStep 11530241 = 8647681) B8647681
theorem B65663065 : Blo 1598998 65663065 := bstep (se 2 (by rfl) ⟨24623649, by rfl⟩ : syracuseStep 65663065 = 49247299) B49247299
theorem B4051073 : Blo 1598998 4051073 := bstep (se 2 (by rfl) ⟨1519152, by rfl⟩ : syracuseStep 4051073 = 3038305) B3038305
theorem B4051367 : Blo 1598998 4051367 := bstep (se 1 (by rfl) ⟨3038525, by rfl⟩ : syracuseStep 4051367 = 6077051) B6077051
theorem B6836699 : Blo 1598998 6836699 := bstep (se 1 (by rfl) ⟨5127524, by rfl⟩ : syracuseStep 6836699 = 10255049) B10255049
theorem B4051529 : Blo 1598998 4051529 := bstep (se 2 (by rfl) ⟨1519323, by rfl⟩ : syracuseStep 4051529 = 3038647) B3038647
theorem B2699959 : Blo 1598998 2699959 := bstep (se 1 (by rfl) ⟨2024969, by rfl⟩ : syracuseStep 2699959 = 4049939) B4049939
theorem B3601079 : Blo 1598998 3601079 := bstep (se 1 (by rfl) ⟨2700809, by rfl⟩ : syracuseStep 3601079 = 5401619) B5401619
theorem B22196921 : Blo 1598998 22196921 := bstep (se 2 (by rfl) ⟨8323845, by rfl⟩ : syracuseStep 22196921 = 16647691) B16647691
theorem B10392263 : Blo 1598998 10392263 := bstep (se 1 (by rfl) ⟨7794197, by rfl⟩ : syracuseStep 10392263 = 15588395) B15588395
theorem B1798879 : Blo 1598998 1798879 := bstep (se 1 (by rfl) ⟨1349159, by rfl⟩ : syracuseStep 1798879 = 2698319) B2698319
theorem B3601295 : Blo 1598998 3601295 := bstep (se 1 (by rfl) ⟨2700971, by rfl⟩ : syracuseStep 3601295 = 5401943) B5401943
theorem B4051883 : Blo 1598998 4051883 := bstep (se 1 (by rfl) ⟨3038912, by rfl⟩ : syracuseStep 4051883 = 6077825) B6077825
theorem B2700263 : Blo 1598998 2700263 := bstep (se 1 (by rfl) ⟨2025197, by rfl⟩ : syracuseStep 2700263 = 4050395) B4050395
theorem B27341873 : Blo 1598998 27341873 := bstep (se 2 (by rfl) ⟨10253202, by rfl⟩ : syracuseStep 27341873 = 20506405) B20506405
theorem B4052065 : Blo 1598998 4052065 := bstep (se 2 (by rfl) ⟨1519524, by rfl⟩ : syracuseStep 4052065 = 3039049) B3039049
theorem B6075607 : Blo 1598998 6075607 := bstep (se 1 (by rfl) ⟨4556705, by rfl⟩ : syracuseStep 6075607 = 9113411) B9113411
theorem B1799455 : Blo 1598998 1799455 := bstep (se 1 (by rfl) ⟨1349591, by rfl⟩ : syracuseStep 1799455 = 2699183) B2699183
theorem B7689595 : Blo 1598998 7689595 := bstep (se 1 (by rfl) ⟨5767196, by rfl⟩ : syracuseStep 7689595 = 11534393) B11534393
theorem B17298821 : Blo 1598998 17298821 := bstep (se 4 (by rfl) ⟨1621764, by rfl⟩ : syracuseStep 17298821 = 3243529) B3243529
theorem B1824167 : Blo 1598998 1824167 := bstep (se 1 (by rfl) ⟨1368125, by rfl⟩ : syracuseStep 1824167 = 2736251) B2736251
theorem B3036665 : Blo 1598998 3036665 := bstep (se 2 (by rfl) ⟨1138749, by rfl⟩ : syracuseStep 3036665 = 2277499) B2277499
theorem B6075911 : Blo 1598998 6075911 := bstep (se 1 (by rfl) ⟨4556933, by rfl⟩ : syracuseStep 6075911 = 9113867) B9113867
theorem B1799743 : Blo 1598998 1799743 := bstep (se 1 (by rfl) ⟨1349807, by rfl⟩ : syracuseStep 1799743 = 2699615) B2699615
theorem B3602015 : Blo 1598998 3602015 := bstep (se 1 (by rfl) ⟨2701511, by rfl⟩ : syracuseStep 3602015 = 5403023) B5403023
theorem B8099513 : Blo 1598998 8099513 := bstep (se 2 (by rfl) ⟨3037317, by rfl⟩ : syracuseStep 8099513 = 6074635) B6074635
theorem B110810915 : Blo 1598998 110810915 := bstep (se 1 (by rfl) ⟨83108186, by rfl⟩ : syracuseStep 110810915 = 166216373) B166216373
theorem B3602231 : Blo 1598998 3602231 := bstep (se 1 (by rfl) ⟨2701673, by rfl⟩ : syracuseStep 3602231 = 5403347) B5403347
theorem B6076367 : Blo 1598998 6076367 := bstep (se 1 (by rfl) ⟨4557275, by rfl⟩ : syracuseStep 6076367 = 9114551) B9114551
theorem B6076397 : Blo 1598998 6076397 := bstep (se 3 (by rfl) ⟨1139324, by rfl⟩ : syracuseStep 6076397 = 2278649) B2278649
theorem B14596175 : Blo 1598998 14596175 := bstep (se 1 (by rfl) ⟨10947131, by rfl⟩ : syracuseStep 14596175 = 21894263) B21894263
theorem B2701417 : Blo 1598998 2701417 := bstep (se 2 (by rfl) ⟨1013031, by rfl⟩ : syracuseStep 2701417 = 2026063) B2026063
theorem B6486281 : Blo 1598998 6486281 := bstep (se 2 (by rfl) ⟨2432355, by rfl⟩ : syracuseStep 6486281 = 4864711) B4864711
theorem B1800571 : Blo 1598998 1800571 := bstep (se 1 (by rfl) ⟨1350428, by rfl⟩ : syracuseStep 1800571 = 2700857) B2700857
theorem B2398631 : Blo 1598998 2398631 := bstep (se 1 (by rfl) ⟨1798973, by rfl⟩ : syracuseStep 2398631 = 3597947) B3597947
theorem B6076883 : Blo 1598998 6076883 := bstep (se 1 (by rfl) ⟨4557662, by rfl⟩ : syracuseStep 6076883 = 9115325) B9115325
theorem B2398715 : Blo 1598998 2398715 := bstep (se 1 (by rfl) ⟨1799036, by rfl⟩ : syracuseStep 2398715 = 3598073) B3598073
theorem B7690825 : Blo 1598998 7690825 := bstep (se 2 (by rfl) ⟨2884059, by rfl⟩ : syracuseStep 7690825 = 5768119) B5768119
theorem B2398841 : Blo 1598998 2398841 := bstep (se 2 (by rfl) ⟨899565, by rfl⟩ : syracuseStep 2398841 = 1799131) B1799131
theorem B2398895 : Blo 1598998 2398895 := bstep (se 1 (by rfl) ⟨1799171, by rfl⟩ : syracuseStep 2398895 = 3598343) B3598343
theorem B2398943 : Blo 1598998 2398943 := bstep (se 1 (by rfl) ⟨1799207, by rfl⟩ : syracuseStep 2398943 = 3598415) B3598415
theorem B25942787 : Blo 1598998 25942787 := bstep (se 1 (by rfl) ⟨19457090, by rfl⟩ : syracuseStep 25942787 = 38914181) B38914181
theorem B1801039 : Blo 1598998 1801039 := bstep (se 1 (by rfl) ⟨1350779, by rfl⟩ : syracuseStep 1801039 = 2701559) B2701559
theorem B4553597 : Blo 1598998 4553597 := bstep (se 3 (by rfl) ⟨853799, by rfl⟩ : syracuseStep 4553597 = 1707599) B1707599
theorem B6077339 : Blo 1598998 6077339 := bstep (se 1 (by rfl) ⟨4558004, by rfl⟩ : syracuseStep 6077339 = 9116009) B9116009
theorem B3038123 : Blo 1598998 3038123 := bstep (se 1 (by rfl) ⟨2278592, by rfl⟩ : syracuseStep 3038123 = 4557185) B4557185
theorem B2399207 : Blo 1598998 2399207 := bstep (se 1 (by rfl) ⟨1799405, by rfl⟩ : syracuseStep 2399207 = 3598811) B3598811
theorem B15375581 : Blo 1598998 15375581 := bstep (se 3 (by rfl) ⟨2882921, by rfl⟩ : syracuseStep 15375581 = 5765843) B5765843
theorem B17784029 : Blo 1598998 17784029 := bstep (se 3 (by rfl) ⟨3334505, by rfl⟩ : syracuseStep 17784029 = 6669011) B6669011
theorem B2399465 : Blo 1598998 2399465 := bstep (se 2 (by rfl) ⟨899799, by rfl⟩ : syracuseStep 2399465 = 1799599) B1799599
theorem B2399519 : Blo 1598998 2399519 := bstep (se 1 (by rfl) ⟨1799639, by rfl⟩ : syracuseStep 2399519 = 3599279) B3599279
theorem B110886245 : Blo 1598998 110886245 := bstep (se 4 (by rfl) ⟨10395585, by rfl⟩ : syracuseStep 110886245 = 20791171) B20791171
theorem B5397947 : Blo 1598998 5397947 := bstep (se 1 (by rfl) ⟨4048460, by rfl⟩ : syracuseStep 5397947 = 8096921) B8096921
theorem B2399687 : Blo 1598998 2399687 := bstep (se 1 (by rfl) ⟨1799765, by rfl⟩ : syracuseStep 2399687 = 3599531) B3599531
theorem B6831641 : Blo 1598998 6831641 := bstep (se 2 (by rfl) ⟨2561865, by rfl⟩ : syracuseStep 6831641 = 5123731) B5123731
theorem B1621567 : Blo 1598998 1621567 := bstep (se 1 (by rfl) ⟨1216175, by rfl⟩ : syracuseStep 1621567 = 2432351) B2432351
theorem B8101457 : Blo 1598998 8101457 := bstep (se 2 (by rfl) ⟨3038046, by rfl⟩ : syracuseStep 8101457 = 6076093) B6076093
theorem B7691885 : Blo 1598998 7691885 := bstep (se 3 (by rfl) ⟨1442228, by rfl⟩ : syracuseStep 7691885 = 2884457) B2884457
theorem B3415787 : Blo 1598998 3415787 := bstep (se 1 (by rfl) ⟨2561840, by rfl⟩ : syracuseStep 3415787 = 5123681) B5123681
theorem B4865771 : Blo 1598998 4865771 := bstep (se 1 (by rfl) ⟨3649328, by rfl⟩ : syracuseStep 4865771 = 7298657) B7298657
theorem B7790339 : Blo 1598998 7790339 := bstep (se 1 (by rfl) ⟨5842754, by rfl⟩ : syracuseStep 7790339 = 11685509) B11685509
theorem B2400041 : Blo 1598998 2400041 := bstep (se 2 (by rfl) ⟨900015, by rfl⟩ : syracuseStep 2400041 = 1800031) B1800031
theorem B2400047 : Blo 1598998 2400047 := bstep (se 1 (by rfl) ⟨1800035, by rfl⟩ : syracuseStep 2400047 = 3600071) B3600071
theorem B12148541 : Blo 1598998 12148541 := bstep (se 3 (by rfl) ⟨2277851, by rfl⟩ : syracuseStep 12148541 = 4555703) B4555703
theorem B5128231 : Blo 1598998 5128231 := bstep (se 1 (by rfl) ⟨3846173, by rfl⟩ : syracuseStep 5128231 = 7692347) B7692347
theorem B10256665 : Blo 1598998 10256665 := bstep (se 2 (by rfl) ⟨3846249, by rfl⟩ : syracuseStep 10256665 = 7692499) B7692499
theorem B6832583 : Blo 1598998 6832583 := bstep (se 1 (by rfl) ⟨5124437, by rfl⟩ : syracuseStep 6832583 = 10248875) B10248875
theorem B2400719 : Blo 1598998 2400719 := bstep (se 1 (by rfl) ⟨1800539, by rfl⟩ : syracuseStep 2400719 = 3601079) B3601079
theorem B2400761 : Blo 1598998 2400761 := bstep (se 2 (by rfl) ⟨900285, by rfl⟩ : syracuseStep 2400761 = 1800571) B1800571
theorem B21881345 : Blo 1598998 21881345 := bstep (se 2 (by rfl) ⟨8205504, by rfl⟩ : syracuseStep 21881345 = 16411009) B16411009
theorem B2277983 : Blo 1598998 2277983 := bstep (se 1 (by rfl) ⟨1708487, by rfl⟩ : syracuseStep 2277983 = 3416975) B3416975
theorem B2400863 : Blo 1598998 2400863 := bstep (se 1 (by rfl) ⟨1800647, by rfl⟩ : syracuseStep 2400863 = 3601295) B3601295
theorem B18227915 : Blo 1598998 18227915 := bstep (se 1 (by rfl) ⟨13670936, by rfl⟩ : syracuseStep 18227915 = 27341873) B27341873
theorem B23053099 : Blo 1598998 23053099 := bstep (se 1 (by rfl) ⟨17289824, by rfl⟩ : syracuseStep 23053099 = 34579649) B34579649
theorem B2024443 : Blo 1598998 2024443 := bstep (se 1 (by rfl) ⟨1518332, by rfl⟩ : syracuseStep 2024443 = 3036665) B3036665
theorem B2401343 : Blo 1598998 2401343 := bstep (se 1 (by rfl) ⟨1801007, by rfl⟩ : syracuseStep 2401343 = 3602015) B3602015
theorem B2401385 : Blo 1598998 2401385 := bstep (se 2 (by rfl) ⟨900519, by rfl⟩ : syracuseStep 2401385 = 1801039) B1801039
theorem B5399675 : Blo 1598998 5399675 := bstep (se 1 (by rfl) ⟨4049756, by rfl⟩ : syracuseStep 5399675 = 8099513) B8099513
theorem B11101373 : Blo 1598998 11101373 := bstep (se 3 (by rfl) ⟨2081507, by rfl⟩ : syracuseStep 11101373 = 4163015) B4163015
theorem B2401487 : Blo 1598998 2401487 := bstep (se 1 (by rfl) ⟨1801115, by rfl⟩ : syracuseStep 2401487 = 3602231) B3602231
theorem B131368169 : Blo 1598998 131368169 := bstep (se 2 (by rfl) ⟨49263063, by rfl⟩ : syracuseStep 131368169 = 98526127) B98526127
theorem B9012491 : Blo 1598998 9012491 := bstep (se 1 (by rfl) ⟨6759368, by rfl⟩ : syracuseStep 9012491 = 13518737) B13518737
theorem B20792627 : Blo 1598998 20792627 := bstep (se 1 (by rfl) ⟨15594470, by rfl⟩ : syracuseStep 20792627 = 31188941) B31188941
theorem B5399945 : Blo 1598998 5399945 := bstep (se 2 (by rfl) ⟨2024979, by rfl⟩ : syracuseStep 5399945 = 4049959) B4049959
theorem B87606805 : Blo 1598998 87606805 := bstep (se 6 (by rfl) ⟨2053284, by rfl⟩ : syracuseStep 87606805 = 4106569) B4106569
theorem B1599087 : Blo 1598998 1599087 := bstep (se 1 (by rfl) ⟨1199315, by rfl⟩ : syracuseStep 1599087 = 2398631) B2398631
theorem B1599143 : Blo 1598998 1599143 := bstep (se 1 (by rfl) ⟨1199357, by rfl⟩ : syracuseStep 1599143 = 2398715) B2398715
theorem B1599227 : Blo 1598998 1599227 := bstep (se 1 (by rfl) ⟨1199420, by rfl⟩ : syracuseStep 1599227 = 2398841) B2398841
theorem B1599263 : Blo 1598998 1599263 := bstep (se 1 (by rfl) ⟨1199447, by rfl⟩ : syracuseStep 1599263 = 2398895) B2398895
theorem B1599295 : Blo 1598998 1599295 := bstep (se 1 (by rfl) ⟨1199471, by rfl⟩ : syracuseStep 1599295 = 2398943) B2398943
theorem B17295191 : Blo 1598998 17295191 := bstep (se 1 (by rfl) ⟨12971393, by rfl⟩ : syracuseStep 17295191 = 25942787) B25942787
theorem B236767157 : Blo 1598998 236767157 := bstep (se 5 (by rfl) ⟨11098460, by rfl⟩ : syracuseStep 236767157 = 22196921) B22196921
theorem B2025415 : Blo 1598998 2025415 := bstep (se 1 (by rfl) ⟨1519061, by rfl⟩ : syracuseStep 2025415 = 3038123) B3038123
theorem B1599471 : Blo 1598998 1599471 := bstep (se 1 (by rfl) ⟨1199603, by rfl⟩ : syracuseStep 1599471 = 2399207) B2399207
theorem B5400701 : Blo 1598998 5400701 := bstep (se 3 (by rfl) ⟨1012631, by rfl⟩ : syracuseStep 5400701 = 2025263) B2025263
theorem B18229373 : Blo 1598998 18229373 := bstep (se 3 (by rfl) ⟨3418007, by rfl⟩ : syracuseStep 18229373 = 6836015) B6836015
theorem B20506769 : Blo 1598998 20506769 := bstep (se 2 (by rfl) ⟨7690038, by rfl⟩ : syracuseStep 20506769 = 15380077) B15380077
theorem B10250387 : Blo 1598998 10250387 := bstep (se 1 (by rfl) ⟨7687790, by rfl⟩ : syracuseStep 10250387 = 15375581) B15375581
theorem B11856019 : Blo 1598998 11856019 := bstep (se 1 (by rfl) ⟨8892014, by rfl⟩ : syracuseStep 11856019 = 17784029) B17784029
theorem B1599643 : Blo 1598998 1599643 := bstep (se 1 (by rfl) ⟨1199732, by rfl⟩ : syracuseStep 1599643 = 2399465) B2399465
theorem B1599679 : Blo 1598998 1599679 := bstep (se 1 (by rfl) ⟨1199759, by rfl⟩ : syracuseStep 1599679 = 2399519) B2399519
theorem B3598631 : Blo 1598998 3598631 := bstep (se 1 (by rfl) ⟨2698973, by rfl⟩ : syracuseStep 3598631 = 5397947) B5397947
theorem B1599791 : Blo 1598998 1599791 := bstep (se 1 (by rfl) ⟨1199843, by rfl⟩ : syracuseStep 1599791 = 2399687) B2399687
theorem B3598649 : Blo 1598998 3598649 := bstep (se 2 (by rfl) ⟨1349493, by rfl⟩ : syracuseStep 3598649 = 2698987) B2698987
theorem B4049291 : Blo 1598998 4049291 := bstep (se 1 (by rfl) ⟨3036968, by rfl⟩ : syracuseStep 4049291 = 6073937) B6073937
theorem B5400971 : Blo 1598998 5400971 := bstep (se 1 (by rfl) ⟨4050728, by rfl⟩ : syracuseStep 5400971 = 8101457) B8101457
theorem B18483721 : Blo 1598998 18483721 := bstep (se 2 (by rfl) ⟨6931395, by rfl⟩ : syracuseStep 18483721 = 13862791) B13862791
theorem B1600027 : Blo 1598998 1600027 := bstep (se 1 (by rfl) ⟨1200020, by rfl⟩ : syracuseStep 1600027 = 2400041) B2400041
theorem B1600031 : Blo 1598998 1600031 := bstep (se 1 (by rfl) ⟨1200023, by rfl⟩ : syracuseStep 1600031 = 2400047) B2400047
theorem B32844365 : Blo 1598998 32844365 := bstep (se 3 (by rfl) ⟨6158318, by rfl⟩ : syracuseStep 32844365 = 12316637) B12316637
theorem B7686827 : Blo 1598998 7686827 := bstep (se 1 (by rfl) ⟨5765120, by rfl⟩ : syracuseStep 7686827 = 11530241) B11530241
theorem B3648187 : Blo 1598998 3648187 := bstep (se 1 (by rfl) ⟨2736140, by rfl⟩ : syracuseStep 3648187 = 5472281) B5472281
theorem B8104697 : Blo 1598998 8104697 := bstep (se 2 (by rfl) ⟨3039261, by rfl⟩ : syracuseStep 8104697 = 6078523) B6078523
theorem B1600347 : Blo 1598998 1600347 := bstep (se 1 (by rfl) ⟨1200260, by rfl⟩ : syracuseStep 1600347 = 2400521) B2400521
theorem B1600415 : Blo 1598998 1600415 := bstep (se 1 (by rfl) ⟨1200311, by rfl⟩ : syracuseStep 1600415 = 2400623) B2400623
theorem B4557799 : Blo 1598998 4557799 := bstep (se 1 (by rfl) ⟨3418349, by rfl⟩ : syracuseStep 4557799 = 6836699) B6836699
theorem B1600559 : Blo 1598998 1600559 := bstep (se 1 (by rfl) ⟨1200419, by rfl⟩ : syracuseStep 1600559 = 2400839) B2400839
theorem B1600583 : Blo 1598998 1600583 := bstep (se 1 (by rfl) ⟨1200437, by rfl⟩ : syracuseStep 1600583 = 2400875) B2400875
theorem B15379577 : Blo 1598998 15379577 := bstep (se 2 (by rfl) ⟨5767341, by rfl⟩ : syracuseStep 15379577 = 11534683) B11534683
theorem B350203013 : Blo 1598998 350203013 := bstep (se 4 (by rfl) ⟨32831532, by rfl⟩ : syracuseStep 350203013 = 65663065) B65663065
theorem B1600735 : Blo 1598998 1600735 := bstep (se 1 (by rfl) ⟨1200551, by rfl⟩ : syracuseStep 1600735 = 2401103) B2401103
theorem B2698663 : Blo 1598998 2698663 := bstep (se 1 (by rfl) ⟨2023997, by rfl⟩ : syracuseStep 2698663 = 4047995) B4047995
theorem B2698825 : Blo 1598998 2698825 := bstep (se 2 (by rfl) ⟨1012059, by rfl⟩ : syracuseStep 2698825 = 2024119) B2024119
theorem B3599945 : Blo 1598998 3599945 := bstep (se 2 (by rfl) ⟨1349979, by rfl⟩ : syracuseStep 3599945 = 2699959) B2699959
theorem B2698859 : Blo 1598998 2698859 := bstep (se 1 (by rfl) ⟨2024144, by rfl⟩ : syracuseStep 2698859 = 4048289) B4048289
theorem B4050607 : Blo 1598998 4050607 := bstep (se 1 (by rfl) ⟨3037955, by rfl⟩ : syracuseStep 4050607 = 6075911) B6075911
theorem B2699129 : Blo 1598998 2699129 := bstep (se 2 (by rfl) ⟨1012173, by rfl⟩ : syracuseStep 2699129 = 2024347) B2024347
theorem B29192075 : Blo 1598998 29192075 := bstep (se 1 (by rfl) ⟨21894056, by rfl⟩ : syracuseStep 29192075 = 43788113) B43788113
theorem B4050911 : Blo 1598998 4050911 := bstep (se 1 (by rfl) ⟨3038183, by rfl⟩ : syracuseStep 4050911 = 6076367) B6076367
theorem B5402591 : Blo 1598998 5402591 := bstep (se 1 (by rfl) ⟨4051943, by rfl⟩ : syracuseStep 5402591 = 8103887) B8103887
theorem B4050931 : Blo 1598998 4050931 := bstep (se 1 (by rfl) ⟨3038198, by rfl⟩ : syracuseStep 4050931 = 6076397) B6076397
theorem B5402753 : Blo 1598998 5402753 := bstep (se 2 (by rfl) ⟨2026032, by rfl⟩ : syracuseStep 5402753 = 4052065) B4052065
theorem B4051255 : Blo 1598998 4051255 := bstep (se 1 (by rfl) ⟨3038441, by rfl⟩ : syracuseStep 4051255 = 6076883) B6076883
theorem B10252793 : Blo 1598998 10252793 := bstep (se 2 (by rfl) ⟨3844797, by rfl⟩ : syracuseStep 10252793 = 7689595) B7689595
theorem B3035731 : Blo 1598998 3035731 := bstep (se 1 (by rfl) ⟨2276798, by rfl⟩ : syracuseStep 3035731 = 4553597) B4553597
theorem B5698151 : Blo 1598998 5698151 := bstep (se 1 (by rfl) ⟨4273613, by rfl⟩ : syracuseStep 5698151 = 8547227) B8547227
theorem B4051559 : Blo 1598998 4051559 := bstep (se 1 (by rfl) ⟨3038669, by rfl⟩ : syracuseStep 4051559 = 6077339) B6077339
theorem B5403239 : Blo 1598998 5403239 := bstep (se 1 (by rfl) ⟨4052429, by rfl⟩ : syracuseStep 5403239 = 8104859) B8104859
theorem B1799023 : Blo 1598998 1799023 := bstep (se 1 (by rfl) ⟨1349267, by rfl⟩ : syracuseStep 1799023 = 2698535) B2698535
theorem B2700283 : Blo 1598998 2700283 := bstep (se 1 (by rfl) ⟨2025212, by rfl⟩ : syracuseStep 2700283 = 4050425) B4050425
theorem B3601403 : Blo 1598998 3601403 := bstep (se 1 (by rfl) ⟨2701052, by rfl⟩ : syracuseStep 3601403 = 5402105) B5402105
theorem B5125295 : Blo 1598998 5125295 := bstep (se 1 (by rfl) ⟨3843971, by rfl⟩ : syracuseStep 5125295 = 7687943) B7687943
theorem B3601583 : Blo 1598998 3601583 := bstep (se 1 (by rfl) ⟨2701187, by rfl⟩ : syracuseStep 3601583 = 5402375) B5402375
theorem B8099027 : Blo 1598998 8099027 := bstep (se 1 (by rfl) ⟨6074270, by rfl⟩ : syracuseStep 8099027 = 12148541) B12148541
theorem B3601619 : Blo 1598998 3601619 := bstep (se 1 (by rfl) ⟨2701214, by rfl⟩ : syracuseStep 3601619 = 5402429) B5402429
theorem B2700715 : Blo 1598998 2700715 := bstep (se 1 (by rfl) ⟨2025536, by rfl⟩ : syracuseStep 2700715 = 4051073) B4051073
theorem B3601889 : Blo 1598998 3601889 := bstep (se 2 (by rfl) ⟨1350708, by rfl⟩ : syracuseStep 3601889 = 2701417) B2701417
theorem B2922095 : Blo 1598998 2922095 := bstep (se 1 (by rfl) ⟨2191571, by rfl⟩ : syracuseStep 2922095 = 4383143) B4383143
theorem B2700911 : Blo 1598998 2700911 := bstep (se 1 (by rfl) ⟨2025683, by rfl⟩ : syracuseStep 2700911 = 4051367) B4051367
theorem B2701019 : Blo 1598998 2701019 := bstep (se 1 (by rfl) ⟨2025764, by rfl⟩ : syracuseStep 2701019 = 4051529) B4051529
theorem B157734641 : Blo 1598998 157734641 := bstep (se 2 (by rfl) ⟨59150490, by rfl⟩ : syracuseStep 157734641 = 118300981) B118300981
theorem B3036923 : Blo 1598998 3036923 := bstep (se 1 (by rfl) ⟨2277692, by rfl⟩ : syracuseStep 3036923 = 4555385) B4555385
theorem B6928175 : Blo 1598998 6928175 := bstep (se 1 (by rfl) ⟨5196131, by rfl⟩ : syracuseStep 6928175 = 10392263) B10392263
theorem B2701255 : Blo 1598998 2701255 := bstep (se 1 (by rfl) ⟨2025941, by rfl⟩ : syracuseStep 2701255 = 4051883) B4051883
theorem B1800175 : Blo 1598998 1800175 := bstep (se 1 (by rfl) ⟨1350131, by rfl⟩ : syracuseStep 1800175 = 2700263) B2700263
theorem B10254433 : Blo 1598998 10254433 := bstep (se 2 (by rfl) ⟨3845412, by rfl⟩ : syracuseStep 10254433 = 7690825) B7690825
theorem B10246337 : Blo 1598998 10246337 := bstep (se 2 (by rfl) ⟨3842376, by rfl⟩ : syracuseStep 10246337 = 7684753) B7684753
theorem B11532547 : Blo 1598998 11532547 := bstep (se 1 (by rfl) ⟨8649410, by rfl⟩ : syracuseStep 11532547 = 17298821) B17298821
theorem B2398505 : Blo 1598998 2398505 := bstep (se 2 (by rfl) ⟨899439, by rfl⟩ : syracuseStep 2398505 = 1798879) B1798879
theorem B2398511 : Blo 1598998 2398511 := bstep (se 1 (by rfl) ⟨1798883, by rfl⟩ : syracuseStep 2398511 = 3597767) B3597767
theorem B4864445 : Blo 1598998 4864445 := bstep (se 3 (by rfl) ⟨912083, by rfl⟩ : syracuseStep 4864445 = 1824167) B1824167
theorem B73873943 : Blo 1598998 73873943 := bstep (se 1 (by rfl) ⟨55405457, by rfl⟩ : syracuseStep 73873943 = 110810915) B110810915
theorem B2398751 : Blo 1598998 2398751 := bstep (se 1 (by rfl) ⟨1799063, by rfl⟩ : syracuseStep 2398751 = 3598127) B3598127
theorem B9730783 : Blo 1598998 9730783 := bstep (se 1 (by rfl) ⟨7298087, by rfl⟩ : syracuseStep 9730783 = 14596175) B14596175
theorem B18217709 : Blo 1598998 18217709 := bstep (se 3 (by rfl) ⟨3415820, by rfl⟩ : syracuseStep 18217709 = 6831641) B6831641
theorem B4324187 : Blo 1598998 4324187 := bstep (se 1 (by rfl) ⟨3243140, by rfl⟩ : syracuseStep 4324187 = 6486281) B6486281
theorem B5397353 : Blo 1598998 5397353 := bstep (se 2 (by rfl) ⟨2024007, by rfl⟩ : syracuseStep 5397353 = 4048015) B4048015
theorem B5397407 : Blo 1598998 5397407 := bstep (se 1 (by rfl) ⟨4048055, by rfl⟩ : syracuseStep 5397407 = 8096111) B8096111
theorem B2399135 : Blo 1598998 2399135 := bstep (se 1 (by rfl) ⟨1799351, by rfl⟩ : syracuseStep 2399135 = 3598703) B3598703
theorem B8100809 : Blo 1598998 8100809 := bstep (se 2 (by rfl) ⟨3037803, by rfl⟩ : syracuseStep 8100809 = 6075607) B6075607
theorem B2399183 : Blo 1598998 2399183 := bstep (se 1 (by rfl) ⟨1799387, by rfl⟩ : syracuseStep 2399183 = 3598775) B3598775
theorem B2399273 : Blo 1598998 2399273 := bstep (se 2 (by rfl) ⟨899727, by rfl⟩ : syracuseStep 2399273 = 1799455) B1799455
theorem B2399279 : Blo 1598998 2399279 := bstep (se 1 (by rfl) ⟨1799459, by rfl⟩ : syracuseStep 2399279 = 3598919) B3598919
theorem B14605379 : Blo 1598998 14605379 := bstep (se 1 (by rfl) ⟨10954034, by rfl⟩ : syracuseStep 14605379 = 21908069) B21908069
theorem B2399303 : Blo 1598998 2399303 := bstep (se 1 (by rfl) ⟨1799477, by rfl⟩ : syracuseStep 2399303 = 3598955) B3598955
theorem B3415223 : Blo 1598998 3415223 := bstep (se 1 (by rfl) ⟨2561417, by rfl⟩ : syracuseStep 3415223 = 5122835) B5122835
theorem B12975389 : Blo 1598998 12975389 := bstep (se 3 (by rfl) ⟨2432885, by rfl⟩ : syracuseStep 12975389 = 4865771) B4865771
theorem B2399567 : Blo 1598998 2399567 := bstep (se 1 (by rfl) ⟨1799675, by rfl⟩ : syracuseStep 2399567 = 3599351) B3599351
theorem B2162089 : Blo 1598998 2162089 := bstep (se 2 (by rfl) ⟨810783, by rfl⟩ : syracuseStep 2162089 = 1621567) B1621567
theorem B2399657 : Blo 1598998 2399657 := bstep (se 2 (by rfl) ⟨899871, by rfl⟩ : syracuseStep 2399657 = 1799743) B1799743
theorem B25943561 : Blo 1598998 25943561 := bstep (se 2 (by rfl) ⟨9728835, by rfl⟩ : syracuseStep 25943561 = 19457671) B19457671
theorem B2399807 : Blo 1598998 2399807 := bstep (se 1 (by rfl) ⟨1799855, by rfl⟩ : syracuseStep 2399807 = 3599711) B3599711
theorem B73924163 : Blo 1598998 73924163 := bstep (se 1 (by rfl) ⟨55443122, by rfl⟩ : syracuseStep 73924163 = 110886245) B110886245
theorem B8101619 : Blo 1598998 8101619 := bstep (se 1 (by rfl) ⟨6076214, by rfl⟩ : syracuseStep 8101619 = 12152429) B12152429
theorem B5127923 : Blo 1598998 5127923 := bstep (se 1 (by rfl) ⟨3845942, by rfl⟩ : syracuseStep 5127923 = 7691885) B7691885
theorem B2277191 : Blo 1598998 2277191 := bstep (se 1 (by rfl) ⟨1707893, by rfl⟩ : syracuseStep 2277191 = 3415787) B3415787
theorem B2400071 : Blo 1598998 2400071 := bstep (se 1 (by rfl) ⟨1800053, by rfl⟩ : syracuseStep 2400071 = 3600107) B3600107
theorem B5193559 : Blo 1598998 5193559 := bstep (se 1 (by rfl) ⟨3895169, by rfl⟩ : syracuseStep 5193559 = 7790339) B7790339
theorem B2400155 : Blo 1598998 2400155 := bstep (se 1 (by rfl) ⟨1800116, by rfl⟩ : syracuseStep 2400155 = 3600233) B3600233
theorem B13672577 : Blo 1598998 13672577 := bstep (se 2 (by rfl) ⟨5127216, by rfl⟩ : syracuseStep 13672577 = 10254433) B10254433
theorem B4555055 : Blo 1598998 4555055 := bstep (se 1 (by rfl) ⟨3416291, by rfl⟩ : syracuseStep 4555055 = 6832583) B6832583
theorem B15376729 : Blo 1598998 15376729 := bstep (se 2 (by rfl) ⟨5766273, by rfl⟩ : syracuseStep 15376729 = 11532547) B11532547
theorem B350315117 : Blo 1598998 350315117 := bstep (se 3 (by rfl) ⟨65684084, by rfl⟩ : syracuseStep 350315117 = 131368169) B131368169
theorem B2400935 : Blo 1598998 2400935 := bstep (se 1 (by rfl) ⟨1800701, by rfl⟩ : syracuseStep 2400935 = 3601403) B3601403
theorem B4047641 : Blo 1598998 4047641 := bstep (se 2 (by rfl) ⟨1517865, by rfl⟩ : syracuseStep 4047641 = 3035731) B3035731
theorem B2401055 : Blo 1598998 2401055 := bstep (se 1 (by rfl) ⟨1800791, by rfl⟩ : syracuseStep 2401055 = 3601583) B3601583
theorem B5399351 : Blo 1598998 5399351 := bstep (se 1 (by rfl) ⟨4049513, by rfl⟩ : syracuseStep 5399351 = 8099027) B8099027
theorem B2401079 : Blo 1598998 2401079 := bstep (se 1 (by rfl) ⟨1800809, by rfl⟩ : syracuseStep 2401079 = 3601619) B3601619
theorem B13861751 : Blo 1598998 13861751 := bstep (se 1 (by rfl) ⟨10396313, by rfl⟩ : syracuseStep 13861751 = 20792627) B20792627
theorem B2401259 : Blo 1598998 2401259 := bstep (se 1 (by rfl) ⟨1800944, by rfl⟩ : syracuseStep 2401259 = 3601889) B3601889
theorem B30737465 : Blo 1598998 30737465 := bstep (se 2 (by rfl) ⟨11526549, by rfl⟩ : syracuseStep 30737465 = 23053099) B23053099
theorem B51897509 : Blo 1598998 51897509 := bstep (se 4 (by rfl) ⟨4865391, by rfl⟩ : syracuseStep 51897509 = 9730783) B9730783
theorem B2024615 : Blo 1598998 2024615 := bstep (se 1 (by rfl) ⟨1518461, by rfl⟩ : syracuseStep 2024615 = 3036923) B3036923
theorem B157844771 : Blo 1598998 157844771 := bstep (se 1 (by rfl) ⟨118383578, by rfl⟩ : syracuseStep 157844771 = 236767157) B236767157
theorem B6833591 : Blo 1598998 6833591 := bstep (se 1 (by rfl) ⟨5125193, by rfl⟩ : syracuseStep 6833591 = 10250387) B10250387
theorem B1599003 : Blo 1598998 1599003 := bstep (se 1 (by rfl) ⟨1199252, by rfl⟩ : syracuseStep 1599003 = 2398505) B2398505
theorem B1599007 : Blo 1598998 1599007 := bstep (se 1 (by rfl) ⟨1199255, by rfl⟩ : syracuseStep 1599007 = 2398511) B2398511
theorem B1599167 : Blo 1598998 1599167 := bstep (se 1 (by rfl) ⟨1199375, by rfl⟩ : syracuseStep 1599167 = 2398751) B2398751
theorem B3598217 : Blo 1598998 3598217 := bstep (se 2 (by rfl) ⟨1349331, by rfl⟩ : syracuseStep 3598217 = 2698663) B2698663
theorem B3598235 : Blo 1598998 3598235 := bstep (se 1 (by rfl) ⟨2698676, by rfl⟩ : syracuseStep 3598235 = 5397353) B5397353
theorem B3598271 : Blo 1598998 3598271 := bstep (se 1 (by rfl) ⟨2698703, by rfl⟩ : syracuseStep 3598271 = 5397407) B5397407
theorem B1599423 : Blo 1598998 1599423 := bstep (se 1 (by rfl) ⟨1199567, by rfl⟩ : syracuseStep 1599423 = 2399135) B2399135
theorem B5400539 : Blo 1598998 5400539 := bstep (se 1 (by rfl) ⟨4050404, by rfl⟩ : syracuseStep 5400539 = 8100809) B8100809
theorem B1599455 : Blo 1598998 1599455 := bstep (se 1 (by rfl) ⟨1199591, by rfl⟩ : syracuseStep 1599455 = 2399183) B2399183
theorem B1599515 : Blo 1598998 1599515 := bstep (se 1 (by rfl) ⟨1199636, by rfl⟩ : syracuseStep 1599515 = 2399273) B2399273
theorem B1599519 : Blo 1598998 1599519 := bstep (se 1 (by rfl) ⟨1199639, by rfl⟩ : syracuseStep 1599519 = 2399279) B2399279
theorem B1599535 : Blo 1598998 1599535 := bstep (se 1 (by rfl) ⟨1199651, by rfl⟩ : syracuseStep 1599535 = 2399303) B2399303
theorem B3598433 : Blo 1598998 3598433 := bstep (se 2 (by rfl) ⟨1349412, by rfl⟩ : syracuseStep 3598433 = 2698825) B2698825
theorem B6072509 : Blo 1598998 6072509 := bstep (se 3 (by rfl) ⟨1138595, by rfl⟩ : syracuseStep 6072509 = 2277191) B2277191
theorem B1599711 : Blo 1598998 1599711 := bstep (se 1 (by rfl) ⟨1199783, by rfl⟩ : syracuseStep 1599711 = 2399567) B2399567
theorem B5400809 : Blo 1598998 5400809 := bstep (se 2 (by rfl) ⟨2025303, by rfl⟩ : syracuseStep 5400809 = 4050607) B4050607
theorem B1599771 : Blo 1598998 1599771 := bstep (se 1 (by rfl) ⟨1199828, by rfl⟩ : syracuseStep 1599771 = 2399657) B2399657
theorem B17295707 : Blo 1598998 17295707 := bstep (se 1 (by rfl) ⟨12971780, by rfl⟩ : syracuseStep 17295707 = 25943561) B25943561
theorem B1599871 : Blo 1598998 1599871 := bstep (se 1 (by rfl) ⟨1199903, by rfl⟩ : syracuseStep 1599871 = 2399807) B2399807
theorem B6924745 : Blo 1598998 6924745 := bstep (se 2 (by rfl) ⟨2596779, by rfl⟩ : syracuseStep 6924745 = 5193559) B5193559
theorem B5401079 : Blo 1598998 5401079 := bstep (se 1 (by rfl) ⟨4050809, by rfl⟩ : syracuseStep 5401079 = 8101619) B8101619
theorem B3418615 : Blo 1598998 3418615 := bstep (se 1 (by rfl) ⟨2563961, by rfl⟩ : syracuseStep 3418615 = 5127923) B5127923
theorem B1600047 : Blo 1598998 1600047 := bstep (se 1 (by rfl) ⟨1200035, by rfl⟩ : syracuseStep 1600047 = 2400071) B2400071
theorem B1600103 : Blo 1598998 1600103 := bstep (se 1 (by rfl) ⟨1200077, by rfl⟩ : syracuseStep 1600103 = 2400155) B2400155
theorem B5401241 : Blo 1598998 5401241 := bstep (se 2 (by rfl) ⟨2025465, by rfl⟩ : syracuseStep 5401241 = 4050931) B4050931
theorem B1600479 : Blo 1598998 1600479 := bstep (se 1 (by rfl) ⟨1200359, by rfl⟩ : syracuseStep 1600479 = 2400719) B2400719
theorem B6835195 : Blo 1598998 6835195 := bstep (se 1 (by rfl) ⟨5126396, by rfl⟩ : syracuseStep 6835195 = 10252793) B10252793
theorem B1600507 : Blo 1598998 1600507 := bstep (se 1 (by rfl) ⟨1200380, by rfl⟩ : syracuseStep 1600507 = 2400761) B2400761
theorem B13675553 : Blo 1598998 13675553 := bstep (se 2 (by rfl) ⟨5128332, by rfl⟩ : syracuseStep 13675553 = 10256665) B10256665
theorem B1600575 : Blo 1598998 1600575 := bstep (se 1 (by rfl) ⟨1200431, by rfl⟩ : syracuseStep 1600575 = 2400863) B2400863
theorem B5401673 : Blo 1598998 5401673 := bstep (se 2 (by rfl) ⟨2025627, by rfl⟩ : syracuseStep 5401673 = 4051255) B4051255
theorem B13667453 : Blo 1598998 13667453 := bstep (se 3 (by rfl) ⟨2562647, by rfl⟩ : syracuseStep 13667453 = 5125295) B5125295
theorem B12151943 : Blo 1598998 12151943 := bstep (se 1 (by rfl) ⟨9113957, by rfl⟩ : syracuseStep 12151943 = 18227915) B18227915
theorem B1600895 : Blo 1598998 1600895 := bstep (se 1 (by rfl) ⟨1200671, by rfl⟩ : syracuseStep 1600895 = 2401343) B2401343
theorem B1600923 : Blo 1598998 1600923 := bstep (se 1 (by rfl) ⟨1200692, by rfl⟩ : syracuseStep 1600923 = 2401385) B2401385
theorem B3599783 : Blo 1598998 3599783 := bstep (se 1 (by rfl) ⟨2699837, by rfl⟩ : syracuseStep 3599783 = 5399675) B5399675
theorem B7400915 : Blo 1598998 7400915 := bstep (se 1 (by rfl) ⟨5550686, by rfl⟩ : syracuseStep 7400915 = 11101373) B11101373
theorem B1600991 : Blo 1598998 1600991 := bstep (se 1 (by rfl) ⟨1200743, by rfl⟩ : syracuseStep 1600991 = 2401487) B2401487
theorem B6008327 : Blo 1598998 6008327 := bstep (se 1 (by rfl) ⟨4506245, by rfl⟩ : syracuseStep 6008327 = 9012491) B9012491
theorem B3599963 : Blo 1598998 3599963 := bstep (se 1 (by rfl) ⟨2699972, by rfl⟩ : syracuseStep 3599963 = 5399945) B5399945
theorem B11530127 : Blo 1598998 11530127 := bstep (se 1 (by rfl) ⟨8647595, by rfl⟩ : syracuseStep 11530127 = 17295191) B17295191
theorem B2699257 : Blo 1598998 2699257 := bstep (se 2 (by rfl) ⟨1012221, by rfl⟩ : syracuseStep 2699257 = 2024443) B2024443
theorem B3600377 : Blo 1598998 3600377 := bstep (se 2 (by rfl) ⟨1350141, by rfl⟩ : syracuseStep 3600377 = 2700283) B2700283
theorem B3600467 : Blo 1598998 3600467 := bstep (se 1 (by rfl) ⟨2700350, by rfl⟩ : syracuseStep 3600467 = 5400701) B5400701
theorem B12152915 : Blo 1598998 12152915 := bstep (se 1 (by rfl) ⟨9114686, by rfl⟩ : syracuseStep 12152915 = 18229373) B18229373
theorem B6074621 : Blo 1598998 6074621 := bstep (se 3 (by rfl) ⟨1138991, by rfl⟩ : syracuseStep 6074621 = 2277983) B2277983
theorem B2699527 : Blo 1598998 2699527 := bstep (se 1 (by rfl) ⟨2024645, by rfl⟩ : syracuseStep 2699527 = 4049291) B4049291
theorem B3600647 : Blo 1598998 3600647 := bstep (se 1 (by rfl) ⟨2700485, by rfl⟩ : syracuseStep 3600647 = 5400971) B5400971
theorem B5124551 : Blo 1598998 5124551 := bstep (se 1 (by rfl) ⟨3843413, by rfl⟩ : syracuseStep 5124551 = 7686827) B7686827
theorem B12145139 : Blo 1598998 12145139 := bstep (se 1 (by rfl) ⟨9108854, by rfl⟩ : syracuseStep 12145139 = 18217709) B18217709
theorem B5403131 : Blo 1598998 5403131 := bstep (se 1 (by rfl) ⟨4052348, by rfl⟩ : syracuseStep 5403131 = 8104697) B8104697
theorem B3600953 : Blo 1598998 3600953 := bstep (se 2 (by rfl) ⟨1350357, by rfl⟩ : syracuseStep 3600953 = 2700715) B2700715
theorem B9736919 : Blo 1598998 9736919 := bstep (se 1 (by rfl) ⟨7302689, by rfl⟩ : syracuseStep 9736919 = 14605379) B14605379
theorem B10253051 : Blo 1598998 10253051 := bstep (se 1 (by rfl) ⟨7689788, by rfl⟩ : syracuseStep 10253051 = 15379577) B15379577
theorem B233468675 : Blo 1598998 233468675 := bstep (se 1 (by rfl) ⟨175101506, by rfl⟩ : syracuseStep 233468675 = 350203013) B350203013
theorem B1799239 : Blo 1598998 1799239 := bstep (se 1 (by rfl) ⟨1349429, by rfl⟩ : syracuseStep 1799239 = 2698859) B2698859
theorem B1799419 : Blo 1598998 1799419 := bstep (se 1 (by rfl) ⟨1349564, by rfl⟩ : syracuseStep 1799419 = 2699129) B2699129
theorem B19461383 : Blo 1598998 19461383 := bstep (se 1 (by rfl) ⟨14596037, by rfl⟩ : syracuseStep 19461383 = 29192075) B29192075
theorem B2700553 : Blo 1598998 2700553 := bstep (se 2 (by rfl) ⟨1012707, by rfl⟩ : syracuseStep 2700553 = 2025415) B2025415
theorem B3601673 : Blo 1598998 3601673 := bstep (se 2 (by rfl) ⟨1350627, by rfl⟩ : syracuseStep 3601673 = 2701255) B2701255
theorem B2700607 : Blo 1598998 2700607 := bstep (se 1 (by rfl) ⟨2025455, by rfl⟩ : syracuseStep 2700607 = 4050911) B4050911
theorem B3601727 : Blo 1598998 3601727 := bstep (se 1 (by rfl) ⟨2701295, by rfl⟩ : syracuseStep 3601727 = 5402591) B5402591
theorem B98579845 : Blo 1598998 98579845 := bstep (se 4 (by rfl) ⟨9241860, by rfl⟩ : syracuseStep 98579845 = 18483721) B18483721
theorem B6837641 : Blo 1598998 6837641 := bstep (se 2 (by rfl) ⟨2564115, by rfl⟩ : syracuseStep 6837641 = 5128231) B5128231
theorem B3601835 : Blo 1598998 3601835 := bstep (se 1 (by rfl) ⟨2701376, by rfl⟩ : syracuseStep 3601835 = 5402753) B5402753
theorem B15808025 : Blo 1598998 15808025 := bstep (se 2 (by rfl) ⟨5928009, by rfl⟩ : syracuseStep 15808025 = 11856019) B11856019
theorem B3798767 : Blo 1598998 3798767 := bstep (se 1 (by rfl) ⟨2849075, by rfl⟩ : syracuseStep 3798767 = 5698151) B5698151
theorem B2701039 : Blo 1598998 2701039 := bstep (se 1 (by rfl) ⟨2025779, by rfl⟩ : syracuseStep 2701039 = 4051559) B4051559
theorem B3602159 : Blo 1598998 3602159 := bstep (se 1 (by rfl) ⟨2701619, by rfl⟩ : syracuseStep 3602159 = 5403239) B5403239
theorem B9107261 : Blo 1598998 9107261 := bstep (se 3 (by rfl) ⟨1707611, by rfl⟩ : syracuseStep 9107261 = 3415223) B3415223
theorem B4864249 : Blo 1598998 4864249 := bstep (se 2 (by rfl) ⟨1824093, by rfl⟩ : syracuseStep 4864249 = 3648187) B3648187
theorem B1948063 : Blo 1598998 1948063 := bstep (se 1 (by rfl) ⟨1461047, by rfl⟩ : syracuseStep 1948063 = 2922095) B2922095
theorem B1800607 : Blo 1598998 1800607 := bstep (se 1 (by rfl) ⟨1350455, by rfl⟩ : syracuseStep 1800607 = 2700911) B2700911
theorem B1800679 : Blo 1598998 1800679 := bstep (se 1 (by rfl) ⟨1350509, by rfl⟩ : syracuseStep 1800679 = 2701019) B2701019
theorem B2398697 : Blo 1598998 2398697 := bstep (se 2 (by rfl) ⟨899511, by rfl⟩ : syracuseStep 2398697 = 1799023) B1799023
theorem B4618783 : Blo 1598998 4618783 := bstep (se 1 (by rfl) ⟨3464087, by rfl⟩ : syracuseStep 4618783 = 6928175) B6928175
theorem B6077065 : Blo 1598998 6077065 := bstep (se 2 (by rfl) ⟨2278899, by rfl⟩ : syracuseStep 6077065 = 4557799) B4557799
theorem B58350253 : Blo 1598998 58350253 := bstep (se 3 (by rfl) ⟨10940672, by rfl⟩ : syracuseStep 58350253 = 21881345) B21881345
theorem B13671179 : Blo 1598998 13671179 := bstep (se 1 (by rfl) ⟨10253384, by rfl⟩ : syracuseStep 13671179 = 20506769) B20506769
theorem B6830891 : Blo 1598998 6830891 := bstep (se 1 (by rfl) ⟨5123168, by rfl⟩ : syracuseStep 6830891 = 10246337) B10246337
theorem B2399087 : Blo 1598998 2399087 := bstep (se 1 (by rfl) ⟨1799315, by rfl⟩ : syracuseStep 2399087 = 3598631) B3598631
theorem B2399099 : Blo 1598998 2399099 := bstep (se 1 (by rfl) ⟨1799324, by rfl⟩ : syracuseStep 2399099 = 3598649) B3598649
theorem B3242963 : Blo 1598998 3242963 := bstep (se 1 (by rfl) ⟨2432222, by rfl⟩ : syracuseStep 3242963 = 4864445) B4864445
theorem B49249295 : Blo 1598998 49249295 := bstep (se 1 (by rfl) ⟨36936971, by rfl⟩ : syracuseStep 49249295 = 73873943) B73873943
theorem B21896243 : Blo 1598998 21896243 := bstep (se 1 (by rfl) ⟨16422182, by rfl⟩ : syracuseStep 21896243 = 32844365) B32844365
theorem B2882785 : Blo 1598998 2882785 := bstep (se 2 (by rfl) ⟨1081044, by rfl⟩ : syracuseStep 2882785 = 2162089) B2162089
theorem B2882791 : Blo 1598998 2882791 := bstep (se 1 (by rfl) ⟨2162093, by rfl⟩ : syracuseStep 2882791 = 4324187) B4324187
theorem B420625709 : Blo 1598998 420625709 := bstep (se 3 (by rfl) ⟨78867320, by rfl⟩ : syracuseStep 420625709 = 157734641) B157734641
theorem B116809073 : Blo 1598998 116809073 := bstep (se 2 (by rfl) ⟨43803402, by rfl⟩ : syracuseStep 116809073 = 87606805) B87606805
theorem B8650259 : Blo 1598998 8650259 := bstep (se 1 (by rfl) ⟨6487694, by rfl⟩ : syracuseStep 8650259 = 12975389) B12975389
theorem B49282775 : Blo 1598998 49282775 := bstep (se 1 (by rfl) ⟨36962081, by rfl⟩ : syracuseStep 49282775 = 73924163) B73924163
theorem B2399963 : Blo 1598998 2399963 := bstep (se 1 (by rfl) ⟨1799972, by rfl⟩ : syracuseStep 2399963 = 3599945) B3599945
theorem B2400233 : Blo 1598998 2400233 := bstep (se 2 (by rfl) ⟨900087, by rfl⟩ : syracuseStep 2400233 = 1800175) B1800175
theorem B2400311 : Blo 1598998 2400311 := bstep (se 1 (by rfl) ⟨1800233, by rfl⟩ : syracuseStep 2400311 = 3600467) B3600467
theorem B8101943 : Blo 1598998 8101943 := bstep (se 1 (by rfl) ⟨6076457, by rfl⟩ : syracuseStep 8101943 = 12152915) B12152915
theorem B2400431 : Blo 1598998 2400431 := bstep (se 1 (by rfl) ⟨1800323, by rfl⟩ : syracuseStep 2400431 = 3600647) B3600647
theorem B2400635 : Blo 1598998 2400635 := bstep (se 1 (by rfl) ⟨1800476, by rfl⟩ : syracuseStep 2400635 = 3600953) B3600953
theorem B5398973 : Blo 1598998 5398973 := bstep (se 3 (by rfl) ⟨1012307, by rfl⟩ : syracuseStep 5398973 = 2024615) B2024615
theorem B2597417 : Blo 1598998 2597417 := bstep (se 2 (by rfl) ⟨974031, by rfl⟩ : syracuseStep 2597417 = 1948063) B1948063
theorem B2400809 : Blo 1598998 2400809 := bstep (se 2 (by rfl) ⟨900303, by rfl⟩ : syracuseStep 2400809 = 1800607) B1800607
theorem B9232993 : Blo 1598998 9232993 := bstep (se 2 (by rfl) ⟨3462372, by rfl⟩ : syracuseStep 9232993 = 6924745) B6924745
theorem B2400905 : Blo 1598998 2400905 := bstep (se 2 (by rfl) ⟨900339, by rfl⟩ : syracuseStep 2400905 = 1800679) B1800679
theorem B2401115 : Blo 1598998 2401115 := bstep (se 1 (by rfl) ⟨1800836, by rfl⟩ : syracuseStep 2401115 = 3601673) B3601673
theorem B8102753 : Blo 1598998 8102753 := bstep (se 2 (by rfl) ⟨3038532, by rfl⟩ : syracuseStep 8102753 = 6077065) B6077065
theorem B2401151 : Blo 1598998 2401151 := bstep (se 1 (by rfl) ⟨1800863, by rfl⟩ : syracuseStep 2401151 = 3601727) B3601727
theorem B77800337 : Blo 1598998 77800337 := bstep (se 2 (by rfl) ⟨29175126, by rfl⟩ : syracuseStep 77800337 = 58350253) B58350253
theorem B46121885 : Blo 1598998 46121885 := bstep (se 3 (by rfl) ⟨8647853, by rfl⟩ : syracuseStep 46121885 = 17295707) B17295707
theorem B2401223 : Blo 1598998 2401223 := bstep (se 1 (by rfl) ⟨1800917, by rfl⟩ : syracuseStep 2401223 = 3601835) B3601835
theorem B4555727 : Blo 1598998 4555727 := bstep (se 1 (by rfl) ⟨3416795, by rfl⟩ : syracuseStep 4555727 = 6833591) B6833591
theorem B2532511 : Blo 1598998 2532511 := bstep (se 1 (by rfl) ⟨1899383, by rfl⟩ : syracuseStep 2532511 = 3798767) B3798767
theorem B2401439 : Blo 1598998 2401439 := bstep (se 1 (by rfl) ⟨1801079, by rfl⟩ : syracuseStep 2401439 = 3602159) B3602159
theorem B13665469 : Blo 1598998 13665469 := bstep (se 3 (by rfl) ⟨2562275, by rfl⟩ : syracuseStep 13665469 = 5124551) B5124551
theorem B6071507 : Blo 1598998 6071507 := bstep (se 1 (by rfl) ⟨4553630, by rfl⟩ : syracuseStep 6071507 = 9107261) B9107261
theorem B4048339 : Blo 1598998 4048339 := bstep (se 1 (by rfl) ⟨3036254, by rfl⟩ : syracuseStep 4048339 = 6072509) B6072509
theorem B3843713 : Blo 1598998 3843713 := bstep (se 2 (by rfl) ⟨1441392, by rfl⟩ : syracuseStep 3843713 = 2882785) B2882785
theorem B3843721 : Blo 1598998 3843721 := bstep (se 2 (by rfl) ⟨1441395, by rfl⟩ : syracuseStep 3843721 = 2882791) B2882791
theorem B1599131 : Blo 1598998 1599131 := bstep (se 1 (by rfl) ⟨1199348, by rfl⟩ : syracuseStep 1599131 = 2398697) B2398697
theorem B1599391 : Blo 1598998 1599391 := bstep (se 1 (by rfl) ⟨1199543, by rfl⟩ : syracuseStep 1599391 = 2399087) B2399087
theorem B1599399 : Blo 1598998 1599399 := bstep (se 1 (by rfl) ⟨1199549, by rfl⟩ : syracuseStep 1599399 = 2399099) B2399099
theorem B9111635 : Blo 1598998 9111635 := bstep (se 1 (by rfl) ⟨6833726, by rfl⟩ : syracuseStep 9111635 = 13667453) B13667453
theorem B4933943 : Blo 1598998 4933943 := bstep (se 1 (by rfl) ⟨3700457, by rfl⟩ : syracuseStep 4933943 = 7400915) B7400915
theorem B36964669 : Blo 1598998 36964669 := bstep (se 3 (by rfl) ⟨6930875, by rfl⟩ : syracuseStep 36964669 = 13861751) B13861751
theorem B1599975 : Blo 1598998 1599975 := bstep (se 1 (by rfl) ⟨1199981, by rfl⟩ : syracuseStep 1599975 = 2399963) B2399963
theorem B7686751 : Blo 1598998 7686751 := bstep (se 1 (by rfl) ⟨5765063, by rfl⟩ : syracuseStep 7686751 = 11530127) B11530127
theorem B1600155 : Blo 1598998 1600155 := bstep (se 1 (by rfl) ⟨1200116, by rfl⟩ : syracuseStep 1600155 = 2400233) B2400233
theorem B3599009 : Blo 1598998 3599009 := bstep (se 2 (by rfl) ⟨1349628, by rfl⟩ : syracuseStep 3599009 = 2699257) B2699257
theorem B4049747 : Blo 1598998 4049747 := bstep (se 1 (by rfl) ⟨3037310, by rfl⟩ : syracuseStep 4049747 = 6074621) B6074621
theorem B8096759 : Blo 1598998 8096759 := bstep (se 1 (by rfl) ⟨6072569, by rfl⟩ : syracuseStep 8096759 = 12145139) B12145139
theorem B3599369 : Blo 1598998 3599369 := bstep (se 2 (by rfl) ⟨1349763, by rfl⟩ : syracuseStep 3599369 = 2699527) B2699527
theorem B1600623 : Blo 1598998 1600623 := bstep (se 1 (by rfl) ⟨1200467, by rfl⟩ : syracuseStep 1600623 = 2400935) B2400935
theorem B6491279 : Blo 1598998 6491279 := bstep (se 1 (by rfl) ⟨4868459, by rfl⟩ : syracuseStep 6491279 = 9736919) B9736919
theorem B6835367 : Blo 1598998 6835367 := bstep (se 1 (by rfl) ⟨5126525, by rfl⟩ : syracuseStep 6835367 = 10253051) B10253051
theorem B2698427 : Blo 1598998 2698427 := bstep (se 1 (by rfl) ⟨2023820, by rfl⟩ : syracuseStep 2698427 = 4047641) B4047641
theorem B1600703 : Blo 1598998 1600703 := bstep (se 1 (by rfl) ⟨1200527, by rfl⟩ : syracuseStep 1600703 = 2401055) B2401055
theorem B3599567 : Blo 1598998 3599567 := bstep (se 1 (by rfl) ⟨2699675, by rfl⟩ : syracuseStep 3599567 = 5399351) B5399351
theorem B1600719 : Blo 1598998 1600719 := bstep (se 1 (by rfl) ⟨1200539, by rfl⟩ : syracuseStep 1600719 = 2401079) B2401079
theorem B1600839 : Blo 1598998 1600839 := bstep (se 1 (by rfl) ⟨1200629, by rfl⟩ : syracuseStep 1600839 = 2401259) B2401259
theorem B4558153 : Blo 1598998 4558153 := bstep (se 2 (by rfl) ⟨1709307, by rfl⟩ : syracuseStep 4558153 = 3418615) B3418615
theorem B20491643 : Blo 1598998 20491643 := bstep (se 1 (by rfl) ⟨15368732, by rfl⟩ : syracuseStep 20491643 = 30737465) B30737465
theorem B34598339 : Blo 1598998 34598339 := bstep (se 1 (by rfl) ⟨25948754, by rfl⟩ : syracuseStep 34598339 = 51897509) B51897509
theorem B105229847 : Blo 1598998 105229847 := bstep (se 1 (by rfl) ⟨78922385, by rfl⟩ : syracuseStep 105229847 = 157844771) B157844771
theorem B4558427 : Blo 1598998 4558427 := bstep (se 1 (by rfl) ⟨3418820, by rfl⟩ : syracuseStep 4558427 = 6837641) B6837641
theorem B3600359 : Blo 1598998 3600359 := bstep (se 1 (by rfl) ⟨2700269, by rfl⟩ : syracuseStep 3600359 = 5400539) B5400539
theorem B9113593 : Blo 1598998 9113593 := bstep (se 2 (by rfl) ⟨3417597, by rfl⟩ : syracuseStep 9113593 = 6835195) B6835195
theorem B3600539 : Blo 1598998 3600539 := bstep (se 1 (by rfl) ⟨2700404, by rfl⟩ : syracuseStep 3600539 = 5400809) B5400809
theorem B3600719 : Blo 1598998 3600719 := bstep (se 1 (by rfl) ⟨2700539, by rfl⟩ : syracuseStep 3600719 = 5401079) B5401079
theorem B3600737 : Blo 1598998 3600737 := bstep (se 2 (by rfl) ⟨1350276, by rfl⟩ : syracuseStep 3600737 = 2700553) B2700553
theorem B3600809 : Blo 1598998 3600809 := bstep (se 2 (by rfl) ⟨1350303, by rfl⟩ : syracuseStep 3600809 = 2700607) B2700607
theorem B3600827 : Blo 1598998 3600827 := bstep (se 1 (by rfl) ⟨2700620, by rfl⟩ : syracuseStep 3600827 = 5401241) B5401241
theorem B9114119 : Blo 1598998 9114119 := bstep (se 1 (by rfl) ⟨6835589, by rfl⟩ : syracuseStep 9114119 = 13671179) B13671179
theorem B3601115 : Blo 1598998 3601115 := bstep (se 1 (by rfl) ⟨2700836, by rfl⟩ : syracuseStep 3601115 = 5401673) B5401673
theorem B280417139 : Blo 1598998 280417139 := bstep (se 1 (by rfl) ⟨210312854, by rfl⟩ : syracuseStep 280417139 = 420625709) B420625709
theorem B3601385 : Blo 1598998 3601385 := bstep (se 2 (by rfl) ⟨1350519, by rfl⟩ : syracuseStep 3601385 = 2701039) B2701039
theorem B32855183 : Blo 1598998 32855183 := bstep (se 1 (by rfl) ⟨24641387, by rfl⟩ : syracuseStep 32855183 = 49282775) B49282775
theorem B9115051 : Blo 1598998 9115051 := bstep (se 1 (by rfl) ⟨6836288, by rfl⟩ : syracuseStep 9115051 = 13672577) B13672577
theorem B3036703 : Blo 1598998 3036703 := bstep (se 1 (by rfl) ⟨2277527, by rfl⟩ : syracuseStep 3036703 = 4555055) B4555055
theorem B6485665 : Blo 1598998 6485665 := bstep (se 2 (by rfl) ⟨2432124, by rfl⟩ : syracuseStep 6485665 = 4864249) B4864249
theorem B3602087 : Blo 1598998 3602087 := bstep (se 1 (by rfl) ⟨2701565, by rfl⟩ : syracuseStep 3602087 = 5403131) B5403131
theorem B233543411 : Blo 1598998 233543411 := bstep (se 1 (by rfl) ⟨175157558, by rfl⟩ : syracuseStep 233543411 = 350315117) B350315117
theorem B20502305 : Blo 1598998 20502305 := bstep (se 2 (by rfl) ⟨7688364, by rfl⟩ : syracuseStep 20502305 = 15376729) B15376729
theorem B155645783 : Blo 1598998 155645783 := bstep (se 1 (by rfl) ⟨116734337, by rfl⟩ : syracuseStep 155645783 = 233468675) B233468675
theorem B6158377 : Blo 1598998 6158377 := bstep (se 2 (by rfl) ⟨2309391, by rfl⟩ : syracuseStep 6158377 = 4618783) B4618783
theorem B12974255 : Blo 1598998 12974255 := bstep (se 1 (by rfl) ⟨9730691, by rfl⟩ : syracuseStep 12974255 = 19461383) B19461383
theorem B2398811 : Blo 1598998 2398811 := bstep (se 1 (by rfl) ⟨1799108, by rfl⟩ : syracuseStep 2398811 = 3598217) B3598217
theorem B2398823 : Blo 1598998 2398823 := bstep (se 1 (by rfl) ⟨1799117, by rfl⟩ : syracuseStep 2398823 = 3598235) B3598235
theorem B2398847 : Blo 1598998 2398847 := bstep (se 1 (by rfl) ⟨1799135, by rfl⟩ : syracuseStep 2398847 = 3598271) B3598271
theorem B2398955 : Blo 1598998 2398955 := bstep (se 1 (by rfl) ⟨1799216, by rfl⟩ : syracuseStep 2398955 = 3598433) B3598433
theorem B42154733 : Blo 1598998 42154733 := bstep (se 3 (by rfl) ⟨7904012, by rfl⟩ : syracuseStep 42154733 = 15808025) B15808025
theorem B2398985 : Blo 1598998 2398985 := bstep (se 2 (by rfl) ⟨899619, by rfl⟩ : syracuseStep 2398985 = 1799239) B1799239
theorem B2399225 : Blo 1598998 2399225 := bstep (se 2 (by rfl) ⟨899709, by rfl⟩ : syracuseStep 2399225 = 1799419) B1799419
theorem B131439793 : Blo 1598998 131439793 := bstep (se 2 (by rfl) ⟨49289922, by rfl⟩ : syracuseStep 131439793 = 98579845) B98579845
theorem B4553927 : Blo 1598998 4553927 := bstep (se 1 (by rfl) ⟨3415445, by rfl⟩ : syracuseStep 4553927 = 6830891) B6830891
theorem B2161975 : Blo 1598998 2161975 := bstep (se 1 (by rfl) ⟨1621481, by rfl⟩ : syracuseStep 2161975 = 3242963) B3242963
theorem B32832863 : Blo 1598998 32832863 := bstep (se 1 (by rfl) ⟨24624647, by rfl⟩ : syracuseStep 32832863 = 49249295) B49249295
theorem B9117035 : Blo 1598998 9117035 := bstep (se 1 (by rfl) ⟨6837776, by rfl⟩ : syracuseStep 9117035 = 13675553) B13675553
theorem B14597495 : Blo 1598998 14597495 := bstep (se 1 (by rfl) ⟨10948121, by rfl⟩ : syracuseStep 14597495 = 21896243) B21896243
theorem B8101295 : Blo 1598998 8101295 := bstep (se 1 (by rfl) ⟨6075971, by rfl⟩ : syracuseStep 8101295 = 12151943) B12151943
theorem B77872715 : Blo 1598998 77872715 := bstep (se 1 (by rfl) ⟨58404536, by rfl⟩ : syracuseStep 77872715 = 116809073) B116809073
theorem B2399855 : Blo 1598998 2399855 := bstep (se 1 (by rfl) ⟨1799891, by rfl⟩ : syracuseStep 2399855 = 3599783) B3599783
theorem B4005551 : Blo 1598998 4005551 := bstep (se 1 (by rfl) ⟨3004163, by rfl⟩ : syracuseStep 4005551 = 6008327) B6008327
theorem B5766839 : Blo 1598998 5766839 := bstep (se 1 (by rfl) ⟨4325129, by rfl⟩ : syracuseStep 5766839 = 8650259) B8650259
theorem B2399975 : Blo 1598998 2399975 := bstep (se 1 (by rfl) ⟨1799981, by rfl⟩ : syracuseStep 2399975 = 3599963) B3599963
theorem B2400251 : Blo 1598998 2400251 := bstep (se 1 (by rfl) ⟨1800188, by rfl⟩ : syracuseStep 2400251 = 3600377) B3600377
theorem B2400359 : Blo 1598998 2400359 := bstep (se 1 (by rfl) ⟨1800269, by rfl⟩ : syracuseStep 2400359 = 3600539) B3600539
theorem B2400479 : Blo 1598998 2400479 := bstep (se 1 (by rfl) ⟨1800359, by rfl⟩ : syracuseStep 2400479 = 3600719) B3600719
theorem B2400491 : Blo 1598998 2400491 := bstep (se 1 (by rfl) ⟨1800368, by rfl⟩ : syracuseStep 2400491 = 3600737) B3600737
theorem B2400539 : Blo 1598998 2400539 := bstep (se 1 (by rfl) ⟨1800404, by rfl⟩ : syracuseStep 2400539 = 3600809) B3600809
theorem B2400551 : Blo 1598998 2400551 := bstep (se 1 (by rfl) ⟨1800413, by rfl⟩ : syracuseStep 2400551 = 3600827) B3600827
theorem B2400743 : Blo 1598998 2400743 := bstep (se 1 (by rfl) ⟨1800557, by rfl⟩ : syracuseStep 2400743 = 3601115) B3601115
theorem B49242629 : Blo 1598998 49242629 := bstep (se 4 (by rfl) ⟨4616496, by rfl⟩ : syracuseStep 49242629 = 9232993) B9232993
theorem B2400923 : Blo 1598998 2400923 := bstep (se 1 (by rfl) ⟨1800692, by rfl⟩ : syracuseStep 2400923 = 3601385) B3601385
theorem B10249001 : Blo 1598998 10249001 := bstep (se 2 (by rfl) ⟨3843375, by rfl⟩ : syracuseStep 10249001 = 7686751) B7686751
theorem B4047671 : Blo 1598998 4047671 := bstep (se 1 (by rfl) ⟨3035753, by rfl⟩ : syracuseStep 4047671 = 6071507) B6071507
theorem B2401391 : Blo 1598998 2401391 := bstep (se 1 (by rfl) ⟨1801043, by rfl⟩ : syracuseStep 2401391 = 3602087) B3602087
theorem B175253057 : Blo 1598998 175253057 := bstep (se 2 (by rfl) ⟨65719896, by rfl⟩ : syracuseStep 175253057 = 131439793) B131439793
theorem B18220625 : Blo 1598998 18220625 := bstep (se 2 (by rfl) ⟨6832734, by rfl⟩ : syracuseStep 18220625 = 13665469) B13665469
theorem B10249901 : Blo 1598998 10249901 := bstep (se 3 (by rfl) ⟨1921856, by rfl⟩ : syracuseStep 10249901 = 3843713) B3843713
theorem B1599207 : Blo 1598998 1599207 := bstep (se 1 (by rfl) ⟨1199405, by rfl⟩ : syracuseStep 1599207 = 2398811) B2398811
theorem B1599215 : Blo 1598998 1599215 := bstep (se 1 (by rfl) ⟨1199411, by rfl⟩ : syracuseStep 1599215 = 2398823) B2398823
theorem B1599231 : Blo 1598998 1599231 := bstep (se 1 (by rfl) ⟨1199423, by rfl⟩ : syracuseStep 1599231 = 2398847) B2398847
theorem B1599303 : Blo 1598998 1599303 := bstep (se 1 (by rfl) ⟨1199477, by rfl⟩ : syracuseStep 1599303 = 2398955) B2398955
theorem B1599323 : Blo 1598998 1599323 := bstep (se 1 (by rfl) ⟨1199492, by rfl⟩ : syracuseStep 1599323 = 2398985) B2398985
theorem B1599483 : Blo 1598998 1599483 := bstep (se 1 (by rfl) ⟨1199612, by rfl⟩ : syracuseStep 1599483 = 2399225) B2399225
theorem B4048937 : Blo 1598998 4048937 := bstep (se 2 (by rfl) ⟨1518351, by rfl⟩ : syracuseStep 4048937 = 3036703) B3036703
theorem B4327519 : Blo 1598998 4327519 := bstep (se 1 (by rfl) ⟨3245639, by rfl⟩ : syracuseStep 4327519 = 6491279) B6491279
theorem B4556911 : Blo 1598998 4556911 := bstep (se 1 (by rfl) ⟨3417683, by rfl⟩ : syracuseStep 4556911 = 6835367) B6835367
theorem B5400863 : Blo 1598998 5400863 := bstep (se 1 (by rfl) ⟨4050647, by rfl⟩ : syracuseStep 5400863 = 8101295) B8101295
theorem B51915143 : Blo 1598998 51915143 := bstep (se 1 (by rfl) ⟨38936357, by rfl⟩ : syracuseStep 51915143 = 77872715) B77872715
theorem B1599903 : Blo 1598998 1599903 := bstep (se 1 (by rfl) ⟨1199927, by rfl⟩ : syracuseStep 1599903 = 2399855) B2399855
theorem B3844559 : Blo 1598998 3844559 := bstep (se 1 (by rfl) ⟨2883419, by rfl⟩ : syracuseStep 3844559 = 5766839) B5766839
theorem B1599983 : Blo 1598998 1599983 := bstep (se 1 (by rfl) ⟨1199987, by rfl⟩ : syracuseStep 1599983 = 2399975) B2399975
theorem B12151457 : Blo 1598998 12151457 := bstep (se 2 (by rfl) ⟨4556796, by rfl⟩ : syracuseStep 12151457 = 9113593) B9113593
theorem B1600167 : Blo 1598998 1600167 := bstep (se 1 (by rfl) ⟨1200125, by rfl⟩ : syracuseStep 1600167 = 2400251) B2400251
theorem B1600207 : Blo 1598998 1600207 := bstep (se 1 (by rfl) ⟨1200155, by rfl⟩ : syracuseStep 1600207 = 2400311) B2400311
theorem B5401295 : Blo 1598998 5401295 := bstep (se 1 (by rfl) ⟨4050971, by rfl⟩ : syracuseStep 5401295 = 8101943) B8101943
theorem B8211169 : Blo 1598998 8211169 := bstep (se 2 (by rfl) ⟨3079188, by rfl⟩ : syracuseStep 8211169 = 6158377) B6158377
theorem B1600287 : Blo 1598998 1600287 := bstep (se 1 (by rfl) ⟨1200215, by rfl⟩ : syracuseStep 1600287 = 2400431) B2400431
theorem B1600423 : Blo 1598998 1600423 := bstep (se 1 (by rfl) ⟨1200317, by rfl⟩ : syracuseStep 1600423 = 2400635) B2400635
theorem B3599315 : Blo 1598998 3599315 := bstep (se 1 (by rfl) ⟨2699486, by rfl⟩ : syracuseStep 3599315 = 5398973) B5398973
theorem B1731611 : Blo 1598998 1731611 := bstep (se 1 (by rfl) ⟨1298708, by rfl⟩ : syracuseStep 1731611 = 2597417) B2597417
theorem B1600539 : Blo 1598998 1600539 := bstep (se 1 (by rfl) ⟨1200404, by rfl⟩ : syracuseStep 1600539 = 2400809) B2400809
theorem B49286225 : Blo 1598998 49286225 := bstep (se 2 (by rfl) ⟨18482334, by rfl⟩ : syracuseStep 49286225 = 36964669) B36964669
theorem B1600603 : Blo 1598998 1600603 := bstep (se 1 (by rfl) ⟨1200452, by rfl⟩ : syracuseStep 1600603 = 2400905) B2400905
theorem B1600743 : Blo 1598998 1600743 := bstep (se 1 (by rfl) ⟨1200557, by rfl⟩ : syracuseStep 1600743 = 2401115) B2401115
theorem B5401835 : Blo 1598998 5401835 := bstep (se 1 (by rfl) ⟨4051376, by rfl⟩ : syracuseStep 5401835 = 8102753) B8102753
theorem B186944759 : Blo 1598998 186944759 := bstep (se 1 (by rfl) ⟨140208569, by rfl⟩ : syracuseStep 186944759 = 280417139) B280417139
theorem B1600767 : Blo 1598998 1600767 := bstep (se 1 (by rfl) ⟨1200575, by rfl⟩ : syracuseStep 1600767 = 2401151) B2401151
theorem B51866891 : Blo 1598998 51866891 := bstep (se 1 (by rfl) ⟨38900168, by rfl⟩ : syracuseStep 51866891 = 77800337) B77800337
theorem B30747923 : Blo 1598998 30747923 := bstep (se 1 (by rfl) ⟨23060942, by rfl⟩ : syracuseStep 30747923 = 46121885) B46121885
theorem B1600815 : Blo 1598998 1600815 := bstep (se 1 (by rfl) ⟨1200611, by rfl⟩ : syracuseStep 1600815 = 2401223) B2401223
theorem B1600959 : Blo 1598998 1600959 := bstep (se 1 (by rfl) ⟨1200719, by rfl⟩ : syracuseStep 1600959 = 2401439) B2401439
theorem B13668203 : Blo 1598998 13668203 := bstep (se 1 (by rfl) ⟨10251152, by rfl⟩ : syracuseStep 13668203 = 20502305) B20502305
theorem B103763855 : Blo 1598998 103763855 := bstep (se 1 (by rfl) ⟨77822891, by rfl⟩ : syracuseStep 103763855 = 155645783) B155645783
theorem B6074423 : Blo 1598998 6074423 := bstep (se 1 (by rfl) ⟨4555817, by rfl⟩ : syracuseStep 6074423 = 9111635) B9111635
theorem B3289295 : Blo 1598998 3289295 := bstep (se 1 (by rfl) ⟨2466971, by rfl⟩ : syracuseStep 3289295 = 4933943) B4933943
theorem B28103155 : Blo 1598998 28103155 := bstep (se 1 (by rfl) ⟨21077366, by rfl⟩ : syracuseStep 28103155 = 42154733) B42154733
theorem B2699831 : Blo 1598998 2699831 := bstep (se 1 (by rfl) ⟨2024873, by rfl⟩ : syracuseStep 2699831 = 4049747) B4049747
theorem B12153401 : Blo 1598998 12153401 := bstep (se 2 (by rfl) ⟨4557525, by rfl⟩ : syracuseStep 12153401 = 9115051) B9115051
theorem B1798951 : Blo 1598998 1798951 := bstep (se 1 (by rfl) ⟨1349213, by rfl⟩ : syracuseStep 1798951 = 2698427) B2698427
theorem B3035951 : Blo 1598998 3035951 := bstep (se 1 (by rfl) ⟨2276963, by rfl⟩ : syracuseStep 3035951 = 4553927) B4553927
theorem B5124961 : Blo 1598998 5124961 := bstep (se 2 (by rfl) ⟨1921860, by rfl⟩ : syracuseStep 5124961 = 3843721) B3843721
theorem B8647553 : Blo 1598998 8647553 := bstep (se 2 (by rfl) ⟨3242832, by rfl⟩ : syracuseStep 8647553 = 6485665) B6485665
theorem B13661095 : Blo 1598998 13661095 := bstep (se 1 (by rfl) ⟨10245821, by rfl⟩ : syracuseStep 13661095 = 20491643) B20491643
theorem B23065559 : Blo 1598998 23065559 := bstep (se 1 (by rfl) ⟨17299169, by rfl⟩ : syracuseStep 23065559 = 34598339) B34598339
theorem B70153231 : Blo 1598998 70153231 := bstep (se 1 (by rfl) ⟨52614923, by rfl⟩ : syracuseStep 70153231 = 105229847) B105229847
theorem B6076079 : Blo 1598998 6076079 := bstep (se 1 (by rfl) ⟨4557059, by rfl⟩ : syracuseStep 6076079 = 9114119) B9114119
theorem B3037151 : Blo 1598998 3037151 := bstep (se 1 (by rfl) ⟨2277863, by rfl⟩ : syracuseStep 3037151 = 4555727) B4555727
theorem B21903455 : Blo 1598998 21903455 := bstep (se 1 (by rfl) ⟨16427591, by rfl⟩ : syracuseStep 21903455 = 32855183) B32855183
theorem B13506725 : Blo 1598998 13506725 := bstep (se 4 (by rfl) ⟨1266255, by rfl⟩ : syracuseStep 13506725 = 2532511) B2532511
theorem B155695607 : Blo 1598998 155695607 := bstep (se 1 (by rfl) ⟨116771705, by rfl⟩ : syracuseStep 155695607 = 233543411) B233543411
theorem B8649503 : Blo 1598998 8649503 := bstep (se 1 (by rfl) ⟨6487127, by rfl⟩ : syracuseStep 8649503 = 12974255) B12974255
theorem B2882633 : Blo 1598998 2882633 := bstep (se 2 (by rfl) ⟨1080987, by rfl⟩ : syracuseStep 2882633 = 2161975) B2161975
theorem B6077537 : Blo 1598998 6077537 := bstep (se 2 (by rfl) ⟨2279076, by rfl⟩ : syracuseStep 6077537 = 4558153) B4558153
theorem B2399339 : Blo 1598998 2399339 := bstep (se 1 (by rfl) ⟨1799504, by rfl⟩ : syracuseStep 2399339 = 3599009) B3599009
theorem B10681469 : Blo 1598998 10681469 := bstep (se 3 (by rfl) ⟨2002775, by rfl⟩ : syracuseStep 10681469 = 4005551) B4005551
theorem B5397785 : Blo 1598998 5397785 := bstep (se 2 (by rfl) ⟨2024169, by rfl⟩ : syracuseStep 5397785 = 4048339) B4048339
theorem B5397839 : Blo 1598998 5397839 := bstep (se 1 (by rfl) ⟨4048379, by rfl⟩ : syracuseStep 5397839 = 8096759) B8096759
theorem B2399579 : Blo 1598998 2399579 := bstep (se 1 (by rfl) ⟨1799684, by rfl⟩ : syracuseStep 2399579 = 3599369) B3599369
theorem B2399711 : Blo 1598998 2399711 := bstep (se 1 (by rfl) ⟨1799783, by rfl⟩ : syracuseStep 2399711 = 3599567) B3599567
theorem B21888575 : Blo 1598998 21888575 := bstep (se 1 (by rfl) ⟨16416431, by rfl⟩ : syracuseStep 21888575 = 32832863) B32832863
theorem B6078023 : Blo 1598998 6078023 := bstep (se 1 (by rfl) ⟨4558517, by rfl⟩ : syracuseStep 6078023 = 9117035) B9117035
theorem B9731663 : Blo 1598998 9731663 := bstep (se 1 (by rfl) ⟨7298747, by rfl⟩ : syracuseStep 9731663 = 14597495) B14597495
theorem B3038951 : Blo 1598998 3038951 := bstep (se 1 (by rfl) ⟨2279213, by rfl⟩ : syracuseStep 3038951 = 4558427) B4558427
theorem B2400239 : Blo 1598998 2400239 := bstep (se 1 (by rfl) ⟨1800179, by rfl⟩ : syracuseStep 2400239 = 3600359) B3600359
theorem B8102267 : Blo 1598998 8102267 := bstep (se 1 (by rfl) ⟨6076700, by rfl⟩ : syracuseStep 8102267 = 12153401) B12153401
theorem B6832667 : Blo 1598998 6832667 := bstep (se 1 (by rfl) ⟨5124500, by rfl⟩ : syracuseStep 6832667 = 10249001) B10249001
theorem B2023967 : Blo 1598998 2023967 := bstep (se 1 (by rfl) ⟨1517975, by rfl⟩ : syracuseStep 2023967 = 3035951) B3035951
theorem B15377039 : Blo 1598998 15377039 := bstep (se 1 (by rfl) ⟨11532779, by rfl⟩ : syracuseStep 15377039 = 23065559) B23065559
theorem B116835371 : Blo 1598998 116835371 := bstep (se 1 (by rfl) ⟨87626528, by rfl⟩ : syracuseStep 116835371 = 175253057) B175253057
theorem B6833267 : Blo 1598998 6833267 := bstep (se 1 (by rfl) ⟨5124950, by rfl⟩ : syracuseStep 6833267 = 10249901) B10249901
theorem B2024767 : Blo 1598998 2024767 := bstep (se 1 (by rfl) ⟨1518575, by rfl⟩ : syracuseStep 2024767 = 3037151) B3037151
theorem B93537641 : Blo 1598998 93537641 := bstep (se 2 (by rfl) ⟨35076615, by rfl⟩ : syracuseStep 93537641 = 70153231) B70153231
theorem B9004483 : Blo 1598998 9004483 := bstep (se 1 (by rfl) ⟨6753362, by rfl⟩ : syracuseStep 9004483 = 13506725) B13506725
theorem B1599559 : Blo 1598998 1599559 := bstep (se 1 (by rfl) ⟨1199669, by rfl⟩ : syracuseStep 1599559 = 2399339) B2399339
theorem B7120979 : Blo 1598998 7120979 := bstep (se 1 (by rfl) ⟨5340734, by rfl⟩ : syracuseStep 7120979 = 10681469) B10681469
theorem B20498615 : Blo 1598998 20498615 := bstep (se 1 (by rfl) ⟨15373961, by rfl⟩ : syracuseStep 20498615 = 30747923) B30747923
theorem B3598523 : Blo 1598998 3598523 := bstep (se 1 (by rfl) ⟨2698892, by rfl⟩ : syracuseStep 3598523 = 5397785) B5397785
theorem B3598559 : Blo 1598998 3598559 := bstep (se 1 (by rfl) ⟨2698919, by rfl⟩ : syracuseStep 3598559 = 5397839) B5397839
theorem B1599719 : Blo 1598998 1599719 := bstep (se 1 (by rfl) ⟨1199789, by rfl⟩ : syracuseStep 1599719 = 2399579) B2399579
theorem B1599807 : Blo 1598998 1599807 := bstep (se 1 (by rfl) ⟨1199855, by rfl⟩ : syracuseStep 1599807 = 2399711) B2399711
theorem B14592383 : Blo 1598998 14592383 := bstep (se 1 (by rfl) ⟨10944287, by rfl⟩ : syracuseStep 14592383 = 21888575) B21888575
theorem B2025967 : Blo 1598998 2025967 := bstep (se 1 (by rfl) ⟨1519475, by rfl⟩ : syracuseStep 2025967 = 3038951) B3038951
theorem B9112135 : Blo 1598998 9112135 := bstep (se 1 (by rfl) ⟨6834101, by rfl⟩ : syracuseStep 9112135 = 13668203) B13668203
theorem B69175903 : Blo 1598998 69175903 := bstep (se 1 (by rfl) ⟨51881927, by rfl⟩ : syracuseStep 69175903 = 103763855) B103763855
theorem B149883493 : Blo 1598998 149883493 := bstep (se 4 (by rfl) ⟨14051577, by rfl⟩ : syracuseStep 149883493 = 28103155) B28103155
theorem B1600159 : Blo 1598998 1600159 := bstep (se 1 (by rfl) ⟨1200119, by rfl⟩ : syracuseStep 1600159 = 2400239) B2400239
theorem B4049615 : Blo 1598998 4049615 := bstep (se 1 (by rfl) ⟨3037211, by rfl⟩ : syracuseStep 4049615 = 6074423) B6074423
theorem B1600239 : Blo 1598998 1600239 := bstep (se 1 (by rfl) ⟨1200179, by rfl⟩ : syracuseStep 1600239 = 2400359) B2400359
theorem B5770025 : Blo 1598998 5770025 := bstep (se 2 (by rfl) ⟨2163759, by rfl⟩ : syracuseStep 5770025 = 4327519) B4327519
theorem B1600319 : Blo 1598998 1600319 := bstep (se 1 (by rfl) ⟨1200239, by rfl⟩ : syracuseStep 1600319 = 2400479) B2400479
theorem B1600327 : Blo 1598998 1600327 := bstep (se 1 (by rfl) ⟨1200245, by rfl⟩ : syracuseStep 1600327 = 2400491) B2400491
theorem B1600359 : Blo 1598998 1600359 := bstep (se 1 (by rfl) ⟨1200269, by rfl⟩ : syracuseStep 1600359 = 2400539) B2400539
theorem B7687021 : Blo 1598998 7687021 := bstep (se 3 (by rfl) ⟨1441316, by rfl⟩ : syracuseStep 7687021 = 2882633) B2882633
theorem B1600367 : Blo 1598998 1600367 := bstep (se 1 (by rfl) ⟨1200275, by rfl⟩ : syracuseStep 1600367 = 2400551) B2400551
theorem B1600495 : Blo 1598998 1600495 := bstep (se 1 (by rfl) ⟨1200371, by rfl⟩ : syracuseStep 1600495 = 2400743) B2400743
theorem B32828419 : Blo 1598998 32828419 := bstep (se 1 (by rfl) ⟨24621314, by rfl⟩ : syracuseStep 32828419 = 49242629) B49242629
theorem B1600615 : Blo 1598998 1600615 := bstep (se 1 (by rfl) ⟨1200461, by rfl⟩ : syracuseStep 1600615 = 2400923) B2400923
theorem B2698447 : Blo 1598998 2698447 := bstep (se 1 (by rfl) ⟨2023835, by rfl⟩ : syracuseStep 2698447 = 4047671) B4047671
theorem B1600927 : Blo 1598998 1600927 := bstep (se 1 (by rfl) ⟨1200695, by rfl⟩ : syracuseStep 1600927 = 2401391) B2401391
theorem B10948225 : Blo 1598998 10948225 := bstep (se 2 (by rfl) ⟨4105584, by rfl⟩ : syracuseStep 10948225 = 8211169) B8211169
theorem B4050719 : Blo 1598998 4050719 := bstep (se 1 (by rfl) ⟨3038039, by rfl⟩ : syracuseStep 4050719 = 6076079) B6076079
theorem B18214793 : Blo 1598998 18214793 := bstep (se 2 (by rfl) ⟨6830547, by rfl⟩ : syracuseStep 18214793 = 13661095) B13661095
theorem B2699291 : Blo 1598998 2699291 := bstep (se 1 (by rfl) ⟨2024468, by rfl⟩ : syracuseStep 2699291 = 4048937) B4048937
theorem B14602303 : Blo 1598998 14602303 := bstep (se 1 (by rfl) ⟨10951727, by rfl⟩ : syracuseStep 14602303 = 21903455) B21903455
theorem B3600575 : Blo 1598998 3600575 := bstep (se 1 (by rfl) ⟨2700431, by rfl⟩ : syracuseStep 3600575 = 5400863) B5400863
theorem B103797071 : Blo 1598998 103797071 := bstep (se 1 (by rfl) ⟨77847803, by rfl⟩ : syracuseStep 103797071 = 155695607) B155695607
theorem B3600863 : Blo 1598998 3600863 := bstep (se 1 (by rfl) ⟨2700647, by rfl⟩ : syracuseStep 3600863 = 5401295) B5401295
theorem B27333125 : Blo 1598998 27333125 := bstep (se 4 (by rfl) ⟨2562480, by rfl⟩ : syracuseStep 27333125 = 5124961) B5124961
theorem B4051691 : Blo 1598998 4051691 := bstep (se 1 (by rfl) ⟨3038768, by rfl⟩ : syracuseStep 4051691 = 6077537) B6077537
theorem B3601223 : Blo 1598998 3601223 := bstep (se 1 (by rfl) ⟨2700917, by rfl⟩ : syracuseStep 3601223 = 5401835) B5401835
theorem B124629839 : Blo 1598998 124629839 := bstep (se 1 (by rfl) ⟨93472379, by rfl⟩ : syracuseStep 124629839 = 186944759) B186944759
theorem B4052015 : Blo 1598998 4052015 := bstep (se 1 (by rfl) ⟨3039011, by rfl⟩ : syracuseStep 4052015 = 6078023) B6078023
theorem B4617629 : Blo 1598998 4617629 := bstep (se 3 (by rfl) ⟨865805, by rfl⟩ : syracuseStep 4617629 = 1731611) B1731611
theorem B6075881 : Blo 1598998 6075881 := bstep (se 2 (by rfl) ⟨2278455, by rfl⟩ : syracuseStep 6075881 = 4556911) B4556911
theorem B1799887 : Blo 1598998 1799887 := bstep (se 1 (by rfl) ⟨1349915, by rfl⟩ : syracuseStep 1799887 = 2699831) B2699831
theorem B8771453 : Blo 1598998 8771453 := bstep (se 3 (by rfl) ⟨1644647, by rfl⟩ : syracuseStep 8771453 = 3289295) B3289295
theorem B5765035 : Blo 1598998 5765035 := bstep (se 1 (by rfl) ⟨4323776, by rfl⟩ : syracuseStep 5765035 = 8647553) B8647553
theorem B2398601 : Blo 1598998 2398601 := bstep (se 2 (by rfl) ⟨899475, by rfl⟩ : syracuseStep 2398601 = 1798951) B1798951
theorem B12147083 : Blo 1598998 12147083 := bstep (se 1 (by rfl) ⟨9110312, by rfl⟩ : syracuseStep 12147083 = 18220625) B18220625
theorem B34610095 : Blo 1598998 34610095 := bstep (se 1 (by rfl) ⟨25957571, by rfl⟩ : syracuseStep 34610095 = 51915143) B51915143
theorem B2563039 : Blo 1598998 2563039 := bstep (se 1 (by rfl) ⟨1922279, by rfl⟩ : syracuseStep 2563039 = 3844559) B3844559
theorem B8100971 : Blo 1598998 8100971 := bstep (se 1 (by rfl) ⟨6075728, by rfl⟩ : syracuseStep 8100971 = 12151457) B12151457
theorem B5766335 : Blo 1598998 5766335 := bstep (se 1 (by rfl) ⟨4324751, by rfl⟩ : syracuseStep 5766335 = 8649503) B8649503
theorem B2399543 : Blo 1598998 2399543 := bstep (se 1 (by rfl) ⟨1799657, by rfl⟩ : syracuseStep 2399543 = 3599315) B3599315
theorem B32857483 : Blo 1598998 32857483 := bstep (se 1 (by rfl) ⟨24643112, by rfl⟩ : syracuseStep 32857483 = 49286225) B49286225
theorem B34577927 : Blo 1598998 34577927 := bstep (se 1 (by rfl) ⟨25933445, by rfl⟩ : syracuseStep 34577927 = 51866891) B51866891
theorem B6487775 : Blo 1598998 6487775 := bstep (se 1 (by rfl) ⟨4865831, by rfl⟩ : syracuseStep 6487775 = 9731663) B9731663
theorem B2400383 : Blo 1598998 2400383 := bstep (se 1 (by rfl) ⟨1800287, by rfl⟩ : syracuseStep 2400383 = 3600575) B3600575
theorem B69198047 : Blo 1598998 69198047 := bstep (se 1 (by rfl) ⟨51898535, by rfl⟩ : syracuseStep 69198047 = 103797071) B103797071
theorem B2400575 : Blo 1598998 2400575 := bstep (se 1 (by rfl) ⟨1800431, by rfl⟩ : syracuseStep 2400575 = 3600863) B3600863
theorem B4555111 : Blo 1598998 4555111 := bstep (se 1 (by rfl) ⟨3416333, by rfl⟩ : syracuseStep 4555111 = 6832667) B6832667
theorem B2400815 : Blo 1598998 2400815 := bstep (se 1 (by rfl) ⟨1800611, by rfl⟩ : syracuseStep 2400815 = 3601223) B3601223
theorem B77890247 : Blo 1598998 77890247 := bstep (se 1 (by rfl) ⟨58417685, by rfl⟩ : syracuseStep 77890247 = 116835371) B116835371
theorem B4555511 : Blo 1598998 4555511 := bstep (se 1 (by rfl) ⟨3416633, by rfl⟩ : syracuseStep 4555511 = 6833267) B6833267
theorem B12149513 : Blo 1598998 12149513 := bstep (se 2 (by rfl) ⟨4556067, by rfl⟩ : syracuseStep 12149513 = 9112135) B9112135
theorem B92234537 : Blo 1598998 92234537 := bstep (se 2 (by rfl) ⟨34587951, by rfl⟩ : syracuseStep 92234537 = 69175903) B69175903
theorem B199844657 : Blo 1598998 199844657 := bstep (se 2 (by rfl) ⟨74941746, by rfl⟩ : syracuseStep 199844657 = 149883493) B149883493
theorem B62358427 : Blo 1598998 62358427 := bstep (se 1 (by rfl) ⟨46768820, by rfl⟩ : syracuseStep 62358427 = 93537641) B93537641
theorem B10249361 : Blo 1598998 10249361 := bstep (se 2 (by rfl) ⟨3843510, by rfl⟩ : syracuseStep 10249361 = 7687021) B7687021
theorem B46146793 : Blo 1598998 46146793 := bstep (se 2 (by rfl) ⟨17305047, by rfl⟩ : syracuseStep 46146793 = 34610095) B34610095
theorem B3417385 : Blo 1598998 3417385 := bstep (se 2 (by rfl) ⟨1281519, by rfl⟩ : syracuseStep 3417385 = 2563039) B2563039
theorem B13665743 : Blo 1598998 13665743 := bstep (se 1 (by rfl) ⟨10249307, by rfl⟩ : syracuseStep 13665743 = 20498615) B20498615
theorem B1599067 : Blo 1598998 1599067 := bstep (se 1 (by rfl) ⟨1199300, by rfl⟩ : syracuseStep 1599067 = 2398601) B2398601
theorem B3597929 : Blo 1598998 3597929 := bstep (se 2 (by rfl) ⟨1349223, by rfl⟩ : syracuseStep 3597929 = 2698447) B2698447
theorem B5400647 : Blo 1598998 5400647 := bstep (se 1 (by rfl) ⟨4050485, by rfl⟩ : syracuseStep 5400647 = 8100971) B8100971
theorem B3844223 : Blo 1598998 3844223 := bstep (se 1 (by rfl) ⟨2883167, by rfl⟩ : syracuseStep 3844223 = 5766335) B5766335
theorem B1599695 : Blo 1598998 1599695 := bstep (se 1 (by rfl) ⟨1199771, by rfl⟩ : syracuseStep 1599695 = 2399543) B2399543
theorem B7686713 : Blo 1598998 7686713 := bstep (se 2 (by rfl) ⟨2882517, by rfl⟩ : syracuseStep 7686713 = 5765035) B5765035
theorem B12143195 : Blo 1598998 12143195 := bstep (se 1 (by rfl) ⟨9107396, by rfl⟩ : syracuseStep 12143195 = 18214793) B18214793
theorem B5401511 : Blo 1598998 5401511 := bstep (se 1 (by rfl) ⟨4051133, by rfl⟩ : syracuseStep 5401511 = 8102267) B8102267
theorem B18222083 : Blo 1598998 18222083 := bstep (se 1 (by rfl) ⟨13666562, by rfl⟩ : syracuseStep 18222083 = 27333125) B27333125
theorem B10251359 : Blo 1598998 10251359 := bstep (se 1 (by rfl) ⟨7688519, by rfl⟩ : syracuseStep 10251359 = 15377039) B15377039
theorem B83086559 : Blo 1598998 83086559 := bstep (se 1 (by rfl) ⟨62314919, by rfl⟩ : syracuseStep 83086559 = 124629839) B124629839
theorem B4050587 : Blo 1598998 4050587 := bstep (se 1 (by rfl) ⟨3037940, by rfl⟩ : syracuseStep 4050587 = 6075881) B6075881
theorem B4747319 : Blo 1598998 4747319 := bstep (se 1 (by rfl) ⟨3560489, by rfl⟩ : syracuseStep 4747319 = 7120979) B7120979
theorem B9728255 : Blo 1598998 9728255 := bstep (se 1 (by rfl) ⟨7296191, by rfl⟩ : syracuseStep 9728255 = 14592383) B14592383
theorem B8098055 : Blo 1598998 8098055 := bstep (se 1 (by rfl) ⟨6073541, by rfl⟩ : syracuseStep 8098055 = 12147083) B12147083
theorem B2699689 : Blo 1598998 2699689 := bstep (se 2 (by rfl) ⟨1012383, by rfl⟩ : syracuseStep 2699689 = 2024767) B2024767
theorem B2699743 : Blo 1598998 2699743 := bstep (se 1 (by rfl) ⟨2024807, by rfl⟩ : syracuseStep 2699743 = 4049615) B4049615
theorem B3846683 : Blo 1598998 3846683 := bstep (se 1 (by rfl) ⟨2885012, by rfl⟩ : syracuseStep 3846683 = 5770025) B5770025
theorem B12005977 : Blo 1598998 12005977 := bstep (se 2 (by rfl) ⟨4502241, by rfl⟩ : syracuseStep 12005977 = 9004483) B9004483
theorem B2700479 : Blo 1598998 2700479 := bstep (se 1 (by rfl) ⟨2025359, by rfl⟩ : syracuseStep 2700479 = 4050719) B4050719
theorem B175084901 : Blo 1598998 175084901 := bstep (se 4 (by rfl) ⟨16414209, by rfl⟩ : syracuseStep 175084901 = 32828419) B32828419
theorem B1799527 : Blo 1598998 1799527 := bstep (se 1 (by rfl) ⟨1349645, by rfl⟩ : syracuseStep 1799527 = 2699291) B2699291
theorem B19469737 : Blo 1598998 19469737 := bstep (se 2 (by rfl) ⟨7301151, by rfl⟩ : syracuseStep 19469737 = 14602303) B14602303
theorem B2701127 : Blo 1598998 2701127 := bstep (se 1 (by rfl) ⟨2025845, by rfl⟩ : syracuseStep 2701127 = 4051691) B4051691
theorem B2701289 : Blo 1598998 2701289 := bstep (se 2 (by rfl) ⟨1012983, by rfl⟩ : syracuseStep 2701289 = 2025967) B2025967
theorem B2701343 : Blo 1598998 2701343 := bstep (se 1 (by rfl) ⟨2026007, by rfl⟩ : syracuseStep 2701343 = 4052015) B4052015
theorem B3078419 : Blo 1598998 3078419 := bstep (se 1 (by rfl) ⟨2308814, by rfl⟩ : syracuseStep 3078419 = 4617629) B4617629
theorem B5847635 : Blo 1598998 5847635 := bstep (se 1 (by rfl) ⟨4385726, by rfl⟩ : syracuseStep 5847635 = 8771453) B8771453
theorem B5397245 : Blo 1598998 5397245 := bstep (se 3 (by rfl) ⟨1011983, by rfl⟩ : syracuseStep 5397245 = 2023967) B2023967
theorem B2399015 : Blo 1598998 2399015 := bstep (se 1 (by rfl) ⟨1799261, by rfl⟩ : syracuseStep 2399015 = 3598523) B3598523
theorem B2399039 : Blo 1598998 2399039 := bstep (se 1 (by rfl) ⟨1799279, by rfl⟩ : syracuseStep 2399039 = 3598559) B3598559
theorem B43809977 : Blo 1598998 43809977 := bstep (se 2 (by rfl) ⟨16428741, by rfl⟩ : syracuseStep 43809977 = 32857483) B32857483
theorem B14597633 : Blo 1598998 14597633 := bstep (se 2 (by rfl) ⟨5474112, by rfl⟩ : syracuseStep 14597633 = 10948225) B10948225
theorem B2399849 : Blo 1598998 2399849 := bstep (se 2 (by rfl) ⟨899943, by rfl⟩ : syracuseStep 2399849 = 1799887) B1799887
theorem B23051951 : Blo 1598998 23051951 := bstep (se 1 (by rfl) ⟨17288963, by rfl⟩ : syracuseStep 23051951 = 34577927) B34577927
theorem B4325183 : Blo 1598998 4325183 := bstep (se 1 (by rfl) ⟨3243887, by rfl⟩ : syracuseStep 4325183 = 6487775) B6487775
theorem B5398703 : Blo 1598998 5398703 := bstep (se 1 (by rfl) ⟨4049027, by rfl⟩ : syracuseStep 5398703 = 8098055) B8098055
theorem B2564455 : Blo 1598998 2564455 := bstep (se 1 (by rfl) ⟨1923341, by rfl⟩ : syracuseStep 2564455 = 3846683) B3846683
theorem B61489691 : Blo 1598998 61489691 := bstep (se 1 (by rfl) ⟨46117268, by rfl⟩ : syracuseStep 61489691 = 92234537) B92234537
theorem B8209117 : Blo 1598998 8209117 := bstep (se 3 (by rfl) ⟨1539209, by rfl⟩ : syracuseStep 8209117 = 3078419) B3078419
theorem B6832907 : Blo 1598998 6832907 := bstep (se 1 (by rfl) ⟨5124680, by rfl⟩ : syracuseStep 6832907 = 10249361) B10249361
theorem B16007969 : Blo 1598998 16007969 := bstep (se 2 (by rfl) ⟨6002988, by rfl⟩ : syracuseStep 16007969 = 12005977) B12005977
theorem B9110495 : Blo 1598998 9110495 := bstep (se 1 (by rfl) ⟨6832871, by rfl⟩ : syracuseStep 9110495 = 13665743) B13665743
theorem B4556513 : Blo 1598998 4556513 := bstep (se 2 (by rfl) ⟨1708692, by rfl⟩ : syracuseStep 4556513 = 3417385) B3417385
theorem B8095463 : Blo 1598998 8095463 := bstep (se 1 (by rfl) ⟨6071597, by rfl⟩ : syracuseStep 8095463 = 12143195) B12143195
theorem B3598163 : Blo 1598998 3598163 := bstep (se 1 (by rfl) ⟨2698622, by rfl⟩ : syracuseStep 3598163 = 5397245) B5397245
theorem B1599343 : Blo 1598998 1599343 := bstep (se 1 (by rfl) ⟨1199507, by rfl⟩ : syracuseStep 1599343 = 2399015) B2399015
theorem B1599359 : Blo 1598998 1599359 := bstep (se 1 (by rfl) ⟨1199519, by rfl⟩ : syracuseStep 1599359 = 2399039) B2399039
theorem B6834239 : Blo 1598998 6834239 := bstep (se 1 (by rfl) ⟨5125679, by rfl⟩ : syracuseStep 6834239 = 10251359) B10251359
theorem B29206651 : Blo 1598998 29206651 := bstep (se 1 (by rfl) ⟨21904988, by rfl⟩ : syracuseStep 29206651 = 43809977) B43809977
theorem B1599899 : Blo 1598998 1599899 := bstep (se 1 (by rfl) ⟨1199924, by rfl⟩ : syracuseStep 1599899 = 2399849) B2399849
theorem B3164879 : Blo 1598998 3164879 := bstep (se 1 (by rfl) ⟨2373659, by rfl⟩ : syracuseStep 3164879 = 4747319) B4747319
theorem B1600255 : Blo 1598998 1600255 := bstep (se 1 (by rfl) ⟨1200191, by rfl⟩ : syracuseStep 1600255 = 2400383) B2400383
theorem B46132031 : Blo 1598998 46132031 := bstep (se 1 (by rfl) ⟨34599023, by rfl⟩ : syracuseStep 46132031 = 69198047) B69198047
theorem B1600383 : Blo 1598998 1600383 := bstep (se 1 (by rfl) ⟨1200287, by rfl⟩ : syracuseStep 1600383 = 2400575) B2400575
theorem B1600543 : Blo 1598998 1600543 := bstep (se 1 (by rfl) ⟨1200407, by rfl⟩ : syracuseStep 1600543 = 2400815) B2400815
theorem B6073481 : Blo 1598998 6073481 := bstep (se 2 (by rfl) ⟨2277555, by rfl⟩ : syracuseStep 6073481 = 4555111) B4555111
theorem B133229771 : Blo 1598998 133229771 := bstep (se 1 (by rfl) ⟨99922328, by rfl⟩ : syracuseStep 133229771 = 199844657) B199844657
theorem B3599585 : Blo 1598998 3599585 := bstep (se 2 (by rfl) ⟨1349844, by rfl⟩ : syracuseStep 3599585 = 2699689) B2699689
theorem B3599657 : Blo 1598998 3599657 := bstep (se 2 (by rfl) ⟨1349871, by rfl⟩ : syracuseStep 3599657 = 2699743) B2699743
theorem B116723267 : Blo 1598998 116723267 := bstep (se 1 (by rfl) ⟨87542450, by rfl⟩ : syracuseStep 116723267 = 175084901) B175084901
theorem B83144569 : Blo 1598998 83144569 := bstep (se 2 (by rfl) ⟨31179213, by rfl⟩ : syracuseStep 83144569 = 62358427) B62358427
theorem B3600431 : Blo 1598998 3600431 := bstep (se 1 (by rfl) ⟨2700323, by rfl⟩ : syracuseStep 3600431 = 5400647) B5400647
theorem B5124475 : Blo 1598998 5124475 := bstep (se 1 (by rfl) ⟨3843356, by rfl⟩ : syracuseStep 5124475 = 7686713) B7686713
theorem B3601007 : Blo 1598998 3601007 := bstep (se 1 (by rfl) ⟨2700755, by rfl⟩ : syracuseStep 3601007 = 5401511) B5401511
theorem B55391039 : Blo 1598998 55391039 := bstep (se 1 (by rfl) ⟨41543279, by rfl⟩ : syracuseStep 55391039 = 83086559) B83086559
theorem B2700391 : Blo 1598998 2700391 := bstep (se 1 (by rfl) ⟨2025293, by rfl⟩ : syracuseStep 2700391 = 4050587) B4050587
theorem B6485503 : Blo 1598998 6485503 := bstep (se 1 (by rfl) ⟨4864127, by rfl⟩ : syracuseStep 6485503 = 9728255) B9728255
theorem B51926831 : Blo 1598998 51926831 := bstep (se 1 (by rfl) ⟨38945123, by rfl⟩ : syracuseStep 51926831 = 77890247) B77890247
theorem B3037007 : Blo 1598998 3037007 := bstep (se 1 (by rfl) ⟨2277755, by rfl⟩ : syracuseStep 3037007 = 4555511) B4555511
theorem B8099675 : Blo 1598998 8099675 := bstep (se 1 (by rfl) ⟨6074756, by rfl⟩ : syracuseStep 8099675 = 12149513) B12149513
theorem B1800319 : Blo 1598998 1800319 := bstep (se 1 (by rfl) ⟨1350239, by rfl⟩ : syracuseStep 1800319 = 2700479) B2700479
theorem B2398619 : Blo 1598998 2398619 := bstep (se 1 (by rfl) ⟨1798964, by rfl⟩ : syracuseStep 2398619 = 3597929) B3597929
theorem B1800751 : Blo 1598998 1800751 := bstep (se 1 (by rfl) ⟨1350563, by rfl⟩ : syracuseStep 1800751 = 2701127) B2701127
theorem B1800859 : Blo 1598998 1800859 := bstep (se 1 (by rfl) ⟨1350644, by rfl⟩ : syracuseStep 1800859 = 2701289) B2701289
theorem B1800895 : Blo 1598998 1800895 := bstep (se 1 (by rfl) ⟨1350671, by rfl⟩ : syracuseStep 1800895 = 2701343) B2701343
theorem B2562815 : Blo 1598998 2562815 := bstep (se 1 (by rfl) ⟨1922111, by rfl⟩ : syracuseStep 2562815 = 3844223) B3844223
theorem B61529057 : Blo 1598998 61529057 := bstep (se 2 (by rfl) ⟨23073396, by rfl⟩ : syracuseStep 61529057 = 46146793) B46146793
theorem B3898423 : Blo 1598998 3898423 := bstep (se 1 (by rfl) ⟨2923817, by rfl⟩ : syracuseStep 3898423 = 5847635) B5847635
theorem B2399369 : Blo 1598998 2399369 := bstep (se 2 (by rfl) ⟨899763, by rfl⟩ : syracuseStep 2399369 = 1799527) B1799527
theorem B25959649 : Blo 1598998 25959649 := bstep (se 2 (by rfl) ⟨9734868, by rfl⟩ : syracuseStep 25959649 = 19469737) B19469737
theorem B12148055 : Blo 1598998 12148055 := bstep (se 1 (by rfl) ⟨9111041, by rfl⟩ : syracuseStep 12148055 = 18222083) B18222083
theorem B9731755 : Blo 1598998 9731755 := bstep (se 1 (by rfl) ⟨7298816, by rfl⟩ : syracuseStep 9731755 = 14597633) B14597633
theorem B15367967 : Blo 1598998 15367967 := bstep (se 1 (by rfl) ⟨11525975, by rfl⟩ : syracuseStep 15367967 = 23051951) B23051951
theorem B2883455 : Blo 1598998 2883455 := bstep (se 1 (by rfl) ⟨2162591, by rfl⟩ : syracuseStep 2883455 = 4325183) B4325183
theorem B2400287 : Blo 1598998 2400287 := bstep (se 1 (by rfl) ⟨1800215, by rfl⟩ : syracuseStep 2400287 = 3600431) B3600431
theorem B2400425 : Blo 1598998 2400425 := bstep (se 2 (by rfl) ⟨900159, by rfl⟩ : syracuseStep 2400425 = 1800319) B1800319
theorem B40993127 : Blo 1598998 40993127 := bstep (se 1 (by rfl) ⟨30744845, by rfl⟩ : syracuseStep 40993127 = 61489691) B61489691
theorem B2400671 : Blo 1598998 2400671 := bstep (se 1 (by rfl) ⟨1800503, by rfl⟩ : syracuseStep 2400671 = 3601007) B3601007
theorem B6832633 : Blo 1598998 6832633 := bstep (se 2 (by rfl) ⟨2562237, by rfl⟩ : syracuseStep 6832633 = 5124475) B5124475
theorem B4555271 : Blo 1598998 4555271 := bstep (se 1 (by rfl) ⟨3416453, by rfl⟩ : syracuseStep 4555271 = 6832907) B6832907
theorem B2401001 : Blo 1598998 2401001 := bstep (se 2 (by rfl) ⟨900375, by rfl⟩ : syracuseStep 2401001 = 1800751) B1800751
theorem B2401145 : Blo 1598998 2401145 := bstep (se 2 (by rfl) ⟨900429, by rfl⟩ : syracuseStep 2401145 = 1800859) B1800859
theorem B2401193 : Blo 1598998 2401193 := bstep (se 2 (by rfl) ⟨900447, by rfl⟩ : syracuseStep 2401193 = 1800895) B1800895
theorem B10945489 : Blo 1598998 10945489 := bstep (se 2 (by rfl) ⟨4104558, by rfl⟩ : syracuseStep 10945489 = 8209117) B8209117
theorem B2024671 : Blo 1598998 2024671 := bstep (se 1 (by rfl) ⟨1518503, by rfl⟩ : syracuseStep 2024671 = 3037007) B3037007
theorem B5399783 : Blo 1598998 5399783 := bstep (se 1 (by rfl) ⟨4049837, by rfl⟩ : syracuseStep 5399783 = 8099675) B8099675
theorem B4556159 : Blo 1598998 4556159 := bstep (se 1 (by rfl) ⟨3417119, by rfl⟩ : syracuseStep 4556159 = 6834239) B6834239
theorem B1599079 : Blo 1598998 1599079 := bstep (se 1 (by rfl) ⟨1199309, by rfl⟩ : syracuseStep 1599079 = 2398619) B2398619
theorem B34612865 : Blo 1598998 34612865 := bstep (se 2 (by rfl) ⟨12979824, by rfl⟩ : syracuseStep 34612865 = 25959649) B25959649
theorem B8439677 : Blo 1598998 8439677 := bstep (se 3 (by rfl) ⟨1582439, by rfl⟩ : syracuseStep 8439677 = 3164879) B3164879
theorem B30754687 : Blo 1598998 30754687 := bstep (se 1 (by rfl) ⟨23066015, by rfl⟩ : syracuseStep 30754687 = 46132031) B46132031
theorem B41019371 : Blo 1598998 41019371 := bstep (se 1 (by rfl) ⟨30764528, by rfl⟩ : syracuseStep 41019371 = 61529057) B61529057
theorem B1599579 : Blo 1598998 1599579 := bstep (se 1 (by rfl) ⟨1199684, by rfl⟩ : syracuseStep 1599579 = 2399369) B2399369
theorem B4048987 : Blo 1598998 4048987 := bstep (se 1 (by rfl) ⟨3036740, by rfl⟩ : syracuseStep 4048987 = 6073481) B6073481
theorem B88819847 : Blo 1598998 88819847 := bstep (se 1 (by rfl) ⟨66614885, by rfl⟩ : syracuseStep 88819847 = 133229771) B133229771
theorem B3599135 : Blo 1598998 3599135 := bstep (se 1 (by rfl) ⟨2699351, by rfl⟩ : syracuseStep 3599135 = 5398703) B5398703
theorem B3419273 : Blo 1598998 3419273 := bstep (se 2 (by rfl) ⟨1282227, by rfl⟩ : syracuseStep 3419273 = 2564455) B2564455
theorem B6073663 : Blo 1598998 6073663 := bstep (se 1 (by rfl) ⟨4555247, by rfl⟩ : syracuseStep 6073663 = 9110495) B9110495
theorem B5197897 : Blo 1598998 5197897 := bstep (se 2 (by rfl) ⟨1949211, by rfl⟩ : syracuseStep 5197897 = 3898423) B3898423
theorem B3600521 : Blo 1598998 3600521 := bstep (se 2 (by rfl) ⟨1350195, by rfl⟩ : syracuseStep 3600521 = 2700391) B2700391
theorem B1708543 : Blo 1598998 1708543 := bstep (se 1 (by rfl) ⟨1281407, by rfl⟩ : syracuseStep 1708543 = 2562815) B2562815
theorem B8647337 : Blo 1598998 8647337 := bstep (se 2 (by rfl) ⟨3242751, by rfl⟩ : syracuseStep 8647337 = 6485503) B6485503
theorem B8098703 : Blo 1598998 8098703 := bstep (se 1 (by rfl) ⟨6074027, by rfl⟩ : syracuseStep 8098703 = 12148055) B12148055
theorem B110859425 : Blo 1598998 110859425 := bstep (se 2 (by rfl) ⟨41572284, by rfl⟩ : syracuseStep 110859425 = 83144569) B83144569
theorem B10245311 : Blo 1598998 10245311 := bstep (se 1 (by rfl) ⟨7683983, by rfl⟩ : syracuseStep 10245311 = 15367967) B15367967
theorem B1922303 : Blo 1598998 1922303 := bstep (se 1 (by rfl) ⟨1441727, by rfl⟩ : syracuseStep 1922303 = 2883455) B2883455
theorem B38942201 : Blo 1598998 38942201 := bstep (se 2 (by rfl) ⟨14603325, by rfl⟩ : syracuseStep 38942201 = 29206651) B29206651
theorem B36927359 : Blo 1598998 36927359 := bstep (se 1 (by rfl) ⟨27695519, by rfl⟩ : syracuseStep 36927359 = 55391039) B55391039
theorem B3037675 : Blo 1598998 3037675 := bstep (se 1 (by rfl) ⟨2278256, by rfl⟩ : syracuseStep 3037675 = 4556513) B4556513
theorem B5396975 : Blo 1598998 5396975 := bstep (se 1 (by rfl) ⟨4047731, by rfl⟩ : syracuseStep 5396975 = 8095463) B8095463
theorem B34617887 : Blo 1598998 34617887 := bstep (se 1 (by rfl) ⟨25963415, by rfl⟩ : syracuseStep 34617887 = 51926831) B51926831
theorem B2398775 : Blo 1598998 2398775 := bstep (se 1 (by rfl) ⟨1799081, by rfl⟩ : syracuseStep 2398775 = 3598163) B3598163
theorem B42687917 : Blo 1598998 42687917 := bstep (se 3 (by rfl) ⟨8003984, by rfl⟩ : syracuseStep 42687917 = 16007969) B16007969
theorem B2399723 : Blo 1598998 2399723 := bstep (se 1 (by rfl) ⟨1799792, by rfl⟩ : syracuseStep 2399723 = 3599585) B3599585
theorem B2399771 : Blo 1598998 2399771 := bstep (se 1 (by rfl) ⟨1799828, by rfl⟩ : syracuseStep 2399771 = 3599657) B3599657
theorem B12975673 : Blo 1598998 12975673 := bstep (se 2 (by rfl) ⟨4865877, by rfl⟩ : syracuseStep 12975673 = 9731755) B9731755
theorem B77815511 : Blo 1598998 77815511 := bstep (se 1 (by rfl) ⟨58361633, by rfl⟩ : syracuseStep 77815511 = 116723267) B116723267
theorem B2400347 : Blo 1598998 2400347 := bstep (se 1 (by rfl) ⟨1800260, by rfl⟩ : syracuseStep 2400347 = 3600521) B3600521
theorem B6930529 : Blo 1598998 6930529 := bstep (se 2 (by rfl) ⟨2598948, by rfl⟩ : syracuseStep 6930529 = 5197897) B5197897
theorem B5398649 : Blo 1598998 5398649 := bstep (se 2 (by rfl) ⟨2024493, by rfl⟩ : syracuseStep 5398649 = 4048987) B4048987
theorem B27328751 : Blo 1598998 27328751 := bstep (se 1 (by rfl) ⟨20496563, by rfl⟩ : syracuseStep 27328751 = 40993127) B40993127
theorem B5399135 : Blo 1598998 5399135 := bstep (se 1 (by rfl) ⟨4049351, by rfl⟩ : syracuseStep 5399135 = 8098703) B8098703
theorem B9110177 : Blo 1598998 9110177 := bstep (se 2 (by rfl) ⟨3416316, by rfl⟩ : syracuseStep 9110177 = 6832633) B6832633
theorem B2278057 : Blo 1598998 2278057 := bstep (se 2 (by rfl) ⟨854271, by rfl⟩ : syracuseStep 2278057 = 1708543) B1708543
theorem B25961467 : Blo 1598998 25961467 := bstep (se 1 (by rfl) ⟨19471100, by rfl⟩ : syracuseStep 25961467 = 38942201) B38942201
theorem B24618239 : Blo 1598998 24618239 := bstep (se 1 (by rfl) ⟨18463679, by rfl⟩ : syracuseStep 24618239 = 36927359) B36927359
theorem B27346247 : Blo 1598998 27346247 := bstep (se 1 (by rfl) ⟨20509685, by rfl⟩ : syracuseStep 27346247 = 41019371) B41019371
theorem B59213231 : Blo 1598998 59213231 := bstep (se 1 (by rfl) ⟨44409923, by rfl⟩ : syracuseStep 59213231 = 88819847) B88819847
theorem B3597983 : Blo 1598998 3597983 := bstep (se 1 (by rfl) ⟨2698487, by rfl⟩ : syracuseStep 3597983 = 5396975) B5396975
theorem B23078591 : Blo 1598998 23078591 := bstep (se 1 (by rfl) ⟨17308943, by rfl⟩ : syracuseStep 23078591 = 34617887) B34617887
theorem B1599183 : Blo 1598998 1599183 := bstep (se 1 (by rfl) ⟨1199387, by rfl⟩ : syracuseStep 1599183 = 2398775) B2398775
theorem B2279515 : Blo 1598998 2279515 := bstep (se 1 (by rfl) ⟨1709636, by rfl⟩ : syracuseStep 2279515 = 3419273) B3419273
theorem B1599815 : Blo 1598998 1599815 := bstep (se 1 (by rfl) ⟨1199861, by rfl⟩ : syracuseStep 1599815 = 2399723) B2399723
theorem B1599847 : Blo 1598998 1599847 := bstep (se 1 (by rfl) ⟨1199885, by rfl⟩ : syracuseStep 1599847 = 2399771) B2399771
theorem B1600191 : Blo 1598998 1600191 := bstep (se 1 (by rfl) ⟨1200143, by rfl⟩ : syracuseStep 1600191 = 2400287) B2400287
theorem B1600283 : Blo 1598998 1600283 := bstep (se 1 (by rfl) ⟨1200212, by rfl⟩ : syracuseStep 1600283 = 2400425) B2400425
theorem B1600447 : Blo 1598998 1600447 := bstep (se 1 (by rfl) ⟨1200335, by rfl⟩ : syracuseStep 1600447 = 2400671) B2400671
theorem B1600667 : Blo 1598998 1600667 := bstep (se 1 (by rfl) ⟨1200500, by rfl⟩ : syracuseStep 1600667 = 2401001) B2401001
theorem B1600763 : Blo 1598998 1600763 := bstep (se 1 (by rfl) ⟨1200572, by rfl⟩ : syracuseStep 1600763 = 2401145) B2401145
theorem B1600795 : Blo 1598998 1600795 := bstep (se 1 (by rfl) ⟨1200596, by rfl⟩ : syracuseStep 1600795 = 2401193) B2401193
theorem B4050233 : Blo 1598998 4050233 := bstep (se 2 (by rfl) ⟨1518837, by rfl⟩ : syracuseStep 4050233 = 3037675) B3037675
theorem B3599855 : Blo 1598998 3599855 := bstep (se 1 (by rfl) ⟨2699891, by rfl⟩ : syracuseStep 3599855 = 5399783) B5399783
theorem B14593985 : Blo 1598998 14593985 := bstep (se 2 (by rfl) ⟨5472744, by rfl⟩ : syracuseStep 14593985 = 10945489) B10945489
theorem B2699561 : Blo 1598998 2699561 := bstep (se 2 (by rfl) ⟨1012335, by rfl⟩ : syracuseStep 2699561 = 2024671) B2024671
theorem B8098217 : Blo 1598998 8098217 := bstep (se 2 (by rfl) ⟨3036831, by rfl⟩ : syracuseStep 8098217 = 6073663) B6073663
theorem B51877007 : Blo 1598998 51877007 := bstep (se 1 (by rfl) ⟨38907755, by rfl⟩ : syracuseStep 51877007 = 77815511) B77815511
theorem B41006249 : Blo 1598998 41006249 := bstep (se 2 (by rfl) ⟨15377343, by rfl⟩ : syracuseStep 41006249 = 30754687) B30754687
theorem B3036847 : Blo 1598998 3036847 := bstep (se 1 (by rfl) ⟨2277635, by rfl⟩ : syracuseStep 3036847 = 4555271) B4555271
theorem B5764891 : Blo 1598998 5764891 := bstep (se 1 (by rfl) ⟨4323668, by rfl⟩ : syracuseStep 5764891 = 8647337) B8647337
theorem B5126141 : Blo 1598998 5126141 := bstep (se 3 (by rfl) ⟨961151, by rfl⟩ : syracuseStep 5126141 = 1922303) B1922303
theorem B73906283 : Blo 1598998 73906283 := bstep (se 1 (by rfl) ⟨55429712, by rfl⟩ : syracuseStep 73906283 = 110859425) B110859425
theorem B6830207 : Blo 1598998 6830207 := bstep (se 1 (by rfl) ⟨5122655, by rfl⟩ : syracuseStep 6830207 = 10245311) B10245311
theorem B3037439 : Blo 1598998 3037439 := bstep (se 1 (by rfl) ⟨2278079, by rfl⟩ : syracuseStep 3037439 = 4556159) B4556159
theorem B23075243 : Blo 1598998 23075243 := bstep (se 1 (by rfl) ⟨17306432, by rfl⟩ : syracuseStep 23075243 = 34612865) B34612865
theorem B5626451 : Blo 1598998 5626451 := bstep (se 1 (by rfl) ⟨4219838, by rfl⟩ : syracuseStep 5626451 = 8439677) B8439677
theorem B2399423 : Blo 1598998 2399423 := bstep (se 1 (by rfl) ⟨1799567, by rfl⟩ : syracuseStep 2399423 = 3599135) B3599135
theorem B17300897 : Blo 1598998 17300897 := bstep (se 2 (by rfl) ⟨6487836, by rfl⟩ : syracuseStep 17300897 = 12975673) B12975673
theorem B28458611 : Blo 1598998 28458611 := bstep (se 1 (by rfl) ⟨21343958, by rfl⟩ : syracuseStep 28458611 = 42687917) B42687917
theorem B3039353 : Blo 1598998 3039353 := bstep (se 2 (by rfl) ⟨1139757, by rfl⟩ : syracuseStep 3039353 = 2279515) B2279515
theorem B18219167 : Blo 1598998 18219167 := bstep (se 1 (by rfl) ⟨13664375, by rfl⟩ : syracuseStep 18219167 = 27328751) B27328751
theorem B5398811 : Blo 1598998 5398811 := bstep (se 1 (by rfl) ⟨4049108, by rfl⟩ : syracuseStep 5398811 = 8098217) B8098217
theorem B36962821 : Blo 1598998 36962821 := bstep (se 4 (by rfl) ⟨3465264, by rfl⟩ : syracuseStep 36962821 = 6930529) B6930529
theorem B27337499 : Blo 1598998 27337499 := bstep (se 1 (by rfl) ⟨20503124, by rfl⟩ : syracuseStep 27337499 = 41006249) B41006249
theorem B15385727 : Blo 1598998 15385727 := bstep (se 1 (by rfl) ⟨11539295, by rfl⟩ : syracuseStep 15385727 = 23078591) B23078591
theorem B3417427 : Blo 1598998 3417427 := bstep (se 1 (by rfl) ⟨2563070, by rfl⟩ : syracuseStep 3417427 = 5126141) B5126141
theorem B1599615 : Blo 1598998 1599615 := bstep (se 1 (by rfl) ⟨1199711, by rfl⟩ : syracuseStep 1599615 = 2399423) B2399423
theorem B4049129 : Blo 1598998 4049129 := bstep (se 2 (by rfl) ⟨1518423, by rfl⟩ : syracuseStep 4049129 = 3036847) B3036847
theorem B7686521 : Blo 1598998 7686521 := bstep (se 2 (by rfl) ⟨2882445, by rfl⟩ : syracuseStep 7686521 = 5764891) B5764891
theorem B1600231 : Blo 1598998 1600231 := bstep (se 1 (by rfl) ⟨1200173, by rfl⟩ : syracuseStep 1600231 = 2400347) B2400347
theorem B3599099 : Blo 1598998 3599099 := bstep (se 1 (by rfl) ⟨2699324, by rfl⟩ : syracuseStep 3599099 = 5398649) B5398649
theorem B3599423 : Blo 1598998 3599423 := bstep (se 1 (by rfl) ⟨2699567, by rfl⟩ : syracuseStep 3599423 = 5399135) B5399135
theorem B6073451 : Blo 1598998 6073451 := bstep (se 1 (by rfl) ⟨4555088, by rfl⟩ : syracuseStep 6073451 = 9110177) B9110177
theorem B16412159 : Blo 1598998 16412159 := bstep (se 1 (by rfl) ⟨12309119, by rfl⟩ : syracuseStep 16412159 = 24618239) B24618239
theorem B18230831 : Blo 1598998 18230831 := bstep (se 1 (by rfl) ⟨13673123, by rfl⟩ : syracuseStep 18230831 = 27346247) B27346247
theorem B34615289 : Blo 1598998 34615289 := bstep (se 2 (by rfl) ⟨12980733, by rfl⟩ : syracuseStep 34615289 = 25961467) B25961467
theorem B49270855 : Blo 1598998 49270855 := bstep (se 1 (by rfl) ⟨36953141, by rfl⟩ : syracuseStep 49270855 = 73906283) B73906283
theorem B2700155 : Blo 1598998 2700155 := bstep (se 1 (by rfl) ⟨2025116, by rfl⟩ : syracuseStep 2700155 = 4050233) B4050233
theorem B9729323 : Blo 1598998 9729323 := bstep (se 1 (by rfl) ⟨7296992, by rfl⟩ : syracuseStep 9729323 = 14593985) B14593985
theorem B1799707 : Blo 1598998 1799707 := bstep (se 1 (by rfl) ⟨1349780, by rfl⟩ : syracuseStep 1799707 = 2699561) B2699561
theorem B8099837 : Blo 1598998 8099837 := bstep (se 3 (by rfl) ⟨1518719, by rfl⟩ : syracuseStep 8099837 = 3037439) B3037439
theorem B34584671 : Blo 1598998 34584671 := bstep (se 1 (by rfl) ⟨25938503, by rfl⟩ : syracuseStep 34584671 = 51877007) B51877007
theorem B3037409 : Blo 1598998 3037409 := bstep (se 2 (by rfl) ⟨1139028, by rfl⟩ : syracuseStep 3037409 = 2278057) B2278057
theorem B39475487 : Blo 1598998 39475487 := bstep (se 1 (by rfl) ⟨29606615, by rfl⟩ : syracuseStep 39475487 = 59213231) B59213231
theorem B2398655 : Blo 1598998 2398655 := bstep (se 1 (by rfl) ⟨1798991, by rfl⟩ : syracuseStep 2398655 = 3597983) B3597983
theorem B4553471 : Blo 1598998 4553471 := bstep (se 1 (by rfl) ⟨3415103, by rfl⟩ : syracuseStep 4553471 = 6830207) B6830207
theorem B15383495 : Blo 1598998 15383495 := bstep (se 1 (by rfl) ⟨11537621, by rfl⟩ : syracuseStep 15383495 = 23075243) B23075243
theorem B3750967 : Blo 1598998 3750967 := bstep (se 1 (by rfl) ⟨2813225, by rfl⟩ : syracuseStep 3750967 = 5626451) B5626451
theorem B11533931 : Blo 1598998 11533931 := bstep (se 1 (by rfl) ⟨8650448, by rfl⟩ : syracuseStep 11533931 = 17300897) B17300897
theorem B2399903 : Blo 1598998 2399903 := bstep (se 1 (by rfl) ⟨1799927, by rfl⟩ : syracuseStep 2399903 = 3599855) B3599855
theorem B18972407 : Blo 1598998 18972407 := bstep (se 1 (by rfl) ⟨14229305, by rfl⟩ : syracuseStep 18972407 = 28458611) B28458611
theorem B23076859 : Blo 1598998 23076859 := bstep (se 1 (by rfl) ⟨17307644, by rfl⟩ : syracuseStep 23076859 = 34615289) B34615289
theorem B20005157 : Blo 1598998 20005157 := bstep (se 4 (by rfl) ⟨1875483, by rfl⟩ : syracuseStep 20005157 = 3750967) B3750967
theorem B49283761 : Blo 1598998 49283761 := bstep (se 2 (by rfl) ⟨18481410, by rfl⟩ : syracuseStep 49283761 = 36962821) B36962821
theorem B10257151 : Blo 1598998 10257151 := bstep (se 1 (by rfl) ⟨7692863, by rfl⟩ : syracuseStep 10257151 = 15385727) B15385727
theorem B5399891 : Blo 1598998 5399891 := bstep (se 1 (by rfl) ⟨4049918, by rfl⟩ : syracuseStep 5399891 = 8099837) B8099837
theorem B2024939 : Blo 1598998 2024939 := bstep (se 1 (by rfl) ⟨1518704, by rfl⟩ : syracuseStep 2024939 = 3037409) B3037409
theorem B1599103 : Blo 1598998 1599103 := bstep (se 1 (by rfl) ⟨1199327, by rfl⟩ : syracuseStep 1599103 = 2398655) B2398655
theorem B4556569 : Blo 1598998 4556569 := bstep (se 2 (by rfl) ⟨1708713, by rfl⟩ : syracuseStep 4556569 = 3417427) B3417427
theorem B4048967 : Blo 1598998 4048967 := bstep (se 1 (by rfl) ⟨3036725, by rfl⟩ : syracuseStep 4048967 = 6073451) B6073451
theorem B1599935 : Blo 1598998 1599935 := bstep (se 1 (by rfl) ⟨1199951, by rfl⟩ : syracuseStep 1599935 = 2399903) B2399903
theorem B2026235 : Blo 1598998 2026235 := bstep (se 1 (by rfl) ⟨1519676, by rfl⟩ : syracuseStep 2026235 = 3039353) B3039353
theorem B65694473 : Blo 1598998 65694473 := bstep (se 2 (by rfl) ⟨24635427, by rfl⟩ : syracuseStep 65694473 = 49270855) B49270855
theorem B3599207 : Blo 1598998 3599207 := bstep (se 1 (by rfl) ⟨2699405, by rfl⟩ : syracuseStep 3599207 = 5398811) B5398811
theorem B23056447 : Blo 1598998 23056447 := bstep (se 1 (by rfl) ⟨17292335, by rfl⟩ : syracuseStep 23056447 = 34584671) B34584671
theorem B2699419 : Blo 1598998 2699419 := bstep (se 1 (by rfl) ⟨2024564, by rfl⟩ : syracuseStep 2699419 = 4049129) B4049129
theorem B26316991 : Blo 1598998 26316991 := bstep (se 1 (by rfl) ⟨19737743, by rfl⟩ : syracuseStep 26316991 = 39475487) B39475487
theorem B5124347 : Blo 1598998 5124347 := bstep (se 1 (by rfl) ⟨3843260, by rfl⟩ : syracuseStep 5124347 = 7686521) B7686521
theorem B3035647 : Blo 1598998 3035647 := bstep (se 1 (by rfl) ⟨2276735, by rfl⟩ : syracuseStep 3035647 = 4553471) B4553471
theorem B10941439 : Blo 1598998 10941439 := bstep (se 1 (by rfl) ⟨8206079, by rfl⟩ : syracuseStep 10941439 = 16412159) B16412159
theorem B12153887 : Blo 1598998 12153887 := bstep (se 1 (by rfl) ⟨9115415, by rfl⟩ : syracuseStep 12153887 = 18230831) B18230831
theorem B7689287 : Blo 1598998 7689287 := bstep (se 1 (by rfl) ⟨5766965, by rfl⟩ : syracuseStep 7689287 = 11533931) B11533931
theorem B12146111 : Blo 1598998 12146111 := bstep (se 1 (by rfl) ⟨9109583, by rfl⟩ : syracuseStep 12146111 = 18219167) B18219167
theorem B18224999 : Blo 1598998 18224999 := bstep (se 1 (by rfl) ⟨13668749, by rfl⟩ : syracuseStep 18224999 = 27337499) B27337499
theorem B1800103 : Blo 1598998 1800103 := bstep (se 1 (by rfl) ⟨1350077, by rfl⟩ : syracuseStep 1800103 = 2700155) B2700155
theorem B6486215 : Blo 1598998 6486215 := bstep (se 1 (by rfl) ⟨4864661, by rfl⟩ : syracuseStep 6486215 = 9729323) B9729323
theorem B2399399 : Blo 1598998 2399399 := bstep (se 1 (by rfl) ⟨1799549, by rfl⟩ : syracuseStep 2399399 = 3599099) B3599099
theorem B10255663 : Blo 1598998 10255663 := bstep (se 1 (by rfl) ⟨7691747, by rfl⟩ : syracuseStep 10255663 = 15383495) B15383495
theorem B2399609 : Blo 1598998 2399609 := bstep (se 2 (by rfl) ⟨899853, by rfl⟩ : syracuseStep 2399609 = 1799707) B1799707
theorem B2399615 : Blo 1598998 2399615 := bstep (se 1 (by rfl) ⟨1799711, by rfl⟩ : syracuseStep 2399615 = 3599423) B3599423
theorem B12648271 : Blo 1598998 12648271 := bstep (se 1 (by rfl) ⟨9486203, by rfl⟩ : syracuseStep 12648271 = 18972407) B18972407
theorem B3416231 : Blo 1598998 3416231 := bstep (se 1 (by rfl) ⟨2562173, by rfl⟩ : syracuseStep 3416231 = 5124347) B5124347
theorem B20504765 : Blo 1598998 20504765 := bstep (se 3 (by rfl) ⟨3844643, by rfl⟩ : syracuseStep 20504765 = 7689287) B7689287
theorem B13336771 : Blo 1598998 13336771 := bstep (se 1 (by rfl) ⟨10002578, by rfl⟩ : syracuseStep 13336771 = 20005157) B20005157
theorem B4047529 : Blo 1598998 4047529 := bstep (se 2 (by rfl) ⟨1517823, by rfl⟩ : syracuseStep 4047529 = 3035647) B3035647
theorem B8102591 : Blo 1598998 8102591 := bstep (se 1 (by rfl) ⟨6076943, by rfl⟩ : syracuseStep 8102591 = 12153887) B12153887
theorem B12149999 : Blo 1598998 12149999 := bstep (se 1 (by rfl) ⟨9112499, by rfl⟩ : syracuseStep 12149999 = 18224999) B18224999
theorem B5399837 : Blo 1598998 5399837 := bstep (se 3 (by rfl) ⟨1012469, by rfl⟩ : syracuseStep 5399837 = 2024939) B2024939
theorem B13674217 : Blo 1598998 13674217 := bstep (se 2 (by rfl) ⟨5127831, by rfl⟩ : syracuseStep 13674217 = 10255663) B10255663
theorem B43796315 : Blo 1598998 43796315 := bstep (se 1 (by rfl) ⟨32847236, by rfl⟩ : syracuseStep 43796315 = 65694473) B65694473
theorem B1599599 : Blo 1598998 1599599 := bstep (se 1 (by rfl) ⟨1199699, by rfl⟩ : syracuseStep 1599599 = 2399399) B2399399
theorem B1599739 : Blo 1598998 1599739 := bstep (se 1 (by rfl) ⟨1199804, by rfl⟩ : syracuseStep 1599739 = 2399609) B2399609
theorem B1599743 : Blo 1598998 1599743 := bstep (se 1 (by rfl) ⟨1199807, by rfl⟩ : syracuseStep 1599743 = 2399615) B2399615
theorem B3599225 : Blo 1598998 3599225 := bstep (se 2 (by rfl) ⟨1349709, by rfl⟩ : syracuseStep 3599225 = 2699419) B2699419
theorem B35089321 : Blo 1598998 35089321 := bstep (se 2 (by rfl) ⟨13158495, by rfl⟩ : syracuseStep 35089321 = 26316991) B26316991
theorem B17296573 : Blo 1598998 17296573 := bstep (se 3 (by rfl) ⟨3243107, by rfl⟩ : syracuseStep 17296573 = 6486215) B6486215
theorem B3599927 : Blo 1598998 3599927 := bstep (se 1 (by rfl) ⟨2699945, by rfl⟩ : syracuseStep 3599927 = 5399891) B5399891
theorem B65711681 : Blo 1598998 65711681 := bstep (se 2 (by rfl) ⟨24641880, by rfl⟩ : syracuseStep 65711681 = 49283761) B49283761
theorem B8097407 : Blo 1598998 8097407 := bstep (se 1 (by rfl) ⟨6073055, by rfl⟩ : syracuseStep 8097407 = 12146111) B12146111
theorem B13676201 : Blo 1598998 13676201 := bstep (se 2 (by rfl) ⟨5128575, by rfl⟩ : syracuseStep 13676201 = 10257151) B10257151
theorem B2699311 : Blo 1598998 2699311 := bstep (se 1 (by rfl) ⟨2024483, by rfl⟩ : syracuseStep 2699311 = 4048967) B4048967
theorem B5403293 : Blo 1598998 5403293 := bstep (se 3 (by rfl) ⟨1013117, by rfl⟩ : syracuseStep 5403293 = 2026235) B2026235
theorem B6075425 : Blo 1598998 6075425 := bstep (se 2 (by rfl) ⟨2278284, by rfl⟩ : syracuseStep 6075425 = 4556569) B4556569
theorem B16864361 : Blo 1598998 16864361 := bstep (se 2 (by rfl) ⟨6324135, by rfl⟩ : syracuseStep 16864361 = 12648271) B12648271
theorem B30741929 : Blo 1598998 30741929 := bstep (se 2 (by rfl) ⟨11528223, by rfl⟩ : syracuseStep 30741929 = 23056447) B23056447
theorem B14588585 : Blo 1598998 14588585 := bstep (se 2 (by rfl) ⟨5470719, by rfl⟩ : syracuseStep 14588585 = 10941439) B10941439
theorem B2399471 : Blo 1598998 2399471 := bstep (se 1 (by rfl) ⟨1799603, by rfl⟩ : syracuseStep 2399471 = 3599207) B3599207
theorem B2400137 : Blo 1598998 2400137 := bstep (se 2 (by rfl) ⟨900051, by rfl⟩ : syracuseStep 2400137 = 1800103) B1800103
theorem B30769145 : Blo 1598998 30769145 := bstep (se 2 (by rfl) ⟨11538429, by rfl⟩ : syracuseStep 30769145 = 23076859) B23076859
theorem B2277487 : Blo 1598998 2277487 := bstep (se 1 (by rfl) ⟨1708115, by rfl⟩ : syracuseStep 2277487 = 3416231) B3416231
theorem B46785761 : Blo 1598998 46785761 := bstep (se 2 (by rfl) ⟨17544660, by rfl⟩ : syracuseStep 46785761 = 35089321) B35089321
theorem B29197543 : Blo 1598998 29197543 := bstep (se 1 (by rfl) ⟨21898157, by rfl⟩ : syracuseStep 29197543 = 43796315) B43796315
theorem B23062097 : Blo 1598998 23062097 := bstep (se 2 (by rfl) ⟨8648286, by rfl⟩ : syracuseStep 23062097 = 17296573) B17296573
theorem B9725723 : Blo 1598998 9725723 := bstep (se 1 (by rfl) ⟨7294292, by rfl⟩ : syracuseStep 9725723 = 14588585) B14588585
theorem B20512763 : Blo 1598998 20512763 := bstep (se 1 (by rfl) ⟨15384572, by rfl⟩ : syracuseStep 20512763 = 30769145) B30769145
theorem B1599647 : Blo 1598998 1599647 := bstep (se 1 (by rfl) ⟨1199735, by rfl⟩ : syracuseStep 1599647 = 2399471) B2399471
theorem B1600091 : Blo 1598998 1600091 := bstep (se 1 (by rfl) ⟨1200068, by rfl⟩ : syracuseStep 1600091 = 2400137) B2400137
theorem B3599081 : Blo 1598998 3599081 := bstep (se 2 (by rfl) ⟨1349655, by rfl⟩ : syracuseStep 3599081 = 2699311) B2699311
theorem B5401727 : Blo 1598998 5401727 := bstep (se 1 (by rfl) ⟨4051295, by rfl⟩ : syracuseStep 5401727 = 8102591) B8102591
theorem B4050283 : Blo 1598998 4050283 := bstep (se 1 (by rfl) ⟨3037712, by rfl⟩ : syracuseStep 4050283 = 6075425) B6075425
theorem B11242907 : Blo 1598998 11242907 := bstep (se 1 (by rfl) ⟨8432180, by rfl⟩ : syracuseStep 11242907 = 16864361) B16864361
theorem B3599891 : Blo 1598998 3599891 := bstep (se 1 (by rfl) ⟨2699918, by rfl⟩ : syracuseStep 3599891 = 5399837) B5399837
theorem B18232289 : Blo 1598998 18232289 := bstep (se 2 (by rfl) ⟨6837108, by rfl⟩ : syracuseStep 18232289 = 13674217) B13674217
theorem B43807787 : Blo 1598998 43807787 := bstep (se 1 (by rfl) ⟨32855840, by rfl⟩ : syracuseStep 43807787 = 65711681) B65711681
theorem B13669843 : Blo 1598998 13669843 := bstep (se 1 (by rfl) ⟨10252382, by rfl⟩ : syracuseStep 13669843 = 20504765) B20504765
theorem B17782361 : Blo 1598998 17782361 := bstep (se 2 (by rfl) ⟨6668385, by rfl⟩ : syracuseStep 17782361 = 13336771) B13336771
theorem B3602195 : Blo 1598998 3602195 := bstep (se 1 (by rfl) ⟨2701646, by rfl⟩ : syracuseStep 3602195 = 5403293) B5403293
theorem B8099999 : Blo 1598998 8099999 := bstep (se 1 (by rfl) ⟨6074999, by rfl⟩ : syracuseStep 8099999 = 12149999) B12149999
theorem B5396705 : Blo 1598998 5396705 := bstep (se 2 (by rfl) ⟨2023764, by rfl⟩ : syracuseStep 5396705 = 4047529) B4047529
theorem B20494619 : Blo 1598998 20494619 := bstep (se 1 (by rfl) ⟨15370964, by rfl⟩ : syracuseStep 20494619 = 30741929) B30741929
theorem B2399483 : Blo 1598998 2399483 := bstep (se 1 (by rfl) ⟨1799612, by rfl⟩ : syracuseStep 2399483 = 3599225) B3599225
theorem B2399951 : Blo 1598998 2399951 := bstep (se 1 (by rfl) ⟨1799963, by rfl⟩ : syracuseStep 2399951 = 3599927) B3599927
theorem B5398271 : Blo 1598998 5398271 := bstep (se 1 (by rfl) ⟨4048703, by rfl⟩ : syracuseStep 5398271 = 8097407) B8097407
theorem B9117467 : Blo 1598998 9117467 := bstep (se 1 (by rfl) ⟨6838100, by rfl⟩ : syracuseStep 9117467 = 13676201) B13676201
theorem B29205191 : Blo 1598998 29205191 := bstep (se 1 (by rfl) ⟨21903893, by rfl⟩ : syracuseStep 29205191 = 43807787) B43807787
theorem B11854907 : Blo 1598998 11854907 := bstep (se 1 (by rfl) ⟨8891180, by rfl⟩ : syracuseStep 11854907 = 17782361) B17782361
theorem B2401463 : Blo 1598998 2401463 := bstep (se 1 (by rfl) ⟨1801097, by rfl⟩ : syracuseStep 2401463 = 3602195) B3602195
theorem B5399999 : Blo 1598998 5399999 := bstep (se 1 (by rfl) ⟨4049999, by rfl⟩ : syracuseStep 5399999 = 8099999) B8099999
theorem B3597803 : Blo 1598998 3597803 := bstep (se 1 (by rfl) ⟨2698352, by rfl⟩ : syracuseStep 3597803 = 5396705) B5396705
theorem B38930057 : Blo 1598998 38930057 := bstep (se 2 (by rfl) ⟨14598771, by rfl⟩ : syracuseStep 38930057 = 29197543) B29197543
theorem B5400377 : Blo 1598998 5400377 := bstep (se 2 (by rfl) ⟨2025141, by rfl⟩ : syracuseStep 5400377 = 4050283) B4050283
theorem B1599655 : Blo 1598998 1599655 := bstep (se 1 (by rfl) ⟨1199741, by rfl⟩ : syracuseStep 1599655 = 2399483) B2399483
theorem B1599967 : Blo 1598998 1599967 := bstep (se 1 (by rfl) ⟨1199975, by rfl⟩ : syracuseStep 1599967 = 2399951) B2399951
theorem B3598847 : Blo 1598998 3598847 := bstep (se 1 (by rfl) ⟨2699135, by rfl⟩ : syracuseStep 3598847 = 5398271) B5398271
theorem B13675175 : Blo 1598998 13675175 := bstep (se 1 (by rfl) ⟨10256381, by rfl⟩ : syracuseStep 13675175 = 20512763) B20512763
theorem B31190507 : Blo 1598998 31190507 := bstep (se 1 (by rfl) ⟨23392880, by rfl⟩ : syracuseStep 31190507 = 46785761) B46785761
theorem B6483815 : Blo 1598998 6483815 := bstep (se 1 (by rfl) ⟨4862861, by rfl⟩ : syracuseStep 6483815 = 9725723) B9725723
theorem B3601151 : Blo 1598998 3601151 := bstep (se 1 (by rfl) ⟨2700863, by rfl⟩ : syracuseStep 3601151 = 5401727) B5401727
theorem B12146597 : Blo 1598998 12146597 := bstep (se 4 (by rfl) ⟨1138743, by rfl⟩ : syracuseStep 12146597 = 2277487) B2277487
theorem B12154859 : Blo 1598998 12154859 := bstep (se 1 (by rfl) ⟨9116144, by rfl⟩ : syracuseStep 12154859 = 18232289) B18232289
theorem B15374731 : Blo 1598998 15374731 := bstep (se 1 (by rfl) ⟨11531048, by rfl⟩ : syracuseStep 15374731 = 23062097) B23062097
theorem B13663079 : Blo 1598998 13663079 := bstep (se 1 (by rfl) ⟨10247309, by rfl⟩ : syracuseStep 13663079 = 20494619) B20494619
theorem B2399387 : Blo 1598998 2399387 := bstep (se 1 (by rfl) ⟨1799540, by rfl⟩ : syracuseStep 2399387 = 3599081) B3599081
theorem B18226457 : Blo 1598998 18226457 := bstep (se 2 (by rfl) ⟨6834921, by rfl⟩ : syracuseStep 18226457 = 13669843) B13669843
theorem B7495271 : Blo 1598998 7495271 := bstep (se 1 (by rfl) ⟨5621453, by rfl⟩ : syracuseStep 7495271 = 11242907) B11242907
theorem B2399927 : Blo 1598998 2399927 := bstep (se 1 (by rfl) ⟨1799945, by rfl⟩ : syracuseStep 2399927 = 3599891) B3599891
theorem B6078311 : Blo 1598998 6078311 := bstep (se 1 (by rfl) ⟨4558733, by rfl⟩ : syracuseStep 6078311 = 9117467) B9117467
theorem B2400767 : Blo 1598998 2400767 := bstep (se 1 (by rfl) ⟨1800575, by rfl⟩ : syracuseStep 2400767 = 3601151) B3601151
theorem B25953371 : Blo 1598998 25953371 := bstep (se 1 (by rfl) ⟨19465028, by rfl⟩ : syracuseStep 25953371 = 38930057) B38930057
theorem B8103239 : Blo 1598998 8103239 := bstep (se 1 (by rfl) ⟨6077429, by rfl⟩ : syracuseStep 8103239 = 12154859) B12154859
theorem B1599591 : Blo 1598998 1599591 := bstep (se 1 (by rfl) ⟨1199693, by rfl⟩ : syracuseStep 1599591 = 2399387) B2399387
theorem B12150971 : Blo 1598998 12150971 := bstep (se 1 (by rfl) ⟨9113228, by rfl⟩ : syracuseStep 12150971 = 18226457) B18226457
theorem B20793671 : Blo 1598998 20793671 := bstep (se 1 (by rfl) ⟨15595253, by rfl⟩ : syracuseStep 20793671 = 31190507) B31190507
theorem B1599951 : Blo 1598998 1599951 := bstep (se 1 (by rfl) ⟨1199963, by rfl⟩ : syracuseStep 1599951 = 2399927) B2399927
theorem B20499641 : Blo 1598998 20499641 := bstep (se 2 (by rfl) ⟨7687365, by rfl⟩ : syracuseStep 20499641 = 15374731) B15374731
theorem B1600975 : Blo 1598998 1600975 := bstep (se 1 (by rfl) ⟨1200731, by rfl⟩ : syracuseStep 1600975 = 2401463) B2401463
theorem B3599999 : Blo 1598998 3599999 := bstep (se 1 (by rfl) ⟨2699999, by rfl⟩ : syracuseStep 3599999 = 5399999) B5399999
theorem B3600251 : Blo 1598998 3600251 := bstep (se 1 (by rfl) ⟨2700188, by rfl⟩ : syracuseStep 3600251 = 5400377) B5400377
theorem B8097731 : Blo 1598998 8097731 := bstep (se 1 (by rfl) ⟨6073298, by rfl⟩ : syracuseStep 8097731 = 12146597) B12146597
theorem B4322543 : Blo 1598998 4322543 := bstep (se 1 (by rfl) ⟨3241907, by rfl⟩ : syracuseStep 4322543 = 6483815) B6483815
theorem B4052207 : Blo 1598998 4052207 := bstep (se 1 (by rfl) ⟨3039155, by rfl⟩ : syracuseStep 4052207 = 6078311) B6078311
theorem B19470127 : Blo 1598998 19470127 := bstep (se 1 (by rfl) ⟨14602595, by rfl⟩ : syracuseStep 19470127 = 29205191) B29205191
theorem B7903271 : Blo 1598998 7903271 := bstep (se 1 (by rfl) ⟨5927453, by rfl⟩ : syracuseStep 7903271 = 11854907) B11854907
theorem B2398535 : Blo 1598998 2398535 := bstep (se 1 (by rfl) ⟨1798901, by rfl⟩ : syracuseStep 2398535 = 3597803) B3597803
theorem B2399231 : Blo 1598998 2399231 := bstep (se 1 (by rfl) ⟨1799423, by rfl⟩ : syracuseStep 2399231 = 3598847) B3598847
theorem B9116783 : Blo 1598998 9116783 := bstep (se 1 (by rfl) ⟨6837587, by rfl⟩ : syracuseStep 9116783 = 13675175) B13675175
theorem B9108719 : Blo 1598998 9108719 := bstep (se 1 (by rfl) ⟨6831539, by rfl⟩ : syracuseStep 9108719 = 13663079) B13663079
theorem B4996847 : Blo 1598998 4996847 := bstep (se 1 (by rfl) ⟨3747635, by rfl⟩ : syracuseStep 4996847 = 7495271) B7495271
theorem B11526781 : Blo 1598998 11526781 := bstep (se 3 (by rfl) ⟨2161271, by rfl⟩ : syracuseStep 11526781 = 4322543) B4322543
theorem B17302247 : Blo 1598998 17302247 := bstep (se 1 (by rfl) ⟨12976685, by rfl⟩ : syracuseStep 17302247 = 25953371) B25953371
theorem B5268847 : Blo 1598998 5268847 := bstep (se 1 (by rfl) ⟨3951635, by rfl⟩ : syracuseStep 5268847 = 7903271) B7903271
theorem B1599023 : Blo 1598998 1599023 := bstep (se 1 (by rfl) ⟨1199267, by rfl⟩ : syracuseStep 1599023 = 2398535) B2398535
theorem B13862447 : Blo 1598998 13862447 := bstep (se 1 (by rfl) ⟨10396835, by rfl⟩ : syracuseStep 13862447 = 20793671) B20793671
theorem B1599487 : Blo 1598998 1599487 := bstep (se 1 (by rfl) ⟨1199615, by rfl⟩ : syracuseStep 1599487 = 2399231) B2399231
theorem B13666427 : Blo 1598998 13666427 := bstep (se 1 (by rfl) ⟨10249820, by rfl⟩ : syracuseStep 13666427 = 20499641) B20499641
theorem B6072479 : Blo 1598998 6072479 := bstep (se 1 (by rfl) ⟨4554359, by rfl⟩ : syracuseStep 6072479 = 9108719) B9108719
theorem B1600511 : Blo 1598998 1600511 := bstep (se 1 (by rfl) ⟨1200383, by rfl⟩ : syracuseStep 1600511 = 2400767) B2400767
theorem B5402159 : Blo 1598998 5402159 := bstep (se 1 (by rfl) ⟨4051619, by rfl⟩ : syracuseStep 5402159 = 8103239) B8103239
theorem B13324925 : Blo 1598998 13324925 := bstep (se 3 (by rfl) ⟨2498423, by rfl⟩ : syracuseStep 13324925 = 4996847) B4996847
theorem B2701471 : Blo 1598998 2701471 := bstep (se 1 (by rfl) ⟨2026103, by rfl⟩ : syracuseStep 2701471 = 4052207) B4052207
theorem B8100647 : Blo 1598998 8100647 := bstep (se 1 (by rfl) ⟨6075485, by rfl⟩ : syracuseStep 8100647 = 12150971) B12150971
theorem B6077855 : Blo 1598998 6077855 := bstep (se 1 (by rfl) ⟨4558391, by rfl⟩ : syracuseStep 6077855 = 9116783) B9116783
theorem B25960169 : Blo 1598998 25960169 := bstep (se 2 (by rfl) ⟨9735063, by rfl⟩ : syracuseStep 25960169 = 19470127) B19470127
theorem B2399999 : Blo 1598998 2399999 := bstep (se 1 (by rfl) ⟨1799999, by rfl⟩ : syracuseStep 2399999 = 3599999) B3599999
theorem B2400167 : Blo 1598998 2400167 := bstep (se 1 (by rfl) ⟨1800125, by rfl⟩ : syracuseStep 2400167 = 3600251) B3600251
theorem B5398487 : Blo 1598998 5398487 := bstep (se 1 (by rfl) ⟨4048865, by rfl⟩ : syracuseStep 5398487 = 8097731) B8097731
theorem B11534831 : Blo 1598998 11534831 := bstep (se 1 (by rfl) ⟨8651123, by rfl⟩ : syracuseStep 11534831 = 17302247) B17302247
theorem B15369041 : Blo 1598998 15369041 := bstep (se 2 (by rfl) ⟨5763390, by rfl⟩ : syracuseStep 15369041 = 11526781) B11526781
theorem B9241631 : Blo 1598998 9241631 := bstep (se 1 (by rfl) ⟨6931223, by rfl⟩ : syracuseStep 9241631 = 13862447) B13862447
theorem B9110951 : Blo 1598998 9110951 := bstep (se 1 (by rfl) ⟨6833213, by rfl⟩ : syracuseStep 9110951 = 13666427) B13666427
theorem B4048319 : Blo 1598998 4048319 := bstep (se 1 (by rfl) ⟨3036239, by rfl⟩ : syracuseStep 4048319 = 6072479) B6072479
theorem B5400431 : Blo 1598998 5400431 := bstep (se 1 (by rfl) ⟨4050323, by rfl⟩ : syracuseStep 5400431 = 8100647) B8100647
theorem B1599999 : Blo 1598998 1599999 := bstep (se 1 (by rfl) ⟨1199999, by rfl⟩ : syracuseStep 1599999 = 2399999) B2399999
theorem B1600111 : Blo 1598998 1600111 := bstep (se 1 (by rfl) ⟨1200083, by rfl⟩ : syracuseStep 1600111 = 2400167) B2400167
theorem B3598991 : Blo 1598998 3598991 := bstep (se 1 (by rfl) ⟨2699243, by rfl⟩ : syracuseStep 3598991 = 5398487) B5398487
theorem B8883283 : Blo 1598998 8883283 := bstep (se 1 (by rfl) ⟨6662462, by rfl⟩ : syracuseStep 8883283 = 13324925) B13324925
theorem B7025129 : Blo 1598998 7025129 := bstep (se 2 (by rfl) ⟨2634423, by rfl⟩ : syracuseStep 7025129 = 5268847) B5268847
theorem B4051903 : Blo 1598998 4051903 := bstep (se 1 (by rfl) ⟨3038927, by rfl⟩ : syracuseStep 4051903 = 6077855) B6077855
theorem B3601439 : Blo 1598998 3601439 := bstep (se 1 (by rfl) ⟨2701079, by rfl⟩ : syracuseStep 3601439 = 5402159) B5402159
theorem B17306779 : Blo 1598998 17306779 := bstep (se 1 (by rfl) ⟨12980084, by rfl⟩ : syracuseStep 17306779 = 25960169) B25960169
theorem B3601961 : Blo 1598998 3601961 := bstep (se 2 (by rfl) ⟨1350735, by rfl⟩ : syracuseStep 3601961 = 2701471) B2701471
theorem B2400959 : Blo 1598998 2400959 := bstep (se 1 (by rfl) ⟨1800719, by rfl⟩ : syracuseStep 2400959 = 3601439) B3601439
theorem B6161087 : Blo 1598998 6161087 := bstep (se 1 (by rfl) ⟨4620815, by rfl⟩ : syracuseStep 6161087 = 9241631) B9241631
theorem B2401307 : Blo 1598998 2401307 := bstep (se 1 (by rfl) ⟨1800980, by rfl⟩ : syracuseStep 2401307 = 3601961) B3601961
theorem B6073967 : Blo 1598998 6073967 := bstep (se 1 (by rfl) ⟨4555475, by rfl⟩ : syracuseStep 6073967 = 9110951) B9110951
theorem B2698879 : Blo 1598998 2698879 := bstep (se 1 (by rfl) ⟨2024159, by rfl⟩ : syracuseStep 2698879 = 4048319) B4048319
theorem B3600287 : Blo 1598998 3600287 := bstep (se 1 (by rfl) ⟨2700215, by rfl⟩ : syracuseStep 3600287 = 5400431) B5400431
theorem B5402537 : Blo 1598998 5402537 := bstep (se 2 (by rfl) ⟨2025951, by rfl⟩ : syracuseStep 5402537 = 4051903) B4051903
theorem B4683419 : Blo 1598998 4683419 := bstep (se 1 (by rfl) ⟨3512564, by rfl⟩ : syracuseStep 4683419 = 7025129) B7025129
theorem B7689887 : Blo 1598998 7689887 := bstep (se 1 (by rfl) ⟨5767415, by rfl⟩ : syracuseStep 7689887 = 11534831) B11534831
theorem B10246027 : Blo 1598998 10246027 := bstep (se 1 (by rfl) ⟨7684520, by rfl⟩ : syracuseStep 10246027 = 15369041) B15369041
theorem B11844377 : Blo 1598998 11844377 := bstep (se 2 (by rfl) ⟨4441641, by rfl⟩ : syracuseStep 11844377 = 8883283) B8883283
theorem B23075705 : Blo 1598998 23075705 := bstep (se 2 (by rfl) ⟨8653389, by rfl⟩ : syracuseStep 23075705 = 17306779) B17306779
theorem B2399327 : Blo 1598998 2399327 := bstep (se 1 (by rfl) ⟨1799495, by rfl⟩ : syracuseStep 2399327 = 3598991) B3598991
theorem B3122279 : Blo 1598998 3122279 := bstep (se 1 (by rfl) ⟨2341709, by rfl⟩ : syracuseStep 3122279 = 4683419) B4683419
theorem B1599551 : Blo 1598998 1599551 := bstep (se 1 (by rfl) ⟨1199663, by rfl⟩ : syracuseStep 1599551 = 2399327) B2399327
theorem B3598505 : Blo 1598998 3598505 := bstep (se 2 (by rfl) ⟨1349439, by rfl⟩ : syracuseStep 3598505 = 2698879) B2698879
theorem B4049311 : Blo 1598998 4049311 := bstep (se 1 (by rfl) ⟨3036983, by rfl⟩ : syracuseStep 4049311 = 6073967) B6073967
theorem B1600639 : Blo 1598998 1600639 := bstep (se 1 (by rfl) ⟨1200479, by rfl⟩ : syracuseStep 1600639 = 2400959) B2400959
theorem B4107391 : Blo 1598998 4107391 := bstep (se 1 (by rfl) ⟨3080543, by rfl⟩ : syracuseStep 4107391 = 6161087) B6161087
theorem B1600871 : Blo 1598998 1600871 := bstep (se 1 (by rfl) ⟨1200653, by rfl⟩ : syracuseStep 1600871 = 2401307) B2401307
theorem B13661369 : Blo 1598998 13661369 := bstep (se 2 (by rfl) ⟨5123013, by rfl⟩ : syracuseStep 13661369 = 10246027) B10246027
theorem B3601691 : Blo 1598998 3601691 := bstep (se 1 (by rfl) ⟨2701268, by rfl⟩ : syracuseStep 3601691 = 5402537) B5402537
theorem B5126591 : Blo 1598998 5126591 := bstep (se 1 (by rfl) ⟨3844943, by rfl⟩ : syracuseStep 5126591 = 7689887) B7689887
theorem B7896251 : Blo 1598998 7896251 := bstep (se 1 (by rfl) ⟨5922188, by rfl⟩ : syracuseStep 7896251 = 11844377) B11844377
theorem B15383803 : Blo 1598998 15383803 := bstep (se 1 (by rfl) ⟨11537852, by rfl⟩ : syracuseStep 15383803 = 23075705) B23075705
theorem B2400191 : Blo 1598998 2400191 := bstep (se 1 (by rfl) ⟨1800143, by rfl⟩ : syracuseStep 2400191 = 3600287) B3600287
theorem B5399081 : Blo 1598998 5399081 := bstep (se 2 (by rfl) ⟨2024655, by rfl⟩ : syracuseStep 5399081 = 4049311) B4049311
theorem B2081519 : Blo 1598998 2081519 := bstep (se 1 (by rfl) ⟨1561139, by rfl⟩ : syracuseStep 2081519 = 3122279) B3122279
theorem B2401127 : Blo 1598998 2401127 := bstep (se 1 (by rfl) ⟨1800845, by rfl⟩ : syracuseStep 2401127 = 3601691) B3601691
theorem B3417727 : Blo 1598998 3417727 := bstep (se 1 (by rfl) ⟨2563295, by rfl⟩ : syracuseStep 3417727 = 5126591) B5126591
theorem B1600127 : Blo 1598998 1600127 := bstep (se 1 (by rfl) ⟨1200095, by rfl⟩ : syracuseStep 1600127 = 2400191) B2400191
theorem B87624341 : Blo 1598998 87624341 := bstep (se 6 (by rfl) ⟨2053695, by rfl⟩ : syracuseStep 87624341 = 4107391) B4107391
theorem B21056669 : Blo 1598998 21056669 := bstep (se 3 (by rfl) ⟨3948125, by rfl⟩ : syracuseStep 21056669 = 7896251) B7896251
theorem B9107579 : Blo 1598998 9107579 := bstep (se 1 (by rfl) ⟨6830684, by rfl⟩ : syracuseStep 9107579 = 13661369) B13661369
theorem B2399003 : Blo 1598998 2399003 := bstep (se 1 (by rfl) ⟨1799252, by rfl⟩ : syracuseStep 2399003 = 3598505) B3598505
theorem B20511737 : Blo 1598998 20511737 := bstep (se 2 (by rfl) ⟨7691901, by rfl⟩ : syracuseStep 20511737 = 15383803) B15383803
theorem B6071719 : Blo 1598998 6071719 := bstep (se 1 (by rfl) ⟨4553789, by rfl⟩ : syracuseStep 6071719 = 9107579) B9107579
theorem B1599335 : Blo 1598998 1599335 := bstep (se 1 (by rfl) ⟨1199501, by rfl⟩ : syracuseStep 1599335 = 2399003) B2399003
theorem B13674491 : Blo 1598998 13674491 := bstep (se 1 (by rfl) ⟨10255868, by rfl⟩ : syracuseStep 13674491 = 20511737) B20511737
theorem B4556969 : Blo 1598998 4556969 := bstep (se 2 (by rfl) ⟨1708863, by rfl⟩ : syracuseStep 4556969 = 3417727) B3417727
theorem B22202869 : Blo 1598998 22202869 := bstep (se 5 (by rfl) ⟨1040759, by rfl⟩ : syracuseStep 22202869 = 2081519) B2081519
theorem B3599387 : Blo 1598998 3599387 := bstep (se 1 (by rfl) ⟨2699540, by rfl⟩ : syracuseStep 3599387 = 5399081) B5399081
theorem B1600751 : Blo 1598998 1600751 := bstep (se 1 (by rfl) ⟨1200563, by rfl⟩ : syracuseStep 1600751 = 2401127) B2401127
theorem B14037779 : Blo 1598998 14037779 := bstep (se 1 (by rfl) ⟨10528334, by rfl⟩ : syracuseStep 14037779 = 21056669) B21056669
theorem B58416227 : Blo 1598998 58416227 := bstep (se 1 (by rfl) ⟨43812170, by rfl⟩ : syracuseStep 58416227 = 87624341) B87624341
theorem B8095625 : Blo 1598998 8095625 := bstep (se 2 (by rfl) ⟨3035859, by rfl⟩ : syracuseStep 8095625 = 6071719) B6071719
theorem B9358519 : Blo 1598998 9358519 := bstep (se 1 (by rfl) ⟨7018889, by rfl⟩ : syracuseStep 9358519 = 14037779) B14037779
theorem B29603825 : Blo 1598998 29603825 := bstep (se 2 (by rfl) ⟨11101434, by rfl⟩ : syracuseStep 29603825 = 22202869) B22202869
theorem B9116327 : Blo 1598998 9116327 := bstep (se 1 (by rfl) ⟨6837245, by rfl⟩ : syracuseStep 9116327 = 13674491) B13674491
theorem B3037979 : Blo 1598998 3037979 := bstep (se 1 (by rfl) ⟨2278484, by rfl⟩ : syracuseStep 3037979 = 4556969) B4556969
theorem B2399591 : Blo 1598998 2399591 := bstep (se 1 (by rfl) ⟨1799693, by rfl⟩ : syracuseStep 2399591 = 3599387) B3599387
theorem B38944151 : Blo 1598998 38944151 := bstep (se 1 (by rfl) ⟨29208113, by rfl⟩ : syracuseStep 38944151 = 58416227) B58416227
theorem B19735883 : Blo 1598998 19735883 := bstep (se 1 (by rfl) ⟨14801912, by rfl⟩ : syracuseStep 19735883 = 29603825) B29603825
theorem B12478025 : Blo 1598998 12478025 := bstep (se 2 (by rfl) ⟨4679259, by rfl⟩ : syracuseStep 12478025 = 9358519) B9358519
theorem B2025319 : Blo 1598998 2025319 := bstep (se 1 (by rfl) ⟨1518989, by rfl⟩ : syracuseStep 2025319 = 3037979) B3037979
theorem B1599727 : Blo 1598998 1599727 := bstep (se 1 (by rfl) ⟨1199795, by rfl⟩ : syracuseStep 1599727 = 2399591) B2399591
theorem B25962767 : Blo 1598998 25962767 := bstep (se 1 (by rfl) ⟨19472075, by rfl⟩ : syracuseStep 25962767 = 38944151) B38944151
theorem B5397083 : Blo 1598998 5397083 := bstep (se 1 (by rfl) ⟨4047812, by rfl⟩ : syracuseStep 5397083 = 8095625) B8095625
theorem B6077551 : Blo 1598998 6077551 := bstep (se 1 (by rfl) ⟨4558163, by rfl⟩ : syracuseStep 6077551 = 9116327) B9116327
theorem B13157255 : Blo 1598998 13157255 := bstep (se 1 (by rfl) ⟨9867941, by rfl⟩ : syracuseStep 13157255 = 19735883) B19735883
theorem B8103401 : Blo 1598998 8103401 := bstep (se 2 (by rfl) ⟨3038775, by rfl⟩ : syracuseStep 8103401 = 6077551) B6077551
theorem B3598055 : Blo 1598998 3598055 := bstep (se 1 (by rfl) ⟨2698541, by rfl⟩ : syracuseStep 3598055 = 5397083) B5397083
theorem B8318683 : Blo 1598998 8318683 := bstep (se 1 (by rfl) ⟨6239012, by rfl⟩ : syracuseStep 8318683 = 12478025) B12478025
theorem B2700425 : Blo 1598998 2700425 := bstep (se 2 (by rfl) ⟨1012659, by rfl⟩ : syracuseStep 2700425 = 2025319) B2025319
theorem B17308511 : Blo 1598998 17308511 := bstep (se 1 (by rfl) ⟨12981383, by rfl⟩ : syracuseStep 17308511 = 25962767) B25962767
theorem B5402267 : Blo 1598998 5402267 := bstep (se 1 (by rfl) ⟨4051700, by rfl⟩ : syracuseStep 5402267 = 8103401) B8103401
theorem B11539007 : Blo 1598998 11539007 := bstep (se 1 (by rfl) ⟨8654255, by rfl⟩ : syracuseStep 11539007 = 17308511) B17308511
theorem B8771503 : Blo 1598998 8771503 := bstep (se 1 (by rfl) ⟨6578627, by rfl⟩ : syracuseStep 8771503 = 13157255) B13157255
theorem B1800283 : Blo 1598998 1800283 := bstep (se 1 (by rfl) ⟨1350212, by rfl⟩ : syracuseStep 1800283 = 2700425) B2700425
theorem B2398703 : Blo 1598998 2398703 := bstep (se 1 (by rfl) ⟨1799027, by rfl⟩ : syracuseStep 2398703 = 3598055) B3598055
theorem B11091577 : Blo 1598998 11091577 := bstep (se 2 (by rfl) ⟨4159341, by rfl⟩ : syracuseStep 11091577 = 8318683) B8318683
theorem B2400377 : Blo 1598998 2400377 := bstep (se 2 (by rfl) ⟨900141, by rfl⟩ : syracuseStep 2400377 = 1800283) B1800283
theorem B7692671 : Blo 1598998 7692671 := bstep (se 1 (by rfl) ⟨5769503, by rfl⟩ : syracuseStep 7692671 = 11539007) B11539007
theorem B1599135 : Blo 1598998 1599135 := bstep (se 1 (by rfl) ⟨1199351, by rfl⟩ : syracuseStep 1599135 = 2398703) B2398703
theorem B14788769 : Blo 1598998 14788769 := bstep (se 2 (by rfl) ⟨5545788, by rfl⟩ : syracuseStep 14788769 = 11091577) B11091577
theorem B3601511 : Blo 1598998 3601511 := bstep (se 1 (by rfl) ⟨2701133, by rfl⟩ : syracuseStep 3601511 = 5402267) B5402267
theorem B11695337 : Blo 1598998 11695337 := bstep (se 2 (by rfl) ⟨4385751, by rfl⟩ : syracuseStep 11695337 = 8771503) B8771503
theorem B5128447 : Blo 1598998 5128447 := bstep (se 1 (by rfl) ⟨3846335, by rfl⟩ : syracuseStep 5128447 = 7692671) B7692671
theorem B39436717 : Blo 1598998 39436717 := bstep (se 3 (by rfl) ⟨7394384, by rfl⟩ : syracuseStep 39436717 = 14788769) B14788769
theorem B2401007 : Blo 1598998 2401007 := bstep (se 1 (by rfl) ⟨1800755, by rfl⟩ : syracuseStep 2401007 = 3601511) B3601511
theorem B1600251 : Blo 1598998 1600251 := bstep (se 1 (by rfl) ⟨1200188, by rfl⟩ : syracuseStep 1600251 = 2400377) B2400377
theorem B7796891 : Blo 1598998 7796891 := bstep (se 1 (by rfl) ⟨5847668, by rfl⟩ : syracuseStep 7796891 = 11695337) B11695337
theorem B1600671 : Blo 1598998 1600671 := bstep (se 1 (by rfl) ⟨1200503, by rfl⟩ : syracuseStep 1600671 = 2401007) B2401007
theorem B5197927 : Blo 1598998 5197927 := bstep (se 1 (by rfl) ⟨3898445, by rfl⟩ : syracuseStep 5197927 = 7796891) B7796891
theorem B6837929 : Blo 1598998 6837929 := bstep (se 2 (by rfl) ⟨2564223, by rfl⟩ : syracuseStep 6837929 = 5128447) B5128447
theorem B52582289 : Blo 1598998 52582289 := bstep (se 2 (by rfl) ⟨19718358, by rfl⟩ : syracuseStep 52582289 = 39436717) B39436717
theorem B6930569 : Blo 1598998 6930569 := bstep (se 2 (by rfl) ⟨2598963, by rfl⟩ : syracuseStep 6930569 = 5197927) B5197927
theorem B4558619 : Blo 1598998 4558619 := bstep (se 1 (by rfl) ⟨3418964, by rfl⟩ : syracuseStep 4558619 = 6837929) B6837929
theorem B140219437 : Blo 1598998 140219437 := bstep (se 3 (by rfl) ⟨26291144, by rfl⟩ : syracuseStep 140219437 = 52582289) B52582289
theorem B18481517 : Blo 1598998 18481517 := bstep (se 3 (by rfl) ⟨3465284, by rfl⟩ : syracuseStep 18481517 = 6930569) B6930569
theorem B186959249 : Blo 1598998 186959249 := bstep (se 2 (by rfl) ⟨70109718, by rfl⟩ : syracuseStep 186959249 = 140219437) B140219437
theorem B12156317 : Blo 1598998 12156317 := bstep (se 3 (by rfl) ⟨2279309, by rfl⟩ : syracuseStep 12156317 = 4558619) B4558619
theorem B12321011 : Blo 1598998 12321011 := bstep (se 1 (by rfl) ⟨9240758, by rfl⟩ : syracuseStep 12321011 = 18481517) B18481517
theorem B8104211 : Blo 1598998 8104211 := bstep (se 1 (by rfl) ⟨6078158, by rfl⟩ : syracuseStep 8104211 = 12156317) B12156317
theorem B124639499 : Blo 1598998 124639499 := bstep (se 1 (by rfl) ⟨93479624, by rfl⟩ : syracuseStep 124639499 = 186959249) B186959249
theorem B83092999 : Blo 1598998 83092999 := bstep (se 1 (by rfl) ⟨62319749, by rfl⟩ : syracuseStep 83092999 = 124639499) B124639499
theorem B5402807 : Blo 1598998 5402807 := bstep (se 1 (by rfl) ⟨4052105, by rfl⟩ : syracuseStep 5402807 = 8104211) B8104211
theorem B8214007 : Blo 1598998 8214007 := bstep (se 1 (by rfl) ⟨6160505, by rfl⟩ : syracuseStep 8214007 = 12321011) B12321011
theorem B110790665 : Blo 1598998 110790665 := bstep (se 2 (by rfl) ⟨41546499, by rfl⟩ : syracuseStep 110790665 = 83092999) B83092999
theorem B3601871 : Blo 1598998 3601871 := bstep (se 1 (by rfl) ⟨2701403, by rfl⟩ : syracuseStep 3601871 = 5402807) B5402807
theorem B10952009 : Blo 1598998 10952009 := bstep (se 2 (by rfl) ⟨4107003, by rfl⟩ : syracuseStep 10952009 = 8214007) B8214007
theorem B2401247 : Blo 1598998 2401247 := bstep (se 1 (by rfl) ⟨1800935, by rfl⟩ : syracuseStep 2401247 = 3601871) B3601871
theorem B73860443 : Blo 1598998 73860443 := bstep (se 1 (by rfl) ⟨55395332, by rfl⟩ : syracuseStep 73860443 = 110790665) B110790665
theorem B7301339 : Blo 1598998 7301339 := bstep (se 1 (by rfl) ⟨5476004, by rfl⟩ : syracuseStep 7301339 = 10952009) B10952009
theorem B4867559 : Blo 1598998 4867559 := bstep (se 1 (by rfl) ⟨3650669, by rfl⟩ : syracuseStep 4867559 = 7301339) B7301339
theorem B1600831 : Blo 1598998 1600831 := bstep (se 1 (by rfl) ⟨1200623, by rfl⟩ : syracuseStep 1600831 = 2401247) B2401247
theorem B49240295 : Blo 1598998 49240295 := bstep (se 1 (by rfl) ⟨36930221, by rfl⟩ : syracuseStep 49240295 = 73860443) B73860443
theorem B3245039 : Blo 1598998 3245039 := bstep (se 1 (by rfl) ⟨2433779, by rfl⟩ : syracuseStep 3245039 = 4867559) B4867559
theorem B32826863 : Blo 1598998 32826863 := bstep (se 1 (by rfl) ⟨24620147, by rfl⟩ : syracuseStep 32826863 = 49240295) B49240295
theorem B2163359 : Blo 1598998 2163359 := bstep (se 1 (by rfl) ⟨1622519, by rfl⟩ : syracuseStep 2163359 = 3245039) B3245039
theorem B21884575 : Blo 1598998 21884575 := bstep (se 1 (by rfl) ⟨16413431, by rfl⟩ : syracuseStep 21884575 = 32826863) B32826863
theorem B5768957 : Blo 1598998 5768957 := bstep (se 3 (by rfl) ⟨1081679, by rfl⟩ : syracuseStep 5768957 = 2163359) B2163359
theorem B29179433 : Blo 1598998 29179433 := bstep (se 2 (by rfl) ⟨10942287, by rfl⟩ : syracuseStep 29179433 = 21884575) B21884575
theorem B3845971 : Blo 1598998 3845971 := bstep (se 1 (by rfl) ⟨2884478, by rfl⟩ : syracuseStep 3845971 = 5768957) B5768957
theorem B19452955 : Blo 1598998 19452955 := bstep (se 1 (by rfl) ⟨14589716, by rfl⟩ : syracuseStep 19452955 = 29179433) B29179433
theorem B25937273 : Blo 1598998 25937273 := bstep (se 2 (by rfl) ⟨9726477, by rfl⟩ : syracuseStep 25937273 = 19452955) B19452955
theorem B5127961 : Blo 1598998 5127961 := bstep (se 2 (by rfl) ⟨1922985, by rfl⟩ : syracuseStep 5127961 = 3845971) B3845971
theorem B69166061 : Blo 1598998 69166061 := bstep (se 3 (by rfl) ⟨12968636, by rfl⟩ : syracuseStep 69166061 = 25937273) B25937273
theorem B6837281 : Blo 1598998 6837281 := bstep (se 2 (by rfl) ⟨2563980, by rfl⟩ : syracuseStep 6837281 = 5127961) B5127961
theorem B4558187 : Blo 1598998 4558187 := bstep (se 1 (by rfl) ⟨3418640, by rfl⟩ : syracuseStep 4558187 = 6837281) B6837281
theorem B46110707 : Blo 1598998 46110707 := bstep (se 1 (by rfl) ⟨34583030, by rfl⟩ : syracuseStep 46110707 = 69166061) B69166061
theorem B30740471 : Blo 1598998 30740471 := bstep (se 1 (by rfl) ⟨23055353, by rfl⟩ : syracuseStep 30740471 = 46110707) B46110707
theorem B3038791 : Blo 1598998 3038791 := bstep (se 1 (by rfl) ⟨2279093, by rfl⟩ : syracuseStep 3038791 = 4558187) B4558187
theorem B4051721 : Blo 1598998 4051721 := bstep (se 2 (by rfl) ⟨1519395, by rfl⟩ : syracuseStep 4051721 = 3038791) B3038791
theorem B20493647 : Blo 1598998 20493647 := bstep (se 1 (by rfl) ⟨15370235, by rfl⟩ : syracuseStep 20493647 = 30740471) B30740471
theorem B2701147 : Blo 1598998 2701147 := bstep (se 1 (by rfl) ⟨2025860, by rfl⟩ : syracuseStep 2701147 = 4051721) B4051721
theorem B13662431 : Blo 1598998 13662431 := bstep (se 1 (by rfl) ⟨10246823, by rfl⟩ : syracuseStep 13662431 = 20493647) B20493647
theorem B3601529 : Blo 1598998 3601529 := bstep (se 2 (by rfl) ⟨1350573, by rfl⟩ : syracuseStep 3601529 = 2701147) B2701147
theorem B9108287 : Blo 1598998 9108287 := bstep (se 1 (by rfl) ⟨6831215, by rfl⟩ : syracuseStep 9108287 = 13662431) B13662431
theorem B2401019 : Blo 1598998 2401019 := bstep (se 1 (by rfl) ⟨1800764, by rfl⟩ : syracuseStep 2401019 = 3601529) B3601529
theorem B6072191 : Blo 1598998 6072191 := bstep (se 1 (by rfl) ⟨4554143, by rfl⟩ : syracuseStep 6072191 = 9108287) B9108287
theorem B4048127 : Blo 1598998 4048127 := bstep (se 1 (by rfl) ⟨3036095, by rfl⟩ : syracuseStep 4048127 = 6072191) B6072191
theorem B1600679 : Blo 1598998 1600679 := bstep (se 1 (by rfl) ⟨1200509, by rfl⟩ : syracuseStep 1600679 = 2401019) B2401019
theorem B2698751 : Blo 1598998 2698751 := bstep (se 1 (by rfl) ⟨2024063, by rfl⟩ : syracuseStep 2698751 = 4048127) B4048127
theorem B1799167 : Blo 1598998 1799167 := bstep (se 1 (by rfl) ⟨1349375, by rfl⟩ : syracuseStep 1799167 = 2698751) B2698751
theorem B2398889 : Blo 1598998 2398889 := bstep (se 2 (by rfl) ⟨899583, by rfl⟩ : syracuseStep 2398889 = 1799167) B1799167
theorem B1599259 : Blo 1598998 1599259 := bstep (se 1 (by rfl) ⟨1199444, by rfl⟩ : syracuseStep 1599259 = 2398889) B2398889

theorem C0 (j : ℕ) (h1 : 399749 ≤ j) (h2 : j ≤ 400248) : Blo 1598998 (4 * j + 3) := by
  interval_cases j
  · exact B1598999
  · exact B1599003
  · exact B1599007
  · exact B1599011
  · exact B1599015
  · exact B1599019
  · exact B1599023
  · exact B1599027
  · exact B1599031
  · exact B1599035
  · exact B1599039
  · exact B1599043
  · exact B1599047
  · exact B1599051
  · exact B1599055
  · exact B1599059
  · exact B1599063
  · exact B1599067
  · exact B1599071
  · exact B1599075
  · exact B1599079
  · exact B1599083
  · exact B1599087
  · exact B1599091
  · exact B1599095
  · exact B1599099
  · exact B1599103
  · exact B1599107
  · exact B1599111
  · exact B1599115
  · exact B1599119
  · exact B1599123
  · exact B1599127
  · exact B1599131
  · exact B1599135
  · exact B1599139
  · exact B1599143
  · exact B1599147
  · exact B1599151
  · exact B1599155
  · exact B1599159
  · exact B1599163
  · exact B1599167
  · exact B1599171
  · exact B1599175
  · exact B1599179
  · exact B1599183
  · exact B1599187
  · exact B1599191
  · exact B1599195
  · exact B1599199
  · exact B1599203
  · exact B1599207
  · exact B1599211
  · exact B1599215
  · exact B1599219
  · exact B1599223
  · exact B1599227
  · exact B1599231
  · exact B1599235
  · exact B1599239
  · exact B1599243
  · exact B1599247
  · exact B1599251
  · exact B1599255
  · exact B1599259
  · exact B1599263
  · exact B1599267
  · exact B1599271
  · exact B1599275
  · exact B1599279
  · exact B1599283
  · exact B1599287
  · exact B1599291
  · exact B1599295
  · exact B1599299
  · exact B1599303
  · exact B1599307
  · exact B1599311
  · exact B1599315
  · exact B1599319
  · exact B1599323
  · exact B1599327
  · exact B1599331
  · exact B1599335
  · exact B1599339
  · exact B1599343
  · exact B1599347
  · exact B1599351
  · exact B1599355
  · exact B1599359
  · exact B1599363
  · exact B1599367
  · exact B1599371
  · exact B1599375
  · exact B1599379
  · exact B1599383
  · exact B1599387
  · exact B1599391
  · exact B1599395
  · exact B1599399
  · exact B1599403
  · exact B1599407
  · exact B1599411
  · exact B1599415
  · exact B1599419
  · exact B1599423
  · exact B1599427
  · exact B1599431
  · exact B1599435
  · exact B1599439
  · exact B1599443
  · exact B1599447
  · exact B1599451
  · exact B1599455
  · exact B1599459
  · exact B1599463
  · exact B1599467
  · exact B1599471
  · exact B1599475
  · exact B1599479
  · exact B1599483
  · exact B1599487
  · exact B1599491
  · exact B1599495
  · exact B1599499
  · exact B1599503
  · exact B1599507
  · exact B1599511
  · exact B1599515
  · exact B1599519
  · exact B1599523
  · exact B1599527
  · exact B1599531
  · exact B1599535
  · exact B1599539
  · exact B1599543
  · exact B1599547
  · exact B1599551
  · exact B1599555
  · exact B1599559
  · exact B1599563
  · exact B1599567
  · exact B1599571
  · exact B1599575
  · exact B1599579
  · exact B1599583
  · exact B1599587
  · exact B1599591
  · exact B1599595
  · exact B1599599
  · exact B1599603
  · exact B1599607
  · exact B1599611
  · exact B1599615
  · exact B1599619
  · exact B1599623
  · exact B1599627
  · exact B1599631
  · exact B1599635
  · exact B1599639
  · exact B1599643
  · exact B1599647
  · exact B1599651
  · exact B1599655
  · exact B1599659
  · exact B1599663
  · exact B1599667
  · exact B1599671
  · exact B1599675
  · exact B1599679
  · exact B1599683
  · exact B1599687
  · exact B1599691
  · exact B1599695
  · exact B1599699
  · exact B1599703
  · exact B1599707
  · exact B1599711
  · exact B1599715
  · exact B1599719
  · exact B1599723
  · exact B1599727
  · exact B1599731
  · exact B1599735
  · exact B1599739
  · exact B1599743
  · exact B1599747
  · exact B1599751
  · exact B1599755
  · exact B1599759
  · exact B1599763
  · exact B1599767
  · exact B1599771
  · exact B1599775
  · exact B1599779
  · exact B1599783
  · exact B1599787
  · exact B1599791
  · exact B1599795
  · exact B1599799
  · exact B1599803
  · exact B1599807
  · exact B1599811
  · exact B1599815
  · exact B1599819
  · exact B1599823
  · exact B1599827
  · exact B1599831
  · exact B1599835
  · exact B1599839
  · exact B1599843
  · exact B1599847
  · exact B1599851
  · exact B1599855
  · exact B1599859
  · exact B1599863
  · exact B1599867
  · exact B1599871
  · exact B1599875
  · exact B1599879
  · exact B1599883
  · exact B1599887
  · exact B1599891
  · exact B1599895
  · exact B1599899
  · exact B1599903
  · exact B1599907
  · exact B1599911
  · exact B1599915
  · exact B1599919
  · exact B1599923
  · exact B1599927
  · exact B1599931
  · exact B1599935
  · exact B1599939
  · exact B1599943
  · exact B1599947
  · exact B1599951
  · exact B1599955
  · exact B1599959
  · exact B1599963
  · exact B1599967
  · exact B1599971
  · exact B1599975
  · exact B1599979
  · exact B1599983
  · exact B1599987
  · exact B1599991
  · exact B1599995
  · exact B1599999
  · exact B1600003
  · exact B1600007
  · exact B1600011
  · exact B1600015
  · exact B1600019
  · exact B1600023
  · exact B1600027
  · exact B1600031
  · exact B1600035
  · exact B1600039
  · exact B1600043
  · exact B1600047
  · exact B1600051
  · exact B1600055
  · exact B1600059
  · exact B1600063
  · exact B1600067
  · exact B1600071
  · exact B1600075
  · exact B1600079
  · exact B1600083
  · exact B1600087
  · exact B1600091
  · exact B1600095
  · exact B1600099
  · exact B1600103
  · exact B1600107
  · exact B1600111
  · exact B1600115
  · exact B1600119
  · exact B1600123
  · exact B1600127
  · exact B1600131
  · exact B1600135
  · exact B1600139
  · exact B1600143
  · exact B1600147
  · exact B1600151
  · exact B1600155
  · exact B1600159
  · exact B1600163
  · exact B1600167
  · exact B1600171
  · exact B1600175
  · exact B1600179
  · exact B1600183
  · exact B1600187
  · exact B1600191
  · exact B1600195
  · exact B1600199
  · exact B1600203
  · exact B1600207
  · exact B1600211
  · exact B1600215
  · exact B1600219
  · exact B1600223
  · exact B1600227
  · exact B1600231
  · exact B1600235
  · exact B1600239
  · exact B1600243
  · exact B1600247
  · exact B1600251
  · exact B1600255
  · exact B1600259
  · exact B1600263
  · exact B1600267
  · exact B1600271
  · exact B1600275
  · exact B1600279
  · exact B1600283
  · exact B1600287
  · exact B1600291
  · exact B1600295
  · exact B1600299
  · exact B1600303
  · exact B1600307
  · exact B1600311
  · exact B1600315
  · exact B1600319
  · exact B1600323
  · exact B1600327
  · exact B1600331
  · exact B1600335
  · exact B1600339
  · exact B1600343
  · exact B1600347
  · exact B1600351
  · exact B1600355
  · exact B1600359
  · exact B1600363
  · exact B1600367
  · exact B1600371
  · exact B1600375
  · exact B1600379
  · exact B1600383
  · exact B1600387
  · exact B1600391
  · exact B1600395
  · exact B1600399
  · exact B1600403
  · exact B1600407
  · exact B1600411
  · exact B1600415
  · exact B1600419
  · exact B1600423
  · exact B1600427
  · exact B1600431
  · exact B1600435
  · exact B1600439
  · exact B1600443
  · exact B1600447
  · exact B1600451
  · exact B1600455
  · exact B1600459
  · exact B1600463
  · exact B1600467
  · exact B1600471
  · exact B1600475
  · exact B1600479
  · exact B1600483
  · exact B1600487
  · exact B1600491
  · exact B1600495
  · exact B1600499
  · exact B1600503
  · exact B1600507
  · exact B1600511
  · exact B1600515
  · exact B1600519
  · exact B1600523
  · exact B1600527
  · exact B1600531
  · exact B1600535
  · exact B1600539
  · exact B1600543
  · exact B1600547
  · exact B1600551
  · exact B1600555
  · exact B1600559
  · exact B1600563
  · exact B1600567
  · exact B1600571
  · exact B1600575
  · exact B1600579
  · exact B1600583
  · exact B1600587
  · exact B1600591
  · exact B1600595
  · exact B1600599
  · exact B1600603
  · exact B1600607
  · exact B1600611
  · exact B1600615
  · exact B1600619
  · exact B1600623
  · exact B1600627
  · exact B1600631
  · exact B1600635
  · exact B1600639
  · exact B1600643
  · exact B1600647
  · exact B1600651
  · exact B1600655
  · exact B1600659
  · exact B1600663
  · exact B1600667
  · exact B1600671
  · exact B1600675
  · exact B1600679
  · exact B1600683
  · exact B1600687
  · exact B1600691
  · exact B1600695
  · exact B1600699
  · exact B1600703
  · exact B1600707
  · exact B1600711
  · exact B1600715
  · exact B1600719
  · exact B1600723
  · exact B1600727
  · exact B1600731
  · exact B1600735
  · exact B1600739
  · exact B1600743
  · exact B1600747
  · exact B1600751
  · exact B1600755
  · exact B1600759
  · exact B1600763
  · exact B1600767
  · exact B1600771
  · exact B1600775
  · exact B1600779
  · exact B1600783
  · exact B1600787
  · exact B1600791
  · exact B1600795
  · exact B1600799
  · exact B1600803
  · exact B1600807
  · exact B1600811
  · exact B1600815
  · exact B1600819
  · exact B1600823
  · exact B1600827
  · exact B1600831
  · exact B1600835
  · exact B1600839
  · exact B1600843
  · exact B1600847
  · exact B1600851
  · exact B1600855
  · exact B1600859
  · exact B1600863
  · exact B1600867
  · exact B1600871
  · exact B1600875
  · exact B1600879
  · exact B1600883
  · exact B1600887
  · exact B1600891
  · exact B1600895
  · exact B1600899
  · exact B1600903
  · exact B1600907
  · exact B1600911
  · exact B1600915
  · exact B1600919
  · exact B1600923
  · exact B1600927
  · exact B1600931
  · exact B1600935
  · exact B1600939
  · exact B1600943
  · exact B1600947
  · exact B1600951
  · exact B1600955
  · exact B1600959
  · exact B1600963
  · exact B1600967
  · exact B1600971
  · exact B1600975
  · exact B1600979
  · exact B1600983
  · exact B1600987
  · exact B1600991
  · exact B1600995

theorem solution (m : ℕ) (hlo : 1598998 ≤ m) (hhi : m ≤ 1600998) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 399749 ≤ j := by omega
    have hj2 : j ≤ 400248 := by omega
    have hb : Blo 1598998 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
